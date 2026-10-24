/* Credential-scoped stat batches (LeanSudo.Sys.Lookup).
 * No command selection, executable-bit test, PATH or dot policy lives here.
 * A child permanently installs one credential set; the parent never changes ids.
 * The private socket carries fixed-width facts, never child pointers or padding.
 */
#include <lean/lean.h>
#include <errno.h>
#include <grp.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/fsuid.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#define LOOKUP_MAX 65536U
#define FACT_FIELDS 8U

static lean_obj_res lookup_error(int err) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(strerror(err))));
}

static int compare_gid(const void *a, const void *b) {
    gid_t x = *(const gid_t *)a, y = *(const gid_t *)b;
    return (x > y) - (x < y);
}

static int drop_credentials(uid_t uid, gid_t gid, const gid_t *groups,
        size_t count, gid_t *verify) {
    uid_t ruid, euid, suid;
    gid_t rgid, egid, sgid;
    if (setgroups(count, groups) == -1 ||
        setresgid(gid, gid, gid) == -1 || setresuid(uid, uid, uid) == -1 ||
        getresuid(&ruid, &euid, &suid) == -1 ||
        getresgid(&rgid, &egid, &sgid) == -1) return -1;
    if (ruid != uid || euid != uid || suid != uid ||
        rgid != gid || egid != gid || sgid != gid ||
        (uid_t)setfsuid((uid_t)-1) != uid || (gid_t)setfsgid((gid_t)-1) != gid)
        goto mismatch;
    if (getgroups(0, NULL) != (int)count) goto mismatch;
    if (count) {
        if (getgroups((int)count, verify) != (int)count) goto mismatch;
        /* Linux sorts supplementary groups when installing them. The requested
         * array was sorted before fork; compare all entries, including duplicates.
         * No allocation or Lean runtime operation is needed in the child. */
        if (memcmp(groups, verify, count * sizeof(*groups)) != 0) goto mismatch;
    }
    return 0;
mismatch:
    errno = EPERM;
    return -1;
}

static int send_exact(int fd, const void *data, size_t size) {
    const unsigned char *p = data;
    while (size) {
        ssize_t n = send(fd, p, size, MSG_NOSIGNAL);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return -1;
        p += n;
        size -= (size_t)n;
    }
    return 0;
}

static int read_exact(int fd, void *data, size_t size) {
    unsigned char *p = data;
    while (size) {
        ssize_t n = read(fd, p, size);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) return -1;
        if (n == 0) { errno = EIO; return -1; }
        p += n;
        size -= (size_t)n;
    }
    return 0;
}

/* Borrowed paths and group storage are prepared before fork. The wire format is
 * two uint64_t header words (credential errno, count), followed on success by
 * count records of eight uint64_t words (stat errno, FileStat's seven fields).
 * Both ends are the same process image, so native endianness is intentional.
 * EOF and successful wait status are required after exactly the expected data. */
static void inspect_child(int fd, const char *const *paths, size_t count,
        uid_t uid, gid_t gid, const gid_t *groups, size_t ngroups, gid_t *verify) {
    uint64_t header[2] = {0, count};
    if (drop_credentials(uid, gid, groups, ngroups, verify) == -1)
        header[0] = (uint64_t)errno;
    if (send_exact(fd, header, sizeof header) == -1) _exit(1);
    if (header[0]) _exit(0);
    for (size_t i = 0; i < count; ++i) {
        struct stat st;
        uint64_t facts[FACT_FIELDS] = {0};
        int rc;
        do { rc = stat(paths[i], &st); } while (rc == -1 && errno == EINTR);
        if (rc == -1) facts[0] = (uint64_t)errno;
        else {
            facts[1] = (uint64_t)st.st_dev;
            facts[2] = (uint64_t)st.st_ino;
            facts[3] = (uint64_t)st.st_mode;
            facts[4] = (uint64_t)st.st_uid;
            facts[5] = (uint64_t)st.st_gid;
            facts[6] = st.st_size < 0 ? 0 : (uint64_t)st.st_size;
            facts[7] = (uint64_t)st.st_rdev;
        }
        if (send_exact(fd, facts, sizeof facts) == -1) _exit(1);
    }
    _exit(0);
}

/* These errno values describe a path which cannot be inspected with the supplied
 * credentials, not an infrastructure failure. In particular ENOMEM, EIO,
 * EOVERFLOW and ENAMETOOLONG must not turn into a successful partial search. */
static int unavailable(uint64_t err) {
    return err == ENOENT || err == ENOTDIR || err == EACCES ||
        err == EPERM || err == ELOOP;
}

LEAN_EXPORT lean_obj_res lean_sudo_inspect_paths(b_lean_obj_arg paths,
        uint32_t uid, uint32_t gid, b_lean_obj_arg group_array) {
    size_t count = lean_array_size(paths), ngroups = lean_array_size(group_array);
    if (uid == UINT32_MAX || gid == UINT32_MAX || count > LOOKUP_MAX ||
        ngroups > LOOKUP_MAX) return lookup_error(EINVAL);
    /* Allocate only syscall inputs; output is streamed directly into Lean. */
    const char **names = count ? malloc(count * sizeof(*names)) : NULL;
    gid_t *groups = ngroups ? malloc(2 * ngroups * sizeof(*groups)) : NULL;
    if ((count && !names) || (ngroups && !groups)) {
        free(names); free(groups); return lookup_error(ENOMEM);
    }
    for (size_t i = 0; i < count; ++i) {
        lean_object *path = lean_array_get_core(paths, i);
        names[i] = lean_string_cstr(path);
        if (strlen(names[i]) != lean_string_size(path) - 1) {
            free(names); free(groups); return lookup_error(EINVAL);
        }
    }
    for (size_t i = 0; i < ngroups; ++i) {
        uint32_t group = lean_unbox_uint32(lean_array_get_core(group_array, i));
        if (group == UINT32_MAX) {
            free(names); free(groups); return lookup_error(EINVAL);
        }
        groups[i] = (gid_t)group;
    }
    if (ngroups > 1) qsort(groups, ngroups, sizeof(*groups), compare_gid);
    int sockets[2];
    if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sockets) == -1) {
        int err = errno; free(names); free(groups); return lookup_error(err);
    }
    pid_t pid = fork();
    if (pid == -1) {
        int err = errno;
        close(sockets[0]); close(sockets[1]); free(names); free(groups);
        return lookup_error(err);
    }
    if (pid == 0) {
        close(sockets[0]);
        inspect_child(sockets[1], names, count, (uid_t)uid, (gid_t)gid,
            groups, ngroups, ngroups ? groups + ngroups : NULL);
    }
    close(sockets[1]); free(names); free(groups);
    lean_object *result = lean_mk_empty_array_with_capacity(lean_box(count));
    int err = 0;
    uint64_t header[2];
    if (read_exact(sockets[0], header, sizeof header) == -1) err = errno;
    else if (header[1] != count || header[0] > INT32_MAX) err = EIO;
    else if (header[0]) err = (int)header[0];
    for (size_t i = 0; !err && i < count; ++i) {
        uint64_t facts[FACT_FIELDS];
        if (read_exact(sockets[0], facts, sizeof facts) == -1) { err = errno; break; }
        lean_object *entry;
        if (facts[0]) {
            if (!unavailable(facts[0])) {
                err = facts[0] <= INT32_MAX ? (int)facts[0] : EIO;
                break;
            }
            entry = lean_box(0);
        } else {
            lean_object *st = lean_alloc_ctor(0, 7, 0);
            for (unsigned j = 0; j < 7; ++j)
                lean_ctor_set(st, j, lean_uint64_to_nat(facts[j + 1]));
            entry = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(entry, 0, st);
        }
        result = lean_array_push(result, entry);
    }
    if (!err) {
        unsigned char extra;
        ssize_t n;
        do { n = read(sockets[0], &extra, 1); } while (n < 0 && errno == EINTR);
        if (n != 0) err = n < 0 ? errno : EIO;
    }
    close(sockets[0]);
    int status;
    pid_t waited;
    do { waited = waitpid(pid, &status, 0); } while (waited == -1 && errno == EINTR);
    if (!err && (waited != pid || !WIFEXITED(status) || WEXITSTATUS(status) != 0))
        err = waited == -1 ? errno : EIO;
    if (err) { lean_dec(result); return lookup_error(err); }
    return lean_io_result_mk_ok(result);
}
