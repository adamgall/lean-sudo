#include "shim.h"
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

static void inspect_child(int fd, const char *const *paths, size_t count,
        uid_t uid, gid_t gid, const gid_t *groups, size_t ngroups, gid_t *verify) {
    uint64_t header[2] = {0, count};
    if (ls_drop_credentials(uid, gid, groups, ngroups, verify) == -1)
        header[0] = (uint64_t)errno;
    if (ls_transfer(fd, (void *)header, sizeof header, 1) == -1) _exit(1);
    if (header[0]) _exit(0);
    for (size_t i = 0; i < count; ++i) {
        struct stat st;
        uint64_t facts[FACT_FIELDS] = {0};
        int rc;
        rc = TEMP_FAILURE_RETRY(stat(paths[i], &st));
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
        if (ls_transfer(fd, (void *)facts, sizeof facts, 1) == -1) _exit(1);
    }
    _exit(0);
}

static int unavailable(uint64_t err) {
    return err == ENOENT || err == ENOTDIR || err == EACCES ||
        err == EPERM || err == ELOOP;
}

LEAN_EXPORT lean_obj_res lean_sudo_inspect_paths(b_lean_obj_arg paths,
        uint32_t uid, uint32_t gid, b_lean_obj_arg group_array) {
    size_t count = lean_array_size(paths), ngroups = lean_array_size(group_array);
    if (uid == UINT32_MAX || gid == UINT32_MAX || count > LOOKUP_MAX ||
        ngroups > LOOKUP_MAX) return ls_errno(EINVAL);
    const char **names = count ? malloc(count * sizeof(*names)) : NULL;
    gid_t *groups = ngroups ? malloc(2 * ngroups * sizeof(*groups)) : NULL;
    if ((count && !names) || (ngroups && !groups)) {
        free(names); free(groups); return ls_errno(ENOMEM);
    }
    for (size_t i = 0; i < count; ++i) {
        lean_object *path = lean_array_get_core(paths, i);
        names[i] = lean_string_cstr(path);
        if (strlen(names[i]) != lean_string_size(path) - 1) {
            free(names); free(groups); return ls_errno(EINVAL);
        }
    }
    for (size_t i = 0; i < ngroups; ++i) {
        uint32_t group = lean_unbox_uint32(lean_array_get_core(group_array, i));
        if (group == UINT32_MAX) {
            free(names); free(groups); return ls_errno(EINVAL);
        }
        groups[i] = (gid_t)group;
    }
    if (ngroups > 1) qsort(groups, ngroups, sizeof(*groups), ls_compare_gid);
    int sockets[2];
    if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sockets) == -1) {
        int err = errno; free(names); free(groups); return ls_errno(err);
    }
    pid_t pid = fork();
    if (pid == -1) {
        int err = errno;
        close(sockets[0]); close(sockets[1]); free(names); free(groups);
        return ls_errno(err);
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
    if (ls_transfer(sockets[0], header, sizeof header, 0) == -1) err = errno;
    else if (header[1] != count || header[0] > INT32_MAX) err = EIO;
    else if (header[0]) err = (int)header[0];
    for (size_t i = 0; !err && i < count; ++i) {
        uint64_t facts[FACT_FIELDS];
        if (ls_transfer(sockets[0], facts, sizeof facts, 0) == -1) { err = errno; break; }
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
        n = TEMP_FAILURE_RETRY(read(sockets[0], &extra, 1));
        if (n != 0) err = n < 0 ? errno : EIO;
    }
    close(sockets[0]);
    int status;
    pid_t waited;
    waited = TEMP_FAILURE_RETRY(waitpid(pid, &status, 0));
    if (!err && (waited != pid || !WIFEXITED(status) || WEXITSTATUS(status) != 0))
        err = waited == -1 ? errno : EIO;
    if (err) { lean_dec(result); return ls_errno(err); }
    return lean_io_result_mk_ok(result);
}
