#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

extern void __gcov_dump(void);
extern void __gcov_reset(void);
extern int __real_execve(const char *, char *const[], char *const[]);
extern int __real_fexecve(int, char *const[], char *const[]);
extern void __real__exit(int) __attribute__((noreturn));
extern void __real__Exit(int) __attribute__((noreturn));
extern int __real_open(const char *, int, ...);

static int coverage_directory = -1;
static struct stat coverage_identity;

__attribute__((constructor)) static void prepare_coverage(void) {
    int saved = errno;
    coverage_directory = __real_open("/coverage", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (coverage_directory >= 0) fstat(coverage_directory, &coverage_identity);
    errno = saved;
}

int __wrap_open(const char *path, int flags, ...) {
    mode_t mode = 0;
    if ((flags & O_CREAT) || (flags & O_TMPFILE) == O_TMPFILE) {
        va_list args;
        va_start(args, flags);
        mode = va_arg(args, mode_t);
        va_end(args);
    }
    if (coverage_directory >= 0 && strncmp(path, "/coverage/", 10) == 0) {
        struct stat current;
        if (fstat(coverage_directory, &current) == 0 &&
            current.st_dev == coverage_identity.st_dev &&
            current.st_ino == coverage_identity.st_ino && S_ISDIR(current.st_mode)) {
            const char *relative = path + 10;
            while (*relative == '/') relative++;
            return openat(coverage_directory, relative, flags, mode);
        }
    }
    return __real_open(path, flags, mode);
}

static void flush(void) {
    int saved = errno;
    __gcov_dump();
    __gcov_reset();
    errno = saved;
}

int __wrap_execve(const char *path, char *const argv[], char *const envp[]) {
    flush();
    return __real_execve(path, argv, envp);
}

int __wrap_fexecve(int fd, char *const argv[], char *const envp[]) {
    flush();
    return __real_fexecve(fd, argv, envp);
}

void __wrap__exit(int status) {
    flush();
    __real__exit(status);
}

void __wrap__Exit(int status) {
    flush();
    __real__Exit(status);
}
