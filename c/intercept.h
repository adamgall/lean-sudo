#ifndef LEAN_SUDO_INTERCEPT_H
#define LEAN_SUDO_INTERCEPT_H
#include <sys/types.h>
int ls_intercept_active(void);
int ls_intercept_trace(void);
int ls_intercept_verify(void);
int ls_intercept_check(const char *, char *const [], char *const [], const char *, pid_t, int);
int ls_intercept_trace_supported(void);
int ls_intercept_trace_child(void);
int ls_intercept_trace_prepare(void);
int ls_intercept_trace_attach(pid_t);
int ls_intercept_trace_wait(pid_t, int);
void ls_intercept_trace_close(void);
#endif
