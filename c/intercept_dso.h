#ifndef LEAN_SUDO_INTERCEPT_DSO_H
#define LEAN_SUDO_INTERCEPT_DSO_H

/* Configure before prepare/fork. All calls return 0 on success, -1 on error. */
void ls_intercept_dso_set_log_only(int enabled);
int ls_intercept_dso_prepare(void);
/* Broker keeps service descriptors; executor keeps only the bootstrap socket. */
void ls_intercept_dso_parent(void);
void ls_intercept_dso_detach_service(void);
/* Call after closefrom/CLOEXEC processing, immediately before initial exec. */
int ls_intercept_dso_child(void);
/* New vector borrows original strings; free with the matching function only. */
char **ls_intercept_dso_environment(char *const envp[]);
void ls_intercept_dso_free_environment(char **envp);
/* One poll/dispatch iteration; -1 timeout blocks, 0 timeout never blocks.
 * Individual malformed/disconnected clients are closed, not server failures.
 * ls_intercept_check runs synchronously in this process (the policy broker).
 */
int ls_intercept_dso_service(int timeout_ms);
void ls_intercept_dso_close(void);

#endif
