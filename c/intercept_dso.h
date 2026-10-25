#ifndef LEAN_SUDO_INTERCEPT_DSO_H
#define LEAN_SUDO_INTERCEPT_DSO_H

void ls_intercept_dso_set_log_only(int enabled);
int ls_intercept_dso_prepare(void);
void ls_intercept_dso_parent(void);
void ls_intercept_dso_detach_service(void);
int ls_intercept_dso_child(void);
char **ls_intercept_dso_environment(char *const envp[]);
void ls_intercept_dso_free_environment(char **envp);
int ls_intercept_dso_service(int timeout_ms);
void ls_intercept_dso_close(void);

#endif
