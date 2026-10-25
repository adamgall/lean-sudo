#ifndef LEAN_SUDO_PLUGINS_H
#define LEAN_SUDO_PLUGINS_H
#include <stddef.h>
#include <poll.h>
#include "sudo_plugin.h"
int ls_plugins_io_active(void);
int ls_plugins_io_stream(int stream);
int ls_plugins_io_write(int stream, const void *data, size_t size);
int ls_plugins_io_winsize(unsigned rows, unsigned cols);
int ls_plugins_io_suspend(int signo);
int ls_plugins_poll(struct pollfd *fds, nfds_t count, int timeout);
void ls_plugins_signal(int signo);
int ls_plugin_conversation_config(int bell, const char *askpass);
int ls_plugin_utf8_valid(const char *text, size_t size);
void ls_plugins_exec_begin(void);
void ls_plugins_exec_status(int type, int status);
int ls_plugins_broker_init(void);
void ls_plugins_broker_child(void);
void ls_plugins_broker_parent(void);
void ls_plugins_broker_close(void);
int ls_plugin_read_reply(const char *prompt, int type, unsigned timeout,
    int use_stdin, char *buf, size_t size, struct sudo_conv_callback *callback);
#endif
