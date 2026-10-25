#ifndef LEANSUDO_LOGSRV_H
#define LEANSUDO_LOGSRV_H

#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

LEAN_EXPORT lean_obj_res leansudo_logsrv_connect(b_lean_obj_arg host,
    b_lean_obj_arg service, uint8_t tls, uint32_t timeout, uint8_t keepalive,
    uint8_t verify, b_lean_obj_arg ca, b_lean_obj_arg cert, b_lean_obj_arg key,
    lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_send(b_lean_obj_arg bytes, lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_receive(uint8_t wait, lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_close(lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_relay(uint32_t mask, lean_obj_arg world);

int ls_logsrv_active(void);
int ls_logsrv_stream(int stream);
int ls_logsrv_event(int event, const void *buf, size_t len, unsigned a, unsigned b);
int ls_logsrv_network_fd(void);
int ls_logsrv_poll(void);
lean_obj_res ls_logsrv_take_error(void);
void ls_logsrv_child_close(void);

LEAN_EXPORT lean_obj_res leansudo_logsrv_queue_init(lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_queue_send(b_lean_obj_arg bytes, lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_queue_close(lean_obj_arg world);
int ls_logsrv_queue_fd(void);
int ls_logsrv_dispatch(void);
void ls_logsrv_detach_child(void);

extern lean_obj_res leansudo_logsrv_io_event(uint32_t event, lean_obj_arg data,
    uint32_t a, uint32_t b, lean_obj_arg world);
extern lean_obj_res leansudo_logsrv_subcommand_wire(lean_obj_arg bytes, lean_obj_arg world);
extern lean_obj_res leansudo_logsrv_poll(lean_obj_arg world);

#endif
