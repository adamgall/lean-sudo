/* Remote log transport only; protocol and failure policy live in Lean. */
#ifndef LEANSUDO_LOGSRV_H
#define LEANSUDO_LOGSRV_H

#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

/* One caller-serialized connection. timeout is in seconds; zero permits no wait.
 * String and ByteArray inputs are borrowed. send/receive add/remove only the
 * network-order 32-bit frame length, with a maximum body size of 2 MiB. */
LEAN_EXPORT lean_obj_res leansudo_logsrv_connect(b_lean_obj_arg host,
    b_lean_obj_arg service, uint8_t tls, uint32_t timeout, uint8_t keepalive,
    uint8_t verify, b_lean_obj_arg ca, b_lean_obj_arg cert, b_lean_obj_arg key,
    lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_send(b_lean_obj_arg bytes, lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_receive(uint8_t wait, lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_close(lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_relay(uint32_t mask, lean_obj_arg world);

/* Relay bits 0..4: stdin, stdout, stderr, ttyin, ttyout. active means the
 * callback relay is enabled, not merely that a socket has been connected. */
int ls_logsrv_active(void);
int ls_logsrv_stream(int stream);
int ls_logsrv_event(int event, const void *buf, size_t len, unsigned a, unsigned b);
int ls_logsrv_network_fd(void);
int ls_logsrv_poll(void);
/* Transfer an owned failed Lean callback result, or NULL when none failed. */
lean_obj_res ls_logsrv_take_error(void);
void ls_logsrv_child_close(void);

/* Initialize after connect and before the broker fork. The single-writer queue
 * snapshots the connection timeout independently of network close.
 * dispatch drains available frames, retaining partial input; errors return -1.
 * detach_child retains only the broker's queue writer; child_close drops both
 * queue descriptors as well as the network descriptor in an exec child. */
LEAN_EXPORT lean_obj_res leansudo_logsrv_queue_init(lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_queue_send(b_lean_obj_arg bytes, lean_obj_arg world);
LEAN_EXPORT lean_obj_res leansudo_logsrv_queue_close(lean_obj_arg world);
int ls_logsrv_queue_fd(void);
int ls_logsrv_dispatch(void);
void ls_logsrv_detach_child(void);

/* Lean owns data and world. Event 5 carries rows/columns in a/b; event 7
 * carries the signal name in data. Callback failure becomes -1 with EIO. */
extern lean_obj_res leansudo_logsrv_io_event(uint32_t event, lean_obj_arg data,
    uint32_t a, uint32_t b, lean_obj_arg world);
extern lean_obj_res leansudo_logsrv_subcommand_wire(lean_obj_arg bytes, lean_obj_arg world);
extern lean_obj_res leansudo_logsrv_poll(lean_obj_arg world);

#endif
