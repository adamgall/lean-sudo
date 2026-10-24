#ifndef LEANSUDO_LOCALE_SCOPE_H
#define LEANSUDO_LOCALE_SCOPE_H

#include <locale.h>

/* Thread-local sudoers locale scope. Unavailable names fall back to C, while
 * allocation/setup errors return zero. Leave every successful scope before
 * returning to caller-locale PAM or front-end diagnostics. */
locale_t leansudo_locale_enter(const char *name, locale_t *previous);
void leansudo_locale_leave(locale_t locale, locale_t previous);

#endif
