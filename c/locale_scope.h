#ifndef LEANSUDO_LOCALE_SCOPE_H
#define LEANSUDO_LOCALE_SCOPE_H

#include <locale.h>

locale_t leansudo_locale_enter(const char *name, locale_t *previous);
void leansudo_locale_leave(locale_t locale, locale_t previous);

#endif
