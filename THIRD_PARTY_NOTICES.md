# Third-party notices

Parts of lean-sudo are derived from sudo 1.9.17p2 (https://www.sudo.ws,
https://github.com/sudo-project/sudo), which is distributed under the ISC license.
The repository keeps no comments in its source files, so the notices those files
would otherwise carry are collected here.

| File | Derived from (sudo 1.9.17p2) | Copyright |
|---|---|---|
| `c/sudo_plugin.h` | `include/sudo_plugin.h` (plugin ABI declarations) | Copyright (c) 2009-2023 Todd C. Miller <Todd.Miller@sudo.ws> |
| `c/exec.c` | job-control and tty-size handling following `src/suspend_parent.c`, `src/ttysize.c` | Copyright (c) 2009-2023 Todd C. Miller <Todd.Miller@sudo.ws> |
| `c/plugins.c` | plugin ABI sequencing following `src/sudo.c`, `src/load_plugins.c`, `src/exec_iolog.c` | Copyright (c) 2009-2024 Todd C. Miller <Todd.Miller@sudo.ws> |
| `c/sys.c` | regular-expression repetition validation from `lib/util/regex.c` | Copyright (c) 2023 Todd C. Miller <Todd.Miller@sudo.ws> |
| `LeanSudo/EventLog.lean` | event log formats from `lib/eventlog/eventlog.c`, `lib/eventlog/logwrap.c`, `include/sudo_eventlog.h` | Copyright (c) 1994-1996, 1998-2023, 2011, 2014-2020, 2020-2021 Todd C. Miller <Todd.Miller@sudo.ws> |
| `LeanSudo/Insults.lean` | insult texts from `plugins/sudoers/ins_2001.h`, `ins_goons.h`, `ins_classic.h`, `ins_csops.h`, `ins_python.h`, `insults.h` | Copyright (c) 1994-1996, 1998-1999, 2004, 2018 Todd C. Miller <Todd.Miller@sudo.ws> |

Portions of sudo's event log code were sponsored in part by the Defense Advanced
Research Projects Agency (DARPA) and Air Force Research Laboratory, Air Force Materiel
Command, USAF, under agreement number F39502-99-1-0512.

## ISC license

```
Permission to use, copy, modify, and distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
```
