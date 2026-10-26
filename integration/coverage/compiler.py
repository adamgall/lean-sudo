#!/usr/bin/env python3
import os
import pathlib
import subprocess
import sys

args = sys.argv[1:]
variant = os.environ['VARIANT']
compile_only = '-c' in args
shim = any(pathlib.Path(arg).suffix == '.c' and '/c/' in '/' + arg for arg in args)
compiler = '/usr/bin/gcc' if variant == 'coverage' else '/usr/bin/clang'
extra = []
if variant == 'coverage':
    if compile_only:
        extra = ['--coverage', '-fprofile-update=atomic', '-fprofile-dir=/coverage',
                 '-O0', '-g', '-Wno-error']
    else:
        extra = ['--coverage', '/src/integration/coverage/flush.o',
                 '-Wl,--wrap=execve,--wrap=fexecve,--wrap=_exit,--wrap=_Exit,--wrap=open']
elif variant == 'sanitize' and compile_only and shim:
    extra = ['-fsanitize=undefined,bounds', '-fsanitize-trap=all', '-g']
elif variant == 'asan':
    if compile_only and shim:
        extra = ['-fsanitize=address', '-fno-omit-frame-pointer', '-g']
    elif not compile_only:
        extra = ['-fsanitize=address', '/src/integration/coverage/asan-options.o']
if variant != 'coverage':
    extra += ['-Wno-error=unused-command-line-argument']
if not compile_only:
    prefix = subprocess.check_output(['lean', '--print-prefix'], text=True).strip()
    extra += ['-L' + prefix + '/lib']
os.execv(compiler, [compiler, *args, *extra])
