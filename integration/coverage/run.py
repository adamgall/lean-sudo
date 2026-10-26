#!/usr/bin/env python3
import argparse
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]


def command(args, **kwargs):
    return subprocess.run(args, check=True, **kwargs)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('variant', choices=['sanitize', 'asan', 'coverage'])
    parser.add_argument('--no-build', action='store_true')
    options = parser.parse_args()
    variant = options.variant
    binaries = ROOT / '.lake' / ('linux-' + variant)
    output = ROOT / 'integration/out' / variant
    output.mkdir(parents=True, exist_ok=True)
    if not options.no_build:
        command([str(ROOT / 'integration/build-variant.sh'), variant])
    image = 'lean-sudo-it-' + variant
    with (output / 'image-build.log').open('w') as log:
        command(['docker', 'build', '--build-arg',
                 'BASE=' + os.environ.get('SUDO_IT_BASE', 'ubuntu:26.04'),
                 '-t', image, str(ROOT / 'integration')], stdout=log, stderr=log)
    data = output / 'data'
    if variant == 'coverage':
        data.mkdir(exist_ok=True)
        if any(data.iterdir()):
            raise SystemExit('move the existing coverage/data directory before a fresh run')
        for note in (binaries / 'notes/.lake/build').rglob('*.gcno'):
            relative = note.relative_to(binaries / 'notes').with_suffix('.gcda')
            target = data / 'src' / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.touch()
            target.chmod(0o666)
    results = []
    findings = []
    for suite in ['sudo', 'visudo']:
        label = variant + '-' + suite
        entry = '/opt/sudo-it/tests.sh' if suite == 'sudo' else '/opt/impl/visudo-tests.sh'
        args = ['docker', 'create', '--hostname', 'sudo-it', '--network', 'none',
                '--cap-add', 'SYS_PTRACE', '--cap-add', 'SYS_ADMIN',
                '-v', str(output) + ':/out', '-e', 'IMPL_LABEL=' + label,
                '-e', 'HOST_UID=' + str(os.getuid()), '-e', 'HOST_GID=' + str(os.getgid()),
                '-e', 'VISUDO_SUDO_BINARY=/opt/impl/sudo', '--entrypoint', entry,
                image, '/opt/impl/' + suite]
        cid = command(args, capture_output=True, text=True).stdout.strip()
        try:
            for name in ['sudo', 'visudo']:
                command(['docker', 'cp', '-q', str(binaries / name), cid + ':/opt/impl/' + name])
            command(['docker', 'cp', '-q', str(ROOT / 'integration/visudo-tests.sh'),
                     cid + ':/opt/impl/visudo-tests.sh'])
            if variant == 'coverage':
                command(['docker', 'cp', '-q', str(data), cid + ':/coverage'])
            with (output / (suite + '-console.log')).open('w') as log:
                result = subprocess.run(['docker', 'start', '-a', cid], stdout=log, stderr=log)
            if variant == 'coverage':
                command(['docker', 'cp', '-q', cid + ':/coverage/.', str(data)])
            text = (output / (suite + '-console.log')).read_text()
            summaries = [line for line in text.splitlines()
                         if re.search(r'^# (passed:|implementation:|FAILED:)|^1\.\.', line)]
            print('\n'.join(summaries), flush=True)
            results.append({'suite': suite, 'status': result.returncode, 'summaries': summaries})
            transcript = (output / (label + '.log')).read_text()
            test = 'suite setup'
            for line in transcript.splitlines():
                if line.startswith('=== '):
                    test = line[4:]
                if re.search(r'AddressSanitizer|Illegal instruction|Trace/breakpoint trap|'
                             r'Aborted|Segmentation fault|libgcov profiling error|profiling:|'
                             r'--- rc=(132|133|134|139|159)\b', line):
                    findings.append({'suite': suite, 'test': test, 'evidence': line})
        finally:
            subprocess.run(['docker', 'rm', '-f', cid], stdout=subprocess.DEVNULL, check=False)
    (output / 'results.json').write_text(json.dumps(
        {'variant': variant, 'suites': results, 'findings': findings}, indent=2) + '\n')
    if variant == 'coverage':
        command(['docker', 'run', '--rm', '--network', 'none',
                 '-v', str(output) + ':/results',
                 '-v', str(ROOT / 'integration/coverage/report.py') + ':/report.py:ro',
                 '--entrypoint', 'python3', 'lean-sudo-coverage-report', '/report.py'])
    print('Results: ' + str(output / 'results.json'))
    return int(bool(findings) or any(item['status'] for item in results))


if __name__ == '__main__':
    sys.exit(main())
