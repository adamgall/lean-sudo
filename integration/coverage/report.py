#!/usr/bin/env python3
import collections
import gzip
import json
import pathlib
import re
import shutil
import subprocess
import tempfile

NOTES = pathlib.Path('/out/notes')
RESULTS = pathlib.Path('/results')
SECURITY = [
    ('c/', 'P0', 'Trusted C memory, descriptor, credential and syscall boundary'),
    ('LeanSudo/Helper', 'P0', 'Privileged helper protocol and credential transition'),
    ('LeanSudo/Sys/Exec', 'P0', 'Execution, descriptors, process isolation and identity'),
    ('LeanSudo/Sys/Pam', 'P0', 'Authentication and account/session enforcement'),
    ('LeanSudo/Sys/Timestamp', 'P0', 'Authentication-cache ownership and replay checks'),
    ('LeanSudo/Sys/Edit', 'P0', 'Privileged file copy-back and path race defenses'),
    ('LeanSudo/Sudoedit', 'P0', 'Editor privilege separation and file validation'),
    ('LeanSudo/Sys/Plugin', 'P1', 'Plugin acceptance, ABI handling and failure decisions'),
    ('LeanSudo/Sys/Intercept', 'P1', 'Child execution mediation and deny paths'),
    ('LeanSudo/Sys/LogSrv', 'P1', 'Remote audit transport and failure handling'),
    ('LeanSudo/Background', 'P1', 'Background supervision, signals and exit accounting'),
]


def classify(name):
    for prefix, priority, reason in SECURITY:
        if name.startswith(prefix):
            return priority, reason
    return 'P2', 'Other generated policy and operational code'


def main():
    work = pathlib.Path(tempfile.mkdtemp(prefix='sudo-coverage-'))
    shutil.copytree(NOTES, work, dirs_exist_ok=True)
    records = []
    diagnostics = []
    data_files = 0
    for note in sorted(work.rglob('*.gcno')):
        relative = note.relative_to(work)
        data = RESULTS / 'data/src' / relative.with_suffix('.gcda')
        if data.exists() and data.stat().st_size:
            shutil.copyfile(data, note.with_suffix('.gcda'))
            data_files += 1
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run(['gcov', '--json-format', str(note)], cwd=directory,
                                    capture_output=True, text=True)
            diagnostics.append(result.stdout + result.stderr)
            if result.returncode:
                raise RuntimeError('gcov failed for ' + str(note) + ': ' + result.stderr)
            for compressed in pathlib.Path(directory).glob('*.gcov.json.gz'):
                with gzip.open(compressed, 'rt') as stream:
                    document = json.load(stream)
                for source in document['files']:
                    filename = source['file'].removeprefix('/src/')
                    if filename.startswith('.lake/build/ir/LeanSudo/'):
                        module = filename.removeprefix('.lake/build/ir/').removesuffix('.c')
                        kind = 'Lean'
                    elif filename.startswith('c/') and filename.endswith('.c'):
                        module, kind = filename, 'C'
                    else:
                        continue
                    priority, reason = classify(module)
                    functions = []
                    for function in source.get('functions', []):
                        symbol = function['name']
                        functions.append({
                            'symbol': symbol,
                            'count': function['execution_count'],
                            'line': function['start_line'],
                            'end_line': function['end_line'],
                        })
                    lines = [{'line': line['line_number'], 'count': line['count']}
                             for line in source['lines']]
                    records.append({'module': module, 'kind': kind, 'source': filename,
                                    'priority': priority, 'reason': reason,
                                    'functions': functions, 'lines': lines})
    for record in records:
        groups = {}
        if record['kind'] == 'Lean':
            for function in record['functions']:
                symbol = function['symbol']
                start = symbol.rfind('LeanSudo_')
                if start < 0 or symbol.startswith('_init_'):
                    continue
                name = re.split(r'___|_spec__', symbol[start:])[0]
                group = groups.setdefault(name, {'name': name, 'hit': False, 'symbols': []})
                group['hit'] |= function['count'] > 0
                group['symbols'].append(symbol)
        record['lean_function_groups'] = list(groups.values())
    totals = collections.defaultdict(lambda: collections.Counter())
    for record in records:
        count = totals[record['kind']]
        count['functions'] += len(record['functions'])
        count['functions_hit'] += sum(f['count'] > 0 for f in record['functions'])
        count['lines'] += len(record['lines'])
        count['lines_hit'] += sum(line['count'] > 0 for line in record['lines'])
        if record['kind'] == 'Lean':
            count['declaration_groups'] += len(record['lean_function_groups'])
            count['declaration_groups_hit'] += sum(
                group['hit'] for group in record['lean_function_groups'])
    suite_results = json.loads((RESULTS / 'results.json').read_text())
    report = {'data_files': data_files, 'totals': dict(totals),
              'suite_results': suite_results, 'modules': records}
    (RESULTS / 'coverage.json').write_text(json.dumps(report, indent=2) + '\n')
    text = ['# Docker full-suite gcov coverage', '',
            'Line numbers for Lean modules refer to generated C, not Lean source lines.',
            'Counts may include inherited pre-fork counters; use hit/miss, not frequencies.',
            'Instrumentation changes timing and is not a production privilege-safety proof.', '']
    for kind, count in sorted(totals.items()):
        text.append(f"{kind}: functions {count['functions_hit']}/{count['functions']}; "
                    f"lines {count['lines_hit']}/{count['lines']}")
        if kind == 'Lean':
            text.append(f"Lean symbol-derived declaration groups: "
                        f"{count['declaration_groups_hit']}/{count['declaration_groups']}")
    text += ['', '## Suite evidence', '', '```text']
    for suite in suite_results['suites']:
        text.extend(suite['summaries'])
    text += ['```', '', f"Runtime diagnostics: {len(suite_results['findings'])}.",
             'See results.json for test-named diagnostics; these are not suppressed.', '']
    text += ['', '## Module totals', '', '| Module | Functions | Lines |', '|---|---:|---:|']
    for record in records:
        functions = record['functions']
        lines = record['lines']
        fh = sum(f['count'] > 0 for f in functions)
        lh = sum(line['count'] > 0 for line in lines)
        text.append(f"| {record['module']} | {fh}/{len(functions)} | {lh}/{len(lines)} |")
    text += ['', '## Prioritised uncovered security boundaries', '']
    text += ['Lean groups merge boxed, reduced-argument and specialised symbols by owning',
             'declaration name; this is a symbol-derived approximation, not a source map.', '']
    for record in sorted(records, key=lambda r: (r['priority'], r['module'])):
        if record['priority'] == 'P2':
            continue
        missed = [f for f in record['functions'] if f['count'] == 0]
        missed_lines = [str(line['line']) for line in record['lines'] if line['count'] == 0]
        if not missed and not missed_lines:
            continue
        text += [f"### {record['priority']}: {record['module']}", '', record['reason'] + '.', '']
        if record['kind'] == 'Lean':
            groups = [g for g in record['lean_function_groups'] if not g['hit']]
            text += ['Unreached Lean declaration groups:']
            text.extend(f"- `{group['name']}`" for group in groups)
            if not groups:
                text.append('- None; missing generated variants/lines are listed below.')
            text += ['', 'Never-executed generated symbols:']
        else:
            text += ['Never-executed C functions:']
        text.extend(f"- `{f['symbol']}` (generated/source C line {f['line']})" for f in missed)
        if not missed:
            text.append('- None; uncovered lines remain inside exercised functions.')
        text += ['', 'Uncovered C lines: ' + ', '.join(missed_lines), '']
    (RESULTS / 'coverage.md').write_text('\n'.join(text) + '\n')
    (RESULTS / 'gcov.log').write_text('\n'.join(diagnostics))
    if not data_files or not totals['C']['lines_hit'] or not totals['Lean']['lines_hit']:
        raise RuntimeError('coverage evidence missing for C or generated Lean code')
    print('\n'.join(text[:11]))
    print('Report: integration/out/coverage/coverage.md')


if __name__ == '__main__':
    main()
