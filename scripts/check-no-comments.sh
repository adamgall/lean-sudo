#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec python3 - "$@" <<'PY'
import io
import pathlib
import re
import subprocess
import sys
import tokenize


def quoted_end(text, start, quote):
    i = start + 1
    while i < len(text):
        if text[i] == '\\':
            i += 2
        elif text[i] == quote:
            return i + 1
        else:
            i += 1
    return i


def compiled_comments(text, lean=False):
    if not lean and '\\\n' in text:
        positions = []
        i = 0
        while i < len(text):
            if text.startswith('\\\n', i):
                i += 2
            else:
                positions.append(i)
                i += 1
        joined = ''.join(text[position] for position in positions)
        return [(positions[a], positions[b - 1] + 1) for a, b in compiled_comments(joined)]
    spans = []
    i = 0
    while i < len(text):
        if lean and text[i] == 'r':
            raw = re.match(r'r(#+)?"', text[i:])
            if raw:
                end = text.find('"' + (raw[1] or ''), i + len(raw[0]))
                i = len(text) if end < 0 else end + 1 + len(raw[1] or '')
                continue
        if text[i] == '"':
            i = quoted_end(text, i, '"')
            continue
        if text[i] == "'":
            if not lean or re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", text[i:]):
                i = quoted_end(text, i, "'")
                continue
        line_mark, block_mark, block_end = ('--', '/-', '-/') if lean else ('//', '/*', '*/')
        if text.startswith(line_mark, i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            spans.append((i, end))
            i = end
        elif text.startswith(block_mark, i):
            start = i
            i += 2
            depth = 1
            while i < len(text) and depth:
                if text.startswith(block_end, i):
                    depth -= 1
                    i += 2
                elif lean and text.startswith(block_mark, i):
                    depth += 1
                    i += 2
                else:
                    i += 1
            spans.append((start, i))
        else:
            i += 1
    return spans


def python_comments(text):
    offsets = [0]
    for line in text.splitlines(keepends=True):
        offsets.append(offsets[-1] + len(line))
    result = []
    for token in tokenize.generate_tokens(io.StringIO(text).readline):
        if token.type == tokenize.COMMENT and not (token.start == (1, 0) and token.string.startswith('#!')):
            result.append((offsets[token.start[0] - 1] + token.start[1], offsets[token.end[0] - 1] + token.end[1]))
    return result


def embedded_language(command, delimiter, body):
    first = body.split('\n', 1)[0]
    if re.search(r'python|\.py(?:[\s"\']|$)', command + first, re.I) or delimiter in ('PY', 'PYTHON'):
        return 'python'
    if re.search(r'\.c(?:[\s"\']|$)', command) or delimiter in ('C', 'CC'):
        return 'c'
    if 'perl' in command + first or delimiter == 'PL':
        return 'perl'
    if first.startswith('#!') or delimiter in ('SH', 'BASH'):
        return 'shell'
    return None


def starts_shell_word(text, offset):
    if offset == 0:
        return True
    if not (text[offset - 1].isspace() or text[offset - 1] in ';|&()`'):
        return False
    backslashes = 0
    i = offset - 2
    while i >= 0 and text[i] == '\\':
        backslashes += 1
        i -= 1
    return backslashes % 2 == 0


def shell_comments(text, heredocs=True):
    spans = []
    pending = []
    stack = []
    quote = None
    i = 0
    line_start = 0
    while i < len(text):
        ch = text[i]
        if ch == '\n':
            i += 1
            if pending and quote is None:
                for delimiter, tabs, command in pending:
                    start = i
                    while i < len(text):
                        end = text.find('\n', i)
                        end = len(text) if end < 0 else end
                        line = text[i:end]
                        if (line.lstrip('\t') if tabs else line) == delimiter:
                            body = text[start:i]
                            language = embedded_language(command, delimiter, body)
                            if language:
                                spans.extend((start + a, start + b) for a, b in comments(body, language))
                            i = min(end + 1, len(text))
                            break
                        i = min(end + 1, len(text))
                pending.clear()
            line_start = i
            continue
        if quote == "'":
            if ch == "'":
                quote = None
            i += 1
            continue
        if ch == '\\':
            i += 2
            continue
        if text.startswith('$(', i) or text.startswith('${', i):
            stack.append((')' if text[i + 1] == '(' else '}', quote))
            quote = None
            i += 2
            continue
        if stack and ch == stack[-1][0] and quote is None:
            _, quote = stack.pop()
            i += 1
            continue
        if quote == '"':
            if ch == '"':
                quote = None
            i += 1
            continue
        if ch in "'\"":
            quote = ch
            i += 1
            continue
        if text.startswith('<<<', i):
            i += 3
            continue
        if heredocs and text.startswith('<<', i) and not text.startswith('<<<', i):
            match = re.match(r'<<(-?)\s*(?:\'([^\']+)\'|"([^"]+)"|([A-Za-z_][A-Za-z_0-9]*))', text[i:])
            if match:
                pending.append((next(x for x in match.groups()[1:] if x is not None), bool(match[1]), text[line_start:i]))
                i += len(match[0])
                continue
        if ch == '#' and starts_shell_word(text, i) and not (stack and stack[-1][0] == '}'):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            if not (i == 0 and text.startswith('#!')):
                spans.append((i, end))
            i = end
            continue
        i += 1
    return spans


def comments(text, language):
    if language == 'lean':
        return compiled_comments(text, True)
    if language == 'c':
        return compiled_comments(text)
    if language == 'python':
        return python_comments(text)
    if language in ('shell', 'perl'):
        return shell_comments(text, language == 'shell')
    result = []
    offset = 0
    for line in text.splitlines(keepends=True):
        if line.lstrip().startswith('#') and not (language == 'docker' and line.strip() == '# syntax=docker/dockerfile:1'):
            result.append((offset, offset + len(line.rstrip('\n'))))
        offset += len(line)
    return result


def language_for(path):
    if path.parts[:2] == ('integration', 'sudoers.d'):
        return None
    if path.suffix in ('.lean', '.c', '.h', '.py', '.sh'):
        return {'.lean': 'lean', '.c': 'c', '.h': 'c', '.py': 'python', '.sh': 'shell'}[path.suffix]
    if path.name.startswith('Dockerfile'):
        return 'docker'
    if path.name in ('.gitignore', '.dockerignore'):
        return 'ignore'
    return None


def main():
    paths = subprocess.check_output(['git', 'ls-files', '-z']).decode().split('\0')
    paths.append('scripts/check-no-comments.sh')
    failed = False
    for name in sorted(set(filter(None, paths))):
        path = pathlib.Path(name)
        language = language_for(path)
        if language and path.is_file():
            text = path.read_text()
            for start, end in comments(text, language):
                print(f'{path}:{text.count(chr(10), 0, start) + 1}: comment')
                failed = True
    if not failed:
        print('No comments found in tracked code files.')
    return int(failed)


if __name__ == '__main__':
    sys.exit(main())
PY
