import hashlib
import random


RECORDER = '/usr/local/bin/conformance-record'
USERS = ('ivan', 'judy', 'kate', 'root')
OPTIONS = (
    'env_reset', '!env_reset', 'set_home', 'always_set_home', 'use_pty', '!use_pty',
    'umask=0027', 'umask_override', 'closefrom=4', 'closefrom_override',
    'env_keep += "CF_KEEP CF_SPACE"', 'env_delete += "CF_DROP"',
    'env_check += "CF_CHECK"', 'secure_path=/usr/bin:/bin', 'set_logname',
    '!set_logname', 'requiretty', 'root_sudo', '!root_sudo', 'targetpw',
    'runaspw', 'rootpw', 'passwd_tries=1', 'passwd_timeout=0.1',
    'timestamp_timeout=0', 'timestamp_type=global', 'listpw=always',
    'verifypw=never', 'fqdn', 'insults', 'pwfeedback', 'visiblepw',
    'log_input', 'log_output', 'log_exit_status', 'log_allowed', '!log_allowed',
    'log_denied', '!log_denied', 'syslog_pid', 'syslog_maxlen=80',
    'mail_always', 'mail_badpass', 'mail_no_perms', 'mail_no_user',
    'mail_no_host', 'ignore_dot', 'path_info', 'fast_glob', 'match_group_by_gid',
    'runas_default=judy', 'runcwd=/tmp', 'runchroot=/', 'command_timeout=2',
    'lecture=always', 'authenticate', '!authenticate', 'sudoedit_checkdir',
    'sudoedit_follow', 'rlimit_nofile=256', 'rlimit_core=0',
)
TAGS = ('NOPASSWD', 'PASSWD', 'SETENV', 'NOSETENV', 'NOEXEC', 'EXEC',
        'MAIL', 'NOMAIL', 'FOLLOW', 'NOFOLLOW', 'LOG_INPUT', 'NOLOG_INPUT',
        'LOG_OUTPUT', 'NOLOG_OUTPUT')
BASE = [
    'Defaults lecture=never, timestamp_timeout=0, passwd_tries=1, !use_pty',
    'Defaults logfile="/var/log/conformance.log", loglinelen=0',
    'Defaults mailerpath=/usr/sbin/sendmail, mailto=root, !mail_badpass',
    'Defaults !mail_no_user, !mail_no_host, !mail_no_perms',
]
LIMITS = dict(
    RLIMIT_NOFILE=[(24, 24), (64, 1024), (1024, 1024)],
    RLIMIT_NPROC=[(64, 64), (4096, 4096)],
    RLIMIT_CORE=[(0, 0), (-1, -1)],
    RLIMIT_FSIZE=[(4096, 4096), (1 << 20, 1 << 20)],
    RLIMIT_STACK=[(256 << 10, 256 << 10), (8 << 20, -1)],
    RLIMIT_AS=[(1 << 30, 1 << 30), (8 << 30, 8 << 30)],
)


def empty_state():
    return dict(descriptors=[], close=[], limits={}, umask='022', cwd_state=None,
                env_raw=[], signals=[], hold_stdin=False)


def process_state(rng, scenario):
    state = empty_state()
    if rng.randrange(2):
        return state
    nofile = None
    if rng.randrange(3) == 0:
        for name in rng.sample(sorted(LIMITS), rng.randrange(1, 4)):
            state['limits'][name] = list(rng.choice(LIMITS[name]))
        if 'RLIMIT_NOFILE' in state['limits']:
            nofile = state['limits']['RLIMIT_NOFILE'][0]
    if rng.randrange(3) == 0:
        numbers = [fd for fd in (3, 4, 9, 63, 64, 255, 1000, 4095)
                   if nofile is None or fd < nofile - 4]
        for fd in sorted(rng.sample(numbers, min(len(numbers), rng.randrange(1, 4)))):
            state['descriptors'].append(dict(
                fd=fd, cloexec=bool(rng.randrange(2)),
                target=rng.choice(['/dev/null', '/etc/hostname', '/etc/passwd'])))
    if rng.randrange(5) == 0:
        state['close'] = sorted(rng.sample([0, 1, 2], rng.randrange(1, 3)))
    if rng.randrange(3) == 0:
        state['umask'] = rng.choice(['000', '002', '027', '077', '777'])
    if rng.randrange(5) == 0:
        state['cwd_state'] = rng.choice(['deleted', 'unreadable'])
    if rng.randrange(3) == 0:
        state['env_raw'] = rng.choice([
            ['CF_LARGE=' + 'x' * 100000],
            ['CF_MANY%04d=%s' % (i, 'v' * 60) for i in range(1500)],
            ['CF_BYTES=\udcff\udcfe'], ['CF_NOEQUALS'], ['=CF_EMPTY_NAME'],
            ['CF_KEEP=\udcc3'], ['CF_DUP=one', 'CF_DUP=two'],
        ])
    if rng.randrange(4) == 0:
        if scenario['argv'][-1:] == [RECORDER]:
            scenario['argv'] = scenario['argv'] + ['--sleep', '1']
        if scenario['feature'] == 'password' and rng.randrange(2):
            state['hold_stdin'] = True
        state['signals'] = [
            [round(rng.uniform(.05, .8), 2), name] for name in
            rng.choice([['SIGINT'], ['SIGTSTP', 'SIGCONT'], ['SIGTERM'], ['SIGHUP'],
                        ['SIGPIPE'], ['SIGQUIT'], ['SIGUSR1']])]
    return state


def generate(seed, count, mode, recorder_bytes):
    rng = random.Random(seed ^ (0x719 if mode == 'visudo' else 0))
    digests = {name: hashlib.new(name, recorder_bytes).hexdigest()
               for name in ('sha224', 'sha256', 'sha384', 'sha512')}
    for index in range(count):
        feature = index % 24
        user = rng.choice(USERS)
        lines = list(BASE)
        includes = {}
        argv = ['-n', RECORDER]
        name = 'plain'
        grant = f'{user} ALL=(ALL:ALL) NOPASSWD: ALL'
        if feature == 1:
            name = 'aliases'
            lines += [f'User_Alias PEOPLE = {user}, !bob',
                      'Runas_Alias TARGETS = root, judy, !bob',
                      'Host_Alias HOSTS = sudo-it, localhost, !otherhost',
                      f'Cmnd_Alias COMMANDS = {RECORDER}, /usr/bin/true']
            grant = 'PEOPLE HOSTS=(TARGETS:ALL) NOPASSWD: COMMANDS'
        elif feature == 2:
            name = 'negation'
            grant += rng.choice([f', !{RECORDER}', ', !/usr/bin/false',
                                 f', !ALL, {RECORDER}'])
        elif feature == 3:
            name = 'tags'
            grant = f'{user} ALL=(ALL:ALL) NOPASSWD: {rng.choice(TAGS)}: ALL'
        elif feature == 4:
            name = 'command-options'
            option = rng.choice(['CWD=/tmp', 'CWD=*', 'CHROOT=/', 'CHROOT=*',
                                 'TIMEOUT=2', 'NOTBEFORE=20200101000000Z',
                                 'NOTAFTER=20400101000000Z',
                                 'NOTAFTER=20200101000000Z'])
            grant = f'{user} ALL=(ALL:ALL) {option} NOPASSWD: ALL'
        elif feature in (5, 6, 7):
            name = 'defaults-binding'
            binding = rng.choice(['', ':' + user, '@sudo-it', '>root', '!' + RECORDER])
            lines.append('Defaults' + binding + ' ' + rng.choice(OPTIONS))
        elif feature == 8:
            name = 'digest'
            algorithm = rng.choice(list(digests))
            digest = digests[algorithm]
            if rng.randrange(3) == 0:
                digest = '0' * len(digest)
            grant = f'{user} ALL=(ALL:ALL) NOPASSWD: {algorithm}:{digest} {RECORDER}'
        elif feature == 9:
            name = 'patterns'
            pattern = rng.choice(['/usr/local/bin/conformance-*',
                                  '^/usr/local/bin/conformance-record$',
                                  RECORDER + ' arg*', RECORDER + ' ^arg[0-9]+$'])
            grant = f'{user} ALL=(ALL:ALL) NOPASSWD: {pattern}'
            argv.append(rng.choice(['arg42', 'arg x', 'other']))
        elif feature == 10:
            name = 'include'
            includes['/etc/conformance-include'] = grant + '\n'
            grant = '@include /etc/conformance-include'
        elif feature == 11:
            name = 'includedir'
            includes['/etc/conformance.d/10-policy'] = grant + '\n'
            includes['/etc/conformance.d/ignored.conf'] = 'not valid sudoers\n'
            grant = '@includedir /etc/conformance.d'
        elif feature == 12:
            name = 'invalid-syntax'
            lines.append(rng.choice(['User_Alias = broken', 'Defaults ,',
                                     'ivan ALL=(root NOPASSWD: ALL',
                                     'Cmnd_Alias BROKEN =']))
        elif feature == 13:
            name = 'alias-errors'
            lines.append(rng.choice(['User_Alias UNUSED = MISSING',
                                     'User_Alias LOOP = LOOP']))
        elif feature == 14:
            name = 'invalid-default'
            lines.append('Defaults timestamp_timeout=not_a_number')
        elif feature == 15:
            name = 'listing'
            argv = [rng.choice(['-l', '-ll']), '-n']
            if rng.randrange(2):
                argv += ['-U', rng.choice(USERS)]
        elif feature == 16:
            name = 'validation-cache'
            argv = rng.choice([[rng.choice(['-v', '-k', '-K']), '-n'], ['-h'], ['--help'],
                               ['-V'], ['-k', '-n', RECORDER], ['-K', RECORDER]])
        elif feature == 17:
            name = 'runas'
            argv = ['-n', '-u', rng.choice(['root', 'judy', '#0', '#65534']),
                    '-g', rng.choice(['root', 'adm', 'judy']), RECORDER]
        elif feature == 18:
            name = 'shell-environment'
            argv = ['-n'] + rng.choice([['-s'], ['-i'], ['-E'],
                                       ['--preserve-env=CF_KEEP,CF_SPACE']]) + [RECORDER]
        elif feature == 19:
            name = 'directory-descriptors-host'
            argv = ['-n'] + rng.choice([['-D', '/tmp'], ['-C', '4'],
                                       ['-h', 'sudo-it', '-l']])
            if '-l' not in argv:
                argv += [RECORDER]
        elif feature == 20:
            name = 'edit'
            argv = ['-n', '-e', '/tmp/conformance-edit']
        elif feature == 21:
            name = 'arguments-environment'
            argv = ['-n', 'CF_KEEP=override', 'CF_NEW=a b', RECORDER,
                    rng.choice(['quotes"', "single'quote", 'space value', 'line\nbreak',
                                'tab\tvalue', 'back\\slash', 'é', '*?[]', '', '$HOME;true',
                                '\x01\x7f', 'bad\udcffbyte'])]
        elif feature == 22:
            name = 'password'
            grant = f'{user} ALL=(ALL:ALL) PASSWD: ALL'
            argv = ['-S', '-p', 'conformance-password: ', RECORDER]
        elif feature == 23:
            name = 'logging'
            lines.append('Defaults log_format=' + rng.choice(['sudo', 'json_compact']))
            lines.append('Defaults log_exit_status, syslog_pid')
        lines.append(grant)
        password = (user + 'pw\n') if rng.randrange(2) else 'wrong-password\n'
        scenario = dict(index=index, mode=mode, feature=name, user=user, lines=lines,
                        includes=includes, argv=argv, stdin=password if '-S' in argv else '',
                        terminal=(index % 31 == 0),
                        env={'CF_KEEP': 'kept', 'CF_DROP': 'drop', 'CF_CHECK': 'safe',
                             'CF_SPACE': 'space value', 'EDITOR': '/usr/bin/true',
                             'SUDO_EDITOR': '/usr/bin/true'})
        scenario['state'] = process_state(rng, scenario) if mode == 'sudo' else empty_state()
        if mode == 'visudo':
            scenario['argv'] = rng.choice([['-c'], ['-c', '-f', '/etc/sudoers']])
            scenario['terminal'] = False
            if index % 5 == 0:
                row = rng.randrange(len(lines))
                line = lines[row]
                position = rng.randrange(len(line) + 1)
                mark = rng.choice([':', '(', '!', '\\', ' '])
                lines[row] = line[:position] + mark + line[position:]
                scenario['feature'] = 'mutated-' + name
        yield scenario
