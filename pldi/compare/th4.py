"""The four formalizations of Amy, Ross and Wesley [2024]: code lines and
check times, all measured on one machine.

    python3 th4.py ../.. th4.json      # in WSL, under the Agda lock
    TH4_DRY=1 python3 th4.py ../.. x   # print the code counts only
    TH4_LINES=1 python3 th4.py ../.. th4.json   # recount, keep the times

The four are two Agda-Lean pairs:

  * Agda Examples/Groups/CCX+H-3qubit-Tietze, the row of Table 1, against
    Lean QCert/ToffoliHadamard, written from the paper (Figure 6's row);
  * Agda Examples/Groups/CCX+H-3qubit-RS, a second Agda proof (by
    translation into Li-Ross-Selinger's presentations), against Lean
    QCert/ToffoliHadamardRS, its translation to Lean: one proof in two
    assistants.

Code lines are counted as loc.py counts them (tracked files, blank lines
and comments excluded; `generated` by loc.kind), and so are code
characters, the non-blank characters outside comments, which do not
depend on how a generator lays out its output (one rewrite step a line in
the Agda derivations, several in the Lean ones).  Check times are measured
as agdatime.py and leantime.py measure them, folder by folder: before each
timing the folder's own interfaces (Agda) or build artifacts (Lean) are
removed and its dependencies are left built, so that only the folder is
checked.  An Agda folder is checked in one process through a root module
importing all its tracked modules, with --profile=modules, and its time is
the sum of the times Agda reports for its own modules; a Lean folder is
built by `LEAN_NUM_THREADS=2 lake build <its modules>`, and its time is the
wall time.  Each timing is preceded by an untimed check of the same
modules, which builds whatever the folder imports.  The script records the
CPU seconds Lean or Agda processes of other projects used during each
timing (`foreign_cpu_s`), the load, and the machine.  Agda runs with
+RTS -M<heap> (TH4_HEAP, default 6G).
"""
import collections, fcntl, glob, json, os, platform, re, subprocess, sys, threading, time

ROOT = os.path.abspath(sys.argv[1])
OUT = sys.argv[2]
HEAP = os.environ.get('TH4_HEAP', '6G')
LENV = dict(os.environ, LEAN_NUM_THREADS='2',
            PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])

# loc.py's definitions (not its main): files, count, kind, TRACKED.
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, 'loc.py'), encoding='utf-8').read().split('def main')[0]
sys.argv = [sys.argv[0], ROOT, os.devnull]
exec(src)
LEANDIR = os.path.join(ROOT, 'Lean')   # after loc.py, which defines LEAN

FORMS = [
    ('Agda Tietze', 'agda', 'Examples/Groups/CCX+H-3qubit-Tietze'),
    ('Lean paper', 'lean', 'Lean/QCert/ToffoliHadamard'),
    ('Agda RS', 'agda', 'Examples/Groups/CCX+H-3qubit-RS'),
    ('Lean RS', 'lean', 'Lean/QCert/ToffoliHadamardRS'),
]


def sources(lang, folder):
    ext = '.agda' if lang == 'agda' else '.lean'
    return sorted(f for f in set(files([folder], ext))
                  if not (lang == 'lean' and '/gen/' in f.replace(os.sep, '/')))


def chars(path, lang):
    """Non-blank characters outside comments, by count's scanner."""
    op, cl = ('{-', '-}') if lang == 'agda' else ('/-', '-/')
    depth = n = 0
    for ln in open(path, encoding='utf-8', errors='replace'):
        s, i = ln.strip(), 0
        while i < len(s):
            if depth > 0:
                if s.startswith(op, i):
                    depth += 1; i += 2
                elif s.startswith(cl, i):
                    depth -= 1; i += 2
                else:
                    i += 1
                continue
            if s.startswith('--', i):
                break
            if s.startswith(op, i):
                depth += 1; i += 2
                continue
            if not s[i].isspace():
                n += 1
            i += 1
    return n


def lines(lang, folder):
    tot, gen, ng = collections.Counter(), collections.Counter(), 0
    fs = sources(lang, folder)
    for f in fs:
        c = dict(count(f, lang), chars=chars(f, lang))
        tot.update(c)
        if kind(f) == 'generated':
            gen.update(c); ng += 1
    return dict(files=len(fs), code=tot['code'], comment=tot['comment'],
                generated_files=ng, generated_code=gen['code'],
                written_code=tot['code'] - gen['code'],
                chars=tot['chars'], generated_chars=gen['chars'])


REAL = os.path.realpath(ROOT)
TICK = os.sysconf('SC_CLK_TCK')


def foreign_ticks():
    out = {}
    for pid in os.listdir('/proc'):
        if not pid.isdigit():
            continue
        try:
            cmd = open(f'/proc/{pid}/cmdline', 'rb').read().replace(b'\0', b' ').decode()
            if not re.search(r'/(lean|lake|agda) ', cmd + ' '):
                continue
            if os.path.realpath(os.readlink(f'/proc/{pid}/cwd')).startswith(REAL) or ROOT in cmd:
                continue
            f = open(f'/proc/{pid}/stat').read().rsplit(')', 1)[1].split()
            out[pid] = int(f[11]) + int(f[12])
        except OSError:
            continue
    return out


class Foreign:
    def __init__(self):
        self.last = foreign_ticks(); self.used = 0; self.stop = threading.Event()
        self.th = threading.Thread(target=self.run, daemon=True); self.th.start()

    def poll(self):
        now = foreign_ticks()
        self.used += sum(t - self.last.get(p, 0) for p, t in now.items())
        self.last = now

    def run(self):
        while not self.stop.wait(2):
            self.poll()

    def done(self):
        self.stop.set(); self.th.join(); self.poll()
        return round(self.used / TICK, 1)


PROFILE = re.compile(r'^(\S+)\s+([\d,]+)ms\s*$')


def agda_modules(folder):
    return [os.path.relpath(f, ROOT)[:-len('.agda')].replace(os.sep, '.')
            for f in sources('agda', folder)]


def agda_check(tag, mods, log):
    root = f'Th4{tag}'
    path = os.path.join(ROOT, root + '.agda')
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(f'module {root} where\n' + ''.join(f'import {m}\n' for m in mods))
    t0 = time.monotonic()
    with open(log, 'w') as fh:
        rc = subprocess.run(['/usr/bin/time', '-f', 'maxrss %M KB', 'agda', '--profile=modules',
                             root + '.agda', '+RTS', f'-M{HEAP}', '-RTS'],
                            cwd=ROOT, stdout=fh, stderr=subprocess.STDOUT).returncode
    secs = time.monotonic() - t0
    os.remove(path)
    for f in glob.glob(os.path.join(ROOT, '_build', '*', 'agda', root + '.agdai')):
        os.remove(f)
    prof, rss = {}, None
    for ln in open(log, encoding='utf-8', errors='replace'):
        m = PROFILE.match(ln)
        if m and m.group(1) not in ('Total', 'Miscellaneous'):
            prof[m.group(1)] = int(m.group(2).replace(',', ''))
        elif ln.startswith('maxrss'):
            rss = int(ln.split()[1])
    return rc, round(secs, 2), rss, prof


def time_agda(name, folder):
    mods = agda_modules(folder)
    tag = re.sub(r'\W', '', name)
    logs = os.path.expanduser('~/th4-logs'); os.makedirs(logs, exist_ok=True)
    rc, warm, _, _ = agda_check(tag, mods, os.path.join(logs, tag + '-warm.log'))
    if rc != 0:
        raise SystemExit(f'{name}: the untimed check failed; see {logs}')
    for m in mods:
        for f in glob.glob(os.path.join(ROOT, '_build', '*', 'agda', m.replace('.', '/') + '.agdai')):
            os.remove(f)
    fo = Foreign(); load0 = os.getloadavg()[0]
    rc, wall, rss, prof = agda_check(tag, mods, os.path.join(logs, tag + '.log'))
    own = {m: prof[m] for m in mods if m in prof}
    return dict(seconds=round(sum(own.values()) / 1000, 2), wall_s=wall, rc=rc,
                modules=len(mods), profiled=len(own), max_rss_kb=rss,
                load_start=round(load0, 2), foreign_cpu_s=fo.done(),
                slowest=sorted(own.items(), key=lambda kv: -kv[1])[:5],
                date=time.strftime('%Y-%m-%d %H:%M'))


def time_lean(name, folder):
    mods = [os.path.relpath(f, LEANDIR)[:-len('.lean')].replace(os.sep, '.')
            for f in sources('lean', folder)]
    tag = re.sub(r'\W', '', name)
    logs = os.path.expanduser('~/th4-logs'); os.makedirs(logs, exist_ok=True)
    with open(os.path.join(logs, tag + '-warm.log'), 'w') as fh:
        rc = subprocess.run(['lake', 'build'] + mods, cwd=LEANDIR, env=LENV,
                            stdout=fh, stderr=subprocess.STDOUT).returncode
    if rc != 0:
        raise SystemExit(f'{name}: the untimed build failed; see {logs}')
    build = os.path.join(LEANDIR, '.lake', 'build')
    for m in mods:
        for d in ('lib/lean', 'ir'):
            for f in glob.glob(os.path.join(build, d, m.replace('.', '/') + '.*')):
                os.remove(f)
    fo = Foreign(); load0 = os.getloadavg()[0]; t0 = time.monotonic()
    with open(os.path.join(logs, tag + '.log'), 'w') as fh:
        rc = subprocess.run(['lake', 'build'] + mods, cwd=LEANDIR, env=LENV,
                            stdout=fh, stderr=subprocess.STDOUT).returncode
    secs = time.monotonic() - t0
    return dict(seconds=round(secs, 2), rc=rc, modules=len(mods),
                load_start=round(load0, 2), foreign_cpu_s=fo.done(),
                date=time.strftime('%Y-%m-%d %H:%M'))


def main():
    rev = subprocess.run(['git', '-C', ROOT, 'rev-parse', '--short', 'HEAD'],
                         capture_output=True, text=True).stdout.strip()
    cpu = next((ln.split(':', 1)[1].strip() for ln in open('/proc/cpuinfo')
                if ln.startswith('model name')), platform.processor())
    mem = int(next(ln.split()[1] for ln in open('/proc/meminfo') if ln.startswith('MemTotal')))
    agda = subprocess.run(['agda', '--version'], capture_output=True, text=True).stdout.split('\n')[0]
    lean = subprocess.run(['lean', '--version'], capture_output=True, text=True, env=LENV,
                          cwd=LEANDIR).stdout.strip()
    rec = dict(run=dict(date=time.strftime('%Y-%m-%d %H:%M %z'), revision=rev, cpu=cpu,
                        logical_cpus=os.cpu_count(), mem_gib=round(mem / 2**20, 1),
                        agda=agda, rts=f'-M{HEAP}', lean=lean), forms={})
    for name, lang, folder in FORMS:
        rec['forms'][name] = dict(folder=folder, lang=lang, **lines(lang, folder))
    if os.environ.get('TH4_DRY'):           # the code counts only
        print(json.dumps(rec['forms'], indent=1, ensure_ascii=False))
        return
    if os.environ.get('TH4_LINES'):         # recount, keep the run and the times
        old = json.load(open(OUT, encoding='utf-8'))
        for name, f in rec['forms'].items():
            f['check'] = old['forms'][name]['check']
        old['forms'] = rec['forms']
        json.dump(old, open(OUT, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
        return
    lock =open(os.path.expanduser('~/.qcert-build-1.lock'), 'w')
    fcntl.flock(lock, fcntl.LOCK_EX)
    for name, lang, folder in FORMS:
        t = time_agda(name, folder) if lang == 'agda' else time_lean(name, folder)
        rec['forms'][name]['check'] = t
        json.dump(rec, open(OUT, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
        f = rec['forms'][name]
        print(f"{name:12} {f['files']:4} files  {f['code']:6} code ({f['generated_code']} generated)  "
              f"{t['seconds']:8.2f} s  rc={t['rc']}  foreign_cpu={t['foreign_cpu_s']} s", flush=True)


main()
