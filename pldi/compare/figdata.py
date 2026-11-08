"""Combine loc.json and features.json with the check times of Table 1
into figdata.json (read by mkfig.py), and print the totals quoted in the
text of Section 3.3 and in tab:compare.

Inputs: loc.json, features.json, agdatime.json, leantime.json and, for
the two Toffoli--Hadamard rows of panel (a), th4.json and part.json (this
directory).  The Agda check times are read from agdatime.json
(agdatime.py), the Lean times from leantime.json (leantime.py), and both
are printed in the form Table 1 quotes them.
"""
import json, os, sys

here = os.path.dirname(os.path.abspath(__file__))
loc = json.load(open(os.path.join(here, 'loc.json')))
feat = json.load(open(os.path.join(here, 'features.json')))
ltime = json.load(open(os.path.join(here, 'leantime.json')))
atime = json.load(open(os.path.join(here, 'agdatime.json')))

# Table 1 order, label, Agda time (s, as recorded on 22 October), Lean time
# (s, of the 1 November run); both replaced below, from agdatime.json and
# leantime.json.
ROWS = [
    ('Greylyn', r'$U_n(\Z[1/\sqrt2,i])$', 42, 115.62),
    ('BianSelingerUn', r'$U_n(\Z[1/2,i])$', 62, 140.99),
    ('LiRossSelinger', r'$O_n(\Z[1/2])$, $L_n$', 79, 157.76),
    ('HadamardPi', r'$O_n(\Z[1/\sqrt2])$, Hadamard-$\Pi$', 44, 315.70),
    ('Clement2019', r"$O_n(\Z[1/\sqrt2])$, Cl\'ement", 64, 52.94),
    ('SelingerClifford', 'Clifford', 34, 103.61),
    ('QuditClifford', r'Clifford, odd prime $p$', 546, 166.92),
    ('RealStabilizer', 'real stabilizer', 35, 62.87),
    ('CNOTDihedral', 'CNOT-dihedral', 24, 77.29),
    ('PhaseAffine', r'phase-affine, prime $d$', 61, 176.59),
    ('CliffordT2', 'two-qubit Clifford+T', 118, 275.40),
    ('CliffordCS3', 'three-qubit Clifford+CS', 250, 1162.66),
    ('RealCliffordCH', 'real Clifford+CH', 405, 8868.59),
    ('ToffoliHadamard', r'Toffoli--Hadamard$^{\ast}$', 102, 328.84),
    ('QutritClifford', 'qutrit Clifford', 282, 164.76),
    ('Minimality', 'minimality, six fragments', 183, 300.20),
]

ROWS = [(k, label, atime['rows'][k]['seconds'], ltime['units'][k]['seconds'])
        for k, label, _, _ in ROWS]
arun = atime['run']
print(f"Agda run {arun['date']} at {arun['revision']}, {arun['modules']} modules, {arun['cpu']}, "
      f"{arun['logical_cpus']} CPUs, {arun['mem_gib']} GiB, {arun['agda']}, {arun['rts']}")
print('Agda shared library', atime['rows']['(shared)'],
      '; wall per unit', {u: v['seconds'] for u, v in atime['units'].items()},
      '; peak RSS (GB)', {u: round((v['max_rss_kb'] or 0) / 2**20, 1) for u, v in atime['units'].items()},
      '; left out', {u: v.get('excluded') for u, v in atime['units'].items() if v.get('excluded')},
      '; other projects (CPU s)', {u: v['foreign_cpu_s'] for u, v in atime['units'].items()
                                    if v['foreign_cpu_s']},
      '; modules profiled', {k: (v['profiled'], v['modules']) for k, v in atime['rows'].items()
                             if v['profiled'] != v['modules']})
slow = sorted(((v['ms'], m, v['unit']) for m, v in atime['modules'].items()), reverse=True)[:8]
print('slowest Agda modules', [(m, round(ms / 1000, 1), u) for ms, m, u in slow])
run = ltime['run']
shared = {u: v['seconds'] for u, v in ltime['units'].items()
          if u not in {r[0] for r in ROWS}}
print(f"Lean run {run['date']} at {run['revision']}, {run['modules']} modules, {run['cpu']}, "
      f"{run['logical_cpus']} CPUs, {run['mem_gib']} GiB")
print('shared units', shared)
print(f"timed total {sum(v['seconds'] for v in ltime['units'].values()):.2f} s; failed",
      {u: v['failed'] for u, v in ltime['units'].items() if v['failed'] or v['rc']})
print('other projects\' Lean during a unit (CPU s):',
      {u: v['foreign_cpu_s'] for u, v in ltime['units'].items() if v.get('foreign_cpu_s')},
      '; units of the first run never re-timed:',
      [u for u, v in ltime['units'].items() if 'foreign_procs' in v])

# Panel (a) of the figure counts, for Toffoli--Hadamard, the one proof in
# both assistants (tab:th4's second pair, measured by th4.py) rather than the
# two proofs of Table 1's row, which take different routes; panel (b) and
# the totals of tab:compare stay those of Table 1's folders.
th4 = json.load(open(os.path.join(here, 'th4.json')))['forms']
FIG_LOC = {'ToffoliHadamard': (th4['Agda RS'], th4['Lean RS'])}

lines = []
tot = dict(ac=0, lc=0, af=0, lf=0)
for i, (key, label, at, lt) in enumerate(ROWS + [('(shared)', 'shared library', None, None)]):
    a, l = loc[key]['agda'], loc[key]['lean']
    fa, fl = FIG_LOC.get(key, (a, l))
    lines.append((i, key, label, fa['code'], fl['code'], at, lt, fa['files'], fl['files']))
    if key != '(shared)':
        tot['ac'] += a['code']; tot['lc'] += l['code']
        tot['af'] += a['files']; tot['lf'] += l['files']

print(f"{'row':18} {'Agda':>7} {'Lean':>7}  {'Agda s':>6} {'Lean s':>8}")
for i, key, label, ac, lc, at, lt, af, lf in lines:
    print(f"{key:18} {ac:7} {lc:7}  {at or '':>6} {lt or '':>8}")
print('totals (16 rows, Table 1 folders)', tot)
for key, (fa, fl) in FIG_LOC.items():
    print(f"panel (a) {key}: {fa['folder']} {fa['code']} and {fl['folder']} {fl['code']} "
          f"in place of {loc[key]['agda']['code']} and {loc[key]['lean']['code']}")
print('Lean shorter in', sum(1 for r in lines[:-1] if r[4] < r[3]), 'of 16 rows; longer in',
      [r[1] for r in lines[:-1] if r[4] > r[3]])
print('Lean faster in', [r[1] for r in lines[:-1] if r[6] < r[5]])
big = max(lines[:-1], key=lambda r: r[6])
print(f"check times: Agda {sum(r[5] for r in lines[:-1]):.2f} s, Lean {sum(r[6] for r in lines[:-1]):.2f} s; "
      f"without {big[1]}: Agda {sum(r[5] for r in lines[:-1] if r is not big):.2f} s, "
      f"Lean {sum(r[6] for r in lines[:-1] if r is not big):.2f} s")
print('Lean/Agda ratio per row', {r[1]: round(r[6] / r[5], 1) for r in lines[:-1]})

sumf = lambda lang, k: sum(feat[r[0]][lang].get(k, 0) for r in ROWS)
print('lean, all files: by', sumf('lean', 'by_all'), 'automation', sumf('lean', 'automation_all'))
print('lean by', sumf('lean', 'by'), 'automation', sumf('lean', 'automation'),
      'noncomputable declarations: written files', sumf('lean', 'noncomputable_decl'),
      'all files', sumf('lean', 'noncomputable_decl_all'),
      'theorems', sumf('lean', 'theorem'), 'decide+kernel', sumf('lean', 'decide_kernel'))
print('agda with', sumf('agda', 'with'), 'solver', sumf('agda', 'solver'),
      'safe files', sumf('agda', 'safe'), 'of', sumf('agda', 'files'),
      'postulates', sumf('agda', 'postulate_any'))
print('libs', {k: len(v) for k, v in feat['_libs'].items()})

# A second Toffoli--Hadamard row, panel (a) only: the Lean translation of
# CCX+H-3qubit-Tietze as far as it went, against the same Agda modules
# (part.json, written by part.py); it has no check times.
part = json.load(open(os.path.join(here, 'part.json')))['totals']
k = next(i for i, r in enumerate(lines) if r[1] == 'ToffoliHadamard') + 1
extra = (k, 'ToffoliHadamardTietzePart', r'Toffoli--Hadamard$^{\dagger}$', part['agda']['code'],
         part['lean']['code'], None, None, part['agda']['files'], part['lean']['files'])
rows = lines[:k] + [extra] + [(r[0] + 1,) + tuple(r[1:]) for r in lines[k:]]
print('panel (a) row', extra[2], extra[3:5], 'modules', extra[7:])
json.dump(dict(rows=rows, totals=tot), open(os.path.join(here, 'figdata.json'), 'w'), indent=1)
