"""Combine loc.json and features.json with the check times of Table 1
into figdata.json (read by mkfig.py), and print the totals quoted in the
text of Section 3.3 and in tab:compare.

Inputs: loc.json, features.json (this directory).  The check times are
those of Table 1 (pldi/qcert.tex, tab:corpus).
"""
import json, os, sys

here = os.path.dirname(os.path.abspath(__file__))
loc = json.load(open(os.path.join(here, 'loc.json')))
feat = json.load(open(os.path.join(here, 'features.json')))

# Table 1 order, label, Agda time (s), Lean time (s).
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
    ('ToffoliHadamard', r'Toffoli--Hadamard', 102, 328.84),
    ('QutritClifford', 'qutrit Clifford', 282, 164.76),
    ('Minimality', 'minimality, six fragments', 183, 300.20),
]

def k(x):
    return round(x / 1000, 2)

lines = []
tot = dict(aw=0, ag=0, ap=0, lw=0, lg=0, af=0, lf=0)
for i, (key, label, at, lt) in enumerate(ROWS + [('(shared)', 'shared library', None, None)]):
    a, l = loc[key]['agda'], loc[key]['lean']
    ac, ag, ap = a['all']['code'], a['generated'].get('code', 0), a['ported'].get('code', 0)
    lc, lg = l['all']['code'], l['generated'].get('code', 0)
    aw, lw = ac - ag - ap, lc - lg
    lines.append((i, key, label, aw, ag + ap, lw, lg, at, lt, a['files'], l['files']))
    if key != '(shared)':
        tot['aw'] += aw; tot['ag'] += ag; tot['ap'] += ap; tot['lw'] += lw; tot['lg'] += lg
        tot['af'] += a['files']; tot['lf'] += l['files']

print(f"{'row':18} {'Agda w':>7} {'Agda g+p':>8} {'Lean w':>7} {'Lean g':>7}  {'Agda s':>6} {'Lean s':>8}")
for i, key, label, aw, agp, lw, lg, at, lt, af, lf in lines:
    print(f"{key:18} {aw:7} {agp:8} {lw:7} {lg:7}  {at or '':>6} {lt or '':>8}")
print('totals (16 rows)', tot)
print('Lean written < Agda written in',
      sum(1 for r in lines[:-1] if r[5] < r[3]), 'of 16 rows')
print('Lean faster in', [r[1] for r in lines[:-1] if r[8] < r[7]])

sumf = lambda lang, k: sum(feat[r[0]][lang].get(k, 0) for r in ROWS)
print('lean by', sumf('lean', 'by'), 'automation', sumf('lean', 'automation'),
      'noncomputable declarations (all files)', sumf('lean', 'noncomputable_decl_all'),
      'theorems', sumf('lean', 'theorem'), 'decide+kernel', sumf('lean', 'decide_kernel'))
print('agda with', sumf('agda', 'with'), 'solver', sumf('agda', 'solver'),
      'safe files', sumf('agda', 'safe'), 'of', sumf('agda', 'files'),
      'postulates', sumf('agda', 'postulate_any'))
print('libs', {k: len(v) for k, v in feat['_libs'].items()})

json.dump(dict(rows=lines, totals=tot), open(os.path.join(here, 'figdata.json'), 'w'), indent=1)
