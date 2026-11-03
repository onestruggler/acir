"""Lines of code of the Agda and Lean developments of Table 1.

For every source file: physical lines, blank lines, comment lines and code
lines (Agda `--`/`{- -}`, Lean `--`/`/- -/`; block comments may nest).
Writes loc.json: per row, per system, the number of files and the totals.
"""
import json, os, re, sys, collections

ROOT = sys.argv[1]
AGDA = {
    'Greylyn': ['Examples/Groups/Clifford+T-2qubit-TwoLevel'],
    'BianSelingerUn': ['Examples/Groups/Clifford+CS-TwoLevel'],
    'LiRossSelinger': ['Examples/Groups/CCX+HH-TwoLevel'],
    'HadamardPi': ['Examples/Groups/Real-Clifford+CH-TwoLevel'],
    'Clement2019': ['Examples/Groups/Real-Clifford+CH-TwoLevel-Clement'],
    'SelingerClifford': ['Examples/Groups/Qubit-Clifford'],
    'QuditClifford': ['Examples/Groups/Symplectic', 'Examples/Groups/ProjectiveClifford/Qupit',
                      'Examples/Groups/Clifford+MinusOne', 'Examples/Groups/ProjectivePauli',
                      'Examples/Groups/Qupit-Clifford'],
    'RealStabilizer': ['Examples/Groups/Real-Clifford'],
    'CNOTDihedral': ['Examples/Groups/CNOT+Dihedral'],
    'PhaseAffine': ['Examples/Groups/Qupit-Phase-Affine'],
    'CliffordT2': ['Examples/Groups/Clifford+T-2qubit'],
    'CliffordCS3': ['Examples/Groups/Clifford+CS-3qubit'],
    'RealCliffordCH': ['Examples/Groups/Real-Clifford+CH'],
    'ToffoliHadamard': ['Examples/Groups/CCX+HH-3qubit'],
    'QutritClifford': ['Examples/Groups/Qutrit-Clifford'],
    'Minimality': ['Examples/Independence'],
    '(shared)': ['Word', 'Presentation', 'Circuit', 'Normalization', 'Examples/Construct',
                 'Examples/Groups/Symmetric', 'Examples/Groups/Cyclic', 'Examples/Groups/Trivial',
                 'Examples/Groups/Pauli', 'Notations.agda'],
}
ROWS = [k for k in AGDA if k != '(shared)']
LEAN = {k: ['Lean/QCert/' + k] for k in ROWS}
LEAN['(shared)'] = ['Lean/QCert/Presentation.lean', 'Lean/QCert/Circuit', 'Lean/QCert/Exact',
                    'Lean/QCert/Matrix', 'Lean/QCert/NumberTheory', 'Lean/QCert/Synthesis.lean']

def files(paths, ext):
    for p in paths:
        q = os.path.join(ROOT, p)
        if os.path.isfile(q):
            yield q
        for r, _, fs in os.walk(q):
            for f in fs:
                if f.endswith(ext):
                    yield os.path.join(r, f)

def count(path, lang):
    text = open(path, encoding='utf-8', errors='replace').read()
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    op, cl = ('{-', '-}') if lang == 'agda' else ('/-', '-/')
    depth = 0
    blank = comment = code = 0
    for ln in lines:
        s = ln.strip()
        if not s and depth == 0:
            blank += 1
            continue
        has_code = False
        i = 0
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
                has_code = True
            i += 1
        if has_code:
            code += 1
        elif s or depth > 0:
            comment += 1
        else:
            blank += 1
    return dict(lines=len(lines), blank=blank, comment=comment, code=code)

def main():
    out = {}
    for lang, table, ext in (('agda', AGDA, '.agda'), ('lean', LEAN, '.lean')):
        for row, paths in table.items():
            tot = collections.Counter(); n = 0
            for f in sorted(set(files(paths, ext))):
                if lang == 'lean' and os.sep + 'gen' + os.sep in f.replace('/', os.sep):
                    continue  # generator templates
                n += 1
                tot.update(count(f, lang))
            out.setdefault(row, {})[lang] = dict(files=n, **tot)
    json.dump(out, open(sys.argv[2], 'w'), indent=1)
    print(f"{'row':18} {'A files':>7} {'A code':>7}   {'L files':>7} {'L code':>7}")
    for row in out:
        a, l = out[row]['agda'], out[row]['lean']
        print(f"{row:18} {a['files']:7} {a['code']:7}   {l['files']:7} {l['code']:7}")

main()
