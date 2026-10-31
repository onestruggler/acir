"""Emit independently checked three-qubit derivations from the proof table.

The only leaves are Figure 2 axioms, proved two-qubit completeness, and
transport through a face action whose relation obligations are themselves
earlier checked derivations. Floating-point matrix tests are not emitted.
"""
from pathlib import Path
import pickle
import re
import sys
from emit import expanded, exp_steps
from leanemit import RuleEmitter
from three import PAIR
from fig2 import rels2
from twoemit import AXNAME

ROOT = Path(__file__).resolve().parent.parent
CACHE = ROOT.parents[1] / '.handover-scratch/cs3/phase-c-current.pkl'
FMT = dict(zip(['i', 'K0', 'K1', 'K2', 'S0', 'S1', 'S2', 'C01', 'C12'],
               ['Gen.i', 'Gen.K₀', 'Gen.K₁', 'Gen.K₂', 'Gen.S₀', 'Gen.S₁', 'Gen.S₂', 'Gen.CS₀₁', 'Gen.CS₁₂']))


def word2(w):
    return '(FreeMonoid.ofList [' + ', '.join('Two.Gen2.' + z for z in w) + '])'


def ax_term(nm):
    if nm.startswith('comm_i_'):
        ax = 'Rel.comm_i %s (by decide)' % FMT[nm[7:]]
    elif nm.startswith('comm_loc_'):
        a, b, q, r = nm[9:]
        ax = 'Rel.comm_loc .%s .%s %s %s (by decide)' % (a, b, q, r)
    elif nm.startswith('comm_0_12_'):
        ax = 'Rel.comm_0_12 .%s' % nm[-1]
    elif nm.startswith('comm_2_01_'):
        ax = 'Rel.comm_2_01 .%s' % nm[-1]
    elif '_' in nm:
        a, n = nm.split('_')
        ax = 'Rel.%s %s' % (a, n)
    else:
        ax = 'Rel.' + nm
    return 'Rule.ofDerivable _ _ (Derivable.of (%s))' % ax


def needed(T, targets):
    seen = set()
    stack = [t for t in targets if t is not None]
    while stack:
        k = stack.pop()
        if k in seen:
            continue
        seen.add(k)
        j = T.eqs[k][2]
        if j[0] == 'der':
            stack.extend(kk for _, kk, _ in j[1])
        elif j[0] == 'face':
            stack.extend(e for e in j[5] if e is not None)
    return sorted(seen)


def write_source(path, content):
    """Replace generated sources atomically, also on Windows-mounted trees."""
    if path.exists() and path.read_text(encoding='utf-8') == content:
        return
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(content, encoding='utf-8', newline='\n')
    tmp.replace(path)


def dependency_imports(dest):
    """Allow derivation batches to overlap the independent pair checks."""
    files = sorted(dest.glob('Pair*.lean')) + sorted(dest.glob('Part*.lean'))
    owner = {}
    for path in files:
        for name in re.findall(r'^def (r\d+)\b', path.read_text(encoding='utf-8'), re.M):
            owner[name] = path.stem
    for path in sorted(dest.glob('Part*.lean')):
        i = int(path.stem[4:])
        if i == 0:
            continue
        source = path.read_text(encoding='utf-8')
        body = source[source.index('set_option'):]
        lanes = {}
        for name in re.findall(r'\br\d+\b', body):
            module = owner[name]
            if module.startswith('Pair'):
                j = int(module[4:])
                lanes[j % 4] = max(j, lanes.get(j % 4, -1))
        imports = ['import QCert.CliffordCS3.Cert.Part%03d' % (i - 1)]
        imports += ['import QCert.CliffordCS3.Cert.Pair%03d' % j for j in sorted(lanes.values())]
        content = source[:source.index('import ')] + '\n\n'.join(imports) + '\n\n' + body
        write_source(path, content)


def main(per=600):
    sys.setrecursionlimit(1000000)
    full = CACHE.with_name('phase-c-roundtrips.pkl')
    with (full if full.exists() else CACHE).open('rb') as f:
        data = pickle.load(f)
    P, CT, faces, done, missing = data[:5]
    aa = data[5] if len(data) > 5 else {}
    A, T = P.A, P.T
    targets = list(done.values())
    base = needed(T, targets)
    base_set = set(base)
    ks = base + [k for k in needed(T, aa.values()) if k not in base_set]
    live = []
    for k in ks:
        l, r, j = T.eqs[k]
        if j[0] == 'def' or expanded(A, k)[0] == expanded(A, k)[1]:
            continue
        live.append(k)

    def steps(k):
        return exp_steps(A, k) if T.eqs[k][2][0] == 'der' else None

    def leaf(k):
        l, r, j = T.eqs[k]
        if j[0] == 'ax':
            return ax_term(j[1])
        if j[0] == 'sem':
            assert j[1][0] == 'pair', j
            pair = j[1][1]
            el, er = expanded(A, k)
            wl = word2([PAIR[pair][z] for z in el])
            wr = word2([PAIR[pair][z] for z in er])
            return ('Rule.ofDerivable _ _ (Two.derivable_embed %d '
                    '(Two.Fast.derivable_of_check (w := %s) (v := %s) (by decide +kernel)))'
                    % (pair, wl, wr))
        assert j[0] == 'face', j
        _, s, x, u, v, _ = j
        tag = 'face%d%d' % (s, x)
        return ('Rule.ofDerivable _ _ ((rs_claimB %s %s_hb '
                '(Two.Fast.derivable_of_check (w := %s) (v := %s) (by decide +kernel))) false).2'
                % (tag, tag, word2(u), word2(v)))

    R = RuleEmitter('r', 'Rule Rel', 'gcode3_bounds', 'gcode3_inj',
                    lambda z: FMT[z], lambda k: expanded(A, k), steps, leaf, wide=True)

    def face_code(s, x):
        F = faces[s, x]
        tag = 'face%d%d' % (s, x)
        out = ['def %s : Bool → Two.Gen2 → Word Gen × Bool' % tag]
        for c in (0, 1):
            for y, (w, d) in F.img[c].items():
                out.append('  | %s, .%s => (FreeMonoid.ofList %s, %s)' %
                           (str(bool(c)).lower(), y, R.word(A.expand(w)), str(bool(d)).lower()))
        out.append('theorem %s_hb (c : Bool) (w v : Word Two.Gen2) (h : Two.Rel2 w v) :\n'
                   '    (hstar %s c w).2 = (hstar %s c v).2 ∧\n'
                   '      Derivable Rel (hstar %s c w).1 (hstar %s c v).1 := by\n'
                   '  cases h with' % (tag, tag, tag, tag, tag))
        obligations = F.b_list()
        proof = {(nm, c): e for (nm, c, _, _), e in zip(obligations, F.b_proofs)}
        def term(nm, c):
            e = proof[nm, c]
            return '⟨by decide +kernel, %s⟩' % (R.name(e) + '.sound' if e in R.names else 'Derivable.refl _')
        for nm, _, _ in rels2():
            if nm.startswith('comm_i_'):
                continue
            ctor = AXNAME[nm].split('.')[-1]
            out.append('  | %s => cases c <;> first\n      | exact %s\n      | exact %s' %
                       (ctor, term(nm, 0), term(nm, 1)))
        out.append('  | comm_i y hy =>\n    cases y with\n    | i => exact (hy rfl).elim')
        for y in ['Ku', 'Kl', 'Su', 'Sl', 'CS']:
            out.append('    | %s => cases c <;> first\n        | exact %s\n        | exact %s' %
                       (y, term('comm_i_' + y, 0), term('comm_i_' + y, 1)))
        return '\n'.join(out) + '\n'

    dest = ROOT / 'Cert'
    dest.mkdir(exist_ok=True)
    emitted_faces = set()
    core = live[:per]
    leaves = [k for k in live[per:] if T.eqs[k][2][0] in ('ax', 'sem')]
    proof = [k for k in live[per:] if T.eqs[k][2][0] not in ('ax', 'sem')]
    batches = [('Part000', ['QCert.CliffordCS3.Code'], core)]
    npairs = (len(leaves) + 399) // 400
    for i in range(npairs):
        prev = 'Part000' if i < 4 else 'Pair%03d' % (i-4)
        batches.append(('Pair%03d' % i, ['QCert.CliffordCS3.Cert.' + prev], leaves[i*400:(i+1)*400]))
    pi = (len(proof) + per - 1) // per
    for i in range(pi):
        imports = ['QCert.CliffordCS3.Cert.Part%03d' % i]
        if i == 0:
            imports += ['QCert.CliffordCS3.Cert.Pair%03d' % j for j in range(max(0,npairs-4),npairs)]
        batches.append(('Part%03d' % (i+1), imports, proof[i*per:(i+1)*per]))
    for mod, imports, batch in batches:
        src = ['/- Generated by QCert/CliffordCS3/gen/threeemit.py. -/']
        src += ['import ' + dep for dep in imports]
        src += ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
                'namespace QCert.CliffordCS3.Cert']
        for k in batch:
            j = T.eqs[k][2]
            if j[0] == 'face' and j[1:3] not in emitted_faces:
                src.append(face_code(*j[1:3]))
                emitted_faces.add(j[1:3])
            src.append(R.emit(k))
        src.append('end QCert.CliffordCS3.Cert\n')
        path = dest / (mod + '.lean')
        content = '\n\n'.join(src)
        write_source(path, content)
    print('rules', len(live), 'parts', pi + 1, 'pair batches', npairs, 'missing', len(missing), flush=True)
    dependency_imports(dest)
    (CACHE.parent / 'cert-modules.txt').write_text('\n'.join(mod for mod, _, _ in batches))
    with (CACHE.parent / 'emitted-current.pkl').open('wb') as f:
        pickle.dump((R.names, pi), f)


if __name__ == '__main__':
    main()
