# The hybrid facts the generic layer (Lemma88/HybridRules) asks of n = 4,
# as transports of the class facts derived in hybfar/hybshift/hybtop:
#   far-p j, far-l j, far-k j (j = 0 .. 12) at the top pair 14,
#   shift c (c = 0 .. 13), and the pair scalar sc at 14.
# For each instance: its sides as decoded blocks, a group element (ops)
# carrying them to the class fact's blocks up to the spelling of the
# middle words, and the respellings that needs.
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import norm, show, BY_NAME
from passes import L
import facts4 as F
import hyb_classes as HC
import hybfar as HF
import hybshift as HS
import hybtop as HT

TOP = 14

def instances():
    out = []
    for j in range(TOP - 1):
        out.append(('far-p', j, [(TOP, 'k'), (j, 'p')], [(j, 'p'), (TOP, 'k')]))
        out.append(('far-l', j, [(TOP, 'k'), (j, 'l')], [(j, 'l'), (TOP, 'k')]))
        out.append(('far-k', j, [(TOP, 'k'), (j, 'k')], [(j, 'k'), (TOP, 'k')]))
    for c in range(TOP):
        out.append(('shift', c, [(c, 'l'), (c + 1, 'l'), (c, 'k')], [(c + 1, 'k'), (c, 'l'), (c + 1, 'l')]))
    out.append(('sc', TOP, [(TOP - 1, "p'"), (TOP - 1, "p'"), (TOP, "p'"), (TOP, 'k')],
                           [(TOP, 'k'), (TOP - 1, "p'"), (TOP - 1, "p'"), (TOP, "p'")]))
    out.append(('cp', TOP, [(TOP, 'k'), (TOP, 'p')], [(TOP, 'p'), (TOP, 'h'), (TOP, 'k')]))
    out.append(('c3', TOP, [(TOP, 'k')] * 3, []))
    out.append(('sq', TOP, [(TOP, 'k'), (TOP - 1, "p'"), (TOP, 'k'), (TOP - 1, "p'"),
                            (TOP - 1, "p'"), (TOP - 1, "p'"), (TOP, "p'")], []))
    import gen_yb as GY
    yl, yr = GY.sides()
    out.append(('yb', TOP, yl, yr))
    return out

def blocks(side): return [F.decoded(a, kind) for a, kind in side]

def is_k(b): return len(b[1]) == len(F.KIMID)

def same_up_to_spelling(bt, bc):
    """blocks equal up to their middle words' spellings (same X set, same kind and target/roles)."""
    if bt[0] != bc[0]: return False
    if is_k(bt) != is_k(bc): return False
    if is_k(bt): return HC.hyb_roles(bt[1])[0] == HC.hyb_roles(bc[1])[0]
    return F.sem(bt) == F.sem(bc)

# the class facts, with their blocks
def far_classes():
    cl = HC.classify(); out = []
    for k, insts in sorted(cl.items()):
        c0, j0, A, B = insts[0]
        tA, sA, pA = HC.hyb_roles(A[1])
        if k[0] in ('kp', 'kl'):
            tB = F.tgt_of(B[1])
            seps = [w for w in range(4) if w not in (tA, tB) and A[0][w] != B[0][w] and w in pA]
            name = HF.far_fact(A, B, seps[0])
            Bc = F.cblock(F.sem(B))
            out.append((k[0], name, [A, Bc], [Bc, A]))
        else:
            tB, sB, pB = HC.hyb_roles(B[1])
            seps = [w for w in range(4) if w not in (tA, tB) and A[0][w] != B[0][w] and w in pA and w in pB]
            Ab, Bw = (A, B) if not any(A[0]) else (B, A)
            name = HF.kk_fact(Ab, Bw, seps[0])
            out.append(('kk', name, [Ab, Bw], [Bw, Ab]))
    return out

def shift_classes():
    done = {}; out = []
    for c in range(TOP):
        key, ops, bt = HS.rep01(c)
        if key in done: continue
        done[key] = c
        A, B, Hc, Hc1 = bt
        name = HS.shift_fact(bt)
        Ac, Bc = F.cblock(F.sem(A)), F.cblock(F.sem(B))
        out.append(('shift', name, [Ac, Bc, Hc], [Hc1, Ac, Bc]))
    return out

def sc_class():
    ops = HT.frame_top()
    name = HT.C_sc()
    k = F.TF(ops, [F.decoded(TOP, 'k')])[0]
    z = F.TF(ops, [F.decoded(TOP - 1, "p'"), F.decoded(TOP - 1, "p'"), F.decoded(TOP, "p'")])
    return [('sc', name, [k] + z, z + [k])]          # the lemma's own direction: k z = z k

def cp_class():
    ops = HT.frame_top()
    name = HT.C_p()
    k, p, h = F.TF(ops, [F.decoded(TOP, 'k'), F.decoded(TOP, 'p'), F.decoded(TOP, 'h')])
    return [('cp', name, [k, p], [p, h, k])]

def c3_class():
    ops = HT.frame_top()
    name = HT.C_3()
    k = F.TF(ops, [F.decoded(TOP, 'k')])[0]
    return [('c3', name, [k, k, k], [])]

def sq_class():
    ops = HT.frame_top()
    name = HT.C_sq()
    bl = F.TF(ops, [F.decoded(TOP, 'k'), F.decoded(TOP - 1, "p'"), F.decoded(TOP, 'k'), F.decoded(TOP - 1, "p'"),
                    F.decoded(TOP - 1, "p'"), F.decoded(TOP - 1, "p'"), F.decoded(TOP, "p'")])
    return [('sq', name, bl, [])]

def yb_class():
    import gen_yb as GY
    ops = HT.frame_top()
    name = GY.C_yb()
    yl, yr = GY.sides()
    return [('yb', name, GY.blocks(yl, ops), GY.blocks(yr, ops))]

KIND = {'far-p': 'kp', 'far-l': 'kl', 'far-k': 'kk', 'shift': 'shift', 'sc': 'sc', 'cp': 'cp', 'c3': 'c3',
        'sq': 'sq', 'yb': 'yb'}

def candidates(inst, classes, Gp):
    """every (ops, fn, kl, kr, Lt, Rt, sw) carrying the instance to a class fact."""
    name, a, l, r = inst
    Lb, Rb = blocks(l), blocks(r)
    out = []
    for (ck, fn, kl, kr) in classes:
        if ck != KIND[name]: continue
        if len(kl) != len(Lb): continue
        for ops in Gp:
            Lt, Rt = F.TF(ops, Lb), F.TF(ops, Rb)
            if all(same_up_to_spelling(x, y) for x, y in zip(Lt, kl)) and                all(same_up_to_spelling(x, y) for x, y in zip(Rt, kr)):
                out.append((ops, fn, kl, kr, Lt, Rt, False))
            if name in ('far-k', 'sc') and all(same_up_to_spelling(x, y) for x, y in zip(Rt, kl)) and                all(same_up_to_spelling(x, y) for x, y in zip(Lt, kr)):
                out.append((ops, fn, kl, kr, Lt, Rt, True))
    return out

def place(inst, classes, Gp):
    c = candidates(inst, classes, Gp)
    return c[0] if c else None

def respellings(Lt, Rt, kl, kr, sw):
    """the middle words that must be respelled: (from, to) pairs."""
    pairs = []
    A, B = (kl, kr) if not sw else (kr, kl)
    for bt, bc in list(zip(Lt, A)) + list(zip(Rt, B)):
        if tuple(norm(list(bt[1]))) != tuple(norm(list(bc[1]))):
            pairs.append((tuple(norm(list(bt[1]))), tuple(norm(list(bc[1])))))
    return pairs

def hyb_resp(rs): return {p for p in rs if len(p[0]) == len(F.KIMID)}

def plan():
    """every instance placed, choosing among the transports the one whose
    hybrid respellings add least to those already chosen."""
    classes = far_classes() + shift_classes() + sc_class() + cp_class() + c3_class() + sq_class() + yb_class()
    Gp = F.group()
    cands = []; missing = []
    for inst in instances():
        cs = candidates(inst, classes, Gp)
        if not cs: missing.append(inst[:2]); continue
        cands.append((inst, [(c, respellings(c[4], c[5], c[2], c[3], c[6])) for c in cs]))
    chosen = set(); out = []
    # the instances with fewest choices first
    for inst, cs in sorted(cands, key=lambda t: len(t[1])):
        best = min(cs, key=lambda cr: (len(hyb_resp(cr[1]) - chosen), len(cr[1])))
        (ops, fn, kl, kr, Lt, Rt, sw), rs = best
        chosen |= hyb_resp(rs)
        out.append((inst, ops, fn, kl, kr, sw, rs))
    order = {inst[:2]: i for i, inst in enumerate(instances())}
    out.sort(key=lambda e: order[e[0][:2]])
    return out, missing

if __name__ == '__main__':
    out, missing = plan()
    print('placed', len(out), 'missing', missing)
    need = set()
    for (inst, ops, fn, kl, kr, sw, rs) in out:
        for (a, b) in rs: need.add((a, b))
        print(inst[0], inst[1], '->', fn[:50], 'sw' if sw else '', 'resp', len(rs))
    print('distinct respellings', len(need))
    new = 0
    for a, b in sorted(need):
        kind = 'hyb' if len(a) == len(F.KIMID) else 'kfree'
        if kind == 'hyb':
            nm = f'respell hyb {show(list(a))[:40]} -> {show(list(b))[:40]}'
            have = nm in L
        else:
            have = None
            try:
                n0 = F.respell(a)
                have = (n0 is None) or (tuple(L[n0][1]) == tuple(b))
            except Exception as e: have = repr(e)[:80]
        if not have: new += 1
        print('  ', kind, 'have' if have is True else ('NEW' if not have else have), show(list(a))[:45], '->', show(list(b))[:45])
    print('respellings not yet derived:', new)
