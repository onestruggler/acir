"""Each gate on its own wires as the circuit of a word in the cycles.

From the macro derivations of search/gates.json (the Toffoli gates t_i
and t'_i of four consecutive positions, the two controlled swaps, CCX)
to one lemma per gate: its letter -> the letters of the cycles of a word
in Lafont's generators.  The word is BASE's for X, CX, CCX and the bottom
swap; for the other two swaps it is whatever the three-wire step gives,
and Agda carries it to Translation's word by Lafont's completeness.
"""
import json
import os

import four as F
from four import M, Proof, LIB, HS, Bot, spw, sp, inv, rev
import inst
from inst import FORMS, OMEGA

HERE = os.path.dirname(os.path.abspath(__file__))


def cycles_to_forms(pr, off, seq, fm):
    """The letters of the cycles seq at off -> their placed gates in the
    forms fm.  Returns the offset after them."""
    for i in seq:
        pr.rw(off, inst.ODEF[i])
        if fm[i] != inst.SYN[i]:
            pr.rw(off, inst.form_change(i, inst.SYN[i], fm[i]))
        off += len(spw(FORMS[i][fm[i]]))
    return off


def spread(pr, o, triple, new):
    """At o: p (b_1 ... b_m) p^-1, the b_k the gates of new on the bottom
    wires and p the frame of the triple.  -> sp(new)."""
    p = F.TRIPLE_FRAME[triple]
    if not p:
        return
    b_new = [sp(F.relabel(g, triple)) for g in new]
    x = o + len(p)
    for k, b in enumerate(b_new):
        x += len(b)
        if k + 1 < len(b_new):
            pr.rw(x, HS('', rev(p) + p))
            x += 2 * len(p)
    x = o
    for g, b in zip(new, b_new):
        pr.run(F.backwards(F.to_frame(g, p, b)), x)
        x += len(sp(g))


def letter_to_gates(letter, triple, l3, gates, gate=None):
    """letter -> sp(gates), a three-wire step on the triple.  l3 is the
    letter on the bottom three wires; gate the placed gate that the
    letter spells, if it is one."""
    p = F.TRIPLE_FRAME[triple]
    pr = Proof(letter)
    if gate is not None:
        assert sp(gate) == letter
        pr.run(F.to_frame(gate, p, l3))
    else:
        pr.rw(0, HS(letter, p + l3 + rev(p)))
    assert pr.cur == p + l3 + rev(p)
    pr.rw(len(p), Bot(l3, ''.join(sp(F.relabel(g, triple)) for g in gates)))
    spread(pr, 0, triple, gates)
    assert pr.cur == spw(gates)
    return pr


def gate_lemmas():
    data = json.load(open(os.path.join(HERE, 'search', 'gates.json')))
    eqs = {}
    for nm, d in data.items():
        assert d['found'], nm
        l, r = d['lhs'], d['rhs']
        assert d['relator'] == l + r[::-1]
        z = LIB.add('G', F.compile_macro(d['relator'], d['steps']), '',
                    'relator of ' + nm)
        eqs[nm] = (l, r, LIB.add('G', F.relator_to_equation(l, r, z), spw(r), nm))

    f0 = {i: 0 for i in range(14)}
    t1, t2 = {}, {}          # the Toffoli gates
    T1L, T2L = {}, {}        # sp(t_i) -> cycles, sp(t'_i) -> cycles
    W1, W2 = {}, {}          # the words of cycles
    for i in range(0, 13, 2):
        l, r, d_eq = eqs['D%d' % i]
        assert l == FORMS[i + 1][0] + FORMS[i][0]
        (t1[i],) = r
        pr = Proof(OMEGA[i + 1] + OMEGA[i])
        cycles_to_forms(pr, 0, [i + 1, i], f0)
        pr.rw(0, d_eq)
        dl = LIB.add('G', pr, sp(t1[i]), 'the cycles %d %d are %s' % (
            i + 1, i, M.gname(t1[i])))
        l, r, v_eq = eqs['V%d' % i]
        assert l == FORMS[i][0] + FORMS[i + 1][0] and r[0] == t1[i]
        t2[i] = r[1]
        pr = Proof(OMEGA[i] + OMEGA[i + 1])
        cycles_to_forms(pr, 0, [i, i + 1], f0)
        pr.rw(0, v_eq)
        vl = LIB.add('G', pr, spw(r), 'the cycles %d %d are %s' % (i, i + 1, M.show(r)))
        T1L[i], W1[i] = dl.sym(), [i + 1, i]
        pr = Proof(sp(t2[i]))
        pr.rw(0, inv(t1[i]).sym())
        pr.rw(0, dl.sym())
        pr.rw(len(OMEGA[i + 1] + OMEGA[i]), vl.sym())
        W2[i] = [i + 1, i, i, i + 1]
        T2L[i] = LIB.add('G', pr, ''.join(OMEGA[k] for k in W2[i]),
                         '%s as cycles' % M.gname(t2[i]))

    def finish(name, pr, plan):
        """pr.cur is sp of the gates of plan, a list of ('t', i), ('u', i)
        or ('fk', lemma, cycles).  Rewrites them into cycles."""
        off = 0
        word = []
        for item in plan:
            if item[0] == 't':
                i = item[1]
                pr.rw(off, T1L[i])
                w = W1[i]
            elif item[0] == 'u':
                i = item[1]
                pr.rw(off, T2L[i])
                w = W2[i]
            else:
                _, lem, w = item
                pr.rw(off, lem)
            off += sum(len(OMEGA[k]) for k in w)
            word.extend(w)
        rhs = ''.join(OMEGA[k] for k in word)
        return LIB.add('G', pr, rhs, name + ' as cycles', name=name), word

    out = {}
    # X on wire 0: the four Toffoli gates from the wires 2 3
    gs = [t1[i] for i in (0, 4, 8, 12)]
    out['X0'] = finish('gate-X0', letter_to_gates('a', (0, 2, 3), 'a', gs, M.gate(0)),
                       [('t', i) for i in (0, 4, 8, 12)])
    # CX: the two from the wires 1 3
    gs = [t1[2], t1[10]]
    out['CX0'] = finish('gate-CX0', letter_to_gates('c', (0, 1, 3), 'c', gs, M.gate(0, (1, 1))),
                        [('t', 2), ('t', 10)])
    # CCX
    l, r, c_eq = eqs['CCX']
    assert r == [t1[4], t1[6], t1[8]] and spw(l) == 'T'
    pr = Proof('T')
    pr.rw(0, c_eq)
    out['CCX0'] = finish('gate-CCX0', pr, [('t', 4), ('t', 6), ('t', 8)])
    # the swap of the wires 0 1: the two controlled swaps
    plan, gs = [], []
    for nm, (i, k, j) in (('FKa', (1, 2, 4)), ('FKb', (9, 10, 12))):
        l, r, fk = eqs[nm]
        assert l == FORMS[i][0] + [t1[k]] + FORMS[j][0]
        pr = Proof(OMEGA[i] + sp(t1[k]) + OMEGA[j])
        x = cycles_to_forms(pr, 0, [i], f0)
        cycles_to_forms(pr, x + len(sp(t1[k])), [j], f0)
        pr.rw(0, fk)
        fkl = LIB.add('G', pr, spw(r), 'the swap of the wires 0 1 under a control: ' + nm)
        # sp(r) -> cycles
        pr = Proof(spw(r))
        pr.rw(0, fkl.sym())
        pr.rw(len(OMEGA[i]), T1L[k])
        w = [i] + W1[k] + [j]
        lem = LIB.add('G', pr, ''.join(OMEGA[q] for q in w), nm + ' as cycles')
        plan.append(('fk', lem, w))
        gs.extend(r)
    out['Ex0'] = finish('gate-Ex0', letter_to_gates('s', (0, 1, 3), 's', gs), plan)
    # the swap of the wires 1 2: CX both ways, from t'
    plan = [('u', i) for i in (4, 8, 2, 10, 4, 8)]
    gs = [t2[i] for _, i in plan]
    out['Ex1'] = finish('gate-Ex1', letter_to_gates('t', (1, 2, 3), 's', gs), plan)
    # the swap of the wires 2 3: CX both ways; X on wire 1 gives the
    # white controls
    x1 = [0, 4, 8, 12]
    cx32 = [10] + x1 + [10] + x1
    cx23 = x1 + [6] + x1 + [6]
    plan = [('u', i) for i in cx32 + cx23 + cx32]
    gs = [t2[i] for _, i in plan]
    out['Ex2'] = finish('gate-Ex2', letter_to_gates('u', (1, 2, 3), 't', gs), plan)
    return out
