"""The 139 typed relations of Appendix B, as used.

Every relation is read off the paper's TeX source (`paper.typed_relations`,
numbered in the order of the source) and checked numerically.  Eleven are
false as printed; each is replaced by a corrected version, taken from the
supplement's own statement where that one is true, and recorded here with
the evidence (`CORRECTIONS`).  The supplement numbers the relations of each
figure left to right and row by row; `supp_number` matches the two
numberings by the left-hand sides.
"""
import paper
import suppdraw

# number in the source order: (corrected right-hand side as parsed gates,
# reason).  'supp' takes the supplement's statement.
CORRECTIONS = {
    6: ('supp', 'H A3 = A2 H is false (A3 = I, A2 = H); the supplement (3.6) has A3 H'),
    20: ('append X0', 'false as printed; true with X on the lower wire appended '
         '(the supplement, 3.20, has the same misprint)'),
    23: ('insert Z0 after the box', 'false as printed; true with Z on the lower wire '
         'right after B6 (the supplement, 3.23, has the same misprint)'),
    24: ('insert Z0 after the box', 'false as printed; true with Z on the lower wire '
         'right after B7 (the supplement, 3.24, has the same misprint)'),
    25: ('supp', 'false as printed (CXZ); the supplement (3.25) has CZ'),
    43: ('supp', 'false as printed; the supplement (4.13) has Z on the lower wire too'),
    47: ('insert Z0 after the box', 'false as printed, as its untyped twin (4.13)'),
    59: ('X C1 = C2', 'X C1 = C1 Z is false; the supplement (4.34) has C1 X, true but '
         'leaving X on a wire labelled 3, where Definition 5.3 does not allow it; '
         'X C1 = C2 is the rule the normalisation needs'),
    62: ('supp', 'X C2 = C2 Z is false; the supplement (4.37) has C1'),
    68: ('supp', 'false as printed; the supplement (5.5) has a different, true, right side'),
    71: ('insert Z0 after the box', 'false as printed; true with Z on the lower wire '
         'right after B8 (the supplement, 5.8, has the same misprint)'),
}


def key(gs):
    def norm(g):
        if g[0] == 'CZ':
            return ('CZ', max(g[1], g[2]), min(g[1], g[2]))
        return g
    return tuple(sorted(map(str, map(norm, gs))))


def records(ders=None):
    """[(num, fig, supp, (lhs gates, neg), (rhs gates, neg), note)]."""
    if ders is None:
        ders, _ = suppdraw.derivations()
    out = []
    for num, fig, (l, ln), (r, rn) in paper.typed_relations():
        lg, rg = l.gates(), r.gates()
        cands = [n for n in ders if not n.startswith('L') and n.split('.')[0] == str(fig)
                 and key(ders[n][0][1]) == key(lg)]
        supp = cands[0] if len(cands) == 1 else None
        note = None
        if num in CORRECTIONS:
            how, note = CORRECTIONS[num]
            if how == 'supp':
                rg, rn = ders[supp][-1][1], ders[supp][-1][2]
            elif how == 'append X0':
                rg = rg + [('X', 0)]
            elif how == 'insert Z0 after the box':
                nb = sum(1 for g in rg if g[0] == 'box')
                rg = rg[:nb] + [('Z', 0)] + rg[nb:]
            elif how == 'X C1 = C2':
                rg = [('box', 'C', 2, (0,))]
            else:
                raise ValueError(how)
        out.append((num, fig, supp, (lg, ln), (rg, rn), note))
    return out


def check(recs):
    """Every relation used holds (numerically)."""
    for num, fig, supp, (lg, ln), (rg, rn), note in recs:
        L = paper.expand(lg) + ([('m',)] if ln else [])
        R = paper.expand(rg) + ([('m',)] if rn else [])
        n = max(paper.width(L), paper.width(R), 2 if any(len(g) > 2 and g[0] != 'box' or
                g[0] == 'box' and len(g[3]) == 2 for g in lg + rg) else 1)
        assert paper.same(L, R, n), (num, lg, rg)
