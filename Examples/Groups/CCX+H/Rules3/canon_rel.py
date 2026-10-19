"""Contraction derivations for one instance of each relation family."""
import sys, time, collections
from decoder import dec, AUX, REL, seg_tokens
from deriv import Deriv, mm, I8
from syn import M, inv


def flat(elems):
    """elements -> alternating token segments [t0, ..., tm] (H's between)"""
    segs = [()]
    for e in elems:
        if e == 'H':
            segs.append(())
        else:
            segs[-1] = segs[-1] + seg_tokens(e)
    return segs


def inv_elems(elems):
    out = []
    for e in reversed(elems):
        if e == 'H':
            out.append('H')
        else:
            out.append(('T', (), inv(seg_tokens(e))))
    return out


def cancel_hh(segs):
    """remove empty segments between two H's: t H () H u -> t u"""
    changed = True
    while changed:
        changed = False
        for k in range(1, len(segs) - 1):
            if segs[k] == ():
                segs[k - 1:k + 2] = [segs[k - 1] + segs[k + 1]]
                changed = True
                break
    return segs


def loop_of(rel):
    lhs = [e for i in rel['auxiliary_left'] for e in dec(AUX[i])]
    rhs = [e for i in rel['auxiliary_right'] for e in dec(AUX[i])]
    return cancel_hh(flat(lhs + inv_elems(rhs)))


if __name__ == "__main__":
    fams = collections.OrderedDict()
    for r in REL['relations']:
        fams.setdefault(r['source'], r)
    only = sys.argv[1:] if len(sys.argv) > 1 else None
    for name, r in fams.items():
        if only and name not in only:
            continue
        if name == 'roundtrip':
            continue
        segs = loop_of(r)
        t0 = time.time()
        D = Deriv(segs)
        st = D.run()
        c = collections.Counter(s[0] for s in st)
        print(name, r['indices'], "H-count", len(segs) - 1, "steps", dict(c), round(time.time() - t0, 1), flush=True)
