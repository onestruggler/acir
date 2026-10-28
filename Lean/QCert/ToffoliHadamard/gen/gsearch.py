import time
def gq(S, a, b, limit, add=False, name=None, extras=(2, 4), grows=(0, 1, 2), verbose=True):
    for ex in extras:
        for g in grows:
            ml = min(25, max(len(a), len(b)) + ex)
            t = time.time()
            st = S.query(a, b, ml, limit, add=add, name=name, grow=g)
            if verbose:
                print("   ", name, "ex", ex, "grow", g, "->", None if st is None else len(st), round(time.time()-t, 1), flush=True)
            if st is not None:
                return st
    return None
