"""levels.py, minimising: all candidates first, then drop greedily.

    python3 -B levels_min.py aff|s8|d8 [maxlen] [extra relators ...]
"""
import sys, time
import levels as Lv

if __name__ == '__main__':
    lev = sys.argv[1]
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    letters, below = Lv.LEVELS[lev], Lv.LEVELS[Lv.BELOW[lev]]
    target = {"d8": 128}.get(lev) or len(Lv.bfs(letters)) // len(Lv.bfs(below))
    fr = list(Lv.free(letters))
    extra = [tuple(w.split()) for w in sys.argv[4:]]
    cl = [x for x in letters if x in (sys.argv[3].split(",") if len(sys.argv) > 3 and "," in sys.argv[3] else letters)]
    cands = Lv.candidates(cl, maxlen, set(fr))
    print(lev, 'target', target, 'candidates', len(cands), flush=True)
    allr = extra + cands
    got = Lv.index(letters, fr + allr, below)
    print('all candidates ->', got, flush=True)
    if got != target:
        sys.exit()
    keep = list(allr)
    for c in list(cands)[::-1]:
        trial = [x for x in keep if x != c]
        if Lv.index(letters, fr + trial, below) == target:
            keep = trial
    print('kept', len(keep))
    for c in keep:
        print('   ', ' '.join(c), ' (gates', len(Lv.gates(' '.join(Lv.MACRO[x] for x in c))), ')')
