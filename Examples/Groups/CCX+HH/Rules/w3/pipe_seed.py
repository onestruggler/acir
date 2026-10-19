"""pipe.py with every level seeded by BFS representatives of its cosets
(computed on signed permutations), to see whether the tables get
smaller.

    python3 -B pipe_seed.py
"""
import time
import pipe as Pp

def bfs_reps(letters, below):
    reps, reps_sp = [()], [Pp.ID]
    def find(g):
        for k, r in enumerate(reps_sp):
            h = Pp.mul(g, Pp.inv(r))
            if (below.member(h) if below else h == Pp.ID):
                return k
        return None
    q = [0]
    while q:
        nq = []
        for k in q:
            for x in letters:
                w = reps[k] + (x,)
                g = Pp.sp(w)
                if find(g) is None:
                    reps.append(w); reps_sp.append(g); nq.append(len(reps) - 1)
        q = nq
    return reps

if __name__ == '__main__':
    free = Pp.free_relators()
    rels = [('inv-' + x, (x, x)) for x in Pp.LET]
    rels += [('comm-%s-%s' % (r[0], r[1]), r) for r in Pp.COMM]
    for nm, rs in free.items():
        rels += [('%s-%d' % (nm, k), r) for k, r in enumerate(rs)]
    rels += list(Pp.THREE.items())
    below = None
    for name, letters in Pp.LEVELS:
        mine = [(nm, r) for nm, r in rels if all(x in letters for x in r)]
        reps = bfs_reps(letters, below)
        loc = {x: k for k, x in enumerate(letters)}
        seed = [tuple(loc[x] for x in r) for r in reps]
        t0 = time.time()
        lev = Pp.Level(name, letters, below, mine, seed=seed)
        print(f'{name}: {len(lev.live)} cosets, defined {len(lev.tc.rep)}, {round(time.time() - t0, 1)} s', flush=True)
        Pp.report(lev)
        below = lev
