"""Complete the macro-action certificates using the existing proof tables.

All successful steps are derivations from Figure 2 and proved two-qubit
identities. Numerical matrices select candidate rewrites only; the emitted
Lean certificates must check every step independently.
"""
import pickle
import sys
import time
from pathlib import Path

from pc import PC, define_phase_c, prove_any
from cross import Ctrl, cross_comm, block_cross_comm, support_vals, commute
from face_transport import FaceProof
import b2q1


def load():
    sys.setrecursionlimit(1000000)
    with open('w3L.pkl', 'rb') as f:
        W, pushes, cancels = pickle.load(f)
    P = PC(W, verbose=False)
    P.pushes, P.cancels = pushes, cancels
    define_phase_c(P)
    return P


def main():
    start = time.monotonic()
    P = load()
    CT = Ctrl(P)
    faces = {}
    done, missing = {}, []
    for nm, c, u, v in b2q1.b2_list():
        if u == v:
            done[(nm, c)] = None
            continue
        if (u, v) in P.T.index:
            done[(nm, c)] = P.T.index[u, v]
            continue
        try:
            done[(nm, c)] = prove_any(P, u, v)
            continue
        except (ValueError, AssertionError):
            pass
        if len(u) == 2 and v == tuple(reversed(u)):
            try:
                done[(nm, c)] = cross_comm(P, CT, u[:1], u[1:])
                print(nm, c, 'cross', flush=True)
                continue
            except (ValueError, AssertionError, StopIteration):
                pass
        if len(u) == 2 and v == tuple(reversed(u)):
            try:
                if u[0] in ('KI', 'KJ'):
                    done[(nm, c)] = block_cross_comm(P, CT, u[:1], u[1:])
                elif u[1] == 'T6J':
                    done[(nm, c)] = commute(P, u[:1], u[1:], ('B', [('T6',), ('C02', 'CCZ')], [None, None]))
                else:
                    raise ValueError('not a block commutation')
                print(nm, c, 'block cross', flush=True)
                continue
            except (ValueError, AssertionError, StopIteration) as ex:
                print(nm, c, 'block failed', repr(ex)[:250], flush=True)
        common = {(s, x) for s in range(3) for x in (0, 1)}
        for z in set(u + v):
            common &= set(support_vals(P.A.mats[z]).items())
        success = False
        for s, x in sorted(common):
            try:
                if (s, x) not in faces:
                    faces[s, x] = FaceProof(P, CT, s, x)
                F = faces[s, x]
                done[(nm, c)] = F.prove(u, v)
                print(nm, c, 'face', s, x, flush=True)
                success = True
                break
            except (ValueError, AssertionError) as ex:
                print(nm, c, 'face failed', repr(ex)[:250], flush=True)
        if not success:
            missing.append((nm, c, u, v))
            print(nm, c, 'missing', flush=True)
    print('proved', len(done), 'missing', len(missing), 'seconds', time.monotonic() - start, flush=True)
    for target in missing:
        print(target, flush=True)
    cache = Path('../../../.handover-scratch/cs3/phase-c-current.pkl')
    cache.parent.mkdir(parents=True, exist_ok=True)
    with cache.open('wb') as f:
        pickle.dump((P, CT, faces, done, missing), f, protocol=pickle.HIGHEST_PROTOCOL)
    assert not missing, 'The macro action still has unproved obligations'


if __name__ == '__main__':
    main()
