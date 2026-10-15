# The controlled functor on words, from the generator-level (F4), (F5).
#
# A frame is a relabelling pi of the five wires (pi[4] the control wire);
# the identity is the frame of control 4, SWAP04 that of control 0.  In a
# frame the images of a generator g (f4's names: I, S0..S3, K0..K3,
# CS0..CS2, read through pi) are pi(lam0(g)), pi(lam1(g)), and the
# generator-level facts are the lemmas F5-* (CS) and windows (the rest),
# F4-g-h, at the renaming pi.
#
#   split(d, k, gens, pi)   the plain word of the generators gens at k (in
#                           the frame) to lam0(gens) lam1(gens): (F5) for
#                           each generator, then every lam0 block moved left
#                           past the lam1 letters before it by (F4)
#   bubble(d, k, g0s, h1s, pi)
#                           lam0(g0s) lam1(h1s) at k to lam1(h1s) lam0(g0s),
#                           block by block by (F4)
import derivn, f4
from derivn import Derivation, show, norm, relabel_word

ID = {w: w for w in range(5)}
SWAP04 = {0: 4, 4: 0, 1: 1, 2: 2, 3: 3}


def gen_letters(g):
    """the plain generator as derivn letters."""
    if g[0] == 'I':
        return [('iI',)]
    if g[0] in ('S', 'K'):
        return [g]
    return [derivn.norm1(('CS', g[1], g[1] + 1))]


def L0(g, pi): return relabel_word(f4.lam0(g), pi)
def L1(g, pi): return relabel_word(f4.lam1(g), pi)
def G(g, pi): return relabel_word(gen_letters(g), pi)


def f5_gen(d, k, g, pi):
    """G(g) at k to L0(g) L1(g)."""
    if g[0] == 'CS':
        d.lemma(f'F5-{g[1]}{g[1] + 1}', k, fwd=False, pi=pi)
    else:
        d.win(k, len(G(g, pi)), L0(g, pi) + L1(g, pi))


def f4_swap(d, k, g, h, pi):
    """L1(h) L0(g) at k to L0(g) L1(h) (F4 backwards)."""
    d.lemma(f'F4-{f4.gname(g)}-{f4.gname(h)}', k, fwd=False, pi=pi)


def bubble_back(d, k, g0s, h1s, pi):
    """L1(h1s) L0(g0s) at k to L0(g0s) L1(h1s)."""
    # move each L0 block (from the first) left past all the L1 letters
    n1 = sum(len(L1(h, pi)) for h in h1s)
    pos = k + n1                       # start of the first L0 block
    for g in g0s:
        b = len(L0(g, pi))
        # the block at pos moves left past the L1 letters h1s (last first)
        p = pos
        for h in reversed(h1s):
            l1 = len(L1(h, pi))
            f4_swap(d, p - l1, g, h, pi)
            p -= l1
        pos += b
    return


def bubble(d, k, g0s, h1s, pi):
    """L0(g0s) L1(h1s) at k to L1(h1s) L0(g0s)."""
    # each L1 letter (from the first) moves left past all the L0 blocks
    n0 = sum(len(L0(g, pi)) for g in g0s)
    pos = k + n0
    for h in h1s:
        l1 = len(L1(h, pi))
        p = pos
        for g in reversed(g0s):
            b = len(L0(g, pi))
            d.lemma(f'F4-{f4.gname(g)}-{f4.gname(h)}', p - b, pi=pi)
            p -= b
        pos += l1


def split(d, k, gens, pi):
    """G(gens) at k to L0(gens) L1(gens); returns the length."""
    p = k
    done = []                          # generators split so far: L0(done) L1(done) at k
    for g in gens:
        q = k + sum(len(L0(x, pi)) + len(L1(x, pi)) for x in done)
        f5_gen(d, q, g, pi)
        # L0(done) L1(done) L0(g) L1(g): move L0(g) left past L1(done)
        n0 = sum(len(L0(x, pi)) for x in done)
        bubble_back(d, k + n0, [g], done, pi)
        done.append(g)
    return sum(len(L0(x, pi)) + len(L1(x, pi)) for x in done)


if __name__ == '__main__':
    import box, boxsym, boxdash, boxbox, f0, f4cs, f5
    derivn.QUIET = True
    L = box.build({})
    f5.build(L); boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L)
    f0.build(L); f4.build(L, verbose=False); f4cs.build(L, verbose=False)
    # a test: the word K1 CS1 S2 split at control 4 and at control 0
    for pi, nm in ((ID, 'four'), (SWAP04, 'zero')):
        gens = [('K', 1), ('CS', 1), ('S', 2), ('I',)]
        w = [x for g in gens for x in G(g, pi)]
        tgt = [x for g in gens for x in L0(g, pi)] + [x for g in gens for x in L1(g, pi)]
        d = Derivation(f'split-test-{nm}', w, tgt, L)
        split(d, 0, gens, pi)
        d.done()
        print('ok split', nm, len(d.steps), 'steps')
