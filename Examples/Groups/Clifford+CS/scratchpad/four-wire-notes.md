# Clifford+CS from four wires on: the Section-8 analogue (design notes)

Date: 2026-10-14.  Status: design + first numerics (tc.py).

## The determinant story

det on the two-level generators of U_N(Z[1/2,i]) (Bian-Selinger,
Clifford+CS-TwoLevel/Syntactics): det i[a] = i, det X[a,b] = -1,
det K[a,b] = i (K = gamma^-1 [[1,1],[1,-1]], det = -2/gamma^2 = i).
The abelianization of the presentation is Z/4 = <det> exactly
(swap rules identify all i's, all X's, all K's; rel-13 gives x = 2*iota,
rel-14 gives kappa = iota, order-i gives 4*iota = 0).

A gate at width n embeds with multiplicity 2^(n-wires(gate)), so at
width >= 4 every circuit has det 1 (e.g. CS: det i^(2^(n-2)) = 1 for
n >= 4; at n = 3 it is -1, which is the Bian-Selinger index-2
phenomenon).  So the auxiliary language for n >= 4 is the det-kernel.

## The alphabet P' (mirroring Clement's P = {-1-1, -1X, XX, HH})

- iib[a,b]   = i[a] i[b]^-1          (phase pair; (iib)^2 = -1-1, so the
                                      sign pair is redundant)
- mX[a;b,c]  = i[a]^2 X[b,c]         (sign-exchange, as in Clement)
- XX[ab,cd]  = X[a,b] X[c,d]         (double exchange, as in Clement)
- KKb[ab,cd] = K[a,b] K[c,d]^-1      (the HH analogue;
                                      K^-1 = K i i by rel-16)

Encoding (Definition 8.2 analogue), all words positive products:
  E(iI) = prod_{x} i[x]                       (2^n letters)
  E(S_w) = prod_{x_w = 1} i[x]                (2^(n-1))
  E(CS_vw) = prod_{x_v = x_w = 1} i[x]        (2^(n-2))
  E(K_w) = prod_{contexts y} K[y0, y1]        (2^(n-1) letters)
Pure i-quadruples factor into P'-letters:
  i_a i_b i_c i_d = (i_a i_b^3)(i_b^2 i_c^2)(i_c^3 i_d)
                  = iib[a,b] . (iib[b,c])^2 . iib[d,c]   (phases commute)
K-products pair off as KKb (even count at every width; the positive
spelling K_ab K_cd = KKb[ab,cd] . (K_cd)^2-correction = KKb . iib-pairs
by rel-16: K^2 = i_a^-1 i_b^-1).

## The quotient / coset prediction

Mod the normal closure of P': all i_a == iota, X == iota^2, all
K == kappa; rel-14 (K i^3 = i K i K) gives iota^3 kappa = iota^2 kappa^2,
so kappa = iota, and the quotient is Z/4 = <iota | iota^4>.

So FOUR cosets, reps {eps, i_0, i_0^2, i_0^3} -- the Definition A.2
analogue.  (Clement's real case had 4 = det x H-parity because no real
relation has odd H-imbalance; our rel-14 has K-imbalance 1 and kills
the K-coset.)

Caveat: Todd-Coxeter must confirm (a) the quotient order is 4
(q-mode in tc.py), and preferably (b) the plain subgroup <P'> already
has index 4 (subgroup mode), i.e. <P'> is normal without help.

## The coset action (item (a) skeleton)

deg: i -> 1, X -> 2, K -> 1 in Z/4; act(c, y) lands in coset c + deg y
with word rep_c . y . rep_{c+deg y}^-1:
  i_a:  iib[a,0] at every coset (eps if a = 0)
  X_bc, 0 not in {b,c}:  mX[0;b,c] at every coset
  X_0c:  mX[0;0,c] . iib[c,0]^c at coset c  (i_0^c X_0c = X_0c i_c^c)
  K_bc:  needs K_bc i_0^-1 as a P'-word -- comes from rel-14; the
         numerics should find a short spelling (word search over P'
         letters against the matrix, as scratchpad/tA2.py did).

## The program (analogue of Real-Clifford+CH, reusing its machinery)

1. Figure-8 analogue: a rule set on P'-words.  The K-free fragment is
   the group of i-phased permutations with det 1; NF's Lehmer-code
   normal form ports with Z/4 phases for Z/2 signs (SignedPerm ->
   "PhasedPerm").
2. Theorem 4.10 analogue: R-S with 4 cosets against the two-level
   presentation; Theorem 4.4 analogue is ALREADY PROVED
   (Clifford+CS-TwoLevel.MainLemma.relations-complete) -- no imported
   hypothesis, unlike Clement's paper.
3. E and e-sem at every width (EncodingSemantics analogue).
4. The hard part: d decodes P'-letters into circuits (multi-controlled
   CS/K boxes) and Lemma 8.7/8.8 analogues; the box calculus will
   probably need a schema axiom from five wires on, as Clement's (19)
   (CLAUDE.md already anticipates this).

## Numerics: results (2026-10-14, tc.py and csP.py)

- Quotient G/<<P'>> (q-mode): order 4 at N = 6, 8 -- for iib,mX,XX,KKb,
  for iib,mX,XX (no K-letter: rel-14 kills the K-coset as predicted),
  and for mm,mX,XX,KKb.
- Plain subgroup <P'> with P' = {iib, mX, XX, KKb}: index 4 (closed) at
  N = 5, 6, 8 and 16 -- so <P'> IS the det-kernel at every N >= 5, in
  particular at every real width (N = 2^n >= 16).  At N = 4 the
  enumeration explodes (MemoryError at an 80k-coset cap): on four
  indices the subgroup is genuinely smaller -- the fresh-index
  phenomenon, as in Clement's constructions.  Since <P'> = kernel and
  the kernel is normal, <P'> is normal, so conjugates of letters are
  P'-words (the Figure-9-analogue theory will spell them out).
- e-sem at width 4 (csP.py esem): E(K_w), E(S_w), E(CS_01), as positive
  two-level products, equal the gates' Kronecker matrices exactly. OK.
- Item (a)'s K-case, by MITM at N = 5 (csP5.py): length 5, with one
  fresh phase index and one fresh K-pair:

      K_01 i_0^-1 = iib[1,0] . iib[2,0] . KKb[01,34] . iib[0,2] . KKb[34,01]
                  = iib[1,0] . [ iib[2,0] , KKb[01,34] ]

  (the i_2 and the K_34 cancel, leaving i_1 i_0^-2 K_01 i_0 K_01^-1 --
  rel-14 in disguise).  No word of length <= 8 exists on 4 indices.
- Letter inverses are letters: iib[a,b]^-1 = iib[b,a],
  XX^-1 = XX, KKb[ab,cd]^-1 = KKb[cd,ab], mX[a;b,c]^-1 = mX[a;b,c] for
  a not in {b,c} (an involution) and mX[c;b,c] for a = b.

## Item (a), the action table (to verify as tP.py, the tA2 analogue)

deg: i -> 1, X -> 2, K -> 1; reps r_c = i_0^c; act(c, g) lands in
c + deg g with word r_c g r_(c+deg g)^-1:
  i_a                : iib[a,0]  (eps if a = 0), same at every coset
  X_bc, 0 not in bc  : mX[0;b,c], same at every coset
  X_0c               : mX[0;0,c] . iib[c,0]^c   (i_0^c X_0c = X_0c i_c^c)
  K_de, 0 not in de  : KKb[de,0z] . Q(z), z fresh; same at every coset
  K_0e               : Q(e) at c = 0; at c >= 1 the word is the
                       i_0^c-conjugate of Q(e), a P'-word by normality
                       (tabulate per c numerically)
where Q(z) = K_0z i_0^-1 is the found word above, renamed.

## Next numerics

- [x] tP.py: the full act table at N = 16, every generator x coset,
      each word checked against its matrix (the tA2.py analogue).
- [ ] the Figure-8-analogue rule set on P'-letters, checked sound in
      the phased-permutation + K model (the tB.py analogue precursor).
- [ ] the decoding d: P'-letters as multi-controlled circuits
      (K-free letters: phased permutations; KKb: a box gadget), at
      width 4 first (sim over dyadic complexes).

## tP.py result

The full action table checks exactly: 256/256 cases at N = 8 and
1024/1024 at N = 16 (every generator at every coset).  The K_0e rows
are the four tabulated MITM words (c = 0..3, all length 5, each a
phase pair around a KKb-commutator); every other row is uniform in the
coset.

## The K-free fragment (tNFcs.py, tF.py)

The closure of the K-free letters is the group of det-1 phased
permutations: 96 at N = 3 and 1536 at N = 4, i.e. 4^(N-1) . N!
(tNFcs.py), so NF's Lehmer-code normal form ports with a Z/4 phase
vector (one global det constraint per permutation) for the Z/2 sign
list.  The rule set is Figure8Free's (20)-(34) transcribed to phases
(tF.py; every instance sound at N = 5 and 6, 896 and 1912 cases):
letters pp a b = i_a i_b^-1, px s a b = i_s^2 X_ab, dx = XX; phases
conjugate under exchanges without inversion, so (24)-(29) and
(31)-(34) keep their shapes with zz c a replaced by (pp c a)^2 in
(30); new are only the pp-algebra rules (20') pp a a = eps,
(20'') pp^4 = eps, (21') pp a b . pp b a = eps, (21'') pp's commute,
(22') pp a b . pp b c = pp a c, and (23') (pp a a')^2 = (px a a a')^2.

## The KKb-letter local algebra (tK.py, 13/13 at N = 8)

The raw-index analogues of Figure 8's K-rules: inverses
(kk[ab,cd] kk[cd,ab] = eps), the square is a phase word
(kk^2 = pp c a . pp d b, the (41)-analogue), bridging
(kk[ab,cd] = kk[ab,ef] kk[ef,cd], the (42)-analogue, no side
condition needed at raw indices), disjoint commutation, the phases
that pass (the -1-1 pair on the K-pair's own indices, and
i_a i_b i_e^-2 as pp(a,e) pp(b,e), from rel-15), rel-13 lifted --
kk . (pp b e)^2 = px(e;a,b) . kk, the -1 moved to a fresh index e
where it becomes the sign of the px; the sign on the first index
costs a further (pp a b)^2, which passes -- the pair exchange
(px(b;a,b) kk px(a;a,b) = (pp a b)^2 kk), XX renaming a K-pair, and
rel-17 bridged through two fresh pairs.  What remains for the rule
set is only the Gray-code layer: the encoded-letter rules
((35)-(37), (40), (43)-(46) analogues), which depend on the
encoding's pairing and come with the decoding design.
