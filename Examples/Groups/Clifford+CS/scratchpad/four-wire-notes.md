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

## Generation (tc.py 'gates' mode)

The subgroup of the two-level group generated by the ENCODED GATES
E(iI), E(S_t), E(K_t), E(CS_vt):

- width 3 (N = 8): **index 2, closed** -- the 3-qubit Clifford+CS
  image in U_8(Z[1/2,i]) is exactly the det-in-{+-1} subgroup, i.e.
  the index-2 statement Bian-Selinger cite from Amy-Glaudell-Ross,
  machine-checked from the presentation alone.  (In particular CCZ,
  CCX and CC(iZ), det -1, -1, 1, are 3-qubit circuits.)
- width 4 (N = 16): the plain HLT enumeration exhausts memory on the
  long subgroup words; 'gates+' adds as scaffolding the encodings of
  circuits on at most 3 wires (X, CX, CCX, CZ, CCZ, iZ, C(iZ),
  CC(iZ)), each licensed by the width-2 (all of U_4) and width-3
  (det +-1) results.  Expected index 4 = the det-1 subgroup, the
  generation half of the width-4 programme.

## The letter-level encoding (tE.py, width 4, all OK)

  quad a b c d = pp[a,b] . pp[b,c]^2 . pp[d,c]        ( = i_a i_b i_c i_d )
  K_p K_q      = KKb[p,q] . i_q0^-1 i_q1^-1           (rel-16)

E(S_t), E(CS_vt), E(iI) are products of quads over their index sets;
E(K_t) is the product of KKb over consecutive context pairs followed
by the collected corrections, inverse quads over the odd pairs'
indices.  All checked against the gate matrices at width 4.

## The Agda plan (mirroring Real-Clifford+CH module by module)

Everything below Section 8's circuit side has a direct source to port,
with Z/2 signs -> Z/4 phases and H-pairs -> K-pairs:

  Auxiliary/P            -> GenP': pp / px / dx / kkb with irrelevant
                            distinctness, degree in Z/4
  Auxiliary/Figure8Free  -> the fragment rules (tF.py's list)
  Auxiliary/Figure8      -> + the K-rules (tK.py's list) and the
                            Gray-code layer (to be designed)
  Auxiliary/SignedPerm   -> PhasedPerm: sgn : idx -> Z/4, sound-ax
                            per rule; prod-L/conj-L carry over
  Auxiliary/NF, Unique   -> the same Lehmer-code normal form; the sign
                            part becomes a Z/4 vector with membership
                            replaced by "phase at an index"; the atoms
                            argument needs phases counted mod 4
  Auxiliary/SPMatrix     -> phased-permutation matrices are faithful
  Auxiliary/Cosets, RS   -> 4 cosets i_0^c; h = the tP.py table
  Auxiliary/DE, ItemA    -> items (a): the monomial cases are the
                            closed forms, the K-case is the tP.py
                            commutator word (rel-14)
  Auxiliary/ItemB, Frame -> item (b): 19 two-level rules x 4 cosets;
                            the Frame/uniform-embedding trick should
                            port (the tags are pp- and KKb-letters)
  Theorem410(Proof)      -> the R-S instantiation; Theorem 4.4's
                            analogue is Clifford+CS-TwoLevel's
                            MainLemma.relations-complete, ALREADY
                            PROVED -- no imported hypothesis
  Encoding, EncodingSem  -> tE.py's quads and K-pairs over Gray order
  Decoding, Lemma 8.7/8.8-> the open circuit-side design: multi-
                            controlled iZ- and K-boxes; Syntactics
                            will need a box schema from five wires
                            (CC(iZ) exists at three wires, det 1;
                            fully controlled iZ at width n is det-1
                            and must come from a W c V c recursion,
                            since no U_2(Z[1/2,i]) square root of iZ
                            exists -- eigenvalue trace zeta_8-sums
                            leave the ring)

Order of work: GenP' + fragment + PhasedPerm + NF (self-contained,
every proof has a template), then items (a)/(b) and Theorem 4.10's
analogue (completeness of the P'-theory), then the encoding, and the
circuit side last.

## Generation at width 4: CLOSED (tc.py 'gates,gates+')

With the colour scaffolding (both control colours of CX, C(iZ), CCX,
CC(iZ)) the enumeration closes: **the subgroup generated by the
encoded width-4 gates has index 4 in the two-level group at N = 16**,
i.e. 4-qubit Clifford+CS circuits are exactly the det-1 subgroup of
U_16(Z[1/2,i]) — modulo the scaffolding licences, each a circuit on
at most 3 wires justified by the width-2 (U_4) and width-3 (det +-1,
index 2, also closed) statements.  So the programme's premise holds:
the auxiliary language presents precisely the circuit group.

## The box recursion: the naive form fails (tBox.py)

Lambda^3(iZ) is NOT W . B . V . B for B = CC(iZ) re-placed and W any
doubly controlled letter from {iZX, iXZ, ZX, X} in any placement
(exhaustive over monomial operators, 0 solutions).  As in Clement,
whose box is a (1/sqrt2)^l-scaled sign rather than Lambda^k(-1), the
iZ-box must be defined by a recursion through K, with semantics a
(1/gamma)^l-scaled phase, and the letters decoded as combinations
where the scales cancel.  That design — Definition 2.4's analogue —
is the next piece, with the FiveQubit/GeneralN sources as templates.

## The K letter: the hybrid ki in place of KKb (2026-10-14)

Running the Reidemeister-Schreier proof showed two things.  (1) No
rule over {iib, mX, XX, KKb} used relation (16), and the model
K' = -K of every other two-level relation fails item (b) for (16)
(tM16.py): a (16)-carrying rule is unavoidable.  (2) With cosets
Z/4 by determinant and i, K both of degree 1, the action needs
K_[a,b] i_[0]^-1, which over KKb is the five-letter Q word on three
fresh indices, and every K obligation would go through a calculus of
Q words.  So the K letter is now the hybrid

    ki[a,b;s] = K_[a,b] i_[s]^-1        (det 1; KKb = ki . ki^-1),

and its rules are the two-level K relations read through the frame
embedding i_a -> i_a i_s^-1, X -> (-1)_s X, K -> K i_s^-1 at a sink s
off their indices ((4)-(9), (13), (14), (15)-(19) verbatim), plus the
sink move ki[a,b;s] . iib[s,t] = ki[a,b;t].  The action's K row is
(i_0 i_t^-1)^k . ki[d,e;t] . (i_t i_0^-1)^(k+1) for one fresh t, and the
frame transport act c y = T c . Phi_g y . T^- c' (T c = (i_0 i_g^-1)^c)
holds for every generator, coset and sink g off 0 and the generator
(tKI.py: rules at every admissible instance, 256/256 action cases,
1372/1372 transport cases at N = 8).  For the encoding, E(K_w) is now a
plain product of ki letters (2^(n-1) of them, the phases i_s^(2^(n-1))
vanishing from n = 3).

## The decoding constructions: what replaces the box (tDec.py, 2026-10-14)

No multi-controlled phase or K gate with every other wire controlling
is a circuit on its own (det i); the det-1 combinations the letters
denote are.  Two commutator identities and a borrowed-wire recursion
build them, all checked exactly at n = 4 and 5 (tDec.py):

    [X, S] = X S X S^-1 = iZ            [K, Z] = K Z K^-1 Z = X Z
    [L_{C2+a}(S_t), L_{C1}(X_a)] = L_C(S_t^3 . CZ_{a t})        (C = C1 + C2)
    [L_{C2+a}(K_t), L_{C1}(X_a)] = L_C(K_t) . L_C(i on a = 0)

With the split-control trick L_{C1+C2}([V,W]) = L_{C1}V L_{C2}W L_{C1}V^-1
L_{C2}W^-1 (Clement's box recursion is its instance [ZX, Z] = -I):

  (1) L^m(S_t)^3 = [L_{C2+a}(S_t), L_{C1}(X_a)] . L_{C+a}(Z_t), |C1| = 2:
      multi-controlled S with >= 2 idle wires, from fewer controls, a
      multi-controlled X (= K box K^-1) and a box.  Base CS.
  (2) L^m(K_t) = [L_{C2+a}(K_t), L_{C1}(X_a)] . X_a L^m(S_a)^3 X_a:
      multi-controlled K with >= 2 idle wires, likewise.  Base CK.
  (3) L^{n-1}(iZ_t) = L_{C1}(X_t) L_{C2}(S_t) L_{C1}(X_t) L_{C2}(S_t)^3,
      |C1| = 2: the consecutive phase pair pp a b (its C2-part has the
      two idle wires C1).
  (4) L^{n-1}(XZ_t) = [CK_{c->t}, L_{rest}(Z_t)]: the rotation, i.e.
      (-1)_a X_ab for consecutive a b -- Clement's CH B CH B with CK.
  (5) [L_{C2+a}(K_t), L_{C1}(X_a)] with C = all but t, a is
      K_(pair at a=1) K_(pair at a=0)^-1: a K pair.
  (6) ki a b s with s one wire-flip from a: L^{n-2}(G) for the 2-qubit
      G = L_u(K_w) . (-i at u=0, w=0) (det 1), by [V,W] = G with
      V = S1 K1 X0, W = S0 X1 S1 CS.  CAVEAT: at n = 4 the controlled
      V, W have det -1 (one idle wire each); valid from n = 5, or with
      V, W of det +-1 (tDec6.py: among the 4858 two-qubit words of
      length <= 5 with det +-1, the pairwise search did not finish in
      50 minutes of pure Python; inconclusive).  Alternatively ki = K
      pair times one hybrid, and the sink moves by pp.

The box itself (L^j(Z) with an idle wire) is Clement's recursion with
CCZX = L^2(ZX) a 3-qubit Clifford+CS circuit (det 1 on three wires).
Open: a uniform recursive definition (Definition 2.4's analogue) with
the idle-wire bookkeeping, the quads i_a i_b i_c i_d, and the Lemma
8.7/8.8 analogues on top.

## The hybrid at every width, and the n = 4 case closed (gadgets.py, hyb1.py, hyb2.py)

The sink can always be put on the pair: ki[a,b;s] = ki[a,b;a] . pp[a,s]
(the rule ki-sink).  With the sink on the pair the letter is a
1-qubit gate under n - 1 controls, G1 = K . diag(-i, 1) (a at t = 0) or
X K X . diag(1, -i) (a at t = 1), both of determinant 1 and order 3.
G1 is not a commutator of two "cheap" elements (reflections U Z U^-1
and rotations U XZ U^-1 of the 1-qubit Clifford group; gadgets.py), but
it is a commutator [A, B] with A a SQUARE in the 1-qubit Clifford group
(hyb2.py, 24 pairs each):

    a at t = 1:  A = (S S K S)^2,  B = K
    a at t = 0:  A = (K S)^2,      B = S S K S S  (= Z K Z)

so L^{n-1}(G1) = L_{C1}(A) L_{C2}(B) L_{C1}(A)^-1 L_{C2}(B)^-1 with
|C1| = 2, |C2| = n - 3, where L_{C1}(V^2) is Barenco's word of two-wire
gates C_{c1}(V) CX_{c1 c2} C_{c2}(V^-1) CX_{c1 c2} C_{c2}(V) (operator
order) under the controlled functor C(S) = CS, C(K) = CK, C(i) = S_c,
and L_{C2}(B) is the K-box (B = K) or a word of S- and K-boxes, each
with the two idle wires C1.  Checked at n = 4 against the letter's
matrix (hyb2.py).  So the n = 4 caveat of construction (6) is gone: no
2-qubit V, W and no det -1 factor.

gadgets.py also checks the recursions as circuits: Clement's box
Lambda-box k (W B V B), the rotation [CK, Ex box] = L^k(XZ), and the
Toffoli K box K^-1, at every k <= 5.

## The decoding, defined and checked (dec.py, 2026-10-14)

dec.py is the blueprint of the Agda decoding: every letter at n = 4
(pp 256, px 1920, dx 120 sampled, ki 1920 cases) and samples at n = 5
decode to the letter's matrix at the Gray numbering.  Frames (width
m + 3; U the box wire of the Z-box, A the borrowed wire, T the target):

    Sbox m  [U=0, T=1, c=2..m+1, A=m+2]
            = box(m+2) . [Toff(A; m, m+1), tau(m,m+2)(Sbox(m-1) with an idle wire on top)]
    Kbox m  [U=0, A=1, c=2..m+1, T=m+2]
            = Sbox(m)^3 . [Toff(A; 2, 3), tau(1,3)(Kbox(m-1) one wire up)]

from L^m(S) = Zbox . [L_{C1}X_A, L_{C2+A}S_T] and L^m(K) = L_C(S_A)^3 .
[L_{C1}X_A, L_{C2+A}K_T] (the general identity [L_{C2+a}G_t, L_{C1}X_a]
= L_C(G_t)^-1 . L_{C+a}(G^2_t)); the K recursion's correction is the
S-box in its own frame exactly, each recursion's child is placed by one
transposition at distance two (Clement's tau_02 pattern), and the
Toffolis are adjacent.  Base gadgets at width n, target 0, controls
1..n-1 (the S-/K-box re-framed by one cycle of the control wires):

    G_pp  = [Toff(0;1,2), L_{3..}(S_0)]                 i at bit 0 of the target
    G_rot = CK(1->0) B S_1 CK(1->0) B, B = Ex-conj(box(n-1))      = L^{n-1}(XZ)
    G_ki  = [Barenco(V = S^2 K S; 0; 1, 2), L_{3..}(K_0)]   = K_[a,b] i_a^-1, a at bit 1

A letter on a consecutive pair is the gadget placed by the layout of
the pair's codes (target where they differ, X on the white controls)
and oriented by the bit of the first index at the target (X on the
target): pp a (a+1) wants bit 0, the rotation (-1)_a X is XZ at bit 0,
the hybrid wants bit 1.  Then, in written order:

    pp a b    = the consecutive gadgets from a up to b, or the flipped
                ones from b up to a
    px a a b  = hi1 a . px (a+1) (a+1) b . lo1 a        (px-shrink_1, no parity)
    px b a b  = hi1 a . px (a+1) b (a+1)... i.e. hi1 a . hi(a+1) . lo1 a   (px-shrink_2)
    px c a b  = pp c a . pp c a . px a a b               (px-sign)
    dx a b c d = px a a b . px b c d                      (dx-split)
    ki a b a  = hi1 a . ki (a+1) b (a+1) . lo1 a   for b > a + 1: the rotation
                (-1)_{a+1} X_{a,a+1} carries K_[a+1,b] i_{a+1}^-1 to
                K_[a,b] i_a^-1, the sink travelling with the pair, so no
                fresh index is needed; consecutive: the hybrid gadget
    ki a b s  = ki a b a . pp a s                          (ki-sink)

where lo1 a = (-1)_a X_{a,a+1} and hi1 a = (-1)_{a+1} X_{a,a+1} are the
two orientations of the rotation.  The shrink rules px-shrink_3/_4
(from the top) are then genuine obligations of Lemma 8.8, unlike in
Clement's theory where the parity conditions make exactly one shrink
rule apply.

## Lemma 8.8 at n = 4: local search does not reach the identities (prover.py, prover2.py)

A prover by 3-wire window rewrites — every step a Lemma 5.1 step at
width 3 (commute two gates on disjoint wires, delete or canonicalise a
window on three wires through a dictionary of shortest words, pass a
gate through a neighbour) — explored 100k–250k words for each of the
first canonical identities (the phase gadget times its flip, its fourth
power, two adjacent phase gadgets commuting, the rotation times its
flip, PP^2 = ROT^2) without reaching them (prover2.py, fingerprints over
F_p; 13 minutes).  The identities are genuinely 4-wire: with
T = Toff(0;1,2) and C = CS_03, PP = [T, C], and PP . PP' = eps reduces by
3-wire steps to "C commutes with T C T", i.e. (conjugating by K_0, with
G = Lambda_3(U_0), U = K^-1 S K, U^2 = X, and D = CCZ) to "G commutes
with [D, G]" — a 2-wire gate against a commutator of a 3-wire gate with
itself, with no idle wire anywhere.  This is the shape of Clement's
schema (19) (Z on the box wire passes the box, equivalently the box
passes the CZ of its box wire and a fifth wire, (249)/(272)), which he
needs as an axiom from five wires on; here it appears at four.

So the next design question is the schema: which identities of that
shape to add to Syntactics at every width n >= 4 (candidates: a gate on
the box wire U passes the Z-box, as Clement's (19); or directly the
phase gadget commuting with the CS of its target and its S-box's idle
wire), chosen so that the rest of Lemma 8.8 follows by his method —
the box recursions expanded, all pairs of letters commuting by Lemma
5.1 or by the statement one width down.  Independence (that no schema
is derivable from the three-qubit rules) would need a model, as in
Independence/; soundness of any schema is one evaluation per width
(Soundness.Relators) only if stated at a fixed width, otherwise a proof
on controlled forms as Clement's box-Z.

## The three-qubit rules are incomplete at four qubits: the CS parity (parity.py, grpTC.py)

The number of CS gates mod 2 is invariant under every rule of
Syntactics (each has an even difference of CS gates between its sides,
in the Agda spellings CX = K^ CS CS K^ i, Swap = CX^3, X = K S S K i),
and under the structural rules; at width 3 it is the determinant, which
is why it survives completeness there.  At width 4 the determinant of
every generator is 1 and the parity is no longer semantic: the true
identity

    CX_32 . CCZ_012 . CX_32  =  CCZ_012 . CCZ_013

(a CNOT carries the CCZ on its target to the product of two CCZs; the
phase polynomial (-1)^{x0 x1 (x2 xor x3)}) has 25 CS gates on one side
and 42 on the other, so it is underivable: the three-qubit rules are
provably incomplete at four qubits, and any complete rule set needs a
rule with an odd CS difference.  Among all true identities of at most
three macro gates on four wires (CX, CS, Swap, S, K, X, CCZ, Toffoli),
the ones with odd parity are exactly the 276 placements of that
equation (CCZ_abc CCZ_abd CX_cd = CX_cd CCZ_abd and its variants), which
makes it the natural candidate schema.  The Toffoli form
CX_31 Toff(0;1,2) CX_31 = Toff(0;1,2) Toff(0;3,2) is its K-conjugate.

The phase gadget's own identity (TC)^2 = (CT)^2 (T = Toff(0;1,2),
C = CS_03) has even parity and is not touched by this invariant;
<T, C> has order 32 with that identity as its only defining relation
beyond T^2 = C^4 = 1 (grpTC.py).  Pushing C through Barenco's
decomposition of T leaves corrections Lambda_13(M_0) with
M = V^-1 S V S^-1 never diagonal (barenco.py), and reduces to the CCZ
control-XOR identity above, so the schema is where its derivation will
have to start.

## The schema is in: cx-ccz, and the first four-wire derivations (deriv.py, lemmas4.py, 2026-10-14)

Syntactics now has the one four-wire rule

    cx-ccz : CX10 ^^ . CCZ . CX10 ^^  ===  CCZ . Swap ^^ . CCZ . Swap ^^

over the shortcuts CS02 = Swap^ CS Swap^ and
CCZ = CS^ CX01 CS^ CS^ CS^ CX01 CS02 (Barenco, with the CNOTs between the
controls 0, 1).  Soundness is one four-wire evaluation (Relators.mD)
through by-relator; Weakening replays it (every rule has at most four
wires, so weakening is still unbounded); Parity is restated as the
independence of cx-ccz from the three-qubit rules (Circuit.Independence
at the selection noD of the instances not using it, Z/2 as Bool under
xor): cx-ccz-independent.  Everything through CompletenessInduction
rechecked green (DecodingChecks/KI1 279 s, Section8 163 s).

CS counts: CCZ has 21 CS gates in the Agda spelling (CS02's two swaps
are 12 of them), so the rule's sides have 25 and 54; the 42 of the
previous section counts two CCZs without the swaps that place the
second.

deriv.py checks a derivation step by step:
  win(i, j, rep)     rewrite the window cur[i:j], on <= 3 wires, to any
                     word on the same wires with the same operator (one
                     Lemma 5.1 step, given completeness on three wires)
  comm(i)            exchange adjacent gates on disjoint wires
  delta(i, forward)  the schema at any placement, either way
  lemma(name, i, fw) an earlier identity
Every step is checked semantically (fingerprints over F_p), so a
finished derivation is one of the circuit theory with the schema.
lemmas4.py has the first three (all ok):

  CCZ312-CCZ012  7 steps  two CCZs sharing two wires commute: with
                          c = CX_30 the schema reads c b c = b a; insert
                          c c, b b, c c and apply it twice
  CCZ123-CX30    7 steps  CCZ_123 passes CX_30, Barenco piece by piece
                          in three-wire windows
  T-CZ03-T      11 steps  Toff(0;1,2) CZ_03 Toff(0;1,2) = CCZ_123 CZ_03:
                          K D K^-1, K^-1 CZ_03 K = CX_30, the schema,
                          the two lemmas

Open: R0 = (T C)^2 = (C T)^2 with T = Toff(0;1,2), C = CS_03, the phase
gadget's identity.  By the quotient argument (grpTC.py) it does not
follow from the macro relations D^2 = 1, G^4 = 1, G^2 D G^2 = D E,
E central alone, so its derivation must open the gates; T-CZ03-T is
the first ingredient (it is the CZ_03-conjugation of T).

## R0 is derivable, from one more four-wire rule (lemmas5.py, 2026-10-14)

Every reduction of R0 = (T C)^2 = (C T)^2 (T = Toff(0;1,2), C = CS_03)
by three-wire windows and the schema led back to an equivalent
four-wire statement: C commutes with T C T; G = K0^-1 C K0 and
D = CCZ_012 satisfy (G D)^2 = (D G)^2; the commutator [D, G] = L_123(iX)
squares to E = CCZ_123; the swap of the controls 2, 3 fixes
PP = [T, C]; the Toffoli acting on a CCZ that shares one of its
controls substitutes, T CCZ_013 T = CCZ_013 CCZ_123 (L2).  The last is
the Toffoli analogue of cx-ccz (x0 -> x0 xor x1 x2 in (-1)^{x0 x1 x3})
and is now the second four-wire rule, toff-ccz.  The macro-level
quotient argument (grpTC.py) shows the macro relations alone do not
give R0; whether toff-ccz follows from cx-ccz with the three-qubit rules
is open (it is equivalent, given cx-ccz, to "the Toffoli white on wire 1
passes CCZ_012", a Clement (335)-type fact).

From the two rules R0 follows (lemmas5.py, 40 lemmas, every step
checked):
  - diagonal named gates (CS, CZ, CCZ on any wires) commute across four
    wires by re-spelling a CCZ with its CNOT's target off the other gate
    (ensure_comm), and two CCZs sharing two wires by the schema (lemma
    0's pattern); a product of named diagonal gates that is semantically
    trivial cancels after sorting (sort_diag);
  - T T13 = T13 T (under K0, the CCZs commute), CS13 passes T (the CCZ
    of T spelled with its CNOT's target 2), CCZ_013 T = T CCZ_013 E
    (toff-ccz), every named diagonal gate passes PP;
  - CX32 PP CX32 = CS13 CCZ_013 E PP and CX23 PP CX23 = PP CS12 CCZ_012 E
    (the schema under K0 gives CX32 T CX32 = T T13, and T13 C T13 = m C
    with m = L_13(iZ) = CS13 CCZ_013 is a window);
  - S3: Swap23 PP Swap23 = PP (64 steps: the two CX-conjugates, PP moved
    past the diagonal junk, which cancels);
  - S2: PP = [Toff(0;1,3), CS_02] (the swap conjugates letter by letter);
  - C commutes with [Toff(0;1,3), CS_02] by windows on {0,1,3} (C T13 =
    T13 m C, m diagonal passes everything, m T13 = T13 m^-1), hence with
    PP: R0.

Consequences (given Lemma 1 and R0): PP^2 = E, PP^4 = 1, PP . PP' = eps
(the flipped gadget is the inverse), and the CX from a control onto the
target maps PP to PP E = PP^-1.

The same analysis for the rotation ROT = [CK10, CCZ_023] = L_123(XZ):
F ROT F = ROT^-1 and CK10 ROT CK10^-1 = ROT^-1 are free (word algebra,
CK10^2 = S1^-1), X0 ROT X0 = ROT E is derivable (the schema under
CX10 on CCZ_023), and everything else reduces to ROT^2 = E, the 2T
torsion relation, which is open: the swap of the single control with a
control of F is the analogue of S3, and its CX-conjugates involve
K0 ROT K0^-1 (semantically ROT^-1).  The gadgets are L_123(P) for P in
the det-1 Cliffords 2T (PP: iZ, ROT: XZ, KI: X K X diag(1,-i)); the
core of Lemma 8.8 at n = 4 is the relations of L_123(2T) as words, plus
how three-wire gates act on them (colours, swaps of controls, gates on
the target) and the commutation of gadgets with different targets.

ROT^2 = E is derived after all (lemmas6.py, 16 more lemmas): the box
B = CCZ T1 CZ13 T1 CCZ CZ13 is the gate CCZ_023 (Lemma 1 at target 1),
so ROT = CK10 F CK10^-1 F = [CK10, F]; under K0 it is [CK10, Toff(0;2,3)]
(windows); under the swap of wires 1, 3 -- conjugating the four letters
by the three adjacent swaps, 139 steps -- it is [CK30, T]^-1; and
U0 PP U0^-1 = [T, CK30] by windows (U0 CS03 U0^-1 = CK30 CX30 S3 since
V = U S U^-1 = K X i, and CX30, S3 pass T, the Toffoli split with
V = U).  So ROT = K0 Swap13 U0 PP^-1 U0^-1 Swap13 K0^-1 and
ROT^2 = E from PP^-2 = E (R0 and Lemma 1).  The same mechanism should
give the hybrid's 2T relations: every gadget is a conjugate of PP by a
Clifford on the target and swaps of the controls.

## The derivations into Agda (scratchpad/four/, Four/, 2026-10-14)

A deriv.py derivation is lowered to primitive steps (four/prim.py,
four/lower.py) and written as an Agda module (four/emit.py), one per
derivation (Four/D/Dnnn.agda, INDEX.txt maps the names), a chain of
segment replacements over macro letters (Four/Chain.agda, Eq80's engine)
in blocks of eight steps between explicit lines.  The macro letters
(Four/Letters.agda, 99 of them) have canonical spellings: a gate on
adjacent wires is the lifted basic word, a gate on wires further apart
the gate one wire closer conjugated by the adjacent swap at its top
(stacked swaps), a three-wire gate on 0 1 2 or 1 2 3 literal and the
other two conjugates by one swap; mac.py checks every spelling against
its operator.  The primitive steps and their Agda:

  W  a literal window: the letters of the segment and the replacement are
     spelled off one wire m, Windows.win at the width-3 words with wire m
     deleted (tt tt for the avoidance, one Same evaluation);
  C  a structural commutation, wires 0..i-1 against i..3: low1-comm,
     low-comm, low3-comm (the last new, in Chain);
  R  a re-bracketing, by-assoc Eq.refl (unfolding or folding a stack);
  A  cx-ccz or toff-ccz at its canonical placement, Tools.ax;
  L  an earlier lemma.

A window whose letters are not spelled off one wire (a letter on wires
0 3 is spelled through 1 2) is conjugated by the adjacent swap bringing
its wires to 0 1 2 or 1 2 3, the swap pushed through every letter, and
the window taken literally there; a rule at another placement is the
canonical instance wrapped in the swaps of a word for the wire
permutation (breadth-first search over permutations, the words tried in
turn).  Pushing a swap through a letter: off the swap's wires it is a C
or a W; a stack with that swap outside unfolds and cancels; a letter
whose renaming is such a stack folds; a letter fitting with the swap in
three wires is a W; a stack whose outer swap commutes with the pushed
one is handled inside; the braid cases are found by a search over words
of atoms (adjacent swaps and literal gates) with cancellations, the
braid relation (a W on the top or bottom three wires), far
commutations, a swap against a gate in a window, and one window on a
whole word within three wires.  A three-wire letter is pushed through
piece by piece (its stack distributed over its Barenco pieces, the
renamed pieces collected again in the renamed letter's frame).  Two
letters on disjoint wires covering all four commute by unfolding one
and moving the other through its atoms.

Sizes: 56 derivations, 599 high-level steps, 6175 primitive ones
(2886 W, 1972 R, 1209 C, 23 A, 85 L); the longest, the swap
conjugation of the rotation's K-form, 743.

Two lessons from typechecking the generated modules: Windows.avoids was
false for a gate at the bottom of a word inserted below wire 0 (place-gen
zero never needed it), now true; and a lifted scalar iI ^ is a different
generator from iI (only the structural rule omega^=omega relates them),
so the scalar letters carry their lift (iota, iota1, ...), the basic-word
builders of mac.py lift it with the gate, and a scalar's lift counts as
its wire for the frame of a literal window.  Modules D001-D046 typecheck
in about 40 s each (S3, 252 steps, in 222 s).

## The commutation engine and the phase gadget's commutation facts (passes.py, lemmas10.py, lib4.py)

passes.py derives "A passes B" (A B = B A) for words of units (a macro
letter, or a coloured gadget X_S core X_S kept whole), checked
semantically before each attempt, by the first strategy that applies:
a window (three wires), structural commutation, re-spelling of two named
diagonals (ensure_comm), two coloured Toffolis on one target (diagonal
under K on the target), a diagonal word conjugated through permutation
letters (diag_through: windows, cx-ccz for a CNOT on a CCZ, toff-ccz for
a Toffoli sharing one control with a CCZ, T-CZ03-T for a Toffoli on a
CZ, K-conjugation when the target is off the diagonal; the result put in
canonical form by its phase polynomial, Moebius inversion), a
permutation letter whose target is off the other word (diagonal under
K), a coloured unit (its X's moved through the other word unit by unit,
each unit X-conjugated), unit by unit, and forms (a gadget rewritten
into another spelling by a lemma).  deriv.relabel moves a lemma to other
wires by conjugating it with adjacent swaps (a new swapconj step, which
the lowering implements by pushing the swap through the word), so a
fact proved once holds at every placement at the cost of the pushes.

Proved for the phase gadget PP (target 0, controls 1 2 3): the copies
white on {3}, {2,3}, {1,2,3} commute with it (same target, separated);
on targets 0 and 1 the copies separated on wire 3 (or 2 and 3), with
either colour at the other's target, commute; and the adjacent pair, all
black, sharing the basis state 1111 (not separated) commutes by a merge:
PP . X3 PP X3 = L_12(iZ_0) = CS12 CCZ012 (merge3: a black and a white
control merge into the gadget with one control less, a named diagonal),
so PP_1 = Q1 . X3 PP_1^-1 X3 with Q1 = CS02 CCZ012 named, which passes
PP_0, while X3 PP_1^-1 X3 is separated from PP_0 (adj01).  With
X-conjugation and relabelling this is every commutation of phase
gadgets at four wires: two placed phase gadgets either act on disjoint
pairs of basis states (then they are separated on a common control) or
share one (adjacent, as above).

Open, and the next obstacle: relations between different gadgets on the
same pair, the 2T relations.  The decoded px-conj2 is
PP . ROT = ROT . PP^-1; with ROT = (S0 K0) PP^-1 (S0 K0)^-1 it is
a b a^-1 = b^-1 for a = L_123(iZ), b = K0^-1 a K0 = L_123(iX) — an
identity in the block group of target-0 gates controlled by functions of
x1 x2 x3.  Letter by letter it fails: a = [Toff(0;1,2), CS03] and
b = [CCZ012, L_3(U_0)] (U = K^-1 S K) share no form whose letters pass
the other gadget.  The merge reduces it to "the controlled-on-3 version
of a three-wire identity", which would follow from a functor
Lambda_3 on three-wire circuits — but Lambda_3 of a generator is not a
circuit (CCS has determinant -1 at four wires).  The hybrid gadget's
relations (ki-x, ki-16, ki-ii, ki-sq at one pair) are of the same kind.
Separated commutations of non-diagonal gadgets (ROT or KI against a
coloured copy) need the engine to keep K-conjugated letters such as
L_3(U_0) = K0^-1 CS03 K0 as units (then the form [CCZ012, L_3(U_0)] of
K0^-1 PP K0 passes a white-on-3 diagonal letter by windows).

The block group behind the same-pair relations (scratchpad grp/blocks2.py,
not committed): with A = x1 x2 and B = x3 as the two control bits,
Gamma = <S0, K0, Toff(0;1,2), CS03> is the group of target-0 gates
(g00, g01, g10, g11) controlled by (A, B); |C1| = |<S, K>| = 96,
|<s,k,t>| = 1536, |<s,k,c>| = 9216, |Gamma| = 1179648, and its fully
controlled part {(1,1,1,x)} is Q8.  Gamma is generated by the P1-part
t^ (A-controlled Paulis), the C1-part c^ (B-controlled Cliffords) and
the diagonal C1, with [p^, c^_b] = n([p, b]) in the fully controlled Q8.
Window relations give only the relations inside <s,k,t> and inside
<s,k,c>; R0 says that c commutes with n([X,S]) = n(iZ).  So in the group
presented by windows and R0 the commutators n_{p,b} = [p^, c^_b] are
related only through R0 and conjugation by C1: nothing identifies two
commutators with the same value, and Q8's relations among them (Q1
among them) are not consequences.  Any derivation of Q1 must leave Gamma
— use gates on the control wires, as S3 did (CNOTs between controls) —
or use a new rule.

## The third four-wire rule, ck-tct (lemmas11.py, 2026-10-14)

    ck-tct : X0 CK(0->1) X0 . Toff(1;2,3) CS01 Toff(1;2,3)
           = Toff(1;2,3) CS01 Toff(1;2,3) . X0 CK(0->1) X0

K on wire 1 when x0 = 0 commutes with i^{x0 (x1 xor x2 x3)}, which acts
only where x0 = 1.  It is a commutation, so it changes no gate count:
neither the CS parity nor any other count invariant can separate it
(the per-wire count lattice of the other rules already has index 1,
invariants2.py).

With it the first same-pair relation follows (Q1, 141 primitive steps
with its lemmas): PP . b = b^-1 . PP for b = K0^-1 PP K0, i.e.
L(iZ) L(iX) L(iZ)^-1 = L(iX)^-1.  The route: the rule at the gadget
(X3 CK30 X3 passes PP: the rule at a = 3, t = 0 is exactly X3 CK30 X3
against T C T, and C^-1 is a window), its inverse, hence every
Lambda_not3(u) for u in <S, K> passes PP; K0 PPw3 K0^-1 is
[CCZ012, Lambda_not3(K S K^-1)], whose letters pass PP, so PPw3 passes
b; the merge writes PP = g . PPw3^-1 (g = CS12 CCZ012); and g b = b^-1 g
by windows (CCZ012 = Lambda_12(Z) is K0 Toff K0^-1, and the Toffoli turns
PP over: T PP T = PP^-1 letter for letter).

The hybrid gadget's relations need the rule with CK(a,t) in place of
CS(a,t) in the middle; that instance follows from the rule, because
K = i S (K S K^-1) S and K S K^-1 commutes with X, so
T Lambda_a(K) T = S_a (T Lambda_a(S) T) Lambda_a(K S K^-1) (T Lambda_a(S) T),
each factor commuting with Lambda_not_a(u).

Independence of ck-tct from the other rules is open.  No count
invariant can show it (it is a commutation; the count lattices are
full).  A model would have to be non-abelian, satisfy every
three-qubit relation on both windows, the two other four-wire rules and
the commutation of wire-0 and wire-3 gates, and fail the rule; models
built from the true semantics twisted by automorphisms of the
three-qubit groups are globally inner (the twist on a window must be a
conjugation by a gate on its outer wire), so they satisfy everything.
What remains is a central extension of the four-qubit group that splits
on both three-wire windows compatibly and has the rule's two sides not
commuting — a Schur-multiplier-type obstruction, not computed.  The same
is true of toff-ccz relative to cx-ccz.

## The gadget layer: separated, same-pair and adjacent facts (gadgetlib.py, samepair.py, consec4.py, 2026-10-14)

A gadget Gad(t, W, d, e) is X_W . d . PP_t^e . d^-1 . X_W: the phase gadget
on target t, conjugated by a target word d in <S, K> (96 elements with
phases, `W1`), inverted when e = -1, white on the controls W.  The
rotation is Gad(0, (), S K, -1) (`consec4.rot_gad`, from ROT-form and the
swap of wires 1 3).

**The controlled action, both ways.**  With a separating control c (the
gadget black on c), a gate controlled white by c passes the gadget
whether it acts on the target (`nc_pass`, the rule ck-tct) or on another
control w (`opp_pass`): spell the core with its CS from the third control
z, [Toff(t; c, w), CS(z, t)]; the Toffoli is then controlled by c and
the unit commutes with it on three wires, and with CS(z, t) on disjoint
wires.  (An earlier diagonal-span argument suggested this needed a new
rule; it overlooked conjugation by black-controlled Toffolis.)  The
colour-flipped version (`blk_pass`) is the same under X_c.

**Separated gadgets commute** (`sep_pass`), whatever their targets and
target words: split each gadget's target word off as gates controlled by
the separating wire (`ca_split`: d = Lambda_c(d) Lambda_not-c(d), and the
opposite half passes the core), so each gadget is controlled gates of its
own colour around a diagonal core; every controlled gate of one passes
the other gadget (the unit passes above), and the two diagonal cores
commute by the engine (its Col format).  So px-comm and the far cases of
px-conj hold at every placement at n = 4.

**The same-pair calculus** (samepair.py).  With T = Toff(0;1,2) and
C(w) = [T, Lambda_3(w_0)] for a target word w: C(S) is the gadget
literally, C(U') = eps for U' = K^-1 S K (T and Lambda_3(U') commute: K
turns T into CCZ012, which is diagonal), and the cocycle
C(v w) = C(v) . Lambda(v) C(w) Lambda(v)^-1 is two inserted cancelling
pairs; the controlled action identifies Lambda(v) g Lambda(v)^-1 with
g on its target conjugated by v (`caw`).  The braid S U' S = U' S U' is
exact, and computing C of both sides gives the core product relation
REL0: PP . Gad(S U') = Gad(U'), that is L(iZ) L(iX) = L(-iY).
Conjugated by any target word (`REL`) and with re-spelling (`spell`:
Gad(d, e) = Gad(d', e') when the gates agree, through S passing the core
and X0 PP X0 = PP^-1) every product of two gadgets on one pair is a
third (`prod`), so the gadgets on one pair satisfy Q8's relations.

**Derived so far at the canonical pair (target 0, black, orientation 0)
and the canonical adjacent pair (targets 0 and 1, all black, orientations
0 and 1):** px-conj2, p l = l p' (`F6`); px-conj on adjacent pairs,
p_{k+1} l_k = l_k p_k p_{k+1} (`F7a`).  The adjacent one merges the
rotation over wire 3 and the phase gadget over wire 2, so that the white
copies are separated from everything else, and what is left is one
identity of two three-wire gates, MB^-1 MA = MA MB^-1 a0, from the
definition of PP and the rule toff-ccz.  Next: the other adjacent case
of px-conj (the transposed configuration; relabelling F7a and F6), the
braid (Clement's (358) argument: merge each rotation over every
colouring of the two common controls into a two-wire rotation, the
two-wire braid word conjugates one rotation into the other), and the
hybrid gadget's facts.
