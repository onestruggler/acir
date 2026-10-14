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
