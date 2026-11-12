# Figures

The `.tikz` files here are of two kinds.

- **TikZiT figures**, which TikZiT can open and save:
  `qubit-fragments-plain.tikz` (Figure 2), `qubit-progress-plain.tikz`
  (Figure 9) and `amy-*.tikz`. `qubit-fragments.tikz` and
  `qubit-progress.tikz` are the earlier versions of those two figures, which
  the paper no longer inputs: their rose boxes also name the family whose
  group they share (`= Gaussian for k ≠ 2`), and each copy differs from its
  original in those three lines only.
  `equacert-qudit-overview.tikz` and `equacert-qudit-route.tikz` drew the
  qudit Clifford case study, which the paper no longer has. Load `figures.tikzstyles` in TikZiT (Styles > Open) before
  opening them. The named colours and the status marks (`\pdone`, `\pchecked`,
  `\ppartial`, `\popen`) are defined in `../qcert.sty`, since a TikZiT file may
  hold only nodes and edges. When TikZiT saves a file it drops anchors other
  than `.center` (`(integral.west)` becomes `(integral)`) and rewrites
  non-integer `out`/`in` angles, so the figures use neither. An arrow with
  bends is a chain of straight edges from its source box through waypoint
  nodes (`w1`, `w2`, ...) to its target box; its ends stay attached when a box
  is moved, and its corners are where the waypoints are. A crossing is marked
  by a white underlay under the arrow drawn later.
- **Hand-written TikZ**, which TikZiT cannot read: `equacert-pipeline.tikz`
  (Figure 1) and `equacert-soundness-completeness.tikz` (Figure 4). They draw
  icons and panels with paths, curves and loops. Edit them as text; opening
  one in TikZiT and saving it replaces it with an empty picture.

`xcxccx/` has its own TikZiT styles (`xcxccx/xcxccx.tikzstyles`).
`xcxccx/draw_lafont.py` writes Lafont's cycle, relations, stairs, rewriting
rules and canonical forms (`lafont-*.tex`), for Section 3 (the introduction
to the framework on the alternating groups) and Section 7, after checking
each against the permutations it draws.

## Notes on Figure 2 (`qubit-fragments.tikz`)

Literature audit (generation is distinct from completeness of relations).
AGR20, arXiv:1908.06076: the six restricted matrix families are Eqs.
(2), (5), (7), (9), (10), (13), with generation Theorems 5.5, 5.10,
5.15, 5.20, 5.26, 5.30 and one-clean-ancilla circuit Corollaries
5.6, 5.11, 5.16, 5.21, 5.27, 5.31, respectively.
GS13, arXiv:1212.0506: Lemma 6 and Theorem 1 give the full ring case.
LRS21: Definitions 5.1--5.2 and Theorem 5.7 give the scaled real group.
BS21: Figure 1, relation (15), gives the Gaussian X redundancy below.
FHK26: Definition 4.5 and Theorem 4.8 give the real matrix generators.

The displayed families are reductions of the published lists:
real: X_[a,b] = H_[a,b] (-1)_[b] H_[a,b];
imaginary: X_[a,b] = F_[a,b]^2 (-1)_[b] F_[a,b]^6;
Gaussian and super-Gaussian:
X_[a,b] = (omega H)_[a,b] i_[b]^2 (omega H)_[a,b]^dagger;
full ring: X_[a,b] = H_[a,b] omega_[b]^4 H_[a,b], T_[a,b]=omega_[b].
These are exact embedded-block equalities, with identity outside the block.
The two BS21 Hadamard phase conventions are inverses of one another.

For the scaled real group, put J=I_(n/2) tensor H. Then
J (-1)_[2j+1] J = X_[2j,2j+1]. On a consecutive quartet (a,b,c,d),
R=(H tensor H)_[a,b,c,d] satisfies R X_[c,d] R = X_[b,d], and
X_[c,d] X_[b,d] X_[c,d] = X_[b,c]. Hence all adjacent transpositions
are generated, and X can be omitted. For n=2 the first identity suffices.

The super-Gaussian group equals G union omega*G, G=U_n(D[i]):
even q gives G; for odd q, omega^-1 2^(-q/2)M=(1-i)M/2^((q+1)/2).
Thus the former product notation was not a direct-product assertion.
Greylyn14 (n=4), BS22 (2 qubits), BS23 (3 qubits), and ARW24
(3 qubits) do not supply unrestricted-width completeness results here.
Amy et al. 2023, arXiv:2305.11305, improves synthesis in the same
integral/scaled-real groups. Mukhopadhyay 2024,
doi:10.1038/s41598-024-64558-8, gives CS synthesis and generators modulo
Clifford, not another multi-level matrix family for this figure.

Each main node pairs circuit gates with its exact-synthesis matrix group
(at most one clean ancilla) and reduced multi-level generators.
n = 2^k is the matrix dimension; k >= 1 is the number of qubits.

## Notes on Figure 9 (`qubit-progress-plain.tikz`, `qubit-progress.tikz`)

Companion to qubit-fragments.tikz: preserve its nodes and inclusion edges.
Status audit: relations_status.pdf (7 Nov 2026), pp. 1--3, Notes 13--15,
and imaginary section, item 10; EquaCert MainTheorems.agda / Table 1.
Q marks an explicit corpus presentation, not an unformalized gate-set transfer.
The dagger records the new Toffoli-Hadamard theory announced in this paper;
its mathematical exposition is in preparation.
Integral k=3 is W(E8), not the extended alphabet presenting O_8(D).
Below three wires the displayed Toffoli-Hadamard alphabet is literally real Clifford.
Pure CS at small widths differs from the CS+omega theory in Minimality.
Imaginary U_2/U_3 Lean proofs are outside this corpus and use native_decide.

In both figures the arrows from Real Clifford to Toffoli--Hadamard and from
Gaussian to Clifford+CS are drawn over white underlays, which mark where they
pass over other arrows.
