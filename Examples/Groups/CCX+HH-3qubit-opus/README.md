# Three-qubit Toffoli–Hadamard circuits

Amy, Ross and Wesley, [*A Sound and Complete Equational Theory for 3-Qubit
Toffoli-Hadamard Circuits*](https://arxiv.org/abs/2407.11152) (QPL 2024),
formalised on this repository's `Word` and `Presentation` framework.
`Theorems.agda` is the entry point:

- `theorem-5-2`: the circuits over Σ₁ (the Toffoli-K gates, K_[0,1,2,3] and
  CCZ) modulo R₁⁺ = Figure 4 ∪ Figure 7 ∪ {r_K} present O(8, 𝔻);
- `theorem-6-3`: the circuits over Σ₂ = Σ₁ ∪ {H₂} modulo R₂⁺ = R₁⁺ ∪
  Figure 8 present TofH(3);
- `r_K-independent`: r_K, the relation K₁₂ = X₀ NK X₀ NK that the paper's
  Section 5.5 uses, holds of the matrices but does not follow from Figures 4
  and 7, so R₁ alone is not complete.

Gates are numbered with qubit 0 the most significant (basis state
`4 x₀ + 2 x₁ + x₂`), and words are in operator order. The misprints of the
paper are corrected; [`ERRATA.md`](ERRATA.md) lists every error found, and
`Errata.agda` refutes each printed equation that is false.

## The proof

Completeness is by translation into Li, Ross and Selinger's presentations
(`CCX+HH-TwoLevel`, and its `Scaled/` part for TofH(3)), which the repository
proves complete:

- **Encoding.** A circuit denotes the matrix of a word over their generators
  (`Encoding`, `Semantics`); soundness by computation (`Soundness`,
  `SoundnessH`).
- **Decoding.** Their generators (-1)_[a], X_[a,b], K_[a,b,c,d] are m0, T 0
  and NK of Figure 7 carried by permutation circuits ("frames") to their
  indices (`Decode`). The frame lemma (`Perm`) says the result depends only on
  where the frame sends the base's indices, since the circuits above them
  commute with the base (Figure 7's (85)–(93)). It rests on the completeness
  of the circuit presentation of S₈ (`Examples/Groups/Symmetric`), transferred
  to the circuits T d of Figure 7 through their Coxeter relations. So every
  relation of Table 1 is carried by one frame (`Frame`) to its standard
  instance, which is a relation of Figure 7 or a Coxeter relation (`dec-cong`).
- **Decoding the encoding gives the circuit back.** `Good` holds of T d,
  (-1)_[0] and NK, is closed under products and, by soundness and Li, Ross and
  Selinger's completeness, under R₁⁺, and so follows each gate's definition in
  Figure 4 (`Completeness`).
- **The circuit identities** that this needs — the Coxeter relations for the
  T d, and the identities leading from them to every gate — are derived from
  Figure 4 by a search (`gen/`), and checked by the rewriting engine
  (`Engine`, `Toffoli/`, `Derived`).
- **Surjectivity.** The decoding of a generator has its matrix, by induction
  along Li, Ross and Selinger's reduction of a generator to a basic one
  (`PresentationO8.dec-sem`).
- **TofH(3).** Lemma 6.1, H₂ passes every circuit over Σ₁ (`Push`), decodes
  Table 2 (`DecodeH`); the rest is as for O(8, 𝔻) (`PresentationH`).

## Checking

Agda 2.8.0, standard-library 2.4, and EucDomain registered. Check
`Theorems.agda`, `GateMatrices.agda` and `Errata.agda`; together they reach
all 31 modules of the development (and `CCX+HH-TwoLevel`, `Symmetric`). Given
the interfaces of those, `Theorems.agda` takes about 4.5 minutes from scratch
in one process, with a peak of 3.1 GB (`+RTS -M4G`), and the other two half a
minute each.
