# Bian–Selinger: generators and relations for Uₙ(ℤ[1/2, i])

X. Bian and P. Selinger, *Generators and relations for Uₙ(ℤ[1/2, i])*,
QPL 2021 (EPTCS 343), arXiv:2105.14047.

## Main theorem

```lean
theorem QCert.BianSelingerUn.presentation (n : ℕ) : IsPresentationOf (Rel n) (sem n)
```

(`Theorem.lean`) is the paper's Theorem 3.1 for **every** `n`: the one- and
two-level matrices `X_[j,k]`, `K_[j,k]` (`j < k`) and `i_[j]` (`Gen n`,
§3.1) with the relations (1)–(19) of Figure 1 (`Rel n`) present the group
`U_ZHalfI n` of unitary `n × n` matrices over `ℤ[1/2, i]`.

**There is no `sorry`.** `#print axioms QCert.BianSelingerUn.presentation`
gives `propext, Classical.choice, Quot.sound`.

## Conventions

* Indices start at `0`, as in the paper.
* A word `w` denotes the product of its letters' matrices in the written
  order (`FreeMonoid.lift (sem n)`, written `⟪w⟫` locally); a state `s` is
  an element of `U_ZHalfI n` and `⟪w⟫ * s` is the paper's `w s`.
* `K† = K⁷` (`K` has order 8 by (3)).
* Numerators are Gaussian integers: `HasNum v k w` says `γᵏ v = w` with
  `γ = 1 + i`, and `lde v` is the least such `k` (Definitions 2.1, 2.4).

## Correspondence with the paper

| Paper | File |
| --- | --- |
| §3.1 generators, Figure 1 (relations (1)–(19)) | `Syntax.lean` |
| matrices of the generators, Definition 2.5 | `Semantics.lean` |
| Remark 3.2 (soundness of Figure 1), invertibility of the generators | `Soundness.lean` (via `Transfer.lean`: each relation on `m ≤ 4` symbolic indices is the image of the same relation on `0, …, m-1`, decided over `ℚ(ω)` by `decide +kernel`) |
| §2.1: `γ`, parity, least denominator exponents, Lemmas 2.3, 2.7, 2.9 | `Gaussian.lean` (Lemma 2.3 is `exists_normal` in `Case3222.lean`) |
| Algorithm 2.14 (pivot, profile), Definition 2.15 (levels) | `Algorithm.lean` |
| step 3 of Algorithm 2.14 (syllables) | `Syllable.lean` |
| Theorem 2.16 (the syllable lowers the level), normal words of §3.2 | `Normal.lean` |
| §3.4: `Step` (Lemma 3.6 for one edge), squares, from the Main Lemma to completeness | `Induction.lean`, `Square.lean` |
| Lemma 3.4 (generators as words of basic generators) | `Decomp.lean` |
| the level remark in the proof of Lemma 3.4 | `LevelBound.lean` |
| derivations in the monoid of words modulo `ℛ` | `Pres.lean` |
| Figure 2, relations (21), (22), (23), (28); (15) and (17) for `K†` | `Derived.lean` |
| Figure 2, (24), (25), conjugation by `X_[j,ℓ]` | `Derived2.lean` |
| Figure 2, (27); the square of the special case; the faces of Case 3.2.2.2 | `Derived3.lean` |
| Lemma 3.7 (Main Lemma), Case 1 (`G = i_[0]`) | `MainI.lean` |
| Lemma 3.7, Case 2 (`G = K_[0,1]`) and the base case (`s = I`) | `MainK.lean` |
| Lemma 3.7, Case 3 (`G = X_[α,α+1]`), Case 3.1 | `MainX.lean` |
| Lemma 3.7, Case 3.2 | `MainX2.lean` |
| Lemma 3.7, Case 3.2.2.2 with four odd entries: the special case | `Special.lean` |
| Lemma 3.7, Case 3.2.2.2 with four odd entries: the general case | `Case3222.lean` |
| Lemma 3.6, Theorem 3.1 | `Completeness.lean`, `Theorem.lean` |

The induction of §3.4 is the shared module `QCert/Synthesis.lean`
(`NormalWords`, `step_of_main_lemma`): `Completeness.lean` supplies the
normal words (`nw`, which reduce every state to `I`), the Main Lemma for the
basic generators `i_[0]`, `K_[0,1]`, `X_[α,α+1]`, and Lemma 3.4.

## Formalization choices

* **Squares.** A square of the Main Lemma at a state `s` with generator `x`
  is a relation `N' x ∼ G' N` (`N`, `N'` the syllables of `s` and `x s`)
  and a path `G'` from `N s` all of whose states lie below `level s`
  (`AllBelow`). Paths of `X` and `i` letters on indices at most the pivot
  keep every column profile, so they stay below (`allBelow_mon`); paths with
  `K` letters are checked state by state.
* **Lemma 3.4.** The paper notes that the basic edges replacing a simple
  edge `s → r` stay at levels at most `max(level s, level r)`; this is
  proved in `LevelBound.lean` (the intermediate states are permutations of
  `s` or `r` fixing the indices above the generator's largest index).
* **Case 3.2.2.2 with four odd entries.** The paper reduces the general
  case to the special case (entries `≡ 1 mod γ³`) with the diagonal word
  `D` of Lemma 2.3 and draws the resulting figure. Here the outer square
  `N' X ∼ E'⁻¹ G'' E N` is assembled from its faces (`F1`–`F5` in
  `Case3222.lean`, with `Derived3.face` and `special_sq`), and in `G''` each
  `K†_[a,b]` is written `i_[a] i_[b] K_[a,b]` (equal to `K⁷` by (17), (18)),
  so that every state of the path is, up to a diagonal word, a state of the
  special chain `C₁ … C₄` of `Special.chain` (whose levels drop because the
  number of odd entries drops).
* **Figure 2.** Only the relations of Figure 2 that the proof of the Main
  Lemma uses are derived ((21)–(25), (27), (28), and the special square);
  the paper calls their proofs straightforward.

## General lemmas (used by `QCert.Greylyn` too)

* `LevelCalc.lean`: products, powers and actions of one- and two-level
  matrices (`twoLevel`, `oneLevel`, `levelMat_mul`, `twoLevel_mulVec`, …).
* `Transfer.lean`: the transfer of identities of level matrices on symbolic
  indices from a computation over `ℚ(ω)`.

## Paper errors

None found: every relation of Figure 1 is sound (checked by computation),
and every case of the Main Lemma goes through as the paper describes it.
The only additions are proofs the paper leaves to the reader (the relations
of Figure 2 that are used, the level remark of Lemma 3.4, and the
reduction of the general to the special case in Case 3.2.2.2).

## Building

```
wsl --exec bash -lc 'cd /mnt/d/work2/acir/Lean && ./check.sh QCert/BianSelingerUn/Theorem.lean'
```
