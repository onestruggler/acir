# Clément (2019): a complete set of relations for Uₙ(ℤ[1/√2])

A. Clément, *A complete set of relations for the real Clifford+T group*,
unpublished notes (supervised by N. J. Ross and P. Selinger), March 2019.
Formalized from the PDF of the notes.  The group is Uₙ(ℤ[1/√2]) = Oₙ(ℤ[1/√2])
(Lemma 1.1), the same group as Hadamard-Π's Theorem 4.14 (`QCert/HadamardPi`).

## Statements

```lean
-- QCert/Clement2019/Theorem.lean
theorem theorem_4_1 (n : ℕ) : IsPresentationOf (Rel (n := n)) (sem n)
-- QCert/Clement2019/Equivalence.lean (syntactic, no presentation theorem used)
theorem fig6_iff_clement (w v : Word (HadamardPi.Gen n)) :
    Derivable Fig6 w v ↔ Derivable Rel (ι w) (ι v)
theorem clement_iff_fig6 (w v : Word (Gen n)) :
    Derivable Rel w v ↔ Derivable Fig6 (tr w) (tr v)
theorem clement_tr (w : Word (Gen n)) : Derivable Rel w (ι (tr w))
theorem conGen_fig6 : conGen (Fig6 (n := n)) = (conGen (Rel (n := n))).comap ι (map_mul ι)
theorem conGen_rel : conGen (Rel (n := n)) = (conGen (Fig6 (n := n))).comap tr (map_mul tr)
```

* `Gen n` (Definition 1.5): `(-1)[j]`, `H[j,k]`, `X[j,k]` for any `j ≠ k`, in
  either order (Remark 1.6).  Indices from 0, as in the notes (Convention 1).
* `Rel` (Definition 3.3): equations (1)–(21) with their printed side
  conditions and the implicit `j ≠ k` of every `X[j,k]`, `H[j,k]`; (19) is
  stated with `j ≠ t` only, so `k = l` is allowed (Remark 3.4); (20) and (21)
  at the indices `0, …, 3` and `0, …, 5` (so present when `n ≥ 4`, `n ≥ 6`);
  (22) when `n = 2` (the Note after Remark 3.4).
* `sem n` sends `H[j,k]` to `levelMat ![j,k] H` (first row and column at `j`,
  Definition 1.2), into `O_ZInvSqrt2 n`.
* `ι` includes Hadamard-Π's generators (increasing indices); `tr` writes
  `X[k,j]` as `X[j,k]` and `H[k,j]` as `X[j,k] H[j,k] X[j,k]` for `j < k`
  (Lemma 1.7).  The equivalence theorems say that each theory's congruence
  is the pullback of the other's, in every dimension (ι induces an
  isomorphism of the presented monoids).  They are proved syntactically,
  relation by relation, and do not depend on any `sorry`.

## Status

| Part | Status |
|---|---|
| Soundness of (1)–(22) (Section 3.5), grouplike | proved (exact checks over ℤ√2 in dimension ≤ 6) |
| Generation (Lemma 1.4) | proved, through the words of Hadamard-Π's Algorithm 1 (`lemma_1_4`) |
| Equivalence with Figure 6 | proved syntactically, no `sorry` (`Equivalence.lean`) |
| Completeness (Theorem 4.1) | from Hadamard-Π's `theorem_4_14` through the equivalence; no `sorry` of its own |

`#print axioms theorem_4_1` shows `[propext, sorryAx, Classical.choice,
Quot.sound]`: the `sorryAx` is the one of `QCert/HadamardPi/Case9.lean`
(`case9_four`), reached through `theorem_4_14` only.  The equivalence
theorems (`fig6_iff_clement`, `clement_iff_fig6`, `clement_tr`,
`conGen_fig6`, `conGen_rel`) depend on `[propext, Classical.choice,
Quot.sound]` only.  Clément's own proof of Theorem 4.1 (his Main Lemma 4.4,
Section 5) is not formalized here.

## The equivalence

| File | Content |
|---|---|
| `RelK.lean` | `RelK full`: (1)–(19) and, when `full`, (20), (21) at every injective placement; invariant under injective maps of indices (`Derivable.mapC`); `RelK false ⊆ Rel` |
| `CheckC.lean` | a checker for derivations from Clément's relations on concrete indices (`deriveC_of`, by `decide +kernel`), moved to any distinct indices by `derC_map` |
| `ConjLemmas.lean` | (generated) from (1)–(19) on at most four indices: Lemma 3.5 along its printed proof, Lemma 1.7, conjugation of each generator by `X[0,1]` |
| `Conj.lean` | conjugation by `X[i,j]` renames `i, j` in every word (`n ≥ 3`); `Rel` is invariant under permutations of the indices (`rel_perm`), so (20), (21) hold at every placement and `RelK true ⊆ Rel` (`relK_rel`) |
| `DerivedC.lean` | (generated) Figure 6's (d3) from (20) and (19) on four indices, (d4) from (21) on six (`kd3`, `kd4`) |
| `FromFig6.lean` | every relation of Figure 6 in Clément's theory (`fig6_rel`): (a1)–(d2) are among (1)–(18); (d3), (d4) are `kd3`, `kd4` moved |
| `Translate.lean` | `ι`, `tr`, both preserve the matrices; `tr ∘ ι = id` |
| `Patterns.lean` | a relation of Clément's as a scheme on `a` indices; any injective instance is an increasing one after a permutation of its indices (`exists_sort`), so a scheme holds in Figure 6 once it holds at the `a!` arrangements of `0, …, a-1` |
| `Tables.lean` | (generated) the Figure 6 derivations of (1)–(19) and (22) at every arrangement of their indices; for (19), (f1) conjugated by `X`'s of adjacent transpositions |
| `ToFig6.lean` | every relation of Clément's, written over `𝒢ₙ`, in Figure 6 (`rel_fig6`): (1)–(19), (22) by the tables, (20), (21) by Hadamard-Π's `c20`, `c21` |
| `Equivalence.lean` | Lemma 1.7 in `Rel` (from Lemma 3.5 when `n ≥ 3`, from (22) when `n = 2`), `clement_tr`, the equivalence theorems |
| `gen/` | the Python scripts that search and check the derivations (see its README) |

The derivation of (d3) from (20): with `A = H[0,1]`, `B = H[2,3]`,
`Q = H[0,2] H[1,3]` and the signed permutation `M = Q (-1)[0] (-1)[1] Q`,
which carries `A` to `B`, (20) is `A Q A Q ≈ Q A Q B`; with (19), which is
Hadamard-Π's (f1) (`Q B ≈ B A Q A`), both `Q B Q B A` and `B Q B Q B` are
`Q A Q`, and then `(B Q)⁴ ≈ (B Q B Q)(Q B Q B A B) ≈ A B`, which is (d3).
The derivation of (d4) from (21) reverses the derivation of (21) from (d4)
of `HadamardPi/Derived.lean`: (21) is `T' T T' ≈ M' T M'` for
`T = Q A Q`, `T' = R A R`, `R = H[0,4] H[1,5]`, `M' = R (-1)[0] (-1)[1] R`.

## Notes on the transcription

* Equation (22) is stated only for `n = 2`, where the Note says it "has to be
  added"; Lemma 3.5 derives it from (1)–(15) when `n ≥ 3` (`ConjLemmas.c22`,
  following the printed proof; every line of the proof checks numerically).
  Two of its steps, labelled (15) and (14), apply those relations with the
  conjugating `X` on the other side, which needs (3) as well (Lemma 3.8).
* (20) and (21) are only stated at the first four and six indices, as printed;
  at other indices they follow by conjugating with transpositions (`Conj.lean`).
* No error was found in the relations: all of (1)–(22) are sound (checked
  exactly), and every derivation step was checked numerically before it was
  checked in Lean.
