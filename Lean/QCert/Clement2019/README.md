# Clément (2019): a complete set of relations for Uₙ(ℤ[1/√2])

A. Clément, *A complete set of relations for the real Clifford+T group*,
unpublished notes (supervised by N. J. Ross and P. Selinger), March 2019.
Formalized from the PDF of the notes.  The group is Uₙ(ℤ[1/√2]) = Oₙ(ℤ[1/√2])
(Lemma 1.1), the same group as Hadamard-Π's Theorem 4.14 (`QCert/HadamardPi`).

## Statements

```lean
-- QCert/Clement2019/Theorem.lean
theorem theorem_4_1 (n : ℕ) : IsPresentationOf (Rel (n := n)) (sem n)
-- QCert/Clement2019/Equivalence.lean
theorem fig6_iff_clement (w v : Word (HadamardPi.Gen n)) :
    Derivable Fig6 w v ↔ Derivable Rel (ι w) (ι v)
theorem clement_tr (w : Word (Gen n)) : Derivable Rel w (ι (tr w))
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
  (Lemma 1.7).  `fig6_iff_clement` and `clement_tr` together say that the two
  theories generate the same congruence in every dimension (ι induces an
  isomorphism of the presented monoids).

## Status

| Part | Status |
|---|---|
| Soundness of (1)–(22) (Section 3.5), grouplike | proved (exact checks over ℤ√2 in dimension ≤ 6) |
| Generation (Lemma 1.4) | proved, through the words of Hadamard-Π's Algorithm 1 (`lemma_1_4`) |
| Completeness (Theorem 4.1) | `sorry` in `theorem_4_1` (the field `complete`): Clément's Main Lemma (Lemma 4.4, Section 5) is not formalized |
| Equivalence with Figure 6 | proved from the two presentation theorems (so it inherits their `sorry`s) |

## Remaining `sorry`s

* `theorem_4_1`, field `complete`: Theorem 4.1 (completeness), i.e. Lemma 4.4
  and its proof in Section 5 (Cases 1–3, Case 3.4 being the case Hadamard-Π
  misses).
* Through `theorem_4_14`, `fig6_iff_clement` and `clement_tr` also depend on
  the two `sorry`s of `QCert/HadamardPi/MainLemma.lean`.

## Notes on the transcription

* Equation (22) is stated only for `n = 2`, where the Note says it "has to be
  added"; Lemma 3.5 derives it from (1)–(15) when `n ≥ 3`.
* (20) and (21) are only stated at the first four and six indices, as printed.
