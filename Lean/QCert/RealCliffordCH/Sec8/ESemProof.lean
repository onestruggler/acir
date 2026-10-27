/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: the encoding preserves the semantics

The encoding of Definition 8.2 is a monoid homomorphism into words over
`𝒫_{2ⁿ}`, and `toP` (the operator in the basis ordered by the Gray code) is
multiplicative, the Gray code being a bijection; so it suffices that the
encoding of each generator is proper and has the generator's matrix, which
is `ESem.Encode.encAt_sem`.
-/
import QCert.RealCliffordCH.Sec8.Statement
import QCert.RealCliffordCH.Sec8.ESem.Encode

namespace QCert.RealCliffordCH.Sec8

/-- The encoding preserves the semantics (Definition 8.2, used in the proof of
Theorem 8.9). -/
theorem esem (n : ℕ) (hn : 3 ≤ n) : ESem n := by
  intro w
  induction w using FreeMonoid.inductionOn' with
  | one =>
    refine ⟨fun p hp => by simp at hp, ?_⟩
    rw [map_one, pSem, map_one, map_one, OneMemClass.coe_one, toP_one]
  | mul_of g w ih =>
    obtain ⟨hp, he⟩ := encAt_sem hn g
    have ew : encW n (FreeMonoid.of g * w) = wordOf (encAt n 0 g) * encW n w := by
      rw [map_mul, encW, FreeMonoid.lift_eval_of]
    rw [ew]
    refine ⟨fun p hp' => ?_, ?_⟩
    · rw [FreeMonoid.toList_mul, List.mem_append] at hp'
      exact hp'.elim (hp p) (ih.1 p)
    · rw [pSem, map_mul, ← pSem, ← pSem, he, ih.2, map_mul (S.sem n), Submonoid.coe_mul, toP_mul]
      rfl

end QCert.RealCliffordCH.Sec8
