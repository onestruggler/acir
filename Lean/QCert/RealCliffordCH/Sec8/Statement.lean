/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: completeness from three wires on, from its four ingredients

The proof of Theorem 8.9 for `n ≥ 3`: two circuits with the same semantics
have encodings with the same matrix (`ESem`, the encoding preserves the
semantics), which are therefore equal by Figure 8 (`Thm410`, Theorem 4.10);
the decoding respects Figure 8 (`Lemma88`, Lemma 8.8) and inverts the
encoding (`Lemma87`, Lemma 8.7).  The proofs of Lemmas 8.7 and 8.8 use
completeness on fewer wires (Lemma 5.1), so they are stated with it as a
hypothesis, and completeness follows by induction on the number of wires
(`Theorem.completeness`).  `complete_of` is that argument; the four
statements are proved, or not, separately.
-/
import QCert.RealCliffordCH.Sec8.Decoding

namespace QCert.RealCliffordCH.Sec8

/-- Completeness on `n` wires. -/
def CompleteAt (n : ℕ) : Prop :=
  ∀ w v : Circ n, S.sem n w = S.sem n v → Derivable (theory n) w v

/-- Theorem 4.10 (completeness part) for `N = 2ⁿ`: proper words over `𝒫_N` with
the same matrix are equal by the equations of Figure 8. -/
def Thm410 (n : ℕ) : Prop :=
  ∀ u v : Word (PG (2 ^ n)), ProperW u → ProperW v → pSem u = pSem v → Derivable (Fig8 n) u v

/-- Lemma 8.7 on `n` wires, given completeness on fewer wires: decoding the
encoding of a circuit gives the circuit back. -/
def Lemma87 (n : ℕ) : Prop :=
  (∀ k < n, CompleteAt k) → ∀ w : Circ n, Derivable (theory n) (decW n (encW n w)) w

/-- Lemma 8.8 on `n` wires, given completeness on fewer wires: the decoding
maps every equation of Figure 8 to an equation derivable from Figure 4. -/
def Lemma88 (n : ℕ) : Prop :=
  (∀ k < n, CompleteAt k) → ∀ u v : Word (PG (2 ^ n)), Fig8 n u v →
    Derivable (theory n) (decW n u) (decW n v)

/-- The back-and-forth argument of Theorem 8.9 (and of Lemma 7.6): from the
four statements on `n` wires and completeness on fewer wires, completeness
on `n` wires. -/
theorem complete_of {n : ℕ} (hE : ESem n) (hT : Thm410 n) (h87 : Lemma87 n) (h88 : Lemma88 n)
    (ih : ∀ k < n, CompleteAt k) : CompleteAt n := by
  intro w v h
  obtain ⟨pw, sw⟩ := hE w
  obtain ⟨pv, sv⟩ := hE v
  have hp : pSem (encW n w) = pSem (encW n v) := by rw [sw, sv, h]
  have d := hT _ _ pw pv hp
  let c : Con (Word (PG (2 ^ n))) := (conGen (theory n)).comap (decW n) (map_mul _)
  have hc : conGen (Fig8 n) ≤ c := Con.conGen_le fun a b hab => h88 ih a b hab
  have dd : Derivable (theory n) (decW n (encW n w)) (decW n (encW n v)) := hc d
  exact ((h87 ih w).symm.trans dd).trans (h87 ih v)

/-! ## The four statements -/

/-- The encoding preserves the semantics (Definition 8.2, used in the proof of
Theorem 8.9).  Not yet proved. -/
theorem esem (n : ℕ) (hn : 3 ≤ n) : ESem n := by
  sorry

/-- Theorem 4.10 (Appendices A.3 and A.4).  Not yet proved. -/
theorem theorem_4_10 (n : ℕ) (hn : 3 ≤ n) : Thm410 n := by
  sorry

/-- Lemma 8.7 (via Lemma 8.6, Appendix E.4).  Not yet proved. -/
theorem lemma_8_7 (n : ℕ) (hn : 3 ≤ n) : Lemma87 n := by
  sorry

/-- Lemma 8.8 (Appendix E.5, with Appendix D).  Not yet proved. -/
theorem lemma_8_8 (n : ℕ) (hn : 3 ≤ n) : Lemma88 n := by
  sorry

/-- Theorem 8.9 on `n ≥ 3` wires, given completeness on fewer wires. -/
theorem complete_ge_three {n : ℕ} (hn : 3 ≤ n) (ih : ∀ k < n, CompleteAt k) : CompleteAt n :=
  complete_of (esem n hn) (theorem_4_10 n hn) (lemma_8_7 n hn) (lemma_8_8 n hn) ih

end QCert.RealCliffordCH.Sec8
