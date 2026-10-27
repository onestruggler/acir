/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: the relations of Case 3.2.2.2

For four indices `j < ℓ < j' < ℓ'`:

* (27): `K†_[ℓ,ℓ'] K†_[j,j'] K†_[j',ℓ'] K†_[j,ℓ]` commutes with `X_[ℓ,j']`,
  from (19), (13), (14) (conjugation by `X_[ℓ,j']` exchanges the two
  pairings `{jℓ, j'ℓ'}` and `{jj', ℓℓ'}`, and (19) says they commute);
* the special square `K†_[j,ℓ] X_[ℓ,j'] ∼ G'' K†_[j,ℓ]` of the special case;
* the faces of the general case: `K†_[j,ℓ] i_[j]^A i_[ℓ]^{A+2m+q} ∼
  i_[j]^A i_[ℓ]^A X_[j,ℓ]^m K†_[j,ℓ] i_[ℓ]^q` (from (15), (17)) and the
  exchange of `i_[ℓ]`, `i_[j']` by `X_[ℓ,j']`.
-/
import QCert.BianSelingerUn.Derived2

namespace QCert.BianSelingerUn

variable {n : ℕ}

/-- In a monoid, inverses of commuting elements commute. -/
theorem inv_comm_of_comm {M : Type*} [Monoid M] {P Q P' Q' : M} (hPQ : Q * P = P * Q)
    (hP : P * P' = 1) (hP' : P' * P = 1) (hQ : Q * Q' = 1) (hQ' : Q' * Q = 1) :
    P' * Q' = Q' * P' := by
  calc P' * Q' = P' * Q' * (P * Q * (Q' * P')) := by
        rw [show P * Q * (Q' * P') = P * (Q * Q') * P' by simp only [mul_assoc], hQ, mul_one, hP,
          mul_one]
    _ = P' * Q' * (Q * P) * (Q' * P') := by rw [hPQ]; simp only [mul_assoc]
    _ = P' * (Q' * Q) * P * Q' * P' := by simp only [mul_assoc]
    _ = Q' * P' := by rw [hQ', mul_one, hP', one_mul]

section TwoIndices

variable (j l : Fin n) (h : j < l)

/-- `K† b² = x K†`, from (15) and (17). -/
theorem fKdbb_t (t : Pres n) :
    gK j l h ^ 7 * (gi l * (gi l * t)) = gX j l h * (gK j l h ^ 7 * t) := by
  conv_lhs => rw [tKd, ← tXK, t10, ← tXb, t4 j l h.ne, ← tKd]

theorem sc_Kd_bb : SemiconjBy (gK j l h ^ 7) (gi l * gi l) (gX j l h) := by
  unfold SemiconjBy; simpa [mul_assoc] using fKdbb_t j l h 1

theorem comm_Kd_ab : Commute (gK j l h ^ 7) (gi j * gi l) := by
  have e := f17 j l h 1
  simp only [mul_one] at e
  unfold Commute SemiconjBy
  rw [e4 j l h.ne, e, ← mul_assoc, e4 j l h.ne]

/-- The left face of Case 3.2.2.2: `K† a^A b^{A+2m+q} ∼ a^A b^A x^m K† b^q`. -/
theorem face (A m q : ℕ) :
    gK j l h ^ 7 * (gi j ^ A * gi l ^ (A + 2 * m + q)) =
      gi j ^ A * gi l ^ A * gX j l h ^ m * (gK j l h ^ 7 * gi l ^ q) := by
  have hab : Commute (gi j) (gi l) := e4 j l h.ne
  have e1' : gi j ^ A * gi l ^ (A + 2 * m + q) =
      (gi j * gi l) ^ A * ((gi l * gi l) ^ m * gi l ^ q) := by
    rw [hab.mul_pow, pow_add, pow_add, pow_mul, pow_two]; simp only [mul_assoc]
  conv_lhs => rw [e1', ← mul_assoc, ((comm_Kd_ab j l h).pow_right A).eq, mul_assoc,
    ← mul_assoc (gK j l h ^ 7), ((sc_Kd_bb j l h).pow_right m).eq, hab.mul_pow]
  simp only [mul_assoc]

end TwoIndices

section FourIndices

variable (j l j' l' : Fin n) (h1 : j < l) (h2 : l < j') (h3 : j' < l')

theorem gK_inv7 (a b : Fin n) (h : a < b) : gK a b h * gK a b h ^ 7 = 1 := gK_mul_pow_seven a b h
theorem gK_inv7' (a b : Fin n) (h : a < b) : gK a b h ^ 7 * gK a b h = 1 := gK_pow_seven_mul a b h

/-- Figure 2, (27). -/
theorem f27 :
    gK l l' (h2.trans h3) ^ 7 * gK j j' (h1.trans h2) ^ 7 * gK j' l' h3 ^ 7 * gK j l h1 ^ 7 *
        gX l j' h2 =
      gX l j' h2 * (gK l l' (h2.trans h3) ^ 7 * gK j j' (h1.trans h2) ^ 7 * gK j' l' h3 ^ 7 *
        gK j l h1 ^ 7) := by
  set Kll := gK l l' (h2.trans h3)
  set Kjj := gK j j' (h1.trans h2)
  set Kj'l := gK j' l' h3
  set Kjl := gK j l h1
  set X := gX l j' h2
  -- (19): the two pairings commute
  have e19' := e19 j l j' l' h1 h3 (h1.trans h2) (h2.trans h3) h2.ne
  have hPQ : (Kjl * Kj'l) * (Kjj * Kll) = (Kjj * Kll) * (Kjl * Kj'l) := by
    simp only [mul_assoc] at e19' ⊢; exact e19'
  have hP : (Kjj * Kll) * (Kll ^ 7 * Kjj ^ 7) = 1 := by
    rw [mul_assoc, ← mul_assoc Kll, gK_inv7, one_mul, gK_inv7]
  have hP' : (Kll ^ 7 * Kjj ^ 7) * (Kjj * Kll) = 1 := by
    rw [mul_assoc, ← mul_assoc (Kjj ^ 7), gK_inv7', one_mul, gK_inv7']
  have hQ : (Kjl * Kj'l) * (Kj'l ^ 7 * Kjl ^ 7) = 1 := by
    rw [mul_assoc, ← mul_assoc Kj'l, gK_inv7, one_mul, gK_inv7]
  have hQ' : (Kj'l ^ 7 * Kjl ^ 7) * (Kjl * Kj'l) = 1 := by
    rw [mul_assoc, ← mul_assoc (Kjl ^ 7), gK_inv7', one_mul, gK_inv7']
  have hc := inv_comm_of_comm hPQ hP hP' hQ hQ'
  -- conjugation by `X_[ℓ,j']` exchanges the pairings
  have hs : SemiconjBy X (Kll ^ 7 * Kjj ^ 7 * Kj'l ^ 7 * Kjl ^ 7)
      (Kj'l ^ 7 * Kjl ^ 7 * Kll ^ 7 * Kjj ^ 7) :=
    ((((sc_XK_high l j' l' h2 h3).pow_right 7).mul_right
      ((sc_XK_low' j l j' h1 h2).pow_right 7)).mul_right
      ((sc_XK_high' l j' l' h2 h3).pow_right 7)).mul_right ((sc_XK_low j l j' h1 h2).pow_right 7)
  have hA : Kj'l ^ 7 * Kjl ^ 7 * Kll ^ 7 * Kjj ^ 7 = Kll ^ 7 * Kjj ^ 7 * Kj'l ^ 7 * Kjl ^ 7 := by
    calc Kj'l ^ 7 * Kjl ^ 7 * Kll ^ 7 * Kjj ^ 7 = (Kj'l ^ 7 * Kjl ^ 7) * (Kll ^ 7 * Kjj ^ 7) := by
          simp only [mul_assoc]
      _ = (Kll ^ 7 * Kjj ^ 7) * (Kj'l ^ 7 * Kjl ^ 7) := hc.symm
      _ = _ := by simp only [mul_assoc]
  rw [hs.eq, hA]

/-- The special square of Case 3.2.2.2:
`K†_[j,ℓ] X_[ℓ,j'] ∼ K_[j',ℓ'] K_[j,j'] K_[ℓ,ℓ'] X_[ℓ,j'] K†_[ℓ,ℓ'] K†_[j,j'] K†_[j',ℓ'] K†_[j,ℓ]`. -/
theorem special_sq :
    gK j l h1 ^ 7 * gX l j' h2 =
      gK j' l' h3 * gK j j' (h1.trans h2) * gK l l' (h2.trans h3) * gX l j' h2 *
        gK l l' (h2.trans h3) ^ 7 * gK j j' (h1.trans h2) ^ 7 * gK j' l' h3 ^ 7 *
        gK j l h1 ^ 7 := by
  have e := f27 j l j' l' h1 h2 h3
  set Kll := gK l l' (h2.trans h3)
  set Kjj := gK j j' (h1.trans h2)
  set Kj'l := gK j' l' h3
  set Kjl := gK j l h1
  set X := gX l j' h2
  have hB : Kj'l * Kjj * Kll * (Kll ^ 7 * Kjj ^ 7 * Kj'l ^ 7) = 1 := by
    simp only [mul_assoc]
    rw [← mul_assoc Kll, gK_inv7, one_mul, ← mul_assoc Kjj, gK_inv7, one_mul, gK_inv7]
  calc Kjl ^ 7 * X = Kj'l * Kjj * Kll * (Kll ^ 7 * Kjj ^ 7 * Kj'l ^ 7) * (Kjl ^ 7 * X) := by
        rw [hB, one_mul]
    _ = Kj'l * Kjj * Kll * ((Kll ^ 7 * Kjj ^ 7 * Kj'l ^ 7 * Kjl ^ 7) * X) := by
        simp only [mul_assoc]
    _ = Kj'l * Kjj * Kll * (X * (Kll ^ 7 * Kjj ^ 7 * Kj'l ^ 7 * Kjl ^ 7)) := by rw [e]
    _ = _ := by simp only [mul_assoc]

end FourIndices

end QCert.BianSelingerUn
