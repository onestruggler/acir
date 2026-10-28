/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Case splits and changes of parameters on patterns

* `pat_conv'`: a window of pattern `P` has pattern `Q` at new parameters,
  when `P` is `Q` with forms substituted for its parameters, up to trailing
  zero coefficients (`Pnorm`), checked by evaluation.
* `pat_dich`: split on the parity of a form `lf` in the parameters with an
  odd coefficient at `p`: in each case `p` is replaced by `2 x + b' − R`
  (`splitL`), `R` the other coefficients of `lf` mod 2, and the window has
  the substituted pattern.
-/
import QCert.HadamardPi.SymState

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### Normal forms of patterns -/

/-- Drop the trailing zero coefficients. -/
def lnorm : List ℤ → List ℤ
  | [] => []
  | a :: as =>
    match lnorm as with
    | [] => if a = 0 then [] else [a]
    | l => a :: l

theorem evv_lnorm : ∀ (l : List ℤ) (t : ℕ → ℤ), evv (lnorm l) t = evv l t
  | [], t => rfl
  | a :: as, t => by
    have ih := evv_lnorm as (fun i => t (i + 1))
    simp only [lnorm]
    cases h : lnorm as with
    | nil =>
      rw [h] at ih
      simp only [evv_nil] at ih
      split_ifs with ha
      · subst ha; simp [evv_cons, ← ih]
      · simp [evv_cons, ← ih]
    | cons b bs =>
      rw [h] at ih
      simp only [evv_cons] at ih ⊢
      rw [ih]

/-- A pattern with its forms normalised. -/
def Pnorm (P : List ZL) : List ZL := P.map fun x => (lnorm x.1, lnorm x.2)

theorem zev_Pnorm (P : List ZL) (t : ℕ → ℤ) (j : ℕ) :
    zev ((Pnorm P).getD j dZ) t = zev (P.getD j dZ) t := by
  simp only [Pnorm, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[j]? with
  | none => rfl
  | some x => simp [zev, evv_lnorm]

/-- Change of parameters, up to normalisation. -/
theorem pat_conv' {w : ℕ} {v : Fin n → ℝ} {f : Fin w → Fin n} {P Q : List ZL}
    {φ : List (List ℤ)} (e : Pnorm (Psubst Q φ) = Pnorm P) {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num v (f j) = zev (P.getD j dZ) t) :
    ∀ j : Fin w, num v (f j) = zev (Q.getD j dZ) fun i => evv (φ.getD i []) (c1 t) := by
  intro j
  rw [hP, ← zev_Pnorm, ← e, zev_Pnorm, zev_Psubst]

/-- The same pattern up to normalisation. -/
theorem pat_eqv {w : ℕ} {v : Fin n → ℝ} {f : Fin w → Fin n} {P Q : List ZL}
    (e : Pnorm Q = Pnorm P) {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num v (f j) = zev (P.getD j dZ) t) :
    ∀ j : Fin w, num v (f j) = zev (Q.getD j dZ) t := by
  intro j
  rw [hP, ← zev_Pnorm, ← e, zev_Pnorm]

/-! ### Coefficients -/

/-- The coefficient at `i` (`0` beyond the list). -/
def lget : List ℤ → ℕ → ℤ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, i + 1 => lget as i

/-- Replace the coefficient at `i`. -/
def lset : List ℤ → ℕ → ℤ → List ℤ
  | [], _, _ => []
  | _ :: as, 0, b => b :: as
  | a :: as, i + 1, b => a :: lset as i b

/-- Every coefficient mod 2. -/
def lmod2 : List ℤ → List ℤ
  | [] => []
  | a :: as => a % 2 :: lmod2 as

theorem evv_lset : ∀ (l : List ℤ) (p : ℕ) (b : ℤ) (t : ℕ → ℤ), p < l.length →
    evv (lset l p b) t = evv l t + (b - lget l p) * t p
  | [], _, _, _, h => by simp at h
  | a :: as, 0, b, t, _ => by simp only [lset, lget, evv_cons]; ring
  | a :: as, p + 1, b, t, h => by
    simp only [lset, lget, evv_cons]
    rw [evv_lset as p b _ (by simp at h; omega)]; ring

theorem evv_update : ∀ (l : List ℤ) (p : ℕ) (a : ℤ) (t : ℕ → ℤ),
    evv l (Function.update t p a) = evv l t + lget l p * (a - t p)
  | [], _, _, _ => by simp [lget]
  | c :: cs, 0, a, t => by
    simp only [evv_cons, lget, Function.update_self]
    have : (fun i => Function.update t 0 a (i + 1)) = fun i => t (i + 1) := by
      funext i; rw [Function.update_of_ne (by omega)]
    rw [this]; ring
  | c :: cs, p + 1, a, t => by
    simp only [evv_cons, lget, Function.update_of_ne (show (0 : ℕ) ≠ p + 1 by omega)]
    have : (fun i => Function.update t (p + 1) a (i + 1)) =
        Function.update (fun i => t (i + 1)) p a := by
      funext i
      by_cases h : i = p
      · subst h; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne h]
    rw [this, evv_update cs p a]; ring

theorem evv_lmod2 : ∀ (l : List ℤ) (t : ℕ → ℤ), ∃ m, evv l t = evv (lmod2 l) t + 2 * m
  | [], t => ⟨0, by simp [lmod2]⟩
  | a :: as, t => by
    obtain ⟨m, hm⟩ := evv_lmod2 as (fun i => t (i + 1))
    refine ⟨a / 2 * t 0 + m, ?_⟩
    simp only [lmod2, evv_cons, hm]
    have : a = a % 2 + 2 * (a / 2) := (Int.emod_add_ediv a 2).symm
    linear_combination t 0 * this

theorem lget_lmod2 : ∀ (l : List ℤ) (p : ℕ), lget (lmod2 l) p = lget l p % 2
  | [], _ => rfl
  | a :: as, 0 => rfl
  | a :: as, p + 1 => lget_lmod2 as p

theorem lget_lsmul : ∀ (c : ℤ) (l : List ℤ) (p : ℕ), lget (lsmul c l) p = c * lget l p
  | _, [], _ => by simp [lget, lsmul]
  | _, a :: as, 0 => rfl
  | c, a :: as, p + 1 => lget_lsmul c as p

theorem lget_lset : ∀ (l : List ℤ) (p : ℕ) (b : ℤ), p < l.length → lget (lset l p b) p = b
  | [], _, _, h => by simp at h
  | a :: as, 0, b, _ => rfl
  | a :: as, p + 1, b, h => lget_lset as p b (by simp at h; omega)

theorem length_lmod2 : ∀ l : List ℤ, (lmod2 l).length = l.length
  | [] => rfl
  | a :: as => by simp [lmod2, length_lmod2 as]

theorem length_lsmul (c : ℤ) : ∀ l : List ℤ, (lsmul c l).length = l.length
  | [] => rfl
  | a :: as => by simp [lsmul, length_lsmul c as]

theorem length_lset : ∀ (l : List ℤ) (p : ℕ) (b : ℤ), (lset l p b).length = l.length
  | [], _, _ => rfl
  | a :: as, 0, b => rfl
  | a :: as, p + 1, b => by simp [lset, length_lset as p b]

/-! ### Splitting on a parity -/

/-- The other coefficients of `lf`, mod 2, with `p` cleared. -/
def splitR (lf : List ℤ) (p : ℕ) : List ℤ := lset (lmod2 lf.tail) p 0

/-- The form `b' + 2 x − R` replacing the parameter `p`, for the case
`lf ≡ b (mod 2)`. -/
def splitL (lf : List ℤ) (p : ℕ) (b : ℤ) : List ℤ :=
  ((b - lf.headD 0) % 2) :: lset (lsmul (-1) (splitR lf p)) p 2

/-- The new value of the parameter `p`. -/
def splitX (lf : List ℤ) (p : ℕ) (b : ℤ) (t : ℕ → ℤ) : ℤ :=
  (t p - (b - lf.headD 0) % 2 + evv (splitR lf p) t) / 2

theorem split_eq {lf : List ℤ} {p : ℕ} (hodd : lget lf.tail p % 2 = 1) (hp : p < lf.tail.length)
    {b : ℤ} {t : ℕ → ℤ} (h : evv lf (c1 t) % 2 = b) :
    evv (splitL lf p b) (c1 (Function.update t p (splitX lf p b t))) = t p := by
  obtain ⟨c0, cs, rfl⟩ : ∃ c0 cs, lf = c0 :: cs := by
    cases lf with
    | nil => simp at hp
    | cons c0 cs => exact ⟨c0, cs, rfl⟩
  simp only [List.tail_cons] at hodd hp
  simp only [splitL, splitX, splitR, List.headD_cons, List.tail_cons, evv_c1] at h ⊢
  set R := lset (lmod2 cs) p 0 with hR
  have hRl : p < (lmod2 cs).length := by rw [length_lmod2]; exact hp
  -- the value of `lf`
  obtain ⟨m, hm⟩ := evv_lmod2 cs t
  have e1 : evv R t = evv (lmod2 cs) t + (0 - lget (lmod2 cs) p) * t p := evv_lset _ _ _ _ hRl
  rw [lget_lmod2, hodd] at e1
  -- the value of the substituted form
  have hR0 : lget R p = 0 := lget_lset _ _ _ hRl
  have e2 : evv (lset (lsmul (-1) R) p 2) (Function.update t p ((t p - (b - c0) % 2 + evv R t) / 2))
      = evv (lsmul (-1) R) (Function.update t p ((t p - (b - c0) % 2 + evv R t) / 2)) +
        (2 - lget (lsmul (-1) R) p) * Function.update t p ((t p - (b - c0) % 2 + evv R t) / 2) p :=
    evv_lset _ _ _ _ (by rw [length_lsmul, hR, length_lset]; exact hRl)
  rw [e2, lget_lsmul, hR0, evv_lsmul, evv_update, hR0, Function.update_self]
  omega

/-- The two cases of a split. -/
theorem pat_dich {w : ℕ} {v : Fin n → ℝ} {f : Fin w → Fin n} {P : List ZL} {nv : ℕ}
    (hw : Pwidth P nv = true) (lf : List ℤ) (p : ℕ) (hodd : lget lf.tail p % 2 = 1)
    (hp : p < lf.tail.length) {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num v (f j) = zev (P.getD j dZ) t) :
    (evv lf (c1 t) % 2 = 0 ∧ ∀ j : Fin w, num v (f j) =
        zev ((Psubst P (splitφ nv p (splitL lf p 0))).getD j dZ)
          (Function.update t p (splitX lf p 0 t))) ∨
      (evv lf (c1 t) % 2 = 1 ∧ ∀ j : Fin w, num v (f j) =
        zev ((Psubst P (splitφ nv p (splitL lf p 1))).getD j dZ)
          (Function.update t p (splitX lf p 1 t))) := by
  rcases Int.emod_two_eq_zero_or_one (evv lf (c1 t)) with h | h
  · exact Or.inl ⟨h, pat_split hw p _ _ (split_eq hodd hp h) hP⟩
  · exact Or.inr ⟨h, pat_split hw p _ _ (split_eq hodd hp h) hP⟩

/-- One case of a split, when the parity is known. -/
theorem pat_case {w : ℕ} {v : Fin n → ℝ} {f : Fin w → Fin n} {P : List ZL} {nv : ℕ}
    (hw : Pwidth P nv = true) (lf : List ℤ) (p : ℕ) (hodd : lget lf.tail p % 2 = 1)
    (hp : p < lf.tail.length) {t : ℕ → ℤ} {b : ℤ} (h : evv lf (c1 t) % 2 = b)
    (hP : ∀ j : Fin w, num v (f j) = zev (P.getD j dZ) t) :
    ∀ j : Fin w, num v (f j) =
      zev ((Psubst P (splitφ nv p (splitL lf p b))).getD j dZ)
        (Function.update t p (splitX lf p b t)) :=
  pat_split hw p _ _ (split_eq hodd hp h) hP

end QCert.HadamardPi
