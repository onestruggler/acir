/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The coset sections

The normal boxes of Figure 6, read as elements of the stabiliser chain:

* `Acirc p u`, for `u ≠ 0`, a one-qudit circuit sending `Z` to `X^{u.1} Z^{u.2}`
  (the inverse of the paper's box `A`): `M_{1/b}` if `u = (0, b)`, and
  `S^{b/a} H³ M_{1/a}` if `u = (a, b)`, `a ≠ 0`;
* `bcirc p u`, a two-qudit circuit sending `Z` on wire 0 to `u ⊗ Z` (wire 0,
  wire 1): the swap if `u = 0`, and `A_u` on wire 0, `H²` on wire 1 after
  `CX` otherwise (the inverse of the paper's box `B`);
* `s₁circ p m u`, for `u ≠ 0` on `m + 1` wires, a circuit sending `Z` on
  wire 0 to `u`: a box `A` on wire 0 if `u` is supported there, otherwise
  the circuit for the rest of `u` moved up one wire after `bcirc (u 0)`
  (the inverse of the paper's Z-normal circuit).

Circuits are in operator order: `bcirc` applies `CX` first.
-/
import QCert.QuditClifford.Quot

namespace QCert.QuditClifford

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### One wire -/

/-- The action of a one-wire circuit on the exponents of one Pauli. -/
def σ1 (c : Circ 1) (u : ZMod p × ZMod p) : ZMod p × ZMod p := σC p 1 c (fun _ => u) 0

theorem σC1_eq (c : Circ 1) (v : V p 1) : σC p 1 c v = fun _ => σ1 p c (v 0) := by
  have hv : v = fun _ => v 0 := V1_ext p rfl
  apply V1_ext p
  show σC p 1 c v 0 = σC p 1 c (fun _ => v 0) 0
  rw [← hv]

theorem σ1_mul (c d : Circ 1) (u : ZMod p × ZMod p) : σ1 p (c * d) u = σ1 p c (σ1 p d u) := by
  simp only [σ1, map_mul, Function.End.mul_def, Function.comp_apply]
  rw [σC1_eq p d]

theorem σ1_one (u : ZMod p × ZMod p) : σ1 p 1 u = u := rfl

theorem σ1_H (u : ZMod p × ZMod p) : σ1 p H u = (-u.2, u.1) := by
  simp [σ1, σC_H]

theorem σ1_S_pow (k : ℕ) (u : ZMod p × ZMod p) : σ1 p (S ^ k) u = (u.1, u.2 + k * u.1) := by
  simp [σ1, σC_S_pow]

theorem σ1_H_pow (k : ℕ) (u : ZMod p × ZMod p) :
    σ1 p (H ^ k) u = (σ1 p H)^[k] u := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih => rw [pow_succ, σ1_mul, ih, Function.iterate_succ_apply]

theorem σ1_H2 (u : ZMod p × ZMod p) : σ1 p (H ^ 2) u = (-u.1, -u.2) := by
  rw [σ1_H_pow]; simp [σ1_H]

theorem σ1_H3 (u : ZMod p × ZMod p) : σ1 p (H ^ 3) u = (u.2, -u.1) := by
  rw [σ1_H_pow]; simp [σ1_H]

theorem σ1_trivial {c : Circ 1} (h : σC p 1 c = 1) (k : ℕ) (u : ZMod p × ZMod p) :
    σ1 p (c ^ k) u = u := by
  simp [σ1, map_pow, h]; rfl

theorem σ1_scalar_pow (k : ℕ) (u : ZMod p × ZMod p) : σ1 p (negω ^ k) u = u :=
  σ1_trivial p (σC_negω p) k u

theorem val_cast (a : ZMod p) : ((a.val : ℕ) : ZMod p) = a := ZMod.natCast_zmod_val a

/-- The multiplier `M_a` acts as `X ↦ X^a`, `Z ↦ Z^{1/a}`. -/
theorem σ1_M {a : ZMod p} (ha : a ≠ 0) (u : ZMod p × ZMod p) : σ1 p (M p a) u = (a * u.1, u.2 / a) := by
  simp only [M, seq_def, σ1_mul, σ1_H, σ1_S_pow, val_cast, neg1, ω, ← pow_mul, σ1_scalar_pow,
    σ1_trivial p (σC_X p), σ1_trivial p (σC_Z p)]
  ext <;> field_simp <;> ring

/-- A one-qudit circuit sending `Z` to `X^{u.1} Z^{u.2}`. -/
def Acirc (u : ZMod p × ZMod p) : Circ 1 :=
  if u.1 = 0 then M p u.2⁻¹ else S ^ (u.2 / u.1).val * H ^ 3 * M p u.1⁻¹

theorem σ1_Acirc {u : ZMod p × ZMod p} (hu : u ≠ 0) : σ1 p (Acirc p u) (0, 1) = u := by
  unfold Acirc
  split_ifs with h1
  · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
    rw [σ1_M p (inv_ne_zero h2)]
    ext <;> simp [h1, h2]
  · rw [σ1_mul, σ1_mul, σ1_M p (inv_ne_zero h1), σ1_H3, σ1_S_pow, val_cast]
    ext <;> field_simp <;> simp

/-! ### Two wires -/

theorem V2_ext {u v : V p 2} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  funext i; fin_cases i
  · exact h0
  · exact h1

theorem σC2_bot (c : Circ 1) (v : V p 2) :
    σC p 2 (Circuit.pad 1 c) v = ![σ1 p c (v 0), v 1] := by
  have := σC_pad p 1 c v
  rw [σC1_eq] at this
  rw [this]
  apply V2_ext p <;> simp [withLow, low]

theorem σC2_top (c : Circ 1) (v : V p 2) :
    σC p 2 (Circuit.shift c) v = ![v 0, σ1 p c (v 1)] := by
  rw [σC_shift, σC1_eq]
  apply V2_ext p
  · rfl
  · rfl

theorem σC2_CZ (v : V p 2) :
    σC p 2 CZ v = ![((v 0).1, (v 0).2 + (v 1).1), ((v 1).1, (v 1).2 + (v 0).1)] := by
  simp only [CZ, Circuit.g2, σC_of, σGen]
  apply V2_ext p <;> simp [Function.update_apply]

/-- The paper's `CX` (T6), control on wire 1, target on wire 0:
`X₁ ↦ X₁ X₀`, `Z₀ ↦ Z₀ Z₁⁻¹`. -/
theorem σC2_CX (v : V p 2) :
    σC p 2 CX v = ![((v 0).1 + (v 1).1, (v 0).2), ((v 1).1, (v 1).2 - (v 0).2)] := by
  simp only [CX, seq_def, bot, map_mul, Function.End.mul_def, Function.comp_apply, σC2_bot,
    σC2_CZ, σ1_H, σ1_H3]
  apply V2_ext p <;> simp <;> ring_nf

/-- The swap (T4) exchanges the two wires. -/
theorem σC2_SWAP (v : V p 2) : σC p 2 (SWAP p) v = ![v 1, v 0] := by
  have hn : ∀ k (v : V p 2), σC p 2 (neg1 p ^ k) v = v := by
    intro k v; simp [neg1, ← pow_mul, map_pow, σC_negω]; rfl
  simp only [SWAP, seq_def, par, bot, top, map_mul, Function.End.mul_def, Function.comp_apply,
    hn, σC2_bot, σC2_top, σC2_CZ, σ1_H]
  apply V2_ext p <;> simp <;> ring_nf

/-- A two-qudit circuit sending `Z` on wire 0 to `u ⊗ Z`. -/
def bcirc (u : ZMod p × ZMod p) : Circ 2 :=
  if u = 0 then SWAP p else Circuit.pad 1 (Acirc p u) * Circuit.shift (H ^ 2) * CX

theorem σC2_bcirc (u : ZMod p × ZMod p) :
    σC p 2 (bcirc p u) ![(0, 1), (0, 0)] = ![u, (0, 1)] := by
  unfold bcirc
  split_ifs with h
  · rw [σC2_SWAP]; subst h; rfl
  · simp only [map_mul, Function.End.mul_def, Function.comp_apply, σC2_CX, σC2_top, σC2_bot, σ1_H2]
    apply V2_ext p
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons]
      convert σ1_Acirc p h using 2 <;> simp
    · simp

/-! ### The section for `Z` on wire 0 -/

/-- A circuit on `m + 1` wires sending `Z` on wire 0 to `u`. -/
def s₁circ : (m : ℕ) → V p (m + 1) → Circ (m + 1)
  | 0, u => Acirc p (u 0)
  | m + 1, u => if Fin.tail u = 0 then Circuit.pad (m + 1) (Acirc p (u 0))
      else Circuit.shift (s₁circ m (Fin.tail u)) * Circuit.pad m (bcirc p (u 0))

/-- `Z` on wire 0. -/
def eZ (m : ℕ) : V p (m + 1) := Fin.cons (0, 1) 0

/-- `X` on wire 0. -/
def eX (m : ℕ) : V p (m + 1) := Fin.cons (1, 0) 0

theorem σC_s₁circ : (m : ℕ) → {u : V p (m + 1)} → u ≠ 0 → σC p (m + 1) (s₁circ p m u) (eZ p m) = u
  | 0, u, hu => by
    have h0 : u 0 ≠ 0 := fun h => hu (V1_ext p h)
    rw [s₁circ, σC1_eq]
    apply V1_ext p
    exact σ1_Acirc p h0
  | m + 1, u, hu => by
    rw [s₁circ]
    split_ifs with ht
    · have h0 : u 0 ≠ 0 := fun h => hu (by rw [← Fin.cons_self_tail u, h, ht]; exact funext fun i => Fin.cases rfl (fun _ => rfl) i)
      rw [σC_pad, σC1_eq]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [withLow, low, eZ]
        exact σ1_Acirc p h0
      · simp only [withLow, low, eZ, Fin.val_succ, Fin.cons_succ]
        rw [dif_neg (by omega)]
        have := congrFun ht i
        simpa [Fin.tail] using this.symm
    · rw [map_mul, Function.End.mul_def, Function.comp_apply]
      erw [σC_pad p m (bcirc p (u 0))]
      have hlow : low p (n := m) (k := 2) (eZ p (m + 1)) = ![(0, 1), (0, 0)] := by
        apply V2_ext p <;> rfl
      rw [hlow, σC2_bcirc]
      have hw : withLow p ![u 0, (0, 1)] (eZ p (m + 1)) = Fin.cons (u 0) (eZ p m) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun i => ?_) i
          · rfl
          · simp [withLow, eZ]
      rw [hw, σC_shift, Fin.cons_zero, Fin.tail_cons, σC_s₁circ m ht, Fin.cons_self_tail]

end QCert.QuditClifford
