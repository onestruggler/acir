/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Local relations of the linear fragment

The relations among `CX`, the crossing and the multipliers on two and
three wires that the normal form for linear circuits (`LinearNF`) uses, as
equations in the group `Q d lv n` on the bottom wires of any circuit.  All
of them are derived from the rules of Figure 1 of Blake
(arXiv:2603.06466) and the laws of the symmetry.

On two wires (`a` the `CX` from wire `1` to wire `0`, `s` the crossing,
`m₀ x`, `m₁ x` the multipliers on the wires `0`, `1`):

* `m₀ x a m₀ x⁻¹ = a^x` ((5)) and `m₁ x a m₁ x⁻¹ = a^{1/x}` ((4));
* `s a s = a s a⁻¹ m₁(-1)` (`swap_conj_cx`, from (7)); this is the Bruhat
  relation of `GL₂(𝔽_d)`, and gives `bruhat`: `s m₁ γ a^α s` is
  `m₁ α a^γ s` followed by `a^{-1/γ} m₁(-γ/α)` (`α, γ ≠ 0`).

On three wires (`b = ↑a` the `CX` from wire `2` to wire `1`, `s₁ = ↑s`,
`L = s₁ a s₁` the `CX` from wire `2` to wire `0`, `ā = s a s` the `CX` from
wire `0` to wire `1`):

* the Yang–Baxter equation `s s₁ s = s₁ s s₁` and the naturality
  `s s₁ a = b s s₁` (the symmetry rules), whence `s b s = L`;
* rule (8), `b a L = a b`, read as the commutator `L = a⁻¹ b⁻¹ a b`;
* Lemmas 23 and 24 of the paper: `a` and `b` commute with `L`.  Here they
  come from (8) and its conjugates by `M_{-1}` on the wire `0` (which
  inverts `a` and `L` and fixes `b`) and on the wire `2` (which inverts `b`
  and `L` and fixes `a`), not from the paper's chains; the argument is
  uniform in `d`, including `d = 2`;
* `ā` commutes with `b` (two `CX` with the same target), and
  `s₁ ā s₁ = s ↑ā s` (the `CX` from wire `0` to wire `2`, in two ways);
* the Steinberg relation `b a^k = a^k b L^{-k}` and the exchange
  `s b^γ s₁ a^α s = b^α s₁ a^γ s s₁` (`stair_swap`).
-/
import QCert.PhaseAffine.Translation

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

/-! ### The shift on the quotients -/

/-- The shift of circuits as a homomorphism of the quotients. -/
def shiftQ {n : ℕ} : Q d lv n →* Q d lv (n + 1) :=
  (conGen (theory d lv n)).lift (mk.comp shift) (Con.conGen_le fun _ _ h =>
    (Con.ker_rel _).2 (mk_shift (mk_lift h)))

@[simp] theorem shiftQ_mk {n : ℕ} (w : C d lv n) : shiftQ (mk w) = mk (shift w) := rfl

theorem comm1Q {n : ℕ} (h : Gate d lv 1) (q : Q d lv n) : Commute (mk (g1 h)) (shiftQ q) := by
  obtain ⟨u, rfl⟩ := mk_surjective q
  exact mk_comm1' h u

theorem comm2Q {n : ℕ} (h : Gate d lv 2) (q : Q d lv n) :
    Commute (mk (g2 h)) (shiftQ (shiftQ q)) := by
  obtain ⟨u, rfl⟩ := mk_surjective q
  exact mk_comm2' h u

/-! ### Labelled powers and conjugation -/

theorem conj_label {G : Type*} [Group G] {g a : G} {t : ZMod d} (ha : a ^ d = 1)
    (h : g * a * g⁻¹ = a ^ t.val) (k : ZMod d) : g * a ^ k.val = a ^ (t * k).val * g := by
  rw [pow_val_mul ha, ← h, conj_pow, inv_mul_cancel_right]

/-! ### The gates as elements of the quotients -/

/-- `CX` on the bottom two wires of `m + 2` (control wire `1`, target wire
`0`). -/
abbrev qa (m : ℕ) : Q d lv (m + 2) := mk (g2 Gate.CX)
/-- The crossing of the bottom two wires of `m + 2`. -/
abbrev qs (m : ℕ) : Q d lv (m + 2) := mk (g2 Gate.SWAP)
/-- The multiplier `M_x` on the bottom wire of `m + 1`. -/
abbrev qm (m : ℕ) (x : (ZMod d)ˣ) : Q d lv (m + 1) := mk (g1 (Gate.M x))

section Two

variable [Fact d.Prime] (m : ℕ)

theorem qa_pow : qa (d := d) (lv := lv) m ^ d = 1 := relCXd m

omit [Fact d.Prime] in
theorem qs_mul_self : qs (d := d) (lv := lv) m * qs m = 1 := relSW2 m

omit [Fact d.Prime] in
theorem qs_mul_self' (x : Q d lv (m + 2)) : qs m * (qs m * x) = x := by
  rw [← mul_assoc, qs_mul_self, one_mul]

theorem qs_inv : (qs (d := d) (lv := lv) m)⁻¹ = qs m := relSW_inv m

theorem qa_neg_one : qa (d := d) (lv := lv) m ^ (-1 : ZMod d).val = (qa m)⁻¹ :=
  pow_val_neg_one (qa_pow m) one_lt_d

theorem qm_mul (x y : (ZMod d)ˣ) : qm (d := d) (lv := lv) m y * qm m x = qm m (x * y) :=
  rel2 m x y

omit [Fact d.Prime] in
theorem qm_one : qm (d := d) (lv := lv) m 1 = 1 := rel1 m

theorem qm_inv (x : (ZMod d)ˣ) : (qm (d := d) (lv := lv) m x)⁻¹ = qm m x⁻¹ :=
  inv_eq_of_mul_eq_one_left (by rw [qm_mul, mul_inv_cancel, qm_one])

theorem qmt_inv (x : (ZMod d)ˣ) :
    (shiftQ (qm (d := d) (lv := lv) m x))⁻¹ = shiftQ (qm m x⁻¹) := by
  rw [← map_inv, qm_inv]

theorem qmt_mul (x y : (ZMod d)ˣ) :
    shiftQ (qm (d := d) (lv := lv) m y) * shiftQ (qm m x) = shiftQ (qm m (x * y)) := by
  rw [← map_mul, qm_mul]

/-- The crossing moves a multiplier from wire `0` to wire `1`. -/
theorem qs_qm (x : (ZMod d)ˣ) :
    qs (d := d) (lv := lv) m * qm (m + 1) x = shiftQ (qm m x) * qs m :=
  relSWnat m (Gate.M x)

theorem qs_qmt (x : (ZMod d)ˣ) :
    qs (d := d) (lv := lv) m * shiftQ (qm m x) = qm (m + 1) x * qs m :=
  relSWnat' m (Gate.M x)

theorem qm_comm (x y : (ZMod d)ˣ) :
    Commute (qm (d := d) (lv := lv) (m + 1) x) (shiftQ (qm m y)) := comm1Q _ _

/-- (5): a multiplier on the target. -/
theorem qm_qa_conj (x : (ZMod d)ˣ) :
    qm (m + 1) x * qa (d := d) (lv := lv) m * (qm (m + 1) x)⁻¹ = qa m ^ (x : ZMod d).val := by
  have e := rel5 m (d := d) (lv := lv) x
  rw [pow_val_neg (qa_pow m)] at e
  have : qm (m + 1) x * qa (d := d) (lv := lv) m = qa m ^ (x : ZMod d).val * qm (m + 1) x := by
    calc qm (m + 1) x * qa m = qa m ^ (x : ZMod d).val *
          ((qa m ^ (x : ZMod d).val)⁻¹ * qm (m + 1) x * qa m) := by group
      _ = _ := by rw [e]
  rw [this, mul_inv_cancel_right]

theorem qm_qa (x : (ZMod d)ˣ) (k : ZMod d) :
    qm (m + 1) x * qa (d := d) (lv := lv) m ^ k.val =
      qa m ^ ((x : ZMod d) * k).val * qm (m + 1) x :=
  conj_label (qa_pow m) (qm_qa_conj m x) k

/-- (4): a multiplier on the control. -/
theorem qmt_qa_conj (x : (ZMod d)ˣ) :
    shiftQ (qm m x) * qa (d := d) (lv := lv) m * (shiftQ (qm m x))⁻¹ =
      qa m ^ ((x⁻¹ : (ZMod d)ˣ) : ZMod d).val := by
  have e : qa (d := d) (lv := lv) m * shiftQ (qm m x⁻¹) =
      shiftQ (qm m x⁻¹) * qa m ^ ((x⁻¹ : (ZMod d)ˣ) : ZMod d).val := rel4 m x⁻¹
  rw [qmt_inv, mul_assoc, e, ← mul_assoc, qmt_mul, inv_mul_cancel, qm_one, map_one, one_mul]

theorem qmt_qa (x : (ZMod d)ˣ) (k : ZMod d) :
    shiftQ (qm m x) * qa (d := d) (lv := lv) m ^ k.val =
      qa m ^ (((x⁻¹ : (ZMod d)ˣ) : ZMod d) * k).val * shiftQ (qm m x) :=
  conj_label (qa_pow m) (qmt_qa_conj m x) k

/-- (7), with `CX^{-1}` written as an inverse. -/
theorem rel7 : qs (d := d) (lv := lv) m = shiftQ (qm m (-1)) *
    (qs m * (qa m)⁻¹ * qs m) * qa m * (qs m * (qa m)⁻¹ * qs m) := by
  have e := mk_rule m (Rules.r7 (d := d) (lv := lv))
  simp only [seq_cons, seq_nil, one_mul, flip, fpow, map_mul, map_pow, Circuit.pad_g2,
    pad_shift, Circuit.pad_g1] at e
  rw [← qa_neg_one]
  simpa [mul_assoc] using e

/-- The Bruhat relation on two wires: `s a s = a s a⁻¹ m₁(-1)`. -/
theorem swap_conj_cx : qs (d := d) (lv := lv) m * qa m * qs m =
    qa m * qs m * (qa m)⁻¹ * shiftQ (qm m (-1)) := by
  set s := qs (d := d) (lv := lv) m
  set a := qa (d := d) (lv := lv) m
  set n := shiftQ (qm (d := d) (lv := lv) m (-1))
  set nb := qm (d := d) (lv := lv) (m + 1) (-1)
  have hs : ∀ x, s * (s * x) = x := qs_mul_self' m
  have hs2 : s * s = 1 := qs_mul_self m
  have hsn : s * n = nb * s := qs_qmt m (-1)
  have hnn : n * n = 1 := relM1_top_sq m
  have hbb : nb * nb = 1 := relM1_sq (m + 1)
  have hna : n * a * n = a⁻¹ := relM1CX m
  have e7 := rel7 (d := d) (lv := lv) m
  -- conjugating (7) by `s`
  have h1 : s = nb * a⁻¹ * (s * a * s) * a⁻¹ := by
    calc s = s * (s * s) := by rw [hs]
      _ = s * (n * (s * a⁻¹ * s) * a * (s * a⁻¹ * s)) * s := by rw [← e7, mul_assoc]
      _ = (s * n) * s * a⁻¹ * (s * a * s) * a⁻¹ * (s * s) := by simp only [mul_assoc]
      _ = nb * a⁻¹ * (s * a * s) * a⁻¹ := by rw [hsn]; simp only [mul_assoc, hs2, mul_one]
  have h2 : s * a * s = a * nb * s * a := by
    calc s * a * s = a * (nb * nb) * (a⁻¹ * (s * a * s) * a⁻¹) * a := by rw [hbb]; group
      _ = a * nb * (nb * a⁻¹ * (s * a * s) * a⁻¹) * a := by group
      _ = a * nb * s * a := by rw [← h1]
  have hns : nb * s = s * n := hsn.symm
  have hna' : n * a = a⁻¹ * n := by
    calc n * a = (n * a * n) * n := by rw [mul_assoc, hnn, mul_one]
      _ = a⁻¹ * n := by rw [hna]
  calc s * a * s = a * (nb * s) * a := by rw [h2]; group
    _ = a * s * (n * a) := by rw [hns]; group
    _ = a * s * a⁻¹ * n := by rw [hna']; group


/-- The Bruhat relation in the form the stairs use (`α, γ ≠ 0`):
`s m₁ γ a^α s = m₁ α a^γ s a^{-1/γ} m₁(-γ/α)`. -/
theorem bruhat (α γ : (ZMod d)ˣ) :
    qs (d := d) (lv := lv) m * (shiftQ (qm m γ) * qa m ^ (α : ZMod d).val * qs m) =
      shiftQ (qm m α) * qa m ^ (γ : ZMod d).val * qs m *
        (qa m ^ (-(γ : ZMod d)⁻¹).val * shiftQ (qm m (-(γ * α⁻¹)))) := by
  have h1 : (1 : ZMod d).val = 1 := val_one_zmod
  have hγs : qs (d := d) (lv := lv) m * shiftQ (qm m γ) = qm (m + 1) γ * qs m := qs_qmt m γ
  have hαs : qs (d := d) (lv := lv) m * qm (m + 1) α = shiftQ (qm m α) * qs m := qs_qm m α
  have hαis : qm (d := d) (lv := lv) (m + 1) α⁻¹ * qs m = qs m * shiftQ (qm m α⁻¹) :=
    (qs_qmt m α⁻¹).symm
  have hγs' : qm (d := d) (lv := lv) (m + 1) γ * qs m = qs m * shiftQ (qm m γ) :=
    (qs_qmt m γ).symm
  have hbt : qm (d := d) (lv := lv) (m + 1) γ * shiftQ (qm m α) =
      shiftQ (qm m α) * qm (m + 1) γ := (qm_comm m γ α).eq
  have hαa : qm (d := d) (lv := lv) (m + 1) α * qa m * qm (m + 1) α⁻¹ =
      qa m ^ (α : ZMod d).val := by
    rw [← qm_inv]; exact qm_qa_conj m α
  have hγa : qm (d := d) (lv := lv) (m + 1) γ * qa m =
      qa m ^ (γ : ZMod d).val * qm (m + 1) γ := by
    have := qm_qa (d := d) (lv := lv) m γ 1
    rwa [h1, pow_one, mul_one] at this
  have hγa' : shiftQ (qm (d := d) (lv := lv) m γ) * qa m ^ (-1 : ZMod d).val =
      qa m ^ (-(γ : ZMod d)⁻¹).val * shiftQ (qm m γ) := by
    rw [qmt_qa m γ (-1), Units.val_inv_eq_inv_val, mul_neg_one]
  have htt : shiftQ (qm (d := d) (lv := lv) m γ) * (shiftQ (qm m (-1)) * shiftQ (qm m α⁻¹)) =
      shiftQ (qm m (-(γ * α⁻¹))) := by
    rw [qmt_mul, qmt_mul]; congr 2; ext; push_cast; ring
  have hB := swap_conj_cx (d := d) (lv := lv) m
  have hinv : (qa (d := d) (lv := lv) m)⁻¹ = qa m ^ (-1 : ZMod d).val := (qa_neg_one m).symm
  set s := qs (d := d) (lv := lv) m
  set a := qa (d := d) (lv := lv) m
  calc s * (shiftQ (qm m γ) * a ^ (α : ZMod d).val * s)
      = (s * shiftQ (qm m γ)) * (a ^ (α : ZMod d).val * s) := by group
    _ = qm (m + 1) γ * (s * a ^ (α : ZMod d).val * s) := by rw [hγs]; group
    _ = qm (m + 1) γ * (s * (qm (m + 1) α * a * qm (m + 1) α⁻¹) * s) := by rw [hαa]
    _ = qm (m + 1) γ * ((s * qm (m + 1) α) * a * (qm (m + 1) α⁻¹ * s)) := by group
    _ = qm (m + 1) γ * shiftQ (qm m α) * (s * a * s) * shiftQ (qm m α⁻¹) := by
        rw [hαs, hαis]; group
    _ = (qm (m + 1) γ * shiftQ (qm m α)) * a * s * a⁻¹ * shiftQ (qm m (-1)) *
          shiftQ (qm m α⁻¹) := by rw [hB]; group
    _ = shiftQ (qm m α) * (qm (m + 1) γ * a) * s * a⁻¹ * shiftQ (qm m (-1)) *
          shiftQ (qm m α⁻¹) := by rw [hbt]; group
    _ = shiftQ (qm m α) * a ^ (γ : ZMod d).val * (qm (m + 1) γ * s) * a⁻¹ *
          shiftQ (qm m (-1)) * shiftQ (qm m α⁻¹) := by rw [hγa]; group
    _ = shiftQ (qm m α) * a ^ (γ : ZMod d).val * s *
          (shiftQ (qm m γ) * a ^ (-1 : ZMod d).val) * shiftQ (qm m (-1)) *
          shiftQ (qm m α⁻¹) := by rw [hγs', hinv]; group
    _ = shiftQ (qm m α) * a ^ (γ : ZMod d).val * s * a ^ (-(γ : ZMod d)⁻¹).val *
          (shiftQ (qm m γ) * (shiftQ (qm m (-1)) * shiftQ (qm m α⁻¹))) := by
        rw [hγa']; group
    _ = _ := by rw [htt]; group

end Two

/-! ### Two group-theoretic facts behind Lemmas 23 and 24 -/

section Core

variable {G : Type*} [Group G]

theorem invol_conj_inv {n x y : G} (hn : n * n = 1) (h : n * x * n = y) :
    n * x⁻¹ * n = y⁻¹ := by
  have hn' : n⁻¹ = n := inv_eq_of_mul_eq_one_left hn
  rw [← h]; simp only [mul_inv_rev, hn', mul_assoc]

theorem invol_cancel {n : G} (hn : n * n = 1) (z : G) : n * (n * z) = z := by
  rw [← mul_assoc, hn, one_mul]

/-- If `b a L = a b` and an involution inverts `a` and `L` and fixes `b`,
then `a` and `L` commute. -/
theorem comm_of_steinberg₀ {a b L n : G} (hn : n * n = 1) (ha : n * a * n = a⁻¹)
    (hb : n * b * n = b) (hL : n * L * n = L⁻¹) (e : b * a * L = a * b) :
    Commute a L := by
  have hn' := invol_cancel hn
  have h1 : L = a⁻¹ * (b⁻¹ * a * b) := by
    calc L = (b * a)⁻¹ * (b * a * L) := by group
      _ = _ := by rw [e]; group
  have h2 : L⁻¹ = a * b⁻¹ * a⁻¹ * b := by
    have hai : n * a⁻¹ * n = a := by rw [invol_conj_inv hn ha, inv_inv]
    have hbi : n * b⁻¹ * n = b⁻¹ := invol_conj_inv hn hb
    calc L⁻¹ = n * L * n := hL.symm
      _ = (n * a⁻¹ * n) * (n * b⁻¹ * n) * (n * a * n) * (n * b * n) := by
          rw [h1]; simp only [mul_assoc, hn']
      _ = _ := by rw [hai, hbi, ha, hb]
  have h3 : L = (b⁻¹ * a * b) * a⁻¹ := by
    rw [← inv_inv L, h2]; group
  show a * L = L * a
  calc a * L = b⁻¹ * a * b := by rw [h1]; group
    _ = L * a := by rw [h3]; group

/-- If `b a L = a b` and an involution inverts `b` and `L` and fixes `a`,
then `b` and `L` commute. -/
theorem comm_of_steinberg₂ {a b L n : G} (hn : n * n = 1) (ha : n * a * n = a)
    (hb : n * b * n = b⁻¹) (hL : n * L * n = L⁻¹) (e : b * a * L = a * b) :
    Commute b L := by
  have hn' := invol_cancel hn
  have h1 : L = (a⁻¹ * b⁻¹ * a) * b := by
    calc L = (b * a)⁻¹ * (b * a * L) := by group
      _ = _ := by rw [e]; group
  have h2 : L⁻¹ = a⁻¹ * b * a * b⁻¹ := by
    have hai : n * a⁻¹ * n = a⁻¹ := invol_conj_inv hn ha
    have hbi : n * b⁻¹ * n = b := by rw [invol_conj_inv hn hb, inv_inv]
    calc L⁻¹ = n * L * n := hL.symm
      _ = (n * a⁻¹ * n) * (n * b⁻¹ * n) * (n * a * n) * (n * b * n) := by
          rw [h1]; simp only [mul_assoc, hn']
      _ = _ := by rw [hai, hbi, ha, hb]
  have h3 : L = b * (a⁻¹ * b⁻¹ * a) := by
    rw [← inv_inv L, h2]; group
  show b * L = L * b
  calc b * L = b * (a⁻¹ * b⁻¹ * a) * b := by rw [h1]; group
    _ = L * b := by rw [← h3]

end Core

section Three

variable [Fact d.Prime] (m : ℕ)

/-- `CX` from wire `2` to wire `0` of `m + 3`, placed by the crossing of
the wires `1, 2` (the paper's long-range `CX`). -/
abbrev qL (m : ℕ) : Q d lv (m + 3) := shiftQ (qs m) * qa (m + 1) * shiftQ (qs m)

omit [Fact d.Prime] in
theorem qs1_mul_self : shiftQ (qs (d := d) (lv := lv) m) * shiftQ (qs m) = 1 := by
  rw [← map_mul, qs_mul_self, map_one]

omit [Fact d.Prime] in
theorem qs1_mul_self' (x : Q d lv (m + 3)) : shiftQ (qs m) * (shiftQ (qs m) * x) = x := by
  rw [← mul_assoc, qs1_mul_self, one_mul]

theorem qs1_inv : (shiftQ (qs (d := d) (lv := lv) m))⁻¹ = shiftQ (qs m) := by
  rw [← map_inv, qs_inv]

omit [Fact d.Prime] in
/-- The Yang–Baxter equation. -/
theorem yang_baxter : qs (d := d) (lv := lv) (m + 1) * shiftQ (qs m) * qs (m + 1) =
    shiftQ (qs m) * qs (m + 1) * shiftQ (qs m) := by
  have e := mk_rule m (Rules.swap_nat2 (d := d) (lv := lv) Gate.SWAP)
  simp only [seq_cons, seq_nil, one_mul, cyc, map_mul, Circuit.pad_g2, pad_shift] at e
  simpa [mul_assoc] using e

omit [Fact d.Prime] in
/-- The naturality of the crossing for `CX`: `s s₁ a = b s s₁`. -/
theorem cyc_cx : qs (d := d) (lv := lv) (m + 1) * shiftQ (qs m) * qa (m + 1) =
    shiftQ (qa m) * qs (m + 1) * shiftQ (qs m) := by
  have e := mk_rule m (Rules.swap_nat2 (d := d) (lv := lv) Gate.CX)
  simp only [seq_cons, seq_nil, one_mul, cyc, map_mul, Circuit.pad_g2, pad_shift] at e
  simpa [mul_assoc] using e

omit [Fact d.Prime] in
/-- (8): `b a L = a b`. -/
theorem steinberg : shiftQ (qa m) * qa (d := d) (lv := lv) (m + 1) * qL m =
    qa (m + 1) * shiftQ (qa m) := by
  have e := mk_rule m (Rules.r8 (d := d) (lv := lv))
  simp only [seq_cons, seq_nil, one_mul, long, map_mul, Circuit.pad_g2, pad_shift] at e
  simpa [mul_assoc] using e

omit [Fact d.Prime] in
/-- `s b s = L`. -/
theorem qs_b_qs : qs (d := d) (lv := lv) (m + 1) * shiftQ (qa m) * qs (m + 1) = qL m := by
  have e := cyc_cx (d := d) (lv := lv) m
  have hs := qs_mul_self' (d := d) (lv := lv) (m + 1)
  have hs1 := qs1_mul_self' (d := d) (lv := lv) m
  calc qs (m + 1) * shiftQ (qa m) * qs (m + 1)
      = qs (m + 1) * (shiftQ (qa m) * qs (m + 1) * shiftQ (qs m)) * shiftQ (qs m) := by
        simp only [mul_assoc, qs1_mul_self, mul_one]
    _ = qL m := by rw [← e]; simp only [mul_assoc, hs]

theorem qL_pow : qL (d := d) (lv := lv) m ^ d = 1 := by
  have : qL (d := d) (lv := lv) m = shiftQ (qs m) * qa (m + 1) * (shiftQ (qs m))⁻¹ := by
    rw [qs1_inv]
  rw [this, conj_pow, qa_pow, mul_one, mul_inv_cancel]

theorem qL_inv :
    (qL (d := d) (lv := lv) m)⁻¹ = shiftQ (qs m) * (qa (m + 1))⁻¹ * shiftQ (qs m) :=
  (invol_conj_inv (qs1_mul_self m) rfl).symm

/-- Lemma 23: the `CX` from wire `1` to wire `0` commutes with the `CX` from
wire `2` to wire `0`. -/
theorem lemma23 : Commute (qa (d := d) (lv := lv) (m + 1)) (qL m) := by
  have hn : qm (d := d) (lv := lv) (m + 2) (-1) * qm (m + 2) (-1) = 1 := relM1_sq (m + 2)
  have hninv : (qm (d := d) (lv := lv) (m + 2) (-1))⁻¹ = qm (m + 2) (-1) :=
    inv_eq_of_mul_eq_one_left hn
  have ha : qm (d := d) (lv := lv) (m + 2) (-1) * qa (m + 1) * qm (m + 2) (-1) =
      (qa (m + 1))⁻¹ := by
    have := qm_qa_conj (d := d) (lv := lv) (m + 1) (-1)
    rwa [hninv, Units.val_neg, Units.val_one, qa_neg_one] at this
  have hb : qm (d := d) (lv := lv) (m + 2) (-1) * shiftQ (qa m) * qm (m + 2) (-1) =
      shiftQ (qa m) := by
    rw [(comm1Q (Gate.M (-1)) (qa m)).eq, mul_assoc, hn, mul_one]
  have hc : qm (d := d) (lv := lv) (m + 2) (-1) * shiftQ (qs m) =
      shiftQ (qs m) * qm (m + 2) (-1) := (comm1Q (Gate.M (-1)) (qs m)).eq
  have hL : qm (d := d) (lv := lv) (m + 2) (-1) * qL m * qm (m + 2) (-1) = (qL m)⁻¹ := by
    rw [qL_inv, ← ha]
    simp only [qL, mul_assoc]
    rw [← mul_assoc _ (shiftQ (qs m)), hc, mul_assoc]
  exact comm_of_steinberg₀ hn ha hb hL (steinberg m)

/-- Lemma 24: the `CX` from wire `2` to wire `1` commutes with the `CX` from
wire `2` to wire `0`. -/
theorem lemma24 : Commute (shiftQ (qa (d := d) (lv := lv) m)) (qL m) := by
  have hn : shiftQ (shiftQ (qm (d := d) (lv := lv) m (-1))) *
      shiftQ (shiftQ (qm m (-1))) = 1 := by
    rw [← map_mul, ← map_mul, relM1_sq, map_one, map_one]
  have ha : shiftQ (shiftQ (qm (d := d) (lv := lv) m (-1))) * qa (m + 1) *
      shiftQ (shiftQ (qm m (-1))) = qa (m + 1) := by
    rw [← (comm2Q Gate.CX (qm (d := d) (lv := lv) m (-1))).eq, mul_assoc, hn, mul_one]
  have hb : shiftQ (shiftQ (qm (d := d) (lv := lv) m (-1))) * shiftQ (qa m) *
      shiftQ (shiftQ (qm m (-1))) = (shiftQ (qa m))⁻¹ := by
    have := congrArg shiftQ (relM1CX (d := d) (lv := lv) m)
    simpa only [map_mul, map_inv, shiftQ_mk] using this
  -- the multiplier passes the crossing of the wires `1, 2` to wire `1`
  have hsn : shiftQ (qs (d := d) (lv := lv) m) * shiftQ (shiftQ (qm m (-1))) =
      shiftQ (qm (m + 1) (-1)) * shiftQ (qs m) := by
    have := congrArg shiftQ (qs_qmt (d := d) (lv := lv) m (-1))
    simpa only [map_mul] using this
  have hns : shiftQ (shiftQ (qm (d := d) (lv := lv) m (-1))) * shiftQ (qs m) =
      shiftQ (qs m) * shiftQ (qm (m + 1) (-1)) := by
    have := congrArg shiftQ (qs_qm (d := d) (lv := lv) m (-1))
    simpa only [map_mul] using this.symm
  have h1a : shiftQ (qm (d := d) (lv := lv) (m + 1) (-1)) * qa (m + 1) *
      shiftQ (qm (m + 1) (-1)) = (qa (m + 1))⁻¹ := relM1CX (m + 1)
  have hL : shiftQ (shiftQ (qm (d := d) (lv := lv) m (-1))) * qL m *
      shiftQ (shiftQ (qm m (-1))) = (qL m)⁻¹ := by
    rw [qL_inv, ← h1a]
    calc shiftQ (shiftQ (qm (d := d) (lv := lv) m (-1))) * qL m *
          shiftQ (shiftQ (qm m (-1)))
        = (shiftQ (shiftQ (qm m (-1))) * shiftQ (qs m)) * qa (m + 1) *
            (shiftQ (qs m) * shiftQ (shiftQ (qm m (-1)))) := by simp only [qL, mul_assoc]
      _ = _ := by rw [hns, hsn]; simp only [mul_assoc]
  exact comm_of_steinberg₂ hn ha hb hL (steinberg m)

/-- `ā = s a s`, the `CX` from wire `0` to wire `1`, commutes with `b`, the
`CX` from wire `2` to wire `1`. -/
theorem abar_comm_b :
    Commute (qs (d := d) (lv := lv) (m + 1) * qa (m + 1) * qs (m + 1)) (shiftQ (qa m)) := by
  have hs := qs_mul_self' (d := d) (lv := lv) (m + 1)
  have hsb := qs_b_qs (d := d) (lv := lv) m
  have h23 := (lemma23 (d := d) (lv := lv) m).eq
  set s := qs (d := d) (lv := lv) (m + 1)
  set a := qa (d := d) (lv := lv) (m + 1)
  set b := shiftQ (qa (d := d) (lv := lv) m)
  show s * a * s * b = b * (s * a * s)
  have hs2 : s * s = 1 := qs_mul_self (m + 1)
  calc s * a * s * b = s * (a * (s * b * s)) * s := by simp only [mul_assoc, hs2, mul_one]
    _ = s * ((s * b * s) * a) * s := by rw [hsb, h23]
    _ = b * (s * a * s) := by simp only [mul_assoc, hs]

omit [Fact d.Prime] in
/-- The cyclic permutation `P = s s₁` has order three. -/
theorem cyc_cube : (qs (d := d) (lv := lv) (m + 1) * shiftQ (qs m)) ^ 3 = 1 := by
  have hs := qs_mul_self' (d := d) (lv := lv) (m + 1)
  have hs2 := qs_mul_self (d := d) (lv := lv) (m + 1)
  have hs1 := qs1_mul_self' (d := d) (lv := lv) m
  have hy := yang_baxter (d := d) (lv := lv) m
  calc (qs (m + 1) * shiftQ (qs m)) ^ 3
      = (qs (m + 1) * shiftQ (qs m) * qs (m + 1)) * (shiftQ (qs m) * qs (m + 1) *
          shiftQ (qs m)) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [hy]; simp only [mul_assoc, hs1, hs, qs1_mul_self]

/-- The `CX` from wire `0` to wire `2`, in two ways: `s₁ ā s₁ = s ↑ā s`. -/
theorem abar_long :
    shiftQ (qs (d := d) (lv := lv) m) * (qs (m + 1) * qa (m + 1) * qs (m + 1)) *
      shiftQ (qs m) =
    qs (m + 1) * shiftQ (qs m * qa m * qs m) * qs (m + 1) := by
  have hc := cyc_cx (d := d) (lv := lv) m
  have h3 := cyc_cube (d := d) (lv := lv) m
  have hsi : (qs (d := d) (lv := lv) (m + 1))⁻¹ = qs (m + 1) := qs_inv (m + 1)
  have hs1i := qs1_inv (d := d) (lv := lv) m
  rw [map_mul, map_mul]
  set s := qs (d := d) (lv := lv) (m + 1)
  set s1 := shiftQ (qs (d := d) (lv := lv) m)
  set a := qa (d := d) (lv := lv) (m + 1)
  set b := shiftQ (qa (d := d) (lv := lv) m)
  have hP : s * s1 * s * s1 = s1 * s := by
    rw [pow_succ, pow_succ, pow_one] at h3
    calc s * s1 * s * s1 = s * s1 * (s * s1) * (s * s1) * (s1⁻¹ * s⁻¹) := by group
      _ = s1 * s := by rw [h3, one_mul, hsi, hs1i]
  have hP' : s1 * s * s1 * s = s * s1 := by
    have h := congrArg (·⁻¹) hP
    simp only [mul_inv_rev, hsi, hs1i] at h
    simpa [mul_assoc] using h
  -- `b = P a P⁻¹` with `P = s s₁`
  have hb : b = s * s1 * a * (s1 * s) := by
    calc b = b * s * s1 * (s1⁻¹ * s⁻¹) := by group
      _ = s * s1 * a * (s1 * s) := by rw [← hc, hsi, hs1i]
  show s1 * (s * a * s) * s1 = s * (s1 * b * s1) * s
  rw [hb]
  calc s1 * (s * a * s) * s1 = (s1 * s) * a * (s * s1) := by group
    _ = (s * s1 * s * s1) * a * (s1 * s * s1 * s) := by rw [hP, hP']
    _ = s * (s1 * (s * s1 * a * (s1 * s)) * s1) * s := by group

/-- The Steinberg relation with labels: `b a^k = a^k b L^{-k}`. -/
theorem steinberg_pow (k : ZMod d) :
    shiftQ (qa (d := d) (lv := lv) m) * qa (m + 1) ^ k.val =
      qa (m + 1) ^ k.val * shiftQ (qa m) * qL m ^ (-k).val := by
  have e := steinberg (d := d) (lv := lv) m
  have hc : Commute (qL (d := d) (lv := lv) m) (qa (m + 1)) := (lemma23 m).symm
  have hp := qL_pow (d := d) (lv := lv) m
  set a := qa (d := d) (lv := lv) (m + 1)
  set b := shiftQ (qa (d := d) (lv := lv) m)
  set L := qL (d := d) (lv := lv) m
  have e' : b * a = a * b * L⁻¹ := by
    rw [← e]; group
  have hK : ∀ K : ℕ, b * a ^ K = a ^ K * b * (L⁻¹) ^ K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      calc b * a ^ (K + 1) = (b * a ^ K) * a := by rw [pow_succ, mul_assoc]
        _ = a ^ K * b * ((L⁻¹) ^ K * a) := by rw [ih]; group
        _ = a ^ K * (b * a) * (L⁻¹) ^ K := by
            rw [((hc.inv_left).pow_left K).eq]; group
        _ = a ^ (K + 1) * b * (L⁻¹) ^ (K + 1) := by rw [e']; group
  rw [hK, pow_val_neg hp, inv_pow]

/-- The exchange of the two lower entries of a stair:
`s b^γ s₁ a^α s = b^α s₁ a^γ s s₁`. -/
theorem stair_swap (α γ : ZMod d) :
    qs (d := d) (lv := lv) (m + 1) * (shiftQ (qa m) ^ γ.val * shiftQ (qs m) *
      qa (m + 1) ^ α.val * qs (m + 1)) =
    shiftQ (qa m) ^ α.val * shiftQ (qs m) * qa (m + 1) ^ γ.val * qs (m + 1) *
      shiftQ (qs m) := by
  have hs1 := qs1_mul_self' (d := d) (lv := lv) m
  have hc := cyc_cx (d := d) (lv := lv) m
  have hy := yang_baxter (d := d) (lv := lv) m
  have h24 := lemma24 (d := d) (lv := lv) m
  have hsb0 := qs_b_qs (d := d) (lv := lv) m
  have hsi : (qs (d := d) (lv := lv) (m + 1))⁻¹ = qs (m + 1) := qs_inv (m + 1)
  have hs1i := qs1_inv (d := d) (lv := lv) m
  set s := qs (d := d) (lv := lv) (m + 1)
  set s1 := shiftQ (qs (d := d) (lv := lv) m)
  set a := qa (d := d) (lv := lv) (m + 1)
  set b := shiftQ (qa (d := d) (lv := lv) m)
  set L := qL (d := d) (lv := lv) m
  have hsb : ∀ K : ℕ, s * b ^ K = L ^ K * s := by
    intro K
    calc s * b ^ K = (s * b * s⁻¹) ^ K * s := by rw [conj_pow]; group
      _ = L ^ K * s := by rw [hsi, hsb0]
  have hPa : ∀ K : ℕ, s * s1 * a ^ K = b ^ K * (s * s1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      calc s * s1 * a ^ (K + 1) = (s * s1 * a ^ K) * a := by rw [pow_succ]; group
        _ = b ^ K * (s * s1 * a) := by rw [ih]; group
        _ = b ^ (K + 1) * (s * s1) := by rw [hc, pow_succ]; group
  have hL : ∀ K : ℕ, s1 * a ^ K * s1 = L ^ K := by
    intro K
    calc s1 * a ^ K * s1 = (s1 * a * s1⁻¹) ^ K := by rw [conj_pow, hs1i]
      _ = L ^ K := by rw [hs1i]
  calc s * (b ^ γ.val * s1 * a ^ α.val * s)
      = L ^ γ.val * (s * s1 * a ^ α.val) * s := by simp only [← mul_assoc]; rw [hsb]
    _ = L ^ γ.val * b ^ α.val * (s * s1 * s) := by rw [hPa]; group
    _ = b ^ α.val * L ^ γ.val * (s1 * s * s1) := by
        rw [hy, ((h24.symm.pow_left γ.val).pow_right α.val).eq]
    _ = b ^ α.val * (s1 * a ^ γ.val * s1) * (s1 * s * s1) := by rw [hL]
    _ = _ := by simp only [mul_assoc, hs1]

end Three

end QCert.PhaseAffine
