/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Derivations under idle wires, and completeness one width down

Toward Theorem 4.4 by induction on the width (a stabiliser-chain argument,
not the paper's 380 box relations):

* a derivation on `k` wires is a derivation on the bottom `k` of `m + k`
  wires (`derives_pad`) and, moved up, on the top `k` of `k + 1`
  (`derives_shift`, in `Soundness.lean`);
* hence, with completeness at a smaller width as hypothesis, a segment of a
  circuit that is syntactically on a proper subset of the wires (padded
  under idle wires, or shifted) may be replaced by any segment with the
  same operator (`seg_pad`, `seg_shift`);
* the scalar `-ω` commutes with every circuit (`negω_comm`), its powers are
  determined by their operators (`negω_pow_derives`), completeness holds on
  no wires (`complete_zero`), and a top circuit times a power of `-ω` with
  trivial operator is derivably trivial (`trivial_of_top`).
-/
import QCert.QutritClifford.Count

namespace QCert.QutritClifford

open Circuit Matrix

/-! ### Padding twice -/

section HEq

variable {G : ℕ → Type}

theorem gate0_heq {a b : ℕ} (h : a = b) (c : G 0) :
    HEq (Gen.gate0 (n := a) c) (Gen.gate0 (n := b) c) := by subst h; rfl

theorem gate1_heq {a b : ℕ} (h : a = b) (c : G 1) :
    HEq (Gen.gate1 (n := a) c) (Gen.gate1 (n := b) c) := by subst h; rfl

theorem gate2_heq {a b : ℕ} (h : a = b) (c : G 2) :
    HEq (Gen.gate2 (n := a) c) (Gen.gate2 (n := b) c) := by subst h; rfl

theorem gate3_heq {a b : ℕ} (h : a = b) (c : G 3) :
    HEq (Gen.gate3 (n := a) c) (Gen.gate3 (n := b) c) := by subst h; rfl

theorem up_heq {a b : ℕ} (h : a = b) {x : Gen G a} {y : Gen G b} (hxy : HEq x y) :
    HEq (Gen.up x) (Gen.up y) := by subst h; cases hxy; rfl

theorem gen_pad_pad_heq (n m : ℕ) : {k : ℕ} → (x : Gen G k) →
    HEq (Gen.pad n (Gen.pad m x)) (Gen.pad (n + m) x)
  | _, .gate0 c => gate0_heq (Nat.add_assoc _ _ _).symm c
  | _, .gate1 c => gate1_heq (Nat.add_assoc _ _ _).symm c
  | _, .gate2 c => gate2_heq (Nat.add_assoc _ _ _).symm c
  | _, .gate3 c => gate3_heq (Nat.add_assoc _ _ _).symm c
  | _, .up x => up_heq (Nat.add_assoc _ _ _).symm (gen_pad_pad_heq n m x)

theorem map_heq {k a b : ℕ} (h : a = b) {f : Gen G k → Gen G a} {f' : Gen G k → Gen G b}
    (hf : ∀ x, HEq (f x) (f' x)) (w : Circuit G k) :
    HEq (FreeMonoid.map f w) (FreeMonoid.map f' w) := by
  subst h
  have : f = f' := funext fun x => eq_of_heq (hf x)
  subst this; rfl

theorem pad_pad_heq (n m : ℕ) {k : ℕ} (w : Circuit G k) :
    HEq (Circuit.pad n (Circuit.pad m w)) (Circuit.pad (n + m) w) := by
  show HEq (FreeMonoid.map (Gen.pad n) (FreeMonoid.map (Gen.pad m) w)) _
  rw [FreeMonoid.map_map]
  exact map_heq (Nat.add_assoc _ _ _).symm (fun x => gen_pad_pad_heq n m x) w

theorem pad_shift (n : ℕ) {k : ℕ} (w : Circuit G k) :
    Circuit.pad n (Circuit.shift w) = Circuit.shift (Circuit.pad n w) := by
  show FreeMonoid.map (Gen.pad n) (FreeMonoid.map Gen.up w) =
    FreeMonoid.map Gen.up (FreeMonoid.map (Gen.pad n) w)
  rw [FreeMonoid.map_map, FreeMonoid.map_map]; rfl

end HEq

/-! ### Derivations under idle wires -/

theorem derives_heq {a b : ℕ} (h : a = b) {w v : Circ a} {w' v' : Circ b} (hw : HEq w w')
    (hv : HEq v v') (d : Derives (Padded Rule) a w v) : Derives (Padded Rule) b w' v' := by
  subst h; cases hw; cases hv; exact d

theorem theory_pad (n : ℕ) {k : ℕ} {w v : Circ k} (h : Theory k w v) :
    Derives (Padded Rule) (n + k) (Circuit.pad n w) (Circuit.pad n v) := by
  induction h with
  | rule hr =>
    cases hr with
    | @pad j m w' v' hb =>
      exact derives_heq (Nat.add_assoc n m j) (pad_pad_heq n m w').symm
        (pad_pad_heq n m v').symm (derives_rule (n := n + m) hb)
  | shift _ ih =>
    rw [pad_shift, pad_shift]; exact derives_shift ih
  | comm1 c y =>
    simp only [map_mul, Circuit.pad, FreeMonoid.map_of]
    exact Derivable.of (Lift.comm1 c (Gen.pad n y))
  | comm2 c y =>
    simp only [map_mul, Circuit.pad, FreeMonoid.map_of]
    exact Derivable.of (Lift.comm2 c (Gen.pad n y))
  | comm3 c y =>
    simp only [map_mul, Circuit.pad, FreeMonoid.map_of]
    exact Derivable.of (Lift.comm3 c (Gen.pad n y))
  | scalar c =>
    simp only [Circuit.pad, FreeMonoid.map_of]
    exact Derivable.of (Lift.scalar (n := n + _) c)

/-- A derivation on `k` wires is a derivation on the bottom `k` of `n + k`
wires. -/
theorem derives_pad (n : ℕ) {k : ℕ} {w v : Circ k} (h : Derives (Padded Rule) k w v) :
    Derives (Padded Rule) (n + k) (Circuit.pad n w) (Circuit.pad n v) := by
  have : conGen (Theory k) ≤ (conGen (Theory (n + k))).comap (Circuit.pad n) (map_mul _) :=
    Con.conGen_le fun a b hab => theory_pad n hab
  exact this h

/-! ### Completeness one width down -/

/-- Completeness on `n` wires: circuits with the same operator are
derivably equal. -/
def Complete (n : ℕ) : Prop :=
  ∀ w v : Circ n, sem n w = sem n v → Derives (Padded Rule) n w v

/-- **Segment replacement, padded**: with completeness on `k` wires, a
segment on the bottom `k` of `m + k` wires (idle wires on top) may be
replaced by any segment with the same operator. -/
theorem seg_pad (m : ℕ) {k : ℕ} (hk : Complete k) {u u' : Circ k} (h : sem k u = sem k u') :
    Derives (Padded Rule) (m + k) (Circuit.pad m u) (Circuit.pad m u') :=
  derives_pad m (hk u u' h)

/-- **Segment replacement, shifted**: with completeness on `k` wires, a
segment on the top `k` of `k + 1` wires (an idle wire below) may be replaced
by any segment with the same operator. -/
theorem seg_shift {k : ℕ} (hk : Complete k) {u u' : Circ k} (h : sem k u = sem k u') :
    Derives (Padded Rule) (k + 1) (Circuit.shift u) (Circuit.shift u') :=
  derives_shift (hk u u' h)

/-! ### The scalar -/

/-- The scalar rule moved up: `-ω` on top of any number of wires is `-ω`. -/
theorem up_negω {n : ℕ} :
    Derives (Padded Rule) (n + 1) (FreeMonoid.of (Gen.gate0 Gate.negω : Gen Gate n).up) negω :=
  Derivable.of (Lift.scalar Gate.negω)

theorem negω_comm_gen : ∀ {n : ℕ} (g : Gen Gate n),
    Derives (Padded Rule) n (negω * FreeMonoid.of g) (FreeMonoid.of g * negω)
  | _, .gate0 .negω => Derivable.refl _
  | n + 1, .gate1 h => by
    have c := Derivable.of (Γ := Theory (n + 1)) (Lift.comm1 h (Gen.gate0 Gate.negω : Gen Gate n))
    exact ((up_negω.symm.mul (Derivable.refl _)).trans c).trans
      ((Derivable.refl _).mul up_negω)
  | n + 2, .gate2 h => by
    have c := Derivable.of (Γ := Theory (n + 2))
      (Lift.comm2 h (Gen.gate0 Gate.negω : Gen Gate n))
    have e : Derives (Padded Rule) (n + 2)
        (FreeMonoid.of (Gen.gate0 Gate.negω : Gen Gate n).up.up) negω := by
      have := derives_shift (up_negω (n := n))
      rw [Circuit.shift_of] at this
      exact this.trans up_negω
    exact ((e.symm.mul (Derivable.refl _)).trans c).trans ((Derivable.refl _).mul e)
  | _, .gate3 g => nomatch g
  | n + 1, .up g => by
    have ih := derives_shift (negω_comm_gen g)
    rw [map_mul, map_mul, Circuit.shift_of] at ih
    exact ((up_negω.symm.mul (Derivable.refl _)).trans
      (by simpa [negω] using ih)).trans ((Derivable.refl _).mul up_negω)

/-- `-ω` commutes with every circuit. -/
theorem negω_comm {n : ℕ} (w : Circ n) : Derives (Padded Rule) n (negω * w) (w * negω) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [mul_one, one_mul]
  | mul_of g w ih =>
    have h1 : Derives (Padded Rule) n (negω * FreeMonoid.of g * w) (FreeMonoid.of g * negω * w) :=
      (negω_comm_gen g).mul (Derivable.refl w)
    have h2 : Derives (Padded Rule) n (FreeMonoid.of g * (negω * w))
        (FreeMonoid.of g * (w * negω)) := (Derivable.refl _).mul ih
    rw [← mul_assoc]
    refine h1.trans ?_
    rw [mul_assoc (FreeMonoid.of g) w negω]
    exact h2

theorem derives_pow {n : ℕ} {x y : Circ n} (h : Derives (Padded Rule) n x y) :
    ∀ k : ℕ, Derives (Padded Rule) n (x ^ k) (y ^ k)
  | 0 => by rw [pow_zero, pow_zero]
  | k + 1 => by rw [pow_succ, pow_succ]; exact (derives_pow h k).mul h

theorem negω_pow_six (n : ℕ) : Derives (Padded Rule) n (negω ^ 6) 1 := by
  have := derives_rule (n := n) Rule.C1
  simp only [map_pow, map_one] at this
  exact this

theorem negω_pow_mod (n a : ℕ) : Derives (Padded Rule) n (negω ^ a) (negω ^ (a % 6)) := by
  have hq : ∀ q : ℕ, Derives (Padded Rule) n ((negω ^ 6) ^ q) 1 := by
    intro q
    induction q with
    | zero => rw [pow_zero]
    | succ q ih =>
      rw [pow_succ, ← mul_one (1 : Circ n)]
      exact ih.mul (negω_pow_six n)
  conv_lhs => rw [← Nat.div_add_mod a 6, pow_add, pow_mul]
  have := (hq (a / 6)).mul (Derivable.refl (negω ^ (a % 6) : Circ n))
  rwa [one_mul] at this

theorem negω_pow_six_eq : (-ωℂ) ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, neg_pow, ωℂ_pow_three]; norm_num

/-- Powers of `-ω` are determined by their value. -/
theorem negω_pow_derives (n : ℕ) {a b : ℕ} (h : (-ωℂ) ^ a = (-ωℂ) ^ b) :
    Derives (Padded Rule) n (negω ^ a) (negω ^ b) := by
  have hmod : ∀ c : ℕ, (-ωℂ) ^ c = (-ωℂ) ^ (c % 6) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c 6, pow_add, pow_mul, negω_pow_six_eq, one_pow, one_mul]
  have e : a % 6 = b % 6 :=
    negω_pow_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      (by rw [← hmod, ← hmod, h])
  exact (negω_pow_mod n a).trans (by rw [e]; exact (negω_pow_mod n b).symm)

/-- On no wires every circuit is a power of `-ω`. -/
theorem circ0_eq (w : Circ 0) : w = negω ^ FreeMonoid.length w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    cases g with
    | gate0 c =>
      cases c
      rw [FreeMonoid.length_mul, FreeMonoid.length_of, add_comm, pow_succ', ← ih]
      rfl

/-- **Completeness on no wires**: by (C1). -/
theorem complete_zero : Complete 0 := by
  intro w v h
  rw [circ0_eq w, circ0_eq v] at h ⊢
  have e := congrArg (fun U : unitaryGroup (State 3 0) ℂ => (U : Op ℂ 3 0) 0 0) h
  simp only [sem_negω_pow, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e
  exact negω_pow_derives 0 e

/-- **A top circuit times a power of `-ω` with trivial operator is
derivably trivial**, given completeness one width down. -/
theorem trivial_of_top {m : ℕ} (hc : Complete m) (u : Circ m) (t : ℕ)
    (h : sem (m + 1) (Circuit.shift u * negω ^ t) = 1) :
    Derives (Padded Rule) (m + 1) (Circuit.shift u * negω ^ t) 1 := by
  set s := (6 - t % 6) % 6 with hs
  have hst : (-ωℂ) ^ (s + t) = 1 := by
    have : (s + t) % 6 = 0 := by omega
    rw [← Nat.div_add_mod (s + t) 6, this, add_zero, pow_mul, negω_pow_six_eq, one_pow]
  have hu : sem m u = sem m (negω ^ s) := by
    apply Subtype.ext
    rw [sem_negω_pow]
    apply onTop1_inj
    have e := congrArg Subtype.val h
    rw [map_mul, Submonoid.coe_mul, sem_negω_pow,
      show ((sem (m + 1) (Circuit.shift u) : unitaryGroup (State 3 (m + 1)) ℂ) : Op ℂ 3 (m + 1)) =
        onTop 1 (sem m u : Op ℂ 3 m) from congrArg Subtype.val (gateSem.sem_shift u)] at e
    rw [onTop_smul, onTop_one]
    calc onTop 1 (sem m u : Op ℂ 3 m)
        = onTop 1 (sem m u : Op ℂ 3 m) * ((-ωℂ) ^ t • (1 : Op ℂ 3 (m + 1))) *
            ((-ωℂ) ^ s • (1 : Op ℂ 3 (m + 1))) := by
          rw [mul_assoc, smul_mul_smul_comm, mul_one, ← pow_add, show t + s = s + t from Nat.add_comm t s,
            hst, one_smul, mul_one]
      _ = (-ωℂ) ^ s • (1 : Op ℂ 3 (m + 1)) := by
          rw [e]; exact one_mul _
  have d1 : Derives (Padded Rule) (m + 1) (Circuit.shift u) (negω ^ s) := by
    refine (derives_shift (hc _ _ hu)).trans ?_
    rw [map_pow, show Circuit.shift (negω : Circ m) =
      FreeMonoid.of (Gen.gate0 Gate.negω : Gen Gate m).up from rfl]
    exact derives_pow up_negω s
  have d2 := d1.mul (Derivable.refl (negω ^ t : Circ (m + 1)))
  rw [← pow_add] at d2
  have d3 := negω_pow_derives (m + 1) (a := s + t) (b := 0) (by rw [hst, pow_zero])
  rw [pow_zero] at d3
  exact d2.trans d3

end QCert.QutritClifford
