/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A normal form for linear circuits

Every linear circuit (multipliers, `CX`, crossings) on `n + 1` wires is
equal in the theory to a *stair* followed by a *fan* and a linear circuit on
the upper `n` wires (`decompose`).  This is the first half of the
completeness of the linear fragment of `Aff_d` (`Linear`), which Blake
(arXiv:2603.06466) takes from Lafont's normal form theorem [17] (with the
derivations of Lafont's rules, Lemma 16); here it is proved directly.

## Design

Write `a = CX` (control wire `1`, target wire `0`, `x₀ ↦ x₀ + x₁`),
`s` for the crossing of the wires `0, 1`, `m₀ u` for `M_u` on wire `0`,
and `↑` for a circuit moved up one wire.  The circuits act on column vectors
`x = (x₀, …, x_n)`, `x₀` on the bottom wire; the linear group is
`GL_{n+1}(𝔽_d)`.

**The subgroup.**  `H` is the stabiliser of the unit vector `e₀`: the maps
`x ↦ (x₀ + ∑ c_j x_{j+1}, B (x₁, …, x_n))`.  Each is `F(c) · ↑B`, with the
*fan*

    F(c) : x₀ ↦ x₀ + c₀ x₁ + ⋯ + c_{n-1} x_n,
    F(c) = s · ↑F(c₁, …, c_{n-1}) · s · a^{c₀}        (`fanW`),

that is, `a^{c₀}` and then the fan from the wires `2, …, n`, which is the
fan on `n` wires placed on the wires `0, 2, …, n` by conjugating with `s`
(`KQ q = s ↑q s`).  The words `F(c) ↑B` with `B` linear on `n` wires form
`H` (`InH`); `H` is closed under products because

* `F(c) F(c') = F(c + c')` (`fan_add`): `a` commutes with the fan from the
  wires `2, …` (`qa_comm_KQfan`, from the `CX` from wire `0` to wire `1`
  commuting with `CX` from wire `2` to wire `1`, `abar_comm_b`, and its
  conjugates, `abar_long`);
* a linear circuit moved up one wire passes a fan, changing its labels by
  an invertible map (`fan_word`): for the generators of the upper wires,
  `M` on wire `1` by (4), the crossing of the wires `1, 2` by the Yang–Baxter
  equation and Lemma 23, `CX` from wire `2` to wire `1` by the Steinberg
  relation (8) and Lemmas 23, 24, and a generator two wires up inductively.

**The representatives.**  The cosets `g H` correspond to the nonzero
vectors `v = g e₀`.  The *stair* of `v` is

    S(v) = M_{v₀}                    if v₁ = ⋯ = v_n = 0,
    S(v) = ↑S(v₁, …, v_n) · a^{v₀} · s   otherwise          (`stairW`),

which sends `e₀` to `v`: the crossing carries `e₀` to `e₁`, `a^{v₀}` adds
`v₀ e₀`, and the stair one wire up carries `e₁` to `(0, v₁, …, v_n)`.

**The rewriting.**  A linear circuit is built by applying generators to
the empty circuit `S(e₀) F(0) ↑1`; a generator `g` applied to `S(v) F(c) ↑B`
is rewritten by the *table* (`table`): `g S(v) = S(w) h` with `w ≠ 0` and
`h ∈ H`, after which `h F(c) ↑B` is in `H` again.  The cases of the table:

* `M_x` on wire `0`: `M_x M_{v₀} = M_{x v₀}` ((2)); on a stair it passes
  `↑S` (disjoint wires), turns `a^{v₀}` into `a^{x v₀}` ((5)), and passes the
  crossing onto wire `1`, leaving `↑M_x ∈ H`;
* `a`: `a M_u = M_u a^{1/u}` ((5)), `a^{1/u} = F(1/u, 0, …) ∈ H`; on a stair
  `a ↑S = ↑S F(c)` for some `c` (a fan pulled through a circuit one wire up),
  and `F(c) a^{v₀} s = a^{c₀ + v₀} s ↑F(c₁, …)`;
* `s`: `s M_u = ↑M_u s`, the stair of `(0, u, 0, …)`; on a stair whose
  stair one wire up is again a stair, the lower two steps exchange
  (`stair_swap`, from the naturality of the crossing for `CX`, Yang–Baxter
  and Lemma 24), leaving the crossing of the wires `1, 2`; on
  `↑M_γ a^α s` (`v = (α, γ, 0, …)`) the Bruhat relation of `GL₂(𝔽_d)` from
  (7) (`bruhat`, `α ≠ 0`) or `s ↑M_γ s = M_γ` (`α = 0`);
* a generator `g` one wire up: `↑g M_u = M_u ↑g`; on a stair `↑g ↑S = ↑(S(w') F(c) ↑B)`
  by the table one wire up, and `↑F(c)`, `↑↑B` pass `a^{v₀} s` into `H`.

The second half, that two such forms with the same linear map are equal
(the stair is fixed by `g e₀`, the fan by the first row, the rest by the
induction on the number of wires), is in `Linear`.
-/
import QCert.PhaseAffine.LinearLocal

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

/-! ### Linear words -/

theorem isLinW_shift {n : ℕ} {w : C d lv n} (h : IsLinW w) : IsLinW (shift w) := by
  intro y hy
  simp only [Circuit.shift, FreeMonoid.toList_map, List.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact h z hz

theorem IsLinW.pow {n : ℕ} {w : C d lv n} (h : IsLinW w) (k : ℕ) : IsLinW (w ^ k) := by
  induction k with
  | zero => simpa using IsLinW.one
  | succ k ih => rw [pow_succ]; exact ih.mul h

theorem IsLinW.of_mul {n : ℕ} {x : Gen (Gate d lv) n} {w : C d lv n}
    (h : IsLinW (FreeMonoid.of x * w)) : x.IsLin ∧ IsLinW w := by
  refine ⟨h x (by simp), fun y hy => h y ?_⟩
  rw [FreeMonoid.toList_of_mul]; exact List.mem_cons_of_mem _ hy

theorem isLinW_M {n : ℕ} (a : (ZMod d)ˣ) : IsLinW (g1 (n := n) (Gate.M (d := d) (lv := lv) a)) :=
  IsLinW.of trivial

theorem isLinW_g2 {n : ℕ} (g : Gate d lv 2) : IsLinW (g2 (n := n) g) := IsLinW.of trivial

/-! ### Fans and stairs as words -/

/-- The fan `F(c)` on `n + 1` wires, `x₀ ↦ x₀ + ∑ c_j x_{j+1}`: `CX^{c₀}`,
then the fan on the wires `0, 2, …, n` (the fan on `n` wires one wire up,
conjugated by the crossing of the wires `0, 1`). -/
def fanW : (n : ℕ) → Lab d n → C d lv (n + 1)
  | 0, _ => 1
  | n + 1, c => g2 Gate.SWAP * shift (fanW n (Fin.tail c)) * g2 Gate.SWAP * g2 Gate.CX ^ (c 0).val

theorem isLinW_fanW : ∀ (n : ℕ) (c : Lab d n), IsLinW (fanW (lv := lv) n c)
  | 0, _ => IsLinW.one
  | n + 1, _ =>
    (((isLinW_g2 _).mul (isLinW_shift (isLinW_fanW n _))).mul (isLinW_g2 _)).mul
      ((isLinW_g2 _).pow _)

section Field

variable [Fact d.Prime]

/-- The unit with value `x` (and `1` at `0`). -/
def unitOf (x : ZMod d) : (ZMod d)ˣ := if h : x = 0 then 1 else Units.mk0 x h

theorem unitOf_val {x : ZMod d} (h : x ≠ 0) : ((unitOf x : (ZMod d)ˣ) : ZMod d) = x := by
  simp [unitOf, h]

theorem unitOf_one : unitOf (1 : ZMod d) = 1 := by
  ext; rw [unitOf_val one_ne_zero, Units.val_one]

/-- The stair of `v ≠ 0` on `n + 1` wires, a linear circuit sending `e₀` to
`v`: `M_{v₀}` if `v` is zero above wire `0`, and otherwise the crossing of
the wires `0, 1`, then `CX^{v₀}`, then the stair of `(v₁, …, v_n)` one wire
up. -/
def stairW : (n : ℕ) → Lab d (n + 1) → C d lv (n + 1)
  | 0, v => g1 (Gate.M (unitOf (v 0)))
  | n + 1, v => if Fin.tail v = 0 then g1 (Gate.M (unitOf (v 0)))
      else shift (stairW n (Fin.tail v)) * g2 Gate.CX ^ (v 0).val * g2 Gate.SWAP

theorem isLinW_stairW : ∀ (n : ℕ) (v : Lab d (n + 1)), IsLinW (stairW (lv := lv) n v)
  | 0, _ => isLinW_M _
  | n + 1, v => by
    rw [stairW]
    split_ifs
    · exact isLinW_M _
    · exact ((isLinW_shift (isLinW_stairW n _)).mul ((isLinW_g2 _).pow _)).mul (isLinW_g2 _)

end Field

/-! ### The placement on the wires `0, 2, 3, …` -/

section Group

variable [Fact d.Prime]

/-- A circuit on `m + 1` wires placed on the wires `0, 2, …, m + 1`: moved up
one wire and conjugated by the crossing of the wires `0, 1`. -/
def KQ (m : ℕ) : Q d lv (m + 1) →* Q d lv (m + 2) where
  toFun q := qs m * shiftQ q * qs m
  map_one' := by rw [map_one, mul_one, qs_mul_self]
  map_mul' q r := by simp only [map_mul, mul_assoc, qs_mul_self']

omit [Fact d.Prime] in
theorem KQ_apply {m : ℕ} (q : Q d lv (m + 1)) : KQ m q = qs m * shiftQ q * qs m := rfl

omit [Fact d.Prime] in
theorem KQ_shiftQ {m : ℕ} (q : Q d lv m) : KQ m (shiftQ q) = shiftQ (shiftQ q) := by
  rw [KQ_apply, (comm2Q Gate.SWAP q).eq, mul_assoc, qs_mul_self, mul_one]

omit [Fact d.Prime] in
theorem KQ_qa (m : ℕ) : KQ (m + 1) (qa (d := d) (lv := lv) m) = qL m := qs_b_qs m

omit [Fact d.Prime] in
theorem KQ_mul_qs {m : ℕ} (q : Q d lv (m + 1)) : KQ m q * qs m = qs m * shiftQ q := by
  rw [KQ_apply, mul_assoc, qs_mul_self, mul_one]

omit [Fact d.Prime] in
theorem qs_mul_shiftQ {m : ℕ} (q : Q d lv (m + 1)) : qs m * shiftQ q = KQ m q * qs m :=
  (KQ_mul_qs q).symm

/-- `M` on wire `1` commutes with a circuit placed on the wires `0, 2, …`. -/
theorem qmt_comm_KQ {m : ℕ} (a : (ZMod d)ˣ) (q : Q d lv (m + 1)) :
    Commute (shiftQ (qm m a)) (KQ m q) := by
  have h1 : shiftQ (qm (d := d) (lv := lv) m a) * qs m = qs m * qm (m + 1) a := (qs_qm m a).symm
  have h2 : qm (d := d) (lv := lv) (m + 1) a * qs m = qs m * shiftQ (qm m a) := (qs_qmt m a).symm
  have h3 : qm (d := d) (lv := lv) (m + 1) a * shiftQ q = shiftQ q * qm (m + 1) a :=
    (comm1Q (Gate.M a) q).eq
  show shiftQ (qm m a) * (qs m * shiftQ q * qs m) = qs m * shiftQ q * qs m * shiftQ (qm m a)
  calc shiftQ (qm m a) * (qs m * shiftQ q * qs m)
      = (shiftQ (qm m a) * qs m) * shiftQ q * qs m := by group
    _ = qs m * ((qm (m + 1) a * shiftQ q) * qs m) := by rw [h1]; group
    _ = qs m * shiftQ q * (qm (m + 1) a * qs m) := by rw [h3]; group
    _ = _ := by rw [h2]; group

theorem commute_conj_invol {G : Type*} [Group G] {n x y : G} (hn : n * n = 1)
    (h : Commute (n * x * n) y) : Commute x (n * y * n) := by
  have hn' := invol_cancel hn
  have e : n * x * n * y = y * (n * x * n) := h.eq
  show x * (n * y * n) = n * y * n * x
  calc x * (n * y * n) = n * (n * x * n * y) * n := by simp only [mul_assoc, hn']
    _ = n * (y * (n * x * n)) * n := by rw [e]
    _ = n * y * n * x := by simp only [mul_assoc, hn, mul_one]

/-! ### Fans -/

/-- The fan as an element of the quotient. -/
def fan (n : ℕ) (c : Lab d n) : Q d lv (n + 1) := mk (fanW n c)

omit [Fact d.Prime] in
theorem fan_succ (n : ℕ) (c : Lab d (n + 1)) :
    fan (lv := lv) (n + 1) c = KQ n (fan n (Fin.tail c)) * qa n ^ (c 0).val := by
  simp only [fan, fanW, map_mul, map_pow, KQ_apply, shiftQ_mk]

theorem fan_zero : ∀ n : ℕ, fan (d := d) (lv := lv) n 0 = 1
  | 0 => map_one _
  | n + 1 => by
    rw [fan_succ, show Fin.tail (0 : Lab d (n + 1)) = 0 from rfl, fan_zero n, map_one, one_mul,
      Pi.zero_apply, ZMod.val_zero, pow_zero]

/-- The `CX` from wire `0` to wire `1` commutes with a fan one wire up. -/
theorem abar_fan : ∀ (n : ℕ) (t : Lab d n),
    Commute (qs n * qa (d := d) (lv := lv) n * qs n) (shiftQ (fan n t))
  | 0, t => by rw [show fan (d := d) (lv := lv) 0 t = 1 from map_one _, map_one]; exact
      Commute.one_right _
  | n + 1, t => by
    rw [fan_succ, map_mul, map_pow, KQ_apply, map_mul, map_mul]
    refine Commute.mul_right ?_ ((abar_comm_b n).pow_right _)
    apply commute_conj_invol (qs1_mul_self n)
    rw [abar_long n]
    have h1 := comm2Q (d := d) (lv := lv) Gate.SWAP (fan n (Fin.tail t))
    have h2 : Commute (shiftQ (qs n * qa (d := d) (lv := lv) n * qs n))
        (shiftQ (shiftQ (fan n (Fin.tail t)))) := (abar_fan n _).map shiftQ
    exact (h1.mul_left h2).mul_left h1

/-- `CX` commutes with the fan from the wires `2, 3, …`. -/
theorem qa_comm_KQfan (n : ℕ) (t : Lab d n) (k : ℕ) :
    Commute (qa (d := d) (lv := lv) n ^ k) (KQ n (fan n t)) := by
  refine Commute.pow_left ?_ k
  rw [KQ_apply]
  exact commute_conj_invol (qs_mul_self n) (abar_fan n t)

theorem fan_succ' (n : ℕ) (c : Lab d (n + 1)) :
    fan (lv := lv) (n + 1) c = qa n ^ (c 0).val * KQ n (fan n (Fin.tail c)) := by
  rw [fan_succ, (qa_comm_KQfan n _ _).eq]

/-- Fans add. -/
theorem fan_add : ∀ (n : ℕ) (c c' : Lab d n), fan (lv := lv) n c * fan n c' = fan n (c + c')
  | 0, c, c' => by simp only [fan, fanW, map_one, mul_one]
  | n + 1, c, c' => by
    rw [fan_succ, fan_succ, fan_succ]
    have hc := (qa_comm_KQfan (d := d) (lv := lv) n (Fin.tail c') (c 0).val).eq
    calc KQ n (fan n (Fin.tail c)) * qa n ^ (c 0).val *
          (KQ n (fan n (Fin.tail c')) * qa n ^ (c' 0).val)
        = KQ n (fan n (Fin.tail c)) * (qa n ^ (c 0).val * KQ n (fan n (Fin.tail c'))) *
          qa n ^ (c' 0).val := by group
      _ = KQ n (fan n (Fin.tail c) * fan n (Fin.tail c')) *
          (qa n ^ (c 0).val * qa n ^ (c' 0).val) := by rw [hc, map_mul]; group
      _ = _ := by rw [fan_add n, ← pow_val_add (qa_pow n)]; rfl

theorem fan_cons_zero (n : ℕ) (k : ZMod d) :
    fan (lv := lv) (n + 1) (Fin.cons k 0) = qa n ^ k.val := by
  rw [fan_succ, Fin.tail_cons, fan_zero, map_one, one_mul, Fin.cons_zero]

theorem fan_zero_cons (n : ℕ) (t : Lab d n) :
    fan (lv := lv) (n + 1) (Fin.cons 0 t) = KQ n (fan n t) := by
  rw [fan_succ, Fin.tail_cons, Fin.cons_zero, ZMod.val_zero, pow_zero, mul_one]

omit [Fact d.Prime] in
theorem fan_two (m : ℕ) (c : Lab d (m + 2)) :
    fan (lv := lv) (m + 2) c = KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) *
      qL m ^ (Fin.tail c 0).val * qa (m + 1) ^ (c 0).val := by
  rw [fan_succ, fan_succ, map_mul, map_pow, KQ_qa]

/-! ### A circuit one wire up passes a fan -/

/-- The statement that `u`, moved up one wire, passes every fan, changing
its labels by an invertible map. -/
def PassesFans {n : ℕ} (u : Q d lv n) : Prop :=
  ∃ φ : Lab d n → Lab d n, Function.Surjective φ ∧
    ∀ c, shiftQ u * fan n c = fan n (φ c) * shiftQ u

omit [Fact d.Prime] in
theorem PassesFans.one {n : ℕ} : PassesFans (1 : Q d lv n) :=
  ⟨id, Function.surjective_id, fun c => by simp⟩

omit [Fact d.Prime] in
theorem PassesFans.mul {n : ℕ} {u v : Q d lv n} (hu : PassesFans u) (hv : PassesFans v) :
    PassesFans (u * v) := by
  obtain ⟨φ, hφ, e⟩ := hu
  obtain ⟨ψ, hψ, f⟩ := hv
  refine ⟨φ ∘ ψ, hφ.comp hψ, fun c => ?_⟩
  rw [map_mul, mul_assoc, f, ← mul_assoc, e, mul_assoc]
  rfl

theorem passes_M (m : ℕ) (a : (ZMod d)ˣ) : PassesFans (qm (d := d) (lv := lv) m a) := by
  refine ⟨fun c => Fin.cons (((a⁻¹ : (ZMod d)ˣ) : ZMod d) * c 0) (Fin.tail c), ?_, fun c => ?_⟩
  · intro c'
    refine ⟨Fin.cons ((a : ZMod d) * c' 0) (Fin.tail c'), ?_⟩
    simp only [Fin.cons_zero, Fin.tail_cons, Units.inv_mul_cancel_left, Fin.cons_self_tail]
  · rw [fan_succ, fan_succ]
    simp only [Fin.tail_cons, Fin.cons_zero]
    rw [← mul_assoc, (qmt_comm_KQ a _).eq, mul_assoc, qmt_qa, mul_assoc]

theorem passes_SW (m : ℕ) : PassesFans (qs (d := d) (lv := lv) m) := by
  set φ : Lab d (m + 2) → Lab d (m + 2) := fun c =>
    Fin.cons (Fin.tail c 0) (Fin.cons (c 0) (Fin.tail (Fin.tail c)))
  have hφ : ∀ c, φ (φ c) = c := by
    intro c
    simp only [φ, Fin.cons_zero, Fin.tail_cons]
    conv_rhs => rw [← Fin.cons_self_tail c, ← Fin.cons_self_tail (Fin.tail c)]
  refine ⟨φ, fun c => ⟨φ c, hφ c⟩, fun c => ?_⟩
  have hs := qs_mul_self' (d := d) (lv := lv) (m + 1)
  have hs1 := qs1_mul_self' (d := d) (lv := lv) m
  have hy := yang_baxter (d := d) (lv := lv) m
  have h23 := lemma23 (d := d) (lv := lv) m
  have hs1s := qs1_mul_self (d := d) (lv := lv) m
  rw [fan_two, fan_two]
  simp only [φ, Fin.cons_zero, Fin.tail_cons]
  set s := qs (d := d) (lv := lv) (m + 1)
  set s1 := shiftQ (qs (d := d) (lv := lv) m)
  set a := qa (d := d) (lv := lv) (m + 1)
  set L := qL (d := d) (lv := lv) m
  have hLdef : L = s1 * a * s1 := rfl
  -- the crossing of the wires `1, 2` passes the fan from the wires `3, …`
  have hK : ∀ X : Q d lv (m + 1), s1 * KQ (m + 1) (KQ m X) = KQ (m + 1) (KQ m X) * s1 := by
    intro X
    have hY : Commute s (shiftQ (shiftQ X)) := comm2Q Gate.SWAP X
    have e : KQ (m + 1) (KQ m X) = s * s1 * shiftQ (shiftQ X) * s1 * s := by
      rw [KQ_apply, KQ_apply, map_mul, map_mul]; simp only [mul_assoc]; rfl
    rw [e]
    calc s1 * (s * s1 * shiftQ (shiftQ X) * s1 * s)
        = (s1 * s * s1) * shiftQ (shiftQ X) * s1 * s := by group
      _ = s * s1 * (s * shiftQ (shiftQ X)) * s1 * s := by rw [← hy]; group
      _ = s * s1 * shiftQ (shiftQ X) * (s * s1 * s) := by rw [hY.eq]; group
      _ = s * s1 * shiftQ (shiftQ X) * s1 * s * s1 := by rw [hy]; group
  have hL : ∀ K : ℕ, s1 * L ^ K = a ^ K * s1 := by
    intro K
    have : s1 * L = a * s1 := by rw [hLdef, ← mul_assoc, ← mul_assoc, hs1s, one_mul]
    calc s1 * L ^ K = (s1 * L * s1⁻¹) ^ K * s1 := by rw [conj_pow]; group
      _ = a ^ K * s1 := by rw [this, mul_inv_cancel_right]
  have ha : ∀ K : ℕ, s1 * a ^ K = L ^ K * s1 := by
    intro K
    have : s1 * a = L * s1 := by rw [hLdef, mul_assoc (s1 * a), hs1s, mul_one]
    calc s1 * a ^ K = (s1 * a * s1⁻¹) ^ K * s1 := by rw [conj_pow]; group
      _ = L ^ K * s1 := by rw [this, mul_inv_cancel_right]
  calc s1 * (KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) * L ^ (Fin.tail c 0).val *
        a ^ (c 0).val)
      = KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) * (s1 * L ^ (Fin.tail c 0).val) *
        a ^ (c 0).val := by rw [← mul_assoc, ← mul_assoc, hK]; group
    _ = KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) * a ^ (Fin.tail c 0).val *
        (s1 * a ^ (c 0).val) := by rw [hL]; group
    _ = KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) *
        (a ^ (Fin.tail c 0).val * L ^ (c 0).val) * s1 := by rw [ha]; group
    _ = _ := by rw [((h23.pow_left _).pow_right _).eq]; group

theorem passes_CX (m : ℕ) : PassesFans (qa (d := d) (lv := lv) m) := by
  refine ⟨fun c => Fin.cons (c 0) (Fin.cons (Fin.tail c 0 - c 0) (Fin.tail (Fin.tail c))),
    fun c' => ⟨Fin.cons (c' 0) (Fin.cons (Fin.tail c' 0 + c' 0) (Fin.tail (Fin.tail c'))), ?_⟩,
    fun c => ?_⟩
  · simp only [Fin.cons_zero, Fin.tail_cons, add_sub_cancel_right]
    conv_rhs => rw [← Fin.cons_self_tail c', ← Fin.cons_self_tail (Fin.tail c')]
  have hc := cyc_cx (d := d) (lv := lv) m
  have h23 := lemma23 (d := d) (lv := lv) m
  have h24 := lemma24 (d := d) (lv := lv) m
  have hst := steinberg_pow (d := d) (lv := lv) m
  have hp := qL_pow (d := d) (lv := lv) m
  rw [fan_two, fan_two]
  simp only [Fin.cons_zero, Fin.tail_cons]
  set s := qs (d := d) (lv := lv) (m + 1)
  set s1 := shiftQ (qs (d := d) (lv := lv) m)
  set a := qa (d := d) (lv := lv) (m + 1)
  set b := shiftQ (qa (d := d) (lv := lv) m)
  set L := qL (d := d) (lv := lv) m
  have hsi : s⁻¹ = s := qs_inv (m + 1)
  have hs1i : s1⁻¹ = s1 := qs1_inv m
  -- `b` passes the fan from the wires `3, …`
  have hK : ∀ X : Q d lv (m + 1), b * KQ (m + 1) (KQ m X) = KQ (m + 1) (KQ m X) * b := by
    intro X
    have hY : Commute a (shiftQ (shiftQ X)) := comm2Q Gate.CX X
    have e : KQ (m + 1) (KQ m X) = s * s1 * shiftQ (shiftQ X) * (s * s1)⁻¹ := by
      rw [KQ_apply, KQ_apply, map_mul, map_mul, mul_inv_rev, hsi, hs1i]; simp only [mul_assoc]
      rfl
    have hb : b * (s * s1) = s * s1 * a := by rw [hc]; group
    have hb' : (s * s1)⁻¹ * b = a * (s * s1)⁻¹ := by
      calc (s * s1)⁻¹ * b = (s * s1)⁻¹ * (b * (s * s1)) * (s * s1)⁻¹ := by group
        _ = a * (s * s1)⁻¹ := by rw [hb]; group
    rw [e]
    calc b * (s * s1 * shiftQ (shiftQ X) * (s * s1)⁻¹)
        = (b * (s * s1)) * shiftQ (shiftQ X) * (s * s1)⁻¹ := by group
      _ = s * s1 * (a * shiftQ (shiftQ X)) * (s * s1)⁻¹ := by rw [hb]; group
      _ = s * s1 * shiftQ (shiftQ X) * (a * (s * s1)⁻¹) := by rw [hY.eq]; group
      _ = s * s1 * shiftQ (shiftQ X) * ((s * s1)⁻¹ * b) := by rw [← hb']
      _ = _ := by group
  calc b * (KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) * L ^ (Fin.tail c 0).val *
        a ^ (c 0).val)
      = KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) * (b * L ^ (Fin.tail c 0).val) *
        a ^ (c 0).val := by rw [← mul_assoc, ← mul_assoc, hK]; group
    _ = KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) * L ^ (Fin.tail c 0).val *
        (b * a ^ (c 0).val) := by rw [(h24.pow_right _).eq]; group
    _ = KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) * L ^ (Fin.tail c 0).val *
        (a ^ (c 0).val * L ^ (-(c 0)).val) * b := by
        rw [hst, mul_assoc _ b, (h24.pow_right _).eq]; group
    _ = KQ (m + 1) (KQ m (fan m (Fin.tail (Fin.tail c)))) *
        (L ^ (Fin.tail c 0).val * L ^ (-(c 0)).val) * a ^ (c 0).val * b := by
        rw [((h23.pow_left _).pow_right _).eq]; group
    _ = _ := by rw [← pow_val_add hp, ← sub_eq_add_neg]

omit [Fact d.Prime] in
theorem passes_up {m : ℕ} {u : Q d lv m} (hu : PassesFans u) : PassesFans (shiftQ u) := by
  obtain ⟨φ, hφ, e⟩ := hu
  refine ⟨fun c => Fin.cons (c 0) (φ (Fin.tail c)), fun c' => ?_, fun c => ?_⟩
  · obtain ⟨t, ht⟩ := hφ (Fin.tail c')
    refine ⟨Fin.cons (c' 0) t, ?_⟩
    simp only [Fin.cons_zero, Fin.tail_cons, ht, Fin.cons_self_tail]
  · rw [fan_succ, fan_succ]
    simp only [Fin.tail_cons, Fin.cons_zero]
    have h1 : shiftQ (shiftQ u) * KQ m (fan m (Fin.tail c)) =
        KQ m (fan m (φ (Fin.tail c))) * shiftQ (shiftQ u) := by
      rw [← KQ_shiftQ, ← map_mul, e, map_mul]
    have h2 : Commute (qa (d := d) (lv := lv) m ^ (c 0).val) (shiftQ (shiftQ u)) :=
      (comm2Q Gate.CX u).pow_left _
    rw [← mul_assoc, h1, mul_assoc, ← h2.eq, mul_assoc]

/-- Every linear generator, moved up one wire, passes the fans. -/
theorem passes_gen : ∀ {n : ℕ} (x : Gen (Gate d lv) n), x.IsLin →
    PassesFans (mk (FreeMonoid.of x))
  | _, .gate0 _, hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 .X, hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 (.M a), _ => passes_M _ a
  | _, .gate1 (.Z _), hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 (.S _), hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 (.T _), hx => absurd hx (by simp [Gen.IsLin])
  | _, .gate2 .CX, _ => passes_CX _
  | _, .gate2 .SWAP, _ => passes_SW _
  | _, .gate3 g, _ => nomatch g
  | _, .up g, hx => by
    rw [← shift_of, ← shiftQ_mk]
    exact passes_up (passes_gen g hx)

/-- Every linear circuit, moved up one wire, passes the fans. -/
theorem passes_word {n : ℕ} (u : C d lv n) (hu : IsLinW u) : PassesFans (mk u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact PassesFans.one
  | mul_of x w ih =>
    obtain ⟨hx, hw⟩ := IsLinW.of_mul hu
    rw [map_mul]
    exact (passes_gen x hx).mul (ih hw)

/-! ### The subgroup `H` -/

/-- The elements of the form `F(c) ↑B` with `B` linear: the stabiliser of
`e₀`. -/
def InH {n : ℕ} (h : Q d lv (n + 1)) : Prop :=
  ∃ (c : Lab d n) (u : C d lv n), IsLinW u ∧ h = fan n c * shiftQ (mk u)

theorem inH_one {n : ℕ} : InH (1 : Q d lv (n + 1)) :=
  ⟨0, 1, IsLinW.one, by rw [fan_zero, map_one, map_one, one_mul]⟩

omit [Fact d.Prime] in
theorem inH_fan {n : ℕ} (c : Lab d n) : InH (fan (lv := lv) n c) :=
  ⟨c, 1, IsLinW.one, by rw [map_one, map_one, mul_one]⟩

theorem inH_shift {n : ℕ} (u : C d lv n) (hu : IsLinW u) : InH (shiftQ (mk u)) :=
  ⟨0, u, hu, by rw [fan_zero, one_mul]⟩

theorem InH.mul {n : ℕ} {h h' : Q d lv (n + 1)} (hh : InH h) (hh' : InH h') : InH (h * h') := by
  obtain ⟨c, u, hu, rfl⟩ := hh
  obtain ⟨c', u', hu', rfl⟩ := hh'
  obtain ⟨φ, -, e⟩ := passes_word u hu
  refine ⟨c + φ c', u * u', hu.mul hu', ?_⟩
  rw [map_mul, map_mul, ← fan_add]
  calc fan n c * shiftQ (mk u) * (fan n c' * shiftQ (mk u'))
      = fan n c * (shiftQ (mk u) * fan n c') * shiftQ (mk u') := by group
    _ = _ := by rw [e]; group

/-! ### Stairs -/

/-- The stair as an element of the quotient. -/
def stair (n : ℕ) (v : Lab d (n + 1)) : Q d lv (n + 1) := mk (stairW n v)

theorem stair_of_tail : ∀ (n : ℕ) (v : Lab d (n + 1)), Fin.tail v = 0 →
    stair (lv := lv) n v = qm n (unitOf (v 0))
  | 0, _, _ => rfl
  | n + 1, v, h => by simp only [stair, stairW, h, if_true]

theorem stair_succ (n : ℕ) (v : Lab d (n + 2)) (h : Fin.tail v ≠ 0) :
    stair (lv := lv) (n + 1) v = shiftQ (stair n (Fin.tail v)) * qa n ^ (v 0).val * qs n := by
  simp only [stair, stairW, h, if_false, map_mul, map_pow, shiftQ_mk]

theorem stair_e0 (n : ℕ) : stair (d := d) (lv := lv) n (Fin.cons 1 0) = 1 := by
  rw [stair_of_tail n _ (Fin.tail_cons _ _), Fin.cons_zero, unitOf_one, qm_one]

theorem tail_ne_zero_of {n : ℕ} {v : Lab d (n + 1)} (hv : v ≠ 0) (h : Fin.tail v = 0) :
    v 0 ≠ 0 := by
  intro h0
  apply hv
  rw [← Fin.cons_self_tail v, h, h0]
  ext i; refine Fin.cases rfl (fun j => rfl) i

/-! ### The table -/

/-- The table of the rewriting: a linear generator applied to a stair is a
stair followed by an element of `H`. -/
def Row {n : ℕ} (g : Q d lv (n + 1)) (v : Lab d (n + 1)) : Prop :=
  ∃ (w : Lab d (n + 1)) (h : Q d lv (n + 1)), w ≠ 0 ∧ InH h ∧ g * stair n v = stair n w * h

theorem cons_ne_zero {n : ℕ} {x : ZMod d} {t : Lab d n} (h : t ≠ 0) :
    (Fin.cons x t : Lab d (n + 1)) ≠ 0 := by
  intro e; apply h
  have := congrArg Fin.tail e
  simpa using this

theorem cons_ne_zero' {n : ℕ} {x : ZMod d} (h : x ≠ 0) (t : Lab d n) :
    (Fin.cons x t : Lab d (n + 1)) ≠ 0 := by
  intro e; apply h
  have := congrFun e 0
  simpa using this

/-- `M_x` on wire `0`. -/
theorem row_M (n : ℕ) (a : (ZMod d)ˣ) (v : Lab d (n + 1)) (hv : v ≠ 0) :
    Row (qm (lv := lv) n a) v := by
  by_cases ht : Fin.tail v = 0
  · have h0 := tail_ne_zero_of hv ht
    refine ⟨Fin.cons ((a : ZMod d) * v 0) 0, 1,
      cons_ne_zero' (mul_ne_zero a.ne_zero h0) 0, inH_one, ?_⟩
    rw [stair_of_tail n v ht, stair_of_tail n _ (Fin.tail_cons _ _), Fin.cons_zero, mul_one,
      qm_mul]
    congr 1
    ext; rw [unitOf_val (mul_ne_zero a.ne_zero h0), Units.val_mul, unitOf_val h0, mul_comm]
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
      cases n with
      | zero => exact absurd (Subsingleton.elim _ _) ht
      | succ n' => exact ⟨n', rfl⟩
    refine ⟨Fin.cons ((a : ZMod d) * v 0) (Fin.tail v), shiftQ (qm n' a),
      cons_ne_zero ht, inH_shift _ (isLinW_M a), ?_⟩
    rw [stair_succ n' v ht, stair_succ n' _ (by rwa [Fin.tail_cons]), Fin.tail_cons,
      Fin.cons_zero]
    have h1 : Commute (qm (d := d) (lv := lv) (n' + 1) a) (shiftQ (stair n' (Fin.tail v))) :=
      comm1Q _ _
    calc qm (n' + 1) a * (shiftQ (stair n' (Fin.tail v)) * qa n' ^ (v 0).val * qs n')
        = shiftQ (stair n' (Fin.tail v)) * (qm (n' + 1) a * qa n' ^ (v 0).val) * qs n' := by
          rw [← mul_assoc, ← mul_assoc, h1.eq]; group
      _ = shiftQ (stair n' (Fin.tail v)) * qa n' ^ ((a : ZMod d) * v 0).val *
          (qm (n' + 1) a * qs n') := by rw [qm_qa]; group
      _ = _ := by rw [(qs_qmt n' a).symm]; group

/-- `CX` on the wires `1 → 0`. -/
theorem row_CX (n : ℕ) (v : Lab d (n + 2)) (hv : v ≠ 0) : Row (qa (lv := lv) n) v := by
  by_cases ht : Fin.tail v = 0
  · have h0 := tail_ne_zero_of hv ht
    refine ⟨v, qa n ^ ((((unitOf (v 0))⁻¹ : (ZMod d)ˣ) : ZMod d)).val, hv, ?_, ?_⟩
    · rw [← fan_cons_zero]; exact inH_fan _
    · rw [stair_of_tail (n + 1) v ht]
      have e := qm_qa (d := d) (lv := lv) n (unitOf (v 0))
        (((unitOf (v 0))⁻¹ : (ZMod d)ˣ) : ZMod d)
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, val_one_zmod, pow_one] at e
      exact e.symm
  · obtain ⟨φ, hφ, e⟩ := passes_word (stairW (lv := lv) n (Fin.tail v)) (isLinW_stairW _ _)
    obtain ⟨c, hc⟩ := hφ (Fin.cons 1 0)
    have h1 : qa (d := d) (lv := lv) n * shiftQ (stair n (Fin.tail v)) =
        shiftQ (stair n (Fin.tail v)) * fan (n + 1) c := by
      have := e c
      rw [hc, fan_cons_zero, val_one_zmod, pow_one] at this
      exact this.symm
    refine ⟨Fin.cons ((c + (Fin.cons (v 0) 0 : Lab d (n + 1))) 0) (Fin.tail v),
      shiftQ (fan n (Fin.tail (c + (Fin.cons (v 0) 0 : Lab d (n + 1))))), cons_ne_zero ht,
      inH_shift _ (isLinW_fanW _ _), ?_⟩
    rw [stair_succ n v ht, stair_succ n _ (by rwa [Fin.tail_cons]), Fin.tail_cons,
      Fin.cons_zero]
    calc qa n * (shiftQ (stair n (Fin.tail v)) * qa n ^ (v 0).val * qs n)
        = shiftQ (stair n (Fin.tail v)) * fan (n + 1) c * fan (n + 1) (Fin.cons (v 0) 0) *
          qs n := by rw [fan_cons_zero]; simp only [← mul_assoc]; rw [h1]
      _ = shiftQ (stair n (Fin.tail v)) * qa n ^ ((c + (Fin.cons (v 0) 0 : Lab d (n + 1))) 0).val *
          (KQ n (fan n (Fin.tail (c + (Fin.cons (v 0) 0 : Lab d (n + 1))))) * qs n) := by
          rw [mul_assoc _ (fan (n + 1) c), fan_add, fan_succ']; group
      _ = _ := by rw [KQ_mul_qs]; group

/-- The crossing of the wires `0, 1`. -/
theorem row_SW (n : ℕ) (v : Lab d (n + 2)) (hv : v ≠ 0) : Row (qs (lv := lv) n) v := by
  by_cases ht : Fin.tail v = 0
  · -- `s M_u = ↑M_u s`, the stair of `(0, u, 0, …)`
    have h0 := tail_ne_zero_of hv ht
    refine ⟨Fin.cons 0 (Fin.cons (v 0) 0), 1,
      cons_ne_zero (cons_ne_zero' h0 0), inH_one, ?_⟩
    have hw : Fin.tail (Fin.cons 0 (Fin.cons (v 0) 0) : Lab d (n + 2)) ≠ 0 := by
      rw [Fin.tail_cons]; exact cons_ne_zero' h0 0
    rw [stair_of_tail (n + 1) v ht, stair_succ n _ hw, Fin.tail_cons,
      stair_of_tail n _ (Fin.tail_cons _ _)]
    simp only [Fin.cons_zero, ZMod.val_zero, pow_zero, mul_one]
    exact qs_qm n _
  by_cases htt : Fin.tail (Fin.tail v) = 0
  · -- the stair one wire up is a multiplier
    have h1 := tail_ne_zero_of ht htt
    have hγ : ((unitOf (Fin.tail v 0) : (ZMod d)ˣ) : ZMod d) = Fin.tail v 0 := unitOf_val h1
    have hS : stair (lv := lv) (n + 1) v =
        shiftQ (qm n (unitOf (Fin.tail v 0))) * qa n ^ (v 0).val * qs n := by
      rw [stair_succ n v ht, stair_of_tail n _ htt]
    by_cases h0 : v 0 = 0
    · refine ⟨Fin.cons (Fin.tail v 0) 0, 1, cons_ne_zero' h1 0, inH_one, ?_⟩
      rw [hS, stair_of_tail (n + 1) _ (Fin.tail_cons _ _)]
      simp only [Fin.cons_zero, h0, ZMod.val_zero, pow_zero, mul_one]
      rw [← mul_assoc, qs_qmt, mul_assoc, qs_mul_self, mul_one]
    · have hα : ((unitOf (v 0) : (ZMod d)ˣ) : ZMod d) = v 0 := unitOf_val h0
      have e := bruhat (d := d) (lv := lv) n (unitOf (v 0)) (unitOf (Fin.tail v 0))
      rw [hα, hγ] at e
      refine ⟨Fin.cons (Fin.tail v 0) (Fin.cons (v 0) 0),
        qa n ^ (-(Fin.tail v 0)⁻¹).val *
          shiftQ (qm n (-(unitOf (Fin.tail v 0) * (unitOf (v 0))⁻¹))),
        cons_ne_zero (cons_ne_zero' h0 0),
        ⟨Fin.cons (-(Fin.tail v 0)⁻¹) 0,
          g1 (Gate.M (-(unitOf (Fin.tail v 0) * (unitOf (v 0))⁻¹))), isLinW_M _, ?_⟩, ?_⟩
      · rw [fan_cons_zero]
      · rw [hS, stair_succ n _ (by rw [Fin.tail_cons]; exact cons_ne_zero' h0 0),
          Fin.tail_cons, stair_of_tail n _ (Fin.tail_cons _ _), Fin.cons_zero, Fin.cons_zero]
        exact e
  · -- two stairs: the lower two steps exchange
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
      cases n with
      | zero => exact absurd (Subsingleton.elim _ _) htt
      | succ n' => exact ⟨n', rfl⟩
    have e := stair_swap (d := d) (lv := lv) n' (v 0) (Fin.tail v 0)
    refine ⟨Fin.cons (Fin.tail v 0) (Fin.cons (v 0) (Fin.tail (Fin.tail v))), shiftQ (qs n'),
      cons_ne_zero (cons_ne_zero htt), inH_shift _ (isLinW_g2 _), ?_⟩
    rw [stair_succ (n' + 1) v ht, stair_succ n' (Fin.tail v) htt,
      stair_succ (n' + 1) _ (by rw [Fin.tail_cons]; exact cons_ne_zero htt), Fin.tail_cons,
      stair_succ n' _ (by rw [Fin.tail_cons]; exact htt), Fin.tail_cons, Fin.cons_zero,
      Fin.cons_zero]
    have hc : Commute (qs (d := d) (lv := lv) (n' + 1))
        (shiftQ (shiftQ (stair n' (Fin.tail (Fin.tail v))))) := comm2Q _ _
    simp only [map_mul, map_pow]
    calc qs (n' + 1) * (shiftQ (shiftQ (stair n' (Fin.tail (Fin.tail v)))) *
          shiftQ (qa n') ^ (Fin.tail v 0).val * shiftQ (qs n') * qa (n' + 1) ^ (v 0).val *
          qs (n' + 1))
        = shiftQ (shiftQ (stair n' (Fin.tail (Fin.tail v)))) * (qs (n' + 1) *
          (shiftQ (qa n') ^ (Fin.tail v 0).val * shiftQ (qs n') * qa (n' + 1) ^ (v 0).val *
          qs (n' + 1))) := by simp only [← mul_assoc]; rw [hc.eq]
      _ = _ := by rw [e]; group

/-- A generator one wire up. -/
theorem row_up (n : ℕ) (g : Gen (Gate d lv) (n + 1)) (hg : g.IsLin)
    (ih : ∀ v : Lab d (n + 1), v ≠ 0 → Row (mk (FreeMonoid.of g)) v)
    (v : Lab d (n + 2)) (hv : v ≠ 0) : Row (shiftQ (mk (FreeMonoid.of g))) v := by
  by_cases ht : Fin.tail v = 0
  · refine ⟨v, shiftQ (mk (FreeMonoid.of g)), hv, inH_shift _ (IsLinW.of hg), ?_⟩
    rw [stair_of_tail (n + 1) v ht]
    exact (comm1Q (Gate.M _) _).eq.symm
  obtain ⟨w', h', hw', ⟨c, u', hu', rfl⟩, e⟩ := ih (Fin.tail v) ht
  obtain ⟨φ, -, ef⟩ := passes_word (fanW (lv := lv) n c) (isLinW_fanW _ _)
  refine ⟨Fin.cons (φ (Fin.cons (v 0) 0) 0) w',
    shiftQ (fan n (Fin.tail (φ (Fin.cons (v 0) 0)))) * KQ n (fan n c) * shiftQ (shiftQ (mk u')),
    cons_ne_zero hw', ((inH_shift _ (isLinW_fanW _ _)).mul ?_).mul ?_, ?_⟩
  · rw [← fan_zero_cons]; exact inH_fan _
  · rw [shiftQ_mk]; exact inH_shift _ (isLinW_shift hu')
  rw [stair_succ n v ht, stair_succ n _ (by rwa [Fin.tail_cons]), Fin.tail_cons, Fin.cons_zero]
  have h1 : shiftQ (fan (lv := lv) n c) * qa n ^ (v 0).val =
      qa n ^ (φ (Fin.cons (v 0) 0) 0).val * KQ n (fan n (Fin.tail (φ (Fin.cons (v 0) 0)))) *
        shiftQ (fan n c) := by
    have := ef (Fin.cons (v 0) 0)
    rw [fan_cons_zero, fan_succ'] at this
    exact this
  have h2 : Commute (shiftQ (shiftQ (mk u'))) (qa (d := d) (lv := lv) n ^ (v 0).val * qs n) :=
    (((comm2Q Gate.CX (mk u')).pow_left _).mul_left (comm2Q Gate.SWAP (mk u'))).symm
  have h3 : shiftQ (fan (lv := lv) n c) * qs n = qs n * KQ n (fan n c) := by
    rw [KQ_apply, ← mul_assoc, ← mul_assoc, qs_mul_self, one_mul]
  have e' := congrArg shiftQ e
  simp only [map_mul] at e'
  calc shiftQ (mk (FreeMonoid.of g)) * (shiftQ (stair n (Fin.tail v)) * qa n ^ (v 0).val *
        qs n)
      = shiftQ (stair n w') * shiftQ (fan n c) * (shiftQ (shiftQ (mk u')) *
        (qa n ^ (v 0).val * qs n)) := by simp only [← mul_assoc]; rw [e']; group
    _ = shiftQ (stair n w') * (shiftQ (fan n c) * qa n ^ (v 0).val) * qs n *
        shiftQ (shiftQ (mk u')) := by rw [h2.eq]; group
    _ = shiftQ (stair n w') * qa n ^ (φ (Fin.cons (v 0) 0) 0).val *
        (KQ n (fan n (Fin.tail (φ (Fin.cons (v 0) 0)))) * (shiftQ (fan n c) * qs n)) *
        shiftQ (shiftQ (mk u')) := by rw [h1]; group
    _ = shiftQ (stair n w') * qa n ^ (φ (Fin.cons (v 0) 0) 0).val *
        (KQ n (fan n (Fin.tail (φ (Fin.cons (v 0) 0)))) * qs n) * KQ n (fan n c) *
        shiftQ (shiftQ (mk u')) := by rw [h3]; group
    _ = _ := by rw [KQ_mul_qs]; group

/-- The table: a linear generator applied to a stair is a stair followed by
an element of `H`. -/
theorem table : ∀ (n : ℕ) (x : Gen (Gate d lv) (n + 1)), x.IsLin → ∀ v : Lab d (n + 1),
    v ≠ 0 → Row (mk (FreeMonoid.of x)) v
  | _, .gate0 _, hx, _, _ => absurd hx (by simp [Gen.IsLin])
  | n, .gate1 (.M a), _, v, hv => row_M n a v hv
  | _, .gate1 .X, hx, _, _ => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 (.Z _), hx, _, _ => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 (.S _), hx, _, _ => absurd hx (by simp [Gen.IsLin])
  | _, .gate1 (.T _), hx, _, _ => absurd hx (by simp [Gen.IsLin])
  | _, .gate2 .CX, _, v, hv => row_CX _ v hv
  | _, .gate2 .SWAP, _, v, hv => row_SW _ v hv
  | _, .gate3 g, _, _, _ => nomatch g
  | 0, .up (.gate0 _), hx, _, _ => absurd hx (by simp [Gen.IsLin])
  | n + 1, .up g, hx, v, hv => by
    rw [← shift_of, ← shiftQ_mk]
    exact row_up n g hx (fun w hw => table n g hx w hw) v hv

/-- Every linear circuit is a stair followed by an element of `H`. -/
theorem decompose (n : ℕ) (w : C d lv (n + 1)) (hw : IsLinW w) :
    ∃ (v : Lab d (n + 1)) (h : Q d lv (n + 1)), v ≠ 0 ∧ InH h ∧ mk w = stair n v * h := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨Fin.cons 1 0, 1, cons_ne_zero' one_ne_zero 0, inH_one,
      by rw [stair_e0, map_one, mul_one]⟩
  | mul_of x w ih =>
    obtain ⟨hx, hw'⟩ := IsLinW.of_mul hw
    obtain ⟨v, h, hv, hh, e⟩ := ih hw'
    obtain ⟨v', h', hv', hh', e'⟩ := table n x hx v hv
    exact ⟨v', h' * h, hv', hh'.mul hh, by rw [map_mul, e, ← mul_assoc, e', mul_assoc]⟩


end Group

end QCert.PhaseAffine
