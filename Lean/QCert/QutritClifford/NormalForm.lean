/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Normal forms of qutrit Clifford circuits (§3)

The normal boxes `A`–`F` of Figure 9, their actions on Pauli operators
(Figure 8, both columns, decided on Pauli data), the `Z`-normal and
`X`-normal circuits of Figure 10 and the normal form of Figure 11
(Definitions 3.2 and 3.3).  The `Z`- and `X`-normal circuits are data
(`ZN`, `XN`) read as circuits; each carries the Pauli operator that it
sends to `Z` on the top wire, resp. `X` on the bottom wire (`ZN.pre`,
`XN.pre`), which determines it.  This is Lemmas 3.5–3.7 (`ZN.act_pre`,
`ZN.exists_pre`, `ZN.pre_injective`, `XN.act_pre`, `XN.exists_pre`,
`XN.pre_injective`, `XN.act_Ztop`).

**Wires.** The paper's top qutrit is our top wire; our wire `0` is its
bottom qutrit.  The `Z`-normal circuit puts its `A` box on the lowest
non-trivial wire of the Pauli and its ladder of `B` boxes goes up to the
`C` box on the top wire; the `X`-normal circuit's ladder of `D` boxes goes
down from the top pair of wires to the bottom pair, and its `E` and `F`
boxes act on wire `0`.  On a pair of wires a box's top wire is wire `1`.
-/
import QCert.QutritClifford.PauliAction

namespace QCert.QutritClifford

open Matrix

/-! ### Pauli data by wires -/

namespace PD

variable {n : ℕ}

/-- Pauli data with the factor `X^{a₀} Z^{b₀}` on a new bottom wire. -/
def cons (a0 b0 : Fin 3) (P : PD n) : PD (n + 1) := ⟨P.c, Fin.cons a0 P.a, Fin.cons b0 P.b⟩

/-- The data on the wires above the bottom one. -/
def tl (P : PD (n + 1)) : PD n := ⟨P.c, Fin.tail P.a, Fin.tail P.b⟩

/-- Data on no wires: the scalar `ω^c`. -/
def nil (c : Fin 3) : PD 0 := ⟨c, ![], ![]⟩

/-- A scalar. -/
def sc (c : Fin 3) : PD n := ⟨c, 0, 0⟩

@[simp] theorem cons_c (a0 b0 : Fin 3) (P : PD n) : (P.cons a0 b0).c = P.c := rfl

theorem cons_tl (P : PD (n + 1)) : P.tl.cons (P.a 0) (P.b 0) = P := by
  cases P
  simp only [cons, tl, Fin.cons_self_tail]

theorem cons_inj {a0 b0 a0' b0' : Fin 3} {P P' : PD n} (h : P.cons a0 b0 = P'.cons a0' b0') :
    a0 = a0' ∧ b0 = b0' ∧ P = P' := by
  simp only [cons, PD.mk.injEq] at h
  obtain ⟨hc, ha, hb⟩ := h
  obtain ⟨ha0, ha⟩ := Fin.cons_injective2 ha
  obtain ⟨hb0, hb⟩ := Fin.cons_injective2 hb
  exact ⟨ha0, hb0, PD.ext hc ha hb⟩

theorem cons_sc (c : Fin 3) : (sc c : PD n).cons 0 0 = sc c := by
  simp only [cons, sc, PD.mk.injEq, true_and]
  constructor <;> funext i <;> refine Fin.cases rfl (fun j => rfl) i

theorem eq_nil (P : PD 0) : P = nil P.c := PD.ext rfl (funext fun x => x.elim0) (funext fun x => x.elim0)

theorem scale_cons (d a0 b0 : Fin 3) (P : PD n) :
    scale d (P.cons a0 b0) = (scale d P).cons a0 b0 := rfl

theorem scale_zero (P : PD n) : scale 0 P = P := by
  simp [scale]

theorem scale_scale (d e : Fin 3) (P : PD n) : scale d (scale e P) = scale (d + e) P := by
  simp [scale, add_assoc]

end PD

/-! ### The wire splits of the framework, on `cons` data -/

theorem split1_fst {n : ℕ} (a0 : Fin 3) (x : Fin n → Fin 3) :
    (split 3 n 1 (Fin.cons a0 x : Fin (n + 1) → Fin 3)).1 = ![a0] := by
  funext i
  rw [Subsingleton.elim i 0]
  rfl

theorem split1_snd {n : ℕ} (a0 : Fin 3) (x : Fin n → Fin 3) :
    (split 3 n 1 (Fin.cons a0 x : Fin (n + 1) → Fin 3)).2 = x := by
  funext j
  show (Fin.cons a0 x : Fin (n + 1) → Fin 3) ⟨1 + j, _⟩ = x j
  rw [show (⟨1 + j, by omega⟩ : Fin (n + 1)) = j.succ from Fin.ext (by simp [Nat.add_comm]),
    Fin.cons_succ]

theorem split1_symm {n : ℕ} (lo : Fin 1 → Fin 3) (hi : Fin n → Fin 3) :
    (split 3 n 1).symm (lo, hi) = Fin.cons (lo 0) hi := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [split]
  · simp only [split, Equiv.coe_fn_symm_mk, Fin.val_succ, Fin.cons_succ]
    rw [dif_neg (by omega)]
    exact congrArg hi (Fin.ext (by simp))

theorem split2_fst {n : ℕ} (a0 a1 : Fin 3) (x : Fin n → Fin 3) :
    (split 3 n 2 (Fin.cons a0 (Fin.cons a1 x) : Fin (n + 2) → Fin 3)).1 = ![a0, a1] := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  rw [Subsingleton.elim j 0]
  rfl

theorem split2_snd {n : ℕ} (a0 a1 : Fin 3) (x : Fin n → Fin 3) :
    (split 3 n 2 (Fin.cons a0 (Fin.cons a1 x) : Fin (n + 2) → Fin 3)).2 = x := by
  funext j
  show (Fin.cons a0 (Fin.cons a1 x) : Fin (n + 2) → Fin 3) ⟨2 + j, _⟩ = x j
  rw [show (⟨2 + j, by omega⟩ : Fin (n + 2)) = j.succ.succ from Fin.ext (by simp; omega),
    Fin.cons_succ, Fin.cons_succ]

theorem split2_symm {n : ℕ} (lo : Fin 2 → Fin 3) (hi : Fin n → Fin 3) :
    (split 3 n 2).symm (lo, hi) = Fin.cons (lo 0) (Fin.cons (lo 1) hi) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
  · simp [split]
  · simp only [split, Equiv.coe_fn_symm_mk, Fin.val_succ, Fin.val_zero, Fin.cons_succ,
      Fin.cons_zero]
    rw [dif_pos (by omega)]
    rfl
  · simp only [split, Equiv.coe_fn_symm_mk, Fin.val_succ, Fin.cons_succ]
    rw [dif_neg (by omega)]
    exact congrArg hi (Fin.ext (by simp))

/-! ### Placing circuits -/

theorem actC_mul {n : ℕ} (x y : Circ n) (P : PD n) :
    actC n (x * y) P = actC n x (actC n y P) := by
  rw [map_mul]; rfl

theorem actC_seq {n : ℕ} (x y : Circ n) (P : PD n) :
    actC n (x ⨾ y) P = actC n y (actC n x P) := actC_mul y x P

theorem actC_one {n : ℕ} (P : PD n) : actC n 1 P = P := by
  rw [map_one]; rfl

/-- A circuit moved up leaves the bottom wire alone. -/
theorem actC_top {n : ℕ} (w : Circ n) (a0 b0 : Fin 3) (P : PD n) :
    actC (n + 1) (top w) (P.cons a0 b0) = (actC n w P).cons a0 b0 := by
  apply PD.op_inj
  rw [← sem_conj, show ((sem (n + 1) (top w) : unitaryGroup (State 3 (n + 1)) ℂ) :
      Op ℂ 3 (n + 1)) = onTop 1 (sem n w : Op ℂ 3 n) from
      congrArg Subtype.val (gateSem.sem_shift w), conj_onTop (sem_conj w)]
  congr 1
  simp only [embedHi, PD.cons, split1_fst, split1_snd, split1_symm]
  rfl

/-- A one-wire circuit on the bottom wire. -/
theorem actC_bot {n : ℕ} (w : Circ 1) (a0 b0 : Fin 3) (P : PD n) {r : PD 1}
    (hr : actC 1 w ⟨0, ![a0], ![b0]⟩ = r) :
    actC (n + 1) (bot w) (P.cons a0 b0) = PD.scale r.c (P.cons (r.a 0) (r.b 0)) := by
  apply PD.op_inj
  rw [← sem_conj, show ((sem (n + 1) (bot w) : unitaryGroup (State 3 (n + 1)) ℂ) :
      Op ℂ 3 (n + 1)) = onBottom (n := n) (sem 1 w : Op ℂ 3 1) from
      congrArg Subtype.val (gateSem.sem_pad n w), conj_onBottom (sem_conj w)]
  congr 1
  simp only [embedLo, PD.cons, split1_fst, split1_snd, split1_symm, hr]
  rfl

/-- A two-wire circuit on the bottom two wires. -/
theorem actC_bot2 {n : ℕ} (w : Circ 2) (a0 b0 a1 b1 : Fin 3) (P : PD n) {r : PD 2}
    (hr : actC 2 w ⟨0, ![a0, a1], ![b0, b1]⟩ = r) :
    actC (n + 2) (bot2 w) ((P.cons a1 b1).cons a0 b0) =
      PD.scale r.c ((P.cons (r.a 1) (r.b 1)).cons (r.a 0) (r.b 0)) := by
  apply PD.op_inj
  rw [← sem_conj, show ((sem (n + 2) (bot2 w) : unitaryGroup (State 3 (n + 2)) ℂ) :
      Op ℂ 3 (n + 2)) = onBottom (n := n) (sem 2 w : Op ℂ 3 2) from
      congrArg Subtype.val (gateSem.sem_pad n w), conj_onBottom (sem_conj w)]
  congr 1
  simp only [embedLo, PD.cons, split2_fst, split2_snd, split2_symm, hr]
  rfl

/-! ### The normal boxes (Figure 9) -/

/-- `A_{ab}`, `(a, b) ≠ (0, 0)`: `A₀₁ = 1`, `A₀₂ = H²`, `A_{1b} = S^b ⨾ H`,
`A_{2b} = H² ⨾ S^{2b} ⨾ H`. -/
def Abox (a b : Fin 3) : Circ 1 :=
  if a = 0 then (if b = 1 then 1 else H ^ 2)
  else if a = 1 then S ^ (b : ℕ) ⨾ H
  else H ^ 2 ⨾ S ^ (2 * (b : ℕ)) ⨾ H

/-- `B₀₁`: the swap, `CZ` twice and `XC`. -/
def B01 : Circ 2 := SWAP ⨾ CZ ⨾ CZ ⨾ XC

/-- `B_{ab}`: `B₀₀ = SWAP ⨾ CZ`, `B₀₁`, `B₀₂ = A₀₂ ⨾ CZ ⨾ B₀₁` and, for
`a ≠ 0`, `B_{ab} = A_{ab} ⨾ CZ ⨾ CZ ⨾ B₀₁`, the `A` box on the top wire. -/
def Bbox (a b : Fin 3) : Circ 2 :=
  if a = 0 then
    (if b = 0 then SWAP ⨾ CZ else if b = 1 then B01 else top (Abox 0 2) ⨾ CZ ⨾ B01)
  else top (Abox a b) ⨾ CZ ⨾ CZ ⨾ B01

/-- `C_b = X^b`. -/
def Cbox (b : Fin 3) : Circ 1 := X ^ (b : ℕ)

/-- `D_{ab}`: `D_{0b} = SWAP ⨾ CZ^{2b}` and, for `a ≠ 0`,
`D_{ab} = A_{ab} ⨾ D₀₁`, the `A` box on the bottom wire. -/
def Dbox (a b : Fin 3) : Circ 2 :=
  if a = 0 then SWAP ⨾ CZ ^ (2 * (b : ℕ)) else bot (Abox a b) ⨾ (SWAP ⨾ CZ ^ 2)

/-- `E_b = S^b`. -/
def Ebox (b : Fin 3) : Circ 1 := S ^ (b : ℕ)

/-- `F_b = Z^{2b}`. -/
def Fbox (b : Fin 3) : Circ 1 := Z ^ (2 * (b : ℕ))

/-! ### Their actions (Figure 8), decided on Pauli data

On a pair of wires the first entry of a vector is wire `0`, the paper's
lower wire. -/

/-- `A_{ab} : X^a Z^b ↦ Z`. -/
theorem A_act : ∀ a b : Fin 3, (a, b) ≠ (0, 0) →
    actC 1 (Abox a b) ⟨0, ![a], ![b]⟩ = ⟨0, ![0], ![1]⟩ := by decide +kernel

/-- `B_{ab} : X^a Z^b ⊗ Z ↦ Z ⊗ I`. -/
theorem B_act : ∀ a b : Fin 3,
    actC 2 (Bbox a b) ⟨0, ![0, a], ![1, b]⟩ = ⟨0, ![0, 0], ![0, 1]⟩ := by decide +kernel

/-- `B_{ab} : ω^{ab} X^{2a} Z^{2b + a² - 1} ⊗ X ↦ X ⊗ I` (Figure 8, third
column). -/
theorem B_act' : ∀ a b : Fin 3,
    actC 2 (Bbox a b) ⟨a * b, ![1, 2 * a], ![0, 2 * b + a ^ 2 - 1]⟩ = ⟨0, ![0, 1], ![0, 0]⟩ := by
  decide +kernel

/-- `C_b : ω^b Z ↦ Z`, `X ↦ X`. -/
theorem C_act : ∀ b : Fin 3, actC 1 (Cbox b) ⟨b, ![0], ![1]⟩ = ⟨0, ![0], ![1]⟩ ∧
    actC 1 (Cbox b) ⟨0, ![1], ![0]⟩ = ⟨0, ![1], ![0]⟩ := by decide +kernel

/-- `D_{ab} : X Z^i ⊗ X^a Z^b ↦ I ⊗ X Z^i` for every `i`. -/
theorem D_act : ∀ a b i : Fin 3,
    actC 2 (Dbox a b) ⟨0, ![a, 1], ![b, i]⟩ = ⟨0, ![1, 0], ![i, 0]⟩ := by decide +kernel

/-- `D_{ab} : Z ⊗ I ↦ I ⊗ Z` (Figure 8, third column). -/
theorem D_actZ : ∀ a b : Fin 3,
    actC 2 (Dbox a b) ⟨0, ![0, 0], ![0, 1]⟩ = ⟨0, ![0, 0], ![1, 0]⟩ := by decide +kernel

/-- `E_b : X Z^b ↦ X`, `Z ↦ Z`. -/
theorem E_act : ∀ b : Fin 3, actC 1 (Ebox b) ⟨0, ![1], ![b]⟩ = ⟨0, ![1], ![0]⟩ ∧
    actC 1 (Ebox b) ⟨0, ![0], ![1]⟩ = ⟨0, ![0], ![1]⟩ := by decide +kernel

/-- `F_b : ω^b X Z^i ↦ X Z^i` for every `i`, `Z ↦ Z`. -/
theorem F_act : ∀ b i : Fin 3, actC 1 (Fbox b) ⟨b, ![1], ![i]⟩ = ⟨0, ![1], ![i]⟩ ∧
    actC 1 (Fbox b) ⟨0, ![0], ![1]⟩ = ⟨0, ![0], ![1]⟩ := by decide +kernel

theorem F_act0 : ∀ b : Fin 3, actC 1 (Fbox b) ⟨0, ![1], ![0]⟩ = ⟨-b, ![1], ![0]⟩ := by
  decide +kernel

/-! ### `Z`-normal circuits (Figure 10a) and Lemma 3.5 -/

/-- The indices of an `A` box. -/
abbrev AIdx := {p : Fin 3 × Fin 3 // p ≠ (0, 0)}

/-- The ladder of `B` boxes from wire `0` up to the `C` box on the top wire
of `k + 1` wires: the `B` box on wires `j, j + 1` has index `js j`. -/
def ladder : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → Fin 3 → Circ (k + 1)
  | 0, _, c => Cbox c
  | k + 1, js, c => bot2 (Bbox (js 0).1 (js 0).2) ⨾ top (ladder k (fun j => js j.succ) c)

/-- Data on `k` wires read off a ladder: wire `j` carries
`X^{(js j).1} Z^{(js j).2}`, the phase is `ω^c`. -/
def zfrom : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → Fin 3 → PD k
  | 0, _, c => PD.nil c
  | k + 1, js, c => (zfrom k (fun j => js j.succ) c).cons (js 0).1 (js 0).2

/-- `Z` on the top wire of `k + 1` wires. -/
def Ztop : (k : ℕ) → PD (k + 1)
  | 0 => ⟨0, ![0], ![1]⟩
  | k + 1 => (Ztop k).cons 0 0

/-- The ladder carries `Z` from wire `0` to the top wire, absorbing the
factors of the wires above and the phase. -/
theorem ladder_act : ∀ (k : ℕ) (js : Fin k → Fin 3 × Fin 3) (c : Fin 3),
    actC (k + 1) (ladder k js c) ((zfrom k js c).cons 0 1) = Ztop k
  | 0, js, c => (C_act c).1
  | k + 1, js, c => by
    rw [ladder, actC_seq, zfrom, actC_bot2 _ _ _ _ _ _ (B_act _ _)]
    simp only [PD.scale_zero]
    exact (actC_top _ _ _ _).trans (congrArg (PD.cons 0 0) (ladder_act k _ c))

theorem zfrom_surj : ∀ (k : ℕ) (P : PD k), ∃ js c, zfrom k js c = P
  | 0, P => ⟨Fin.elim0, P.c, (PD.eq_nil P).symm⟩
  | k + 1, P => by
    obtain ⟨js, c, h⟩ := zfrom_surj k P.tl
    refine ⟨Fin.cons (P.a 0, P.b 0) js, c, ?_⟩
    rw [zfrom]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [h, PD.cons_tl]

theorem zfrom_inj : ∀ (k : ℕ) {js js' : Fin k → Fin 3 × Fin 3} {c c' : Fin 3},
    zfrom k js c = zfrom k js' c' → js = js' ∧ c = c'
  | 0, js, js', c, c', h => ⟨funext fun x => x.elim0, congrArg PD.c h⟩
  | k + 1, js, js', c, c', h => by
    rw [zfrom, zfrom] at h
    obtain ⟨h1, h2, h3⟩ := PD.cons_inj h
    obtain ⟨hj, hc⟩ := zfrom_inj k h3
    refine ⟨funext fun j => Fin.cases (Prod.ext h1 h2) (fun i => congrFun hj i) j, hc⟩

/-- A `Z`-normal circuit on `n` wires (Figure 10a): `core` puts the `A` box
on wire `0` with the ladder above it, `skip` leaves the bottom wire idle. -/
inductive ZN : ℕ → Type
  | core {k : ℕ} (i : AIdx) (js : Fin k → Fin 3 × Fin 3) (c : Fin 3) : ZN (k + 1)
  | skip {n : ℕ} (z : ZN n) : ZN (n + 1)

namespace ZN

/-- The circuit of a `Z`-normal circuit. -/
def circ : {n : ℕ} → ZN n → Circ n
  | _, core i js c => bot (Abox i.1.1 i.1.2) ⨾ ladder _ js c
  | _, skip z => top z.circ

/-- The Pauli operator that a `Z`-normal circuit sends to `Z` on the top
wire, read off its indices. -/
def pre : {n : ℕ} → ZN n → PD n
  | _, core i js c => (zfrom _ js c).cons i.1.1 i.1.2
  | _, skip z => z.pre.cons 0 0

/-- `Z` on the top wire, for every positive width. -/
def ztop : (n : ℕ) → PD n
  | 0 => PD.nil 0
  | k + 1 => Ztop k

theorem not_zero (z : ZN 0) : False := by cases z

/-- **Lemma 3.5**, the action: `L • pre L = Z ⊗ I ⊗ ⋯ ⊗ I`. -/
theorem act_pre : ∀ {n : ℕ} (z : ZN n), actC n z.circ z.pre = ztop n
  | _, core i js c => by
    rw [circ, pre, actC_seq, actC_bot _ _ _ _ (A_act _ _ i.2)]
    simp only [PD.scale_zero]
    exact ladder_act _ js c
  | _, @skip 0 z => (not_zero z).elim
  | _, @skip (k + 1) z => by
    rw [circ, pre, actC_top, act_pre z]
    rfl

/-- The `Z`-normal circuits read off their preimages: a non-scalar Pauli is
the preimage of one. -/
theorem exists_pre : ∀ {n : ℕ} (P : PD n), (∃ j, P.a j ≠ 0 ∨ P.b j ≠ 0) → ∃ z : ZN n, z.pre = P
  | 0, _, ⟨j, _⟩ => j.elim0
  | k + 1, P, h => by
    by_cases h0 : (P.a 0, P.b 0) = (0, 0)
    · have h0a : P.a 0 = 0 := congrArg Prod.fst h0
      have h0b : P.b 0 = 0 := congrArg Prod.snd h0
      obtain ⟨z, hz⟩ := exists_pre P.tl (by
        obtain ⟨j, hj⟩ := h
        refine Fin.cases (fun hj => ?_) (fun i hj => ⟨i, hj⟩) j hj
        rw [h0a, h0b] at hj
        simp at hj)
      refine ⟨skip z, ?_⟩
      rw [pre, hz]
      conv_rhs => rw [← PD.cons_tl P]
      rw [h0a, h0b]
    · obtain ⟨js, c, hjs⟩ := zfrom_surj k P.tl
      refine ⟨core ⟨(P.a 0, P.b 0), h0⟩ js c, ?_⟩
      rw [pre, hjs]
      exact PD.cons_tl P

/-- Distinct `Z`-normal circuits have distinct preimages. -/
theorem pre_injective : ∀ {n : ℕ} {z z' : ZN n}, z.pre = z'.pre → z = z'
  | _, core i js c, core i' js' c', h => by
    rw [pre, pre] at h
    obtain ⟨h1, h2, h3⟩ := PD.cons_inj h
    obtain ⟨hj, hc⟩ := zfrom_inj _ h3
    have hi : i = i' := Subtype.ext (Prod.ext h1 h2)
    subst hi hj hc
    rfl
  | _, core i js c, skip z', h => by
    rw [pre, pre] at h
    obtain ⟨h1, h2, -⟩ := PD.cons_inj h
    exact (i.2 (Prod.ext h1 h2)).elim
  | _, skip z, core i' js' c', h => by
    rw [pre, pre] at h
    obtain ⟨h1, h2, -⟩ := PD.cons_inj h
    exact (i'.2 (Prod.ext h1.symm h2.symm)).elim
  | _, skip z, skip z', h => by
    rw [pre, pre] at h
    rw [pre_injective (PD.cons_inj h).2.2]

end ZN

/-! ### `X`-normal circuits (Figure 10b) and Lemmas 3.6, 3.7 -/

/-- The ladder of `D` boxes on `k + 1` wires, from the top pair of wires
down to wires `0, 1`; the `D` box on wires `j, j + 1` has index `ds j`. -/
def dladder : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → Circ (k + 1)
  | 0, _ => 1
  | k + 1, ds => top (dladder k (fun j => ds j.succ)) ⨾ bot2 (Dbox (ds 0).1 (ds 0).2)

/-- Data on `k + 1` wires read off an `X`-normal circuit: wire `j < k`
carries `X^{(ds j).1} Z^{(ds j).2}`, the top wire `X Z^i`, the phase is
`ω^c`. -/
def xfrom : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → Fin 3 → Fin 3 → PD (k + 1)
  | 0, _, i, c => ⟨c, ![1], ![i]⟩
  | k + 1, ds, i, c => (xfrom k (fun j => ds j.succ) i c).cons (ds 0).1 (ds 0).2

/-- `ω^c X Z^i` on the bottom wire of `k + 1` wires. -/
def Xbot (k : ℕ) (i c : Fin 3) : PD (k + 1) := (PD.sc c : PD k).cons 1 i

/-- `Z` on the bottom wire of `k + 1` wires. -/
def Zbot (k : ℕ) : PD (k + 1) := (PD.sc 0 : PD k).cons 0 1

theorem xfrom_zero (ds : Fin 0 → Fin 3 × Fin 3) (i c : Fin 3) : xfrom 0 ds i c = Xbot 0 i c := by
  refine PD.ext rfl ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

theorem Ztop_zero : Ztop 0 = Zbot 0 := by
  refine PD.ext rfl ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

/-- The `D` ladder carries `X Z^i` from the top wire to wire `0`, absorbing
the factors of the wires below. -/
theorem dladder_act : ∀ (k : ℕ) (ds : Fin k → Fin 3 × Fin 3) (i c : Fin 3),
    actC (k + 1) (dladder k ds) (xfrom k ds i c) = Xbot k i c
  | 0, ds, i, c => by rw [dladder, actC_one, xfrom_zero]
  | k + 1, ds, i, c => by
    rw [dladder, actC_seq, xfrom, actC_top, dladder_act k _ i c]
    simp only [Xbot]
    rw [actC_bot2 _ _ _ _ _ _ (D_act _ _ _)]
    simp only [PD.scale_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
      PD.cons_sc]

/-- The `D` ladder carries `Z` from the top wire to wire `0` (Lemma 3.7). -/
theorem dladder_actZ : ∀ (k : ℕ) (ds : Fin k → Fin 3 × Fin 3),
    actC (k + 1) (dladder k ds) (Ztop k) = Zbot k
  | 0, ds => by rw [dladder, actC_one, Ztop_zero]
  | k + 1, ds => by
    rw [dladder, actC_seq, Ztop, actC_top, dladder_actZ k _]
    simp only [Zbot]
    rw [actC_bot2 _ _ _ _ _ _ (D_actZ _ _)]
    simp only [PD.scale_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
      PD.cons_sc]

/-- An `X`-normal circuit on `k + 1` wires (Figure 10b): the indices of the
`D` boxes and of the `E` and `F` boxes. -/
structure XN (k : ℕ) where
  /-- The index of the `D` box on wires `j, j + 1`. -/
  ds : Fin k → Fin 3 × Fin 3
  /-- The index of the `E` box. -/
  h : Fin 3
  /-- The index of the `F` box. -/
  v : Fin 3

namespace XN

/-- The circuit of an `X`-normal circuit. -/
def circ {k : ℕ} (M : XN k) : Circ (k + 1) := dladder k M.ds ⨾ bot (Ebox M.h) ⨾ bot (Fbox M.v)

/-- The Pauli operator that an `X`-normal circuit sends to `X` on the bottom
wire. -/
def pre {k : ℕ} (M : XN k) : PD (k + 1) := xfrom k M.ds M.h M.v

/-- **Lemma 3.6**, the action: `M • pre M = I ⊗ ⋯ ⊗ I ⊗ X`. -/
theorem act_pre {k : ℕ} (M : XN k) : actC (k + 1) M.circ M.pre = Xbot k 0 0 := by
  rw [circ, pre, actC_seq, actC_seq, dladder_act]
  simp only [Xbot]
  rw [actC_bot _ _ _ _ (E_act _).1]
  simp only [PD.scale_zero, Matrix.cons_val_zero]
  rw [actC_bot _ _ _ _ (F_act0 _), PD.scale_cons]
  simp only [Matrix.cons_val_zero, PD.scale, PD.sc, neg_add_cancel]

/-- **Lemma 3.7**: an `X`-normal circuit carries `Z` from the top wire to the
bottom wire. -/
theorem act_Ztop {k : ℕ} (M : XN k) : actC (k + 1) M.circ (Ztop k) = Zbot k := by
  rw [circ, actC_seq, actC_seq, dladder_actZ]
  simp only [Zbot]
  rw [actC_bot _ _ _ _ (E_act _).2]
  simp only [PD.scale_zero, Matrix.cons_val_zero]
  rw [actC_bot _ _ _ _ (F_act _ 0).2]
  simp only [PD.scale_zero, Matrix.cons_val_zero]

theorem xfrom_surj : ∀ (k : ℕ) (P : PD (k + 1)), P.a (Fin.last k) = 1 →
    ∃ ds i c, xfrom k ds i c = P
  | 0, P, h => ⟨Fin.elim0, P.b 0, P.c, by
      refine PD.ext rfl ?_ ?_
      · funext j; fin_cases j; exact h.symm
      · funext j; fin_cases j; rfl⟩
  | k + 1, P, h => by
    obtain ⟨ds, i, c, hx⟩ := xfrom_surj k P.tl h
    refine ⟨Fin.cons (P.a 0, P.b 0) ds, i, c, ?_⟩
    rw [xfrom]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hx, PD.cons_tl]

theorem xfrom_inj : ∀ (k : ℕ) {ds ds' : Fin k → Fin 3 × Fin 3} {i i' c c' : Fin 3},
    xfrom k ds i c = xfrom k ds' i' c' → ds = ds' ∧ i = i' ∧ c = c'
  | 0, ds, ds', i, i', c, c', h => by
    simp only [xfrom, PD.mk.injEq] at h
    exact ⟨funext fun x => x.elim0, by simpa using congrFun h.2.2 0, h.1⟩
  | k + 1, ds, ds', i, i', c, c', h => by
    rw [xfrom, xfrom] at h
    obtain ⟨h1, h2, h3⟩ := PD.cons_inj h
    obtain ⟨hd, hi, hc⟩ := xfrom_inj k h3
    exact ⟨funext fun j => Fin.cases (Prod.ext h1 h2) (fun l => congrFun hd l) j, hi, hc⟩

/-- The `X`-normal circuits read off their preimages: a Pauli with `X Z^i`
on the top wire is the preimage of one. -/
theorem exists_pre {k : ℕ} (P : PD (k + 1)) (h : P.a (Fin.last k) = 1) :
    ∃ M : XN k, M.pre = P := by
  obtain ⟨ds, i, c, hx⟩ := xfrom_surj k P h
  exact ⟨⟨ds, i, c⟩, hx⟩

theorem pre_injective {k : ℕ} {M M' : XN k} (h : M.pre = M'.pre) : M = M' := by
  obtain ⟨hd, hi, hc⟩ := xfrom_inj k h
  cases M; cases M'
  simp only at hd hi hc
  rw [hd, hi, hc]

end XN

end QCert.QutritClifford
