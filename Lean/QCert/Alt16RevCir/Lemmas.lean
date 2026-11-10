/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Derivations in the circuits' theory: what the Reidemeister–Schreier step from Lafont's presentation of 𝔄₁₆ needs of the rules of Syntactics

Translation of `Lemmas.agda`.  Two facts about the translation `g` of
Lafont's cycles into circuits, the two hypotheses of the step in that
direction (`Iso`):

* `lemma_g_rel`: every instance of Lafont's relation, read through `g`, is a
  rule of `Syntactics`.  His relations `order`, `near` and `far` at the
  cycles `d` points up are the rules `order d`, `near d` and `far d`, and his
  commutation of the cycle with a generator three or more points further up
  is the rule `apart`.  An instance one point up is the same instance read
  one point further up (`gd_up`), so the statement is about `gd d` for every
  `d`, by recursion on the instance.  It is proved in any congruence in
  which those four families hold (`FromCycles`), which `Equivalence` uses
  for the rules (1)–(7).

* `lemma_g_f`: every gate is the circuit of its word in the cycles.  For
  the six gates on their own wires that is one of the rules `gate_X`, …,
  `gate_Ex₂`.  A gate further up is that gate between swaps (`lemma_X_up`,
  `lemma_CX_up`, `lemma_CCX_up`, from the naturality of the swap), and
  `Translation.f` was defined to follow: its word is the word of the gate
  between the words of the swaps.

**Deviations from the Agda.**  The Agda's module `FromCycles`, parameterised
by a congruence and the four families, is a namespace whose lemmas take them
as arguments.  `conjugate` is stated over any relation, and `Theory` reuses
it (the Agda has a copy in each).  The circuit of a cycle is computed by
`lift_g_ω₀`, …, `lift_g_ω₁₃` (`rfl`), with which a word in the cycles is
read through `g` by `simp`, where the Agda's `g ʷ` computes.
-/
import QCert.Alt16RevCir.Translation

namespace QCert.Alt16RevCir

open QCert QCert.Circuit CircuitProp

variable {n : ℕ}

/-! ## Reading a shifted word -/

/-- A word one point up, read `d` points up, is the word read `d + 1` points
up (the Agda's `gᵈ-↑`). -/
theorem gd_up (d : ℕ) (w : Alternating.Circ n) :
    FreeMonoid.lift (gd d) (shift w) = FreeMonoid.lift (gd (d + 1)) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of y w ih =>
    rw [map_mul, shift_of, map_mul, map_mul, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of, ih]
    rfl

/-! The circuits of the fourteen cycles. -/

theorem lift_g_ω₀ : FreeMonoid.lift g ω₀ = Ω 0 := rfl

theorem lift_g_ω₁ : FreeMonoid.lift g ω₁ = Ω 1 := rfl

theorem lift_g_ω₂ : FreeMonoid.lift g ω₂ = Ω 2 := rfl

theorem lift_g_ω₃ : FreeMonoid.lift g ω₃ = Ω 3 := rfl

theorem lift_g_ω₄ : FreeMonoid.lift g ω₄ = Ω 4 := rfl

theorem lift_g_ω₅ : FreeMonoid.lift g ω₅ = Ω 5 := rfl

theorem lift_g_ω₆ : FreeMonoid.lift g ω₆ = Ω 6 := rfl

theorem lift_g_ω₇ : FreeMonoid.lift g ω₇ = Ω 7 := rfl

theorem lift_g_ω₈ : FreeMonoid.lift g ω₈ = Ω 8 := rfl

theorem lift_g_ω₉ : FreeMonoid.lift g ω₉ = Ω 9 := rfl

theorem lift_g_ω₁₀ : FreeMonoid.lift g ω₁₀ = Ω 10 := rfl

theorem lift_g_ω₁₁ : FreeMonoid.lift g ω₁₁ = Ω 11 := rfl

theorem lift_g_ω₁₂ : FreeMonoid.lift g ω₁₂ = Ω 12 := rfl

theorem lift_g_ω₁₃ : FreeMonoid.lift g ω₁₃ = Ω 13 := rfl

/-- Read a word in the cycles through `g`. -/
macro "lift_g" : tactic =>
  `(tactic| simp only [map_mul, lift_g_ω₀, lift_g_ω₁, lift_g_ω₂, lift_g_ω₃, lift_g_ω₄,
    lift_g_ω₅, lift_g_ω₆, lift_g_ω₇, lift_g_ω₈, lift_g_ω₉, lift_g_ω₁₀, lift_g_ω₁₁, lift_g_ω₁₂,
    lift_g_ω₁₃])

/-! ## Lafont's relations, read through g

In any congruence on the circuits in which the relations between the cycles
hold: that of `Syntactics`, where they are rules, and that of the rules
(1)–(7) (`Theory`), where they are theorems (`Equivalence`). -/

namespace FromCycles

variable (Γ : WRel (Gn 4))
  (order' : ∀ i, i ≤ 13 → Derivable Γ (Ω i * Ω i * Ω i) 1)
  (near' : ∀ i, i ≤ 12 → Derivable Γ (Ω i * Ω (i + 1) * Ω i) (Ω (i + 1) * Ω (i + 1)))
  (far' : ∀ i, i ≤ 11 → Derivable Γ (Ω i * Ω (i + 2) * Ω i) (Ω (i + 2) * Ω i * Ω (i + 1)))
  (apart' : ∀ i j, i + 3 ≤ j → j ≤ 13 → Derivable Γ (Ω j * Ω i) (Ω i * Ω j))

/-- A generator read `c` points up is a circuit `Ω j` with `c ≤ j`. -/
theorem gd_above : ∀ {k : ℕ} (c : ℕ) (y : Alternating.Gn k), c + k = 16 →
    ∃ j, gd c y = Ω j ∧ c ≤ j ∧ j ≤ 13
  | _, _, .gate0 g, _ => nomatch g
  | _, _, .gate1 g, _ => nomatch g
  | _, _, .gate2 g, _ => nomatch g
  | _, c, .gate3 .ω_gate, eq => ⟨c, rfl, le_rfl, by omega⟩
  | _, c, .up y, eq =>
    let ⟨j, e, h₁, h₂⟩ := gd_above (c + 1) y (by omega)
    ⟨j, e, by omega, h₂⟩

include order' near' far' apart' in
/-- Every instance of Lafont's relation, read through `g` at any shift. -/
theorem lemma_g_rel : ∀ {n : ℕ} (d : ℕ), d + n = 16 → ∀ {u t : Alternating.Circ n},
    Lift Alternating.SRel n u t →
    Derivable Γ (FreeMonoid.lift (gd d) u) (FreeMonoid.lift (gd d) t)
  | _, d, eq, _, _, .rule .order => by
    simp only [map_mul, map_one, FreeMonoid.lift_eval_of]
    exact order' d (by omega)
  | _, d, eq, _, _, .rule .near => by
    simp only [map_mul, shift_of, FreeMonoid.lift_eval_of]
    exact near' d (by omega)
  | _, d, eq, _, _, .rule .far => by
    simp only [map_mul, shift_of, FreeMonoid.lift_eval_of]
    exact far' d (by omega)
  | _, d, eq, _, _, .shift p => by
    rw [gd_up, gd_up]
    exact lemma_g_rel (d + 1) (by omega) p
  | _, d, eq, _, _, .comm3 .ω_gate y => by
    obtain ⟨j, e, h₁, h₂⟩ := gd_above (d + 3) y (by omega)
    simp only [map_mul, FreeMonoid.lift_eval_of]
    show Derivable Γ (gd (d + 3) y * Ω d) (Ω d * gd (d + 3) y)
    rw [e]
    exact apart' d j h₁ h₂
  | _, _, _, _, _, .comm1 h _ => nomatch h
  | _, _, _, _, _, .comm2 h _ => nomatch h
  | _, _, _, _, _, .scalar c => nomatch c

end FromCycles

/-- Every instance of Lafont's relation, read through `g` at any shift, is a
rule of `Syntactics`. -/
theorem lemma_g_rel (d : ℕ) (eq : d + n = 16) {u t : Alternating.Circ n}
    (r : Lift Alternating.SRel n u t) :
    4 ⊢ FreeMonoid.lift (gd d) u ≈ FreeMonoid.lift (gd d) t :=
  FromCycles.lemma_g_rel (VRel SRel 4)
    (fun i p => srel_rule (SRel.order i p))
    (fun i p => srel_rule (SRel.near i p))
    (fun i p => srel_rule (SRel.far i p))
    (fun i j p q => srel_rule (SRel.apart i j p q)) d eq r

/-! ## A gate one wire up, between swaps -/

/-- If `a` followed by `s` is `s` followed by `b`, and `s'` undoes `s`, then
`b` is `a` between `s'` and `s`. -/
theorem conjugate {R : CRel Gate} {a b s s' : Circ n} (inv : Der R n (s' * s) 1)
    (nat : Der R n (a * s) (s * b)) : Der R n b (s' * a * s) := by
  have h : Der R n (1 * b) (s' * a * s) :=
    (inv.symm.mul (Derivable.refl b)).trans (by
      rw [mul_assoc, mul_assoc]
      exact (Derivable.refl s').mul nat.symm)
  rwa [one_mul] at h

theorem lemma_X_up : (n + 2) ⊢ shift X ≈ Ex * X * Ex :=
  conjugate σ_invol (sym_rule (Sym.σ_nat₁ Gate.X_gate))

theorem lemma_CX_up : (n + 3) ⊢ shift CX ≈ σcInv 2 * CX * σc 2 :=
  conjugate (σInvσ 2) (sym_rule (Sym.σ_nat₂ Gate.CX_gate))

theorem lemma_CCX_up : (n + 4) ⊢ shift CCX ≈ σcInv 3 * CCX * σc 3 :=
  conjugate (σInvσ 3) (sym_rule (Sym.σ_nat₃ Gate.CCX_gate))

/-! ## The gates, read through f and back through g -/

/-! The words of the gates on their own wires, read through `g`. -/

theorem lift_g_fX :
    FreeMonoid.lift g fX = Ω 1 * Ω 0 * Ω 5 * Ω 4 * Ω 9 * Ω 8 * Ω 13 * Ω 12 := by
  rw [fX]; lift_g

theorem lift_g_fCX : FreeMonoid.lift g fCX = Ω 3 * Ω 2 * Ω 11 * Ω 10 := by
  rw [fCX]; lift_g

theorem lift_g_fCCX : FreeMonoid.lift g fCCX = Ω 5 * Ω 4 * Ω 7 * Ω 6 * Ω 9 * Ω 8 := by
  rw [fCCX]; lift_g

theorem lift_g_fEx₀ :
    FreeMonoid.lift g fEx₀ = Ω 1 * Ω 3 * Ω 2 * Ω 4 * Ω 9 * Ω 11 * Ω 10 * Ω 12 := by
  rw [fEx₀]; lift_g

theorem lift_g_fEx₁ : FreeMonoid.lift g fEx₁ =
    Ω 2 * Ω 3 * Ω 4 * Ω 2 * Ω 5 * Ω 3 * Ω 8 * Ω 9 * Ω 10 * Ω 8 * Ω 11 * Ω 9 := by
  rw [fEx₁]; lift_g

theorem lift_g_fEx₂ : FreeMonoid.lift g fEx₂ =
    Ω 6 * Ω 7 * Ω 8 * Ω 9 * Ω 10 * Ω 11 * Ω 12 * Ω 13 *
    Ω 4 * Ω 5 * Ω 6 * Ω 7 * Ω 8 * Ω 9 * Ω 10 * Ω 11 *
    Ω 6 * Ω 7 * Ω 8 * Ω 9 * Ω 4 * Ω 5 * Ω 6 * Ω 7 := by
  rw [fEx₂]; lift_g

/-! The gates on their own wires: the rules that name their words. -/

private theorem x₀ : 4 ⊢ X₀ ≈ FreeMonoid.lift g fX := by
  rw [lift_g_fX]; exact srel_rule SRel.gate_X

private theorem cx₀ : 4 ⊢ CX ≈ FreeMonoid.lift g fCX := by
  rw [lift_g_fCX]; exact srel_rule SRel.gate_CX

private theorem ccx₀ : 4 ⊢ CCX ≈ FreeMonoid.lift g fCCX := by
  rw [lift_g_fCCX]; exact srel_rule SRel.gate_CCX

private theorem ex₀ : 4 ⊢ Ex₀ ≈ FreeMonoid.lift g fEx₀ := by
  rw [lift_g_fEx₀]; exact srel_rule SRel.gate_Ex₀

private theorem ex₁ : 4 ⊢ Ex₁ ≈ FreeMonoid.lift g fEx₁ := by
  rw [lift_g_fEx₁]; exact srel_rule SRel.gate_Ex₁

private theorem ex₂ : 4 ⊢ Ex₂ ≈ FreeMonoid.lift g fEx₂ := by
  rw [lift_g_fEx₂]; exact srel_rule SRel.gate_Ex₂

/-! NOT further up: between the swaps below it, one wire at a time. -/

private theorem x₁ : 4 ⊢ X₁ ≈ FreeMonoid.lift g fX₁ := by
  rw [fX₁, map_mul, map_mul]
  exact lemma_X_up.trans ((ex₀.mul x₀).mul ex₀)

private theorem x₂ : 4 ⊢ X₂ ≈ FreeMonoid.lift g fX₂ := by
  rw [fX₂, map_mul, map_mul]
  exact (lemma_cong_up (lemma_X_up (n := 1))).trans ((ex₁.mul x₁).mul ex₁)

private theorem x₃ : 4 ⊢ X₃ ≈ FreeMonoid.lift g fX₃ := by
  rw [fX₃, map_mul, map_mul]
  exact (lemma_cong_up (lemma_cong_up (lemma_X_up (n := 0)))).trans ((ex₂.mul x₂).mul ex₂)

/-! `CX` and `CCX` further up: between the cycles of swaps. -/

private theorem cx₁ : 4 ⊢ shift CX ≈ FreeMonoid.lift g fCX₁ := by
  rw [fCX₁, map_mul, map_mul, map_mul, map_mul]
  exact lemma_CX_up.trans (((ex₀.mul ex₁).mul cx₀).mul (ex₁.mul ex₀))

private theorem cx₂ : 4 ⊢ shift (shift CX) ≈ FreeMonoid.lift g fCX₂ := by
  rw [fCX₂, map_mul, map_mul, map_mul, map_mul]
  exact (lemma_cong_up (lemma_CX_up (n := 0))).trans
    (((ex₁.mul ex₂).mul cx₁).mul (ex₂.mul ex₁))

private theorem ccx₁ : 4 ⊢ shift CCX ≈ FreeMonoid.lift g fCCX₁ := by
  rw [fCCX₁]
  simp only [map_mul]
  exact lemma_CCX_up.trans ((((ex₀.mul ex₁).mul ex₂).mul ccx₀).mul ((ex₂.mul ex₁).mul ex₀))

/-- Each gate is the circuit of its word in the cycles. -/
theorem lemma_g_f : ∀ x : Gn 4, 4 ⊢ FreeMonoid.of x ≈ FreeMonoid.lift g (f x)
  | .gate0 g => nomatch g
  | .gate1 .X_gate => x₀
  | .gate2 .CX_gate => cx₀
  | .gate2 .Ex_gate => ex₀
  | .gate3 .CCX_gate => ccx₀
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => x₁
  | .up (.gate2 .CX_gate) => cx₁
  | .up (.gate2 .Ex_gate) => ex₁
  | .up (.gate3 .CCX_gate) => ccx₁
  | .up (.up (.gate0 g)) => nomatch g
  | .up (.up (.gate1 .X_gate)) => x₂
  | .up (.up (.gate2 .CX_gate)) => cx₂
  | .up (.up (.gate2 .Ex_gate)) => ex₂
  | .up (.up (.up (.gate0 g))) => nomatch g
  | .up (.up (.up (.gate1 .X_gate))) => x₃
  | .up (.up (.up (.up (.gate0 g)))) => nomatch g

end QCert.Alt16RevCir
