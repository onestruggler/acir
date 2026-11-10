/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The rules (1)–(7) present 𝔄₁₆ on four wires

Translation of `Equivalence.agda`: the second Reidemeister–Schreier step of
this folder.  Its two relation sets are over the same gates: `Syntactics`'
relation (Lafont's relations read on the cycles `Ω i`, and one rule per
gate naming its word in the cycles) and the rules r1, …, r7 of `Theory`.
The translations are the identity, so the step is that each relation set's
rules follow from the other's:

* `t_to_s` (`Theory`): the rules r1, …, r7 hold for functions on states,
  for which `Syntactics`' relation is complete.

* `s_to_t`, here: every rule of `Syntactics` is derived from r1, …, r7.  The
  relations between the cycles are `Four.Relations`' (`orderT`, …):
  derivations on four wires found by search and replayed by the engine,
  from rule (7) and three-wire steps, which rest on the completeness of the
  rules on three wires (`ThreeWire`).  The gate rules follow from them:
  `Four.Relations` has each gate on its own wires as the circuit of some
  word in the cycles (`gate_XT`, …); that word and `Translation`'s have the
  same permutation, so they are equal by Lafont's relations (his
  completeness), and `g` carries the equation to the circuits, the
  relations between the cycles being derived (`to_f`).

So the two congruences coincide on four wires (`rules_iso_relations`: the
identity is an isomorphism), the step from Lafont's presentation holds for
the rules as it does for `Syntactics`' relation (`Theorem_Rules_iso_Cycles`,
with the same translations `f` and `g`), and the circuits modulo r1, …, r7
present 𝔄₁₆ (`presentationT`), soundly and completely for the functions on
states, with the canonical circuits of `NormalForm` as unique normal forms.

**Deviations from the Agda.**  `s_to_t` is the inclusion of the generated
congruences, where the Agda's is an induction on derivations.  The
isomorphisms are `MulEquiv`s of the quotient monoids (`Lib/Morphism`), and
the Agda's module `Theoremᵀ` is the lemmas `f_well_definedT`,
`g_left_inv_genT`, `rsStepT`.  The Agda's `⋯ᵀ` names are `⋯T`, and `s⇒t`,
`t⇒s` are `s_to_t`, `t_to_s`.
-/
import QCert.Alt16RevCir.NormalForm
import QCert.Alt16RevCir.Four.Relations

namespace QCert.Alt16RevCir.Equivalence

open QCert QCert.Circuit CircuitProp
open Four.Relations

variable {n : ℕ}

/-! ## Lafont's relations, read through g, from the rules -/

/-- Each instance of his relation is one of the relations between the
cycles, which `Four.Relations` derives. -/
theorem g_well_definedT {u t : Alternating.Circ 16} (r : Lift Alternating.SRel 16 u t) :
    4 ⊢ᵀ FreeMonoid.lift g u ≈ FreeMonoid.lift g t :=
  FromCycles.lemma_g_rel (VRel TRel 4) orderT nearT farT apartT 0 rfl r

/-- The Agda's `gʷ-congᵀ`. -/
theorem gw_congT {u t : Alternating.Circ 16} (d : Derivable (Lift Alternating.SRel 16) u t) :
    4 ⊢ᵀ FreeMonoid.lift g u ≈ FreeMonoid.lift g t :=
  Morphism.lift_cong g g_well_definedT d

/-! ## The gates, read through f and back through g -/

/-- A circuit that is the circuit of some word in the cycles is the circuit
of its own word: the two words have the same permutation, that of the
circuit's function on states, so they are equal by Lafont's relations, and
`g` carries the equation back. -/
theorem to_f (c : Circ 4) (u : Alternating.Circ 16) (e : 4 ⊢ᵀ c ≈ FreeMonoid.lift g u) :
    4 ⊢ᵀ c ≈ FreeMonoid.lift g (FreeMonoid.lift f c) :=
  e.trans (gw_congT (Alternating.completeness fun i =>
    (g_sem u i).symm.trans
      ((congrArg dec (T_sound e (enc i)).symm).trans (f_sem c i).symm)))

/-! The gates further up, between swaps, as circuits of words in the
cycles. -/

private def uX₁ : Alternating.Circ 16 := wEx₀ * wX * wEx₀

private def uX₂ : Alternating.Circ 16 := wEx₁ * uX₁ * wEx₁

private def uX₃ : Alternating.Circ 16 := wEx₂ * uX₂ * wEx₂

private def uCX₁ : Alternating.Circ 16 := (wEx₀ * wEx₁) * wCX * (wEx₁ * wEx₀)

private def uCX₂ : Alternating.Circ 16 := (wEx₁ * wEx₂) * uCX₁ * (wEx₂ * wEx₁)

private def uCCX₁ : Alternating.Circ 16 := (wEx₀ * wEx₁ * wEx₂) * wCCX * ((wEx₂ * wEx₁) * wEx₀)

private theorem x₁ : 4 ⊢ᵀ X₁ ≈ FreeMonoid.lift g uX₁ := by
  rw [uX₁, map_mul, map_mul]
  exact X_up.trans ((gate_Ex₀T.mul gate_XT).mul gate_Ex₀T)

private theorem x₂ : 4 ⊢ᵀ X₂ ≈ FreeMonoid.lift g uX₂ := by
  rw [uX₂, map_mul, map_mul]
  exact (lemma_cong_up (X_up (n := 1))).trans ((gate_Ex₁T.mul x₁).mul gate_Ex₁T)

private theorem x₃ : 4 ⊢ᵀ X₃ ≈ FreeMonoid.lift g uX₃ := by
  rw [uX₃, map_mul, map_mul]
  exact (lemma_cong_up (lemma_cong_up (X_up (n := 0)))).trans
    ((gate_Ex₂T.mul x₂).mul gate_Ex₂T)

private theorem cx₁ : 4 ⊢ᵀ shift CX ≈ FreeMonoid.lift g uCX₁ := by
  rw [uCX₁, map_mul, map_mul, map_mul, map_mul]
  exact CX_up.trans (((gate_Ex₀T.mul gate_Ex₁T).mul gate_CXT).mul (gate_Ex₁T.mul gate_Ex₀T))

private theorem cx₂ : 4 ⊢ᵀ shift (shift CX) ≈ FreeMonoid.lift g uCX₂ := by
  rw [uCX₂, map_mul, map_mul, map_mul, map_mul]
  exact (lemma_cong_up (CX_up (n := 0))).trans
    (((gate_Ex₁T.mul gate_Ex₂T).mul cx₁).mul (gate_Ex₂T.mul gate_Ex₁T))

private theorem ccx₁ : 4 ⊢ᵀ shift CCX ≈ FreeMonoid.lift g uCCX₁ := by
  rw [uCCX₁]
  simp only [map_mul]
  exact CCX_up.trans
    ((((gate_Ex₀T.mul gate_Ex₁T).mul gate_Ex₂T).mul gate_CCXT).mul
      ((gate_Ex₂T.mul gate_Ex₁T).mul gate_Ex₀T))

/-- Each gate is the circuit of its word in the cycles. -/
theorem lemma_g_fT : ∀ x : Gn 4, 4 ⊢ᵀ FreeMonoid.of x ≈ FreeMonoid.lift g (f x)
  | .gate0 g => nomatch g
  | .gate1 .X_gate => to_f _ wX gate_XT
  | .gate2 .CX_gate => to_f _ wCX gate_CXT
  | .gate2 .Ex_gate => to_f _ wEx₀ gate_Ex₀T
  | .gate3 .CCX_gate => to_f _ wCCX gate_CCXT
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => to_f _ uX₁ x₁
  | .up (.gate2 .CX_gate) => to_f _ uCX₁ cx₁
  | .up (.gate2 .Ex_gate) => to_f _ wEx₁ gate_Ex₁T
  | .up (.gate3 .CCX_gate) => to_f _ uCCX₁ ccx₁
  | .up (.up (.gate0 g)) => nomatch g
  | .up (.up (.gate1 .X_gate)) => to_f _ uX₂ x₂
  | .up (.up (.gate2 .CX_gate)) => to_f _ uCX₂ cx₂
  | .up (.up (.gate2 .Ex_gate)) => to_f _ wEx₂ gate_Ex₂T
  | .up (.up (.up (.gate0 g))) => nomatch g
  | .up (.up (.up (.gate1 .X_gate))) => to_f _ uX₃ x₃
  | .up (.up (.up (.up (.gate0 g)))) => nomatch g

/-! ## From the translated relations to the rules -/

private theorem s_to_t_rule : ∀ {n : ℕ} {w v : Circ n}, SRel n w v → n ⊢ᵀ w ≈ v
  | _, _, _, .order i p => orderT i p
  | _, _, _, .near i p => nearT i p
  | _, _, _, .far i p => farT i p
  | _, _, _, .apart i j p q => apartT i j p q
  | _, _, _, .gate_X => by rw [← lift_g_fX]; exact lemma_g_fT (.gate1 .X_gate)
  | _, _, _, .gate_CX => by rw [← lift_g_fCX]; exact lemma_g_fT (.gate2 .CX_gate)
  | _, _, _, .gate_CCX => by rw [← lift_g_fCCX]; exact lemma_g_fT (.gate3 .CCX_gate)
  | _, _, _, .gate_Ex₀ => by rw [← lift_g_fEx₀]; exact lemma_g_fT (.gate2 .Ex_gate)
  | _, _, _, .gate_Ex₁ => by rw [← lift_g_fEx₁]; exact lemma_g_fT (.up (.gate2 .Ex_gate))
  | _, _, _, .gate_Ex₂ => by rw [← lift_g_fEx₂]; exact lemma_g_fT (.up (.up (.gate2 .Ex_gate)))

/-- Each rule of `Syntactics`' relation is a consequence of r1, …, r7: its
own rules as above; the laws of the swap and the structural rules are the
same on both sides. -/
theorem s_to_t_ax : ∀ {n : ℕ} {w v : Circ n}, VRel SRel n w v → n ⊢ᵀ w ≈ v
  | _, _, _, .rule (.srel r) => s_to_t_rule r
  | _, _, _, .rule (.σrel s) => sym_rule s
  | _, _, _, .shift a => lemma_cong_up (s_to_t_ax a)
  | _, _, _, .comm1 h x => Derivable.of (Lift.comm1 h x)
  | _, _, _, .comm2 h x => Derivable.of (Lift.comm2 h x)
  | _, _, _, .comm3 h x => Derivable.of (Lift.comm3 h x)
  | _, _, _, .scalar c => nomatch c

theorem s_to_t {w v : Circ n} (d : n ⊢ w ≈ v) : n ⊢ᵀ w ≈ v := by
  have : conGen (VRel SRel n) ≤ conGen (VRel TRel n) :=
    Con.conGen_le fun _ _ r => s_to_t_ax r
  exact this d

/-- And back, on four wires (`Theory`). -/
theorem t_to_s_ax {w v : Circ 4} (a : VRel TRel 4 w v) : 4 ⊢ w ≈ v :=
  t_to_s (Derivable.of a)

/-! ## The two relation sets generate the same congruence -/

/-- Every gate has an inverse by the rules, as it has by `Syntactics`'. -/
theorem grouplikeT : Grouplike (VRel TRel 4) := fun x =>
  let ⟨w, h⟩ := Iso.grouplike x
  ⟨w, s_to_t h⟩

/-- The identity is an isomorphism of the two monoids of circuits (the Agda's
`rules≅relations`). -/
def rules_iso_relations :
    (conGen (VRel TRel 4)).Quotient ≃* (conGen (VRel SRel 4)).Quotient :=
  Morphism.idIso t_to_s_ax s_to_t_ax

/-! ## The step from Lafont's presentation, for the rules -/

/-- `f`: circuits → Lafont's words.  The rules hold for functions on states,
so the words of their two sides have the same permutation. -/
theorem f_well_definedT {w v : Circ 4} (r : VRel TRel 4 w v) :
    Derivable (Lift Alternating.SRel 16) (FreeMonoid.lift f w) (FreeMonoid.lift f v) :=
  Alternating.completeness fun i =>
    (f_sem w i).trans ((congrArg dec (T_ax_sound r (enc i))).trans (f_sem v i).symm)

theorem g_left_inv_genT (x : Gn 4) : 4 ⊢ᵀ FreeMonoid.of x ≈ FreeMonoid.lift g (f x) :=
  lemma_g_fT x

/-- The four facts, for the rules (a cycle and the word of its circuit: as
for `Syntactics`' relation). -/
theorem rsStepT : Morphism.RSStep (VRel TRel 4) (Lift Alternating.SRel 16) f g where
  f_well_defined := f_well_definedT
  f_left_inv_gen := Iso.f_left_inv_gen
  g_well_defined := g_well_definedT
  g_left_inv_gen := g_left_inv_genT

/-- The circuits modulo the rules and the words in the cycles modulo
Lafont's relations are isomorphic, by `f ʷ`. -/
def Theorem_Rules_iso_Cycles :
    (conGen (VRel TRel 4)).Quotient ≃* (conGen (Lift Alternating.SRel 16)).Quotient :=
  rsStepT.iso

/-! ## The presentation -/

/-- Two circuits are equal by the rules exactly when they are the same
function on states. -/
theorem soundT {w v : Circ 4} (d : 4 ⊢ᵀ w ≈ v) : sem w ≐ sem v :=
  T_sound d

theorem completeT {w v : Circ 4} (e : sem w ≐ sem v) : 4 ⊢ᵀ w ≈ v :=
  s_to_t (complete e)

/-- The circuits modulo r1, …, r7 present 𝔄₁₆, a circuit read as the even
permutation of its word in the cycles. -/
theorem presentationT : IsPresentationOf (VRel TRel 4) permA :=
  presentation_semA grouplikeT (fun d => semA_congr (T_sound d))
    (fun e => completeT (feq_of_semA e))

/-! ## The normal form -/

/-- Every circuit is equal by the rules to its canonical circuit, the
translation of Lafont's canonical form (`NormalForm`), -/
theorem normal_formT (w : Circ 4) : 4 ⊢ᵀ canon (nf w) ≈ w :=
  s_to_t (normal_form w)

/-- and circuits equal by the rules have the same normal form. -/
theorem nf_congT {w v : Circ 4} (e : 4 ⊢ᵀ w ≈ v) : nf w = nf v :=
  nf_cong (t_to_s e)

end QCert.Alt16RevCir.Equivalence
