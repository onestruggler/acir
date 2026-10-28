/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of CliffCS₂ on two wires

Theorem 22 (5) on two wires, which the paper does not treat: by transfer
from Bian and Selinger's presentation of `U₄(ℤ[½, i])`
(`QCert.BianSelingerUn`), refined by a new central scalar `w` with `w² = i`
(Appendix I, `refine_complete`).

* The encoding (basis index `s₀ + 2 s₁`, wire `0` the least significant
  bit): `ω₈ ↦ w`, `H₀ ↦ w K_[0,1] K_[2,3]`, `H₁ ↦ w K_[0,2] K_[1,3]`,
  `S₀ ↦ i_[1] i_[3]`, `S₁ ↦ i_[2] i_[3]`, `CS ↦ i_[3]`, the swap
  `↦ X_[1,2]`; it preserves the semantics on each generator, decided over
  `ℚ(ω)` (`e_ok`).
* The decoding is the block decoding of `W2Blocks` read as circuits
  (`blk`): every block relation is derived from Figure 6 (`W2Lemmas`,
  `brel_circ`), so every refined relation decodes to a derivable equation
  (`W2Rels.rel_dec`), and decoding the encoding of a generator derives it
  (`DE_gen`).
-/
import QCert.Minimality.CliffordCS.W2Rels
import QCert.Minimality.CliffordCS.W2Lemmas
import QCert.Minimality.CliffordCS.Completeness

namespace QCert.Minimality.CliffordCS.W2

open Matrix QCert.Circuit OmegaParity

/-! ### The blocks as circuits -/

/-- The circuit of a block (time order in `tw`). -/
def blk : Blk → Circuit Gate 2
  | .t0 => tw 2 [(.H, 0), (.S, 0), (.S, 0), (.CS, 0), (.CS, 0), (.H, 0)]
  | .t1 => tw 2 [(.SW, 0)]
  | .t2 => tw 2 [(.H, 0), (.CS, 0), (.CS, 0), (.H, 0)]
  | .x0 => tw 2 [(.H, 0), (.S, 0), (.S, 0), (.H, 0)]
  | .x1 => tw 2 [(.H, 1), (.S, 1), (.S, 1), (.H, 1)]
  | .cs => tw 2 [(.CS, 0)]
  | .ck => tw 2 [(.S, 1), (.S, 1), (.S, 1), (.CS, 0), (.H, 0), (.CS, 0), (.H, 0), (.CS, 0)]
  | .w => tw 2 [(.w, 0)]
  | .h0 => tw 2 [(.H, 0)]
  | .h1 => tw 2 [(.H, 1)]
  | .s0 => tw 2 [(.S, 0)]
  | .s1 => tw 2 [(.S, 1)]

instance : DecidableEq (Circuit Gate 2) := inferInstanceAs (DecidableEq (List (QCert.Gen Gate 2)))

/-- Words of blocks as circuits. -/
def blkW : FreeMonoid Blk →* Circuit Gate 2 := FreeMonoid.lift blk

/-- The derived equations match the block relations, one for one. -/
def check : List (DEqn Th 2) → List (List Blk × List Blk) → Bool
  | [], [] => true
  | q :: qs, p :: ps =>
    (decide (q.lhs = blkW (FreeMonoid.ofList p.1)) && decide (q.rhs = blkW (FreeMonoid.ofList p.2)))
      && check qs ps
  | _, _ => false

theorem check_mem : ∀ (qs : List (DEqn Th 2)) (ps : List (List Blk × List Blk)),
    check qs ps = true → ∀ p ∈ ps,
      Derivable (Lift Th 2) (blkW (FreeMonoid.ofList p.1)) (blkW (FreeMonoid.ofList p.2))
  | [], [], _, p, hp => absurd hp (List.not_mem_nil)
  | q :: qs, p' :: ps, h, p, hp => by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [← h.1.1, ← h.1.2]; exact q.proof
    · exact check_mem qs ps h.2 p hp
  | [], _ :: _, h, _, _ => by simp [check] at h
  | _ :: _, [], h, _, _ => by simp [check] at h

theorem circ_check : check circ brels = true := by decide +kernel

/-- Every block relation holds for the circuits. -/
theorem brel_circ {a b : BW} (h : BRel a b) : Derivable (Lift Th 2) (blkW a) (blkW b) :=
  check_mem circ brels circ_check _ h

/-- An equation of blocks holds for their circuits. -/
theorem toCirc {a b : BW} (h : Derivable BRel a b) : Derivable (Lift Th 2) (blkW a) (blkW b) :=
  derivable_map_of _ BRel blkW (fun _ _ r => brel_circ r) h

/-! ### The encoding -/

open QCert.BianSelingerUn in
/-- The encoding of the generators on two wires. -/
def e : QCert.Gen Gate 2 → FreeMonoid (Option (QCert.BianSelingerUn.Gen 4))
  | .gate0 .ω => wl
  | .gate1 .H => wl * FreeMonoid.of (some (.K 0 1 (by decide))) * FreeMonoid.of (some (.K 2 3 (by decide)))
  | .gate1 .S => FreeMonoid.of (some (.i 1)) * FreeMonoid.of (some (.i 3))
  | .gate2 .CS => FreeMonoid.of (some (.i 3))
  | .gate2 .swap => FreeMonoid.of (some (.X 1 2 (by decide)))
  | .up (.gate0 .ω) => wl
  | .up (.gate1 .H) =>
    wl * FreeMonoid.of (some (.K 0 2 (by decide))) * FreeMonoid.of (some (.K 1 3 (by decide)))
  | .up (.gate1 .S) => FreeMonoid.of (some (.i 2)) * FreeMonoid.of (some (.i 3))
  | .up (.up (.gate0 .ω)) => wl

theorem e_ok : ∀ g : QCert.Gen Gate 2,
    ofMat (d := 2) (k := 2) (FreeMonoid.lift (matR UN.matU) (e g)) =
      QOmega.invSqrt2 ^ scaled.exGen g • (scaled.ops.gen g).map ZOmega.toQ
  | .gate0 .ω => by decide +kernel
  | .gate1 .H => by decide +kernel
  | .gate1 .S => by decide +kernel
  | .gate2 .CS => by decide +kernel
  | .gate2 .swap => by decide +kernel
  | .up (.gate0 .ω) => by decide +kernel
  | .up (.gate1 .H) => by decide +kernel
  | .up (.gate1 .S) => by decide +kernel
  | .up (.up (.gate0 .ω)) => by decide +kernel

theorem gi_eq : FreeMonoid.lift (UN.matU (m := 4)) (UN.gi 4) = QOmega.I • 1 := by decide +kernel

/-! ### The decoding -/

/-- The decoding of the refined generators in dimension `4`. -/
def D : FreeMonoid (Option (QCert.BianSelingerUn.Gen 4)) →* Circuit Gate 2 := blkW.comp DB

/-- Every refined relation decodes to a derivable equation. -/
theorem rel_derivable {a b : FreeMonoid (Option (QCert.BianSelingerUn.Gen 4))}
    (r : RRel (QCert.BianSelingerUn.Rel 4) (UN.gi 4) a b) : Derivable (Lift Th 2) (D a) (D b) :=
  toCirc (rel_dec r)

private theorem de {g : QCert.Gen Gate 2} {L R : List Blk}
    (hL : DB (e g) = FreeMonoid.ofList L) (hR : blkW (FreeMonoid.ofList R) = FreeMonoid.of g)
    (h : Derivable BRel (FreeMonoid.ofList L) (FreeMonoid.ofList R)) :
    Derivable (Lift Th 2) (D (e g)) (FreeMonoid.of g) := by
  have := toCirc h
  rw [← hL, hR] at this
  exact this

/-- Decoding the encoding of a generator derives it. -/
theorem DE_gen : ∀ g : QCert.Gen Gate 2, Derivable (Lift Th 2) (D (e g)) (FreeMonoid.of g)
  | .gate0 .ω => Derivable.refl _
  | .gate1 .H => de (by decide) (by decide) de_H0
  | .gate1 .S => de (by decide) (by decide) de_S0
  | .gate2 .CS => Derivable.refl _
  | .gate2 .swap => de (by decide) (by decide) de_swap
  | .up (.gate0 .ω) => (Derivable.of (Lift.scalar Gate.ω)).symm
  | .up (.gate1 .H) => de (by decide) (by decide) de_H1
  | .up (.gate1 .S) => de (by decide) (by decide) de_S1
  | .up (.up (.gate0 .ω)) => scalar_up2 (n := 0) Gate.ω

end W2

/-- Theorem 22 (5) on two wires, from the completeness of Bian and Selinger's
presentation in dimension `4`. -/
theorem complete₂_of_source
    (hsrc : ∀ a b : Word (QCert.BianSelingerUn.Gen 4),
      FreeMonoid.lift (QCert.BianSelingerUn.sem 4) a =
        FreeMonoid.lift (QCert.BianSelingerUn.sem 4) b →
        Derivable (QCert.BianSelingerUn.Rel 4) a b)
    (w v : Circuit Gate 2) (h : sem.sem 2 w = sem.sem 2 v) : pres.Proves 2 w v :=
  complete_of_flat (n := 2) scaled sem sem_toOps (Lift Th 2)
    (RRel (QCert.BianSelingerUn.Rel 4) (UN.gi 4))
    ((QOmega.toC.mapMatrix : Matrix (Fin 4) (Fin 4) QOmega →+* Matrix (Fin 4) (Fin 4) ℂ).toMonoidHom.comp
      (FreeMonoid.lift (matR UN.matU)))
    (MonoidHom.id _) Function.injective_id (matR UN.matU)
    (fun y => by rw [MonoidHom.id_apply, MonoidHom.comp_apply, FreeMonoid.lift_eval_of]; rfl)
    W2.e W2.e_ok W2.D
    (fun a b hab => refine_complete (UN.complete_Q hsrc) UN.sound_Q W2.gi_eq UN.matU_even
      (UN.lift_ne_zero (by norm_num)) a b (UN.mapC_injective hab))
    (fun _ _ hab => derivable_map_of _ _ W2.D (fun _ _ r => W2.rel_derivable r) hab)
    (derivable_lift_comp W2.e W2.D W2.DE_gen) w v h

end QCert.Minimality.CliffordCS
