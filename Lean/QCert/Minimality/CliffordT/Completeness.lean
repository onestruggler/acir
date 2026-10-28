/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of CliffT₂ up to two qubits (Theorem 22 (4))

Theorem 21 for CliffT₂ at each width up to two:

* on two wires from Bian and Selinger's presentation of the two-qubit
  Clifford+T operators (`complete₂_of_source`, Appendices D, F.4, G.4),
  whose relations, stated in the order of matrix multiplication, the paper
  draws left to right: the decoding reads them reversed, and the encoding
  is reversed too, every gate's matrix being symmetric (`complete_of_flat_rev`);
* on one wire and none from Greylyn's presentation of `Uₘ(ℤ[1/√2, i])` in
  dimensions `2` and `1` (`complete₁_of_source`, `complete₀_of_source`),
  which the paper leaves implicit.

Each takes the completeness of its source as a hypothesis, so that the
transfer does not depend on how the source is proved; `complete` combines
them with the sources' theorems into completeness up to two wires.
-/
import QCert.Minimality.CliffordT.Derivations
import QCert.Minimality.CliffordT.Soundness
import QCert.CliffordT2.Theorem
import QCert.Greylyn.Theorem

namespace QCert.Minimality.CliffordT

open Matrix QCert.Circuit

/-- Theorem 22 (4) on two wires, from the completeness of Bian and
Selinger's presentation. -/
theorem complete₂_of_source
    (hsrc : ∀ a b : Word QCert.CliffordT2.Gen,
      FreeMonoid.lift QCert.CliffordT2.sem a = FreeMonoid.lift QCert.CliffordT2.sem b →
        Derivable QCert.CliffordT2.Rel a b)
    (w v : Circuit Gate 2) (h : sem.sem 2 w = sem.sem 2 v) : pres.Proves 2 w v :=
  complete_of_flat_rev (n := 2) scaled sem sem_toOps (Lift Th 2) QCert.CliffordT2.Rel
    (FreeMonoid.lift QCert.CliffordT2.sem) (unitaryGroup (Fin 4) ℂ).subtype Subtype.val_injective
    QCert.CliffordT2.matQ BS.matQ_symm (fun y => by rw [FreeMonoid.lift_eval_of]; rfl) BS.e BS.e_ok
    BS.D hsrc (fun _ _ r => BS.rel_derivable r) (derivable_lift_comp BS.e BS.D BS.DE_gen) w v h

/-- Theorem 22 (4) on one wire, from the completeness of Greylyn's
presentation in dimension `2`. -/
theorem complete₁_of_source
    (hsrc : ∀ a b : Word (QCert.Greylyn.Gen 2),
      FreeMonoid.lift (QCert.Greylyn.sem 2) a = FreeMonoid.lift (QCert.Greylyn.sem 2) b →
        Derivable (QCert.Greylyn.Rel 2) a b)
    (w v : Circuit Gate 1) (h : sem.sem 1 w = sem.sem 1 v) : pres.Proves 1 w v :=
  complete_of_flat (n := 1) scaled sem sem_toOps (Lift Th 1) (QCert.Greylyn.Rel 2)
    (FreeMonoid.lift (QCert.Greylyn.sem 2)) (GL.κ 2) (GL.κ_injective 2) GL.matG GL.κ_sem
    GL.e₁ GL.e₁_ok GL.D₁ hsrc
    (fun _ _ hab => derivable_map_of _ _ GL.D₁ (fun _ _ r => GL.rel_derivable₁ r) hab)
    (derivable_lift_comp GL.e₁ GL.D₁ GL.DE₁_gen) w v h

/-- Theorem 22 (4) with no wire, from the completeness of Greylyn's
presentation in dimension `1`. -/
theorem complete₀_of_source
    (hsrc : ∀ a b : Word (QCert.Greylyn.Gen 1),
      FreeMonoid.lift (QCert.Greylyn.sem 1) a = FreeMonoid.lift (QCert.Greylyn.sem 1) b →
        Derivable (QCert.Greylyn.Rel 1) a b)
    (w v : Circuit Gate 0) (h : sem.sem 0 w = sem.sem 0 v) : pres.Proves 0 w v :=
  complete_of_flat (n := 0) scaled sem sem_toOps (Lift Th 0) (QCert.Greylyn.Rel 1)
    (FreeMonoid.lift (QCert.Greylyn.sem 1)) (GL.κ 1) (GL.κ_injective 1) GL.matG GL.κ_sem
    GL.e₀ GL.e₀_ok GL.D₀ hsrc
    (fun _ _ hab => derivable_map_of _ _ GL.D₀ (fun _ _ r => GL.rel_derivable₀ r) hab)
    (derivable_lift_comp GL.e₀ GL.D₀ GL.DE₀_gen) w v h

/-- Theorem 22 (4), the transfer: CliffT₂ is complete up to two wires as
soon as Bian and Selinger's presentation and Greylyn's in dimensions `1`
and `2` are. -/
theorem complete_of_source
    (h₂ : ∀ a b : Word QCert.CliffordT2.Gen,
      FreeMonoid.lift QCert.CliffordT2.sem a = FreeMonoid.lift QCert.CliffordT2.sem b →
        Derivable QCert.CliffordT2.Rel a b)
    (h₁ : ∀ a b : Word (QCert.Greylyn.Gen 2),
      FreeMonoid.lift (QCert.Greylyn.sem 2) a = FreeMonoid.lift (QCert.Greylyn.sem 2) b →
        Derivable (QCert.Greylyn.Rel 2) a b)
    (h₀ : ∀ a b : Word (QCert.Greylyn.Gen 1),
      FreeMonoid.lift (QCert.Greylyn.sem 1) a = FreeMonoid.lift (QCert.Greylyn.sem 1) b →
        Derivable (QCert.Greylyn.Rel 1) a b) :
    pres.CompleteUpTo (fun n => sem.sem n) 2 := by
  intro n hn w v h
  match n, hn with
  | 0, _ => exact complete₀_of_source h₀ w v h
  | 1, _ => exact complete₁_of_source h₁ w v h
  | 2, _ => exact complete₂_of_source h₂ w v h

/-- Theorem 22 (4): CliffT₂ is complete for Clifford+T circuits up to two
wires, given Bian and Selinger's Theorem 2.1 and Greylyn's Theorem 22. -/
theorem complete : pres.CompleteUpTo (fun n => sem.sem n) 2 :=
  complete_of_source (fun _ _ h => QCert.CliffordT2.theorem_2_1.complete h)
    (fun _ _ h => (QCert.Greylyn.presentation 2 (by norm_num)).complete h)
    (fun _ _ h => (QCert.Greylyn.presentation 1 (by norm_num)).complete h)

end QCert.Minimality.CliffordT
