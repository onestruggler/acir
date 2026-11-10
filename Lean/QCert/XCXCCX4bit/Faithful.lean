/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The circuits that keep a wire, and their faithfulness

Translation of `Faithful.agda`.  A placed letter keeps wire `m` when its
target is another wire, and a word of letters that each keep wire `m` acts
on the 16 states as a permutation that preserves that wire's bit.
`Faithful m` says that the theory decides those words: two of them with the
same function are equal.  The subgroup that keeps wire 3 is the paper's
`K`, and faithfulness of `K` gives faithfulness for every wire
(`faithful`), by the relabelling `τ m` that exchanges wires `m` and 3, as
`Placed.narrow` does for the three-wire circuits; that `τ m` takes a letter
keeping wire `m` to one keeping wire 3 is decided for all letters
(`keeps_τ_check`).
-/
import QCert.XCXCCX4bit.Placed

namespace QCert.XCXCCX4bit.Faithful

open QCert QCert.Circuit CircuitProp IndepProp
open Coxeter Coxeter.Circuits Placed

/-! ## Targets -/

def target : PG → Wire
  | .Xₚ t => t
  | .CXₚ _ t _ => t
  | .CCXₚ _ _ t _ => t

/-- The letter does not change wire `m`. -/
def keeps (m : Wire) (g : PG) : Bool := !weq m (target g)

theorem every_append (p : PG → Bool) (xs ys : List PG) (hx : every p xs = true)
    (hy : every p ys = true) : every p (xs ++ ys) = true := by
  rw [every_iff] at hx hy ⊢
  intro x hx'
  rcases List.mem_append.1 hx' with h | h
  exacts [hx x h, hy x h]

/-- A word whose letters target `a` or `b` keeps every other wire. -/
def targets (a b : Wire) (g : PG) : Bool := weq (target g) a || weq (target g) b

theorem keep_by (m a b x : Wire) (h : (weq x a || weq x b) = true) (ha : (!weq m a) = true)
    (hb : (!weq m b) = true) : (!weq m x) = true := by
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rwa [weq_sound h]
  · rwa [weq_sound h]

theorem keeps_from (m a b : Wire) : ∀ xs : List PG, every (targets a b) xs = true →
    (!weq m a) = true → (!weq m b) = true → every (keeps m) xs = true
  | [], _, _, _ => rfl
  | x :: xs, h, ha, hb => by
    simp only [every, Bool.and_eq_true] at h ⊢
    exact ⟨keep_by m a b (target x) h.1 ha hb, keeps_from m a b xs h.2 ha hb⟩

/-! ## Relabelling: `τ m` takes a letter that keeps wire `m` to one that keeps
wire 3 (decided once for all letters and wires) -/

/-- `a` implies `b`, as a Boolean. -/
def imp (a b : Bool) : Bool := !a || b

theorem imp_sound {a b : Bool} (h : imp a b = true) (ha : a = true) : b = true := by
  subst ha; exact h

theorem keeps_τ_check : ∀ m : Wire,
    forallPG (fun g => imp (keeps m g) (keeps 3 (relabel (τ m) g))) = true
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | 2 => by decide +kernel
  | 3 => by decide +kernel

theorem keeps_τ (m : Wire) (g : PG) (h : keeps m g = true) : keeps 3 (relabel (τ m) g) = true :=
  imp_sound (forallPG_sound _ (keeps_τ_check m) g) h

theorem every_keeps_τ (m : Wire) : ∀ u : List PG, every (keeps m) u = true →
    every (keeps 3) (u.map (relabel (τ m))) = true
  | [], _ => rfl
  | g :: u, h => by
    simp only [every, Bool.and_eq_true, List.map_cons] at h ⊢
    exact ⟨keeps_τ m g h.1, every_keeps_τ m u h.2⟩

/-! ## Faithfulness -/

set_option linter.dupNamespace false in
/-- The theory decides the words that keep wire `m`. -/
def Faithful (m : Wire) : Prop :=
  ∀ u v : List PG, every (keeps m) u = true → every (keeps m) v = true →
    semPs u ≐ semPs v → 4 ⊢ ιs u ≈ ιs v

/-- Faithfulness for wire 3 is faithfulness for every wire. -/
theorem faithful (f₃ : Faithful 3) (m : Wire) : Faithful m := by
  intro u v hu hv e
  have hu' := every_keeps_τ m u hu
  have hv' := every_keeps_τ m v hv
  have eu := relabel_ιs (τ m) u
  have ev := relabel_ιs (τ m) v
  have e' : sem (ιs u) ≐ sem (ιs v) := feq_trans (ιs_sem u) (feq_trans e (feq_sym (ιs_sem v)))
  have mid : sem (S (τ m) * ιs u * Sinv (τ m)) ≐ sem (S (τ m) * ιs v * Sinv (τ m)) := fun x => by
    simp only [sem_mul]
    rw [e' (sem (S (τ m)) x)]
  have sem' : semPs (u.map (relabel (τ m))) ≐ semPs (v.map (relabel (τ m))) :=
    feq_trans (feq_sym (ιs_sem _)) (feq_trans (sound eu) (feq_trans mid
      (feq_trans (feq_sym (sound ev)) (ιs_sem _))))
  exact unconj (Sinv_S (τ m)) (eu.symm.trans ((f₃ _ _ hu' hv' sem').trans ev))

end QCert.XCXCCX4bit.Faithful
