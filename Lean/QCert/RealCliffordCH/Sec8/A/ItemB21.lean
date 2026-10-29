/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b): Clément's relation (21) from Equation (46)

The relation `w46L ≈ w46R` of `ItemB46.lean` is in the congruence of Claim B
at the indices `2, …, 7`, hence at every placement (`gc46_all`, by
`gc_perm`).  Clément's (21) at `0, …, 5`, Figure 7's (d4*), is
`(-1)_[2](-1)_[3]` times that relation conjugated: `(21) ≈ Z₂₃ (46) Z₂₃`, the
conjugation by `X_[0,2]X_[1,3]` carrying `H_[0,4]H_[1,5]` to `H_[2,4]H_[3,5]`
and `H_[0,1]` to `H_[2,3]`.  Each step of that rewriting is an identity on at
most five indices (`ch21`), which the pullback of the congruence contains by
the completeness of Figure 6 on five indices, where it has (d3) but no (d4)
(`chkSound`).  So (21) is in the congruence (`gc_r21`).

The chain is generated (`.handover-scratch/thm410/ib/c21.py`, `gen21.py`),
each step checked numerically.
-/
import QCert.RealCliffordCH.Sec8.A.ItemBRel
import QCert.RealCliffordCH.Sec8.A.ItemB46

namespace QCert.RealCliffordCH.Sec8

open QCert.HadamardPi FreeMonoid Chk

/-- Clément's (21) at `0, …, 5`, over `𝒢₆`. -/
def c21L : List (HadamardPi.Gen 6) := [hL 0 1, hL 0 2, hL 1 3, hL 0 4, hL 1 5, hL 0 1, zL 0, zL 1, hL 0 4, hL 1 5, hL 0 2, hL 1 3]
/-- The right-hand side. -/
def c21R : List (HadamardPi.Gen 6) := [hL 0 2, hL 1 3, hL 0 4, hL 1 5, hL 0 1, zL 0, zL 1, hL 0 4, hL 1 5, hL 0 2, hL 1 3, hL 0 1]
/-- The relation of (46) at `0, …, 5`, the one extra equation. -/
def e46E : List (List (HadamardPi.Gen 6) × List (HadamardPi.Gen 6)) :=
  [([hL 0 1, hL 0 2, hL 1 3, hL 2 4, hL 3 5, hL 2 3, hL 4 5, hL 4 5, zL 3, zL 2, hL 2 4, hL 3 5, hL 0 2, hL 1 3],
    [hL 0 2, hL 1 3, hL 2 4, hL 3 5, zL 3, zL 2, hL 4 5, hL 2 3, hL 4 5, hL 2 4, hL 3 5, hL 0 2, hL 1 3, hL 0 1])]
/-- The chain. -/
def ch21 : List (CS 6 5) := [
  .sem ![0, 1, 2, 3, 4] [hL 0 1, hL 0 2, hL 1 3, hL 0 4] [hL 0 1, hL 0 2, hL 1 3, xL 0 2, xL 1 3, xL 0 2, xL 1 3, hL 0 4] 0,
  .sem ![0, 1, 2, 3, 5] [hL 1 4, hL 0 2, hL 1 3] [hL 1 4, xL 0 2, xL 1 3, xL 0 2, xL 1 3, hL 0 2, hL 1 3] 13,
  .sem ![0, 1, 2, 3, 4] [hL 0 1, zL 0, zL 1] [xL 0 2, xL 1 3, xL 0 2, xL 1 3, hL 0 1, xL 0 2, xL 1 3, xL 0 2, xL 1 3, zL 0, zL 1, xL 0 2, xL 1 3, xL 0 2, xL 1 3] 9,
  .sem ![0, 1, 2, 3, 4] [hL 0 2, hL 1 3, xL 0 2, xL 1 3] [zL 2, zL 3, hL 0 2, hL 1 3] 1,
  .sem ![0, 1, 2, 3, 4] [xL 1 3, hL 0 4] [hL 0 4, xL 1 3] 6,
  .sem ![0, 1, 2, 3, 4] [xL 0 2, xL 1 3, xL 0 2] [xL 1 3] 9,
  .sem ![0, 1, 2, 3, 5] [xL 1 3, hL 1 4, xL 1 3] [hL 3 4] 7,
  .sem ![0, 1, 2, 3, 4] [xL 0 2, hL 0 4] [hL 2 4, xL 0 2] 5,
  .sem ![0, 1, 2, 3, 5] [xL 0 2, hL 3 4] [hL 3 4, xL 0 2] 6,
  .sem ![0, 1, 2, 3, 4] [xL 0 2, xL 1 3, hL 0 1, xL 0 2, xL 1 3] [hL 2 3] 7,
  .sem ![0, 1, 2, 3, 4] [xL 0 2, xL 1 3, zL 0, zL 1, xL 0 2, xL 1 3] [zL 2, zL 3] 8,
  .sem ![0, 1, 2, 3, 4] [xL 1 3, hL 0 4] [hL 0 4, xL 1 3] 11,
  .sem ![0, 1, 2, 3, 4] [xL 0 2, xL 1 3, xL 0 2] [xL 1 3] 14,
  .sem ![0, 1, 2, 3, 5] [xL 1 3, hL 1 4, xL 1 3] [hL 3 4] 12,
  .sem ![0, 1, 2, 3, 4] [xL 0 2, hL 0 4] [hL 2 4, xL 0 2] 10,
  .sem ![0, 1, 2, 3, 5] [xL 0 2, hL 3 4] [hL 3 4, xL 0 2] 11,
  .sem ![0, 1, 2, 3, 4] [xL 0 2, xL 1 3, hL 0 2, hL 1 3] [hL 0 2, hL 1 3, zL 2, zL 3] 12,
  .sem ![0, 1, 2, 3, 4] [hL 0 1, zL 2, zL 3] [zL 2, zL 3, hL 0 1] 0,
  .sem ![0, 1, 2, 4, 5] [] [hL 3 4, hL 3 4] 8,
  .sem ![0, 1, 2, 3, 4] [zL 2, zL 3] [zL 3, zL 2] 10,
  .ext 0 2 true,
  .sem ![0, 1, 2, 3, 4] [zL 3, zL 2] [zL 2, zL 3] 6,
  .sem ![0, 2, 3, 4, 5] [hL 3 4, hL 1 2, hL 3 4] [hL 1 2] 8,
  .sem ![0, 1, 2, 3, 4] [zL 2, zL 3, hL 2 3] [hL 2 3, zL 2, zL 3] 6,
  .sem ![0, 1, 2, 3, 4] [hL 0 1, zL 2, zL 3] [zL 2, zL 3, hL 0 1] 13,
  .sem ![0, 1, 2, 3, 4] [hL 0 2, hL 1 3, zL 2, zL 3] [xL 0 2, xL 1 3, hL 0 2, hL 1 3] 11,
  .sem ![0, 1, 2, 3, 5] [hL 3 4, xL 0 2] [xL 0 2, hL 3 4] 10,
  .sem ![0, 1, 2, 3, 4] [hL 2 4, xL 0 2] [xL 0 2, hL 0 4] 9,
  .sem ![0, 1, 2, 3, 5] [hL 3 4] [xL 1 3, hL 1 4, xL 1 3] 11,
  .sem ![0, 1, 2, 3, 4] [xL 1 3] [xL 0 2, xL 1 3, xL 0 2] 13,
  .sem ![0, 1, 2, 3, 4] [hL 0 4, xL 1 3] [xL 1 3, hL 0 4] 10,
  .sem ![0, 1, 2, 3, 4] [zL 2, zL 3] [xL 0 2, xL 1 3, zL 0, zL 1, xL 0 2, xL 1 3] 7,
  .sem ![0, 1, 2, 3, 4] [hL 2 3] [xL 0 2, xL 1 3, hL 0 1, xL 0 2, xL 1 3] 6,
  .sem ![0, 1, 2, 3, 5] [hL 3 4, xL 0 2] [xL 0 2, hL 3 4] 5,
  .sem ![0, 1, 2, 3, 4] [hL 2 4, xL 0 2] [xL 0 2, hL 0 4] 4,
  .sem ![0, 1, 2, 3, 5] [hL 3 4] [xL 1 3, hL 1 4, xL 1 3] 6,
  .sem ![0, 1, 2, 3, 4] [xL 1 3] [xL 0 2, xL 1 3, xL 0 2] 8,
  .sem ![0, 1, 2, 3, 4] [hL 0 4, xL 1 3] [xL 1 3, hL 0 4] 5,
  .sem ![0, 1, 2, 3, 4] [zL 2, zL 3, hL 0 2, hL 1 3] [hL 0 2, hL 1 3, xL 0 2, xL 1 3] 0,
  .sem ![0, 1, 2, 3, 4] [xL 0 2, xL 1 3, xL 0 2, xL 1 3, hL 0 1, xL 0 2, xL 1 3, xL 0 2, xL 1 3, zL 0, zL 1, xL 0 2, xL 1 3, xL 0 2, xL 1 3, hL 0 4] [hL 0 1, zL 0, zL 1, hL 0 4] 8,
  .sem ![0, 1, 2, 3, 5] [hL 1 4, xL 0 2, xL 1 3, xL 0 2, xL 1 3, hL 0 2, hL 1 3, hL 0 1] [hL 1 4, hL 0 2, hL 1 3, hL 0 1] 12,
  .sem ![0, 1, 2, 3, 4] [xL 0 2, xL 1 3, xL 0 2, xL 1 3] [] 2]
theorem run21 : Chk.run e46E ch21 c21L = some c21R := by decide +kernel
variable {n : ℕ}

/-- The relation of (46) on Clément's generators. -/
def W46CL : List (Clement2019.Gen 6) := [c 0 1, c 0 2, c 1 3, c 2 4, c 3 5, c 2 3, c 4 5, c 4 5,
  .Z 3, .Z 2, c 2 4, c 3 5, c 0 2, c 1 3]
where c (a b : Fin 6) (h : a ≠ b := by decide) : Clement2019.Gen 6 := .H a b h

/-- The right-hand side. -/
def W46CR : List (Clement2019.Gen 6) := [W46CL.c 0 2, W46CL.c 1 3, W46CL.c 2 4, W46CL.c 3 5, .Z 3,
  .Z 2, W46CL.c 4 5, W46CL.c 2 3, W46CL.c 4 5, W46CL.c 2 4, W46CL.c 3 5, W46CL.c 0 2,
  W46CL.c 1 3, W46CL.c 0 1]

theorem raw_map {k m : ℕ} (f : Fin k → Fin m) (hf : Function.Injective f) (g : Clement2019.Gen k) :
    (g.map f hf).raw = g.raw.map f := by
  cases g <;> rfl

/-- `tr` of a Clément word moved along an increasing map. -/
theorem tr_wmapC {k : ℕ} (f : Fin k → Fin (2 ^ n)) (hf : StrictMono f) (l : List (Clement2019.Gen k)) :
    Clement2019.tr (Clement2019.wmapC f hf.injective (ofList l)) =
      wmap f hf (ofList (Clement2019.trL (l.map Clement2019.Gen.raw))) := by
  rw [Clement2019.wmapC_ofList, Clement2019.tr_ofList, List.map_map]
  have e : (Clement2019.Gen.raw ∘ Clement2019.Gen.map f hf.injective) =
      (Clement2019.RL.map f ∘ Clement2019.Gen.raw) := funext fun g => raw_map f hf.injective g
  rw [e, ← List.map_map, Clement2019.trL_map f hf, wmap_ofList]

theorem trL_W46L : Clement2019.trL (W46CL.map Clement2019.Gen.raw) = W46L := by decide +kernel
theorem trL_W46R : Clement2019.trL (W46CR.map Clement2019.Gen.raw) = W46R := by decide +kernel

/-- The relation of (46) at the indices `2, …, 7`, in `GC n`. -/
theorem gc46 (hn : 3 ≤ n) :
    GC n (Clement2019.wmapC (f27 hn) (f27_mono hn).injective (ofList W46CL))
      (Clement2019.wmapC (f27 hn) (f27_mono hn).injective (ofList W46CR)) := by
  show GB n (Clement2019.tr _) (Clement2019.tr _)
  rw [tr_wmapC _ (f27_mono hn), tr_wmapC _ (f27_mono hn), trL_W46L, trL_W46R, wmap_ofList,
    wmap_ofList]
  exact gb46 hn

/-- The relation of (46) at every injective placement, in `GC n`. -/
theorem gc46_all (hn : 3 ≤ n) (f : Fin 6 → Fin (2 ^ n)) (hf : Function.Injective f) :
    GC n (Clement2019.wmapC f hf (ofList W46CL)) (Clement2019.wmapC f hf (ofList W46CR)) :=
  gc_place hn _ (gc46 hn) f hf

/-- Clément's (21) at `0, …, 5`, over `𝒢_{2ⁿ}`, is in `GB n`. -/
theorem gb21 (hn : 3 ≤ n) (h6 : 6 ≤ 2 ^ n) :
    GB n (wmap (Fin.castLE h6) (Fin.strictMono_castLE h6) (ofList c21L))
      (wmap (Fin.castLE h6) (Fin.strictMono_castLE h6) (ofList c21R)) := by
  refine Chk.run_sound (chkSound hn le_rfl (Fin.castLE h6) (Fin.strictMono_castLE h6)
    (fun f hf => d3At_all hn _ _) ?_) ch21 run21
  intro p hp
  simp only [e46E, List.mem_singleton] at hp
  subst hp
  have k := gc46_all hn (Fin.castLE h6) (Fin.castLE_injective h6)
  change GB n (Clement2019.tr _) (Clement2019.tr _) at k
  rw [tr_wmapC _ (Fin.strictMono_castLE h6), tr_wmapC _ (Fin.strictMono_castLE h6), trL_W46L,
    trL_W46R] at k
  exact k

end QCert.RealCliffordCH.Sec8
