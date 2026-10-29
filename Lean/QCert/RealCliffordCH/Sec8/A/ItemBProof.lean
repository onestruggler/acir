/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b) of the Reidemeister–Schreier theorem

Every relation of Figure 6 is in the congruence of Claim B (`item_b_proof`).
Through Clément's relations: the pullback `GC n` of the congruence along
`tr` contains (1)–(19) (`relK_gc`), (20) (`gb20`, from Equation (45)) and
(21) (`gb21`, from Equation (46)), hence all of Clément's relations
(`gc_rel`); a relation of Figure 6 is a consequence of Clément's relations
between the included words (`Clement2019.fig6_to_rel`), and `tr` undoes the
inclusion (`Clement2019.tr_ι`).
-/
import QCert.RealCliffordCH.Sec8.A.ItemB21

namespace QCert.RealCliffordCH.Sec8

open FreeMonoid QCert.HadamardPi

variable {n : ℕ}

/-- `tr` of a Clément word on the first indices. -/
theorem tr_first {k : ℕ} (hk : k ≤ 2 ^ n) {L : List (Clement2019.RL k)}
    {w : Word (Clement2019.Gen (2 ^ n))}
    (hw : w.toList.map Clement2019.Gen.raw = L.map (Clement2019.RL.map (Fin.castLE hk))) :
    Clement2019.tr w =
      wmap (Fin.castLE hk) (Fin.strictMono_castLE hk) (ofList (Clement2019.trL L)) := by
  rw [Clement2019.tr_eq, hw, Clement2019.trL_map _ (Fin.strictMono_castLE hk), wmap_ofList]

/-- A Clément relation on the first indices, from its image over `𝒢`. -/
theorem gc_first {k : ℕ} (hk : k ≤ 2 ^ n) {L R : List (Clement2019.RL k)}
    {w v : Word (Clement2019.Gen (2 ^ n))}
    (hw : w.toList.map Clement2019.Gen.raw = L.map (Clement2019.RL.map (Fin.castLE hk)))
    (hv : v.toList.map Clement2019.Gen.raw = R.map (Clement2019.RL.map (Fin.castLE hk)))
    (h : GB n (wmap (Fin.castLE hk) (Fin.strictMono_castLE hk) (ofList (Clement2019.trL L)))
      (wmap (Fin.castLE hk) (Fin.strictMono_castLE hk) (ofList (Clement2019.trL R)))) :
    GC n w v := by
  show GB n (Clement2019.tr w) (Clement2019.tr v)
  rw [tr_first hk hw, tr_first hk hv]
  exact h

/-- Every relation of Clément's is in `GC n`. -/
theorem gc_rel (hn : 3 ≤ n) {w v : Word (Clement2019.Gen (2 ^ n))} (h : Clement2019.Rel w v) :
    GC n w v := by
  cases h with
  | r1 j => exact relK_gc hn (Clement2019.RelK.r1 j)
  | r2 h => exact relK_gc hn (Clement2019.RelK.r2 h)
  | r3 h => exact relK_gc hn (Clement2019.RelK.r3 h)
  | r4 h => exact relK_gc hn (Clement2019.RelK.r4 h)
  | r5 h1 h2 h3 => exact relK_gc hn (Clement2019.RelK.r5 h1 h2 h3)
  | r6 h1 h2 h3 => exact relK_gc hn (Clement2019.RelK.r6 h1 h2 h3)
  | r7 h1 h2 h3 h4 h5 h6 => exact relK_gc hn (Clement2019.RelK.r7 h1 h2 h3 h4 h5 h6)
  | r8 h1 h2 h3 h4 h5 h6 => exact relK_gc hn (Clement2019.RelK.r8 h1 h2 h3 h4 h5 h6)
  | r9 h1 h2 h3 h4 h5 h6 => exact relK_gc hn (Clement2019.RelK.r9 h1 h2 h3 h4 h5 h6)
  | r10 h => exact relK_gc hn (Clement2019.RelK.r10 h)
  | r11 h => exact relK_gc hn (Clement2019.RelK.r11 h)
  | r12 h1 h2 h3 => exact relK_gc hn (Clement2019.RelK.r12 h1 h2 h3)
  | r13 h1 h2 h3 => exact relK_gc hn (Clement2019.RelK.r13 h1 h2 h3)
  | r14 h1 h2 h3 => exact relK_gc hn (Clement2019.RelK.r14 h1 h2 h3)
  | r15 h1 h2 h3 => exact relK_gc hn (Clement2019.RelK.r15 h1 h2 h3)
  | r16 h => exact relK_gc hn (Clement2019.RelK.r16 h)
  | r17 h => exact relK_gc hn (Clement2019.RelK.r17 h)
  | r18 h => exact relK_gc hn (Clement2019.RelK.r18 h)
  | r19 h1 h2 h3 h4 h5 => exact relK_gc hn (Clement2019.RelK.r19 h1 h2 h3 h4 h5)
  | r20 h4 =>
    refine gc_first h4 (L := Clement2019.sch20.1) (R := Clement2019.sch20.2) rfl rfl ?_
    have e1 : Clement2019.trL Clement2019.sch20.1 =
        [hL 0 1, hL 0 2, hL 1 3, hL 0 1, zL 0, zL 1, hL 0 2, hL 1 3] := by decide +kernel
    have e2 : Clement2019.trL Clement2019.sch20.2 =
        [hL 0 2, hL 1 3, hL 0 1, zL 0, zL 1, hL 0 2, hL 1 3, hL 0 1] := by decide +kernel
    rw [e1, e2, wmap_ofList, wmap_ofList]
    have m := Fin.strictMono_castLE h4
    exact gb20 hn (a := Fin.castLE h4 0) (b := Fin.castLE h4 1) (c := Fin.castLE h4 2)
      (d := Fin.castLE h4 3) (m (by decide)) (m (by decide)) (m (by decide))
      ((Fin.castLE_injective h4).ne (by decide)) ((Fin.castLE_injective h4).ne (by decide))
  | r21 h6 =>
    refine gc_first h6 (L := Clement2019.sch21.1) (R := Clement2019.sch21.2) rfl rfl ?_
    have e1 : Clement2019.trL Clement2019.sch21.1 = c21L := by decide +kernel
    have e2 : Clement2019.trL Clement2019.sch21.2 = c21R := by decide +kernel
    rw [e1, e2]
    exact gb21 hn h6
  | r22 h2 =>
    exfalso
    have := h8_of hn
    omega

/-- **Hypothesis (b)**: every relation of Figure 6 is in the congruence of Claim B. -/
theorem item_b_proof (n : ℕ) (hn : 3 ≤ n) : ItemB n := by
  intro c w w' h
  have h1 := Clement2019.fig6_to_rel (Derivable.of h)
  have h2 : GC n (Clement2019.ι w) (Clement2019.ι w') :=
    (Con.conGen_le fun x y hxy => gc_rel hn hxy) h1
  change GB n (Clement2019.tr _) (Clement2019.tr _) at h2
  rw [Clement2019.tr_ι, Clement2019.tr_ι] at h2
  exact (show rsRel (tauA n) (Fig8 n) w w' from h2) c

end QCert.RealCliffordCH.Sec8
