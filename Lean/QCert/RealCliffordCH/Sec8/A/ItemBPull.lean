/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b): pulling the congruence back to few indices

Along a strictly increasing `g : Fin k → Fin 2ⁿ`, the congruence of Claim B
pulls back to a congruence on the words of `Fin k`.  It contains every
instance of (a1)–(d2) (`gb_rule`), hence, when `k ≤ 5` and the congruence
contains (d3), every relation of Figure 6 on `Fin k` (`pull_fig6`; (d4) needs
six indices), hence by the completeness of Figure 6 on `k` indices every
pair of words with the same matrix (`sound_sem`).  That is what makes the
chains of `ItemBChk.lean` sound in it (`chkSound`).
-/
import QCert.RealCliffordCH.Sec8.A.ItemBCon
import QCert.RealCliffordCH.Sec8.A.ItemBChk

namespace QCert.RealCliffordCH.Sec8

open QCert.HadamardPi FreeMonoid

variable {n : ℕ}

theorem wmap_comp {k m N : ℕ} (f : Fin k → Fin m) (hf : StrictMono f) (g : Fin m → Fin N)
    (hg : StrictMono g) (w : Word (HadamardPi.Gen k)) :
    wmap g hg (wmap f hf w) = wmap (g ∘ f) (hg.comp hf) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of x w ih =>
    rw [map_mul, map_mul, map_mul, ih]
    cases x <;> rfl

/-- Every instance of (a1)–(d2), moved along `g`, is in `GB`. -/
theorem gb_rule (hn : 3 ≤ n) {m : ℕ} (g : Fin m → Fin (2 ^ n)) (hg : StrictMono g) {t : Tag}
    {ix : List (Fin m)} {P Q : List (HadamardPi.Gen m)} (hb : Chk.bigTag t = false)
    (h : ruleG t ix = some (P, Q)) : GB n (wmap g hg (ofList P)) (wmap g hg (ofList Q)) := by
  rw [wmap_ofList, wmap_ofList]
  revert hb
  unfold ruleG at h
  split at h <;> (try split_ifs at h with hc) <;> (try simp only [Option.some.injEq,
    Prod.mk.injEq, reduceCtorEq] at h) <;> (try obtain ⟨rfl, rfl⟩ := h) <;> intro hb
  · exact gb_a1 hn _
  · exact gb_a2 hn (hg hc)
  · exact gb_a3 hn (hg hc)
  · exact gb_b1 hn (fun e => hc (hg.injective e))
  · exact gb_b2 hn (hg hc.1) (fun e => hc.2.1 (hg.injective e)) (fun e => hc.2.2 (hg.injective e))
  · exact gb_b3 hn (hg hc.1) (hg hc.2.1) (fun e => hc.2.2.1 (hg.injective e))
      (fun e => hc.2.2.2.1 (hg.injective e)) (fun e => hc.2.2.2.2.1 (hg.injective e))
      (fun e => hc.2.2.2.2.2 (hg.injective e))
  · exact gb_b4 hn (hg hc.1) (fun e => hc.2.1 (hg.injective e)) (fun e => hc.2.2 (hg.injective e))
  · exact gb_b5 hn (hg hc.1) (hg hc.2.1) (fun e => hc.2.2.1 (hg.injective e))
      (fun e => hc.2.2.2.1 (hg.injective e)) (fun e => hc.2.2.2.2.1 (hg.injective e))
      (fun e => hc.2.2.2.2.2 (hg.injective e))
  · exact gb_b6 hn (hg hc.1) (hg hc.2.1) (fun e => hc.2.2.1 (hg.injective e))
      (fun e => hc.2.2.2.1 (hg.injective e)) (fun e => hc.2.2.2.2.1 (hg.injective e))
      (fun e => hc.2.2.2.2.2 (hg.injective e))
  · exact gb_c1 hn (hg hc)
  · exact gb_c2 hn (hg hc.1) (hg hc.2)
  · exact gb_c3 hn (hg hc.1) (hg hc.2)
  · exact gb_c4 hn (hg hc.1) (hg hc.2)
  · exact gb_c5 hn (hg hc.1) (hg hc.2)
  · exact gb_d1 hn (hg hc)
  · exact gb_d2 hn (hg hc)
  · simp [Chk.bigTag] at hb
  · simp [Chk.bigTag] at hb

/-- (d3) at four indices of `Fin k`, moved along `g`. -/
def D3At {k : ℕ} (n : ℕ) (g : Fin k → Fin (2 ^ n)) (hg : StrictMono g) : Prop :=
  ∀ {a b c d : Fin k} (hab : a < b) (hcd : c < d) (hac : a < c) (hbd : b < d), b ≠ c →
    GB n (wmap g hg ((H_[c,d] * H_[a,c] * H_[b,d]) ^ 4)) (wmap g hg (H_[a,b] * H_[c,d]))

/-- There is no instance of (d3) on three indices. -/
theorem d3At_three {k : ℕ} (hk : k ≤ 3) (g : Fin k → Fin (2 ^ n)) (hg : StrictMono g) :
    D3At n g hg := by
  intro a b c d hab hcd hac hbd hbc
  exfalso
  have := d.2
  simp only [Fin.lt_def, ne_eq, Fin.ext_iff] at hab hcd hac hbd hbc
  omega

/-- Every relation of Figure 6 on at most five indices, moved along `g`, is in `GB`
when (d3) is. -/
theorem pull_fig6 (hn : 3 ≤ n) {k : ℕ} (hk : k ≤ 5) (g : Fin k → Fin (2 ^ n))
    (hg : StrictMono g) (hd3 : D3At n g hg) {w v : Word (HadamardPi.Gen k)} (h : Fig6 w v) :
    GB n (wmap g hg w) (wmap g hg v) := by
  have ne : ∀ {a b : Fin k}, a ≠ b → g a ≠ g b := fun h e => h (hg.injective e)
  cases h with
  | a1 a => exact gb_a1 hn (g a)
  | a2 h => exact gb_a2 hn (hg h)
  | a3 h => exact gb_a3 hn (hg h)
  | b1 h => exact gb_b1 hn (ne h)
  | b2 hbc hab hac => exact gb_b2 hn (hg hbc) (ne hab) (ne hac)
  | b3 hab hcd hac had hbc hbd =>
    exact gb_b3 hn (hg hab) (hg hcd) (ne hac) (ne had) (ne hbc) (ne hbd)
  | b4 hbc hab hac => exact gb_b4 hn (hg hbc) (ne hab) (ne hac)
  | b5 hab hcd hac had hbc hbd =>
    exact gb_b5 hn (hg hab) (hg hcd) (ne hac) (ne had) (ne hbc) (ne hbd)
  | b6 hab hcd hac had hbc hbd =>
    exact gb_b6 hn (hg hab) (hg hcd) (ne hac) (ne had) (ne hbc) (ne hbd)
  | c1 h => exact gb_c1 hn (hg h)
  | c2 hab hbc => exact gb_c2 hn (hg hab) (hg hbc)
  | c3 hab hbc => exact gb_c3 hn (hg hab) (hg hbc)
  | c4 hab hbc => exact gb_c4 hn (hg hab) (hg hbc)
  | c5 hab hbc => exact gb_c5 hn (hg hab) (hg hbc)
  | d1 h => exact gb_d1 hn (hg h)
  | d2 h => exact gb_d2 hn (hg h)
  | d3 hab hcd hac hbd hbc => exact hd3 hab hcd hac hbd hbc
  | @d4 a b c d e f hac hbd hab hce hdf hef hbc hbe hcd hde =>
    exfalso
    have := f.2
    simp only [Fin.lt_def, ne_eq, Fin.ext_iff] at hac hbd hab hce hdf hef hbc hbe hcd hde
    omega

/-- Words of `Fin K` with the same matrix are related, moved along `f`, in a congruence
that contains the relations of Figure 6 moved along `f`. -/
theorem sound_sem {m K : ℕ} (c : Con (Word (HadamardPi.Gen m)))
    (hfig : ∀ (f : Fin K → Fin m) (hf : StrictMono f) (w v : Word (HadamardPi.Gen K)), Fig6 w v →
      c (wmap f hf w) (wmap f hf v))
    (f : Fin K → Fin m) (hf : StrictMono f) (W R : List (HadamardPi.Gen K))
    (h : wordMat invSqrt2 (ofList W) = wordMat invSqrt2 (ofList R)) :
    c (ofList (W.map (HadamardPi.Gen.map f hf))) (ofList (R.map (HadamardPi.Gen.map f hf))) := by
  have hs : FreeMonoid.lift (sem K) (ofList W) = FreeMonoid.lift (sem K) (ofList R) := by
    apply Subtype.ext; apply Subtype.ext
    rw [lift_sem_val, lift_sem_val, h]
  have hd := (theorem_4_14 K).complete hs
  have hle : conGen (Fig6 (n := K)) ≤ c.comap (wmap f hf) (map_mul _) :=
    Con.conGen_le fun x y hxy => hfig f hf x y hxy
  have := hle hd
  rwa [Con.comap_rel, wmap_ofList, wmap_ofList] at this

/-- The pullback of `GB` along `g`. -/
def pullGB (n : ℕ) {m : ℕ} (g : Fin m → Fin (2 ^ n)) (hg : StrictMono g) : Con (Word (HadamardPi.Gen m)) :=
  (GB n).comap (wmap g hg) (map_mul _)

/-- Chains with semantic steps on `K ≤ 5` indices are sound in the pullback, given (d3)
and the extra equations. -/
theorem chkSound (hn : 3 ≤ n) {m K : ℕ} (hK : K ≤ 5) (g : Fin m → Fin (2 ^ n))
    (hg : StrictMono g)
    (hd3 : ∀ (f : Fin K → Fin m) (hf : StrictMono f), D3At n (g ∘ f) (hg.comp hf))
    {E : List (List (HadamardPi.Gen m) × List (HadamardPi.Gen m))}
    (hE : ∀ p ∈ E, GB n (wmap g hg (ofList p.1)) (wmap g hg (ofList p.2))) :
    Chk.Sound (pullGB n g hg) K E where
  rel t ix P Q hb h := gb_rule hn g hg hb h
  sem := sound_sem _ (fun f hf w v h => by
    show GB n (wmap g hg (wmap f hf w)) (wmap g hg (wmap f hf v))
    rw [wmap_comp, wmap_comp]
    exact pull_fig6 hn hK (g ∘ f) (hg.comp hf) (hd3 f hf) h)
  ext p hp := hE p hp

end QCert.RealCliffordCH.Sec8
