/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rules (36) and (37)

The left-hand side `H_[a,b]H_[c,d]`, its Gray codes of the form
`(x0y0z, x1y0z, x0y1z, x1y1z)` (resp. `(x0y0z, x0y1z, x1y0z, x1y1z)`), decodes
to the multi-controlled `H` with its box on the wire `w` and its `H` on the
wire `u` (resp. the other way round), coloured by `G(a)` (Definition 8.3).
The right-hand side `𝒲₁` (resp. `𝒲₂`) of Appendix A.4.1 decodes, as the paper
says, to the gadget `D(H_[0,1]H_[3,2])` conjugated by swaps and `X` gates:
`D(E_{k,ℓ}(swap))` is the swap of the wires `ℓ, ℓ + 1` and `D(ℰ⁰(X))` is `X`
(`E/Swap36`).  The `X` gates colour the controls of the gadget by (81) and the
swaps move it by (307), (313), (353) (`placedBy_mc`); the network of `𝒲₁`, `𝒲₂`
carries the wire `0` to `u` (resp. `w`), the wire `1` to `w` (resp. `u`), and
the other wires back to their places in order (`pos_netW`), which is the
placement of Definition 8.3.  Checked numerically first (`gen/sec8/e/m36.py`).
-/
import QCert.RealCliffordCH.Sec8.E.Swap36

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## The networks of `𝒲₁` and `𝒲₂` -/

/-- The swaps carrying the wire `m + 1` up to `m + 1 + ℓ`. -/
def netA (m ℓ : ℕ) : List ℕ := (List.range ℓ).map (m + 1 + ·)

/-- The swaps carrying the wires `0`, `1` up to `m`, `m + 1`. -/
def netB (m : ℕ) : List ℕ := (List.range m).flatMap fun j => [j + 1, j]

/-- The network of `𝒲₁` (`kind = 1`) and `𝒲₂`, in the order the wires move
when the gadget is carried to its place. -/
def netW (kind m ℓ : ℕ) : List ℕ := ((if kind = 1 then [0] else []) ++ netB m) ++ netA m ℓ

theorem pos_netA (m ℓ q : ℕ) : pos (netA m ℓ) q =
    if q = m + 1 then m + 1 + ℓ else if m + 1 < q ∧ q ≤ m + 1 + ℓ then q - 1 else q := by
  induction ℓ with
  | zero =>
    simp only [netA, List.range_zero, List.map_nil, pos_nil]
    split_ifs <;> omega
  | succ ℓ ih =>
    have e : netA m (ℓ + 1) = netA m ℓ ++ [m + 1 + ℓ] := by
      simp [netA, List.range_succ]
    rw [e, pos_append, ih]
    simp only [pos_cons, pos_nil, Net.tau]
    split_ifs <;> omega

theorem pos_netB (m q : ℕ) : pos (netB m) q =
    if q = 0 then m else if q = 1 then m + 1 else if q ≤ m + 1 then q - 2 else q := by
  induction m with
  | zero =>
    simp only [netB, List.range_zero, List.flatMap_nil, pos_nil]
    split_ifs <;> omega
  | succ m ih =>
    have e : netB (m + 1) = netB m ++ [m + 1, m] := by
      simp [netB, List.range_succ, List.flatMap_append]
    rw [e, pos_append, ih]
    simp only [pos_cons, pos_nil, Net.tau]
    split_ifs <;> omega

theorem pos_mid (kind q : ℕ) (hq : 2 ≤ q) : pos (if kind = 1 then [0] else []) q = q := by
  split_ifs
  · simp only [pos_cons, pos_nil, Net.tau]; split_ifs <;> omega
  · rfl

/-- Where the network of `𝒲₁`/`𝒲₂` carries the wires `0`, `1` and the others. -/
theorem pos_netW_zero (kind m ℓ : ℕ) :
    pos (netW kind m ℓ) 0 = if kind = 1 then m + 1 + ℓ else m := by
  rw [netW, pos_append, pos_append]
  split_ifs with hk
  · simp only [pos_cons, pos_nil, Net.tau]
    rw [pos_netB, pos_netA]; simp
  · rw [show pos ([] : List ℕ) 0 = 0 from rfl, pos_netB, pos_netA]; simp

theorem pos_netW_one (kind m ℓ : ℕ) :
    pos (netW kind m ℓ) 1 = if kind = 1 then m else m + 1 + ℓ := by
  rw [netW, pos_append, pos_append]
  split_ifs with hk
  · simp only [pos_cons, pos_nil, Net.tau]
    rw [pos_netB, pos_netA]; simp
  · rw [show pos ([] : List ℕ) 1 = 1 from rfl, pos_netB, pos_netA]; simp

theorem pos_netW_ge (kind m ℓ q : ℕ) (hq : 2 ≤ q) :
    pos (netW kind m ℓ) q = if q ≤ m + 1 then q - 2 else if q ≤ m + 1 + ℓ then q - 1 else q := by
  rw [netW, pos_append, pos_append, pos_mid kind q hq, pos_netB, pos_netA]
  split_ifs <;> omega

/-! ## The left-hand side -/

theorem patt_bounds {n a b c d k u w : ℕ} (hp : patt n a b c d = some (k, u, w)) :
    w < u ∧ u < n := by
  unfold patt at hp
  obtain ⟨u', hu', hp'⟩ := List.exists_of_findSome?_eq_some hp
  obtain ⟨w', hw', hp''⟩ := List.exists_of_findSome?_eq_some hp'
  simp only at hp''
  split_ifs at hp'' <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp'' <;>
    obtain ⟨-, rfl, rfl⟩ := hp'' <;> simp at hu' hw' <;> omega

theorem dec_patt {n a b c d k u w : ℕ} (hn : 3 ≤ n) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n)
    (hd : d < 2 ^ n) (h : Distinct4 a b c d) (hp : patt n a b c d = some (k, u, w)) :
    dec n (Hh n a b c d) = if k = 1 then mc n .hg [w, u] (ctl2Of (gray a) w u)
      else mc n .hg [u, w] (ctl2Of (gray a) u w) := by
  obtain ⟨hwu, hun⟩ := patt_bounds hp
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [show Hh (n' + 2) a b c d = .hh (ix (n' + 2) a) (ix (n' + 2) b) (ix (n' + 2) c)
    (ix (n' + 2) d) from rfl, dec_hh_val h ha hb hc hd]
  simp only [dHH4, hp]
  split_ifs with hk
  · rw [← placeAt2_mc n' (gray a) w u (by omega) hun (by omega)]
    congr 1
    funext j; exact Bool.or_comm _ _
  · exact placeAt2_mc n' (gray a) u w hun (by omega) (by omega)

/-! ## The right-hand side -/

/-- `E_{n-j-2,j}(swap)`, the encoded swap of the wires `j`, `j + 1`. -/
abbrev encS (n j : ℕ) : List (PG (2 ^ n)) := encSwap n (n - j - 2) j

/-- The decoded negation of the wire `n - j - 1`, if any. -/
def xOpt (n ga u w j : ℕ) : Circ n := if restBit n ga u w j = 1 then xAt n (n - j - 1) else 1

theorem dec_flatMap {α : Type*} {n : ℕ} (l : List α) (f : α → List (PG (2 ^ n))) (g : α → Circ n)
    (h : ∀ a ∈ l, Derivable (theory n) (decW n (wordOf (f a))) (g a)) :
    Derivable (theory n) (decW n (wordOf (l.flatMap f))) (l.map g).prod := by
  induction l with
  | nil => simp [decW_wordOf]; exact Derivable.refl _
  | cons a l ihl =>
    rw [List.flatMap_cons, decW_append, List.map_cons, List.prod_cons]
    exact dmul (h a (by simp)) (ihl (fun b hb => h b (by simp [hb])))

theorem prod_map_ite {n : ℕ} (l : List ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → Circ n) :
    (l.map fun j => if p j then f j else 1).prod = ((l.filter fun j => decide (p j)).map f).prod := by
  induction l with
  | nil => rfl
  | cons a l ihl =>
    by_cases hp : p a
    · simp [hp, ihl]
    · simp [hp, ihl]

section RHS

variable {M : ℕ} (ih : IH (M + 3))
include ih

theorem dec_net (l : List ℕ) (hl : ∀ j ∈ l, j + 2 ≤ M + 3) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (l.flatMap (encS (M + 3)))))
      (swW (M + 3) l.reverse) := by
  refine (dec_flatMap l _ (swAt (M + 3)) (fun j hj => dec_encSwap ih _ j (by
    have := hl j hj; omega))).trans (der_of_eq ?_)
  rw [swW_eq_drawn]
  simp [drawn, List.map_reverse]

theorem dec_neg (ga u w j : ℕ) (hj : j < M + 1) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf (encNeg (M + 3) j (M + 3 - j - 1) (1 - restBit (M + 3) ga u w j))))
      (xOpt (M + 3) ga u w j) := by
  unfold xOpt
  have hb : restBit (M + 3) ga u w j < 2 := by unfold restBit; exact bitOf_lt_two _ _
  rcases (show restBit (M + 3) ga u w j = 0 ∨ restBit (M + 3) ga u w j = 1 by omega) with h0 | h1
  · rw [h0, if_neg (by omega)]
    simp [encNeg, decW_wordOf]; exact Derivable.refl _
  · rw [h1, if_pos rfl]
    exact dec_encNeg ih j (M + 3 - j - 1) (by omega)

end RHS

/-! ## The word `𝒲₁`, `𝒲₂` in blocks -/

theorem wW_eq (n kind ga u w : ℕ) :
    wW n kind ga u w = (netW kind w (u - w - 1)).reverse.flatMap (encS n) ++
      ((List.range (n - 2)).reverse.flatMap fun j => encNeg n j (n - j - 1) (1 - restBit n ga u w j)) ++
      [Hh n 0 1 3 2] ++
      ((List.range (n - 2)).flatMap fun j => encNeg n j (n - j - 1) (1 - restBit n ga u w j)) ++
      (netW kind w (u - w - 1)).flatMap (encS n) := by
  have hB : ∀ m, (List.range m).reverse.flatMap (fun j => encSwap n (n - j - 2) j ++
      encSwap n (n - j - 3) (j + 1)) = (netB m).reverse.flatMap (encS n) := by
    intro m
    rw [netB, List.reverse_flatMap, List.flatMap_assoc]
    apply List.flatMap_congr
    intro j _
    rw [show n - j - 3 = n - (j + 1) - 2 by omega]
    simp [encS]
  have hB' : ∀ m, (List.range m).flatMap (fun j => encSwap n (n - j - 3) (j + 1) ++
      encSwap n (n - j - 2) j) = (netB m).flatMap (encS n) := by
    intro m
    rw [netB, List.flatMap_assoc]
    apply List.flatMap_congr
    intro j _
    rw [show n - j - 3 = n - (j + 1) - 2 by omega]
    simp [encS]
  have hA : ∀ m ℓ, (List.range ℓ).reverse.flatMap (fun i => encSwap n (n - (m + 1 + i) - 2) (m + 1 + i)) =
      (netA m ℓ).reverse.flatMap (encS n) := by
    intro m ℓ
    rw [netA, ← List.map_reverse, List.flatMap_map]
  have hA' : ∀ m ℓ, (List.range ℓ).flatMap (fun i => encSwap n (n - (m + 1 + i) - 2) (m + 1 + i)) =
      (netA m ℓ).flatMap (encS n) := by
    intro m ℓ
    rw [netA, List.flatMap_map]
  have hM : (if kind = 1 then encSwap n (n - 2) 0 else []) =
      (if kind = 1 then [0] else []).flatMap (encS n) := by
    split_ifs <;> simp [encS]
  unfold wW netW
  simp only [List.reverse_append, List.flatMap_append, ← hA, ← hA', ← hB, ← hB']
  rw [show (if kind = 1 then [0] else ([] : List ℕ)).reverse = if kind = 1 then [0] else [] by
    split_ifs <;> rfl, ← hM]
  simp only [List.append_assoc]

section Main

variable {M : ℕ} (ih : IH (M + 3))
include ih

omit ih in
theorem netW_ok (kind u w : ℕ) (hwu : w < u) (hun : u < M + 3) :
    ∀ j ∈ netW kind w (u - w - 1), j + 2 ≤ M + 3 := by
  intro j hj
  simp only [netW, netA, netB, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil] at hj
  rcases hj with (hj | ⟨a, ha, hj⟩) | ⟨a, ha, rfl⟩
  · split_ifs at hj <;> simp at hj; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
  · omega

/-- The decoded right-hand side of (36) (`kind = 1`) and (37) (`kind = 2`). -/
theorem dec_wW (kind : ℕ) (ga u w : ℕ) (hwu : w < u) (hun : u < M + 3) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (wW (M + 3) kind ga u w)))
      (mc (M + 3) .hg (if kind = 1 then [w, u] else [u, w]) (ctl2Of ga w u)) := by
  set n := M + 3 with hn
  set ν := netW kind w (u - w - 1) with hν
  have hok := netW_ok kind u w hwu hun
  have hokr : ∀ j ∈ ν.reverse, j + 2 ≤ n := fun j hj => hok j (List.mem_reverse.1 hj)
  have hOk : Ok n ν.reverse := fun j hj => hokr j hj
  set p : ℕ → Prop := fun j => restBit n ga u w j = 1
  set ws := (((List.range (n - 2)).reverse.filter fun j => decide (p j)).map fun j => n - j - 1)
    with hws
  rw [wW_eq, decW_append, decW_append, decW_append, decW_append]
  have S1 := dec_net ih ν.reverse hokr
  rw [List.reverse_reverse] at S1
  have S2 := dec_net ih ν hok
  have X1 := dec_flatMap (List.range (n - 2)).reverse _ (xOpt n ga u w)
    (fun j hj => dec_neg ih ga u w j (by simp at hj; omega))
  have X2 := dec_flatMap (List.range (n - 2)) _ (xOpt n ga u w)
    (fun j hj => dec_neg ih ga u w j (by simp at hj; omega))
  have G : decW n (wordOf [Hh n 0 1 3 2]) = mc n .hg [1, 0] (ctl2Of 0 1 0) := by
    rw [decW_wordOf]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [dec_0132 (by omega), show n = (M + 1) + 2 by omega, gadget_mc]
  rw [G]
  refine (dmul (dmul (dmul (dmul S1 X1) (Derivable.refl _)) X2) S2).trans ?_
  -- the `X` gates
  have hX1 : ((List.range (n - 2)).reverse.map (xOpt n ga u w)).prod = (ws.map (xAt n)).prod := by
    unfold xOpt
    rw [prod_map_ite, hws, List.map_map]; rfl
  have hX2 : ((List.range (n - 2)).map (xOpt n ga u w)).prod = ((ws.map (xAt n)).reverse).prod := by
    unfold xOpt
    rw [prod_map_ite, hws, List.map_map, ← List.map_reverse, List.filter_reverse,
      List.reverse_reverse]; rfl
  rw [hX1, hX2]
  have hwsnd : ws.Nodup := by
    rw [hws]
    refine List.Nodup.map_on (fun a ha b hb e => ?_)
      (List.Nodup.filter _ (List.nodup_reverse.2 List.nodup_range))
    simp only [List.mem_filter, List.mem_reverse, List.mem_range] at ha hb
    omega
  have hwsmem : ∀ J, J ∈ ws ↔ 2 ≤ J ∧ J < n ∧ p (n - 1 - J) := by
    intro J
    rw [hws]
    simp only [List.mem_map, List.mem_filter, List.mem_reverse, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨j, ⟨hj, hpj⟩, rfl⟩
      exact ⟨by omega, by omega, by rw [show n - 1 - (n - j - 1) = j by omega]; exact hpj⟩
    · rintro ⟨h2, hJ, hpJ⟩
      exact ⟨n - 1 - J, ⟨by omega, hpJ⟩, by omega⟩
  have rc := recolour (N := n) .hg [1, 0] ws (ctl2Of 0 1 0) hwsnd (fun J hJ => by
    obtain ⟨h2, hJn, _⟩ := (hwsmem J).1 hJ
    refine ⟨hJn, by simp; omega, ?_⟩
    simp [ctl2Of, show J ≠ 1 by omega, show J ≠ 0 by omega])
  have erc : drawn (ws.map (xAt n) ++ [mc n .hg [1, 0] (ctl2Of 0 1 0)] ++ (ws.map (xAt n)).reverse) =
      (ws.map (xAt n)).prod * mc n .hg [1, 0] (ctl2Of 0 1 0) * ((ws.map (xAt n)).reverse).prod := by
    simp [drawn, List.reverse_append, mul_assoc]
  rw [erc] at rc
  -- the swaps: the conjugation by the network
  have ep : swW n ν * (ws.map (xAt n)).prod * mc n .hg [1, 0] (ctl2Of 0 1 0) *
      ((ws.map (xAt n)).reverse).prod * swW n ν.reverse =
      placedBy n ν.reverse ((ws.map (xAt n)).prod * mc n .hg [1, 0] (ctl2Of 0 1 0) *
        ((ws.map (xAt n)).reverse).prod) := by
    unfold placedBy; rw [List.reverse_reverse]; simp only [mul_assoc]
  rw [ep]
  refine (placedBy_cong _ rc).trans ?_
  have pm := placedBy_mc (mcSwapAll ih) ν.reverse hOk .hg [1, 0] (flipOn ws (ctl2Of 0 1 0)) rfl
    (by simp) (by simp; omega)
  rw [List.reverse_reverse] at pm
  refine pm.trans (der_of_eq ?_)
  have hT : [1, 0].map (pos ν) = if kind = 1 then [w, u] else [u, w] := by
    simp only [List.map_cons, List.map_nil, hν, pos_netW_zero, pos_netW_one]
    split_ifs <;> simp <;> omega
  rw [hT]
  refine Net.mc_congr _ _ _ (fun j hj => ?_)
  set J := pos ν.reverse j with hJ
  have hJn : J < n := pos_lt _ hOk j hj
  have hJj : pos ν J = j := pos_reverse' ν j
  simp only [Function.comp]
  rw [← hJ]
  rcases (show J = 0 ∨ J = 1 ∨ 2 ≤ J by omega) with h0 | h1 | h2
  · rw [h0] at hJj
    rw [hν, pos_netW_zero] at hJj
    have hnot : (0 : ℕ) ∉ ws := fun h => by have := (hwsmem 0).1 h; omega
    rw [h0]
    simp only [flipOn, if_neg hnot, ctl2Of]
    split_ifs at hJj <;> simp <;> omega
  · rw [h1] at hJj
    rw [hν, pos_netW_one] at hJj
    have hnot : (1 : ℕ) ∉ ws := fun h => by have := (hwsmem 1).1 h; omega
    rw [h1]
    simp only [flipOn, if_neg hnot, ctl2Of]
    split_ifs at hJj <;> simp <;> omega
  · rw [hν, pos_netW_ge kind w (u - w - 1) J h2] at hJj
    have hju : j ≠ u ∧ j ≠ w := by split_ifs at hJj <;> omega
    have hb : p (n - 1 - J) ↔ bitOf ga j = 1 := by
      simp only [p, restBit]
      have e : n - 1 - (if n - 1 - J < n - 1 - u then n - 1 - J
          else if n - 1 - J + 1 < n - 1 - w then n - 1 - J + 1 else n - 1 - J + 2) = j := by
        split_ifs at hJj ⊢ <;> omega
      rw [e]
    have hc0 : ctl2Of 0 1 0 J = some false := by
      simp [ctl2Of, show J ≠ 1 by omega, show J ≠ 0 by omega, bitOf]
    simp only [flipOn, ctl2Of, if_neg (show ¬ (j = w ∨ j = u) by omega)]
    have hbz : bitOf 0 J = 0 := by simp [bitOf]
    by_cases hp : p (n - 1 - J)
    · rw [if_pos ((hwsmem J).2 ⟨h2, hJn, hp⟩)]
      simp [hb.1 hp, hbz, show J ≠ 1 by omega, show J ≠ 0 by omega]
    · rw [if_neg (fun h => hp ((hwsmem J).1 h).2.2)]
      have : bitOf ga j ≠ 1 := fun h => hp (hb.2 h)
      simp [this, hbz, show J ≠ 1 by omega, show J ≠ 0 by omega]

end Main

/-! ## The rules -/

/-- (36): the multi-controlled `H` placed and coloured by Definition 8.3 is the
gadget conjugated by the decoded `𝒲₁`. -/
theorem dec36 {M : ℕ} (ih : IH (M + 3)) (a b c d u w : ℕ) (ha : a < 2 ^ (M + 3))
    (hb : b < 2 ^ (M + 3)) (hc : c < 2 ^ (M + 3)) (hd : d < 2 ^ (M + 3)) (h : Distinct4 a b c d)
    (hp : patt (M + 3) a b c d = some (1, u, w)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Hh (M + 3) a b c d]))
      (decW (M + 3) (wordOf (wW (M + 3) 1 (gray a) u w))) := by
  obtain ⟨hwu, hun⟩ := patt_bounds hp
  rw [decW_wordOf]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [dec_patt (by omega) ha hb hc hd h hp, if_pos rfl]
  have := dec_wW ih 1 (gray a) u w hwu hun
  rw [if_pos rfl] at this
  exact this.symm

/-- (37): the same with `𝒲₂`. -/
theorem dec37 {M : ℕ} (ih : IH (M + 3)) (a b c d u w : ℕ) (ha : a < 2 ^ (M + 3))
    (hb : b < 2 ^ (M + 3)) (hc : c < 2 ^ (M + 3)) (hd : d < 2 ^ (M + 3)) (h : Distinct4 a b c d)
    (hp : patt (M + 3) a b c d = some (2, u, w)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Hh (M + 3) a b c d]))
      (decW (M + 3) (wordOf (wW (M + 3) 2 (gray a) u w))) := by
  obtain ⟨hwu, hun⟩ := patt_bounds hp
  rw [decW_wordOf]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [dec_patt (by omega) ha hb hc hd h hp, if_neg (by decide)]
  have := dec_wW ih 2 (gray a) u w hwu hun
  rw [if_neg (by decide), ctl2Of_comm] at this
  exact this.symm

end QCert.RealCliffordCH.Sec8.E
