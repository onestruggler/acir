/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (65) at every tuple of distinct indices

For a tuple whose Gray codes have the form of (36) or (37), the word `𝒲₁` or
`𝒲₂` of Appendix A.4.1 is `U Λ U'` (`wW_eq`), where `U` is a product of
swap encodings (`sop_encSwap`) and negations (`sop_encNeg`) and `U'` lists
the same blocks in the other order.  As signed permutations of the basis
states `U` is the composite `F` of the negations (writing the bitstring
`x y z` of the tuple on the wires `2, …, n - 1`), the swap of the wires
`0, 1` for (36), and the swap networks carrying the wires `0, 1` to the
two distinguished wires `u > w` (`bit_F`); so `U` sends the indices
`0, 1, 3, 2` (the states `00, 01, 10, 11`) to `a, b, c, d`, with no sign,
and `U U'` is the identity: `U, U'` is a frame (`frame_wW`).  With
`frame_eq` this gives (65) from (36), (37) (`e65_patt`), and with
`e65_of_35`, (65) at every tuple of distinct indices (`e65`).
-/
import QCert.RealCliffordCH.Sec8.A.E65Blocks

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

theorem SOp.app0 {B₁ B₂ : List (PG (2 ^ n))} {f₁ f₂ : ℕ → ℕ} (h₁ : SOp n B₁ f₁ fun _ => false)
    (h₂ : SOp n B₂ f₂ fun _ => false) : SOp n (B₁ ++ B₂) (f₁ ∘ f₂) fun _ => false :=
  (SOp.append h₁ h₂).congr (fun _ _ => rfl) (fun _ _ => rfl)

/-! ## The pieces of `𝒲₁`, `𝒲₂` -/

/-- The swaps carrying wire `m + 1` up by `ℓ` wires. -/
def fSL (m : ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | i + 1 => swapB (m + 1 + i) ∘ fSL m i

def fSL' (m : ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | i + 1 => fSL' m i ∘ swapB (m + 1 + i)

/-- The swaps carrying the wires `0, 1` up by `m` wires. -/
def fSM : ℕ → ℕ → ℕ
  | 0 => id
  | j + 1 => (swapB j ∘ swapB (j + 1)) ∘ fSM j

def fSM' : ℕ → ℕ → ℕ
  | 0 => id
  | j + 1 => fSM' j ∘ (swapB (j + 1) ∘ swapB j)

/-- The swap of the wires `0, 1` in `𝒲₁`. -/
def fMID (kind : ℕ) : ℕ → ℕ := if kind = 1 then swapB 0 else id

/-- The negation of `𝒲₁`, `𝒲₂` on the wire `n - j - 1`. -/
def gN (n ga u w j : ℕ) : ℕ → ℕ := if 1 - restBit n ga u w j = 1 then id else flipB (n - j - 1)

def fNG (n ga u w : ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | j + 1 => gN n ga u w j ∘ fNG n ga u w j

def fNG' (n ga u w : ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | j + 1 => fNG' n ga u w j ∘ gN n ga u w j

theorem sop_SL (hn : 3 ≤ n) (m : ℕ) : ∀ ℓ, m + 1 + ℓ < n →
    SOp n ((List.range ℓ).reverse.flatMap fun i => encSwap n (n - (m + 1 + i) - 2) (m + 1 + i))
        (fSL m ℓ) (fun _ => false) ∧
      SOp n ((List.range ℓ).flatMap fun i => encSwap n (n - (m + 1 + i) - 2) (m + 1 + i))
        (fSL' m ℓ) (fun _ => false)
  | 0, _ => ⟨SOp.nil, SOp.nil⟩
  | ℓ + 1, h => by
    obtain ⟨ih1, ih2⟩ := sop_SL hn m ℓ (by omega)
    have hb := sop_encSwap hn (k := n - (m + 1 + ℓ) - 2) (ℓ := m + 1 + ℓ) (by omega)
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton, List.flatMap_append,
      List.flatMap_singleton, List.singleton_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact ⟨SOp.app0 hb ih1, SOp.app0 ih2 hb⟩

theorem sop_SM (hn : 3 ≤ n) : ∀ m, m + 2 ≤ n →
    SOp n ((List.range m).reverse.flatMap fun j => encSwap n (n - j - 2) j ++
        encSwap n (n - j - 3) (j + 1)) (fSM m) (fun _ => false) ∧
      SOp n ((List.range m).flatMap fun j => encSwap n (n - j - 3) (j + 1) ++
        encSwap n (n - j - 2) j) (fSM' m) (fun _ => false)
  | 0, _ => ⟨SOp.nil, SOp.nil⟩
  | m + 1, h => by
    obtain ⟨ih1, ih2⟩ := sop_SM hn m (by omega)
    have hb := sop_encSwap hn (k := n - m - 2) (ℓ := m) (by omega)
    have hb' := sop_encSwap hn (k := n - m - 3) (ℓ := m + 1) (by omega)
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton, List.flatMap_append,
      List.flatMap_singleton, List.singleton_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact ⟨SOp.app0 (SOp.app0 hb hb') ih1, SOp.app0 ih2 (SOp.app0 hb' hb)⟩

theorem sop_NG (hn : 3 ≤ n) (ga u w : ℕ) : ∀ K, K ≤ n →
    SOp n ((List.range K).reverse.flatMap fun j => encNeg n j (n - j - 1) (1 - restBit n ga u w j))
        (fNG n ga u w K) (fun _ => false) ∧
      SOp n ((List.range K).flatMap fun j => encNeg n j (n - j - 1) (1 - restBit n ga u w j))
        (fNG' n ga u w K) (fun _ => false)
  | 0, _ => ⟨SOp.nil, SOp.nil⟩
  | K + 1, h => by
    obtain ⟨ih1, ih2⟩ := sop_NG hn ga u w K (by omega)
    have hb := sop_encNeg hn (k := K) (ℓ := n - K - 1) (x := 1 - restBit n ga u w K) (by omega)
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton, List.flatMap_append,
      List.flatMap_singleton, List.singleton_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact ⟨SOp.app0 hb ih1, SOp.app0 ih2 hb⟩

theorem sop_MID (hn : 3 ≤ n) (kind : ℕ) :
    SOp n (if kind = 1 then encSwap n (n - 2) 0 else []) (fMID kind) (fun _ => false) := by
  unfold fMID
  split_ifs
  · exact sop_encSwap hn (by omega)
  · exact SOp.nil

/-! ## The inverse -/

theorem fSL_inv (m : ℕ) : ∀ ℓ s, fSL m ℓ (fSL' m ℓ s) = s
  | 0, _ => rfl
  | ℓ + 1, s => by
    simp only [fSL, fSL', Function.comp_apply]; rw [fSL_inv m ℓ, swapB_swapB]

theorem fSM_inv : ∀ m s, fSM m (fSM' m s) = s
  | 0, _ => rfl
  | m + 1, s => by
    simp only [fSM, fSM', Function.comp_apply]; rw [fSM_inv m, swapB_swapB, swapB_swapB]

theorem gN_inv (n ga u w j s : ℕ) : gN n ga u w j (gN n ga u w j s) = s := by
  unfold gN; split_ifs
  · rfl
  · exact flipB_flipB _ _

theorem fNG_inv (ga u w : ℕ) : ∀ K s, fNG n ga u w K (fNG' n ga u w K s) = s
  | 0, _ => rfl
  | K + 1, s => by
    simp only [fNG, fNG', Function.comp_apply]; rw [fNG_inv ga u w K, gN_inv]

theorem fMID_inv (kind s : ℕ) : fMID kind (fMID kind s) = s := by
  unfold fMID; split_ifs
  · exact swapB_swapB _ _
  · rfl

/-! ## Bits -/

/-- Where `fSL m ℓ` reads the bit it puts on wire `q`. -/
def sigL (m ℓ q : ℕ) : ℕ := if m + 1 ≤ q ∧ q < m + 1 + ℓ then q + 1 else if q = m + 1 + ℓ then m + 1 else q

/-- Where `fSM m` reads the bit it puts on wire `q`. -/
def rhoM (m q : ℕ) : ℕ := if q < m then q + 2 else if q = m then 0 else if q = m + 1 then 1 else q

theorem bit_fSL (m : ℕ) : ∀ ℓ s q, bit q (fSL m ℓ s) = bit (sigL m ℓ q) s
  | 0, s, q => by
    rw [show sigL m 0 q = q by unfold sigL; split_ifs <;> omega]; rfl
  | ℓ + 1, s, q => by
    show bit q (swapB (m + 1 + ℓ) (fSL m ℓ s)) = _
    rw [bit_swapB, bit_fSL m ℓ]
    congr 1
    unfold sigL tauB; split_ifs <;> omega

theorem bit_fSM : ∀ m s q, bit q (fSM m s) = bit (rhoM m q) s
  | 0, s, q => by
    rw [show rhoM 0 q = q by unfold rhoM; split_ifs <;> omega]; rfl
  | m + 1, s, q => by
    show bit q (swapB m (swapB (m + 1) (fSM m s))) = _
    rw [bit_swapB, bit_swapB, bit_fSM m]
    congr 1
    unfold rhoM tauB; split_ifs <;> omega

theorem bit_fMID (kind s q : ℕ) :
    bit q (fMID kind s) = bit (if kind = 1 then tauB 0 q else q) s := by
  unfold fMID; split_ifs
  · exact bit_swapB 0 s q
  · rfl

theorem restBit_lt (ga u w j : ℕ) : restBit n ga u w j < 2 := by
  unfold restBit bitOf; exact Nat.mod_lt _ (by norm_num)

theorem bit_fNG (ga u w : ℕ) : ∀ K, K ≤ n → ∀ s q, bit q (fNG n ga u w K s) =
    if q < n ∧ n - 1 - q < K ∧ restBit n ga u w (n - 1 - q) = 1 then 1 - bit q s else bit q s
  | 0, _, s, q => by simp [fNG]
  | K + 1, hK, s, q => by
    have ih := bit_fNG ga u w K (by omega) s
    show bit q (gN n ga u w K (fNG n ga u w K s)) = _
    have hr := restBit_lt (n := n) ga u w K
    unfold gN
    by_cases hq : q = n - K - 1
    · subst hq
      have e : n - 1 - (n - K - 1) = K := by omega
      rcases (by omega : restBit n ga u w K = 0 ∨ restBit n ga u w K = 1) with r | r
      · rw [if_pos (by omega), id, ih, e, r]
        simp
      · rw [if_neg (by omega), bit_flipB_self, ih, e, r]
        simp [show n - K - 1 < n by omega]
    · have hb : ∀ X, bit q ((if 1 - restBit n ga u w K = 1 then id else flipB (n - K - 1)) X) =
          bit q X := by
        intro X; split_ifs
        · rfl
        · exact bit_flipB_ne X hq
      rw [hb, ih]
      by_cases hqn : q < n
      · have : n - 1 - q ≠ K := by omega
        by_cases h1 : n - 1 - q < K
        · simp [hqn, h1, show n - 1 - q < K + 1 by omega]
        · simp [hqn, h1, show ¬ n - 1 - q < K + 1 by omega]
      · simp [hqn]


/-! ## The halves of `𝒲₁`, `𝒲₂` -/

/-- The first half of `𝒲₁` (`kind = 1`) or `𝒲₂` (`kind = 2`). -/
def wU (n kind ga u w : ℕ) : List (PG (2 ^ n)) :=
  ((List.range (u - w - 1)).reverse.flatMap fun i => encSwap n (n - (w + 1 + i) - 2) (w + 1 + i)) ++
  ((List.range w).reverse.flatMap fun j => encSwap n (n - j - 2) j ++ encSwap n (n - j - 3) (j + 1)) ++
  (if kind = 1 then encSwap n (n - 2) 0 else []) ++
  ((List.range (n - 2)).reverse.flatMap fun j => encNeg n j (n - j - 1) (1 - restBit n ga u w j))

/-- The second half of `𝒲₁`, `𝒲₂`. -/
def wU' (n kind ga u w : ℕ) : List (PG (2 ^ n)) :=
  ((List.range (n - 2)).flatMap fun j => encNeg n j (n - j - 1) (1 - restBit n ga u w j)) ++
  (if kind = 1 then encSwap n (n - 2) 0 else []) ++
  ((List.range w).flatMap fun j => encSwap n (n - j - 3) (j + 1) ++ encSwap n (n - j - 2) j) ++
  ((List.range (u - w - 1)).flatMap fun i => encSwap n (n - (w + 1 + i) - 2) (w + 1 + i))

theorem wW_eq (kind ga u w : ℕ) :
    wW n kind ga u w = wU n kind ga u w ++ Lam n :: wU' n kind ga u w := by
  simp only [wW, wU, wU', Lam, List.append_assoc, List.cons_append, List.singleton_append,
    List.nil_append]

/-- The basis states as `wU` permutes them. -/
def fW (n kind ga u w : ℕ) : ℕ → ℕ :=
  fSL w (u - w - 1) ∘ fSM w ∘ fMID kind ∘ fNG n ga u w (n - 2)

def fW' (n kind ga u w : ℕ) : ℕ → ℕ :=
  fNG' n ga u w (n - 2) ∘ fMID kind ∘ fSM' w ∘ fSL' w (u - w - 1)

theorem fW_inv (kind ga u w s : ℕ) : fW n kind ga u w (fW' n kind ga u w s) = s := by
  simp only [fW, fW', Function.comp_apply]
  rw [fNG_inv, fMID_inv, fSM_inv, fSL_inv]

theorem sop_wU (hn : 3 ≤ n) {kind ga u w : ℕ} (hu : u < n) (hw : w < u) :
    SOp n (wU n kind ga u w) (fW n kind ga u w) (fun _ => false) ∧
      SOp n (wU' n kind ga u w) (fW' n kind ga u w) (fun _ => false) := by
  obtain ⟨l1, l2⟩ := sop_SL hn w (u - w - 1) (by omega)
  obtain ⟨m1, m2⟩ := sop_SM hn w (by omega)
  obtain ⟨n1, n2⟩ := sop_NG hn ga u w (n - 2) (by omega)
  have md := sop_MID hn kind
  exact ⟨(SOp.app0 (SOp.app0 (SOp.app0 l1 m1) md) n1).congr (fun _ _ => rfl) (fun _ _ => rfl),
    (SOp.app0 (SOp.app0 (SOp.app0 n2 md) m2) l2).congr (fun _ _ => rfl) (fun _ _ => rfl)⟩

/-! ## The images of `0, 1, 3, 2` -/

theorem sigL_u {w u : ℕ} (hw : w < u) : sigL w (u - w - 1) u = w + 1 := by
  unfold sigL; split_ifs <;> omega

theorem sigL_lo {w u q : ℕ} (hq : q ≤ w) : sigL w (u - w - 1) q = q := by
  unfold sigL; split_ifs <;> omega

theorem sigL_mid {w u q : ℕ} (h1 : w < q) (h2 : q < u) : sigL w (u - w - 1) q = q + 1 := by
  unfold sigL; split_ifs <;> omega

theorem sigL_hi {w u q : ℕ} (hw : w < u) (h : u < q) : sigL w (u - w - 1) q = q := by
  unfold sigL; split_ifs <;> omega

theorem rhoM_lt {w x : ℕ} (h : x < w) : rhoM w x = x + 2 := by
  unfold rhoM; split_ifs <;> omega

theorem rhoM_hi {w x : ℕ} (h : w + 1 < x) : rhoM w x = x := by
  unfold rhoM; split_ifs <;> omega

theorem tauB0_hi {x : ℕ} (h : 2 ≤ x) : tauB 0 x = x := by
  unfold tauB; split_ifs <;> omega

theorem bitOf_eq_bit (v i : ℕ) : bitOf v i = bit i v := by
  unfold bitOf bit; rw [Nat.shiftRight_eq_div_pow]

theorem restBit_at {ga u w q : ℕ} (hu : u < n) (hw : w < u) (hq : q < n) (hqu : q ≠ u)
    (hqw : q ≠ w) :
    restBit n ga u w (n - 1 - (if q < w then q + 2 else if q < u then q + 1 else q)) = bit q ga := by
  simp only [restBit, bitOf_eq_bit]
  congr 1
  split_ifs <;> omega

theorem bit_fW (hn : 3 ≤ n) {kind ga u w : ℕ} (hu : u < n) (hw : w < u)
    (hk : kind = 1 ∨ kind = 2) (hga : ga < 2 ^ n) {t : ℕ} (ht : t < 4) (q : ℕ) :
    bit q (fW n kind ga u w t) =
      if q = u then bit (if kind = 1 then 0 else 1) t
      else if q = w then bit (if kind = 1 then 1 else 0) t else bit q ga := by
  simp only [fW, Function.comp_apply]
  rw [bit_fSL, bit_fSM, bit_fMID, bit_fNG ga u w (n - 2) (by omega)]
  have t2 : ∀ p, 2 ≤ p → bit p t = 0 := fun p hp => bit_of_ge (n := 2) (by norm_num; omega) hp
  have hC : ∀ π, π < 2 → ¬ (π < n ∧ n - 1 - π < n - 2 ∧ restBit n ga u w (n - 1 - π) = 1) :=
    fun π hπ h => by omega
  have hR : ∀ π, 2 ≤ π → π < n → restBit n ga u w (n - 1 - π) = bit q ga →
      (if π < n ∧ n - 1 - π < n - 2 ∧ restBit n ga u w (n - 1 - π) = 1 then 1 - bit π t
        else bit π t) = bit q ga := by
    intro π h2 hn' hr
    rw [hr, t2 π h2]
    have := bit_lt q ga
    rcases (by omega : bit q ga = 0 ∨ bit q ga = 1) with e | e
    · rw [e, if_neg (by omega)]
    · rw [e, if_pos ⟨hn', by omega, rfl⟩]
  have hrb := fun (hq : q < n) (h1 : q ≠ u) (h2 : q ≠ w) =>
    restBit_at (ga := ga) hu hw hq h1 h2
  by_cases hqu : q = u
  · subst hqu
    rw [sigL_u hw, show rhoM w (w + 1) = 1 by unfold rhoM; split_ifs <;> omega, if_pos rfl]
    have e : (if kind = 1 then tauB 0 1 else 1) = (if kind = 1 then 0 else 1) := by
      rcases hk with rfl | rfl <;> rfl
    rw [e, if_neg (hC _ (by split_ifs <;> norm_num))]
  rw [if_neg hqu]
  by_cases hqw : q = w
  · subst hqw
    rw [sigL_lo le_rfl, show rhoM q q = 0 by unfold rhoM; split_ifs <;> omega, if_pos rfl]
    have e : (if kind = 1 then tauB 0 0 else 0) = (if kind = 1 then 1 else 0) := by
      rcases hk with rfl | rfl <;> rfl
    rw [e, if_neg (hC _ (by split_ifs <;> norm_num))]
  rw [if_neg hqw]
  have hid : ∀ x, 2 ≤ x → (if kind = 1 then tauB 0 x else x) = x := fun x hx => by
    split_ifs
    · exact tauB0_hi hx
    · rfl
  rcases lt_or_gt_of_ne hqw with h1 | h1
  · -- below `w`
    have hr := hrb (by omega) hqu hqw
    rw [if_pos h1] at hr
    rw [sigL_lo h1.le, rhoM_lt h1, hid _ (by omega)]
    exact hR _ (by omega) (by omega) hr
  rcases lt_or_gt_of_ne hqu with h2 | h2
  · -- between `w` and `u`
    have hr := hrb (by omega) hqu hqw
    rw [if_neg (by omega), if_pos h2] at hr
    rw [sigL_mid h1 h2, rhoM_hi (by omega), hid _ (by omega)]
    exact hR _ (by omega) (by omega) hr
  · -- above `u`
    rw [sigL_hi hw h2, rhoM_hi (by omega), hid _ (by omega)]
    by_cases hqn : q < n
    · have hr := hrb hqn hqu hqw
      rw [if_neg (by omega), if_neg (by omega)] at hr
      exact hR _ (by omega) hqn hr
    · rw [if_neg (fun h => hqn h.1), t2 _ (by omega), bit_of_ge hga (by omega)]

/-! ## The pattern -/

theorem patt_some {a b c d kind u w : ℕ} (h : patt n a b c d = some (kind, u, w)) :
    u < n ∧ w < u ∧
    clear2 (gray a) u w = clear2 (gray b) u w ∧ clear2 (gray a) u w = clear2 (gray c) u w ∧
    clear2 (gray a) u w = clear2 (gray d) u w ∧
    bitOf (gray a) u = 0 ∧ bitOf (gray a) w = 0 ∧ bitOf (gray d) u = 1 ∧ bitOf (gray d) w = 1 ∧
    ((kind = 1 ∧ bitOf (gray b) u = 1 ∧ bitOf (gray b) w = 0 ∧ bitOf (gray c) u = 0 ∧
        bitOf (gray c) w = 1) ∨
      (kind = 2 ∧ bitOf (gray b) u = 0 ∧ bitOf (gray b) w = 1 ∧ bitOf (gray c) u = 1 ∧
        bitOf (gray c) w = 0)) := by
  unfold patt at h
  obtain ⟨u', hu', h1⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨w', hw', h2⟩ := List.exists_of_findSome?_eq_some h1
  rw [List.mem_range] at hu' hw'
  simp only at h2
  split_ifs at h2 with c1 c2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    obtain ⟨⟨s1, s2, s3⟩, ba, bb, bc, bd⟩ := c1
    simp only [Prod.mk.injEq] at ba bb bc bd
    exact ⟨hu', hw', s1, s2, s3, ba.1, ba.2, bd.1, bd.2, Or.inl ⟨rfl, bb.1, bb.2, bc.1, bc.2⟩⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    obtain ⟨⟨s1, s2, s3⟩, ba, bb, bc, bd⟩ := c2
    simp only [Prod.mk.injEq] at ba bb bc bd
    exact ⟨hu', hw', s1, s2, s3, ba.1, ba.2, bd.1, bd.2, Or.inr ⟨rfl, bb.1, bb.2, bc.1, bc.2⟩⟩

theorem clear2_eq {u w : ℕ} (huw : u ≠ w) (v : ℕ) : clear2 v u w = clr w (clr u v) := by
  unfold clear2
  rw [bitOf_eq_bit, bitOf_eq_bit, ← bit_clr_ne u w v (Ne.symm huw)]
  have h1 := clr_add_bit u v
  have h2 := clr_add_bit w (clr u v)
  omega

theorem bit_clear2 {u w q : ℕ} (huw : u ≠ w) (hqu : q ≠ u) (hqw : q ≠ w) (v : ℕ) :
    bit q (clear2 v u w) = bit q v := by
  rw [clear2_eq huw, bit_clr_ne w q _ hqw, bit_clr_ne u q _ hqu]

theorem bit_of_clear2 {u w : ℕ} (huw : u ≠ w) {v v' : ℕ} (h : clear2 v u w = clear2 v' u w)
    {βu βw : ℕ} (hu : bitOf v' u = βu) (hw : bitOf v' w = βw) (q : ℕ) :
    bit q v' = if q = u then βu else if q = w then βw else bit q v := by
  rw [bitOf_eq_bit] at hu hw
  split_ifs with h1 h2
  · subst h1; exact hu
  · subst h2; exact hw
  · rw [← bit_clear2 huw h1 h2 v, h, bit_clear2 huw h1 h2]

theorem sop_val {B : List (PG (2 ^ n))} {f : ℕ → ℕ} {σ : ℕ → Bool} (h : SOp n B f σ) {j : ℕ}
    (hj : j < 2 ^ n) : ((spW (wordOf B)).perm (ix n j) : ℕ) = gInv n (f (gray j)) ∧
      (spW (wordOf B)).neg (ix n j) = σ (gray j) := by
  have e : ix n j = gx n (gray j) := by
    rw [← gx_gray (ix n j), ix_val hj]
  obtain ⟨l, p, q⟩ := h.2 (gray j) (gray_lt hj)
  rw [e, p, gx_val l, q]
  exact ⟨rfl, rfl⟩

/-- The halves of `𝒲₁`, `𝒲₂` are a frame. -/
theorem frame_wW (hn : 3 ≤ n) {a b c d kind u w : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hp : patt n a b c d = some (kind, u, w)) :
    Frame n a b c d (wU n kind (gray a) u w) (wU' n kind (gray a) u w) := by
  obtain ⟨hu, hw, s1, s2, s3, ba1, ba2, bd1, bd2, hbc⟩ := patt_some hp
  have hk : kind = 1 ∨ kind = 2 := by rcases hbc with h | h; exacts [Or.inl h.1, Or.inr h.1]
  have huw : u ≠ w := by omega
  have h4 : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  obtain ⟨S, S'⟩ := sop_wU hn (kind := kind) (ga := gray a) hu hw
  have hga := gray_lt ha
  -- the image of the state `t`, read off its bits
  have img : ∀ (t x : ℕ), t < 4 → x < 2 ^ n →
      clear2 (gray a) u w = clear2 (gray x) u w →
      bitOf (gray x) u = bit (if kind = 1 then 0 else 1) t →
      bitOf (gray x) w = bit (if kind = 1 then 1 else 0) t →
      gInv n (fW n kind (gray a) u w t) = x := by
    intro t x ht hx e eu ew
    have : fW n kind (gray a) u w t = gray x := eq_of_bits fun q => by
      rw [bit_fW hn hu hw hk hga ht, bit_of_clear2 huw e eu ew]
    rw [this, gInv_gray hx]
  have g0 : gray 0 = 0 := rfl
  have g1 : gray 1 = 1 := rfl
  have g3 : gray 3 = 2 := rfl
  have g2 : gray 2 = 3 := rfl
  have v0 := sop_val S (j := 0) (by omega)
  have v1 := sop_val S (j := 1) (by omega)
  have v3 := sop_val S (j := 3) (by omega)
  have v2 := sop_val S (j := 2) (by omega)
  rw [g0] at v0; rw [g1] at v1; rw [g3] at v3; rw [g2] at v2
  refine ⟨S.1, S'.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have T := SOp.app0 S S'
    apply SP.ext <;> funext j
    · have e := (T.2 (gray j) (gray_lt j.2)).2.1
      rw [gx_gray] at e
      rw [e, Function.comp_apply, fW_inv, gx_gray]; rfl
    · have e := (T.2 (gray j) (gray_lt j.2)).2.2
      rw [gx_gray] at e
      rw [e]; rfl
  · rw [v0.1]; exact img 0 a (by norm_num) ha rfl (by rw [ba1]; split_ifs <;> rfl)
      (by rw [ba2]; split_ifs <;> rfl)
  · rw [v1.1]
    rcases hbc with ⟨rfl, b1, b2, -, -⟩ | ⟨rfl, b1, b2, -, -⟩
    · exact img 1 b (by norm_num) hb s1 (by rw [b1]; rfl) (by rw [b2]; rfl)
    · exact img 1 b (by norm_num) hb s1 (by rw [b1]; rfl) (by rw [b2]; rfl)
  · rw [v3.1]
    rcases hbc with ⟨rfl, -, -, c1, c2⟩ | ⟨rfl, -, -, c1, c2⟩
    · exact img 2 c (by norm_num) hc s2 (by rw [c1]; rfl) (by rw [c2]; rfl)
    · exact img 2 c (by norm_num) hc s2 (by rw [c1]; rfl) (by rw [c2]; rfl)
  · rw [v2.1]
    rcases hk with rfl | rfl
    · exact img 3 d (by norm_num) hd s3 (by rw [bd1]; rfl) (by rw [bd2]; rfl)
    · exact img 3 d (by norm_num) hd s3 (by rw [bd1]; rfl) (by rw [bd2]; rfl)
  · rw [v0.2, v1.2]
  · rw [v3.2, v2.2]

/-! ## Equation (65) -/

/-- Equation (65) when the Gray codes have the form of (36) or (37). -/
theorem e65_patt (hn : 3 ≤ n) {a b c d kind u w : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (h : Distinct4 a b c d)
    (hp : patt n a b c d = some (kind, u, w)) :
    D8 n [Hh n a b c d] ((sigmaW n a b c d).1 ++ Lam n :: (sigmaW n a b c d).2) := by
  have h8 : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hF := frame_wW hn ha hb hc hd hp
  obtain ⟨-, -, -, -, -, -, -, -, -, hbc⟩ := patt_some hp
  have hax : D8 n [Hh n a b c d] (wW n kind (gray a) u w) := by
    rcases hbc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact DR.ax (Fig8.r36 a b c d u w ha hb hc hd h hp)
    · exact DR.ax (Fig8.r37 a b c d u w ha hb hc hd h hp)
  rw [wW_eq] at hax
  exact hax.trans (frame_eq (by omega) hF (Frame.sigma h8 ha hb hc hd h))

/-- **Equation (65)** at every tuple of distinct indices. -/
theorem e65 (n : ℕ) (hn : 3 ≤ n) : E65 n := by
  intro a b c d ha hb hc hd h
  cases hp : patt n a b c d with
  | none => exact e65_of_35 ha hb hc hd h hp
  | some r =>
    obtain ⟨kind, u, w⟩ := r
    exact e65_patt hn ha hb hc hd h hp

end QCert.RealCliffordCH.Sec8
