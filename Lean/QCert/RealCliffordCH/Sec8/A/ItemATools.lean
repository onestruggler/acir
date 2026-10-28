/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Tools for hypothesis (a): moving a letter of `𝒫_N` past `H_[a,b]H_[c,d]`

All from Equation (65) (`E65`, proved in `Sec8/A/E65.lean`):

* `cjA`: a Hadamard-free letter `u` with an inverse moves past `H_[a,b]H_[c,d]`,
  renaming its indices, when its signs agree on `a, b` and on `c, d`
  (`hh_conj`); `cjT`: when they disagree on `a, b`, at the cost of a mixed
  letter (`push_twist`, through Equation (66));
* `flip2`, `flip1`: reversing a pair of a letter, `H_[a,b]H_[d,c] ≈
  H_[a,b]H_[c,d] · (-1)_[d]X_[c,d]` (the twist of Equation (40), then
  `push_twist` with the exchange of `c, d`): the paper's Equation (67).
-/
import QCert.RealCliffordCH.Sec8.A.E65

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- Replacing a segment of a word. -/
theorem D8.seg {L M l l' : List (PG (2 ^ n))} (pre suf : List (PG (2 ^ n))) (h : D8 n l l')
    (h1 : L = pre ++ l ++ suf) (h2 : M = pre ++ l' ++ suf) : D8 n L M := by
  subst h1 h2; exact DR.ctx pre suf h

/-- Corollary A.5 on letters with natural-number indices. -/
theorem a5NL (hN : 4 ≤ 2 ^ n) {L L' : List NL} (hb : ∀ x ∈ L, x.Bd n) (hb' : ∀ x ∈ L', x.Bd n)
    (hp : ∀ x ∈ L, x.Pr) (hp' : ∀ x ∈ L', x.Pr)
    (h : ∀ j < 2 ^ n, permL L j = permL L' j ∧ negL L j = negL L' j) :
    D8 n (L.map (NL.toPG n)) (L'.map (NL.toPG n)) :=
  A5s hN (HP_NL hb hp) (HP_NL hb' hp') (spW_eq_of_NL hb hb' h)

/-- Proper letters. -/
macro "pr_tac" : tactic => `(tactic| (simp [NL.Pr] <;> omega))

theorem swN_ne {a b x : ℕ} (ha : x ≠ a) (hb : x ≠ b) : swN a b x = x := by
  unfold swN; rw [if_neg ha, if_neg hb]

theorem swN_left (a b : ℕ) : swN a b a = b := by unfold swN; rw [if_pos rfl]

theorem fresh1 (h8 : 8 ≤ 2 ^ n) (a b c d : ℕ) :
    ∃ x, x < 2 ^ n ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  obtain ⟨r, -, hr, -, -, hr', -⟩ := exists_fresh_pair ({a, b, c, d} : Finset ℕ)
    ((Finset.card_le_four).trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr'
  exact ⟨r, by omega, hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2⟩

theorem Distinct4.img {a b c d : ℕ} (h : Distinct4 a b c d) {f : ℕ → ℕ} (hf : Function.Injective f) :
    Distinct4 (f a) (f b) (f c) (f d) := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h
  exact ⟨fun e => d1 (hf e), fun e => d2 (hf e), fun e => d3 (hf e), fun e => d4 (hf e),
    fun e => d5 (hf e), fun e => d6 (hf e)⟩

section Conj

variable (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {u u' : NL} (hu : u.Bd n) (hu' : u'.Bd n) (pu : u.Pr)
  (pu' : u'.Pr) (hi : ∀ v < 2 ^ n, permL [u, u'] v = v ∧ negL [u, u'] v = false)
  (hi' : ∀ v < 2 ^ n, permL [u', u] v = v ∧ negL [u', u] v = false)
include h8 hE hu hu' pu pu' hi hi'

theorem cancel_inv : D8 n [] [u'.toPG n, u.toPG n] :=
  a5NL (L := []) (L' := [u', u]) (by omega) (by simp) (by simp [hu, hu']) (by simp)
    (by simp [pu, pu']) (fun j hj => ⟨(hi' j hj).1.symm, (hi' j hj).2.symm⟩)

/-- A letter whose signs agree on both pairs moves past `H_[a,b]H_[c,d]`. -/
theorem cjA {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
    (h : Distinct4 a b c d) (s1 : negL [u] a = negL [u] b) (s2 : negL [u] c = negL [u] d) :
    D8 n [u.toPG n, Hh n a b c d] [Hh n (u.perm a) (u.perm b) (u.perm c) (u.perm d), u.toPG n] := by
  have k := hh_conj h8 hE (P := [u]) (P' := [u']) (by simpa using hu) (by simpa using hu')
    (by simpa using pu) (by simpa using pu') hi ha hb hc hd h s1 s2
  have c0 := cancel_inv h8 hE hu hu' pu pu' hi hi'
  refine (D8.seg [u.toPG n, Hh n a b c d] [] c0 (by simp) rfl).trans ?_
  exact D8.seg [] [u.toPG n] k (by simp) (by simp [permL])

/-- A letter whose signs disagree on the first pair moves past `H_[a,b]H_[c,d]`, leaving
a mixed letter on the images of that pair. -/
theorem cjT {a b c d x : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
    (hx : x < 2 ^ n) (h : Distinct4 a b c d) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hxd : x ≠ d) (s1 : negL [u] a = !negL [u] b) (s2 : negL [u] c = negL [u] d) :
    D8 n [u.toPG n, Hh n a b c d]
      [Hh n (u.perm a) (u.perm b) (u.perm c) (u.perm d), Zx n (u.perm a) (u.perm b) (u.perm a),
        u.toPG n] := by
  have k := push_twist h8 hE (P := [u]) (P' := [u']) (by simpa using hu) (by simpa using hu')
    (by simpa using pu) (by simpa using pu') hi hc hd ha hb hx h.swap hxc hxd hxa hxb s2 s1
  have c0 := cancel_inv h8 hE hu hu' pu pu' hi hi'
  have e1 := e66 h8 hE ha hb hc hd h
  have inj := NL.perm_inj u
  have hl : ∀ v < 2 ^ n, u.perm v < 2 ^ n := fun v hv => perm_lt hu hv
  have e2 := e66 h8 hE (hl c hc) (hl d hd) (hl a ha) (hl b hb) (h.swap.img inj)
  refine (D8.seg [u.toPG n] [] e1 (by simp) rfl).trans ?_
  refine (D8.seg [u.toPG n, Hh n c d a b] [] c0 (by simp) rfl).trans ?_
  refine (D8.seg [] [u.toPG n] k (by simp) rfl).trans ?_
  exact D8.seg [] [Zx n (u.perm a) (u.perm b) (u.perm a), u.toPG n] e2 (by simp [permL])
    (by simp)

end Conj

/-! ## Reversing a pair (Equation (67)) -/

section FlipFacts

variable {c d x : ℕ} (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hx : x < 2 ^ n) (hxc : x ≠ c)
  (hxd : x ≠ d) (d6 : c ≠ d)
include hc hd hx hxc hxd d6

theorem flip_a1 (hN : 4 ≤ 2 ^ n) : D8 n [Zx n d d c] [Zz n c x, Zz n c x, Zx n d d c] :=
  a5NL (L := [NL.zx d d c]) (L' := [NL.zz c x, NL.zz c x, NL.zx d d c]) hN (by bd_tac)
    (by bd_tac) (by pr_tac) (by pr_tac) (fun j hj => by nl_eval)

theorem flip_a2 (hN : 4 ≤ 2 ^ n) : D8 n [] [Zx n d c d, Zx n c c d] :=
  a5NL (L := []) (L' := [NL.zx d c d, NL.zx c c d]) hN (by bd_tac) (by bd_tac) (by pr_tac)
    (by pr_tac) (fun j hj => by nl_eval)

theorem flip_b1 (hN : 4 ≤ 2 ^ n) : D8 n [Zx n c d c, Zx n c c d] [Zz n c d] :=
  a5NL (L := [NL.zx c d c, NL.zx c c d]) (L' := [NL.zz c d]) hN (by bd_tac) (by bd_tac)
    (by pr_tac) (by pr_tac) (fun j hj => by nl_eval)

theorem flip_b2 (hN : 4 ≤ 2 ^ n) : D8 n [Zz n c x, Zx n d d c, Zz n c x] [Zx n c c d] :=
  a5NL (L := [NL.zz c x, NL.zx d d c, NL.zz c x]) (L' := [NL.zx c c d]) hN (by bd_tac)
    (by bd_tac) (by pr_tac) (by pr_tac) (fun j hj => by nl_eval)

theorem flip_b3 (hN : 4 ≤ 2 ^ n) : D8 n [Zx n c c d, Zz n c d] [Zx n d c d] :=
  a5NL (L := [NL.zx c c d, NL.zz c d]) (L' := [NL.zx d c d]) hN (by bd_tac) (by bd_tac)
    (by pr_tac) (by pr_tac) (fun j hj => by nl_eval)

theorem flip_a3 (hN : 4 ≤ 2 ^ n) :
    D8 n [Zz n c x, Zx n d d c, Zz n c x, Zx n c d c, Zx n c c d] [Zx n d c d] :=
  (D8.seg [Zz n c x, Zx n d d c, Zz n c x] [] (flip_b1 hc hd hx hxc hxd d6 hN) (by simp) rfl).trans
    ((D8.seg [] [Zz n c d] (flip_b2 hc hd hx hxc hxd d6 hN) (by simp) rfl).trans
      (flip_b3 hc hd hx hxc hxd d6 hN))

theorem flip_inv : ∀ v < 2 ^ n, permL ([NL.zx d d c] ++ [NL.zx c d c]) v = v ∧
    negL ([NL.zx d d c] ++ [NL.zx c d c]) v = false := fun v hv => by
  simp only [List.cons_append, List.nil_append]; nl_eval

end FlipFacts

/-- `H_[a,b]H_[d,c] ≈ H_[a,b]H_[c,d] · (-1)_[d]X_[c,d]`. -/
theorem flip2 (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (h : Distinct4 a b c d) :
    D8 n [Hh n a b d c] [Hh n a b c d, Zx n d c d] := by
  have hN : 4 ≤ 2 ^ n := by omega
  obtain ⟨x, hx, hxa, hxb, hxc, hxd⟩ := fresh1 h8 a b c d
  have h' := h
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h'
  have tw := twist h8 hE ha hb hc hd hx h hxa hxb hxc hxd
  have sq := hh_sq h8 hE ha hb hc hd h
  -- `H Zz H ≈ Zz Zx`
  have i1 : D8 n [Hh n a b c d, Zz n c x, Hh n a b c d] [Zz n c x, Zx n d d c] :=
    (D8.seg [Hh n a b c d] [] tw (by simp) rfl).trans
      (D8.seg [] [Zz n c x, Zx n d d c] sq (by simp) (by simp))
  have a1 := flip_a1 hc hd hx hxc hxd d6 hN
  -- `Zx H ≈ H Zz Zx Zz`
  have i2 : D8 n [Zx n d d c, Hh n a b c d]
      [Hh n a b c d, Zz n c x, Zx n d d c, Zz n c x] :=
    (D8.seg [] [Hh n a b c d] a1 (by simp) rfl).trans <|
      (D8.seg [Zz n c x] [Hh n a b c d] i1.symm (by simp) rfl).trans <|
      (D8.seg [Zz n c x, Hh n a b c d, Zz n c x] [] sq (by simp) rfl).trans
      (D8.seg [] [Zz n c x] tw (by simp) (by simp))
  -- the exchange of `c, d`
  have pt := push_twist h8 hE (P := [NL.zx d d c]) (P' := [NL.zx c d c]) (by bd_tac) (by bd_tac)
    (by pr_tac) (by pr_tac) (flip_inv hc hd hx hxc hxd d6) ha hb hc hd hx h
    hxa hxb hxc hxd
    (by simp [negL, permL, NL.neg, NL.perm, swN_ne d3 d2, swN_ne d5 d4, d3, d5])
    (by simp [negL, permL, NL.neg, NL.perm, swN_left, swN_right, d6])
  have ea : permL [NL.zx d d c] a = a := swN_ne d3 d2
  have eb : permL [NL.zx d d c] b = b := swN_ne d5 d4
  have ec : permL [NL.zx d d c] c = d := swN_right d c
  have ed : permL [NL.zx d d c] d = c := swN_left d c
  rw [ea, eb, ec, ed] at pt
  have a2 := flip_a2 hc hd hx hxc hxd d6 hN
  have a3 := flip_a3 hc hd hx hxc hxd d6 hN
  refine (D8.seg [Hh n a b d c] [] a2 (by simp) rfl).trans ?_
  refine (D8.seg [] [Zx n c c d] pt.symm (by simp) rfl).trans ?_
  refine (D8.seg [] [Zx n c d c, Zx n c c d] i2 (by simp [NL.toPG]) rfl).trans ?_
  exact D8.seg [Hh n a b c d] [] a3 (by simp) (by simp)

/-- `H_[b,a]H_[c,d] ≈ H_[a,b]H_[c,d] · (-1)_[b]X_[a,b]`. -/
theorem flip1 (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (h : Distinct4 a b c d) :
    D8 n [Hh n b a c d] [Hh n a b c d, Zx n b a b] := by
  have h' := h
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h'
  have hba : Distinct4 b a c d := ⟨Ne.symm d1, d4, d5, d2, d3, d6⟩
  refine (e66 h8 hE hb ha hc hd hba).trans ?_
  refine (flip2 h8 hE hc hd ha hb h.swap).trans ?_
  exact D8.seg [] [Zx n b a b] (e66 h8 hE hc hd ha hb h.swap) (by simp) (by simp)

end QCert.RealCliffordCH.Sec8
