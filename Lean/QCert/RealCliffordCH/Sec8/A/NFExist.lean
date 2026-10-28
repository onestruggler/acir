/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-free words: existence of the normal form

`NFW b d = SWl b (sidx n) ++ PN d (2ⁿ)`, a sign part and a permutation part.
Every proper Hadamard-free word is derivably equal to such a word
(`nf_exists`): every letter is a product of letters `σ_j`, their inverses
`σ_j³` (Equation (48)) and signs (Equations (25)–(28), (30), (33), (34)),
and the normal form absorbs each of these.
-/
import QCert.RealCliffordCH.Sec8.A.Signs

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- The normal form of a Hadamard-free word. -/
def NFW (n : ℕ) (b : ℕ → Bool) (d : ℕ → ℕ) : List (PG (2 ^ n)) :=
  SWl n b (sidx n) ++ PN n d (2 ^ n)

theorem nf_sg (hN : 4 ≤ 2 ^ n) {b : ℕ → Bool} {d : ℕ → ℕ} (hd : Code d (2 ^ n)) {j : ℕ}
    (hj : j + 1 < 2 ^ n) :
    ∃ b' d', Code d' (2 ^ n) ∧ DH n (NFW n b d ++ [sg n j]) (NFW n b' d') := by
  obtain ⟨ps, d', hps, hd', h⟩ := push_sg hN (2 ^ n) d le_rfl hd j hj
  obtain ⟨b', hb⟩ := absorb_zzs (n := n) b ps hps
  refine ⟨b', d', hd', ?_⟩
  unfold NFW
  exact (DR.rfl' (List.append_assoc _ _ _)).trans ((DR.left (SWl n b (sidx n)) h).trans
    ((DR.rfl' (List.append_assoc _ _ _).symm).trans (DR.right (PN n d' (2 ^ n)) hb)))

theorem nf_zz (hN : 4 ≤ 2 ^ n) {b : ℕ → Bool} {d : ℕ → ℕ} (hd : Code d (2 ^ n)) {c e : ℕ}
    (hc : c < 2 ^ n) (he : e < 2 ^ n) : ∃ b', DH n (NFW n b d ++ [Zz n c e]) (NFW n b' d) := by
  have hz := zz_through hN (js := pidx d (2 ^ n)) (fun j hj => pidx_lt hd j hj) hc he
  obtain ⟨b', hb⟩ := absorb_zz (n := n) b (swL_lt (fun j hj => pidx_lt hd j hj) hc)
    (swL_lt (fun j hj => pidx_lt hd j hj) he)
  refine ⟨b', ?_⟩
  unfold NFW
  exact (DR.rfl' (List.append_assoc _ _ _)).trans ((DR.left (SWl n b (sidx n)) hz).trans
    ((DR.rfl' (List.append_assoc _ _ _).symm).trans (DR.right (PN n d (2 ^ n)) hb)))

/-- Equation (48): `σ_j⁻¹ = σ_j³`. -/
theorem tg_cube {j : ℕ} (hj : j + 1 < 2 ^ n) : DH n [tg n j] [sg n j, sg n j, sg n j] := by
  have hj' : j < 2 ^ n := by omega
  exact (DR.ctx [] [tg n j] (zz_sq hj' hj)).symm.trans <|
    (DR.ctx [] [Zz n j (j + 1), tg n j] (e23 n hj)).trans <|
    (DR.ctx [sg n j, sg n j] [tg n j] (e23 n hj)).trans <|
    DR.ctx [sg n j, sg n j, sg n j] [] (e29 n hj)

/-- The letters the normal form absorbs directly. -/
def Basic (n : ℕ) (x : PG (2 ^ n)) : Prop :=
  (∃ j k, k = j + 1 ∧ k < 2 ^ n ∧ (x = Zx n j j k ∨ x = Zx n k j k)) ∨
    ∃ c e, c < 2 ^ n ∧ e < 2 ^ n ∧ x = Zz n c e

theorem nf_basic (hN : 4 ≤ 2 ^ n) {b : ℕ → Bool} {d : ℕ → ℕ} (hd : Code d (2 ^ n))
    {x : PG (2 ^ n)} (hx : Basic n x) :
    ∃ b' d', Code d' (2 ^ n) ∧ DH n (NFW n b d ++ [x]) (NFW n b' d') := by
  rcases hx with ⟨j, k, rfl, hk, rfl | rfl⟩ | ⟨c, e, hc, he, rfl⟩
  · exact nf_sg hN hd hk
  · obtain ⟨b1, d1, hd1, h1⟩ := nf_sg (b := b) hN hd hk
    obtain ⟨b2, d2, hd2, h2⟩ := nf_sg (b := b1) hN hd1 hk
    obtain ⟨b3, d3, hd3, h3⟩ := nf_sg (b := b2) hN hd2 hk
    refine ⟨b3, d3, hd3, (DR.left (NFW n b d) (tg_cube hk)).trans ?_⟩
    exact (DR.rfl' (by simp)).trans ((DR.right [sg n j, sg n j] h1).trans
      ((DR.rfl' (by simp)).trans ((DR.right [sg n j] h2).trans h3)))
  · obtain ⟨b', hb⟩ := nf_zz (b := b) hN hd hc he
    exact ⟨b', d, hd, hb⟩

/-- A word of basic letters. -/
def Basics (n : ℕ) (w : List (PG (2 ^ n))) : Prop := ∀ x ∈ w, Basic n x

theorem nf_basics (hN : 4 ≤ 2 ^ n) : ∀ (w : List (PG (2 ^ n))), Basics n w →
    ∀ (b : ℕ → Bool) (d : ℕ → ℕ), Code d (2 ^ n) →
      ∃ b' d', Code d' (2 ^ n) ∧ DH n (NFW n b d ++ w) (NFW n b' d')
  | [], _, b, d, hd => ⟨b, d, hd, DR.rfl' (List.append_nil _)⟩
  | x :: w, hw, b, d, hd => by
    obtain ⟨b1, d1, hd1, h1⟩ := nf_basic hN hd (hw x (by simp)) (b := b)
    obtain ⟨b2, d2, hd2, h2⟩ :=
      nf_basics hN w (fun y hy => hw y (List.mem_cons_of_mem _ hy)) b1 d1 hd1
    exact ⟨b2, d2, hd2, (DR.rfl' (by simp)).trans ((DR.right w h1).trans h2)⟩

/-! ## Every Hadamard-free letter is a word of basic letters -/

theorem basics_append {w w' : List (PG (2 ^ n))} (h : Basics n w) (h' : Basics n w') :
    Basics n (w ++ w') := fun x hx => (List.mem_append.1 hx).elim (h x) (h' x)

theorem basics_single {x : PG (2 ^ n)} (h : Basic n x) : Basics n [x] := fun y hy => by
  simp only [List.mem_singleton] at hy; exact hy ▸ h

theorem basic_sg {j k : ℕ} (hk : k = j + 1) (hk' : k < 2 ^ n) : Basic n (Zx n j j k) :=
  Or.inl ⟨j, k, hk, hk', Or.inl rfl⟩

theorem basic_tg {j k : ℕ} (hk : k = j + 1) (hk' : k < 2 ^ n) : Basic n (Zx n k j k) :=
  Or.inl ⟨j, k, hk, hk', Or.inr rfl⟩

/-- `(-1)_[a]X_[a,c]` and `(-1)_[c]X_[a,c]`, `a < c`. -/
theorem dec_AB : ∀ (g a : ℕ), a + 1 + g < 2 ^ n →
    (∃ w, Basics n w ∧ DH n [Zx n a a (a + 1 + g)] w) ∧
      ∃ w, Basics n w ∧ DH n [Zx n (a + 1 + g) a (a + 1 + g)] w
  | 0, a, h => ⟨⟨_, basics_single (basic_sg rfl h), DR.refl _⟩,
    ⟨_, basics_single (basic_tg rfl h), DR.refl _⟩⟩
  | g + 1, a, h => by
    have hb : Basics n [Zx n (a + 1) a (a + 1)] := basics_single (basic_tg rfl (by omega))
    have hb' : Basics n [Zx n a a (a + 1)] := basics_single (basic_sg rfl (by omega))
    by_cases hodd : (a + 1 + (g + 1) - a) % 2 = 1
    · obtain ⟨⟨w1, hw1, h1⟩, ⟨w2, hw2, h2⟩⟩ := dec_AB g (a + 1) (by omega)
      rw [show a + 1 + 1 + g = a + 1 + (g + 1) by omega] at h1 h2
      refine ⟨⟨_, basics_append (basics_append hb hw1) hb', ?_⟩,
        ⟨_, basics_append (basics_append hb hw2) hb', ?_⟩⟩
      · exact (e25 n (by omega) h hodd).trans
          (DR.ctx [Zx n (a + 1) a (a + 1)] [Zx n a a (a + 1)] h1)
      · exact (e26 n (by omega) h hodd).trans
          (DR.ctx [Zx n (a + 1) a (a + 1)] [Zx n a a (a + 1)] h2)
    · obtain ⟨⟨w1, hw1, h1⟩, ⟨w2, hw2, h2⟩⟩ := dec_AB g a (by omega)
      have e1 : a + 1 + (g + 1) - 1 = a + 1 + g := by omega
      have hc : Basics n [Zx n (a + 1 + (g + 1) - 1) (a + 1 + (g + 1) - 1) (a + 1 + (g + 1))] :=
        basics_single (basic_sg (by omega) h)
      have hc' : Basics n [Zx n (a + 1 + (g + 1)) (a + 1 + (g + 1) - 1) (a + 1 + (g + 1))] :=
        basics_single (basic_tg (by omega) h)
      refine ⟨⟨_, basics_append (basics_append hc hw1) hc', ?_⟩,
        ⟨_, basics_append (basics_append hc hw2) hc', ?_⟩⟩
      · refine (e27 n (a := a) (by omega) h (by omega)).trans
          (DR.ctx [Zx n (a + 1 + (g + 1) - 1) (a + 1 + (g + 1) - 1) (a + 1 + (g + 1))]
            [Zx n (a + 1 + (g + 1)) (a + 1 + (g + 1) - 1) (a + 1 + (g + 1))]
            (l := [Zx n a a (a + 1 + (g + 1) - 1)]) (l' := w1) ?_)
        rw [e1]; exact h1
      · refine (e28 n (a := a) (by omega) h (by omega)).trans
          (DR.ctx [Zx n (a + 1 + (g + 1) - 1) (a + 1 + (g + 1) - 1) (a + 1 + (g + 1))]
            [Zx n (a + 1 + (g + 1)) (a + 1 + (g + 1) - 1) (a + 1 + (g + 1))]
            (l := [Zx n (a + 1 + (g + 1) - 1) a (a + 1 + (g + 1) - 1)]) (l' := w2) ?_)
        rw [e1]; exact h2

theorem dec_A {a c : ℕ} (hac : a < c) (hc : c < 2 ^ n) :
    ∃ w, Basics n w ∧ DH n [Zx n a a c] w := by
  have := (dec_AB (n := n) (c - a - 1) a (by omega)).1
  rwa [show a + 1 + (c - a - 1) = c by omega] at this

theorem dec_B {a c : ℕ} (hac : a < c) (hc : c < 2 ^ n) :
    ∃ w, Basics n w ∧ DH n [Zx n c a c] w := by
  have := (dec_AB (n := n) (c - a - 1) a (by omega)).2
  rwa [show a + 1 + (c - a - 1) = c by omega] at this

/-- `(-1)_[c]X_[c,d]` whatever the order of `c, d`. -/
theorem dec_cc {c d : ℕ} (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hcd : c ≠ d) :
    ∃ w, Basics n w ∧ DH n [Zx n c c d] w := by
  rcases Nat.lt_or_gt_of_ne hcd with h | h
  · exact dec_A h hd
  · obtain ⟨w, hw, h'⟩ := dec_B h hc
    exact ⟨w, hw, (e33 n hd hc (Ne.symm hcd)).symm.trans h'⟩

/-- `(-1)_[s]X_[c,d]`, `c ≠ d`. -/
theorem dec_zx {s c d : ℕ} (hs : s < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hcd : c ≠ d) :
    ∃ w, Basics n w ∧ DH n [Zx n s c d] w := by
  by_cases h1 : s = c
  · subst h1; exact dec_cc hs hd hcd
  by_cases h2 : s = d
  · subst h2
    obtain ⟨w, hw, h'⟩ := dec_cc hs hc (Ne.symm hcd)
    exact ⟨w, hw, (e33 n hc hs hcd).trans h'⟩
  obtain ⟨w, hw, h'⟩ := dec_cc hc hd hcd
  exact ⟨[Zz n s c] ++ w, basics_append (basics_single (Or.inr ⟨s, c, hs, hc, rfl⟩)) hw,
    (e30 n hd hc hs hcd h1 h2).trans (DR.left [Zz n s c] h')⟩

theorem ix_eq {a : Fin (2 ^ n)} : ix n a = a := Fin.ext (Nat.mod_eq_of_lt a.2)

/-- Every proper Hadamard-free letter is a word of basic letters. -/
theorem dec_letter {x : PG (2 ^ n)} (hx : x.HF) (hp : x.Proper) :
    ∃ w, Basics n w ∧ DH n [x] w := by
  cases x with
  | zz a c =>
    refine ⟨[.zz a c], basics_single (Or.inr ⟨a, c, a.2, c.2, ?_⟩), DR.refl _⟩
    simp [Zz, ix_eq]
  | zx a c d =>
    have hcd : (c : ℕ) ≠ d := fun h => hp (Fin.ext h)
    obtain ⟨w, hw, h⟩ := dec_zx (n := n) a.2 c.2 d.2 hcd
    exact ⟨w, hw, by simpa [Zx, ix_eq] using h⟩
  | xx a b c d =>
    have hab : (a : ℕ) ≠ b := fun h => hp.1 (Fin.ext h)
    have hcd : (c : ℕ) ≠ d := fun h => hp.2 (Fin.ext h)
    obtain ⟨w1, hw1, h1⟩ := dec_zx (n := n) a.2 a.2 b.2 hab
    obtain ⟨w2, hw2, h2⟩ := dec_zx (n := n) b.2 c.2 d.2 hcd
    refine ⟨w1 ++ w2, basics_append hw1 hw2, ?_⟩
    have := (e34 n a.2 b.2 c.2 d.2 hab hcd).trans (DR.append h1 h2)
    simpa [Xx, ix_eq] using this
  | hh a b c d => exact absurd hx id

/-- Every proper Hadamard-free word is derivably equal to a normal form. -/
theorem nf_exists (hN : 4 ≤ 2 ^ n) : ∀ (l : List (PG (2 ^ n))), (∀ x ∈ l, x.HF ∧ x.Proper) →
    ∀ (b : ℕ → Bool) (d : ℕ → ℕ), Code d (2 ^ n) →
      ∃ b' d', Code d' (2 ^ n) ∧ DH n (NFW n b d ++ l) (NFW n b' d')
  | [], _, b, d, hd => ⟨b, d, hd, DR.rfl' (List.append_nil _)⟩
  | x :: l, hl, b, d, hd => by
    obtain ⟨w, hw, hx⟩ := dec_letter (hl x (by simp)).1 (hl x (by simp)).2
    obtain ⟨b1, d1, hd1, h1⟩ := nf_basics hN w hw b d hd
    obtain ⟨b2, d2, hd2, h2⟩ :=
      nf_exists hN l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) b1 d1 hd1
    refine ⟨b2, d2, hd2, ?_⟩
    exact (DR.rfl' (by simp)).trans ((DR.ctx (NFW n b d) l hx).trans
      ((DR.right l h1).trans h2))

end QCert.RealCliffordCH.Sec8
