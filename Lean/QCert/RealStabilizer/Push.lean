/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits: normalization (Section 5.1)

Lemma 5.4 and Proposition 5.7 of Makary, Ross and Selinger: every circuit
equals a normal form by the typed relations of Appendix B, hence by
R1–R16.  As in `SelingerClifford/Push.lean`, the circuit is put before the
normal form of the identity and its gates, now *dirty*, are moved through
the boxes with the relations (`Tables`), in a fixed order and by structural
recursion instead of the paper's lexicographic termination argument: a
dirty gate is pushed through a `B`-ladder (`pbc`), the `A` box in front of
it (`pushL1`), the `D`-ladder (`pdc`), and what comes out on the top
`n - 1` wires is pushed into the normal form there (`pushN`).  The labels
of Definition 5.3 are the predicates `okB`, `okD`, `okN` of `Dirty`: a gate
a relation leaves behind is allowed where it stands (checked once per row
in `Tables`), so some relation applies to it next.  Inside a `B`-ladder the
type of the current wire (Definition 4.6) is carried along: it decides
which of the boxes `B₁`–`B₈` the ladder has and which gates are allowed,
and every relation keeps the type above the boxes it rewrites, so the rest
of the ladder stays well typed.
-/
import QCert.RealStabilizer.Tables

namespace QCert.RealStabilizer

/-! ### Chaining equations -/

theorem Holds.thru {n : ℕ} {u b b' x c c' y : List Lt} (h1 : Holds n (u ++ b) (b' ++ x))
    (h2 : Holds n (x ++ c) (c' ++ y)) : Holds n (u ++ b ++ c) (b' ++ c' ++ y) := by
  have e1 : Holds n (u ++ b ++ c) (b' ++ x ++ c) := h1.app (Holds.refl n c)
  have e2 : Holds n (b' ++ (x ++ c)) (b' ++ (c' ++ y)) := (Holds.refl n b').app h2
  simp only [List.append_assoc] at e1 e2 ⊢
  exact e1.trans e2

/-- Pushing a word of dirty gates, one gate at a time from the last. -/
theorem push_word {α : Type} {n : ℕ} (S : α → Prop) (W : α → List Lt) (P Q : Dg → Bool)
    (single : ∀ a, S a → ∀ g, P g = true → g.hi ≤ n →
      ∃ a' r', S a' ∧ Holds n (g.word ++ W a) (W a' ++ dw r') ∧ OkL Q n r') :
    ∀ (r : List Dg) (a : α), S a → OkL P n r →
      ∃ a' r', S a' ∧ Holds n (dw r ++ W a) (W a' ++ dw r') ∧ OkL Q n r' := by
  intro r
  induction r using List.reverseRecOn with
  | nil =>
    intro a ha _
    exact ⟨a, [], ha, by simpa using Holds.refl n (W a), OkL.nil Q n⟩
  | append_singleton r g ih =>
    intro a ha hr
    have hg := hr g (by simp)
    obtain ⟨a1, s1, ha1, h1, ok1⟩ := single a ha g hg.1 hg.2
    obtain ⟨a2, s2, ha2, h2, ok2⟩ := ih a1 ha1 (fun x hx => hr x (by simp [hx]))
    refine ⟨a2, s2 ++ s1, ha2, ?_, ok2.append ok1⟩
    have e1 := (Holds.refl n (dw r)).app h1
    have e2 := h2.app (Holds.refl n (dw s1))
    simp only [dw_append, dw_cons, dw_nil, List.append_nil, List.append_assoc] at e1 e2 ⊢
    exact e1.trans e2

/-- A gate below a ladder passes it. -/
theorem pass_below {n c : ℕ} {g : Dg} {v : List Lt} (hb : g.hi ≤ c) (hv : Above c v) :
    Holds n (g.word ++ v) (v ++ dw [g]) := by
  simpa using Holds.pass_up ((below_word g).mono hb) hv

/-- A gate above a box passes it. -/
theorem pass_above {n c : ℕ} {g : Dg} {v : List Lt} (hg : Above c g.word) (hv : Below c v) :
    Holds n (g.word ++ v) (v ++ g.word) :=
  Holds.pass_down hg hv

theorem above_of_lo {g : Dg} {c : ℕ} (hg : g ≠ .neg) (hw : ∀ w, (g = .H w ∨ g = .Z w ∨
    g = .X w ∨ g = .CZ w ∨ g = .CXZ w) → c ≤ w) : Above c g.word := above_word hg hw

theorem okD_of_below {t : Ty} {c n : ℕ} {g : Dg} (hg : okB t c g = true) (hb : g.hi ≤ c)
    (hc : c < n) : okD true (n - 1) g = true := by
  cases g <;> simp [okB, okD, Dg.hi] at hg hb ⊢ <;> omega

theorem tBs_cons (t : Ty) (j : Fin 4) (js : List (Fin 4)) :
    tBs t (j :: js) = tBs (tB t j) js := rfl

/-! ### The `B`-ladder -/

/-- Pushing dirty gates through a `B`-ladder on the wires `c, …, n - 1`
whose current wire has type `t` (labels ②: `okB t c`) to the end of the
Z-circuit (labels ③①: `okD true (n - 1)`). -/
def PBC (n : ℕ) (js : List (Fin 4)) : Prop :=
  ∀ (t : Ty) (c : ℕ) (k : Fin 2) (r : List Dg), c + js.length + 1 = n → tBs t js = false →
    OkL (okB t c) n r →
    ∃ (js' : List (Fin 4)) (k' : Fin 2) (r' : List Dg), js'.length = js.length ∧
      tBs t js' = false ∧ Holds n (dw r ++ BC t c js k) (BC t c js' k' ++ dw r') ∧
      OkL (okD true (n - 1)) n r'

/-- One dirty gate through a `B`-ladder, given the shorter ladders. -/
theorem pbc1 (n L : ℕ) (ih : ∀ m < L, ∀ js : List (Fin 4), js.length = m → PBC n js)
    (t : Ty) (js : List (Fin 4)) (hjs : js.length = L) (htj : tBs t js = false) (k : Fin 2)
    (c : ℕ) (hc : c + L + 1 = n) (g : Dg) (hg : okB t c g = true) (hgn : g.hi ≤ n) :
    ∃ (p' : List (Fin 4) × Fin 2) (r' : List Dg), (p'.1.length = L ∧ tBs t p'.1 = false) ∧
      Holds n (g.word ++ BC t c js k) (BC t c p'.1 p'.2 ++ dw r') ∧
      OkL (okD true (n - 1)) n r' := by
  -- a gate below the ladder passes it
  by_cases hb : g.hi ≤ c
  · exact ⟨(js, k), [g], ⟨hjs, htj⟩, pass_below hb (within_BC t c js k).1,
      OkL.single (okD_of_below hg hb (by omega)) hgn⟩
  rcases js with _ | ⟨j, js⟩
  · -- the box `C_k` on the wire `c = n - 1`, which is simple
    simp only [List.length_nil] at hjs
    subst hjs
    obtain rfl : t = false := htj
    cases g with
    | neg => simp [Dg.hi] at hb
    | H w => simp [okB, Dg.hi] at hg hgn hb; omega
    | Z w =>
      obtain rfl : w = c := by simp [Dg.hi] at hgn hb; omega
      obtain ⟨k', out, h1, ok1⟩ := tCZ k
      have h2 := h1.at w n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bC, upN_dw, Nat.add_zero] at h2
      refine ⟨([], k'), out.map (Dg.shift w), ⟨rfl, rfl⟩, h2, ?_⟩
      have e : n - 1 = w + 0 := by omega
      rw [e]; exact ok1.shiftD.mono (fun x h _ => h) (by omega)
    | X w =>
      obtain rfl : w = c := by simpa [okB] using hg
      obtain ⟨k', out, h1, ok1⟩ := tCX k
      have h2 := h1.at w n (by omega)
      simp only [upN_append, upN_bX, upN_bC, upN_dw, Nat.add_zero] at h2
      refine ⟨([], k'), out.map (Dg.shift w), ⟨rfl, rfl⟩, h2, ?_⟩
      have e : n - 1 = w + 0 := by omega
      rw [e]; exact ok1.shiftD.mono (fun x h _ => h) (by omega)
    | CZ w =>
      obtain rfl : c = w + 1 := by simp [okB, Dg.hi] at hg hgn hb; omega
      obtain ⟨k', out, h1, ok1⟩ := tCCZ k
      have h2 := h1.at w n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bC, upN_dw, Nat.add_zero] at h2
      refine ⟨([], k'), out.map (Dg.shift w), ⟨rfl, rfl⟩, h2, ?_⟩
      have e : n - 1 = w + 1 := by omega
      rw [e]; exact ok1.shiftD.mono (fun x h _ => h) (by omega)
    | CXZ w => simp [okB] at hg
  · -- the box `B` on the wires `c, c + 1`
    simp only [List.length_cons] at hjs
    subst hjs
    rw [tBs_cons] at htj
    -- the rest of the ladder, from the wire `c + 1`
    have rest : ∀ (k : Fin 2) (r : List Dg), OkL (okB (tB t j) (c + 1)) n r →
        ∃ (js' : List (Fin 4)) (k' : Fin 2) (r' : List Dg), js'.length = js.length ∧
          tBs (tB t j) js' = false ∧
          Holds n (dw r ++ BC (tB t j) (c + 1) js k) (BC (tB t j) (c + 1) js' k' ++ dw r') ∧
          OkL (okD true (n - 1)) n r' :=
      fun k r hr => ih js.length (by omega) js rfl (tB t j) (c + 1) k r (by omega) htj hr
    -- a table at the box, then the rest of the ladder
    have finish : ∀ (j' : Fin 4) (out : List Dg), tB t j' = tB t j →
        Holds n (g.word ++ bB (bIdx t j) c) (bB (bIdx t j') c ++ dw out) →
        OkL (okB (tB t j) (c + 1)) n out →
        ∃ (p' : List (Fin 4) × Fin 2) (r' : List Dg),
          (p'.1.length = js.length + 1 ∧ tBs t p'.1 = false) ∧
          Holds n (g.word ++ BC t c (j :: js) k) (BC t c p'.1 p'.2 ++ dw r') ∧
          OkL (okD true (n - 1)) n r' := by
      intro j' out hty h1 ok1
      obtain ⟨js', k', r', hl, ht', h2, ok2⟩ := rest k out ok1
      refine ⟨(j' :: js', k'), r', ⟨by simp [hl], by rw [tBs_cons, hty]; exact ht'⟩, ?_, ok2⟩
      have := Holds.thru h1 h2
      simpa [BC, hty] using this
    -- a gate above the box passes it
    have above : Above (c + 2) g.word → okB (tB t j) (c + 1) g = true →
        ∃ (p' : List (Fin 4) × Fin 2) (r' : List Dg),
          (p'.1.length = js.length + 1 ∧ tBs t p'.1 = false) ∧
          Holds n (g.word ++ BC t c (j :: js) k) (BC t c p'.1 p'.2 ++ dw r') ∧
          OkL (okD true (n - 1)) n r' := by
      intro ha hg1
      obtain ⟨js', k', r', hl, ht', h2, ok2⟩ := rest k [g] (OkL.single hg1 hgn)
      refine ⟨(j :: js', k'), r', ⟨by simp [hl], by rw [tBs_cons]; exact ht'⟩, ?_, ok2⟩
      have h1 := pass_above (n := n) ha (within_bB (bIdx t j) c).2
      have := Holds.thru h1 (by simpa using h2)
      simpa [BC] using this
    cases g with
    | neg => simp [Dg.hi] at hb
    | H w =>
      simp [okB, Dg.hi] at hg hgn hb
      by_cases hw : w = c
      · subst hw
        obtain rfl : t = true := by simpa using hg
        obtain ⟨j', out, h1, hty, ok1⟩ := tBH0 j
        have h2 := h1.at w n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bB, upN_dw, Nat.add_zero] at h2
        exact finish j' _ hty h2 (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => h) (by omega))
      by_cases hw' : w = c + 1
      · subst hw'
        obtain ⟨j', out, h1, hty, ok1⟩ := tBH1 t j
        have h2 := h1.at c n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bB, upN_dw, Nat.add_zero] at h2
        exact finish j' _ hty h2 (hty ▸ (ok1.shiftB (s := c)).mono (fun x h _ => h) (by omega))
      · exact above (above_of_lo (by simp) (by simp; omega)) (by simp [okB]; omega)
    | Z w =>
      simp [Dg.hi] at hgn hb
      by_cases hw : w = c
      · subst hw
        obtain ⟨j', out, h1, hty, ok1⟩ := tBZ0 t j
        have h2 := h1.at w n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bB, upN_dw, Nat.add_zero] at h2
        exact finish j' _ hty h2 (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => h) (by omega))
      by_cases hw' : w = c + 1
      · subst hw'
        obtain ⟨j', out, h1, hty, ok1⟩ := tBZ1 t j
        have h2 := h1.at c n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bB, upN_dw, Nat.add_zero] at h2
        exact finish j' _ hty h2 (hty ▸ (ok1.shiftB (s := c)).mono (fun x h _ => h) (by omega))
      · exact above (above_of_lo (by simp) (by simp; omega)) (by simp [okB])
    | X w =>
      obtain rfl : w = c := by simpa [okB] using hg
      obtain ⟨j', out, h1, hty, ok1⟩ := tBX t j
      have h2 := h1.at w n (by omega)
      simp only [upN_append, upN_bX, upN_bB, upN_dw, Nat.add_zero] at h2
      exact finish j' _ hty h2 (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => h) (by omega))
    | CZ w =>
      simp [okB, Dg.hi] at hg hgn hb
      by_cases hw : w + 1 = c
      · -- below the box, on its lower wire, which is simple
        subst hw
        obtain rfl : t = false := by simpa using hg
        obtain ⟨j', out, h1, hty, ok1⟩ := tBCZ j
        have h2 := h1.at w n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bB, upN_dw, Nat.add_zero] at h2
        exact finish j' _ hty h2 (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => h) (by omega))
      by_cases hw' : w = c + 1
      · -- two boxes: `B_j` and the next one
        subst hw'
        rcases js with _ | ⟨j2, js⟩
        · simp at hc; omega
        rw [tBs_cons] at htj
        obtain ⟨a', b', out, h1, hty, ok1⟩ := tBB t j j2
        have h2 := h1.at c n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bB, upN_dw, Nat.add_zero] at h2
        obtain ⟨js', k', r', hl, ht', h3, ok3⟩ := ih js.length (by simp) js rfl
          (tB (tB t j) j2) (c + 2) k (out.map (Dg.shift c)) (by simp at hc; omega) htj
          (hty ▸ (ok1.shiftB (s := c)).mono (fun x h _ => h) (by simp at hc; omega))
        refine ⟨(a' :: b' :: js', k'), r', ⟨by simp [hl],
          by rw [tBs_cons, tBs_cons, hty]; exact ht'⟩, ?_, ok3⟩
        have := Holds.thru h2 h3
        simpa [BC, Nat.add_assoc, hty] using this
      · exact above (above_of_lo (by simp) (by simp; omega)) (by simp [okB]; omega)
    | CXZ w =>
      simp [okB] at hg
      obtain ⟨rfl, rfl⟩ := hg
      obtain ⟨j', out, h1, hty, ok1⟩ := tBCXZ j
      have h2 := h1.at w n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bB, upN_dw, Nat.add_zero] at h2
      exact finish j' _ hty h2 (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => h) (by omega))

/-- Dirty gates through every `B`-ladder. -/
theorem pbc (n : ℕ) : ∀ L, ∀ js : List (Fin 4), js.length = L → PBC n js := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro js hjs t c k r hc htj hr
    obtain ⟨⟨js', k'⟩, r', ⟨hl, ht'⟩, h, ok⟩ :=
      push_word (n := n) (fun p : List (Fin 4) × Fin 2 => p.1.length = L ∧ tBs t p.1 = false)
        (fun p => BC t c p.1 p.2) (okB t c) (okD true (n - 1))
        (fun p hp g hg hgn => pbc1 n L ih t p.1 hp.1 hp.2 p.2 c (by omega) g hg hgn) r (js, k)
        ⟨hjs, htj⟩ hr
    exact ⟨js', k', r', by simp_all, ht', h, ok⟩

/-! ### The `D`-ladder -/

/-- Pushing dirty gates through a `D`-ladder whose current wire is `L`
(label ④, or ③ when `top`) to the wires above the bottom one (`okN`). -/
def PDC (n : ℕ) (top : Bool) (L : ℕ) : Prop :=
  ∀ (ls : List (Fin 4)) (h : Fin 2) (r : List Dg), ls.length = L → L + 1 ≤ n →
    OkL (okD top L) n r →
    ∃ (ls' : List (Fin 4)) (h' : Fin 2) (r' : List Dg), ls'.length = L ∧
      Holds n (dw r ++ DC ls h) (DC ls' h' ++ dw r') ∧ OkL okN n r'

/-- One dirty gate through a `D`-ladder, given the shorter ladders. -/
theorem pdc1 (n L : ℕ) (ih : ∀ m < L, ∀ top, PDC n top m) (top : Bool)
    (ls : List (Fin 4)) (hls : ls.length = L) (h : Fin 2) (hL : L + 1 ≤ n)
    (g : Dg) (hg : okD top L g = true) (hgn : g.hi ≤ n) :
    ∃ (p' : List (Fin 4) × Fin 2) (r' : List Dg), p'.1.length = L ∧
      Holds n (g.word ++ DC ls h) (DC p'.1 p'.2 ++ dw r') ∧ OkL okN n r' := by
  -- a gate above the ladder passes it
  have above : Above (L + 1) g.word → okN g = true →
      ∃ (p' : List (Fin 4) × Fin 2) (r' : List Dg), p'.1.length = L ∧
        Holds n (g.word ++ DC ls h) (DC p'.1 p'.2 ++ dw r') ∧ OkL okN n r' := by
    intro ha hN
    refine ⟨(ls, h), [g], hls, ?_, OkL.single hN hgn⟩
    have := pass_above (n := n) ha (by simpa [hls] using (within_DC ls h).2)
    simpa using this
  -- a gate below the first box passes it
  have below : ∀ (l : Fin 4) (ls0 : List (Fin 4)), ls = l :: ls0 → g.hi ≤ ls0.length →
      okD false ls0.length g = true →
      ∃ (p' : List (Fin 4) × Fin 2) (r' : List Dg), p'.1.length = L ∧
        Holds n (g.word ++ DC ls h) (DC p'.1 p'.2 ++ dw r') ∧ OkL okN n r' := by
    intro l ls0 e hb hg0
    subst e
    simp only [List.length_cons] at hls
    obtain ⟨ls', h', r', hl, h3, ok3⟩ := ih ls0.length (by omega) false ls0 h [g] rfl
      (by omega) (OkL.single hg0 hgn)
    refine ⟨(l :: ls', h'), r', by simp [hl, ← hls], ?_, ok3⟩
    have h1 := pass_below (n := n) hb (within_bD (l.val + 1) ls0.length).1
    have := Holds.thru h1 h3
    simpa [DC, hl] using this
  -- a table at the first box, then the rest of the ladder
  have table : ∀ (l : Fin 4) (ls0 : List (Fin 4)), ls = l :: ls0 → ∀ (l' : Fin 4) (out : List Dg),
      Holds n (g.word ++ bD (l.val + 1) ls0.length) (bD (l'.val + 1) ls0.length ++ dw out) →
      OkL (okD false ls0.length) n out →
      ∃ (p' : List (Fin 4) × Fin 2) (r' : List Dg), p'.1.length = L ∧
        Holds n (g.word ++ DC ls h) (DC p'.1 p'.2 ++ dw r') ∧ OkL okN n r' := by
    intro l ls0 e l' out h2 ok2
    subst e
    simp only [List.length_cons] at hls
    obtain ⟨ls', h', r', hl, h3, ok3⟩ := ih ls0.length (by omega) false ls0 h out rfl (by omega) ok2
    refine ⟨(l' :: ls', h'), r', by simp [hl, ← hls], ?_, ok3⟩
    have := Holds.thru h2 h3
    simpa [DC, hl] using this
  cases g with
  | neg =>
    refine ⟨(ls, h), [.neg], hls, ?_, OkL.single rfl (Nat.zero_le _)⟩
    simpa [Dg.word] using Holds.neg_pass (k := n) (DC ls h)
  | X w => simp [okD] at hg
  | CXZ w => simp [okD] at hg
  | H w =>
    simp [okD, Dg.hi] at hg hgn
    by_cases hw : L < w
    · exact above (above_of_lo (by simp) (by simp; omega)) (by simp [okN]; omega)
    rcases ls with _ | ⟨l, ls⟩
    · simp at hls; omega
    simp only [List.length_cons] at hls
    by_cases hw' : w = ls.length
    · subst hw'
      obtain ⟨l', out, h1, ok1⟩ := tDH l
      have h2 := h1.at ls.length n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bD, upN_dw, Nat.add_zero] at h2
      exact table l ls rfl l' _ h2
        ((ok1.shiftD (s := ls.length)).mono (fun x h _ => by simpa using h) (by omega))
    · exact below l ls rfl (by simp [Dg.hi]; omega) (by simp [okD]; omega)
  | Z w =>
    simp [Dg.hi] at hgn
    by_cases hw : L < w
    · exact above (above_of_lo (by simp) (by simp; omega)) (by simp [okN]; omega)
    rcases ls with _ | ⟨l, ls⟩
    · simp at hls
      obtain rfl : w = 0 := by omega
      obtain ⟨h', h1⟩ := tEZ h
      refine ⟨([], h'), [], by simpa using hls, ?_, OkL.nil _ _⟩
      simpa [DC] using h1.mono (by omega)
    simp only [List.length_cons] at hls
    by_cases hw1 : w = ls.length + 1
    · subst hw1
      obtain ⟨l', out, h1, ok1⟩ := tDZ1 l
      have h2 := h1.at ls.length n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bD, upN_dw, Nat.add_zero] at h2
      exact table l ls rfl l' _ h2
        ((ok1.shiftD (s := ls.length)).mono (fun x h _ => by simpa using h) (by omega))
    by_cases hw0 : w = ls.length
    · subst hw0
      obtain ⟨l', out, h1, ok1⟩ := tDZ0 l
      have h2 := h1.at ls.length n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bD, upN_dw, Nat.add_zero] at h2
      exact table l ls rfl l' _ h2
        ((ok1.shiftD (s := ls.length)).mono (fun x h _ => by simpa using h) (by omega))
    · exact below l ls rfl (by simp [Dg.hi]; omega) (by simp [okD])
  | CZ w =>
    simp [okD, Dg.hi] at hg hgn
    by_cases hw : L < w
    · exact above (above_of_lo (by simp) (by simp; omega)) (by simp [okN]; omega)
    rcases ls with _ | ⟨l, ls⟩
    · simp at hls; omega
    simp only [List.length_cons] at hls
    by_cases hw0 : w = ls.length
    · -- on the wires of the box, below the first `D` only
      subst hw0
      obtain ⟨l', out, h1, ok1⟩ := tDCZ l
      have h2 := h1.at ls.length n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bD, upN_dw, Nat.add_zero] at h2
      exact table l ls rfl l' _ h2
        ((ok1.shiftD (s := ls.length)).mono (fun x h _ => by simpa using h) (by omega))
    by_cases hw1 : w + 1 = ls.length
    · -- two boxes: the `D` and the next one
      rcases ls with _ | ⟨l2, ls⟩
      · simp at hw1
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hw1 hls
      subst hw1
      obtain ⟨l', l2', out, h1, ok1⟩ := tDD l l2
      have h2 := h1.at ls.length n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bD, upN_dw, Nat.add_zero] at h2
      obtain ⟨ls', h', r', hl, h3, ok3⟩ := ih ls.length (by omega) false ls h
        (out.map (Dg.shift ls.length)) rfl (by omega)
        ((ok1.shiftD (s := ls.length)).mono (fun x h _ => by simpa using h) (by omega))
      refine ⟨(l' :: l2' :: ls', h'), r', by simp [hl, ← hls], ?_, ok3⟩
      have := Holds.thru h2 h3
      simpa [DC, hl, Nat.add_comm 1] using this
    · exact below l ls rfl (by simp [Dg.hi]; omega) (by simp [okD]; omega)

/-- Dirty gates through every `D`-ladder. -/
theorem pdc (n : ℕ) : ∀ L top, PDC n top L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro top ls h r hls hL hr
    obtain ⟨⟨ls', h'⟩, r', hl, hh, ok⟩ :=
      push_word (n := n) (fun p : List (Fin 4) × Fin 2 => p.1.length = L)
        (fun p => DC p.1 p.2) (okD top L) okN
        (fun p hp g hg hgn => pdc1 n L ih top p.1 hp p.2 hL g hg hgn) r (ls, h) hls hr
    exact ⟨ls', h', r', hl, hh, ok⟩

/-! ### The Z-circuit -/

theorem okD_of_belowA {a n : ℕ} {g : Dg} (hg : okA g = true) (hb : g.hi ≤ a) (ha : a < n) :
    okD true (n - 1) g = true := by
  cases g <;> simp [okA, okD, Dg.hi] at hg hb ⊢ <;> omega

/-- One dirty gate through a Z-circuit. -/
theorem pushL1 {n : ℕ} (Z : ZNormal n) (g : Dg) (hg : okA g = true) (hgn : g.hi ≤ n) :
    ∃ (Z' : ZNormal n) (r' : List Dg), Holds n (g.word ++ Z.word) (Z'.word ++ dw r') ∧
      OkL (okD true (n - 1)) n r' := by
  obtain ⟨a, i, js, k, ha, hti⟩ := Z
  simp only [ZNormal.word]
  -- a gate below the circuit passes it
  by_cases hb : g.hi ≤ a
  · exact ⟨⟨a, i, js, k, ha, hti⟩, [g], pass_below hb ((within_bA _ a).1.append
      (within_BC _ a js k).1), OkL.single (okD_of_belowA hg hb (by omega)) hgn⟩
  -- the `B`-ladder from the wire `c`, of type `t`, after a table at the `A` box
  have ladder : ∀ (c : ℕ) (t : Ty) (pre : List Lt) (js0 : List (Fin 4)) (out : List Dg),
      c + js0.length + 1 = n → tBs t js0 = false → OkL (okB t c) n out →
      Holds n (g.word ++ (bA (i.val + 1) a ++ BC (tA i) a js k)) (pre ++ dw out ++ BC t c js0 k) →
      (∀ (js' : List (Fin 4)) (k' : Fin 2), js'.length = js0.length → tBs t js' = false →
        ∃ Z' : ZNormal n, Z'.word = pre ++ BC t c js' k') →
      ∃ (Z' : ZNormal n) (r' : List Dg), Holds n (g.word ++ (bA (i.val + 1) a ++ BC (tA i) a js k))
        (Z'.word ++ dw r') ∧ OkL (okD true (n - 1)) n r' := by
    intro c t pre js0 out hc ht0 ok1 h1 mk
    obtain ⟨js', k', r', hl, ht', h2, ok2⟩ := pbc n _ js0 rfl t c k out hc ht0 ok1
    obtain ⟨Z', hZ⟩ := mk js' k' hl ht'
    refine ⟨Z', r', ?_, ok2⟩
    have e : Holds n (pre ++ dw out ++ BC t c js0 k) (pre ++ (BC t c js' k' ++ dw r')) := by
      simpa only [List.append_assoc] using (Holds.refl n pre).app h2
    rw [hZ]
    simpa only [List.append_assoc] using h1.trans e
  -- a gate above the `A` box passes it
  have above : Above (a + 1) g.word → okB (tA i) a g = true →
      ∃ (Z' : ZNormal n) (r' : List Dg), Holds n (g.word ++ (bA (i.val + 1) a ++ BC (tA i) a js k))
        (Z'.word ++ dw r') ∧ OkL (okD true (n - 1)) n r' := by
    intro hab hga
    refine ladder a (tA i) (bA (i.val + 1) a) js [g] ha hti (OkL.single hga hgn) ?_
      (fun js' k' hl ht => ⟨⟨a, i, js', k', by omega, ht⟩, rfl⟩)
    have := (pass_above (n := n) hab (within_bA (i.val + 1) a).2).app
      (Holds.refl n (BC (tA i) a js k))
    simpa using this
  -- a table at the `A` box that keeps it on the wire `a`
  have stay : ∀ (i' : Fin 3) (out : List Dg), tA i' = tA i →
      Holds n (g.word ++ bA (i.val + 1) a) (bA (i'.val + 1) a ++ dw out) →
      OkL (okB (tA i) a) n out →
      ∃ (Z' : ZNormal n) (r' : List Dg), Holds n (g.word ++ (bA (i.val + 1) a ++ BC (tA i) a js k))
        (Z'.word ++ dw r') ∧ OkL (okD true (n - 1)) n r' := by
    intro i' out hty h2 ok1
    refine ladder a (tA i) (bA (i'.val + 1) a) js out ha hti ok1 ?_
      (fun js' k' hl ht => ⟨⟨a, i', js', k', by omega, by rw [hty]; exact ht⟩,
        by simp [ZNormal.word, hty]⟩)
    simpa using h2.app (Holds.refl n (BC (tA i) a js k))
  cases g with
  | neg => simp [Dg.hi] at hb
  | X w => simp [okA] at hg
  | CXZ w => simp [okA] at hg
  | H w =>
    simp [Dg.hi] at hgn hb
    by_cases hw : w = a
    · subst hw
      obtain ⟨i', out, h1, hty, ok1⟩ := tAH i
      have h2 := h1.at w n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bA, upN_dw, Nat.add_zero] at h2
      exact stay i' _ hty h2 (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => by simpa using h)
        (by omega))
    · exact above (above_of_lo (by simp) (by simp; omega)) (by simp [okB]; omega)
  | Z w =>
    simp [Dg.hi] at hgn hb
    by_cases hw : w = a
    · subst hw
      obtain ⟨i', out, h1, hty, ok1⟩ := tAZ i
      have h2 := h1.at w n (by omega)
      simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bA, upN_dw, Nat.add_zero] at h2
      exact stay i' _ hty h2 (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => by simpa using h)
        (by omega))
    · exact above (above_of_lo (by simp) (by simp; omega)) (by simp [okB])
  | CZ w =>
    simp [Dg.hi] at hgn hb
    by_cases hw1 : w + 1 = a
    · -- `A_i` on the upper wire of the CZ
      subst hw1
      rcases tACZ i with ⟨i', out, h1, hty, ok1⟩ | ⟨i', j, out, h1, hty, ok1⟩
      · have h2 := h1.at w n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bA, upN_dw, Nat.add_zero] at h2
        exact stay i' _ hty h2 (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => h) (by omega))
      · -- the ladder grows down by one wire
        have h2 := h1.at w n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bA, upN_bB, upN_dw,
          Nat.add_zero] at h2
        refine ladder (w + 1) (tA i) (bA (i'.val + 1) w ++ bB (bIdx (tA i') j) w) js
          (out.map (Dg.shift w)) ha hti
          (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => h) (by omega)) ?_
          (fun js' k' hl ht => ⟨⟨w, i', j :: js', k', by simp; omega,
            by rw [tBs_cons, hty]; exact ht⟩, by simp [ZNormal.word, BC, hty]⟩)
        simpa [Dg.word] using h2.app (Holds.refl n (BC (tA i) (w + 1) js k))
    by_cases hw0 : w = a
    · -- the CZ on the wires of `A_i B_j`
      subst hw0
      rcases js with _ | ⟨j, js⟩
      · simp at ha; omega
      simp only [List.length_cons] at ha
      rw [tBs_cons] at hti
      rcases tAB i j with ⟨i', j', out, h1, hty, ok1⟩ | ⟨i', out, h1, hty, ok1⟩
      · have h2 := h1.at w n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bA, upN_bB, upN_dw,
          Nat.add_zero] at h2
        refine ladder (w + 1) (tB (tA i) j) (bA (i'.val + 1) w ++ bB (bIdx (tA i') j') w) js
          (out.map (Dg.shift w)) (by omega) hti
          (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => h) (by omega)) ?_
          (fun js' k' hl ht => ⟨⟨w, i', j' :: js', k', by simp; omega,
            by rw [tBs_cons, hty]; exact ht⟩, by simp [ZNormal.word, BC, hty]⟩)
        simpa [Dg.word, BC] using h2.app (Holds.refl n (BC (tB (tA i) j) (w + 1) js k))
      · -- the ladder shrinks by one wire
        have h2 := h1.at w n (by omega)
        simp only [upN_append, upN_cons, upN_nil, Lt.upBy, upN_bA, upN_bB, upN_dw,
          Nat.add_zero] at h2
        refine ladder (w + 1) (tB (tA i) j) (bA (i'.val + 1) (w + 1)) js
          (out.map (Dg.shift w)) (by omega) hti
          (hty ▸ (ok1.shiftB (s := w)).mono (fun x h _ => h) (by omega)) ?_
          (fun js' k' hl ht => ⟨⟨w + 1, i', js', k', by omega, by rw [hty]; exact ht⟩,
            by simp [ZNormal.word, hty]⟩)
        simpa [Dg.word, BC] using h2.app (Holds.refl n (BC (tB (tA i) j) (w + 1) js k))
    · exact above (above_of_lo (by simp) (by simp; omega)) (by simp [okB]; omega)

/-! ### Normal forms -/

/-- A gate one wire down. -/
def Dg.down : Dg → Dg
  | .neg => .neg
  | .H w => .H (w - 1)
  | .Z w => .Z (w - 1)
  | .X w => .X (w - 1)
  | .CZ w => .CZ (w - 1)
  | .CXZ w => .CXZ (w - 1)

theorem shift_down {g : Dg} (h : okN g = true) : g.down.shift 1 = g := by
  cases g <;> simp [okN, Dg.down, Dg.shift] at h ⊢ <;> omega

theorem okA_down {g : Dg} (h : okN g = true) : okA g.down = true := by
  cases g <;> simp [okN, okA, Dg.down] at h ⊢

theorem hi_down {g : Dg} {n : ℕ} (h : okN g = true) (hn : g.hi ≤ n + 1) : g.down.hi ≤ n := by
  cases g <;> simp [okN, Dg.down, Dg.hi] at h hn ⊢ <;> omega

/-- `(-1)² = 1` (R1). -/
theorem neg_reduce (q : ℕ) : Holds 0 (List.replicate q .neg) (List.replicate (q % 2) .neg) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    by_cases hq : q < 2
    · rw [Nat.mod_eq_of_lt hq]; exact Holds.refl 0 _
    obtain ⟨q', rfl⟩ : ∃ q', q = 2 + q' := ⟨q - 2, by omega⟩
    have h1 : Holds 0 (List.replicate (2 + q') .neg) (List.replicate q' .neg) := by
      rw [List.replicate_add]
      simpa using (Holds.sq .neg (le_refl 0)).app (Holds.refl 0 (List.replicate q' .neg))
    have h2 := ih q' (by omega)
    rw [show (2 + q') % 2 = q' % 2 by omega]
    exact h1.trans h2

/-- Dirty gates through a normal form. -/
theorem pushN : ∀ (n : ℕ) (N : NF n) (r : List Dg), OkL okA n r →
    ∃ N' : NF n, Holds n (dw r ++ N.word) N'.word
  | 0, .scalar p, r, hr => by
    -- on no wires every gate is a scalar
    have e : dw r = List.replicate r.length .neg := by
      induction r with
      | nil => rfl
      | cons x r ih =>
        have hx := (hr x (by simp)).2
        cases x <;> simp [Dg.hi] at hx
        simp [Dg.word, ih (fun y hy => hr y (by simp [hy])), List.replicate_succ]
    refine ⟨.scalar ⟨(r.length + p.val) % 2, Nat.mod_lt _ (by omega)⟩, ?_⟩
    simp only [NF.word, e, ← List.replicate_add]
    exact neg_reduce _
  | n + 1, .cons Z M N, r, hr => by
    have single : ∀ a : NF (n + 1), True → ∀ g, okA g = true → g.hi ≤ n + 1 →
        ∃ (a' : NF (n + 1)) (r' : List Dg), True ∧ Holds (n + 1) (g.word ++ a.word)
          (a'.word ++ dw r') ∧ OkL (fun _ => false) (n + 1) r' := by
      intro a _ g hg hgn
      cases a with
      | cons Z M N =>
        obtain ⟨Z', r1, h1, ok1⟩ := pushL1 Z g hg hgn
        obtain ⟨ls', h', r2, hl, h2, ok2⟩ := pdc (n + 1) n true M.ls M.h r1
          (by have := M.hl; omega) le_rfl (by simpa using ok1)
        have hr2 : r2 = (r2.map Dg.down).map (Dg.shift 1) := by
          rw [List.map_map]
          conv_lhs => rw [← List.map_id r2]
          exact List.map_congr_left (fun x hx => (shift_down (ok2 x hx).1).symm)
        obtain ⟨N', h3⟩ := pushN n N (r2.map Dg.down)
          (fun x hx => by
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
            exact ⟨okA_down (ok2 y hy).1, hi_down (ok2 y hy).1 (ok2 y hy).2⟩)
        refine ⟨.cons Z' ⟨ls', h', by omega⟩ N', [], trivial, ?_, OkL.nil _ _⟩
        have h3' : Holds (n + 1) (dw r2 ++ N.word.map Lt.up) (N'.word.map Lt.up ++ dw []) := by
          have := h3.up
          rw [List.map_append] at this
          rw [hr2, ← upN_dw]
          simpa [upN] using this
        have := Holds.thru (Holds.thru h1 h2) h3'
        simpa [NF.word, XNormal.word, List.append_assoc] using this
    obtain ⟨N', r', -, h, ok⟩ := push_word (n := n + 1) (fun _ : NF (n + 1) => True) NF.word
      okA (fun _ => false) single r (.cons Z M N) trivial hr
    obtain rfl : r' = [] := by
      rcases r' with _ | ⟨x, r'⟩
      · rfl
      · exact absurd (ok x (by simp)).1 (by simp)
    exact ⟨N', by simpa using h⟩

/-! ### The normal form of the identity -/

theorem tBs_rep : ∀ n : ℕ, tBs false (List.replicate n 0) = false
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, tBs_cons]; exact tBs_rep n

/-- The normal form of the identity: `A₁ B₁ ⋯ B₁ C₁`, `D₁ ⋯ D₁ E₁` on every
number of wires (the proof of Proposition 5.7). -/
def Nid : (n : ℕ) → NF n
  | 0 => .scalar 0
  | n + 1 => .cons ⟨0, 0, List.replicate n 0, 0, by simp, tBs_rep n⟩
      ⟨List.replicate n 0, 0, by simp⟩ (Nid n)

theorem BC_rep (n : ℕ) :
    BC false 0 (List.replicate (n + 1) 0) 0 =
      bB (bIdx false 0) 0 ++ upN 1 (BC false 0 (List.replicate n 0) 0) := by
  rw [upN_BC]; rfl

theorem DC_rep : ∀ n : ℕ,
    DC (List.replicate (n + 1) 0) 0 = upN 1 (DC (List.replicate n 0) 0) ++ bD 1 0
  | 0 => by simp [DC, bE, upN_nil]
  | n + 1 => by
    conv_lhs => rw [List.replicate_succ, DC, DC_rep n]
    conv_rhs => rw [List.replicate_succ, DC]
    simp [upN_bD, Nat.add_comm 1 n]

theorem ladders_id : ∀ n : ℕ,
    Holds (n + 1) (BC false 0 (List.replicate n 0) 0 ++ DC (List.replicate n 0) 0) []
  | 0 => by simpa [BC, DC, bC, bE] using Holds.refl 1 []
  | n + 1 => by
    rw [BC_rep, DC_rep]
    have h1 := (ladders_id n).at 1 (n + 2) (by omega)
    simp only [upN_append, upN_nil] at h1
    have h2 : Holds (n + 2) (bB (bIdx false 0) 0 ++ bD 1 0) [] := by
      have := (rel139.symm).mono (show 2 ≤ n + 2 by omega)
      simpa [bC] using this
    have h3 := ((Holds.refl (n + 2) (bB (bIdx false 0) 0)).app h1).app
      (Holds.refl (n + 2) (bD 1 0))
    simp only [List.append_nil] at h3
    simpa only [List.append_assoc] using h3.trans h2

theorem nid_word : ∀ n : ℕ, Holds n [] (Nid n).word
  | 0 => Holds.refl 0 []
  | n + 1 => by
    have h1 := (ladders_id n).symm
    have h2 := (nid_word n).up
    have := h1.app h2
    simpa [Nid, NF.word, ZNormal.word, XNormal.word, bA, tA] using this

/-! ### Proposition 5.7 -/

open Circuit

/-- The gates of a generator, as dirty gates. -/
def gdg : {n : ℕ} → Gen Gate n → List Dg
  | _, .gate0 .neg => [.neg]
  | _, .gate1 .H => [.H 0]
  | _, .gate1 .Z => [.Z 0]
  | _, .gate2 .CZ => [.CZ 0]
  | _, .up g => (gdg g).map (Dg.shift 1)

theorem gdg_ok : ∀ {n : ℕ} (x : Gen Gate n), Eqv n (FreeMonoid.of x) (wc n (dw (gdg x))) ∧
    OkL okA n (gdg x)
  | _, .gate0 .neg => ⟨by simpa [gdg, wc, Dg.word, Lt.circ] using Eqv.refl _,
      by simp [OkL, gdg, okA, Dg.hi]⟩
  | _, .gate1 .H => ⟨by simpa [gdg, wc, Dg.word, Lt.circ, onW1] using Eqv.refl _,
      by simp [OkL, gdg, okA, Dg.hi]⟩
  | _, .gate1 .Z => ⟨by simpa [gdg, wc, Dg.word, Lt.circ, onW1] using Eqv.refl _,
      by simp [OkL, gdg, okA, Dg.hi]⟩
  | _, .gate2 .CZ => ⟨by simpa [gdg, wc, Dg.word, Lt.circ, onW2] using Eqv.refl _,
      by simp [OkL, gdg, okA, Dg.hi]⟩
  | _, .gate3 g => nomatch g
  | n + 1, .up g => by
    obtain ⟨h1, h2⟩ := gdg_ok g
    refine ⟨?_, ?_⟩
    · have e : dw ((gdg g).map (Dg.shift 1)) = (dw (gdg g)).map Lt.up := by
        rw [← upN_dw]; rfl
      simp only [gdg, e]
      exact (Eqv.shift h1).trans (wc_up n _).symm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (by simpa [gdg] using hx)
      refine ⟨?_, (hi_shift 1 y).trans (by have := (h2 y hy).2; omega)⟩
      have := (h2 y hy).1
      cases y <;> simp_all [okA, Dg.shift]

/-- Every circuit after a normal form is a normal form. -/
theorem normalize {n : ℕ} (w : Circ n) : ∀ N₀ : NF n, ∃ N : NF n, Eqv n (N₀.circ * w) N.circ := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact fun N₀ => ⟨N₀, by simpa using Eqv.refl _⟩
  | mul_of x w ih =>
    intro N₀
    obtain ⟨h1, h2⟩ := gdg_ok x
    obtain ⟨N₁, h3⟩ := pushN n N₀ (gdg x) h2
    obtain ⟨N, h4⟩ := ih N₁
    refine ⟨N, ?_⟩
    have e : Eqv n (N₀.circ * FreeMonoid.of x) N₁.circ := by
      have := h3 n le_rfl
      rw [wc_append] at this
      exact (Eqv.mul_left _ h1).trans this
    rw [← mul_assoc]
    exact (Eqv.mul_right w e).trans h4

/-- **Proposition 5.7**: every circuit equals a normal form, by the typed
relations of Appendix B and hence by R1–R16. -/
theorem exists_normal' {n : ℕ} (w : Circ n) : ∃ N : NF n, Eqv n w N.circ := by
  obtain ⟨N, h⟩ := normalize w (Nid n)
  refine ⟨N, ?_⟩
  have e : Eqv n 1 (Nid n).circ := by
    simpa [NF.circ, wc] using nid_word n n le_rfl
  have := (Eqv.mul_right w e).trans h
  simpa using this

end QCert.RealStabilizer
