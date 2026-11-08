/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Permutations of basis states as words, and the frame lemma

Translation of `Examples/Groups/Symmetric/CoxeterFrames.agda`, with its
foundation, the completeness of the Coxeter presentation of `Sₙ`, proved
here.

A Coxeter word is a word in the adjacent transpositions `(i i+1)` of the
basis states, written by the index `i` of each letter (`CW`).  In a monoid,
elements `τ i` satisfying the Coxeter relations for `i < N` (`CoxRel`) read
such words (`ev`), and:

* two words in `S_{N+1}` with the same permutation have the same value
  (`perm_complete`);
* a word fixing the states below `j` has the value of a word in the `τ i`
  with `i ≥ j` (`stab`), so an element `b` that those `τ i` commute with,
  conjugated by a word, depends only on where the word sends the states
  below `j` (`frame_eq`);
* `frame ts` sends the states `0, 1, …` to the distinct states `ts`
  (`frame_act`).

`Circuits` reads Coxeter words as words over any alphabet whose words `T d`
satisfy the Coxeter relations modulo a theory (`Coxeter`), through the
quotient monoid of the theory.

**Deviation from the Agda.**  The Agda reads Coxeter words as circuits of
its presentation of `Sₙ` (`Examples/Groups/Symmetric`) and gets
`perm-complete` from that presentation's completeness (proved there by a
coset normal form through Reidemeister–Schreier) and `stab` from its
surjectivity.  The Lean library has no presentation of `Sₙ`, so here the
letters are indices and both facts are proved directly by one normal form:
`frame (map π [0, …, N])`, the word `cyc (π 0)` followed, one wire up, by the
normal form of the rest.  Multiplying a normal form on the left by a
generator gives the normal form of the product (`key`), by the order,
braid and far commutation relations; so every word equals the normal form
of its permutation, and a permutation fixing the states below `j` has a
normal form in the letters `i ≥ j`.
-/
import QCert.Presentation
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace QCert.ToffoliHadamardRS.CoxeterFrames

/-! ## Coxeter words and their action on states -/

/-- A Coxeter word: the letter `i` is the transposition of the states
`i, i + 1`. -/
abbrev CW := List ℕ

/-- The transposition of `i` and `i + 1`. -/
def sw (i x : ℕ) : ℕ := if x = i then i + 1 else if x = i + 1 then i else x

/-- The permutation of states of a word (the rightmost letter acts first). -/
def act (w : CW) (x : ℕ) : ℕ := w.foldr sw x

/-- The inverse of a Coxeter word: its letters reversed. -/
def inv (w : CW) : CW := w.reverse

@[simp] theorem act_nil (x : ℕ) : act [] x = x := rfl

@[simp] theorem act_cons (i : ℕ) (w : CW) (x : ℕ) : act (i :: w) x = sw i (act w x) := rfl

theorem act_append (u v : CW) (x : ℕ) : act (u ++ v) x = act u (act v x) := by
  simp [act, List.foldr_append]

theorem sw_sw (i x : ℕ) : sw i (sw i x) = x := by
  unfold sw; split_ifs <;> omega

theorem act_inv (p : CW) (x : ℕ) : act (inv p) (act p x) = x := by
  induction p generalizing x with
  | nil => rfl
  | cons i p ih =>
    rw [inv, List.reverse_cons, act_append, act_cons]
    show act p.reverse (sw i (sw i (act p x))) = x
    rw [sw_sw]; exact ih x

theorem act_inv' (p : CW) (x : ℕ) : act p (act (inv p) x) = x := by
  have := act_inv (inv p) x
  simp only [inv, List.reverse_reverse] at this ⊢; exact this

theorem sw_inj {i x y : ℕ} (h : sw i x = sw i y) : x = y := by
  rw [← sw_sw i x, h, sw_sw]

theorem sw_lt {i x n : ℕ} (hi : i + 1 < n) (hx : x < n) : sw i x < n := by
  unfold sw; split_ifs <;> omega

/-- The letters of a word lie below `N`: a word of `S_{N+1}`. -/
def Valid (N : ℕ) (w : CW) : Prop := ∀ i ∈ w, i < N

theorem act_lt {N : ℕ} {w : CW} (hw : Valid N w) {x : ℕ} (hx : x < N + 1) : act w x < N + 1 := by
  induction w with
  | nil => exact hx
  | cons i w ih =>
    rw [act_cons]
    exact sw_lt (by have := hw i (by simp); omega)
      (ih fun j hj => hw j (List.mem_cons_of_mem _ hj))

theorem act_inj {w : CW} {x y : ℕ} (h : act w x = act w y) : x = y := by
  rw [← act_inv w x, h, act_inv]

theorem valid_inv {N : ℕ} {w : CW} (hw : Valid N w) : Valid N (inv w) := by
  intro i hi; exact hw i (List.mem_reverse.1 hi)

theorem valid_append {N : ℕ} {u v : CW} (hu : Valid N u) (hv : Valid N v) : Valid N (u ++ v) := by
  intro i hi
  rcases List.mem_append.1 hi with h | h
  exacts [hu i h, hv i h]

/-! ## Cycles and frames -/

/-- `cyc t = [t-1, …, 1, 0]` sends `0` to `t` and every other state `x + 1`
to `punchIn t x`. -/
def cyc (t : ℕ) : CW := (List.range t).reverse

theorem cyc_succ (t : ℕ) : cyc (t + 1) = t :: cyc t := by
  simp [cyc, List.range_succ]

theorem mem_cyc {t i : ℕ} (h : i ∈ cyc t) : i < t := by
  simpa [cyc] using h

/-- `punchOut`: the states other than `t`, renumbered. -/
def pout (t y : ℕ) : ℕ := if y < t then y else y - 1

/-- `punchIn`, its inverse. -/
def pin (t y : ℕ) : ℕ := if y < t then y else y + 1

theorem pin_pout {t y : ℕ} (h : y ≠ t) : pin t (pout t y) = y := by
  unfold pin pout; split_ifs <;> omega

theorem pout_inj {t x y : ℕ} (hx : x ≠ t) (hy : y ≠ t) (h : pout t x = pout t y) : x = y := by
  rw [← pin_pout hx, ← pin_pout hy, h]

/-- The frame of a list of states, with fuel. -/
def frameN : ℕ → List ℕ → CW
  | 0, _ => []
  | _, [] => []
  | n + 1, t :: ts => cyc t ++ (frameN n (ts.map (pout t))).map Nat.succ

/-- `frame ts` sends the states `0, 1, …` to the entries of `ts`: it is
`cyc` of the head followed, one wire up, by the frame of the rest punched
out at the head. -/
def frame (ts : List ℕ) : CW := frameN ts.length ts

theorem frame_nil : frame [] = [] := rfl

theorem frame_cons (t : ℕ) (ts : List ℕ) :
    frame (t :: ts) = cyc t ++ (frame (ts.map (pout t))).map Nat.succ := by
  simp [frame, frameN, List.length_map]

theorem act_cyc_zero (t : ℕ) : act (cyc t) 0 = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [cyc_succ, act_cons, ih]; simp [sw]

theorem act_cyc_succ (t y : ℕ) : act (cyc t) (y + 1) = pin t y := by
  induction t with
  | zero => simp [cyc, pin]
  | succ t ih =>
    rw [cyc_succ, act_cons, ih]; unfold sw pin; split_ifs <;> omega

theorem act_map_succ_zero (F : CW) : act (F.map Nat.succ) 0 = 0 := by
  induction F with
  | nil => rfl
  | cons i F ih => simp only [List.map_cons, act_cons, ih]; simp [sw]

theorem act_map_succ_succ (F : CW) (y : ℕ) : act (F.map Nat.succ) (y + 1) = act F y + 1 := by
  induction F with
  | nil => rfl
  | cons i F ih =>
    simp only [List.map_cons, act_cons, ih]; unfold sw; split_ifs <;> omega

theorem nodup_map_pout {t : ℕ} {ts : List ℕ} (h : (t :: ts).Nodup) : (ts.map (pout t)).Nodup := by
  rw [List.nodup_cons] at h
  refine List.Nodup.map_on (fun x hx y hy e => pout_inj ?_ ?_ e) h.2
  · rintro rfl; exact h.1 hx
  · rintro rfl; exact h.1 hy

/-- The frame sends `i` to the `i`-th entry. -/
theorem frame_act : ∀ (ts : List ℕ), ts.Nodup → ∀ (i : ℕ) (hi : i < ts.length),
    act (frame ts) i = ts[i]
  | [], _, i, hi => by simp at hi
  | t :: ts, hd, i, hi => by
    rw [frame_cons, act_append]
    cases i with
    | zero => rw [act_map_succ_zero, act_cyc_zero]; rfl
    | succ i =>
      have hi' : i < (ts.map (pout t)).length := by simp at hi ⊢; omega
      rw [act_map_succ_succ, act_cyc_succ, frame_act _ (nodup_map_pout hd) i hi',
        List.getElem_map]
      simp only [List.getElem_cons_succ]
      apply pin_pout
      intro e
      rw [List.nodup_cons] at hd
      exact hd.1 (e ▸ List.getElem_mem _)
termination_by ts _ _ _ => ts.length

theorem frame_act' (ts : List ℕ) (hd : ts.Nodup) (i x : ℕ) (h : ts[i]? = some x) :
    act (frame ts) i = x := by
  have hi : i < ts.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  rw [frame_act ts hd i hi]
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

/-- The letters of a frame of distinct states below `N + 1` lie below `N`. -/
theorem frame_valid : ∀ (N : ℕ) (ts : List ℕ), ts.Nodup → (∀ t ∈ ts, t < N + 1) →
    Valid N (frame ts)
  | N, [], _, _ => by intro i hi; simp [frame_nil] at hi
  | N, t :: ts, hd, hb => by
    rw [frame_cons]
    intro i hi
    rcases List.mem_append.1 hi with h | h
    · have := mem_cyc h; have := hb t (by simp); omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
      cases N with
      | zero =>
        have ht := hb t (by simp)
        cases ts with
        | nil => simp [frame_nil] at hj
        | cons y ys =>
          have hy := hb y (by simp)
          rw [List.nodup_cons] at hd
          exact absurd (show y = t by omega) (fun e => hd.1 (by simp [e]))
      | succ N =>
        have := frame_valid N (ts.map (pout t)) (nodup_map_pout hd) (by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
          have hzt : z ≠ t := by rintro rfl; rw [List.nodup_cons] at hd; exact hd.1 hz
          have := hb z (by simp [hz]); have := hb t (by simp)
          unfold pout; split_ifs <;> omega) j hj
        omega
termination_by _ ts _ _ => ts.length

theorem frame_range : ∀ m : ℕ, frame (List.range m) = []
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ_eq_map, frame_cons, List.map_map]
    have : (pout 0 ∘ Nat.succ) = id := by funext y; simp [pout]
    rw [this, List.map_id, frame_range m]; rfl

/-! ## Values in a monoid -/

section Monoid

variable {M : Type*} [Monoid M] (τ : ℕ → M)

/-- The value of a Coxeter word. -/
def ev (w : CW) : M := (w.map τ).prod

@[simp] theorem ev_nil : ev τ [] = 1 := rfl

@[simp] theorem ev_cons (i : ℕ) (w : CW) : ev τ (i :: w) = τ i * ev τ w := by simp [ev]

theorem ev_append (u v : CW) : ev τ (u ++ v) = ev τ u * ev τ v := by simp [ev]

theorem ev_map_succ (w : CW) : ev τ (w.map Nat.succ) = ev (fun i => τ (i + 1)) w := by
  simp only [ev, List.map_map]; rfl

/-- The Coxeter relations for `τ i`, `i < N`. -/
structure CoxRel (N : ℕ) : Prop where
  order : ∀ i, i < N → τ i * τ i = 1
  braid : ∀ i, i + 1 < N → τ i * τ (i + 1) * τ i = τ (i + 1) * τ i * τ (i + 1)
  far : ∀ i j, i + 2 ≤ j → j < N → τ i * τ j = τ j * τ i

variable {τ}

theorem CoxRel.shift {N : ℕ} (h : CoxRel τ (N + 1)) : CoxRel (fun i => τ (i + 1)) N where
  order i hi := h.order (i + 1) (by omega)
  braid i hi := h.braid (i + 1) (by omega)
  far i j hij hj := h.far (i + 1) (j + 1) (by omega) (by omega)

theorem CoxRel.mono {N N' : ℕ} (h : CoxRel τ N) (hN : N' ≤ N) : CoxRel τ N' where
  order i hi := h.order i (by omega)
  braid i hi := h.braid i (by omega)
  far i j hij hj := h.far i j hij (by omega)

theorem cyc_far {N : ℕ} (h : CoxRel τ N) {a : ℕ} (ha : a < N) :
    ∀ t, t + 1 ≤ a → τ a * ev τ (cyc t) = ev τ (cyc t) * τ a
  | 0, _ => by simp [cyc]
  | t + 1, ht => by
    rw [cyc_succ, ev_cons, ← mul_assoc, ← h.far t a (by omega) ha, mul_assoc,
      cyc_far h ha t (by omega), mul_assoc]

theorem cyc_braid {N : ℕ} (h : CoxRel τ N) (g : ℕ) :
    ∀ t, g + 1 < t → t ≤ N → τ g * ev τ (cyc t) = ev τ (cyc t) * τ (g + 1) := by
  intro t ht hN
  induction t, ht using Nat.le_induction with
  | base =>
    rw [cyc_succ, cyc_succ, ev_cons, ev_cons]
    calc τ g * (τ (g + 1) * (τ g * ev τ (cyc g)))
        = (τ g * τ (g + 1) * τ g) * ev τ (cyc g) := by simp only [mul_assoc]
      _ = (τ (g + 1) * τ g * τ (g + 1)) * ev τ (cyc g) := by rw [h.braid g (by omega)]
      _ = τ (g + 1) * (τ g * (τ (g + 1) * ev τ (cyc g))) := by simp only [mul_assoc]
      _ = τ (g + 1) * (τ g * (ev τ (cyc g) * τ (g + 1))) := by
          rw [cyc_far h (by omega) g le_rfl]
      _ = τ (g + 1) * (τ g * ev τ (cyc g)) * τ (g + 1) := by simp only [mul_assoc]
  | succ t ht ih =>
    rw [cyc_succ, ev_cons, ← mul_assoc, h.far g t (by omega) (by omega), mul_assoc,
      ih (by omega), mul_assoc]

/-- A full listing of the states below `N + 1`. -/
structure Full (N : ℕ) (ts : List ℕ) : Prop where
  length : ts.length = N + 1
  nodup : ts.Nodup
  bound : ∀ t ∈ ts, t < N + 1

theorem Full.rest {N : ℕ} {t : ℕ} {ts : List ℕ} (h : Full (N + 1) (t :: ts)) :
    Full N (ts.map (pout t)) where
  length := by have := h.length; simp at this ⊢; omega
  nodup := nodup_map_pout h.nodup
  bound y hy := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have hzt : z ≠ t := by
      rintro rfl; have := h.nodup; rw [List.nodup_cons] at this; exact this.1 hz
    have := h.bound z (by simp [hz]); have := h.bound t (by simp)
    unfold pout; split_ifs <;> omega

theorem Full.map_act {N : ℕ} {ts : List ℕ} (h : Full N ts) {w : CW} (hw : Valid N w) :
    Full N (ts.map (act w)) where
  length := by simp [h.length]
  nodup := h.nodup.map (fun _ _ e => act_inj e)
  bound y hy := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact act_lt hw (h.bound z hz)

theorem full_range (N : ℕ) : Full N (List.range (N + 1)) where
  length := List.length_range
  nodup := List.nodup_range
  bound _ ht := List.mem_range.1 ht

/-- A generator times a normal form is the normal form of the product. -/
theorem key : ∀ (N : ℕ) (τ : ℕ → M), CoxRel τ N → ∀ g, g < N → ∀ ts, Full N ts →
    τ g * ev τ (frame ts) = ev τ (frame (ts.map (sw g)))
  | 0, _, _, g, hg, _, _ => absurd hg (Nat.not_lt_zero g)
  | N + 1, τ, h, g, hg, [], hf => by have := hf.length; simp at this
  | N + 1, τ, h, g, hg, t :: rest, hf => by
    have hrest : ∀ y ∈ rest, y ≠ t := by
      intro y hy e; subst e; have := hf.nodup; rw [List.nodup_cons] at this; exact this.1 hy
    have ht : t < N + 2 := hf.bound t (by simp)
    rw [List.map_cons, frame_cons, frame_cons, ev_append, ev_append, ev_map_succ, ev_map_succ,
      List.map_map]
    rcases lt_trichotomy t g with htg | heq | htg
    · -- the generator is above `t`: it passes `cyc t` and goes up one wire
      have hs : sw g t = t := by unfold sw; split_ifs <;> omega
      have hlist : rest.map (pout (sw g t) ∘ sw g) = (rest.map (pout t)).map (sw (g - 1)) := by
        rw [List.map_map]; apply List.map_congr_left; intro y hy
        have := hrest y hy
        simp only [Function.comp, hs]; unfold pout sw; split_ifs <;> omega
      rw [hlist, hs, ← mul_assoc, cyc_far h hg t (by omega), mul_assoc]
      congr 1
      have ih := key N (fun i => τ (i + 1)) h.shift (g - 1) (by omega) _ hf.rest
      beta_reduce at ih ⊢
      rwa [show g - 1 + 1 = g by omega] at ih
    · -- the generator is `t`: `t :: cyc t = cyc (t + 1)`
      subst heq
      have hs : sw t t = t + 1 := by simp [sw]
      have hlist : rest.map (pout (sw t t) ∘ sw t) = rest.map (pout t) := by
        apply List.map_congr_left; intro y hy
        have := hrest y hy
        simp only [Function.comp, hs]; unfold pout sw; split_ifs <;> omega
      rw [hlist, hs, cyc_succ, ev_cons, mul_assoc]
    · rcases Nat.lt_or_ge (g + 1) t with htg' | htg'
      · -- the generator is below `t - 1`: it passes `cyc t` as the next one up
        have hs : sw g t = t := by unfold sw; split_ifs <;> omega
        have hlist : rest.map (pout (sw g t) ∘ sw g) = (rest.map (pout t)).map (sw g) := by
          rw [List.map_map]; apply List.map_congr_left; intro y hy
          have := hrest y hy
          simp only [Function.comp, hs]; unfold pout sw; split_ifs <;> omega
        rw [hlist, hs, ← mul_assoc, cyc_braid h g t htg' (by omega), mul_assoc]
        congr 1
        exact key N (fun i => τ (i + 1)) h.shift g (by omega) _ hf.rest
      · -- the generator is `t - 1`: `(t - 1) :: cyc t = cyc (t - 1)` after cancelling
        have hgt : t = g + 1 := by omega
        subst hgt
        have hs : sw g (g + 1) = g := by simp [sw]
        have hlist : rest.map (pout (sw g (g + 1)) ∘ sw g) = rest.map (pout (g + 1)) := by
          apply List.map_congr_left; intro y hy
          have := hrest y hy
          simp only [Function.comp, hs]; unfold pout sw; split_ifs <;> omega
        rw [hlist, hs, cyc_succ, ev_cons, ← mul_assoc, ← mul_assoc, h.order g hg, one_mul]
theorem ev_append_frame {N : ℕ} (h : CoxRel τ N) :
    ∀ (w : CW), Valid N w → ∀ ts, Full N ts → ev τ (w ++ frame ts) = ev τ (frame (ts.map (act w)))
  | [], _, ts, _ => by
    have e : ts.map (act []) = ts := by
      conv_rhs => rw [← List.map_id ts]
      rfl
    rw [List.nil_append, e]
  | g :: w, hw, ts, hf => by
    have hw' : Valid N w := fun i hi => hw i (List.mem_cons_of_mem _ hi)
    rw [List.cons_append, ev_cons, ev_append_frame h w hw' ts hf,
      key N τ h g (hw g (by simp)) _ (hf.map_act hw'), List.map_map]
    rfl

/-- A word is the normal form of its permutation. -/
theorem ev_eq_frame {N : ℕ} (h : CoxRel τ N) {w : CW} (hw : Valid N w) :
    ev τ w = ev τ (frame ((List.range (N + 1)).map (act w))) := by
  rw [← ev_append_frame h w hw _ (full_range N), frame_range, List.append_nil]

/-- Two words with the same permutation have the same value. -/
theorem perm_complete {N : ℕ} (h : CoxRel τ N) {p q : CW} (hp : Valid N p) (hq : Valid N q)
    (e : ∀ x, x < N + 1 → act p x = act q x) : ev τ p = ev τ q := by
  have : (List.range (N + 1)).map (act p) = (List.range (N + 1)).map (act q) :=
    List.map_congr_left (fun x hx => e x (List.mem_range.1 hx))
  rw [ev_eq_frame h hp, ev_eq_frame h hq, this]

/-- A word followed by its inverse. -/
theorem ev_inv {N : ℕ} (h : CoxRel τ N) {p : CW} (hp : Valid N p) : ev τ p * ev τ (inv p) = 1 := by
  induction p with
  | nil => simp [inv]
  | cons i p ih =>
    have hp' : Valid N p := fun j hj => hp j (List.mem_cons_of_mem _ hj)
    rw [inv, List.reverse_cons, ev_append, ev_cons]
    calc τ i * ev τ p * (ev τ p.reverse * ev τ [i])
        = τ i * (ev τ p * ev τ (inv p)) * ev τ [i] := by simp only [inv, mul_assoc]
      _ = 1 := by rw [ih hp', mul_one]; simp [h.order i (hp i (by simp))]

theorem ev_inv' {N : ℕ} (h : CoxRel τ N) {p : CW} (hp : Valid N p) : ev τ (inv p) * ev τ p = 1 := by
  have := ev_inv h (valid_inv hp)
  rwa [inv, inv, List.reverse_reverse] at this

/-- Elements that every `τ i` with `j ≤ i < N` commutes with. -/
def CommGe (N j : ℕ) (b : M) : Prop := ∀ i, j ≤ i → i < N → τ i * b = b * τ i

theorem comm_word {N j : ℕ} {b : M} (cb : CommGe (τ := τ) N j b) :
    ∀ w : CW, (∀ i ∈ w, j ≤ i ∧ i < N) → ev τ w * b = b * ev τ w
  | [], _ => by simp
  | i :: w, hw => by
    rw [ev_cons, mul_assoc, comm_word cb w (fun k hk => hw k (List.mem_cons_of_mem _ hk)),
      ← mul_assoc, cb i (hw i (by simp)).1 (hw i (by simp)).2, mul_assoc]

/-- The frame of states whose first `j` are `0, …, j-1` has letters `≥ j`. -/
theorem frame_ge : ∀ (j : ℕ) (ts : List ℕ), ts.Nodup → (∀ i < j, ts[i]? = some i) →
    ∀ l ∈ frame ts, j ≤ l
  | 0, _, _, _, l, _ => Nat.zero_le l
  | j + 1, [], _, h, l, _ => by have := h 0 (by omega); simp at this
  | j + 1, t :: ts, hd, h, l, hl => by
    have ht : t = 0 := by have := h 0 (by omega); simpa using this
    subst ht
    rw [frame_cons, cyc, List.range_zero, List.reverse_nil, List.nil_append] at hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    have := frame_ge j (ts.map (pout 0)) (nodup_map_pout hd) (by
      intro i hi
      have := h (i + 1) (by omega)
      simp only [List.getElem?_cons_succ] at this
      rw [List.getElem?_map, this]; simp [pout]) l' hl'
    omega

/-- A word fixing the states below `j` commutes with `b` (the Agda's `stab`). -/
theorem stab {N j : ℕ} (h : CoxRel τ N) (hj : j ≤ N + 1) {b : M} (cb : CommGe (τ := τ) N j b)
    {r : CW} (hr : Valid N r) (fix : ∀ x, x < j → act r x = x) : ev τ r * b = b * ev τ r := by
  rw [ev_eq_frame h hr]
  have hf := (full_range N).map_act hr
  apply comm_word cb
  intro l hl
  refine ⟨frame_ge j _ hf.nodup (fun i hi => ?_) l hl, frame_valid N _ hf.nodup hf.bound l hl⟩
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  simp [fix i hi]

/-- Frames: `b` conjugated by two words that agree below `j` (the Agda's
`frame≈`). -/
theorem frame_eq {N j : ℕ} (h : CoxRel τ N) (hj : j ≤ N + 1) {b : M} (cb : CommGe (τ := τ) N j b)
    {p q : CW} (hp : Valid N p) (hq : Valid N q) (e : ∀ x, x < j → act p x = act q x) :
    ev τ p * b * ev τ (inv p) = ev τ q * b * ev τ (inv q) := by
  set r := inv q ++ p
  have hr : Valid N r := valid_append (valid_inv hq) hp
  have fix : ∀ x, x < j → act r x = x := by
    intro x hx; rw [act_append, e x hx, act_inv]
  have hpr : ev τ p = ev τ q * ev τ r := by
    rw [ev_append, ← mul_assoc, ev_inv h hq, one_mul]
  have hri : ev τ r * ev τ (inv p) = ev τ (inv q) := by
    rw [ev_append, mul_assoc, ev_inv h hp, mul_one]
  rw [hpr, mul_assoc (ev τ q), stab h hj cb hr fix, mul_assoc, mul_assoc, hri, ← mul_assoc]

end Monoid

/-! ## Coxeter words as words over an alphabet -/

section Circuits

variable {A : Type*} (T : ℕ → Word A)

/-- A Coxeter word read with `T d` for its letter `d`. -/
def Pc (w : CW) : Word A := (w.map T).prod

theorem Pc_append (u v : CW) : Pc T (u ++ v) = Pc T u * Pc T v := by simp [Pc]

theorem Pc_cons (i : ℕ) (w : CW) : Pc T (i :: w) = T i * Pc T w := by simp [Pc]

/-- The Coxeter relations for the words `T d`, `d ≤ 6`, modulo `Γ`. -/
structure Coxeter (Γ : WRel A) : Prop where
  order : ∀ i, i ≤ 6 → Derivable Γ (T i * T i) 1
  braid : ∀ i, i ≤ 5 → Derivable Γ (T i * T (i + 1) * T i) (T (i + 1) * T i * T (i + 1))
  far : ∀ i j, 2 + i ≤ j → j ≤ 6 → Derivable Γ (T i * T j) (T j * T i)

/-- A circuit conjugated by a Coxeter word. -/
def Fr (b : Word A) (p : CW) : Word A := Pc T p * b * Pc T (inv p)

theorem Fr_conj (b : Word A) (r p : CW) :
    Pc T r * Fr T b p * Pc T (inv r) = Fr T b (r ++ p) := by
  simp only [Fr, inv, List.reverse_append, Pc_append, mul_assoc]

variable {T} {Γ : WRel A}

/-- The class of a word modulo `Γ`. -/
abbrev cl (Γ : WRel A) (w : Word A) : (conGen Γ).Quotient := (conGen Γ).mk' w

theorem cl_eq {w v : Word A} : cl Γ w = cl Γ v ↔ Derivable Γ w v := (conGen Γ).eq

theorem cl_mul (w v : Word A) : cl Γ (w * v) = cl Γ w * cl Γ v := map_mul _ w v

theorem cl_one : cl Γ 1 = 1 := map_one _

theorem cl_Pc (w : CW) : cl Γ (Pc T w) = ev (fun i => cl Γ (T i)) w := by
  induction w with
  | nil => exact cl_one
  | cons i w ih => rw [Pc_cons, cl_mul, ih, ev_cons]

theorem Coxeter.rel (cox : Coxeter T Γ) : CoxRel (fun i => cl Γ (T i)) 7 where
  order i hi := by
    show cl Γ (T i) * cl Γ (T i) = 1
    rw [← cl_mul, ← cl_one]; exact cl_eq.2 (cox.order i (by omega))
  braid i hi := by
    show cl Γ (T i) * cl Γ (T (i + 1)) * cl Γ (T i) = cl Γ (T (i + 1)) * cl Γ (T i) * cl Γ (T (i + 1))
    simp only [← cl_mul]; exact cl_eq.2 (cox.braid i (by omega))
  far i j hij hj := by
    show cl Γ (T i) * cl Γ (T j) = cl Γ (T j) * cl Γ (T i)
    simp only [← cl_mul]; exact cl_eq.2 (cox.far i j (by omega) (by omega))

/-- Words in `T d` commuting with `b` for every `d ≥ j` (the Agda's
`Comm≥`). -/
def CommGeW (Γ : WRel A) (T : ℕ → Word A) (j : ℕ) (b : Word A) : Prop :=
  ∀ i, j ≤ i → i ≤ 6 → Derivable Γ (T i * b) (b * T i)

theorem CommGeW.toCommGe {j : ℕ} {b : Word A} (cb : CommGeW Γ T j b) :
    CommGe (τ := fun i => cl Γ (T i)) 7 j (cl Γ b) := by
  intro i hi hi'
  show cl Γ (T i) * cl Γ b = cl Γ b * cl Γ (T i)
  simp only [← cl_mul]; exact cl_eq.2 (cb i hi (by omega))

variable (cox : Coxeter T Γ)
include cox

/-- Two Coxeter words of `S₈` with the same permutation are equal circuits. -/
theorem Pc_complete {p q : CW} (hp : Valid 7 p) (hq : Valid 7 q)
    (e : ∀ x, x < 8 → act p x = act q x) : Derivable Γ (Pc T p) (Pc T q) := by
  apply cl_eq.1; rw [cl_Pc, cl_Pc]; exact perm_complete cox.rel hp hq e

/-- A Coxeter word followed by its inverse. -/
theorem Pc_inv {p : CW} (hp : Valid 7 p) : Derivable Γ (Pc T p * Pc T (inv p)) 1 := by
  apply cl_eq.1; rw [cl_mul, cl_Pc, cl_Pc, ev_inv cox.rel hp, cl_one]

theorem Pc_inv' {p : CW} (hp : Valid 7 p) : Derivable Γ (Pc T (inv p) * Pc T p) 1 := by
  apply cl_eq.1; rw [cl_mul, cl_Pc, cl_Pc, ev_inv' cox.rel hp, cl_one]

/-- Frames: `b` conjugated by two Coxeter words that agree below `j`. -/
theorem frame_eqW {j : ℕ} (hj : j ≤ 8) {b : Word A} (cb : CommGeW Γ T j b) {p q : CW}
    (hp : Valid 7 p) (hq : Valid 7 q) (e : ∀ x, x < j → act p x = act q x) :
    Derivable Γ (Fr T b p) (Fr T b q) := by
  apply cl_eq.1
  simp only [Fr, cl_mul, cl_Pc]
  exact frame_eq cox.rel hj cb.toCommGe hp hq e

end Circuits

end QCert.ToffoliHadamardRS.CoxeterFrames
