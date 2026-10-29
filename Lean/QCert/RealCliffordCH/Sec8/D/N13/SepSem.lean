/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Gates separated on a wire commute in the semantics

Two gates controlled on a wire `p` with opposite colours commute: one acts as
the identity on the states where wire `p` is `0`, the other where it is `1`
(`Triv`, `Triv.comm`).  Conjugating by a circuit that carries wire `p` to a
wire `q` and back (`Route`) moves this property from `q` to `p`
(`Triv.conj`).  For words of engine letters, `rtW` follows a wire through a
word (swaps move it, other letters must avoid it) and `route_wc` turns that
computation into `Route`.

These are semantic facts proved once, for all words: they replace the
semantic windows the engine decides by simulation (`SE.lcheck`), whose kernel
cost grows with the letters and the wires (one window of 34 letters on five
wires passed 4.5 GB).
-/
import QCert.RealCliffordCH.Sec8.D.N13.Sem

namespace QCert.RealCliffordCH.Sec8.D.N13.Sep

open Matrix Circuit Eng SE Net N8 Sim

variable {N : ℕ}

/-! ## Operators -/

/-- `U` carries the value of wire `a` (of its input) to wire `b` (of its output). -/
def Route (a b : ℕ) (U : Op Q 2 N) : Prop := ∀ s t, MS.bit s b ≠ MS.bit t a → U s t = 0

/-- `U` is the identity on the states whose wire `p` is `v`. -/
def Triv (p : ℕ) (v : Fin 2) (U : Op Q 2 N) : Prop :=
  ∀ s t, (MS.bit s p = v ∨ MS.bit t p = v) → U s t = (1 : Op Q 2 N) s t

theorem fin2_eq : ∀ {x y v : Fin 2}, x ≠ v → y ≠ v → x = y := by decide

theorem fin2_or : ∀ {v w : Fin 2}, v ≠ w → ∀ x : Fin 2, x = v ∨ x = w := by decide

theorem Route.mul {a b c : ℕ} {U W : Op Q 2 N} (hW : Route a b W) (hU : Route b c U) :
    Route a c (U * W) := by
  intro s t h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : MS.bit u b = MS.bit t a
  · rw [hU s u (by rw [hu]; exact h), zero_mul]
  · rw [hW u t hu, mul_zero]

theorem Route.one (a : ℕ) : Route a a (1 : Op Q 2 N) := by
  intro s t h
  exact Matrix.one_apply_ne (fun e => h (e ▸ rfl))

theorem Route.congr {a b : ℕ} {U V : Op Q 2 N} (h : Route a b U) (e : U = V) : Route a b V :=
  e ▸ h

theorem Triv.zero {p : ℕ} {v : Fin 2} {U : Op Q 2 N} (h : Triv p v U) {s t : State 2 N}
    (hst : MS.bit s p ≠ MS.bit t p) : U s t = 0 := by
  have hne : s ≠ t := fun e => hst (e ▸ rfl)
  by_cases hs : MS.bit s p = v
  · rw [h s t (Or.inl hs)]; exact Matrix.one_apply_ne hne
  by_cases ht : MS.bit t p = v
  · rw [h s t (Or.inr ht)]; exact Matrix.one_apply_ne hne
  exact absurd (fin2_eq hs ht) hst

theorem Triv.row {p : ℕ} {v : Fin 2} {U : Op Q 2 N} (h : Triv p v U) {s : State 2 N}
    (hs : MS.bit s p = v) (W : Op Q 2 N) (t : State 2 N) : (U * W) s t = W s t := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [h s s (Or.inl hs), Matrix.one_apply_eq, one_mul]
  · intro u _ hu; rw [h s u (Or.inl hs), Matrix.one_apply_ne (Ne.symm hu), zero_mul]
  · intro hs'; exact absurd (Finset.mem_univ s) hs'

theorem Triv.col {p : ℕ} {v : Fin 2} {U : Op Q 2 N} (h : Triv p v U) {t : State 2 N}
    (ht : MS.bit t p = v) (W : Op Q 2 N) (s : State 2 N) : (W * U) s t = W s t := by
  rw [Matrix.mul_apply, Finset.sum_eq_single t]
  · rw [h t t (Or.inr ht), Matrix.one_apply_eq, mul_one]
  · intro u _ hu; rw [h u t (Or.inr ht), Matrix.one_apply_ne hu, mul_zero]
  · intro ht'; exact absurd (Finset.mem_univ t) ht'

theorem Triv.cross {p : ℕ} {v w : Fin 2} {U W : Op Q 2 N} (hU : Triv p v U) (hW : Triv p w W)
    {s t : State 2 N} (hst : MS.bit s p ≠ MS.bit t p) : (U * W) s t = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : MS.bit s p = MS.bit u p
  · rw [hW.zero (fun e => hst (hu.trans e)), mul_zero]
  · rw [hU.zero hu, zero_mul]

/-- Gates trivial on complementary blocks of one wire commute. -/
theorem Triv.comm {p : ℕ} {v w : Fin 2} {U W : Op Q 2 N} (hU : Triv p v U) (hW : Triv p w W)
    (hvw : v ≠ w) : U * W = W * U := by
  funext s t
  by_cases hst : MS.bit s p = MS.bit t p
  · rcases fin2_or hvw (MS.bit s p) with hs | hs
    · rw [hU.row hs, hU.col (hst.symm.trans hs)]
    · rw [hW.col (hst.symm.trans hs), hW.row hs]
  · rw [hU.cross hW hst, hW.cross hU hst]

theorem Triv.one (p : ℕ) (v : Fin 2) : Triv p v (1 : Op Q 2 N) := fun _ _ _ => rfl

theorem Triv.mul {p : ℕ} {v : Fin 2} {U W : Op Q 2 N} (hU : Triv p v U) (hW : Triv p v W) :
    Triv p v (U * W) := by
  intro s t h
  rcases h with hs | ht
  · rw [hU.row hs]; exact hW s t (Or.inl hs)
  · rw [hW.col ht]; exact hU s t (Or.inr ht)

/-- Conjugation by a circuit carrying wire `p` to wire `q` (and its inverse
carrying it back). -/
theorem Triv.conj {p q : ℕ} {v : Fin 2} {P P' X : Op Q 2 N} (hP : Route q p P)
    (hP' : Route p q P') (hinv : P * P' = 1) (hX : Triv q v X) : Triv p v (P * X * P') := by
  intro s t h
  rcases h with hs | ht
  · have e : ∀ u, (P * X) s u = P s u := by
      intro u
      conv_rhs => rw [← Matrix.mul_one P]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hw : MS.bit w q = v
      · rw [hX w u (Or.inl hw)]
      · rw [hP s w (fun e => hw (e.symm.trans hs)), zero_mul, zero_mul]
    rw [Matrix.mul_apply]
    simp only [e]
    rw [← Matrix.mul_apply, hinv]
  · have e : ∀ u, (X * P') u t = P' u t := by
      intro u
      conv_rhs => rw [← Matrix.one_mul P']
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hw : MS.bit w q = v
      · rw [hX u w (Or.inr hw)]
      · rw [hP' w t (fun e => hw (e.trans ht)), mul_zero, mul_zero]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [e]
    rw [← Matrix.mul_apply, hinv]

/-! ## Gates -/

theorem route_onW {a : ℕ} (ha : a < N) {ws : List ℕ} (hws : a ∉ ws) {k : ℕ} (G : Op Q 2 k) :
    Route a a (MS.onW N ws G) := by
  intro s t h
  unfold MS.onW
  rw [if_neg (fun H => h (H a ha hws))]

theorem route_lamOp {a : ℕ} (ha : a < N) {tg : List ℕ} (hat : a ∉ tg) (c : ℕ → Option Bool)
    {k : ℕ} (U : Op Q 2 k) : Route a a (MS.lamOp N tg c U) := by
  intro s t h
  unfold MS.lamOp
  rw [if_neg (fun H => h (H a ha hat))]

theorem route_swAt {j a : ℕ} (hj : j + 2 ≤ N) (ha : a < N) :
    Route a (MS.tau j a) (opsQ.eval N (swAt N j)) := by
  intro s t h
  rw [MS.eval_swAt hj]
  unfold MS.pOp
  rw [if_neg]
  intro e
  apply h
  have hb : MS.tau j a < N := by unfold MS.tau; split_ifs <;> omega
  rw [e, MS.bit_permSt _ _ hb, MS.tau_tau]

/-- A multi-controlled gate is trivial where one of its controls does not match. -/
theorem triv_lamOp {a : ℕ} {tg : List ℕ} {c : ℕ → Option Bool} (U : Op Q 2 a) {p : ℕ}
    (hp : p < N) (hpt : p ∉ tg) {b : Bool} (hc : c p = some b) (ha : tg.length = a) :
    Triv p (if b then 0 else 1) (MS.lamOp N tg c U) := by
  intro s t hst
  unfold MS.lamOp
  by_cases hag : ∀ j < N, j ∉ tg → MS.bit s j = MS.bit t j
  · rw [if_pos hag]
    have hm : ¬ MS.Match N tg c t := by
      intro hm
      have h1 := hm p hp hpt b hc
      have h2 := hag p hp hpt
      rcases hst with h | h <;> cases b <;> simp_all
    rw [if_neg hm]
    by_cases hst' : s = t
    · subst hst'; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hst', Matrix.one_apply_ne]
      intro e
      apply hst'
      apply MS.state_ext
      intro j hj
      by_cases hj' : j ∈ tg
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hj'
        have := congrFun e ⟨i, ha ▸ hi⟩
        simpa [MS.rd, List.getElem?_eq_getElem hi] using this
      · exact hag j hj hj'
  · rw [if_neg hag]
    have hne : s ≠ t := fun e => hag (fun j _ _ => e ▸ rfl)
    exact (Matrix.one_apply_ne hne).symm

/-! ## Words of engine letters -/

/-- Where a letter carries a local wire: a swap moves it, any other letter
must avoid it (`none` otherwise). -/
def rt : Lt → ℕ → Option ℕ
  | .s (.S j), a => some (MS.tau j a)
  | .s l, a => if l.lo + l.wd ≤ a ∨ a < l.lo then some a else none
  | .g _ tg _ _, a => if a ∈ tg then none else some a

/-- Where a word (in drawn order) carries a local wire. -/
def rtW : List Lt → ℕ → Option ℕ
  | [], a => some a
  | x :: l, a => (rt x a).bind (rtW l)

theorem rt_sound {K : ℕ} (hKN : K ≤ N) (x : Lt) (hx : x.ok K = true) {a b : ℕ} (ha : a < K)
    (h : rt x a = some b) : b < K ∧ Route a b (opsQ.eval N (x.circ K N)) := by
  cases x with
  | s l =>
    simp only [Lt.ok, decide_eq_true_eq] at hx
    cases l with
    | S j =>
      simp only [rt, Option.some.injEq] at h
      subst h
      simp only [L.lo, L.wd] at hx
      refine ⟨by unfold MS.tau; split_ifs <;> omega, ?_⟩
      exact route_swAt (by omega) (by omega)
    | H j =>
      simp only [rt, L.lo, L.wd] at h hx
      split_ifs at h with hc
      cases h
      refine ⟨ha, ?_⟩
      show Route a a (opsQ.eval N (place1 N j h))
      rw [MS.eval_place1 N j _ (by omega)]
      exact route_onW (by omega) (by simp; omega) _
    | Z j =>
      simp only [rt, L.lo, L.wd] at h hx
      split_ifs at h with hc
      cases h
      refine ⟨ha, ?_⟩
      show Route a a (opsQ.eval N (place1 N j z))
      rw [MS.eval_place1 N j _ (by omega)]
      exact route_onW (by omega) (by simp; omega) _
    | C j =>
      simp only [rt, L.lo, L.wd] at h hx
      split_ifs at h with hc
      cases h
      refine ⟨ha, ?_⟩
      show Route a a (opsQ.eval N (place2 N j cz))
      rw [MS.eval_place2 N j _ (by omega)]
      exact route_onW (by omega) (by simp; omega) _
    | K j =>
      simp only [rt, L.lo, L.wd] at h hx
      split_ifs at h with hc
      cases h
      refine ⟨ha, ?_⟩
      show Route a a (opsQ.eval N (place2 N j ch))
      rw [MS.eval_place2 N j _ (by omega)]
      exact route_onW (by omega) (by simp; omega) _
  | g Kd tg cs bb =>
    simp only [rt] at h
    split_ifs at h with hat
    cases h
    simp only [Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hx
    obtain ⟨⟨hnd, hlt⟩, har⟩ := hx
    refine ⟨ha, ?_⟩
    show Route a a (opsQ.eval N (mc N Kd tg (ctl K cs bb)))
    rw [MS.eval_mc _ hnd (fun j hj => by have := hlt j hj; simp at this; omega) har]
    exact route_lamOp (by omega) hat _ _

theorem route_wc {K : ℕ} (hKN : K ≤ N) : ∀ (w : List Lt), (∀ x ∈ w, x.ok K = true) →
    ∀ {a b : ℕ}, a < K → rtW w a = some b → Route a b (opsQ.eval N (wc K N w))
  | [], _, a, b, _, h => by
    simp only [rtW, Option.some.injEq] at h
    subst h
    simpa [wc, drawn] using Route.one (N := N) a
  | x :: l, hw, a, b, ha, h => by
    simp only [rtW] at h
    cases hx : rt x a with
    | none => rw [hx] at h; simp at h
    | some c =>
      rw [hx] at h
      simp only [Option.bind_some] at h
      obtain ⟨hc, r1⟩ := rt_sound hKN x (hw x (by simp)) ha hx
      have r2 := route_wc hKN l (fun y hy => hw y (by simp [hy])) hc h
      rw [wc_cons, map_mul]
      exact Route.mul r1 r2

/-- A multi-controlled letter is trivial where one of its local controls does
not match. -/
theorem triv_g {K : ℕ} (hKN : K ≤ N) (Kd : Kind) (tg : List ℕ) (cs : List (ℕ × Bool)) (bb : Bool)
    (hx : (Lt.g Kd tg cs bb).ok K = true) {p : ℕ} (hp : p < K) (hpt : p ∉ tg) {b : Bool}
    (hl : cs.lookup p = some b) :
    Triv p (if b then 0 else 1) (opsQ.eval N ((Lt.g Kd tg cs bb).circ K N)) := by
  simp only [Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hx
  obtain ⟨⟨hnd, hlt⟩, har⟩ := hx
  show Triv p _ (opsQ.eval N (mc N Kd tg (ctl K cs bb)))
  rw [MS.eval_mc _ hnd (fun j hj => by have := hlt j hj; simp at this; omega) har]
  exact triv_lamOp _ (by omega) hpt (by simp [ctl, hp, hl]) har

/-- A letter conjugated by a word that carries wire `p` to the letter's
wire `q`: trivial on the same block of `p` as the letter on `q`. -/
theorem triv_conj {K : ℕ} (hKN : K ≤ N) {u u' : List Lt} {X : Circ N} {p q : ℕ} {v : Fin 2}
    (hu : ∀ x ∈ u, x.ok K = true) (hu' : ∀ x ∈ u', x.ok K = true) (hp : p < K) (hq : q < K)
    (r : rtW u p = some q) (r' : rtW u' q = some p)
    (hinv : opsQ.eval N (wc K N u') * opsQ.eval N (wc K N u) = 1)
    (hX : Triv q v (opsQ.eval N X)) :
    Triv p v (opsQ.eval N (wc K N u' * X * wc K N u)) := by
  rw [map_mul, map_mul]
  exact Triv.conj (route_wc hKN u' hu' hq r') (route_wc hKN u hu hp r) hinv hX

/-- Two words trivial on complementary blocks of a wire commute in the
semantics. -/
theorem sep_sem {K M : ℕ} {u w : List Lt} {p : ℕ} {v v' : Fin 2} (hvv : v ≠ v')
    (hu : Triv p v (opsQ.eval M (wc K M u))) (hw : Triv p v' (opsQ.eval M (wc K M w))) :
    S.sem M (wc K M (u ++ w)) = S.sem M (wc K M (w ++ u)) := by
  apply sem_of_eval
  rw [wc_append, wc_append, map_mul, map_mul]
  exact Triv.comm hw hu hvv.symm

end QCert.RealCliffordCH.Sec8.D.N13.Sep
