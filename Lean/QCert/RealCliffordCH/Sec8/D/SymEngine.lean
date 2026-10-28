/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A rewriting engine at every width

The equations of Appendix D.5 are schemas: on `N` wires, with a few *local*
wires `0, …, K - 1` at the bottom and the *bulk* `K, …, N - 1` above, every
multi-controlled gate having the bulk as black controls (or not touching it).
Here such circuits are words of letters (`Lt`): the small letters of `EngineN`
on local wires, and multi-controlled gates `g Kd tg cs b` (special wires `tg`,
local controls `cs`, the bulk black if `b`), read on `m + K` wires for every
`m` (`wc`).

* Semantics (`eval_wc_blk`): a word is block diagonal in the bulk; on the
  block where the bulk is all `1` it is the word read on `K` wires (`onW`),
  elsewhere the word without its bulk-controlled gates (`offW`).  So two words
  have the same semantics at every width as soon as two identities on `K`
  wires hold, decided by `Fast.check`.
* A derivation is a list of steps (`St`): rewriting with an equation of a
  table of schemas (`rw`), exchanging two small letters on disjoint wires
  (`sw`), and Lemma 5.1 (`sem`): a window of letters none of which touches
  the local wire `q` is replaced by another one, when the two, with wire `q`
  removed, have the same semantics (decided on `K - 1` wires).  The window is
  carried to a circuit idle on the top wire by the swaps moving wire `q` up;
  that each letter is carried there to its version without wire `q` is the
  hypothesis `Frame` (the placement lemmas of `Net`).
* `check_sound`: a run that passes `check` (a Boolean, decided by
  `decide +kernel`) is a derivation on `m + K` wires for every `m`, given
  completeness below (`IH`).
-/
import QCert.RealCliffordCH.Sec8.MCSem
import QCert.RealCliffordCH.Sec8.Fast
import QCert.RealCliffordCH.Sec8.EngineN

namespace QCert.RealCliffordCH.Sec8.SE

open Matrix Circuit Eng MS

/-! ## Letters -/

/-- Letters: small gates on local wires, and multi-controlled gates. -/
inductive Lt
  /-- a small gate -/
  | s (l : L)
  /-- `mc` of kind `Kd`, special wires `tg`, local controls `cs`, the bulk
  black controls if `b`, untouched otherwise -/
  | g (Kd : Kind) (tg : List ℕ) (cs : List (ℕ × Bool)) (b : Bool)
  deriving DecidableEq, Repr

/-- The controls of a multi-controlled letter on local width `K`. -/
def ctl (K : ℕ) (cs : List (ℕ × Bool)) (b : Bool) : ℕ → Option Bool :=
  fun j => if j < K then cs.lookup j else if b then some true else none

namespace Lt

/-- A letter on `N` wires, local width `K`. -/
def circ (K N : ℕ) : Lt → Circ N
  | s l => l.circ N
  | g Kd tg cs b => mc N Kd tg (ctl K cs b)

/-- A letter is well formed on `K` local wires. -/
def ok (K : ℕ) : Lt → Bool
  | s l => decide (l.lo + l.wd ≤ K)
  | g Kd tg _ _ => decide tg.Nodup && tg.all (· < K) && (tg.length == Kd.ar)

/-- The letter on the bulk-all-`1` block, on `K` wires. -/
def on (K : ℕ) : Lt → Circ K
  | s l => l.circ K
  | g Kd tg cs b => mc K Kd tg (ctl K cs b)

/-- The letter on the other blocks, on `K` wires. -/
def off (K : ℕ) : Lt → Circ K
  | s l => l.circ K
  | g Kd tg cs b => if b then 1 else mc K Kd tg (ctl K cs b)

end Lt

/-- A word of letters, in drawn order. -/
def wc (K N : ℕ) (l : List Lt) : Circ N := drawn (l.map (Lt.circ K N))

def onW (K : ℕ) (l : List Lt) : Circ K := drawn (l.map (Lt.on K))
def offW (K : ℕ) (l : List Lt) : Circ K := drawn (l.map (Lt.off K))

theorem drawn_cons {n : ℕ} (a : Circ n) (l : List (Circ n)) : drawn (a :: l) = drawn l * a := by
  simp [drawn, List.prod_append]

theorem drawn_append {n : ℕ} (a b : List (Circ n)) : drawn (a ++ b) = drawn b * drawn a := by
  simp [drawn, List.prod_append]

theorem wc_cons (K N : ℕ) (x : Lt) (l : List Lt) : wc K N (x :: l) = wc K N l * x.circ K N := by
  simp [wc, drawn_cons]

theorem wc_append (K N : ℕ) (a b : List Lt) : wc K N (a ++ b) = wc K N b * wc K N a := by
  simp [wc, drawn_append]

/-! ## Semantics: block diagonal in the bulk -/

theorem topMatch_ctl {K m : ℕ} (cs : List (ℕ × Bool)) (b : Bool) (h : State 2 m) :
    TopMatch K (ctl K cs b) h ↔ (b = true → ∀ j, h j = 1) := by
  unfold TopMatch ctl
  constructor
  · intro H hb j
    have := H j true (by simp [hb])
    simpa using this
  · intro H j bb hbb
    rw [if_neg (by omega)] at hbb
    cases b
    · simp at hbb
    · simp only [if_true, Option.some.injEq] at hbb
      subst hbb; simpa using H rfl j

theorem eval_L_blk {m K : ℕ} (l : L) (hl : l.lo + l.wd ≤ K) :
    opsQ.eval (m + K) (l.circ (m + K)) =
      blk (m := m) (k := K) fun _ => opsQ.eval K (l.circ K) := by
  cases l with
  | H j => exact eval_place1_blk (by simp [L.lo, L.wd] at hl; omega) _
  | Z j => exact eval_place1_blk (by simp [L.lo, L.wd] at hl; omega) _
  | C j => exact eval_place2_blk (by simp [L.lo, L.wd] at hl; omega) _
  | K j => exact eval_place2_blk (by simp [L.lo, L.wd] at hl; omega) _
  | S j => exact eval_place2_blk (by simp [L.lo, L.wd] at hl; omega) _

theorem eval_letter_blk {m K : ℕ} (x : Lt) (hx : x.ok K = true) :
    opsQ.eval (m + K) (x.circ K (m + K)) =
      blk (m := m) (k := K) fun h =>
        if ∀ j, h j = 1 then opsQ.eval K (x.on K) else opsQ.eval K (x.off K) := by
  cases x with
  | s l =>
    simp only [Lt.ok, decide_eq_true_eq] at hx
    simp only [Lt.circ, Lt.on, Lt.off, ite_self]
    exact eval_L_blk l hx
  | g Kd tg cs b =>
    simp only [Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hx
    obtain ⟨⟨hnd, hlt⟩, ha⟩ := hx
    simp only [Lt.circ, Lt.on, Lt.off]
    rw [eval_mc_blk (ctl K cs b) hnd (fun j hj => by simpa using hlt j hj) ha]
    congr 1; funext h
    cases b
    · rw [if_pos ((topMatch_ctl cs false h).2 (by simp))]; simp
    · by_cases hh : ∀ j, h j = 1
      · rw [if_pos ((topMatch_ctl cs true h).2 (fun _ => hh)), if_pos hh]
      · rw [if_neg (fun H => hh ((topMatch_ctl cs true h).1 H rfl)), if_neg hh]; simp

/-- A word is block diagonal in the bulk. -/
theorem eval_wc_blk {m K : ℕ} : ∀ (l : List Lt), (∀ x ∈ l, x.ok K = true) →
    opsQ.eval (m + K) (wc K (m + K) l) =
      blk (m := m) (k := K) fun h =>
        if ∀ j, h j = 1 then opsQ.eval K (onW K l) else opsQ.eval K (offW K l)
  | [], _ => by
    simp only [wc, onW, offW, List.map_nil, drawn, List.reverse_nil, List.prod_nil, map_one,
      ite_self]
    rw [← onBottom_one (n := m), onBottom_eq_blk]
  | x :: l, hl => by
    rw [wc_cons, map_mul, eval_wc_blk l (fun y hy => hl y (by simp [hy])),
      eval_letter_blk x (hl x (by simp)), blk_mul]
    congr 1; funext h
    simp only [onW, offW, List.map_cons, drawn_cons, map_mul]
    split_ifs <;> rfl

/-- Two words have the same semantics at every width when they agree on the
two kinds of blocks. -/
theorem sem_wc {m K : ℕ} {l₁ l₂ : List Lt} (h₁ : ∀ x ∈ l₁, x.ok K = true)
    (h₂ : ∀ x ∈ l₂, x.ok K = true) (hon : Fast.check (onW K l₁) (onW K l₂) = true)
    (hoff : Fast.check (offW K l₁) (offW K l₂) = true) :
    S.sem (m + K) (wc K (m + K) l₁) = S.sem (m + K) (wc K (m + K) l₂) := by
  apply sem_of_eval
  rw [eval_wc_blk l₁ h₁, eval_wc_blk l₂ h₂, Fast.check_sound hon, Fast.check_sound hoff]


/-! ## Removing a local wire -/

/-- The wires once wire `q` is removed. -/
def dropW (q j : ℕ) : ℕ := if j < q then j else j - 1

namespace Lt

/-- The letter does not touch the local wire `q`. -/
def avoids (q : ℕ) : Lt → Bool
  | s l => decide (l.lo + l.wd ≤ q) || decide (q < l.lo)
  | g _ tg cs _ => !(tg.contains q) && !(cs.any fun p => p.1 == q)

/-- The letter with wire `q` removed. -/
def drop (q : ℕ) : Lt → Lt
  | s l => if q < l.lo then s l.down else s l
  | g Kd tg cs b => g Kd (tg.map (dropW q)) (cs.map fun p => (dropW q p.1, p.2)) b

end Lt

/-- The placement hypothesis: conjugating by `c m q` (with inverse `c' m q`)
carries a letter avoiding the local wire `q` to its version without that wire,
with an idle wire on top.  (In `Net`: the swaps of `topNet`.) -/
structure Frame (k : ℕ) where
  c : (m q : ℕ) → Circ (m + k + 1)
  c' : (m q : ℕ) → Circ (m + k + 1)
  inv : ∀ m q, Derivable (theory (m + k + 1)) (c' m q * c m q) 1
  inv' : ∀ m q, Derivable (theory (m + k + 1)) (c m q * c' m q) 1
  top : ∀ m q (x : Lt), q ≤ k → x.ok (k + 1) = true → x.avoids q = true →
    Derivable (theory (m + k + 1)) (c m q * x.circ (k + 1) (m + k + 1) * c' m q)
      (padTop ((x.drop q).circ k (m + k)))

section Window

variable {k : ℕ} (F : Frame k) (m : ℕ)

/-- A word avoiding wire `q`, carried to the top. -/
theorem Frame.word {q : ℕ} (hq : q ≤ k) : ∀ (l : List Lt),
    (∀ x ∈ l, x.ok (k + 1) = true ∧ x.avoids q = true) →
    Derivable (theory (m + k + 1)) (F.c m q * wc (k + 1) (m + k + 1) l * F.c' m q)
      (padTop (wc k (m + k) (l.map (Lt.drop q))))
  | [], _ => by
    simp only [wc, List.map_nil, drawn, List.reverse_nil, List.prod_nil, map_one, mul_one]
    exact F.inv' m q
  | x :: l, hl => by
    have h1 := Frame.word hq l (fun y hy => hl y (by simp [hy]))
    have h2 := F.top m q x hq (hl x (by simp)).1 (hl x (by simp)).2
    rw [wc_cons, List.map_cons, wc_cons, map_mul]
    have e3 : F.c m q * (wc (k + 1) (m + k + 1) l * x.circ (k + 1) (m + k + 1)) * F.c' m q =
        F.c m q * wc (k + 1) (m + k + 1) l * 1 * (x.circ (k + 1) (m + k + 1) * F.c' m q) := by
      simp only [mul_one, mul_assoc]
    have e4 : F.c m q * wc (k + 1) (m + k + 1) l * (F.c' m q * F.c m q) *
        (x.circ (k + 1) (m + k + 1) * F.c' m q) =
        (F.c m q * wc (k + 1) (m + k + 1) l * F.c' m q) *
          (F.c m q * x.circ (k + 1) (m + k + 1) * F.c' m q) := by simp only [mul_assoc]
    rw [e3]
    refine (dctx _ _ (F.inv m q).symm).trans ?_
    rw [e4]
    exact dmul h1 h2

include F in
/-- Lemma 5.1 on a window avoiding the local wire `q`. -/
theorem Frame.window (ih : IH (m + k + 1)) {q : ℕ} (hq : q ≤ k) {a b : List Lt}
    (ha : ∀ x ∈ a, x.ok (k + 1) = true ∧ x.avoids q = true)
    (hb : ∀ x ∈ b, x.ok (k + 1) = true ∧ x.avoids q = true)
    (hsem : S.sem (m + k) (wc k (m + k) (a.map (Lt.drop q))) =
      S.sem (m + k) (wc k (m + k) (b.map (Lt.drop q)))) :
    Derivable (theory (m + k + 1)) (wc (k + 1) (m + k + 1) a) (wc (k + 1) (m + k + 1) b) := by
  have hp := sem_step_top ih hsem
  have e : ∀ w : Circ (m + k + 1), Derivable (theory (m + k + 1)) w
      (F.c' m q * (F.c m q * w * F.c' m q) * F.c m q) := by
    intro w
    have h1 : F.c' m q * (F.c m q * w * F.c' m q) * F.c m q =
        (F.c' m q * F.c m q) * w * (F.c' m q * F.c m q) := by simp only [mul_assoc]
    rw [h1]
    have := dmul (dmul (F.inv m q) (Derivable.refl w)) (F.inv m q)
    simpa using this.symm
  exact (e _).trans ((dctx _ _ ((F.word m hq a ha).trans (hp.trans
    (F.word m hq b hb).symm))).trans (e _).symm)

end Window

/-! ## Steps and runs -/

/-- A table of equations between words. -/
abbrev Tbl := List (List Lt × List Lt)

/-- Every equation of the table holds on `m + K` wires. -/
def AllD (K m : ℕ) (T : Tbl) : Prop :=
  ∀ e ∈ T, Derivable (theory (m + K)) (wc K (m + K) e.1) (wc K (m + K) e.2)

/-- A step of a derivation. -/
inductive St
  /-- rewrite at position `i` with equation `e` of the table (backwards when `dir`) -/
  | rw (i e : ℕ) (dir : Bool)
  /-- exchange the small letters at positions `i`, `i + 1`, on disjoint wires -/
  | sw (i : ℕ)
  /-- Lemma 5.1: replace the `len` letters at `i` by `r`, all avoiding wire `q` -/
  | sem (i len : ℕ) (r : List Lt) (q : ℕ)
  deriving Repr

/-- Two windows avoiding wire `q` with the same semantics without it. -/
def semOK (k q : ℕ) (a b : List Lt) : Bool :=
  decide (q ≤ k) && (a ++ b).all (fun x => x.ok (k + 1) && x.avoids q) &&
    ((a ++ b).map (Lt.drop q)).all (Lt.ok k) &&
    Fast.check (onW k (a.map (Lt.drop q))) (onW k (b.map (Lt.drop q))) &&
    Fast.check (offW k (a.map (Lt.drop q))) (offW k (b.map (Lt.drop q)))

def orient (dir : Bool) (e : List Lt × List Lt) : List Lt × List Lt :=
  if dir then (e.2, e.1) else e

/-- Apply a step. -/
def applyStep (k : ℕ) (T : Tbl) (cur : List Lt) : St → Option (List Lt)
  | .rw i e dir =>
    match T[e]? with
    | none => none
    | some eq =>
      if (cur.drop i).take (orient dir eq).1.length == (orient dir eq).1 then
        some (cur.take i ++ (orient dir eq).2 ++ cur.drop (i + (orient dir eq).1.length))
      else none
  | .sw i =>
    match (cur.drop i).take 2 with
    | [.s x, .s y] => if disj x y then some (cur.take i ++ [.s y, .s x] ++ cur.drop (i + 2)) else none
    | _ => none
  | .sem i len r q =>
    if ((cur.drop i).take len).length == len && semOK k q ((cur.drop i).take len) r then
      some (cur.take i ++ r ++ cur.drop (i + len))
    else none

/-- Run a derivation. -/
def runSteps (k : ℕ) (T : Tbl) : List Lt → List St → Option (List Lt)
  | cur, [] => some cur
  | cur, s :: ss =>
    match applyStep k T cur s with
    | none => none
    | some nxt => runSteps k T nxt ss

/-- Run a derivation from `w` and compare with `v`. -/
def check (k : ℕ) (T : Tbl) (w v : List Lt) (ss : List St) : Bool :=
  match runSteps k T w ss with
  | none => false
  | some u => u == v

section Sound

variable {k : ℕ} (F : Frame k) {m : ℕ} (ih : IH (m + k + 1))

theorem replace (u a b v : List Lt)
    (h : Derivable (theory (m + k + 1)) (wc (k + 1) (m + k + 1) a) (wc (k + 1) (m + k + 1) b)) :
    Derivable (theory (m + k + 1)) (wc (k + 1) (m + k + 1) (u ++ a ++ v))
      (wc (k + 1) (m + k + 1) (u ++ b ++ v)) := by
  rw [wc_append, wc_append, wc_append, wc_append, ← mul_assoc, ← mul_assoc]
  exact dctx _ _ h

theorem split_at (cur : List Lt) (i len : ℕ) :
    cur = cur.take i ++ (cur.drop i).take len ++ cur.drop (i + len) := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

include F ih in
theorem semOK_sound {q : ℕ} {a b : List Lt} (h : semOK k q a b = true) :
    Derivable (theory (m + k + 1)) (wc (k + 1) (m + k + 1) a) (wc (k + 1) (m + k + 1) b) := by
  simp only [semOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hq, hab⟩, hok⟩, hon⟩, hoff⟩ := h
  have hab' : ∀ x ∈ a ++ b, x.ok (k + 1) = true ∧ x.avoids q = true := fun x hx => by
    simpa using hab x hx
  refine F.window m ih hq (fun x hx => hab' x (List.mem_append_left _ hx))
    (fun x hx => hab' x (List.mem_append_right _ hx)) ?_
  exact sem_wc (fun x hx => hok x (by rw [List.map_append]; exact List.mem_append_left _ hx))
    (fun x hx => hok x (by rw [List.map_append]; exact List.mem_append_right _ hx)) hon hoff

include F ih in
theorem applyStep_sound {T : Tbl} (hT : AllD (k + 1) m T) {cur nxt : List Lt} {s : St}
    (h : applyStep k T cur s = some nxt) :
    Derivable (theory (m + k + 1)) (wc (k + 1) (m + k + 1) cur) (wc (k + 1) (m + k + 1) nxt) := by
  cases s with
  | rw i e dir =>
    simp only [applyStep] at h
    split at h
    · exact absurd h (by simp)
    · rename_i eq he
      split_ifs at h with hm
      cases h
      have hmem : eq ∈ T := List.mem_of_getElem? he
      have he' : Derivable (theory (m + k + 1)) (wc (k + 1) (m + k + 1) (orient dir eq).1)
          (wc (k + 1) (m + k + 1) (orient dir eq).2) := by
        unfold orient; split_ifs
        · exact (hT eq hmem).symm
        · exact hT eq hmem
      rw [beq_iff_eq] at hm
      conv_lhs => rw [split_at cur i (orient dir eq).1.length, hm]
      exact replace _ _ _ _ he'
  | sw i =>
    simp only [applyStep] at h
    split at h
    · rename_i x y hxy
      split_ifs at h with hd
      cases h
      conv_lhs => rw [split_at cur i 2, hxy]
      refine replace _ _ _ _ ?_
      simp only [wc, List.map_cons, List.map_nil, Lt.circ, drawn, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
      exact comm_disj (m + k + 1) x y hd
    · exact absurd h (by simp)
  | sem i len r q =>
    simp only [applyStep] at h
    split_ifs at h with hm
    cases h
    rw [Bool.and_eq_true] at hm
    conv_lhs => rw [split_at cur i len]
    exact replace _ _ _ _ (semOK_sound F ih hm.2)

include F ih in
theorem runSteps_sound {T : Tbl} (hT : AllD (k + 1) m T) :
    ∀ {cur u : List Lt} {ss : List St}, runSteps k T cur ss = some u →
      Derivable (theory (m + k + 1)) (wc (k + 1) (m + k + 1) cur) (wc (k + 1) (m + k + 1) u) := by
  intro cur u ss h
  induction ss generalizing cur with
  | nil => simp only [runSteps, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | cons s ss ihs =>
    simp only [runSteps] at h
    split at h
    · exact absurd h (by simp)
    · rename_i nxt hn
      exact (applyStep_sound F ih hT hn).trans (ihs h)

include F ih in
/-- A run that passes `check` is a derivation on `m + k + 1` wires. -/
theorem check_sound {T : Tbl} (hT : AllD (k + 1) m T) {w v : List Lt} {ss : List St}
    (h : check k T w v ss = true) :
    Derivable (theory (m + k + 1)) (wc (k + 1) (m + k + 1) w) (wc (k + 1) (m + k + 1) v) := by
  unfold check at h
  split at h
  · exact absurd h (by simp)
  · rename_i u hu
    rw [beq_iff_eq] at h
    subst h
    exact runSteps_sound F ih hT hu

end Sound

end QCert.RealCliffordCH.Sec8.SE
