/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A fixed-width engine over gadget tokens (packages (ii), (iii))

The equations of Appendices D.3 and D.4 live on four and five wires, and
their gates are mostly multi-controlled gadgets (`MC.mc`) and two-wire gates
on wires that need not be adjacent.  Here a circuit on `N` wires is a word of
tokens (`Tk`), in drawn order:

* `s l`: a letter of `EngineN` (a gate on one wire or two adjacent wires);
* `g Kd tg cs`: the multi-controlled gate `mc N Kd tg c` with the controls
  `cs` (a list of wires and colours), simulated directly (`LSim`, through
  `SymEngine.gAct`);
* `p m w ps`: the `m`-wire letter word `w` placed on the wires `ps`
  (`MC.placeG`), e.g. `CZ` between wires `0` and `3`.

Steps rewrite with a table (`rw`), exchange two disjoint letters (`sw`), or
replace a window by Lemma 5.1 (`sem`): every token of both windows avoids a
wire `q` (any wire, the middle ones included), and the two windows with that
wire removed have the same semantics on `N - 1` wires, decided by simulating
the tokens.  The window is carried to a circuit idle on the top wire by the
swaps of `Net.topNet` (`Net.letter_toTop`, `Net.mc_toTop`,
`Net.placeG_toTop`), and `Net.semIdle` applies.

`check_sound`: a run that passes `check` (decided by `decide +kernel`) is a
derivation on `M + 1` wires, given completeness below (`IH (M + 1)`).
-/
import QCert.RealCliffordCH.Sec8.D.EngineFrame

namespace QCert.RealCliffordCH.Sec8.WE

open Matrix Circuit Eng Net Fast

/-! ## Tokens -/

/-- Tokens: small letters, multi-controlled gates, placed small circuits. -/
inductive Tk
  /-- a letter of `EngineN` -/
  | s (l : L)
  /-- `mc` of kind `Kd`, special wires `tg`, controls `cs` -/
  | g (Kd : Kind) (tg : List ℕ) (cs : List (ℕ × Bool))
  /-- the `m`-wire word `w` placed on the wires `ps` -/
  | p (m : ℕ) (w : List L) (ps : List ℕ)
  deriving DecidableEq, Repr

namespace Tk

/-- A token on `N` wires. -/
def circ (N : ℕ) : Tk → Circ N
  | s l => l.circ N
  | g Kd tg cs => mc N Kd tg (SE.ctl N cs false)
  | p m w ps => placeG N (circW m w) ps

/-- A token is well formed on `N` wires. -/
def ok (N : ℕ) : Tk → Bool
  | s l => decide (l.lo + l.wd ≤ N)
  | g Kd tg cs => (SE.Lt.g Kd tg cs false).ok N
  | p m w ps => decide ps.Nodup && ps.all (· < N) && (ps.length == m) &&
      w.all (fun x => decide (x.lo + x.wd ≤ m))

/-- The token does not touch wire `q`. -/
def avoids (q : ℕ) : Tk → Bool
  | s l => decide (l.lo + l.wd ≤ q) || decide (q < l.lo)
  | g Kd tg cs => (SE.Lt.g Kd tg cs false).avoids q
  | p _ _ ps => !(ps.contains q)

/-- The token with wire `q` removed. -/
def drop (q : ℕ) : Tk → Tk
  | s l => if q < l.lo then s l.down else s l
  | g Kd tg cs => g Kd (tg.map (SE.dropW q)) (cs.map fun p => (SE.dropW q p.1, p.2))
  | p m w ps => p m w (ps.map (SE.dropW q))

end Tk

/-- A word of tokens, in drawn order. -/
def wcT (N : ℕ) (l : List Tk) : Circ N := drawn (l.map (Tk.circ N))

theorem wcT_cons (N : ℕ) (x : Tk) (l : List Tk) : wcT N (x :: l) = wcT N l * x.circ N := by
  simp [wcT, SE.drawn_cons]

theorem wcT_append (N : ℕ) (a b : List Tk) : wcT N (a ++ b) = wcT N b * wcT N a := by
  simp [wcT, SE.drawn_append]

/-- A word of letters is a word of `s` tokens. -/
theorem circW_eq_wcT (N : ℕ) (l : List L) : circW N l = wcT N (l.map Tk.s) := by
  simp only [circW, wcT, List.map_map]; rfl

/-! ## Simulation -/

section Sim

open LS Sim

/-- The action of a token on `K` wires (scaled by a power of `√2`). -/
def Tk.act (K : ℕ) : Tk → V K → V K
  | .s l, v => actW (l.circ K) v
  | .g Kd tg cs, v => SE.gAct K Kd tg cs v
  | .p m w ps, v => actW (placeG K (circW m w) ps) v

def Tk.inc (K : ℕ) : Tk → ℕ
  | .s l => incW (l.circ K)
  | .g Kd _ _ => SE.gInc Kd
  | .p m w ps => incW (placeG K (circW m w) ps)

local notation "√2" => (Quadratic.X : QSqrt2)

theorem tf_act {K : ℕ} (x : Tk) (hx : x.ok K = true) (v : V K) :
    toFun (toS (x.act K v)) = √2 ^ x.inc K • (opsQ.eval K (x.circ K) *ᵥ toFun (toS v)) := by
  cases x with
  | s l => exact tf_actW _ _
  | g Kd tg cs => exact SE.tf_gAct Kd tg cs false hx v
  | p m w ps => exact tf_actW _ _

/-- A word simulated on `K` wires, the first token first. -/
def simT (K : ℕ) : List Tk → V K → V K
  | [], v => v
  | x :: l, v => simT K l (x.act K v)

def incT (K : ℕ) (l : List Tk) : ℕ := (l.map (Tk.inc K)).sum

theorem tf_simT {K : ℕ} : ∀ (l : List Tk), (∀ x ∈ l, x.ok K = true) → ∀ (v : V K),
    toFun (toS (simT K l v)) = √2 ^ incT K l • (opsQ.eval K (wcT K l) *ᵥ toFun (toS v))
  | [], _, v => by
    simp only [simT, incT, wcT, drawn, List.map_nil, List.sum_nil, pow_zero, one_smul,
      List.reverse_nil, List.prod_nil, map_one, one_mulVec]
  | x :: l, hl, v => by
    rw [simT, tf_simT l (fun y hy => hl y (by simp [hy])), tf_act x (hl x (by simp)),
      mulVec_smul, smul_smul, ← pow_add]
    have e1 : incT K (x :: l) = incT K l + x.inc K := by simp [incT, Nat.add_comm]
    rw [e1, wcT_cons, map_mul, mulVec_mulVec]

/-- Two words act alike on `K` wires. -/
def tcheck (K : ℕ) (l₁ l₂ : List Tk) : Bool :=
  let k1 := incT K l₁
  let k2 := incT K l₂
  (Sim.allStates K).all fun t =>
    vbeq (vscale (k2 - k1) (simT K l₁ (basisV t))) (vscale (k1 - k2) (simT K l₂ (basisV t)))

theorem tcheck_sound {K : ℕ} {l₁ l₂ : List Tk} (h₁ : ∀ x ∈ l₁, x.ok K = true)
    (h₂ : ∀ x ∈ l₂, x.ok K = true) (h : tcheck K l₁ l₂ = true) :
    S.sem K (wcT K l₁) = S.sem K (wcT K l₂) := by
  apply sem_of_eval
  funext s t
  rw [tcheck, List.all_eq_true] at h
  have ht := vbeq_eq (h t (Sim.mem_allStates t))
  have hf : toFun (toS (vscale (incT K l₂ - incT K l₁) (simT K l₁ (basisV t)))) =
      toFun (toS (vscale (incT K l₁ - incT K l₂) (simT K l₂ (basisV t)))) := by rw [ht]
  rw [tf_scale, tf_scale, tf_simT l₁ h₁, tf_simT l₂ h₂, toS_basis, Sim.toFun_basis,
    smul_smul, smul_smul, ← pow_add, ← pow_add] at hf
  have e : incT K l₂ - incT K l₁ + incT K l₁ = incT K l₁ - incT K l₂ + incT K l₂ := by omega
  rw [e] at hf
  have hc := congrFun (pow_cancel hf) s
  simpa only [mulVec_single_one, transpose_apply] using hc

end Sim

/-! ## Windows avoiding a wire, carried to the top -/

section Top

variable {M : ℕ}

theorem tk_toTop {q : ℕ} (hq : q ≤ M) (x : Tk) (hx : x.ok (M + 1) = true)
    (hav : x.avoids q = true) : ToTop M q (x.circ (M + 1)) ((x.drop q).circ M) := by
  cases x with
  | s l =>
    simp only [Tk.ok, decide_eq_true_eq] at hx
    simp only [Tk.avoids, Bool.or_eq_true, decide_eq_true_eq] at hav
    have hq' : q < l.lo ∨ l.lo + l.wd ≤ q := hav.symm
    have h := ToTop.letter hq l hx hq'
    have e : (Tk.drop q (Tk.s l)).circ M = (dropL q l).circ M := by
      simp only [Tk.drop]
      rw [← SE.dropL_eq q l hq']; split_ifs <;> rfl
    rw [e]; exact h
  | g Kd tg cs =>
    simp only [Tk.ok, SE.Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      beq_iff_eq] at hx
    obtain ⟨⟨hnd, hlt⟩, ha⟩ := hx
    simp only [Tk.avoids, SE.Lt.avoids, Bool.and_eq_true, Bool.not_eq_true'] at hav
    have hqt : q ∉ tg := by
      intro hm
      have : tg.contains q = true := by simpa using hm
      rw [this] at hav; exact Bool.noConfusion hav.1
    have hcs : ∀ p ∈ cs, p.1 ≠ q := by
      intro p hp e
      have : cs.any (fun p => p.1 == q) = true := List.any_eq_true.2 ⟨p, hp, by simp [e]⟩
      rw [this] at hav; exact Bool.noConfusion hav.2
    have hcq : SE.ctl (M + 1) cs false q = none := by
      simp only [SE.ctl, if_pos (show q < M + 1 by omega)]
      exact List.lookup_eq_none_iff.2 (fun p hp => by simpa using (hcs p hp).symm)
    have h := ToTop.mc hq Kd tg (SE.ctl (M + 1) cs false) (by rw [← SE.kindSp_eq]; exact ha) hnd
      (fun t ht => by have := hlt t ht; simp at this; omega) hqt hcq
    have e : (Tk.drop q (Tk.g Kd tg cs)).circ M =
        mc M Kd (tg.map (SE.dropW q)) (SE.ctl M (cs.map fun p => (SE.dropW q p.1, p.2)) false) :=
      rfl
    rw [e, SE.dropW_eq]
    have hmc : mc M Kd (tg.map (Net.dropW q)) (SE.ctl (M + 1) cs false ∘ liftW q) =
        mc M Kd (tg.map (Net.dropW q)) (SE.ctl M (cs.map fun p => (Net.dropW q p.1, p.2)) false) := by
      refine mc_congr M Kd _ (fun i hi => ?_)
      simp only [Function.comp_apply, SE.ctl]
      by_cases hik : i < M
      · rw [if_pos hik, SE.lookup_drop q cs hcs i,
          if_pos (show liftW q i < M + 1 by simp only [liftW]; split_ifs <;> omega)]
      · rw [if_neg hik, if_neg (show ¬ liftW q i < M + 1 by simp only [liftW]; split_ifs <;> omega)]
    rw [hmc] at h
    exact h
  | p m w ps =>
    simp only [Tk.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hx
    obtain ⟨⟨⟨hnd, hlt⟩, hm⟩, -⟩ := hx
    simp only [Tk.avoids, Bool.not_eq_true'] at hav
    have hqp : q ∉ ps := by
      intro hm'
      have : ps.contains q = true := by simpa using hm'
      rw [this] at hav; exact Bool.noConfusion hav
    have h := placeG_toTop (circW m w) hnd (fun t ht => by have := hlt t ht; simp at this; omega)
      hm q hq hqp
    unfold ToTop
    rw [← SE.dropW_eq] at h
    exact h

/-- A word avoiding wire `q`, carried to the top. -/
theorem word_toTop {q : ℕ} (hq : q ≤ M) : ∀ (l : List Tk),
    (∀ x ∈ l, x.ok (M + 1) = true ∧ x.avoids q = true) →
    ToTop M q (wcT (M + 1) l) (wcT M (l.map (Tk.drop q)))
  | [], _ => by simpa [wcT, drawn] using ToTop.one M q
  | x :: l, hl => by
    rw [wcT_cons, List.map_cons, wcT_cons]
    exact (word_toTop hq l (fun y hy => hl y (by simp [hy]))).mul
      (tk_toTop hq x (hl x (by simp)).1 (hl x (by simp)).2)

end Top

/-! ## Steps and runs -/

/-- A table of equations between words. -/
abbrev Tbl := List (List Tk × List Tk)

/-- Every equation of the table holds on `N` wires. -/
def AllD (N : ℕ) (T : Tbl) : Prop :=
  ∀ e ∈ T, Derivable (theory N) (wcT N e.1) (wcT N e.2)

theorem AllD.nil (N : ℕ) : AllD N [] := fun _ h => by simp at h

theorem AllD.cons {N : ℕ} {a b : List Tk} {T : Tbl}
    (h : Derivable (theory N) (wcT N a) (wcT N b)) (hT : AllD N T) : AllD N ((a, b) :: T) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact h
  · exact hT e he

/-- A step of a derivation. -/
inductive St
  /-- rewrite at position `i` with equation `e` of the table (backwards when `dir`) -/
  | rw (i e : ℕ) (dir : Bool)
  /-- exchange the small letters at positions `i`, `i + 1`, on disjoint wires -/
  | sw (i : ℕ)
  /-- Lemma 5.1: replace the `len` tokens at `i` by `r`, all avoiding wire `q` -/
  | sem (i len : ℕ) (r : List Tk) (q : ℕ)
  /-- the token `a` conjugated by the swap of wires `j, j + 1` is `b`: replace
  `[S j, a, S j]` at `i` by `[b]` (or back, when `dir`) -/
  | swp (i j : ℕ) (a b : Tk) (dir : Bool)
  deriving Repr

/-- Two windows avoiding wire `q` of `M + 1` wires, with the same semantics
without it. -/
def semOK (M q : ℕ) (a b : List Tk) : Bool :=
  decide (q ≤ M) && (a ++ b).all (fun x => x.ok (M + 1) && x.avoids q) &&
    ((a ++ b).map (Tk.drop q)).all (Tk.ok M) &&
    tcheck M (a.map (Tk.drop q)) (b.map (Tk.drop q))

def orient (dir : Bool) (e : List Tk × List Tk) : List Tk × List Tk :=
  if dir then (e.2, e.1) else e

/-- `a` conjugated by the swap of wires `j, j + 1` of `N` wires is `b`
(`Net.placeG_swap`, `Net.mc_swap`). -/
def swpOK (N j : ℕ) : Tk → Tk → Bool
  | .p m w ps, .p m' w' ps' =>
    decide (j + 2 ≤ N) && (m == m') && (w == w') && (ps' == ps.map (Net.tau j)) &&
      decide ps.Nodup && ps.all (· < N) && (ps.length == m)
  | .g Kd tg cs, .g Kd' tg' cs' =>
    decide (j + 2 ≤ N) && (Kd == Kd') && (tg' == tg.map (Net.tau j)) &&
      (SE.Lt.g Kd tg cs false).ok N &&
      (List.range N).all (fun i => SE.ctl N cs' false i == SE.ctl N cs false (Net.tau j i)) &&
      !(decide (j ∈ ctrlWires N tg (SE.ctl N cs false)) &&
        decide (j + 1 ∈ ctrlWires N tg (SE.ctl N cs false)))
  | _, _ => false

/-- Apply a step. -/
def applyStep (M : ℕ) (T : Tbl) (cur : List Tk) : St → Option (List Tk)
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
    if ((cur.drop i).take len).length == len && semOK M q ((cur.drop i).take len) r then
      some (cur.take i ++ r ++ cur.drop (i + len))
    else none
  | .swp i j a b dir =>
    if swpOK (M + 1) j a b then
      if dir then
        if (cur.drop i).take 1 == [b] then some (cur.take i ++ [.s (.S j), a, .s (.S j)] ++ cur.drop (i + 1))
        else none
      else
        if (cur.drop i).take 3 == [.s (.S j), a, .s (.S j)] then some (cur.take i ++ [b] ++ cur.drop (i + 3))
        else none
    else none

/-- Run a derivation. -/
def runSteps (M : ℕ) (T : Tbl) : List Tk → List St → Option (List Tk)
  | cur, [] => some cur
  | cur, s :: ss =>
    match applyStep M T cur s with
    | none => none
    | some nxt => runSteps M T nxt ss

/-- Run a derivation from `w` and compare with `v`. -/
def check (M : ℕ) (T : Tbl) (w v : List Tk) (ss : List St) : Bool :=
  match runSteps M T w ss with
  | none => false
  | some u => u == v

section Sound

variable {M : ℕ} (ih : IH (M + 1))

theorem replace (u a b v : List Tk)
    (h : Derivable (theory (M + 1)) (wcT (M + 1) a) (wcT (M + 1) b)) :
    Derivable (theory (M + 1)) (wcT (M + 1) (u ++ a ++ v)) (wcT (M + 1) (u ++ b ++ v)) := by
  rw [wcT_append, wcT_append, wcT_append, wcT_append, ← mul_assoc, ← mul_assoc]
  exact dctx _ _ h

theorem split_at (cur : List Tk) (i len : ℕ) :
    cur = cur.take i ++ (cur.drop i).take len ++ cur.drop (i + len) := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

include ih in
theorem semOK_sound {q : ℕ} {a b : List Tk} (h : semOK M q a b = true) :
    Derivable (theory (M + 1)) (wcT (M + 1) a) (wcT (M + 1) b) := by
  simp only [semOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hq, hab⟩, hok⟩, hc⟩ := h
  have hab' : ∀ x ∈ a ++ b, x.ok (M + 1) = true ∧ x.avoids q = true := fun x hx => by
    simpa using hab x hx
  have hA := word_toTop hq a (fun x hx => hab' x (List.mem_append_left _ hx))
  have hB := word_toTop hq b (fun x hx => hab' x (List.mem_append_right _ hx))
  refine semIdle ih hA hB ?_
  exact tcheck_sound (fun x hx => hok x (by rw [List.map_append]; exact List.mem_append_left _ hx))
    (fun x hx => hok x (by rw [List.map_append]; exact List.mem_append_right _ hx)) hc

theorem swpOK_sound {N j : ℕ} {a b : Tk} (h : swpOK N j a b = true) :
    Derivable (theory N) (wcT N [.s (.S j), a, .s (.S j)]) (wcT N [b]) := by
  have ew : ∀ x : Tk, wcT N [.s (.S j), x, .s (.S j)] = drawn [swAt N j, x.circ N, swAt N j] := by
    intro x; rfl
  have e1 : wcT N [b] = b.circ N := by simp [wcT, drawn]
  rw [ew, e1]
  match a, b, h with
  | .p m w ps, .p m' w' ps', h =>
    simp only [swpOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hj, rfl⟩, rfl⟩, rfl⟩, hnd⟩, hlt⟩, hm⟩ := h
    exact placeG_swap (circW m w) hnd (fun p hp => by simpa using hlt p hp) hm j hj
  | .g Kd tg cs, .g Kd' tg' cs', h =>
    simp only [swpOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨⟨⟨hj, rfl⟩, rfl⟩, hok⟩, hc⟩, hnc⟩ := h
    simp only [SE.Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hnd, hlt⟩, ha⟩ := hok
    have h1 := mc_swap N j hj Kd tg (SE.ctl N cs false) (by rw [← SE.kindSp_eq]; exact ha) hnd
      (fun t ht => by simpa using hlt t ht) (fun ⟨h1, h2⟩ => by rcases hnc with h | h <;> contradiction)
    refine h1.trans (der_of_eq ?_)
    refine mc_congr N _ _ (fun i hi => ?_)
    have := hc i (List.mem_range.2 hi)
    simp only [beq_iff_eq] at this
    simp only [Function.comp_apply]
    exact this.symm
  | .s _, _, h => simp [swpOK] at h
  | .p .., .s _, h => simp [swpOK] at h
  | .p .., .g .., h => simp [swpOK] at h
  | .g .., .s _, h => simp [swpOK] at h
  | .g .., .p .., h => simp [swpOK] at h

include ih in
theorem applyStep_sound {T : Tbl} (hT : AllD (M + 1) T) {cur nxt : List Tk} {s : St}
    (h : applyStep M T cur s = some nxt) :
    Derivable (theory (M + 1)) (wcT (M + 1) cur) (wcT (M + 1) nxt) := by
  cases s with
  | rw i e dir =>
    simp only [applyStep] at h
    split at h
    · exact absurd h (by simp)
    · rename_i eq he
      split_ifs at h with hm
      cases h
      have hmem : eq ∈ T := List.mem_of_getElem? he
      have he' : Derivable (theory (M + 1)) (wcT (M + 1) (orient dir eq).1)
          (wcT (M + 1) (orient dir eq).2) := by
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
      simp only [wcT, List.map_cons, List.map_nil, Tk.circ, drawn, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
      exact comm_disj (M + 1) x y hd
    · exact absurd h (by simp)
  | sem i len r q =>
    simp only [applyStep] at h
    split_ifs at h with hm
    cases h
    rw [Bool.and_eq_true] at hm
    conv_lhs => rw [split_at cur i len]
    exact replace _ _ _ _ (semOK_sound ih hm.2)
  | swp i j a b dir =>
    simp only [applyStep] at h
    split_ifs at h with hs hd hm hm
    · cases h
      rw [beq_iff_eq] at hm
      conv_lhs => rw [split_at cur i 1, hm]
      exact replace _ _ _ _ (swpOK_sound hs).symm
    · cases h
      rw [beq_iff_eq] at hm
      conv_lhs => rw [split_at cur i 3, hm]
      exact replace _ _ _ _ (swpOK_sound hs)

include ih in
theorem runSteps_sound {T : Tbl} (hT : AllD (M + 1) T) :
    ∀ {cur u : List Tk} {ss : List St}, runSteps M T cur ss = some u →
      Derivable (theory (M + 1)) (wcT (M + 1) cur) (wcT (M + 1) u) := by
  intro cur u ss h
  induction ss generalizing cur with
  | nil => simp only [runSteps, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | cons s ss ihs =>
    simp only [runSteps] at h
    split at h
    · exact absurd h (by simp)
    · rename_i nxt hn
      exact (applyStep_sound ih hT hn).trans (ihs h)

include ih in
/-- A run that passes `check` is a derivation on `M + 1` wires. -/
theorem check_sound {T : Tbl} (hT : AllD (M + 1) T) {w v : List Tk} {ss : List St}
    (h : check M T w v ss = true) :
    Derivable (theory (M + 1)) (wcT (M + 1) w) (wcT (M + 1) v) := by
  unfold check at h
  split at h
  · exact absurd h (by simp)
  · rename_i u hu
    rw [beq_iff_eq] at h
    subst h
    exact runSteps_sound ih hT hu

end Sound

end QCert.RealCliffordCH.Sec8.WE
