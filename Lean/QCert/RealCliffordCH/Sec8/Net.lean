/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: swap networks

The paper works in a PROP, where a gate on wires that are not the bottom
ones is defined by conjugation with swaps, the network being irrelevant up
to the topological rules (Definition 2.4, Section 2.2).  Our circuits form
a PRO and the swap is the circuit of Equation (8); `placeG` fixes one
network (`netL`).  This file shows that the choice does not matter, at
every width.

* The Coxeter relations for the swaps `swAt N j` (`sw_inv`, `sw_far`,
  `sw_braid`): the involution is (g), the far commutation is structural,
  the braid relation follows from (f2), (f3) on three wires.
* Local derivations moved anywhere (`lift_word`): a derivation between
  words of letters (`Eng.L`) on `K` wires holds on any `K` consecutive wires
  of a wider circuit.

Derivations here use no semantic step, so nothing here needs completeness
on fewer wires.
-/
import QCert.RealCliffordCH.Sec8.EngineN
import QCert.RealCliffordCH.Sec8.MC

namespace QCert.RealCliffordCH.Sec8.Net

open Circuit Eng

/-! ## Runs of the engine without semantic steps -/

/-- A step that is not a semantic step. -/
def Step.pure : Step → Bool
  | .sem .. => false
  | _ => true

theorem applyStep_pure {N : ℕ} {T : Tbl} (hT : AllD (N + 1) T) {cur nxt : List L} {s : Step}
    (hs : Step.pure s = true) (h : applyStep N T cur s = some nxt) :
    Derivable (theory (N + 1)) (circW (N + 1) cur) (circW (N + 1) nxt) := by
  cases s with
  | rw i k dir =>
    simp only [applyStep] at h
    split at h
    · exact absurd h (by simp)
    · rename_i e he
      split_ifs at h with hm
      cases h
      have hmem : e ∈ T := List.mem_of_getElem? he
      have he' : Derivable (theory (N + 1)) (circW (N + 1) (orient dir e).1)
          (circW (N + 1) (orient dir e).2) := by
        unfold orient; split_ifs
        · exact (hT e hmem).symm
        · exact hT e hmem
      rw [beq_iff_eq] at hm
      conv_lhs => rw [split_at cur i (orient dir e).1.length, hm]
      exact replace _ _ _ _ he'
  | sw i =>
    simp only [applyStep] at h
    split at h
    · rename_i x y hxy
      split_ifs at h with hd
      cases h
      conv_lhs => rw [split_at cur i 2, hxy]
      refine replace _ _ _ _ ?_
      rw [circW_cons, circW_cons, circW_cons, circW_cons, circW_nil, one_mul, one_mul]
      exact comm_disj (N + 1) x y hd
    · exact absurd h (by simp)
  | sem i len r => exact absurd hs (by simp [Step.pure])

theorem runSteps_pure {N : ℕ} {T : Tbl} (hT : AllD (N + 1) T) :
    ∀ {cur u : List L} {ss : List Step}, ss.all Step.pure = true → runSteps N T cur ss = some u →
      Derivable (theory (N + 1)) (circW (N + 1) cur) (circW (N + 1) u) := by
  intro cur u ss hp h
  induction ss generalizing cur with
  | nil => simp only [runSteps, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | cons s ss ihs =>
    simp only [List.all_cons, Bool.and_eq_true] at hp
    simp only [runSteps] at h
    split at h
    · exact absurd h (by simp)
    · rename_i nxt hn
      exact (applyStep_pure hT hp.1 hn).trans (ihs hp.2 h)

/-- A run without semantic steps that passes `check` is a derivation; it
needs no completeness hypothesis. -/
theorem check_pure {N : ℕ} {T : Tbl} (hT : AllD (N + 1) T) {w v : List L} {ss : List Step}
    (hp : ss.all Step.pure = true) (h : check N T w v ss = true) :
    Derivable (theory (N + 1)) (circW (N + 1) w) (circW (N + 1) v) := by
  unfold check at h
  split at h
  · exact absurd h (by simp)
  · rename_i u hu
    rw [beq_iff_eq] at h
    subst h
    exact runSteps_pure hT hp hu

/-! ## Moving local derivations -/

/-- The letter one wire up. -/
def upL : L → L
  | .H j => .H (j + 1) | .Z j => .Z (j + 1) | .C j => .C (j + 1) | .K j => .K (j + 1)
  | .S j => .S (j + 1)

@[simp] theorem upL_lo (x : L) : (upL x).lo = x.lo + 1 := by cases x <;> rfl
@[simp] theorem upL_wd (x : L) : (upL x).wd = x.wd := by cases x <;> rfl
@[simp] theorem down_upL (x : L) : (upL x).down = x := by cases x <;> rfl

/-- The letter `j` wires up. -/
def upLBy : ℕ → L → L
  | 0, x => x
  | j + 1, x => upL (upLBy j x)

@[simp] theorem upLBy_lo (j : ℕ) (x : L) : (upLBy j x).lo = x.lo + j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, upL_lo, ih]; omega

@[simp] theorem upLBy_wd (j : ℕ) (x : L) : (upLBy j x).wd = x.wd := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, upL_wd, ih]

theorem circW_up (N : ℕ) (l : List L) : circW (N + 1) (l.map upL) = shift (circW N l) := by
  rw [circW_shift N _ (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; simp), List.map_map]
  congr 2
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left (fun x _ => down_upL x)

/-- A derivation between words that fit on `K` wires holds on every wider
circuit, on the bottom wires. -/
theorem lift_top {K : ℕ} {a b : List L} (hab : ∀ x ∈ a ++ b, x.lo + x.wd ≤ K)
    (d : Derivable (theory K) (circW K a) (circW K b)) :
    ∀ N, K ≤ N → Derivable (theory N) (circW N a) (circW N b) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact d
  | succ N hKN ih =>
    rw [circW_top N a (fun x hx => le_trans (hab x (List.mem_append_left _ hx)) hKN),
      circW_top N b (fun x hx => le_trans (hab x (List.mem_append_right _ hx)) hKN)]
    exact derivable_padTop ih

/-- A derivation between words that fit on `K` wires holds on any `K`
consecutive wires `j, …, j + K - 1` of a wider circuit. -/
theorem lift_word {K : ℕ} {a b : List L} (hab : ∀ x ∈ a ++ b, x.lo + x.wd ≤ K)
    (d : Derivable (theory K) (circW K a) (circW K b)) :
    ∀ j N, j + K ≤ N →
      Derivable (theory N) (circW N (a.map (upLBy j))) (circW N (b.map (upLBy j))) := by
  intro j
  induction j with
  | zero =>
    intro N hN
    have e0 : ∀ l : List L, l.map (upLBy 0) = l := fun l => by
      induction l with
      | nil => rfl
      | cons x l ih => simp only [List.map_cons, ih]; rfl
    rw [e0, e0]
    exact lift_top hab d N (by omega)
  | succ j ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have e : ∀ l : List L, l.map (upLBy (j + 1)) = (l.map (upLBy j)).map upL := by
      intro l; rw [List.map_map]; exact List.map_congr_left (fun x _ => rfl)
    rw [e, e, circW_up, circW_up]
    exact derivable_shift (ih M (by omega))

/-! ## The Coxeter relations of the swaps -/

/-- The swap of wires `j`, `j + 1`, as a letter. -/
theorem swAt_eq (N j : ℕ) : swAt N j = (L.S j).circ N := rfl

theorem upBy_S (j i : ℕ) : upLBy j (L.S i) = L.S (i + j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, ih, upL]; rfl

/-- (g) on two wires, in letters. -/
theorem inv2 : Derivable (theory 2) (circW 2 [L.S 0, L.S 0]) (circW 2 []) := by
  have h := derivable_rule Rule.g 0
  simpa [circW, drawn, map_mul, L.circ, place2] using h

/-- The swap is an involution. -/
theorem sw_inv (N j : ℕ) (hj : j + 2 ≤ N) :
    Derivable (theory N) (drawn [swAt N j, swAt N j]) 1 := by
  have h := lift_word (K := 2) (by decide) inv2 j N hj
  simpa [upBy_S, circW, swAt_eq] using h

/-- Swaps on disjoint pairs of wires commute. -/
theorem sw_far (N i j : ℕ) (h : i + 2 ≤ j) :
    Derivable (theory N) (drawn [swAt N i, swAt N j]) (drawn [swAt N j, swAt N i]) := by
  have := comm_disj N (L.S i) (L.S j) (by simp [disj, below, L.lo, L.wd]; omega)
  simpa [drawn, swAt_eq] using this

/-- The table for the braid relation on three wires: the definition (8) of
the swap on wires 0, 1 and 1, 2, (f2) on wires 0, 1 and 1, 2, and (f3). -/
def braidT : Tbl :=
  [([.S 0], [.C 0, .H 1, .H 0, .C 0, .H 1, .H 0, .C 0, .H 1, .H 0]),
   ([.S 1], [.C 1, .H 2, .H 1, .C 1, .H 2, .H 1, .C 1, .H 2, .H 1]),
   ([.H 1, .S 0], [.S 0, .H 0]),
   ([.H 2, .S 1], [.S 1, .H 1]),
   ([.C 1, .S 0, .S 1], [.S 0, .S 1, .C 0])]

theorem braidT_ok : AllD 3 braidT := by
  intro e he
  simp only [braidT, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Derivable.refl _
  · exact Derivable.refl _
  · have h := derivable_rule Rule.f2 1
    simpa [circW, drawn, map_mul, L.circ, place2, place1] using h
  · have h := derivable_shift (derivable_rule Rule.f2 0)
    simpa [circW, drawn, map_mul, L.circ, place2, place1] using h
  · have h := derivable_rule Rule.f3 0
    simpa [circW, drawn, map_mul, L.circ, place2, place1] using h

/-- The braid relation on three wires. -/
theorem braid3 : Derivable (theory 3) (circW 3 [.S 1, .S 0, .S 1]) (circW 3 [.S 0, .S 1, .S 0]) :=
  check_pure (N := 2) braidT_ok (ss := [.rw 0 1 false,
      .rw 8 2 false, .sw 9, .sw 7, .rw 8 3 false, .rw 6 4 false,
      .rw 5 2 false, .sw 6, .sw 4, .rw 5 3 false, .rw 3 4 false,
      .rw 2 2 false, .sw 3, .sw 1, .rw 2 3 false, .rw 0 4 false,
      .rw 2 0 true]) (by decide) (by decide)

/-- The braid relation. -/
theorem sw_braid (N j : ℕ) (hj : j + 3 ≤ N) :
    Derivable (theory N) (drawn [swAt N (j + 1), swAt N j, swAt N (j + 1)])
      (drawn [swAt N j, swAt N (j + 1), swAt N j]) := by
  have h := lift_word (K := 3) (by decide) braid3 j N hj
  simpa [upBy_S, circW, swAt_eq, Nat.add_comm] using h

/-! ## Swap words up to the Coxeter relations -/

/-- A word of swaps `swAt N j`, in drawn order. -/
def swW (N : ℕ) (l : List ℕ) : Circ N := circW N (l.map L.S)

theorem swW_nil (N : ℕ) : swW N [] = 1 := rfl

theorem swW_append (N : ℕ) (a b : List ℕ) : swW N (a ++ b) = swW N b * swW N a := by
  simp only [swW, List.map_append, circW_append]

theorem swW_cons (N j : ℕ) (l : List ℕ) : swW N (j :: l) = swW N l * swAt N j := by
  rw [show j :: l = [j] ++ l from rfl, swW_append]
  simp [swW, circW, drawn, swAt_eq]

/-- The transposition of `j` and `j + 1`. -/
def tau (j q : ℕ) : ℕ := if q = j then j + 1 else if q = j + 1 then j else q

theorem tau_tau (j q : ℕ) : tau j (tau j q) = q := by
  unfold tau; split_ifs <;> omega

theorem tau_of_lt {j q : ℕ} (h : q < j) : tau j q = q := by
  unfold tau; split_ifs <;> omega

theorem tau_of_gt {j q : ℕ} (h : j + 1 < q) : tau j q = q := by
  unfold tau; split_ifs <;> omega

/-- Where the wire at position `q` is after the swaps `l` (drawn order). -/
def pos (l : List ℕ) (q : ℕ) : ℕ := l.foldl (fun q j => tau j q) q

@[simp] theorem pos_nil (q : ℕ) : pos [] q = q := rfl
@[simp] theorem pos_cons (j : ℕ) (l : List ℕ) (q : ℕ) : pos (j :: l) q = pos l (tau j q) := rfl
theorem pos_append (a b : List ℕ) (q : ℕ) : pos (a ++ b) q = pos b (pos a q) := by
  simp [pos, List.foldl_append]

theorem pos_reverse : ∀ (l : List ℕ) (q : ℕ), pos l.reverse (pos l q) = q
  | [], _ => rfl
  | j :: l, q => by
    simp only [List.reverse_cons, pos_append, pos_cons, pos_nil, pos_reverse l, tau_tau]

theorem pos_reverse' (l : List ℕ) (q : ℕ) : pos l (pos l.reverse q) = q := by
  have := pos_reverse l.reverse q
  rwa [List.reverse_reverse] at this

theorem pos_injective (l : List ℕ) : Function.Injective (pos l) := fun a b h => by
  rw [← pos_reverse l a, ← pos_reverse l b, h]

/-- `pos l` fixes a position below every index of `l`. -/
theorem pos_below : ∀ (l : List ℕ) (q : ℕ), (∀ x ∈ l, q < x) → pos l q = q
  | [], _, _ => rfl
  | j :: l, q, h => by
    rw [pos_cons, tau_of_lt (h j (by simp)), pos_below l q (fun x hx => h x (by simp [hx]))]

/-- The indices of a word are valid on `N` wires. -/
def Ok (N : ℕ) (l : List ℕ) : Prop := ∀ j ∈ l, j + 2 ≤ N

/-- Equality of swap words modulo the Coxeter relations. -/
inductive SwEq (N : ℕ) : List ℕ → List ℕ → Prop
  | refl (l : List ℕ) : SwEq N l l
  | symm {a b : List ℕ} : SwEq N a b → SwEq N b a
  | trans {a b c : List ℕ} : SwEq N a b → SwEq N b c → SwEq N a c
  | cong (u v : List ℕ) {a b : List ℕ} : SwEq N a b → SwEq N (u ++ a ++ v) (u ++ b ++ v)
  | inv (j : ℕ) : j + 2 ≤ N → SwEq N [j, j] []
  | far (i j : ℕ) : i + 2 ≤ j → SwEq N [i, j] [j, i]
  | braid (j : ℕ) : j + 3 ≤ N → SwEq N [j + 1, j, j + 1] [j, j + 1, j]

namespace SwEq

variable {N : ℕ}

theorem der {a b : List ℕ} (h : SwEq N a b) : Derivable (theory N) (swW N a) (swW N b) := by
  induction h with
  | refl l => exact Derivable.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | cong u v _ ih =>
    rw [swW_append, swW_append, swW_append, swW_append]
    simpa only [mul_assoc] using dctx (swW N v) (swW N u) ih
  | inv j hj => simpa [swW, circW, swAt_eq] using sw_inv N j hj
  | far i j hij => simpa [swW, circW, swAt_eq] using sw_far N i j hij
  | braid j hj => simpa [swW, circW, swAt_eq] using sw_braid N j hj

theorem pos_eq {a b : List ℕ} (h : SwEq N a b) : pos a = pos b := by
  induction h with
  | refl l => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | cong u v _ ih => funext q; rw [pos_append, pos_append, pos_append, pos_append, ih]
  | inv j hj => funext q; simp [tau_tau]
  | far i j hij => funext q; simp only [pos_cons, pos_nil]; unfold tau; split_ifs <;> omega
  | braid j hj => funext q; simp only [pos_cons, pos_nil]; unfold tau; split_ifs <;> omega

theorem of_eq {a b : List ℕ} (h : a = b) : SwEq N a b := h ▸ refl a

theorem app {a b : List ℕ} (u v : List ℕ) (h : SwEq N a b) : SwEq N (u ++ a ++ v) (u ++ b ++ v) :=
  cong u v h

theorem appL {a b : List ℕ} (u : List ℕ) (h : SwEq N a b) : SwEq N (u ++ a) (u ++ b) := by
  simpa using cong u [] h

theorem appR {a b : List ℕ} (v : List ℕ) (h : SwEq N a b) : SwEq N (a ++ v) (b ++ v) := by
  simpa using cong [] v h

theorem cons {a b : List ℕ} (j : ℕ) (h : SwEq N a b) : SwEq N (j :: a) (j :: b) := appL [j] h

theorem reverse {a b : List ℕ} (h : SwEq N a b) : SwEq N a.reverse b.reverse := by
  induction h with
  | refl l => exact refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | cong u v _ ih =>
    simp only [List.reverse_append]
    simpa only [List.append_assoc] using cong v.reverse u.reverse ih
  | inv j hj => exact inv j hj
  | far i j hij => exact (far i j hij).symm
  | braid j hj => exact braid j hj

/-- A word followed by its reverse cancels. -/
theorem cancel : ∀ (l : List ℕ), Ok N l → SwEq N (l ++ l.reverse) []
  | [], _ => refl _
  | j :: l, hl => by
    have h1 := cancel l (fun x hx => hl x (by simp [hx]))
    have e : j :: l ++ (j :: l).reverse = [j] ++ (l ++ l.reverse) ++ [j] := by simp
    rw [e]
    refine (app [j] [j] h1).trans ?_
    simpa using inv j (hl j (by simp))

/-- An index commutes with a word all of whose indices are far from it. -/
theorem pass : ∀ (j : ℕ) (l : List ℕ), (∀ x ∈ l, x + 2 ≤ j ∨ j + 2 ≤ x) →
    SwEq N (j :: l) (l ++ [j])
  | _, [], _ => refl _
  | j, x :: l, h => by
    have h1 : SwEq N [j, x] [x, j] := by
      rcases h x (by simp) with h' | h'
      · exact (far x j h').symm
      · exact far j x h'
    have h2 := pass j l (fun y hy => h y (by simp [hy]))
    have e1 : j :: x :: l = [] ++ [j, x] ++ l := rfl
    rw [e1]
    refine (app [] l h1).trans ?_
    simpa using cons x h2

end SwEq

/-! ## The normal form of swap words -/

/-- The swaps carrying position `c` down to position `i`: `c - 1, …, i`. -/
def run (c i : ℕ) : List ℕ := (List.range (c - i)).reverse.map (i + ·)

theorem run_self (i : ℕ) : run i i = [] := by simp [run]

theorem run_succ {c i : ℕ} (h : i ≤ c) : run (c + 1) i = c :: run c i := by
  simp only [run, show c + 1 - i = (c - i) + 1 by omega, List.range_succ, List.reverse_append,
    List.map_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
    List.map_nil, List.singleton_append]
  congr 1; omega

theorem mem_run {c i x : ℕ} (h : x ∈ run c i) : i ≤ x ∧ x < c := by
  simp only [run, List.mem_map, List.mem_reverse, List.mem_range] at h
  obtain ⟨d, hd, rfl⟩ := h; omega

/-- A run splits at an intermediate position. -/
theorem run_split {c k i : ℕ} (h1 : i ≤ k) (h2 : k ≤ c) : run c i = run c k ++ run k i := by
  induction c, h2 using Nat.le_induction with
  | base => rw [run_self, List.nil_append]
  | succ c hkc ih => rw [run_succ (by omega), run_succ hkc, ih]; rfl

theorem pos_run {c i : ℕ} (hic : i ≤ c) (q : ℕ) :
    pos (run c i) q = if q = c then i else if i ≤ q ∧ q < c then q + 1 else q := by
  induction c, hic using Nat.le_induction generalizing q with
  | base => rw [run_self, pos_nil]; split_ifs <;> omega
  | succ c hic ih =>
    rw [run_succ hic, pos_cons, ih]
    unfold tau
    split_ifs <;> omega

/-- `s_j` past a run it does not end: `s_j r ≈ r s_{j+1}`. -/
theorem run_braid {N c i j : ℕ} (hij : i ≤ j) (hjc : j + 2 ≤ c) (hc : c + 1 ≤ N) :
    SwEq N (j :: run c i) (run c i ++ [j + 1]) := by
  rw [run_split (k := j + 2) (by omega) hjc, run_split (c := j + 2) (k := j) hij (by omega),
    run_succ (by omega), run_succ (le_refl j), run_self]
  have hA : SwEq N (j :: run c (j + 2)) (run c (j + 2) ++ [j]) :=
    SwEq.pass j _ (fun x hx => Or.inr (mem_run hx).1)
  have hB : SwEq N ((j + 1) :: run j i) (run j i ++ [j + 1]) :=
    SwEq.pass (j + 1) _ (fun x hx => Or.inl (by have := (mem_run hx).2; omega))
  have hbr : SwEq N [j, j + 1, j] [j + 1, j, j + 1] := (SwEq.braid j (by omega)).symm
  refine (SwEq.of_eq (by simp)).trans ((SwEq.appR ([j + 1, j] ++ run j i) hA).trans ?_)
  refine (SwEq.of_eq (by simp)).trans ((SwEq.app (run c (j + 2)) (run j i) hbr).trans ?_)
  refine (SwEq.of_eq (by simp)).trans ((SwEq.appL (run c (j + 2) ++ [j + 1, j]) hB).trans ?_)
  exact SwEq.of_eq (by simp)

/-- The word of a code `cᵢ, cᵢ₊₁, …`: for each level `k` from `i` on, the run
carrying position `cₖ` down to position `k`. -/
def nfw : ℕ → List ℕ → List ℕ
  | _, [] => []
  | i, c :: cs => run c i ++ nfw (i + 1) cs

/-- Prepending `s_j` to the word of a code. -/
def ins (j : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs =>
    if j = c then (c + 1) :: cs
    else if j + 1 = c then j :: cs
    else if c < j then c :: ins j cs
    else c :: ins (j + 1) cs

/-- A valid code at level `i` on `N` wires. -/
def VC (N : ℕ) : ℕ → List ℕ → Prop
  | i, [] => i = N
  | i, c :: cs => i ≤ c ∧ c + 1 ≤ N ∧ VC N (i + 1) cs

theorem mem_nfw : ∀ {N i : ℕ} {cs : List ℕ}, VC N i cs → ∀ x ∈ nfw i cs, i ≤ x ∧ x + 2 ≤ N
  | _, _, [], _, x, hx => by simp [nfw] at hx
  | N, i, c :: cs, ⟨h1, h2, h3⟩, x, hx => by
    rcases List.mem_append.1 hx with hx | hx
    · have := mem_run hx; omega
    · have := mem_nfw h3 x hx; omega

theorem ins_spec {N : ℕ} : ∀ (cs : List ℕ) (i j : ℕ), VC N i cs → i ≤ j → j + 2 ≤ N →
    SwEq N (j :: nfw i cs) (nfw i (ins j cs)) ∧ VC N i (ins j cs)
  | [], i, j, hv, hij, hjN => by simp only [VC] at hv; omega
  | c :: cs, i, j, ⟨h1, h2, h3⟩, hij, hjN => by
    simp only [ins]
    split_ifs with e1 e2 e3
    · subst e1
      refine ⟨?_, ⟨by omega, by omega, h3⟩⟩
      simp only [nfw, run_succ h1]
      exact SwEq.refl _
    · subst e2
      refine ⟨?_, ⟨hij, by omega, h3⟩⟩
      simp only [nfw, run_succ hij]
      have := SwEq.appR (run j i ++ nfw (i + 1) cs) (SwEq.inv (N := N) j hjN)
      simpa using this
    · obtain ⟨hs, hv⟩ := ins_spec cs (i + 1) j h3 (by omega) hjN
      refine ⟨?_, ⟨h1, h2, hv⟩⟩
      simp only [nfw]
      have hp : SwEq N (j :: run c i) (run c i ++ [j]) :=
        SwEq.pass j _ (fun x hx => Or.inl (by have := (mem_run hx).2; omega))
      have := SwEq.appR (nfw (i + 1) cs) hp
      refine this.trans ?_
      simpa using SwEq.appL (run c i) hs
    · obtain ⟨hs, hv⟩ := ins_spec cs (i + 1) (j + 1) h3 (by omega) (by omega)
      refine ⟨?_, ⟨h1, h2, hv⟩⟩
      simp only [nfw]
      have hp : SwEq N (j :: run c i) (run c i ++ [j + 1]) := run_braid hij (by omega) h2
      have := SwEq.appR (nfw (i + 1) cs) hp
      refine this.trans ?_
      simpa using SwEq.appL (run c i) hs

/-- The code of the empty word at level `i`. -/
def idCode (N i : ℕ) : List ℕ := List.range' i (N - i)

theorem idCode_spec (N : ℕ) : ∀ i, i ≤ N → VC N i (idCode N i) ∧ nfw i (idCode N i) = []
  | i, hi => by
    by_cases h : i = N
    · subst h; simp [idCode, VC, nfw]
    · have e : idCode N i = i :: idCode N (i + 1) := by
        simp only [idCode, show N - i = (N - (i + 1)) + 1 by omega, List.range'_succ]
      obtain ⟨h1, h2⟩ := idCode_spec N (i + 1) (by omega)
      rw [e]
      exact ⟨⟨le_refl i, by omega, h1⟩, by simp [nfw, run_self, h2]⟩
termination_by i => N - i

/-- The code of a word. -/
def code (N : ℕ) (l : List ℕ) : List ℕ := l.foldr ins (idCode N 0)

/-- Every swap word is equal to the word of its code. -/
theorem nf_spec {N : ℕ} : ∀ (l : List ℕ), Ok N l → SwEq N l (nfw 0 (code N l)) ∧ VC N 0 (code N l)
  | [], _ => by
    obtain ⟨h1, h2⟩ := idCode_spec N 0 (Nat.zero_le _)
    exact ⟨by simp only [code, List.foldr_nil, h2]; exact SwEq.refl _, h1⟩
  | j :: l, hl => by
    obtain ⟨hs, hv⟩ := nf_spec l (fun x hx => hl x (by simp [hx]))
    obtain ⟨hs', hv'⟩ := ins_spec (code N l) 0 j hv (Nat.zero_le _) (hl j (by simp))
    exact ⟨(SwEq.cons j hs).trans hs', hv'⟩

/-- The word of a code whose permutation fixes the positions `i, …, m - 1`
has all its indices at least `m`. -/
theorem nfw_high {N m : ℕ} : ∀ (cs : List ℕ) (i : ℕ), VC N i cs →
    (∀ q, i ≤ q → q < m → pos (nfw i cs) q = q) → ∀ x ∈ nfw i cs, m ≤ x
  | [], _, _, _, x, hx => by simp [nfw] at hx
  | c :: cs, i, ⟨h1, h2, h3⟩, hfix, x, hx => by
    by_cases him : i < m
    · have hrest : ∀ y ∈ nfw (i + 1) cs, i + 1 ≤ y := fun y hy => (mem_nfw h3 y hy).1
      have hr : pos (run c i) c = i := by rw [pos_run h1]; simp
      have hc : pos (nfw i (c :: cs)) c = i := by
        rw [nfw, pos_append, hr]
        exact pos_below _ _ (fun y hy => by have := hrest y hy; omega)
      have hi := hfix i (le_refl i) him
      have hci : c = i := pos_injective _ (hc.trans hi.symm)
      subst hci
      simp only [nfw, run_self, List.nil_append] at hx hfix
      exact nfw_high cs (c + 1) h3 (fun q hq hqm => hfix q (by omega) hqm) x hx
    · have := (mem_nfw (N := N) (i := i) (cs := c :: cs) ⟨h1, h2, h3⟩ x hx).1; omega

/-- A swap word whose permutation fixes the positions below `m` is equal to
one whose indices are all at least `m`. -/
theorem parabolic {N m : ℕ} (l : List ℕ) (hl : Ok N l) (hfix : ∀ q < m, pos l q = q) :
    ∃ l', SwEq N l l' ∧ Ok N l' ∧ ∀ x ∈ l', m ≤ x := by
  obtain ⟨hs, hv⟩ := nf_spec l hl
  refine ⟨_, hs, fun x hx => (mem_nfw hv x hx).2, nfw_high _ 0 hv ?_⟩
  intro q _ hqm
  rw [← hs.pos_eq]; exact hfix q hqm

/-! ## Gates on disjoint wires commute -/

/-- One above the highest wire a generator acts on. -/
def gHi : {n : ℕ} → Gen Gate n → ℕ
  | _, .gate0 _ => 0
  | _, .gate1 _ => 1
  | _, .gate2 _ => 2
  | _, .gate3 _ => 3
  | _, .up g => gHi g + 1

/-- The lowest wire a generator acts on. -/
def gLo : {n : ℕ} → Gen Gate n → ℕ
  | _, .gate0 _ => 0
  | _, .gate1 _ => 0
  | _, .gate2 _ => 0
  | _, .gate3 _ => 0
  | _, .up g => gLo g + 1

theorem comm_gen : ∀ {n : ℕ} (a b : Gen Gate n), gHi a ≤ gLo b →
    Derivable (theory n) (FreeMonoid.of b * FreeMonoid.of a) (FreeMonoid.of a * FreeMonoid.of b)
  | _, .gate0 c, _, _ => nomatch c
  | _, .gate3 c, _, _ => nomatch c
  | _, .gate1 c, .up b, _ => Derivable.of (Lift.comm1 c b)
  | _, .gate2 c, .up (.up b), _ => Derivable.of (Lift.comm2 c b)
  | _, .up a, .up b, h => by
    have := derivable_shift (comm_gen a b (by simp only [gHi, gLo] at h; omega))
    simpa using this
  | _, .gate1 _, .gate0 c, _ => nomatch c
  | _, .gate1 _, .gate1 _, h => by simp [gHi, gLo] at h
  | _, .gate1 _, .gate2 _, h => by simp [gHi, gLo] at h
  | _, .gate1 _, .gate3 c, _ => nomatch c
  | _, .gate2 _, .gate0 c, _ => nomatch c
  | _, .gate2 _, .gate1 _, h => by simp [gHi, gLo] at h
  | _, .gate2 _, .gate2 _, h => by simp [gHi, gLo] at h
  | _, .gate2 _, .gate3 c, _ => nomatch c
  | _, .gate2 _, .up (.gate0 c), _ => nomatch c
  | _, .gate2 _, .up (.gate1 _), h => by simp [gHi, gLo] at h
  | _, .gate2 _, .up (.gate2 _), h => by simp [gHi, gLo] at h
  | _, .gate2 _, .up (.gate3 c), _ => nomatch c
  | _, .up _, .gate0 c, _ => nomatch c
  | _, .up _, .gate1 _, h => by simp [gHi, gLo] at h
  | _, .up _, .gate2 _, h => by simp [gHi, gLo] at h
  | _, .up _, .gate3 c, _ => nomatch c

/-- Every generator of `u` acts below wire `m`. -/
def LowW {n : ℕ} (m : ℕ) (u : Circ n) : Prop := ∀ g ∈ FreeMonoid.toList u, gHi g ≤ m

/-- Every generator of `v` acts on wire `m` or above. -/
def HighW {n : ℕ} (m : ℕ) (v : Circ n) : Prop := ∀ g ∈ FreeMonoid.toList v, m ≤ gLo g

theorem comm_low_high {n m : ℕ} (u v : Circ n) (hu : LowW m u) (hv : HighW m v) :
    Derivable (theory n) (v * u) (u * v) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rw [mul_one, one_mul]
  | mul_of a u ih =>
    have ha : gHi a ≤ m := hu a (by simp)
    have hu' : LowW m u := fun g hg => hu g (by simp [hg])
    have hva : Derivable (theory n) (v * FreeMonoid.of a) (FreeMonoid.of a * v) := by
      clear ih hu hu'
      induction v using FreeMonoid.inductionOn' with
      | one => rw [mul_one, one_mul]
      | mul_of b v ihv =>
        have hb : m ≤ gLo b := hv b (by simp)
        have hv' : HighW m v := fun g hg => hv g (by simp [hg])
        have h1 := dleft (FreeMonoid.of b) (ihv hv')
        have h2 := dright v (comm_gen a b (le_trans ha hb))
        rw [mul_assoc]
        refine h1.trans ?_
        rw [← mul_assoc, ← mul_assoc]
        exact h2
    rw [← mul_assoc]
    refine (dright u hva).trans ?_
    rw [mul_assoc, mul_assoc]
    exact dleft _ (ih hu')

theorem gHi_le : ∀ {n : ℕ} (g : Gen Gate n), gHi g ≤ n
  | _, .gate0 c => nomatch c
  | _, .gate3 c => nomatch c
  | _, .gate1 _ => by simp [gHi]
  | _, .gate2 _ => by simp [gHi]
  | _, .up g => by have := gHi_le g; simp only [gHi]; omega

theorem gHi_padTop : ∀ {n : ℕ} (g : Gen Gate n), gHi (Gen.padTop g) = gHi g
  | _, .gate0 c => nomatch c
  | _, .gate3 c => nomatch c
  | _, .gate1 _ => rfl
  | _, .gate2 _ => rfl
  | _, .up g => by simp only [Gen.padTop, gHi, gHi_padTop g]

theorem lowW_atBot : ∀ (N : ℕ) {m : ℕ} (g : Circ m), LowW m (atBot N g)
  | 0, _, _ => by intro x hx; simp [atBot] at hx
  | N + 1, m, g => by
    intro x hx
    by_cases h : m = N + 1
    · subst h
      rw [atBot_self] at hx
      exact gHi_le x
    · rw [atBot_succ N g h] at hx
      simp only [padTop, FreeMonoid.toList_map, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [gHi_padTop]
      exact lowW_atBot N g y hy

theorem gLo_swAt : ∀ (N j : ℕ), HighW j (swAt N j)
  | N + 1, j + 1 => by
    intro x hx
    have e : swAt (N + 1) (j + 1) = shift (swAt N j) := rfl
    rw [e] at hx
    simp only [Circuit.shift, FreeMonoid.toList_map, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [gLo]
    have := gLo_swAt N j y hy
    omega
  | _, 0 => fun _ _ => Nat.zero_le _
  | 0, _ + 1 => by intro x hx; simp [swAt, place2] at hx

theorem highW_mul {n m : ℕ} {u v : Circ n} (hu : HighW m u) (hv : HighW m v) : HighW m (u * v) := by
  intro g hg
  simp only [FreeMonoid.toList_mul, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hu g hg
  · exact hv g hg

theorem highW_swW {N m : ℕ} : ∀ (l : List ℕ), (∀ x ∈ l, m ≤ x) → HighW m (swW N l)
  | [], _ => by intro g hg; simp [swW, circW, drawn] at hg
  | j :: l, h => by
    rw [swW_cons]
    refine highW_mul (highW_swW l (fun x hx => h x (by simp [hx]))) ?_
    intro g hg
    exact le_trans (h j (by simp)) (gLo_swAt N j g hg)

/-! ## The placement lemma -/

/-- `A` conjugated by a swap network: the network `μ`, `A`, `μ` backwards. -/
def placedBy (N : ℕ) (μ : List ℕ) (A : Circ N) : Circ N := swW N μ.reverse * A * swW N μ

/-- Two networks that bring the same wires to the positions `0, …, m - 1`,
in the same order, place a circuit on the bottom `m` wires identically. -/
theorem placement {N m : ℕ} {μ₁ μ₂ : List ℕ} (h₁ : Ok N μ₁) (h₂ : Ok N μ₂) {A : Circ N}
    (hA : LowW m A) (H : ∀ q i, i < m → (pos μ₁ q = i ↔ pos μ₂ q = i)) :
    Derivable (theory N) (placedBy N μ₁ A) (placedBy N μ₂ A) := by
  have hok : Ok N (μ₁.reverse ++ μ₂) := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact h₁ x (List.mem_reverse.1 hx)
    · exact h₂ x hx
  obtain ⟨ρ, hρ, hρok, hρm⟩ := parabolic (m := m) (μ₁.reverse ++ μ₂) hok (by
    intro q hq
    rw [pos_append]
    exact (H _ q hq).1 (pos_reverse' μ₁ q))
  have e2 : SwEq N μ₂ (μ₁ ++ ρ) := by
    have c1 : SwEq N (μ₁ ++ μ₁.reverse) [] := SwEq.cancel μ₁ h₁
    have : SwEq N (μ₁ ++ (μ₁.reverse ++ μ₂)) μ₂ := by
      simpa [List.append_assoc] using SwEq.appR μ₂ c1
    exact this.symm.trans (SwEq.appL μ₁ hρ)
  have e2r : SwEq N μ₂.reverse (ρ.reverse ++ μ₁.reverse) := by
    simpa using e2.reverse
  have hρr : HighW m (swW N ρ.reverse) := highW_swW _ (fun x hx => hρm x (List.mem_reverse.1 hx))
  have hcanc : Derivable (theory N) (swW N ρ.reverse * swW N ρ) 1 := by
    rw [← swW_append]; exact (SwEq.cancel ρ hρok).der
  unfold placedBy
  refine Derivable.symm ((dmul (dmul e2r.der (Derivable.refl A)) e2.der).trans ?_)
  rw [swW_append, swW_append]
  have hc := comm_low_high A (swW N ρ.reverse) hA hρr
  have e3 : swW N μ₁.reverse * swW N ρ.reverse * A * (swW N ρ * swW N μ₁) =
      swW N μ₁.reverse * (swW N ρ.reverse * A) * swW N ρ * swW N μ₁ := by simp only [mul_assoc]
  rw [e3]
  refine (dright (swW N μ₁) (dright (swW N ρ) (dleft (swW N μ₁.reverse) hc))).trans ?_
  have e4 : swW N μ₁.reverse * (A * swW N ρ.reverse) * swW N ρ * swW N μ₁ =
      swW N μ₁.reverse * A * (swW N ρ.reverse * swW N ρ) * swW N μ₁ := by simp only [mul_assoc]
  rw [e4]
  have := dright (swW N μ₁) (dleft (swW N μ₁.reverse * A) hcanc)
  simpa only [mul_one] using this

/-! ## The network of `placeG` -/

/-- `pos l` fixes a position above every index of `l`. -/
theorem pos_below_gt : ∀ (l : List ℕ) (q : ℕ), (∀ x ∈ l, x + 1 < q) → pos l q = q
  | [], _, _ => rfl
  | j :: l, q, h => by
    rw [pos_cons, tau_of_gt (h j (by simp)), pos_below_gt l q (fun x hx => h x (by simp [hx]))]

/-- The swap indices of `netL`: the runs carrying the wires of `ps` down,
one at a time. -/
def netK (ps : List ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => netK ps k ++ run (curPos ps k (ps.getD k 0)) k

theorem moveDown_eq (N p i : ℕ) : moveDown N p i = (run p i).map (swAt N) := by
  simp only [moveDown, run, List.map_map]; rfl

theorem netL_eq (N : ℕ) (ps : List ℕ) : netL N ps = (netK ps ps.length).map (swAt N) := by
  have : ∀ k, ((List.range k).flatMap fun i => moveDown N (curPos ps i (ps.getD i 0)) i) =
      (netK ps k).map (swAt N) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, ih, netK, List.map_append]
      simp [moveDown_eq]
  exact this _

theorem swW_eq_drawn (N : ℕ) (l : List ℕ) : swW N l = drawn (l.map (swAt N)) := by
  simp only [swW, circW, List.map_map]; rfl

theorem placeG_eq (N : ℕ) {m : ℕ} (g : Circ m) (ps : List ℕ) :
    placeG N g ps = placedBy N (netK ps ps.length) (atBot N g) := by
  simp only [placeG, placedBy, netL_eq, swW_eq_drawn, drawn, List.reverse_append,
    List.prod_append, List.map_reverse, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem pos_lt {N : ℕ} : ∀ (l : List ℕ), Ok N l → ∀ q < N, pos l q < N
  | [], _, q, hq => hq
  | j :: l, hl, q, hq => by
    rw [pos_cons]
    refine pos_lt l (fun x hx => hl x (by simp [hx])) _ ?_
    have := hl j (by simp)
    unfold tau; split_ifs <;> omega

section Lists

variable {ps : List ℕ}

theorem getD_eq {k : ℕ} (hk : k < ps.length) : ps.getD k 0 = ps[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem take_succ_getD {k : ℕ} (hk : k < ps.length) :
    ps.take (k + 1) = ps.take k ++ [ps.getD k 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, getD_eq hk]; rfl

theorem getD_mem_take {i k : ℕ} (hi : i < k) (hk : k ≤ ps.length) : ps.getD i 0 ∈ ps.take k := by
  rw [getD_eq (by omega)]
  have h1 : i < (ps.take k).length := by simp; omega
  have := List.getElem_mem h1
  rwa [List.getElem_take] at this

theorem getD_inj (hnd : ps.Nodup) {i k : ℕ} (hi : i < ps.length) (hk : k < ps.length)
    (h : ps.getD i 0 = ps.getD k 0) : i = k := by
  rw [getD_eq hi, getD_eq hk] at h
  exact (List.Nodup.getElem_inj_iff hnd).1 h

theorem getD_not_mem_take (hnd : ps.Nodup) {k : ℕ} (hk : k < ps.length) :
    ps.getD k 0 ∉ ps.take k := by
  intro h
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  rw [List.getElem_take] at he
  have hi' : i < k := by simp at hi; omega
  have := getD_inj hnd (i := i) (k := k) (by omega) hk (by rw [getD_eq (by omega), he])
  omega

theorem curPos_zero (q : ℕ) : curPos ps 0 q = q := by simp [curPos]

theorem curPos_succ {k : ℕ} (hk : k < ps.length) (q : ℕ) :
    curPos ps (k + 1) q = curPos ps k q + if q < ps.getD k 0 then 1 else 0 := by
  rw [curPos, curPos, take_succ_getD hk, List.filter_append, List.length_append]
  generalize ps.getD k 0 = p
  by_cases h : q < p <;> simp [h] <;> omega

theorem curPos_mono (hnd : ps.Nodup) : ∀ k, k ≤ ps.length → ∀ q q', q ∉ ps.take k →
    q' ∉ ps.take k → q < q' → curPos ps k q < curPos ps k q'
  | 0, _, q, q', _, _, h => by rw [curPos_zero, curPos_zero]; exact h
  | k + 1, hk, q, q', hq, hq', h => by
    have hk' : k < ps.length := by omega
    rw [take_succ_getD hk'] at hq hq'
    simp only [List.mem_append, List.mem_singleton, not_or] at hq hq'
    have ih := curPos_mono hnd k (by omega) q q' hq.1 hq'.1 h
    have hp := getD_not_mem_take hnd hk'
    rw [curPos_succ hk', curPos_succ hk']
    by_cases h1 : q < ps.getD k 0 <;> by_cases h2 : q' < ps.getD k 0
    · simp only [h1, h2, if_true]; omega
    · have a1 := curPos_mono hnd k (by omega) q _ hq.1 hp h1
      have a2 := curPos_mono hnd k (by omega) _ q' hp hq'.1 (by omega)
      simp only [h1, h2, if_true, if_false]; omega
    · omega
    · simp only [h1, h2, if_false]; omega

/-- The network of `placeG` carries the `i`-th wire of `ps` to position `i`,
and every other wire to its `curPos`. -/
theorem netK_spec {N : ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) : ∀ k, k ≤ ps.length →
    Ok N (netK ps k) ∧ (∀ i < k, pos (netK ps k) (ps.getD i 0) = i) ∧
      (∀ q, q ∉ ps.take k → pos (netK ps k) q = curPos ps k q)
  | 0, _ => ⟨fun x hx => by simp [netK] at hx, fun i hi => by omega,
      fun q _ => by rw [curPos_zero]; rfl⟩
  | k + 1, hk => by
    have hk' : k < ps.length := by omega
    obtain ⟨hok, ha, hb⟩ := netK_spec hnd hps k (by omega)
    rw [show netK ps (k + 1) = netK ps k ++ run (curPos ps k (ps.getD k 0)) k from rfl]
    set p := ps.getD k 0 with hp_def
    have hpn := getD_not_mem_take hnd hk'
    have hpN : p < N := hps p (by rw [hp_def, getD_eq hk']; exact List.getElem_mem hk')
    set c := curPos ps k p with hc_def
    have hpc : pos (netK ps k) p = c := hb p hpn
    -- positions below `k` are taken by the first `k` wires
    have hge : ∀ q, q ∉ ps.take k → k ≤ pos (netK ps k) q := by
      intro q hq
      by_contra hlt
      push Not at hlt
      have e := ha _ hlt
      have hqq : ps.getD (pos (netK ps k) q) 0 = q := pos_injective _ e
      exact hq (hqq ▸ getD_mem_take hlt (by omega))
    have hkc : k ≤ c := hpc ▸ hge p hpn
    have hcN : c < N := hpc ▸ pos_lt _ hok p hpN
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hok x hx
      · have := mem_run hx; omega
    · intro i hi
      simp only [pos_append]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [ha i hi, pos_run hkc]
        split_ifs <;> omega
      · rw [hpc, pos_run hkc, if_pos rfl]
    · intro q hq
      rw [take_succ_getD hk'] at hq
      simp only [List.mem_append, List.mem_singleton, not_or] at hq
      simp only [pos_append]
      rw [hb q hq.1, pos_run hkc, curPos_succ hk']
      have hx := hb q hq.1 ▸ hge q hq.1
      have hne : curPos ps k q ≠ c := fun h => hq.2 (pos_injective _ (by rw [hb q hq.1, hpc, h]))
      have hmono : curPos ps k q < c ↔ q < p := by
        constructor
        · intro h
          by_contra h'
          have : p < q := by omega
          have := curPos_mono hnd k (by omega) p q hpn hq.1 this
          omega
        · intro h; exact curPos_mono hnd k (by omega) q p hq.1 hpn h
      by_cases h1 : q < p
      · rw [if_neg hne, if_pos ⟨hx, hmono.2 h1⟩, if_pos h1]
      · rw [if_neg hne, if_neg (fun h => h1 (hmono.1 h.2)), if_neg h1]; rfl

theorem netK_pos_iff {N : ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {q i : ℕ}
    (hi : i < ps.length) : pos (netK ps ps.length) q = i ↔ q = ps.getD i 0 := by
  obtain ⟨_, ha, _⟩ := netK_spec hnd hps ps.length le_rfl
  constructor
  · intro h; exact pos_injective _ (h.trans (ha i hi).symm)
  · rintro rfl; exact ha i hi

end Lists

theorem map_nodup {ps : List ℕ} (hnd : ps.Nodup) (f : ℕ → ℕ) (hf : Function.Injective f) :
    (ps.map f).Nodup := hnd.map hf

/-- Naturality of `placeG`: conjugating a placed gate by a swap network
places it on the wires the network carries back. -/
theorem placeG_net {N m : ℕ} (g : Circ m) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < N) (hm : ps.length = m) (σ : List ℕ) (hσ : Ok N σ) :
    Derivable (theory N) (swW N σ.reverse * placeG N g ps * swW N σ)
      (placeG N g (ps.map (pos σ.reverse))) := by
  have hinj : Function.Injective (pos σ.reverse) := pos_injective _
  have hσr : Ok N σ.reverse := fun x hx => hσ x (List.mem_reverse.1 hx)
  have hnd' : (ps.map (pos σ.reverse)).Nodup := hnd.map hinj
  have hps' : ∀ p ∈ ps.map (pos σ.reverse), p < N := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact pos_lt _ hσr q (hps q hq)
  rw [placeG_eq, placeG_eq]
  have e : swW N σ.reverse * placedBy N (netK ps ps.length) (atBot N g) * swW N σ =
      placedBy N (σ ++ netK ps ps.length) (atBot N g) := by
    simp only [placedBy, List.reverse_append, swW_append, mul_assoc]
  rw [e]
  refine placement (m := m) ?_ (netK_spec hnd' hps' _ le_rfl).1 (hm ▸ lowW_atBot N g) ?_
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hσ x hx
    · exact (netK_spec hnd hps _ le_rfl).1 x hx
  · intro q i hi
    rw [← hm] at hi
    have hi' : i < (ps.map (pos σ.reverse)).length := by simpa using hi
    have h2 := netK_pos_iff hnd' hps' hi' (q := q)
    rw [pos_append, netK_pos_iff hnd hps hi, h2, getD_eq hi', getD_eq hi, List.getElem_map]
    constructor
    · intro h; rw [← h, pos_reverse]
    · intro h; rw [h, pos_reverse']

/-- Naturality of `placeG` for one swap. -/
theorem placeG_swap {N m : ℕ} (g : Circ m) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < N) (hm : ps.length = m) (j : ℕ) (hj : j + 2 ≤ N) :
    Derivable (theory N) (drawn [swAt N j, placeG N g ps, swAt N j])
      (placeG N g (ps.map (tau j))) := by
  have h := placeG_net g hnd hps hm [j] (fun x hx => by simp at hx; omega)
  have e : drawn [swAt N j, placeG N g ps, swAt N j] = swW N [j].reverse * placeG N g ps * swW N [j] := by
    simp [drawn, swW_eq_drawn, mul_assoc]
  rw [e]
  have e2 : pos [j].reverse = tau j := by funext q; rfl
  rwa [e2] at h

/-! ## Gates idle on the top wire -/

theorem swAt_top (M j : ℕ) (hj : j + 2 ≤ M) : swAt (M + 1) j = padTop (swAt M j) :=
  circ_top M (L.S j) hj

theorem drawn_map_padTop {M : ℕ} (l : List (Circ M)) : drawn (l.map padTop) = padTop (drawn l) := by
  simp [drawn, ← List.map_reverse, map_list_prod]

/-- A gate placed on wires below `M` is idle on the top wire of `M + 1`. -/
theorem placeG_top {M m : ℕ} (g : Circ m) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < M) (hm : ps.length = m) :
    placeG (M + 1) g ps = padTop (placeG M g ps) := by
  have hok := (netK_spec (N := M) hnd hps _ le_rfl).1
  have hmM : m ≠ M + 1 := by
    have : ps.length ≤ M := by
      calc ps.length = ps.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
        _ ≤ (Finset.range M).card := Finset.card_le_card (fun x hx => by
            simp only [List.mem_toFinset] at hx; simpa using hps x hx)
        _ = M := Finset.card_range M
    omega
  have hnet : netL (M + 1) ps = (netL M ps).map padTop := by
    rw [netL_eq, netL_eq, List.map_map]
    refine List.map_congr_left (fun j hj => ?_)
    exact swAt_top M j (hok j hj)
  simp only [placeG, hnet, atBot_succ M g hmM]
  rw [← List.map_reverse, ← drawn_map_padTop]
  simp

/-- The swaps carrying wire `w` to the top wire `M` of `M + 1` wires, the
wires above `w` moving down one: `w, w + 1, …, M - 1`. -/
def topNet (M w : ℕ) : List ℕ := (List.range (M - w)).map (w + ·)

/-- Where a wire goes when wire `w` is moved to the top. -/
def dropW (w q : ℕ) : ℕ := if q < w then q else q - 1

theorem topNet_ok (M w : ℕ) : Ok (M + 1) (topNet M w) := by
  intro x hx
  simp only [topNet, List.mem_map, List.mem_range] at hx
  obtain ⟨d, hd, rfl⟩ := hx; omega

theorem pos_topNet (M w : ℕ) (hw : w ≤ M) (q : ℕ) (hq : q ≤ M) :
    pos (topNet M w) q = if q = w then M else dropW w q := by
  induction M, hw using Nat.le_induction generalizing q with
  | base => simp [topNet, dropW]; split_ifs <;> omega
  | succ M hwM ih =>
    have e : topNet (M + 1) w = topNet M w ++ [M] := by
      simp only [topNet, show M + 1 - w = (M - w) + 1 by omega, List.range_succ, List.map_append,
        List.map_singleton]
      congr 2; omega
    rw [e, pos_append]
    rcases Nat.lt_or_ge q (M + 1) with h | h
    · rw [ih q (by omega)]
      simp only [pos_cons, pos_nil, dropW]
      unfold tau; split_ifs <;> omega
    · have hq' : q = M + 1 := by omega
      subst hq'
      have : pos (topNet M w) (M + 1) = M + 1 :=
        pos_below_gt _ _ (fun x hx => by
          simp only [topNet, List.mem_map, List.mem_range] at hx
          obtain ⟨d, hd, rfl⟩ := hx; omega)
      rw [this]
      simp only [pos_cons, pos_nil, dropW]
      unfold tau; split_ifs <;> omega

/-- A gate placed on wires that avoid `w`, conjugated by the swaps carrying
wire `w` to the top: the same gate on the wires that remain, idle on the
top wire. -/
theorem placeG_toTop {M m : ℕ} (g : Circ m) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p ≤ M) (hm : ps.length = m) (w : ℕ) (hw : w ≤ M) (hwp : w ∉ ps) :
    Derivable (theory (M + 1))
      (swW (M + 1) (topNet M w) * placeG (M + 1) g ps * swW (M + 1) (topNet M w).reverse)
      (padTop (placeG M g (ps.map (dropW w)))) := by
  have hσ : Ok (M + 1) (topNet M w).reverse := fun x hx => topNet_ok M w x (List.mem_reverse.1 hx)
  have h := placeG_net g hnd (fun p hp => by have := hps p hp; omega) hm _ hσ
  rw [List.reverse_reverse] at h
  have e : ps.map (pos (topNet M w)) = ps.map (dropW w) := by
    refine List.map_congr_left (fun q hq => ?_)
    rw [pos_topNet M w hw q (hps q hq), if_neg (fun (h : q = w) => hwp (h ▸ hq))]
  rw [e] at h
  have hnd' : (ps.map (dropW w)).Nodup := by
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) hnd
    simp only [dropW] at hab
    have := hps a ha; have := hps b hb
    have ha' : a ≠ w := fun (h : a = w) => hwp (h ▸ ha)
    have hb' : b ≠ w := fun (h : b = w) => hwp (h ▸ hb)
    split_ifs at hab <;> omega
  have hlt : ∀ p ∈ ps.map (dropW w), p < M := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have := hps q hq
    have hq' : q ≠ w := fun (h : q = w) => hwp (h ▸ hq)
    simp only [dropW]; split_ifs <;> omega
  rwa [placeG_top g hnd' hlt (by simp [hm])] at h

/-! ## Gates on given wires: where they act -/

theorem gHi_pad (n : ℕ) : ∀ {k : ℕ} (g : Gen Gate k), gHi (Gen.pad n g) = gHi g
  | _, .gate0 c => nomatch c
  | _, .gate3 c => nomatch c
  | _, .gate1 _ => rfl
  | _, .gate2 _ => rfl
  | _, .up g => by simp only [Gen.pad, gHi, gHi_pad n g]

theorem lowW_pad {n k m : ℕ} (w : Circ k) (hk : k ≤ m) : LowW m (Circuit.pad n w) := by
  intro x hx
  simp only [Circuit.pad, FreeMonoid.toList_map, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  rw [gHi_pad]; exact le_trans (gHi_le y) hk

theorem lowW_shift {n m : ℕ} {w : Circ n} (h : LowW m w) : LowW (m + 1) (shift w) := by
  intro x hx
  simp only [Circuit.shift, FreeMonoid.toList_map, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [gHi]; have := h y hy; omega

theorem highW_shift {n m : ℕ} {w : Circ n} (h : HighW m w) : HighW (m + 1) (shift w) := by
  intro x hx
  simp only [Circuit.shift, FreeMonoid.toList_map, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [gLo]; have := h y hy; omega

theorem lowW_mul {n m : ℕ} {u v : Circ n} (hu : LowW m u) (hv : LowW m v) : LowW m (u * v) := by
  intro g hg
  simp only [FreeMonoid.toList_mul, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hu g hg
  · exact hv g hg

theorem place1_wires : ∀ (N j : ℕ) (w : Circ 1), LowW (j + 1) (place1 N j w) ∧ HighW j (place1 N j w)
  | N + 1, j + 1, w => by
    obtain ⟨h1, h2⟩ := place1_wires N j w
    exact ⟨lowW_shift h1, highW_shift h2⟩
  | k + 1, 0, w => ⟨lowW_pad w le_rfl, fun _ _ => Nat.zero_le _⟩
  | 0, 0, _ => ⟨fun x hx => by simp [place1] at hx, fun x hx => by simp [place1] at hx⟩
  | 0, _ + 1, _ => ⟨fun x hx => by simp [place1] at hx, fun x hx => by simp [place1] at hx⟩

theorem place2_wires : ∀ (N j : ℕ) (w : Circ 2), LowW (j + 2) (place2 N j w) ∧ HighW j (place2 N j w)
  | N + 1, j + 1, w => by
    obtain ⟨h1, h2⟩ := place2_wires N j w
    exact ⟨lowW_shift h1, highW_shift h2⟩
  | k + 2, 0, w => ⟨lowW_pad w le_rfl, fun _ _ => Nat.zero_le _⟩
  | 0, 0, _ => ⟨fun x hx => by simp [place2] at hx, fun x hx => by simp [place2] at hx⟩
  | 0, _ + 1, _ => ⟨fun x hx => by simp [place2] at hx, fun x hx => by simp [place2] at hx⟩
  | 1, 0, _ => ⟨fun x hx => by simp [place2] at hx, fun x hx => by simp [place2] at hx⟩

theorem place1_mul : ∀ (N j : ℕ) (a b : Circ 1), place1 N j (a * b) = place1 N j a * place1 N j b
  | N + 1, j + 1, a, b => by
    show shift (place1 N j (a * b)) = shift (place1 N j a) * shift (place1 N j b)
    rw [place1_mul N j, map_mul]
  | k + 1, 0, a, b => map_mul (Circuit.pad k) a b
  | 0, 0, _, _ => rfl
  | 0, _ + 1, _, _ => rfl

theorem xAt_eq (N q : ℕ) : xAt N q = circW N [L.H q, L.Z q, L.H q] := by
  simp only [xAt, x, drawn, circW, List.map, L.circ, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
  erw [place1_mul, place1_mul]

theorem xAt_wires (N q : ℕ) : LowW (q + 1) (xAt N q) ∧ HighW q (xAt N q) :=
  place1_wires N q x

theorem swAt_wires (N j : ℕ) : LowW (j + 2) (swAt N j) ∧ HighW j (swAt N j) :=
  place2_wires N j swap

@[simp] theorem upLBy_H (j i : ℕ) : upLBy j (L.H i) = L.H (i + j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, ih, upL]; rfl
@[simp] theorem upLBy_Z (j i : ℕ) : upLBy j (L.Z i) = L.Z (i + j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, ih, upL]; rfl
@[simp] theorem upLBy_C (j i : ℕ) : upLBy j (L.C i) = L.C (i + j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, ih, upL]; rfl
@[simp] theorem upLBy_K (j i : ℕ) : upLBy j (L.K i) = L.K (i + j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, ih, upL]; rfl

/-! ## `X` through swaps -/

/-- The table for `X` through a swap: (f2) and (f1). -/
def xsT : Tbl := [([.H 1, .S 0], [.S 0, .H 0]), ([.Z 1, .S 0], [.S 0, .Z 0])]

theorem xsT_ok : AllD 2 xsT := by
  intro e he
  simp only [xsT, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · have h := derivable_rule Rule.f2 0
    simpa [circW, drawn, map_mul, L.circ, place2, place1] using h
  · have h := derivable_rule Rule.f1 0
    simpa [circW, drawn, map_mul, L.circ, place2, place1] using h

theorem xs2 : Derivable (theory 2) (circW 2 [.H 1, .Z 1, .H 1, .S 0]) (circW 2 [.S 0, .H 0, .Z 0, .H 0]) :=
  check_pure (N := 1) xsT_ok (ss := [.rw 2 0 false, .rw 1 1 false, .rw 0 0 false]) (by decide)
    (by decide)

/-- `X` on the upper wire of a swap comes out on the lower one. -/
theorem x_sw_up (N j : ℕ) (hj : j + 2 ≤ N) :
    Derivable (theory N) (drawn [xAt N (j + 1), swAt N j]) (drawn [swAt N j, xAt N j]) := by
  have h := lift_word (K := 2) (by decide) xs2 j N hj
  simp only [List.map, upLBy_H, upLBy_Z, upBy_S, Nat.zero_add] at h
  rw [show 1 + j = j + 1 by omega] at h
  rw [xAt_eq, xAt_eq, swAt_eq]
  simpa [circW, drawn, mul_assoc] using h

/-- Two inverse conjugations. -/
theorem conj_mul {N : ℕ} {c a b : Circ N} (hc : Derivable (theory N) (c * c) 1) :
    Derivable (theory N) (c * (a * b) * c) ((c * a * c) * (c * b * c)) := by
  have : (c * a * c) * (c * b * c) = c * a * (c * c) * b * c := by simp only [mul_assoc]
  rw [this]
  have := dright c (dright b (dleft (c * a) hc))
  simpa only [mul_one, mul_assoc] using this.symm

theorem swsw (N j : ℕ) (hj : j + 2 ≤ N) : Derivable (theory N) (swAt N j * swAt N j) 1 := by
  simpa [drawn] using sw_inv N j hj

/-- Conjugating `X` by a swap. -/
theorem x_conj (N j q : ℕ) (hj : j + 2 ≤ N) :
    Derivable (theory N) (swAt N j * xAt N q * swAt N j) (xAt N (tau j q)) := by
  have hs := swsw N j hj
  -- from `drawn [X, s] ≈ drawn [s, X']`, i.e. `s X ≈ X' s`
  have of_pass : ∀ q', Derivable (theory N) (swAt N j * xAt N q) (xAt N q' * swAt N j) →
      Derivable (theory N) (swAt N j * xAt N q * swAt N j) (xAt N q') := by
    intro q' h
    have := dright (swAt N j) h
    rw [mul_assoc (xAt N q')] at this
    have h2 := dleft (xAt N q') hs
    rw [mul_one] at h2
    exact this.trans h2
  by_cases h1 : q = j + 1
  · subst h1
    have : tau j (j + 1) = j := by simp [tau]
    rw [this]
    exact of_pass j (by simpa [drawn] using x_sw_up N j hj)
  by_cases h2 : q = j
  · subst h2
    have : tau q q = q + 1 := by simp [tau]
    rw [this]
    refine of_pass (q + 1) ?_
    -- `s X_q ≈ X_{q+1} s` from `s X_{q+1} ≈ X_q s` by conjugating with `s`
    have h := (by simpa [drawn] using x_sw_up N q hj :
      Derivable (theory N) (swAt N q * xAt N (q + 1)) (xAt N q * swAt N q))
    have a1 := dright (swAt N q) (dleft (swAt N q) h)
    have e1 : swAt N q * (swAt N q * xAt N (q + 1)) * swAt N q =
        (swAt N q * swAt N q) * xAt N (q + 1) * swAt N q := by simp only [mul_assoc]
    have e2 : swAt N q * (xAt N q * swAt N q) * swAt N q =
        swAt N q * xAt N q * (swAt N q * swAt N q) := by simp only [mul_assoc]
    rw [e1, e2] at a1
    have b1 := dright (swAt N q) (dright (xAt N (q + 1)) hs)
    have b2 := dleft (swAt N q * xAt N q) hs
    rw [one_mul] at b1; rw [mul_one] at b2
    exact b2.symm.trans (a1.symm.trans b1)
  · have ht : tau j q = q := by unfold tau; split_ifs <;> omega
    rw [ht]
    refine of_pass q ?_
    rcases Nat.lt_or_ge q j with h3 | h3
    · exact comm_low_high (xAt N q) (swAt N j) (fun g hg => le_trans ((xAt_wires N q).1 g hg) h3)
        (swAt_wires N j).2
    · exact (comm_low_high (swAt N j) (xAt N q)
        (fun g hg => le_trans ((swAt_wires N j).1 g hg) (by omega)) (xAt_wires N q).2).symm

theorem drawn_cons {N : ℕ} (a : Circ N) (l : List (Circ N)) : drawn (a :: l) = drawn l * a := by
  simp [drawn]

/-- Conjugating a row of `X` gates by a swap. -/
theorem xs_conj (N j : ℕ) (hj : j + 2 ≤ N) : ∀ ws : List ℕ,
    Derivable (theory N) (swAt N j * drawn (ws.map (xAt N)) * swAt N j)
      (drawn ((ws.map (tau j)).map (xAt N)))
  | [] => by simpa [drawn] using swsw N j hj
  | q :: ws => by
    simp only [List.map_cons, drawn_cons]
    exact (conj_mul (swsw N j hj)).trans (dmul (xs_conj N j hj ws) (x_conj N j q hj))

theorem colourW_eq (N : ℕ) (ws : List ℕ) (G : Circ N) :
    colourW N ws G = drawn (ws.map (xAt N)) * G * drawn (ws.map (xAt N)) := by
  simp [colourW, drawn, List.reverse_append, List.prod_append, mul_assoc]

/-- Conjugating a coloured gate by a swap. -/
theorem colourW_conj (N j : ℕ) (hj : j + 2 ≤ N) (ws : List ℕ) (G : Circ N) :
    Derivable (theory N) (swAt N j * colourW N ws G * swAt N j)
      (colourW N (ws.map (tau j)) (swAt N j * G * swAt N j)) := by
  rw [colourW_eq, colourW_eq]
  have hs := swsw N j hj
  have h1 := conj_mul (a := drawn (ws.map (xAt N)) * G) (b := drawn (ws.map (xAt N))) hs
  have h2 := conj_mul (a := drawn (ws.map (xAt N))) (b := G) hs
  exact h1.trans (dmul (h2.trans (dmul (xs_conj N j hj ws) (Derivable.refl _)))
    (xs_conj N j hj ws))

/-! ## Naturality of `mc` -/

/-- A strictly increasing list is determined by its elements. -/
theorem eq_of_lt_mem : ∀ {l₁ l₂ : List ℕ}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (by simp)) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      have ha := (h a).1 (by simp)
      have hb := (h b).2 (by simp)
      simp only [List.mem_cons] at ha hb
      rcases ha with ha | ha
      · exact ha
      rcases hb with hb | hb
      · exact hb.symm
      have := h₂.1 a ha; have := h₁.1 b hb; omega
    subst hab
    rw [eq_of_lt_mem h₁.2 h₂.2 (fun x => ?_)]
    constructor
    · intro hx
      have hx' := (h x).1 (by simp [hx])
      have : a < x := h₁.1 x hx
      simp only [List.mem_cons] at hx'
      rcases hx' with rfl | hx'
      · omega
      · exact hx'
    · intro hx
      have hx' := (h x).2 (by simp [hx])
      have : a < x := h₂.1 x hx
      simp only [List.mem_cons] at hx'
      rcases hx' with rfl | hx'
      · omega
      · exact hx'

theorem tau_lt {j N q : ℕ} (hj : j + 2 ≤ N) (hq : q < N) : tau j q < N := by
  unfold tau; split_ifs <;> omega

/-- Filtering `range N` by a predicate read through the transposition. -/
theorem filter_tau {N j : ℕ} (hj : j + 2 ≤ N) (P : ℕ → Bool) (hP : ¬ (P j = true ∧ P (j + 1) = true)) :
    (List.range N).filter (fun i => P (tau j i)) = ((List.range N).filter P).map (tau j) := by
  have hr : (List.range N).Pairwise (· < ·) := List.pairwise_lt_range
  refine eq_of_lt_mem (hr.filter _) ?_ ?_
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) (hr.filter P)
    simp only [List.mem_filter] at ha hb
    unfold tau
    split_ifs <;> first | omega | (exfalso; apply hP; constructor <;> simp_all)
  · intro q
    simp only [List.mem_filter, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨hq, hP'⟩
      exact ⟨tau j q, ⟨tau_lt hj hq, hP'⟩, tau_tau j q⟩
    · rintro ⟨y, ⟨hy, hPy⟩, rfl⟩
      exact ⟨tau_lt hj hy, by rw [tau_tau]; exact hPy⟩

theorem contains_map_tau (j i : ℕ) (tg : List ℕ) :
    (tg.map (tau j)).contains i = tg.contains (tau j i) := by
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [tau_tau]
  · intro h; exact ⟨tau j i, h, tau_tau j i⟩

/-- The number of special wires of a kind. -/
def kindSp : Kind → ℕ
  | .box => 1 | .zx => 1 | .xz => 1 | .hg => 2

theorem canonAt_swap {N : ℕ} (K : Kind) (k : ℕ) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < N) (hlen : ps.length = kindSp K + k) (j : ℕ) (hj : j + 2 ≤ N) :
    Derivable (theory N) (drawn [swAt N j, canonAt N K k ps, swAt N j])
      (canonAt N K k (ps.map (tau j))) := by
  cases K with
  | box => exact placeG_swap (box k) hnd hps (by simp [kindSp] at hlen; omega) j hj
  | zx => exact placeG_swap (zx k) hnd hps (by simp [kindSp] at hlen; omega) j hj
  | xz => exact placeG_swap (xz k) hnd hps (by simp [kindSp] at hlen; omega) j hj
  | hg => exact placeG_swap (mch k) hnd hps (by simp [kindSp] at hlen; omega) j hj

theorem ctrlWires_nodup (N : ℕ) (tg : List ℕ) (c : ℕ → Option Bool) (htg : tg.Nodup) :
    (tg ++ ctrlWires N tg c).Nodup := by
  rw [List.nodup_append]
  refine ⟨htg, (List.nodup_range).filter _, fun a ha b hb hab => ?_⟩
  subst hab
  simp only [ctrlWires, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hb
  have h3 : ¬ tg.contains a = true := by rw [hb.2.2]; decide
  exact h3 (List.contains_iff_mem.2 ha)

/-- Naturality of `mc` for one swap that does not exchange two controls. -/
theorem mc_swap (N j : ℕ) (hj : j + 2 ≤ N) (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool)
    (htg : tg.length = kindSp K) (hnd : tg.Nodup) (htgN : ∀ t ∈ tg, t < N)
    (hnc : ¬ (j ∈ ctrlWires N tg c ∧ j + 1 ∈ ctrlWires N tg c)) :
    Derivable (theory N) (drawn [swAt N j, mc N K tg c, swAt N j])
      (mc N K (tg.map (tau j)) (c ∘ tau j)) := by
  have hcw : ctrlWires N (tg.map (tau j)) (c ∘ tau j) = (ctrlWires N tg c).map (tau j) := by
    unfold ctrlWires
    have := filter_tau hj (fun i => (c i).isSome && !(tg.contains i)) (by
      intro ⟨h1, h2⟩; apply hnc
      simp only [ctrlWires, List.mem_filter, List.mem_range]
      exact ⟨⟨by omega, h1⟩, ⟨by omega, h2⟩⟩)
    rw [← this]
    congr 1; funext i
    simp only [Function.comp, contains_map_tau]
  have hww : whiteWires N (tg.map (tau j)) (c ∘ tau j) = (whiteWires N tg c).map (tau j) := by
    unfold whiteWires
    have := filter_tau hj (fun i => c i == some false && !(tg.contains i)) (by
      intro ⟨h1, h2⟩; apply hnc
      simp only [ctrlWires, List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
      refine ⟨⟨by omega, by simp [h1.1], h1.2⟩, ⟨by omega, by simp [h2.1], h2.2⟩⟩)
    rw [← this]
    congr 1; funext i
    simp only [Function.comp, contains_map_tau]
  unfold mc
  rw [hcw, hww, List.length_map]
  have hs := swsw N j hj
  have e : drawn [swAt N j, colourW N (whiteWires N tg c)
      (canonAt N K (ctrlWires N tg c).length (tg ++ ctrlWires N tg c)), swAt N j] =
      swAt N j * colourW N (whiteWires N tg c)
        (canonAt N K (ctrlWires N tg c).length (tg ++ ctrlWires N tg c)) * swAt N j := by
    simp [drawn, mul_assoc]
  rw [e]
  refine (colourW_conj N j hj _ _).trans ?_
  rw [colourW_eq, colourW_eq]
  refine dright _ (dleft _ ?_)
  have h := canonAt_swap K (ctrlWires N tg c).length (ctrlWires_nodup N tg c hnd)
    (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact htgN p hp
      · simp only [ctrlWires, List.mem_filter, List.mem_range] at hp; exact hp.1)
    (by simp [htg]) j hj
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one, List.map_append] at h
  simpa only [mul_assoc, List.map_append] using h

/-! ## `atBot` -/

theorem atBot_mul : ∀ (N : ℕ) {m : ℕ} (a b : Circ m), atBot N (a * b) = atBot N a * atBot N b
  | 0, _, _, _ => by simp [atBot]
  | N + 1, m, a, b => by
    by_cases h : m = N + 1
    · subst h; simp
    · rw [atBot_succ N _ h, atBot_succ N _ h, atBot_succ N _ h, atBot_mul N, map_mul]

theorem atBot_drawn (N : ℕ) {m : ℕ} (l : List (Circ m)) :
    atBot N (drawn l) = drawn (l.map (atBot N)) := by
  induction l with
  | nil =>
    show atBot N 1 = 1
    have := atBot_mul N (1 : Circ m) 1
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  | cons a l ih => rw [drawn_cons, List.map_cons, drawn_cons, atBot_mul, ih]

/-- A derivation on `m` wires holds on the bottom `m` wires of `N ≥ m`. -/
theorem der_atBot {m : ℕ} {a b : Circ m} (d : Derivable (theory m) a b) :
    ∀ N, m ≤ N → Derivable (theory N) (atBot N a) (atBot N b)
  | 0, h => by simp [atBot]; exact Derivable.refl _
  | N + 1, h => by
    by_cases e : m = N + 1
    · subst e; simpa using d
    · rw [atBot_succ N _ e, atBot_succ N _ e]
      exact derivable_padTop (der_atBot d N (by omega))

theorem atBot_swAt {m : ℕ} (u : ℕ) (hu : u + 2 ≤ m) : ∀ N, m ≤ N → atBot N (swAt m u) = swAt N u
  | 0, h => by omega
  | N + 1, h => by
    by_cases e : m = N + 1
    · subst e; simp
    · rw [atBot_succ N _ e, atBot_swAt u hu N (by omega), swAt_top N u (by omega)]

/-! ## Swapping two controls -/

/-- The canonical gate of a kind with `k` controls, on its own wires. -/
def canonC : (K : Kind) → (k : ℕ) → Circ (k + kindSp K)
  | .box, k => box k
  | .zx, k => zx k
  | .xz, k => xz k
  | .hg, k => mch k

theorem canonAt_eq (N : ℕ) (K : Kind) (k : ℕ) (ps : List ℕ) :
    canonAt N K k ps = placeG N (canonC K k) ps := by
  cases K <;> rfl

/-- The canonical gate commutes with the swap of any two adjacent controls
(Equations (307), (313) and (353) at the canonical position). -/
def CanonSym (K : Kind) (k : ℕ) : Prop :=
  ∀ u, kindSp K ≤ u → u + 2 ≤ k + kindSp K →
    Derivable (theory (k + kindSp K)) (drawn [swAt _ u, canonC K k, swAt _ u]) (canonC K k)

theorem tau_getD {ps : List ℕ} (hnd : ps.Nodup) {u j i : ℕ} (hi : i < ps.length)
    (hu : u + 1 < ps.length) (hpu : ps.getD u 0 = j) (hpu' : ps.getD (u + 1) 0 = j + 1) :
    tau j (ps.getD (tau u i) 0) = ps.getD i 0 := by
  by_cases h1 : i = u
  · subst h1
    have e : tau i i = i + 1 := by simp [tau]
    rw [e, hpu', hpu]; simp [tau]
  by_cases h2 : i = u + 1
  · subst h2
    have e : tau u (u + 1) = u := by simp [tau]
    rw [e, hpu, hpu']; simp [tau]
  · have e : tau u i = i := by unfold tau; rw [if_neg h1, if_neg h2]
    rw [e]
    have n1 : ps.getD i 0 ≠ j := fun h => h1 (getD_inj hnd hi (by omega) (h.trans hpu.symm))
    have n2 : ps.getD i 0 ≠ j + 1 := fun h => h2 (getD_inj hnd hi hu (h.trans hpu'.symm))
    unfold tau; rw [if_neg n1, if_neg n2]

/-- A placed gate that is symmetric in its wires `u`, `u + 1`, placed with
those on the wires `j`, `j + 1`, commutes with their swap. -/
theorem placeG_sym {N m : ℕ} (g : Circ m) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < N) (hm : ps.length = m) (u j : ℕ) (hu : u + 2 ≤ m) (hj : j + 2 ≤ N)
    (hpu : ps.getD u 0 = j) (hpu' : ps.getD (u + 1) 0 = j + 1)
    (hsym : Derivable (theory m) (drawn [swAt m u, g, swAt m u]) g) :
    Derivable (theory N) (drawn [swAt N j, placeG N g ps, swAt N j]) (placeG N g ps) := by
  have hmN : m ≤ N := by
    calc m = ps.length := hm.symm
      _ = ps.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ (Finset.range N).card := Finset.card_le_card (fun x hx => by
          simp only [List.mem_toFinset] at hx; simpa using hps x hx)
      _ = N := Finset.card_range N
  have hA := der_atBot hsym N hmN
  rw [atBot_drawn, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    atBot_swAt u hu N hmN] at hA
  set A := atBot N g
  set μ := netK ps ps.length
  have hok := (netK_spec hnd hps _ le_rfl).1
  rw [placeG_eq]
  have e1 : drawn [swAt N j, placedBy N μ A, swAt N j] = placedBy N (j :: μ) A := by
    simp only [placedBy, drawn, List.reverse_cons, swW_append, swW_cons, swW_nil, List.reverse_nil,
      List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one, one_mul,
      List.singleton_append, mul_assoc]
  rw [e1]
  have e2 : placedBy N (j :: μ) (drawn [swAt N u, A, swAt N u]) = placedBy N (j :: μ ++ [u]) A := by
    simp only [placedBy, drawn, List.reverse_cons, List.reverse_append, swW_append, swW_cons,
      swW_nil, List.reverse_nil, List.nil_append, List.cons_append, List.prod_cons, List.prod_nil,
      mul_one, one_mul, List.singleton_append, mul_assoc]
  have h3 : Derivable (theory N) (placedBy N (j :: μ) A) (placedBy N (j :: μ ++ [u]) A) := by
    rw [← e2]; unfold placedBy; exact dright _ (dleft _ hA.symm)
  refine h3.trans ?_
  refine placement (m := m) ?_ hok (lowW_atBot N g) ?_
  · intro x hx
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hx | rfl
    · exact hj
    · exact hok x hx
    · omega
  · intro q i hi
    rw [← hm] at hi
    have hτi : tau u i < ps.length := by unfold tau; split_ifs <;> omega
    have hu1 : u + 1 < ps.length := by omega
    have aux := tau_getD hnd hi hu1 hpu hpu'
    rw [pos_append, pos_cons, pos_cons, pos_nil, netK_pos_iff hnd hps hi]
    constructor
    · intro h
      have h' : pos μ (tau j q) = tau u i := by rw [← h, tau_tau]
      rw [netK_pos_iff hnd hps hτi] at h'
      rw [← tau_tau j q, h', aux]
    · intro h
      subst h
      rw [← aux, tau_tau, (netK_pos_iff hnd hps hτi).2 rfl, tau_tau]

theorem range_split {N j : ℕ} (hj : j + 2 ≤ N) :
    List.range N = List.range j ++ j :: (j + 1) :: List.range' (j + 1 + 1) (N - (j + 2)) := by
  have h1 := @List.range'_append_1 0 j (N - j)
  rw [Nat.zero_add, show j + (N - j) = N by omega] at h1
  rw [List.range_eq_range', List.range_eq_range', ← h1]
  congr 1
  rw [show N - j = (N - (j + 2)) + 1 + 1 by omega, List.range'_succ, List.range'_succ]

/-- A permutation of a row of distinct `X` gates. -/
theorem xs_perm {N : ℕ} {l l' : List ℕ} (hp : l.Perm l') (hnd : l.Nodup) :
    Derivable (theory N) (drawn (l.map (xAt N))) (drawn (l'.map (xAt N))) := by
  induction hp with
  | nil => exact Derivable.refl _
  | cons x _ ih =>
    simp only [List.map_cons, drawn_cons]
    exact dright _ (ih (List.nodup_cons.1 hnd).2)
  | swap x y l =>
    simp only [List.map_cons, drawn_cons, mul_assoc]
    refine dleft _ ?_
    have hxy : y ≠ x := fun h => by subst h; simp at hnd
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · exact comm_low_high (xAt N y) (xAt N x) (fun g hg => le_trans ((xAt_wires N y).1 g hg) h)
        (xAt_wires N x).2
    · exact (comm_low_high (xAt N x) (xAt N y) (fun g hg => le_trans ((xAt_wires N x).1 g hg) h)
        (xAt_wires N y).2).symm
  | trans h1 _ ih1 ih2 => exact (ih1 hnd).trans (ih2 (h1.nodup_iff.1 hnd))

theorem whiteWires_nodup (N : ℕ) (tg : List ℕ) (c : ℕ → Option Bool) : (whiteWires N tg c).Nodup :=
  (List.nodup_range).filter _

/-- The white wires after a swap are those before, swapped, in another order. -/
theorem whiteWires_perm (N j : ℕ) (hj : j + 2 ≤ N) (tg : List ℕ) (c : ℕ → Option Bool) :
    ((whiteWires N tg c).map (tau j)).Perm (whiteWires N (tg.map (tau j)) (c ∘ tau j)) := by
  refine (List.perm_ext_iff_of_nodup ((whiteWires_nodup N tg c).map (fun a b h => by
    rw [← tau_tau j a, h, tau_tau])) (whiteWires_nodup N _ _)).2 (fun i => ?_)
  simp only [whiteWires, List.mem_map, List.mem_filter, List.mem_range, Function.comp,
    contains_map_tau]
  constructor
  · rintro ⟨y, ⟨hy, hP⟩, rfl⟩
    exact ⟨tau_lt hj hy, by rw [tau_tau]; exact hP⟩
  · rintro ⟨hi, hP⟩
    exact ⟨tau j i, ⟨tau_lt hj hi, hP⟩, tau_tau j i⟩

/-- Naturality of `mc` for one swap, for every kind and every controls,
given the symmetry of the canonical gate in its controls. -/
theorem mc_swap_sym (N j : ℕ) (hj : j + 2 ≤ N) (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool)
    (htg : tg.length = kindSp K) (hnd : tg.Nodup) (htgN : ∀ t ∈ tg, t < N)
    (hsym : CanonSym K (ctrlWires N tg c).length) :
    Derivable (theory N) (drawn [swAt N j, mc N K tg c, swAt N j])
      (mc N K (tg.map (tau j)) (c ∘ tau j)) := by
  by_cases hb : j ∈ ctrlWires N tg c ∧ j + 1 ∈ ctrlWires N tg c
  swap
  · exact mc_swap N j hj K tg c htg hnd htgN hb
  set P : ℕ → Bool := fun i => (c i).isSome && !(tg.contains i) with hP
  have hPj : P j = true := by
    have := hb.1; simp only [ctrlWires, List.mem_filter] at this; exact this.2
  have hPj' : P (j + 1) = true := by
    have := hb.2; simp only [ctrlWires, List.mem_filter] at this; exact this.2
  have hjt : j ∉ tg := by
    intro h; simp only [hP, Bool.and_eq_true, Bool.not_eq_true'] at hPj
    have h3 : ¬ tg.contains j = true := by rw [hPj.2]; decide
    exact h3 (List.contains_iff_mem.2 h)
  have hjt' : j + 1 ∉ tg := by
    intro h; simp only [hP, Bool.and_eq_true, Bool.not_eq_true'] at hPj'
    have h3 : ¬ tg.contains (j + 1) = true := by rw [hPj'.2]; decide
    exact h3 (List.contains_iff_mem.2 h)
  have htg' : tg.map (tau j) = tg := by
    conv_rhs => rw [← List.map_id tg]
    refine List.map_congr_left (fun t ht => ?_)
    have : t ≠ j := fun h => hjt (h ▸ ht)
    have : t ≠ j + 1 := fun h => hjt' (h ▸ ht)
    simp only [id]; unfold tau; split_ifs <;> omega
  -- the control wires do not change
  have hcw : ctrlWires N tg (c ∘ tau j) = ctrlWires N tg c := by
    unfold ctrlWires
    refine List.filter_congr (fun i _ => ?_)
    simp only [Function.comp]
    have hs1 : (c j).isSome = true := by
      simp only [hP, Bool.and_eq_true] at hPj; exact hPj.1
    have hs2 : (c (j + 1)).isSome = true := by
      simp only [hP, Bool.and_eq_true] at hPj'; exact hPj'.1
    unfold tau; split_ifs with h1 h2
    · rw [h1, hs1, hs2]
    · rw [h2, hs1, hs2]
    · rfl
  -- the position of `j` among the wires of the canonical gate
  have hsplit : ctrlWires N tg c =
      (List.range j).filter P ++ j :: (j + 1) :: (List.range' (j + 1 + 1) (N - (j + 2))).filter P := by
    unfold ctrlWires
    rw [range_split hj, List.filter_append, List.filter_cons_of_pos hPj,
      List.filter_cons_of_pos hPj']
  set u := tg.length + ((List.range j).filter P).length with hu
  have hpu : (tg ++ ctrlWires N tg c).getD u 0 = j := by
    rw [hsplit, ← List.append_assoc, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp [hu])]
    simp [hu]
  have hpu' : (tg ++ ctrlWires N tg c).getD (u + 1) 0 = j + 1 := by
    rw [hsplit, ← List.append_assoc, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp only [List.length_append, hu]; omega)]
    simp [hu, show tg.length + (List.filter P (List.range j)).length + 1 -
      (tg.length + (List.filter P (List.range j)).length) = 1 by omega]
  have hlen : (tg ++ ctrlWires N tg c).length = (ctrlWires N tg c).length + kindSp K := by
    simp [htg, Nat.add_comm]
  have hu2 : u + 2 ≤ (ctrlWires N tg c).length + kindSp K := by
    rw [← hlen, hsplit]; simp [hu]; omega
  have hsym' := hsym u (by simp [hu, htg]) hu2
  have hps : ∀ p ∈ tg ++ ctrlWires N tg c, p < N := fun p hp => by
    rcases List.mem_append.1 hp with hp | hp
    · exact htgN p hp
    · simp only [ctrlWires, List.mem_filter, List.mem_range] at hp; exact hp.1
  have hG := placeG_sym (canonC K (ctrlWires N tg c).length) (ctrlWires_nodup N tg c hnd) hps
    hlen u j hu2 hj hpu hpu' hsym'
  unfold mc
  rw [htg', hcw, canonAt_eq]
  have e : drawn [swAt N j, colourW N (whiteWires N tg c)
      (placeG N (canonC K (ctrlWires N tg c).length) (tg ++ ctrlWires N tg c)), swAt N j] =
      swAt N j * colourW N (whiteWires N tg c)
        (placeG N (canonC K (ctrlWires N tg c).length) (tg ++ ctrlWires N tg c)) * swAt N j := by
    simp [drawn, mul_assoc]
  rw [e]
  refine (colourW_conj N j hj _ _).trans ?_
  rw [colourW_eq, colourW_eq]
  have hG' : Derivable (theory N)
      (swAt N j * placeG N (canonC K (ctrlWires N tg c).length) (tg ++ ctrlWires N tg c) * swAt N j)
      (placeG N (canonC K (ctrlWires N tg c).length) (tg ++ ctrlWires N tg c)) := by
    simpa [drawn, mul_assoc] using hG
  have hw := whiteWires_perm N j hj tg c
  rw [htg'] at hw
  have hx := xs_perm (N := N) hw ((whiteWires_nodup N tg c).map (fun a b h => by
    rw [← tau_tau j a, h, tau_tau]))
  exact dmul (dmul hx hG') hx

/-! ## The canonical gates at the canonical position -/

theorem netK_id : ∀ (m k : ℕ), k ≤ m → netK (List.range m) k = []
  | _, 0, _ => rfl
  | m, k + 1, hk => by
    rw [netK, netK_id m k (by omega)]
    have h1 : (List.range m).getD k 0 = k := by
      rw [getD_eq (by simp; omega), List.getElem_range]
    have h2 : curPos (List.range m) k k = k := by
      have : (List.take k (List.range m)).filter (fun p => decide (k < p)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        rw [List.take_range] at ha
        simp only [List.mem_range] at ha
        simp only [decide_eq_true_eq]; omega
      simp only [curPos, this, List.length_nil, Nat.add_zero]
    rw [h1, h2, run_self]; rfl

theorem placeG_id (m : ℕ) (g : Circ m) : placeG m g (List.range m) = g := by
  simp [placeG, netL_eq, netK_id m m le_rfl, drawn]

/-- The canonical gate is `mc` on its own wires with black controls. -/
theorem mc_canon (K : Kind) (k : ℕ) :
    mc (k + kindSp K) K (List.range (kindSp K)) (blackOn (kindSp K) (k + kindSp K)) =
      canonC K k := by
  have hcw : ctrlWires (k + kindSp K) (List.range (kindSp K)) (blackOn (kindSp K) (k + kindSp K)) =
      List.range' (kindSp K) k := by
    refine eq_of_lt_mem ((List.pairwise_lt_range).filter _) ?_ (fun i => ?_)
    · exact List.pairwise_lt_range'
    · simp only [ctrlWires, blackOn, List.mem_filter, List.mem_range, List.mem_range'_1,
        Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq]
      constructor
      · rintro ⟨_, h1, h2⟩
        by_cases h : kindSp K ≤ i ∧ i < k + kindSp K
        · omega
        · simp [h] at h1
      · intro h
        refine ⟨by omega, by simp; omega, ?_⟩
        simp only [List.any_eq_false, List.mem_range, beq_iff_eq]
        intro x hx; omega
  have hww : whiteWires (k + kindSp K) (List.range (kindSp K)) (blackOn (kindSp K) (k + kindSp K)) =
      [] := by
    simp only [whiteWires, List.filter_eq_nil_iff, blackOn]
    intro i _
    split_ifs <;> simp
  have hps : List.range (kindSp K) ++ List.range' (kindSp K) k = List.range (k + kindSp K) := by
    have h1 := @List.range'_append_1 0 (kindSp K) k
    rw [Nat.zero_add] at h1
    rw [List.range_eq_range', List.range_eq_range', h1, Nat.add_comm]
  simp only [mc, hcw, hww, List.length_range', hps, canonAt_eq, placeG_id]
  simp [colourW, drawn]

/-- The symmetry of the canonical gate in its controls, from the same
statement for its `mc` form on its own wires. -/
theorem canonSym_of (K : Kind) (k : ℕ)
    (h : ∀ u, kindSp K ≤ u → u + 2 ≤ k + kindSp K →
      Derivable (theory (k + kindSp K))
        (drawn [mc (k + kindSp K) K (List.range (kindSp K)) (blackOn (kindSp K) (k + kindSp K)),
          swAt (k + kindSp K) u])
        (drawn [swAt (k + kindSp K) u,
          mc (k + kindSp K) K (List.range (kindSp K)) (blackOn (kindSp K) (k + kindSp K))])) :
    CanonSym K k := by
  intro u hu hu2
  have hu' := h u hu hu2
  rw [mc_canon] at hu'
  have hs := swsw (k + kindSp K) u hu2
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one] at hu' ⊢
  have h1 := dright (swAt (k + kindSp K) u) hu'
  have h2 := dleft (canonC K k) hs
  rw [mul_one] at h2
  rw [← mul_assoc]
  exact h1.trans (by rw [mul_assoc]; exact h2)

/-- (307) at the canonical position: the symmetry of the box in its controls. -/
theorem canonSym_box (k : ℕ)
    (h307 : ∀ j, 1 ≤ j → j + 2 ≤ k + 1 →
      Derivable (theory (k + 1)) (drawn [mc (k + 1) .box [0] (blackOn 1 (k + 1)), swAt (k + 1) j])
        (drawn [swAt (k + 1) j, mc (k + 1) .box [0] (blackOn 1 (k + 1))])) :
    CanonSym .box k :=
  canonSym_of .box k h307

/-- (313) at the canonical position. -/
theorem canonSym_hg (k : ℕ)
    (h313 : ∀ j, 2 ≤ j → j + 2 ≤ k + 2 →
      Derivable (theory (k + 2)) (drawn [mc (k + 2) .hg [0, 1] (blackOn 2 (k + 2)), swAt (k + 2) j])
        (drawn [swAt (k + 2) j, mc (k + 2) .hg [0, 1] (blackOn 2 (k + 2))])) :
    CanonSym .hg k :=
  canonSym_of .hg k h313

/-- (353) at the canonical position, for `ZX` (`a = false`) and `XZ`. -/
theorem canonSym_zx (k : ℕ) (a : Bool)
    (h353 : ∀ j, 1 ≤ j → j + 2 ≤ k + 1 →
      Derivable (theory (k + 1))
        (drawn [mc (k + 1) (Kind.sgnZX a) [0] (blackOn 1 (k + 1)), swAt (k + 1) j])
        (drawn [swAt (k + 1) j, mc (k + 1) (Kind.sgnZX a) [0] (blackOn 1 (k + 1))])) :
    CanonSym (Kind.sgnZX a) k := by
  cases a
  · exact canonSym_of .zx k h353
  · exact canonSym_of .xz k h353

/-! ## `mc` gates idle on a wire, moved to the top -/

theorem der_of_eq {N : ℕ} {a b : Circ N} (h : a = b) : Derivable (theory N) a b :=
  h ▸ Derivable.refl a

/-- The inverse of `dropW w` on the wires other than `w`. -/
def liftW (w i : ℕ) : ℕ := if i < w then i else i + 1

/-- `mc` reads its controls only on its own wires. -/
theorem mc_congr (N : ℕ) (K : Kind) (tg : List ℕ) {c c' : ℕ → Option Bool}
    (h : ∀ i < N, c i = c' i) : mc N K tg c = mc N K tg c' := by
  have h1 : ctrlWires N tg c = ctrlWires N tg c' := by
    unfold ctrlWires
    refine List.filter_congr (fun i hi => ?_)
    rw [h i (List.mem_range.1 hi)]
  have h2 : whiteWires N tg c = whiteWires N tg c' := by
    unfold whiteWires
    refine List.filter_congr (fun i hi => ?_)
    rw [h i (List.mem_range.1 hi)]
  simp only [mc, h1, h2]

theorem xAt_top (M w : ℕ) (hw : w < M) : xAt (M + 1) w = padTop (xAt M w) :=
  place1_top M w x (by omega)

theorem colourW_top (M : ℕ) (ws : List ℕ) (hws : ∀ w ∈ ws, w < M) (G : Circ M) :
    colourW (M + 1) ws (padTop G) = padTop (colourW M ws G) := by
  have e : ws.map (xAt (M + 1)) = (ws.map (xAt M)).map padTop := by
    rw [List.map_map]
    exact List.map_congr_left (fun w hw => xAt_top M w (hws w hw))
  rw [colourW_eq, colourW_eq, e, drawn_map_padTop, map_mul, map_mul]

/-- An `mc` gate whose top wire is idle is `padTop` of the gate one wire
narrower. -/
theorem mc_top (M : ℕ) (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool)
    (htg : tg.length = kindSp K) (hnd : tg.Nodup) (htgM : ∀ t ∈ tg, t < M) (hcM : c M = none) :
    mc (M + 1) K tg c = padTop (mc M K tg c) := by
  have h1 : ctrlWires (M + 1) tg c = ctrlWires M tg c := by
    unfold ctrlWires
    rw [List.range_succ, List.filter_append]
    simp [hcM]
  have h2 : whiteWires (M + 1) tg c = whiteWires M tg c := by
    unfold whiteWires
    rw [List.range_succ, List.filter_append]
    simp [hcM]
  have hps : ∀ p ∈ tg ++ ctrlWires M tg c, p < M := fun p hp => by
    rcases List.mem_append.1 hp with hp | hp
    · exact htgM p hp
    · simp only [ctrlWires, List.mem_filter, List.mem_range] at hp; exact hp.1
  unfold mc
  rw [h1, h2, canonAt_eq, canonAt_eq,
    placeG_top _ (ctrlWires_nodup M tg c hnd) hps (by simp [htg, Nat.add_comm]),
    colourW_top M _ (fun w hw => by
      simp only [whiteWires, List.mem_filter, List.mem_range] at hw; exact hw.1)]

/-- The swaps `q, q + 1, …, q + d - 1`. -/
def upNet (q d : ℕ) : List ℕ := (List.range d).map (q + ·)

theorem upNet_succ (q d : ℕ) : upNet q (d + 1) = upNet q d ++ [q + d] := by
  simp [upNet, List.range_succ]

theorem pos_upNet (q : ℕ) : ∀ d, pos (upNet q d) q = q + d
  | 0 => rfl
  | d + 1 => by
    rw [upNet_succ, pos_append, pos_upNet q d, pos_cons, pos_nil]
    unfold tau; rw [if_pos rfl]; omega

theorem swW_single (N j : ℕ) : swW N [j] = swAt N j := by simp [swW, circW, drawn, swAt_eq]

/-- Moving an idle wire up by `d` swaps relabels the gate. -/
theorem mc_upNet (M : ℕ) (K : Kind) (q : ℕ) (hqM : q ≤ M) (tg : List ℕ) (c : ℕ → Option Bool)
    (htg : tg.length = kindSp K) (hnd : tg.Nodup) (htgM : ∀ t ∈ tg, t ≤ M) (hcq : c q = none) :
    ∀ d, q + d ≤ M →
      Derivable (theory (M + 1))
        (swW (M + 1) (upNet q d) * mc (M + 1) K tg c * swW (M + 1) (upNet q d).reverse)
        (mc (M + 1) K (tg.map (pos (upNet q d))) (c ∘ pos (upNet q d).reverse))
  | 0, _ => by
    have e1 : tg.map (pos (upNet q 0)) = tg := by
      conv_rhs => rw [← List.map_id tg]
      exact List.map_congr_left (fun _ _ => rfl)
    have e2 : c ∘ pos (upNet q 0).reverse = c := rfl
    rw [e1, e2]
    simpa [upNet, swW_nil] using Derivable.refl (Γ := theory (M + 1)) (mc (M + 1) K tg c)
  | d + 1, hd => by
    have ih := mc_upNet M K q hqM tg c htg hnd htgM hcq d (by omega)
    set ℓ := upNet q d
    have hok : Ok (M + 1) ℓ := fun x hx => by
      simp only [ℓ, upNet, List.mem_map, List.mem_range] at hx
      obtain ⟨e, he, rfl⟩ := hx; omega
    have hinj : Function.Injective (pos ℓ) := pos_injective ℓ
    have hsw := mc_swap (M + 1) (q + d) (by omega) K (tg.map (pos ℓ)) (c ∘ pos ℓ.reverse)
      (by simp [htg]) (hnd.map hinj)
      (fun t ht => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
        exact pos_lt ℓ hok s (by have := htgM s hs; omega))
      (by
        intro ⟨h1, _⟩
        simp only [ctrlWires, List.mem_filter, Function.comp, Bool.and_eq_true] at h1
        have : pos ℓ.reverse (q + d) = q := by rw [← pos_upNet q d, pos_reverse]
        rw [this, hcq] at h1
        simp at h1)
    rw [upNet_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      swW_append, swW_single, swW_cons]
    have e : swAt (M + 1) (q + d) * swW (M + 1) ℓ * mc (M + 1) K tg c *
        (swW (M + 1) ℓ.reverse * swAt (M + 1) (q + d)) =
        swAt (M + 1) (q + d) * (swW (M + 1) ℓ * mc (M + 1) K tg c * swW (M + 1) ℓ.reverse) *
          swAt (M + 1) (q + d) := by simp only [mul_assoc]
    rw [e]
    refine (dright _ (dleft _ ih)).trans ?_
    have e2 : swAt (M + 1) (q + d) * mc (M + 1) K (tg.map (pos ℓ)) (c ∘ pos ℓ.reverse) *
        swAt (M + 1) (q + d) =
        drawn [swAt (M + 1) (q + d), mc (M + 1) K (tg.map (pos ℓ)) (c ∘ pos ℓ.reverse),
          swAt (M + 1) (q + d)] := by simp [drawn, mul_assoc]
    rw [e2]
    have e3 : (tg.map (pos ℓ)).map (tau (q + d)) = tg.map (pos (ℓ ++ [q + d])) := by
      rw [List.map_map]; exact List.map_congr_left (fun t _ => by simp [pos_append])
    have e4 : (c ∘ pos ℓ.reverse) ∘ tau (q + d) = c ∘ pos ((q + d) :: ℓ.reverse) := rfl
    rw [e3, e4] at hsw
    exact hsw

/-- `toTop` for `mc`: a gate idle on wire `q`, conjugated by the swaps
carrying `q` to the top, is `padTop` of the gate on the remaining wires. -/
theorem mc_toTop (M q : ℕ) (hqM : q ≤ M) (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool)
    (htg : tg.length = kindSp K) (hnd : tg.Nodup) (htgM : ∀ t ∈ tg, t ≤ M) (hqt : q ∉ tg)
    (hcq : c q = none) :
    Derivable (theory (M + 1))
      (swW (M + 1) (topNet M q) * mc (M + 1) K tg c * swW (M + 1) (topNet M q).reverse)
      (padTop (mc M K (tg.map (dropW q)) (c ∘ liftW q))) := by
  have e0 : topNet M q = upNet q (M - q) := rfl
  have h := mc_upNet M K q hqM tg c htg hnd htgM hcq (M - q) (by omega)
  rw [← e0] at h
  have hpos : ∀ t ∈ tg, pos (topNet M q) t = dropW q t := fun t ht => by
    rw [pos_topNet M q hqM t (htgM t ht), if_neg (fun (h : t = q) => hqt (h ▸ ht))]
  have e1 : tg.map (pos (topNet M q)) = tg.map (dropW q) := List.map_congr_left hpos
  rw [e1] at h
  refine h.trans (der_of_eq ?_)
  have htg' : ∀ t ∈ tg.map (dropW q), t < M := fun t ht => by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    have := htgM s hs
    have hs' : s ≠ q := fun h => hqt (h ▸ hs)
    simp only [dropW]; split_ifs <;> omega
  have hnd' : (tg.map (dropW q)).Nodup := by
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) hnd
    have ha' : a ≠ q := fun h => hqt (h ▸ ha)
    have hb' : b ≠ q := fun h => hqt (h ▸ hb)
    simp only [dropW] at hab; split_ifs at hab <;> omega
  have hrev : ∀ i ≤ M, pos (topNet M q).reverse i = if i = M then q else liftW q i := by
    intro i hi
    by_cases him : i = M
    · have h1 : pos (topNet M q) q = M := by rw [pos_topNet M q hqM q hqM, if_pos rfl]
      rw [if_pos him, him]
      have h2 := pos_reverse (topNet M q) q
      rw [h1] at h2
      exact h2
    · rw [if_neg him]
      have hl : liftW q i ≤ M := by simp only [liftW]; split_ifs <;> omega
      have hlq : liftW q i ≠ q := by simp only [liftW]; split_ifs <;> omega
      have : pos (topNet M q) (liftW q i) = i := by
        rw [pos_topNet M q hqM _ hl, if_neg hlq]
        simp only [dropW, liftW]; split_ifs <;> omega
      have h2 := pos_reverse (topNet M q) (liftW q i)
      rw [this] at h2
      exact h2
  rw [mc_top M K _ _ (by simp [htg]) hnd' htg' (by
    simp only [Function.comp]; rw [hrev M le_rfl, if_pos rfl, hcq])]
  congr 1
  refine mc_congr M K _ (fun i hi => ?_)
  simp only [Function.comp]
  rw [hrev i (by omega), if_neg (by omega)]

end QCert.RealCliffordCH.Sec8.Net
