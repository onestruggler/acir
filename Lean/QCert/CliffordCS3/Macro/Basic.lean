/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The macro alphabet for `Uₙ(ℤ[1/2, i])`

Hypothesis (b) of the Reidemeister–Schreier theorem is checked through an
intermediate alphabet (as in the authors' Step 2, and as in
`QCert.ToffoliHadamard.Macro`): the *tokens* `T d` are the transpositions of
consecutive points `g d, g (d + 1)` of a Gray path `g` of the basis states,
and the *atoms* `Z = i_[z]`, `K = K_[a, z]` sit at the last two points
`a = g (n - 2)`, `z = g (n - 1)`.  A one- or two-level generator is
encoded (`AG.enc`) as an atom conjugated by a token word (a *frame*), and
`X_[p,q]` as a token word of the transposition `(p q)`; the two-level
matrix `K` is encoded for every ordered pair `(p, q)` (`AG.k p q`), so that
every token renames every generator (`AG.act`).

`MRel D`: the macro axioms of the data `D` (the Coxeter relations of the
tokens, the atoms commuting with the tokens of their stabilisers, and one
standard instance of each relation family).  Given the transport table
(`Adj D`: conjugating an encoding by a token encodes the renamed
generator), conjugation by the word of a path renames a relation
(`transport_rel`), which carries a standard instance to every instance.
-/
import QCert.Presentation
import QCert.CliffordT2.FastRewrite

namespace QCert.CliffordCS3.Macro

/-- The macro letters: tokens `T d` (`d < 7`) and the atoms `Z`, `K`. -/
inductive ML : Type
  | T (d : Fin 7)
  | Z
  | K
  deriving DecidableEq, Repr

/-- The digit of a macro letter (for `QCert.FastRewrite`). -/
def mcode : ML → ℕ
  | .T d => d.val + 1
  | .Z => 8
  | .K => 9

theorem mcode_bounds : ∀ a, 0 < mcode a ∧ mcode a < 16 := by
  intro a; cases a with
  | T d => simp only [mcode]; omega
  | Z => decide
  | K => decide

theorem mcode_inj : Function.Injective mcode := by
  intro a b h
  cases a <;> cases b <;> simp only [mcode, Nat.add_right_cancel_iff, ML.T.injEq] at h ⊢ <;>
    first | exact Fin.ext h | rfl | omega

/-- A one- or two-level generator by its indices: `i_[p]`, `X_[p,q]`, and the
two-level `K` on the ordered pair `(p, q)`. -/
inductive AG : Type
  | i (p : ℕ)
  | x (p q : ℕ)
  | k (p q : ℕ)
  deriving DecidableEq, Repr

/-- The data of a macro alphabet. -/
structure Data where
  /-- The Gray path. -/
  gray : List ℕ
  /-- The frame of `i_[p]`: a token word sending `z` to `p`. -/
  fz : List (List ML)
  /-- The frame of `K` on `(p, q)`: a token word sending `a, z` to `p, q`. -/
  fk : List (List (List ML))
  /-- A palindromic path of the transposition `(p q)` (its word `pathW` encodes `X_[p,q]`). -/
  xp : List (List (List (Fin 7)))
  /-- The macro axioms. -/
  ax : List (List ML × List ML)

namespace Data

variable (D : Data)

/-- The transposition `(a b)`. -/
def swapP (a b p : ℕ) : ℕ := if p = a then b else if p = b then a else p

/-- The token `T d` on points. -/
def tp (d : ℕ) (p : ℕ) : ℕ := swapP (D.gray.getD d 0) (D.gray.getD (d + 1) 0) p

end Data

/-- The word of a path `d₁, …, dₘ` (`T d₁` applied first): `T dₘ ⋯ T d₁`. -/
def pathW : List (Fin 7) → List ML
  | [] => []
  | d :: P => pathW P ++ [.T d]

/-- The encoding of a generator over the macro alphabet. -/
def AG.enc (D : Data) : AG → List ML
  | .i p => (D.fz.getD p []) ++ [.Z] ++ (D.fz.getD p []).reverse
  | .x p q => pathW ((D.xp.getD p []).getD q [])
  | .k p q => ((D.fk.getD p []).getD q []) ++ [.K] ++ ((D.fk.getD p []).getD q []).reverse

/-- A token renaming the indices of a generator. -/
def AG.act (D : Data) (d : ℕ) : AG → AG
  | .i p => .i (D.tp d p)
  | .x p q => .x (D.tp d p) (D.tp d q)
  | .k p q => .k (D.tp d p) (D.tp d q)

/-- The macro axioms as a relation. -/
inductive MRel (D : Data) : WRel ML
  | ax {e : List ML × List ML} : e ∈ D.ax → MRel D (FreeMonoid.ofList e.1) (FreeMonoid.ofList e.2)

/-- The rule of a macro axiom. -/
def axRule (D : Data) (e : List ML × List ML) (h : e ∈ D.ax) : Rule (MRel D) :=
  ⟨e.1, e.2, Derivable.of (MRel.ax h)⟩

/-- A path applied to the indices of a generator (`d₁` first). -/
def AG.actPath (D : Data) : List (Fin 7) → AG → AG
  | [], g => g
  | d :: P, g => AG.actPath D P (g.act D d)

/-- The encoding of a list of generators. -/
def encL (D : Data) (l : List AG) : List ML := l.flatMap (AG.enc D)

section Transport

variable {D : Data}

theorem derivable_middle {Γ : WRel ML} {l r : List ML}
    (h : Derivable Γ (FreeMonoid.ofList l) (FreeMonoid.ofList r)) (p q : List ML) :
    Derivable Γ (FreeMonoid.ofList (p ++ l ++ q)) (FreeMonoid.ofList (p ++ r ++ q)) := by
  simp only [FreeMonoid.ofList_append]
  exact (h.mul_left _).mul_right _

/-- Every token is an involution (`T d T d ≈ ε`, a macro axiom), for the
tokens used. -/
def TokInv (D : Data) (n : ℕ) : Prop :=
  ∀ d : Fin 7, d.val < n → Derivable (MRel D) (FreeMonoid.ofList [.T d, .T d]) 1

/-- `l · rev l ≈ ε` for a word of involutive tokens. -/
theorem tw_cancel {n : ℕ} (hinv : TokInv D n) (l : List ML)
    (hl : ∀ x ∈ l, ∃ d : Fin 7, d.val < n ∧ x = .T d) :
    Derivable (MRel D) (FreeMonoid.ofList (l ++ l.reverse)) 1 := by
  induction l with
  | nil => simp; rfl
  | cons x l ih =>
    obtain ⟨d, hd, rfl⟩ := hl x (by simp)
    have h1 := derivable_middle (Γ := MRel D) (ih (fun y hy => hl y (by simp [hy]))) [.T d] [.T d]
    have e1 : [ML.T d] ++ (l ++ l.reverse) ++ [.T d] = .T d :: l ++ (.T d :: l).reverse := by simp
    rw [e1] at h1
    refine h1.trans ?_
    simpa using hinv d hd

theorem pathW_T {n : ℕ} (P : List (Fin 7)) (hP : ∀ d ∈ P, d.val < n) :
    ∀ x ∈ pathW P, ∃ d : Fin 7, d.val < n ∧ x = .T d := by
  induction P with
  | nil => simp [pathW]
  | cons d P ih =>
    intro x hx
    simp only [pathW, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih (fun i hi => hP i (by simp [hi])) x hx
    · exact ⟨d, hP d (by simp), rfl⟩

theorem pathW_cancel {n : ℕ} (hinv : TokInv D n) (P : List (Fin 7)) (hP : ∀ d ∈ P, d.val < n) :
    Derivable (MRel D) (FreeMonoid.ofList (pathW P ++ (pathW P).reverse)) 1 :=
  tw_cancel hinv _ (pathW_T P hP)

theorem pathW_cancel' {n : ℕ} (hinv : TokInv D n) (P : List (Fin 7)) (hP : ∀ d ∈ P, d.val < n) :
    Derivable (MRel D) (FreeMonoid.ofList ((pathW P).reverse ++ pathW P)) 1 := by
  have := tw_cancel hinv (pathW P).reverse (by
    intro x hx; exact pathW_T P hP x (List.mem_reverse.1 hx))
  simpa using this

/-- The transport table: conjugating the encoding of a generator of `S` by a
token encodes the renamed generator, which is again in `S`. -/
def Adj (D : Data) (n : ℕ) (S : List AG) : Prop :=
  ∀ d : Fin 7, d.val < n → ∀ g ∈ S, g.act D d ∈ S ∧
    Derivable (MRel D) (FreeMonoid.ofList ([.T d] ++ g.enc D ++ [.T d]))
      (FreeMonoid.ofList ((g.act D d).enc D))

theorem transport {n : ℕ} {S : List AG} (hadj : Adj D n S) :
    ∀ (P : List (Fin 7)) (g : AG), g ∈ S → (∀ d ∈ P, d.val < n) →
    Derivable (MRel D) (FreeMonoid.ofList (pathW P ++ g.enc D ++ (pathW P).reverse))
      (FreeMonoid.ofList ((g.actPath D P).enc D)) := by
  intro P
  induction P with
  | nil => intro g _ _; simp [pathW, AG.actPath]; rfl
  | cons d P ih =>
    intro g hg hP
    have hd : d.val < n := hP d (by simp)
    have h1 := derivable_middle (hadj d hd g hg).2 (pathW P) (pathW P).reverse
    have e1 : pathW P ++ ([.T d] ++ g.enc D ++ [.T d]) ++ (pathW P).reverse =
        pathW (d :: P) ++ g.enc D ++ (pathW (d :: P)).reverse := by simp [pathW]
    rw [e1] at h1
    exact h1.trans (ih (g.act D d) (hadj d hd g hg).1 (fun i hi => hP i (by simp [hi])))

theorem actPath_mem {n : ℕ} {S : List AG} (hadj : Adj D n S) :
    ∀ (P : List (Fin 7)) (g : AG), g ∈ S → (∀ d ∈ P, d.val < n) → g.actPath D P ∈ S := by
  intro P
  induction P with
  | nil => intro g hg _; exact hg
  | cons d P ih =>
    intro g hg hP
    exact ih _ (hadj d (hP d (by simp)) g hg).1 (fun i hi => hP i (by simp [hi]))

theorem conj_list {n : ℕ} {S : List AG} (hinv : TokInv D n) (hadj : Adj D n S)
    (P : List (Fin 7)) (hP : ∀ d ∈ P, d.val < n) : ∀ l : List AG, (∀ g ∈ l, g ∈ S) →
    Derivable (MRel D) (FreeMonoid.ofList (encL D (l.map (AG.actPath D P))))
      (FreeMonoid.ofList (pathW P ++ encL D l ++ (pathW P).reverse)) := by
  intro l
  induction l with
  | nil =>
    intro _
    simpa [encL] using (pathW_cancel hinv P hP).symm
  | cons g l ih =>
    intro hl
    have hg := hl g (by simp)
    have h1 := (transport hadj P g hg hP).symm
    have h2 := ih (fun g' hg' => hl g' (by simp [hg']))
    have h3 := h1.mul h2
    simp only [← FreeMonoid.ofList_append] at h3
    refine (by simpa [encL] using h3 : Derivable (MRel D) _ _).trans ?_
    have h4 := derivable_middle (pathW_cancel' hinv P hP) (pathW P ++ g.enc D)
      (encL D l ++ (pathW P).reverse)
    simpa [encL] using h4

/-- A relation carried along a path. -/
theorem transport_rel {n : ℕ} {S : List AG} (hinv : TokInv D n) (hadj : Adj D n S)
    (P : List (Fin 7)) (hP : ∀ d ∈ P, d.val < n) (l r : List AG) (hv : ∀ g ∈ l ++ r, g ∈ S)
    (h : Derivable (MRel D) (FreeMonoid.ofList (encL D l)) (FreeMonoid.ofList (encL D r))) :
    Derivable (MRel D) (FreeMonoid.ofList (encL D (l.map (AG.actPath D P))))
      (FreeMonoid.ofList (encL D (r.map (AG.actPath D P)))) := by
  have hl := conj_list hinv hadj P hP l (fun g hg => hv g (by simp [hg]))
  have hr := conj_list hinv hadj P hP r (fun g hg => hv g (by simp [hg]))
  have hm := derivable_middle h (pathW P) (pathW P).reverse
  exact hl.trans (hm.trans hr.symm)

/-- `P` carries the relation `L = R` to `Lt = Rt`. -/
def ok (D : Data) (n : ℕ) (S : List AG) (P : List (Fin 7)) (L R Lt Rt : List AG) : Bool :=
  P.all (fun d => decide (d.val < n)) && (L ++ R).all (fun g => S.contains g) &&
    L.map (AG.actPath D P) == Lt && R.map (AG.actPath D P) == Rt

theorem of_ok {n : ℕ} {S : List AG} (hinv : TokInv D n) (hadj : Adj D n S)
    {P : List (Fin 7)} {L R Lt Rt : List AG} (hok : ok D n S P L R Lt Rt = true)
    (h : Derivable (MRel D) (FreeMonoid.ofList (encL D L)) (FreeMonoid.ofList (encL D R))) :
    Derivable (MRel D) (FreeMonoid.ofList (encL D Lt)) (FreeMonoid.ofList (encL D Rt)) := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at hok
  obtain ⟨⟨⟨hP, hv⟩, rfl⟩, rfl⟩ := hok
  exact transport_rel hinv hadj P hP L R (fun g hg => hv g hg) h

/-- Conjugation by a palindromic path renames a generator. -/
theorem pal {n : ℕ} {S : List AG} (hinv : TokInv D n) (hadj : Adj D n S)
    (P : List (Fin 7)) (hP : ∀ d ∈ P, d.val < n) (hpal : (pathW P).reverse = pathW P)
    (g : AG) (hg : g ∈ S) :
    Derivable (MRel D) (FreeMonoid.ofList (pathW P ++ g.enc D))
      (FreeMonoid.ofList ((g.actPath D P).enc D ++ pathW P)) := by
  have ht := transport hadj P g hg hP
  rw [hpal] at ht
  have hc : Derivable (MRel D) (FreeMonoid.ofList (pathW P ++ pathW P)) 1 := by
    have := pathW_cancel hinv P hP
    rwa [hpal] at this
  have h1 := derivable_middle hc (pathW P ++ g.enc D) []
  have h2 := derivable_middle ht [] (pathW P)
  simp only [List.nil_append, List.append_nil] at h1 h2
  rw [← List.append_assoc] at h1
  exact h1.symm.trans (by simpa using h2)

/-- `P` is a palindromic path renaming `g` to `g'`. -/
def okPal (D : Data) (n : ℕ) (S : List AG) (P : List (Fin 7)) (g g' : AG) : Bool :=
  P.all (fun d => decide (d.val < n)) && S.contains g && (pathW P).reverse == pathW P &&
    g.actPath D P == g'

theorem of_okPal {n : ℕ} {S : List AG} (hinv : TokInv D n) (hadj : Adj D n S)
    {P : List (Fin 7)} {g g' : AG} (h : okPal D n S P g g' = true) :
    Derivable (MRel D) (FreeMonoid.ofList (pathW P ++ g.enc D))
      (FreeMonoid.ofList (g'.enc D ++ pathW P)) := by
  simp only [okPal, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨hP, hg⟩, hpal⟩, rfl⟩ := h
  exact pal hinv hadj P hP hpal g hg

/-- A palindromic path squares to the identity. -/
theorem pal_sq {n : ℕ} (hinv : TokInv D n) (P : List (Fin 7)) (hP : ∀ d ∈ P, d.val < n)
    (hpal : (pathW P).reverse = pathW P) :
    Derivable (MRel D) (FreeMonoid.ofList (pathW P ++ pathW P)) 1 := by
  have := pathW_cancel hinv P hP
  rwa [hpal] at this

end Transport

/-! ## Paths by bubble sort, in the positions of the Gray path -/

/-- The position of a point on the Gray path. -/
def Data.pos (D : Data) (p : ℕ) : ℕ := D.gray.idxOf p

/-- Where each point goes: the `i`-th index of `s` to the `i`-th index of `t`, the
other points to the other targets in order. -/
def arrange (N : ℕ) (s t : List ℕ) : List ℕ :=
  let free := (List.range N).filter (· ∉ s)
  let freeT := (List.range N).filter (· ∉ t)
  (List.range N).map fun p =>
    match s.idxOf? p with
    | some i => t.getD i 0
    | none => freeT.getD (free.idxOf p) 0

/-- One pass of bubble sort, carrying the largest element `a` seen so far, from
position `i`: the new list and the swaps. -/
def bpass (a : ℕ) : List ℕ → ℕ → List ℕ × List ℕ
  | [], _ => ([a], [])
  | b :: rest, i =>
    if b < a then
      let r := bpass a rest (i + 1)
      (b :: r.1, i :: r.2)
    else
      let r := bpass b rest (i + 1)
      (a :: r.1, r.2)

/-- One pass over a list. -/
def bpass0 : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | a :: l => bpass a l 0

/-- The swaps of `k` passes of bubble sort. -/
def bubble : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | k + 1, l => (bpass0 l).2 ++ bubble k (bpass0 l).1

/-- A path of tokens taking the points `s` to `t`: bubble sort of the arrangement in
Gray positions. -/
def pathTo (D : Data) (s t : List ℕ) : List (Fin 7) :=
  let N := D.gray.length
  let perm := arrange N s t
  let l := (List.range N).map fun q => D.pos (perm.getD (D.gray.getD q 0) 0)
  (bubble N l).map fun d => if h : d < 7 then ⟨d, h⟩ else 0


/-! ## Checking the tables -/

/-- `p a` for every `a < n`. -/
def allBelow (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

theorem allBelow_spec {n : ℕ} {p : ℕ → Bool} (h : allBelow n p = true) {a : ℕ} (ha : a < n) :
    p a = true := by
  simp only [allBelow, List.all_eq_true, List.mem_range] at h
  exact h a ha

theorem imp_spec {p : Prop} [Decidable p] {b : Bool} (h : (!decide p || b) = true) (hp : p) :
    b = true := by
  simpa [hp] using h

/-- The transport table, checked: for every token and generator, a rule with the
right sides. -/
def adjOK (D : Data) (n : ℕ) (S : List AG) (tab : List (Fin 7 × AG × Rule (MRel D))) : Bool :=
  (List.finRange 7).all fun d => !(decide (d.val < n)) || S.all fun g =>
    S.contains (g.act D d) && tab.any fun e =>
      e.1 == d && e.2.1 == g && e.2.2.lhs == [ML.T d] ++ g.enc D ++ [ML.T d] &&
        e.2.2.rhs == (g.act D d).enc D

theorem adj_of_ok {D : Data} {n : ℕ} {S : List AG} {tab : List (Fin 7 × AG × Rule (MRel D))}
    (h : adjOK D n S tab = true) : Adj D n S := by
  intro d hd g hg
  simp only [adjOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at h
  rcases h d with h | h
  · omega
  · have h2 := h g hg
    simp only [Bool.and_eq_true, List.contains_iff_mem, List.any_eq_true, beq_iff_eq] at h2
    obtain ⟨hm, ⟨e, -, ⟨⟨⟨-, -⟩, hl⟩, hr⟩⟩⟩ := h2
    refine ⟨hm, ?_⟩
    have := e.2.2.sound
    rwa [hl, hr] at this

/-- Every token used is an involution by a macro axiom. -/
def invOK (D : Data) (n : ℕ) : Bool :=
  (List.finRange 7).all fun d => !(decide (d.val < n)) || D.ax.contains ([ML.T d, ML.T d], [])

theorem tokInv_of_ok {D : Data} {n : ℕ} (h : invOK D n = true) : TokInv D n := by
  intro d hd
  simp only [invOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, not_lt, List.contains_iff_mem] at h
  rcases h d with h | h
  · omega
  · exact Derivable.of (MRel.ax h)

end QCert.CliffordCS3.Macro
