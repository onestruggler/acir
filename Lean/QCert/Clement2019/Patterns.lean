/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément's relations in Figure 6, one order pattern at a time

`tr` writes a Clément generator over `𝒢ₙ` according to the order of its two
indices, so the image of a relation instance depends on the relative order of
its indices.  A relation of Clément's on `a` indices is a *scheme*: two lists
of raw letters (`RL a`, letters without the distinctness proofs) on the
indices `0, …, a-1`, instantiated at an injective `x : Fin a → Fin n`.  Every
injective `x` is a strictly increasing map after a permutation `p` of
`Fin a` (`exists_sort`, by sorting its image), and `tr` commutes with strictly
increasing maps (`trR_map`), along which Figure 6 derivations move
(`HadamardPi.der_map`).  So a scheme holds in Figure 6 at every instance
once it holds at the `a!` arrangements `p` of `0, …, a-1` (`Good.apply`),
which a table of derivations checked by `decide +kernel` gives
(`good_of_check`).
-/
import QCert.Clement2019.Translate
import QCert.HadamardPi.Check

namespace QCert.Clement2019

open FreeMonoid
open HadamardPi (Fig6 der_map runSteps derive_of)

variable {m n a : ℕ}

/-- Clément's letters without the distinctness proofs. -/
inductive RL (m : ℕ)
  | z (a : Fin m)
  | x (a b : Fin m)
  | h (a b : Fin m)
  deriving DecidableEq

/-- A raw letter moved along a map of indices. -/
def RL.map (f : Fin m → Fin n) : RL m → RL n
  | .z a => .z (f a)
  | .x a b => .x (f a) (f b)
  | .h a b => .h (f a) (f b)

/-- `tr` on raw letters (a degenerate letter `x a a`, `h a a` gives `[]`). -/
def trR : RL m → List (HadamardPi.Gen m)
  | .z a => [.Z a]
  | .x a b => if h : a < b then [.X a b h] else if h' : b < a then [.X b a h'] else []
  | .h a b => if h : a < b then [.H a b h] else
      if h' : b < a then [.X b a h', .H b a h', .X b a h'] else []

/-- `tr` on lists of raw letters. -/
def trL (l : List (RL m)) : List (HadamardPi.Gen m) := l.flatMap trR

/-- A letter as a raw letter. -/
def Gen.raw : Gen n → RL n
  | .Z a => .z a
  | .X a b _ => .x a b
  | .H a b _ => .h a b

theorem trg_raw (g : Gen n) : trg g = ofList (trR g.raw) := by
  cases g with
  | Z a => rfl
  | X a b h =>
    simp only [trg, trR, Gen.raw]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  | H a b h =>
    simp only [trg, trR, Gen.raw]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem tr_ofList (l : List (Gen n)) : tr (ofList l) = ofList (trL (l.map Gen.raw)) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [ofList_cons, map_mul, ih]
    simp only [trL, List.map_cons, List.flatMap_cons, ofList_append]
    rw [show tr (of g) = ofList (trR g.raw) from by simp [tr, trg_raw]]

theorem tr_eq (w : Word (Gen n)) : tr w = ofList (trL (w.toList.map Gen.raw)) := by
  rw [← tr_ofList, ofList_toList]

theorem trR_map (f : Fin m → Fin n) (hf : StrictMono f) (r : RL m) :
    trR (r.map f) = (trR r).map (HadamardPi.Gen.map f hf) := by
  cases r with
  | z a => rfl
  | x a b =>
    simp only [trR, RL.map]
    by_cases h1 : a < b
    · rw [dif_pos h1, dif_pos (hf h1)]; rfl
    · rw [dif_neg h1, dif_neg (fun e => h1 (hf.lt_iff_lt.1 e))]
      by_cases h2 : b < a
      · rw [dif_pos h2, dif_pos (hf h2)]; rfl
      · rw [dif_neg h2, dif_neg (fun e => h2 (hf.lt_iff_lt.1 e))]; rfl
  | h a b =>
    simp only [trR, RL.map]
    by_cases h1 : a < b
    · rw [dif_pos h1, dif_pos (hf h1)]; rfl
    · rw [dif_neg h1, dif_neg (fun e => h1 (hf.lt_iff_lt.1 e))]
      by_cases h2 : b < a
      · rw [dif_pos h2, dif_pos (hf h2)]; rfl
      · rw [dif_neg h2, dif_neg (fun e => h2 (hf.lt_iff_lt.1 e))]; rfl

theorem trL_map (f : Fin m → Fin n) (hf : StrictMono f) (l : List (RL m)) :
    trL (l.map (RL.map f)) = (trL l).map (HadamardPi.Gen.map f hf) := by
  induction l with
  | nil => rfl
  | cons r l ih => simp [trL, List.flatMap_cons, trR_map f hf] at ih ⊢; rw [ih]

theorem RL.map_comp {k : ℕ} (f : Fin m → Fin n) (g : Fin k → Fin m) (r : RL k) :
    (r.map g).map f = r.map (f ∘ g) := by
  cases r <;> rfl

/-- Every injective map is a strictly increasing one after a permutation. -/
theorem exists_sort (x : Fin a → Fin n) (hx : Function.Injective x) :
    ∃ g : Fin a → Fin n, StrictMono g ∧ ∃ p : Fin a → Fin a, Function.Injective p ∧
      ∀ i, x i = g (p i) := by
  classical
  let s : Finset (Fin n) := Finset.univ.image x
  have hs : s.card = a := by
    rw [Finset.card_image_of_injective _ hx]; simp
  refine ⟨fun i => s.orderEmbOfFin hs i, (s.orderEmbOfFin hs).strictMono,
    fun i => (s.orderIsoOfFin hs).symm ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩, ?_, ?_⟩
  · intro i j hij
    have := congrArg (fun y => ((s.orderIsoOfFin hs) y : Fin n)) hij
    simp only [OrderIso.apply_symm_apply] at this
    exact hx this
  · intro i
    dsimp only
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

/-- A scheme holds in Figure 6 at every arrangement of its indices. -/
def Good (L R : List (RL a)) : Prop :=
  ∀ p : Fin a → Fin a, Function.Injective p →
    Derivable Fig6 (ofList (trL (L.map (RL.map p)))) (ofList (trL (R.map (RL.map p))))

/-- A good scheme holds in Figure 6 at every instance. -/
theorem Good.apply {L R : List (RL a)} (hG : Good L R) (x : Fin a → Fin n)
    (hx : Function.Injective x) :
    Derivable Fig6 (ofList (trL (L.map (RL.map x)))) (ofList (trL (R.map (RL.map x)))) := by
  obtain ⟨g, hg, p, hp, hxp⟩ := exists_sort x hx
  have e : RL.map x = RL.map g ∘ RL.map p := by
    funext r; rw [Function.comp_apply, RL.map_comp]; congr 1; funext i; exact hxp i
  have hl : ∀ l : List (RL a), trL (l.map (RL.map x)) =
      (trL (l.map (RL.map p))).map (HadamardPi.Gen.map g hg) := by
    intro l; rw [e, ← List.map_map, trL_map g hg]
  rw [hl, hl]
  exact der_map g hg (hG p hp)

/-- The lists of length `k` over `Fin a`. -/
def tuples (a : ℕ) : ℕ → List (List (Fin a))
  | 0 => [[]]
  | k + 1 => (List.finRange a).flatMap fun i => (tuples a k).map (i :: ·)

theorem mem_tuples : ∀ t : List (Fin a), t ∈ tuples a t.length
  | [] => by simp [tuples]
  | i :: t => by
    simp only [tuples, List.mem_flatMap, List.mem_finRange, List.mem_map,
      true_and]
    exact ⟨i, t, mem_tuples t, rfl⟩

/-- The map `i ↦ t[i]`. -/
def vecOf (t : List (Fin a)) : Fin a → Fin a := fun i => t.getD i i

theorem vecOf_ofFn (p : Fin a → Fin a) : vecOf (List.ofFn p) = p := by
  funext i; simp [vecOf]

/-- The steps the table gives for an arrangement. -/
def look (tbl : List (List (Fin a) × List (HadamardPi.Step a))) (t : List (Fin a)) :
    List (HadamardPi.Step a) :=
  match tbl.find? (fun e => e.1 == t) with
  | some e => e.2
  | none => []

/-- Every arrangement of `0, …, a-1` is derived by the table. -/
def checkTbl (L R : List (RL a)) (tbl : List (List (Fin a) × List (HadamardPi.Step a))) :
    Bool :=
  (tuples a a).all fun t => !decide t.Nodup ||
    runSteps (look tbl t) (trL (L.map (RL.map (vecOf t)))) == some (trL (R.map (RL.map (vecOf t))))

theorem good_of_check (L R : List (RL a)) (tbl : List (List (Fin a) × List (HadamardPi.Step a)))
    (h : checkTbl L R tbl = true) : Good L R := by
  intro p hp
  have ht : List.ofFn p ∈ tuples a a := by
    have := mem_tuples (List.ofFn p); rwa [List.length_ofFn] at this
  have := List.all_eq_true.mp h _ ht
  have hn : (List.ofFn p).Nodup := List.nodup_ofFn.mpr hp
  simp only [hn, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq, vecOf_ofFn] at this
  exact derive_of _ this

end QCert.Clement2019
