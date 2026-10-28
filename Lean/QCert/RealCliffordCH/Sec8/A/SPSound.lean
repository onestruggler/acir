/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The Hadamard-free equations of Figure 8 hold for signed permutations

To compute, Hadamard-free letters are described by their indices as
natural numbers (`NL`), with the signed permutation on `ℕ` (`permL`,
`negL`, transpositions `swN`); for indices below `2ⁿ` this is the signed
permutation of the letters (`spW_NL`).  Every equation of Figure 8 between
Hadamard-free words then holds for signed permutations by a case analysis
on `ℕ` (`spW_sound`), and so does every derivation `DH` (`DH.spW`).
-/
import QCert.RealCliffordCH.Sec8.A.SP

namespace QCert.RealCliffordCH.Sec8

theorem ix_val {n a : ℕ} (h : a < 2 ^ n) : (ix n a : ℕ) = a := Nat.mod_eq_of_lt h

/-- The transposition of `a` and `b` on `ℕ`. -/
def swN (a b x : ℕ) : ℕ := if x = a then b else if x = b then a else x

/-- A Hadamard-free letter with natural-number indices. -/
inductive NL
  | zz (a c : ℕ)
  | zx (a c d : ℕ)
  | xx (a b c d : ℕ)

namespace NL

/-- The letter of `𝒫_{2ⁿ}`. -/
def toPG (n : ℕ) : NL → PG (2 ^ n)
  | zz a c => Zz n a c
  | zx a c d => Zx n a c d
  | xx a b c d => Xx n a b c d

/-- The indices are below `2ⁿ`. -/
def Bd (n : ℕ) : NL → Prop
  | zz a c => a < 2 ^ n ∧ c < 2 ^ n
  | zx a c d => a < 2 ^ n ∧ c < 2 ^ n ∧ d < 2 ^ n
  | xx a b c d => a < 2 ^ n ∧ b < 2 ^ n ∧ c < 2 ^ n ∧ d < 2 ^ n

def perm : NL → ℕ → ℕ
  | zz _ _ => id
  | zx _ c d => swN c d
  | xx a b c d => fun x => swN a b (swN c d x)

def neg : NL → ℕ → Bool
  | zz a c => fun x => if x = a then (if x = c then false else true) else (if x = c then true else false)
  | zx a c d => fun x => if swN c d x = a then true else false
  | xx _ _ _ _ => fun _ => false

end NL

def permL : List NL → ℕ → ℕ
  | [] => id
  | x :: l => fun j => x.perm (permL l j)

def negL : List NL → ℕ → Bool
  | [] => fun _ => false
  | x :: l => fun j => if x.neg (permL l j) then !negL l j else negL l j

variable {n : ℕ}

theorem swN_lt {a b x : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hx : x < 2 ^ n) :
    swN a b x < 2 ^ n := by
  unfold swN; split_ifs <;> assumption

theorem swap_val {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (j : Fin (2 ^ n)) :
    (Equiv.swap (ix n a) (ix n b) j : ℕ) = swN a b j := by
  rw [Equiv.swap_apply_def, swN]
  have e : ∀ c (hc : c < 2 ^ n), (j = ix n c ↔ (j : ℕ) = c) := fun c hc => by
    rw [Fin.ext_iff, ix_val hc]
  by_cases h1 : (j : ℕ) = a
  · rw [if_pos ((e a ha).2 h1), if_pos h1, ix_val hb]
  · rw [if_neg (fun h => h1 ((e a ha).1 h)), if_neg h1]
    by_cases h2 : (j : ℕ) = b
    · rw [if_pos ((e b hb).2 h2), if_pos h2, ix_val ha]
    · rw [if_neg (fun h => h2 ((e b hb).1 h)), if_neg h2]

theorem perm_lt {x : NL} (hx : x.Bd n) {j : ℕ} (hj : j < 2 ^ n) : x.perm j < 2 ^ n := by
  cases x with
  | zz a c => exact hj
  | zx a c d => exact swN_lt hx.2.1 hx.2.2 hj
  | xx a b c d => exact swN_lt hx.1 hx.2.1 (swN_lt hx.2.2.1 hx.2.2.2 hj)

theorem spL_NL {x : NL} (hx : x.Bd n) (j : Fin (2 ^ n)) :
    ((spL (x.toPG n)).perm j : ℕ) = x.perm j ∧ (spL (x.toPG n)).neg j = x.neg j := by
  cases x with
  | zz a c =>
    refine ⟨rfl, ?_⟩
    simp only [NL.toPG, Zz, spL, NL.neg, Fin.ext_iff, ix_val hx.1, ix_val hx.2]
    split_ifs <;> simp_all
  | zx a c d =>
    refine ⟨swap_val hx.2.1 hx.2.2 j, ?_⟩
    simp only [NL.toPG, Zx, spL, NL.neg, Fin.ext_iff, ix_val hx.1, swap_val hx.2.1 hx.2.2]
    split_ifs <;> simp_all
  | xx a b c d =>
    refine ⟨?_, rfl⟩
    simp only [NL.toPG, Xx, spL, NL.perm, Function.comp]
    rw [swap_val hx.1 hx.2.1, swap_val hx.2.2.1 hx.2.2.2]

theorem spW_NL {l : List NL} (hl : ∀ x ∈ l, x.Bd n) (j : Fin (2 ^ n)) :
    ((spW (wordOf (l.map (NL.toPG n)))).perm j : ℕ) = permL l j ∧
      (spW (wordOf (l.map (NL.toPG n)))).neg j = negL l j := by
  induction l generalizing j with
  | nil => exact ⟨rfl, rfl⟩
  | cons x l ih =>
    have ih' := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    rw [List.map_cons, spW_wordOf, List.map_cons, List.prod_cons, ← spW_wordOf]
    obtain ⟨h1, h2⟩ := ih' j
    set k := (spW (wordOf (l.map (NL.toPG n)))).perm j
    have hk : k = ⟨permL l j, h1 ▸ k.2⟩ := Fin.ext h1
    obtain ⟨e1, e2⟩ := spL_NL (hl x (by simp)) k
    refine ⟨?_, ?_⟩
    · rw [SP.mul_perm, e1, h1]; rfl
    · rw [SP.mul_neg, e2, h2, h1]; simp only [negL]
      cases x.neg (permL l j) <;> cases negL l j <;> rfl

/-- Two lists of letters with the same signed permutation on `ℕ` below `2ⁿ`
have the same signed permutation. -/
theorem spW_eq_of_NL {l l' : List NL} (hl : ∀ x ∈ l, x.Bd n) (hl' : ∀ x ∈ l', x.Bd n)
    (h : ∀ j < 2 ^ n, permL l j = permL l' j ∧ negL l j = negL l' j) :
    spW (wordOf (l.map (NL.toPG n))) = spW (wordOf (l'.map (NL.toPG n))) := by
  apply SP.ext <;> funext j
  · apply Fin.ext; rw [(spW_NL hl j).1, (spW_NL hl' j).1, (h j j.2).1]
  · rw [(spW_NL hl j).2, (spW_NL hl' j).2, (h j j.2).2]

/-! ## Soundness of the Hadamard-free equations -/

/-- The indices of a list of `NL` letters are below `2ⁿ`. -/
macro "bd_tac" : tactic => `(tactic| (simp [NL.Bd] <;> omega))

/-- Evaluate both signed permutations at `j`, the relevant equalities of `j`
being decided. -/
macro "nl_eval" : tactic => `(tactic| (constructor <;> (try simp (disch := omega) only [permL, negL, NL.perm, NL.neg, swN, if_pos, if_neg, id, Bool.not_true, Bool.not_false, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true]) <;> first | rfl | omega | (exfalso; omega) | (split_ifs <;> first | rfl | omega | (exfalso; omega))))

theorem snd_r20 {a : ℕ} (ha : a < 2 ^ n) :
    spW (wordOf ([.zz a a].map (NL.toPG n))) =
      spW (wordOf ([].map (NL.toPG n))) :=
  spW_eq_of_NL (by bd_tac) (by bd_tac) (fun j hj => by nl_eval)

theorem snd_r21 {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    spW (wordOf ([.zz a b].map (NL.toPG n))) =
      spW (wordOf ([.zz b a].map (NL.toPG n))) :=
  spW_eq_of_NL (by bd_tac) (by bd_tac)
      (fun j hj => by nl_eval)

theorem snd_r22 {a b c : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) :
    spW (wordOf ([.zz a b, .zz b c].map (NL.toPG n))) =
      spW (wordOf ([.zz a c].map (NL.toPG n))) :=
  spW_eq_of_NL (by bd_tac) (by bd_tac)
      (fun j hj => by nl_eval)

theorem snd_r23 {a : ℕ} (ha : a + 1 < 2 ^ n) :
    spW (wordOf ([.zz a (a + 1)].map (NL.toPG n))) =
      spW (wordOf ([.zx a a (a + 1), .zx a a (a + 1)].map (NL.toPG n))) :=
  spW_eq_of_NL
      (by bd_tac) (by bd_tac)
      (fun j hj => by by_cases h1 : j = a <;> by_cases h2 : j = a + 1 <;> nl_eval)

theorem snd_r24 {a : ℕ} (ha : a + 2 < 2 ^ n) :
    spW (wordOf ([.zx a a (a + 1), .zx (a + 1) (a + 1) (a + 2), .zx a a (a + 1)].map (NL.toPG n))) =
      spW (wordOf ([.zx (a + 1) (a + 1) (a + 2), .zx a a (a + 1), .zx (a + 1) (a + 1) (a + 2)].map (NL.toPG n))) :=
  spW_eq_of_NL
      (by bd_tac) (by bd_tac) (fun j hj => by
        by_cases h1 : j = a <;> by_cases h2 : j = a + 1 <;> by_cases h3 : j = a + 2 <;> nl_eval)

theorem snd_r25 {a c : ℕ} (hac : a + 1 < c) (hc : c < 2 ^ n) :
    spW (wordOf ([.zx a a c].map (NL.toPG n))) =
      spW (wordOf ([.zx (a + 1) a (a + 1), .zx (a + 1) (a + 1) c, .zx a a (a + 1)].map (NL.toPG n))) :=
  spW_eq_of_NL
      (by bd_tac) (by bd_tac) (fun j hj => by
        by_cases h1 : j = a <;> by_cases h2 : j = a + 1 <;> by_cases h3 : j = c <;> nl_eval)

theorem snd_r26 {a c : ℕ} (hac : a + 1 < c) (hc : c < 2 ^ n) :
    spW (wordOf ([.zx c a c].map (NL.toPG n))) =
      spW (wordOf ([.zx (a + 1) a (a + 1), .zx c (a + 1) c, .zx a a (a + 1)].map (NL.toPG n))) :=
  spW_eq_of_NL
      (by bd_tac) (by bd_tac) (fun j hj => by
        by_cases h1 : j = a <;> by_cases h2 : j = a + 1 <;> by_cases h3 : j = c <;> nl_eval)

theorem snd_r27 {a c : ℕ} (hac : a + 1 < c) (hc : c < 2 ^ n) :
    spW (wordOf ([.zx a a c].map (NL.toPG n))) =
      spW (wordOf ([.zx (c - 1) (c - 1) c, .zx a a (c - 1), .zx c (c - 1) c].map (NL.toPG n))) :=
  spW_eq_of_NL
      (by bd_tac) (by bd_tac) (fun j hj => by
        by_cases h1 : j = a <;> by_cases h2 : j = c - 1 <;> by_cases h3 : j = c <;> nl_eval)

theorem snd_r28 {a c : ℕ} (hac : a + 1 < c) (hc : c < 2 ^ n) :
    spW (wordOf ([.zx c a c].map (NL.toPG n))) =
      spW (wordOf ([.zx (c - 1) (c - 1) c, .zx (c - 1) a (c - 1), .zx c (c - 1) c].map (NL.toPG n))) :=
  spW_eq_of_NL
      (by bd_tac) (by bd_tac) (fun j hj => by
        by_cases h1 : j = a <;> by_cases h2 : j = c - 1 <;> by_cases h3 : j = c <;> nl_eval)

theorem snd_r29 {a : ℕ} (ha : a + 1 < 2 ^ n) :
    spW (wordOf ([.zx a a (a + 1), .zx (a + 1) a (a + 1)].map (NL.toPG n))) =
      spW (wordOf ([].map (NL.toPG n))) :=
  spW_eq_of_NL
      (by bd_tac) (by bd_tac)
      (fun j hj => by by_cases h1 : j = a <;> by_cases h2 : j = a + 1 <;> nl_eval)

theorem snd_r30 {a b c : ℕ} (hb : b < 2 ^ n) (ha : a < 2 ^ n) (hc : c < 2 ^ n) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) :
    spW (wordOf ([.zx c a b].map (NL.toPG n))) =
      spW (wordOf ([.zz c a, .zx a a b].map (NL.toPG n))) :=
  spW_eq_of_NL (by bd_tac) (by bd_tac)
      (fun j hj => by nl_eval)

theorem snd_r31 {a c : ℕ} (ha : a + 1 < 2 ^ n) (hc : c < 2 ^ n) (hca : c ≠ a) (hca1 : c ≠ a + 1) :
    spW (wordOf ([.zz (a + 1) c, .zx a a (a + 1)].map (NL.toPG n))) =
      spW (wordOf ([.zx a a (a + 1), .zz a c].map (NL.toPG n))) :=
  spW_eq_of_NL
      (by bd_tac) (by bd_tac) (fun j hj => by
        by_cases h1 : j = a <;> by_cases h2 : j = a + 1 <;> by_cases h3 : j = c <;> nl_eval)

theorem snd_r32 {a b : ℕ} (hab : a + 1 < b) (hb : b + 1 < 2 ^ n) :
    spW (wordOf ([.zx a a (a + 1), .zx b b (b + 1)].map (NL.toPG n))) =
      spW (wordOf ([.zx b b (b + 1), .zx a a (a + 1)].map (NL.toPG n))) :=
  spW_eq_of_NL (by bd_tac) (by bd_tac) (fun j hj => by
        by_cases h1 : j = a <;> by_cases h2 : j = a + 1 <;> by_cases h3 : j = b <;>
          by_cases h4 : j = b + 1 <;> nl_eval)

theorem snd_r33 {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) :
    spW (wordOf ([.zx b a b].map (NL.toPG n))) =
      spW (wordOf ([.zx b b a].map (NL.toPG n))) :=
  spW_eq_of_NL (by bd_tac) (by bd_tac)
      (fun j hj => by nl_eval)

theorem snd_r34 {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
    (hab : a ≠ b) (hcd : c ≠ d) :
    spW (wordOf ([.xx a b c d].map (NL.toPG n))) =
      spW (wordOf ([.zx a a b, .zx b c d].map (NL.toPG n))) :=
  spW_eq_of_NL (by bd_tac) (by bd_tac)
      (fun j hj => by nl_eval)

/-- The equations of Figure 8 between Hadamard-free words hold for signed
permutations. -/
theorem spW_sound {u v : Word (PG (2 ^ n))} (h : Fig8H n u v) : spW u = spW v := by
  obtain ⟨h, hu, hv⟩ := h
  cases h with
  | r20 a ha => exact snd_r20 ha
  | r21 a b ha hb => exact snd_r21 ha hb
  | r22 a b c ha hb hc => exact snd_r22 ha hb hc
  | r23 a ha => exact snd_r23 ha
  | r24 a ha => exact snd_r24 ha
  | r25 a c hac hc hodd => exact snd_r25 hac hc
  | r26 a c hac hc hodd => exact snd_r26 hac hc
  | r27 a c hac hc heven => exact snd_r27 hac hc
  | r28 a c hac hc heven => exact snd_r28 hac hc
  | r29 a ha => exact snd_r29 ha
  | r30 a b c hb ha hc hab hca hcb => exact snd_r30 hb ha hc hab hca hcb
  | r31 a c ha hc hca hca1 => exact snd_r31 ha hc hca hca1
  | r32 a b hab hb => exact snd_r32 hab hb
  | r33 a b ha hb hab => exact snd_r33 ha hb hab
  | r34 a b c d ha hb hc hd hab hcd => exact snd_r34 ha hb hc hd hab hcd
  | _ => exfalso; simp [wordOf, Zz, Zx, Xx, Hh, PG.HF] at hu

/-- Derivations between Hadamard-free words preserve the signed permutation. -/
theorem DH.spW {l l' : List (PG (2 ^ n))} (h : DH n l l') : spW (wordOf l) = spW (wordOf l') :=
  derivable_sound (sem := spL) (fun _ _ huv => spW_sound huv) h

end QCert.RealCliffordCH.Sec8
