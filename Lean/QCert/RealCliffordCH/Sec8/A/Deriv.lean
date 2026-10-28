/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Derivations with the equations of Figure 8, on lists of letters

`D8 n l l'`: the words of the letter lists `l` and `l'` are equal by the
equations of Figure 8; `DH n l l'` the same using only the equations
between Hadamard-free words (`Fig8H`), which embed (`DH.toD8`) and are
sound for signed permutations.  Steps are applied inside any context
(`DR.ctx`), and derivations chain with `calc`.  `sg n j` is the letter
`(-1)_[j] X_[j,j+1]` and `tg n j` its inverse `(-1)_[j+1] X_[j,j+1]`
(Equation (29)).
-/
import QCert.RealCliffordCH.Sec8.Fig8

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- Derivability between letter lists under a relation on words. -/
def DR {X : Type*} (Γ : WRel X) (l l' : List X) : Prop :=
  Derivable Γ (FreeMonoid.ofList l) (FreeMonoid.ofList l')

namespace DR

variable {X : Type*} {Γ : WRel X} {l l' l'' a b c d : List X}

theorem refl (l : List X) : DR Γ l l := Derivable.refl _

theorem rfl' (h : l = l') : DR Γ l l' := h ▸ refl l

theorem symm (h : DR Γ l l') : DR Γ l' l := Derivable.symm h

theorem trans (h : DR Γ l l') (h' : DR Γ l' l'') : DR Γ l l'' := Derivable.trans h h'

theorem ax (h : Γ (FreeMonoid.ofList l) (FreeMonoid.ofList l')) : DR Γ l l' := Derivable.of h

theorem append (h1 : DR Γ a b) (h2 : DR Γ c d) : DR Γ (a ++ c) (b ++ d) := by
  unfold DR; rw [FreeMonoid.ofList_append, FreeMonoid.ofList_append]; exact h1.mul h2

theorem ctx (p s : List X) (h : DR Γ l l') : DR Γ (p ++ l ++ s) (p ++ l' ++ s) :=
  (append (refl p) h).append (refl s)

theorem left (p : List X) (h : DR Γ l l') : DR Γ (p ++ l) (p ++ l') := append (refl p) h

theorem right (s : List X) (h : DR Γ l l') : DR Γ (l ++ s) (l' ++ s) := append h (refl s)

theorem cons (x : X) (h : DR Γ l l') : DR Γ (x :: l) (x :: l') := left [x] h

/-- A derivation under a smaller relation is one under a larger. -/
theorem mono {Δ : WRel X} (hΓ : ∀ u v, Γ u v → Δ u v) (h : DR Γ l l') : DR Δ l l' :=
  (Con.conGen_le fun u v huv => ConGen.Rel.of _ _ (hΓ u v huv) :
    conGen Γ ≤ conGen Δ) h

end DR

instance {X : Type*} {Γ : WRel X} : Trans (DR Γ) (DR Γ) (DR Γ) := ⟨DR.trans⟩

/-- Figure 8 derivability between letter lists. -/
abbrev D8 (n : ℕ) : List (PG (2 ^ n)) → List (PG (2 ^ n)) → Prop := DR (Fig8 n)

/-- A letter of `𝒫_N` other than `H_[a,b]H_[c,d]`. -/
def PG.HF {N : ℕ} : PG N → Prop
  | .hh _ _ _ _ => False
  | _ => True

/-- The equations of Figure 8 between Hadamard-free words. -/
def Fig8H (n : ℕ) : WRel (PG (2 ^ n)) :=
  fun u v => Fig8 n u v ∧ (∀ x ∈ u.toList, x.HF) ∧ ∀ x ∈ v.toList, x.HF

/-- Derivability by the equations of Figure 8 between Hadamard-free words. -/
abbrev DH (n : ℕ) : List (PG (2 ^ n)) → List (PG (2 ^ n)) → Prop := DR (Fig8H n)

theorem DH.toD8 {l l' : List (PG (2 ^ n))} (h : DH n l l') : D8 n l l' :=
  DR.mono (fun _ _ h => h.1) h

/-- An equation of Figure 8 between Hadamard-free lists. -/
theorem DH.ax' {l l' : List (PG (2 ^ n))} (h : Fig8 n (wordOf l) (wordOf l'))
    (hl : ∀ x ∈ l, x.HF) (hl' : ∀ x ∈ l', x.HF) : DH n l l' :=
  DR.ax ⟨h, by simpa [wordOf] using hl, by simpa [wordOf] using hl'⟩

/-- `(-1)_[j] X_[j,j+1]`. -/
abbrev sg (n j : ℕ) : PG (2 ^ n) := Zx n j j (j + 1)

/-- `(-1)_[j+1] X_[j,j+1]`, the inverse of `sg n j`. -/
abbrev tg (n j : ℕ) : PG (2 ^ n) := Zx n (j + 1) j (j + 1)

/-! ## The equations of Figure 8 used for the Hadamard-free fragment -/

section Axioms

variable (n)

theorem e20 {a : ℕ} (ha : a < 2 ^ n) : DH n [Zz n a a] [] :=
  DH.ax' (Fig8.r20 a ha) (by simp [Zz, PG.HF]) (by simp)

theorem e21 {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) : DH n [Zz n a b] [Zz n b a] :=
  DH.ax' (Fig8.r21 a b ha hb) (by simp [Zz, PG.HF]) (by simp [Zz, PG.HF])

theorem e22 {a b c : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) :
    DH n [Zz n a b, Zz n b c] [Zz n a c] :=
  DH.ax' (Fig8.r22 a b c ha hb hc) (by simp [Zz, PG.HF]) (by simp [Zz, PG.HF])

theorem e23 {a : ℕ} (ha : a + 1 < 2 ^ n) : DH n [Zz n a (a + 1)] [sg n a, sg n a] :=
  DH.ax' (Fig8.r23 a ha) (by simp [Zz, PG.HF]) (by simp [Zx, PG.HF])

theorem e24 {a : ℕ} (ha : a + 2 < 2 ^ n) :
    DH n [sg n a, sg n (a + 1), sg n a] [sg n (a + 1), sg n a, sg n (a + 1)] :=
  DH.ax' (Fig8.r24 a ha) (by simp [Zx, PG.HF]) (by simp [Zx, PG.HF])

theorem e29 {a : ℕ} (ha : a + 1 < 2 ^ n) : DH n [sg n a, tg n a] [] :=
  DH.ax' (Fig8.r29 a ha) (by simp [Zx, PG.HF]) (by simp)

theorem e31 {a c : ℕ} (ha : a + 1 < 2 ^ n) (hc : c < 2 ^ n) (h1 : c ≠ a) (h2 : c ≠ a + 1) :
    DH n [Zz n (a + 1) c, sg n a] [sg n a, Zz n a c] :=
  DH.ax' (Fig8.r31 a c ha hc h1 h2) (by simp [Zz, Zx, PG.HF]) (by simp [Zz, Zx, PG.HF])

theorem e32 {a b : ℕ} (hab : a + 1 < b) (hb : b + 1 < 2 ^ n) :
    DH n [sg n a, sg n b] [sg n b, sg n a] :=
  DH.ax' (Fig8.r32 a b hab hb) (by simp [Zx, PG.HF]) (by simp [Zx, PG.HF])

theorem e25 {a c : ℕ} (hac : a + 1 < c) (hc : c < 2 ^ n) (hodd : (c - a) % 2 = 1) :
    DH n [Zx n a a c] [tg n a, Zx n (a + 1) (a + 1) c, sg n a] :=
  DH.ax' (Fig8.r25 a c hac hc hodd) (by simp [Zx, PG.HF]) (by simp [Zx, PG.HF])

theorem e26 {a c : ℕ} (hac : a + 1 < c) (hc : c < 2 ^ n) (hodd : (c - a) % 2 = 1) :
    DH n [Zx n c a c] [tg n a, Zx n c (a + 1) c, sg n a] :=
  DH.ax' (Fig8.r26 a c hac hc hodd) (by simp [Zx, PG.HF]) (by simp [Zx, PG.HF])

theorem e27 {a c : ℕ} (hac : a + 1 < c) (hc : c < 2 ^ n) (heven : (c - a) % 2 = 0) :
    DH n [Zx n a a c] [Zx n (c - 1) (c - 1) c, Zx n a a (c - 1), Zx n c (c - 1) c] :=
  DH.ax' (Fig8.r27 a c hac hc heven) (by simp [Zx, PG.HF]) (by simp [Zx, PG.HF])

theorem e28 {a c : ℕ} (hac : a + 1 < c) (hc : c < 2 ^ n) (heven : (c - a) % 2 = 0) :
    DH n [Zx n c a c] [Zx n (c - 1) (c - 1) c, Zx n (c - 1) a (c - 1), Zx n c (c - 1) c] :=
  DH.ax' (Fig8.r28 a c hac hc heven) (by simp [Zx, PG.HF]) (by simp [Zx, PG.HF])

theorem e30 {a b c : ℕ} (hb : b < 2 ^ n) (ha : a < 2 ^ n) (hc : c < 2 ^ n) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) : DH n [Zx n c a b] [Zz n c a, Zx n a a b] :=
  DH.ax' (Fig8.r30 a b c hb ha hc hab hca hcb) (by simp [Zx, PG.HF]) (by simp [Zz, Zx, PG.HF])

theorem e33 {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) :
    DH n [Zx n b a b] [Zx n b b a] :=
  DH.ax' (Fig8.r33 a b ha hb hab) (by simp [Zx, PG.HF]) (by simp [Zx, PG.HF])

theorem e34 {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
    (hab : a ≠ b) (hcd : c ≠ d) : DH n [Xx n a b c d] [Zx n a a b, Zx n b c d] :=
  DH.ax' (Fig8.r34 a b c d ha hb hc hd hab hcd) (by simp [Xx, PG.HF]) (by simp [Zx, PG.HF])

end Axioms

end QCert.RealCliffordCH.Sec8
