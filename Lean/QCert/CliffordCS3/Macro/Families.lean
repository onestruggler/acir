/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Every relation of `Uₙ(ℤ[1/2, i])` over the macro alphabet

The relations (1)–(19) of Bian–Selinger's presentation of `Uₙ(ℤ[1/2, i])`
(`QCert.BianSelingerUn.Rel`), encoded over the macro alphabet (`encW`), are
derivable from the macro axioms (`b1_of`), given the transport table and
one Boolean check per family (the fields of `Checks`), decided for each `n`
by `decide +kernel`:

* (1), (3), (4), (6), (9), (15)–(19) are carried along a path (`pathTo`) from
  the standard instance, a macro axiom (`okStd`);
* (2), (5), (7), (8), (10)–(14) are conjugations by `X_[p,q]`, whose encoding is
  the word of a palindromic path (`okX`).
-/
import QCert.CliffordCS3.Macro.Basic
import QCert.BianSelingerUn.Syntax

namespace QCert.CliffordCS3.Macro

open BianSelingerUn

variable {n : ℕ}

/-- A generator of `Uₙ(ℤ[1/2, i])` by its indices. -/
def toAG : Gen n → AG
  | .X j k _ => .x j k
  | .K j k _ => .k j k
  | .i j => .i j

/-- The encoding of words over the macro alphabet. -/
def encW (D : Data) : Word (Gen n) →* Word ML :=
  FreeMonoid.lift fun y => FreeMonoid.ofList ((toAG y).enc D)

theorem encW_of (D : Data) (y : Gen n) :
    encW D (FreeMonoid.of y) = FreeMonoid.ofList ((toAG y).enc D) := by
  simp [encW]

/-- The palindromic path of `X_[p,q]`. -/
def xpath (D : Data) (p q : ℕ) : List (Fin 7) := (D.xp.getD p []).getD q []

theorem enc_x (D : Data) (p q : ℕ) : (AG.x p q).enc D = pathW (xpath D p q) := rfl

section Checks

variable (D : Data) (m : ℕ) (S : List AG)

/-- The path from the standard indices `s` carries `L = R` to `Lt = Rt`. -/
def okStd (s t : List ℕ) (L R Lt Rt : List AG) : Bool := ok D m S (pathTo D s t) L R Lt Rt

/-- The conjugation by `X_[p,q]` renames `g` to `g'`. -/
def okX (p q : ℕ) (g g' : AG) : Bool := okPal D m S (xpath D p q) g g'

end Checks

/-- The data of the macro alphabet of `Uₙ` and the family checks. -/
structure Checks (D : Data) (n : ℕ) where
  S : List AG
  hinv : TokInv D (n - 1)
  hadj : Adj D (n - 1) S
  /-- The standard instances. -/
  z : ℕ
  s3 : ℕ × ℕ
  s4 : ℕ × ℕ
  s6 : ℕ × ℕ × ℕ
  s9 : ℕ × ℕ × ℕ × ℕ
  s15 : ℕ × ℕ
  s19 : ℕ × ℕ × ℕ × ℕ
  /-- The standard instances are macro axioms. -/
  ax1 : Derivable (MRel D) (FreeMonoid.ofList (encL D [.i z, .i z, .i z, .i z])) 1
  ax3 : Derivable (MRel D) (FreeMonoid.ofList (encL D (List.replicate 8 (.k s3.1 s3.2)))) 1
  ax4 : Derivable (MRel D) (FreeMonoid.ofList (encL D [.i s4.1, .i s4.2]))
    (FreeMonoid.ofList (encL D [.i s4.2, .i s4.1]))
  ax6 : Derivable (MRel D) (FreeMonoid.ofList (encL D [.i s6.1, .k s6.2.1 s6.2.2]))
    (FreeMonoid.ofList (encL D [.k s6.2.1 s6.2.2, .i s6.1]))
  ax9 : Derivable (MRel D) (FreeMonoid.ofList (encL D [.k s9.1 s9.2.1, .k s9.2.2.1 s9.2.2.2]))
    (FreeMonoid.ofList (encL D [.k s9.2.2.1 s9.2.2.2, .k s9.1 s9.2.1]))
  ax15 : Derivable (MRel D) (FreeMonoid.ofList (encL D [.k s15.1 s15.2, .i s15.2, .i s15.2]))
    (FreeMonoid.ofList (encL D [.x s15.1 s15.2, .k s15.1 s15.2]))
  ax16 : Derivable (MRel D) (FreeMonoid.ofList (encL D [.k s15.1 s15.2, .i s15.2, .i s15.2, .i s15.2]))
    (FreeMonoid.ofList (encL D [.i s15.2, .k s15.1 s15.2, .i s15.2, .k s15.1 s15.2]))
  ax17 : Derivable (MRel D) (FreeMonoid.ofList (encL D [.k s15.1 s15.2, .i s15.1, .i s15.2]))
    (FreeMonoid.ofList (encL D [.i s15.1, .i s15.2, .k s15.1 s15.2]))
  ax18 : Derivable (MRel D) (FreeMonoid.ofList (encL D [.k s15.1 s15.2, .k s15.1 s15.2, .i s15.1, .i s15.2])) 1
  ax19 : Derivable (MRel D)
    (FreeMonoid.ofList (encL D [.k s19.1 s19.2.1, .k s19.2.2.1 s19.2.2.2, .k s19.1 s19.2.2.1, .k s19.2.1 s19.2.2.2]))
    (FreeMonoid.ofList (encL D [.k s19.1 s19.2.2.1, .k s19.2.1 s19.2.2.2, .k s19.1 s19.2.1, .k s19.2.2.1 s19.2.2.2]))
  /-- The family checks. -/
  c1 : allBelow n (fun j => okStd D (n - 1) S [z] [j] [.i z, .i z, .i z, .i z] [] [.i j, .i j, .i j, .i j] []) = true
  c2 : allBelow n (fun j => allBelow n fun k => !decide (j < k) ||
    okPal D (n - 1) S (xpath D j k) (.x j k) (.x k j)) = true
  c3 : allBelow n (fun j => allBelow n fun k => !decide (j < k) ||
    okStd D (n - 1) S [s3.1, s3.2] [j, k] (List.replicate 8 (.k s3.1 s3.2)) [] (List.replicate 8 (.k j k)) []) = true
  c4 : allBelow n (fun j => allBelow n fun k => !decide (j ≠ k) ||
    okStd D (n - 1) S [s4.1, s4.2] [j, k] [.i s4.1, .i s4.2] [.i s4.2, .i s4.1] [.i j, .i k] [.i k, .i j]) = true
  c5 : allBelow n (fun j => allBelow n fun k => allBelow n fun l => !decide (k < l ∧ j ≠ k ∧ j ≠ l) ||
    okX D (n - 1) S k l (.i j) (.i j)) = true
  c6 : allBelow n (fun j => allBelow n fun k => allBelow n fun l => !decide (k < l ∧ j ≠ k ∧ j ≠ l) ||
    okStd D (n - 1) S [s6.1, s6.2.1, s6.2.2] [j, k, l] [.i s6.1, .k s6.2.1 s6.2.2]
      [.k s6.2.1 s6.2.2, .i s6.1] [.i j, .k k l] [.k k l, .i j]) = true
  c7 : allBelow n (fun j => allBelow n fun k => !decide (j < k) || allBelow n fun l => allBelow n fun m =>
    !decide (l < m ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m) || okX D (n - 1) S j k (.x l m) (.x l m)) = true
  c8 : allBelow n (fun j => allBelow n fun k => !decide (j < k) || allBelow n fun l => allBelow n fun m =>
    !decide (l < m ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m) || okX D (n - 1) S j k (.k l m) (.k l m)) = true
  c9 : allBelow n (fun j => allBelow n fun k => !decide (j < k) || allBelow n fun l => allBelow n fun m =>
    !decide (l < m ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m) ||
    okStd D (n - 1) S [s9.1, s9.2.1, s9.2.2.1, s9.2.2.2] [j, k, l, m]
      [.k s9.1 s9.2.1, .k s9.2.2.1 s9.2.2.2] [.k s9.2.2.1 s9.2.2.2, .k s9.1 s9.2.1]
      [.k j k, .k l m] [.k l m, .k j k]) = true
  c10 : allBelow n (fun j => allBelow n fun k => !decide (j < k) || okX D (n - 1) S j k (.i j) (.i k)) = true
  c11 : allBelow n (fun j => allBelow n fun k => allBelow n fun l => !decide (j < k ∧ k < l) ||
    okX D (n - 1) S j k (.x j l) (.x k l)) = true
  c12 : allBelow n (fun j => allBelow n fun k => allBelow n fun l => !decide (j < k ∧ k < l) ||
    okX D (n - 1) S k l (.x j k) (.x j l)) = true
  c13 : allBelow n (fun j => allBelow n fun k => allBelow n fun l => !decide (j < k ∧ k < l) ||
    okX D (n - 1) S j k (.k j l) (.k k l)) = true
  c14 : allBelow n (fun j => allBelow n fun k => allBelow n fun l => !decide (j < k ∧ k < l) ||
    okX D (n - 1) S k l (.k j k) (.k j l)) = true
  c15 : allBelow n (fun j => allBelow n fun k => !decide (j < k) ||
    (okStd D (n - 1) S [s15.1, s15.2] [j, k] [.k s15.1 s15.2, .i s15.2, .i s15.2]
      [.x s15.1 s15.2, .k s15.1 s15.2] [.k j k, .i k, .i k] [.x j k, .k j k] &&
    okStd D (n - 1) S [s15.1, s15.2] [j, k] [.k s15.1 s15.2, .i s15.2, .i s15.2, .i s15.2]
      [.i s15.2, .k s15.1 s15.2, .i s15.2, .k s15.1 s15.2] [.k j k, .i k, .i k, .i k]
      [.i k, .k j k, .i k, .k j k] &&
    okStd D (n - 1) S [s15.1, s15.2] [j, k] [.k s15.1 s15.2, .i s15.1, .i s15.2]
      [.i s15.1, .i s15.2, .k s15.1 s15.2] [.k j k, .i j, .i k] [.i j, .i k, .k j k] &&
    okStd D (n - 1) S [s15.1, s15.2] [j, k] [.k s15.1 s15.2, .k s15.1 s15.2, .i s15.1, .i s15.2] []
      [.k j k, .k j k, .i j, .i k] [])) = true
  c19 : allBelow n (fun j => allBelow n fun k => !decide (j < k) || allBelow n fun l => allBelow n fun m =>
    !decide (l < m ∧ j < l ∧ k < m ∧ k ≠ l) ||
    okStd D (n - 1) S [s19.1, s19.2.1, s19.2.2.1, s19.2.2.2] [j, k, l, m]
      [.k s19.1 s19.2.1, .k s19.2.2.1 s19.2.2.2, .k s19.1 s19.2.2.1, .k s19.2.1 s19.2.2.2]
      [.k s19.1 s19.2.2.1, .k s19.2.1 s19.2.2.2, .k s19.1 s19.2.1, .k s19.2.2.1 s19.2.2.2]
      [.k j k, .k l m, .k j l, .k k m] [.k j l, .k k m, .k j k, .k l m]) = true

section Proofs

variable {D : Data} (C : Checks D n)
include C

theorem std_of {s t : List ℕ} {L R Lt Rt : List AG} (h : okStd D (n - 1) C.S s t L R Lt Rt = true)
    (hd : Derivable (MRel D) (FreeMonoid.ofList (encL D L)) (FreeMonoid.ofList (encL D R))) :
    Derivable (MRel D) (FreeMonoid.ofList (encL D Lt)) (FreeMonoid.ofList (encL D Rt)) :=
  of_ok C.hinv C.hadj h hd

theorem x_of {p q : ℕ} {g g' : AG} (h : okX D (n - 1) C.S p q g g' = true) :
    Derivable (MRel D) (FreeMonoid.ofList ((AG.x p q).enc D ++ g.enc D))
      (FreeMonoid.ofList (g'.enc D ++ (AG.x p q).enc D)) :=
  of_okPal C.hinv C.hadj h

theorem sq_of {p q : ℕ} {g g' : AG} (h : okX D (n - 1) C.S p q g g' = true) :
    Derivable (MRel D) (FreeMonoid.ofList ((AG.x p q).enc D ++ (AG.x p q).enc D)) 1 := by
  simp only [okX, okPal, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact pal_sq C.hinv _ h.1.1.1 h.1.2

end Proofs

theorem lt_val {a b : Fin n} (h : a < b) : a.val < b.val := h
theorem ne_val {a b : Fin n} (h : a ≠ b) : a.val ≠ b.val := fun e => h (Fin.ext e)

theorem encW_ofList (D : Data) (l : List (Gen n)) :
    encW D (FreeMonoid.ofList l) = FreeMonoid.ofList (encL D (l.map toAG)) := by
  induction l with
  | nil => rfl
  | cons y l ih => simp [FreeMonoid.ofList_cons, ih, encW_of, encL, FreeMonoid.ofList_append]

theorem encL_two (D : Data) (g h : AG) : encL D [g, h] = g.enc D ++ h.enc D := by simp [encL]

/-- Every relation of `Uₙ(ℤ[1/2, i])` is derivable over the macro alphabet. -/
theorem b1_of {D : Data} (C : Checks D n) :
    ∀ w w', Rel n w w' → Derivable (MRel D) (encW D w) (encW D w') := by
  intro w w' h
  cases h with
  | r1 j =>
    have d := std_of C (allBelow_spec C.c1 j.2) C.ax1
    rw [show (i j ^ 4 : Word (Gen n)) = FreeMonoid.ofList [.i j, .i j, .i j, .i j] from rfl,
      show (1 : Word (Gen n)) = FreeMonoid.ofList [] from rfl, encW_ofList, encW_ofList]
    simpa [toAG] using d
  | r2 j k hjk =>
    have d := sq_of C (imp_spec (allBelow_spec (allBelow_spec C.c2 j.2) k.2) (lt_val hjk))
    rw [show (X j k hjk ^ 2 : Word (Gen n)) = FreeMonoid.ofList [.X j k hjk, .X j k hjk] from rfl,
      show (1 : Word (Gen n)) = FreeMonoid.ofList [] from rfl, encW_ofList, encW_ofList]
    simpa [toAG, encL_two] using d
  | r3 j k hjk =>
    have d := std_of C (imp_spec (allBelow_spec (allBelow_spec C.c3 j.2) k.2) (lt_val hjk)) C.ax3
    rw [show (K j k hjk ^ 8 : Word (Gen n)) = FreeMonoid.ofList (List.replicate 8 (.K j k hjk))
        from rfl, show (1 : Word (Gen n)) = FreeMonoid.ofList [] from rfl, encW_ofList, encW_ofList]
    simpa [toAG] using d
  | r4 j k hjk =>
    have d := std_of C (imp_spec (allBelow_spec (allBelow_spec C.c4 j.2) k.2) (ne_val hjk)) C.ax4
    rw [show (i j * i k : Word (Gen n)) = FreeMonoid.ofList [.i j, .i k] from rfl,
      show (i k * i j : Word (Gen n)) = FreeMonoid.ofList [.i k, .i j] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG] using d
  | r5 j k l hkl hjk hjl =>
    have d := x_of C (imp_spec (allBelow_spec (allBelow_spec (allBelow_spec C.c5 j.2) k.2) l.2)
      ⟨lt_val hkl, ne_val hjk, ne_val hjl⟩)
    rw [show (i j * X k l hkl : Word (Gen n)) = FreeMonoid.ofList [.i j, .X k l hkl] from rfl,
      show (X k l hkl * i j : Word (Gen n)) = FreeMonoid.ofList [.X k l hkl, .i j] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG, encL_two] using d.symm
  | r6 j k l hkl hjk hjl =>
    have d := std_of C (imp_spec (allBelow_spec (allBelow_spec (allBelow_spec C.c6 j.2) k.2) l.2)
      ⟨lt_val hkl, ne_val hjk, ne_val hjl⟩) C.ax6
    rw [show (i j * K k l hkl : Word (Gen n)) = FreeMonoid.ofList [.i j, .K k l hkl] from rfl,
      show (K k l hkl * i j : Word (Gen n)) = FreeMonoid.ofList [.K k l hkl, .i j] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG] using d
  | r7 j k l m hjk hlm hjl hjm hkl hkm =>
    have d := x_of C (imp_spec (allBelow_spec (allBelow_spec (imp_spec (allBelow_spec
      (allBelow_spec C.c7 j.2) k.2) (lt_val hjk)) l.2) m.2)
      ⟨lt_val hlm, ne_val hjl, ne_val hjm, ne_val hkl, ne_val hkm⟩)
    rw [show (X j k hjk * X l m hlm : Word (Gen n)) =
        FreeMonoid.ofList [.X j k hjk, .X l m hlm] from rfl,
      show (X l m hlm * X j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.X l m hlm, .X j k hjk] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG, encL_two] using d
  | r8 j k l m hjk hlm hjl hjm hkl hkm =>
    have d := x_of C (imp_spec (allBelow_spec (allBelow_spec (imp_spec (allBelow_spec
      (allBelow_spec C.c8 j.2) k.2) (lt_val hjk)) l.2) m.2)
      ⟨lt_val hlm, ne_val hjl, ne_val hjm, ne_val hkl, ne_val hkm⟩)
    rw [show (X j k hjk * K l m hlm : Word (Gen n)) =
        FreeMonoid.ofList [.X j k hjk, .K l m hlm] from rfl,
      show (K l m hlm * X j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.K l m hlm, .X j k hjk] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG, encL_two] using d
  | r9 j k l m hjk hlm hjl hjm hkl hkm =>
    have d := std_of C (imp_spec (allBelow_spec (allBelow_spec (imp_spec (allBelow_spec
      (allBelow_spec C.c9 j.2) k.2) (lt_val hjk)) l.2) m.2)
      ⟨lt_val hlm, ne_val hjl, ne_val hjm, ne_val hkl, ne_val hkm⟩) C.ax9
    rw [show (K j k hjk * K l m hlm : Word (Gen n)) =
        FreeMonoid.ofList [.K j k hjk, .K l m hlm] from rfl,
      show (K l m hlm * K j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.K l m hlm, .K j k hjk] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG] using d
  | r10 j k hjk =>
    have d := x_of C (imp_spec (allBelow_spec (allBelow_spec C.c10 j.2) k.2) (lt_val hjk))
    rw [show (i k * X j k hjk : Word (Gen n)) = FreeMonoid.ofList [.i k, .X j k hjk] from rfl,
      show (X j k hjk * i j : Word (Gen n)) = FreeMonoid.ofList [.X j k hjk, .i j] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG, encL_two] using d.symm
  | r11 j k l hjk hkl =>
    have d := x_of C (imp_spec (allBelow_spec (allBelow_spec (allBelow_spec C.c11 j.2) k.2) l.2)
      ⟨lt_val hjk, lt_val hkl⟩)
    rw [show (X k l hkl * X j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.X k l hkl, .X j k hjk] from rfl,
      show (X j k hjk * X j l (hjk.trans hkl) : Word (Gen n)) =
        FreeMonoid.ofList [.X j k hjk, .X j l (hjk.trans hkl)] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG, encL_two] using d.symm
  | r12 j k l hjk hkl =>
    have d := x_of C (imp_spec (allBelow_spec (allBelow_spec (allBelow_spec C.c12 j.2) k.2) l.2)
      ⟨lt_val hjk, lt_val hkl⟩)
    rw [show (X j l (hjk.trans hkl) * X k l hkl : Word (Gen n)) =
        FreeMonoid.ofList [.X j l (hjk.trans hkl), .X k l hkl] from rfl,
      show (X k l hkl * X j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.X k l hkl, .X j k hjk] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG, encL_two] using d.symm
  | r13 j k l hjk hkl =>
    have d := x_of C (imp_spec (allBelow_spec (allBelow_spec (allBelow_spec C.c13 j.2) k.2) l.2)
      ⟨lt_val hjk, lt_val hkl⟩)
    rw [show (K k l hkl * X j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.K k l hkl, .X j k hjk] from rfl,
      show (X j k hjk * K j l (hjk.trans hkl) : Word (Gen n)) =
        FreeMonoid.ofList [.X j k hjk, .K j l (hjk.trans hkl)] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG, encL_two] using d.symm
  | r14 j k l hjk hkl =>
    have d := x_of C (imp_spec (allBelow_spec (allBelow_spec (allBelow_spec C.c14 j.2) k.2) l.2)
      ⟨lt_val hjk, lt_val hkl⟩)
    rw [show (K j l (hjk.trans hkl) * X k l hkl : Word (Gen n)) =
        FreeMonoid.ofList [.K j l (hjk.trans hkl), .X k l hkl] from rfl,
      show (X k l hkl * K j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.X k l hkl, .K j k hjk] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG, encL_two] using d.symm
  | r15 j k hjk =>
    have hc := imp_spec (allBelow_spec (allBelow_spec C.c15 j.2) k.2) (lt_val hjk)
    simp only [Bool.and_eq_true] at hc
    have d := std_of C hc.1.1.1 C.ax15
    rw [show (K j k hjk * i k ^ 2 : Word (Gen n)) =
        FreeMonoid.ofList [.K j k hjk, .i k, .i k] from rfl,
      show (X j k hjk * K j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.X j k hjk, .K j k hjk] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG] using d
  | r16 j k hjk =>
    have hc := imp_spec (allBelow_spec (allBelow_spec C.c15 j.2) k.2) (lt_val hjk)
    simp only [Bool.and_eq_true] at hc
    have d := std_of C hc.1.1.2 C.ax16
    rw [show (K j k hjk * i k ^ 3 : Word (Gen n)) =
        FreeMonoid.ofList [.K j k hjk, .i k, .i k, .i k] from rfl,
      show (i k * K j k hjk * i k * K j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.i k, .K j k hjk, .i k, .K j k hjk] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG] using d
  | r17 j k hjk =>
    have hc := imp_spec (allBelow_spec (allBelow_spec C.c15 j.2) k.2) (lt_val hjk)
    simp only [Bool.and_eq_true] at hc
    have d := std_of C hc.1.2 C.ax17
    rw [show (K j k hjk * i j * i k : Word (Gen n)) =
        FreeMonoid.ofList [.K j k hjk, .i j, .i k] from rfl,
      show (i j * i k * K j k hjk : Word (Gen n)) =
        FreeMonoid.ofList [.i j, .i k, .K j k hjk] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG] using d
  | r18 j k hjk =>
    have hc := imp_spec (allBelow_spec (allBelow_spec C.c15 j.2) k.2) (lt_val hjk)
    simp only [Bool.and_eq_true] at hc
    have d := std_of C hc.2 C.ax18
    rw [show (K j k hjk ^ 2 * i j * i k : Word (Gen n)) =
        FreeMonoid.ofList [.K j k hjk, .K j k hjk, .i j, .i k] from rfl,
      show (1 : Word (Gen n)) = FreeMonoid.ofList [] from rfl, encW_ofList, encW_ofList]
    simpa [toAG] using d
  | r19 j k l m hjk hlm hjl hkm hkl =>
    have d := std_of C (imp_spec (allBelow_spec (allBelow_spec (imp_spec (allBelow_spec
      (allBelow_spec C.c19 j.2) k.2) (lt_val hjk)) l.2) m.2)
      ⟨lt_val hlm, lt_val hjl, lt_val hkm, ne_val hkl⟩) C.ax19
    rw [show (K j k hjk * K l m hlm * K j l hjl * K k m hkm : Word (Gen n)) =
        FreeMonoid.ofList [.K j k hjk, .K l m hlm, .K j l hjl, .K k m hkm] from rfl,
      show (K j l hjl * K k m hkm * K j k hjk * K l m hlm : Word (Gen n)) =
        FreeMonoid.ofList [.K j l hjl, .K k m hkm, .K j k hjk, .K l m hlm] from rfl,
      encW_ofList, encW_ofList]
    simpa [toAG] using d

end QCert.CliffordCS3.Macro
