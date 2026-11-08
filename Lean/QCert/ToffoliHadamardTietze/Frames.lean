/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-Tietze`: frames

Translation of `Frames.agda`: Coxeter words of `S₈` as circuits (`p`), the
adjacent transpositions `s0`, …, `s6`, the check that two of them are equal
circuits when they permute the states alike (`checked`), and some word
algebra for moving circuits past frames.  Coxeter words are `CoxeterFrames`'
lists of indices (see `Permutation`), so `s0 ++ s1` is the Agda's `s0 • s1`,
and a word must be checked to be one of `S₈` (`Valid 7`).
-/
import QCert.ToffoliHadamardTietze.Permutation

namespace QCert.ToffoliHadamardTietze

open QCert.ToffoliHadamardRS.CoxeterFrames

/-- Coxeter words of `S₈`. -/
abbrev PWord := CW

/-- The adjacent transpositions. -/
def s0 : PWord := [0]
def s1 : PWord := [1]
def s2 : PWord := [2]
def s3 : PWord := [3]
def s4 : PWord := [4]
def s5 : PWord := [5]
def s6 : PWord := [6]

/-- A Coxeter word as a circuit. -/
abbrev p (w : PWord) : Word Gen := Pc adjacent w

theorem checked (u v : PWord) (hu : Valid 7 u) (hv : Valid 7 v)
    (e : ∀ x, x < 8 → act u x = act v x) : p u ≈ p v :=
  permutation_complete hu hv e

/-! ## Word algebra -/

/-- The class of a word modulo the relations. -/
abbrev cls (w : Word Gen) : (conGen Rel).Quotient := (conGen Rel).mk' w

theorem cls_eq {w v : Word Gen} : cls w = cls v ↔ w ≈ v := (conGen Rel).eq

theorem cls_mul (w v : Word Gen) : cls (w * v) = cls w * cls v := map_mul _ w v

theorem cls_one : cls 1 = 1 := map_one _

theorem commute_product {q a b : Word Gen} (ea : a * q ≈ q * a) (eb : b * q ≈ q * b) :
    a * b * q ≈ q * (a * b) := by
  have ha := cls_eq.2 ea; have hb := cls_eq.2 eb
  simp only [cls_mul] at ha hb
  apply cls_eq.1; simp only [cls_mul]
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

theorem forget_frame {a b c i : Word Gen} (e : a * b ≈ c * a) (inverse : a * i ≈ 1) :
    a * b * i ≈ c := by
  have he := cls_eq.2 e; have hi := cls_eq.2 inverse
  simp only [cls_mul, cls_one] at he hi
  apply cls_eq.1; simp only [cls_mul]
  rw [he, mul_assoc, hi, mul_one]

theorem move_product {q a a' b b' : Word Gen} (ea : q * a ≈ a' * q) (eb : q * b ≈ b' * q) :
    q * (a * b) ≈ a' * b' * q := by
  have ha := cls_eq.2 ea; have hb := cls_eq.2 eb
  simp only [cls_mul] at ha hb
  apply cls_eq.1; simp only [cls_mul]
  rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]

theorem move_compose {a b x y z : Word Gen} (ea : a * y ≈ z * a) (eb : b * x ≈ y * b) :
    a * b * x ≈ z * (a * b) := by
  have ha := cls_eq.2 ea; have hb := cls_eq.2 eb
  simp only [cls_mul] at ha hb
  apply cls_eq.1; simp only [cls_mul]
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

end QCert.ToffoliHadamardTietze
