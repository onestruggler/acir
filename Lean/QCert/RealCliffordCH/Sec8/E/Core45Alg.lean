/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (45): the algebra

The decoded rule (45) is `T = T'` with `T = a b a w b` and `T' = b w a b a`
(monoid order), every letter an involution, i.e. `T T = 1`.  The facts below
are the steps of the paper's chain (pages 264–269 of arXiv:2602.06644),
regrouped; `alg45` assembles them in any monoid.

* `T = k V`, `V = a e a v e`, with `k` the box white on `1`, `3, …` and black
  on `2`: `w = k v` ((309)), `b = f e` ((310)), `k` passes `a`, `b`, `f`
  passes `a`, `w`, `k`, `b` ((337), (338), (340), (344)).  As `k` passes `V`,
  `T T = V V`.
* `V = P₀₁ X P₀₁`, `X = q h₁ z₀ h₀ z₀ p`: Definition 2.4 in the frames
  `[0, 1]`, `[2, 0]`, `[2, 1]` (`P₀₁`, `P₂₀`, `P₂₁` the `P ⊗ P`), the Klein
  relations (130), (308) for the boxes `v`, `p`, `q`, the merges (309) and the
  box wire moves (274).
* `X X = 1`: `h₁` passes `z₀`, `h₀` ((339), (340)), and `p`, `q` pass
  `h₀`, `h₁`, `z₀` (boxes commute, (308)).
-/
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Common

namespace QCert.RealCliffordCH.Sec8.E

section Alg45

variable {Q : Type*} [Monoid Q]

/-- `x x = 1` and `y y = 1` with `x y = y x` give `(x y) (x y) = 1`. -/
theorem inv_pair_comm {x y : Q} (hx : x * x = 1) (hy : y * y = 1) (hc : Commute x y) :
    (x * y) * (x * y) = 1 := by
  calc (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
    _ = x * (x * y) * y := by rw [hc.eq]
    _ = (x * x) * (y * y) := by simp only [mul_assoc]
    _ = 1 := by rw [hx, hy, one_mul]

/-- Conjugating by an involution: `u (u x u) u = x`. -/
theorem conj_conj {u x : Q} (hu : u * u = 1) : u * (u * x * u) * u = x := by
  calc u * (u * x * u) * u = (u * u) * x * (u * u) := by simp only [mul_assoc]
    _ = x := by rw [hu, one_mul, mul_one]

theorem alg45 {a b w k f v e P01 P20 P21 beta phi zp z z0 z1 y y0 u0 u1 vp p q h0 h1 : Q}
    -- involutions
    (ik : k * k = 1) (ia : a * a = 1) (ib : b * b = 1) (iw : w * w = 1) (i_f : f * f = 1)
    (iy : y * y = 1) (iy0 : y0 * y0 = 1) (iu0 : u0 * u0 = 1) (iu1 : u1 * u1 = 1)
    (iz0 : z0 * z0 = 1) (iz1 : z1 * z1 = 1) (ih0 : h0 * h0 = 1) (ih1 : h1 * h1 = 1)
    (iP01 : P01 * P01 = 1)
    -- the box `k` and the gate `f`
    (ckb : Commute k b) (ckf : Commute k f) (ckw : Commute k w) (cka : Commute k a)
    (mv : k * w = v) (me : f * b = e) (cfw : Commute f w) (cfa : Commute f a) (cfb : Commute f b)
    -- Definition 2.4, Klein, (308), merges and moves
    (fb : b = P01 * beta * P01) (ff : f = P01 * phi * P01) (mzp : phi * beta = zp)
    (fa : a = P20 * y * P20) (kl1 : P20 * P01 = P21) (kl2 : P01 * P20 = P21)
    (cvP : Commute P20 v) (mvv : v = vp) (mvp : y * y0 = vp)
    (mp : u0 * y0 = p) (mq : u1 * y = q) (cpP : Commute p P21) (cqP : Commute q P21)
    (fh0 : h0 = P21 * u0 * P21) (fh1 : h1 = P21 * u1 * P21) (mvz : zp = z) (mz : z1 * z0 = z)
    (cz1h0 : Commute z1 h0) (cz0h1 : Commute z0 h1) (ch0h1 : Commute h0 h1)
    -- boxes commute
    (c1 : Commute y0 u0) (c2 : Commute y0 u1) (c3 : Commute u0 u1) (c4 : Commute y u0)
    (c5 : Commute y u1) (c6 : Commute y y0) (c7 : Commute z0 y0) (c8 : Commute z0 u0)
    (c9 : Commute z0 y) (c10 : Commute z0 u1) (c11 : Commute z1 y0) (c12 : Commute z1 u0)
    (c13 : Commute z0 z1) :
    a * b * a * w * b = b * w * a * b * a := by
  /- Part 3: `X X = 1`. -/
  have pdef : p = u0 * y0 := mp.symm
  have qdef : q = u1 * y := mq.symm
  have cpu0 : Commute p u0 := by rw [pdef]; exact (Commute.refl u0).mul_left c1
  have cpu1 : Commute p u1 := by rw [pdef]; exact c3.mul_left c2
  have cqu0 : Commute q u0 := by rw [qdef]; exact c3.symm.mul_left c4
  have cqu1 : Commute q u1 := by rw [qdef]; exact (Commute.refl u1).mul_left c5
  have cpz0 : Commute p z0 := by rw [pdef]; exact c8.symm.mul_left c7.symm
  have cqz0 : Commute q z0 := by rw [qdef]; exact c10.symm.mul_left c9.symm
  have cph0 : Commute p h0 := by rw [fh0]; exact (cpP.mul_right cpu0).mul_right cpP
  have cph1 : Commute p h1 := by rw [fh1]; exact (cpP.mul_right cpu1).mul_right cpP
  have cqh0 : Commute q h0 := by rw [fh0]; exact (cqP.mul_right cqu0).mul_right cqP
  have cqh1 : Commute q h1 := by rw [fh1]; exact (cqP.mul_right cqu1).mul_right cqP
  have cpq : Commute p q := by
    rw [pdef, qdef]
    exact (c3.mul_right c4.symm).mul_left (c2.mul_right c6.symm)
  have ip : p * p = 1 := by rw [pdef]; exact inv_pair_comm iu0 iy0 c1.symm
  have iq : q * q = 1 := by rw [qdef]; exact inv_pair_comm iu1 iy c5.symm
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = h1 * z0 * h0 * z0 := ⟨_, rfl⟩
  have hY : Y = z0 * h0 * z0 * h1 := by
    have : Commute h1 (z0 * h0 * z0) := (cz0h1.symm.mul_right ch0h1.symm).mul_right cz0h1.symm
    calc Y = h1 * (z0 * h0 * z0) := by simp only [hYdef, mul_assoc]
      _ = z0 * h0 * z0 * h1 := this.eq
  have cpY : Commute p Y := by
    rw [hYdef]; exact ((cph1.mul_right cpz0).mul_right cph0).mul_right cpz0
  have cqY : Commute q Y := by
    rw [hYdef]; exact ((cqh1.mul_right cqz0).mul_right cqh0).mul_right cqz0
  have iY : Y * Y = 1 := by
    calc Y * Y = (h1 * z0 * h0 * z0) * Y := by rw [← hYdef]
      _ = (h1 * z0 * h0 * z0) * (z0 * h0 * z0 * h1) := by rw [← hY]
      _ = h1 * z0 * h0 * (z0 * z0) * h0 * z0 * h1 := by simp only [mul_assoc]
      _ = 1 := by
          rw [iz0, mul_one]
          calc h1 * z0 * h0 * h0 * z0 * h1 = h1 * z0 * (h0 * h0) * z0 * h1 := by
                simp only [mul_assoc]
            _ = h1 * (z0 * z0) * h1 := by rw [ih0, mul_one]; simp only [mul_assoc]
            _ = 1 := by rw [iz0, mul_one, ih1]
  have hX : (q * h1 * z0 * h0 * z0 * p) * (q * h1 * z0 * h0 * z0 * p) = 1 := by
    have e1 : q * h1 * z0 * h0 * z0 * p = Y * (q * p) := by
      calc q * h1 * z0 * h0 * z0 * p = q * Y * p := by simp only [hYdef, mul_assoc]
        _ = Y * (q * p) := by rw [cqY.eq, mul_assoc]
    rw [e1]
    have cY : Commute (q * p) Y := cqY.mul_left cpY
    calc Y * (q * p) * (Y * (q * p)) = Y * ((q * p) * Y) * (q * p) := by simp only [mul_assoc]
      _ = Y * (Y * (q * p)) * (q * p) := by rw [cY.eq]
      _ = (Y * Y) * ((q * p) * (q * p)) := by simp only [mul_assoc]
      _ = 1 := by rw [iY, inv_pair_comm iq ip cpq.symm, one_mul]
  /- Part 2: `V = P₀₁ X P₀₁`. -/
  have ee : e = P01 * z * P01 := by
    calc e = f * b := me.symm
      _ = P01 * phi * (P01 * P01) * beta * P01 := by rw [ff, fb]; simp only [mul_assoc]
      _ = P01 * (phi * beta) * P01 := by rw [iP01, mul_one]; simp only [mul_assoc]
      _ = P01 * z * P01 := by rw [mzp, mvz]
  have P20e : P20 = P01 * P21 := by
    calc P20 = (P01 * P01) * P20 := by rw [iP01, one_mul]
      _ = P01 * P21 := by rw [mul_assoc, kl2]
  have yv : y * v = y0 := by
    calc y * v = y * (y * y0) := by rw [mvv, mvp]
      _ = y0 := by rw [← mul_assoc, iy, one_mul]
  have yeq : y = u1 * q := by rw [qdef, ← mul_assoc, iu1, one_mul]
  have y0eq : y0 = u0 * p := by rw [pdef, ← mul_assoc, iu0, one_mul]
  have hPy : P21 * y * P21 = h1 * q := by
    calc P21 * y * P21 = P21 * u1 * (q * P21) := by rw [yeq]; simp only [mul_assoc]
      _ = P21 * u1 * (P21 * q) := by rw [cqP.eq]
      _ = h1 * q := by rw [fh1]; simp only [mul_assoc]
  have hPy0 : P21 * y0 * P21 = h0 * p := by
    calc P21 * y0 * P21 = P21 * u0 * (p * P21) := by rw [y0eq]; simp only [mul_assoc]
      _ = P21 * u0 * (P21 * p) := by rw [cpP.eq]
      _ = h0 * p := by rw [fh0]; simp only [mul_assoc]
  have czp : Commute z p := by
    rw [← mz, pdef]
    exact (c12.mul_right c11).mul_left (c8.mul_right c7)
  have zhz : z * h0 * z = z0 * h0 * z0 := by
    rw [← mz]
    calc z1 * z0 * h0 * (z1 * z0) = z1 * z0 * (h0 * z1) * z0 := by simp only [mul_assoc]
      _ = z1 * (z0 * z1) * h0 * z0 := by rw [← cz1h0.eq]; simp only [mul_assoc]
      _ = z1 * (z1 * z0) * h0 * z0 := by rw [c13.eq]
      _ = z0 * h0 * z0 := by rw [← mul_assoc z1 z1 z0, iz1, one_mul]
  have hV : a * e * a * v * e = P01 * (q * h1 * z0 * h0 * z0 * p) * P01 := by
    calc a * e * a * v * e
        = P20 * y * (P20 * P01) * z * (P01 * P20) * y * (P20 * v) * P01 * z * P01 := by
          rw [fa, ee]; simp only [mul_assoc]
      _ = P20 * y * P21 * z * P21 * (y * v) * (P20 * P01) * z * P01 := by
          conv_lhs => rw [kl1, kl2, cvP.eq]
          simp only [mul_assoc]
      _ = P01 * (P21 * y * P21) * z * (P21 * y0 * P21) * z * P01 := by
          conv_lhs => rw [yv, kl1, P20e]
          simp only [mul_assoc]
      _ = P01 * (h1 * q) * z * (h0 * p) * z * P01 := by rw [hPy, hPy0]
      _ = P01 * (h1 * q) * z * h0 * (p * z) * P01 := by simp only [mul_assoc]
      _ = P01 * (q * h1) * (z * h0 * z) * p * P01 := by
          rw [← czp.eq, ← cqh1.eq]; simp only [mul_assoc]
      _ = P01 * (q * h1 * z0 * h0 * z0 * p) * P01 := by rw [zhz]; simp only [mul_assoc]
  have iV : (a * e * a * v * e) * (a * e * a * v * e) = 1 := by
    rw [hV]
    calc P01 * (q * h1 * z0 * h0 * z0 * p) * P01 * (P01 * (q * h1 * z0 * h0 * z0 * p) * P01)
        = P01 * (q * h1 * z0 * h0 * z0 * p) * (P01 * P01) * (q * h1 * z0 * h0 * z0 * p) * P01 := by
          simp only [mul_assoc]
      _ = P01 * ((q * h1 * z0 * h0 * z0 * p) * (q * h1 * z0 * h0 * z0 * p)) * P01 := by
          rw [iP01, mul_one]; simp only [mul_assoc]
      _ = 1 := by rw [hX, mul_one, iP01]
  /- Part 1: `T = k V`, `k` passes `V`. -/
  have wkv : w = k * v := by rw [← mv, ← mul_assoc, ik, one_mul]
  have bfe : b = f * e := by rw [← me, ← mul_assoc, i_f, one_mul]
  have cfe : Commute f e := by rw [← me]; exact (Commute.refl f).mul_right cfb
  have cfv : Commute f v := by rw [← mv]; exact ckf.symm.mul_right cfw
  have cke : Commute k e := by rw [← me]; exact ckf.mul_right ckb
  have ckv : Commute k v := by rw [← mv]; exact (Commute.refl k).mul_right ckw
  have hT : a * b * a * w * b = k * (a * e * a * v * e) := by
    have c1' : Commute k (a * b * a) := (cka.mul_right ckb).mul_right cka
    have c2' : Commute f (e * a * v) := (cfe.mul_right cfa).mul_right cfv
    calc a * b * a * w * b = (a * b * a * k) * v * b := by rw [wkv]; simp only [mul_assoc]
      _ = k * (a * b * a * v * b) := by rw [← c1'.eq]; simp only [mul_assoc]
      _ = k * (a * f * (e * a * v * f) * e) := by rw [bfe]; simp only [mul_assoc]
      _ = k * (a * (f * f) * e * a * v * e) := by rw [← c2'.eq]; simp only [mul_assoc]
      _ = k * (a * e * a * v * e) := by rw [i_f, mul_one]
  have ckV : Commute k (a * e * a * v * e) :=
    (((cka.mul_right cke).mul_right cka).mul_right ckv).mul_right cke
  have iT : (a * b * a * w * b) * (a * b * a * w * b) = 1 := by
    rw [hT]
    calc k * (a * e * a * v * e) * (k * (a * e * a * v * e))
        = k * ((a * e * a * v * e) * k) * (a * e * a * v * e) := by simp only [mul_assoc]
      _ = (k * k) * ((a * e * a * v * e) * (a * e * a * v * e)) := by
          rw [← ckV.eq]; simp only [mul_assoc]
      _ = 1 := by rw [ik, iV, one_mul]
  have iTT : (b * w * a * b * a) * (a * b * a * w * b) = 1 := by
    calc (b * w * a * b * a) * (a * b * a * w * b)
        = b * w * a * b * (a * a) * b * a * w * b := by simp only [mul_assoc]
      _ = b * w * a * (b * b) * a * w * b := by rw [ia, mul_one]; simp only [mul_assoc]
      _ = b * w * (a * a) * w * b := by rw [ib, mul_one]; simp only [mul_assoc]
      _ = b * (w * w) * b := by rw [ia, mul_one]; simp only [mul_assoc]
      _ = 1 := by rw [iw, mul_one, ib]
  calc a * b * a * w * b = ((b * w * a * b * a) * (a * b * a * w * b)) * (a * b * a * w * b) := by
        rw [iTT, one_mul]
    _ = (b * w * a * b * a) * ((a * b * a * w * b) * (a * b * a * w * b)) := by
        simp only [mul_assoc]
    _ = b * w * a * b * a := by rw [iT, mul_one]

end Alg45

end QCert.RealCliffordCH.Sec8.E
