/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.7 (Lemmas D.12–D.13): the interface of package (v)

The commutation properties of multi-controlled gates that Appendix E uses,
stated on `N` wires with completeness on fewer wires as a hypothesis, in
the conventions of `MC` (see `PLAN.md`).  In Lemma D.13 the controls `Λˣ`,
`Λʸ` are colourings `x`, `y` of the top wires `k, …, N - 1` (`colOn k N`),
the half-black dots of the figures are Boolean parameters `c₁, c₂, …`
(`ctlAt`), and "`x ≠ y`" is `DiffOn k N x y`.  Every statement here was
checked numerically against the definitions at `N = 3, …, 6` (scratch
`r87/iface.py`).  They are stated, not yet proved: package (v) of `PLAN.md`
replaces each `sorry` by its proof and keeps the statements.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E319
import QCert.RealCliffordCH.Sec8.D.N13.Low
import QCert.RealCliffordCH.Sec8.D.N13.E345
import QCert.RealCliffordCH.Sec8.D.N13.E337
import QCert.RealCliffordCH.Sec8.D.N13.LowHg
import QCert.RealCliffordCH.Sec8.D.N13.LowHg338
import QCert.RealCliffordCH.Sec8.D.N13.E338Merge
import QCert.RealCliffordCH.Sec8.D.N13.E344t
import QCert.RealCliffordCH.Sec8.D.N13.E333
import QCert.RealCliffordCH.Sec8.D.N13.E346
import QCert.RealCliffordCH.Sec8.D.N13.Low342
import QCert.RealCliffordCH.Sec8.D.N13.Low339W4
import QCert.RealCliffordCH.Sec8.D.N13.Low344W4
import QCert.RealCliffordCH.Sec8.D.N13.Low342W4
import QCert.RealCliffordCH.Sec8.D.N13.E351t

namespace QCert.RealCliffordCH.Sec8.D

open Circuit


/-! ## Lemma D.12 -/

/-- (315): `X` on the box wire commutes with the box. -/
theorem eq315 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [xAt N 0, Bx N]) (drawn [Bx N, xAt N 0]) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have h := eq308 (k + 1) hN ih 1 le_rfl (by omega) x
  have e : atBot (k + 1) (x : Circ 1) = xAt (k + 1) 0 := (Net.pad_atBot1 k x).symm
  rw [e] at h
  exact h

/-- (316): `X` on the box wire commutes with the multi-controlled `H`. -/
theorem eq316 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [xAt N 0, mc N .hg [0, 1] (blackOn 2 N)])
      (drawn [mc N .hg [0, 1] (blackOn 2 N), xAt N 0]) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have h := eq314 (k + 1) hN ih 1 le_rfl (by omega) x
  have e : atBot (k + 1) (x : Circ 1) = xAt (k + 1) 0 := (Net.pad_atBot1 k x).symm
  rw [e] at h
  exact h

/-- (317): the multi-controlled `ZX` and `XZ` are inverse. -/
theorem eq317 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    Derivable (theory N) (drawn [mc N .zx [0] (colOn 1 N x), mc N .xz [0] (colOn 1 N x)]) 1 ∧
    Derivable (theory N) (drawn [mc N .xz [0] (colOn 1 N x), mc N .zx [0] (colOn 1 N x)]) 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 + 1 := ⟨N - 2, by omega⟩
  have hc : ∀ i, (colOn 1 (m + 1 + 1) x i).isSome = true ↔ 1 ≤ i ∧ i < (m + 1) + 1 := by
    intro i; simp only [colOn]; split_ifs with h <;> simp [h] <;> omega
  have ezx := mc_full .zx (m + 1) _ hc
  have exz := mc_full .xz (m + 1) _ hc
  simp only [Net.kindSp, Net.canonC] at ezx exz
  rw [show List.range 1 = [0] from rfl] at ezx exz
  rw [ezx, exz]
  obtain ⟨hnd, hws⟩ := whiteWires_ok (m + 1 + 1) [0] (colOn 1 (m + 1 + 1) x)
  have hbox : Derivable (theory (m + 1 + 1)) (box (m + 1) * box (m + 1)) 1 := by
    have h := eq299 (m + 1 + 1) hN ih
    have e := Net.mc_canon .box (m + 1)
    simp only [Net.kindSp, Net.canonC] at e
    rw [show List.range 1 = [0] from rfl] at e
    simpa [Bx, e, drawn] using h
  set B' : Circ (m + 1 + 1) := conj swap (box (m + 1)) with hB'
  have hB : Derivable (theory (m + 1 + 1)) (B' * B') 1 := by
    have e : B' * B' = swap * box (m + 1) * (swap * swap) * box (m + 1) * swap := by
      simp [hB', conj, drawn, mul_assoc]
    rw [e]
    refine (dright _ (cancel_mid (swap_inv m) (swap * box (m + 1)) (box (m + 1)))).trans ?_
    have e2 : swap * box (m + 1) * box (m + 1) * swap =
        swap * (box (m + 1) * box (m + 1)) * swap := by simp only [mul_assoc]
    rw [e2]
    refine (cancel_mid hbox swap swap).trans ?_
    simpa using swap_inv m
  have hch := ch_inv m
  have exz' : xz (m + 1) = ch * B' * ch * B' := by simp [xz, hB', drawn, mul_assoc]
  have ezx' : zx (m + 1) = B' * ch * B' * ch := by simp [zx, hB', drawn, mul_assoc]
  have lift : ∀ G : Circ (m + 1 + 1), Derivable (theory (m + 1 + 1)) G 1 →
      Derivable (theory (m + 1 + 1))
        (colourW (m + 1 + 1) (whiteWires (m + 1 + 1) [0] (colOn 1 (m + 1 + 1) x)) G) 1 := by
    intro G hG
    rw [Net.colourW_eq]
    refine (dctx _ _ hG).trans ?_
    rw [mul_one]; exact xs_inv _ _ hnd hws
  constructor
  · rw [Net.drawn_cons, Net.drawn_cons, show drawn ([] : List (Circ (m + 1 + 1))) = 1 from rfl, one_mul]
    refine (colourW_mul _ _ hnd hws _ _).trans (lift _ ?_)
    rw [exz', ezx']; exact palin hch hB
  · rw [Net.drawn_cons, Net.drawn_cons, show drawn ([] : List (Circ (m + 1 + 1))) = 1 from rfl, one_mul]
    refine (colourW_mul _ _ hnd hws _ _).trans (lift _ ?_)
    rw [exz', ezx']; exact palin hB hch

/-! ## Lemma D.13: commutations of coloured multi-controlled gates -/

/-- (335) -/
theorem eq335 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .box [0] (colOn 1 N x)) (mc N .box [0] (colOn 1 N y)) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N13.comm335_3 ih x y
  · exact N13.comm335_4 ih x y
  · exact N13.comm335_ge5 N h5 ih x y

/-- (336) -/
theorem eq336 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N13.comm336_3 ih x y c₁ c₂
  · exact N13.comm336_4 ih x y c₁ c₂
  · exact N13.comm336_ge5 N h5 ih x y c₁ c₂

/-- (337) -/
theorem eq337 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (c₁ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [0, 1] (colOn 2 N y)) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N13.comm337_3 ih x y hxy c₁
  · exact N13.comm337_4 ih x y hxy c₁
  · exact N13.comm337_ge5 N h5 ih x y hxy c₁

/-- (338) -/
theorem eq338 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (c₁ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [1, 0] (colOn 2 N y)) := by
  refine N13.comm338_from_diff N hN ih (fun x y hxy c => ?_) (fun x y => eq335 N hN ih x y) x y c₁
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N13.comm338_3 ih x y c
  · exact N13.comm338_4 ih x y hxy c
  · exact N13.comm338d_ge5 N h5 ih x y hxy c

/-- (339) -/
theorem eq339 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ c₃ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 N y))) := by
  rcases (by omega : N = 4 ∨ N = 5 ∨ 6 ≤ N) with rfl | rfl | h6
  · exact N13.L339W4.eq339_4 ih x y hxy c₁ c₂ c₃
  · exact N13.L339.eq339_5 ih x y hxy c₁ c₂ c₃
  · exact N13.comm339_ge6 N h6 ih x y hxy c₁ c₂ c₃

/-- (333): the multi-controlled `ZX` written with a multi-controlled `H`
(box wire 2, `H` on wire 0) and a box (box wire 1). -/
theorem eq333 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .zx [0] (blackOn 1 N))
      (drawn [mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))]) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  refine N13.comm333 M ih (fun y hy => ?_)
  have h4 : 4 ≤ M + 3 := by obtain ⟨j, hj3, hjN, -⟩ := hy; omega
  exact eq339 (M + 3) h4 ih (fun _ => true) y hy true true true

/-- (334): the same for the multi-controlled `XZ`. -/
theorem eq334 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .xz [0] (blackOn 1 N))
      (drawn [mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N))]) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  have h317 := (eq317 (M + 3) hN ih (fun _ => true)).1
  have e : ∀ K : Kind, mc (M + 3) K [0] (colOn 1 (M + 3) (fun _ => true)) =
      mc (M + 3) K [0] (blackOn 1 (M + 3)) := fun K =>
    Net.mc_congr _ _ _ (fun i hi => by simp [colOn, blackOn])
  rw [e .zx, e .xz] at h317
  exact N13.comm334 M ih (eq333 (M + 3) hN ih) h317

/-- (340) -/
theorem eq340 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N13.comm340_3 ih x y
  · exact N13.comm340_4 ih x y
  · exact N13.comm340_ge5 N h5 ih x y

/-- (342) -/
theorem eq342 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [0, 2] (ctlOr (ctlAt 1 c₂) (colOn 3 N y))) := by
  rcases (by omega : N = 4 ∨ N = 5 ∨ 6 ≤ N) with rfl | rfl | h6
  · exact N13.L342W4.eq342_4 ih x y hxy c₁ c₂
  · exact N13.L342.eq342_5 ih x y hxy c₁ c₂
  · exact N13.comm342_ge6 N h6 ih x y hxy c₁ c₂

/-- (344) -/
theorem eq344 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₂) (colOn 3 N y))) := by
  rcases (by omega : N = 4 ∨ N = 5 ∨ 6 ≤ N) with rfl | rfl | h6
  · exact N13.L344W4.eq344_4 ih x y hxy c₁ c₂
  · exact N13.L344.eq344_5 ih x y hxy c₁ c₂
  · exact N13.comm344_ge6 N h6 ih x y hxy c₁ c₂

/-- (345) -/
theorem eq345 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .hg [1, 0] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) := by
  exact N13.comm345 N hN ih x y

/-- (346) -/
theorem eq346 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (a : Bool) :
    Comm N (mc N .box [0] (colOn 1 N x)) (mc N (Kind.sgnZX a) [0] (colOn 1 N y)) :=
  N13.comm346 hN ih (eq333 N hN ih) (eq334 N hN ih) (fun x y c₁ c₂ => eq336 N hN ih x y c₁ c₂)
    (fun x y c₁ => eq338 N hN ih x y c₁) x y a

/-- Naturality of every multi-controlled gate under swaps, from (333), (339),
(317) and (353) (`N13/S353`). -/
theorem mcSwapAll (N : ℕ) (ih : IH N) : E.McSwapAll N :=
  N13.R347.mcSwapAll ih (fun n hn hnN => eq333 n hn (ih.mono hnN))
    (fun n hn hnN => eq339 n hn (ih.mono hnN)) (fun n hn hnN => eq317 n hn (ih.mono hnN))

/-- (347) -/
theorem eq347 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ c₂ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) :=
  N13.R347.comm347 hN ih (mcSwapAll N ih) (eq333 N hN ih) (eq334 N hN ih) (eq336 N hN ih)
    (eq337 N hN ih) x y hxy a c₁ c₂

/-- (348) -/
theorem eq348 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ : Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x))
      (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N y))) := by
  rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | h4
  · -- Three wires: open (the decomposition leaves no wire to spare).
    sorry
  · exact N13.R347.comm348 h4 ih (mcSwapAll N ih) (eq333 N hN ih) (eq334 N hN ih)
      (eq338 N hN ih) (eq344 N h4 ih) x y hxy a c₁

/-- (349) -/
theorem eq349 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ : Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x))
      (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 c₁) (colOn 2 N y))) := by
  rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | h4
  · exact N13.R347.comm349_3 ih (mcSwapAll 3 ih) (eq333 3 hN ih) (eq334 3 hN ih) (eq337 3 hN ih)
      x y hxy a c₁
  · exact N13.R347.comm349 h4 ih (mcSwapAll N ih) (eq333 N hN ih) (eq334 N hN ih)
      (eq339 N h4 ih) (eq340 N hN ih) x y hxy a c₁

/-- (350) -/
theorem eq350 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (a c₁ c₂ c₃ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N (Kind.sgnZX a) [2] (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 0 c₃) (colOn 3 N y)))) :=
  N13.R347.comm350 hN ih (mcSwapAll N ih) (eq333 N (by omega) ih) (eq334 N (by omega) ih)
    (eq337 N (by omega) ih) (eq344 N hN ih) x y hxy a c₁ c₂ c₃

/-- (351) -/
theorem eq351 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (a b : Bool) :
    Comm N (mc N (Kind.sgnZX a) [0] (colOn 1 N x)) (mc N (Kind.sgnZX b) [0] (colOn 1 N y)) := by
  by_cases hd : DiffOn 1 N x y
  · rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | h4
    · exact N13.R347.comm351_3 ih (mcSwapAll 3 ih) (eq333 3 hN ih) (eq334 3 hN ih)
        (eq317 3 hN ih) (eq336 3 hN ih) (eq337 3 hN ih) x y hd a b
    · exact N13.R347.comm351 h4 ih (mcSwapAll N ih) (eq333 N hN ih) (eq334 N hN ih)
        (eq317 N hN ih) (eq335 N hN ih) (eq339 N h4 ih) (eq340 N hN ih) x y a b
  · exact N13.R347.comm351_same (eq317 N hN ih) x y hd a b

/-- (352) -/
theorem eq352 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a b c₁ c₂ : Bool) :
    Comm N (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | h4
  · -- Three wires: open (the decomposition leaves no wire to spare).
    sorry
  · exact N13.R347.comm352 h4 ih (mcSwapAll N ih) (eq333 N hN ih) (eq334 N hN ih)
      (eq335 N hN ih) (eq339 N h4 ih) (eq345 N hN ih) x y hxy a b c₁ c₂

end QCert.RealCliffordCH.Sec8.D
