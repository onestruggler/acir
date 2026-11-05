/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The steps of the case tree of Case 3.4, one check each

A node of `Case34.lean` is one of six steps.  Each is a lemma taking the data
of the node, *one* Boolean check of everything the step needs on the pattern
(decided by `decide +kernel`), and the nodes it continues with:

* `dichStep`: a split on the parity of a form `lf` in the parameters
  (`pat_dich'`: the parameter `p` with an odd coefficient is replaced by
  `2 x + b' − R`, the substitution computed by `Psplit`, which touches the one
  parameter instead of substituting a form for each);
* `twStep`: a transfer along a word `K` on the window (`transfer_win`), the
  window then shrunk to the target's (`shrink_window`) and its pattern
  converted (`pat_conv'`);
* `monoStep`: a transfer along a monomial word (`transfer_mono`);
* `extStep`: an entry outside the window forced by an odd class count
  (`tail_entry`), moved to the window (`extend_entry`);
* `oddStep`: an entry forced by an odd number of odd entries
  (`tail_odd_entry`), of either class;
* `cleanStep`: the entries outside the window cleaned (`clean_ind`).

One check per node, where the nodes had five to eleven, shares the window
after the word between the tests and spares the fixed cost of a `decide`
for each.

The generated modules write their integer lists as `zl[a, b, -c, …]`
(`elabZl`), which builds the list from the constructors `Int.ofNat`,
`Int.negSucc` on literals: elaborated as numerals, the patterns of the case
tree cost about 50 ms each (an instance problem and a `Neg.neg` per
coefficient), and the parameter changes of the transfers about 90 ms each.
-/
import QCert.HadamardPi.Case34Base

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### Integer lists in the generated modules -/

/-- `zl[a, b, -c, …]`: the list `[a, b, -c, …] : List ℤ` (scoped to `QCert.HadamardPi`, so that
the token does not reach the modules that import this one without opening the namespace). -/
scoped syntax (name := zlLit) "zl[" ("-"? num),* "]" : term

open Lean Elab Term in
/-- `zl[…]` elaborated directly into `Int.ofNat n`, `Int.negSucc n` on raw literals, with no
instance problem per coefficient. -/
@[term_elab zlLit] def elabZl : TermElab := fun stx _ => do
  let mut e := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Int)
  for a in stx[1].getSepArgs.reverse do
    let some k := a[1].isNatLit? | throwErrorAt a "zl[…]: a numeral expected"
    let v := if !a[0].isNone && k != 0 then mkApp (mkConst ``Int.negSucc) (mkRawNatLit (k - 1))
      else mkApp (mkConst ``Int.ofNat) (mkRawNatLit k)
    e := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Int) v e
  return e

example : zl[3, 0, -2, -1] = [3, 0, -2, -1] := rfl

noncomputable section

/-! ### Substituting one parameter -/

theorem lget_eq_zero_of_le : ∀ (l : List ℤ) {p : ℕ}, l.length ≤ p → lget l p = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: as, p + 1, h => lget_eq_zero_of_le as (by simp at h; omega)

/-- Substitute the form `L` for the parameter `p` in the form `f`. -/
def substAt (f : List ℤ) (p : ℕ) (L : List ℤ) : List ℤ :=
  match f with
  | [] => []
  | c :: cs =>
    if (lget cs p).natAbs = 0 then c :: cs
    else ladd ((c + lget cs p * L.headD 0) :: lset cs p 0) (0 :: lsmul (lget cs p) L.tail)

theorem evv_headD_tail (L : List ℤ) (t : ℕ → ℤ) : evv L (c1 t) = L.headD 0 + evv L.tail t := by
  cases L with
  | nil => simp
  | cons c cs => rw [evv_c1]; rfl

theorem evv_substAt (f : List ℤ) (p : ℕ) (L : List ℤ) (t : ℕ → ℤ) :
    evv (substAt f p L) (c1 t) = evv f (c1 (Function.update t p (evv L (c1 t)))) := by
  cases f with
  | nil => rfl
  | cons c cs =>
    simp only [substAt]
    split_ifs with ha
    · rw [Int.natAbs_eq_zero] at ha
      rw [evv_c1, evv_c1, evv_update, ha, zero_mul, add_zero]
    · have hp : p < cs.length := by
        by_contra h
        exact ha (by rw [lget_eq_zero_of_le cs (not_lt.1 h)]; rfl)
      simp only [evv_ladd, evv_c1, evv_lsmul, zero_add]
      rw [evv_lset cs p 0 t hp, evv_update, evv_headD_tail]
      ring

/-- The pattern with the form `L` substituted for the parameter `p`. -/
def Psplit (P : List ZL) (p : ℕ) (L : List ℤ) : List ZL :=
  P.map fun x => (substAt x.1 p L, substAt x.2 p L)

theorem zev_Psplit (P : List ZL) (p : ℕ) (L : List ℤ) (t : ℕ → ℤ) (j : ℕ) :
    zev ((Psplit P p L).getD j dZ) t = zev (P.getD j dZ) (Function.update t p (evv L (c1 t))) := by
  simp only [Psplit, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[j]? with
  | none => simp [dZ, zev]
  | some x => simp [zev, evv_substAt]

/-- A split on the parity of a form, the substitution computed by `Psplit`
(`pat_dich` with the new pattern in one-parameter form). -/
theorem pat_dich' {w : ℕ} {v : Fin n → ℝ} {f : Fin w → Fin n} {P : List ZL} (lf : List ℤ) (p : ℕ)
    (hodd : lget lf.tail p % 2 = 1) (hp : p < lf.tail.length) {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num v (f j) = zev (P.getD j dZ) t) :
    (evv lf (c1 t) % 2 = 0 ∧ ∀ j : Fin w, num v (f j) =
        zev ((Psplit P p (splitL lf p 0)).getD j dZ) (Function.update t p (splitX lf p 0 t))) ∨
      (evv lf (c1 t) % 2 = 1 ∧ ∀ j : Fin w, num v (f j) =
        zev ((Psplit P p (splitL lf p 1)).getD j dZ) (Function.update t p (splitX lf p 1 t))) := by
  have key : ∀ b : ℤ, evv lf (c1 t) % 2 = b → ∀ j : Fin w, num v (f j) =
      zev ((Psplit P p (splitL lf p b)).getD j dZ) (Function.update t p (splitX lf p b t)) := by
    intro b hb j
    rw [zev_Psplit, split_eq hodd hp hb, Function.update_idem, Function.update_eq_self, hP]
  rcases Int.emod_two_eq_zero_or_one (evv lf (c1 t)) with h | h
  · exact Or.inl ⟨h, key 0 h⟩
  · exact Or.inr ⟨h, key 1 h⟩

/-! ### A split -/

/-- The check of a split on the parity of `lf`: an odd coefficient at `p`, and
the patterns `Q0`, `Q1` of the two children. -/
def dichChk (P : List ZL) (lf : List ℤ) (p : ℕ) (Q0 Q1 : List ZL) : Bool :=
  decide (lget lf.tail p % 2 = 1) && decide (p < lf.tail.length) &&
    decide (Pnorm Q0 = Pnorm (Psplit P p (splitL lf p 0))) &&
    decide (Pnorm Q1 = Pnorm (Psplit P p (splitL lf p 1)))

theorem dichStep {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {kb : ℕ} (hK : kb ≤ lde (col s (pj s (piv_pos hs)))) {P : List ZL}
    {t : ℕ → ℤ} (hP : WinPat s hs hw P t) {d : ℕ} (htail : TailD s hs w d) (lf : List ℤ) (p : ℕ)
    (Q0 Q1 : List ZL) (hchk : dichChk P lf p Q0 Q1 = true) {A B : List (Gen w)}
    (h0 : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w ≤ piv s', kb ≤ lde (col s' (pj s' (piv_pos hs'))) → ∀ t' : ℕ → ℤ,
      WinPat s' hs' hw' Q0 t' → TailD s' hs' w d → wJ s' hw' A B)
    (h1 : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w ≤ piv s', kb ≤ lde (col s' (pj s' (piv_pos hs'))) → ∀ t' : ℕ → ℤ,
      WinPat s' hs' hw' Q1 t' → TailD s' hs' w d → wJ s' hw' A B) :
    wJ s hw A B := by
  simp only [dichChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hodd, hp⟩, e0⟩, e1⟩ := hchk
  rcases pat_dich' lf p hodd hp hP with ⟨-, hP0⟩ | ⟨-, hP1⟩
  · exact h0 s hs hk hw hK _ (pat_eqv e0 hP0) htail
  · exact h1 s hs hk hw hK _ (pat_eqv e1 hP1) htail

/-! ### Transfers -/

/-- The checks of a transfer along `K` on a window of `w` entries, continuing
on the window `0, …, w'-1` with the pattern `Q` at the parameters `φ`. -/
def twChk {w : ℕ} (P : List ZL) (K A B : List (Gen w)) (w' : ℕ) (Q : List ZL)
    (φ : List (List ℤ)) : Bool :=
  let V := divAll P K
  disjW A K && disjW B K && allSome P K && oddSure (V.getD 0 dZ) && sameOdd (w := w) P V &&
    pathOK P K A && pathOK P K B && tailDiv V w' w &&
    decide (Pnorm (Psubst Q φ) = Pnorm (V.take w'))

theorem twStep {w w' : ℕ} (hww : w' ≤ w) (hw0 : 0 < w) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ}
    (hP : WinPat s hs hw P t) {d : ℕ} (hd : 1 ≤ d) (htail : TailD s hs w d)
    (K : List (Gen w)) {A B : List (Gen w)} (Q : List ZL) (φ : List (List ℤ))
    (hchk : twChk P K A B w' Q φ = true) {A' B' : List (Gen w')}
    (hA' : A'.map (Gen.map (Fin.castLE hww) (Fin.strictMono_castLE hww)) = A)
    (hB' : B'.map (Gen.map (Fin.castLE hww) (Fin.strictMono_castLE hww)) = B)
    (hJ : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w' ≤ piv s', 1 ≤ lde (col s' (pj s' (piv_pos hs'))) → ∀ t' : ℕ → ℤ,
      WinPat s' hs' hw' Q t' → TailD s' hs' w' 1 → wJ s' hw' A' B') :
    wJ s hw A B := by
  simp only [twChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hdA, hdB⟩, hc⟩, ho⟩, hsame⟩, hpA⟩, hpB⟩, htd⟩, hconv⟩ := hchk
  refine transfer_win hs hk hw hP (T := fun u => ∃ y, rt2 ^ d * y = u) htail
    (comm_word_win hdA) (comm_word_win hdB) hc ⟨0, hw0⟩ ho hsame hpA hpB
    fun s' hs' hk' hw' hP' ht' => ?_
  obtain ⟨hP6, ht6⟩ := shrink_window hww hw' hP' ht' hd htd
  have := hJ s' hs' hk' (hww.trans hw') (Nat.one_le_iff_ne_zero.2 hk') _
    (pat_conv' (φ := φ) hconv hP6.take) ht6
  rw [← hA', ← hB', map_castLE_castLE, map_castLE_castLE]
  exact this

/-- The checks of a transfer along a monomial word `m`, with `A' m ≈ μ A`,
`B' m ≈ ν B`, continuing with the pattern `Q` at the parameters `φ`. -/
def monoChk {w : ℕ} (P : List ZL) (m μ ν A : List (Gen w)) (Q : List ZL)
    (φ : List (List ℤ)) : Bool :=
  allMono m && allMono μ && allMono ν && allSome P m && oddSure ((divAll P m).getD 0 dZ) &&
    pathOK P [] A && decide (Pnorm (Psubst Q φ) = Pnorm (divAll P m))

theorem monoStep {w : ℕ} (hw0 : 0 < w) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ}
    (hP : WinPat s hs hw P t) {d : ℕ} (htail : TailD s hs w d) (m μ ν : List (Gen w))
    {A B : List (Gen w)} (A' B' : List (Gen w))
    (hA : Derivable Fig6 (ofList (A' ++ m)) (ofList (μ ++ A)))
    (hB : Derivable Fig6 (ofList (B' ++ m)) (ofList (ν ++ B)))
    (Q : List ZL) (φ : List (List ℤ)) (hchk : monoChk P m μ ν A Q φ = true)
    (hJ : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w ≤ piv s', 1 ≤ lde (col s' (pj s' (piv_pos hs'))) → ∀ t' : ℕ → ℤ,
      WinPat s' hs' hw' Q t' → TailD s' hs' w d → wJ s' hw' A' B') :
    wJ s hw A B := by
  simp only [monoChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hm, hμ⟩, hν⟩, hc⟩, ho⟩, hpA⟩, hconv⟩ := hchk
  exact transfer_mono hs hk hw hP (T := fun u => ∃ y, rt2 ^ d * y = u) htail hm hμ hν hA hB hc
    ⟨0, hw0⟩ ho hpA fun s' hs' hk' hw' hP' ht' =>
      hJ s' hs' hk' hw' (Nat.one_le_iff_ne_zero.2 hk') _ (pat_conv' (φ := φ) hconv hP') ht'

/-! ### Entries outside the window -/

/-- The checks of an entry of depth `δ` and class `γ` forced by an odd class
count after `D`, moved to the window; `Q` the pattern of the extended window. -/
def extChk {w : ℕ} (P : List ZL) (nv : ℕ) (D A B : List (Gen w)) (δ : ℕ) (γ : Bool)
    (Q : List ZL) : Bool :=
  let V := divAllD P D δ
  allSomeD P D δ && decide (2 ≤ (List.range w).countP fun j => oddSure (V.getD j dZ)) &&
    clsCount (w := w) V γ 1 && Pwidth P nv && decide (P.length = w) && oddSure (P.getD 0 dZ) &&
    pathOK P [] A && pathOK P [] B && decide (Pnorm Q = Pnorm (P ++ [dent δ γ nv]))

theorem extStep {w : ℕ} (hw0 : 0 < w) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hw : w ≤ piv s) {kb : ℕ}
    (hK : kb ≤ lde (col s (pj s (piv_pos hs)))) {P : List ZL} {t : ℕ → ℤ}
    (hP : WinPat s hs hw P t) {δ : ℕ} (hδ : 1 ≤ δ) (hδle : δ ≤ lde (col s (pj s (piv_pos hs))))
    (htail : TailD s hs w δ) (nv : ℕ) (D : List (Gen w)) {A B : List (Gen w)} (γ : Bool)
    (Q : List ZL) (hchk : extChk P nv D A B δ γ Q = true) {A' B' : List (Gen (w + 1))}
    (hA' : A.map (Gen.map (Fin.castLE (Nat.le_succ w)) (Fin.strictMono_castLE _)) = A')
    (hB' : B.map (Gen.map (Fin.castLE (Nat.le_succ w)) (Fin.strictMono_castLE _)) = B')
    (hJ : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w + 1 ≤ piv s', kb ≤ lde (col s' (pj s' (piv_pos hs'))) → ∀ t' : ℕ → ℤ,
      WinPat s' hs' hw' Q t' → TailD s' hs' (w + 1) δ → wJ s' hw' A' B') :
    wJ s hw A B := by
  simp only [extChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hcD, hcnt⟩, hcls⟩, hPw⟩, hPl⟩, ho0⟩, hpA⟩, hpB⟩, hQ⟩ := hchk
  have hKd : δ + 1 ≤ lde (col s (pj s (piv_pos hs))) := by
    have h := pow_ge_of_odd (Fin.castLE (hw.trans (piv_le_n s))) (Fin.strictMono_castLE _) hs hP
      D δ hδle hcD (htail.castLE _)
    have := one_le_of_pow h (by exact_mod_cast hcnt)
    omega
  obtain ⟨i, hi, y, hyo, hyc, hy⟩ := tail_entry (Fin.castLE (hw.trans (piv_le_n s)))
    (Fin.strictMono_castLE _) hs hP D δ hKd hcD (htail.castLE _) γ hcls
  refine extend_entry hs hk hw (nv := nv) hPw hPl hP ⟨0, hw0⟩ ho0
    (T := fun u => ∃ y, rt2 ^ δ * y = u) (fun u hu => not_odd_of_rt2 hδ hu) htail
    (idx_castLE_lt _ _) (idx_castLE_lt _ _) (lev_lt_of_check hs hk hw hP hpA)
    (lev_lt_of_check hs hk hw hP hpB) ((castLE_ne_iff _ i).1 hi) (δ := δ) (γ := γ) hy hyo hyc
    fun s' hs' hk' hw' hP' ht' hlev => ?_
  have := hJ s' hs' hk' hw' (by rw [lde_eq_of_lev hs hs' hlev]; exact hK) _ (pat_eqv hQ hP') ht'
  simp only [wJ] at this
  rw [← hA', ← hB', map_castLE_castLE, map_castLE_castLE] at this
  exact this

/-- The checks of an entry of depth `δ0 + 1` forced by an odd number of odd
entries after `DM` (the exponent bound from `D0` at depth `δ0`), of either
class: `Qt`, `Qf` the patterns of the extended window for the two classes. -/
def oddChk {w : ℕ} (P : List ZL) (nv : ℕ) (D0 DM A B : List (Gen w)) (δ0 : ℕ)
    (Qt Qf : List ZL) : Bool :=
  allSomeD P D0 δ0 &&
    decide (3 ≤ (List.range w).countP fun j => oddSure ((divAllD P D0 δ0).getD j dZ)) &&
    allSomeD P DM (δ0 + 1) && oddSureL (sumRe (w := w) (divAllD P DM (δ0 + 1))) &&
    Pwidth P nv && decide (P.length = w) && oddSure (P.getD 0 dZ) &&
    pathOK P [] A && pathOK P [] B &&
    decide (Pnorm Qt = Pnorm (P ++ [dent (δ0 + 1) true nv])) &&
    decide (Pnorm Qf = Pnorm (P ++ [dent (δ0 + 1) false nv]))

theorem oddStep {w : ℕ} (hw0 : 0 < w) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hw : w ≤ piv s) {kb : ℕ}
    (hK : kb ≤ lde (col s (pj s (piv_pos hs)))) {P : List ZL} {t : ℕ → ℤ}
    (hP : WinPat s hs hw P t) {δ0 : ℕ} (hδle : δ0 ≤ lde (col s (pj s (piv_pos hs))))
    (htail : TailD s hs w (δ0 + 1)) (nv : ℕ) (D0 DM : List (Gen w)) {A B : List (Gen w)}
    (Qt Qf : List ZL) (hchk : oddChk P nv D0 DM A B δ0 Qt Qf = true) {A' B' : List (Gen (w + 1))}
    (hA' : A.map (Gen.map (Fin.castLE (Nat.le_succ w)) (Fin.strictMono_castLE _)) = A')
    (hB' : B.map (Gen.map (Fin.castLE (Nat.le_succ w)) (Fin.strictMono_castLE _)) = B')
    (hJt : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w + 1 ≤ piv s', kb ≤ lde (col s' (pj s' (piv_pos hs'))) → ∀ t' : ℕ → ℤ,
      WinPat s' hs' hw' Qt t' → TailD s' hs' (w + 1) (δ0 + 1) → wJ s' hw' A' B')
    (hJf : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w + 1 ≤ piv s', kb ≤ lde (col s' (pj s' (piv_pos hs'))) → ∀ t' : ℕ → ℤ,
      WinPat s' hs' hw' Qf t' → TailD s' hs' (w + 1) (δ0 + 1) → wJ s' hw' A' B') :
    wJ s hw A B := by
  simp only [oddChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc0, hcnt⟩, hcM⟩, hsum⟩, hPw⟩, hPl⟩, ho0⟩, hpA⟩, hpB⟩, hQt⟩, hQf⟩ := hchk
  have hKd : δ0 + 1 + 1 ≤ lde (col s (pj s (piv_pos hs))) := by
    have h := pow_ge_of_odd (Fin.castLE (hw.trans (piv_le_n s))) (Fin.strictMono_castLE _) hs hP
      D0 δ0 hδle hc0 (htail.mono.castLE _)
    have := two_le_of_pow h (by exact_mod_cast hcnt)
    omega
  obtain ⟨i, hi, y, hyo, hy⟩ := tail_odd_entry (Fin.castLE (hw.trans (piv_le_n s)))
    (Fin.strictMono_castLE _) hs hP DM (δ0 + 1) hKd hcM (htail.castLE _) hsum
  by_cases hc : Odd y.im
  · refine extend_entry hs hk hw (nv := nv) hPw hPl hP ⟨0, hw0⟩ ho0
      (T := fun u => ∃ y, rt2 ^ (δ0 + 1) * y = u) (fun u hu => not_odd_of_rt2 (by omega) hu) htail
      (idx_castLE_lt _ _) (idx_castLE_lt _ _) (lev_lt_of_check hs hk hw hP hpA)
      (lev_lt_of_check hs hk hw hP hpB) ((castLE_ne_iff _ i).1 hi) (δ := δ0 + 1) (γ := true)
      hy hyo (iff_of_true hc rfl) fun s' hs' hk' hw' hP' ht' hlev => ?_
    have := hJt s' hs' hk' hw' (by rw [lde_eq_of_lev hs hs' hlev]; exact hK) _ (pat_eqv hQt hP') ht'
    simp only [wJ] at this
    rw [← hA', ← hB', map_castLE_castLE, map_castLE_castLE] at this
    exact this
  · refine extend_entry hs hk hw (nv := nv) hPw hPl hP ⟨0, hw0⟩ ho0
      (T := fun u => ∃ y, rt2 ^ (δ0 + 1) * y = u) (fun u hu => not_odd_of_rt2 (by omega) hu) htail
      (idx_castLE_lt _ _) (idx_castLE_lt _ _) (lev_lt_of_check hs hk hw hP hpA)
      (lev_lt_of_check hs hk hw hP hpB) ((castLE_ne_iff _ i).1 hi) (δ := δ0 + 1) (γ := false)
      hy hyo (iff_of_false hc (by simp)) fun s' hs' hk' hw' hP' ht' hlev => ?_
    have := hJf s' hs' hk' hw' (by rw [lde_eq_of_lev hs hs' hlev]; exact hK) _ (pat_eqv hQf hP') ht'
    simp only [wJ] at this
    rw [← hA', ← hB', map_castLE_castLE, map_castLE_castLE] at this
    exact this

/-! ### Cleaning the tail -/

/-- The checks of the cleaning (`cleanOK`) with the exponent bound. -/
def cleanChk {w : ℕ} (P : List ZL) (nv δ : ℕ) (D A0 B0 : List (Gen w)) : Bool :=
  cleanOK P nv δ D A0 B0 && allSomeD P D δ &&
    decide (2 ≤ (List.range w).countP fun j => oddSure ((divAllD P D δ).getD j dZ))

theorem cleanStep {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ} (hP : WinPat s hs hw P t) {δ : ℕ}
    (hδle : δ ≤ lde (col s (pj s (piv_pos hs)))) (htail : TailD s hs w δ) (nv : ℕ)
    (D : List (Gen w)) {A0 B0 : List (Gen w)} (hchk : cleanChk P nv δ D A0 B0 = true)
    (step : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w ≤ piv s', δ + 1 ≤ lde (col s' (pj s' (piv_pos hs'))) → ∀ t' : ℕ → ℤ,
      WinPat s' hs' hw' P t' → TailD s' hs' w (δ + 1) → wJ s' hw' A0 B0) :
    wJ s hw A0 B0 := by
  simp only [cleanChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨hok, hcD⟩, hcnt⟩ := hchk
  have hK2 : δ + 1 ≤ lde (col s (pj s (piv_pos hs))) := by
    have h := pow_ge_of_odd (Fin.castLE (hw.trans (piv_le_n s))) (Fin.strictMono_castLE _) hs hP
      D δ hδle hcD (htail.castLE _)
    have := one_le_of_pow h (by exact_mod_cast hcnt)
    omega
  exact clean_ind hok step s hs hk hw hK2 t hP htail

end

end QCert.HadamardPi
