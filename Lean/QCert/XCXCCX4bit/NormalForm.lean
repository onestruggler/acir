/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The block normal form `NF(E, B, S)`

Translation of `NormalForm.agda`: Section 3 of the paper.  Every four-wire
circuit is equal to exactly one circuit `NF(E, B, S) = C(E) D(B) r_S` (in
composition order), for `E` an even permutation and `B` a permutation of the
eight states of the lower wires and `S` an eight-element set of the sixteen
states.  `r_S` carries `S` onto the half `H₀` where wire 3 is 0, `D(B)`
applies `B` to the lower wires and `C(E)` applies `E` to them on the half
where wire 3 is 1.  The circuits are fixed by the formalization's own
deterministic choices (the theorems hold for any): `D(B)` is the circuit of
Symmetric's Coxeter word for `B` on the Gray positions (`Width3`'s edge
Toffolis), `C(E)` the controlled matchings of `EvenRS 8`'s symbols for `E`'s
word (`CCerts`' `Φ`), and `r_S` the circuit of `EvenRS 16`'s symbols for the
frame of `S`'s states followed by the others (`NFLib`'s `ts`), with one
transposition of the last two states when that word is odd.

Here: the states and `Four`'s numbering (`NFTables`), the building blocks
and their functions (`D_sem`, `C_low`, `C_high`, `r_sem`), the coordinates
(`Coords`) and the function of a normal form (`NF_sem`); uniqueness of the
coordinates (`NF_unique`), the coordinates of a circuit (`Of`, `coords`,
`normal_form`, `unique`), Proposition 3.3's bijection onto `Alt(16)`
(`NF_onto`, with `NF_unique`), and Theorem 5.1's absorption of a gate
(`absorb`, `absorption`, and the updated coordinates in `Absorb`).

Names.  The Agda's `F.enc`, `F.dec` are `Four.enc`, `Four.dec`; its
`⟦_⟧`, `_⟨$⟩ʳ_`, `_⟨$⟩ˡ_` are `sem`, application and `Equiv.symm`; `flip B`
is `B.symm` and `π ∘ₚ ρ` is `π.trans ρ`; `isHi-<ᵇ` is `isHi_ltb`, `γ⁻` is
`(γ S).symm`, `q⁻` is `q'`; the fields of `Coords` are read `c.E`, `c.B`,
`c.S`, `c.S8`.

**Deviations from the Agda.**

* The building blocks `D`, `C`, `r` are `irreducible_def`s (the Agda's
  `opaque` blocks), with their definitions as the equations `D_def`, `C_def`,
  `r_def`; `r_cong` is proved from `r_def`.
* `tr` is typed at `SG (8 + 8)` as in the Agda, and its function is
  `Groups.Fourw.at_` (`at_`); the Agda repeats that proof and `parity-f`
  here (`parity_tr` is `Groups.Fourw.parity_f`).  `gen↓`, `word↓` are
  `Placed.gen_down`, `Placed.word_down`, and `C_low` reads the lower half
  through `KFaithful.Xs_low` (the Agda's `Xs-sem` and `mF*-low`).
* `e_lift` is proved on the two halves of `Fin (8 + 8)` (`Fin.addCases`,
  with `idx_lo` and `NFTables.hi_lift`) where the Agda lists the sixteen
  states.
* The modules `Of u` and `Absorb c w` are namespaces whose definitions take
  `u` (resp. `c`, `w`) explicitly; `back`, which the Agda states inside `Of`
  without using `u`, is `idx_back`.
* `NF_onto` returns a subtype (the Agda's `Σ`).
-/
import QCert.XCXCCX4bit.Groups
import QCert.XCXCCX4bit.NFTables
import QCert.XCXCCX4bit.CBase
import Mathlib.Tactic.IrreducibleDef

namespace QCert.XCXCCX4bit.NormalForm

open QCert QCert.Circuit CircuitProp IndepProp
open Symmetric (SG)
open Alternating NFLib NFTables
open CSem (enc8 pos mFs)

/-! ## States, in `Four`'s numbering -/

private theorem enc_agree : ∀ i, Four.enc i = enc' i := by decide

/-- The half (wire 3) of a numbered state. -/
def isHi (i : Fin 16) : Bool := w3 (Four.enc i)

/-- The Gray position of a numbered state. -/
def pos4 (i : Fin 16) : Fin 8 := pos (Four.enc i)

theorem enc_idx (b : Bool) (p : Fin 8) : Four.enc (idx b p) = st b p :=
  (enc_agree (idx b p)).trans (enc'_idx b p)

theorem dec_st (b : Bool) (p : Fin 8) : Four.dec (st b p) = idx b p := by
  rw [← enc_idx, Four.dec_enc]

theorem isHi_idx (b : Bool) (p : Fin 8) : isHi (idx b p) = b := by
  unfold isHi; rw [enc_idx, w3_st]

theorem pos4_idx (b : Bool) (p : Fin 8) : pos4 (idx b p) = p := by
  unfold pos4; rw [enc_idx, pos_st]

theorem idx_isHi (i : Fin 16) : idx (isHi i) (pos4 i) = i := by
  unfold isHi pos4; rw [enc_agree]; exact idx_eta i

/-- The Agda's `isHi-<ᵇ`. -/
theorem isHi_ltb (i : Fin 16) : isHi i = !Nat.blt i.1 8 := by
  unfold isHi; rw [enc_agree]; exact isHi_lt i

/-- A numbered state is the state of its half at its position. -/
theorem enc_st (i : Fin 16) : Four.enc i = st (isHi i) (pos4 i) := (st_eta (Four.enc i)).symm

/-- An index of half `b` is the index of its position (the Agda's `back`). -/
theorem idx_back (b : Bool) (j : Fin 16) (e : isHi j = b) : idx b (pos4 j) = j := by
  rw [← e]; exact idx_isHi j

/-- The lower half in order. -/
theorem idx_lo : ∀ p : Fin 8, idx false p = Fin.castAdd 8 p := by decide

/-! ## A circuit as a permutation of the numbered states -/

/-- `Four`'s translation into the symbols of `EvenRS 16`, as a Coxeter word.
Its width is written `8 + 8` so that the sign lemmas of `EvenWord.Lift`, at
`j = m = 8`, meet the same spelling. -/
def tr (u : Circ 4) : Word (SG (8 + 8)) :=
  FreeMonoid.lift (EvenRS.f 16) (ByEvenRS.Realisation.translate Four.tw (ToPlaced.pg u))

theorem at_ (u : Circ 4) (i : Fin 16) : sem u (Four.enc i) = Four.enc (Symmetric.perm (tr u) i) :=
  Groups.Fourw.at_ u i

/-- The permutation of the numbered states that a circuit carries out. -/
def perm (u : Circ 4) : Equiv.Perm (Fin (8 + 8)) := Symmetric.perm (tr u)

theorem perm_at (u : Circ 4) (i : Fin 16) : perm u i = Four.dec (sem u (Four.enc i)) :=
  (Four.dec_enc _).symm.trans (congrArg Four.dec (at_ u i).symm)

theorem parity_tr (u : Circ 4) : parity (tr u) = false :=
  Groups.Fourw.parity_f _

/-! ## Reversed circuits -/

def revC (w : Circ 4) : Circ 4 := FreeMonoid.reverse w

theorem revC_sem (w : Circ 4) (x : Bits 4) : sem (revC w) (sem w x) = x := by
  induction w using FreeMonoid.inductionOn' generalizing x with
  | one => rfl
  | mul_of g w ih =>
    rw [revC, FreeMonoid.reverse_mul, FreeMonoid.reverse_of, sem_mul, sem_mul, ← revC, ih,
      sem_of, sem_of, Groups.inv_sem]

/-! ## `D(B)`: `B` on the lower wires -/

/-- The circuit of Symmetric's word for `B` on the lower wires.  Irreducible:
a goal about `sem (D B) x` met by a lemma about its unfolding would make the
kernel evaluate the circuit of Symmetric's word for `B` on the state. -/
irreducible_def D (B : Equiv.Perm (Fin 8)) : Circ 4 := PFrames.Pc 0 (Symmetric.go 8 B)

/-- Over a variable word with its permutation. -/
private theorem Pc_st (w : Word (SG 8)) (B : Equiv.Perm (Fin 8))
    (hw : ∀ p, Symmetric.perm w p = B p) (b : Bool) (p : Fin 8) :
    sem (PFrames.Pc 0 w) (st b p) = st b (B p) :=
  (congrArg (fun c => sem c (st b p)) (CBase.Pc_down 0 w)).trans
    ((Placed.word_down (CBase.Pc₃ 0 w) (Width3.enc p) b).trans
      (congrArg (· ++ (b ∷ .nil))
        ((ByCoxeter.Via.Pc_sem 3 8 Width3.T Width3.enc Width3.T_act w p).trans
          (congrArg Width3.enc (hw p)))))

theorem D_sem (B : Equiv.Perm (Fin 8)) (b : Bool) (p : Fin 8) : sem (D B) (st b p) = st b (B p) :=
  (congrArg (fun c => sem c (st b p)) (D_def B)).trans
    (Pc_st (Symmetric.go 8 B) B (EvenWord.Coset.go_sem 8 B) b p)

/-! ## `C(E)`: `E` on the lower wires where wire 3 is 1 -/

/-- The controlled matchings of `EvenRS 8`'s symbols for Symmetric's word for
`E` (irreducible, as `D`). -/
irreducible_def C (a : Alt 8) : Circ 4 := CCerts.Xs (CCerts.Φs (EvenWord.Coset.syms 8 a))

theorem C_low (a : Alt 8) (p : Fin 8) : sem (C a) (st false p) = st false p := by
  rw [C_def]
  show sem _ (Width3.enc p ++ (false ∷ .nil)) = Width3.enc p ++ (false ∷ .nil)
  generalize Width3.enc p = x
  match x with
  | a' ∷ b ∷ c ∷ .nil => exact KFaithful.Xs_low _ a' b c

/-- Over a variable word of symbols with its permutation. -/
private theorem Xs_st (x : Word (EvenRS.Sch 8)) (E : Equiv.Perm (Fin 8))
    (hx : ∀ p, Symmetric.perm (FreeMonoid.lift (EvenRS.f 8) x) p = E p) (p : Fin 8) :
    sem (CCerts.Xs (CCerts.Φs x)) (st true p) = st true (E p) :=
  (CFaithful.Xs_sem (CCerts.Φs x) (st true p)).trans
    ((congrArg (mFs (CCerts.Φs x)) (enc8_st p).symm).trans
      ((CFaithful.Φs_act x p).trans ((congrArg enc8 (hx p)).trans (enc8_st (E p)))))

theorem C_high (a : Alt 8) (p : Fin 8) : sem (C a) (st true p) = st true (Alt.perm a p) := by
  rw [C_def]
  exact Xs_st (EvenWord.Coset.syms 8 a) (Alt.perm a) (EvenWord.Coset.sym_sem 8 a) p

/-! ## `r_S`: `S` onto the half `H₀` -/

/-- The transposition of the last two states. -/
def s14 : SG 16 := ⟨14, by decide⟩

def fixB : Bool → Word (SG 16) → Word (SG 16)
  | true, w => w * FreeMonoid.of s14
  | false, w => w

/-- A word made even by the transposition of the last two states. -/
def fix (w : Word (SG 16)) : Word (SG 16) := fixB (parity w) w

theorem fix_parity (w : Word (SG 16)) : parity (fix w) = false := by
  unfold fix
  generalize h : parity w = b
  cases b with
  | true => simp [fixB, parity_mul, h]
  | false => exact h

/-- The word of `r_S`. -/
def wS (S : Fin 16 → Bool) : Word (SG 16) := fix (frameL (ts S))

/-- The permutation of `r_S`. -/
def γ (S : Fin 16 → Bool) : Equiv.Perm (Fin 16) := Symmetric.perm (wS S)

private theorem isHi_s14 : ∀ j : Fin 16, isHi (Symmetric.perm (FreeMonoid.of s14) j) = isHi j := by
  decide +kernel

private theorem isHi_fix (w : Word (SG 16)) (j : Fin 16) :
    isHi (Symmetric.perm (fix w) j) = isHi (Symmetric.perm w j) := by
  unfold fix
  generalize parity w = b
  cases b with
  | true =>
    show isHi (Symmetric.perm (w * FreeMonoid.of s14) j) = _
    rw [Symmetric.perm_mul_apply, isHi_s14]
  | false => rfl

private theorem blt_decide (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

/-- The frame of `ts S` sends `S` into `H₀` and the rest into `H₁`. -/
private theorem frame_half (S : Fin 16 → Bool) (w8 : weight S = 8) (i : Fin 16) :
    isHi (Symmetric.perm (frameL (ts S)) i) = !(S i) := by
  have hlen : (Symmetric.perm (frameL (ts S)) i).1 < (ts S).length := by
    rw [ts_length]; exact (Symmetric.perm (frameL (ts S)) i).2
  obtain ⟨x, hx⟩ := nth_total (ts S) _ hlen
  have x_i : x = i :=
    (frameL_act (ts S) (ts_distinct S) _ x hx).symm.trans
      ((Symmetric.perm (frameL (ts S))).symm_apply_apply i)
  have S_i := nth_ts S _ hx
  rw [x_i, w8] at S_i
  rw [isHi_ltb, S_i, blt_decide]

theorem isHi_γ (S : Fin 16 → Bool) (w8 : weight S = 8) (i : Fin 16) : isHi (γ S i) = !(S i) :=
  (isHi_fix (frameL (ts S)) i).trans (frame_half S w8 i)

/-- The circuit `r_S` (irreducible, as `D`). -/
irreducible_def r (S : Fin 16 → Bool) : Circ 4 :=
  Placed.ιs (Four.RL.Rs (EvenRS.rs 16 false (wS S)).1)

/-- `r_S` depends only on the states of `S`. -/
theorem r_cong {S S' : Fin 16 → Bool} (e : ∀ i, S i = S' i) : r S = r S' := by
  rw [r_def, r_def, wS, wS, ts_cong e]

theorem r_sem (S : Fin 16 → Bool) (i : Fin 16) : sem (r S) (Four.enc i) = Four.enc (γ S i) := by
  rw [r_def]
  exact (Placed.ιs_sem _ (Four.enc i)).trans ((Four.RL.Rs_act _ i).trans
    (congrArg Four.enc
      (EvenRS.rs_sem (wS S) (EvenWord.Coset.coset_even 16 (wS S) (fix_parity _)) i)))

theorem γ_cong {S S' : Fin 16 → Bool} (e : ∀ i, S i = S' i) (i : Fin 16) : γ S i = γ S' i := by
  unfold γ wS; rw [ts_cong e]

/-! ## The normal form -/

/-- The coordinates: `E ∈ Alt(8)`, `B ∈ Sym(8)` and an eight-subset `S` of the
sixteen states (in `Four`'s numbering). -/
structure Coords where
  E : Alt 8
  B : Equiv.Perm (Fin 8)
  S : Fin 16 → Bool
  S8 : weight S = 8

/-- `NF(E, B, S) = C(E) D(B) r_S` in composition order: `r_S` first. -/
def NF (c : Coords) : Circ 4 := r c.S * (D c.B * C c.E)

/-- The function of the block part: `B` on `H₀`, `E B` on `H₁`. -/
def blk (E B : Equiv.Perm (Fin 8)) : Bool → Fin 8 → Bits 4
  | false, p => st false (B p)
  | true, p => st true (E (B p))

theorem w3_blk (E B : Equiv.Perm (Fin 8)) : ∀ b p, w3 (blk E B b p) = b
  | false, p => w3_st false (B p)
  | true, p => w3_st true (E (B p))

/-- The function of a normal form: `r_S`, then the blocks. -/
theorem NF_sem (c : Coords) (i : Fin 16) :
    sem (NF c) (Four.enc i) = blk (Alt.perm c.E) c.B (isHi (γ c.S i)) (pos4 (γ c.S i)) := by
  have blocks : ∀ b p, sem (D c.B * C c.E) (st b p) = blk (Alt.perm c.E) c.B b p
    | false, p => (sem_mul _ _ _).trans
        ((congrArg (sem (C c.E)) (D_sem c.B false p)).trans (C_low c.E (c.B p)))
    | true, p => (sem_mul _ _ _).trans
        ((congrArg (sem (C c.E)) (D_sem c.B true p)).trans (C_high c.E (c.B p)))
  rw [NF, sem_mul, r_sem, enc_st (γ c.S i), blocks]

/-! ## Uniqueness of the coordinates (the injective half of Proposition 3.3) -/

private theorem not_inj {a b : Bool} (e : (!a) = !b) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem w3_NF (c : Coords) (i : Fin 16) : w3 (sem (NF c) (Four.enc i)) = !(c.S i) := by
  rw [NF_sem, w3_blk, isHi_γ c.S c.S8 i]

/-- At the state that `r_S` sends to the index of half `b`, position `p`. -/
private theorem NF_at (c : Coords) (b : Bool) (p : Fin 8) :
    sem (NF c) (Four.enc ((γ c.S).symm (idx b p))) = blk (Alt.perm c.E) c.B b p := by
  rw [NF_sem, Equiv.apply_symm_apply, isHi_idx, pos4_idx]

theorem NF_unique (c c' : Coords) (e : sem (NF c) ≐ sem (NF c')) :
    (∀ i, c.S i = c'.S i) ∧ (∀ p, c.B p = c'.B p) ∧
      (∀ p, Alt.perm c.E p = Alt.perm c'.E p) := by
  have sameS : ∀ i, c.S i = c'.S i := fun i =>
    not_inj ((w3_NF c i).symm.trans ((congrArg w3 (e _)).trans (w3_NF c' i)))
  -- The two `r_S` are the same, so are their inverses.
  have γinv : ∀ k, (γ c.S).symm k = (γ c'.S).symm k := fun k => by
    rw [Equiv.ext (γ_cong sameS)]
  have blk_eq : ∀ b p, blk (Alt.perm c.E) c.B b p = blk (Alt.perm c'.E) c'.B b p := fun b p =>
    (NF_at c b p).symm.trans ((e _).trans
      ((congrArg (fun k => sem (NF c') (Four.enc k)) (γinv (idx b p))).trans (NF_at c' b p)))
  have sameB : ∀ p, c.B p = c'.B p := fun p =>
    (pos_st false (c.B p)).symm.trans ((congrArg pos (blk_eq false p)).trans (pos_st false (c'.B p)))
  refine ⟨sameS, sameB, fun p => ?_⟩
  have h := congrArg pos (blk_eq true (c.B.symm p))
  simp only [blk, pos_st, Equiv.apply_symm_apply] at h
  rw [← sameB, Equiv.apply_symm_apply] at h
  exact h

/-! ## The coordinates of a circuit (the onto half) -/

namespace Of

variable (u : Circ 4)

/-- The permutation of `u`. -/
def π : Equiv.Perm (Fin (8 + 8)) := perm u

/-- The states that `u` sends into `H₀`. -/
def Su (i : Fin 16) : Bool := !(isHi (π u i))

theorem Su8 : weight (Su u) = 8 :=
  (weight_perm (π u) (fun i => !(isHi i))).trans (by decide +kernel)

def g : Equiv.Perm (Fin 16) := γ (Su u)

theorem half_g (i : Fin 16) : isHi (g u i) = !(Su u i) := isHi_γ (Su u) (Su8 u) i

/-- `u` after `r_S`'s inverse preserves the halves. -/
def q (j : Fin 16) : Fin 16 := π u ((g u).symm j)

/-- The Agda's `q⁻`. -/
def q' (j : Fin 16) : Fin 16 := g u ((π u).symm j)

theorem q_q' (j : Fin 16) : q u (q' u j) = j := by
  unfold q q'; rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem q'_q (j : Fin 16) : q' u (q u j) = j := by
  unfold q q'; rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem q_half (j : Fin 16) : isHi (q u j) = isHi j := by
  have h := half_g u ((g u).symm j)
  rw [Equiv.apply_symm_apply, Su, Bool.not_not] at h
  exact h.symm

theorem q'_half (j : Fin 16) : isHi (q' u j) = isHi j := by
  unfold q'; rw [half_g, Su, Bool.not_not, Equiv.apply_symm_apply]

/-- The blocks. -/
def bF (b : Bool) (p : Fin 8) : Fin 8 := pos4 (q u (idx b p))

def bG (b : Bool) (p : Fin 8) : Fin 8 := pos4 (q' u (idx b p))

theorem bF_bG (b : Bool) (p : Fin 8) : bF u b (bG u b p) = p := by
  unfold bF bG
  rw [idx_back b (q' u (idx b p)) ((q'_half u _).trans (isHi_idx b p)), q_q', pos4_idx]

theorem bG_bF (b : Bool) (p : Fin 8) : bG u b (bF u b p) = p := by
  unfold bF bG
  rw [idx_back b (q u (idx b p)) ((q_half u _).trans (isHi_idx b p)), q'_q, pos4_idx]

def Bb (b : Bool) : Equiv.Perm (Fin 8) := ⟨bF u b, bG u b, bG_bF u b, bF_bG u b⟩

theorem Bb_apply (b : Bool) (p : Fin 8) : Bb u b p = bF u b p := by
  rw [Bb, Equiv.coe_fn_mk]

theorem Bb_symm_apply (b : Bool) (p : Fin 8) : (Bb u b).symm p = bG u b p := by
  rw [Bb, Equiv.coe_fn_symm_mk]

def B0 : Equiv.Perm (Fin 8) := Bb u false

def B1 : Equiv.Perm (Fin 8) := Bb u true

/-- `E = B₁ B₀⁻¹` in composition order. -/
def Ep : Equiv.Perm (Fin 8) := (B0 u).symm.trans (B1 u)

/-- `E` is even: the circuit `D(B₀⁻¹)`, then `r_S` reversed, then `u`, is the
identity on `H₀` and `E` on `H₁`. -/
def v : Circ 4 := D (B0 u).symm * (revC (r (Su u)) * u)

theorem rinv (j : Fin 16) : sem (revC (r (Su u))) (Four.enc j) = Four.enc ((g u).symm j) := by
  have h : Four.enc j = sem (r (Su u)) (Four.enc ((g u).symm j)) := by
    rw [r_sem]; exact congrArg Four.enc (Equiv.apply_symm_apply _ _).symm
  rw [h, revC_sem]

theorem v_at (b : Bool) (p : Fin 8) :
    sem (v u) (st b p) = Four.enc (q u (idx b (bG u false p))) := by
  unfold v
  rw [sem_mul, sem_mul, D_sem, ← enc_idx, rinv]
  exact at_ u _

theorem v_lo (p : Fin 8) : perm (v u) (idx false p) = idx false p := by
  rw [perm_at, enc_idx, v_at, Four.dec_enc]
  unfold bG
  rw [idx_back false (q' u (idx false p)) ((q'_half u _).trans (isHi_idx false p)), q_q']

theorem v_hi (p : Fin 8) : perm (v u) (idx true p) = idx true (Ep u p) := by
  rw [perm_at, enc_idx, v_at, Four.dec_enc]
  exact (idx_back true _ ((q_half u _).trans (isHi_idx true _))).symm

theorem e_lift (i : Fin (8 + 8)) :
    perm (v u) i = Coxeter.liftN 8 (rev8.trans ((Ep u).trans rev8)) i := by
  induction i using Fin.addCases with
  | left p =>
    rw [Coxeter.liftN_lo 8 _ _ (by simp), ← idx_lo p]
    exact v_lo u p
  | right k =>
    have hk : Fin.natAdd 8 k = idx true (rev8 k) := by
      rw [hi_lift, show rev8 (rev8 k) = k from rv_rv k]
    rw [Coxeter.liftN_natAdd, hk, v_hi u, hi_lift]
    rfl

theorem Ep_even : sign (Ep u) = false :=
  EvenWord.Lift.lift_sign 8 8 (tr (v u)) (parity_tr (v u)) rev8 (Ep u) (e_lift u)

def coords : Coords where
  E := Alt.mk (Ep u) (Ep_even u)
  B := B0 u
  S := Su u
  S8 := Su8 u

theorem coords_E : Alt.perm (coords u).E = Ep u := rfl

theorem coords_B : (coords u).B = B0 u := rfl

theorem coords_S : (coords u).S = Su u := rfl

theorem q_g (i : Fin 16) : q u (g u i) = π u i := by
  unfold q; rw [Equiv.symm_apply_apply]

/-- The normal form of the coordinates denotes `u`. -/
theorem NF_enc (i : Fin 16) : sem (NF (coords u)) (Four.enc i) = Four.enc (π u i) := by
  have by_half : ∀ (j : Fin 16) (b : Bool), isHi j = b →
      blk (Ep u) (B0 u) b (pos4 j) = Four.enc (q u j) := by
    intro j b e
    rw [enc_st (q u j), q_half, e]
    cases b with
    | false => rw [blk, B0, Bb_apply, bF, idx_back false j e]
    | true =>
      rw [blk, Ep, Equiv.trans_apply, Equiv.symm_apply_apply, B1, Bb_apply, bF,
        idx_back true j e]
  have h := by_half (g u i) _ rfl
  rw [q_g] at h
  rw [NF_sem, coords_E, coords_B, coords_S, show γ (Su u) = g u from rfl]
  exact h

theorem NF_u : sem (NF (coords u)) ≐ sem u := fun x =>
  (congrArg (sem (NF (coords u))) (Four.enc_dec x).symm).trans
    ((NF_enc u (Four.dec x)).trans
      ((at_ u (Four.dec x)).symm.trans (congrArg (sem u) (Four.enc_dec x))))

end Of

/-- The coordinates of a circuit. -/
def coords (u : Circ 4) : Coords := Of.coords u

/-! ## The theorems -/

/-- Every four-wire circuit rewrites to the normal form of its coordinates
(the main theorem's normal form)... -/
theorem normal_form (u : Circ 4) : 4 ⊢ u ≈ NF (coords u) :=
  Completeness.complete₄ fun x => (Of.NF_u u x).symm

/-- ... and to no other: the coordinates are unique. -/
theorem unique (u : Circ 4) (c : Coords) (e : 4 ⊢ u ≈ NF c) :
    (∀ i, c.S i = (coords u).S i) ∧ (∀ p, c.B p = (coords u).B p) ∧
      (∀ p, Alt.perm c.E p = Alt.perm (coords u).E p) :=
  NF_unique c (coords u) fun x => (sound e x).symm.trans (sound (normal_form u) x)

/-- Proposition 3.3, the semantic bijection
`Alt(8) × Sym(8) × (eight-subsets) → Alt(16)`: injective (`NF_unique`) and
onto, every even permutation of the sixteen states being the function of a
normal form. -/
def NF_onto (a : Alt 16) :
    {c : Coords // ∀ i, sem (NF c) (Four.enc i) = Four.enc (Alt.perm a i)} :=
  ⟨coords (Groups.Fourw.E.circA a), fun i =>
    (sound (normal_form (Groups.Fourw.E.circA a)).symm (Four.enc i)).trans
      (Groups.Fourw.E.circA_sem a i)⟩

/-- The paper's check of the count: `(16 choose 8) · 8! · 8!/2 = 16!/2`. -/
theorem count : 12870 * (Nat.factorial 8 * (Nat.factorial 8 / 2)) = Nat.factorial 16 / 2 := by
  decide

/-! ## Theorem 5.1: gate absorption

For any circuit `w` (in particular one of the 28 placed gates), `w` followed
by `NF(E, B, S)` (in composition order `NF(E, B, S) w`) is the normal form of
`absorb c w`; its coordinates are the paper's update `S′ = w⁻¹ S`,
`B′ = B A₀` and `E′ = E B A₁ A₀⁻¹ B⁻¹`, where `R = r_S w r_S′⁻¹` preserves
the halves with blocks `A₀`, `A₁`. -/

def absorb (c : Coords) (w : Circ 4) : Coords := coords (w * NF c)

theorem absorption (c : Coords) (w : Circ 4) : 4 ⊢ w * NF c ≈ NF (absorb c w) :=
  normal_form (w * NF c)

namespace Absorb

variable (c : Coords) (w : Circ 4)

/-- The updated coordinates. -/
def c' : Coords := absorb c w

/-- The state that `w` sends the numbered state `i` to. -/
def wk (i : Fin 16) : Fin 16 := Four.dec (sem w (Four.enc i))

private def EB (p : Fin 8) : Fin 8 := Alt.perm c.E (c.B p)

private theorem NF_w (i : Fin 16) :
    Of.π (w * NF c) i = Four.dec (sem (NF c) (Four.enc (wk w i))) := by
  rw [Of.π, perm_at, sem_mul, wk, Four.enc_dec]

private theorem half_dec : ∀ b p, isHi (Four.dec (blk (Alt.perm c.E) c.B b p)) = b
  | false, p => by
    show isHi (Four.dec (st false (c.B p))) = false
    rw [dec_st, isHi_idx]
  | true, p => by
    show isHi (Four.dec (st true (EB c p))) = true
    rw [dec_st, isHi_idx]

/-- `S′ = w⁻¹ S`. -/
theorem absorb_S (i : Fin 16) : (c' c w).S i = c.S (wk w i) := by
  rw [c', absorb, coords, Of.coords_S, Of.Su, NF_w, NF_sem, half_dec, isHi_γ c.S c.S8,
    Bool.not_not]

/-- `R = r_S w r_S′⁻¹` (in composition order) on the numbered states. -/
def R (j : Fin 16) : Fin 16 := γ c.S (wk w ((γ (c' c w).S).symm j))

theorem R_half (j : Fin 16) : isHi (R c w j) = isHi j := by
  unfold R
  rw [isHi_γ c.S c.S8, ← absorb_S, ← isHi_γ (c' c w).S (c' c w).S8, Equiv.apply_symm_apply]

/-- Its blocks. -/
def A (b : Bool) (p : Fin 8) : Fin 8 := pos4 (R c w (idx b p))

private theorem q_R (b : Bool) (p : Fin 8) :
    Of.q (w * NF c) (idx b p) = Four.dec (blk (Alt.perm c.E) c.B b (A c w b p)) := by
  show Of.π (w * NF c) ((γ (c' c w).S).symm (idx b p)) = _
  rw [NF_w, NF_sem]
  exact congrArg (fun b' => Four.dec (blk (Alt.perm c.E) c.B b' (A c w b p)))
    ((R_half c w (idx b p)).trans (isHi_idx b p))

private theorem pos_blk : ∀ b p,
    pos4 (Four.dec (blk (Alt.perm c.E) c.B b p)) = pos (blk (Alt.perm c.E) c.B b p)
  | false, p => by
    show pos4 (Four.dec (st false (c.B p))) = pos (st false (c.B p))
    rw [dec_st, pos4_idx, pos_st]
  | true, p => by
    show pos4 (Four.dec (st true (EB c p))) = pos (st true (EB c p))
    rw [dec_st, pos4_idx, pos_st]

/-- `B′ = B A₀`. -/
theorem absorb_B (p : Fin 8) : (c' c w).B p = c.B (A c w false p) := by
  rw [c', absorb, coords, Of.coords_B, Of.B0, Of.Bb_apply, Of.bF, q_R, pos_blk]
  exact pos_st false _

/-- `E′ B′ = E B A₁`, i.e. `E′ = E B A₁ A₀⁻¹ B⁻¹`. -/
theorem absorb_E (p : Fin 8) :
    Alt.perm (c' c w).E ((c' c w).B p) = Alt.perm c.E (c.B (A c w true p)) := by
  rw [c', absorb, coords, Of.coords_E, Of.coords_B, Of.Ep, Equiv.trans_apply,
    Equiv.symm_apply_apply, Of.B1, Of.Bb_apply, Of.bF, q_R, pos_blk]
  exact pos_st true _

end Absorb

end QCert.XCXCCX4bit.NormalForm
