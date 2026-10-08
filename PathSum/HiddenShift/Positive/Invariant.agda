------------------------------------------------------------------------
-- Presentations of groups
--
-- The invariant that output-safe, Clifford-safe reductions keep
--
-- PathSum.HiddenShift.Positive proves that every maximal chain of
-- PathSum.HiddenShift.Positive.Class's admissible steps from the hidden
-- shift circuit on |0⟩ is complete.  This module states the invariant
-- that argument rests on and proves that every admissible step keeps
-- it (Inv-step, Inv-chain).  Inv ξ says, of a path-sum ξ of order one
-- (phase ½F modulo 1, outputs G modulo 2: PathSum.HiddenShift.Positive.
-- Values' VTracks):
--
-- * inj: the outputs determine the path variables that occur in them --
--   two paths with the same outputs agree at every variable that is
--   not internal (Class's Int);
-- * a witness T, a set of internal variables each of which occurs in
--   the phase only quadratically (Class's Clifᶜ), such that the partial
--   sum of (-1)^F over T is stabilizer-like (PathSum.HiddenShift.
--   Positive.Stabilizer's SL): 2^d times it is a constant times the
--   indicator of an affine subspace times (-1)^R, R quadratic.
--
-- Why each step keeps it.  Renumbering permutes everything (Inv-front;
-- Stabilizer's Σ-unfr).  [ω] and [Case] never apply at order one
-- (Values' ω-impossible, case-impossible).  [Elim] at the head sums
-- (-1)^F over a variable F does not read, and [HH] at the head with
-- y_i ← Q sums it over the head and y_i together: the head's
-- derivative is y_i ⊕ q, so of the four terms two cancel and two equal
-- (-1)^F at y₀ = 0, y_i = q, the reduct's (σ-hh).  Both rules
-- therefore turn a partial sum of the path-sum's signs into twice one
-- of the reduct's, once the summed variables are added to the witness
-- (SL-grow: a partial sum of a stabilizer-like function is one, by
-- Gaussian elimination); the new witness is the old one without them.
-- It stays internal because an [HH] substituting a form with an
-- internal variable substitutes an internal variable (OutSafe), so an
-- internal variable never enters an output (Int-hh), and it stays
-- quadratic because the step is Clifford-safe (CliffSafe).  The same
-- fact, that internal variables stay internal, keeps inj.
--
-- Everything is read off values: the syntactic Int and Clifᶜ are
-- converted to independence (Indep) and affine derivatives (Cl) of G
-- and F (Int⇒Indep, Indep⇒Int, Clif⇒Cl, Cl⇒Clif), whose behaviour
-- under the rules' substitutions PathSum.HiddenShift.Positive.Boolean
-- records.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive.Invariant (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_)
open import Data.Integer.Properties using (+-identityʳ; +-identityˡ)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₂)
open import Data.Vec.Base using (_∷_; lookup; insertAt; removeAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base using (PathSum; phase; out; head-part)
open import PathSum.HiddenShift.Positive.Boolean
open import PathSum.HiddenShift.Positive.Class M₀ using
  (Int; Clifᶜ; OutSafe; CliffSafe; Adm; Admᶠ; _⟶ᴷ*_; εᴷ; _◅ᴷ_)
open import PathSum.HiddenShift.Positive.Stabilizer
open import PathSum.HiddenShift.Positive.Values M₀ using
  (VTracks; front-vtracks; elim-vtracks; module HH; elim-flat;
   ω-impossible; case-impossible; Int⇒flat; flat⇒Int; Aff⇒Clif; Clif⇒Aff)
open import PathSum.Polynomial using
  (Poly; y[_]; sgn; 0ᴾ; μ; _+ᴾ_; _·ᴾ_; _≈[_]_)
open import PathSum.Polynomial.Boolean using (BoolValued)
open import PathSum.Polynomial.Decidable using (Absent?)
open import PathSum.Polynomial.Substitution using (Absent)
open import PathSum.Reorder using (front)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using (plain; at)
open import PathSum.Full M using (_⟶ᶠ_)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½; elim-reduct)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ; hhᴳ-reduct)

private
  variable
    N n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Syntax and values

-- An internal variable is one G does not read ...

Int⇒Indep : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
            {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
            (v : Fin (suc m)) → Int ξ v → ∀ w → Indep (G w) v
Int⇒Indep {G = G} tr v int w p =
  trans (cong (G w) (set-as-insertAt p v true))
    (trans (Int⇒flat tr v int w (removeAt p v))
           (cong (G w) (sym (set-as-insertAt p v false))))

Indep⇒Int : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
            {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
            (v : Fin (suc m)) → (∀ w → Indep (G w) v) → Int ξ v
Indep⇒Int {G = G} tr v h = flat⇒Int tr v λ w z →
  trans (cong (G w) (sym (set-insertAt z v false true)))
    (trans (h w (insertAt z v false))
           (cong (G w) (set-insertAt z v false false)))

-- ... and a Clifford one, one in which F's derivative is affine.

Clif⇒Cl : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
          {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
          (v : Fin (suc m)) → Clifᶜ (phase ξ) v → Cl F v
Clif⇒Cl {F = F} tr v c = Aff-cong
  (λ p → sym (cong₂ (λ a b → F a xor F b) (set-as-insertAt p v true)
                                          (set-as-insertAt p v false)))
  (Aff-∘ (Clif⇒Aff tr v c) (AffMap-removeAt v))

Cl⇒Clif : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
          {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
          (v : Fin (suc m)) → Cl F v → Clifᶜ (phase ξ) v
Cl⇒Clif {F = F} tr v c = Aff⇒Clif tr v (Aff-cong
  (λ z → cong₂ (λ a b → F a xor F b) (set-insertAt z v false true)
                                     (set-insertAt z v false false))
  (Aff-∘ c (AffMap-insertAt v false)))


------------------------------------------------------------------------
-- Internal and Clifford variables through the rules

-- Renumbering.

Int-front : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
            {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
            (j v : Fin (suc m)) → Int ξ (πᶠ j v) → Int (front j ξ) v
Int-front {G = G} tr j v int = Indep⇒Int (front-vtracks tr j) v
  (λ w → Indep-unfr {f = G w} j v (Int⇒Indep tr (πᶠ j v) int w))

Clif-front : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
             {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
             (j v : Fin (suc m)) → Clifᶜ (phase ξ) (πᶠ j v) →
             Clifᶜ (phase (front j ξ)) v
Clif-front {F = F} tr j v c = Cl⇒Clif (front-vtracks tr j) v
  (Cl-unfr {f = F} j v (Clif⇒Cl tr (πᶠ j v) c))

-- [Elim] at the head.

Int-elim : {χ : PathSum N (suc (suc k)) (suc m)} {F : Pt (suc m) → Bool}
           {G : Fin N → Pt (suc m) → Bool} → VTracks χ F G →
           (v : Fin m) → Int χ (suc v) → Int (elim-reduct χ) v
Int-elim {m = suc m} {G = G} tr v int = Indep⇒Int (elim-vtracks tr) v
  (λ w → Indep-tail {f = G w} v (Int⇒Indep tr (suc v) int w))

Clif-elim : {χ : PathSum N (suc (suc k)) (suc m)} {F : Pt (suc m) → Bool}
            {G : Fin N → Pt (suc m) → Bool} → VTracks χ F G →
            (v : Fin m) → Clifᶜ (phase χ) (suc v) →
            Clifᶜ (phase (elim-reduct χ)) v
Clif-elim {m = suc m} {F = F} tr v c = Cl⇒Clif (elim-vtracks tr) v
  (Cl-tail {f = F} v (Clif⇒Cl tr (suc v) c))

-- [HH] at the head: the substituted variable is no longer read, and an
-- internal variable stays internal -- if Q reads it, the substituted
-- variable is internal too (OutSafe), and the substitution leaves the
-- outputs alone.

module HHᴵ {χ : PathSum N k (suc (suc m))} {F : Pt (suc (suc m)) → Bool}
           {G : Fin N → Pt (suc (suc m)) → Bool} (tr : VTracks χ F G)
           (i : Fin (suc m)) (Q : Poly N (suc m)) (bQ : BoolValued Q)
           (absQ : Absent y[ i ] Q)
           (eqP : head-part (phase χ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))) where

  open HH tr i Q bQ absQ eqP public

  q-indep : ∀ v → Absent y[ v ] Q → Indep q v
  q-indep v abs p = trans (q-off v abs p true) (sym (q-off v abs p false))

  Int-self : Int (hhᴳ-reduct χ i Q) i
  Int-self = Indep⇒Int reduct i
    (λ w → Indep-hh-self {f = G w} {q} i (q-indep i absQ))


  Int-hh : OutSafe χ i Q → ∀ v → Int χ (suc v) → Int (hhᴳ-reduct χ i Q) v
  Int-hh os v int = Indep⇒Int reduct v (λ w → go w (v ≟ i))
    where
    by-abs : ∀ w → v ≢ i → Dec (Absent y[ v ] Q) → Indep (G″ w) v
    by-abs w v≢i (yes abs) = Indep-hh-off {f = G w} {q} i v v≢i
      (q-indep v abs) (Int⇒Indep tr (suc v) int w)
    by-abs w v≢i (no ¬abs) = Indep-hh-out {f = G w} {q} i v
      (Int⇒Indep tr (suc i) (os v int ¬abs) w) (Int⇒Indep tr (suc v) int w)

    go : ∀ w → Dec (v ≡ i) → Indep (G″ w) v
    go w (yes v≡i) = subst (Indep (G″ w)) (sym v≡i)
      (Indep-hh-self {f = G w} {q} i (q-indep i absQ))
    go w (no v≢i)  = by-abs w v≢i (Absent? y[ v ] Q)

  -- Summing (-1)^F over the head and y_i: of the four terms, the two
  -- off y_i = q cancel and the two on it are (-1)^F″.

  private
    two : ∀ t f → sgn f + sgn t ≡ (if t xor f then 0ℤ else sgn f + sgn f)
    two false false = refl
    two false true  = refl
    two true  false = refl
    two true  true  = refl

  A : Pt (suc m) → ℤ
  A y = sgn (F (false ∷ y)) + sgn (F (true ∷ y))

  private
    one : ∀ y b → A (set y i b) ≡
          (if b xor q y then 0ℤ
           else sgn (F (false ∷ set y i b)) + sgn (F (false ∷ set y i b)))
    one y b = trans (two (F (true ∷ set y i b)) (F (false ∷ set y i b)))
      (cong (λ d → if d then 0ℤ else S′ + S′)
            (trans (deriv (set y i b))
                   (cong₂ _xor_ (lookup-set-here y i b) (q-off i absQ y b))))
      where
      S′ : ℤ
      S′ = sgn (F (false ∷ set y i b))

  σ-hh : ∀ y → σ i A y ≡ sgn (F″ y) + sgn (F″ y)
  σ-hh y = fin (q y) refl
    where
    S : Bool → ℤ
    S b = sgn (F (false ∷ set y i b)) + sgn (F (false ∷ set y i b))

    fin : ∀ c → q y ≡ c → σ i A y ≡ sgn (F″ y) + sgn (F″ y)
    lo : ∀ c → q y ≡ c → A (set y i false) ≡ (if c then 0ℤ else S false)
    lo c e = trans (one y false) (cong (λ c → if c then 0ℤ else S false) e)

    hi : ∀ c → q y ≡ c → A (set y i true) ≡ (if not c then 0ℤ else S true)
    hi c e = trans (one y true) (cong (λ c → if not c then 0ℤ else S true) e)

    fin false e = trans (cong₂ _+_ (lo false e) (hi false e))
      (trans (+-identityʳ (S false)) (cong S (sym e)))
    fin true  e = trans (cong₂ _+_ (lo true e) (hi true e))
      (trans (+-identityˡ (S true)) (cong S (sym e)))


------------------------------------------------------------------------
-- The invariant

record Inv (ξ : PathSum N k m) : Set where
  constructor inv
  field
    F     : Pt m → Bool
    G     : Fin N → Pt m → Bool
    vt    : VTracks ξ F G
    inj   : ∀ p p′ → (∀ w → G w p ≡ G w p′) →
            ∀ v → ¬ Int ξ v → lookup p v ≡ lookup p′ v
    T     : Fin m → Bool
    T-int : ∀ v → T v ≡ true → Int ξ v
    T-clf : ∀ v → T v ≡ true → Clifᶜ (phase ξ) v
    T-sl  : SL (Σ[ T ] (λ p → sgn (F p)))


------------------------------------------------------------------------
-- Every admissible step keeps it

-- Renumbering.

Inv-front : {ξ : PathSum N k (suc m)} → Inv ξ → (j : Fin (suc m)) →
            Inv (front j ξ)
Inv-front {ξ = ξ} I j = record
  { F     = λ p → F (unfr j p)
  ; G     = λ w p → G w (unfr j p)
  ; vt    = front-vtracks vt j
  ; inj   = λ p p′ eq v ¬int → trans (sym (lookup-unfr j p v))
      (trans (inj (unfr j p) (unfr j p′) eq (πᶠ j v)
                  (λ int → ¬int (Int-front vt j v int)))
             (lookup-unfr j p′ v))
  ; T     = λ u → T (πᶠ j u)
  ; T-int = λ v e → Int-front vt j v (T-int (πᶠ j v) e)
  ; T-clf = λ v e → Clif-front vt j v (T-clf (πᶠ j v) e)
  ; T-sl  = SL-cong (λ p → sym (Σ-unfr T j (λ y → sgn (F y)) p))
                    (SL-∘ T-sl (AffMap-unfr j))
  }
  where open Inv I

-- [Elim] at the head: the head joins the witness and is summed away.

Inv-elim : {χ : PathSum N (suc (suc k)) (suc m)} → Inv χ →
           head-part (phase χ) ≈[ pow M ] 0ᴾ → Inv (elim-reduct χ)
Inv-elim {χ = χ} I eqP = record
  { F     = λ p → F (false ∷ p)
  ; G     = λ w p → G w (false ∷ p)
  ; vt    = elim-vtracks vt
  ; inj   = λ p p′ eq v ¬int → inj (false ∷ p) (false ∷ p′) eq (suc v)
                                   (λ int → ¬int (Int-elim vt v int))
  ; T     = T′
  ; T-int = λ v e → Int-elim vt v (T-int (suc v) e)
  ; T-clf = λ v e → Clif-elim vt v (T-clf (suc v) e)
  ; T-sl  = SL-half (SL-cong sums
      (SL-∘ (SL-grow T zero {λ y → sgn (F y)} T-sl)
            (AffMap-insertAt zero false)))
  }
  where
  open Inv I

  T′ : Fin _ → Bool
  T′ v = T (suc v)

  sF′ : Pt _ → ℤ
  sF′ p = sgn (F (false ∷ p))

  sums : ∀ p → Σ[ setᵀ T zero true ] (λ y → sgn (F y)) (false ∷ p) ≡
               Σ[ T′ ] sF′ p + Σ[ T′ ] sF′ p
  sums p = trans
    (Σ-cong T′ (λ y → cong (λ b → sgn (F (false ∷ y)) + sgn b)
                           (elim-flat vt eqP y)) p)
    (Σ-+ T′ sF′ sF′ p)

-- [HH] at the head: the head and y_i join the witness and are summed
-- away.

Inv-hh : {χ : PathSum N k (suc m)} → Inv χ → (i : Fin m) (Q : Poly N m)
         (bQ : BoolValued Q) (absQ : Absent y[ i ] Q) →
         (eqP : head-part (phase χ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))) →
         OutSafe χ i Q → CliffSafe χ i Q → Inv (hhᴳ-reduct χ i Q)
Inv-hh {m = zero}  I () Q bQ absQ eqP os cs
Inv-hh {m = suc m} {χ = χ} I i Q bQ absQ eqP os cs = record
  { F     = F″
  ; G     = G″
  ; vt    = reduct
  ; inj   = inj″
  ; T     = T″
  ; T-int = λ v e → Int-hh os v (T-int (suc v) (proj₂ (kept v e)))
  ; T-clf = λ v e → cs v (T-int (suc v) (proj₂ (kept v e)))
                         (T-clf (suc v) (proj₂ (kept v e)))
  ; T-sl  = SL-half (SL-cong sums (SL-∘
      (SL-grow (setᵀ T zero true) (suc i) {λ y → sgn (F y)}
               (SL-grow T zero {λ y → sgn (F y)} T-sl))
      (AffMap-insertAt zero false)))
  }
  where
  open Inv I
  open HHᴵ vt i Q bQ absQ eqP

  T′ T″ : Fin (suc m) → Bool
  T′ v = T (suc v)
  T″   = setᵀ T′ i false

  kept : ∀ v → T″ v ≡ true → (v ≢ i) × (T (suc v) ≡ true)
  kept v e with v ≟ i
  ... | yes refl = ⊥-elim (f≢t (trans (sym (setᵀ-here T′ i false)) e))
    where
    f≢t : false ≢ true
    f≢t ()
  ... | no v≢i   = v≢i , trans (sym (setᵀ-there T′ false v≢i)) e

  inj″ : ∀ p p′ → (∀ w → G″ w p ≡ G″ w p′) →
         ∀ v → ¬ Int (hhᴳ-reduct χ i Q) v → lookup p v ≡ lookup p′ v
  inj″ p p′ eq v ¬int with v ≟ i
  ... | yes refl = ⊥-elim (¬int Int-self)
  ... | no v≢i   = trans (sym (lookup-set-there p (q p) v≢i))
    (trans (inj (false ∷ set p i (q p)) (false ∷ set p′ i (q p′)) eq (suc v)
                (λ int → ¬int (Int-hh os v int)))
           (lookup-set-there p′ (q p′) v≢i))

  sF″ : Pt (suc m) → ℤ
  sF″ p = sgn (F″ p)

  sums : ∀ p → Σ[ setᵀ (setᵀ T zero true) (suc i) true ] (λ y → sgn (F y))
                 (false ∷ p) ≡
               Σ[ T″ ] sF″ p + Σ[ T″ ] sF″ p
  sums p = trans (Σ-pull (setᵀ T′ i true) i (setᵀ-here T′ i true) A p)
    (trans (Σ-congᵀ (setᵀ-agree (setᵀ T′ i true) T″ i false
                                (setᵀ-here T′ i false)
                       (λ l l≢i → trans (setᵀ-there T′ false l≢i)
                                        (sym (setᵀ-there T′ true l≢i))))
                    (σ i A) p)
      (trans (Σ-cong T″ σ-hh p) (Σ-+ T″ sF″ sF″ p)))

-- A head step: [ω] and [Case] never apply.

Inv-head : {χ : PathSum N k m} {ζ : PathSum N k′ m′} → Inv χ →
           (s : χ ⟶ᴳ ζ) → Adm s → Inv ζ
Inv-head I (elimᴳ χ eqP eqf)              _        = Inv-elim I eqP
Inv-head I (ωᴳ χ Q bQ eqP eqf)            _        =
  ⊥-elim (ω-impossible (Inv.vt I) Q eqP)
Inv-head I (hhᴳ χ i Q bQ absQ eqP eqf)    (os , cs) =
  Inv-hh I i Q bQ absQ eqP os cs
Inv-head I (caseᴳ χ X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ eqfᵢ eqfⱼ) _ =
  ⊥-elim (case-impossible (Inv.vt I) X Q Q′ bX e₁₀ e₀₁)

-- Any admissible step, and so any chain of them.

Inv-step : {ξ : PathSum N k m} {ζ : PathSum N k′ m′} → Inv ξ →
           (s : ξ ⟶ᶠ ζ) → Admᶠ s → Inv ζ
Inv-step I (plain (plain s)) a = Inv-head I s a
Inv-step I (plain (at j s))  a = Inv-head (Inv-front I j) s a
Inv-step I (at j (plain s))  a = Inv-head (Inv-front I j) s a
Inv-step I (at j (at j′ s))  a = Inv-head (Inv-front (Inv-front I j) j′) s a

Inv-chain : {ξ : PathSum N k m} {ζ : PathSum N k′ m′} → Inv ξ →
            ξ ⟶ᴷ* ζ → Inv ζ
Inv-chain I εᴷ               = I
Inv-chain I ((s , a) ◅ᴷ ss) = Inv-chain (Inv-step I s a) ss
