------------------------------------------------------------------------
-- Presentations of groups
--
-- The class admits the complete reductions Exists builds
--
-- PathSum.HiddenShift.Exists reduces the hidden shift circuit on |0⟩
-- (and every path-sum written as it) completely, in three passes over
-- the coordinates i < m:
--
--   pass 1: [HH] at b_i with d_i ← a_i ⊕ s_L,i, then [Elim] of d_i;
--   pass 2: [HH] at c_i with e_i ← s_L,i,       then [Elim] of e_i;
--   pass 3: [HH] at a_i with h_i ← s_R,i,       then [Elim] of h_i.
--
-- This module shows that every one of those steps is a step of
-- PathSum.HiddenShift.Positive.Class's class, so that the passes are a
-- chain of the class (hidden-shift-admits, written-admits).  [Elim] is
-- always admissible.  The [HH]s of passes 2 and 3 substitute
-- constants: output-safe vacuously, and Clifford-safe because a
-- substitution that reads no variable keeps every Clifford variable
-- Clifford (Positive.Admit's cs-from).  The [HH] of pass 1 substitutes
-- for d_i, an internal variable (the outputs are e and h), so it is
-- output-safe; its quotient mentions a_i alone, and when a_i is
-- Clifford so is d_i -- both derivatives are γ ⊕ (affine), γ the
-- derivative of g in coordinate i (Positive.ExistsLink) -- so it is
-- Clifford-safe.
--
-- How it is built.  Exists' construction is private, so it is rebuilt
-- here: the stages, the label bookkeeping (locate, Flip, Advance) and
-- the passes are Exists' own, copied, with the chain a chain of the
-- class (State's chain : ξ₀ ⟶ᴷ* ξ) and each [HH]+[Elim] made by
-- Positive.Admit's hh-elimᴷ, which asks for the two safety proofs.  The
-- rule instances are those of Exists, step for step; that the forgetful
-- image of this chain equals the term Exists builds is not stated (its
-- intermediate stages are private).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive.Exists (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_)
open import Data.Bool.Properties using (xor-comm; xor-assoc; xor-same)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; punchIn; punchOut)
open import Data.Fin.Properties using
  (punchIn-injective; punchInᵢ≢i; punchIn-punchOut)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift M₀ using (HS; hs-norm; boolᴾ; boolᴾ-resp)
open import PathSum.HiddenShift.Blocks
open import PathSum.HiddenShift.Exists M₀ using
  (pos₀; lab₀; lab₀-pos₀; pos₀-lab₀; module Sweep; ρ₀; Written; written₀;
   written-tracks)
open import PathSum.HiddenShift.Positive.Admit M₀ using
  (_◅◅ᴷ_; hh-elimᴷ; module Safe; Cl-unfr⁻¹)
open import PathSum.HiddenShift.Positive.Boolean
open import PathSum.HiddenShift.Positive.Class M₀ using
  (Int; Clifᶜ; OutSafe; CliffSafe; _⟶ᴷ*_; εᴷ)
open import PathSum.HiddenShift.Positive.ExistsLink M₀ using (module Link)
open import PathSum.HiddenShift.Positive.Initial M₀ using (Fblk-cong)
open import PathSum.HiddenShift.Positive.Invariant M₀ using
  (Indep⇒Int; Clif⇒Cl; Cl⇒Clif)
open import PathSum.HiddenShift.Positive.Values M₀ using
  (VTracks; vtr; front-vtracks)
open import PathSum.HiddenShift.Simulation M₀ using (at0)
open import PathSum.HiddenShift.Stuck.Machine M₀ using (tracks-cong)
open import PathSum.HiddenShift.Track M₀ using (Tracks; hh-premise)
open import PathSum.HiddenShift.Walsh using (lhalf; rhalf)
open import PathSum.Polynomial using (Poly; y[_]; eval)
open import PathSum.Polynomial.Boolean using
  (var; lit; _⊕ᵉ_; liftᵉ; eval-liftᵉ; Absent-liftᵉ; BoolValued; IsBit;
   IsBit-if)
open import PathSum.Polynomial.Substitution using (Absent)
open import PathSum.Reorder using
  (insertᵃ; insertᵃ-here; insertᵃ-punchIn; front)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Reduction M using (elim-reduct)
open import PathSum.Reduction.General M using (hhᴳ-reduct)

private
  variable
    k : ℕ


------------------------------------------------------------------------
-- Small facts (Exists')

private
  fin0 : Fin 0 → ⊥
  fin0 ()

  t≢f : true ≢ false
  t≢f ()

  y-inj : ∀ {n k} {i j : Fin k} → y[_] {n} {k} i ≡ y[ j ] → i ≡ j
  y-inj refl = refl

  -- Labels in different blocks, or at different coordinates, differ.

  blk≢ : ∀ {m} {b b′ : Blk} {i i′ : Fin m} → b ≢ b′ → (b , i) ≢ (b′ , i′)
  blk≢ ne e = ne (cong proj₁ e)

  crd≢ : ∀ {m} {b : Blk} {i i′ : Fin m} → i ≢ i′ → (b , i) ≢ (b , i′)
  crd≢ ne e = ne (cong proj₂ e)

  -- Setting y_j to either bit leaves the other positions alone.

  insertᵃ-off : ∀ (j p : Fin (suc k)) → j ≢ p → (c c′ : Bool)
                (y : Assign k) → insertᵃ j c y p ≡ insertᵃ j c′ y p
  insertᵃ-off j p j≢p c c′ y = trans
    (cong (insertᵃ j c y) (sym (punchIn-punchOut j≢p)))
    (trans (insertᵃ-punchIn j c y (punchOut j≢p))
      (sym (trans (cong (insertᵃ j c′ y) (sym (punchIn-punchOut j≢p)))
                  (insertᵃ-punchIn j c′ y (punchOut j≢p)))))


------------------------------------------------------------------------
-- The reduction, for one g and s

module _ {m : ℕ} (g : Poly m 0) (s : Assign (m ℕ+ m)) where

  private
    sL sR : Assign m
    sL = lhalf {m} s
    sR = rhalf {m} s

  open Phase (boolᴾ g) (boolᴾ-resp g) sL sR

  private
    -- A present label other than v is at a position other than v's.

    locate : ∀ {Ret : Lbl m → Bool} {k} (lab : Fin (suc k) → Lbl m) →
             (∀ ℓ → Ret ℓ ≡ true → Σ (Fin (suc k)) (λ p → lab p ≡ ℓ)) →
             ∀ {v} (j : Fin (suc k)) → lab j ≡ v →
             ∀ u → Ret u ≡ true → u ≢ v →
             Σ (Fin k) (λ i → lab (punchIn j i) ≡ u)
    locate lab fd j lj u Ru u≢v =
      punchOut j≢p , trans (cong lab (punchIn-punchOut j≢p)) (proj₂ (fd u Ru))
      where
      j≢p : j ≢ proj₁ (fd u Ru)
      j≢p e = u≢v (trans (sym (proj₂ (fd u Ru)))
                         (trans (cong lab (sym e)) lj))

    -- Two present labels do not fit in one path variable.

    one-slot : ∀ {Ret : Lbl m → Bool} (lab : Fin 1 → Lbl m) →
               (∀ ℓ → Ret ℓ ≡ true → Σ (Fin 1) (λ p → lab p ≡ ℓ)) →
               ∀ v u → Ret v ≡ true → Ret u ≡ true → v ≢ u → ⊥
    one-slot lab fd v u Rv Ru v≢u with fd v Rv | fd u Ru
    ... | zero , lv | zero , lu = v≢u (trans (sym lv) lu)

  ----------------------------------------------------------------------
  -- The path-sum with y_j set, read by label

  -- A present label other than v keeps its value when y_j, which is v,
  -- flips; v takes the value of y_j; a removed label keeps its fixed
  -- value.

  private
    module Flip {Ret : Lbl m → Bool} {k : ℕ}
                (lab : Fin (suc k) → Lbl m) (ρ : Assign (suc k) → LAssign m)
                (rd : ∀ y p → ρ y (lab p) ≡ y p)
                (df : ∀ y ℓ → Ret ℓ ≡ false → ρ y ℓ ≡ dflt ℓ (ρ y))
                (fd : ∀ ℓ → Ret ℓ ≡ true → Σ (Fin (suc k)) (λ p → lab p ≡ ℓ))
                (j : Fin (suc k)) {v : Lbl m} (lj : lab j ≡ v) where

      Zᶜ : Bool → Assign k → LAssign m
      Zᶜ c y = ρ (insertᵃ j c y)

      self : ∀ c y → Zᶜ c y v ≡ c
      self c y = trans (cong (Zᶜ c y) (sym lj))
                       (trans (rd (insertᵃ j c y) j) (insertᵃ-here j c y))

      flipped : ∀ y → Zᶜ true y v xor Zᶜ false y v ≡ true
      flipped y = cong₂ _xor_ (self true y) (self false y)

      read : ∀ y (p : Fin k) {ℓ} → lab (punchIn j p) ≡ ℓ → Zᶜ false y ℓ ≡ y p
      read y p lp = trans (cong (Zᶜ false y) (sym lp))
        (trans (rd (insertᵃ j false y) (punchIn j p))
               (insertᵃ-punchIn j false y p))

      kept : ∀ y ℓ → Ret ℓ ≡ true → ℓ ≢ v → Zᶜ true y ℓ ≡ Zᶜ false y ℓ
      kept y ℓ R ℓ≢v = trans (cong (Zᶜ true y) (sym (proj₂ (fd ℓ R))))
        (trans (rd (insertᵃ j true y) (proj₁ (fd ℓ R)))
          (trans (insertᵃ-off j (proj₁ (fd ℓ R)) j≢p true false y)
            (trans (sym (rd (insertᵃ j false y) (proj₁ (fd ℓ R))))
                   (cong (Zᶜ false y) (proj₂ (fd ℓ R))))))
        where
        j≢p : j ≢ proj₁ (fd ℓ R)
        j≢p e = ℓ≢v (trans (sym (proj₂ (fd ℓ R)))
                           (trans (cong lab (sym e)) lj))

      dfl : ∀ c y ℓ → Ret ℓ ≡ false → Zᶜ c y ℓ ≡ dflt ℓ (Zᶜ c y)
      dfl c y ℓ R = df (insertᵃ j c y) ℓ R

      -- A removed label whose fixed value is the same at both paths.

      fixed : ∀ y ℓ → Ret ℓ ≡ false →
              dflt ℓ (Zᶜ true y) ≡ dflt ℓ (Zᶜ false y) →
              Zᶜ true y ℓ ≡ Zᶜ false y ℓ
      fixed y ℓ R e = trans (dfl true y ℓ R) (trans e (sym (dfl false y ℓ R)))

  ----------------------------------------------------------------------
  -- One [HH] and one [Elim]: the new invariants

  -- After [HH] at y_j (label v) with y_i ← q and [Elim] of y_i (label
  -- u), the path-sum's paths are read at y_j = 0, y_i = q; v and u are
  -- removed, with the values the rules fixed.

  private
    module Advance {Ret Ret′ : Lbl m → Bool} {k : ℕ}
      (lab : Fin (suc (suc k)) → Lbl m) (ρ : Assign (suc (suc k)) → LAssign m)
      (rd : ∀ y p → ρ y (lab p) ≡ y p)
      (df : ∀ y ℓ → Ret ℓ ≡ false → ρ y ℓ ≡ dflt ℓ (ρ y))
      (fd : ∀ ℓ → Ret ℓ ≡ true → Σ (Fin (suc (suc k))) (λ p → lab p ≡ ℓ))
      (on : ∀ p → Ret (lab p) ≡ true)
      (ij : ∀ p q → lab p ≡ lab q → p ≡ q)
      (j : Fin (suc (suc k))) (i : Fin (suc k)) (q : Assign (suc k) → Bool)
      {v u : Lbl m} (lj : lab j ≡ v) (li : lab (punchIn j i) ≡ u)
      (dv : ∀ Z → dflt v Z ≡ false)
      (du : ∀ y → dflt u (ρ (insertᵃ j false
                    (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ]))) ≡
                  q (insertᵃ i false y))
      (Rv : Ret′ v ≡ false) (Ru : Ret′ u ≡ false)
      (R′ : ∀ ℓ → ℓ ≢ v → ℓ ≢ u → Ret′ ℓ ≡ Ret ℓ)
      where

      σ : Assign k → Assign (suc (suc k))
      σ y = insertᵃ j false (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ])

      lab″ : Fin k → Lbl m
      lab″ p = lab (punchIn j (punchIn i p))

      ρ″ : Assign k → LAssign m
      ρ″ y = ρ (σ y)

      reads″ : ∀ y p → ρ″ y (lab″ p) ≡ y p
      reads″ y p = trans (rd (σ y) (punchIn j (punchIn i p)))
        (trans (insertᵃ-punchIn j false
                  (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ])
                  (punchIn i p))
          (trans (≔-there (insertᵃ i false y) (q (insertᵃ i false y))
                          (punchInᵢ≢i i p))
                 (insertᵃ-punchIn i false y p)))

      dflts″ : ∀ y ℓ → Ret′ ℓ ≡ false → ρ″ y ℓ ≡ dflt ℓ (ρ″ y)
      dflts″ y ℓ R = go (ℓ ≟ˡ v) (ℓ ≟ˡ u)
        where
        go : Dec (ℓ ≡ v) → Dec (ℓ ≡ u) → ρ″ y ℓ ≡ dflt ℓ (ρ″ y)
        go (yes e) _ = trans (cong (ρ″ y) (trans e (sym lj)))
          (trans (rd (σ y) j)
            (trans (insertᵃ-here j false
                     (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ]))
                   (sym (trans (cong (λ t → dflt t (ρ″ y)) e) (dv (ρ″ y))))))
        go (no _) (yes e) = trans (cong (ρ″ y) (trans e (sym li)))
          (trans (rd (σ y) (punchIn j i))
            (trans (insertᵃ-punchIn j false
                     (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ]) i)
              (trans (≔-here (insertᵃ i false y) i (q (insertᵃ i false y)))
                     (sym (trans (cong (λ t → dflt t (ρ″ y)) e) (du y))))))
        go (no ℓ≢v) (no ℓ≢u) = df (σ y) ℓ (trans (sym (R′ ℓ ℓ≢v ℓ≢u)) R)

      find″ : ∀ ℓ → Ret′ ℓ ≡ true → Σ (Fin k) (λ p → lab″ p ≡ ℓ)
      find″ ℓ R =
        punchOut i≢p₁ ,
        trans (cong (λ t → lab (punchIn j t)) (punchIn-punchOut i≢p₁))
              (trans (cong lab (punchIn-punchOut j≢p)) (proj₂ found))
        where
        ℓ≢v : ℓ ≢ v
        ℓ≢v e = t≢f (trans (sym R) (trans (cong Ret′ e) Rv))

        ℓ≢u : ℓ ≢ u
        ℓ≢u e = t≢f (trans (sym R) (trans (cong Ret′ e) Ru))

        found : Σ (Fin (suc (suc k))) (λ p → lab p ≡ ℓ)
        found = fd ℓ (trans (sym (R′ ℓ ℓ≢v ℓ≢u)) R)

        j≢p : j ≢ proj₁ found
        j≢p e = ℓ≢v (trans (sym (proj₂ found)) (trans (cong lab (sym e)) lj))

        i≢p₁ : i ≢ punchOut j≢p
        i≢p₁ e = ℓ≢u (trans (sym (proj₂ found))
          (trans (cong lab (sym (punchIn-punchOut j≢p)))
                 (trans (cong (λ t → lab (punchIn j t)) (sym e)) li)))

      only″ : ∀ p → Ret′ (lab″ p) ≡ true
      only″ p = trans (R′ (lab″ p) ≢v ≢u) (on (punchIn j (punchIn i p)))
        where
        ≢v : lab″ p ≢ v
        ≢v e = punchInᵢ≢i j (punchIn i p) (ij _ _ (trans e (sym lj)))

        ≢u : lab″ p ≢ u
        ≢u e = punchInᵢ≢i i p
          (punchIn-injective j (punchIn i p) i (ij _ _ (trans e (sym li))))

      inj″ : ∀ p p′ → lab″ p ≡ lab″ p′ → p ≡ p′
      inj″ p p′ e = punchIn-injective i p p′
        (punchIn-injective j (punchIn i p) (punchIn i p′) (ij _ _ e))

  ----------------------------------------------------------------------
  -- The reduction of a written path-sum

  -- Everything below is about one path-sum ξ₀ with the circuit's
  -- values, known through tr₀.

  module Reduce
    (ξ₀ : PathSum (m ℕ+ m) (hs-norm (m ℕ+ m)) (hs-norm (m ℕ+ m)))
    (tr₀ : Tracks ξ₀ (λ Y → Fblk (ρ₀ g s Y)) (λ w Y → Gblk w (ρ₀ g s Y)))
    where

    --------------------------------------------------------------------
    -- A stage of the reduction

    -- Ret says which labels are still path variables.

    record State (Ret : Lbl m → Bool) : Set where
      constructor stage
      field
        size   : ℕ
        ξ      : PathSum (m ℕ+ m) size size
        lab    : Fin size → Lbl m
        ρ      : Assign size → LAssign m
        chain  : ξ₀ ⟶ᴷ* ξ
        tracks : Tracks ξ (λ y → Fblk (ρ y)) (λ w y → Gblk w (ρ y))
        reads  : ∀ y p → ρ y (lab p) ≡ y p
        dflts  : ∀ y ℓ → Ret ℓ ≡ false → ρ y ℓ ≡ dflt ℓ (ρ y)
        find   : ∀ ℓ → Ret ℓ ≡ true → Σ (Fin size) (λ p → lab p ≡ ℓ)
        only   : ∀ p → Ret (lab p) ≡ true
        inj    : ∀ p q → lab p ≡ lab q → p ≡ q

    State-resp : ∀ {Ret Ret′} → (∀ ℓ → Ret ℓ ≡ Ret′ ℓ) →
                 State Ret → State Ret′
    State-resp h (stage sz ξ lab ρ ch tr rd df fd on ij) =
      stage sz ξ lab ρ ch tr rd (λ y ℓ R → df y ℓ (trans (h ℓ) R))
            (λ ℓ R → fd ℓ (trans (h ℓ) R))
            (λ p → trans (sym (h (lab p))) (on p)) ij

    -- A stage reads its paths through their values, so it is known by
    -- its values as a function of points (Positive.Values' VTracks).

    ρ-resp : ∀ {Ret : Lbl m → Bool} {sz} (lab : Fin sz → Lbl m)
             (ρ : Assign sz → LAssign m) →
             (∀ y p → ρ y (lab p) ≡ y p) →
             (∀ y ℓ → Ret ℓ ≡ false → ρ y ℓ ≡ dflt ℓ (ρ y)) →
             (∀ ℓ → Ret ℓ ≡ true → Σ (Fin sz) (λ p → lab p ≡ ℓ)) →
             ∀ y y′ → (∀ p → y p ≡ y′ p) → ∀ ℓ → ρ y ℓ ≡ ρ y′ ℓ
    ρ-resp {Ret} lab ρ rd df fd y y′ h ℓ = by ℓ (Ret ℓ) refl
      where
      pres : ∀ ℓ → Ret ℓ ≡ true → ρ y ℓ ≡ ρ y′ ℓ
      pres ℓ R = trans (cong (ρ y) (sym (proj₂ (fd ℓ R))))
        (trans (rd y (proj₁ (fd ℓ R)))
          (trans (h (proj₁ (fd ℓ R)))
            (trans (sym (rd y′ (proj₁ (fd ℓ R))))
                   (cong (ρ y′) (proj₂ (fd ℓ R))))))

      byA : ∀ t c → Ret (A₁ , t) ≡ c → ρ y (A₁ , t) ≡ ρ y′ (A₁ , t)
      byA t true  R = pres (A₁ , t) R
      byA t false R = trans (df y (A₁ , t) R) (sym (df y′ (A₁ , t) R))

      dflt-eq : ∀ ℓ → dflt ℓ (ρ y) ≡ dflt ℓ (ρ y′)
      dflt-eq (A₁ , t) = refl
      dflt-eq (B₁ , t) = refl
      dflt-eq (C₂ , t) = refl
      dflt-eq (D₂ , t) = cong (_xor sL t) (byA t (Ret (A₁ , t)) refl)
      dflt-eq (E₃ , t) = refl
      dflt-eq (H₃ , t) = refl

      by : ∀ ℓ c → Ret ℓ ≡ c → ρ y ℓ ≡ ρ y′ ℓ
      by ℓ true  R = pres ℓ R
      by ℓ false R = trans (df y ℓ R) (trans (dflt-eq ℓ) (sym (df y′ ℓ R)))

    vt-of : ∀ {Ret : Lbl m → Bool} {sz} {ξ : PathSum (m ℕ+ m) sz sz}
            (lab : Fin sz → Lbl m) (ρ : Assign sz → LAssign m) →
            (∀ y p → ρ y (lab p) ≡ y p) →
            (∀ y ℓ → Ret ℓ ≡ false → ρ y ℓ ≡ dflt ℓ (ρ y)) →
            (∀ ℓ → Ret ℓ ≡ true → Σ (Fin sz) (λ p → lab p ≡ ℓ)) →
            Tracks ξ (λ y → Fblk (ρ y)) (λ w y → Gblk w (ρ y)) →
            VTracks ξ (λ p → Fblk (ρ (lookup p)))
                      (λ w p → Gblk w (ρ (lookup p)))
    vt-of {Ret = Ret} lab ρ rd df fd tr = vtr (tracks-cong tr
      (λ y → Fblk-cong g s (same y))
      (λ w y → Gblk-cong {Z = ρ y} {Z′ = ρ (lookup (tabulate y))}
                         (λ t → same y (E₃ , t)) (λ t → same y (H₃ , t)) w))
      where
      same : ∀ y ℓ → ρ y ℓ ≡ ρ (lookup (tabulate y)) ℓ
      same y = ρ-resp {Ret} lab ρ rd df fd y (lookup (tabulate y))
                      (λ p → sym (lookup∘tabulate y p))

    -- ξ₀, every label present.

    initial : State (Ret₁ (λ _ → false))
    initial = stage (hs-norm (m ℕ+ m)) ξ₀ (lab₀ m) (ρ₀ g s) εᴷ tr₀
      (λ Y p → cong Y (pos₀-lab₀ m p))
      (λ Y ℓ R → ⊥-elim (t≢f (trans (sym (Ret₁-all ℓ)) R)))
      (λ ℓ _ → pos₀ m ℓ , lab₀-pos₀ m ℓ)
      (λ p → Ret₁-all (lab₀ m p))
      (λ p q e → trans (sym (pos₀-lab₀ m p))
                       (trans (cong (pos₀ m) e) (pos₀-lab₀ m q)))

    -- No label present: no path variable left.

    finish : State (Ret₃ (λ _ → true)) →
             Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → ξ₀ ⟶ᴷ* ζ)
    finish (stage zero    ξ lab ρ ch tr rd df fd on ij) = ξ , ch
    finish (stage (suc _) ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (t≢f (trans (sym (on zero)) (Ret₃-none (lab zero))))

    --------------------------------------------------------------------
    -- Pass 1: [HH] at b_i with d_i ← a_i ⊕ s_L,i, then [Elim] of d_i

    pass₁ : ∀ d i → d i ≡ false →
            State (Ret₁ d) → State (Ret₁ (d [ i ≔ true ]))
    pass₁ d i di (stage zero ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (fin0 (proj₁ (fd (B₁ , i) (cong not di))))
    pass₁ d i di (stage (suc zero) ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (one-slot lab fd (B₁ , i) (D₂ , i) (cong not di) (cong not di)
                       (blk≢ (λ ())))
    pass₁ d i di (stage (suc (suc k)) ξ lab ρ ch tr rd df fd on ij) =
      stage k ζ lab″ ρ″ (ch ◅◅ᴷ proj₁ res) (proj₂ res)
            reads″ dflts″ find″ only″ inj″
      where
      j : Fin (suc (suc k))
      j = proj₁ (fd (B₁ , i) (cong not di))

      lj : lab j ≡ (B₁ , i)
      lj = proj₂ (fd (B₁ , i) (cong not di))

      iu : Fin (suc k)
      iu = proj₁ (locate lab fd j lj (D₂ , i) (cong not di) (blk≢ (λ ())))

      li : lab (punchIn j iu) ≡ (D₂ , i)
      li = proj₂ (locate lab fd j lj (D₂ , i) (cong not di) (blk≢ (λ ())))

      a : Fin (suc k)
      a = proj₁ (locate lab fd j lj (A₁ , i) refl (blk≢ (λ ())))

      la : lab (punchIn j a) ≡ (A₁ , i)
      la = proj₂ (locate lab fd j lj (A₁ , i) refl (blk≢ (λ ())))

      a≢iu : a ≢ iu
      a≢iu e = blk≢ {b = A₁} {b′ = D₂} (λ ()) (trans (sym la)
                             (trans (cong (λ t → lab (punchIn j t)) e) li))

      q : Assign (suc k) → Bool
      q y = y a xor sL i

      Q : Poly (m ℕ+ m) (suc k)
      Q = liftᵉ (var y[ a ] ⊕ᵉ lit (sL i))

      open Flip lab ρ rd df fd j lj

      -- The labels other than b_i keep their values.

      A-kept : ∀ y t → Zᶜ true y (A₁ , t) ≡ Zᶜ false y (A₁ , t)
      A-kept y t = kept y (A₁ , t) refl (blk≢ (λ ()))

      B-kept : ∀ y t → t ≢ i → Zᶜ true y (B₁ , t) ≡ Zᶜ false y (B₁ , t)
      B-kept y t t≢i = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (B₁ , t) ≡ Zᶜ false y (B₁ , t)
        go false e = kept y (B₁ , t) (cong not e) (crd≢ t≢i)
        go true  e = fixed y (B₁ , t) (cong not e) refl

      C-kept : ∀ y t → Zᶜ true y (C₂ , t) ≡ Zᶜ false y (C₂ , t)
      C-kept y t = kept y (C₂ , t) refl (blk≢ (λ ()))

      D-kept : ∀ y t → Zᶜ true y (D₂ , t) ≡ Zᶜ false y (D₂ , t)
      D-kept y t = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (D₂ , t) ≡ Zᶜ false y (D₂ , t)
        go false e = kept y (D₂ , t) (cong not e) (blk≢ (λ ()))
        go true  e = fixed y (D₂ , t) (cong not e)
                           (cong (_xor sL t) (A-kept y t))

      E-kept : ∀ y t → Zᶜ true y (E₃ , t) ≡ Zᶜ false y (E₃ , t)
      E-kept y t = kept y (E₃ , t) refl (blk≢ (λ ()))

      H-kept : ∀ y t → Zᶜ true y (H₃ , t) ≡ Zᶜ false y (H₃ , t)
      H-kept y t = kept y (H₃ , t) refl (blk≢ (λ ()))

      -- The derivative in b_i is d_i ⊕ (a_i ⊕ s_L,i).

      dF : ∀ y → Fblk (Zᶜ true y) xor Fblk (Zᶜ false y) ≡ y iu xor q y
      dF y = trans
        (∂-b (Zᶜ true y) (Zᶜ false y) i (A-kept y) (B-kept y) (flipped y)
             (C-kept y) (D-kept y) (E-kept y) (H-kept y))
        (trans (cong₂ (λ p r → (p xor sL i) xor r)
                      (read y a la) (read y iu li))
               (xor-comm (y a xor sL i) (y iu)))

      dG : ∀ w y → Gblk w (Zᶜ true y) ≡ Gblk w (Zᶜ false y)
      dG w y = Gblk-cong {Z = Zᶜ true y} {Z′ = Zᶜ false y}
                         (E-kept y) (H-kept y) w

      ζ : PathSum (m ℕ+ m) k k
      ζ = elim-reduct (front iu (hhᴳ-reduct (front j ξ) iu Q))

      hq : ∀ x y → eval Q x y ≡ [ q y ]ᶻ
      hq x y = eval-liftᵉ (var y[ a ] ⊕ᵉ lit (sL i)) x y

      absQ : Absent y[ iu ] Q
      absQ = Absent-liftᵉ y[ iu ] (var y[ a ] ⊕ᵉ lit (sL i))
                          ((λ e → a≢iu (sym (y-inj e))) , tt)

      -- The step is in the class.  d_i is internal: the outputs read
      -- e and h only.  Q mentions a_i alone, and a_i Clifford makes
      -- d_i Clifford (Positive.ExistsLink).

      vt : VTracks ξ (λ p → Fblk (ρ (lookup p)))
                     (λ w p → Gblk w (ρ (lookup p)))
      vt = vt-of lab ρ rd df fd tr

      trχ : VTracks (front j ξ) (λ p → Fblk (ρ (lookup (unfr j p))))
                                (λ w p → Gblk w (ρ (lookup (unfr j p))))
      trχ = front-vtracks vt j

      bQ : BoolValued Q
      bQ x y = subst IsBit (sym (hq x y)) (IsBit-if (q y))

      open Safe trχ iu Q bQ absQ (hh-premise ξ tr j iu Q q hq dF)

      module L = Link g s lab ρ rd df fd i di

      int-d : Int (front j ξ) (suc iu)
      int-d = Indep⇒Int trχ (suc iu) (λ w →
        Indep-unfr {f = λ p → Gblk w (ρ (lookup p))} j (suc iu) (λ p →
          Gblk-cong {Z = ρ (lookup (set p (punchIn j iu) true))}
                    {Z′ = ρ (lookup (set p (punchIn j iu) false))}
            (λ t → kept′ p (E₃ , t) refl (blk≢ (λ ())))
            (λ t → kept′ p (H₃ , t) refl (blk≢ (λ ()))) w))
        where
        kept′ : ∀ p ℓ (R : Ret₁ d ℓ ≡ true) → ℓ ≢ (D₂ , i) →
                ρ (lookup (set p (punchIn j iu) true)) ℓ ≡
                ρ (lookup (set p (punchIn j iu) false)) ℓ
        kept′ p ℓ R ne =
          trans (L.keep-present (punchIn j iu) li p true ℓ R ne)
                (sym (L.keep-present (punchIn j iu) li p false ℓ R ne))

      cs : CliffSafe (front j ξ) iu Q
      cs = cs-from
        (Aff-cong (λ p → sym (q-agree (λ p → lookup p a xor sL i)
                                      (λ x p → hq x (lookup p)) p))
                  (Aff-xor (Aff-lookup a) (Aff-const (sL i))))
        forced
        where
        forced : ∀ v → ¬ Absent y[ v ] Q → Int (front j ξ) (suc v) →
                 Clifᶜ (phase (front j ξ)) (suc v) →
                 Clifᶜ (phase (front j ξ)) (suc iu)
        forced v ¬abs _ cl = by (v Fin.≟ a)
          where
          by : Dec (v ≡ a) → Clifᶜ (phase (front j ξ)) (suc iu)
          by (no v≢a)  = ⊥-elim (¬abs (Absent-liftᵉ y[ v ]
            (var y[ a ] ⊕ᵉ lit (sL i)) ((λ e → v≢a (y-inj e)) , tt)))
          by (yes v≡a) = Cl⇒Clif trχ (suc iu)
            (Cl-unfr {f = L.Fv} j (suc iu)
              (L.g-link (punchIn j a) (punchIn j iu) la li
                (Cl-unfr⁻¹ {f = L.Fv} j (suc a)
                  (Clif⇒Cl trχ (suc a)
                    (subst (λ u → Clifᶜ (phase (front j ξ)) (suc u)) v≡a cl)))))

      res = hh-elimᴷ ξ tr j iu Q q hq absQ dF dG (os-target int-d) cs

      -- d_i is fixed to a_i ⊕ s_L,i, a_i being still a path variable.

      σ₁ : Assign k → Assign (suc (suc k))
      σ₁ y =
        insertᵃ j false (insertᵃ iu false y [ iu ≔ q (insertᵃ iu false y) ])

      du : ∀ y → dflt (D₂ , i) (ρ (σ₁ y)) ≡ q (insertᵃ iu false y)
      du y = cong (_xor sL i) (trans (cong (ρ (σ₁ y)) (sym la))
        (trans (rd (σ₁ y) (punchIn j a))
          (trans (insertᵃ-punchIn j false
                    (insertᵃ iu false y [ iu ≔ q (insertᵃ iu false y) ]) a)
                 (≔-there (insertᵃ iu false y) (q (insertᵃ iu false y))
                          a≢iu))))

      R′ : ∀ ℓ → ℓ ≢ (B₁ , i) → ℓ ≢ (D₂ , i) →
           Ret₁ (d [ i ≔ true ]) ℓ ≡ Ret₁ d ℓ
      R′ (A₁ , t) _  _  = refl
      R′ (B₁ , t) ne _  =
        cong not (≔-there d true (λ e → ne (cong (B₁ ,_) e)))
      R′ (C₂ , t) _  _  = refl
      R′ (D₂ , t) _  ne =
        cong not (≔-there d true (λ e → ne (cong (D₂ ,_) e)))
      R′ (E₃ , t) _  _  = refl
      R′ (H₃ , t) _  _  = refl

      open Advance {Ret′ = Ret₁ (d [ i ≔ true ])} lab ρ rd df fd on ij j iu q
                   lj li (λ _ → refl) du
                   (cong not (≔-here d i true))
                   (cong not (≔-here d i true)) R′

    --------------------------------------------------------------------
    -- Pass 2: [HH] at c_i with e_i ← s_L,i, then [Elim] of e_i

    pass₂ : ∀ d i → d i ≡ false →
            State (Ret₂ d) → State (Ret₂ (d [ i ≔ true ]))
    pass₂ d i di (stage zero ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (fin0 (proj₁ (fd (C₂ , i) (cong not di))))
    pass₂ d i di (stage (suc zero) ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (one-slot lab fd (C₂ , i) (E₃ , i) (cong not di) (cong not di)
                       (blk≢ (λ ())))
    pass₂ d i di (stage (suc (suc k)) ξ lab ρ ch tr rd df fd on ij) =
      stage k ζ lab″ ρ″ (ch ◅◅ᴷ proj₁ res) (proj₂ res)
            reads″ dflts″ find″ only″ inj″
      where
      j : Fin (suc (suc k))
      j = proj₁ (fd (C₂ , i) (cong not di))

      lj : lab j ≡ (C₂ , i)
      lj = proj₂ (fd (C₂ , i) (cong not di))

      iu : Fin (suc k)
      iu = proj₁ (locate lab fd j lj (E₃ , i) (cong not di) (blk≢ (λ ())))

      li : lab (punchIn j iu) ≡ (E₃ , i)
      li = proj₂ (locate lab fd j lj (E₃ , i) (cong not di) (blk≢ (λ ())))

      q : Assign (suc k) → Bool
      q _ = sL i

      Q : Poly (m ℕ+ m) (suc k)
      Q = liftᵉ (lit (sL i))

      open Flip lab ρ rd df fd j lj

      -- The labels other than c_i keep their values; d is a ⊕ s_L.

      A-kept : ∀ y t → Zᶜ true y (A₁ , t) ≡ Zᶜ false y (A₁ , t)
      A-kept y t = kept y (A₁ , t) refl (blk≢ (λ ()))

      B-kept : ∀ y t → Zᶜ true y (B₁ , t) ≡ Zᶜ false y (B₁ , t)
      B-kept y t = fixed y (B₁ , t) refl refl

      C-kept : ∀ y t → t ≢ i → Zᶜ true y (C₂ , t) ≡ Zᶜ false y (C₂ , t)
      C-kept y t t≢i = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (C₂ , t) ≡ Zᶜ false y (C₂ , t)
        go false e = kept y (C₂ , t) (cong not e) (crd≢ t≢i)
        go true  e = fixed y (C₂ , t) (cong not e) refl

      D-kept : ∀ y t → Zᶜ true y (D₂ , t) ≡ Zᶜ false y (D₂ , t)
      D-kept y t = fixed y (D₂ , t) refl (cong (_xor sL t) (A-kept y t))

      E-kept : ∀ y t → Zᶜ true y (E₃ , t) ≡ Zᶜ false y (E₃ , t)
      E-kept y t = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (E₃ , t) ≡ Zᶜ false y (E₃ , t)
        go false e = kept y (E₃ , t) (cong not e) (blk≢ (λ ()))
        go true  e = fixed y (E₃ , t) (cong not e) refl

      H-kept : ∀ y t → Zᶜ true y (H₃ , t) ≡ Zᶜ false y (H₃ , t)
      H-kept y t = kept y (H₃ , t) refl (blk≢ (λ ()))

      -- The derivative in c_i is a_i ⊕ d_i ⊕ e_i = e_i ⊕ s_L,i.

      dF : ∀ y → Fblk (Zᶜ true y) xor Fblk (Zᶜ false y) ≡ y iu xor q y
      dF y = trans
        (∂-c (Zᶜ true y) (Zᶜ false y) i (A-kept y) (B-kept y) (C-kept y)
             (flipped y) (D-kept y) (E-kept y) (H-kept y))
        (trans (cong₂ (λ p r → (Zᶜ false y (A₁ , i) xor p) xor r)
                      (dfl false y (D₂ , i) refl) (read y iu li))
          (trans (cong (_xor y iu) (xor-cancelˡ (Zᶜ false y (A₁ , i)) (sL i)))
                 (xor-comm (sL i) (y iu))))

      dG : ∀ w y → Gblk w (Zᶜ true y) ≡ Gblk w (Zᶜ false y)
      dG w y = Gblk-cong {Z = Zᶜ true y} {Z′ = Zᶜ false y}
                         (E-kept y) (H-kept y) w

      ζ : PathSum (m ℕ+ m) k k
      ζ = elim-reduct (front iu (hhᴳ-reduct (front j ξ) iu Q))

      hq : ∀ x y → eval Q x y ≡ [ q y ]ᶻ
      hq x y = eval-liftᵉ (lit (sL i)) x y

      -- The step is in the class: Q mentions no variable.

      none : ∀ v → Absent y[ v ] Q
      none v = Absent-liftᵉ y[ v ] (lit (sL i)) tt

      vt : VTracks ξ (λ p → Fblk (ρ (lookup p)))
                     (λ w p → Gblk w (ρ (lookup p)))
      vt = vt-of lab ρ rd df fd tr

      bQ : BoolValued Q
      bQ x y = subst IsBit (sym (hq x y)) (IsBit-if (q y))

      open Safe (front-vtracks vt j) iu Q bQ (none iu)
                (hh-premise ξ tr j iu Q q hq dF)

      res = hh-elimᴷ ξ tr j iu Q q hq (none iu) dF dG (os-none none)
        (cs-from (Aff-cong (λ p → sym (q-agree (λ _ → sL i)
                                               (λ x p → hq x (lookup p)) p))
                           (Aff-const (sL i)))
                 (λ v ¬abs _ _ → ⊥-elim (¬abs (none v))))

      R′ : ∀ ℓ → ℓ ≢ (C₂ , i) → ℓ ≢ (E₃ , i) →
           Ret₂ (d [ i ≔ true ]) ℓ ≡ Ret₂ d ℓ
      R′ (A₁ , t) _  _  = refl
      R′ (B₁ , t) _  _  = refl
      R′ (C₂ , t) ne _  =
        cong not (≔-there d true (λ e → ne (cong (C₂ ,_) e)))
      R′ (D₂ , t) _  _  = refl
      R′ (E₃ , t) _  ne =
        cong not (≔-there d true (λ e → ne (cong (E₃ ,_) e)))
      R′ (H₃ , t) _  _  = refl

      open Advance {Ret′ = Ret₂ (d [ i ≔ true ])} lab ρ rd df fd on ij j iu q
                   lj li (λ _ → refl) (λ _ → refl)
                   (cong not (≔-here d i true))
                   (cong not (≔-here d i true)) R′

    --------------------------------------------------------------------
    -- Pass 3: [HH] at a_i with h_i ← s_R,i, then [Elim] of h_i

    pass₃ : ∀ d i → d i ≡ false →
            State (Ret₃ d) → State (Ret₃ (d [ i ≔ true ]))
    pass₃ d i di (stage zero ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (fin0 (proj₁ (fd (A₁ , i) (cong not di))))
    pass₃ d i di (stage (suc zero) ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (one-slot lab fd (A₁ , i) (H₃ , i) (cong not di) (cong not di)
                       (blk≢ (λ ())))
    pass₃ d i di (stage (suc (suc k)) ξ lab ρ ch tr rd df fd on ij) =
      stage k ζ lab″ ρ″ (ch ◅◅ᴷ proj₁ res) (proj₂ res)
            reads″ dflts″ find″ only″ inj″
      where
      j : Fin (suc (suc k))
      j = proj₁ (fd (A₁ , i) (cong not di))

      lj : lab j ≡ (A₁ , i)
      lj = proj₂ (fd (A₁ , i) (cong not di))

      iu : Fin (suc k)
      iu = proj₁ (locate lab fd j lj (H₃ , i) (cong not di) (blk≢ (λ ())))

      li : lab (punchIn j iu) ≡ (H₃ , i)
      li = proj₂ (locate lab fd j lj (H₃ , i) (cong not di) (blk≢ (λ ())))

      q : Assign (suc k) → Bool
      q _ = sR i

      Q : Poly (m ℕ+ m) (suc k)
      Q = liftᵉ (lit (sR i))

      open Flip lab ρ rd df fd j lj

      -- a_i flips, and d_i with it; the other labels keep their values.

      A-kept : ∀ y t → t ≢ i → Zᶜ true y (A₁ , t) ≡ Zᶜ false y (A₁ , t)
      A-kept y t t≢i = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (A₁ , t) ≡ Zᶜ false y (A₁ , t)
        go false e = kept y (A₁ , t) (cong not e) (crd≢ t≢i)
        go true  e = fixed y (A₁ , t) (cong not e) refl

      B-kept : ∀ y t → Zᶜ true y (B₁ , t) ≡ Zᶜ false y (B₁ , t)
      B-kept y t = fixed y (B₁ , t) refl refl

      C-kept : ∀ y t → Zᶜ true y (C₂ , t) ≡ Zᶜ false y (C₂ , t)
      C-kept y t = fixed y (C₂ , t) refl refl

      E-kept : ∀ y t → Zᶜ true y (E₃ , t) ≡ Zᶜ false y (E₃ , t)
      E-kept y t = fixed y (E₃ , t) refl refl

      H-kept : ∀ y t → Zᶜ true y (H₃ , t) ≡ Zᶜ false y (H₃ , t)
      H-kept y t = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (H₃ , t) ≡ Zᶜ false y (H₃ , t)
        go false e = kept y (H₃ , t) (cong not e) (blk≢ (λ ()))
        go true  e = fixed y (H₃ , t) (cong not e) refl

      -- The derivative in a_i (and d_i) is h_i ⊕ s_R,i.

      dF : ∀ y → Fblk (Zᶜ true y) xor Fblk (Zᶜ false y) ≡ y iu xor q y
      dF y = trans
        (∂-a (Zᶜ true y) (Zᶜ false y) i (A-kept y) (flipped y) (B-kept y)
             (C-kept y) (λ t → dfl true y (D₂ , t) refl)
             (λ t → dfl false y (D₂ , t) refl) (E-kept y) (H-kept y))
        (trans (cong (sR i xor_) (read y iu li)) (xor-comm (sR i) (y iu)))

      dG : ∀ w y → Gblk w (Zᶜ true y) ≡ Gblk w (Zᶜ false y)
      dG w y = Gblk-cong {Z = Zᶜ true y} {Z′ = Zᶜ false y}
                         (E-kept y) (H-kept y) w

      ζ : PathSum (m ℕ+ m) k k
      ζ = elim-reduct (front iu (hhᴳ-reduct (front j ξ) iu Q))

      hq : ∀ x y → eval Q x y ≡ [ q y ]ᶻ
      hq x y = eval-liftᵉ (lit (sR i)) x y

      -- The step is in the class: Q mentions no variable.

      none : ∀ v → Absent y[ v ] Q
      none v = Absent-liftᵉ y[ v ] (lit (sR i)) tt

      vt : VTracks ξ (λ p → Fblk (ρ (lookup p)))
                     (λ w p → Gblk w (ρ (lookup p)))
      vt = vt-of lab ρ rd df fd tr

      bQ : BoolValued Q
      bQ x y = subst IsBit (sym (hq x y)) (IsBit-if (q y))

      open Safe (front-vtracks vt j) iu Q bQ (none iu)
                (hh-premise ξ tr j iu Q q hq dF)

      res = hh-elimᴷ ξ tr j iu Q q hq (none iu) dF dG (os-none none)
        (cs-from (Aff-cong (λ p → sym (q-agree (λ _ → sR i)
                                               (λ x p → hq x (lookup p)) p))
                           (Aff-const (sR i)))
                 (λ v ¬abs _ _ → ⊥-elim (¬abs (none v))))

      R′ : ∀ ℓ → ℓ ≢ (A₁ , i) → ℓ ≢ (H₃ , i) →
           Ret₃ (d [ i ≔ true ]) ℓ ≡ Ret₃ d ℓ
      R′ (A₁ , t) ne _  =
        cong not (≔-there d true (λ e → ne (cong (A₁ ,_) e)))
      R′ (B₁ , t) _  _  = refl
      R′ (C₂ , t) _  _  = refl
      R′ (D₂ , t) _  _  = refl
      R′ (E₃ , t) _  _  = refl
      R′ (H₃ , t) _  ne =
        cong not (≔-there d true (λ e → ne (cong (H₃ ,_) e)))

      open Advance {Ret′ = Ret₃ (d [ i ≔ true ])} lab ρ rd df fd on ij j iu q
                   lj li (λ _ → refl) (λ _ → refl)
                   (cong not (≔-here d i true))
                   (cong not (≔-here d i true)) R′

    --------------------------------------------------------------------
    -- The three passes

    -- Every coordinate through pass 1, then pass 2, then pass 3.

    reduced : State (Ret₃ (λ _ → true))
    reduced =
      third (State-resp Ret₂₃ (second (State-resp Ret₁₂ (first initial))))
      where
      first : State (Ret₁ (λ _ → false)) → State (Ret₁ (λ _ → true))
      first = Sweep.all (λ d → State (Ret₁ d))
                        (λ h → State-resp (Ret₁-resp h)) pass₁

      second : State (Ret₂ (λ _ → false)) → State (Ret₂ (λ _ → true))
      second = Sweep.all (λ d → State (Ret₂ d))
                         (λ h → State-resp (Ret₂-resp h)) pass₂

      third : State (Ret₃ (λ _ → false)) → State (Ret₃ (λ _ → true))
      third = Sweep.all (λ d → State (Ret₃ d))
                        (λ h → State-resp (Ret₃-resp h)) pass₃

    -- A complete reduction of ξ₀.

    complete : Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → ξ₀ ⟶ᴷ* ζ)
    complete = finish reduced


  ----------------------------------------------------------------------
  -- The theorems

  -- Exists' three passes are a chain of the class, from every path-sum
  -- written as the circuit's ...

  written-admits : ∀ ξ₀ → Written g s ξ₀ →
                   Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → ξ₀ ⟶ᴷ* ζ)
  written-admits ξ₀ w = Reduce.complete ξ₀ (written-tracks g s ξ₀ w)

  -- ... and in particular from the circuit on |0⟩.

  hidden-shift-admits :
    Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → at0 (HS g s) ⟶ᴷ* ζ)
  hidden-shift-admits = written-admits (at0 (HS g s)) (written₀ g s)
