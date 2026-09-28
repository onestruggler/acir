------------------------------------------------------------------------
-- Presentations of groups
--
-- Reducing a path-sum known by its values, one labelled variable at a
-- time
--
-- PathSum.HiddenShift.Exists reduces the hidden shift composite by the
-- rules [HH] and [Elim] of figure 2 (Amy, QPL 2018) at named
-- variables: each path variable carries a label, the path-sum's values
-- are functions of the labelled path, and each step is proved from the
-- derivative of those functions.  This module is that machine for any
-- labels, and for values that may depend on the inputs
-- (PathSum.HiddenShift.TrackX), so that the circuits of figure 3 --
-- whose path variables are more and differently ordered than the
-- composite's, and, in figure 3(b), whose phase reads a register of
-- symbolic inputs -- can be reduced by it.
--
-- The labels are any type L with decidable equality.  The values are F
-- (the phase is ½F modulo 1), G (the outputs modulo 2) and dflt (the
-- value a removed label keeps), all functions of the input x and the
-- labelled path Z : L → Bool.  A stage of a reduction of ξ₀ (State
-- Ret, where Ret says which labels are still path variables) is a
-- path-sum ξ with a chain ξ₀ ⟶ᶠ* ξ; a label for each of its variables
-- (lab: injective, every present label has a position -- find -- and
-- only present labels do -- only); and a map ρ from its paths to
-- labelled paths that reads a present label off the path (reads) and
-- gives a removed one its fixed value (dflts), such that ξ has the
-- values F and G of ρ (tracks).
--
-- One step (step) is [HH] at the variable labelled v with the variable
-- labelled u replaced by a quotient, then [Elim] of u.  The quotient is
-- an exclusive or of constants, inputs and labels other than u and v
-- still present (QExp, QOk), translated into the current positions.
-- The step's premises are about labelled paths only (Step): whenever
-- two labelled paths differ in v -- as far as present labels go,
-- removed ones having their fixed values (FlipAt) -- F changes by the
-- value of u xor the quotient and G does not change; v's fixed value
-- is 0 and u's is the quotient.  The positions of v and u are found
-- through the labels, never computed, and the rules' premises are
-- proved from values by Möbius inversion (TrackX.hh-elimˣ).  A stage
-- in which no label is present has no path variable left (finish).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Engine (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; punchIn; punchOut)
open import Data.Fin.Properties using
  (punchIn-injective; punchInᵢ≢i; punchIn-punchOut)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using (PathSum)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.TrackX M₀ using (Tracksˣ; hh-elimˣ)
open import PathSum.Polynomial using (Poly; x[_]; y[_])
open import PathSum.Polynomial.Boolean using
  (BExp; var; lit; _⊕ᵉ_; _∧ᵉ_; ⟦_⟧ᵉ; liftᵉ; eval-liftᵉ; _∉ᵉ_;
   Absent-liftᵉ)
open import PathSum.Reorder using
  (insertᵃ; insertᵃ-here; insertᵃ-punchIn; front)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Full M using (_⟶ᶠ*_; _◅◅ᶠ_)
open import PathSum.Reduction M using (elim-reduct)
open import PathSum.Reduction.General M using (hhᴳ-reduct)

private
  variable
    n m : ℕ
    L : Set


------------------------------------------------------------------------
-- Small facts

private
  fin0 : Fin 0 → ⊥
  fin0 ()

  t≢f : true ≢ false
  t≢f ()

  y-inj : ∀ {n k} {i j : Fin k} → y[_] {n} {k} i ≡ y[ j ] → i ≡ j
  y-inj refl = refl

  -- Setting y_j to either bit leaves the other positions alone.

  insertᵃ-off : ∀ {k} (j p : Fin (suc k)) → j ≢ p → (c c′ : Bool)
                (y : Assign k) → insertᵃ j c y p ≡ insertᵃ j c′ y p
  insertᵃ-off j p j≢p c c′ y = trans
    (cong (insertᵃ j c y) (sym (punchIn-punchOut j≢p)))
    (trans (insertᵃ-punchIn j c y (punchOut j≢p))
      (sym (trans (cong (insertᵃ j c′ y) (sym (punchIn-punchOut j≢p)))
                  (insertᵃ-punchIn j c′ y (punchOut j≢p)))))

-- A Boolean expression does not read a variable absent from it.

⟦⟧ᵉ-≔ : (e : BExp n m) {i : Fin m} → y[ i ] ∉ᵉ e →
        (x : Assign n) (y : Assign m) (b : Bool) →
        ⟦ e ⟧ᵉ x (y [ i ≔ b ]) ≡ ⟦ e ⟧ᵉ x y
⟦⟧ᵉ-≔ (var x[ w ]) _  x y b = refl
⟦⟧ᵉ-≔ (var y[ a ]) ne x y b =
  ≔-there y b (λ a≡i → ne (cong y[_] (sym a≡i)))
⟦⟧ᵉ-≔ (lit c)      _  x y b = refl
⟦⟧ᵉ-≔ (e₁ ⊕ᵉ e₂) (h₁ , h₂) x y b =
  cong₂ _xor_ (⟦⟧ᵉ-≔ e₁ h₁ x y b) (⟦⟧ᵉ-≔ e₂ h₂ x y b)
⟦⟧ᵉ-≔ (e₁ ∧ᵉ e₂) (h₁ , h₂) x y b =
  cong₂ _∧_ (⟦⟧ᵉ-≔ e₁ h₁ x y b) (⟦⟧ᵉ-≔ e₂ h₂ x y b)


------------------------------------------------------------------------
-- Quotients over labels

infixl 6 _q⊕_

-- An exclusive or of constants, inputs and labelled path variables.

data QExp (L : Set) (n : ℕ) : Set where
  qlit : Bool → QExp L n
  qin  : Fin n → QExp L n
  qvar : L → QExp L n
  _q⊕_ : QExp L n → QExp L n → QExp L n

⟦_⟧q : QExp L n → Assign n → (L → Bool) → Bool
⟦ qlit b    ⟧q x Z = b
⟦ qin w     ⟧q x Z = x w
⟦ qvar ℓ    ⟧q x Z = Z ℓ
⟦ e₁ q⊕ e₂ ⟧q x Z = ⟦ e₁ ⟧q x Z xor ⟦ e₂ ⟧q x Z

-- Every label the quotient reads is still a path variable, and is
-- neither of the two the step removes.

QOk : (L → Bool) → L → L → QExp L n → Set
QOk Ret v u (qlit b)    = ⊤
QOk Ret v u (qin w)     = ⊤
QOk Ret v u (qvar ℓ)    = (Ret ℓ ≡ true) × (ℓ ≢ v) × (ℓ ≢ u)
QOk Ret v u (e₁ q⊕ e₂) = QOk Ret v u e₁ × QOk Ret v u e₂


------------------------------------------------------------------------
-- The machine

-- For labels L, values F, G and fixed values dflt, reducing ξ₀.

module Machine {N : ℕ} {L : Set} (_≟ℓ_ : DecidableEquality L)
               (F : Assign N → (L → Bool) → Bool)
               (G : Fin N → Assign N → (L → Bool) → Bool)
               (dflt : Assign N → L → (L → Bool) → Bool)
               {K : ℕ} (ξ₀ : PathSum N K K) where

  ----------------------------------------------------------------------
  -- Two labelled paths that differ in one label

  -- Zt and Zf give v the values 1 and 0, agree on the other present
  -- labels, and give each removed label its fixed value.

  record FlipAt (Ret : L → Bool) (v : L) (x : Assign N)
                (Zt Zf : L → Bool) : Set where
    field
      flip-t : Zt v ≡ true
      flip-f : Zf v ≡ false
      kept   : ∀ ℓ → Ret ℓ ≡ true → ℓ ≢ v → Zt ℓ ≡ Zf ℓ
      dflt-t : ∀ ℓ → Ret ℓ ≡ false → Zt ℓ ≡ dflt x ℓ Zt
      dflt-f : ∀ ℓ → Ret ℓ ≡ false → Zf ℓ ≡ dflt x ℓ Zf

  open FlipAt public

  -- A label other than v keeps its value if it is present, or if it is
  -- removed and its fixed value is the same on both sides.

  kept-or-fixed : ∀ {Ret v x Zt Zf} → FlipAt Ret v x Zt Zf →
                  ∀ ℓ → ℓ ≢ v →
                  (Ret ℓ ≡ false → dflt x ℓ Zt ≡ dflt x ℓ Zf) →
                  Zt ℓ ≡ Zf ℓ
  kept-or-fixed {Ret} {x = x} {Zt} {Zf} fl ℓ ℓ≢v h = go (Ret ℓ) refl
    where
    go : ∀ b → Ret ℓ ≡ b → Zt ℓ ≡ Zf ℓ
    go true  e = kept fl ℓ e ℓ≢v
    go false e = trans (dflt-t fl ℓ e) (trans (h e) (sym (dflt-f fl ℓ e)))

  ----------------------------------------------------------------------
  -- A stage of the reduction

  record State (Ret : L → Bool) : Set where
    constructor stage
    field
      size   : ℕ
      ξ      : PathSum N size size
      lab    : Fin size → L
      ρ      : Assign N → Assign size → L → Bool
      chain  : ξ₀ ⟶ᶠ* ξ
      tracks : Tracksˣ ξ (λ x y → F x (ρ x y)) (λ w x y → G w x (ρ x y))
      reads  : ∀ x y p → ρ x y (lab p) ≡ y p
      dflts  : ∀ x y ℓ → Ret ℓ ≡ false → ρ x y ℓ ≡ dflt x ℓ (ρ x y)
      find   : ∀ ℓ → Ret ℓ ≡ true → Σ (Fin size) (λ p → lab p ≡ ℓ)
      only   : ∀ p → Ret (lab p) ≡ true
      inj    : ∀ p q → lab p ≡ lab q → p ≡ q

  State-resp : ∀ {Ret Ret′} → (∀ ℓ → Ret ℓ ≡ Ret′ ℓ) →
               State Ret → State Ret′
  State-resp h (stage sz ξ lab ρ ch tr rd df fd on ij) =
    stage sz ξ lab ρ ch tr rd (λ x y ℓ R → df x y ℓ (trans (h ℓ) R))
          (λ ℓ R → fd ℓ (trans (h ℓ) R))
          (λ p → trans (sym (h (lab p))) (on p)) ij

  -- No label present: no path variable left.

  finish : ∀ {Ret} → State Ret → (∀ ℓ → Ret ℓ ≡ false) →
           Σ (PathSum N 0 0) (λ ζ → ξ₀ ⟶ᶠ* ζ)
  finish (stage zero    ξ lab ρ ch tr rd df fd on ij) none = ξ , ch
  finish (stage (suc _) ξ lab ρ ch tr rd df fd on ij) none =
    ⊥-elim (t≢f (trans (sym (on zero)) (none (lab zero))))

  ----------------------------------------------------------------------
  -- Locating variables

  private
    -- A present label other than v is at a position other than v's.

    locate : ∀ {Ret : L → Bool} {k} (lab : Fin (suc k) → L) →
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

    one-slot : ∀ {Ret : L → Bool} (lab : Fin 1 → L) →
               (∀ ℓ → Ret ℓ ≡ true → Σ (Fin 1) (λ p → lab p ≡ ℓ)) →
               ∀ v u → Ret v ≡ true → Ret u ≡ true → v ≢ u → ⊥
    one-slot lab fd v u Rv Ru v≢u with fd v Rv | fd u Ru
    ... | zero , lv | zero , lu = v≢u (trans (sym lv) lu)

  ----------------------------------------------------------------------
  -- The path-sum with y_j set, read by label

  private
    module Flip {Ret : L → Bool} {k : ℕ}
                (lab : Fin (suc k) → L)
                (ρ : Assign N → Assign (suc k) → L → Bool)
                (rd : ∀ x y p → ρ x y (lab p) ≡ y p)
                (df : ∀ x y ℓ → Ret ℓ ≡ false → ρ x y ℓ ≡ dflt x ℓ (ρ x y))
                (fd : ∀ ℓ → Ret ℓ ≡ true → Σ (Fin (suc k)) (λ p → lab p ≡ ℓ))
                (j : Fin (suc k)) {v : L} (lj : lab j ≡ v) where

      Zᶜ : Bool → Assign N → Assign k → L → Bool
      Zᶜ c x y = ρ x (insertᵃ j c y)

      self : ∀ c x y → Zᶜ c x y v ≡ c
      self c x y = trans (cong (Zᶜ c x y) (sym lj))
                         (trans (rd x (insertᵃ j c y) j) (insertᵃ-here j c y))

      read : ∀ c x y (p : Fin k) {ℓ} → lab (punchIn j p) ≡ ℓ →
             Zᶜ c x y ℓ ≡ y p
      read c x y p lp = trans (cong (Zᶜ c x y) (sym lp))
        (trans (rd x (insertᵃ j c y) (punchIn j p))
               (insertᵃ-punchIn j c y p))

      kept′ : ∀ x y ℓ → Ret ℓ ≡ true → ℓ ≢ v →
              Zᶜ true x y ℓ ≡ Zᶜ false x y ℓ
      kept′ x y ℓ R ℓ≢v = trans (cong (Zᶜ true x y) (sym (proj₂ (fd ℓ R))))
        (trans (rd x (insertᵃ j true y) (proj₁ (fd ℓ R)))
          (trans (insertᵃ-off j (proj₁ (fd ℓ R)) j≢p true false y)
            (trans (sym (rd x (insertᵃ j false y) (proj₁ (fd ℓ R))))
                   (cong (Zᶜ false x y) (proj₂ (fd ℓ R))))))
        where
        j≢p : j ≢ proj₁ (fd ℓ R)
        j≢p e = ℓ≢v (trans (sym (proj₂ (fd ℓ R)))
                           (trans (cong lab (sym e)) lj))

      flipAt : ∀ x y → FlipAt Ret v x (Zᶜ true x y) (Zᶜ false x y)
      flipAt x y = record
        { flip-t = self true x y
        ; flip-f = self false x y
        ; kept   = kept′ x y
        ; dflt-t = λ ℓ R → df x (insertᵃ j true y) ℓ R
        ; dflt-f = λ ℓ R → df x (insertᵃ j false y) ℓ R
        }

      -- The quotient, over the variables left once y_j is gone.

      toB : ∀ {u} (e : QExp L N) → QOk Ret v u e → BExp N k
      toB (qlit b)    _               = lit b
      toB (qin w)     _               = var x[ w ]
      toB (qvar ℓ)    (R , ℓ≢v , _)   =
        var y[ proj₁ (locate lab fd j lj ℓ R ℓ≢v) ]
      toB (e₁ q⊕ e₂) (o₁ , o₂)       = toB e₁ o₁ ⊕ᵉ toB e₂ o₂

      eval-toB : ∀ {u} (e : QExp L N) (ok : QOk Ret v u e) (c : Bool) x
                 (y : Assign k) → ⟦ toB e ok ⟧ᵉ x y ≡ ⟦ e ⟧q x (Zᶜ c x y)
      eval-toB (qlit b)    _             c x y = refl
      eval-toB (qin w)     _             c x y = refl
      eval-toB (qvar ℓ)    (R , ℓ≢v , _) c x y =
        sym (read c x y (proj₁ (locate lab fd j lj ℓ R ℓ≢v))
                  (proj₂ (locate lab fd j lj ℓ R ℓ≢v)))
      eval-toB (e₁ q⊕ e₂) (o₁ , o₂)     c x y =
        cong₂ _xor_ (eval-toB e₁ o₁ c x y) (eval-toB e₂ o₂ c x y)

      absent-toB : ∀ {u} (e : QExp L N) (ok : QOk Ret v u e) (iu : Fin k) →
                   lab (punchIn j iu) ≡ u → y[ iu ] ∉ᵉ toB e ok
      absent-toB (qlit b)    _               iu li = tt
      absent-toB (qin w)     _               iu li = λ ()
      absent-toB (qvar ℓ)    (R , ℓ≢v , ℓ≢u) iu li e =
        ℓ≢u (trans (sym (proj₂ (locate lab fd j lj ℓ R ℓ≢v)))
               (trans (cong (λ t → lab (punchIn j t)) (sym (y-inj e))) li))
      absent-toB (e₁ q⊕ e₂) (o₁ , o₂)       iu li =
        absent-toB e₁ o₁ iu li , absent-toB e₂ o₂ iu li

  ----------------------------------------------------------------------
  -- One [HH] and one [Elim]: the new invariants

  -- After [HH] at y_j (label v) with y_i ← q and [Elim] of y_i (label
  -- u), the paths are read at y_j = 0, y_i = q; v and u are removed,
  -- with the values the rules fixed.

  private
    module Advance {Ret Ret′ : L → Bool} {k : ℕ}
      (lab : Fin (suc (suc k)) → L)
      (ρ : Assign N → Assign (suc (suc k)) → L → Bool)
      (rd : ∀ x y p → ρ x y (lab p) ≡ y p)
      (df : ∀ x y ℓ → Ret ℓ ≡ false → ρ x y ℓ ≡ dflt x ℓ (ρ x y))
      (fd : ∀ ℓ → Ret ℓ ≡ true → Σ (Fin (suc (suc k))) (λ p → lab p ≡ ℓ))
      (on : ∀ p → Ret (lab p) ≡ true)
      (ij : ∀ p q → lab p ≡ lab q → p ≡ q)
      (j : Fin (suc (suc k))) (i : Fin (suc k))
      (q : Assign N → Assign (suc k) → Bool)
      {v u : L} (lj : lab j ≡ v) (li : lab (punchIn j i) ≡ u)
      (dv : ∀ x Z → dflt x v Z ≡ false)
      (du : ∀ x y → dflt x u (ρ x (insertᵃ j false
                      (insertᵃ i false y [ i ≔ q x (insertᵃ i false y) ]))) ≡
                    q x (insertᵃ i false y))
      (Rv : Ret′ v ≡ false) (Ru : Ret′ u ≡ false)
      (R′ : ∀ ℓ → ℓ ≢ v → ℓ ≢ u → Ret′ ℓ ≡ Ret ℓ)
      where

      σ : Assign N → Assign k → Assign (suc (suc k))
      σ x y =
        insertᵃ j false (insertᵃ i false y [ i ≔ q x (insertᵃ i false y) ])

      lab″ : Fin k → L
      lab″ p = lab (punchIn j (punchIn i p))

      ρ″ : Assign N → Assign k → L → Bool
      ρ″ x y = ρ x (σ x y)

      reads″ : ∀ x y p → ρ″ x y (lab″ p) ≡ y p
      reads″ x y p = trans (rd x (σ x y) (punchIn j (punchIn i p)))
        (trans (insertᵃ-punchIn j false
                  (insertᵃ i false y [ i ≔ q x (insertᵃ i false y) ])
                  (punchIn i p))
          (trans (≔-there (insertᵃ i false y) (q x (insertᵃ i false y))
                          (punchInᵢ≢i i p))
                 (insertᵃ-punchIn i false y p)))

      dflts″ : ∀ x y ℓ → Ret′ ℓ ≡ false → ρ″ x y ℓ ≡ dflt x ℓ (ρ″ x y)
      dflts″ x y ℓ R = go (ℓ ≟ℓ v) (ℓ ≟ℓ u)
        where
        go : Dec (ℓ ≡ v) → Dec (ℓ ≡ u) → ρ″ x y ℓ ≡ dflt x ℓ (ρ″ x y)
        go (yes e) _ = trans (cong (ρ″ x y) (trans e (sym lj)))
          (trans (rd x (σ x y) j)
            (trans (insertᵃ-here j false
                     (insertᵃ i false y [ i ≔ q x (insertᵃ i false y) ]))
                   (sym (trans (cong (λ t → dflt x t (ρ″ x y)) e)
                               (dv x (ρ″ x y))))))
        go (no _) (yes e) = trans (cong (ρ″ x y) (trans e (sym li)))
          (trans (rd x (σ x y) (punchIn j i))
            (trans (insertᵃ-punchIn j false
                     (insertᵃ i false y [ i ≔ q x (insertᵃ i false y) ]) i)
              (trans (≔-here (insertᵃ i false y) i (q x (insertᵃ i false y)))
                     (sym (trans (cong (λ t → dflt x t (ρ″ x y)) e)
                                 (du x y))))))
        go (no ℓ≢v) (no ℓ≢u) =
          df x (σ x y) ℓ (trans (sym (R′ ℓ ℓ≢v ℓ≢u)) R)

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
  -- One step

  -- What the caller supplies for [HH] at v with u replaced by quot:
  -- both present and distinct, the derivative of F in v on labelled
  -- paths, G unchanged by v, and the fixed values of v and u.

  record Step (Ret : L → Bool) (v u : L) : Set where
    field
      v-on    : Ret v ≡ true
      u-on    : Ret u ≡ true
      v≢u     : v ≢ u
      quot    : QExp L N
      quot-ok : QOk Ret v u quot
      ∂F      : ∀ x Zt Zf → FlipAt Ret v x Zt Zf →
                F x Zt xor F x Zf ≡ Zf u xor ⟦ quot ⟧q x Zf
      ∂G      : ∀ x Zt Zf → FlipAt Ret v x Zt Zf →
                ∀ w → G w x Zt ≡ G w x Zf
      v-dflt  : ∀ x Z → dflt x v Z ≡ false
      u-dflt  : ∀ x Z → dflt x u Z ≡ ⟦ quot ⟧q x Z

  -- The step itself: two rules, v and u removed.

  step : ∀ {Ret v u} → State Ret → Step Ret v u →
         (Ret′ : L → Bool) → Ret′ v ≡ false → Ret′ u ≡ false →
         (∀ ℓ → ℓ ≢ v → ℓ ≢ u → Ret′ ℓ ≡ Ret ℓ) → State Ret′
  step {v = v} (stage zero ξ lab ρ ch tr rd df fd on ij) S Ret′ Rv Ru R′ =
    ⊥-elim (fin0 (proj₁ (fd v (Step.v-on S))))
  step {v = v} {u} (stage (suc zero) ξ lab ρ ch tr rd df fd on ij) S
       Ret′ Rv Ru R′ =
    ⊥-elim (one-slot lab fd v u (Step.v-on S) (Step.u-on S) (Step.v≢u S))
  step {Ret} {v} {u} (stage (suc (suc k)) ξ lab ρ ch tr rd df fd on ij) S
       Ret′ Rv Ru R′ =
    stage k ζ lab″ ρ″ (ch ◅◅ᶠ proj₁ res) (proj₂ res)
          reads″ dflts″ find″ only″ inj″
    where
    open Step S

    j : Fin (suc (suc k))
    j = proj₁ (fd v v-on)

    lj : lab j ≡ v
    lj = proj₂ (fd v v-on)

    iu : Fin (suc k)
    iu = proj₁ (locate lab fd j lj u u-on (λ e → v≢u (sym e)))

    li : lab (punchIn j iu) ≡ u
    li = proj₂ (locate lab fd j lj u u-on (λ e → v≢u (sym e)))

    open Flip lab ρ rd df fd j lj

    B : BExp N (suc k)
    B = toB quot quot-ok

    q : Assign N → Assign (suc k) → Bool
    q x y = ⟦ B ⟧ᵉ x y

    Q : Poly N (suc k)
    Q = liftᵉ B

    dF : ∀ x y → F x (Zᶜ true x y) xor F x (Zᶜ false x y) ≡ y iu xor q x y
    dF x y = trans (∂F x (Zᶜ true x y) (Zᶜ false x y) (flipAt x y))
      (cong₂ _xor_ (read false x y iu li)
                   (sym (eval-toB quot quot-ok false x y)))

    dG : ∀ w x y → G w x (Zᶜ true x y) ≡ G w x (Zᶜ false x y)
    dG w x y = ∂G x (Zᶜ true x y) (Zᶜ false x y) (flipAt x y) w

    ζ : PathSum N k k
    ζ = elim-reduct (front iu (hhᴳ-reduct (front j ξ) iu Q))

    res = hh-elimˣ ξ tr j iu Q q (λ x y → eval-liftᵉ B x y)
            (Absent-liftᵉ y[ iu ] B (absent-toB quot quot-ok iu li)) dF dG

    du′ : ∀ x y → dflt x u (ρ x (insertᵃ j false
                    (insertᵃ iu false y [ iu ≔ q x (insertᵃ iu false y) ]))) ≡
                  q x (insertᵃ iu false y)
    du′ x y = trans (u-dflt x _)
      (trans (sym (eval-toB quot quot-ok false x
                    (insertᵃ iu false y [ iu ≔ q x (insertᵃ iu false y) ])))
             (⟦⟧ᵉ-≔ B (absent-toB quot quot-ok iu li) x (insertᵃ iu false y)
                    (q x (insertᵃ iu false y))))

    open Advance {Ret′ = Ret′} lab ρ rd df fd on ij j iu q lj li v-dflt du′
                 Rv Ru R′
