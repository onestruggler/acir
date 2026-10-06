------------------------------------------------------------------------
-- Presentations of groups
--
-- Reducing a path-sum known by its values with the linear rules
--
-- PathSum.HiddenShift.Stuck.Machine follows a path-sum through
-- figure 2's [HH] and [Elim] (PathSum.Full's _⟶ᶠ_, by
-- PathSum.HiddenShift.Track's hh-elim), the quotient being any Boolean
-- polynomial.  This module does the same for the linear calculus of
-- PathSum.Anywhere, _⟶ᵍ_ -- [Elim], and [HH] with a Z₂-linear quotient
-- c ⊕ ⨁S (PathSum.Reduction), the rules of lemma 4.3 and of the
-- polynomial-time normaliser -- so that a chain built here is a chain
-- of both calculi (PathSum.Full.⟶ᵍ*⇒⟶ᶠ*).
--
-- A step is [HH] at y_j (Anywhere's hhAt) whose quotient is the linear
-- form the derivative of the phase in y_j is, followed by [Elim] of
-- the variable y_i it substitutes for (elimAt).  The premises come
-- from values, by Möbius inversion (PathSum.Polynomial.Boolean's
-- ≈-from-values): the quotient of the phase by y_j is ½(c ⊕ ⨁S) modulo
-- 1 because the derivative of F is c ⊕ ⨁S at every point
-- (hh-premiseᴸ); the reduct's values are F and G read at y_j = 0 and
-- y_i = c ⊕ ⨁(S ∖ y_i) (eval-substʸ, from Polynomial.Properties'
-- eval-subst and eval-split); and y_i, overwritten, is absent from them
-- (par-off), which gives [Elim]'s premises.  On the side of the normal
-- forms the linear form is read off the derivative by
-- PathSum.Polynomial.ANF's linᴿ (LinOk, checked by refl), and the
-- reduct's values are the same normal forms as Machine's (nextF,
-- nextG).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Stuck.Linear (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc; punchOut)
open import Data.Fin.Properties using
  (_≟_; suc-injective; punchIn-punchOut)
open import Data.Fin.Subset using (Subset; ⊥; inside; outside; _∈_)
  renaming (_-_ to _∖_)
open import Data.Integer.Base using (ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣n⇒∣m*n)
open import Data.Integer.Properties using (+-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (_∷_; here; there; lookup)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Vec.Properties as Vec

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; tail-part)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Stuck.Machine M₀ using
  (tracks-cong; quotᴿ; nextᴿ; nextF; nextG; OutOk; xor-false;
   insertᵃ-cong; insertᵃ-≔; NoVar-unfront₀)
open import PathSum.HiddenShift.Track M₀ using
  (Tracks; phase-at; out-at; eval-/ʸ; eval-∖ʸ; out-premise; elim-tracks)
open import PathSum.Linear using
  (par; par-⊥; par-cong; par-∖; parᵐ; eval-liftXor)
open import PathSum.Polynomial using
  (Poly; Mon; y[_]; _∈ᵐ_; _∈ᵐ?_; _∖ᵐ_; 0ᴾ; liftXor; _·ᴾ_; _≈[_]_; NoVar;
   eval)
  renaming (subst to substᴸ)
open import PathSum.Polynomial.ANF using
  (RM; 𝟘; evalᴿ; evalᴿ-cong; derivᴿ; eval-derivᴿ; restrict;
   eval-restrict; substitute; eval-substitute; eqᴿ; eqᴿ-sound; allFin;
   allFin-sound; linᴿ; linᴿ-sound)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using (≈-from-values)
open import PathSum.Polynomial.Product using (eval-0ᴾ)
open import PathSum.Polynomial.Properties using
  (_∖ᵛ_; _/ᵛ_; eval-subst; eval-split; eval-off; eval-·ᴾ; eval-cong; v∉S∖v)
open import PathSum.Reorder using
  (insertᵃ; insertᵃ-here; insertᵃ-punchIn; front; frontᴾ; _/ʸ_)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using
  (_⟶ᵍ*_; εᵍ; _◅ᵍ_; _◅◅ᵍ_; elimAt; hhAt)
open import PathSum.Full.Canonical M using (pow∣½·2)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½; elim-reduct; hh-reduct)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Arithmetic of halves

private
  -- Half of an even number is a multiple of 2^M.

  half-even : ∀ t → (+ 2) ∣ t → pow M ∣ (½ * t)
  half-even t (divides r eq) =
    subst (pow M ∣_) (sym (trans (cong (½ *_) eq) (swap ½ r)))
          (∣n⇒∣m*n r pow∣½·2)
    where
    swap : ∀ h r → h * (r * (+ 2)) ≡ r * (h * (+ 2))
    swap = solve 2 (λ h r → h :* (r :* con (+ 2)) := r :* (h :* con (+ 2)))
                   refl

  -- Three bits with a ⊕ b = c: [a] - [b] - [c] is even.

  bits3 : ∀ a b c → a xor b ≡ c → (+ 2) ∣ (([ a ]ᶻ - [ b ]ᶻ) - [ c ]ᶻ)
  bits3 false false false _ = divides (+ 0) refl
  bits3 false true  true  _ = divides (- (+ 1)) refl
  bits3 true  false true  _ = divides (+ 0) refl
  bits3 true  true  false _ = divides (+ 0) refl
  bits3 false false true  ()
  bits3 false true  false ()
  bits3 true  false false ()
  bits3 true  true  true  ()


------------------------------------------------------------------------
-- Parities that do not read a position

-- A parity over a subset without i does not read position i.

par-off : (p : Subset k) (i : Fin k) → ¬ (i ∈ p) →
          (f g : Fin k → Bool) → (∀ j → j ≢ i → f j ≡ g j) →
          par p f ≡ par p g
par-off (inside  ∷ p) zero    i∉ f g h = contradiction here i∉
par-off (outside ∷ p) zero    i∉ f g h =
  par-cong p (λ j → h (suc j) (λ ()))
par-off (inside  ∷ p) (suc i) i∉ f g h = cong₂ _xor_ (h zero (λ ()))
  (par-off p i (λ i∈ → i∉ (there i∈)) (λ j → f (suc j)) (λ j → g (suc j))
           (λ j j≢i → h (suc j) (λ e → j≢i (suc-injective e))))
par-off (outside ∷ p) (suc i) i∉ f g h =
  par-off p i (λ i∈ → i∉ (there i∈)) (λ j → f (suc j)) (λ j → g (suc j))
          (λ j j≢i → h (suc j) (λ e → j≢i (suc-injective e)))


------------------------------------------------------------------------
-- Values through the linear [HH]

-- [HH] at y_j with the linear quotient c ⊕ ⨁S, from values.

hh-premiseᴸ : (ξ : PathSum n k (suc m)) {F : Assign (suc m) → Bool}
              {G : Fin n → Assign (suc m) → Bool} → Tracks ξ F G →
              (j : Fin (suc m)) (c : Bool) (S : Mon n m) →
              (∀ x y → F (insertᵃ j true y) xor F (insertᵃ j false y) ≡
                       c xor parᵐ S x y) →
              (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ liftXor c S)
hh-premiseᴸ ξ {F} tr j c S dF =
  ≈-from-values (phase ξ /ʸ j) (½ ·ᴾ liftXor c S) value
  where
  value : ∀ x y → pow M ∣ (eval (phase ξ /ʸ j) x y -
                           eval (½ ·ᴾ liftXor c S) x y)
  value x y = subst (pow M ∣_)
    (sym (trans (cong₂ _-_ (eval-/ʸ (phase ξ) j x y) rhs)
                (shape a b ½ A B C)))
    (∣m∣n⇒∣m+n
      (∣m∣n⇒∣m-n (phase-at tr x (insertᵃ j true y))
                 (phase-at tr x (insertᵃ j false y)))
      (half-even ((A - B) - C)
        (bits3 (F (insertᵃ j true y)) (F (insertᵃ j false y))
               (c xor parᵐ S x y) (dF x y))))
    where
    a b A B C : ℤ
    a = eval (phase ξ) x (insertᵃ j true y)
    b = eval (phase ξ) x (insertᵃ j false y)
    A = [ F (insertᵃ j true y) ]ᶻ
    B = [ F (insertᵃ j false y) ]ᶻ
    C = [ c xor parᵐ S x y ]ᶻ

    rhs : eval (½ ·ᴾ liftXor c S) x y ≡ ½ * C
    rhs = trans (eval-·ᴾ ½ (liftXor c S) x y)
                (cong (½ *_) (eval-liftXor c S x y))

    shape : ∀ a b h A B C →
            (a - b) - h * C ≡
            ((a - h * A) - (b - h * B)) + h * ((A - B) - C)
    shape = solve 6 (λ a b h A B C →
      (a :- b) :- h :* C :=
      ((a :- h :* A) :- (b :- h :* B)) :+ h :* ((A :- B) :- C)) refl

private
  -- The parts of a polynomial with and without a variable do not
  -- read it.

  ∖ᵛ-off : (R : Poly n m) (i : Fin m) → ∀ γ → y[ i ] ∈ᵐ γ →
           (R ∖ᵛ y[ i ]) γ ≡ (+ 0)
  ∖ᵛ-off R i γ i∈ with y[ i ] ∈ᵐ? γ
  ... | yes _ = refl
  ... | no ¬p = contradiction i∈ ¬p

  /ᵛ-off : (R : Poly n m) (i : Fin m) → ∀ γ → y[ i ] ∈ᵐ γ →
           (R /ᵛ y[ i ]) γ ≡ (+ 0)
  /ᵛ-off R i γ i∈ with y[ i ] ∈ᵐ? γ
  ... | yes _ = refl
  ... | no ¬p = contradiction i∈ ¬p

-- Substituting c ⊕ ⨁S for y_i is reading the value with y_i set to
-- the value of c ⊕ ⨁S.

eval-substʸ : (R : Poly n m) (i : Fin m) (c : Bool) (S : Mon n m)
              (x : Fin n → Bool) (y : Fin m → Bool) →
              eval (substᴸ R y[ i ] c S) x y ≡
              eval R x (y [ i ≔ c xor parᵐ S x y ])
eval-substʸ R i c S x y = trans (eval-subst R y[ i ] c S x y)
  (sym (trans (eval-split R y[ i ] x y′)
    (cong₂ _+_
      (sym (eval-off (R ∖ᵛ y[ i ]) i (∖ᵛ-off R i) x y y′ agree))
      (cong₂ _*_
        (trans (cong (λ t → if t then + 1 else + 0) (≔-here y i v))
               (sym (eval-liftXor c S x y)))
        (sym (eval-off (R /ᵛ y[ i ]) i (/ᵛ-off R i) x y y′ agree))))))
  where
  v : Bool
  v = c xor parᵐ S x y

  y′ : Fin _ → Bool
  y′ = y [ i ≔ v ]

  agree : ∀ j → ¬ (j ≡ i) → y j ≡ y′ j
  agree j j≢i = sym (≔-there y v j≢i)


------------------------------------------------------------------------
-- The linear form of a derivative

-- The derivative of the phase in y_j is linear and mentions y_i.

private
  linCheck : Fin (suc k) → Maybe (Bool × Subset (suc k)) → Bool
  linCheck i nothing        = false
  linCheck i (just (c , β)) = lookup β i

  linCheck-sound : (i : Fin (suc k)) (mb : Maybe (Bool × Subset (suc k))) →
                   linCheck i mb ≡ true →
                   Σ Bool (λ c → Σ (Subset (suc k)) (λ β →
                     (mb ≡ just (c , β)) × (lookup β i ≡ inside)))
  linCheck-sound i (just (c , β)) e = c , β , refl , e

LinOk : Fin (suc (suc k)) → Fin (suc k) → RM (suc (suc k)) → Bool
LinOk j i p = linCheck i (linᴿ (derivᴿ j p))

private
  -- Inserting either bit leaves the other positions alone.

  insertᵃ-off : (i : Fin (suc k)) (b b′ : Bool) (y : Fin k → Bool) →
                ∀ p → p ≢ i → insertᵃ i b y p ≡ insertᵃ i b′ y p
  insertᵃ-off i b b′ y p p≢i =
    trans (cong (insertᵃ i b y) (sym (punchIn-punchOut i≢p)))
      (trans (insertᵃ-punchIn i b y (punchOut i≢p))
        (trans (sym (insertᵃ-punchIn i b′ y (punchOut i≢p)))
               (cong (insertᵃ i b′ y) (punchIn-punchOut i≢p))))
    where
    i≢p : i ≢ p
    i≢p e = p≢i (sym e)


------------------------------------------------------------------------
-- One step

module ReduceL {N K K′ : ℕ} (ξ₀ : PathSum N K K′) where

  -- A stage: a path-sum reached from ξ₀ by the linear rules, with the
  -- values pF and pG.

  record StageL (k : ℕ) (pF : RM k) (pG : Fin N → RM k) : Set where
    constructor stageL
    field
      ξ      : PathSum N k k
      chain  : ξ₀ ⟶ᵍ* ξ
      tracks : Tracks ξ (evalᴿ pF) (λ w → evalᴿ (pG w))

  open StageL public

  -- [HH] at y_j with y_i ← the linear quotient, then [Elim] of y_i.

  stepL : ∀ {k} {pF : RM (suc (suc k))} {pG : Fin N → RM (suc (suc k))} →
          StageL (suc (suc k)) pF pG →
          (j : Fin (suc (suc k))) (i : Fin (suc k)) →
          LinOk j i pF ≡ true → OutOk j pG ≡ true →
          StageL k (nextF j i pF) (nextG j i pF pG)
  stepL {k} {pF} {pG} (stageL ξ ch tr) j i okL okG =
    stageL _ (ch ◅◅ᵍ (s₁ ◅ᵍ s₂ ◅ᵍ εᵍ))
      (tracks-cong (elim-tracks ζ₁ tr₁ i) (value pF) (λ w → value (pG w)))
    where
    ex = linCheck-sound i (linᴿ (derivᴿ j pF)) okL

    c : Bool
    c = proj₁ ex

    β : Subset (suc k)
    β = proj₁ (proj₂ ex)

    lin : linᴿ (derivᴿ j pF) ≡ just (c , β)
    lin = proj₁ (proj₂ (proj₂ ex))

    i∈β : lookup β i ≡ inside
    i∈β = proj₂ (proj₂ (proj₂ ex))

    S : Mon N (suc k)
    S = ⊥ , β

    yi∈S : y[ i ] ∈ᵐ S
    yi∈S = Vec.lookup⇒[]= i β i∈β

    -- The derivative of the phase in y_j is c ⊕ ⨁S.

    dF : ∀ x y → evalᴿ pF (insertᵃ j true y) xor evalᴿ pF (insertᵃ j false y) ≡
                 c xor parᵐ S x y
    dF x y = trans (sym (eval-derivᴿ j pF y))
      (trans (linᴿ-sound (derivᴿ j pF) lin y)
             (cong (λ t → c xor (t xor par β y)) (sym (par-⊥ x))))

    dG : ∀ w y → evalᴿ (pG w) (insertᵃ j true y) ≡
                 evalᴿ (pG w) (insertᵃ j false y)
    dG w y = xor-false (trans (sym (eval-derivᴿ j (pG w) y))
      (cong (λ t → evalᴿ t y)
            (eqᴿ-sound (derivᴿ j (pG w)) 𝟘
                       (allFin-sound (λ w′ → eqᴿ (derivᴿ j (pG w′)) 𝟘) okG w))))

    ζ₁ : PathSum N (suc (suc k)) (suc k)
    ζ₁ = hh-reduct (front j ξ) i c S

    s₁ = hhAt ξ j i c S yi∈S (hh-premiseᴸ ξ tr j c S dF)
           (λ w → NoVar-unfront₀ j (out ξ w) (out-premise ξ tr j dG w))

    -- The reduct reads the values at y_j = 0, y_i = c ⊕ ⨁(S ∖ y_i).

    v₁ : Assign (suc k) → Bool
    v₁ y = c xor par (β ∖ i) y

    σ₁ : Assign (suc k) → Assign (suc (suc k))
    σ₁ y = insertᵃ j false (y [ i ≔ v₁ y ])

    val₁ : ∀ (P : Poly N (suc (suc k))) x y →
           eval (substᴸ (tail-part (frontᴾ j P)) y[ i ] c (S ∖ᵐ y[ i ])) x y ≡
           eval P x (σ₁ y)
    val₁ P x y = trans (eval-substʸ (tail-part (frontᴾ j P)) i c (S ∖ᵐ y[ i ]) x y)
      (trans (eval-∖ʸ P j x (y [ i ≔ c xor parᵐ (S ∖ᵐ y[ i ]) x y ]))
        (eval-cong P {x} {x} (λ _ → refl)
          (insertᵃ-cong j false (λ p → cong (λ b → (y [ i ≔ b ]) p)
            (cong (λ t → c xor (t xor par (β ∖ i) y)) (par-⊥ x))))))

    F₁ : Assign (suc k) → Bool
    F₁ y = evalᴿ pF (σ₁ y)

    G₁ : Fin N → Assign (suc k) → Bool
    G₁ w y = evalᴿ (pG w) (σ₁ y)

    tr₁ : Tracks ζ₁ F₁ G₁
    tr₁ = record
      { phase-at = λ x y →
          subst (λ t → pow M ∣ (t - ½ * [ F₁ y ]ᶻ)) (sym (val₁ (phase ξ) x y))
                (phase-at tr x (σ₁ y))
      ; out-at = λ w x y →
          trans (cong odd (val₁ (out ξ w) x y)) (out-at tr w x (σ₁ y))
      }

    -- y_i is overwritten, so the reduct's values do not read it.

    i∉ : ¬ (i ∈ (β ∖ i))
    i∉ = v∉S∖v S y[ i ]

    flat : ∀ b y p → σ₁ (insertᵃ i b y) p ≡
                     insertᵃ j false (insertᵃ i (v₁ (insertᵃ i false y)) y) p
    flat b y = insertᵃ-cong j false (λ p → trans
      (insertᵃ-≔ i b (v₁ (insertᵃ i b y)) y p)
      (cong (λ t → insertᵃ i (c xor t) y p)
            (par-off (β ∖ i) i i∉ (insertᵃ i b y) (insertᵃ i false y)
                     (insertᵃ-off i b false y))))

    flipF : ∀ y → F₁ (insertᵃ i true y) ≡ F₁ (insertᵃ i false y)
    flipF y = trans (evalᴿ-cong pF (flat true y))
                    (sym (evalᴿ-cong pF (flat false y)))

    flipG : ∀ w y → G₁ w (insertᵃ i true y) ≡ G₁ w (insertᵃ i false y)
    flipG w y = trans (evalᴿ-cong (pG w) (flat true y))
                      (sym (evalᴿ-cong (pG w) (flat false y)))

    premise₂ : (phase ζ₁ /ʸ i) ≈[ pow M ] 0ᴾ
    premise₂ = ≈-from-values (phase ζ₁ /ʸ i) 0ᴾ value₂
      where
      value₂ : ∀ x y → pow M ∣ (eval (phase ζ₁ /ʸ i) x y - eval 0ᴾ x y)
      value₂ x y = subst (pow M ∣_) eq d
        where
        a b t : ℤ
        a = eval (phase ζ₁) x (insertᵃ i true y)
        b = eval (phase ζ₁) x (insertᵃ i false y)
        t = ½ * [ F₁ (insertᵃ i false y) ]ᶻ

        d : pow M ∣ ((a - t) - (b - t))
        d = ∣m∣n⇒∣m-n
          (subst (λ u → pow M ∣ (a - ½ * [ u ]ᶻ)) (flipF y)
                 (phase-at tr₁ x (insertᵃ i true y)))
          (phase-at tr₁ x (insertᵃ i false y))

        shape₂ : ∀ a b t → (a - t) - (b - t) ≡ a - b
        shape₂ = solve 3 (λ a b t → (a :- t) :- (b :- t) := a :- b) refl

        eq : (a - t) - (b - t) ≡ eval (phase ζ₁ /ʸ i) x y - eval 0ᴾ x y
        eq = trans (shape₂ a b t) (sym (trans
          (cong₂ _-_ (eval-/ʸ (phase ζ₁) i x y) (eval-0ᴾ x y))
          (+-identityʳ (a - b))))

    s₂ = elimAt ζ₁ i premise₂
           (λ w → NoVar-unfront₀ i (out ζ₁ w) (out-premise ζ₁ tr₁ i flipG w))

    -- The values after [Elim] are the normal forms nextᴿ.

    qval : ∀ y → v₁ (insertᵃ i false y) ≡ evalᴿ (quotᴿ j i pF) y
    qval y = sym (trans (eval-restrict i false (derivᴿ j pF) y)
      (trans (linᴿ-sound (derivᴿ j pF) lin (insertᵃ i false y))
        (cong (c xor_) (trans (par-∖ (insertᵃ i false y) (Vec.lookup⇒[]= i β i∈β))
          (trans (cong (par (β ∖ i) (insertᵃ i false y) xor_)
                       (insertᵃ-here i false y))
                 (xor-identityʳ _))))))

    value : ∀ r y → evalᴿ r (σ₁ (insertᵃ i false y)) ≡ evalᴿ (nextᴿ j i pF r) y
    value r y = trans (evalᴿ-cong r (flat false y))
      (sym (trans (eval-substitute i (quotᴿ j i pF) (restrict j false r) y)
        (trans (eval-restrict j false r (insertᵃ i (evalᴿ (quotᴿ j i pF) y) y))
          (evalᴿ-cong r (insertᵃ-cong j false (λ p →
            cong (λ t → insertᵃ i t y p) (sym (qval y))))))))
