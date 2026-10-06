------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.1 for path-sums with constant inputs (Amy, QPL 2018)
--
-- Definition 2.1 lets an input be a Boolean constant, and the paper's
-- partial isometries are typically of that kind: a qubit initialised in
-- |0⟩ or |1⟩.  PathSum.Signature writes such a path-sum σ ⊢ ξ.  Its
-- operator is ξ's on the inputs σ admits and 0 elsewhere (ampˢ), and
-- definition 2.3 for it is ≋ˢ.  Lemma 4.1 for it says: if the admitted
-- columns are well formed, σ ⊢ ξ is the identity on the inputs σ
-- admits, (σ ⊢ ξ) ≋ˢ (σ ⊢ idPS), exactly when the restricted sum is 1
-- at every admitted input (lemma-4-1ˢ).  Both conditions read the
-- admitted columns only:
--
--   * WellFormedˢ: every admitted column has trace-form norm at most
--     1, PathSum.Isometry's WellFormed on those columns.  The other
--     columns of ampˢ are 0, so this says every column of the signed
--     operator has norm at most 1 (WellFormedˢ⇔columns).
--   * Restriction-idˢ: amp ξ x x = √2^k ζ⁰ at every admitted x.  With
--     the constants written into the path-sum (PathSum.Signature's
--     inline) this is the paper's restriction f(x, y) = x, where x
--     carries the constants (Restriction-idˢ⇔inline).
--
-- The proof is PathSum.Isometry's, one column at a time
-- (column-off-diagonal): a diagonal entry √2^k spends the column's
-- whole budget 2^k, so its other entries vanish.  The forward direction
-- needs no hypothesis (lemma-4-1ˢ⇒).  Without constants nothing changes:
-- on ⌜ ξ ⌝ (every wire a variable) the two conditions are WellFormed
-- and Restriction-id (WellFormedˢ-vars, Restriction-idˢ-vars) and ≋ˢ
-- is ≋ (PathSum.Signature's ≋ˢ⇔≋), so lemma-4-1ˢ restates
-- PathSum.Isometry's lemma-4-1.
--
-- Definition 2.4 for σ ⊢ ξ asks its operator, extended by zero, to be a
-- partial isometry (PartialIsometricˢ; on ⌜ ξ ⌝ it is
-- PathSum.PartialIsometry's PartialIsometric, PartialIsometricˢ-vars).
-- The quadratic argument of PathSum.PartialIsometry, run on the columns
-- of any matrix, shows that it implies WellFormedˢ
-- (PartialIsometricˢ⇒WellFormedˢ).  So lemma 4.1 holds for path-sums
-- with constant inputs under the paper's own hypothesis
-- (lemma-4-1ˢ-partial).
--
-- Two examples.  PathSum.Compose.Counterexample's erase = |x⟩ ↦ |0⟩ is
-- not the identity (erase-not-id), but with its input the constant 0
-- it is (erase-signed: |0⟩ ↦ |0⟩), which lemma-4-1ˢ reads off the one
-- admitted diagonal entry.  And the hypothesis is needed here too:
-- PathSum.Isometry.Counterexample's tied dupᵗ = |x⟩ ↦ |x⟩ + |x ⊕ 1⟩,
-- with the constant 0, has the restriction of the identity and is not
-- it (lemma-4-1ˢ-needs-WellFormed).  Any ≋ between path-sums is a ≋ˢ
-- under every signature (≋⇒≋ˢ).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; _^_; z≤n)

module PathSum.Signature.Isometry (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (zero)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _*_; _≤_; +≤+)
open import Data.Integer.Properties using
  (+-assoc; +-identityˡ; +-inverseˡ; *-identityʳ; *-identityˡ; *-zeroˡ;
   +-monoʳ-≤; ≤-refl; ≤-trans; ≤-reflexive; ≤-antisym)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using (same; same-true; same-≗)
open import PathSum.AssignSum using
  (Σᶻ; RespectsZ; Σᶻ-cong; Σᶻ-point; Σᶻ-≥0; Σᶻ-≡0; Σᶻ-0)
open import PathSum.Base using (PathSum; idPS)
open import PathSum.Compose.Counterexample M₀ using
  (erase; aᵉ; real-erase; WellFormed-∘-fails)
open import PathSum.Compose.Properties M₀ using (amp-≗ˣ)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; _·ᴬ_; zpow; zpow-0≢0ᴬ; coeff; coeff-map; coeff-·ᴬ;
   scale; scale-map)
open import PathSum.Denotation M₀ using
  (Assign; amp; _≋_; amp-idPS; amp-≗)
open import PathSum.Hermitian M₀ using
  (Σᵃ; Σᵃ-cong; inner; inner-cong; inner-herm; inner-coeff0; coeff-Σᵃ;
   Σᶻ-term≤)
open import PathSum.Isometry M₀ using
  (WellFormed; Restriction-id; lemma-4-1⇒; amp-no-path; idPS-diagonal)
open import PathSum.Isometry.Counterexample M₀ using
  (dup; dupᵗ; amp-dup; dupᵗ≋dup; dupᵗ-restriction)
open import PathSum.Norm M₀ using
  (‖_‖²; ‖‖²-cong; ‖‖²-≥0; ‖‖²-zero; ‖‖²-scale; ‖zpow0‖²; ‖0ᴬ‖²)
open import PathSum.PartialIsometry M₀ using (gram; PartialIsometric; quad)
open import PathSum.Ring M₀ using
  (_⊛_; conj; ⊛-cong; ·ᴬ-cong; coeff0²≤‖‖²; ‖‖²-coeff0)
open import PathSum.Signature M₀ using
  (Signature; Agrees; agrees?; Signed; _⊢_; sig; ps; ampˢ; ampˢ-in;
   ampˢ-out; ampˢ-≗ˣ; ampˢ-⌜⌝; _≋ˢ_; ≋ˢ-sym; ≋ˢ-trans; ≋ˢ⇔on; vars;
   vars-agrees; ⌜_⌝; inline; pin; pin-agrees; amp-inline; at;
   Agrees-at; scale-0ᴬ)

private
  variable
    n k m k′ m′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- One column at a time

private
  -- A masked term of a non-negative summand is non-negative.

  if-≥0 : ∀ b {t} → 0ℤ ≤ t → 0ℤ ≤ (if b then 0ℤ else t)
  if-≥0 true  _   = ≤-refl
  if-≥0 false t≥0 = t≥0

  -- Whatever a spends of a budget a, it has nothing left to spend.

  cancel≤ : ∀ a b → a + b ≤ a → b ≤ 0ℤ
  cancel≤ a b h = ≤-trans (≤-reflexive (sym drop))
    (≤-trans (+-monoʳ-≤ (- a) h) (≤-reflexive (+-inverseˡ a)))
    where
    drop : - a + (a + b) ≡ b
    drop = trans (sym (+-assoc (- a) a b))
                 (trans (cong (_+ b) (+-inverseˡ a)) (+-identityˡ b))

-- PathSum.Isometry's budget argument reads one column: a column of norm
-- at most 2^k whose diagonal entry is √2^k ζ⁰ vanishes off the
-- diagonal.

column-off-diagonal : (ξ : PathSum n k m) (x : Assign n) →
                      Σᶻ (λ z → ‖ amp ξ x z ‖²) ≤ + (2 ^ k) →
                      amp ξ x x ≐ scale k (zpow 0ℤ) →
                      ∀ z → same x z ≡ false → amp ξ x z ≐ 0ᴬ
column-off-diagonal {n = n} {k = k} ξ x wf rid z ne =
  ‖‖²-zero (amp ξ x z)
    (trans (sym (cong (λ b → if b then 0ℤ else f z) ne))
           (Σᶻ-≡0 rest rest≥0 rest-resp Σrest≡0 z))
  where
  f : Assign n → ℤ
  f u = ‖ amp ξ x u ‖²

  f-resp : RespectsZ f
  f-resp u v u≗v = ‖‖²-cong (amp-≗ ξ x u≗v)

  rest : Assign n → ℤ
  rest u = if same x u then 0ℤ else f u

  rest≥0 : ∀ u → 0ℤ ≤ rest u
  rest≥0 u = if-≥0 (same x u) (‖‖²-≥0 (amp ξ x u))

  rest-resp : RespectsZ rest
  rest-resp u v u≗v = cong₂ (λ b t → if b then 0ℤ else t)
    (same-≗ (λ _ → refl) u≗v) (f-resp u v u≗v)

  -- The diagonal term is the whole budget.

  diag : f x ≡ + (2 ^ k)
  diag = trans (‖‖²-cong rid)
    (trans (‖‖²-scale k (zpow 0ℤ))
      (trans (cong (λ t → (+ (2 ^ k)) * t) ‖zpow0‖²)
             (*-identityʳ (+ (2 ^ k)))))

  split : Σᶻ f ≡ + (2 ^ k) + Σᶻ rest
  split = trans (Σᶻ-point f f-resp x) (cong (_+ Σᶻ rest) diag)

  spent : + (2 ^ k) + Σᶻ rest ≤ + (2 ^ k)
  spent = ≤-trans (≤-reflexive (sym split)) wf

  Σrest≡0 : Σᶻ rest ≡ 0ℤ
  Σrest≡0 = ≤-antisym (cancel≤ (+ (2 ^ k)) (Σᶻ rest) spent)
                      (Σᶻ-≥0 rest rest≥0)


------------------------------------------------------------------------
-- The two conditions, on the admitted columns

-- Every admitted column has norm at most 1.

WellFormedˢ : Signed n k m → Set
WellFormedˢ {k = k} ξ =
  ∀ x → Agrees (sig ξ) x → Σᶻ (λ z → ‖ amp (ps ξ) x z ‖²) ≤ + (2 ^ k)

-- The restricted sum is 1 at every admitted input.

Restriction-idˢ : Signed n k m → Set
Restriction-idˢ {k = k} ξ =
  ∀ x → Agrees (sig ξ) x → amp (ps ξ) x x ≐ scale k (zpow 0ℤ)

-- WellFormedˢ bounds every column of the signed operator, the columns
-- σ does not admit being 0.

WellFormedˢ⇔columns : (ξ : Signed n k m) →
                      WellFormedˢ ξ ⇔
                      (∀ x → Σᶻ (λ z → ‖ ampˢ ξ x z ‖²) ≤ + (2 ^ k))
WellFormedˢ⇔columns {k = k} ξ = mk⇔ to from
  where
  to : WellFormedˢ ξ → ∀ x → Σᶻ (λ z → ‖ ampˢ ξ x z ‖²) ≤ + (2 ^ k)
  to wf x = by (agrees? (sig ξ) x)
    where
    by : Dec (Agrees (sig ξ) x) → Σᶻ (λ z → ‖ ampˢ ξ x z ‖²) ≤ + (2 ^ k)
    by (yes a) = ≤-trans
      (≤-reflexive (Σᶻ-cong (λ z → ‖‖²-cong (ampˢ-in ξ a z)))) (wf x a)
    by (no na) = ≤-trans
      (≤-reflexive (trans (Σᶻ-cong (λ z →
         trans (‖‖²-cong (ampˢ-out ξ na z)) ‖0ᴬ‖²)) Σᶻ-0))
      (+≤+ z≤n)

  from : (∀ x → Σᶻ (λ z → ‖ ampˢ ξ x z ‖²) ≤ + (2 ^ k)) → WellFormedˢ ξ
  from h x a = ≤-trans
    (≤-reflexive (Σᶻ-cong (λ z → ‖‖²-cong (≐-sym (ampˢ-in ξ a z))))) (h x)

-- A WellFormed path-sum is WellFormedˢ under every signature.

WellFormed⇒WellFormedˢ : (σ : Signature n) (ξ : PathSum n k m) →
                         WellFormed ξ → WellFormedˢ (σ ⊢ ξ)
WellFormed⇒WellFormedˢ σ ξ wf x _ = wf x

-- With the constants written in, the restriction is the paper's
-- f(x, y) = x, the input x carrying the constants.

Restriction-idˢ⇔inline :
  (σ : Signature n) (ξ : PathSum n k m) →
  Restriction-idˢ (σ ⊢ ξ) ⇔
  (∀ x → amp (inline σ ξ) x (pin σ x) ≐ scale k (zpow 0ℤ))
Restriction-idˢ⇔inline σ ξ = mk⇔
  (λ rid x → amp-inline σ ξ x (pin σ x) ∙ rid (pin σ x) (pin-agrees σ x))
  (λ h x a → amp-≗ˣ ξ (λ i → sym (a i)) x
             ∙ amp-≗ ξ (pin σ x) (λ i → sym (a i))
             ∙ ≐-sym (amp-inline σ ξ x (pin σ x))
             ∙ h x)

-- Without constants they are PathSum.Isometry's conditions.

WellFormedˢ-vars : (ξ : PathSum n k m) → WellFormedˢ ⌜ ξ ⌝ ⇔ WellFormed ξ
WellFormedˢ-vars ξ = mk⇔ (λ wf x → wf x (vars-agrees x)) (λ wf x _ → wf x)

Restriction-idˢ-vars : (ξ : PathSum n k m) →
                       Restriction-idˢ ⌜ ξ ⌝ ⇔ Restriction-id ξ
Restriction-idˢ-vars ξ =
  mk⇔ (λ rid x → rid x (vars-agrees x)) (λ rid x _ → rid x)


------------------------------------------------------------------------
-- Lemma 4.1 with constant inputs

-- The forward direction is ≋ˢ read on the admitted diagonal.

lemma-4-1ˢ⇒ : (σ : Signature n) (ξ : PathSum n k m) →
              (σ ⊢ ξ) ≋ˢ (σ ⊢ idPS) → Restriction-idˢ (σ ⊢ ξ)
lemma-4-1ˢ⇒ {k = k} σ ξ e x a =
  Equivalence.to (≋ˢ⇔on σ ξ idPS) e x x a ∙ scale-map k (amp-idPS x)

-- The converse spends WellFormedˢ, one admitted column at a time.

lemma-4-1ˢ⇐ : (σ : Signature n) (ξ : PathSum n k m) →
              WellFormedˢ (σ ⊢ ξ) → Restriction-idˢ (σ ⊢ ξ) →
              (σ ⊢ ξ) ≋ˢ (σ ⊢ idPS)
lemma-4-1ˢ⇐ {k = k} σ ξ wf rid =
  Equivalence.from (≋ˢ⇔on σ ξ idPS) (λ x z a → entry x z a (same x z) refl)
  where
  entry : ∀ x z → Agrees σ x → ∀ b → same x z ≡ b →
          amp ξ x z ≐ scale k (amp idPS x z)
  entry x z a true  eq =
    amp-≗ ξ x (λ w → sym (same-true x z eq w))
    ∙ rid x a
    ∙ scale-map k (≐-sym (amp-idPS x) ∙ amp-≗ idPS x (same-true x z eq))
  entry x z a false eq =
    column-off-diagonal ξ x (wf x a) (rid x a) z eq
    ∙ ≐-sym (scale-map k (amp-no-path idPS x z
                            (λ y → idPS-diagonal x y z) eq)
             ∙ scale-0ᴬ k)

lemma-4-1ˢ : (σ : Signature n) (ξ : PathSum n k m) →
             WellFormedˢ (σ ⊢ ξ) →
             ((σ ⊢ ξ) ≋ˢ (σ ⊢ idPS)) ⇔ Restriction-idˢ (σ ⊢ ξ)
lemma-4-1ˢ σ ξ wf = mk⇔ (lemma-4-1ˢ⇒ σ ξ) (lemma-4-1ˢ⇐ σ ξ wf)


------------------------------------------------------------------------
-- Definition 2.4 with constant inputs

-- The Gram matrix of the signed operator, and definition 2.4 for it,
-- as PathSum.PartialIsometry states them for amp.

gramˢ : Signed n k m → Assign n → Assign n → Amp
gramˢ ξ x x′ = inner (ampˢ ξ x) (ampˢ ξ x′)

PartialIsometricˢ : Signed n k m → Set
PartialIsometricˢ {n = n} {k = k} ξ =
  ∀ (x x′ : Assign n) →
  Σᵃ (λ x″ → gramˢ ξ x x″ ⊛ gramˢ ξ x″ x′) ≐ (+ (2 ^ k)) ·ᴬ gramˢ ξ x x′

-- Without constants it is definition 2.4 for the path-sum.

PartialIsometricˢ-vars : (ξ : PathSum n k m) →
                         PartialIsometricˢ ⌜ ξ ⌝ ⇔ PartialIsometric ξ
PartialIsometricˢ-vars {k = k} ξ = mk⇔
  (λ pi x x′ →
     ≐-sym (Σᵃ-cong (λ x″ → ⊛-cong (g≐ x x″) (g≐ x″ x′)))
     ∙ pi x x′ ∙ ·ᴬ-cong (+ (2 ^ k)) (g≐ x x′))
  (λ pi x x′ →
     Σᵃ-cong (λ x″ → ⊛-cong (g≐ x x″) (g≐ x″ x′))
     ∙ pi x x′ ∙ ·ᴬ-cong (+ (2 ^ k)) (≐-sym (g≐ x x′)))
  where
  g≐ : ∀ x x′ → gramˢ ⌜ ξ ⌝ x x′ ≐ gram ξ x x′
  g≐ x x′ = inner-cong {ψ = ampˢ ⌜ ξ ⌝ x} {ψ′ = amp ξ x}
                       {φ = ampˢ ⌜ ξ ⌝ x′} {φ′ = amp ξ x′}
                       (ampˢ-⌜⌝ ξ x) (ampˢ-⌜⌝ ξ x′)

-- PathSum.PartialIsometry's quadratic argument, for any matrix given
-- by its columns A x: if the Gram matrix squares to b times itself,
-- every column has norm at most b.  With t the norm of column x,
-- t² ≤ ‖G_xx‖² ≤ Σ_x″ ‖G_xx″‖² = b·t.

private
  columns-bounded :
    (A : Assign n → Assign n → Amp) (b : ℕ) →
    (∀ x {u v : Assign n} → (∀ i → u i ≡ v i) →
     inner (A x) (A u) ≐ inner (A x) (A v)) →
    (∀ x x′ → Σᵃ (λ x″ → inner (A x) (A x″) ⊛ inner (A x″) (A x′)) ≐
              (+ b) ·ᴬ inner (A x) (A x′)) →
    ∀ x → Σᶻ (λ z → ‖ A x z ‖²) ≤ + b
  columns-bounded {n = n} A b resp pi x =
    ≤-trans (≤-reflexive (sym diag)) (quad t b t≥0 t²≤)
    where
    g : Assign n → Amp
    g x″ = inner (A x) (A x″)

    t : ℤ
    t = coeff (g x) 0ℤ

    diag : t ≡ Σᶻ (λ z → ‖ A x z ‖²)
    diag = inner-coeff0 (A x)

    square : Σᵃ (λ x″ → g x″ ⊛ conj (g x″)) ≐ (+ b) ·ᴬ g x
    square i = trans
      (Σᵃ-cong (λ x″ → ⊛-cong {a = g x″} {a′ = g x″}
                              (λ _ → refl) (inner-herm (A x) (A x″))) i)
      (pi x x i)

    sum-sq : Σᶻ (λ x″ → ‖ g x″ ‖²) ≡ (+ b) * t
    sum-sq = trans (sym (Σᶻ-cong (λ x″ → ‖‖²-coeff0 (g x″))))
      (trans (sym (coeff-Σᵃ (λ x″ → g x″ ⊛ conj (g x″)) 0ℤ))
        (trans (coeff-map square 0ℤ) (coeff-·ᴬ (+ b) (g x) 0ℤ)))

    resp′ : RespectsZ (λ x″ → ‖ g x″ ‖²)
    resp′ u v u≗v = ‖‖²-cong (resp x u≗v)

    t²≤ : t * t ≤ (+ b) * t
    t²≤ = ≤-trans (coeff0²≤‖‖² (g x))
      (≤-trans (Σᶻ-term≤ (λ x″ → ‖ g x″ ‖²) resp′
                         (λ x″ → ‖‖²-≥0 (g x″)) x)
               (≤-reflexive sum-sq))

    t≥0 : 0ℤ ≤ t
    t≥0 = ≤-trans (Σᶻ-≥0 (λ z → ‖ A x z ‖²) (λ z → ‖‖²-≥0 (A x z)))
                  (≤-reflexive (sym diag))

-- Definition 2.4 for the signed operator implies WellFormedˢ ...

PartialIsometricˢ⇒WellFormedˢ : (ξ : Signed n k m) →
                                PartialIsometricˢ ξ → WellFormedˢ ξ
PartialIsometricˢ⇒WellFormedˢ {k = k} ξ pi =
  Equivalence.from (WellFormedˢ⇔columns ξ)
    (columns-bounded (ampˢ ξ) (2 ^ k)
      (λ x {u} {v} u≗v →
         inner-cong {ψ = ampˢ ξ x} {ψ′ = ampˢ ξ x}
                    {φ = ampˢ ξ u} {φ′ = ampˢ ξ v}
                    (λ _ _ → refl) (ampˢ-≗ˣ ξ u≗v))
      pi)

-- ... so lemma 4.1 holds under the paper's own hypothesis.

lemma-4-1ˢ-partial : (σ : Signature n) (ξ : PathSum n k m) →
                     PartialIsometricˢ (σ ⊢ ξ) →
                     ((σ ⊢ ξ) ≋ˢ (σ ⊢ idPS)) ⇔ Restriction-idˢ (σ ⊢ ξ)
lemma-4-1ˢ-partial σ ξ pi =
  lemma-4-1ˢ σ ξ (PartialIsometricˢ⇒WellFormedˢ (σ ⊢ ξ) pi)


------------------------------------------------------------------------
-- Equivalence carries over to every signature

≋⇒≋ˢ : (σ : Signature n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
       ξ ≋ ζ → (σ ⊢ ξ) ≋ˢ (σ ⊢ ζ)
≋⇒≋ˢ σ ξ ζ e = Equivalence.from (≋ˢ⇔on σ ξ ζ) (λ x z _ → e x z)


------------------------------------------------------------------------
-- Examples

private
  x₀ x₁ : Assign 1
  x₀ _ = false
  x₁ _ = true

  -- The input 0 is the one the constant 0 admits.

  x₀-agrees : Agrees (at zero false) x₀
  x₀-agrees = Equivalence.from (Agrees-at zero false x₀) refl

-- erase = |x⟩ ↦ |0⟩ is not the identity: its entry from 1 to 1 is 0.

erase-not-id : ¬ (erase ≋ idPS)
erase-not-id e = zpow-0≢0ᴬ
  (≐-sym (lemma-4-1⇒ erase e x₁) ∙ real-erase x₁ x₁ ∙ zero-entry)
  where
  zero-entry : aᵉ true true ·ᴬ zpow 0ℤ ≐ 0ᴬ
  zero-entry i = *-zeroˡ (zpow 0ℤ i)

-- With its input the constant 0 it is |0⟩ ↦ |0⟩, the identity there.
-- Its columns have norm 1, and its one admitted diagonal entry is 1.

erase-signed : (at zero false ⊢ erase) ≋ˢ (at zero false ⊢ idPS)
erase-signed =
  Equivalence.from
    (lemma-4-1ˢ (at zero false) erase
                (WellFormed⇒WellFormedˢ (at zero false) erase wf))
    rid
  where
  wf : WellFormed erase
  wf = proj₁ (proj₂ WellFormed-∘-fails)

  one-entry : ∀ b → b ≡ false → aᵉ b b ·ᴬ zpow 0ℤ ≐ scale 0 (zpow 0ℤ)
  one-entry false refl i = *-identityˡ (zpow 0ℤ i)

  rid : Restriction-idˢ (at zero false ⊢ erase)
  rid x a = real-erase x x
            ∙ one-entry (x zero) (Equivalence.to (Agrees-at zero false x) a)

-- Without WellFormedˢ the lemma fails with constants too: dupᵗ, with
-- the constant 0, has the restriction of the identity, but its entry
-- from 0 to 1 is not 0.

lemma-4-1ˢ-needs-WellFormed :
  Restriction-idˢ (at zero false ⊢ dupᵗ) ×
  ¬ ((at zero false ⊢ dupᵗ) ≋ˢ (at zero false ⊢ idPS))
lemma-4-1ˢ-needs-WellFormed = (λ x _ → dupᵗ-restriction x) , not-id
  where
  σ : Signature 1
  σ = at zero false

  not-id : ¬ ((σ ⊢ dupᵗ) ≋ˢ (σ ⊢ idPS))
  not-id e = zpow-0≢0ᴬ (λ i →
    trans (sym (amp-dup x₀ x₁ i)) (trans (at01 i) (off i)))
    where
    e′ : (σ ⊢ dup) ≋ˢ (σ ⊢ idPS)
    e′ = ≋ˢ-trans {ξ = σ ⊢ dup} {ζ = σ ⊢ dupᵗ} {χ = σ ⊢ idPS}
           (≋ˢ-sym {ξ = σ ⊢ dupᵗ} {ζ = σ ⊢ dup}
                   (≋⇒≋ˢ σ dupᵗ dup dupᵗ≋dup))
           e

    at01 : amp dup x₀ x₁ ≐ amp idPS x₀ x₁
    at01 = Equivalence.to (≋ˢ⇔on σ dup idPS) e′ x₀ x₁ x₀-agrees

    off : amp idPS x₀ x₁ ≐ 0ᴬ
    off = amp-no-path idPS x₀ x₁ (λ y → idPS-diagonal x₀ y x₁) refl
