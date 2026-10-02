------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary 4.4 for every circuit over {H, CNOT, R_k, R_k†}: the level
-- checked in the monad, and the equivalence bound in the volume (Amy,
-- QPL 2018)
--
-- PathSum.Cost.Gauss.Corollary decides, in polynomial time and by the
-- paper's route, whether ⟦ C ⟧ is the identity for a Clifford circuit
-- C over {H, CNOT, R_k, R_k†} -- level C ≤ 2, the largest k of an R_k
-- or R_k† in C -- and takes that level bound as a hypothesis, the
-- promise of corollary 4.4 ("if C is a Clifford-group quantum
-- circuit").  The program does not read the level.  Here the promise
-- is checked by the program itself, so that the procedure is total.
--
--  * levelᶜ computes the level in the monad: one step per gate, and one
--    more per R_k or R_k† for the maximum (value-levelᶜ: its value is
--    PathSum.CRK.Circuit.level; cost-levelᶜ: at most 2 |C|).
--
--  * decideᴷᶜ C reads the level, compares it with 2, and either
--    answers nothing (above 2: C is not syntactically Clifford, and
--    the elimination at order 2 is not a decision there) or runs
--    decideᴳᶜ and answers its verdict.  It is correct for every
--    circuit, with no hypothesis (decideᴷ-correct):
--
--      value (decideᴷᶜ C) ≡ just b  ⇔  level C ≤ 2 × (b ≡ true ⇔ ⟦ C ⟧ ≋ idPS),
--
--    it answers nothing exactly above level 2 (decideᴷ-nothing), and
--    within level 2 it answers just decideᴳᶜ's verdict (decideᴷ-agrees).
--    Its cost is at most 399 (n + |C| + 3)^11, and 399 (2 n |C| + 3)^11
--    in the volume, for every circuit (cost-decideᴷᶜ,
--    cost-decideᴷ-volume): the level costs at most 2 |C| and the
--    comparison one step, both absorbed by decideᴳᶜ's 398 B^11.
--    corollary-4-4-polytime-total packages the three, unconditionally.
--
--  * equivᴷᶜ C₁ C₂ builds the miter C₁ ++ C₂† (PathSum.Cost.Gauss.
--    Corollary.miterᴷᶜ) and runs decideᴷᶜ on it.  The level of the
--    miter is the larger of the two levels (PathSum.CRK.Adjoint's
--    level-++ and level-†), so checking it checks both circuits
--    (level-miter⇔): equivᴷ-correct says that the answer is just b
--    exactly when both circuits are Clifford and b says whether
--    ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧.  The cost is at most
--    401 (n + |C₁| + |C₂| + 3)^11 (cost-equivᴷᶜ) and
--    401 (2 n (|C₁| + |C₂|) + 3)^11 in the volume (cost-equivᴷ-volume);
--    equivalence-polytime-total packages the three.
--
--  * The equivalence bound of PathSum.Cost.Gauss.Corollary (equivᴳᶜ,
--    for two Clifford circuits, the levels a hypothesis) in the volume
--    n · (|C₁| + |C₂|): at most 400 (2 n (|C₁| + |C₂|) + 3)^11
--    (cost-equivᴳ-volume, packaged with correctness and the polynomial
--    bound as equivalence-polytime-gauss-volume).  A gate names a wire,
--    so n ≥ 1 as soon as one circuit has a gate, and then
--    n + |C₁| + |C₂| ≤ 2 n (|C₁| + |C₂|) (PathSum.Size.Sparse.volume-≤);
--    two empty circuits are answered in one step (two, for equivᴷᶜ).
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.  Conventions beyond PathSum.Cost's: the maximum
-- of a gate's k and the running level is one step, as is the
-- comparison of the level with 2 (word-RAM operations on naturals, as
-- PathSum.Cost charges counters).  The k of an R_k or R_k† is an
-- unbounded natural in PathSum.CRK.Circuit; charging one step for it
-- assumes that it fits in a machine word, as the other unit-cost
-- conventions assume their numbers small -- coefficients below 2^M,
-- counters that never exceed the size of the circuit.  (Only k ≤ M is
-- meaningful anyway: PathSum.CRK.Circuit interprets R_k for k > M as
-- R_M.)  Everything else is PathSum.Cost.Gauss.Corollary's.  The
-- bounds are upper bounds, not tight; they are opaque, with their
-- defining equations exported, and every cost lemma is proved at a
-- variable B first (CLAUDE.md's Cost pitfall).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Cost.Gauss.Total (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using
  (zero; _+_; _*_; _^_; _≤_; _⊔_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Properties.Equivalence using ()
  renaming (trans to ⇔-trans; sym to ⇔-sym)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (idPS)
open import PathSum.Cost
open import PathSum.Cost.Bound using (^-mono; ^-pos; B*B)
open import PathSum.Cost.Gauss.Corollary M₀ using
  (decideᴳᶜ; decideᴳ-correct; cost-decideᴳ-at; miterᴷᶜ; value-miterᴷᶜ;
   cost-miterᴷᶜ; length-miterᴷ; equivᴳᶜ; equivᴳ-correct; cost-equivᴳ-at;
   equivᴳBound; cost-equivᴳᶜ)
open import PathSum.CRK.Adjoint M using (_†; level-++; level-†; level-miter)
open import PathSum.CRK.Circuit M using (Gate; Circuit; level; ⟦_⟧)
open import PathSum.CRK.Miter M₀ using (miter)
open import PathSum.Denotation M₀ using (_≋_)
open import PathSum.Size.Sparse M using (volume-≤)

import Data.Nat.Properties as ℕ
import PathSum.CRK.Circuit

private
  module K = PathSum.CRK.Circuit M

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The level, in the monad

-- One step per gate, and one more for the maximum at an R_k or R_k†.

levelᶜ : Circuit n → Cost ℕ
levelᶜ []                  = pure 0
levelᶜ (K.H _ ∷ C)         = tick >> levelᶜ C
levelᶜ (K.CNOT _ _ _ ∷ C)  = tick >> levelᶜ C
levelᶜ (K.R k _ ∷ C)       = do
  tick
  ℓ ← levelᶜ C
  step (k ⊔ ℓ)
levelᶜ (K.R† k _ ∷ C)      = do
  tick
  ℓ ← levelᶜ C
  step (k ⊔ ℓ)

value-levelᶜ : (C : Circuit n) → value (levelᶜ C) ≡ level C
value-levelᶜ []                  = refl
value-levelᶜ (K.H _ ∷ C)         = value-levelᶜ C
value-levelᶜ (K.CNOT _ _ _ ∷ C)  = value-levelᶜ C
value-levelᶜ (K.R k _ ∷ C)       = cong (k ⊔_) (value-levelᶜ C)
value-levelᶜ (K.R† k _ ∷ C)      = cong (k ⊔_) (value-levelᶜ C)

private
  one-more : ∀ {a} L → a ≤ 2 * L → suc a ≤ 2 * suc L
  one-more L a≤ = ℕ.≤-trans (ℕ.n≤1+n _)
    (ℕ.≤-trans (s≤s (s≤s a≤)) (ℕ.≤-reflexive (sym (ℕ.*-suc 2 L))))

  two-more : ∀ {a} L → a ≤ 2 * L → suc (a + 1) ≤ 2 * suc L
  two-more {a} L a≤ = ℕ.≤-trans
    (s≤s (ℕ.≤-reflexive (ℕ.+-comm a 1)))
    (ℕ.≤-trans (s≤s (s≤s a≤)) (ℕ.≤-reflexive (sym (ℕ.*-suc 2 L))))

cost-levelᶜ : (C : Circuit n) → cost (levelᶜ C) ≤ 2 * length C
cost-levelᶜ []                 = z≤n
cost-levelᶜ (K.H _ ∷ C)        = one-more (length C) (cost-levelᶜ C)
cost-levelᶜ (K.CNOT _ _ _ ∷ C) = one-more (length C) (cost-levelᶜ C)
cost-levelᶜ (K.R _ _ ∷ C)      = two-more (length C) (cost-levelᶜ C)
cost-levelᶜ (K.R† _ _ ∷ C)     = two-more (length C) (cost-levelᶜ C)


------------------------------------------------------------------------
-- The total decision

-- Within level 2, decideᴳᶜ's verdict; above it, nothing.

answerᶜ : Bool → Circuit n → Cost (Maybe Bool)
answerᶜ true  C = just <$> decideᴳᶜ C
answerᶜ false C = pure nothing

decideᴷᶜ : Circuit n → Cost (Maybe Bool)
decideᴷᶜ C = do
  ℓ  ← levelᶜ C
  ok ← step (ℓ ≤ᵇ 2)
  answerᶜ ok C

-- Booleans with the same truth are equal.

private
  bool-⇔ : (v b : Bool) → (v ≡ true → b ≡ true) → (b ≡ true → v ≡ true) →
           v ≡ b
  bool-⇔ true  true  _ _ = refl
  bool-⇔ true  false f _ = sym (f refl)
  bool-⇔ false true  _ g = g refl
  bool-⇔ false false _ _ = refl

  nothing≢just : ∀ {b : Bool} → nothing ≡ just b → ⊥
  nothing≢just ()

  -- The comparison with 2, read as ≤.
  ≤ᵇ-true : ∀ {ℓ} → true ≡ (ℓ ≤ᵇ 2) → ℓ ≤ 2
  ≤ᵇ-true {ℓ} e = ℕ.≤ᵇ⇒≤ ℓ 2 (subst T e tt)

  ≤ᵇ-false : ∀ {ℓ} → false ≡ (ℓ ≤ᵇ 2) → ¬ (ℓ ≤ 2)
  ≤ᵇ-false e le = subst T (sym e) (ℕ.≤⇒≤ᵇ le)

-- Correct for every circuit: the answer is just b exactly when the
-- circuit is Clifford and b says whether ⟦ C ⟧ is the identity.

decideᴷ-correct : (C : Circuit n) (b : Bool) →
                  (value (decideᴷᶜ C) ≡ just b ⇔
                   (level C ≤ 2 × (b ≡ true ⇔ ⟦ C ⟧ ≋ idPS)))
decideᴷ-correct C b =
  at (value (levelᶜ C) ≤ᵇ 2) (cong (_≤ᵇ 2) (value-levelᶜ C))
  where
  at : (o : Bool) → o ≡ (level C ≤ᵇ 2) →
       (value (answerᶜ o C) ≡ just b ⇔
        (level C ≤ 2 × (b ≡ true ⇔ ⟦ C ⟧ ≋ idPS)))
  at true  e = mk⇔
    (λ h → lv , mk⇔
      (λ bt → Equivalence.to dec (trans (just-injective h) bt))
      (λ p → trans (sym (just-injective h)) (Equivalence.from dec p)))
    (λ { (_ , bp) → cong just (bool-⇔ (value (decideᴳᶜ C)) b
           (λ vt → Equivalence.from bp (Equivalence.to dec vt))
           (λ bt → Equivalence.from dec (Equivalence.to bp bt))) })
    where
    lv : level C ≤ 2
    lv = ≤ᵇ-true e

    dec = decideᴳ-correct C lv
  at false e = mk⇔ (λ h → ⊥-elim (nothing≢just h))
                   (λ { (lv , _) → ⊥-elim (≤ᵇ-false e lv) })

-- Within level 2 its answer is decideᴳᶜ's.

decideᴷ-agrees : (C : Circuit n) → level C ≤ 2 →
                 value (decideᴷᶜ C) ≡ just (value (decideᴳᶜ C))
decideᴷ-agrees C lv =
  at (value (levelᶜ C) ≤ᵇ 2) (cong (_≤ᵇ 2) (value-levelᶜ C))
  where
  at : (o : Bool) → o ≡ (level C ≤ᵇ 2) →
       value (answerᶜ o C) ≡ just (value (decideᴳᶜ C))
  at true  e = refl
  at false e = ⊥-elim (≤ᵇ-false e lv)

-- And it answers nothing exactly above level 2.

decideᴷ-nothing : (C : Circuit n) →
                  (value (decideᴷᶜ C) ≡ nothing ⇔ (¬ (level C ≤ 2)))
decideᴷ-nothing C =
  at (value (levelᶜ C) ≤ᵇ 2) (cong (_≤ᵇ 2) (value-levelᶜ C))
  where
  at : (o : Bool) → o ≡ (level C ≤ᵇ 2) →
       (value (answerᶜ o C) ≡ nothing ⇔ (¬ (level C ≤ 2)))
  at true  e = mk⇔ (λ ()) (λ nl → ⊥-elim (nl (≤ᵇ-true e)))
  at false e = mk⇔ (λ _ → ≤ᵇ-false e) (λ _ → refl)


------------------------------------------------------------------------
-- The explicit polynomials

-- Opaque, with their defining equations exported.

opaque
  decideᴷBound : ℕ → ℕ → ℕ
  decideᴷBound n ℓ = 399 * (3 + (n + ℓ)) ^ 11

  decideᴷBound-def : ∀ n ℓ → decideᴷBound n ℓ ≡ 399 * (3 + (n + ℓ)) ^ 11
  decideᴷBound-def n ℓ = refl

  volumeᴷBound : ℕ → ℕ
  volumeᴷBound v = 399 * (3 + 2 * v) ^ 11

  volumeᴷBound-def : ∀ v → volumeᴷBound v ≡ 399 * (3 + 2 * v) ^ 11
  volumeᴷBound-def v = refl

  equivᴷBound : ℕ → ℕ → ℕ → ℕ
  equivᴷBound n a b = 401 * (3 + (n + (a + b))) ^ 11

  equivᴷBound-def : ∀ n a b →
                    equivᴷBound n a b ≡ 401 * (3 + (n + (a + b))) ^ 11
  equivᴷBound-def n a b = refl

  equivᴷVolumeBound : ℕ → ℕ
  equivᴷVolumeBound v = 401 * (3 + 2 * v) ^ 11

  equivᴷVolumeBound-def : ∀ v → equivᴷVolumeBound v ≡ 401 * (3 + 2 * v) ^ 11
  equivᴷVolumeBound-def v = refl

  equivᴳVolumeBound : ℕ → ℕ
  equivᴳVolumeBound v = 400 * (3 + 2 * v) ^ 11

  equivᴳVolumeBound-def : ∀ v → equivᴳVolumeBound v ≡ 400 * (3 + 2 * v) ^ 11
  equivᴳVolumeBound-def v = refl


------------------------------------------------------------------------
-- Arithmetic at a variable B

private
  1≤ : ∀ {x B} → 3 + x ≤ B → 1 ≤ B
  1≤ le = ℕ.≤-trans (s≤s z≤n) le

  -- 2 L + 1 ≤ B^11 when L + 3 ≤ B.
  small : ∀ L B → 3 + L ≤ B → 2 * L + 1 ≤ B ^ 11
  small L B le = ℕ.≤-trans
    (ℕ.≤-trans (ℕ.m≤m+n (2 * L + 1) 5)
      (ℕ.≤-reflexive (solve 1 (λ L → (con 2 :* L :+ con 1) :+ con 5 :=
                                     con 2 :* (con 3 :+ L)) refl L)))
    (ℕ.≤-trans (ℕ.*-monoʳ-≤ 2 le)
    (ℕ.≤-trans (ℕ.*-monoˡ-≤ B (ℕ.≤-trans (s≤s (s≤s z≤n)) le))
    (ℕ.≤-trans (ℕ.≤-reflexive (B*B B))
               (^-mono (1≤ le) (ℕ.m≤m+n 2 9)))))

  -- a + (1 + c) ≤ 399 P when a + 1 ≤ P and c ≤ 398 P.
  gather : ∀ {a c} P → a + 1 ≤ P → c ≤ 398 * P → a + (1 + c) ≤ 399 * P
  gather {a} {c} P a≤ c≤ = ℕ.≤-trans
    (ℕ.≤-reflexive (solve 2 (λ a c → a :+ (con 1 :+ c) :=
                                     (a :+ con 1) :+ c) refl a c))
    (ℕ.≤-trans (ℕ.+-mono-≤ a≤ c≤)
               (ℕ.≤-reflexive (solve 1 (λ P → P :+ con 398 :* P :=
                                              con 399 :* P) refl P)))

  -- A gate names a wire.
  gate-wire : Gate n → 1 ≤ n
  gate-wire (K.H w)        = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)
  gate-wire (K.CNOT c t _) = ℕ.≤-trans (s≤s z≤n) (toℕ<n c)
  gate-wire (K.R k w)      = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)
  gate-wire (K.R† k w)     = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)

  -- Small constants are below any positive multiple of a positive
  -- power.
  const≤ : ∀ {k} c P → k ≤ c → 1 ≤ P → k ≤ c * P
  const≤ c P k≤c 1≤P = ℕ.≤-trans k≤c
    (ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.*-identityʳ c))) (ℕ.*-monoʳ-≤ c 1≤P))


------------------------------------------------------------------------
-- The cost of the total decision

cost-decideᴷ-at : (C : Circuit n) (B : ℕ) → 3 + (n + length C) ≤ B →
                  cost (decideᴷᶜ C) ≤ 399 * B ^ 11
cost-decideᴷ-at {n} C B le =
  gather (B ^ 11)
    (ℕ.≤-trans (ℕ.+-monoˡ-≤ 1 (cost-levelᶜ C))
               (small (length C) B
                 (ℕ.≤-trans (ℕ.+-monoʳ-≤ 3 (ℕ.m≤n+m (length C) n)) le)))
    (at (value (levelᶜ C) ≤ᵇ 2) (cong (_≤ᵇ 2) (value-levelᶜ C)))
  where
  at : (o : Bool) → o ≡ (level C ≤ᵇ 2) →
       cost (answerᶜ o C) ≤ 398 * B ^ 11
  at true  e = cost-decideᴳ-at C (≤ᵇ-true e) B le
  at false e = z≤n

cost-decideᴷᶜ : (C : Circuit n) →
                cost (decideᴷᶜ C) ≤ decideᴷBound n (length C)
cost-decideᴷᶜ {n} C = subst (cost (decideᴷᶜ C) ≤_)
  (sym (decideᴷBound-def n (length C)))
  (cost-decideᴷ-at C (3 + (n + length C)) ℕ.≤-refl)

-- In the volume: the empty circuit costs two steps.

private
  volumeᴷ-at : (C : Circuit n) (v : ℕ) → v ≡ n * length C →
               cost (decideᴷᶜ C) ≤ 399 * (3 + 2 * v) ^ 11
  volumeᴷ-at []      v eq =
    const≤ 399 ((3 + 2 * v) ^ 11) (s≤s (s≤s z≤n))
           (^-pos {B = 3 + 2 * v} {k = 11} (s≤s z≤n))
  volumeᴷ-at {n} (g ∷ C) v eq = cost-decideᴷ-at (g ∷ C) (3 + 2 * v)
    (ℕ.+-monoʳ-≤ 3 (ℕ.≤-trans
      (volume-≤ n (length (g ∷ C)) (gate-wire g) (s≤s z≤n))
      (ℕ.≤-reflexive (cong (2 *_) (sym eq)))))

cost-decideᴷ-volume : (C : Circuit n) →
                      cost (decideᴷᶜ C) ≤ volumeᴷBound (n * length C)
cost-decideᴷ-volume {n} C = subst (cost (decideᴷᶜ C) ≤_)
  (sym (volumeᴷBound-def (n * length C)))
  (volumeᴷ-at C (n * length C) refl)


------------------------------------------------------------------------
-- Corollary 4.4, total

record Corollary-4-4ᴷ {n : ℕ} (C : Circuit n) : Set where
  field
    decides    : ∀ b → value (decideᴷᶜ C) ≡ just b ⇔
                       (level C ≤ 2 × (b ≡ true ⇔ ⟦ C ⟧ ≋ idPS))
    polynomial : cost (decideᴷᶜ C) ≤ decideᴷBound n (length C)
    volume     : cost (decideᴷᶜ C) ≤ volumeᴷBound (n * length C)

corollary-4-4-polytime-total : (C : Circuit n) → Corollary-4-4ᴷ C
corollary-4-4-polytime-total C = record
  { decides    = decideᴷ-correct C
  ; polynomial = cost-decideᴷᶜ C
  ; volume     = cost-decideᴷ-volume C
  }


------------------------------------------------------------------------
-- Equivalence, total

-- The miter is Clifford exactly when both circuits are.

level-miter⇔ : (C₁ C₂ : Circuit n) →
               (level (C₁ ++ C₂ †) ≤ 2 ⇔ (level C₁ ≤ 2 × level C₂ ≤ 2))
level-miter⇔ C₁ C₂ = mk⇔
  (λ lv → let lv′ = subst (_≤ 2) eq lv in
          ℕ.≤-trans (ℕ.m≤m⊔n (level C₁) (level C₂)) lv′ ,
          ℕ.≤-trans (ℕ.m≤n⊔m (level C₁) (level C₂)) lv′)
  (λ { (lv₁ , lv₂) → level-miter C₁ C₂ lv₁ lv₂ })
  where
  eq : level (C₁ ++ C₂ †) ≡ level C₁ ⊔ level C₂
  eq = trans (level-++ C₁ (C₂ †)) (cong (level C₁ ⊔_) (level-† C₂))

equivᴷᶜ : Circuit n → Circuit n → Cost (Maybe Bool)
equivᴷᶜ C₁ C₂ = miterᴷᶜ C₁ C₂ >>= decideᴷᶜ

private
  ×-⇔ : {A A′ B B′ : Set} → A ⇔ A′ → B ⇔ B′ → (A × B) ⇔ (A′ × B′)
  ×-⇔ f g = mk⇔ (λ { (a , b) → Equivalence.to f a , Equivalence.to g b })
                (λ { (a , b) → Equivalence.from f a , Equivalence.from g b })

  ⇔-right : {X P Q : Set} → P ⇔ Q → (X ⇔ P) ⇔ (X ⇔ Q)
  ⇔-right pq = mk⇔ (λ h → ⇔-trans h pq) (λ h → ⇔-trans h (⇔-sym pq))

equivᴷ-correct : (C₁ C₂ : Circuit n) (b : Bool) →
                 (value (equivᴷᶜ C₁ C₂) ≡ just b ⇔
                  ((level C₁ ≤ 2 × level C₂ ≤ 2) ×
                   (b ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)))
equivᴷ-correct {n} C₁ C₂ b =
  ⇔-trans (decideᴷ-correct D b) (×-⇔ lv-part ≋-part)
  where
  -- (The two parts are typed separately, and the miter circuit is
  -- taken as PathSum.Cost.Gauss.Corollary.value-miterᴷᶜ spells it, so
  -- that no two statements about ≋ need to be compared by unfolding
  -- it into amplitudes.)
  D = value (miterᴷᶜ C₁ C₂)

  eq = value-miterᴷᶜ C₁ C₂

  L : Circuit n → Set
  L E = level E ≤ 2

  P : Circuit n → Set
  P E = ⟦ E ⟧ ≋ idPS

  lv-part : level D ≤ 2 ⇔ (level C₁ ≤ 2 × level C₂ ≤ 2)
  lv-part = ⇔-trans (mk⇔ (subst L eq) (subst L (sym eq)))
                    (level-miter⇔ C₁ C₂)

  ≋-part : (b ≡ true ⇔ ⟦ D ⟧ ≋ idPS) ⇔ (b ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
  ≋-part = ⇔-right (⇔-trans (mk⇔ (subst P eq) (subst P (sym eq)))
                            (⇔-sym (miter C₁ C₂)))

-- At most 401 (n + |C₁| + |C₂| + 3)^11.

cost-equivᴷ-at : (C₁ C₂ : Circuit n) (B : ℕ) →
                 3 + (n + (length C₁ + length C₂)) ≤ B →
                 cost (equivᴷᶜ C₁ C₂) ≤ 401 * B ^ 11
cost-equivᴷ-at {n} C₁ C₂ B le = ℕ.≤-trans
  (ℕ.+-mono-≤ (ℕ.≤-trans (cost-miterᴷᶜ C₁ C₂) (ℕ.+-mono-≤ bb≤ a≤))
              (cost-decideᴷ-at D B lenD≤))
  (ℕ.≤-reflexive (solve 1 (λ P → (P :+ P) :+ con 399 :* P := con 401 :* P)
                         refl (B ^ 11)))
  where
  D = value (miterᴷᶜ C₁ C₂)

  1≤B : 1 ≤ B
  1≤B = 1≤ le

  ab≤B : length C₁ + length C₂ ≤ B
  ab≤B = ℕ.≤-trans (ℕ.m≤n+m _ n) (ℕ.≤-trans (ℕ.m≤n+m _ 3) le)

  lenD≤ : 3 + (n + length D) ≤ B
  lenD≤ = subst (λ ℓ → 3 + (n + ℓ) ≤ B) (sym (length-miterᴷ C₁ C₂)) le

  b≤B : length C₂ ≤ B
  b≤B = ℕ.≤-trans (ℕ.m≤n+m (length C₂) (length C₁)) ab≤B

  sb≤B : suc (length C₂) ≤ B
  sb≤B = ℕ.≤-trans (s≤s (ℕ.≤-trans (ℕ.m≤n+m (length C₂) (length C₁))
                                   (ℕ.m≤n+m _ n)))
                   (ℕ.≤-trans (ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.n≤1+n _)) le)

  bb≤ : length C₂ * suc (length C₂) ≤ B ^ 11
  bb≤ = ℕ.≤-trans (ℕ.*-mono-≤ b≤B sb≤B)
    (ℕ.≤-trans (ℕ.≤-reflexive (B*B B)) (^-mono 1≤B (ℕ.m≤m+n 2 9)))

  a≤ : length C₁ ≤ B ^ 11
  a≤ = ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤m+n (length C₁) (length C₂)) ab≤B)
         (ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.^-identityʳ B)))
                    (^-mono 1≤B (ℕ.m≤m+n 1 10)))

cost-equivᴷᶜ : (C₁ C₂ : Circuit n) →
               cost (equivᴷᶜ C₁ C₂) ≤ equivᴷBound n (length C₁) (length C₂)
cost-equivᴷᶜ {n} C₁ C₂ = subst (cost (equivᴷᶜ C₁ C₂) ≤_)
  (sym (equivᴷBound-def n (length C₁) (length C₂)))
  (cost-equivᴷ-at C₁ C₂ (3 + (n + (length C₁ + length C₂))) ℕ.≤-refl)


------------------------------------------------------------------------
-- The equivalence bounds in the volume n · (|C₁| + |C₂|)

-- A gate in either circuit names a wire; then n + |C₁| + |C₂| is at
-- most twice the volume.

private
  two-volume : ∀ {n} (C₁ C₂ : Circuit n) (v : ℕ) →
               v ≡ n * (length C₁ + length C₂) → 1 ≤ n →
               1 ≤ length C₁ + length C₂ →
               3 + (n + (length C₁ + length C₂)) ≤ 3 + 2 * v
  two-volume {n} C₁ C₂ v eq 1≤n 1≤ℓ = ℕ.+-monoʳ-≤ 3 (ℕ.≤-trans
    (volume-≤ n (length C₁ + length C₂) 1≤n 1≤ℓ)
    (ℕ.≤-reflexive (cong (2 *_) (sym eq))))

  volumeᴷᴱ-at : (C₁ C₂ : Circuit n) (v : ℕ) →
                v ≡ n * (length C₁ + length C₂) →
                cost (equivᴷᶜ C₁ C₂) ≤ 401 * (3 + 2 * v) ^ 11
  volumeᴷᴱ-at [] [] v eq =
    const≤ 401 ((3 + 2 * v) ^ 11) (s≤s (s≤s z≤n))
           (^-pos {B = 3 + 2 * v} {k = 11} (s≤s z≤n))
  volumeᴷᴱ-at (g ∷ C₁) C₂ v eq = cost-equivᴷ-at (g ∷ C₁) C₂ (3 + 2 * v)
    (two-volume (g ∷ C₁) C₂ v eq (gate-wire g) (s≤s z≤n))
  volumeᴷᴱ-at [] (g ∷ C₂) v eq = cost-equivᴷ-at [] (g ∷ C₂) (3 + 2 * v)
    (two-volume [] (g ∷ C₂) v eq (gate-wire g) (s≤s z≤n))

  volumeᴳᴱ-at : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 → level C₂ ≤ 2 →
                (v : ℕ) → v ≡ n * (length C₁ + length C₂) →
                cost (equivᴳᶜ C₁ C₂) ≤ 400 * (3 + 2 * v) ^ 11
  volumeᴳᴱ-at [] [] lv₁ lv₂ v eq =
    const≤ 400 ((3 + 2 * v) ^ 11) (s≤s z≤n)
           (^-pos {B = 3 + 2 * v} {k = 11} (s≤s z≤n))
  volumeᴳᴱ-at (g ∷ C₁) C₂ lv₁ lv₂ v eq =
    cost-equivᴳ-at (g ∷ C₁) C₂ lv₁ lv₂ (3 + 2 * v)
      (two-volume (g ∷ C₁) C₂ v eq (gate-wire g) (s≤s z≤n))
  volumeᴳᴱ-at [] (g ∷ C₂) lv₁ lv₂ v eq =
    cost-equivᴳ-at [] (g ∷ C₂) lv₁ lv₂ (3 + 2 * v)
      (two-volume [] (g ∷ C₂) v eq (gate-wire g) (s≤s z≤n))

cost-equivᴷ-volume : (C₁ C₂ : Circuit n) →
                     cost (equivᴷᶜ C₁ C₂) ≤
                     equivᴷVolumeBound (n * (length C₁ + length C₂))
cost-equivᴷ-volume {n} C₁ C₂ = subst (cost (equivᴷᶜ C₁ C₂) ≤_)
  (sym (equivᴷVolumeBound-def (n * (length C₁ + length C₂))))
  (volumeᴷᴱ-at C₁ C₂ (n * (length C₁ + length C₂)) refl)

cost-equivᴳ-volume : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 → level C₂ ≤ 2 →
                     cost (equivᴳᶜ C₁ C₂) ≤
                     equivᴳVolumeBound (n * (length C₁ + length C₂))
cost-equivᴳ-volume {n} C₁ C₂ lv₁ lv₂ = subst (cost (equivᴳᶜ C₁ C₂) ≤_)
  (sym (equivᴳVolumeBound-def (n * (length C₁ + length C₂))))
  (volumeᴳᴱ-at C₁ C₂ lv₁ lv₂ (n * (length C₁ + length C₂)) refl)


------------------------------------------------------------------------
-- The equivalence procedures, packaged

-- Total: for every pair of circuits.

record PolyEquivalenceᴷ {n : ℕ} (C₁ C₂ : Circuit n) : Set where
  field
    decides    : ∀ b → value (equivᴷᶜ C₁ C₂) ≡ just b ⇔
                       ((level C₁ ≤ 2 × level C₂ ≤ 2) ×
                        (b ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧))
    polynomial : cost (equivᴷᶜ C₁ C₂) ≤
                 equivᴷBound n (length C₁) (length C₂)
    volume     : cost (equivᴷᶜ C₁ C₂) ≤
                 equivᴷVolumeBound (n * (length C₁ + length C₂))

equivalence-polytime-total : (C₁ C₂ : Circuit n) → PolyEquivalenceᴷ C₁ C₂
equivalence-polytime-total C₁ C₂ = record
  { decides    = equivᴷ-correct C₁ C₂
  ; polynomial = cost-equivᴷᶜ C₁ C₂
  ; volume     = cost-equivᴷ-volume C₁ C₂
  }

-- PathSum.Cost.Gauss.Corollary's procedure, for two Clifford circuits,
-- with its bound in the volume too.

record PolyEquivalenceᴳᵛ {n : ℕ} (C₁ C₂ : Circuit n) : Set where
  field
    decides    : value (equivᴳᶜ C₁ C₂) ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧
    polynomial : cost (equivᴳᶜ C₁ C₂) ≤
                 equivᴳBound n (length C₁) (length C₂)
    volume     : cost (equivᴳᶜ C₁ C₂) ≤
                 equivᴳVolumeBound (n * (length C₁ + length C₂))

equivalence-polytime-gauss-volume : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 →
                                    level C₂ ≤ 2 → PolyEquivalenceᴳᵛ C₁ C₂
equivalence-polytime-gauss-volume C₁ C₂ lv₁ lv₂ = record
  { decides    = equivᴳ-correct C₁ C₂ lv₁ lv₂
  ; polynomial = cost-equivᴳᶜ C₁ C₂ lv₁ lv₂
  ; volume     = cost-equivᴳ-volume C₁ C₂ lv₁ lv₂
  }
