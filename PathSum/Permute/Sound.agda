------------------------------------------------------------------------
-- Presentations of groups
--
-- Renaming path variables and relabelling wires, on operators (Amy,
-- QPL 2018, remark 2.8)
--
-- PathSum.Permute renames the variables of a path-sum along
-- bijections: renumber π renames the path variables, relabel σ the
-- wires.  Here is what they do to the operator.
--
-- Renaming the path variables changes nothing: the paths of
-- renumber π ξ are those of ξ read through π, so its amplitudes are
-- ξ's sums taken in another order (amp-renumber, by Σᴮ-pull, the
-- reindexing of a sum over assignments along a bijection), and
-- renumber π ξ ≋ ξ (renumber-≋).  This generalises
-- PathSum.Anywhere.Sound.front-≋, which moves one variable to the
-- front.
--
-- Relabelling the wires conjugates the operator by the permutation of
-- basis states it induces: the entry of relabel σ ξ from x to z is
-- the entry of ξ from x ∘ σ to z ∘ σ (amp-relabel), so relabelling
-- respects ≋ (relabel-≋).
--
-- Last, the relation that matches how a path-sum is read.
-- ξ ≈ᴿ⟨ π ⟩ ζ: the same normalisation, and, once ξ's path variables
-- are renamed by π, phases congruent modulo 2^M and outputs modulo 2,
-- coefficient by coefficient -- PathSum.Congruence's
-- Congruent (renumber π ξ) ζ.
-- It is weaker than PathSum.Permute's ξ ≡ᴿ⟨ π ⟩ ζ, which has the
-- coefficients equal as integers (≡ᴿ⇒≈ᴿ), and implies ξ ≋ ζ
-- (≈ᴿ⇒≋): renaming changes nothing, and congruent path-sums are
-- equivalent (PathSum.Congruence.congruent-≋).  It too follows from
-- values: phases taking the same values and outputs the same bits,
-- after the renaming (≈ᴿ-by-values, by Möbius inversion modulo 2,
-- PathSum.Polynomial.Boolean.≈-from-values).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Permute.Sound (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Permutation using
  (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_; inverseˡ; inverseʳ; remove;
   punchIn-permute)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Integer.Base using (ℤ; +_; _+_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (+-inverseʳ)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere.Sound M₀ using (Σᴮ-insert)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Compose.Properties M₀ using (hits-outBit)
open import PathSum.Compose.Sum M₀ using (bool-iff; if-cong; zpow-≡)
open import PathSum.Congruence M₀ using (Congruent; congruent-≋)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; extend; Σᴮ; Σᴮ-cong; Respects; zpow; scale-map)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; _≋_; ≋-sym; ≋-trans; hits-intro;
   hits-elim; hits-≗³)
open import PathSum.HiddenShift.Sign M₀ using (odd-≡)
open import PathSum.Order M using (pow)
open import PathSum.Permute using
  (renumberᴾ; relabelᴾ; renumber; relabel; eval-renumberᴾ;
   eval-relabelᴾ; _≡ᴿ⟨_⟩_; renamed)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using (≈-from-values)
open import PathSum.Polynomial.Properties using (eval-cong; i∣0)
open import PathSum.Reorder using (insertᵃ; insertᵃ-here; insertᵃ-punchIn)

private
  variable
    k k′ l n n′ m m′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Sums over assignments, reindexed

-- A sum over the assignments to l variables, each read through a
-- bijection π : Fin k ↔ Fin l, is the sum over the assignments to k
-- variables.  π sends the first variable to some j; split the sum at
-- j (Σᴮ-insert), and an assignment with b inserted at j reads, through
-- π, as b followed by the rest read through remove 0 π.

Σᴮ-pull : (π : Permutation k l) (F : Assign k → Amp) → Respects F →
          Σᴮ {l} (λ y → F (λ i → y (π ⟨$⟩ʳ i))) ≐ Σᴮ F
Σᴮ-pull {zero}  {zero}  π F resp = resp _ _ (λ ())
Σᴮ-pull {zero}  {suc l} π F resp = contradiction (π ⟨$⟩ˡ zero) ¬Fin0
Σᴮ-pull {suc k} {zero}  π F resp = contradiction (π ⟨$⟩ʳ zero) ¬Fin0
Σᴮ-pull {suc k} {suc l} π F resp w =
  trans (Σᴮ-insert j G respG w) (cong₂ _+_ (half true) (half false))
  where
  j : Fin (suc l)
  j = π ⟨$⟩ʳ zero

  ρ : Permutation k l
  ρ = remove zero π

  G : Assign (suc l) → Amp
  G y = F (λ i → y (π ⟨$⟩ʳ i))

  respG : Respects G
  respG g h g≗h = resp _ _ (λ i → g≗h (π ⟨$⟩ʳ i))

  pt : ∀ b (g : Assign l) i →
       insertᵃ j b g (π ⟨$⟩ʳ i) ≡ extend b (λ i′ → g (ρ ⟨$⟩ʳ i′)) i
  pt b g zero    = insertᵃ-here j b g
  pt b g (suc i) = trans (cong (insertᵃ j b g) (punchIn-permute π zero i))
                         (insertᵃ-punchIn j b g (ρ ⟨$⟩ʳ i))

  respb : ∀ b → Respects (λ g → F (extend b g))
  respb b g h g≗h = resp (extend b g) (extend b h) λ where
    zero    → refl
    (suc i) → g≗h i

  half : ∀ b → Σᴮ (λ g → G (insertᵃ j b g)) w ≡ Σᴮ (λ g → F (extend b g)) w
  half b = trans (Σᴮ-cong (λ g → resp _ _ (pt b g)) w)
                 (Σᴮ-pull ρ (λ g → F (extend b g)) (respb b) w)


------------------------------------------------------------------------
-- Renaming the path variables

-- The outputs and the guards of a renumbered path-sum read the
-- original's along the path read through π.

outBit-renumber : (π : Permutation m m′) (ξ : PathSum n k m) (x : Assign n)
                  (y : Assign m′) (w : Fin n) →
                  outBit (renumber π ξ) x y w ≡
                  outBit ξ x (λ j → y (π ⟨$⟩ʳ j)) w
outBit-renumber π ξ x y w = cong odd (eval-renumberᴾ π (out ξ w) x y)

hits-renumber : (π : Permutation m m′) (ξ : PathSum n k m) (x : Assign n)
                (y : Assign m′) (z : Assign n) →
                hits (renumber π ξ) x y z ≡ hits ξ x (λ j → y (π ⟨$⟩ʳ j)) z
hits-renumber π ξ x y z =
  hits-outBit (renumber π ξ) ξ x x y (λ j → y (π ⟨$⟩ʳ j)) z
              (outBit-renumber π ξ x y)

-- So the amplitudes are the same sums, over the paths in another
-- order.

amp-renumber : (π : Permutation m m′) (ξ : PathSum n k m) (x z : Assign n) →
               amp (renumber π ξ) x z ≐ amp ξ x z
amp-renumber π ξ x z =
  Σᴮ-cong (λ y → if-cong (hits-renumber π ξ x y z)
                         (zpow-≡ (eval-renumberᴾ π (phase ξ) x y)))
  ∙ Σᴮ-pull π T respT
  where
  T : Assign _ → Amp
  T y = if hits ξ x y z then zpow (eval (phase ξ) x y) else 0ᴬ

  respT : Respects T
  respT g h g≗h = if-cong (hits-≗³ ξ {x} {x} {g} {h} {z} {z}
                                   (λ _ → refl) g≗h (λ _ → refl))
                          (zpow-≡ (eval-cong (phase ξ) {x} {x} {g} {h}
                                             (λ _ → refl) g≗h))

renumber-≋ : (π : Permutation m m′) (ξ : PathSum n k m) → renumber π ξ ≋ ξ
renumber-≋ {k = k} π ξ x z = scale-map k (amp-renumber π ξ x z)


------------------------------------------------------------------------
-- Relabelling the wires

-- The output on wire w of relabel σ ξ is ξ's output on σ⁻¹ w, at the
-- input read through σ.

outBit-relabel : (σ : Permutation n n′) (ξ : PathSum n k m)
                 (x : Assign n′) (y : Assign m) (w : Fin n′) →
                 outBit (relabel σ ξ) x y w ≡
                 outBit ξ (λ i → x (σ ⟨$⟩ʳ i)) y (σ ⟨$⟩ˡ w)
outBit-relabel σ ξ x y w = cong odd (eval-relabelᴾ σ (out ξ (σ ⟨$⟩ˡ w)) x y)

-- A path of relabel σ ξ hits z exactly when the same path of ξ hits
-- z read through σ.

hits-relabel : (σ : Permutation n n′) (ξ : PathSum n k m)
               (x : Assign n′) (y : Assign m) (z : Assign n′) →
               hits (relabel σ ξ) x y z ≡
               hits ξ (λ i → x (σ ⟨$⟩ʳ i)) y (λ i → z (σ ⟨$⟩ʳ i))
hits-relabel σ ξ x y z = bool-iff
  (λ e → hits-intro ξ x′ y z′ (λ w →
     trans (sym (at w)) (hits-elim (relabel σ ξ) x y z e (σ ⟨$⟩ʳ w))))
  (λ e → hits-intro (relabel σ ξ) x y z (λ w →
     trans (outBit-relabel σ ξ x y w)
           (trans (hits-elim ξ x′ y z′ e (σ ⟨$⟩ˡ w))
                  (cong z (inverseʳ σ)))))
  where
  x′ z′ : Assign _
  x′ i = x (σ ⟨$⟩ʳ i)
  z′ i = z (σ ⟨$⟩ʳ i)

  at : ∀ w → outBit (relabel σ ξ) x y (σ ⟨$⟩ʳ w) ≡ outBit ξ x′ y w
  at w = trans (outBit-relabel σ ξ x y (σ ⟨$⟩ʳ w))
               (cong (outBit ξ x′ y) (inverseˡ σ))

-- The operator of relabel σ ξ is that of ξ conjugated by the
-- permutation of basis states σ induces: its entry from x to z is ξ's
-- from x ∘ σ to z ∘ σ.

amp-relabel : (σ : Permutation n n′) (ξ : PathSum n k m) (x z : Assign n′) →
              amp (relabel σ ξ) x z ≐
              amp ξ (λ i → x (σ ⟨$⟩ʳ i)) (λ i → z (σ ⟨$⟩ʳ i))
amp-relabel σ ξ x z = Σᴮ-cong (λ y →
  if-cong (hits-relabel σ ξ x y z) (zpow-≡ (eval-relabelᴾ σ (phase ξ) x y)))

-- Hence relabelling respects ≋.

relabel-≋ : (σ : Permutation n n′) (ξ : PathSum n k m)
            (ζ : PathSum n k′ m′) → ξ ≋ ζ → relabel σ ξ ≋ relabel σ ζ
relabel-≋ {k = k} {k′ = k′} σ ξ ζ eq x z =
  scale-map k′ (amp-relabel σ ξ x z)
  ∙ eq (λ i → x (σ ⟨$⟩ʳ i)) (λ i → z (σ ⟨$⟩ʳ i))
  ∙ scale-map k (≐-sym (amp-relabel σ ζ x z))


------------------------------------------------------------------------
-- Congruence up to renaming

-- ξ ≈ᴿ⟨ π ⟩ ζ: the same normalisation, and ξ with its path variables
-- renamed by π congruent to ζ -- outputs modulo 2 and phases modulo
-- 2^M, coefficient by coefficient.

infix 4 _≈ᴿ⟨_⟩_

record _≈ᴿ⟨_⟩_ (ξ : PathSum n k m) (π : Permutation m m′)
               (ζ : PathSum n k′ m′) : Set where
  constructor congruent-renamed
  field
    norm≈     : k ≡ k′
    congruent : Congruent (renumber π ξ) ζ

open _≈ᴿ⟨_⟩_ public

-- Equal integers are congruent modulo anything.

private
  ≡⇒∣ : ∀ {c a b} → a ≡ b → c ∣ (a - b)
  ≡⇒∣ {c} {a} {b} refl = subst (c ∣_) (sym (+-inverseʳ a)) i∣0

-- Equal coefficients are congruent ones.

≡ᴿ⇒≈ᴿ : {ξ : PathSum n k m} {π : Permutation m m′} {ζ : PathSum n k′ m′} →
        ξ ≡ᴿ⟨ π ⟩ ζ → ξ ≈ᴿ⟨ π ⟩ ζ
≡ᴿ⇒≈ᴿ (renamed e ph ou) =
  congruent-renamed e ((λ w γ → ≡⇒∣ (ou w γ)) , (λ γ → ≡⇒∣ (ph γ)))

-- Congruence up to renaming is equivalence.

≈ᴿ⇒≋ : {ξ : PathSum n k m} {π : Permutation m m′} {ζ : PathSum n k′ m′} →
       ξ ≈ᴿ⟨ π ⟩ ζ → ξ ≋ ζ
≈ᴿ⇒≋ {ξ = ξ} {π} {ζ} (congruent-renamed e c) =
  ≋-trans {ξ = ξ} {ζ = renumber π ξ} {χ = ζ}
    (≋-sym {ξ = renumber π ξ} {ζ = ξ} (renumber-≋ π ξ))
    (congruent-≋ (renumber π ξ) ζ e c)

≡ᴿ⇒≋ : {ξ : PathSum n k m} {π : Permutation m m′} {ζ : PathSum n k′ m′} →
       ξ ≡ᴿ⟨ π ⟩ ζ → ξ ≋ ζ
≡ᴿ⇒≋ {ξ = ξ} {π} {ζ} r = ≈ᴿ⇒≋ {ξ = ξ} {π} {ζ} (≡ᴿ⇒≈ᴿ r)

-- It follows from values: phases with the same values, and outputs
-- with the same bits, once ξ's path is read through π.

≈ᴿ-by-values : (ξ : PathSum n k m) (ζ : PathSum n k′ m′)
               (π : Permutation m m′) → k ≡ k′ →
               (∀ x y → eval (phase ξ) x (λ j → y (π ⟨$⟩ʳ j)) ≡
                        eval (phase ζ) x y) →
               (∀ w x y → outBit ξ x (λ j → y (π ⟨$⟩ʳ j)) w ≡
                          outBit ζ x y w) →
               ξ ≈ᴿ⟨ π ⟩ ζ
≈ᴿ-by-values ξ ζ π k≡k′ ph ob = congruent-renamed k≡k′
  ( (λ w → ≈-from-values (renumberᴾ π (out ξ w)) (out ζ w) (λ x y →
       odd-≡ (eval (renumberᴾ π (out ξ w)) x y) (eval (out ζ w) x y)
             (trans (cong odd (eval-renumberᴾ π (out ξ w) x y)) (ob w x y))))
  , ≈-from-values (renumberᴾ π (phase ξ)) (phase ζ) (λ x y →
       ≡⇒∣ (trans (eval-renumberᴾ π (phase ξ) x y) (ph x y))) )
