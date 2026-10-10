------------------------------------------------------------------------
-- Presentations of groups
--
-- The equations that complete the diagrams of Case 1 of Lemma 4.4.
--
-- Most are conjugations by an X (Clément's (10)–(15), here (c1)–(c5)
-- of Figure 6): X[a,b] moves the indices a and b of the generator it
-- conjugates.  Then (18) (here (d2)), and the square of Subcase 1.11.2,
-- which conjugates two H's and commutes them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Equations {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (<⇒≢)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (Z-Z ; X-X ; H-H ; conj-X ; conj-X′ ; comm-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pairings {n} using (HX)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

------------------------------------------------------------------------
-- One index pair

module _ {a b : Fin n} (ab : a < b) where

  -- (10), (11): X conjugates (-1)[a] and (-1)[b].
  XZaX : X a b ab • Zʷ a • X a b ab ≈ Zʷ b
  XZaX = sym (conj-X ab (axiom (c1 ab)))

  XZbX : X a b ab • Zʷ b • X a b ab ≈ Zʷ a
  XZbX = sym (conj-X′ ab (axiom (c1 ab)))

  -- (18): (-1)[b] H X = H.
  ZHX : Zʷ b • H a b ab • X a b ab ≈ H a b ab
  ZHX = begin
    Zʷ b • H a b ab • X a b ab     ≈⟨ cright HX ab ⟩
    Zʷ b • Zʷ b • H a b ab         ≈⟨ sym assoc ⟩
    (Zʷ b • Zʷ b) • H a b ab       ≈⟨ cleft Z-Z ⟩
    ε • H a b ab                   ≈⟨ left-unit ⟩
    H a b ab                       ∎

------------------------------------------------------------------------
-- Three indices a < b < c

module _ {a b c : Fin n} (ab : a < b) (bc : b < c) where

  private
    ac = FinP.<-trans ab bc

  -- (14), (15): X conjugates the H's.
  XHbcX : X a b ab • H b c bc • X a b ab ≈ H a c ac
  XHbcX = sym (conj-X ab (axiom (c4 ab bc)))

  XHacX : X a b ab • H a c ac • X a b ab ≈ H b c bc
  XHacX = sym (conj-X′ ab (axiom (c4 ab bc)))

  XHabX : X b c bc • H a b ab • X b c bc ≈ H a c ac
  XHabX = sym (conj-X′ bc (axiom (c5 ab bc)))

  XHacX′ : X b c bc • H a c ac • X b c bc ≈ H a b ab
  XHacX′ = sym (conj-X bc (axiom (c5 ab bc)))

  -- (12), (13): X conjugates the X's.
  XXbcX : X a b ab • X b c bc • X a b ab ≈ X a c ac
  XXbcX = sym (conj-X ab (axiom (c2 ab bc)))

  XXacX : X a b ab • X a c ac • X a b ab ≈ X b c bc
  XXacX = sym (conj-X′ ab (axiom (c2 ab bc)))

  -- Subcase 1.3.2: X[a,b] X[a,c] X[b,c] = X[a,c].
  XXX : X a b ab • X a c ac • X b c bc ≈ X a c ac
  XXX = begin
    X a b ab • X a c ac • X b c bc      ≈⟨ cright axiom (c3 ab bc) ⟩
    X a b ab • X b c bc • X a b ab      ≈⟨ XXbcX ⟩
    X a c ac                            ∎

------------------------------------------------------------------------
-- Subcase 1.11.2: a < b < c, b < d, c ≠ d

module _ {a b c d : Fin n} (ab : a < b) (bc : b < c) (bd : b < d) (c≢d : c ≢ d) where

  private
    ac = FinP.<-trans ab bc
    ad = FinP.<-trans ab bd
    a≢b = <⇒≢ ab
    a≢c = <⇒≢ ac
    b≢c = <⇒≢ bc
    b≢d = <⇒≢ bd
    a≢d = <⇒≢ ad

  -- H[b,d] X[a,b] H[b,c] · H[a,d] · X[a,b] = H[a,c].
  sq1112 : (H b d bd • X a b ab • H b c bc) • H a d ad • X a b ab ≈ H a c ac
  sq1112 = begin
    (H b d bd • X a b ab • H b c bc) • H a d ad • X a b ab
      ≈⟨ cright cleft sym right-unit ⟩
    (H b d bd • X a b ab • H b c bc) • (H a d ad • ε) • X a b ab
      ≈⟨ by-assoc ≡.refl ⟩
    H b d bd • (X a b ab • H b c bc • ε) • H a d ad • X a b ab
      ≈⟨ cright cleft cright cright sym (X-X ab) ⟩
    H b d bd • (X a b ab • H b c bc • X a b ab • X a b ab) • H a d ad • X a b ab
      ≈⟨ by-assoc ≡.refl ⟩
    H b d bd • (X a b ab • H b c bc • X a b ab) • (X a b ab • H a d ad • X a b ab)
      ≈⟨ cright cong (XHbcX ab bc) (XHacX ab bd) ⟩
    H b d bd • H a c ac • H b d bd
      ≈⟨ sym assoc ⟩
    (H b d bd • H a c ac) • H b d bd
      ≈⟨ cleft comm-gen (H-gen b d bd) (H-gen a c ac) ((sym≢ a≢b ∷ b≢c ∷ []) ∷ (sym≢ a≢d ∷ sym≢ c≢d ∷ []) ∷ []) ⟩
    (H a c ac • H b d bd) • H b d bd
      ≈⟨ assoc ⟩
    H a c ac • H b d bd • H b d bd
      ≈⟨ cright H-H bd ⟩
    H a c ac • ε
      ≈⟨ right-unit ⟩
    H a c ac ∎
