------------------------------------------------------------------------
-- Presentations of groups
--
-- The eight-element image of the scaled source's four-state action.
-- It is the dihedral group D8: the dyadic translations form C2 x C2,
-- and IH acts by the nontrivial shear.  All finite algebra is checked
-- by reduction; source soundness reuses the proved four-state action.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.DihedralQuotient where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _*_ ; _<_)
open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
open import Data.Fin.Base using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Data.Product.Base using (Σ ; _,_ ; _×_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Empty using (⊥)
open import Level using (0ℓ)
open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms ; module MonoidMorphisms)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; isEquivalence)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.GroupLike as GL
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as UD
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete
import Examples.Groups.CCX+H.GeneralN.Action as Action
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity
open Action using (Coset ; c00 ; c10 ; c11 ; c01)

-- q_ab is translation by ab; h_ab is shear followed by translation.
data D8 : Set where
  q00 q10 q11 q01 h00 h10 h11 h01 : D8

act : Coset → D8 → Coset
act c q00 = c
act c00 q10 = c10
act c10 q10 = c00
act c11 q10 = c01
act c01 q10 = c11
act c00 q11 = c11
act c10 q11 = c01
act c11 q11 = c00
act c01 q11 = c10
act c00 q01 = c01
act c10 q01 = c11
act c11 q01 = c10
act c01 q01 = c00
act c00 h00 = c00
act c10 h00 = c11
act c11 h00 = c10
act c01 h00 = c01
act c00 h10 = c10
act c10 h10 = c01
act c11 h10 = c00
act c01 h10 = c11
act c00 h11 = c11
act c10 h11 = c00
act c11 h11 = c01
act c01 h11 = c10
act c00 h01 = c01
act c10 h01 = c10
act c11 h01 = c11
act c01 h01 = c00

infixl 7 _·_
_·_ : D8 → D8 → D8
q00 · q00 = q00
q00 · q10 = q10
q00 · q11 = q11
q00 · q01 = q01
q00 · h00 = h00
q00 · h10 = h10
q00 · h11 = h11
q00 · h01 = h01
q10 · q00 = q10
q10 · q10 = q00
q10 · q11 = q01
q10 · q01 = q11
q10 · h00 = h11
q10 · h10 = h01
q10 · h11 = h00
q10 · h01 = h10
q11 · q00 = q11
q11 · q10 = q01
q11 · q11 = q00
q11 · q01 = q10
q11 · h00 = h10
q11 · h10 = h00
q11 · h11 = h01
q11 · h01 = h11
q01 · q00 = q01
q01 · q10 = q11
q01 · q11 = q10
q01 · q01 = q00
q01 · h00 = h01
q01 · h10 = h11
q01 · h11 = h10
q01 · h01 = h00
h00 · q00 = h00
h00 · q10 = h10
h00 · q11 = h11
h00 · q01 = h01
h00 · h00 = q00
h00 · h10 = q10
h00 · h11 = q11
h00 · h01 = q01
h10 · q00 = h10
h10 · q10 = h00
h10 · q11 = h01
h10 · q01 = h11
h10 · h00 = q11
h10 · h10 = q01
h10 · h11 = q00
h10 · h01 = q10
h11 · q00 = h11
h11 · q10 = h01
h11 · q11 = h00
h11 · q01 = h10
h11 · h00 = q10
h11 · h10 = q00
h11 · h11 = q01
h11 · h01 = q11
h01 · q00 = h01
h01 · q10 = h11
h01 · q11 = h10
h01 · q01 = h00
h01 · h00 = q01
h01 · h10 = q11
h01 · h11 = q10
h01 · h01 = q00

inverse : D8 → D8
inverse q00 = q00
inverse q10 = q10
inverse q11 = q11
inverse q01 = q01
inverse h00 = h00
inverse h10 = h11
inverse h11 = h10
inverse h01 = h01

odd : D8 → Bool
odd q00 = false
odd q10 = false
odd q11 = false
odd q01 = false
odd h00 = true
odd h10 = true
odd h11 = true
odd h01 = true

private
  all : {P : D8 → Set} → P q00 → P q10 → P q11 → P q01 → P h00 → P h10 → P h11 → P h01 → ∀ q → P q
  all a b c d e f g h q00 = a
  all a b c d e f g h q10 = b
  all a b c d e f g h q11 = c
  all a b c d e f g h q01 = d
  all a b c d e f g h h00 = e
  all a b c d e f g h h10 = f
  all a b c d e f g h h11 = g
  all a b c d e f g h h01 = h

  all-cosets : {P : Coset → Set} → P c00 → P c10 → P c11 → P c01 → ∀ c → P c
  all-cosets a b c d c00 = a
  all-cosets a b c d c10 = b
  all-cosets a b c d c11 = c
  all-cosets a b c d c01 = d

faithful : ∀ q r → (∀ c → act c q ≡ act c r) → q ≡ r
faithful q00 q00 eq = refl
faithful q00 q10 eq with eq c00
... | ()
faithful q00 q11 eq with eq c00
... | ()
faithful q00 q01 eq with eq c00
... | ()
faithful q00 h00 eq with eq c10
... | ()
faithful q00 h10 eq with eq c00
... | ()
faithful q00 h11 eq with eq c00
... | ()
faithful q00 h01 eq with eq c00
... | ()
faithful q10 q00 eq with eq c00
... | ()
faithful q10 q10 eq = refl
faithful q10 q11 eq with eq c00
... | ()
faithful q10 q01 eq with eq c00
... | ()
faithful q10 h00 eq with eq c00
... | ()
faithful q10 h10 eq with eq c10
... | ()
faithful q10 h11 eq with eq c00
... | ()
faithful q10 h01 eq with eq c00
... | ()
faithful q11 q00 eq with eq c00
... | ()
faithful q11 q10 eq with eq c00
... | ()
faithful q11 q11 eq = refl
faithful q11 q01 eq with eq c00
... | ()
faithful q11 h00 eq with eq c00
... | ()
faithful q11 h10 eq with eq c00
... | ()
faithful q11 h11 eq with eq c10
... | ()
faithful q11 h01 eq with eq c00
... | ()
faithful q01 q00 eq with eq c00
... | ()
faithful q01 q10 eq with eq c00
... | ()
faithful q01 q11 eq with eq c00
... | ()
faithful q01 q01 eq = refl
faithful q01 h00 eq with eq c00
... | ()
faithful q01 h10 eq with eq c00
... | ()
faithful q01 h11 eq with eq c00
... | ()
faithful q01 h01 eq with eq c10
... | ()
faithful h00 q00 eq with eq c10
... | ()
faithful h00 q10 eq with eq c00
... | ()
faithful h00 q11 eq with eq c00
... | ()
faithful h00 q01 eq with eq c00
... | ()
faithful h00 h00 eq = refl
faithful h00 h10 eq with eq c00
... | ()
faithful h00 h11 eq with eq c00
... | ()
faithful h00 h01 eq with eq c00
... | ()
faithful h10 q00 eq with eq c00
... | ()
faithful h10 q10 eq with eq c10
... | ()
faithful h10 q11 eq with eq c00
... | ()
faithful h10 q01 eq with eq c00
... | ()
faithful h10 h00 eq with eq c00
... | ()
faithful h10 h10 eq = refl
faithful h10 h11 eq with eq c00
... | ()
faithful h10 h01 eq with eq c00
... | ()
faithful h11 q00 eq with eq c00
... | ()
faithful h11 q10 eq with eq c00
... | ()
faithful h11 q11 eq with eq c10
... | ()
faithful h11 q01 eq with eq c00
... | ()
faithful h11 h00 eq with eq c00
... | ()
faithful h11 h10 eq with eq c00
... | ()
faithful h11 h11 eq = refl
faithful h11 h01 eq with eq c00
... | ()
faithful h01 q00 eq with eq c00
... | ()
faithful h01 q10 eq with eq c00
... | ()
faithful h01 q11 eq with eq c00
... | ()
faithful h01 q01 eq with eq c10
... | ()
faithful h01 h00 eq with eq c00
... | ()
faithful h01 h10 eq with eq c00
... | ()
faithful h01 h11 eq with eq c00
... | ()
faithful h01 h01 eq = refl

act-product : ∀ q r c → act c (q · r) ≡ act (act c q) r
act-product q00 = all
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
act-product q10 = all
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
act-product q11 = all
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
act-product q01 = all
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
act-product h00 = all
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
act-product h10 = all
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
act-product h11 = all
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
act-product h01 = all
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)
  (all-cosets refl refl refl refl)

associative : ∀ q r s → (q · r) · s ≡ q · (r · s)
associative q r s = faithful ((q · r) · s) (q · (r · s)) λ c →
  trans (act-product (q · r) s c)
    (trans (cong (λ d → act d s) (act-product q r c))
      (sym (trans (act-product q (r · s) c) (act-product r s (act c q)))))

identityˡ : ∀ q → q00 · q ≡ q
identityˡ = (all refl refl refl refl refl refl refl refl)

identityʳ : ∀ q → q · q00 ≡ q
identityʳ = (all refl refl refl refl refl refl refl refl)

inverseˡ : ∀ q → inverse q · q ≡ q00
inverseˡ = (all refl refl refl refl refl refl refl refl)

inverseʳ : ∀ q → q · inverse q ≡ q00
inverseʳ = (all refl refl refl refl refl refl refl refl)

odd-product : ∀ q r → odd (q · r) ≡ (odd q xor odd r)
odd-product = (all (all refl refl refl refl refl refl refl refl) (all refl refl refl refl refl refl refl refl) (all refl refl refl refl refl refl refl refl) (all refl refl refl refl refl refl refl refl) (all refl refl refl refl refl refl refl refl) (all refl refl refl refl refl refl refl refl) (all refl refl refl refl refl refl refl refl) (all refl refl refl refl refl refl refl refl))

group : Group 0ℓ 0ℓ
group = record
  { Carrier = D8
  ; _≈_ = _≡_
  ; _∙_ = _·_
  ; ε = q00
  ; _⁻¹ = inverse
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _·_ }
        ; assoc = associative
        }
      ; identity = identityˡ , identityʳ
      }
    ; inverse = inverseˡ , inverseʳ
    ; ⁻¹-cong = cong inverse
    }
  }


identity-from-zero-even : ∀ q → act c00 q ≡ c00 → odd q ≡ false → q ≡ q00
identity-from-zero-even q00 z e = refl
identity-from-zero-even q10 () e
identity-from-zero-even q11 () e
identity-from-zero-even q01 () e
identity-from-zero-even h00 z ()
identity-from-zero-even h10 () e
identity-from-zero-even h11 () e
identity-from-zero-even h01 () e

-- A quarter-turn and a reflection generate all eight elements.
rotation reflection : D8
rotation = q10 · h00
reflection = h00

rotation-four : ((rotation · rotation) · rotation) · rotation ≡ q00
rotation-four = refl

reflection-two : reflection · reflection ≡ q00
reflection-two = refl

reflection-rotation : (reflection · rotation) · reflection ≡ inverse rotation
reflection-rotation = refl

rotation-two-nontrivial : rotation · rotation ≡ q00 → ⊥
rotation-two-nontrivial ()

rotation-power : ℕ → D8
rotation-power zero = q00
rotation-power (suc j) = rotation-power j · rotation

reflection-bit : Bool → D8
reflection-bit false = q00
reflection-bit true = reflection

rotation-generation : ∀ q → Σ ℕ λ j → Σ Bool λ b →
  rotation-power j · reflection-bit b ≡ q
rotation-generation q00 = 0 , false , refl
rotation-generation q10 = 1 , true , refl
rotation-generation q11 = 3 , true , refl
rotation-generation q01 = 2 , false , refl
rotation-generation h00 = 0 , true , refl
rotation-generation h10 = 3 , false , refl
rotation-generation h11 = 1 , false , refl
rotation-generation h01 = 2 , true , refl

letter : ∀ {N} → T.Genᴸ N → D8
letter T.⌊ U.M-gen a ⌋ = q10
letter T.⌊ U.X-gen a b ab ⌋ = q11
letter T.⌊ U.K-gen a b c d ab bc cd ⌋ = q01
letter T.IH = h00

quotient : ∀ {N} → Word (T.Genᴸ N) → D8
quotient [ g ]ʷ = letter g
quotient ε = q00
quotient (u • v) = quotient u · quotient v

private
  letter-correct : ∀ {N} c (g : T.Genᴸ N) → act c (letter g) ≡ Action.step c g
  letter-correct c00 (T.⌊ U.M-gen a ⌋) = refl
  letter-correct c00 (T.⌊ U.X-gen a b ab ⌋) = refl
  letter-correct c00 (T.⌊ U.K-gen a b c d ab bc cd ⌋) = refl
  letter-correct c00 (T.IH) = refl
  letter-correct c10 (T.⌊ U.M-gen a ⌋) = refl
  letter-correct c10 (T.⌊ U.X-gen a b ab ⌋) = refl
  letter-correct c10 (T.⌊ U.K-gen a b c d ab bc cd ⌋) = refl
  letter-correct c10 (T.IH) = refl
  letter-correct c11 (T.⌊ U.M-gen a ⌋) = refl
  letter-correct c11 (T.⌊ U.X-gen a b ab ⌋) = refl
  letter-correct c11 (T.⌊ U.K-gen a b c d ab bc cd ⌋) = refl
  letter-correct c11 (T.IH) = refl
  letter-correct c01 (T.⌊ U.M-gen a ⌋) = refl
  letter-correct c01 (T.⌊ U.X-gen a b ab ⌋) = refl
  letter-correct c01 (T.⌊ U.K-gen a b c d ab bc cd ⌋) = refl
  letter-correct c01 (T.IH) = refl

  letter-odd : ∀ {N} (g : T.Genᴸ N) → odd (letter g) ≡ Parity.source-parity [ g ]ʷ
  letter-odd T.⌊ U.M-gen a ⌋ = refl
  letter-odd T.⌊ U.X-gen a b ab ⌋ = refl
  letter-odd T.⌊ U.K-gen a b c d ab bc cd ⌋ = refl
  letter-odd T.IH = refl

correct : ∀ {N} c (w : Word (T.Genᴸ N)) → act c (quotient w) ≡ Action.At.state N c w
correct c [ g ]ʷ = letter-correct c g
correct c ε = refl
correct {N} c (u • v) = trans (act-product (quotient u) (quotient v) c)
  (trans (correct (act c (quotient u)) v)
    (cong (λ d → Action.At.state N d v) (correct c u)))

parity-correct : ∀ {N} (w : Word (T.Genᴸ N)) → odd (quotient w) ≡ Parity.source-parity w
parity-correct [ g ]ʷ = letter-odd g
parity-correct ε = refl
parity-correct (u • v) = trans (odd-product (quotient u) (quotient v))
  (cong₂ _xor_ (parity-correct u) (parity-correct v))

sound : ∀ {N} {u v : Word (T.Genᴸ N)} → PB._≈_ T._===ᴸ_ u v → quotient u ≡ quotient v
sound {N} {u} {v} eq = faithful (quotient u) (quotient v) λ c →
  trans (correct c u) (trans (Action.At.state-cong N c eq) (sym (correct c v)))

semantic : ∀ k → 0 < k → {u v : Word (T.Genᴸ (k * 2))} →
  S.Dim.⟦_⟧ᴸ k u ≡ S.Dim.⟦_⟧ᴸ k v → quotient u ≡ quotient v
semantic zero ()
semantic (suc k) positive {u} {v} eq = sound {u = u} {v = v}
  (Complete.completeness k {u = u} {v = v} eq)

module SourceGroup (N : ℕ) where
  private
    gl : GL.Grouplike (T._===ᴸ_ {N})
    gl T.⌊ g ⌋ = [ T.⌊ g ⌋ ]ʷ , T.⌊⌋-cong (UD.gen-gen g)
    gl T.IH = T.H , PB.axiom T.r7a

  module G = GL.Group-Lemmas (T._===ᴸ_ {N}) gl
  open GroupMorphisms (Group.rawGroup G.•-ε-group) (Group.rawGroup group)
  open MonoidMorphisms (Group.rawMonoid G.•-ε-group) (Group.rawMonoid group)
    using (IsMonoidHomomorphism)

  monoid-homomorphism : IsMonoidHomomorphism (quotient {N})
  monoid-homomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = sound }
      ; homo = λ u v → refl
      }
    ; ε-homo = refl
    }

  homomorphism : IsGroupHomomorphism (quotient {N})
  homomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
    G.•-ε-group group monoid-homomorphism

  open IsGroupHomomorphism homomorphism public using ()
    renaming (⁻¹-homo to inverse-correct)

  kernel-conjugate : ∀ u v → quotient v ≡ q00 →
    quotient ((u • v) • G._⁻¹ u) ≡ q00
  kernel-conjugate u v kernel = trans
    (cong₂ _·_ (cong (quotient u ·_) kernel) (inverse-correct u))
    (trans (cong (_· inverse (quotient u)) (identityʳ (quotient u)))
      (inverseʳ (quotient u)))

kernel-from-closed-even : ∀ {N} (w : Word (T.Genᴸ N)) →
  Action.At.state N c00 w ≡ c00 → Parity.source-parity w ≡ false → quotient w ≡ q00
kernel-from-closed-even w closed even = identity-from-zero-even (quotient w)
  (trans (correct c00 w) closed) (trans (parity-correct w) even)

kernel-action : ∀ {N} (w : Word (T.Genᴸ N)) → quotient w ≡ q00 →
  ∀ c → Action.At.state N c w ≡ c
kernel-action w eq c = trans (sym (correct c w)) (cong (act c) eq)

stabilizer : ∀ q → act c00 q ≡ c00 → q ≡ q00 ⊎ q ≡ h00
stabilizer q00 eq = inj₁ refl
stabilizer q10 ()
stabilizer q11 ()
stabilizer q01 ()
stabilizer h00 eq = inj₂ refl
stabilizer h10 ()
stabilizer h11 ()
stabilizer h01 ()

stabilizer-state : ∀ q → q ≡ q00 ⊎ q ≡ h00 → act c00 q ≡ c00
stabilizer-state .q00 (inj₁ refl) = refl
stabilizer-state .h00 (inj₂ refl) = refl

-- Surjectivity already holds with two basis levels: M0 and X01 supply
-- both translations, and IH supplies the shear.
module Section {N : ℕ} (a b : Fin N) .(ab : Data.Fin.Base._<_ a b) where
  private
    m x : Word (T.Genᴸ N)
    m = T.Mᴸ a
    x = T.Xᴸ a b ab

  section : D8 → Word (T.Genᴸ N)
  section q00 = ε
  section q10 = m
  section q11 = x
  section q01 = m • x
  section h00 = (ε) • T.H
  section h10 = (x) • T.H
  section h11 = (m) • T.H
  section h01 = (m • x) • T.H

  section-correct : ∀ q → quotient (section q) ≡ q
  section-correct = (all refl refl refl refl refl refl refl refl)

module Surjective (n : ℕ) = Section {suc (suc n)} fzero (fsuc fzero)
  (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)

