------------------------------------------------------------------------
-- Presentations of groups
--
-- The abelianization of scaled Tables 1 and 2 is C2 x C2 whenever
-- there are at least two levels.  In particular this describes every
-- positive even dimension in which the scaled matrix presentation is
-- complete.  Its characters are the first dyadic charge and IH parity.
-- This is a quotient of the ambient presentation, not extra circuit
-- identities.  Table 2 identifies the dyadic sign and exchange classes.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; s≤s ; z≤n)

module Examples.Groups.CCX+H.GeneralN.ScaledAbelianization (N : ℕ) where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
import Data.Bool.Properties as BP
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Presentation.GroupLike as GL
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as UD
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH.Subgroup.Abelianization as Dyadic
import Examples.Groups.CCX+H.GeneralN.DihedralQuotient as D
import Examples.Groups.CCX+H.GeneralN.Action as Action
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity

private
  n = 2 + N
  module DA = Dyadic N
  module Source = PB (T._===ᴸ_ {n})

Character = Bool × Bool

infixl 7 _⊕_
_⊕_ : Character → Character → Character
(a , b) ⊕ (c , d) = (a xor c) , (b xor d)

neutral : Character
neutral = false , false

projection : D.D8 → Character
projection D.q00 = false , false
projection D.q10 = true , false
projection D.q11 = true , false
projection D.q01 = false , false
projection D.h00 = false , true
projection D.h10 = true , true
projection D.h11 = true , true
projection D.h01 = false , true

private
  all : {P : D.D8 → Set} → P D.q00 → P D.q10 → P D.q11 → P D.q01 →
    P D.h00 → P D.h10 → P D.h11 → P D.h01 → ∀ q → P q
  all a b c d e f g h D.q00 = a
  all a b c d e f g h D.q10 = b
  all a b c d e f g h D.q11 = c
  all a b c d e f g h D.q01 = d
  all a b c d e f g h D.h00 = e
  all a b c d e f g h D.h10 = f
  all a b c d e f g h D.h11 = g
  all a b c d e f g h D.h01 = h

projection-product : ∀ q r → projection (q D.· r) ≡ projection q ⊕ projection r
projection-product = all
  (all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
  (all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
  (all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
  (all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
  (all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
  (all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
  (all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
  (all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)

character : Word (T.Genᴸ n) → Character
character w = projection (D.quotient w)

character-product : ∀ u v → character (u • v) ≡ character u ⊕ character v
character-product u v = projection-product (D.quotient u) (D.quotient v)

first-charge : Action.Coset → Bool
first-charge Action.c00 = false
first-charge Action.c10 = true
first-charge Action.c11 = true
first-charge Action.c01 = false

private
  projection-charge : ∀ q → proj₁ (projection q) ≡ first-charge (D.act Action.c00 q)
  projection-charge = all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl

  projection-parity : ∀ q → proj₂ (projection q) ≡ D.odd q
  projection-parity = all Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl

character-charge : ∀ w → proj₁ (character w) ≡ first-charge (Action.At.state n Action.c00 w)
character-charge w = Eq.trans (projection-charge (D.quotient w))
  (Eq.cong first-charge (D.correct Action.c00 w))

character-parity : ∀ w → proj₂ (character w) ≡ Parity.source-parity w
character-parity w = Eq.trans (projection-parity (D.quotient w)) (D.parity-correct w)

private
  plus-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
  plus-comm (a , b) (c , d) = Eq.cong₂ _,_ (BP.xor-comm a c) (BP.xor-comm b d)

  source-sound : ∀ {u v} → u Source.≈ v → character u ≡ character v
  source-sound {u} {v} eq = Eq.cong projection (D.sound {u = u} {v = v} eq)

data Relations : WRel (T.Genᴸ n) where
  source : ∀ {u v} → u T.===ᴸ v → Relations u v
  commute : ∀ u v → Relations (u • v) (v • u)

open PB Relations public hiding (_===_)
open PP Relations using (by-assoc ; word-setoid)
open import Relation.Binary.Reasoning.Setoid word-setoid

source-cong : ∀ {u v} → u Source.≈ v → u ≈ v
source-cong PB.refl = refl
source-cong (PB.sym p) = sym (source-cong p)
source-cong (PB.trans p q) = trans (source-cong p) (source-cong q)
source-cong (PB.cong p q) = cong (source-cong p) (source-cong q)
source-cong PB.assoc = assoc
source-cong PB.left-unit = left-unit
source-cong PB.right-unit = right-unit
source-cong (PB.axiom p) = axiom (source p)

grouplike : GL.Grouplike Relations
grouplike T.⌊ g ⌋ = [ T.⌊ g ⌋ ]ʷ , source-cong (T.⌊⌋-cong (UD.gen-gen g))
grouplike T.IH = T.H , axiom (source T.r7a)

sound : ∀ {u v} → u ≈ v → character u ≡ character v
sound refl = Eq.refl
sound (sym p) = Eq.sym (sound p)
sound (trans p q) = Eq.trans (sound p) (sound q)
sound (cong {x} {y} {z} {t} p q) = Eq.trans (character-product x z)
  (Eq.trans (Eq.cong₂ _⊕_ (sound p) (sound q)) (Eq.sym (character-product y t)))
sound (assoc {x} {y} {z}) = source-sound {u = (x • y) • z} {v = x • (y • z)} PB.assoc
sound (left-unit {x}) = source-sound {u = ε • x} {v = x} PB.left-unit
sound (right-unit {x}) = source-sound {u = x • ε} {v = x} PB.right-unit
sound (axiom (source {u} {v} ax)) = source-sound {u = u} {v = v} (PB.axiom ax)
sound (axiom (commute u v)) = Eq.trans (character-product u v)
  (Eq.trans (plus-comm (character u) (character v)) (Eq.sym (character-product v u)))

private
  dyadic-axiom : ∀ {u v} → DA.Relations u v → T.⌊ u ⌋ʷ ≈ T.⌊ v ⌋ʷ
  dyadic-axiom (DA.source ax) = axiom (source (T.table1 ax))
  dyadic-axiom (DA.commute u v) = axiom (commute T.⌊ u ⌋ʷ T.⌊ v ⌋ʷ)

  dyadic-cong : ∀ {u v} → u DA.≈ v → T.⌊ u ⌋ʷ ≈ T.⌊ v ⌋ʷ
  dyadic-cong = PP.GenCongruence.fʷ-cong DA.Relations Relations T.⌊_⌋ dyadic-axiom

  i j : Fin n
  i = zero
  j = suc zero
  ij : i < j
  ij = s≤s z≤n

  m x h : Word (T.Genᴸ n)
  m = T.Mᴸ i
  x = T.Xᴸ i j ij
  h = T.H

  mm : m • m ≈ ε
  mm = axiom (source (T.table1 U.r1b))
  hh : h • h ≈ ε
  hh = axiom (source T.r7a)

  exchange-sign : x ≈ m
  exchange-sign = begin
    x ≈⟨ sym left-unit ⟩
    ε • x ≈⟨ cong (sym hh) refl ⟩
    (h • h) • x ≈⟨ assoc ⟩
    h • (h • x) ≈⟨ cong refl (axiom (commute h x)) ⟩
    h • (x • h) ≈⟨ axiom (source (T.r7d₀ ij Eq.refl Eq.refl)) ⟩
    T.Mᴸ j ≈⟨ dyadic-cong (DA.gen-reference (U.M-gen j)) ⟩
    m ∎

rep : Character → Word (T.Genᴸ n)
rep (false , false) = ε
rep (true , false) = m
rep (false , true) = h
rep (true , true) = m • h

gen-reference : ∀ g → [ g ]ʷ ≈ rep (character [ g ]ʷ)
gen-reference T.⌊ U.M-gen a ⌋ = dyadic-cong (DA.gen-reference (U.M-gen a))
gen-reference T.⌊ U.X-gen a b ab ⌋ = trans
  (dyadic-cong (DA.gen-reference (U.X-gen a b ab))) exchange-sign
gen-reference T.⌊ U.K-gen a b c d ab bc cd ⌋ = trans
  (dyadic-cong (DA.gen-reference (U.K-gen a b c d ab bc cd)))
  (trans (cong refl exchange-sign) mm)
gen-reference T.IH = refl

rep-product : ∀ c d → rep c • rep d ≈ rep (c ⊕ d)
rep-product (false , false) d = left-unit
rep-product (true , false) (false , false) = right-unit
rep-product (true , false) (true , false) = mm
rep-product (true , false) (false , true) = refl
rep-product (true , false) (true , true) = trans (sym assoc) (trans (cong mm refl) left-unit)
rep-product (false , true) (false , false) = right-unit
rep-product (false , true) (true , false) = axiom (commute h m)
rep-product (false , true) (false , true) = hh
rep-product (false , true) (true , true) = begin
  h • (m • h) ≈⟨ sym assoc ⟩
  (h • m) • h ≈⟨ cong (axiom (commute h m)) refl ⟩
  (m • h) • h ≈⟨ assoc ⟩
  m • (h • h) ≈⟨ cong refl hh ⟩
  m • ε ≈⟨ right-unit ⟩
  m ∎
rep-product (true , true) (false , false) = right-unit
rep-product (true , true) (true , false) = begin
  (m • h) • m ≈⟨ assoc ⟩
  m • (h • m) ≈⟨ cong refl (axiom (commute h m)) ⟩
  m • (m • h) ≈⟨ sym assoc ⟩
  (m • m) • h ≈⟨ cong mm refl ⟩
  ε • h ≈⟨ left-unit ⟩
  h ∎
rep-product (true , true) (false , true) = trans assoc (trans (cong refl hh) right-unit)
rep-product (true , true) (true , true) = begin
  (m • h) • (m • h) ≈⟨ by-assoc Eq.refl ⟩
  m • ((h • m) • h) ≈⟨ cong refl (cong (axiom (commute h m)) refl) ⟩
  m • ((m • h) • h) ≈⟨ by-assoc Eq.refl ⟩
  (m • m) • (h • h) ≈⟨ cong mm hh ⟩
  ε • ε ≈⟨ left-unit ⟩
  ε ∎

normalize : ∀ w → w ≈ rep (character w)
normalize [ g ]ʷ = gen-reference g
normalize ε = refl
normalize (u • v) = trans (cong (normalize u) (normalize v))
  (trans (rep-product (character u) (character v))
    (refl' (Eq.cong rep (Eq.sym (character-product u v)))))

complete : ∀ {u v} → character u ≡ character v → u ≈ v
complete {u} {v} eq = trans (normalize u)
  (trans (refl' (Eq.cong rep eq)) (sym (normalize v)))

representatives : ∀ c → character (rep c) ≡ c
representatives (false , false) = Eq.refl
representatives (false , true) = Eq.refl
representatives (true , false) = Eq.refl
representatives (true , true) = Eq.refl

Derived : Word (T.Genᴸ n) → Set
Derived w = w ≈ ε

kernel : ∀ {w} → character w ≡ neutral → Derived w
kernel {w} = complete {u = w} {v = ε}

kernel-only : ∀ {w} → Derived w → character w ≡ neutral
kernel-only = sound

private
  projection-kernel : ∀ q → projection q ≡ neutral → q ≡ D.q00 ⊎ q ≡ D.q01
  projection-kernel D.q00 eq = inj₁ Eq.refl
  projection-kernel D.q10 ()
  projection-kernel D.q11 ()
  projection-kernel D.q01 eq = inj₂ Eq.refl
  projection-kernel D.h00 ()
  projection-kernel D.h10 ()
  projection-kernel D.h11 ()
  projection-kernel D.h01 ()

derived-dihedral : ∀ {w} → Derived w → D.quotient w ≡ D.q00 ⊎ D.quotient w ≡ D.q01
derived-dihedral {w} derived = projection-kernel (D.quotient w) (kernel-only derived)

dihedral-derived : ∀ {w} → D.quotient w ≡ D.q00 ⊎ D.quotient w ≡ D.q01 → Derived w
dihedral-derived {w} (inj₁ eq) = kernel {w} (Eq.cong projection eq)
dihedral-derived {w} (inj₂ eq) = kernel {w} (Eq.cong projection eq)

-- This is precisely the universal quotient imposing commutation.
module Universal {Y : Set} (Δ : WRel Y) (f : T.Genᴸ n → Word Y)
  (source-respects : ∀ {u v} → u T.===ᴸ v → PB._≈_ Δ ((f ʷ) u) ((f ʷ) v))
  (commutative : ∀ u v → PB._≈_ Δ (u • v) (v • u)) where

  private
    respects : ∀ {u v} → Relations u v → PB._≈_ Δ ((f ʷ) u) ((f ʷ) v)
    respects (source ax) = source-respects ax
    respects (commute u v) = commutative ((f ʷ) u) ((f ʷ) v)

  factor : ∀ {u v} → u ≈ v → PB._≈_ Δ ((f ʷ) u) ((f ʷ) v)
  factor = PP.StarCongruence.fʷ-cong Relations Δ f respects

C₂×C₂ : Group 0ℓ 0ℓ
C₂×C₂ = record
  { Carrier = Character
  ; _≈_ = _≡_
  ; _∙_ = _⊕_
  ; ε = neutral
  ; _⁻¹ = λ c → c
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong = Eq.cong₂ _⊕_
          }
        ; assoc = λ { (a , b) (c , d) (e , f) →
            Eq.cong₂ _,_ (BP.xor-assoc a c e) (BP.xor-assoc b d f) }
        }
      ; identity = (λ { (a , b) → Eq.cong₂ _,_ (BP.xor-identityˡ a) (BP.xor-identityˡ b) }) ,
          (λ { (a , b) → Eq.cong₂ _,_ (BP.xor-identityʳ a) (BP.xor-identityʳ b) })
      }
    ; inverse = (λ { (a , b) → Eq.cong₂ _,_ (BP.xor-same a) (BP.xor-same b) }) ,
        (λ { (a , b) → Eq.cong₂ _,_ (BP.xor-same a) (BP.xor-same b) })
    ; ⁻¹-cong = λ eq → eq
    }
  }

private module G = GL.Group-Lemmas Relations grouplike

commutator : Word (T.Genᴸ n) → Word (T.Genᴸ n) → Word (T.Genᴸ n)
commutator u v = ((u • v) • G._⁻¹ u) • G._⁻¹ v

commutator-member : ∀ u v → Derived (commutator u v)
commutator-member u v = begin
  ((u • v) • G._⁻¹ u) • G._⁻¹ v ≈⟨ cong assoc refl ⟩
  (u • (v • G._⁻¹ u)) • G._⁻¹ v
    ≈⟨ cong (cong refl (axiom (commute v (G._⁻¹ u)))) refl ⟩
  (u • (G._⁻¹ u • v)) • G._⁻¹ v
    ≈⟨ trans (cong (sym assoc) refl) assoc ⟩
  (u • G._⁻¹ u) • (v • G._⁻¹ v)
    ≈⟨ cong (G.inverseʳ {g = u}) (G.inverseʳ {g = v}) ⟩
  ε • ε ≈⟨ left-unit ⟩
  ε ∎

abelian-group : Group 0ℓ 0ℓ
abelian-group = G.•-ε-group

private
  module Mono = MonoidMorphisms (Group.rawMonoid abelian-group) (Group.rawMonoid C₂×C₂)
  module Maps = GroupMorphisms (Group.rawGroup abelian-group) (Group.rawGroup C₂×C₂)

  monoid-homomorphism : Mono.IsMonoidHomomorphism character
  monoid-homomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = sound }
      ; homo = character-product
      }
    ; ε-homo = Eq.refl
    }

isomorphism : Maps.IsGroupIsomorphism character
isomorphism = record
  { isGroupMonomorphism = record
    { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
        abelian-group C₂×C₂ monoid-homomorphism
    ; injective = complete
    }
  ; surjective = λ c → rep c , λ eq → Eq.trans (sound eq) (representatives c)
  }
