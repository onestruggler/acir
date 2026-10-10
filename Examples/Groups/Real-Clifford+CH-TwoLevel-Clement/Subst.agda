------------------------------------------------------------------------
-- Presentations of groups
--
-- Substitutions in forms (Forms).
--
-- * substF v h f: the form f with its variable v replaced by the form h,
--   whose value is that of f at ρ with ρ v replaced by the value of h;
-- * a split on a form g, whose coefficient at v is 1, substitutes
--   b - (g - v) + √2 v for v, where b is the parity of g: every value
--   of the forms is a value of the substituted forms for b = 0 or b = 1
--   (split-sound), which makes the parity of g that b;
-- * liftF prepends a variable that f does not involve.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Subst where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Integer.Base using (+_)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (∃ ; ∃₂ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_ ; _[_]≔_)
open import Relation.Binary.PropositionalEquality

open import Quantum.Synthesis.Ring using (RootTwo)
open import Examples.Groups.Clifford+CS-TwoLevel.Vector using (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (Z ; module ZR ; module ZG ; √2ᶻ ; oddᶻ ; even⇒δ∣ ; oddᶻ-+)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms

open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

private
  variable
    r : ℕ

------------------------------------------------------------------------
-- Scaling

infixr 7 _⊛_

_⊛_ : Z → Form r → Form r
c ⊛ form k cs = form (c ZR.* k) (Vec.map (c ZR.*_) cs)

private
  dot-⊛ : (c : Z) (cs ρ : Vec Z r) → dot (Vec.map (c ZR.*_) cs) ρ ≡ c ZR.* dot cs ρ
  dot-⊛ c [] [] = ZG.solve 1 (λ c → con ZR.0# := c :* con ZR.0#) refl c
  dot-⊛ c (d ∷ cs) (x ∷ ρ) =
    trans (cong ((c ZR.* d) ZR.* x ZR.+_) (dot-⊛ c cs ρ))
      (ZG.solve 4 (λ c d x t → c :* d :* x :+ c :* t := c :* (d :* x :+ t)) refl c d x (dot cs ρ))

⟦⊛⟧ : ∀ (c : Z) (f : Form r) ρ → ⟦ c ⊛ f ⟧ ρ ≡ c ZR.* ⟦ f ⟧ ρ
⟦⊛⟧ c (form k cs) ρ =
  trans (cong (c ZR.* k ZR.+_) (dot-⊛ c cs ρ)) (ZG.solve 3 (λ c k t → c :* k :+ c :* t := c :* (k :+ t)) refl c k (dot cs ρ))

------------------------------------------------------------------------
-- Substitution

substF : Fin r → Form r → Form r → Form r
substF v h (form k cs) = form k (cs [ v ]≔ ZR.0#) ⊕ ((cs ! v) ⊛ h)

private
  -- A dot product with one variable changed.
  dot-upd : (v : Fin r) (cs ρ : Vec Z r) (c y : Z) →
            dot (cs [ v ]≔ c) (ρ [ v ]≔ y) ≡ dot (cs [ v ]≔ ZR.0#) ρ ZR.+ c ZR.* y
  dot-upd zero (d ∷ cs) (x ∷ ρ) c y =
    ZG.solve 4 (λ c y x t → c :* y :+ t := con ZR.0# :* x :+ t :+ c :* y) refl c y x (dot cs ρ)
  dot-upd (suc v) (d ∷ cs) (x ∷ ρ) c y =
    trans (cong (d ZR.* x ZR.+_) (dot-upd v cs ρ c y))
      (ZG.solve 4 (λ d x t u → d :* x :+ (t :+ u) := d :* x :+ t :+ u) refl d x (dot (cs [ v ]≔ ZR.0#) ρ) (c ZR.* y))

  upd-self : (v : Fin r) (cs : Vec Z r) → cs [ v ]≔ (cs ! v) ≡ cs
  upd-self zero (c ∷ cs) = refl
  upd-self (suc v) (c ∷ cs) = cong (c ∷_) (upd-self v cs)

  upd-upd : (v : Fin r) (ρ : Vec Z r) (y z : Z) → (ρ [ v ]≔ y) [ v ]≔ z ≡ ρ [ v ]≔ z
  upd-upd zero (x ∷ ρ) y z = refl
  upd-upd (suc v) (x ∷ ρ) y z = cong (x ∷_) (upd-upd v ρ y z)

  upd-! : (v : Fin r) (ρ : Vec Z r) (y : Z) → (ρ [ v ]≔ y) ! v ≡ y
  upd-! zero (x ∷ ρ) y = refl
  upd-! (suc v) (x ∷ ρ) y = upd-! v ρ y

  -- The value of a form with its variable v changed.
  ⟦upd⟧ : (v : Fin r) (k : Z) (cs ρ : Vec Z r) (y : Z) →
          ⟦ form k cs ⟧ (ρ [ v ]≔ y) ≡ ⟦ form k (cs [ v ]≔ ZR.0#) ⟧ ρ ZR.+ (cs ! v) ZR.* y
  ⟦upd⟧ v k cs ρ y =
    trans (cong (λ cs′ → k ZR.+ dot cs′ (ρ [ v ]≔ y)) (sym (upd-self v cs)))
      (trans (cong (k ZR.+_) (dot-upd v cs ρ (cs ! v) y))
        (ZG.solve 3 (λ k t u → k :+ (t :+ u) := k :+ t :+ u) refl k (dot (cs [ v ]≔ ZR.0#) ρ) ((cs ! v) ZR.* y)))

⟦substF⟧ : ∀ (v : Fin r) (h f : Form r) ρ → ⟦ substF v h f ⟧ ρ ≡ ⟦ f ⟧ (ρ [ v ]≔ ⟦ h ⟧ ρ)
⟦substF⟧ v h (form k cs) ρ =
  trans (⟦⊕⟧ (form k (cs [ v ]≔ ZR.0#)) ((cs ! v) ⊛ h) ρ)
    (trans (cong (⟦ form k (cs [ v ]≔ ZR.0#) ⟧ ρ ZR.+_) (⟦⊛⟧ (cs ! v) h ρ))
      (sym (⟦upd⟧ v k cs ρ (⟦ h ⟧ ρ))))

------------------------------------------------------------------------
-- Splits

-- The parity bit as an element.
bitᶻ : Bool → Z
bitᶻ false = ZR.0#
bitᶻ true = ZR.1#

-- The coefficient 1.
isOne : Z → Bool
isOne (RootTwo (+ 1) (+ 0)) = true
isOne _ = false

isOne-sound : ∀ c → isOne c ≡ true → c ≡ ZR.1#
isOne-sound (RootTwo (+ 1) (+ 0)) _ = refl
isOne-sound (RootTwo (+ zero) _) ()
isOne-sound (RootTwo (+ suc (suc _)) _) ()
isOne-sound (RootTwo (+ 1) (+ suc _)) ()
isOne-sound (RootTwo (+ 1) (Data.Integer.Base.-[1+ _ ])) ()
isOne-sound (RootTwo (Data.Integer.Base.-[1+ _ ]) _) ()

-- The form substituted for v on the branch b of a split on g.
splitH : Fin r → Form r → Bool → Form r
splitH v (form k cs) b = form (bitᶻ b ZR.- k) ((Vec.map ZR.-_ cs) [ v ]≔ √2ᶻ)

private
  bit-odd : ∀ x → oddᶻ (x ZR.- bitᶻ (oddᶻ x)) ≡ false
  bit-odd x with oddᶻ x in o
  ... | false = trans (oddᶻ-+ x (ZR.- ZR.0#)) (cong (_xor false) o)
  ... | true = trans (oddᶻ-+ x (ZR.- ZR.1#)) (cong (_xor true) o)

  dot-neg′ : (cs ρ : Vec Z r) → dot (Vec.map ZR.-_ cs) ρ ≡ ZR.- dot cs ρ
  dot-neg′ [] [] = ZG.solve 0 (con ZR.0# := :- con ZR.0#) refl
  dot-neg′ (c ∷ cs) (x ∷ ρ) =
    trans (cong ((ZR.- c) ZR.* x ZR.+_) (dot-neg′ cs ρ))
      (ZG.solve 3 (λ c x s → (:- c) :* x :+ (:- s) := :- (c :* x :+ s)) refl c x (dot cs ρ))

  map-upd : (v : Fin r) (cs : Vec Z r) → Vec.map ZR.-_ (cs [ v ]≔ ZR.0#) ≡ (Vec.map ZR.-_ cs) [ v ]≔ ZR.0#
  map-upd zero (c ∷ cs) = cong (_∷ Vec.map ZR.-_ cs) (ZG.solve 0 (:- con ZR.0# := con ZR.0#) refl)
  map-upd (suc v) (c ∷ cs) = cong (ZR.- c ∷_) (map-upd v cs)

-- Every point is a point of one branch of a split.
split-sound : ∀ (v : Fin r) (g : Form r) → isOne (co g ! v) ≡ true → ∀ ρ →
              ∃₂ λ b ρ′ → ∀ f → ⟦ substF v (splitH v g b) f ⟧ ρ′ ≡ ⟦ f ⟧ ρ
split-sound v (form k cs) one ρ = b , ρ′ , λ f → trans (⟦substF⟧ v h f ρ′) (cong ⟦ f ⟧ back)
  where
  G = ⟦ form k cs ⟧ ρ
  b = oddᶻ G
  y = proj₁ (even⇒δ∣ (G ZR.- bitᶻ b) (bit-odd G))
  ey : G ZR.- bitᶻ b ≡ √2ᶻ ZR.* y
  ey = proj₂ (even⇒δ∣ (G ZR.- bitᶻ b) (bit-odd G))
  ρ′ = ρ [ v ]≔ y
  h = splitH v (form k cs) b
  c1 : cs ! v ≡ ZR.1#
  c1 = isOne-sound (cs ! v) one
  -- G = k + rest + ρ v, rest the dot product without v.
  rest = dot (cs [ v ]≔ ZR.0#) ρ
  eG : G ≡ k ZR.+ rest ZR.+ ρ ! v
  eG = trans (cong (λ ρ″ → ⟦ form k cs ⟧ ρ″) (sym (upd-self v ρ)))
         (trans (⟦upd⟧ v k cs ρ (ρ ! v))
           (trans (cong (λ c → k ZR.+ rest ZR.+ c ZR.* (ρ ! v)) c1)
             (ZG.solve 3 (λ k t x → k :+ t :+ con ZR.1# :* x := k :+ t :+ x) refl k rest (ρ ! v))))
  eh : ⟦ h ⟧ ρ′ ≡ ρ ! v
  eh = begin
    bitᶻ b ZR.- k ZR.+ dot ((Vec.map ZR.-_ cs) [ v ]≔ √2ᶻ) ρ′
      ≡⟨ cong (bitᶻ b ZR.- k ZR.+_) (dot-upd v (Vec.map ZR.-_ cs) ρ √2ᶻ y) ⟩
    bitᶻ b ZR.- k ZR.+ (dot ((Vec.map ZR.-_ cs) [ v ]≔ ZR.0#) ρ ZR.+ √2ᶻ ZR.* y)
      ≡⟨ cong (λ t → bitᶻ b ZR.- k ZR.+ (t ZR.+ √2ᶻ ZR.* y))
              (trans (cong (λ u → dot u ρ) (sym (map-upd v cs))) (dot-neg′ (cs [ v ]≔ ZR.0#) ρ)) ⟩
    bitᶻ b ZR.- k ZR.+ (ZR.- rest ZR.+ √2ᶻ ZR.* y)
      ≡⟨ cong (λ t → bitᶻ b ZR.- k ZR.+ (ZR.- rest ZR.+ t)) (sym ey) ⟩
    bitᶻ b ZR.- k ZR.+ (ZR.- rest ZR.+ (G ZR.- bitᶻ b))
      ≡⟨ cong (λ t → bitᶻ b ZR.- k ZR.+ (ZR.- rest ZR.+ (t ZR.- bitᶻ b))) eG ⟩
    bitᶻ b ZR.- k ZR.+ (ZR.- rest ZR.+ (k ZR.+ rest ZR.+ ρ ! v ZR.- bitᶻ b))
      ≡⟨ ZG.solve 4 (λ c k t x → c :- k :+ (:- t :+ (k :+ t :+ x :- c)) := x) refl (bitᶻ b) k rest (ρ ! v) ⟩
    ρ ! v ∎
    where open ≡-Reasoning
  back : ρ′ [ v ]≔ ⟦ h ⟧ ρ′ ≡ ρ
  back = trans (cong (ρ′ [ v ]≔_) eh) (trans (upd-upd v ρ y (ρ ! v)) (upd-self v ρ))

------------------------------------------------------------------------
-- A new variable

liftF : Form r → Form (suc r)
liftF (form k cs) = form k (ZR.0# ∷ cs)

⟦liftF⟧ : ∀ (f : Form r) y ρ → ⟦ liftF f ⟧ (y ∷ ρ) ≡ ⟦ f ⟧ ρ
⟦liftF⟧ (form k cs) y ρ = ZG.solve 3 (λ k y t → k :+ (con ZR.0# :* y :+ t) := k :+ t) refl k y (dot cs ρ)
