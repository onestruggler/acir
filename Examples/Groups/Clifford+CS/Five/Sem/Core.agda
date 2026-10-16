------------------------------------------------------------------------
-- Presentations of groups
--
-- From five wires to four, for products of two-level operators
--
-- A product of two-level operators on five-bit vectors, conjugated by
-- the permutation of a bijection f, is the product on the images
-- (`conj-Π`).  When every image has its top bit 0, that product is the
-- control (Five.Sem.TL.ctrl) of the product of the four-wire operators
-- on the bottom bits (`ctrl-Π`).  As the control is injective, two
-- products on five wires that agree give products on four wires that
-- agree (`core`): the semantic half of the decoding's rules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Core where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl ; ctrl ; ctrl-∙ ; ctrl-ε ; ctrl-inj ; tl-ctrl ; F ; module Bij)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; blkOf)

private
  variable
    n : ℕ

-- A gadget with its two points.
Pt : ℕ → Set
Pt n = Kind × Bits n × Bits n

Πp : List (Pt n) → Scaled n
Πp []                  = ε∙
Πp ((V , p , q) ∷ L)   = tl (blkOf V) p q ∙ Πp L

-- The bottom four bits, and the vector with its top bit put back to 0.
low : Bits 5 → Bits 4
low (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ _ ∷ []) = x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []

top : Bits 5 → Bool
top (_ ∷ _ ∷ _ ∷ _ ∷ b ∷ []) = b

low-F : (y : Bits 5) → top y ≡ false → low y ++ F ≡ y
low-F (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ .false ∷ []) refl = refl

------------------------------------------------------------------------
-- Conjugation

module _ (f g : Bits n → Bits n) (fg : ∀ x → f (g x) ≡ x) (gf : ∀ x → g (f x) ≡ x) where
  open Bij f g fg gf using (conjS ; conj-cong ; conj-tl ; conj-∙ ; conj-ε)

  mapf : List (Pt n) → List (Pt n)
  mapf = map (λ { (V , p , q) → V , f p , f q })

  conj-Π : (L : List (Pt n)) → conjS (Πp L) ~ Πp (mapf L)
  conj-Π []                = conj-ε
  conj-Π ((V , p , q) ∷ L) =
    ~-trans {s = conjS (tl (blkOf V) p q ∙ Πp L)} {t = conjS (tl (blkOf V) p q) ∙ conjS (Πp L)}
            {u = Πp (mapf ((V , p , q) ∷ L))}
      (conj-∙ (tl (blkOf V) p q) (Πp L))
      (∙-cong {s = conjS (tl (blkOf V) p q)} {s' = tl (blkOf V) (f p) (f q)}
              {t = conjS (Πp L)} {t' = Πp (mapf L)}
        (conj-tl (blkOf V) p q) (conj-Π L))

------------------------------------------------------------------------
-- The control

ext : List (Pt 4) → List (Pt 5)
ext = map (λ { (V , a , b) → V , a ++ F , b ++ F })

ctrl-Π : (Q : List (Pt 4)) → ctrl (Πp Q) ~ Πp (ext Q)
ctrl-Π []                = ctrl-ε {4}
ctrl-Π ((V , a , b) ∷ Q) =
  ~-trans {s = ctrl (tl (blkOf V) a b ∙ Πp Q)} {t = ctrl (tl (blkOf V) a b) ∙ ctrl (Πp Q)}
          {u = Πp (ext ((V , a , b) ∷ Q))}
    (ctrl-∙ (tl (blkOf V) a b) (Πp Q))
    (∙-cong {s = ctrl (tl (blkOf V) a b)} {s' = tl (blkOf V) (a ++ F) (b ++ F)}
            {t = ctrl (Πp Q)} {t' = Πp (ext Q)}
      (~-sym {s = tl (blkOf V) (a ++ F) (b ++ F)} {t = ctrl (tl (blkOf V) a b)} (tl-ctrl (blkOf V) a b))
      (ctrl-Π Q))

------------------------------------------------------------------------
-- Down to four wires

-- Both points of every gadget have top bit 0.
OnHalf : List (Pt 5) → Set
OnHalf = All (λ { (V , p , q) → top p ≡ false × top q ≡ false })

lows : List (Pt 5) → List (Pt 4)
lows = map (λ { (V , p , q) → V , low p , low q })

ext-lows : (L : List (Pt 5)) → OnHalf L → ext (lows L) ≡ L
ext-lows []                []             = refl
ext-lows ((V , p , q) ∷ L) ((hp , hq) ∷ h) =
  Eq.cong₂ _∷_ (Eq.cong₂ (λ x y → V , x , y) (low-F p hp) (low-F q hq)) (ext-lows L h)

module _ (f g : Bits 5 → Bits 5) (fg : ∀ x → f (g x) ≡ x) (gf : ∀ x → g (f x) ≡ x) where
  open Bij f g fg gf using (conjS ; conj-cong)

  core : (L L′ : List (Pt 5)) → Πp L ~ Πp L′ →
         OnHalf (mapf f g fg gf L) → OnHalf (mapf f g fg gf L′) →
         Πp (lows (mapf f g fg gf L)) ~ Πp (lows (mapf f g fg gf L′))
  core L L′ e h h′ = ctrl-inj {s = Πp (lows M)} {t = Πp (lows M′)} step
    where
    M M′ : List (Pt 5)
    M  = mapf f g fg gf L
    M′ = mapf f g fg gf L′

    upΠ : (K : List (Pt 5)) → OnHalf K → ctrl (Πp (lows K)) ~ Πp K
    upΠ K hK = Eq.subst (λ X → ctrl (Πp (lows K)) ~ Πp X) (ext-lows K hK) (ctrl-Π (lows K))

    step : ctrl (Πp (lows M)) ~ ctrl (Πp (lows M′))
    step =
      ~-trans {s = ctrl (Πp (lows M))} {t = Πp M} {u = ctrl (Πp (lows M′))} (upΠ M h)
        (~-trans {s = Πp M} {t = conjS (Πp L)} {u = ctrl (Πp (lows M′))}
          (~-sym {s = conjS (Πp L)} {t = Πp M} (conj-Π f g fg gf L))
          (~-trans {s = conjS (Πp L)} {t = conjS (Πp L′)} {u = ctrl (Πp (lows M′))}
            (conj-cong {s = Πp L} {t = Πp L′} e)
            (~-trans {s = conjS (Πp L′)} {t = Πp M′} {u = ctrl (Πp (lows M′))}
              (conj-Π f g fg gf L′)
              (~-sym {s = ctrl (Πp (lows M′))} {t = Πp M′} (upΠ M′ h′)))))
