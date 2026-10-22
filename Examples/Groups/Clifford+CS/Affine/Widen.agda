------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine circuits one wire wider
--
-- An affine word on 4 + m wires, its wires renamed into 5 + m wires
-- (`ι*`, below the new top wire), is as a circuit the old one with an
-- idle wire on top (`ι*-top`): each letter's network, widened, is a
-- network for the renamed letter (NetTop, LocalPlace.place-eq).  And
-- the decoding's affine circuit at two states whose top bit is 0 is the
-- renamed one of the width below (`α-top`): the X's, the fan-out and its
-- pivot never reach the top wire.  With G one width up the white half of
-- the gate below, this is the paper's hyperplane lemma for the top wire.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Complete)

module Examples.Groups.Clifford+CS.Affine.Widen (m : ℕ) (c4 : Complete 4) where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Fin using (Fin ; toℕ ; inject₁) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (inject₁-injective)
import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (zero ; suc ; _<_ ; s≤s ; z≤n)
open import Data.Product using (proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; _∷ʳ_)
import Data.Empty.Irrelevant as Irr
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import Notations using (₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.PermCalc using (perm ; revS ; perm-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; place-eq)
open import Examples.Groups.Clifford+CS.Networks using (bring₁ ; bring₂)
open import Examples.Groups.Clifford+CS.NetTop using (topS ; perm-top ; pl-top)

import Examples.Groups.Clifford+CS.Affine.Theory (₃₊ m) as A₀
import Examples.Groups.Clifford+CS.Affine.Theory (₄₊ m) as A₁
import Examples.Groups.Clifford+CS.Affine.Equivariance (₃₊ m) as E₀
import Examples.Groups.Clifford+CS.Affine.Equivariance (₄₊ m) as E₁
import Examples.Groups.Clifford+CS.Affine.Alpha (₃₊ m) as Al₀
import Examples.Groups.Clifford+CS.Affine.Alpha (₄₊ m) as Al₁
import Examples.Groups.Clifford+CS.Affine.Circuits m c4 as C₀
import Examples.Groups.Clifford+CS.Affine.Circuits (suc m) c4 as C₁

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Renaming the wires below the new top

ιL : A₀.Lt → A₁.Lt
ιL (A₀.xL a)     = A₁.xL (inject₁ a)
ιL (A₀.tL u v p) = A₁.tL (inject₁ u) (inject₁ v) (λ e → p (inject₁-injective e))

ι* : Word A₀.Lt → Word A₁.Lt
ι* = wmap ιL

ι*-rev : ∀ (w : Word A₀.Lt) → ι* (A₀.rev w) ≡ A₁.rev (ι* w)
ι*-rev [ a ]ʷ  = Eq.refl
ι*-rev ε       = Eq.refl
ι*-rev (u • v) = Eq.cong₂ _•_ (ι*-rev v) (ι*-rev u)

------------------------------------------------------------------------
-- As circuits: an idle wire on top

private
  back-to : ∀ {n} (σ : Word (S.Gen n)) {a i} →
            perm σ ⟨$⟩ʳ a ≡ i → perm (revS σ) ⟨$⟩ʳ i ≡ a
  back-to σ {a} e = Eq.subst (λ x → perm (revS σ) ⟨$⟩ʳ x ≡ a) e (perm-inv σ a)

  module T₁ = Tools ((suc (₄₊ m)) VRel,_===_)

  ≡→≈ : ∀ {a b : Circuit (suc (₄₊ m))} → a ≡ b → (suc (₄₊ m)) ⊢ a ≈ b
  ≡→≈ Eq.refl = T₁.refl

ιL-top : ∀ (a : A₀.Lt) → (suc (₄₊ m)) ⊢ C₁.⟪ ιL a ⟫ ≈ top C₀.⟪ a ⟫
ιL-top (A₀.xL a) =
  T₁.trans (place-eq {k = 1} X b₁ (topS b₀) agree) (T₁.sym (≡→≈ (pl-top b₀ X)))
  where
  B₀ = bring₁ a
  b₀ = proj₁ B₀
  B₁ = bring₁ (inject₁ a)
  b₁ = proj₁ B₁
  agree : ∀ (j : Fin (suc (₄₊ m))) → toℕ j < 1 → perm (topS b₀) ⟨$⟩ʳ (perm (revS b₁) ⟨$⟩ʳ j) ≡ j
  agree 0F _ =
    Eq.trans (Eq.cong (perm (topS b₀) ⟨$⟩ʳ_) (back-to b₁ (proj₂ B₁)))
             (Eq.trans (perm-top b₀ a) (Eq.cong inject₁ (proj₂ B₀)))
  agree (sF j) (s≤s ())
ιL-top (A₀.tL u v p) =
  T₁.trans (place-eq {k = 2} CX₁₀ b₁ (topS b₀) agree) (T₁.sym (≡→≈ (pl-top b₀ CX₁₀)))
  where
  B₀ = bring₂ v u (C₀.ne p)
  b₀ = proj₁ B₀
  B₁ = bring₂ (inject₁ v) (inject₁ u) (C₁.ne (λ e → p (inject₁-injective e)))
  b₁ = proj₁ B₁
  agree : ∀ (j : Fin (suc (₄₊ m))) → toℕ j < 2 → perm (topS b₀) ⟨$⟩ʳ (perm (revS b₁) ⟨$⟩ʳ j) ≡ j
  agree 0F _ =
    Eq.trans (Eq.cong (perm (topS b₀) ⟨$⟩ʳ_) (back-to b₁ (proj₁ (proj₂ B₁))))
             (Eq.trans (perm-top b₀ v) (Eq.cong inject₁ (proj₁ (proj₂ B₀))))
  agree (sF 0F) _ =
    Eq.trans (Eq.cong (perm (topS b₀) ⟨$⟩ʳ_) (back-to b₁ (proj₂ (proj₂ B₁))))
             (Eq.trans (perm-top b₀ u) (Eq.cong inject₁ (proj₂ (proj₂ B₀))))
  agree (sF (sF j)) (s≤s (s≤s ()))

ι*-top : ∀ (w : Word A₀.Lt) → (suc (₄₊ m)) ⊢ C₁.⟪ ι* w ⟫ʷ ≈ top C₀.⟪ w ⟫ʷ
ι*-top [ a ]ʷ  = ιL-top a
ι*-top ε       = T₁.refl
ι*-top (u • v) = T₁.cong (ι*-top u) (ι*-top v)

------------------------------------------------------------------------
-- The affine circuits at states with the top bit 0

_⁺ : ∀ {j} → Vec Bool j → Vec Bool (suc j)
p ⁺ = p ∷ʳ false

⊕-⁺ : ∀ {j} (p q : Vec Bool j) → Al₁._⊕_ (p ⁺) (q ⁺) ≡ (Al₀._⊕_ p q) ⁺
⊕-⁺ []      []      = Eq.refl
⊕-⁺ (a ∷ p) (b ∷ q) = Eq.cong ((a xor b) ∷_) (⊕-⁺ p q)

private
  xs-⁺ : ∀ (p : Vec Bool k) (ι : Fin (suc k) → A₁.Wire) → Al₁.xs (p ⁺) ι ≡ Al₁.xs p (λ i → ι (inject₁ i))
  xs-⁺ []          ι = Eq.refl
  xs-⁺ (true  ∷ p) ι = Eq.cong (A₁.X (ι 0F) •_) (xs-⁺ p (λ i → ι (sF i)))
  xs-⁺ (false ∷ p) ι = xs-⁺ p (λ i → ι (sF i))

  ι*-xs : ∀ (p : Vec Bool k) (ι : Fin k → A₀.Wire) → ι* (Al₀.xs p ι) ≡ Al₁.xs p (λ i → inject₁ (ι i))
  ι*-xs []          ι = Eq.refl
  ι*-xs (true  ∷ p) ι = Eq.cong ([ A₁.xL (inject₁ (ι 0F)) ]ʷ •_) (ι*-xs p (λ i → ι (sF i)))
  ι*-xs (false ∷ p) ι = ι*-xs p (λ i → ι (sF i))

  fan-⁺ : ∀ (w : Vec Bool k) (ι : Fin (suc k) → Fin (₄₊ m)) → A₁.fan (w ⁺) ι ≡ A₁.fan w (λ i → ι (inject₁ i))
  fan-⁺ []          ι = Eq.refl
  fan-⁺ (true  ∷ w) ι = Eq.cong (A₁.T0 (ι 0F) •_) (fan-⁺ w (λ i → ι (sF i)))
  fan-⁺ (false ∷ w) ι = fan-⁺ w (λ i → ι (sF i))

  ι*-fan : ∀ (w : Vec Bool k) (ι : Fin k → Fin (₃₊ m)) → ι* (A₀.fan w ι) ≡ A₁.fan w (λ i → inject₁ (ι i))
  ι*-fan []          ι = Eq.refl
  ι*-fan (true  ∷ w) ι = Eq.cong (A₁.T0 (inject₁ (ι 0F)) •_) (ι*-fan w (λ i → ι (sF i)))
  ι*-fan (false ∷ w) ι = ι*-fan w (λ i → ι (sF i))

  first-⁺ : ∀ (w : Vec Bool k) → E₁.first (w ⁺) ≡ Maybe.map inject₁ (E₀.first w)
  first-⁺ []          = Eq.refl
  first-⁺ (true  ∷ w) = Eq.refl
  first-⁺ (false ∷ w) = Eq.trans (Eq.cong (Maybe.map sF) (first-⁺ w)) (map-sF-inject (E₀.first w))
    where
    map-sF-inject : ∀ {j} (x : Maybe (Fin j)) → Maybe.map sF (Maybe.map inject₁ x) ≡ Maybe.map inject₁ (Maybe.map sF x)
    map-sF-inject nothing  = Eq.refl
    map-sF-inject (just i) = Eq.refl

  F-⁺ : ∀ (w : Vec Bool (₃₊ m)) → E₁.F (w ⁺) ≡ ι* (E₀.F w)
  F-⁺ w = Eq.trans (fan-⁺ w (λ i → i)) (Eq.sym (ι*-fan w (λ i → i)))

  L₀-⁺ : ∀ (w : Vec Bool (₃₊ m)) (x : Maybe (Fin (₃₊ m))) → E₀.first w ≡ x →
         E₁.L₀ (Maybe.map inject₁ x) (w ⁺) ≡ ι* (E₀.L₀ x w)
  L₀-⁺ w nothing  _ = Eq.refl
  L₀-⁺ w (just j) _ = Eq.cong (A₁.T (sF (inject₁ j)) 0F A₁.s≢0 •_) (F-⁺ w)

L-⁺ : ∀ (w : Vec Bool (₄₊ m)) → E₁.L (w ⁺) ≡ ι* (E₀.L w)
L-⁺ (true  ∷ w) = F-⁺ w
L-⁺ (false ∷ w) =
  Eq.trans (Eq.cong (λ x → E₁.L₀ x (w ⁺)) (first-⁺ w)) (L₀-⁺ w (E₀.first w) Eq.refl)

α-⁺ : ∀ (p q : Vec Bool (₄₊ m)) → Al₁.α (p ⁺) (q ⁺) ≡ ι* (Al₀.α p q)
α-⁺ p q =
  Eq.cong₂ _•_ (Eq.trans (xs-⁺ p (λ i → i)) (Eq.sym (ι*-xs p (λ i → i))))
               (Eq.trans (Eq.cong E₁.L (⊕-⁺ p q)) (L-⁺ (Al₀._⊕_ p q)))
