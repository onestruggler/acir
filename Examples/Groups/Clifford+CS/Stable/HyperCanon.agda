------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 for decoded words at every width, from closed four-wire
-- checks
--
-- An equation of the decoding's alphabet becomes an equation between
-- two words over the indices of its letters (`IW`), read at a list of
-- basis states (`inst`).  Up to five distinct states are moved by an
-- affine word to a canonical position that depends only on their
-- pattern (Affine.Canon), whose images are four bits followed by zeros:
-- so by Stable.Hyper.hyper the equation at any states on 5 + m wires
-- follows from the one at the pattern's images on 4 + m, and by `hyper`
-- again (with the empty affine word) from the one at the pattern's
-- images on four wires.  `lemma`: if two index words decode equally at
-- the images of every pattern on four wires — closed equations, decided
-- with completeness there — they decode equally at every assignment of
-- distinct states on every width from five on; and, in the induction
-- on the width, with no closed check at all: equal semantics on 5 + m
-- wires and completeness on 4 + m suffice (`lemma-sem`, through
-- Stable.HyperSem).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
import Examples.Groups.Clifford+CS.Stable.Gadget as Gadget
import Examples.Groups.Clifford+CS.Stable.GadgetAll as GadgetAll

module Examples.Groups.Clifford+CS.Stable.HyperCanon
  (c4 : Complete 4) (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (K : Set) (G₄ : K → Circuit 4)
  (ind₄ : ∀ κ → Gadget.Indep₀ 0 c4 (f4 0) (f5 0) (tr 0) (G₄ κ))
  (f6 : ∀ κ → Gadget.TopTarget 0 c4 (f4 0) (f5 0) (tr 0) (G₄ κ))
  (ssym : ∀ κ m → Gadget.SwapSym (suc m) c4 (f4 (suc m)) (f5 (suc m)) (tr (suc m))
                    (GadgetAll.gad c4 f4 f5 tr (G₄ κ) (ind₄ κ) (f6 κ) (suc m)))
  where

open import Data.Bool using (Bool ; false)
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Nat using (zero ; _≤_)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; replicate ; _++_ ; _∷ʳ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε)

import Examples.Groups.Clifford+CS.Affine.Alpha as Alpha
import Examples.Groups.Clifford+CS.Affine.Canon as Canon
import Examples.Groups.Clifford+CS.Affine.Widen as Widen
open import Examples.Groups.Clifford+CS.Stable.Hyper c4 f4 f5 tr K G₄ ind₄ f6 ssym
open import Examples.Groups.Clifford+CS.Stable.HyperSem c4 f4 f5 tr K G₄ ind₄ f6 ssym using (hyper-sem)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)

private
  variable
    a b k : ℕ

------------------------------------------------------------------------
-- Words over the indices of a list of states

IW : ℕ → Set
IW k = List (K × Fin k × Fin k)

at : Vec (Vec Bool a) k → K × Fin k × Fin k → K × Vec Bool a × Vec Bool a
at ps (κ , i , j) = κ , lookup ps i , lookup ps j

inst : Vec (Vec Bool a) k → IW k → List (K × Vec Bool a × Vec Bool a)
inst ps = map (at ps)

ne-at : Vec (Vec Bool a) k → K × Fin k × Fin k → Set
ne-at ps (κ , i , j) = lookup ps i ≢ lookup ps j

-- Every letter's two indices name distinct states.
NeW : Vec (Vec Bool a) k → IW k → Set
NeW ps = All (ne-at ps)

private
  ne-inst : ∀ {m} (ps : Vec (Vec Bool (₄₊ m)) k) (w : IW k) → NeW ps w → Ne (inst ps w)
  ne-inst ps []                []       = []
  ne-inst ps ((κ , i , j) ∷ w) (n ∷ ns) = n ∷ ne-inst ps w ns

  inst-map : ∀ (f : Vec Bool a → Vec Bool b) (ps : Vec (Vec Bool a) k) (qs : Vec (Vec Bool b) k) →
             (∀ i → f (lookup ps i) ≡ lookup qs i) → ∀ w → map (trip f) (inst ps w) ≡ inst qs w
  inst-map f ps qs h []                = Eq.refl
  inst-map f ps qs h ((κ , i , j) ∷ w) =
    Eq.cong₂ _∷_ (Eq.cong₂ (λ x y → κ , x , y) (h i) (h j)) (inst-map f ps qs h w)

  -- Distinct images have distinct sources.
  ne-map : ∀ (f : Vec Bool a → Vec Bool b) (ps : Vec (Vec Bool a) k) (qs : Vec (Vec Bool b) k) →
           (∀ i → f (lookup ps i) ≡ lookup qs i) → ∀ w → NeW qs w → NeW ps w
  ne-map f ps qs h []                []       = []
  ne-map f ps qs h ((κ , i , j) ∷ w) (n ∷ ns) =
    (λ e → n (Eq.trans (Eq.sym (h i)) (Eq.trans (Eq.cong f e) (h j)))) ∷ ne-map f ps qs h w ns

  -- An injective map keeps distinct states distinct.
  ne-inj : ∀ (f : Vec Bool a → Vec Bool b) (ps : Vec (Vec Bool a) k) (qs : Vec (Vec Bool b) k) →
           (∀ {x y} → f x ≡ f y → x ≡ y) → (∀ i → f (lookup ps i) ≡ lookup qs i) →
           ∀ w → NeW ps w → NeW qs w
  ne-inj f ps qs inj h []                []       = []
  ne-inj f ps qs inj h ((κ , i , j) ∷ w) (n ∷ ns) =
    (λ e → n (inj (Eq.trans (h i) (Eq.trans e (Eq.sym (h j)))))) ∷ ne-inj f ps qs inj h w ns

------------------------------------------------------------------------
-- Patterns at every width

-- Canon's patterns do not depend on the width, but the type does, by
-- the module parameter: copy one across.
cp : ∀ {a b r j} → Canon.Pat a r j → Canon.Pat b r j
cp Canon.done      = Canon.done
cp (Canon.new p)   = Canon.new (cp p)
cp (Canon.old c p) = Canon.old c (cp p)

private
  ext-indep : ∀ a b {r} (c : Vec Bool r) → Canon.ext a c ≡ Canon.ext b c
  ext-indep a b []                    = Eq.refl
  ext-indep a b (x ∷ [])              = Eq.refl
  ext-indep a b (x ∷ y ∷ [])          = Eq.refl
  ext-indep a b (x ∷ y ∷ z ∷ [])      = Eq.refl
  ext-indep a b (x ∷ y ∷ z ∷ w ∷ c)   = Eq.refl

  unitR-indep : ∀ a b r → Canon.unitR a r ≡ Canon.unitR b r
  unitR-indep a b zero    = Eq.refl
  unitR-indep a b (suc r) = Eq.cong (false ∷_) (unitR-indep a b r)

  rep-up : ∀ n → replicate n false ∷ʳ false ≡ false ∷ replicate n false
  rep-up zero    = Eq.refl
  rep-up (suc n) = Eq.cong (false ∷_) (rep-up n)

  pad-up : ∀ (c : Vec Bool 4) (n : ℕ) → (c ++ replicate n false) ∷ʳ false ≡ c ++ replicate (suc n) false
  pad-up (x ∷ y ∷ z ∷ w ∷ []) n = Eq.cong (λ v → x ∷ y ∷ z ∷ w ∷ v) (rep-up n)

-- One width up, the images of a pattern are those a width down with a 0
-- on top.
imgs-up : ∀ m {a r j} (p : Canon.Pat a r j) (i : Fin j) →
          Widen._⁺ m c4 (lookup (Canon.imgs m (cp p)) i) ≡ lookup (Canon.imgs (suc m) (cp p)) i
imgs-up m {r = r} (Canon.new p) 0F =
  Eq.trans (pad-up (Canon.ext m (Canon.unitR m r)) m)
    (Eq.cong (λ v → v ++ replicate (suc m) false)
       (Eq.trans (ext-indep m (suc m) (Canon.unitR m r)) (Eq.cong (Canon.ext (suc m)) (unitR-indep m (suc m) r))))
imgs-up m (Canon.new p)   (sF i) = imgs-up m p i
imgs-up m (Canon.old c p) 0F     =
  Eq.trans (pad-up (Canon.ext m c) m) (Eq.cong (λ v → v ++ replicate (suc m) false) (ext-indep m (suc m) c))
imgs-up m (Canon.old c p) (sF i) = imgs-up m p i

private
  imgs-cpcp : ∀ {a b r j} (p : Canon.Pat a r j) (i : Fin j) →
              lookup (Canon.imgs a (cp (cp {b = b} p))) i ≡ lookup (Canon.imgs a p) i
  imgs-cpcp (Canon.new p)   0F     = Eq.refl
  imgs-cpcp (Canon.new p)   (sF i) = imgs-cpcp p i
  imgs-cpcp (Canon.old c p) 0F     = Eq.refl
  imgs-cpcp (Canon.old c p) (sF i) = imgs-cpcp p i

------------------------------------------------------------------------
-- Lemma 8.8 for decoded words

module _ {j : ℕ} (w₁ w₂ : IW (suc j))
  (closed : ∀ (p : Canon.Pat 0 0 (suc j)) → NeW (Canon.imgs 0 p) w₁ → NeW (Canon.imgs 0 p) w₂ →
            4 ⊢ᵧ D 0 (inst (Canon.imgs 0 p) w₁) ≈ D 0 (inst (Canon.imgs 0 p) w₂))
  where

  -- At the images of a pattern, on every width from four on.
  at-pattern : ∀ m (p : Canon.Pat 0 0 (suc j)) →
               NeW (Canon.imgs m (cp p)) w₁ → NeW (Canon.imgs m (cp p)) w₂ →
               (₄₊ m) ⊢ᵧ D m (inst (Canon.imgs m (cp p)) w₁) ≈ D m (inst (Canon.imgs m (cp p)) w₂)
  at-pattern zero    p n₁ n₂ = closed (cp p) n₁ n₂
  at-pattern (suc m) p n₁ n₂ =
    hyper m ε (inst I₁ w₁) (inst I₁ w₂) (inst I₀ w₁) (inst I₀ w₂)
      (ne-inst I₁ w₁ n₁) (ne-inst I₁ w₂ n₂) (eq w₁) (eq w₂)
      (at-pattern m p (ne-map (Widen._⁺ m c4) I₀ I₁ (imgs-up m p) w₁ n₁)
                      (ne-map (Widen._⁺ m c4) I₀ I₁ (imgs-up m p) w₂ n₂))
    where
    I₀ = Canon.imgs m (cp p)
    I₁ = Canon.imgs (suc m) (cp p)
    eq : ∀ w → ren m ε (inst I₁ w) ≡ up m (inst I₀ w)
    eq w = Eq.trans (inst-map (Alpha.amapʷ (₄₊ m) ε) I₁ I₁ (λ i → Eq.refl) w)
                    (Eq.sym (inst-map (Widen._⁺ m c4) I₀ I₁ (imgs-up m p) w))

  -- At any distinct states, on every width from five on.
  lemma : ∀ m (ps : Vec (Vec Bool (₄₊ (suc m))) (suc j)) → j ≤ 4 → NeW ps w₁ → NeW ps w₂ →
          (₄₊ (suc m)) ⊢ᵧ D (suc m) (inst ps w₁) ≈ D (suc m) (inst ps w₂)
  lemma m (p₀ ∷ ps) j≤ n₁ n₂ =
    hyper m τ (inst (p₀ ∷ ps) w₁) (inst (p₀ ∷ ps) w₂) (inst I₀ w₁) (inst I₀ w₂)
      (ne-inst (p₀ ∷ ps) w₁ n₁) (ne-inst (p₀ ∷ ps) w₂ n₂) (eq w₁) (eq w₂)
      (at-pattern m pat (ne₀ w₁ n₁) (ne₀ w₂ n₂))
    where
    module C₁ = Canon (suc m)
    module Al = Alpha (₄₊ m)
    c   = C₁.canon p₀ ps j≤
    τ   = C₁.Canon.τ c
    pat : Canon.Pat 0 0 (suc j)
    pat = cp (C₁.Canon.pat c)
    I₀ = Canon.imgs m (cp pat)
    I₁ = Canon.imgs (suc m) (cp pat)
    img : ∀ i → Al.amapʷ τ (lookup (p₀ ∷ ps) i) ≡ lookup I₁ i
    img i = Eq.trans (C₁.Canon.img c i) (Eq.sym (imgs-cpcp (C₁.Canon.pat c) i))
    eq : ∀ w → ren m τ (inst (p₀ ∷ ps) w) ≡ up m (inst I₀ w)
    eq w = Eq.trans (inst-map (Al.amapʷ τ) (p₀ ∷ ps) I₁ img w)
                    (Eq.sym (inst-map (Widen._⁺ m c4) I₀ I₁ (imgs-up m pat) w))
    ne₀ : ∀ w → NeW (p₀ ∷ ps) w → NeW I₀ w
    ne₀ w n = ne-map (Widen._⁺ m c4) I₀ I₁ (imgs-up m pat) w
                (ne-inj (Al.amapʷ τ) (p₀ ∷ ps) I₁ (Al.amapʷ-inj τ) img w n)

------------------------------------------------------------------------
-- Lemma 8.8 for decoded words from their semantics

-- At any distinct states on 5 + m wires, equal semantics make the two
-- decoded words equal, given completeness on 4 + m wires
-- (Stable.HyperSem): no closed check is needed.
lemma-sem : ∀ m → Completeᵧ (₄₊ m) → ∀ {j} (w₁ w₂ : IW (suc j)) (ps : Vec (Vec Bool (₄₊ (suc m))) (suc j)) →
            j ≤ 4 → NeW ps w₁ → NeW ps w₂ →
            ⟦ D (suc m) (inst ps w₁) ⟧ ~ ⟦ D (suc m) (inst ps w₂) ⟧ →
            (₄₊ (suc m)) ⊢ᵧ D (suc m) (inst ps w₁) ≈ D (suc m) (inst ps w₂)
lemma-sem m c {j} w₁ w₂ (p₀ ∷ ps) j≤ n₁ n₂ s =
  hyper-sem m c τ (inst (p₀ ∷ ps) w₁) (inst (p₀ ∷ ps) w₂) (inst I₀ w₁) (inst I₀ w₂)
    (ne-inst (p₀ ∷ ps) w₁ n₁) (ne-inst (p₀ ∷ ps) w₂ n₂) (eq w₁) (eq w₂) s
  where
  module C₁ = Canon (suc m)
  module Al = Alpha (₄₊ m)
  c′  = C₁.canon p₀ ps j≤
  τ   = C₁.Canon.τ c′
  pat : Canon.Pat 0 0 (suc j)
  pat = cp (C₁.Canon.pat c′)
  I₀ = Canon.imgs m (cp pat)
  I₁ = Canon.imgs (suc m) (cp pat)
  img : ∀ i → Al.amapʷ τ (lookup (p₀ ∷ ps) i) ≡ lookup I₁ i
  img i = Eq.trans (C₁.Canon.img c′ i) (Eq.sym (imgs-cpcp (C₁.Canon.pat c′) i))
  eq : ∀ w → ren m τ (inst (p₀ ∷ ps) w) ≡ up m (inst I₀ w)
  eq w = Eq.trans (inst-map (Al.amapʷ τ) (p₀ ∷ ps) I₁ img w)
                  (Eq.sym (inst-map (Widen._⁺ m c4) I₀ I₁ (imgs-up m pat) w))
