------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 5.5 and Corollary 5.6, for n = 2(k + 1): I ⊗ H can be moved
-- past any word G over 𝒢ₙ, (I⊗H) G ≈ G′ (I⊗H) with G′ over 𝒢ₙ, so
-- every word over ℱₙ is G (I⊗H)^ℓ with G over 𝒢ₙ and ℓ ∈ {0, 1}.
--
-- For the basic generators (-1)_[0], X_[x,x+1] and K_[0,1,2,3] this is
-- Table 2 with (7a); the others are X g′ X for an adjacent X and a
-- generator g′ closer to a basic one (Conjugation.decompose, as in the
-- paper's appeal to Lemma A.19).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _%_ ; s≤s ; z≤n)

module Examples.Groups.CCX+HH-TwoLevel.Scaled.Normal (k : ℕ) where

open import Data.Bool.Base using (Bool ; true ; false ; not)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; _<_ ; fromℕ<)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics as S using (Gen ; M-gen ; X-gen ; K-gen)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Conjugation using (Basic ; size ; Step ; decompose)

n : ℕ
n = suc k ℕ.* 2

open PB (_===ᴸ_ {n}) hiding (_===_)
open PP (_===ᴸ_ {n}) using (word-setoid)

------------------------------------------------------------------------
-- Parities

private
  parity : ∀ m → m % 2 ≡ 0 ⊎ m % 2 ≡ 1
  parity zero = inj₁ ≡.refl
  parity (suc zero) = inj₂ ≡.refl
  parity (suc (suc m)) = parity m

  odd-suc : ∀ m → suc m % 2 ≡ 1 → m % 2 ≡ 0
  odd-suc zero _ = ≡.refl
  odd-suc (suc zero) ()
  odd-suc (suc (suc m)) h = odd-suc m h

  -- An even index below 2(j + 1) has its successor below it too.
  even-room : ∀ j t → t % 2 ≡ 0 → t ℕ.< suc j ℕ.* 2 → suc t ℕ.< suc j ℕ.* 2
  even-room j zero _ _ = s≤s (s≤s z≤n)
  even-room j (suc zero) () _
  even-room zero (suc (suc t)) _ (s≤s (s≤s ()))
  even-room (suc j) (suc (suc t)) h (s≤s (s≤s lt)) = s≤s (s≤s (even-room j t h lt))

------------------------------------------------------------------------
-- Moving I ⊗ H

HH : H • H ≈ ε
HH = axiom r7a

-- From H w H ≈ v to H w ≈ v H.
past : ∀ {w v : Word (Genᴸ n)} → H • w • H ≈ v → H • w ≈ v • H
past {w} {v} e = begin
  H • w                   ≈⟨ sym right-unit ⟩
  (H • w) • ε             ≈⟨ cright sym HH ⟩
  (H • w) • (H • H)       ≈⟨ sym assoc ⟩
  ((H • w) • H) • H       ≈⟨ cleft assoc ⟩
  (H • w • H) • H         ≈⟨ cleft e ⟩
  v • H                   ∎
  where open import Relation.Binary.Reasoning.Setoid word-setoid

-- Lemma 5.5 for a generator: (I⊗H) g ≈ g′ (I⊗H).
Past : Word (Gen n) → Set
Past w = Σ (Word (Gen n)) λ w′ → H • ⌊ w ⌋ʷ ≈ ⌊ w′ ⌋ʷ • H

private
  basic : (g : Gen n) → Basic g → Past [ g ]ʷ
  basic (M-gen a) a0 = ([ M-gen a ]ʷ • [ X-gen a one p ]ʷ • [ M-gen a ]ʷ) , past (axiom (r7c p a0 ≡.refl))
    where
    one : Fin n
    one = suc zero
    p : a < one
    p = ≡.subst (λ t → suc t ℕ.≤ 1) (≡.sym a0) ℕP.≤-refl
  basic (X-gen x y p) adj = by (parity (toℕ x))
    where
    by : toℕ x % 2 ≡ 0 ⊎ toℕ x % 2 ≡ 1 → Past [ X-gen x y p ]ʷ
    by (inj₁ ev) = [ M-gen y ]ʷ , past (axiom (r7d₀ p adj ev))
    by (inj₂ od) = odd (toℕ x) ≡.refl od
      where
      odd : ∀ t → toℕ x ≡ t → t % 2 ≡ 1 → Past [ X-gen x y p ]ʷ
      odd zero _ ()
      odd (suc t) tx _ = ([ X-gen x y p ]ʷ • [ K-gen w x y z wx p yz ]ʷ) , past (axiom (r7d₁ wx p yz tw adj tz od))
        where
        t<n : t ℕ.< n
        t<n = ℕP.<-trans (ℕP.n<1+n t) (≡.subst (ℕ._< n) tx (FinP.toℕ<n x))
        w : Fin n
        w = fromℕ< t<n
        tw : toℕ x ≡ suc (toℕ w)
        tw = ≡.trans tx (≡.cong suc (≡.sym (FinP.toℕ-fromℕ< t<n)))
        wx : w < x
        wx = ≡.subst (ℕ._≤ toℕ x) (≡.cong suc (≡.sym (FinP.toℕ-fromℕ< t<n))) (ℕP.≤-reflexive (≡.sym tx))
        yev : toℕ y % 2 ≡ 0
        yev = ≡.subst (λ m → m % 2 ≡ 0) (≡.sym (≡.trans adj (≡.cong suc tx))) (odd-suc t (≡.subst (λ m → m % 2 ≡ 1) tx od))
        sy<n : suc (toℕ y) ℕ.< n
        sy<n = even-room k (toℕ y) yev (FinP.toℕ<n y)
        z : Fin n
        z = fromℕ< sy<n
        tz : toℕ z ≡ suc (toℕ y)
        tz = FinP.toℕ-fromℕ< sy<n
        yz : y < z
        yz = ℕP.≤-reflexive (≡.sym tz)
  basic (K-gen a b c d p q r) (a0 , b1 , c2 , d3) = [ K-gen a b c d p q r ]ʷ , past (axiom (r7b p q r a0 b1 c2 d3))

  -- All generators, by induction on their distance to a basic one.
  gen : ∀ fuel (g : Gen n) → size g ℕ.< fuel → Past [ g ]ʷ
  gen zero g ()
  gen (suc fuel) g sz = by (decompose g)
    where
    by : Basic g ⊎ Step g → Past [ g ]ʷ
    by (inj₁ B) = basic g B
    by (inj₂ st) = (X′ • g″ • X′) , (begin
      H • ⌊ [ g ]ʷ ⌋ʷ                         ≈⟨ cright ⌊⌋-cong rel ⟩
      H • (Xw • [ ⌊ g′ ⌋ ]ʷ • Xw)              ≈⟨ sym assoc ⟩
      (H • Xw) • [ ⌊ g′ ⌋ ]ʷ • Xw              ≈⟨ cleft proj₂ PX ⟩
      (⌊ X′ ⌋ʷ • H) • [ ⌊ g′ ⌋ ]ʷ • Xw          ≈⟨ assoc ⟩
      ⌊ X′ ⌋ʷ • H • [ ⌊ g′ ⌋ ]ʷ • Xw            ≈⟨ cright sym assoc ⟩
      ⌊ X′ ⌋ʷ • (H • [ ⌊ g′ ⌋ ]ʷ) • Xw          ≈⟨ cright cleft proj₂ Pg ⟩
      ⌊ X′ ⌋ʷ • (⌊ g″ ⌋ʷ • H) • Xw              ≈⟨ cright assoc ⟩
      ⌊ X′ ⌋ʷ • ⌊ g″ ⌋ʷ • (H • Xw)              ≈⟨ cright cright proj₂ PX ⟩
      ⌊ X′ ⌋ʷ • ⌊ g″ ⌋ʷ • (⌊ X′ ⌋ʷ • H)          ≈⟨ cright sym assoc ⟩
      ⌊ X′ ⌋ʷ • (⌊ g″ ⌋ʷ • ⌊ X′ ⌋ʷ) • H          ≈⟨ sym assoc ⟩
      ⌊ X′ • g″ • X′ ⌋ʷ • H                    ∎)
      where
      open Step st
      open import Relation.Binary.Reasoning.Setoid word-setoid
      Xw = [ ⌊ X-gen x y xy ⌋ ]ʷ
      PX = basic (X-gen x y xy) adj
      X′ = proj₁ PX
      Pg = gen fuel g′ (ℕP.<-≤-trans small (ℕP.≤-pred sz))
      g″ = proj₁ Pg

-- Lemma 5.5.
lemma-5-5 : (w : Word (Gen n)) → Past w
lemma-5-5 [ g ]ʷ = gen (suc (size g)) g ℕP.≤-refl
lemma-5-5 ε = ε , trans right-unit (sym left-unit)
lemma-5-5 (u • v) = (u′ • v′) , (begin
  H • ⌊ u ⌋ʷ • ⌊ v ⌋ʷ          ≈⟨ sym assoc ⟩
  (H • ⌊ u ⌋ʷ) • ⌊ v ⌋ʷ        ≈⟨ cleft proj₂ Pu ⟩
  (⌊ u′ ⌋ʷ • H) • ⌊ v ⌋ʷ       ≈⟨ assoc ⟩
  ⌊ u′ ⌋ʷ • (H • ⌊ v ⌋ʷ)       ≈⟨ cright proj₂ Pv ⟩
  ⌊ u′ ⌋ʷ • (⌊ v′ ⌋ʷ • H)      ≈⟨ sym assoc ⟩
  (⌊ u′ ⌋ʷ • ⌊ v′ ⌋ʷ) • H      ∎)
  where
  open import Relation.Binary.Reasoning.Setoid word-setoid
  Pu = lemma-5-5 u
  Pv = lemma-5-5 v
  u′ = proj₁ Pu
  v′ = proj₁ Pv

------------------------------------------------------------------------
-- Corollary 5.6: the normal form G (I⊗H)^ℓ

Hᵇ : Bool → Word (Genᴸ n)
Hᵇ true = H
Hᵇ false = ε

NF : Word (Genᴸ n) → Set
NF w = Σ (Word (Gen n)) λ G → Σ Bool λ ℓ → w ≈ ⌊ G ⌋ʷ • Hᵇ ℓ

private
  H-Hᵇ : ∀ ℓ → H • Hᵇ ℓ ≈ Hᵇ (not ℓ)
  H-Hᵇ true = HH
  H-Hᵇ false = right-unit

nf : (w : Word (Genᴸ n)) → NF w
nf [ ⌊ g ⌋ ]ʷ = [ g ]ʷ , false , sym right-unit
nf [ IH ]ʷ = ε , true , sym left-unit
nf ε = ε , false , sym left-unit
nf (u • v) = by (nf u) (nf v)
  where
  open import Relation.Binary.Reasoning.Setoid word-setoid
  by : NF u → NF v → NF (u • v)
  by (G , false , eu) (G′ , ℓ′ , ev) = (G • G′) , ℓ′ , (begin
    u • v                              ≈⟨ cong eu ev ⟩
    (⌊ G ⌋ʷ • ε) • (⌊ G′ ⌋ʷ • Hᵇ ℓ′)     ≈⟨ cleft right-unit ⟩
    ⌊ G ⌋ʷ • (⌊ G′ ⌋ʷ • Hᵇ ℓ′)           ≈⟨ sym assoc ⟩
    (⌊ G ⌋ʷ • ⌊ G′ ⌋ʷ) • Hᵇ ℓ′           ∎)
  by (G , true , eu) (G′ , ℓ′ , ev) = (G • G″) , not ℓ′ , (begin
    u • v                              ≈⟨ cong eu ev ⟩
    (⌊ G ⌋ʷ • H) • (⌊ G′ ⌋ʷ • Hᵇ ℓ′)     ≈⟨ assoc ⟩
    ⌊ G ⌋ʷ • H • ⌊ G′ ⌋ʷ • Hᵇ ℓ′         ≈⟨ cright sym assoc ⟩
    ⌊ G ⌋ʷ • (H • ⌊ G′ ⌋ʷ) • Hᵇ ℓ′       ≈⟨ cright cleft proj₂ P ⟩
    ⌊ G ⌋ʷ • (⌊ G″ ⌋ʷ • H) • Hᵇ ℓ′       ≈⟨ cright assoc ⟩
    ⌊ G ⌋ʷ • ⌊ G″ ⌋ʷ • H • Hᵇ ℓ′         ≈⟨ sym assoc ⟩
    (⌊ G ⌋ʷ • ⌊ G″ ⌋ʷ) • (H • Hᵇ ℓ′)     ≈⟨ cright H-Hᵇ ℓ′ ⟩
    (⌊ G ⌋ʷ • ⌊ G″ ⌋ʷ) • Hᵇ (not ℓ′)     ∎)
    where
    P = lemma-5-5 G′
    G″ = proj₁ P
