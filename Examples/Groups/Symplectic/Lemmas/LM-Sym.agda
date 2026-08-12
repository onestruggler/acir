{-# OPTIONS --cubical-compatible --safe #-}
--{-# OPTIONS --termination-depth=2 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')


open import Function using (_∘_)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.Vec hiding ([_])

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.LM-Sym (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
-- (Normalization.Boxes is re-exported below, through Section.)


open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open LM2

-- The box interpretations ([_]ᵃ … [_], and the BoxType/⟦_⟧ dispatcher)
-- live in Normalization.Section and are re-exported here, so that a box
-- written through this module and one written through Section are the
-- SAME function.  They used to be duplicated, clause for clause, which
-- made them distinct definitions: on an open argument neither side
-- reduces, so `LM.[ x ]ᵃ ≡ [ x ]ᵃ` needed a case split to prove (the
-- abox-eq / bbox-eq / dbox-eq bridges of BR.Two.ML'-Top, and the
-- composite bridges of Normalization.Pushing.SectionLMBridge).  Those
-- bridges remain true and remain proved by their existing clauses; they
-- are now trivial.
--
-- Only [_]ᵐˡ' is kept back: Section's is over ML' n from Boxes, whereas
-- the one below is over this module's own LM' n, built from Cosets2 /
-- Cosets3.  The two are genuinely different functions.
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  hiding ([_]ᵐˡ') public

private
  variable
    n : ℕ


-- B'_ab sends (X^-1 Z^0, X^a Z^b) to (X^-1 Z^ab , I).
B' = B
[_]ᵇ' : ∀ {n} → B' → Word (Gen (₂₊ n))
[_]ᵇ' {n} (a , b) = CZ^ a • H • CZ^ b

{- old
[_]ᵈ' : ∀ {n} → D → Word (Gen (₂₊ n))
[_]ᵈ' {n} (₀ , ₀) = Ex
[_]ᵈ' {n} (a@₀ , b@(₁₊ _)) = CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑ • Ex
[_]ᵈ' {n} (a@(₁₊ _) , b) = CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑ • Ex
-}

[_]ᵈ' : ∀ {n} → D → Word (Gen (₂₊ n))
[_]ᵈ' {n} (₀ , b) = CZ^ (- b) • Ex
[_]ᵈ' {n} (a@(₁₊ _) , b) = CZ^ (- a) • H ↑ • S^ -b/a ↑ • Ex
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

data Cosets2-noEx : Set where
  case-||ₐ : CZPowers → Postfix → Cosets2-noEx
  case-|| : CZPowers* → SPowers → Postfix → Cosets2-noEx
  case-| : MC → NF1 → Cosets2-noEx
  case-nf1 : NF1 → Cosets2-noEx

data Cosets3 : Set where
  case-I : D → Cosets2 → Cosets3
  case-II : D → Cosets2-noEx → B' → Cosets3

c2-emb : Cosets2-noEx → Cosets2
c2-emb (case-||ₐ x x₁) = case-||ₐ x x₁
c2-emb (case-|| x x₁ x₂) = case-|| x x₁ x₂
c2-emb (case-| x x₁) = case-| x x₁
c2-emb (case-nf1 x) = case-nf1 x

c1-emb : Cosets1-noε → Cosets1
c1-emb (HS^ x) = HS^ x

₁* : ℤ* ₚ
₁* = (₁ , λ ())

rm-mc : Cosets2-noEx →  Cosets2-noEx
rm-mc (case-||ₐ x x₁@(s , mc↑ , mc)) = case-||ₐ x (s , mc↑ , (₁* , ε))
rm-mc (case-|| x x₁ x₂@(s , mc↑ , mc)) = case-|| x x₁ (s , mc↑ , (₁* , ε))
rm-mc (case-| x x₁@(s , mc)) = case-| x ((s , ₁* , ε))
rm-mc (case-nf1 x@(s , mc)) = case-nf1 (s , ₁* , ε)

mc-of : Cosets2-noEx → MC
mc-of (case-||ₐ x x₁@(s , mc↑ , mc)) = mc
mc-of (case-|| x x₁ x₂@(s , mc↑ , mc)) = mc
mc-of (case-| x x₁@(s , mc)) = mc
mc-of (case-nf1 x@(s , mc)) = mc

-- update a mc such that if it sent P to Z before updating, then it
-- send P to X^-1 after updating. But it may produce extra S's.
update-mc : MC → SPowers × MC
update-mc (m , ε) = ₀ , (m ⁻¹ , HS^ ₀)
update-mc (m , HS^ k) = k * m ^2 , (m ⁻¹ , ε)

s-of-HM : MC → SPowers
s-of-HM = proj₁ ∘ update-mc

mc-of-HM : MC → MC
mc-of-HM = proj₂ ∘ update-mc

-- used in coset updating.
update-mc-in-c2 : Cosets2-noEx →  Cosets2-noEx
update-mc-in-c2 (case-||ₐ x x₁@(s , mc↑ , mc)) = case-||ₐ x (s + s-of-HM mc , mc↑ , mc-of-HM mc)
update-mc-in-c2 (case-|| x x₁ x₂@(s , mc↑ , mc)) = case-|| x x₁ (s + s-of-HM mc , mc↑ , mc-of-HM mc)
update-mc-in-c2 (case-| x x₁@(s , mc)) = case-| x ((s + s-of-HM mc , mc-of-HM mc))
update-mc-in-c2 (case-nf1 x@(s , mc)) = case-nf1 (s + s-of-HM mc , mc-of-HM mc)

⟦_⟧₃ : Cosets3 → Word (Gen (₃₊ n))
⟦ case-I d c2 ⟧₃ = [ d ]ᵈ • ⟦ c2 ⟧₂ ↑
⟦ case-II d c2 b ⟧₃ = [ d ]ᵈ • ⟦ c2-emb (rm-mc c2) ⟧₂ ↑ • [ b ]ᵇ • ⟦ mc-of c2 ⟧ₘ₊


LM' : (n : ℕ) → Set
LM' 0 = ⊤
LM' 1 = NF1
LM' 2 = Cosets2
LM' 3 = Cosets3
LM' (₄₊ n) = M (₄₊ n) × L' (₄₊ n) ⊎ D × LM' (₃₊ n) 

[_]ᵐˡ' : ∀ {n} → LM' n → Word (Gen n)
[_]ᵐˡ' {0} _ = ε
[_]ᵐˡ' {1} lm1 = ⟦ lm1 ⟧₁
[_]ᵐˡ' {2} lm2 = ⟦ lm2 ⟧₂
[_]ᵐˡ' {3} lm3 = ⟦ lm3 ⟧₃
[_]ᵐˡ' {₄₊ n} (inj₁ (m , l)) = [ m ]ᵐ • [ l ]ˡ'
[_]ᵐˡ' {₄₊ n} (inj₂ (d , lm)) = [ d ]ᵈ • [ lm ]ᵐˡ' ↑
