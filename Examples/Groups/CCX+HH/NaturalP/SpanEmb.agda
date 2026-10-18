------------------------------------------------------------------------
-- Presentations of groups
--
-- The linear map of an independent list.
--
-- An independent list L of k bit vectors gives an injective linear map
-- from 𝔽₂ᵏ, sending the i-th unit vector to the i-th vector of L
-- (`embL`, `embL-unit`), which AffineRoute's `route` then inverts by an
-- affine word.  Independence does not depend on the order of two blocks
-- of the list (`indep-swap`), and for at most three vectors it is the
-- non-vanishing of their nonempty sums (`indep₁`, `indep₂`, `indep₃`).
-- Differences of distinct states do not vanish (`diff-nz`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.SpanEmb where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_ ; _∧_)
open import Data.Bool.Properties using (xor-identityʳ ; xor-assoc ; xor-comm)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; replicate ; _++_ ; tabulate ; lookup)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (_⊕_ ; unit ; Lin ; Emb)
open import Examples.Groups.CCX+HH.NaturalP.Span
  using (comb ; Indep ; InSpan ; _⊕ᵥ_ ; comb-⊕ ; indep-extend)

private
  variable
    n m k j : ℕ

------------------------------------------------------------------------
-- Concatenated lists

comb-++ : (xs : Vec (State n) k) (ys : Vec (State n) j) (as : Vec Bool k) (bs : Vec Bool j) →
  comb (xs ++ ys) (as ++ bs) ≈s comb xs as ⊕ comb ys bs
comb-++ []       ys []       bs i = refl
comb-++ (x ∷ xs) ys (a ∷ as) bs i =
  trans (cong ((a ∧ x i) xor_) (comb-++ xs ys as bs i))
    (sym (xor-assoc (a ∧ x i) (comb xs as i) (comb ys bs i)))

private
  split : ∀ j {k} (cs : Vec Bool (j + k)) →
    Σ (Vec Bool j) λ bs → Σ (Vec Bool k) λ as → cs ≡ bs ++ as
  split zero    cs       = [] , cs , refl
  split (suc j) (c ∷ cs) with split j cs
  ... | bs , as , refl = (c ∷ bs) , as , refl

  ++-false : (as : Vec Bool k) (bs : Vec Bool j) → as ++ bs ≡ replicate (k + j) false →
    as ≡ replicate k false × bs ≡ replicate j false
  ++-false []       bs e = refl , e
  ++-false (a ∷ as) bs e with VecP.∷-injective e
  ... | refl , e′ = cong (false ∷_) (proj₁ (++-false as bs e′)) , proj₂ (++-false as bs e′)

  false-++ : ∀ j k → replicate j false ++ replicate k false ≡ replicate (j + k) false
  false-++ zero    k = refl
  false-++ (suc j) k = cong (false ∷_) (false-++ j k)

-- Independence does not see the order of two blocks.
indep-swap : {xs : Vec (State n) k} {ys : Vec (State n) j} → Indep (xs ++ ys) → Indep (ys ++ xs)
indep-swap {k = k} {j} {xs} {ys} ind cs z with split j cs
... | bs , as , refl =
  trans (cong₂ _++_ (proj₂ both) (proj₁ both)) (false-++ j k)
  where
  z′ : comb (xs ++ ys) (as ++ bs) ≈s zeros
  z′ i = trans (comb-++ xs ys as bs i)
    (trans (xor-comm (comb xs as i) (comb ys bs i)) (trans (sym (comb-++ ys xs bs as i)) (z i)))
  both = ++-false as bs (ind (as ++ bs) z′)

------------------------------------------------------------------------
-- The map of a list

private
  tab-⊕ : (s t : State k) → tabulate (s ⊕ t) ≡ tabulate s ⊕ᵥ tabulate t
  tab-⊕ {zero}  s t = refl
  tab-⊕ {suc k} s t = cong ((s zero xor t zero) ∷_) (tab-⊕ (λ i → s (suc i)) (λ i → t (suc i)))

  comb-false : (L : Vec (State n) k) → comb L (tabulate (λ _ → false)) ≈s zeros
  comb-false []      i = refl
  comb-false (x ∷ L) i = comb-false L i

comb-unit : (L : Vec (State n) k) (i : Fin k) → comb L (tabulate (unit i)) ≈s lookup L i
comb-unit (x ∷ L) zero    j = trans (cong (x j xor_) (comb-false L j)) (xor-identityʳ (x j))
comb-unit (x ∷ L) (suc i) j = comb-unit L i j

embL : (L : Vec (State m) k) → Indep L → Emb k m
embL L ind = record
  { f   = λ s → comb L (tabulate s)
  ; lin = record
      { add  = λ s t i → trans (cong (λ c → comb L c i) (tab-⊕ s t))
                           (comb-⊕ L (tabulate s) (tabulate t) i)
      ; resp = λ e i → cong (λ c → comb L c i) (VecP.tabulate-cong e) }
  ; inj = λ s z i → trans (sym (VecP.lookup∘tabulate s i))
                     (trans (cong (λ c → lookup c i) (ind (tabulate s) z))
                       (VecP.lookup-replicate i false)) }

embL-unit : (L : Vec (State m) k) (ind : Indep L) (i : Fin k) →
  Emb.f (embL L ind) (unit i) ≈s lookup L i
embL-unit L ind = comb-unit L

------------------------------------------------------------------------
-- Short independent lists

NZ : State n → Set
NZ x = ¬ (x ≈s zeros)

private
  b₁ : ∀ a b → a xor false ≡ b → b xor a ≡ false
  b₁ false false e = refl
  b₁ true  true  e = refl
  b₁ false true  ()
  b₁ true  false ()

  b₂ : ∀ a b c → a xor (b xor false) ≡ c → (c xor a) xor b ≡ false
  b₂ false false false e = refl
  b₂ false true  true  e = refl
  b₂ true  false true  e = refl
  b₂ true  true  false e = refl
  b₂ false false true  ()
  b₂ false true  false ()
  b₂ true  false false ()
  b₂ true  true  true  ()

indep₀ : Indep ([] {A = State n})
indep₀ [] z = refl

indep₁ : {x : State n} → NZ x → Indep (x ∷ [])
indep₁ nx = indep-extend indep₀ λ { ([] , p) → nx (λ i → sym (p i)) }

indep₂ : {x y : State n} → NZ x → NZ y → NZ (x ⊕ y) → Indep (x ∷ y ∷ [])
indep₂ {x = x} {y} nx ny nxy = indep-extend (indep₁ ny) out
  where
  out : ¬ InSpan (y ∷ []) x
  out ((false ∷ []) , p) = nx (λ i → sym (p i))
  out ((true ∷ [])  , p) = nxy (λ i → b₁ (y i) (x i) (p i))

indep₃ : {x y z : State n} → NZ x → NZ y → NZ z → NZ (x ⊕ y) → NZ (x ⊕ z) → NZ (y ⊕ z) →
  NZ ((x ⊕ y) ⊕ z) → Indep (x ∷ y ∷ z ∷ [])
indep₃ {x = x} {y} {z} nx ny nz nxy nxz nyz nxyz = indep-extend (indep₂ ny nz nyz) out
  where
  out : ¬ InSpan (y ∷ z ∷ []) x
  out ((false ∷ false ∷ []) , p) = nx (λ i → sym (p i))
  out ((true  ∷ false ∷ []) , p) = nxy (λ i → b₁ (y i) (x i) (p i))
  out ((false ∷ true  ∷ []) , p) = nxz (λ i → b₁ (z i) (x i) (p i))
  out ((true  ∷ true  ∷ []) , p) = nxyz (λ i → b₂ (y i) (z i) (x i) (p i))

-- Distinct states have a non-vanishing difference.
diff-nz : {s t : State n} → ¬ (s ≈s t) → NZ (s ⊕ t)
diff-nz {s = s} {t} ne z = ne λ i → xf (s i) (t i) (z i)
  where
  xf : ∀ a b → a xor b ≡ false → a ≡ b
  xf false false e = refl
  xf true  true  e = refl
  xf false true  ()
  xf true  false ()
