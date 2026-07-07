------------------------------------------------------------------------
-- Presentations of groups
--
-- Unique normal form for the loose (endofunction) semantics of Sₙ.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Loose.Uniqueness where

open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
import Data.Fin.Properties as FP
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Symmetric.Cosets
open import Examples.Groups.Symmetric.Loose.Semantics
open import Examples.Groups.Symmetric.Normalization
  using (nf-of ; NF ; inv-nf ; nf-cong ; inv-nf∘nf≈id)
open import Examples.Groups.Symmetric.Syntactics
open import Notations
import Normalization.Base as NFBase
open import Word.Base using (_•_)
open import Word.Properties using (wconcatmap-[f]ʷ)

private variable n : ℕ

------------------------------------------------------------------------
-- Encoding coset descriptors as Fin indices

private
  -- Depth of a coset descriptor: the number of σ• layers, as a Fin index.
  depth : ∀ {n} → C n → Fin (₁₊ n)
  depth ε      = fzero
  depth (σ• c) = fsuc (depth c)

  -- depth is injective, so it embeds C n into Fin (₁₊ n).
  depth-injective : ∀ {n} {r r' : C n} → depth r ≡ depth r' → r ≡ r'
  depth-injective {r = ε}    {r' = ε}     _  = Eq.refl
  depth-injective {r = ε}    {r' = σ• _}  ()
  depth-injective {r = σ• _} {r' = ε}     ()
  depth-injective {r = σ• c} {r' = σ• c'} eq =
    Eq.cong σ•_ (depth-injective (FP.suc-injective eq))

  -- Evaluating a coset representative at fzero recovers the depth of its
  -- descriptor.
  ⟦[]ᶜ⟧-zero : ∀ {n} (r : C n) → ⟦ [ r ]ᶜ ⟧ fzero ≡ depth r
  ⟦[]ᶜ⟧-zero ε      = Eq.refl
  ⟦[]ᶜ⟧-zero (σ• c) =
    Eq.trans (⟦↑⟧ ([ c ]ᶜ) (fsuc fzero))
             (Eq.cong fsuc (⟦[]ᶜ⟧-zero c))

  -- A coset representative is injective on fsuc-values, so its action can
  -- be cancelled there.
  ⟦[]ᶜ⟧-suc-injective : ∀ {n} (r : C n) {j₁ j₂ : Fin n}
    → ⟦ [ r ]ᶜ ⟧ (fsuc j₁) ≡ ⟦ [ r ]ᶜ ⟧ (fsuc j₂) → j₁ ≡ j₂
  ⟦[]ᶜ⟧-suc-injective ε {j₁} {j₂} eq with eq
  ... | Eq.refl = Eq.refl
  ⟦[]ᶜ⟧-suc-injective (σ• c) {fzero}    {fzero}    _   = Eq.refl
  ⟦[]ᶜ⟧-suc-injective (σ• c) {fzero}    {fsuc j₂'} eq
    with Eq.trans (Eq.sym (⟦↑⟧ ([ c ]ᶜ) fzero))
                  (Eq.trans eq (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₂'))))
  ... | ()
  ⟦[]ᶜ⟧-suc-injective (σ• c) {fsuc j₁'} {fzero}    eq
    with Eq.trans (Eq.trans (Eq.sym (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₁')))) eq)
                  (⟦↑⟧ ([ c ]ᶜ) fzero)
  ... | ()
  ⟦[]ᶜ⟧-suc-injective (σ• c) {fsuc j₁'} {fsuc j₂'} eq =
    Eq.cong fsuc (⟦[]ᶜ⟧-suc-injective c step)
    where
    step : ⟦ [ c ]ᶜ ⟧ (fsuc j₁') ≡ ⟦ [ c ]ᶜ ⟧ (fsuc j₂')
    step = FP.suc-injective
      (Eq.trans (Eq.sym (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₁'))))
      (Eq.trans eq      (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₂')))))

------------------------------------------------------------------------
-- Cancelling the coset factor of a normal form

private
  -- Equal denotations of inv-nf l ↑ • [ r ]ᶜ determine the coset
  -- component: evaluate both sides at fzero and apply depth-injective.
  coset-unique : ∀ n (l l' : NF (₁₊ n)) (r r' : C (₁₊ n))
    → (eq : ∀ k → ⟦ inv-nf {(₁₊ n)} l ↑ • [ r ]ᶜ ⟧ k ≡ ⟦ inv-nf {(₁₊ n)} l' ↑ • [ r' ]ᶜ ⟧ k)
    → r ≡ r'
  coset-unique n l l' r r' eq =
    depth-injective
      (Eq.trans (Eq.sym (⟦[]ᶜ⟧-zero r))
      (Eq.trans
        (Eq.trans
          (Eq.cong (⟦ [ r ]ᶜ ⟧) (Eq.sym (⟦↑⟧ (inv-nf {(₁₊ n)} l) fzero)))
          (Eq.trans (eq fzero)
          (Eq.cong (⟦ [ r' ]ᶜ ⟧) (⟦↑⟧ (inv-nf {(₁₊ n)} l') fzero))))
        (⟦[]ᶜ⟧-zero r')))

  -- Once r ≡ r' is known, the coset factor cancels, leaving pointwise
  -- equality of the lifted inv-nf prefixes.
  prefix-unique : ∀ n (l l' : NF (₁₊ n)) (r r' : C (₁₊ n))
    → r ≡ r'
    → (eq : ∀ k → ⟦ inv-nf {(₁₊ n)} l ↑ • [ r ]ᶜ ⟧ k ≡ ⟦ inv-nf {(₁₊ n)} l' ↑ • [ r' ]ᶜ ⟧ k)
    → ∀ j → ⟦ inv-nf {(₁₊ n)} l ⟧ j ≡ ⟦ inv-nf {(₁₊ n)} l' ⟧ j
  prefix-unique n l l' r r' r≡r' eq j =
    ⟦[]ᶜ⟧-suc-injective r
      (Eq.trans
        (Eq.cong (⟦ [ r ]ᶜ ⟧) (Eq.sym (⟦↑⟧ (inv-nf {(₁₊ n)} l) (fsuc j))))
        (Eq.trans
          (Eq.subst
            (λ s → ⟦ [ r ]ᶜ ⟧ (⟦ inv-nf {(₁₊ n)} l ↑ ⟧ (fsuc j))
                 ≡ ⟦ [ s ]ᶜ ⟧ (⟦ inv-nf {(₁₊ n)} l' ↑ ⟧ (fsuc j)))
            (Eq.sym r≡r')
            (eq (fsuc j)))
          (Eq.cong (⟦ [ r ]ᶜ ⟧) (⟦↑⟧ (inv-nf {(₁₊ n)} l') (fsuc j)))))

------------------------------------------------------------------------
-- Semantic injectivity of inv-nf: pointwise-equal denotations imply equal NFs

private
  -- By induction on the coset tower: the cases n = 0, 1 are trivial since
  -- NF is ⊤ there; at ₂₊ n' the normal form splits as prefix × coset, the
  -- coset components agree by coset-unique, and the prefixes agree by the
  -- induction hypothesis via prefix-unique.
  ⟦inv-nf⟧-injective : ∀ n {u v : NF n}
    → (∀ k → ⟦ inv-nf {n} u ⟧ k ≡ ⟦ inv-nf {n} v ⟧ k)
    → u ≡ v
  ⟦inv-nf⟧-injective 0       {tt}     {tt}      _   = Eq.refl
  ⟦inv-nf⟧-injective 1       {tt}     {tt}      _   = Eq.refl
  ⟦inv-nf⟧-injective (₂₊ n') {l , r} {l' , r'} eq  =
    ≡×≡⇒≡ (⟦inv-nf⟧-injective (₁₊ n') (prefix-unique n' l l' r r' r≡r' eq↑) , r≡r')
    where
    -- inv-nf {₂₊ n'} (x , s) is (f *)(inv-nf x) • [ s ]ᶜ; bridge to the ↑ form
    to↑ : ∀ (x : NF (₁₊ n')) (s : C (₁₊ n')) k
        → ⟦ inv-nf {(₂₊ n')} (x , s) ⟧ k ≡ ⟦ inv-nf {(₁₊ n')} x ↑ • [ s ]ᶜ ⟧ k
    to↑ x s k = Eq.cong (λ z → ⟦ z • [ s ]ᶜ ⟧ k) (wconcatmap-[f]ʷ (inv-nf {(₁₊ n')} x))
    eq↑ : ∀ k → ⟦ inv-nf {(₁₊ n')} l ↑ • [ r ]ᶜ ⟧ k
              ≡ ⟦ inv-nf {(₁₊ n')} l' ↑ • [ r' ]ᶜ ⟧ k
    eq↑ k = Eq.trans (Eq.sym (to↑ l r k)) (Eq.trans (eq k) (to↑ l' r' k))
    r≡r' = coset-unique n' l l' r r' eq↑

------------------------------------------------------------------------
-- Unique normal form for the loose semantics

-- The normal form of Examples.Groups.Symmetric.Normalization is unique for
-- the endofunction semantics: the NormalForm witness is packaged together
-- with uniqueness, given by ⟦inv-nf⟧-injective.
unique-nf : ∀ n →
  NFBase.UniqueNormalForm (_VRel,_===_ n) (Endo-setoid n) (⟦_⟧ {n})
unique-nf n = record
  { normalForm = record
      { NF = NF n ; nf = nf-of ; nf-cong = nf-cong
      ; inv-nf = inv-nf ; inv-nf∘nf=id = inv-nf∘nf≈id n }
  ; unique = ⟦inv-nf⟧-injective n
  }
