------------------------------------------------------------------------
-- Presentations of groups
--
-- The affine letters denote the permutations of their bit maps
--
-- A network's bit map moves the bit at i to the position its
-- permutation sends i to (`lookup-nb`), and the reversed network's map
-- reads it back (`lookup-nb⁻`).  So X placed by a network that brings
-- wire a to wire 0 toggles the bit a (`X-letter`), and CX₁₀ placed by
-- one that brings v to wire 0 and u to wire 1 adds the bit u to the bit
-- v (`CX-letter`): the letters of Affine.Circuits denote the
-- permutation operators of Affine.Theory's `toggle` and Affine.
-- Equivariance's `tmap`, the bit maps the decoding's equivariance is
-- stated with.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.AffSem where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_ ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Nat using (ℕ ; suc)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control using (permOp)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; X ; CX₁₀)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.PermCalc using (perm ; revS ; perm-inv ; perm-inj)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl)
open import Examples.Groups.Clifford+CS.Networks using (perm-↑0 ; perm-↑s)
open import Examples.Groups.Clifford+CS.Stable.NetSem using (nb ; nbg)
open import Examples.Groups.Clifford+CS.Stable.PlaceSem using (nb-revS ; nb-revS′ ; pl-sem ; fl0 ; cx0 ; X-sem ; CX-sem)
import Examples.Groups.Clifford+CS.Five.Sem.TL as TL
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Equivariance as Equivariance

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Bits under a network

lookup-nb : ∀ (σ : Word (S.Gen n)) (x : Bits n) (i : Fin n) → lookup (nb σ x) (perm σ ⟨$⟩ʳ i) ≡ lookup x i
lookup-nb [ g ]ʷ  x i = gen g x i
  where
  gen : ∀ {n} (g : S.Gen n) (x : Bits n) (i : Fin n) → lookup (nbg g x) (perm [ g ]ʷ ⟨$⟩ʳ i) ≡ lookup x i
  gen (S.gate₀ ())
  gen (S.gate₁ ())
  gen (S.gate₂ S.σ-gate) (a ∷ b ∷ x) 0F          = Eq.refl
  gen (S.gate₂ S.σ-gate) (a ∷ b ∷ x) (sF 0F)     = Eq.refl
  gen (S.gate₂ S.σ-gate) (a ∷ b ∷ x) (sF (sF i)) = Eq.refl
  gen (g S.↥) (a ∷ x) 0F     = Eq.cong (lookup (a ∷ nbg g x)) (perm-↑0 [ g ]ʷ)
  gen (g S.↥) (a ∷ x) (sF i) = Eq.trans (Eq.cong (lookup (a ∷ nbg g x)) (perm-↑s [ g ]ʷ i)) (gen g x i)
lookup-nb ε       x i = Eq.refl
lookup-nb (u • v) x i = Eq.trans (lookup-nb v (nb u x) (perm u ⟨$⟩ʳ i)) (lookup-nb u x i)

lookup-nb⁻ : ∀ (σ : Word (S.Gen n)) (z : Bits n) (i : Fin n) → lookup (nb (revS σ) z) i ≡ lookup z (perm σ ⟨$⟩ʳ i)
lookup-nb⁻ σ z i =
  Eq.subst (λ j → lookup (nb (revS σ) z) j ≡ lookup z (perm σ ⟨$⟩ʳ i)) (perm-inv σ i)
           (lookup-nb (revS σ) z (perm σ ⟨$⟩ʳ i))

private
  vec-ext : ∀ {n} (x y : Vec Bool n) → (∀ i → lookup x i ≡ lookup y i) → x ≡ y
  vec-ext []      []      h = Eq.refl
  vec-ext (a ∷ x) (b ∷ y) h = Eq.cong₂ _∷_ (h 0F) (vec-ext x y (λ i → h (sF i)))

  -- Conjugating a bit map by the network.
  back : ∀ (σ : Word (S.Gen n)) (f : Bits n → Bits n) (h : Bits n → Bits n) →
         (∀ x → nb (revS σ) (f (nb σ x)) ≡ h x) → ∀ x y → δb (f (nb σ x)) (nb σ y) ≡ permOp h x y
  back σ f h e x y =
    Eq.trans (TL.Bij.δ-move (nb σ) (nb (revS σ)) (nb-revS′ σ) (nb-revS σ) (f (nb σ x)) y)
             (Eq.cong (λ z → δb z y) (e x))

  fl0-at : ∀ (w : Bits (₁₊ n)) (j : Fin (₁₊ n)) → j ≢ 0F → lookup (fl0 w) j ≡ lookup w j
  fl0-at (c ∷ w) 0F     ne = ⊥-elim (ne Eq.refl)
  fl0-at (c ∷ w) (sF j) ne = Eq.refl

  cx0-at : ∀ (w : Bits (₂₊ n)) (j : Fin (₂₊ n)) → j ≢ 0F → lookup (cx0 w) j ≡ lookup w j
  cx0-at (c ∷ d ∷ w) 0F     ne = ⊥-elim (ne Eq.refl)
  cx0-at (c ∷ d ∷ w) (sF j) ne = Eq.refl

  cx0-0 : ∀ (w : Bits (₂₊ n)) → lookup (cx0 w) 0F ≡ (lookup w 0F xor lookup w (sF 0F))
  cx0-0 (c ∷ d ∷ w) = Eq.refl

------------------------------------------------------------------------
-- The letters

module _ (k : ℕ) where
  private
    module T = Theory k
    module E = Equivariance k
    W : ℕ
    W = ₁₊ k

  -- X on the wire a network brings to wire 0 toggles that bit.
  X-letter : ∀ (b : Word (S.Gen W)) (a : Fin W) → perm b ⟨$⟩ʳ a ≡ 0F →
             ⟦ pl b X ⟧ ~ (0 , permOp (λ x → T.toggle x a))
  X-letter b a h =
    ~-trans {s = ⟦ pl b X ⟧} {0 , λ x y → permOp fl0 (nb b x) (nb b y)} {0 , permOp (λ x → T.toggle x a)}
      (pl-sem b X 0 (permOp fl0) (X-sem k))
      (~-reflexive {l = 0} {0} Eq.refl (back b fl0 (λ x → T.toggle x a) key))
    where
    key : ∀ x → nb (revS b) (fl0 (nb b x)) ≡ T.toggle x a
    key x = vec-ext _ _ λ i → Eq.trans (lookup-nb⁻ b (fl0 (nb b x)) i) (at i (i ≟ᶠ a))
      where
      at : ∀ i → Relation.Nullary.Dec (i ≡ a) → lookup (fl0 (nb b x)) (perm b ⟨$⟩ʳ i) ≡ lookup (T.toggle x a) i
      at i (yes Eq.refl) =
        Eq.trans (Eq.cong (λ j → lookup (fl0 (nb b x)) j) h)
          (Eq.trans (fl0-0 (nb b x))
            (Eq.trans (Eq.cong not (Eq.trans (Eq.cong (lookup (nb b x)) (Eq.sym h)) (lookup-nb b x a)))
                      (Eq.sym (T.lookup-toggle x a))))
        where
        fl0-0 : ∀ (w : Bits W) → lookup (fl0 w) 0F ≡ not (lookup w 0F)
        fl0-0 (c ∷ w) = Eq.refl
      at i (no ne) =
        Eq.trans (fl0-at (nb b x) (perm b ⟨$⟩ʳ i) (λ e → ne (perm-inj b (Eq.trans e (Eq.sym h)))))
          (Eq.trans (lookup-nb b x i) (Eq.sym (T.lookup-toggle′ x a i ne)))

module _ (k : ℕ) where
  private
    module T = Theory (suc k)
    module E = Equivariance (suc k)
    W : ℕ
    W = ₂₊ k

  -- CX₁₀ on the wires a network brings to wires 0 and 1 adds the bit u
  -- to the bit v.
  CX-letter : ∀ (b : Word (S.Gen W)) (u v : Fin W) → perm b ⟨$⟩ʳ v ≡ 0F → perm b ⟨$⟩ʳ u ≡ sF 0F →
              ⟦ pl b CX₁₀ ⟧ ~ (0 , permOp (E.tmap u v))
  CX-letter b u v hv hu =
    ~-trans {s = ⟦ pl b CX₁₀ ⟧} {0 , λ x y → permOp cx0 (nb b x) (nb b y)} {0 , permOp (E.tmap u v)}
      (pl-sem b CX₁₀ 0 (permOp cx0) (CX-sem k))
      (~-reflexive {l = 0} {0} Eq.refl (back b cx0 (E.tmap u v) key))
    where
    key : ∀ x → nb (revS b) (cx0 (nb b x)) ≡ E.tmap u v x
    key x = vec-ext _ _ λ i → Eq.trans (lookup-nb⁻ b (cx0 (nb b x)) i) (at i (i ≟ᶠ v))
      where
      xv xu : Bool
      xv = lookup x v
      xu = lookup x u

      tm-v : lookup (E.tmap u v x) v ≡ (xv xor xu)
      tm-v with lookup x u
      ... | true  = Eq.trans (T.lookup-toggle x v) (xor-t xv)
        where
        xor-t : ∀ c → not c ≡ (c xor true)
        xor-t true  = Eq.refl
        xor-t false = Eq.refl
      ... | false = xor-f xv
        where
        xor-f : ∀ c → c ≡ (c xor false)
        xor-f true  = Eq.refl
        xor-f false = Eq.refl

      tm-o : ∀ i → i ≢ v → lookup (E.tmap u v x) i ≡ lookup x i
      tm-o i ne with lookup x u
      ... | true  = T.lookup-toggle′ x v i ne
      ... | false = Eq.refl

      at : ∀ i → Relation.Nullary.Dec (i ≡ v) → lookup (cx0 (nb b x)) (perm b ⟨$⟩ʳ i) ≡ lookup (E.tmap u v x) i
      at i (yes Eq.refl) =
        Eq.trans (Eq.cong (λ j → lookup (cx0 (nb b x)) j) hv)
          (Eq.trans (cx0-0 (nb b x))
            (Eq.trans (Eq.cong₂ _xor_ (Eq.trans (Eq.cong (lookup (nb b x)) (Eq.sym hv)) (lookup-nb b x v))
                                      (Eq.trans (Eq.cong (lookup (nb b x)) (Eq.sym hu)) (lookup-nb b x u)))
                      (Eq.sym tm-v)))
      at i (no ne) =
        Eq.trans (cx0-at (nb b x) (perm b ⟨$⟩ʳ i) (λ e → ne (perm-inj b (Eq.trans e (Eq.sym hv)))))
          (Eq.trans (lookup-nb b x i) (Eq.sym (tm-o i ne)))
