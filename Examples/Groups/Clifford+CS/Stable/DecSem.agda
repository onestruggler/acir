------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of the affine decoding at every width
--
-- An affine word of Affine.Circuits on 4 + m wires denotes the
-- permutation operator of its bit map read backwards (`aff-sem`: the
-- letters by Stable.AffSem, products composing the maps), and the
-- reversed word's map inverts the word's (`amapʷ-rev`).  So conjugating
-- a gate that denotes a two-level operator by an affine word moves its
-- two states by the word's bit map (`conj-sem`, through Five.Sem.TL's
-- tl-pull): the decoding d p q = α p q • G • (α p q)⁻¹ of a gadget with
-- block B on 0 and e₀ denotes the block B on the images of 0 and e₀
-- under α p q (`d-sem`).  With Stable.GadgetSem this is the decoding's
-- semantics, which Lemma 8.8 at every width needs (Stable.HyperSem).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)

module Examples.Groups.Clifford+CS.Stable.DecSem (m : ℕ) (c4 : Complete 4) where

open import Algebra.Bundles using (Monoid)
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (suc) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as NP
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; lookup)
import Data.Empty.Irrelevant as Irr
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control using (permOp)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Networks using (bring₁ ; bring₂)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (⟦•⟧ ; ⟦ε⟧ ; ∙-cong′)
open import Examples.Groups.Clifford+CS.Stable.NetSem using (perm-⊙)
open import Examples.Groups.Clifford+CS.Stable.AffSem using (X-letter ; CX-letter)
import Examples.Groups.Clifford+CS.Five.Sem.TL as TL
import Examples.Groups.Clifford+CS.Affine.Theory (₃₊ m) as A
import Examples.Groups.Clifford+CS.Affine.Alpha (₃₊ m) as Al
import Examples.Groups.Clifford+CS.Affine.Equivariance (₃₊ m) as E
import Examples.Groups.Clifford+CS.Affine.Circuits m c4 as C

open TL using (Blk ; tl ; tlOp)
open A using (Lt ; xL ; tL ; Wire)

private
  W : ℕ
  W = ₄₊ m

  St : Set
  St = Vec Bool W

  module R = SetoidR (Monoid.setoid (Scaled-monoid W))

------------------------------------------------------------------------
-- The reversed word inverts the bit map

private
  tmap-invol : ∀ (u v : Wire) → u ≢ v → ∀ p → E.tmap u v (E.tmap u v p) ≡ p
  tmap-invol u v uv p = go (lookup p u) Eq.refl
    where
    go : ∀ b → lookup p u ≡ b → E.tmap u v (if b then A.toggle p v else p) ≡ p
    go true e =
      Eq.trans (Eq.cong (λ c → if c then A.toggle (A.toggle p v) v else A.toggle p v)
                        (Eq.trans (A.lookup-toggle′ p v u uv) e))
               (Al.toggle-invol p v)
    go false e = Eq.cong (λ c → if c then A.toggle p v else p) e

  amap-invol : ∀ (a : Lt) p → Al.amap a (Al.amap a p) ≡ p
  amap-invol (xL v)     p = Al.toggle-invol p v
  amap-invol (tL u v r) p = tmap-invol u v (λ e → Irr.⊥-elim (r e)) p

amapʷ-rev : ∀ (w : Word Lt) (x : St) → Al.amapʷ (A.rev w) (Al.amapʷ w x) ≡ x
amapʷ-rev [ a ]ʷ  x = amap-invol a x
amapʷ-rev ε       x = Eq.refl
amapʷ-rev (u • v) x =
  Eq.trans (Eq.cong (Al.amapʷ (A.rev v)) (amapʷ-rev u (Al.amapʷ v x))) (amapʷ-rev v x)

amapʷ-rev′ : ∀ (w : Word Lt) (x : St) → Al.amapʷ w (Al.amapʷ (A.rev w) x) ≡ x
amapʷ-rev′ w x = Eq.subst (λ τ → Al.amapʷ τ (Al.amapʷ (A.rev w) x) ≡ x) (A.rev-rev w) (amapʷ-rev (A.rev w) x)

------------------------------------------------------------------------
-- Affine words

aff-sem : ∀ (w : Word Lt) → ⟦ C.⟪ w ⟫ʷ ⟧ ~ (0 , permOp (Al.amapʷ (A.rev w)))
aff-sem [ xL a ]ʷ     = X-letter (₃₊ m) (proj₁ (bring₁ a)) a (proj₂ (bring₁ a))
aff-sem [ tL u v r ]ʷ =
  CX-letter (₂₊ m) (proj₁ B) u v (proj₁ (proj₂ B)) (proj₂ (proj₂ B))
  where
  B = bring₂ v u (C.ne r)
aff-sem ε =
  ~-trans {s = ⟦ C.⟪ ε ⟫ʷ ⟧} {ε∙} {0 , permOp (Al.amapʷ (A.rev ε))} ⟦ε⟧
    (~-reflexive {l = 0} {0} Eq.refl (λ x y → Eq.refl))
aff-sem (u • v) = begin
  ⟦ C.⟪ u ⟫ʷ • C.⟪ v ⟫ʷ ⟧                     ≈⟨ ⟦•⟧ C.⟪ u ⟫ʷ C.⟪ v ⟫ʷ ⟩
  ⟦ C.⟪ u ⟫ʷ ⟧ ∙ ⟦ C.⟪ v ⟫ʷ ⟧                 ≈⟨ ∙-cong′ ⟦ C.⟪ u ⟫ʷ ⟧ (0 , permOp πu) ⟦ C.⟪ v ⟫ʷ ⟧ (0 , permOp πv)
                                                   (aff-sem u) (aff-sem v) ⟩
  (0 , permOp πu) ∙ (0 , permOp πv)           ≈⟨ ~-reflexive {l = 0} {0} Eq.refl (perm-⊙ πu πv) ⟩
  (0 , permOp (Al.amapʷ (A.rev (u • v))))     ∎
  where
  open R
  πu πv : St → St
  πu = Al.amapʷ (A.rev u)
  πv = Al.amapʷ (A.rev v)

------------------------------------------------------------------------
-- Conjugating a two-level operator

conj-sem : ∀ (w : Word Lt) (G : Circuit W) (B : Blk) (p q : St) → ⟦ G ⟧ ~ tl B p q →
           ⟦ C.⟪ w ⟫ʷ • G • C.⟪ A.rev w ⟫ʷ ⟧ ~ tl B (Al.amapʷ w p) (Al.amapʷ w q)
conj-sem w G B p q hG = begin
  ⟦ C.⟪ w ⟫ʷ • G • C.⟪ A.rev w ⟫ʷ ⟧
    ≈⟨ ⟦•⟧ C.⟪ w ⟫ʷ (G • C.⟪ A.rev w ⟫ʷ) ⟩
  ⟦ C.⟪ w ⟫ʷ ⟧ ∙ ⟦ G • C.⟪ A.rev w ⟫ʷ ⟧
    ≈⟨ ∙-cong′ ⟦ C.⟪ w ⟫ʷ ⟧ (0 , permOp f) ⟦ G • C.⟪ A.rev w ⟫ʷ ⟧ (tl B p q ∙ (0 , permOp g)) (aff-sem w)
         (begin
            ⟦ G • C.⟪ A.rev w ⟫ʷ ⟧             ≈⟨ ⟦•⟧ G C.⟪ A.rev w ⟫ʷ ⟩
            ⟦ G ⟧ ∙ ⟦ C.⟪ A.rev w ⟫ʷ ⟧         ≈⟨ ∙-cong′ ⟦ G ⟧ (tl B p q) ⟦ C.⟪ A.rev w ⟫ʷ ⟧ (0 , permOp g) hG
                                                    (~-trans {s = ⟦ C.⟪ A.rev w ⟫ʷ ⟧} {0 , permOp (Al.amapʷ (A.rev (A.rev w)))} {0 , permOp g}
                                                       (aff-sem (A.rev w))
                                                       (~-reflexive {l = 0} {0} Eq.refl
                                                          (λ x y → Eq.cong (λ τ → δb (Al.amapʷ τ x) y) (A.rev-rev w)))) ⟩
            tl B p q ∙ (0 , permOp g)          ∎) ⟩
  (0 , permOp f) ∙ (tl B p q ∙ (0 , permOp g))
    ≈⟨ ~-reflexive {l = 0 +ℕ (Blk.k B +ℕ 0)} {Blk.k B} (NP.+-identityʳ (Blk.k B)) op ⟩
  tl B (g p) (g q) ∎
  where
  open R
  f g : St → St
  f = Al.amapʷ (A.rev w)
  g = Al.amapʷ w
  -- δ moves across the bijection.
  δg : ∀ z y → δb (g z) y ≡ δb z (f y)
  δg z y =
    Eq.trans (δb-sym (g z) y)
      (Eq.trans (TL.Bij.δ-move g f (amapʷ-rev′ w) (amapʷ-rev w) y z) (δb-sym (f y) z))
  op : (permOp f ⊙ (tlOp B p q ⊙ permOp g)) ≐ tlOp B (g p) (g q)
  op x y =
    Eq.trans (Σ-δˡ (f x) (λ z → (tlOp B p q ⊙ permOp g) z y))
      (Eq.trans (Σ-cong {f = λ z → tlOp B p q (f x) z * δb (g z) y} {g = λ z → tlOp B p q (f x) z * δb z (f y)}
                        (λ z → Eq.cong (tlOp B p q (f x) z *_) (δg z y)))
        (Eq.trans (Σ-δʳ (f y) (λ z → tlOp B p q (f x) z))
                  (TL.Bij.tl-pull g f (amapʷ-rev′ w) (amapʷ-rev w) B p q x y)))

-- The decoding of a gadget with block B on 0 and e₀ denotes B on the
-- images of 0 and e₀ under the affine circuit.
d-sem : ∀ (G : Circuit W) (B : Blk) (o e : St) → ⟦ G ⟧ ~ tl B o e → ∀ (p q : St) →
        ⟦ C.⟪ Al.α p q ⟫ʷ • G • C.⟪ A.rev (Al.α p q) ⟫ʷ ⟧ ~ tl B (Al.amapʷ (Al.α p q) o) (Al.amapʷ (Al.α p q) e)
d-sem G B o e hG p q = conj-sem (Al.α p q) G B o e hG
