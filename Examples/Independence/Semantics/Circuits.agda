------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of PROP circuits, from the values of the gates
--
-- A valuation gives each gate its scaled matrix on its own wires; a
-- gate on the bottom wires of a wider circuit is that matrix tensored
-- with the identity (embs), a shifted gate is the identity tensored
-- with it (↑s), and a circuit is the product of its gates in diagram
-- order.  For any group of phases (Scaled.Phases):
--
-- * an axiom checked on its own wires holds on the bottom wires of
--   every wider circuit (⟦↓⟧), and shifting commutes with reading
--   (⟦↑⟧), so cong↑ is sound;
-- * the comm rules and ω↑=ω are the tensor calculus, so they hold for
--   every valuation;
-- * the symmetry rules are owed for the swap and each gate, on two,
--   three or four wires.
--
-- Theory turns this into soundness of a fragment: given its axioms on
-- their own wires, every derivable equation holds, at every width.
-- Separate is Lemma 25 for the same semantics: given the axioms of
-- Keep ρ b, it separates ρ (Examples.Independence.Model).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Integer.Base using (ℤ)
open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Independence.Semantics.Quartic as Quartic
import Examples.Independence.Semantics.Scaled as Scaled
import Examples.Independence.Prop as Prop

module Examples.Independence.Semantics.Circuits
  (d : ℕ) (p q : ℤ)
  (r : Quartic.Q p q)
  (r-cancel : ∀ {a b} → Quartic._*_ p q r a ≡ Quartic._*_ p q r b → a ≡ b)
  (N-1 : ℕ)
  (x^N : Quartic._^_ p q (Quartic.x p q) (suc N-1) ≡ Quartic.1q p q)
  {Gate : ℕ → Set}
  (val : ∀ {k} → Prop.PGate Gate k → Scaled.Sc d p q r r-cancel N-1 x^N k)
  where

open import Data.Nat.Base using (zero ; _≤_) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
import Data.Nat.Properties as ℕP
open import Algebra.Bundles using (Monoid)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Relation.Nullary.Negation using (¬_)

open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB

open import Examples.Independence.Prop Gate
open import Examples.Independence.Semantics.Scaled d p q r r-cancel N-1 x^N
import Examples.Independence.Model Gate as Model

private
  variable
    k n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- Reading circuits

⟦_⟧₀ : Gen n → Sc n
⟦ gate₀ g ⟧₀ = proj₁ (val g) , scalM (entries (proj₂ (val g)))
⟦ gate₁ g ⟧₀ = embs (val g)
⟦ gate₂ g ⟧₀ = embs (val g)
⟦ gate₃ g ⟧₀ = embs (val g)
⟦ g ↥ ⟧₀     = ↑s ⟦ g ⟧₀

⟦_⟧ : Circuit n → Sc n
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧₀
⟦ ε ⟧      = εs
⟦ w • v ⟧  = ⟦ w ⟧ ∙ ⟦ v ⟧

------------------------------------------------------------------------
-- The laws, for any group of phases

module Laws
  (P : ℕ → Set) (P0 : P 0)
  (P+ : ∀ {k l} → P k → P l → P (k +ℕ l))
  (P⁻ : ∀ {k} → P k → P (N-1 *ℕ k))
  where

  open Phases P P0 P+ P⁻ public
  open Decide P P0 P+ P⁻ public

  private
    ≈-trans' : {s₁ s₂ s₃ : Sc n} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
    ≈-trans' {s₁ = s₁} {s₂} {s₃} = ≈-trans {s₁ = s₁} {s₂} {s₃}

    ≈-sym' : {s s' : Sc n} → s ≈ s' → s' ≈ s
    ≈-sym' {s = s} {s'} = ≈-sym {s = s} {s'}

  ----------------------------------------------------------------------
  -- Localisation

  ⟦↧⟧₀ : (g : Gen k) (n : ℕ) → ⟦ g ↧ᵏ n ⟧₀ ≈ embs {k} {n} ⟦ g ⟧₀
  ⟦↧⟧₀ {k} (gate₀ g) n =
    ≐→≈ {s = ⟦ gate₀ {k +ℕ n} g ⟧₀} {embs {k} {n} ⟦ gate₀ g ⟧₀} refl
      (≐-trans (ix-scalM {k +ℕ n} c)
      (≐-trans (scal-emb {k} {n} c)
      (≐-trans (emb-cong {k} {n} (≐-sym (ix-scalM {k} c)))
               (≐-sym (ix-emb {k} {n} (scalM c))))))
    where c = entries (proj₂ (val g))
  ⟦↧⟧₀ {suc k} (gate₁ g) n =
    ≐→≈ {s = ⟦ gate₁ {k +ℕ n} g ⟧₀} {embs {suc k} {n} ⟦ gate₁ g ⟧₀} refl
      (≐-trans (ix-emb {1} {k +ℕ n} M)
      (≐-trans (emb-pad₁ {k} {n} (ix M))
      (≐-trans (emb-cong {suc k} {n} (≐-sym (ix-emb {1} {k} M)))
               (≐-sym (ix-emb {suc k} {n} (tenM M (idM {k})))))))
    where M = proj₂ (val g)
  ⟦↧⟧₀ {suc (suc k)} (gate₂ g) n =
    ≐→≈ {s = ⟦ gate₂ {k +ℕ n} g ⟧₀} {embs {suc (suc k)} {n} ⟦ gate₂ g ⟧₀} refl
      (≐-trans (ix-emb {2} {k +ℕ n} M)
      (≐-trans (emb-pad₂ {k} {n} (ix M))
      (≐-trans (emb-cong {suc (suc k)} {n} (≐-sym (ix-emb {2} {k} M)))
               (≐-sym (ix-emb {suc (suc k)} {n} (tenM M (idM {k})))))))
    where M = proj₂ (val g)
  ⟦↧⟧₀ {suc (suc (suc k))} (gate₃ g) n =
    ≐→≈ {s = ⟦ gate₃ {k +ℕ n} g ⟧₀} {embs {suc (suc (suc k))} {n} ⟦ gate₃ g ⟧₀} refl
      (≐-trans (ix-emb {3} {k +ℕ n} M)
      (≐-trans (emb-pad₃ {k} {n} (ix M))
      (≐-trans (emb-cong {suc (suc (suc k))} {n} (≐-sym (ix-emb {3} {k} M)))
               (≐-sym (ix-emb {suc (suc (suc k))} {n} (tenM M (idM {k})))))))
    where M = proj₂ (val g)
  ⟦↧⟧₀ {suc k} (g ↥) n =
    ≈-trans' {s₁ = ↑s ⟦ g ↧ᵏ n ⟧₀} {↑s (embs {k} {n} ⟦ g ⟧₀)} {embs {suc k} {n} (↑s ⟦ g ⟧₀)}
      (↑s-cong {s = ⟦ g ↧ᵏ n ⟧₀} {embs {k} {n} ⟦ g ⟧₀} (⟦↧⟧₀ g n))
      (≐→≈ {s = ↑s (embs {k} {n} ⟦ g ⟧₀)} {embs {suc k} {n} (↑s ⟦ g ⟧₀)} refl
        (≐-trans (ix-up (tenM G (idM {n})))
        (≐-trans (up-cong (ix-emb {k} {n} G))
        (≐-trans (up-emb {k} {n} (ix G))
        (≐-trans (emb-cong {suc k} {n} (≐-sym (ix-up G)))
                 (≐-sym (ix-emb {suc k} {n} (tenM (idM {1}) G))))))))
    where G = proj₂ ⟦ g ⟧₀

  ⟦↓⟧ : (w : Circuit k) (n : ℕ) → ⟦ w ↓ᵏ n ⟧ ≈ embs {k} {n} ⟦ w ⟧
  ⟦↓⟧ [ g ]ʷ  n = ⟦↧⟧₀ g n
  ⟦↓⟧ {k} ε   n = ≈-sym' {s = embs {k} {n} εs} {εs} (embs-ε {k} {n})
  ⟦↓⟧ {k} (w • v) n =
    ≈-trans' {s₁ = ⟦ w ↓ᵏ n ⟧ ∙ ⟦ v ↓ᵏ n ⟧} {embs {k} {n} ⟦ w ⟧ ∙ embs ⟦ v ⟧}
             {embs {k} {n} (⟦ w ⟧ ∙ ⟦ v ⟧)}
      (∙-cong {s₁ = ⟦ w ↓ᵏ n ⟧} {embs {k} {n} ⟦ w ⟧} {⟦ v ↓ᵏ n ⟧} {embs {k} {n} ⟦ v ⟧}
              (⟦↓⟧ w n) (⟦↓⟧ v n))
      (≈-sym' {s = embs {k} {n} (⟦ w ⟧ ∙ ⟦ v ⟧)} {embs {k} {n} ⟦ w ⟧ ∙ embs ⟦ v ⟧}
              (embs-∙ {k} {n} ⟦ w ⟧ ⟦ v ⟧))

  -- The same, for the circuit spelled at the wider width: the two are
  -- compared as words, which is cheap, rather than as values.
  ⟦↓≡⟧ : (w : Circuit k) {n : ℕ} {w' : Circuit (k +ℕ n)} → w ↓ᵏ n ≡ w' →
         ⟦ w' ⟧ ≈ embs {k} {n} ⟦ w ⟧
  ⟦↓≡⟧ w {n} refl = ⟦↓⟧ w n

  ⟦↑⟧ : (w : Circuit n) → ⟦ w ↑ ⟧ ≈ ↑s ⟦ w ⟧
  ⟦↑⟧ [ g ]ʷ  = ≈-refl {s = ↑s ⟦ g ⟧₀}
  ⟦↑⟧ {n} ε   = ≈-sym' {s = ↑s (εs {n})} {εs} (↑s-ε {n})
  ⟦↑⟧ (w • v) =
    ≈-trans' {s₁ = ⟦ w ↑ ⟧ ∙ ⟦ v ↑ ⟧} {↑s ⟦ w ⟧ ∙ ↑s ⟦ v ⟧} {↑s (⟦ w ⟧ ∙ ⟦ v ⟧)}
      (∙-cong {s₁ = ⟦ w ↑ ⟧} {↑s ⟦ w ⟧} {⟦ v ↑ ⟧} {↑s ⟦ v ⟧} (⟦↑⟧ w) (⟦↑⟧ v))
      (≈-sym' {s = ↑s (⟦ w ⟧ ∙ ⟦ v ⟧)} {↑s ⟦ w ⟧ ∙ ↑s ⟦ v ⟧} (↑s-∙ ⟦ w ⟧ ⟦ v ⟧))

  ----------------------------------------------------------------------
  -- The structural rules of Circuit.Base

  cong↑-sound : ⟦ w ⟧ ≈ ⟦ v ⟧ → ⟦ w ↑ ⟧ ≈ ⟦ v ↑ ⟧
  cong↑-sound {w = w} {v} e =
    ≈-trans' {s₁ = ⟦ w ↑ ⟧} {↑s ⟦ w ⟧} {⟦ v ↑ ⟧} (⟦↑⟧ w)
      (≈-trans' {s₁ = ↑s ⟦ w ⟧} {↑s ⟦ v ⟧} {⟦ v ↑ ⟧}
        (↑s-cong {s = ⟦ w ⟧} {⟦ v ⟧} e)
        (≈-sym' {s = ⟦ v ↑ ⟧} {↑s ⟦ v ⟧} (⟦↑⟧ v)))

  comm₁-sound : (h : PGate 1) (g : Gen n) →
                ⟦ [ g ↥ ]ʷ • [ gate₁ h ]ʷ ⟧ ≈ ⟦ [ gate₁ h ]ʷ • [ g ↥ ]ʷ ⟧
  comm₁-sound {n} h g =
    ≐→≈ {s = ↑s ⟦ g ⟧₀ ∙ embs (val h)} {embs (val h) ∙ ↑s ⟦ g ⟧₀}
        (ℕP.+-comm (proj₁ ⟦ g ⟧₀) (proj₁ (val h)))
      (≐-trans (ix-mul E U)
      (≐-trans (⊙-cong (ix-emb {1} {n} V) (ix-up G))
      (≐-trans (emb-up-comm {1} {n} (ix V) (ix G))
      (≐-trans (⊙-cong (≐-sym (ix-up G)) (≐-sym (ix-emb {1} {n} V)))
               (≐-sym (ix-mul U E))))))
    where
    V = proj₂ (val h)
    G = proj₂ ⟦ g ⟧₀
    E = tenM V (idM {n})
    U = tenM (idM {1}) G

  comm₂-sound : (h : PGate 2) (g : Gen n) →
                ⟦ [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ ⟧ ≈ ⟦ [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ ⟧
  comm₂-sound {n} h g =
    ≐→≈ {s = ↑s (↑s ⟦ g ⟧₀) ∙ embs (val h)} {embs (val h) ∙ ↑s (↑s ⟦ g ⟧₀)}
        (ℕP.+-comm (proj₁ ⟦ g ⟧₀) (proj₁ (val h)))
      (≐-trans (ix-mul E U)
      (≐-trans (⊙-cong (ix-emb {2} {n} V) UU)
      (≐-trans (emb-up-comm {2} {n} (ix V) (ix G))
      (≐-trans (⊙-cong (≐-sym UU) (≐-sym (ix-emb {2} {n} V)))
               (≐-sym (ix-mul U E))))))
    where
    V = proj₂ (val h)
    G = proj₂ ⟦ g ⟧₀
    E = tenM V (idM {n})
    U = tenM (idM {1}) (tenM (idM {1}) G)
    UU : ix U ≐ upk 2 (ix G)
    UU = ≐-trans (ix-up (tenM (idM {1}) G))
           (≐-trans (up-cong (ix-up G)) (up-up (ix G)))

  comm₃-sound : (h : PGate 3) (g : Gen n) →
                ⟦ [ g ↥ ↥ ↥ ]ʷ • [ gate₃ h ]ʷ ⟧ ≈ ⟦ [ gate₃ h ]ʷ • [ g ↥ ↥ ↥ ]ʷ ⟧
  comm₃-sound {n} h g =
    ≐→≈ {s = ↑s (↑s (↑s ⟦ g ⟧₀)) ∙ embs (val h)} {embs (val h) ∙ ↑s (↑s (↑s ⟦ g ⟧₀))}
        (ℕP.+-comm (proj₁ ⟦ g ⟧₀) (proj₁ (val h)))
      (≐-trans (ix-mul E U)
      (≐-trans (⊙-cong (ix-emb {3} {n} V) UUU)
      (≐-trans (emb-up-comm {3} {n} (ix V) (ix G))
      (≐-trans (⊙-cong (≐-sym UUU) (≐-sym (ix-emb {3} {n} V)))
               (≐-sym (ix-mul U E))))))
    where
    V = proj₂ (val h)
    G = proj₂ ⟦ g ⟧₀
    E = tenM V (idM {n})
    U₂ = tenM (idM {1}) (tenM (idM {1}) G)
    U = tenM (idM {1}) U₂
    UU : ix U₂ ≐ upk 2 (ix G)
    UU = ≐-trans (ix-up (tenM (idM {1}) G))
           (≐-trans (up-cong (ix-up G)) (up-up (ix G)))
    UUU : ix U ≐ upk 3 (ix G)
    UUU = ≐-trans (ix-up U₂) (≐-trans (up-cong UU) (up-upk 2 (ix G)))

  ω↑=ω-sound : (h : PGate 0) → ⟦ [ gate₀ {n} h ]ʷ ↑ ⟧ ≈ ⟦ [ gate₀ h ]ʷ ⟧
  ω↑=ω-sound {n} h =
    ≐→≈ {s = ↑s ⟦ gate₀ {n} h ⟧₀} {⟦ gate₀ {suc n} h ⟧₀} refl
      (≐-trans (ix-up (scalM c))
      (≐-trans (up-cong (ix-scalM {n} c))
      (≐-trans (up-scal c) (≐-sym (ix-scalM {suc n} c)))))
    where c = entries (proj₂ (val h))

  ----------------------------------------------------------------------
  -- The symmetry rules, from their instances on two and three wires

  module Symmetry
    (σσ-ok  : ⟦ σ {0} • σ {0} ⟧ ≈ ⟦ ε {X = Gen 2} ⟧)
    (nat₁-ok : (h : Gate 1) →
               ⟦ [ gate₁ {1} ⌈ h ⌉ ]ʷ • σ {0} ⟧ ≈ ⟦ σ {0} • [ gate₁ {0} ⌈ h ⌉ ]ʷ ↑ ⟧)
    (nat₂-ok : (h : PGate 2) →
               ⟦ [ gate₂ {1} h ]ʷ • σ[_] {0} 2 ⟧ ≈
               ⟦ σ[_] {0} 2 • [ gate₂ {0} h ]ʷ ↑ ⟧)
    (nat₃-ok : (h : Gate 3) →
               ⟦ [ gate₃ {1} ⌈ h ⌉ ]ʷ • σ[_] {0} 3 ⟧ ≈
               ⟦ σ[_] {0} 3 • [ gate₃ {0} ⌈ h ⌉ ]ʷ ↑ ⟧)
    where

    private
      -- An equation on k wires, read on the bottom wires of k + n.
      lift : (l r : Circuit k) {n : ℕ} {w v : Circuit (k +ℕ n)} →
             l ↓ᵏ n ≡ w → r ↓ᵏ n ≡ v → ⟦ l ⟧ ≈ ⟦ r ⟧ → ⟦ w ⟧ ≈ ⟦ v ⟧
      lift {k} l r {n} {w} {v} el er e =
        ≈-trans' {s₁ = ⟦ w ⟧} {embs {k} {n} ⟦ l ⟧} {⟦ v ⟧} (⟦↓≡⟧ l el)
          (≈-trans' {s₁ = embs {k} {n} ⟦ l ⟧} {embs {k} {n} ⟦ r ⟧} {⟦ v ⟧}
            (embs-cong {k} {n} {s = ⟦ l ⟧} {⟦ r ⟧} e)
            (≈-sym' {s = ⟦ v ⟧} {embs {k} {n} ⟦ r ⟧} (⟦↓≡⟧ r er)))

    sym-sound : n Sym, w === v → ⟦ w ⟧ ≈ ⟦ v ⟧
    sym-sound σ-inv          = lift (σ • σ) ε refl refl σσ-ok
    sym-sound (σ-nat₁ ⌈ h ⌉) = lift ([ gate₁ ⌈ h ⌉ ]ʷ • σ) (σ • [ gate₁ ⌈ h ⌉ ]ʷ ↑)
                                    refl refl (nat₁-ok h)
    sym-sound (σ-nat₂ h)     = lift ([ gate₂ h ]ʷ • σ[ 2 ]) (σ[ 2 ] • [ gate₂ h ]ʷ ↑)
                                    refl refl (nat₂-ok h)
    sym-sound (σ-nat₃ ⌈ h ⌉) = lift ([ gate₃ ⌈ h ⌉ ]ʷ • σ[ 3 ]) (σ[ 3 ] • [ gate₃ ⌈ h ⌉ ]ʷ ↑)
                                    refl refl (nat₃-ok h)

    --------------------------------------------------------------------
    -- Soundness of a fragment

    module Theory
      {Rule : Set} (arity : Rule → ℕ)
      (lhs rhs : (r : Rule) → Circuit (arity r))
      (ax-ok : ∀ r → ⟦ lhs r ⟧ ≈ ⟦ rhs r ⟧)
      where

      open Fragment arity lhs rhs

      vrel-sound : n VRel, w === v → ⟦ w ⟧ ≈ ⟦ v ⟧
      vrel-sound (srel (σrel s))         = sym-sound s
      vrel-sound (srel (srel (ax r k))) = lift (lhs r) (rhs r) refl refl (ax-ok r)
      vrel-sound (cong↑ {w = w} {v = v} a) = cong↑-sound {w = w} {v} (vrel-sound a)
      vrel-sound (comm₁ h g)     = comm₁-sound h g
      vrel-sound (comm₂ h g)     = comm₂-sound h g
      vrel-sound (comm₃ h g)     = comm₃-sound h g
      vrel-sound (ω↑=ω h)        = ω↑=ω-sound h

      -- Every derivable equation holds.
      sound : n ⊢ w ≈ v → ⟦ w ⟧ ≈ ⟦ v ⟧
      sound {w = w} PB.refl          = ≈-refl {s = ⟦ w ⟧}
      sound {w = w} {v} (PB.sym e)   = ≈-sym' {s = ⟦ v ⟧} {⟦ w ⟧} (sound e)
      sound {w = w} {v} (PB.trans {v = u} e f) =
        ≈-trans' {s₁ = ⟦ w ⟧} {⟦ u ⟧} {⟦ v ⟧} (sound e) (sound f)
      sound (PB.cong {w = w} {w' = w'} {v = v} {v' = v'} e f) =
        ∙-cong {s₁ = ⟦ w ⟧} {⟦ w' ⟧} {⟦ v ⟧} {⟦ v' ⟧} (sound e) (sound f)
      sound (PB.assoc {w = w} {v = v} {u = u}) =
        Monoid.assoc (monoid _) ⟦ w ⟧ ⟦ v ⟧ ⟦ u ⟧
      sound (PB.left-unit {w = w})  = proj₁ (Monoid.identity (monoid _)) ⟦ w ⟧
      sound (PB.right-unit {w = w}) = proj₂ (Monoid.identity (monoid _)) ⟦ w ⟧
      sound (PB.axiom a)            = vrel-sound a

    --------------------------------------------------------------------
    -- Lemma 25, with this semantics as the model

    module Separate
      {Rule : Set} (arity : Rule → ℕ)
      (lhs rhs : (r : Rule) → Circuit (arity r))
      (ρ : Rule) (b : ℕ)
      (ax-ok : ∀ r → ¬ r ≡ ρ → arity r ≤ b → ⟦ lhs r ⟧ ≈ ⟦ rhs r ⟧)
      where

      open Fragment arity lhs rhs
      open Model.Separators arity lhs rhs
      open Separator ρ b monoid ⟦_⟧₀
        using (module Separates) renaming (⟦_⟧ to ⟦_⟧ᴹ)

      private
        -- The model's reading is this one.
        ᴹ≡ : (w : Circuit n) → ⟦ w ⟧ᴹ ≡ ⟦ w ⟧
        ᴹ≡ [ g ]ʷ  = refl
        ᴹ≡ ε       = refl
        ᴹ≡ (w • v) = Eq.cong₂ _∙_ (ᴹ≡ w) (ᴹ≡ v)

        ≈-subst : {s₁ s₂ t₁ t₂ : Sc n} → s₁ ≡ s₂ → t₁ ≡ t₂ → s₁ ≈ t₁ → s₂ ≈ t₂
        ≈-subst refl refl e = e

        ᴹ : {w v : Circuit n} → ⟦ w ⟧ ≈ ⟦ v ⟧ → ⟦ w ⟧ᴹ ≈ ⟦ v ⟧ᴹ
        ᴹ {w = w} {v} = ≈-subst (Eq.sym (ᴹ≡ w)) (Eq.sym (ᴹ≡ v))

      -- The separation is read on ρ ↓ᵏ 0: for a given ρ, that is ρ on
      -- its own wires, by computation.
      separates : arity ρ ≤ b → ¬ (⟦ lhs ρ ↓ᵏ 0 ⟧ ≈ ⟦ rhs ρ ↓ᵏ 0 ⟧) →
                  Independent-axiom ρ
      separates ar≤b sep =
        Separates.separates
          (λ {_} {w} {v} s → ᴹ {w = w} {v} (sym-sound s))
          (λ r k r≢ρ ar≤b' → ᴹ {w = lhs r ↓ᵏ k} {rhs r ↓ᵏ k} (lift (lhs r) (rhs r) refl refl (ax-ok r r≢ρ ar≤b')))
          (λ {_} {w} {v} _ _ e →
             ᴹ {w = w ↑} {v ↑}
               (cong↑-sound {w = w} {v} (≈-subst (ᴹ≡ w) (ᴹ≡ v) e)))
          (λ h g → comm₁-sound h g) (λ h g → comm₂-sound h g)
          (λ h g → comm₃-sound h g)
          (λ {n} h → ᴹ {w = [ gate₀ {n} h ]ʷ ↑} {[ gate₀ h ]ʷ} (ω↑=ω-sound h))
          ar≤b
          (λ e → sep (≈-subst (ᴹ≡ (lhs ρ ↓ᵏ 0)) (ᴹ≡ (rhs ρ ↓ᵏ 0)) e))

------------------------------------------------------------------------
-- The exact semantics, and its quotient by global phases

module Exact = Laws (λ k → k ≡ 0) refl (λ { refl refl → refl })
                    (λ { refl → ℕP.*-zeroʳ N-1 })

module Projective = Laws (λ _ → ⊤) tt (λ _ _ → tt) (λ _ → tt)
