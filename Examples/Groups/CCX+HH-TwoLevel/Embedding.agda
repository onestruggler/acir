------------------------------------------------------------------------
-- Presentations of groups
--
-- Embedding a smaller dimension: a strictly increasing map of indices
-- ι : Fin d → Fin n relabels generators, and it carries every relation
-- of Table 1 in dimension d to the same relation in dimension n.  So a
-- relation derived in a small fixed dimension, over concrete indices,
-- holds at any increasing choice of indices.  The maps are built from
-- strictly increasing sequences of indices (emb).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Embedding where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ ; s≤s)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics

private
  variable
    d n : ℕ

------------------------------------------------------------------------
-- Increasing maps of indices

record Emb (d n : ℕ) : Set where
  field
    ι    : Fin d → Fin n
    mono : ∀ {a b : Fin d} → a < b → ι a < ι b

  injective : ∀ {a b : Fin d} → a ≢ b → ι a ≢ ι b
  injective {a} {b} a≢b with FinP.<-cmp a b
  ... | tri< a<b _ _ = λ eq → FinP.<-irrefl eq (mono a<b)
  ... | tri≈ _ a≡b _ = λ _ → a≢b a≡b
  ... | tri> _ _ b<a = λ eq → FinP.<-irrefl (sym eq) (mono b<a)

  -- Relabelling generators and words.
  gen : Gen d → Gen n
  gen (M-gen a)             = M-gen (ι a)
  gen (X-gen a b p)         = X-gen (ι a) (ι b) (mono p)
  gen (K-gen a b c d p q r) = K-gen (ι a) (ι b) (ι c) (ι d) (mono p) (mono q) (mono r)

  word : Word (Gen d) → Word (Gen n)
  word = wmap gen

open Emb public

------------------------------------------------------------------------
-- Embeddings from increasing sequences

infixr 5 _∷ᵢ_

-- Strictly increasing sequences of indices.
data Incr {n : ℕ} : {d : ℕ} → Vec (Fin n) d → Set where
  []ᵢ  : Incr []
  [_]ᵢ : (a : Fin n) → Incr (a ∷ [])
  _∷ᵢ_ : ∀ {d a b} {v : Vec (Fin n) d} → a < b → Incr (b ∷ v) → Incr (a ∷ b ∷ v)

private
  head< : ∀ {d a} {v : Vec (Fin n) d} → Incr (a ∷ v) → ∀ y → a < lookup v y
  head< [ a ]ᵢ   ()
  head< (p ∷ᵢ i) zero    = p
  head< (p ∷ᵢ i) (suc y) = FinP.<-trans p (head< i y)

  mono-incr : ∀ {d} {v : Vec (Fin n) d} → Incr v → ∀ {x y : Fin d} → x < y → lookup v x < lookup v y
  mono-incr []ᵢ      {()}
  mono-incr [ a ]ᵢ   {zero}  {zero}  ()
  mono-incr [ a ]ᵢ   {zero}  {suc ()}
  mono-incr [ a ]ᵢ   {suc ()}
  mono-incr (p ∷ᵢ i) {zero}  {zero}  ()
  mono-incr (p ∷ᵢ i) {zero}  {suc y} _         = head< (p ∷ᵢ i) y
  mono-incr (p ∷ᵢ i) {suc x} {zero}  ()
  mono-incr (p ∷ᵢ i) {suc x} {suc y} (s≤s lt) = mono-incr i lt

emb : (v : Vec (Fin n) d) → Incr v → Emb d n
emb v i = record { ι = lookup v ; mono = mono-incr i }

------------------------------------------------------------------------
-- Embeddings carry relations to relations

module _ (e : Emb d n) where

  private
    module D = PB (_===_ {d})
    module N = PB (_===_ {n})
    m = mono e
    j = injective e

  -- Each axiom goes to the same axiom.
  word-axiom : ∀ {w v} → w === v → word e w N.≈ word e v
  word-axiom (r1a p) = N.axiom (r1a (m p))
  word-axiom r1b = N.axiom r1b
  word-axiom (r1c p q r) = N.axiom (r1c (m p) (m q) (m r))
  word-axiom (r2a p q ac ad bc bd) = N.axiom (r2a (m p) (m q) (j ac) (j ad) (j bc) (j bd))
  word-axiom (r2b p ca cb) = N.axiom (r2b (m p) (j ca) (j cb))
  word-axiom (r2c p q r s ac ad ae af bc bd be bf) =
    N.axiom (r2c (m p) (m q) (m r) (m s) (j ac) (j ad) (j ae) (j af) (j bc) (j bd) (j be) (j bf))
  word-axiom (r2d ab) = N.axiom (r2d (j ab))
  word-axiom (r2e p q r ab ac ad ae) = N.axiom (r2e (m p) (m q) (m r) (j ab) (j ac) (j ad) (j ae))
  word-axiom (r2f p q r s t u ae af ag ah be bf bg bh ce cf cg ch de df dg dh) =
    N.axiom (r2f (m p) (m q) (m r) (m s) (m t) (m u)
                 (j ae) (j af) (j ag) (j ah) (j be) (j bf) (j bg) (j bh)
                 (j ce) (j cf) (j cg) (j ch) (j de) (j df) (j dg) (j dh))
  word-axiom (r3a p q r) = N.axiom (r3a (m p) (m q) (m r))
  word-axiom (r3b p q r) = N.axiom (r3b (m p) (m q) (m r))
  word-axiom (r3c p) = N.axiom (r3c (m p))
  word-axiom (r3d p q r s t) = N.axiom (r3d (m p) (m q) (m r) (m s) (m t))
  word-axiom (r3e p q r s t u) = N.axiom (r3e (m p) (m q) (m r) (m s) (m t) (m u))
  word-axiom (r3f p q r s t u) = N.axiom (r3f (m p) (m q) (m r) (m s) (m t) (m u))
  word-axiom (r3g p q r s t) = N.axiom (r3g (m p) (m q) (m r) (m s) (m t))
  word-axiom (r4a p q r s) = N.axiom (r4a (m p) (m q) (m r) (m s))
  word-axiom (r4b p q r) = N.axiom (r4b (m p) (m q) (m r))
  word-axiom (r4c p q r s) = N.axiom (r4c (m p) (m q) (m r) (m s))
  word-axiom (r5a p q r s t u v) = N.axiom (r5a (m p) (m q) (m r) (m s) (m t) (m u) (m v))
  word-axiom (r6a p q r s t u v w) = N.axiom (r6a (m p) (m q) (m r) (m s) (m t) (m u) (m v) (m w))

  -- And hence derivable equations to derivable equations.
  word-≈ : ∀ {w v} → w D.≈ v → word e w N.≈ word e v
  word-≈ = PP.GenCongruence.fʷ-cong (_===_ {d}) (_===_ {n}) (gen e) word-axiom
