------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine circuits built from bits
--
-- Blake's affine circuits (at p = 2) that the decoding conjugates its
-- gadgets by, written from bit vectors so that their action on bits
-- (Five.Sem.Aff.bm) computes: X on the wires where a vector has a 1
-- (`Xb`), the fan-out of wire 0 onto the wires of a vector (`colB`), the
-- fan-in onto wire 0 of the parity of a set of wires (`rowB`), and from
-- them `α p q`, which sends the basis state 0 to p and e₀ to q whenever
-- p ≠ q (`α-o`, `α-e`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Build where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_ ; _∧_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Nat.Primality using (prime[2])
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics using (Bits)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff using (bm ; bmg ; Lv ; Bv ; bm-fn ; Lv-Bv)

import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Aff 0 prime[2] using (adm)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm using (fn)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Bits

ze : Bits n
ze {zero}  = []
ze {suc n} = false ∷ ze

infixl 6 _⊕ᵥ_
_⊕ᵥ_ : Bits n → Bits n → Bits n
[]      ⊕ᵥ []      = []
(a ∷ x) ⊕ᵥ (b ∷ y) = (a xor b) ∷ (x ⊕ᵥ y)

dot : Bits n → Bits n → Bool
dot []      []      = false
dot (c ∷ w) (b ∷ x) = (c ∧ b) xor dot w x

-- The vector keeping only the first 1.
first : Bits n → Bits n
first []          = []
first (true ∷ v)  = true ∷ ze
first (false ∷ v) = false ∷ first v

ze-⊕ : (p : Bits n) → ze ⊕ᵥ p ≡ p
ze-⊕ []      = refl
ze-⊕ (a ∷ p) = Eq.cong (a ∷_) (ze-⊕ p)

⊕-cancel : (p q : Bits n) → (p ⊕ᵥ q) ⊕ᵥ p ≡ q
⊕-cancel []      []      = refl
⊕-cancel (a ∷ p) (b ∷ q) =
  Eq.cong₂ _∷_ (Eq.trans (Eq.cong (_xor a) (BoolP.xor-comm a b))
                 (Eq.trans (BoolP.xor-assoc b a a) (Eq.trans (Eq.cong (b xor_) (BoolP.xor-same a))
                   (BoolP.xor-identityʳ b))))
               (⊕-cancel p q)

⊕-ze : (p q : Bits n) → p ⊕ᵥ q ≡ ze → p ≡ q
⊕-ze []          []          e = refl
⊕-ze (false ∷ p) (false ∷ q) e = Eq.cong (false ∷_) (⊕-ze p q (Eq.cong tail e))
  where tail : ∀ {k} → Bits (suc k) → Bits k
        tail (_ ∷ x) = x
⊕-ze (true ∷ p)  (true ∷ q)  e = Eq.cong (true ∷_) (⊕-ze p q (Eq.cong tail e))
  where tail : ∀ {k} → Bits (suc k) → Bits k
        tail (_ ∷ x) = x
⊕-ze (false ∷ p) (true ∷ q)  ()
⊕-ze (true ∷ p)  (false ∷ q) ()

dot-zeʳ : (w : Bits n) → dot w ze ≡ false
dot-zeʳ []      = refl
dot-zeʳ (c ∷ w) = Eq.trans (Eq.cong (_xor dot w ze) (BoolP.∧-zeroʳ c)) (dot-zeʳ w)

dot-zeˡ : (x : Bits n) → dot ze x ≡ false
dot-zeˡ []      = refl
dot-zeˡ (b ∷ x) = dot-zeˡ x

dot-first : (v : Bits n) → v ≢ ze → dot (first v) v ≡ true
dot-first []          ne = ⊥-elim (ne refl)
dot-first (true ∷ v)  ne = Eq.cong not (dot-zeˡ v)
dot-first (false ∷ v) ne = dot-first v (λ e → ne (Eq.cong (false ∷_) e))

------------------------------------------------------------------------
-- Lifting

bm-↑ : (w : B.Circuit n) (a : Bool) (x : Bits n) → bm (w B.↑) (a ∷ x) ≡ a ∷ bm w x
bm-↑ [ g ]ʷ  a x = refl
bm-↑ ε       a x = refl
bm-↑ (u • v) a x = Eq.trans (Eq.cong (bm (u B.↑)) (bm-↑ v a x)) (bm-↑ u a (bm v x))

-- Blake's action, through bits.
fn-bm : (w : B.Circuit n) (x : Bits n) → fn w (Lv x) ≡ Lv (bm w x)
fn-bm w x = Eq.trans (Eq.sym (Lv-Bv (fn w (Lv x)))) (Eq.cong Lv (bm-fn w x))

------------------------------------------------------------------------
-- X on the wires of a vector

Xb : Bits n → B.Circuit n
Xb []          = ε
Xb (true ∷ b)  = B.X • Xb b B.↑
Xb (false ∷ b) = Xb b B.↑

bm-Xb : (b x : Bits n) → bm (Xb b) x ≡ x ⊕ᵥ b
bm-Xb []          []      = refl
bm-Xb (true ∷ b)  (a ∷ x) =
  Eq.trans (Eq.cong (bmg (B.gate₁ B.X-gate)) (bm-↑ (Xb b) a x))
    (Eq.cong₂ _∷_ (xor-true a) (bm-Xb b x))
  where
  xor-true : ∀ a → not a ≡ a xor true
  xor-true false = refl
  xor-true true  = refl
bm-Xb (false ∷ b) (a ∷ x) =
  Eq.trans (bm-↑ (Xb b) a x) (Eq.cong₂ _∷_ (Eq.sym (BoolP.xor-identityʳ a)) (bm-Xb b x))

------------------------------------------------------------------------
-- The fan-out from wire 0, at 0 and e₀

private
  cxr : Bool → B.Circuit (suc (suc n))
  cxr true  = B.CXʳ
  cxr false = ε

  cxr-e : (c : Bool) (x : Bits n) → bm (cxr c) (true ∷ false ∷ x) ≡ true ∷ c ∷ x
  cxr-e true  x = refl
  cxr-e false x = refl

  cxr-o : (c : Bool) (x : Bits n) → bm (cxr c) (false ∷ false ∷ x) ≡ false ∷ false ∷ x
  cxr-o true  x = refl
  cxr-o false x = refl

colB : Bits n → B.Circuit (suc n)
colB []      = ε
colB (c ∷ v) = (B.SWAP • colB v B.↑ • B.SWAP) • cxr c

colB-e : (v : Bits n) → bm (colB v) (true ∷ ze) ≡ true ∷ v
colB-e []      = refl
colB-e (c ∷ v) =
  Eq.trans (Eq.cong (bm (B.SWAP • colB v B.↑ • B.SWAP)) (cxr-e c ze))
    (Eq.cong (bm B.SWAP) (Eq.trans (bm-↑ (colB v) c (true ∷ ze)) (Eq.cong (c ∷_) (colB-e v))))

colB-o : (v : Bits n) → bm (colB v) (false ∷ ze) ≡ false ∷ ze
colB-o []      = refl
colB-o (c ∷ v) =
  Eq.trans (Eq.cong (bm (B.SWAP • colB v B.↑ • B.SWAP)) (cxr-o c ze))
    (Eq.cong (bm B.SWAP) (Eq.trans (bm-↑ (colB v) false (false ∷ ze)) (Eq.cong (false ∷_) (colB-o v))))

------------------------------------------------------------------------
-- The fan-in onto wire 0

private
  cx : Bool → B.Circuit (suc (suc n))
  cx true  = B.CX
  cx false = ε

  cx-at : (c a b : Bool) (x : Bits n) → bm (cx c) (a ∷ b ∷ x) ≡ (a xor (c ∧ b)) ∷ b ∷ x
  cx-at true  a b x = refl
  cx-at false a b x = Eq.cong (λ t → t ∷ b ∷ x) (Eq.sym (BoolP.xor-identityʳ a))

rowB : Bits n → B.Circuit (suc n)
rowB []      = ε
rowB (c ∷ w) = (B.SWAP • rowB w B.↑ • B.SWAP) • cx c

bm-rowB : (w : Bits n) (a : Bool) (x : Bits n) → bm (rowB w) (a ∷ x) ≡ (a xor dot w x) ∷ x
bm-rowB []      a []      = Eq.cong (_∷ []) (Eq.sym (BoolP.xor-identityʳ a))
bm-rowB (c ∷ w) a (b ∷ x) =
  Eq.trans (Eq.cong (bm (B.SWAP • rowB w B.↑ • B.SWAP)) (cx-at c a b x))
    (Eq.cong (bm B.SWAP)
      (Eq.trans (bm-↑ (rowB w) b ((a xor (c ∧ b)) ∷ x))
        (Eq.cong (b ∷_) (Eq.trans (bm-rowB w (a xor (c ∧ b)) x)
          (Eq.cong (_∷ x) (BoolP.xor-assoc a (c ∧ b) (dot w x)))))))

------------------------------------------------------------------------
-- A linear circuit sending e₀ to a nonzero vector

L : Bits (suc n) → B.Circuit (suc n)
L (true ∷ v)  = colB v
L (false ∷ v) = rowB (first v) • colB v

L-o : (d : Bits (suc n)) → bm (L d) ze ≡ ze
L-o (true ∷ v)  = colB-o v
L-o (false ∷ v) =
  Eq.trans (Eq.cong (bm (rowB (first v))) (colB-o v))
    (Eq.trans (bm-rowB (first v) false ze) (Eq.cong (_∷ ze) (dot-zeʳ (first v))))

L-e : (d : Bits (suc n)) → d ≢ ze → bm (L d) (true ∷ ze) ≡ d
L-e (true ∷ v)  ne = colB-e v
L-e (false ∷ v) ne =
  Eq.trans (Eq.cong (bm (rowB (first v))) (colB-e v))
    (Eq.trans (bm-rowB (first v) true v)
      (Eq.cong (λ t → not t ∷ v) (dot-first v (λ e → ne (Eq.cong (false ∷_) e)))))

------------------------------------------------------------------------
-- The affine circuit sending 0 to p and e₀ to q

α : Bits (suc n) → Bits (suc n) → B.Circuit (suc n)
α p q = Xb p • L (p ⊕ᵥ q)

α-o : (p q : Bits (suc n)) → bm (α p q) ze ≡ p
α-o p q = Eq.trans (Eq.cong (bm (Xb p)) (L-o (p ⊕ᵥ q))) (Eq.trans (bm-Xb p ze) (ze-⊕ p))

α-e : (p q : Bits (suc n)) → p ≢ q → bm (α p q) (true ∷ ze) ≡ q
α-e p q ne =
  Eq.trans (Eq.cong (bm (Xb p)) (L-e (p ⊕ᵥ q) (λ e → ne (⊕-ze p q e))))
    (Eq.trans (bm-Xb p (p ⊕ᵥ q)) (⊕-cancel p q))
