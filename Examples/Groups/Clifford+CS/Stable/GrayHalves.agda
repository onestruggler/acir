------------------------------------------------------------------------
-- Presentations of groups
--
-- The two halves of the Gray numbering, at every width
--
-- On 5 + m wires the basis indices below 2^(4 + m) are those whose code
-- has the top bit 0, and read the (4 + m)-wire code there (`lo`,
-- `cod-lo`); the others have the top bit 1 and read the (4 + m)-wire
-- code with its own top bit flipped (`hi`, `cod-hi`): the reflected
-- Gray code reflects the lower half onto the upper.  The bitwise formula
-- of the code (Real-Clifford+CH.Auxiliary.Gray) gives both: `ungray`
-- keeps a bit 0 put on top and turns a 1 put on top over the flipped
-- code into the same digits with a 1 on top (`ungray0`, `ungray1`), so
-- the two embeddings add 0 and 2^(4 + m) to the index (`toℕ-lo`,
-- `toℕ-hi`) and keep the order of the indices, as Stable.Ren needs.
-- Five.Sem.Gray5 is the case m = 0, by computation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Stable.GrayHalves (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
open import Data.Fin using (Fin ; toℕ ; cast ; _<_)
open import Data.Fin.Properties using (toℕ-cast ; toℕ-fromℕ< ; toℕ-injective)
open import Data.Nat using (zero ; suc ; _+_ ; _*_ ; _^_)
open import Data.Nat.Properties using (+-identityʳ ; *-zeroʳ ; *-identityʳ ; +-monoˡ-<)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Vec using (Vec ; [] ; _∷_ ; _∷ʳ_)
open import Data.Vec.Properties using (∷ʳ-injectiveˡ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₄₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (hd ; bit ; fromBits ; toBits ; gray ; ungray ; code ; index ; ungray-gray ; fromBits-toBits)
open import Data.Fin.Properties using (toℕ<n)
import Examples.Groups.Clifford+CS.Numbering as Numbering

private
  module N0 = Numbering (₄₊ m)
  module N1 = Numbering (₄₊ (suc m))

  B : ℕ → Set
  B = Vec Bool

------------------------------------------------------------------------
-- The top bit of a code

-- The last bit flipped.
flp : ∀ {k} → B (suc k) → B (suc k)
flp {zero}  (x ∷ []) = not x ∷ []
flp {suc k} (x ∷ g)  = x ∷ flp g

flp-flp : ∀ {k} (g : B (suc k)) → flp (flp g) ≡ g
flp-flp {zero}  (true  ∷ []) = Eq.refl
flp-flp {zero}  (false ∷ []) = Eq.refl
flp-flp {suc k} (x ∷ g)      = Eq.cong (x ∷_) (flp-flp g)

private
  hd-snoc0 : ∀ {k} (w : B k) → hd (w ∷ʳ false) ≡ hd w
  hd-snoc0 []      = Eq.refl
  hd-snoc0 (x ∷ w) = Eq.refl

  hd-snoc : ∀ {k} (w : B (suc k)) (b : Bool) → hd (w ∷ʳ b) ≡ hd w
  hd-snoc (x ∷ w) b = Eq.refl

-- A 0 on top keeps the digits.
ungray0 : ∀ {k} (g : B k) → ungray (g ∷ʳ false) ≡ ungray g ∷ʳ false
ungray0 []      = Eq.refl
ungray0 (x ∷ g) =
  Eq.cong₂ _∷_ (Eq.cong (x xor_) (Eq.trans (Eq.cong hd (ungray0 g)) (hd-snoc0 (ungray g)))) (ungray0 g)

-- A 1 on top over the flipped code is the same digits with a 1 on top.
ungray1 : ∀ {k} (g : B (suc k)) → ungray (flp g ∷ʳ true) ≡ ungray g ∷ʳ true
ungray1 {zero}  (true  ∷ []) = Eq.refl
ungray1 {zero}  (false ∷ []) = Eq.refl
ungray1 {suc k} (x ∷ g)      =
  Eq.cong₂ _∷_ (Eq.cong (x xor_) (Eq.trans (Eq.cong hd (ungray1 g)) (hd-snoc (ungray g) true))) (ungray1 g)

fromBits-snoc : ∀ {k} (v : B k) (b : Bool) → fromBits (v ∷ʳ b) ≡ fromBits v + 2 ^ k * bit b
fromBits-snoc []      true  = Eq.refl
fromBits-snoc []      false = Eq.refl
fromBits-snoc {suc k} (x ∷ v) b =
  Eq.trans (Eq.cong (λ t → bit x + 2 * t) (fromBits-snoc v b))
    (solve 4 (λ a f p c → a :+ con 2 :* (f :+ p :* c) := (a :+ con 2 :* f) :+ (con 2 :* p) :* c)
           Eq.refl (bit x) (fromBits v) (2 ^ k) (bit b))
  where open +-*-Solver

------------------------------------------------------------------------
-- The two embeddings

lo hi : Fin N0.N → Fin N1.N
lo a = N1.idx (N0.cod a ∷ʳ false)
hi a = N1.idx (flp (N0.cod a) ∷ʳ true)

cod-lo : ∀ (a : Fin N0.N) → N1.cod (lo a) ≡ N0.cod a ∷ʳ false
cod-lo a = N1.cod-idx (N0.cod a ∷ʳ false)

cod-hi : ∀ (a : Fin N0.N) → N1.cod (hi a) ≡ flp (N0.cod a) ∷ʳ true
cod-hi a = N1.cod-idx (flp (N0.cod a) ∷ʳ true)

lo-inj : ∀ {a b} → lo a ≡ lo b → a ≡ b
lo-inj e = N0.cod-inj (∷ʳ-injectiveˡ _ _ (N1.idx-inj e))

hi-inj : ∀ {a b} → hi a ≡ hi b → a ≡ b
hi-inj {a} {b} e =
  N0.cod-inj (Eq.trans (Eq.sym (flp-flp (N0.cod a)))
               (Eq.trans (Eq.cong flp (∷ʳ-injectiveˡ (flp (N0.cod a)) (flp (N0.cod b)) (N1.idx-inj e))) (flp-flp (N0.cod b))))

------------------------------------------------------------------------
-- The embeddings on the indices

private
  -- An index is the number of the digits of its code.
  toℕ-idx : ∀ n (x : B n) → toℕ (Numbering.idx n x) ≡ fromBits (ungray x)
  toℕ-idx n x =
    Eq.trans (toℕ-cast (Eq.sym (Numbering.N≡ n)) (index n x)) (toℕ-fromℕ< _)

  toℕ-cod : ∀ n (a : Fin (Numbering.N n)) → toℕ a ≡ fromBits (ungray (Numbering.cod n a))
  toℕ-cod n a =
    Eq.sym (Eq.trans (Eq.cong fromBits (ungray-gray (toBits n (toℕ (cast (Numbering.N≡ n) a)))))
             (Eq.trans (fromBits-toBits n _ (toℕ<n (cast (Numbering.N≡ n) a)))
                       (toℕ-cast (Numbering.N≡ n) a)))

toℕ-lo : ∀ (a : Fin N0.N) → toℕ (lo a) ≡ toℕ a
toℕ-lo a =
  Eq.trans (toℕ-idx (₄₊ (suc m)) (N0.cod a ∷ʳ false))
    (Eq.trans (Eq.cong fromBits (ungray0 (N0.cod a)))
      (Eq.trans (fromBits-snoc (ungray (N0.cod a)) false)
        (Eq.trans (Eq.cong (fromBits (ungray (N0.cod a)) +_) (*-zeroʳ (2 ^ ₄₊ m)))
          (Eq.trans (+-identityʳ _) (Eq.sym (toℕ-cod (₄₊ m) a))))))

toℕ-hi : ∀ (a : Fin N0.N) → toℕ (hi a) ≡ toℕ a + 2 ^ ₄₊ m
toℕ-hi a =
  Eq.trans (toℕ-idx (₄₊ (suc m)) (flp (N0.cod a) ∷ʳ true))
    (Eq.trans (Eq.cong fromBits (ungray1 (N0.cod a)))
      (Eq.trans (fromBits-snoc (ungray (N0.cod a)) true)
        (Eq.trans (Eq.cong (fromBits (ungray (N0.cod a)) +_) (*-identityʳ (2 ^ ₄₊ m)))
          (Eq.cong (_+ 2 ^ ₄₊ m) (Eq.sym (toℕ-cod (₄₊ m) a))))))

lo-mono : ∀ {a b : Fin N0.N} → a < b → lo a < lo b
lo-mono {a} {b} lt = Eq.subst₂ Data.Nat._<_ (Eq.sym (toℕ-lo a)) (Eq.sym (toℕ-lo b)) lt

hi-mono : ∀ {a b : Fin N0.N} → a < b → hi a < hi b
hi-mono {a} {b} lt =
  Eq.subst₂ Data.Nat._<_ (Eq.sym (toℕ-hi a)) (Eq.sym (toℕ-hi b)) (+-monoˡ-< (2 ^ ₄₊ m) lt)
