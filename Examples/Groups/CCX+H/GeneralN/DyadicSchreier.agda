------------------------------------------------------------------------
-- Presentations of groups
--
-- Every dyadic K edge reduces to two even signed permutations and one
-- mixed atom M_a X_bc K_abcd.  Only two spare indices outside the four
-- K indices are needed for this factorization.  The circuit realization
-- of the mixed atom uses further spare indices (construct.py, n >= 4).
-- All equalities here follow from Table 1, at symbolic dimension.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.DyadicSchreier (N : ℕ) where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as D
import Examples.Groups.CCX+HH.Subgroup.Presentation as Sub
open import Examples.Groups.CCX+HH.Subgroup.Action using (Coset ; c00 ; c10 ; c11 ; c01 ; dyadic-step)
import Examples.Groups.CCX+H.GeneralN.Factorization as Factorization
open import Presentation.Base (U._===_ {2 + N}) hiding (_===_)
open import Presentation.GroupLike using (module Group-Lemmas)

private
  module G = Group-Lemmas (U._===_ {2 + N}) D.grouplike
  module F = Factorization (U._===_ {2 + N}) D.grouplike
  module P = Sub N

open G using (_⁻¹)
open P using (rep ; state)
open F using (comm-product ; product-comm)

-- A syntactic witness that a word has no K letters.
data Signed : Word (U.Gen (2 + N)) → Set where
  sign : ∀ a → Signed (U.M a)
  exchange : ∀ a b .(p : a < b) → Signed (U.X a b p)
  unit : Signed ε
  product : ∀ {u v} → Signed u → Signed v → Signed (u • v)

signed-inverse : ∀ {w} → Signed w → Signed (w ⁻¹)
signed-inverse (sign a) = sign a
signed-inverse (exchange a b p) = exchange a b p
signed-inverse unit = unit
signed-inverse (product u v) = product (signed-inverse v) (signed-inverse u)

rep-signed : ∀ c → Signed (rep c)
rep-signed c00 = unit
rep-signed c10 = sign _
rep-signed c11 = exchange _ _ _
rep-signed c01 = product (sign _) (exchange _ _ _)

module Block
  (a b c d e f : Fin (2 + N))
  .(ab : a < b) .(bc : b < c) .(cd : c < d) .(ef : e < f)
  (ea : e ≢ a) (eb : e ≢ b) (ec : e ≢ c) (ed : e ≢ d)
  (fa : f ≢ a) (fb : f ≢ b) (fc : f ≢ c) (fd : f ≢ d)
  where

  A K J : Word (U.Gen (2 + N))
  A = U.M a • U.X b c bc
  K = U.K a b c d ab bc cd
  J = A • K

  R Z T S : Coset → Word (U.Gen (2 + N))
  R q = rep (dyadic-step q (U.K-gen a b c d ab bc cd)) ⁻¹
  Z c00 = U.M e • U.X e f ef
  Z c10 = U.X e f ef
  Z c11 = U.M e
  Z c01 = ε
  T q = (rep q • A ⁻¹) • R q
  S q = Z q • R q

  private
    Me-J : U.M e • J ≈ J • U.M e
    Me-J = comm-product
      (comm-product (axiom (U.r2d ea)) (sym (axiom (U.r2b bc eb ec))))
      (axiom (U.r2e ab bc cd ea eb ec ed))

    Xef-J : U.X e f ef • J ≈ J • U.X e f ef
    Xef-J = comm-product
      (comm-product
        (axiom (U.r2b ef (λ eq → ea (Eq.sym eq)) (λ eq → fa (Eq.sym eq))))
        (axiom (U.r2a ef bc eb ec fb fc)))
      (axiom (U.r2c ef ab bc cd ea eb ec ed fa fb fc fd))

  Z-commutes : ∀ q → Z q • J ≈ J • Z q
  Z-commutes c00 = product-comm Me-J Xef-J
  Z-commutes c10 = Xef-J
  Z-commutes c11 = Me-J
  Z-commutes c01 = trans left-unit (sym right-unit)

  -- This is exactly the source image of the formal Schreier generator.
  edge-factor : ∀ q → P.e (q , U.K-gen a b c d ab bc cd) ≈
    (T q • S q ⁻¹) • (J • S q)
  edge-factor q = F.factor (rep q) (R q) A K (Z q) (Z-commutes q)

  A-signed : Signed A
  A-signed = product (sign a) (exchange b c bc)

  R-signed : ∀ q → Signed (R q)
  R-signed q = signed-inverse
    (rep-signed (dyadic-step q (U.K-gen a b c d ab bc cd)))

  Z-signed : ∀ q → Signed (Z q)
  Z-signed c00 = product (sign e) (exchange e f ef)
  Z-signed c10 = exchange e f ef
  Z-signed c11 = sign e
  Z-signed c01 = unit

  T-signed : ∀ q → Signed (T q)
  T-signed q = product (product (rep-signed q) (signed-inverse A-signed)) (R-signed q)

  S-signed : ∀ q → Signed (S q)
  S-signed q = product (Z-signed q) (R-signed q)

  -- For signed permutations, state 00 means both the sign count and
  -- permutation parity are even.  These proofs are independent of
  -- the chosen indices, including coincidences with representative 0,1.
  T-closed : ∀ q → state c00 (T q) ≡ c00
  T-closed c00 = Eq.refl
  T-closed c10 = Eq.refl
  T-closed c11 = Eq.refl
  T-closed c01 = Eq.refl

  S-closed : ∀ q → state c00 (S q) ≡ c00
  S-closed c00 = Eq.refl
  S-closed c10 = Eq.refl
  S-closed c11 = Eq.refl
  S-closed c01 = Eq.refl

  J-closed : state c00 J ≡ c00
  J-closed = Eq.refl
