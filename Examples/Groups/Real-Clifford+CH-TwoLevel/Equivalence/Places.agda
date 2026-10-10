------------------------------------------------------------------------
-- Presentations of groups
--
-- Sorted indices s₀ < … < s_{m-1} of Fin (m + k), for m = 4, 6: their
-- embedding (emb), and the transpositions (ps) that take the first m
-- indices to them, index by index (place): conjugation by these moves
-- an equation on the first m indices to the sorted ones
-- (ClementLocal.move).  Generated.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.Places where

open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; _<_ ; _↑ˡ_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base as ℕ using (ℕ ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Embedding using (Emb)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric using (τ ; τ-p ; τ-o)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.ClementLocal as CL

private
  lt⇒≢ : ∀ {n} {x y : Fin n} → toℕ x ℕ.< toℕ y → x ≢ y
  lt⇒≢ lt e = ℕP.<-irrefl (≡.cong toℕ e) lt

  sy : ∀ {n} {x y : Fin n} → x ≢ y → y ≢ x
  sy ne e = ne (≡.sym e)

------------------------------------------------------------------------
-- 4 sorted indices

module Emb4 {n : ℕ} {s0 s1 s2 s3 : Fin n}
  (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) where

  -- The sorted indices.
  σ : Fin 4 → Fin n
  σ zero = s0
  σ (suc zero) = s1
  σ (suc (suc zero)) = s2
  σ (suc (suc (suc zero))) = s3

  -- toℕ sᵢ ≥ i.
  b0 : 0 ℕ.≤ toℕ s0
  b0 = z≤n
  b1 : 1 ℕ.≤ toℕ s1
  b1 = ℕP.≤-trans (s≤s b0) p0
  b2 : 2 ℕ.≤ toℕ s2
  b2 = ℕP.≤-trans (s≤s b1) p1
  b3 : 3 ℕ.≤ toℕ s3
  b3 = ℕP.≤-trans (s≤s b2) p2

  -- sᵢ < sⱼ for i < j.
  o01 : s0 < s1
  o01 = p0
  o02 : s0 < s2
  o02 = FinP.<-trans o01 p1
  o03 : s0 < s3
  o03 = FinP.<-trans o02 p2
  o12 : s1 < s2
  o12 = p1
  o13 : s1 < s3
  o13 = FinP.<-trans o12 p2
  o23 : s2 < s3
  o23 = p2

  emb : Emb 4 n
  emb = record { ι = σ ; mono = mono′ }
    where
    mono′ : ∀ {a b : Fin 4} → a < b → σ a < σ b
    mono′ {zero} {zero} ()
    mono′ {zero} {(suc zero)} _ = o01
    mono′ {zero} {(suc (suc zero))} _ = o02
    mono′ {zero} {(suc (suc (suc zero)))} _ = o03
    mono′ {(suc zero)} {zero} ()
    mono′ {(suc zero)} {(suc zero)} (s≤s ())
    mono′ {(suc zero)} {(suc (suc zero))} _ = o12
    mono′ {(suc zero)} {(suc (suc (suc zero)))} _ = o13
    mono′ {(suc (suc zero))} {zero} ()
    mono′ {(suc (suc zero))} {(suc zero)} (s≤s ())
    mono′ {(suc (suc zero))} {(suc (suc zero))} (s≤s (s≤s ()))
    mono′ {(suc (suc zero))} {(suc (suc (suc zero)))} _ = o23
    mono′ {(suc (suc (suc zero)))} {zero} ()
    mono′ {(suc (suc (suc zero)))} {(suc zero)} (s≤s ())
    mono′ {(suc (suc (suc zero)))} {(suc (suc zero))} (s≤s (s≤s ()))
    mono′ {(suc (suc (suc zero)))} {(suc (suc (suc zero)))} (s≤s (s≤s (s≤s ())))

module Sorted4 {k : ℕ} {s0 s1 s2 s3 : Fin (4 ℕ.+ k)}
  (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) where

  open Emb4 p0 p1 p2 public
  open CL {4 ℕ.+ k} using (τs)

  -- The first m indices.
  f : Fin 4 → Fin (4 ℕ.+ k)
  f i = i ↑ˡ k

  -- The placement τ_{f 0, s0} ∘ … ∘ τ_{f 3, s3}.
  ps : List (Fin (4 ℕ.+ k) × Fin (4 ℕ.+ k))
  ps = (f zero , s0) ∷ (f (suc zero) , s1) ∷ (f (suc (suc zero)) , s2) ∷ (f (suc (suc (suc zero))) , s3) ∷ []

  place : ∀ i → τs ps (f i) ≡ σ i
  place zero = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-o (f (suc (suc (suc zero)))) s3 (f zero) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b3)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-o (f (suc (suc zero))) s2 (f zero) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b2)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-o (f (suc zero)) s1 (f zero) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b1)))) ((τ-p (f zero) s0))))
  place (suc zero) = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-o (f (suc (suc (suc zero)))) s3 (f (suc zero)) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b3)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-o (f (suc (suc zero))) s2 (f (suc zero)) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b2)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-p (f (suc zero)) s1)) ((τ-o (f zero) s0 s1 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b1))) (sy (FinP.<⇒≢ o01))))))
  place (suc (suc zero)) = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-o (f (suc (suc (suc zero)))) s3 (f (suc (suc zero))) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (z≤n)))) b3)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-p (f (suc (suc zero))) s2)) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-o (f (suc zero)) s1 s2 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b2))) (sy (FinP.<⇒≢ o12)))) ((τ-o (f zero) s0 s2 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b2))) (sy (FinP.<⇒≢ o02))))))
  place (suc (suc (suc zero))) = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-p (f (suc (suc (suc zero)))) s3)) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-o (f (suc (suc zero))) s2 s3 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (z≤n)))) b3))) (sy (FinP.<⇒≢ o23)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-o (f (suc zero)) s1 s3 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b3))) (sy (FinP.<⇒≢ o13)))) ((τ-o (f zero) s0 s3 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b3))) (sy (FinP.<⇒≢ o03))))))

------------------------------------------------------------------------
-- 6 sorted indices

module Emb6 {n : ℕ} {s0 s1 s2 s3 s4 s5 : Fin n}
  (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) (p3 : s3 < s4) (p4 : s4 < s5) where

  -- The sorted indices.
  σ : Fin 6 → Fin n
  σ zero = s0
  σ (suc zero) = s1
  σ (suc (suc zero)) = s2
  σ (suc (suc (suc zero))) = s3
  σ (suc (suc (suc (suc zero)))) = s4
  σ (suc (suc (suc (suc (suc zero))))) = s5

  -- toℕ sᵢ ≥ i.
  b0 : 0 ℕ.≤ toℕ s0
  b0 = z≤n
  b1 : 1 ℕ.≤ toℕ s1
  b1 = ℕP.≤-trans (s≤s b0) p0
  b2 : 2 ℕ.≤ toℕ s2
  b2 = ℕP.≤-trans (s≤s b1) p1
  b3 : 3 ℕ.≤ toℕ s3
  b3 = ℕP.≤-trans (s≤s b2) p2
  b4 : 4 ℕ.≤ toℕ s4
  b4 = ℕP.≤-trans (s≤s b3) p3
  b5 : 5 ℕ.≤ toℕ s5
  b5 = ℕP.≤-trans (s≤s b4) p4

  -- sᵢ < sⱼ for i < j.
  o01 : s0 < s1
  o01 = p0
  o02 : s0 < s2
  o02 = FinP.<-trans o01 p1
  o03 : s0 < s3
  o03 = FinP.<-trans o02 p2
  o04 : s0 < s4
  o04 = FinP.<-trans o03 p3
  o05 : s0 < s5
  o05 = FinP.<-trans o04 p4
  o12 : s1 < s2
  o12 = p1
  o13 : s1 < s3
  o13 = FinP.<-trans o12 p2
  o14 : s1 < s4
  o14 = FinP.<-trans o13 p3
  o15 : s1 < s5
  o15 = FinP.<-trans o14 p4
  o23 : s2 < s3
  o23 = p2
  o24 : s2 < s4
  o24 = FinP.<-trans o23 p3
  o25 : s2 < s5
  o25 = FinP.<-trans o24 p4
  o34 : s3 < s4
  o34 = p3
  o35 : s3 < s5
  o35 = FinP.<-trans o34 p4
  o45 : s4 < s5
  o45 = p4

  emb : Emb 6 n
  emb = record { ι = σ ; mono = mono′ }
    where
    mono′ : ∀ {a b : Fin 6} → a < b → σ a < σ b
    mono′ {zero} {zero} ()
    mono′ {zero} {(suc zero)} _ = o01
    mono′ {zero} {(suc (suc zero))} _ = o02
    mono′ {zero} {(suc (suc (suc zero)))} _ = o03
    mono′ {zero} {(suc (suc (suc (suc zero))))} _ = o04
    mono′ {zero} {(suc (suc (suc (suc (suc zero)))))} _ = o05
    mono′ {(suc zero)} {zero} ()
    mono′ {(suc zero)} {(suc zero)} (s≤s ())
    mono′ {(suc zero)} {(suc (suc zero))} _ = o12
    mono′ {(suc zero)} {(suc (suc (suc zero)))} _ = o13
    mono′ {(suc zero)} {(suc (suc (suc (suc zero))))} _ = o14
    mono′ {(suc zero)} {(suc (suc (suc (suc (suc zero)))))} _ = o15
    mono′ {(suc (suc zero))} {zero} ()
    mono′ {(suc (suc zero))} {(suc zero)} (s≤s ())
    mono′ {(suc (suc zero))} {(suc (suc zero))} (s≤s (s≤s ()))
    mono′ {(suc (suc zero))} {(suc (suc (suc zero)))} _ = o23
    mono′ {(suc (suc zero))} {(suc (suc (suc (suc zero))))} _ = o24
    mono′ {(suc (suc zero))} {(suc (suc (suc (suc (suc zero)))))} _ = o25
    mono′ {(suc (suc (suc zero)))} {zero} ()
    mono′ {(suc (suc (suc zero)))} {(suc zero)} (s≤s ())
    mono′ {(suc (suc (suc zero)))} {(suc (suc zero))} (s≤s (s≤s ()))
    mono′ {(suc (suc (suc zero)))} {(suc (suc (suc zero)))} (s≤s (s≤s (s≤s ())))
    mono′ {(suc (suc (suc zero)))} {(suc (suc (suc (suc zero))))} _ = o34
    mono′ {(suc (suc (suc zero)))} {(suc (suc (suc (suc (suc zero)))))} _ = o35
    mono′ {(suc (suc (suc (suc zero))))} {zero} ()
    mono′ {(suc (suc (suc (suc zero))))} {(suc zero)} (s≤s ())
    mono′ {(suc (suc (suc (suc zero))))} {(suc (suc zero))} (s≤s (s≤s ()))
    mono′ {(suc (suc (suc (suc zero))))} {(suc (suc (suc zero)))} (s≤s (s≤s (s≤s ())))
    mono′ {(suc (suc (suc (suc zero))))} {(suc (suc (suc (suc zero))))} (s≤s (s≤s (s≤s (s≤s ()))))
    mono′ {(suc (suc (suc (suc zero))))} {(suc (suc (suc (suc (suc zero)))))} _ = o45
    mono′ {(suc (suc (suc (suc (suc zero)))))} {zero} ()
    mono′ {(suc (suc (suc (suc (suc zero)))))} {(suc zero)} (s≤s ())
    mono′ {(suc (suc (suc (suc (suc zero)))))} {(suc (suc zero))} (s≤s (s≤s ()))
    mono′ {(suc (suc (suc (suc (suc zero)))))} {(suc (suc (suc zero)))} (s≤s (s≤s (s≤s ())))
    mono′ {(suc (suc (suc (suc (suc zero)))))} {(suc (suc (suc (suc zero))))} (s≤s (s≤s (s≤s (s≤s ()))))
    mono′ {(suc (suc (suc (suc (suc zero)))))} {(suc (suc (suc (suc (suc zero)))))} (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

module Sorted6 {k : ℕ} {s0 s1 s2 s3 s4 s5 : Fin (6 ℕ.+ k)}
  (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) (p3 : s3 < s4) (p4 : s4 < s5) where

  open Emb6 p0 p1 p2 p3 p4 public
  open CL {6 ℕ.+ k} using (τs)

  -- The first m indices.
  f : Fin 6 → Fin (6 ℕ.+ k)
  f i = i ↑ˡ k

  -- The placement τ_{f 0, s0} ∘ … ∘ τ_{f 5, s5}.
  ps : List (Fin (6 ℕ.+ k) × Fin (6 ℕ.+ k))
  ps = (f zero , s0) ∷ (f (suc zero) , s1) ∷ (f (suc (suc zero)) , s2) ∷ (f (suc (suc (suc zero))) , s3) ∷ (f (suc (suc (suc (suc zero)))) , s4) ∷ (f (suc (suc (suc (suc (suc zero))))) , s5) ∷ []

  place : ∀ i → τs ps (f i) ≡ σ i
  place zero = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (τ (f (suc (suc (suc (suc zero))))) s4 (y)))))) (τ-o (f (suc (suc (suc (suc (suc zero)))))) s5 (f zero) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b5)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (y))))) (τ-o (f (suc (suc (suc (suc zero))))) s4 (f zero) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b4)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-o (f (suc (suc (suc zero)))) s3 (f zero) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b3)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-o (f (suc (suc zero))) s2 (f zero) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b2)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-o (f (suc zero)) s1 (f zero) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b1)))) ((τ-p (f zero) s0))))))
  place (suc zero) = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (τ (f (suc (suc (suc (suc zero))))) s4 (y)))))) (τ-o (f (suc (suc (suc (suc (suc zero)))))) s5 (f (suc zero)) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b5)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (y))))) (τ-o (f (suc (suc (suc (suc zero))))) s4 (f (suc zero)) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b4)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-o (f (suc (suc (suc zero)))) s3 (f (suc zero)) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b3)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-o (f (suc (suc zero))) s2 (f (suc zero)) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b2)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-p (f (suc zero)) s1)) ((τ-o (f zero) s0 s1 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b1))) (sy (FinP.<⇒≢ o01))))))))
  place (suc (suc zero)) = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (τ (f (suc (suc (suc (suc zero))))) s4 (y)))))) (τ-o (f (suc (suc (suc (suc (suc zero)))))) s5 (f (suc (suc zero))) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (z≤n)))) b5)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (y))))) (τ-o (f (suc (suc (suc (suc zero))))) s4 (f (suc (suc zero))) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (z≤n)))) b4)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-o (f (suc (suc (suc zero)))) s3 (f (suc (suc zero))) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (z≤n)))) b3)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-p (f (suc (suc zero))) s2)) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-o (f (suc zero)) s1 s2 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b2))) (sy (FinP.<⇒≢ o12)))) ((τ-o (f zero) s0 s2 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b2))) (sy (FinP.<⇒≢ o02))))))))
  place (suc (suc (suc zero))) = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (τ (f (suc (suc (suc (suc zero))))) s4 (y)))))) (τ-o (f (suc (suc (suc (suc (suc zero)))))) s5 (f (suc (suc (suc zero)))) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (s≤s (z≤n))))) b5)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (y))))) (τ-o (f (suc (suc (suc (suc zero))))) s4 (f (suc (suc (suc zero)))) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (s≤s (z≤n))))) b4)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-p (f (suc (suc (suc zero)))) s3)) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-o (f (suc (suc zero))) s2 s3 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (z≤n)))) b3))) (sy (FinP.<⇒≢ o23)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-o (f (suc zero)) s1 s3 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b3))) (sy (FinP.<⇒≢ o13)))) ((τ-o (f zero) s0 s3 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b3))) (sy (FinP.<⇒≢ o03))))))))
  place (suc (suc (suc (suc zero)))) = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (τ (f (suc (suc (suc (suc zero))))) s4 (y)))))) (τ-o (f (suc (suc (suc (suc (suc zero)))))) s5 (f (suc (suc (suc (suc zero))))) (λ ()) (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) b5)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (y))))) (τ-p (f (suc (suc (suc (suc zero))))) s4)) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-o (f (suc (suc (suc zero)))) s3 s4 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (s≤s (z≤n))))) b4))) (sy (FinP.<⇒≢ o34)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-o (f (suc (suc zero))) s2 s4 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (z≤n)))) b4))) (sy (FinP.<⇒≢ o24)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-o (f (suc zero)) s1 s4 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b4))) (sy (FinP.<⇒≢ o14)))) ((τ-o (f zero) s0 s4 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b4))) (sy (FinP.<⇒≢ o04))))))))
  place (suc (suc (suc (suc (suc zero))))) = ≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (τ (f (suc (suc (suc (suc zero))))) s4 (y)))))) (τ-p (f (suc (suc (suc (suc (suc zero)))))) s5)) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (τ (f (suc (suc (suc zero)))) s3 (y))))) (τ-o (f (suc (suc (suc (suc zero))))) s4 s5 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) b5))) (sy (FinP.<⇒≢ o45)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (τ (f (suc (suc zero))) s2 (y)))) (τ-o (f (suc (suc (suc zero)))) s3 s5 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (s≤s (z≤n))))) b5))) (sy (FinP.<⇒≢ o35)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (τ (f (suc zero)) s1 (y))) (τ-o (f (suc (suc zero))) s2 s5 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (s≤s (z≤n)))) b5))) (sy (FinP.<⇒≢ o25)))) (≡.trans (≡.cong (λ y → τ (f zero) s0 (y)) (τ-o (f (suc zero)) s1 s5 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (s≤s (z≤n))) b5))) (sy (FinP.<⇒≢ o15)))) ((τ-o (f zero) s0 s5 (sy (lt⇒≢ (ℕP.<-≤-trans (s≤s (z≤n)) b5))) (sy (FinP.<⇒≢ o05))))))))

