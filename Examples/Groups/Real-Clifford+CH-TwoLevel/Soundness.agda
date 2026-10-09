------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the relations (Theorem 4.13): every relation of Figure 6
-- holds in Oₙ(ℤ[1/√2]).
--
-- The relations (b1)–(b6) say that generators with disjoint indices
-- commute, which holds for any indices (EmbedAction.comm-sound).  Each
-- of the others involves at most six indices in a known order, so it is
-- the image, under an increasing embedding, of the same relation in
-- dimension at most 6, where both sides are concrete matrices over
-- 𝔻[√2] and are compared by computation.  (d3) holds for both orders
-- of its indices b and c, and (d4) for all six interleavings of its
-- chains b < d and c < e, each checked separately.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Soundness where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ ; suc ; z≤n ; s≤s)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (recompute)

open import Word.Base

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Embedding
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Six indices in increasing order

emb₆ : (a b c d e f : Fin n) → a < b → b < c → c < d → d < e → e < f → Emb 6 n
emb₆ {n} a b c d e f ab bc cd de ef = record { ι = ι₆ ; mono = mono₆ }
  where
  ι₆ : Fin 6 → Fin n
  ι₆ zero = a
  ι₆ (suc zero) = b
  ι₆ (suc (suc zero)) = c
  ι₆ (suc (suc (suc zero))) = d
  ι₆ (suc (suc (suc (suc zero)))) = e
  ι₆ (suc (suc (suc (suc (suc zero))))) = f
  mono₆ : ∀ {x y : Fin 6} → x < y → ι₆ x < ι₆ y
  mono₆ {zero} {(suc zero)} _ = ab
  mono₆ {zero} {(suc (suc zero))} _ = FinP.<-trans ab bc
  mono₆ {zero} {(suc (suc (suc zero)))} _ = FinP.<-trans ab (FinP.<-trans bc cd)
  mono₆ {zero} {(suc (suc (suc (suc zero))))} _ = FinP.<-trans ab (FinP.<-trans bc (FinP.<-trans cd de))
  mono₆ {zero} {(suc (suc (suc (suc (suc zero)))))} _ = FinP.<-trans ab (FinP.<-trans bc (FinP.<-trans cd (FinP.<-trans de ef)))
  mono₆ {(suc zero)} {(suc (suc zero))} _ = bc
  mono₆ {(suc zero)} {(suc (suc (suc zero)))} _ = FinP.<-trans bc cd
  mono₆ {(suc zero)} {(suc (suc (suc (suc zero))))} _ = FinP.<-trans bc (FinP.<-trans cd de)
  mono₆ {(suc zero)} {(suc (suc (suc (suc (suc zero)))))} _ = FinP.<-trans bc (FinP.<-trans cd (FinP.<-trans de ef))
  mono₆ {(suc (suc zero))} {(suc (suc (suc zero)))} _ = cd
  mono₆ {(suc (suc zero))} {(suc (suc (suc (suc zero))))} _ = FinP.<-trans cd de
  mono₆ {(suc (suc zero))} {(suc (suc (suc (suc (suc zero)))))} _ = FinP.<-trans cd (FinP.<-trans de ef)
  mono₆ {(suc (suc (suc zero)))} {(suc (suc (suc (suc zero))))} _ = de
  mono₆ {(suc (suc (suc zero)))} {(suc (suc (suc (suc (suc zero)))))} _ = FinP.<-trans de ef
  mono₆ {(suc (suc (suc (suc zero))))} {(suc (suc (suc (suc (suc zero)))))} _ = ef
  mono₆ {zero} {zero} ()
  mono₆ {(suc zero)} {zero} ()
  mono₆ {(suc zero)} {(suc zero)} (s≤s ())
  mono₆ {(suc (suc zero))} {zero} ()
  mono₆ {(suc (suc zero))} {(suc zero)} (s≤s ())
  mono₆ {(suc (suc zero))} {(suc (suc zero))} (s≤s (s≤s ()))
  mono₆ {(suc (suc (suc zero)))} {zero} ()
  mono₆ {(suc (suc (suc zero)))} {(suc zero)} (s≤s ())
  mono₆ {(suc (suc (suc zero)))} {(suc (suc zero))} (s≤s (s≤s ()))
  mono₆ {(suc (suc (suc zero)))} {(suc (suc (suc zero)))} (s≤s (s≤s (s≤s ())))
  mono₆ {(suc (suc (suc (suc zero))))} {zero} ()
  mono₆ {(suc (suc (suc (suc zero))))} {(suc zero)} (s≤s ())
  mono₆ {(suc (suc (suc (suc zero))))} {(suc (suc zero))} (s≤s (s≤s ()))
  mono₆ {(suc (suc (suc (suc zero))))} {(suc (suc (suc zero)))} (s≤s (s≤s (s≤s ())))
  mono₆ {(suc (suc (suc (suc zero))))} {(suc (suc (suc (suc zero))))} (s≤s (s≤s (s≤s (s≤s ()))))
  mono₆ {(suc (suc (suc (suc (suc zero)))))} {zero} ()
  mono₆ {(suc (suc (suc (suc (suc zero)))))} {(suc zero)} (s≤s ())
  mono₆ {(suc (suc (suc (suc (suc zero)))))} {(suc (suc zero))} (s≤s (s≤s ()))
  mono₆ {(suc (suc (suc (suc (suc zero)))))} {(suc (suc (suc zero)))} (s≤s (s≤s (s≤s ())))
  mono₆ {(suc (suc (suc (suc (suc zero)))))} {(suc (suc (suc (suc zero))))} (s≤s (s≤s (s≤s (s≤s ()))))
  mono₆ {(suc (suc (suc (suc (suc zero)))))} {(suc (suc (suc (suc (suc zero)))))} (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

------------------------------------------------------------------------
-- Concrete indices

private
  f0¹ : Fin 1
  f0¹ = zero

private
  f0² f1² : Fin 2
  f0² = zero
  f1² = (suc zero)
  lt01² : f0² < f1²
  lt01² = s≤s z≤n

private
  f0³ f1³ f2³ : Fin 3
  f0³ = zero
  f1³ = (suc zero)
  f2³ = (suc (suc zero))
  lt01³ : f0³ < f1³
  lt01³ = s≤s z≤n
  lt02³ : f0³ < f2³
  lt02³ = s≤s z≤n
  lt12³ : f1³ < f2³
  lt12³ = s≤s (s≤s z≤n)

private
  f0⁴ f1⁴ f2⁴ f3⁴ : Fin 4
  f0⁴ = zero
  f1⁴ = (suc zero)
  f2⁴ = (suc (suc zero))
  f3⁴ = (suc (suc (suc zero)))
  lt01⁴ : f0⁴ < f1⁴
  lt01⁴ = s≤s z≤n
  lt02⁴ : f0⁴ < f2⁴
  lt02⁴ = s≤s z≤n
  lt03⁴ : f0⁴ < f3⁴
  lt03⁴ = s≤s z≤n
  lt12⁴ : f1⁴ < f2⁴
  lt12⁴ = s≤s (s≤s z≤n)
  lt13⁴ : f1⁴ < f3⁴
  lt13⁴ = s≤s (s≤s z≤n)
  lt23⁴ : f2⁴ < f3⁴
  lt23⁴ = s≤s (s≤s (s≤s z≤n))

private
  f0⁶ f1⁶ f2⁶ f3⁶ f4⁶ f5⁶ : Fin 6
  f0⁶ = zero
  f1⁶ = (suc zero)
  f2⁶ = (suc (suc zero))
  f3⁶ = (suc (suc (suc zero)))
  f4⁶ = (suc (suc (suc (suc zero))))
  f5⁶ = (suc (suc (suc (suc (suc zero)))))
  lt01⁶ : f0⁶ < f1⁶
  lt01⁶ = s≤s z≤n
  lt02⁶ : f0⁶ < f2⁶
  lt02⁶ = s≤s z≤n
  lt03⁶ : f0⁶ < f3⁶
  lt03⁶ = s≤s z≤n
  lt04⁶ : f0⁶ < f4⁶
  lt04⁶ = s≤s z≤n
  lt05⁶ : f0⁶ < f5⁶
  lt05⁶ = s≤s z≤n
  lt12⁶ : f1⁶ < f2⁶
  lt12⁶ = s≤s (s≤s z≤n)
  lt13⁶ : f1⁶ < f3⁶
  lt13⁶ = s≤s (s≤s z≤n)
  lt14⁶ : f1⁶ < f4⁶
  lt14⁶ = s≤s (s≤s z≤n)
  lt15⁶ : f1⁶ < f5⁶
  lt15⁶ = s≤s (s≤s z≤n)
  lt23⁶ : f2⁶ < f3⁶
  lt23⁶ = s≤s (s≤s (s≤s z≤n))
  lt24⁶ : f2⁶ < f4⁶
  lt24⁶ = s≤s (s≤s (s≤s z≤n))
  lt25⁶ : f2⁶ < f5⁶
  lt25⁶ = s≤s (s≤s (s≤s z≤n))
  lt34⁶ : f3⁶ < f4⁶
  lt34⁶ = s≤s (s≤s (s≤s (s≤s z≤n)))
  lt35⁶ : f3⁶ < f5⁶
  lt35⁶ = s≤s (s≤s (s≤s (s≤s z≤n)))
  lt45⁶ : f4⁶ < f5⁶
  lt45⁶ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

------------------------------------------------------------------------
-- The relations in dimension at most 6, checked by computation
--
-- The words are transparent, so that their embeddings compute; the
-- equations are proved in an opaque block that unfolds the action, the
-- vector updates and the arithmetic of 𝔻[√2], which the matrices of
-- concrete words compute through.

private
  l-a1 r-a1 : Word (Gen 1)
  l-a1 = Z f0¹ • Z f0¹
  r-a1 = ε
  l-a2 r-a2 : Word (Gen 2)
  l-a2 = X f0² f1² lt01² • X f0² f1² lt01²
  r-a2 = ε
  l-a3 r-a3 : Word (Gen 2)
  l-a3 = H f0² f1² lt01² • H f0² f1² lt01²
  r-a3 = ε
  l-c1 r-c1 : Word (Gen 2)
  l-c1 = Z f0² • X f0² f1² lt01²
  r-c1 = X f0² f1² lt01² • Z f1²
  l-c2 r-c2 : Word (Gen 3)
  l-c2 = X f1³ f2³ lt12³ • X f0³ f1³ lt01³
  r-c2 = X f0³ f1³ lt01³ • X f0³ f2³ lt02³
  l-c3 r-c3 : Word (Gen 3)
  l-c3 = X f0³ f2³ lt02³ • X f1³ f2³ lt12³
  r-c3 = X f1³ f2³ lt12³ • X f0³ f1³ lt01³
  l-c4 r-c4 : Word (Gen 3)
  l-c4 = H f1³ f2³ lt12³ • X f0³ f1³ lt01³
  r-c4 = X f0³ f1³ lt01³ • H f0³ f2³ lt02³
  l-c5 r-c5 : Word (Gen 3)
  l-c5 = H f0³ f2³ lt02³ • X f1³ f2³ lt12³
  r-c5 = X f1³ f2³ lt12³ • H f0³ f1³ lt01³
  l-d1 r-d1 : Word (Gen 2)
  l-d1 = Z f0² • Z f1² • H f0² f1² lt01²
  r-d1 = H f0² f1² lt01² • Z f0² • Z f1²
  l-d2 r-d2 : Word (Gen 2)
  l-d2 = Z f1² • H f0² f1² lt01²
  r-d2 = H f0² f1² lt01² • X f0² f1² lt01²
  l-d3-abcd r-d3-abcd : Word (Gen 4)
  l-d3-abcd = H f2⁴ f3⁴ lt23⁴ • H f0⁴ f2⁴ lt02⁴ • H f1⁴ f3⁴ lt13⁴ • H f2⁴ f3⁴ lt23⁴ • H f0⁴ f2⁴ lt02⁴ • H f1⁴ f3⁴ lt13⁴ • H f2⁴ f3⁴ lt23⁴ • H f0⁴ f2⁴ lt02⁴ • H f1⁴ f3⁴ lt13⁴ • H f2⁴ f3⁴ lt23⁴ • H f0⁴ f2⁴ lt02⁴ • H f1⁴ f3⁴ lt13⁴
  r-d3-abcd = H f0⁴ f1⁴ lt01⁴ • H f2⁴ f3⁴ lt23⁴
  l-d3-acbd r-d3-acbd : Word (Gen 4)
  l-d3-acbd = H f1⁴ f3⁴ lt13⁴ • H f0⁴ f1⁴ lt01⁴ • H f2⁴ f3⁴ lt23⁴ • H f1⁴ f3⁴ lt13⁴ • H f0⁴ f1⁴ lt01⁴ • H f2⁴ f3⁴ lt23⁴ • H f1⁴ f3⁴ lt13⁴ • H f0⁴ f1⁴ lt01⁴ • H f2⁴ f3⁴ lt23⁴ • H f1⁴ f3⁴ lt13⁴ • H f0⁴ f1⁴ lt01⁴ • H f2⁴ f3⁴ lt23⁴
  r-d3-acbd = H f0⁴ f2⁴ lt02⁴ • H f1⁴ f3⁴ lt13⁴
  l-d4-abdcef r-d4-abdcef : Word (Gen 6)
  l-d4-abdcef = H f0⁶ f3⁶ lt03⁶ • H f1⁶ f2⁶ lt12⁶ • H f0⁶ f1⁶ lt01⁶ • H f0⁶ f3⁶ lt03⁶ • H f1⁶ f2⁶ lt12⁶ • X f3⁶ f4⁶ lt34⁶ • X f2⁶ f5⁶ lt25⁶ • H f0⁶ f3⁶ lt03⁶ • H f1⁶ f2⁶ lt12⁶ • H f0⁶ f1⁶ lt01⁶ • H f0⁶ f3⁶ lt03⁶ • H f1⁶ f2⁶ lt12⁶ • X f3⁶ f4⁶ lt34⁶ • X f2⁶ f5⁶ lt25⁶ • H f0⁶ f3⁶ lt03⁶ • H f1⁶ f2⁶ lt12⁶ • H f0⁶ f1⁶ lt01⁶ • H f0⁶ f3⁶ lt03⁶ • H f1⁶ f2⁶ lt12⁶ • X f3⁶ f4⁶ lt34⁶ • X f2⁶ f5⁶ lt25⁶
  r-d4-abdcef = H f3⁶ f4⁶ lt34⁶ • H f2⁶ f5⁶ lt25⁶ • H f4⁶ f5⁶ lt45⁶ • H f3⁶ f4⁶ lt34⁶ • H f2⁶ f5⁶ lt25⁶ • X f3⁶ f4⁶ lt34⁶ • X f2⁶ f5⁶ lt25⁶
  l-d4-abcdef r-d4-abcdef : Word (Gen 6)
  l-d4-abcdef = H f0⁶ f2⁶ lt02⁶ • H f1⁶ f3⁶ lt13⁶ • H f0⁶ f1⁶ lt01⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f3⁶ lt13⁶ • X f2⁶ f4⁶ lt24⁶ • X f3⁶ f5⁶ lt35⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f3⁶ lt13⁶ • H f0⁶ f1⁶ lt01⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f3⁶ lt13⁶ • X f2⁶ f4⁶ lt24⁶ • X f3⁶ f5⁶ lt35⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f3⁶ lt13⁶ • H f0⁶ f1⁶ lt01⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f3⁶ lt13⁶ • X f2⁶ f4⁶ lt24⁶ • X f3⁶ f5⁶ lt35⁶
  r-d4-abcdef = H f2⁶ f4⁶ lt24⁶ • H f3⁶ f5⁶ lt35⁶ • H f4⁶ f5⁶ lt45⁶ • H f2⁶ f4⁶ lt24⁶ • H f3⁶ f5⁶ lt35⁶ • X f2⁶ f4⁶ lt24⁶ • X f3⁶ f5⁶ lt35⁶
  l-d4-abcedf r-d4-abcedf : Word (Gen 6)
  l-d4-abcedf = H f0⁶ f2⁶ lt02⁶ • H f1⁶ f4⁶ lt14⁶ • H f0⁶ f1⁶ lt01⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f4⁶ lt14⁶ • X f2⁶ f3⁶ lt23⁶ • X f4⁶ f5⁶ lt45⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f4⁶ lt14⁶ • H f0⁶ f1⁶ lt01⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f4⁶ lt14⁶ • X f2⁶ f3⁶ lt23⁶ • X f4⁶ f5⁶ lt45⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f4⁶ lt14⁶ • H f0⁶ f1⁶ lt01⁶ • H f0⁶ f2⁶ lt02⁶ • H f1⁶ f4⁶ lt14⁶ • X f2⁶ f3⁶ lt23⁶ • X f4⁶ f5⁶ lt45⁶
  r-d4-abcedf = H f2⁶ f3⁶ lt23⁶ • H f4⁶ f5⁶ lt45⁶ • H f3⁶ f5⁶ lt35⁶ • H f2⁶ f3⁶ lt23⁶ • H f4⁶ f5⁶ lt45⁶ • X f2⁶ f3⁶ lt23⁶ • X f4⁶ f5⁶ lt45⁶
  l-d4-acbdef r-d4-acbdef : Word (Gen 6)
  l-d4-acbdef = H f0⁶ f1⁶ lt01⁶ • H f2⁶ f3⁶ lt23⁶ • H f0⁶ f2⁶ lt02⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f3⁶ lt23⁶ • X f1⁶ f4⁶ lt14⁶ • X f3⁶ f5⁶ lt35⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f3⁶ lt23⁶ • H f0⁶ f2⁶ lt02⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f3⁶ lt23⁶ • X f1⁶ f4⁶ lt14⁶ • X f3⁶ f5⁶ lt35⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f3⁶ lt23⁶ • H f0⁶ f2⁶ lt02⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f3⁶ lt23⁶ • X f1⁶ f4⁶ lt14⁶ • X f3⁶ f5⁶ lt35⁶
  r-d4-acbdef = H f1⁶ f4⁶ lt14⁶ • H f3⁶ f5⁶ lt35⁶ • H f4⁶ f5⁶ lt45⁶ • H f1⁶ f4⁶ lt14⁶ • H f3⁶ f5⁶ lt35⁶ • X f1⁶ f4⁶ lt14⁶ • X f3⁶ f5⁶ lt35⁶
  l-d4-acbedf r-d4-acbedf : Word (Gen 6)
  l-d4-acbedf = H f0⁶ f1⁶ lt01⁶ • H f2⁶ f4⁶ lt24⁶ • H f0⁶ f2⁶ lt02⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f4⁶ lt24⁶ • X f1⁶ f3⁶ lt13⁶ • X f4⁶ f5⁶ lt45⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f4⁶ lt24⁶ • H f0⁶ f2⁶ lt02⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f4⁶ lt24⁶ • X f1⁶ f3⁶ lt13⁶ • X f4⁶ f5⁶ lt45⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f4⁶ lt24⁶ • H f0⁶ f2⁶ lt02⁶ • H f0⁶ f1⁶ lt01⁶ • H f2⁶ f4⁶ lt24⁶ • X f1⁶ f3⁶ lt13⁶ • X f4⁶ f5⁶ lt45⁶
  r-d4-acbedf = H f1⁶ f3⁶ lt13⁶ • H f4⁶ f5⁶ lt45⁶ • H f3⁶ f5⁶ lt35⁶ • H f1⁶ f3⁶ lt13⁶ • H f4⁶ f5⁶ lt45⁶ • X f1⁶ f3⁶ lt13⁶ • X f4⁶ f5⁶ lt45⁶
  l-d4-acebdf r-d4-acebdf : Word (Gen 6)
  l-d4-acebdf = H f0⁶ f1⁶ lt01⁶ • H f3⁶ f4⁶ lt34⁶ • H f0⁶ f3⁶ lt03⁶ • H f0⁶ f1⁶ lt01⁶ • H f3⁶ f4⁶ lt34⁶ • X f1⁶ f2⁶ lt12⁶ • X f4⁶ f5⁶ lt45⁶ • H f0⁶ f1⁶ lt01⁶ • H f3⁶ f4⁶ lt34⁶ • H f0⁶ f3⁶ lt03⁶ • H f0⁶ f1⁶ lt01⁶ • H f3⁶ f4⁶ lt34⁶ • X f1⁶ f2⁶ lt12⁶ • X f4⁶ f5⁶ lt45⁶ • H f0⁶ f1⁶ lt01⁶ • H f3⁶ f4⁶ lt34⁶ • H f0⁶ f3⁶ lt03⁶ • H f0⁶ f1⁶ lt01⁶ • H f3⁶ f4⁶ lt34⁶ • X f1⁶ f2⁶ lt12⁶ • X f4⁶ f5⁶ lt45⁶
  r-d4-acebdf = H f1⁶ f2⁶ lt12⁶ • H f4⁶ f5⁶ lt45⁶ • H f2⁶ f5⁶ lt25⁶ • H f1⁶ f2⁶ lt12⁶ • H f4⁶ f5⁶ lt45⁶ • X f1⁶ f2⁶ lt12⁶ • X f4⁶ f5⁶ lt45⁶

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  private
    m-a1 : ⟦ l-a1 ⟧ᵐ ≡ ⟦ r-a1 ⟧ᵐ
    m-a1 = refl

    m-a2 : ⟦ l-a2 ⟧ᵐ ≡ ⟦ r-a2 ⟧ᵐ
    m-a2 = refl

    m-a3 : ⟦ l-a3 ⟧ᵐ ≡ ⟦ r-a3 ⟧ᵐ
    m-a3 = refl

    m-c1 : ⟦ l-c1 ⟧ᵐ ≡ ⟦ r-c1 ⟧ᵐ
    m-c1 = refl

    m-c2 : ⟦ l-c2 ⟧ᵐ ≡ ⟦ r-c2 ⟧ᵐ
    m-c2 = refl

    m-c3 : ⟦ l-c3 ⟧ᵐ ≡ ⟦ r-c3 ⟧ᵐ
    m-c3 = refl

    m-c4 : ⟦ l-c4 ⟧ᵐ ≡ ⟦ r-c4 ⟧ᵐ
    m-c4 = refl

    m-c5 : ⟦ l-c5 ⟧ᵐ ≡ ⟦ r-c5 ⟧ᵐ
    m-c5 = refl

    m-d1 : ⟦ l-d1 ⟧ᵐ ≡ ⟦ r-d1 ⟧ᵐ
    m-d1 = refl

    m-d2 : ⟦ l-d2 ⟧ᵐ ≡ ⟦ r-d2 ⟧ᵐ
    m-d2 = refl

    m-d3-abcd : ⟦ l-d3-abcd ⟧ᵐ ≡ ⟦ r-d3-abcd ⟧ᵐ
    m-d3-abcd = refl

    m-d3-acbd : ⟦ l-d3-acbd ⟧ᵐ ≡ ⟦ r-d3-acbd ⟧ᵐ
    m-d3-acbd = refl

    m-d4-abdcef : ⟦ l-d4-abdcef ⟧ᵐ ≡ ⟦ r-d4-abdcef ⟧ᵐ
    m-d4-abdcef = refl

    m-d4-abcdef : ⟦ l-d4-abcdef ⟧ᵐ ≡ ⟦ r-d4-abcdef ⟧ᵐ
    m-d4-abcdef = refl

    m-d4-abcedf : ⟦ l-d4-abcedf ⟧ᵐ ≡ ⟦ r-d4-abcedf ⟧ᵐ
    m-d4-abcedf = refl

    m-d4-acbdef : ⟦ l-d4-acbdef ⟧ᵐ ≡ ⟦ r-d4-acbdef ⟧ᵐ
    m-d4-acbdef = refl

    m-d4-acbedf : ⟦ l-d4-acbedf ⟧ᵐ ≡ ⟦ r-d4-acbedf ⟧ᵐ
    m-d4-acbedf = refl

    m-d4-acebdf : ⟦ l-d4-acebdf ⟧ᵐ ≡ ⟦ r-d4-acebdf ⟧ᵐ
    m-d4-acebdf = refl

------------------------------------------------------------------------
-- Soundness of the axioms

-- Relevant proofs of order, recomputed from irrelevant ones.
private
  rc : {a b : Fin n} → .(a < b) → a < b
  rc {a = a} {b} p = recompute (a FinP.<? b) p

sound-axiom : {w v : Word (Gen n)} → w === v → ⟦ w ⟧ᵐ ≡ ⟦ v ⟧ᵐ
sound-axiom (a1 {a = a}) = emb-sound (emb₁ a) l-a1 r-a1 m-a1
sound-axiom (a2 {a = a} {b = b} p) = emb-sound (emb₂ a b (rc p)) l-a2 r-a2 m-a2
sound-axiom (a3 {a = a} {b = b} p) = emb-sound (emb₂ a b (rc p)) l-a3 r-a3 m-a3
sound-axiom (b1 {a = a} {b = b} ab) =
  comm-sound (Z-gen a) (Z-gen b) λ { x i-a i-a → ab refl }
sound-axiom (b2 {b = b} {c = c} {a = a} p ab ac) =
  comm-sound (Z-gen a) (X-gen b c p) λ { x i-a X-a → ab refl ; x i-a X-b → ac refl }
sound-axiom (b3 {a = a} {b = b} {c = c} {d = d} p q ac ad bc bd) =
  comm-sound (X-gen a b p) (X-gen c d q)
    λ { x X-a X-a → ac refl ; x X-a X-b → ad refl ; x X-b X-a → bc refl ; x X-b X-b → bd refl }
sound-axiom (b4 {b = b} {c = c} {a = a} p ab ac) =
  comm-sound (Z-gen a) (H-gen b c p) λ { x i-a K-a → ab refl ; x i-a K-b → ac refl }
sound-axiom (b5 {a = a} {b = b} {c = c} {d = d} p q ac ad bc bd) =
  comm-sound (X-gen a b p) (H-gen c d q)
    λ { x X-a K-a → ac refl ; x X-a K-b → ad refl ; x X-b K-a → bc refl ; x X-b K-b → bd refl }
sound-axiom (b6 {a = a} {b = b} {c = c} {d = d} p q ac ad bc bd) =
  comm-sound (H-gen a b p) (H-gen c d q)
    λ { x K-a K-a → ac refl ; x K-a K-b → ad refl ; x K-b K-a → bc refl ; x K-b K-b → bd refl }
sound-axiom (c1 {a = a} {b = b} p) = emb-sound (emb₂ a b (rc p)) l-c1 r-c1 m-c1
sound-axiom (c2 {a = a} {b = b} {c = c} p q) = emb-sound (emb₃ a b c p q) l-c2 r-c2 m-c2
sound-axiom (c3 {a = a} {b = b} {c = c} p q) = emb-sound (emb₃ a b c p q) l-c3 r-c3 m-c3
sound-axiom (c4 {a = a} {b = b} {c = c} p q) = emb-sound (emb₃ a b c p q) l-c4 r-c4 m-c4
sound-axiom (c5 {a = a} {b = b} {c = c} p q) = emb-sound (emb₃ a b c p q) l-c5 r-c5 m-c5
sound-axiom (d1 {a = a} {b = b} p) = emb-sound (emb₂ a b (rc p)) l-d1 r-d1 m-d1
sound-axiom (d2 {a = a} {b = b} p) = emb-sound (emb₂ a b (rc p)) l-d2 r-d2 m-d2
sound-axiom (d3 {a = a} {b = b} {c = c} {d = d} ab ac bd cd b≢c) with FinP.<-cmp b c
... | tri< b<c _ _ = emb-sound (emb₄ a b c d ab b<c cd) l-d3-abcd r-d3-abcd m-d3-abcd
... | tri≈ _ b≡c _ = ⊥-elim (b≢c b≡c)
... | tri> _ _ c<b = emb-sound (emb₄ a c b d ac c<b bd) l-d3-acbd r-d3-acbd m-d3-acbd
sound-axiom (d4 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} ab ac bd ce df ef b≢c b≢e d≢c d≢e)
  with FinP.<-cmp d c | FinP.<-cmp e b | FinP.<-cmp b c | FinP.<-cmp d e
... | tri< d<c _ _ | _ | _ | _ =
  emb-sound (emb₆ a b d c e f ab bd d<c ce ef) l-d4-abdcef r-d4-abdcef m-d4-abdcef
... | tri≈ _ d≡c _ | _ | _ | _ = ⊥-elim (d≢c d≡c)
... | tri> _ _ c<d | tri< e<b _ _ | _ | _ =
  emb-sound (emb₆ a c e b d f ac ce e<b bd df) l-d4-acebdf r-d4-acebdf m-d4-acebdf
... | tri> _ _ c<d | tri≈ _ e≡b _ | _ | _ = ⊥-elim (b≢e (sym e≡b))
... | tri> _ _ c<d | tri> _ _ b<e | tri< b<c _ _ | tri< d<e _ _ =
  emb-sound (emb₆ a b c d e f ab b<c c<d d<e ef) l-d4-abcdef r-d4-abcdef m-d4-abcdef
... | tri> _ _ c<d | tri> _ _ b<e | tri< b<c _ _ | tri> _ _ e<d =
  emb-sound (emb₆ a b c e d f ab b<c ce e<d df) l-d4-abcedf r-d4-abcedf m-d4-abcedf
... | tri> _ _ c<d | tri> _ _ b<e | tri> _ _ c<b | tri< d<e _ _ =
  emb-sound (emb₆ a c b d e f ac c<b bd d<e ef) l-d4-acbdef r-d4-acbdef m-d4-acbdef
... | tri> _ _ c<d | tri> _ _ b<e | tri> _ _ c<b | tri> _ _ e<d =
  emb-sound (emb₆ a c b e d f ac c<b b<e e<d df) l-d4-acbedf r-d4-acbedf m-d4-acbedf
... | tri> _ _ c<d | tri> _ _ b<e | tri≈ _ b≡c _ | _ = ⊥-elim (b≢c b≡c)
... | tri> _ _ c<d | tri> _ _ b<e | _ | tri≈ _ d≡e _ = ⊥-elim (d≢e d≡e)
