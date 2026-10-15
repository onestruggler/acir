------------------------------------------------------------------------
-- Presentations of groups
--
-- Exactly four cosets of the physical H group in the scaled ambient
-- group, at every width at least four.  Every ambient word factors as
-- an H circuit followed by one of four dyadic representatives.  The
-- representative's state is unique, with exact matrix equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.AmbientCosets (n : ℕ) where

open import Data.Nat.Base using (_*_ ; _<_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Product.Base using (Σ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; _•_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)
import Presentation.Base as PB
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.GeneralN.Semantics as Sem
import Examples.Groups.CCX+H.GeneralN.Generation as Generation
import Examples.Groups.CCX+H.GeneralN.DihedralQuotient as Q
import Examples.Groups.CCX+H.GeneralN.DihedralKernel as Kernel
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
open import Examples.Groups.CCX+H.GeneralN.Action using (Coset ; c00 ; c10 ; c11 ; c01)

width = 4 + n
k = 2 ^ℕ (3 + n)
N = k * 2
module C = Sem.At (3 + n)
module G = Generation n
module K = Kernel n
module M = S.Dim k
module Source = Q.SourceGroup N
private module A = PB (T._===ᴸ_ {N})

private
  positive : 0 < k
  positive = NP.m^n>0 2 (3 + n)

  translation : Coset → Q.D8
  translation c00 = Q.q00
  translation c10 = Q.q10
  translation c11 = Q.q11
  translation c01 = Q.q01

  translation-state : ∀ c → Q.act c00 (translation c) ≡ c
  translation-state c00 = Eq.refl
  translation-state c10 = Eq.refl
  translation-state c11 = Eq.refl
  translation-state c01 = Eq.refl

  reset : ∀ q → Q.act c00 (Q._·_ q (Q.inverse (translation (Q.act c00 q)))) ≡ c00
  reset Q.q00 = Eq.refl
  reset Q.q10 = Eq.refl
  reset Q.q11 = Eq.refl
  reset Q.q01 = Eq.refl
  reset Q.h00 = Eq.refl
  reset Q.h10 = Eq.refl
  reset Q.h11 = Eq.refl
  reset Q.h01 = Eq.refl

state : Word (T.Genᴸ N) → Coset
state w = Q.act c00 (Q.quotient w)

representative : Coset → Word (T.Genᴸ N)
representative c = K.representative (translation c)

representative-correct : ∀ c → Q.quotient (representative c) ≡ translation c
representative-correct c = K.representative-correct (translation c)

representative-state : ∀ c → state (representative c) ≡ c
representative-state c = Eq.trans (Eq.cong (Q.act c00) (representative-correct c))
  (translation-state c)

record Decomposition (w : Word (T.Genᴸ N)) : Set where
  field
    body : H.Circuit width
    coset : Coset
    correct : C.interpret body ·*· M.⟦ representative coset ⟧ᴸ ≡ M.⟦ w ⟧ᴸ

decompose : ∀ w → Decomposition w
decompose w = finish (G.generated remainder closed)
  where
  q = Q.quotient w
  rep = representative (state w)
  remainder = w • Source.G._⁻¹ rep

  closed : G.Auxiliary.state c00 remainder ≡ c00
  closed = Eq.trans (Eq.sym (Q.correct c00 remainder))
    (Eq.trans (Eq.cong (λ r → Q.act c00 (Q._·_ q r))
      (Eq.trans (Source.inverse-correct rep)
        (Eq.cong Q.inverse (representative-correct (state w))))) (reset q))

  factor : (remainder • rep) A.≈ w
  factor = A.trans A.assoc
    (A.trans (A.cong A.refl (Source.G.inverseˡ {g = rep})) A.right-unit)

  finish : (Σ (H.Circuit width) λ c → C.interpret c ≡ M.⟦ remainder ⟧ᴸ) →
    Decomposition w
  finish (c , eq) = record
    { body = c
    ; coset = state w
    ; correct = Eq.trans (Eq.cong (_·*· M.⟦ rep ⟧ᴸ) eq)
        (Eq.trans (Eq.sym (M.⟦•⟧ᴸ remainder rep)) (S.soundness k factor))
    }

private
  compiled-closed : ∀ (c : H.Circuit width) → state (C.compile c) ≡ c00
  compiled-closed c = Eq.trans (Q.correct c00 (C.compile c))
    (G.necessary (C.compile c) c (Eq.sym (C.encoding-correct c)))

  component : ∀ (u : H.Circuit width) c →
    state (C.compile u • representative c) ≡ c
  component u c = Eq.trans
    (Q.act-product (Q.quotient (C.compile u)) (Q.quotient (representative c)) c00)
    (Eq.trans (Eq.cong (λ d → Q.act d (Q.quotient (representative c))) (compiled-closed u))
      (representative-state c))

  matrix : ∀ (u : H.Circuit width) c →
    M.⟦ C.compile u • representative c ⟧ᴸ ≡
      C.interpret u ·*· M.⟦ representative c ⟧ᴸ
  matrix u c = Eq.trans (M.⟦•⟧ᴸ (C.compile u) (representative c))
    (Eq.cong (_·*· M.⟦ representative c ⟧ᴸ) (C.encoding-correct u))

-- Equality after multiplication by any physical H circuits still
-- forces the same representative.  All four states occur above.
coset-unique : ∀ (u v : H.Circuit width) c d →
  C.interpret u ·*· M.⟦ representative c ⟧ᴸ ≡
    C.interpret v ·*· M.⟦ representative d ⟧ᴸ → c ≡ d
coset-unique u v c d eq = Eq.trans (Eq.sym (component u c))
  (Eq.trans (Eq.cong (Q.act c00) (Q.semantic k positive
    {u = C.compile u • representative c} {v = C.compile v • representative d}
    (Eq.trans (matrix u c) (Eq.trans eq (Eq.sym (matrix v d)))))) (component v d))

representative-injective : ∀ c d →
  M.⟦ representative c ⟧ᴸ ≡ M.⟦ representative d ⟧ᴸ → c ≡ d
representative-injective c d eq = Eq.trans (Eq.sym (representative-state c))
  (Eq.trans (Eq.cong (Q.act c00) (Q.semantic k positive
    {u = representative c} {v = representative d} eq)) (representative-state d))
