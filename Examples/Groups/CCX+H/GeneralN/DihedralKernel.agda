------------------------------------------------------------------------
-- Presentations of groups
--
-- The physical HH image is exactly the kernel of the scaled ambient
-- D8 quotient.  The physical H image is the preimage of its order-two
-- reflection subgroup.  Both descriptions include circuit synthesis.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.DihedralKernel (n : ℕ) where

open import Data.Nat.Base using (_*_ ; _<_ ; s≤s ; z≤n) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Fin.Base using (Fin ; fromℕ< ; toℕ)
import Data.Fin.Properties as FP
open import Data.Bool.Base using (false)
open import Data.Product.Base using (Σ ; _,_)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; _•_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)
import Presentation.Base as PB
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.GeneralN.Semantics as Sem
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as Physical
import Examples.Groups.CCX+H.GeneralN.Generation as Generation
import Examples.Groups.CCX+H.GeneralN.HadamardDecomposition as Decomposition
import Examples.Groups.CCX+H.GeneralN.HadamardEmbedding as Embed
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity
import Examples.Groups.CCX+H.GeneralN.DihedralQuotient as Q
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
open import Examples.Groups.CCX+H.GeneralN.Action using (c00)

width = 4 + n
k = 2 ^ℕ (3 + n)
N = k * 2
module C = Sem.At (3 + n)
module G = Generation n
module D = Decomposition n
module M = S.Dim k
module Source = Q.SourceGroup N

private
  dimension : 2 ^ℕ width ≡ N
  dimension = NP.*-comm 2 k

  positive : 0 < k
  positive = NP.m^n>0 2 (3 + n)

  first-bound : 0 < N
  first-bound = Eq.subst (0 <_) dimension (NP.m^n>0 2 width)

  second-bound : 1 < N
  second-bound = Eq.subst (1 <_) dimension (NP.^-monoʳ-≤ 2 {1} {width} (s≤s z≤n))

  first second : Fin N
  first = fromℕ< first-bound
  second = fromℕ< second-bound

  ordered : toℕ first < toℕ second
  ordered = Eq.subst₂ _<_ (Eq.sym (FP.toℕ-fromℕ< first-bound))
    (Eq.sym (FP.toℕ-fromℕ< second-bound)) (s≤s z≤n)

  module Reps = Q.Section first second ordered
  module A = PB (T._===ᴸ_ {N})

representative : Q.D8 → Word (T.Genᴸ N)
representative = Reps.section

representative-correct : ∀ q → Q.quotient (representative q) ≡ q
representative-correct = Reps.section-correct

-- Exact equality to an embedded HH circuit forces the identity in D8.
necessary : ∀ w (u : HH.Circuit width) →
  C.interpret (Embed.embed u) ≡ M.⟦ w ⟧ᴸ → Q.quotient w ≡ Q.q00
necessary w u eq = Q.kernel-from-closed-even w
  (G.necessary w (Embed.embed u) eq) even
  where
  even : Parity.source-parity w ≡ false
  even = Eq.trans
    (Eq.sym (Parity.source-semantic k positive
      {u = C.compile (Embed.embed u)} {v = w}
      (Eq.trans (C.encoding-correct (Embed.embed u)) eq)))
    (Eq.trans (Parity.compiled (3 + n) (Embed.embed u)) (Parity.expanded u))

-- Conversely every kernel word is synthesized into an actual HH
-- circuit on these same wires.  The first synthesis gives an H circuit;
-- quotient parity proves it even and the proved decomposition removes H.
generated : ∀ w → Q.quotient w ≡ Q.q00 →
  Σ (HH.Circuit width) λ u → C.interpret (Embed.embed u) ≡ M.⟦ w ⟧ᴸ
generated w kernel = finish (D.even-body circuit even)
  where
  closed : G.Auxiliary.state c00 w ≡ c00
  closed = Q.kernel-action w kernel c00

  circuit : H.Circuit width
  circuit = G.synthesize w

  correct : C.interpret circuit ≡ M.⟦ w ⟧ᴸ
  correct = G.correct w closed

  even : Parity.parity circuit ≡ false
  even = Eq.trans (Eq.sym (Parity.compiled (3 + n) circuit))
    (Eq.trans (Parity.source-semantic k positive {u = C.compile circuit} {v = w}
      (Eq.trans (C.encoding-correct circuit) correct))
      (Eq.trans (Eq.sym (Q.parity-correct w)) (Eq.cong Q.odd kernel)))

  finish : (Σ (HH.Circuit width) λ u → width P.⊢ circuit ≈ Embed.embed u) →
    Σ (HH.Circuit width) λ u → C.interpret (Embed.embed u) ≡ M.⟦ w ⟧ᴸ
  finish (u , eq) = u , Eq.trans
    (Eq.sym (Physical.At.backward (3 + n) {circuit} {Embed.embed u} (P.sound width eq)))
    correct

physical-necessary : ∀ w (u : HH.Circuit width) →
  Physical.interpret (Embed.embed u) ≡ Physical.cast-matrix (Eq.sym dimension) M.⟦ w ⟧ᴸ →
  Q.quotient w ≡ Q.q00
physical-necessary w u eq = necessary w u
  (Physical.cast-injective (Eq.sym dimension)
    (Eq.trans (Physical.At.correct (3 + n) (Embed.embed u)) eq))

physical-generated : ∀ w → Q.quotient w ≡ Q.q00 →
  Σ (HH.Circuit width) λ u →
    Physical.interpret (Embed.embed u) ≡ Physical.cast-matrix (Eq.sym dimension) M.⟦ w ⟧ᴸ
physical-generated w kernel = finish (generated w kernel)
  where
  finish : (Σ (HH.Circuit width) λ u → C.interpret (Embed.embed u) ≡ M.⟦ w ⟧ᴸ) →
    Σ (HH.Circuit width) λ u →
      Physical.interpret (Embed.embed u) ≡ Physical.cast-matrix (Eq.sym dimension) M.⟦ w ⟧ᴸ
  finish (u , eq) = u , Eq.trans (Eq.sym (Physical.At.correct (3 + n) (Embed.embed u)))
    (Eq.cong (Physical.cast-matrix (Eq.sym dimension)) eq)

-- The H image is the full preimage of {identity, reflection} in D8.
H-necessary : ∀ w (c : H.Circuit width) → C.interpret c ≡ M.⟦ w ⟧ᴸ →
  Q.quotient w ≡ Q.q00 ⊎ Q.quotient w ≡ Q.h00
H-necessary w c eq = Q.stabilizer (Q.quotient w)
  (Eq.trans (Q.correct c00 w) (G.necessary w c eq))

H-generated : ∀ w → Q.quotient w ≡ Q.q00 ⊎ Q.quotient w ≡ Q.h00 →
  Σ (H.Circuit width) λ c → C.interpret c ≡ M.⟦ w ⟧ᴸ
H-generated w member = G.generated w
  (Eq.trans (Eq.sym (Q.correct c00 w)) (Q.stabilizer-state (Q.quotient w) member))

-- Normality in the full scaled ambient group, with a circuit witness
-- for the conjugate by every ambient word.
normal-generated : ∀ a w (u : HH.Circuit width) →
  C.interpret (Embed.embed u) ≡ M.⟦ w ⟧ᴸ →
  Σ (HH.Circuit width) λ v →
    C.interpret (Embed.embed v) ≡ M.⟦ (a • w) • Source.G._⁻¹ a ⟧ᴸ
normal-generated a w u eq = generated ((a • w) • Source.G._⁻¹ a)
  (Source.kernel-conjugate a w (necessary w u eq))

-- There are exactly eight HH cosets in the scaled ambient group.
record CosetDecomposition (w : Word (T.Genᴸ N)) : Set where
  field
    body : HH.Circuit width
    coset : Q.D8
    correct : C.interpret (Embed.embed body) ·*· M.⟦ representative coset ⟧ᴸ ≡ M.⟦ w ⟧ᴸ

decompose : ∀ w → CosetDecomposition w
decompose w = finish (generated remainder kernel)
  where
  q = Q.quotient w
  rep = representative q
  remainder = w • Source.G._⁻¹ rep

  kernel : Q.quotient remainder ≡ Q.q00
  kernel = Eq.trans
    (Eq.cong (Q._·_ q)
      (Eq.trans (Source.inverse-correct rep) (Eq.cong Q.inverse (representative-correct q))))
    (Q.inverseʳ q)

  factor : (remainder • rep) A.≈ w
  factor = A.trans A.assoc
    (A.trans (A.cong A.refl (Source.G.inverseˡ {g = rep})) A.right-unit)

  finish : (Σ (HH.Circuit width) λ u → C.interpret (Embed.embed u) ≡ M.⟦ remainder ⟧ᴸ) →
    CosetDecomposition w
  finish (u , eq) = record
    { body = u
    ; coset = q
    ; correct = Eq.trans (Eq.cong (_·*· M.⟦ rep ⟧ᴸ) eq)
        (Eq.trans (Eq.sym (M.⟦•⟧ᴸ remainder rep)) (S.soundness k factor))
    }

coset-unique : ∀ (u v : HH.Circuit width) q r →
  C.interpret (Embed.embed u) ·*· M.⟦ representative q ⟧ᴸ ≡
    C.interpret (Embed.embed v) ·*· M.⟦ representative r ⟧ᴸ → q ≡ r
coset-unique u v q r eq = Eq.trans (Eq.sym (component u q))
  (Eq.trans (Q.semantic k positive
    {u = C.compile (Embed.embed u) • representative q}
    {v = C.compile (Embed.embed v) • representative r}
    (Eq.trans (matrix u q) (Eq.trans eq (Eq.sym (matrix v r))))) (component v r))
  where
  component : ∀ (u : HH.Circuit width) q →
    Q.quotient (C.compile (Embed.embed u) • representative q) ≡ q
  component u q = Eq.trans
    (Eq.cong₂ Q._·_ (necessary (C.compile (Embed.embed u)) u
      (Eq.sym (C.encoding-correct (Embed.embed u)))) (representative-correct q))
    (Q.identityˡ q)

  matrix : ∀ (u : HH.Circuit width) q →
    M.⟦ C.compile (Embed.embed u) • representative q ⟧ᴸ ≡
      C.interpret (Embed.embed u) ·*· M.⟦ representative q ⟧ᴸ
  matrix u q = Eq.trans (M.⟦•⟧ᴸ (C.compile (Embed.embed u)) (representative q))
    (Eq.cong (_·*· M.⟦ representative q ⟧ᴸ) (C.encoding-correct (Embed.embed u)))
