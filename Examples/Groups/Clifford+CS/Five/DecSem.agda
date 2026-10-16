------------------------------------------------------------------------
-- Presentations of groups
--
-- The affine decoding on five wires preserves the semantics
--
-- Each gadget denotes its two-level block (Five.Sem.Gad5), so the
-- decoding of a list of gadgets denotes their product (`Dg-sem`), and
-- the decoding of a word over P′ has the word's reading (`dʷ-sem`): the
-- decoding is the decoding of its gadgets up to the sound five-wire
-- theory (Five.Dec5.dʷ-D, Five.Soundness), and the reading is their
-- product (Five.Decode.sem-w).  So a word over P′ decodes to a circuit
-- with its matrix as soon as its decoding is that circuit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Primality using (prime[2])
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (_•_)
open import Examples.Groups.Clifford+CS.Five.Inputs using (Inputs)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)
open import Examples.Groups.Clifford+CS.Five.Affine using (τ)
open import Examples.Groups.Clifford+CS.Five.Stab using (e₀)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)
import Examples.Groups.Clifford+CS.Five.Calc as Calc
import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan 0 prime[2] 0 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Aff 0 prime[2] using (adm)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm using (fn)
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹)

module Examples.Groups.Clifford+CS.Five.DecSem
  (I : Inputs)
  (F : Facts4)
  (cind : (V : Kind) (α β : B.Circuit 5) → fn α 0ᵛ ≡ fn β 0ᵛ → fn α e₀ ≡ fn β e₀ →
          5 ⊢ₓ τ α • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (α ⁻¹)
             ≈ τ β • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (β ⁻¹))
  where

open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Fin.Properties using (<⇒≢)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_ ; refl)
open import Word.Base using (Word ; ε ; _ʷ)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; ⟦⟧ₒ-ε)
open import Examples.Groups.Clifford+CS.Five.Soundness using (soundₓ)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Five.Sem.Core using (Pt ; Πp)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (blkOf ; kpp ; krot ; kki)
open import Examples.Groups.Clifford+CS.Encoding 1 using (N ; cod ; cod-inj)
open import Examples.Groups.Clifford+CS.BridgeGray 5 using (⟦_⟧PY)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Five.Decode 1
  using (Gd ; gd ; kind ; i ; j ; GL ; Valid ; valid-GL ; Π ; sem-w)
open import Examples.Groups.Clifford+CS.Five.Dec5 I F cind using (d ; Dg ; gad₅ ; pts ; dʷ-D)

open Inputs I using (F4ᵍ ; F5ᵍ ; x4x4)
open import Examples.Groups.Clifford+CS.Five.Sem.Gad5 F4ᵍ F5ᵍ x4x4 (Facts4.G F) (Facts4.sem F)
  using (gad₅-sem)

------------------------------------------------------------------------
-- Lists of gadgets

Dist : Pt 5 → Set
Dist (V , p , q) = p ≢ q

Dg-sem : (L : List (Pt 5)) → All Dist L → ⟦ Dg L ⟧ ~ Πp L
Dg-sem []                []        = ~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {5} ε} {Idₒ} refl ⟦⟧ₒ-ε
Dg-sem ((V , p , q) ∷ L) (ne ∷ ds) =
  ~-trans {s = ⟦ gad₅ V p q • Dg L ⟧} {t = ⟦ gad₅ V p q ⟧ ∙ ⟦ Dg L ⟧} {u = Πp ((V , p , q) ∷ L)}
    (hom (gad₅ V p q) (Dg L))
    (∙-cong {s = ⟦ gad₅ V p q ⟧} {s' = tl (blkOf V) p q} {t = ⟦ Dg L ⟧} {t' = Πp L}
      (gad₅-sem V p q ne) (Dg-sem L ds))

------------------------------------------------------------------------
-- Words

private
  vne : ∀ G → Valid G → i G ≢ j G
  vne (gd kpp a b)  ne = ne
  vne (gd krot a b) ne = ne
  vne (gd kki a b)  lt = λ e → <⇒≢ lt (Eq.sym e)

  dists : ∀ Gs → All Valid Gs → All Dist (pts Gs)
  dists []       []        = []
  dists (G ∷ Gs) (vG ∷ vs) = (λ e → vne G vG (cod-inj e)) ∷ dists Gs vs

  Π-pts : ∀ Gs → Π Gs ≡ Πp (pts Gs)
  Π-pts []       = refl
  Π-pts (G ∷ Gs) = Eq.cong (tl (blkOf (kind G)) (cod (i G)) (cod (j G)) ∙_) (Π-pts Gs)

-- The decoding of a word has the word's reading.
dʷ-sem : (u : Word (GenP N)) → ⟦ (d ʷ) u ⟧ ~ ⟦ u ⟧PY
dʷ-sem u =
  ~-trans {s = ⟦ (d ʷ) u ⟧} {t = ⟦ Dg (pts (GL u)) ⟧} {u = ⟦ u ⟧PY} (soundₓ (dʷ-D u))
    (~-trans {s = ⟦ Dg (pts (GL u)) ⟧} {t = Πp (pts (GL u))} {u = ⟦ u ⟧PY}
      (Dg-sem (pts (GL u)) (dists (GL u) (valid-GL u)))
      (Eq.subst (_~ ⟦ u ⟧PY) (Π-pts (GL u)) (~-sym {s = ⟦ u ⟧PY} {t = Π (GL u)} (sem-w u))))
