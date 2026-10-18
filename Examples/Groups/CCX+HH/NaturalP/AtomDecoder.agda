------------------------------------------------------------------------
-- Presentations of groups
--
-- Decoding an auxiliary atom by routing it into a window.
--
-- On 4 + k + c wires, an atom p of GeneralN/DecodingPlans that moves
-- some coordinates is `Routed` when its points, listed by an injection
-- `pts`, are carried by an affine word K to fixed states `cst` of the
-- top four wires (the other wires 0), and p acts on its points as a
-- canonical atom q on 16 coordinates acts on the indices of those
-- states.  Its decoding is then
--
--   ⌈ inv K ⌉ • Λw k (Λw c c₄) • ⌈ K ⌉,
--
-- where c₄ is GeneralN/Decoding's physical circuit for q on four
-- wires, under c white controls under k more.  An atom that moves
-- nothing decodes to ε.  `decode-act`: the decoding acts on vectors as
-- the atom's Table 1 word, and so has its matrix (`decode-correct`).
-- The proof is AtCalc's: c₄ acts at the indices of `cst` as the
-- canonical word (GeneralN/Decoding.atom-correct), the controls carry
-- that to the window (`Λ-at`), and K carries the window to the points
-- (`at-perm`), where the atom acts the same way.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+HH.NaturalP.AtomDecoder (k c : ℕ) where

open import Data.Fin.Base using (Fin)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; ε ; _•_ ; wmap)
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (_!_ ; actVʷ ; same-action ; same-matrix ; ⟦_⟧ᵐ)
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum ; encoding-action)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (idx ; bits ; idx-cong)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)
open import Examples.Groups.CCX+HH.GeneralN.DecodingPlans using (Atom ; e)
import Examples.Groups.CCX+HH.GeneralN.Decoding as Decoding
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Bridge as B
open B using (τ)
open import Examples.Groups.CCX+HH.NaturalP.Lambda using (Λw)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; ⌈_⌉ ; inv ; ιC ; τ-aff)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (A⟦_⟧ ; A-cong ; A-inv)
open import Examples.Groups.CCX+HH.NaturalP.AtCalc
  using (Op ; AtI ; at→I ; atI-ext ; atI-cong ; atI-∘ ; ιW ; Λ-at ; perm-! ; at-perm)
open import Examples.Groups.CCX+HH.NaturalP.Route4 using (stack ; stack-ιW)

private
  module Dec₀ = Decoding 0

W : ℕ
W = ₄₊ (k + (c + 0))

N : ℕ
N = 2 ^ W

------------------------------------------------------------------------
-- Routed atoms

record Routed (p : Atom N) : Set where
  field
    m      : ℕ
    pts    : Fin m → Fin N
    G      : Op m
    tbl    : AtI pts G (actVʷ (e p))
    q      : Atom 16
    cst    : Fin m → State 4
    can    : AtI (λ y → idx 4 (cst y)) G (actVʷ (e q))
    K      : Word (AGen W)
    lands  : ∀ y → A⟦ K ⟧ (bits W (pts y)) ≈s stack (k + (c + 0)) zeros (cst y)

data Decoded (p : Atom N) : Set where
  trivial : (∀ v → actVʷ (e p) v ≡ v) → Decoded p
  routed  : Routed p → Decoded p

------------------------------------------------------------------------
-- The decoding

-- The physical circuit of a canonical atom.
c₄ : Atom 16 → P.Circuit 4
c₄ q = B.ι (Dec₀.atom q)

window : Atom 16 → P.Circuit W
window q = Λw k (Λw c (c₄ q))

decode : {p : Atom N} → Decoded p → P.Circuit W
decode (trivial _) = ε
decode (routed r)  = ⌈ inv K ⌉ • (window q • ⌈ K ⌉)
  where open Routed r

------------------------------------------------------------------------
-- Correctness

c₄-act : (q : Atom 16) → ∀ v → quantum (τ (c₄ q)) v ≡ actVʷ (e q) v
c₄-act q v =
  trans (cong (λ w → quantum w v) (B.τι (Dec₀.atom q)))
  (trans (sym (encoding-action (Dec₀.atom q) v))
    (same-action (E.encode (Dec₀.atom q)) (e q)
      (trans (Q.encoding-correct (Dec₀.atom q)) (Dec₀.atom-correct q)) v))

-- An affine word permutes the coordinates as it permutes the states.
perm-aff : (a : Word (AGen W)) → ∀ (v : Vec D N) s →
  quantum (τ ⌈ a ⌉) v ! idx W (A⟦ a ⟧ s) ≡ v ! idx W s
perm-aff a v s = trans (cong (λ w → quantum w v ! idx W (A⟦ a ⟧ s)) (τ-aff a)) (perm-! (wmap ιC a) v s)

decode-act : {p : Atom N} (x : Decoded p) → ∀ v → quantum (τ (decode x)) v ≡ actVʷ (e p) v
decode-act (trivial t) v = sym (t v)
decode-act (routed r)  v = atI-ext conj tbl (λ u → refl) v
  where
  open Routed r
  F : Op N
  F = quantum (τ (window q))
  win-at : AtI (λ y → ι (ιW k (c + 0)) (ι (ιW c 0) (idx 4 (cst y)))) G F
  win-at = atI-∘ (at→I (Λ-at k (Λw c (c₄ q))))
    (atI-∘ (at→I (Λ-at c (c₄ q))) (atI-cong can (λ u → refl) (λ u → sym (c₄-act q u))))
  cond : ∀ y → ι (ιW k (c + 0)) (ι (ιW c 0) (idx 4 (cst y))) ≡ idx W (A⟦ K ⟧ (bits W (pts y)))
  cond y = trans (stack-ιW k c (cst y)) (idx-cong W (λ i → sym (lands y i)))
  conj : AtI pts G (λ u → quantum (τ ⌈ inv K ⌉) (F (quantum (τ ⌈ K ⌉) u)))
  conj = at-perm (quantum (τ ⌈ K ⌉)) (quantum (τ ⌈ inv K ⌉)) A⟦ K ⟧ A⟦ inv K ⟧
    (perm-aff K) (perm-aff (inv K)) (A-inv K) (A-cong (inv K)) win-at pts cond

decode-correct : {p : Atom N} (x : Decoded p) → Q.interpret (τ (decode x)) ≡ ⟦ e p ⟧ᵐ
decode-correct {p} x =
  trans (sym (Q.encoding-correct (τ (decode x))))
    (same-matrix (E.encode (τ (decode x))) (e p)
      (λ u → trans (encoding-action (τ (decode x)) u) (decode-act x u)))
