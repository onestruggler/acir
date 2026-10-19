------------------------------------------------------------------------
-- Presentations of groups
--
-- A coset table of three-wire circuits over W(D8), and deciding
-- equations with it.
--
-- The table has, for each coset c and gate g, a label (a word in the
-- nine letters) and a next coset, with a derivation of
-- rep c • g ≈ label • rep next (checked against the table by one
-- boolean).  Every circuit then walks to a label followed by a
-- representative (`normal`), and two circuits that reach one coset
-- with labels of one signed permutation are equal (`by-table`): the
-- labels are, by the completeness of W(D8) decoded into Natural.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_)
open import Data.Vec.Base using (Vec)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Kit using (Gen ; Eqn)

module Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.TableKit
  {ck : ℕ}
  (repT : Vec (List (Gen 3)) ck)
  (tabT : Vec (Vec (List (Fin 9) × Fin ck) 8) ck)
  (factT : Vec (Vec (Eqn 3) 8) ck)
  where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Fin.Base using (zero ; suc)
open import Data.List.Base using ([] ; _∷_ ; _++_ ; concatMap)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; inspect)
  renaming ([_] to [_]ᵢ)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; _ᵗ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Kit
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Letters using (dec)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Decode using (decW ; decode-cong ; decW-list)
import Examples.Groups.CCX+HH.Natural.Engine as En
import Examples.Groups.CCX+HH.Natural.ThreeWire.Pure as Pu
import Examples.Groups.CCX+HH.Natural.ThreeWire.Gamma as Γm
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Invariants using (ιD)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound)
import Examples.Groups.CCX+HH.Natural.ThreeWire.D8 as D8

open PB (3 VRel,_===_) using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

private
  ≡→≈ : ∀ {u v : Circuit 3} → u ≡ v → 3 ⊢ u ≈ v
  ≡→≈ Eq.refl = refl

  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = Eq.refl

  ∧-r : ∀ a {b} → a ∧ b ≡ true → b ≡ true
  ∧-r true h = h

------------------------------------------------------------------------
-- Gates as indices

gix : Gen 3 → Fin 8
gix x₀   = ₀
gix x₁   = ₁
gix x₂   = ₂
gix cx₀  = ₃
gix cx₁  = ₄
gix ccx₀ = ₅
gix hh₀  = ₆
gix hh₁  = ₇
gix (gate₀ ())
gix (gate₀ () ↥)
gix (gate₀ () ↥ ↥)
gix (gate₀ () ↥ ↥ ↥)

gate : Fin 8 → Gen 3
gate ₀ = x₀
gate ₁ = x₁
gate ₂ = x₂
gate ₃ = cx₀
gate ₄ = cx₁
gate ₅ = ccx₀
gate ₆ = hh₀
gate ₇ = hh₁

gate-gix : ∀ g → gate (gix g) ≡ g
gate-gix x₀   = Eq.refl
gate-gix x₁   = Eq.refl
gate-gix x₂   = Eq.refl
gate-gix cx₀  = Eq.refl
gate-gix cx₁  = Eq.refl
gate-gix ccx₀ = Eq.refl
gate-gix hh₀  = Eq.refl
gate-gix hh₁  = Eq.refl
gate-gix (gate₀ ())
gate-gix (gate₀ () ↥)
gate-gix (gate₀ () ↥ ↥)
gate-gix (gate₀ () ↥ ↥ ↥)

------------------------------------------------------------------------
-- The table

E9 : Word (Fin 9) → Word Γm.L
E9 = (λ x → [ ιD x ]ʷ) ʷ

F : Word (Fin 9) → Circuit 3
F l = decW (E9 l)

rep : Fin ck → Circuit 3
rep c = ⟪ lookup repT c ⟫

h : Fin ck → Gen 3 → Word (Fin 9) × Fin ck
h c g = Pu.word-of-list (proj₁ (lookup (lookup tabT c) (gix g))) , proj₂ (lookup (lookup tabT c) (gix g))

out : Fin ck → Circuit 3 → Word (Fin 9)
out c w = proj₁ ((h ᵗ) c w)

state : Fin ck → Circuit 3 → Fin ck
state c w = proj₂ ((h ᵗ) c w)

match : Fin ck → Fin 8 → Bool
match c i =
  En.eqL (lhs e) (lookup repT c ++ gate i ∷ []) ∧
  En.eqL (rhs e) (concatMap (λ x → dec (ιD x)) (proj₁ (lookup (lookup tabT c) i)) ++
                  lookup repT (proj₂ (lookup (lookup tabT c) i)))
  where e = lookup (lookup factT c) i

module Checked (I : Fin ck) (rep-I : lookup repT I ≡ [])
               (facts-ok : allFin ck (λ c → allFin 8 (match c)) ≡ true) where

  private
    -- Reading a decoded label list.
    F-list : (l : List (Fin 9)) → 3 ⊢ F (Pu.word-of-list l) ≈ ⟪ concatMap (λ x → dec (ιD x)) l ⟫
    F-list []       = refl
    F-list (x ∷ xs) = trans (cong refl (F-list xs))
      (sym (En.⟪++⟫ (dec (ιD x)) (concatMap (λ x → dec (ιD x)) xs)))

    glue : ∀ (r : List (Gen 3)) (g : Gen 3) (l : List (Fin 9)) (r′ : List (Gen 3)) (e : Eqn 3) →
           lhs e ≡ r ++ g ∷ [] → rhs e ≡ concatMap (λ x → dec (ιD x)) l ++ r′ →
           3 ⊢ ⟪ r ⟫ • [ g ]ʷ ≈ F (Pu.word-of-list l) • ⟪ r′ ⟫
    glue r g l r′ e el er =
      trans (cong refl (sym right-unit))
      (trans (sym (En.⟪++⟫ r (g ∷ [])))
      (trans (≡→≈ (Eq.cong ⟪_⟫ (Eq.sym el)))
      (trans (prf e)
      (trans (≡→≈ (Eq.cong ⟪_⟫ er))
      (trans (En.⟪++⟫ (concatMap (λ x → dec (ιD x)) l) r′)
        (cong (sym (F-list l)) refl))))))

  fact : ∀ c g → 3 ⊢ rep c • [ g ]ʷ ≈ F (proj₁ (h c g)) • rep (proj₂ (h c g))
  fact c g = Eq.subst (λ y → 3 ⊢ rep c • [ y ]ʷ ≈ F (proj₁ (h c g)) • rep (proj₂ (h c g)))
    (gate-gix g)
    (glue (lookup repT c) (gate (gix g)) (proj₁ (lookup (lookup tabT c) (gix g)))
      (lookup repT (proj₂ (lookup (lookup tabT c) (gix g)))) (lookup (lookup factT c) (gix g))
      (En.eqL-sound _ _ (∧-l ok))
      (En.eqL-sound _ _ (∧-r (En.eqL (lhs (lookup (lookup factT c) (gix g)))
                                      (lookup repT c ++ gate (gix g) ∷ [])) ok)))
    where
    ok : match c (gix g) ≡ true
    ok = allFin-sound 8 (match c) (allFin-sound ck (λ c → allFin 8 (match c)) facts-ok c) (gix g)

  module _ where
    open SR (PP.word-setoid (3 VRel,_===_))

    normal-at : ∀ c w → 3 ⊢ rep c • w ≈ F (out c w) • rep (state c w)
    normal-at c [ g ]ʷ = fact c g
    normal-at c ε = trans right-unit (sym left-unit)
    normal-at c (u • v) with (h ᵗ) c u | inspect ((h ᵗ) c) u
    ... | (u′ , c′) | [ Eq.refl ]ᵢ with (h ᵗ) c′ v | inspect ((h ᵗ) c′) v
    ... | (v′ , c″) | [ Eq.refl ]ᵢ = begin
      rep c • (u • v)               ≈⟨ sym assoc ⟩
      (rep c • u) • v               ≈⟨ cong (normal-at c u) refl ⟩
      (F u′ • rep c′) • v           ≈⟨ assoc ⟩
      F u′ • (rep c′ • v)           ≈⟨ cong refl (normal-at c′ v) ⟩
      F u′ • (F v′ • rep c″)        ≈⟨ sym assoc ⟩
      (F u′ • F v′) • rep c″        ∎

    normal : ∀ w → 3 ⊢ w ≈ F (out I w) • rep (state I w)
    normal w = begin
      w                        ≈⟨ sym left-unit ⟩
      ε • w                    ≈⟨ cong (≡→≈ (Eq.cong ⟪_⟫ (Eq.sym rep-I))) refl ⟩
      rep I • w                ≈⟨ normal-at I w ⟩
      F (out I w) • rep (state I w) ∎

  -- Two circuits reaching one coset with labels of one signed permutation.
  by-table : ∀ u v → state I u ≡ state I v →
             Γm.sp (E9 (out I u)) ≡ Γm.sp (E9 (out I v)) → 3 ⊢ u ≈ v
  by-table u v hs hl = trans (normal u) (trans (cong labels
    (≡→≈ (Eq.cong rep hs))) (sym (normal v)))
    where
    labels : 3 ⊢ F (out I u) ≈ F (out I v)
    labels = decode-cong (D8.complete (out I u) (out I v) hl)
