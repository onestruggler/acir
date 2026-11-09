------------------------------------------------------------------------
-- Presentations of groups
--
-- The circuits that keep wire 3 are faithful
--
-- K, the group of the four-wire circuits whose letters do not target
-- wire 3, is C ⋊ P: P the circuits of the lower three wires and C the
-- group of the controlled matchings (on the half where wire 3 is 1).
-- Every letter of K is a word in the letters of the lower wires and
-- G = CX₃₀ (expand: CX₃₁ and CX₃₂ are CX₃₀ under a swap, and a Toffoli
-- controlled by wire 3 is equation (8) and the commutation E3 under a
-- relabelling, expand-ok).  A letter of the lower wires carries a
-- controlled matching to another (push: the frame of G by the
-- letter's Coxeter word, decided for the 105 labels by the frame
-- lemma W′), and G is the label μ₀, so every word of K is a word of
-- labels followed by a word of the lower wires (nf).  Two words of K
-- with the same function: the labels fix the lower half, so the two
-- lower words agree there, hence everywhere (they do not see wire 3),
-- and are equal by completeness on three wires; cancelling them, the
-- two words of labels have the same function and are equal by
-- CFaithful.  That is Faithful ₃, the hypothesis of Four.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.KFaithful where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; reverse ; [_])
open import Data.List.Properties using (unfold-reverse)
open import Data.Maybe.Base using (fromMaybe)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (_•_ ; ε)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics
  using (Bits ; ⟦_⟧ ; _≐_ ; allB ; allB-sound ; eqF ; eqF-sound ; eqV ; eqV-sound ; sound)
open import Examples.Groups.XCXCCX-4bit.Placed
  using ( PG ; Xᵖ ; CXᵖ ; CCXᵖ ; Wire ; ι ; ι* ; every ; avoids ; ⟦_⟧ᵖ ; ⟦_⟧ᵖ* ; ι*-sem
        ; forallPG ; forallPG-sound ; ρ4 )
open import Examples.Groups.XCXCCX-4bit.PlacedEngine
  using ( Eqnᵖ ; prf ; derive ; rw ; narrow ; sym⁼ ; relabel⁼ ; eqPG ; eqPG-sound
        ; narrow-check ; narrow-sound )
open import Examples.Groups.XCXCCX-4bit.Equations4 using (eq8⁼ ; E3⁼)
open import Examples.Groups.XCXCCX-4bit.ToPlaced using (pg ; pg-ok ; ι*-++)
open import Examples.Groups.XCXCCX-4bit.Narrow3 using (narrowᵖ)
open import Examples.Groups.XCXCCX-4bit.Faithful using (Faithful ; keeps ; every-++)
open import Examples.Groups.XCXCCX-4bit.PFrames using (Pc ; Fr ; Fr-conj ; inv)
open import Examples.Groups.XCXCCX-4bit.CBase using (G)
open import Examples.Groups.XCXCCX-4bit.CFrame using (matchF ; eqMatch ; W′)
open import Examples.Groups.XCXCCX-4bit.CRel using (L ; Xm ; frm ; find)
open import Examples.Groups.XCXCCX-4bit.CSem using (allFin ; allFin-sound ; mF ; mF*)
open import Examples.Groups.XCXCCX-4bit.CCerts using (Xs ; μ₀)
open import Examples.Groups.XCXCCX-4bit.CFaithful using (cfaith ; Xs-sem)
open import Examples.Groups.XCXCCX-4bit.KData using (rg)

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)
open SR (PP.word-setoid (4 VRel,_===_))

private
  ∧ˡ : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
  ∧ˡ {true} _ = Eq.refl

  ∧ʳ : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
  ∧ʳ {true} h = h

  imp : ∀ a {b} → (not a ∨ b) ≡ true → a ≡ true → b ≡ true
  imp true h _ = h

  ≡→≈ : {u v : Circuit 4} → u ≡ v → 4 ⊢ u ≈ v
  ≡→≈ Eq.refl = refl

  -- An identity of placed words on three wires.
  nar : (m : Wire) (u v : List PG) → every (avoids m) u ≡ true → every (avoids m) v ≡ true →
        eqF 4 ⟦ u ⟧ᵖ* ⟦ v ⟧ᵖ* ≡ true → 4 ⊢ ι* u ≈ ι* v
  nar m u v hu hv hs = narrowᵖ m u v hu hv (eqF-sound 4 _ _ hs)

------------------------------------------------------------------------
-- Every letter is an involution

private
  inv-check : forallPG (λ g → narrow-check (g ∷ g ∷ []) []) ≡ true
  inv-check = Eq.refl

gg : (g : PG) → 4 ⊢ ι g • ι g ≈ ε
gg g = trans (cong refl (sym right-unit))
         (narrow-sound (g ∷ g ∷ []) [] (forallPG-sound (λ g → narrow-check (g ∷ g ∷ []) []) inv-check g))

-- A word of letters followed by its reverse.
rev-cancel : (p : List PG) → 4 ⊢ ι* p • ι* (reverse p) ≈ ε
rev-cancel []      = left-unit
rev-cancel (g ∷ p) = begin
  (ι g • ι* p) • ι* (reverse (g ∷ p))
    ≈⟨ cong refl (≡→≈ (Eq.cong ι* (unfold-reverse g p))) ⟩
  (ι g • ι* p) • ι* (reverse p ++ [ g ])
    ≈⟨ cong refl (ι*-++ (reverse p) [ g ]) ⟩
  (ι g • ι* p) • (ι* (reverse p) • (ι g • ε))
    ≈⟨ assoc ⟩
  ι g • (ι* p • (ι* (reverse p) • (ι g • ε)))
    ≈⟨ cong refl (sym assoc) ⟩
  ι g • ((ι* p • ι* (reverse p)) • (ι g • ε))
    ≈⟨ cong refl (cong (rev-cancel p) refl) ⟩
  ι g • (ε • (ι g • ε))
    ≈⟨ cong refl (trans left-unit right-unit) ⟩
  ι g • ι g
    ≈⟨ gg g ⟩
  ε
    ∎

------------------------------------------------------------------------
-- The letters of the lower wires push across the controlled matchings

-- The label of a matching conjugated by a letter of the lower wires.
ρ : PG → L → L
ρ g ν = fromMaybe ν (find (matchF (rg g • frm ν)))

private
  -- A letter of the lower wires is the circuit of its Coxeter word and
  -- of the inverse word (three-wire identities), and carries every
  -- label ν to ρ g ν (the frame lemma's condition).
  low-ok : PG → Bool
  low-ok g =
    (every (avoids ₃) (pg (Pc 0 (rg g))) ∧ eqF 4 ⟦ pg (Pc 0 (rg g)) ⟧ᵖ* ⟦ g ∷ [] ⟧ᵖ*)
    ∧ ((every (avoids ₃) (pg (Pc 0 (inv (rg g)))) ∧ eqF 4 ⟦ pg (Pc 0 (inv (rg g))) ⟧ᵖ* ⟦ g ∷ [] ⟧ᵖ*)
    ∧ allFin 105 (λ ν → eqMatch (rg g • frm ν) (frm (ρ g ν))))

  low-check : forallPG (λ g → not (avoids ₃ g) ∨ low-ok g) ≡ true
  low-check = Eq.refl

  low-sound : (g : PG) → avoids ₃ g ≡ true → low-ok g ≡ true
  low-sound g a = imp (avoids ₃ g) (forallPG-sound (λ g → not (avoids ₃ g) ∨ low-ok g) low-check g) a

  one : (g : PG) → avoids ₃ g ≡ true → every (avoids ₃) (g ∷ []) ≡ true
  one g a = Eq.cong (λ b → b ∧ true) a

  ιg-Pc : (g : PG) → avoids ₃ g ≡ true → 4 ⊢ ι g ≈ Pc 0 (rg g)
  ιg-Pc g a = sym (trans (pg-ok (Pc 0 (rg g)))
                    (trans (nar ₃ (pg (Pc 0 (rg g))) (g ∷ []) (∧ˡ h) (one g a) (∧ʳ {every (avoids ₃) (pg (Pc 0 (rg g)))} h))
                           right-unit))
    where
    h = ∧ˡ (low-sound g a)

  ιg-Pc⁻ : (g : PG) → avoids ₃ g ≡ true → 4 ⊢ ι g ≈ Pc 0 (inv (rg g))
  ιg-Pc⁻ g a = sym (trans (pg-ok (Pc 0 (inv (rg g))))
                     (trans (nar ₃ (pg (Pc 0 (inv (rg g)))) (g ∷ []) (∧ˡ h) (one g a)
                                 (∧ʳ {every (avoids ₃) (pg (Pc 0 (inv (rg g))))} h))
                            right-unit))
    where
    h = ∧ˡ (∧ʳ {every (avoids ₃) (pg (Pc 0 (rg g))) ∧ eqF 4 ⟦ pg (Pc 0 (rg g)) ⟧ᵖ* ⟦ g ∷ [] ⟧ᵖ*} (low-sound g a))

  match-ok : (g : PG) → avoids ₃ g ≡ true → (ν : L) → eqMatch (rg g • frm ν) (frm (ρ g ν)) ≡ true
  match-ok g a ν =
    allFin-sound 105 (λ ν → eqMatch (rg g • frm ν) (frm (ρ g ν)))
      (∧ʳ {every (avoids ₃) (pg (Pc 0 (inv (rg g)))) ∧ eqF 4 ⟦ pg (Pc 0 (inv (rg g))) ⟧ᵖ* ⟦ g ∷ [] ⟧ᵖ*}
          (∧ʳ {every (avoids ₃) (pg (Pc 0 (rg g))) ∧ eqF 4 ⟦ pg (Pc 0 (rg g)) ⟧ᵖ* ⟦ g ∷ [] ⟧ᵖ*} (low-sound g a)))
      ν

push : (g : PG) → avoids ₃ g ≡ true → (ν : L) → 4 ⊢ ι g • Xm ν ≈ Xm (ρ g ν) • ι g
push g a ν = begin
  ι g • Xm ν
    ≈⟨ sym right-unit ⟩
  (ι g • Xm ν) • ε
    ≈⟨ cong refl (sym (gg g)) ⟩
  (ι g • Xm ν) • (ι g • ι g)
    ≈⟨ assoc ⟩
  ι g • (Xm ν • (ι g • ι g))
    ≈⟨ cong refl (sym assoc) ⟩
  ι g • ((Xm ν • ι g) • ι g)
    ≈⟨ sym assoc ⟩
  (ι g • ((Xm ν • ι g))) • ι g
    ≈⟨ cong (cong (ιg-Pc g a) (cong refl (ιg-Pc⁻ g a))) refl ⟩
  (Pc 0 (rg g) • (Xm ν • Pc 0 (inv (rg g)))) • ι g
    ≈⟨ cong (Fr-conj G (rg g) (frm ν)) refl ⟩
  Fr G (rg g • frm ν) • ι g
    ≈⟨ cong (W′ (rg g • frm ν) (frm (ρ g ν)) (match-ok g a ν)) refl ⟩
  Xm (ρ g ν) • ι g
    ∎

push* : (g : PG) → avoids ₃ g ≡ true → (as : List L) → 4 ⊢ ι g • Xs as ≈ Xs (map (ρ g) as) • ι g
push* g a []       = trans right-unit (sym left-unit)
push* g a (ν ∷ as) = begin
  ι g • (Xm ν • Xs as)                    ≈⟨ sym assoc ⟩
  (ι g • Xm ν) • Xs as                    ≈⟨ cong (push g a ν) refl ⟩
  (Xm (ρ g ν) • ι g) • Xs as              ≈⟨ assoc ⟩
  Xm (ρ g ν) • (ι g • Xs as)              ≈⟨ cong refl (push* g a as) ⟩
  Xm (ρ g ν) • (Xs (map (ρ g) as) • ι g)  ≈⟨ sym assoc ⟩
  (Xm (ρ g ν) • Xs (map (ρ g) as)) • ι g  ∎

------------------------------------------------------------------------
-- The normal form over the lower letters and G

isG : PG → Bool
isG g = eqPG g (CXᵖ ₃ ₀)

basic : PG → Bool
basic g = isG g ∨ avoids ₃ g

NF : Set
NF = List L × List PG

cons : Bool → PG → NF → NF
cons true  g (a , p) = μ₀ ∷ a , p
cons false g (a , p) = map (ρ g) a , g ∷ p

nf : List PG → NF
nf []      = [] , []
nf (g ∷ u) = cons (isG g) g (nf u)

private
  Xμ₀ : 4 ⊢ Xm μ₀ ≈ G
  Xμ₀ = trans left-unit right-unit

  cons-ok : (b : Bool) (g : PG) → isG g ≡ b → (b ∨ avoids ₃ g) ≡ true → (r : NF) →
            4 ⊢ ι g • (Xs (proj₁ r) • ι* (proj₂ r)) ≈ Xs (proj₁ (cons b g r)) • ι* (proj₂ (cons b g r))
  cons-ok true  g e _ (a , p) = at (eqPG-sound g (CXᵖ ₃ ₀) e)
    where
    at : g ≡ CXᵖ ₃ ₀ → 4 ⊢ ι g • (Xs a • ι* p) ≈ (Xm μ₀ • Xs a) • ι* p
    at Eq.refl = trans (cong (sym Xμ₀) refl) (sym assoc)
  cons-ok false g e h (a , p) = trans (sym assoc) (trans (cong (push* g h a) refl) assoc)

  cons-low : (b : Bool) (g : PG) → (b ∨ avoids ₃ g) ≡ true → (r : NF) →
             every (avoids ₃) (proj₂ r) ≡ true → every (avoids ₃) (proj₂ (cons b g r)) ≡ true
  cons-low true  g _ (a , p) hp = hp
  cons-low false g h (a , p) hp = Eq.cong₂ _∧_ h hp

nf-ok : (u : List PG) → every basic u ≡ true → 4 ⊢ ι* u ≈ Xs (proj₁ (nf u)) • ι* (proj₂ (nf u))
nf-ok []      _ = sym left-unit
nf-ok (g ∷ u) h =
  trans (cong refl (nf-ok u (∧ʳ {basic g} h))) (cons-ok (isG g) g Eq.refl (∧ˡ h) (nf u))

nf-low : (u : List PG) → every basic u ≡ true → every (avoids ₃) (proj₂ (nf u)) ≡ true
nf-low []      _ = Eq.refl
nf-low (g ∷ u) h = cons-low (isG g) g (∧ˡ h) (nf u) (nf-low u (∧ʳ {basic g} h))

------------------------------------------------------------------------
-- Every letter of K in the lower letters and G

private
  SW01 SW02 E31 E32 : List PG
  SW01 = CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ []
  SW02 = CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₂ ∷ []
  E31 = SW01 ++ CXᵖ ₃ ₀ ∷ SW01
  E32 = SW02 ++ CXᵖ ₃ ₀ ∷ SW02

-- CX₃ₜ is CX₃₀ under the swap of wires 0 and t; CCX from wires a, 3 onto
-- t is CX₃ᵦ CCXᵦₐₜ CX₃ᵦ CCXᵦₐₜ, b the third lower wire.
expand : PG → List PG
expand (CXᵖ ₃ ₁)    = E31
expand (CXᵖ ₃ ₂)    = E32
expand (CCXᵖ ₀ ₃ ₁) = E32 ++ CCXᵖ ₀ ₂ ₁ ∷ E32 ++ CCXᵖ ₀ ₂ ₁ ∷ []
expand (CCXᵖ ₀ ₃ ₂) = E31 ++ CCXᵖ ₀ ₁ ₂ ∷ E31 ++ CCXᵖ ₀ ₁ ₂ ∷ []
expand (CCXᵖ ₁ ₃ ₀) = E32 ++ CCXᵖ ₁ ₂ ₀ ∷ E32 ++ CCXᵖ ₁ ₂ ₀ ∷ []
expand (CCXᵖ ₁ ₃ ₂) = CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ []
expand (CCXᵖ ₂ ₃ ₀) = E31 ++ CCXᵖ ₁ ₂ ₀ ∷ E31 ++ CCXᵖ ₁ ₂ ₀ ∷ []
expand (CCXᵖ ₂ ₃ ₁) = CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ []
expand g            = g ∷ []

private
  d31 d32 : Eqnᵖ
  d31 = derive E31 (CXᵖ ₃ ₁ ∷ []) (narrow 0 7 (CXᵖ ₃ ₁ ∷ []) ∷ []) Eq.refl
  d32 = derive E32 (CXᵖ ₃ ₂ ∷ []) (narrow 0 7 (CXᵖ ₃ ₂ ∷ []) ∷ []) Eq.refl

  -- Equation (8) and E3 with wires 0, 1, 2, 3 on t, 3, b, a.
  d031 d032 d130 d132 d230 d231 : Eqnᵖ
  d031 = derive (expand (CCXᵖ ₀ ₃ ₁)) (CCXᵖ ₀ ₃ ₁ ∷ [])
    (narrow 0 7 (CXᵖ ₃ ₂ ∷ []) ∷ narrow 2 7 (CXᵖ ₃ ₂ ∷ []) ∷
     rw 0 (relabel⁼ (ρ4 ₁ ₃ ₂ ₀) eq8⁼) ∷ rw 1 (sym⁼ (relabel⁼ (ρ4 ₁ ₃ ₂ ₀) E3⁼)) ∷ narrow 0 2 [] ∷ [])
    Eq.refl
  d032 = derive (expand (CCXᵖ ₀ ₃ ₂)) (CCXᵖ ₀ ₃ ₂ ∷ [])
    (narrow 0 7 (CXᵖ ₃ ₁ ∷ []) ∷ narrow 2 7 (CXᵖ ₃ ₁ ∷ []) ∷
     rw 0 (relabel⁼ (ρ4 ₂ ₃ ₁ ₀) eq8⁼) ∷ rw 1 (sym⁼ (relabel⁼ (ρ4 ₂ ₃ ₁ ₀) E3⁼)) ∷ narrow 0 2 [] ∷ [])
    Eq.refl
  d130 = derive (expand (CCXᵖ ₁ ₃ ₀)) (CCXᵖ ₁ ₃ ₀ ∷ [])
    (narrow 0 7 (CXᵖ ₃ ₂ ∷ []) ∷ narrow 2 7 (CXᵖ ₃ ₂ ∷ []) ∷
     rw 0 (relabel⁼ (ρ4 ₀ ₃ ₂ ₁) eq8⁼) ∷ rw 1 (sym⁼ (relabel⁼ (ρ4 ₀ ₃ ₂ ₁) E3⁼)) ∷ narrow 0 2 [] ∷ [])
    Eq.refl
  d132 = derive (expand (CCXᵖ ₁ ₃ ₂)) (CCXᵖ ₁ ₃ ₂ ∷ [])
    (rw 0 (relabel⁼ (ρ4 ₂ ₃ ₀ ₁) eq8⁼) ∷ rw 1 (sym⁼ (relabel⁼ (ρ4 ₂ ₃ ₀ ₁) E3⁼)) ∷ narrow 0 2 [] ∷ [])
    Eq.refl
  d230 = derive (expand (CCXᵖ ₂ ₃ ₀)) (CCXᵖ ₂ ₃ ₀ ∷ [])
    (narrow 0 7 (CXᵖ ₃ ₁ ∷ []) ∷ narrow 2 7 (CXᵖ ₃ ₁ ∷ []) ∷
     rw 0 (relabel⁼ (ρ4 ₀ ₃ ₁ ₂) eq8⁼) ∷ rw 1 (sym⁼ (relabel⁼ (ρ4 ₀ ₃ ₁ ₂) E3⁼)) ∷ narrow 0 2 [] ∷ [])
    Eq.refl
  d231 = derive (expand (CCXᵖ ₂ ₃ ₁)) (CCXᵖ ₂ ₃ ₁ ∷ [])
    (rw 0 (relabel⁼ (ρ4 ₁ ₃ ₀ ₂) eq8⁼) ∷ rw 1 (sym⁼ (relabel⁼ (ρ4 ₁ ₃ ₀ ₂) E3⁼)) ∷ narrow 0 2 [] ∷ [])
    Eq.refl

  -- From a derivation of a letter's expansion.
  by : (g : PG) (d : Eqnᵖ) → 4 ⊢ ι* (expand g) ≈ ι g • ε → 4 ⊢ ι g ≈ ι* (expand g)
  by g d e = sym (trans e right-unit)

expand-ok : (g : PG) → 4 ⊢ ι g ≈ ι* (expand g)
expand-ok (Xᵖ t)         = sym right-unit
expand-ok (CXᵖ ₀ t)      = sym right-unit
expand-ok (CXᵖ ₁ t)      = sym right-unit
expand-ok (CXᵖ ₂ t)      = sym right-unit
expand-ok (CXᵖ ₃ ₀)      = sym right-unit
expand-ok (CXᵖ ₃ ₁)      = by (CXᵖ ₃ ₁) d31 (prf d31)
expand-ok (CXᵖ ₃ ₂)      = by (CXᵖ ₃ ₂) d32 (prf d32)
expand-ok (CXᵖ ₃ ₃)      = sym right-unit
expand-ok (CCXᵖ ₀ ₀ t)   = sym right-unit
expand-ok (CCXᵖ ₀ ₁ t)   = sym right-unit
expand-ok (CCXᵖ ₀ ₂ t)   = sym right-unit
expand-ok (CCXᵖ ₀ ₃ ₀)   = sym right-unit
expand-ok (CCXᵖ ₀ ₃ ₁)   = by (CCXᵖ ₀ ₃ ₁) d031 (prf d031)
expand-ok (CCXᵖ ₀ ₃ ₂)   = by (CCXᵖ ₀ ₃ ₂) d032 (prf d032)
expand-ok (CCXᵖ ₀ ₃ ₃)   = sym right-unit
expand-ok (CCXᵖ ₁ ₀ t)   = sym right-unit
expand-ok (CCXᵖ ₁ ₁ t)   = sym right-unit
expand-ok (CCXᵖ ₁ ₂ t)   = sym right-unit
expand-ok (CCXᵖ ₁ ₃ ₀)   = by (CCXᵖ ₁ ₃ ₀) d130 (prf d130)
expand-ok (CCXᵖ ₁ ₃ ₁)   = sym right-unit
expand-ok (CCXᵖ ₁ ₃ ₂)   = by (CCXᵖ ₁ ₃ ₂) d132 (prf d132)
expand-ok (CCXᵖ ₁ ₃ ₃)   = sym right-unit
expand-ok (CCXᵖ ₂ ₀ t)   = sym right-unit
expand-ok (CCXᵖ ₂ ₁ t)   = sym right-unit
expand-ok (CCXᵖ ₂ ₂ t)   = sym right-unit
expand-ok (CCXᵖ ₂ ₃ ₀)   = by (CCXᵖ ₂ ₃ ₀) d230 (prf d230)
expand-ok (CCXᵖ ₂ ₃ ₁)   = by (CCXᵖ ₂ ₃ ₁) d231 (prf d231)
expand-ok (CCXᵖ ₂ ₃ ₂)   = sym right-unit
expand-ok (CCXᵖ ₂ ₃ ₃)   = sym right-unit
expand-ok (CCXᵖ ₃ b t)   = sym right-unit

private
  basic-check : forallPG (λ g → not (keeps ₃ g) ∨ every basic (expand g)) ≡ true
  basic-check = Eq.refl

expand* : List PG → List PG
expand* []      = []
expand* (g ∷ u) = expand g ++ expand* u

expand*-ok : (u : List PG) → 4 ⊢ ι* u ≈ ι* (expand* u)
expand*-ok []      = refl
expand*-ok (g ∷ u) = trans (cong (expand-ok g) (expand*-ok u)) (sym (ι*-++ (expand g) (expand* u)))

expand*-basic : (u : List PG) → every (keeps ₃) u ≡ true → every basic (expand* u) ≡ true
expand*-basic []      _ = Eq.refl
expand*-basic (g ∷ u) h =
  every-++ basic (expand g) (expand* u)
    (imp (keeps ₃ g) (forallPG-sound (λ g → not (keeps ₃ g) ∨ every basic (expand g)) basic-check g) (∧ˡ h))
    (expand*-basic u (∧ʳ {keeps ₃ g} h))

------------------------------------------------------------------------
-- Semantics

-- Wire 3 flipped.
flip3 : Bits 4 → Bits 4
flip3 (a ∷ b ∷ c ∷ d ∷ []) = a ∷ b ∷ c ∷ not d ∷ []

private
  flip-check : forallPG (λ g → not (avoids ₃ g) ∨ allB 4 (λ x → eqV (⟦ g ⟧ᵖ (flip3 x)) (flip3 (⟦ g ⟧ᵖ x)))) ≡ true
  flip-check = Eq.refl

-- A word that avoids wire 3 does not see it.
flip-comm : (p : List PG) → every (avoids ₃) p ≡ true → ∀ x → ⟦ p ⟧ᵖ* (flip3 x) ≡ flip3 (⟦ p ⟧ᵖ* x)
flip-comm []      h x = Eq.refl
flip-comm (g ∷ p) h x =
  Eq.trans (Eq.cong ⟦ p ⟧ᵖ* (flip-one (∧ˡ h)))
           (flip-comm p (∧ʳ {avoids ₃ g} h) (⟦ g ⟧ᵖ x))
  where
  flip-one : avoids ₃ g ≡ true → ⟦ g ⟧ᵖ (flip3 x) ≡ flip3 (⟦ g ⟧ᵖ x)
  flip-one a =
    eqV-sound (⟦ g ⟧ᵖ (flip3 x)) (flip3 (⟦ g ⟧ᵖ x))
      (allB-sound 4 (λ x → eqV (⟦ g ⟧ᵖ (flip3 x)) (flip3 (⟦ g ⟧ᵖ x)))
        (imp (avoids ₃ g)
          (forallPG-sound (λ g → not (avoids ₃ g) ∨ allB 4 (λ x → eqV (⟦ g ⟧ᵖ (flip3 x)) (flip3 (⟦ g ⟧ᵖ x))))
            flip-check g) a) x)

-- The controlled matchings fix the lower half.
mF*-low : (ws : List L) (a b c : Bool) → mF* ws (a ∷ b ∷ c ∷ false ∷ []) ≡ a ∷ b ∷ c ∷ false ∷ []
mF*-low []       a b c = Eq.refl
mF*-low (l ∷ ws) a b c = mF*-low ws a b c

Xs-low : (ws : List L) (a b c : Bool) → ⟦ Xs ws ⟧ (a ∷ b ∷ c ∷ false ∷ []) ≡ a ∷ b ∷ c ∷ false ∷ []
Xs-low ws a b c = Eq.trans (Xs-sem ws (a ∷ b ∷ c ∷ false ∷ [])) (mF*-low ws a b c)

------------------------------------------------------------------------
-- Faithfulness of K

faithful₃ : Faithful ₃
faithful₃ u v hu hv e =
  trans eu (trans (cong (cfaith a b Xab) ιpq) (sym ev))
  where
  bu = expand*-basic u hu
  bv = expand*-basic v hv
  a = proj₁ (nf (expand* u))
  p = proj₂ (nf (expand* u))
  b = proj₁ (nf (expand* v))
  q = proj₂ (nf (expand* v))

  eu : 4 ⊢ ι* u ≈ Xs a • ι* p
  eu = trans (expand*-ok u) (nf-ok (expand* u) bu)

  ev : 4 ⊢ ι* v ≈ Xs b • ι* q
  ev = trans (expand*-ok v) (nf-ok (expand* v) bv)

  hp : every (avoids ₃) p ≡ true
  hp = nf-low (expand* u) bu

  hq : every (avoids ₃) q ≡ true
  hq = nf-low (expand* v) bv

  sem : ⟦ Xs a • ι* p ⟧ ≐ ⟦ Xs b • ι* q ⟧
  sem x =
    Eq.trans (Eq.sym (sound eu x))
      (Eq.trans (ι*-sem u x)
        (Eq.trans (e x) (Eq.trans (Eq.sym (ι*-sem v x)) (sound ev x))))

  -- The lower words agree on the lower half, where the labels act
  -- trivially, and so everywhere.
  low : (a₀ a₁ a₂ : Bool) → ⟦ p ⟧ᵖ* (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ []) ≡ ⟦ q ⟧ᵖ* (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ [])
  low a₀ a₁ a₂ =
    Eq.trans (Eq.sym (ι*-sem p y))
      (Eq.trans (Eq.cong ⟦ ι* p ⟧ (Eq.sym (Xs-low a a₀ a₁ a₂)))
        (Eq.trans (sem y)
          (Eq.trans (Eq.cong ⟦ ι* q ⟧ (Xs-low b a₀ a₁ a₂)) (ι*-sem q y))))
    where
    y = a₀ ∷ a₁ ∷ a₂ ∷ false ∷ []

  pq : ⟦ p ⟧ᵖ* ≐ ⟦ q ⟧ᵖ*
  pq (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ []) = low a₀ a₁ a₂
  pq (a₀ ∷ a₁ ∷ a₂ ∷ true ∷ [])  =
    Eq.trans (flip-comm p hp (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ []))
      (Eq.trans (Eq.cong flip3 (low a₀ a₁ a₂)) (Eq.sym (flip-comm q hq (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ []))))

  ιpq : 4 ⊢ ι* p ≈ ι* q
  ιpq = narrowᵖ ₃ p q hp hq pq

  -- Cancelling the lower words, the labels have the same function.
  P′ = ι* (reverse p)

  l1 : 4 ⊢ Xs a ≈ (Xs a • ι* p) • P′
  l1 = trans (sym right-unit) (trans (cong refl (sym (rev-cancel p))) (sym assoc))

  l2 : 4 ⊢ (Xs b • ι* q) • P′ ≈ Xs b
  l2 = trans (cong (cong refl (sym ιpq)) refl) (trans assoc (trans (cong refl (rev-cancel p)) right-unit))

  Xab : ⟦ Xs a ⟧ ≐ ⟦ Xs b ⟧
  Xab x = Eq.trans (sound l1 x) (Eq.trans (Eq.cong ⟦ P′ ⟧ (sem x)) (sound l2 x))
