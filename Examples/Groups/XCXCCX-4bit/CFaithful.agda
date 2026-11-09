------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled matchings are faithful
--
-- Two words of labels whose controlled matchings have the same
-- function are equal circuits.  As ByEvenRS does on four wires, at
-- eight states: the words of the symbols of EvenRS 8 (CCerts' Φ) act on
-- the upper half as the even permutations f (γ c d) (Φ*-act, from the
-- functions of the labels, CSem), the relations of EvenRS 8 hold for
-- them (R-rel), and every label is a word of symbols (ψ, along the
-- closure tree: a label is its parent conjugated by the word of a
-- symbol, conj-list).  So two words of labels with the same function
-- translate to words of symbols with the same permutation, which
-- EvenRS 8's completeness relates, and the relations carry over.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.CFaithful where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; reverse ; [_])
open import Data.List.Properties using (++-assoc ; ++-identityʳ ; unfold-reverse)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≡ᵇ_)
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Relation.Binary.Reasoning.Setoid as SR
import Presentation.Properties as PP

import Examples.Groups.Symmetric.Interpretation as SymI

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (Bits ; ⟦_⟧ ; _≐_ ; ⨾-cong ; eqV ; eqV-sound ; sound)
open import Examples.Groups.XCXCCX-4bit.CRel using (L ; Xm ; c3 ; _==ᴸ_ ; ==ᴸ-sound ; conj-ok)
open import Examples.Groups.XCXCCX-4bit.CBC using (X-conj)
open import Examples.Groups.XCXCCX-4bit.CSem
  using (allFin-sound ; enc8 ; enc8-injective ; mF ; mF* ; mF*-++ ; Xm-sem)
open import Examples.Groups.XCXCCX-4bit.CCerts
  using ( Xs ; Xs-++ ; Φ ; Φ* ; Φ-act-ok ; R-rel ; inv-sym ; rev-ok ; μ₀ ; base-word ; base-ok
        ; par ; sym-of ; dep ; star ; conjs-ok ; cstep ; closure-ok ; closure-all )
import Examples.Groups.XCXCCX-4bit.EvenRS as ERS
open ERS 8 using (Sch ; f ; _RS,_===_ ; rs-complete)

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)
open SR (PP.word-setoid (4 VRel,_===_))

private
  ∧ˡ : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
  ∧ˡ {true} _ = Eq.refl

  ∧ʳ : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
  ∧ʳ {true} h = h

  ≡→≈ : {u v : Circuit 4} → u ≡ v → 4 ⊢ u ≈ v
  ≡→≈ Eq.refl = refl

  T-true : ∀ {b} → b ≡ true → Data.Bool.Base.T b
  T-true Eq.refl = _

  import Data.Bool.Base

------------------------------------------------------------------------
-- Conjugation by a word of labels

-- Xs ws • Xm ν • Xs (reverse ws) is the label of the conjugate.
conj-list : (ws : List L) (ν : L) → conjs-ok ws ν ≡ true →
            4 ⊢ Xs ws • (Xm ν • Xs (reverse ws)) ≈ Xm (star ws ν)
conj-list []       ν h = trans left-unit right-unit
conj-list (w ∷ ws) ν h = begin
  (Xm w • Xs ws) • (Xm ν • Xs (reverse (w ∷ ws)))
    ≈⟨ cong refl (cong refl (≡→≈ (Eq.cong Xs (unfold-reverse w ws)))) ⟩
  (Xm w • Xs ws) • (Xm ν • Xs (reverse ws ++ [ w ]))
    ≈⟨ cong refl (cong refl (trans (Xs-++ (reverse ws) [ w ]) (cong refl right-unit))) ⟩
  (Xm w • Xs ws) • (Xm ν • (Xs (reverse ws) • Xm w))
    ≈⟨ assoc ⟩
  Xm w • (Xs ws • (Xm ν • (Xs (reverse ws) • Xm w)))
    ≈⟨ cong refl (cong refl (sym assoc)) ⟩
  Xm w • (Xs ws • ((Xm ν • Xs (reverse ws)) • Xm w))
    ≈⟨ cong refl (sym assoc) ⟩
  Xm w • ((Xs ws • (Xm ν • Xs (reverse ws))) • Xm w)
    ≈⟨ cong refl (cong (conj-list ws ν (∧ʳ {conj-ok w (star ws ν)} h)) refl) ⟩
  Xm w • (Xm (star ws ν) • Xm w)
    ≈⟨ X-conj w (star ws ν) (∧ˡ h) ⟩
  Xm (c3 w (star ws ν))
    ∎

------------------------------------------------------------------------
-- Every label is a word of symbols

-- The word of symbols of a label, along the closure tree (with fuel
-- for its depth).
ψf : ℕ → L → Word Sch
ψf zero    μ = base-word
ψf (suc n) μ = [ sym-of μ ]ʷ • (ψf n (par μ) • [ inv-sym (sym-of μ) ]ʷ)

ψ : L → Word Sch
ψ μ = ψf (dep μ) μ

private
  closure-sound : (μ : L) → cstep μ (dep μ) ≡ true
  closure-sound μ = allFin-sound 105 closure-ok closure-all μ

cl : (n : ℕ) (μ : L) → dep μ ≡ n → 4 ⊢ Xm μ ≈ Xs (Φ* (ψf n μ))
cl zero μ e = at (==ᴸ-sound μ μ₀ (Eq.subst (λ k → cstep μ k ≡ true) e (closure-sound μ)))
  where
  at : μ ≡ μ₀ → 4 ⊢ Xm μ ≈ Xs (Φ* base-word)
  at Eq.refl = trans (sym right-unit) (sym base-ok)
cl (suc n) μ e = begin
  Xm μ
    ≈⟨ ≡→≈ (Eq.cong Xm (Eq.sym (==ᴸ-sound (star W p) μ (∧ʳ {conjs-ok W p} h′)))) ⟩
  Xm (star W p)
    ≈⟨ sym (conj-list W p (∧ˡ h′)) ⟩
  Xs W • (Xm p • Xs (reverse W))
    ≈⟨ cong refl (cong (cl n p (ℕP.≡ᵇ⇒≡ (dep p) n (T-true (∧ˡ h)))) (rev-ok s)) ⟩
  Xs W • (Xs (Φ* (ψf n p)) • Xs (Φ (inv-sym s)))
    ≈⟨ cong refl (sym (Xs-++ (Φ* (ψf n p)) (Φ (inv-sym s)))) ⟩
  Xs W • Xs (Φ* (ψf n p) ++ Φ (inv-sym s))
    ≈⟨ sym (Xs-++ W (Φ* (ψf n p) ++ Φ (inv-sym s))) ⟩
  Xs (Φ* (ψf (suc n) μ))
    ∎
  where
  s = sym-of μ
  p = par μ
  W = Φ s
  h : cstep μ (suc n) ≡ true
  h = Eq.subst (λ k → cstep μ k ≡ true) e (closure-sound μ)
  h′ : (conjs-ok W p ∧ (star W p ==ᴸ μ)) ≡ true
  h′ = ∧ʳ {dep p ≡ᵇ n} h

-- A word of labels as a word of symbols.
ψ* : List L → Word Sch
ψ* []       = ε
ψ* (μ ∷ ws) = ψ μ • ψ* ws

ψ*-ok : (ws : List L) → 4 ⊢ Xs ws ≈ Xs (Φ* (ψ* ws))
ψ*-ok []       = refl
ψ*-ok (μ ∷ ws) =
  trans (cong (cl (dep μ) μ Eq.refl) (ψ*-ok ws)) (sym (Xs-++ (Φ* (ψ μ)) (Φ* (ψ* ws))))

------------------------------------------------------------------------
-- The relations of EvenRS 8 carry over

Φ*-cong : {u v : Word Sch} → PB._≈_ _RS,_===_ u v → 4 ⊢ Xs (Φ* u) ≈ Xs (Φ* v)
Φ*-cong PB.refl                    = refl
Φ*-cong (PB.sym e)                 = sym (Φ*-cong e)
Φ*-cong (PB.trans e e′)            = trans (Φ*-cong e) (Φ*-cong e′)
Φ*-cong (PB.cong {w = x} {w' = x′} {v = y} {v' = y′} e e′) =
  trans (Xs-++ (Φ* x) (Φ* y))
    (trans (cong (Φ*-cong e) (Φ*-cong e′)) (sym (Xs-++ (Φ* x′) (Φ* y′))))
Φ*-cong (PB.assoc {w = x} {v = y} {u = z}) = ≡→≈ (Eq.cong Xs (++-assoc (Φ* x) (Φ* y) (Φ* z)))
Φ*-cong PB.left-unit               = refl
Φ*-cong (PB.right-unit {w = x})    = ≡→≈ (Eq.cong Xs (++-identityʳ (Φ* x)))
Φ*-cong (PB.axiom r)               = R-rel r

------------------------------------------------------------------------
-- Semantics

Xs-sem : (ws : List L) → ⟦ Xs ws ⟧ ≐ mF* ws
Xs-sem []       x = Eq.refl
Xs-sem (l ∷ ws) = ⨾-cong (Xm-sem l) (Xs-sem ws)

Φ-act : (x : Sch) (i : Fin 8) → mF* (Φ x) (enc8 i) ≡ enc8 (SymI.⟦ f x ⟧ ⟨$⟩ʳ i)
Φ-act x i =
  eqV-sound (mF* (Φ x) (enc8 i)) (enc8 (SymI.⟦ f x ⟧ ⟨$⟩ʳ i))
    (allFin-sound 8 (λ j → eqV (mF* (Φ x) (enc8 j)) (enc8 (SymI.⟦ f x ⟧ ⟨$⟩ʳ j))) (Φ-act-ok x) i)

Φ*-act : (w : Word Sch) (i : Fin 8) → mF* (Φ* w) (enc8 i) ≡ enc8 (SymI.⟦ (f ʷ) w ⟧ ⟨$⟩ʳ i)
Φ*-act [ x ]ʷ   i = Φ-act x i
Φ*-act ε       i = Eq.refl
Φ*-act (u • v) i =
  Eq.trans (mF*-++ (Φ* u) (Φ* v) (enc8 i))
    (Eq.trans (Eq.cong (mF* (Φ* v)) (Φ*-act u i)) (Φ*-act v (SymI.⟦ (f ʷ) u ⟧ ⟨$⟩ʳ i)))

------------------------------------------------------------------------
-- Faithfulness

-- Two words of labels with the same function are equal.
cfaith : (a b : List L) → ⟦ Xs a ⟧ ≐ ⟦ Xs b ⟧ → 4 ⊢ Xs a ≈ Xs b
cfaith a b e =
  trans (ψ*-ok a) (trans (Φ*-cong (rs-complete (ψ* a) (ψ* b) same)) (sym (ψ*-ok b)))
  where
  at : (ws : List L) (i : Fin 8) → ⟦ Xs ws ⟧ (enc8 i) ≡ enc8 (SymI.⟦ (f ʷ) (ψ* ws) ⟧ ⟨$⟩ʳ i)
  at ws i =
    Eq.trans (sound (ψ*-ok ws) (enc8 i))
      (Eq.trans (Xs-sem (Φ* (ψ* ws)) (enc8 i)) (Φ*-act (ψ* ws) i))
  same : ∀ i → SymI.⟦ (f ʷ) (ψ* a) ⟧ ⟨$⟩ʳ i ≡ SymI.⟦ (f ʷ) (ψ* b) ⟧ ⟨$⟩ʳ i
  same i = enc8-injective (Eq.trans (Eq.sym (at a i)) (Eq.trans (e (enc8 i)) (at b i)))
