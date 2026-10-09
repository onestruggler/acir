------------------------------------------------------------------------
-- Presentations of groups
--
-- Tools for the edges at a level with pivot p.
--
-- * Units ±1, and their sums and differences with 0.
-- * States that are I from column p on (AtI p), as Algorithm 1 leaves
--   a unit pivot column, and words whose letters act below p (Under
--   p): along such a word every state is I from p on, so lies below
--   every level with pivot p.
-- * Pair columns, units at c < d and 0 elsewhere: their syllable is
--   that of the pair (c, d), and if H_[c,d]·M has such a syllable,
--   the edge H_[c,d] out of M follows from the edge X_[0,c] (as out
--   of I, BaseCase).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Real-Clifford+CH-TwoLevel.EdgeTools {n : ℕ} where

open import Data.Bool.Base using (true ; false)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; oddᶻ ; rbit ; √2ᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; Minimal ; Odd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Hᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; Beyond ; level-below)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (syl ; top ; Beyond-actM ; actV-e-beyond)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (H-H ; flip-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n} using (Hs ; Xs ; HsT ; XsT)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; path-ε ; Low)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n} using (via)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (path-normal ; syl-of)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} lt = recompute (a FinP.<? b) lt

  true≢false : true ≢ false
  true≢false ()

------------------------------------------------------------------------
-- Units

Unit1 : Z → Set
Unit1 u = u ≡ ZR.1# ⊎ u ≡ ZR.- ZR.1#

unit-odd : ∀ {u} → Unit1 u → Odd u
unit-odd (inj₁ ≡.refl) = ≡.refl
unit-odd (inj₂ ≡.refl) = ≡.refl

unit≢0 : ∀ {u} → Unit1 u → u ≢ ZR.0#
unit≢0 (inj₁ ≡.refl) ()
unit≢0 (inj₂ ≡.refl) ()

unit-rbit : ∀ {u} → Unit1 u → rbit u ≡ false
unit-rbit (inj₁ ≡.refl) = ≡.refl
unit-rbit (inj₂ ≡.refl) = ≡.refl

unit-+0 : ∀ {u} → Unit1 u → Unit1 (u ZR.+ ZR.0#)
unit-+0 (inj₁ ≡.refl) = inj₁ ≡.refl
unit-+0 (inj₂ ≡.refl) = inj₂ ≡.refl

unit-0+ : ∀ {u} → Unit1 u → Unit1 (ZR.0# ZR.+ u)
unit-0+ (inj₁ ≡.refl) = inj₁ ≡.refl
unit-0+ (inj₂ ≡.refl) = inj₂ ≡.refl

unit--0 : ∀ {u} → Unit1 u → Unit1 (u ZR.- ZR.0#)
unit--0 (inj₁ ≡.refl) = inj₁ ≡.refl
unit--0 (inj₂ ≡.refl) = inj₂ ≡.refl

unit-0- : ∀ {u} → Unit1 u → Unit1 (ZR.0# ZR.- u)
unit-0- (inj₁ ≡.refl) = inj₂ ≡.refl
unit-0- (inj₂ ≡.refl) = inj₁ ≡.refl

------------------------------------------------------------------------
-- States that are I from column p on, and words acting below p

AtI : Fin n → Matrix n n D → Set
AtI p M = Beyond p M × col M p ≡ col 𝕀 p

Under : Fin n → Word (Gen n) → Set
Under p [ g ]ʷ = top g < p
Under p ε = ⊤
Under p (u • v) = Under p u × Under p v

AtI-act : (g : Gen n) {p : Fin n} {M : Matrix n n D} → top g < p → AtI p M → AtI p (actM g M)
AtI-act g {p} {M} tg (be , cp) =
  Beyond-actM g {p} {M} (ℕP.<⇒≤ tg) be ,
  ≡.trans (col-actM g M p) (≡.trans (≡.cong (actV g) cp) (actV-e-beyond g {top g} {p} FinP.≤-refl tg))

AtI-actʷ : (w : Word (Gen n)) {p : Fin n} {M : Matrix n n D} → Under p w → AtI p M → AtI p (actMʷ w M)
AtI-actʷ [ g ]ʷ {p} {M} h a = AtI-act g {p} {M} h a
AtI-actʷ ε _ a = a
AtI-actʷ (u • v) {p} {M} (hu , hv) a = AtI-actʷ u {p} {actMʷ v M} hu (AtI-actʷ v {p} {M} hv a)

-- Every letter of the word joins states below any level with pivot p.
under-below : (w : Word (Gen n)) {p : Fin n} {M : Matrix n n D} → Under p w → AtI p M →
              ∀ k m → Low (suc (toℕ p) , k , m) w M
under-below [ g ]ʷ {p} {M} h a k m =
  level-below M (proj₂ a) (proj₁ a) k m ,
  level-below (actM g M) (proj₂ (AtI-act g {p} {M} h a)) (proj₁ (AtI-act g {p} {M} h a)) k m
under-below ε _ _ k m = tt
under-below (u • v) {p} {M} (hu , hv) a k m =
  under-below v {p} {M} hv a k m , under-below u {p} {actMʷ v M} hu (AtI-actʷ v {p} {M} hv a) k m

-- The symmetric words.
Under-XsT : ∀ {p} (a b : Fin n) (t : Tri (a < b) (a ≡ b) (b < a)) → a < p → b < p → Under p (XsT a b t)
Under-XsT a b (tri< _ _ _) ap bp = bp
Under-XsT a b (tri≈ _ _ _) ap bp = tt
Under-XsT a b (tri> _ _ _) ap bp = ap

Under-Xs : ∀ {p} (a b : Fin n) → a < p → b < p → Under p (Xs a b)
Under-Xs a b = Under-XsT a b (FinP.<-cmp a b)

Under-HsT : ∀ {p} (a b : Fin n) (t : Tri (a < b) (a ≡ b) (b < a)) → a < p → b < p → Under p (HsT a b t)
Under-HsT a b (tri< _ _ _) ap bp = bp
Under-HsT a b (tri≈ _ _ _) ap bp = tt
Under-HsT a b (tri> _ _ _) ap bp = ap , ap , ap

Under-Hs : ∀ {p} (a b : Fin n) → a < p → b < p → Under p (Hs a b)
Under-Hs a b = Under-HsT a b (FinP.<-cmp a b)

------------------------------------------------------------------------
-- Pair columns

module Pair (w : Vec Z n) {c d : Fin n} (cd : c < d) (uc : Unit1 (w ! c)) (ud : Unit1 (w ! d))
            (z : ∀ x → x ≢ c → x ≢ d → w ! x ≡ ZR.0#) where

  min : Minimal 1 w
  min = inj₂ (c , unit-odd uc)

  first : firstOdd w ≡ just c
  first = firstOdd-char w (unit-odd uc)
    (λ x x<c → ≡.cong oddᶻ (z x (λ { ≡.refl → FinP.<-irrefl ≡.refl x<c })
                                (λ { ≡.refl → FinP.<-irrefl ≡.refl (FinP.<-trans x<c cd) })))

  next : nextSame c w ≡ just d
  next = nextSame-char w cd (unit-odd ud , ≡.trans (unit-rbit ud) (≡.sym (unit-rbit uc)))
    (λ x c<x x<d (ox , _) → true≢false (≡.trans (≡.sym ox)
       (≡.cong oddᶻ (z x (λ { ≡.refl → FinP.<-irrefl ≡.refl c<x }) (λ { ≡.refl → FinP.<-irrefl ≡.refl x<d })))))

  -- The syllable of a state whose pivot column is w / √2.
  syl≡ : (M : Matrix n n D) {q : Fin n} → pivot M ≡ just q → col M q ≡ scV 1 w → syl M ≡ pairSyl c d cd
  syl≡ M {q} pv eq = ≡.trans (syl-of M pv 1 w eq min) (sylData-pair {p = q} 0 w first next cd)

-- H_[c,d] takes a unit at c or d, and 0 elsewhere, to a pair column.
H-pair : (u : Vec Z n) {c d : Fin n} → c ≢ d → (∀ x → x ≢ c → x ≢ d → u ! x ≡ ZR.0#) →
         (Unit1 (u ! c) × u ! d ≡ ZR.0#) ⊎ (u ! c ≡ ZR.0# × Unit1 (u ! d)) →
         Unit1 (Hᶻ c d u ! c) × Unit1 (Hᶻ c d u ! d) × (∀ x → x ≢ c → x ≢ d → Hᶻ c d u ! x ≡ ZR.0#)
H-pair u {c} {d} c≢d z units = at-c units , at-d units , off
  where
  Hc : Hᶻ c d u ! c ≡ u ! c ZR.+ u ! d
  Hc = set₂-a c d _ _ _
  Hd : Hᶻ c d u ! d ≡ u ! c ZR.- u ! d
  Hd = set₂-b c d _ _ _ c≢d
  at-c : (Unit1 (u ! c) × u ! d ≡ ZR.0#) ⊎ (u ! c ≡ ZR.0# × Unit1 (u ! d)) → Unit1 (Hᶻ c d u ! c)
  at-c (inj₁ (uc , d0)) = ≡.subst Unit1 (≡.sym (≡.trans Hc (≡.cong (λ t → u ! c ZR.+ t) d0))) (unit-+0 uc)
  at-c (inj₂ (c0 , ud)) = ≡.subst Unit1 (≡.sym (≡.trans Hc (≡.cong (λ t → t ZR.+ u ! d) c0))) (unit-0+ ud)
  at-d : (Unit1 (u ! c) × u ! d ≡ ZR.0#) ⊎ (u ! c ≡ ZR.0# × Unit1 (u ! d)) → Unit1 (Hᶻ c d u ! d)
  at-d (inj₁ (uc , d0)) = ≡.subst Unit1 (≡.sym (≡.trans Hd (≡.cong (λ t → u ! c ZR.- t) d0))) (unit--0 uc)
  at-d (inj₂ (c0 , ud)) = ≡.subst Unit1 (≡.sym (≡.trans Hd (≡.cong (λ t → t ZR.- u ! d) c0))) (unit-0- ud)
  off : ∀ x → x ≢ c → x ≢ d → Hᶻ c d u ! x ≡ ZR.0#
  off x x≢c x≢d = ≡.trans (set₂-≢ c d _ _ _ x≢c x≢d)
                    (≡.trans (VecP.lookup-map x (√2ᶻ ZR.*_) u) (≡.trans (≡.cong (√2ᶻ ZR.*_) (z x x≢c x≢d)) (ZR.zeroʳ √2ᶻ)))

-- The edge H_[c,d] out of M, when the syllable of H_[c,d]·M is that of
-- the pair (c, d), given the edge X_[0,c] out of M.
edge-H-pair : (M : Matrix n n D) .(o : ColOrth M) (c d : Fin n) .(cd : c < d) {q : Fin n} →
              pivot (actM (H-gen c d cd) M) ≡ just q → syl (actM (H-gen c d cd) M) ≡ pairSyl c d cd →
              ((pos : 0 ℕ.< toℕ c) → Path (X (zeroOf c) c (zeroOf-< c pos)) M o) → Path [ H-gen c d cd ]ʷ M o
edge-H-pair M o c d cd pv syl≡ xedge = by-c (toℕ c ℕP.≟ 0)
  where
  cd′ = rc cd
  HM = actM (H-gen c d cd) M
  by-c : Dec (toℕ c ≡ 0) → Path [ H-gen c d cd ]ʷ M o
  by-c (yes c0) =
    via (H-gen c d cd) M o (syl HM) ε (path-normal HM (ColOrth-actMʷ [ H-gen c d cd ]ʷ o) pv)
        (trans (cleft refl′ (≡.trans syl≡ (pairSyl-0 c d cd c0))) (H-H cd)) (path-ε M o)
  by-c (no c≢0) =
    via (H-gen c d cd) M o (syl HM) (X z c 0<c) (path-normal HM (ColOrth-actMʷ [ H-gen c d cd ]ʷ o) pv) rel (xedge pos)
    where
    pos : 0 ℕ.< toℕ c
    pos = ℕP.n≢0⇒n>0 c≢0
    z = zeroOf c
    0<c : z < c
    0<c = zeroOf-< c pos
    0<d = ℕP.<-trans 0<c cd′
    c4′ : H z d 0<d • X z c 0<c ≈ X z c 0<c • H c d cd
    c4′ = flip-X 0<c (axiom (c4 0<c cd′))
    rel : syl HM • H c d cd ≈ X z c 0<c
    rel = begin
      syl HM • H c d cd                                      ≈⟨ cleft refl′ (≡.trans syl≡ (pairSyl-s c d cd pos)) ⟩
      (H z d 0<d • X z c 0<c) • H c d cd                     ≈⟨ cleft c4′ ⟩
      (X z c 0<c • H c d cd) • H c d cd                      ≈⟨ assoc ⟩
      X z c 0<c • (H c d cd • H c d cd)                      ≈⟨ cright H-H cd ⟩
      X z c 0<c • ε                                          ≈⟨ right-unit ⟩
      X z c 0<c                                              ∎
