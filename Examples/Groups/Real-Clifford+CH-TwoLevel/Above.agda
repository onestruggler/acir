------------------------------------------------------------------------
-- Presentations of groups
--
-- Edges of generators that reach above the pivot.
--
-- If s agrees with I beyond p and g moves the basis vector e_d with
-- d > p (Z_[d], X_[c,d], H_[c,d]), then g·s has pivot d, and Algorithm
-- 1 removes g in one syllable as from I: Z_[d], X_[c,d], or H_[0,d]
-- X_[0,c] = X_[0,c] H_[c,d] (so the edge H_[c,d] out of s follows from
-- the edge X_[0,c]).  The edges close whatever the level of s.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Above {n : ℕ} where

open import Data.Bool.Base using (true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; scV-! ; Minimal)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; pivot-char ; Beyond)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable
  using (syl ; top ; Beyond-actM ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (Z-Z ; X-X ; H-H ; flip-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; path-ε)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n} using (via)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (path-normal ; syl-of ; ne-𝕀 ; ne-𝕀-at)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  e-a : (a : Fin n) → eᶻ a ! a ≡ ZR.1#
  e-a a = ≡.trans (eᶻ-! a a) (eδ-refl a)

  e-≢ : {a x : Fin n} → x ≢ a → eᶻ a ! x ≡ ZR.0#
  e-≢ {a} {x} x≢a = ≡.trans (eᶻ-! a x) (eδ-≢ x≢a)

  -1≢1 : ZR.- ZR.1# ≢ ZR.1#
  -1≢1 ()

  0≢1 : ZR.0# ≢ ZR.1#
  0≢1 ()

  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} lt = recompute (a FinP.<? b) lt

module At (s : Matrix n n D) .(o : ColOrth s) (p : Fin n) (be : Beyond p s) where

  private
    -- Beyond p, and so beyond any d > p.
    be-d : ∀ {d} → p < d → Beyond d s
    be-d p<d x d<x = be x (ℕP.<-trans p<d d<x)

    col-g : (g : Gen n) (c : Fin n) → p < c → col (actM g s) c ≡ actV g (scV 0 (eᶻ c))
    col-g g c p<c = ≡.trans (col-actM g s c) (≡.cong (actV g) (≡.trans (be c p<c) (col𝕀≡ c)))

    pivot-g : (g : Gen n) (d : Fin n) → p < d → top g Fin.≤ d → col (actM g s) d ≢ col 𝕀 d → pivot (actM g s) ≡ just d
    pivot-g g d p<d tg ne = pivot-char (actM g s) ne (Beyond-actM g {M = s} tg (be-d p<d))

  ----------------------------------------------------------------------
  -- Z_[d]

  edge-Z : (d : Fin n) → p < d → Path [ Z-gen d ]ʷ s o
  edge-Z d p<d = via (Z-gen d) s o (syl M) ε (path-normal M (ColOrth-actMʷ [ Z-gen d ]ʷ o) pv)
                   (trans (cleft refl′ syl≡) Z-Z) (path-ε s o)
    where
    M = actM (Z-gen d) s
    w = Zᶻ d (eᶻ d)
    col≡ : col M d ≡ scV 0 w
    col≡ = ≡.trans (col-g (Z-gen d) d p<d) (actV-Z d 0 (eᶻ d))
    wd : w ! d ≡ ZR.- ZR.1#
    wd = ≡.trans (set₁-a d (ZR.- (eᶻ d ! d)) (eᶻ d)) (≡.cong ZR.-_ (e-a d))
    w≢ : ∀ {x} → x ≢ d → w ! x ≡ ZR.0#
    w≢ {x} x≢d = ≡.trans (set₁-≢ d (ZR.- (eᶻ d ! d)) (eᶻ d) x≢d) (e-≢ x≢d)
    min : Minimal 0 w
    min = inj₁ ≡.refl
    pv : pivot M ≡ just d
    pv = pivot-g (Z-gen d) d p<d FinP.≤-refl
           (ne-𝕀-at M d 0 w col≡ min d (λ e → -1≢1 (≡.trans (≡.sym wd) (≡.trans e (e-a d)))))
    fo : firstOdd w ≡ just d
    fo = firstOdd-char w (≡.cong oddᶻ wd) (λ x x<d → ≡.cong oddᶻ (w≢ (λ { ≡.refl → FinP.<-irrefl ≡.refl x<d })))
    syl≡ : syl M ≡ Zʷ d
    syl≡ = ≡.trans (syl-of M pv 0 w col≡ min) (≡.trans (sylData-unit≡ w fo) (≡.cong (λ z → Zτ d (negᶻ z)) wd))

  ----------------------------------------------------------------------
  -- X_[c,d]

  edge-X : (c d : Fin n) .(cd : c < d) → p < d → Path [ X-gen c d cd ]ʷ s o
  edge-X c d cd p<d =
    via (X-gen c d cd) s o (syl M) ε (path-normal M (ColOrth-actMʷ [ X-gen c d cd ]ʷ o) pv)
        (trans (cleft trans (refl′ syl≡) right-unit) (X-X cd)) (path-ε s o)
    where
    c≢d : c ≢ d
    c≢d = <⇒≢ cd
    M = actM (X-gen c d cd) s
    w = Xᶻ c d (eᶻ d)
    col≡ : col M d ≡ scV 0 w
    col≡ = ≡.trans (col-g (X-gen c d cd) d p<d) (actV-X c d cd 0 (eᶻ d))
    -- w = e_c.
    w≡ : w ≡ eᶻ c
    w≡ = vec-ext λ x → dec-elim (x FinP.≟ c)
      (λ { ≡.refl → ≡.trans (set₂-a x d (eᶻ d ! d) (eᶻ d ! x) (eᶻ d)) (≡.trans (e-a d) (≡.sym (e-a x))) })
      (λ x≢c → dec-elim (x FinP.≟ d)
        (λ { ≡.refl → ≡.trans (set₂-b c x (eᶻ x ! x) (eᶻ x ! c) (eᶻ x) c≢d)
                               (≡.trans (e-≢ c≢d) (≡.sym (e-≢ (λ e → c≢d (≡.sym e))))) })
        (λ x≢d → ≡.trans (set₂-≢ c d (eᶻ d ! d) (eᶻ d ! c) (eᶻ d) x≢c x≢d) (≡.trans (e-≢ x≢d) (≡.sym (e-≢ x≢c)))))
    col≡′ : col M d ≡ scV 0 (eᶻ c)
    col≡′ = ≡.trans col≡ (≡.cong (scV 0) w≡)
    min : Minimal 0 (eᶻ c)
    min = inj₁ ≡.refl
    pv : pivot M ≡ just d
    pv = pivot-g (X-gen c d cd) d p<d FinP.≤-refl
           (ne-𝕀-at M d 0 (eᶻ c) col≡′ min d (λ e → 0≢1 (≡.trans (≡.sym (e-≢ (λ e′ → c≢d (≡.sym e′)))) (≡.trans e (e-a d)))))
    fo : firstOdd (eᶻ c) ≡ just c
    fo = firstOdd-char (eᶻ c) (≡.cong oddᶻ (e-a c)) (λ x x<c → ≡.cong oddᶻ (e-≢ (λ { ≡.refl → FinP.<-irrefl ≡.refl x<c })))
    syl≡ : syl M ≡ X c d cd • ε
    syl≡ = ≡.trans (syl-of M pv 0 (eᶻ c) col≡′ min)
             (≡.trans (sylData-unit< (eᶻ c) fo (rc cd)) (≡.cong (λ z → X c d cd • Zτ c (negᶻ z)) (e-a c)))

  ----------------------------------------------------------------------
  -- H_[c,d], given the edges X_[0,c]

  edge-H : (c d : Fin n) .(cd : c < d) → p < d →
           (∀ (x y : Fin n) .(xy : x < y) → Path [ X-gen x y xy ]ʷ s o) → Path [ H-gen c d cd ]ʷ s o
  edge-H c d cd p<d xedge = by-c (toℕ c ℕP.≟ 0)
    where
    cd′ = rc cd
    c≢d : c ≢ d
    c≢d = <⇒≢ cd
    M = actM (H-gen c d cd) s
    w = Hᶻ c d (eᶻ d)
    col≡ : col M d ≡ scV 1 w
    col≡ = ≡.trans (col-g (H-gen c d cd) d p<d) (actV-H c d cd 0 (eᶻ d))
    wc : w ! c ≡ ZR.1#
    wc = ≡.trans (set₂-a c d _ _ _) (≡.cong₂ ZR._+_ (e-≢ c≢d) (e-a d))
    wd : w ! d ≡ ZR.- ZR.1#
    wd = ≡.trans (set₂-b c d _ _ _ c≢d) (≡.cong₂ ZR._-_ (e-≢ c≢d) (e-a d))
    w≢ : ∀ {x} → x ≢ c → x ≢ d → w ! x ≡ ZR.0#
    w≢ {x} x≢c x≢d = ≡.trans (set₂-≢ c d _ _ _ x≢c x≢d)
                       (≡.trans (VecP.lookup-map x (√2ᶻ ZR.*_) (eᶻ d)) (≡.cong (√2ᶻ ZR.*_) (e-≢ x≢d)))
    min : Minimal 1 w
    min = inj₂ (c , ≡.cong oddᶻ wc)
    pv : pivot M ≡ just d
    pv = pivot-g (H-gen c d cd) d p<d FinP.≤-refl (ne-𝕀 M d 0 w col≡ min)
    fo : firstOdd w ≡ just c
    fo = firstOdd-char w (≡.cong oddᶻ wc) (λ x x<c → ≡.cong oddᶻ (w≢ (λ { ≡.refl → FinP.<-irrefl ≡.refl x<c })
                                                              (λ { ≡.refl → FinP.<-irrefl ≡.refl (FinP.<-trans x<c cd′) })))
    true≢false : true ≢ false
    true≢false ()
    nx : nextSame c w ≡ just d
    nx = nextSame-char w cd′ (≡.cong oddᶻ wd , ≡.trans (≡.cong rbit wd) (≡.sym (≡.cong rbit wc)))
           (λ x c<x x<d (ox , _) → true≢false (≡.trans (≡.sym ox)
              (≡.cong oddᶻ (w≢ (λ { ≡.refl → FinP.<-irrefl ≡.refl c<x }) (λ { ≡.refl → FinP.<-irrefl ≡.refl x<d })))))
    syl≡ : syl M ≡ pairSyl c d cd
    syl≡ = ≡.trans (syl-of M pv 1 w col≡ min) (sylData-pair {p = d} 0 w fo nx cd′)
    by-c : Dec (toℕ c ≡ 0) → Path [ H-gen c d cd ]ʷ s o
    by-c (yes c0) =
      via (H-gen c d cd) s o (syl M) ε (path-normal M (ColOrth-actMʷ [ H-gen c d cd ]ʷ o) pv)
          (trans (cleft refl′ (≡.trans syl≡ (pairSyl-0 c d cd c0))) (H-H cd)) (path-ε s o)
    by-c (no c≢0) =
      via (H-gen c d cd) s o (syl M) (X z c 0<c) (path-normal M (ColOrth-actMʷ [ H-gen c d cd ]ʷ o) pv) rel (xedge z c 0<c)
      where
      pos : 0 ℕ.< toℕ c
      pos = ℕP.n≢0⇒n>0 c≢0
      z = zeroOf c
      0<c : z < c
      0<c = zeroOf-< c pos
      0<d = ℕP.<-trans 0<c cd′
      c4′ : H z d 0<d • X z c 0<c ≈ X z c 0<c • H c d cd
      c4′ = flip-X 0<c (axiom (c4 0<c cd′))
      rel : syl M • H c d cd ≈ X z c 0<c
      rel = begin
        syl M • H c d cd                                       ≈⟨ cleft refl′ (≡.trans syl≡ (pairSyl-s c d cd pos)) ⟩
        (H z d 0<d • X z c 0<c) • H c d cd                     ≈⟨ cleft c4′ ⟩
        (X z c 0<c • H c d cd) • H c d cd                      ≈⟨ assoc ⟩
        X z c 0<c • (H c d cd • H c d cd)                      ≈⟨ cright H-H cd ⟩
        X z c 0<c • ε                                          ≈⟨ right-unit ⟩
        X z c 0<c                                              ∎
