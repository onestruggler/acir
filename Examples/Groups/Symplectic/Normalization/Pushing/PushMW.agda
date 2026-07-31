------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing the B-side residual Wof vb (PushBvcz) through an M box:
--
--   [ m ]ᵐ • Wof vb ≈ dir ↑ • [ m' ]ᵐ
--
-- Recursion on vb.  Wof (x∷v) = Ex • Wof v ↑ • Ex • CZ^k; Ex and CZ^k are
-- Gen-2 words (padded), pushed by PushMword.push-Mʷ-suc; the middle
-- Wof v ↑ recurses through the tail M box (cong↑) and commutes past the
-- bottom D box (push-lift-M).  The base Wof [] = CZ is push-Mʷ2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushMW (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (∃ ; ∃-syntax ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; _∷_ ; [])
import Relation.Binary.PropositionalEquality as Eq

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime using (comm-dbox-w↑↑)
open import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime using (No-Top-H ; ntH-CZ ; push-D-w)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime using (CZ^-↓ᵏ)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMword p-2 p-prime using (push-Mʷ2 ; push-Mʷ-suc)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBvcz p-2 p-prime using (Wof ; dir-k)

open import Notations
open import Word.Base using (Word ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

-- Ex {Gen 2} padded is Ex; definitional (wmap over Ex's explicit gates).
Ex-↓ᵏ : ∀ {m} → Ex {0} ↓ᵏ (₁₊ m) Eq.≡ Ex {₁₊ m}
Ex-↓ᵏ = Eq.refl

mutual
  push-MW : ∀ {m} (mm : M (₂₊ m)) (vb : Vec B m) → let open PB ((₂₊ m) QRel,_===_) in
    ∃[ dir ] ∃[ mm' ] ([ mm ]ᵐ • Wof vb ≈ dir ↑ • [ mm' ]ᵐ)
  push-MW {0} (d₀ ∷ [] , e) [] =
    let (e' , dir , d₀') = push-D-w d₀ CZ ntH-CZ
    in dir , (d₀' ∷ [] , e + - e') , push-Mʷ2 d₀ e CZ ntH-CZ
  push-MW {₁₊ m} mm (x ∷ v) = (dir1 • dir2 • dir3 • dir4) , mm4 , chain
    where
    open PB ((₃₊ m) QRel,_===_) ; open PP ((₃₊ m) QRel,_===_) ; open SR word-setoid

    p1 = push-Mʷ-suc mm Ex
    dir1 = proj₁ p1 ; mm1 = proj₁ (proj₂ p1)
    eq1 : [ mm ]ᵐ • Ex ≈ dir1 ↑ • [ mm1 ]ᵐ
    eq1 = proj₂ (proj₂ p1)

    p2 = push-lift-M mm1 v
    dir2 = proj₁ p2 ; mm2 = proj₁ (proj₂ p2)
    eq2 : [ mm1 ]ᵐ • (Wof v ↑) ≈ dir2 ↑ • [ mm2 ]ᵐ
    eq2 = proj₂ (proj₂ p2)

    p3 = push-Mʷ-suc mm2 Ex
    dir3 = proj₁ p3 ; mm3 = proj₁ (proj₂ p3)
    eq3 : [ mm2 ]ᵐ • Ex ≈ dir3 ↑ • [ mm3 ]ᵐ
    eq3 = proj₂ (proj₂ p3)

    p4 = push-Mʷ-suc mm3 (CZ^ (dir-k x))
    dir4 = proj₁ p4 ; mm4 = proj₁ (proj₂ p4)
    eq4 : [ mm3 ]ᵐ • CZ^ (dir-k x) ≈ dir4 ↑ • [ mm4 ]ᵐ
    eq4 = trans (cright (refl' (Eq.sym (CZ^-↓ᵏ (dir-k x) (₁₊ m))))) (proj₂ (proj₂ p4))

    seq : ∀ (mmA mmB mmC : M (₃₊ m)) (da db : Word (Gen (₂₊ m)))
            {P Q : Word (Gen (₃₊ m))} →
          [ mmA ]ᵐ • P ≈ da ↑ • [ mmB ]ᵐ → [ mmB ]ᵐ • Q ≈ db ↑ • [ mmC ]ᵐ →
          [ mmA ]ᵐ • (P • Q) ≈ (da • db) ↑ • [ mmC ]ᵐ
    seq mmA mmB mmC da db {P} {Q} h1 h2 = begin
      [ mmA ]ᵐ • (P • Q)         ≈⟨ sym assoc ⟩
      ([ mmA ]ᵐ • P) • Q         ≈⟨ cleft h1 ⟩
      (da ↑ • [ mmB ]ᵐ) • Q      ≈⟨ assoc ⟩
      da ↑ • ([ mmB ]ᵐ • Q)      ≈⟨ cright h2 ⟩
      da ↑ • (db ↑ • [ mmC ]ᵐ)   ≈⟨ sym assoc ⟩
      (da • db) ↑ • [ mmC ]ᵐ     ∎

    chain : [ mm ]ᵐ • Wof (x ∷ v) ≈ (dir1 • dir2 • dir3 • dir4) ↑ • [ mm4 ]ᵐ
    chain = seq mm mm1 mm4 dir1 (dir2 • dir3 • dir4) eq1
              (seq mm1 mm2 mm4 dir2 (dir3 • dir4) eq2
                (seq mm2 mm3 mm4 dir3 dir4 eq3 eq4))

  -- Push Wof v ↑ through an M (₃₊ m) box: recurse through the tail, then
  -- commute the escaping residual past the bottom D box.
  push-lift-M : ∀ {m} (mm : M (₃₊ m)) (v : Vec B m) → let open PB ((₃₊ m) QRel,_===_) in
    ∃[ dir ] ∃[ mm' ] ([ mm ]ᵐ • (Wof v ↑) ≈ dir ↑ • [ mm' ]ᵐ)
  push-lift-M {m} (d₀ ∷ dr , e) v = (dir' ↑) , (d₀ ∷ proj₁ tl2 , proj₂ tl2) , body
    where
    open PB ((₃₊ m) QRel,_===_) ; open PP ((₃₊ m) QRel,_===_) ; open SR word-setoid
    rec  = push-MW (dr , e) v
    dir' = proj₁ rec ; tl2 = proj₁ (proj₂ rec)
    receq = proj₂ (proj₂ rec)

    body : [ (d₀ ∷ dr , e) ]ᵐ • (Wof v ↑) ≈ (dir' ↑) ↑ • [ (d₀ ∷ proj₁ tl2 , proj₂ tl2) ]ᵐ
    body = begin
      ([ d₀ ]ᵈ • [ (dr , e) ]ᵐ ↑) • (Wof v ↑)   ≈⟨ assoc ⟩
      [ d₀ ]ᵈ • (([ (dr , e) ]ᵐ • Wof v) ↑)      ≈⟨ cright (lemma-cong↑ _ _ receq) ⟩
      [ d₀ ]ᵈ • ((dir' ↑ • [ tl2 ]ᵐ) ↑)          ≈⟨ sym assoc ⟩
      ([ d₀ ]ᵈ • dir' ↑ ↑) • [ tl2 ]ᵐ ↑          ≈⟨ cleft (comm-dbox-w↑↑ d₀ dir') ⟩
      (dir' ↑ ↑ • [ d₀ ]ᵈ) • [ tl2 ]ᵐ ↑          ≈⟨ assoc ⟩
      dir' ↑ ↑ • ([ d₀ ]ᵈ • [ tl2 ]ᵐ ↑)          ∎
