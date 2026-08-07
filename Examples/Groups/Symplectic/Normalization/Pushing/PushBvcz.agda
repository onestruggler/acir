------------------------------------------------------------------------
-- Presentations of groups
--
-- The B-side cascade: pushing CZ through a lifted B-vector leaves the
-- vector unchanged and emits a residual word W:
--
--   [ vb ]ᵛᵇ ↑ • CZ ≈ W • [ vb ]ᵛᵇ ↑
--
-- Induction on vb.  The head box passes CZ unchanged, emitting
-- dir = CZ02 • CZ^k (PushBcz.gen-B↑←CZ).  The CZ^k part commutes past the
-- ↑↑ tail (lemma-comm-CZᵏ-w↑↑); the CZ02 = Ex • CZ↑ • Ex part reduces its
-- inner CZ↑ to the recursive call via cong↑, with Ex commuting past the
-- ↑↑ tail (lemma-comm-Ex-w↑↑).  Residual: W(x∷v) = Ex • W(v)↑ • Ex • CZ^k.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushBvcz (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (∃-syntax ; _,_)
open import Data.Vec using (Vec ; _∷_ ; [])
open import Data.Fin using (toℕ)
import Relation.Binary.PropositionalEquality as Eq

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime
  using (lemma-comm-Ex-w↑↑ ; lemma-comm-CZᵏ-w↑↑)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBcz p-2 p-prime using (gen-B↑←CZ)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime using (CZ^-↓ᵏ)
import Examples.Groups.Symplectic.BR.Three.B-CZ p-2 p-prime as BCZ

open import Notations
open import Word.Base using (Word ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

-- BCZ.dir-of x = CZ02 • CZ^ (dir-k x).
dir-k : B → ℤ ₚ
dir-k (₀ , b)        = - b
dir-k (a@(₁₊ _) , b) = - a

dir-eq : ∀ {m} (x : B) → BCZ.dir-of x ↓ᵏ m Eq.≡ CZ02 • CZ^ (dir-k x)
dir-eq {m} (₀ , b)        = Eq.cong₂ _•_ Eq.refl (CZ^-↓ᵏ (- b) m)
dir-eq {m} (a@(₁₊ _) , b) = Eq.cong₂ _•_ Eq.refl (CZ^-↓ᵏ (- a) m)

-- The residual word emitted by pushing CZ through the lifted B-vector.
Wof : ∀ {m} → Vec B m → Word (Gen (₂₊ m))
Wof []      = CZ
Wof (x ∷ v) = Ex • Wof v ↑ • Ex • CZ^ (dir-k x)

bvec↑-cz : ∀ {m} (vb : Vec B m) → let open PB ((₂₊ m) QRel,_===_) in
  [ vb ]ᵛᵇ ↑ • CZ ≈ Wof vb • [ vb ]ᵛᵇ ↑
bvec↑-cz {0} [] = trans left-unit (sym right-unit)
  where open PB (2 QRel,_===_) ; open PP (2 QRel,_===_) ; open SR word-setoid
bvec↑-cz {₁₊ m} (x ∷ v) = proof
  where
  open PB ((₃₊ m) QRel,_===_) ; open PP ((₃₊ m) QRel,_===_) ; open SR word-setoid
  Wv  = Wof v
  recv = bvec↑-cz v
  k   = dir-k x
  Av   = [ v ]ᵛᵇ ↑ ↑
  Bb  = [ x ]ᵇ ↑
  W   = Ex • Wv ↑ • Ex • CZ^ k

  -- Av • CZ ↑ ≈ Wv ↑ • Av  (recursion, lifted once):
  Xcz : Av • CZ ↑ ≈ Wv ↑ • Av
  Xcz = lemma-cong↑ _ _ recv

  mid2 : Av • CZ02 ≈ (Ex • Wv ↑ • Ex) • Av
  mid2 = begin
    Av • CZ02                              ≈⟨ refl ⟩
    Av • (Ex • CZ ↑ • Ex)                  ≈⟨ sym assoc ⟩
    (Av • Ex) • (CZ ↑ • Ex)                ≈⟨ cleft (sym (lemma-comm-Ex-w↑↑ [ v ]ᵛᵇ)) ⟩
    (Ex • Av) • (CZ ↑ • Ex)                ≈⟨ assoc ⟩
    Ex • (Av • (CZ ↑ • Ex))                ≈⟨ cright (sym assoc) ⟩
    Ex • ((Av • CZ ↑) • Ex)                ≈⟨ cright (cleft Xcz) ⟩
    Ex • ((Wv ↑ • Av) • Ex)                ≈⟨ cright assoc ⟩
    Ex • (Wv ↑ • (Av • Ex))                ≈⟨ cright (cright (sym (lemma-comm-Ex-w↑↑ [ v ]ᵛᵇ))) ⟩
    Ex • (Wv ↑ • (Ex • Av))                ≈⟨ cright (sym assoc) ⟩
    Ex • ((Wv ↑ • Ex) • Av)                ≈⟨ sym assoc ⟩
    (Ex • (Wv ↑ • Ex)) • Av                ∎

  middle : Av • (CZ02 • CZ^ k) ≈ W • Av
  middle = begin
    Av • (CZ02 • CZ^ k)                    ≈⟨ sym assoc ⟩
    (Av • CZ02) • CZ^ k                    ≈⟨ cleft mid2 ⟩
    ((Ex • (Wv ↑ • Ex)) • Av) • CZ^ k      ≈⟨ assoc ⟩
    (Ex • (Wv ↑ • Ex)) • (Av • CZ^ k)      ≈⟨ cright (sym (lemma-comm-CZᵏ-w↑↑ (toℕ k) [ v ]ᵛᵇ)) ⟩
    (Ex • (Wv ↑ • Ex)) • (CZ^ k • Av)      ≈⟨ sym assoc ⟩
    ((Ex • (Wv ↑ • Ex)) • CZ^ k) • Av      ≈⟨ cleft assoc ⟩
    (Ex • ((Wv ↑ • Ex) • CZ^ k)) • Av      ≈⟨ cleft (cright assoc) ⟩
    (Ex • (Wv ↑ • (Ex • CZ^ k))) • Av      ∎

  proof : [ (x ∷ v) ]ᵛᵇ ↑ • CZ ≈ W • [ (x ∷ v) ]ᵛᵇ ↑
  proof = begin
    (Av • Bb) • CZ                         ≈⟨ assoc ⟩
    Av • (Bb • CZ)                         ≈⟨ cright (gen-B↑←CZ x) ⟩
    Av • ((BCZ.dir-of x ↓ᵏ m) • Bb)        ≈⟨ cright (cleft (refl' (dir-eq x))) ⟩
    Av • ((CZ02 • CZ^ k) • Bb)             ≈⟨ sym assoc ⟩
    (Av • (CZ02 • CZ^ k)) • Bb             ≈⟨ cleft middle ⟩
    (W • Av) • Bb                          ≈⟨ assoc ⟩
    W • (Av • Bb)                          ∎
