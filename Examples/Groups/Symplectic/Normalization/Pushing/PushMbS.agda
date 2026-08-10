------------------------------------------------------------------------
-- Presentations of groups
--
-- The core of the bottom-wire unary coset action: pushing one S-gate
-- through an M column · B-vector,
--
--   ([ m ]ᵐ • [ bv ]ᵛᵇ) • S ≈ dir ↑ • ([ m' ]ᵐ • [ bv ]ᵛᵇ)
--
-- (mb-S; the B-vector is left unchanged).  Recursion on the vector length:
-- the bottom B box emits S↑ • R₀ (B.lemma-B-br … S-gen); R₀ (= S^(c²)•CZ^(-c),
-- no-↥) is routed by PushMBword.push-MBvec-word, while S↑ recurses on the
-- shorter vector (peeling one wire, ML'-Top-mbv-push style).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+ ; zero ; suc)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushMbS (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; _∷_ ; [])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
import Examples.Groups.Symplectic.BR.Two.B p-2 p-prime as BB
import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime using (cong↓ᵏ)

open import Notations
open import Word.Base using (Word ; _•_ ; ε ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- Widening B.lemma-B-br (bottom S through a B box) to width (₂₊ k).

B-S-br-n : ∀ {k} (b : B) →
  let open PB ((₂₊ k) QRel,_===_) in
  [ b ]ᵇ • S ≈ (BB.dir-of b S-gen (λ ()) (λ ()) ↓ᵏ k) • [ b ]ᵇ
B-S-br-n {k} b =
  trans (refl' (Eq.cong₂ _•_ (Eq.sym (ML'T.bbox-↓ᵏ b k)) Eq.refl))
    (trans (cong↓ᵏ k _ _ (BB.lemma-B-br b S-gen (λ ()) (λ ())))
      (refl' (Eq.cong₂ _•_ Eq.refl (ML'T.bbox-↓ᵏ b k))))
  where open PB ((₂₊ k) QRel,_===_)

------------------------------------------------------------------------
-- The no-↥ part R₀ of the residual, and the split dir = S↑ • R₀.

open import Examples.Groups.Symplectic.Normalization.Pushing.PushBword p-2 p-prime
  using (No-Top ; εⁿ ; _•ⁿ_ ; nt-S^ ; nt-CZ^)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushM p-2 p-prime
  using (push-M-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMBword p-2 p-prime
  using (push-MBvec-word)
open import Examples.Groups.Symplectic.Normalization.Pushing.SectionLMBridge p-2 p-prime
  using (mbox-eq ; vbbox-eq)

Rof : B → Word (Gen 2)
Rof (₀ , ₀)          = ε
Rof (₀ , b@(₁₊ _))   = S^ (b * b) • CZ^ (- b)
Rof (a@(₁₊ _) , b)   = S^ (a * a) • CZ^ (- a)

Rof-nt : (b : B) → No-Top (Rof b)
Rof-nt (₀ , ₀)        = εⁿ
Rof-nt (₀ , ₁₊ _)     = nt-S^ _ •ⁿ nt-CZ^ _
Rof-nt (₁₊ _ , b)     = nt-S^ _ •ⁿ nt-CZ^ _

B-S-split : (b : B) →
  let open PB (2 QRel,_===_) in
  BB.dir-of b S-gen (λ ()) (λ ()) ≈ S ↑ • Rof b
B-S-split (₀ , ₀)      = sym right-unit
  where open PB (2 QRel,_===_) ; open PP (2 QRel,_===_)
B-S-split (₀ , ₁₊ _)   = refl
  where open PB (2 QRel,_===_)
B-S-split (₁₊ _ , b)   = refl
  where open PB (2 QRel,_===_)

------------------------------------------------------------------------
-- Pushing one S through the M column · B-vector.

mb-S : ∀ {k} (m : M (₁₊ k)) (bv : Vec B k) →
  let open PB ((₁₊ k) QRel,_===_) in
  ∃ λ (dir : Word (Gen k)) → ∃ λ (m' : M (₁₊ k)) →
    ([ m ]ᵐ • [ bv ]ᵛᵇ) • S ≈ dir ↑ • ([ m' ]ᵐ • [ bv ]ᵛᵇ)
-- Base: E box absorbs the S (push-M-S), nothing escapes.
mb-S {0} ([] , e) [] =
  ε , proj₁ (proj₂ (push-M-S ([] , e))) , (begin
    ([ ([] , e) ]ᵐ • ε) • S      ≈⟨ cleft right-unit ⟩
    [ ([] , e) ]ᵐ • S            ≈⟨ proj₂ (proj₂ (push-M-S ([] , e))) ⟩
    ε • [ m' ]ᵐ                  ≈⟨ cright (sym right-unit) ⟩
    ε • ([ m' ]ᵐ • ε)            ∎)
  where
  open PB (1 QRel,_===_)
  open PP (1 QRel,_===_)
  open SR word-setoid
  m' = proj₁ (proj₂ (push-M-S ([] , e)))
mb-S {₁₊ k'} (d₀ ∷ dr , e) (b₀ ∷ bv') = (dirS ↑ • dirR) , m'R , proof
  where
  open PB ((₂₊ k') QRel,_===_)
  open PP ((₂₊ k') QRel,_===_)
  open SR word-setoid
  module P1 = PB ((₁₊ k') QRel,_===_)
  rec  = mb-S {k'} (dr , e) bv'
  dirS = proj₁ rec
  m'S  = proj₁ (proj₂ rec)
  eqS  = proj₂ (proj₂ rec)
  mS2 : M (₂₊ k')
  mS2  = (d₀ ∷ m'S .proj₁ , m'S .proj₂)
  R    = Rof b₀
  pR   = push-MBvec-word R (Rof-nt b₀) mS2 bv'
  dirR = proj₁ pR
  m'R  = proj₁ (proj₂ pR)
  eqR  = proj₂ (proj₂ pR)

  B-S-br-split : [ b₀ ]ᵇ • S ≈ (S ↑ • (R ↓ᵏ k')) • [ b₀ ]ᵇ
  B-S-br-split = trans (B-S-br-n b₀) (cleft (cong↓ᵏ k' _ _ (B-S-split b₀)))

  s-step : [ (d₀ ∷ dr , e) ]ᵐ • ([ bv' ]ᵛᵇ • S) ↑ ≈ dirS ↑ ↑ • ([ mS2 ]ᵐ • [ bv' ]ᵛᵇ ↑)
  s-step = begin
    ([ d₀ ]ᵈ • [ (dr , e) ]ᵐ ↑) • ([ bv' ]ᵛᵇ • S) ↑
      ≈⟨ assoc ⟩
    [ d₀ ]ᵈ • ([ (dr , e) ]ᵐ ↑ • ([ bv' ]ᵛᵇ • S) ↑)
      ≈⟨ cright (lemma-cong↑ _ _ (P1.sym P1.assoc)) ⟩
    [ d₀ ]ᵈ • ((([ (dr , e) ]ᵐ • [ bv' ]ᵛᵇ) • S) ↑)
      ≈⟨ cright (lemma-cong↑ _ _ eqS) ⟩
    [ d₀ ]ᵈ • ((dirS ↑ • ([ m'S ]ᵐ • [ bv' ]ᵛᵇ)) ↑)
      ≈⟨ sym assoc ⟩
    ([ d₀ ]ᵈ • dirS ↑ ↑) • ([ m'S ]ᵐ ↑ • [ bv' ]ᵛᵇ ↑)
      ≈⟨ cleft (ML'T.comm-dbox-w↑↑-S d₀ dirS) ⟩
    (dirS ↑ ↑ • [ d₀ ]ᵈ) • ([ m'S ]ᵐ ↑ • [ bv' ]ᵛᵇ ↑)
      ≈⟨ assoc ⟩
    dirS ↑ ↑ • ([ d₀ ]ᵈ • ([ m'S ]ᵐ ↑ • [ bv' ]ᵛᵇ ↑))
      ≈⟨ cright (sym assoc) ⟩
    dirS ↑ ↑ • ([ mS2 ]ᵐ • [ bv' ]ᵛᵇ ↑) ∎

  r-step : [ mS2 ]ᵐ • ([ bv' ]ᵛᵇ ↑ • (R ↓ᵏ k')) ≈ dirR ↑ • ([ m'R ]ᵐ • [ bv' ]ᵛᵇ ↑)
  r-step = trans (cong (refl' (mbox-eq mS2))
                       (cong (refl' (Eq.cong (_↑) (vbbox-eq bv'))) refl))
             (trans eqR
                    (cright (cong (refl' (Eq.sym (mbox-eq m'R)))
                                  (refl' (Eq.sym (Eq.cong (_↑) (vbbox-eq bv')))))))

  proof : ([ (d₀ ∷ dr , e) ]ᵐ • [ b₀ ∷ bv' ]ᵛᵇ) • S
        ≈ (dirS ↑ • dirR) ↑ • ([ m'R ]ᵐ • [ b₀ ∷ bv' ]ᵛᵇ)
  proof = begin
    ([ (d₀ ∷ dr , e) ]ᵐ • ([ bv' ]ᵛᵇ ↑ • [ b₀ ]ᵇ)) • S
      ≈⟨ assoc ⟩
    [ (d₀ ∷ dr , e) ]ᵐ • (([ bv' ]ᵛᵇ ↑ • [ b₀ ]ᵇ) • S)
      ≈⟨ cright assoc ⟩
    [ (d₀ ∷ dr , e) ]ᵐ • ([ bv' ]ᵛᵇ ↑ • ([ b₀ ]ᵇ • S))
      ≈⟨ cright (cright B-S-br-split) ⟩
    [ (d₀ ∷ dr , e) ]ᵐ • ([ bv' ]ᵛᵇ ↑ • ((S ↑ • (R ↓ᵏ k')) • [ b₀ ]ᵇ))
      ≈⟨ cright (cright assoc) ⟩
    [ (d₀ ∷ dr , e) ]ᵐ • ([ bv' ]ᵛᵇ ↑ • (S ↑ • ((R ↓ᵏ k') • [ b₀ ]ᵇ)))
      ≈⟨ cright (sym assoc) ⟩
    [ (d₀ ∷ dr , e) ]ᵐ • (([ bv' ]ᵛᵇ ↑ • S ↑) • ((R ↓ᵏ k') • [ b₀ ]ᵇ))
      ≈⟨ sym assoc ⟩
    ([ (d₀ ∷ dr , e) ]ᵐ • ([ bv' ]ᵛᵇ ↑ • S ↑)) • ((R ↓ᵏ k') • [ b₀ ]ᵇ)
      ≈⟨ cleft s-step ⟩
    (dirS ↑ ↑ • ([ mS2 ]ᵐ • [ bv' ]ᵛᵇ ↑)) • ((R ↓ᵏ k') • [ b₀ ]ᵇ)
      ≈⟨ assoc ⟩
    dirS ↑ ↑ • (([ mS2 ]ᵐ • [ bv' ]ᵛᵇ ↑) • ((R ↓ᵏ k') • [ b₀ ]ᵇ))
      ≈⟨ cright (sym assoc) ⟩
    dirS ↑ ↑ • ((([ mS2 ]ᵐ • [ bv' ]ᵛᵇ ↑) • (R ↓ᵏ k')) • [ b₀ ]ᵇ)
      ≈⟨ cright (cleft assoc) ⟩
    dirS ↑ ↑ • (([ mS2 ]ᵐ • ([ bv' ]ᵛᵇ ↑ • (R ↓ᵏ k'))) • [ b₀ ]ᵇ)
      ≈⟨ cright (cleft r-step) ⟩
    dirS ↑ ↑ • ((dirR ↑ • ([ m'R ]ᵐ • [ bv' ]ᵛᵇ ↑)) • [ b₀ ]ᵇ)
      ≈⟨ cright assoc ⟩
    dirS ↑ ↑ • (dirR ↑ • (([ m'R ]ᵐ • [ bv' ]ᵛᵇ ↑) • [ b₀ ]ᵇ))
      ≈⟨ cright (cright assoc) ⟩
    dirS ↑ ↑ • (dirR ↑ • ([ m'R ]ᵐ • ([ bv' ]ᵛᵇ ↑ • [ b₀ ]ᵇ)))
      ≈⟨ sym assoc ⟩
    (dirS ↑ ↑ • dirR ↑) • ([ m'R ]ᵐ • ([ bv' ]ᵛᵇ ↑ • [ b₀ ]ᵇ)) ∎

------------------------------------------------------------------------
-- Iterate mb-S to push a power S ^ j.

module _ {k : ℕ} where
  open PB ((₁₊ k) QRel,_===_)
  open PP ((₁₊ k) QRel,_===_)
  open SR word-setoid

  mbSⁿ : (j : ℕ) (m : M (₁₊ k)) (bv : Vec B k) →
    ∃ λ (dir : Word (Gen k)) → ∃ λ (m' : M (₁₊ k)) →
      ([ m ]ᵐ • [ bv ]ᵛᵇ) • (S ^ j) ≈ dir ↑ • ([ m' ]ᵐ • [ bv ]ᵛᵇ)
  mbSⁿ zero m bv = ε , m , (begin
    ([ m ]ᵐ • [ bv ]ᵛᵇ) • ε   ≈⟨ right-unit ⟩
    [ m ]ᵐ • [ bv ]ᵛᵇ         ≈⟨ sym left-unit ⟩
    ε • ([ m ]ᵐ • [ bv ]ᵛᵇ)   ∎)
  mbSⁿ (suc zero) m bv = mb-S m bv
  mbSⁿ (suc (suc j)) m bv =
    let r1 = mb-S m bv
        d1 = proj₁ r1 ; m1 = proj₁ (proj₂ r1) ; eq1 = proj₂ (proj₂ r1)
        rj = mbSⁿ (suc j) m1 bv
        dj = proj₁ rj ; mj = proj₁ (proj₂ rj) ; eqj = proj₂ (proj₂ rj)
    in (d1 • dj) , mj , (begin
      ([ m ]ᵐ • [ bv ]ᵛᵇ) • (S • S ^ suc j) ≈⟨ sym assoc ⟩
      (([ m ]ᵐ • [ bv ]ᵛᵇ) • S) • S ^ suc j ≈⟨ cleft eq1 ⟩
      (d1 ↑ • ([ m1 ]ᵐ • [ bv ]ᵛᵇ)) • S ^ suc j ≈⟨ assoc ⟩
      d1 ↑ • (([ m1 ]ᵐ • [ bv ]ᵛᵇ) • S ^ suc j) ≈⟨ cright eqj ⟩
      d1 ↑ • (dj ↑ • ([ mj ]ᵐ • [ bv ]ᵛᵇ))  ≈⟨ sym assoc ⟩
      (d1 ↑ • dj ↑) • ([ mj ]ᵐ • [ bv ]ᵛᵇ)  ∎)
