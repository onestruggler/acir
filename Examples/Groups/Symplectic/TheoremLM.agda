------------------------------------------------------------------------
-- Presentations of groups
--
-- The single-level box-existence theorem `Theorem-LM` for the plain gate
-- set: given a symplectic pair (p , q) — sform p q = 1 — there is an ML
-- coset box sending p to pZ₀ and q to pX₀.  This is the constructive core
-- of surjectivity (Examples.Groups.Symplectic.Surjectivity).
--
-- Built by induction on the width n on top of the single-qupit box
-- actions of Examples.Groups.Symplectic.BoxAction.  n = 0 is vacuous
-- (sform = 0 ≠ 1) and n = 1 assembles the ML 1 box  S^(-e) • [p]ᵃ.
--
-- (An earlier version of this comment said the n ≥ 2 cases were
-- postulated.  That was stale: this module contains no postulate and
-- is --safe.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.TheoremLM (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Vec using ([] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_ ; module ≡-Reasoning)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; sform ; sform1 ; pZ ; pX ; pI ; pZ₀ ; pX₀ ; pIₙ)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (Circuit ; Gen)

open import Data.Vec using (_∷ʳ_)

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (pZₙ)

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using (ML ; [_]ᵐˡ ; [_]ᵈ ; [_]ᵐ ; [_]ᵛᵇ ; [_]ᵃ ; A ; B ; E ; D ; M)

open import Examples.Groups.Symplectic.BoxAction p-2 p-prime
  using (act ; act-S^ ; act-M ; act-HS^ ; lemma-act-↑)

open import Examples.Groups.Symplectic.DBox p-2 p-prime
  using (lemma-dbox-IZ ; lemma-dbox)

open import Examples.Groups.Symplectic.ABox p-2 p-prime
  using (lemma-abox ; lemma-abox-X ; e-after-abox)
open import Examples.Groups.Symplectic.BBox p-2 p-prime
  using (lemma-bboxes ; lemma-pZₙ ; lemma-mcol-Z
        ; act-bboxes ; lemma-bboxes-X' ; lemma-act-bboxes-shape ; lemma-mcol-X)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- n ≥ 2, top of p nonzero (inj₁ case).  Claim 1 (p → pZ₀) is PROVEN
-- (a-box clears p₁, b-vector clears the row, m-column moves Z to front);
-- claim 2 (q → pX₀) chooses m = (vd , e₀), where the a-box sends q₁ to
-- (sform1 p1 q1 , e₀), the b-vector reshapes the row to vd ∷ʳ (1 , e₀)
-- (its last a-component is sform (p1∷ptail) (q1∷qtail) = 1), and the
-- m-column moves that X to the front.

q-side-2 : ∀ {n} (p1 : Pauli1) (pr : p1 ≢ (₀ , ₀))
  (ptail : Pauli (₁₊ n)) (q1 : Pauli1) (qtail : Pauli (₁₊ n)) →
  sform (p1 ∷ ptail) (q1 ∷ qtail) ≡ ₁ →
  ∃ λ (m : M (₂₊ n)) →
    act [ inj₁ (m , (ptail , (p1 , pr))) ]ᵐˡ (q1 ∷ qtail) ≡ pX₀
q-side-2 {n} p1 pr ptail q1 qtail sf = (vd , e0) , claim2
  where
  open ≡-Reasoning
  spq   = sform1 p1 q1
  e0    = e-after-abox p1 pr q1
  shape = lemma-act-bboxes-shape spq e0 ptail qtail
  vd    = shape .proj₁
  claim2 : act [ inj₁ ((vd , e0) , (ptail , (p1 , pr))) ]ᵐˡ (q1 ∷ qtail) ≡ pX₀
  claim2 = begin
    act ([ (vd , e0) ]ᵐ • ([ ptail ]ᵛᵇ • [ (p1 , pr) ]ᵃ)) (q1 ∷ qtail)
      ≡⟨ Eq.cong (λ z → act [ (vd , e0) ]ᵐ (act [ ptail ]ᵛᵇ z)) (lemma-abox-X p1 pr q1 qtail) ⟩
    act [ (vd , e0) ]ᵐ (act [ ptail ]ᵛᵇ ((spq , e0) ∷ qtail))
      ≡⟨ Eq.cong (act [ (vd , e0) ]ᵐ) (lemma-bboxes-X' (spq , e0) ptail qtail) ⟩
    act [ (vd , e0) ]ᵐ (act-bboxes (spq , e0) ptail qtail)
      ≡⟨ Eq.cong (act [ (vd , e0) ]ᵐ) (shape .proj₂) ⟩
    act [ (vd , e0) ]ᵐ (vd ∷ʳ (spq + sform ptail qtail , e0))
      ≡⟨ Eq.cong (λ z → act [ (vd , e0) ]ᵐ (vd ∷ʳ (z , e0))) sf ⟩
    act [ (vd , e0) ]ᵐ (vd ∷ʳ (₁ , e0))
      ≡⟨ lemma-mcol-X vd e0 ⟩
    pX₀ ∎

inj₁-case : ∀ {n} (p1 : Pauli1) (pr : p1 ≢ (₀ , ₀))
  (ptail : Pauli (₁₊ n)) (q1 : Pauli1) (qtail : Pauli (₁₊ n)) →
  sform (p1 ∷ ptail) (q1 ∷ qtail) ≡ ₁ →
  ∃ λ (lm : ML (₂₊ n)) →
    act [ lm ]ᵐˡ (p1 ∷ ptail) ≡ pZ₀ × act [ lm ]ᵐˡ (q1 ∷ qtail) ≡ pX₀
inj₁-case p1 pr ptail q1 qtail sf =
  inj₁ (m , (ptail , (p1 , pr))) , claim1 , qs .proj₂
  where
  open ≡-Reasoning
  qs = q-side-2 p1 pr ptail q1 qtail sf
  m  = qs .proj₁
  claim1 : act [ inj₁ (m , (ptail , (p1 , pr))) ]ᵐˡ (p1 ∷ ptail) ≡ pZ₀
  claim1 = begin
    act ([ m ]ᵐ • ([ ptail ]ᵛᵇ • [ (p1 , pr) ]ᵃ)) (p1 ∷ ptail)
      ≡⟨ Eq.cong (λ z → act [ m ]ᵐ (act [ ptail ]ᵛᵇ z)) (lemma-abox p1 pr ptail) ⟩
    act [ m ]ᵐ (act [ ptail ]ᵛᵇ (pZ ∷ ptail))
      ≡⟨ Eq.cong (act [ m ]ᵐ) (lemma-bboxes ptail) ⟩
    act [ m ]ᵐ pZₙ
      ≡⟨ Eq.cong (act [ m ]ᵐ) lemma-pZₙ ⟩
    act [ m ]ᵐ (pIₙ ∷ʳ pZ)
      ≡⟨ lemma-mcol-Z (m .proj₁) (m .proj₂) ⟩
    pZ₀ ∎

------------------------------------------------------------------------
-- The theorem

Theorem-LM : ∀ {n} (p q : Pauli n) → sform p q ≡ ₁ →
  ∃ λ (lm : ML n) → act [ lm ]ᵐˡ p ≡ pZ₀ × act [ lm ]ᵐˡ q ≡ pX₀

-- n = 0 : sform [] [] = 0 ≠ 1.
Theorem-LM {0} [] [] sf = ⊥-elim (0ₚ≢1ₚ sf)

-- n = 1, p = (0,0) : sform1 (0,0) q = 0, contradiction.
Theorem-LM {1} ((₀ , ₀) ∷ []) ((c , d) ∷ []) sf =
  ⊥-elim (0ₚ≢1ₚ (Eq.trans (Eq.sym reduce) sf))
  where
  reduce : sform ((₀ , ₀) ∷ []) ((c , d) ∷ []) ≡ ₀
  reduce = Eq.trans (+-identityʳ (sform1 (₀ , ₀) (c , d)))
    (Eq.trans (Eq.cong (_+ c * ₀) (Eq.trans (Eq.cong (_* d) -0#≈0#) (*-zeroˡ d)))
              (Eq.trans (+-identityˡ (c * ₀)) (*-zeroʳ c)))

-- n = 1, p = (0 , b) with b ≠ 0 : clear with the M(b⁻¹) box, e = d·b⁻¹.
Theorem-LM {1} ((₀ , ₁₊ b') ∷ []) ((c , d) ∷ []) sf = lm , claim1 , claim2
  where
  open ≡-Reasoning
  bb  = (₁₊ b' , λ ()) ⁻¹                 -- b⁻¹ as a ℤ*
  x   = bb .proj₁                          -- = (₁₊ b')⁻¹
  e   = d * x
  pr  : (₀ , ₁₊ b') ≢ (₀ , ₀)
  pr  = λ ()
  lm  : ML 1
  lm  = (([] , e) , ([] , ((₀ , ₁₊ b') , pr)))

  bx=1 : (₁₊ b') * x ≡ ₁
  bx=1 = lemma-⁻¹ʳ (₁₊ b') {{nztoℕ {y = ₁₊ b'} {neq0 = λ ()}}}

  cb=1 : c * (₁₊ b') ≡ ₁
  cb=1 = begin
    c * (₁₊ b')                              ≡⟨ Eq.sym (+-identityˡ (c * (₁₊ b'))) ⟩
    ₀ + c * (₁₊ b')                          ≡⟨ Eq.cong (_+ c * (₁₊ b')) (Eq.sym (Eq.trans (Eq.cong (_* d) -0#≈0#) (*-zeroˡ d))) ⟩
    (- ₀) * d + c * (₁₊ b')                  ≡⟨ Eq.sym (+-identityʳ _) ⟩
    ((- ₀) * d + c * (₁₊ b')) + ₀            ≡⟨ sf ⟩
    ₁ ∎

  claim1 : act [ lm ]ᵐˡ ((₀ , ₁₊ b') ∷ []) ≡ pZ₀
  claim1 = begin
    act [ lm ]ᵐˡ ((₀ , ₁₊ b') ∷ [])
      ≡⟨ Eq.cong (act (Symplectic.S^ (- e))) (act-M bb ₀ (₁₊ b') []) ⟩
    act (Symplectic.S^ (- e)) ((₀ * (bb ⁻¹) .proj₁ , (₁₊ b') * x) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) ((z , (₁₊ b') * x) ∷ [])) (*-zeroˡ ((bb ⁻¹) .proj₁)) ⟩
    act (Symplectic.S^ (- e)) ((₀ , (₁₊ b') * x) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) ((₀ , z) ∷ [])) bx=1 ⟩
    act (Symplectic.S^ (- e)) ((₀ , ₁) ∷ [])
      ≡⟨ act-S^ (- e) ₀ ₁ [] ⟩
    (₀ , ₁ + ₀ * (- e)) ∷ []
      ≡⟨ Eq.cong (λ z → (₀ , ₁ + z) ∷ []) (*-zeroˡ (- e)) ⟩
    (₀ , ₁ + ₀) ∷ []
      ≡⟨ Eq.cong (λ z → (₀ , z) ∷ []) (+-identityʳ ₁) ⟩
    pZ₀ ∎

  claim2 : act [ lm ]ᵐˡ ((c , d) ∷ []) ≡ pX₀
  claim2 = begin
    act [ lm ]ᵐˡ ((c , d) ∷ [])
      ≡⟨ Eq.cong (act (Symplectic.S^ (- e))) (act-M bb c d []) ⟩
    act (Symplectic.S^ (- e)) ((c * (bb ⁻¹) .proj₁ , d * x) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) ((c * z , d * x) ∷ [])) (inv-involutive (₁₊ b' , λ ())) ⟩
    act (Symplectic.S^ (- e)) ((c * (₁₊ b') , d * x) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) ((z , d * x) ∷ [])) cb=1 ⟩
    act (Symplectic.S^ (- e)) ((₁ , d * x) ∷ [])
      ≡⟨ act-S^ (- e) ₁ (d * x) [] ⟩
    (₁ , d * x + ₁ * (- e)) ∷ []
      ≡⟨ Eq.cong (λ z → (₁ , d * x + z) ∷ []) (*-identityˡ (- e)) ⟩
    (₁ , d * x + (- e)) ∷ []
      ≡⟨ Eq.cong (λ z → (₁ , z) ∷ []) (+-inverseʳ (d * x)) ⟩
    pX₀ ∎

-- n = 1, p = (a , b) with a ≠ 0 : clear with the M(a⁻¹)·H·S box, e = c·a⁻¹.
Theorem-LM {1} ((₁₊ a' , b) ∷ []) ((c , d) ∷ []) sf = lm , claim1 , claim2
  where
  open ≡-Reasoning
  aa   = (₁₊ a' , λ ()) ⁻¹
  x    = aa .proj₁                          -- = (₁₊ a')⁻¹
  -b/a = - b * x
  e    = c * x
  pr   : (₁₊ a' , b) ≢ (₀ , ₀)
  pr   = λ ()
  lm   : ML 1
  lm   = (([] , e) , ([] , ((₁₊ a' , b) , pr)))

  ax=1 : (₁₊ a') * x ≡ ₁
  ax=1 = lemma-⁻¹ʳ (₁₊ a') {{nztoℕ {y = ₁₊ a'} {neq0 = λ ()}}}

  -- (₁₊ a') · (-b/a) = -b, so the H·S rotation zeroes the top of p.
  aux-p : b + (₁₊ a') * -b/a ≡ ₀
  aux-p = begin
    b + (₁₊ a') * (- b * x)     ≡⟨ Eq.cong (b +_) (Eq.sym (*-assoc (₁₊ a') (- b) x)) ⟩
    b + (₁₊ a') * (- b) * x     ≡⟨ Eq.cong (λ z → b + z * x) (*-comm (₁₊ a') (- b)) ⟩
    b + (- b) * (₁₊ a') * x     ≡⟨ Eq.cong (b +_) (*-assoc (- b) (₁₊ a') x) ⟩
    b + (- b) * ((₁₊ a') * x)   ≡⟨ Eq.cong (λ z → b + (- b) * z) ax=1 ⟩
    b + (- b) * ₁               ≡⟨ Eq.cong (b +_) (*-identityʳ (- b)) ⟩
    b + (- b)                   ≡⟨ +-inverseʳ b ⟩
    ₀ ∎

  -- F = -(d + c·(-b/a))·(₁₊ a') = sform1 (a,b)(c,d) = 1.
  F=1 : - (d + c * -b/a) * (₁₊ a') ≡ ₁
  F=1 = begin
    - (d + c * (- b * x)) * (₁₊ a')
      ≡⟨ Eq.sym (-‿distribˡ-* (d + c * (- b * x)) (₁₊ a')) ⟩
    - ((d + c * (- b * x)) * (₁₊ a'))
      ≡⟨ Eq.cong -_ (*-distribʳ-+ (₁₊ a') d (c * (- b * x))) ⟩
    - (d * (₁₊ a') + c * (- b * x) * (₁₊ a'))
      ≡⟨ Eq.cong (λ z → - (d * (₁₊ a') + z)) reduce-c ⟩
    - (d * (₁₊ a') + (- (c * b)))
      ≡⟨ Eq.trans (Eq.sym (-‿+-comm (d * (₁₊ a')) (- (c * b)))) (Eq.cong (- (d * (₁₊ a')) +_) (-‿involutive (c * b))) ⟩
    - (d * (₁₊ a')) + c * b
      ≡⟨ Eq.cong (_+ c * b) (Eq.trans (Eq.cong -_ (*-comm d (₁₊ a'))) (-‿distribˡ-* (₁₊ a') d)) ⟩
    (- (₁₊ a')) * d + c * b
      ≡⟨ sf1 ⟩
    ₁ ∎
    where
    reduce-c : c * (- b * x) * (₁₊ a') ≡ - (c * b)
    reduce-c = begin
      c * (- b * x) * (₁₊ a')       ≡⟨ *-assoc c (- b * x) (₁₊ a') ⟩
      c * ((- b * x) * (₁₊ a'))     ≡⟨ Eq.cong (c *_) (*-assoc (- b) x (₁₊ a')) ⟩
      c * ((- b) * (x * (₁₊ a')))   ≡⟨ Eq.cong (λ z → c * ((- b) * z)) (Eq.trans (*-comm x (₁₊ a')) ax=1) ⟩
      c * ((- b) * ₁)               ≡⟨ Eq.cong (λ z → c * z) (*-identityʳ (- b)) ⟩
      c * (- b)                     ≡⟨ Eq.trans (*-comm c (- b)) (Eq.trans (Eq.sym (-‿distribˡ-* b c)) (Eq.cong -_ (*-comm b c))) ⟩
      - (c * b) ∎
    sf1 : (- (₁₊ a')) * d + c * b ≡ ₁
    sf1 = Eq.trans (Eq.sym (+-identityʳ _)) sf

  claim1 : act [ lm ]ᵐˡ ((₁₊ a' , b) ∷ []) ≡ pZ₀
  claim1 = begin
    act [ lm ]ᵐˡ ((₁₊ a' , b) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) (act (Symplectic.M aa) z)) (act-HS^ -b/a (₁₊ a') b []) ⟩
    act (Symplectic.S^ (- e)) (act (Symplectic.M aa) ((- (b + (₁₊ a') * -b/a) , ₁₊ a') ∷ []))
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) (act (Symplectic.M aa) ((- z , ₁₊ a') ∷ []))) aux-p ⟩
    act (Symplectic.S^ (- e)) (act (Symplectic.M aa) ((- ₀ , ₁₊ a') ∷ []))
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) (act (Symplectic.M aa) ((z , ₁₊ a') ∷ []))) -0#≈0# ⟩
    act (Symplectic.S^ (- e)) (act (Symplectic.M aa) ((₀ , ₁₊ a') ∷ []))
      ≡⟨ Eq.cong (act (Symplectic.S^ (- e))) (act-M aa ₀ (₁₊ a') []) ⟩
    act (Symplectic.S^ (- e)) ((₀ * (aa ⁻¹) .proj₁ , (₁₊ a') * x) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) ((z , (₁₊ a') * x) ∷ [])) (*-zeroˡ ((aa ⁻¹) .proj₁)) ⟩
    act (Symplectic.S^ (- e)) ((₀ , (₁₊ a') * x) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) ((₀ , z) ∷ [])) ax=1 ⟩
    act (Symplectic.S^ (- e)) ((₀ , ₁) ∷ [])
      ≡⟨ act-S^ (- e) ₀ ₁ [] ⟩
    (₀ , ₁ + ₀ * (- e)) ∷ []
      ≡⟨ Eq.cong (λ z → (₀ , ₁ + z) ∷ []) (*-zeroˡ (- e)) ⟩
    (₀ , ₁ + ₀) ∷ []
      ≡⟨ Eq.cong (λ z → (₀ , z) ∷ []) (+-identityʳ ₁) ⟩
    pZ₀ ∎

  claim2 : act [ lm ]ᵐˡ ((c , d) ∷ []) ≡ pX₀
  claim2 = begin
    act [ lm ]ᵐˡ ((c , d) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) (act (Symplectic.M aa) z)) (act-HS^ -b/a c d []) ⟩
    act (Symplectic.S^ (- e)) (act (Symplectic.M aa) ((- (d + c * -b/a) , c) ∷ []))
      ≡⟨ Eq.cong (act (Symplectic.S^ (- e))) (act-M aa (- (d + c * -b/a)) c []) ⟩
    act (Symplectic.S^ (- e)) (((- (d + c * -b/a)) * (aa ⁻¹) .proj₁ , c * x) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) (((- (d + c * -b/a)) * z , c * x) ∷ [])) (inv-involutive (₁₊ a' , λ ())) ⟩
    act (Symplectic.S^ (- e)) (((- (d + c * -b/a)) * (₁₊ a') , c * x) ∷ [])
      ≡⟨ Eq.cong (λ z → act (Symplectic.S^ (- e)) ((z , c * x) ∷ [])) F=1 ⟩
    act (Symplectic.S^ (- e)) ((₁ , c * x) ∷ [])
      ≡⟨ act-S^ (- e) ₁ (c * x) [] ⟩
    (₁ , c * x + ₁ * (- e)) ∷ []
      ≡⟨ Eq.cong (λ z → (₁ , c * x + z) ∷ []) (*-identityˡ (- e)) ⟩
    (₁ , c * x + (- e)) ∷ []
      ≡⟨ Eq.cong (λ z → (₁ , z) ∷ []) (+-inverseʳ (c * x)) ⟩
    pX₀ ∎

-- n ≥ 2, p top = (0,0) : peel the top wire — d-box for q's top, recurse.
Theorem-LM {2+ n} ((₀ , ₀) ∷ ptail) (q1@(qa , qb) ∷ qtail) sf =
  inj₂ (q1 , ih .proj₁) , claim1 , claim2
  where
  open ≡-Reasoning
  sform1-I : sform1 (₀ , ₀) q1 ≡ ₀
  sform1-I = Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (_* qb) -0#≈0#) (*-zeroˡ qb)) (*-zeroʳ qa))
                      (+-identityˡ ₀)
  sf' : sform ptail qtail ≡ ₁
  sf' = Eq.trans (Eq.sym (Eq.trans (Eq.cong (_+ sform ptail qtail) sform1-I)
                                   (+-identityˡ (sform ptail qtail)))) sf
  ih = Theorem-LM {₁₊ n} ptail qtail sf'

  claim1 : act [ inj₂ (q1 , ih .proj₁) ]ᵐˡ ((₀ , ₀) ∷ ptail) ≡ pZ₀
  claim1 = begin
    act ([ q1 ]ᵈ • [ ih .proj₁ ]ᵐˡ Symplectic.↑) (pI ∷ ptail)
      ≡⟨ Eq.cong (act [ q1 ]ᵈ) (lemma-act-↑ [ ih .proj₁ ]ᵐˡ pI ptail) ⟩
    act [ q1 ]ᵈ (pI ∷ act [ ih .proj₁ ]ᵐˡ ptail)
      ≡⟨ Eq.cong (λ z → act [ q1 ]ᵈ (pI ∷ z)) (ih .proj₂ .proj₁) ⟩
    act [ q1 ]ᵈ (pI ∷ pZ₀)
      ≡⟨ lemma-dbox-IZ q1 pIₙ ⟩
    pZ₀ ∎

  claim2 : act [ inj₂ (q1 , ih .proj₁) ]ᵐˡ (q1 ∷ qtail) ≡ pX₀
  claim2 = begin
    act ([ q1 ]ᵈ • [ ih .proj₁ ]ᵐˡ Symplectic.↑) (q1 ∷ qtail)
      ≡⟨ Eq.cong (act [ q1 ]ᵈ) (lemma-act-↑ [ ih .proj₁ ]ᵐˡ q1 qtail) ⟩
    act [ q1 ]ᵈ (q1 ∷ act [ ih .proj₁ ]ᵐˡ qtail)
      ≡⟨ Eq.cong (λ z → act [ q1 ]ᵈ (q1 ∷ z)) (ih .proj₂ .proj₂) ⟩
    act [ q1 ]ᵈ (q1 ∷ pX₀)
      ≡⟨ lemma-dbox q1 pIₙ ⟩
    pX₀ ∎

-- n ≥ 2, p top ≠ (0,0) : the inj₁ case (claim1 proven, claim2 = q-side-2).
Theorem-LM {2+ n} ((₀ , ₁₊ b) ∷ ptail) (q1 ∷ qtail) sf = inj₁-case (₀ , ₁₊ b) (λ ()) ptail q1 qtail sf
Theorem-LM {2+ n} ((₁₊ a , b) ∷ ptail) (q1 ∷ qtail) sf = inj₁-case (₁₊ a , b) (λ ()) ptail q1 qtail sf
