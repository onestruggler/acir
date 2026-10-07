------------------------------------------------------------------------
-- Presentations of groups
--
-- A diagonal circuit, split along wire 0
--
-- On ₁₊ m wires, a product of phase gates is a product of phase gates
-- one wire up, times the canonical form T ^ a • F β γ of its part
-- involving x₀ (D-split):  P e₀ is T, P (sw ℓ) is P ℓ one wire up, and
-- P (cx ℓ) is P ℓ one wire up times T times C₂ ℓ ⁷, a form by
-- Diagonal.EForm.  The forms add, and everything diagonal commutes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.Decompose where

open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_ ; _%_)
open import Data.Nat.DivMod using (_mod_ ; m%n<n)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; replicate ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.CNOT+Dihedral.Semantics.Z8 using (ℤ₈) renaming (_+_ to _+₈_)
open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Powers
open import Examples.Groups.CNOT+Dihedral.Linear.Base using (NZ ; e₀ ; cx ; sw ; r)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Phase using (P)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Calculus
open import Examples.Groups.CNOT+Dihedral.Diagonal.Gates using (CS)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Split
open import Examples.Groups.CNOT+Dihedral.Diagonal.EForm

private
  variable
    m : ℕ

------------------------------------------------------------------------
-- The wire-0 data and forms

EData : ℕ → Set
EData m = ℤ₈ × Vec (Fin 4) m × Tri m

E : EData m → Circuit (₁₊ m)
E (a , bs , cs) = T ^ toℕ a • F bs cs

E0 : EData m
E0 {m} = 0F , replicate m 0F , tri0 m

infixl 6 _⊞_
_⊞_ : EData m → EData m → EData m
(a , bs , cs) ⊞ (a' , bs' , cs') = a +₈ a' , zipWith _+₄_ bs bs' , triXor cs cs'

T-+ : (a b : ℤ₈) → (₁₊ m) ⊢ T ^ toℕ a • T ^ toℕ b ≈ T ^ toℕ (a +₈ b)
T-+ {m} a b = begin
  T ^ toℕ a • T ^ toℕ b           ≈⟨ sym (Pow.pow-+ (₁₊ m) T (toℕ a) (toℕ b)) ⟩
  T ^ (toℕ a + toℕ b)             ≈⟨ Pow.pow-mod (₁₊ m) T (trans (by-assoc Eq.refl) (ax R₇)) (toℕ a + toℕ b) ⟩
  T ^ ((toℕ a + toℕ b) % 8)       ≈⟨ refl' (Eq.cong (T ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ a + toℕ b) 8)))) ⟩
  T ^ toℕ (a +₈ b)                ∎
  where open Width (₁₊ m)

E-diag : (e : EData m) → Diag (₁₊ m) (E e)
E-diag {m} (a , bs , cs) = `T `^ toℕ a `• proj₁ (F-diag bs cs) , cong refl (proj₂ (F-diag bs cs))
  where open Width (₁₊ m)

E-• : (e e' : EData m) → (₁₊ m) ⊢ E e • E e' ≈ E (e ⊞ e')
E-• {m} (a , bs , cs) (a' , bs' , cs') = begin
  (T ^ toℕ a • F bs cs) • T ^ toℕ a' • F bs' cs'
    ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  T ^ toℕ a • (F bs cs • T ^ toℕ a') • F bs' cs'
    ≈⟨ back _ (front _ (diag-comm (F-diag bs cs) (`T `^ toℕ a' , refl))) ⟩
  T ^ toℕ a • (T ^ toℕ a' • F bs cs) • F bs' cs'
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (T ^ toℕ a • T ^ toℕ a') • F bs cs • F bs' cs'
    ≈⟨ cong (T-+ a a') (F-• bs bs' cs cs') ⟩
  T ^ toℕ (a +₈ a') • F (zipWith _+₄_ bs bs') (triXor cs cs') ∎
  where open Width (₁₊ m)

E0-ε : (₁₊ m) ⊢ E {m} E0 ≈ ε
E0-ε {m} = Width.trans Width.left-unit (F-zero m)

------------------------------------------------------------------------
-- Diagonal circuits as products of phase gates, with a scalar

DiagE : (m : ℕ) → Circuit m → Set
DiagE m w = Σ (ℕ × PE m) (λ e → m ⊢ w ≈ ⟦ e ⟧ₑ)

toDiagE : ∀ {w : Circuit m} → Diag m w → DiagE m w
toDiagE {m} (d , p) = toPE d , Width.trans p (D-sound d)

diagE-comm : ∀ {a b : Circuit m} → DiagE m a → DiagE m b → m ⊢ a • b ≈ b • a
diagE-comm {m} (e , p) (e' , q) =
  trans (cong p q) (trans (⟦⟧ₑ-comm e e') (sym (cong q p)))
  where open Width m

------------------------------------------------------------------------
-- One phase gate, split

up-part : NZ (₁₊ m) × ℕ → PE m
up-part (e₀   , k) = []
up-part (cx ℓ , k) = (ℓ , k) ∷ []
up-part (sw ℓ , k) = (ℓ , k) ∷ []

e-part : NZ (₁₊ m) × ℕ → EData m
e-part {m} (e₀   , k) = k mod 8 , replicate m 0F , tri0 m
e-part     (cx ℓ , k) = k mod 8 , (k * 7) ·b bvec ℓ , (k * 7) ·t cvec ℓ
e-part     (sw ℓ , k) = E0

private
  T-mod : (k : ℕ) → (₁₊ m) ⊢ T ^ k ≈ T ^ toℕ (k mod 8)
  T-mod {m} k =
    trans (Pow.pow-mod (₁₊ m) T (trans (by-assoc Eq.refl) (ax R₇)) k)
          (refl' (Eq.cong (T ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k 8)))))
    where open Width (₁₊ m)

  P↑-diag : (ℓ : NZ (₁₊ m)) → DiagE (₂₊ m) ((P ℓ) ↑)
  P↑-diag {m} ℓ = (0 , (sw ℓ , 1) ∷ []) , trans (split-sw' ℓ) (sym (trans left-unit right-unit))
    where
    open Width (₂₊ m)
    split-sw' : (ℓ : NZ (₁₊ m)) → (₂₊ m) ⊢ (P ℓ) ↑ ≈ P (sw ℓ)
    split-sw' ℓ = sym (split-sw ℓ)

  T-diag : DiagE (₁₊ m) T
  T-diag {m} = toDiagE (`T , Width.refl)

  C₂⁷-diag : (ℓ : NZ (₁₊ m)) → DiagE (₂₊ m) (C₂ ℓ ^ 7)
  C₂⁷-diag {m} ℓ = toDiagE (proj₁ (F-diag (bvec ℓ) (cvec ℓ)) `^ 7 ,
                    Pow.pow-cong (₂₊ m) 7 (Width.trans (C₂≈F ℓ) (proj₂ (F-diag (bvec ℓ) (cvec ℓ)))))

  •-diag : ∀ {a b : Circuit m} → DiagE m a → DiagE m b → DiagE m (a • b)
  •-diag {m} ((s , pe) , p) ((t , qe) , q) =
    (s + t , pe ++ qe) , Width.trans (Width.cong p q) (D-sound' s pe t qe)
    where
    D-sound' : (s : ℕ) (pe : PE m) (t : ℕ) (qe : PE m) →
               m ⊢ ⟦ s , pe ⟧ₑ • ⟦ t , qe ⟧ₑ ≈ ⟦ s + t , pe ++ qe ⟧ₑ
    D-sound' s pe t qe = begin
      (ω ^ s • prod pe) • ω ^ t • prod qe        ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
      ω ^ s • (prod pe • ω ^ t) • prod qe        ≈⟨ back _ (front _ (sym (ωᵏ-comm t (prod pe)))) ⟩
      ω ^ s • (ω ^ t • prod pe) • prod qe        ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
      (ω ^ s • ω ^ t) • prod pe • prod qe        ≈⟨ cong (sym (Pow.pow-+ m ω s t)) (sym (prod-++ pe qe)) ⟩
      ω ^ (s + t) • prod (pe ++ qe)              ∎
      where open Width m

entry-split : (x : NZ (₁₊ m) × ℕ) →
              (₁₊ m) ⊢ Pz (proj₁ x) ^ proj₂ x ≈ (prod (up-part x)) ↑ • E (e-part x)
entry-split {m} (e₀ , k) = begin
  (ε • T • ε) ^ k                               ≈⟨ Pow.pow-cong (₁₊ m) k (by-assoc Eq.refl) ⟩
  T ^ k                                         ≈⟨ T-mod k ⟩
  T ^ toℕ (k mod 8)                             ≈⟨ sym (trans left-unit (trans (back _ (F-zero m)) right-unit)) ⟩
  ε • T ^ toℕ (k mod 8) • F (replicate m 0F) (tri0 m) ∎
  where open Width (₁₊ m)
entry-split {suc m} (sw ℓ , k) = begin
  P (sw ℓ) ^ k                         ≈⟨ Pow.pow-cong (₂₊ m) k (split-sw ℓ) ⟩
  ((P ℓ) ↑) ^ k                        ≈⟨ refl' (Eq.sym (↑-pow (P ℓ) k)) ⟩
  (P ℓ ^ k) ↑                          ≈⟨ sym (trans (cong (lift Width.right-unit) E0-ε) right-unit) ⟩
  (P ℓ ^ k • ε) ↑ • E E0               ∎
  where open Width (₂₊ m)
entry-split {suc m} (cx ℓ , k) = begin
  P (cx ℓ) ^ k
    ≈⟨ Pow.pow-cong (₂₊ m) k (split-cx ℓ) ⟩
  ((P ℓ) ↑ • T • C₂ ℓ ^ 7) ^ k
    ≈⟨ Pow.pow-• (₂₊ m) k (diagE-comm (P↑-diag ℓ) (•-diag T-diag (C₂⁷-diag ℓ))) ⟩
  ((P ℓ) ↑) ^ k • (T • C₂ ℓ ^ 7) ^ k
    ≈⟨ cong (refl' (Eq.sym (↑-pow (P ℓ) k))) (Pow.pow-• (₂₊ m) k (diagE-comm T-diag (C₂⁷-diag ℓ))) ⟩
  (P ℓ ^ k) ↑ • T ^ k • (C₂ ℓ ^ 7) ^ k
    ≈⟨ back _ (cong (T-mod k) (Pow.pow-pow (₂₊ m) (C₂ ℓ) 7 k)) ⟩
  (P ℓ ^ k) ↑ • T ^ toℕ (k mod 8) • C₂ ℓ ^ (k * 7)
    ≈⟨ back _ (back _ (trans (Pow.pow-cong (₂₊ m) (k * 7) (C₂≈F ℓ)) (F-^ (k * 7) (bvec ℓ) (cvec ℓ)))) ⟩
  (P ℓ ^ k) ↑ • T ^ toℕ (k mod 8) • F ((k * 7) ·b bvec ℓ) ((k * 7) ·t cvec ℓ)
    ≈⟨ front _ (lift (Width.sym Width.right-unit)) ⟩
  (P ℓ ^ k • ε) ↑ • T ^ toℕ (k mod 8) • F ((k * 7) ·b bvec ℓ) ((k * 7) ·t cvec ℓ) ∎
  where open Width (₂₊ m)

------------------------------------------------------------------------
-- A product of phase gates, split

ups : PE (₁₊ m) → PE m
ups []       = []
ups (x ∷ pe) = up-part x ++ ups pe

es : PE (₁₊ m) → EData m
es []       = E0
es (x ∷ pe) = e-part x ⊞ es pe

D-split : (pe : PE (₁₊ m)) → (₁₊ m) ⊢ prod pe ≈ (prod (ups pe)) ↑ • E (es pe)
D-split {m} [] = sym (trans left-unit E0-ε)
  where open Width (₁₊ m)
D-split {m} ((ℓ , k) ∷ pe) = begin
  Pz ℓ ^ k • prod pe
    ≈⟨ cong (entry-split (ℓ , k)) (D-split pe) ⟩
  (U₁ ↑ • E e₁) • U₂ ↑ • E e₂
    ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  U₁ ↑ • (E e₁ • U₂ ↑) • E e₂
    ≈⟨ back _ (front _ (diagE-comm (toDiagE (E-diag e₁)) U₂↑-diag)) ⟩
  U₁ ↑ • (U₂ ↑ • E e₁) • E e₂
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (U₁ ↑ • U₂ ↑) • E e₁ • E e₂
    ≈⟨ cong (lift (Width.sym (prod-++ (up-part (ℓ , k)) (ups pe)))) (E-• e₁ e₂) ⟩
  (prod (up-part (ℓ , k) ++ ups pe)) ↑ • E (e₁ ⊞ e₂) ∎
  where
  open Width (₁₊ m)
  U₁ = prod (up-part (ℓ , k))
  U₂ = prod (ups pe)
  e₁ = e-part (ℓ , k)
  e₂ = es pe
  U₂↑-diag : DiagE (₁₊ m) (U₂ ↑)
  U₂↑-diag = (0 , map liftE (ups pe)) , trans (prod-↑ (ups pe)) (sym left-unit)
