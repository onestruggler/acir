------------------------------------------------------------------------
-- Presentations of groups
--
-- The independence of the affine decoding on five wires
--
-- A gadget G on five wires (acting on the basis states 0 and e₀) is
-- conjugated by affine circuits α (Five.Affine's τ of Blake's circuits).
-- If G commutes with seven letters — CX from wire j + 1 onto j (j = 0 ..
-- 3) and the SWAPs of the wires 1 2, 2 3, 3 4 — then it commutes with
-- every affine circuit that fixes 0 and e₀ (`indep`, through Five.Stab's
-- normal form, whose letters are among those seven), and so the
-- conjugate τα · G · τ(α⁻¹) depends only on where α sends 0 and e₀
-- (`conj-indep`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (_•_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; CX₁₀ ; Swap ; _↑)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Five.Rules using (_XVRel,_===_ ; _⊢ₓ_≈_)

module Examples.Groups.Clifford+CS.Five.Indep
  (G : Circuit 5)
  (p-cx₀ : 5 ⊢ₓ CX₁₀ • G ≈ G • CX₁₀)
  (p-cx₁ : 5 ⊢ₓ CX₁₀ ↑ • G ≈ G • CX₁₀ ↑)
  (p-cx₂ : 5 ⊢ₓ CX₁₀ ↑ ↑ • G ≈ G • CX₁₀ ↑ ↑)
  (p-cx₃ : 5 ⊢ₓ CX₁₀ ↑ ↑ ↑ • G ≈ G • CX₁₀ ↑ ↑ ↑)
  (p-sw₁ : 5 ⊢ₓ Swap ↑ • G ≈ G • Swap ↑)
  (p-sw₂ : 5 ⊢ₓ Swap ↑ ↑ • G ≈ G • Swap ↑ ↑)
  (p-sw₃ : 5 ⊢ₓ Swap ↑ ↑ ↑ • G ≈ G • Swap ↑ ↑ ↑)
  where

open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Primality using (prime[2])
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε)
import Presentation.Base as PB

open Tools (_XVRel,_===_ 5)

open import Examples.Groups.Clifford+CS.Five.Rules using (embed)
open import Examples.Groups.Clifford+CS.Five.Affine using (τ ; τg ; aff⇒)
open import Examples.Groups.Clifford+CS.Five.Stab using (stab ; R′ ; pw ; CXin₁ ; CXin₂ ; CXin₃ ; CXin₄ ; e₀)

import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
open import Examples.Groups.Qupit-Phase-Affine.Field 0 prime[2] using (F)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base 0 prime[2] 0
  using (LGen ; cx ; sw ; mul ; _↥ₗ ; ι ; ⌊_⌋)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan 0 prime[2] 0 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Aff 0 prime[2] using (adm)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm using (fn ; sound ; fn-• ; fn-ε)
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹ ; module Inv)

private
  -- a • G ≈ G • a and b • G ≈ G • b give (a • b) • G ≈ G • (a • b).
  slide : ∀ {a b : Circuit 5} → a • G ≈ G • a → b • G ≈ G • b → (a • b) • G ≈ G • (a • b)
  slide {a} {b} ea eb = begin
    (a • b) • G   ≈⟨ assoc ⟩
    a • (b • G)   ≈⟨ back a eb ⟩
    a • (G • b)   ≈⟨ sym assoc ⟩
    (a • G) • b   ≈⟨ front b ea ⟩
    (G • a) • b   ≈⟨ assoc ⟩
    G • (a • b)   ∎

  passε : ε • G ≈ G • ε
  passε = trans left-unit (sym right-unit)

  pass≈ : ∀ {a b : Circuit 5} → a ≈ b → a • G ≈ G • a → b • G ≈ G • b
  pass≈ e p = trans (front G (sym e)) (trans p (back G e))

------------------------------------------------------------------------
-- The letters of the normal form

-- A linear letter on the wires above 0.
pass-up : (y : LGen 4) → τg (ι y) ↑ • G ≈ G • τg (ι y) ↑
pass-up cx                    = p-cx₁
pass-up sw                    = p-sw₁
pass-up (mul a)               = passε
pass-up (cx ↥ₗ)               = p-cx₂
pass-up (sw ↥ₗ)               = p-sw₂
pass-up (mul a ↥ₗ)            = passε
pass-up (cx ↥ₗ ↥ₗ)            = p-cx₃
pass-up (sw ↥ₗ ↥ₗ)            = p-sw₃
pass-up (mul a ↥ₗ ↥ₗ)         = passε
pass-up (mul a ↥ₗ ↥ₗ ↥ₗ)      = passε

pass-⌊⌋ : (L : Word (LGen 4)) → τ (⌊ L ⌋ B.↑) • G ≈ G • τ (⌊ L ⌋ B.↑)
pass-⌊⌋ [ y ]ʷ  = pass-up y
pass-⌊⌋ ε       = passε
pass-⌊⌋ (u • v) = slide (pass-⌊⌋ u) (pass-⌊⌋ v)

-- The fan-in onto wire 0.
private
  in₁ : τ CXin₁ • G ≈ G • τ CXin₁
  in₁ = p-cx₀
  in₂ : τ CXin₂ • G ≈ G • τ CXin₂
  in₂ = slide p-sw₁ (slide p-cx₀ p-sw₁)
  in₃ : τ CXin₃ • G ≈ G • τ CXin₃
  in₃ = slide p-sw₂ (slide in₂ p-sw₂)
  in₄ : τ CXin₄ • G ≈ G • τ CXin₄
  in₄ = slide p-sw₃ (slide in₃ p-sw₃)

  pass-pw : ∀ (c : F) {w : B.Circuit 5} → τ w • G ≈ G • τ w → τ (pw c w) • G ≈ G • τ (pw c w)
  pass-pw zero       p = passε
  pass-pw (suc zero) p = p

pass-R′ : (w : Vec F 4) → τ (R′ w) • G ≈ G • τ (R′ w)
pass-R′ (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ []) =
  slide (pass-pw c₁ in₁) (slide (pass-pw c₂ in₂) (slide (pass-pw c₃ in₃) (pass-pw c₄ in₄)))

------------------------------------------------------------------------
-- Independence

-- G commutes with every affine circuit fixing 0 and e₀.
indep : (γ : B.Circuit 5) → fn γ 0ᵛ ≡ 0ᵛ → fn γ e₀ ≡ e₀ → τ γ • G ≈ G • τ γ
indep γ h0 h1 with stab γ h0 h1
... | L′ , w , e = pass≈ (sym (embed (aff⇒ e))) (slide (pass-⌊⌋ L′) (pass-R′ w))

private
  fn-inv : (W : B.Circuit 5) (x : _) → fn (W ⁻¹) (fn W x) ≡ x
  fn-inv W x =
    Eq.trans (Eq.sym (fn-• (W ⁻¹) W x)) (Eq.trans (Eq.cong proj₁ (sound (Inv.inverseˡ 5) x)) (fn-ε x))

  module BI = Inv 5

-- The conjugate depends only on the images of 0 and e₀.
conj-indep : (α β : B.Circuit 5) → fn α 0ᵛ ≡ fn β 0ᵛ → fn α e₀ ≡ fn β e₀ →
             τ α • G • τ (α ⁻¹) ≈ τ β • G • τ (β ⁻¹)
conj-indep α β e0 e1 = sym (begin
  τ β • G • τ (β ⁻¹)                          ≈⟨ cong (embed (aff⇒ β≈)) (back G (embed (aff⇒ β⁻≈))) ⟩
  (τ α • τ γ) • G • (τ (γ ⁻¹) • τ (α ⁻¹))     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
  τ α • (τ γ • G) • τ (γ ⁻¹) • τ (α ⁻¹)       ≈⟨ back (τ α) (front _ (indep γ γ0 γ1)) ⟩
  τ α • (G • τ γ) • τ (γ ⁻¹) • τ (α ⁻¹)       ≈⟨ back (τ α) (by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl) ⟩
  τ α • G • (τ γ • τ (γ ⁻¹)) • τ (α ⁻¹)       ≈⟨ back (τ α) (back G (front _ (embed (aff⇒ (BI.inverseʳ {γ}))))) ⟩
  τ α • G • ε • τ (α ⁻¹)                      ≈⟨ back (τ α) (back G left-unit) ⟩
  τ α • G • τ (α ⁻¹)                          ∎)
  where
  γ : B.Circuit 5
  γ = α ⁻¹ • β

  γ0 : fn γ 0ᵛ ≡ 0ᵛ
  γ0 = Eq.trans (fn-• (α ⁻¹) β 0ᵛ) (Eq.trans (Eq.cong (fn (α ⁻¹)) (Eq.sym e0)) (fn-inv α 0ᵛ))

  γ1 : fn γ e₀ ≡ e₀
  γ1 = Eq.trans (fn-• (α ⁻¹) β e₀) (Eq.trans (Eq.cong (fn (α ⁻¹)) (Eq.sym e1)) (fn-inv α e₀))

  -- β = α γ and β⁻¹ = γ⁻¹ α⁻¹, in Blake's theory.
  β≈ : 5 B.⊢ β ≈ α • γ
  β≈ = PB.trans (PB.sym PB.left-unit) (PB.trans (PB.cong (PB.sym (BI.inverseʳ {α})) PB.refl) PB.assoc)

  β⁻≈ : 5 B.⊢ β ⁻¹ ≈ γ ⁻¹ • α ⁻¹
  β⁻≈ = PB.trans (BI.⁻¹-cong β≈) (BI.⁻¹-anti-homo-• {α} {γ})
