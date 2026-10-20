------------------------------------------------------------------------
-- Presentations of groups
--
-- A circuit on k wires placed by a swap network
--
-- Real-Clifford+CH.GeneralN.LocalPlace for the Clifford+CS gates.
-- `pl σ g = net σ • g • net (revS σ)` conjugates g by a network; with
-- g = u ↓ᵏ r it puts the k-wire circuit u on the k wires that σ brings
-- to 0 … k − 1, and it depends on σ only through those k wires
-- (`place-eq`): two networks that agree there differ by a network
-- fixing the wires 0 … k − 1, which is a network k wires up (`lift-k`)
-- and so passes u (`local-comm`, gate by gate).  Placing is a
-- congruence and a homomorphism (`pl-cong`, `pl-•`), and placements
-- compose (`pl-pl`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.LocalPlace where

open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_ ; remove ; lift₀-remove)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; s≤s ; z≤n)
open import Data.Product using (Σ ; _×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Symmetric.Interpretation using (⟦↑⟧)
open import Examples.Groups.Symmetric.Surjectivity using (surjective)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.PermCalc
  using (net ; net-↑ ; perm ; perm-≈ ; revS ; net-inv ; net-inv′)

private
  variable
    n r : ℕ

------------------------------------------------------------------------
-- Placing by a network

pl : Word (S.Gen n) → Circuit n → Circuit n
pl σ g = net σ • g • net (revS σ)

pl-cong : ∀ (σ : Word (S.Gen n)) {g g′ : Circuit n} → n ⊢ g ≈ g′ → n ⊢ pl σ g ≈ pl σ g′
pl-cong {n} σ e = cong refl (cong e refl)
  where open Tools (n VRel,_===_)

pl-• : ∀ (σ : Word (S.Gen n)) (g h : Circuit n) → n ⊢ pl σ (g • h) ≈ pl σ g • pl σ h
pl-• {n} σ g h = begin
  net σ • (g • h) • net (revS σ)
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
  (net σ • g) • (h • net (revS σ))
    ≈⟨ back _ (sym left-unit) ⟩
  (net σ • g) • (ε • h • net (revS σ))
    ≈⟨ back _ (front _ (sym (net-inv′ σ))) ⟩
  (net σ • g) • ((net (revS σ) • net σ) • h • net (revS σ))
    ≈⟨ by-passoc ((□ • □) • ((□ • □) • □ • □)) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (net σ • g • net (revS σ)) • (net σ • h • net (revS σ)) ∎
  where open Tools (n VRel,_===_)

pl-ε : ∀ (σ : Word (S.Gen n)) → n ⊢ pl σ ε ≈ ε
pl-ε {n} σ = trans (back _ left-unit) (net-inv σ)
  where open Tools (n VRel,_===_)

-- Placements compose.
pl-pl : ∀ (σ τ : Word (S.Gen n)) (g : Circuit n) → n ⊢ pl σ (pl τ g) ≈ pl (σ • τ) g
pl-pl {n} σ τ g = by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl
  where open Tools (n VRel,_===_)

------------------------------------------------------------------------
-- k wires up

-- A circuit shifted up k wires.
up : ∀ k → Circuit r → Circuit (k + r)
up zero    w = w
up (suc k) w = up k w ↑

-- A circuit on the bottom k wires passes anything k wires up.
local-comm : ∀ {k} (u : Circuit k) (w : Circuit r) → (k + r) ⊢ (u ↓ᵏ r) • up k w ≈ up k w • (u ↓ᵏ r)
local-comm {r = r} {k = k} [ gate₀ h ]ʷ w = PB.sym (comm-gate₀-w h (up k w))
local-comm {r = r} {k = suc k} [ gate₁ h ]ʷ w = PB-sym (comm-gate₁-w↑ h (up k w))
  where open Tools ((suc (k + r)) VRel,_===_) renaming (sym to PB-sym)
local-comm {r = r} {k = suc (suc k)} [ gate₂ h ]ʷ w = PB-sym (comm-gate₂-w↑↑ h (up k w))
  where open Tools ((suc (suc (k + r))) VRel,_===_) renaming (sym to PB-sym)
local-comm {r = r} {k = suc k} [ g ↥ ]ʷ w =
  lemma-cong↑ (([ g ]ʷ ↓ᵏ r) • up k w) (up k w • ([ g ]ʷ ↓ᵏ r)) (local-comm [ g ]ʷ w)
local-comm {r = r} {k = k} ε w = trans left-unit (sym right-unit)
  where open Tools ((k + r) VRel,_===_)
local-comm {r = r} {k = k} (a • b) w = begin
  ((a ↓ᵏ r) • (b ↓ᵏ r)) • up k w   ≈⟨ assoc ⟩
  (a ↓ᵏ r) • ((b ↓ᵏ r) • up k w)   ≈⟨ back _ (local-comm b w) ⟩
  (a ↓ᵏ r) • (up k w • (b ↓ᵏ r))   ≈⟨ sym assoc ⟩
  ((a ↓ᵏ r) • up k w) • (b ↓ᵏ r)   ≈⟨ front _ (local-comm a w) ⟩
  (up k w • (a ↓ᵏ r)) • (b ↓ᵏ r)   ≈⟨ assoc ⟩
  up k w • (a ↓ᵏ r) • (b ↓ᵏ r) ∎
  where open Tools ((k + r) VRel,_===_)

------------------------------------------------------------------------
-- A network fixing the bottom k wires is a network k wires up

private
  sF-inj : ∀ {n} {a b : Fin n} → sF a ≡ sF b → a ≡ b
  sF-inj Eq.refl = Eq.refl

  lift0′ : ∀ {n} (u : Word (S.Gen (₁₊ n))) → perm u ⟨$⟩ʳ 0F ≡ 0F →
           Σ (Word (S.Gen n)) λ v → ((₁₊ n) ⊢ net u ≈ net v ↑) ×
                                    (∀ i → perm u ⟨$⟩ʳ sF i ≡ sF (perm v ⟨$⟩ʳ i))
  lift0′ {n} u p with surjective {n} (remove 0F (perm u))
  ... | v , ok = v , Eq.subst (λ w → (₁₊ n) ⊢ net u ≈ w) (net-↑ v) (perm-≈ {u = u} {v = v S.↑} pw) , sv
    where
    sv : ∀ i → perm u ⟨$⟩ʳ sF i ≡ sF (perm v ⟨$⟩ʳ i)
    sv i = Eq.trans (Eq.sym (lift₀-remove (perm u) p (sF i))) (Eq.cong sF (Eq.sym (ok PB.refl i)))

    pw : ∀ k → perm u ⟨$⟩ʳ k ≡ perm (v S.↑) ⟨$⟩ʳ k
    pw 0F     = Eq.trans p (Eq.sym (⟦↑⟧ v 0F))
    pw (sF k) = Eq.trans (sv k) (Eq.sym (⟦↑⟧ v (sF k)))

lift-k : ∀ k (u : Word (S.Gen (k + r))) → (∀ (i : Fin (k + r)) → toℕ i < k → perm u ⟨$⟩ʳ i ≡ i) →
         Σ (Word (S.Gen r)) λ v → (k + r) ⊢ net u ≈ up k (net v)
lift-k {r} zero    u fix = u , refl
  where open Tools (r VRel,_===_)
lift-k {r} (suc k) u fix = step₁ (lift0′ u (fix 0F (s≤s z≤n)))
  where
  open Tools ((suc (k + r)) VRel,_===_)
  -- Helpers taking the two results as arguments: abstracted by ,
  -- they made the goal be normalised (15 s).
  step₁ : (Σ (Word (S.Gen (k + r))) λ v → ((₁₊ (k + r)) ⊢ net u ≈ net v ↑) ×
                                          (∀ i → perm u ⟨$⟩ʳ sF i ≡ sF (perm v ⟨$⟩ʳ i))) →
          Σ (Word (S.Gen r)) λ w → (suc k + r) ⊢ net u ≈ up (suc k) (net w)
  step₁ (v , e , sv) = step₂ (lift-k k v (λ i i<k → sF-inj (Eq.trans (Eq.sym (sv i)) (fix (sF i) (s≤s i<k)))))
    where
    step₂ : (Σ (Word (S.Gen r)) λ w → (k + r) ⊢ net v ≈ up k (net w)) →
            Σ (Word (S.Gen r)) λ w → (suc k + r) ⊢ net u ≈ up (suc k) (net w)
    step₂ (w , e′) = w , trans e (lemma-cong↑ (net v) (up k (net w)) e′)

------------------------------------------------------------------------
-- The placement depends only on the k wires

place-eq : ∀ {k} (u : Circuit k) (σ σ′ : Word (S.Gen (k + r))) →
           (∀ (j : Fin (k + r)) → toℕ j < k → perm σ′ ⟨$⟩ʳ (perm (revS σ) ⟨$⟩ʳ j) ≡ j) →
           (k + r) ⊢ pl σ (u ↓ᵏ r) ≈ pl σ′ (u ↓ᵏ r)
place-eq {r} {k} u σ σ′ agree with lift-k k (revS σ • σ′) agree
... | v , e = sym (begin
  net σ′ • U • net (revS σ′)
    ≈⟨ sym left-unit ⟩
  ε • (net σ′ • U • net (revS σ′))
    ≈⟨ front _ (sym (net-inv σ)) ⟩
  (net σ • net (revS σ)) • (net σ′ • U • net (revS σ′))
    ≈⟨ by-passoc ((□ • □) • (□ • □ • □)) (□ • ((□ • □) • □) • □) Eq.refl ⟩
  net σ • ((net (revS σ) • net σ′) • U) • net (revS σ′)
    ≈⟨ back _ (front _ (trans (front _ e) (sym (local-comm u (net v))))) ⟩
  net σ • (U • up k (net v)) • net (revS σ′)
    ≈⟨ back _ (front _ (back _ (sym e))) ⟩
  net σ • (U • (net (revS σ) • net σ′)) • net (revS σ′)
    ≈⟨ by-passoc (□ • (□ • (□ • □)) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
  net σ • U • net (revS σ) • (net σ′ • net (revS σ′))
    ≈⟨ back _ (back _ (trans (back _ (net-inv σ′)) right-unit)) ⟩
  net σ • U • net (revS σ) ∎)
  where
  open Tools ((k + r) VRel,_===_)
  U : Circuit (k + r)
  U = u ↓ᵏ r
