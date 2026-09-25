------------------------------------------------------------------------
-- Presentations of groups
--
-- A circuit on k wires placed by a swap network
--
-- `pl σ (u ↓ᵏ r)` puts the k-wire circuit u on the k wires that σ
-- brings to 0 … k − 1.  It depends on σ only through those k wires
-- (`place-eq`): two networks that agree there differ by a network
-- fixing the wires 0 … k − 1, which is a network k wires up (`lift-k`)
-- and so passes u (`local-comm`, gate by gate).  This generalises
-- OneWire's `on1-net` (k = 1) and BoxFrames' `frame-eq` (the box, whose
-- controls may moreover be permuted among themselves).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace where

open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_ ; remove ; lift₀ ; lift₀-remove)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (Σ ; _×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Symmetric.Interpretation using (⟦↑⟧)
open import Examples.Groups.Symmetric.Surjectivity using (surjective)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; net-↑ ; perm ; perm-≈)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS ; net-inv ; perm-inv)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl)

private
  variable
    r : ℕ

------------------------------------------------------------------------
-- k wires up

-- A circuit shifted up k wires.
up : ∀ k → Circuit r → Circuit (k + r)
up zero    w = w
up (suc k) w = up k w ↑

-- A circuit on the bottom k wires passes anything k wires up.
local-comm : ∀ {k} (u : Circuit k) (w : Circuit r) → (k + r) ⊢ (u ↓ᵏ r) • up k w ≈ up k w • (u ↓ᵏ r)
local-comm {k} [ gate₀ () ]ʷ w
local-comm {suc k} {r} [ gate₁ h ]ʷ w = PB-sym (comm-gate₁-w↑ h (up k w))
  where open Tools ((suc (k + r)) VRel,_===_) renaming (sym to PB-sym)
local-comm {suc (suc k)} {r} [ gate₂ h ]ʷ w = PB-sym (comm-gate₂-w↑↑ h (up k w))
  where open Tools ((suc (suc (k + r))) VRel,_===_) renaming (sym to PB-sym)
local-comm {suc k} {r} [ g ↥ ]ʷ w = lemma-cong↑ (([ g ]ʷ ↓ᵏ r) • up k w) (up k w • ([ g ]ʷ ↓ᵏ r)) (local-comm [ g ]ʷ w)
local-comm {k} {r} ε w = trans left-unit (sym right-unit)
  where open Tools ((k + r) VRel,_===_)
local-comm {k} {r} (a • b) w = begin
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

  -- lift0 of NetWires, keeping what the lifted network does.
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
lift-k {r} (suc k) u fix with lift0′ u (fix 0F (s≤s z≤n))
... | v , e , sv with lift-k k v (λ i i<k → sF-inj (Eq.trans (Eq.sym (sv i)) (fix (sF i) (s≤s i<k))))
... | w , e′ = w , trans e (lemma-cong↑ (net v) (up k (net w)) e′)
  where open Tools ((suc (k + r)) VRel,_===_)

------------------------------------------------------------------------
-- The placement depends only on the k wires

place-eq : ∀ {k} (u : Circuit k) (σ σ′ : Word (S.Gen (k + r))) →
           (∀ (j : Fin (k + r)) → toℕ j < k → perm σ′ ⟨$⟩ʳ (perm (revS σ) ⟨$⟩ʳ j) ≡ j) →
           pl σ (u ↓ᵏ r) ≈ pl σ′ (u ↓ᵏ r)
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
