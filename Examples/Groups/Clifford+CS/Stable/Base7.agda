------------------------------------------------------------------------
-- Presentations of groups
--
-- A seven-wire equation of the transport from completeness on six:
-- borrowed wires switched one at a time, through windows
--
-- Stable.Transport takes as a hypothesis, among ten closed equations,
-- the commutation on seven wires of the controlled CS of the wires 0 1,
-- Σ(0; 6, 1 | 2, 3), with the controlled CS of the wires 4 5,
-- Σ(4; 6, 5 | 2, 3) (`comm₂-base₂` at m = 1): the two images cover every
-- wire, so no wire can be inserted.  Here it is derived from
-- completeness on six wires (and five), as the joint paper's stability
-- argument does: each S-box is moved, one borrowed wire at a time, to
-- borrow inside the other's wires — Σ(0; 6, 1 | 4, 5) and
-- Σ(4; 6, 5 | 0, 1) — every switch an equation that leaves one wire
-- idle, so a window on six wires; and the two moved S-boxes sit on the
-- same five wires, where they commute by completeness on five.
--
-- A circuit u on five wires is placed by a swap network σ as
-- LocalPlace.pl σ (u ↓ᵏ 2), and two placements that send the five wires
-- to the same places are equal (LocalPlace.place-eq).  A window with
-- idle wire w is pl τ (top Y), τ carrying w to the top and Y a placement
-- in six wires.  The networks are computed and checked by
-- scratchpad/stable/nets.py.
--
-- That the two six-wire circuits of each window have the same semantics
-- (`Nets7.Windows₆`) is Stable.Windows6: deciding it by evaluation
-- exhausts 8 GB, the S-boxes being long, but each is a controlled CS
-- conjugated by a swap the control does not see.  The derivation is
-- stated over the record (`comm₂-base₂₁`) and instantiated with it
-- (`comm₂-base₂₇`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)

module Examples.Groups.Clifford+CS.Stable.Base7
  (c₅ : ∀ {u v : Circuit 5} → ⟦ u ⟧ ~ ⟦ v ⟧ → 5 ⊢ᵧ u ≈ v)
  (c₆ : ∀ {u v : Circuit 6} → ⟦ u ⟧ ~ ⟦ v ⟧ → 6 ⊢ᵧ u ≈ v)
  where

open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.SemanticSteps using (same-sem)
open import Examples.Groups.Clifford+CS.TopWeakening using (σ ; σ⁻¹ ; σσ⁻¹ ; nat ; top-cong)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; perm ; revS)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; pl-• ; pl-pl ; place-eq)
open import Examples.Groups.Clifford+CS.Lambda using (Σᵗ ; λ¹ ; λ¹ʷ ; λ⁰ ; Xᵗ)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (λ¹-~)
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb2-0-41-3 ; b-Sb0-2-43-1)
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.Soundness using (axiom-soundᵧ)
open import Examples.Groups.Clifford+CS.Stable.Weakening using (top-congᵧ)
open import Examples.Groups.Clifford+CS.Stable.Insert4 using (top2)
open import Examples.Groups.Clifford+CS.Stable.Nets7
open import Examples.Groups.Clifford+CS.Stable.Windows6 using (windows₆)
open import Examples.Groups.Clifford+CS.Stable.CalcSem using (F4-sem)
open import Examples.Groups.Clifford+CS.Stable.XPlace using (Xᵗ-placed)

private
  variable
    n : ℕ

private
  refl≡ᵧ : ∀ {n} {a b : Circuit n} → a ≡ b → n ⊢ᵧ a ≈ b
  refl≡ᵧ Eq.refl = PB.refl

  -- Two placements that send the five wires to the same places.
  frame : (u : Circuit 5) (s s′ : Word (S.Gen 7)) →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ 0F) ≡ 0F →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ sF 0F) ≡ sF 0F →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ sF (sF 0F)) ≡ sF (sF 0F) →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ sF (sF (sF 0F))) ≡ sF (sF (sF 0F)) →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ sF (sF (sF (sF 0F)))) ≡ sF (sF (sF (sF 0F))) →
          7 ⊢ᵧ P₇ s u ≈ P₇ s′ u
  frame u s s′ e0 e1 e2 e3 e4 = embed (place-eq u s s′ agree)
    where
    agree : ∀ (j : Fin 7) → toℕ j < 5 → perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ j) ≡ j
    agree 0F                          _ = e0
    agree (sF 0F)                     _ = e1
    agree (sF (sF 0F))                _ = e2
    agree (sF (sF (sF 0F)))           _ = e3
    agree (sF (sF (sF (sF 0F))))      _ = e4
    agree (sF (sF (sF (sF (sF j))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

  -- A window: wire τ carries to the top is idle on both sides.
  win : (t : Word (S.Gen 7)) (Y Y′ : Circuit 6) → ⟦ Y ⟧ ~ ⟦ Y′ ⟧ →
        7 ⊢ᵧ pl t (top Y) ≈ pl t (top Y′)
  win t Y Y′ e = PB.cong PB.refl (PB.cong (top-congᵧ (c₆ {Y} {Y′} e)) PB.refl)

  -- One borrowed wire switched: from the placement s, through the window
  -- t with the six-wire placements ρ and ρ′, to the placement s′.
  switch : (u : Circuit 5) (s t : Word (S.Gen 7)) (ρ ρ′ : List ℕ) (s′ : Word (S.Gen 7)) →
           7 ⊢ᵧ P₇ s u ≈ P₇ (t • ns₇ ρ) u →
           pl (ns₇ ρ) (u ↓ᵏ 2) ≡ top (P₆ (ns₆ ρ) u) →
           ⟦ P₆ (ns₆ ρ) u ⟧ ~ ⟦ P₆ (ns₆ ρ′) u ⟧ →
           pl (ns₇ ρ′) (u ↓ᵏ 2) ≡ top (P₆ (ns₆ ρ′) u) →
           7 ⊢ᵧ P₇ (t • ns₇ ρ′) u ≈ P₇ s′ u →
           7 ⊢ᵧ P₇ s u ≈ P₇ s′ u
  switch u s t ρ ρ′ s′ f₁ n₁ e n₂ f₂ = begin
    P₇ s u                              ≈⟨ f₁ ⟩
    P₇ (t • ns₇ ρ) u                    ≈⟨ sym (embed (pl-pl t (ns₇ ρ) (u ↓ᵏ 2))) ⟩
    pl t (pl (ns₇ ρ) (u ↓ᵏ 2))          ≈⟨ refl≡ᵧ (Eq.cong (pl t) n₁) ⟩
    pl t (top (P₆ (ns₆ ρ) u))           ≈⟨ win t (P₆ (ns₆ ρ) u) (P₆ (ns₆ ρ′) u) e ⟩
    pl t (top (P₆ (ns₆ ρ′) u))          ≈⟨ refl≡ᵧ (Eq.cong (pl t) (Eq.sym n₂)) ⟩
    pl t (pl (ns₇ ρ′) (u ↓ᵏ 2))         ≈⟨ embed (pl-pl t (ns₇ ρ′) (u ↓ᵏ 2)) ⟩
    P₇ (t • ns₇ ρ′) u                   ≈⟨ f₂ ⟩
    P₇ s′ u ∎
    where open Tools (7 YVRel,_===_)

module _ (W₆ : Windows₆) where
 open Windows₆ W₆

 private
  -- Both moved to the wires 0 1 4 5 6.
   N : Word (S.Gen 7)
   N = ns₇ (3 ∷ 2 ∷ 4 ∷ 3 ∷ 5 ∷ 4 ∷ [])

   -- Σ(0; 6, 1 | 2, 3) to Σ(0; 6, 1 | 2, 5) (idle wire 4) to
   -- Σ(0; 6, 1 | 4, 5) (idle wire 3).
   P-moved : 7 ⊢ᵧ Σᵗ 2 ≈ P₇ N Σ₀
   P-moved = begin
     Σᵗ 2
       ≈⟨ by-assoc Eq.refl ⟩
     P₇ (ns₇ (5 ∷ 4 ∷ [])) Σ₀
       ≈⟨ switch Σ₀ (ns₇ (5 ∷ 4 ∷ [])) (ns₇ (4 ∷ 5 ∷ [])) (4 ∷ []) (3 ∷ 4 ∷ [])
            (ns₇ (4 ∷ 3 ∷ 5 ∷ 4 ∷ []))
            (frame Σ₀ (ns₇ (5 ∷ 4 ∷ [])) (ns₇ (4 ∷ 5 ∷ []) • ns₇ (4 ∷ []))
               Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) Eq.refl
            w₁ Eq.refl
            (frame Σ₀ (ns₇ (4 ∷ 5 ∷ []) • ns₇ (3 ∷ 4 ∷ [])) (ns₇ (4 ∷ 3 ∷ 5 ∷ 4 ∷ []))
               Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) ⟩
     P₇ (ns₇ (4 ∷ 3 ∷ 5 ∷ 4 ∷ [])) Σ₀
       ≈⟨ switch Σ₀ (ns₇ (4 ∷ 3 ∷ 5 ∷ 4 ∷ [])) (ns₇ (3 ∷ 4 ∷ 5 ∷ [])) (3 ∷ 4 ∷ []) (2 ∷ 3 ∷ 4 ∷ []) N
            (frame Σ₀ (ns₇ (4 ∷ 3 ∷ 5 ∷ 4 ∷ [])) (ns₇ (3 ∷ 4 ∷ 5 ∷ []) • ns₇ (3 ∷ 4 ∷ []))
               Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) Eq.refl
            w₂ Eq.refl
            (frame Σ₀ (ns₇ (3 ∷ 4 ∷ 5 ∷ []) • ns₇ (2 ∷ 3 ∷ 4 ∷ [])) N
               Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) ⟩
     P₇ N Σ₀ ∎
     where open Tools (7 YVRel,_===_)

   -- A circuit one wire up is the circuit with an idle wire on top,
   -- carried down by the cycle σ.
   ↑≈ : (w : Circuit n) → (₁₊ n) ⊢ w ↑ ≈ σ n • top w • σ⁻¹ n
   ↑≈ {n} w = begin
     w ↑                         ≈⟨ sym right-unit ⟩
     w ↑ • ε                     ≈⟨ back _ (sym (σσ⁻¹ n)) ⟩
     w ↑ • σ n • σ⁻¹ n           ≈⟨ sym assoc ⟩
     (w ↑ • σ n) • σ⁻¹ n         ≈⟨ front _ (nat w) ⟩
     (σ n • top w) • σ⁻¹ n       ≈⟨ assoc ⟩
     σ n • top w • σ⁻¹ n ∎
     where open Tools ((₁₊ n) VRel,_===_)

   Q-placed : 7 ⊢ Σ₂ ↑ ↑ ≈ P₇ (ns₇ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) Σ₂
   Q-placed = begin
     Σ₂ ↑ ↑                                       ≈⟨ ↑≈ (Σ₂ ↑) ⟩
     σ 6 • top (Σ₂ ↑) • σ⁻¹ 6                     ≈⟨ back _ (front _ (top-cong (↑≈ Σ₂))) ⟩
     σ 6 • top (σ 5 • top Σ₂ • σ⁻¹ 5) • σ⁻¹ 6     ≈⟨ by-assoc Eq.refl ⟩
     P₇ (ns₇ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) Σ₂ ∎
     where open Tools (7 VRel,_===_)

   -- Σ(4; 6, 5 | 2, 3) to Σ(4; 6, 5 | 0, 3) (idle wire 1) to
   -- Σ(4; 6, 5 | 0, 1) (idle wire 2).
   Q-moved : 7 ⊢ᵧ Σ₂ ↑ ↑ ≈ P₇ N Σ₂
   Q-moved = begin
     Σ₂ ↑ ↑
       ≈⟨ embed Q-placed ⟩
     P₇ (ns₇ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) Σ₂
       ≈⟨ switch Σ₂ (ns₇ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) (ns₇ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []))
            (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) (ns₇ (2 ∷ 1 ∷ 3 ∷ 2 ∷ 4 ∷ 3 ∷ 5 ∷ 4 ∷ []))
            (frame Σ₂ (ns₇ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []))
               (ns₇ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) • ns₇ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []))
               Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) Eq.refl
            w₃ Eq.refl
            (frame Σ₂ (ns₇ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) • ns₇ (1 ∷ 2 ∷ 3 ∷ 4 ∷ []))
               (ns₇ (2 ∷ 1 ∷ 3 ∷ 2 ∷ 4 ∷ 3 ∷ 5 ∷ 4 ∷ []))
               Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) ⟩
     P₇ (ns₇ (2 ∷ 1 ∷ 3 ∷ 2 ∷ 4 ∷ 3 ∷ 5 ∷ 4 ∷ [])) Σ₂
       ≈⟨ switch Σ₂ (ns₇ (2 ∷ 1 ∷ 3 ∷ 2 ∷ 4 ∷ 3 ∷ 5 ∷ 4 ∷ [])) (ns₇ (2 ∷ 3 ∷ 4 ∷ 5 ∷ []))
            (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) (2 ∷ 3 ∷ 4 ∷ []) N
            (frame Σ₂ (ns₇ (2 ∷ 1 ∷ 3 ∷ 2 ∷ 4 ∷ 3 ∷ 5 ∷ 4 ∷ [])) (ns₇ (2 ∷ 3 ∷ 4 ∷ 5 ∷ []) • ns₇ (1 ∷ 2 ∷ 3 ∷ 4 ∷ []))
               Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) Eq.refl
            w₄ Eq.refl
            (frame Σ₂ (ns₇ (2 ∷ 3 ∷ 4 ∷ 5 ∷ []) • ns₇ (2 ∷ 3 ∷ 4 ∷ [])) N
               Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) ⟩
     P₇ N Σ₂ ∎
     where open Tools (7 YVRel,_===_)

   -- On the same five wires they commute, by completeness on five: they
   -- are the controlled images of the commuting CS of the wires 0 1 and 2 3.
   comm₅ : 5 ⊢ᵧ Σ₂ • Σ₀ ≈ Σ₀ • Σ₂
   comm₅ = c₅ {Σ₂ • Σ₀} {Σ₀ • Σ₂}
             (λ¹-~ {0} {[ gate₂ CS-gate ↥ ↥ ]ʷ • [ gate₂ CS-gate ]ʷ} {[ gate₂ CS-gate ]ʷ • [ gate₂ CS-gate ↥ ↥ ]ʷ}
               (axiom-soundᵧ (comm₂ᵧ CS-gate (gate₂ CS-gate))))

   moved-comm : 7 ⊢ᵧ P₇ N Σ₂ • P₇ N Σ₀ ≈ P₇ N Σ₀ • P₇ N Σ₂
   moved-comm = begin
     P₇ N Σ₂ • P₇ N Σ₀              ≈⟨ sym (embed (pl-• N (Σ₂ ↓ᵏ 2) (Σ₀ ↓ᵏ 2))) ⟩
     pl N ((Σ₂ • Σ₀) ↓ᵏ 2)          ≈⟨ cong refl (cong (top-congᵧ (top-congᵧ comm₅)) refl) ⟩
     pl N ((Σ₀ • Σ₂) ↓ᵏ 2)          ≈⟨ embed (pl-• N (Σ₀ ↓ᵏ 2) (Σ₂ ↓ᵏ 2)) ⟩
     P₇ N Σ₀ • P₇ N Σ₂ ∎
     where open Tools (7 YVRel,_===_)

 ------------------------------------------------------------------------
 -- The equation

 comm₂-base₂₁ : (₂₊ (₄₊ (suc zero))) ⊢ᵧ λ¹ {suc (suc zero)} (top2 (₃₊ (suc zero)) CS-gate) • λ¹ {suc (suc zero)} (gate₂ CS-gate)
                                     ≈ λ¹ {suc (suc zero)} (gate₂ CS-gate) • λ¹ {suc (suc zero)} (top2 (₃₊ (suc zero)) CS-gate)
 comm₂-base₂₁ = begin
   Σ₂ ↑ ↑ • Σᵗ 2              ≈⟨ cong Q-moved P-moved ⟩
   P₇ N Σ₂ • P₇ N Σ₀          ≈⟨ moved-comm ⟩
   P₇ N Σ₀ • P₇ N Σ₂          ≈⟨ sym (cong P-moved Q-moved) ⟩
   Σᵗ 2 • Σ₂ ↑ ↑ ∎
   where open Tools (7 YVRel,_===_)

------------------------------------------------------------------------
 -- The same with the first letter white (Stable.Mixed.MixBase): X on the
 -- control is X on the moved S-box's control (Stable.XPlace), and on five
 -- wires the white and the black S-box commute by (F4) there.

 private
   sw5 : ℕ → Word (S.Gen 5)
   sw5 0 = [ S.gate₂ S.σ-gate ]ʷ
   sw5 1 = [ S.gate₂ S.σ-gate S.↥ ]ʷ
   sw5 2 = [ S.gate₂ S.σ-gate S.↥ S.↥ ]ʷ
   sw5 3 = [ S.gate₂ S.σ-gate S.↥ S.↥ S.↥ ]ʷ
   sw5 _ = ε

   ns5 : List ℕ → Word (S.Gen 5)
   ns5 []       = ε
   ns5 (p ∷ ps) = sw5 p • ns5 ps

   comm⁰₅ : 5 ⊢ᵧ (Xᵗ 4 • Σ₂ • Xᵗ 4) • Σ₀ ≈ Σ₀ • (Xᵗ 4 • Σ₂ • Xᵗ 4)
   comm⁰₅ = c₅ {(Xᵗ 4 • Σ₂ • Xᵗ 4) • Σ₀} {Σ₀ • (Xᵗ 4 • Σ₂ • Xᵗ 4)}
              (F4-sem {0} (gate₂ CS-gate ↥ ↥) (gate₂ CS-gate))

   X-moved : 7 ⊢ Xᵗ 6 ≈ P₇ N (Xᵗ 4)
   X-moved = begin
     Xᵗ 6                                                 ≈⟨ Xᵗ-placed 6 (N • ns₇ (3 ∷ 2 ∷ 1 ∷ 0 ∷ [])) Eq.refl ⟩
     pl (N • ns₇ (3 ∷ 2 ∷ 1 ∷ 0 ∷ [])) (X {0} ↓ᵏ 6)        ≈⟨ sym (pl-pl N (ns₇ (3 ∷ 2 ∷ 1 ∷ 0 ∷ [])) (X {0} ↓ᵏ 6)) ⟩
     pl N (pl (ns₇ (3 ∷ 2 ∷ 1 ∷ 0 ∷ [])) (X {0} ↓ᵏ 6))     ≈⟨ sym (cong refl (cong (top-cong (top-cong (Xᵗ-placed 4 (ns5 (3 ∷ 2 ∷ 1 ∷ 0 ∷ [])) Eq.refl))) refl)) ⟩
     P₇ N (Xᵗ 4) ∎
     where open Tools (7 VRel,_===_)

   moved-comm⁰ : 7 ⊢ᵧ (P₇ N (Xᵗ 4) • P₇ N Σ₂ • P₇ N (Xᵗ 4)) • P₇ N Σ₀
                    ≈ P₇ N Σ₀ • (P₇ N (Xᵗ 4) • P₇ N Σ₂ • P₇ N (Xᵗ 4))
   moved-comm⁰ = begin
     (P₇ N x • P₇ N Σ₂ • P₇ N x) • P₇ N Σ₀
       ≈⟨ cong (trans (back _ (sym (embed (pl-• N (Σ₂ ↓ᵏ 2) (x ↓ᵏ 2)))))
                      (sym (embed (pl-• N (x ↓ᵏ 2) ((Σ₂ • x) ↓ᵏ 2))))) refl ⟩
     P₇ N (x • Σ₂ • x) • P₇ N Σ₀
       ≈⟨ sym (embed (pl-• N ((x • Σ₂ • x) ↓ᵏ 2) (Σ₀ ↓ᵏ 2))) ⟩
     pl N (((x • Σ₂ • x) • Σ₀) ↓ᵏ 2)
       ≈⟨ cong refl (cong (top-congᵧ (top-congᵧ comm⁰₅)) refl) ⟩
     pl N ((Σ₀ • (x • Σ₂ • x)) ↓ᵏ 2)
       ≈⟨ embed (pl-• N (Σ₀ ↓ᵏ 2) ((x • Σ₂ • x) ↓ᵏ 2)) ⟩
     P₇ N Σ₀ • P₇ N (x • Σ₂ • x)
       ≈⟨ cong refl (trans (embed (pl-• N (x ↓ᵏ 2) ((Σ₂ • x) ↓ᵏ 2)))
                           (back _ (embed (pl-• N (Σ₂ ↓ᵏ 2) (x ↓ᵏ 2))))) ⟩
     P₇ N Σ₀ • (P₇ N x • P₇ N Σ₂ • P₇ N x) ∎
     where
     x = Xᵗ 4
     open Tools (7 YVRel,_===_)

 mix-base₁ : (₂₊ (₄₊ (suc zero))) ⊢ᵧ λ⁰ {suc (suc zero)} (top2 (₃₊ (suc zero)) CS-gate) • λ¹ {suc (suc zero)} (gate₂ CS-gate)
                                 ≈ λ¹ {suc (suc zero)} (gate₂ CS-gate) • λ⁰ {suc (suc zero)} (top2 (₃₊ (suc zero)) CS-gate)
 mix-base₁ = begin
   (Xᵗ 6 • Σ₂ ↑ ↑ • Xᵗ 6) • Σᵗ 2                     ≈⟨ cong (cong xm (cong Q-moved xm)) P-moved ⟩
   (P₇ N (Xᵗ 4) • P₇ N Σ₂ • P₇ N (Xᵗ 4)) • P₇ N Σ₀    ≈⟨ moved-comm⁰ ⟩
   P₇ N Σ₀ • (P₇ N (Xᵗ 4) • P₇ N Σ₂ • P₇ N (Xᵗ 4))    ≈⟨ sym (cong P-moved (cong xm (cong Q-moved xm))) ⟩
   Σᵗ 2 • (Xᵗ 6 • Σ₂ ↑ ↑ • Xᵗ 6) ∎
   where
   xm = embed X-moved
   open Tools (7 YVRel,_===_)

-- From completeness on five and six wires alone.
mix-base-7 : (₂₊ (₄₊ (suc zero))) ⊢ᵧ λ⁰ {suc (suc zero)} (top2 (₃₊ (suc zero)) CS-gate) • λ¹ {suc (suc zero)} (gate₂ CS-gate)
                                ≈ λ¹ {suc (suc zero)} (gate₂ CS-gate) • λ⁰ {suc (suc zero)} (top2 (₃₊ (suc zero)) CS-gate)
mix-base-7 = mix-base₁ windows₆

-- From completeness on five and six wires alone.
comm₂-base₂₇ : (₂₊ (₄₊ (suc zero))) ⊢ᵧ λ¹ {suc (suc zero)} (top2 (₃₊ (suc zero)) CS-gate) • λ¹ {suc (suc zero)} (gate₂ CS-gate)
                                   ≈ λ¹ {suc (suc zero)} (gate₂ CS-gate) • λ¹ {suc (suc zero)} (top2 (₃₊ (suc zero)) CS-gate)
comm₂-base₂₇ = comm₂-base₂₁ windows₆
