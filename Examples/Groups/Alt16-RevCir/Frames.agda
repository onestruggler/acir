------------------------------------------------------------------------
-- Presentations of groups
--
-- Four wires: frames
--
-- The NOT gates and the swaps generate the symmetries of the 4-cube,
-- and a gate anywhere on the four wires, with black or white controls,
-- is a gate on the bottom wires between a word p of them and its
-- reverse: a three-wire circuit b in the frame p.  This module decides
-- the two kinds of equation that such words obey for structural
-- reasons, so that a derivation can use each as one step:
--
-- * hstep u v: two words in the NOT gates and swaps with the same
--   function are equal.  hnorm brings such a word to the form
--   q • X₃ᵉ • r — q on the bottom three wires, r one of four words that
--   bring each wire to the top — one letter at a time, by a table
--   (tab) whose 28 entries are derived from the rules; two words with
--   the same r, the same e and q's of the same function are then equal
--   by completeness on three wires.
--
-- * frame p p′ b b′: p • b • p⁻¹ = p′ • b′ • p′⁻¹ when p⁻¹ • p′ keeps
--   the top wire in place, q • X₃ᵉ say, and q • b′ • q⁻¹ and b have the
--   same function (X₃ commutes with circuits on the bottom wires).
--
-- The evidence of each is a boolean that evaluation decides.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Frames where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _xor_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; reverse)
open import Data.List.Properties using (map-++)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Alt16-RevCir.Semantics using (same)
open import Examples.Groups.Alt16-RevCir.Syntactics
  using ( Gen ; Circuit ; X-gate ; CX-gate ; Ex-gate ; CCX-gate
        ; gate₀ ; gate₁ ; gate₂ ; gate₃
        ; X-gen ; CX-gen ; Ex-gen ; CCX-gen ; _↥ ; _↧ᵏ_ )
open import Examples.Groups.Alt16-RevCir.Theory using (module T)
open import Examples.Groups.Alt16-RevCir.FourWire

open PB (T._VRel,_===_ 4)
  using (_≈_ ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)
  renaming (refl to refl≈)
open PP (T._VRel,_===_ 4) using (word-setoid ; module Pattern-Assoc)
open Pattern-Assoc using (by-passoc ; □)

------------------------------------------------------------------------
-- The letters

-- The NOT gates and the swaps.
data HL : Set where
  hx0 hx1 hx2 hx3 he0 he1 he2 : HL

⌜_⌝ : HL → Gen 4
⌜ hx0 ⌝ = x0
⌜ hx1 ⌝ = x1
⌜ hx2 ⌝ = x2
⌜ hx3 ⌝ = x3
⌜ he0 ⌝ = ex0
⌜ he1 ⌝ = ex1
⌜ he2 ⌝ = ex2

⌜_⌝ˡ : List HL → List (Gen 4)
⌜_⌝ˡ = map ⌜_⌝

-- A circuit on the bottom three wires.
dn : List (Gen 3) → List (Gen 4)
dn = map (_↧ᵏ 1)

private
  a₃ b₃ d₃ s₃ t₃ : Gen 3
  a₃ = X-gen
  b₃ = X-gen ↥
  d₃ = X-gen ↥ ↥
  s₃ = Ex-gen
  t₃ = Ex-gen ↥

  H++ : (u v : List HL) → ⟪ ⌜ u ++ v ⌝ˡ ⟫ ≈ ⟪ ⌜ u ⌝ˡ ⟫ • ⟪ ⌜ v ⌝ˡ ⟫
  H++ u v = trans (⟪≈⟫ (map-++ ⌜_⌝ u v)) (⟪++⟫ ⌜ u ⌝ˡ ⌜ v ⌝ˡ)

  dn++ : (q b : List (Gen 3)) → ⟪ dn (q ++ b) ⟫ ≈ ⟪ dn q ⟫ • ⟪ dn b ⟫
  dn++ q b = trans (⟪≈⟫ (map-++ (_↧ᵏ 1) q b)) (⟪++⟫ (dn q) (dn b))

------------------------------------------------------------------------
-- X on the top wire commutes with the bottom three wires

private
  x3-letter : (g : Gen 3) →
              [ x3 ]ʷ • [ g ↧ᵏ 1 ]ʷ ≈ [ g ↧ᵏ 1 ]ʷ • [ x3 ]ʷ
  x3-letter (gate₁ X-gate)       = PB.axiom (T.comm₁ X-gate (X-gen ↥ ↥))
  x3-letter (gate₂ CX-gate)      = PB.axiom (T.comm₂ CX-gate (X-gen ↥))
  x3-letter (gate₂ Ex-gate)      = PB.axiom (T.comm₂ Ex-gate (X-gen ↥))
  x3-letter (gate₃ CCX-gate)     = PB.axiom (T.comm₃ CCX-gate X-gen)
  x3-letter (gate₁ X-gate ↥)     =
    PB.axiom (T.cong↑ (T.comm₁ X-gate (X-gen ↥)))
  x3-letter (gate₂ CX-gate ↥)    =
    PB.axiom (T.cong↑ (T.comm₂ CX-gate X-gen))
  x3-letter (gate₂ Ex-gate ↥)    =
    PB.axiom (T.cong↑ (T.comm₂ Ex-gate X-gen))
  x3-letter (gate₁ X-gate ↥ ↥)   =
    PB.axiom (T.cong↑ (T.cong↑ (T.comm₁ X-gate X-gen)))
  x3-letter (gate₀ ())
  x3-letter (gate₀ () ↥)
  x3-letter (gate₀ () ↥ ↥)
  x3-letter (gate₀ () ↥ ↥ ↥)

  x3-word : (b : List (Gen 3)) →
            [ x3 ]ʷ • ⟪ dn b ⟫ ≈ ⟪ dn b ⟫ • [ x3 ]ʷ
  x3-word []      = trans right-unit (sym left-unit)
  x3-word (g ∷ b) = begin
    [ x3 ]ʷ • ([ g ↧ᵏ 1 ]ʷ • ⟪ dn b ⟫)   ≈⟨ sym assoc ⟩
    ([ x3 ]ʷ • [ g ↧ᵏ 1 ]ʷ) • ⟪ dn b ⟫   ≈⟨ cong (x3-letter g) refl≈ ⟩
    ([ g ↧ᵏ 1 ]ʷ • [ x3 ]ʷ) • ⟪ dn b ⟫   ≈⟨ assoc ⟩
    [ g ↧ᵏ 1 ]ʷ • ([ x3 ]ʷ • ⟪ dn b ⟫)   ≈⟨ cong refl≈ (x3-word b) ⟩
    [ g ↧ᵏ 1 ]ʷ • (⟪ dn b ⟫ • [ x3 ]ʷ)   ≈⟨ sym assoc ⟩
    ([ g ↧ᵏ 1 ]ʷ • ⟪ dn b ⟫) • [ x3 ]ʷ   ∎
    where open SR word-setoid

-- X on the top wire, or nothing.
x3^ : Bool → List (Gen 4)
x3^ false = []
x3^ true  = x3 ∷ []

private
  E-word : (e : Bool) (b : List (Gen 3)) →
           ⟪ x3^ e ⟫ • ⟪ dn b ⟫ ≈ ⟪ dn b ⟫ • ⟪ x3^ e ⟫
  E-word false b = trans left-unit (sym right-unit)
  E-word true  b =
    trans (cong right-unit refl≈)
          (trans (x3-word b) (cong refl≈ (sym right-unit)))

  x3x3 : ⟪ x3^ true ⟫ • ⟪ x3^ true ⟫ ≈ ε
  x3x3 = trans (cong right-unit refl≈)
               (prf (top (d₃ ∷ d₃ ∷ []) [] refl))

  E-mul : (e e′ : Bool) → ⟪ x3^ e ⟫ • ⟪ x3^ e′ ⟫ ≈ ⟪ x3^ (e xor e′) ⟫
  E-mul false e′    = left-unit
  E-mul true  false = right-unit
  E-mul true  true  = x3x3

  E-sq : (e : Bool) → ⟪ x3^ e ⟫ • ⟪ x3^ e ⟫ ≈ ε
  E-sq false = left-unit
  E-sq true  = x3x3

------------------------------------------------------------------------
-- The table

-- The words that bring a wire to the top: none, the top swap, and the
-- swaps below it.
data Rep : Set where
  r0 r1 r2 r3 : Rep

rep : Rep → List (Gen 4)
rep r0 = []
rep r1 = ex2 ∷ []
rep r2 = ex2 ∷ ex1 ∷ []
rep r3 = ex2 ∷ ex1 ∷ ex0 ∷ []

record Out : Set where
  constructor out
  field
    ob : List (Gen 3)
    oe : Bool
    or : Rep

open Out

-- rep r followed by a letter is a letter on the bottom wires or X on
-- the top wire, followed by a rep.
tab : Rep → HL → Out
tab r0 hx0 = out (a₃ ∷ []) false r0
tab r0 hx1 = out (b₃ ∷ []) false r0
tab r0 hx2 = out (d₃ ∷ []) false r0
tab r0 hx3 = out []        true  r0
tab r0 he0 = out (s₃ ∷ []) false r0
tab r0 he1 = out (t₃ ∷ []) false r0
tab r0 he2 = out []        false r1
tab r1 hx0 = out (a₃ ∷ []) false r1
tab r1 hx1 = out (b₃ ∷ []) false r1
tab r1 hx2 = out []        true  r1
tab r1 hx3 = out (d₃ ∷ []) false r1
tab r1 he0 = out (s₃ ∷ []) false r1
tab r1 he1 = out []        false r2
tab r1 he2 = out []        false r0
tab r2 hx0 = out (a₃ ∷ []) false r2
tab r2 hx1 = out []        true  r2
tab r2 hx2 = out (b₃ ∷ []) false r2
tab r2 hx3 = out (d₃ ∷ []) false r2
tab r2 he0 = out []        false r3
tab r2 he1 = out []        false r1
tab r2 he2 = out (t₃ ∷ []) false r2
tab r3 hx0 = out []        true  r3
tab r3 hx1 = out (a₃ ∷ []) false r3
tab r3 hx2 = out (b₃ ∷ []) false r3
tab r3 hx3 = out (d₃ ∷ []) false r3
tab r3 he0 = out []        false r2
tab r3 he1 = out (s₃ ∷ []) false r3
tab r3 he2 = out (t₃ ∷ []) false r3

private
  -- Pushing a letter through a swap, on the bottom or the top three
  -- wires.
  b2 t2 : (x y x′ y′ : Gen 3) →
          same 3 ⟪ x ∷ y ∷ [] ⟫ ⟪ x′ ∷ y′ ∷ [] ⟫ ≡ true → Eqn 4
  b2 x y x′ y′ = bot (x ∷ y ∷ []) (x′ ∷ y′ ∷ [])
  t2 x y x′ y′ = top (x ∷ y ∷ []) (x′ ∷ y′ ∷ [])

  braid₃ : Eqn 3
  braid₃ = sem₃ (t₃ ∷ s₃ ∷ t₃ ∷ []) (s₃ ∷ t₃ ∷ s₃ ∷ []) refl

  tab-ok : (r : Rep) (y : HL) →
           ⟪ rep r ++ ⌜ y ⌝ ∷ [] ⟫ ≈
           ⟪ dn (ob (tab r y)) ++ (x3^ (oe (tab r y)) ++ rep (or (tab r y))) ⟫
  tab-ok r0 hx0 = refl≈
  tab-ok r0 hx1 = refl≈
  tab-ok r0 hx2 = refl≈
  tab-ok r0 hx3 = refl≈
  tab-ok r0 he0 = refl≈
  tab-ok r0 he1 = refl≈
  tab-ok r0 he2 = refl≈
  tab-ok r1 hx0 = prf comm-ex2-x0
  tab-ok r1 hx1 = prf (t2 t₃ a₃ a₃ t₃ refl)
  tab-ok r1 hx2 = prf (t2 t₃ b₃ d₃ t₃ refl)
  tab-ok r1 hx3 = prf (t2 t₃ d₃ b₃ t₃ refl)
  tab-ok r1 he0 = prf comm-ex2-ex0
  tab-ok r1 he1 = refl≈
  tab-ok r1 he2 = prf (top (t₃ ∷ t₃ ∷ []) [] refl)
  tab-ok r2 hx0 = prf (derive
    (ex2 ∷ ex1 ∷ x0 ∷ []) (x0 ∷ ex2 ∷ ex1 ∷ [])
    (rw 1 (b2 t₃ a₃ a₃ t₃ refl) ∷ rw 0 comm-ex2-x0 ∷ []) refl)
  tab-ok r2 hx1 = prf (derive
    (ex2 ∷ ex1 ∷ x1 ∷ []) (x3 ∷ ex2 ∷ ex1 ∷ [])
    (rw 1 (b2 t₃ b₃ d₃ t₃ refl) ∷ rw 0 (t2 t₃ b₃ d₃ t₃ refl) ∷ []) refl)
  tab-ok r2 hx2 = prf (derive
    (ex2 ∷ ex1 ∷ x2 ∷ []) (x1 ∷ ex2 ∷ ex1 ∷ [])
    (rw 1 (b2 t₃ d₃ b₃ t₃ refl) ∷ rw 0 (t2 t₃ a₃ a₃ t₃ refl) ∷ []) refl)
  tab-ok r2 hx3 = prf (derive
    (ex2 ∷ ex1 ∷ x3 ∷ []) (x2 ∷ ex2 ∷ ex1 ∷ [])
    (rw 1 (t2 s₃ d₃ d₃ s₃ refl) ∷ rw 0 (t2 t₃ d₃ b₃ t₃ refl) ∷ []) refl)
  tab-ok r2 he0 = refl≈
  tab-ok r2 he1 = prf (derive
    (ex2 ∷ ex1 ∷ ex1 ∷ []) (ex2 ∷ [])
    (rw 1 (bot (t₃ ∷ t₃ ∷ []) [] refl) ∷ []) refl)
  tab-ok r2 he2 = prf (lift⁼ braid₃)
  tab-ok r3 hx0 = prf (derive
    (ex2 ∷ ex1 ∷ ex0 ∷ x0 ∷ []) (x3 ∷ ex2 ∷ ex1 ∷ ex0 ∷ [])
    ( rw 2 (b2 s₃ a₃ b₃ s₃ refl) ∷ rw 1 (b2 t₃ b₃ d₃ t₃ refl)
    ∷ rw 0 (t2 t₃ b₃ d₃ t₃ refl) ∷ []) refl)
  tab-ok r3 hx1 = prf (derive
    (ex2 ∷ ex1 ∷ ex0 ∷ x1 ∷ []) (x0 ∷ ex2 ∷ ex1 ∷ ex0 ∷ [])
    ( rw 2 (b2 s₃ b₃ a₃ s₃ refl) ∷ rw 1 (b2 t₃ a₃ a₃ t₃ refl)
    ∷ rw 0 comm-ex2-x0 ∷ []) refl)
  tab-ok r3 hx2 = prf (derive
    (ex2 ∷ ex1 ∷ ex0 ∷ x2 ∷ []) (x1 ∷ ex2 ∷ ex1 ∷ ex0 ∷ [])
    ( rw 2 (b2 s₃ d₃ d₃ s₃ refl) ∷ rw 1 (b2 t₃ d₃ b₃ t₃ refl)
    ∷ rw 0 (t2 t₃ a₃ a₃ t₃ refl) ∷ []) refl)
  tab-ok r3 hx3 = prf (derive
    (ex2 ∷ ex1 ∷ ex0 ∷ x3 ∷ []) (x2 ∷ ex2 ∷ ex1 ∷ ex0 ∷ [])
    ( rw 2 (sym⁼ comm-x3-ex0) ∷ rw 1 (t2 s₃ d₃ d₃ s₃ refl)
    ∷ rw 0 (t2 t₃ d₃ b₃ t₃ refl) ∷ []) refl)
  tab-ok r3 he0 = prf (derive
    (ex2 ∷ ex1 ∷ ex0 ∷ ex0 ∷ []) (ex2 ∷ ex1 ∷ [])
    (rw 2 (bot (s₃ ∷ s₃ ∷ []) [] refl) ∷ []) refl)
  tab-ok r3 he1 = prf (derive
    (ex2 ∷ ex1 ∷ ex0 ∷ ex1 ∷ []) (ex0 ∷ ex2 ∷ ex1 ∷ ex0 ∷ [])
    ( rw 1 (bot (t₃ ∷ s₃ ∷ t₃ ∷ []) (s₃ ∷ t₃ ∷ s₃ ∷ []) refl)
    ∷ rw 0 comm-ex2-ex0 ∷ []) refl)
  tab-ok r3 he2 = prf (derive
    (ex2 ∷ ex1 ∷ ex0 ∷ ex2 ∷ []) (ex1 ∷ ex2 ∷ ex1 ∷ ex0 ∷ [])
    ( rw 2 (sym⁼ comm-ex2-ex0) ∷ rw 0 (lift⁼ braid₃) ∷ []) refl)

------------------------------------------------------------------------
-- The normal form of a word in the NOT gates and swaps

record St : Set where
  constructor st
  field
    sq : List (Gen 3)
    se : Bool
    sr : Rep

open St

-- The word of a state.
W : St → Circuit 4
W s = ⟪ dn (sq s) ⟫ • (⟪ x3^ (se s) ⟫ • ⟪ rep (sr s) ⟫)

step : St → HL → St
step s y = st (sq s ++ ob (tab (sr s) y)) (se s xor oe (tab (sr s) y))
              (or (tab (sr s) y))

hnorm : St → List HL → St
hnorm s []      = s
hnorm s (y ∷ u) = hnorm (step s y) u

s₀ : St
s₀ = st [] false r0

hnorm₀ : List HL → St
hnorm₀ = hnorm s₀

private
  tabʷ : (r : Rep) (y : HL) →
         ⟪ rep r ⟫ • [ ⌜ y ⌝ ]ʷ ≈
         ⟪ dn (ob (tab r y)) ⟫ •
           (⟪ x3^ (oe (tab r y)) ⟫ • ⟪ rep (or (tab r y)) ⟫)
  tabʷ r y = begin
    ⟪ rep r ⟫ • [ ⌜ y ⌝ ]ʷ        ≈⟨ cong refl≈ (sym right-unit) ⟩
    ⟪ rep r ⟫ • ⟪ ⌜ y ⌝ ∷ [] ⟫    ≈⟨ sym (⟪++⟫ (rep r) (⌜ y ⌝ ∷ [])) ⟩
    ⟪ rep r ++ ⌜ y ⌝ ∷ [] ⟫       ≈⟨ tab-ok r y ⟩
    ⟪ dn b ++ (x3^ e ++ rep r′) ⟫  ≈⟨ ⟪++⟫ (dn b) (x3^ e ++ rep r′) ⟩
    ⟪ dn b ⟫ • ⟪ x3^ e ++ rep r′ ⟫ ≈⟨ cong refl≈ (⟪++⟫ (x3^ e) (rep r′)) ⟩
    ⟪ dn b ⟫ • (⟪ x3^ e ⟫ • ⟪ rep r′ ⟫) ∎
    where
    open SR word-setoid
    b  = ob (tab r y)
    e  = oe (tab r y)
    r′ = or (tab r y)

  step-ok : (s : St) (y : HL) → W s • [ ⌜ y ⌝ ]ʷ ≈ W (step s y)
  step-ok s y = begin
    (Q • (E • R)) • Y
      ≈⟨ by-passoc ((□ • (□ • □)) • □) (□ • (□ • (□ • □))) refl ⟩
    Q • (E • (R • Y))
      ≈⟨ cong refl≈ (cong refl≈ (tabʷ (sr s) y)) ⟩
    Q • (E • (B • (E′ • R′)))
      ≈⟨ by-passoc (□ • (□ • (□ • (□ • □))))
                   (□ • ((□ • □) • (□ • □))) refl ⟩
    Q • ((E • B) • (E′ • R′))
      ≈⟨ cong refl≈ (cong (E-word (se s) (ob o)) refl≈) ⟩
    Q • ((B • E) • (E′ • R′))
      ≈⟨ by-passoc (□ • ((□ • □) • (□ • □)))
                   ((□ • □) • ((□ • □) • □)) refl ⟩
    (Q • B) • ((E • E′) • R′)
      ≈⟨ cong (sym (dn++ (sq s) (ob o)))
              (cong (E-mul (se s) (oe o)) refl≈) ⟩
    W (step s y) ∎
    where
    open SR word-setoid
    o  = tab (sr s) y
    Q  = ⟪ dn (sq s) ⟫
    E  = ⟪ x3^ (se s) ⟫
    R  = ⟪ rep (sr s) ⟫
    Y  = [ ⌜ y ⌝ ]ʷ
    B  = ⟪ dn (ob o) ⟫
    E′ = ⟪ x3^ (oe o) ⟫
    R′ = ⟪ rep (or o) ⟫

  hnorm-ok : (s : St) (u : List HL) → W s • ⟪ ⌜ u ⌝ˡ ⟫ ≈ W (hnorm s u)
  hnorm-ok s []      = right-unit
  hnorm-ok s (y ∷ u) =
    trans (sym assoc)
          (trans (cong (step-ok s y) refl≈) (hnorm-ok (step s y) u))

  hnorm₀-ok : (u : List HL) → ⟪ ⌜ u ⌝ˡ ⟫ ≈ W (hnorm₀ u)
  hnorm₀-ok u =
    trans (sym left-unit)
          (trans (cong (sym (trans left-unit left-unit)) refl≈)
                 (hnorm-ok s₀ u))

------------------------------------------------------------------------
-- Comparing normal forms

private
  eqRep : Rep → Rep → Bool
  eqRep r0 r0 = true
  eqRep r1 r1 = true
  eqRep r2 r2 = true
  eqRep r3 r3 = true
  eqRep _  _  = false

  eqRep-sound : (r r′ : Rep) → eqRep r r′ ≡ true → r ≡ r′
  eqRep-sound r0 r0 _ = refl
  eqRep-sound r1 r1 _ = refl
  eqRep-sound r2 r2 _ = refl
  eqRep-sound r3 r3 _ = refl
  eqRep-sound r0 r1 ()
  eqRep-sound r0 r2 ()
  eqRep-sound r0 r3 ()
  eqRep-sound r1 r0 ()
  eqRep-sound r1 r2 ()
  eqRep-sound r1 r3 ()
  eqRep-sound r2 r0 ()
  eqRep-sound r2 r1 ()
  eqRep-sound r2 r3 ()
  eqRep-sound r3 r0 ()
  eqRep-sound r3 r1 ()
  eqRep-sound r3 r2 ()

  eqB : Bool → Bool → Bool
  eqB true  true  = true
  eqB false false = true
  eqB _     _     = false

  eqB-sound : (e e′ : Bool) → eqB e e′ ≡ true → e ≡ e′
  eqB-sound true  true  _ = refl
  eqB-sound false false _ = refl
  eqB-sound true  false ()
  eqB-sound false true  ()

  ∧₁ : (a b : Bool) → a ∧ b ≡ true → a ≡ true
  ∧₁ true  b h = refl
  ∧₁ false b ()

  ∧₂ : (a b : Bool) → a ∧ b ≡ true → b ≡ true
  ∧₂ true  b h = h
  ∧₂ false b ()

-- Two states with the same word, up to the function of the part on the
-- bottom wires.
okSt : St → St → Bool
okSt s s′ =
  eqRep (sr s) (sr s′) ∧ (eqB (se s) (se s′) ∧ same 3 ⟪ sq s ⟫ ⟪ sq s′ ⟫)

private
  W-cong′ : (q q′ : List (Gen 3)) (e e′ : Bool) (r r′ : Rep) →
            r ≡ r′ → e ≡ e′ → same 3 ⟪ q ⟫ ⟪ q′ ⟫ ≡ true →
            W (st q e r) ≈ W (st q′ e′ r′)
  W-cong′ q q′ e e′ r r′ refl refl h = cong (prf (bot q q′ h)) refl≈

  W-cong : (s s′ : St) → okSt s s′ ≡ true → W s ≈ W s′
  W-cong s s′ h =
    W-cong′ (sq s) (sq s′) (se s) (se s′) (sr s) (sr s′)
      (eqRep-sound _ _ (∧₁ c₁ (c₂ ∧ c₃) h))
      (eqB-sound _ _ (∧₁ c₂ c₃ (∧₂ c₁ (c₂ ∧ c₃) h)))
      (∧₂ c₂ c₃ (∧₂ c₁ (c₂ ∧ c₃) h))
    where
    c₁ = eqRep (sr s) (sr s′)
    c₂ = eqB (se s) (se s′)
    c₃ = same 3 ⟪ sq s ⟫ ⟪ sq s′ ⟫

-- Two words in the NOT gates and swaps with the same normal form.
hstep : (u v : List HL) → okSt (hnorm₀ u) (hnorm₀ v) ≡ true → Eqn 4
hstep u v h = eqn ⌜ u ⌝ˡ ⌜ v ⌝ˡ
  (trans (hnorm₀-ok u) (trans (W-cong _ _ h) (sym (hnorm₀-ok v))))

------------------------------------------------------------------------
-- Changing the frame

private
  isR0 : Rep → Bool
  isR0 r0 = true
  isR0 _  = false

  isR0-sound : (r : Rep) → isR0 r ≡ true → r ≡ r0
  isR0-sound r0 _ = refl
  isR0-sound r1 ()
  isR0-sound r2 ()
  isR0-sound r3 ()

-- From the frame p to the frame p′.
fwd : List HL → List HL → St
fwd p p′ = hnorm₀ (reverse p ++ p′)

frame-ok : (p p′ : List HL) (b b′ : List (Gen 3)) → Bool
frame-ok p p′ b b′ =
  okSt (hnorm₀ (p ++ reverse p)) s₀ ∧
  (isR0 (sr (fwd p p′)) ∧
  (isR0 (sr (fwd p′ p)) ∧
  (eqB (se (fwd p′ p)) (se (fwd p p′)) ∧
   same 3 ⟪ sq (fwd p p′) ++ (b′ ++ sq (fwd p′ p)) ⟫ ⟪ b ⟫)))

private
  -- The calculation, on words.
  module Conj
    {P P̄ P′ P̄′ Q Q̄ E B B′ : Circuit 4}
    (pp̄ : P • P̄ ≈ ε)
    (u  : P̄ • P′ ≈ Q • (E • ε))
    (ū  : P̄′ • P ≈ Q̄ • (E • ε))
    (EB′ : E • B′ ≈ B′ • E)
    (EQ̄  : E • Q̄ ≈ Q̄ • E)
    (EE  : E • E ≈ ε)
    (m   : Q • (B′ • Q̄) ≈ B)
    where

    open SR word-setoid

    inner : (Q • E) • (B′ • (Q̄ • E)) ≈ B
    inner = begin
      (Q • E) • (B′ • (Q̄ • E))
        ≈⟨ by-passoc ((□ • □) • (□ • (□ • □)))
                     (□ • ((□ • □) • (□ • □))) refl ⟩
      Q • ((E • B′) • (Q̄ • E))
        ≈⟨ cong refl≈ (cong EB′ refl≈) ⟩
      Q • ((B′ • E) • (Q̄ • E))
        ≈⟨ by-passoc (□ • ((□ • □) • (□ • □)))
                     (□ • (□ • ((□ • □) • □))) refl ⟩
      Q • (B′ • ((E • Q̄) • E))
        ≈⟨ cong refl≈ (cong refl≈ (cong EQ̄ refl≈)) ⟩
      Q • (B′ • ((Q̄ • E) • E))
        ≈⟨ by-passoc (□ • (□ • ((□ • □) • □)))
                     ((□ • (□ • □)) • (□ • □)) refl ⟩
      (Q • (B′ • Q̄)) • (E • E)
        ≈⟨ cong m EE ⟩
      B • ε
        ≈⟨ right-unit ⟩
      B ∎

    conj : P′ • (B′ • P̄′) ≈ P • (B • P̄)
    conj = begin
      P′ • (B′ • P̄′)
        ≈⟨ cong (sym left-unit) (cong refl≈ (sym right-unit)) ⟩
      (ε • P′) • (B′ • (P̄′ • ε))
        ≈⟨ cong (cong (sym pp̄) refl≈)
                (cong refl≈ (cong refl≈ (sym pp̄))) ⟩
      ((P • P̄) • P′) • (B′ • (P̄′ • (P • P̄)))
        ≈⟨ by-passoc (((□ • □) • □) • (□ • (□ • (□ • □))))
                     (□ • (((□ • □) • (□ • (□ • □))) • □)) refl ⟩
      P • (((P̄ • P′) • (B′ • (P̄′ • P))) • P̄)
        ≈⟨ cong refl≈ (cong (cong u (cong refl≈ ū)) refl≈) ⟩
      P • (((Q • (E • ε)) • (B′ • (Q̄ • (E • ε)))) • P̄)
        ≈⟨ cong refl≈ (cong (cong (cong refl≈ right-unit)
             (cong refl≈ (cong refl≈ right-unit))) refl≈) ⟩
      P • (((Q • E) • (B′ • (Q̄ • E))) • P̄)
        ≈⟨ cong refl≈ (cong inner refl≈) ⟩
      P • (B • P̄) ∎

  W-r0 : (q : List (Gen 3)) (e e′ : Bool) (r : Rep) → r ≡ r0 → e ≡ e′ →
         W (st q e r) ≈ ⟪ dn q ⟫ • (⟪ x3^ e′ ⟫ • ε)
  W-r0 q e e′ r refl refl = refl≈

  split : (p : List HL) (b : List (Gen 3)) →
          ⟪ ⌜ p ⌝ˡ ++ (dn b ++ ⌜ reverse p ⌝ˡ) ⟫ ≈
          ⟪ ⌜ p ⌝ˡ ⟫ • (⟪ dn b ⟫ • ⟪ ⌜ reverse p ⌝ˡ ⟫)
  split p b =
    trans (⟪++⟫ ⌜ p ⌝ˡ (dn b ++ ⌜ reverse p ⌝ˡ))
          (cong refl≈ (⟪++⟫ (dn b) ⌜ reverse p ⌝ˡ))

-- A circuit b on the bottom three wires in the frame p is the circuit
-- b′ in the frame p′.
frame : (p p′ : List HL) (b b′ : List (Gen 3)) →
        frame-ok p p′ b b′ ≡ true → Eqn 4
frame p p′ b b′ h =
  eqn (⌜ p ⌝ˡ ++ (dn b ++ ⌜ reverse p ⌝ˡ))
      (⌜ p′ ⌝ˡ ++ (dn b′ ++ ⌜ reverse p′ ⌝ˡ))
      (trans (split p b) (trans (sym conj) (sym (split p′ b′))))
  where
  s  = fwd p p′
  s′ = fwd p′ p
  c₁ = okSt (hnorm₀ (p ++ reverse p)) s₀
  c₂ = isR0 (sr s)
  c₃ = isR0 (sr s′)
  c₄ = eqB (se s′) (se s)
  c₅ = same 3 ⟪ sq s ++ (b′ ++ sq s′) ⟫ ⟪ b ⟫
  k₂ = ∧₂ c₁ (c₂ ∧ (c₃ ∧ (c₄ ∧ c₅))) h
  k₃ = ∧₂ c₂ (c₃ ∧ (c₄ ∧ c₅)) k₂
  k₄ = ∧₂ c₃ (c₄ ∧ c₅) k₃
  h₁ = ∧₁ c₁ (c₂ ∧ (c₃ ∧ (c₄ ∧ c₅))) h
  h₂ = ∧₁ c₂ (c₃ ∧ (c₄ ∧ c₅)) k₂
  h₃ = ∧₁ c₃ (c₄ ∧ c₅) k₃
  h₄ = ∧₁ c₄ c₅ k₄
  h₅ = ∧₂ c₄ c₅ k₄

  pp̄ : ⟪ ⌜ p ⌝ˡ ⟫ • ⟪ ⌜ reverse p ⌝ˡ ⟫ ≈ ε
  pp̄ = trans (sym (H++ p (reverse p)))
             (prf (hstep (p ++ reverse p) [] h₁))

  u : ⟪ ⌜ reverse p ⌝ˡ ⟫ • ⟪ ⌜ p′ ⌝ˡ ⟫ ≈
      ⟪ dn (sq s) ⟫ • (⟪ x3^ (se s) ⟫ • ε)
  u = trans (sym (H++ (reverse p) p′))
     (trans (hnorm₀-ok (reverse p ++ p′))
            (W-r0 (sq s) (se s) (se s) (sr s) (isR0-sound _ h₂) refl))

  ū : ⟪ ⌜ reverse p′ ⌝ˡ ⟫ • ⟪ ⌜ p ⌝ˡ ⟫ ≈
      ⟪ dn (sq s′) ⟫ • (⟪ x3^ (se s) ⟫ • ε)
  ū = trans (sym (H++ (reverse p′) p))
     (trans (hnorm₀-ok (reverse p′ ++ p))
            (W-r0 (sq s′) (se s′) (se s) (sr s′) (isR0-sound _ h₃)
                  (eqB-sound _ _ h₄)))

  m : ⟪ dn (sq s) ⟫ • (⟪ dn b′ ⟫ • ⟪ dn (sq s′) ⟫) ≈ ⟪ dn b ⟫
  m = trans (cong refl≈ (sym (dn++ b′ (sq s′))))
     (trans (sym (dn++ (sq s) (b′ ++ sq s′)))
            (prf (bot (sq s ++ (b′ ++ sq s′)) b h₅)))

  open Conj pp̄ u ū (E-word (se s) b′) (E-word (se s) (sq s′))
            (E-sq (se s)) m using (conj)
