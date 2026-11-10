------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of the two translations between Lafont's cycles on
-- sixteen points and the gates on four wires
--
-- A circuit on four wires denotes a function on the sixteen states
-- (Semantics), a word in Lafont's cycles an even permutation of the
-- sixteen positions (Examples.Groups.Alternating), and the Gray code
-- numbers the states by the positions (Numbering).  Along that
-- numbering each translation keeps the meaning of what it translates:
--
-- * f-sem: the word of a circuit permutes the positions as the circuit
--   maps the states;
--
-- * g-sem: the circuit of a word in the cycles maps the states as the
--   word permutes the positions.
--
-- Both are proved on the generators by evaluation at the sixteen
-- positions, the words being closed (f-sem-gen for the twelve gates,
-- g-sem-gen for the fourteen cycles), and then by induction on the
-- word.  Everything is stated position by position: two even
-- permutations are never compared as such.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Bridge where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong)

open import Word.Base using ([_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.Alternating.Interpretation
  using () renaming (⟦_⟧ to L⟦_⟧)
open import Examples.Groups.Alternating.Semantics using (perm)
import Examples.Groups.Alternating.Syntactics as L

open import Examples.Groups.Alt16-RevCir.Numbering
  using (enc ; dec ; dec-enc ; enc-dec ; fin16)
open import Examples.Groups.Alt16-RevCir.Semantics using (⟦_⟧ᵍ ; ⟦_⟧)
open import Examples.Groups.Alt16-RevCir.Syntactics
open import Examples.Groups.Alt16-RevCir.Translation using (f ; g)

private
  -- A generator of Lafont's four points further up.
  pattern 4↥ y = y L.↥ L.↥ L.↥ L.↥

------------------------------------------------------------------------
-- A gate as a word in the cycles

-- The word of a gate carries the position of a state to the position
-- of the state the gate sends it to.
f-sem-gen : (x : Gen 4) (i : Fin 16) →
            perm L⟦ f x ⟧ ⟨$⟩ʳ i ≡ dec (⟦ x ⟧ᵍ (enc i))
f-sem-gen X-gen = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen CX-gen = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen Ex-gen = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen CCX-gen = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen (X-gen ↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen (CX-gen ↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen (Ex-gen ↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen (CCX-gen ↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen (X-gen ↥ ↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen (CX-gen ↥ ↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen (Ex-gen ↥ ↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen (X-gen ↥ ↥ ↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
f-sem-gen (gate₀ ())
f-sem-gen (gate₀ () ↥)
f-sem-gen (gate₀ () ↥ ↥)
f-sem-gen (gate₀ () ↥ ↥ ↥)
f-sem-gen (gate₀ () ↥ ↥ ↥ ↥)

-- The same for a circuit, letter by letter: the position reached after
-- w is that of the state reached after w.
f-sem : (w : Circuit 4) (i : Fin 16) →
        perm L⟦ (f ʷ) w ⟧ ⟨$⟩ʳ i ≡ dec (⟦ w ⟧ (enc i))
f-sem [ x ]ʷ  i = f-sem-gen x i
f-sem ε       i = sym (dec-enc i)
f-sem (w • v) i =
  trans (f-sem v _)
        (cong (dec ∘ ⟦ v ⟧) (trans (cong enc (f-sem w i)) (enc-dec _)))

------------------------------------------------------------------------
-- A cycle as a circuit

-- The circuit Ω d of the cycle ω d points up sends the state at a
-- position to the state at the position the cycle sends it to.  There
-- are fourteen cycles; a fifteenth would be a generator on two points.
g-sem-gen : (y : L.Gen 16) (i : Fin 16) →
            dec (⟦ g y ⟧ (enc i)) ≡ perm L⟦ [ y ]ʷ ⟧ ⟨$⟩ʳ i
g-sem-gen L.ω-gen = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (L.ω-gen L.↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (L.ω-gen L.↥ L.↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (L.ω-gen L.↥ L.↥ L.↥) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ L.ω-gen) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (L.ω-gen L.↥)) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (L.ω-gen L.↥ L.↥)) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (L.ω-gen L.↥ L.↥ L.↥)) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (4↥ L.ω-gen)) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (4↥ (L.ω-gen L.↥))) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (4↥ (L.ω-gen L.↥ L.↥))) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (4↥ (L.ω-gen L.↥ L.↥ L.↥))) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (4↥ (4↥ L.ω-gen))) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (4↥ (4↥ (L.ω-gen L.↥)))) = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl
g-sem-gen (4↥ (4↥ (4↥ (y L.↥ L.↥)))) = ⊥-elim (L.no-gen₂ y)

-- The same for a word in the cycles, letter by letter.
g-sem : (u : L.Circuit 16) (i : Fin 16) →
        dec (⟦ (g ʷ) u ⟧ (enc i)) ≡ perm L⟦ u ⟧ ⟨$⟩ʳ i
g-sem [ y ]ʷ  i = g-sem-gen y i
g-sem ε       i = dec-enc i
g-sem (u • t) i =
  trans (cong (dec ∘ ⟦ (g ʷ) t ⟧)
              (trans (sym (enc-dec _)) (cong enc (g-sem u i))))
        (g-sem t _)
