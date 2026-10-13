------------------------------------------------------------------------
-- Presentations of groups
--
-- Hadamard parity is invariant under the scaled source relations and
-- under physical circuit equality.  Expanding an HH circuit has even
-- parity.  This distinguishes the two dyadic cosets without adding any
-- semantic equation to the circuit presentation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.HadamardParity where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _*_ ; _<_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
open import Data.Empty using (⊥)
import Data.Bool.Properties as BP
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as M
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Normal as Normal
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.GeneralN.StructuralEncoding as E
import Examples.Groups.CCX+H.GeneralN.Semantics as S
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as P
import Examples.Groups.CCX+H.GeneralN.HadamardEmbedding as Embed
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+HH.StructuralEncoding as DE

source-parity : ∀ {N} → Word (T.Genᴸ N) → Bool
source-parity [ T.⌊ g ⌋ ]ʷ = false
source-parity [ T.IH ]ʷ = true
source-parity ε = false
source-parity (u • v) = source-parity u xor source-parity v

dyadic-parity : ∀ {N} (w : Word (U.Gen N)) → source-parity T.⌊ w ⌋ʷ ≡ false
dyadic-parity [ g ]ʷ = refl
dyadic-parity ε = refl
dyadic-parity (u • v) = cong₂ _xor_ (dyadic-parity u) (dyadic-parity v)

private
  source-axiom : ∀ {N} {u v : Word (T.Genᴸ N)} → u T.===ᴸ v →
    source-parity u ≡ source-parity v
  source-axiom (T.table1 {u} {v} ax) = trans (dyadic-parity u) (sym (dyadic-parity v))
  source-axiom T.r7a = refl
  source-axiom (T.r7b _ _ _ _ _ _ _) = refl
  source-axiom (T.r7c _ _ _) = refl
  source-axiom (T.r7d₀ _ _ _) = refl
  source-axiom (T.r7d₁ _ _ _ _ _ _ _) = refl

source-sound : ∀ {N} {u v : Word (T.Genᴸ N)} → PB._≈_ T._===ᴸ_ u v →
  source-parity u ≡ source-parity v
source-sound PB.refl = refl
source-sound (PB.sym eq) = sym (source-sound eq)
source-sound (PB.trans eq eq′) = trans (source-sound eq) (source-sound eq′)
source-sound (PB.cong eq eq′) = cong₂ _xor_ (source-sound eq) (source-sound eq′)
source-sound (PB.assoc {x} {y} {z}) = BP.xor-assoc (source-parity x) (source-parity y) (source-parity z)
source-sound PB.left-unit = refl
source-sound (PB.right-unit {x}) = BP.xor-identityʳ (source-parity x)
source-sound (PB.axiom ax) = source-axiom ax

source-semantic : ∀ k → 0 < k → {u v : Word (T.Genᴸ (k * 2))} →
  M.Dim.⟦_⟧ᴸ k u ≡ M.Dim.⟦_⟧ᴸ k v → source-parity u ≡ source-parity v
source-semantic zero ()
source-semantic (suc k) positive {u} {v} eq = source-sound
  (Complete.completeness k {u = u} {v = v} eq)

normal-parity : ∀ k (w : Word (U.Gen (suc k * 2))) b →
  source-parity (T.⌊ w ⌋ʷ • Normal.Hᵇ k b) ≡ b
normal-parity k w false = cong (_xor false) (dyadic-parity w)
normal-parity k w true = cong (_xor true) (dyadic-parity w)

-- This is the parity of the number of actual H gates; classical gates
-- contribute zero, regardless of their indexed placement.
gate-parity : ∀ {n} → H.Gen n → Bool
gate-parity g with E.classify g
... | inj₁ dg = false
... | inj₂ p = true

parity : ∀ {n} → H.Circuit n → Bool
parity [ g ]ʷ = gate-parity g
parity ε = false
parity (u • v) = parity u xor parity v

private
  encoded-gate : ∀ {n} (g : H.Gen n) → source-parity (E.e g) ≡ gate-parity g
  encoded-gate g with E.classify g
  ... | inj₁ dg = dyadic-parity (DE.e dg)
  ... | inj₂ p = cong (_xor true) (dyadic-parity (DE.encode (E.prefix p)))

encoded : ∀ {n} (w : H.Circuit n) → source-parity (E.encode w) ≡ parity w
encoded [ g ]ʷ = encoded-gate g
encoded ε = refl
encoded (u • v) = cong₂ _xor_ (encoded u) (encoded v)

cast-parity : ∀ {m n} (p : m ≡ n) (w : Word (T.Genᴸ m)) →
  source-parity (S.cast-word p w) ≡ source-parity w
cast-parity refl w = refl

compiled : ∀ n (w : H.Circuit (suc n)) → source-parity (S.At.compile n w) ≡ parity w
compiled n w = trans (cong source-parity (S.At.compile-cast n w))
  (trans (cast-parity (NP.*-comm 2 (2 ^ℕ n)) (E.encode w)) (encoded w))

private
  empty-parity : ∀ (w : H.Circuit 0) → parity w ≡ false
  empty-parity [ H.gate₀ () ]ʷ
  empty-parity ε = refl
  empty-parity (u • v) = cong₂ _xor_ (empty-parity u) (empty-parity v)

physical-sound : ∀ {n} {u v : H.Circuit n} → P.interpret u ≡ P.interpret v → parity u ≡ parity v
physical-sound {zero} {u} {v} eq = trans (empty-parity u) (sym (empty-parity v))
physical-sound {suc n} {u} {v} eq = trans (sym (compiled n u))
  (trans (source-semantic (2 ^ℕ n) (NP.m^n>0 2 n)
    {u = S.At.compile n u} {v = S.At.compile n v}
    (trans (S.At.encoding-correct n u)
      (trans (P.At.backward n {u = u} {v = v} eq) (sym (S.At.encoding-correct n v)))))
    (compiled n v))

gate-shift : ∀ {n} (g : H.Gen n) → gate-parity (g H.↥) ≡ gate-parity g
gate-shift g with E.classify g
... | inj₁ dg = refl
... | inj₂ p = refl

shift : ∀ {n} (w : H.Circuit n) → parity (w H.↑) ≡ parity w
shift [ g ]ʷ = gate-shift g
shift ε = refl
shift (u • v) = cong₂ _xor_ (shift u) (shift v)

private
  expanded-gate : ∀ {n} (g : HH.Gen n) → parity (Embed.e g) ≡ false
  expanded-gate (HH.gate₀ ())
  expanded-gate (HH.gate₁ HH.X-gate) = refl
  expanded-gate (HH.gate₂ HH.CX-gate) = refl
  expanded-gate (HH.gate₂ HH.HH-gate) = refl
  expanded-gate (HH.gate₃ HH.CCX-gate) = refl
  expanded-gate (g HH.↥) = trans (shift (Embed.e g)) (expanded-gate g)

expanded : ∀ {n} (w : HH.Circuit n) → parity (Embed.embed w) ≡ false
expanded [ g ]ʷ = expanded-gate g
expanded ε = refl
expanded (u • v) = cong₂ _xor_ (expanded u) (expanded v)

-- A concrete representative of the parity bit on any positive width.
tail : ∀ {n} → Bool → H.Circuit (suc n)
tail false = ε
tail true = H.H

tail-parity : ∀ {n} b → parity (tail {n} b) ≡ b
tail-parity false = refl
tail-parity true = refl

factor-parity : ∀ {n} (w : HH.Circuit (suc n)) b →
  parity (Embed.embed w • tail b) ≡ b
factor-parity w b = trans (cong₂ _xor_ (expanded w) (tail-parity b)) refl

factor-bit-unique : ∀ {n} (u v : HH.Circuit (suc n)) b c →
  P.interpret (Embed.embed u • tail b) ≡ P.interpret (Embed.embed v • tail c) → b ≡ c
factor-bit-unique u v b c eq = trans (sym (factor-parity u b))
  (trans (physical-sound {u = Embed.embed u • tail b} {v = Embed.embed v • tail c} eq)
    (factor-parity v c))

separate : ∀ {n} (u v : HH.Circuit (suc n)) →
  P.interpret (Embed.embed u) ≡ P.interpret (Embed.embed v • H.H) → ⊥
separate u v eq = impossible (trans (sym (expanded u))
  (trans (physical-sound {u = Embed.embed u} {v = Embed.embed v • H.H} eq)
    (factor-parity v true)))
  where
  impossible : false ≡ true → ⊥
  impossible ()
