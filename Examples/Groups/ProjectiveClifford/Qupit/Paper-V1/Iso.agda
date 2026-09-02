{-# OPTIONS --cubical-compatible --safe #-}
------------------------------------------------------------------------
-- Presentations of groups
--
-- The id-isomorphism  Paper-V1.Clifford-Relations ≅ Paper-V0.Clifford-Relations.
--
-- Both rule sets are relations over the SAME alphabet — Symplectic's
-- three gates H, S, CZ — so the candidate isomorphism is the identity on
-- words, exactly as in Simplified-V2.Iso, and the whole content is the
-- pair of well-definedness proofs:
--
--   f-well-defined : every Paper-V1 axiom holds in Paper-V0;
--   g-well-defined : every Paper-V0 axiom holds in Paper-V1.
--
-- Paper-V1 is Paper-V0 with the multiplier respelled — RHR x x⁻¹ becomes
-- SHS' x⁻¹ x — and with one axiom dropped.  So the twelve axioms that
-- neither mention the multiplier nor are order-SH are the same word on
-- both sides, and discharge by `axiom` straight across:
--
--     order-S  comm-HHSHHS  order-CZ  order-Ex  comm-CZ-S↑
--     semi-Ex-S↑  semi-Ex-H↑  blake-c12  yang-baxter  cz-slide
--     semi-CX↑-CZ↓          (and the structural rules, likewise)
--
-- Four mention the multiplier — order-H, M-power, semi-MR, semi-M↑CZ —
-- and each needs the bridge between the two spellings, at -1, at g and at
-- g ^ k.  That bridge is the real mathematics, and it is Shared.PauliBase
-- (instantiated below at Simplified-V1, whose theorems Paper-V0.Iso
-- transports).
--
-- One axiom is asymmetric: Paper-V0 has order-SH, Paper-V1 does not, so
-- g has a case for it that f has no counterpart to.  See the note there.
--
-- Everything is now a theorem, so `Theorem-PaperV1-iso-PaperV0` below is
-- unconditional.  (A `BridgeData` record used to carry whichever facts
-- were still open, the way Qubit.ExactExtension carries ExactData; it is
-- gone.)
--
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (id)
open import Data.Product using (_,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
open import Word.Base using (Word ; _•_ ; ε ; _^_ ; [_]ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open GroupMorphisms

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import Notations

import Relation.Binary.PropositionalEquality as Eq

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Iso
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- The Paper-V1 side is opened unqualified: it re-exports the shared
-- generator layer (Gen, and the derived words S, H, CZ, Ex, CX, CZ02, …),
-- which both rule sets are written over.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as PapV0
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as V1
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas
  p-3 p-prime g* g-gen as V1L
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas
  p-3 p-prime g* g-gen as PapL

-- Paper-V0 is already proved isomorphic to Simplified-V1, and that
-- isomorphism transports Simplified-V1 theorems into Paper-V0's theory.
-- Simplified-V1 has the full Pauli calculus, so Paper-V0 does not need
-- its own copy: anything provable there arrives here for free.
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Iso
  p-3 p-prime g* g-gen as PapV0Iso
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.LemmasXZ
  p-3 p-prime g* g-gen as SimXZ
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Lemmas
  p-3 p-prime g* g-gen as SimL
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics
  p-3 p-prime g* g-gen as SimS
import Examples.Groups.ProjectiveClifford.Qupit.Shared.PauliBase
  p-3 p-prime g* g-gen as Shared

-- The shared bridge, instantiated at Simplified-V1: it has every fact
-- the calculus needs, X • Z ≈ Z • X included.
module SimBridge (n : ℕ) =
  Shared.BridgeCalc n (SimS.Clifford-Relations._QRel,_===_ (₁₊ n))
    (SimL.Lemmas1.lemma-order-X n)
    (SimL.Lemmas1.lemma-order-Z n)
    (SimL.Lemmas1.lemma-comm-Z-S n)
    (SimXZ.Lemmas1b.lemma-comm-X-Z n)
    (SimXZ.Lemmas1b.conj-H-X^k n)
    (SimXZ.Lemmas1b.conj-X^k-H n)
    (SimXZ.Lemmas1b.lemma-XS n)
    (SimXZ.Lemmas1b.aux-pow-mod n)
    SimS.Lemmas-Clifford.lemma-Induction
    SimS.Lemmas-Clifford.lemma-Inductionˡ

module PapR = Clifford-Relations
module PapV0R  = PapV0.Clifford-Relations

-- Sanity check that the transport really lands where it should: X and Z
-- commute in Paper-V0's theory, borrowed from Simplified-V1.
v0-comm-X-Z : ∀ n → let open PB (PapV0R._QRel,_===_ (₁₊ n)) in
              PapV0R.X • PapV0R.Z ≈ PapV0R.Z • PapV0R.X
v0-comm-X-Z n = PapV0Iso.Theorem.v1⇒pap (₁₊ n) (SimXZ.Lemmas1b.lemma-comm-X-Z n)

-- The bridge, in Paper-V0's theory: proved in Simplified-V1 (which has
-- the calculus) and carried across by the same transport.  XM x is
-- M (x ⁻¹) on both sides, so this is the bridge at x ⁻¹ with the middle
-- exponent identified by inv-involutive.
v0-XM-bridge : ∀ n (x : ℤ* ₚ) →
               let open PB (PapV0R._QRel,_===_ (₁₊ n)) using (_≈_) in
               PapV0R.XM x ≈ PapR.XM x
v0-XM-bridge n x = PapV0Iso.Theorem.v1⇒pap (₁₊ n) sim
  where
  open PB (SimS.Clifford-Relations._QRel,_===_ (₁₊ n))

  b : ℤ ₚ
  b = (x ⁻¹) .proj₁

  eq₁ : PapV0R.XM x
        ≡ Shared.R^ b • (H • (Shared.R^ (((x ⁻¹) ⁻¹) .proj₁)
          • (H • (Shared.R^ b • H))))
  eq₁ = Eq.cong (λ z → Shared.R^ b • (H • (Shared.R^ z
          • (H • (Shared.R^ b • H)))))
          (Eq.sym (inv-involutive x))

  eq₂ : Shared.Z^ ((b + - ₁) * Shared.1/2)
        • (Shared.X^ ((₁ + - (((x ⁻¹) ⁻¹) .proj₁)) * Shared.1/2)
        • (Shared.S^' b • (H • (Shared.S^' (((x ⁻¹) ⁻¹) .proj₁)
        • (H • (Shared.S^' b • H))))))
        ≡ PapR.XM x
  eq₂ = Eq.cong (λ z → Shared.Z^ ((b + - ₁) * Shared.1/2)
          • (Shared.X^ ((₁ + - z) * Shared.1/2)
          • (Shared.S^' b • (H • (Shared.S^' z
          • (H • (Shared.S^' b • H)))))))
          (inv-involutive x)

  sim : PapV0R.XM x ≈ PapR.XM x
  sim = trans (refl' eq₁)
          (trans (SimBridge.Bridge.bridge n (x ⁻¹)) (refl' eq₂))

-- The same for M, where no rewriting is needed at all: Paper-V0's M x is
-- the shared bridge's left-hand side and Paper-V1's is its right-hand
-- side, on the nose.
v0-M-bridge : ∀ n (x : ℤ* ₚ) →
              let open PB (PapV0R._QRel,_===_ (₁₊ n)) using (_≈_) in
              PapV0R.M x ≈ PapR.M x
v0-M-bridge n x = PapV0Iso.Theorem.v1⇒pap (₁₊ n) (SimBridge.Bridge.bridge n x)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Where the two halves are proved
--
-- Nothing is outstanding; a `BridgeData` record of obligations used to
-- stand here, and the last of its fields is gone.  For the record, where
-- each half now lives:
--
--   * Paper-V0's axioms, as Paper-V1 theorems — Paper-V1.Lemmas.
--     semi-M↓CZ and comm-CZ-S↓ are the ↑-rules conjugated by the swap.
--     c10 sheds a leading H ↑ off each side (the left by lemma-CZ-H↑,
--     the right by the Euler decomposition of the multiplier by −1) and
--     is then blake-c12's commutator with R for S, the two reconciled by
--     the Pauli-versus-XC rule lemma-conj-XC-Z↑ since R = S • Z ^ ½.
--     c11 is c10 conjugated by the swap.  c12 is the progress report's
--     Lemma 9.  Both sides of c13 are CZ02.  c14 telescopes, because
--     conjugation by ⊤⊥ ↑ sends CZ to CZ02 and CZ02 to the inverse of
--     CZ • CZ02, and ⊤⊥ ↑ has order 3.  c15 is c14 transported along the
--     transposition of wires 0 and 2.
--
--   * Paper-V1's axioms, as Paper-V0 theorems —
--     Paper-V0.ExRules.  The five with no S in them are transported
--     from the symplectic tree along Paper-V0.Forward's f, which
--     sends the symplectic S to R = S • Z ^ ½ and fixes everything else.
--     The two that do mention S come back from that transport in the
--     R-spelling, and the difference is a Pauli: for semi-Ex-S↑ a single
--     Z ^ ½, moved across the swap and cancelled; for blake-c12 four of
--     them, one of which crosses the CX and is doubled onto the other
--     wire, after which each wire's exponent is h • p.

------------------------------------------------------------------------
-- The isomorphism

module Theorem where

  -- Paper-V1 is a copy of Paper-V0 with M and XM respelled, so the two
  -- axiom sets have the *same constructors*, and every axiom whose
  -- statement does not mention the multiplier is the same word on both
  -- sides — those discharge by `axiom` straight across.  The structural
  -- layer is shared outright (the same Lift-Relation over the same
  -- gates), so comm₁ / comm₂ / cong↑ map constructor to constructor.
  --
  -- That leaves exactly four, the ones stated over M₋₁ or XMg:
  --
  --     order-H   M-power   semi-MR   semi-M↑CZ
  --
  -- Each needs the bridge between the two spellings — that the R-word
  -- RHR x x⁻¹ and the S-word SHS' x⁻¹ x are equal — at -1, at g, and at
  -- g ^ k respectively.  See the note below on where that stands.

  -- f : Paper-V1 → Paper-V0.
  f-well-defined : ∀ {n} → let open PB (PapV0R._QRel,_===_ n) renaming (_≈_ to _≈₂_) in
    ∀ {w v} -> PapR._QRel,_===_ n w v -> id w ≈₂ id v
  f-well-defined PapR.order-S        = PB.axiom PapV0R.order-S
  f-well-defined PapR.comm-HHSHHS    = PB.axiom PapV0R.comm-HHSHHS
  f-well-defined PapR.order-CZ       = PB.axiom PapV0R.order-CZ
  f-well-defined PapR.order-Ex       = PB.axiom PapV0R.order-Ex
  f-well-defined PapR.comm-CZ-S↑     = PB.axiom PapV0R.comm-CZ-S↑
  f-well-defined PapR.semi-Ex-S↑     = PB.axiom PapV0R.semi-Ex-S↑
  f-well-defined PapR.semi-Ex-H↑     = PB.axiom PapV0R.semi-Ex-H↑
  f-well-defined PapR.blake-c12      = PB.axiom PapV0R.blake-c12
  f-well-defined PapR.yang-baxter    = PB.axiom PapV0R.yang-baxter
  f-well-defined PapR.cz-slide       = PB.axiom PapV0R.cz-slide
  f-well-defined PapR.semi-CX↑-CZ↓   = PB.axiom PapV0R.semi-CX↑-CZ↓
  -- The four stated over the multiplier.  Each is Paper-V0's own axiom
  -- with XMg rewritten across the bridge; M₋₁ needs no XM detour, since
  -- both sides spell it as M at -1.
  f-well-defined {₁₊ n} PapR.order-H =
    trans (axiom PapV0R.order-H) (v0-M-bridge n -'₁)
    where open PB (PapV0R._QRel,_===_ (₁₊ n))

  f-well-defined {₁₊ n} (PapR.M-power k) =
    trans (^-cong _ _ (toℕ k) (sym bridge-g))
      (trans (axiom (PapV0R.M-power k)) (v0-XM-bridge n (g^ k)))
    where
    open PB (PapV0R._QRel,_===_ (₁₊ n))
    open PP (PapV0R._QRel,_===_ (₁₊ n)) using (^-cong)
    bridge-g = v0-XM-bridge n g′

  f-well-defined {₁₊ n} PapR.semi-MR =
    trans (cleft (sym bridge-g))
      (trans (axiom PapV0R.semi-MR) (cright bridge-g))
    where
    open PB (PapV0R._QRel,_===_ (₁₊ n))
    bridge-g = v0-XM-bridge n g′

  f-well-defined {₂₊ n} PapR.semi-M↑CZ =
    trans (cleft (sym bridge-g↑))
      (trans (axiom PapV0R.semi-M↑CZ) (cright bridge-g↑))
    where
    open PB (PapV0R._QRel,_===_ (₂₊ n))
    bridge-g↑ = PapV0R.lemma-cong↑ _ _ (v0-XM-bridge n g′)
  -- Structural rules: the same layer on both sides.
  f-well-defined (PapR.comm₁ gt w)   = PB.axiom (PapV0R.comm₁ gt w)
  f-well-defined (PapR.comm₂ gt w)   = PB.axiom (PapV0R.comm₂ gt w)
  f-well-defined (PapR.cong↑ eq)     = PapV0R.lemma-cong↑ _ _ (f-well-defined eq)

  -- g : Paper-V0 → Paper-V1.
  g-well-defined : ∀ {n} → let open PB (PapR._QRel,_===_ n) renaming (_≈_ to _≈₁_) in
    ∀ {u t} -> PapV0R._QRel,_===_ n u t -> id u ≈₁ id t
  g-well-defined PapV0R.order-S      = PB.axiom PapR.order-S
  g-well-defined PapV0R.comm-HHSHHS  = PB.axiom PapR.comm-HHSHHS
  g-well-defined PapV0R.order-CZ     = PB.axiom PapR.order-CZ
  g-well-defined PapV0R.order-Ex     = PB.axiom PapR.order-Ex
  g-well-defined PapV0R.comm-CZ-S↑   = PB.axiom PapR.comm-CZ-S↑
  g-well-defined PapV0R.semi-Ex-S↑   = PB.axiom PapR.semi-Ex-S↑
  g-well-defined PapV0R.semi-Ex-H↑   = PB.axiom PapR.semi-Ex-H↑
  g-well-defined PapV0R.blake-c12    = PB.axiom PapR.blake-c12
  g-well-defined PapV0R.yang-baxter  = PB.axiom PapR.yang-baxter
  g-well-defined PapV0R.cz-slide     = PB.axiom PapR.cz-slide
  g-well-defined PapV0R.semi-CX↑-CZ↓ = PB.axiom PapR.semi-CX↑-CZ↓
  -- The axiom sets are no longer quite the same: Paper-V0 has order-SH
  -- and Paper-V1 does not, so this direction has to prove it rather than
  -- quote it.  One-Wire.lemma-order-SH does, from M-power at k = 0 —
  -- under the SHS' spelling M₁ is the word (S • H) ^ 3 outright.  This is
  -- the only case with no counterpart on the f side.
  g-well-defined {₁₊ n} PapV0R.order-SH = PapL.One-Wire.lemma-order-SH n
  -- The four stated over the multiplier.
  --
  -- order-H is exactly lemma-M₋₁-R: Paper-V0's M₋₁ *is* the R-word
  -- RHR(-1)(-1), once both exponents are identified with p-1 (the first
  -- by lemma-toℕ-1ₚ, the second because -1 is its own inverse), and
  -- lemma-M₋₁-R says that word is H ^ 2 in Paper-V1's theory.
  g-well-defined {n} PapV0R.order-H =
    PB.trans (PB.sym (PapL.One-Wire-Group.lemma-M₋₁-R _)) (PB.refl' _ eqn)
    where
    eqn : PapR.R ^ p-1 • (H • (PapR.R ^ p-1 • (H • (PapR.R ^ p-1 • H))))
          ≡ PapV0R.M₋₁
    eqn = Eq.sym
      (Eq.cong₂ (λ a b → PapR.R ^ a • (H • (PapR.R ^ b • (H • (PapR.R ^ a • H)))))
         lemma-toℕ-1ₚ
         (Eq.trans (Eq.cong toℕ aux-₁⁻¹) lemma-toℕ-1ₚ))
  -- The other three are the bridge at g and at g ^ k: Paper-V0's XM is
  -- the R-word, Paper-V1's is the S-word, and XM-bridge says they agree.
  -- Once XMg is rewritten across, each rule is Paper-V1's own axiom.
  g-well-defined {₁₊ n} (PapV0R.M-power k) =
    trans (^-cong _ _ (toℕ k) bridge-g)
      (trans (axiom (PapR.M-power k))
        (sym (PapL.One-Wire-Group.XM-bridge n (g^ k))))
    where
    open PB (PapR._QRel,_===_ (₁₊ n))
    open PP (PapR._QRel,_===_ (₁₊ n)) using (^-cong)
    bridge-g = PapL.One-Wire-Group.XM-bridge n g′

  g-well-defined {₁₊ n} PapV0R.semi-MR =
    trans (cleft bridge-g) (trans (axiom PapR.semi-MR) (cright (sym bridge-g)))
    where
    open PB (PapR._QRel,_===_ (₁₊ n))
    bridge-g = PapL.One-Wire-Group.XM-bridge n g′

  g-well-defined {₂₊ n} PapV0R.semi-M↑CZ =
    trans (cleft bridge-g↑)
      (trans (axiom PapR.semi-M↑CZ) (cright (sym bridge-g↑)))
    where
    open PB (PapR._QRel,_===_ (₂₊ n))
    bridge-g↑ = PapR.lemma-cong↑ _ _ (PapL.One-Wire-Group.XM-bridge n g′)
  -- Structural rules.
  g-well-defined (PapV0R.comm₁ gt w) = PB.axiom (PapR.comm₁ gt w)
  g-well-defined (PapV0R.comm₂ gt w) = PB.axiom (PapR.comm₂ gt w)
  g-well-defined (PapV0R.cong↑ eq)   = PapR.lemma-cong↑ _ _ (g-well-defined eq)

  ------------------------------------------------------------------------
  -- Group-likeness of the Paper-V1 rules
  --
  -- Transported rather than reproved: g-well-defined lifts to the whole
  -- congruence (Star-Congruence.lemma-id*-cong), so every Paper-V0
  -- theorem is a Paper-V1 theorem, and in particular each generator keeps
  -- the left inverse Paper-V0 gives it.

  module _ (n : ℕ) where

    open import Presentation.MorphismId
      (PapV0R._QRel,_===_ n) (PapR._QRel,_===_ n) using (module Star-Congruence)

    v1⇒pap : ∀ {w v} → let open PB (PapV0R._QRel,_===_ n) using (_≈_) in
             w ≈ v → let open PB (PapR._QRel,_===_ n) renaming (_≈_ to _≈'_) in w ≈' v
    v1⇒pap = Star-Congruence.lemma-id*-cong g-well-defined

  pap-grouplike : Grouplike (PapR._QRel,_===_ n)
  pap-grouplike {n} x with PapV0Iso.Theorem.pap-grouplike {n} x
  ... | w , inv = w , v1⇒pap n inv


  ------------------------------------------------------------------------
  -- The theorem

  module M (n : ℕ) where
    module G1 = Group-Lemmas (PapR._QRel,_===_ n) (pap-grouplike {n})
    module G2 = Group-Lemmas (PapV0R._QRel,_===_ n) (PapV0Iso.Theorem.pap-grouplike {n})

    open import Presentation.MorphismId (PapR._QRel,_===_ n) (PapV0R._QRel,_===_ n)
    open GroupMorphs (pap-grouplike {n}) (PapV0Iso.Theorem.pap-grouplike {n})

    Theorem-PaperV1-iso-PaperV0 :
      IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) id
    Theorem-PaperV1-iso-PaperV0 =
      StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
