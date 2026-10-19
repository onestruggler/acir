------------------------------------------------------------------------
-- Presentations of groups
--
-- The cosets of the top table are told apart by their matrices.
--
-- Each coset c of the top table is a coset of ThreeQubit's (`τ c`),
-- its representative being a nine-letter label times ThreeQubit's
-- representative, as matrices (`bridge`, one boolean).  Each of the
-- nine letters encodes to a two-level word equal, in the Table 1
-- presentation, to a signed one (`sgn-eq`), so a label followed by a
-- representative is a signed word followed by ThreeQubit's
-- representative, and ThreeQubit.Separation tells those apart
-- (`separate`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Separate where

open import Data.Bool.Base using (Bool ; true ; false ; T)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.List.Base using (List)
open import Data.Nat.Base using (_<ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_ ; RingD)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (⟦_⟧ᵐ ; actV ; set₁ ; set₂)
import Examples.Groups.CCX+HH-TwoLevel.MainLemma {8} as Main
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.Semantics as C
open import Examples.Groups.CCX+HH.Decide using (eqD ; eqMat ; by-eq)
import Examples.Groups.CCX+HH.ThreeQubit.Cosets as TQC
import Examples.Groups.CCX+HH.ThreeQubit.Separation as TQS
import Examples.Groups.CCX+HH.ThreeQubit.QuarticInvariant as Q
import Examples.Groups.CCX+HH.Natural.Soundness as NS

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Kit using (Circuit ; ⟪_⟫ ; _⊢_≈_)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Letters using (dec)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Columns using (F9)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.TopTable using (repT ; rep)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.TopCosets using (τT ; τinv ; λT)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Invariants using (ιD)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound ; eqF ; eqF-sound)
import Examples.Groups.CCX+HH.Natural.ThreeWire.Pure as Pu

private
  module Δ = PB (T._===_ {8})

  toT : ∀ {b} → b ≡ true → T b
  toT refl = tt

  lt : ∀ {a b : Fin 8} → T (toℕ a <ᵇ toℕ b) → toℕ a Data.Nat.Base.< toℕ b
  lt {a} {b} h = <ᵇ⇒< (toℕ a) (toℕ b) h
    where import Data.Nat.Base

  X : (a b : Fin 8) → T (toℕ a <ᵇ toℕ b) → Word (T.Gen 8)
  X a b h = T.X a b (lt {a} {b} h)

------------------------------------------------------------------------
-- The nine letters as signed two-level words

sgn : Fin 9 → Word (T.Gen 8)
sgn ₀ = X ₀ ₁ tt • X ₂ ₃ tt • X ₄ ₅ tt • X ₆ ₇ tt
sgn ₁ = X ₀ ₂ tt • X ₁ ₃ tt • X ₄ ₆ tt • X ₅ ₇ tt
sgn ₂ = X ₀ ₄ tt • X ₁ ₅ tt • X ₂ ₆ tt • X ₃ ₇ tt
sgn ₃ = X ₂ ₃ tt • X ₆ ₇ tt
sgn ₄ = X ₄ ₆ tt • X ₅ ₇ tt
sgn ₅ = X ₁ ₃ tt • X ₅ ₇ tt
sgn ₆ = X ₂ ₆ tt • X ₃ ₇ tt
sgn ₇ = X ₆ ₇ tt
sgn (Data.Fin.Base.suc ₇) = T.M ₂ • T.M ₃ • T.M ₆ • T.M ₇

private
  Xs : ∀ (a b : Fin 8) h → Q.Signed (X a b h)
  Xs a b h = Q.exchange a b (lt {a} {b} h)

sgn-signed : ∀ x → Q.Signed (sgn x)
sgn-signed ₀ = Q.product (Xs ₀ ₁ tt) (Q.product (Xs ₂ ₃ tt) (Q.product (Xs ₄ ₅ tt) (Xs ₆ ₇ tt)))
sgn-signed ₁ = Q.product (Xs ₀ ₂ tt) (Q.product (Xs ₁ ₃ tt) (Q.product (Xs ₄ ₆ tt) (Xs ₅ ₇ tt)))
sgn-signed ₂ = Q.product (Xs ₀ ₄ tt) (Q.product (Xs ₁ ₅ tt) (Q.product (Xs ₂ ₆ tt) (Xs ₃ ₇ tt)))
sgn-signed ₃ = Q.product (Xs ₂ ₃ tt) (Xs ₆ ₇ tt)
sgn-signed ₄ = Q.product (Xs ₄ ₆ tt) (Xs ₅ ₇ tt)
sgn-signed ₅ = Q.product (Xs ₁ ₃ tt) (Xs ₅ ₇ tt)
sgn-signed ₆ = Q.product (Xs ₂ ₆ tt) (Xs ₃ ₇ tt)
sgn-signed ₇ = Xs ₆ ₇ tt
sgn-signed (Data.Fin.Base.suc ₇) =
  Q.product (Q.minus ₂) (Q.product (Q.minus ₃) (Q.product (Q.minus ₆) (Q.minus ₇)))

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  private
    chkS : Fin 9 → Bool
    chkS x = eqMat eqD (C.interpret ⟪ dec (ιD x) ⟫) ⟦ sgn x ⟧ᵐ

    chkS-ok : allFin 9 chkS ≡ true
    chkS-ok = refl

  sgn-sem : ∀ x → C.interpret ⟪ dec (ιD x) ⟫ ≡ ⟦ sgn x ⟧ᵐ
  sgn-sem x = by-eq (toT (allFin-sound 9 chkS chkS-ok x))

sgn-eq : ∀ x → E.encode ⟪ dec (ιD x) ⟫ Δ.≈ sgn x
sgn-eq x = Main.completeness (Eq.trans (C.encoding-correct ⟪ dec (ιD x) ⟫) (sgn-sem x))

S : Word (Fin 9) → Word (T.Gen 8)
S = sgn ʷ

S-signed : ∀ l → Q.Signed (S l)
S-signed [ x ]ʷ  = sgn-signed x
S-signed ε       = Q.empty
S-signed (u • v) = Q.product (S-signed u) (S-signed v)

S-eq : ∀ l → E.encode (F9 l) Δ.≈ S l
S-eq [ x ]ʷ  = sgn-eq x
S-eq ε       = Δ.refl
S-eq (u • v) = Δ.cong (S-eq u) (S-eq v)

------------------------------------------------------------------------
-- The cosets

τ : Fin 135 → TQC.Coset
τ c = lookup τT c

lab : Fin 135 → Word (Fin 9)
lab c = Pu.word-of-list (lookup λT c)

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  private
    chkB : Fin 135 → Bool
    chkB c = eqMat eqD (C.interpret (rep c)) (C.interpret (F9 (lab c) • TQC.rep (τ c)))

    chkB-ok : allFin 135 chkB ≡ true
    chkB-ok = refl

  bridge : ∀ c → C.interpret (rep c) ≡ C.interpret (F9 (lab c) • TQC.rep (τ c))
  bridge c = by-eq (toT (allFin-sound 135 chkB chkB-ok c))

private
  τinv-τ-ok : allFin 135 (λ c → eqF (τinv (τ c)) c) ≡ true
  τinv-τ-ok = refl

  τinv-τ : ∀ c → τinv (τ c) ≡ c
  τinv-τ c = eqF-sound _ _ (allFin-sound 135 (λ c → eqF (τinv (τ c)) c) τinv-τ-ok c)


separate : ∀ c c′ (l m : Word (Fin 9)) →
           C.interpret (F9 l • rep c) ≡ C.interpret (F9 m • rep c′) → c ≡ c′
separate c c′ l m eq = Eq.trans (Eq.sym (τinv-τ c)) (Eq.trans (Eq.cong τinv same) (τinv-τ c′))
  where
  moved : ∀ k c → C.interpret (F9 k • rep c) ≡ C.interpret (F9 (k • lab c) • TQC.rep (τ c))
  moved k c = Eq.trans (Eq.cong (λ M → C.interpret (F9 k) Mat.·*· M) (bridge c))
    (NS.sound {w = F9 k • (F9 (lab c) • TQC.rep (τ c))} (PB.sym PB.assoc))
    where import Quantum.Synthesis.Matrix as Mat
  eq′ : C.interpret (F9 (l • lab c) • TQC.rep (τ c)) ≡ C.interpret (F9 (m • lab c′) • TQC.rep (τ c′))
  eq′ = Eq.trans (Eq.sym (moved l c)) (Eq.trans eq (moved m c′))
  enc : E.encode (F9 (l • lab c) • TQC.rep (τ c)) Δ.≈ E.encode (F9 (m • lab c′) • TQC.rep (τ c′))
  enc = Main.completeness {E.encode (F9 (l • lab c) • TQC.rep (τ c))} {E.encode (F9 (m • lab c′) • TQC.rep (τ c′))}
    (Eq.trans (C.encoding-correct (F9 (l • lab c) • TQC.rep (τ c)))
      (Eq.trans eq′ (Eq.sym (C.encoding-correct (F9 (m • lab c′) • TQC.rep (τ c′))))))
  signed : (S (l • lab c) • E.encode (TQC.rep (τ c))) Δ.≈ (S (m • lab c′) • E.encode (TQC.rep (τ c′)))
  signed = Δ.trans (Δ.cong (Δ.sym (S-eq (l • lab c))) Δ.refl)
    (Δ.trans enc (Δ.cong (S-eq (m • lab c′)) Δ.refl))
  same : τ c ≡ τ c′
  same = TQS.separate-signed (τ c) (τ c′) (S-signed (l • lab c)) (S-signed (m • lab c′)) signed
