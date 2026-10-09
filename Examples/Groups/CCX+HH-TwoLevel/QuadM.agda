------------------------------------------------------------------------
-- Presentations of groups
--
-- The edge (-1)_[0] at a level with a positive exponent (Lemma A.20,
-- Subcase 2.2).
--
-- (-1)_[0] keeps the parities of the pivot column, so the same four
-- entries a < b < c < d are odd after it.  If entry 0 is one of them,
-- it is a, its class modulo 4 changes, and so does the sign t of the
-- syllable: the normal syllable of (-1)_[0]·s undoes (-1)_[0]
-- (Subcase 2.2.1).  Otherwise (-1)_[0] commutes with the syllable
-- (Subcase 2.2.2).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; level)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (lde)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadM {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s)) where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; Minimal)
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ ; τ-neg)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction using (Mᶻ ; actV-M)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (_!_ ; set₁-a ; set₁-≢ ; Distinct₄ ; actM ; ColOrth-actMʷ)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (syl)
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (odd-M ; Minimal-M)
open import Examples.Groups.CCX+HH-TwoLevel.Signs {n}
open import Examples.Groups.CCX+HH-TwoLevel.QuadBase s o ps ks ih
open R {n} using (Path)
open import Examples.Groups.CCX+HH-TwoLevel.PathTools {n} using (via)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  open Distinct₄ D₄

  KQ : Word (Gen n)
  KQ = K a b c d a<b b<c c<d

edge-M : (e : Fin n) → toℕ e ≡ 0 → Path (M e) s o
edge-M e e0 = by (e FinP.≟ a)
  where
  e≤p : e ≤ p
  e≤p = ≡.subst (ℕ._≤ toℕ p) (≡.sym e0) ℕ.z≤n
  W′ = Mᶻ e W
  eq : col (actM (M-gen e) s) p ≡ scV K′ W′
  eq = ≡.trans (colg (M-gen e)) (actV-M e K′ W)
  mn : Minimal K′ W′
  mn = Minimal-M e W minK
  N′≡ : sylData p K′ W′ ≡ KQ • Mτ a (σ₄ W′ a b c d)
  N′≡ = syl-same-odd W′ (odd-M e W)
  pN′ : Path (sylData p K′ W′) (actM (M-gen e) s) (ColOrth-actMʷ (M e) o)
  pN′ = path-g (M-gen e) e≤p W′ eq mn
  -- W′ agrees with W off e.
  off : ∀ x → x ≢ e → W′ ! x ≡ W ! x
  off x x≢e = set₁-≢ e (ℤ.- (W ! e)) W x≢e
  by : Dec (e ≡ a) → Path (M e) s o
  -- Entry 0 is a: the sign of the syllable changes.
  by (yes e≡a) = via (M-gen e) s o (sylData p K′ W′) (syl s) pN′ rel pN
    where
    oa : oddℤ (W ! a) ≡ true
    oa = proj₁ (firstOdd-spec W fo)
    t′ : σ₄ W′ a b c d ≡ not t
    t′ = ≡.trans (≡.cong (λ x → ((x xor τ (W′ ! b)) xor τ (W′ ! c)) xor τ (W′ ! d))
                    (≡.trans (≡.cong τ (≡.trans (≡.cong (W′ !_) (≡.sym e≡a)) (set₁-a e (ℤ.- (W ! e)) W)))
                             (≡.trans (≡.cong (λ y → τ (ℤ.- (W ! y))) e≡a) (τ-neg (W ! a) oa))))
           (≡.trans (≡.cong₂ (λ y z → ((not (τ (W ! a)) xor τ y) xor τ z) xor τ (W′ ! d))
                       (off b (λ e′ → ab (≡.trans (≡.sym e≡a) (≡.sym e′)) ))
                       (off c (λ e′ → ac (≡.trans (≡.sym e≡a) (≡.sym e′)))))
              (≡.trans (≡.cong (λ z → ((not (τ (W ! a)) xor τ (W ! b)) xor τ (W ! c)) xor τ z)
                         (off d (λ e′ → ad (≡.trans (≡.sym e≡a) (≡.sym e′)))))
                 (not-xor (τ (W ! a)) (τ (W ! b)) (τ (W ! c)) (τ (W ! d)))))
      where
      not-xor : ∀ p q r s → ((not p xor q) xor r) xor s ≡ not (((p xor q) xor r) xor s)
      not-xor true true true true = ≡.refl
      not-xor true true true false = ≡.refl
      not-xor true true false true = ≡.refl
      not-xor true true false false = ≡.refl
      not-xor true false true true = ≡.refl
      not-xor true false true false = ≡.refl
      not-xor true false false true = ≡.refl
      not-xor true false false false = ≡.refl
      not-xor false true true true = ≡.refl
      not-xor false true true false = ≡.refl
      not-xor false true false true = ≡.refl
      not-xor false true false false = ≡.refl
      not-xor false false true true = ≡.refl
      not-xor false false true false = ≡.refl
      not-xor false false false true = ≡.refl
      not-xor false false false false = ≡.refl
    rel : sylData p K′ W′ • M e ≈ syl s
    rel = begin
      sylData p K′ W′ • M e                ≈⟨ cleft refl′ N′≡ ⟩
      (KQ • Mτ a (σ₄ W′ a b c d)) • M e    ≈⟨ cleft cright refl′ (≡.cong (Mτ a) t′) ⟩
      (KQ • Mτ a (not t)) • M e            ≈⟨ assoc ⟩
      KQ • (Mτ a (not t) • M e)            ≈⟨ cright cright refl′ (≡.cong M e≡a) ⟩
      KQ • (Mτ a (not t) • M a)            ≈⟨ cright Mτ-flip a t ⟩
      KQ • Mτ a t                          ≈⟨ refl′ (≡.sym N≡) ⟩
      syl s                                ∎
  -- Entry 0 is even: (-1)_[0] commutes with the syllable.
  by (no e≢a) = square (M-gen e) (sylData p K′ W′) (M e) pN′ e≤p rel
    where
    -- e lies below a, b, c and d.
    e<a : e < a
    e<a = ℕP.≤∧≢⇒< (≡.subst (ℕ._≤ toℕ a) (≡.sym e0) ℕ.z≤n) (λ te → e≢a (FinP.toℕ-injective te))
    e<b = FinP.<-trans e<a a<b
    e<c = FinP.<-trans e<b b<c
    e<d = FinP.<-trans e<c c<d
    ne : ∀ {x} → e < x → e ≢ x
    ne lt ≡.refl = FinP.<-irrefl ≡.refl lt
    t′ : σ₄ W′ a b c d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ y z → ((τ y xor τ z) xor τ (W′ ! c)) xor τ (W′ ! d))
                   (off a (λ e′ → ne e<a (≡.sym e′))) (off b (λ e′ → ne e<b (≡.sym e′))))
                 (≡.cong₂ (λ y z → ((τ (W ! a) xor τ (W ! b)) xor τ y) xor τ z)
                   (off c (λ e′ → ne e<c (≡.sym e′))) (off d (λ e′ → ne e<d (≡.sym e′))))
    rel : M e • syl s ≈ sylData p K′ W′ • M e
    rel = begin
      M e • syl s                          ≈⟨ cright refl′ N≡ ⟩
      M e • (KQ • Mτ a t)                  ≈⟨ sym assoc ⟩
      (M e • KQ) • Mτ a t                  ≈⟨ cleft comm-M e (K-gen a b c d a<b b<c c<d) (ne e<a , ne e<b , ne e<c , ne e<d) ⟩
      (KQ • M e) • Mτ a t                  ≈⟨ assoc ⟩
      KQ • (M e • Mτ a t)                  ≈⟨ cright sym (Mτ-comm a t (M-gen e) (λ e′ → ne e<a (≡.sym e′))) ⟩
      KQ • (Mτ a t • M e)                  ≈⟨ sym assoc ⟩
      (KQ • Mτ a t) • M e                  ≈⟨ cleft cright refl′ (≡.cong (Mτ a) (≡.sym t′)) ⟩
      (KQ • Mτ a (σ₄ W′ a b c d)) • M e    ≈⟨ cleft refl′ (≡.sym N′≡) ⟩
      sylData p K′ W′ • M e                ∎
