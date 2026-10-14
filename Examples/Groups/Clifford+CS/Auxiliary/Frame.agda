------------------------------------------------------------------------
-- Presentations of groups
--
-- The coset action through a frame
--
-- Item (b) of the Reidemeister–Schreier method asks that the two sides
-- of every two-level relation, traversed by the coset action from the
-- same coset, emit equivalent words.  Fix a sink g other than 0 and
-- embed the generators uniformly,
--
--     Φ(i_[a]) = i_[a] i_[g]⁻¹,  Φ(X_[a,b]) = (−1)_[g] X_[a,b],
--     Φ(K_[a,b]) = K_[a,b] i_[g]⁻¹;
--
-- then on any generator off g the action is conjugation of Φ by the
-- frame words T c = (i_[0] i_[g]⁻¹)^c,
--
--     act c y  ≈  T c · Φ(y) · T⁻ c′        (c′ the coset reached),
--
-- (`tr`), and along a word off g the conjugations telescope (`run`).
-- Φ of a two-level relation with a K is a rule of the hybrid letter at
-- the sink g, so item (b) for it is that rule (`ItemB`).
--
-- On the K-free generators `tr` is Corollary A.5's analogue: both sides
-- read as the same phased permutation (`ActionFree.row` and
-- `ActionFree.FramePP`).  On K it is the sink move: the action's K row
-- sits at its own sink t, and (i_[0] i_[t]⁻¹)^c = T c (i_[g] i_[t]⁻¹)^c,
-- the second factor passing K_[d,e] i_[t]⁻¹ (`ki-pp`), which then
-- becomes K_[d,e] i_[g]⁻¹ i_[g] i_[t]⁻¹ (`ki-sink`), the phases left
-- over being T⁻ (c + 1).  Checked on exact matrices for every
-- generator, coset and sink (scratchpad/tKI.py, 1372/1372 at N = 8).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin using (Fin ; zero)
open import Data.Nat using (ℕ ; suc ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≢_)

module Examples.Groups.Clifford+CS.Auxiliary.Frame
  (N′ : ℕ) (big : 16 ≤ suc N′) (g : Fin (suc N′)) (g0 : g ≢ zero) where

open import Data.Fin using (suc) renaming (_<_ to _<ᶠ_)
open import Data.List using ([] ; _∷_)
open import Data.List.Relation.Unary.All using ([] ; _∷_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
import Relation.Binary.Reasoning.Setoid as SR
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _ᵗ)

import Presentation.Base as PB

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (i-gen ; X-gen ; K-gen)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (pw ; xw)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules
  using (_R,_===_ ; kiw ; free⇒full-≈ ; ki-sink ; ki-pp)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets
  using (Coset ; ⟨0⟩ ; ⟨1⟩ ; ⟨2⟩ ; ⟨3⟩ ; inc ; inc² ; pows)
open import Examples.Groups.Clifford+CS.Auxiliary.CosetAction N′ big
  using (act ; 𝟎 ; Krow ; sink ; sink-off)
open import Examples.Groups.Clifford+CS.Auxiliary.ActionFree N′ big
  using (row ; row-kf ; pows-kf ; module FramePP)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc N′)
  using (_≐_ ; ≐-trans ; ≐-sym ; sp)
open import Examples.Groups.Clifford+CS.Auxiliary.NF N′
  using (KFreeʷ ; kf-pp ; kf-px ; gen ; cat ; nil)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique N′ using (A5)

open FramePP g using (TT⁻ ; T⁻T ; fr-i ; fr-X ; F1 ; F2)

private
  N : ℕ
  N = suc N′

  W : Set
  W = Word (GenP N)

open PB (N R,_===_)
  using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
open import Presentation.Properties (N R,_===_) using (word-setoid)
open SR word-setoid

private
  front : ∀ {a b} (s : W) → a ≈ b → a • s ≈ b • s
  front s e = cong e refl

  back : ∀ (p : W) {a b} → a ≈ b → p • a ≈ p • b
  back p e = cong refl e

  -- Corollary A.5's analogue, in the full theory.
  byA5 : ∀ {u v : W} → KFreeʷ u → KFreeʷ v → sp u ≐ sp v → u ≈ v
  byA5 ku kv e = free⇒full-≈ (A5 ku kv e)

  -- A product passes what each factor passes.
  pass-two : ∀ {w v x : W} → w • x ≈ x • w → v • x ≈ x • v →
             (w • v) • x ≈ x • (w • v)
  pass-two {w} {v} {x} wx vx = begin
    (w • v) • x    ≈⟨ assoc ⟩
    w • (v • x)    ≈⟨ back w vx ⟩
    w • (x • v)    ≈⟨ sym assoc ⟩
    (w • x) • v    ≈⟨ front v wx ⟩
    (x • w) • v    ≈⟨ assoc ⟩
    x • (w • v) ∎

  pows-pass : ∀ (c : Coset) {w x : W} → w • x ≈ x • w → pows c w • x ≈ x • pows c w
  pows-pass ⟨0⟩ e = trans left-unit (sym right-unit)
  pows-pass ⟨1⟩ e = e
  pows-pass ⟨2⟩ e = pass-two e e
  pows-pass ⟨3⟩ e = pass-two e (pass-two e e)

------------------------------------------------------------------------
-- The frame

T T⁻ : Coset → W
T  c = pows c (pw 𝟎 g)
T⁻ c = pows c (pw g 𝟎)

Φ : TL.Gen N → W
Φ (i-gen a)     = pw a g
Φ (X-gen a b p) = xw g a b p
Φ (K-gen a b p) = kiw a b g p

Φʷ : Word (TL.Gen N) → W
Φʷ [ y ]ʷ  = Φ y
Φʷ ε       = ε
Φʷ (u • v) = Φʷ u • Φʷ v

-- A generator off the sink.
Av : TL.Gen N → Set
Av (i-gen _)     = ⊤
Av (X-gen a b _) = g ≢ a × g ≢ b
Av (K-gen a b _) = g ≢ a × g ≢ b

Avʷ : Word (TL.Gen N) → Set
Avʷ [ y ]ʷ  = Av y
Avʷ ε       = ⊤
Avʷ (u • v) = Avʷ u × Avʷ v

private
  T-kf : ∀ (c : Coset) → KFreeʷ (T c)
  T-kf c = pows-kf c (gen (kf-pp 𝟎 g))

  T⁻-kf : ∀ (c : Coset) → KFreeʷ (T⁻ c)
  T⁻-kf c = pows-kf c (gen (kf-pp g 𝟎))

TT⁻≈ : ∀ (c : Coset) → T c • T⁻ c ≈ ε
TT⁻≈ c = byA5 (cat (T-kf c) (T⁻-kf c)) nil (TT⁻ c)

T⁻T≈ : ∀ (c : Coset) → T⁻ c • T c ≈ ε
T⁻T≈ c = byA5 (cat (T⁻-kf c) (T-kf c)) nil (T⁻T c)

------------------------------------------------------------------------
-- One generator

private
  -- The K row: its sink t moves to g.
  tr-K : ∀ (c : Coset) (d e : Fin N) .(p : d <ᶠ e) → g ≢ d → g ≢ e →
         Krow c d e p ≈ T c • (kiw d e g p • T⁻ (inc c))
  tr-K c d e p gd ge = begin
    A • (Kt • B)
      ≈⟨ front _ F1≈ ⟩
    (T c • Q) • (Kt • B)
      ≈⟨ assoc ⟩
    T c • (Q • (Kt • B))
      ≈⟨ back (T c) (sym assoc) ⟩
    T c • ((Q • Kt) • B)
      ≈⟨ back (T c) (front B QK) ⟩
    T c • ((Kt • Q) • B)
      ≈⟨ back (T c) assoc ⟩
    T c • (Kt • (Q • B))
      ≈⟨ back (T c) (front _ (sym (axiom (ki-sink d e g t p)))) ⟩
    T c • ((Kg • pw g t) • (Q • B))
      ≈⟨ back (T c) assoc ⟩
    T c • (Kg • (pw g t • (Q • B)))
      ≈⟨ back (T c) (back Kg F2≈) ⟩
    T c • (Kg • T⁻ (inc c)) ∎
    where
    t = sink d e
    A = pows c (pw 𝟎 t)
    B = pows (inc c) (pw t 𝟎)
    Q = pows c (pw g t)
    Kt = kiw d e t p
    Kg = kiw d e g p

    td : t ≢ d
    td with sink-off d e
    ... | _ ∷ q ∷ _ = q

    te : t ≢ e
    te with sink-off d e
    ... | _ ∷ _ ∷ q ∷ _ = q

    F1≈ : A ≈ T c • Q
    F1≈ = byA5 (pows-kf c (gen (kf-pp 𝟎 t)))
               (cat (T-kf c) (pows-kf c (gen (kf-pp g t)))) (F1 c t)

    F2≈ : pw g t • (Q • B) ≈ T⁻ (inc c)
    F2≈ = byA5 (cat (gen (kf-pp g t))
                    (cat (pows-kf c (gen (kf-pp g t)))
                         (pows-kf (inc c) (gen (kf-pp t 𝟎)))))
               (T⁻-kf (inc c)) (F2 c t)

    QK : Q • Kt ≈ Kt • Q
    QK = pows-pass c (axiom (ki-pp d e t g p gd ge td te))

-- The action is the frame's conjugation of Φ.
tr : ∀ (c : Coset) (y : TL.Gen N) → Av y →
     proj₁ (act c y) ≈ T c • (Φ y • T⁻ (proj₂ (act c y)))
tr c (i-gen a) _ =
  byA5 (row-kf c (i-gen a) tt)
       (cat (T-kf c) (cat (gen (kf-pp a g)) (T⁻-kf (inc c))))
       (≐-trans (row c (i-gen a) tt) (≐-sym (fr-i c a)))
tr c (X-gen zero b p) (ga , gb) =
  byA5 (row-kf c (X-gen zero b p) tt)
       (cat (T-kf c) (cat (gen (kf-px g zero b p)) (T⁻-kf (inc² c))))
       (≐-trans (row c (X-gen zero b p) tt) (≐-sym (fr-X c zero b p ga gb)))
tr c (X-gen (suc a) b p) (ga , gb) =
  byA5 (row-kf c (X-gen (suc a) b p) tt)
       (cat (T-kf c) (cat (gen (kf-px g (suc a) b p)) (T⁻-kf (inc² c))))
       (≐-trans (row c (X-gen (suc a) b p) tt) (≐-sym (fr-X c (suc a) b p ga gb)))
tr c (K-gen d e p) (gd , ge) = tr-K c d e p gd ge

------------------------------------------------------------------------
-- Along a word

run : ∀ (c : Coset) (u : Word (TL.Gen N)) → Avʷ u →
      proj₁ ((act ᵗ) c u) ≈ T c • (Φʷ u • T⁻ (proj₂ ((act ᵗ) c u)))
run c [ y ]ʷ  av        = tr c y av
run c ε       _         = sym (trans (back (T c) left-unit) (TT⁻≈ c))
run c (u • v) (au , av) = begin
  proj₁ ((act ᵗ) c u) • proj₁ ((act ᵗ) c′ v)
    ≈⟨ cong (run c u au) (run c′ v av) ⟩
  (T c • (Φʷ u • T⁻ c′)) • (T c′ • (Φʷ v • T⁻ c″))
    ≈⟨ assoc ⟩
  T c • ((Φʷ u • T⁻ c′) • (T c′ • (Φʷ v • T⁻ c″)))
    ≈⟨ back (T c) assoc ⟩
  T c • (Φʷ u • (T⁻ c′ • (T c′ • (Φʷ v • T⁻ c″))))
    ≈⟨ back (T c) (back (Φʷ u) (sym assoc)) ⟩
  T c • (Φʷ u • ((T⁻ c′ • T c′) • (Φʷ v • T⁻ c″)))
    ≈⟨ back (T c) (back (Φʷ u) (front (Φʷ v • T⁻ c″) (T⁻T≈ c′))) ⟩
  T c • (Φʷ u • (ε • (Φʷ v • T⁻ c″)))
    ≈⟨ back (T c) (back (Φʷ u) left-unit) ⟩
  T c • (Φʷ u • (Φʷ v • T⁻ c″))
    ≈⟨ back (T c) (sym assoc) ⟩
  T c • ((Φʷ u • Φʷ v) • T⁻ c″) ∎
  where
  c′ c″ : Coset
  c′ = proj₂ ((act ᵗ) c u)
  c″ = proj₂ ((act ᵗ) c′ v)
