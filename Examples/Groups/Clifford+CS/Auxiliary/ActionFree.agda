------------------------------------------------------------------------
-- Presentations of groups
--
-- The K-free rows of the coset action, read as phased permutations
--
-- A K-free two-level generator is a phased permutation — i_[a] a phase
-- i at a, X_[a,b] the transposition — and so is every K-free word
-- over P′ (`PhasedPerm.sp`).  Read that way the action does what it
-- says: on a phase or an exchange at the coset c it emits a word whose
-- phased permutation is the generator's conjugated by i_[0]^c on the
-- left and i_[0]^-c′ on the right (`row`), and along a K-free word the
-- conjugations telescope (`run`).
--
-- With Corollary A.5's analogue (`Unique.A5`: K-free words with the
-- same phased permutation are equivalent) that settles everything
-- K-free in the Reidemeister–Schreier conditions at once — item (a)
-- for the three K-free letter shapes, and item (b) for every K-free
-- rule of the two-level presentation at every coset — with no case
-- analysis on where the indices meet 0.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)

module Examples.Groups.Clifford+CS.Auxiliary.ActionFree
  (N′ : ℕ) (big : 16 ≤ suc N′) where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin ; zero ; suc ; toℕ) renaming (_<_ to _<ᶠ_)
open import Data.Fin.Properties using (_<?_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _ᵗ)

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (i-gen ; X-gen ; K-gen)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets
  using (Coset ; ⟨0⟩ ; ⟨1⟩ ; ⟨2⟩ ; ⟨3⟩ ; inc ; inc² ; pows)
open import Examples.Groups.Clifford+CS.Auxiliary.CosetAction N′ big
  using (act ; 𝟎)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc N′)
open import Examples.Groups.Clifford+CS.Auxiliary.NF N′
  using (KFree ; KFreeʷ ; kf-pp ; kf-px ; gen ; nil ; cat)

private
  N : ℕ
  N = suc N′

------------------------------------------------------------------------
-- The two-level generators as phased permutations

-- A K is read as the identity: only K-free words are ever read.
spTg : TL.Gen N → PP
spTg (i-gen a)     = PH a p1
spTg (X-gen a b _) = SWP a b
spTg (K-gen _ _ _) = idPP

spT : Word (TL.Gen N) → PP
spT [ y ]ʷ  = spTg y
spT ε       = idPP
spT (u • v) = spT u ⊙ spT v

KFreeG : TL.Gen N → Set
KFreeG (i-gen _)     = ⊤
KFreeG (X-gen _ _ _) = ⊤
KFreeG (K-gen _ _ _) = ⊥

KFreeT : Word (TL.Gen N) → Set
KFreeT [ y ]ʷ  = KFreeG y
KFreeT ε       = ⊤
KFreeT (u • v) = KFreeT u × KFreeT v

------------------------------------------------------------------------
-- The representatives as phased permutations

-- The phase of a coset, and its negative.
cph cng : Coset → Ph
cph ⟨0⟩ = p0
cph ⟨1⟩ = p1
cph ⟨2⟩ = p2
cph ⟨3⟩ = p3

cng ⟨0⟩ = p0
cng ⟨1⟩ = p3
cng ⟨2⟩ = p2
cng ⟨3⟩ = p1

-- i_[0]^c and its inverse.
ρ ρ⁻ : Coset → PP
ρ  c = PH 𝟎 (cph c)
ρ⁻ c = PH 𝟎 (cng c)

private
  ph-cong : ∀ (x : Fin N) {k l : Ph} → k ≡ l → PH x k ≐ PH x l
  ph-cong x e = ≡⇒≐ (Eq.cong (PH x) e)

  cng-cph : ∀ (c : Coset) → cng c +ᵖ cph c ≡ p0
  cng-cph ⟨0⟩ = Eq.refl
  cng-cph ⟨1⟩ = Eq.refl
  cng-cph ⟨2⟩ = Eq.refl
  cng-cph ⟨3⟩ = Eq.refl

  cph-cng : ∀ (c : Coset) → cph c +ᵖ cng c ≡ p0
  cph-cng ⟨0⟩ = Eq.refl
  cph-cng ⟨1⟩ = Eq.refl
  cph-cng ⟨2⟩ = Eq.refl
  cph-cng ⟨3⟩ = Eq.refl

  -- The degrees the rows need.
  i-ar : ∀ (c : Coset) → cph c +ᵖ cng (inc c) ≡ p3
  i-ar ⟨0⟩ = Eq.refl
  i-ar ⟨1⟩ = Eq.refl
  i-ar ⟨2⟩ = Eq.refl
  i-ar ⟨3⟩ = Eq.refl

  x-ar : ∀ (c : Coset) → cph c +ᵖ cng (inc² c) ≡ p2
  x-ar ⟨0⟩ = Eq.refl
  x-ar ⟨1⟩ = Eq.refl
  x-ar ⟨2⟩ = Eq.refl
  x-ar ⟨3⟩ = Eq.refl

  x0-ar : ∀ (c : Coset) → p2 +ᵖ cng c ≡ cng (inc² c)
  x0-ar ⟨0⟩ = Eq.refl
  x0-ar ⟨1⟩ = Eq.refl
  x0-ar ⟨2⟩ = Eq.refl
  x0-ar ⟨3⟩ = Eq.refl

ρ⁻ρ : ∀ (c : Coset) → ρ⁻ c ⊙ ρ c ≐ idPP
ρ⁻ρ c = ≐-trans (PH-fuse 𝟎 (cng c) (cph c))
                (≐-trans (ph-cong 𝟎 (cng-cph c)) (PH-id 𝟎))

ρρ⁻ : ∀ (c : Coset) → ρ c ⊙ ρ⁻ c ≐ idPP
ρρ⁻ c = ≐-trans (PH-fuse 𝟎 (cph c) (cng c))
                (≐-trans (ph-cong 𝟎 (cph-cng c)) (PH-id 𝟎))

-- At ⟨0⟩ both are the identity.
ρ⟨0⟩ : ρ ⟨0⟩ ≐ idPP
ρ⟨0⟩ = PH-id 𝟎

ρ⁻⟨0⟩ : ρ⁻ ⟨0⟩ ≐ idPP
ρ⁻⟨0⟩ = PH-id 𝟎

------------------------------------------------------------------------
-- The rows

private
  -- A phase on 0 and the row's phase meet and fuse.
  row-i : ∀ (c : Coset) (a : Fin N) →
          PH a p1 ⊙ PH 𝟎 p3 ≐ ρ c ⊙ (PH a p1 ⊙ ρ⁻ (inc c))
  row-i c a = ≐-sym (begin
    PH 𝟎 α ⊙ (PH a p1 ⊙ PH 𝟎 β)
      ≈⟨ hop (PH 𝟎 α) (PH a p1) (PH 𝟎 α) (PH a p1) (PH 𝟎 β)
             (PH-comm 𝟎 a α p1) ⟩
    PH a p1 ⊙ (PH 𝟎 α ⊙ PH 𝟎 β)
      ≈⟨ ⊙-cong (≐-refl {PH a p1})
                (≐-trans (PH-fuse 𝟎 α β) (ph-cong 𝟎 (i-ar c))) ⟩
    PH a p1 ⊙ PH 𝟎 p3 ∎)
    where
    α = cph c
    β = cng (inc c)

  -- An exchange away from 0 passes the row's phases.
  row-X : ∀ (c : Coset) (a : Fin N′) (b : Fin N) .(p : suc a <ᶠ b) →
          PH 𝟎 p2 ⊙ SWP (suc a) b ≐ ρ c ⊙ (SWP (suc a) b ⊙ ρ⁻ (inc² c))
  row-X c a b p = ≐-sym (begin
    PH 𝟎 α ⊙ (SWP s b ⊙ PH 𝟎 β)
      ≈⟨ ⊙-cong (≐-refl {PH 𝟎 α})
                (≐-trans (SWP-PH s b 𝟎 β)
                         (⊙-cong (ph≡≐ (swapF-o s b 𝟎 (λ ()) z≢b))
                                 (≐-refl {SWP s b}))) ⟩
    PH 𝟎 α ⊙ (PH 𝟎 β ⊙ SWP s b)
      ≈⟨ ≐-sym (⊙-assoc (PH 𝟎 α) (PH 𝟎 β) (SWP s b)) ⟩
    (PH 𝟎 α ⊙ PH 𝟎 β) ⊙ SWP s b
      ≈⟨ ⊙-cong (≐-trans (PH-fuse 𝟎 α β) (ph-cong 𝟎 (x-ar c)))
                (≐-refl {SWP s b}) ⟩
    PH 𝟎 p2 ⊙ SWP s b ∎)
    where
    s = suc a
    α = cph c
    β = cng (inc² c)

    p′ : suc a <ᶠ b
    p′ = recompute (suc a <? b) p

    no : ∀ {x : Fin N′} → suc x <ᶠ 𝟎 → ⊥
    no ()

    z≢b : 𝟎 ≢ b
    z≢b e = no (Eq.subst (λ y → suc a <ᶠ y) (Eq.sym e) p′)

  -- The phases on 0 and b, collected.
  pair-mul : ∀ (b : Fin N) (x y x′ y′ : Ph) →
             (PH b x ⊙ PH 𝟎 y) ⊙ (PH b x′ ⊙ PH 𝟎 y′)
             ≐ PH b (x +ᵖ x′) ⊙ PH 𝟎 (y +ᵖ y′)
  pair-mul b x y x′ y′ = begin
    (PH b x ⊙ PH 𝟎 y) ⊙ (PH b x′ ⊙ PH 𝟎 y′)
      ≈⟨ ⊙-assoc (PH b x) (PH 𝟎 y) (PH b x′ ⊙ PH 𝟎 y′) ⟩
    PH b x ⊙ (PH 𝟎 y ⊙ (PH b x′ ⊙ PH 𝟎 y′))
      ≈⟨ ⊙-cong (≐-refl {PH b x})
                (hop (PH 𝟎 y) (PH b x′) (PH 𝟎 y) (PH b x′) (PH 𝟎 y′)
                     (PH-comm 𝟎 b y x′)) ⟩
    PH b x ⊙ (PH b x′ ⊙ (PH 𝟎 y ⊙ PH 𝟎 y′))
      ≈⟨ ≐-sym (⊙-assoc (PH b x) (PH b x′) (PH 𝟎 y ⊙ PH 𝟎 y′)) ⟩
    (PH b x ⊙ PH b x′) ⊙ (PH 𝟎 y ⊙ PH 𝟎 y′)
      ≈⟨ ⊙-cong (PH-fuse b x x′) (PH-fuse 𝟎 y y′) ⟩
    PH b (x +ᵖ x′) ⊙ PH 𝟎 (y +ᵖ y′) ∎

  -- (i_[b] i_[0]⁻¹)^c, collected.
  pows-P₂ : ∀ (b : Fin N) (c : Coset) →
            sp (pows c [ pp b 𝟎 ]ʷ) ≐ PH b (cph c) ⊙ PH 𝟎 (cng c)
  pows-P₂ b ⟨0⟩ =
    ≐-sym (≐-trans (⊙-cong (PH-id b) (PH-id 𝟎)) (⊙-idˡ idPP))
  pows-P₂ b ⟨1⟩ = ≐-refl
  pows-P₂ b ⟨2⟩ = pair-mul b p1 p3 p1 p3
  pows-P₂ b ⟨3⟩ =
    ≐-trans (⊙-cong (≐-refl {P₂ b 𝟎}) (pair-mul b p1 p3 p1 p3))
            (pair-mul b p1 p3 p2 p2)

  -- The transposition of 0 and b carries those phases across.
  sw2 : ∀ (b : Fin N) (x y : Ph) →
        SWP 𝟎 b ⊙ (PH b x ⊙ PH 𝟎 y) ≐ PH 𝟎 x ⊙ (PH b y ⊙ SWP 𝟎 b)
  sw2 b x y = begin
    SWP 𝟎 b ⊙ (PH b x ⊙ PH 𝟎 y)
      ≈⟨ hop (SWP 𝟎 b) (PH b x) (SWP 𝟎 b) (PH 𝟎 x) (PH 𝟎 y)
             (≐-trans (SWP-PH 𝟎 b b x)
                      (⊙-cong (ph≡≐ (swapF-b 𝟎 b)) (≐-refl {SWP 𝟎 b}))) ⟩
    PH 𝟎 x ⊙ (SWP 𝟎 b ⊙ PH 𝟎 y)
      ≈⟨ ⊙-cong (≐-refl {PH 𝟎 x})
                (≐-trans (SWP-PH 𝟎 b 𝟎 y)
                         (⊙-cong (ph≡≐ (swapF-a 𝟎 b)) (≐-refl {SWP 𝟎 b}))) ⟩
    PH 𝟎 x ⊙ (PH b y ⊙ SWP 𝟎 b) ∎

  -- An exchange on 0: its own phase, and the trailing phase pairs.
  row-X0 : ∀ (c : Coset) (b : Fin N) →
           (PH b p2 ⊙ SWP 𝟎 b) ⊙ sp (pows c [ pp b 𝟎 ]ʷ)
           ≐ ρ c ⊙ (SWP 𝟎 b ⊙ ρ⁻ (inc² c))
  row-X0 c b = ≐-trans lhs (≐-sym rhs)
    where
    α = cph c
    γ = cng c
    β = cng (inc² c)

    lhs : (PH b p2 ⊙ SWP 𝟎 b) ⊙ sp (pows c [ pp b 𝟎 ]ʷ)
          ≐ PH 𝟎 α ⊙ (PH b β ⊙ SWP 𝟎 b)
    lhs = begin
      (PH b p2 ⊙ SWP 𝟎 b) ⊙ sp (pows c [ pp b 𝟎 ]ʷ)
        ≈⟨ ⊙-assoc (PH b p2) (SWP 𝟎 b) (sp (pows c [ pp b 𝟎 ]ʷ)) ⟩
      PH b p2 ⊙ (SWP 𝟎 b ⊙ sp (pows c [ pp b 𝟎 ]ʷ))
        ≈⟨ ⊙-cong (≐-refl {PH b p2})
                  (⊙-cong (≐-refl {SWP 𝟎 b}) (pows-P₂ b c)) ⟩
      PH b p2 ⊙ (SWP 𝟎 b ⊙ (PH b α ⊙ PH 𝟎 γ))
        ≈⟨ ⊙-cong (≐-refl {PH b p2}) (sw2 b α γ) ⟩
      PH b p2 ⊙ (PH 𝟎 α ⊙ (PH b γ ⊙ SWP 𝟎 b))
        ≈⟨ hop (PH b p2) (PH 𝟎 α) (PH b p2) (PH 𝟎 α) (PH b γ ⊙ SWP 𝟎 b)
               (PH-comm b 𝟎 p2 α) ⟩
      PH 𝟎 α ⊙ (PH b p2 ⊙ (PH b γ ⊙ SWP 𝟎 b))
        ≈⟨ ⊙-cong (≐-refl {PH 𝟎 α})
                  (≐-trans (fuse (PH b p2) (PH b γ) (PH b (p2 +ᵖ γ)) (SWP 𝟎 b)
                                 (PH-fuse b p2 γ))
                           (⊙-cong (ph-cong b (x0-ar c)) (≐-refl {SWP 𝟎 b}))) ⟩
      PH 𝟎 α ⊙ (PH b β ⊙ SWP 𝟎 b) ∎

    rhs : ρ c ⊙ (SWP 𝟎 b ⊙ ρ⁻ (inc² c)) ≐ PH 𝟎 α ⊙ (PH b β ⊙ SWP 𝟎 b)
    rhs = ⊙-cong (≐-refl {PH 𝟎 α})
                 (≐-trans (SWP-PH 𝟎 b 𝟎 β)
                          (⊙-cong (ph≡≐ (swapF-a 𝟎 b)) (≐-refl {SWP 𝟎 b})))

row : ∀ (c : Coset) (y : TL.Gen N) → KFreeG y →
      sp (proj₁ (act c y)) ≐ ρ c ⊙ (spTg y ⊙ ρ⁻ (proj₂ (act c y)))
row c (i-gen a)           _ = row-i c a
row c (X-gen zero b p)    _ = row-X0 c b
row c (X-gen (suc a) b p) _ = row-X c a b p

private
  pows-kf : ∀ (c : Coset) {w : Word (GenP N)} → KFreeʷ w → KFreeʷ (pows c w)
  pows-kf ⟨0⟩ k = nil
  pows-kf ⟨1⟩ k = k
  pows-kf ⟨2⟩ k = cat k k
  pows-kf ⟨3⟩ k = cat k (cat k k)

row-kf : ∀ (c : Coset) (y : TL.Gen N) → KFreeG y → KFreeʷ (proj₁ (act c y))
row-kf c (i-gen a)           _ = gen (kf-pp a 𝟎)
row-kf c (X-gen zero b p)    _ = cat (gen (kf-px b 𝟎 b p)) (pows-kf c (gen (kf-pp b 𝟎)))
row-kf c (X-gen (suc a) b p) _ = gen (kf-px 𝟎 (suc a) b p)

------------------------------------------------------------------------
-- Along a word

run : ∀ (c : Coset) (u : Word (TL.Gen N)) → KFreeT u →
      sp (proj₁ ((act ᵗ) c u)) ≐ ρ c ⊙ (spT u ⊙ ρ⁻ (proj₂ ((act ᵗ) c u)))
run c [ y ]ʷ  k         = row c y k
run c ε       _         =
  ≐-sym (≐-trans (⊙-cong (≐-refl {ρ c}) (⊙-idˡ (ρ⁻ c))) (ρρ⁻ c))
run c (u • v) (ku , kv) = begin
  sp wu ⊙ sp wv
    ≈⟨ ⊙-cong (run c u ku) (run c′ v kv) ⟩
  (ρ c ⊙ (spT u ⊙ ρ⁻ c′)) ⊙ (ρ c′ ⊙ (spT v ⊙ ρ⁻ c″))
    ≈⟨ ⊙-assoc (ρ c) (spT u ⊙ ρ⁻ c′) (ρ c′ ⊙ (spT v ⊙ ρ⁻ c″)) ⟩
  ρ c ⊙ ((spT u ⊙ ρ⁻ c′) ⊙ (ρ c′ ⊙ (spT v ⊙ ρ⁻ c″)))
    ≈⟨ ⊙-cong (≐-refl {ρ c})
              (⊙-assoc (spT u) (ρ⁻ c′) (ρ c′ ⊙ (spT v ⊙ ρ⁻ c″))) ⟩
  ρ c ⊙ (spT u ⊙ (ρ⁻ c′ ⊙ (ρ c′ ⊙ (spT v ⊙ ρ⁻ c″))))
    ≈⟨ ⊙-cong (≐-refl {ρ c})
              (⊙-cong (≐-refl {spT u})
                      (drop (ρ⁻ c′) (ρ c′) (spT v ⊙ ρ⁻ c″) (ρ⁻ρ c′))) ⟩
  ρ c ⊙ (spT u ⊙ (spT v ⊙ ρ⁻ c″))
    ≈⟨ ⊙-cong (≐-refl {ρ c}) (≐-sym (⊙-assoc (spT u) (spT v) (ρ⁻ c″))) ⟩
  ρ c ⊙ ((spT u ⊙ spT v) ⊙ ρ⁻ c″) ∎
  where
  c′ c″ : Coset
  c′ = proj₂ ((act ᵗ) c u)
  c″ = proj₂ ((act ᵗ) c′ v)

  wu wv : Word (GenP N)
  wu = proj₁ ((act ᵗ) c u)
  wv = proj₁ ((act ᵗ) c′ v)

run-kf : ∀ (c : Coset) (u : Word (TL.Gen N)) → KFreeT u →
         KFreeʷ (proj₁ ((act ᵗ) c u))
run-kf c [ y ]ʷ  k         = row-kf c y k
run-kf c ε       _         = nil
run-kf c (u • v) (ku , kv) =
  cat (run-kf c u ku) (run-kf (proj₂ ((act ᵗ) c u)) v kv)
