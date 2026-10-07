------------------------------------------------------------------------
-- Presentations of groups
--
-- The diagonal calculus: products of phase gates, and a decision
-- procedure for equations between them
--
-- A list of rows with exponents denotes the product of the phase
-- gates P ℓ ^ k (prod).  Phase gates commute (Diagonal.Phase), have
-- order 8, and are permuted by conjugation with a linear generator
-- (Pz-conj: y • P ℓ • y ≈ P (ℓ ⋆ y), from the row step) and by the
-- shift (Pz-↑).  So a diagonal expression — T, ω, shifts, conjugates
-- by linear generators, products and powers (DE) — denotes a power of
-- ω times a product of phase gates (D-sound), and two expressions with
-- the same normal form (sorted, merged, exponents and the power of ω
-- reduced modulo 8) denote equal circuits (by-dnorm).  Equations that
-- need a relation beyond commutation and order — R₈, R₉, R₁₃ — are
-- proved by adding an instance of the relation, as an expression
-- equal to ε, before normalising (by-dnorm-with).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.Calculus where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map ; foldr)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_ ; _%_ ; _<ᵇ_)
open import Data.Nat.Properties using (*-comm)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Powers
open import Examples.Groups.CNOT+Dihedral.Evaluation using (_⁻¹ ; module Inv)
open import Examples.Groups.CNOT+Dihedral.Linear.Local using (CX01)
open import Examples.Groups.CNOT+Dihedral.Linear.Base hiding (s)
open import Examples.Groups.CNOT+Dihedral.Linear.Steps
open import Examples.Groups.CNOT+Dihedral.Diagonal.LocalT
open import Examples.Groups.CNOT+Dihedral.Diagonal.Phase

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Rows and phase gates at every width

liftNZ : NZ n → NZ (₁₊ n)
liftNZ {suc m} ℓ = sw ℓ

Pz : NZ n → Circuit n
Pz {suc m} ℓ = P ℓ

------------------------------------------------------------------------
-- The scalar

ω-comm : (w : Circuit n) → n ⊢ ω • w ≈ w • ω
ω-comm {n} w = Width.sym (comm-gate₀-w ω-gate w)

ωᵏ-comm : (k : ℕ) (w : Circuit n) → n ⊢ ω ^ k • w ≈ w • ω ^ k
ωᵏ-comm {n} k w = Pow.pow-comm n k (ω-comm w)

ω↑ : (₁₊ n) ⊢ ω ↑ ≈ ω
ω↑ {n} = ax' (ω↑=ω ω-gate)

ωᵏ↑ : (k : ℕ) → (₁₊ n) ⊢ (ω ^ k) ↑ ≈ ω ^ k
ωᵏ↑ {n} k = trans (refl' (↑-pow ω k)) (Pow.pow-cong (₁₊ n) k ω↑)
  where open Width (₁₊ n)

ωᵏ-mod : (k : ℕ) → n ⊢ ω ^ k ≈ ω ^ (k % 8)
ωᵏ-mod {n} k = Pow.pow-mod n ω (trans (by-assoc Eq.refl) (ax R₁₀)) k
  where open Width n

------------------------------------------------------------------------
-- Products of phase gates

PE : ℕ → Set
PE n = List (NZ n × ℕ)

prod : PE n → Circuit n
prod []             = ε
prod ((ℓ , k) ∷ pe) = Pz ℓ ^ k • prod pe

Pz-comm : (ℓ ℓ' : NZ n) → n ⊢ Pz ℓ • Pz ℓ' ≈ Pz ℓ' • Pz ℓ
Pz-comm {suc m} ℓ ℓ' = P-comm ℓ ℓ'

Pz-order : (ℓ : NZ n) → n ⊢ Pz ℓ ^ 8 ≈ ε
Pz-order {suc m} ℓ = begin
  (r ℓ ⁻¹ • T • r ℓ) ^ 8      ≈⟨ Pow.pow-conj (₁₊ m) (r ℓ) T 8 ⟩
  r ℓ ⁻¹ • T ^ 8 • r ℓ        ≈⟨ back _ (front _ (trans (by-assoc Eq.refl) (ax R₇))) ⟩
  r ℓ ⁻¹ • ε • r ℓ            ≈⟨ back _ left-unit ⟩
  r ℓ ⁻¹ • r ℓ                ≈⟨ Inv.inverseˡ (₁₊ m) ⟩
  ε                           ∎
  where open Width (₁₊ m)

private
  entry-comm : (ℓ : NZ n) (a : ℕ) (pe : PE n) → n ⊢ Pz ℓ ^ a • prod pe ≈ prod pe • Pz ℓ ^ a
  entry-comm {n} ℓ a []              = trans right-unit (sym left-unit)
    where open Width n
  entry-comm {n} ℓ a ((ℓ' , b) ∷ pe) =
    slide (Pow.pow-comm₂ n a b (Pz-comm ℓ ℓ')) (entry-comm ℓ a pe)
    where open Width n

prod-comm : (pe pe' : PE n) → n ⊢ prod pe • prod pe' ≈ prod pe' • prod pe
prod-comm {n} []             pe' = trans left-unit (sym right-unit)
  where open Width n
prod-comm {n} ((ℓ , a) ∷ pe) pe' = begin
  (Pz ℓ ^ a • prod pe) • prod pe'      ≈⟨ assoc ⟩
  Pz ℓ ^ a • prod pe • prod pe'        ≈⟨ back _ (prod-comm pe pe') ⟩
  Pz ℓ ^ a • prod pe' • prod pe        ≈⟨ sym assoc ⟩
  (Pz ℓ ^ a • prod pe') • prod pe      ≈⟨ front _ (entry-comm ℓ a pe') ⟩
  (prod pe' • Pz ℓ ^ a) • prod pe      ≈⟨ assoc ⟩
  prod pe' • Pz ℓ ^ a • prod pe        ∎
  where open Width n

prod-++ : (pe pe' : PE n) → n ⊢ prod (pe ++ pe') ≈ prod pe • prod pe'
prod-++ {n} []             pe' = sym left-unit
  where open Width n
prod-++ {n} ((ℓ , a) ∷ pe) pe' = trans (back _ (prod-++ pe pe')) (sym assoc)
  where open Width n

------------------------------------------------------------------------
-- Shifts and conjugates

liftE : NZ n × ℕ → NZ (₁₊ n) × ℕ
liftE (ℓ , k) = liftNZ ℓ , k

Pz-↑ : (ℓ : NZ n) → (₁₊ n) ⊢ (Pz ℓ) ↑ ≈ Pz (liftNZ ℓ)
Pz-↑ {suc m} ℓ = Width.sym (P-sw ℓ)

prod-↑ : (pe : PE n) → (₁₊ n) ⊢ (prod pe) ↑ ≈ prod (map liftE pe)
prod-↑ {n} []             = refl
  where open Width (₁₊ n)
prod-↑ {n} ((ℓ , k) ∷ pe) =
  cong (trans (refl' (↑-pow (Pz ℓ) k)) (Pow.pow-cong (₁₊ n) k (Pz-↑ ℓ))) (prod-↑ pe)
  where open Width (₁₊ n)

private
  -- T commutes with the letters the row step emits.
  T-K : (k : Word (KLet (₁₊ n))) → (₁₊ n) ⊢ T • ⟪ k ⟫ ≈ ⟪ k ⟫ • T
  T-K [ kup y ]ʷ = T-↑ [ ι y ]ʷ
  T-K [ kcx ]ʷ   = T-CX01
  T-K {n} ε       = Width.slide-ε (₁₊ n)
  T-K {n} (w • v) = Width.slide (₁₊ n) (T-K w) (T-K v)

  ι⁻¹ : (y : LGen n) → n ⊢ [ ι y ]ʷ ⁻¹ ≈ [ ι y ]ʷ
  ι⁻¹ {n} y = Width.sym (Inv.inverseʳ-unique n (ι-invol y))

Pz-conj : (y : LGen n) (ℓ : NZ n) → n ⊢ [ ι y ]ʷ • Pz ℓ • [ ι y ]ʷ ≈ Pz (ℓ ⋆ y)
Pz-conj {suc m} y ℓ = begin
  [ ι y ]ʷ • (r ℓ ⁻¹ • T • r ℓ) • [ ι y ]ʷ
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
  [ ι y ]ʷ • r ℓ ⁻¹ • T • r ℓ • [ ι y ]ʷ
    ≈⟨ front _ (sym (ι⁻¹ y)) ⟩
  [ ι y ]ʷ ⁻¹ • r ℓ ⁻¹ • T • r ℓ • [ ι y ]ʷ
    ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
  (r ℓ • [ ι y ]ʷ) ⁻¹ • T • r ℓ • [ ι y ]ʷ
    ≈⟨ cong (Inv.⁻¹-cong (₁₊ m) (r-step ℓ y)) (back T (r-step ℓ y)) ⟩
  (K • r ℓ') ⁻¹ • T • K • r ℓ'
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  r ℓ' ⁻¹ • (K ⁻¹ • T • K) • r ℓ'
    ≈⟨ back _ (front _ cancel-K) ⟩
  r ℓ' ⁻¹ • T • r ℓ' ∎
  where
  open Width (₁₊ m)
  K  = ⟪ rk ℓ y ⟫
  ℓ' = ℓ ⋆ y
  cancel-K : (₁₊ m) ⊢ K ⁻¹ • T • K ≈ T
  cancel-K = trans (back _ (T-K (rk ℓ y)))
               (trans (sym assoc) (trans (front _ (Inv.inverseˡ (₁₊ m))) left-unit))

conjE : LGen n → NZ n × ℕ → NZ n × ℕ
conjE y (ℓ , k) = ℓ ⋆ y , k

prod-conj : (y : LGen n) (pe : PE n) →
            n ⊢ [ ι y ]ʷ • prod pe • [ ι y ]ʷ ≈ prod (map (conjE y) pe)
prod-conj {n} y [] = trans (back _ left-unit) (ι-invol y)
  where open Width n
prod-conj {n} y ((ℓ , k) ∷ pe) = begin
  Y • (Pz ℓ ^ k • prod pe) • Y
    ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  Y • Pz ℓ ^ k • prod pe • Y
    ≈⟨ back Y (back _ (sym (Involution.cancelˡ (ι-invol y) (prod pe • Y)))) ⟩
  Y • Pz ℓ ^ k • Y • Y • prod pe • Y
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl ⟩
  (Y • Pz ℓ ^ k • Y) • Y • prod pe • Y
    ≈⟨ cong conj-pow (prod-conj y pe) ⟩
  Pz (ℓ ⋆ y) ^ k • prod (map (conjE y) pe) ∎
  where
  open Width n
  Y = [ ι y ]ʷ
  conj-pow : n ⊢ Y • Pz ℓ ^ k • Y ≈ Pz (ℓ ⋆ y) ^ k
  conj-pow = begin
    Y • Pz ℓ ^ k • Y          ≈⟨ front _ (sym (ι⁻¹ y)) ⟩
    Y ⁻¹ • Pz ℓ ^ k • Y       ≈⟨ sym (Pow.pow-conj n Y (Pz ℓ) k) ⟩
    (Y ⁻¹ • Pz ℓ • Y) ^ k     ≈⟨ Pow.pow-cong n k (front _ (ι⁻¹ y)) ⟩
    (Y • Pz ℓ • Y) ^ k        ≈⟨ Pow.pow-cong n k (Pz-conj y ℓ) ⟩
    Pz (ℓ ⋆ y) ^ k            ∎

------------------------------------------------------------------------
-- Powers of products

private
  pow-pow : (w : Circuit n) (i j : ℕ) → n ⊢ (w ^ i) ^ j ≈ w ^ (j * i)
  pow-pow {n} w i zero    = refl
    where open Width n
  pow-pow {n} w i (suc j) = begin
    (w ^ i) ^ suc j          ≈⟨ Pow.pow-suc n (w ^ i) j ⟩
    w ^ i • (w ^ i) ^ j      ≈⟨ back _ (pow-pow w i j) ⟩
    w ^ i • w ^ (j * i)      ≈⟨ sym (Pow.pow-+ n w i (j * i)) ⟩
    w ^ (i + j * i)          ∎
    where open Width n

scaleE : ℕ → NZ n × ℕ → NZ n × ℕ
scaleE k (ℓ , a) = ℓ , k * a

prod-pow : (k : ℕ) (pe : PE n) → n ⊢ prod pe ^ k ≈ prod (map (scaleE k) pe)
prod-pow {n} k [] = Pow.pow-ε n k
prod-pow {n} k ((ℓ , a) ∷ pe) = begin
  (Pz ℓ ^ a • prod pe) ^ k                ≈⟨ Pow.pow-• n k (entry-comm ℓ a pe) ⟩
  (Pz ℓ ^ a) ^ k • prod pe ^ k            ≈⟨ cong (pow-pow (Pz ℓ) a k) (prod-pow k pe) ⟩
  Pz ℓ ^ (k * a) • prod (map (scaleE k) pe) ∎
  where open Width n

------------------------------------------------------------------------
-- Diagonal expressions

infixr 7 _`•_
infixl 8 _`^_ _`↑

data DE : ℕ → Set where
  `T   : DE (₁₊ n)
  `ω   : DE n
  `ε   : DE n
  _`↑  : DE n → DE (₁₊ n)
  `c   : LGen n → DE n → DE n
  _`•_ : DE n → DE n → DE n
  _`^_ : DE n → ℕ → DE n

⟦_⟧ᴰ : DE n → Circuit n
⟦ `T ⟧ᴰ      = T
⟦ `ω ⟧ᴰ      = ω
⟦ `ε ⟧ᴰ      = ε
⟦ d `↑ ⟧ᴰ    = ⟦ d ⟧ᴰ ↑
⟦ `c y d ⟧ᴰ  = [ ι y ]ʷ • ⟦ d ⟧ᴰ • [ ι y ]ʷ
⟦ d `• e ⟧ᴰ  = ⟦ d ⟧ᴰ • ⟦ e ⟧ᴰ
⟦ d `^ k ⟧ᴰ  = ⟦ d ⟧ᴰ ^ k

-- The power of ω and the phase gates.
toPE : DE n → ℕ × PE n
toPE `T         = 0 , (e₀ , 1) ∷ []
toPE `ω         = 1 , []
toPE `ε         = 0 , []
toPE (d `↑)     = proj₁ (toPE d) , map liftE (proj₂ (toPE d))
toPE (`c y d)   = proj₁ (toPE d) , map (conjE y) (proj₂ (toPE d))
toPE (d `• e)   = proj₁ (toPE d) + proj₁ (toPE e) , proj₂ (toPE d) ++ proj₂ (toPE e)
toPE (d `^ k)   = k * proj₁ (toPE d) , map (scaleE k) (proj₂ (toPE d))

⟦_⟧ₑ : ℕ × PE n → Circuit n
⟦ s , pe ⟧ₑ = ω ^ s • prod pe

D-sound : (d : DE n) → n ⊢ ⟦ d ⟧ᴰ ≈ ⟦ toPE d ⟧ₑ
D-sound {n} `T = by-assoc Eq.refl
  where open Width n
D-sound {n} `ω = sym right-unit
  where open Width n
D-sound {n} `ε = sym left-unit
  where open Width n
D-sound {suc n} (d `↑) = begin
  ⟦ d ⟧ᴰ ↑                                 ≈⟨ lift (D-sound d) ⟩
  (ω ^ s) ↑ • (prod pe) ↑                  ≈⟨ cong (ωᵏ↑ s) (prod-↑ pe) ⟩
  ω ^ s • prod (map liftE pe)              ∎
  where
  open Width (suc n)
  s  = proj₁ (toPE d)
  pe = proj₂ (toPE d)
D-sound {n} (`c y d) = begin
  Y • ⟦ d ⟧ᴰ • Y                         ≈⟨ back Y (front Y (D-sound d)) ⟩
  Y • (ω ^ s • prod pe) • Y              ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (Y • ω ^ s) • prod pe • Y              ≈⟨ front _ (sym (ωᵏ-comm s Y)) ⟩
  (ω ^ s • Y) • prod pe • Y              ≈⟨ assoc ⟩
  ω ^ s • Y • prod pe • Y                ≈⟨ back _ (prod-conj y pe) ⟩
  ω ^ s • prod (map (conjE y) pe)        ∎
  where
  open Width n
  Y  = [ ι y ]ʷ
  s  = proj₁ (toPE d)
  pe = proj₂ (toPE d)
D-sound {n} (d `• e) = begin
  ⟦ d ⟧ᴰ • ⟦ e ⟧ᴰ                              ≈⟨ cong (D-sound d) (D-sound e) ⟩
  (ω ^ s • prod pe) • ω ^ t • prod qe          ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  ω ^ s • (prod pe • ω ^ t) • prod qe          ≈⟨ back _ (front _ (sym (ωᵏ-comm t (prod pe)))) ⟩
  ω ^ s • (ω ^ t • prod pe) • prod qe          ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (ω ^ s • ω ^ t) • prod pe • prod qe          ≈⟨ cong (sym (Pow.pow-+ n ω s t)) (sym (prod-++ pe qe)) ⟩
  ω ^ (s + t) • prod (pe ++ qe)                ∎
  where
  open Width n
  s  = proj₁ (toPE d)
  pe = proj₂ (toPE d)
  t  = proj₁ (toPE e)
  qe = proj₂ (toPE e)
D-sound {n} (d `^ k) = begin
  ⟦ d ⟧ᴰ ^ k                                   ≈⟨ Pow.pow-cong n k (D-sound d) ⟩
  (ω ^ s • prod pe) ^ k                        ≈⟨ Pow.pow-• n k (ωᵏ-comm s (prod pe)) ⟩
  (ω ^ s) ^ k • prod pe ^ k                    ≈⟨ cong (pow-pow ω s k) (prod-pow k pe) ⟩
  ω ^ (k * s) • prod (map (scaleE k) pe)       ∎
  where
  open Width n
  s  = proj₁ (toPE d)
  pe = proj₂ (toPE d)

------------------------------------------------------------------------
-- Normal forms of products

_≟ₙ_ : DecidableEquality (NZ n)
e₀   ≟ₙ e₀   = yes Eq.refl
e₀   ≟ₙ cx _ = no λ ()
e₀   ≟ₙ sw _ = no λ ()
cx _ ≟ₙ e₀   = no λ ()
sw _ ≟ₙ e₀   = no λ ()
cx ℓ ≟ₙ cx ℓ' with ℓ ≟ₙ ℓ'
... | yes Eq.refl = yes Eq.refl
... | no ¬p       = no λ { Eq.refl → ¬p Eq.refl }
sw ℓ ≟ₙ sw ℓ' with ℓ ≟ₙ ℓ'
... | yes Eq.refl = yes Eq.refl
... | no ¬p       = no λ { Eq.refl → ¬p Eq.refl }
cx _ ≟ₙ sw _ = no λ ()
sw _ ≟ₙ cx _ = no λ ()

key : NZ n → ℕ
key e₀     = 1
key (cx ℓ) = 1 + 2 * key ℓ
key (sw ℓ) = 2 * key ℓ

insert : NZ n × ℕ → PE n → PE n
insert (ℓ , a) [] = (ℓ , a) ∷ []
insert (ℓ , a) ((ℓ' , b) ∷ pe) with ℓ ≟ₙ ℓ'
... | yes _ = (ℓ' , a + b) ∷ pe
... | no _ with key ℓ <ᵇ key ℓ'
...   | true  = (ℓ , a) ∷ (ℓ' , b) ∷ pe
...   | false = (ℓ' , b) ∷ insert (ℓ , a) pe

sortPE : PE n → PE n
sortPE = foldr insert []

reduce : PE n → PE n
reduce [] = []
reduce ((ℓ , k) ∷ pe) with k % 8
... | zero  = reduce pe
... | suc j = (ℓ , suc j) ∷ reduce pe

norm : PE n → PE n
norm pe = reduce (sortPE pe)

insert-sound : (ℓ : NZ n) (a : ℕ) (pe : PE n) →
               n ⊢ prod (insert (ℓ , a) pe) ≈ Pz ℓ ^ a • prod pe
insert-sound {n} ℓ a [] = refl
  where open Width n
insert-sound {n} ℓ a ((ℓ' , b) ∷ pe) with ℓ ≟ₙ ℓ'
... | yes Eq.refl = trans (front _ (Pow.pow-+ n (Pz ℓ) a b)) assoc
  where open Width n
... | no _ with key ℓ <ᵇ key ℓ'
...   | true  = refl
  where open Width n
...   | false = begin
  Pz ℓ' ^ b • prod (insert (ℓ , a) pe)     ≈⟨ back _ (insert-sound ℓ a pe) ⟩
  Pz ℓ' ^ b • Pz ℓ ^ a • prod pe           ≈⟨ sym assoc ⟩
  (Pz ℓ' ^ b • Pz ℓ ^ a) • prod pe         ≈⟨ front _ (Pow.pow-comm₂ n b a (Pz-comm ℓ' ℓ)) ⟩
  (Pz ℓ ^ a • Pz ℓ' ^ b) • prod pe         ≈⟨ assoc ⟩
  Pz ℓ ^ a • Pz ℓ' ^ b • prod pe           ∎
  where open Width n

sort-sound : (pe : PE n) → n ⊢ prod (sortPE pe) ≈ prod pe
sort-sound {n} [] = refl
  where open Width n
sort-sound {n} ((ℓ , a) ∷ pe) = trans (insert-sound ℓ a (sortPE pe)) (back _ (sort-sound pe))
  where open Width n

reduce-sound : (pe : PE n) → n ⊢ prod (reduce pe) ≈ prod pe
reduce-sound {n} [] = refl
  where open Width n
reduce-sound {n} ((ℓ , k) ∷ pe) with k % 8 | Pow.pow-mod n (Pz ℓ) (Pz-order ℓ) k
... | zero  | e = trans (reduce-sound pe) (trans (sym left-unit) (front _ (sym e)))
  where open Width n
... | suc j | e = cong (sym e) (reduce-sound pe)
  where open Width n

norm-sound : (pe : PE n) → n ⊢ prod (norm pe) ≈ prod pe
norm-sound {n} pe = trans (reduce-sound (sortPE pe)) (sort-sound pe)
  where open Width n

------------------------------------------------------------------------
-- Deciding equations between diagonal expressions

dnorm : DE n → ℕ × PE n
dnorm d = proj₁ (toPE d) % 8 , norm (proj₂ (toPE d))

dnorm-sound : (d : DE n) → n ⊢ ⟦ d ⟧ᴰ ≈ ⟦ dnorm d ⟧ₑ
dnorm-sound {n} d =
  trans (D-sound d) (cong (ωᵏ-mod (proj₁ (toPE d))) (sym (norm-sound (proj₂ (toPE d)))))
  where open Width n

by-dnorm : (d e : DE n) → dnorm d ≡ dnorm e → n ⊢ ⟦ d ⟧ᴰ ≈ ⟦ e ⟧ᴰ
by-dnorm {n} d e eq =
  trans (dnorm-sound d) (trans (refl' (Eq.cong ⟦_⟧ₑ eq)) (sym (dnorm-sound e)))
  where open Width n

-- With a relation: an expression equal to ε, multiplied in first.
by-dnorm-with : (d e rel : DE n) → n ⊢ ⟦ rel ⟧ᴰ ≈ ε →
                dnorm (d `• rel) ≡ dnorm e → n ⊢ ⟦ d ⟧ᴰ ≈ ⟦ e ⟧ᴰ
by-dnorm-with {n} d e rel z eq =
  trans (sym right-unit) (trans (back _ (sym z)) (by-dnorm (d `• rel) e eq))
  where open Width n

------------------------------------------------------------------------
-- Instances of relations, as expressions equal to ε

private
  prod-8 : (pe : PE n) → n ⊢ prod (map (scaleE 8) pe) ≈ ε
  prod-8 {n} [] = refl
    where open Width n
  prod-8 {n} ((ℓ , a) ∷ pe) = begin
    Pz ℓ ^ (8 * a) • prod (map (scaleE 8) pe)   ≈⟨ cong p8 (prod-8 pe) ⟩
    ε • ε                                       ≈⟨ left-unit ⟩
    ε                                           ∎
    where
    open Width n
    p8 : n ⊢ Pz ℓ ^ (8 * a) ≈ ε
    p8 = trans (refl' (Eq.cong (Pz ℓ ^_) (*-comm 8 a)))
           (trans (sym (pow-pow (Pz ℓ) 8 a))
             (trans (Pow.pow-cong n a (Pz-order ℓ)) (Pow.pow-ε n a)))

  ω-8 : (s : ℕ) → n ⊢ ω ^ (8 * s) ≈ ε
  ω-8 {n} s = trans (refl' (Eq.cong (ω ^_) (*-comm 8 s)))
                (trans (sym (pow-pow ω 8 s))
                  (trans (Pow.pow-cong n s (trans (by-assoc Eq.refl) (ax R₁₀))) (Pow.pow-ε n s)))
    where open Width n

-- The eighth power of any diagonal expression is ε.
pow8-ε : (d : DE n) → n ⊢ ⟦ d `^ 8 ⟧ᴰ ≈ ε
pow8-ε {n} d =
  trans (D-sound (d `^ 8)) (trans (cong (ω-8 (proj₁ (toPE d))) (prod-8 (proj₂ (toPE d)))) left-unit)
  where open Width n

-- l • r⁷, which is ε when l is r.
rel : DE n → DE n → DE n
rel l r = l `• r `^ 7

rel-ε : (l r : DE n) → n ⊢ ⟦ l ⟧ᴰ ≈ ⟦ r ⟧ᴰ → n ⊢ ⟦ rel l r ⟧ᴰ ≈ ε
rel-ε {n} l r e = begin
  ⟦ l ⟧ᴰ • ⟦ r ⟧ᴰ ^ 7     ≈⟨ front _ e ⟩
  ⟦ r ⟧ᴰ • ⟦ r ⟧ᴰ ^ 7     ≈⟨ sym (Pow.pow-suc n ⟦ r ⟧ᴰ 7) ⟩
  ⟦ r `^ 8 ⟧ᴰ             ≈⟨ pow8-ε r ⟩
  ε                       ∎
  where open Width n

-- Instances moved around.
conj-ε : (y : LGen n) (d : DE n) → n ⊢ ⟦ d ⟧ᴰ ≈ ε → n ⊢ ⟦ `c y d ⟧ᴰ ≈ ε
conj-ε {n} y d e = trans (back _ (trans (front _ e) left-unit)) (ι-invol y)
  where open Width n

up-ε : (d : DE n) → n ⊢ ⟦ d ⟧ᴰ ≈ ε → (₁₊ n) ⊢ ⟦ d `↑ ⟧ᴰ ≈ ε
up-ε d e = lift e

•-ε : (d e : DE n) → n ⊢ ⟦ d ⟧ᴰ ≈ ε → n ⊢ ⟦ e ⟧ᴰ ≈ ε → n ⊢ ⟦ d `• e ⟧ᴰ ≈ ε
•-ε {n} d e p q = trans (cong p q) left-unit
  where open Width n

^-ε : (d : DE n) (k : ℕ) → n ⊢ ⟦ d ⟧ᴰ ≈ ε → n ⊢ ⟦ d `^ k ⟧ᴰ ≈ ε
^-ε {n} d k e = trans (Pow.pow-cong n k e) (Pow.pow-ε n k)
  where open Width n
