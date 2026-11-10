------------------------------------------------------------------------
-- Presentations of groups
--
-- The block normal form NF(E, B, S)
--
-- Section 3 of the paper: every four-wire circuit is equal to exactly
-- one circuit NF(E, B, S) = C(E) D(B) r_S (in composition order), for E
-- an even permutation and B a permutation of the eight states of the
-- lower wires and S an eight-element set of the sixteen states.  r_S
-- carries S onto the half H₀ where wire 3 is 0, D(B) applies B to the
-- lower wires and C(E) applies E to them on the half where wire 3 is 1.
-- The circuits are fixed by the formalization's own deterministic
-- choices (the theorems hold for any): D(B) is the circuit of
-- Symmetric's Coxeter word for B on the Gray positions (Width3's edge
-- Toffolis), C(E) the controlled matchings of EvenRS 8's symbols for
-- E's word (CCerts' Φ), and r_S the circuit of EvenRS 16's symbols for
-- the frame of S's states followed by the others (NFLib's ts), with one
-- transposition of the last two states when that word is odd.
--
-- Here: the states and Four's numbering (NFTables), the building
-- blocks and their functions (D-sem, C-low, C-high, r-sem), the
-- coordinates (Coords) and the function of a normal form (NF-sem).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.NormalForm where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
open import Data.Bool.Properties using (not-involutive)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Fin.Permutation
  using (Permutation′ ; permutation ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; inverseˡ ; inverseʳ ; _∘ₚ_ ; flip)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _/_ ; _! ; _<ᵇ_)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
import Data.Vec.Base as V
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇ ; ₈ ; ₉ ; ₁₀ ; ₁₁ ; ₁₂ ; ₁₃ ; ₁₄ ; ₁₅)

import Examples.Groups.Symmetric.Interpretation as SymI
import Examples.Groups.Symmetric.Surjectivity as SSurj
import Examples.Groups.Symmetric.Syntactics as Sym
import Examples.Groups.Symmetric.CoxeterFrames as CF
open import Examples.Groups.Alternating.Parity using (parity ; sign)
open import Examples.Groups.Alternating.Semantics using (Alt)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (Bits ; ⟦_⟧ ; ⟦_⟧ᵍ ; _≐_ ; sound)
open import Examples.Groups.XCXCCX-4bit.Placed using (ι* ; ι*-sem)
open import Examples.Groups.XCXCCX-4bit.ToPlaced using (pg ; pg-ok)
import Examples.Groups.XCXCCX-4bit.Coxeter as Cox
import Examples.Groups.XCXCCX-4bit.ByCoxeter as ByCoxeter
import Examples.Groups.XCXCCX-4bit.EvenRS as ERS
import Examples.Groups.XCXCCX-4bit.Width3 as W3
import Examples.Groups.XCXCCX-4bit.Four as Four
open import Examples.Groups.XCXCCX-4bit.PFrames using (Pc)
open import Examples.Groups.XCXCCX-4bit.CBase using (Pc-↓)
open import Examples.Groups.XCXCCX-4bit.CSem using (enc8 ; pos ; mF*)
open import Examples.Groups.XCXCCX-4bit.CCerts using (Xs ; Φ*)
open import Examples.Groups.XCXCCX-4bit.CFaithful using (Xs-sem ; Φ*-act)
open import Examples.Groups.XCXCCX-4bit.KFaithful using (faithful₃ ; mF*-low)
open import Examples.Groups.XCXCCX-4bit.Groups using (inv-sem)
import Examples.Groups.XCXCCX-4bit.Groups as Groups
open import Examples.Groups.XCXCCX-4bit.Completeness using (complete₄)
open import Examples.Groups.XCXCCX-4bit.NFLib
  using (ts ; ts-cong ; ts-length ; ts-distinct ; weight ; weight-perm ; ‼-total ; ‼-ts ; frameL ; frameL-act)
open import Examples.Groups.XCXCCX-4bit.EvenWord using (module Coset ; module Lift)
open import Examples.Groups.XCXCCX-4bit.NFTables
  using (w3 ; st ; w3-st ; pos-st ; st-eta ; enc8-st ; idx ; enc′ ; enc′-idx ; isHi′ ; pos4′
        ; idx-eta ; isHi-lt ; rev8 ; hi-lift)

module F = Four faithful₃
open F using (enc ; dec ; dec-enc ; enc-dec)
open F.RL using (R* ; R*-act)
open F.RL.Complete F.R-rel F.tw F.tw-ok using (translate ; translate-ok)
module E16 = ERS 16

------------------------------------------------------------------------
-- States, in Four's numbering

private
  enc-agree : ∀ i → enc i ≡ enc′ i
  enc-agree ₀ = Eq.refl
  enc-agree ₁ = Eq.refl
  enc-agree ₂ = Eq.refl
  enc-agree ₃ = Eq.refl
  enc-agree ₄ = Eq.refl
  enc-agree ₅ = Eq.refl
  enc-agree ₆ = Eq.refl
  enc-agree ₇ = Eq.refl
  enc-agree ₈ = Eq.refl
  enc-agree ₉ = Eq.refl
  enc-agree ₁₀ = Eq.refl
  enc-agree ₁₁ = Eq.refl
  enc-agree ₁₂ = Eq.refl
  enc-agree ₁₃ = Eq.refl
  enc-agree ₁₄ = Eq.refl
  enc-agree ₁₅ = Eq.refl

-- The half (wire 3) and the Gray position of a numbered state.
isHi : Fin 16 → Bool
isHi i = w3 (enc i)

pos4 : Fin 16 → Fin 8
pos4 i = pos (enc i)

enc-idx : ∀ b p → enc (idx b p) ≡ st b p
enc-idx b p = Eq.trans (enc-agree (idx b p)) (enc′-idx b p)

dec-st : ∀ b p → dec (st b p) ≡ idx b p
dec-st b p = Eq.trans (Eq.cong dec (Eq.sym (enc-idx b p))) (dec-enc (idx b p))

isHi-idx : ∀ b p → isHi (idx b p) ≡ b
isHi-idx b p = Eq.trans (Eq.cong w3 (enc-idx b p)) (w3-st b p)

pos4-idx : ∀ b p → pos4 (idx b p) ≡ p
pos4-idx b p = Eq.trans (Eq.cong pos (enc-idx b p)) (pos-st b p)

idx-isHi : ∀ i → idx (isHi i) (pos4 i) ≡ i
idx-isHi i = Eq.subst (λ x → idx (w3 x) (pos x) ≡ i) (Eq.sym (enc-agree i)) (idx-eta i)

isHi-<ᵇ : ∀ i → isHi i ≡ not (toℕ i <ᵇ 8)
isHi-<ᵇ i = Eq.trans (Eq.cong w3 (enc-agree i)) (isHi-lt i)

-- A numbered state is the state of its half at its position.
enc-st : ∀ i → enc i ≡ st (isHi i) (pos4 i)
enc-st i = Eq.sym (st-eta (enc i))

------------------------------------------------------------------------
-- A circuit as a permutation of the numbered states

-- Four's translation into the symbols of EvenRS 16, as a Coxeter word.
-- Its width is written 8 + 8 so that the sign lemmas of EvenWord.Lift,
-- at j = m = 8, meet the same spelling.
tr : Circuit 4 → Word (Cox.SG (8 + 8))
tr u = (E16.f ʷ) (translate (pg u))

at : ∀ u i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ tr u ⟧ ⟨$⟩ʳ i)
at u i =
  Eq.trans (sound (PB.trans (pg-ok u) (translate-ok (pg u))) (enc i))
    (Eq.trans (ι*-sem (R* (translate (pg u))) (enc i)) (R*-act (translate (pg u)) i))

perm : Circuit 4 → Permutation′ (8 + 8)
perm u = SymI.⟦ tr u ⟧

perm-at : ∀ u i → perm u ⟨$⟩ʳ i ≡ dec (⟦ u ⟧ (enc i))
perm-at u i = Eq.trans (Eq.sym (dec-enc _)) (Eq.cong dec (Eq.sym (at u i)))

private
  parity-f : (w : Word E16.Sch) → parity ((E16.f ʷ) w) ≡ false
  parity-f [ E16.γ false d p q ]ʷ = Eq.refl
  parity-f [ E16.γ true  d p q ]ʷ = Eq.refl
  parity-f ε                     = Eq.refl
  parity-f (u • v)               = Eq.cong₂ _xor_ (parity-f u) (parity-f v)

parity-tr : ∀ u → parity (tr u) ≡ false
parity-tr u = parity-f (translate (pg u))

------------------------------------------------------------------------
-- Reversed circuits

revC : Circuit 4 → Circuit 4
revC [ g ]ʷ   = [ g ]ʷ
revC ε       = ε
revC (u • v) = revC v • revC u

revC-sem : ∀ w x → ⟦ revC w ⟧ (⟦ w ⟧ x) ≡ x
revC-sem [ g ]ʷ   x = inv-sem g x
revC-sem ε       x = Eq.refl
revC-sem (u • v) x = Eq.trans (Eq.cong ⟦ revC u ⟧ (revC-sem v (⟦ u ⟧ x))) (revC-sem u x)

------------------------------------------------------------------------
-- D(B): B on the lower wires

private
  module V3 = ByCoxeter.Via 3 8 W3.T W3.cox W3.enc W3.dec W3.dec-enc W3.T-act W3.tw W3.tw-ok
  open Cox.Circuits 8 W3.T using () renaming (Pc to Pc₃)

  gen↓ : {n : ℕ} (g : Gen n) (x : Bits n) (b : Bool) →
         ⟦ g ↧ᵏ 1 ⟧ᵍ (x V.++ (b ∷ [])) ≡ ⟦ g ⟧ᵍ x V.++ (b ∷ [])
  gen↓ (gate₀ ⌈ () ⌉) x b
  gen↓ (gate₁ ⌈ X-gate ⌉) (a ∷ x) b = Eq.refl
  gen↓ (gate₂ ⌈ CX-gate ⌉) (a ∷ c ∷ x) b = Eq.refl
  gen↓ (gate₂ swap) (a ∷ c ∷ x) b = Eq.refl
  gen↓ (gate₃ ⌈ CCX-gate ⌉) (a ∷ c ∷ d ∷ x) b = Eq.refl
  gen↓ (g ↥) (a ∷ x) b = Eq.cong (a ∷_) (gen↓ g x b)

  word↓ : {n : ℕ} (w : Circuit n) (x : Bits n) (b : Bool) →
          ⟦ w ↓ᵏ 1 ⟧ (x V.++ (b ∷ [])) ≡ ⟦ w ⟧ x V.++ (b ∷ [])
  word↓ [ g ]ʷ   x b = gen↓ g x b
  word↓ ε       x b = Eq.refl
  word↓ (u • v) x b = Eq.trans (Eq.cong ⟦ v ↓ᵏ 1 ⟧ (word↓ u x b)) (word↓ v (⟦ u ⟧ x) b)

-- The building blocks are opaque, with their definitions as equations:
-- a goal about ⟦ D B ⟧ x met by a lemma about its unfolding made Agda
-- evaluate the circuit of Symmetric's word for B on the state.
opaque
  D : Permutation′ 8 → Circuit 4
  D B = Pc 0 (proj₁ (SSurj.go 8 B))

  D-def : ∀ B → D B ≡ Pc 0 (proj₁ (SSurj.go 8 B))
  D-def B = Eq.refl

private
  -- Over a variable word with its permutation.
  Pc-st : (w : Word (Cox.SG 8)) (B : Permutation′ 8) → (∀ p → SymI.⟦ w ⟧ ⟨$⟩ʳ p ≡ B ⟨$⟩ʳ p) →
          ∀ b p → ⟦ Pc 0 w ⟧ (st b p) ≡ st b (B ⟨$⟩ʳ p)
  Pc-st w B hw b p =
    Eq.trans (Eq.cong (λ c → ⟦ c ⟧ (st b p)) (Pc-↓ 0 w))
      (Eq.trans (word↓ (Pc₃ 0 w) (W3.enc p) b)
        (Eq.cong (λ x → x V.++ (b ∷ [])) (Eq.trans (V3.Pc-sem w p) (Eq.cong W3.enc (hw p)))))

D-sem : ∀ B b p → ⟦ D B ⟧ (st b p) ≡ st b (B ⟨$⟩ʳ p)
D-sem B b p =
  Eq.trans (Eq.cong (λ c → ⟦ c ⟧ (st b p)) (D-def B)) (Pc-st (proj₁ (SSurj.go 8 B)) B (Coset.go-sem 8 B) b p)

------------------------------------------------------------------------
-- C(E): E on the lower wires where wire 3 is 1

-- The controlled matchings of EvenRS 8's symbols for Symmetric's word
-- for E.
opaque
  C : Alt 8 → Circuit 4
  C a = Xs (Φ* (Coset.syms 8 a))

  C-def : ∀ a → C a ≡ Xs (Φ* (Coset.syms 8 a))
  C-def a = Eq.refl

C-low : ∀ a p → ⟦ C a ⟧ (st false p) ≡ st false p
C-low a p = Eq.trans (Eq.cong (λ c → ⟦ c ⟧ (st false p)) (C-def a)) (go (W3.enc p))
  where
  go : (x : Bits 3) → ⟦ Xs (Φ* (Coset.syms 8 a)) ⟧ (x V.++ (false ∷ [])) ≡ x V.++ (false ∷ [])
  go (a′ ∷ b ∷ c ∷ []) = Eq.trans (Xs-sem (Φ* (Coset.syms 8 a)) _) (mF*-low (Φ* (Coset.syms 8 a)) a′ b c)

private
  -- Over a variable word of symbols with its permutation.
  Xs-st : (x : Word (Coset.Sch 8)) (E : Permutation′ 8) → (∀ p → SymI.⟦ (Coset.f 8 ʷ) x ⟧ ⟨$⟩ʳ p ≡ E ⟨$⟩ʳ p) →
          ∀ p → ⟦ Xs (Φ* x) ⟧ (st true p) ≡ st true (E ⟨$⟩ʳ p)
  Xs-st x E hx p =
    Eq.trans (Xs-sem (Φ* x) (st true p))
      (Eq.trans (Eq.cong (mF* (Φ* x)) (Eq.sym (enc8-st p)))
        (Eq.trans (Φ*-act x p) (Eq.trans (Eq.cong enc8 (hx p)) (enc8-st (E ⟨$⟩ʳ p)))))

C-high : (a : Alt 8) → ∀ p → ⟦ C a ⟧ (st true p) ≡ st true (Alt.perm a ⟨$⟩ʳ p)
C-high a p =
  Eq.trans (Eq.cong (λ c → ⟦ c ⟧ (st true p)) (C-def a))
    (Xs-st (Coset.syms 8 a) (Alt.perm a) (Coset.sym-sem 8 a) p)

------------------------------------------------------------------------
-- r_S: S onto the half H₀

-- The transposition of the last two states.
s14 : Cox.SG 16
s14 = Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥

fixB : Bool → Word (Cox.SG 16) → Word (Cox.SG 16)
fixB true  w = w • [ s14 ]ʷ
fixB false w = w

-- A word made even by the transposition of the last two states.
fix : Word (Cox.SG 16) → Word (Cox.SG 16)
fix w = fixB (parity w) w

fix-parity : ∀ w → parity (fix w) ≡ false
fix-parity w = go (parity w) Eq.refl
  where
  go : (b : Bool) → parity w ≡ b → parity (fixB b w) ≡ false
  go true  e = Eq.cong (_xor true) e
  go false e = e

-- The word of r_S, and its permutation γ S.
wS : (Fin 16 → Bool) → Word (Cox.SG 16)
wS S = fix (frameL (ts S))

γ : (Fin 16 → Bool) → Permutation′ 16
γ S = SymI.⟦ wS S ⟧

private
  isHi-s14 : ∀ j → isHi (SymI.⟦ [ s14 ]ʷ ⟧ ⟨$⟩ʳ j) ≡ isHi j
  isHi-s14 ₀ = Eq.refl
  isHi-s14 ₁ = Eq.refl
  isHi-s14 ₂ = Eq.refl
  isHi-s14 ₃ = Eq.refl
  isHi-s14 ₄ = Eq.refl
  isHi-s14 ₅ = Eq.refl
  isHi-s14 ₆ = Eq.refl
  isHi-s14 ₇ = Eq.refl
  isHi-s14 ₈ = Eq.refl
  isHi-s14 ₉ = Eq.refl
  isHi-s14 ₁₀ = Eq.refl
  isHi-s14 ₁₁ = Eq.refl
  isHi-s14 ₁₂ = Eq.refl
  isHi-s14 ₁₃ = Eq.refl
  isHi-s14 ₁₄ = Eq.refl
  isHi-s14 ₁₅ = Eq.refl

  isHi-fix : ∀ w j → isHi (SymI.⟦ fix w ⟧ ⟨$⟩ʳ j) ≡ isHi (SymI.⟦ w ⟧ ⟨$⟩ʳ j)
  isHi-fix w j = go (parity w)
    where
    go : (b : Bool) → isHi (SymI.⟦ fixB b w ⟧ ⟨$⟩ʳ j) ≡ isHi (SymI.⟦ w ⟧ ⟨$⟩ʳ j)
    go true  = isHi-s14 (SymI.⟦ w ⟧ ⟨$⟩ʳ j)
    go false = Eq.refl

  -- The frame of ts S sends S into H₀ and the rest into H₁.
  frame-half : (S : Fin 16 → Bool) → weight S ≡ 8 → ∀ i →
               isHi (SymI.⟦ frameL (ts S) ⟧ ⟨$⟩ʳ i) ≡ not (S i)
  frame-half S w8 i = Eq.trans (isHi-<ᵇ j) (Eq.cong not (Eq.sym S-i))
    where
    j = SymI.⟦ frameL (ts S) ⟧ ⟨$⟩ʳ i
    entry = ‼-total (ts S) (toℕ j) (Eq.subst (toℕ j Data.Nat.Base.<_) (Eq.sym (ts-length S)) (FinP.toℕ<n j))
      where import Data.Nat.Base
    x = proj₁ entry
    x≡i : x ≡ i
    x≡i = Eq.trans (Eq.sym (frameL-act (ts S) (ts-distinct S) j x (proj₂ entry)))
                   (inverseˡ (SymI.⟦ frameL (ts S) ⟧))
    S-i : S i ≡ (toℕ j <ᵇ 8)
    S-i = Eq.subst (λ y → S y ≡ (toℕ j <ᵇ 8)) x≡i
            (Eq.trans (‼-ts S (toℕ j) (proj₂ entry)) (Eq.cong (toℕ j <ᵇ_) w8))

isHi-γ : (S : Fin 16 → Bool) → weight S ≡ 8 → ∀ i → isHi (γ S ⟨$⟩ʳ i) ≡ not (S i)
isHi-γ S w8 i = Eq.trans (isHi-fix (frameL (ts S)) i) (frame-half S w8 i)

-- The circuit r_S.
opaque
  r : (Fin 16 → Bool) → Circuit 4
  r S = ι* (R* (proj₁ (E16.rs false (wS S))))

  r-def : ∀ S → r S ≡ ι* (R* (proj₁ (E16.rs false (wS S))))
  r-def S = Eq.refl

  -- r_S depends only on the states of S.
  r-cong : {S S′ : Fin 16 → Bool} → (∀ i → S i ≡ S′ i) → r S ≡ r S′
  r-cong e = Eq.cong (λ l → ι* (R* (proj₁ (E16.rs false (fix (frameL l)))))) (ts-cong e)

r-sem : ∀ S i → ⟦ r S ⟧ (enc i) ≡ enc (γ S ⟨$⟩ʳ i)
r-sem S i =
  Eq.trans (Eq.cong (λ c → ⟦ c ⟧ (enc i)) (r-def S))
    (Eq.trans (ι*-sem (R* (proj₁ (E16.rs false (wS S)))) (enc i))
      (Eq.trans (R*-act (proj₁ (E16.rs false (wS S))) i)
        (Eq.cong enc (E16.rs-sem (wS S) (Coset.coset-even 16 (wS S) (fix-parity (frameL (ts S)))) i))))

γ-cong : {S S′ : Fin 16 → Bool} → (∀ i → S i ≡ S′ i) → ∀ i → γ S ⟨$⟩ʳ i ≡ γ S′ ⟨$⟩ʳ i
γ-cong e i = Eq.cong (λ l → SymI.⟦ fix (frameL l) ⟧ ⟨$⟩ʳ i) (ts-cong e)

------------------------------------------------------------------------
-- The normal form

-- The coordinates: E ∈ Alt(8), B ∈ Sym(8) and an eight-subset S of the
-- sixteen states (in Four's numbering).
record Coords : Set where
  field
    E  : Alt 8
    B  : Permutation′ 8
    S  : Fin 16 → Bool
    S8 : weight S ≡ 8

open Coords public

-- NF(E, B, S) = C(E) D(B) r_S in composition order: r_S first.
NF : Coords → Circuit 4
NF c = r (S c) • (D (B c) • C (E c))

-- The function of the block part: B on H₀, E B on H₁.
blk : Permutation′ 8 → Permutation′ 8 → Bool → Fin 8 → Bits 4
blk E B false p = st false (B ⟨$⟩ʳ p)
blk E B true  p = st true (E ⟨$⟩ʳ (B ⟨$⟩ʳ p))

w3-blk : ∀ E B b p → w3 (blk E B b p) ≡ b
w3-blk E B false p = w3-st false (B ⟨$⟩ʳ p)
w3-blk E B true  p = w3-st true (E ⟨$⟩ʳ (B ⟨$⟩ʳ p))

-- The function of a normal form: r_S, then the blocks.
NF-sem : (c : Coords) (i : Fin 16) →
         ⟦ NF c ⟧ (enc i) ≡ blk (Alt.perm (E c)) (B c) (isHi (γ (S c) ⟨$⟩ʳ i)) (pos4 (γ (S c) ⟨$⟩ʳ i))
NF-sem c i =
  Eq.trans (Eq.cong (λ x → ⟦ D (B c) • C (E c) ⟧ x) (Eq.trans (r-sem (S c) i) (enc-st j)))
    (blocks (isHi j) (pos4 j))
  where
  j = γ (S c) ⟨$⟩ʳ i
  blocks : ∀ b p → ⟦ D (B c) • C (E c) ⟧ (st b p) ≡ blk (Alt.perm (E c)) (B c) b p
  blocks false p = Eq.trans (Eq.cong ⟦ C (E c) ⟧ (D-sem (B c) false p)) (C-low (E c) (B c ⟨$⟩ʳ p))
  blocks true  p = Eq.trans (Eq.cong ⟦ C (E c) ⟧ (D-sem (B c) true p)) (C-high (E c) (B c ⟨$⟩ʳ p))

------------------------------------------------------------------------
-- Uniqueness of the coordinates (the injective half of Proposition 3.3)

private
  not-inj : ∀ {a b} → not a ≡ not b → a ≡ b
  not-inj {false} {false} _ = Eq.refl
  not-inj {true}  {true}  _ = Eq.refl
  not-inj {false} {true}  ()
  not-inj {true}  {false} ()

  w3-NF : (c : Coords) (i : Fin 16) → w3 (⟦ NF c ⟧ (enc i)) ≡ not (S c i)
  w3-NF c i =
    Eq.trans (Eq.cong w3 (NF-sem c i))
      (Eq.trans (w3-blk (Alt.perm (E c)) (B c) (isHi (γ (S c) ⟨$⟩ʳ i)) (pos4 (γ (S c) ⟨$⟩ʳ i)))
                (isHi-γ (S c) (S8 c) i))

  -- At the state that r_S sends to the index of half b, position p.
  NF-at : (c : Coords) (b : Bool) (p : Fin 8) →
          ⟦ NF c ⟧ (enc (γ (S c) ⟨$⟩ˡ idx b p)) ≡ blk (Alt.perm (E c)) (B c) b p
  NF-at c b p =
    Eq.trans (NF-sem c (γ (S c) ⟨$⟩ˡ idx b p))
      (Eq.cong₂ (blk (Alt.perm (E c)) (B c))
        (Eq.trans (Eq.cong isHi (inverseʳ (γ (S c)))) (isHi-idx b p))
        (Eq.trans (Eq.cong pos4 (inverseʳ (γ (S c)))) (pos4-idx b p)))

NF-unique : (c c′ : Coords) → ⟦ NF c ⟧ ≐ ⟦ NF c′ ⟧ →
            (∀ i → S c i ≡ S c′ i) × (∀ p → B c ⟨$⟩ʳ p ≡ B c′ ⟨$⟩ʳ p) ×
            (∀ p → Alt.perm (E c) ⟨$⟩ʳ p ≡ Alt.perm (E c′) ⟨$⟩ʳ p)
NF-unique c c′ e = sameS , sameB , sameE
  where
  sameS : ∀ i → S c i ≡ S c′ i
  sameS i = not-inj (Eq.trans (Eq.sym (w3-NF c i)) (Eq.trans (Eq.cong w3 (e (enc i))) (w3-NF c′ i)))

  -- The two r_S are the same, so are their inverses.
  γ⁻ : ∀ k → γ (S c) ⟨$⟩ˡ k ≡ γ (S c′) ⟨$⟩ˡ k
  γ⁻ k =
    Eq.trans (Eq.sym (inverseˡ (γ (S c′))))
      (Eq.cong (γ (S c′) ⟨$⟩ˡ_)
        (Eq.trans (Eq.sym (γ-cong sameS (γ (S c) ⟨$⟩ˡ k))) (inverseʳ (γ (S c)))))

  blk≡ : ∀ b p → blk (Alt.perm (E c)) (B c) b p ≡ blk (Alt.perm (E c′)) (B c′) b p
  blk≡ b p =
    Eq.trans (Eq.sym (NF-at c b p))
      (Eq.trans (e _) (Eq.trans (Eq.cong (λ k → ⟦ NF c′ ⟧ (enc k)) (γ⁻ (idx b p))) (NF-at c′ b p)))

  sameB : ∀ p → B c ⟨$⟩ʳ p ≡ B c′ ⟨$⟩ʳ p
  sameB p =
    Eq.trans (Eq.sym (pos-st false (B c ⟨$⟩ʳ p)))
      (Eq.trans (Eq.cong pos (blk≡ false p)) (pos-st false (B c′ ⟨$⟩ʳ p)))

  sameE : ∀ p → Alt.perm (E c) ⟨$⟩ʳ p ≡ Alt.perm (E c′) ⟨$⟩ʳ p
  sameE p =
    Eq.trans (Eq.cong (Alt.perm (E c) ⟨$⟩ʳ_) (Eq.sym (inverseʳ (B c))))
      (Eq.trans (Eq.sym (pos-st true _))
        (Eq.trans (Eq.cong pos (blk≡ true q))
          (Eq.trans (pos-st true _)
            (Eq.cong (Alt.perm (E c′) ⟨$⟩ʳ_) (Eq.trans (Eq.sym (sameB q)) (inverseʳ (B c)))))))
    where
    q = B c ⟨$⟩ˡ p

------------------------------------------------------------------------
-- The coordinates of a circuit (the onto half)

module Of (u : Circuit 4) where

  π : Permutation′ (8 + 8)
  π = perm u

  -- The states that u sends into H₀.
  Su : Fin 16 → Bool
  Su i = not (isHi (π ⟨$⟩ʳ i))

  Su8 : weight Su ≡ 8
  Su8 = weight-perm π (λ i → not (isHi i))

  g : Permutation′ 16
  g = γ Su

  half-g : ∀ i → isHi (g ⟨$⟩ʳ i) ≡ not (Su i)
  half-g = isHi-γ Su Su8

  -- u after r_S's inverse preserves the halves.
  q : Fin 16 → Fin 16
  q j = π ⟨$⟩ʳ (g ⟨$⟩ˡ j)

  q⁻ : Fin 16 → Fin 16
  q⁻ j = g ⟨$⟩ʳ (π ⟨$⟩ˡ j)

  q-q⁻ : ∀ j → q (q⁻ j) ≡ j
  q-q⁻ j = Eq.trans (Eq.cong (π ⟨$⟩ʳ_) (inverseˡ g)) (inverseʳ π)

  q⁻-q : ∀ j → q⁻ (q j) ≡ j
  q⁻-q j = Eq.trans (Eq.cong (g ⟨$⟩ʳ_) (inverseˡ π)) (inverseʳ g)

  q-half : ∀ j → isHi (q j) ≡ isHi j
  q-half j =
    Eq.trans (Eq.sym (not-involutive (isHi (q j))))
      (Eq.trans (Eq.sym (half-g (g ⟨$⟩ˡ j))) (Eq.cong isHi (inverseʳ g)))

  q⁻-half : ∀ j → isHi (q⁻ j) ≡ isHi j
  q⁻-half j =
    Eq.trans (half-g (π ⟨$⟩ˡ j))
      (Eq.trans (not-involutive (isHi (π ⟨$⟩ʳ (π ⟨$⟩ˡ j)))) (Eq.cong isHi (inverseʳ π)))

  -- An index of half b is the index of its position.
  back : ∀ b j → isHi j ≡ b → idx b (pos4 j) ≡ j
  back b j e = Eq.trans (Eq.cong (λ b′ → idx b′ (pos4 j)) (Eq.sym e)) (idx-isHi j)

  -- The blocks.
  bF : Bool → Fin 8 → Fin 8
  bF b p = pos4 (q (idx b p))

  bG : Bool → Fin 8 → Fin 8
  bG b p = pos4 (q⁻ (idx b p))

  bF-bG : ∀ b p → bF b (bG b p) ≡ p
  bF-bG b p =
    Eq.trans (Eq.cong (λ j → pos4 (q j)) (back b (q⁻ (idx b p)) (Eq.trans (q⁻-half (idx b p)) (isHi-idx b p))))
      (Eq.trans (Eq.cong pos4 (q-q⁻ (idx b p))) (pos4-idx b p))

  bG-bF : ∀ b p → bG b (bF b p) ≡ p
  bG-bF b p =
    Eq.trans (Eq.cong (λ j → pos4 (q⁻ j)) (back b (q (idx b p)) (Eq.trans (q-half (idx b p)) (isHi-idx b p))))
      (Eq.trans (Eq.cong pos4 (q⁻-q (idx b p))) (pos4-idx b p))

  Bb : Bool → Permutation′ 8
  Bb b = permutation (bF b) (bG b) (bF-bG b) (bG-bF b)

  B0 B1 : Permutation′ 8
  B0 = Bb false
  B1 = Bb true

  -- E = B₁ B₀⁻¹ in composition order.
  Ep : Permutation′ 8
  Ep = flip B0 ∘ₚ B1

  -- E is even: the circuit D(B₀⁻¹), then r_S reversed, then u, is the
  -- identity on H₀ and E on H₁.
  v : Circuit 4
  v = D (flip B0) • (revC (r Su) • u)

  rinv : ∀ j → ⟦ revC (r Su) ⟧ (enc j) ≡ enc (g ⟨$⟩ˡ j)
  rinv j =
    Eq.trans (Eq.cong ⟦ revC (r Su) ⟧ (Eq.trans (Eq.cong enc (Eq.sym (inverseʳ g))) (Eq.sym (r-sem Su (g ⟨$⟩ˡ j)))))
      (revC-sem (r Su) (enc (g ⟨$⟩ˡ j)))

  v-at : ∀ b p → ⟦ v ⟧ (st b p) ≡ enc (q (idx b (bG false p)))
  v-at b p =
    Eq.trans (Eq.cong (λ x → ⟦ u ⟧ (⟦ revC (r Su) ⟧ x)) (Eq.trans (D-sem (flip B0) b p) (Eq.sym (enc-idx b (bG false p)))))
      (Eq.trans (Eq.cong ⟦ u ⟧ (rinv (idx b (bG false p)))) (at u (g ⟨$⟩ˡ idx b (bG false p))))

  v-lo : ∀ p → perm v ⟨$⟩ʳ (idx false p) ≡ idx false p
  v-lo p =
    Eq.trans (perm-at v (idx false p))
      (Eq.trans (Eq.cong (λ x → dec (⟦ v ⟧ x)) (enc-idx false p))
        (Eq.trans (Eq.cong dec (v-at false p))
          (Eq.trans (dec-enc _)
            (Eq.trans (Eq.cong q (back false (q⁻ (idx false p)) (Eq.trans (q⁻-half (idx false p)) (isHi-idx false p))))
              (q-q⁻ (idx false p))))))

  v-hi : ∀ p → perm v ⟨$⟩ʳ (idx true p) ≡ idx true (Ep ⟨$⟩ʳ p)
  v-hi p =
    Eq.trans (perm-at v (idx true p))
      (Eq.trans (Eq.cong (λ x → dec (⟦ v ⟧ x)) (enc-idx true p))
        (Eq.trans (Eq.cong dec (v-at true p))
          (Eq.trans (dec-enc _)
            (Eq.sym (back true (q (idx true (bG false p)))
                       (Eq.trans (q-half (idx true (bG false p))) (isHi-idx true (bG false p))))))))

  e-lift : ∀ i → SymI.⟦ tr v ⟧ ⟨$⟩ʳ i ≡ CF.liftN 8 (rev8 ∘ₚ (Ep ∘ₚ rev8)) ⟨$⟩ʳ i
  e-lift ₀ = v-lo ₀
  e-lift ₁ = v-lo ₁
  e-lift ₂ = v-lo ₂
  e-lift ₃ = v-lo ₃
  e-lift ₄ = v-lo ₄
  e-lift ₅ = v-lo ₅
  e-lift ₆ = v-lo ₆
  e-lift ₇ = v-lo ₇
  e-lift ₈ = Eq.trans (v-hi ₇) (hi-lift (Ep ⟨$⟩ʳ ₇))
  e-lift ₉ = Eq.trans (v-hi ₆) (hi-lift (Ep ⟨$⟩ʳ ₆))
  e-lift ₁₀ = Eq.trans (v-hi ₅) (hi-lift (Ep ⟨$⟩ʳ ₅))
  e-lift ₁₁ = Eq.trans (v-hi ₄) (hi-lift (Ep ⟨$⟩ʳ ₄))
  e-lift ₁₂ = Eq.trans (v-hi ₃) (hi-lift (Ep ⟨$⟩ʳ ₃))
  e-lift ₁₃ = Eq.trans (v-hi ₂) (hi-lift (Ep ⟨$⟩ʳ ₂))
  e-lift ₁₄ = Eq.trans (v-hi ₁) (hi-lift (Ep ⟨$⟩ʳ ₁))
  e-lift ₁₅ = Eq.trans (v-hi ₀) (hi-lift (Ep ⟨$⟩ʳ ₀))

  Ep-even : sign Ep ≡ false
  Ep-even = Lift.lift-sign 8 8 (tr v) (parity-tr v) rev8 Ep e-lift

  coords : Coords
  coords = record { E = record { perm = Ep ; even = Ep-even } ; B = B0 ; S = Su ; S8 = Su8 }

  -- The normal form of the coordinates denotes u.
  NF-enc : ∀ i → ⟦ NF coords ⟧ (enc i) ≡ enc (π ⟨$⟩ʳ i)
  NF-enc i =
    Eq.trans (NF-sem coords i)
      (Eq.trans (by-half (isHi j) Eq.refl) (Eq.cong (λ k → enc (π ⟨$⟩ʳ k)) (inverseˡ g)))
    where
    j = g ⟨$⟩ʳ i
    by-half : (b : Bool) → isHi j ≡ b → blk Ep B0 b (pos4 j) ≡ enc (q j)
    by-half false e =
      Eq.trans (Eq.cong (λ k → st false (pos4 (q k))) (back false j e))
        (Eq.sym (Eq.trans (enc-st (q j)) (Eq.cong (λ b → st b (pos4 (q j))) (Eq.trans (q-half j) e))))
    by-half true e =
      Eq.trans (Eq.cong (λ y → st true (bF true y)) (bG-bF false (pos4 j)))
        (Eq.trans (Eq.cong (λ k → st true (pos4 (q k))) (back true j e))
          (Eq.sym (Eq.trans (enc-st (q j)) (Eq.cong (λ b → st b (pos4 (q j))) (Eq.trans (q-half j) e)))))

  NF-u : ⟦ NF coords ⟧ ≐ ⟦ u ⟧
  NF-u x =
    Eq.trans (Eq.cong ⟦ NF coords ⟧ (Eq.sym (enc-dec x)))
      (Eq.trans (NF-enc (dec x)) (Eq.trans (Eq.sym (at u (dec x))) (Eq.cong ⟦ u ⟧ (enc-dec x))))

coords : Circuit 4 → Coords
coords = Of.coords

------------------------------------------------------------------------
-- The theorems

-- Every four-wire circuit rewrites to the normal form of its
-- coordinates (the main theorem's normal form)...
normal-form : (u : Circuit 4) → 4 ⊢ u ≈ NF (coords u)
normal-form u = complete₄ (λ x → Eq.sym (Of.NF-u u x))

-- ... and to no other: the coordinates are unique.
unique : (u : Circuit 4) (c : Coords) → 4 ⊢ u ≈ NF c →
         (∀ i → S c i ≡ S (coords u) i) × (∀ p → B c ⟨$⟩ʳ p ≡ B (coords u) ⟨$⟩ʳ p) ×
         (∀ p → Alt.perm (E c) ⟨$⟩ʳ p ≡ Alt.perm (E (coords u)) ⟨$⟩ʳ p)
unique u c e = NF-unique c (coords u) (λ x → Eq.trans (Eq.sym (sound e x)) (sound (normal-form u) x))

-- Proposition 3.3, the semantic bijection
-- Alt(8) × Sym(8) × (eight-subsets) → Alt(16): injective (NF-unique)
-- and onto, every even permutation of the sixteen states being the
-- function of a normal form.
NF-onto : (a : Alt 16) → Σ Coords (λ c → ∀ i → ⟦ NF c ⟧ (enc i) ≡ enc (Alt.perm a ⟨$⟩ʳ i))
NF-onto a = coords (Groups.Fourw.circᴬ a) , λ i →
  Eq.trans (sound (PB.sym (normal-form (Groups.Fourw.circᴬ a))) (enc i)) (Groups.Fourw.circᴬ-sem a i)

-- The paper's check of the count: (16 choose 8) · 8! · 8!/2 = 16!/2.
count : 12870 * (8 ! * (8 ! / 2)) ≡ 16 ! / 2
count = Eq.refl

------------------------------------------------------------------------
-- Theorem 5.1: gate absorption

-- For any circuit w (in particular one of the 28 placed gates), w
-- followed by NF(E, B, S) (in composition order NF(E, B, S) w) is the
-- normal form of absorb c w; its coordinates are the paper's update
-- S′ = w⁻¹ S, B′ = B A₀ and E′ = E B A₁ A₀⁻¹ B⁻¹, where R = r_S w r_S′⁻¹
-- preserves the halves with blocks A₀, A₁.
absorb : Coords → Circuit 4 → Coords
absorb c w = coords (w • NF c)

absorption : (c : Coords) (w : Circuit 4) → 4 ⊢ w • NF c ≈ NF (absorb c w)
absorption c w = normal-form (w • NF c)

module Absorb (c : Coords) (w : Circuit 4) where

  private
    module O = Of (w • NF c)

  c′ : Coords
  c′ = absorb c w

  -- The state that w sends the numbered state i to.
  wk : Fin 16 → Fin 16
  wk i = dec (⟦ w ⟧ (enc i))

  private
    EB : Fin 8 → Fin 8
    EB p = Alt.perm (E c) ⟨$⟩ʳ (B c ⟨$⟩ʳ p)

  private
    NF-w : ∀ i → O.π ⟨$⟩ʳ i ≡ dec (⟦ NF c ⟧ (enc (wk i)))
    NF-w i = Eq.trans (perm-at (w • NF c) i) (Eq.cong (λ x → dec (⟦ NF c ⟧ x)) (Eq.sym (enc-dec (⟦ w ⟧ (enc i)))))

  -- S′ = w⁻¹ S.
  absorb-S : ∀ i → S c′ i ≡ S c (wk i)
  absorb-S i =
    Eq.trans (Eq.cong (λ k → not (isHi k)) (NF-w i))
      (Eq.trans (Eq.cong (λ x → not (isHi (dec x))) (NF-sem c (wk i)))
        (Eq.trans (Eq.cong not (half-dec _ _))
          (Eq.trans (Eq.cong not (isHi-γ (S c) (S8 c) (wk i))) (not-involutive (S c (wk i))))))
    where
    half-dec : ∀ b p → isHi (dec (blk (Alt.perm (E c)) (B c) b p)) ≡ b
    half-dec false p = Eq.trans (Eq.cong isHi (dec-st false (B c ⟨$⟩ʳ p))) (isHi-idx false (B c ⟨$⟩ʳ p))
    half-dec true  p = Eq.trans (Eq.cong isHi (dec-st true (EB p))) (isHi-idx true (EB p))

  -- R = r_S w r_S′⁻¹ (in composition order) on the numbered states.
  R : Fin 16 → Fin 16
  R j = γ (S c) ⟨$⟩ʳ wk (γ (S c′) ⟨$⟩ˡ j)

  R-half : ∀ j → isHi (R j) ≡ isHi j
  R-half j =
    Eq.trans (isHi-γ (S c) (S8 c) (wk y))
      (Eq.trans (Eq.cong not (Eq.sym (absorb-S y)))
        (Eq.trans (Eq.sym (isHi-γ (S c′) (S8 c′) y)) (Eq.cong isHi (inverseʳ (γ (S c′))))))
    where
    y = γ (S c′) ⟨$⟩ˡ j

  -- Its blocks.
  A : Bool → Fin 8 → Fin 8
  A b p = pos4 (R (idx b p))

  private
    q-R : ∀ b p → O.q (idx b p) ≡ dec (blk (Alt.perm (E c)) (B c) b (A b p))
    q-R b p =
      Eq.trans (NF-w (γ (S c′) ⟨$⟩ˡ idx b p))
        (Eq.trans (Eq.cong dec (NF-sem c (wk (γ (S c′) ⟨$⟩ˡ idx b p))))
          (Eq.cong (λ b′ → dec (blk (Alt.perm (E c)) (B c) b′ (A b p))) (Eq.trans (R-half (idx b p)) (isHi-idx b p))))

    pos-blk : ∀ b p → pos4 (dec (blk (Alt.perm (E c)) (B c) b p)) ≡ pos (blk (Alt.perm (E c)) (B c) b p)
    pos-blk false p = Eq.trans (Eq.cong pos4 (dec-st false (B c ⟨$⟩ʳ p))) (Eq.trans (pos4-idx false (B c ⟨$⟩ʳ p)) (Eq.sym (pos-st false (B c ⟨$⟩ʳ p))))
    pos-blk true  p = Eq.trans (Eq.cong pos4 (dec-st true (EB p))) (Eq.trans (pos4-idx true (EB p)) (Eq.sym (pos-st true (EB p))))

  -- B′ = B A₀.
  absorb-B : ∀ p → B c′ ⟨$⟩ʳ p ≡ B c ⟨$⟩ʳ (A false p)
  absorb-B p =
    Eq.trans (Eq.cong pos4 (q-R false p)) (Eq.trans (pos-blk false (A false p)) (pos-st false (B c ⟨$⟩ʳ A false p)))

  -- E′ B′ = E B A₁, i.e. E′ = E B A₁ A₀⁻¹ B⁻¹.
  absorb-E : ∀ p → Alt.perm (E c′) ⟨$⟩ʳ (B c′ ⟨$⟩ʳ p) ≡ Alt.perm (E c) ⟨$⟩ʳ (B c ⟨$⟩ʳ (A true p))
  absorb-E p =
    Eq.trans (Eq.cong (O.bF true) (O.bG-bF false p))
      (Eq.trans (Eq.cong pos4 (q-R true p)) (Eq.trans (pos-blk true (A true p)) (pos-st true (EB (A true p)))))
