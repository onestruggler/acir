{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The three-wire layer of the Paper-V0 calculus, over any family of
-- relations: the remote CZ, Paper-V0's yang-baxter and cz-slide as
-- theorems, and Selinger's c12–c15.
--
-- Three-Wire-Calculus takes the family and a Three-Wire-Rules record:
-- the Two-Wire-Rules, one of Paper-V0's three three-wire rules
-- (semi-CX↑-CZ↓), and the structural rule for a two-wire gate against a
-- word shifted two wires up (comm₂).  The other two three-wire rules,
-- yang-baxter and cz-slide, it derives (Three-Wire.lemma-yang-baxter,
-- lemma-cz-slide).  Paper-V0.Lemmas instantiates it at Paper-V0, which
-- keeps both as axioms; Reduced, through Paper-V1.Lemmas.V0Rules, at a
-- rule set that has neither.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ<)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.ThreeWire
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- The words only, as in OneWire.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
  using ( Z ; X ; Z⁻¹ ; X⁻¹ ; Z^ ; X^ ; R ; R^ ; RHR ; M ; XM ; XM≡M⁻¹
        ; M₁ ; M₋₁ ; Mg ; Mg^ ; XMg ; XMg^ )
-- _↑ commuting with a power; relation-free, so Paper-V0's serves.
open Lemmas-Clifford using (lemma-↑^)

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.OneWire
  p-3 p-prime g* g-gen as OW
open OW using (lemma-pow-mod ; lemma-Induction ; lemma-Inductionˡ)
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.TwoWire
  p-3 p-prime g* g-gen as TW
open import Examples.Groups.ProjectiveClifford.Qupit.Shared.Conjugation
  using (module Conjugation)

------------------------------------------------------------------------
-- Three pieces of group theory
--
-- Three-Wire derives cz-slide and yang-baxter.  The argument has a
-- half about the gates — how the swaps, CX ↑ and the multipliers act on
-- the CZs of three wires — and a half that is pure group theory, stated
-- here over abstract words in any group-like relation.

-- A word whose square and whose p-th power are ε is ε, p being odd: it
-- is its own (2 · ½)-th power.
module Odd {G : Set} (Δ : WRel G) where

  open PB Δ hiding (_===_)
  open PP Δ
  open SR word-setoid

  sq⇒ε : ∀ {x : Word G} → x ^ p ≈ ε → x • x ≈ ε → x ≈ ε
  sq⇒ε {x} xᵖ xx = begin
    x                                ≡⟨ Eq.cong (x ^_) (Eq.sym (Eq.cong toℕ two)) ⟩
    x ^ toℕ (2ₚ * 1/2)               ≡⟨ Eq.cong (x ^_) (Eq.sym (lemma-toℕ-% 2ₚ 1/2)) ⟩
    x ^ ((2 Nat.* toℕ 1/2) Nat.% p)  ≈⟨ sym (lemma-pow-mod xᵖ (2 Nat.* toℕ 1/2)) ⟩
    x ^ (2 Nat.* toℕ 1/2)            ≈⟨ sym (^^ x 2 (toℕ 1/2)) ⟩
    (x ^ 2) ^ toℕ 1/2                ≈⟨ ^-cong (x ^ 2) ε (toℕ 1/2) xx ⟩
    ε ^ toℕ 1/2                      ≈⟨ ε^k=ε (toℕ 1/2) ⟩
    ε ∎
    where
    2ₚ : ℤ ₚ
    2ₚ = ₂

    two : 2ₚ * 1/2 ≡ ₁
    two = Eq.trans (*-comm 2ₚ 1/2)
            (lemma-⁻¹ˡ 2ₚ {{nztoℕ {y = 2ₚ} {neq0 = λ ()}}})

-- A commutation forced by rescaling: the progress report's Lemma 9, as
-- lemma-comm-CZ-CZ02 proves it, over abstract words.  If conjugating by
-- A sends B to x • y, and a word m commutes with A while m ^ j rescales
-- B, x and y alike by e = g ^′ j, then (x • y) ^ e ≈ x ^ e • y ^ e.
-- Some power of g is 2, and there that says x and y commute.
module Rescale
  {G : Set} (Δ : WRel G) (gl : Grouplike Δ)
  (A B x y m : Word G)
  (A-B : let open Conjugation Δ gl in Conj A B (x • y))
  (m-A : let open Conjugation Δ gl in ∀ j → Conj (m ^ j) A A)
  (m-B : let open Conjugation Δ gl in
         ∀ j → Conj (m ^ j) B (B ^ toℕ (g ^′ j)))
  (m-x : let open Conjugation Δ gl in
         ∀ j → Conj (m ^ j) x (x ^ toℕ (g ^′ j)))
  (m-y : let open Conjugation Δ gl in
         ∀ j → Conj (m ^ j) y (y ^ toℕ (g ^′ j)))
  where

  open PB Δ hiding (_===_)
  open PP Δ
  open SR word-setoid
  open Conjugation Δ gl
  open Group-Lemmas Δ gl using (•-cancelˡ ; •-cancelʳ)

  private
    2ₚ : ℤ ₚ
    2ₚ = ₂

    -- The power of g that is 2.
    j₂ : ℕ
    j₂ = toℕ (g-gen (2ₚ , λ ()) .proj₁)

    e₂ : toℕ (g ^′ j₂) ≡ 2
    e₂ = Eq.cong toℕ (Eq.sym (g-gen (2ₚ , λ ()) .proj₂))

    -- A-B rescaled: m ^ j carries it to the exponent e.
    rescaled : ∀ j → let e = toℕ (g ^′ j) in Conj A (B ^ e) (x ^ e • y ^ e)
    rescaled j = conj-unique
      (conj-cong A-B refl (conj-• (m-A j) (m-B j)))
      (conj-• (conj-• (m-x j) (m-y j)) (m-A j))

    distribute : ∀ j → let e = toℕ (g ^′ j) in (x • y) ^ e ≈ x ^ e • y ^ e
    distribute j = conj-unique (conj-^ A-B (toℕ (g ^′ j))) (rescaled j)

    square : (x • y) • (x • y) ≈ (x • x) • (y • y)
    square = Eq.subst (λ e → (x • y) ^ e ≈ x ^ e • y ^ e) e₂ (distribute j₂)

  comm : x • y ≈ y • x
  comm = sym (•-cancelʳ {h = y} (•-cancelˡ {g = x} (begin
    x • ((y • x) • y)   ≈⟨ by-assoc' ⟩
    (x • y) • (x • y)   ≈⟨ square ⟩
    (x • x) • (y • y)   ≈⟨ by-assoc'' ⟩
    x • ((x • y) • y) ∎)))
    where
    by-assoc' : x • ((y • x) • y) ≈ (x • y) • (x • y)
    by-assoc' = trans (cright assoc) (sym assoc)

    by-assoc'' : (x • x) • (y • y) ≈ x • ((x • y) • y)
    by-assoc'' = trans assoc (cright sym assoc)

-- The swap argument.  Let a and b be involutions whose braids a • b • a
-- and b • a • b are the same word e, and let c and d be commuting words
-- of order p, with inverses c' and d'.  If b fixes c, a fixes d, a sends
-- c to d' • c', and e sends c • d' to c' • d, then e sends c to d.
--
-- At three wires a and b are the half-swaps on wires 1-2, e = Ex ↑,
-- c = CZ and d = CZ02, and the conclusion is cz-slide.  The proof: let
-- Ω' be b's image of d', and V' e's image of d'.  Reading e as
-- b • a • b and as a • b • a sends c to Ω' • c' and to V' • c • d, and
-- d' to two images of V' that differ by b; together these make c', d'
-- and Ω' commute.  The hypothesis on c • d' then says that
-- x = Ω' • c' • d' squares to ε; x has order p, so x is ε, and Ω' • c',
-- e's image of c, is d.
module Swap-Argument
  {G : Set} (Δ : WRel G) (gl : Grouplike Δ)
  (a b c c' d d' e : Word G)
  (aa    : let open PB Δ in a • a ≈ ε)
  (bb    : let open PB Δ in b • b ≈ ε)
  (e-bab : let open PB Δ in e ≈ b • (a • b))
  (e-aba : let open PB Δ in e ≈ a • (b • a))
  (cc'   : let open PB Δ in c • c' ≈ ε)
  (c'c   : let open PB Δ in c' • c ≈ ε)
  (dd'   : let open PB Δ in d • d' ≈ ε)
  (d'd   : let open PB Δ in d' • d ≈ ε)
  (cᵖ    : let open PB Δ in c ^ p ≈ ε)
  (dᵖ    : let open PB Δ in d ^ p ≈ ε)
  (c-d   : let open Conjugation Δ gl in Conj c d d)
  (b-c   : let open Conjugation Δ gl in Conj b c c)
  (a-d   : let open Conjugation Δ gl in Conj a d d)
  (a-c   : let open Conjugation Δ gl in Conj a c (d' • c'))
  (e-cd' : let open Conjugation Δ gl in Conj e (c • d') (c' • d))
  where

  open PB Δ hiding (_===_)
  open PP Δ
  open SR word-setoid
  open Pattern-Assoc
  open Conjugation Δ gl
  open Group-Lemmas Δ gl using (•-cancelˡ ; •-cancelʳ)
  open Odd Δ using (sq⇒ε)

  private
    -- Inverses carried along.
    c-d' : Conj c d' d'
    c-d' = conj-inv-u dd' d'd c-d

    c'-d' : Conj c' d' d'
    c'-d' = comm-sym (conj-inv-u cc' c'c (comm-sym c-d'))

    b-c' : Conj b c' c'
    b-c' = conj-inv-u cc' c'c b-c

    a-d' : Conj a d' d'
    a-d' = conj-inv-u dd' d'd a-d

    a-c' : Conj a c' (c • d)
    a-c' = conj-inv-u cc' (tele dd' cc') a-c

    -- The images of d' under b, and then under a.
    Ω' : Word G
    Ω' = b • (d' • b)

    V' : Word G
    V' = a • (Ω' • a)

    b-d' : Conj b d' Ω'
    b-d' = conj-lit bb

    b-Ω' : Conj b Ω' d'
    b-Ω' = conj-lit' bb

    a-Ω' : Conj a Ω' V'
    a-Ω' = conj-lit aa

    -- e read as b • a • b, and as a • b • a.
    e-c : Conj e c (Ω' • c')
    e-c = conj-congˡ (sym e-bab)
            (conj-∘ (conj-∘ b-c a-c) (conj-• b-d' b-c'))

    e-c-aba : Conj e c (V' • (c • d))
    e-c-aba = conj-congˡ (sym e-aba)
                (conj-∘ (conj-∘ a-c (conj-• b-d' b-c')) (conj-• a-Ω' a-c'))

    e-d' : Conj e d' V'
    e-d' = conj-congˡ (sym e-aba) (conj-∘ (conj-∘ a-d' b-d') a-Ω')

    e-d'-bab : Conj e d' (b • (V' • b))
    e-d'-bab = conj-congˡ (sym e-bab) (conj-∘ (conj-∘ b-d' a-Ω') (conj-lit bb))

    R1 : Ω' • c' ≈ V' • (c • d)
    R1 = conj-unique e-c e-c-aba

    -- V' is fixed by b.
    b-V' : Conj b V' V'
    b-V' = trans (cright conj-unique e-d' e-d'-bab) (cancel-• bb)

    V'≈ : V' ≈ (Ω' • c') • (d' • c')
    V'≈ = begin
      V'                           ≈⟨ sym right-unit ⟩
      V' • ε                       ≈⟨ cright sym (tele dd' cc') ⟩
      V' • ((c • d) • (d' • c'))   ≈⟨ sym assoc ⟩
      (V' • (c • d)) • (d' • c')   ≈⟨ cleft sym R1 ⟩
      (Ω' • c') • (d' • c') ∎

    -- c commutes with Ω': b's image of c commuting with d'.
    c-Ω' : Conj c Ω' Ω'
    c-Ω' = conj-unique (conj-cong c-d' refl (conj-• b-c b-d'))
             (conj-• b-d' b-c)

    c'-Ω' : Conj c' Ω' Ω'
    c'-Ω' = comm-sym (conj-inv-u cc' c'c (comm-sym c-Ω'))

    -- d' commutes with Ω': b fixes V' and exchanges d' and Ω'.
    R4 : (Ω' • c') • (d' • c') ≈ (d' • c') • (Ω' • c')
    R4 = conj-unique (conj-cong V'≈ V'≈ b-V')
           (conj-• (conj-• b-Ω' b-c') (conj-• b-d' b-c'))

    R5 : (Ω' • c') • d' ≈ (d' • c') • Ω'
    R5 = •-cancelʳ {h = c'} (begin
      ((Ω' • c') • d') • c'   ≈⟨ assoc ⟩
      (Ω' • c') • (d' • c')   ≈⟨ R4 ⟩
      (d' • c') • (Ω' • c')   ≈⟨ sym assoc ⟩
      ((d' • c') • Ω') • c' ∎)

    d'-Ω' : Conj d' Ω' Ω'
    d'-Ω' = sym (•-cancelʳ {h = c'} (begin
      (Ω' • d') • c'   ≈⟨ assoc ⟩
      Ω' • (d' • c')   ≈⟨ cright sym c'-d' ⟩
      Ω' • (c' • d')   ≈⟨ sym assoc ⟩
      (Ω' • c') • d'   ≈⟨ R5 ⟩
      (d' • c') • Ω'   ≈⟨ assoc ⟩
      d' • (c' • Ω')   ≈⟨ cright c'-Ω' ⟩
      d' • (Ω' • c')   ≈⟨ sym assoc ⟩
      (d' • Ω') • c' ∎))

    -- The hypothesis on c • d', with e read as b • a • b on c and as
    -- a • b • a on d'.
    R2 : (Ω' • c') • V' ≈ c' • d
    R2 = conj-unique (conj-• e-c e-d') e-cd'

    x : Word G
    x = Ω' • (c' • d')

    x•x : x • x ≈ ε
    x•x = begin
      x • x
        ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • □)))
                     (□ • (□ • ((□ • □) • (□ • □)))) auto ⟩
      Ω' • (c' • ((d' • Ω') • (c' • d')))
        ≈⟨ cright cright cleft d'-Ω' ⟩
      Ω' • (c' • ((Ω' • d') • (c' • d')))
        ≈⟨ cright cright by-passoc ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) auto ⟩
      Ω' • (c' • (Ω' • ((d' • c') • d')))
        ≈⟨ cright cright cright cleft sym c'-d' ⟩
      Ω' • (c' • (Ω' • ((c' • d') • d')))
        ≈⟨ cright cright cright assoc ⟩
      Ω' • (c' • (Ω' • (c' • (d' • d'))))
        ≈⟨ cright cright cright cright cright sym right-unit ⟩
      Ω' • (c' • (Ω' • (c' • (d' • (d' • ε)))))
        ≈⟨ cright cright cright cright cright cright sym c'c ⟩
      Ω' • (c' • (Ω' • (c' • (d' • (d' • (c' • c))))))
        ≈⟨ cright cright cright cright cright sym assoc ⟩
      Ω' • (c' • (Ω' • (c' • (d' • ((d' • c') • c)))))
        ≈⟨ cright cright cright cright cright cleft sym c'-d' ⟩
      Ω' • (c' • (Ω' • (c' • (d' • ((c' • d') • c)))))
        ≈⟨ by-passoc (□ • (□ • (□ • (□ • (□ • ((□ • □) • □))))))
                     (((□ • □) • ((□ • □) • (□ • □))) • (□ • □)) auto ⟩
      ((Ω' • c') • ((Ω' • c') • (d' • c'))) • (d' • c)
        ≈⟨ cleft cright sym V'≈ ⟩
      ((Ω' • c') • V') • (d' • c)
        ≈⟨ cleft R2 ⟩
      (c' • d) • (d' • c)
        ≈⟨ tele dd' c'c ⟩
      ε ∎

    -- x has order p: its three factors commute and each has order p.
    inv-order : ∀ {u u'} → u • u' ≈ ε → u' • u ≈ ε → u ^ p ≈ ε → u' ^ p ≈ ε
    inv-order {u} {u'} uu' u'u uᵖ = begin
      u' ^ p              ≈⟨ sym right-unit ⟩
      u' ^ p • ε          ≈⟨ cright sym uᵖ ⟩
      u' ^ p • u ^ p      ≈⟨ sym (^-• u' u p (trans u'u (sym uu'))) ⟩
      (u' • u) ^ p        ≈⟨ ^-cong (u' • u) ε p u'u ⟩
      ε ^ p               ≈⟨ ε^k=ε p ⟩
      ε ∎

    Ω'ᵖ : Ω' ^ p ≈ ε
    Ω'ᵖ = •-cancelʳ {h = b} (begin
      Ω' ^ p • b      ≈⟨ sym (conj-^ b-d' p) ⟩
      b • d' ^ p      ≈⟨ cright inv-order dd' d'd dᵖ ⟩
      b • ε           ≈⟨ right-unit ⟩
      b               ≈⟨ sym left-unit ⟩
      ε • b ∎)

    xᵖ : x ^ p ≈ ε
    xᵖ = begin
      (Ω' • (c' • d')) ^ p
        ≈⟨ ^-• Ω' (c' • d') p (conj-• (comm-sym c'-Ω') (comm-sym d'-Ω')) ⟩
      Ω' ^ p • (c' • d') ^ p
        ≈⟨ cright ^-• c' d' p c'-d' ⟩
      Ω' ^ p • (c' ^ p • d' ^ p)
        ≈⟨ cong Ω'ᵖ (cong (inv-order cc' c'c cᵖ) (inv-order dd' d'd dᵖ)) ⟩
      ε • (ε • ε)
        ≈⟨ trans left-unit left-unit ⟩
      ε ∎

    Ω'c'≈d : Ω' • c' ≈ d
    Ω'c'≈d = begin
      Ω' • c'                ≈⟨ sym right-unit ⟩
      (Ω' • c') • ε          ≈⟨ cright sym d'd ⟩
      (Ω' • c') • (d' • d)   ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • (□ • □)) • □) auto ⟩
      (Ω' • (c' • d')) • d   ≈⟨ cleft sq⇒ε xᵖ x•x ⟩
      ε • d                  ≈⟨ left-unit ⟩
      d ∎

  swap : Conj e c d
  swap = conj-cong refl Ω'c'≈d e-c

------------------------------------------------------------------------
-- The rules
--
-- M₋₁ is a parameter for the reason OneWire gives, fixed by
-- Three-Wire-Rules.

record Three-Wire-Rules-At (Γ : (n : ℕ) → WRel (Gen n))
                           (m₋₁ : ∀ {n} → Word (Gen (₁₊ n))) : Set where
  field
    two-wire     : TW.Two-Wire-Rules-At Γ m₋₁
    semi-CX↑-CZ↓ : ∀ {n} → let open PB (Γ (₃₊ n)) in
                    CZ ↓ • CX ↑ ≈ CZ02 • CX ↑ • CZ ↓
    comm₂       : ∀ {n} (h : SympGate 2) (x : Gen (₁₊ n)) →
                   let open PB (Γ (₃₊ n)) in
                   [ x ↥ ↥ ]ʷ • [ gate₂ h ]ʷ ≈ [ gate₂ h ]ʷ • [ x ↥ ↥ ]ʷ

  open TW.Two-Wire-Rules-At two-wire public

Three-Wire-Rules : ((n : ℕ) → WRel (Gen n)) → Set
Three-Wire-Rules Γ = Three-Wire-Rules-At Γ M₋₁

module Three-Wire-Calculus
  (Γ     : (n : ℕ) → WRel (Gen n))
  (rules : Three-Wire-Rules Γ)
  where

  open Three-Wire-Rules-At rules

  -- The two-wire layer, re-exported: a client of this module sees the
  -- whole calculus.
  open TW.Two-Wire-Calculus Γ two-wire public

  ------------------------------------------------------------------------
  -- The structural commutation of CZ with a word two wires up

  comm-CZ : ∀ {n} {x : Gen (₁₊ n)} →
            PB._≈_ (Γ (₃₊ n)) ([ x ↥ ↥ ]ʷ • CZ) (CZ • [ x ↥ ↥ ]ʷ)
  comm-CZ {x = x} = comm₂ CZ-gate x

  lemma-comm-CZ-w↑ : ∀ {n} w → let open PB (Γ (₃₊ n)) in
    
    CZ • w ↑ ↑ ≈ w ↑ ↑ • CZ
    
  lemma-comm-CZ-w↑ {n} [ x ]ʷ = sym (comm-CZ)
    where
    open PB (Γ (₃₊ n))
  lemma-comm-CZ-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB (Γ (₃₊ n))
  lemma-comm-CZ-w↑ {n} (w • w₁) = begin
    CZ • ((w • w₁) ↑ ↑) ≈⟨ refl ⟩
    CZ • (w ↑ ↑ • w₁ ↑ ↑) ≈⟨ sym assoc ⟩
    (CZ • w ↑ ↑) • w₁ ↑ ↑ ≈⟨ cong (lemma-comm-CZ-w↑ w) refl ⟩
    (w ↑ ↑ • CZ) • w₁ ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • CZ • w₁ ↑ ↑ ≈⟨ cong refl (lemma-comm-CZ-w↑ w₁) ⟩
    w ↑ ↑ • w₁ ↑ ↑ • CZ ≈⟨ sym assoc ⟩
    ((w • w₁) ↑ ↑) • CZ ∎
    where
    open PB (Γ (₃₊ n))
    open PP (Γ (₃₊ n))
    open SR word-setoid

  ------------------------------------------------------------------------
  -- The remote CZ, at three wires
  --
  -- CZ02 is *defined* as Ex • CZ ↑ • Ex — the CZ on wires 1-2 carried onto
  -- wires 0-2 by the swap of wires 0-1 — so conjugation facts about it are
  -- definitional, and its order follows from the order of CZ.
  --
  -- This is the correction term of the paper's C18
  -- (semi-CX↑-CZ↓ : CX ↑ • CZ ↓ === CZ ↓ • CZ02 • CX ↑): CX ↑ retargets
  -- wire 1, which is what a CZ on wires 0-1 reads, so pushing that CZ
  -- through picks up a CZ on wires 0-2.  Deriving selinger-c12 turns on
  -- those corrections cancelling, and they cancel because CX ↑ occurs in
  -- the C6-expansion of a CZ with total exponent 1 + (p-1) = p, leaving
  -- CZ02 ^ p ≈ ε.

  module Three-Wire (n : ℕ) where

    open PB (Γ (₃₊ n))
    open PP (Γ (₃₊ n))
    open SR word-setoid
    open Ex-Conjugation (₁₊ n)


    open Group-Lemmas (Γ (₃₊ n)) (Paper-GroupLike.grouplike {₃₊ n})
      using (•-cancelʳ ; •-cancelˡ)

    -- CZ on the upper pair has order p, inherited from order-CZ one wire
    -- down.  (ε ↑ is ε definitionally, so the shift leaves no residue.)
    lemma-order-CZ↑ : (CZ ↑) ^ p ≈ ε
    lemma-order-CZ↑ = begin
      (CZ ↑) ^ p  ≈⟨ refl' (Eq.sym (lemma-↑^ p CZ)) ⟩
      (CZ ^ p) ↑  ≈⟨ lemma-cong↑ _ _ (order-CZ) ⟩
      ε ∎

    -- Conjugation commutes with powers.  Stated over an arbitrary u so it
    -- serves CZ02 and anything else conjugated by the swap.
    lemma-conj-pow : ∀ (u : Word (Gen (₃₊ n))) k →
                     (Ex • (u • Ex)) ^ k ≈ Ex • (u ^ k • Ex)
    lemma-conj-pow u ₀ = begin
      ε              ≈⟨ sym lemma-Ex-Ex ⟩
      Ex • Ex        ≈⟨ cright sym left-unit ⟩
      Ex • (ε • Ex) ∎
    lemma-conj-pow u ₁ = refl
    lemma-conj-pow u (₂₊ k) = begin
      (Ex • (u • Ex)) • (Ex • (u • Ex)) ^ ₁₊ k
        ≈⟨ cright lemma-conj-pow u (₁₊ k) ⟩
      (Ex • (u • Ex)) • (Ex • (u ^ ₁₊ k • Ex))
        ≈⟨ assoc ⟩
      Ex • ((u • Ex) • (Ex • (u ^ ₁₊ k • Ex)))
        ≈⟨ cright assoc ⟩
      Ex • (u • (Ex • (Ex • (u ^ ₁₊ k • Ex))))
        ≈⟨ cright cright sym assoc ⟩
      Ex • (u • ((Ex • Ex) • (u ^ ₁₊ k • Ex)))
        ≈⟨ cright cright cleft lemma-Ex-Ex ⟩
      Ex • (u • (ε • (u ^ ₁₊ k • Ex)))
        ≈⟨ cright cright left-unit ⟩
      Ex • (u • (u ^ ₁₊ k • Ex))
        ≈⟨ cright sym assoc ⟩
      Ex • ((u • u ^ ₁₊ k) • Ex) ∎

    -- The remote CZ has order p as well: p copies of it are p copies of
    -- CZ ↑ with the two swaps cancelling.
    lemma-order-CZ02 : CZ02 ^ p ≈ ε
    lemma-order-CZ02 = begin
      CZ02 ^ p                ≈⟨ lemma-conj-pow (CZ ↑) p ⟩
      Ex • ((CZ ↑) ^ p • Ex)  ≈⟨ cright cleft lemma-order-CZ↑ ⟩
      Ex • (ε • Ex)           ≈⟨ cright left-unit ⟩
      Ex • Ex                 ≈⟨ lemma-Ex-Ex ⟩
      ε ∎

    ------------------------------------------------------------------------
    -- The multiplier commutes with anything on the wires above it
    --
    -- Mg is a product of powers of S, H and Z on wire 0, and each of those
    -- commutes with a shifted word; the two combinators below lift that
    -- through the products and powers Mg is built from.  Taking w = CX
    -- gives what the rescaled C18 needs.

    private
      comm-• : ∀ {u v} {w : Word (Gen (₂₊ n))} →
               u • w ↑ ≈ w ↑ • u → v • w ↑ ≈ w ↑ • v →
               (u • v) • w ↑ ≈ w ↑ • (u • v)
      comm-• {u} {v} {w} cu cv = begin
        (u • v) • w ↑  ≈⟨ assoc ⟩
        u • (v • w ↑)  ≈⟨ cright cv ⟩
        u • (w ↑ • v)  ≈⟨ sym assoc ⟩
        (u • w ↑) • v  ≈⟨ cleft cu ⟩
        (w ↑ • u) • v  ≈⟨ assoc ⟩
        w ↑ • (u • v) ∎

      comm-pow : ∀ {u} {w : Word (Gen (₂₊ n))} →
                 u • w ↑ ≈ w ↑ • u → ∀ k → u ^ k • w ↑ ≈ w ↑ • u ^ k
      comm-pow cu ₀      = trans left-unit (sym right-unit)
      comm-pow cu ₁      = cu
      comm-pow cu (₂₊ k) = comm-• cu (comm-pow cu (₁₊ k))

    lemma-Mg-w↑ : ∀ (w : Word (Gen (₂₊ n))) → Mg • w ↑ ≈ w ↑ • Mg
    lemma-Mg-w↑ w =
      comm-• cR^ (comm-• cH (comm-• cR^' (comm-• cH (comm-• cR^ cH))))
      where
      cH = lemma-comm-H-w↑ w
      cZ^ = comm-pow (lemma-comm-Z-w↑ w) (toℕ 1/2)
      cR  = comm-• (lemma-comm-S-w↑ w) cZ^
      cR^ = comm-pow cR (toℕ g)
      cR^' = comm-pow cR (toℕ ((g′ ⁻¹) .proj₁))

    lemma-Mg-CX↑ : Mg • CX ↑ ≈ CX ↑ • Mg
    lemma-Mg-CX↑ = lemma-Mg-w↑ CX

    ------------------------------------------------------------------------
    -- The multiplier on wire 0 rescales the remote CZ too
    --
    -- CZ02 is Ex • CZ ↑ • Ex, so the multiplier passes onto the upper wire
    -- with the swap, rescales there against CZ ↑, and comes back; the
    -- power is carried through the swap by lemma-conj-pow.

    private
      -- semi-M↓CZ one wire up: Mg on wire 1 against CZ on wires 1-2.
      -- The instance one wire down, so that cong↑ lands at this width.
      semi↑ : Mg ↑ • CZ ↑ ≈ (CZ ↑) ^ toℕ g • Mg ↑
      semi↑ = trans (lemma-cong↑ _ _ (Ex-Conjugation.lemma-semi-Mg-CZ n))
                    (refl' (Eq.cong (_• Mg ↑) (lemma-↑^ (toℕ g) CZ)))

      -- The swap carries the multiplier from wire 1 down to wire 0.
      mg↑Ex : Mg ↑ • Ex ≈ Ex • Mg
      mg↑Ex = begin
        Mg ↑ • Ex               ≈⟨ sym left-unit ⟩
        ε • (Mg ↑ • Ex)         ≈⟨ cleft sym lemma-Ex-Ex ⟩
        (Ex • Ex) • (Mg ↑ • Ex) ≈⟨ assoc ⟩
        Ex • (Ex • (Mg ↑ • Ex)) ≈⟨ cright lemma-conj-Ex-Mg↑ ⟩
        Ex • Mg ∎

    lemma-Mg-CZ02 : Mg • CZ02 ≈ CZ02 ^ toℕ g • Mg
    lemma-Mg-CZ02 = begin
      Mg • (Ex • (CZ ↑ • Ex))
        ≈⟨ sym assoc ⟩
      (Mg • Ex) • (CZ ↑ • Ex)
        ≈⟨ cleft sym lemma-Ex-Mg↑ ⟩
      (Ex • Mg ↑) • (CZ ↑ • Ex)
        ≈⟨ assoc ⟩
      Ex • (Mg ↑ • (CZ ↑ • Ex))
        ≈⟨ cright sym assoc ⟩
      Ex • ((Mg ↑ • CZ ↑) • Ex)
        ≈⟨ cright cleft semi↑ ⟩
      Ex • (((CZ ↑) ^ toℕ g • Mg ↑) • Ex)
        ≈⟨ cright assoc ⟩
      Ex • ((CZ ↑) ^ toℕ g • (Mg ↑ • Ex))
        ≈⟨ cright cright mg↑Ex ⟩
      Ex • ((CZ ↑) ^ toℕ g • (Ex • Mg))
        ≈⟨ cright sym assoc ⟩
      Ex • (((CZ ↑) ^ toℕ g • Ex) • Mg)
        ≈⟨ sym assoc ⟩
      (Ex • ((CZ ↑) ^ toℕ g • Ex)) • Mg
        ≈⟨ cleft sym (lemma-conj-pow (CZ ↑) (toℕ g)) ⟩
      CZ02 ^ toℕ g • Mg ∎

    ------------------------------------------------------------------------
    -- Iterating the multiplier: from the fixed generator to any unit
    --
    -- Mg ^ j rescales by g ^′ j.  The induction costs only associativity,
    -- because x ^′ (suc k) is x * (x ^′ k) definitionally; the ₀/₁/₂₊ split
    -- is forced by w ^ 1 being w rather than w • w ^ 0.

    ------------------------------------------------------------------------
    -- The transposition of wires 0 and 2
    --
    -- Ex swaps wires 0-1 and Ex ↑ swaps 1-2, so Ex • Ex ↑ • Ex transposes
    -- 0 and 2.  It carries CZ (wires 0-1) to CZ ↑ (wires 1-2), which is the
    -- transport between the progress report's form of C15 —
    -- CZ₁₂ • CZ₀₂ = CZ₀₂ • CZ₁₂, stated "up to qubit wire permutation" —
    -- and selinger-c12 as Simplified-V1 states it.  It is also the mirror
    -- that exchanges c14 and c15, since it swaps ⊤⊥ ↑ with ⊥⊤ as well.
    --
    -- Note Ex ↓ is Ex definitionally: _↓ maps every gate to itself and Ex
    -- is a word of gate letters with no symbolic power, so cz-slide and
    -- yang-baxter, which Paper-V0 states with Ex ↓, are proved below
    -- against Ex directly.

    ------------------------------------------------------------------------
    -- Iterating C18
    --
    -- Each CZ pushed leftwards through CX ↑ leaves a CZ02 behind, so a
    -- power of CZ leaves the alternating product (CZ • CZ02) ^ k.  No
    -- commutation between CZ and CZ02 is assumed — the two stay
    -- interleaved, which is the whole point: comparing this against the
    -- multiplier-rescaled form of the same word is what proves they
    -- commute.

    -- C18 read with CX ↑ on the left of the CZ.  The axiom as stated emits
    -- its CZ02 on the far left when a CZ crosses CX ↑ leftwards; read the
    -- other way it emits CZ02 ⁻¹, and it is that form the iteration needs,
    -- because the emitted factor lands outside CX ↑ and so does not block
    -- the next step.  (The axiom used to be stated in circuit order, which
    -- is the reverse of Word order; this is the same relation read the
    -- right way round.)

    private
      CZ02⁻ : Word (Gen (₃₊ n))
      CZ02⁻ = CZ02 ^ p-1

      lemma-CZ02-CZ02⁻ : CZ02 • CZ02⁻ ≈ ε
      lemma-CZ02-CZ02⁻ = begin
        CZ02 • CZ02 ^ p-1     ≈⟨ sym (^-+ CZ02 1 p-1) ⟩
        CZ02 ^ (1 Nat.+ p-1)  ≈⟨ lemma-order-CZ02 ⟩
        ε ∎

    lemma-C18' : CX ↑ • CZ ≈ (CZ02⁻ • CZ) • CX ↑
    lemma-C18' = •-cancelˡ {g = CZ02} (begin
      CZ02 • (CX ↑ • CZ)
        ≈⟨ sym (semi-CX↑-CZ↓) ⟩
      CZ • CX ↑
        ≈⟨ cleft sym left-unit ⟩
      (ε • CZ) • CX ↑
        ≈⟨ cleft cleft sym lemma-CZ02-CZ02⁻ ⟩
      ((CZ02 • CZ02⁻) • CZ) • CX ↑
        ≈⟨ cleft assoc ⟩
      (CZ02 • (CZ02⁻ • CZ)) • CX ↑
        ≈⟨ assoc ⟩
      CZ02 • ((CZ02⁻ • CZ) • CX ↑) ∎)

    lemma-C18ᵏ : ∀ k → CX ↑ • CZ ^ k ≈ (CZ02⁻ • CZ) ^ k • CX ↑
    lemma-C18ᵏ ₀ = trans right-unit (sym left-unit)
    lemma-C18ᵏ ₁ = lemma-C18'
    lemma-C18ᵏ (₂₊ k) = begin
      CX ↑ • (CZ • CZ ^ ₁₊ k)
        ≈⟨ sym assoc ⟩
      (CX ↑ • CZ) • CZ ^ ₁₊ k
        ≈⟨ cleft lemma-C18' ⟩
      ((CZ02⁻ • CZ) • CX ↑) • CZ ^ ₁₊ k
        ≈⟨ assoc ⟩
      (CZ02⁻ • CZ) • (CX ↑ • CZ ^ ₁₊ k)
        ≈⟨ cright lemma-C18ᵏ (₁₊ k) ⟩
      (CZ02⁻ • CZ) • ((CZ02⁻ • CZ) ^ ₁₊ k • CX ↑)
        ≈⟨ sym assoc ⟩
      ((CZ02⁻ • CZ) • (CZ02⁻ • CZ) ^ ₁₊ k) • CX ↑ ∎

    ------------------------------------------------------------------------
    -- The alternating product has order p as well
    --
    -- CX ↑ • CZ ^ p is CX ↑ on the nose, so lemma-C18ᵏ at p says
    -- (CZ02 ⁻¹ • CZ) ^ p • CX ↑ is too, and CX ↑ cancels on the right.

    lemma-order-CZ·CZ02 : (CZ02⁻ • CZ) ^ p ≈ ε
    lemma-order-CZ·CZ02 = •-cancelʳ {h = CX ↑} (begin
      (CZ02⁻ • CZ) ^ p • CX ↑ ≈⟨ sym (lemma-C18ᵏ p) ⟩
      CX ↑ • CZ ^ p           ≈⟨ cright order-CZ ⟩
      CX ↑ • ε                ≈⟨ right-unit ⟩
      CX ↑                    ≈⟨ sym left-unit ⟩
      ε • CX ↑ ∎)

    ------------------------------------------------------------------------
    -- The rescaled C18, and the exponent identity it forces
    --
    -- Conjugating C18 by Mg ^ j — which commutes with CX ↑ and rescales
    -- both CZ and CZ02 by g ^′ j — gives (A).  Comparing it against the
    -- interleaved form (B) of lemma-C18ᵏ at the same exponent, and
    -- cancelling CX ↑, leaves (C): the two CZs distribute over that power.

    lemma-Mg-CZ02^ : ∀ (a : ℤ ₚ) → Mg • CZ02 ^ toℕ a ≈ CZ02 ^ toℕ (g * a) • Mg
    lemma-Mg-CZ02^ a = begin
      Mg • CZ02 ^ toℕ a
        ≈⟨ lemma-Induction lemma-Mg-CZ02 (toℕ a) ⟩
      (CZ02 ^ toℕ g) ^ toℕ a • Mg
        ≈⟨ cleft (^^ CZ02 (toℕ g) (toℕ a)) ⟩
      CZ02 ^ (toℕ g Nat.* toℕ a) • Mg
        ≈⟨ cleft (lemma-pow-mod lemma-order-CZ02 (toℕ g Nat.* toℕ a)) ⟩
      CZ02 ^ ((toℕ g Nat.* toℕ a) Nat.% p) • Mg
        ≈⟨ cleft refl' (Eq.cong (CZ02 ^_) (lemma-toℕ-% g a)) ⟩
      CZ02 ^ toℕ (g * a) • Mg ∎

    lemma-Mgᵏ-CZ02 : ∀ j → Mg ^ j • CZ02 ≈ CZ02 ^ toℕ (g ^′ j) • Mg ^ j
    lemma-Mgᵏ-CZ02 ₀ = begin
      ε • CZ02  ≈⟨ left-unit ⟩
      CZ02      ≈⟨ sym right-unit ⟩
      CZ02 • ε ∎
    lemma-Mgᵏ-CZ02 ₁ = begin
      Mg • CZ02             ≈⟨ lemma-Mg-CZ02 ⟩
      CZ02 ^ toℕ g • Mg
        ≡⟨ Eq.cong (λ z → CZ02 ^ toℕ z • Mg) (Eq.sym (lemma-x^′1=x g)) ⟩
      CZ02 ^ toℕ (g ^′ 1) • Mg ∎
    lemma-Mgᵏ-CZ02 (₂₊ j) = begin
      (Mg • Mg ^ ₁₊ j) • CZ02
        ≈⟨ assoc ⟩
      Mg • (Mg ^ ₁₊ j • CZ02)
        ≈⟨ cright lemma-Mgᵏ-CZ02 (₁₊ j) ⟩
      Mg • (CZ02 ^ toℕ (g ^′ ₁₊ j) • Mg ^ ₁₊ j)
        ≈⟨ sym assoc ⟩
      (Mg • CZ02 ^ toℕ (g ^′ ₁₊ j)) • Mg ^ ₁₊ j
        ≈⟨ cleft lemma-Mg-CZ02^ (g ^′ ₁₊ j) ⟩
      (CZ02 ^ toℕ (g * (g ^′ ₁₊ j)) • Mg) • Mg ^ ₁₊ j
        ≈⟨ assoc ⟩
      CZ02 ^ toℕ (g * (g ^′ ₁₊ j)) • (Mg • Mg ^ ₁₊ j) ∎

    lemma-Mgᵏ-CX↑ : ∀ j → Mg ^ j • CX ↑ ≈ CX ↑ • Mg ^ j
    lemma-Mgᵏ-CX↑ = comm-pow lemma-Mg-CX↑

    -- (A): C18 with every CZ exponent rescaled by g ^′ j.  The multiplier
    -- rescales the emitted CZ02 ⁻¹ too, so its exponent picks up the same
    -- factor: CZ02 ^ (p-1) becomes CZ02 ^ ((p-1) * e).
    lemma-A : ∀ j → let e = toℕ (g ^′ j) in
              CX ↑ • CZ ^ e ≈ (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • CX ↑
    lemma-A j = •-cancelʳ {h = Mg ^ j} (begin
      (CX ↑ • CZ ^ e) • Mg ^ j
        ≈⟨ assoc ⟩
      CX ↑ • (CZ ^ e • Mg ^ j)
        ≈⟨ cright sym (lemma-Mgᵏ-CZ j) ⟩
      CX ↑ • (Mg ^ j • CZ)
        ≈⟨ sym assoc ⟩
      (CX ↑ • Mg ^ j) • CZ
        ≈⟨ cleft sym (lemma-Mgᵏ-CX↑ j) ⟩
      (Mg ^ j • CX ↑) • CZ
        ≈⟨ assoc ⟩
      Mg ^ j • (CX ↑ • CZ)
        ≈⟨ cright lemma-C18' ⟩
      Mg ^ j • ((CZ02⁻ • CZ) • CX ↑)
        ≈⟨ sym assoc ⟩
      (Mg ^ j • (CZ02⁻ • CZ)) • CX ↑
        ≈⟨ cleft sym assoc ⟩
      ((Mg ^ j • CZ02⁻) • CZ) • CX ↑
        ≈⟨ cleft cleft rescale ⟩
      ((CZ02 ^ (p-1 Nat.* e) • Mg ^ j) • CZ) • CX ↑
        ≈⟨ cleft assoc ⟩
      (CZ02 ^ (p-1 Nat.* e) • (Mg ^ j • CZ)) • CX ↑
        ≈⟨ cleft cright (lemma-Mgᵏ-CZ j) ⟩
      (CZ02 ^ (p-1 Nat.* e) • (CZ ^ e • Mg ^ j)) • CX ↑
        ≈⟨ cleft sym assoc ⟩
      ((CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • Mg ^ j) • CX ↑
        ≈⟨ assoc ⟩
      (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • (Mg ^ j • CX ↑)
        ≈⟨ cright (lemma-Mgᵏ-CX↑ j) ⟩
      (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • (CX ↑ • Mg ^ j)
        ≈⟨ sym assoc ⟩
      ((CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • CX ↑) • Mg ^ j ∎)
      where
      e = toℕ (g ^′ j)
      rescale : Mg ^ j • CZ02⁻ ≈ CZ02 ^ (p-1 Nat.* e) • Mg ^ j
      rescale = begin
        Mg ^ j • CZ02 ^ p-1
          ≈⟨ lemma-Induction (lemma-Mgᵏ-CZ02 j) p-1 ⟩
        (CZ02 ^ e) ^ p-1 • Mg ^ j
          ≈⟨ cleft (^^ CZ02 e p-1) ⟩
        CZ02 ^ (e Nat.* p-1) • Mg ^ j
          ≡⟨ Eq.cong (λ m → CZ02 ^ m • Mg ^ j) (NP.*-comm e p-1) ⟩
        CZ02 ^ (p-1 Nat.* e) • Mg ^ j ∎

    -- (C): the two CZs distribute over the rescaled power.
    lemma-C : ∀ j → let e = toℕ (g ^′ j) in
              (CZ02⁻ • CZ) ^ e ≈ CZ02 ^ (p-1 Nat.* e) • CZ ^ e
    lemma-C j = •-cancelʳ {h = CX ↑} (begin
      (CZ02⁻ • CZ) ^ e • CX ↑                 ≈⟨ sym (lemma-C18ᵏ e) ⟩
      CX ↑ • CZ ^ e                           ≈⟨ lemma-A j ⟩
      (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • CX ↑ ∎)
      where e = toℕ (g ^′ j)

    ------------------------------------------------------------------------
    -- The two CZs sharing a wire commute
    --
    -- This is the progress report's C15, its Lemma 9.  Since g generates
    -- the units, some power of it is 2, and (C) at that exponent reads
    --
    --     (CZ • CZ02) • (CZ • CZ02)  ≈  (CZ • CZ) • (CZ02 • CZ02)
    --
    -- Cancelling a CZ on the left and a CZ02 on the right is the whole of
    -- the rest.  Nothing here is circular: the multiplier rescaling is an
    -- input from outside the CZ/CZ02 family, which is exactly why the
    -- report inserts M₂ • M½.

    private
      ₂ᵤ : ℤ* ₚ
      ₂ᵤ = (2ₚ , λ ())
        where
        2ₚ : ℤ ₚ
        2ₚ = ₂

      -- The power of g that is 2.
      j₂ : ℕ
      j₂ = toℕ (g-gen ₂ᵤ .proj₁)

      e₂ : toℕ (g ^′ j₂) ≡ 2
      e₂ = Eq.cong toℕ (Eq.sym (g-gen ₂ᵤ .proj₂))

      -- (C) with the exponent evaluated.
      lemma-C₂ : (CZ02⁻ • CZ) • (CZ02⁻ • CZ) ≈ (CZ02⁻ • CZ02⁻) • (CZ • CZ)
      lemma-C₂ = begin
        (CZ02⁻ • CZ) • (CZ02⁻ • CZ)
          ≡⟨ Eq.cong ((CZ02⁻ • CZ) ^_) (Eq.sym e₂) ⟩
        (CZ02⁻ • CZ) ^ toℕ (g ^′ j₂)
          ≈⟨ lemma-C j₂ ⟩
        CZ02 ^ (p-1 Nat.* toℕ (g ^′ j₂)) • CZ ^ toℕ (g ^′ j₂)
          ≡⟨ Eq.cong₂ (λ a b → CZ02 ^ (p-1 Nat.* a) • CZ ^ b) e₂ e₂ ⟩
        CZ02 ^ (p-1 Nat.* 2) • (CZ • CZ)
          ≈⟨ cleft sym (^^ CZ02 p-1 2) ⟩
        (CZ02⁻ • CZ02⁻) • (CZ • CZ) ∎

      -- Cancelling one CZ02 ⁻¹ on the left and one CZ on the right.  All
      -- explicit assoc: CZ02 ⁻¹ is a symbolic power, so to-list is stuck.
      lemma-comm-CZ-CZ02⁻ : CZ • CZ02⁻ ≈ CZ02⁻ • CZ
      lemma-comm-CZ-CZ02⁻ =
        •-cancelˡ {g = CZ02⁻} (•-cancelʳ {h = CZ} (begin
          (CZ02⁻ • (CZ • CZ02⁻)) • CZ
            ≈⟨ cleft sym assoc ⟩
          ((CZ02⁻ • CZ) • CZ02⁻) • CZ
            ≈⟨ assoc ⟩
          (CZ02⁻ • CZ) • (CZ02⁻ • CZ)
            ≈⟨ lemma-C₂ ⟩
          (CZ02⁻ • CZ02⁻) • (CZ • CZ)
            ≈⟨ assoc ⟩
          CZ02⁻ • (CZ02⁻ • (CZ • CZ))
            ≈⟨ cright sym assoc ⟩
          CZ02⁻ • ((CZ02⁻ • CZ) • CZ)
            ≈⟨ sym assoc ⟩
          (CZ02⁻ • (CZ02⁻ • CZ)) • CZ ∎))

      lemma-CZ02⁻-CZ02 : CZ02⁻ • CZ02 ≈ ε
      lemma-CZ02⁻-CZ02 = begin
        CZ02 ^ p-1 • CZ02
          ≈⟨ sym (^-+ CZ02 p-1 1) ⟩
        CZ02 ^ (p-1 Nat.+ 1)
          ≡⟨ Eq.cong (CZ02 ^_) (NP.+-comm p-1 1) ⟩
        CZ02 ^ (1 Nat.+ p-1)
          ≈⟨ lemma-order-CZ02 ⟩
        ε ∎

    -- CZ commutes with CZ02 ⁻¹, hence with CZ02.
    lemma-comm-CZ-CZ02 : CZ • CZ02 ≈ CZ02 • CZ
    lemma-comm-CZ-CZ02 = begin
      CZ • CZ02
        ≈⟨ cleft sym left-unit ⟩
      (ε • CZ) • CZ02
        ≈⟨ cleft cleft sym lemma-CZ02-CZ02⁻ ⟩
      ((CZ02 • CZ02⁻) • CZ) • CZ02
        ≈⟨ cleft assoc ⟩
      (CZ02 • (CZ02⁻ • CZ)) • CZ02
        ≈⟨ cleft cright sym lemma-comm-CZ-CZ02⁻ ⟩
      (CZ02 • (CZ • CZ02⁻)) • CZ02
        ≈⟨ cleft sym assoc ⟩
      ((CZ02 • CZ) • CZ02⁻) • CZ02
        ≈⟨ assoc ⟩
      (CZ02 • CZ) • (CZ02⁻ • CZ02)
        ≈⟨ cright lemma-CZ02⁻-CZ02 ⟩
      (CZ02 • CZ) • ε
        ≈⟨ right-unit ⟩
      CZ02 • CZ ∎

    T : Word (Gen (₃₊ n))
    T = Ex • Ex ↑ • Ex

    lemma-Ex↑-Ex↑ : Ex ↑ • Ex ↑ ≈ ε
    lemma-Ex↑-Ex↑ = lemma-cong↑ _ _ (order-Ex)

    ------------------------------------------------------------------------
    -- cz-slide and yang-baxter are theorems
    --
    -- Paper-V0 states both as axioms; neither is needed.  The swap of
    -- wires 1-2, Ex ↑, is the braid of the two half-swaps on those wires,
    -- a = ₕ|ₕ ↑ and b = ʰ|ʰ ↑ (lemma-Ex-hhh lifted), and cz-slide is the
    -- statement that it carries CZ to CZ02.  Swap-Argument derives that
    -- from how a, b and Ex ↑ act on CZ and CZ02, and every one of those
    -- actions comes from the two-wire calculus, semi-CX↑-CZ↓ and
    -- lemma-comm-CZ-CZ02:
    --
    --   c12        CZ ↑ against CZ: lemma-comm-CZ-CZ02 conjugated by Ex
    --   H ↑, M₋₁ ↑ against CZ02: Ex carries them to wire 0
    --   CZ ↑ against CZ02: lemma-comm-CZ-CZ02's rescaling again
    --              (Rescale), with XC for CX ↑ and the multiplier on
    --              wire 2 for the one on wire 0
    --   a on CZ    lemma-c14-key: CZ ↦ (CZ • CZ02)⁻¹
    --   Ex ↑ on CZ • CZ02⁻¹: inverted, read through
    --              Ex ↑ ≈ CX ↑ • XC' ↑ • CX ↑ • M₋₁ ↑ (lemma-Ex-CX-XC)
    --
    -- yang-baxter then follows: Ex and Ex ↑ conjugate each other to the
    -- same word, letter by letter, once both carry a CZ to CZ02.

    open Conjugation (Γ (₃₊ n)) (Paper-GroupLike.grouplike {₃₊ n})
    open Pattern-Assoc using (by-passoc ; □)

    private
      CZ⁻ : Word (Gen (₃₊ n))
      CZ⁻ = CZ ^ p-1

      lemma-CZ-CZ⁻ : CZ • CZ⁻ ≈ ε
      lemma-CZ-CZ⁻ = begin
        CZ • CZ ^ p-1       ≈⟨ sym (^-+ CZ 1 p-1) ⟩
        CZ ^ (1 Nat.+ p-1)  ≈⟨ order-CZ ⟩
        ε ∎

      lemma-CZ⁻-CZ : CZ⁻ • CZ ≈ ε
      lemma-CZ⁻-CZ = begin
        CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
        CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
        CZ ^ (1 Nat.+ p-1)  ≈⟨ order-CZ ⟩
        ε ∎

      -- Ex carries CZ02 to CZ ↑, CZ02 being Ex • CZ ↑ • Ex.
      Ex-CZ02 : Conj Ex CZ02 (CZ ↑)
      Ex-CZ02 = cancel-• lemma-Ex-Ex

      Ex-CZ↑ : Conj Ex (CZ ↑) CZ02
      Ex-CZ↑ = sym (begin
        (Ex • (CZ ↑ • Ex)) • Ex   ≈⟨ by-assoc auto ⟩
        Ex • (CZ ↑ • (Ex • Ex))   ≈⟨ cright cright lemma-Ex-Ex ⟩
        Ex • (CZ ↑ • ε)           ≈⟨ cright right-unit ⟩
        Ex • CZ ↑ ∎)

    -- c12, by conjugating lemma-comm-CZ-CZ02 with Ex, which fixes CZ and
    -- carries CZ02 to CZ ↑.
    lemma-selinger-c12 : CZ ↑ • CZ ≈ CZ • CZ ↑
    lemma-selinger-c12 = sym (conj-unique
      (conj-cong lemma-comm-CZ-CZ02 refl (conj-• lemma-Ex-CZ Ex-CZ02))
      (conj-• Ex-CZ02 lemma-Ex-CZ))

    -- H ↑ commutes with CZ02: Ex carries it to H on wire 0, which passes
    -- CZ ↑ structurally, and carries it back.
    lemma-comm-H↑-CZ02 : H ↑ • CZ02 ≈ CZ02 • H ↑
    lemma-comm-H↑-CZ02 = begin
      H ↑ • (Ex • (CZ ↑ • Ex))   ≈⟨ sym assoc ⟩
      (H ↑ • Ex) • (CZ ↑ • Ex)   ≈⟨ cleft sym lemma-Ex-H ⟩
      (Ex • H) • (CZ ↑ • Ex)     ≈⟨ by-assoc auto ⟩
      Ex • ((H • CZ ↑) • Ex)     ≈⟨ cright cleft lemma-comm-H-w↑ CZ ⟩
      Ex • ((CZ ↑ • H) • Ex)     ≈⟨ cright assoc ⟩
      Ex • (CZ ↑ • (H • Ex))     ≈⟨ cright cright sym lemma-Ex-H↑ ⟩
      Ex • (CZ ↑ • (Ex • H ↑))   ≈⟨ by-assoc auto ⟩
      (Ex • (CZ ↑ • Ex)) • H ↑ ∎

    -- …and so does the multiplier by −1 on wire 1, which is H ↑ ^ 2.
    lemma-M₋₁↑-CZ02 : M₋₁ ↑ • CZ02 ≈ CZ02 • M₋₁ ↑
    lemma-M₋₁↑-CZ02 = conj-congˡ (lemma-cong↑ _ _ order-H)
      (conj-∘ lemma-comm-H↑-CZ02 lemma-comm-H↑-CZ02)

    -- XC conjugates CZ ↑ to CZ ↑ • CZ02 ⁻¹: semi-CX↑-CZ↓, read for the
    -- inverse CX' ↑ of CX ↑, between the two H ↑ of XC.
    private
      H↑³-H↑ : (H ↑) ^ 3 • H ↑ ≈ ε
      H↑³-H↑ = trans (by-assoc auto) lemma-order-H↑

      CX↑-CX'↑ : CX ↑ • CX' ↑ ≈ ε
      CX↑-CX'↑ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-CX-CX' n)

      CX'↑-CX↑ : CX' ↑ • CX ↑ ≈ ε
      CX'↑-CX↑ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-CX'-CX n)

      CZ-CX'↑ : Conj CZ (CX' ↑) (CX' ↑ • CZ02⁻)
      CZ-CX'↑ = conj-inv-u CX↑-CX'↑ (tele lemma-CZ02⁻-CZ02 CX'↑-CX↑)
                  (trans semi-CX↑-CZ↓ (sym assoc))

      H↑³-CX'↑ : Conj ((H ↑) ^ 3) (CX' ↑) (CZ ↑)
      H↑³-CX'↑ = begin
        (H ↑) ^ 3 • (H ↑ • (CZ ↑ • (H ↑) ^ 3))   ≈⟨ by-assoc auto ⟩
        (H ↑) ^ 4 • (CZ ↑ • (H ↑) ^ 3)           ≈⟨ cleft lemma-order-H↑ ⟩
        ε • (CZ ↑ • (H ↑) ^ 3)                   ≈⟨ left-unit ⟩
        CZ ↑ • (H ↑) ^ 3 ∎

    lemma-XC-CZ↑ : Conj XC (CZ ↑) (CZ ↑ • CZ02⁻)
    lemma-XC-CZ↑ =
      conj-∘ (conj-∘ (conj-lit H↑³-H↑) CZ-CX'↑)
        (conj-• H↑³-CX'↑ (conj-^ (conj-^ˡ lemma-comm-H↑-CZ02 3) p-1))

    -- CZ ↑ commutes with CZ02, by rescaling lemma-XC-CZ↑ with the
    -- multiplier on wire 2.  That multiplier commutes with every word on
    -- wires 0-1, rescales CZ ↑ by semi-M↑CZ, and rescales CZ02 the same
    -- way, Ex carrying it past.
    private
      ↑↑-H : ∀ (w : Word (Gen (₁₊ n))) → Conj (w ↑ ↑) H H
      ↑↑-H w = sym (lemma-comm-H-w↑ (w ↑))

      ↑↑-H↑ : ∀ (w : Word (Gen (₁₊ n))) → Conj (w ↑ ↑) (H ↑) (H ↑)
      ↑↑-H↑ w = sym (lemma-cong↑ _ _ (lemma-comm-H-w↑ w))

      ↑↑-CZ : ∀ (w : Word (Gen (₁₊ n))) → Conj (w ↑ ↑) CZ CZ
      ↑↑-CZ w = sym (lemma-comm-CZ-w↑ w)

      ↑↑-XC : ∀ (w : Word (Gen (₁₊ n))) → Conj (w ↑ ↑) XC XC
      ↑↑-XC w = conj-• (conj-^ (↑↑-H↑ w) 3) (conj-• (↑↑-CZ w) (↑↑-H↑ w))

      ↑↑-Ex : ∀ (w : Word (Gen (₁₊ n))) → Conj (w ↑ ↑) Ex Ex
      ↑↑-Ex w =
        conj-• cz (conj-• h (conj-• h↑ (conj-• cz (conj-• h (conj-• h↑
          (conj-• cz (conj-• h h↑)))))))
        where
        cz = ↑↑-CZ w
        h  = ↑↑-H w
        h↑ = ↑↑-H↑ w

      Mg↑↑^ : ∀ j → ((Mg {n} ^ j) ↑) ↑ ≡ (Mg {n} ↑ ↑) ^ j
      Mg↑↑^ j = Eq.trans (Eq.cong (λ w → w ↑) (lemma-↑^ j Mg)) (lemma-↑^ j (Mg ↑))

      m-XC : ∀ j → Conj ((Mg ↑ ↑) ^ j) XC XC
      m-XC j = Eq.subst (λ z → Conj z XC XC) (Mg↑↑^ j) (↑↑-XC (Mg ^ j))

      m-Ex : ∀ j → Conj ((Mg ↑ ↑) ^ j) Ex Ex
      m-Ex j = Eq.subst (λ z → Conj z Ex Ex) (Mg↑↑^ j) (↑↑-Ex (Mg ^ j))

      m-CZ↑ : ∀ j → Conj ((Mg ↑ ↑) ^ j) (CZ ↑) ((CZ ↑) ^ toℕ (g ^′ j))
      m-CZ↑ j = begin
        (Mg ↑ ↑) ^ j • CZ ↑
          ≡⟨ Eq.cong (_• CZ ↑) (Eq.sym (lemma-↑^ j (Mg ↑))) ⟩
        ((Mg ↑) ^ j) ↑ • CZ ↑
          ≈⟨ lemma-cong↑ _ _ (Ex-Conjugation.lemma-Mgᵏ↑-CZ n j) ⟩
        (CZ ^ toℕ (g ^′ j)) ↑ • ((Mg ↑) ^ j) ↑
          ≡⟨ Eq.cong₂ _•_ (lemma-↑^ (toℕ (g ^′ j)) CZ) (lemma-↑^ j (Mg ↑)) ⟩
        (CZ ↑) ^ toℕ (g ^′ j) • (Mg ↑ ↑) ^ j ∎

      m-CZ02⁻ : ∀ j → Conj ((Mg ↑ ↑) ^ j) CZ02⁻ (CZ02⁻ ^ toℕ (g ^′ j))
      m-CZ02⁻ j = conj-cong refl (^^' CZ02 e p-1) (conj-^ m-CZ02 p-1)
        where
        e = toℕ (g ^′ j)
        m-CZ02 : Conj ((Mg ↑ ↑) ^ j) CZ02 (CZ02 ^ e)
        m-CZ02 = conj-cong refl (sym (lemma-conj-pow (CZ ↑) e))
                   (conj-• (m-Ex j) (conj-• (m-CZ↑ j) (m-Ex j)))

      module R5 = Rescale (Γ (₃₊ n)) (Paper-GroupLike.grouplike {₃₊ n})
                    XC (CZ ↑) (CZ ↑) CZ02⁻ (Mg ↑ ↑)
                    lemma-XC-CZ↑ m-XC m-CZ↑ m-CZ↑ m-CZ02⁻

    lemma-comm-CZ↑-CZ02 : CZ ↑ • CZ02 ≈ CZ02 • CZ ↑
    lemma-comm-CZ↑-CZ02 =
      conj-inv-u lemma-CZ02⁻-CZ02 lemma-CZ02-CZ02⁻ R5.comm

    -- CX ↑ fixes CZ02, and XC' ↑ fixes CZ.
    private
      CX↑-CZ02 : Conj (CX ↑) CZ02 CZ02
      CX↑-CZ02 = conj-∘ (conj-∘ lemma-comm-H↑-CZ02 lemma-comm-CZ↑-CZ02)
                   (conj-^ˡ lemma-comm-H↑-CZ02 3)

      H↑↑-CZ : Conj (H ↑ ↑) CZ CZ
      H↑↑-CZ = ↑↑-CZ H

      XC'↑-CZ : Conj (XC' ↑) CZ CZ
      XC'↑-CZ = conj-∘ (conj-∘ (conj-^ˡ H↑↑-CZ 3) lemma-selinger-c12) H↑↑-CZ

    ------------------------------------------------------------------------
    -- The identity c14 turns on
    --
    --     CZ • ₕ|ₕ ↑ • CZ • ₕ|ₕ ↑ ≈ CZ02
    --
    -- i.e. conjugating CZ by the upper half-swap gives CZ⁻¹ • CZ02.  This
    -- is where C18 enters.
    --
    -- The half-swap is M₋₁ • CX (lemma-ₕ|ₕ-CX), so C18 applies directly:
    -- it moves CX ↑ across the CZ at the cost of a CZ02.  The two CX ↑ that
    -- are left sandwich a multiplier, and that sandwich collapses back to
    -- the multiplier because the half-swap is an involution.  What remains
    -- is a multiplier passing two CZs, rescaling one of them to its inverse
    -- and commuting with the other.

    private
      -- The half-swap is an involution, and it is M₋₁ ↑ • CX ↑, so the two
      -- CX ↑ sandwiching a multiplier collapse back to that multiplier.
      ₕ|ₕ↑-CX : M₋₁ ↑ • CX ↑ ≈ ₕ|ₕ ↑
      ₕ|ₕ↑-CX = lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-CX n)

      M₋₁↑-invol : M₋₁ ↑ • M₋₁ ↑ ≈ ε
      M₋₁↑-invol = lemma-cong↑ _ _ (One-Wire.lemma-M₋₁^2 (₁₊ n))

      lemma-CX↑-M₋₁↑ : CX ↑ • (M₋₁ ↑ • CX ↑) ≈ M₋₁ ↑
      lemma-CX↑-M₋₁↑ = •-cancelˡ {g = M₋₁ ↑} (begin
        M₋₁ ↑ • (CX ↑ • (M₋₁ ↑ • CX ↑))
          ≈⟨ sym assoc ⟩
        (M₋₁ ↑ • CX ↑) • (M₋₁ ↑ • CX ↑)
          ≈⟨ cong ₕ|ₕ↑-CX ₕ|ₕ↑-CX ⟩
        ₕ|ₕ ↑ • ₕ|ₕ ↑
          ≈⟨ lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n) ⟩
        ε
          ≈⟨ sym M₋₁↑-invol ⟩
        M₋₁ ↑ • M₋₁ ↑ ∎)

    -- Conjugating CZ by the upper half-swap gives the inverse of CZ • CZ02.
    -- Stated inverse-free, that is this.
    lemma-c14-key : CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • ₕ|ₕ ↑))) ≈ ε
    lemma-c14-key = begin
      CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • ₕ|ₕ ↑)))
        ≈⟨ cright cright cong (sym ₕ|ₕ↑-CX) (cright sym ₕ|ₕ↑-CX) ⟩
      CZ • (CZ02 • ((M₋₁ ↑ • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑))))
        -- explicit assoc, not by-assoc: M₋₁'s symbolic power blocks to-list
        ≈⟨ cright sym assoc ⟩
      CZ • ((CZ02 • (M₋₁ ↑ • CX ↑)) • (CZ • (M₋₁ ↑ • CX ↑)))
        ≈⟨ cright cleft sym assoc ⟩
      CZ • (((CZ02 • M₋₁ ↑) • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑)))
        ≈⟨ cright cleft cleft sym lemma-M₋₁↑-CZ02 ⟩
      CZ • (((M₋₁ ↑ • CZ02) • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑)))
        ≈⟨ cright cleft assoc ⟩
      CZ • ((M₋₁ ↑ • (CZ02 • CX ↑)) • (CZ • (M₋₁ ↑ • CX ↑)))
        ≈⟨ cright assoc ⟩
      CZ • (M₋₁ ↑ • ((CZ02 • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑))))
        ≈⟨ cright cright sym assoc ⟩
      CZ • (M₋₁ ↑ • (((CZ02 • CX ↑) • CZ) • (M₋₁ ↑ • CX ↑)))
        ≈⟨ cright cright cleft assoc ⟩
      CZ • (M₋₁ ↑ • ((CZ02 • (CX ↑ • CZ)) • (M₋₁ ↑ • CX ↑)))
        -- the axiom, right to left
        ≈⟨ cright cright cleft sym (semi-CX↑-CZ↓) ⟩
      CZ • (M₋₁ ↑ • ((CZ • CX ↑) • (M₋₁ ↑ • CX ↑)))
        ≈⟨ cright cright assoc ⟩
      CZ • (M₋₁ ↑ • (CZ • (CX ↑ • (M₋₁ ↑ • CX ↑))))
        ≈⟨ cright cright cright lemma-CX↑-M₋₁↑ ⟩
      CZ • (M₋₁ ↑ • (CZ • M₋₁ ↑))
        ≈⟨ cright sym assoc ⟩
      CZ • ((M₋₁ ↑ • CZ) • M₋₁ ↑)
        ≈⟨ cright cleft lemma-M₋₁↑-CZ ⟩
      CZ • ((CZ ^ toℕ (-'₁ .proj₁) • M₋₁ ↑) • M₋₁ ↑)
        ≈⟨ cright assoc ⟩
      CZ • (CZ ^ toℕ (-'₁ .proj₁) • (M₋₁ ↑ • M₋₁ ↑))
        ≈⟨ cright cright M₋₁↑-invol ⟩
      CZ • (CZ ^ toℕ (-'₁ .proj₁) • ε)
        ≈⟨ cright right-unit ⟩
      CZ • CZ ^ toℕ (-'₁ .proj₁)
        ≈⟨ lemma-CZ-CZ₋₁ ⟩
      ε ∎

    ------------------------------------------------------------------------
    -- The swap argument at three wires

    private
      au bu : Word (Gen (₃₊ n))
      au = ₕ|ₕ ↑
      bu = ʰ|ʰ ↑

      au-au : au • au ≈ ε
      au-au = lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n)

      bu-bu : bu • bu ≈ ε
      bu-bu = lemma-cong↑ _ _ (Ex-Conjugation.lemma-ʰ|ʰ-invol n)

      Ex↑-aba : Ex ↑ ≈ au • (bu • au)
      Ex↑-aba = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-hhh n)

      Ex↑-bab : Ex ↑ ≈ bu • (au • bu)
      Ex↑-bab = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-hhh' n)

      Ex↑-CX : Ex ↑ ≈ CX ↑ • (XC' ↑ • (CX ↑ • M₋₁ ↑))
      Ex↑-CX = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-CX-XC n)

      -- b fixes CZ: H ↑ ↑ passes it structurally, CZ ↑ by c12.
      bu-CZ : Conj bu CZ CZ
      bu-CZ = conj-∘ (conj-∘ H↑↑-CZ lemma-selinger-c12) H↑↑-CZ

      -- a fixes CZ02.
      au-CZ02 : Conj au CZ02 CZ02
      au-CZ02 = conj-∘ (conj-∘ lemma-comm-H↑-CZ02 lemma-comm-CZ↑-CZ02)
                  lemma-comm-H↑-CZ02

      -- a sends CZ to (CZ • CZ02)⁻¹: lemma-c14-key.
      au-CZ : Conj au CZ (CZ02⁻ • CZ⁻)
      au-CZ = conj-cong refl img (conj-lit au-au)
        where
        img : au • (CZ • au) ≈ CZ02⁻ • CZ⁻
        img = begin
          au • (CZ • au)
            ≈⟨ sym left-unit ⟩
          ε • (au • (CZ • au))
            ≈⟨ cleft sym (tele lemma-CZ⁻-CZ lemma-CZ02⁻-CZ02) ⟩
          ((CZ02⁻ • CZ⁻) • (CZ • CZ02)) • (au • (CZ • au))
            ≈⟨ by-passoc (((□ • □) • (□ • □)) • □) ((□ • □) • (□ • (□ • □))) auto ⟩
          (CZ02⁻ • CZ⁻) • (CZ • (CZ02 • (au • (CZ • au))))
            ≈⟨ cright lemma-c14-key ⟩
          (CZ02⁻ • CZ⁻) • ε
            ≈⟨ right-unit ⟩
          CZ02⁻ • CZ⁻ ∎

      -- Ex ↑ inverts CZ • CZ02⁻¹, read through lemma-Ex-CX-XC: M₋₁ ↑
      -- inverts CZ and fixes CZ02, CX ↑ turns CZ⁻¹ into CZ⁻¹ • CZ02 (C18)
      -- and fixes CZ02, and XC' ↑ fixes CZ.
      M↑-CZ : Conj (M₋₁ ↑) CZ CZ⁻
      M↑-CZ = trans lemma-M₋₁↑-CZ (cleft refl' (Eq.cong (CZ ^_) lemma-toℕ-1ₚ))

      CX↑-CZ⁻ : Conj (CX ↑) CZ⁻ (CZ⁻ • CZ02)
      CX↑-CZ⁻ = conj-inv-u lemma-CZ-CZ⁻ (tele lemma-CZ02-CZ02⁻ lemma-CZ⁻-CZ)
                  lemma-C18'

      Ex↑-CZCZ02⁻ : Conj (Ex ↑) (CZ • CZ02⁻) (CZ⁻ • CZ02)
      Ex↑-CZCZ02⁻ = conj-congˡ (sym Ex↑-CX)
        (conj-∘ (conj-∘ (conj-∘ q₁ q₂) q₃) CX↑-CZ⁻)
        where
        q₁ : Conj (M₋₁ ↑) (CZ • CZ02⁻) (CZ⁻ • CZ02⁻)
        q₁ = conj-• M↑-CZ (conj-^ lemma-M₋₁↑-CZ02 p-1)

        q₂ : Conj (CX ↑) (CZ⁻ • CZ02⁻) CZ⁻
        q₂ = conj-cong refl
               (trans assoc (trans (cright lemma-CZ02-CZ02⁻) right-unit))
               (conj-• CX↑-CZ⁻ (conj-^ CX↑-CZ02 p-1))

        q₃ : Conj (XC' ↑) CZ⁻ CZ⁻
        q₃ = conj-^ XC'↑-CZ p-1

      module SA = Swap-Argument (Γ (₃₊ n)) (Paper-GroupLike.grouplike {₃₊ n})
                    au bu CZ CZ⁻ CZ02 CZ02⁻ (Ex ↑)
                    au-au bu-bu Ex↑-bab Ex↑-aba
                    lemma-CZ-CZ⁻ lemma-CZ⁻-CZ lemma-CZ02-CZ02⁻ lemma-CZ02⁻-CZ02
                    order-CZ lemma-order-CZ02
                    lemma-comm-CZ-CZ02 bu-CZ au-CZ02 au-CZ Ex↑-CZCZ02⁻

    -- The swap of wires 1-2 carries CZ to CZ02.
    lemma-Ex↑-CZ : Ex ↑ • CZ ≈ CZ02 • Ex ↑
    lemma-Ex↑-CZ = SA.swap

    -- CZ02 through the upper swap rather than the lower one.
    lemma-CZ02' : Ex ↑ • (CZ • Ex ↑) ≈ CZ02
    lemma-CZ02' = begin
      Ex ↑ • (CZ • Ex ↑)     ≈⟨ sym assoc ⟩
      (Ex ↑ • CZ) • Ex ↑     ≈⟨ cleft lemma-Ex↑-CZ ⟩
      (CZ02 • Ex ↑) • Ex ↑   ≈⟨ assoc ⟩
      CZ02 • (Ex ↑ • Ex ↑)   ≈⟨ cright lemma-Ex↑-Ex↑ ⟩
      CZ02 • ε               ≈⟨ right-unit ⟩
      CZ02 ∎

    -- Paper-V0's cz-slide.
    lemma-cz-slide : Ex ↓ • Ex ↑ • CZ ≈ CZ ↑ • Ex ↓ • Ex ↑
    lemma-cz-slide = begin
      Ex • (Ex ↑ • CZ)     ≈⟨ cright lemma-Ex↑-CZ ⟩
      Ex • (CZ02 • Ex ↑)   ≈⟨ sym assoc ⟩
      (Ex • CZ02) • Ex ↑   ≈⟨ cleft Ex-CZ02 ⟩
      (CZ ↑ • Ex) • Ex ↑   ≈⟨ assoc ⟩
      CZ ↑ • (Ex • Ex ↑) ∎

    -- Paper-V0's yang-baxter.  Ex sends the letters CZ ↑, H ↑, H ↑ ↑ of
    -- Ex ↑ to CZ02, H, H ↑ ↑, and Ex ↑ sends the letters CZ, H, H ↑ of Ex
    -- to the same three, so the two swaps conjugate each other to one
    -- word Y, and both sides of the braid relation are Y.
    private
      Y : Word (Gen (₃₊ n))
      Y = CZ02 • (H • (H ↑ ↑ • (CZ02 • (H • (H ↑ ↑ • (CZ02 • (H • H ↑ ↑)))))))

      Ex-Ex↑ : Conj Ex (Ex ↑) Y
      Ex-Ex↑ =
        conj-• cz (conj-• h (conj-• h↑ (conj-• cz (conj-• h (conj-• h↑
          (conj-• cz (conj-• h h↑)))))))
        where
        cz = Ex-CZ↑
        h  = lemma-Ex-H↑
        h↑ = comm-sym (↑↑-Ex H)

      Ex↑-Ex : Conj (Ex ↑) Ex Y
      Ex↑-Ex =
        conj-• cz (conj-• h (conj-• h↑ (conj-• cz (conj-• h (conj-• h↑
          (conj-• cz (conj-• h h↑)))))))
        where
        cz = lemma-Ex↑-CZ
        h  = sym (lemma-comm-H-w↑ Ex)
        h↑ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-H n)

      involution : ∀ {a u v} → a • a ≈ ε → Conj a u v → a • (u • a) ≈ v
      involution aa e =
        trans (sym assoc) (trans (cleft e) (trans assoc (trans (cright aa) right-unit)))

    lemma-yang-baxter : Ex ↑ • Ex ↓ • Ex ↑ ≈ Ex ↓ • Ex ↑ • Ex ↓
    lemma-yang-baxter =
      trans (involution lemma-Ex↑-Ex↑ Ex↑-Ex) (sym (involution lemma-Ex-Ex Ex-Ex↑))

    ------------------------------------------------------------------------
    -- The swaps generate S₃
    --
    -- order-Ex makes each swap an involution and lemma-yang-baxter is the
    -- braid relation, so the 3-cycle σ = Ex • Ex ↑ has order 3.  Both c14
    -- and c15 assert that some element cubes to ε, so this is the shape
    -- they have to be matched against.

    lemma-σ³ : ((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑) ≈ ε
    lemma-σ³ = begin
      ((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑)
        ≈⟨ by-assoc auto ⟩
      Ex • (Ex ↑ • Ex • Ex ↑) • (Ex • Ex ↑)
        ≈⟨ cright cleft lemma-yang-baxter ⟩
      Ex • (Ex ↓ • Ex ↑ • Ex ↓) • (Ex • Ex ↑)
        ≈⟨ by-assoc auto ⟩
      (Ex • Ex) • Ex ↑ • (Ex • Ex) • Ex ↑
        ≈⟨ cleft lemma-Ex-Ex ⟩
      ε • Ex ↑ • (Ex • Ex) • Ex ↑
        ≈⟨ left-unit ⟩
      Ex ↑ • (Ex • Ex) • Ex ↑
        ≈⟨ cright cleft lemma-Ex-Ex ⟩
      Ex ↑ • ε • Ex ↑
        ≈⟨ cright left-unit ⟩
      Ex ↑ • Ex ↑
        ≈⟨ lemma-Ex↑-Ex↑ ⟩
      ε ∎

    lemma-T-T : T • T ≈ ε
    lemma-T-T = begin
      (Ex • Ex ↑ • Ex) • (Ex • Ex ↑ • Ex)  ≈⟨ by-assoc auto ⟩
      (Ex • Ex ↑) • (Ex • Ex) • (Ex ↑ • Ex) ≈⟨ cright cleft lemma-Ex-Ex ⟩
      (Ex • Ex ↑) • ε • (Ex ↑ • Ex)         ≈⟨ cright left-unit ⟩
      (Ex • Ex ↑) • (Ex ↑ • Ex)             ≈⟨ by-assoc auto ⟩
      Ex • (Ex ↑ • Ex ↑) • Ex               ≈⟨ cright cleft lemma-Ex↑-Ex↑ ⟩
      Ex • ε • Ex                           ≈⟨ cright left-unit ⟩
      Ex • Ex                               ≈⟨ lemma-Ex-Ex ⟩
      ε ∎

    lemma-T-CZ : T • CZ • T ≈ CZ ↑
    lemma-T-CZ = begin
      (Ex • Ex ↑ • Ex) • CZ • (Ex • Ex ↑ • Ex)
        ≈⟨ by-assoc auto ⟩
      (Ex • Ex ↑) • (Ex • CZ) • (Ex • Ex ↑ • Ex)
        ≈⟨ cright cleft lemma-Ex-CZ ⟩
      (Ex • Ex ↑) • (CZ • Ex) • (Ex • Ex ↑ • Ex)
        ≈⟨ by-assoc auto ⟩
      (Ex ↓ • Ex ↑ • CZ) • (Ex • Ex) • (Ex ↑ • Ex)
        ≈⟨ cleft lemma-cz-slide ⟩
      (CZ ↑ • Ex ↓ • Ex ↑) • (Ex • Ex) • (Ex ↑ • Ex)
        ≈⟨ cright cleft lemma-Ex-Ex ⟩
      (CZ ↑ • Ex ↓ • Ex ↑) • ε • (Ex ↑ • Ex)
        ≈⟨ cright left-unit ⟩
      (CZ ↑ • Ex ↓ • Ex ↑) • (Ex ↑ • Ex)
        ≈⟨ by-assoc auto ⟩
      CZ ↑ • Ex • (Ex ↑ • Ex ↑) • Ex
        ≈⟨ cright cright cleft lemma-Ex↑-Ex↑ ⟩
      CZ ↑ • Ex • ε • Ex
        ≈⟨ cright cright left-unit ⟩
      CZ ↑ • Ex • Ex
        ≈⟨ cright lemma-Ex-Ex ⟩
      CZ ↑ • ε
        ≈⟨ right-unit ⟩
      CZ ↑ ∎

    ------------------------------------------------------------------------
    -- The lower half-swap commutes with the upper CZ
    --
    -- ₕ|ₕ is H • CZ • H, all on wires 0 and 1.  The H commutes with CZ ↑
    -- structurally — it is a one-wire gate against a gate shifted off wire
    -- 0 — and the two CZs commute by c12.  This is what makes c13
    -- collapse.

    lemma-comm-ₕ|ₕ-CZ↑ : ₕ|ₕ • CZ ↑ ≈ CZ ↑ • ₕ|ₕ
    lemma-comm-ₕ|ₕ-CZ↑ = begin
      (H • CZ • H) • CZ ↑
        ≈⟨ by-assoc auto ⟩
      H • (CZ • (H • CZ ↑))
        ≈⟨ cright cright sym (comm-H) ⟩
      H • (CZ • (CZ ↑ • H))
        ≈⟨ cright sym assoc ⟩
      H • ((CZ • CZ ↑) • H)
        ≈⟨ cright cleft sym lemma-selinger-c12 ⟩
      H • ((CZ ↑ • CZ) • H)
        ≈⟨ by-assoc auto ⟩
      (H • CZ ↑) • (CZ • H)
        ≈⟨ cleft sym (comm-H) ⟩
      (CZ ↑ • H) • (CZ • H)
        ≈⟨ by-assoc auto ⟩
      CZ ↑ • (H • CZ • H) ∎

    ------------------------------------------------------------------------
    -- Half of c13: conjugating the upper CZ by the half-swaps gives CZ02
    --
    -- With ⊥⊤ = Ex • ₕ|ₕ and ⊤⊥ = ₕ|ₕ • Ex, the word ⊥⊤ • CZ ↑ • ⊤⊥ is
    -- Ex • (ₕ|ₕ • CZ ↑ • ₕ|ₕ) • Ex; the previous lemma moves CZ ↑ out
    -- through one ₕ|ₕ, the involution kills the pair, and what is left is
    -- Ex • CZ ↑ • Ex, which is CZ02 by definition.
    --
    -- Semantically both sides of c13 are CZ02 — that is how this shape was
    -- found — so the other half is the same statement about the upper pair.

    ------------------------------------------------------------------------
    -- The upper half-swap commutes with CZ02
    --
    -- The mirror of lemma-comm-ₕ|ₕ-CZ↑, one wire up.  ₕ|ₕ ↑ is
    -- H ↑ • CZ ↑ • H ↑, and both its letters commute with CZ02
    -- (lemma-comm-H↑-CZ02 and lemma-comm-CZ↑-CZ02, from the derivation of
    -- cz-slide above).

    lemma-comm-ₕ|ₕ↑-CZ02 :
      (H ↑ • CZ ↑ • H ↑) • CZ02 ≈ CZ02 • (H ↑ • CZ ↑ • H ↑)
    lemma-comm-ₕ|ₕ↑-CZ02 = begin
      (H ↑ • CZ ↑ • H ↑) • CZ02
        ≈⟨ by-assoc auto ⟩
      H ↑ • (CZ ↑ • (H ↑ • CZ02))
        ≈⟨ cright cright lemma-comm-H↑-CZ02 ⟩
      H ↑ • (CZ ↑ • (CZ02 • H ↑))
        ≈⟨ cright sym assoc ⟩
      H ↑ • ((CZ ↑ • CZ02) • H ↑)
        ≈⟨ cright cleft lemma-comm-CZ↑-CZ02 ⟩
      H ↑ • ((CZ02 • CZ ↑) • H ↑)
        ≈⟨ sym assoc ⟩
      (H ↑ • (CZ02 • CZ ↑)) • H ↑
        ≈⟨ cleft sym assoc ⟩
      ((H ↑ • CZ02) • CZ ↑) • H ↑
        ≈⟨ cleft cleft lemma-comm-H↑-CZ02 ⟩
      ((CZ02 • H ↑) • CZ ↑) • H ↑
        ≈⟨ by-assoc auto ⟩
      CZ02 • (H ↑ • CZ ↑ • H ↑) ∎

    lemma-c13-right : ⊥⊤ • (CZ ↑ • ⊤⊥) ≈ CZ02
    lemma-c13-right = begin
      ⊥⊤ • (CZ ↑ • ⊤⊥)
        ≈⟨ cleft lemma-⊥⊤-simple ⟩
      (Ex • ₕ|ₕ) • (CZ ↑ • ⊤⊥)
        ≈⟨ cright cright lemma-⊤⊥-simple ⟩
      (Ex • ₕ|ₕ) • (CZ ↑ • (ₕ|ₕ • Ex))
        ≈⟨ by-assoc auto ⟩
      Ex • (((ₕ|ₕ • CZ ↑) • ₕ|ₕ) • Ex)
        ≈⟨ cright cleft cleft lemma-comm-ₕ|ₕ-CZ↑ ⟩
      Ex • (((CZ ↑ • ₕ|ₕ) • ₕ|ₕ) • Ex)
        ≈⟨ cright cleft assoc ⟩
      Ex • ((CZ ↑ • (ₕ|ₕ • ₕ|ₕ)) • Ex)
        ≈⟨ cright cleft cright lemma-ₕ|ₕ-invol ⟩
      Ex • ((CZ ↑ • ε) • Ex)
        ≈⟨ cright cleft right-unit ⟩
      Ex • (CZ ↑ • Ex) ∎

    ------------------------------------------------------------------------
    -- The other half of c13, and c13 itself
    --
    -- One wire up, with lemma-comm-ₕ|ₕ↑-CZ02 in place of lemma-comm-ₕ|ₕ-CZ↑
    -- and lemma-CZ02' in place of the definition of CZ02.  Both sides of
    -- c13 are CZ02, so the rule is the two halves glued.

    lemma-c13-left : ⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑) ≈ CZ02
    lemma-c13-left = begin
      ⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑)
        ≈⟨ cleft (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-simple n)) ⟩
      ((H ↑ • CZ ↑ • H ↑) • Ex ↑) • (CZ • ⊥⊤ {n} ↑)
        ≈⟨ cright cright (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊥⊤-simple n)) ⟩
      ((H ↑ • CZ ↑ • H ↑) • Ex ↑) • (CZ • (Ex ↑ • (H ↑ • CZ ↑ • H ↑)))
        ≈⟨ by-assoc auto ⟩
      (H ↑ • CZ ↑ • H ↑) • ((Ex ↑ • (CZ • Ex ↑)) • (H ↑ • CZ ↑ • H ↑))
        ≈⟨ cright cleft lemma-CZ02' ⟩
      (H ↑ • CZ ↑ • H ↑) • (CZ02 • (H ↑ • CZ ↑ • H ↑))
        ≈⟨ sym assoc ⟩
      ((H ↑ • CZ ↑ • H ↑) • CZ02) • (H ↑ • CZ ↑ • H ↑)
        ≈⟨ cleft lemma-comm-ₕ|ₕ↑-CZ02 ⟩
      (CZ02 • (H ↑ • CZ ↑ • H ↑)) • (H ↑ • CZ ↑ • H ↑)
        ≈⟨ assoc ⟩
      CZ02 • ((H ↑ • CZ ↑ • H ↑) • (H ↑ • CZ ↑ • H ↑))
        ≈⟨ cright (lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n)) ⟩
      CZ02 • ε
        ≈⟨ right-unit ⟩
      CZ02 ∎

    lemma-selinger-c13 :
      ⊤⊥ {n} ↑ • CZ ↓ • ⊥⊤ {n} ↑ ≈ ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
    lemma-selinger-c13 = trans lemma-c13-left (sym lemma-c13-right)

    ------------------------------------------------------------------------
    -- c13 as a commutation rule
    --
    -- Since ⊥⊤ ↑ inverts ⊤⊥ ↑, the conjugation form of c13 is equivalently
    -- a rule for moving ⊤⊥ ↑ across a CZ, which turns it from CZ into
    -- CZ02.  This is the form c14 uses: its element ⊤⊥ ↑ • CZ becomes
    -- CZ02 • ⊤⊥ ↑, so cubing it is a question about how ⊤⊥ ↑ moves across
    -- CZ02 — the one step c14 still lacks.

    lemma-⊤⊥↑-CZ : ⊤⊥ {n} ↑ • CZ ≈ CZ02 • ⊤⊥ {n} ↑
    lemma-⊤⊥↑-CZ = begin
      ⊤⊥ {n} ↑ • CZ
        ≈⟨ sym right-unit ⟩
      (⊤⊥ {n} ↑ • CZ) • ε
        ≈⟨ cright sym (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊥⊤-⊤⊥ n)) ⟩
      (⊤⊥ {n} ↑ • CZ) • (⊥⊤ {n} ↑ • ⊤⊥ {n} ↑)
        ≈⟨ by-assoc auto ⟩
      (⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑)) • ⊤⊥ {n} ↑
        ≈⟨ cleft lemma-c13-left ⟩
      CZ02 • ⊤⊥ {n} ↑ ∎

    ------------------------------------------------------------------------
    -- c14
    --
    -- Write A for ⊤⊥ ↑.  Conjugation by A sends CZ to CZ02 (that is c13,
    -- as lemma-⊤⊥↑-CZ) and CZ02 to the inverse of CZ • CZ02 (that is
    -- lemma-c14-key).  A has order 3, so cubing A • CZ telescopes: pushing
    -- the three A's rightwards leaves CZ02 • (CZ • CZ02)⁻¹ • CZ, which is ε.
    --
    -- The inverses are real words here — CZ ⁻¹ is CZ ^ p-1 — so this section
    -- uses explicit assoc throughout, to-list being stuck on them.

    private
      -- lemma-c14-key with one half-swap cancelled off the right.
      key' : CZ • (CZ02 • (ₕ|ₕ ↑ • CZ)) ≈ ₕ|ₕ ↑
      key' = •-cancelʳ {h = ₕ|ₕ ↑} (begin
        (CZ • (CZ02 • (ₕ|ₕ ↑ • CZ))) • ₕ|ₕ ↑
          ≈⟨ assoc ⟩
        CZ • ((CZ02 • (ₕ|ₕ ↑ • CZ)) • ₕ|ₕ ↑)
          ≈⟨ cright assoc ⟩
        CZ • (CZ02 • ((ₕ|ₕ ↑ • CZ) • ₕ|ₕ ↑))
          ≈⟨ cright cright assoc ⟩
        CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • ₕ|ₕ ↑)))
          ≈⟨ lemma-c14-key ⟩
        ε
          ≈⟨ sym (lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n)) ⟩
        ₕ|ₕ ↑ • ₕ|ₕ ↑ ∎)

      -- Ex ↑ carries CZ02 to CZ, since CZ02 is Ex ↑ • CZ • Ex ↑.
      ex↑-CZ02 : Ex ↑ • CZ02 ≈ CZ • Ex ↑
      ex↑-CZ02 = begin
        Ex ↑ • CZ02
          ≈⟨ cright sym lemma-CZ02' ⟩
        Ex ↑ • (Ex ↑ • (CZ • Ex ↑))
          ≈⟨ sym assoc ⟩
        (Ex ↑ • Ex ↑) • (CZ • Ex ↑)
          ≈⟨ cleft lemma-Ex↑-Ex↑ ⟩
        ε • (CZ • Ex ↑)
          ≈⟨ left-unit ⟩
        CZ • Ex ↑ ∎

      ⊤⊥↑-split : ⊤⊥ {n} ↑ ≈ ₕ|ₕ ↑ • Ex ↑
      ⊤⊥↑-split = lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-simple n)

    -- Conjugation by ⊤⊥ ↑ sends CZ02 to the inverse of CZ • CZ02.
    lemma-⊤⊥↑-CZ02 : CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02)) ≈ ⊤⊥ {n} ↑
    lemma-⊤⊥↑-CZ02 = begin
      CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02))
        ≈⟨ cright cright cleft ⊤⊥↑-split ⟩
      CZ • (CZ02 • ((ₕ|ₕ ↑ • Ex ↑) • CZ02))
        ≈⟨ cright cright assoc ⟩
      CZ • (CZ02 • (ₕ|ₕ ↑ • (Ex ↑ • CZ02)))
        ≈⟨ cright cright cright ex↑-CZ02 ⟩
      CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • Ex ↑)))
        ≈⟨ cright cright sym assoc ⟩
      CZ • (CZ02 • ((ₕ|ₕ ↑ • CZ) • Ex ↑))
        ≈⟨ cright sym assoc ⟩
      CZ • ((CZ02 • (ₕ|ₕ ↑ • CZ)) • Ex ↑)
        ≈⟨ sym assoc ⟩
      (CZ • (CZ02 • (ₕ|ₕ ↑ • CZ))) • Ex ↑
        ≈⟨ cleft key' ⟩
      ₕ|ₕ ↑ • Ex ↑
        ≈⟨ sym ⊤⊥↑-split ⟩
      ⊤⊥ {n} ↑ ∎

    private
      -- The three ways ⊤⊥ ↑ moves across the two CZs and their inverses.
      A·CZ02 : ⊤⊥ {n} ↑ • CZ02 ≈ (CZ02⁻ • CZ⁻) • ⊤⊥ {n} ↑
      A·CZ02 = begin
        ⊤⊥ {n} ↑ • CZ02
          ≈⟨ sym left-unit ⟩
        ε • (⊤⊥ {n} ↑ • CZ02)
          ≈⟨ cleft sym lemma-CZ02⁻-CZ02 ⟩
        (CZ02⁻ • CZ02) • (⊤⊥ {n} ↑ • CZ02)
          ≈⟨ cleft cright sym left-unit ⟩
        (CZ02⁻ • (ε • CZ02)) • (⊤⊥ {n} ↑ • CZ02)
          ≈⟨ cleft cright cleft sym lemma-CZ⁻-CZ ⟩
        (CZ02⁻ • ((CZ⁻ • CZ) • CZ02)) • (⊤⊥ {n} ↑ • CZ02)
          ≈⟨ cleft cright assoc ⟩
        (CZ02⁻ • (CZ⁻ • (CZ • CZ02))) • (⊤⊥ {n} ↑ • CZ02)
          ≈⟨ cleft sym assoc ⟩
        ((CZ02⁻ • CZ⁻) • (CZ • CZ02)) • (⊤⊥ {n} ↑ • CZ02)
          ≈⟨ assoc ⟩
        (CZ02⁻ • CZ⁻) • ((CZ • CZ02) • (⊤⊥ {n} ↑ • CZ02))
          ≈⟨ cright assoc ⟩
        (CZ02⁻ • CZ⁻) • (CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02)))
          ≈⟨ cright lemma-⊤⊥↑-CZ02 ⟩
        (CZ02⁻ • CZ⁻) • ⊤⊥ {n} ↑ ∎

      -- Right-multiplying lemma-⊤⊥↑-CZ02 by CZ02 ⁻¹.
      A·CZ02⁻ : ⊤⊥ {n} ↑ • CZ02⁻ ≈ (CZ • CZ02) • ⊤⊥ {n} ↑
      A·CZ02⁻ = begin
        ⊤⊥ {n} ↑ • CZ02⁻
          ≈⟨ cleft sym lemma-⊤⊥↑-CZ02 ⟩
        (CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02))) • CZ02⁻
          ≈⟨ assoc ⟩
        CZ • ((CZ02 • (⊤⊥ {n} ↑ • CZ02)) • CZ02⁻)
          ≈⟨ cright assoc ⟩
        CZ • (CZ02 • ((⊤⊥ {n} ↑ • CZ02) • CZ02⁻))
          ≈⟨ cright cright assoc ⟩
        CZ • (CZ02 • (⊤⊥ {n} ↑ • (CZ02 • CZ02⁻)))
          ≈⟨ cright cright cright lemma-CZ02-CZ02⁻ ⟩
        CZ • (CZ02 • (⊤⊥ {n} ↑ • ε))
          ≈⟨ cright cright right-unit ⟩
        CZ • (CZ02 • ⊤⊥ {n} ↑)
          ≈⟨ sym assoc ⟩
        (CZ • CZ02) • ⊤⊥ {n} ↑ ∎

      -- c13 iterated: A moves across CZ ⁻¹ turning it into CZ02 ⁻¹.
      A·CZ⁻ : ⊤⊥ {n} ↑ • CZ⁻ ≈ CZ02⁻ • ⊤⊥ {n} ↑
      A·CZ⁻ = lemma-Induction lemma-⊤⊥↑-CZ p-1

      tb : Word (Gen (₃₊ n))
      tb = ⊤⊥ {n} ↑

      tb³ : (tb • tb) • tb ≈ ε
      tb³ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-cube3 n)

      -- The collapse.  Each A meeting a CZ02 on its right emits
      -- CZ02 ⁻¹ • CZ ⁻¹ and moves past it; the emitted factors cancel
      -- against the CZ02 and CZ already standing to the left, and after
      -- three such moves only the cube of A is left.
      cube-collapse : (CZ02 • tb) • ((CZ02 • tb) • (CZ02 • tb)) ≈ ε
      cube-collapse = begin
        (CZ02 • tb) • ((CZ02 • tb) • (CZ02 • tb))
          ≈⟨ assoc ⟩
        CZ02 • (tb • ((CZ02 • tb) • (CZ02 • tb)))
          ≈⟨ cright sym assoc ⟩
        CZ02 • ((tb • (CZ02 • tb)) • (CZ02 • tb))
          ≈⟨ cright cleft sym assoc ⟩
        CZ02 • (((tb • CZ02) • tb) • (CZ02 • tb))
          ≈⟨ cright cleft cleft A·CZ02 ⟩
        CZ02 • ((((CZ02⁻ • CZ⁻) • tb) • tb) • (CZ02 • tb))
          ≈⟨ cright cleft assoc ⟩
        CZ02 • (((CZ02⁻ • CZ⁻) • (tb • tb)) • (CZ02 • tb))
          ≈⟨ cright assoc ⟩
        CZ02 • ((CZ02⁻ • CZ⁻) • ((tb • tb) • (CZ02 • tb)))
          ≈⟨ cright assoc ⟩
        CZ02 • (CZ02⁻ • (CZ⁻ • ((tb • tb) • (CZ02 • tb))))
          ≈⟨ sym assoc ⟩
        (CZ02 • CZ02⁻) • (CZ⁻ • ((tb • tb) • (CZ02 • tb)))
          ≈⟨ cleft lemma-CZ02-CZ02⁻ ⟩
        ε • (CZ⁻ • ((tb • tb) • (CZ02 • tb)))
          ≈⟨ left-unit ⟩
        CZ⁻ • ((tb • tb) • (CZ02 • tb))
          ≈⟨ cright assoc ⟩
        CZ⁻ • (tb • (tb • (CZ02 • tb)))
          ≈⟨ cright cright sym assoc ⟩
        CZ⁻ • (tb • ((tb • CZ02) • tb))
          ≈⟨ cright cright cleft A·CZ02 ⟩
        CZ⁻ • (tb • (((CZ02⁻ • CZ⁻) • tb) • tb))
          ≈⟨ cright cright cleft assoc ⟩
        CZ⁻ • (tb • ((CZ02⁻ • (CZ⁻ • tb)) • tb))
          ≈⟨ cright cright assoc ⟩
        CZ⁻ • (tb • (CZ02⁻ • ((CZ⁻ • tb) • tb)))
          ≈⟨ cright sym assoc ⟩
        CZ⁻ • ((tb • CZ02⁻) • ((CZ⁻ • tb) • tb))
          ≈⟨ cright cleft A·CZ02⁻ ⟩
        CZ⁻ • (((CZ • CZ02) • tb) • ((CZ⁻ • tb) • tb))
          ≈⟨ cright assoc ⟩
        CZ⁻ • ((CZ • CZ02) • (tb • ((CZ⁻ • tb) • tb)))
          ≈⟨ cright assoc ⟩
        CZ⁻ • (CZ • (CZ02 • (tb • ((CZ⁻ • tb) • tb))))
          ≈⟨ sym assoc ⟩
        (CZ⁻ • CZ) • (CZ02 • (tb • ((CZ⁻ • tb) • tb)))
          ≈⟨ cleft lemma-CZ⁻-CZ ⟩
        ε • (CZ02 • (tb • ((CZ⁻ • tb) • tb)))
          ≈⟨ left-unit ⟩
        CZ02 • (tb • ((CZ⁻ • tb) • tb))
          ≈⟨ cright cright assoc ⟩
        CZ02 • (tb • (CZ⁻ • (tb • tb)))
          ≈⟨ cright sym assoc ⟩
        CZ02 • ((tb • CZ⁻) • (tb • tb))
          ≈⟨ cright cleft A·CZ⁻ ⟩
        CZ02 • ((CZ02⁻ • tb) • (tb • tb))
          ≈⟨ cright assoc ⟩
        CZ02 • (CZ02⁻ • (tb • (tb • tb)))
          ≈⟨ sym assoc ⟩
        (CZ02 • CZ02⁻) • (tb • (tb • tb))
          ≈⟨ cleft lemma-CZ02-CZ02⁻ ⟩
        ε • (tb • (tb • tb))
          ≈⟨ left-unit ⟩
        tb • (tb • tb)
          ≈⟨ sym assoc ⟩
        (tb • tb) • tb
          ≈⟨ tb³ ⟩
        ε ∎

    lemma-selinger-c14 : (⊤⊥ {n} ↑ • CZ ↓) ^ 3 ≈ ε
    lemma-selinger-c14 = begin
      (tb • CZ) • ((tb • CZ) • (tb • CZ))
        ≈⟨ cong lemma-⊤⊥↑-CZ (cong lemma-⊤⊥↑-CZ lemma-⊤⊥↑-CZ) ⟩
      (CZ02 • tb) • ((CZ02 • tb) • (CZ02 • tb))
        ≈⟨ cube-collapse ⟩
      ε ∎

    ------------------------------------------------------------------------
    -- c15, by transporting c14 along the transposition of wires 0 and 2
    --
    -- T = Ex • Ex ↑ • Ex exchanges wires 0 and 2 and fixes wire 1.  So it
    -- fixes H ↑, exchanges CZ with CZ ↑ (lemma-T-CZ) and exchanges the two
    -- swaps, hence carries ⊤⊥ ↑ to ⊥⊤ — which turns c14's element into
    -- c15's.  Since T is an involution, conjugating a cube is the cube of
    -- the conjugate, so c15 is c14 read through T.

    private
      -- Conjugation by T merges: it is a homomorphism, T • T being ε.
      merge : ∀ {X Y} → (T • (X • T)) • (T • (Y • T)) ≈ T • ((X • Y) • T)
      merge {X} {Y} = begin
        (T • (X • T)) • (T • (Y • T))
          ≈⟨ assoc ⟩
        T • ((X • T) • (T • (Y • T)))
          ≈⟨ cright assoc ⟩
        T • (X • (T • (T • (Y • T))))
          ≈⟨ cright cright sym assoc ⟩
        T • (X • ((T • T) • (Y • T)))
          ≈⟨ cright cright cleft lemma-T-T ⟩
        T • (X • (ε • (Y • T)))
          ≈⟨ cright cright left-unit ⟩
        T • (X • (Y • T))
          ≈⟨ cright sym assoc ⟩
        T • ((X • Y) • T) ∎

      -- T fixes wire 1, so it commutes with H ↑.
      lemma-T-H↑ : T • H ↑ ≈ H ↑ • T
      lemma-T-H↑ = begin
        (Ex • Ex ↑ • Ex) • H ↑
          ≈⟨ by-assoc auto ⟩
        Ex • (Ex ↑ • (Ex • H ↑))
          ≈⟨ cright cright lemma-Ex-H↑ ⟩
        Ex • (Ex ↑ • (H • Ex))
          ≈⟨ cright sym assoc ⟩
        Ex • ((Ex ↑ • H) • Ex)
          ≈⟨ cright cleft sym (lemma-comm-H-w↑ Ex) ⟩
        Ex • ((H • Ex ↑) • Ex)
          ≈⟨ by-assoc auto ⟩
        (Ex • H) • (Ex ↑ • Ex)
          ≈⟨ cleft lemma-Ex-H ⟩
        (H ↑ • Ex) • (Ex ↑ • Ex)
          ≈⟨ by-assoc auto ⟩
        H ↑ • (Ex • Ex ↑ • Ex) ∎

      lemma-T-CZ↑ : T • (CZ ↑ • T) ≈ CZ
      lemma-T-CZ↑ = begin
        T • (CZ ↑ • T)
          ≈⟨ cright cleft sym lemma-T-CZ ⟩
        T • ((T • (CZ • T)) • T)
          ≈⟨ cright assoc ⟩
        T • (T • ((CZ • T) • T))
          ≈⟨ sym assoc ⟩
        (T • T) • ((CZ • T) • T)
          ≈⟨ cleft lemma-T-T ⟩
        ε • ((CZ • T) • T)
          ≈⟨ left-unit ⟩
        (CZ • T) • T
          ≈⟨ assoc ⟩
        CZ • (T • T)
          ≈⟨ cright lemma-T-T ⟩
        CZ • ε
          ≈⟨ right-unit ⟩
        CZ ∎

      -- lemma-yang-baxter gives the other spelling of T, and the two swaps
      -- then cancel in pairs.
      lemma-T-Ex↑ : T • (Ex ↑ • T) ≈ Ex
      lemma-T-Ex↑ = begin
        T • (Ex ↑ • T)
          ≈⟨ cleft sym lemma-yang-baxter ⟩
        (Ex ↑ • Ex ↓ • Ex ↑) • (Ex ↑ • T)
          ≈⟨ by-assoc auto ⟩
        Ex ↑ • (Ex • ((Ex ↑ • Ex ↑) • T))
          ≈⟨ cright cright cleft lemma-Ex↑-Ex↑ ⟩
        Ex ↑ • (Ex • (ε • T))
          ≈⟨ cright cright left-unit ⟩
        Ex ↑ • (Ex • T)
          ≈⟨ by-assoc auto ⟩
        Ex ↑ • ((Ex • Ex) • (Ex ↑ • Ex))
          ≈⟨ cright cleft lemma-Ex-Ex ⟩
        Ex ↑ • (ε • (Ex ↑ • Ex))
          ≈⟨ cright left-unit ⟩
        Ex ↑ • (Ex ↑ • Ex)
          ≈⟨ sym assoc ⟩
        (Ex ↑ • Ex ↑) • Ex
          ≈⟨ cleft lemma-Ex↑-Ex↑ ⟩
        ε • Ex
          ≈⟨ left-unit ⟩
        Ex ∎

      lemma-T-ₕ|ₕ↑ : T • ((H ↑ • CZ ↑ • H ↑) • T) ≈ ʰ|ʰ
      lemma-T-ₕ|ₕ↑ = begin
        T • ((H ↑ • CZ ↑ • H ↑) • T)
          ≈⟨ cright cleft sym assoc ⟩
        T • (((H ↑ • CZ ↑) • H ↑) • T)
          ≈⟨ cright assoc ⟩
        T • ((H ↑ • CZ ↑) • (H ↑ • T))
          ≈⟨ cright cright sym lemma-T-H↑ ⟩
        T • ((H ↑ • CZ ↑) • (T • H ↑))
          ≈⟨ cright assoc ⟩
        T • (H ↑ • (CZ ↑ • (T • H ↑)))
          ≈⟨ sym assoc ⟩
        (T • H ↑) • (CZ ↑ • (T • H ↑))
          ≈⟨ cleft lemma-T-H↑ ⟩
        (H ↑ • T) • (CZ ↑ • (T • H ↑))
          ≈⟨ assoc ⟩
        H ↑ • (T • (CZ ↑ • (T • H ↑)))
          ≈⟨ cright cright sym assoc ⟩
        H ↑ • (T • ((CZ ↑ • T) • H ↑))
          ≈⟨ cright sym assoc ⟩
        H ↑ • ((T • (CZ ↑ • T)) • H ↑)
          ≈⟨ cright cleft lemma-T-CZ↑ ⟩
        H ↑ • (CZ • H ↑) ∎

      lemma-T-⊤⊥↑ : T • (⊤⊥ {n} ↑ • T) ≈ ⊥⊤
      lemma-T-⊤⊥↑ = begin
        T • (⊤⊥ {n} ↑ • T)
          ≈⟨ cright cleft ⊤⊥↑-split ⟩
        T • ((ₕ|ₕ ↑ • Ex ↑) • T)
          ≈⟨ sym merge ⟩
        (T • (ₕ|ₕ ↑ • T)) • (T • (Ex ↑ • T))
          ≈⟨ cong lemma-T-ₕ|ₕ↑ lemma-T-Ex↑ ⟩
        ʰ|ʰ • Ex
          ≈⟨ cleft sym lemma-ʰ|ʰ-conj ⟩
        (Ex • (ₕ|ₕ • Ex)) • Ex
          ≈⟨ assoc ⟩
        Ex • ((ₕ|ₕ • Ex) • Ex)
          ≈⟨ cright assoc ⟩
        Ex • (ₕ|ₕ • (Ex • Ex))
          ≈⟨ cright cright lemma-Ex-Ex ⟩
        Ex • (ₕ|ₕ • ε)
          ≈⟨ cright right-unit ⟩
        Ex • ₕ|ₕ
          ≈⟨ sym lemma-⊥⊤-simple ⟩
        ⊥⊤ ∎

    lemma-selinger-c15 : (⊥⊤ ↓ • CZ ↑) ^ 3 ≈ ε
    lemma-selinger-c15 = begin
      (⊥⊤ • CZ ↑) • ((⊥⊤ • CZ ↑) • (⊥⊤ • CZ ↑))
        ≈⟨ cong conj (cong conj conj) ⟩
      (T • ((tb • CZ) • T)) • ((T • ((tb • CZ) • T)) • (T • ((tb • CZ) • T)))
        ≈⟨ cright merge ⟩
      (T • ((tb • CZ) • T)) • (T • (((tb • CZ) • (tb • CZ)) • T))
        ≈⟨ merge ⟩
      T • (((tb • CZ) • ((tb • CZ) • (tb • CZ))) • T)
        ≈⟨ cright cleft lemma-selinger-c14 ⟩
      T • (ε • T)
        ≈⟨ cright left-unit ⟩
      T • T
        ≈⟨ lemma-T-T ⟩
      ε ∎
      where
      conj : ⊥⊤ • CZ ↑ ≈ T • ((tb • CZ) • T)
      conj = begin
        ⊥⊤ • CZ ↑
          ≈⟨ cong (sym lemma-T-⊤⊥↑) (sym lemma-T-CZ) ⟩
        (T • (tb • T)) • (T • (CZ • T))
          ≈⟨ merge ⟩
        T • ((tb • CZ) • T) ∎

    lemma-⊥⊤↑-CZ02 : ⊥⊤ {n} ↑ • CZ02 ≈ CZ • ⊥⊤ {n} ↑
    lemma-⊥⊤↑-CZ02 = •-cancelˡ {g = ⊤⊥ {n} ↑} (begin
      ⊤⊥ {n} ↑ • (⊥⊤ {n} ↑ • CZ02)
        ≈⟨ sym assoc ⟩
      (⊤⊥ {n} ↑ • ⊥⊤ {n} ↑) • CZ02
        ≈⟨ cleft (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-⊥⊤ n)) ⟩
      ε • CZ02
        ≈⟨ left-unit ⟩
      CZ02
        ≈⟨ sym right-unit ⟩
      CZ02 • ε
        ≈⟨ cright sym (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-⊥⊤ n)) ⟩
      CZ02 • (⊤⊥ {n} ↑ • ⊥⊤ {n} ↑)
        ≈⟨ sym assoc ⟩
      (CZ02 • ⊤⊥ {n} ↑) • ⊥⊤ {n} ↑
        ≈⟨ cleft sym lemma-⊤⊥↑-CZ ⟩
      (⊤⊥ {n} ↑ • CZ) • ⊥⊤ {n} ↑
        ≈⟨ assoc ⟩
      ⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑) ∎)
