------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 1's words, read in the rule set with -1.
--
-- Translation's `new` sends ν = -ω to -1 • ω and each gate to itself,
-- so the image Gʷ w of a Figure-1 word w is its gate part, embedded,
-- interleaved with copies of -1 • ω.  This module computes that image
-- for every word Figure 1's rules are written over, in the form the
-- rules need it: the gate part as one embedded Paper-V0 circuit ⌜ u ⌝,
-- with the scalars collected on the right as powers of ω and -1.
--
--     H, S, CZ, X, Z, CX, their powers and shifts    ⌜ u ⌝ on the nose
--     ω^ t                                           ω^ t, i.e. ω ^ toℕ t
--     λ²  = (-1)^((p-1)/2)                           -1 ^ ((p-1)/2)
--     (a/p)_L                                        the sign of a
--     M_a = (T1)                                     ⌜ XM a ⌝ • sign a
--                                                      • ω^ (M-phase a)
--     SWAP = (T4)                                    ⌜ Ex ⌝ • -1 ^ ((p-1)/2)
--
-- The multiplier's gate part is Figure 1 mod scalars' XM a, which spells
-- the exponent of its Z prefix (a⁻¹ - 1)/2 where T1 has (1 - a)/(2a);
-- `M-Z-exponent≡` identifies the two.
--
-- Scalar words are central (ω and -1 commute with every letter), and
-- the module ends with the bookkeeping that moving them uses.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Images
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_ ; [m+kn]%n≡m%n)
open import Data.Product using (proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; wmap ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)

open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime
  using (toℕ-+)

import Examples.Groups.Clifford+MinusOne.Qupit.Syntactics
  p-3 p-prime g* g-gen as N
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics
  p-3 p-prime g* g-gen as F
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.Syntactics
  p-3 p-prime g* g-gen as FQ
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Legendre
  p-3 p-prime g* g-gen as L
import Examples.Groups.Clifford+MinusOne.Qupit.Translation
  p-3 p-prime g* g-gen as T

open T using (Alph ; _≈±_ ; Gʷ ; ⇑)
module FQR = FQ.Clifford-Relations

open FQ using (Gen ; S ; H ; CZ ; S^ ; CZ^ ; Ex ; CX ; _↑ ; _↓)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Embedding and powers

⌜^⌝ : (u : Word (Gen n)) (k : ℕ) → N.⌜ u ^ k ⌝ ≡ N.⌜ u ⌝ ^ k
⌜^⌝ u k = Eq.trans (Eq.cong (wmap inj₁) (T.wmap-^ inj₂ u k))
                   (T.wmap-^ inj₁ (wmap inj₂ u) k)

G^ : (w : Word (F.Gen n)) (k : ℕ) → Gʷ (w ^ k) ≡ Gʷ w ^ k
G^ w k = T.ʷ-^ T.new w k

-- A Figure-1 word whose image is an embedded circuit keeps that
-- property under powers.
G-pow : (w : Word (F.Gen n)) (u : Word (Gen n)) → Gʷ w ≡ N.⌜ u ⌝ →
        ∀ k → Gʷ (w ^ k) ≡ N.⌜ u ^ k ⌝
G-pow w u e k =
  Eq.trans (G^ w k) (Eq.trans (Eq.cong (_^ k) e) (Eq.sym (⌜^⌝ u k)))

-- … and under the shift.
G-↑ : (w : Word (F.Gen n)) (u : Word (Gen n)) → Gʷ w ≡ N.⌜ u ⌝ →
      Gʷ (w F.↑) ≡ N.⌜ u ↑ ⌝
G-↑ w u e = Eq.trans (T.G-↑ w) (Eq.trans (Eq.cong ⇑ e) (T.⇑-⌜⌝ u))

------------------------------------------------------------------------
-- The gate words

G-S^ : (y : ℤ ₚ) → Gʷ (F.S^ {n} y) ≡ N.⌜ S^ y ⌝
G-S^ y = G-pow F.S S Eq.refl (toℕ y)

G-S⁻¹ : Gʷ (F.S⁻¹ {n}) ≡ N.⌜ FQ.S⁻¹ ⌝
G-S⁻¹ = G-pow F.S S Eq.refl p-1

G-Z : Gʷ (F.Z {n}) ≡ N.⌜ FQR.Z ⌝
G-Z = Eq.cong
  (λ t → N.⌜ H ⌝ • (N.⌜ H ⌝ • (N.⌜ S ⌝ • (N.⌜ H ⌝ • (N.⌜ H ⌝ • t)))))
  G-S⁻¹

G-X : Gʷ (F.X {n}) ≡ N.⌜ FQR.X ⌝
G-X = Eq.cong
  (λ t → N.⌜ H ⌝ • (N.⌜ S ⌝ • (N.⌜ H ⌝ • (N.⌜ H ⌝ • (t • N.⌜ H ⌝)))))
  G-S⁻¹

G-Z^ : (y : ℤ ₚ) → Gʷ (F.Z^ {n} y) ≡ N.⌜ FQR.Z^ y ⌝
G-Z^ y = G-pow F.Z FQR.Z G-Z (toℕ y)

G-X^ : (y : ℤ ₚ) → Gʷ (F.X^ {n} y) ≡ N.⌜ FQR.X^ y ⌝
G-X^ y = G-pow F.X FQR.X G-X (toℕ y)

G-CZ^ : (y : ℤ ₚ) → Gʷ (F.CZ^ {n} y) ≡ N.⌜ CZ^ y ⌝
G-CZ^ y = G-pow F.CZ CZ Eq.refl (toℕ y)

G-CX : Gʷ (F.CX {n}) ≡ N.⌜ CX ⌝
G-CX = Eq.refl

------------------------------------------------------------------------
-- The scalars

module Scalars (n : ℕ) where

  open T.Algebra n
  open SR word-setoid

  -- ω to a power in ℤₚ.
  ωℤ : ℤ ₚ → Word (Alph n)
  ωℤ t = N.ω± ^ toℕ t

  G-ν^ : (k : ℕ) → Gʷ (F.ν {n} ^ k) ≡ N.-ω± ^ k
  G-ν^ k = G^ F.ν k

  -- (-ω)^p is -1 and (-ω)^(p+1) is ω: the round trips of Translation.
  G--1 : Gʷ (F.-1ˢ {n}) ≈ N.-1±
  G--1 = sym (T.new-left-inv-gen (inj₂ tt))

  G-ω : Gʷ (F.ωˢ {n}) ≈ N.ω±
  G-ω = sym (T.new-left-inv-gen (inj₁ (inj₁ tt)))

  G-ω^ : (t : ℤ ₚ) → Gʷ (F.ω^ {n} t) ≈ ωℤ t
  G-ω^ t = trans (refl' (G^ F.ωˢ (toℕ t))) (^-cong _ _ (toℕ t) G-ω)

  G-λ² : Gʷ (F.λ² {n}) ≈ N.-1± ^ F.p-1/2
  G-λ² = trans (refl' (G^ F.-1ˢ F.p-1/2)) (^-cong _ _ F.p-1/2 G--1)

  -- The Legendre symbol, as a sign: Legendre.Signs at -1.
  module Sg = L.Signs (n N.Exact±,_===_) N.-1± -1²≈ε

  G-legendre-by : ∀ {y : ℤ ₚ} (d : Dec (toℕ y Eq.≡ 1)) →
                  Gʷ (F.legendre-by {n} d) ≈ Sg.sign-by d
  G-legendre-by (yes _) = refl
  G-legendre-by (no _)  = G--1

  G-legendre : (x : ℤ* ₚ) → Gʷ (F.legendre {n} x) ≈ Sg.sign x
  G-legendre x = G-legendre-by (F.is-one (toℕ (x .proj₁ ^′ F.p-1/2)))

  --------------------------------------------------------------------
  -- Central words

  Central : Word (Alph n) → Set
  Central s = ∀ w → w • s ≈ s • w

  central-• : ∀ {s t} → Central s → Central t → Central (s • t)
  central-• cs ct w =
    trans (sym assoc)
      (trans (cong (cs w) refl)
        (trans assoc (trans (cong refl (ct w)) (sym assoc))))

  central-ε : Central ε
  central-ε w = trans right-unit (sym left-unit)

  central-ω : ∀ k → Central (N.ω± ^ k)
  central-ω k w = ω^-central k w

  central--1 : ∀ k → Central (N.-1± ^ k)
  central--1 k w = -1^-central k w

  central-sign-by : ∀ {y : ℤ ₚ} (d : Dec (toℕ y Eq.≡ 1)) →
                    Central (Sg.sign-by d)
  central-sign-by (yes _) = central-ε
  central-sign-by (no _)  = -1-central

  central-sign : ∀ x → Central (Sg.sign x)
  central-sign x = central-sign-by (F.is-one (toℕ (x .proj₁ ^′ F.p-1/2)))

  -- Swapping a central word out to the right of a product.
  collect : ∀ a b {s t} → Central s →
            (a • s) • (b • t) ≈ (a • b) • (s • t)
  collect a b {s} {t} cs = begin
    (a • s) • (b • t)   ≈⟨ assoc ⟩
    a • (s • (b • t))   ≈⟨ cright sym assoc ⟩
    a • ((s • b) • t)   ≈⟨ cright cleft sym (cs b) ⟩
    a • ((b • s) • t)   ≈⟨ cright assoc ⟩
    a • (b • (s • t))   ≈⟨ sym assoc ⟩
    (a • b) • (s • t)   ∎

  -- Exponent arithmetic for ω and -1.
  ωℤ-+ : ∀ a b → ωℤ a • ωℤ b ≈ ωℤ (a + b)
  ωℤ-+ a b = begin
    N.ω± ^ toℕ a • N.ω± ^ toℕ b          ≈⟨ sym (^-+ N.ω± (toℕ a) (toℕ b)) ⟩
    N.ω± ^ (toℕ a Nat.+ toℕ b)           ≈⟨ ω^-mod (toℕ a Nat.+ toℕ b) ⟩
    N.ω± ^ ((toℕ a Nat.+ toℕ b) % p)
      ≡⟨ Eq.cong (N.ω± ^_) (Eq.sym (toℕ-+ a b)) ⟩
    N.ω± ^ toℕ (a + b)                   ∎

  ωℤ-* : ∀ a b → ωℤ a ^ toℕ b ≈ ωℤ (a * b)
  ωℤ-* a b = begin
    (N.ω± ^ toℕ a) ^ toℕ b               ≈⟨ ^^ N.ω± (toℕ a) (toℕ b) ⟩
    N.ω± ^ (toℕ a Nat.* toℕ b)           ≈⟨ ω^-mod (toℕ a Nat.* toℕ b) ⟩
    N.ω± ^ ((toℕ a Nat.* toℕ b) % p)
      ≡⟨ Eq.cong (N.ω± ^_) (lemma-toℕ-% a b) ⟩
    N.ω± ^ toℕ (a * b)                   ∎

  ωℤ-cong : ∀ {a b} → a ≡ b → ωℤ a ≈ ωℤ b
  ωℤ-cong e = refl' (Eq.cong ωℤ e)

  -- An even power of -1 vanishes.
  -1^-double : ∀ k → N.-1± ^ k • N.-1± ^ k ≈ ε
  -1^-double k = begin
    N.-1± ^ k • N.-1± ^ k        ≈⟨ sym (^-+ N.-1± k k) ⟩
    N.-1± ^ (k Nat.+ k)          ≈⟨ -1^-mod (k Nat.+ k) ⟩
    N.-1± ^ ((k Nat.+ k) % 2)    ≡⟨ Eq.cong (N.-1± ^_) even ⟩
    ε                            ∎
    where
    even : (k Nat.+ k) % 2 ≡ 0
    even = Eq.trans (Eq.cong (_% 2) shape) ([m+kn]%n≡m%n 0 k 2)
      where
      shape : k Nat.+ k ≡ 0 Nat.+ k Nat.* 2
      shape = Eq.trans (Eq.cong (k Nat.+_) (Eq.sym (NP.+-identityʳ k)))
                       (NP.*-comm 2 k)

  --------------------------------------------------------------------
  -- Shifting scalar words leaves them alone

  ⇑-ω^ : ∀ k → ⇑ (N.ω± {n} ^ k) ≡ N.ω± ^ k
  ⇑-ω^ k = T.wmap-^ T.shift± N.ω± k

  ⇑--1^ : ∀ k → ⇑ (N.-1± {n} ^ k) ≡ N.-1± ^ k
  ⇑--1^ k = T.wmap-^ T.shift± N.-1± k

  ⇑-sign-by : ∀ {y : ℤ ₚ} (d : Dec (toℕ y Eq.≡ 1)) →
              ⇑ (Sg.sign-by d) ≡ L.Signs.sign-by ((₁₊ n) N.Exact±,_===_)
                                    N.-1± (T.Algebra.-1²≈ε (₁₊ n)) d
  ⇑-sign-by (yes _) = Eq.refl
  ⇑-sign-by (no _)  = Eq.refl

------------------------------------------------------------------------
-- The multiplier, T1

-- T1's Z-exponent (1 - a)/(2a) is Figure 1 mod scalars' (a⁻¹ - 1)/2.
M-Z-exponent≡ : (x : ℤ* ₚ) →
                F.M-Z-exponent x ≡ (((x ⁻¹) .proj₁) + - ₁) * F.1/2
M-Z-exponent≡ x = begin
  (₁ + - a) * F.1/2 * a⁻¹       ≡⟨ *-assoc (₁ + - a) F.1/2 a⁻¹ ⟩
  (₁ + - a) * (F.1/2 * a⁻¹)     ≡⟨ Eq.cong ((₁ + - a) *_) (*-comm F.1/2 a⁻¹) ⟩
  (₁ + - a) * (a⁻¹ * F.1/2)     ≡⟨ Eq.sym (*-assoc (₁ + - a) a⁻¹ F.1/2) ⟩
  (₁ + - a) * a⁻¹ * F.1/2       ≡⟨ Eq.cong (_* F.1/2) inner ⟩
  (a⁻¹ + - ₁) * F.1/2           ∎
  where
  open Eq.≡-Reasoning
  a = x .proj₁
  a⁻¹ = (x ⁻¹) .proj₁

  aa⁻¹ : a * a⁻¹ ≡ ₁
  aa⁻¹ = lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = x .proj₂}}}

  inner : (₁ + - a) * a⁻¹ ≡ a⁻¹ + - ₁
  inner = begin
    (₁ + - a) * a⁻¹         ≡⟨ *-distribʳ-+ a⁻¹ ₁ (- a) ⟩
    ₁ * a⁻¹ + (- a) * a⁻¹   ≡⟨ Eq.cong₂ _+_ (*-identityˡ a⁻¹) (neg-* a a⁻¹) ⟩
    a⁻¹ + - (a * a⁻¹)       ≡⟨ Eq.cong (λ t → a⁻¹ + - t) aa⁻¹ ⟩
    a⁻¹ + - ₁               ∎
    where
    neg-* : ∀ (u v : ℤ ₚ) → (- u) * v ≡ - (u * v)
    neg-* u v = Eq.trans (*-assoc ₋₁ u v) Eq.refl

module Multiplier (n : ℕ) where

  open T.Algebra (₁₊ n)
  open Scalars (₁₊ n)
  open SR word-setoid
  open PP ((₁₊ n) N.Exact±,_===_) using (module Pattern-Assoc)
  open Pattern-Assoc

  -- The scalar M_a carries, read on this side.
  M-scalar : ℤ* ₚ → Word (Alph (₁₊ n))
  M-scalar x = Sg.sign x • ωℤ (F.M-phase x)

  central-M-scalar : ∀ x → Central (M-scalar x)
  central-M-scalar x =
    central-• (central-sign x) (central-ω (toℕ (F.M-phase x)))

  G-M : (x : ℤ* ₚ) → Gʷ (F.M {n} x) ≈ N.⌜ FQR.XM x ⌝ • M-scalar x
  G-M x = begin
    Gʷ (F.M x)
      ≡⟨ shape ⟩
    N.⌜ FQR.Z^ γ ⌝ • (N.⌜ FQR.X^ δ ⌝ • (N.⌜ S^ a⁻¹ ⌝ • (N.⌜ H ⌝
      • (N.⌜ S^ a ⌝ • (N.⌜ H ⌝ • (N.⌜ S^ a⁻¹ ⌝ • (N.⌜ H ⌝
      • (Gʷ (F.legendre x) • Gʷ (F.ω^ (F.M-phase x))))))))))
      ≈⟨ by-passoc (□ ^ 10) (□ ^ 8 • □ ^ 2) Eq.refl ⟩
    N.⌜ FQR.XM x ⌝ • (Gʷ (F.legendre x) • Gʷ (F.ω^ (F.M-phase x)))
      ≈⟨ cright cong (G-legendre x) (G-ω^ (F.M-phase x)) ⟩
    N.⌜ FQR.XM x ⌝ • M-scalar x
      ∎
    where
    a = x .proj₁
    a⁻¹ = (x ⁻¹) .proj₁
    γ = (a⁻¹ + - ₁) * F.1/2
    δ = (₁ + - a) * F.1/2

    shape : Gʷ (F.M x) ≡
            N.⌜ FQR.Z^ γ ⌝ • (N.⌜ FQR.X^ δ ⌝ • (N.⌜ S^ a⁻¹ ⌝ • (N.⌜ H ⌝
              • (N.⌜ S^ a ⌝ • (N.⌜ H ⌝ • (N.⌜ S^ a⁻¹ ⌝ • (N.⌜ H ⌝
              • (Gʷ (F.legendre x) • Gʷ (F.ω^ (F.M-phase x))))))))))
    shape =
      Eq.cong₂ _•_
        (Eq.trans (G-Z^ (F.M-Z-exponent x))
                  (Eq.cong (λ e → N.⌜ FQR.Z^ e ⌝) (M-Z-exponent≡ x)))
        (Eq.cong₂ _•_ (G-X^ δ)
          (Eq.cong₂ _•_ (G-S^ a⁻¹)
            (Eq.cong (N.⌜ H ⌝ •_)
              (Eq.cong₂ _•_ (G-S^ a)
                (Eq.cong (N.⌜ H ⌝ •_)
                  (Eq.cong₂ _•_ (G-S^ a⁻¹) Eq.refl))))))

------------------------------------------------------------------------
-- The swap, T4

module Swap (n : ℕ) where

  open T.Algebra (₂₊ n)
  open Scalars (₂₊ n)
  open SR word-setoid
  open PP ((₂₊ n) N.Exact±,_===_) using (module Pattern-Assoc)
  open Pattern-Assoc

  λ²± : Word (Alph (₂₊ n))
  λ²± = N.-1± ^ F.p-1/2

  G-SWAP : Gʷ (F.SWAP {n}) ≈ N.⌜ Ex ⌝ • λ²±
  G-SWAP = trans (by-passoc (□ ^ 10) (□ ^ 9 • □) Eq.refl) (cright G-λ²)
