------------------------------------------------------------------------
-- Figure 1 and Figure1-MS: changing only C4.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ ; inject₁ ; fromℕ<)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; _×_ ; ∃ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.FF-Iso
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_ ; _/_ ; m%n<n ; m≡m%n+[m/n]*n)
open import Data.Fin.Properties using (toℕ-fromℕ< ; toℕ-inject₁)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR
open import Word.Base using (Word ; WRel ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.SemiMS
  p-3 p-prime g* g-gen as Arithmetic
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime using (toℕ-+)
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics
  p-3 p-prime g* g-gen as F
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.Syntactics
  p-3 p-prime g* g-gen as F′
open F using (Gen ; H ; S ; Z ; S⁻¹ ; S^ ; Z^ ; ν ; M ; Mg ; M₋₁ ; -1ˢ ; p-1/2)
open Primitive-Root-Modp' g* g-gen

import Examples.Groups.ProjectiveClifford.Qupit.Shared.PauliBase
  p-3 p-prime g* g-gen as Shared

private
  twice-half : ∀ x → x * F.1/2 + x * F.1/2 ≡ x
  twice-half x = Eq.trans (Eq.cong₂ _+_ (*-comm x F.1/2) (*-comm x F.1/2))
                          (Shared.aux-half-half x)

  subtract-difference : ∀ b t → b + - (b + - t) ≡ t
  subtract-difference b t = Eq.trans (Eq.cong (b +_) (Shared.neg-+ b (- t)))
    (Eq.trans (Eq.cong (λ x → b + (- b + x)) (Shared.neg-involutive t))
      (Eq.trans (Eq.sym (+-assoc b (- b) t))
        (Eq.trans (Eq.cong (_+ t) (+-inverseʳ b)) (+-identityˡ t))))

  subtract-twice : ∀ b t →
    (b + - ((b + - t) * F.1/2)) + - ((b + - t) * F.1/2) ≡ t
  subtract-twice b t = Eq.trans (+-assoc b (- h) (- h))
    (Eq.trans (Eq.cong (b +_) (Eq.sym (Shared.neg-+ h h)))
      (Eq.trans (Eq.cong (λ x → b + - x) (twice-half (b + - t)))
        (subtract-difference b t)))
    where h = (b + - t) * F.1/2

  c-alt : Arithmetic.c ≡ (Arithmetic.d + - F.g⁻¹) * F.1/2
  c-alt = Eq.trans (*-assoc (₁ + - g) F.1/2 Arithmetic.d)
    (Eq.trans (Eq.cong ((₁ + - g) *_) (*-comm F.1/2 Arithmetic.d))
      (Eq.trans (Eq.sym (*-assoc (₁ + - g) Arithmetic.d F.1/2))
        (Eq.cong (_* F.1/2) (Eq.trans (*-distribʳ-+ Arithmetic.d ₁ (- g))
          (Eq.cong₂ _+_ (*-identityˡ Arithmetic.d)
            (Eq.trans (Shared.neg-* g Arithmetic.d)
              (Eq.cong -_ (Eq.trans (Eq.sym (*-assoc g F.g⁻¹ F.g⁻¹))
                (Eq.trans (Eq.cong (_* F.g⁻¹)
                  (lemma-⁻¹ʳ g {{nztoℕ {y = g} {neq0 = g≠0}}}))
                  (*-identityˡ F.g⁻¹))))))))))

  old-action : (Arithmetic.d + - Arithmetic.c) + - Arithmetic.c ≡ F.g⁻¹
  old-action = Eq.trans (Eq.cong (λ x → (Arithmetic.d + - x) + - x) c-alt)
                         (subtract-twice Arithmetic.d F.g⁻¹)

  new-action : ((g * g) + - Arithmetic.e) + - Arithmetic.e ≡ g
  new-action = subtract-twice (g * g) g

-- The following calculus is parameterised by the SHARED axioms only.
-- In particular, it has no C4 hypothesis and no semantic imports.
module Common (n : ℕ) (Γ : WRel (Gen (₁₊ n)))
  (c0 : let open PB Γ in ν ^ (p Nat.+ p) ≈ ε)
  (c1 : let open PB Γ in S ^ p ≈ ε)
  (c2 : let open PB Γ in H ^ 2 ≈ M₋₁ • -1ˢ ^ p-1/2)
  (c3 : let open PB Γ in ∀ k → Mg ^ toℕ k ≈ M (g^ k))
  (c5 : let open PB Γ in S • H • H • S • H • H ≈ H • H • S • H • H • S)
  (central : let open PB Γ in ∀ k w → ν ^ k • w ≈ w • ν ^ k)
  where

  open PB Γ
  open PP Γ
  open SR word-setoid

  M-cong : ∀ x y → x .proj₁ ≡ y .proj₁ → M {n} x ≡ M y
  M-cong (x , _) (.x , _) Eq.refl = Eq.refl

  pow-mod : ∀ (w : Word (Gen (₁₊ n))) (r : ℕ) →
    .{{_ : Nat.NonZero r}} → w ^ r ≈ ε → ∀ m → w ^ m ≈ w ^ (m % r)
  pow-mod w r ord m = begin
    w ^ m ≡⟨ Eq.cong (w ^_) (m≡m%n+[m/n]*n m r) ⟩
    w ^ (m % r Nat.+ (m / r) Nat.* r)
      ≈⟨ ^-+ w (m % r) ((m / r) Nat.* r) ⟩
    w ^ (m % r) • w ^ ((m / r) Nat.* r)
      ≈⟨ cright trans (refl' (Eq.cong (w ^_) (NP.*-comm (m / r) r)))
          (trans (sym (^^ w r (m / r)))
            (trans (^-cong (w ^ r) ε (m / r) ord) (ε^k=ε (m / r)))) ⟩
    w ^ (m % r) • ε ≈⟨ right-unit ⟩
    w ^ (m % r) ∎

  M1 : M (₁ , λ ()) ≈ ε
  M1 = trans (refl' (M-cong (₁ , λ ()) (g^ ₀) Eq.refl)) (sym (c3 ₀))

  Mg-order : Mg ^ p-1 ≈ ε
  Mg-order = begin
    Mg ^ p-1
      ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    Mg ^ toℕ k ≈⟨ c3 k ⟩
    M (g^ k) ≡⟨ M-cong (g^ k) (₁ , λ ()) value ⟩
    M (₁ , λ ()) ≈⟨ M1 ⟩
    ε ∎
    where
    k = fromℕ< (NP.n<1+n p-1)
    value = Eq.trans (Eq.cong (g ^′_) (toℕ-fromℕ< (NP.n<1+n p-1)))
                     Fermat's-little-theorem'

  M-log : ∀ x → M x ≈ Mg ^ toℕ (inject₁ (g-gen x .proj₁))
  M-log x = trans (refl' (M-cong x (g^ k) (Eq.sym (lemma-log-inject x))))
                  (sym (c3 k))
    where k = inject₁ (g-gen x .proj₁)

  M-mul : ∀ x y → M x • M y ≈ M (x *' y)
  M-mul x y = begin
    M x • M y ≈⟨ cong (M-log x) (M-log y) ⟩
    Mg ^ toℕ k • Mg ^ toℕ l ≈⟨ sym (^-+ Mg (toℕ k) (toℕ l)) ⟩
    Mg ^ t ≈⟨ pow-mod Mg p-1 Mg-order t ⟩
    Mg ^ (t % p-1) ≡⟨ Eq.cong (Mg ^_) (Eq.sym repr) ⟩
    Mg ^ toℕ q ≈⟨ c3 q ⟩
    M (g^ q) ≡⟨ M-cong (g^ q) (x *' y) value ⟩
    M (x *' y) ∎
    where
    k = inject₁ (g-gen x .proj₁)
    l = inject₁ (g-gen y .proj₁)
    t = toℕ k Nat.+ toℕ l
    q = inject₁ (fromℕ< (m%n<n t p-1))
    repr = Eq.trans (toℕ-inject₁ (fromℕ< (m%n<n t p-1)))
                    (toℕ-fromℕ< (m%n<n t p-1))
    value = Eq.trans (Eq.cong (g ^′_) repr)
      (Eq.trans (Eq.sym (aux-g^′-% t))
        (Eq.trans (Eq.sym (+-^′-distribʳ g (toℕ k) (toℕ l)))
          (Eq.cong₂ _*_ (lemma-log-inject x) (lemma-log-inject y))))

  minus-square : M₋₁ ^ 2 ≈ ε
  minus-square = trans (M-mul -'₁ -'₁)
    (trans (refl' (M-cong (-'₁ *' -'₁) (₁ , λ ()) value)) M1)
    where
    open import Algebra.Properties.Ring (+-*-ring p-2)
    value = Eq.trans (-1*x≈-x (- ₁)) (-‿involutive ₁)

  phase-square : (-1ˢ ^ p-1/2) ^ 2 ≈ ε
  phase-square = begin
    (-1ˢ ^ p-1/2) ^ 2 ≈⟨ ^^' -1ˢ p-1/2 2 ⟩
    (-1ˢ ^ 2) ^ p-1/2
      ≈⟨ ^-cong (-1ˢ ^ 2) ε p-1/2 (trans (sym (^-+ ν p p)) c0) ⟩
    ε ^ p-1/2 ≈⟨ ε^k=ε p-1/2 ⟩
    ε ∎

  phase-central : ∀ w → (-1ˢ ^ p-1/2) • w ≈ w • (-1ˢ ^ p-1/2)
  phase-central w = comm⇒pow-comm p-1/2 1 (central p w)

  H-order : H ^ 4 ≈ ε
  H-order = begin
    H ^ 4 ≈⟨ sym (^^ H 2 2) ⟩
    (H ^ 2) ^ 2 ≈⟨ ^-cong (H ^ 2) (M₋₁ • -1ˢ ^ p-1/2) 2 c2 ⟩
    (M₋₁ • -1ˢ ^ p-1/2) ^ 2
      ≈⟨ ^-• M₋₁ (-1ˢ ^ p-1/2) 2 (sym (phase-central M₋₁)) ⟩
    M₋₁ ^ 2 • (-1ˢ ^ p-1/2) ^ 2 ≈⟨ cong minus-square phase-square ⟩
    ε • ε ≈⟨ left-unit ⟩
    ε ∎

  J : Word (Gen (₁₊ n))
  J = H • H

  J-square : J • J ≈ ε
  J-square = trans (by-assoc auto) H-order

  J-Mg : J • Mg ≈ Mg • J
  J-Mg = begin
    J • Mg ≈⟨ cleft c2 ⟩
    (M₋₁ • -1ˢ ^ p-1/2) • Mg ≈⟨ assoc ⟩
    M₋₁ • ((-1ˢ ^ p-1/2) • Mg) ≈⟨ cright phase-central Mg ⟩
    M₋₁ • (Mg • -1ˢ ^ p-1/2) ≈⟨ sym assoc ⟩
    (M₋₁ • Mg) • -1ˢ ^ p-1/2
      ≈⟨ cleft trans (cong (M-log -'₁) refl)
          (trans (pow-comm Mg (toℕ (inject₁ (g-gen -'₁ .proj₁))) 1)
            (cong refl (sym (M-log -'₁)))) ⟩
    (Mg • M₋₁) • -1ˢ ^ p-1/2 ≈⟨ assoc ⟩
    Mg • (M₋₁ • -1ˢ ^ p-1/2) ≈⟨ cright sym c2 ⟩
    Mg • J ∎

  lemma-comm-SHHS^kHH :
    ∀ k → S • H • H • S ^ k • H • H ≈ (H • H • S ^ k • H • H) • S
  lemma-comm-SHHS^kHH k@0 = begin
    S • H • H • ε • H • H      ≈⟨ by-assoc auto ⟩
    S • H • H • H • H          ≈⟨ cright H-order ⟩
    S • ε                      ≈⟨ trans right-unit (sym left-unit) ⟩
    ε • S                      ≈⟨ cleft sym H-order ⟩
    (H • H • H • H) • S        ≈⟨ by-assoc auto ⟩
    (H • H • ε • H • H) • S ∎
    where

    open Pattern-Assoc

  lemma-comm-SHHS^kHH k@1 = by-assoc-and c5 auto auto
  lemma-comm-SHHS^kHH k@(₁₊ k'@(₁₊ k'')) = begin
    S • H • H • S ^ k • H • H
      ≈⟨ refl ⟩
    S • H • H • (S • S ^ k') • H • H
      ≈⟨ cright cright cright cleft cright sym left-unit ⟩
    S • H • H • (S • ε • S ^ k') • H • H
      ≈⟨ cright cright cright cleft cright cleft sym H-order ⟩
    S • H • H • (S • (H • H • H • H) • S ^ k') • H • H
      ≈⟨ by-passoc (□ • □ • □ • (□ • □ ^ 4 • □) • □ ^ 2) (□ ^ 6 • □ ^ 5) auto ⟩
    (S • H • H • S • H • H) • H • H • S ^ k' • H • H
      ≈⟨ cleft c5 ⟩
    (H • H • S • H • H • S) • H • H • S ^ k' • H • H
      ≈⟨ by-passoc (□ ^ 6 • □ ^ 5) (□ ^ 5 • □ ^ 6) auto ⟩
    (H • H • S • H • H) • S • H • H • S ^ k' • H • H
      ≈⟨ cright lemma-comm-SHHS^kHH k' ⟩
    (H • H • S • H • H) • (H • H • S ^ k' • H • H) • S
      ≈⟨ by-passoc (□ ^ 5 • □ ^ 5 • □) (□ ^ 7 • □ ^ 4) auto ⟩
    (H • H • S • H • H • H • H) • S ^ k' • H • H • S
      ≈⟨ cleft (cright cright trans (cright H-order) right-unit) ⟩
    (H • H • S) • S ^ k' • H • H • S
      ≈⟨ by-passoc (□ ^ 3 • □ ^ 4) (□ • □ • □ ^ 2 • □ ^ 3) auto ⟩
    H • H • (S • S ^ k') • H • H • S
      ≈⟨ by-passoc (□ ^ 6) (□ ^ 5 • □) auto ⟩
    (H • H • S ^ k • H • H) • S ∎
    where

    open Pattern-Assoc

  lemma-Z^k-ℕ : ∀ k → Z ^ k ≈ H • H • S ^ k • H • H • S⁻¹ ^ k
  lemma-Z^k-ℕ k@0 = sym (by-assoc-and H-order auto auto)
  lemma-Z^k-ℕ k@1 = refl
  lemma-Z^k-ℕ k@(₁₊ k'@(₁₊ k'')) = begin
    Z • Z ^ k'
      ≈⟨ cright lemma-Z^k-ℕ k' ⟩
    Z • H • H • S ^ k' • H • H • S⁻¹ ^ k'
      ≈⟨ refl ⟩
    (H • H • S • H • H • S⁻¹) • H • H • S ^ k' • H • H • S⁻¹ ^ k'
      ≈⟨ by-passoc (□ ^ 6 • □ ^ 6) (□ ^ 5 • □ ^ 6 • □) auto ⟩
    (H • H • S • H • H) • (S⁻¹ • H • H • S ^ k' • H • H) • S⁻¹ ^ k'
      ≈⟨ cright cleft comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH k') ⟩
    (H • H • S • H • H) • ((H • H • S ^ k' • H • H) • S⁻¹) • S⁻¹ ^ k'
      ≈⟨ by-passoc (□ ^ 5 • (□ ^ 5 • □) • □) (□ ^ 7 • □ ^ 3 • □ ^ 2) auto ⟩
    (H • H • S • H • H • H • H) • (S ^ k' • H • H) • S⁻¹ • S⁻¹ ^ k'
      ≈⟨ cleft (cright cright trans (cright H-order) right-unit) ⟩
    (H • H • S) • (S ^ k' • H • H) • S⁻¹ ^ ₁₊ k'
      ≈⟨ by-passoc (□ ^ 3 • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (H • H) • (S • S ^ k') • H • H • S⁻¹ ^ ₁₊ k'
      ≈⟨ refl ⟩
    (H • H) • S ^ ₁₊ k' • H • H • S⁻¹ ^ ₁₊ k'
      ≈⟨ assoc ⟩
    H • H • S ^ k • H • H • S⁻¹ ^ k ∎
    where

    open Pattern-Assoc


  Z-order : Z ^ p ≈ ε
  Z-order = begin
    Z ^ p ≈⟨ lemma-Z^k-ℕ p ⟩
    H • H • S ^ p • H • H • S⁻¹ ^ p
      ≈⟨ cright cright cong c1 (cright cright
        trans (^^' S p-1 p) (trans (^-cong (S ^ p) ε p-1 c1) (ε^k=ε p-1))) ⟩
    H • H • ε • H • H • ε ≈⟨ by-assoc auto ⟩
    H ^ 4 ≈⟨ H-order ⟩
    ε ∎

  Z-S : Z • S ≈ S • Z
  Z-S = begin
    Z • S ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H) • (S⁻¹ • S)
      ≈⟨ cright pow-comm S p-1 1 ⟩
    (H • H • S • H • H) • (S • S⁻¹) ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H • S) • S⁻¹ ≈⟨ cleft sym c5 ⟩
    (S • H • H • S • H • H) • S⁻¹ ≈⟨ by-assoc auto ⟩
    S • Z ∎

  pow-+ : ∀ w → w ^ p ≈ ε → ∀ a b →
    w ^ toℕ a • w ^ toℕ b ≈ w ^ toℕ (a + b)
  pow-+ w ord a b = trans (sym (^-+ w (toℕ a) (toℕ b)))
    (trans (pow-mod w p ord _) (refl' (Eq.cong (w ^_) (Eq.sym (toℕ-+ a b)))))

  pow-* : ∀ w → w ^ p ≈ ε → ∀ a b →
    (w ^ toℕ a) ^ toℕ b ≈ w ^ toℕ (a * b)
  pow-* w ord a b = trans (^^ w (toℕ a) (toℕ b))
    (trans (pow-mod w p ord _) (refl' (Eq.cong (w ^_) (lemma-toℕ-% a b))))

  S-inverse : S • S⁻¹ ≈ ε
  S-inverse = trans (sym (^-+ S 1 p-1)) c1

  cancel-S : ∀ {a b} → a • S ≈ b • S → a ≈ b
  cancel-S {a} {b} eq = begin
    a ≈⟨ sym right-unit ⟩
    a • ε ≈⟨ cright sym S-inverse ⟩
    a • (S • S⁻¹) ≈⟨ sym assoc ⟩
    (a • S) • S⁻¹ ≈⟨ cleft eq ⟩
    (b • S) • S⁻¹ ≈⟨ assoc ⟩
    b • (S • S⁻¹) ≈⟨ cright S-inverse ⟩
    b • ε ≈⟨ right-unit ⟩
    b ∎

  C : Word (Gen (₁₊ n)) → Word (Gen (₁₊ n))
  C w = J • w • J

  C-cong : ∀ {a b} → a ≈ b → C a ≈ C b
  C-cong eq = cright cleft eq

  C-ε : C ε ≈ ε
  C-ε = trans (cright left-unit) J-square

  C-• : ∀ a b → C (a • b) ≈ C a • C b
  C-• a b = begin
    C (a • b) ≈⟨ trans (cright assoc) (sym assoc) ⟩
    (J • a) • (b • J) ≈⟨ cright sym left-unit ⟩
    (J • a) • (ε • (b • J)) ≈⟨ cright cleft sym J-square ⟩
    (J • a) • ((J • J) • (b • J))
      ≈⟨ by-passoc (□ ^ 2 • (□ ^ 2 • □ ^ 2)) (□ ^ 3 • □ ^ 3) auto ⟩
    C a • C b ∎
    where open Pattern-Assoc

  C-invol : ∀ w → C (C w) ≈ w
  C-invol w = begin
    C (C w) ≈⟨ trans (cright assoc) (trans (sym assoc) (cright assoc)) ⟩
    (J • J) • (w • (J • J)) ≈⟨ cong J-square (cright J-square) ⟩
    ε • (w • ε) ≈⟨ trans left-unit right-unit ⟩
    w ∎

  C-pow : ∀ w k → C (w ^ k) ≈ C w ^ k
  C-pow w ₀ = C-ε
  C-pow w (₁₊ ₀) = refl
  C-pow w (₂₊ k) = trans (C-• w (w ^ ₁₊ k)) (cright C-pow w (₁₊ k))

  C-Mg : C Mg ≈ Mg
  C-Mg = trans (cright (sym J-Mg))
    (trans (sym assoc) (trans (cleft J-square) left-unit))

  C-S : C S ≈ Z • S
  C-S = begin
    C S ≈⟨ sym right-unit ⟩
    C S • ε ≈⟨ cright sym (trans (pow-comm S p-1 1) S-inverse) ⟩
    C S • (S⁻¹ • S) ≈⟨ by-assoc auto ⟩
    Z • S ∎

  C-Z-inverse : C Z • Z ≈ ε
  C-Z-inverse = cancel-S (begin
    (C Z • Z) • S ≈⟨ assoc ⟩
    C Z • (Z • S) ≈⟨ cright sym C-S ⟩
    C Z • C S ≈⟨ sym (C-• Z S) ⟩
    C (Z • S) ≈⟨ C-cong (sym C-S) ⟩
    C (C S) ≈⟨ C-invol S ⟩
    S ≈⟨ sym left-unit ⟩
    ε • S ∎)

  C-Z : C Z ≈ Z^ (- ₁)
  C-Z = begin
    C Z ≈⟨ sym right-unit ⟩
    C Z • ε ≈⟨ cright sym (trans (pow-+ Z Z-order ₁ (- ₁))
      (refl' (Eq.cong Z^ (+-inverseʳ ₁)))) ⟩
    C Z • (Z • Z^ (- ₁)) ≈⟨ sym assoc ⟩
    (C Z • Z) • Z^ (- ₁) ≈⟨ cleft C-Z-inverse ⟩
    ε • Z^ (- ₁) ≈⟨ left-unit ⟩
    Z^ (- ₁) ∎

  C-Z^ : ∀ k → C (Z^ k) ≈ Z^ (- k)
  C-Z^ k = trans (C-pow Z (toℕ k))
    (trans (^-cong (C Z) (Z^ (- ₁)) (toℕ k) C-Z)
      (trans (pow-* Z Z-order (- ₁) k) (refl' (Eq.cong Z^ (-1*x≈-x k)))))
    where open import Algebra.Properties.Ring (+-*-ring p-2)

  C-S^ : ∀ k → C (S^ k) ≈ Z^ k • S^ k
  C-S^ k = trans (C-pow S (toℕ k))
    (trans (^-cong (C S) (Z • S) (toℕ k) C-S)
      (^-• Z S (toℕ k) Z-S))

  Z-prefix : ∀ a b w → Z^ a • (Z^ b • w) ≈ Z^ (a + b) • w
  Z-prefix a b w = trans (sym assoc) (cleft pow-+ Z Z-order a b)

  C-row : ∀ a b → C (Z^ a • S^ b) ≈ Z^ (- a + b) • S^ b
  C-row a b = trans (C-• (Z^ a) (S^ b))
    (trans (cong (C-Z^ a) (C-S^ b)) (Z-prefix (- a) b (S^ b)))

  exponent-cancel : ∀ (a b : ℤ ₚ) → ((b + - a) + - a) + a ≡ - a + b
  exponent-cancel a b = Eq.trans (+-assoc (b + - a) (- a) a)
    (Eq.trans (Eq.cong ((b + - a) +_) (+-inverseˡ a))
      (Eq.trans (+-identityʳ (b + - a)) (+-comm b (- a))))

  forward-action : ∀ a b → Mg • S ≈ (Z^ a • S^ b) • Mg →
    Mg • Z ≈ Z^ ((b + - a) + - a) • Mg
  forward-action a b eq = cancel-S (begin
    (Mg • Z) • S ≈⟨ assoc ⟩
    Mg • (Z • S) ≈⟨ cong (sym C-Mg) (sym C-S) ⟩
    C Mg • C S ≈⟨ sym (C-• Mg S) ⟩
    C (Mg • S) ≈⟨ C-cong eq ⟩
    C ((Z^ a • S^ b) • Mg) ≈⟨ C-• (Z^ a • S^ b) Mg ⟩
    C (Z^ a • S^ b) • C Mg ≈⟨ cong (C-row a b) C-Mg ⟩
    (Z^ (- a + b) • S^ b) • Mg
      ≡⟨ Eq.cong (λ x → (Z^ x • S^ b) • Mg) (Eq.sym (exponent-cancel a b)) ⟩
    (Z^ (t + a) • S^ b) • Mg ≈⟨ assoc ⟩
    Z^ (t + a) • (S^ b • Mg) ≈⟨ sym (Z-prefix t a (S^ b • Mg)) ⟩
    Z^ t • (Z^ a • (S^ b • Mg)) ≈⟨ cright sym assoc ⟩
    Z^ t • ((Z^ a • S^ b) • Mg) ≈⟨ cright sym eq ⟩
    Z^ t • (Mg • S) ≈⟨ sym assoc ⟩
    (Z^ t • Mg) • S ∎)
    where t = (b + - a) + - a

  cancel-pow : ∀ w → w ^ p ≈ ε → ∀ k {a b} →
    a • w ^ toℕ k ≈ b • w ^ toℕ k → a ≈ b
  cancel-pow w ord k {a} {b} eq = begin
    a ≈⟨ sym right-unit ⟩
    a • ε ≈⟨ cright sym inv ⟩
    a • (w ^ toℕ k • w ^ toℕ (- k)) ≈⟨ sym assoc ⟩
    (a • w ^ toℕ k) • w ^ toℕ (- k) ≈⟨ cleft eq ⟩
    (b • w ^ toℕ k) • w ^ toℕ (- k) ≈⟨ assoc ⟩
    b • (w ^ toℕ k • w ^ toℕ (- k)) ≈⟨ cright inv ⟩
    b • ε ≈⟨ right-unit ⟩
    b ∎
    where
    inv = trans (pow-+ w ord k (- k))
      (refl' (Eq.cong (λ x → w ^ toℕ x) (+-inverseʳ k)))

  backward-action : ∀ a b → S • Mg ≈ Mg • (Z^ a • S^ b) →
    Z • Mg ≈ Mg • Z^ ((b + - a) + - a)
  backward-action a b eq = cancel-pow Z Z-order a
    (cancel-pow S c1 b (begin
    ((Z • Mg) • Z^ a) • S^ b ≈⟨ assoc ⟩
    (Z • Mg) • (Z^ a • S^ b) ≈⟨ assoc ⟩
    Z • (Mg • (Z^ a • S^ b)) ≈⟨ cright sym eq ⟩
    Z • (S • Mg) ≈⟨ sym assoc ⟩
    (Z • S) • Mg ≈⟨ cong (sym C-S) (sym C-Mg) ⟩
    C S • C Mg ≈⟨ sym (C-• S Mg) ⟩
    C (S • Mg) ≈⟨ C-cong eq ⟩
    C (Mg • (Z^ a • S^ b)) ≈⟨ C-• Mg (Z^ a • S^ b) ⟩
    C Mg • C (Z^ a • S^ b) ≈⟨ cong C-Mg (C-row a b) ⟩
    Mg • (Z^ (- a + b) • S^ b)
      ≡⟨ Eq.cong (λ x → Mg • (Z^ x • S^ b)) (Eq.sym (exponent-cancel a b)) ⟩
    Mg • (Z^ (t + a) • S^ b) ≈⟨ cright sym (Z-prefix t a (S^ b)) ⟩
    Mg • (Z^ t • (Z^ a • S^ b)) ≈⟨ sym assoc ⟩
    (Mg • Z^ t) • (Z^ a • S^ b) ≈⟨ sym assoc ⟩
    ((Mg • Z^ t) • Z^ a) • S^ b ∎))
    where t = (b + - a) + - a

  move-power : ∀ {a b c} → a • b ≈ c • a → ∀ k → a • b ^ k ≈ c ^ k • a
  move-power eq ₀ = trans right-unit (sym left-unit)
  move-power eq (₁₊ ₀) = eq
  move-power {a} {b} {c} eq (₂₊ k) = begin
    a • (b • b ^ ₁₊ k) ≈⟨ sym assoc ⟩
    (a • b) • b ^ ₁₊ k ≈⟨ cleft eq ⟩
    (c • a) • b ^ ₁₊ k ≈⟨ assoc ⟩
    c • (a • b ^ ₁₊ k) ≈⟨ cright move-power eq (₁₊ k) ⟩
    c • (c ^ ₁₊ k • a) ≈⟨ sym assoc ⟩
    (c • c ^ ₁₊ k) • a ∎

open Arithmetic using (c ; d ; e ; g⁻¹ ; d·gg ; g·[x·u] ; c·gg+e·u ; -[e·d]·u ; gg·d)

module Conversion
  (n : ℕ)
  (Γ : WRel (Gen (₁₊ n)))
  (W : Word (Gen (₁₊ n)))
  (order-S : let open PB Γ in S ^ p ≈ ε)
  (order-Z : let open PB Γ in Z ^ p ≈ ε)
  (comm-Z-S : let open PB Γ in Z • S ≈ S • Z)
  (pow-mod : let open PB Γ in
             ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ m → w ^ m ≈ w ^ (m % p))
  (Z-W : let open PB Γ in ∀ k → Z^ k • W ≈ W • Z^ (g * k))
  where

  open PB Γ
  open PP Γ
  open SR word-setoid

  --------------------------------------------------------------------
  -- Powers at ℤₚ exponents

  private
    pow-+ : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ (a b : ℤ ₚ) →
            w ^ toℕ a • w ^ toℕ b ≈ w ^ toℕ (a + b)
    pow-+ w ord a b = begin
      w ^ toℕ a • w ^ toℕ b          ≈⟨ sym (^-+ w (toℕ a) (toℕ b)) ⟩
      w ^ (toℕ a Nat.+ toℕ b)        ≈⟨ pow-mod w ord (toℕ a Nat.+ toℕ b) ⟩
      w ^ ((toℕ a Nat.+ toℕ b) % p)  ≈⟨ refl' (Eq.cong (w ^_) (Eq.sym (toℕ-+ a b))) ⟩
      w ^ toℕ (a + b)                ∎

    pow-* : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ (a b : ℤ ₚ) →
            (w ^ toℕ a) ^ toℕ b ≈ w ^ toℕ (a * b)
    pow-* w ord a b = begin
      (w ^ toℕ a) ^ toℕ b            ≈⟨ ^^ w (toℕ a) (toℕ b) ⟩
      w ^ (toℕ a Nat.* toℕ b)        ≈⟨ pow-mod w ord _ ⟩
      w ^ ((toℕ a Nat.* toℕ b) % p)  ≈⟨ refl' (Eq.cong (w ^_) (lemma-toℕ-% a b)) ⟩
      w ^ toℕ (a * b)                ∎

  Z^-+ : ∀ a b → Z^ a • Z^ b ≈ Z^ (a + b)
  Z^-+ = pow-+ Z order-Z

  Z^-* : ∀ a b → (Z^ a) ^ toℕ b ≈ Z^ (a * b)
  Z^-* = pow-* Z order-Z

  S^-* : ∀ a b → (S^ a) ^ toℕ b ≈ S^ (a * b)
  S^-* = pow-* S order-S

  comm-Z^-S^ : ∀ a b → Z^ a • S^ b ≈ S^ b • Z^ a
  comm-Z^-S^ a b = comm⇒pow-comm (toℕ a) (toℕ b) comm-Z-S

  -- A Z-power past W, the other way: W • Z^x ≈ Z^(x·g⁻¹) • W.
  W-Z : ∀ x → W • Z^ x ≈ Z^ (x * g⁻¹) • W
  W-Z x = begin
    W • Z^ x                  ≡⟨ Eq.cong (λ t → W • Z^ t) (Eq.sym (g·[x·u] x)) ⟩
    W • Z^ (g * (x * g⁻¹))    ≈⟨ sym (Z-W (x * g⁻¹)) ⟩
    Z^ (x * g⁻¹) • W          ∎

  -- Z^x • Z^(-x) is ε.
  Z^-cancel : ∀ x → Z^ x • Z^ (- x) ≈ ε
  Z^-cancel x = trans (Z^-+ x (- x)) (refl' (Eq.cong (λ t → Z^ t) (+-inverseʳ x)))

  --------------------------------------------------------------------
  -- Iterating a conjugation

  private
    induction : ∀ {a b c'} → a • b ≈ c' • a → ∀ k → a • b ^ k ≈ c' ^ k • a
    induction eq ₀      = trans right-unit (sym left-unit)
    induction eq (₁₊ ₀) = eq
    induction {a} {b} {c'} eq (₂₊ k) = begin
      a • (b • b ^ ₁₊ k)    ≈⟨ sym assoc ⟩
      (a • b) • b ^ ₁₊ k    ≈⟨ cleft eq ⟩
      (c' • a) • b ^ ₁₊ k   ≈⟨ assoc ⟩
      c' • (a • b ^ ₁₊ k)   ≈⟨ cright induction eq (₁₊ k) ⟩
      c' • (c' ^ ₁₊ k • a)  ≈⟨ sym assoc ⟩
      (c' • c' ^ ₁₊ k) • a  ∎

    inductionˡ : ∀ {a b c'} → a • b ≈ b • c' → ∀ k → a ^ k • b ≈ b • c' ^ k
    inductionˡ eq ₀      = trans left-unit (sym right-unit)
    inductionˡ eq (₁₊ ₀) = eq
    inductionˡ {a} {b} {c'} eq (₂₊ k) = begin
      (a • a ^ ₁₊ k) • b    ≈⟨ assoc ⟩
      a • (a ^ ₁₊ k • b)    ≈⟨ cright inductionˡ eq (₁₊ k) ⟩
      a • (b • c' ^ ₁₊ k)   ≈⟨ sym assoc ⟩
      (a • b) • c' ^ ₁₊ k   ≈⟨ cleft eq ⟩
      (b • c') • c' ^ ₁₊ k  ≈⟨ assoc ⟩
      b • (c' • c' ^ ₁₊ k)  ∎

  --------------------------------------------------------------------
  -- semi-MS ⇒ semi-MR

  MS⇒MR : W • S ≈ Z^ c • (S^ d • W) → W • (S^ (g * g) • Z^ e) ≈ S • W
  MS⇒MR ms = begin
    W • (S^ (g * g) • Z^ e)                ≈⟨ sym assoc ⟩
    (W • S^ (g * g)) • Z^ e                ≈⟨ cleft iterated ⟩
    ((Z^ c' • S) • W) • Z^ e                ≈⟨ assoc ⟩
    (Z^ c' • S) • (W • Z^ e)                ≈⟨ cright W-Z e ⟩
    (Z^ c' • S) • (Z^ (e * g⁻¹) • W)        ≈⟨ assoc ⟩
    Z^ c' • (S • (Z^ (e * g⁻¹) • W))        ≈⟨ cright sym assoc ⟩
    Z^ c' • ((S • Z^ (e * g⁻¹)) • W)        ≈⟨ cright cleft sym (comm-Z^-S^ (e * g⁻¹) ₁) ⟩
    Z^ c' • ((Z^ (e * g⁻¹) • S) • W)        ≈⟨ cright assoc ⟩
    Z^ c' • (Z^ (e * g⁻¹) • (S • W))        ≈⟨ sym assoc ⟩
    (Z^ c' • Z^ (e * g⁻¹)) • (S • W)        ≈⟨ cleft Z^-+ c' (e * g⁻¹) ⟩
    Z^ (c' + e * g⁻¹) • (S • W)             ≡⟨ Eq.cong (λ t → Z^ t • (S • W)) c·gg+e·u ⟩
    ε • (S • W)                             ≈⟨ left-unit ⟩
    S • W                                   ∎
    where
    c' : ℤ ₚ
    c' = c * (g * g)

    -- semi-MS, iterated g² times.
    iterated : W • S^ (g * g) ≈ (Z^ c' • S) • W
    iterated = begin
      W • S ^ toℕ (g * g)
        ≈⟨ induction (trans ms (sym assoc)) (toℕ (g * g)) ⟩
      (Z^ c • S^ d) ^ toℕ (g * g) • W
        ≈⟨ cleft ^-• (Z^ c) (S^ d) (toℕ (g * g)) (comm-Z^-S^ c d) ⟩
      ((Z^ c) ^ toℕ (g * g) • (S^ d) ^ toℕ (g * g)) • W
        ≈⟨ cleft cong (Z^-* c (g * g)) (S^-* d (g * g)) ⟩
      (Z^ c' • S^ (d * (g * g))) • W
        ≡⟨ Eq.cong (λ t → (Z^ c' • S^ t) • W) d·gg ⟩
      (Z^ c' • S) • W
        ∎

  --------------------------------------------------------------------
  -- semi-MR ⇒ semi-MS

  MR⇒MS : W • (S^ (g * g) • Z^ e) ≈ S • W → W • S ≈ Z^ c • (S^ d • W)
  MR⇒MS mr = begin
    W • S                                   ≈⟨ sym right-unit ⟩
    (W • S) • ε                             ≈⟨ cright sym (Z^-cancel f) ⟩
    (W • S) • (Z^ f • Z^ (- f))             ≈⟨ sym assoc ⟩
    ((W • S) • Z^ f) • Z^ (- f)             ≈⟨ cleft assoc ⟩
    (W • (S • Z^ f)) • Z^ (- f)             ≈⟨ cleft sym iterated ⟩
    (S^ d • W) • Z^ (- f)                  ≈⟨ assoc ⟩
    S^ d • (W • Z^ (- f))                  ≈⟨ cright W-Z (- f) ⟩
    S^ d • (Z^ (- f * g⁻¹) • W)            ≡⟨ Eq.cong (λ t → S^ d • (Z^ t • W)) -[e·d]·u ⟩
    S^ d • (Z^ c • W)                      ≈⟨ sym assoc ⟩
    (S^ d • Z^ c) • W                      ≈⟨ cleft sym (comm-Z^-S^ c d) ⟩
    (Z^ c • S^ d) • W                      ≈⟨ assoc ⟩
    Z^ c • (S^ d • W)                      ∎
    where
    f : ℤ ₚ
    f = e * d

    -- semi-MR, iterated g⁻² times.
    iterated : S^ d • W ≈ W • (S • Z^ f)
    iterated = begin
      S ^ toℕ d • W
        ≈⟨ inductionˡ (sym mr) (toℕ d) ⟩
      W • (S^ (g * g) • Z^ e) ^ toℕ d
        ≈⟨ cright ^-• (S^ (g * g)) (Z^ e) (toℕ d) (sym (comm-Z^-S^ e (g * g))) ⟩
      W • ((S^ (g * g)) ^ toℕ d • (Z^ e) ^ toℕ d)
        ≈⟨ cright cong (S^-* (g * g) d) (Z^-* e d) ⟩
      W • (S^ ((g * g) * d) • Z^ f)
        ≡⟨ Eq.cong (λ t → W • (S^ t • Z^ f)) gg·d ⟩
      W • (S • Z^ f)
        ∎

------------------------------------------------------------------------
-- Instantiate the shared calculus, once in each presentation.

module Figure1 (n : ℕ) where
  private
    Γ = F._F,_===_ (₁₊ n)
  module Common₁ = Common n Γ
    (PB.axiom (F.srel F.c0)) (PB.axiom (F.srel F.c1))
    (PB.axiom (F.srel F.c2)) (λ k → PB.axiom (F.srel (F.c3 k)))
    (PB.axiom (F.srel F.c5)) F.ν^-central
  open PB Γ
  open PP Γ
  open SR word-setoid

  Mg-Z : Mg • Z ≈ Z^ g⁻¹ • Mg
  Mg-Z = trans
    (Common₁.forward-action c d (trans (axiom (F.srel F.c4)) (sym assoc)))
    (refl' (Eq.cong (λ x → Z^ x • Mg) old-action))

  Z-Mg : ∀ k → Z^ k • Mg ≈ Mg • Z^ (g * k)
  Z-Mg k = sym (begin
    Mg • Z^ (g * k) ≈⟨ Common₁.move-power Mg-Z (toℕ (g * k)) ⟩
    (Z^ g⁻¹) ^ toℕ (g * k) • Mg
      ≈⟨ cleft Common₁.pow-* Z Common₁.Z-order g⁻¹ (g * k) ⟩
    Z^ (g⁻¹ * (g * k)) • Mg ≡⟨ Eq.cong (λ x → Z^ x • Mg) value ⟩
    Z^ k • Mg ∎)
    where
    value = Eq.trans (Eq.sym (*-assoc g⁻¹ g k))
      (Eq.trans (Eq.cong (_* k) (lemma-⁻¹ˡ g {{nztoℕ {y = g} {neq0 = g≠0}}}))
        (*-identityˡ k))

  private
    module Convert = Conversion n Γ Mg (axiom (F.srel F.c1))
      Common₁.Z-order Common₁.Z-S (λ w → Common₁.pow-mod w p) Z-Mg

  -- The replacement C4, derived in the original Figure 1 theory.
  c4′ : S • Mg ≈ Mg • S^ (g * g) • Z^ e
  c4′ = sym (Convert.MS⇒MR (axiom (F.srel F.c4)))

module Figure1-MS (n : ℕ) where
  private
    Γ = F′._F,_===_ (₁₊ n)
  module Common₂ = Common n Γ
    (PB.axiom (F′.srel F′.c0)) (PB.axiom (F′.srel F′.c1))
    (PB.axiom (F′.srel F′.c2)) (λ k → PB.axiom (F′.srel (F′.c3 k)))
    (PB.axiom (F′.srel F′.c5)) F′.ν^-central
  open PB Γ
  open PP Γ
  open SR word-setoid

  Z-Mg₁ : Z • Mg ≈ Mg • Z^ g
  Z-Mg₁ = trans
    (Common₂.backward-action e (g * g)
      (trans (axiom (F′.srel F′.c4))
        (cright sym (comm⇒pow-comm (toℕ e) (toℕ (g * g)) Common₂.Z-S))))
    (refl' (Eq.cong (λ x → Mg • Z^ x) new-action))

  Z-Mg : ∀ k → Z^ k • Mg ≈ Mg • Z^ (g * k)
  Z-Mg k = begin
    Z^ k • Mg ≈⟨ sym (Common₂.move-power (sym Z-Mg₁) (toℕ k)) ⟩
    Mg • (Z^ g) ^ toℕ k ≈⟨ cright Common₂.pow-* Z Common₂.Z-order g k ⟩
    Mg • Z^ (g * k) ∎

  private
    module Convert = Conversion n Γ Mg (axiom (F′.srel F′.c1))
      Common₂.Z-order Common₂.Z-S (λ w → Common₂.pow-mod w p) Z-Mg

  -- The original C4, derived in the Figure1-MS theory.
  c4 : Mg • S ≈ Z^ c • S^ d • Mg
  c4 = Convert.MR⇒MS (sym (axiom (F′.srel F′.c4)))

------------------------------------------------------------------------
-- Every other axiom is identical.  The structural lift is respected too.

F⇒F′-axiom : ∀ {n w v} → F._F,_===_ n w v → F′._≈ᶠ_ w v
F⇒F′-axiom (F.srel F.c0) = PB.axiom (F′.srel F′.c0)
F⇒F′-axiom (F.srel F.c1) = PB.axiom (F′.srel F′.c1)
F⇒F′-axiom (F.srel F.c2) = PB.axiom (F′.srel F′.c2)
F⇒F′-axiom (F.srel (F.c3 k)) = PB.axiom (F′.srel (F′.c3 k))
F⇒F′-axiom {₁₊ n} (F.srel F.c4) = Figure1-MS.c4 n
F⇒F′-axiom (F.srel F.c5) = PB.axiom (F′.srel F′.c5)
F⇒F′-axiom (F.srel F.c6) = PB.axiom (F′.srel F′.c6)
F⇒F′-axiom (F.srel F.c7) = PB.axiom (F′.srel F′.c7)
F⇒F′-axiom (F.srel F.c8) = PB.axiom (F′.srel F′.c8)
F⇒F′-axiom (F.srel F.c9) = PB.axiom (F′.srel F′.c9)
F⇒F′-axiom (F.srel F.c10) = PB.axiom (F′.srel F′.c10)
F⇒F′-axiom (F.srel F.c11) = PB.axiom (F′.srel F′.c11)
F⇒F′-axiom (F.srel F.c12) = PB.axiom (F′.srel F′.c12)
F⇒F′-axiom (F.srel F.c13) = PB.axiom (F′.srel F′.c13)
F⇒F′-axiom (F.srel F.c14) = PB.axiom (F′.srel F′.c14)
F⇒F′-axiom (F.srel F.c15) = PB.axiom (F′.srel F′.c15)
F⇒F′-axiom (F.cong↑ {w = w} {v} a) = F′.lemma-cong↑ w v (F⇒F′-axiom a)
F⇒F′-axiom (F.comm₁ h g) = PB.axiom (F′.comm₁ h g)
F⇒F′-axiom (F.comm₂ h g) = PB.axiom (F′.comm₂ h g)
F⇒F′-axiom (F.ω↑=ω h) = PB.axiom (F′.ω↑=ω h)

F′⇒F-axiom : ∀ {n w v} → F′._F,_===_ n w v → F._≈ᶠ_ w v
F′⇒F-axiom (F′.srel F′.c0) = PB.axiom (F.srel F.c0)
F′⇒F-axiom (F′.srel F′.c1) = PB.axiom (F.srel F.c1)
F′⇒F-axiom (F′.srel F′.c2) = PB.axiom (F.srel F.c2)
F′⇒F-axiom (F′.srel (F′.c3 k)) = PB.axiom (F.srel (F.c3 k))
F′⇒F-axiom {₁₊ n} (F′.srel F′.c4) = Figure1.c4′ n
F′⇒F-axiom (F′.srel F′.c5) = PB.axiom (F.srel F.c5)
F′⇒F-axiom (F′.srel F′.c6) = PB.axiom (F.srel F.c6)
F′⇒F-axiom (F′.srel F′.c7) = PB.axiom (F.srel F.c7)
F′⇒F-axiom (F′.srel F′.c8) = PB.axiom (F.srel F.c8)
F′⇒F-axiom (F′.srel F′.c9) = PB.axiom (F.srel F.c9)
F′⇒F-axiom (F′.srel F′.c10) = PB.axiom (F.srel F.c10)
F′⇒F-axiom (F′.srel F′.c11) = PB.axiom (F.srel F.c11)
F′⇒F-axiom (F′.srel F′.c12) = PB.axiom (F.srel F.c12)
F′⇒F-axiom (F′.srel F′.c13) = PB.axiom (F.srel F.c13)
F′⇒F-axiom (F′.srel F′.c14) = PB.axiom (F.srel F.c14)
F′⇒F-axiom (F′.srel F′.c15) = PB.axiom (F.srel F.c15)
F′⇒F-axiom (F′.cong↑ {w = w} {v} a) = F.lemma-cong↑ w v (F′⇒F-axiom a)
F′⇒F-axiom (F′.comm₁ h g) = PB.axiom (F.comm₁ h g)
F′⇒F-axiom (F′.comm₂ h g) = PB.axiom (F.comm₂ h g)
F′⇒F-axiom (F′.ω↑=ω h) = PB.axiom (F.ω↑=ω h)

F⇒F′ : ∀ {n} {w v : Word (Gen n)} → F._≈ᶠ_ w v → F′._≈ᶠ_ w v
F⇒F′ PB.refl = PB.refl
F⇒F′ (PB.sym a) = PB.sym (F⇒F′ a)
F⇒F′ (PB.trans a b) = PB.trans (F⇒F′ a) (F⇒F′ b)
F⇒F′ (PB.cong a b) = PB.cong (F⇒F′ a) (F⇒F′ b)
F⇒F′ PB.assoc = PB.assoc
F⇒F′ PB.left-unit = PB.left-unit
F⇒F′ PB.right-unit = PB.right-unit
F⇒F′ (PB.axiom a) = F⇒F′-axiom a

F′⇒F : ∀ {n} {w v : Word (Gen n)} → F′._≈ᶠ_ w v → F._≈ᶠ_ w v
F′⇒F PB.refl = PB.refl
F′⇒F (PB.sym a) = PB.sym (F′⇒F a)
F′⇒F (PB.trans a b) = PB.trans (F′⇒F a) (F′⇒F b)
F′⇒F (PB.cong a b) = PB.cong (F′⇒F a) (F′⇒F b)
F′⇒F PB.assoc = PB.assoc
F′⇒F PB.left-unit = PB.left-unit
F′⇒F PB.right-unit = PB.right-unit
F′⇒F (PB.axiom a) = F′⇒F-axiom a

-- Equality of the generated congruences, on the very same circuits.
Theorem-Figure1-equivalent-Figure1-MS : ∀ {n} (w v : Word (Gen n)) →
  (F._≈ᶠ_ w v → F′._≈ᶠ_ w v) × (F′._≈ᶠ_ w v → F._≈ᶠ_ w v)
Theorem-Figure1-equivalent-Figure1-MS w v = F⇒F′ , F′⇒F

------------------------------------------------------------------------
-- The identity isomorphism of the presented monoids and groups.

open import Function using (id)
open import Algebra.Bundles using (Monoid ; Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
import Presentation.Morphism as Morphism
open import Word.Base using ([_]ʷ)

module Iso (n : ℕ) where
  private
    Γ = F._F,_===_ n
    Δ = F′._F,_===_ n
  open MonoidMorphisms (Monoid.rawMonoid (PP.•-ε-monoid Γ))
                       (Monoid.rawMonoid (PP.•-ε-monoid Δ))

  isMonoidHomomorphism : IsMonoidHomomorphism id
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = F⇒F′ }
      ; homo = λ _ _ → PB.refl }
    ; ε-homo = PB.refl }

  isMonoidIsomorphism : IsMonoidIsomorphism id
  isMonoidIsomorphism = record
    { isMonoidMonomorphism = record
      { isMonoidHomomorphism = isMonoidHomomorphism
      ; injective = F′⇒F }
    ; surjective = λ w → w , F⇒F′ }

-- Finite orders give inverses directly; no presentation theorem is used.
grouplike-F : ∀ {n} → Grouplike (F._F,_===_ n)
grouplike-F {n} (F.gate₀ F.ν-gate) = ν ^ (p Nat.+ p-1) ,
  PB.trans (PB.sym (PP.^-+ (F._F,_===_ n) ν (p Nat.+ p-1) 1))
    (PB.trans (PB.refl' (F._F,_===_ n) (Eq.cong (ν ^_)
      (Eq.trans (NP.+-comm (p Nat.+ p-1) 1) (Eq.sym (NP.+-suc p p-1)))))
      (PB.axiom (F.srel F.c0)))
grouplike-F {₁₊ n} (F.gate₁ F.H-gate) = H ^ 3 ,
  PB.trans (PB.sym (PP.^-+ (F._F,_===_ (₁₊ n)) H 3 1))
    (Figure1.Common₁.H-order n)
grouplike-F {₁₊ n} (F.gate₁ F.S-gate) = S ^ p-1 ,
  PB.trans (PB.sym (PP.^-+ (F._F,_===_ (₁₊ n)) S p-1 1))
    (PB.trans (PB.refl' (F._F,_===_ (₁₊ n)) (Eq.cong (S ^_) (NP.+-comm p-1 1)))
      (PB.axiom (F.srel F.c1)))
grouplike-F {₂₊ n} (F.gate₂ F.CZ-gate) = F.CZ ^ p-1 ,
  PB.trans (PB.sym (PP.^-+ (F._F,_===_ (₂₊ n)) F.CZ p-1 1))
    (PB.trans (PB.refl' (F._F,_===_ (₂₊ n)) (Eq.cong (F.CZ ^_) (NP.+-comm p-1 1)))
      (PB.axiom (F.srel F.c6)))
grouplike-F {₁₊ n} (x F.↥) with grouplike-F x
... | ix , prf = (ix F.↑) , F.lemma-cong↑ (ix • [ x ]ʷ) ε prf

grouplike-F′ : ∀ {n} → Grouplike (F′._F,_===_ n)
grouplike-F′ x with grouplike-F x
... | ix , prf = ix , F⇒F′ prf

module GroupIso (n : ℕ) where
  private
    Γ = F._F,_===_ n
    Δ = F′._F,_===_ n
    module G = Group-Lemmas Γ grouplike-F
    module G′ = Group-Lemmas Δ grouplike-F′
    module GM = Morphism.GroupMorphism Γ Δ grouplike-F grouplike-F′
    module Hom = GM.MonoidHom⇒GroupHom id (Iso.isMonoidHomomorphism n)
  open GroupMorphisms (Group.rawGroup G.•-ε-group) (Group.rawGroup G′.•-ε-group)

  isGroupIsomorphism : IsGroupIsomorphism id
  isGroupIsomorphism = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = Hom.isGroupHomomorphism
      ; injective = F′⇒F }
    ; surjective = λ w → w , F⇒F′ }

Theorem-Figure1-iso-Figure1-MS : ∀ n →
  let module G = Group-Lemmas (F._F,_===_ n) grouplike-F
      module G′ = Group-Lemmas (F′._F,_===_ n) grouplike-F′
  in GroupMorphisms.IsGroupIsomorphism
    (Group.rawGroup G.•-ε-group) (Group.rawGroup G′.•-ε-group) id
Theorem-Figure1-iso-Figure1-MS = GroupIso.isGroupIsomorphism
