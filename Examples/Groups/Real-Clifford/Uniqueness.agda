------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal forms that act alike on Pauli operators are equal, but for
-- their sign
--
-- A normal form W = N ↑ • M • L acts on signed Pauli operators by
-- conjugation (Pauli).  N ↑ fixes Z₀, the operator Z on wire 0, and the
-- X-circuit M moves Z from the top wire to wire 0, so W⁻¹ sends Z₀ to
-- L⁻¹ Z_top L, which determines the Z-circuit L (QZ-inj); then
-- (N ↑ • M)⁻¹ sends X₀ to M⁻¹ X₀ M, which determines M (QX-inj); and
-- N ↑ acts on the wires above as N.  The sign of a normal form is a
-- scalar and acts trivially: the matrix semantics tells it.
--
-- These are the uniqueness halves of Propositions 4.11 and 4.12 of the
-- paper (QZ-inj, QX-inj), and its Proposition 4.13 (QX-Z); the paper's
-- first tensor factor is the top wire here, its last one wire 0.
--
-- The operators are read one wire at a time.  Climbing a ladder, a B
-- gate leaves on its lower wire the letter (Z or XZ) of its lower
-- input type, and on its upper wire a letter that tells it from the
-- other B gates with that lower input; descending a D-ladder, a D gate
-- leaves on its lower wire a letter that tells it from the other D
-- gates.  No B or D gate changes the sign, so the sign at the end
-- tells C₁ from C₂, and E₁ from E₂.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Uniqueness where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Engine using (⟪_⟫)
open import Examples.Groups.Real-Clifford.NormalForm
open import Examples.Groups.Real-Clifford.Pauli

private
  variable
    n m : ℕ
    t u : Ty

------------------------------------------------------------------------
-- Circuits that act alike

infix 4 _≗ᵃ_
_≗ᵃ_ : Circuit n → Circuit n → Set
w ≗ᵃ v = ∀ P → act w P ≡ act v P

-- Their inverses act alike.
≗ᵃ-inv : {w v : Circuit n} → w ≗ᵃ v → inv w ≗ᵃ inv v
≗ᵃ-inv {w = w} {v} e P = begin
  act (inv w) P                         ≡⟨ Eq.cong (act (inv w)) (Eq.sym (inv-act v P)) ⟩
  act (inv w) (act v (act (inv v) P))   ≡⟨ Eq.cong (act (inv w)) (Eq.sym (e (act (inv v) P))) ⟩
  act (inv w) (act w (act (inv v) P))   ≡⟨ act-inv w (act (inv v) P) ⟩
  act (inv v) P                         ∎
  where open Eq.≡-Reasoning

-- A common last factor cancels.
≗ᵃ-cancel : {w v : Circuit n} (u : Circuit n) → (w • u) ≗ᵃ (v • u) → w ≗ᵃ v
≗ᵃ-cancel {w = w} {v} u e P = begin
  act w P                         ≡⟨ Eq.cong (act w) (Eq.sym (inv-act u P)) ⟩
  act w (act u (act (inv u) P))   ≡⟨ e (act (inv u) P) ⟩
  act v (act u (act (inv u) P))   ≡⟨ Eq.cong (act v) (inv-act u P) ⟩
  act v P                         ∎
  where open Eq.≡-Reasoning

-- Circuits one wire up act alike only if they do one wire down.
≗ᵃ-↑ : (w v : Circuit n) → (w ↑) ≗ᵃ (v ↑) → w ≗ᵃ v
≗ᵃ-↑ w v e (σ , ps) = Eq.cong (λ P → proj₁ P , tail (proj₂ P))
  (Eq.trans (Eq.sym (act-↑ w σ 𝐈 ps)) (Eq.trans (e (σ , 𝐈 ∷ ps)) (act-↑ v σ 𝐈 ps)))

-- The inverse of a circuit one wire up acts on the wires above, and
-- fixes wire 0 when they carry I.
act-inv-↑ : (w : Circuit n) (σ : Bool) (p : Letter) (ps : Vec Letter n) →
            act (inv (w ↑)) (σ , p ∷ ps) ≡ (proj₁ (act (inv w) (σ , ps)) , p ∷ proj₂ (act (inv w) (σ , ps)))
act-inv-↑ w σ p ps =
  Eq.trans (Eq.cong (λ v → act v (σ , p ∷ ps)) (inv-↑ w)) (act-↑ (inv w) σ p ps)

fix-↑ : (w : Circuit n) (σ : Bool) (p : Letter) → act (inv (w ↑)) (σ , p ∷ I^ n) ≡ (σ , p ∷ I^ n)
fix-↑ w σ p = Eq.trans (act-inv-↑ w σ p (I^ _))
  (Eq.cong (λ P → proj₁ P , p ∷ proj₂ P) (act-I (inv w) σ))

------------------------------------------------------------------------
-- Pauli operators on wire 0 and on the top wire

Z₀ X₀ : (n : ℕ) → Pauli (₁₊ n)
Z₀ n = false , 𝐙 ∷ I^ n
X₀ n = false , 𝐗 ∷ I^ n

ztop : (n : ℕ) → Vec Letter (₁₊ n)
ztop zero    = 𝐙 ∷ []
ztop (suc n) = 𝐈 ∷ ztop n

------------------------------------------------------------------------
-- The derived generators on Pauli operators

-- The letter of a wire type.
T : Ty → Letter
T sg = 𝐙
T db = 𝐘

-- An A gate, on the letter of its type.
ℓA : AT t → Letter
ℓA A₁ = 𝐙
ℓA A₂ = 𝐗
ℓA A₃ = 𝐘

A-act : (a : AT t) (σ : Bool) (R : Vec Letter n) →
        act (inv ⟪ Al a ⟫) (σ , T t ∷ R) ≡ (σ , ℓA a ∷ R)
A-act A₁ σ     R = refl
A-act A₂ false R = refl
A-act A₂ true  R = refl
A-act A₃ σ     R = refl

-- A B gate, on I below and the letter of its upper output type above.
ℓB : BT t u → Letter
ℓB B₁ = 𝐈
ℓB B₂ = 𝐗
ℓB B₃ = 𝐙
ℓB B₄ = 𝐘
ℓB B₅ = 𝐈
ℓB B₆ = 𝐗
ℓB B₇ = 𝐙
ℓB B₈ = 𝐘

B-act : (b : BT t u) (σ : Bool) (R : Vec Letter n) →
        act (inv ⟪ Bl b ⟫) (σ , 𝐈 ∷ T u ∷ R) ≡ (σ , T t ∷ ℓB b ∷ R)
B-act B₁ false R = refl
B-act B₁ true  R = refl
B-act B₂ false R = refl
B-act B₂ true  R = refl
B-act B₃ false R = refl
B-act B₃ true  R = refl
B-act B₄ false R = refl
B-act B₄ true  R = refl
B-act B₅ false R = refl
B-act B₅ true  R = refl
B-act B₆ false R = refl
B-act B₆ true  R = refl
B-act B₇ false R = refl
B-act B₇ true  R = refl
B-act B₈ false R = refl
B-act B₈ true  R = refl

-- A C gate, on Z.
csign : CT → Bool
csign C₁ = false
csign C₂ = true

-- A D gate, on X or XZ below and I above, and on Z below.
data XY : Set where
  xX xY : XY

xy : XY → Letter
xy xX = 𝐗
xy xY = 𝐘

ℓD : DT → Letter
ℓD D₁ = 𝐈
ℓD D₂ = 𝐗
ℓD D₃ = 𝐙
ℓD D₄ = 𝐘

swapD : DT → XY → XY
swapD D₄ xX = xY
swapD D₄ xY = xX
swapD D₁ ℓ  = ℓ
swapD D₂ ℓ  = ℓ
swapD D₃ ℓ  = ℓ

D-act : (d : DT) (ℓ : XY) (σ : Bool) (R : Vec Letter n) →
        act (inv ⟪ Dl d ⟫) (σ , xy ℓ ∷ 𝐈 ∷ R) ≡ (σ , ℓD d ∷ xy (swapD d ℓ) ∷ R)
D-act D₁ xX false R = refl
D-act D₁ xX true  R = refl
D-act D₁ xY false R = refl
D-act D₁ xY true  R = refl
D-act D₂ xX false R = refl
D-act D₂ xX true  R = refl
D-act D₂ xY false R = refl
D-act D₂ xY true  R = refl
D-act D₃ xX false R = refl
D-act D₃ xX true  R = refl
D-act D₃ xY false R = refl
D-act D₃ xY true  R = refl
D-act D₄ xX false R = refl
D-act D₄ xX true  R = refl
D-act D₄ xY false R = refl
D-act D₄ xY true  R = refl

D-Z : (d : DT) (R : Vec Letter n) →
      act (inv ⟪ Dl d ⟫) (false , 𝐙 ∷ 𝐈 ∷ R) ≡ (false , 𝐈 ∷ 𝐙 ∷ R)
D-Z D₁ R = refl
D-Z D₂ R = refl
D-Z D₃ R = refl
D-Z D₄ R = refl

-- An E gate, on X.
esign : ET → Bool
esign E₁ = false
esign E₂ = true

------------------------------------------------------------------------
-- Reading the gates back

pickA : Letter → Σ Ty AT
pickA 𝐗 = sg , A₂
pickA 𝐘 = db , A₃
pickA 𝐙 = sg , A₁
pickA 𝐈 = sg , A₁

pickA-ok : (a : AT t) → pickA (ℓA a) ≡ (t , a)
pickA-ok A₁ = refl
pickA-ok A₂ = refl
pickA-ok A₃ = refl

𝐈≢ℓA : (a : AT t) → 𝐈 ≢ ℓA a
𝐈≢ℓA A₁ ()
𝐈≢ℓA A₂ ()
𝐈≢ℓA A₃ ()

pickB : (t : Ty) → Letter → Σ Ty (BT t)
pickB sg 𝐈 = sg , B₁
pickB sg 𝐗 = sg , B₂
pickB sg 𝐙 = sg , B₃
pickB sg 𝐘 = db , B₄
pickB db 𝐈 = db , B₅
pickB db 𝐗 = db , B₆
pickB db 𝐙 = db , B₇
pickB db 𝐘 = sg , B₈

pickB-ok : (b : BT t u) → pickB t (ℓB b) ≡ (u , b)
pickB-ok B₁ = refl
pickB-ok B₂ = refl
pickB-ok B₃ = refl
pickB-ok B₄ = refl
pickB-ok B₅ = refl
pickB-ok B₆ = refl
pickB-ok B₇ = refl
pickB-ok B₈ = refl

csign-inj : (c c' : CT) → csign c ≡ csign c' → c ≡ c'
csign-inj C₁ C₁ _ = refl
csign-inj C₂ C₂ _ = refl

pickD : Letter → DT
pickD 𝐈 = D₁
pickD 𝐗 = D₂
pickD 𝐙 = D₃
pickD 𝐘 = D₄

pickD-ok : (d : DT) → pickD (ℓD d) ≡ d
pickD-ok D₁ = refl
pickD-ok D₂ = refl
pickD-ok D₃ = refl
pickD-ok D₄ = refl

esign-inj : (e e' : ET) → esign e ≡ esign e' → e ≡ e'
esign-inj E₁ E₁ _ = refl
esign-inj E₂ E₂ _ = refl

------------------------------------------------------------------------
-- X-circuits

-- A D-ladder, inverted, on X or XZ on wire 0.
QD : DL (₁₊ n) → XY → Bool → Pauli (₁₊ n)
QD dl ℓ σ = act (inv ⟦ dl ⟧ᴰ) (σ , xy ℓ ∷ I^ _)

QD-step : (d : DT) (dl : DL (₁₊ n)) (ℓ : XY) (σ : Bool) →
          QD (d ∷ᴰ dl) ℓ σ ≡ (proj₁ (QD dl (swapD d ℓ) σ) , ℓD d ∷ proj₂ (QD dl (swapD d ℓ) σ))
QD-step d dl ℓ σ = Eq.trans (Eq.cong (act (inv (⟦ dl ⟧ᴰ ↑))) (D-act d ℓ σ (I^ _)))
  (act-inv-↑ ⟦ dl ⟧ᴰ σ (ℓD d) (xy (swapD d ℓ) ∷ I^ _))

QD-inj : (dl dl' : DL (₁₊ n)) (ℓ : XY) (σ σ' : Bool) →
         QD dl ℓ σ ≡ QD dl' ℓ σ' → dl ≡ dl' × σ ≡ σ'
QD-inj []ᴰ []ᴰ ℓ σ σ' e = refl , Eq.cong proj₁ e
QD-inj (d ∷ᴰ dl) (d' ∷ᴰ dl') ℓ σ σ' e
  with e' ← Eq.trans (Eq.sym (QD-step d dl ℓ σ)) (Eq.trans e (QD-step d' dl' ℓ σ'))
  with refl ← Eq.trans (Eq.sym (pickD-ok d)) (Eq.trans (Eq.cong (pickD ∘ head ∘ proj₂) e') (pickD-ok d'))
  with (p , q) ← QD-inj dl dl' (swapD d ℓ) σ σ' (Eq.cong (λ P → proj₁ P , tail (proj₂ P)) e')
  = Eq.cong (d ∷ᴰ_) p , q

-- An X-circuit, inverted, on X₀; it moves Z from wire 0 to the top.
QX : Xc (₁₊ n) → Pauli (₁₊ n)
QX M = act (inv ⟦ M ⟧ˣ) (X₀ _)

QX-def : (e : ET) (dl : DL (₁₊ n)) → QX (e ,ˣ dl) ≡ QD dl xX (esign e)
QX-def E₁ dl = refl
QX-def E₂ dl = refl

QX-inj : (M M' : Xc (₁₊ n)) → QX M ≡ QX M' → M ≡ M'
QX-inj (e ,ˣ dl) (e' ,ˣ dl') h
  with (p , q) ← QD-inj dl dl' xX (esign e) (esign e')
                   (Eq.trans (Eq.sym (QX-def e dl)) (Eq.trans h (QX-def e' dl')))
  = Eq.cong₂ _,ˣ_ (esign-inj e e' q) p

QD-Z : (dl : DL (₁₊ n)) → act (inv ⟦ dl ⟧ᴰ) (Z₀ n) ≡ (false , ztop n)
QD-Z []ᴰ       = refl
QD-Z (d ∷ᴰ dl) = Eq.trans (Eq.cong (act (inv (⟦ dl ⟧ᴰ ↑))) (D-Z d (I^ _)))
  (Eq.trans (act-inv-↑ ⟦ dl ⟧ᴰ false 𝐈 (𝐙 ∷ I^ _))
            (Eq.cong (λ P → proj₁ P , 𝐈 ∷ proj₂ P) (QD-Z dl)))

QX-Z : (M : Xc (₁₊ n)) → act (inv ⟦ M ⟧ˣ) (Z₀ n) ≡ (false , ztop n)
QX-Z (E₁ ,ˣ dl) = QD-Z dl
QX-Z (E₂ ,ˣ dl) = QD-Z dl

------------------------------------------------------------------------
-- Z-circuits

-- A ladder, inverted, on Z on the top wire.
QL : Lad t (₁₊ n) → Pauli (₁₊ n)
QL lad = act (inv ⟦ lad ⟧ᴸ) (false , ztop _)

QL-up : (b : BT t u) (lad : Lad u (₁₊ n)) →
        QL (b ∷ᴮ lad) ≡ act (inv ⟪ Bl b ⟫) (proj₁ (QL lad) , 𝐈 ∷ proj₂ (QL lad))
QL-up b lad = Eq.cong (act (inv ⟪ Bl b ⟫)) (act-inv-↑ ⟦ lad ⟧ᴸ false 𝐈 (ztop _))

QL-head : (lad : Lad t (₁₊ n)) → QL lad ≡ (proj₁ (QL lad) , T t ∷ tail (proj₂ (QL lad)))
QL-step : (b : BT t u) (lad : Lad u (₁₊ n)) →
          QL (b ∷ᴮ lad) ≡ (proj₁ (QL lad) , T t ∷ ℓB b ∷ tail (proj₂ (QL lad)))

QL-step b lad = Eq.trans (QL-up b lad)
  (Eq.trans (Eq.cong (λ P → act (inv ⟪ Bl b ⟫) (proj₁ P , 𝐈 ∷ proj₂ P)) (QL-head lad))
            (B-act b (proj₁ (QL lad)) (tail (proj₂ (QL lad)))))

QL-head (top C₁) = refl
QL-head (top C₂) = refl
QL-head {t = t} (b ∷ᴮ lad) = Eq.trans (QL-step b lad)
  (Eq.sym (Eq.cong (λ P → proj₁ P , T t ∷ tail (proj₂ P)) (QL-step b lad)))

QL-inj : (lad lad' : Lad t (₁₊ n)) → QL lad ≡ QL lad' → lad ≡ lad'
QL-inj (top c) (top c') e = Eq.cong top (csign-inj c c' (Eq.trans (csign-QL c) (Eq.trans (Eq.cong proj₁ e) (Eq.sym (csign-QL c')))))
  where
  csign-QL : (c : CT) → csign c ≡ proj₁ (QL (top c))
  csign-QL C₁ = refl
  csign-QL C₂ = refl
QL-inj {t = t} (_∷ᴮ_ {u = u} b lad) (b' ∷ᴮ lad') e
  with e' ← Eq.trans (Eq.sym (QL-step b lad)) (Eq.trans e (QL-step b' lad'))
  with refl ← Eq.trans (Eq.sym (pickB-ok b))
                (Eq.trans (Eq.cong (pickB t ∘ head ∘ tail ∘ proj₂) e') (pickB-ok b'))
  = Eq.cong (b ∷ᴮ_) (QL-inj lad lad' (Eq.trans (QL-head lad)
      (Eq.trans (Eq.cong (λ P → proj₁ P , T u ∷ tail (tail (proj₂ P))) e') (Eq.sym (QL-head lad')))))

-- A Z-circuit, inverted, on Z on the top wire.
QZ : Zc (₁₊ n) → Pauli (₁₊ n)
QZ L = act (inv ⟦ L ⟧ᶻ) (false , ztop _)

QZ-up : (L : Zc (₁₊ n)) → QZ (up L) ≡ (proj₁ (QZ L) , 𝐈 ∷ proj₂ (QZ L))
QZ-up L = act-inv-↑ ⟦ L ⟧ᶻ false 𝐈 (ztop _)

QZ-at : (a : AT t) (lad : Lad t (₁₊ n)) →
        QZ (at a lad) ≡ (proj₁ (QL lad) , ℓA a ∷ tail (proj₂ (QL lad)))
QZ-at a lad = Eq.trans (Eq.cong (act (inv ⟪ Al a ⟫)) (QL-head lad))
  (A-act a (proj₁ (QL lad)) (tail (proj₂ (QL lad))))

QZ-inj : (L L' : Zc (₁₊ n)) → QZ L ≡ QZ L' → L ≡ L'
QZ-inj (up L) (up L') e = Eq.cong up (QZ-inj L L'
  (Eq.cong (λ P → proj₁ P , tail (proj₂ P)) (Eq.trans (Eq.sym (QZ-up L)) (Eq.trans e (QZ-up L')))))
QZ-inj (up L) (at a lad) e = ⊥-elim (𝐈≢ℓA a
  (Eq.cong (head ∘ proj₂) (Eq.trans (Eq.sym (QZ-up L)) (Eq.trans e (QZ-at a lad)))))
QZ-inj (at a lad) (up L) e = ⊥-elim (𝐈≢ℓA a
  (Eq.cong (head ∘ proj₂) (Eq.trans (Eq.sym (QZ-up L)) (Eq.trans (Eq.sym e) (QZ-at a lad)))))
QZ-inj (at {t = t} a lad) (at a' lad') e
  with e' ← Eq.trans (Eq.sym (QZ-at a lad)) (Eq.trans e (QZ-at a' lad'))
  with refl ← Eq.trans (Eq.sym (pickA-ok a)) (Eq.trans (Eq.cong (pickA ∘ head ∘ proj₂) e') (pickA-ok a'))
  = Eq.cong (at a) (QL-inj lad lad' (Eq.trans (QL-head lad)
      (Eq.trans (Eq.cong (λ P → proj₁ P , T t ∷ tail (proj₂ P)) e') (Eq.sym (QL-head lad')))))

------------------------------------------------------------------------
-- Normal forms

-- The sign, and the normal form with sign +.
sign : NF n → Bool
sign (nf₀ s)     = s
sign (nfₛ _ _ N) = sign N

unsign : NF n → NF n
unsign (nf₀ _)     = nf₀ false
unsign (nfₛ L M N) = nfₛ L M (unsign N)

-- A normal form is its sign and its unsigned form.
unsign-sign : (nf nf' : NF n) → unsign nf ≡ unsign nf' → sign nf ≡ sign nf' → nf ≡ nf'
unsign-sign (nf₀ s)     (nf₀ s')       _ e' = Eq.cong nf₀ e'
unsign-sign (nfₛ L M N) (nfₛ L' M' N') e e' =
  Eq.cong₂ (λ p N → nfₛ (proj₁ p) (proj₂ p) N) (Eq.cong heads e) (unsign-sign N N' (Eq.cong rest e) e')
  where
  heads : NF (₁₊ m) → Zc (₁₊ m) × Xc (₁₊ m)
  heads (nfₛ L M _) = L , M
  rest : NF (₁₊ m) → NF m
  rest (nfₛ _ _ N) = N

-- The inverse of a normal form on Z₀, and of its last two parts on X₀.
nf-Z : (L : Zc (₁₊ n)) (M : Xc (₁₊ n)) (N : NF n) → act (inv ⟦ nfₛ L M N ⟧ⁿ) (Z₀ n) ≡ QZ L
nf-Z L M N = Eq.cong (act (inv ⟦ L ⟧ᶻ))
  (Eq.trans (Eq.cong (act (inv ⟦ M ⟧ˣ)) (fix-↑ ⟦ N ⟧ⁿ false 𝐙)) (QX-Z M))

nf-X : (M : Xc (₁₊ n)) (N : NF n) → act (inv (⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ)) (X₀ n) ≡ QX M
nf-X M N = Eq.cong (act (inv ⟦ M ⟧ˣ)) (fix-↑ ⟦ N ⟧ⁿ false 𝐗)

act-unique : (nf nf' : NF n) → ⟦ nf ⟧ⁿ ≗ᵃ ⟦ nf' ⟧ⁿ → unsign nf ≡ unsign nf'
act-unique (nf₀ _) (nf₀ _) e = refl
act-unique (nfₛ L M N) (nfₛ L' M' N') e
  with refl ← QZ-inj L L' (Eq.trans (Eq.sym (nf-Z L M N)) (Eq.trans (≗ᵃ-inv {w = ⟦ nfₛ L M N ⟧ⁿ} {v = ⟦ nfₛ L' M' N' ⟧ⁿ} e (Z₀ _))
                                     (nf-Z L' M' N')))
  with e₂ ← ≗ᵃ-cancel {w = ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ} {v = ⟦ N' ⟧ⁿ ↑ • ⟦ M' ⟧ˣ} ⟦ L ⟧ᶻ e
  with refl ← QX-inj M M' (Eq.trans (Eq.sym (nf-X M N)) (Eq.trans (≗ᵃ-inv {w = ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ} {v = ⟦ N' ⟧ⁿ ↑ • ⟦ M' ⟧ˣ} e₂ (X₀ _)) (nf-X M' N')))
  = Eq.cong (nfₛ L M) (act-unique N N' (≗ᵃ-↑ ⟦ N ⟧ⁿ ⟦ N' ⟧ⁿ
      (≗ᵃ-cancel {w = ⟦ N ⟧ⁿ ↑} {v = ⟦ N' ⟧ⁿ ↑} ⟦ M ⟧ˣ e₂)))
