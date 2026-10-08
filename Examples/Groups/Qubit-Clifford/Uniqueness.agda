------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal forms that act alike on Pauli operators are equal, but for
-- their scalar
--
-- A normal form W = N ↑ • M • L acts on Pauli operators by conjugation
-- (Pauli).  N ↑ fixes Z₀, the operator Z on wire 0, and the X-normal
-- circuit M moves Z from the top wire to wire 0 (Lemma 5.3), so W⁻¹
-- sends Z₀ to L⁻¹ Z_top L, which determines the Z-normal circuit L
-- (QZ-inj, the uniqueness half of Lemma 5.1); then (N ↑ • M)⁻¹ sends X₀
-- to M⁻¹ X₀ M, which determines M (QX-inj, Lemma 5.2); and N ↑ acts on
-- the wires above as N.  The scalar ω^p acts trivially: the matrix
-- semantics tells it (Proposition 5.5 leaves it open).  The paper's
-- first tensor factor is the top wire here, its last one wire 0.
--
-- The operators are read one wire at a time.  Climbing a ladder, a B
-- gate leaves Z on its lower wire and, on its upper wire, a letter that
-- tells it from the other B gates; descending a D-ladder, a D gate
-- leaves on its lower wire a letter that tells it from the other D
-- gates and passes X or Y up.  These gates shift the phase by a fixed
-- amount, so the phase at the end tells C₁ from C₂, and with the letter
-- the E gates apart.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Uniqueness where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₀ ; ₁₊ ; ₂₊)

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Engine using (⟪_⟫)
open import Examples.Groups.Qubit-Clifford.NormalForm
open import Examples.Groups.Qubit-Clifford.Pauli

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- Circuits that act alike

infix 4 _≗ᵃ_
_≗ᵃ_ : Circuit n → Circuit n → Set
w ≗ᵃ v = ∀ P → act w P ≡ act v P

-- Their inverses act alike.
≗ᵃ-inv : {w v : Circuit n} → w ≗ᵃ v → ∀ P → act⁻ w P ≡ act⁻ v P
≗ᵃ-inv {w = w} {v} e P = begin
  act⁻ w P                         ≡⟨ Eq.cong (act⁻ w) (Eq.sym (act-act⁻ v P)) ⟩
  act⁻ w (act v (act⁻ v P))        ≡⟨ Eq.cong (act⁻ w) (Eq.sym (e (act⁻ v P))) ⟩
  act⁻ w (act w (act⁻ v P))        ≡⟨ act⁻-act w (act⁻ v P) ⟩
  act⁻ v P                         ∎
  where open Eq.≡-Reasoning

-- A common last factor cancels.
≗ᵃ-cancel : {w v : Circuit n} (u : Circuit n) → (w • u) ≗ᵃ (v • u) → w ≗ᵃ v
≗ᵃ-cancel {w = w} {v} u e P = begin
  act w P                         ≡⟨ Eq.cong (act w) (Eq.sym (act-act⁻ u P)) ⟩
  act w (act u (act⁻ u P))        ≡⟨ e (act⁻ u P) ⟩
  act v (act u (act⁻ u P))        ≡⟨ Eq.cong (act v) (act-act⁻ u P) ⟩
  act v P                         ∎
  where open Eq.≡-Reasoning

-- Circuits one wire up act alike only if they do one wire down.
≗ᵃ-↑ : (w v : Circuit n) → (w ↑) ≗ᵃ (v ↑) → w ≗ᵃ v
≗ᵃ-↑ w v e (σ , ps) = Eq.cong (λ P → proj₁ P , tail (proj₂ P))
  (Eq.trans (Eq.sym (act-↑ w σ 𝐈 ps)) (Eq.trans (e (σ , 𝐈 ∷ ps)) (act-↑ v σ 𝐈 ps)))

-- The inverse of a circuit one wire up fixes wire 0 when the wires
-- above carry I.
fix-↑ : (w : Circuit n) (σ : Ph) (p : Letter) → act⁻ (w ↑) (σ , p ∷ I^ n) ≡ (σ , p ∷ I^ n)
fix-↑ w σ p = Eq.trans (act⁻-↑ w σ p (I^ _))
  (Eq.cong (λ P → proj₁ P , p ∷ proj₂ P) (act⁻-I w σ))

------------------------------------------------------------------------
-- Pauli operators on wire 0 and on the top wire

Z₀ X₀ : (n : ℕ) → Pauli (₁₊ n)
Z₀ n = p0 , 𝐙 ∷ I^ n
X₀ n = p0 , 𝐗 ∷ I^ n

ztop : (n : ℕ) → Vec Letter (₁₊ n)
ztop zero    = 𝐙 ∷ []
ztop (suc n) = 𝐈 ∷ ztop n

------------------------------------------------------------------------
-- The gates A to E on Pauli operators (Figure 2), read backwards

-- An A gate, on Z.
ℓA : AT → Letter
ℓA A₁ = 𝐙
ℓA A₂ = 𝐗
ℓA A₃ = 𝐘

αA : AT → Ph
αA A₁ = p0
αA A₂ = p0
αA A₃ = p1

-- A B gate, on I below and Z above.
ℓB : BT → Letter
ℓB B₁ = 𝐈
ℓB B₂ = 𝐗
ℓB B₃ = 𝐘
ℓB B₄ = 𝐙

βB : BT → Ph
βB B₁ = p0
βB B₂ = p0
βB B₃ = p1
βB B₄ = p0

-- A C gate, on Z.
csign : CT → Ph
csign C₁ = p0
csign C₂ = p2

-- A D gate, on X or Y below and I above, and on Z below.
data XY : Set where
  xX xY : XY

xy : XY → Letter
xy xX = 𝐗
xy xY = 𝐘

ℓD : DT → Letter
ℓD D₁ = 𝐈
ℓD D₂ = 𝐗
ℓD D₃ = 𝐘
ℓD D₄ = 𝐙

δD : DT → Ph
δD D₁ = p0
δD D₂ = p0
δD D₃ = p1
δD D₄ = p0

D-Z : (d : DT) (R : Vec Letter n) →
      act⁻ ⟪ Dl d ⟫ (p0 , 𝐙 ∷ 𝐈 ∷ R) ≡ (p0 , 𝐈 ∷ 𝐙 ∷ R)
D-Z D₁ R = refl
D-Z D₂ R = refl
D-Z D₃ R = refl
D-Z D₄ R = refl

-- An E gate, on X.
ℓE : ET → XY
ℓE E₁ = xX
ℓE E₂ = xY
ℓE E₃ = xX
ℓE E₄ = xY

σE : ET → Ph
σE E₁ = p0
σE E₂ = p3
σE E₃ = p2
σE E₄ = p1

A-act : (a : AT) (σ : Ph) (R : Vec Letter n) →
        act⁻ ⟪ Al a ⟫ (σ , 𝐙 ∷ R) ≡ (σ ⊕ αA a , ℓA a ∷ R)
A-act A₁ p0 R = refl
A-act A₁ p1 R = refl
A-act A₁ p2 R = refl
A-act A₁ p3 R = refl
A-act A₂ p0 R = refl
A-act A₂ p1 R = refl
A-act A₂ p2 R = refl
A-act A₂ p3 R = refl
A-act A₃ p0 R = refl
A-act A₃ p1 R = refl
A-act A₃ p2 R = refl
A-act A₃ p3 R = refl

B-act : (b : BT) (σ : Ph) (R : Vec Letter n) →
        act⁻ ⟪ Bl b ⟫ (σ , 𝐈 ∷ 𝐙 ∷ R) ≡ (σ ⊕ βB b , 𝐙 ∷ ℓB b ∷ R)
B-act B₁ p0 R = refl
B-act B₁ p1 R = refl
B-act B₁ p2 R = refl
B-act B₁ p3 R = refl
B-act B₂ p0 R = refl
B-act B₂ p1 R = refl
B-act B₂ p2 R = refl
B-act B₂ p3 R = refl
B-act B₃ p0 R = refl
B-act B₃ p1 R = refl
B-act B₃ p2 R = refl
B-act B₃ p3 R = refl
B-act B₄ p0 R = refl
B-act B₄ p1 R = refl
B-act B₄ p2 R = refl
B-act B₄ p3 R = refl

D-act : (d : DT) (ℓ : XY) (σ : Ph) (R : Vec Letter n) →
        act⁻ ⟪ Dl d ⟫ (σ , xy ℓ ∷ 𝐈 ∷ R) ≡ (σ ⊕ δD d , ℓD d ∷ xy ℓ ∷ R)
D-act D₁ xX p0 R = refl
D-act D₁ xX p1 R = refl
D-act D₁ xX p2 R = refl
D-act D₁ xX p3 R = refl
D-act D₁ xY p0 R = refl
D-act D₁ xY p1 R = refl
D-act D₁ xY p2 R = refl
D-act D₁ xY p3 R = refl
D-act D₂ xX p0 R = refl
D-act D₂ xX p1 R = refl
D-act D₂ xX p2 R = refl
D-act D₂ xX p3 R = refl
D-act D₂ xY p0 R = refl
D-act D₂ xY p1 R = refl
D-act D₂ xY p2 R = refl
D-act D₂ xY p3 R = refl
D-act D₃ xX p0 R = refl
D-act D₃ xX p1 R = refl
D-act D₃ xX p2 R = refl
D-act D₃ xX p3 R = refl
D-act D₃ xY p0 R = refl
D-act D₃ xY p1 R = refl
D-act D₃ xY p2 R = refl
D-act D₃ xY p3 R = refl
D-act D₄ xX p0 R = refl
D-act D₄ xX p1 R = refl
D-act D₄ xX p2 R = refl
D-act D₄ xX p3 R = refl
D-act D₄ xY p0 R = refl
D-act D₄ xY p1 R = refl
D-act D₄ xY p2 R = refl
D-act D₄ xY p3 R = refl

------------------------------------------------------------------------
-- Reading the gates back

pickA : Letter → AT
pickA 𝐗 = A₂
pickA 𝐘 = A₃
pickA 𝐙 = A₁
pickA 𝐈 = A₁

pickA-ok : (a : AT) → pickA (ℓA a) ≡ a
pickA-ok A₁ = refl
pickA-ok A₂ = refl
pickA-ok A₃ = refl

𝐈≢ℓA : (a : AT) → 𝐈 ≢ ℓA a
𝐈≢ℓA A₁ ()
𝐈≢ℓA A₂ ()
𝐈≢ℓA A₃ ()

pickB : Letter → BT
pickB 𝐈 = B₁
pickB 𝐗 = B₂
pickB 𝐘 = B₃
pickB 𝐙 = B₄

pickB-ok : (b : BT) → pickB (ℓB b) ≡ b
pickB-ok B₁ = refl
pickB-ok B₂ = refl
pickB-ok B₃ = refl
pickB-ok B₄ = refl

csign-inj : (c c' : CT) → csign c ≡ csign c' → c ≡ c'
csign-inj C₁ C₁ _ = refl
csign-inj C₂ C₂ _ = refl

pickD : Letter → DT
pickD 𝐈 = D₁
pickD 𝐗 = D₂
pickD 𝐘 = D₃
pickD 𝐙 = D₄

pickD-ok : (d : DT) → pickD (ℓD d) ≡ d
pickD-ok D₁ = refl
pickD-ok D₂ = refl
pickD-ok D₃ = refl
pickD-ok D₄ = refl

xy-inj : (ℓ ℓ' : XY) → xy ℓ ≡ xy ℓ' → ℓ ≡ ℓ'
xy-inj xX xX _ = refl
xy-inj xY xY _ = refl

E-inj : (e e' : ET) → ℓE e ≡ ℓE e' → σE e ≡ σE e' → e ≡ e'
E-inj E₁ E₁ _ _ = refl
E-inj E₂ E₂ _ _ = refl
E-inj E₃ E₃ _ _ = refl
E-inj E₄ E₄ _ _ = refl
E-inj E₁ E₂ () _
E-inj E₁ E₃ _ ()
E-inj E₁ E₄ () _
E-inj E₂ E₁ () _
E-inj E₂ E₃ () _
E-inj E₂ E₄ _ ()
E-inj E₃ E₁ _ ()
E-inj E₃ E₂ () _
E-inj E₃ E₄ () _
E-inj E₄ E₁ () _
E-inj E₄ E₂ _ ()
E-inj E₄ E₃ () _

------------------------------------------------------------------------
-- X-normal circuits

-- A D-ladder, inverted, on X or Y on wire 0.
QD : DL (₁₊ n) → XY → Ph → Pauli (₁₊ n)
QD dl ℓ σ = act⁻ ⟦ dl ⟧ᴰ (σ , xy ℓ ∷ I^ _)

QD-step : (d : DT) (dl : DL (₁₊ n)) (ℓ : XY) (σ : Ph) →
          QD (d ∷ᴰ dl) ℓ σ ≡ (proj₁ (QD dl ℓ (σ ⊕ δD d)) , ℓD d ∷ proj₂ (QD dl ℓ (σ ⊕ δD d)))
QD-step d dl ℓ σ = Eq.trans (Eq.cong (act⁻ (⟦ dl ⟧ᴰ ↑)) (D-act d ℓ σ (I^ _)))
  (act⁻-↑ ⟦ dl ⟧ᴰ (σ ⊕ δD d) (ℓD d) (xy ℓ ∷ I^ _))

QD-inj : (dl dl' : DL (₁₊ n)) (ℓ ℓ' : XY) (σ σ' : Ph) →
         QD dl ℓ σ ≡ QD dl' ℓ' σ' → dl ≡ dl' × ℓ ≡ ℓ' × σ ≡ σ'
QD-inj []ᴰ []ᴰ ℓ ℓ' σ σ' e = refl , xy-inj ℓ ℓ' (Eq.cong (head ∘ proj₂) e) , Eq.cong proj₁ e
QD-inj (d ∷ᴰ dl) (d' ∷ᴰ dl') ℓ ℓ' σ σ' e
  with e' ← Eq.trans (Eq.sym (QD-step d dl ℓ σ)) (Eq.trans e (QD-step d' dl' ℓ' σ'))
  with refl ← Eq.trans (Eq.sym (pickD-ok d)) (Eq.trans (Eq.cong (pickD ∘ head ∘ proj₂) e') (pickD-ok d'))
  with (p , q , r) ← QD-inj dl dl' ℓ ℓ' (σ ⊕ δD d) (σ' ⊕ δD d) (Eq.cong (λ P → proj₁ P , tail (proj₂ P)) e')
  = Eq.cong (d ∷ᴰ_) p , q , ⊕-cancel σ σ' (δD d) r

-- An X-normal circuit, inverted, on X₀; it moves Z from wire 0 to the
-- top.
QX : Xc (₁₊ n) → Pauli (₁₊ n)
QX M = act⁻ ⟦ M ⟧ˣ (X₀ _)

QX-def : (e : ET) (dl : DL (₁₊ n)) → QX (e ,ˣ dl) ≡ QD dl (ℓE e) (σE e)
QX-def E₁ dl = refl
QX-def E₂ dl = refl
QX-def E₃ dl = refl
QX-def E₄ dl = refl

QX-inj : (M M' : Xc (₁₊ n)) → QX M ≡ QX M' → M ≡ M'
QX-inj (e ,ˣ dl) (e' ,ˣ dl') h
  with (p , q , r) ← QD-inj dl dl' (ℓE e) (ℓE e') (σE e) (σE e')
                       (Eq.trans (Eq.sym (QX-def e dl)) (Eq.trans h (QX-def e' dl')))
  = Eq.cong₂ _,ˣ_ (E-inj e e' q r) p

QD-Z : (dl : DL (₁₊ n)) → act⁻ ⟦ dl ⟧ᴰ (Z₀ n) ≡ (p0 , ztop n)
QD-Z []ᴰ       = refl
QD-Z (d ∷ᴰ dl) = Eq.trans (Eq.cong (act⁻ (⟦ dl ⟧ᴰ ↑)) (D-Z d (I^ _)))
  (Eq.trans (act⁻-↑ ⟦ dl ⟧ᴰ p0 𝐈 (𝐙 ∷ I^ _))
            (Eq.cong (λ P → proj₁ P , 𝐈 ∷ proj₂ P) (QD-Z dl)))

-- Lemma 5.3, read backwards.
QX-Z : (M : Xc (₁₊ n)) → act⁻ ⟦ M ⟧ˣ (Z₀ n) ≡ (p0 , ztop n)
QX-Z (E₁ ,ˣ dl) = QD-Z dl
QX-Z (E₂ ,ˣ dl) = QD-Z dl
QX-Z (E₃ ,ˣ dl) = QD-Z dl
QX-Z (E₄ ,ˣ dl) = QD-Z dl

------------------------------------------------------------------------
-- Z-normal circuits

-- A ladder, inverted, on Z on the top wire.
QL : Lad (₁₊ n) → Pauli (₁₊ n)
QL lad = act⁻ ⟦ lad ⟧ᴸ (p0 , ztop _)

QL-up : (b : BT) (lad : Lad (₁₊ n)) →
        QL (b ∷ᴮ lad) ≡ act⁻ ⟪ Bl b ⟫ (proj₁ (QL lad) , 𝐈 ∷ proj₂ (QL lad))
QL-up b lad = Eq.cong (act⁻ ⟪ Bl b ⟫) (act⁻-↑ ⟦ lad ⟧ᴸ p0 𝐈 (ztop _))

QL-head : (lad : Lad (₁₊ n)) → QL lad ≡ (proj₁ (QL lad) , 𝐙 ∷ tail (proj₂ (QL lad)))
QL-step : (b : BT) (lad : Lad (₁₊ n)) →
          QL (b ∷ᴮ lad) ≡ (proj₁ (QL lad) ⊕ βB b , 𝐙 ∷ ℓB b ∷ tail (proj₂ (QL lad)))

QL-step b lad = Eq.trans (QL-up b lad)
  (Eq.trans (Eq.cong (λ P → act⁻ ⟪ Bl b ⟫ (proj₁ P , 𝐈 ∷ proj₂ P)) (QL-head lad))
            (B-act b (proj₁ (QL lad)) (tail (proj₂ (QL lad)))))

QL-head (top C₁) = refl
QL-head (top C₂) = refl
QL-head (b ∷ᴮ lad) = Eq.trans (QL-step b lad)
  (Eq.sym (Eq.cong (λ P → proj₁ P , 𝐙 ∷ tail (proj₂ P)) (QL-step b lad)))

-- Equal phases and equal letters above the bottom wire, which carries Z.
QL-from : (lad lad' : Lad (₁₊ n)) → proj₁ (QL lad) ≡ proj₁ (QL lad') →
          tail (proj₂ (QL lad)) ≡ tail (proj₂ (QL lad')) → QL lad ≡ QL lad'
QL-from lad lad' p t =
  Eq.trans (QL-head lad) (Eq.trans (Eq.cong₂ (λ σ R → σ , 𝐙 ∷ R) p t) (Eq.sym (QL-head lad')))

QL-inj : (lad lad' : Lad (₁₊ n)) → QL lad ≡ QL lad' → lad ≡ lad'
QL-inj (top c) (top c') e = Eq.cong top (csign-inj c c' (Eq.trans (csign-QL c) (Eq.trans (Eq.cong proj₁ e) (Eq.sym (csign-QL c')))))
  where
  csign-QL : (c : CT) → csign c ≡ proj₁ (QL (top c))
  csign-QL C₁ = refl
  csign-QL C₂ = refl
QL-inj (b ∷ᴮ lad) (b' ∷ᴮ lad') e
  with e' ← Eq.trans (Eq.sym (QL-step b lad)) (Eq.trans e (QL-step b' lad'))
  with refl ← Eq.trans (Eq.sym (pickB-ok b))
                (Eq.trans (Eq.cong (pickB ∘ head ∘ tail ∘ proj₂) e') (pickB-ok b'))
  = Eq.cong (b ∷ᴮ_) (QL-inj lad lad' (QL-from lad lad'
      (⊕-cancel _ _ (βB b) (Eq.cong proj₁ e'))
      (Eq.cong (tail ∘ tail ∘ proj₂) e')))

-- A Z-normal circuit, inverted, on Z on the top wire.
QZ : Zc (₁₊ n) → Pauli (₁₊ n)
QZ L = act⁻ ⟦ L ⟧ᶻ (p0 , ztop _)

QZ-up : (L : Zc (₁₊ n)) → QZ (up L) ≡ (proj₁ (QZ L) , 𝐈 ∷ proj₂ (QZ L))
QZ-up L = act⁻-↑ ⟦ L ⟧ᶻ p0 𝐈 (ztop _)

QZ-at : (a : AT) (lad : Lad (₁₊ n)) →
        QZ (at a lad) ≡ (proj₁ (QL lad) ⊕ αA a , ℓA a ∷ tail (proj₂ (QL lad)))
QZ-at a lad = Eq.trans (Eq.cong (act⁻ ⟪ Al a ⟫) (QL-head lad))
  (A-act a (proj₁ (QL lad)) (tail (proj₂ (QL lad))))

QZ-inj : (L L' : Zc (₁₊ n)) → QZ L ≡ QZ L' → L ≡ L'
QZ-inj (up L) (up L') e = Eq.cong up (QZ-inj L L'
  (Eq.cong (λ P → proj₁ P , tail (proj₂ P)) (Eq.trans (Eq.sym (QZ-up L)) (Eq.trans e (QZ-up L')))))
QZ-inj (up L) (at a lad) e = ⊥-elim (𝐈≢ℓA a
  (Eq.cong (head ∘ proj₂) (Eq.trans (Eq.sym (QZ-up L)) (Eq.trans e (QZ-at a lad)))))
QZ-inj (at a lad) (up L) e = ⊥-elim (𝐈≢ℓA a
  (Eq.cong (head ∘ proj₂) (Eq.trans (Eq.sym (QZ-up L)) (Eq.trans (Eq.sym e) (QZ-at a lad)))))
QZ-inj (at a lad) (at a' lad') e
  with e' ← Eq.trans (Eq.sym (QZ-at a lad)) (Eq.trans e (QZ-at a' lad'))
  with refl ← Eq.trans (Eq.sym (pickA-ok a)) (Eq.trans (Eq.cong (pickA ∘ head ∘ proj₂) e') (pickA-ok a'))
  = Eq.cong (at a) (QL-inj lad lad' (QL-from lad lad'
      (⊕-cancel _ _ (αA a) (Eq.cong proj₁ e'))
      (Eq.cong (tail ∘ proj₂) e')))

------------------------------------------------------------------------
-- Normal forms

-- The scalar, and the normal form with scalar 1.
phase : NF n → Fin 8
phase (nf₀ p)     = p
phase (nfₛ _ _ N) = phase N

unphase : NF n → NF n
unphase (nf₀ _)     = nf₀ ₀
unphase (nfₛ L M N) = nfₛ L M (unphase N)

-- A normal form is its scalar and the rest.
unphase-phase : (nf nf' : NF n) → unphase nf ≡ unphase nf' → phase nf ≡ phase nf' → nf ≡ nf'
unphase-phase (nf₀ p)     (nf₀ p')       _ e' = Eq.cong nf₀ e'
unphase-phase (nfₛ L M N) (nfₛ L' M' N') e e' =
  Eq.cong₂ (λ p N → nfₛ (proj₁ p) (proj₂ p) N) (Eq.cong heads e) (unphase-phase N N' (Eq.cong rest e) e')
  where
  heads : NF (₁₊ m) → Zc (₁₊ m) × Xc (₁₊ m)
  heads (nfₛ L M _) = L , M
  rest : NF (₁₊ m) → NF m
  rest (nfₛ _ _ N) = N

-- The inverse of a normal form on Z₀, and of its last two parts on X₀.
nf-Z : (L : Zc (₁₊ n)) (M : Xc (₁₊ n)) (N : NF n) → act⁻ ⟦ nfₛ L M N ⟧ⁿ (Z₀ n) ≡ QZ L
nf-Z L M N = Eq.cong (act⁻ ⟦ L ⟧ᶻ)
  (Eq.trans (Eq.cong (act⁻ ⟦ M ⟧ˣ) (fix-↑ ⟦ N ⟧ⁿ p0 𝐙)) (QX-Z M))

nf-X : (M : Xc (₁₊ n)) (N : NF n) → act⁻ (⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ) (X₀ n) ≡ QX M
nf-X M N = Eq.cong (act⁻ ⟦ M ⟧ˣ) (fix-↑ ⟦ N ⟧ⁿ p0 𝐗)

act-unique : (nf nf' : NF n) → ⟦ nf ⟧ⁿ ≗ᵃ ⟦ nf' ⟧ⁿ → unphase nf ≡ unphase nf'
act-unique (nf₀ _) (nf₀ _) e = refl
act-unique (nfₛ L M N) (nfₛ L' M' N') e
  with refl ← QZ-inj L L' (Eq.trans (Eq.sym (nf-Z L M N)) (Eq.trans (≗ᵃ-inv {w = ⟦ nfₛ L M N ⟧ⁿ} {v = ⟦ nfₛ L' M' N' ⟧ⁿ} e (Z₀ _))
                                     (nf-Z L' M' N')))
  with e₂ ← ≗ᵃ-cancel {w = ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ} {v = ⟦ N' ⟧ⁿ ↑ • ⟦ M' ⟧ˣ} ⟦ L ⟧ᶻ e
  with refl ← QX-inj M M' (Eq.trans (Eq.sym (nf-X M N)) (Eq.trans (≗ᵃ-inv {w = ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ} {v = ⟦ N' ⟧ⁿ ↑ • ⟦ M' ⟧ˣ} e₂ (X₀ _)) (nf-X M' N')))
  = Eq.cong (nfₛ L M) (act-unique N N' (≗ᵃ-↑ ⟦ N ⟧ⁿ ⟦ N' ⟧ⁿ
      (≗ᵃ-cancel {w = ⟦ N ⟧ⁿ ↑} {v = ⟦ N' ⟧ⁿ ↑} ⟦ M ⟧ˣ e₂)))
