------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators of Li, Ross and Selinger at n = 8, decoded as circuits
-- over Σ₁, and the transport of their relations.
--
-- Each generator is a circuit b conjugated by a Coxeter word: (-1)_[a]
-- is m0 (that is (-1)_[0]) carried by a frame sending 0 to a, X_[a,b]
-- is T 0 (that is X_[0,1]) carried by one sending 0, 1 to a, b, and
-- K_[a,b,c,d] is NK (K_[0,1,2,3]) carried by one sending 0, 1, 2, 3 to
-- a, b, c, d.  By the frame lemma of Perm the result depends only on
-- where the frame sends those states, since the T i above them commute
-- with b (Figure 7's (85)–(93), and the Coxeter relations).  So a word
-- whose letters are all carried by one frame F from a word w₀ decodes
-- to the conjugate of w₀'s decoding by F (Tr, tr-sound), and a relation
-- of Table 1 follows from one standard instance of it (transport).
--
-- The development is parameterised by the Coxeter relations for the
-- circuits T d, which Toffoli.Coxeter derives from Figure 4.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.CCX+HH-3qubit-opus.Gates using (G₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics using (_===₁⁺_)
open import Examples.Groups.CCX+HH-3qubit-opus.Perm using (Coxeter)

module Examples.Groups.CCX+HH-3qubit-opus.Decode (cox : Coxeter _===₁⁺_) where

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; _<_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Bool.Base using (true)
open import Data.Fin using (#_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s ; _∸_)
import Data.Nat.Properties as ℕP
import Data.Nat.Base as ℕ
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics as L using (Gen ; M-gen ; X-gen ; K-gen)

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Encoding using (lt)
open import Examples.Groups.CCX+HH-3qubit-opus.Perm hiding (Coxeter)
open import Examples.Groups.CCX+HH-3qubit-opus.Frame
open import Examples.Groups.CCX+HH-3qubit-opus.Check using (all8 ; below ; eqᵇ ; agree ; everywhere ; distinct)
import Examples.Groups.Symmetric.Syntactics as Sym
open Sym using (gate₂ ; σ-gate ; _↥)

open Complete cox public
open PB _===₁⁺_
open PP _===₁⁺_ using (by-assoc)
open SR (PP.word-setoid _===₁⁺_)
open Coxeter cox

------------------------------------------------------------------------
-- What the T i above a base circuit commute with

-- (85)–(90): the T i with i ≥ 1 commute with (-1)_[0].
comm-m0 : Comm≥ 1 m0
comm-m0 (suc zero)                               _ _ = axiom (fig7 r85)
comm-m0 (suc (suc zero))                         _ _ = axiom (fig7 r86)
comm-m0 (suc (suc (suc zero)))                   _ _ = axiom (fig7 r87)
comm-m0 (suc (suc (suc (suc zero))))             _ _ = axiom (fig7 r88)
comm-m0 (suc (suc (suc (suc (suc zero)))))       _ _ = axiom (fig7 r89)
comm-m0 (suc (suc (suc (suc (suc (suc zero)))))) _ _ = axiom (fig7 r90)
comm-m0 (suc (suc (suc (suc (suc (suc (suc _))))))) _ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))

-- (91)–(93): the T i with i ≥ 4 commute with K_[0,1,2,3].
comm-NK : Comm≥ 4 NKw
comm-NK zero                                     () _
comm-NK (suc zero)                               (s≤s ()) _
comm-NK (suc (suc zero))                         (s≤s (s≤s ())) _
comm-NK (suc (suc (suc zero)))                   (s≤s (s≤s (s≤s ()))) _
comm-NK (suc (suc (suc (suc zero))))             _ _ = axiom (fig7 r91)
comm-NK (suc (suc (suc (suc (suc zero)))))       _ _ = axiom (fig7 r92)
comm-NK (suc (suc (suc (suc (suc (suc zero)))))) _ _ = axiom (fig7 r93)
comm-NK (suc (suc (suc (suc (suc (suc (suc _))))))) _ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))

-- The Coxeter relations: the T i with i ≥ 2 commute with X_[0,1].
comm-T0 : Comm≥ 2 (T 0)
comm-T0 i lo hi = sym (far 0 i lo hi)

------------------------------------------------------------------------
-- The decoding

private
  <⇒≢ : {a b : Fin 8} → .(a < b) → a ≢ b
  <⇒≢ p e = ⊥-elim (FinP.<-irrefl e p)

  <-trans : {a b c : Fin 8} → a < b → b < c → a < c
  <-trans = FinP.<-trans

dist2 : {a b : Fin 8} → .(a < b) → Distinct (a ∷ b ∷ [])
dist2 p = (<⇒≢ p ∷ []) ∷ ([] ∷ [])

dist4 : {a b c d : Fin 8} → .(a < b) → .(b < c) → .(c < d) → Distinct (a ∷ b ∷ c ∷ d ∷ [])
dist4 p q r = (<⇒≢ p ∷ <⇒≢ (<-trans p q) ∷ <⇒≢ (<-trans (<-trans p q) r) ∷ [])
            ∷ (<⇒≢ q ∷ <⇒≢ (<-trans q r) ∷ []) ∷ (<⇒≢ r ∷ []) ∷ [] ∷ []

dec : Gen 8 → Word G₁
dec (M-gen a)             = Fr m0 (frame (a ∷ []) ([] ∷ []))
dec (X-gen a b p)         = Fr (T 0) (frame (a ∷ b ∷ []) (dist2 p))
dec (K-gen a b c d p q r) = Fr NKw (frame (a ∷ b ∷ c ∷ d ∷ []) (dist4 p q r))

decʷ : Word (Gen 8) → Word G₁
decʷ = dec ʷ

------------------------------------------------------------------------
-- Conjugation by a Coxeter word

Cj : CW → Word G₁ → Word G₁
Cj F w = Pc 0 F • w • Pc 0 (inv F)

Cj-ε : (F : CW) → Cj F ε ≈ ε
Cj-ε F = trans (cong refl left-unit) (Pc-inv 0 ℕP.≤-refl F)

Cj-• : (F : CW) (u v : Word G₁) → Cj F u • Cj F v ≈ Cj F (u • v)
Cj-• F u v = begin
  (P • (u • P⁻)) • (P • (v • P⁻))        ≈⟨ assoc ⟩
  P • ((u • P⁻) • (P • (v • P⁻)))        ≈⟨ cong refl assoc ⟩
  P • (u • (P⁻ • (P • (v • P⁻))))        ≈⟨ cong refl (cong refl (sym assoc)) ⟩
  P • (u • ((P⁻ • P) • (v • P⁻)))        ≈⟨ cong refl (cong refl (trans (cong (Pc-inv′ 0 ℕP.≤-refl F) refl) left-unit)) ⟩
  P • (u • (v • P⁻))                     ≈⟨ cong refl (sym assoc) ⟩
  P • ((u • v) • P⁻)                     ∎
  where
  P = Pc 0 F
  P⁻ = Pc 0 (inv F)

Cj-cong : (F : CW) {u v : Word G₁} → u ≈ v → Cj F u ≈ Cj F v
Cj-cong F e = cong refl (cong e refl)

-- A frame conjugating a circuit by itself twice.
Fr-sq : (b : Word G₁) → b • b ≈ ε → (p : CW) → Fr b p • Fr b p ≈ ε
Fr-sq b bb p = begin
  (P • (b • P⁻)) • (P • (b • P⁻))     ≈⟨ assoc ⟩
  P • ((b • P⁻) • (P • (b • P⁻)))     ≈⟨ cong refl assoc ⟩
  P • (b • (P⁻ • (P • (b • P⁻))))     ≈⟨ cong refl (cong refl (sym assoc)) ⟩
  P • (b • ((P⁻ • P) • (b • P⁻)))     ≈⟨ cong refl (cong refl (trans (cong (Pc-inv′ 0 ℕP.≤-refl p) refl) left-unit)) ⟩
  P • (b • (b • P⁻))                  ≈⟨ cong refl (sym assoc) ⟩
  P • ((b • b) • P⁻)                  ≈⟨ cong refl (trans (cong bb refl) left-unit) ⟩
  P • P⁻                              ≈⟨ Pc-inv 0 ℕP.≤-refl p ⟩
  ε                                   ∎
  where
  P = Pc 0 p
  P⁻ = Pc 0 (inv p)

-- A Coxeter word passing a frame.
Pc-Fr : (b : Word G₁) (x p : CW) → Pc 0 x • Fr b p ≈ Fr b (x • p) • Pc 0 x
Pc-Fr b x p = begin
  X • (P • (b • P⁻))                       ≈⟨ sym assoc ⟩
  (X • P) • (b • P⁻)                       ≈⟨ cong refl (cong refl (sym right-unit)) ⟩
  (X • P) • (b • (P⁻ • ε))                 ≈⟨ cong refl (cong refl (cong refl (sym (Pc-inv′ 0 ℕP.≤-refl x)))) ⟩
  (X • P) • (b • (P⁻ • (X⁻ • X)))          ≈⟨ cong refl (cong refl (sym assoc)) ⟩
  (X • P) • (b • ((P⁻ • X⁻) • X))          ≈⟨ cong refl (sym assoc) ⟩
  (X • P) • ((b • (P⁻ • X⁻)) • X)          ≈⟨ sym assoc ⟩
  ((X • P) • (b • (P⁻ • X⁻))) • X          ∎
  where
  X = Pc 0 x
  X⁻ = Pc 0 (inv x)
  P = Pc 0 p
  P⁻ = Pc 0 (inv p)

------------------------------------------------------------------------
-- Transport along a frame

-- u is u₀ with every state x replaced by act F x.
data Tr (F : CW) : Word (Gen 8) → Word (Gen 8) → Set where
  trM : {a i : Fin 8} → act F i ≡ a → Tr F [ M-gen a ]ʷ [ M-gen i ]ʷ
  -- The order proofs are explicit: being irrelevant, they could not be
  -- found by unification.
  trX : {a b i j : Fin 8} .(p : a < b) .(q : i < j) → act F i ≡ a → act F j ≡ b →
        Tr F [ X-gen a b p ]ʷ [ X-gen i j q ]ʷ
  trK : {a b c d i₀ i₁ i₂ i₃ : Fin 8} .(p : a < b) .(q : b < c) .(r : c < d)
        .(p′ : i₀ < i₁) .(q′ : i₁ < i₂) .(r′ : i₂ < i₃) →
        act F i₀ ≡ a → act F i₁ ≡ b → act F i₂ ≡ c → act F i₃ ≡ d →
        Tr F [ K-gen a b c d p q r ]ʷ [ K-gen i₀ i₁ i₂ i₃ p′ q′ r′ ]ʷ
  trε : Tr F ε ε
  tr• : {u u₀ v v₀ : Word (Gen 8)} → Tr F u u₀ → Tr F v v₀ → Tr F (u • v) (u₀ • v₀)

tr-sound : {F : CW} {u u₀ : Word (Gen 8)} → Tr F u u₀ → decʷ u ≈ Cj F (decʷ u₀)
tr-sound {F} (trM {a} {i} e) =
  trans (frame≈ 1 7 ℕP.≤-refl m0 comm-m0 (frame (a ∷ []) ([] ∷ [])) (F • frame (i ∷ []) ([] ∷ [])) ag)
        (sym (Fr-conj m0 F (frame (i ∷ []) ([] ∷ []))))
  where
  ag : ∀ x → toℕ x ℕ.< 1 → act (frame (a ∷ []) ([] ∷ [])) x ≡ act (F • frame (i ∷ []) ([] ∷ [])) x
  ag zero _ = Eq.trans (frame-act (a ∷ []) ([] ∷ []) zero a Eq.refl)
                (Eq.sym (Eq.trans (Eq.cong (act F) (frame-act (i ∷ []) ([] ∷ []) zero i Eq.refl)) e))
  ag (suc x) (s≤s ())
tr-sound {F} (trX {a} {b} {i} {j} p q e₀ e₁) =
  trans (frame≈ 2 6 ℕP.≤-refl (T 0) comm-T0 (frame (a ∷ b ∷ []) (dist2 p)) (F • frame (i ∷ j ∷ []) (dist2 q)) ag)
        (sym (Fr-conj (T 0) F (frame (i ∷ j ∷ []) (dist2 q))))
  where
  ag : ∀ x → toℕ x ℕ.< 2 → act (frame (a ∷ b ∷ []) (dist2 p)) x ≡ act (F • frame (i ∷ j ∷ []) (dist2 q)) x
  ag zero _ = Eq.trans (frame-act (a ∷ b ∷ []) (dist2 p) zero a Eq.refl)
                (Eq.sym (Eq.trans (Eq.cong (act F) (frame-act (i ∷ j ∷ []) (dist2 q) zero i Eq.refl)) e₀))
  ag (suc zero) _ = Eq.trans (frame-act (a ∷ b ∷ []) (dist2 p) (suc zero) b Eq.refl)
                (Eq.sym (Eq.trans (Eq.cong (act F) (frame-act (i ∷ j ∷ []) (dist2 q) (suc zero) j Eq.refl)) e₁))
  ag (suc (suc x)) (s≤s (s≤s ()))
tr-sound {F} (trK {a} {b} {c} {d} {i₀} {i₁} {i₂} {i₃} p q r p′ q′ r′ e₀ e₁ e₂ e₃) =
  trans (frame≈ 4 4 ℕP.≤-refl NKw comm-NK (frame ts (dist4 p q r)) (F • frame is (dist4 p′ q′ r′)) ag)
        (sym (Fr-conj NKw F (frame is (dist4 p′ q′ r′))))
  where
  ts = a ∷ b ∷ c ∷ d ∷ []
  is = i₀ ∷ i₁ ∷ i₂ ∷ i₃ ∷ []
  one : ∀ (x : Fin 8) {y i} → ts ‼ toℕ x ≡ just y → is ‼ toℕ x ≡ just i → act F i ≡ y →
        act (frame ts (dist4 p q r)) x ≡ act (F • frame is (dist4 p′ q′ r′)) x
  one x {y} {i} h h′ e = Eq.trans (frame-act ts (dist4 p q r) x y h)
    (Eq.sym (Eq.trans (Eq.cong (act F) (frame-act is (dist4 p′ q′ r′) x i h′)) e))
  ag : ∀ x → toℕ x ℕ.< 4 → act (frame ts (dist4 p q r)) x ≡ act (F • frame is (dist4 p′ q′ r′)) x
  ag zero _ = one zero Eq.refl Eq.refl e₀
  ag (suc zero) _ = one (suc zero) Eq.refl Eq.refl e₁
  ag (suc (suc zero)) _ = one (suc (suc zero)) Eq.refl Eq.refl e₂
  ag (suc (suc (suc zero))) _ = one (suc (suc (suc zero))) Eq.refl Eq.refl e₃
  ag (suc (suc (suc (suc x)))) (s≤s (s≤s (s≤s (s≤s ()))))
tr-sound {F} trε = sym (Cj-ε F)
tr-sound {F} (tr• {u₀ = u₀} {v₀ = v₀} s t) = trans (cong (tr-sound s) (tr-sound t)) (Cj-• F (decʷ u₀) (decʷ v₀))

-- A relation between words carried by one frame from a relation between
-- their standard instances.
transport : (F : CW) {l r l₀ r₀ : Word (Gen 8)} → Tr F l l₀ → Tr F r r₀ → decʷ l₀ ≈ decʷ r₀ → decʷ l ≈ decʷ r
transport F tl tr e = trans (tr-sound tl) (trans (Cj-cong F e) (sym (tr-sound tr)))

------------------------------------------------------------------------
-- Increasing lists of states are duplicate-free

data Chain : List (Fin 8) → Set where
  one  : {x : Fin 8} → Chain (x ∷ [])
  _<∷_ : {x y : Fin 8} {ys : List (Fin 8)} → .(x < y) → Chain (y ∷ ys) → Chain (x ∷ y ∷ ys)

infixr 5 _<∷_

chain-avoid : {x y : Fin 8} {ys : List (Fin 8)} → .(x < y) → Chain (y ∷ ys) → Avoid x (y ∷ ys)
chain-avoid p one      = <⇒≢ p ∷ []
chain-avoid p (q <∷ c) = <⇒≢ p ∷ chain-avoid (<-trans p q) c

chain : {ts : List (Fin 8)} → Chain ts → Distinct ts
chain one      = [] ∷ []
chain (p <∷ c) = chain-avoid p c ∷ chain c

------------------------------------------------------------------------
-- The aliases of Figure 7 as frames

-- The generator of S₈'s presentation on the states a, a + 1.
sgen : ℕ → SG 8
sgen 0 = gate₂ σ-gate
sgen 1 = (gate₂ σ-gate) ↥
sgen 2 = ((gate₂ σ-gate) ↥) ↥
sgen 3 = (((gate₂ σ-gate) ↥) ↥) ↥
sgen 4 = ((((gate₂ σ-gate) ↥) ↥) ↥) ↥
sgen 5 = (((((gate₂ σ-gate) ↥) ↥) ↥) ↥) ↥
sgen _ = ((((((gate₂ σ-gate) ↥) ↥) ↥) ↥) ↥) ↥

-- Xab and Kq of Syntactics, as Coxeter words.
xr : ℕ → ℕ → CW
xr a zero    = [ sgen a ]ʷ
xr a (suc d) = [ sgen a ]ʷ • (xr (suc a) d • [ sgen a ]ʷ)

xw : ℕ → ℕ → CW
xw a b = go (b ∸ a)
  where
  go : ℕ → CW
  go zero    = ε
  go (suc d) = xr a d

kq kq′ : ℕ → ℕ → ℕ → ℕ → CW
kq  a b c d = xw 0 a • (xw 1 b • (xw 2 c • xw 3 d))
kq′ a b c d = xw 3 d • (xw 2 c • (xw 1 b • xw 0 a))

-- The Coxeter word of a decoded X_[a,b].
xcw : {a b : Fin 8} → .(a < b) → CW
xcw {a} {b} p = frame (a ∷ b ∷ []) (dist2 p) • ([ gate₂ σ-gate ]ʷ • inv (frame (a ∷ b ∷ []) (dist2 p)))

alias₁ : (p q : CW) → all8 (below 1 (act p) (act q)) ≡ true →
         all8 (λ x → eqᵇ (act (inv q) x) (act q x)) ≡ true → Fr m0 p ≈ Pc 0 q • m0 • Pc 0 q
alias₁ p q h₁ h₂ = trans (frame≈ 1 7 ℕP.≤-refl m0 comm-m0 p q (agree 1 (act p) (act q) h₁))
  (cong refl (cong refl (perm-complete (inv q) q (everywhere (act (inv q)) (act q) h₂))))

alias₄ : (p q q′ : CW) → all8 (below 4 (act p) (act q)) ≡ true →
         all8 (λ x → eqᵇ (act (inv q) x) (act q′ x)) ≡ true → Fr NKw p ≈ Pc 0 q • NKw • Pc 0 q′
alias₄ p q q′ h₁ h₂ = trans (frame≈ 4 4 ℕP.≤-refl NKw comm-NK p q (agree 4 (act p) (act q) h₁))
  (cong refl (cong refl (perm-complete (inv q) q′ (everywhere (act (inv q)) (act q′) h₂))))

aliasX : (p q : CW) → all8 (λ x → eqᵇ (act p x) (act q x)) ≡ true → Pc 0 p ≈ Pc 0 q
aliasX p q h = perm-complete p q (everywhere (act p) (act q) h)

-- The letters of the standard instances, and Figure 7's names for them.
data Std : Set where
  m0ˢ m1ˢ m3ˢ m4ˢ x01 x12 x13 x23 x34 x45 x04 k0123 k4567 k1345 k2345 k0124 : Std

std : Std → Gen 8
std m0ˢ   = M-gen (# 0)
std m1ˢ   = M-gen (# 1)
std m3ˢ   = M-gen (# 3)
std m4ˢ   = M-gen (# 4)
std x01   = X-gen (# 0) (# 1) (lt (# 0) (# 1))
std x12   = X-gen (# 1) (# 2) (lt (# 1) (# 2))
std x13   = X-gen (# 1) (# 3) (lt (# 1) (# 3))
std x23   = X-gen (# 2) (# 3) (lt (# 2) (# 3))
std x34   = X-gen (# 3) (# 4) (lt (# 3) (# 4))
std x45   = X-gen (# 4) (# 5) (lt (# 4) (# 5))
std x04   = X-gen (# 0) (# 4) (lt (# 0) (# 4))
std k0123 = K-gen (# 0) (# 1) (# 2) (# 3) (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
std k4567 = K-gen (# 4) (# 5) (# 6) (# 7) (lt (# 4) (# 5)) (lt (# 5) (# 6)) (lt (# 6) (# 7))
std k1345 = K-gen (# 1) (# 3) (# 4) (# 5) (lt (# 1) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5))
std k2345 = K-gen (# 2) (# 3) (# 4) (# 5) (lt (# 2) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5))
std k0124 = K-gen (# 0) (# 1) (# 2) (# 4) (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 4))

al : Std → Word G₁
al m0ˢ   = m0
al m1ˢ   = m 1
al m3ˢ   = m 3
al m4ˢ   = m 4
al x01   = T 0
al x12   = T 1
al x13   = Xab 1 3
al x23   = T 2
al x34   = T 3
al x45   = T 4
al x04   = Xab 0 4
al k0123 = NKw
al k4567 = Kq 4 5 6 7
al k1345 = Kq 1 3 4 5
al k2345 = Kq 2 3 4 5
al k0124 = Kq 0 1 2 4

al-ok : (s : Std) → dec (std s) ≈ al s
al-ok m0ˢ   = by-assoc Eq.refl
al-ok m1ˢ   = alias₁ (frame (# 1 ∷ []) ([] ∷ [])) (xw 0 1) Eq.refl Eq.refl
al-ok m3ˢ   = alias₁ (frame (# 3 ∷ []) ([] ∷ [])) (xw 0 3) Eq.refl Eq.refl
al-ok m4ˢ   = alias₁ (frame (# 4 ∷ []) ([] ∷ [])) (xw 0 4) Eq.refl Eq.refl
al-ok x01   = aliasX (xcw (lt (# 0) (# 1))) (xw 0 1) Eq.refl
al-ok x12   = aliasX (xcw (lt (# 1) (# 2))) (xw 1 2) Eq.refl
al-ok x13   = aliasX (xcw (lt (# 1) (# 3))) (xw 1 3) Eq.refl
al-ok x23   = aliasX (xcw (lt (# 2) (# 3))) (xw 2 3) Eq.refl
al-ok x34   = aliasX (xcw (lt (# 3) (# 4))) (xw 3 4) Eq.refl
al-ok x45   = aliasX (xcw (lt (# 4) (# 5))) (xw 4 5) Eq.refl
al-ok x04   = aliasX (xcw (lt (# 0) (# 4))) (xw 0 4) Eq.refl
al-ok k0123 = by-assoc Eq.refl
al-ok k4567 = trans (alias₄ (frame (# 4 ∷ # 5 ∷ # 6 ∷ # 7 ∷ []) (dist4 (lt (# 4) (# 5)) (lt (# 5) (# 6)) (lt (# 6) (# 7))))
                      (kq 4 5 6 7) (kq′ 4 5 6 7) Eq.refl Eq.refl) (by-assoc Eq.refl)
al-ok k1345 = trans (alias₄ (frame (# 1 ∷ # 3 ∷ # 4 ∷ # 5 ∷ []) (dist4 (lt (# 1) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5))))
                      (kq 1 3 4 5) (kq′ 1 3 4 5) Eq.refl Eq.refl) (by-assoc Eq.refl)
al-ok k2345 = trans (alias₄ (frame (# 2 ∷ # 3 ∷ # 4 ∷ # 5 ∷ []) (dist4 (lt (# 2) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5))))
                      (kq 2 3 4 5) (kq′ 2 3 4 5) Eq.refl Eq.refl) (by-assoc Eq.refl)
al-ok k0124 = trans (alias₄ (frame (# 0 ∷ # 1 ∷ # 2 ∷ # 4 ∷ []) (dist4 (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 4))))
                      (kq 0 1 2 4) (kq′ 0 1 2 4) Eq.refl Eq.refl) (by-assoc Eq.refl)

stdʷ : Word Std → Word (Gen 8)
stdʷ = wmap std

alʷ : Word Std → Word G₁
alʷ = al ʷ

alʷ-ok : (w : Word Std) → decʷ (stdʷ w) ≈ alʷ w
alʷ-ok [ x ]ʷ   = al-ok x
alʷ-ok ε       = refl
alʷ-ok (u • v) = cong (alʷ-ok u) (alʷ-ok v)

-- A relation between standard instances, from one between their aliases.
by-al : (l r : Word Std) → alʷ l ≈ alʷ r → decʷ (stdʷ l) ≈ decʷ (stdʷ r)
by-al l r e = trans (alʷ-ok l) (trans e (sym (alʷ-ok r)))
