------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of Li, Ross and Selinger's Table 1 at n = 8 hold for
-- their decoded circuits (axiom-decode, decode-cong).
--
-- Every generator is a circuit b conjugated by a Coxeter word (dec):
-- (-1)_[a] is m0 carried by a frame sending 0 to a, X_[a,b] is t01
-- carried by one sending 0, 1 to a, b, and K_[a,b,c,d] is NK carried
-- by one sending 0, 1, 2, 3 to a, b, c, d.  By the frame lemma
-- (Symmetric.CoxeterFrames.frame≈) the result depends only on where
-- the frame sends those states, since the T i above them commute with
-- b (Figure 7's (85)–(93), and the Coxeter relations).  So a word whose
-- letters are all carried by one frame F from a word w₀ decodes to the
-- conjugate of w₀'s decoding by F (Tr, tr-sound), and a relation of
-- Table 1 follows from one standard instance of it (transport): one
-- argument per relation family, at symbolic indices.  This replaces
-- the 2,123 finite instances, their dispatchers and the frame moves
-- that this development used to check one by one.
--
-- FrameWords' decoding conjugates by the Coxeter words of its tables
-- instead; one evaluated check per table (okM, okX, okK) says where
-- they send the states, and the frame lemma turns each decoded
-- generator into its frame (bridge).
--
-- The argument is CCX+HH-3qubit-opus's Decode, on this development's
-- rules: its Figure 7 states (101) as m0 m4 t04 ρ = ρ t04 m4 m0, so the
-- standard instance of (6a) also uses (3c), (1a), (1b) and (2d).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TwoLevel where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; if_then_else_)
import Data.Bool.Base as B
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; _<_)
open import Data.Fin using (#_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (dec-true ; dec-false)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

import Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL
open TL using (M-gen ; X-gen ; K-gen)
import Examples.Groups.Symmetric.Syntactics as Sym
open Sym using (gate₀ ; gate₁ ; gate₂ ; σ-gate ; _↥)
open import Examples.Groups.Symmetric.CoxeterFrames

open import Examples.Groups.CCX+HH-3qubit.Syntactics hiding (_≈_)
import Examples.Groups.CCX+HH-3qubit.Permutation as Perm
open Perm using (adjacent)
import Examples.Groups.CCX+HH-3qubit.Frames as Fm
open import Examples.Groups.CCX+HH-3qubit.FrameWords
  using (decode ; dM ; dX ; dK ; fM ; fX ; fK ; fK′)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP
open import Examples.Groups.CCX+HH-3qubit.States

open PB _===_ hiding (_===_)
open PP _===_ using (by-assoc)
open SR (PP.word-setoid _===_)

------------------------------------------------------------------------
-- The Coxeter relations for the circuits of the adjacent transpositions

open Circuits adjacent

cox : Coxeter _===_
cox = record
  { order = λ i _ → Perm.involution i
  ; braid = λ i h → Perm.braid {0} i (ℕP.+-monoˡ-≤ 3 h)
  ; far   = far′
  }
  where
  far′ : ∀ i j → 2 ℕ.+ i ≤ j → j ≤ 6 → adjacent i • adjacent j ≈ adjacent j • adjacent i
  far′ i j lo hi = Eq.subst (λ z → adjacent i • adjacent z ≈ adjacent z • adjacent i)
    (proj₂ (ℕP.m≤n⇒∃[o]m+o≡n lo)) (Perm.apart i (proj₁ (ℕP.m≤n⇒∃[o]m+o≡n lo)))

open Complete cox
open Coxeter cox

-- The circuits of Coxeter words in Frames are those of Pc 0.
private
  dec-tr : ∀ {n} (o : ℕ) (g : SG n) → Perm.decode o g ≡ adjacent (tr o g)
  dec-tr o (gate₀ ())
  dec-tr o (gate₁ ())
  dec-tr o (gate₂ σ-gate) = Eq.refl
  dec-tr o (g ↥)          = dec-tr (suc o) g

p≡Pc : (w : CW) → Fm.p w ≡ Pc 0 w
p≡Pc [ g ]ʷ   = dec-tr 0 g
p≡Pc ε       = Eq.refl
p≡Pc (u • v) = Eq.cong₂ _•_ (p≡Pc u) (p≡Pc v)

------------------------------------------------------------------------
-- What the T i above a base circuit commute with

-- (85)–(90): the T i with i ≥ 1 commute with (-1)_[0].
comm-m0 : Comm≥ 1 m0
comm-m0 (suc zero)                               _ _ = axiom r085
comm-m0 (suc (suc zero))                         _ _ = axiom r086
comm-m0 (suc (suc (suc zero)))                   _ _ = axiom r087
comm-m0 (suc (suc (suc (suc zero))))             _ _ = axiom r088
comm-m0 (suc (suc (suc (suc (suc zero)))))       _ _ = axiom r089
comm-m0 (suc (suc (suc (suc (suc (suc zero)))))) _ _ = axiom r090
comm-m0 (suc (suc (suc (suc (suc (suc (suc _))))))) _ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))

-- (91)–(93): the T i with i ≥ 4 commute with K_[0,1,2,3].
comm-NK : Comm≥ 4 NK
comm-NK zero                                     () _
comm-NK (suc zero)                               (s≤s ()) _
comm-NK (suc (suc zero))                         (s≤s (s≤s ())) _
comm-NK (suc (suc (suc zero)))                   (s≤s (s≤s (s≤s ()))) _
comm-NK (suc (suc (suc (suc zero))))             _ _ = axiom r091
comm-NK (suc (suc (suc (suc (suc zero)))))       _ _ = axiom r092
comm-NK (suc (suc (suc (suc (suc (suc zero)))))) _ _ = axiom r093
comm-NK (suc (suc (suc (suc (suc (suc (suc _))))))) _ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))

-- The Coxeter relations: the T i with i ≥ 2 commute with X_[0,1].
comm-T0 : Comm≥ 2 t01
comm-T0 i lo hi = sym (far 0 i lo hi)

------------------------------------------------------------------------
-- The decoding by frames

private
  <⇒≢ : {a b : Fin 8} → .(a < b) → a ≢ b
  <⇒≢ p e = ⊥-elim (FinP.<-irrefl e p)

  <-trans : {a b c : Fin 8} → a < b → b < c → a < c
  <-trans = FinP.<-trans

lt : (a b : Fin 8) → {B.T (toℕ a ℕ.<ᵇ toℕ b)} → a < b
lt a b {p} = ℕP.<ᵇ⇒< (toℕ a) (toℕ b) p

dist2 : {a b : Fin 8} → .(a < b) → Distinct (a ∷ b ∷ [])
dist2 p = (<⇒≢ p ∷ []) ∷ ([] ∷ [])

dist4 : {a b c d : Fin 8} → .(a < b) → .(b < c) → .(c < d) → Distinct (a ∷ b ∷ c ∷ d ∷ [])
dist4 p q r = (<⇒≢ p ∷ <⇒≢ (<-trans p q) ∷ <⇒≢ (<-trans (<-trans p q) r) ∷ [])
            ∷ (<⇒≢ q ∷ <⇒≢ (<-trans q r) ∷ []) ∷ (<⇒≢ r ∷ []) ∷ [] ∷ []

dec : TL.Gen 8 → Word Gen
dec (M-gen a)             = Fr m0 (frame (a ∷ []) ([] ∷ []))
dec (X-gen a b p)         = Fr t01 (frame (a ∷ b ∷ []) (dist2 p))
dec (K-gen a b c d p q r) = Fr NK (frame (a ∷ b ∷ c ∷ d ∷ []) (dist4 p q r))

decʷ : Word (TL.Gen 8) → Word Gen
decʷ = dec ʷ

------------------------------------------------------------------------
-- Conjugation by a Coxeter word

Cj : CW → Word Gen → Word Gen
Cj F w = Pc 0 F • w • Pc 0 (inv F)

Cj-ε : (F : CW) → Cj F ε ≈ ε
Cj-ε F = trans (cong refl left-unit) (Pc-inv 0 ℕP.≤-refl F)

Cj-• : (F : CW) (u v : Word Gen) → Cj F u • Cj F v ≈ Cj F (u • v)
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

Cj-cong : (F : CW) {u v : Word Gen} → u ≈ v → Cj F u ≈ Cj F v
Cj-cong F e = cong refl (cong e refl)

-- A frame conjugating a circuit by itself twice.
Fr-sq : (b : Word Gen) → b • b ≈ ε → (p : CW) → Fr b p • Fr b p ≈ ε
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
Pc-Fr : (b : Word Gen) (x p : CW) → Pc 0 x • Fr b p ≈ Fr b (x • p) • Pc 0 x
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
data Tr (F : CW) : Word (TL.Gen 8) → Word (TL.Gen 8) → Set where
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
  tr• : {u u₀ v v₀ : Word (TL.Gen 8)} → Tr F u u₀ → Tr F v v₀ → Tr F (u • v) (u₀ • v₀)

tr-sound : {F : CW} {u u₀ : Word (TL.Gen 8)} → Tr F u u₀ → decʷ u ≈ Cj F (decʷ u₀)
tr-sound {F} (trM {a} {i} e) =
  trans (frame≈ 1 7 ℕP.≤-refl m0 comm-m0 (frame (a ∷ []) ([] ∷ [])) (F • frame (i ∷ []) ([] ∷ [])) ag)
        (sym (Fr-conj m0 F (frame (i ∷ []) ([] ∷ []))))
  where
  ag : ∀ x → toℕ x ℕ.< 1 → act (frame (a ∷ []) ([] ∷ [])) x ≡ act (F • frame (i ∷ []) ([] ∷ [])) x
  ag zero _ = Eq.trans (frame-act (a ∷ []) ([] ∷ []) zero a Eq.refl)
                (Eq.sym (Eq.trans (Eq.cong (act F) (frame-act (i ∷ []) ([] ∷ []) zero i Eq.refl)) e))
  ag (suc x) (s≤s ())
tr-sound {F} (trX {a} {b} {i} {j} p q e₀ e₁) =
  trans (frame≈ 2 6 ℕP.≤-refl t01 comm-T0 (frame (a ∷ b ∷ []) (dist2 p)) (F • frame (i ∷ j ∷ []) (dist2 q)) ag)
        (sym (Fr-conj t01 F (frame (i ∷ j ∷ []) (dist2 q))))
  where
  ag : ∀ x → toℕ x ℕ.< 2 → act (frame (a ∷ b ∷ []) (dist2 p)) x ≡ act (F • frame (i ∷ j ∷ []) (dist2 q)) x
  ag zero _ = Eq.trans (frame-act (a ∷ b ∷ []) (dist2 p) zero a Eq.refl)
                (Eq.sym (Eq.trans (Eq.cong (act F) (frame-act (i ∷ j ∷ []) (dist2 q) zero i Eq.refl)) e₀))
  ag (suc zero) _ = Eq.trans (frame-act (a ∷ b ∷ []) (dist2 p) (suc zero) b Eq.refl)
                (Eq.sym (Eq.trans (Eq.cong (act F) (frame-act (i ∷ j ∷ []) (dist2 q) (suc zero) j Eq.refl)) e₁))
  ag (suc (suc x)) (s≤s (s≤s ()))
tr-sound {F} (trK {a} {b} {c} {d} {i₀} {i₁} {i₂} {i₃} p q r p′ q′ r′ e₀ e₁ e₂ e₃) =
  trans (frame≈ 4 4 ℕP.≤-refl NK comm-NK (frame ts (dist4 p q r)) (F • frame is (dist4 p′ q′ r′)) ag)
        (sym (Fr-conj NK F (frame is (dist4 p′ q′ r′))))
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
transport : (F : CW) {l r l₀ r₀ : Word (TL.Gen 8)} → Tr F l l₀ → Tr F r r₀ → decʷ l₀ ≈ decʷ r₀ → decʷ l ≈ decʷ r
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
-- Frames against words of Figure 7, decided by evaluation

-- A frame for m0 or NK, as it conjugated by Q and Q′, where Q agrees
-- with the frame below 1 or 4 and Q′ acts as the inverse of Q.
alias₁′ : (P Q Q′ : CW) → (∀ x → toℕ x ℕ.< 1 → act P x ≡ act Q x) → (∀ x → act (inv Q) x ≡ act Q′ x) →
          Fr m0 P ≈ Pc 0 Q • m0 • Pc 0 Q′
alias₁′ P Q Q′ h₁ h₂ =
  trans (frame≈ 1 7 ℕP.≤-refl m0 comm-m0 P Q h₁) (cong refl (cong refl (perm-complete (inv Q) Q′ h₂)))

alias₄′ : (P Q Q′ : CW) → (∀ x → toℕ x ℕ.< 4 → act P x ≡ act Q x) → (∀ x → act (inv Q) x ≡ act Q′ x) →
          Fr NK P ≈ Pc 0 Q • NK • Pc 0 Q′
alias₄′ P Q Q′ h₁ h₂ =
  trans (frame≈ 4 4 ℕP.≤-refl NK comm-NK P Q h₁) (cong refl (cong refl (perm-complete (inv Q) Q′ h₂)))

alias₁ : (P Q Q′ : CW) → all8 (below 1 (act P) (act Q)) ≡ true →
         all8 (λ x → eqᵇ (act (inv Q) x) (act Q′ x)) ≡ true → Fr m0 P ≈ Pc 0 Q • m0 • Pc 0 Q′
alias₁ P Q Q′ h₁ h₂ = alias₁′ P Q Q′ (agree 1 (act P) (act Q) h₁) (everywhere (act (inv Q)) (act Q′) h₂)

alias₄ : (P Q Q′ : CW) → all8 (below 4 (act P) (act Q)) ≡ true →
         all8 (λ x → eqᵇ (act (inv Q) x) (act Q′ x)) ≡ true → Fr NK P ≈ Pc 0 Q • NK • Pc 0 Q′
alias₄ P Q Q′ h₁ h₂ = alias₄′ P Q Q′ (agree 4 (act P) (act Q) h₁) (everywhere (act (inv Q)) (act Q′) h₂)

aliasX : (P Q : CW) → all8 (λ x → eqᵇ (act P x) (act Q x)) ≡ true → Pc 0 P ≈ Pc 0 Q
aliasX P Q h = perm-complete P Q (everywhere (act P) (act Q) h)

-- The Coxeter word of a decoded X_[a,b].
xcw : (a b : Fin 8) → .(a < b) → CW
xcw a b p = frame (a ∷ b ∷ []) (dist2 p) • ([ gate₂ σ-gate ]ʷ • inv (frame (a ∷ b ∷ []) (dist2 p)))

-- X0 as a Coxeter word (GatePermutations).
X0w : CW
X0w = Fm.s3 • Fm.s2 • Fm.s1 • Fm.s0 • Fm.s4 • Fm.s3 • Fm.s2 • Fm.s1 • Fm.s5 • Fm.s4 • Fm.s3 • Fm.s2 • Fm.s6 • Fm.s5 • Fm.s4 • Fm.s3

X0≈ : Pc 0 X0w ≈ X0
X0≈ = sym (trans GP.gateX0 (refl' (p≡Pc X0w)))

-- The letters of the standard instances, and Figure 7's names for them.
data Std : Set where
  m0ˢ m1ˢ m3ˢ m4ˢ x01 x12 x13 x23 x34 x45 x56 x67 x04 k0123 k4567ˢ k1345ˢ k2345ˢ k0124ˢ : Std

std : Std → TL.Gen 8
std m0ˢ    = M-gen (# 0)
std m1ˢ    = M-gen (# 1)
std m3ˢ    = M-gen (# 3)
std m4ˢ    = M-gen (# 4)
std x01    = X-gen (# 0) (# 1) (lt (# 0) (# 1))
std x12    = X-gen (# 1) (# 2) (lt (# 1) (# 2))
std x13    = X-gen (# 1) (# 3) (lt (# 1) (# 3))
std x23    = X-gen (# 2) (# 3) (lt (# 2) (# 3))
std x34    = X-gen (# 3) (# 4) (lt (# 3) (# 4))
std x45    = X-gen (# 4) (# 5) (lt (# 4) (# 5))
std x56    = X-gen (# 5) (# 6) (lt (# 5) (# 6))
std x67    = X-gen (# 6) (# 7) (lt (# 6) (# 7))
std x04    = X-gen (# 0) (# 4) (lt (# 0) (# 4))
std k0123  = K-gen (# 0) (# 1) (# 2) (# 3) (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
std k4567ˢ = K-gen (# 4) (# 5) (# 6) (# 7) (lt (# 4) (# 5)) (lt (# 5) (# 6)) (lt (# 6) (# 7))
std k1345ˢ = K-gen (# 1) (# 3) (# 4) (# 5) (lt (# 1) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5))
std k2345ˢ = K-gen (# 2) (# 3) (# 4) (# 5) (lt (# 2) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5))
std k0124ˢ = K-gen (# 0) (# 1) (# 2) (# 4) (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 4))

al : Std → Word Gen
al m0ˢ    = m0
al m1ˢ    = m1
al m3ˢ    = m3
al m4ˢ    = m4
al x01    = t01
al x12    = t12
al x13    = t13
al x23    = t23
al x34    = t34
al x45    = t45
al x56    = t56
al x67    = t67
al x04    = t04
al k0123  = NK
al k4567ˢ = k4567
al k1345ˢ = k1345
al k2345ˢ = k2345
al k0124ˢ = k0124

private
  fr1 : Fin 8 → CW
  fr1 a = frame (a ∷ []) ([] ∷ [])

  fr4 : (a b c d : Fin 8) → .(a < b) → .(b < c) → .(c < d) → CW
  fr4 a b c d p q r = frame (a ∷ b ∷ c ∷ d ∷ []) (dist4 p q r)

  open Fm using (s0 ; s1 ; s2 ; s3 ; s4)

al-ok : (s : Std) → dec (std s) ≈ al s
al-ok m0ˢ    = by-assoc Eq.refl
al-ok m1ˢ    = alias₁ (fr1 (# 1)) s0 s0 Eq.refl Eq.refl
al-ok m3ˢ    = trans (alias₁ (fr1 (# 3)) (s2 • s1 • s0) (s0 • s1 • s2) Eq.refl Eq.refl) (by-assoc Eq.refl)
al-ok m4ˢ    = trans (alias₁ (fr1 (# 4)) X0w X0w Eq.refl Eq.refl) (cong X0≈ (cong refl X0≈))
al-ok x01    = aliasX (xcw (# 0) (# 1) (lt (# 0) (# 1))) s0 Eq.refl
al-ok x12    = aliasX (xcw (# 1) (# 2) (lt (# 1) (# 2))) s1 Eq.refl
al-ok x13    = aliasX (xcw (# 1) (# 3) (lt (# 1) (# 3))) (s1 • s2 • s1) Eq.refl
al-ok x23    = aliasX (xcw (# 2) (# 3) (lt (# 2) (# 3))) s2 Eq.refl
al-ok x34    = aliasX (xcw (# 3) (# 4) (lt (# 3) (# 4))) s3 Eq.refl
al-ok x45    = aliasX (xcw (# 4) (# 5) (lt (# 4) (# 5))) s4 Eq.refl
al-ok x56    = aliasX (xcw (# 5) (# 6) (lt (# 5) (# 6))) Fm.s5 Eq.refl
al-ok x67    = aliasX (xcw (# 6) (# 7) (lt (# 6) (# 7))) Fm.s6 Eq.refl
al-ok x04    = aliasX (xcw (# 0) (# 4) (lt (# 0) (# 4))) (s0 • s1 • s2 • s3 • s2 • s1 • s0) Eq.refl
al-ok k0123  = by-assoc Eq.refl
al-ok k4567ˢ = trans (alias₄ (fr4 (# 4) (# 5) (# 6) (# 7) (lt (# 4) (# 5)) (lt (# 5) (# 6)) (lt (# 6) (# 7)))
                        X0w X0w Eq.refl Eq.refl) (cong X0≈ (cong refl X0≈))
al-ok k1345ˢ = trans (alias₄ (fr4 (# 1) (# 3) (# 4) (# 5) (lt (# 1) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5)))
                        (s0 • (s1 • s2 • s1) • (s2 • s3 • s2) • (s3 • s4 • s3))
                        ((s3 • s4 • s3) • (s2 • s3 • s2) • (s1 • s2 • s1) • s0) Eq.refl Eq.refl) (by-assoc Eq.refl)
al-ok k2345ˢ = trans (alias₄ (fr4 (# 2) (# 3) (# 4) (# 5) (lt (# 2) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5)))
                        ((s0 • s1 • s0) • (s1 • s2 • s1) • (s2 • s3 • s2) • (s3 • s4 • s3))
                        ((s3 • s4 • s3) • (s2 • s3 • s2) • (s1 • s2 • s1) • (s0 • s1 • s0)) Eq.refl Eq.refl) (by-assoc Eq.refl)
al-ok k0124ˢ = alias₄ (fr4 (# 0) (# 1) (# 2) (# 4) (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 4))) s3 s3 Eq.refl Eq.refl

stdʷ : Word Std → Word (TL.Gen 8)
stdʷ = wmap std

alʷ : Word Std → Word Gen
alʷ = al ʷ

alʷ-ok : (w : Word Std) → decʷ (stdʷ w) ≈ alʷ w
alʷ-ok [ x ]ʷ   = al-ok x
alʷ-ok ε       = refl
alʷ-ok (u • v) = cong (alʷ-ok u) (alʷ-ok v)

-- A relation between standard instances, from one between their aliases.
by-al : (l r : Word Std) → alʷ l ≈ alʷ r → decʷ (stdʷ l) ≈ decʷ (stdʷ r)
by-al l r e = trans (alʷ-ok l) (trans e (sym (alʷ-ok r)))

------------------------------------------------------------------------
-- Word algebra for the standard instance of (6a)

private
  -- X B A = A B X when X conjugates B to A and A to B.
  swap3 : {A B X : Word Gen} → X • B ≈ A • X → X • A ≈ B • X → X • (B • A) ≈ (A • B) • X
  swap3 {A} {B} {X} xb xa = begin
    X • (B • A)   ≈⟨ sym assoc ⟩
    (X • B) • A   ≈⟨ cong xb refl ⟩
    (A • X) • A   ≈⟨ assoc ⟩
    A • (X • A)   ≈⟨ cong refl xa ⟩
    A • (B • X)   ≈⟨ sym assoc ⟩
    (A • B) • X   ∎

  -- X A = B X from X B = A X, X being an involution.
  xflip : {A B X : Word Gen} → X • X ≈ ε → X • B ≈ A • X → X • A ≈ B • X
  xflip {A} {B} {X} xx xb = begin
    X • A                   ≈⟨ sym right-unit ⟩
    (X • A) • ε             ≈⟨ cong refl (sym xx) ⟩
    (X • A) • (X • X)       ≈⟨ assoc ⟩
    X • (A • (X • X))       ≈⟨ cong refl (sym assoc) ⟩
    X • ((A • X) • X)       ≈⟨ cong refl (cong (sym xb) refl) ⟩
    X • ((X • B) • X)       ≈⟨ cong refl assoc ⟩
    X • (X • (B • X))       ≈⟨ sym assoc ⟩
    (X • X) • (B • X)       ≈⟨ cong xx refl ⟩
    ε • (B • X)             ≈⟨ left-unit ⟩
    B • X                   ∎

  -- X B A X A B = ε.
  tail6 : {A B X : Word Gen} → X • X ≈ ε → A • A ≈ ε → B • B ≈ ε → A • B ≈ B • A → X • B ≈ A • X →
          X • (B • (A • (X • (A • B)))) ≈ ε
  tail6 {A} {B} {X} xx aa bb ab xb = begin
    X • (B • (A • (X • (A • B))))         ≈⟨ cong refl (sym assoc) ⟩
    X • ((B • A) • (X • (A • B)))         ≈⟨ sym assoc ⟩
    (X • (B • A)) • (X • (A • B))         ≈⟨ cong (swap3 xb (xflip xx xb)) refl ⟩
    ((A • B) • X) • (X • (A • B))         ≈⟨ assoc ⟩
    (A • B) • (X • (X • (A • B)))         ≈⟨ cong refl (trans (sym assoc) (trans (cong xx refl) left-unit)) ⟩
    (A • B) • (A • B)                     ≈⟨ cong refl ab ⟩
    (A • B) • (B • A)                     ≈⟨ assoc ⟩
    A • (B • (B • A))                     ≈⟨ cong refl (trans (sym assoc) (trans (cong bb refl) left-unit)) ⟩
    A • A                                 ≈⟨ aa ⟩
    ε                                     ∎

  -- Eight letters followed by u.
  glue8 : {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ u : Word Gen} →
          (a₁ • a₂ • a₃ • a₄ • a₅ • a₆ • a₇ • a₈) • u ≈ a₁ • a₂ • a₃ • a₄ • a₅ • a₆ • a₇ • a₈ • u
  glue8 = trans assoc (cong refl (trans assoc (cong refl (trans assoc (cong refl (trans assoc (cong refl
            (trans assoc (cong refl (trans assoc (cong refl assoc)))))))))))

  six : {A B X K₁ K₂ Y : Word Gen} →
        A • B • X • K₂ • K₁ • Y • K₁ • K₂ ≈ K₂ • K₁ • Y • K₁ • K₂ • X • B • A →
        X • X ≈ ε → A • A ≈ ε → B • B ≈ ε → A • B ≈ B • A → X • B ≈ A • X →
        A • B • X • K₂ • K₁ • Y • K₁ • K₂ • X • A • B ≈ K₂ • K₁ • Y • K₁ • K₂
  six {A} {B} {X} {K₁} {K₂} {Y} e xx aa bb ab xb = begin
    A • B • X • K₂ • K₁ • Y • K₁ • K₂ • X • A • B
      ≈⟨ sym glue8 ⟩
    (A • B • X • K₂ • K₁ • Y • K₁ • K₂) • (X • A • B)
      ≈⟨ cong e refl ⟩
    (K₂ • K₁ • Y • K₁ • K₂ • X • B • A) • (X • A • B)
      ≈⟨ glue8 ⟩
    K₂ • K₁ • Y • K₁ • K₂ • X • B • A • X • A • B
      ≈⟨ cong refl (cong refl (cong refl (cong refl (trans (cong refl (tail6 xx aa bb ab xb)) right-unit)))) ⟩
    K₂ • K₁ • Y • K₁ • K₂   ∎

------------------------------------------------------------------------
-- The relations of Table 1

private
  ⟨_⟩ : Std → Word Std
  ⟨ s ⟩ = [ s ]ʷ

  at : (ts : List (Fin 8)) (D : Distinct ts) (k : Fin 8) {x : Fin 8} → ts ‼ toℕ k ≡ just x →
       act (frame ts D) k ≡ x
  at ts D k = frame-act ts D k _

  ≢-sym : {a b : Fin 8} → a ≢ b → b ≢ a
  ≢-sym ne e = ne (Eq.sym e)

  le : (m n : ℕ) → {B.T (m ℕ.≤ᵇ n)} → m ≤ n
  le m n {h} = ℕP.≤ᵇ⇒≤ m n h

  -- An X_[i,j] conjugating a K frame.
  xk-base : (x F₁ F₂ : CW) → all8 (below 4 (act (x • F₁)) (act F₂)) ≡ true →
            Pc 0 x • Fr NK F₁ ≈ Fr NK F₂ • Pc 0 x
  xk-base x F₁ F₂ h = trans (Pc-Fr NK x F₁)
    (cong (frame≈ 4 4 ℕP.≤-refl NK comm-NK (x • F₁) F₂ (agree 4 (act (x • F₁)) (act F₂) h)) refl)

  dist5 : {a b c d e : Fin 8} → .(a < b) → .(b < c) → .(c < d) → .(d < e) → Distinct (a ∷ b ∷ c ∷ d ∷ e ∷ [])
  dist5 p q r s = chain (p <∷ q <∷ r <∷ s <∷ one)

  -- The standard instance of (2d), from (95).
  base2d : decʷ (stdʷ (⟨ m0ˢ ⟩ • ⟨ m1ˢ ⟩)) ≈ decʷ (stdʷ (⟨ m1ˢ ⟩ • ⟨ m0ˢ ⟩))
  base2d = transport G (tr• (trM {i = # 0} (g (# 0) Eq.refl)) (trM {i = # 4} (g (# 4) Eq.refl)))
                       (tr• (trM {i = # 4} (g (# 4) Eq.refl)) (trM {i = # 0} (g (# 0) Eq.refl)))
                       (by-al (⟨ m0ˢ ⟩ • ⟨ m4ˢ ⟩) (⟨ m4ˢ ⟩ • ⟨ m0ˢ ⟩) (axiom r095))
    where
    gs = # 0 ∷ # 2 ∷ # 3 ∷ # 5 ∷ # 1 ∷ []
    Dg = distinct gs Eq.refl
    G = frame gs Dg
    g = at gs Dg

-- (1a), (1b), (2d) and (3c), on their own: the standard instance of
-- (6a) uses them.
dec-1a : {a b : Fin 8} .(p : a < b) → decʷ (TL.X a b p • TL.X a b p) ≈ decʷ ε
dec-1a {a} {b} p = Fr-sq t01 (order 0 z≤n) (frame (a ∷ b ∷ []) (dist2 p))

dec-1b : {a : Fin 8} → decʷ (TL.M a • TL.M a) ≈ decʷ ε
dec-1b {a} = Fr-sq m0 (axiom r083) (frame (a ∷ []) ([] ∷ []))

dec-2d : {a b : Fin 8} → a ≢ b → decʷ (TL.M a • TL.M b) ≈ decʷ (TL.M b • TL.M a)
dec-2d {a} {b} ab =
  transport (frame ts D) (tr• (trM {i = # 0} (f (# 0) Eq.refl)) (trM {i = # 1} (f (# 1) Eq.refl)))
                         (tr• (trM {i = # 1} (f (# 1) Eq.refl)) (trM {i = # 0} (f (# 0) Eq.refl))) base2d
  where
  ts = a ∷ b ∷ []
  D = (ab ∷ []) ∷ [] ∷ []
  f = at ts D

dec-3c : {a b : Fin 8} .(p : a < b) → decʷ (TL.X a b p • TL.M b) ≈ decʷ (TL.M a • TL.X a b p)
dec-3c {a} {b} p =
  transport (frame ts D) (tr• (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl)) (trM {i = # 1} (f (# 1) Eq.refl)))
                         (tr• (trM {i = # 0} (f (# 0) Eq.refl)) (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl)))
    (by-al (⟨ x01 ⟩ • ⟨ m1ˢ ⟩) (⟨ m0ˢ ⟩ • ⟨ x01 ⟩)
      (trans (sym assoc) (trans (cong (order 0 z≤n) refl) left-unit)))
  where
  ts = a ∷ b ∷ []
  D = dist2 p
  f = at ts D

private
  -- The standard instance of (6a), from (101), with (3c), (1a), (1b) and (2d).
  base6a : decʷ (stdʷ (⟨ m0ˢ ⟩ • ⟨ m4ˢ ⟩ • ⟨ x04 ⟩ • ⟨ k4567ˢ ⟩ • ⟨ k0123 ⟩ • ⟨ x34 ⟩ • ⟨ k0123 ⟩ • ⟨ k4567ˢ ⟩ •
                   ⟨ x04 ⟩ • ⟨ m0ˢ ⟩ • ⟨ m4ˢ ⟩))
         ≈ decʷ (stdʷ (⟨ k4567ˢ ⟩ • ⟨ k0123 ⟩ • ⟨ x34 ⟩ • ⟨ k0123 ⟩ • ⟨ k4567ˢ ⟩))
  base6a = six
    (by-al (⟨ m0ˢ ⟩ • ⟨ m4ˢ ⟩ • ⟨ x04 ⟩ • ⟨ k4567ˢ ⟩ • ⟨ k0123 ⟩ • ⟨ x34 ⟩ • ⟨ k0123 ⟩ • ⟨ k4567ˢ ⟩)
           (⟨ k4567ˢ ⟩ • ⟨ k0123 ⟩ • ⟨ x34 ⟩ • ⟨ k0123 ⟩ • ⟨ k4567ˢ ⟩ • ⟨ x04 ⟩ • ⟨ m4ˢ ⟩ • ⟨ m0ˢ ⟩)
           (trans (axiom r101) (by-assoc Eq.refl)))
    (dec-1a {# 0} {# 4} (lt (# 0) (# 4))) (dec-1b {# 0}) (dec-1b {# 4}) (dec-2d {# 0} {# 4} (λ ()))
    (dec-3c {# 0} {# 4} (lt (# 0) (# 4)))

-- Each Tr letter is given its standard states ({i = # 0}, …): left to
-- unification they are solved from `act (frame ts D) i`, and Agda
-- reduces the frame of the symbolic states ts to compare.
dec-ax : {u v : Word (TL.Gen 8)} → u TL.=== v → decʷ u ≈ decʷ v
-- (1a)–(1c)
dec-ax (TL.r1a {a = a} {b = b} p) = dec-1a {a} {b} p
dec-ax (TL.r1b {a = a}) = dec-1b {a}
dec-ax (TL.r1c {a = a} {b = b} {c = c} {d = d} p q r) = Fr-sq NK (axiom r084) (frame (a ∷ b ∷ c ∷ d ∷ []) (dist4 p q r))
-- (2a)
dec-ax (TL.r2a {a = a} {b = b} {c = c} {d = d} p q ac ad bc bd) =
  transport (frame ts D) (tr• (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl))
                              (trX {i = # 2} {j = # 3} q (lt (# 2) (# 3)) (f (# 2) Eq.refl) (f (# 3) Eq.refl)))
                         (tr• (trX {i = # 2} {j = # 3} q (lt (# 2) (# 3)) (f (# 2) Eq.refl) (f (# 3) Eq.refl))
                              (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl)))
    (by-al (⟨ x01 ⟩ • ⟨ x23 ⟩) (⟨ x23 ⟩ • ⟨ x01 ⟩) (far 0 2 (le 2 2) (le 2 6)))
  where
  ts = a ∷ b ∷ c ∷ d ∷ []
  D = (<⇒≢ p ∷ ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ (<⇒≢ q ∷ []) ∷ [] ∷ []
  f = at ts D
-- (2b)
dec-ax (TL.r2b {a = a} {b = b} {c = c} p ca cb) =
  transport (frame ts D) (tr• (trX {i = # 1} {j = # 2} p (lt (# 1) (# 2)) (f (# 1) Eq.refl) (f (# 2) Eq.refl)) (trM {i = # 0} (f (# 0) Eq.refl)))
                         (tr• (trM {i = # 0} (f (# 0) Eq.refl)) (trX {i = # 1} {j = # 2} p (lt (# 1) (# 2)) (f (# 1) Eq.refl) (f (# 2) Eq.refl)))
    (by-al (⟨ x12 ⟩ • ⟨ m0ˢ ⟩) (⟨ m0ˢ ⟩ • ⟨ x12 ⟩) (axiom r085))
  where
  ts = c ∷ a ∷ b ∷ []
  D = (ca ∷ cb ∷ []) ∷ (<⇒≢ p ∷ []) ∷ [] ∷ []
  f = at ts D
-- (2c)
dec-ax (TL.r2c {a = a} {b = b} {c = c} {d = d} {e = e} {f = f′} p q r s ac ad ae af bc bd be bf) =
  transport (frame ts D) (tr• (trX {i = # 4} {j = # 5} p (lt (# 4) (# 5)) (f (# 4) Eq.refl) (f (# 5) Eq.refl)) K)
                         (tr• K (trX {i = # 4} {j = # 5} p (lt (# 4) (# 5)) (f (# 4) Eq.refl) (f (# 5) Eq.refl)))
    (by-al (⟨ x45 ⟩ • ⟨ k0123 ⟩) (⟨ k0123 ⟩ • ⟨ x45 ⟩) (axiom r091))
  where
  ts = c ∷ d ∷ e ∷ f′ ∷ a ∷ b ∷ []
  D = (<⇒≢ q ∷ <⇒≢ (<-trans q r) ∷ <⇒≢ (<-trans (<-trans q r) s) ∷ ≢-sym ac ∷ ≢-sym bc ∷ [])
    ∷ (<⇒≢ r ∷ <⇒≢ (<-trans r s) ∷ ≢-sym ad ∷ ≢-sym bd ∷ [])
    ∷ (<⇒≢ s ∷ ≢-sym ae ∷ ≢-sym be ∷ []) ∷ (≢-sym af ∷ ≢-sym bf ∷ []) ∷ (<⇒≢ p ∷ []) ∷ [] ∷ []
  f = at ts D
  K = trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 3} q r s (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
          (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl)
-- (2d)
dec-ax (TL.r2d {a = a} {b = b} ab) = dec-2d {a} {b} ab
-- (2e)
dec-ax (TL.r2e {b = b} {c = c} {d = d} {e = e} {a = a} p q r ab ac ad ae) =
  transport (frame ts D) (tr• (trM {i = # 4} (f (# 4) Eq.refl)) K) (tr• K (trM {i = # 4} (f (# 4) Eq.refl)))
    (by-al (⟨ m4ˢ ⟩ • ⟨ k0123 ⟩) (⟨ k0123 ⟩ • ⟨ m4ˢ ⟩) (axiom r094))
  where
  ts = b ∷ c ∷ d ∷ e ∷ a ∷ []
  D = (<⇒≢ p ∷ <⇒≢ (<-trans p q) ∷ <⇒≢ (<-trans (<-trans p q) r) ∷ ≢-sym ab ∷ [])
    ∷ (<⇒≢ q ∷ <⇒≢ (<-trans q r) ∷ ≢-sym ac ∷ []) ∷ (<⇒≢ r ∷ ≢-sym ad ∷ []) ∷ (≢-sym ae ∷ []) ∷ [] ∷ []
  f = at ts D
  K = trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 3} p q r (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
          (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl)
-- (2f)
dec-ax (TL.r2f {a = a} {b = b} {c = c} {d = d} {e = e} {f = f′} {g = g} {h = h} p q r s t u
               ae af ag ah be bf bg bh ce cf cg ch de df dg dh) =
  transport (frame ts D) (tr• K₁ K₂) (tr• K₂ K₁)
    (by-al (⟨ k0123 ⟩ • ⟨ k4567ˢ ⟩) (⟨ k4567ˢ ⟩ • ⟨ k0123 ⟩) (axiom r096))
  where
  ts = a ∷ b ∷ c ∷ d ∷ e ∷ f′ ∷ g ∷ h ∷ []
  D = (<⇒≢ p ∷ <⇒≢ (<-trans p q) ∷ <⇒≢ (<-trans (<-trans p q) r) ∷ ae ∷ af ∷ ag ∷ ah ∷ [])
    ∷ (<⇒≢ q ∷ <⇒≢ (<-trans q r) ∷ be ∷ bf ∷ bg ∷ bh ∷ [])
    ∷ (<⇒≢ r ∷ ce ∷ cf ∷ cg ∷ ch ∷ []) ∷ (de ∷ df ∷ dg ∷ dh ∷ [])
    ∷ (<⇒≢ s ∷ <⇒≢ (<-trans s t) ∷ <⇒≢ (<-trans (<-trans s t) u) ∷ [])
    ∷ (<⇒≢ t ∷ <⇒≢ (<-trans t u) ∷ []) ∷ (<⇒≢ u ∷ []) ∷ [] ∷ []
  fr = at ts D
  K₁ = trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 3} p q r (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
           (fr (# 0) Eq.refl) (fr (# 1) Eq.refl) (fr (# 2) Eq.refl) (fr (# 3) Eq.refl)
  K₂ = trK {i₀ = # 4} {i₁ = # 5} {i₂ = # 6} {i₃ = # 7} s t u (lt (# 4) (# 5)) (lt (# 5) (# 6)) (lt (# 6) (# 7))
           (fr (# 4) Eq.refl) (fr (# 5) Eq.refl) (fr (# 6) Eq.refl) (fr (# 7) Eq.refl)
-- (3a), (3b): permutations only.
dec-ax (TL.r3a {a = a} {a′ = a′} {b = b} p q r) =
  transport (frame ts D) (tr• (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl))
                              (trX {i = # 0} {j = # 2} r (lt (# 0) (# 2)) (f (# 0) Eq.refl) (f (# 2) Eq.refl)))
                         (tr• (trX {i = # 1} {j = # 2} q (lt (# 1) (# 2)) (f (# 1) Eq.refl) (f (# 2) Eq.refl))
                              (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl)))
    (aliasX (xcw (# 0) (# 1) (lt (# 0) (# 1)) • xcw (# 0) (# 2) (lt (# 0) (# 2))) (xcw (# 1) (# 2) (lt (# 1) (# 2)) • xcw (# 0) (# 1) (lt (# 0) (# 1))) Eq.refl)
  where
  ts = a ∷ a′ ∷ b ∷ []
  D = chain (p <∷ q <∷ one)
  f = at ts D
dec-ax (TL.r3b {a = a} {b = b} {b′ = b′} p q r) =
  transport (frame ts D) (tr• (trX {i = # 1} {j = # 2} q (lt (# 1) (# 2)) (f (# 1) Eq.refl) (f (# 2) Eq.refl))
                              (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl)))
                         (tr• (trX {i = # 0} {j = # 2} r (lt (# 0) (# 2)) (f (# 0) Eq.refl) (f (# 2) Eq.refl))
                              (trX {i = # 1} {j = # 2} q (lt (# 1) (# 2)) (f (# 1) Eq.refl) (f (# 2) Eq.refl)))
    (aliasX (xcw (# 1) (# 2) (lt (# 1) (# 2)) • xcw (# 0) (# 1) (lt (# 0) (# 1))) (xcw (# 0) (# 2) (lt (# 0) (# 2)) • xcw (# 1) (# 2) (lt (# 1) (# 2))) Eq.refl)
  where
  ts = a ∷ b ∷ b′ ∷ []
  D = chain (p <∷ q <∷ one)
  f = at ts D
-- (3c)
dec-ax (TL.r3c {a = a} {b = b} p) = dec-3c {a} {b} p
-- (3d)–(3g): an X renaming one index of a K.
dec-ax (TL.r3d {a = a} {a′ = a′} {b = b} {c = c} {d = d} p q r s t) =
  transport (frame ts D)
    (tr• (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl))
         (trK {i₀ = # 0} {i₁ = # 2} {i₂ = # 3} {i₃ = # 4} t r s (lt (# 0) (# 2)) (lt (# 2) (# 3)) (lt (# 3) (# 4))
              (f (# 0) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl) (f (# 4) Eq.refl)))
    (tr• (trK {i₀ = # 1} {i₁ = # 2} {i₂ = # 3} {i₃ = # 4} q r s (lt (# 1) (# 2)) (lt (# 2) (# 3)) (lt (# 3) (# 4))
              (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl) (f (# 4) Eq.refl))
         (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl)))
    (xk-base (xcw (# 0) (# 1) (lt (# 0) (# 1)))
      (frame (# 0 ∷ # 2 ∷ # 3 ∷ # 4 ∷ []) (dist4 (lt (# 0) (# 2)) (lt (# 2) (# 3)) (lt (# 3) (# 4))))
      (frame (# 1 ∷ # 2 ∷ # 3 ∷ # 4 ∷ []) (dist4 (lt (# 1) (# 2)) (lt (# 2) (# 3)) (lt (# 3) (# 4)))) Eq.refl)
  where
  ts = a ∷ a′ ∷ b ∷ c ∷ d ∷ []
  D = dist5 p q r s
  f = at ts D
dec-ax (TL.r3e {a = a} {b = b} {b′ = b′} {c = c} {d = d} p q r s t u) =
  transport (frame ts D)
    (tr• (trX {i = # 1} {j = # 2} q (lt (# 1) (# 2)) (f (# 1) Eq.refl) (f (# 2) Eq.refl))
         (trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 3} {i₃ = # 4} p t s (lt (# 0) (# 1)) (lt (# 1) (# 3)) (lt (# 3) (# 4))
              (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 3) Eq.refl) (f (# 4) Eq.refl)))
    (tr• (trK {i₀ = # 0} {i₁ = # 2} {i₂ = # 3} {i₃ = # 4} u r s (lt (# 0) (# 2)) (lt (# 2) (# 3)) (lt (# 3) (# 4))
              (f (# 0) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl) (f (# 4) Eq.refl))
         (trX {i = # 1} {j = # 2} q (lt (# 1) (# 2)) (f (# 1) Eq.refl) (f (# 2) Eq.refl)))
    (xk-base (xcw (# 1) (# 2) (lt (# 1) (# 2)))
      (frame (# 0 ∷ # 1 ∷ # 3 ∷ # 4 ∷ []) (dist4 (lt (# 0) (# 1)) (lt (# 1) (# 3)) (lt (# 3) (# 4))))
      (frame (# 0 ∷ # 2 ∷ # 3 ∷ # 4 ∷ []) (dist4 (lt (# 0) (# 2)) (lt (# 2) (# 3)) (lt (# 3) (# 4)))) Eq.refl)
  where
  ts = a ∷ b ∷ b′ ∷ c ∷ d ∷ []
  D = dist5 p q r s
  f = at ts D
dec-ax (TL.r3f {a = a} {b = b} {c = c} {c′ = c′} {d = d} p q r s t u) =
  transport (frame ts D)
    (tr• (trX {i = # 2} {j = # 3} r (lt (# 2) (# 3)) (f (# 2) Eq.refl) (f (# 3) Eq.refl))
         (trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 4} p q t (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 4))
              (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 4) Eq.refl)))
    (tr• (trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 3} {i₃ = # 4} p u s (lt (# 0) (# 1)) (lt (# 1) (# 3)) (lt (# 3) (# 4))
              (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 3) Eq.refl) (f (# 4) Eq.refl))
         (trX {i = # 2} {j = # 3} r (lt (# 2) (# 3)) (f (# 2) Eq.refl) (f (# 3) Eq.refl)))
    (xk-base (xcw (# 2) (# 3) (lt (# 2) (# 3)))
      (frame (# 0 ∷ # 1 ∷ # 2 ∷ # 4 ∷ []) (dist4 (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 4))))
      (frame (# 0 ∷ # 1 ∷ # 3 ∷ # 4 ∷ []) (dist4 (lt (# 0) (# 1)) (lt (# 1) (# 3)) (lt (# 3) (# 4)))) Eq.refl)
  where
  ts = a ∷ b ∷ c ∷ c′ ∷ d ∷ []
  D = dist5 p q r s
  f = at ts D
dec-ax (TL.r3g {a = a} {b = b} {c = c} {d = d} {d′ = d′} p q r s t) =
  transport (frame ts D)
    (tr• (trX {i = # 3} {j = # 4} s (lt (# 3) (# 4)) (f (# 3) Eq.refl) (f (# 4) Eq.refl))
         (trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 3} p q r (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
              (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl)))
    (tr• (trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 4} p q t (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 4))
              (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 4) Eq.refl))
         (trX {i = # 3} {j = # 4} s (lt (# 3) (# 4)) (f (# 3) Eq.refl) (f (# 4) Eq.refl)))
    (xk-base (xcw (# 3) (# 4) (lt (# 3) (# 4)))
      (frame (# 0 ∷ # 1 ∷ # 2 ∷ # 3 ∷ []) (dist4 (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))))
      (frame (# 0 ∷ # 1 ∷ # 2 ∷ # 4 ∷ []) (dist4 (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 4)))) Eq.refl)
  where
  ts = a ∷ b ∷ c ∷ d ∷ d′ ∷ []
  D = dist5 p q r s
  f = at ts D
-- (4a)–(4c): (97)–(99) of Figure 7.
dec-ax (TL.r4a {a = a} {b = b} {c = c} {d = d} p q r s) =
  transport (frame ts D) (tr• (trX {i = # 0} {j = # 1} p (lt (# 0) (# 1)) (f (# 0) Eq.refl) (f (# 1) Eq.refl)) K)
    (tr• K (tr• (trX {i = # 1} {j = # 3} s (lt (# 1) (# 3)) (f (# 1) Eq.refl) (f (# 3) Eq.refl))
           (tr• (trM {i = # 1} (f (# 1) Eq.refl)) (trM {i = # 3} (f (# 3) Eq.refl)))))
    (by-al (⟨ x01 ⟩ • ⟨ k0123 ⟩) (⟨ k0123 ⟩ • ⟨ x13 ⟩ • ⟨ m1ˢ ⟩ • ⟨ m3ˢ ⟩) (axiom r097))
  where
  ts = a ∷ b ∷ c ∷ d ∷ []
  D = dist4 p q r
  f = at ts D
  K = trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 3} p q r (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
          (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl)
dec-ax (TL.r4b {a = a} {b = b} {c = c} {d = d} p q r) =
  transport (frame ts D) (tr• (trX {i = # 1} {j = # 2} q (lt (# 1) (# 2)) (f (# 1) Eq.refl) (f (# 2) Eq.refl)) K)
    (tr• M₀ (tr• K (tr• M₀ (tr• K M₀))))
    (by-al (⟨ x12 ⟩ • ⟨ k0123 ⟩) (⟨ m0ˢ ⟩ • ⟨ k0123 ⟩ • ⟨ m0ˢ ⟩ • ⟨ k0123 ⟩ • ⟨ m0ˢ ⟩) (axiom r098))
  where
  ts = a ∷ b ∷ c ∷ d ∷ []
  D = dist4 p q r
  f = at ts D
  K = trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 3} p q r (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
          (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl)
  M₀ = trM {i = # 0} (f (# 0) Eq.refl)
dec-ax (TL.r4c {a = a} {b = b} {c = c} {d = d} p q r s) =
  transport (frame ts D) (tr• (trX {i = # 2} {j = # 3} r (lt (# 2) (# 3)) (f (# 2) Eq.refl) (f (# 3) Eq.refl)) K)
    (tr• K (trX {i = # 1} {j = # 3} s (lt (# 1) (# 3)) (f (# 1) Eq.refl) (f (# 3) Eq.refl)))
    (by-al (⟨ x23 ⟩ • ⟨ k0123 ⟩) (⟨ k0123 ⟩ • ⟨ x13 ⟩) (axiom r099))
  where
  ts = a ∷ b ∷ c ∷ d ∷ []
  D = dist4 p q r
  f = at ts D
  K = trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 3} p q r (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
          (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl)
-- (5a): (100) of Figure 7.
dec-ax (TL.r5a {a = a} {b = b} {c = c} {d = d} {e = e} {f = f′} p q r s t u v) =
  transport (frame ts D)
    (tr• (trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 3} p q r (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
              (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 3) Eq.refl))
         (trK {i₀ = # 1} {i₁ = # 3} {i₂ = # 4} {i₃ = # 5} u s t (lt (# 1) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5))
              (f (# 1) Eq.refl) (f (# 3) Eq.refl) (f (# 4) Eq.refl) (f (# 5) Eq.refl)))
    (tr• (trK {i₀ = # 2} {i₁ = # 3} {i₂ = # 4} {i₃ = # 5} r s t (lt (# 2) (# 3)) (lt (# 3) (# 4)) (lt (# 4) (# 5))
              (f (# 2) Eq.refl) (f (# 3) Eq.refl) (f (# 4) Eq.refl) (f (# 5) Eq.refl))
         (trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 4} p q v (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 4))
              (f (# 0) Eq.refl) (f (# 1) Eq.refl) (f (# 2) Eq.refl) (f (# 4) Eq.refl)))
    (by-al (⟨ k0123 ⟩ • ⟨ k1345ˢ ⟩) (⟨ k2345ˢ ⟩ • ⟨ k0124ˢ ⟩) (axiom r100))
  where
  ts = a ∷ b ∷ c ∷ d ∷ e ∷ f′ ∷ []
  D = chain (p <∷ q <∷ r <∷ s <∷ t <∷ one)
  f = at ts D
-- (6a): (101) of Figure 7, with (3c), (1a), (1b) and (2d) at the
-- standard instance (base6a).
dec-ax (TL.r6a {a = a} {b = b} {c = c} {d = d} {e = e} {f = f′} {g = g} {h = h} p q r s t u v w) =
  transport (frame ts D)
    (tr• M₀ (tr• M₄ (tr• X₀₄ (tr• K₂ (tr• K₁ (tr• X₃₄ (tr• K₁ (tr• K₂ (tr• X₀₄ (tr• M₀ M₄))))))))))
    (tr• K₂ (tr• K₁ (tr• X₃₄ (tr• K₁ K₂))))
    base6a
  where
  ts = a ∷ b ∷ c ∷ d ∷ e ∷ f′ ∷ g ∷ h ∷ []
  D = chain (p <∷ q <∷ r <∷ s <∷ t <∷ u <∷ v <∷ one)
  fr = at ts D
  M₀ = trM {i = # 0} (fr (# 0) Eq.refl)
  M₄ = trM {i = # 4} (fr (# 4) Eq.refl)
  X₀₄ = trX {i = # 0} {j = # 4} w (lt (# 0) (# 4)) (fr (# 0) Eq.refl) (fr (# 4) Eq.refl)
  X₃₄ = trX {i = # 3} {j = # 4} s (lt (# 3) (# 4)) (fr (# 3) Eq.refl) (fr (# 4) Eq.refl)
  K₁ = trK {i₀ = # 0} {i₁ = # 1} {i₂ = # 2} {i₃ = # 3} p q r (lt (# 0) (# 1)) (lt (# 1) (# 2)) (lt (# 2) (# 3))
           (fr (# 0) Eq.refl) (fr (# 1) Eq.refl) (fr (# 2) Eq.refl) (fr (# 3) Eq.refl)
  K₂ = trK {i₀ = # 4} {i₁ = # 5} {i₂ = # 6} {i₃ = # 7} t u v (lt (# 4) (# 5)) (lt (# 5) (# 6)) (lt (# 6) (# 7))
           (fr (# 4) Eq.refl) (fr (# 5) Eq.refl) (fr (# 6) Eq.refl) (fr (# 7) Eq.refl)

------------------------------------------------------------------------
-- The tables of FrameWords, checked

-- The transposition of a and b.
swapᶠ : Fin 8 → Fin 8 → Fin 8 → Fin 8
swapᶠ a b x = if eqᵇ x a then b else (if eqᵇ x b then a else x)

okMᵇ : Fin 8 → Bool
okMᵇ a = eqᵇ (act (fM a) zero) a ∧ all8 (λ y → eqᵇ (act (inv (fM a)) y) (act (fM a) y))

okXᵇ : Fin 8 → Fin 8 → Bool
okXᵇ a b = all8 (λ x → eqᵇ (act (fX a b) x) (swapᶠ a b x))

okKᵇ : Fin 8 → Fin 8 → Fin 8 → Fin 8 → Bool
okKᵇ a b c d =
  eqᵇ (act (fK a b c d) zero) a ∧ (eqᵇ (act (fK a b c d) (suc zero)) b ∧
  (eqᵇ (act (fK a b c d) (suc (suc zero))) c ∧ (eqᵇ (act (fK a b c d) (suc (suc (suc zero)))) d ∧
  all8 (λ y → eqᵇ (act (inv (fK a b c d)) y) (act (fK′ a b c d) y)))))

private
  okM : all8 okMᵇ ≡ true
  okM = Eq.refl

  okX : all8 (λ a → all8 (λ b → if incr a b then okXᵇ a b else true)) ≡ true
  okX = Eq.refl

  okK : all8 (λ a → all8 (λ b → all8 (λ c → all8 (λ d →
          if incr a b ∧ (incr b c ∧ incr c d) then okKᵇ a b c d else true)))) ≡ true
  okK = Eq.refl

  ∧-true : ∀ {x y} → x ≡ true → y ≡ true → x ∧ y ≡ true
  ∧-true Eq.refl Eq.refl = Eq.refl

okM-at : ∀ a → okMᵇ a ≡ true
okM-at = all8-sound okMᵇ okM

okX-at : ∀ a b → .(a < b) → okXᵇ a b ≡ true
okX-at a b p = if-true (incr a b) (incr-ok p)
  (all8-sound (λ b → if incr a b then okXᵇ a b else true)
    (all8-sound (λ a → all8 (λ b → if incr a b then okXᵇ a b else true)) okX a) b)

okK-at : ∀ a b c d → .(a < b) → .(b < c) → .(c < d) → okKᵇ a b c d ≡ true
okK-at a b c d p q r = if-true (incr a b ∧ (incr b c ∧ incr c d))
  (∧-true (incr-ok p) (∧-true (incr-ok q) (incr-ok r)))
  (all8-sound (λ d → if incr a b ∧ (incr b c ∧ incr c d) then okKᵇ a b c d else true)
    (all8-sound (λ c → all8 (λ d → if incr a b ∧ (incr b c ∧ incr c d) then okKᵇ a b c d else true))
      (all8-sound (λ b → all8 (λ c → all8 (λ d → if incr a b ∧ (incr b c ∧ incr c d) then okKᵇ a b c d else true)))
        (all8-sound (λ a → all8 (λ b → all8 (λ c → all8 (λ d →
                       if incr a b ∧ (incr b c ∧ incr c d) then okKᵇ a b c d else true)))) okK a) b) c) d)

------------------------------------------------------------------------
-- The decoding of FrameWords is the decoding by frames

private
  σw : CW
  σw = [ gate₂ σ-gate ]ʷ

  σ-fix : (y : Fin 8) → y ≢ zero → y ≢ suc zero → act σw y ≡ y
  σ-fix zero          h₀ h₁ = ⊥-elim (h₀ Eq.refl)
  σ-fix (suc zero)    h₀ h₁ = ⊥-elim (h₁ Eq.refl)
  σ-fix (suc (suc y)) h₀ h₁ = Eq.refl

  eqᵇ-refl : (x : Fin 8) → eqᵇ x x ≡ true
  eqᵇ-refl x = dec-true (x FinP.≟ x) Eq.refl

  eqᵇ-ne : (x y : Fin 8) → x ≢ y → eqᵇ x y ≡ false
  eqᵇ-ne x y ne = dec-false (x FinP.≟ y) ne

  swap-a : (a b : Fin 8) → swapᶠ a b a ≡ b
  swap-a a b = Eq.cong (λ t → if t then b else (if eqᵇ a b then a else a)) (eqᵇ-refl a)

  swap-b : (a b : Fin 8) → a ≢ b → swapᶠ a b b ≡ a
  swap-b a b ab = Eq.trans (Eq.cong (λ t → if t then b else (if eqᵇ b b then a else b)) (eqᵇ-ne b a (≢-sym ab)))
                           (Eq.cong (λ t → if t then a else b) (eqᵇ-refl b))

  swap-o : (a b x : Fin 8) → x ≢ a → x ≢ b → swapᶠ a b x ≡ x
  swap-o a b x xa xb = Eq.trans (Eq.cong (λ t → if t then b else (if eqᵇ x b then a else x)) (eqᵇ-ne x a xa))
                                (Eq.cong (λ t → if t then a else x) (eqᵇ-ne x b xb))

  -- A frame sending 0, 1 to a, b carries the transposition of 0 and 1 to
  -- that of a and b.
  conj-σ : (F : CW) {a b : Fin 8} → a ≢ b → act F zero ≡ a → act F (suc zero) ≡ b →
           ∀ x → act (F • (σw • inv F)) x ≡ swapᶠ a b x
  conj-σ F {a} {b} ab Fa Fb x = go (x FinP.≟ a) (x FinP.≟ b)
    where
    back : ∀ z → act F (act (inv F) z) ≡ z
    back = act-inv′ F
    at-a : act F (act σw (act (inv F) a)) ≡ b
    at-a = Eq.trans (Eq.cong (λ z → act F (act σw (act (inv F) z))) (Eq.sym Fa))
                    (Eq.trans (Eq.cong (λ z → act F (act σw z)) (act-inv F zero)) Fb)
    at-b : act F (act σw (act (inv F) b)) ≡ a
    at-b = Eq.trans (Eq.cong (λ z → act F (act σw (act (inv F) z))) (Eq.sym Fb))
                    (Eq.trans (Eq.cong (λ z → act F (act σw z)) (act-inv F (suc zero))) Fa)
    go : Dec (x ≡ a) → Dec (x ≡ b) → act F (act σw (act (inv F) x)) ≡ swapᶠ a b x
    go (yes e) _ = Eq.subst (λ z → act F (act σw (act (inv F) z)) ≡ swapᶠ a b z) (Eq.sym e)
                     (Eq.trans at-a (Eq.sym (swap-a a b)))
    go (no xa) (yes e) = Eq.subst (λ z → act F (act σw (act (inv F) z)) ≡ swapᶠ a b z) (Eq.sym e)
                     (Eq.trans at-b (Eq.sym (swap-b a b ab)))
    go (no xa) (no xb) = Eq.trans (Eq.cong (act F) (σ-fix y y0 y1)) (Eq.trans (back x) (Eq.sym (swap-o a b x xa xb)))
      where
      y = act (inv F) x
      y0 : y ≢ zero
      y0 e = xa (Eq.trans (Eq.sym (back x)) (Eq.trans (Eq.cong (act F) e) Fa))
      y1 : y ≢ suc zero
      y1 e = xb (Eq.trans (Eq.sym (back x)) (Eq.trans (Eq.cong (act F) e) Fb))

  ok₁ : ∀ {p q} → p ∧ q ≡ true → p ≡ true
  ok₁ {p} {q} = ∧-l {p} {q}

  ok₂ : ∀ {p q} → p ∧ q ≡ true → q ≡ true
  ok₂ {p} {q} = ∧-r {p} {q}

bridgeM : (a : Fin 8) → dM a ≈ dec (M-gen a)
bridgeM a = begin
  Fm.p (fM a) • m0 • Fm.p (fM a)                   ≡⟨ Eq.cong₂ (λ u v → u • m0 • v) (p≡Pc (fM a)) (p≡Pc (fM a)) ⟩
  Pc 0 (fM a) • m0 • Pc 0 (fM a)                   ≈⟨ sym (alias₁′ (frame (a ∷ []) ([] ∷ [])) (fM a) (fM a) ag inv≈) ⟩
  Fr m0 (frame (a ∷ []) ([] ∷ []))                 ∎
  where
  h = okM-at a
  ag : ∀ x → toℕ x ℕ.< 1 → act (frame (a ∷ []) ([] ∷ [])) x ≡ act (fM a) x
  ag zero _ = Eq.trans (frame-act (a ∷ []) ([] ∷ []) zero a Eq.refl)
                (Eq.sym (eqᵇ-sound _ _ (ok₁ {eqᵇ (act (fM a) zero) a} h)))
  ag (suc x) (s≤s ())
  inv≈ : ∀ y → act (inv (fM a)) y ≡ act (fM a) y
  inv≈ = everywhere (act (inv (fM a))) (act (fM a)) (ok₂ {eqᵇ (act (fM a) zero) a} h)

bridgeX : (a b : Fin 8) .(p : a < b) → dX a b ≈ dec (X-gen a b p)
bridgeX a b p = begin
  Fm.p (fX a b)                                ≡⟨ p≡Pc (fX a b) ⟩
  Pc 0 (fX a b)                                ≈⟨ perm-complete (fX a b) (F • (σw • inv F)) same ⟩
  Fr t01 F                                     ∎
  where
  F = frame (a ∷ b ∷ []) (dist2 p)
  same : ∀ x → act (fX a b) x ≡ act (F • (σw • inv F)) x
  same x = Eq.trans (everywhere (act (fX a b)) (swapᶠ a b) (okX-at a b p) x)
    (Eq.sym (conj-σ F (<⇒≢ p) (frame-act (a ∷ b ∷ []) (dist2 p) zero a Eq.refl)
                              (frame-act (a ∷ b ∷ []) (dist2 p) (suc zero) b Eq.refl) x))

bridgeK : (a b c d : Fin 8) .(p : a < b) .(q : b < c) .(r : c < d) → dK a b c d ≈ dec (K-gen a b c d p q r)
bridgeK a b c d p q r = begin
  Fm.p (fK a b c d) • NK • Fm.p (fK′ a b c d)      ≡⟨ Eq.cong₂ (λ u v → u • NK • v) (p≡Pc (fK a b c d)) (p≡Pc (fK′ a b c d)) ⟩
  Pc 0 (fK a b c d) • NK • Pc 0 (fK′ a b c d)      ≈⟨ sym (alias₄′ F (fK a b c d) (fK′ a b c d) ag inv≈) ⟩
  Fr NK F                                          ∎
  where
  ts = a ∷ b ∷ c ∷ d ∷ []
  F = frame ts (dist4 p q r)
  Q = fK a b c d
  h = okK-at a b c d p q r
  h₁ = ok₂ {eqᵇ (act Q zero) a} h
  h₂ = ok₂ {eqᵇ (act Q (suc zero)) b} h₁
  h₃ = ok₂ {eqᵇ (act Q (suc (suc zero))) c} h₂
  pt : (x : Fin 8) {y : Fin 8} → ts ‼ toℕ x ≡ just y → eqᵇ (act Q x) y ≡ true → act F x ≡ act Q x
  pt x {y} e k = Eq.trans (frame-act ts (dist4 p q r) x y e) (Eq.sym (eqᵇ-sound _ _ k))
  ag : ∀ x → toℕ x ℕ.< 4 → act F x ≡ act Q x
  ag zero _ = pt zero Eq.refl (ok₁ {eqᵇ (act Q zero) a} h)
  ag (suc zero) _ = pt (suc zero) Eq.refl (ok₁ {eqᵇ (act Q (suc zero)) b} h₁)
  ag (suc (suc zero)) _ = pt (suc (suc zero)) Eq.refl (ok₁ {eqᵇ (act Q (suc (suc zero))) c} h₂)
  ag (suc (suc (suc zero))) _ = pt (suc (suc (suc zero))) Eq.refl (ok₁ {eqᵇ (act Q (suc (suc (suc zero)))) d} h₃)
  ag (suc (suc (suc (suc x)))) (s≤s (s≤s (s≤s (s≤s ()))))
  inv≈ : ∀ y → act (inv Q) y ≡ act (fK′ a b c d) y
  inv≈ = everywhere (act (inv Q)) (act (fK′ a b c d)) (ok₂ {eqᵇ (act Q (suc (suc (suc zero)))) d} h₃)

bridge : (g : TL.Gen 8) → decode g ≈ dec g
bridge (M-gen a)             = bridgeM a
bridge (X-gen a b p)         = bridgeX a b p
bridge (K-gen a b c d p q r) = bridgeK a b c d p q r

bridgeʷ : (w : Word (TL.Gen 8)) → (decode ʷ) w ≈ decʷ w
bridgeʷ [ g ]ʷ   = bridge g
bridgeʷ ε       = refl
bridgeʷ (u • v) = cong (bridgeʷ u) (bridgeʷ v)

------------------------------------------------------------------------
-- The relations of Table 1 hold for the decoded circuits

axiom-decode : ∀ {w v} → TL._===_ {8} w v → (decode ʷ) w ≈ (decode ʷ) v
axiom-decode {w} {v} a = trans (bridgeʷ w) (trans (dec-ax a) (sym (bridgeʷ v)))

decode-cong : ∀ {w v} → PB._≈_ (TL._===_ {8}) w v → (decode ʷ) w ≈ (decode ʷ) v
decode-cong = PP.StarCongruence.fʷ-cong (TL._===_ {8}) _===_ decode axiom-decode

-- The alias of K_[4,5,6,7] that PrimitiveFrames uses.
k4567≈K4567 : k4567 ≈ dK (# 4) (# 5) (# 6) (# 7)
k4567≈K4567 = trans (sym (al-ok k4567ˢ))
  (sym (bridgeK (# 4) (# 5) (# 6) (# 7) (lt (# 4) (# 5)) (lt (# 5) (# 6)) (lt (# 6) (# 7))))
