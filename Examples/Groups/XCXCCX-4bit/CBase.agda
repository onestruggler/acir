------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled matching G = CX₃₀ and its frames over P
--
-- G is X on wire 0 controlled by wire 3: on the half where wire 3 is 1
-- it is the perfect matching μ₀ of the lower states that flips wire 0,
-- the pairs (0 1)(2 3)(4 5)(6 7) of Width3's Gray positions.  Its
-- frames Fr G p (PFrames) are the matching p μ₀ p⁻¹, controlled.  A
-- frame depends only on that matching, because a three-wire circuit
-- whose permutation commutes with the flip of wire 0 commutes with G
-- (wcore): on the states it is a flip of wire 0 on some values of
-- wires 2, 1 (Width3's T 0, T 2, T 4, T 6, each commuting with G by
-- equation E8 and X on its controls) followed by a permutation of
-- those values (a two-wire circuit on wires 1, 2, which G does not
-- touch).  The decomposition is computed from the permutation and
-- checked by evaluation (wcheck), so wcore and W take the check as a
-- hypothesis: every use is at concrete Coxeter words.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.CBase where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Properties as ℕP
open import Data.Vec.Base using ([] ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (Bits ; ⟦_⟧ ; eqF ; eqF-sound)
open import Examples.Groups.XCXCCX-4bit.Placed using (PG ; Xᵖ ; CXᵖ ; CCXᵖ ; ι ; ι* ; every ; disjoint ; disj-comm)
open import Examples.Groups.XCXCCX-4bit.ToPlaced using (pg ; pg-ok)
open import Examples.Groups.XCXCCX-4bit.PFrames
import Examples.Groups.XCXCCX-4bit.Width3 as W3
import Examples.Groups.XCXCCX-4bit.Coxeter as Cox
open import Examples.Groups.XCXCCX-4bit.Equations4 using (E8⁼)
open import Examples.Groups.XCXCCX-4bit.PlacedEngine using (prf)

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)
open SR (PP.word-setoid (4 VRel,_===_))

-- The circuits of Coxeter words on the three lower wires.
open Cox.Circuits 8 W3.T using () renaming (Pc to Pc₃)

private
  ∧ˡ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧ˡ {true} _ = Eq.refl

  ∧ʳ : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧ʳ {true} h = h

------------------------------------------------------------------------
-- Commutation

Comm : Circuit 4 → Circuit 4 → Set
Comm a b = 4 ⊢ a • b ≈ b • a

comm-ε : {c : Circuit 4} → Comm ε c
comm-ε = trans left-unit (sym right-unit)

comm-• : {a b c : Circuit 4} → Comm a c → Comm b c → Comm (a • b) c
comm-• {a} {b} {c} ea eb = begin
  (a • b) • c   ≈⟨ assoc ⟩
  a • (b • c)   ≈⟨ cong refl eb ⟩
  a • (c • b)   ≈⟨ sym assoc ⟩
  (a • c) • b   ≈⟨ cong ea refl ⟩
  (c • a) • b   ≈⟨ assoc ⟩
  c • (a • b)   ∎

comm-≈ : {a a′ c : Circuit 4} → 4 ⊢ a ≈ a′ → Comm a′ c → Comm a c
comm-≈ e h = trans (cong e refl) (trans h (cong refl (sym e)))

comm-sym : {a c : Circuit 4} → Comm a c → Comm c a
comm-sym h = sym h

-- Every letter of a word of placed letters disjoint from g.
comm-list : (g : PG) (xs : List PG) → every (λ x → disjoint x g) xs ≡ true → Comm (ι* xs) (ι g)
comm-list g []       _ = comm-ε
comm-list g (x ∷ xs) h = comm-• (disj-comm x g (∧ˡ h)) (comm-list g xs (∧ʳ {disjoint x g} h))

-- A circuit whose placed letters are disjoint from g.
comm-circ : (u : Circuit 4) (g : PG) → every (λ x → disjoint x g) (pg u) ≡ true → Comm u (ι g)
comm-circ u g h = comm-≈ (pg-ok u) (comm-list g (pg u) h)

------------------------------------------------------------------------
-- G and Ḡ

G : Circuit 4
G = ι (CXᵖ ₃ ₀)

-- G with its control negated: X on wire 0 controlled by wire 3 = 0.
Ḡ : Circuit 4
Ḡ = ι (Xᵖ ₃) • G • ι (Xᵖ ₃)

-- A circuit that commutes with G and with X on wire 3 commutes with Ḡ.
commḠ : {a : Circuit 4} → Comm a G → Comm a (ι (Xᵖ ₃)) → Comm a Ḡ
commḠ hG hX = comm-sym (comm-• (comm-sym hX) (comm-• (comm-sym hG) (comm-sym hX)))

------------------------------------------------------------------------
-- The flips of wire 0 commute with G

private
  -- E8: CCX₂₁→₀ commutes with G.
  comm-T4 : Comm (ι (CCXᵖ ₁ ₂ ₀)) G
  comm-T4 = begin
    ι (CCXᵖ ₁ ₂ ₀) • G                    ≈⟨ cong refl (sym right-unit) ⟩
    ι* (CCXᵖ ₁ ₂ ₀ ∷ CXᵖ ₃ ₀ ∷ [])        ≈⟨ prf E8⁼ ⟩
    ι* (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₀ ∷ [])        ≈⟨ cong refl right-unit ⟩
    G • ι (CCXᵖ ₁ ₂ ₀)                    ∎

  comm-X₁ : Comm (ι (Xᵖ ₁)) G
  comm-X₁ = disj-comm (Xᵖ ₁) (CXᵖ ₃ ₀) Eq.refl

  comm-X₂ : Comm (ι (Xᵖ ₂)) G
  comm-X₂ = disj-comm (Xᵖ ₂) (CXᵖ ₃ ₀) Eq.refl

-- The four flips of Width3: T 0, T 2, T 4, T 6 (X on the white
-- controls of CCX₂₁→₀).
flip-comm₀ : Comm (T₄ 0) G
flip-comm₀ = comm-≈ (pg-ok (T₄ 0))
  (comm-• comm-X₂ (comm-• comm-X₁ (comm-• comm-T4 (comm-• comm-X₁ (comm-• comm-X₂ comm-ε)))))

flip-comm₂ : Comm (T₄ 2) G
flip-comm₂ = comm-≈ (pg-ok (T₄ 2)) (comm-• comm-X₂ (comm-• comm-T4 (comm-• comm-X₂ comm-ε)))

flip-comm₄ : Comm (T₄ 4) G
flip-comm₄ = comm-≈ (pg-ok (T₄ 4)) (comm-• comm-T4 comm-ε)

flip-comm₆ : Comm (T₄ 6) G
flip-comm₆ = comm-≈ (pg-ok (T₄ 6)) (comm-• comm-X₁ (comm-• comm-T4 (comm-• comm-X₁ comm-ε)))

------------------------------------------------------------------------
-- Two-wire circuits on wires 1, 2 commute with G

-- c on wires 1, 2 of a four-wire circuit.
on12 : Circuit 2 → Circuit 4
on12 c = (c ↑) ↓ᵏ 1

comm-on12 : (c : Circuit 2) → Comm (on12 c) G
comm-on12 [ gate₀ ⌈ () ⌉ ]ʷ
comm-on12 [ gate₁ ⌈ X-gate ⌉ ]ʷ     = comm-circ [ gate₁ ⌈ X-gate ⌉ ↥ ]ʷ (CXᵖ ₃ ₀) Eq.refl
comm-on12 [ gate₂ ⌈ CX-gate ⌉ ]ʷ    = comm-circ [ gate₂ ⌈ CX-gate ⌉ ↥ ]ʷ (CXᵖ ₃ ₀) Eq.refl
comm-on12 [ gate₂ swap ]ʷ           = comm-circ [ gate₂ swap ↥ ]ʷ (CXᵖ ₃ ₀) Eq.refl
comm-on12 [ gate₀ ⌈ () ⌉ ↥ ]ʷ
comm-on12 [ gate₁ ⌈ X-gate ⌉ ↥ ]ʷ   = comm-circ [ gate₁ ⌈ X-gate ⌉ ↥ ↥ ]ʷ (CXᵖ ₃ ₀) Eq.refl
comm-on12 [ gate₀ ⌈ () ⌉ ↥ ↥ ]ʷ
comm-on12 ε                         = comm-ε
comm-on12 (u • v)                   = comm-• (comm-on12 u) (comm-on12 v)

------------------------------------------------------------------------
-- The decomposition of a permutation commuting with the flip of wire 0

-- A circuit or nothing.
fl : Bool → Circuit 3 → Circuit 3
fl true  c = c
fl false _ = ε

-- The four flips, chosen by the values (wire 1, wire 2) they act on.
flipsC : (Bits 2 → Bool) → Circuit 3
flipsC b = fl (b (false ∷ false ∷ [])) (W3.T 0) • fl (b (true ∷ false ∷ [])) (W3.T 2)
         • fl (b (true ∷ true ∷ [])) (W3.T 4) • fl (b (false ∷ true ∷ [])) (W3.T 6)

-- A two-wire circuit for each permutation of the values of two wires,
-- given by its images of 00, 10, 01, 11 (wire 0 first).
pairC : Bits 2 → Bits 2 → Bits 2 → Bits 2 → Circuit 2
pairC (false ∷ false ∷ []) (false ∷ true ∷ []) (true ∷ false ∷ []) (true ∷ true ∷ []) = σ
pairC (false ∷ false ∷ []) (false ∷ true ∷ []) (true ∷ true ∷ []) (true ∷ false ∷ []) = CX • σ
pairC (false ∷ false ∷ []) (true ∷ false ∷ []) (false ∷ true ∷ []) (true ∷ true ∷ []) = ε
pairC (false ∷ false ∷ []) (true ∷ false ∷ []) (true ∷ true ∷ []) (false ∷ true ∷ []) = CX
pairC (false ∷ false ∷ []) (true ∷ true ∷ []) (false ∷ true ∷ []) (true ∷ false ∷ []) = CX • σ • CX
pairC (false ∷ false ∷ []) (true ∷ true ∷ []) (true ∷ false ∷ []) (false ∷ true ∷ []) = σ • CX
pairC (false ∷ true ∷ []) (false ∷ false ∷ []) (true ∷ false ∷ []) (true ∷ true ∷ []) = X • CX • σ
pairC (false ∷ true ∷ []) (false ∷ false ∷ []) (true ∷ true ∷ []) (true ∷ false ∷ []) = X • σ
pairC (false ∷ true ∷ []) (true ∷ false ∷ []) (false ∷ false ∷ []) (true ∷ true ∷ []) = X ↑ • CX • σ • CX
pairC (false ∷ true ∷ []) (true ∷ false ∷ []) (true ∷ true ∷ []) (false ∷ false ∷ []) = σ • CX • X ↑
pairC (false ∷ true ∷ []) (true ∷ true ∷ []) (false ∷ false ∷ []) (true ∷ false ∷ []) = X ↑
pairC (false ∷ true ∷ []) (true ∷ true ∷ []) (true ∷ false ∷ []) (false ∷ false ∷ []) = CX • X ↑
pairC (true ∷ false ∷ []) (false ∷ false ∷ []) (false ∷ true ∷ []) (true ∷ true ∷ []) = X • CX
pairC (true ∷ false ∷ []) (false ∷ false ∷ []) (true ∷ true ∷ []) (false ∷ true ∷ []) = X
pairC (true ∷ false ∷ []) (false ∷ true ∷ []) (false ∷ false ∷ []) (true ∷ true ∷ []) = X ↑ • σ • CX
pairC (true ∷ false ∷ []) (false ∷ true ∷ []) (true ∷ true ∷ []) (false ∷ false ∷ []) = CX • X ↑ • σ • CX
pairC (true ∷ false ∷ []) (true ∷ true ∷ []) (false ∷ false ∷ []) (false ∷ true ∷ []) = X ↑ • σ
pairC (true ∷ false ∷ []) (true ∷ true ∷ []) (false ∷ true ∷ []) (false ∷ false ∷ []) = CX • X ↑ • σ
pairC (true ∷ true ∷ []) (false ∷ false ∷ []) (false ∷ true ∷ []) (true ∷ false ∷ []) = X • σ • CX
pairC (true ∷ true ∷ []) (false ∷ false ∷ []) (true ∷ false ∷ []) (false ∷ true ∷ []) = X • CX • σ • CX
pairC (true ∷ true ∷ []) (false ∷ true ∷ []) (false ∷ false ∷ []) (true ∷ false ∷ []) = X ↑ • CX
pairC (true ∷ true ∷ []) (false ∷ true ∷ []) (true ∷ false ∷ []) (false ∷ false ∷ []) = X • X ↑
pairC (true ∷ true ∷ []) (true ∷ false ∷ []) (false ∷ false ∷ []) (false ∷ true ∷ []) = X ↑ • CX • σ
pairC (true ∷ true ∷ []) (true ∷ false ∷ []) (false ∷ true ∷ []) (false ∷ false ∷ []) = X • X ↑ • σ
pairC _ _ _ _ = ε

-- The canonical circuit of a permutation π of the lower states:
-- flip wire 0 where π does on the states with wire 0 = 0, then permute
-- the values of wires 1, 2 as π does.
canB : (Bits 3 → Bits 3) → Bits 2 → Bool
canB π v = head (π (false ∷ v))

canS : (Bits 3 → Bits 3) → Bits 2 → Bits 2
canS π v = tail (π (false ∷ v))

canP : (Bits 3 → Bits 3) → Circuit 2
canP π = pairC (canS π (false ∷ false ∷ [])) (canS π (true ∷ false ∷ []))
               (canS π (false ∷ true ∷ [])) (canS π (true ∷ true ∷ []))

canon : (Bits 3 → Bits 3) → Circuit 3
canon π = flipsC (canB π) • canP π ↑

-- The check: the permutation of r is its canonical circuit's.
wcheck : CW → Bool
wcheck r = eqF 3 ⟦ Pc₃ 0 r ⟧ ⟦ canon ⟦ Pc₃ 0 r ⟧ ⟧

------------------------------------------------------------------------
-- The frame lemma for G

Pc-↓ : (o : ℕ) {n : ℕ} (r : Word (SG n)) → Pc o r ≡ Pc₃ o r ↓ᵏ 1
Pc-↓ o [ g ]ʷ   = Eq.refl
Pc-↓ o ε       = Eq.refl
Pc-↓ o (u • v) = Eq.cong₂ _•_ (Pc-↓ o u) (Pc-↓ o v)

comm-flips : (b : Bits 2 → Bool) → Comm (flipsC b ↓ᵏ 1) G
comm-flips b =
  comm-• (cf (b (false ∷ false ∷ [])) 0 flip-comm₀)
  (comm-• (cf (b (true ∷ false ∷ [])) 2 flip-comm₂)
  (comm-• (cf (b (true ∷ true ∷ [])) 4 flip-comm₄) (cf (b (false ∷ true ∷ [])) 6 flip-comm₆)))
  where
  cf : (x : Bool) (k : ℕ) → Comm (T₄ k) G → Comm (fl x (W3.T k) ↓ᵏ 1) G
  cf true  k h = h
  cf false k h = comm-ε

-- A Coxeter word whose permutation passes the check commutes with G.
wcore : (r : CW) → wcheck r ≡ true → Comm (Pc 0 r) G
wcore r h =
  Eq.subst (λ z → Comm z G) (Eq.sym (Pc-↓ 0 r))
    (comm-≈ (P-eq {Pc₃ 0 r} {canon π} (eqF-sound 3 ⟦ Pc₃ 0 r ⟧ ⟦ canon π ⟧ h))
      (comm-• (comm-flips (canB π)) (comm-on12 (canP π))))
  where
  π = ⟦ Pc₃ 0 r ⟧

-- Two frames of G whose Coxeter words differ by a word commuting with G
-- are equal.
Wc : (p q : CW) → Comm (Pc 0 (inv q • p)) G → 4 ⊢ Fr G p ≈ Fr G q
Wc p q h = begin
  Pc 0 p • G • Pc 0 (inv p)                              ≈⟨ cong p≈ refl ⟩
  (Pc 0 q • Pc 0 r) • G • Pc 0 (inv p)                   ≈⟨ assoc ⟩
  Pc 0 q • (Pc 0 r • G • Pc 0 (inv p))                   ≈⟨ cong refl (sym assoc) ⟩
  Pc 0 q • ((Pc 0 r • G) • Pc 0 (inv p))                 ≈⟨ cong refl (cong h refl) ⟩
  Pc 0 q • ((G • Pc 0 r) • Pc 0 (inv p))                 ≈⟨ cong refl assoc ⟩
  Pc 0 q • (G • (Pc 0 r • Pc 0 (inv p)))                 ≈⟨ cong refl (cong refl ip) ⟩
  Pc 0 q • G • Pc 0 (inv q)                              ∎
  where
  r = inv q • p
  p≈ : 4 ⊢ Pc 0 p ≈ Pc 0 q • Pc 0 r
  p≈ = begin
    Pc 0 p                                ≈⟨ sym left-unit ⟩
    ε • Pc 0 p                            ≈⟨ cong (sym (Pc-inv 0 ℕP.≤-refl q)) refl ⟩
    (Pc 0 q • Pc 0 (inv q)) • Pc 0 p      ≈⟨ assoc ⟩
    Pc 0 q • (Pc 0 (inv q) • Pc 0 p)      ∎
  ip : 4 ⊢ Pc 0 r • Pc 0 (inv p) ≈ Pc 0 (inv q)
  ip = begin
    (Pc 0 (inv q) • Pc 0 p) • Pc 0 (inv p)    ≈⟨ assoc ⟩
    Pc 0 (inv q) • (Pc 0 p • Pc 0 (inv p))    ≈⟨ cong refl (Pc-inv 0 ℕP.≤-refl p) ⟩
    Pc 0 (inv q) • ε                          ≈⟨ right-unit ⟩
    Pc 0 (inv q)                              ∎

-- The same with the commutation checked.
W : (p q : CW) → wcheck (inv q • p) ≡ true → 4 ⊢ Fr G p ≈ Fr G q
W p q h = Wc p q (wcore (inv q • p) h)
