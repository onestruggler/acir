------------------------------------------------------------------------
-- Presentations of groups
--
-- The adder the paper's tool verified, classically (Amy, QPL 2018,
-- section 5.2 and table 2)
--
-- The paper describes its adder in words only -- "a standard
-- out-of-place ripple-carry adder which uses n − 1 ancilla bits to
-- store intermediate carry values and an additional n bit register to
-- store the output, before copying out and uncomputing ... 5n − 1 bits
-- of space ... 4(n − 1) Toffoli gates" -- but its tool, Feynman
-- (github.com/meamy/feynman), generates it: carryRipple, in
-- src/Feynman/Verification/SOP.hs, verified by verifyOOPAdder against
-- adderOOPSpec.  Here is that netlist, gate for gate, and the proof
-- that it computes what the tool's specification says, for every n.
--
-- The wires.  Five registers of n = m + 1 bits each (Reg, Line): the
-- inputs a and b, the output c, the register anc that holds the sum
-- bits, and carry, whose bit i holds the carry into position i --
-- carry₀ included, the carry into position 0, which is 0 on input and
-- on output: the tool allocates it and its first majority block uses
-- it as scratch, but it never holds a carry.  That is 5n
-- wires, table 2's 40 and 80 qubits for n = 8 and n = 16; the text's
-- 5n − 1 counts only the n − 1 carries that store a value.  On the
-- tool's layout (standardᶠ) register r's bit i is wire n·r + i, in the
-- order a, b, c, anc, carry of its verifyOOPAdder.
--
-- The netlist (carryRipple), in the tool's words:
--
--    maj a b c c′ = CNOT b c; Toffoli a c c′; CNOT b c; Toffoli b c c′
--    plus a b c d = CNOT a d; CNOT b d; CNOT c d
--    compute      = CNOT a₀ anc₀; CNOT b₀ anc₀;
--                   for i = 0 … n − 2: maj aᵢ bᵢ carryᵢ carryᵢ₊₁;
--                                      plus aᵢ₊₁ bᵢ₊₁ carryᵢ₊₁ ancᵢ₊₁
--    copy         = for i = 0 … n − 1: CNOT ancᵢ cᵢ
--    carryRipple  = compute; copy; compute reversed
--
-- (majᶠ, plusᶠ, sum₀ᶠ, compute, copyᶠ; the tool uncomputes with the
-- adjoint of the expanded compute, which is compute reversed with each
-- Toffoli circuit replaced by its adjoint: the same gates, read as a
-- netlist, since a Toffoli gate is its own inverse).  maj adds the
-- majority maj(a, b, c) = a (c ⊕ b) ⊕ b c into c′ and restores c
-- (majᶠ-here, majᶠ-there); plus adds a ⊕ b ⊕ c into d.  The netlist
-- displayed for n = 2 (netlistᶠ-2) is the tool's list for n = 2.
--
-- The theorem.  Call an input blank when anc and carry read 0
-- (Blankᶠ; they are the ancillas, the tool's constant-0 inputs).  On a
-- blank input the output register gains the n sum bits of a + b --
-- cᵢ becomes cᵢ ⊕ sumbit(a, b)ᵢ (carryRipple-out), PathSum.Adder.
-- Binary's sumbit, so from c = 0 it reads (a + b) mod 2^n
-- (carryRipple-value): the carry out is never computed.  On every
-- input every other wire ends as it began (carryRipple-work).
-- Together: on blank inputs the netlist computes |a⟩|b⟩|c⟩ ↦
-- |a⟩|b⟩|c ⊕ ((a + b) mod 2^n)⟩, every other wire unchanged
-- (additionᶠ, carryRipple-computes) -- exactly the function of the
-- tool's specification, whose output register is symbolic too
-- (PathSum.Adder.Tool).  The proof is PathSum.Adder.Ripple's:
-- compute writes the sum bits into anc and the carries into
-- carry₁ … carry_(n−1), and no other wire -- carry₀, which the first
-- majority block borrows, is given back (compute-values, steps-frame,
-- compute-frame, by induction on the positions, the positions after
-- the first forming the same netlist with carry in carry₁: innerᶠ);
-- the copy xors anc into c (copyᶠ-values, copyᶠ-frame); and Bennett's
-- lemma (PathSum.Reversible) uncomputes.
--
-- Resources: 4(n − 1) Toffoli gates and 11n − 6 CNOTs, for every n ≥ 1
-- (carryRipple-toffolis, carryRipple-cnots).  Against PathSum.Adder.
-- Ripple's adder, which computes the carry out as well, in the same 5n
-- qubits and 4(n − 1) Toffoli gates: at position 0 the tool runs the
-- full majority block against carry₀ (one Toffoli gate and two CNOTs
-- more, each way), and it copies no carry out (two Toffoli gates and
-- two CNOTs fewer).  With 28 and 60 Toffoli gates and 82 and 170 CNOTs
-- at n = 8 and n = 16 (table-2-Adder8ᶠ, table-2-Adder16ᶠ), and the
-- tool's Toffoli circuit (two Hadamards, seven CNOTs, seven T gates:
-- PathSum.Toffoli.Depth3), this is table 2's rows exactly: 56 and 120
-- path variables, 196 and 420 T gates, 9 · 28 + 82 = 334 and
-- 9 · 60 + 170 = 710 Clifford gates (PathSum.Adder.Tool computes them
-- from the circuit).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Adder.CarryRipple where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; _xor_)
open import Data.Bool.Properties using (xor-assoc; xor-same; xor-identityʳ)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; combine)
open import Data.List.Base using
  (List; []; _∷_; _++_; reverse; map; allFin)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat.Base using
  (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _%_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (m^n≢0; +-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Data.Fin.Properties as Fin

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

open import PathSum.Adder.Binary using
  (val; val-cong; maj; sumbit; carry; sumbit-mod)
open import PathSum.Adder.Layout using (Layout; wire; wire-inj)
open import PathSum.Adder.Ripple using (distinct; gate-wires)
open import PathSum.Reversible using
  (Gate; ccx; cx; ⟪_⟫; run; run-++; ⟪⟫-here; ⟪⟫-there; run-frame; Within;
   bennett-work; bennett-out; count; count-++; count-reverse; is-ccx;
   is-cx; toffolis; cnots)

private
  variable
    m N : ℕ

  Bits : ℕ → Set
  Bits N = Fin N → Bool

  run-++ᵂ : (gs hs : List (Gate N)) (x : Bits N) (w : Fin N) →
            run (gs ++ hs) x w ≡ run hs (run gs x) w
  run-++ᵂ gs hs x w = cong (λ f → f w) (run-++ gs hs x)

  cancel : ∀ p q → (p xor q) xor q ≡ p
  cancel p q = trans (xor-assoc p q q)
                     (trans (cong (p xor_) (xor-same q)) (xor-identityʳ p))

  maj-cong : ∀ {p p′ q q′ r r′} → p ≡ p′ → q ≡ q′ → r ≡ r′ →
             maj p q r ≡ maj p′ q′ r′
  maj-cong refl refl refl = refl


------------------------------------------------------------------------
-- The wires

-- The tool's registers: the inputs a and b, the output c, the sum bits
-- anc and the carries carry.

data Reg : Set where
  ra rb rc ranc rcarry : Reg

-- n = m + 1 bits of each.

Line : ℕ → Set
Line m = Reg × Fin (suc m)

-- The positions after the first, as the same registers one bit
-- shorter.

shiftᶠ : Line m → Line (suc m)
shiftᶠ (r , i) = r , suc i

shiftᶠ-injective : (u v : Line m) → shiftᶠ u ≡ shiftᶠ v → u ≡ v
shiftᶠ-injective (r , i) (r′ , i′) e =
  cong₂ _,_ (cong proj₁ e) (Fin.suc-injective (cong proj₂ e))

innerᶠ : Layout (Line (suc m)) N → Layout (Line m) N
innerᶠ L = record
  { wire     = λ v → wire L (shiftᶠ v)
  ; wire-inj = λ u v e →
      shiftᶠ-injective u v (wire-inj L (shiftᶠ u) (shiftᶠ v) e)
  }


------------------------------------------------------------------------
-- The tool's blocks

-- maj x y c t: t ⊕= maj(x, y, c), by c ⊕= y, t ⊕= x c, c ⊕= y,
-- t ⊕= y c.

majᶠ : (x y c t : Fin N) → .(y ≢ c) → .(x ≢ c) → .(x ≢ t) → .(c ≢ t) →
       .(y ≢ t) → List (Gate N)
majᶠ x y c t yc xc xt ct yt =
  cx y c yc ∷ ccx x c t xc xt ct ∷ cx y c yc ∷ ccx y c t yc yt ct ∷ []

private
  maj-tool : ∀ a b c → maj a b c ≡ (a ∧ (c xor b)) xor (b ∧ c)
  maj-tool false false false = refl
  maj-tool false false true  = refl
  maj-tool false true  false = refl
  maj-tool false true  true  = refl
  maj-tool true  false false = refl
  maj-tool true  false true  = refl
  maj-tool true  true  false = refl
  maj-tool true  true  true  = refl

module _ {x y c t : Fin N} (yc : y ≢ c) (xc : x ≢ c) (xt : x ≢ t)
         (ct : c ≢ t) (yt : y ≢ t) (u : Bits N) where

  private
    g₁ g₂ g₄ : Gate N
    g₁ = cx y c yc
    g₂ = ccx x c t xc xt ct
    g₄ = ccx y c t yc yt ct

    u₁ u₂ u₃ : Bits N
    u₁ = ⟪ g₁ ⟫ u
    u₂ = ⟪ g₂ ⟫ u₁
    u₃ = ⟪ g₁ ⟫ u₂

    tc : t ≢ c
    tc e = ct (sym e)

    u₁-c : u₁ c ≡ u c xor u y
    u₁-c = ⟪⟫-here g₁ u

    u₂-t : u₂ t ≡ u t xor (u x ∧ (u c xor u y))
    u₂-t = trans (⟪⟫-here g₂ u₁)
                 (cong₂ _xor_ (⟪⟫-there g₁ u tc)
                        (cong₂ _∧_ (⟪⟫-there g₁ u xc) u₁-c))

    u₂-y : u₂ y ≡ u y
    u₂-y = trans (⟪⟫-there g₂ u₁ yt) (⟪⟫-there g₁ u yc)

    u₃-c : u₃ c ≡ u c
    u₃-c = trans (⟪⟫-here g₁ u₂)
                 (trans (cong₂ _xor_ (trans (⟪⟫-there g₂ u₁ ct) u₁-c) u₂-y)
                        (cancel (u c) (u y)))

  -- The target gains maj(x, y, c) = x (c ⊕ y) ⊕ y c ...

  majᶠ-here : run (majᶠ x y c t yc xc xt ct yt) u t ≡
              u t xor maj (u x) (u y) (u c)
  majᶠ-here =
    trans (⟪⟫-here g₄ u₃)
    (trans (cong₂ _xor_ (trans (⟪⟫-there g₁ u₂ tc) u₂-t)
                        (cong₂ _∧_ (trans (⟪⟫-there g₁ u₂ yc) u₂-y) u₃-c))
    (trans (xor-assoc (u t) (u x ∧ (u c xor u y)) (u y ∧ u c))
           (cong (u t xor_) (sym (maj-tool (u x) (u y) (u c))))))

  -- ... and every other wire, c included, is as it was.

  majᶠ-there : ∀ w → w ≢ t → run (majᶠ x y c t yc xc xt ct yt) u w ≡ u w
  majᶠ-there w w≢t = go (w Fin.≟ c)
    where
    go : Dec (w ≡ c) → run (majᶠ x y c t yc xc xt ct yt) u w ≡ u w
    go (no w≢c)  = run-frame (majᶠ x y c t yc xc xt ct yt) u
                             (w≢c ∷ w≢t ∷ w≢c ∷ w≢t ∷ [])
    go (yes w≡c) =
      trans (cong (run (majᶠ x y c t yc xc xt ct yt) u) w≡c)
      (trans (⟪⟫-there g₄ u₃ ct)
             (trans u₃-c (cong u (sym w≡c))))

-- plus x y c d: d ⊕= x ⊕ y ⊕ c.

plusᶠ : (x y c d : Fin N) → .(x ≢ d) → .(y ≢ d) → .(c ≢ d) → List (Gate N)
plusᶠ x y c d xd yd cd = cx x d xd ∷ cx y d yd ∷ cx c d cd ∷ []

module _ {x y c d : Fin N} (xd : x ≢ d) (yd : y ≢ d) (cd : c ≢ d)
         (u : Bits N) where

  private
    h₁ h₂ h₃ : Gate N
    h₁ = cx x d xd
    h₂ = cx y d yd
    h₃ = cx c d cd

    v₁ v₂ : Bits N
    v₁ = ⟪ h₁ ⟫ u
    v₂ = ⟪ h₂ ⟫ v₁

  plusᶠ-here : run (plusᶠ x y c d xd yd cd) u d ≡
               u d xor (u x xor (u y xor u c))
  plusᶠ-here =
    trans (⟪⟫-here h₃ v₂)
    (trans (cong₂ _xor_
             (trans (⟪⟫-here h₂ v₁)
                    (cong₂ _xor_ (⟪⟫-here h₁ u) (⟪⟫-there h₁ u yd)))
             (trans (⟪⟫-there h₂ v₁ cd) (⟪⟫-there h₁ u cd)))
    (trans (xor-assoc (u d xor u x) (u y) (u c))
           (xor-assoc (u d) (u x) (u y xor u c))))

  plusᶠ-there : ∀ w → w ≢ d → run (plusᶠ x y c d xd yd cd) u w ≡ u w
  plusᶠ-there w w≢d =
    run-frame (plusᶠ x y c d xd yd cd) u (w≢d ∷ w≢d ∷ w≢d ∷ [])

-- The first sum bit, d ⊕= x ⊕ y (there is no carry in).

sum₀ᶠ : (x y d : Fin N) → .(x ≢ d) → .(y ≢ d) → List (Gate N)
sum₀ᶠ x y d xd yd = cx x d xd ∷ cx y d yd ∷ []

module _ {x y d : Fin N} (xd : x ≢ d) (yd : y ≢ d) (u : Bits N) where

  sum₀ᶠ-here : run (sum₀ᶠ x y d xd yd) u d ≡ u d xor (u x xor u y)
  sum₀ᶠ-here =
    trans (⟪⟫-here (cx y d yd) (⟪ cx x d xd ⟫ u))
    (trans (cong₂ _xor_ (⟪⟫-here (cx x d xd) u)
                        (⟪⟫-there (cx x d xd) u yd))
           (xor-assoc (u d) (u x) (u y)))

  sum₀ᶠ-there : ∀ w → w ≢ d → run (sum₀ᶠ x y d xd yd) u w ≡ u w
  sum₀ᶠ-there w w≢d = run-frame (sum₀ᶠ x y d xd yd) u (w≢d ∷ w≢d ∷ [])


------------------------------------------------------------------------
-- The netlist

-- anc₀ ⊕= a₀ ⊕ b₀.

sum₀ : Layout (Line m) N → List (Gate N)
sum₀ L =
  sum₀ᶠ (wire L (ra , zero)) (wire L (rb , zero)) (wire L (ranc , zero))
        (distinct L (ra , zero) (ranc , zero) (λ ()))
        (distinct L (rb , zero) (ranc , zero) (λ ()))

-- One step: the carry into position 1, carry₁ ⊕= maj(a₀, b₀, carry₀),
-- then the sum bit at position 1, anc₁ ⊕= a₁ ⊕ b₁ ⊕ carry₁.

module _ (L : Layout (Line (suc m)) N) where

  private
    yc : wire L (rb , zero) ≢ wire L (rcarry , zero)
    yc = distinct L (rb , zero) (rcarry , zero) (λ ())

    xc : wire L (ra , zero) ≢ wire L (rcarry , zero)
    xc = distinct L (ra , zero) (rcarry , zero) (λ ())

    xt : wire L (ra , zero) ≢ wire L (rcarry , suc zero)
    xt = distinct L (ra , zero) (rcarry , suc zero) (λ ())

    ct : wire L (rcarry , zero) ≢ wire L (rcarry , suc zero)
    ct = distinct L (rcarry , zero) (rcarry , suc zero) (λ ())

    yt : wire L (rb , zero) ≢ wire L (rcarry , suc zero)
    yt = distinct L (rb , zero) (rcarry , suc zero) (λ ())

    xd : wire L (ra , suc zero) ≢ wire L (ranc , suc zero)
    xd = distinct L (ra , suc zero) (ranc , suc zero) (λ ())

    yd : wire L (rb , suc zero) ≢ wire L (ranc , suc zero)
    yd = distinct L (rb , suc zero) (ranc , suc zero) (λ ())

    cd : wire L (rcarry , suc zero) ≢ wire L (ranc , suc zero)
    cd = distinct L (rcarry , suc zero) (ranc , suc zero) (λ ())

  carry-step : List (Gate N)
  carry-step =
    majᶠ (wire L (ra , zero)) (wire L (rb , zero)) (wire L (rcarry , zero))
         (wire L (rcarry , suc zero)) yc xc xt ct yt

  sum-step : List (Gate N)
  sum-step =
    plusᶠ (wire L (ra , suc zero)) (wire L (rb , suc zero))
          (wire L (rcarry , suc zero)) (wire L (ranc , suc zero)) xd yd cd

  step : List (Gate N)
  step = carry-step ++ sum-step

  carry-step-here :
    (u : Bits N) →
    run carry-step u (wire L (rcarry , suc zero)) ≡
    u (wire L (rcarry , suc zero)) xor
      maj (u (wire L (ra , zero))) (u (wire L (rb , zero)))
          (u (wire L (rcarry , zero)))
  carry-step-here = majᶠ-here yc xc xt ct yt

  carry-step-there : (u : Bits N) → ∀ w → w ≢ wire L (rcarry , suc zero) →
                     run carry-step u w ≡ u w
  carry-step-there = majᶠ-there yc xc xt ct yt

  sum-step-here :
    (u : Bits N) →
    run sum-step u (wire L (ranc , suc zero)) ≡
    u (wire L (ranc , suc zero)) xor
      (u (wire L (ra , suc zero)) xor
        (u (wire L (rb , suc zero)) xor u (wire L (rcarry , suc zero))))
  sum-step-here = plusᶠ-here xd yd cd

  sum-step-there : (u : Bits N) → ∀ w → w ≢ wire L (ranc , suc zero) →
                   run sum-step u w ≡ u w
  sum-step-there = plusᶠ-there xd yd cd

-- The steps, position after position.

steps : Layout (Line m) N → List (Gate N)
steps {zero}  L = []
steps {suc m} L = step L ++ steps (innerᶠ L)

-- The tool's compute, copy, and the whole netlist.

compute : Layout (Line m) N → List (Gate N)
compute L = sum₀ L ++ steps L

copy₀ᶠ : Layout (Line m) N → Gate N
copy₀ᶠ L = cx (wire L (ranc , zero)) (wire L (rc , zero))
              (distinct L (ranc , zero) (rc , zero) (λ ()))

copyᶠ : Layout (Line m) N → List (Gate N)
copyᶠ {zero}  L = copy₀ᶠ L ∷ []
copyᶠ {suc m} L = copy₀ᶠ L ∷ copyᶠ (innerᶠ L)

carryRipple : Layout (Line m) N → List (Gate N)
carryRipple L = compute L ++ copyᶠ L ++ reverse (compute L)


------------------------------------------------------------------------
-- What compute does

-- The steps write no wire but carry₁ … carry_m and anc₁ … anc_m ...

steps-frame : (L : Layout (Line m) N) (u : Bits N) (w : Fin N) →
              (∀ j → wire L (rcarry , suc j) ≢ w) →
              (∀ i → wire L (ranc , suc i) ≢ w) →
              run (steps L) u w ≡ u w
steps-frame {zero}  L u w hk hs = refl
steps-frame {suc m} L u w hk hs =
  trans (run-++ᵂ (step L) (steps (innerᶠ L)) u w)
  (trans (steps-frame (innerᶠ L) (run (step L) u) w
                      (λ j → hk (suc j)) (λ i → hs (suc i)))
  (trans (run-++ᵂ (carry-step L) (sum-step L) u w)
  (trans (sum-step-there L (run (carry-step L) u) w (λ e → hs zero (sym e)))
         (carry-step-there L u w (λ e → hk zero (sym e))))))

-- ... where, from an input whose carries after the first and sum bits
-- after the first read 0, they write the carries of a + b + c (c the
-- carry in, on carry₀) and the sum bits after the first.

steps-values :
  (L : Layout (Line m) N) (u : Bits N) (a b : Fin (suc m) → Bool)
  (c : Bool) →
  (∀ i → u (wire L (ra , i)) ≡ a i) → (∀ i → u (wire L (rb , i)) ≡ b i) →
  u (wire L (rcarry , zero)) ≡ c →
  (∀ j → u (wire L (rcarry , suc j)) ≡ false) →
  (∀ i → u (wire L (ranc , suc i)) ≡ false) →
  (∀ j → run (steps L) u (wire L (rcarry , suc j)) ≡ carry a b c j) ×
  (∀ i → run (steps L) u (wire L (ranc , suc i)) ≡ sumbit a b c (suc i))
steps-values {zero}  L u a b c ha hb hc hk hs = (λ ()) , (λ ())
steps-values {suc m} {N} L u a b c ha hb hc hk hs = carries , sums
  where
  u₁ u₂ : Bits N
  u₁ = run (carry-step L) u
  u₂ = run (step L) u

  c′ : Bool
  c′ = maj (a zero) (b zero) c

  k₁ s₁ : Fin N
  k₁ = wire L (rcarry , suc zero)
  s₁ = wire L (ranc , suc zero)

  -- The carry step writes carry₁ only, with the first carry ...

  u₁-off : ∀ w → w ≢ k₁ → u₁ w ≡ u w
  u₁-off = carry-step-there L u

  u₁-k₁ : u₁ k₁ ≡ c′
  u₁-k₁ = trans (carry-step-here L u)
                (cong₂ _xor_ (hk zero) (maj-cong (ha zero) (hb zero) hc))

  -- ... and the sum step anc₁ only, with the second sum bit.

  u₂-off : ∀ w → w ≢ s₁ → u₂ w ≡ u₁ w
  u₂-off w p = trans (run-++ᵂ (carry-step L) (sum-step L) u w)
                     (sum-step-there L u₁ w p)

  u₂-u : (v : Line (suc m)) → v ≢ (rcarry , suc zero) →
         v ≢ (ranc , suc zero) → u₂ (wire L v) ≡ u (wire L v)
  u₂-u v p q = trans (u₂-off _ (distinct L v _ q))
                     (u₁-off _ (distinct L v _ p))

  u₂-k₁ : u₂ k₁ ≡ c′
  u₂-k₁ = trans (u₂-off _ (distinct L (rcarry , suc zero) (ranc , suc zero)
                                   (λ ())))
                u₁-k₁

  u₂-s₁ : u₂ s₁ ≡ sumbit a b c (suc zero)
  u₂-s₁ =
    trans (run-++ᵂ (carry-step L) (sum-step L) u s₁)
    (trans (sum-step-here L u₁)
    (cong₂ _xor_
      (trans (u₁-off _ (distinct L (ranc , suc zero) (rcarry , suc zero)
                                 (λ ())))
             (hs zero))
      (cong₂ _xor_
        (trans (u₁-off _ (distinct L (ra , suc zero) (rcarry , suc zero)
                                   (λ ())))
               (ha (suc zero)))
        (cong₂ _xor_
          (trans (u₁-off _ (distinct L (rb , suc zero) (rcarry , suc zero)
                                     (λ ())))
                 (hb (suc zero)))
          u₁-k₁))))

  -- The remaining positions, with carry in carry₁.

  inner-values :
    (∀ j → run (steps (innerᶠ L)) u₂ (wire L (rcarry , suc (suc j))) ≡
           carry (λ i → a (suc i)) (λ i → b (suc i)) c′ j) ×
    (∀ i → run (steps (innerᶠ L)) u₂ (wire L (ranc , suc (suc i))) ≡
           sumbit (λ i → a (suc i)) (λ i → b (suc i)) c′ (suc i))
  inner-values =
    steps-values (innerᶠ L) u₂ (λ i → a (suc i)) (λ i → b (suc i)) c′
      (λ i → trans (u₂-u (ra , suc i) (λ ()) (λ ())) (ha (suc i)))
      (λ i → trans (u₂-u (rb , suc i) (λ ()) (λ ())) (hb (suc i)))
      u₂-k₁
      (λ j → trans (u₂-u (rcarry , suc (suc j)) (λ ()) (λ ())) (hk (suc j)))
      (λ i → trans (u₂-u (ranc , suc (suc i)) (λ ()) (λ ())) (hs (suc i)))

  -- The remaining positions write neither carry₁ nor anc₁.

  away : (v : Line (suc m)) → (∀ j → (rcarry , suc (suc j)) ≢ v) →
         (∀ i → (ranc , suc (suc i)) ≢ v) →
         run (steps (innerᶠ L)) u₂ (wire L v) ≡ u₂ (wire L v)
  away v p q = steps-frame (innerᶠ L) u₂ (wire L v)
                 (λ j → distinct L _ v (p j)) (λ i → distinct L _ v (q i))

  carries : ∀ j → run (steps L) u (wire L (rcarry , suc j)) ≡ carry a b c j
  carries zero    =
    trans (run-++ᵂ (step L) (steps (innerᶠ L)) u k₁)
    (trans (away (rcarry , suc zero) (λ j ()) (λ i ())) u₂-k₁)
  carries (suc j) =
    trans (run-++ᵂ (step L) (steps (innerᶠ L)) u _) (proj₁ inner-values j)

  sums : ∀ i → run (steps L) u (wire L (ranc , suc i)) ≡ sumbit a b c (suc i)
  sums zero    =
    trans (run-++ᵂ (step L) (steps (innerᶠ L)) u s₁)
    (trans (away (ranc , suc zero) (λ j ()) (λ i ())) u₂-s₁)
  sums (suc i) =
    trans (run-++ᵂ (step L) (steps (innerᶠ L)) u _) (proj₂ inner-values i)

-- The inputs the netlist is for: its ancillas, anc and carry, read 0.

Blankᶠ : Layout (Line m) N → Bits N → Set
Blankᶠ L x = (∀ i → x (wire L (ranc , i)) ≡ false) ×
             (∀ i → x (wire L (rcarry , i)) ≡ false)

-- The input registers as bit vectors.

abits bbits : Layout (Line m) N → Bits N → Fin (suc m) → Bool
abits L x i = x (wire L (ra , i))
bbits L x i = x (wire L (rb , i))

-- compute writes no wire but anc and carry ...

compute-frame : (L : Layout (Line m) N) (u : Bits N) (w : Fin N) →
                (∀ i → wire L (ranc , i) ≢ w) →
                (∀ i → wire L (rcarry , i) ≢ w) →
                run (compute L) u w ≡ u w
compute-frame L u w hs hk =
  trans (run-++ᵂ (sum₀ L) (steps L) u w)
  (trans (steps-frame L (run (sum₀ L) u) w (λ j → hk (suc j))
                      (λ i → hs (suc i)))
         (sum₀ᶠ-there (distinct L (ra , zero) (ranc , zero) (λ ()))
                      (distinct L (rb , zero) (ranc , zero) (λ ())) u w
                      (λ e → hs zero (sym e))))

-- ... where, from a blank input, it writes the sum bits of a + b into
-- anc and the carries into carry₁ … carry_m.

compute-values :
  (L : Layout (Line m) N) (x : Bits N) → Blankᶠ L x →
  (∀ i → run (compute L) x (wire L (ranc , i)) ≡
         sumbit (abits L x) (bbits L x) false i) ×
  (∀ j → run (compute L) x (wire L (rcarry , suc j)) ≡
         carry (abits L x) (bbits L x) false j)
compute-values {m} {N} L x (bs , bk) = sums , carries
  where
  u₀ : Bits N
  u₀ = run (sum₀ L) x

  s₀ : Fin N
  s₀ = wire L (ranc , zero)

  u₀-off : ∀ w → w ≢ s₀ → u₀ w ≡ x w
  u₀-off = sum₀ᶠ-there (distinct L (ra , zero) (ranc , zero) (λ ()))
                       (distinct L (rb , zero) (ranc , zero) (λ ())) x

  u₀-u : (v : Line m) → v ≢ (ranc , zero) → u₀ (wire L v) ≡ x (wire L v)
  u₀-u v p = u₀-off _ (distinct L v _ p)

  u₀-s₀ : u₀ s₀ ≡ sumbit (abits L x) (bbits L x) false zero
  u₀-s₀ =
    trans (sum₀ᶠ-here (distinct L (ra , zero) (ranc , zero) (λ ()))
                      (distinct L (rb , zero) (ranc , zero) (λ ())) x)
    (trans (cong (_xor (abits L x zero xor bbits L x zero)) (bs zero))
           (cong (abits L x zero xor_)
                 (sym (xor-identityʳ (bbits L x zero)))))

  values :
    (∀ j → run (steps L) u₀ (wire L (rcarry , suc j)) ≡
           carry (abits L x) (bbits L x) false j) ×
    (∀ i → run (steps L) u₀ (wire L (ranc , suc i)) ≡
           sumbit (abits L x) (bbits L x) false (suc i))
  values = steps-values L u₀ (abits L x) (bbits L x) false
             (λ i → u₀-u (ra , i) (λ ())) (λ i → u₀-u (rb , i) (λ ()))
             (trans (u₀-u (rcarry , zero) (λ ())) (bk zero))
             (λ j → trans (u₀-u (rcarry , suc j) (λ ())) (bk (suc j)))
             (λ i → trans (u₀-u (ranc , suc i) (λ ())) (bs (suc i)))

  sums : ∀ i → run (compute L) x (wire L (ranc , i)) ≡
               sumbit (abits L x) (bbits L x) false i
  sums zero    =
    trans (run-++ᵂ (sum₀ L) (steps L) x s₀)
    (trans (steps-frame L u₀ s₀
              (λ j → distinct L (rcarry , suc j) (ranc , zero) (λ ()))
              (λ i → distinct L (ranc , suc i) (ranc , zero) (λ ())))
           u₀-s₀)
  sums (suc i) =
    trans (run-++ᵂ (sum₀ L) (steps L) x _) (proj₂ values i)

  carries : ∀ j → run (compute L) x (wire L (rcarry , suc j)) ≡
                  carry (abits L x) (bbits L x) false j
  carries j = trans (run-++ᵂ (sum₀ L) (steps L) x _) (proj₁ values j)

-- compute lies within the wires other than the output.

private
  steps-within : (L : Layout (Line m) N) (Q : Fin N → Set) →
                 (∀ r i → r ≢ rc → Q (wire L (r , i))) →
                 All (Within Q) (steps L)
  steps-within {zero}  L Q hQ = []
  steps-within {suc m} L Q hQ =
    ++⁺ (++⁺ ((qb₀ , qk₀) ∷ (qa₀ , qk₀ , qk₁) ∷ (qb₀ , qk₀) ∷
              (qb₀ , qk₀ , qk₁) ∷ [])
             ((hQ ra (suc zero) (λ ()) , qs₁) ∷
              (hQ rb (suc zero) (λ ()) , qs₁) ∷ (qk₁ , qs₁) ∷ []))
        (steps-within (innerᶠ L) Q (λ r i p → hQ r (suc i) p))
    where
    qa₀ : Q (wire L (ra , zero))
    qa₀ = hQ ra zero (λ ())

    qb₀ : Q (wire L (rb , zero))
    qb₀ = hQ rb zero (λ ())

    qk₀ : Q (wire L (rcarry , zero))
    qk₀ = hQ rcarry zero (λ ())

    qk₁ : Q (wire L (rcarry , suc zero))
    qk₁ = hQ rcarry (suc zero) (λ ())

    qs₁ : Q (wire L (ranc , suc zero))
    qs₁ = hQ ranc (suc zero) (λ ())

compute-within : (L : Layout (Line m) N) (Q : Fin N → Set) →
                 (∀ r i → r ≢ rc → Q (wire L (r , i))) →
                 All (Within Q) (compute L)
compute-within L Q hQ =
  ++⁺ ((hQ ra zero (λ ()) , hQ ranc zero (λ ())) ∷
       (hQ rb zero (λ ()) , hQ ranc zero (λ ())) ∷ [])
      (steps-within L Q hQ)


------------------------------------------------------------------------
-- The copy

-- It writes no wire but the output ...

copyᶠ-frame : (L : Layout (Line m) N) (u : Bits N) (w : Fin N) →
              (∀ i → wire L (rc , i) ≢ w) → run (copyᶠ L) u w ≡ u w
copyᶠ-frame {zero}  L u w h = ⟪⟫-there (copy₀ᶠ L) u (λ e → h zero (sym e))
copyᶠ-frame {suc m} L u w h =
  trans (copyᶠ-frame (innerᶠ L) (⟪ copy₀ᶠ L ⟫ u) w (λ i → h (suc i)))
        (⟪⟫-there (copy₀ᶠ L) u (λ e → h zero (sym e)))

-- ... where it xors the sum bits in.

copyᶠ-values : (L : Layout (Line m) N) (u : Bits N) →
               ∀ i → run (copyᶠ L) u (wire L (rc , i)) ≡
                     u (wire L (rc , i)) xor u (wire L (ranc , i))
copyᶠ-values {zero}  L u zero    = ⟪⟫-here (copy₀ᶠ L) u
copyᶠ-values {suc m} L u zero    =
  trans (copyᶠ-frame (innerᶠ L) (⟪ copy₀ᶠ L ⟫ u) (wire L (rc , zero))
                     (λ i → distinct L (rc , suc i) (rc , zero) (λ ())))
        (⟪⟫-here (copy₀ᶠ L) u)
copyᶠ-values {suc m} L u (suc i) =
  trans (copyᶠ-values (innerᶠ L) (⟪ copy₀ᶠ L ⟫ u) i)
        (cong₂ _xor_ (off (rc , suc i) (λ ())) (off (ranc , suc i) (λ ())))
  where
  off : (v : Line (suc m)) → v ≢ (rc , zero) →
        ⟪ copy₀ᶠ L ⟫ u (wire L v) ≡ u (wire L v)
  off v p = ⟪⟫-there (copy₀ᶠ L) u (distinct L v (rc , zero) p)


------------------------------------------------------------------------
-- The adder

-- The wires other than the output.

Workᶠ : Layout (Line m) N → Fin N → Set
Workᶠ L w = ∀ i → wire L (rc , i) ≢ w

module _ (L : Layout (Line m) N) where

  private
    work : ∀ r i → r ≢ rc → Workᶠ L (wire L (r , i))
    work r i p i′ e = p (sym (cong proj₁ (wire-inj L (rc , i′) (r , i) e)))

    within : All (Within (Workᶠ L)) (compute L)
    within = compute-within L (Workᶠ L) work

  -- Every wire but the output ends as it began, on every input.

  carryRipple-work : (x : Bits N) (w : Fin N) → Workᶠ L w →
                     run (carryRipple L) x w ≡ x w
  carryRipple-work x w q =
    bennett-work (Workᶠ L) (compute L) (copyᶠ L) within
                 (λ u w′ q′ → copyᶠ-frame L u w′ q′) x w q

  -- In particular the ancillas are restored.

  carryRipple-clean : (x : Bits N) → Blankᶠ L x →
                      Blankᶠ L (run (carryRipple L) x)
  carryRipple-clean x (bs , bk) =
    (λ i → trans (carryRipple-work x _ (work ranc i (λ ()))) (bs i)) ,
    (λ i → trans (carryRipple-work x _ (work rcarry i (λ ()))) (bk i))

  -- On a blank input the output gains the n sum bits of a + b.

  carryRipple-out : (x : Bits N) → Blankᶠ L x →
                    ∀ i → run (carryRipple L) x (wire L (rc , i)) ≡
                          x (wire L (rc , i)) xor
                          sumbit (abits L x) (bbits L x) false i
  carryRipple-out x bl i =
    trans (bennett-out (Workᶠ L) (compute L) (copyᶠ L) within x
                       (wire L (rc , i)) (λ q → q i refl))
    (trans (copyᶠ-values L (run (compute L) x) i)
           (cong₂ _xor_
             (compute-frame L x (wire L (rc , i))
               (λ i′ → distinct L (ranc , i′) (rc , i) (λ ()))
               (λ i′ → distinct L (rcarry , i′) (rc , i) (λ ())))
             (proj₁ (compute-values L x bl) i)))

  -- So from c = 0 it reads (a + b) mod 2^n: the carry out is lost.

  carryRipple-value : (x : Bits N) → Blankᶠ L x →
                      (∀ i → x (wire L (rc , i)) ≡ false) →
                      val (λ i → run (carryRipple L) x (wire L (rc , i))) ≡
                      _%_ (val (abits L x) + val (bbits L x)) (2 ^ suc m)
                          {{m^n≢0 2 (suc m)}}
  carryRipple-value x bl c0 =
    trans (val-cong (λ i → trans (carryRipple-out x bl i)
                                 (cong (_xor sumbit (abits L x) (bbits L x)
                                                    false i)
                                       (c0 i))))
    (trans (sumbit-mod (abits L x) (bbits L x) false)
           (cong (λ v → _%_ v (2 ^ suc m) {{m^n≢0 2 (suc m)}})
                 (+-identityʳ (val (abits L x) + val (bbits L x)))))

  -- As a Boolean function: the bit a wire gains is found by searching
  -- the output register for it.

  outᶠ? : (w : Fin N) → Dec (∃ λ i → wire L (rc , i) ≡ w)
  outᶠ? w = Fin.any? (λ i → wire L (rc , i) Fin.≟ w)

  gainᶠ : (x : Bits N) (w : Fin N) → Dec (∃ λ i → wire L (rc , i) ≡ w) →
          Bool
  gainᶠ x w (yes (i , _)) = sumbit (abits L x) (bbits L x) false i
  gainᶠ x w (no _)        = false

  additionᶠ : Bits N → Bits N
  additionᶠ x w = x w xor gainᶠ x w (outᶠ? w)

  -- What it does, independently of the search.

  additionᶠ-out : (x : Bits N) →
                  ∀ i → additionᶠ x (wire L (rc , i)) ≡
                        x (wire L (rc , i)) xor
                        sumbit (abits L x) (bbits L x) false i
  additionᶠ-out x i =
    cong (x (wire L (rc , i)) xor_) (go (outᶠ? (wire L (rc , i))))
    where
    go : (d : Dec (∃ λ i′ → wire L (rc , i′) ≡ wire L (rc , i))) →
         gainᶠ x (wire L (rc , i)) d ≡ sumbit (abits L x) (bbits L x) false i
    go (yes (i′ , e)) = cong (sumbit (abits L x) (bbits L x) false)
                             (cong proj₂ (wire-inj L (rc , i′) (rc , i) e))
    go (no ¬o)        = ⊥-elim (¬o (i , refl))

  additionᶠ-work : (x : Bits N) (w : Fin N) → Workᶠ L w → additionᶠ x w ≡ x w
  additionᶠ-work x w q = go (outᶠ? w)
    where
    go : (d : Dec (∃ λ i → wire L (rc , i) ≡ w)) → x w xor gainᶠ x w d ≡ x w
    go (yes (i , e)) = ⊥-elim (q i e)
    go (no _)        = xor-identityʳ (x w)

  -- The netlist computes it on blank inputs.

  carryRipple-computes : (x : Bits N) → Blankᶠ L x →
                         ∀ w → run (carryRipple L) x w ≡ additionᶠ x w
  carryRipple-computes x bl w = go (outᶠ? w)
    where
    go : (d : Dec (∃ λ i → wire L (rc , i) ≡ w)) →
         run (carryRipple L) x w ≡ x w xor gainᶠ x w d
    go (yes (i , e)) =
      subst (λ v → run (carryRipple L) x v ≡
                   x v xor sumbit (abits L x) (bbits L x) false i)
            e (carryRipple-out x bl i)
    go (no ¬o) = trans (carryRipple-work x w (λ i e → ¬o (i , e)))
                       (sym (xor-identityʳ (x w)))


------------------------------------------------------------------------
-- Resources

-- A count of the netlist's gates is twice compute's plus the copy's.

carryRipple-count : (f : Gate N → ℕ) (L : Layout (Line m) N) →
                    count f (carryRipple L) ≡
                    count f (compute L) +
                    (count f (copyᶠ L) + count f (compute L))
carryRipple-count f L =
  trans (count-++ f (compute L) (copyᶠ L ++ reverse (compute L)))
        (cong (count f (compute L) +_)
              (trans (count-++ f (copyᶠ L) (reverse (compute L)))
                     (cong (count f (copyᶠ L) +_)
                           (count-reverse f (compute L)))))

-- Each step has two Toffoli gates and five CNOTs; the first sum bit two
-- CNOTs; the copy one CNOT per bit.

private
  steps-tof : (L : Layout (Line m) N) → toffolis (steps L) ≡ 2 * m
  steps-tof {zero}  L = refl
  steps-tof {suc m} L =
    trans (count-++ is-ccx (step L) (steps (innerᶠ L)))
    (trans (cong (2 +_) (steps-tof (innerᶠ L)))
           (solve 1 (λ m → con 2 :+ con 2 :* m := con 2 :* (con 1 :+ m))
                  refl m))

  steps-cx : (L : Layout (Line m) N) → cnots (steps L) ≡ 5 * m
  steps-cx {zero}  L = refl
  steps-cx {suc m} L =
    trans (count-++ is-cx (step L) (steps (innerᶠ L)))
    (trans (cong (5 +_) (steps-cx (innerᶠ L)))
           (solve 1 (λ m → con 5 :+ con 5 :* m := con 5 :* (con 1 :+ m))
                  refl m))

  compute-tof : (L : Layout (Line m) N) → toffolis (compute L) ≡ 2 * m
  compute-tof L = trans (count-++ is-ccx (sum₀ L) (steps L)) (steps-tof L)

  compute-cx : (L : Layout (Line m) N) → cnots (compute L) ≡ 2 + 5 * m
  compute-cx L =
    trans (count-++ is-cx (sum₀ L) (steps L)) (cong (2 +_) (steps-cx L))

  copy-tof : (L : Layout (Line m) N) → toffolis (copyᶠ L) ≡ 0
  copy-tof {zero}  L = refl
  copy-tof {suc m} L = copy-tof (innerᶠ L)

  copy-cx : (L : Layout (Line m) N) → cnots (copyᶠ L) ≡ suc m
  copy-cx {zero}  L = refl
  copy-cx {suc m} L = cong suc (copy-cx (innerᶠ L))

-- For every n = m + 1 ≥ 1: 4(n − 1) Toffoli gates and 11n − 6 CNOTs.

carryRipple-toffolis : (L : Layout (Line m) N) →
                       toffolis (carryRipple L) ≡ 4 * m
carryRipple-toffolis {m} L =
  trans (carryRipple-count is-ccx L)
  (trans (cong₂ (λ t c → t + (c + t)) (compute-tof L) (copy-tof L))
         (solve 1 (λ m → con 2 :* m :+ (con 0 :+ con 2 :* m) := con 4 :* m)
                refl m))

carryRipple-cnots : (L : Layout (Line m) N) →
                    cnots (carryRipple L) ≡ 11 * suc m ∸ 6
carryRipple-cnots {m} L =
  trans (carryRipple-count is-cx L)
  (trans (cong₂ (λ t c → t + (c + t)) (compute-cx L) (copy-cx L))
  (trans (solve 1 (λ m → (con 2 :+ con 5 :* m) :+ ((con 1 :+ m)
                         :+ (con 2 :+ con 5 :* m))
                         := con 5 :+ con 11 :* m)
                refl m)
         (sym (cong (_∸ 6) (solve 1 (λ m → con 11 :* (con 1 :+ m)
                                           := con 6 :+ (con 5 :+ con 11 :* m))
                                  refl m)))))


------------------------------------------------------------------------
-- The tool's layout

-- Register r's bit i on wire n·r + i: a, b, c, anc, carry in that
-- order, as the tool's verifyOOPAdder lists them.

regᶠ : Reg → Fin 5
regᶠ ra     = zero
regᶠ rb     = suc zero
regᶠ rc     = suc (suc zero)
regᶠ ranc   = suc (suc (suc zero))
regᶠ rcarry = suc (suc (suc (suc zero)))

private
  unreg : Fin 5 → Reg
  unreg zero                          = ra
  unreg (suc zero)                    = rb
  unreg (suc (suc zero))              = rc
  unreg (suc (suc (suc zero)))        = ranc
  unreg (suc (suc (suc (suc zero))))  = rcarry

  unreg-reg : ∀ r → unreg (regᶠ r) ≡ r
  unreg-reg ra     = refl
  unreg-reg rb     = refl
  unreg-reg rc     = refl
  unreg-reg ranc   = refl
  unreg-reg rcarry = refl

  regᶠ-injective : ∀ r r′ → regᶠ r ≡ regᶠ r′ → r ≡ r′
  regᶠ-injective r r′ e =
    trans (sym (unreg-reg r)) (trans (cong unreg e) (unreg-reg r′))

placeᶠ : Line m → Fin (5 * suc m)
placeᶠ (r , i) = combine (regᶠ r) i

standardᶠ : (m : ℕ) → Layout (Line m) (5 * suc m)
standardᶠ m = record
  { wire     = placeᶠ
  ; wire-inj = inj
  }
  where
  inj : (u v : Line m) → placeᶠ u ≡ placeᶠ v → u ≡ v
  inj (r , i) (r′ , i′) e =
    cong₂ _,_
      (regᶠ-injective r r′
         (proj₁ (Fin.combine-injective (regᶠ r) i (regᶠ r′) i′ e)))
      (proj₂ (Fin.combine-injective (regᶠ r) i (regᶠ r′) i′ e))

standardᶠ-position : ∀ m r (i : Fin (suc m)) →
                     toℕ (wire (standardᶠ m) (r , i)) ≡
                     suc m * toℕ (regᶠ r) + toℕ i
standardᶠ-position m r i = Fin.toℕ-combine (regᶠ r) i

-- Table 2's Adder8 and Adder16: 40 and 80 qubits, 28 and 60 Toffoli
-- gates, 82 and 170 CNOTs.

table-2-Adder8ᶠ :
  (5 * 8 ≡ 40) × (toffolis (carryRipple (standardᶠ 7)) ≡ 28) ×
  (cnots (carryRipple (standardᶠ 7)) ≡ 82)
table-2-Adder8ᶠ =
  refl , carryRipple-toffolis (standardᶠ 7) , carryRipple-cnots (standardᶠ 7)

table-2-Adder16ᶠ :
  (5 * 16 ≡ 80) × (toffolis (carryRipple (standardᶠ 15)) ≡ 60) ×
  (cnots (carryRipple (standardᶠ 15)) ≡ 170)
table-2-Adder16ᶠ =
  refl , carryRipple-toffolis (standardᶠ 15) ,
  carryRipple-cnots (standardᶠ 15)


------------------------------------------------------------------------
-- Cross-checks

-- The netlist for n = 2 on the tool's ten wires: a₀ a₁ = 0 1,
-- b₀ b₁ = 2 3, c₀ c₁ = 4 5, anc₀ anc₁ = 6 7, carry₀ carry₁ = 8 9.
-- compute (anc₀ ⊕= a₀, b₀; maj a₀ b₀ carry₀ carry₁; plus a₁ b₁ carry₁
-- anc₁), copy (c₀ ⊕= anc₀, c₁ ⊕= anc₁), compute reversed: the tool's
-- list for n = 2, 4 Toffoli gates and 16 CNOTs.

netlistᶠ-2 :
  map gate-wires (carryRipple (standardᶠ 1)) ≡
  (0 ∷ 6 ∷ []) ∷ (2 ∷ 6 ∷ []) ∷
  (2 ∷ 8 ∷ []) ∷ (0 ∷ 8 ∷ 9 ∷ []) ∷ (2 ∷ 8 ∷ []) ∷ (2 ∷ 8 ∷ 9 ∷ []) ∷
  (1 ∷ 7 ∷ []) ∷ (3 ∷ 7 ∷ []) ∷ (9 ∷ 7 ∷ []) ∷
  (6 ∷ 4 ∷ []) ∷ (7 ∷ 5 ∷ []) ∷
  (9 ∷ 7 ∷ []) ∷ (3 ∷ 7 ∷ []) ∷ (1 ∷ 7 ∷ []) ∷
  (2 ∷ 8 ∷ 9 ∷ []) ∷ (2 ∷ 8 ∷ []) ∷ (0 ∷ 8 ∷ 9 ∷ []) ∷ (2 ∷ 8 ∷ []) ∷
  (2 ∷ 6 ∷ []) ∷ (0 ∷ 6 ∷ []) ∷ []
netlistᶠ-2 = refl

-- Run at n = 2: 1 + 1 = 2 (a₀ = b₀ = 1: c₁ = 1), and 3 + 1 = 0 modulo 4
-- (a₀ = a₁ = b₀ = 1: c stays 0, the carry out lost -- where
-- PathSum.Adder.Ripple's adder sets its third output bit); every
-- other wire ends as it began.

sum-1+1ᶠ :
  map (run (carryRipple (standardᶠ 1)) (λ w → (toℕ w ≡ᵇ 0) ∨ (toℕ w ≡ᵇ 2)))
      (allFin 10) ≡
  true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷
  false ∷ []
sum-1+1ᶠ = refl

sum-3+1ᶠ :
  map (run (carryRipple (standardᶠ 1)) (λ w → toℕ w <ᵇ 3)) (allFin 10) ≡
  true ∷ true ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷
  false ∷ []
sum-3+1ᶠ = refl
