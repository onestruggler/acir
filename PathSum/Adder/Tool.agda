------------------------------------------------------------------------
-- Presentations of groups
--
-- The paper's own adder over Clifford+T, verified for every n, and
-- table 2's Adder8 and Adder16 rows (Amy, QPL 2018, section 5.2)
--
-- The circuit the paper verified is the one its tool generates
-- (PathSum.Adder.CarryRipple: Feynman's carryRipple), each Toffoli gate
-- expanded by the tool's own Toffoli circuit (PathSum.Toffoli.Depth3:
-- Feynman's toffoli, sixteen gates) -- expand₃, carryRippleᶜ L on any
-- layout, CarryRippleᶜ m on the tool's (n = m + 1).  Its specification
-- is the tool's adderOOPSpec: the classical path-sum toolˢ L whose
-- output on the output wire cᵢ is the lift of cᵢ ⊕ sᵢ, sᵢ the i-th sum
-- bit of a + b built by symbolic addition (PathSum.Adder.Spec.sumbitᵉ:
-- the tool's cᵢ + carryᵢ + aᵢ + bᵢ, carry₀ = 0 and carryᵢ₊₁ the
-- majority), and whose other outputs are the inputs.  It computes
-- PathSum.Adder.CarryRipple's additionᶠ, |a⟩|b⟩|c⟩ ↦
-- |a⟩|b⟩|c ⊕ ((a + b) mod 2^n)⟩ (toolˢ-computes), so from an input
-- whose output register reads 0 it ends holding (a + b) mod 2^n
-- (toolˢ-value): the tool's adder and its specification drop the
-- carry out, the paper's |x⟩|y⟩|0⟩ ↦ |x⟩|y⟩|x + y⟩ read in an n-bit
-- output register, as its text's "n bit register to store the output"
-- has it.  The tool's ancillas, anc and carry, are constant-0 inputs
-- and outputs of its specification; here they are listed by ancᶠ,
-- and, as for PathSum.Adder's circuit,
--
--    ⟦ carryRippleᶜ L ⟧ ≋[ ancᶠ L ]₀* toolˢ L         (carryRippleᶜ-spec)
--
-- -- on the inputs whose ancillas read 0 the circuit is the
-- specification -- the ancillas are left clean (carryRippleᶜ-clean),
-- and with them read as the constant 0 on both sides, as the tool
-- reads them, the path-sums are ≋ (carryRippleᶜ-set0).  That is the
-- statement the tool checked for n = 8 and n = 16, here for every
-- n ≥ 1, by the same composition as PathSum.Adder: the tool's Toffoli
-- circuit computes the Toffoli gate (PathSum.Toffoli.Depth3.
-- tof₃-computes), so the expansion computes the netlist's function
-- (expand₃-computes), which is the addition modulo 2^n on blank inputs
-- (PathSum.Adder.CarryRipple.carryRipple-computes).
--
-- Resources, computed from the circuit: per Toffoli gate two path
-- variables, seven T gates and nine Clifford gates (two Hadamards and
-- seven CNOTs), per CNOT one Clifford gate (paths-expand₃,
-- tcount-expand₃, cliffords-expand₃); so, for every n ≥ 1, 8(n − 1)
-- path variables, 28(n − 1) T gates and 36(n − 1) + 11n − 6 Clifford
-- gates (Tool-paths, Tool-tcount, Tool-cliffords).  The qubits are
-- counted as the tool counts them, as the wires the circuit's gates
-- touch (PathSum.CRK.Qubits.qubits): every one of the 5n wires for
-- n ≥ 2 (Tool-qubits, through PathSum.Adder.Wires), but four for
-- n = 1, where no gate touches the carry-in wire carry₀ (Tool-qubits-1,
-- Tool-idle-1 -- the tool's own count is 4 there too).  At n = 8 and
-- n = 16 these are table 2's rows exactly (Adder8ᵀ, Adder16ᵀ):
--
--                 qubits   path vars   Clifford     T
--    Adder8          40        56         334      196
--    Adder16         80       120         710      420
--
-- One difference from the tool's circuit remains here, and it changes
-- no count: the tool uncomputes with the adjoint of its expanded
-- compute, which reverses each Toffoli circuit and swaps T and T†,
-- where the netlist here is uncomputed by the same Toffoli circuit (a
-- Toffoli gate is its own inverse, and the adjoint has the same gates
-- up to T ↔ T†).  PathSum.Adder.Feynman builds the tool's circuit
-- literally, with that adjoint -- Feynman's gate list, gate for gate
-- -- and proves the same theorems and rows for it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Adder.Tool (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; _xor_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (_+_; _*_; _∸_; _^_; _%_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; m^n≢0)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adder.Binary using (val; val-cong; sumbit; sumbit-mod)
open import PathSum.Adder.CarryRipple using
  (Reg; ra; rb; rc; ranc; rcarry; Line; carryRipple; Blankᶠ; abits; bbits;
   Workᶠ; outᶠ?; gainᶠ; additionᶠ; additionᶠ-out; additionᶠ-work;
   carryRipple-computes; carryRipple-toffolis; carryRipple-cnots;
   standardᶠ)
open import PathSum.Adder.Layout using (Layout; wire; wire-inj)
open import PathSum.Adder.Ripple using (distinct)
open import PathSum.Adder.Spec M₀ using (sumbitᵉ; ⟦sumbitᵉ⟧)
open import PathSum.Adder.Wires using (carryRipple-every)
open import PathSum.Ancillas M₀ using
  (Clean; set0ˢ; _≋[_]₀*_; ≋[]₀*⇔set0ˢ; computes⇒≋[]₀*; clean-ancillas)
open import PathSum.Base using (PathSum)
open import PathSum.Classical M₀ using
  (_computes_; classical; classical-computes; computes-≗; fun; fun-liftᵉ;
   outBit-none; ⟦++⟧-computes; ⟦[]⟧-computes; ⟦CNOT⟧-computes; none)
open import PathSum.Compose.CRK M₀ using (norm-++)
open import PathSum.CRK.Circuit M using (paths≡norm)
open import PathSum.CRK.Path M₀ using (CNOT; Circuit; ⟦_⟧; norm; paths)
open import PathSum.CRK.Qubits M₀ using
  (_∈ᶜ_; ∈ᶜ-++ˡ; ∈ᶜ-++ʳ; ∈ᶜ-touched; qubits; qubits-all)
open import PathSum.Cyclotomic M₀ using (_≐_; 0ᴬ)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Polynomial using (Poly; x[_])
open import PathSum.Polynomial.Boolean using
  (BExp; ⟦_⟧ᵉ; var; lit; _⊕ᵉ_; liftᵉ)
open import PathSum.QFT.Count M₀ using (cliffords; cliffords-++)
open import PathSum.Reversible using
  (Gate; ccx; cx; run; recover; toffolis; cnots)
open import PathSum.Reversible.Wires using (_∈ᴿ_)
open import PathSum.Toffoli.Depth3 M₀ using (tof₃; tof₃-computes)
open import PathSum.Toffoli.Netlist M₀ using (tcount; tcount-++)

private
  variable
    n m N : ℕ


------------------------------------------------------------------------
-- The expansion by the tool's Toffoli circuit

-- A Toffoli gate as the tool's sixteen-gate circuit, a CNOT as itself.

expand₃ : List (Gate n) → Circuit n
expand₃ []                       = []
expand₃ (ccx c₁ c₂ t p q r ∷ gs) =
  tof₃ c₁ c₂ t (recover p) (recover q) (recover r) ++ expand₃ gs
expand₃ (cx c t p ∷ gs)          = CNOT c t (recover p) ∷ expand₃ gs

-- It computes the netlist's Boolean function.

expand₃-computes : (gs : List (Gate n)) → ⟦ expand₃ gs ⟧ computes run gs
expand₃-computes []                       = ⟦[]⟧-computes
expand₃-computes (ccx c₁ c₂ t p q r ∷ gs) =
  ⟦++⟧-computes (tof₃ c₁ c₂ t (recover p) (recover q) (recover r))
                (expand₃ gs)
                (tof₃-computes c₁ c₂ t (recover p) (recover q) (recover r))
                (expand₃-computes gs)
expand₃-computes (cx c t p ∷ gs)          =
  ⟦++⟧-computes (CNOT c t (recover p) ∷ []) (expand₃ gs)
                (⟦CNOT⟧-computes c t (recover p)) (expand₃-computes gs)

-- Per Toffoli gate: two Hadamards (so two path variables), seven T or
-- T†, nine Clifford gates, sixteen gates; per CNOT one Clifford gate.

norm-expand₃ : (gs : List (Gate n)) → norm (expand₃ gs) ≡ toffolis gs * 2
norm-expand₃ []                       = refl
norm-expand₃ (ccx c₁ c₂ t p q r ∷ gs) =
  trans (norm-++ (tof₃ c₁ c₂ t (recover p) (recover q) (recover r))
                 (expand₃ gs))
        (cong (2 +_) (norm-expand₃ gs))
norm-expand₃ (cx c t p ∷ gs)          = norm-expand₃ gs

paths-expand₃ : (gs : List (Gate n)) → paths (expand₃ gs) ≡ toffolis gs * 2
paths-expand₃ gs = trans (paths≡norm (expand₃ gs)) (norm-expand₃ gs)

tcount-expand₃ : (gs : List (Gate n)) → tcount (expand₃ gs) ≡ toffolis gs * 7
tcount-expand₃ []                       = refl
tcount-expand₃ (ccx c₁ c₂ t p q r ∷ gs) =
  trans (tcount-++ (tof₃ c₁ c₂ t (recover p) (recover q) (recover r))
                   (expand₃ gs))
        (cong (7 +_) (tcount-expand₃ gs))
tcount-expand₃ (cx c t p ∷ gs)          = tcount-expand₃ gs

cliffords-expand₃ : (gs : List (Gate n)) →
                    cliffords (expand₃ gs) ≡ toffolis gs * 9 + cnots gs
cliffords-expand₃ []                       = refl
cliffords-expand₃ (ccx c₁ c₂ t p q r ∷ gs) =
  trans (cliffords-++ (tof₃ c₁ c₂ t (recover p) (recover q) (recover r))
                      (expand₃ gs))
        (cong (9 +_) (cliffords-expand₃ gs))
cliffords-expand₃ (cx c t p ∷ gs)          =
  trans (cong suc (cliffords-expand₃ gs))
        (sym (+-suc (toffolis gs * 9) (cnots gs)))

length-expand₃ : (gs : List (Gate n)) →
                 length (expand₃ gs) ≡ toffolis gs * 16 + cnots gs
length-expand₃ []                       = refl
length-expand₃ (ccx c₁ c₂ t p q r ∷ gs) =
  trans (length-++ (tof₃ c₁ c₂ t (recover p) (recover q) (recover r))
                   {expand₃ gs})
        (cong (16 +_) (length-expand₃ gs))
length-expand₃ (cx c t p ∷ gs)          =
  trans (cong suc (length-expand₃ gs))
        (sym (+-suc (toffolis gs * 16) (cnots gs)))

-- The tool's Toffoli circuit touches its three wires: t with its first
-- gate (H t), c₁ with its second (T c₁), c₂ with its third (T c₂) ...

∈ᶜ-tof₃ : (c₁ c₂ t : Fin n) (p : c₁ ≢ c₂) (q : c₁ ≢ t) (r : c₂ ≢ t)
          {u : Fin n} → u ∈ c₁ ∷ c₂ ∷ t ∷ [] → u ∈ᶜ tof₃ c₁ c₂ t p q r
∈ᶜ-tof₃ c₁ c₂ t p q r (here refl)                 = there (here (here refl))
∈ᶜ-tof₃ c₁ c₂ t p q r (there (here refl))         =
  there (there (here (here refl)))
∈ᶜ-tof₃ c₁ c₂ t p q r (there (there (here refl))) = here (here refl)

-- ... so the expansion touches every wire of the netlist (the wires
-- the tool counts as qubits: PathSum.CRK.Qubits).

∈ᶜ-expand₃ : (gs : List (Gate n)) {u : Fin n} → u ∈ᴿ gs → u ∈ᶜ expand₃ gs
∈ᶜ-expand₃ (ccx c₁ c₂ t p q r ∷ gs) (here m)  =
  ∈ᶜ-++ˡ (tof₃ c₁ c₂ t (recover p) (recover q) (recover r)) (expand₃ gs)
         (∈ᶜ-tof₃ c₁ c₂ t (recover p) (recover q) (recover r) m)
∈ᶜ-expand₃ (ccx c₁ c₂ t p q r ∷ gs) (there m) =
  ∈ᶜ-++ʳ (tof₃ c₁ c₂ t (recover p) (recover q) (recover r)) (expand₃ gs)
         (∈ᶜ-expand₃ gs m)
∈ᶜ-expand₃ (cx c t p ∷ gs)          (here m)  = here m
∈ᶜ-expand₃ (cx c t p ∷ gs)          (there m) = there (∈ᶜ-expand₃ gs m)


------------------------------------------------------------------------
-- The tool's specification

-- The input registers as symbolic vectors.

aᵉ bᵉ : Layout (Line m) N → Fin (suc m) → BExp N 0
aᵉ L i = var x[ wire L (ra , i) ]
bᵉ L i = var x[ wire L (rb , i) ]

-- On cᵢ, cᵢ ⊕ sᵢ; elsewhere the wire's input.

toolᵉ : (L : Layout (Line m) N) (w : Fin N) →
        Dec (∃ λ i → wire L (rc , i) ≡ w) → BExp N 0
toolᵉ L w (yes (i , _)) = var x[ w ] ⊕ᵉ sumbitᵉ (aᵉ L) (bᵉ L) (lit false) i
toolᵉ L w (no _)        = var x[ w ]

toolᵒ : Layout (Line m) N → Fin N → Poly N 0
toolᵒ L w = liftᵉ (toolᵉ L w (outᶠ? L w))

toolˢ : Layout (Line m) N → PathSum N 0 0
toolˢ L = classical (toolᵒ L)

-- It computes |a⟩|b⟩|c⟩ ↦ |a⟩|b⟩|c ⊕ ((a + b) mod 2^n)⟩, on every input.

fun-toolˢ : (L : Layout (Line m) N) (x : Assign N) →
            ∀ w → fun (toolᵒ L) x w ≡ additionᶠ L x w
fun-toolˢ L x w =
  trans (fun-liftᵉ (λ v → toolᵉ L v (outᶠ? L v)) x w) (go (outᶠ? L w))
  where
  go : (d : Dec (∃ λ i → wire L (rc , i) ≡ w)) →
       ⟦ toolᵉ L w d ⟧ᵉ x none ≡ x w xor gainᶠ L x w d
  go (yes (i , _)) =
    cong (x w xor_) (⟦sumbitᵉ⟧ (aᵉ L) (bᵉ L) (lit false) x none i)
  go (no _)        = sym (xor-identityʳ (x w))

toolˢ-computes : (L : Layout (Line m) N) → toolˢ L computes additionᶠ L
toolˢ-computes L =
  computes-≗ (toolˢ L) (fun-toolˢ L) (classical-computes (toolᵒ L))

-- So it adds modulo 2^n: from an input whose output register reads 0,
-- the output register ends holding (a + b) mod 2^n.

toolˢ-value : (L : Layout (Line m) N) (x : Assign N) →
              (∀ i → x (wire L (rc , i)) ≡ false) →
              val (λ i → fun (toolᵒ L) x (wire L (rc , i))) ≡
              _%_ (val (abits L x) + val (bbits L x)) (2 ^ suc m)
                  {{m^n≢0 2 (suc m)}}
toolˢ-value {m} L x c0 =
  trans (val-cong (λ i →
           trans (fun-toolˢ L x (wire L (rc , i)))
           (trans (additionᶠ-out L x i)
                  (cong (_xor sumbit (abits L x) (bbits L x) false i)
                        (c0 i)))))
  (trans (sumbit-mod (abits L x) (bbits L x) false)
         (cong (λ v → _%_ v (2 ^ suc m) {{m^n≢0 2 (suc m)}})
               (+-identityʳ (val (abits L x) + val (bbits L x)))))


------------------------------------------------------------------------
-- The ancillas

-- anc, then carry.

ancᶠ : Layout (Line m) N → Fin (suc m + suc m) → Fin N
ancᶠ {m} L j =
  [ (λ i → wire L (ranc , i)) , (λ i → wire L (rcarry , i)) ]′
    (splitAt (suc m) j)

-- An input is clean on them exactly when it is blank.

cleanᶠ⇔blankᶠ : (L : Layout (Line m) N) (x : Assign N) →
                Clean (ancᶠ L) x ⇔ Blankᶠ L x
cleanᶠ⇔blankᶠ {m} L x = mk⇔ to from
  where
  at : Fin (suc m) ⊎ Fin (suc m) → Fin _
  at = [ (λ i → wire L (ranc , i)) , (λ i → wire L (rcarry , i)) ]′

  to : Clean (ancᶠ L) x → Blankᶠ L x
  to cl =
    (λ i → subst (λ s → x (at s) ≡ false)
                 (Fin.splitAt-↑ˡ (suc m) i (suc m)) (cl (i ↑ˡ suc m))) ,
    (λ i → subst (λ s → x (at s) ≡ false)
                 (Fin.splitAt-↑ʳ (suc m) (suc m) i) (cl (suc m ↑ʳ i)))

  from : Blankᶠ L x → Clean (ancᶠ L) x
  from (bs , bk) j = go (splitAt (suc m) j)
    where
    go : (s : Fin (suc m) ⊎ Fin (suc m)) → x (at s) ≡ false
    go (inj₁ i) = bs i
    go (inj₂ i) = bk i

-- They are not the output.

ancᶠ-work : (L : Layout (Line m) N) (j : Fin (suc m + suc m)) →
            Workᶠ L (ancᶠ L j)
ancᶠ-work {m} L j = go (splitAt (suc m) j)
  where
  go : (s : Fin (suc m) ⊎ Fin (suc m)) →
       Workᶠ L ([ (λ i → wire L (ranc , i)) , (λ i → wire L (rcarry , i)) ]′
                  s)
  go (inj₁ i) i′ = distinct L (rc , i′) (ranc , i) (λ ())
  go (inj₂ i) i′ = distinct L (rc , i′) (rcarry , i) (λ ())


------------------------------------------------------------------------
-- The theorem

-- The netlist, each Toffoli gate expanded by the tool's circuit.

carryRippleᶜ : Layout (Line m) N → Circuit N
carryRippleᶜ L = expand₃ (carryRipple L)

carryRippleᶜ-computes : (L : Layout (Line m) N) →
                        ⟦ carryRippleᶜ L ⟧ computes run (carryRipple L)
carryRippleᶜ-computes L = expand₃-computes (carryRipple L)

-- On the inputs whose ancillas read 0 it is the tool's specification.

carryRippleᶜ-spec : (L : Layout (Line m) N) →
                    ⟦ carryRippleᶜ L ⟧ ≋[ ancᶠ L ]₀* toolˢ L
carryRippleᶜ-spec L =
  computes⇒≋[]₀* ⟦ carryRippleᶜ L ⟧ (toolˢ L) (ancᶠ L)
    (carryRippleᶜ-computes L) (toolˢ-computes L)
    (λ x cl w →
       carryRipple-computes L x (Equivalence.to (cleanᶠ⇔blankᶠ L x) cl) w)

-- The ancillas are left clean.

carryRippleᶜ-clean : (L : Layout (Line m) N) → ∀ x z →
                     Clean (ancᶠ L) x → (j : Fin (suc m + suc m)) →
                     z (ancᶠ L j) ≡ true → amp ⟦ carryRippleᶜ L ⟧ x z ≐ 0ᴬ
carryRippleᶜ-clean L = clean-ancillas (ancᶠ L) (carryRippleᶜ-spec L) out0
  where
  out0 : ∀ x (y : Assign 0) → Clean (ancᶠ L) x →
         ∀ j → outBit (toolˢ L) x y (ancᶠ L j) ≡ false
  out0 x y cl j =
    trans (outBit-none (toolˢ L) x y (ancᶠ L j))
    (trans (fun-toolˢ L x (ancᶠ L j))
    (trans (additionᶠ-work L x (ancᶠ L j) (ancᶠ-work L j)) (cl j)))

-- With the ancillas read as the constant 0 on both sides, as the tool
-- reads them, the path-sums are equivalent.

carryRippleᶜ-set0 : (L : Layout (Line m) N) →
                    set0ˢ (ancᶠ L) ⟦ carryRippleᶜ L ⟧ ≋
                    set0ˢ (ancᶠ L) (toolˢ L)
carryRippleᶜ-set0 L =
  Equivalence.to (≋[]₀*⇔set0ˢ (ancᶠ L) ⟦ carryRippleᶜ L ⟧ (toolˢ L))
                 (carryRippleᶜ-spec L)


------------------------------------------------------------------------
-- The tool's layout, for every n ≥ 1

-- On 5n wires: a, b, c, anc, carry (n = m + 1).

CarryRippleᶜ : (m : ℕ) → Circuit (5 * suc m)
CarryRippleᶜ m = carryRippleᶜ (standardᶠ m)

Tool-spec : (m : ℕ) → ⟦ CarryRippleᶜ m ⟧ ≋[ ancᶠ (standardᶠ m) ]₀*
                        toolˢ (standardᶠ m)
Tool-spec m = carryRippleᶜ-spec (standardᶠ m)

Tool-clean : (m : ℕ) → ∀ x z → Clean (ancᶠ (standardᶠ m)) x →
             (j : Fin (suc m + suc m)) → z (ancᶠ (standardᶠ m) j) ≡ true →
             amp ⟦ CarryRippleᶜ m ⟧ x z ≐ 0ᴬ
Tool-clean m = carryRippleᶜ-clean (standardᶠ m)

Tool-set0 : (m : ℕ) →
            set0ˢ (ancᶠ (standardᶠ m)) ⟦ CarryRippleᶜ m ⟧ ≋
            set0ˢ (ancᶠ (standardᶠ m)) (toolˢ (standardᶠ m))
Tool-set0 m = carryRippleᶜ-set0 (standardᶠ m)

-- Its resources: 8(n − 1) path variables, 28(n − 1) T gates and
-- 36(n − 1) + 11n − 6 Clifford gates, for every n ≥ 1.

Tool-paths-gates : (m : ℕ) →
                   paths (CarryRippleᶜ m) ≡
                   toffolis (carryRipple (standardᶠ m)) * 2
Tool-paths-gates m = paths-expand₃ (carryRipple (standardᶠ m))

Tool-tcount-gates : (m : ℕ) →
                    tcount (CarryRippleᶜ m) ≡
                    toffolis (carryRipple (standardᶠ m)) * 7
Tool-tcount-gates m = tcount-expand₃ (carryRipple (standardᶠ m))

Tool-cliffords-gates : (m : ℕ) →
                       cliffords (CarryRippleᶜ m) ≡
                       toffolis (carryRipple (standardᶠ m)) * 9 +
                       cnots (carryRipple (standardᶠ m))
Tool-cliffords-gates m = cliffords-expand₃ (carryRipple (standardᶠ m))

Tool-paths : (m : ℕ) → paths (CarryRippleᶜ m) ≡ 4 * m * 2
Tool-paths m =
  trans (Tool-paths-gates m) (cong (_* 2) (carryRipple-toffolis (standardᶠ m)))

Tool-tcount : (m : ℕ) → tcount (CarryRippleᶜ m) ≡ 4 * m * 7
Tool-tcount m =
  trans (Tool-tcount-gates m) (cong (_* 7) (carryRipple-toffolis (standardᶠ m)))

Tool-cliffords : (m : ℕ) → cliffords (CarryRippleᶜ m) ≡
                 4 * m * 9 + (11 * suc m ∸ 6)
Tool-cliffords m =
  trans (Tool-cliffords-gates m)
        (cong₂ (λ t c → t * 9 + c) (carryRipple-toffolis (standardᶠ m))
                                   (carryRipple-cnots (standardᶠ m)))

-- Its qubits, counted as the tool counts them -- the wires its gates
-- touch (PathSum.CRK.Qubits.qubits) -- are all 5n wires for every
-- n ≥ 2 (m ≢ 0): every wire of the netlist is touched
-- (PathSum.Adder.Wires.carryRipple-every), and so by the expansion.

Tool-qubits : (m : ℕ) → m ≢ 0 → qubits (CarryRippleᶜ m) ≡ 5 * suc m
Tool-qubits m p =
  qubits-all (CarryRippleᶜ m)
    (λ u → ∈ᶜ-expand₃ (carryRipple (standardᶠ m)) (carryRipple-every m p u))

-- For n = 1 they are four: without a majority block nothing touches
-- the carry-in wire carry₀ -- as the tool's own count, 4, has it.

Tool-qubits-1 : qubits (CarryRippleᶜ 0) ≡ 4
Tool-qubits-1 = refl

Tool-idle-1 : ¬ (wire (standardᶠ 0) (rcarry , zero) ∈ᶜ CarryRippleᶜ 0)
Tool-idle-1 p = untouched (∈ᶜ-touched (CarryRippleᶜ 0) _ p)
  where
  untouched : false ≡ true → ⊥
  untouched ()

-- Table 2's Adder8 and Adder16, exactly: qubits, path variables,
-- Clifford gates, T gates, each counted from the circuit.  (The
-- circuits are never computed: these are the counts above at n = 8
-- and n = 16.)

Adder8ᵀ : (qubits (CarryRippleᶜ 7) ≡ 40) × (paths (CarryRippleᶜ 7) ≡ 56) ×
          (cliffords (CarryRippleᶜ 7) ≡ 334) × (tcount (CarryRippleᶜ 7) ≡ 196)
Adder8ᵀ =
  Tool-qubits 7 (λ ()) , Tool-paths 7 , Tool-cliffords 7 , Tool-tcount 7

Adder16ᵀ : (qubits (CarryRippleᶜ 15) ≡ 80) ×
           (paths (CarryRippleᶜ 15) ≡ 120) ×
           (cliffords (CarryRippleᶜ 15) ≡ 710) ×
           (tcount (CarryRippleᶜ 15) ≡ 420)
Adder16ᵀ =
  Tool-qubits 15 (λ ()) , Tool-paths 15 , Tool-cliffords 15 ,
  Tool-tcount 15
