------------------------------------------------------------------------
-- Presentations of groups
--
-- The paper's tool's hidden shift circuits, read along one path
--
-- PathSum.HiddenShift.Tool and ToolSymbolic build the hidden shift and
-- symbolic shift circuits exactly as the paper's tool, Feynman,
-- generates them (Amy, QPL 2018, section 5.2): the tool's own ccz
-- (PathSum.HiddenShift.ToolCCZ), its cz and Z, and X a primitive gate
-- (PathSum.CRK.WithX), so that they have exactly 3n path variables, as
-- in table 2.  To reduce their path-sums by the rules of figure 2
-- (PathSum.HiddenShift.ToolExists) only their values along each path
-- are needed, and this module computes them, layer by layer, without
-- ever computing a polynomial:
--
--  * The tool's ccz on a, b, c (RunsE-ccz) adds exactly ½ v_a v_b v_c
--    to the phase and leaves the wires as it found them.  Its CNOTs
--    share their work, so the wires a, b, c pass through the values
--    PathSum.Toffoli.Depth3 lists for the same network between its
--    Hadamards (PathSum.Toffoli.Gate's three-wire assignments w3), and
--    its seven T and T† add 2^(M-3) times a signed sum of those bits
--    that is 4 v_a v_b v_c, by cases (bracket).
--  * So a block of draws, and the oracles O_f and O_f̃ the tool builds
--    from them, add ½ times the sum of the drawn monomials (Runs-gᶜ,
--    Runs-Oᶠᵗ, Runs-Oᵈᵗ), as PathSum.HiddenShift.Runs's oracles do.
--  * The hidden shift circuit from |0⟩ (runs-HSᵗ), along the path whose
--    three Hadamard layers read y₁, y₂, y₃ (PathSum.HiddenShift.
--    ThreeLayers' lay₁, lay₂, lay₃): the X layers put y₁ ⊕ s and then
--    y₁ back on the wires and add nothing (PathSum.HiddenShift.TraceX's
--    Runsˣ-flips), so the phase is ½ hs-par, i.e. ½ (f(y₁ ⊕ s) + y₁·y₂
--    + f̃(y₂) + y₂·y₃), and the wires end at y₃.
--  * The symbolic shift circuit from data |0⟩ and shift register xs
--    (runs-SSᶜᵗ): the same with s the shift register, which the
--    CNOT layers add and take off again; the wires end at y₃ and xs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.ToolRuns (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Bool.Properties using (xor-identityʳ; xor-comm; xor-assoc)
open import Data.Fin.Base using (Fin; toℕ; opposite; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Nat.Base using (suc; _∸_) renaming (_+_ to _ℕ+_)
open import Data.Vec.Base using (toList)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

import Data.Fin.Properties as Fin
import Data.Integer.Solver as ℤS
import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-≔; ≔-comm; ≔-cong; ≔-self)
open import PathSum.CRK.Trace M₀ using
  (Stream; shift; trace-cong; conf≈; ≈φ; ≈v; norm-++)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Circuit M₀ using
  (fTerms; f̃Terms; onLeft; onRight; xyTerms; sum-f; sum-f̃)
open import PathSum.HiddenShift.Gates M₀ using
  (Term; mapTerm; sumᵇ; sumᵇ-++; sumᵇ-resp; oracle; upper; norm-upper)
open import PathSum.HiddenShift.Layers M₀ using (hadamards; norm-hadamards)
open import PathSum.HiddenShift.LayersX M₀ using
  (flipsˣ; norm-flipsˣ; norm-++ˣ)
open import PathSum.HiddenShift.Layout using (hs-par)
open import PathSum.HiddenShift.Runs M₀ using
  (Runs; RunsE; runsE; exact-φ; exact-v; RunsE-++; RunsE-exp; RunsE-out;
   RunsE⇒Runs; RunsE-R; RunsE-R†; RunsE-CNOT; Runs-[]; Runs-++;
   Runs-resp; Runs-upper; Runs-hadamards; Runs-oracle; Runs-cnots; hbits)
open import PathSum.HiddenShift.Symbolic M₀ using
  (norm-cnots; ⧺-cong₂)
open import PathSum.HiddenShift.ThreeLayers M₀ using (lay₁; lay₂; lay₃)
open import PathSum.HiddenShift.Tool M₀ using
  (Block; block; drawTerm; gTerms; blockᶜ; gᶜ; gˡ; gʳ; cTᶜ; Oᶠᵗ; Oᵈᵗ;
   norm-Oᶠᵗ; norm-Oᵈᵗ; hTˣ; HSᵗ; HSᵗ-layers)
open import PathSum.HiddenShift.ToolCCZ M₀ using (cczᶜ)
open import PathSum.HiddenShift.ToolSymbolic M₀ using
  (xTˢ; hTˢ; SSᶜᵗ; SSᶜᵗ-layers)
open import PathSum.HiddenShift.TraceX M₀ using
  (Runsˣ; Runsˣ-++; Runsˣ-embed; Runsˣ-flips; Runsˣ-resp)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; _⧺_; ⧺-↑ˡ; ⧺-↑ʳ; dot; dot-cong; dot-0ˡ; mm)
open import PathSum.Toffoli.Arith M₀ using (four-T)
open import PathSum.Toffoli.Gate M₀ using (module Wires)

private
  M : ℕ
  M = suc (suc (suc M₀))

import PathSum.CRK.Circuit
import PathSum.CRK.WithX

private
  module CRK = PathSum.CRK.Circuit M
  module Wˣ  = PathSum.CRK.WithX M₀

open CRK using (Gate; Circuit; norm; CNOT; R; R†)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)

private
  variable
    n m d : ℕ


------------------------------------------------------------------------
-- The tool's ccz along a path

-- The bits the CNOT network puts on the wires a, b, c holding α, β, γ
-- (PathSum.Toffoli.Depth3's, private there): b reads β₁ = β ⊕ α; c
-- reads γ₁ = γ ⊕ β₁, then γ₂ = γ₁ ⊕ β₁; a reads α₁ = α ⊕ γ₁,
-- α₂ = α₁ ⊕ β₁, α₃ = α₂ ⊕ γ₂; and b at the end β₂ = β₁ ⊕ α₃.

private
  β₁ᶠ : Bool → Bool → Bool
  β₁ᶠ α β = β xor α

  γ₁ᶠ α₁ᶠ α₂ᶠ γ₂ᶠ α₃ᶠ β₂ᶠ : Bool → Bool → Bool → Bool
  γ₁ᶠ α β γ = γ xor β₁ᶠ α β
  α₁ᶠ α β γ = α xor γ₁ᶠ α β γ
  α₂ᶠ α β γ = α₁ᶠ α β γ xor β₁ᶠ α β
  γ₂ᶠ α β γ = γ₁ᶠ α β γ xor β₁ᶠ α β
  α₃ᶠ α β γ = α₂ᶠ α β γ xor γ₂ᶠ α β γ
  β₂ᶠ α β γ = β₁ᶠ α β xor α₃ᶠ α β γ

  -- At the end the wires hold α, β, γ again.

  α₃-back : ∀ α β γ → α₃ᶠ α β γ ≡ α
  α₃-back false false false = refl
  α₃-back false false true  = refl
  α₃-back false true  false = refl
  α₃-back false true  true  = refl
  α₃-back true  false false = refl
  α₃-back true  false true  = refl
  α₃-back true  true  false = refl
  α₃-back true  true  true  = refl

  β₂-back : ∀ α β γ → β₂ᶠ α β γ ≡ β
  β₂-back false false false = refl
  β₂-back false false true  = refl
  β₂-back false true  false = refl
  β₂-back false true  true  = refl
  β₂-back true  false false = refl
  β₂-back true  false true  = refl
  β₂-back true  true  false = refl
  β₂-back true  true  true  = refl

  γ₂-back : ∀ α β γ → γ₂ᶠ α β γ ≡ γ
  γ₂-back false false false = refl
  γ₂-back false false true  = refl
  γ₂-back false true  false = refl
  γ₂-back false true  true  = refl
  γ₂-back true  false false = refl
  γ₂-back true  false true  = refl
  γ₂-back true  true  false = refl
  γ₂-back true  true  true  = refl

  -- The seven T and T† add 2^(M-3) times this signed sum of the bits
  -- they read, which is 4αβγ.

  bracket : ∀ α β γ →
    [ α ]ᶻ + ([ β ]ᶻ + ([ γ ]ᶻ + (- [ α₁ᶠ α β γ ]ᶻ + (- [ β₁ᶠ α β ]ᶻ +
      ([ γ₁ᶠ α β γ ]ᶻ + - [ α₂ᶠ α β γ ]ᶻ))))) ≡
    (+ 4) * [ α ∧ (β ∧ γ) ]ᶻ
  bracket false false false = refl
  bracket false false true  = refl
  bracket false true  false = refl
  bracket false true  true  = refl
  bracket true  false false = refl
  bracket true  false true  = refl
  bracket true  true  false = refl
  bracket true  true  true  = refl

  -- The phase the fourteen gates add, in the order they add it.

  T : ℤ
  T = pow (M ∸ 3)

  Δccz : Bool → Bool → Bool → ℤ
  Δccz α β γ =
    T * [ α ]ᶻ + (T * [ β ]ᶻ + (T * [ γ ]ᶻ + (0ℤ + (0ℤ + (0ℤ +
      (- (T * [ α₁ᶠ α β γ ]ᶻ) + (- (T * [ β₁ᶠ α β ]ᶻ) +
        (T * [ γ₁ᶠ α β γ ]ᶻ + (0ℤ + (- (T * [ α₂ᶠ α β γ ]ᶻ) +
          (0ℤ + (0ℤ + 0ℤ))))))))))))

  Δccz-½ : ∀ α β γ → Δccz α β γ ≡ ½ * [ α ∧ (β ∧ γ) ]ᶻ
  Δccz-½ α β γ =
    trans (shape T [ α ]ᶻ [ β ]ᶻ [ γ ]ᶻ [ α₁ᶠ α β γ ]ᶻ [ β₁ᶠ α β ]ᶻ
                 [ γ₁ᶠ α β γ ]ᶻ [ α₂ᶠ α β γ ]ᶻ)
      (trans (cong (T *_) (bracket α β γ)) (four-T [ α ∧ (β ∧ γ) ]ᶻ))
    where
    open ℤS.+-*-Solver using (solve; con; _:+_; _:*_; :-_; _:=_)

    shape : ∀ t A B C D E F G →
      t * A + (t * B + (t * C + (0ℤ + (0ℤ + (0ℤ + (- (t * D) +
        (- (t * E) + (t * F + (0ℤ + (- (t * G) + (0ℤ + (0ℤ + 0ℤ)))))))))))) ≡
      t * (A + (B + (C + (- D + (- E + (F + - G))))))
    shape = solve 8 (λ t A B C D E F G →
      t :* A :+ (t :* B :+ (t :* C :+ (con 0ℤ :+ (con 0ℤ :+ (con 0ℤ :+
        (:- (t :* D) :+ (:- (t :* E) :+ (t :* F :+ (con 0ℤ :+
          (:- (t :* G) :+ (con 0ℤ :+ (con 0ℤ :+ con 0ℤ)))))))))))) :=
      t :* (A :+ (B :+ (C :+ (:- D :+ (:- E :+ (F :+ :- G))))))) refl

  -- A circuit read from wires that agree with v reads as from v.

  RunsE-in : {C : Circuit n} {s : Stream} {u u′ v′ : Assign n} {Δ : ℤ} →
             (∀ w → u w ≡ u′ w) → RunsE C s u′ Δ v′ → RunsE C s u Δ v′
  RunsE-in {C = C} {s} h r = runsE
    (λ φ → trans (≈φ (e φ)) (exact-φ r φ))
    (λ φ w → trans (≈v (e φ) w) (exact-v r φ w))
    where
    e = λ φ → trace-cong C {s = s} {s′ = s} (λ _ → refl) (conf≈ refl h)

  -- One gate in front of a circuit.

  RunsE-∷ : {g : Gate n} {C : Circuit n} {s : Stream} {u u₁ u₂ : Assign n}
            {Δ₁ Δ₂ : ℤ} →
            RunsE (g ∷ []) (shift (norm C) s) u Δ₁ u₁ → RunsE C s u₁ Δ₂ u₂ →
            RunsE (g ∷ C) s u (Δ₁ + Δ₂) u₂
  RunsE-∷ {g = g} {C} = RunsE-++ (g ∷ []) C

module _ {n : ℕ} {a b c : Fin n} (p : a ≢ b) (q : a ≢ c) (r : b ≢ c)
         (v : Assign n) where

  open Wires p q r v

  private
    -- CNOTs onto a (PathSum.Toffoli.Depth3's, private there).

    w3-set-a : ∀ α β γ α′ u → (w3 α β γ [ a ≔ α′ ]) u ≡ w3 α′ β γ u
    w3-set-a α β γ α′ u =
      trans (≔-comm (v [ a ≔ α ] [ b ≔ β ]) γ α′ (λ e → q (sym e)) u)
            (≔-cong c γ (λ u′ →
               trans (≔-comm (v [ a ≔ α ]) β α′ (λ e → p (sym e)) u′)
                     (≔-cong b β (≔-≔ v a α α′) u′)) u)

    cnot-a : (ctl : Fin n) (α β γ val : Bool) → w3 α β γ ctl ≡ val →
             ∀ u → (w3 α β γ [ a ≔ w3 α β γ a xor w3 α β γ ctl ]) u ≡
                   w3 (α xor val) β γ u
    cnot-a ctl α β γ val eq u =
      trans (cong (λ z → (w3 α β γ [ a ≔ z ]) u)
                  (cong₂ _xor_ (w3-c₁ α β γ) eq))
            (w3-set-a α β γ (α xor val) u)

    -- The network's gates on the states w3 α β γ, each with its phase
    -- and the state it leaves.

    tA : ∀ α β γ {s : Stream} →
         RunsE (R 3 a ∷ []) s (w3 α β γ) (T * [ α ]ᶻ) (w3 α β γ)
    tA α β γ {s} = RunsE-exp (cong (λ z → T * [ z ]ᶻ) (w3-c₁ α β γ))
                             (RunsE-R 3 a s (w3 α β γ))

    tB : ∀ α β γ {s : Stream} →
         RunsE (R 3 b ∷ []) s (w3 α β γ) (T * [ β ]ᶻ) (w3 α β γ)
    tB α β γ {s} = RunsE-exp (cong (λ z → T * [ z ]ᶻ) (w3-c₂ α β γ))
                             (RunsE-R 3 b s (w3 α β γ))

    tC : ∀ α β γ {s : Stream} →
         RunsE (R 3 c ∷ []) s (w3 α β γ) (T * [ γ ]ᶻ) (w3 α β γ)
    tC α β γ {s} = RunsE-exp (cong (λ z → T * [ z ]ᶻ) (w3-t α β γ))
                             (RunsE-R 3 c s (w3 α β γ))

    tA† : ∀ α β γ {s : Stream} →
          RunsE (R† 3 a ∷ []) s (w3 α β γ) (- (T * [ α ]ᶻ)) (w3 α β γ)
    tA† α β γ {s} = RunsE-exp (cong (λ z → - (T * [ z ]ᶻ)) (w3-c₁ α β γ))
                              (RunsE-R† 3 a s (w3 α β γ))

    tB† : ∀ α β γ {s : Stream} →
          RunsE (R† 3 b ∷ []) s (w3 α β γ) (- (T * [ β ]ᶻ)) (w3 α β γ)
    tB† α β γ {s} = RunsE-exp (cong (λ z → - (T * [ z ]ᶻ)) (w3-c₂ α β γ))
                              (RunsE-R† 3 b s (w3 α β γ))

    cAB : ∀ α β γ {s : Stream} →
          RunsE (CNOT a b p ∷ []) s (w3 α β γ) 0ℤ (w3 α (β xor α) γ)
    cAB α β γ {s} = RunsE-out (cnot-c₂ α β γ) (RunsE-CNOT a b p s (w3 α β γ))

    cBC : ∀ α β γ {s : Stream} →
          RunsE (CNOT b c r ∷ []) s (w3 α β γ) 0ℤ (w3 α β (γ xor β))
    cBC α β γ {s} = RunsE-out (cnot-t b α β γ β (w3-c₂ α β γ))
                              (RunsE-CNOT b c r s (w3 α β γ))

    cCA : ∀ α β γ {s : Stream} →
          RunsE (CNOT c a (λ e → q (sym e)) ∷ []) s (w3 α β γ) 0ℤ
                (w3 (α xor γ) β γ)
    cCA α β γ {s} = RunsE-out (cnot-a c α β γ γ (w3-t α β γ))
                              (RunsE-CNOT c a (λ e → q (sym e)) s (w3 α β γ))

    cBA : ∀ α β γ {s : Stream} →
          RunsE (CNOT b a (λ e → p (sym e)) ∷ []) s (w3 α β γ) 0ℤ
                (w3 (α xor β) β γ)
    cBA α β γ {s} = RunsE-out (cnot-a b α β γ β (w3-c₂ α β γ))
                              (RunsE-CNOT b a (λ e → p (sym e)) s (w3 α β γ))

    -- The fourteen gates, from a, b, c holding α, β, γ.

    chain : ∀ α β γ (s : Stream) →
            RunsE (cczᶜ a b c p q r) s (w3 α β γ) (Δccz α β γ)
                  (w3 (α₃ᶠ α β γ) (β₂ᶠ α β γ) (γ₂ᶠ α β γ))
    chain α β γ s =
      RunsE-∷ (tA α β γ) (RunsE-∷ (tB α β γ) (RunsE-∷ (tC α β γ)
      (RunsE-∷ (cAB α β γ) (RunsE-∷ (cBC α β₁ γ) (RunsE-∷ (cCA α β₁ γ₁)
      (RunsE-∷ (tA† α₁ β₁ γ₁) (RunsE-∷ (tB† α₁ β₁ γ₁) (RunsE-∷ (tC α₁ β₁ γ₁)
      (RunsE-∷ (cBA α₁ β₁ γ₁) (RunsE-∷ (tA† α₂ β₁ γ₁)
      (RunsE-∷ (cBC α₂ β₁ γ₁) (RunsE-∷ (cCA α₂ β₁ γ₂)
               (cAB α₃ β₁ γ₂)))))))))))))
      where
      β₁ γ₁ α₁ α₂ γ₂ α₃ : Bool
      β₁ = β₁ᶠ α β
      γ₁ = γ₁ᶠ α β γ
      α₁ = α₁ᶠ α β γ
      α₂ = α₂ᶠ α β γ
      γ₂ = γ₂ᶠ α β γ
      α₃ = α₃ᶠ α β γ

    -- v is w3 of its own bits on a, b, c.

    w3-self : ∀ u → w3 (v a) (v b) (v c) u ≡ v u
    w3-self u = trans (sym (w3-x (v c) u)) (≔-self v c u)

  -- Along any path the tool's ccz adds exactly ½ v_a v_b v_c and leaves
  -- the wires alone.

  RunsE-ccz : ∀ (s : Stream) →
              RunsE (cczᶜ a b c p q r) s v (½ * [ v a ∧ (v b ∧ v c) ]ᶻ) v
  RunsE-ccz s =
    RunsE-in (λ u → sym (w3-self u))
      (RunsE-exp (Δccz-½ (v a) (v b) (v c))
        (RunsE-out back (chain (v a) (v b) (v c) s)))
    where
    back : ∀ u → w3 (α₃ᶠ (v a) (v b) (v c)) (β₂ᶠ (v a) (v b) (v c))
                    (γ₂ᶠ (v a) (v b) (v c)) u ≡ v u
    back u = trans
      (cong₂ (λ α β → w3 α β (γ₂ᶠ (v a) (v b) (v c)) u)
             (α₃-back (v a) (v b) (v c)) (β₂-back (v a) (v b) (v c)))
      (trans (cong (λ γ → w3 (v a) (v b) γ u) (γ₂-back (v a) (v b) (v c)))
             (w3-self u))


------------------------------------------------------------------------
-- The tool's oracles along a path

-- The draws on the wires ρ i add ½ times the sum of their monomials.

Runs-gᶜ : (ρ : Fin m → Fin n) (inj : ∀ {a b} → ρ a ≡ ρ b → a ≡ b)
          (Bs : List (Block d m)) (s : Stream) (v : Assign n) →
          Runs (gᶜ ρ inj Bs) s v (sumᵇ (map (mapTerm ρ inj) (gTerms Bs)) v) v
Runs-gᶜ ρ inj []                          s v = Runs-[] s v
Runs-gᶜ ρ inj (block a b c p q r ds ∷ Bs) s v =
  Runs-resp sum (λ _ → refl)
    (Runs-++ (blockᶜ ρ inj (block a b c p q r ds)) (gᶜ ρ inj Bs)
             {β₁ = ccz xor sumᵇ D v} {β₂ = sumᵇ G v}
      (Runs-++ (cczᶜ (ρ a) (ρ b) (ρ c) p′ q′ r′) (oracle D)
               {β₁ = ccz} {β₂ = sumᵇ D v}
        (RunsE⇒Runs {β = ccz} (RunsE-ccz p′ q′ r′ v _) refl)
        (Runs-oracle D _ v))
      (Runs-gᶜ ρ inj Bs s v))
  where
  p′ : ρ a ≢ ρ b
  p′ e = p (inj e)

  q′ : ρ a ≢ ρ c
  q′ e = q (inj e)

  r′ : ρ b ≢ ρ c
  r′ e = r (inj e)

  f : Term _ → Term _
  f = mapTerm ρ inj

  D G : List (Term _)
  D = map f (map drawTerm (toList ds))
  G = map f (gTerms Bs)

  ccz : Bool
  ccz = v (ρ a) ∧ (v (ρ b) ∧ v (ρ c))

  sum : (ccz xor sumᵇ D v) xor sumᵇ G v ≡
        sumᵇ (map f (gTerms (block a b c p q r ds ∷ Bs))) v
  sum = trans (xor-assoc (v (ρ a) ∧ (v (ρ b) ∧ v (ρ c))) (sumᵇ D v)
                         (sumᵇ G v))
    (cong ((v (ρ a) ∧ (v (ρ b) ∧ v (ρ c))) xor_)
          (sym (trans (cong (λ l → sumᵇ l v)
                            (map-++ f (map drawTerm (toList ds)) (gTerms Bs)))
                      (sumᵇ-++ D G v))))

-- O_f = g ++ cTrans adds ½ f, and O_f̃ = g′ ++ cTrans adds ½ f̃.

Runs-Oᶠᵗ : (Bs : List (Block d m)) (s : Stream) (v : Assign (m ℕ+ m)) →
           Runs (Oᶠᵗ Bs) s v (sumᵇ (fTerms (gTerms Bs)) v) v
Runs-Oᶠᵗ {m = m} Bs s v =
  Runs-resp (sym (sumᵇ-++ (onLeft (gTerms Bs)) (xyTerms m) v)) (λ _ → refl)
    (Runs-++ (gˡ Bs) (cTᶜ m)
      (Runs-gᶜ (λ i → i ↑ˡ m) (λ {a} {b} → Fin.↑ˡ-injective m a b) Bs _ v)
      (Runs-oracle (xyTerms m) s v))

Runs-Oᵈᵗ : (Bs : List (Block d m)) (s : Stream) (v : Assign (m ℕ+ m)) →
           Runs (Oᵈᵗ Bs) s v (sumᵇ (f̃Terms (gTerms Bs)) v) v
Runs-Oᵈᵗ {m = m} Bs s v =
  Runs-resp (trans (xor-comm (sumᵇ (onRight (gTerms Bs)) v)
                             (sumᵇ (xyTerms m) v))
                   (sym (sumᵇ-++ (xyTerms m) (onRight (gTerms Bs)) v)))
            (λ _ → refl)
    (Runs-++ (gʳ Bs) (cTᶜ m)
      (Runs-gᶜ (λ i → m ↑ʳ i) (λ {a} {b} → Fin.↑ʳ-injective m a b) Bs _ v)
      (Runs-oracle (xyTerms m) s v))


------------------------------------------------------------------------
-- Shared arithmetic of the two circuits

private
  -- The positions of the first and second layers' bits, once the
  -- layers between have no Hadamards.

  pos₁ : ∀ t {nx nh nd : ℕ} → nx ≡ 0 → nh ≡ n → nd ≡ 0 →
         (((t ℕ+ nx) ℕ+ nh) ℕ+ nd) ℕ+ nh ≡ n ℕ+ (n ℕ+ t)
  pos₁ {n} t refl refl refl =
    trans (cong (_ℕ+ n) (ℕ.+-identityʳ ((t ℕ+ 0) ℕ+ n)))
      (trans (cong (λ z → (z ℕ+ n) ℕ+ n) (ℕ.+-identityʳ t))
        (trans (ℕ.+-comm (t ℕ+ n) n) (cong (n ℕ+_) (ℕ.+-comm t n))))

  pos₂ : ∀ t {nh nd : ℕ} → nh ≡ n → nd ≡ 0 → (t ℕ+ nd) ℕ+ nh ≡ n ℕ+ t
  pos₂ {n} t refl refl =
    trans (cong (_ℕ+ n) (ℕ.+-identityʳ t)) (ℕ.+-comm t n)

  xor-back : ∀ a b → (a xor b) xor b ≡ a
  xor-back false false = refl
  xor-back false true  = refl
  xor-back true  false = refl
  xor-back true  true  = refl

  -- The parity the layers add is hs-par.

  β-hs : ∀ {m} (gs : List (Term m)) (sv y₁ y₂ y₃ : Assign (m ℕ+ m)) →
         (((dot (0ᵃ {m ℕ+ m}) y₁ xor
            (false xor (sumᵇ (fTerms gs) (y₁ ⊕ᵃ sv) xor false))) xor
           dot ((y₁ ⊕ᵃ sv) ⊕ᵃ sv) y₂) xor
          sumᵇ (f̃Terms gs) y₂) xor dot y₂ y₃ ≡
         hs-par (sumᵇ gs) sv y₁ y₂ y₃
  β-hs {m} gs sv y₁ y₂ y₃ = cong₂ _xor_
    (cong₂ _xor_
      (cong₂ _xor_ first
        (dot-cong (λ i → xor-back (y₁ i) (sv i)) (λ _ → refl)))
      (sum-f̃ gs y₂))
    refl
    where
    S : Bool
    S = sumᵇ (fTerms gs) (y₁ ⊕ᵃ sv)

    first : dot (0ᵃ {m ℕ+ m}) y₁ xor (false xor (S xor false)) ≡
            mm (sumᵇ gs) (y₁ ⊕ᵃ sv)
    first = trans (cong (_xor (false xor (S xor false))) (dot-0ˡ y₁))
                  (trans (xor-identityʳ S) (sum-f gs (y₁ ⊕ᵃ sv)))


------------------------------------------------------------------------
-- The hidden shift circuit along a path

-- From |0⟩, along the path whose layers read y₁, y₂, y₃: phase
-- ½ hs-par with the shift s, wires y₃.

module _ {m d : ℕ} (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) where

  private
    n′ : ℕ
    n′ = m ℕ+ m

    Hn Fx O′ D′ X′ : Wˣ.Circuit (m ℕ+ m)
    Hn = hTˣ m
    Fx = flipsˣ s
    O′ = map Wˣ.embed (Oᶠᵗ Bs)
    D′ = map Wˣ.embed (Oᵈᵗ Bs)
    X′ = Fx ++ (O′ ++ Fx)

    nH : Wˣ.norm Hn ≡ n′
    nH = trans (Wˣ.norm-embed (hadamards n′)) (norm-hadamards n′)

    nD : Wˣ.norm D′ ≡ 0
    nD = trans (Wˣ.norm-embed (Oᵈᵗ Bs)) (norm-Oᵈᵗ Bs)

    nX : Wˣ.norm X′ ≡ 0
    nX = trans (norm-++ˣ Fx (O′ ++ Fx))
      (cong₂ _ℕ+_ (norm-flipsˣ s)
        (trans (norm-++ˣ O′ Fx)
          (cong₂ _ℕ+_ (trans (Wˣ.norm-embed (Oᶠᵗ Bs)) (norm-Oᶠᵗ Bs))
                      (norm-flipsˣ s))))

    -- The streams the layers read: the last Hadamard layer the path's
    -- own, each earlier layer the stream past the later layers'
    -- Hadamards.

    s₁ s₂ s₃ sH : Stream → Stream
    s₁ st = shift (Wˣ.norm Hn) st
    s₂ st = shift (Wˣ.norm D′) (s₁ st)
    s₃ st = shift (Wˣ.norm Hn) (s₂ st)
    sH st = shift (Wˣ.norm X′) (s₃ st)

    h₁ : ∀ st w → hbits n′ (sH st) w ≡ lay₁ n′ st w
    h₁ st w = cong st (pos₁ (toℕ (opposite w)) nX nH nD)

    h₂ : ∀ st w → hbits n′ (s₂ st) w ≡ lay₂ n′ st w
    h₂ st w = cong st (pos₂ (toℕ (opposite w)) nH nD)

    -- A Hadamard layer whose bits are Y.

    RH : ∀ (st : Stream) (Y v : Assign n′) → (∀ w → hbits n′ st w ≡ Y w) →
         Runsˣ Hn st v (dot v Y) Y
    RH st Y v h = Runsˣ-embed (hadamards n′)
      (Runs-resp (dot-cong (λ _ → refl) h) h (Runs-hadamards n′ st v))

  runs-HSᵗ : ∀ (st : Stream) →
             Runsˣ (HSᵗ s Bs) st (0ᵃ {m ℕ+ m})
                   (hs-par (sumᵇ (gTerms Bs)) s (lay₁ n′ st) (lay₂ n′ st)
                           (lay₃ n′ st))
                   (lay₃ n′ st)
  runs-HSᵗ st =
    subst (λ C → Runsˣ C st (0ᵃ {n′}) β (lay₃ n′ st)) (sym (HSᵗ-layers s Bs))
      (Runsˣ-resp (β-hs (gTerms Bs) s Y₁ Y₂ Y₃) (λ _ → refl)
        (Runsˣ-++ (((Hn ++ X′) ++ Hn) ++ D′) Hn
          (Runsˣ-++ ((Hn ++ X′) ++ Hn) D′
            (Runsˣ-++ (Hn ++ X′) Hn
              (Runsˣ-++ Hn X′ (RH _ Y₁ (0ᵃ {n′}) (h₁ st))
                (Runsˣ-++ Fx (O′ ++ Fx) (Runsˣ-flips s _ Y₁)
                  (Runsˣ-++ O′ Fx
                    (Runsˣ-embed (Oᶠᵗ Bs) (Runs-Oᶠᵗ Bs _ (Y₁ ⊕ᵃ s)))
                    (Runsˣ-flips s _ (Y₁ ⊕ᵃ s)))))
              (RH _ Y₂ ((Y₁ ⊕ᵃ s) ⊕ᵃ s) (h₂ st)))
            (Runsˣ-embed (Oᵈᵗ Bs) (Runs-Oᵈᵗ Bs _ Y₂)))
          (RH st Y₃ Y₂ (λ _ → refl))))
    where
    Y₁ Y₂ Y₃ : Assign n′
    Y₁ = lay₁ n′ st
    Y₂ = lay₂ n′ st
    Y₃ = lay₃ n′ st

    β : Bool
    β = hs-par (sumᵇ (gTerms Bs)) s Y₁ Y₂ Y₃


------------------------------------------------------------------------
-- The symbolic shift circuit along a path

-- From data |0⟩ and shift register xs, along the path whose layers
-- read y₁, y₂, y₃: phase ½ hs-par with the shift xs, wires y₃ and xs.

module _ {m d : ℕ} (Bs : List (Block d m)) where

  private
    n′ : ℕ
    n′ = m ℕ+ m

    A cn O Xc Dc : Circuit (n′ ℕ+ n′)
    A  = hTˢ m
    cn = xTˢ m
    O  = upper n′ (Oᶠᵗ Bs)
    Xc = cn ++ (O ++ cn)
    Dc = upper n′ (Oᵈᵗ Bs)

    nA : norm A ≡ n′
    nA = trans (norm-upper n′ (hadamards n′)) (norm-hadamards n′)

    nC : norm cn ≡ 0
    nC = norm-cnots {n′} {n′} (λ i → i)

    nX : norm Xc ≡ 0
    nX = trans (norm-++ cn (O ++ cn))
      (cong₂ _ℕ+_ nC (trans (norm-++ O cn)
        (cong₂ _ℕ+_ (trans (norm-upper n′ (Oᶠᵗ Bs)) (norm-Oᶠᵗ Bs)) nC)))

    nD : norm Dc ≡ 0
    nD = trans (norm-upper n′ (Oᵈᵗ Bs)) (norm-Oᵈᵗ Bs)

    s₁ s₂ s₃ sA : Stream → Stream
    s₁ st = shift (norm A) st
    s₂ st = shift (norm Dc) (s₁ st)
    s₃ st = shift (norm A) (s₂ st)
    sA st = shift (norm Xc) (s₃ st)

    h₁ : ∀ st w → hbits n′ (sA st) w ≡ lay₁ n′ st w
    h₁ st w = cong st (pos₁ (toℕ (opposite w)) nX nA nD)

    h₂ : ∀ st w → hbits n′ (s₂ st) w ≡ lay₂ n′ st w
    h₂ st w = cong st (pos₂ (toℕ (opposite w)) nA nD)

    -- Each layer, on a data register Y and a shift register xs.

    L-A : ∀ st (Y xs U : Assign n′) → (∀ w → hbits n′ st w ≡ U w) →
          Runs A st (Y ⧺ xs) (dot Y U) (U ⧺ xs)
    L-A st Y xs U h = Runs-resp
      (dot-cong {u = λ i → (Y ⧺ xs) (i ↑ˡ n′)} {u′ = Y}
                (λ i → ⧺-↑ˡ Y xs i) h)
      (⧺-cong₂ {k = n′} {l = n′} h (λ j → ⧺-↑ʳ Y xs j))
      (Runs-upper n′ (hadamards n′)
        (Runs-hadamards n′ st (λ i → (Y ⧺ xs) (i ↑ˡ n′))))

    L-cn : ∀ st (Y xs : Assign n′) →
           Runs cn st (Y ⧺ xs) false ((Y ⊕ᵃ xs) ⧺ xs)
    L-cn st Y xs = Runs-resp refl
      (⧺-cong₂ {k = n′} {l = n′}
               (λ i → cong₂ _xor_ (⧺-↑ˡ Y xs i) (⧺-↑ʳ Y xs i))
               (λ j → ⧺-↑ʳ Y xs j))
      (Runs-cnots {n′} {n′} (λ i → i) st (Y ⧺ xs))

    L-O : ∀ (C : Circuit n′) (ts : List (Term n′)) →
          (∀ st v → Runs C st v (sumᵇ ts v) v) →
          ∀ st (Y xs : Assign n′) →
          Runs (upper n′ C) st (Y ⧺ xs) (sumᵇ ts Y) (Y ⧺ xs)
    L-O C ts RC st Y xs = Runs-resp
      (sumᵇ-resp ts (λ i → (Y ⧺ xs) (i ↑ˡ n′)) Y (λ i → ⧺-↑ˡ Y xs i))
      (⧺-cong₂ {k = n′} {l = n′} (λ i → ⧺-↑ˡ Y xs i) (λ j → ⧺-↑ʳ Y xs j))
      (Runs-upper n′ C (RC st (λ i → (Y ⧺ xs) (i ↑ˡ n′))))

    L-X : ∀ st (Y xs : Assign n′) →
          Runs Xc st (Y ⧺ xs)
               (false xor (sumᵇ (fTerms (gTerms Bs)) (Y ⊕ᵃ xs) xor false))
               (((Y ⊕ᵃ xs) ⊕ᵃ xs) ⧺ xs)
    L-X st Y xs = Runs-++ cn (O ++ cn) (L-cn _ Y xs)
      (Runs-++ O cn (L-O (Oᶠᵗ Bs) (fTerms (gTerms Bs)) (Runs-Oᶠᵗ Bs) _
                         (Y ⊕ᵃ xs) xs)
                    (L-cn st (Y ⊕ᵃ xs) xs))

  runs-SSᶜᵗ : ∀ (st : Stream) (xs : Assign (m ℕ+ m)) →
              Runs (SSᶜᵗ Bs) st (0ᵃ {m ℕ+ m} ⧺ xs)
                   (hs-par (sumᵇ (gTerms Bs)) xs (lay₁ n′ st) (lay₂ n′ st)
                           (lay₃ n′ st))
                   (lay₃ n′ st ⧺ xs)
  runs-SSᶜᵗ st xs =
    subst (λ C → Runs C st (0ᵃ {n′} ⧺ xs) β (Y₃ ⧺ xs)) (sym (SSᶜᵗ-layers Bs))
      (Runs-resp (β-hs (gTerms Bs) xs Y₁ Y₂ Y₃) (λ _ → refl)
        (Runs-++ (((A ++ Xc) ++ A) ++ Dc) A
          (Runs-++ ((A ++ Xc) ++ A) Dc
            (Runs-++ (A ++ Xc) A
              (Runs-++ A Xc (L-A _ (0ᵃ {n′}) xs Y₁ (h₁ st)) (L-X _ Y₁ xs))
              (L-A _ ((Y₁ ⊕ᵃ xs) ⊕ᵃ xs) xs Y₂ (h₂ st)))
            (L-O (Oᵈᵗ Bs) (f̃Terms (gTerms Bs)) (Runs-Oᵈᵗ Bs) _ Y₂ xs))
          (L-A st Y₂ xs Y₃ (λ _ → refl))))
    where
    Y₁ Y₂ Y₃ : Assign n′
    Y₁ = lay₁ n′ st
    Y₂ = lay₂ n′ st
    Y₃ = lay₃ n′ st

    β : Bool
    β = hs-par (sumᵇ (gTerms Bs)) xs Y₁ Y₂ Y₃
