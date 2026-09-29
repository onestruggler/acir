------------------------------------------------------------------------
-- Presentations of groups
--
-- The isometry restriction of a Clifford circuit, computed sparsely in
-- the cost model (for Amy, QPL 2018, section 4.1 and corollary 4.4)
--
-- Corollary 4.4 does not reduce the path-sum of a circuit but its
-- isometry restriction ξ|f(x,y)=x, reified.  The paper reifies it by
-- Gaussian elimination.  Over {H, S, CZ} every wire holds a single
-- variable, and the restriction is reified during interpretation, as
-- PathSum.Circuit.⟦_⟧ᴿ does it: a Hadamard allocates a fresh path
-- variable only when a later Hadamard touches its wire, and otherwise
-- puts x_w back.  This module computes ⟦ C ⟧ᴿ on sparse data, in the
-- monad of PathSum.Cost.
--
-- The state (Stateᴿ) is a list of terms and a vector of the variables
-- on the n wires; it starts with no terms and x_w on wire w
-- (initᴿᶜ).  The gates, as PathSum.Size.Interpreter.Clifford does them
-- for ⟦ C ⟧, each prepend one term:
--
--    S w     ¼ u        (u the variable on w)
--    CZ w v  ½ u u′     (u, u′ on w and v)
--    H w     ½ u y₀ and y₀ on w, the other terms and variables read
--            with the fresh y₀ (allocHᶜ), when hasHᶜ finds a later
--            Hadamard on w;
--            ½ u x_w and x_w on w (finalHᶜ) when it does not.
--
-- The lookahead hasHᶜ walks the rest of the circuit, so a Hadamard
-- costs O(|C|) more than the other gates; the whole run is quadratic
-- in n + |C|.  At the end the variables become the forms of a
-- PathSum.Size.Sparse.Rep (toRepᶜ).  Proved:
--
--  * interpᴿ-denotes: the result denotes ⟦ C ⟧ᴿ -- it has paths C
--    path variables, and represents ⟦ C ⟧ᴿ in the sense of
--    Sparse.Represents.  The run is tracked against PathSum.Circuit.run
--    gate by gate (Agreeᴿ, runᴿ-agree): the terms sum to the dense phase
--    modulo 2^M, coefficient by coefficient, and the vector holds the
--    dense signature.
--  * interpᴿ-length and interpᴿ-paths≤: exactly |C| terms, and at most
--    |C| path variables.
--  * cost-interpᴿᶜ: at most 19 (n + |C| + 1)^2 steps.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.  Comparing two wire indices is one step, and so
-- is writing down a constant coefficient with a new term.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Restriction (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∨_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate)
  renaming (map to mapⱽ)
open import Data.Vec.Properties using (lookup-map; lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary.Decidable using (⌊_⌋; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import PathSum.Base using (PathSum; ⟨_,_⟩)
open import PathSum.Cost
open import PathSum.Cost.Monomial using
  (varᶜ; value-varᶜ; cost-varᶜ; unionᵐᶜ; value-unionᵐᶜ; cost-unionᵐᶜ)
open import PathSum.Linear using (Lin; liftᴸ; varᴸ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Var; x[_]; y[_]; ⟪_⟫; _∪ᵐ_; _≈[_]_; _·ᴾ_; μ)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Size M using (μ-lifted)
open import PathSum.Size.Interpreter M using
  (Denotes; denotes; denotes-paths; denotes-represents)
open import PathSum.Size.Sparse M using
  (Term; ⟦_⟧ˢ; residue; Rep; rep; terms; forms; Represents)
open import PathSum.Size.Terms M using (≈-++; wkᵀ; wk-≈; term-≈)

import Data.Fin.Properties as Fin
import Data.List.Properties as List
import Data.Nat.Properties as ℕ
import PathSum.Circuit

private
  module Q = PathSum.Circuit M

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    A : Set
    k n m : ℕ


------------------------------------------------------------------------
-- Two traversals

-- Writing one entry of a vector: the cells before it are visited.

setᶜ : Vec A k → Fin k → A → Cost (Vec A k)
setᶜ (a ∷ as) zero    b = step (b ∷ as)
setᶜ (a ∷ as) (suc i) b = do
  tick
  bs ← setᶜ as i b
  pure (a ∷ bs)

-- Fin._≟_ at two successors is a map′, which does not compute here.

≟-suc : (v i : Fin k) → ⌊ suc v Fin.≟ suc i ⌋ ≡ ⌊ v Fin.≟ i ⌋
≟-suc v i with v Fin.≟ i | suc v Fin.≟ suc i
... | yes _ | yes _ = refl
... | no  _ | no  _ = refl
... | yes p | no ¬q = contradiction (cong suc p) ¬q
... | no ¬p | yes q = contradiction (Fin.suc-injective q) ¬p

lookup-setᶜ : (as : Vec A k) (i : Fin k) (b : A) (v : Fin k) →
              lookup (value (setᶜ as i b)) v ≡
              (if ⌊ v Fin.≟ i ⌋ then b else lookup as v)
lookup-setᶜ (a ∷ as) zero    b zero    = refl
lookup-setᶜ (a ∷ as) zero    b (suc v) = refl
lookup-setᶜ (a ∷ as) (suc i) b zero    = refl
lookup-setᶜ (a ∷ as) (suc i) b (suc v) = trans (lookup-setᶜ as i b v)
  (cong (λ c → if c then b else lookup as v) (sym (≟-suc v i)))

cost-setᶜ : (as : Vec A k) (i : Fin k) (b : A) → cost (setᶜ as i b) ≤ k
cost-setᶜ (a ∷ as) zero    b = s≤s z≤n
cost-setᶜ (a ∷ as) (suc i) b = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (setᶜ as i b))))
             (cost-setᶜ as i b))

-- Whether a later gate is a Hadamard on wire w: one step per gate, and
-- one more to compare the wire of each Hadamard.

hasHᶜ : Fin n → Q.Circuit n → Cost Bool
hasHᶜ w []             = pure false
hasHᶜ w (Q.H v ∷ C)    = do
  tick
  e ← step ⌊ w Fin.≟ v ⌋
  r ← hasHᶜ w C
  pure (e ∨ r)
hasHᶜ w (Q.S _ ∷ C)    = tick >> hasHᶜ w C
hasHᶜ w (Q.CZ _ _ ∷ C) = tick >> hasHᶜ w C

value-hasHᶜ : (w : Fin n) (C : Q.Circuit n) → value (hasHᶜ w C) ≡ Q.hasH w C
value-hasHᶜ w []             = refl
value-hasHᶜ w (Q.H v ∷ C)    = cong (⌊ w Fin.≟ v ⌋ ∨_) (value-hasHᶜ w C)
value-hasHᶜ w (Q.S _ ∷ C)    = value-hasHᶜ w C
value-hasHᶜ w (Q.CZ _ _ ∷ C) = value-hasHᶜ w C

private
  two-suc′ : ∀ c L → c ≤ 2 * L → suc (suc c) ≤ 2 * suc L
  two-suc′ c L le = ℕ.≤-trans (s≤s (s≤s le))
    (ℕ.≤-reflexive (solve 1 (λ L → con 2 :+ con 2 :* L :=
                                   con 2 :* (con 1 :+ L)) refl L))

  two-suc : ∀ c L → c ≤ 2 * L → suc (suc (c + 0)) ≤ 2 * suc L
  two-suc c L le = ℕ.≤-trans
    (ℕ.≤-reflexive (cong (λ z → suc (suc z)) (ℕ.+-identityʳ c)))
    (two-suc′ c L le)

  one-suc : ∀ c L → c ≤ 2 * L → suc c ≤ 2 * suc L
  one-suc c L le = ℕ.≤-trans (ℕ.n≤1+n (suc c)) (two-suc′ c L le)

cost-hasHᶜ : (w : Fin n) (C : Q.Circuit n) → cost (hasHᶜ w C) ≤ 2 * length C
cost-hasHᶜ w []             = z≤n
cost-hasHᶜ w (Q.H v ∷ C)    =
  two-suc (cost (hasHᶜ w C)) (length C) (cost-hasHᶜ w C)
cost-hasHᶜ w (Q.S _ ∷ C)    =
  one-suc (cost (hasHᶜ w C)) (length C) (cost-hasHᶜ w C)
cost-hasHᶜ w (Q.CZ _ _ ∷ C) =
  one-suc (cost (hasHᶜ w C)) (length C) (cost-hasHᶜ w C)

-- The number of Hadamards: the normalisation of ⟦ C ⟧ᴿ.

countHᶜ : Q.Circuit n → Cost ℕ
countHᶜ []             = pure 0
countHᶜ (Q.H _ ∷ C)    = do
  tick
  c ← countHᶜ C
  step (suc c)
countHᶜ (Q.S _ ∷ C)    = tick >> countHᶜ C
countHᶜ (Q.CZ _ _ ∷ C) = tick >> countHᶜ C

value-countHᶜ : (C : Q.Circuit n) → value (countHᶜ C) ≡ Q.norm C
value-countHᶜ []             = refl
value-countHᶜ (Q.H _ ∷ C)    = cong suc (value-countHᶜ C)
value-countHᶜ (Q.S _ ∷ C)    = value-countHᶜ C
value-countHᶜ (Q.CZ _ _ ∷ C) = value-countHᶜ C

cost-countHᶜ : (C : Q.Circuit n) → cost (countHᶜ C) ≤ 2 * length C
cost-countHᶜ []             = z≤n
cost-countHᶜ (Q.H _ ∷ C)    = ℕ.≤-trans
  (ℕ.≤-reflexive (cong suc (ℕ.+-comm (cost (countHᶜ C)) 1)))
  (two-suc′ (cost (countHᶜ C)) (length C) (cost-countHᶜ C))
cost-countHᶜ (Q.S _ ∷ C)    =
  one-suc (cost (countHᶜ C)) (length C) (cost-countHᶜ C)
cost-countHᶜ (Q.CZ _ _ ∷ C) =
  one-suc (cost (countHᶜ C)) (length C) (cost-countHᶜ C)


------------------------------------------------------------------------
-- The interpreter

-- A list of terms, and the variable on each wire.

Stateᴿ : ℕ → ℕ → Set
Stateᴿ n m = List (Term n m) × Vec (Var n m) n

initᴿᶜ : Cost (Stateᴿ n 0)
initᴿᶜ = (λ σ → [] , σ) <$> tabulateᶜ (λ w → step x[ w ])

-- The gates.

stepSᶜ : Fin n → Stateᴿ n m → Cost (Stateᴿ n m)
stepSᶜ w (ts , σ) = do
  u ← lookupᶜ σ w
  δ ← varᶜ u
  step ((δ , residue ¼) ∷ ts , σ)

stepCZᶜ : Fin n → Fin n → Stateᴿ n m → Cost (Stateᴿ n m)
stepCZᶜ w v (ts , σ) = do
  u  ← lookupᶜ σ w
  u′ ← lookupᶜ σ v
  δ  ← varᶜ u
  δ′ ← varᶜ u′
  γ  ← unionᵐᶜ δ δ′
  step ((γ , residue ½) ∷ ts , σ)

allocHᶜ : Fin n → Stateᴿ n m → Cost (Stateᴿ n (suc m))
allocHᶜ w (ts , σ) = do
  u  ← lookupᶜ σ w
  δ  ← varᶜ (Q.wkVar u)
  δ′ ← varᶜ y[ zero ]
  γ  ← unionᵐᶜ δ δ′
  us ← mapᶜ (λ t → step (wkᵀ t)) ts
  σ′ ← mapVᶜ (λ u → step (Q.wkVar u)) σ
  σ″ ← setᶜ σ′ w y[ zero ]
  step ((γ , residue ½) ∷ us , σ″)

finalHᶜ : Fin n → Stateᴿ n m → Cost (Stateᴿ n m)
finalHᶜ w (ts , σ) = do
  u  ← lookupᶜ σ w
  δ  ← varᶜ u
  δ′ ← varᶜ x[ w ]
  γ  ← unionᵐᶜ δ δ′
  σ′ ← setᶜ σ w x[ w ]
  step ((γ , residue ½) ∷ ts , σ′)

-- The circuit, left to right, looking ahead at each Hadamard.

mutual
  runᴿᶜ : Q.Circuit n → Stateᴿ n m → Cost (∃ (Stateᴿ n))
  runᴿᶜ []             s = pure (_ , s)
  runᴿᶜ (Q.H w ∷ C)    s = do
    tick
    b ← hasHᶜ w C
    afterHᶜ b w C s
  runᴿᶜ (Q.S w ∷ C)    s = do
    tick
    s′ ← stepSᶜ w s
    runᴿᶜ C s′
  runᴿᶜ (Q.CZ w v ∷ C) s = do
    tick
    s′ ← stepCZᶜ w v s
    runᴿᶜ C s′

  afterHᶜ : Bool → Fin n → Q.Circuit n → Stateᴿ n m → Cost (∃ (Stateᴿ n))
  afterHᶜ true  w C s = allocHᶜ w s >>= runᴿᶜ C
  afterHᶜ false w C s = finalHᶜ w s >>= runᴿᶜ C

-- The variables become forms.

toRepᶜ : Stateᴿ n m → Cost (Rep n m)
toRepᶜ (ts , σ) =
  (λ fs → rep ts (lookup fs)) <$> mapVᶜ (λ u → (false ,_) <$> varᶜ u) σ

-- The whole interpretation.

interpᴿᶜ : Q.Circuit n → Cost (∃ (Rep n))
interpᴿᶜ C = do
  s ← initᴿᶜ
  p ← runᴿᶜ C s
  R ← toRepᶜ (proj₂ p)
  pure (proj₁ p , R)


------------------------------------------------------------------------
-- Correctness

-- A sparse state agrees with a dense one when they have the same
-- number of path variables, the terms sum to the dense phase modulo
-- 2^M, and the vector holds the dense signature.

data Agreeᴿ {n : ℕ} : ∃ (Stateᴿ n) → ∃ (Q.State n) → Set where
  agreeᴿ : ∀ {m} (ts : List (Term n m)) (σ : Vec (Var n m) n)
           (st : Q.State n m) → Q.poly st ≈[ pow M ] ⟦ ts ⟧ˢ →
           (∀ v → lookup σ v ≡ Q.sig st v) →
           Agreeᴿ (m , (ts , σ)) (m , st)

-- The monomials the gates write down.

private
  var-at : (σ : Vec (Var n m) n) (st : Q.State n m) →
           (∀ v → lookup σ v ≡ Q.sig st v) → (w : Fin n) →
           value (varᶜ (value (lookupᶜ σ w))) ≡ ⟪ Q.sig st w ⟫
  var-at σ st hσ w =
    trans (value-varᶜ _) (cong ⟪_⟫ (trans (value-lookupᶜ σ w) (hσ w)))

  length-mapᶜ : (f : Term n m → Term n (suc m)) (ts : List (Term n m)) →
                length (value (mapᶜ (λ t → step (f t)) ts)) ≡ length ts
  length-mapᶜ f ts = trans (cong length (value-mapᶜ (λ t → step (f t)) ts))
                           (List.length-map f ts)

-- Every gate preserves agreement.

mutual
  runᴿ-agree : (C : Q.Circuit n) (ts : List (Term n m))
               (σ : Vec (Var n m) n) (st : Q.State n m) →
               Q.poly st ≈[ pow M ] ⟦ ts ⟧ˢ →
               (∀ v → lookup σ v ≡ Q.sig st v) →
               Agreeᴿ (value (runᴿᶜ C (ts , σ))) (Q.run C st)
  runᴿ-agree []             ts σ st h hσ = agreeᴿ ts σ st h hσ
  runᴿ-agree (Q.H w ∷ C)    ts σ st h hσ =
    subst (λ b → Agreeᴿ (value (afterHᶜ b w C (ts , σ)))
                        (Q.run C (proj₂ (Q.stepH (Q.hasH w C) w st))))
          (sym (value-hasHᶜ w C))
          (afterH-agree (Q.hasH w C) w C ts σ st h hσ)
  runᴿ-agree (Q.S w ∷ C)    ts σ st h hσ =
    runᴿ-agree C _ σ (Q.stepS w st)
      (subst (λ δ → Q.poly (Q.stepS w st) ≈[ pow M ]
                    ⟦ (δ , residue ¼) ∷ ts ⟧ˢ)
             (sym (var-at σ st hσ w))
             (≈-++ {P = Q.poly st} {Q = ¼ ·ᴾ Q.mono ⟪ Q.sig st w ⟫} ts
                   ((⟪ Q.sig st w ⟫ , residue ¼) ∷ []) h
                   (term-≈ ¼ ⟪ Q.sig st w ⟫)))
      hσ
  runᴿ-agree (Q.CZ w v ∷ C) ts σ st h hσ =
    runᴿ-agree C _ σ (Q.stepCZ w v st)
      (subst (λ δ → Q.poly (Q.stepCZ w v st) ≈[ pow M ]
                    ⟦ (δ , residue ½) ∷ ts ⟧ˢ)
             (sym (trans (value-unionᵐᶜ _ _)
                         (cong₂ _∪ᵐ_ (var-at σ st hσ w) (var-at σ st hσ v))))
             (≈-++ {P = Q.poly st} {Q = ½ ·ᴾ Q.mono δ₀} ts
                   ((δ₀ , residue ½) ∷ []) h (term-≈ ½ δ₀)))
      hσ
    where
    δ₀ = ⟪ Q.sig st w ⟫ ∪ᵐ ⟪ Q.sig st v ⟫

  afterH-agree : (b : Bool) (w : Fin n) (C : Q.Circuit n)
                 (ts : List (Term n m)) (σ : Vec (Var n m) n)
                 (st : Q.State n m) →
                 Q.poly st ≈[ pow M ] ⟦ ts ⟧ˢ →
                 (∀ v → lookup σ v ≡ Q.sig st v) →
                 Agreeᴿ (value (afterHᶜ b w C (ts , σ)))
                        (Q.run C (proj₂ (Q.stepH b w st)))
  afterH-agree true  w C ts σ st h hσ =
    runᴿ-agree C _ _ (Q.allocH w st)
      (subst₂ (λ δ us → Q.poly (Q.allocH w st) ≈[ pow M ]
                        ⟦ (δ , residue ½) ∷ us ⟧ˢ)
              (sym (trans (value-unionᵐᶜ _ _)
                     (cong₂ _∪ᵐ_
                       (trans (value-varᶜ _)
                         (cong (λ u → ⟪ Q.wkVar u ⟫)
                               (trans (value-lookupᶜ σ w) (hσ w))))
                       (value-varᶜ y[ zero ]))))
              (sym (value-mapᶜ (λ t → step (wkᵀ t)) ts))
              (≈-++ {P = Q.wkPoly (Q.poly st)} {Q = ½ ·ᴾ Q.mono δ₀}
                    (map wkᵀ ts) ((δ₀ , residue ½) ∷ [])
                    (wk-≈ {P = Q.poly st} ts h) (term-≈ ½ δ₀)))
      (λ v → trans (lookup-setᶜ (value (mapVᶜ (λ u → step (Q.wkVar u)) σ))
                                w y[ zero ] v)
        (cong (λ z → if ⌊ v Fin.≟ w ⌋ then y[ zero ] else z)
          (trans (cong (λ σ₁ → lookup σ₁ v)
                       (value-mapVᶜ (λ u → step (Q.wkVar u)) σ))
            (trans (lookup-map v Q.wkVar σ) (cong Q.wkVar (hσ v))))))
    where
    δ₀ = ⟪ Q.wkVar (Q.sig st w) ⟫ ∪ᵐ ⟪ y[ zero ] ⟫
  afterH-agree false w C ts σ st h hσ =
    runᴿ-agree C _ _ (Q.finalH w st)
      (subst (λ δ → Q.poly (Q.finalH w st) ≈[ pow M ]
                    ⟦ (δ , residue ½) ∷ ts ⟧ˢ)
             (sym (trans (value-unionᵐᶜ _ _)
                    (cong₂ _∪ᵐ_ (var-at σ st hσ w) (value-varᶜ x[ w ]))))
             (≈-++ {P = Q.poly st} {Q = ½ ·ᴾ Q.mono δ₀} ts
                   ((δ₀ , residue ½) ∷ []) h (term-≈ ½ δ₀)))
      (λ v → trans (lookup-setᶜ σ w x[ w ] v)
        (cong (λ z → if ⌊ v Fin.≟ w ⌋ then x[ w ] else z) (hσ v)))
    where
    δ₀ = ⟪ Q.sig st w ⟫ ∪ᵐ ⟪ x[ w ] ⟫

-- The start agrees with PathSum.Circuit.init.

private
  init-sig : ∀ (v : Fin n) → lookup (proj₂ (value (initᴿᶜ {n}))) v ≡ x[ v ]
  init-sig {n} v = trans
    (cong (λ σ → lookup σ v) (value-tabulateᶜ (λ w → step (x[_] {n} {0} w))))
    (lookup∘tabulate x[_] v)

interpᴿ-agree : (C : Q.Circuit n) →
                Agreeᴿ (value (runᴿᶜ C (value (initᴿᶜ {n})))) (Q.run C Q.init)
interpᴿ-agree {n} C =
  runᴿ-agree C [] (proj₂ (value (initᴿᶜ {n}))) Q.init (λ γ → i∣0) init-sig

-- The forms of the result are the variables, lifted: μ u.

private
  psᵈ : ∀ {k} (q : ∃ (Q.State n)) → PathSum n k (proj₁ q)
  psᵈ q = ⟨ Q.poly (proj₂ q) , (λ w → μ (Q.sig (proj₂ q) w)) ⟩

  agree⇒denotes : ∀ {k} (p : ∃ (Stateᴿ n)) (q : ∃ (Q.State n)) →
                  Agreeᴿ p q →
                  Denotes (psᵈ {k = k} q) (proj₁ p , value (toRepᶜ (proj₂ p)))
  agree⇒denotes _ _ (agreeᴿ ts σ st h hσ) =
    denotes (value (toRepᶜ (ts , σ)))
      (h , λ w γ → trans (μ-lifted (Q.sig st w) γ)
                         (cong (λ l → liftᴸ l γ) (sym (form-at w))))
    where
    form-at : ∀ w → forms (value (toRepᶜ (ts , σ))) w ≡ varᴸ (Q.sig st w)
    form-at w = trans
      (cong (λ fs → lookup fs w)
            (value-mapVᶜ (λ u → (false ,_) <$> varᶜ u) σ))
      (trans (lookup-map w (λ u → false , value (varᶜ u)) σ)
             (cong (false ,_) (trans (value-varᶜ (lookup σ w))
                                     (cong ⟪_⟫ (hσ w)))))

-- The interpreter computes ⟦ C ⟧ᴿ.

interpᴿ-denotes : (C : Q.Circuit n) → Denotes Q.⟦ C ⟧ᴿ (value (interpᴿᶜ C))
interpᴿ-denotes {n} C = agree⇒denotes {k = Q.norm C}
  (value (runᴿᶜ C (value (initᴿᶜ {n})))) (Q.run C Q.init) (interpᴿ-agree C)

interpᴿ-paths : (C : Q.Circuit n) → proj₁ (value (interpᴿᶜ C)) ≡ Q.paths C
interpᴿ-paths C = denotes-paths (value (interpᴿᶜ C)) (interpᴿ-denotes C)

interpᴿ-represents : (C : Q.Circuit n) →
  Represents Q.⟦ C ⟧ᴿ
    (subst (Rep n) (interpᴿ-paths C) (proj₂ (value (interpᴿᶜ C))))
interpᴿ-represents C =
  denotes-represents (value (interpᴿᶜ C)) (interpᴿ-denotes C)


------------------------------------------------------------------------
-- The size of the result

-- One term per gate, and at most one path variable per gate.

mutual
  runᴿ-length : (C : Q.Circuit n) (ts : List (Term n m))
                (σ : Vec (Var n m) n) →
                length (proj₁ (proj₂ (value (runᴿᶜ C (ts , σ))))) ≡
                length C + length ts
  runᴿ-length []             ts σ = refl
  runᴿ-length (Q.H w ∷ C)    ts σ =
    afterH-length (value (hasHᶜ w C)) w C ts σ
  runᴿ-length (Q.S w ∷ C)    ts σ =
    trans (runᴿ-length C _ σ) (ℕ.+-suc (length C) (length ts))
  runᴿ-length (Q.CZ w v ∷ C) ts σ =
    trans (runᴿ-length C _ σ) (ℕ.+-suc (length C) (length ts))

  afterH-length : (b : Bool) (w : Fin n) (C : Q.Circuit n)
                  (ts : List (Term n m)) (σ : Vec (Var n m) n) →
                  length (proj₁ (proj₂ (value (afterHᶜ b w C (ts , σ))))) ≡
                  suc (length C + length ts)
  afterH-length true  w C ts σ = trans (runᴿ-length C _ _)
    (trans (cong (λ z → length C + suc z) (length-mapᶜ wkᵀ ts))
           (ℕ.+-suc (length C) (length ts)))
  afterH-length false w C ts σ =
    trans (runᴿ-length C _ _) (ℕ.+-suc (length C) (length ts))

mutual
  runᴿ-paths : (C : Q.Circuit n) (s : Stateᴿ n m) →
               proj₁ (value (runᴿᶜ C s)) ≤ m + length C
  runᴿ-paths {m = m} []             s = ℕ.≤-reflexive (sym (ℕ.+-identityʳ m))
  runᴿ-paths {m = m} (Q.H w ∷ C)    s =
    afterH-paths (value (hasHᶜ w C)) w C s
  runᴿ-paths {m = m} (Q.S w ∷ C)    s = ℕ.≤-trans
    (runᴿ-paths C (value (stepSᶜ w s)))
    (ℕ.+-monoʳ-≤ m (ℕ.n≤1+n (length C)))
  runᴿ-paths {m = m} (Q.CZ w v ∷ C) s = ℕ.≤-trans
    (runᴿ-paths C (value (stepCZᶜ w v s)))
    (ℕ.+-monoʳ-≤ m (ℕ.n≤1+n (length C)))

  afterH-paths : (b : Bool) (w : Fin n) (C : Q.Circuit n) (s : Stateᴿ n m) →
                 proj₁ (value (afterHᶜ b w C s)) ≤ m + suc (length C)
  afterH-paths {m = m} true  w C s = ℕ.≤-trans
    (runᴿ-paths C (value (allocHᶜ w s)))
    (ℕ.≤-reflexive (sym (ℕ.+-suc m (length C))))
  afterH-paths {m = m} false w C s = ℕ.≤-trans
    (runᴿ-paths C (value (finalHᶜ w s)))
    (ℕ.+-monoʳ-≤ m (ℕ.n≤1+n (length C)))

interpᴿ-length : (C : Q.Circuit n) →
                 length (terms (proj₂ (value (interpᴿᶜ C)))) ≡ length C
interpᴿ-length {n} C = trans (runᴿ-length C [] (proj₂ (value (initᴿᶜ {n}))))
                             (ℕ.+-identityʳ (length C))

interpᴿ-paths≤ : (C : Q.Circuit n) → proj₁ (value (interpᴿᶜ C)) ≤ length C
interpᴿ-paths≤ {n} C = runᴿ-paths C (value (initᴿᶜ {n}))


------------------------------------------------------------------------
-- Cost

-- Each gate, in terms of a bound N on n, on the path variables and on
-- the terms.

private
  _+ˡ_ : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
  _+ˡ_ = ℕ.+-mono-≤
  infixr 6 _+ˡ_

  lin : ∀ {a b N} → a ≤ N → b ≤ N → a + b ≤ N + N
  lin = ℕ.+-mono-≤

cost-stepSᶜ : (w : Fin n) (ts : List (Term n m)) (σ : Vec (Var n m) n)
              {N : ℕ} → n ≤ N → m ≤ N →
              cost (stepSᶜ w (ts , σ)) ≤ 3 * N + 1
cost-stepSᶜ {n} {m} w ts σ {N} n≤ m≤ = ℕ.≤-trans
  ((ℕ.≤-trans (cost-lookupᶜ σ w) n≤) +ˡ
   (ℕ.≤-trans (cost-varᶜ (value (lookupᶜ σ w))) (lin n≤ m≤)) +ˡ
   ℕ.≤-refl {1})
  (ℕ.≤-reflexive (solve 1 (λ N → N :+ ((N :+ N) :+ con 1) :=
                                 con 3 :* N :+ con 1) refl N))

cost-stepCZᶜ : (w v : Fin n) (ts : List (Term n m)) (σ : Vec (Var n m) n)
               {N : ℕ} → n ≤ N → m ≤ N →
               cost (stepCZᶜ w v (ts , σ)) ≤ 8 * N + 1
cost-stepCZᶜ {n} {m} w v ts σ {N} n≤ m≤ = ℕ.≤-trans
  ((ℕ.≤-trans (cost-lookupᶜ σ w) n≤) +ˡ
   (ℕ.≤-trans (cost-lookupᶜ σ v) n≤) +ˡ
   (ℕ.≤-trans (cost-varᶜ (value (lookupᶜ σ w))) (lin n≤ m≤)) +ˡ
   (ℕ.≤-trans (cost-varᶜ (value (lookupᶜ σ v))) (lin n≤ m≤)) +ˡ
   (ℕ.≤-trans (cost-unionᵐᶜ (value (varᶜ (value (lookupᶜ σ w))))
                            (value (varᶜ (value (lookupᶜ σ v)))))
              (lin n≤ m≤)) +ˡ
   ℕ.≤-refl {1})
  (ℕ.≤-reflexive (solve 1 (λ N → N :+ (N :+ ((N :+ N) :+ ((N :+ N) :+
                                   ((N :+ N) :+ con 1)))) :=
                                 con 8 :* N :+ con 1) refl N))

cost-allocHᶜ : (w : Fin n) (ts : List (Term n m)) (σ : Vec (Var n m) n)
               {N : ℕ} → n ≤ N → suc m ≤ N → length ts ≤ N →
               cost (allocHᶜ w (ts , σ)) ≤ 12 * N + 1
cost-allocHᶜ {n} {m} w ts σ {N} n≤ m≤ L≤ = ℕ.≤-trans
  ((ℕ.≤-trans (cost-lookupᶜ σ w) n≤) +ˡ
   (ℕ.≤-trans (cost-varᶜ (Q.wkVar (value (lookupᶜ σ w)))) (lin n≤ m≤)) +ˡ
   (ℕ.≤-trans (cost-varᶜ (y[_] {n} {suc m} zero)) (lin n≤ m≤)) +ˡ
   (ℕ.≤-trans (cost-unionᵐᶜ (value (varᶜ (Q.wkVar (value (lookupᶜ σ w)))))
                            (value (varᶜ (y[_] {n} {suc m} zero))))
              (lin n≤ m≤)) +ˡ
   (ℕ.≤-trans (cost-mapᶜ (λ t → step (wkᵀ t)) ts (λ _ → ℕ.≤-refl {1}))
              (ℕ.*-monoˡ-≤ 2 L≤)) +ˡ
   (ℕ.≤-trans (cost-mapVᶜ (λ u → step (Q.wkVar u)) σ (λ _ → ℕ.≤-refl {1}))
              (ℕ.*-monoˡ-≤ 2 n≤)) +ˡ
   (ℕ.≤-trans (cost-setᶜ (value (mapVᶜ (λ u → step (Q.wkVar u)) σ)) w
                         y[ zero ]) n≤) +ˡ
   ℕ.≤-refl {1})
  (ℕ.≤-reflexive (solve 1 (λ N → N :+ ((N :+ N) :+ ((N :+ N) :+ ((N :+ N) :+
                                   (N :* con 2 :+ (N :* con 2 :+
                                   (N :+ con 1)))))) :=
                                 con 12 :* N :+ con 1) refl N))

cost-finalHᶜ : (w : Fin n) (ts : List (Term n m)) (σ : Vec (Var n m) n)
               {N : ℕ} → n ≤ N → m ≤ N →
               cost (finalHᶜ w (ts , σ)) ≤ 8 * N + 1
cost-finalHᶜ {n} {m} w ts σ {N} n≤ m≤ = ℕ.≤-trans
  ((ℕ.≤-trans (cost-lookupᶜ σ w) n≤) +ˡ
   (ℕ.≤-trans (cost-varᶜ (value (lookupᶜ σ w))) (lin n≤ m≤)) +ˡ
   (ℕ.≤-trans (cost-varᶜ (x[_] {n} {m} w)) (lin n≤ m≤)) +ˡ
   (ℕ.≤-trans (cost-unionᵐᶜ (value (varᶜ (value (lookupᶜ σ w))))
                            (value (varᶜ (x[_] {n} {m} w))))
              (lin n≤ m≤)) +ˡ
   (ℕ.≤-trans (cost-setᶜ σ w x[ w ]) n≤) +ˡ
   ℕ.≤-refl {1})
  (ℕ.≤-reflexive (solve 1 (λ N → N :+ ((N :+ N) :+ ((N :+ N) :+ ((N :+ N) :+
                                   (N :+ con 1)))) :=
                                 con 8 :* N :+ con 1) refl N))

-- The run: at most 16 (N + 1) per gate, as long as n ≤ N and the path
-- variables, and the terms, together with the gates to come stay below
-- N -- which every gate keeps true.

private
  G : ℕ → ℕ
  G N = 16 * suc N

  8≤12 : 8 ≤ 12
  8≤12 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

  -- One gate: 2 + b + a ≤ 16 (N + 1) when a ≤ 12 N + 1 and b ≤ 2 N.
  gate≤ : ∀ {a b N} → b ≤ 2 * N → a ≤ 12 * N + 1 → suc (b + a) ≤ G N
  gate≤ {a} {b} {N} b≤ a≤ = ℕ.≤-trans (s≤s (ℕ.+-mono-≤ b≤ a≤))
    (ℕ.≤-trans (ℕ.≤-reflexive (solve 1 (λ N → con 1 :+ (con 2 :* N :+
                                          (con 12 :* N :+ con 1)) :=
                                        con 14 :* N :+ con 2) refl N))
      (ℕ.≤-trans (ℕ.+-mono-≤ (ℕ.*-monoˡ-≤ N (ℕ.m≤m+n 14 2))
                             (ℕ.m≤m+n 2 14))
        (ℕ.≤-reflexive (solve 1 (λ N → con 16 :* N :+ con 16 :=
                                       con 16 :* (con 1 :+ N)) refl N))))

  small≤ : ∀ {a N} → a ≤ 8 * N + 1 → suc a ≤ G N
  small≤ {a} {N} a≤ = gate≤ {a = a} {b = 0} z≤n
    (ℕ.≤-trans a≤ (ℕ.+-monoˡ-≤ 1 (ℕ.*-monoˡ-≤ N 8≤12)))

  le-S : ∀ {m C N} → m + suc C ≤ N → m + C ≤ N
  le-S {m} {C} le = ℕ.≤-trans (ℕ.+-monoʳ-≤ m (ℕ.n≤1+n C)) le

  le-T : ∀ {L C N} → L + suc C ≤ N → suc L + C ≤ N
  le-T {L} {C} le = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.+-suc L C))) le

  le-A : ∀ {m C N} → m + suc C ≤ N → suc m + C ≤ N
  le-A {m} {C} le = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.+-suc m C))) le

  le-m : ∀ {m C N} → m + suc C ≤ N → m ≤ N
  le-m {m} {C} le = ℕ.≤-trans (ℕ.m≤m+n m (suc C)) le

  le-sm : ∀ {m C N} → m + suc C ≤ N → suc m ≤ N
  le-sm {m} {C} le = ℕ.≤-trans (s≤s (ℕ.m≤m+n m C)) (le-A {m} {C} le)

  le-C : ∀ {m C N} → m + suc C ≤ N → C ≤ N
  le-C {m} {C} le = ℕ.≤-trans (ℕ.≤-trans (ℕ.n≤1+n C) (ℕ.m≤n+m (suc C) m)) le

mutual
  cost-runᴿᶜ : (C : Q.Circuit n) (ts : List (Term n m))
               (σ : Vec (Var n m) n) (N : ℕ) → n ≤ N →
               m + length C ≤ N → length ts + length C ≤ N →
               cost (runᴿᶜ C (ts , σ)) ≤ length C * G N
  cost-runᴿᶜ []             ts σ N n≤ mC≤ LC≤ = z≤n
  cost-runᴿᶜ (Q.H w ∷ C)    ts σ N n≤ mC≤ LC≤ = ℕ.≤-trans
    (s≤s (ℕ.+-mono-≤ (cost-hasHᶜ w C)
                     (cost-afterHᶜ (value (hasHᶜ w C)) w C ts σ N n≤ mC≤ LC≤)))
    (ℕ.≤-trans
      (ℕ.≤-reflexive (cong suc (sym (ℕ.+-assoc (2 * length C) (12 * N + 1)
                                               (length C * G N)))))
      (ℕ.+-monoˡ-≤ (length C * G N)
        (gate≤ (ℕ.*-monoʳ-≤ 2 (le-C mC≤)) ℕ.≤-refl)))
  cost-runᴿᶜ (Q.S w ∷ C)    ts σ N n≤ mC≤ LC≤ = ℕ.+-mono-≤
    (small≤ (ℕ.≤-trans (cost-stepSᶜ w ts σ n≤ (le-m mC≤))
      (ℕ.+-monoˡ-≤ 1 (ℕ.*-monoˡ-≤ N (ℕ.m≤m+n 3 5)))))
    (cost-runᴿᶜ C _ σ N n≤ (le-S mC≤) (le-T LC≤))
  cost-runᴿᶜ (Q.CZ w v ∷ C) ts σ N n≤ mC≤ LC≤ = ℕ.+-mono-≤
    (small≤ (cost-stepCZᶜ w v ts σ n≤ (le-m mC≤)))
    (cost-runᴿᶜ C _ σ N n≤ (le-S mC≤) (le-T LC≤))

  cost-afterHᶜ : (b : Bool) (w : Fin n) (C : Q.Circuit n)
                 (ts : List (Term n m)) (σ : Vec (Var n m) n) (N : ℕ) →
                 n ≤ N → m + suc (length C) ≤ N →
                 length ts + suc (length C) ≤ N →
                 cost (afterHᶜ b w C (ts , σ)) ≤
                 (12 * N + 1) + length C * G N
  cost-afterHᶜ {n} {m} true  w C ts σ N n≤ mC≤ LC≤ = ℕ.+-mono-≤
    (cost-allocHᶜ w ts σ n≤ (le-sm mC≤)
      (ℕ.≤-trans (ℕ.m≤m+n (length ts) (suc (length C))) LC≤))
    (cost-runᴿᶜ C _ _ N n≤ (le-A mC≤)
      (ℕ.≤-trans (ℕ.≤-reflexive (cong (λ z → suc z + length C)
                                      (length-mapᶜ wkᵀ ts)))
                 (le-T LC≤)))
  cost-afterHᶜ {n} {m} false w C ts σ N n≤ mC≤ LC≤ = ℕ.+-mono-≤
    (ℕ.≤-trans (cost-finalHᶜ w ts σ n≤ (le-m mC≤))
               (ℕ.+-monoˡ-≤ 1 (ℕ.*-monoˡ-≤ N 8≤12)))
    (cost-runᴿᶜ C _ _ N n≤ (le-S mC≤) (le-T LC≤))

-- The whole interpretation: at most 19 (n + |C| + 1)^2.

cost-interpᴿᶜ : (C : Q.Circuit n) →
                cost (interpᴿᶜ C) ≤ 19 * suc (n + length C) ^ 2
cost-interpᴿᶜ {n} C = ℕ.≤-trans
  ((ℕ.≤-trans (cost-tabulateᶜ (λ w → step (x[_] {n} {0} w)) (λ _ → ℕ.≤-refl))
              (ℕ.*-monoˡ-≤ 2 n≤X)) +ˡ
   (ℕ.≤-trans (cost-runᴿᶜ C [] σ₀ N (ℕ.m≤m+n n (length C))
                          (ℕ.m≤n+m (length C) n) (ℕ.m≤n+m (length C) n))
              (ℕ.*-monoˡ-≤ (16 * X) C≤X)) +ˡ
   (ℕ.≤-trans (cost-mapVᶜ (λ u → (false ,_) <$> varᶜ u) (proj₂ (proj₂ p))
                          (λ u → cost-varᶜ u))
              (ℕ.*-mono-≤ n≤X (s≤s (ℕ.+-monoʳ-≤ n (interpᴿ-paths≤ C))))) +ˡ
   z≤n {0})
  (ℕ.≤-trans (ℕ.≤-reflexive (collect X))
    (ℕ.≤-trans (ℕ.+-monoʳ-≤ (17 * (X * X)) (ℕ.*-monoʳ-≤ 2 X≤XX))
      (ℕ.≤-reflexive (trans (solve 1 (λ Y → con 17 :* Y :+ con 2 :* Y :=
                                           con 19 :* Y) refl (X * X))
                            (cong (λ z → 19 * (X * z))
                                  (sym (ℕ.*-identityʳ X)))))))
  where
  N = n + length C
  X = suc N
  σ₀ = proj₂ (value (initᴿᶜ {n}))
  p = value (runᴿᶜ C (value (initᴿᶜ {n})))

  n≤X : n ≤ X
  n≤X = ℕ.≤-trans (ℕ.m≤m+n n (length C)) (ℕ.n≤1+n N)

  C≤X : length C ≤ X
  C≤X = ℕ.≤-trans (ℕ.m≤n+m (length C) n) (ℕ.n≤1+n N)

  X≤XX : X ≤ X * X
  X≤XX = ℕ.m≤m*n X X

  collect : ∀ X → X * 2 + (X * (16 * X) + (X * X + 0)) ≡
                  17 * (X * X) + 2 * X
  collect = solve 1 (λ X → X :* con 2 :+ (X :* (con 16 :* X) :+
                            (X :* X :+ con 0)) :=
                          con 17 :* (X :* X) :+ con 2 :* X) refl
