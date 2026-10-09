# 6. An Agda primer

The formalisation is written in [Agda](https://agda.readthedocs.io), a
programming language in which types can express mathematical statements
and programs can be proofs of them. This chapter teaches just enough to
**read** the formal statements in `PathSum/Theorems.agda`. Writing proofs
takes longer to learn; pointers are at the end.

## 6.1 Data and functions

Agda programs are made of data types and functions defined by
**pattern matching**:

```agda
data Bool : Set where
  false true : Bool

not : Bool → Bool
not false = true
not true  = false
```

`Set` is the type of (small) types. `Bool → Bool` is the type of
functions from booleans to booleans. Natural numbers are built from zero
and successor, and recursive functions follow that structure:

```agda
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)
```

The underscores in `_+_` say where the arguments go, so you can write
`m + n`. Agda uses Unicode freely: `ℕ`, `→`, `≡`, `⟦_⟧` are all ordinary
names or notation.

## 6.2 Types that depend on values

The key feature: a type can depend on a value. `Fin n` is the type of
numbers $0, 1, \dots, n-1$, a different type for each `n`. A function
`Fin n → Bool` assigns a bit to each of `n` wires; the formalisation calls
this type `Assign n`. Likewise a path-sum on `n` qubits with normalisation
`k` and `m` path variables has type `PathSum n k m`.

Arguments in curly braces `{n : ℕ}` are **implicit**: Agda works them out
from the other arguments, and you can omit them.

## 6.3 Propositions are types, proofs are programs

A statement is a type, and a proof of it is a value of that type. The
simplest statement is equality:

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
```

`x ≡ y` has a value (`refl`) only when `x` and `y` are the same after
computing. So a proof that double negation does nothing is a function
that, for every boolean, produces an equality, by cases:

```agda
not-not : (b : Bool) → not (not b) ≡ b
not-not false = refl
not-not true  = refl
```

A proof by **induction** is a recursive function. To prove `n + zero ≡ n`,
the case `suc n` uses the proof for `n`:

```agda
+-zero : (n : ℕ) → n + zero ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)
```

Agda checks that every case is covered and that the recursion terminates,
so a function of this type really is a proof for all `n`.

## 6.4 Logic, as types

| Logic | Agda | A proof is … |
|---|---|---|
| $A$ and $B$ | `A × B` | a pair `(a , b)` |
| $A$ or $B$ | `A ⊎ B` | `inj₁ a` or `inj₂ b` |
| $A$ implies $B$ | `A → B` | a function |
| for all $x$, $P(x)$ | `(x : X) → P x` or `∀ x → P x` | a function |
| there exists $x$ with $P(x)$ | `∃ λ x → P x`, or `Σ X P` | a pair: a witness and a proof |
| false | `⊥` | (none) |
| not $A$ | `¬ A`, i.e. `A → ⊥` | a function into the empty type |
| $A$ if and only if $B$ | `A ⇔ B` | functions both ways |
| $A$ is decidable | `Dec A` | `yes a` or `no ¬a`: an answer *with* its proof |

`Dec` deserves a remark. A value of `Dec A` is a decision procedure: it
computes an answer and comes with a proof that the answer is right. So
`circuit-decidable : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)` is literally an
algorithm deciding whether a circuit is the identity, proved correct.

## 6.5 Modules with parameters

A file is a **module**, and a module can take parameters that all its
definitions share. Many PathSum modules take the precision `M₀ : ℕ`:
phases are fractions with denominator $2^M$ where $M = M_0 + 3$, so `M₀ = 0`
means phases in eighths, enough for Clifford+T. Writing
`PathSum.Circuit 3` uses the circuit module at $M = 3$. Because the
theorems hold for every `M₀`, the precision is not a limitation of the
proofs, only of what a given instance can express.

## 6.6 Reading a real statement

Here is the formal Corollary 4.4, as `PathSum/Theorems.agda` states it:

```agda
corollary-4-4-syntactic : (C : Circuit n) →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ C ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
```

Read it piece by piece:

- `(C : Circuit n) →` — for every circuit `C` on `n` wires (over H, S, CZ),
- `⟦ C ⟧ ≋ idPS` — the circuit's path-sum is equivalent to the identity
  path-sum (same operator),
- `⇔` — if and only if
- `∃ λ (ξ′ : PathSum n 0 0) →` — there is a path-sum `ξ′` with **no** path
  variables and no normalisation, such that
- `⟦ C ⟧ᴿ ⟶* ξ′` — the circuit's *restricted* path-sum (chapter 4) rewrites
  to `ξ′` by the rules of chapter 3,
- `∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]` — every output wire `w` of `ξ′` is
  the input variable `x_w`, modulo 2, and
- `phase ξ′ ≈[ pow M ] 0ᴾ` — the phase of `ξ′` is zero, modulo 1
  (coefficients are numerators over $2^M$).

In words: a Clifford circuit is the identity exactly when its restricted
path-sum rewrites to something that is *syntactically* the identity. That
is the heart of the paper's section 4, as one checked statement.

Two more, for practice:

```agda
⟶-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ ζ → ξ ≋ ζ
```

Every rewrite step preserves the operator (Proposition 3.1).

```agda
hidden-shift : (g : Poly m 0) (s z : Assign (m + m)) →
               amp (HSh.HS g s) 0ᵃ z ≐
               (if same s z then scale (HSh.hs-norm (m + m)) (zpow 0ℤ)
                else 0ᴬ)
```

For every function `g` and shift `s`, the amplitude of the hidden shift
circuit from input $\lvert 0\rangle$ to output $\lvert z\rangle$ is $1$ (up to the
normalisation, here cleared of its denominator) when `z` is `s`, and $0$
otherwise: the circuit outputs $\lvert s\rangle$.

## 6.7 No cheating

Every file starts with

```agda
{-# OPTIONS --cubical-compatible --safe #-}
```

`--safe` forbids everything that could make a false statement
typecheck: no `postulate` (unproved assumptions), no switching off the
termination checker, no unsolved holes. The development uses none of
them, so once the root module typechecks, every theorem it states is
proved from the definitions alone.

## 6.8 Running it yourself

1. Install Agda 2.8 and the Agda standard library 2.4, and register the
   library in `~/.config/agda/libraries`.
2. From the repository root, check one module, for example the worked
   examples of section 3:

   ```
   agda +RTS -M6G -RTS PathSum/Examples/Section3.agda
   ```

   The `+RTS -M6G -RTS` part caps Agda's memory at 6 GB. The first run
   checks every module this one depends on; later runs reuse the saved
   interface files in `_build/` and are fast.
3. To check everything, run the same command on `PathSum/Theorems.agda`.
   From scratch this takes about 40 minutes of CPU time.

To go further, the
[Agda documentation](https://agda.readthedocs.io), the online book
*Programming Language Foundations in Agda* (PLFA) and the standard library's
source are good next steps. Editor support (agda-mode in Emacs or VS
Code) lets you load a file, see goals, and fill in proofs interactively.

## Check yourself

1. What is the type of a proof that addition is commutative?
2. What would a value of `Dec (⟦ C ⟧ ≋ idPS)` look like for a circuit
   that is *not* the identity?
3. In `corollary-4-4-syntactic`, why must `ξ′` have type `PathSum n 0 0`
   and not `PathSum n k m` for arbitrary `k` and `m`?

Next: [7. Inside the formalisation](07-formalisation.md).
