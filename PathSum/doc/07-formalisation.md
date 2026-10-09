# 7. Inside the formalisation

This chapter walks through how the objects of chapters 2–4 are defined in
Agda, with excerpts from the actual files. The aim is that you can open
any module in `PathSum/` and recognise what it is doing.

## 7.1 The map

The development has about 340 modules. They are layered: each builds on
the ones above it in this table.

| Layer | Modules | Paper |
|---|---|---|
| Polynomials | `Polynomial`, `Polynomial/Properties`, `Order`, `Mobius` | §2: dyadic polynomials, lemma 2.5, order, lemma 2.13 |
| Path-sums | `Base` | definition 2.1 |
| Rewriting | `Reduction`, `Reduction/General`, `Anywhere`, `Full` | figure 2, at the first variable and at any variable |
| Meaning | `Cyclotomic`, `Denotation`, `Semantics` | the operator $U_\xi$, definition 2.3, proposition 3.1 |
| Circuits | `Circuit`, `CircuitSemantics`, `CRK/` | definition 2.9, proposition 2.10 |
| Section 4 | `Isometry`, `Interference`, `Clifford`, `Decide`, `Syntactic`, `Corollary`, `Gauss` | lemmas 4.1–4.3, corollary 4.4 |
| Around it | `Compose`, `Ring`, `PartialIsometry`, `Cost`, `Hierarchy`, … | composition, unitarity, time bounds, the hierarchy |
| Section 5 | `ToffoliN`, `Maslov`, `Adder`, `QFT`, `HiddenShift` | the case studies, for every size |
| Examples | `Examples/` | the paper's worked examples |
| Root | `Theorems` | restates everything |

## 7.2 Polynomials as functions on monomials

A monomial like $x_1 y_2 y_3$ is determined by which input variables and
which path variables it contains, so it is a pair of subsets:

```agda
Mon : ℕ → ℕ → Set
Mon n m = Subset n × Subset m
```

A polynomial assigns a coefficient to every monomial. Coefficients of
phases are dyadic fractions with denominator $2^M$, so the formalisation
stores just the **numerator**, an integer:

```agda
Poly : ℕ → ℕ → Set
Poly n m = Mon n m → ℤ
```

So at $M = 3$ the phase $\tfrac12 x y_1$ is the function sending the
monomial $x y_1$ to $4$ (since $\tfrac12 = \tfrac48$) and every other
monomial to $0$. Two phases are equal modulo 1 when their numerators agree
modulo $2^M$, written `P ≈[ pow M ] Q`. Output polynomials reuse the same
type, read modulo 2: `f ≈[ + 2 ] g`.

Representing a polynomial as a function on *all* $2^{n+m}$ monomials is
simple and exact, which is ideal for proofs. It would be hopeless for
computing with big circuits, so the part of the development about running
time (`Cost/`) uses sparse lists of terms instead and proves the two agree.

## 7.3 Path-sums, and why two indices

```agda
record PathSum (n k m : ℕ) : Set where
  constructor ⟨_,_⟩
  field
    phase : Poly n m
    -- The output polynomials, whose coefficients are read modulo 2.
    out   : Fin n → Poly n m
```

A path-sum on `n` qubits with `m` path variables stores its phase and one
output polynomial per wire. The third index `k` is the exponent of the
normalisation $1/\sqrt{2^k}$. Definition 2.1 says $k = m$, so why keep them
apart? Look back at the rules in chapter 3:

| Rule | path variables | factors of $1/\sqrt2$ |
|---|---|---|
| [Elim] | − 1 | − 2 |
| [ω] | − 1 | − 1 |
| [HH] | − 1 | 0 |

After a few rewrites, $k$ and $m$ have drifted apart, so a type with
$k = m$ built in could not even state the rules. This is the kind of detail
a paper can wave past ("applied to path-sums in the obvious way") and a
proof assistant cannot.

The identity path-sum has no path variables, phase $0$, and output $x_i$
on wire $i$:

```agda
idPS : PathSum n 0 0
idPS = ⟨ 0ᴾ , (λ i → μ x[ i ]) ⟩
```

## 7.4 Exact amplitudes, with no real numbers

To say two path-sums are equivalent we need their operators, which
involve $\sqrt2$ and $e(\theta)$. The formalisation never uses real or
floating-point numbers. Instead, every phase is a power of the root of
unity $\zeta = e(1/2^M)$, and amplitudes live in the ring $\mathbb{Z}[\zeta]$:
integer combinations of powers of $\zeta$, stored as a list of integer
coefficients (`Amp` in `Cyclotomic.agda`). Even $\sqrt 2$ is there:
$\sqrt2 = \zeta^{c} + \zeta^{-c}$ where $\zeta^c = e(1/8)$, because
$e^{i\pi/4} + e^{-i\pi/4} = 2\cos(\pi/4) = \sqrt2$.

The amplitude from input `x` to output `z`, before dividing by the
normalisation, is the sum of $\zeta^{P(x,y)}$ over the paths `y` that hit `z`:

```agda
amp : PathSum n k m → Assign n → Assign n → Amp
amp ξ x z = Σᴮ (λ y → if hits ξ x y z then zpow (eval (phase ξ) x y) else 0ᴬ)
```

and equivalence compares amplitudes with the normalisations
cross-multiplied, so no division is needed:

```agda
_≋_ : PathSum n k m → PathSum n k′ m′ → Set
_≋_ {k = k} {k′ = k′} ξ ζ =
  ∀ x z → scale k′ (amp ξ x z) ≐ scale k (amp ζ x z)
```

`scale k` multiplies by $\sqrt2^{\,k}$. Everything here is exact
integer arithmetic, so statements about amplitudes can even be checked by
computation.

## 7.5 The rules as an inductive relation

A rewrite step is a value of type `ξ ⟶ ζ`. Each constructor is one rule,
and its arguments are the rule's side conditions:

```agda
data _⟶_ {n : ℕ} : ∀ {k m k′ m′} →
                   PathSum n k m → PathSum n k′ m′ → Set where

  elim : ∀ {k m} (ξ : PathSum n (suc (suc k)) (suc m)) →
         head-part (phase ξ) ≈[ pow M ] 0ᴾ →
         (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
         ξ ⟶ elim-reduct ξ

  hh   : ∀ {k m} (ξ : PathSum n k (suc m)) (i : Fin m) (c : Bool)
         (S : Mon n m) → y[ i ] ∈ᵐ S →
         head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
         (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
         ξ ⟶ hh-reduct ξ i c S
  …
```

Read `elim`: for a path-sum with at least two factors of normalisation
(`suc (suc k)`) and at least one path variable (`suc m`), if the part of
the phase containing the first variable $y_0$ is zero (`head-part … ≈ 0ᴾ`)
and $y_0$ occurs in no output (`NoVar … y₀ …`), then it steps to the
result `elim-reduct ξ`, which has two fewer normalisation factors and one
fewer variable. In `hh`, the set `S` of variables and the bit `c` stand
for the linear Boolean form $c \oplus \bigoplus_{v \in S} v$; the rule asks that
the part containing $y_0$ be $\tfrac12 y_0$ times (the lifting of) that form,
with $y_i$ among its variables, and substitutes for $y_i$.

These rules act at the first path variable; `Anywhere` and `Full` lift
them to any variable and add [Case]. Soundness, `⟶-sound`, is proved
rule by rule exactly as in chapter 3, but with every step justified.

## 7.6 Circuits, and a built-in restriction

```agda
data Gate (n : ℕ) : Set where
  H  : Fin n → Gate n
  S  : Fin n → Gate n
  CZ : Fin n → Fin n → Gate n

Circuit : ℕ → Set
Circuit n = List (Gate n)
```

A circuit is a list of gates in time order. `⟦ C ⟧` is its path-sum
(definition 2.9). There is also `⟦ C ⟧ᴿ`, the *restriction* of chapter 4
computed directly. When a Hadamard's path variable is never touched by a
later Hadamard, the condition $f(x,y) = x$ forces it to equal the input on
its wire, so `⟦ C ⟧ᴿ` simply does not create that variable. The
connection to the real thing is lemma 4.1:

```agda
lemma-4-1-circuit : (C : Circuit n) → (⟦ C ⟧ ≋ idPS ⇔ ⟦ C ⟧ᴿ ≋ idPS)
```

## 7.7 A complete small example: $HH = I$

`PathSum/Examples/Section3.agda` checks the paper's first example. At
$M = 3$ (phases in eighths) the paper's path-sum for $HH$ is written
directly:

```agda
-- ½(x y1 + y1 y2), output y2; y1 is yᵐ zero.

HHᵖ : PathSum 1 2 2
HHᵖ = ⟨ ½ ·ᴾ (mono (xᵐ zero ∪ᵐ yᵐ zero) +ᴾ
              mono (yᵐ zero ∪ᵐ yᵐ (suc zero)))
      , (λ _ → μ y[ suc zero ]) ⟩
```

The reduction of chapter 3 is two steps, [HH] then [Elim], and the proof
that it is the identity follows from soundness:

```agda
HHᵖ₁ : PathSum 1 2 1
HHᵖ₁ = hh-reduct HHᵖ zero false (xᵐ zero ∪ᵐ yᵐ zero)

HHᵖ₂ : PathSum 1 0 0
HHᵖ₂ = elim-reduct HHᵖ₁

HHᵖ-reduces : HHᵖ ⟶* HHᵖ₂
HHᵖ-reduces = hh! HHᵖ zero false (xᵐ zero ∪ᵐ yᵐ zero) ◅ (elim! HHᵖ₁ ◅ ε)

HHᵖ-id : HHᵖ ≋ idPS
HHᵖ-id = reduces-to-id! HHᵖ-reduces
```

`hh!` and `elim!` are versions of the rules whose side conditions Agda
checks **by computation**, so the proof needs no hand-written argument for
them. The same module also does it the corollary 4.4 way. The restricted
path-sum `⟦ HH ⟧ᴿ` has already set $y_2 = x$, so its phase is
$\tfrac12 xy + \tfrac12 yx = xy$, an integer, and one [Elim] finishes:

```agda
_ : phase ⟦ HH ⟧ᴿ (xᵐ zero ∪ᵐ yᵐ zero) ≡ + 8
_ = refl

HH-id : ⟦ HH ⟧ ≋ idPS
HH-id = circuit-id! HH HH-reduces
```

The first line is a test you can read: the coefficient of $xy$ is
$8/8 = 1$, which vanishes modulo 1. Agda confirms it by computing (`refl`).

## 7.8 How the whole thing hangs together

- **The root.** `PathSum/Theorems.agda` restates every headline result of
  every module, under a section heading naming the module that proves it.
  Typechecking the root therefore typechecks everything. Its opening
  comment also lists every departure from the paper.
- **Departures.** A few choices differ from the paper, all documented:
  - the precision is fixed by the parameter $M$;
  - the normalisation $k$ and the path count $m$ are separate;
  - lemma 4.1 is proved under a weaker notion of well-formed;
  - remark 2.8's "strictly equal" holds up to renaming path variables,
    because the renaming really is needed.
- **Time bounds.** Statements like "polynomial time" are proved in a cost
  model: a program that counts its own steps, with a proof that the count
  is bounded by a polynomial. That is a faithful reading of the paper's
  claims, but not a statement about real seconds on a real machine.
- **Proof engineering.** Some statements are cheap to state and expensive to
  check: Agda may unfold a definition into an enormous term while
  comparing two types. `PathSum/CLAUDE.md` records many such pitfalls and
  their fixes. For example, two modules once needed 10 GB of memory
  because of one pattern of case analysis, and now need under 1 GB.

## Check yourself

1. At $M = 3$, what numerator stores the coefficient $\tfrac14$? What about
   $\tfrac34$, and why are $\tfrac34$ and $-\tfrac14$ the same phase?
2. Using the rule table in 7.3, if a path-sum starts with $k = m = 4$ and
   one [HH], one [Elim] and one [ω] are applied, what are $k$ and $m$?
3. Why does `elim` require `suc (suc k)` in its type, while `hh` takes
   any `k`?

Next: [8. What machine checking found](08-findings.md).
