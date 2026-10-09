# 9. Exercises and solutions

Part A has longer exercises; try them before reading the solutions in
part B. Part C answers the check-yourself questions at the end of each
chapter. Throughout, $e(\theta) = e^{2\pi i\theta}$ and phases are taken
modulo 1.

## A. Exercises

**9.1 (path-sums of gates).** Write path-sums for $X$, $S^\dagger$, the SWAP
gate $\lvert x_1x_2\rangle \mapsto \lvert x_2x_1\rangle$, and $X \otimes Z$.

**9.2 (a CNOT from a CZ).** The circuit "H on wire 2, CZ on wires 1 and 2,
H on wire 2" implements CNOT. Compute its path-sum and reduce it to
$\lvert x_1x_2\rangle \mapsto \lvert x_1, x_1 \oplus x_2\rangle$.

**9.3 (a stuck path-sum that is fine).** Compute the path-sum of $HTH$.
Show that no rule of figure 2 applies. Is that a problem?

**9.4 (lifting).** Using the lifting rules of chapter 2, compute
$\overline{x \oplus y \oplus z}$ and check it on all eight inputs.

**9.5 (orders).** Compute the order of each term, and of the whole
polynomial: $\tfrac14 x_1 + \tfrac12 x_1x_2 + \tfrac18 x_1x_2x_3$.

**9.6 (the [ω] calculation).** Verify $1 + e(\tfrac14 + \tfrac12 q) = \sqrt2\, e(\tfrac18 - \tfrac14 q)$
for $q = 0$ and $q = 1$ by computing both sides as complex numbers.

**9.7 (a refutation).** Use Lemma 4.1 or 4.2 to show the circuit $HH S$
(H, then H, then S) is not the identity, without computing a matrix.

**9.8 (Lemma 4.2's hypothesis).** Find a polynomial $Q$ in one input
variable $x$ that is non-zero, integer-valued and has no path variables,
but for which the branches of $y_0$ in $e(\tfrac12 y_0 Q)$ never cancel.
Why does that not contradict the corrected lemma?

**9.9 (Clifford hierarchy).** Show $S \in C_2$ by computing $SXS^\dagger$ and
$SZS^\dagger$. Then show $T \in C_3 \setminus C_2$.

**9.10 (hands-on Agda).** Create a file `PathSum/MyTutorial.agda` with
the contents below, and typecheck it from the repository root with
`agda +RTS -M6G -RTS PathSum/MyTutorial.agda`. Before running it, predict:
why is the coefficient $+4$? Why is $S^4$ the identity but not $S^3$?

```agda
{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.MyTutorial where

open import Data.Fin.Base using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using ([]; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (True; False)

open import PathSum.Base using (phase)
open import PathSum.Polynomial using (_∪ᵐ_)
open import PathSum.Corollary 0 using (circuit-decidable)
open import PathSum.Examples.Base using (xᵐ; yᵐ; Circuit; H; S)
open import PathSum.Examples.Section3 using (HHᵖ)

-- (a) the coefficient of x·y₁ in the paper's path-sum for HH, in eighths

_ : phase HHᵖ (xᵐ zero ∪ᵐ yᵐ zero) ≡ + 4
_ = refl

-- (b) corollary 4.4's decision procedure, run by the typechecker

S⁴ : Circuit 1
S⁴ = S zero ∷ S zero ∷ S zero ∷ S zero ∷ []

S³ : Circuit 1
S³ = S zero ∷ S zero ∷ S zero ∷ []

S⁴-decided : True (circuit-decidable S⁴)
S⁴-decided = tt

S³-decided : False (circuit-decidable S³)
S³-decided = tt

-- (c) H S S H is not the identity (it is X)

HSSH : Circuit 1
HSSH = H zero ∷ S zero ∷ S zero ∷ H zero ∷ []

HSSH-decided : False (circuit-decidable HSSH)
HSSH-decided = tt
```

Then try changing `S³-decided`'s type to `True (circuit-decidable S³)` and
read Agda's error. Finally, add a circuit of your own and decide it.

**9.11 (reading Agda).** State in words what each of these says:

```agda
lemma-4-1-circuit : (C : Circuit n) → (⟦ C ⟧ ≋ idPS ⇔ ⟦ C ⟧ᴿ ≋ idPS)
circuit-decidable : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
prop-2-14-false-at-1 :
  ¬ (∀ (C : K.Circuit 1) → K.level C ≤ 1 → K.Deg≤ 1 (phase K.⟦ C ⟧))
```

**9.12 (write a type).** Write the Agda type of "every chain of rewrite
steps preserves equivalence", using `_⟶*_` and `_≋_`. (The development
calls it `⟶*-sound`.)

## B. Solutions

**9.1.** $X: \lvert x\rangle \mapsto \lvert 1\oplus x\rangle$.
$S^\dagger: \lvert x\rangle \mapsto e(-\tfrac x4)\lvert x\rangle = e(\tfrac{3x}4)\lvert x\rangle$.
SWAP: $\lvert x_1x_2\rangle \mapsto \lvert x_2x_1\rangle$.
$X\otimes Z: \lvert x_1x_2\rangle \mapsto e(\tfrac{x_2}2)\lvert 1\oplus x_1, x_2\rangle$.
None needs a path variable.

**9.2.** The first H gives path variable $y_1$ with phase $\tfrac12 x_2y_1$ and
wire 2 holding $y_1$. CZ adds $\tfrac12 x_1y_1$. The second H gives $y_2$ with
$\tfrac12 y_1y_2$. So

$$
\lvert x_1x_2\rangle \mapsto \tfrac12\sum_{y_1,y_2} e\big(\tfrac12 y_1(y_2 + x_1 + x_2)\big)\lvert x_1 y_2\rangle .
$$

$y_1$ is internal: [HH] substitutes $y_2 \leftarrow x_1 \oplus x_2$, and [Elim]
removes $y_2$, leaving $\lvert x_1, x_1\oplus x_2\rangle$.

**9.3.** $\tfrac12\sum_{y_1,y_2} e(\tfrac12 xy_1 + \tfrac18 y_1 + \tfrac12 y_1y_2)\lvert y_2\rangle$. The
only internal variable is $y_1$, and its part is $\tfrac18 y_1 + \tfrac12 y_1(x\oplus y_2)$.
[Elim] needs it to vanish, [HH] needs only halves, and [ω] needs exactly
$\tfrac14 y_1$; $\tfrac18$ fits none. That is not a problem: $HTH$ is not the
identity and is not a Clifford circuit. Its matrix genuinely has four
non-zero entries, so some path variable must remain.

**9.4.** $\overline{x\oplus y} = x + y - 2xy$. Then
$\overline{(x\oplus y)\oplus z} = (x+y-2xy) + z - 2(x+y-2xy)z
= x + y + z - 2xy - 2xz - 2yz + 4xyz$.
For instance at $x=y=z=1$: $3 - 6 + 4 = 1 = 1\oplus1\oplus1$.

**9.5.** $\tfrac14 x_1$: $b = 2$, one variable, order $2$.
$\tfrac12x_1x_2$: $b = 1$, two variables, order $2$.
$\tfrac18x_1x_2x_3$: $b = 3$, three variables, order $5$.
The polynomial's order is the maximum, $5$.

**9.6.** $q = 0$: $1 + e(\tfrac14) = 1 + i$, and $\sqrt2\,e(\tfrac18) = \sqrt2(\tfrac{1}{\sqrt2} + \tfrac{i}{\sqrt2}) = 1 + i$.
$q = 1$: $1 + e(\tfrac34) = 1 - i$, and $\sqrt2\,e(-\tfrac18) = 1 - i$.

**9.7.** $HH$ reduces to $\lvert x\rangle$, so $HHS$ reduces to
$\lvert x\rangle \mapsto e(\tfrac x4)\lvert x\rangle$, with no path variables. Its
phase $\tfrac14 x$ is not $0$ modulo 1 (at $x = 1$ it is $\tfrac14$), so its
diagonal entry at $x = 1$ is $i \ne 1$ and it is not the identity. (This
is `HHS-decided` in `PathSum/Examples/Clifford.agda`.)

**9.8.** $Q = 2x$ (or $Q = 2$, or $Q = 4x$): then $\tfrac12y_0Q$ is an integer,
$e(\tfrac12y_0Q) = 1$, and both branches contribute $+1$. The corrected
lemma needs $Q$ to be **odd** at some input; every such $Q$ is even everywhere.

**9.9.** $S = \mathrm{diag}(1, i)$, so $SZS^\dagger = Z$ and
$SXS^\dagger = \begin{pmatrix}0 & -i\\ i & 0\end{pmatrix} = iXZ$, a Pauli
(it is $Y$). So $S \in C_2$. For $T = \mathrm{diag}(1,\omega)$:
$TZT^\dagger = Z$ and $TXT^\dagger = \begin{pmatrix}0 & \omega^{-1}\\ \omega & 0\end{pmatrix} = \omega^{-1}SX$.
That is not a Pauli (its entries are not in $\{0,\pm1,\pm i\}$), so $T \notin C_2$,
but it is a Clifford times a phase, which is in $C_2$, so $T \in C_3$.

**9.10.** (a) $HH^p$'s phase is $\tfrac12(xy_1 + y_1y_2)$, and $\tfrac12 = \tfrac48$:
coefficients are numerators over $2^M = 8$. (b) $S^4$ has phase
$4\cdot\tfrac x4 = x$, an integer, so it is the identity; $S^3$ has
phase $\tfrac{3x}4$, which is $\tfrac34$ at $x = 1$. (c) $HSSH = HZH = X$
flips its input, so its diagonal is $0$. In each case `circuit-decidable`
computes a `yes` or a `no`, and `True`/`False` check which one it was, by
running the algorithm inside the typechecker. Changing (b) to the wrong
answer gives a type error, because `True (no …)` is the empty type.

**9.11.**
- `lemma-4-1-circuit`: a circuit over $\{H, S, CZ\}$ is the identity
  exactly when its restricted path-sum is.
- `circuit-decidable`: there is an algorithm that, given any such circuit,
  correctly answers whether it is the identity.
- `prop-2-14-false-at-1`: it is not the case that every one-qubit circuit
  of level ≤ 1 over $\{H, \mathrm{CNOT}, R_k\}$ has a phase of degree ≤ 1.
  That is, proposition 2.14 fails at $k = 1$.

**9.12.**

```agda
⟶*-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶* ζ → ξ ≋ ζ
```

## C. Answers to the check-yourself questions

**Chapter 1.**
1. $S = \mathrm{diag}(1,i)$; $S^2 = \mathrm{diag}(1,-1) = Z$; $T^2 = \mathrm{diag}(1,\omega^2) = \mathrm{diag}(1,i) = S$.
2. $H\lvert0\rangle = \lvert+\rangle$, $H\lvert1\rangle = \lvert-\rangle$, and
   $H\lvert+\rangle = \tfrac1{\sqrt2}(\lvert+\rangle + \lvert-\rangle) = \lvert0\rangle$.
3. The inverse of the empty circuit is empty, so the miter is $C$ itself.
4. $XZ = \begin{pmatrix}0&-1\\1&0\end{pmatrix}$ and $ZX = \begin{pmatrix}0&1\\-1&0\end{pmatrix} = -XZ$.

**Chapter 2.**
1. $S^\dagger: \lvert x\rangle \mapsto e(-\tfrac x4)\lvert x\rangle$; SWAP: $\lvert x_1x_2\rangle\mapsto\lvert x_2x_1\rangle$.
2. $\lvert x\rangle \mapsto \tfrac12\sum_{y_1,y_2} e(\tfrac12xy_1 + \tfrac18y_1 + \tfrac12y_1y_2)\lvert y_2\rangle$ (see 9.3).
3. See 9.4.
4. $\tfrac14x_1x_2$: $2 + 2 - 1 = 3$. $\tfrac38x_1$: $3 + 1 - 1 = 3$.

**Chapter 3.**
1. The phase is $\tfrac12y_0(y_1 \oplus x)$: [HH] substitutes $y_1 \leftarrow x$
   (the output is unchanged), then [Elim] removes $y_1$. The result is
   $\lvert x\rangle\mapsto\lvert x\rangle$.
2. If $y_0$ is in the output, its two branches end at **different** basis
   vectors, so they never meet and cannot cancel. $H$'s own path-sum
   $\tfrac1{\sqrt2}\sum_{y_0} e(\tfrac12xy_0)\lvert y_0\rangle$ is an example: summing
   $y_0$ away would be wrong.
3. $S^4$ has phase $x$, which is $0$ modulo 1, and no path variables: it is
   already the identity, so no rule is needed.
4. The phase is $\tfrac12xy_1 + \tfrac12y_1 + \tfrac12y_1y_2 = \tfrac12y_1(y_2 \oplus x \oplus 1)$:
   [HH] substitutes $y_2 \leftarrow 1\oplus x$, then [Elim]. The result is
   $\lvert x\rangle\mapsto\lvert 1\oplus x\rangle$.

**Chapter 4.**
1. $X$ maps $\lvert x\rangle$ to $\lvert 1\oplus x\rangle$, so no path ends at
   $\lvert x\rangle$: every diagonal entry is 0, not 1.
2. $Q'$ is then a non-zero linear Boolean polynomial in the inputs, odd at
   some input, so by Lemma 4.2 that diagonal entry is 0 and the path-sum
   is not the identity.
3. $HXH = \tfrac12\begin{pmatrix}1&1\\1&-1\end{pmatrix}\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&1\\1&-1\end{pmatrix} = \begin{pmatrix}1&0\\0&-1\end{pmatrix} = Z$, and similarly $HZH = X$.
4. See 9.9.

**Chapter 5.**
1. $C' ; C^\dagger$ has matrix $U_{C}^\dagger U_{C'}$, which is $I$ exactly when
   $U_{C'} = U_C$, however many gates each circuit has.
2. With $x_1, y_1$ the low bits, the carry out is
   $x_2y_2 \oplus (x_2\oplus y_2)x_1y_1 = x_2y_2 \oplus x_1x_2y_1 \oplus x_1y_1y_2$: three monomials.
3. $W(00) = 2$, $W(10) = 2$, $W(01) = 2$, $W(11) = -2$.

**Chapter 6.**
1. `(m n : ℕ) → m + n ≡ n + m`.
2. `no p`, where `p : ¬ (⟦ C ⟧ ≋ idPS)` turns any claimed proof of
   equivalence into a contradiction.
3. With no path variables the operator is $\lvert x\rangle \mapsto e(P(x))\lvert f(x)\rangle$
   divided by $\sqrt{2^k}$; with $k > 0$ that can never be the identity, and
   with path variables left, "syntactically the identity" would not
   determine the operator.

**Chapter 7.**
1. $\tfrac14 = \tfrac28$ is stored as $2$, and $\tfrac34$ as $6$; $6 \equiv -2 \pmod 8$, and
   $\tfrac34 - (-\tfrac14) = 1$ is an integer.
2. [HH]: $(k, m) = (4, 3)$; [Elim]: $(2, 2)$; [ω]: $(1, 1)$.
3. [Elim] removes two factors of $1/\sqrt2$, so there must be at least two;
   [HH] removes none.

**Chapter 8.**
1. $Q = 2$, or $Q = 2x_2$, or $Q = 4x_1x_2$: any even-valued $Q$.
2. $P_0 = \begin{pmatrix}1&0\\0&0\end{pmatrix}$, $P_+ = \tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix}$,
   $A = P_+P_0 = \tfrac12\begin{pmatrix}1&0\\1&0\end{pmatrix}$. Then
   $A^\dagger A = \tfrac12\begin{pmatrix}1&0\\0&0\end{pmatrix}$ and
   $(A^\dagger A)^2 = \tfrac14\begin{pmatrix}1&0\\0&0\end{pmatrix} \ne A^\dagger A$, so
   $A^\dagger A$ is not a projection and $A$ is not a partial isometry.
3. Every circuit with a Hadamard has the degree-2 term $\tfrac12xy$; at
   $k = 1$ the claim allows degree 1 only, at $k = 2$ it allows degree 2.

Back to the [index](README.md).
