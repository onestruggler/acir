# 3. Rewriting path-sums

A path-sum can have many path variables and still describe a simple map:
$HH$ in chapter 2 had two, yet it is the identity. This chapter explains
the paper's **rewrite rules** (its section 3), which remove path
variables one at a time by recognising **interference**: paths that cancel
or reinforce each other.

## 3.1 Interference, by hand

Take $HH$ again:

$$
\lvert x\rangle \;\mapsto\; \frac{1}{2} \sum_{y_1, y_2} e\!\left(\tfrac{x y_1 + y_1 y_2}{2}\right) \lvert y_2\rangle
= \frac{1}{2} \sum_{y_2} \Big(\sum_{y_1} (-1)^{y_1 (x + y_2)}\Big) \lvert y_2\rangle .
$$

The variable $y_1$ is **internal**: it is not in the output. Summing over it
first, the inner sum is $1 + (-1)^{x+y_2}$, which is $2$ when $y_2 = x$ and
$0$ when $y_2 \ne x$. The two paths $y_1 = 0, 1$ **reinforce** each other
when $y_2 = x$ and **cancel** otherwise. So only $y_2 = x$ survives:

$$
\lvert x\rangle \;\mapsto\; \frac{1}{2}\cdot 2 \,\lvert x\rangle = \lvert x\rangle .
$$

The general pattern: whenever an internal variable $y_0$ enters the phase
only as $\tfrac12 y_0 \cdot Q$, its two branches cancel where $Q$ is odd and
double where $Q$ is even. The rules below package this and two similar
patterns as **local, mechanical** transformations of the polynomials, so
a computer can apply them without ever expanding a sum.

## 3.2 The four rules of figure 2

In each rule $y_0$ is an **internal** path variable (in no output),
quotients $Q$ are Boolean-valued polynomials, and $R$ and $Q$ do not mention
$y_0$. The rules are written for $y_0$, but they apply to any internal
variable. Here $y \in \mathbb{Z}_2^m$ are the remaining path variables.

**[Elim] — a variable that does nothing.** If $y_0$ appears nowhere (not in
the phase, not in the outputs), summing over it just doubles everything:

$$
\frac{1}{\sqrt{2^{m+2}}}\sum_{y_0}\sum_{y} e(P)\lvert f\rangle
\;\longrightarrow\;
\frac{1}{\sqrt{2^{m}}}\sum_{y} e(P)\lvert f\rangle .
$$

Why: $\sum_{y_0} 1 = 2$ and $2/\sqrt{2^{m+2}} = 1/\sqrt{2^m}$. Notice that one
path variable disappears but **two** factors of $1/\sqrt2$ go with it.

**[HH] — interference that solves an equation.** If the phase is
$\tfrac12 y_0(y_i \oplus Q) + R$ where $y_i$ does not occur in $Q$,

$$
\frac{1}{\sqrt{2^{m+1}}}\sum_{y_0}\sum_{y} e\big(\tfrac12 y_0 (y_i + Q) + R\big)\lvert f\rangle
\;\longrightarrow\;
\frac{1}{\sqrt{2^{m+1}}}\sum_{y} e\big(R[y_i \leftarrow Q]\big)\lvert f[y_i \leftarrow Q]\rangle .
$$

Why: as in 3.1, the sum over $y_0$ is $2$ on the paths with $y_i = Q$ and
$0$ elsewhere, so we may **substitute** $Q$ for $y_i$ everywhere, the phase
getting the lifted $\overline Q$. After the substitution $y_i$ no longer
occurs, so it is a do-nothing variable and [Elim] can remove it next; this
is why reductions often say "[HH, Elim]". The name comes from $HH = I$.

**[ω] — interference that leaves a phase.** If the phase is
$\tfrac14 y_0 + \tfrac12 y_0 Q + R$,

$$
\frac{1}{\sqrt{2^{m+1}}}\sum_{y_0}\sum_{y} e\big(\tfrac14 y_0 + \tfrac12 y_0 Q + R\big)\lvert f\rangle
\;\longrightarrow\;
\frac{1}{\sqrt{2^{m}}}\sum_{y} e\big(\tfrac18 - \tfrac14 \overline{Q} + R\big)\lvert f\rangle .
$$

Why: the sum over $y_0$ is $1 + e(\tfrac14 + \tfrac12 Q) = 1 + i(-1)^Q$, which is
$1 + i = \sqrt2\,\omega$ when $Q = 0$ and $1 - i = \sqrt2\,\omega^{-1}$ when
$Q = 1$, that is $\sqrt2\, e(\tfrac18 - \tfrac14 Q)$ in both cases. The
$\sqrt2$ cancels one normalisation factor. The rule comes from the identity
$(SH)^3 = \omega I$.

**[Case] — two interferences, chosen by an input bit.** The fourth rule
handles a phase that can be read in two ways, depending on an input bit
$x$: as $\tfrac14 y_i x + \tfrac12 y_i(y_j + Q) + R$ and as
$\tfrac14 y_j(1-x) + \tfrac12 y_j(y_i + Q') + R'$, with $y_i, y_j$ internal.
When $x = 0$ the first form is an [HH] pattern at $y_i$, and when $x = 1$
the second is one at $y_j$. The rule removes both variables at once,
giving the phase $(1-x)R[y_j \leftarrow Q] + x R'[y_i \leftarrow Q']$. The
paper introduces it for one particular two-qubit Clifford+T identity, and
the formalisation confirmed that this identity cannot be proved without
it (module `PathSum/Examples/CaseIdentity.agda`).

**Proposition 3.1 (correctness).** Every rule preserves the operator: if
$\xi \longrightarrow^* \xi'$ then $\xi \equiv \xi'$. The calculations above
are the proof.

## 3.3 Worked reductions

**$HH = I$.** The phase $\tfrac12(x y_1 + y_1 y_2) = \tfrac12 y_1 (y_2 \oplus x)$ is an
[HH] pattern at $y_1$, with $y_i = y_2$ and $Q = x$:

$$
\frac{1}{2}\sum_{y_1,y_2} e\big(\tfrac12 y_1(y_2 + x)\big)\lvert y_2\rangle
\;\xrightarrow{\text{[HH]}}\;
\frac12\sum_{y_2} \lvert x\rangle
\;\xrightarrow{\text{[Elim]}}\;
\lvert x\rangle .
$$

**The Toffoli gate (example 3.3).** A standard Clifford+T implementation
of the Toffoli gate has the path-sum
$\frac12\sum_{y_1,y_2} e\big(\tfrac12(x_3y_1 + x_1x_2y_1 + y_1y_2)\big)\lvert x_1x_2y_2\rangle$.
Factor out $y_1$: the phase is $\tfrac12 y_1 (y_2 \oplus x_3 \oplus x_1x_2)$, so [HH]
at $y_1$ substitutes $y_2 \leftarrow x_3 \oplus x_1x_2$ in the output, and
[Elim] removes $y_2$:

$$
\lvert x_1x_2x_3\rangle \;\mapsto\; \lvert x_1, x_2, x_3 \oplus x_1x_2\rangle .
$$

That is the Toffoli specification, obtained **symbolically**, for all
eight inputs at once.

**$(SH)^3 = \omega I$ (example B.1).** The circuit applies H, S, H, S, H, S.
Each H adds a path variable and each S adds $\tfrac14$ times the current
wire value, so

$$
P = \tfrac12 x y_1 + \tfrac14 y_1 + \tfrac12 y_1 y_2 + \tfrac14 y_2 + \tfrac12 y_2 y_3 + \tfrac14 y_3,
\qquad \text{output } \lvert y_3\rangle,\quad \text{normalisation } \tfrac{1}{\sqrt{2^3}} .
$$

1. $y_1$ is internal and occurs as $\tfrac14 y_1 + \tfrac12 y_1(x \oplus y_2)$: an
   [ω] pattern with $Q = x \oplus y_2$, whose lift is $x + y_2 - 2xy_2$. The
   new phase is
   $\tfrac18 - \tfrac14(x + y_2 - 2xy_2) + \tfrac14 y_2 + \tfrac12 y_2y_3 + \tfrac14 y_3
   = \tfrac18 - \tfrac14 x + \tfrac12 y_2(x \oplus y_3) + \tfrac14 y_3$
   (using $\tfrac12 x y_2 + \tfrac12 y_2 y_3 = \tfrac12 y_2 (x \oplus y_3)$ modulo 1),
   with normalisation $1/\sqrt{2^2}$.
2. $y_2$ is internal and occurs as $\tfrac12 y_2(y_3 \oplus x)$: [HH] substitutes
   $y_3 \leftarrow x$, giving phase $\tfrac18 - \tfrac14 x + \tfrac14 x = \tfrac18$ and
   output $\lvert x\rangle$.
3. [Elim] removes the leftover $y_3$.

The result is $\lvert x\rangle \mapsto e(\tfrac18)\lvert x\rangle = \omega\lvert x\rangle$.
(The path-sum *printed* in the paper's appendix has coefficients $\tfrac68$
instead of $\tfrac28$; that one is actually the identity. See chapter 8.)

## 3.4 Normal forms, termination, and what can go wrong

Every rule removes at least one path variable, so any sequence of rewrites
**terminates** after at most $m$ steps. A path-sum where no rule applies is
a **normal form**. Two warnings:

- **Normal forms are not unique.** Different rule choices can end at
  different irreducible path-sums with the same operator.
- **Getting stuck is possible.** Section 4 of the paper exhibits a
  Clifford+T circuit equal to the identity whose path-sum is irreducible
  with eight path variables left. So the rules alone cannot prove every
  true identity: the calculus is **incomplete**. The paper's remedy is to
  expand the leftover variables by brute force (exponential in their
  number); the formalisation proves that remedy correct
  (`PathSum/Expand.agda`).

**Proposition 3.2** claims each rule can be matched in polynomial time, so
normal forms are reached in polynomial time. The first half is true. The
second needs more care: a rule's result can be much larger than its input,
and chapter 8 describes a family of path-sums whose every normal form is
exponentially large. For Clifford circuits (order 2) the claim does hold.

## Check yourself

1. Which rule applies to $\frac{1}{2}\sum_{y_0,y_1} e(\tfrac12 y_0 y_1 + \tfrac12 y_0 x)\lvert x\rangle$,
   and what is the result?
2. Why must $y_0$ be internal for [HH]? Construct a small path-sum where
   $y_0$ is in the output and the [HH] calculation breaks.
3. Reduce the path-sum of $S^4$ (no Hadamards!) and confirm it is the
   identity. Which rule did you need? (Trick question.)
4. Reduce $HSSH$ (= $HZH$ = $X$) to $\lvert x\rangle \mapsto \lvert 1\oplus x\rangle$.

Next: [4. Deciding Clifford circuits](04-clifford.md).
