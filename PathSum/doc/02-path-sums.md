# 2. Path-sums

This chapter introduces the paper's central object (its section 2). A
path-sum describes a linear map on qubits by three pieces of data —
inputs, a phase polynomial and output polynomials — instead of a matrix.

## 2.1 Where the "paths" come from

Look again at the Hadamard gate. Written as a sum,

$$
H\lvert x\rangle = \frac{1}{\sqrt 2}\big(\lvert 0\rangle + (-1)^x\lvert 1\rangle\big)
= \frac{1}{\sqrt 2}\sum_{y \in \mathbb{Z}_2} (-1)^{xy}\lvert y\rangle
= \frac{1}{\sqrt 2}\sum_{y \in \mathbb{Z}_2} e\!\left(\tfrac{xy}{2}\right)\lvert y\rangle .
$$

The new variable $y$ ranges over the two branches the Hadamard creates.
Think of it as a fork in the road: an input $\lvert x\rangle$ takes both
"paths" $y = 0$ and $y = 1$, and along path $y$ it picks up the phase
$e(xy/2)$ and ends at $\lvert y\rangle$.

A circuit with several Hadamards forks several times; a run through the
circuit is then a choice of one branch at each Hadamard, a vector
$y \in \mathbb{Z}_2^m$ of **path variables**. The final state is the sum over
all paths of (phase of the path) × (where the path ends). This is
Feynman's *sum over paths* (or path integral), in a discrete form.

## 2.2 The definition

**Definition 2.1 (path-sum).** An $n$-qubit path-sum $\xi$ consists of

- an **input signature** $\lvert x_1 \cdots x_n\rangle$ (variables, or Boolean constants);
- a **phase polynomial** $P(x, y)$ in the inputs $x$ and path variables
  $y = y_1 \dots y_m$, with *dyadic* coefficients (fractions $a/2^b$);
- an **output signature** $\lvert f_1(x,y) \cdots f_n(x,y)\rangle$, each $f_i$
  a Boolean polynomial (coefficients in $\mathbb{Z}_2$).

It stands for the linear map

$$
U_\xi : \lvert x\rangle \;\mapsto\; \frac{1}{\sqrt{2^m}} \sum_{y \in \mathbb{Z}_2^m} e\big(P(x,y)\big)\, \lvert f(x,y)\rangle .
$$

Two facts about $P$ make life easier.

- Only $P$ **modulo 1** matters, because $e(\theta + 1) = e(\theta)$. So the
  phase $\tfrac12 y + \tfrac12 y = y$ is the same as $0$.
- Because the variables are Boolean, $x^2 = x$, so every polynomial can be
  taken **multilinear**: no variable appears squared.

A path variable is **internal** if it appears in no output $f_i$. Internal
variables are the ones a reduction can sum away (chapter 3).

## 2.3 Path-sums of the gates

Each gate of chapter 1 has a short path-sum. Only H needs a path variable.

| Gate | Path-sum |
|---|---|
| $X$ | $\lvert x\rangle \mapsto \lvert 1 \oplus x\rangle$ |
| $R_k$ (so $Z, S, T$) | $\lvert x\rangle \mapsto e\!\left(\tfrac{x}{2^k}\right)\lvert x\rangle$ |
| $H$ | $\lvert x\rangle \mapsto \frac{1}{\sqrt2}\sum_{y} e\!\left(\tfrac{xy}{2}\right)\lvert y\rangle$ |
| CNOT | $\lvert x_1 x_2\rangle \mapsto \lvert x_1, x_1 \oplus x_2\rangle$ |
| CZ | $\lvert x_1 x_2\rangle \mapsto e\!\left(\tfrac{x_1x_2}{2}\right)\lvert x_1 x_2\rangle$ |

Path-sums can also be written straight down as **specifications**, and
this is where they shine (the paper's example 2.2):

$$
\begin{aligned}
\mathrm{Toffoli}_n &: \lvert x_1 \cdots x_n\rangle \mapsto \lvert x_1 \cdots x_{n-1},\; x_n \oplus x_1x_2\cdots x_{n-1}\rangle,\\
\mathrm{QFT}_n &: \lvert x\rangle \mapsto \frac{1}{\sqrt{2^n}}\sum_{y \in \mathbb{Z}_2^n} e\!\left(\tfrac{[x]\,[y]}{2^n}\right)\lvert y\rangle,
\end{aligned}
$$

where $[x] = x_1 + 2x_2 + \dots + 2^{n-1}x_n$ is the integer a bit string
stands for. These are exactly how a textbook describes the quantum Fourier
transform, so a specification is easy for a human to read and check.

## 2.4 Composing path-sums

To get the path-sum of a circuit, compose the path-sums of its gates.
Sequential composition is **substitution**: feed the outputs of the first
path-sum into the inputs of the second, rename the second's path
variables so they do not clash, and add the phases.

**Example: $HH$.** The first H gives
$\frac1{\sqrt2}\sum_{y_1} e(\tfrac{x y_1}{2})\lvert y_1\rangle$. The second H,
with its own path variable $y_2$, maps $\lvert x'\rangle$ to
$\frac1{\sqrt2}\sum_{y_2} e(\tfrac{x' y_2}{2})\lvert y_2\rangle$. Substitute
$x' \leftarrow y_1$ and multiply out:

$$
HH : \lvert x\rangle \;\mapsto\; \frac{1}{\sqrt{2^2}} \sum_{y_1, y_2} e\!\left(\tfrac{x y_1 + y_1 y_2}{2}\right) \lvert y_2\rangle .
$$

This is the paper's section 3.1 example. It does not *look* like the
identity yet; chapter 3 will show that it is.

**A catch: XOR inside a phase.** Output polynomials live in
$\mathbb{Z}_2$, where $1 + 1 = 0$; phases live in the dyadic rationals,
where $1 + 1 = 2$. When a substitution puts an output into a phase, the
Boolean polynomial must first be **lifted** to an ordinary polynomial with
the same values on bits. The paper's lifting is

$$
\overline{x^\alpha} = x^\alpha, \qquad \overline{P \oplus Q} = \overline P + \overline Q - 2\,\overline P\,\overline Q ,
$$

so for instance $\overline{x \oplus y} = x + y - 2xy$ (check it on the four
inputs). **Lemma 2.5** says the lifting is correct: on bits,
$\overline P(x) = P(x) \bmod 2$.

**Example: CNOT then T on the second wire.** After CNOT the second wire
holds $x_1 \oplus x_2$, so T contributes the phase
$\tfrac18(x_1 \oplus x_2)$, lifted to
$\tfrac18(x_1 + x_2 - 2x_1x_2) = \tfrac18 x_1 + \tfrac18 x_2 - \tfrac14 x_1x_2$.

**Proposition 2.7** says composition is correct: the operator of the
composite is the product of the operators. (Its first half, about
"well-formed" path-sums, turned out to be false; see chapter 8.)

Doing this gate by gate for a whole circuit $C$ gives its **path-sum
interpretation** $[\![C]\!]$ (the paper's definition 2.9), and
**Proposition 2.10** says it is right: the operator of $[\![C]\!]$ is the
circuit's matrix.

## 2.5 How big does a path-sum get?

Every Hadamard adds one path variable, and every gate adds a few terms to
the phase, so a circuit's path-sum stays small. Over $\{H, \mathrm{CNOT}, R_k\}$
the outputs stay *linear* (XORs of variables) and the phase polynomial has
bounded degree. To say how bounded, the paper defines the **order** of a
term $\tfrac{a}{2^b}x^\alpha$ with $a$ odd as $b + \lvert\alpha\rvert - 1$
(definition 2.11), where $\lvert\alpha\rvert$ is the number of variables in
the monomial. For example

$$
\operatorname{ord}\!\left(\tfrac12\right) = 0, \qquad
\operatorname{ord}\!\left(\tfrac12 x_1 + \tfrac12 x_2\right) = 1, \qquad
\operatorname{ord}\!\left(\tfrac32 x_2 + \tfrac12 x_1x_2x_3\right) = 3 .
$$

Substituting a linear Boolean polynomial never raises the order
(**Lemma 2.13**), so a Clifford circuit's phase has order at most 2, and a
circuit over $\{H, \mathrm{CNOT}, R_k\}$ has order at most $\max(2, k)$.
The paper says "degree at most $k$" (**Proposition 2.14**); that is false
for $k = 1$ (chapter 8). Either way, the size is polynomial in the
circuit's size (**Corollary 2.15**).

## 2.6 Equal operators, different path-sums

Many path-sums have the same operator: $HH$ above and the identity
$\lvert x\rangle \mapsto \lvert x\rangle$ are an example. So the paper
defines **equivalence** $\xi_1 \equiv \xi_2$ to mean $U_{\xi_1} = U_{\xi_2}$
(definition 2.3). A path-sum is **well-formed** if its operator is an
isometry or a partial isometry (definition 2.4); the path-sum of a circuit
always is, but a hand-written specification might not be:
$\lvert x\rangle \mapsto \lvert 0\rangle$ is a perfectly good path-sum
whose operator is not an isometry.

The question "is circuit $C$ the identity?" becomes "is
$[\![C]\!] \equiv (\lvert x\rangle \mapsto \lvert x\rangle)$?". The next
chapter shows how to answer it by rewriting.

## Check yourself

1. Write the path-sum of $S^\dagger = S^3$ and of the SWAP gate
   $\lvert x_1x_2\rangle \mapsto \lvert x_2x_1\rangle$.
2. Compose $H$ then $T$ then $H$ into one path-sum.
3. Check $\overline{x \oplus y \oplus z} = x + y + z - 2xy - 2xz - 2yz + 4xyz$
   on all eight inputs.
4. What is the order of $\tfrac14 x_1 x_2$? Of $\tfrac38 x_1$?

Next: [3. Rewriting path-sums](03-rewriting.md).
