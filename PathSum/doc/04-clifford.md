# 4. Deciding Clifford circuits

Chapter 3 ended with bad news: rewriting can get stuck on a circuit that
*is* the identity. This chapter covers the paper's section 4, which shows
that for **Clifford circuits** nothing goes wrong: three extra ideas turn
the rewrite rules into a complete, polynomial-time test of whether a
circuit is the identity (Corollary 4.4). It ends with the Clifford
hierarchy from section 1.6.

## 4.1 The question

Given a circuit $C$ over $\{H, S, \mathrm{CNOT}\}$ (or $\{H, S, \mathrm{CZ}\}$),
decide whether $[\![C]\!] \equiv \big(\lvert x\rangle \mapsto \lvert x\rangle\big)$.
To compare two circuits, apply this to the miter $C_1 ; C_2^\dagger$.

## 4.2 Look only at the diagonal (Lemma 4.1)

The entry of the operator at row $x$, column $x$ — "how much of
$\lvert x\rangle$ comes back as $\lvert x\rangle$" — is the sum over just
those paths that end where they started:

$$
\langle x\vert U_\xi\vert x\rangle = \frac{1}{\sqrt{2^m}} \sum_{y \,:\, f(x,y) = x} e\big(P(x,y)\big).
$$

**Lemma 4.1.** If $\xi$ is well-formed (its operator is an isometry or a
partial isometry), then $\xi$ is the identity **exactly when every diagonal
entry is 1**.

*Why.* $U\lvert x\rangle$ has length at most 1, and its $\lvert x\rangle$
component is 1. A vector of length at most 1 with one component equal to 1
has every other component equal to 0, so $U\lvert x\rangle = \lvert x\rangle$.

Well-formedness is essential. The map $\lvert x\rangle \mapsto \lvert x\rangle + \lvert 1 \oplus x\rangle$
is a valid path-sum whose diagonal entries are all 1, but it is not the
identity. (The formalisation proves this counterexample too.)

So instead of $\xi$ we may study the **restriction** $\xi\vert_{f(x,y)=x}$,
which keeps only the paths satisfying $f(x,y) = x$. For a Clifford circuit
the outputs $f_i$ are **linear** (XORs of variables), so $f(x,y) = x$ is a
system of linear equations over $\mathbb{Z}_2$ in the unknowns $y$.
Gaussian elimination solves it: each equation
$y_j \oplus (\text{rest}) = x_i$ lets us substitute for $y_j$ and remove it.
If some equation has no solution for some input, that diagonal entry is 0
and the circuit is not the identity. After this step every remaining
path variable is **internal**.

## 4.3 Spotting a non-identity (Lemma 4.2)

If an internal $y_0$ occurs in the phase as $\tfrac12 y_0 Q(x) + R$, where $Q$
mentions no path variables, then at every input where $Q(x)$ is **odd**,
the two branches of $y_0$ cancel on every path, so the diagonal entry
there is $0$ — the path-sum is not the identity.

The paper states this for "$Q$ a non-zero integer-valued polynomial", and
that is not enough: $Q = 2x_1$ is non-zero, but $\tfrac12 y_0 \cdot 2x_1 = y_0x_1$
is an integer, so the branches never cancel. The correct condition is
**$Q$ is odd for some input**; for a Boolean-valued $Q$, "non-zero" does
mean that, which is the case the paper actually uses. (Chapter 8 has the
formal counterexample.)

## 4.4 Clifford path-sums never get stuck (Lemma 4.3)

Here is why Clifford circuits are special. Their phases have **order at
most 2**, so for any internal variable $y_0$ the phase can be written

$$
P = y_0 \Big(\tfrac14 a + \tfrac12 b\, Q'\Big) + R, \qquad a, b \in \{0,1\},
$$

with $Q'$ a linear Boolean polynomial not mentioning $y_0$. There are three
cases.

| Case | Rule | Why it applies |
|---|---|---|
| $a = 0, b = 0$ | [Elim] | $y_0$ does not occur at all |
| $a = 0, b = 1$, $Q'$ mentions some path variable $y_i$ | [HH] | write $Q' = y_i \oplus Q''$ |
| $a = 0, b = 1$, $Q'$ mentions only inputs | — | Lemma 4.2: not the identity |
| $a = 1$ | [ω] | the phase has the [ω] shape |

**Lemma 4.3 (progress and preservation).** If a path-sum is the
identity, has phase of order at most 2 and only internal path variables,
then some rule applies, and the result again has order at most 2.

So on an identity Clifford path-sum, rewriting never gets stuck while
path variables remain. When none remain, the path-sum is
$\lvert x\rangle \mapsto e(P(x))\lvert f(x)\rangle$ with no sums at all, and
checking it is the identity means checking $f(x) = x$ and $P \equiv 0$
(mod 1), which can be read off the coefficients.

## 4.5 The algorithm (Corollary 4.4)

Putting it together, to decide whether a Clifford circuit $C$ is the
identity:

1. compute $[\![C]\!]$, gate by gate (polynomial size, chapter 2);
2. restrict to $f(x,y) = x$ by Gaussian elimination; if impossible, answer **no**;
3. rewrite with [Elim], [HH], [ω]; each step removes a variable and keeps order ≤ 2;
4. if Lemma 4.2's pattern shows up, answer **no**;
5. when no path variables remain, answer **yes** exactly when the
   outputs are $x$ and the phase vanishes.

**Corollary 4.4.** This decides whether a Clifford circuit is the
identity, in time polynomial in its size.

The formalisation proves this for circuits over $\{H, S, \mathrm{CZ}\}$, and
also for the paper's own gate set $\{H, \mathrm{CNOT}, R_k\}$ at level ≤ 2
by the same Gaussian elimination route. It also found that the paper's
proof needs one more fact: since step 3 may use any rule, not just the
ones Lemma 4.3 picks, **every** rule must keep the order at most 2. That
is true, and is proved in `PathSum/Full/Clifford.agda`. The
polynomial-time claim is proved in an explicit cost model that counts
steps (`PathSum/Cost/`).

## 4.6 The Clifford hierarchy, revisited

Recall $C_1$ is the Pauli group and
$C_{k+1} = \{U : U P U^\dagger \in C_k \text{ for all Paulis } P\}$. The paper's
preliminaries say:

> For $k \ge 1$, all three gates [H, $R_k$, CNOT] lie in $C_k$ … While for
> $k \le 3$ the above gates suffice to generate $C_k$, it is not generally
> known whether $C_k = \langle H, R_k, \mathrm{CNOT}\rangle$.

The formalisation (`PathSum/Hierarchy/`) checks this carefully:

- $R_k$ and $R_k^\dagger$ are in $C_k$ for every $k \ge 1$, and not in $C_{k-1}$.
- $H$ and CNOT are in $C_k$ for every $k \ge 2$, **but not in $C_1$**: they
  are not Paulis. So "for $k \ge 1$" should read "for $k \ge 2$".
- Every circuit over $\{H, S, \mathrm{CZ}\}$, and every level-≤2 circuit over
  $\{H, \mathrm{CNOT}, R_k\}$, implements an element of $C_2$.
- **$C_3$ is not a group.** $T$ and $TH$ are in $C_3$, but $THT$ is not. So
  the group generated by $H$, $T$ and CNOT ("Clifford+T") is strictly bigger
  than $C_3$, and "the gates generate $C_3$" is false read literally.
- **The gates do generate $C_2$**, for every number of qubits: every
  element of $C_2$ is a circuit over $\{H, S, \mathrm{CZ}\}$ times a scalar
  (`PathSum/Hierarchy/Generation.agda`). The proof is the classic one:
  conjugation by a Clifford maps the Paulis $X_w, Z_w$ of each wire to other
  Paulis, and an explicit circuit built from those images undoes it, wire
  by wire. On one qubit, $C_2$ modulo scalars has exactly 24 elements,
  each a word in $H$ and $S$.

## Check yourself

1. Use Lemma 4.1 to explain why the path-sum of $X$ is not the identity:
   which diagonal entry fails?
2. In the case table of 4.4, why can $b = 1$ with $Q'$ input-only never
   happen for an identity path-sum?
3. Show $H X H = Z$ and $H Z H = X$, so $H \in C_2$.
4. Compute $T X T^\dagger$ and show it is not a Pauli (so $T \notin C_2$) but is
   a Clifford (so $T \in C_3$).

Next: [5. Case studies](05-case-studies.md).
