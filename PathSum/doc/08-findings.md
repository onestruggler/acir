# 8. What machine checking found

Formalising a paper is like refereeing it with a referee who never gets
tired and never says "clearly". Every case must be handled, every
"obvious" step written out, every hypothesis used exactly as stated. Most
of the paper survives this. Its main results — the rewrite rules are
sound, Clifford circuits can be checked in polynomial time, the case
studies are correct — all hold. But the process turned up three kinds of
problems: statements that are **false as printed**, smaller **slips**, and
**gaps** in proofs. This chapter explains each, at the level of the
earlier chapters.

None of this is a criticism of the paper. These are the normal
imperfections of careful mathematical writing. They are found precisely
because a proof assistant reads the text far more literally than any human
reader.

## 8.1 Statements that are false as printed

### Lemma 4.2 needs "odd", not "non-zero"

Lemma 4.2 says: if the phase is $\tfrac12 y_0 Q + R$ with $Q$ "a non-zero
integer-valued polynomial not containing any path variables", the
path-sum is not the identity. The idea (chapter 4) is that the two
branches of $y_0$ cancel wherever $Q$ is odd.

But a non-zero $Q$ need not ever be odd. Take $Q = 2x_1$: then
$\tfrac12 y_0 \cdot 2x_1 = y_0 x_1$ is an integer, $e(y_0x_1) = 1$, and the
branches **add** instead of cancelling. A path-sum with this phase can be
the identity: the formalisation builds one with three path variables and
the paper's own normalisation $1/\sqrt{2^3}$ and proves it equals
$\lvert x\rangle \mapsto \lvert x\rangle$ (`lemma-4-2-as-stated-fails-tied`).

**Corrected:** the conclusion holds when $Q$ is odd for some input
(`interferenceᴳ`). Where the paper uses the lemma, $Q$ is Boolean-valued,
and then "non-zero" does imply "odd somewhere", so nothing downstream breaks.

### Proposition 2.14 fails at $k = 1$

Proposition 2.14 says the phase of a circuit over $\{H, \mathrm{CNOT}, R_k\}$
has degree at most $k$. At $k = 1$ the gate set is $\{H, \mathrm{CNOT}, Z\}$,
yet a single Hadamard contributes $\tfrac12 xy$, of degree 2
(`prop-2-14-false-at-1`).

**Corrected:** the bound is $\max(2, k)$ (`prop-2-14`). For $k \ge 2$, which
covers every use in the paper, the printed statement is right.

### Proposition 2.7: composing well-formed path-sums

Proposition 2.7 says that composing two well-formed path-sums gives a
well-formed one (well-formed = the operator is a partial isometry). It
does not. The projections $P_0 = \lvert 0\rangle\langle 0\rvert$ and
$P_+ = \lvert +\rangle\langle +\rvert$ are both partial isometries, but

$$
P_+ P_0 = \lvert +\rangle\langle + \vert 0\rangle\langle 0\rvert = \tfrac{1}{\sqrt2}\lvert +\rangle\langle 0\rvert
$$

is not: it shrinks $\lvert 0\rangle$ to length $1/\sqrt2$
(`PartialIsometric-∘-fails-tied`).

**Corrected:** well-formedness is preserved when the second path-sum is
an isometry, which covers composing unitary gates, the only case the paper
needs (`Isometric-∘`, `WellFormed-∘`). The other half of the proposition, that
the composite's operator is the product of the operators, is true.

### Proposition 3.2's time bound, beyond Clifford

Proposition 3.2 says every sequence of rewrites reaches a normal form in
polynomial time. The number of steps is indeed small (each removes a
variable). But a step's *result* can be much bigger than its input:
[HH] substitutes a polynomial $Q$ for a variable, and if $Q$ is non-linear,
multiplying out can create many new terms.

The formalisation builds a family $\xi_n$ (a "ladder" of $n$ Toffoli-like
gadgets) with $2n$ qubits, $4n$ terms and phase of order 3. Every normal
form reachable from $\xi_n$, by any rules in any order, has an output
polynomial with at least $2^n$ monomials (read modulo 2). Writing it down
as a list of monomials takes exponential time
(`PathSum/Ladder/Size.agda`).

**What survives:** at order 2, the Clifford case Corollary 4.4 needs, the
bound holds and is proved. The counterexample is about representing
polynomials as lists of monomials, and $\xi_n$ is a family of path-sums,
not shown to come from circuits.

## 8.2 Smaller slips

These change no result, and each is recorded in the header of the module
that deals with it.

| Where | As printed | What is meant |
|---|---|---|
| Definition 2.6 | renames the second path-sum's variables in the phase only | they must be renamed in its outputs too |
| Section 4.1 | for $f_i = y_i \oplus Q$, "substitute $Q$ for $y_i$ to get $f_i = x_i$" | substitute $y_i \leftarrow x_i \oplus Q$ (substituting $Q$ gives $f_i = 0$) |
| Example 3.4, 4th line | $\tfrac18(x_1y_4 + x_1x_2)$ | $\tfrac12 x_1y_4 + \tfrac18 x_1x_2$; the conclusion stands |
| Example B.1 | the printed path-sum (coefficients $\tfrac68$) "reduces to $\omega I$" | that path-sum is the identity; the true $(SH)^3$ has coefficients $\tfrac28$ (chapter 3) |
| Section 5.2, hidden shift | $f'(x,y) = f((x,y)+s) = (-1)^{g(x)+xy}$ | the last expression is $f$'s, not $f'$'s |
| Section 5.2, adder | "$5n - 1$ bits of space" | $5n$ qubits for $n \ge 2$, as table 2 says |
| Section 5.2, hidden shift | the calculus "finds $\lvert s\rangle$ even without providing the specification" | along a suitable reduction (some get stuck), and along every reduction of a natural class (chapter 5) |
| Section 2 | "for $k \ge 1$, all three gates lie in $C_k$" | for $k \ge 2$: H and CNOT are not Paulis |
| Section 2 | "for $k \le 3$ the above gates suffice to generate $C_k$" | false read literally at $k = 1$ and $k = 3$ ($C_3$ is not a group); true at $k = 2$ |

## 8.3 Gaps that were filled

Some proofs were right in spirit but skipped a step that needed its own
argument.

- **Corollary 4.4 uses any rules.** Its proof rewrites by whichever rules
  apply, but Lemma 4.3 only shows that *its own* choice of rule keeps the
  order at most 2. The proof needs every rule to keep it at most 2. That is
  true, and is proved (`PathSum/Full/Clifford.agda`).
- **Lemma 4.3's hidden side condition.** A rule may need more
  normalisation factors than the path-sum has left (recall the table in
  chapter 7). For a path-sum equal to the identity this never happens.
  The paper does not say so, and the formalisation proves it.
- **"Applied in the obvious way."** The rules are written for the first
  path variable and applied "in the obvious way" to others. Making that
  precise needs a renumbering of variables built into each rule (a
  separate reordering step would let rewriting loop forever).
- **Corollary 2.15 at volume 0.** "Polynomial in the volume $n \cdot \lvert C\rvert$"
  fails for the empty circuit, whose volume is 0 but whose path-sum still
  has $n$ outputs. It holds in $n + \lvert C\rvert$.

## 8.4 Claims confirmed beyond the paper

Several things the paper asserts without proof, or leaves to its tool,
were proved:

- the [Case] rule is genuinely needed for the identity of section 3.2;
- table 2's gate counts, recomputed from the tool's own circuit generators;
- the Toffoli, Maslov, adder, QFT and hidden-shift circuits, correct for **every** size;
- the hidden shift algorithm for every bent function, not only the family used;
- the remedy for incompleteness (expanding leftover variables) is sound
  and complete;
- the Clifford group is generated by $\{H, S, \mathrm{CZ}\}$ on any number of
  qubits (up to a scalar).

## 8.5 What to take away

The problems found have a common shape:

- **Edge cases of hypotheses.** $k = 1$, $Q = 2x_1$, the empty circuit:
  the statement is right in every case the author had in mind, and wrong
  in one the wording allows.
- **"Obvious" steps.** Rules "applied in the obvious way", or a proof that
  uses "any rule" where a lemma covered only some. These are exactly the
  places a human reader skims.
- **Long calculations.** A coefficient or a variable name changed
  somewhere in a ten-line derivation.

A proof assistant does not get tired at line ten, and it cannot be
persuaded by "clearly". That is what makes it useful as a second reader,
even for a paper whose main results turn out to be right.

## Check yourself

1. Give another $Q$, not a multiple of $2x_1$, that is non-zero, integer-valued,
   free of path variables, and even at every input.
2. Verify $P_+P_0 = \tfrac1{\sqrt2}\lvert +\rangle\langle 0\rvert$ with $2 \times 2$
   matrices, and show it is not a partial isometry: compute $A^\dagger A$ and
   check it is not a projection.
3. Why does a single Hadamard break "degree ≤ $k$" at $k = 1$ but not at
   $k = 2$?

Next: [9. Exercises and solutions](09-exercises.md).
