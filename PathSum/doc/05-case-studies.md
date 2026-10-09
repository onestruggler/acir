# 5. Case studies

Section 5 of the paper puts path-sums to work. The author implemented the
calculus in a Haskell tool called **Feynman** and used it two ways:
checking that a compiler's optimisation did not change a circuit
(*translation validation*), and checking circuits for well-known
algorithms against path-sum *specifications*. This chapter describes both,
and what the formalisation proves about them.

One difference in kind is worth stating up front. The paper reports
**runs**: a given circuit, of a given size, checked by the tool in so many
seconds. The formalisation cannot run the tool, but it can do something
the tool cannot: prove a whole **family** of circuits correct, for every
size $n$ at once, by induction.

## 5.1 Translation validation

A compiler that optimises quantum circuits (to use fewer T gates, say)
should not change what the circuit does. Translation validation checks
each compilation after the fact: given the original circuit $C$ and the
optimised $C'$, check that the miter $C' ; C^\dagger$ is the identity.

The paper ran this on a suite of benchmark circuits optimised by the
Gray-Synth algorithm (table 1): circuits of up to 96 qubits and over 25,000
gates were verified, mostly in under a minute. To test the other
direction, one random gate was deleted from each optimised circuit, and
the tool proved those **not** equivalent, using Lemma 4.2.

The formalisation proves the procedure sound (`validation-sound`: a "yes"
is always right), proves its refutations sound, and proves it complete for
circuits of level at most 2. At level 3 it is incomplete, as chapter 3
warned: `PathSum/Examples/ValidationIncomplete.agda` gives two equivalent
circuits whose miter gets stuck.

## 5.2 Generalised Toffoli gates

The $n$-bit Toffoli gate flips its last bit when all the others are 1:

$$
\mathrm{Toffoli}_n : \lvert x_1 \cdots x_n\rangle \mapsto \lvert x_1 \cdots x_{n-1},\; x_n \oplus x_1x_2\cdots x_{n-1}\rangle .
$$

It is built from ordinary 3-bit Toffolis using extra **ancilla** qubits
that start and end in $\lvert 0\rangle$. The paper verified two
constructions: a "V-chain" of $2(n-3)+1$ Toffolis with $n-3$ ancillas, and
Maslov's construction with cheaper *relative-phase* Toffolis and
$\lceil (n-3)/2\rceil$ ancillas, up to 100 bits in seconds.

The formalisation proves both constructions correct **for every $n \ge 3$**,
including that the ancillas come back clean (`PathSum/ToffoliN.agda`,
`PathSum/Maslov.agda`). It also transcribes the tool's own circuit
generators, proves them equal to the formal circuits gate for gate, and
recomputes table 2's columns (qubits, path variables, Clifford and T
counts) from them.

## 5.3 An adder

An out-of-place adder computes $\lvert x\rangle\lvert y\rangle\lvert 0\rangle \mapsto \lvert x\rangle\lvert y\rangle\lvert x + y\rangle$
using a ripple of carry bits, which it computes, copies out, and
uncomputes. The specification was produced by doing binary addition on
*symbolic* bits.

Here the paper notes that the specification itself grows large: it could
verify 16-bit adders but not 32-bit ones. The formalisation explains why
exactly: the carry out of $n$-bit addition, written as a polynomial over
$\mathbb{Z}_2$, has **exactly $2^n - 1$ monomials**, however it is written
(`PathSum/Adder/Expansion.agda`). It also proves the adder correct for every
$n$, and notes that the circuit uses $5n$ qubits (as table 2 says), not the
$5n - 1$ the text says.

## 5.4 The quantum Fourier transform

The QFT is specified exactly as a textbook writes it:

$$
\mathrm{QFT}_n : \lvert x\rangle \mapsto \frac{1}{\sqrt{2^n}} \sum_{y \in \mathbb{Z}_2^n} e\!\left(\tfrac{[x]\,[y]}{2^n}\right)\lvert y\rangle .
$$

Its circuit uses controlled rotations, so it needs $R_k$ gates for large
$k$, and the phases have large denominators. The paper verified it up to
31 qubits, where the tool's integer arithmetic overflowed. The
formalisation proves the circuit correct **for every $n$** (`QFT-≋`), given
enough precision to write the phases, and shows the specification is
unitary exactly when the precision suffices.

## 5.5 The hidden shift algorithm

This is the most striking example. A **bent function** is a Boolean
function $f$ that is as far as possible from every linear function; each
has a *dual* bent function $\tilde f$. Writing $f$ as a $\pm1$-valued
function, suppose we are given oracles (subcircuits) for $\tilde f$ and for
a *shifted* copy $f'(x) = f(x \oplus s)$, with the shift $s$ unknown. Then

$$
H^{\otimes n}\, O_{\tilde f}\, H^{\otimes n}\, O_{f'}\, H^{\otimes n} \lvert 0\rangle = \lvert s\rangle,
$$

so one run of the circuit reveals $s$. The paper uses the
Maiorana–McFarland bent functions $f(x, y) = (-1)^{g(x) + x\cdot y}$, with
dual $(-1)^{g(y) + x\cdot y}$, for random $g$, and verified instances with up
to 60 qubits (table 2), far beyond the earlier simulation methods.

What the formalisation proves:

- the circuit maps $\lvert 0\rangle$ to $\lvert s\rangle$ for **every** $m$,
  every $g$ and every $s$ (`hidden-shift`), and also for every bent function
  with its dual, not only the Maiorana–McFarland ones;
- complete reductions exist: the rewrite rules reduce the circuit's
  path-sum to $\lvert x\rangle \mapsto \lvert s\rangle$ with no path variables
  left, and every complete reduction ends there.

The paper also says: "Our calculus further finds the correct output
$\lvert s\rangle$ … even without providing the specification." The
formalisation shows this needs care. **Some** maximal reductions get stuck
with path variables left, already for a 6-qubit Clifford instance. But
there is a natural class of strategies that never gets stuck: restrict
each [HH] step to be *output-safe* and *Clifford-safe*. Then **every**
maximal reduction in the class reaches $\lvert s\rangle$, for every $m$, $g$
and $s$ (`PathSum/HiddenShift/Positive.agda`).

- *Output-safe:* a quotient mentioning a variable absent from the outputs
  may only substitute such a variable.
- *Clifford-safe:* variables of degree at most 2 stay so.

## Check yourself

1. Why does a miter $C' ; C^\dagger$ test equivalence even when $C'$ and $C$
   have different numbers of gates?
2. For $n = 2$, list the monomials of the carry out of $x + y$ (bits
   $x_1x_2$, $y_1y_2$) and confirm there are $2^2 - 1 = 3$.
3. Show that $f(x) = (-1)^{x_1 x_2}$ on two bits is bent: its Walsh
   coefficients $\sum_x f(x)(-1)^{u\cdot x}$ all have absolute value 2.

Next: [6. An Agda primer](06-agda-primer.md).
