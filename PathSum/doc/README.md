# Path-sums, and a machine-checked proof of them: a tutorial

This tutorial explains a research paper and its formalisation to an
undergraduate who has seen some linear algebra and some discrete
mathematics. The paper is

> Matthew Amy, *Towards Large-scale Functional Verification of Universal
> Quantum Circuits*, QPL 2018 (EPTCS 287, pp. 1–21, 2019).

The paper proposes **path-sums**, a way of writing down what a quantum
circuit does using polynomials instead of exponentially large matrices,
and a set of **rewrite rules** that simplify path-sums until it is
obvious what a circuit computes. With them it decides in polynomial time
whether a *Clifford* circuit equals the identity, and it verifies
circuits with hundreds of qubits.

The directory above this one, `PathSum/`, is a **formalisation** of the
paper in the proof assistant [Agda](https://agda.readthedocs.io): every
definition, lemma and theorem of the paper is written as Agda code, and
the computer checks every proof. That process confirmed most of the
paper, filled in some gaps, and found a handful of statements that are
false as printed, together with corrected versions.

## Who this is for

You should be comfortable with:

- vectors, matrices and matrix multiplication; complex numbers, $e^{i\theta}$;
- Boolean logic (AND, XOR) and polynomials;
- proofs by induction and by cases.

You do **not** need to know quantum mechanics beyond what chapter 1
explains, and you do not need to know Agda: chapter 6 teaches enough to
read the formal statements.

## How to read it

The chapters build on each other. Chapters 1–5 are about the paper and
need no Agda at all; chapters 6–8 are about the formalisation. Each
chapter ends with a few check-yourself questions, and chapter 9 collects
longer exercises with solutions.

| Chapter | Topic |
|---|---|
| [1. Quantum circuits in a nutshell](01-quantum-circuits.md) | qubits, gates, circuits, why checking them is hard |
| [2. Path-sums](02-path-sums.md) | the paper's representation, gate by gate and circuit by circuit |
| [3. Rewriting path-sums](03-rewriting.md) | interference, the four rules of figure 2, worked reductions |
| [4. Deciding Clifford circuits](04-clifford.md) | restrictions, refutations, corollary 4.4, the Clifford hierarchy |
| [5. Case studies](05-case-studies.md) | Toffoli gates, adders, the QFT, the hidden shift algorithm |
| [6. An Agda primer](06-agda-primer.md) | just enough Agda to read the formal statements |
| [7. Inside the formalisation](07-formalisation.md) | how the paper's objects become Agda definitions |
| [8. What machine checking found](08-findings.md) | the paper's errata, the gaps that were filled, and why |
| [9. Exercises and solutions](09-exercises.md) | practice, from hand calculations to reading Agda |

A [glossary](#glossary) is at the end of this page.

## Notation used throughout

- $\mathbb{Z}_2 = \{0, 1\}$ with addition modulo 2, written $\oplus$ (XOR).
  A bit string of length $n$ is an element of $\mathbb{Z}_2^n$.
- $\lvert x\rangle$ is the basis vector labelled by the bit string $x$.
- $e(\theta)$ abbreviates $e^{2\pi i \theta}$. Only the fractional part of
  $\theta$ matters: $e(\theta + 1) = e(\theta)$.
- $\omega = e(1/8) = e^{i\pi/4}$, a primitive eighth root of unity.

## Where things are in the code

- [`PathSum/Theorems.agda`](../Theorems.agda) restates every result of the
  formalisation in one place, section by section, each with the name of
  the module that proves it. It is the best entry point.
- [`PathSum/CLAUDE.md`](../CLAUDE.md) is the developers' map of every
  module, the departures from the paper and the known pitfalls.
- [`PathSum/Examples/`](../Examples) holds the paper's worked examples,
  checked by the computer at the smallest precision (phases in eighths).

## Glossary

**Amplitude.** The complex number in front of a basis vector in a state.

**Clifford circuit.** A circuit over the gates H, S and CNOT (or CZ). The
operators these circuits implement form the *Clifford group* $C_2$.

**Clifford hierarchy.** The sets $C_1 \subseteq C_2 \subseteq C_3 \dots$ of
unitaries defined in chapter 4; $C_1$ is the Pauli group, $C_2$ the
Clifford group.

**Dyadic fraction.** A number $a/2^b$ with $a, b$ integers. Phases of the
gates studied here are dyadic.

**Internal path variable.** A path variable that occurs in no output of
the path-sum. Only internal variables can be summed away.

**Miter.** To check that circuits $C_1$ and $C_2$ agree, check that
$C_1$ followed by the inverse of $C_2$ is the identity.

**Normal form.** A path-sum to which no rewrite rule applies.

**Path-sum.** A triple (inputs, phase polynomial, output polynomials)
describing a linear map as a sum over paths (chapter 2).

**Path variable.** One of the Boolean variables $y_1, \dots, y_m$ summed
over in a path-sum.

**Phase polynomial.** The polynomial $P$ whose value $e(P)$ is the phase
picked up along a path.

**Proof assistant.** A program that checks mathematical proofs written
in a precise formal language; Agda is one.

**Unitary.** A square complex matrix $U$ with $U^\dagger U = I$; every
gate is unitary.
