# 1. Quantum circuits in a nutshell

This chapter gives the minimum of quantum computing needed for the rest:
states, gates, circuits, and why checking a circuit is hard. If you have
taken a quantum computing course, skim it for notation.

## 1.1 States are vectors

A classical register of $n$ bits holds one bit string $x \in \mathbb{Z}_2^n$.
A **quantum register** of $n$ qubits holds a unit vector in the complex
vector space $\mathbb{C}^{2^n}$. That space has one basis vector for each
bit string, written $\lvert x\rangle$ ("ket $x$"), so a general state is

$$
\lvert\psi\rangle = \sum_{x \in \mathbb{Z}_2^n} \alpha_x \lvert x\rangle,
\qquad \sum_x \lvert\alpha_x\rvert^2 = 1 .
$$

The complex numbers $\alpha_x$ are **amplitudes**. For example, on one
qubit,

$$
\lvert +\rangle = \tfrac{1}{\sqrt 2}\big(\lvert 0\rangle + \lvert 1\rangle\big),
\qquad
\lvert -\rangle = \tfrac{1}{\sqrt 2}\big(\lvert 0\rangle - \lvert 1\rangle\big).
$$

The important point for us: an $n$-qubit state has $2^n$ amplitudes. Ten
qubits need about a thousand numbers; a hundred qubits need $2^{100}$.

## 1.2 Gates are unitary matrices

A quantum **gate** on $n$ qubits is a $2^n \times 2^n$ unitary matrix $U$,
meaning $U^\dagger U = I$, where $U^\dagger$ is the conjugate transpose.
Because a gate is linear, it is enough to say what it does to each basis
vector $\lvert x\rangle$. Here are the gates this tutorial uses. Remember
$e(\theta) = e^{2\pi i\theta}$ and $\omega = e(1/8)$.

| Gate | Qubits | Action on basis states | Comment |
|---|---|---|---|
| $X$ | 1 | $\lvert x\rangle \mapsto \lvert 1 \oplus x\rangle$ | NOT |
| $Z$ | 1 | $\lvert x\rangle \mapsto (-1)^x \lvert x\rangle = e(x/2)\lvert x\rangle$ | phase flip |
| $S$ | 1 | $\lvert x\rangle \mapsto i^x \lvert x\rangle = e(x/4)\lvert x\rangle$ | |
| $T$ | 1 | $\lvert x\rangle \mapsto \omega^x \lvert x\rangle = e(x/8)\lvert x\rangle$ | |
| $R_k$ | 1 | $\lvert x\rangle \mapsto e(x/2^k)\lvert x\rangle$ | $R_1 = Z$, $R_2 = S$, $R_3 = T$ |
| $H$ | 1 | $\lvert x\rangle \mapsto \frac{1}{\sqrt2}\big(\lvert 0\rangle + (-1)^x \lvert 1\rangle\big)$ | Hadamard |
| CNOT | 2 | $\lvert x_1 x_2\rangle \mapsto \lvert x_1, x_1 \oplus x_2\rangle$ | controlled NOT |
| CZ | 2 | $\lvert x_1 x_2\rangle \mapsto (-1)^{x_1 x_2}\lvert x_1 x_2\rangle$ | controlled Z |
| Toffoli | 3 | $\lvert x_1 x_2 x_3\rangle \mapsto \lvert x_1, x_2, x_3 \oplus x_1x_2\rangle$ | controlled-controlled NOT |

As matrices, for instance,

$$
H = \frac{1}{\sqrt 2}\begin{pmatrix} 1 & 1\\ 1 & -1\end{pmatrix},\qquad
R_k = \begin{pmatrix} 1 & 0\\ 0 & e(1/2^k)\end{pmatrix},\qquad
\mathrm{CNOT} = \begin{pmatrix}1&0&0&0\\0&1&0&0\\0&0&0&1\\0&0&1&0\end{pmatrix}.
$$

Notice one gate behaves differently from the others: **H is the only gate
that turns one basis vector into a combination of two**. Every other gate
in the table maps a basis vector to a single basis vector times a phase.
That is exactly where "paths" will come from in chapter 2.

## 1.3 Circuits are sequences of gates

A **circuit** applies gates one after another, each to some of the wires.
If a circuit applies $G_1$, then $G_2$, …, then $G_\ell$, its overall matrix
is the product $U_C = G_\ell \cdots G_2 G_1$ (later gates on the left), where
a gate on some of the wires is extended to all $n$ wires by tensoring with
identities.

Two famous small circuits:

- $HH = I$: the Hadamard gate is its own inverse.
- $(SH)^3 = \omega I$: applying H then S three times multiplies every
  state by the global phase $\omega$.

You can check both with $2 \times 2$ matrices. In chapter 3 we will check
them with path-sums instead, without ever writing a matrix.

## 1.4 When are two circuits the same?

Two circuits are **equivalent** when they have the same matrix. A subtle
point is the **global phase**: the matrices $U$ and $e^{i\theta}U$ give
physically indistinguishable results, so some authors identify them. The
paper, and the formalisation, compare matrices exactly, so $(SH)^3$ is *not*
equal to the identity: it equals $\omega I$. (The formalisation also has a
version of the main result up to a global phase, in `PathSum/GlobalPhase.agda`.)

Checking that a circuit $C_1$ implements the same operator as $C_2$
reduces to checking that one circuit is the identity: $C_1 \equiv C_2$
exactly when $C_1$ followed by the inverse $C_2^\dagger$ is the identity.
This trick is called a **miter**. The inverse of a circuit is the reversed
circuit with every gate inverted ($H^\dagger = H$, $S^\dagger = S^3$, …).

## 1.5 Why checking circuits is hard

To decide whether a circuit on $n$ qubits is the identity, you could
multiply out its $2^n \times 2^n$ matrix. That works for ten qubits and is
hopeless for a hundred. Testing is no better: running the circuit on a
quantum computer only samples its output distribution, and simulating it
on a classical computer generally takes exponential time too.

Verification tools therefore need **symbolic** representations, which
describe a circuit's action on a *symbolic* input $\lvert x\rangle$ with
$x$ a vector of variables, and grow only polynomially with the circuit.
Path-sums are one such representation.

## 1.6 Gate sets, and the Clifford hierarchy

Circuits over $\{H, S, \mathrm{CNOT}\}$ are called **Clifford circuits**.
They are important but special: they can be simulated efficiently on a
classical computer (the Gottesman–Knill theorem). Adding the $T$ gate gives
**Clifford+T**, a *universal* gate set: every unitary can be approximated
by Clifford+T circuits.

The paper places these gates in the **Clifford hierarchy**. Its first
level $C_1$ is the **Pauli group**: all products $i^a X^{x} Z^{z}$ of
Paulis on each wire, with a phase $i^a$. Higher levels are defined by
conjugation:

$$
C_{k+1} = \{\, U \text{ unitary} \;:\; U P U^\dagger \in C_k \text{ for every Pauli } P \,\}.
$$

So $C_2$ is the set of unitaries that map Paulis to Paulis by conjugation:
the **Clifford group**. For instance $S X S^\dagger = iXZ$ (a Pauli) and
$S Z S^\dagger = Z$, so $S \in C_2$. The $T$ gate is in $C_3$ but not
$C_2$, and in general $R_k \in C_k$. Chapter 4 says more, including two
places where the paper's description of the hierarchy is not quite right.

## Check yourself

1. Write the matrix of $S$ and check $S^2 = Z$ and $T^2 = S$.
2. Compute $H\lvert 0\rangle$ and $H\lvert 1\rangle$; then compute
   $H(H\lvert 0\rangle)$ and confirm it is $\lvert 0\rangle$.
3. Why is a circuit $C$ the identity exactly when its miter with the empty
   circuit is the identity? (Trivial, but make sure the definition is clear.)
4. Show that $X$ and $Z$ anticommute: $XZ = -ZX$.

Next: [2. Path-sums](02-path-sums.md).
