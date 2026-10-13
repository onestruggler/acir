# Four-state auxiliary subgroup

`Presentation.agda` proves a complete presentation of the charge-zero
subgroup of the dyadic two-level presentation in every dimension at least
two. It applies the stateful form of Clément's translation to Table 1 in
`CCX+HH-TwoLevel/`. It does not assume a circuit decoder.

The four coset states are `00`, `10`, `11`, and `01`. Reading a source
letter adds its charge in the group of two binary coordinates:

| Source letter | Charge |
| --- | --- |
| `M[a]` | `10` |
| `X[a,b]` | `11` |
| `K[a,b,c,d]` | `01` |

`Action.agda` proves that every Table 1 relation preserves this action,
for every choice of its indices. The first coordinate is determinant
parity. The second agrees with the rational spinor square-class of two;
the formal proofs use only the displayed action, without a spinor-norm
library.

The representatives of the four states are
`epsilon`, `M[0]`, `X[0,1]`, and `M[0] X[0,1]`.
An auxiliary generator is an edge `(c,g)`, encoded by
`rep(c) g inverse(rep(c.g))`. The equations are:

1. Each source axiom, decoded starting at each of the four states.
2. For each edge generator, its circuit-free encode/decode equation.

`Schreier.agda` proves this construction for an arbitrary presented
group acting on states with a chosen representative for every state.
Its `encode-cong` and `encode-injective` establish both directions of
derivability. Its `encode-closed` and `decode-loop` show that the image
is exactly the stabilizer of the initial state. It also proves that
the resulting presentation is grouplike. No matrix equality is a
generating equation.

`Presentation.agda` specializes these results and transports the existing
two-level completeness theorem. It exports matrix `soundness` and
`completeness`, matrix invariance of the state (`state-semantic`), and
the constructive image theorem (`stabilizer-generated`).

`Charge.agda` supplies the membership calculation for spectator wires.
`word-embedding` says that increasing relabelling preserves charge.
`parallel-closed` says that any two embedded copies of the same word
have charge zero. The theorem is independent of how their coordinates
are interleaved, and even does not require the two embeddings to be
disjoint.

There are 84 translated relation schemas and 12 edge roundtrip schemas.
For a fixed dimension `N`, retaining duplicate and trivial instances,
let

```
g(N) = N + binom(N,2) + binom(N,4)
r(N) = N + 4 binom(N,2) + 5 binom(N,3) + 10 binom(N,4)
         + 9 binom(N,5) + 16 binom(N,6) + 71 binom(N,8).
```

The presentation has `4 g(N)` generators and `4 r(N) + 4 g(N)`
equations. These formulas count ordinary index instances, ignoring
proof arguments. For example, `r(4)=58`, matching the independently
enumerated Table 1 instances used by the two-qubit experiment.

Identifying this auxiliary subgroup with the physical gate image at
four or more qubits requires a constructive circuit interpretation of
the edge generators. That is a separate decoding obligation; the
auxiliary presentation does not claim it by definition.

All six modules, including `Charge` and `CircuitCharge`, passed
Agda 2.8 with `--safe`. `CircuitCharge.image-closed` proves membership
of every structurally encoded circuit on at least four wires, at
every starting coset.
