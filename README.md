# qupit — Agda formalisation

Agda formalisation of group presentations, normal forms, and complete
relation sets for multi-qudit Clifford circuits.

## Versions

| Component            | Version |
| -------------------- | ------- |
| Agda                 | 2.8     |
| Agda standard library| 2.4     |


The library configuration is in [`qupit.agda-lib`](qupit.agda-lib): it
includes the repository root (`.`) and depends on `standard-library`.

## Typechecking

Any of the following roots covers the whole live library:

```bash
agda Examples/Groups/Symmetric/Theorems.agda
agda Examples/Amalgamations/CliffordT1.agda
agda Examples/Amalgamations/QutritCliffordT1.agda
agda Examples/Amalgamations/U33Di.agda
```

`MainTheorems.agda` restates the headline theorems and typechecks
together with the roots above.
