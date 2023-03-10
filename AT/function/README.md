# Functional model of the autonomous taxi system: RG and TTES

This model includes a set of background definitions for general concepts used in route and trajectory planning. It then defines the two components RG (route generator) and TTES (trajectory generator, trajectory follower, environment, and state estimator), using contracts. It then defines the top level requirements of the autonomous taxi system and queries a solver to check that RT and TTES together refine the specification.

Queries can be run by passing this model to an SMT solver such as z3:

```
> z3 AT.smt2
unsat
unsat
unsat
>
```

A call to the solver should return unsat for all queries (meaning that their negation is valid).