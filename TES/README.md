# Functional model of the autonomous taxi system: TES

This model includes a set of background definitions for general concepts such as trajectories and neighborhoods. It then defines a trajectory follower TF, an environment ENV, and a state estimator SE using contracts. It then defines the top level requirements of TES and checks that TF, ENV, and SE together refine the specification.

Queries can be run by passing this model to an SMT solver such as z3:

```
> z3 TES.smt2
unsat
unsat
>
```

A call to the solver should return unsat for all queries (meaning that their negation is valid).