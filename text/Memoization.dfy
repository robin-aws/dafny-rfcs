include "./Validatable.dfy"

module Memoization {

  import opened Validation

  // Specialized to nat -> nat because parameterized classes can't
  // extend traits yet.
  class Memoizer extends Validatable {
    const f: nat -> nat
    var results: map<nat, nat>

    predicate Valid() reads this {
      forall t :: t in results.Keys ==> results[t] == f(t)
    }

    constructor(singletons: AllSingletons, f: nat -> nat)
      requires singletons.AllValid()
      modifies singletons
      ensures Valid()
      ensures singletons.AllValid()
    {
      this.f := f;
      this.results := map[];
      Repr := {this};
      new;
      singletons.AddSingleton(this);
    }

    method Apply(t: nat) returns (res: nat)
      requires Valid()
      modifies this
      ensures Valid()
      ensures res == f(t)
    {
      if t in results {
        res := results[t];
      } else {
        res := f(t);
        results := results[t := res];
      }
    }
  }

}