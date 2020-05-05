module Memoization {

  class Memoizer<T(==), R> {
    const f: T -> R
    var results: map<T, R>

    predicate Valid() reads this {
      forall t :: t in results.Keys ==> results[t] == f(t)
    }

    constructor(f: T -> R)
      ensures Valid()
    {
      this.f := f;
      this.results := map[];
    }

    method Apply(t: T) returns (res: R)
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