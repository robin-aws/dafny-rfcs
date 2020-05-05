module Memoization {

  class Memoizer<T(==), R> {
    const f: T -> R
    var results: map<T, R>

    predicate Valid() reads this {
      forall t :: t in results.Keys ==> results[t] == f(t)
    }

    constructor(f: T -> R)
    {
      this.f := f;
    }

    method Store(t: T, r: R) 
      modifies this
    {
      results := results[t := r];
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