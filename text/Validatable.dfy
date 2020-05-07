module Validation {
  trait {:termination false} Validatable {
    ghost var Repr: set<object>
    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr
  }

  // This would be a singleton to track all valid-by-default objects
  class AllSingletons {
    var singletons: set<Validatable>
    ghost var singletonReprs: set<object>

    predicate AllValid() reads this, singletons, singletonReprs {
      forall s :: s in singletons ==> (
        && this !in s.Repr // No Russel's paradox please :)
        && s.Valid()
        && s.Repr <= singletonReprs 
        && (forall other :: other in singletons && other != s ==> other.Repr !! s.Repr)
      )
    }

    constructor() 
      ensures AllValid() 
      ensures singletons == {}
      ensures singletonReprs == {}
    {
      singletons := {};
      singletonReprs := {};
    }

    method AddSingleton(v: Validatable) 
      requires AllValid()
      requires v.Valid()
      requires this !in v.Repr
      requires singletonReprs !! v.Repr
      modifies this
      ensures singletons == old(singletons) + {v}
      ensures singletonReprs == old(singletonReprs) + v.Repr
      ensures AllValid()
    {
      singletons := singletons + {v};
      singletonReprs := singletonReprs + v.Repr;
    }

    method ExpectValid(s: Validatable) 
      requires AllValid()
      ensures s in singletons
      ensures s.Valid()
      ensures s.Repr <= singletonReprs
    {
      expect s in singletons;
    }

    twostate lemma AllStillValid(v: Validatable)
      requires old(AllValid())
      requires v in singletons
      requires unchanged(`singletons)
      requires forall o :: o !in v.Repr ==> unchanged(o)
      requires v.Valid()
      requires fresh(v.Repr - old(v.Repr))
      requires singletonReprs == old(singletonReprs) + v.Repr
      ensures AllValid() 
    {
    }
  }
}