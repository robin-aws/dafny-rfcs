module Validation {
  trait {:termination false} Validatable {
    ghost var Repr: set<object>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr

    predicate ValidComponent(component: Validatable) reads this, Repr {
      && component in Repr
      && component.Repr <= Repr
      && this !in component.Repr
      && component.Valid()
    }

    // Convenience predicate, since you often want to assert that 
    // new objects in Repr are fresh as well.
    // TODO-RS: Better name?
    twostate predicate ValidAndFresh() 
      reads this, Repr
      ensures ValidAndFresh() ==> Valid() && fresh(Repr - old(Repr))
    {
      Valid() && fresh(Repr - old(Repr))
    }
  }

  class ValidSet extends Validatable {
    var objects: set<Validatable>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && objects <= Repr
      && forall s :: s in objects ==> (
        && s in Repr
        && s.Repr <= Repr 
        && this !in s.Repr
        && s.Valid()
        && (forall other :: other in objects && other != s ==> other.Repr !! s.Repr)
      )
    }

    constructor() 
      ensures Valid() 
      ensures objects == {}
      ensures Repr == {this}
    {
      objects := {};
      Repr := {this};
    }

    method Add(v: Validatable) 
      requires Valid()
      requires v.Valid()
      requires this !in v.Repr
      requires Repr !! v.Repr
      modifies this
      ensures objects == old(objects) + {v}
      ensures Repr == old(Repr) + v.Repr
      ensures Valid()
    {
      objects := objects + {v};
      Repr := Repr + v.Repr;
    }

    twostate lemma Updated(v: Validatable)
      requires old(Valid())
      requires v in objects
      requires v.Valid()
      requires unchanged(`objects)
      requires forall o :: 
        o !in old(v.Repr) && o != this ==> fresh(o) || unchanged(o)
      requires fresh(v.Repr - old(v.Repr))
      requires Repr == old(Repr) + v.Repr
      ensures ValidAndFresh() 
    {
    }
  }
}