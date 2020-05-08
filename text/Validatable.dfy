module Validation {
  trait {:termination false} Validatable {
    ghost var Repr: set<object>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr

    predicate ValidComponent(component: Validatable)
      reads this, Repr 
      ensures ValidComponent(component) ==> (
        && component in Repr
        && component.Repr <= Repr
        && this !in component.Repr
        && component.Valid()
      )
    {
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

  function AllReprs(objects: set<Validatable>): set<object> reads objects {
    set x,o | o in objects && x in o.Repr :: x
  }

  predicate Independent(objects: set<Validatable>) 
    reads objects, AllReprs(objects)
  {
    forall o, o' :: o in objects && o' in objects && o != o' ==> o.Repr !! o'.Repr
  }

  // A collection of mutually disjoint (in terms of Repr's) Validatable objects.
  // The advantage of this datatype is allowing individual elements to change
  // from one Valid() state to another under the right conditions.
  class ValidSet extends Validatable {
    var objects: set<Validatable>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && forall o :: o in objects ==> ValidComponent(o)
      && objects <= Repr
      && AllReprs(objects) <= Repr
      && Independent(objects)
    }

    constructor(objects: set<Validatable>)
      requires forall s :: s in objects ==> s.Valid()
      requires Independent(objects)
      ensures Valid() 
      ensures objects == objects
      ensures Repr == {this} + objects + AllReprs(objects)
    {
      this.objects := objects;
      Repr := {this} + objects + AllReprs(objects);
    }

    predicate Contains(other: ValidSet) 
      requires Valid()
      requires other.Valid()
      reads Repr, other.Repr 
    {
      other.objects <= objects
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