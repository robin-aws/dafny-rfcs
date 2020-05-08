module Validation {

  // A trait for objects with a Valid() predicate. Necessary in order to
  // generalize some proofs, but also useful for reducing the boilerplate
  // that most such objects need to include.
  trait {:termination false} Validatable {
    // TODO-RS: repr?
    ghost var Repr: set<object>

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr

    // Convenience predicate for when your object's validity depends on one
    // or more other objects.
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

  // TODO-RS: Better name? I don't hate this but...
  predicate Independent(objects: set<Validatable>) 
    reads objects, AllReprs(objects)
  {
    forall o, o' :: o in objects && o' in objects && o != o' ==> o.Repr !! o'.Repr
  }

  // A collection of mutually disjoint (in terms of Repr's) Validatable objects.
  // The advantage of this datatype is allowing individual elements to change
  // from one Valid() state to another under the right conditions.
  class IndependentSet extends Validatable {
    // TODO-RS: Curently non-ghost because of the expect statements, but
    // I believe those aren't necessary with refactoring - calling contexts
    // should be aware of the contents if carefully managed.
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

    predicate Contains(other: IndependentSet) 
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

    // Used to re-assert validity when a single contained object
    // changes to a new Valid() state.
    // TODO-RS: Is there some way to combine this with the
    // `Repr := Repr + v.Repr` statement that every invocation
    // will have to do first?
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