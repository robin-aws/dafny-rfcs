include "./Collections.dfy"
include "./Validatable.dfy"

module Profiling {

  import opened Collections
  import opened Validation

  class Profiler extends Validatable {

    predicate Valid() 
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && calls in Repr
      && calls.Repr <= Repr
      && this !in calls.Repr
      && calls.Valid()
    }
    var calls: List
    var locations: map<string, nat>

    constructor() 
      ensures Valid()
      ensures fresh(Repr)
    {
      calls := new ArrayList();
      new;
      Repr := {this} + calls.Repr;
    }

    method AddLocation(name: string)
      requires Valid()
      modifies Repr
      ensures ValidAndFresh()
    {
      locations := locations[name := |locations| + 1];
    }

    method RecordCall(name: string)
      requires Valid()
      requires name in locations
      modifies Repr
      ensures ValidAndFresh()
    {
      var id := locations[name];
      calls.Add(id);
      Repr := {this} + calls.Repr;
    }
  }
}