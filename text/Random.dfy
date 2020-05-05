module Random {
  trait RandomNumberGenerator {
    ghost var Repr: set<object>
    predicate Valid() 
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr
    }
    method Generate(max: nat) returns (res: nat) 
      requires Valid()
      requires 0 < max
      modifies Repr
      ensures Valid()
      ensures 0 <= res < max 
  }

  // Goofy implementation that technically obeys the spec. :)
  class MyRandomNumberGenerator extends RandomNumberGenerator {
    var next: nat
    constructor() 
      ensures Valid() 
      ensures fresh(Repr)
    {
      Repr := {this};
    }

    method Generate(max: nat) returns (res: nat)
      requires Valid()
      requires 0 < max
      modifies Repr
      ensures Valid()
      ensures 0 <= res < max 
    {
      if next >= max {
        next := 0;
      }
      res := next;
      next := next + 1;
    }
  }
}