include "./Validatable.dfy"

module Random {

  import opened Validation

  class Singleton extends Validatable {

    var generatorWrapper: RandomNumberGeneratorAsValidatable?

    constructor() 
      ensures Valid() 
      ensures fresh(Repr) 
    {
      var generator := new MyRandomNumberGenerator();
      this.generatorWrapper := new RandomNumberGeneratorAsValidatable(generator);
      new;
      Repr := {this} + generatorWrapper.Repr;
    }

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && generatorWrapper != null
      && ValidComponent(generatorWrapper)
    }

    method GenerateRandom(context: ValidSet, max: nat) returns (res: nat) 
      requires Valid()
      requires context.Valid()
      requires this in context.objects
      requires 0 < max
      modifies Repr, context
      ensures Valid()
      ensures context.Valid()
    {
      res := generatorWrapper.Generate(max);
      Repr := Repr + generatorWrapper.Repr;

      context.Repr := context.Repr + Repr;
      context.Updated(this);
    }
  }

  trait RandomNumberGenerator {
    ghost var Repr: set<object>
    predicate Valid() 
      reads this, Repr
      ensures Valid() ==> this in Repr

    method Generate(max: nat) returns (res: nat) 
      requires Valid()
      requires 0 < max
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
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

    predicate Valid() 
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      Repr == {this}
    }
    
    method Generate(max: nat) returns (res: nat)
      requires Valid()
      requires 0 < max
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures 0 <= res < max 
    {
      if next >= max {
        next := 0;
      }
      res := next;
      next := next + 1;
    }
  }

  // Adaptor - only necessary because RandomNumberGenerator can't extend
  // Validatable itself. Useful to show existing types can be plugged into
  // the system though.
  class RandomNumberGeneratorAsValidatable extends Validatable {
    const generator: RandomNumberGenerator

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && generator in Repr
      && generator.Repr <= Repr
      && this !in generator.Repr
      && generator.Valid()
    }

    constructor(generator: RandomNumberGenerator)
      requires generator.Valid()
      ensures Valid()
      ensures fresh(Repr - generator.Repr)
    {
      this.generator := generator;
      this.Repr := {this} + generator.Repr;
      new;
    }

    method Generate(max: nat) returns (res: nat)
      requires Valid()
      requires 0 < max
      modifies Repr
      ensures ValidAndFresh()
      ensures 0 <= res < max 
    {
      res := generator.Generate(max);
      Repr := {this} + generator.Repr;
    }
  }
}