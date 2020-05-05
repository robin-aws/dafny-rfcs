include "./Profiler.dfy"
include "./Random.dfy"

module Singletons {

  import opened Profiling
  import opened Random

  class Globals {
    var generator: RandomNumberGenerator?
    const profiler: Profiler

    constructor() 
      ensures profiler.Valid() 
      ensures fresh(profiler.Repr)
      ensures generator != null
    {
      profiler := new Profiler();
      generator := new MyRandomNumberGenerator();
      
      new;
      
      profiler.AddLocation("Foo");
      profiler.AddLocation("Bar");
    }
  }

  method Main() {
    var globals := new Globals();

    var random := globals.generator.Generate(10);

    expect "Foo" in globals.profiler.locations;
    globals.profiler.RecordCall("Foo");
  }
}

