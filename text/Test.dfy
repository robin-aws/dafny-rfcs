include "./Profiler.dfy"
include "./Random.dfy"
include "./Memoization.dfy"
include "./Validatable.dfy"

module Singletons {

  import opened Profiling
  import opened Random
  import opened Memoization
  import opened Validation

  class Globals {
    const singletons: AllSingletons
    var generatorWrapper: RandomNumberGeneratorAsValidatable?
    const profiler: Profiler
    const fibonacciMemoized: Memoizer
    const factorialMemoized: Memoizer

    constructor() 
      ensures singletons.AllValid()
      ensures fresh(singletons)
      ensures fresh(singletons.singletonReprs)
    {
      this.singletons := new AllSingletons();

      this.profiler := new Profiler();
      
      var generator := new MyRandomNumberGenerator();
      this.generatorWrapper := new RandomNumberGeneratorAsValidatable(generator);
      
      fibonacciMemoized := new Memoizer((n: nat) => Fibonacci(n));
      factorialMemoized := new Memoizer((n: nat) => Factorial(n));
      
      new;

      singletons.AddSingleton(profiler);
      singletons.AddSingleton(generatorWrapper);
      singletons.AddSingleton(fibonacciMemoized);
      singletons.AddSingleton(factorialMemoized);
      
      profiler.AddLocation(singletons, "Foo");
      profiler.AddLocation(singletons, "Bar");
    }

    static function method Fibonacci(n: nat): nat
    {
      if n < 2 then n else Fibonacci(n-2) + Fibonacci(n-1)
    }

    static function method Factorial(n: nat): nat
    {
      if n == 0 then 1 else n * Factorial(n-1)
    }
  }

  method Main() {
    var globals := new Globals();
      
    if globals.generatorWrapper != null {
      globals.singletons.ExpectValid(globals.generatorWrapper);
      var random := globals.generatorWrapper.generator.Generate(10);
      if globals.generatorWrapper != null {
        globals.singletons.AllStillValid(globals.generatorWrapper);
        assert globals.singletons.AllValid();
      }
    }

    globals.singletons.ExpectValid(globals.profiler);
    expect "Foo" in globals.profiler.locations;
    globals.profiler.RecordCall("Foo");

    globals.singletons.ExpectValid(globals.factorialMemoized);
    var tenthFactorial := globals.factorialMemoized.Apply(10);

    globals.singletons.ExpectValid(globals.fibonacciMemoized);
    var tenthFibonacci := globals.fibonacciMemoized.Apply(10);
  }

  method GenerateRandom(globals: Globals, max: nat) returns (res: nat) 
    requires globals.singletons.AllValid()
    requires globals.generatorWrapper != null;
    requires 0 < max
    modifies globals.generatorWrapper.Repr
    ensures globals.singletons.AllValid()
  {
    globals.singletons.ExpectValid(globals.generatorWrapper);
    res := globals.generatorWrapper.Generate(max);
    globals.singletons.AllStillValid(globals.generatorWrapper);
  }

  method RecordCall(globals: Globals, name: string)
    requires globals.singletons.AllValid()
    requires name in globals.profiler.locations
    modifies globals.profiler.Repr, globals.singletons
    ensures globals.singletons.AllValid()
  {
    globals.singletons.ExpectValid(globals.profiler);
    assert globals.singletons !in globals.profiler.Repr;
    globals.profiler.RecordCall(name);
    assert globals.singletons !in globals.profiler.Repr;
    globals.singletons.singletonReprs := globals.singletons.singletonReprs + globals.profiler.Repr;
    assert globals.profiler.Valid();
    globals.singletons.AllStillValid(globals.profiler);
  }
}

