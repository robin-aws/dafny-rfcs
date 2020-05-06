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
      ensures fresh(singletons.singletonReprs)
    {
      var singletons := new AllSingletons();
      this.singletons := singletons;

      var profiler := new Profiler();
      this.profiler := profiler;
      singletons.AddSingleton(profiler);

      var generator := new MyRandomNumberGenerator();
      var generatorWrapper := new RandomNumberGeneratorAsValidatable(generator);
      this.generatorWrapper := generatorWrapper;
      singletons.AddSingleton(generatorWrapper);

      fibonacciMemoized := new Memoizer((n: nat) => Fibonacci(n));
      factorialMemoized := new Memoizer((n: nat) => Factorial(n));
      
      new;
      
      singletons.AddSingleton(profiler);
      
      profiler.AddLocation(singletons, "Foo");
      profiler.AddLocation(singletons, "Bar");
      assert fresh(fibonacciMemoized.Repr);
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
    }

    globals.singletons.ExpectValid(globals.profiler);
    expect "Foo" in globals.profiler.locations;
    globals.profiler.RecordCall("Foo");

    globals.singletons.ExpectValid(globals.factorialMemoized);
    var tenthFactorial := globals.factorialMemoized.Apply(10);

    globals.singletons.ExpectValid(globals.fibonacciMemoized);
    var tenthFibonacci := globals.fibonacciMemoized.Apply(10);
  }
}

