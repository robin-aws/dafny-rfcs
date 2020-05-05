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
    var generator: RandomNumberGenerator?
    const profiler: Profiler
    const fibonacciMemoized: Memoizer
    const factorialMemoized: Memoizer

    constructor() 
      ensures profiler.Valid() 
      ensures fresh(profiler.Repr)
      ensures generator != null && generator.Valid()
      ensures fresh(generator.Repr)
      ensures fibonacciMemoized.Valid()
      ensures fresh(fibonacciMemoized)
      ensures factorialMemoized.Valid()
      ensures fresh(factorialMemoized)
    {
      var singletons := new AllSingletons();
      this.singletons := singletons;

      profiler := new Profiler(singletons);

      var generator := new MyRandomNumberGenerator();
      this.generator := generator;
      var wrapper := new RandomNumberGeneratorAsValidatable(singletons, generator);
      assert singletons.AllValid();
      fibonacciMemoized := new Memoizer(singletons, (n: nat) => Fibonacci(n));
      factorialMemoized := new Memoizer(singletons, (n: nat) => Factorial(n));

      new;
      
      profiler.AddLocation("Foo");
      profiler.AddLocation("Bar");
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

    var random := globals.generator.Generate(10);

    expect "Foo" in globals.profiler.locations;
    globals.profiler.RecordCall("Foo");

    var tenthFactorial := globals.factorialMemoized.Apply(10);
  }
}

