include "./Profiler.dfy"
include "./Random.dfy"
include "./Memoization.dfy"

module Singletons {

  import opened Profiling
  import opened Random
  import opened Memoization

  class Globals {
    var generator: RandomNumberGenerator?
    const profiler: Profiler
    const fibonacciMemoized: Memoizer<nat, nat>
    const factorialMemoized: Memoizer<nat, nat>

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
      profiler := new Profiler();
      generator := new MyRandomNumberGenerator();
      fibonacciMemoized := new Memoizer(n => Fibonacci(n));
      factorialMemoized := new Memoizer(n => Factorial(n));

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

