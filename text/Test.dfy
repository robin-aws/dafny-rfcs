include "./Profiler.dfy"
include "./Random.dfy"
include "./Memoization.dfy"
include "./Validatable.dfy"

module SingletonsTest {

  import opened Profiling
  import opened Random
  import opened Memoization
  import opened Validation

  // Top-level object used to simulate singleton support.
  // Ultimately, singletons are equivalent to explicitly passing shared
  // objects as extra arguments to every function and method, and that's what
  // I'm doing here. It means that verification should be tractable no matter what,
  // but we could be stuck with a lot of repetition. The intention is for IndependentSet
  // to abstract that away, and it's promising so far but the POC is not yet complete
  // (this file is currently hanging the verification process).
  class Globals {
    const singletons: IndependentSet
    var random: Random.Singleton
    const profiler: Profiler
    const fibonacciMemoized: Memoizer
    const factorialMemoized: Memoizer

  
    constructor() 
      ensures singletons.Valid()
      ensures fresh(singletons.Repr)
      ensures random.Valid()
      ensures fresh(random.Repr)
      ensures random in singletons.Repr
    {
      this.singletons := new IndependentSet({});

      this.profiler := new Profiler();
      
      this.random := new Random.Singleton();
      
      fibonacciMemoized := new Memoizer((n: nat) => Fibonacci(n));
      factorialMemoized := new Memoizer((n: nat) => Factorial(n));
      
      new;

      singletons.Add(profiler);
      singletons.Add(random);
      singletons.Add(fibonacciMemoized);
      singletons.Add(factorialMemoized);
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
      
    // var randomNumber := globals.random.GenerateRandom(globals.singletons, 10);
    // globals.singletons.Updated(globals.random);
    // assert globals.singletons.Valid();

    expect "Foo" in globals.profiler.locations;
    expect globals.profiler in globals.singletons.objects;
    RecordCall(globals, "Foo");
    
    expect globals.fibonacciMemoized in globals.singletons.objects;
    var tenthFibonacci := FibonacciMemoized(globals, 10);
  }

  method FibonacciMemoized(globals: Globals, n: nat) returns (res: nat)
    requires globals.singletons.Valid()
    requires globals.fibonacciMemoized in globals.singletons.objects
    modifies globals.fibonacciMemoized.Repr, globals.singletons
    ensures globals.singletons.ValidAndFresh()
  {
    res := globals.fibonacciMemoized.Apply(n);

    globals.singletons.Repr := globals.singletons.Repr + globals.fibonacciMemoized.Repr;
    globals.singletons.Updated(globals.fibonacciMemoized);
  }

  method RecordCall(globals: Globals, name: string)
    requires globals.singletons.Valid()
    requires globals.profiler in globals.singletons.objects
    requires name in globals.profiler.locations
    modifies globals.profiler.Repr, globals.singletons
    ensures globals.singletons.ValidAndFresh()
  {
    globals.profiler.RecordCall(name);

    globals.singletons.Repr := globals.singletons.Repr + globals.profiler.Repr;
    globals.singletons.Updated(globals.profiler);
  }
}

