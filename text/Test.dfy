include "./Profiler.dfy"
include "./Random.dfy"
include "./Memoization.dfy"
include "./Validatable.dfy"

module SingletonsTest {

  import opened Profiling
  import opened Random
  import opened Memoization
  import opened Validation

  // Top-level object used to simulate singleton support
  class Globals {
    const singletons: ValidSet
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
      this.singletons := new ValidSet({});

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

