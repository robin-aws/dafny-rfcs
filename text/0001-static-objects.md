
- Feature Name: static-objects
- Start Date: 2020-04-30
- RFC PR: [dafny-lang/rfcs#2](https://github.com/dafny-lang/rfcs/pull/2)
- Dafny Issue: 

# Summary
[summary]: #summary

This feature would allow top-level references to the heap, which are currently only allowed inside class definitions.

It consists of two separate but closely-related changes to the language:

1. allowing module fields to be mutable (i.e. allowing `var` and not just `const`), and
2. providing "module constructors" that can execute statements in order to initialize fields.

The first implies that module fields are allowed to exist on the heap, and the second allows even constant fields to refer to objects on the heap.

# Motivation
[motivation]: #motivation

Dafny currently cannot share any implicit mutable state between contexts: objects must be provided as explicit parameters to all methods.

TODO: more here - some of the good stuff is in the next section.

It is technically possible to declare module fields with class or trait types, but it is not possible to set them to anything other than null, because their right-hand side must be a logical expression. This in turn makes it impossible to provide heap-based witnesses ([#339](https://github.com/dafny-lang/dafny/issues/339)).

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

Modules would be permitted to declare `var` fields as well as `const` fields. Their right-hand sides will still be restricted to logical expressions.

```dafny
module Foo {
  var x := 42
  var y := x * 7
  var z: int                // Implicity set to 0
  
  var o1: object?           // Implicitly set to null
  var o2: MyClass? := null  
  var o3: MyClass           // Must be initialized in constructor
}
```

To support initializing fields with object types (constant or variable), modules would be permitted at most one constructor. This constructor is automatically executed exactly once, and must:

1. be anonymous,
2. take no parameters,
3. specify no `requires` clauses (although they implicitly assume the post-condition of all imported module constructors),
4. not specify `decreases *`,
4. ???

Here are some examples:

## Example 1: Shared resources

```dafny
module System {
  
  class FileHandleOutput {
    const handle: int

    constructor(handle: int) {
      this.handle := handle;
    }

    ...
  }

  const STDOUT: FileHandleOutput
  const STDERR: FileHandleOutput

  constructor() {
    STDOUT := new FileHandleOutput(1);
    STDERR := new FileHandleOutput(2);
  }
}
```

## Example 2: Dependency injection

```dafny
module Math {

  trait RandomNumberGenerator {
    method Generate(max: int) returns (res: int)
  }

  var RandomImpl: RandomNumberGenerator?

  method SetRandomNumberGenerator(impl: RandomNumberGenerator) 
    requires RandomImpl == null 
  {
    RandomImpl := impl;
  }

  method GetRandomNumber(max: int) returns (res: int) 
    requires RandomImpl != null
  {
    res := RandomImpl.Generate(max);
  }
}
```

This pattern will be particularly useful in allowing native code to be developed as a separately-compiled entity which registers its implementations on initialization. If `GetRandomNumber` was an `{:extern}` method instead, the external implementation has to be available in order to build the Dafny package in many target languages.

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

Modules would be constructed in the order they are encountered in a depth-first traversal of the module import graph, where the order of edges between modules is determined by the order of `import` statements. Because this graph must be acyclical, and since the contents of the module constructor can only reference imported modules, this would ensure circular dependencies between module initialization is not possible.

The post-conditions of module constructors would be required to be no weaker than the post-conditions of the modules they import. For example:

```dafny
module A {
  var x: nat
  predicate Valid() {
    x > 1
  }
  constructor() ensures Valid() {
    x := 12;
  }
}

module B {
  import A
  var y: nat
  predicate Valid() {
    y % 2 == 0
  }
  constructor() ensures Valid() && A.Valid() {
    y := 10;
    A.x := A.x + y;
  }
}
```

Module constructors would have similar rules around refinement to module methods: if `A refines B` and both `A` and `B` define a module constructor, `A`'s must be a valid refinement of `B`'s.

# Drawbacks
[drawbacks]: #drawbacks

Verification will potentially be more complicated, since it must account for the presence of globally-addressable objects. They would still have to be mentioned in `modifies` clauses, but the challenge will be in avoiding having all methods explicitly specify that they do not modify these objects. We may need new heuristics to assume they are disjoint from most `Repr`s unless stated otherwise.

A motivating example:

```dafny
module Foo {

  class Collector {

    ...

    ghost var Repr: set<object>
    predicate Valid() reads Repr
    
    constructor() ensures Valid() { ... }

    method Collect(x: int)
    ...
  }

  const SharedCollector: Collector

  constructor() {
    SharedCollector := new Collector();
  }

  method Main() {
    SomeOtherMethodThatHasNeverHeardOfCollectors();

    // How to prove that SharedCollector.Valid() is true here?
    SharedCollector.Collect(42);
  }
}
```

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

Using "constructor" for the initialization method allows us to avoid introducing another keyword, but is slightly confusing. It does imply the same two-phase initialization constraints that class constructors require, although allowing the `new;` statement in module constructors is also questionable.

An alternate version of this proposal (c/o Rustan) would introduce "singleton" objects instead, which are similar to class definitions but define a single object instance, and with the same constructor restrictions as proposed for modules above.

TODO: pros and cons. 

Here are the examples above using this variant:

```dafny
singleton System {
  
  class FileHandleOutput {
    const handle: int

    constructor(handle: int) {
      this.handle := handle;
    }

    ...
  }

  const STDOUT: FileHandleOutput
  const STDERR: FileHandleOutput

  constructor() {
    STDOUT := new FileHandleOutput(1);
    STDERR := new FileHandleOutput(2);
  }
}

singleton Math {

  trait RandomNumberGenerator {
    method Generate(max: int) returns (res: int)
  }

  var RandomImpl: RandomNumberGenerator?

  method SetRandomNumberGenerator(impl: RandomNumberGenerator) 
    requires RandomImpl == null 
  {
    RandomImpl := impl;
  }

  method GetRandomNumber(max: int) returns (res: int) 
    requires RandomImpl != null
  {
    res := RandomImpl.Generate(max);
  }
}

module Foo {

  singleton SharedCollector {
    ...

    ghost var Repr: set<object>
    predicate Valid() reads Repr
    
    constructor() ensures Valid() { ... }

    method Collect(x: int)
    ...
  }

  method Main() {
    SomeOtherMethodThatHasNeverHeardOfCollectors();

    // How to prove that SharedCollector.Valid() is true here?
    SharedCollector.Collect(42);
  }
}
```

# Prior art
[prior-art]: #prior-art

Several other languages have similar, if more powerful and error-prone, features.

**Java**: *Static class fields* are roughly equivalent to module fields, and do not have to be `final`. They can be initialized as they are declared, or in separate `static { ... }` code blocks in the class.

TODO: More! e.g. Scripting languages let you perform basically any statements at the top-level.

# Unresolved questions
[unresolved-questions]: #unresolved-questions

Do we need to allow a refining module to change a `var` field to a `const` or vice-versa? I believe neither is valid in general.

# Future possibilities
[future-possibilities]: #future-possibilities

The initial version of this feature only needs to support initializing module fields in the single constructor. In the future, we could add support for initializing fields when they are declared, using the same syntax for initializing variables:

```dafny
module Foo {

  var x := 5
  var y := new MyClass(x)
  const z := MakeObject(y)
}
```

These statements would be executed in textual order immediately before the constructor is executed, if provided. This would be pure sugar: the generic compiler could prepend these module-level statements to any user-provided constructor, maintaining order.
 