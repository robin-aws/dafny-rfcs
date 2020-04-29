
- Feature Name: module-constructors
- Start Date: 2020-04-29
- RFC PR: [dafny-lang/rfcs#2](https://github.com/dafny-lang/rfcs/pull/2)
- Dafny Issue: 

# Summary
[summary]: #summary

Two new features related to Fields in modules:

1. Allow `var` and not just `const`
2. Allow heap values

The second is not currently a direct restriction, but a consequence of the fact that there is no way of obtaining an object reference in a logical expression other than `null`.



# Motivation
[motivation]: #motivation

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

* Need to define an ordering of statements

# Drawbacks
[drawbacks]: #drawbacks

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

# Prior art
[prior-art]: #prior-art

# Unresolved questions
[unresolved-questions]: #unresolved-questions

# Future possibilities
[future-possibilities]: #future-possibilities



### Static "resources"

```dafny
module System {
  
  class FileHandleOutput {
    const handle: int

    constructor(handle: int) {
      this.handle := handle;
    }
  }

  const STDOUT: FileHandleOutput
  const STDERR: FileHandleOutput

  constructor() {
    STDOUT := new FileHandleOutput(1);
    STDERR := new FileHandleOutput(2);
  }
}
```

### Dependency Injection

```dafny

```