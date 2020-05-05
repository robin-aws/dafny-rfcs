module Random {
  trait RandomNumberGenerator {
    method Generate(max: nat) returns (res: nat) 
      requires 0 < max
      ensures 0 <= res < max
  }

  class MyRandomNumberGenerator extends RandomNumberGenerator {
    constructor() {}

    method Generate(max: nat) returns (res: nat)
      requires 0 < max
      ensures 0 <= res < max 
    {
      // What :)
      return max / 2;
    }
  }
}