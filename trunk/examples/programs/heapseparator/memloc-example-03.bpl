//#Safe
/*
 * expected partitioning result: 2 blocks
 */
var #memory_int, #valid : [int] int;

procedure main();
modifies #memory_int, #valid;

implementation main() {
  var p, q, p1, q1, x, y : int;

  assume #valid[p] == 0;
  #valid[p] := 1;
 
  #memory_int[p] := 5;

  call q := foo();

  assume p1 == p && q1 == q;

  x := #memory_int[p1];
  y := #memory_int[q1];
  
  assert x == 5;
}

procedure foo() returns (res : int);
modifies #memory_int, #valid;

implementation foo() returns (res : int) {
  var i : int;

  assume #valid[i] == 0;
  #valid[i] := 1;

  #memory_int[i] := 7;

  res := i;
}