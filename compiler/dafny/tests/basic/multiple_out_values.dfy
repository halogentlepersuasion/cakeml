method Main() {
  var a, b, c := foo();
	print a, " ", b, " ", c, "\n";
}

method foo() returns (a: int, b: int, c: int) {
    return 1, 2, 3;
}
