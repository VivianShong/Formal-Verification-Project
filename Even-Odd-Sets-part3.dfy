
/*** Even ***/

ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m;
	}
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
lemma EvenTimes(n1: int, n2: int)
  ensures isEven(n1) || isEven(n2) ==> isEven(n1 * n2)
{
  if isEven(n1) {
	var m1 := n1 / 2;
	assert n1 * n2 == 2 * (m1 * n2);
  } else if isEven(n2) {
	var m2 := n2 / 2;
	assert n1 * n2 == 2 * (n1 * m2);
  }
}

/*** Odd ***/

ghost predicate isOdd(n: int) {
  exists m: int :: n == 2 * m + 1
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{
	if n % 2 != 0 {
	  var m := n / 2;
	  assert n == 2 * m + 1;
	}
}
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{
	OddModulo(n);
	ModuloOdd(n);
}
lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{
  if isOdd(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1 + m2) + 1;
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{
  if n % 2 == 0 {
	ModuloEven(n);
  } else {
	ModuloOdd(n);
  }
}

lemma EvenTimesOdd(n1: int, n2: int)
  ensures isEven(n1) && isOdd(n2) ==> isEven(n1 * n2)
{
  if isEven(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1);
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{
	if isEven(n) {
		var m := invertParity(n);
		ModuloOdd(m);
	} else {
		var m := invertParity(n);
		ModuloEven(m);
	}
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
  forall i, j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == s[j] ==> i == j
}

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  ensures b <==> isSet(s)
{
  b := isSet(s);
}

/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
 isSet(s) && forall x :: x in s ==> isEven(x)
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  ensures b <==> isEvenSet(s)
{
  b := isSet(s) && forall x :: x in s ==> checkEven(x);
  forall x | x in s ensures checkEven(x) <==> isEven(x)
  {
    checkEvenCorrect(x);
  }
}

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  isSet(s) && forall x :: x in s ==> isOdd(x)
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{
  b := isSet(s) && forall x :: x in s ==> checkOdd(x);
  forall x | x in s ensures checkOdd(x) <==> isOdd(x)
  {
    checkOddCorrect(x);
  }
}

/*** Set Operations ***/

/* Adds n to a set s, making sure it remains a set */
// Hint: use recursion
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
  requires isSet(s)
  ensures isSet(b)
  ensures forall x :: (0 <= x < |b|) ==> (b[x] in s || b[x] == n)
  ensures forall x :: (0 <= x < |s|) ==>  s[x] in b
  ensures n in s ==> b == s
  ensures !(n in s) ==> b == s + [n]
  ensures isEvenSet(s) && isEven(n) ==> isEvenSet(b)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(b)
{
  if n in s {
    b := s;
  } else {
    b := s + [n];
  }
}

/* unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 || t[x] in s2)
  ensures forall x :: (0 <= x < |s1| ==> s1[x] in t)
  ensures forall x :: (0 <= x < |s2| ==> s2[x] in t)
  ensures isEvenSet(s1) && isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{
  t := [];
  var elements := s1 + s2;
  var i := 0;
  while i < |elements|
    invariant 0 <= i <= |elements|
    invariant isSet(t)
    invariant forall x :: x in t <==> x in elements[..i]
  {
    t := addToSet(t, elements[i]);
    i := i + 1;
  }
  assert elements[..i] == elements;
  forall x | 0 <= x < |t| ensures t[x] in s1 || t[x] in s2
  {
    assert t[x] in elements;
  }
}

/* intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && t[x] in s2)
  ensures forall x, y :: (0 <= x < |s1| && 0 <= y < |s2| && s1[x] == s2[y]) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
{
  t := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant forall x :: x in t <==> (x in s1[..i] && x in s2)
    invariant isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
  {
    // An element cannot be both even and odd, so if s1 is even and s2 is odd,
    // s1[i] is never in s2 and t stays empty
    NotEvenANDOdd(s1[i]);
    if s1[i] in s2 {
      t := addToSet(t, s1[i]);
    }
    i := i + 1;
  }
  assert s1[..i] == s1;
}

/* difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && !(t[x] in s2))
  ensures forall x :: (0 <= x < |s1| && !(s1[x] in s2)) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> t == s1 // hint: don't use addToSet in your code -- use t + [s1[i]] instead
{
  t := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant forall x :: x in t <==> (x in s1[..i] && x !in s2)
    invariant isEvenSet(s1) && isOddSet(s2) ==> t == s1[..i]
  {
    // An element cannot be both even and odd, so if s1 is even and s2 is odd,
    // s1[i] is never in s2 and every element of s1 is kept
    NotEvenANDOdd(s1[i]);
    assert s1[..i+1] == s1[..i] + [s1[i]];
    if s1[i] !in s2 {
      // s1 has no duplicates, so s1[i] is not already in t
      assert s1[i] !in s1[..i];
      t := t + [s1[i]];
    }
    i := i + 1;
  }
  assert s1[..i] == s1;
}

/* multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> exists i :: 0<= i < |s| && t[x] == s[i] * n)
  ensures forall x :: (0 <= x < |s| ==> s[x] * n in t)
  ensures isEvenSet(s) || isEven(n) ==> isEvenSet(t)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(t)
{
  t := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant isSet(t)
    invariant forall x :: x in t ==> exists k :: 0 <= k < i && x == s[k] * n
    invariant forall k :: 0 <= k < i ==> s[k] * n in t
    invariant isEvenSet(s) || isEven(n) ==> isEvenSet(t)
    invariant isOddSet(s) && isOdd(n) ==> isOddSet(t)
  {
    EvenTimes(s[i], n);
    OddTimesOdd(s[i], n);
    t := addToSet(t, s[i] * n);
    i := i + 1;
  }
  forall x | 0 <= x < |t| ensures exists k :: 0 <= k < |s| && t[x] == s[k] * n
  {
    assert t[x] in t;
  }
}

// Supporting definitions for setProduct.
// They are opaque so that the product terms s1[a] * s2[b] stay hidden from Dafny
// except where they are needed; otherwise verification of setProduct times out.

// x is the product of an element from the first i elements of s1 with an element of s2
ghost opaque predicate ProdIn(x: int, s1: seq<int>, s2: seq<int>, i: int)
{
  exists a, b :: 0 <= a < i && 0 <= a < |s1| && 0 <= b < |s2| && x == s1[a] * s2[b]
}

// Every product of an element from the first i elements of s1 with an element of s2 is in t
ghost opaque predicate RowsIn(t: seq<int>, s1: seq<int>, s2: seq<int>, i: int)
{
  forall a, b :: 0 <= a < i && 0 <= a < |s1| && 0 <= b < |s2| ==> s1[a] * s2[b] in t
}

// Adding row i (s2 scaled by s1[i]) to t extends both properties from i to i + 1
lemma ProductStep(t: seq<int>, row: seq<int>, t': seq<int>, s1: seq<int>, s2: seq<int>, i: int)
  requires 0 <= i < |s1|
  requires forall x :: x in t ==> ProdIn(x, s1, s2, i)
  requires RowsIn(t, s1, s2, i)
  // what setScale(s2, s1[i]) guarantees about row
  requires forall x :: (0 <= x < |row| ==> exists k :: 0 <= k < |s2| && row[x] == s2[k] * s1[i])
  requires forall x :: (0 <= x < |s2| ==> s2[x] * s1[i] in row)
  // what union(t, row) guarantees about t'
  requires forall x :: (0 <= x < |t'| ==> t'[x] in t || t'[x] in row)
  requires forall x :: (0 <= x < |t| ==> t[x] in t')
  requires forall x :: (0 <= x < |row| ==> row[x] in t')
  ensures forall x :: x in t' ==> ProdIn(x, s1, s2, i + 1)
  ensures RowsIn(t', s1, s2, i + 1)
{
  forall x | x in t' ensures ProdIn(x, s1, s2, i + 1)
  {
    var k :| 0 <= k < |t'| && t'[k] == x;
    if x in t {
      assert ProdIn(x, s1, s2, i);
      reveal ProdIn();
    } else {
      var r :| 0 <= r < |row| && row[r] == x;
      var b :| 0 <= b < |s2| && x == s2[b] * s1[i];
      assert x == s1[i] * s2[b];
      reveal ProdIn();
    }
  }
  reveal RowsIn();
  forall a, b | 0 <= a < i + 1 && 0 <= a < |s1| && 0 <= b < |s2|
    ensures s1[a] * s2[b] in t'
  {
    if a < i {
      var k :| 0 <= k < |t| && t[k] == s1[a] * s2[b];
    } else {
      assert s2[b] * s1[i] in row;
      var k :| 0 <= k < |row| && row[k] == s2[b] * s1[i];
      assert s1[a] * s2[b] == s2[b] * s1[i];
    }
  }
}

method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: x in t ==> exists i1, j1 :: 0<= i1 < |s1| && 0<= j1 < |s2| && x == s1[i1] * s2[j1]
  ensures forall i1, j1 :: i1 in s1 && j1 in s2 ==> i1 * j1 in t
  ensures isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{
  t := [];
  var i := 0;
  reveal RowsIn();
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    // t holds exactly the products from rows 0..i-1
    invariant forall x :: x in t ==> ProdIn(x, s1, s2, i)
    invariant RowsIn(t, s1, s2, i)
    invariant isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
    invariant isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
  {
    // Row i: every element of s2 multiplied by s1[i]
    // (setScale proves the parity facts using EvenTimes / OddTimesOdd)
    assert s1[i] in s1;
    var row := setScale(s2, s1[i]);
    var t' := union(t, row);
    ProductStep(t, row, t', s1, s2, i);
    t := t';
    i := i + 1;
  }
  // Translate the invariants into the postconditions
  reveal ProdIn();
  forall i1, j1 | i1 in s1 && j1 in s2
    ensures i1 * j1 in t
  {
    var a :| 0 <= a < |s1| && s1[a] == i1;
    var b :| 0 <= b < |s2| && s2[b] == j1;
    assert s1[a] * s2[b] in t;
  }
}


/* converts an even set to an odd set by inverting the parity of each element  */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
  requires isEvenSet(s) || isOddSet(s)
  ensures isEvenSet(s) ==> isOddSet(t)
  ensures isOddSet(s) ==> isEvenSet(t)
  ensures |t| == |s|
  ensures forall i :: 0 <= i < |s| ==> t[i] == invertParity(s[i])
{
  t := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall k :: 0 <= k < i ==> t[k] == invertParity(s[k])
    // invertParity is injective (n + 1) and s has no duplicates, so t has none either
    invariant isSet(t)
    invariant isEvenSet(s) ==> isOddSet(t)
    invariant isOddSet(s) ==> isEvenSet(t)
  {
    InvertParityCorrect(s[i]);
    t := t + [invertParity(s[i])];
    i := i + 1;
  }
}
