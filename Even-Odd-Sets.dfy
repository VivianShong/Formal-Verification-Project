/*** 
Name: Hong Shen; Student ID: 22338684 
Name: Leon Andorfi; Student ID: 23335878
***/
/*** Even ***/

ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
// The next three lemmas prove that modulo-based definition is equivalent to existential-based definition
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m; // Hint for Dafny to choose n/2 as witness for the existential in the isEven predicate
	}
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
// Useful lemma that may be used later
// It shows that the product of two integers is even if at least one of them is even
lemma EvenTimesAny(n1: int, n2: int)
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
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{
  if n % 2 == 1 {
	  var m := n / 2;
	  assert n == 2 * m + 1;
	}
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
    var m1 :| n1 == 2 * m1 + 1;
    var m2 :| n2 == 2 * m2 + 1;
    var m := 2 * m1 * m2 + m1 + m2;
    assert n1 * n2 == 2 * m + 1;
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

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{
  if isEven(n) {
    var m :| n == 2 * m;
    assert invertParity(n) == 2 * m + 1;
  }
  if isOdd(n) {
    var m :| n == 2 * m + 1;
    assert invertParity(n) == 2 * (m + 1);
  }
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) 
{
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
 isSet(s) && forall i :: 0<=i<|s| ==> isEven(s[i])
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  ensures b <==> isEvenSet(s)
{ 
  b := isSet(s) && forall i :: 0 <= i < |s| ==> checkEven(s[i]);
  forall i | 0 <= i < |s| ensures checkEven(s[i]) <==> isEven(s[i])
  {
    checkEvenCorrect(s[i]);
  }
}

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  
  isSet(s) && forall i :: 0<=i<|s| ==> isOdd(s[i])
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{
  b := isSet(s) && forall i :: 0 <= i < |s| ==> checkOdd(s[i]);
  forall i | 0 <= i < |s| ensures checkOdd(s[i]) <==> isOdd(s[i])
  {
    checkOddCorrect(s[i]);
  }
}

/*** Set Operations ***/

// For the following methods specify their behaviour so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
// Marks will be awarded for specifying as much as possible all relevant properties of the output.

/* Adds n to a set s, making sure it remains a set */
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
  requires isSet(s)
  ensures isSet(b)
  ensures forall x :: x in b <==> (x in s || x == n)
  ensures n in s ==> b == s
  ensures n !in s ==> b == s + [n]
{
  if n in s {
    b := s;
  } else {
    b := s + [n];
  }
}

/* Unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  ensures isSet(t)
  ensures forall x :: x in t <==> (x in s1 || x in s2)
  ensures |t| <= |s1| + |s2|
{
  t := [];
  var elements := s1 + s2;
  var i := 0;

  while i < |elements|
    invariant 0 <= i <= |elements|
    invariant isSet(t)
    invariant |t| <= i
    invariant forall x :: x in t <==> x in elements[..i]
  {
    t := addToSet(t, elements[i]);
    i := i + 1;
  }
  assert elements[..i] == elements;
}

/* Intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  ensures isSet(t)
  ensures forall x :: x in t <==> (x in s1 && x in s2)
  ensures |t| <= |s1|
{
  t := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant |t| <= i
    invariant forall x :: x in t <==> (x in s1[..i] && x in s2)
  {
    if s1[i] in s2 {
      t := addToSet(t, s1[i]);
    }
    i := i + 1;
  }
  assert s1[..i] == s1;
}

/* Difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  ensures isSet(t)
  ensures forall x :: x in t <==> (x in s1 && x !in s2)
  ensures |t| <= |s1|
{
  t := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant |t| <= i
    invariant forall x :: x in t <==> (x in s1[..i] && x !in s2)
  {
    if s1[i] !in s2 {
      t := addToSet(t, s1[i]);
    }
    i := i + 1;
  }
  assert s1[..i] == s1;
}

/* Multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
  requires isSet(s)
  ensures isSet(t)
  // t contains exactly the scaled elements of s
  ensures forall x :: x in t <==> (exists i :: 0 <= i < |s| && x == s[i] * n)
  ensures |t| <= |s|
  // Scaling by a non-zero n is injective, so no elements are merged
  ensures n != 0 ==> |t| == |s|
  // Scaling by 0 collapses a non-empty set to {0}
  ensures n == 0 && |s| > 0 ==> t == [0]
  // Parity properties
  ensures isEven(n) ==> isEvenSet(t)
  ensures isEvenSet(s) ==> isEvenSet(t)
  ensures isOdd(n) && isOddSet(s) ==> isOddSet(t)
{
  t := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant isSet(t)
    invariant |t| <= i
    invariant forall x :: x in t <==> (exists k :: 0 <= k < i && x == s[k] * n)
  {
    t := addToSet(t, s[i] * n);
    i := i + 1;
  }
}

/* Computes the product set of two sets s1 and s2, returning a new set t = { n * m | n in s1, m in s2 }  */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  // t contains exactly the pairwise products of elements of s1 and s2
  ensures forall x :: x in t <==>
            (exists i, j :: 0 <= i < |s1| && 0 <= j < |s2| && x == s1[i] * s2[j])
  ensures |t| <= |s1| * |s2|
  // The product set is empty iff one of the inputs is empty
  ensures |t| == 0 <==> (|s1| == 0 || |s2| == 0)
  // Parity properties (EvenTimesAny / OddTimesOdd lifted to sets)
  ensures isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{
  t := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant |t| <= i * |s2|
    // t holds exactly the products from rows 0..i-1
    invariant forall x :: x in t <==>
                (exists a, b :: 0 <= a < i && 0 <= b < |s2| && x == s1[a] * s2[b])
  {
    var j := 0;
    while j < |s2|
      invariant 0 <= j <= |s2|
      invariant isSet(t)
      invariant |t| <= i * |s2| + j
      // t holds rows 0..i-1 plus the first j products of row i
      invariant forall x :: x in t <==>
                  ((exists a, b :: 0 <= a < i && 0 <= b < |s2| && x == s1[a] * s2[b]) ||
                   (exists b :: 0 <= b < j && x == s1[i] * s2[b]))
    {
      t := addToSet(t, s1[i] * s2[j]);
      j := j + 1;
    }
    i := i + 1;
  }
}

/* Converts an even set to an odd set by inverting the parity of each element
   Hint: Use the invertParity function */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
  requires isSet(s)
  ensures isSet(t)
  // Element-wise: t is s with invertParity applied at each position (order preserved)
  ensures |t| == |s|
  ensures forall i :: 0 <= i < |s| ==> t[i] == invertParity(s[i])
  ensures forall x :: x in t <==> (exists i :: 0 <= i < |s| && x == invertParity(s[i]))
  // Parity flips for the whole set
  ensures isEvenSet(s) ==> isOddSet(t)
  ensures isOddSet(s) ==> isEvenSet(t)
{
  t := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall k :: 0 <= k < i ==> t[k] == invertParity(s[k])
    // invertParity is injective (n + 1) and s has no duplicates, so t has none either
    invariant isSet(t)
  {
    t := t + [invertParity(s[i])];
    i := i + 1;
  }
}
