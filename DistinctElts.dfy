/* Here, we make the simplifying assumption that every element in the list is distinct. 
    The proof is still extremely non-trivial, but it allows us to reason about indices more directly */


function filter<T>(a: seq<T>, f:T -> bool) : seq<T>
decreases a 
{
  if (|a| > 0) then
    if (f(a[0])) then [a[0]] + filter(a[1..], f)
    else filter(a[1..], f)
  else a
}

lemma {: induction a} filterSize<T>(a: seq<T>, f: T -> bool, x:T)
requires (f(x))
ensures(multiset(a)[x] == multiset(filter(a, f))[x])
 {
  if (|a| <= 0) {}
  else {
    assert(a == [a[0]] + a[1..]);
  }
}


function numLt(x: int, a : seq<int>) : int
decreases x
{
  if x < 1 then 0 else
  if (x-1) in a then 1 + numLt(x-1, a) else numLt(x-1, a)
}

function numLeq(x: int, a : seq<int>) : int {
    numLt(x, a) + (if x in a then 1 else 0)
}

function numLt_alt(x: int, a : seq<int>) : int{
    |filter(a, y => y < x)|
}

lemma numLt_alt_minus(x: int, a : seq<int>)
ensures(numLt_alt(x-1, a) == |filter (a, y => y < x - 1)|) {

}

function numLeq_alt(x: int, a : seq<int>) : int {
  numLt_alt(x, a) + (if x in a then 1 else 0)
}

/*lemma idx_exists<T>(a:seq<T>, x : T) 
requires (x in a)
ensures(exists i :: 0 <= i < |a| && a[i] == x) {
}*/

//function and specification to find index of element - that is important in a few cases
function find_idx<T>(a:seq<T>, x : T) : int {
  if(|a| == 0) then -1
  else if (a[0] == x) then 0 else 1 + find_idx(a[1..], x)
}

lemma find_idx_spec<T>(a: seq<T>, x: T)
decreases a
requires (x in a)
ensures (0 <= find_idx(a,x) < |a|)
ensures(a[find_idx(a, x)] == x) {
  if(|a| == 0) {
  }
  else {
    if(a[0] == x) {
    }
    else {
      assert (x in (a[1..]));
    }
  }
}

predicate noDups<T>(a: array<T>)
reads a {
    forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length && i != j ==> a[i] != a[j]
}


predicate noDups_seq<T>(a: seq<T>) {
  forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]
}

lemma noDups_arr_to_seq<T>(a: array<T>)
requires(noDups(a))
ensures(noDups_seq(a[..])) {
}

//Holy shit, it proved this automatically!
lemma filter_lt_decompose(a: seq<int>, b : int)
requires(0 < b)
ensures(|filter(a, y => y < b)| == |filter(a, y => y < b - 1)| + |filter(a, y => y == b - 1)|) {
}

lemma {: induction a} filter_app<T>(a : seq<T>, b: seq<T>, f: T -> bool) 
ensures(filter(a + b, f) == filter(a, f) + filter(b, f) ) {
  if (|a| == 0) {
    assert (a == []);
    assert (a + b == b);
  }
  else {
    assert ((a+b)[1..] == a[1..] + b);
  }
}

lemma filterEmpty<T>(a: seq<T>, f : T -> bool)
requires(forall x : T :: x in a ==> ! f(x))
ensures(filter(a, f) == []) {

}
//A key lemma - if a list contains no duplicates and an element x is in the list, keeping only the elements equal to x gives a singleton list
//for some reason dafny doesn't like this with x, then plugging in x - 1 (maybe because of score of x in anonymous function) - so we use x-1 directly
lemma {: induction a} filter_length_nodups(a: seq<int>, x: int)
requires((x- 1) in a)
requires(noDups_seq(a))
ensures(|filter(a, y => y == (x - 1))| == 1) {
  var i := find_idx(a, (x- 1));
  find_idx_spec(a, (x-1));
  assert(a == a[0..i] + a[i..]);
  filter_app(a[0..i], a[i..], y => y == (x- 1));
  assert(filter(a, y => y == (x- 1)) == filter(a[0..i], y => y == (x - 1)) + filter(a[i..], y => y == (x- 1)));
  assert(!((x-1) in a[0..i]));
  assert(filter(a[0..i], y => y == (x - 1)) == []);
  assert(a[i..] == [a[i]] + a[(i+1)..]);
  filter_app([a[i]], a[(i+1)..], y => y == (x - 1));
  assert(filter(a, y => y == (x - 1)) == filter(a[i..], y => y == (x - 1)));
  assert(filter(a, y => y == (x - 1)) == filter([a[i]], y => y == (x - 1)) + filter(a[i+1..], y => y == (x - 1)));
  assert(!((x - 1) in a[i+1..]));
  filterEmpty(a[i+1..], y => y == (x - 1));
  assert(filter(a[i+1..], y => y == (x - 1)) == []);
}

/* the big one: linking the two implementations of numLt*/
lemma {: induction x} numLt_equiv(x: int, a : seq<int>)
requires(forall x : int :: x in a ==> x >= 0)
requires(noDups_seq(a))
ensures(numLt(x, a) == numLt_alt(x,a)) {
  assert( numLt_alt(x,a) == |filter(a, y => y < x)|);
    if(x < 1) {
      filterEmpty(a, y => y < x);
    }
    else {
      if((x-1) in a) {
        filter_lt_decompose(a, (x));
        //assert((|filter(a, y => y < x)| == |filter(a, y => y < x - 1)| + |filter(a, y => y == x - 1)|));
        filter_length_nodups(a, x);
        //assert(|filter(a, y => y == (x - 1))| == 1);
        //assert(|filter(a, y => y < x)| == |filter(a, y => y < x - 1)| + 1);
        numLt_alt_minus(x, a);
        //assert(numLt_alt(x-1, a) == |filter(a, y => y < x - 1)| );

        //assert(numLt_alt(x, a) == 1 + numLt_alt(x-1, a));
      }
      else {
        filter_lt_decompose(a, (x));
        //assert(forall y :: y in a ==> y != x);
        filterEmpty(a, y => y == (x - 1));
        numLt_alt_minus(x, a);
      }

    }
}

/*why that lemma was so important - we can look at numLt in 2 different ways
  1. inductive definition (1 or 0 + numLt(x-1)) - this is needed for the loop creating the prefix sum
  2. filter definition - this is the meaning of the function (number of elts less than x) and makes it easy to prove bounds - 
     for instance, it is always <= length of list 
    We will also use this definition to prove transitivity and injectivity properties */

function seqSet<T>(a: seq<T>) : set<T> {
    set x : T | x in a
}
/*
function noDups(a: seq<int>) : bool
{
    |a| == |seqSet(a)|
}
*/

/*
lemma noDups_def(a: seq<int>)
ensures(forall i : int, j : int :: 0 <= i < |a| ==> 0 <= j < |a| ==> a[i] == a[j] ==> i == j)
{

}
*/

// Need to prove that numLeq(x,a) < a.Length. This is obvious but difficult to prove in Dafny

//If a predicate holds on all elements in an array, it also holds on all elements in the seq version of the array
lemma inSeqArray<T>(a: array<T>, p : T -> bool)
requires(forall i : int :: 0 <= i < a.Length ==> p(a[i]))
ensures(forall x : T :: x in a[..] ==> p(x)) {

}
/*
lemma noDups_multiset<T>(a: array<T>, i: T)
requires(noDups(a))
ensures(multiset(a[..])[i] == if i in a[..] then 1 else 0) {
    var x := multiset(a[..])[i];
    if(x <= 0) {
    }
    else if (x == 1) { 
    }
    else {
        assert(exists i, j : int :: ((a[..])[i] == x) && ((a[..])[j] == x) && i != j);

    }

}
*/
method countOccurrences (a: array<int>, k: int) returns (b: array<int>)
requires 0 < a.Length
requires 0 < k
requires (noDups(a))
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= a[i] < k)
ensures (b.Length == k + 1)
ensures(forall i : int :: 0 <= i <= k ==> b[i] == (if i in a[..] then 1 else 0))
{
  b := new int[k+1](i => 0);
  var i := 0;
  while(i < a.Length) 
  decreases(a.Length - i)
  invariant (0 <= i <= a.Length)
  invariant(forall j : int :: 0 <= j <= k ==> b[j] == if j in a[0..i] then 1 else 0) {
    b[a[i]] := b[a[i]] + 1;
    i := i + 1;
  }
   // assert (a[0..a.Length] == a[..]);
}
/*
numLtTrans(x: int, y:int, a:seq<int>)
requires(x < y) 
ensures(numLt(x, a) <= num)

lemma numLeqTrans(x: int, y: int, a:seq<int>)
requires(x < y)
ensures (numLeq(x, a) < numLeq(y,a)) {
  if(x in a) {

  }
  else {

  }


}
*/

/*
lemma numLeq_distinct(a: seq<int>, x : int, y : int)
requires(x != y)
ensures(numLeq(x, a) != numLeq(y,a)) {
  if(x <= y) {
    numLeqTrans(x, y, a);
  }
  else {

  }
}
*/

method prefixSum (a:array<int>, b : array<int>) returns (c: array<int>)
requires(0 < b.Length)
requires(noDups(a))
requires(forall i : int :: 0 <= i < b.Length ==> b[i] == (if i in a[..] then 1 else 0))
ensures(c.Length == b.Length)
ensures(forall i : int {:induction i} :: 0 <= i < b.Length ==> (c[i] == numLeq(i, a[..])));
ensures(noDups(c))
{
  var i := 1;
  assert(numLeq(0, a[..]) == b[0]);
  c := new int[b.Length];
  c[0] := b[0];
  while(i < c.Length)
  decreases (b.Length - i)
  invariant (1 <= i <= c.Length)
  invariant(forall j: int {:induction j} :: (0 <= j < i ==> c[j] == numLeq(j, a[..])))
  //invariant(forall j: int :: i <= j < b.Length ==> b[j] == multiset(a[..])[j]) {
  {
    c[i] := b[i] + c[i-1];
    i := i + 1;
  }
}
/*
//a is the original array, b is prefix sum array
method constructSortedArray (a: array<int>, b: array<int>) returns (c : array<int>)
requires(noDups(a))
//requires(a.Length > 0)
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..])));
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)

//TODO: fill in postconditions
{
  var blen := b.Length;
  c := new int[a.Length](i => -1);
  var i := a.Length - 1;
  //establish loop invariants
  /*
  assert(a[0..(i+1)] == a[..]);
  assume(forall j : int :: 0 <= numLeq(j, a[..]) < a.Length); //TODO: prove this
  assert(a[(i+1)..a.Length] == []);
  inSeqArray(c, y => y < 0);
  filterEmpty(c[..], y => y >= 0);
  assert(filter(c[..], y => y >= 0) == []);
  assert(multiset(a[(i + 1)..a.Length]) == multiset(filter(c[..], y => y >= 0)));
  assert(forall j : int :: 0 <= j < a.Length ==> b[a[j]] == numLt(a[j], a[..]) + numEq(a[j], a[0..a.Length]));
  assert(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < blen); //temp
  */
  assert(a[(i+1)..a.Length] == []);
  inSeqArray(c, y => y < 0);
  filterEmpty(c[..], y => y >= 0);
  assert(filter(c[..], y => y >= 0) == []);
  assert(seqSet(a[(i+1)..a.Length]) == seqSet(filter(c[..], y => y >= 0)));
  //assume((forall j: int :: 0 <= i < a.Length ==> 0 <= b[a[j]] < c.Length));\
  assume(forall j: int :: 0 <= j < b.Length ==> 0 <= b[j] < c.Length);
  assert((forall j: int:: 0 <= j <= i ==> c[b[a[j]]] == -1));

  while(i >= 0)
  invariant(-1 <= i < a.Length)
  invariant(forall j: int ::i < j < a.Length ==> 0 <= b[a[j]] < c.Length)
  invariant(forall j: int:: i < j < a.Length ==> c[b[a[j]]] != -1)
  invariant(forall j: int:: 0 <= j <= i ==> c[b[a[j]]] == -1)
  invariant(seqSet(a[(i+1)..a.Length]) == seqSet(filter(c[..], y => y >= 0)))
  {

    assert(0 <= i < a.Length);
    assert(0 <= a[i] < b.Length);
    assume(0 <= b[a[i]] < c.Length);
    assert(seqSet(a[i..a.Length]) == seqSet(a[(i+1)..a.Length]) + {a[i]} );
    assert(a[i] != -1);
    assert(forall j: int:: 0 <= j <= i - 1 ==> c[b[a[j]]] == -1);
    assert(forall j : int :: 0 <= j < i - 1 ==> b[a[j]] != b[a[i]]);
    c[b[a[i]]] := a[i];
    assert(forall j: int:: 0 <= j <= i - 1 ==> c[b[a[j]]] == -1);

    //assert(c[..] == c[0..b[a[i]]] + c[b[a[i]]..]);
    //assert(c[b[a[i]]..] == [c[b[a[i]]]] + c[b[a[i]] + 1..]);
    assert(c[..] == c[0..b[a[i]]] + [c[b[a[i]]]] + c[b[a[i]] + 1..]);
    //assert(seqSet(filter(c[..], y => y >= 0)) == seqSet(filter(c[0..b[a[i]]], y => y >= 0)))
    i := i - 1;
  }
  
/*
  while(i >= 0)
  invariant(-1 <= i < a.Length)
  invariant(b.Length == blen)
  invariant(forall j : int :: 0 <= j < a.Length ==> a[j] < b.Length) //should be obvious already
  //invariant(0 <= (numLt(i, a[..]) + numEq(i, a[0..i + 1])) < c.Length) TODO: actually prove this
  invariant(forall j : int :: 0 <= j < a.Length ==> b[a[j]] == numLt(a[j], a[..]) + numEq(a[j], a[0..(i+1)]))
  //invariant(forall j : int {:induction j} :: 0 <= j < k ==> b[j] == numLt(j, a[..]) + numEq(j, a[0..j + 1]))
  //REAL - invariant(forall j : int :: 0 <= j < c.Length ==> c[j] >= 0 ==> exists k : int :: 0 <= k < a.Length && (numLt(a[k], a[..]) + numEq(a[k], a[0..k]) == j) && c[j] == a[k])
  //invariant(forall j : int :: i < j < a.Length ==>  c[(numLt(a[j], a[..]) + numEq(a[j], a[0.. j+1]))] == a[j])
  invariant(multiset(a[(i + 1)..a.Length]) == multiset(filter(c[..], y => y >= 0))) {
    // assert(b[a[i]] == numLt(a[i], a[..]) + numEq(a[i], a[0..(i+1)]));
    // assume(b[a[i]] <= numLeq (a[i], a[..]));
    // assume(forall j : int :: 0 <= numLeq(j, a[..]) < a.Length);
    // assert(0 <= b[a[i]] < a.Length);

    assert(numEq(a[i], a[0..(i+1)]) == 1 + numEq(a[i], a[0..i]));
    assert(forall j : int :: 0 <= j < a.Length ==> 0 <= a[j] < blen);
    assert(0 <= i < a.Length);
    assert(0 <= a[i] < b.Length);
    assume(0 <= b[a[i]] < c.Length);

    c[b[a[i]]] := a[i];
    b[a[i]] := b[a[i]] - 1;
    i := i - 1;
  }
  */

}

/*
method countOccurrences (a : array<int>, len : int, k : int) returns (b: array<int>)
requires 0 < len && a.Length == len
requires 0 < k
requires (forall i: int :: 0 <= i < len ==> 0<= a[i] < k)
ensures (b.Length == k + 1)
ensures (forall i: int :: 0 <= i < k ==> (b[i] == numLeq(i, a[..])))
{
  //Part 1: Count Occurences of each element, put result in array b
  //fill up b with 0 
  b := new int[k+1](i => 0);
  //populate b with counts of each element
  var i := 0;
  while(i < a.Length) 
  decreases(a.Length - i)
  invariant (0 <= i <= a.Length)
  invariant(forall j : int :: 0 <= j <= k ==> b[j] == multiset(a[0..i])[j]) {
    b[a[i]] := b[a[i]] + 1;
    i := i + 1;
  }
  assert (a[0..a.Length] == a[..]);
  //specification of array b
  assert (b.Length == k + 1);
  assert (forall i : int :: 0 <= i <= k ==> (b[i] == multiset(a[..])[i]));

  //Part 2: Prefix sum, put result in array C
 //note: doesnt work on array of all zeroes, maybe fix - cannot establish loop invar
  i := 1;
  assert(numLeq(0, a[..]) == b[0]);
  while(i < b.Length)
  decreases (b.Length - i)
  invariant (1 <= i <= b.Length)
  invariant(forall j: int {:induction j} :: (0 <= j < i ==> b[j] == numLeq(j, a[..])))
  invariant(forall j: int :: i <= j <= k ==> b[j] == multiset(a[..])[j]) {
    b[i] := b[i] + b[i-1];
    i := i + 1;
  }
  //specification of array b after second loop - b[i] is the number of elements in a <= i
  assert(forall i : int {:induction i} :: 0 <= i <= k ==> (b[i] == numLeq(i, a[..])));
  //assert(forall i : int :: 0 <= i <= k ==> 0 <= b[i] < a.Length);

  // //The third loop is the most complicated. Here we use array c representing the final input
  //TODO: maybe change - in order to reason about the intermediate steps, we need to separate unititialized and filled values. So we fill the 
  //array with -1, representing uninitialized 
  var c := new int[a.Length](i => -1);
  i := a.Length - 1;
  //establish loop invariants
  assert(a[0..(i+1)] == a[..]);
  assume(forall j : int :: 0 <= numLeq(j, a[..]) < a.Length); //TODO: prove this
  assert(a[(i+1)..a.Length] == []);
  inSeqArray(c, y => y < 0);
  filterEmpty(c[..], y => y >= 0);
  assert(filter(c[..], y => y >= 0) == []);
  assert(multiset(a[(i + 1)..a.Length]) == multiset(filter(c[..], y => y >= 0)));
  
  while(i >= 0)
  invariant(-1 <= i < a.Length)
  //invariant(0 <= (numLt(i, a[..]) + numEq(i, a[0..i + 1])) < c.Length) TODO: actually prove this
  invariant(forall j : int :: 0 <= j < a.Length ==> b[a[j]] == numLt(a[j], a[..]) + numEq(a[j], a[0..(i+1)]))
  //invariant(forall j : int {:induction j} :: 0 <= j < k ==> b[j] == numLt(j, a[..]) + numEq(j, a[0..j + 1]))
  invariant(forall j : int :: 0 <= j < c.Length ==> c[j] >= 0 ==> exists k : int :: 0 <= k < a.Length && (numLt(a[k], a[..]) + numEq(a[k], a[0..k]) == j) && c[j] == a[k])
  //invariant(forall j : int :: i < j < a.Length ==>  c[(numLt(a[j], a[..]) + numEq(a[j], a[0.. j+1]))] == a[j])
  invariant(multiset(a[(i + 1)..a.Length]) == multiset(filter(c[..], y => y >= 0))) {
    //numLeq_array(a[i], a);
    //assume(numLeq(a[i], a[..]) < a.Length);
    assert(b[a[i]] == numLt(a[i], a[..]) + numEq(a[i], a[0..(i+1)]));
    assume(b[a[i]] <= numLeq (a[i], a[..]));
    assume(forall j : int :: 0 <= numLeq(j, a[..]) < a.Length);
    assert(0 <= b[a[i]] < a.Length);
    //assert(0 <= a[i] <= k);
    //assume(numLt(a[i], a[..]) + numEq(a[i], a[0..(i+1)]) <= numLeq(a[i], a[..]));
    //assert(0 <= b[a[i]] < a.Length);
    //assert(b[a[i]] == numLt(a[i], a[..]) + numEq(a[i], a[0..(i+1)]));
    assert(numEq(a[i], a[0..(i+1)]) == 1 + numEq(a[i], a[0..i]));
    c[b[a[i]]] := a[i];
    b[a[i]] := b[a[i]] - 1;
    i := i - 1;
  }
  */
//}*/


