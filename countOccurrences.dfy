function numEq(x: int, a : seq<int>) : int
{
  multiset(a)[x]
}

function numLt(x: int, a : seq<int>) : int
decreases x
{
  if x < 1 then 0 else
  multiset(a)[x - 1] + numLt(x-1, a)
}

function numLeq(x: int, a : seq<int>) : int
{
  numEq(x, a) + numLt(x, a)
}

// Need to prove that numLeq(x,a) < a.Length. This is obvious but difficult to prove in Dafny
/*
method numLt_alt(x: int, a : seq<int>) returns (y: int)
ensures(y == numLt(x, a))
ensures(y <= |a|) {
  if(x < 1) {
    return 0;
  }
  else {
    var i := 0;
    while(i < x)
    invariant(0 <= i <= x);
    invariant(forall j: int :: 0 <= j < i ==> y == numLt(i + 1, a));
     {
      y := y + multiset(a)[i];
      i := i + 1;
    }
  }
}*/

function filter<T>(a: seq<T>, f:T -> bool) : seq<T>
decreases a 
{
  if (|a| > 0) then
    if (f(a[0])) then [a[0]] + filter(a[1..], f)
    else filter(a[1..], f)
  else a
}

lemma filterSize<T>(a: seq<T>, f: T -> bool, x:T) 
requires (f(x))
ensures(multiset(a)[x] == multiset(filter(a, f))[x]) {
  if (|a| <= 0) {}
  else {
    assert(a == [a[0]] + a[1..]);
  }
}

lemma filterEmpty<T>(a: seq<T>, f : T -> bool)
requires(forall x : T :: x in a ==> ! f(x))
ensures(filter(a, f) == []) {

}

//If a predicate holds on all elements in an array, it also holds on all elements in the seq version of the array
lemma inSeqArray<T>(a: array<T>, p : T -> bool)
requires(forall i : int :: 0 <= i < a.Length ==> p(a[i]))
ensures(forall x : T :: x in a[..] ==> p(x)) {

}

lemma numEqLeqZero(a:array<int>)
ensures(numEq(0, a[..]) == numLeq(0, a[..])) {

}

// lemma numLt_filter_bound(x:int, y:int, a: seq<int>)
// requires(x <= y)
// ensures (numLt(x, filter(a, z => z < y - 1)) == numLt(x, filter(a, y => y < x)));

// lemma numLt_filter(x : int, a : seq<int>, bound:int)
// requires(bound <= x)
// ensures(numLt(x, a) == numLt(x, filter(a, y => y < x))) {
//   if(x < 1) {
//   }
//   else {
//     assert (x - 1 < x);
//     filterSize(a, y => y < x, x - 1);
//     assert(numLt(x-1, filter(a, y => y < x - 1)) == numLt(x-1, filter(a, y => y < x)));
//     assert(numLt(x-1, a) == numLt(x-1, filter(a, y => y < x - 1)));

//   }
// }

// lemma numLeq_filter(x : int, a : seq<int>)
// ensures(numLt(x, a) == numLeq(x, filter(a, y => y <= x))) {
// }

//lemma numLt

  //   if(f(a[0])) {
  //     if(a[0] == x) {
  //       //assert(filter(a,f) == [a[0]] + filter(a[1..], f));
  //       //assert(multiset(filter(a,f))[x] == 1 + multiset(filter(a[1..], f))[x]);
  //       assert(a == [a[0]] + a[1..]);
  //     }
  //     else {
  //       //assert(filter(a,f) == [a[0]] +  filter(a[1..], f));
  //       //assert(multiset(filter(a,f))[x] == multiset(filter(a[1..], f))[x]);
  //       assert(a == [a[0]] + a[1..]);
  //     }
  //   }
  //   else {
  //     assert(a[0] != x);
  //     assert(a == [a[0]] + a[1..]);

  //   }

  // }

//}

// lemma filterSpec<T>(a: seq<T>, f: T -> bool, x:T)
// requires(!f(x))
// ensures(multiset(a)[x] == multiset(filter(a, f))[x]) {

// }

// lemma numLeq_multiset(x: int, a : array<int>)
// ensures(numLeq(x, a) <= |multiset(a[..])|) {
  
// }

// lemma numLeq_array (x: int, a : array<int>)
// ensures(numLeq(x,a) <= a.Length - 1) {

// }

//for x >= 0, returns the number of elements of a <= x
// function numLeq (x:int, a : array<int>) : int 
// reads a
// {
//   if x < 0 then 0 else
//   multiset(a[..])[x] + numLeq(x-1, a) 
// }



// function remove(x:int, a : array<int>) : array<int> {
//   array.filter(function (y) {
//     return y != x;
//   })
// }

// function remove(x:int, a:seq<int>) : seq<int> 
// requires (forall y : int :: 0 < i < |a| && a[i] != x ==> multiset(a)[a[i]] == multiset)
// {
//   if (|a| > 0) then 
//     if (a[0] == x) then remove (x, a[1..]) else (a[0..0] + remove (x, a[1..]))
//   else a
// }

// assert(forall y : int :: y != x ==> )

// lemma numLeqMax(x: int, a:array<int>)
// requires(forall i : int :: 0 <= i < a.Length ==> a[i] <= x)
// ensures(numLeq(x,a) == a.Length) {

//}

// method max(a:array<int>) returns (m: int)
// ensures(forall i: int :: 0 < i < a.Length ==> a[i] <= m)

// lemma numLeqTrans(x: int, y: int, a:array<int>)
// requires(x <= y)
// ensures (numLeq(x, a) <= numLeq(y,a)) {

// }

// lemma numLeqBound(x: int, a : array<int>)
// ensures(numLeq(x, a) < a.Length) {

// }

method countOccurrences (a: array<int>, k: int) returns (b: array<int>)
requires 0 < a.Length
requires 0 < k
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= a[i] < k)
ensures (b.Length == k + 1)
ensures(forall i : int :: 0 <= i <= k ==> b[i] == numEq(i, a[..]))
{
  b := new int[k+1](i => 0);
  var i := 0;
  while(i < a.Length) 
  decreases(a.Length - i)
  invariant (0 <= i <= a.Length)
  invariant(forall j : int :: 0 <= j <= k ==> b[j] == multiset(a[0..i])[j]) {
    b[a[i]] := b[a[i]] + 1;
    i := i + 1;
  }
    assert (a[0..a.Length] == a[..]);
}

method prefixSum (a:array<int>, b : array<int>) returns (c: array<int>)
requires(0 < b.Length)
requires(forall i : int :: 0 <= i < b.Length ==> b[i] == numEq(i, a[..]))
ensures(c.Length == b.Length)
ensures(forall i : int {:induction i} :: 0 <= i < b.Length ==> (c[i] == numLeq(i, a[..])));
{
  var i := 1;
  assert(numLeq(0, a[..]) == b[0]);
  c := new int[b.Length];
  c[0] := b[0];
  while(i < c.Length)
  decreases (b.Length - i)
  invariant (1 <= i <= c.Length)
  invariant(forall j: int {:induction j} :: (0 <= j < i ==> c[j] == numLeq(j, a[..])))
  invariant(forall j: int :: i <= j < b.Length ==> b[j] == multiset(a[..])[j]) {
    c[i] := b[i] + c[i-1];
    i := i + 1;
  }
}

//a is the original array, b is prefix sum array
method constructSortedArray (a: array<int>, b: array<int>) returns (c : array<int>)
modifies b
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..])));
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)

//TODO: fill in postconditions
{
  var blen := b.Length;
  c := new int[a.Length](i => -1);
  var i := a.Length - 1;
  //establish loop invariants
  assert(a[0..(i+1)] == a[..]);
  assume(forall j : int :: 0 <= numLeq(j, a[..]) < a.Length); //TODO: prove this
  assert(a[(i+1)..a.Length] == []);
  inSeqArray(c, y => y < 0);
  filterEmpty(c[..], y => y >= 0);
  assert(filter(c[..], y => y >= 0) == []);
  assert(multiset(a[(i + 1)..a.Length]) == multiset(filter(c[..], y => y >= 0)));
  assert(forall j : int :: 0 <= j < a.Length ==> b[a[j]] == numLt(a[j], a[..]) + numEq(a[j], a[0..a.Length]));
  assert(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < blen); //temp

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
//}


