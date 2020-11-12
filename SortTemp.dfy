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

method constructSortedArray (a: array<int>, b: array<int>) returns (c : array<int>)
modifies b
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..])));
requires(forall i : int {:induction i} :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)
{
  var i := a.Length - 1;
  assert(a[0..(i+1)] == a[..]);
  //assert(forall j : int :: 0 <= j < a.Length ==> b[a[j]] == numLt(a[j], a[..]) + numEq(a[j], a[0..(i+1)]));
  
  while(i >= 0)
  invariant(-1 <= i < a.Length)
  //invariant(forall j : int :: 0 <= j < a.Length ==> b[a[j]] == numLt(a[j], a[..]) + numEq(a[j], a[0..(i+1)]))
  {
    assert(0 <= i < a.Length);
    assert(0 <= a[i] < b.Length);
    b[a[i]] := b[a[i]] - 1;
    i := i - 1;
  }
  
}

/*
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
  //???? Why the fuck isnt this known already? invariant(forall j : int :: 0 <= j < a.Length ==> 0 <= a[j] < b.Length) //should be obvious already
  //invariant(0 <= (numLt(i, a[..]) + numEq(i, a[0..i + 1])) < c.Length) TODO: actually prove this
  invariant(forall j : int :: 0 <= j < a.Length ==> b[a[j]] == numLt(a[j], a[..]) + numEq(a[j], a[0..(i+1)]))
  //invariant(forall j : int {:induction j} :: 0 <= j < k ==> b[j] == numLt(j, a[..]) + numEq(j, a[0..j + 1]))
  //REAL - invariant(forall j : int :: 0 <= j < c.Length ==> c[j] >= 0 ==> exists k : int :: 0 <= k < a.Length && (numLt(a[k], a[..]) + numEq(a[k], a[0..k]) == j) && c[j] == a[k])
  //invariant(forall j : int :: i < j < a.Length ==>  c[(numLt(a[j], a[..]) + numEq(a[j], a[0.. j+1]))] == a[j])
  //REAL - TODO invariant(multiset(a[(i + 1)..a.Length]) == multiset(filter(c[..], y => y >= 0)))
   {
    // assert(b[a[i]] == numLt(a[i], a[..]) + numEq(a[i], a[0..(i+1)]));
    // assume(b[a[i]] <= numLeq (a[i], a[..]));
    // assume(forall j : int :: 0 <= numLeq(j, a[..]) < a.Length);
    // assert(0 <= b[a[i]] < a.Length);

    assert(numEq(a[i], a[0..(i+1)]) == 1 + numEq(a[i], a[0..i]));
    assert(forall j : int :: 0 <= j < a.Length ==> 0 <= a[j] < b.Length);
    assert(0 <= i < a.Length); //WHAT THE FUCK DAFNY!
    assert(0 <= a[i] < b.Length);
    assume(0 <= b[a[i]] < c.Length);
    assert(forall j : int :: 0 <= j < a.Length ==> b[a[j]] == numLt(a[j], a[..]) + numEq(a[j], a[0..(i+1)]));
    assert(b[a[i]] == numLt(a[i], a[..]) + numEq(a[i], a[0..(i+1)]));
    c[b[a[i]]] := a[i];
    b[a[i]] := b[a[i]] - 1;
    assert(b[a[i]] == numLt(a[i], a[..]) + numEq(a[i], a[0..(i+1)]) - 1);
    assert(b[a[i]] == numLt(a[i], a[..]) + numEq(a[i], a[0..(i)]));

    i := i - 1;
  }

}*/