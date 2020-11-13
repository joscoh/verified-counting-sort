/* Here, we make the simplifying assumption that every element in the list is distinct. 
    The proof is still extremely non-trivial, but it allows us to make 2 key simplifications: dont have to change b in the 3rd loop
     and we can more easily show that the third loop does not consider the same index twice */


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
  |filter(a, y => y <= x)|
}

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

lemma filterAll<T>(a: seq<T>, f : T -> bool)
requires(forall x : T :: x in a ==> f(x))
ensures(filter(a, f) == a) {

}

lemma filter_length_leq<T>(a: seq<T>, f: T -> bool)
ensures(|filter(a, f)| <= |a|) {

}

lemma {:induction a} filter_same_length_all<T>(a:seq<T>, f: T -> bool)
requires(|filter(a, f)| == |a|)
ensures(forall x : T :: x in a ==> f(x)) {
  if (|a| <= 0) {
  }
  else {
    if(f(a[0])) {
    }
    else {
      filter_length_leq(a[1..], f);
    }
  }
}

lemma {: induction a} filter_eq_nodups(a:seq<int>, x : int)
requires(noDups_seq(a))
ensures(|filter(a, y => y == x)| == if (x in a) then 1 else 0) {
}

//for some reason Dafny cannot prove this from above
lemma {: induction a} filter_eq_nodups_minus(a:seq<int>, x : int)
requires(noDups_seq(a))
ensures(|filter(a, y => y == x-1)| == if (x-1 in a) then 1 else 0) {
}

lemma {: induction a} filter_length_nodups(a: seq<int>, x : int)
requires((x-1) in a)
requires(noDups_seq(a))
ensures(|filter(a, y => y == (x - 1))| == 1) {
  filter_eq_nodups_minus(a, x);
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
        filter_length_nodups(a, x);
        numLt_alt_minus(x, a);
      }
      else {
        filter_lt_decompose(a, (x));
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

//First, we define numLeq in terms of filter

//dafny is magical
lemma filter_leq_decompose(a: seq<int>, x : int)
ensures(|filter(a, y => y <= x)| == |filter(a, y => y < x)| + |filter(a, y => y == x)|) {
}

lemma {: induction x} numLeq_equiv(x: int, a : seq<int>)
requires(forall x : int :: x in a ==> x >= 0)
requires(noDups_seq(a))
ensures(numLeq(x, a) == numLeq_alt(x,a)) {
  numLt_equiv(x, a);
  filter_leq_decompose(a, x);
  filter_eq_nodups(a, x);
}

/* Bounds on num_Leq - need for array checks */
lemma {:induction x} numLt_nonneg(x: int, a : seq<int>)
ensures(0 <= numLt(x,a)) {
}

lemma numLeq_nonneg(x: int, a : seq<int>)
requires (x in a)
ensures(1 <= numLeq(x,a)) {
  numLt_nonneg(x, a);
}

lemma numLeq_upper_bound(x: int, a : seq<int>)
requires(forall x : int :: x in a ==> x >= 0)
requires (noDups_seq(a))
ensures(numLeq(x, a) <= |a|) {
  numLeq_equiv(x, a);
  filter_length_leq(a, y => y <= x);
}

//Now, we prove a form of injectivity for numLeq
lemma {: induction a} filter_leq_decompose_bounds(a : seq<int>, x : int, y : int)
requires (x < y)
ensures (|filter(a, z => z <= y)| == |filter(a, z => z <= x)| + |filter(a, z => x < z && z <= y)|) {
}

lemma filter_bounded_in(a:seq<int>, x : int, y : int)
requires(x < y)
requires(y in a)
ensures(|filter(a, z => x < z && z <= y)| > 0){
}

lemma numLeq_lt_trans(a:seq<int>, x: int, y: int)
requires(x < y)
requires(y in a)
requires(forall x : int :: x in a ==> x >= 0)
requires(noDups_seq(a))
ensures(numLeq(x, a) < numLeq(y, a)) {
  numLeq_equiv(x, a);
  numLeq_equiv(y, a);
  filter_leq_decompose_bounds(a, x, y);
  filter_bounded_in(a, x, y);
}

lemma numLeq_inj(a:seq<int>, x : int, y : int)
requires(x != y)
requires(x in a)
requires (y in a)
requires(forall x : int :: x in a ==> x >= 0)
requires(noDups_seq(a))
ensures(numLeq(x, a) != numLeq(y, a)) {
  if(x < y) {
    numLeq_lt_trans(a, x, y);
  }
  else {
    numLeq_lt_trans(a, y, x);
  }
}

function seqSet<T>(a: seq<T>) : set<T> {
    set x : T | x in a
}

lemma seq_set_app<T>(a: seq<T>, b : seq<T>)
ensures(seqSet(a + b) == seqSet(a) + seqSet(b)) {

}

//If a predicate holds on all elements in an array, it also holds on all elements in the seq version of the array - TODO, may have proved this twice
lemma inSeqArray<T>(a: array<T>, p : T -> bool)
requires(forall i : int :: 0 <= i < a.Length ==> p(a[i]))
ensures(forall x : T :: x in a[..] ==> p(x)) {

}

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
}

//general proofs about propositions
lemma all_elems_seq_array<T>(a: array<T>, f : T -> bool)
requires(forall x :: (x in a[..]) ==> f(x))
ensures(forall i :: 0 <= i < a.Length ==> f(a[i])) {
}

method prefixSum (a:array<int>, b : array<int>) returns (c: array<int>)
requires(0 < b.Length)
requires(noDups(a))
requires(forall i : int :: 0 <= i < b.Length ==> b[i] == (if i in a[..] then 1 else 0))
ensures(c.Length == b.Length)
ensures(forall i : int {:induction i} :: 0 <= i < b.Length ==> (c[i] == numLeq(i, a[..]) - 1));
{
  var i := 1;
  assert(numLeq(0, a[..]) == b[0]);
  c := new int[b.Length];
  c[0] := b[0] - 1;
  while(i < c.Length)
  decreases (b.Length - i)
  invariant (1 <= i <= c.Length)
  invariant(forall j: int {:induction j} :: (0 <= j < i ==> c[j] == numLeq(j, a[..]) - 1))
  {
    c[i] := b[i] + c[i-1];
    i := i + 1;
  }
}

lemma prefixSumBounds(a: array<int>, b : array<int>, j : int)
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..]) - 1))
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)
requires(0 <= j < a.Length)
requires(noDups(a))
ensures(0 <= b[a[j]] < a.Length) {
  assert(a[j] in a[..]);
  numLeq_nonneg(a[j], a[..]);
  numLeq_upper_bound(a[j], a[..]);
}

//puts this in a forall statement we can use - NOTE!!! this is how you introduce quanfitied vars in Dafny!
lemma prefixSumBounds'(a: array<int>, b : array<int>)
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..]) - 1))
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)
requires(noDups(a))
ensures(forall j : int {: induction j} :: 0 <= j < a.Length ==> 0 <= b[a[j]] < a.Length) {
  forall j : int | 0 <= j < a.Length {
    prefixSumBounds(a, b, j);
  }
}

//need this in loop to make sure we don't repeat
lemma prefixSumInj(a: array<int>, b : array<int>, i: int)
requires(noDups(a))
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..]) - 1))
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)
requires(0 <= i < a.Length)
ensures(forall j : int :: 0 <= j <= i - 1 ==> b[a[j]] != b[a[i]]) {
  forall j : int | 0 <= j <= i - 1
   ensures (b[a[j]] != b[a[i]]) 
   {
    //NOTE: use noDups in non trivial way here - rely on fact that i != j -> a[i] != a[j]
    numLeq_inj(a[..], a[i], a[j]);
  }
}

//Results about permutations

predicate permutation<T>(a: seq<T>, b : seq<T>) {
  //multiset(a) == multiset(b) - real one
  seqSet(a) == seqSet(b)
}

//todo: move these lemmas about seqSet
lemma {:induction a} seqSet_size_leq<T>(a: seq<T>)
ensures(|seqSet(a)| <= |a|) {
  if(|a| <= 0) {}
  else {
    assert(|a| == 1 + |a[1..]|);
    assert(seqSet(a) == seqSet(a[1..]) + {a[0]});
  }
}

lemma {:induction a} noDups_implies_size<T>(a: seq<T>)
requires(noDups_seq(a))
ensures(|a| == |seqSet(a)|) {
  if(|a| <= 0) {
  }
  else {
    assert(seqSet(a) == seqSet(a[1..]) + {a[0]});
  }
}

lemma {:induction a} size_implies_noDups<T>(a: seq<T>)
requires(|a| == |seqSet(a)|)
ensures(noDups_seq(a)) {
  if (|a| <= 0) {
  }
  else {
    assert(seqSet(a) == seqSet(a[1..]) + {a[0]});
    if(a[0] in a[1..]) {
      seqSet_size_leq(a[1..]);
    }
    else {
    }
  }
}

lemma noDups_perm(a: seq<int>, b: seq<int>)
requires(permutation(a, b))
requires(noDups_seq(a))
requires(|a| == |b|)
ensures(noDups_seq(b)) {
  noDups_implies_size(a);
  size_implies_noDups(b);  
}

lemma perm_sym<T>(a: seq<T>, b : seq<T>)
requires(permutation(a,b))
ensures(permutation(b,a)) {

}

lemma perm_in<T>(a: seq<T>, b : seq<T>) 
requires(permutation(a, b))
ensures(forall x :: x in b ==> x in a) {
  forall x | x in b 
  ensures (x in a) {
    assert(x in seqSet(b));
  }
}
lemma perm_preserves_preds<T>(a: seq<T>, b: seq<T>, f: T -> bool)
requires(permutation(a, b))
requires(forall x :: x in a ==> f(x))
ensures(forall x :: x in b ==> f(x)) {
  perm_in(a, b);
 }

//need to be able to reason about position in c rather than a - ie, numLeq respects permutations
lemma {:induction x} numLt_perm(a: seq<int>, b: seq<int>, x : int)
requires (permutation(a, b))
requires (|a| == |b|)
requires(noDups_seq(a))
requires(forall x : int :: x in a ==> x >= 0)
ensures(numLt(x, a) == numLt(x, b)) {
  perm_in(a, b);
  perm_in(b,a);
}
//didnt actually need all those permutation lemmas


//need to be able to reason about position in c rather than a - ie, numLeq respects permutations
lemma numLeq_perm(a: seq<int>, b: seq<int>, x : int)
requires (permutation(a, b))
requires (|a| == |b|)
requires(noDups_seq(a))
requires(forall x : int :: x in a ==> x >= 0)
ensures(numLeq(x, a) == numLeq(x, b)) {
  numLt_perm(a, b, x);
  perm_in(a,b);
  perm_in(b,a);
}

predicate sorted(a: seq<int>) {
  forall i : int, j : int :: 0 <= i < |a| ==> 0 <= j < |a| && i <= j ==> a[i] <= a[j]
}

/*equivalent sorting condition - if every element is at its correct position in the array, then the array is sorted
  (requires noDups, otherwise there is ambiguity)*/
predicate sorted_alt(a:seq<int>) {
  forall i : int :: 0 <= i < |a| ==> i == numLeq(a[i], a[..]) - 1
}

lemma sorted_alt_implies_sorted(a: seq<int>)
requires(noDups_seq(a))
requires(sorted_alt(a))
requires(forall x : int :: x in a ==> x >= 0)
ensures(sorted(a)) {
  forall i : int, j : int | 0 <= i < |a| && 0 <= j < |a| && i <= j
    ensures(a[i] <= a[j]) {
      if(a[j] < a[i]) {
        numLeq_lt_trans(a, a[j], a[i]);
      }
      else {
      }
    }
}

lemma sorted_alt_seq_array(a: array<int>) 
requires(forall i : int :: 0 <= i < a.Length ==> i == numLeq(a[i], a[..]) - 1)
ensures(sorted_alt(a[..])){
}

//the final (hopefully) condition we need: 
lemma sorted_alt_perm(a : array<int>, b : array<int>)
requires(forall i : int :: 0 <= i < a.Length ==> a[i] >= 0)
requires(permutation(a[..],b[..]))
requires(|a[..]| == |b[..]|)
requires(noDups(a))
requires(forall j : int :: 0 <= j < b.Length ==> j == numLeq(b[j], a[..]) - 1)
ensures((forall j : int :: 0 <= j < b.Length ==> j == numLeq(b[j], b[..]) - 1))  {
  forall j | 0 <= j < b.Length
  ensures (j == numLeq(b[j], b[..]) - 1) {
    numLeq_perm(a[..], b[..], b[j]);
  }
}

//a is the original array, b is prefix sum array
method constructSortedArray (a: array<int>, b: array<int>) returns (c : array<int>)
requires(noDups(a))
//requires(a.Length > 0)
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..]) - 1));
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)
ensures(permutation(a[..], c[..]))
ensures(sorted(c[..]))
ensures(c.Length == a.Length)
{
  var blen := b.Length;
  c := new int[a.Length](i => -1);
  var i := a.Length - 1;
  //establish loop invariants
  assert(a[(i+1)..a.Length] == []);
  inSeqArray(c, y => y < 0);
  filterEmpty(c[..], y => y >= 0);
  assert(filter(c[..], y => y >= 0) == []);
  assert(seqSet(a[(i+1)..a.Length]) == seqSet(filter(c[..], y => y >= 0)));
  prefixSumBounds'(a,b);
  assert(forall j : int :: 0 <= j < a.Length ==> 0 <= b[a[j]] < a.Length);
  assert((forall j: int:: 0 <= j <= i ==> c[b[a[j]]] == -1));

  while(i >= 0)
  decreases (i-0)
  invariant(-1 <= i < a.Length)
  invariant(forall j: int ::i < j < a.Length ==> 0 <= b[a[j]] < c.Length) //bounds safety
  invariant(forall j: int:: i < j < a.Length ==> c[b[a[j]]] >= 0) //what we've done
  invariant(forall j: int:: 0 <= j <= i ==> c[b[a[j]]] == -1) //what we haven't done yet
  invariant(|filter(c[..], y => y >= 0)| == a.Length - (i + 1)); //ensures that we fill all of c
  invariant(permutation((a[(i+1)..a.Length]),(filter(c[..], y => y >= 0)))) //permutation invariant
  invariant(forall j : int :: 0 <= j < c.Length ==> c[j] != -1 ==> j == numLeq(c[j], a[..]) - 1) //sorting invariant
  {

    assert(0 <= i < a.Length);
    assert(0 <= a[i] < b.Length);
    assert(0 <= b[a[i]] < c.Length);
    //permutation invar
    assert(seqSet(a[i..a.Length]) == seqSet(a[(i+1)..a.Length]) + {a[i]} );
    assert(c[..] == (c[0..b[a[i]]] + [c[b[a[i]]]])+ c[b[a[i]] + 1..c.Length]);
    assert(c[b[a[i]]] == -1);
    filter_app(c[0..b[a[i]]] + [c[b[a[i]]]], c[b[a[i]] + 1..c.Length], y => y >= 0);
    filter_app(c[0..b[a[i]]], [c[b[a[i]]]], y => y >= 0);
    assert(filter(c[..], y => y >= 0) == 
      filter(c[0..b[a[i]]], y => y >= 0) + 
      filter([c[b[a[i]]]], y => y >= 0) +
      filter(c[b[a[i]] + 1..c.Length], y => y >= 0));
    filterEmpty([c[b[a[i]]]], y => y >= 0);
    //this says that we can ignore the b[a[i]]th element when considering the previous c
    assert(filter(c[..], y => y >= 0) == 
      filter(c[0..b[a[i]]], y => y >= 0) + 
      filter(c[b[a[i]] + 1..c.Length], y => y >= 0));
    

    assert(a[i] != -1);
    assert(forall j: int:: 0 <= j <= i - 1 ==> c[b[a[j]]] == -1);
    //idea: noDups: i <> j -> a[i] <> a[j], so then by (injectivity), b[a[i]] <> b[a[j]]
    prefixSumInj(a, b, i);

    //The actual update
    c[b[a[i]]] := a[i];

    //also need to know that c[b[a[j]] <> c[b[a[i]]] - filtered part has nodups
    assert(forall j: int:: 0 <= j <= i - 1 ==> b[a[j]] != b[a[i]] ==> c[b[a[j]]] == -1);
    assert(forall j: int:: 0 <= j <= i - 1 ==> b[a[j]] != b[a[i]]);

    //filter invariant
    assert(filter([c[b[a[i]]]], y => y >= 0) == [c[b[a[i]]]]);
    assert(filter([c[b[a[i]]]], y => y >= 0) == [a[i]]);
    assert(c[..] == (c[0..b[a[i]]] + [c[b[a[i]]]])+ c[b[a[i]] + 1..c.Length]);
    filter_app(c[0..b[a[i]]] + [c[b[a[i]]]], c[b[a[i]] + 1..c.Length], y => y >= 0);
    filter_app(c[0..b[a[i]]], [c[b[a[i]]]], y => y >= 0);

    assert(filter(c[..], y => y >= 0) == 
      filter(c[0..b[a[i]]], y => y >= 0) + 
      filter([c[b[a[i]]]], y => y >= 0) +
      filter(c[b[a[i]] + 1..c.Length], y => y >= 0));
    //now the proof goes through!

    //sorting invariant
    assert(b[a[i]] == numLeq(c[b[a[i]]], a[..]) - 1);
    i := i - 1;
  }
  //Now:prove that the invariants imply the properties we want
  //First, permutation:
  assert(a[..] == a[0..a.Length]);
  assert(permutation((a[..]),(filter(c[..], y => y >= 0))));
  assert(|filter(c[..], y => y >= 0)| == a.Length); //length is correct
  assert(|a[..]| == a.Length);
  filter_same_length_all(c[..], y => y >= 0);
  filterAll(c[..], y => y >= 0);
  assert(filter(c[..], y => y >= 0) == c[..]);
  // sorted invariant - first we prove the alternate condition
  assert(forall x :: (x in c[..]) ==> x >= 0);
  all_elems_seq_array(c, y => y >= 0);
  assert(forall j : int :: 0 <= j < c.Length ==> c[j] >= 0);
  assert(forall j : int :: 0 <= j < c.Length ==> c[j] != -1);
  assert(forall j : int :: 0 <= j < c.Length ==> j == numLeq(c[j], a[..]) - 1);
  sorted_alt_perm(a, c); //c satisfied sorted_alt condition
  sorted_alt_seq_array(c); //c[..] satsifes sorted_alt condition
  noDups_arr_to_seq(a); //a[..] has no duplicates
  noDups_perm(a[..], c[..]); // c[..] has no duplicates
  sorted_alt_implies_sorted(c[..]); //c[..] is sorted
  return c;
}


//Our final counting sort method for arrays with no duplicates
method countingSort(a: array<int>, k : int) returns (s: array<int>)
requires(0 < k)
requires(noDups(a))
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= a[i] < k)
ensures(sorted(s[..]))
ensures(permutation(a[..], s[..]))
ensures(s.Length == a.Length)
{
  if(a.Length == 0) {
    s := a;
  }
  else {
    var b := countOccurrences(a, k);
    var c := prefixSum(a, b);
    s := constructSortedArray(a, c);
  }
}