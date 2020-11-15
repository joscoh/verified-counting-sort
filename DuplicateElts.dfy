/* Allows duplicate elements */

//TODO: factor out common stuff

/* filter - keep all elements of a list that satisfy a predicate, in order */


function filter<T>(a: seq<T>, f:T -> bool) : seq<T>
decreases a 
{
  if (|a| > 0) then
    if (f(a[0])) then [a[0]] + filter(a[1..], f)
    else filter(a[1..], f)
  else a
}

/* Proofs about [filter] */

//Generic facts about filter (for any predicate)

//A key property of filtering - it distributes over append
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

//If we filter a list where no elements satisfy the predicate, we get the empty list
lemma {:induction a} filterEmpty<T>(a: seq<T>, f : T -> bool)
requires(forall x : T :: x in a ==> ! f(x))
ensures(filter(a, f) == []) {
}

//If we filter a list where all elements satisfy the predicate, we get the whole list
lemma {:induction a} filterAll<T>(a: seq<T>, f : T -> bool)
requires(forall x : T :: x in a ==> f(x))
ensures(filter(a, f) == a) {
}

//The length of a filtered list is at most the length of the original list
lemma {:induction a} filter_length_leq<T>(a: seq<T>, f: T -> bool)
ensures(|filter(a, f)| <= |a|) {
}

//If we filter a list and the length is the same, every element in the list satisfies the predicate
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

//Proofs about filtering int lists by lt/leq/eq relations

lemma {:induction a} filter_lt_decompose(a: seq<int>, b : int)
ensures(|filter(a, y => y < b)| == |filter(a, y => y < b - 1)| + |filter(a, y => y == b - 1)|) {
}

lemma {:induction a} filter_leq_decompose(a: seq<int>, x : int)
ensures(|filter(a, y => y <= x)| == |filter(a, y => y < x)| + |filter(a, y => y == x)|) {
}

lemma filter_lt_leq_minus_one(a: seq<int>, x : int)
ensures(filter(a, y => y < x) == filter(a, y => y <= x - 1)) {

}

lemma {:induction a} filter_bounded_in(a:seq<int>, x : int, y : int)
requires(x < y)
requires(y in a)
ensures(|filter(a, z => x < z && z <= y)| > 0){
}

lemma {: induction a} filter_leq_decompose_bounds(a : seq<int>, x : int, y : int)
requires (x <= y)
ensures (|filter(a, z => z <= y)| == |filter(a, z => z <= x)| + |filter(a, z => x < z && z <= y)|) {
}

/* The [numLt] and [numLeq] predicates - specifies the number of elements less than/leq the given element in an array
  used to specify the correct position of the element in a sorted array */

//We provide 2 equivalent definitions (TODO: change) - first, an inductive one

function numLt(x: int, a : seq<int>) : int {
  |filter(a, y => y < x)|
}

function numEq(x: int, a : seq<int>) : int {
  |filter(a, y => y == x)|
}

function numLeq(x: int, a : seq<int>) : int {
  numLt(x, a) + numEq(x, a)
}

//An element's position in the sorted array is as follows
function seqArr<T>(x: int, a : seq<T>) : seq<T> {
  if x < 0 then [] 
    else if x > |a| then []
    else a[..x]
}

lemma seqArr_bounds<T>(x: int, a : seq<T>)
requires(0 <= x < |a|)
ensures(seqArr(x, a) == a[..x]) {}

//in reality, x = a[i] (for anything useful here)
function position(x : int, i : int, a : seq<int>) : int {
    numLt(x, a) + numEq(x, seqArr(i+1, a)) - 1
}

//Dafny cannot infer this automatically and cannot even infer from generic versions
//(parameterized by x) - this is a very annoying limitation
lemma numLt_unfold_zero(a : seq<int>) 
ensures(numLt(0, a) == |filter(a, y => y < 0)|) {}
lemma numEq_minus_one(x: int, a : seq<int>)
ensures(numEq(x-1, a) == |filter(a, y => y == x-1)|) {
}

lemma numLt_minus_one(x: int, a : seq<int>)
ensures(numLt(x-1, a) == |filter(a, y => y < x-1)|) {
}

//TODO see
/*lemma numEq_direct(x: int,  a: seq<int>)
ensures (numEq(x, a) == |filter(a, y => y == x)|) {} */

//Some alternate characterizations that make some things easier
lemma numLeq_direct(x:int, a : seq<int>) 
ensures(numLeq(x, a) == |filter(a, y => y <= x)|) {
}

lemma {: induction x} numLt_ind(x: int, a : seq<int>)
ensures(numLt(x, a) == numEq(x-1, a) + numLt(x-1, a)) {
  numEq_minus_one(x, a);
  numLt_minus_one(x, a);
  filter_lt_decompose(a, x);
}

lemma numLt_leq_minus_one(x: int, a : seq<int>)
ensures(numLt(x, a) == numLeq(x-1, a)) {
  numLt_ind(x, a);
}

lemma numLeq_ind(x: int, a : seq<int>) 
ensures(numLeq(x,a) == numLeq(x-1, a) + numEq(x, a)) {
  numLeq_direct(x, a);
  assert(numLeq(x,a) == |filter(a, y => y <= x)|);
  filter_leq_decompose(a, x);
  numLt_leq_minus_one(x, a);  
}

lemma numEq_app(x: int, a : seq<int>, b : seq<int>)
ensures(numEq(x, a + b) == numEq(x, a) + numEq(x,b)) {
  filter_app(a, b, y => y == x);
}

lemma numEq_singleton(x: int)
ensures(numEq(x, [x]) == 1) {
  filterAll([x], y => y == x);
}

/* Bounds on [numLeq] - needed for bounds checks in counting sort */
lemma {:induction x} numLt_nonneg(x: int, a : seq<int>)
ensures(0 <= numLt(x,a)) {
}

lemma {:induction a} numEq_in_pos(x: int, a : seq<int>)
requires (x in a)
ensures (numEq(x, a) > 0) {
  if(|a| <= 0) {}
  else {
    if(a[0] == x) {
    }
    else {
      assert(x in a[1..]);
    }
  }
}

lemma numLeq_nonneg(x: int, a : seq<int>)
requires (x in a)
ensures(1 <= numLeq(x,a)) {
  numLt_nonneg(x, a);
  numEq_in_pos(x, a);
}

lemma numLeq_upper_bound(x: int, a : seq<int>)
ensures(numLeq(x, a) <= |a|) {
  numLeq_direct(x, a);
  filter_length_leq(a, y => y <= x);
}

/* Transitivity and injectivity of [numLeq] - used in proving that counting sort does not repeat elts and 
  that the result is actually sorted */

lemma numLeq_lt_trans(a:seq<int>, x: int, y: int)
requires(x < y)
requires(y in a)
ensures(numLeq(x, a) < numLeq(y, a)) {
  numLeq_direct(y, a);
  numLeq_direct(x, a);
  filter_leq_decompose_bounds(a, x, y);
  filter_bounded_in(a, x, y);
}

//We need 2 more similar lemmas for the sortedness equivalence proof
lemma numLeq_leq_trans(a:seq<int>, x : int, y : int)
requires(x <= y)
ensures(numLeq(x, a) <= numLeq(y, a)) {
    numLeq_direct(x, a);
    numLeq_direct(y, a);
    filter_leq_decompose_bounds(a, x, y);
}

lemma numLt_leq_bound(a: seq<int>, x : int, y : int) 
requires(x < y)
ensures(numLeq(x, a) - 1 < numLt(y, a)) {
    numLt_leq_minus_one(y, a);
    numLeq_leq_trans(a, x, y-1);
}

//what we really need - injectivity for position function - if a[i] and a[j] have the same position - i = j

lemma position_bounds(a: seq<int>, x: int, i : int)
requires(0 <= i < |a|)
requires(x in a[..i+1])
ensures(numLt(x, a) <= position(x, i, a) <= numLeq(x, a) - 1) {
  numEq_in_pos(x, a[..(i+1)]);
  assert(numLt(x, a) <= position(x, i, a));
  assert(a == a[..(i+1)] + a[(i+1)..]);
  filter_app(a[..(i+1)], a[(i+1)..], y => y == x);
  assert (numEq(x, a[..(i+1)]) <= numEq(x, a));
}
lemma position_inj(a: seq<int>, i : int, j : int)
requires(0 <= i < |a|)
requires(0 <= j < |a|)
requires(position(a[i], i, a) == position(a[j], j, a))
ensures(i == j) {
  //proof by contradiction
  if(i == j) {}
  else {
    if(a[i] == a[j]) { 
      assert(numLt(a[i], a) == numLt(a[j], a));
      //both cases are similar
      if(i < j) {
        assert(a[..(j+1)] == a[..(i+1)] + a[i+1..j+1]);
        numEq_app(a[j], a[..(i+1)], a[i+1..j+1]);
        numEq_in_pos(a[j], a[i+1..j+1]);
      }
      else {
        assert(a[..(i+1)] == a[..(j+1)] + a[j+1..i+1]);
        numEq_app(a[i], a[..(j+1)], a[j+1..i+1]);
        numEq_in_pos(a[i], a[j+1..i+1]);
      }
    }
    else {
      //again, cases are similar
      if(a[i] < a[j]) {
        position_bounds(a, a[i], i);
        position_bounds(a, a[j], j);
        numLt_leq_bound(a, a[i], a[j]);
      }
      else {
        position_bounds(a, a[i], i);
        position_bounds(a, a[j], j);
        numLt_leq_bound(a, a[j], a[i]);
      }
    }    
  }
}

//How position changes when we decrease index
lemma position_decr_index_same(a : seq<int>, i : int)
requires(0 <= i < |a|)
ensures(position(a[i], i - 1, a[..]) == position(a[i], i, a[..]) - 1) {
  assert (a[..(i+1)] == a[..i] + [a[i]]);
  numEq_app(a[i], a[..i], [a[i]]);
  numEq_singleton(a[i]);
  //assert(numEq(a[i], [a[i]]) == 1);
  //assert(numEq(a[i], a[..(i+1)]) == numEq(a[i], a[..i]) + numEq(a[i], [a[i]]));
  //assert(numEq(a[i], a[..i]) == numEq(a[i], a[..i+1]) - 1);
}

lemma position_decr_index_diff(a : seq<int>, i : int, x : int)
requires(0 <= i < |a|)
requires(a[i] != x)
ensures(position(x, i - 1, a[..]) == position(x, i, a[..])) {
  assert (a[..(i+1)] == a[..i] + [a[i]]);
  numEq_app(x, a[..i], [a[i]]);
  filterEmpty([a[i]], y => y == x);
  assert(numEq(x, [a[i]]) == 0);
}

/*
position_inj(a: seq<int>, i : int, j : int)
requires(0 <= i < |a|)
requires(0 <= j < |a|)
requires(position(a[i], i, a) == position(a[j], j, a))


      assert(b[j] == oldB[j] - 1);
      assert(position(j, i-1, a[..]) == position(j, i, a[..]) - 1);
*/
/*
lemma numLt_numLeq_trans_bound(a:seq<int>, x : int, y : int)
requires(y < x)
requires(y in a)
*/

lemma numLeq_inj(a:seq<int>, x : int, y : int)
requires(x != y)
requires(x in a)
requires (y in a)
ensures(numLeq(x, a) != numLeq(y, a)) {
  if(x < y) {
    numLeq_lt_trans(a, x, y);
  }
  else {
    numLeq_lt_trans(a, y, x);
  }
}

predicate permutation<T>(a: seq<T>, b : seq<T>) {
  multiset(a) == multiset(b)
}

//TODO: maybe prove this to remove assumption from sorted theorem, but maybe not
/*
lemma permutation_length<T>(a: seq<T>, b : seq<T>) 
requires(permutation(a, b))
ensures(|a| == |b|) {

}
*/

lemma multiset_app<T>(a: seq<T>, b : seq<T>)
ensures(multiset(a + b) == multiset(a) + multiset(b)) {
}

//If a and b are permutations, then if x is in b, x is in a 
//Proves that (forall x, x in b <==> x in a) since the permutation relation is symmetric
lemma perm_in<T>(a: seq<T>, b : seq<T>) 
requires(permutation(a, b))
ensures(forall x :: x in b ==> x in a) {
  forall x | x in b 
  ensures (x in a) {
    assert(x in multiset(b));
  }
}

lemma {:induction a} numEq_multiset(x: int, a : seq<int>)
ensures(numEq(x,a) == multiset(a)[x]) {
  if(|a| <= 0) {
  }
  else {
    assert(a ==[a[0]] + a[1..]);
  }
}
/*
lemma perm_remove<T>(a:seq<T>, b : seq<T>, i : int, j : int, x : T)
requires(permutation(a,b))
requires(0 <= i < |a|)
requires(0 <= j < |b|)
requires(a[i] == x)
requires(b[j] == x)
ensures(permutation(a[..i] + a[(i+1)..], b[..j] + b[j+1..])) {


}
*/

lemma numEq_perm(a:seq<int>, b : seq<int>, x : int)
requires(permutation(a,b))
ensures(numEq(x, a) == numEq(x, b)) {
    numEq_multiset(x, a);
    numEq_multiset(x, b);
}

//The more general version of this uses filter, but we will do that later (maybe)
lemma perm_preserve_pred<T>(a:seq<T>, b:seq<T>, f: T -> bool)
requires(permutation(a, b))
requires(forall x :: x in a ==> f(x))
ensures(forall x :: x in b ==> f(x)) {
  forall x | x in b {
    perm_in(a, b);
  }
}

//This is really true without the lower bound but it is much easier to prove this way, and it is OK because all elts are positive anyway
lemma {:induction x} numLt_perm(a: seq<int>, b: seq<int>, x : int)
requires (permutation(a, b))
requires(forall x :: x in a ==> x >= 0)
ensures(numLt(x, a) == numLt(x, b)) {
  if(x <= 0) {
    filterEmpty(a, y => y < x);
    perm_preserve_pred(a, b, y => y >= 0);
    filterEmpty(b, y => y < x);
  }
  else {
    numLt_ind(x, a);
    numLt_ind(x, b);
    numLt_perm(a, b, x-1);
    assert(numLt(x, a) == |filter(a, y => y < x)|);
    assert(numLt(x, b) == |filter(b, y => y < x)|);
    numEq_perm(a, b, x-1);
    assert(numEq(x-1, a) == numEq(x-1, b));
    perm_in(a, b);
    perm_in(b,a);
  }
}

//numLeq is also preserved over permutations
lemma numLeq_perm(a: seq<int>, b: seq<int>, x : int)
requires (permutation(a, b))
requires(forall x : int :: x in a ==> x >= 0)
ensures(numLeq(x, a) == numLeq(x, b)) {
  numLt_perm(a, b, x);
  numEq_perm(a, b, x);
  perm_in(a,b);
  perm_in(b,a);
}

/* Relating arrays and sequences */

//If a predicate holds on all elements in an array, it also holds on all elements in the seq version of the array
lemma inSeqArray<T>(a: array<T>, p : T -> bool)
requires(forall i : int :: 0 <= i < a.Length ==> p(a[i]))
ensures(forall x : T :: x in a[..] ==> p(x)) {
}

//The other direction
lemma all_elems_seq_array<T>(a: array<T>, f : T -> bool)
requires(forall x :: (x in a[..]) ==> f(x))
ensures(forall i :: 0 <= i < a.Length ==> f(a[i])) {
}

/* Sortedness - two equivalent definitions */

//A sequence is sorted if the expected condition is satisfied - ie, if i <= j, a[i] <= a[j]
predicate sorted(a: seq<int>) {
  forall i : int, j : int :: 0 <= i < |a| ==> 0 <= j < |a| && i <= j ==> a[i] <= a[j]
}

/*alternate sorting condition - if every element is at one of its possible correct positions in the array, then the array is sorted
  generalization of version in DistinctElts, because an element can be in a range of possible positions*/ //TODO: use position
predicate sorted_alt(a:seq<int>) {
  forall i : int :: 0 <= i < |a| ==> numLt(a[i], a[..]) <= i <= numLeq(a[i], a[..]) - 1
}

//The only direction we need - if a sequence satsifies [sorted_alt(a)], then it satisfies [sorted(a)]
lemma sorted_alt_implies_sorted(a: seq<int>)
requires(sorted_alt(a))
ensures(sorted(a)) {
  forall i : int, j : int | 0 <= i < |a| && 0 <= j < |a| && i <= j
    ensures(a[i] <= a[j]) {
      if(a[j] < a[i]) {
        numLt_leq_bound(a, a[j], a[i]);
      }
      else {
      }
    }
}

//We use a stronger invariant, so we want to show that this implies sorting
lemma all_positions_implies_sorted(a : seq<int>, c : seq<int>)
requires(permutation(a, c))
requires(|a| == |c|)
requires(forall x :: x in a ==> x >= 0)
requires(forall j :: 0 <= j < |c| ==> exists k :: ((-1 < k < |a|) && c[j] == a[k] && j == position(a[k], k, a[..])))
ensures(sorted_alt(c)) {
  forall i : int | 0 <= i < |a|
  ensures(numLt(c[i], c[..]) <= i <= numLeq(c[i], c[..]) - 1) {
    assert(0 <= i < |c|);
    var k :| (-1 < k < |a|) && c[i] == a[k] && i == position(a[k], k, a[..]);
    position_bounds(a, a[k], k);
    numLt_perm(a, c, c[i]);
    numEq_perm(a, c, c[i]);
  }
}

//If the [sorted_alt] condition holds on an array, then it holds on the seq version of the array too
lemma sorted_alt_seq_array(a: array<int>) 
requires(forall i : int :: 0 <= i < a.Length ==> numLt(a[i], a[..]) <= i <= numLeq(a[i], a[..]) - 1)
ensures(sorted_alt(a[..])){
}

/*If the sorted_alt condition holds with respect to array a, then it also holds
  with respect to array b, if a and b are permutations
 */
 //TODO: need to do this
 lemma sorted_alt_perm(a : array<int>, b : array<int>)
requires(forall i : int :: 0 <= i < a.Length ==> a[i] >= 0)
requires(permutation(a[..],b[..]))
//requires(forall i : int :: 0 <= i < |b| ==> numLt(b[i], a[..]) <= i <= numLeq(a[i], a[..]) - 1)
requires(forall j : int :: 0 <= j < b.Length ==> j == numLeq(b[j], a[..]) - 1)
ensures((forall j : int :: 0 <= j < b.Length ==> j == numLeq(b[j], b[..]) - 1))  {
  forall j | 0 <= j < b.Length
  ensures (j == numLeq(b[j], b[..]) - 1) {
    numLeq_perm(a[..], b[..], b[j]);
  }
}

/* Lemmas to prove function invariants */

lemma filter_split_idx<T>(a: array<T>, f: T -> bool, i : int)
requires(0 <= i < a.Length) 
ensures(filter(a[..i+1], f) == filter(a[..i], f) + filter([a[i]], f)) {
  assert(a[..i+1] == a[..i] + [a[i]]);
  filter_app(a[..i], [a[i]], f);
}

lemma numEq_split_idx(a: array<int>, i : int) 
requires(0 <= i < a.Length)
ensures(forall j :: numEq(j, a[..i+1]) == numEq(j, a[..i]) + numEq(j, [a[i]])) {
  forall j  {
    filter_split_idx(a, y => y == j, i);
  }
}

/*The first loop of countingSort - builds an array that counts the occurrences of each element */

lemma countOccurrencesInvariant(a : array<int>, b : seq<int>, newB : seq<int>, i : int, elt: int)
requires(0 <= i < a.Length)
requires(0 <= a[i] < |b|)
requires(|b| == |newB|)
requires(a[i] == elt)
requires(newB == b[elt := b[elt]   + 1])
requires(forall j :: 0 <= j < |b| ==> b[j] == numEq(j, a[..i]))
ensures(forall j :: 0 <= j < |newB| ==> newB[j] == numEq(j, a[..i+1])) {
  forall j | 0 <= j <|newB|
  ensures(newB[j] == numEq(j, a[..i+1])) {
    assert(a[..i+1] == a[..i] + [a[i]]);
    numEq_app(j, a[..i], [a[i]]);
    if(j == elt) {
      numEq_singleton(a[i]);
      assert(newB[j] == b[elt] + 1);  
    }
    else {
      filterEmpty([a[i]], y => y == j); 
    }
  }
}

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
  invariant(forall j : int :: 0 <= j <= k ==> b[j] == numEq(j, a[..i])) {
    //assert(a[..(i+1)] == a[..(i)] + [a[i]]);
    //ghost var t := a[i];
    //filter_app(a[..(i)], [a[i]], y => y == t);
    //numEq_split_idx(a, i);
    //assert(forall t :: numEq(t, a[..(i+1)]) == numEq(t, a[..i]) + numEq(t, [a[i]]));
    //assert(numEq(t, [a[i]]) == 1);
    //assert(0 <= a[i] < k);
    //assert(b[a[i]] == numEq(a[i], a[..i]));
    ghost var oldB := b[..];
    ghost var ai := a[i];
    b[a[i]] := b[a[i]] + 1;

    assert(b[..] == oldB[ai := oldB[ai] + 1]);
    countOccurrencesInvariant(a, oldB, b[..], i, a[i]);

    i := i + 1;
    //assert(b[a[i-1]] == numEq(a[i-1], a[..i]));
    //assert(forall j : int :: 0 <= j < k ==> j != a[i-1] ==> b[j] == oldB[j]);
    assert(forall j : int :: 0 <= j <= k ==> b[j] == numEq(j, a[..i])); //for some reason, need this for it to verify
  }
  assert(a[..i] == a[..]);
}


/*The second loop in countingSort - returns array which gives positions of elements in sorted array*/
method prefixSum (a:array<int>, b : array<int>) returns (c: array<int>)
requires(0 < b.Length)
requires(forall i : int :: 0 <= i < b.Length ==> b[i] == numEq(i, a[..]))
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= a[i])
ensures(c.Length == b.Length)
ensures(forall i : int {:induction i} :: 0 <= i < b.Length ==> (c[i] == numLeq(i, a[..]) - 1));
{
  var i := 1;
  //need to know that there are no elements less than x
  numLt_unfold_zero(a[..]);
  filterEmpty(a[..], y => y < 0);
  assert(numLeq(0, a[..]) == b[0]);
  c := new int[b.Length];
  c[0] := b[0] - 1;
  while(i < c.Length)
  decreases (b.Length - i)
  invariant (1 <= i <= c.Length)
  invariant(forall j: int {:induction j} :: (0 <= j < i ==> c[j] == numLeq(j, a[..]) - 1))
  {
    numLeq_ind(i, a[..]);
    c[i] := b[i] + c[i-1];
    i := i + 1;
  }
}

lemma constructSortedArrayBInvarEntry(a: array<int>, b : array<int>, i : int)
requires (forall j :: 0 <= j < b.Length ==> b[j] == numLeq(j, a[..]) - 1)
requires(i == a.Length - 1)
ensures (forall j :: 0 <= j < b.Length ==> b[j] == numLt(j, a[..]) + numEq(j, a[..(i+1)]) - 1) {
    forall j | 0 <= j < b.Length
    ensures (b[j] == numLt(j, a[..]) + numEq(j, a[..(i+1)]) - 1) {
        assert (a[..(i+1)] == a[..]);
    }
}

//The key lemma: in our loop, c[b1[a]] != -1, so we do not overwrite a previously written value
lemma sortedArrayLoopSeesNewElt (a: array<int>, b: array<int>, c: array<int>, i : int)
requires(a.Length == c.Length)
requires(0 <= i < a.Length)
requires(forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..])))
//requires(forall j, k :: 0 <= j < c.Length ==> 0 <= k < a.Length ==> c[j] == a[k] ==> j == position(a[k], k, a[..])) //every element in its correct position
requires((forall j :: 0 <= j < b.Length ==> b[j] == position(j, i, a[..])))
requires(0 <= a[i] < b.Length)
requires(0 <= b[a[i]] < c.Length)
//(forall j :: 0 <= j < |oldC| ==> oldC[j] != -1 ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(a[k], k, a[..])))
ensures(c[b[a[i]]] == -1) {
  //pf by contradiction
  if(c[b[a[i]]] == -1) {}
  else {
    var k :| (i < k < a.Length) && c[b[a[i]]] == a[k] && b[a[i]] == position(a[k], k, a[..]);
    assert(b[a[i]] == position(a[k], k, a[..]));
    assert(b[a[i]] == position(a[i], i, a[..]));
    position_inj(a[..], i, k);

  }
}
lemma seq_split<T>(a: seq<T>, i : int)
requires (0 <= i < |a|)
ensures(a == a[..i] + [a[i]] + a[i+1..]) {}
/*
lemma seq_split_plus<T>(a: seq<T>, i : int)
requires(0 <= i < |a|)
ensures(a == a[..i+1] + a[i+1..]) {}
*/

lemma seq_split_start<T>(a:seq<T>, i : int)
requires(0 <= i < |a|)
ensures(a[i..] == [a[i]] + a[i+1..]){}

lemma seq_ext_eq<T>(a: seq<T>, b : seq<T>)
requires(|a| == |b|)
requires(forall i :: 0 <= i < |a| ==> a[i] == b[i])
ensures(a == b) {}

lemma update_def<T>(oldA: seq<T>, a : seq<T>, i : int, newVal : T)
requires(0 <= i < |a|)
requires(|a| == |oldA|)
requires(forall j :: 0 <= j < |oldA| ==> j != i ==> oldA[j] == a[j])
requires(a[i] == newVal)
ensures(a == oldA[i := newVal]) {

}

lemma permutation_invariant(a: array<int>, c : seq<int>, oldC : seq<int>, idx : int, i : int)
requires(0 <= i < a.Length)
requires(a.Length == |c|)
requires(|c| == |oldC|)
requires(0 <= idx < a.Length)
requires(c == oldC[idx := a[i]])
requires(oldC[idx] == -1)
requires(0 <= a[i])
requires((permutation((a[(i+1)..]),(filter(oldC, y => y >= 0)))))
ensures(permutation(a[i..], filter(c, y => y >= 0))) {
  //assert(multiset(a[i+1..]) == multiset(filter(oldC, y => y >= 0)));
    seq_split_start(a[..], i);
    //assert(a[i..] == [a[i]] + a[i+1..]);
    multiset_app([a[i]], a[i+1..]);
    //assert(multiset(a[i..]) == multiset{a[i]} + multiset(a[i+1..]));
    seq_split(oldC, idx);
    //assert(oldC == (oldC[..idx] + [oldC[idx]])+ oldC[idx + 1..]);
    filter_app(oldC[..idx] + [oldC[idx]], oldC[idx + 1..], y => y >= 0); //we can split filter into 0..b[a[i]], the elt b[a[i]], and the rest of the list
    filter_app(oldC[..idx], [oldC[idx]], y => y >= 0);
    multiset_app(filter(oldC[..idx] + [oldC[idx]], y => y >= 0), filter(oldC[idx + 1..], y => y >= 0)); //we can split filter into 0..b[a[i]], the elt b[a[i]], and the rest of the list
    multiset_app(filter(oldC[..idx], y => y >= 0), filter([oldC[idx]], y => y >= 0));
    /*assert((filter(oldC, y => y >= 0)) ==
      (filter(oldC[..idx], y => y >= 0)) +
      (filter([oldC[idx]], y => y >= 0)) +
      (filter(oldC[idx+1..], y => y >= 0)));*/
    /*assert(multiset(filter(oldC, y => y >= 0)) ==
      multiset(filter(oldC[..idx], y => y >= 0)) +
      multiset(filter([oldC[idx]], y => y >= 0)) +
      multiset(filter(oldC[idx+1..], y => y >= 0)));*/
    //assert(multiset(filter([oldC[idx]], y => y >= 0)) == multiset{});
    seq_ext_eq(c[..idx], oldC[..idx]);
    seq_ext_eq(c[idx+1..], oldC[idx+1..]);
    seq_split(c[..], idx);
    //assert(c[..] == c[..idx] + [c[idx]] + c[idx+1..]);
    filter_app(oldC[..idx] + [c[idx]], oldC[idx + 1..], y => y >= 0);
    filter_app(oldC[..idx], [c[idx]], y => y >= 0);
    multiset_app(filter(oldC[..idx] + [c[idx]], y => y >= 0), filter(oldC[idx + 1..], y => y >= 0)); //we can split filter into 0..b[a[i]], the elt b[a[i]], and the rest of the list
    multiset_app(filter(oldC[..idx], y => y >= 0), filter([c[idx]], y => y >= 0));
    /*assert(multiset(filter(c[..], y => y >= 0)) ==
      multiset(filter(oldC[..idx], y => y >= 0)) +
      multiset(filter([c[idx]], y => y >= 0)) +
      multiset(filter(oldC[idx+1..], y => y >= 0)));*/
    /*assert(multiset(filter([c[idx]], y => y >= 0)) == multiset{a[i]});
    assert(multiset(filter(c[..], y => y >= 0)) == multiset{a[i]} +
      multiset(filter(oldC, y => y >= 0)));
    assert(multiset(a[i..]) == multiset(filter(c[..], y => y >= 0)));*/
}

lemma filter_length_invariant(a: array<int>, c : seq<int>, oldC : seq<int>, idx : int, i : int)
requires(0 <= i < a.Length)
requires(a.Length == |c|)
requires(|c| == |oldC|)
requires(0 <= idx < a.Length)
requires(c == oldC[idx := a[i]])
requires(oldC[idx] == -1)
requires(0 <= a[i])
requires(|filter(oldC, y => y >= 0)| == a.Length - (i + 1))
ensures(|filter(c[..], y => y >= 0)| == a.Length - i) {
  assert(|filter(oldC, y => y >= 0)| == a.Length - (i + 1)); //assumption
    seq_split(oldC, idx);
    assert(oldC == (oldC[..idx] + [oldC[idx]])+ oldC[idx + 1..]);
    filter_app(oldC[..idx] + [oldC[idx]], oldC[idx + 1..], y => y >= 0); //we can split filter into 0..b[a[i]], the elt b[a[i]], and the rest of the list
    filter_app(oldC[..idx], [oldC[idx]], y => y >= 0);
    filterEmpty([oldC[idx]], y => y >= 0); //since c[idx] = -1
    seq_ext_eq(c[..idx], oldC[..idx]);
    seq_ext_eq(c[idx+1..], oldC[idx+1..]);
    seq_split(c[..], idx);
    assert(c[..] == c[..idx] + [c[idx]] + c[idx+1..]);
    filter_app(oldC[..idx] + [c[idx]], oldC[idx + 1..], y => y >= 0);
    filter_app(oldC[..idx], [c[idx]], y => y >= 0); 
}

lemma b_bound_invariant(a: array<int>, oldB : seq<int>, b : seq<int>, i: int, idx : int)
requires(0 <= i < a.Length)
requires(0 <= a[i] < |oldB|)
requires(|b| == |oldB|)
requires(b[a[i]] == idx - 1)
requires(forall j :: 0 <= j < |b| ==> j != a[i] ==> b[j] == oldB[j]);
requires(idx == oldB[a[i]])
requires(forall j : int :: 0 <= j < |oldB| ==> oldB[j] <= numLeq(j, a[..]) - 1)
ensures((forall j : int :: 0 <= j < |b| ==> b[j] <= numLeq(j, a[..]) - 1)){
}

lemma b_position_invariant(a:array<int>, oldB : seq<int>, b : seq<int>, i : int, idx : int)
requires(0 <= i < a.Length)
requires(0 <= a[i] < |oldB|)
requires(|b| == |oldB|)
requires(b[a[i]] == idx - 1)
requires(forall j :: 0 <= j < |b| ==> j != a[i] ==> b[j] == oldB[j]);
requires(idx == oldB[a[i]])
requires(forall j :: 0 <= j < |oldB| ==> oldB[j] == position(j, i, a[..]));
ensures(forall j :: 0 <= j < |b| ==> b[j] == position(j, i-1, a[..])) {
  forall j | 0 <= j < |b| 
  ensures(b[j] == position(j, i-1, a[..])) {
    if(j == a[i]) {
      assert(b[j] == oldB[j] - 1);
      position_decr_index_same(a[..], i);
      assert(position(j, i-1, a[..]) == position(j, i, a[..]) - 1);
    }
    else {
      position_decr_index_diff(a[..], i, j);
    }
  }
}

lemma c_structure_invariant(a: array<int>, b: seq<int>, c : seq<int>, oldC: seq<int>, idx : int, i : int)
requires(0 <= i < a.Length)
requires(0 <= a[i] < |b|)
requires(a.Length == |c|)
requires(idx == b[a[i]])
requires(idx == position(a[i], i, a[..]))
requires(|c| == |oldC|)
requires(0 <= idx < a.Length)
requires(c == oldC[idx := a[i]])
requires(forall j :: 0 <= j < |oldC| ==> oldC[j] != -1 ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(a[k], k, a[..])))
ensures(forall j :: 0 <= j < |c| ==> c[j] != -1 ==> exists k :: ((i-1 < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..]))) {
  forall j | 0 <= j < |c| && c[j] != -1
  ensures(exists k :: (i-1 < k < a.Length) && c[j] == a[k]) {
    if(j != idx) {
    }
    else {
      assert(-1 < i < a.Length);
      assert(c[j] == a[i]);
      assert(j == position(a[i], i, a[..]));
    }
  }
}
/*
lemma c_position_invariant(a: array<int>, b:seq<int>, c : seq<int>, oldC: seq<int>, idx : int, i : int)
requires(0 <= i < a.Length)
requires(0 <= a[i] < |b|)
requires(a.Length == |c|)
requires(|c| == |oldC|)
requires(idx == b[a[i]])
requires(idx == position(a[i], i, a[..]))
requires(0 <= idx < a.Length)
requires(c == oldC[idx := a[i]])
requires(forall p, k :: 0 <= p < |oldC| ==> 0 <= k < a.Length ==> oldC[p] == a[k] ==> p == position(a[k], k, a[..]))
ensures(forall p, k :: 0 <= p < |c| ==> 0 <= k < a.Length ==> c[p] == a[k] ==> p == position(a[k], k, a[..])) {
  forall p, k | 0 <= p < |c| && 0 <= k < a.Length && c[p] == a[k]
  ensures(p == position(a[k], k, a[..])) {
    if(p == idx) {
      assert(c[p] == a[i]);
      assert(a[k] == a[i]);
      assert(p == position(a[i], i, a[..]));

    }
      assert(p == position())
    }
    else {
    }
  } 
}
*/

//b1[j] == position(j, i, a[..]))

/*
lemma filter_length_invariant(a: array<int>, c : seq<int>, oldC : seq<int>, idx : int, i : int)
requires(0 <= i < a.Length)
requires(a.Length == |c|)
requires(|c| == |oldC|)
requires(0 <= idx < a.Length)
requires(c == oldC[idx := a[i]])
requires(oldC[idx] == -1)
requires(0 <= a[i])
*/
//position_decr_index_diff(a : seq<int>, i : int, x : int)

//Prove that the invariants imply the postconditions in a separate lemma
//TODO: dont actually need the length fact, can prove from permutation
lemma afterLoopPermutation(a: array<int>, c : array<int>)
requires(permutation((a[0..]),(filter(c[..], y => y >= 0)))) //permutation invariant
requires(|filter(c[..], y => y >= 0)| == a.Length)
requires(a.Length == c.Length)
ensures(permutation(a[..], c[..])) {
  filter_same_length_all(c[..], y => y >= 0); //the filtered list is the original list
  filterAll(c[..], y => y >= 0);  
}

lemma afterLoopSorted(a : array<int>, c : array<int>)
requires(forall x :: x in a[..] ==> x >= 0)
requires(|filter(c[..], y => y >= 0)| == a.Length)
requires(permutation(a[..], c[..]))
requires(a.Length == c.Length)
requires(forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> exists k :: ((-1 < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..])))
ensures(sorted(c[..])) {
  filter_same_length_all(c[..], y => y >= 0); //the filtered list is the original list
  filterAll(c[..], y => y >= 0);
  all_elems_seq_array(c, y => y >= 0); //all elements in c satsify y >= 0
  all_elems_seq_array(c, y => y != -1);
  assert(forall j :: 0 <= j  < c.Length ==> c[j] != -1);
  assert(forall j :: 0 <= j < c.Length ==> exists k :: ((-1 < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..])));
  all_positions_implies_sorted(a[..], c[..]);
  assert(sorted_alt(c[..])); 
  sorted_alt_seq_array(c); //c[..] satsifes sorted_alt condition
  sorted_alt_implies_sorted(c[..]); //c[..] is sorted
}




/*The third (and much more complicated) loop of counting sort: put each element in its correct position 
a is the original array, b is prefix sum array */

method constructSortedArray (a: array<int>, b: array<int>) returns (c : array<int>)
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..]) - 1));
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)
ensures(permutation(a[..], c[..]))
ensures(sorted(c[..]))
//ensures(c.Length == a.Length)
{
  //TODO:SEE IF THIS HELPS
  var b1 := new int[b.Length];
  var i := 0;
  while(i < b.Length) 
  invariant(0 <= i <= b.Length)
  invariant(forall j :: 0 <= j < i ==> b1[j] == b[j]) {
    b1[i] := b[i];
    i := i + 1;
  }
  assert(forall i :: 0 <= i < b1.Length ==> b1[i] == b[i]);
  assert(forall i :: 0 <= i < b1.Length ==> b1[i] == numLeq(i, a[..]) - 1);
  assert(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b1.Length);

  c := new int[a.Length](i => -1);
  i := a.Length - 1;
  //establish loop invariants
  assert(a[(i+1)..a.Length] == []);
  inSeqArray(c, y => y < 0);
  filterEmpty(c[..], y => y >= 0);
  //establish the b invariant
  constructSortedArrayBInvarEntry(a, b1, i);
  // (forall x :: numEq(x, a[..(i+1)]) == numEq(x, a[..]));

  //assert(filter(c[..], y => y >= 0) == []);
  //assert(seqSet(a[(i+1)..a.Length]) == seqSet(filter(c[..], y => y >= 0)));
  //prefixSumBounds'(a,b);
  //assert(forall j : int :: 0 <= j < a.Length ==> 0 <= b[a[j]] < a.Length);
  //assert((forall j: int:: 0 <= j <= i ==> c[b[a[j]]] == -1));

  ghost var bLen := b.Length;

  while(i >= 0)
  decreases (i-0)
  invariant(-1 <= i < a.Length)
  invariant(b1.Length == bLen) //need for bounds
  invariant(forall j :: 0 <= j < a.Length ==> 0 <= a[j] < bLen); //also need for bounds
  invariant(forall j : int :: 0 <= j < bLen ==> b1[j] <= numLeq(j, a[..]) - 1) //used for bounds checks
  //invariant(forall j: int ::i < j < a.Length ==> 0 <= b[a[j]] < c.Length) //bounds safety
  //invariant(forall j: int:: i < j < a.Length ==> c[b[a[j]]] >= 0) //what we've done (not true bc of b - see if we need)
  //invariant(forall j : int :: 0 <= j < a.Length ==> 0 <= a[j] < b1.Length ==> 0 <= b1[a[j]] < c.Length ==> c[b1[a[j]]] != -1 ==> i < j) - not true bc of b
  //invariant(0 <= i < a.Length ==> 0 <= a[i] < b.Length ==> 0 <= b1[a[i]] < c.Length ==> c[b1[a[i]]] == -1) //we haven't done the current elt yet - the preconditions always true
  //invariant(forall j: int:: 0 <= j <= i ==> c[b[a[j]]] == -1) //what we haven't done yet
  invariant(|filter(c[..], y => y >= 0)| == a.Length - (i + 1)); //ensures that we fill all of c
  invariant(permutation((a[(i+1)..]),(filter(c[..], y => y >= 0)))) //permutation invariant
  invariant(forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i, a[..])) //the array b at each step (b is changing)
  //invariant(forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> j == position(c[j], j, a[..])) //every element is in its correct position
  invariant(forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..]))) //every filled in element of c is a previously seen elt
  //TODO: invariant(forall j, k :: 0 <= j < c.Length ==> 0 <= k < a.Length ==> c[j] == a[k] ==> j == position(a[k], k, a[..])) //every element in its correct position
  //invariant(forall j : int :: 0 <= j < c.Length ==> c[j] != -1 ==> j == numLeq(c[j], a[..]) - 1) //sorting invariant
  {
    //TODO: make actual invariant
    //assume (forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i, a[..])); //the array b at each step (b is changing)
    //assume(forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> exists k :: (i < k < a.Length) && c[j] == a[k]); //every filled in element of c is a previously seen elt
    //assume (forall j, k :: 0 <= j < c.Length ==> 0 <= k < a.Length ==> c[j] == a[k] ==> j == position(a[k], k, a[..])); //every element in its correct position
    //assume (forall j : int :: 0 <= j < bLen ==> b1[j] <= numLeq(j, a[..]) - 1); //used for bounds checks
    //assume(permutation((a[(i+1)..]),(filter(c[..], y => y >= 0)))); //permutation invariant

    //done
    //assume(|filter(c[..], y => y >= 0)| == a.Length - (i + 1)); //ensures that we fill all of c


  

    //make sure everything is in bounds
    assert(0 <= i < a.Length);
    assert(0 <= a[i] < bLen);
    //first, show that b[a[i]] is nonnegative
    numEq_in_pos(a[i], a[..(i+1)]);
    assert(0 <= b1[a[i]]);
    //then, show that it is bounded
    ghost var ai := a[i];
    filter_length_leq(a[..], y => y <= ai);
    numLeq_direct(ai, a[..]);
    assert(0 <= b1[a[i]] < c.Length);


    ghost var oldC := c[..];
    ghost var oldB := b1[..];
    ghost var idx := b1[a[i]];
    ghost var oldI := i;

    //A crucial step: show that c[b1[a[i]]] == -1, so we are actually considering a new element
    sortedArrayLoopSeesNewElt(a, b1, c, i);
    assert(c[b1[a[i]]] == -1);
    
    //The actual update
    c[b1[a[i]]] := a[i];

    b1[a[i]] := b1[a[i]] - 1;
    assert(c[..] == oldC[idx := a[i]]);
    assert(b1[a[i]] == idx - 1);
    assert(forall j :: 0 <= j < |oldB| ==> j != a[i] ==> b1[j] == oldB[j]);

    
    
    permutation_invariant(a, c[..], oldC, idx, i);
    assert(permutation((a[i..]),(filter(c[..], y => y >= 0)))); //for some reason, need this
    filter_length_invariant(a, c[..], oldC, idx, i);
    //assert();
    assert(forall j : int :: 0 <= j < |oldB| ==> oldB[j] <= numLeq(j, a[..]) - 1);
    b_bound_invariant(a, oldB, b1[..], i, idx);
    b_position_invariant(a, oldB, b1[..], i, idx);
    assert((forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i-1, a[..])));
    //c_exists_elt_invariant(a, c[..], oldC, idx, i);
    //assert(forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> exists k :: (i-1 < k < a.Length) && c[j] == a[k]);
    c_structure_invariant(a, oldB, c[..], oldC, idx, i);
    assert (forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> exists k :: ((i - 1 < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..])));  
    //asserr(forall j :: 0 <= j < |c| ==> c[j] != -1 ==> exists k :: ((i-1 < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..]))) {

    //assert(forall j, k :: 0 <= j < c.Length ==> 0 <= k < a.Length ==> c[j] == a[k] ==> j == position(a[k], k, a[..]));
    
    
    i := i - 1;
    assert(permutation((a[(i+1)..]),(filter(c[..], y => y >= 0))));
    assert((forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i, a[..])));
    assert(forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> exists k :: (i < k < a.Length) && c[j] == a[k]);
    assert (forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..])));  

  }
  afterLoopPermutation(a, c);
  assert(permutation(a[..], c[..]));
  afterLoopSorted(a, c);
  assert(sorted(c[..]));
  /*
  //Now:prove that the invariants imply the properties we want
  //First, permutation:
  assert(a[..] == a[0..a.Length]);
  assert(permutation((a[..]),(filter(c[..], y => y >= 0))));
  //assert(|filter(c[..], y => y >= 0)| == a.Length); //length is correct
  //assert(|a[..]| == a.Length);
  filter_same_length_all(c[..], y => y >= 0); //the filtered list is the original list
  filterAll(c[..], y => y >= 0);
  assert(permutation(a[..], c[..]));
  //assert(filter(c[..], y => y >= 0) == c[..]);
  // sorted invariant - first we prove the alternate condition
  //assert(forall x :: (x in c[..]) ==> x >= 0);
  all_elems_seq_array(c, y => y >= 0); //all elements in c satsify y >= 0
  all_elems_seq_array(c, y => y != -1);
  //assert(forall j : int :: 0 <= j < c.Length ==> c[j] >= 0);
  //assert(forall j : int :: 0 <= j < c.Length ==> c[j] != -1);
  //assert(forall j : int :: 0 <= j < c.Length ==> j == numLeq(c[j], a[..]) - 1);
  assert (forall j :: 0 <= j < c.Length ==> c[j] != -1 ==> exists k :: ((i - 1 < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..])));  
  assert(forall j :: 0 <= j  < c.Length ==> c[j] != -1);
  assert(forall j :: 0 <= j < c.Length ==> exists k :: ((-1 < k < a.Length) && c[j] == a[k] && j == position(a[k], k, a[..])));
  all_positions_implies_sorted(a[..], c[..]);
  assert(sorted_alt(c[..])); 
  //sorted_alt_perm(a, c); //c satisfied sorted_alt condition (sorted_alt(c)
  sorted_alt_seq_array(c); //c[..] satsifes sorted_alt condition
  //noDups_arr_to_seq(a); //a[..] has no duplicates
  //noDups_perm(a[..], c[..]); // c[..] has no duplicates
  sorted_alt_implies_sorted(c[..]); //c[..] is sorted
  assert(sorted(c[..]));
  assert(permutation(a[..], c[..]));
  //assert(sorted(c[..]));
  return c;
  */

}