/* A generic version of counting sort - allows elements of any type G along with a key function of type G -> int
    Counting sort will sort by key and ensure stability of the underlying elements.  */

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



//Everything is parametric in the type G and function key. This method of parameterization is taken from 
//https://github.com/dafny-lang/dafny/blob/master/Test/dafny4/GHC-MergeSort.dfy.
type G

function method key(x : G) : int

//Proofs about filtering lists by lt/leq/eq relations

lemma {:induction a} filter_lt_decompose(a: seq<G>, b : int)
ensures(|filter(a, y => key(y) < b)| == |filter(a, y => key(y) < b - 1)| + |filter(a, y => key(y) == b - 1)|) {
}

lemma {:induction a} filter_leq_decompose(a: seq<G>, x : int)
ensures(|filter(a, y => key(y) <= x)| == |filter(a, y => key(y) < x)| + |filter(a, y => key(y) == x)|) {
}

lemma {:induction a} filter_bounded_in(a:seq<G>, x : int, y : int)
requires(x < y)
requires(exists t  :: t in a && key(t) == y)
ensures(|filter(a, z => x < key(z) && key(z) <= y)| > 0){
}

lemma {: induction a} filter_leq_decompose_bounds(a : seq<G>, x : int, y : int)
requires (x <= y)
ensures (|filter(a, z => key(z) <= y)| == |filter(a, z => key(z) <= x)| + |filter(a, z => x < key(z) && key(z) <= y)|) {
}


// The numLt, numEq, and numLeq predicates - specifies the number of elements whose key is less than/leq the given value in an array
// used to specify the correct position of the element in a sorted array 

function numLt(x: int, a : seq<G>) : int {
  |filter(a, y => key(y) < x)|
}

function numEq(x: int, a : seq<G>) : int {
  |filter(a, y => key(y) == x)|
}

function numLeq(x: int, a : seq<G>) : int {
  numLt(x, a) + numEq(x, a)
}

function seqArr<T>(x: int, a : seq<T>) : seq<T> {
  if x < 0 then [] 
    else if x > |a| then []
    else a[..x]
}

//An key's position in the array a[..i+1] is as follows. For this definition to be useful, x = key(a[i]).
//We will show that if every element a[i] occurs in c at position(key(a[i]), i, a), then c is sorted
function position(x : int, i : int, a : seq<G>) : int {
    numLt(x, a) + numEq(x, seqArr(i+1, a)) - 1
}

//Dafny cannot infer this automatically and cannot even infer from generic versions - not sure why
lemma numLt_unfold_zero(a : seq<G>) 
ensures(numLt(0, a) == |filter(a, y => key(y) < 0)|) {}

lemma numEq_minus_one(x: int, a : seq<G>)
ensures(numEq(x-1, a) == |filter(a, y => key(y) == x-1)|) {
}

lemma numLt_minus_one(x: int, a : seq<G>)
ensures(numLt(x-1, a) == |filter(a, y => key(y) < x-1)|) {
}

//Some alternate characterizations that make some things easier
lemma numLeq_direct(x:int, a : seq<G>) 
ensures(numLeq(x, a) == |filter(a, y => key(y) <= x)|) {
}

lemma {: induction x} numLt_ind(x: int, a : seq<G>)
ensures(numLt(x, a) == numEq(x-1, a) + numLt(x-1, a)) {
  numEq_minus_one(x, a);
  numLt_minus_one(x, a);
  filter_lt_decompose(a, x);
}

lemma numLt_leq_minus_one(x: int, a : seq<G>)
ensures(numLt(x, a) == numLeq(x-1, a)) {
  numLt_ind(x, a);
}

lemma numLeq_ind(x: int, a : seq<G>) 
ensures(numLeq(x,a) == numLeq(x-1, a) + numEq(x, a)) {
  numLeq_direct(x, a);
  assert(numLeq(x,a) == |filter(a, y => key(y) <= x)|);
  filter_leq_decompose(a, x);
  numLt_leq_minus_one(x, a);  
}

lemma numEq_app(x: int, a : seq<G>, b : seq<G>)
ensures(numEq(x, a + b) == numEq(x, a) + numEq(x,b)) {
  filter_app(a, b, y => key(y) == x);
}

lemma numEq_singleton(x: G, y : int)
requires(key(x) == y)
ensures(numEq(y, [x]) == 1) {
  filterAll([x], z => key(z) == y);
}

lemma {:induction a} numEq_in_pos(x: G, a : seq<G>)
requires (x in a)
ensures (numEq(key(x), a) > 0) {
  if(|a| <= 0) {}
  else {
    if(a[0] == x) {
    }
    else {
      assert(x in a[1..]);
    }
  }
}

// Transitivity and injectivity of [numLeq] - used in proving that counting sort does not repeat elts and 
// that the result is actually sorted 

//We need 2 more similar lemmas for the sortedness equivalence proof
lemma numLeq_leq_trans(a:seq<G>, x : int, y : int)
requires(x <= y)
ensures(numLeq(x, a) <= numLeq(y, a)) {
    numLeq_direct(x, a);
    numLeq_direct(y, a);
    filter_leq_decompose_bounds(a, x, y);
}

lemma numLt_leq_bound(a: seq<G>, x : int, y : int) 
requires(x < y)
ensures(numLeq(x, a) - 1 < numLt(y, a)) {
    numLt_leq_minus_one(y, a);
    numLeq_leq_trans(a, x, y-1);
}

//the position of an element is among the possible positions of that key in a sorted array
lemma position_bounds(a: seq<G>, x: G, i : int)
requires(0 <= i < |a|)
requires(x in a[..i+1])
ensures(numLt(key(x), a) <= position(key(x), i, a) <= numLeq(key(x), a) - 1) {
  numEq_in_pos(x, a[..(i+1)]);
  assert(numLt(key(x), a) <= position(key(x), i, a));
  assert(a == a[..(i+1)] + a[(i+1)..]);
  numEq_app(key(x), a[..(i+1)], a[(i+1)..]);
  assert (numEq(key(x), a[..(i+1)]) <= numEq(key(x), a));
}

//injectivity for position function - if a[i] and a[j] have the same position - i = j
lemma position_inj(a: seq<G>, i : int, j : int)
requires(0 <= i < |a|)
requires(0 <= j < |a|)
requires(position(key(a[i]), i, a) == position(key(a[j]), j, a))
ensures(i == j) {
  //proof by contradiction
  if(i == j) {}
  else {
    if(key(a[i]) == key(a[j])) { 
      assert(numLt(key(a[i]), a) == numLt(key(a[j]), a));
      //both cases are similar
      if(i < j) {
        assert(a[..(j+1)] == a[..(i+1)] + a[i+1..j+1]);
        numEq_app(key(a[j]), a[..(i+1)], a[i+1..j+1]);
        numEq_in_pos(a[j], a[i+1..j+1]);
      }
      else {
        assert(a[..(i+1)] == a[..(j+1)] + a[j+1..i+1]);
        numEq_app(key(a[i]), a[..(j+1)], a[j+1..i+1]);
        numEq_in_pos(a[i], a[j+1..i+1]);
      }
    }
    else {
      //again, cases are similar
      if(key(a[i]) < key(a[j])) {
        position_bounds(a, a[i], i);
        position_bounds(a, a[j], j);
        numLt_leq_bound(a, key(a[i]), key(a[j]));
      }
      else {
        position_bounds(a, a[i], i);
        position_bounds(a, a[j], j);
        numLt_leq_bound(a, key(a[j]), key(a[i]));
      }
    }    
  }
}

//For equal elements, positions and indices have the same ordering
lemma positions_eq_preserve_order(a : seq<G>, k : int, i : int, x : G)
requires(0 <= i < |a|)
requires(0 <= k < |a|)
requires(position(key(x), k, a[..]) < position(key(x), i, a[..]))
ensures(k < i) {
  if(k < i) {
  }
  else {
    assert(i <= k);
    assert(a[..k+1] == a[..i+1] + a[i+1..k+1]);
    numEq_app(key(x), a[..i+1], a[i+1..k+1]);
  }
}

//How position changes when we decrease index
lemma position_decr_index_same(a : seq<G>, i : int)
requires(0 <= i < |a|)
ensures(position(key(a[i]), i - 1, a[..]) == position(key(a[i]), i, a[..]) - 1) {
  assert (a[..(i+1)] == a[..i] + [a[i]]);
  numEq_app(key(a[i]), a[..i], [a[i]]);
  numEq_singleton(a[i], key(a[i]));
}

lemma position_decr_index_diff(a : seq<G>, i : int, x : int)
requires(0 <= i < |a|)
requires(key(a[i]) != x)
ensures(position(x, i - 1, a[..]) == position(x, i, a[..])) {
  assert (a[..(i+1)] == a[..i] + [a[i]]);
  numEq_app(x, a[..i], [a[i]]);
  filterEmpty([a[i]], y => key(y) == x);
  assert(numEq(x, [a[i]]) == 0);
}

/* Definition of permutations */

predicate permutation<T>(a: seq<T>, b : seq<T>) {
  multiset(a) == multiset(b)
}

//A few facts about multisets 

lemma multiset_app<T>(a: seq<T>, b : seq<T>)
ensures(multiset(a + b) == multiset(a) + multiset(b)) {
}

lemma multiset_elt_app<T>(a: multiset<T>, b : multiset<T>, x : T)
ensures((a + b)[x] == a[x] + b[x]) {
}

lemma multiset_union_inj<T>(a: multiset<T>, b : multiset<T>, s: multiset<T>) 
requires(a + s == b + s)
ensures (a == b) {
  forall x : T
  ensures (a[x] == b[x]) {
    multiset_elt_app(a, s, x);
    multiset_elt_app(b, s, x);
  }
}

//Now, we prove that if a and b are permutations, then they have the same length
lemma permutation_length<T>(a: seq<T>, b : seq<T>) 
requires(permutation(a, b))
ensures(|a| == |b|) {
  if (|a| == 0) {
    assert(multiset(a) == multiset([]));
    assert(multiset(b) == multiset([]));
    assert(|multiset(b)| == 0);
  }
  else {
    assert(a[0] in a);
    perm_in(b, a);
    assert (a[0] in b);
    assert(exists k :: 0 <= k < |b| && b[k] == a[0]);
    var k :| 0 <= k < |b| && b[k] == a[0];
    assert(b == b[..k] + [b[k]] + b[k+1..]);
    assert(a == [a[0]] + a[1..]);
    assert(multiset(b) == multiset(b[..k]) + multiset([b[k]]) + multiset(b[k+1..]));
    assert(multiset(a) == multiset([a[0]]) + multiset(a[1..]));
    var newB := b[..k] + b[k+1..];
    assert(multiset(newB) + multiset([b[k]]) == multiset(b));
    assert(multiset([b[k]]) == multiset([a[0]]));
    multiset_union_inj(multiset(a[1..]), multiset(newB), multiset([a[0]]));
    permutation_length(a[1..], newB);
  }
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

//In order to prove that permutations preserve the numEq, numLeq, and numLt relations, we need to relate
//the original seq to the seq consisting of the keys. Here is a specialized map function to do that.
function mapKey(a: seq<G>) : seq<int> {
    if (|a| <= 0) then [] else [key(a[0])] + mapKey(a[1..]) 
}

lemma mapKey_length(a: seq<G>) 
ensures(|a| == |mapKey(a)|) {
}

lemma mapKey_nil(a: seq<G>)
requires(|a| == 0)
ensures(mapKey(a) == []) {
}

lemma mapKey_app(a: seq<G>, b : seq<G>)
ensures(mapKey(a + b) == mapKey(a) + mapKey(b)) {
    if(|a| <= 0) {
        assert(a == []);
        mapKey_nil(a);
        assert(a + b == b);
    }
    else {
        assert((a+b)[1..] == a[1..] + b);
    }
}

lemma mapKey_in(a: seq<G>, x : G, k : int)
requires(x in a)
requires(0 <= k < |a|)
requires(a[k] == x)
requires(|a| == |mapKey(a)|) //always true but needed for ensures to verify
ensures(mapKey(a)[k] == key(x)) {
    if (|a| <= 0) {
    }
    else {
        if (k == 0) {}
        else {
            mapKey_length(a[1..]);
            mapKey_in(a[1..], x, k-1);
            assert(mapKey(a[1..])[k-1] == mapKey(a[..])[k]);
        }
    }
}

lemma numEq_mapKey(a: seq<G>, x : int)
ensures(numEq(x, a) == |filter(mapKey(a), y => y == x)|) {
}

//An annoying lemma to prove: if a and b are permutations, then so are mapKey(a) and mapKey(b)
lemma perm_mapKey(a: seq<G>, b : seq<G>) 
requires(permutation(a,b))
ensures(permutation(mapKey(a), mapKey(b))) {
    permutation_length(a, b);
    if (|a| <= 0) {}
    else {
        assert(a[0] in a);
        assert(key(a[0]) in mapKey(a));
        perm_in(b, a);
        assert (a[0] in b);
        assert(exists k :: 0 <= k < |b| && b[k] == a[0]);
        var k :| 0 <= k < |b| && b[k] == a[0];
        mapKey_length(b);
        mapKey_in(b, a[0], k);
        assert(b == b[..k] + [b[k]] + b[k+1..]);
        assert(a == [a[0]] + a[1..]);
        var newB := b[..k] + b[k+1..];
        assert(multiset(b) == multiset(b[..k]) + multiset([b[k]]) + multiset(b[k+1..]));
        assert(multiset(a) == multiset([a[0]]) + multiset(a[1..]));
        assert(multiset(newB) + multiset([b[k]]) == multiset(b));
        assert(multiset([b[k]]) == multiset([a[0]]));
        multiset_union_inj(multiset(a[1..]), multiset(newB), multiset([a[0]]));
        assert(multiset(a[1..]) == multiset(newB));
        perm_mapKey(a[1..], newB); //use IH
        assert(multiset(mapKey(a[1..])) == multiset(mapKey(newB)));
        assert(b == b[..k] + b[k..]);
        mapKey_app(b[..k], b[k..]);
        multiset_app(mapKey(b[..k]), mapKey(b[k..]));
        assert(multiset(mapKey(b)) == multiset(mapKey(b[..k])) + multiset(mapKey(b[k..])));
        mapKey_app([a[0]], a[1..]);
        mapKey_app(b[..k], b[k..]);
        assert(b[k..] == [b[k]] + b[k+1..]);
        mapKey_app([b[k]], b[k+1..]);
        mapKey_app(b[..k], b[k+1..]);
        multiset_app(mapKey([a[0]]), mapKey(a[1..]));
        multiset_app(mapKey([b[k]]), mapKey(b[k+1..]));
        multiset_app(mapKey(b[..k]), mapKey(b[k+1..]));
    }
}

lemma filter_eq_multiset(a: seq<int>, x : int) 
ensures(|filter(a, y => y == x)| == multiset(a)[x]) {
    if (|a| <= 0) {
    }
    else {
        assert(a == [a[0]] + a[1..]);
    }
}

lemma perm_preserves_filter_eq(a: seq<int>, b : seq<int>, x : int)
requires(permutation(a, b))
ensures(|filter(a, y => y == x)| == |filter(b, y => y == x)|) {
    filter_eq_multiset(a, x);
    filter_eq_multiset(b, x);
}

//why we needed the perm_mapKey lemma: permutations agree on numEq
lemma numEq_perm(a:seq<G>, b : seq<G>, x : int)
requires(permutation(a,b))
ensures(numEq(x, a) == numEq(x, b)) {
    perm_mapKey(a, b);
    numEq_mapKey(a, x);
    numEq_mapKey(b, x);
    perm_preserves_filter_eq(mapKey(a), mapKey(b), x);
}

lemma perm_preserve_pred(a:seq<G>, b:seq<G>, f: G -> bool)
requires(permutation(a, b))
requires(forall x :: x in a ==> f(x))
ensures(forall x :: x in b ==> f(x)) {
  forall x | x in b {
    perm_in(a, b);
  }
}

//We now want to show that numLt is preserved by permutations. This can be proved directly, which would avoid the assumption that all keys are nonnegative, but it
//is much easier to use induction and numEq_perm, which requires that x is bounded below by 0. This assumption is OK because we need it for counting sort anyway.
lemma {:induction x} numLt_perm(a: seq<G>, b: seq<G>, x : int)
requires (permutation(a, b))
requires(forall x :: x in a ==> key(x) >= 0)
ensures(numLt(x, a) == numLt(x, b)) {
  if(x <= 0) {
    filterEmpty(a, y => key(y) < x);
    perm_preserve_pred(a, b, y => key(y) >= 0);
    filterEmpty(b, y => key(y) < x);
  }
  else {
    numLt_ind(x, a);
    numLt_ind(x, b);
    numLt_perm(a, b, x-1);
    assert(numLt(x, a) == |filter(a, y => key(y) < x)|);
    assert(numLt(x, b) == |filter(b, y => key(y) < x)|);
    numEq_perm(a, b, x-1);
    assert(numEq(x-1, a) == numEq(x-1, b));
    perm_in(a, b);
    perm_in(b,a);
  }
}

// Relating arrays and sequences 

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

// Sortedness - two equivalent definitions 

//We sort sequences by keys
predicate sorted(a: seq<G>) {
  forall i : int, j : int :: 0 <= i < |a| ==> 0 <= j < |a| && i <= j ==> key(a[i]) <= key(a[j])
}

//alternate sorting condition - if every element is at one of its possible correct positions in the array, then the array is sorted
predicate sorted_alt(a:seq<G>) {
  forall i : int :: 0 <= i < |a| ==> numLt(key(a[i]), a[..]) <= i <= numLeq(key(a[i]), a[..]) - 1
}

//The only direction we need - if a sequence satsifies sorted_alt(a), then it satisfies sorted(a)
lemma sorted_alt_implies_sorted(a: seq<G>)
requires(sorted_alt(a))
ensures(sorted(a)) {
  forall i : int, j : int | 0 <= i < |a| && 0 <= j < |a| && i <= j
  ensures(key(a[i]) <= key(a[j])) {
    if(key(a[j]) < key(a[i])) {
      numLt_leq_bound(a, key(a[j]), key(a[i]));
    }
    else {
    }
  }
}

//We use a stronger invariant, so we want to show that this implies sorting_alt (and thus sorted)
lemma all_positions_implies_sorted(a : seq<G>, c : seq<G>)
requires(permutation(a, c))
requires(|a| == |c|)
requires(forall x :: x in a ==> key(x) >= 0)
requires(forall j :: 0 <= j < |c| ==> exists k :: ((-1 < k < |a|) && c[j] == a[k] && j == position(key(a[k]), k, a[..])))
ensures(sorted_alt(c)) {
  forall i : int | 0 <= i < |a|
  ensures(numLt(key(c[i]), c[..]) <= i <= numLeq(key(c[i]), c[..]) - 1) {
    assert(0 <= i < |c|);
    var k :| (-1 < k < |a|) && c[i] == a[k] && i == position(key(a[k]), k, a[..]);
    position_bounds(a, a[k], k);
    numLt_perm(a, c, key(c[i]));
    numEq_perm(a, c, key(c[i]));
  }
}

//If the [sorted_alt] condition holds on an array, then it holds on the seq version of the array too
lemma sorted_alt_seq_array(a: array<G>) 
requires(forall i : int :: 0 <= i < a.Length ==> numLt(key(a[i]), a[..]) <= i <= numLeq(key(a[i]), a[..]) - 1)
ensures(sorted_alt(a[..])){
}

// Stability = we say that a and b are stable with respect to each other if all elements with the same key appear in the same order
//  We can express that as the following:

predicate stable(a : seq<G>, b : seq<G>) {
  forall x : int :: filter(a, y => key(y) == x) == filter(b, y => key(y) == x)
}

//The first loop of countingSort - builds an array that counts the occurrences of each element 

//Prove the invariant is preserved through the loop in a separate lemma, since Dafny has trouble proving it automatically
lemma countOccurrencesInvariant(a : array<G>, b : seq<int>, newB : seq<int>, i : int, elt: int)
requires(0 <= i < a.Length)
requires(0 <= key(a[i]) < |b|)
requires(|b| == |newB|)
requires(key(a[i]) == elt)
requires(newB == b[elt := b[elt]   + 1])
requires(forall j :: 0 <= j < |b| ==> b[j] == numEq(j, a[..i]))
ensures(forall j :: 0 <= j < |newB| ==> newB[j] == numEq(j, a[..i+1])) {
  forall j | 0 <= j <|newB|
  ensures(newB[j] == numEq(j, a[..i+1])) {
    assert(a[..i+1] == a[..i] + [a[i]]);
    numEq_app(j, a[..i], [a[i]]);
    if(j == elt) {
      numEq_singleton(a[i], key(a[i]));
      assert(newB[j] == b[elt] + 1);  
    }
    else {
      filterEmpty([a[i]], y => key(y) == j); 
    }
  }
}

method countOccurrences(a: array<G>, k: int) returns (b: array<int>)
requires 0 < a.Length
requires 0 < k
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= key(a[i]) < k)
ensures (b.Length == k + 1)
ensures(forall i : int :: 0 <= i <= k ==> b[i] == numEq(i, a[..]))
{
  b := new int[k+1](i => 0);
  var i := 0;
  while(i < a.Length) 
  decreases(a.Length - i)
  invariant (0 <= i <= a.Length)
  invariant(forall j : int :: 0 <= j <= k ==> b[j] == numEq(j, a[..i])) {
    ghost var oldB := b[..];
    ghost var ai := key(a[i]);
    b[key(a[i])] := b[key(a[i])] + 1;

    assert(b[..] == oldB[ai := oldB[ai] + 1]);
    countOccurrencesInvariant(a, oldB, b[..], i, key(a[i]));

    i := i + 1;
    assert(forall j : int :: 0 <= j <= k ==> b[j] == numEq(j, a[..i])); //for some reason, need this for it to verify
  }
  assert(a[..i] == a[..]);
}


//The second loop in countingSort - returns array which gives positions of elements in sorted array
method prefixSum(a:array<G>, b : array<int>) returns (c: array<int>)
requires(0 < b.Length)
requires(forall i : int :: 0 <= i < b.Length ==> b[i] == numEq(i, a[..]))
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= key(a[i]))
ensures(c.Length == b.Length)
ensures(forall i : int {:induction i} :: 0 <= i < b.Length ==> (c[i] == numLeq(i, a[..]) - 1));
{
  var i := 1;
  //need to know that there are no elements less than x
  numLt_unfold_zero(a[..]);
  filterEmpty(a[..], y => key(y) < 0);
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

// The third loop - lemmas and invariants 

//The third loop is much more complicated to prove correct. To ensure Dafny does not time out, we do almost all
//of the nontrivial work (invariant preservation, proving postconditions, proving key properties) in the following lemmas.

//The array b is correct to begin
lemma constructSortedArrayBInvarEntry(a: array<G>, b : array<int>, i : int)
requires (forall j :: 0 <= j < b.Length ==> b[j] == numLeq(j, a[..]) - 1)
requires(i == a.Length - 1)
ensures (forall j :: 0 <= j < b.Length ==> b[j] == numLt(j, a[..]) + numEq(j, a[..(i+1)]) - 1) {
    forall j | 0 <= j < b.Length
    ensures (b[j] == numLt(j, a[..]) + numEq(j, a[..(i+1)]) - 1) {
        assert (a[..(i+1)] == a[..]);
    }
}

//A key lemma: in our loop, c[b1[ke requires, ensures, y(a[i])]] == default, so we do not overwrite a previously written value
lemma sortedArrayLoopSeesNewElt(a: array<G>, b: array<int>, c: array<G>, i : int, default : G)
requires(a.Length == c.Length)
requires(0 <= i < a.Length)
requires(forall x :: x in a[..] ==> x != default)
requires(forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..])))
requires((forall j :: 0 <= j < b.Length ==> b[j] == position(j, i, a[..])))
requires(0 <= key(a[i]) < b.Length)
requires(0 <= b[key(a[i])] < c.Length)
ensures(c[b[key(a[i])]] == default) {
  //pf by contradiction
  if(c[b[key(a[i])]] == default) {}
  else {
    var k :| (i < k < a.Length) && c[b[key(a[i])]] == a[k] && b[key(a[i])] == position(key(a[k]), k, a[..]);
    assert(b[key(a[i])] == position(key(a[k]), k, a[..]));
    assert(b[key(a[i])] == position(key(a[i]), i, a[..]));
    position_inj(a[..], i, k);
  }
}

//trivial but fairly useful: splitting lemma by index
lemma seq_split<T>(a: seq<T>, i : int)
requires (0 <= i < |a|)
ensures(a == a[..i] + [a[i]] + a[i+1..]) {}

//TODO: move - wow dafny can do this automatically TODO note
lemma filter_fst_idx<T>(a: seq<T>, f: T -> bool)
requires(0 < |filter(a, f)|)
ensures(exists i : int :: 0 <= i < |a| && f(a[i]) && forall j : int :: 0 <= j < i ==> !f(a[j])) {
}

lemma seq_remove_hd_help<T>(a: seq<T>, b : seq<T>)
requires(a == b)
requires(|a| > 0)
requires(|b| > 0)
ensures(a[0] == b[0] && a[1..] == b[1..]) {

}

lemma seq_remove_hd<T>(a: seq<T>, b: seq<T>, x : T, y : T)
requires([x] + a == [y] + b)
ensures(a == b) {
  seq_remove_hd_help([x] + a, [y] + b);
}

//stability invariant implies permutation
lemma stable_implies_permutation(a: seq<G>, b : seq<G>)
requires(forall x : int :: filter(a, y => key(y) == x) == filter(b, y => key(y) == x))
ensures(permutation(a, b)) {
  if(|a| <= 0) {
    if(|b| <= 0) {
      assert (a == []);
      assert(b == []);
    }
    else {
      var k := key(b[0]);
      assert (filter(a, y => key(y) == k) == filter(b, y => key(y) == k));
    }
  }
  else {
    //idea: we consider a[0], find corresponding elt b[i] (first with same key) based on stability, then we split both arrays and use induction
    assert(a == [a[0]] + a[1..]);
    var k := key(a[0]);
    assert (filter(a, y => key(y) == k) == filter(b, y => key(y) == k));
    assert (0 < |filter(b, y => key(y) == k)|);
    filter_fst_idx(b, y => key(y) == k);
    var i :| (0 <= i < |b| && key(b[i]) == k && forall j :: 0 <= j < i ==> key(b[j]) != k);
    assert (b == (b[..i] + [b[i]]) + b[i+1..]);

    //need to show a[0] == b[i]
    filter_app(b[..i] + [b[i]], b[i+1..], y => key(y) == k);
    filter_app(b[..i], [b[i]], y => key(y) == k);
    filterEmpty(b[..i], y => key(y) == k);
    filter_app([a[0]], a[1..], y => key(y) == k);
    filterAll([a[0]], y => key(y) == k);
    filterAll([b[i]], y => key(y) == k);
    assert(filter(a, y => key(y) == k) == [a[0]] + filter(a[1..], y => key(y) == k));
    assert(filter(b, y => key(y) == k) == [b[i]] + filter(b[i+1..], y => key(y) == k));
    seq_remove_hd_help([a[0]] + filter(a[1..], y => key(y) == k), [b[i]] + filter(b[i+1..], y => key(y) == k));
    assert(a[0] == b[i]);

    
    //establish precondition for induction
    forall x 
    ensures(filter(a[1..], y => key(y) == x) == filter(b[..i] + b[i+1..], y => key(y) == x)) {
      if(x == k) {
        filter_app(b[..i], b[i+1..], y => key(y) == k);
      }
      else {
        filter_app(b[..i] + [b[i]], b[i+1..], y => key(y) == x);
        filter_app(b[..i], [b[i]], y => key(y) == x);
        filter_app(b[..i], b[i+1..], y => key(y) == x);
        filter_app([a[0]], a[1..], y => key(y) == x);
        filterEmpty([a[0]], y => key(y) == x);
        filterEmpty([b[i]], y => key(y) == x);
      }
    }
    stable_implies_permutation(a[1..], b[..i] + b[i+1..]);
    multiset_app([a[0]], a[1..]);
    multiset_app(b[..i] + [b[i]], b[i+1..]);
    multiset_app(b[..i], [b[i]]);
    multiset_app(b[..i], b[i+1..]);
    assert(multiset(a) == multiset(a[1..]) + multiset([a[0]]));
    assert(multiset(b) == multiset(b[..i] + b[i+1..]) + multiset([b[i]]));
    assert(multiset([a[0]]) == multiset([b[i]]));
  }
}

/*
//The permutation invariant: the completed part of c is a permutation of a[(i+1)..]
lemma permutation_invariant(a: array<G>, c : seq<G>, oldC : seq<G>, idx : int, i : int, default : G)
requires(0 <= i < a.Length)
requires(a.Length == |c|)
requires(|c| == |oldC|)
requires(0 <= idx < a.Length)
requires(c == oldC[idx := a[i]])
requires(forall x :: x in a[..] ==> x != default)
requires(oldC[idx] == default)
requires(0 <= key(a[i]))
requires((permutation((a[(i+1)..]),(filter(oldC, y => y != default)))))
ensures(permutation(a[i..], filter(c, y => y != default))) {
    assert(a[i..] == [a[i]] + a[(i+1)..]);
    multiset_app([a[i]], a[i+1..]);
    seq_split(oldC, idx);
    filter_app(oldC[..idx] + [oldC[idx]], oldC[idx + 1..], y => y != default);
    filter_app(oldC[..idx], [oldC[idx]], y => y != default);
    multiset_app(filter(oldC[..idx] + [oldC[idx]], y => y != default), filter(oldC[idx + 1..], y => y != default));
    multiset_app(filter(oldC[..idx], y => y != default), filter([oldC[idx]], y => y != default));
    filterEmpty([oldC[idx]], y => y != default);
    assert(multiset(filter(oldC, y => y != default)) == multiset((filter(oldC[..idx], y => y != default))) +
        multiset((filter(oldC[idx+1..], y => y != default))));
    seq_split(c[..], idx);
    filter_app(oldC[..idx] + [c[idx]], oldC[idx + 1..], y => y != default);
    filter_app(oldC[..idx], [c[idx]], y => y != default);
    assert(c[idx] == a[i]);
    multiset_app(filter(oldC[..idx] + [c[idx]], y => y != default), filter(oldC[idx + 1..], y => y != default));
    multiset_app(filter(oldC[..idx], y => y != default), filter([c[idx]], y => y != default));
    assert(multiset(a[i..]) == multiset([a[i]]) + multiset(a[i+1..]));
    assert(c[idx] == a[i]);
    assert(a[i] in a[..]);
    assert(c[idx] != default);
    filterAll([c[idx]], y => y != default);
}
*/

//The invariant that the length of the completed part of c is |a| - (i+1) (actually follows from permutation invariant but it is faster if we use both and keep them separate)
lemma filter_length_invariant(a: array<G>, c : seq<G>, oldC : seq<G>, idx : int, i : int, default : G)
requires(0 <= i < a.Length)
requires(a.Length == |c|)
requires(|c| == |oldC|)
requires(0 <= idx < a.Length)
requires(c == oldC[idx := a[i]])
requires(oldC[idx] == default)
requires(0 <= key(a[i]))
requires (forall x :: x in a[..] ==> x != default)
requires(|filter(oldC, y => y != default)| == a.Length - (i + 1))
ensures(|filter(c[..], y => y != default)| == a.Length - i) {
  assert(|filter(oldC, y => y != default)| == a.Length - (i + 1));
    seq_split(oldC, idx);
    assert(oldC == (oldC[..idx] + [oldC[idx]])+ oldC[idx + 1..]);
    filter_app(oldC[..idx] + [oldC[idx]], oldC[idx + 1..], y => y != default);
    filter_app(oldC[..idx], [oldC[idx]], y => y != default);
    filterEmpty([oldC[idx]], y => y != default); //since c[idx] == default
    seq_split(c[..], idx);
    assert(c[..] == c[..idx] + [c[idx]] + c[idx+1..]);
    filter_app(oldC[..idx] + [c[idx]], oldC[idx + 1..], y => y != default);
    filter_app(oldC[..idx], [c[idx]], y => y != default);
    assert(c[idx] == a[i]);
    assert(a[i] in a[..]);
    assert(c[idx] != default);
}

//The values in the b array are bounded (used for array bounds)
lemma b_bound_invariant(a: array<G>, oldB : seq<int>, b : seq<int>, i: int, idx : int)
requires(0 <= i < a.Length)
requires(0 <= key(a[i]) < |oldB|)
requires(|b| == |oldB|)
requires(b[key(a[i])] == idx - 1)
requires(forall j :: 0 <= j < |b| ==> j != key(a[i]) ==> b[j] == oldB[j]);
requires(idx == oldB[key(a[i])])
requires(forall j : int :: 0 <= j < |oldB| ==> oldB[j] <= numLeq(j, a[..]) - 1)
ensures((forall j : int :: 0 <= j < |b| ==> b[j] <= numLeq(j, a[..]) - 1)){
}

//Invariant that the array b consists of the positions of all elements, only considering equal elements up to index i
lemma b_position_invariant(a:array<G>, oldB : seq<int>, b : seq<int>, i : int, idx : int)
requires(0 <= i < a.Length)
requires(0 <= key(a[i]) < |oldB|)
requires(|b| == |oldB|)
requires(b[key(a[i])] == idx - 1)
requires(forall j :: 0 <= j < |b| ==> j != key(a[i]) ==> b[j] == oldB[j]);
requires(idx == oldB[key(a[i])])
requires(forall j :: 0 <= j < |oldB| ==> oldB[j] == position(j, i, a[..]));
ensures(forall j :: 0 <= j < |b| ==> b[j] == position(j, i-1, a[..])) {
  forall j | 0 <= j < |b| 
  ensures(b[j] == position(j, i-1, a[..])) {
    if(j == key(a[i])) {
      assert(b[j] == oldB[j] - 1);
      position_decr_index_same(a[..], i);
      assert(position(j, i-1, a[..]) == position(j, i, a[..]) - 1);
    }
    else {
      position_decr_index_diff(a[..], i, j);
    }
  }
}

//The important invariant for sorting and stability: each element c[j] corresponds to the element of k actually at position j in a sorted and stable array
lemma c_structure_invariant(a: array<G>, b: seq<int>, c : seq<G>, oldC: seq<G>, idx : int, i : int, default : G)
requires(0 <= i < a.Length)
requires(0 <= key(a[i]) < |b|)
requires(a.Length == |c|)
requires(idx == b[key(a[i])])
requires(idx == position(key(a[i]), i, a[..]))
requires(|c| == |oldC|)
requires(0 <= idx < a.Length)
requires(c == oldC[idx := a[i]])
requires(forall x :: x in a[..] ==> x != default)
requires(forall j :: 0 <= j < |oldC| ==> oldC[j] != default ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..])))
ensures(forall j :: 0 <= j < |c| ==> c[j] != default ==> exists k :: ((i-1 < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..]))) {
  forall j | 0 <= j < |c| && c[j] != default
  ensures(exists k :: (i-1 < k < a.Length) && c[j] == a[k]) {
    if(j != idx) {
    }
    else {
      assert(-1 < i < a.Length);
      assert(c[j] == a[i]);
      assert(j == position(key(a[i]), i, a[..]));
    }
  }
}

//Proofs that the invariants imply the postconditions in a the following lemmas

//Our loop invariants imply the output is a permutation of the input
/*
lemma afterLoopPermutation(a: array<G>, c : array<G>, default : G)
requires(permutation((a[0..]),(filter(c[..], y => y != default))))
requires(a.Length == c.Length)
ensures(permutation(a[..], c[..])) {
  permutation_length(a[..], (filter(c[..], y => y != default)));
  filter_same_length_all(c[..], y => y != default); //the filtered list is the original list
  filterAll(c[..], y => y != default);  
}
*/

//Our loops invariants imply the output is sorted
lemma afterLoopSorted(a : array<G>, c : array<G>, default : G)
requires(forall x :: x in a[..] ==> key(x) >= 0)
requires(|filter(c[..], y => y != default)| == a.Length)
requires(permutation(a[..], c[..]))
requires(a.Length == c.Length)
requires(forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((-1 < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..])))
ensures(sorted(c[..])) {
  filter_same_length_all(c[..], y => y != default); //the filtered list is the original list
  filterAll(c[..], y => y != default);
  all_elems_seq_array(c, y => y != default); 
  assert(forall j :: 0 <= j  < c.Length ==> c[j] != default);
  assert(forall j :: 0 <= j < c.Length ==> exists k :: ((-1 < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..])));
  all_positions_implies_sorted(a[..], c[..]);
  assert(sorted_alt(c[..])); 
  sorted_alt_seq_array(c); //c[..] satsifes sorted_alt condition
  sorted_alt_implies_sorted(c[..]); //c[..] is sorted
}

lemma no_default_elts(a: array<G>, default : G)
requires(forall j :: 0 <= j < a.Length ==> 0 <= key(a[j])); 
requires(key(default) < 0)
ensures(forall x :: x in a[..] ==> x != default) {
}

// Proofs for stability 

//First, we need to know that at any point in the loop, for all j < b[key(a[i])], c[j] != a[i] - ie, the current element is the
//first one in the current array with that value - because we loop backwards, this ensures stability
lemma all_same_elts_come_after(a: array<G>, oldC : seq<G>, i : int, ai : G, bai : int, default : G)
requires(0 <= i < a.Length)
requires(ai == a[i])
requires(0 <= key(ai))
requires(key(default) < 0)
requires(bai == position(key(ai), i, a[..]))
requires(0 <= bai < |oldC|)
requires(a.Length == |oldC|)
requires(forall j :: 0 <= j < |oldC| ==> oldC[j] != default ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..])))
ensures(forall j :: 0 <= j < bai ==> key(oldC[j]) != key(a[i])) {
  forall j | 0 <= j < bai
  ensures(key(oldC[j]) != key(a[i])) {
    if(key(oldC[j]) == key(a[i])) {
      var k :| ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..]));
      assert(position(key(a[i]), k, a[..]) < position(key(a[i]), i, a[..]));
      positions_eq_preserve_order((a[..]), k, i, a[i]);
    }
    else {}
  }
}

//True for arbitrary functions but Dafny has trouble using a more generic definition
lemma filter_filter_special(a: seq<G>, default : G, x: int)
ensures(filter((filter(a, y => y != default)), y => key(y) == x) == filter(a, y => y != default && key(y) == x)) {
}

//The stability invariant - that the completed portion of c and a[i+1..] are stable with respect to each other. This proof is long and tedious.
lemma stable_invariant_preserved(a: array<G>, b : seq<int>, oldC : seq<G>, c : seq<G>, i : int, ai: G, bai : int, default: G)
requires(0 <= i < a.Length)
requires(ai == a[i])
requires(0 <= key(ai) < |b|)
requires(bai == b[key(a[i])])
requires(bai == position(key(ai), i, a[..]))
requires(0 <= bai < |c|)
requires(a.Length == |c|)
requires(|c| == |oldC|)
requires(oldC[bai] == default)
requires(c == oldC[bai := ai])
requires(a[i] != default)
requires(key(default) < 0)
requires(forall j :: 0 <= j < |oldC| ==> oldC[j] != default ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..])))
requires(forall x : int :: filter(a[i+1..], y => key(y) == x) == filter(filter(oldC, y => y != default), y => key(y) == x))
ensures(forall x : int :: filter(a[i..], y => key(y) == x) == filter(filter(c, y => y != default), y => key(y) == x)) {
  forall x 
  ensures (filter(a[i..], y => key(y) == x) == filter(filter(c, y => y != default), y => key(y) == x)) {
    assert(filter(a[i+1..], y => key(y) == x) == filter(filter(oldC, y => y != default), y => key(y) == x));
    filter_filter_special(c, default, x);
    filter_filter_special(oldC, default, x);
    assert(a[i..] == [a[i]] + a[i+1..]);
    filter_app([a[i]], a[i+1..], y => key(y) == x);
    filter_app(c[..b[key(a[i])]], c[b[key(a[i])]..], y => (y != default && key(y) == x));
    assert(c == c[..b[key(a[i])]] + c[b[key(a[i])]..]);
    assert(c[b[key(a[i])]..] == [c[b[key(a[i])]]] + c[b[key(a[i])] + 1..]);
    filter_app([c[b[key(a[i])]]], c[b[key(a[i])] + 1..], y => (y != default && key(y) == x));
    filter_app(oldC[..b[key(a[i])]], oldC[b[key(a[i])]..], y => (y != default && key(y) == x));
    assert(oldC == oldC[..b[key(a[i])]] + oldC[b[key(a[i])]..]);
    assert(oldC[b[key(a[i])]..] == [oldC[b[key(a[i])]]] + oldC[b[key(a[i])] + 1..]);
    filter_app([oldC[b[key(a[i])]]], oldC[b[key(a[i])] + 1..], y => (y != default && key(y) == x));
    assert(c[bai] == a[i]);
    assert(a[i] in a[..]);
    assert(c[bai] != default);

    //so now we know that (with abuse of notation):
    // filter(a[i..]) = filter(a[i]) + filter(a[i+1..])
    // filter(c) = filter(c[..b[a[i]]]) + filter(c[b[a[i]]]) + filter(c[b[a[i]] + 1..])
    // filter(c) = filter(oldC[..b[a[i]]]) + filter(oldC[b[a[i]]]) + filter(oldC[b[a[i]] + 1..])
    
    if(x == key(a[i])) {
      //idea: filter(c[..b[a[i]]]) = [] and same for oldC by [all_same_elts_come_after] - the rest is easy
      all_same_elts_come_after(a, oldC, i, a[i], b[key(a[i])], default);
      assert(forall j :: 0 <= j < b[key(a[i])] ==> key(c[j]) != x);
      
      filterEmpty(c[..b[key(a[i])]], y => (y != default && key(y) == x));
      filterEmpty(oldC[..b[key(a[i])]], y => (y != default && key(y) == x));
      assert(filter([c[b[key(a[i])]]], y => (y != default && key(y) == x)) == [a[i]]);
      filterEmpty([oldC[b[key(a[i])]]], y => (y != default && key(y) == x));

      assert(filter(filter(c, y => y != default), y => key(y) == x) == filter(c, y => (y != default && key(y) == x)));
      assert(filter(c[..b[key(a[i])]], y => (y != default && key(y) == x)) == []);
      assert(c == c[..b[key(a[i])]] + [c[b[key(a[i])]]] + c[b[key(a[i])] + 1..]);

      assert(filter(filter(c, y => y != default), y => key(y) == x) == [a[i]] + filter(c[b[key(a[i])] + 1..], y => (y != default && key(y) == x)));

      assert(filter(filter(oldC, y => y != default), y => key(y) == x) == filter(oldC[b[key(a[i])] + 1..], y => (y != default && key(y) == x))); 
      assert((filter(a[i..], y => key(y) == x) == filter(filter(c, y => y != default), y => key(y) == x))); 
    }
    else {
      filterEmpty([c[b[key(a[i])]]], y => (y != default && key(y) == x));
    }
  }
}


//Our stability invariant implies that a and c are stable after the loop is finished
lemma afterLoopStable(a : array<G>, c : array<G>, default : G)
requires(a.Length == c.Length)
requires(forall x : int :: filter(a[..], y => key(y) == x) == filter(filter(c[..], y => y != default), y => key(y) == x))
requires(|filter(c[..], y => y != default)| == a.Length)
ensures(stable(a[..], c[..])) {
    filter_same_length_all(c[..], y => y != default);
    filterAll(c[..], y => y != default);
    assert((filter(c[..], y => y != default) == c[..]));
}

//Finally, the code for the loop itself. We put each element in its correct position. The invariants are much more complicated here.
//a is the original array, b is prefix sum array 
method constructSortedArray(a: array<G>, b: array<int>, default : G) returns (c : array<G>)
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..]) - 1));
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= key(a[i]) < b.Length)
requires(key(default) < 0)

ensures(permutation(a[..], c[..]))
ensures(sorted(c[..]))
ensures(stable(a[..], c[..]))
{
  //we copy b into a new array becaues Dafny really doesnt like it when you modify inputs in the function; it has
  //difficulty proving lots of things
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
  assert(forall i : int :: 0 <= i < a.Length ==> 0 <= key(a[i]) < b1.Length);

  c := new G[a.Length](i => default);
  i := a.Length - 1;
  //establish loop invariants
  assert(a[(i+1)..a.Length] == []);
  inSeqArray(c, y => y == default);
  filterEmpty(c[..], y => y != default);
  
  //establish the b invariant
  constructSortedArrayBInvarEntry(a, b1, i);

  while(i >= 0)
  decreases (i-0)
  invariant(-1 <= i < a.Length)
  invariant(forall j :: 0 <= j < a.Length ==> 0 <= key(a[j]) < b1.Length); //also need for bounds
  invariant(forall j : int :: 0 <= j < b1.Length ==> b1[j] <= numLeq(j, a[..]) - 1) //used for bounds checks
  //invariant(permutation((a[(i+1)..]),(filter(c[..], y => y != default)))) //permutation invariant
  //technically, this invariant is implied by the next one (by permutation_length), but the proofs are much faster if we include both
  invariant(|filter(c[..], y => y != default)| == a.Length - (i + 1)); //ensures that we fill all of c
  invariant(forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i, a[..])) //the array b at each step (b is changing)
  invariant(forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..]))) //every filled in element of c is a previously seen elt
  invariant(forall x : int :: filter(a[(i+1)..], y => key(y) == x) == filter(filter(c[..], y => y != default), y => key(y) == x)) //stability invariant
  
  {
    //make sure everything is in bounds
    assert(0 <= i < a.Length);
    var ai := key(a[i]);
    assert(0 <= ai < b1.Length);
    //first, show that b[key(a[i])] is nonnegative
    numEq_in_pos(a[i], a[..(i+1)]);
    assert(0 <= b1[ai]);
    //then, show that it is bounded
    filter_length_leq(a[..], y => key(y) <= ai);
    numLeq_direct(ai, a[..]);
    assert(0 <= b1[ai] < c.Length);
  
    //ghost variables to refer to the old values of variables
    ghost var oldC := c[..];
    ghost var oldB := b1[..];
    ghost var cLen := c.Length;
    var idx := b1[ai];

    no_default_elts(a, default);  
    //A crucial step: show that c[b1[key(a[i])]] == default, so we are actually considering a new element
    sortedArrayLoopSeesNewElt(a, b1, c, i, default);
    assert(c[idx] == default);
  
   
    //The actual update
    c[idx] := a[i];
    b1[ai] := idx - 1;


    //What we changed
    assert(c[..] == oldC[idx := a[i]]);
    assert(b1[ai] == idx - 1);
    assert(forall j :: 0 <= j < |oldB| ==> j != ai ==> b1[j] == oldB[j]); // takes a long time

    //re-establish invariants with auxilliary lemmas
    //permutation_invariant(a, c[..], oldC, idx, i, default);
    //assert(permutation((a[i..]),(filter(c[..], y => y != default)))); 
    filter_length_invariant(a, c[..], oldC, idx, i, default);
    assert(forall j : int :: 0 <= j < |oldB| ==> oldB[j] <= numLeq(j, a[..]) - 1);
    b_position_invariant(a, oldB, b1[..], i, idx);
    assert((forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i-1, a[..])));
    b_bound_invariant(a, oldB, b1[..], i, idx);
    assert(|oldC| == cLen);
    assert(forall j :: 0 <= j < |oldC| ==> oldC[j] != default ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..])));
    c_structure_invariant(a, oldB, c[..], oldC, idx, i, default);   
    assert (forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((i - 1 < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..]))); 
    assert(key(default) < 0);
    stable_invariant_preserved(a, oldB, oldC, c[..], i, a[i], idx, default); 
    
    //update loop counter
    i := i - 1;
  }
  
  //invariants => postcondition
  //afterLoopPermutation(a, c, default);
  //assert(permutation(a[..], c[..]));
  
  //requires(|filter(c[..], y => y != default)| == a.Length)
  
  
  afterLoopStable(a, c, default);
  assert(stable(a[..], c[..])); 
  stable_implies_permutation(a[..], c[..]);
  assert(permutation(a[..], c[..]));
  filter_same_length_all(c[..], y => y != default);
  filterAll(c[..], y => y != default);
  permutation_length(a[..], filter(c[..], y => y != default));
  afterLoopSorted(a, c, default);
  assert(sorted(c[..]));
  
} 

/** The counting sort algorithm: simply calls each of the 3 loops. We require the following conditions on the input:
  1. For every x in a, 0 <= key(x) < k - this is required for counting sort in general.
  2. There is an element of G called default such that key(default) < 0. This is not technically required for the algorithm,
     but it is for the proof of correctness, so that we can tell which portion of the array has been filled in so far. This is
     a very mild condition to satsify: we can always add 1 more element to type G and assign its key to be negative (equivalently,
     use the type (option G) instead, and set key(None) == -1, and key(Some x) == key(x)).
 */
method countingSort(a: array<G>, k : int, default : G) returns (s: array<G>)
requires(0 < k)
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= key(a[i]) < k)
requires(key(default) < 0)
ensures(sorted(s[..]))
ensures(permutation(a[..], s[..]))
ensures(stable(a[..], s[..]))
{
  if(a.Length == 0) {
    s := a;
  }
  else {
    var b := countOccurrences(a, k);
    var c := prefixSum(a, b);
    s := constructSortedArray(a, c, default);
  }
}
