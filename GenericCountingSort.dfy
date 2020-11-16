/* A generic version of counting sort - allows elements of any type along with a key function of type T -> int
    Counting sort will sort by key and ensure stability of the underlying elements */

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

lemma filter_filter<T>(a: seq<T>, f : T -> bool, g: T -> bool)
ensures(filter(filter(a, f), g) == filter(a, y => f(y) && g(y))) {

}

//Proofs about filtering lists by lt/leq/eq relations

lemma {:induction a} filter_lt_decompose<T>(a: seq<T>, b : int, key : T -> int)
ensures(|filter(a, y => key(y) < b)| == |filter(a, y => key(y) < b - 1)| + |filter(a, y => key(y) == b - 1)|) {
}

lemma {:induction a} filter_leq_decompose<T>(a: seq<T>, x : int, key : T -> int)
ensures(|filter(a, y => key(y) <= x)| == |filter(a, y => key(y) < x)| + |filter(a, y => key(y) == x)|) {
}

lemma filter_lt_leq_minus_one<T>(a: seq<T>, x : int, key : T -> int)
ensures(filter(a, y => key(y) < x) == filter(a, y => key(y) <= x - 1)) {
}

//NOTE
lemma {:induction a} filter_bounded_in<T>(a:seq<T>, x : int, y : int, key : T -> int)
requires(x < y)
requires(exists t  :: t in a && key(t) == y)
ensures(|filter(a, z => x < key(z) && key(z) <= y)| > 0){
}

lemma {: induction a} filter_leq_decompose_bounds<T>(a : seq<T>, x : int, y : int, key : T -> int)
requires (x <= y)
ensures (|filter(a, z => key(z) <= y)| == |filter(a, z => key(z) <= x)| + |filter(a, z => x < key(z) && key(z) <= y)|) {
}

// The [numLt] and [numLeq] predicates - specifies the number of elements whose key is less than/leq the given value in an array
//  used to specify the correct position of the element in a sorted array 

function numLt<T>(x: int, a : seq<T>, key : T -> int) : int {
  |filter(a, y => key(y) < x)|
}

function numEq<T>(x: int, a : seq<T>, key : T -> int) : int {
  |filter(a, y => key(y) == x)|
}

function numLeq<T>(x: int, a : seq<T>, key : T -> int) : int {
  numLt(x, a, key) + numEq(x, a, key)
}

//An element's position in the sorted array is as follows
function seqArr<T>(x: int, a : seq<T>) : seq<T> {
  if x < 0 then [] 
    else if x > |a| then []
    else a[..x]
}

//in reality, x = a[i] (for anything useful here)
//NOTE: have as position of a given key - NOT an element
function position<T>(x : int, i : int, a : seq<T>, key : T -> int) : int {
    numLt(x, a, key) + numEq(x, seqArr(i+1, a), key) - 1
}

//Dafny cannot infer this automatically and cannot even infer from generic versions
//(parameterized by x) - this is a very annoying limitation
lemma numLt_unfold_zero<T>(a : seq<T>, key : T -> int) 
ensures(numLt(0, a, key) == |filter(a, y => key(y) < 0)|) {}

lemma numEq_minus_one<T>(x: int, a : seq<T>, key : T -> int)
ensures(numEq(x-1, a, key) == |filter(a, y => key(y) == x-1)|) {
}

lemma numLt_minus_one<T>(x: int, a : seq<T>, key : T -> int)
ensures(numLt(x-1, a, key) == |filter(a, y => key(y) < x-1)|) {
}

//Some alternate characterizations that make some things easier
lemma numLeq_direct<T>(x:int, a : seq<T>, key : T -> int) 
ensures(numLeq(x, a, key) == |filter(a, y => key(y) <= x)|) {
}

lemma {: induction x} numLt_ind<T>(x: int, a : seq<T>, key : T -> int)
ensures(numLt(x, a, key) == numEq(x-1, a, key) + numLt(x-1, a, key)) {
  numEq_minus_one(x, a, key);
  numLt_minus_one(x, a, key);
  filter_lt_decompose(a, x, key);
}

lemma numLt_leq_minus_one<T>(x: int, a : seq<T>, key : T -> int)
ensures(numLt(x, a, key) == numLeq(x-1, a, key)) {
  numLt_ind(x, a, key);
}

lemma numLeq_ind<T>(x: int, a : seq<T>, key : T -> int) 
ensures(numLeq(x,a, key) == numLeq(x-1, a, key) + numEq(x, a, key)) {
  numLeq_direct(x, a, key);
  assert(numLeq(x,a, key) == |filter(a, y => key(y) <= x)|);
  filter_leq_decompose(a, x, key);
  numLt_leq_minus_one(x, a, key);  
}

lemma numEq_app<T>(x: int, a : seq<T>, b : seq<T>, key : T -> int)
ensures(numEq(x, a + b, key) == numEq(x, a, key) + numEq(x,b, key)) {
  filter_app(a, b, y => key(y) == x);
}

//NOTE
lemma numEq_singleton<T>(x: T, y : int, key : T -> int)
requires(key(x) == y)
ensures(numEq(y, [x], key) == 1) {
  filterAll([x], z => key(z) == y);
}


//sorta note
lemma {:induction a} numEq_in_pos<T>(x: T, a : seq<T>, key : T -> int)
requires (x in a)
ensures (numEq(key(x), a, key) > 0) {
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
//  that the result is actually sorted 

lemma numLeq_lt_trans<T>(a:seq<T>, x: T, y: T, key : T -> int)
requires(key(x) < key(y))
requires(y in a)
ensures(numLeq(key(x), a, key) < numLeq(key(y), a, key)) {
  numLeq_direct(key(y), a, key);
  numLeq_direct(key(x), a, key);
  filter_leq_decompose_bounds(a, key(x), key(y), key);
  filter_bounded_in(a, key(x), key(y), key);
}

//We need 2 more similar lemmas for the sortedness equivalence proof
lemma numLeq_leq_trans<T>(a:seq<T>, x : int, y : int, key : T -> int)
requires(x <= y)
ensures(numLeq(x, a, key) <= numLeq(y, a, key)) {
    numLeq_direct(x, a, key);
    numLeq_direct(y, a, key);
    filter_leq_decompose_bounds(a, x, y, key);
}

lemma numLt_leq_bound<T>(a: seq<T>, x : int, y : int, key : T -> int) 
requires(x < y)
ensures(numLeq(x, a, key) - 1 < numLt(y, a, key)) {
    numLt_leq_minus_one(y, a, key);
    numLeq_leq_trans(a, x, y-1, key);
}

//what we really need - injectivity for position function - if a[i] and a[j] have the same position - i = j

lemma position_bounds<T>(a: seq<T>, x: T, i : int, key : T -> int)
requires(0 <= i < |a|)
requires(x in a[..i+1])
ensures(numLt(key(x), a, key) <= position(key(x), i, a, key) <= numLeq(key(x), a, key) - 1) {
  numEq_in_pos(x, a[..(i+1)], key);
  assert(numLt(key(x), a, key) <= position(key(x), i, a, key));
  assert(a == a[..(i+1)] + a[(i+1)..]);
  numEq_app(key(x), a[..(i+1)], a[(i+1)..], key);
  assert (numEq(key(x), a[..(i+1)], key) <= numEq(key(x), a, key));
}


lemma position_inj<T>(a: seq<T>, i : int, j : int, key : T -> int)
requires(0 <= i < |a|)
requires(0 <= j < |a|)
requires(position(key(a[i]), i, a, key) == position(key(a[j]), j, a, key))
ensures(i == j) {
  //proof by contradiction
  if(i == j) {}
  else {
    if(key(a[i]) == key(a[j])) { 
      assert(numLt(key(a[i]), a, key) == numLt(key(a[j]), a, key));
      //both cases are similar
      if(i < j) {
        assert(a[..(j+1)] == a[..(i+1)] + a[i+1..j+1]);
        numEq_app(key(a[j]), a[..(i+1)], a[i+1..j+1], key);
        numEq_in_pos(a[j], a[i+1..j+1], key);
      }
      else {
        assert(a[..(i+1)] == a[..(j+1)] + a[j+1..i+1]);
        numEq_app(key(a[i]), a[..(j+1)], a[j+1..i+1], key);
        numEq_in_pos(a[i], a[j+1..i+1], key);
      }
    }
    else {
      //again, cases are similar
      if(key(a[i]) < key(a[j])) {
        position_bounds(a, a[i], i, key);
        position_bounds(a, a[j], j, key);
        numLt_leq_bound(a, key(a[i]), key(a[j]), key);
      }
      else {
        position_bounds(a, a[i], i, key);
        position_bounds(a, a[j], j, key);
        numLt_leq_bound(a, key(a[j]), key(a[i]), key);
      }
    }    
  }
}

//For equal elements, positions and indices have the same ordering
lemma positions_eq_preserve_order<T>(a : seq<T>, k : int, i : int, x : T, key: T -> int)
requires(0 <= i < |a|)
requires(0 <= k < |a|)
requires(position(key(x), k, a[..], key) < position(key(x), i, a[..], key))
ensures(k < i) {
  if(k < i) {
  }
  else {
    assert(i <= k);
    assert(a[..k+1] == a[..i+1] + a[i+1..k+1]);
    numEq_app(key(x), a[..i+1], a[i+1..k+1], key);
  }
}

//a is array of T's
//b is array that counts number of elts in a with each key
//so initially, b[j] = numLeq(a, j, key)
//then b[j] = position()
//NOTE : b will be array of T's, then b[j] == position()

//How position changes when we decrease index
//NOTE
lemma position_decr_index_same<T>(a : seq<T>, i : int, key : T -> int)
requires(0 <= i < |a|)
ensures(position(key(a[i]), i - 1, a[..], key) == position(key(a[i]), i, a[..], key) - 1) {
  assert (a[..(i+1)] == a[..i] + [a[i]]);
  numEq_app(key(a[i]), a[..i], [a[i]], key);
  numEq_singleton(a[i], key(a[i]), key);
}

lemma position_decr_index_diff<T>(a : seq<T>, i : int, x : int, key: T -> int)
requires(0 <= i < |a|)
requires(key(a[i]) != x)
ensures(position(x, i - 1, a[..], key) == position(x, i, a[..], key)) {
  assert (a[..(i+1)] == a[..i] + [a[i]]);
  numEq_app(x, a[..i], [a[i]], key);
  filterEmpty([a[i]], y => key(y) == x);
  assert(numEq(x, [a[i]], key) == 0);
}

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

//Now, we prove that if a and b are permutations, then they have the same length (not the case with noDups)
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

//We define the map function and don't do too much with it (SEE)
function mapKey<T>(a: seq<T>, key : T -> int) : seq<int> {
    if (|a| <= 0) then [] else [key(a[0])] + mapKey(a[1..], key) 
}

lemma mapKey_length<T>(a: seq<T>, key: T -> int) 
ensures(|a| == |mapKey(a, key)|) {
}

lemma mapKey_nil<T>(a: seq<T>, key : T -> int)
requires(|a| == 0)
ensures(mapKey(a, key) == []) {

}

lemma mapKey_app<T>(a: seq<T>, b : seq<T>, key : T -> int)
ensures(mapKey(a + b, key) == mapKey(a, key) + mapKey(b, key)) {
    if(|a| <= 0) {
        assert(a == []);
        mapKey_nil(a, key);
        assert(a + b == b);
    }
    else {
        assert((a+b)[1..] == a[1..] + b);
    }
}

lemma mapKey_in<T>(a: seq<T>, x : T, k : int, key : T -> int)
requires(x in a)
requires(0 <= k < |a|)
requires(a[k] == x)
requires(|a| == |mapKey(a, key)|) //always true
ensures(mapKey(a, key)[k] == key(x)) {
    if (|a| <= 0) {
    }
    else {
        if (k == 0) {}
        else {
            mapKey_length(a[1..], key);
            mapKey_in(a[1..], x, k-1, key);
            assert(mapKey(a[1..], key)[k-1] == mapKey(a[..], key)[k]);
        }
    }
}

lemma numEq_mapKey<T>(a: seq<T>, x : int, key : T -> int)
ensures(numEq(x, a, key) == |filter(mapKey(a, key), y => y == x)|) {

}

//really annoying to prove (of couse, holds for map in general)
lemma perm_mapKey<T>(a: seq<T>, b : seq<T>, key : T -> int) 
requires(permutation(a,b))
ensures(permutation(mapKey(a, key), mapKey(b, key))) {
    permutation_length(a, b);
    if (|a| <= 0) {}
    else {
        assert(a[0] in a);
        assert(key(a[0]) in mapKey(a, key));
        perm_in(b, a);
        assert (a[0] in b);
        assert(exists k :: 0 <= k < |b| && b[k] == a[0]);
        var k :| 0 <= k < |b| && b[k] == a[0];
        mapKey_length(b, key);
        mapKey_in(b, a[0], k, key);
        assert(b == b[..k] + [b[k]] + b[k+1..]);
        assert(a == [a[0]] + a[1..]);
        var newB := b[..k] + b[k+1..];
        assert(multiset(b) == multiset(b[..k]) + multiset([b[k]]) + multiset(b[k+1..]));
        assert(multiset(a) == multiset([a[0]]) + multiset(a[1..]));
        assert(multiset(newB) + multiset([b[k]]) == multiset(b));
        assert(multiset([b[k]]) == multiset([a[0]]));
        multiset_union_inj(multiset(a[1..]), multiset(newB), multiset([a[0]]));
        assert(multiset(a[1..]) == multiset(newB));
        perm_mapKey(a[1..], newB, key); //use IH
        assert(multiset(mapKey(a[1..], key)) == multiset(mapKey(newB, key)));
        assert(b == b[..k] + b[k..]);
        mapKey_app(b[..k], b[k..], key);
        multiset_app(mapKey(b[..k], key), mapKey(b[k..], key));
        assert(multiset(mapKey(b, key)) == multiset(mapKey(b[..k], key)) + multiset(mapKey(b[k..], key)));
        mapKey_app([a[0]], a[1..], key);
        mapKey_app(b[..k], b[k..], key);
        assert(b[k..] == [b[k]] + b[k+1..]);
        mapKey_app([b[k]], b[k+1..], key);
        mapKey_app(b[..k], b[k+1..], key);
        multiset_app(mapKey([a[0]], key), mapKey(a[1..], key));
        multiset_app(mapKey([b[k]], key), mapKey(b[k+1..], key));
        multiset_app(mapKey(b[..k], key), mapKey(b[k+1..], key));
    }
}

//todo: here
/*
lemma {:induction a} numEq_multiset<T>(x: T, a : seq<T>, key : T -> int)
ensures(numEq(key(x), a, key) == multiset(a)[x]) {
  if(|a| <= 0) {
  }
  else {
    assert(a ==[a[0]] + a[1..]);
    numEq_app(key(x), [a[0]], a[1..], key);
    multiset_app([a[0]], a[1..]);
  }
}
*/

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

//|filter(mapKey(a, key), y => y == x)|

lemma numEq_perm<T>(a:seq<T>, b : seq<T>, x : int, key : T -> int)
requires(permutation(a,b))
ensures(numEq(x, a, key) == numEq(x, b, key)) {
    perm_mapKey(a, b, key);
    numEq_mapKey(a, x, key);
    numEq_mapKey(b, x, key);
    perm_preserves_filter_eq(mapKey(a, key), mapKey(b, key), x);
}

lemma perm_preserve_pred<T>(a:seq<T>, b:seq<T>, f: T -> bool)
requires(permutation(a, b))
requires(forall x :: x in a ==> f(x))
ensures(forall x :: x in b ==> f(x)) {
  forall x | x in b {
    perm_in(a, b);
  }
}

//This is really true without the lower bound but it is much easier to prove this way, and it is OK because all elts are positive anyway
lemma {:induction x} numLt_perm<T>(a: seq<T>, b: seq<T>, x : int, key : T -> int)
requires (permutation(a, b))
requires(forall x :: x in a ==> key(x) >= 0)
ensures(numLt(x, a, key) == numLt(x, b, key)) {
  if(x <= 0) {
    filterEmpty(a, y => key(y) < x);
    perm_preserve_pred(a, b, y => key(y) >= 0);
    filterEmpty(b, y => key(y) < x);
  }
  else {
    numLt_ind(x, a, key);
    numLt_ind(x, b, key);
    numLt_perm(a, b, x-1, key);
    assert(numLt(x, a, key) == |filter(a, y => key(y) < x)|);
    assert(numLt(x, b, key) == |filter(b, y => key(y) < x)|);
    numEq_perm(a, b, x-1, key);
    assert(numEq(x-1, a, key) == numEq(x-1, b, key));
    perm_in(a, b);
    perm_in(b,a);
  }
}

//numLeq is also preserved over permutations
lemma numLeq_perm<T>(a: seq<T>, b: seq<T>, x : int, key : T -> int)
requires (permutation(a, b))
requires(forall x : T :: x in a ==> key(x) >= 0)
ensures(numLeq(x, a, key) == numLeq(x, b, key)) {
  numLt_perm(a, b, x, key);
  numEq_perm(a, b, x, key);
  perm_in(a,b);
  perm_in(b,a);
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

//A sequence is sorted if the expected condition is satisfied - ie, if i <= j, a[i] <= a[j]
predicate sorted<T>(a: seq<T>, key : T -> int) {
  forall i : int, j : int :: 0 <= i < |a| ==> 0 <= j < |a| && i <= j ==> key(a[i]) <= key(a[j])
}

//alternate sorting condition - if every element is at one of its possible correct positions in the array, then the array is sorted
//  generalization of version in DistinctElts, because an element can be in a range of possible positions
predicate sorted_alt<T>(a:seq<T>, key : T -> int) {
  forall i : int :: 0 <= i < |a| ==> numLt(key(a[i]), a[..], key) <= i <= numLeq(key(a[i]), a[..], key) - 1
}

//The only direction we need - if a sequence satsifies [sorted_alt(a)], then it satisfies [sorted(a)]
lemma sorted_alt_implies_sorted<T>(a: seq<T>, key : T -> int)
requires(sorted_alt(a, key))
ensures(sorted(a, key)) {
  forall i : int, j : int | 0 <= i < |a| && 0 <= j < |a| && i <= j
    ensures(key(a[i]) <= key(a[j])) {
      if(key(a[j]) < key(a[i])) {
        numLt_leq_bound(a, key(a[j]), key(a[i]), key);
      }
      else {
      }
    }
}

//We use a stronger invariant, so we want to show that this implies sorting
lemma all_positions_implies_sorted<T>(a : seq<T>, c : seq<T>, key : T -> int)
requires(permutation(a, c))
requires(|a| == |c|)
requires(forall x :: x in a ==> key(x) >= 0)
requires(forall j :: 0 <= j < |c| ==> exists k :: ((-1 < k < |a|) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key)))
ensures(sorted_alt(c, key)) {
  forall i : int | 0 <= i < |a|
  ensures(numLt(key(c[i]), c[..], key) <= i <= numLeq(key(c[i]), c[..], key) - 1) {
    assert(0 <= i < |c|);
    var k :| (-1 < k < |a|) && c[i] == a[k] && i == position(key(a[k]), k, a[..], key);
    position_bounds(a, a[k], k, key);
    numLt_perm(a, c, key(c[i]), key);
    numEq_perm(a, c, key(c[i]), key);
  }
}

//If the [sorted_alt] condition holds on an array, then it holds on the seq version of the array too
lemma sorted_alt_seq_array<T>(a: array<T>, key : T -> int) 
requires(forall i : int :: 0 <= i < a.Length ==> numLt(key(a[i]), a[..], key) <= i <= numLeq(key(a[i]), a[..], key) - 1)
ensures(sorted_alt(a[..], key)){
}

// Stability = we say that a and b are stable with respect to each other if the relative order of equal elements is preseved
//  We can express that as the following 

predicate stable<T>(a : seq<T>, b : seq<T>, key : T -> int) {
  forall x : int :: filter(a, y => key(y) == x) == filter(b, y => key(y) == x)
}
/* Lemmas to prove function invariants */

lemma filter_split_idx<T>(a: array<T>, f: T -> bool, i : int)
requires(0 <= i < a.Length) 
ensures(filter(a[..i+1], f) == filter(a[..i], f) + filter([a[i]], f)) {
  assert(a[..i+1] == a[..i] + [a[i]]);
  filter_app(a[..i], [a[i]], f);
}

lemma numEq_split_idx<T>(a: array<T>, i : int, key : T -> int) 
requires(0 <= i < a.Length)
ensures(forall j :: numEq(j, a[..i+1], key) == numEq(j, a[..i], key) + numEq(j, [a[i]], key)) {
  forall j  {
    filter_split_idx(a, y => key(y) == j, i);
  }
}

//The first loop of countingSort - builds an array that counts the occurrences of each element 

//Prove the invariant is preserved through the loop in a separate lemma, since Dafny has trouble proving it automatically
lemma countOccurrencesInvariant<T>(a : array<T>, b : seq<int>, newB : seq<int>, i : int, elt: int, key : T -> int)
requires(0 <= i < a.Length)
requires(0 <= key(a[i]) < |b|)
requires(|b| == |newB|)
requires(key(a[i]) == elt)
requires(newB == b[elt := b[elt]   + 1])
requires(forall j :: 0 <= j < |b| ==> b[j] == numEq(j, a[..i], key))
ensures(forall j :: 0 <= j < |newB| ==> newB[j] == numEq(j, a[..i+1], key)) {
  forall j | 0 <= j <|newB|
  ensures(newB[j] == numEq(j, a[..i+1], key)) {
    assert(a[..i+1] == a[..i] + [a[i]]);
    numEq_app(j, a[..i], [a[i]], key);
    if(j == elt) {
      numEq_singleton(a[i], key(a[i]), key);
      assert(newB[j] == b[elt] + 1);  
    }
    else {
      filterEmpty([a[i]], y => key(y) == j); 
    }
  }
}

method countOccurrences<T> (a: array<T>, k: int, key : T -> int) returns (b: array<int>)
requires 0 < a.Length
requires 0 < k
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= key(a[i]) < k)
ensures (b.Length == k + 1)
ensures(forall i : int :: 0 <= i <= k ==> b[i] == numEq(i, a[..], key))
{
  b := new int[k+1](i => 0);
  var i := 0;
  while(i < a.Length) 
  decreases(a.Length - i)
  invariant (0 <= i <= a.Length)
  invariant(forall j : int :: 0 <= j <= k ==> b[j] == numEq(j, a[..i], key)) {
    ghost var oldB := b[..];
    ghost var ai := key(a[i]);
    b[key(a[i])] := b[key(a[i])] + 1;

    assert(b[..] == oldB[ai := oldB[ai] + 1]);
    countOccurrencesInvariant(a, oldB, b[..], i, key(a[i]), key);

    i := i + 1;
    assert(forall j : int :: 0 <= j <= k ==> b[j] == numEq(j, a[..i], key)); //for some reason, need this for it to verify
  }
  assert(a[..i] == a[..]);
}


//The second loop in countingSort - returns array which gives positions of elements in sorted array//
method prefixSum<T>(a:array<T>, b : array<int>, key : T -> int) returns (c: array<int>)
requires(0 < b.Length)
requires(forall i : int :: 0 <= i < b.Length ==> b[i] == numEq(i, a[..], key))
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= key(a[i]))
ensures(c.Length == b.Length)
ensures(forall i : int {:induction i} :: 0 <= i < b.Length ==> (c[i] == numLeq(i, a[..], key) - 1));
{
  var i := 1;
  //need to know that there are no elements less than x
  numLt_unfold_zero(a[..], key);
  filterEmpty(a[..], y => key(y) < 0);
  assert(numLeq(0, a[..], key) == b[0]);
  c := new int[b.Length];
  c[0] := b[0] - 1;
  while(i < c.Length)
  decreases (b.Length - i)
  invariant (1 <= i <= c.Length)
  invariant(forall j: int {:induction j} :: (0 <= j < i ==> c[j] == numLeq(j, a[..], key) - 1))
  {
    numLeq_ind(i, a[..], key);
    c[i] := b[i] + c[i-1];
    i := i + 1;
  }
}

// The third loop - lemmas and invariants 

//The third loop is much more complicated to prove correct. To ensure Dafny does not time out, we do almost all
//  of the nontrivial work (invariant preservation, proving postconditions, proving key properties) in the following lemmas.

//The array b is correct to begin
lemma constructSortedArrayBInvarEntry<T>(a: array<T>, b : array<int>, i : int, key : T -> int)
requires (forall j :: 0 <= j < b.Length ==> b[j] == numLeq(j, a[..], key) - 1)
requires(i == a.Length - 1)
ensures (forall j :: 0 <= j < b.Length ==> b[j] == numLt(j, a[..], key) + numEq(j, a[..(i+1)], key) - 1) {
    forall j | 0 <= j < b.Length
    ensures (b[j] == numLt(j, a[..], key) + numEq(j, a[..(i+1)], key) - 1) {
        assert (a[..(i+1)] == a[..]);
    }
}

//requires(forall j :: 0 <= j < |c| ==> exists k :: ((-1 < k < |a|) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key)))


//A key lemma: in our loop, c[b1[a]] != -1, so we do not overwrite a previously written value
//NOTE: for default - plan is to require a default where key(default) == -1
lemma sortedArrayLoopSeesNewElt<T>(a: array<T>, b: array<int>, c: array<T>, i : int, default : T, key : T -> int)
requires(a.Length == c.Length)
requires(0 <= i < a.Length)
requires(forall x : T :: x in a[..] ==> x != default)
requires(forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key)))
requires((forall j :: 0 <= j < b.Length ==> b[j] == position(j, i, a[..], key)))
requires(0 <= key(a[i]) < b.Length)
requires(0 <= b[key(a[i])] < c.Length)
ensures(c[b[key(a[i])]] == default) {
  //pf by contradiction
  if(c[b[key(a[i])]] == default) {}
  else {
    var k :| (i < k < a.Length) && c[b[key(a[i])]] == a[k] && b[key(a[i])] == position(key(a[k]), k, a[..], key);
    assert(b[key(a[i])] == position(key(a[k]), k, a[..], key));
    assert(b[key(a[i])] == position(key(a[i]), i, a[..], key));
    position_inj(a[..], i, k, key);
  }
}

//trivial but fairly useful: splitting lemma by index
lemma seq_split<T>(a: seq<T>, i : int)
requires (0 <= i < |a|)
ensures(a == a[..i] + [a[i]] + a[i+1..]) {}

//The permutation invariant: the completed part of c is a permutation of a[(i+1)..]
lemma permutation_invariant<T>(a: array<T>, c : seq<T>, oldC : seq<T>, idx : int, i : int, default : T, key : T -> int)
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
    filter_app(oldC[..idx] + [oldC[idx]], oldC[idx + 1..], y => y != default); //we can split filter into 0..b[a[i]], the elt b[a[i]], and the rest of the list
    filter_app(oldC[..idx], [oldC[idx]], y => y != default);
    multiset_app(filter(oldC[..idx] + [oldC[idx]], y => y != default), filter(oldC[idx + 1..], y => y != default)); //we can split filter into 0..b[a[i]], the elt b[a[i]], and the rest of the list
    multiset_app(filter(oldC[..idx], y => y != default), filter([oldC[idx]], y => y != default));
    filterEmpty([oldC[idx]], y => y != default);
    assert(multiset(filter(oldC, y => y != default)) == multiset((filter(oldC[..idx], y => y != default))) +
        multiset((filter(oldC[idx+1..], y => y != default))));
    seq_split(c[..], idx);
    filter_app(oldC[..idx] + [c[idx]], oldC[idx + 1..], y => y != default);
    filter_app(oldC[..idx], [c[idx]], y => y != default);
    assert(c[idx] == a[i]);
    multiset_app(filter(oldC[..idx] + [c[idx]], y => y != default), filter(oldC[idx + 1..], y => y != default)); //we can split filter into 0..b[a[i]], the elt b[a[i]], and the rest of the list
    multiset_app(filter(oldC[..idx], y => y != default), filter([c[idx]], y => y != default));
    assert(multiset(a[i..]) == multiset([a[i]]) + multiset(a[i+1..]));
    assert(c[idx] == a[i]);
    assert(a[i] in a[..]);
    assert(c[idx] != default);
    filterAll([c[idx]], y => y != default);
}

//The invariant that the length of the completed part of c is |a| - (i+1)
lemma filter_length_invariant<T>(a: array<T>, c : seq<T>, oldC : seq<T>, idx : int, i : int, default : T, key : T -> int)
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
  assert(|filter(oldC, y => y != default)| == a.Length - (i + 1)); //assumption
    seq_split(oldC, idx);
    assert(oldC == (oldC[..idx] + [oldC[idx]])+ oldC[idx + 1..]);
    filter_app(oldC[..idx] + [oldC[idx]], oldC[idx + 1..], y => y != default); //we can split filter into 0..b[a[i]], the elt b[a[i]], and the rest of the list
    filter_app(oldC[..idx], [oldC[idx]], y => y != default);
    filterEmpty([oldC[idx]], y => y != default); //since c[idx] = -1
    seq_split(c[..], idx);
    assert(c[..] == c[..idx] + [c[idx]] + c[idx+1..]);
    filter_app(oldC[..idx] + [c[idx]], oldC[idx + 1..], y => y != default);
    filter_app(oldC[..idx], [c[idx]], y => y != default);
    assert(c[idx] == a[i]);
    assert(a[i] in a[..]);
    assert(c[idx] != default);
}


//The values in the b array are bounded (used for array bounds)
lemma b_bound_invariant<T>(a: array<T>, oldB : seq<int>, b : seq<int>, i: int, idx : int, key : T -> int)
requires(0 <= i < a.Length)
requires(0 <= key(a[i]) < |oldB|)
requires(|b| == |oldB|)
requires(b[key(a[i])] == idx - 1)
requires(forall j :: 0 <= j < |b| ==> j != key(a[i]) ==> b[j] == oldB[j]);
requires(idx == oldB[key(a[i])])
requires(forall j : int :: 0 <= j < |oldB| ==> oldB[j] <= numLeq(j, a[..], key) - 1)
ensures((forall j : int :: 0 <= j < |b| ==> b[j] <= numLeq(j, a[..], key) - 1)){
}

//Invariant that the array "b" consists of the positions of all elements, only considering equal elements up to index i
lemma b_position_invariant<T>(a:array<T>, oldB : seq<int>, b : seq<int>, i : int, idx : int, key : T -> int)
requires(0 <= i < a.Length)
requires(0 <= key(a[i]) < |oldB|)
requires(|b| == |oldB|)
requires(b[key(a[i])] == idx - 1)
requires(forall j :: 0 <= j < |b| ==> j != key(a[i]) ==> b[j] == oldB[j]);
requires(idx == oldB[key(a[i])])
requires(forall j :: 0 <= j < |oldB| ==> oldB[j] == position(j, i, a[..], key));
ensures(forall j :: 0 <= j < |b| ==> b[j] == position(j, i-1, a[..], key)) {
  forall j | 0 <= j < |b| 
  ensures(b[j] == position(j, i-1, a[..], key)) {
    if(j == key(a[i])) {
      assert(b[j] == oldB[j] - 1);
      position_decr_index_same(a[..], i, key);
      assert(position(j, i-1, a[..], key) == position(j, i, a[..], key) - 1);
    }
    else {
      position_decr_index_diff(a[..], i, j, key);
    }
  }
}

//The important invariant for sorting and stability: each element c[j] corresponds to the element of k actually at position j in a sorted array
lemma c_structure_invariant<T>(a: array<T>, b: seq<int>, c : seq<T>, oldC: seq<T>, idx : int, i : int, default : T, key : T -> int)
requires(0 <= i < a.Length)
requires(0 <= key(a[i]) < |b|)
requires(a.Length == |c|)
requires(idx == b[key(a[i])])
requires(idx == position(key(a[i]), i, a[..], key))
requires(|c| == |oldC|)
requires(0 <= idx < a.Length)
requires(c == oldC[idx := a[i]])
requires(forall x :: x in a[..] ==> x != default)
requires(forall j :: 0 <= j < |oldC| ==> oldC[j] != default ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..], key)))
ensures(forall j :: 0 <= j < |c| ==> c[j] != default ==> exists k :: ((i-1 < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key))) {
  forall j | 0 <= j < |c| && c[j] != default
  ensures(exists k :: (i-1 < k < a.Length) && c[j] == a[k]) {
    if(j != idx) {
    }
    else {
      assert(-1 < i < a.Length);
      assert(c[j] == a[i]);
      assert(j == position(key(a[i]), i, a[..], key));
    }
  }
}

//Prove that the invariants imply the postconditions in a separate lemma

//Our loop invariants imply the output is a permutation of the input
lemma afterLoopPermutation<T>(a: array<T>, c : array<T>, default : T, key : T -> int)
requires(permutation((a[0..]),(filter(c[..], y => y != default)))) //permutation invariant
requires(a.Length == c.Length)
ensures(permutation(a[..], c[..])) {
  permutation_length(a[..], (filter(c[..], y => y != default)));
  filter_same_length_all(c[..], y => y != default); //the filtered list is the original list
  filterAll(c[..], y => y != default);  
}

//Our loops invariants imply the output is sorted
lemma afterLoopSorted<T>(a : array<T>, c : array<T>, default : T, key : T -> int)
requires(forall x :: x in a[..] ==> key(x) >= 0)
requires(|filter(c[..], y => y != default)| == a.Length)
requires(permutation(a[..], c[..]))
requires(a.Length == c.Length)
requires(forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((-1 < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key)))
ensures(sorted(c[..], key)) {
  filter_same_length_all(c[..], y => y != default); //the filtered list is the original list
  filterAll(c[..], y => y != default);
  all_elems_seq_array(c, y => y != default); //all elements in c satsify y >= 0
  all_elems_seq_array(c, y => y != default);
  assert(forall j :: 0 <= j  < c.Length ==> c[j] != default);
  assert(forall j :: 0 <= j < c.Length ==> exists k :: ((-1 < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key)));
  all_positions_implies_sorted(a[..], c[..], key);
  assert(sorted_alt(c[..], key)); 
  sorted_alt_seq_array(c, key); //c[..] satsifes sorted_alt condition
  sorted_alt_implies_sorted(c[..], key); //c[..] is sorted
}

lemma no_default_elts<T>(a: array<T>, default : T, key : T -> int)
requires(forall j :: 0 <= j < a.Length ==> 0 <= key(a[j])); 
requires(key(default) < 0)
ensures(forall x : T :: x in a[..] ==> x != default) {

}

// Proofs for stability 

//(Note: because we sort using the integer values, stability is kind of meaningless, and we can in fact "prove" it using 
// the permutation info. But we do the real proof that holds even when sorting by a specific key)

//first, we need to know that at any point in the loop, for all j < b[a[i]], c[j] != a[i] - ie, the current element is the
//first one in the current array with that value - because we go backwards, this ensures stability
lemma all_same_elts_come_after<T>(a: array<T>, oldC : seq<T>, i : int, ai : T, bai : int, default : T, key : T -> int)
requires(0 <= i < a.Length)
requires(ai == a[i])
requires(0 <= key(ai))
//requires(forall x :: x in a[..] ==> x != default)
requires(key(default) < 0)
// /requires(0 <= ai < |b|)
//requires(bai == b[ai])
requires(bai == position(key(ai), i, a[..], key))
requires(0 <= bai < |oldC|)
requires(a.Length == |oldC|)
requires(forall j :: 0 <= j < |oldC| ==> oldC[j] != default ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..], key)))
ensures(forall j :: 0 <= j < bai ==> key(oldC[j]) != key(a[i])) {
  forall j | 0 <= j < bai
  ensures(key(oldC[j]) != key(a[i])) {
    if(key(oldC[j]) == key(a[i])) {
      //assert(oldC[j] != default);
      var k :| ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..], key));
      assert(position(key(a[i]), k, a[..], key) < position(key(a[i]), i, a[..], key));
      positions_eq_preserve_order((a[..]), k, i, a[i], key);
    }
    else {}
  }
}
/*
lemma no_elts_come_before<T>(a: array<T>, oldC : seq<T>, i : int, ai : T, bai : int, default : T, key : T -> int)
requires(0 <= i < a.Length)
requires(ai == a[i])
requires(0 <= key(ai))
requires(a[i] != default)
// /requires(0 <= ai < |b|)
//requires(bai == b[ai])
requires(bai == position(key(ai), i, a[..], key))
requires(0 <= bai < |oldC|)
requires(a.Length == |oldC|)
requires(forall j :: 0 <= j < |oldC| ==> oldC[j] != default ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..], key)))
ensures(forall j :: 0 <= j < bai ==> oldC[j] != a[i]) {

}*/

lemma filter_filter_special<T>(a: seq<T>, default : T, x: int, key : T -> int)
ensures(filter((filter(a, y => y != default)), y => key(y) == x) == filter(a, y => y != default && key(y) == x)) {
}

lemma stable_invariant_preserved<T>(a: array<T>, b : seq<int>, oldC : seq<T>, c : seq<T>, i : int, ai: T, bai : int, default: T, key : T -> int)
requires(0 <= i < a.Length)
requires(ai == a[i])
requires(0 <= key(ai) < |b|)
requires(bai == b[key(a[i])])
requires(bai == position(key(ai), i, a[..], key))
requires(0 <= bai < |c|)
requires(a.Length == |c|)
requires(|c| == |oldC|)
requires(oldC[bai] == default)
requires(c == oldC[bai := ai])
requires(a[i] != default)
requires(key(default) < 0)
requires(forall j :: 0 <= j < |oldC| ==> oldC[j] != default ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..], key)))
requires(forall x : int :: filter(a[i+1..], y => key(y) == x) == filter(filter(oldC, y => y != default), y => key(y) == x))
ensures(forall x : int :: filter(a[i..], y => key(y) == x) == filter(filter(c, y => y != default), y => key(y) == x)) {
  forall x 
  ensures (filter(a[i..], y => key(y) == x) == filter(filter(c, y => y != default), y => key(y) == x)) {
    assert(filter(a[i+1..], y => key(y) == x) == filter(filter(oldC, y => y != default), y => key(y) == x));
    filter_filter_special(c, default, x, key);
    filter_filter_special(oldC, default, x, key);
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
      all_same_elts_come_after(a, oldC, i, a[i], b[key(a[i])], default, key);
      assert(forall j :: 0 <= j < b[key(a[i])] ==> key(c[j]) != x);
      
      filterEmpty(c[..b[key(a[i])]], y => (y != default && key(y) == x));
      filterEmpty(oldC[..b[key(a[i])]], y => (y != default && key(y) == x));
      assert(filter([c[b[key(a[i])]]], y => (y != default && key(y) == x)) == [a[i]]);
      filterEmpty([oldC[b[key(a[i])]]], y => (y != default && key(y) == x));
      //filter_filter_special(c, x, default, key);
      
      assert(filter(filter(c, y => y != default), y => key(y) == x) == filter(c, y => (y != default && key(y) == x)));
      assert(filter(c[..b[key(a[i])]], y => (y != default && key(y) == x)) == []);
      assert(c == c[..b[key(a[i])]] + [c[b[key(a[i])]]] + c[b[key(a[i])] + 1..]);
      //assert(filter(c, y => (y >= 0 && y == x)) == filter(c[..b[a[i]]], y => (y >= 0 && y == x)) +  filter([c[b[a[i]]]], y => (y >= 0 && y == x)) + filter(c[b[a[i]] + 1..], y => (y >= 0 && y == x)));

      //assert(filter(c, y => (y >= 0 && y == x)) == filter([c[b[a[i]]]], y => (y >= 0 && y == x)) + filter(c[b[a[i]] + 1..], y => (y >= 0 && y == x)));
      assert(filter(filter(c, y => y != default), y => key(y) == x) == [a[i]] + filter(c[b[key(a[i])] + 1..], y => (y != default && key(y) == x)));

      assert(filter(filter(oldC, y => y != default), y => key(y) == x) == filter(oldC[b[key(a[i])] + 1..], y => (y != default && key(y) == x))); 
      assert((filter(a[i..], y => key(y) == x) == filter(filter(c, y => y != default), y => key(y) == x))); 
    }
    else {
      filterEmpty([c[b[key(a[i])]]], y => (y != default && key(y) == x));
    }
    
  }
}


lemma afterLoopStable<T>(a : array<T>, c : array<T>, default : T, key : T -> int)
requires(a.Length == c.Length)
requires(forall x : int :: filter(a[..], y => key(y) == x) == filter(filter(c[..], y => y != default), y => key(y) == x))
requires(|filter(c[..], y => y != default)| == a.Length)
ensures(stable(a[..], c[..], key)) {
    filter_same_length_all(c[..], y => y != default);
    filterAll(c[..], y => y != default);
    assert((filter(c[..], y => y != default) == c[..]));
}


//The third (and much more complicated) loop of counting sort: put each element in its correct position 
//a is the original array, b is prefix sum array 

method constructSortedArray<T>(a: array<T>, b: array<int>, default : T, key : T -> int) returns (c : array<T>)
requires(forall i : int {:induction i} :: 0 <= i < b.Length ==> (b[i] == numLeq(i, a[..], key) - 1));
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= key(a[i]) < b.Length)
requires(key(default) < 0)
//ensures(permutation(a[..], c[..]))
//ensures(sorted(c[..], key))
//ensures(stable(a[..], c[..], key))
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
  assert(forall i :: 0 <= i < b1.Length ==> b1[i] == numLeq(i, a[..], key) - 1);
  assert(forall i : int :: 0 <= i < a.Length ==> 0 <= key(a[i]) < b1.Length);

  c := new T[a.Length](i => default);
  i := a.Length - 1;
  //establish loop invariants
  assert(a[(i+1)..a.Length] == []);
  inSeqArray(c, y => y == default);
  filterEmpty(c[..], y => y != default);
  
  //establish the b invariant
  constructSortedArrayBInvarEntry(a, b1, i, key);
  
  //ghost var bLen := b.Length;



  while(i >= 0)
  decreases (i-0)
  
  invariant(-1 <= i < a.Length)
  invariant(b1.Length == b.Length) //need for bounds
  invariant(forall j :: 0 <= j < a.Length ==> 0 <= key(a[j]) < b1.Length); //also need for bounds
  invariant(forall j : int :: 0 <= j < b1.Length ==> b1[j] <= numLeq(j, a[..], key) - 1) //used for bounds checks
  //technically, this invariant is implied by the next one (by permutation_length), but the proofs are much faster if we include both
  invariant(|filter(c[..], y => y != default)| == a.Length - (i + 1)); //ensures that we fill all of c
  invariant(permutation((a[(i+1)..]),(filter(c[..], y => y != default)))) //permutation invariant
  invariant(forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i, a[..], key)) //the array b at each step (b is changing)
  invariant(forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key))) //every filled in element of c is a previously seen elt
  invariant(forall x : int :: filter(a[(i+1)..], y => key(y) == x) == filter(filter(c[..], y => y != default), y => key(y) == x)) 
  
  {
/*
  assume(-1 <= i < a.Length);
  assume(b1.Length == b.Length); //need for bounds
  assume(forall j :: 0 <= j < a.Length ==> 0 <= key(a[j]) < b1.Length); //also need for bounds
  assume(forall j : int :: 0 <= j < b1.Length ==> b1[j] <= numLeq(j, a[..], key) - 1); //used for bounds checks
  //technically, this invariant is implied by the next one (by permutation_length), but the proofs are much faster if we include both
  assume(|filter(c[..], y => y != default)| == a.Length - (i + 1)); //ensures that we fill all of c
  assume(permutation((a[(i+1)..]),(filter(c[..], y => y != default)))); //permutation invariant
  assume(forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i, a[..], key)); //the array b at each step (b is changing)
  assume(forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key))); //every filled in element of c is a previously seen elt
  assume(forall x : int :: filter(a[(i+1)..], y => key(y) == x) == filter(filter(c[..], y => y != default), y => key(y) == x));*/
    //make sure everything is in bounds
    assert(0 <= i < a.Length);
    var ai := key(a[i]);
    assert(0 <= ai < b1.Length);
    //first, show that b[a[i]] is nonnegative
    numEq_in_pos(a[i], a[..(i+1)], key);
    assert(0 <= b1[ai]);
    //then, show that it is bounded
    //ghost var ai := key(a[i]);
    filter_length_leq(a[..], y => key(y) <= ai);
    numLeq_direct(ai, a[..], key);
    assert(0 <= b1[ai] < c.Length);
  
    //ghost variables to refer to the old values of variables
    ghost var oldC := c[..];
    ghost var oldB := b1[..];
    ghost var cLen := c.Length;
    var idx := b1[ai];



    no_default_elts(a, default, key);  
    //A crucial step: show that c[b1[a[i]]] == -1, so we are actually considering a new element
    sortedArrayLoopSeesNewElt(a, b1, c, i, default, key);
    assert(c[idx] == default);
  
   
    //The actual update
    c[idx] := a[i];

    b1[ai] := idx - 1;



    //What we changed
    assert(c[..] == oldC[idx := a[i]]);
    //assert(b1[..] == oldB[ai := idx - 1]);
    assert(b1[ai] == idx - 1);
    assert(forall j :: 0 <= j < |oldB| ==> j != ai ==> b1[j] == oldB[j]); // takes a long time



    
    //re-establish invariants with auxilliary lemmas
    permutation_invariant(a, c[..], oldC, idx, i, default, key);
    assert(permutation((a[i..]),(filter(c[..], y => y != default)))); 
    filter_length_invariant(a, c[..], oldC, idx, i, default, key);
    assert(forall j : int :: 0 <= j < |oldB| ==> oldB[j] <= numLeq(j, a[..], key) - 1);
   

    b_position_invariant(a, oldB, b1[..], i, idx, key);
    assert((forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i-1, a[..], key)));
     b_bound_invariant(a, oldB, b1[..], i, idx, key);
    assert(|oldC| == cLen);
   // assume(forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key))); //every filled in element of c is a previously seen elt   
   
      assert(forall j :: 0 <= j < |oldC| ==> oldC[j] != default ==> exists k :: ((i < k < a.Length) && oldC[j] == a[k] && j == position(key(a[k]), k, a[..], key)));

    c_structure_invariant(a, oldB, c[..], oldC, idx, i, default, key);   
    assert (forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((i - 1 < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key))); 
    assert(key(default) < 0);
    stable_invariant_preserved(a, oldB, oldC, c[..], i, a[i], idx, default, key); 
    
    
    
    i := i - 1;
    /*
    //some of the proofs seem to go better if we tell Dafny that the invariant holds explicitly (TODO: see if we need this)
    assert(permutation((a[(i+1)..]),(filter(c[..], y => y != default))));
    assert((forall j :: 0 <= j < b.Length ==> b1[j] == position(j, i, a[..], key)));
    //assert(forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: (i < k < a.Length) && c[j] == a[k]);
    assert (forall j :: 0 <= j < c.Length ==> c[j] != default ==> exists k :: ((i < k < a.Length) && c[j] == a[k] && j == position(key(a[k]), k, a[..], key))); 

    assert(forall j :: 0 <= j < a.Length ==> 0 <= key(a[j]) < b1.Length); //also need for bounds
    assert(forall j : int :: 0 <= j < b1.Length ==> b1[j] <= numLeq(j, a[..], key) - 1); //used for bounds checks
    //technically, this invariant is implied by the next one (by permutation_length), but the proofs are much faster if we include both
    assert(|filter(c[..], y => y != default)| == a.Length - (i + 1)); //ensures that we fill all of c
    assert(forall x : int :: filter(a[(i+1)..], y => key(y) == x) == filter(filter(c[..], y => y != default), y => key(y) == x));
    assert(-1 <= i < a.Length);
    assert(b1.Length == b.Length); //need for bounds 
    */
  }
  /*
  //invariants => postcondition (do in different lemmas so it is faster)
  afterLoopPermutation(a, c);
  assert(permutation(a[..], c[..]));
  afterLoopSorted(a, c);
  assert(sorted(c[..]));
  afterLoopStable(a, c);
  assert(stable(a[..], c[..])); 
  assume(false);*/
} 
/*
//The final algorithm
method countingSort(a: array<int>, k : int) returns (s: array<int>)
requires(0 < k)
requires (forall i: int :: 0 <= i < a.Length ==> 0 <= a[i] < k)
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
    s := constructSortedArray(a, c);
  }
}*/