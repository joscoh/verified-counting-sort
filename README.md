# verified-counting-sort
Verified Counting Sort in Dafny

This repo contains a version of [counting sort](https://en.wikipedia.org/wiki/Counting_sort) implemented and verified in Dafny.

CountingSort.dfy is parameterized by a type G and a function key : G -> int, and it sorts the input array by key. We prove that the output satisfies the following 3 properties:

1. The output is a permutation of the input.
2. The output is sorted by key.
3. The output is stable - ie, the order of elements with the same key is the same in both the input and output.
