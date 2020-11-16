method example(a: array<int>, b: array<int>) returns (c: int) 
modifies b
requires(0 < a.Length)
requires(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)
{
    var i := 0;
    while(i < a.Length)
    invariant(0 <= i <= a.Length)
    {
        assert(0 <= i < a.Length);
        assert(0 <= a[i] < b.Length);
        b[a[i]] := b[a[i]] + 1;
        i := i + 1;
    }
    return 0;
}


// method example(a: array<int>, b: array<int>) returns (c: int) 
// modifies b
// requires(a.Length > 0)
// requires(forall i : int :: 0 <= i < a.Length ==> 0 <= a[i] < b.Length)
// {
//     var i := a.Length - 1;
//     while(i >= 0)
//     invariant(0 <= i < a.Length)
//     {
//         assert(0 <= i < a.Length);
//         assert(0 <= a[i] < b.Length);
//         b[a[i]] := b[a[i]] + 1;
//     }
//     return 0;
// }
 