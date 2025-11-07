method sumn(n: Int): Int
    requires n >= 0
{
    var acc: Int := 0;
    var i: Int := 0;
    loop 
        // Error: Invariant may not be preserved
        invariant i <= n 
        // The correct one
        // invariant 0 <= i && i <= n + 1
        // invariant acc == i * (i - 1) / 2
    {
        i <= n =>
            acc := acc + i;
            i := i + 1
    };   
    return acc
}