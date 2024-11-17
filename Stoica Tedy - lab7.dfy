function add(x : int, y : int) : int
{
    x + y
}

// method Main() {
//     var y := add(2, 4);
//     print "Sum is ", y;
// }

method Inc(x: int) returns (y: int) {
    y := x + 1;
}

method IncPrim(x: int) returns (y: int)
    requires (x >= 3)
    ensures (y >= 4)
{
    y := x + 1;
}

predicate gcdpredicate(x: int, y: int, result: int)
{
    result > 0 && 
    x % result == 0 && 
    y % result == 0 && 
    forall z: int :: (z > result && z < x && z < y) ==> (x % z != 0 || y % z != 0)
}

method GCD(x: int, y: int) returns (result: int)
    requires (x > 0 && y > 0)
    ensures gcdpredicate(x, y, result)
{
    var a := x;
    var b := y;
    result := x % y;
    a := y;
    b := result;
    while b > 0 
        invariant 0 <= result <= b
        invariant a - b > 0
        decreases b
    {
        result := a % b;
        a := b;
        b := result;
    }
}


method m4(n: int) returns (s: int)
    requires n >= 0
    ensures s == n * (n + 1) * (2 * n + 1) / 6
{
    var i : int;
    var k : int;
    s := 0;
    k := 1;
    i := 1;
    while (i <= n)
        invariant 0 <= i <= n+1
        invariant k == i * i
        invariant s == i * (i - 1) * (2 * i - 1) / 6
        decreases n - i
    {
        s := s + k;
        k := k + 2 * i + 1;
        i := i+1;
    }
}

// s = 0, k = 1, i = 1
// s = 1, k = 3, i = 2
// s = 4, k = 8, i = 3
// s = 12, k = 15, i = 4
// s = 27, k = 24, i = 5
// s = 51, k = 35, i = 6

predicate maxTwoElementsInArr(a : seq<int>, m : int, n : int)
{
    exists i :: ((0 <= i < |a| && a[i] == m) && (forall k :: (0 <= k < |a|) ==> (a[k] <= m)) && 
    (exists j :: (0 <= j < |a| && a[j] == m) && (forall k :: (0 <= k < |a| && i != j) ==> (a[k] <= n))))
}

method maxtwo(a : seq<int>) returns (x: int, y: int)
    requires |a| >= 2
    ensures maxTwoElementsInArr(a, x, y)
{
    var i : int;
    var primulpos : int;
    i := 0;
    x := a[0];
    primulpos := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant (forall k :: (0 <= k < i) ==> (a[k] <= x))
        invariant (exists j :: (0 <= j < |a| && a[j] == x))
        decreases |a| - i
    {
        if a[i] > x {
            x := a[i];
            primulpos := i;
        }
        i := i + 1;
    }
    i := 0;
    y := a[1];
    while i < |a|
        invariant 0 <= i <= |a|
        invariant (forall k :: (0 <= k < i && primulpos != k) ==> (a[k] <= y))
        decreases |a| - i
    {
        if a[i] > y && i != primulpos {
            y := a[i];
        }
        i := i + 1;
    }
}

method Main() {
    var a : seq<int>;
    a := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    var x : int;
    var y : int;
    x, y := maxtwo(a);
    print "Max two elements are ", x, " and ", y;
}