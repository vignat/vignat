//permalink: http://rise4fun.com/Dafny/OIU
class zaMap {
  var busybits :array<bool>;
  var keys : array<int>;
  var values : array<int>;
  
  predicate wellformed ()
    reads busybits, keys, values, this
  {
    busybits != null && keys != null && values != null &&
    keys != values &&
    busybits.Length == keys.Length &&
    keys.Length == values.Length
  }
  
  predicate nodups()
    requires wellformed ()
    reads busybits, keys, values, this
  {
    forall i, j :: 0 <= i < j < busybits.Length && busybits[i] && busybits[j] ==> keys[i] != keys[j]
  }
  
  predicate contains(k : int)
    requires wellformed()
    reads busybits, keys, values, this
  {
    exists i :: 0 <= i < busybits.Length && busybits[i] && keys[i] == k
  }
  
  predicate mapsto(k : int, v : int)
    requires wellformed()
    reads busybits, keys, values, this
  {
    exists i :: 0 <= i < busybits.Length && busybits[i] && keys[i] == k && values[i] == v
  }
  
  predicate empty()
    requires busybits != null
    reads busybits, this
  {
    true !in busybits[..]
  }
  
  predicate full()
    requires busybits != null
    reads busybits, this
  {
    false !in busybits[..]
  }
  
  method findEmpty() returns (ei : int)
    requires wellformed()
    ensures ei < 0 <==> full()
    ensures ei >= 0 <==> !full() && ei < busybits.Length && busybits[ei] == false
  {
    ei := 0;
    while (ei < busybits.Length)
      invariant ei <= busybits.Length
      invariant false !in busybits[..ei]
    {
      if (!busybits[ei]) { return ;}
      ei := ei + 1;
    } 
    ei := -1;
  }
  
  method findKey(k : int) returns (ki : int)
    requires wellformed()
    ensures ki < 0 <==> !contains(k)
    ensures ki >= 0 <==> !empty() && contains(k) &&
                         0 <= ki < busybits.Length && busybits[ki] && keys[ki] == k
  {
    ki := 0;
    while (ki < busybits.Length)
      invariant ki <= keys.Length
      invariant forall i :: 0 <= i < ki ==> !busybits[i] || keys[i] != k
    {
      if (busybits[ki] && keys[ki] == k) { return; }
      ki := ki + 1;
    }
    ki := -1;
  }
  
  method size() returns (s : int)
    requires wellformed()
    ensures 0 <= s <= busybits.Length
    ensures s == 0 <==> empty()
    ensures (s == busybits.Length) <==> full()
  {
    var i := 0;
    s := 0;
    while ( i < busybits.Length)
    invariant 0 <= s <= i
    invariant 0 <= i <= busybits.Length
    invariant s == 0 <==> true !in busybits[..i]
    invariant s == i <==> false !in busybits[..i]
    {
      if (busybits[i]) {s := s + 1;}
      i := i + 1;
    }
    assert s <= i;
    assert i == busybits.Length;
  }
  
  method get(k : int) returns (val : int, present : bool)
    requires wellformed()
    ensures !present ==> !contains(k)
    ensures present ==> contains(k) && mapsto(k, val) 
  {
    var i := findKey(k);
    if (i < 0)
    {
      present := false;
      return;
    }
    present := true;
    val := values[i];
  }
  
  method put(k : int, v : int) returns (success : bool)
    requires wellformed()
    modifies busybits, keys, values
    ensures !success ==> full()
    ensures success ==> mapsto(k, v)
  {
    var i := findEmpty();
    if (i < 0)
    {
      success := false;
      return;
    }
    assert !busybits[i];
    busybits[i] := true;
    keys[i] := k;
    values[i] := v;
    success := true;
  }
  
  method erase(k : int) returns (success : bool)
    requires wellformed()
    requires nodups()
    modifies busybits
    ensures !success ==> !contains(k)
    ensures success ==> !contains(k)
  {
    var i := findKey(k);
    if (i < 0)
    {
      success := false;
      return;
    }
    busybits[i] := false;
    success := true;
  }
  
  constructor (m : zaMap)
    requires m != null && m.wellformed()
    //ensures wellformed()
    ensures busybits != null && m.busybits[..] == busybits[..]
    ensures keys != null && m.keys[..] == keys[..]
    ensures values != null && m.values[..] == values[..]
    modifies this
  {
    busybits := new bool[m.busybits.Length];
    keys := new int[m.busybits.Length];
    values := new int[m.busybits.Length];
    assert busybits != null;
    var i := 0;
    while (i < m.busybits.Length)
      invariant m.busybits[..i] == busybits[..i]
      invariant m.keys[..i] == keys[..i]
      invariant m.values[..i] == values[..i]
    {
      busybits[i] := m.busybits[i];
      keys[i] := m.keys[i];
      values[i] := m.values[i];
    }
  }
}

method testGetPut1(m : zaMap, k : int, v : int) 
  requires m!=null && m.wellformed()
  requires !m.full()
{
  var m2 := new zaMap(m);
  var a;
  a := m2.put(k, v);
  var val, present;
  val, present := m2.get(k);
  assert (val == v);
}


method Main() {
  print "hello, Dafny\n";
}
