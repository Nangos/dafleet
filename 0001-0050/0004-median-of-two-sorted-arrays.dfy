/* https://leetcode.com/problems/median-of-two-sorted-arrays/
Given two sorted arrays nums1 and nums2 of size m and n respectively, return the median of the two sorted arrays.
The overall run time complexity should be O(log (m+n)).

Example 1:
Input: nums1 = [1,3], nums2 = [2]
Output: 2.00000
Explanation: merged array = [1,2,3] and median is 2.
*/


// First things first, let us formulate the problem specifications, starting from `sorted`...
ghost predicate sorted(s: seq<int>) {
  forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

// An abstract function for merging two sorted sequences, thus `opaque`.
//
// The implementation detail is not important here,
// it merely serves as a "witness", so we're sure that our specification is "implementable" (a.k.a. "consistent").
ghost opaque function merge(s1: seq<int>, s2: seq<int>): (s: seq<int>)
  requires sorted(s1) && sorted(s2)
  ensures sorted(s)
  ensures multiset(s) == multiset(s1 + s2)
{
  if s1 == [] then
    s2
  else if s2 == [] then
    s1
  else if s1[0] <= s2[0] then
    predicate_multiset_to_seq(merge(s1[1..], s2), x => s1[0] <= x);
    assert s1 == [s1[0]] + s1[1..];
    [s1[0]] + merge(s1[1..], s2)
  else
    predicate_multiset_to_seq(merge(s1, s2[1..]), x => s2[0] <= x);
    assert s2 == [s2[0]] + s2[1..];
    [s2[0]] + merge(s1, s2[1..])
}
//, where the below "silly" lemma is used:
lemma predicate_multiset_to_seq<T>(s: seq<T>, P: T -> bool)
  requires forall x | x in multiset(s) :: P(x)
  ensures forall i | 0 <= i < |s| :: P(s[i])
{}

// A common way to calculate median for a sorted sequence.
ghost function median(s: seq<int>): real
  requires |s| > 0
  requires sorted(s)
{
  if |s| % 2 == 0 then
    ((s[|s|/2 - 1] + s[|s|/2]) as real) / 2.0
  else
    s[|s|/2] as real
}


// Below are helpful functions for verification:

// We split `s1` into `s1[..i1]` (left) and `s1[i1..]` (right),
// similarly split `s2` into `s2[..i2]`(left) and `s2[i2..]`(right).
// Returns `true` iff any element in the "left part" is smaller than any element in the "right part".
ghost predicate valid_split(s1: seq<int>, s2: seq<int>, i1: int, i2: int)
  requires sorted(s1) && sorted(s2)
{
  && 0 <= i1 <= |s1|
  && 0 <= i2 <= |s2|
  && (forall x, y | (x in s1[..i1] || x in s2[..i2]) && (y in s1[i1..] || y in s2[i2..]) :: x <= y)
}

// The below lemma proves that when we turn a multiset into a sorted array, that sorted array is unique.
lemma lemma_sorted_seq_is_unique(s1: seq<int>, s2: seq<int>)
  requires sorted(s1) && sorted(s2)
  requires multiset(s1) == multiset(s2)
  ensures s1 == s2
{
  if s1 == [] {
    // base case, trivial
  } else {
    // inductive case
    assert s1[0] == s2[0] by {
      assert s1[0] in multiset(s2) && s2[0] in multiset(s1);
    }
    assert s1 == [s1[0]] + s1[1..] && s2 == [s2[0]] + s2[1..];
    assert multiset(s1[1..]) == multiset(s1) - multiset{s1[0]};
    assert multiset(s2[1..]) == multiset(s2) - multiset{s2[0]};
    lemma_sorted_seq_is_unique(s1[1..], s2[1..]);
  }
}

// Proves if a split is "valid", the "left" and "right" parts can be simply "joined together".
lemma lemma_valid_split(s1: seq<int>, s2: seq<int>, i1: int, i2: int)
  requires sorted(s1) && sorted(s2)
  requires valid_split(s1, s2, i1, i2)
  ensures merge(s1, s2) == merge(s1[..i1], s2[..i2]) + merge(s1[i1..], s2[i2..])
{
  var left, right := merge(s1[..i1], s2[..i2]), merge(s1[i1..], s2[i2..]);
  var concat := left + right;
  assert sorted(concat) by {
    forall i, j | 0 <= i < j < |concat| ensures concat[i] <= concat[j] {
      if i < |left| && j >= |left| {
        assert concat[i] in multiset(s1[..i1] + s2[..i2]);
        assert concat[i] in s1[..i1] || concat[i] in s2[..i2];
        assert concat[j] in multiset(s1[i1..] + s2[i2..]);
        assert concat[j] in s1[i1..] || concat[j] in s2[i2..];
      }
    }
  }
  assert multiset(s1 + s2) == multiset(left + right) by {
    assert s1 == s1[..i1] + s1[i1..];
    assert s2 == s2[..i2] + s2[i2..];
  }
  lemma_sorted_seq_is_unique(merge(s1, s2), left + right);
}

// Proves that, given a certain `k`, a "valid split", whose "left side" contains `k` elements, must exist.
lemma lemma_valid_split_exists(s1: seq<int>, s2: seq<int>, k: int, valid_func: int -> bool)
  requires sorted(s1) && sorted(s2)
  requires 0 <= k <= |s1| + |s2|
  requires valid_func == (m => valid_split(s1, s2, m, k - m))
  ensures exists m :: valid_func(m)
{
  if k == 0 {  // base case
    assert valid_func(0);
  } else {  // inductive case
    var valid_func_prev := m => valid_split(s1, s2, m, k - 1 - m);
    lemma_valid_split_exists(s1, s2, k - 1, valid_func_prev);
    var m :| valid_func_prev(m);
    if k - 1 - m == |s2| || (m < |s1| && s1[m] < s2[k - 1 - m]) {
      assert valid_func(m + 1) by { assert s1[m] in s1[m..]; }
    } else {
      assert valid_func(m) by {}
    }
  }
}

// Implies how to find the minimum among two sorted sequences without actually merging them.
lemma lemma_merge_min(s1: seq<int>, s2: seq<int>, x: int)
  requires s1 != [] || s2 != []
  requires sorted(s1) && sorted(s2)
  requires s1 == [] ==> x == s2[0]
  requires s2 == [] ==> x == s1[0]
  requires (s1 != [] && s2 != []) ==> x == if s1[0] < s2[0] then s1[0] else s2[0]
  ensures merge(s1, s2) != [] && x == merge(s1, s2)[0]
{
  var s := merge(s1, s2);
  assert x in multiset(s);
  forall y | y in s ensures x <= y {
    assert y in multiset(s);
  }
  assert s[0] in s;
}

// Similarly, how to find the maximum among two sorted sequences without actually merging them.
lemma lemma_merge_max(s1: seq<int>, s2: seq<int>, x: int)
  requires s1 != [] || s2 != []
  requires sorted(s1) && sorted(s2)
  requires s1 == [] ==> x == last(s2)
  requires s2 == [] ==> x == last(s1)
  requires (s1 != [] && s2 != []) ==> x == if last(s1) > last(s2) then last(s1) else last(s2)
  ensures merge(s1, s2) != [] && x == last(merge(s1, s2))
{
  var s := merge(s1, s2);
  assert x in multiset(s);
  forall y | y in s ensures x >= y {
    assert y in multiset(s);
  }
  assert last(s) in s;
}
//, where
ghost function last<T>(s: seq<T>): T
  requires |s| > 0
{
  s[|s| - 1]
}

// Proves an "obvious" fact:
lemma lemma_merge_commutative(s1: seq<int>, s2: seq<int>)
  requires sorted(s1) && sorted(s2)
  ensures merge(s1, s2) == merge(s2, s1)
{
  lemma_sorted_seq_is_unique(merge(s1, s2), merge(s2, s1));
}


// Now verifying the main algorithm.
//
// It applies binary search on the shorter sequence between the two, for a position splitting both sequences in half.
// The median can then be read at the splitting position.
method {:vcs_split_on_every_assert} findMedianSortedArrays(nums1: seq<int>, nums2: seq<int>) returns (mid: real)
  requires |nums1| + |nums2| > 0
  requires sorted(nums1) && sorted(nums2)
  ensures mid == median(merge(nums1, nums2))
{
  var (longer, shorter) := if |nums1| >= |nums2| then (nums1, nums2) else (nums2, nums1);
  var lo, hi := 0, |shorter| + 1;  // Why "+1"? See discussion for such "binary-search peculiarities"...
  var half_len := (|longer| + |shorter|) / 2;
  // asserting some obvious facts:
  assert |longer| + |shorter| == |nums1| + |nums2|;
  assert |merge(nums1, nums2)| > 0;
  // (Below specifies what is a "valid position". This is required due to how Dafny selects triggers; see discussion)
  ghost var valid_position := p => valid_split(shorter, longer, p, half_len - p);

  // binary-searching where to split `shorter`: 
  while lo < hi
    decreases hi - lo
    invariant 0 <= lo <= hi <= |shorter| + 1
    invariant forall p | p < lo :: !valid_position(p)   /* (A) */
    invariant forall p | p >= hi :: !valid_position(p)  /* (B) */
  {
    var m := (lo + hi) / 2;   // to split `shorter` into [..m] and [m..]
    var n := half_len - m;    // to split `longer` into [..n] and [n..]

    // We want `shorter[m-1] <= longer[n] && longer[n-1] <= shorter[m]` (whenever indices are in-bound).
    // If it does not hold, then `m` and `n` are NOT a right place to split:
    if m - 1 >= 0 && n < |longer| && shorter[m-1] > longer[n] {
      forall p | m <= p <= |shorter| ensures !valid_position(p) {  // eliminating the "right half":
        assert shorter[m-1] in shorter[..p] && longer[n] in longer[(half_len - p)..]; 
        assert !valid_split(shorter, longer, p, half_len - p);
      }
      hi := m;
    } else if n - 1 >= 0 && m < |shorter| && longer[n-1] > shorter[m] {
      forall p | 0 <= p <= m ensures !valid_position(p) {  // eliminating the "left half":
        assert shorter[m] in shorter[p..] && longer[n-1] in longer[..(half_len - p)];
        assert !valid_split(shorter, longer, p, half_len - p);
      }
      lo := m + 1;
    } else {
      assert valid_split(shorter, longer, m, n);  // split position found!
      lemma_valid_split(shorter, longer, m, n);
      lemma_merge_commutative(nums1, nums2);
      var right_min := if n == |longer| || (m < |shorter| && shorter[m] < longer[n]) then shorter[m] else longer[n];
      // we prove that `right_min` is "in the middle":
      assert right_min == merge(nums1, nums2)[|merge(nums1, nums2)| / 2] by {
        lemma_merge_min(shorter[m..], longer[n..], right_min);
      }
      if (|longer| + |shorter|) % 2 == 1 {  // odd length
        return right_min as real;
      } else {  // even length
        var left_max := if n == 0 || (m > 0 && shorter[m-1] > longer[n-1]) then shorter[m-1] else longer[n-1];
        // similarly, we prove that `left_max` is "in the middle":
        assert left_max == merge(nums1, nums2)[|merge(nums1, nums2)| / 2 - 1] by {
          lemma_merge_max(shorter[..m], longer[..n], left_max);
        }
        return ((left_max + right_min) as real) / 2.0;
      }
    }
  }
  // Finally we prove unreachability: as a "valid split" must exist, the loop cannot exit without finding one.
  lemma_valid_split_exists(shorter, longer, half_len, valid_position);
}

/* Discussions
1. This problem "opens up" our minds about "binary search".
  Traditionally, we learn that binary search are used on a "sorted" (or "monotonic") sequence.
  It's NOT as "narrow" as you intuitively imagine.

  In general, the "core" of any binary-search solution is essentially encoded in two invariants (see A and B above).
  While (A) asserts that every element on the left of `lo` satisfies something,
  (B) asserts that every element on the right of `hi` satisfies another thing (either the same thing or not).
  As long as you "sniff such hints", consider binary search!

2. Be careful when handling binary search.
  In this problem, the search range is from `0` to `|shorter|`, inclusive. (Error-prone!!!)
  If we follow Python's or Dafny's convention of array-slicing notation (left-inclusive but right-exclusive),
  the "search interval" should be written as `0 .. |shorter| + 1`.
  That `+ 1` at the end might be carelessly forgotten.

  Typically, when we search in an array `s`, we are really searching from index `0` to index `|s|-1`,
  which is written as `0 .. |s|`, that's why no `+1` is present. Don't let impressions mislead you.

3. Binary search can also be coded in a "symmetric style", where both `lo` and `hi` are "inclusive".
  Don't mix up different styles while you code. I will show it below.

4. Dafny triggers are weird...
  It seems if a function has too many parameters, Dafny won't let it be a trigger (??)
  One of the most effective solutions is to use a "lambda" to remove irrelevant parameters,
  for example, wrapping `valid_split` (4 parameters, no trigger) in `valid_position` (1 parameter, triggered).
*/


// Below I'll show a "cleaner" way to code the solution.

// We model the "extended integer" type, containing "positive infinity" and "negative infinity".
// It is actually built-in in many languages (e.g. Python), or hackable (e.g. `INT_MAX := 0x7fffffff`),
// so these "helper functions" below are NOT needed in reality.
datatype ex_int = PosInf | NegInf | Int(val: int)
{
  predicate lt(that: ex_int) {  // less-than operator
    match this {
      case NegInf => !that.NegInf?
      case Int(val) => !that.NegInf? && (that.PosInf? || this.val < that.val)
      case PosInf => false
    }
  }
}

function max(a: ex_int, b: ex_int): ex_int {
  if a.lt(b) then b else a
}
function min(a: ex_int, b: ex_int): ex_int {
  if a.lt(b) then a else b
}

// Essentially the same solution, just "less dirty" in appearance.
// Notice how "symmetric" the code looks (sans assertions, of course...)
method {:vcs_split_on_every_assert} findMedianSortedArrays'(nums1: seq<int>, nums2: seq<int>) returns (mid: real)
  requires |nums1| + |nums2| > 0
  requires sorted(nums1) && sorted(nums2)
  ensures mid == median(merge(nums1, nums2))
{
  var (longer, shorter) := if |nums1| >= |nums2| then (nums1, nums2) else (nums2, nums1);
  var lo, hi := 0, |shorter|;
  var half_len := (|longer| + |shorter|) / 2;

  assert |longer| + |shorter| == |nums1| + |nums2|;
  assert |merge(nums1, nums2)| > 0;
  ghost var valid_position := p => valid_split(shorter, longer, p, half_len - p);

  while lo <= hi
    decreases hi - lo
    invariant 0 <= lo && lo <= hi + 1 && hi <= |shorter|
    invariant forall p | p < lo :: !valid_position(p)
    invariant forall p | p > hi :: !valid_position(p)
  {
    var m := (lo + hi) / 2;
    var n := half_len - m;

    var shorter_left_max := if m-1 >= 0 then Int(shorter[m-1]) else NegInf;
    var shorter_right_min := if m < |shorter| then Int(shorter[m]) else PosInf;
    var longer_left_max := if n-1 >= 0 then Int(longer[n-1]) else NegInf;
    var longer_right_min := if n < |longer| then Int(longer[n]) else PosInf;

    if longer_right_min.lt(shorter_left_max) {
      forall p | m <= p <= |shorter| ensures !valid_position(p) {
        assert shorter[m-1] in shorter[..p] && longer[n] in longer[(half_len - p)..]; 
        assert shorter_left_max.val == shorter[m-1] && longer_right_min.val == longer[n];
        assert !valid_split(shorter, longer, p, half_len - p);
      }
      hi := m - 1;
    } else if shorter_right_min.lt(longer_left_max) {
      forall p | 0 <= p <= m ensures !valid_position(p) {
        assert shorter[m] in shorter[p..] && longer[n-1] in longer[..(half_len - p)];
        assert !valid_split(shorter, longer, p, half_len - p);
      }
      lo := m + 1;
    } else {
      assert valid_split(shorter, longer, m, n);
      lemma_valid_split(shorter, longer, m, n);
      lemma_merge_commutative(nums1, nums2);

      var right_min := min(shorter_right_min, longer_right_min).val;
      assert right_min == merge(nums1, nums2)[|merge(nums1, nums2)| / 2] by {
        lemma_merge_min(shorter[m..], longer[n..], right_min);
      }
      if (|longer| + |shorter|) % 2 == 1 {
        return right_min as real;
      } else {
        var left_max := max(shorter_left_max, longer_left_max).val;
        assert left_max == merge(nums1, nums2)[|merge(nums1, nums2)| / 2 - 1] by {
          lemma_merge_max(shorter[..m], longer[..n], left_max);
        }
        return ((left_max + right_min) as real) / 2.0;
      }
    } 
  }
  lemma_valid_split_exists(shorter, longer, half_len, valid_position);
}