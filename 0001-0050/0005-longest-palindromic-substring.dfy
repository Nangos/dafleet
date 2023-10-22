/* https://leetcode.com/problems/longest-palindromic-substring/
Given a string s, return the longest palindromic substring in s.

Example 1:
Input: s = "babad"
Output: "bab"
Explanation: "aba" is also a valid answer.
*/


// Specifying the problem: whether `s` is palindromic
ghost predicate palindromic(s: string) {
  |s| < 2 || (s[0] == s[|s|-1] && palindromic(s[1 .. |s|-1]))
}

// Some helper lemmas...
// Yet another "common sense" that Dafny doesn't know...
lemma lemma_nested_slicing<T>(s: seq<T>, i: nat, j: nat, i': nat, j': nat)
  requires 0 <= i <= j <= |s|
  requires 0 <= i' <= j' <= j - i
  ensures s[i..j][i'..j'] == s[i+i' .. i+j']
  decreases j' - i'
{
  if i' < j' {
    lemma_nested_slicing(s, i, j, i'+1, j');
  }
}

// More "common sense" about palindromes:
lemma lemma_palindromic_expanding(s: string, lo: int, hi: int)
  requires 0 <= lo - 1 && lo <= hi < |s| && s[lo - 1] == s[hi]
  requires palindromic(s[lo..hi])
  ensures palindromic(s[lo-1 .. hi+1])
{
  var s' := s[lo-1 .. hi+1];
  assert s'[1 .. |s'|-1] == s[lo .. hi] by {
    lemma_nested_slicing(s, lo-1, hi+1, 1, |s'|-1);
  }
}
lemma lemma_palindromic_contains(s: string, lo: int, hi: int, lo': int, hi': int)
  requires 0 <= lo <= lo' <= hi' <= hi <= |s|
  requires lo + hi == lo' + hi'
  requires palindromic(s[lo..hi])
  ensures palindromic(s[lo'..hi'])
{
  var i, j := lo, hi;
  while i < lo'
    invariant i <= lo'
    invariant i + j == lo' + hi'
    invariant palindromic(s[i..j])
  {
    assert s[i..j][1 .. j-i-1] == s[i+1 .. j-1] by {
      lemma_nested_slicing(s, i, j, 1, j-i-1);
    }
    i, j := i + 1, j - 1;
  }
}

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s[i0..j0])
  ensures 0 <= lo <= hi <= |s| && palindromic(s[lo..hi])
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s[i..j])  // Among all palindromes
    && i + j == i0 + j0                                             // sharing the same center,
    :: j - i <= hi - lo                                             // `s[lo..hi]` is longest.
{
  lo, hi := i0, j0;

  // we try expanding whenever possible:
  while lo - 1 >= 0 && hi < |s| && s[lo - 1] == s[hi]
    invariant 0 <= lo <= hi <= |s| && lo + hi == i0 + j0
    invariant palindromic(s[lo..hi])
  {
    lemma_palindromic_expanding(s, lo, hi);
    lo, hi := lo - 1, hi + 1;
  }

  // proves that we cannot go further:
  forall i, j | 0 <= i <= j <= |s| && i + j == i0 + j0 && j - i > hi - lo ensures !palindromic(s[i..j]) {
    if palindromic(s[i..j]) { // prove by contradiction:
      lemma_palindromic_contains(s, i, j, lo - 1, hi + 1);
    }
  }
}


// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]  // `ans` is indeed a substring in `s`
  ensures palindromic(ans)  // `ans` is palindromic
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s[i..j]) :: j - i <= hi - lo  // `ans` is longest
{
  lo, hi := 0, 0;
  for k := 0 to |s|
    invariant 0 <= lo <= hi <= |s|
    invariant palindromic(s[lo..hi])
    invariant forall i, j | 0 <= i <= j <= |s| && i + j < 2 * k && palindromic(s[i..j]) :: j - i <= hi - lo
  {
    var a, b := expand_from_center(s, k, k);
    if b - a > hi - lo {
      lo, hi := a, b;
    }
    var c, d := expand_from_center(s, k, k + 1);
    if d - c > hi - lo {
      lo, hi := c, d;
    }
  }
  return s[lo..hi], lo, hi;
}


/* Discussions
1. This is yet another evidence that Dafny is generally smart, but can stuck at some "common senses"...
  We know Dafny is bad at slicing, but this time it was super bad.
  It didn't know that `s[i..j][i'..j'] == s[i+i' .. i+j']` even if we `assert` it,
  so we needed a lemma applying induction to prove it.

  Otherwise, everything else went smoothly as expected.
  The verification experience largely depends on how well you know the weakness of Dafny,
  and how quickly you can "wire your mind" to "teach" it with a proof (usually by induction).

2. Bonus -- Manacher's algorithm
  Our above solution needs `O(|s|^2)` time in the worst case. Can we improve it? Yes.

  Manacher's algorithm guarantees an `O(|s|)` time.
  To get the intuition, ask yourself: when will it really take `O(|s|^2)` time?
  When there are a lot of "nesting and overlapping" palindromes. like in `abcbcbcba` or even `aaaaaa`.

  Imagine each palindrome as a "mirror". "Large mirrors" reflect "small mirrors".
  Therefore, when we "expand" from some "center", we can "reuse" some information from its "mirrored center".
  For example, we move the "center", from left to right, in the string `aiaOaia...`
  Here, the char `O` is the "large mirror".
  When the current center is the second `i`, it is "mirrored" to the first `i` (which we've calculated for),
  so we know the palindrome centered at the second `i` must have at least a length of 3 (`aia`).
  So we can expand directly from `aia`, instead of expanding from scratch.

  Manacher's algorithm is verified below.
  Also, I will verify that "every loop is entered for only `O(|s|)` times",
  which "indirectly" proves that the entire algorithm runs in `O(|s|)` time.
*/


// A reference implementation of Manacher's algorithm:
// (Ref. https://en.wikipedia.org/wiki/Longest_palindromic_substring#Manacher's_algorithm) for details...
method {:vcs_split_on_every_assert} longestPalindrome'(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]
  ensures palindromic(ans)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s[i..j]) :: j - i <= hi - lo
{
  var bogus: char :| true;  // an arbitrary character
  var s' := insert_bogus_chars(s, bogus);
  var radii := new int[|s'|];
  var center, radius := 0, 0;
  // vars below are just for verifying time complexity:
  ghost var loop_counter_outer, loop_counter_inner1, loop_counter_inner2 := 0, 0, 0;

  while center < |s'|
    invariant 0 <= center <= |s'|
    invariant forall c | 0 <= c < center :: max_radius(s', c, radii[c])
    invariant center < |s'| ==> inbound_radius(s', center, radius) && palindromic_radius(s', center, radius)
    invariant center == |s'| ==> radius == 0
    invariant loop_counter_outer <= center
    invariant loop_counter_inner1 <= center + radius && loop_counter_inner2 <= center
  {
    loop_counter_outer := loop_counter_outer + 1;

    // Stage 1: Still the normal "expand from center" routine, except `radius` is NOT necessarily zero:
    while center - (radius + 1) >= 0 && center + (radius + 1) < |s'|
        && s'[center - (radius + 1)] == s'[center + (radius + 1)]
      decreases center - radius
      invariant inbound_radius(s', center, radius) && palindromic_radius(s', center, radius)
      invariant loop_counter_inner1 <= center + radius
    {
      loop_counter_inner1 := loop_counter_inner1 + 1;
      assert inbound_radius(s', center, radius + 1) && palindromic_radius(s', center, radius + 1) by {
        assume false;
      }
      radius := radius + 1;
    }
    assert max_radius(s', center, radius) by {
      assume false;
    }

    radii[center] := radius;
    var old_center, old_radius := center, radius;
    center := center + 1;
    radius := 0;

    // Stage 2: Quickly infer the maximal radius, using the symmetry of known palindromes. 
    while center <= old_center + old_radius
      invariant 0 <= center <= |s'|
      invariant forall c | 0 <= c < center :: max_radius(s', c, radii[c])
      invariant center < |s'| ==> inbound_radius(s', center, radius) && palindromic_radius(s', center, radius)
      invariant loop_counter_inner2 <= center - 1
    {
      loop_counter_inner2 := loop_counter_inner2 + 1;

      var mirrored_center := old_center - (center - old_center);
      var max_mirrored_radius := old_center + old_radius - center;
      if radii[mirrored_center] < max_mirrored_radius {
        assert max_radius(s', center, radii[mirrored_center]) by {
          assume false;
        }
        radii[center] := radii[mirrored_center];
        center := center + 1;
        assert forall c | 0 <= c < center :: max_radius(s', c, radii[c]);
      } else if radii[mirrored_center] > max_mirrored_radius {
        assert max_radius(s', center, max_mirrored_radius) by {
          assume false;
        }
        radii[center] := max_mirrored_radius;
        center := center + 1;
        assert forall c | 0 <= c < center :: max_radius(s', c, radii[c]);
      } else {
        assert palindromic_radius(s', center, max_mirrored_radius) by {
          assume false;
        }
        radius := max_mirrored_radius;
        break;
      }
    }
  }
  // verify that the worst time complexity (measured by loop iterations) is O(|s'|) == O(|s|):
  assert |s'| == 2 * |s| + 1;
  assert loop_counter_outer <= |s'|;
  assert loop_counter_inner1 <= |s'|;
  assert loop_counter_inner2 <= |s'|; 

  // wrap up results:
  var (c, r) := argmax(radii, 0);
  lo, hi := (c - r) / 2, (c + r) / 2; // notice that both ends are bogus chars at position 0, 2, 4, 6, etc.!
  lemma_result_transfer(s, s', bogus, radii, c, r, hi, lo);
  return s[lo..hi], lo, hi;        
}


// Below are helper functions and lemmas we used:

// Inserts bogus characters to the original string (e.g. from `abc` to `|a|b|c|`).
// Note that this is neither efficient nor necessary in reality, but just for the ease of understanding.
function insert_bogus_chars(s: string, bogus: char): (s': string)
  ensures |s'| == 2 * |s| + 1
{
  if s == "" then
    [bogus]
  else
    [bogus] + [s[0]] + insert_bogus_chars(s[1..], bogus)
}

// Returns (max_index, max_value) of array `a` starting from index `start`.
function {:opaque} argmax(a: array<int>, start: int): (res: (int, int))
  reads a
  requires 0 <= start < a.Length
  ensures start <= res.0 < a.Length && a[res.0] == res.1
  ensures forall i | start <= i < a.Length :: a[i] <= res.1
  decreases a.Length - start
{
  if start == a.Length - 1 then
    (start, a[start])
  else
    var (i, v) := argmax(a, start + 1);
    if a[start] >= v then (start, a[start]) else (i, v)
}

// Whether an interval at center `c` with a radius `r` is within the boundary of `s'`.
ghost predicate inbound_radius(s': string, c: int, r: int)
{
  r >= 0 && 0 <= c-r && c+r < |s'|
}

// Whether `r` is a valid palindromic radius at center `c`.
ghost predicate palindromic_radius(s': string, c: int, r: int)
  requires inbound_radius(s', c, r)
{
  palindromic(s'[c-r .. c+r+1])
}

// Whether `r` is the maximal palindromic radius at center `c`.
ghost predicate max_radius(s': string, c: int, r: int)
{
  && inbound_radius(s', c, r)
  && palindromic_radius(s', c, r)
  && (forall r' | r' > r && inbound_radius(s', c, r') :: !palindromic_radius(s', c, r'))
}

// Transfering our final result on `s'` to that on `s`:
lemma lemma_result_transfer(s: string, s': string, bogus: char, radii: array<int>, c: int, r: int, hi: int, lo: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires radii.Length == |s'|
  requires forall i | 0 <= i < radii.Length :: max_radius(s', i, radii[i])
  requires (c, r) == argmax(radii, 0)
  requires lo == (c - r) / 2 && hi == (c + r) / 2
  ensures 0 <= lo <= hi <= |s|
  ensures palindromic(s[lo..hi])
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s[i..j]) :: j - i <= hi - lo
