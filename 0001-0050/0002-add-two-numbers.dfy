/* https://leetcode.com/problems/add-two-numbers/
Given an array of integers nums and an integer target, return indices of the two numbers such that they add up to target.
You are given two non-empty linked lists representing two non-negative integers.
The digits are stored in reverse order, and each of their nodes contains a single digit
Add the two numbers and return the sum as a linked list.

You may assume the two numbers do not contain any leading zero, except the number 0 itself.

Example 1:
Input: l1 = [2,4,3], l2 = [5,6,4]
Output: [7,0,8]
Explanation: 342 + 465 = 807.
*/


// First things first, I like to encode the most apparent constraints into types, for an intuitive look.
// Here we define a digit to be exclusively 0-9. 
type digit = x: int | 0 <= x <= 9 witness 0

// In the following, we'll work out the specifications...
// Firstly, we define when a sequence of digits is "valid":
ghost predicate valid_seq(l: seq<digit>) {
  && |l| > 0                      // non-empty
  && (l == [0] || l[|l|-1] != 0)  // no leading zero except the number 0
}

// Then we specify which integer is encoded by a given sequence of digits.
// We do it recursively from the lower digits to the higher ones.
ghost function {:opaque} value_of(l: seq<digit>): int {
  if l == [] then
    0
  else
    var hi := |l| - 1;
    value_of(l[..hi]) + pow10(hi) * l[hi]
}
//, where:
ghost function {:opaque} pow10(n: nat): int {
  if n == 0 then 1 else 10 * pow10(n - 1)
}

// BTW, a couple of "inline" functions:
ghost function min(x: int, y: int): (z: int) {
  if x < y then x else y
}
ghost function max(x: int, y: int): (z: int) {
  if x < y then y else x
}

// For verification purposes, we need a couple more preparations...
//
// Now we recursively define the "partial sum" of two sequences `l1` and `l2`,
// which is another sequence (plus a `carry`) that equals the sum of their lowest `n` digits.
ghost function {:opaque} partial_sum(l1: seq<digit>, l2: seq<digit>, n: nat): (sum: (seq<digit>, digit))
  ensures |sum.0| == n
  ensures 0 <= sum.1 <= 1
  ensures value_of(sum.0 + [sum.1]) == value_of(l1[..min(n, |l1|)]) + value_of(l2[..min(n, |l2|)])
{
  if n == 0 then
    reveal value_of();
    ([], 0)
  else
    var (rem, carry) := partial_sum(l1, l2, n - 1);
    var x1 := if n - 1 < |l1| then (l1[n - 1]) else 0;
    var x2 := if n - 1 < |l2| then (l2[n - 1]) else 0;
    var y := x1 + x2 + carry;
    var (rem', carry') := if y < 10 then (y, 0) else (y - 10, 1);

    // Such a lengthy chain of rewriting! Just skim it, if it looks boring to you...
    calc {
      value_of(rem + [rem'] + [carry']);
    == { reveal value_of(), pow10(); }
      value_of(rem) + pow10(|rem|) * rem' + pow10(|rem|) * 10 * carry';
    ==
      value_of(rem) + pow10(|rem|) * (rem' + 10 * carry');
    ==
      value_of(rem) + pow10(|rem|) * (x1 + x2 + carry);
    ==
      value_of(rem) + pow10(|rem|) * carry + pow10(|rem|) * (x1 + x2);
    == { reveal value_of(); }
      value_of(rem + [carry]) + pow10(|rem|) * (x1 + x2);
    ==
      value_of(l1[..min(n-1, |l1|)]) + value_of(l2[..min(n-1, |l2|)]) + pow10(n-1) * (x1 + x2);
    ==
      (value_of(l1[..min(n-1, |l1|)]) + pow10(n-1) * x1) + (value_of(l2[..min(n-1, |l2|)]) + pow10(n-1) * x2);
    == { reveal value_of(); assert n - 1 < |l1| ==> l1[..n][..n-1] == l1[..n-1]; }
      value_of(l1[..min(n, |l1|)]) + (value_of(l2[..min(n-1, |l2|)]) + pow10(n-1) * x2);
    == { reveal value_of(); assert n - 1 < |l2| ==> l2[..n][..n-1] == l2[..n-1]; }
      value_of(l1[..min(n, |l1|)]) + value_of(l2[..min(n, |l2|)]);
    }
    (rem + [rem'], carry')
}

// We'd also like to make sure the final result is a valid sequence as `l1` and `l2` are,
// which we formulate as the following lemma:
lemma lemma_validity_of_final_sum(l1: seq<digit>, l2: seq<digit>, rem: seq<digit>, carry: digit)
  requires valid_seq(l1) && valid_seq(l2)
  requires (rem, carry) == partial_sum(l1, l2, max(|l1|, |l2|))
  ensures carry > 0 || valid_seq(rem)
{
  reveal partial_sum();
  // Surprise! Dafny did all other magics.
}


// Finally we're ready to verify our main method!!
// For verification simplicity, we pretend as if:
// - `seq` were (loop-less) linked list
method {:vcs_split_on_every_assert} addTwoNumbers(l1: seq<digit>, l2: seq<digit>) returns (sum: seq<digit>)
  requires valid_seq(l1) && valid_seq(l2)
  ensures valid_seq(sum)
  ensures value_of(sum) == value_of(l1) + value_of(l2)
{
  var p1, p2 := 0, 0;  // initialize pointers for `l1` and `l2`
  var carry := 0;
  sum := [];
  assert (sum, carry) == partial_sum(l1, l2, |sum|) by { reveal partial_sum(); }

  // We simply perform primary-school addition in a loop.
  // We're just "simulating" linked lists, otherwise would be something like `p.next == null`...
  while p1 < |l1| || p2 < |l2|
    invariant 0 <= p1 <= |l1| && 0 <= p2 <= |l2|
    invariant (p1 < |l1| && p2 < |l2|) ==> p1 == p2
    invariant (p1 == |l1| && p2 < |l2|) ==> p1 <= p2
    invariant (p1 < |l1| && p2 == |l2|) ==> p1 >= p2
    invariant |sum| == max(p1, p2)
    invariant 0 <= carry <= 1
    invariant (sum, carry) == partial_sum(l1, l2, |sum|)   /* (A): a "primary" invariant */
    decreases |l1| - p1, |l2| - p2
  {
    // "atomically" read a digit and proceed the pointer (this is less error-prone):
    var (x1, p1') := if p1 < |l1| then (l1[p1] as int, p1 + 1) else (0, p1);
    var (x2, p2') := if p2 < |l2| then (l2[p2] as int, p2 + 1) else (0, p2);

    // process the carry:
    var y := x1 + x2 + carry;
    var (carry', rem) := if y < 10 then (0, y) else (1, (y - 10));
    var sum' := sum + [rem as digit];  // would be like `tail.next := new ListNode(y); tail := tail.next;`

    // update out-of-loop variables: 
    assert (sum', carry') == partial_sum(l1, l2, |sum'|) by { reveal partial_sum(); }
    p1, p2, carry, sum := p1', p2', carry', sum';
  }

  // let's remind Dafny what we've achieved at the end of the loop:
  assert l1[..|l1|] == l1 && l2[..|l2|] == l2;
  assert (sum, carry) == partial_sum(l1, l2, max(|l1|, |l2|));
  assert value_of(sum + [carry]) == value_of(l1) + value_of(l2);

  if carry == 1 { // append `carry` to the final result:
    sum := sum + [carry];
    // the final sum must be valid in this case, since `carry` cannot be a leading zero
  } else {
    // now that `carry == 0`, we already have `sum` as the final result:
    assert value_of(sum) == value_of(sum + [carry]) by { reveal value_of(); }
    lemma_validity_of_final_sum(l1, l2, sum, carry);
  }
}


/* Discussions (Part I)
1. The strengths & weakness of Dafny
  As shown in this problem, Dafny is sometimes surprisingly good at proving certain things.
  For example, `lemma_validity_of_final_sum` is almost automatically proved.
  But at other times, it needs a lot of "human intervention", adding a lot of (maybe obvious) assertions.

  From my experience so far, Dafny tends to be good at proof-by-case and recursions, needing minimal assistance.
  It's not so good at rewriting math formulas and sequence operations though, would need "hints" now and then.

2. The trick of "opaque functions"
  Sometimes it helps to mark a function `{:opaque}`, especially when it's recursive.
  I found it particularly useful when rewriting formulas, as it narrows down Dafny's search space.
  Whenever you need to expand the function definition, just `reveal` it temporarily at a particular step!

3. Finding loop invariants is tricky
  As a rule of thumb, you have to consider every out-of-loop variable. They record the "state of progress".
  Unless you're a genius, don't expect to find all invariants at once.
  Instead, start with one or two "primary" invariants necessary to prove the post-condition (e.g. formula A),
  and then gradually figure out the others needed to prove the "primary" ones.

4. Faster solution exploiting the structure of linked list!
  When the two linked lists differ a lot in length, there is a simple trick to make the addition faster,
  decreasing the (average) time complexity from `O(max(|l1|, |l2|))` to `O(min(|l1|, |l2|))`.
  If you still don't realize what it is, see the method `addTwoNumbers'` below.

  P.S. This trick is only safe if the linked lists are "read-only after construction" or a.k.a. "immutable".
*/

// An optimizated solution that works better when `|l1|` and `|l2|` differs a lot:
method {:vcs_split_on_every_assert} addTwoNumbers'(l1: seq<digit>, l2: seq<digit>) returns (sum: seq<digit>)
  requires valid_seq(l1) && valid_seq(l2)
  ensures valid_seq(sum)
  ensures value_of(sum) == value_of(l1) + value_of(l2)
{
  var p1, p2 := 0, 0;
  var carry := 0;
  sum := [];
  assert (sum, carry) == partial_sum(l1, l2, |sum|) by { reveal partial_sum(); }

  while p1 < |l1| || p2 < |l2|
    invariant 0 <= p1 <= |l1| && 0 <= p2 <= |l2|
    invariant (p1 < |l1| && p2 < |l2|) ==> p1 == p2
    invariant (p1 == |l1| && p2 < |l2|) ==> p1 <= p2
    invariant (p1 < |l1| && p2 == |l2|) ==> p1 >= p2
    invariant |sum| == max(p1, p2)
    invariant 0 <= carry <= 1
    invariant (sum, carry) == partial_sum(l1, l2, |sum|)
    decreases |l1| - p1, |l2| - p2
  {
    // early-termination conditions:
    if p2 == |l2| && carry == 0 {
      lemma_quick_sum(l1, l2, sum);
      assert (sum + l1[p1..], 0) == partial_sum(l1, l2, max(|l1|, |l2|));
      sum := sum + l1[p1..];  // in linked-list reality, it's like `tail.next := p1`;
      break;
    }
    if p1 == |l1| && carry == 0 {
      lemma_partial_sum_commutative(l1, l2, |sum|);
      lemma_quick_sum(l2, l1, sum);
      lemma_partial_sum_commutative(l1, l2, |l2|);
      sum := sum + l2[p2..];  // in linked-list reality, it's like `tail.next := p2`
      break;
    }

    // otherwise, calculate as usual:
    reveal partial_sum();
    var (x1, p1') := if p1 < |l1| then (l1[p1] as int, p1 + 1) else (0, p1);
    var (x2, p2') := if p2 < |l2| then (l2[p2] as int, p2 + 1) else (0, p2);
    var y := x1 + x2 + carry;
    var (carry', rem) := if y < 10 then (0, y) else (1, (y - 10));
    sum := sum + [rem];
    p1, p2, carry := p1', p2', carry';
  }

  assert l1[..|l1|] == l1 && l2[..|l2|] == l2;
  assert (sum, carry) == partial_sum(l1, l2, max(|l1|, |l2|));
  assert value_of(sum + [carry]) == value_of(l1) + value_of(l2);

  if carry == 1 {
    sum := sum + [carry];
  } else {
    assert value_of(sum) == value_of(sum + [carry]) by { reveal value_of(); }
    lemma_validity_of_final_sum(l1, l2, sum, carry);
  }
}

// To verify the above solution, a couple of new lemmas are needed.
// The lemma below essentially says "a + b == b + a".
lemma lemma_partial_sum_commutative(l1: seq<digit>, l2: seq<digit>, n: nat)
  ensures partial_sum(l1, l2, n) == partial_sum(l2, l1, n)
{
  reveal partial_sum();
}

// This lemma supports the correctness for "skipping to the final result":
lemma lemma_quick_sum(longer: seq<digit>, shorter: seq<digit>, p_sum: seq<digit>)
  requires (p_sum, 0) == partial_sum(longer, shorter, |p_sum|)
  requires |shorter| <= |p_sum| <= |longer|
  ensures (p_sum + longer[|p_sum|..], 0) == partial_sum(longer, shorter, |longer|)
{
  reveal partial_sum();
  var sum := p_sum;
  for i := |p_sum| to |longer|
    invariant (sum, 0) == partial_sum(longer, shorter, i)
    invariant sum == p_sum + longer[|p_sum|..i]
  {
    sum := sum + [longer[i]];
  }
  assert longer[|p_sum|..|longer|] == longer[|p_sum|..];
}


/* Discussions (Part II)
5. As the complexity grows, Dafny's performance becomes unpredictable!!
  It is hard to predict which assertions/lemma/refactoring will speed up or slow down Dafny.
  I even feel sometimes "it's just luck"... (perhaps the random seed??)

  This issue is discussed here: http://dafny.org/dafny/VerificationOptimization/VerificationOptimization
  {:vcs_split_on_every_assert} indeed does some (limited) magic, and helps a bit on troubleshooting...

6. Fun duality! ...Between program and proof
  We hear a lot about using theorems to prove a program, but how about using a program to prove a theorem?!
  As you just see, `lemma_quick_sum` does exactly this!

  (a) In Dafny, you can write assertions (most importantly, loop invariants) to verify a stateful program.
  (b) In Dafny, you can also write a stateful program (most interestingly, loop bodies) to prove a lemma!
  While (a) is well known, (b) is certainly one thing I've found of most fun with Dafny.

  ...And it's not just fun, but also useful when it's more intuitive to prove by iteration than by recursion.

7. Recursion direction matters
  It is tempting to recurse from another direction when defining the `value_of` function (see below).
  At the first glance, it is more concise and "natural", why didn't we use it?

  Because we needed to be consistent with the algorithm under verification (i.e. primary-school addition),
  which iterates from lower digits to higher ones.

  But is this `addTwoNumbers` problem really a one-way street? Well... No.
  Next, we'll show that the other direction also works!
*/

// Alternative definition of `value_of`:
ghost function {:opaque} value_of'(l: seq<digit>): int {
  if l == [] then
    0
  else
    l[0] + 10 * value_of'(l[1..])
}

// FYI, their equivalence is given by the following lemma:
lemma lemma_equivalence_of_value(l: seq<digit>)
  ensures value_of(l) == value_of'(l)
{
  reveal pow10(), value_of(), value_of'();
  if |l| <= 1 {
    // base case, trivial to prove
  } else {
    // inductive case
    var hi := |l| - 1;
    calc {
      value_of'(l);
    ==
      l[0] + 10 * value_of(l[1..]);
    == { assert l[1..][..(hi - 1)] == l[1..hi]; }
      l[0] + 10 * (value_of(l[1..hi]) + pow10(hi - 1) * l[hi]);
    ==
      (l[0] + 10 * value_of'(l[1..hi])) + 10 * pow10(hi - 1) * l[hi];
    ==
      value_of'(l[..hi]) + pow10(hi) * l[hi];
    ==
      value_of(l);
    }
  }
}

// Alternative direction of recursion: from higher digits to lower digits.
function {:opaque} sum_recursive(l1: seq<digit>, l2: seq<digit>, carry: digit): (sum: seq<digit>)
  requires 0 <= carry <= 1
  ensures value_of'(sum) == value_of'(l1) + value_of'(l2) + carry
  // For below, notice that `valid_seq(l1) && valid_seq(l2) ==> valid_seq(sum)` does NOT hold recursively,
  // thus we need to "loose" it a little bit:
  requires (valid_seq(l1) || l1 == []) && (valid_seq(l2) || l2 == [])
  ensures (l1 != [] || l2 != []) ==> valid_seq(sum)
{
  reveal value_of'(), sum_recursive();
  if l1 == [] && l2 == [] && carry == 0 then
    []
  else
    var (x1, l1') := if l1 == [] then (0, []) else (l1[0], l1[1..]);
    var (x2, l2') := if l2 == [] then (0, []) else (l2[0], l2[1..]);
    var y := x1 + x2 + carry;
    var (carry', z) := if y < 10 then (0, y) else (1, y - 10);
    [z] + sum_recursive(l1', l2', carry')
}
// In fact, the above assertions about `valid_seq` are NOT totally inductive, but still get verified!
// Dafny must have automatically "unrolled" this function several times, amazing...


// The above function natually lead to a "recursive solution" of `addTwoNumbers`:
method addTwoNumbers''(l1: seq<digit>, l2: seq<digit>) returns (sum: seq<digit>)
  requires valid_seq(l1) && valid_seq(l2)
  ensures valid_seq(sum)
  ensures value_of'(sum) == value_of'(l1) + value_of'(l2)
{
  return sum_recursive(l1, l2, 0);
}

// However, the above solution is inferior, as it needs O(|sum|) "extra space" to store the recursion stack
// (unless somehow eliminated by a compiler's "tail recursion optimization").
// In comparison, the "iterative solution" only needs O(1) "extra space".
//
// Nevertheless, we can use the "recursive solution" above to verify our "iterative solution", shown below.
// Following this path of verification, we get rid of the `pow10` function and the tedious `calc`!
method {:vcs_split_on_every_assert} addTwoNumbers'''(l1: seq<digit>, l2: seq<digit>) returns (sum: seq<digit>)
  requires valid_seq(l1) && valid_seq(l2)
  ensures valid_seq(sum)
  ensures value_of'(sum) == value_of'(l1) + value_of'(l2)
{
  // It's totally the SAME method as the original solution `addTwoNumbers`, just verified in a different way.
  var p1, p2 := 0, 0;
  var carry := 0;
  sum := [];

  while p1 < |l1| || p2 < |l2|
    invariant 0 <= p1 <= |l1| && 0 <= p2 <= |l2|
    invariant (p1 < |l1| && p2 < |l2|) ==> p1 == p2
    invariant (p1 == |l1| && p2 < |l2|) ==> p1 <= p2
    invariant (p1 < |l1| && p2 == |l2|) ==> p1 >= p2
    invariant |sum| == max(p1, p2)
    invariant 0 <= carry <= 1
    invariant sum + sum_recursive(l1[p1..], l2[p2..], carry) == sum_recursive(l1, l2, 0)
    decreases |l1| - p1, |l2| - p2
  {
    var (x1, p1') := if p1 < |l1| then (l1[p1] as int, p1 + 1) else (0, p1);
    var (x2, p2') := if p2 < |l2| then (l2[p2] as int, p2 + 1) else (0, p2);
    var y := x1 + x2 + carry;
    var (carry', rem) := if y < 10 then (0, y) else (1, (y - 10));
    assert sum_recursive(l1[p1..], l2[p2..], carry) == [rem] + sum_recursive(l1[p1'..], l2[p2'..], carry') by {
      reveal sum_recursive();
    }
    var sum' := sum + [rem];
    p1, p2, carry, sum := p1', p2', carry', sum';
  }

  // All we want is `sum == sum_recursive(l1, l2, 0)`, which leads to the post-conditions.
  // Not quite now, so next we'll fill this "last gap":
  assert sum + sum_recursive([], [], carry) == sum_recursive(l1, l2, 0) by {
    assert l1[p1..] == [] && l2[p2..] == [];
  }
  if carry == 1 {
    assert sum_recursive([], [], carry) == [carry] by { reveal sum_recursive(); }
    sum := sum + [carry];
  } else {
    assert sum_recursive([], [], carry) == [] by { reveal sum_recursive(); }
    assert sum + [] == sum;
  }
}
