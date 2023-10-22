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


type digit = x: int | 0 <= x <= 9 witness 0

// Firstly, we define when a sequence of digits is "valid":
ghost predicate valid_seq(l: seq<digit>) {
  && |l| > 0                      // non-empty
  && (l == [0] || l[|l|-1] != 0)  // no leading zero except the number 0
}

// Then we specify which integer is encoded by a given sequence of digits.
ghost function value_of(l: seq<digit>): int {
  if l == [] then
    0
  else
    l[0] + 10 * value_of(l[1..])
}

method addTwoNumbers(l1: seq<digit>, l2: seq<digit>) returns (sum: seq<digit>)
  requires valid_seq(l1) && valid_seq(l2)
  ensures valid_seq(sum)
  ensures value_of(sum) == value_of(l1) + value_of(l2)
{
  // Up to you!
}
