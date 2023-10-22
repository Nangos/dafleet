/* https://leetcode.com/problems/median-of-two-sorted-arrays/
Given two sorted arrays nums1 and nums2 of size m and n respectively, return the median of the two sorted arrays.
The overall run time complexity should be O(log (m+n)).

Example 1:
Input: nums1 = [1,3], nums2 = [2]
Output: 2.00000
Explanation: merged array = [1,2,3] and median is 2.
*/


ghost predicate sorted(s: seq<int>) {
  forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

// An abstract function for merging two sorted sequences, thus `opaque`.
ghost opaque function merge(s1: seq<int>, s2: seq<int>): (s: seq<int>)
  requires sorted(s1) && sorted(s2)
  ensures sorted(s)
  ensures multiset(s) == multiset(s1 + s2)

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

method findMedianSortedArrays(nums1: seq<int>, nums2: seq<int>) returns (mid: real)
  requires |nums1| + |nums2| > 0
  requires sorted(nums1) && sorted(nums2)
  ensures mid == median(merge(nums1, nums2))
{
  // Up to you!
}
