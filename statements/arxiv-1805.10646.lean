import Mathlib

/-!
# Palindromes in starlike trees with three branches

Source: https://arxiv.org/abs/1805.10646, conjecture after Table 1
(Amy Glen, Jamie Simpson and W. F. Smyth)
Credit: @pyaf

A (3,n)-starlike tree has a central vertex and three branches, each a path
of n edges, and every edge carries one letter. A palindrome of the tree is a
non-empty palindromic word read along a simple path. As in the abstract the
alphabet is binary. The paper proves at most 4n − 1 palindromes and
conjectures that, for all n ≥ 2, the maximum is exactly 4n − 2 (attained by
the branches aⁿ, baⁿ⁻¹, bbaⁿ⁻²). Searches of arXiv for later work on
palindromes in starlike trees found only results on general trees
(e.g. arXiv:2008.13209), not this conjecture.

A branch is given by its word read from the centre outwards. Every simple
path lies on a leaf-to-leaf path through the centre, so the palindromes of
the tree are the palindromic non-empty factors of the three words R(x)y,
R(x)z and R(y)z.
-/

namespace OMA.S_arxiv_1805_10646

/-- The three leaf-to-leaf words through the central vertex. -/
def leafPaths (x y z : List Bool) : List (List Bool) :=
  [x.reverse ++ y, x.reverse ++ z, y.reverse ++ z]

/-- The distinct non-empty palindromes of the starlike tree. -/
def palindromes (x y z : List Bool) : Set (List Bool) :=
  {p | p ≠ [] ∧ p.reverse = p ∧ ∃ w ∈ leafPaths x y z, p <:+: w}

theorem main : ∀ n ≥ 2,
    (∃ x y z : List Bool, x.length = n ∧ y.length = n ∧ z.length = n ∧
      (palindromes x y z).ncard = 4 * n - 2) ∧
    ∀ x y z : List Bool, x.length = n → y.length = n → z.length = n →
      (palindromes x y z).ncard ≤ 4 * n - 2 := by
  sorry

end OMA.S_arxiv_1805_10646
