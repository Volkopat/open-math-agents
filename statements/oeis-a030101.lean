import Mathlib

/-!
# A030101: binary reversal via the lexicographic rank A264596

Source: https://oeis.org/A030101 (conjecture stated in the OEIS entry)

A030101(n) is the number obtained by writing `n` in binary, reversing the digits and
reading the result back in binary.
A264596(n) is the position (indexing from 0) of `n` in the list of the numbers `0..n`
written in binary with the least significant bit on the left and sorted
lexicographically. In Lean, `Nat.digits 2 m` is exactly the binary expansion of `m`
with the least significant bit first, and lists are compared lexicographically by `<`
(a proper prefix is smaller); the position of `n` is the number of `m <= n` whose
expansion is smaller. (Whether `0` is written as the empty word or as `0` does not
change any position, since `0` is the smallest word either way.)
A053645(n) = n - 2^floor(log2 n) is the distance from `n` to the largest power of 2 not
exceeding `n`.

Conjecture: `a(n) = 2*w(n) - 2*w(A053645(n)) - 1` for `n > 0`, where `w = A264596`.
-/

namespace OMA.S_oeis_a030101

/-- A030101: reverse the binary digits of `n`. -/
def a (n : ℕ) : ℕ := Nat.ofDigits 2 (Nat.digits 2 n).reverse

/-- A264596: position (from 0) of `n` among `0..n` sorted lexicographically by their binary
expansions written least significant bit first. -/
def w (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun m => Nat.digits 2 m < Nat.digits 2 n)).card

/-- A053645: distance from `n` to the largest power of 2 that is `≤ n`. -/
def A053645 (n : ℕ) : ℕ := n - 2 ^ Nat.log 2 n

theorem main : ∀ n : ℕ, 0 < n → (a n : ℤ) = 2 * w n - 2 * w (A053645 n) - 1 := by
  sorry

end OMA.S_oeis_a030101
