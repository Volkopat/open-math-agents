import Mathlib

/-!
# A280386: n as the sum of two squares and a strict partition number

Source: https://oeis.org/A280386

A280386 (offset 1): `a(n)` is the number of ways to write `n` as the sum of two squares and a
term of A000009 (the number of partitions into distinct parts): 1, 2, 3, 3, 4, 5, 4, 4, 4, 6, …
For example `a(1) = 1` since `1 = 0^2 + 0^2 + 1` with `1 = A000009(1) = A000009(2)`.

Conjecture (Zhi-Wei Sun, Jan 01 2017): `a(n) > 0` for all `n > 0`. The entry notes that this
has been verified for `n` up to `10^9` (Qing-Hu Hou).

`a(n) > 0` says exactly that `n` is the sum of two squares of nonnegative integers and a value
of A000009, and the conjecture is stated in that form.

Conventions: A000009(k) is the number of partitions of `k` into distinct parts, the cardinality
of Mathlib's finset `Nat.Partition.distincts k` (1, 1, 1, 2, 2, 3, 4, 5, … for `k = 0, 1, 2, …`).
The squares are squares of natural numbers, and `0^2` is allowed, as in the entry's examples.
-/

namespace OMA.S_oeis_a280386

/-- The strict partition function A000009: the number of partitions of `n` into distinct
parts. -/
def strictPartitionNumber (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y k : ℕ, x ^ 2 + y ^ 2 + strictPartitionNumber k = n := by
  sorry

end OMA.S_oeis_a280386
