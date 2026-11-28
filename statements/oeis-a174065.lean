import Mathlib

/-!
# A174065: the sequence whose convolution with its aerated variant is the partition numbers

Source: https://oeis.org/A174065 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A174065 (Gary W. Adamson, Mar 06 2010), offset 0: Convolved with its aerated
variant = A000041. Data 1, 1, 1, 2, 3, 4, 5, 7, 9, 12, 15, 19, 25, 31, 38, 48, 60, 73, 89, ...

Comments: A000041 = (1, 1, 2, 3, 5, 7, ...) = (1, 1, 1, 2, 3, 4, 5, 7, ...) *
(1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 7, 0, 9, 0, ...).
The sequence diverges from A100853 after 16 terms; and is a conjectured Euler transform of
A035263: (1, 0, 1, 1, 1, 0, 1, 0, 1, ...).

Formalization notes.
* A000041(n) is the number of partitions of n (`Fintype.card (Nat.Partition n)`).
* The aerated variant of a sequence a is (a(0), 0, a(1), 0, a(2), 0, ...). `IsA a` says that
  the convolution of a with its aerated variant is A000041: for each n,
  Sum_{i + j = n, j even} a(i) a(j/2) = A000041(n). This property determines the sequence
  (the case n = 0 gives a(0) = 1, and then each a(n) follows from the smaller terms).
* A035263 (offset 1) is the indicator of the integers k >= 1 with an even 2-adic valuation:
  A035263(k) = 1 if the exponent of 2 in k is even, and 0 otherwise.
* The Euler transform of a 0-1 sequence, the indicator of a set S of positive integers, has
  the generating function Product_{k in S} 1/(1 - x^k). Its n-th term is the number of
  partitions of n whose parts are all in S. So the Euler transform of A035263 at n is the
  number of partitions of n into parts with an even 2-adic valuation.
* `main` is the conjecture: each sequence with the defining property is this Euler transform.
-/

namespace OMA.S_oeis_a174065

/-- The defining property of A174065: the convolution with the aerated variant gives the
partition numbers A000041. -/
def IsA (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, if Even ij.2 then a ij.1 * a (ij.2 / 2) else 0)
    = Fintype.card (Nat.Partition n)

/-- The Euler transform of A035263 at n: the number of partitions of n into parts with an
even 2-adic valuation. -/
def euler (n : ℕ) : ℕ :=
  Fintype.card {π : Nat.Partition n // ∀ k ∈ π.parts, Even (padicValNat 2 k)}

/-- Conjecture of Adamson: A174065 is the Euler transform of A035263. -/
theorem main : ∀ a : ℕ → ℕ, IsA a → ∀ n : ℕ, a n = euler n := by
  sorry

end OMA.S_oeis_a174065
