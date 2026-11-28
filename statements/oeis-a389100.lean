import Mathlib

/-!
# A389100: Elements of a non-singleton interval of natural numbers whose product is divisible by the square of the largest prime factor of th

Source: https://oeis.org/A389100
Credit: @max-otc

The entry states: "Conjecture: A387054 is a subsequence."

* A070003: numbers divisible by the square of their largest prime factor.
* A388654: elements of an interval of natural numbers whose product is divisible by the square of
  the largest prime factor (single-element intervals are permitted).
* A387054: elements of A388654 that do not lie in A070003.
* A389100: elements of a non-singleton interval of natural numbers whose product is divisible by
  the square of the largest prime factor of the product.

An interval of natural numbers is `[a, b] = {a, a + 1, ..., b}` with `1 ≤ a ≤ b`; it is
non-singleton when `a < b`. A number `m` is divisible by the square of its largest prime factor when
some prime `q` divides `m`, every prime factor of `m` is at most `q`, and `q ^ 2 ∣ m` (this fails for
`m = 1`, which has no prime factor, and for `m = 0`, which has no largest prime factor). All four
sequences list their terms in increasing order, so "A387054 is a subsequence of A389100" means that
every term of A387054 is a term of A389100.
-/

namespace OMA.S_oeis_a389100

/-- `m` is divisible by the square of its largest prime factor. -/
def SqGpfDvd (m : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ (∀ p : ℕ, p.Prime → p ∣ m → p ≤ q) ∧ q ^ 2 ∣ m

/-- `[a, b]` is an interval of natural numbers whose product is divisible by the square of the
largest prime factor of the product. -/
def BadInterval (a b : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ SqGpfDvd (∏ i ∈ Finset.Icc a b, i)

/-- `k` is a term of A070003. -/
def InA070003 (k : ℕ) : Prop := SqGpfDvd k

/-- `k` is a term of A388654. -/
def InA388654 (k : ℕ) : Prop := ∃ a b : ℕ, BadInterval a b ∧ a ≤ k ∧ k ≤ b

/-- `k` is a term of A387054. -/
def InA387054 (k : ℕ) : Prop := InA388654 k ∧ ¬ InA070003 k

/-- `k` is a term of A389100. -/
def InA389100 (k : ℕ) : Prop := ∃ a b : ℕ, BadInterval a b ∧ a < b ∧ a ≤ k ∧ k ≤ b

/-- A387054 is a subsequence of A389100. -/
theorem main : ∀ k : ℕ, InA387054 k → InA389100 k := by
  sorry

end OMA.S_oeis_a389100
