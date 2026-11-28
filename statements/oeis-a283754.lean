import Mathlib

/-!
# A283754: The smallest number k such that k*2^n mod 3^n = 1

Source: https://oeis.org/A283754 (conjecture by Robert Israel, Mar 28 2017)

Conjecture: 2*a(n+1) - a(n) = 3^n * A055620(n).

Conventions:
* `a n` (offset 1) is the least natural number `k` with `k * 2^n mod 3^n = 1`, written as the
  infimum of that set (for `n >= 1` the set is nonempty since 2 and 3 are coprime; the value
  at `n = 0` is irrelevant and never used).
* A055620 (offset 0) lists the base-6 digits of an idempotent 6-adic integer. A 6-adic
  integer with digits `d 0, d 1, ...` (each `< 6`) is idempotent exactly when, for every `n`,
  the integer `psum d n = Sum_(i < n) d i * 6^i` satisfies `psum d n ^ 2 = psum d n`
  modulo `6^n` (the 6-adic integers are the inverse limit of the rings Z/6^n). Besides 0
  and 1 there are exactly two idempotent 6-adic integers; A055620 is the one whose first
  digit is 4 (the other one, A054869, starts with 3). `IsIdemDigits d` says that `d` is the
  digit sequence of this idempotent.
* The statement asserts that such a digit sequence exists and that for every such `d`
  the identity holds for all `n >= 1` (the range where `a n` is defined), in the integers.
-/

namespace OMA.S_oeis_a283754

/-- A283754(n): the smallest `k` with `k * 2^n mod 3^n = 1`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | k * 2 ^ n % 3 ^ n = 1}

/-- The integer with base-6 digits `d 0, ..., d (n-1)` (least significant first). -/
def psum (d : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, d i * 6 ^ i

/-- `d` is the digit sequence of the idempotent 6-adic integer A055620 (first digit 4). -/
def IsIdemDigits (d : ℕ → ℕ) : Prop :=
  (∀ i, d i < 6) ∧ d 0 = 4 ∧ ∀ n, psum d n ^ 2 % 6 ^ n = psum d n % 6 ^ n

theorem main : (∃ d, IsIdemDigits d) ∧
    ∀ d, IsIdemDigits d → ∀ n : ℕ, 1 ≤ n → 2 * (a (n + 1) : ℤ) - a n = 3 ^ n * d n := by
  sorry

end OMA.S_oeis_a283754
