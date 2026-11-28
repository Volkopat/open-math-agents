import Mathlib

/-!
# OEIS A152191

Source: https://oeis.org/A152191 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Haruzame0

a(n) is the nearest integer to
Product_{k=1..floor((n-1)/2)} (1 + 4 cos(k*pi/n)^2) (1 - 4 sin(k*pi/n)^2).
The product is empty, hence 1, when the upper index is less than 1, including n = 0.

R. J. Mathar conjectured that for n > 0,
a(n) = (-1)^(n+1) * Fibonacci(n) * A101675(n-1).
A101675 is the period-6 sequence 1, -1, -2, 1, 1, 0.
The same comment also gives a generating function and an even-index identification;
the theorem is the closed form.
-/

namespace OMA.S_oeis_a152191

noncomputable def raw (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 ((n - 1) / 2),
    (1 + 4 * Real.cos ((k : ℝ) * Real.pi / (n : ℝ)) ^ 2) *
      (1 - 4 * Real.sin ((k : ℝ) * Real.pi / (n : ℝ)) ^ 2)

/-- A101675 at `n`, period 6. -/
def coeff (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => 1
  | 1 => -1
  | 2 => -2
  | 3 => 1
  | 4 => 1
  | _ => 0

theorem main : ∀ n : ℕ, 0 < n →
    round (raw n) =
      (-1 : ℤ) ^ (n + 1) * (Nat.fib n : ℤ) * coeff (n - 1) := by
  sorry

end OMA.S_oeis_a152191
