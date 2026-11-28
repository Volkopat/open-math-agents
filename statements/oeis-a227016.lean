import Mathlib

/-!
# OEIS A227016

Source: https://oeis.org/A227016 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Haruzame0

a(n) is the floor of the harmonic mean of the integers from
g(n - 1) + 1 through g(n), where g(n) = n * (n + 1) * (n + 2) / 6.
For n = 1 the range is the singleton {1}.

The ordinary generating function on the page has denominator
(1 - x)^3 * (1 - x^8). For every n > 12 that gives
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) + a(n-8) - 3*a(n-9) + 3*a(n-10) - a(n-11).
The page writes the relation for n > 1; it already fails at n = 12, and it holds
from n = 13 onward.
-/

namespace OMA.S_oeis_a227016

def tetra (n : ℕ) : ℕ := n * (n + 1) * (n + 2) / 6

noncomputable def raw (n : ℕ) : ℝ :=
  let lo := tetra (n - 1) + 1
  let hi := tetra n
  let count : ℝ := (hi - lo + 1 : ℕ)
  let denom : ℝ := ∑ k ∈ Finset.Icc lo hi, (1 / (k : ℝ))
  count / denom

noncomputable def term (n : ℕ) : ℕ := Nat.floor (raw n)

theorem main : ∀ n : ℕ, 12 < n →
    (term n : ℤ) =
      3 * (term (n - 1) : ℤ) - 3 * (term (n - 2) : ℤ) + (term (n - 3) : ℤ) +
        (term (n - 8) : ℤ) - 3 * (term (n - 9) : ℤ) + 3 * (term (n - 10) : ℤ) -
        (term (n - 11) : ℤ) := by
  sorry

end OMA.S_oeis_a227016
