import Mathlib

/-!
# A300219: Number of ways to write n^2 as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers and z <= w such that both x and 4*x - 3*y are powers of 4 (including 4^0 = 1).

Source: https://oeis.org/A300219
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; verified for n up to 10^7), part (i): a(n) > 0 for all n > 0,
and a(n) = 1 only for n = 4^k*m (k = 0, 1, 2, ... and m = 1, 2, 3, 5, 15, 37, 83, 263). Also, for each
n = 2, 3, ... we can write n^2 as x^2 + y^2 + z^2 + w^2 with x, y, z, w nonnegative integers such
that both x and 4*x - 3*y lie in the set {2^(2k+1): k = 0, 1, ...}. (Part (ii), with its exceptional
family based on 81503, is not stated here.)

Formalization notes:
* 4x - 3y is computed in ℤ; being a power of 4 (or in {2^(2k+1)}) forces it to be positive.
* a(n) counts quadruples with entries ≤ n; "a(n) = 1 only for ..." is an equivalence for n > 0.
* Controls (computed): for 1 ≤ n < 300 all three claims hold.
-/

namespace OMA.S_oeis_a300219

open Classical in
/-- A300219(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    fun t : ℕ × ℕ × ℕ × ℕ => t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = n ^ 2 ∧
      t.2.2.1 ≤ t.2.2.2 ∧ (∃ j : ℕ, t.1 = 4 ^ j) ∧ (∃ j : ℕ, 4 * (t.1 : ℤ) - 3 * t.2.1 = 4 ^ j)).card

/-- Part (i) of the conjecture. -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      (∀ n : ℕ, 0 < n → (a n = 1 ↔ ∃ k : ℕ, ∃ m ∈ ({1, 2, 3, 5, 15, 37, 83, 263} : Finset ℕ),
        n = 4 ^ k * m)) ∧
      ∀ n : ℕ, 2 ≤ n → ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧
        (∃ j : ℕ, x = 2 ^ (2 * j + 1)) ∧ (∃ j : ℕ, 4 * (x : ℤ) - 3 * y = 2 ^ (2 * j + 1)) := by
  sorry

end OMA.S_oeis_a300219
