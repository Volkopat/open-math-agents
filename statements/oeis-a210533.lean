import Mathlib

/-!
# A210533: Number of ways to write 2n = x+y (x,y>0) with x-1 and x+1 both prime, and x and x^3+y^3 both practical.

Source: https://oeis.org/A210533
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A210533 (Zhi-Wei Sun, Jan 28 2013): a(n)>0 for all n>2.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, ...). `a n` is the number of
  pairs (x, y) with 2n = x + y, x, y > 0, x - 1 and x + 1 both prime, and x and x^3 + y^3 both
  practical, exactly as in the OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* x - 1 is an exact natural-number subtraction since x > 0.
* Only the first sentence of the conjecture is formalized; the `Moreover` sentence (about x^m +
  y^m) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a210533

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A210533 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℕ) : Prop :=
  x + y = 2 * n ∧ 0 < x ∧ 0 < y ∧ (x - 1).Prime ∧ (x + 1).Prime ∧ Practical x ∧
  Practical (x ^ 3 + y ^ 3)

/-- A210533: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A210533. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a210533
