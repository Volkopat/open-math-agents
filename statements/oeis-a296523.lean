import Mathlib

/-!
# A296523: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x > 0, y >= 0 and 0 <= z <= w such that 64*x^2 + 65*y^2 = q^2 for some practical number q.

Source: https://oeis.org/A296523
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A296523 (Zhi-Wei Sun, Dec 14 2017), part (i): a(n) > 0
for all n > 0. Also, a(n) = 1 only for those numbers 2^k (k = 0,1,2,...), 4^k*m (k = 0,1,...; m =
3, 7), 4^k*47 (k = 0,1,2,3), 4^k*s (k = 0,1,2; s = 15, 23, 31, 39, 71); 4^k*t (k = 0,1; t = 87,
111, 119, 159, 191, 311).

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n = x^2 + y^2 + z^2 + w^2, x > 0, z <= w and
  64*x^2 + 65*y^2 = q^2 for some practical number q, exactly as in the OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* Only part (i) of the conjecture is formalized; any other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a296523

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A296523 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ 0 < x ∧ z ≤ w ∧
  ∃ q : ℕ, Practical q ∧ 64 * x ^ 2 + 65 * y ^ 2 = q ^ 2

/-- A296523: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A296523. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      (∃ k : ℕ, n = 2 ^ k) ∨ (∃ k : ℕ, n = 4 ^ k * 3 ∨ n = 4 ^ k * 7) ∨
      (∃ k : ℕ, k ≤ 3 ∧ n = 4 ^ k * 47) ∨
      (∃ k s : ℕ, k ≤ 2 ∧ s ∈ ({15, 23, 31, 39, 71} : Finset ℕ) ∧ n = 4 ^ k * s) ∨
      (∃ k t : ℕ, k ≤ 1 ∧ t ∈ ({87, 111, 119, 159, 191, 311} : Finset ℕ) ∧
      n = 4 ^ k * t))) := by
  sorry

end OMA.S_oeis_a296523
