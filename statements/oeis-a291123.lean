import Mathlib

/-!
# A291123: Number of ways to write 4*n+1 as (p-1)^2 + q^2 + r^2, where p is prime and q and r are nonnegative integers with q <= r.

Source: https://oeis.org/A291123
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n, and a(n) = 1 only for n = 0, 3, 6, 23, 44.
(ii) Any positive integer relatively prime to 6 can be written as (p-1)^2 + q^2 + 3*r^2, where p is
prime, and q and r are integers.
(iii) Let n be any nonnegative integer. Then 4*n+1 can be written as x^2 + y^2 + z^2, where x, y, z
are nonnegative integers with x + y + 2*z prime; 4*n+2 can be written as x^2 + y^2 + z^2, where
x, y, z are nonnegative integers with x + 3*y prime. Also, we can write 4*n+3 as 2*x^2 + y^2 + z^2,
where x, y, z are nonnegative integers with 2*x+1 prime.

Formalization notes:
* a(n) counts triples (p, q, r) with p prime, q ≤ r and (p-1)^2 + q^2 + r^2 = 4n + 1; all three are
  at most 4n + 2.
* In (ii) only squares of q and r occur, so q, r ∈ ℕ is equivalent to integers.
* Controls (computed): for n < 1200, a(n) > 0 and a(n) = 1 exactly at 0, 3, 6, 23, 44; (ii) holds
  for n < 3000 coprime to 6; the three claims of (iii) hold for n < 1200.
-/

namespace OMA.S_oeis_a291123

/-- A291123(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (4 * n + 3) ×ˢ Finset.range (4 * n + 3) ×ˢ Finset.range (4 * n + 3)).filter
    fun t : ℕ × ℕ × ℕ => t.1.Prime ∧ t.2.1 ≤ t.2.2 ∧
      (t.1 - 1) ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 4 * n + 1).card

/-- The conjecture of the entry (all three parts). -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧
      (∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 3, 6, 23, 44} : Finset ℕ)) ∧
      (∀ m : ℕ, 0 < m → Nat.Coprime m 6 →
        ∃ p q r : ℕ, p.Prime ∧ (p - 1) ^ 2 + q ^ 2 + 3 * r ^ 2 = m) ∧
      (∀ n : ℕ, ∃ x y z : ℕ, (x + y + 2 * z).Prime ∧ x ^ 2 + y ^ 2 + z ^ 2 = 4 * n + 1) ∧
      (∀ n : ℕ, ∃ x y z : ℕ, (x + 3 * y).Prime ∧ x ^ 2 + y ^ 2 + z ^ 2 = 4 * n + 2) ∧
      ∀ n : ℕ, ∃ x y z : ℕ, (2 * x + 1).Prime ∧ 2 * x ^ 2 + y ^ 2 + z ^ 2 = 4 * n + 3 := by
  sorry

end OMA.S_oeis_a291123
