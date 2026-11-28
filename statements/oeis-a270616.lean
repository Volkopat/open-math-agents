import Mathlib

/-!
# A270616: Number of ordered ways to write n as the sum of a positive square, the square of a triangular number, and a generalized pentagonal number (A001318).

Source: https://oeis.org/A270616
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A270616 (Zhi-Wei Sun, Mar 20 2016): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 1, 8, 29, 34, 5949, 10913.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 2, 2, 3, 2, 1, 3, 4, 4, 3, ...). `a n` is the number of
  triples (s, t, g) of natural numbers with s a positive square, t the square of a triangular
  number, g a generalized pentagonal number and n = s + t + g, exactly as in the OEIS name.
* Triangular numbers are k*(k+1)/2 with k = 0, 1, 2, ... (0 included), and generalized pentagonal
  numbers (A001318) are z*(3*z-1)/2 with z any integer; the divisions by 2 are exact.
* The ways are counted by the values of the three summands, in this order.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a270616

/-- The condition in the name of A270616 on a tuple, for a given n. -/
def P (n : ℕ) (s t g : ℕ) : Prop :=
  (∃ x : ℕ, 0 < x ∧ s = x ^ 2) ∧ (∃ k : ℕ, t = (k * (k + 1) / 2) ^ 2) ∧
    (∃ z : ℤ, (g : ℤ) = z * (3 * z - 1) / 2) ∧ s + t + g = n

/-- A270616: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A270616. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 8, 29, 34, 5949, 10913} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a270616
