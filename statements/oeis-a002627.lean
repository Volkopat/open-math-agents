import Mathlib

/-!
# A002627: a(n) = n*a(n-1) + 1, a(0) = 0.

Source: https://oeis.org/A002627
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a002627

/-- The OEIS sequence defined by `a(0) = 0` and `a(n) = n*a(n-1) + 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * a n + 1

/-- R. J. Mathar's conjectured recurrence, together with the adjacent identity stated
in the same OEIS entry. The first recurrence is cast to the integers because it has a
negative coefficient. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n →
      (a n : ℤ) + (-(n : ℤ) - 1) * (a (n - 1) : ℤ) +
        ((n : ℤ) - 1) * (a (n - 2) : ℤ) = 0) ∧
    (∀ n : ℕ,
      a (n + 1) = a n + Nat.factorial n +
        ∑ k ∈ Finset.Icc 1 n, (Nat.factorial n / Nat.factorial k) * a k) := by
  sorry

end OMA.S_oeis_a002627
