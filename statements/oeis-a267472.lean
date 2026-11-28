import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range

/-!
# OEIS A267472

R. H. Hardin counts four-letter words on 0,...,n. After the first adjacent
repeat the remaining letters may not exceed the repeated letter. The source
lists (3,6,3,5) as a valid word. Colin Barker proposed the two identities
on February 5, 2018. https://oeis.org/A267472
-/
namespace OMA.S_oeis_a267472

/-- Fix the second letter b and sum over the first letter a. If a=b, each of
the final two letters lies in 0,...,b. Otherwise sum over the third letter c.
The last letter is bounded by b if c=b and is unrestricted otherwise. -/
def words (q : ℕ) : ℤ :=
  ∑ b ∈ Finset.range q, ∑ a ∈ Finset.range q,
    if a = b then ((b : ℤ) + 1)^2
    else ∑ c ∈ Finset.range q, if c = b then (b : ℤ) + 1 else (q : ℤ)

/-- The generating series starts at index one. -/
def coeff : ℕ → ℤ
  | 0 => 0
  | n+1 => words (n+2)

def shift (a : ℕ → ℤ) (j m : ℕ) := if j ≤ m then a (m-j) else 0

def numerator : ℕ → ℤ
  | 1 => 12 | 2 => 2 | 3 => 14 | 4 => -5 | 5 => 1 | _ => 0

/-- The generating-series identity after multiplying by (1-x)^5, and the
order-five recurrence in the original positive indexing. -/
theorem main :
    (∀ m, coeff m - 5*shift coeff 1 m + 10*shift coeff 2 m
      - 10*shift coeff 3 m + 5*shift coeff 4 m - shift coeff 5 m = numerator m) ∧
    (∀ t, coeff (t+6) = 5*coeff (t+5) - 10*coeff (t+4) + 10*coeff (t+3)
      - 5*coeff (t+2) + coeff (t+1)) := by
  sorry
end OMA.S_oeis_a267472
