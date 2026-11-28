import Mathlib

/-!
# A114976: Number of subsets of {1,2,....,n} with an arithmetic mean that is an integer and also a divisor of n.

Source: https://oeis.org/A114976
Credit: @esracummings31-blip

a(n) counts the (nonempty) subsets S of {1, ..., n} whose arithmetic mean (Sum S)/|S| is an
integer dividing n. Data: 1, 2, 2, 5, 2, 14, 2, 30, 11, 80, ...

Comment (OEIS): "a(n) = 2 iff n is prime, just as for the number of divisors of n and also, at
least for the very first terms, a(n) = odd iff n is a square: these observations might suggest
conjectures on a deeper relationship with A000005."

We state both observations for n ≥ 1.
-/

namespace OMA.S_oeis_a114976

/-- A114976: subsets of `{1, ..., n}` whose mean is an integer dividing `n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S => S.Nonempty ∧ S.card ∣ ∑ x ∈ S, x ∧
    (∑ x ∈ S, x) / S.card ∣ n)).card

theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n = 2 ↔ n.Prime)) ∧
    (∀ n : ℕ, 1 ≤ n → (Odd (a n) ↔ IsSquare n)) := by
  sorry

end OMA.S_oeis_a114976
