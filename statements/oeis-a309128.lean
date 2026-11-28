import Mathlib

/-!
# A309128: `(1/n)` times the sum of the elements of the subsets of `[n]` whose sum is divisible by `n`

Source: https://oeis.org/A309128
Credit: @avivorly

A309128 (Alois P. Heinz, Jul 2019), name: (1/n) times the sum of the elements of all subsets of [n] whose
sum is divisible by n. Offset 1; data 1, 1, 4, 4, 12, 20, 40, 70, 150, 284, 564, 1116, ...
(example in the entry: the subsets of [5] whose sum is divisible by 5 are {}, {5}, {1,4}, {2,3}, {1,4,5},
{2,3,5}, {1,2,3,4}, {1,2,3,4,5}, with total 60, so a(5) = 60/5 = 12).

A063776, name: Number of subsets of {1,2,...,n} which sum to 0 modulo n. Offset 1; data 2, 2, 4, 4, 8, 12, ...
A053636, name: a(n) = Sum_{odd d|n} phi(d)*2^(n/d). Offset 0; data 0, 2, 4, 12, 16, 40, 72, 140, ...

Conjecture (Petros Hadjicostas, Jul 20 2019, in the entry):
a(n) = (n + 1) * A063776(n)/4 - (phi(n)/2) * (1 + (-1)^n)/2
     = ((n + 1)/(4*n)) * A053636(n) - (phi(n)/2) * (1 + (-1)^n)/2.

Conventions:
- `[n] = {1, ..., n}` is `Finset.Icc 1 n`. Every subset counts, including the empty set (sum `0`, divisible
  by `n`) and `[n]` itself, as in the entry's example for `n = 5`.
- `a n` is defined in `ℚ` as `(1/n)` times the total. It is an integer, since every counted subset sum is
  divisible by `n`.
- `phi` is `Nat.totient`. The conjecture is stated for all `n ≥ 1` (the offset of A309128 and A063776), in
  `ℚ`, so the divisions by `4`, `2` and `4*n` are exact rational divisions. The chained equality
  `a(n) = X = Y` is stated as `a n = X ∧ a n = Y`.
- `A053636` follows its name with `n.divisors` (empty for `n = 0`, which gives its first data term
  `A053636 0 = 0`).
-/

namespace OMA.S_oeis_a309128

/-- The subsets of `[n] = {1, ..., n}` whose sum is divisible by `n`. -/
def subsetsDvd (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i)

/-- A309128: `(1/n)` times the sum of the elements of all subsets of `[n]` whose sum is divisible
by `n`. -/
def a (n : ℕ) : ℚ :=
  (1 / (n : ℚ)) * ((∑ S ∈ subsetsDvd n, ∑ i ∈ S, i : ℕ) : ℚ)

/-- A063776: the number of subsets of `{1, 2, ..., n}` which sum to `0` modulo `n`. -/
def A063776 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S => (∑ i ∈ S, i) % n = 0)).card

/-- A053636: `Sum_{odd d | n} phi(d) * 2^(n/d)`. -/
def A053636 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors.filter Odd, Nat.totient d * 2 ^ (n / d)

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = ((n : ℚ) + 1) * (A063776 n : ℚ) / 4 -
        ((Nat.totient n : ℚ) / 2) * (1 + (-1 : ℚ) ^ n) / 2 ∧
    a n = (((n : ℚ) + 1) / (4 * (n : ℚ))) * (A053636 n : ℚ) -
        ((Nat.totient n : ℚ) / 2) * (1 + (-1 : ℚ) ^ n) / 2 := by
  sorry

end OMA.S_oeis_a309128
