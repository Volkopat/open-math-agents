import Mathlib

/-!
# OEIS A285999: odd divisors minus middle divisors, summed up to `n`

Source: https://oeis.org/A285999 (OEIS Foundation, CC BY-SA 4.0).

`a(n)` is the total number of odd divisors of all positive integers `≤ n`, minus the total number
of middle divisors of all positive integers `≤ n`. Offset 1; the data begins
`0, 0, 2, 2, 4, 4, 6, 6, 8, 10, 12, 12, ...`.
* The number of odd divisors of `j` is A001227(j).
* The number of middle divisors of `j` is A067742(j): the divisors of `j` in the half-open interval
  `[sqrt(j/2), sqrt(j*2))`.

Conjecture 1 (Omar E. Pol, comments of the entry): `a(n)` is also twice the total number of
partitions of all positive integers `≤ n` into an even number of consecutive parts. (The formula
section's `a(n) = 2*A285902(n)` says the same, A285902(n) being that total.)

Formalization notes:
* A partition of `j` into consecutive parts is a pair `(s, k)` with `s, k ≥ 1` and
  `s + (s + 1) + ... + (s + k - 1) = j` (smallest part `s`, `k` parts); both `s` and `k` are then
  at most `j`. A131576(j) counts those with `k` even.
* Conjecture 2 and the other formula conjecture involve the symmetric representation of sigma and
  the Dyck paths of A237593; they are not stated here.
* The subtraction defining `a(n)` is in `ℕ`; the conjecture is stated for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a285999

/-- A001227(j): the number of odd divisors of `j`. -/
def A001227 (j : ℕ) : ℕ := (j.divisors.filter Odd).card

open Classical in
/-- A067742(j): the number of divisors of `j` in the half-open interval `[sqrt(j/2), sqrt(j*2))`. -/
noncomputable def A067742 (j : ℕ) : ℕ :=
  (j.divisors.filter
    (fun d : ℕ => Real.sqrt ((j : ℝ) / 2) ≤ (d : ℝ) ∧ (d : ℝ) < Real.sqrt ((j : ℝ) * 2))).card

/-- A285999(n): total number of odd divisors of `1, ..., n` minus their total number of middle
divisors. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ j ∈ Finset.Icc 1 n, A001227 j) - ∑ j ∈ Finset.Icc 1 n, A067742 j

/-- Partitions of `j` into consecutive parts: pairs `(s, k)` with `s, k ≥ 1` and
`s + (s + 1) + ... + (s + k - 1) = j`. -/
def reps (j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 j ×ˢ Finset.Icc 1 j).filter (fun p => ∑ i ∈ Finset.range p.2, (p.1 + i) = j)

/-- A131576(j): the number of partitions of `j` into an even number of consecutive parts. -/
def A131576 (j : ℕ) : ℕ := ((reps j).filter (fun p => Even p.2)).card

/-- Pol's Conjecture 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 2 * ∑ j ∈ Finset.Icc 1 n, A131576 j := by
  sorry

end OMA.S_oeis_a285999
