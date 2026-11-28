import Mathlib

/-!
# OEIS A034836: boxes with integer edges and volume `n`

Source: https://oeis.org/A034836 (OEIS Foundation, CC BY-SA 4.0).

`a(n)` is the number of ways to write `n` as `n = x * y * z` with `1 ≤ x ≤ y ≤ z`.
Offset 1; the data begins `1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, ...`.

Conjecture (Ton Biegstraaten, Jan 04 2016, formula section of the entry): let
`s(1), ..., s(m)` be the signature of `n` (the exponents of its prime factorization) and put
* `np = ∏_{k=1..m} binomial(2 + s(k), 2)`,
* `ntp = ∏_{k=1..m} floor((s(k) - (s(k) mod 3)) / s(k))` (`1` if `n` is a cube, else `0`),
* `nsq = ∏_{k=1..m} (floor(s(k) / 2) + 1)` (the number of squares dividing `n`).

Then `a(n) = (np + 3 * (nsq - ntp) + 5 * ntp) / 6 = (np + 3 * nsq + 2 * ntp) / 6`.

Formalization notes:
* The signature is read off `n.factorization` on `n.primeFactors`, so each product runs over
  the prime factors of `n`; for `n = 1` all three products are empty and equal `1`.
* `a n` counts triples in `[1, n]^3`, which contains every factorization of `n ≥ 1`.
* Both displayed forms are stated, with natural-number division and subtraction, for every
  `n ≥ 1` (the entry's range).
-/

namespace OMA.S_oeis_a034836

/-- A034836(n): the number of ways to write `n = x * y * z` with `1 ≤ x ≤ y ≤ z`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 * t.2.1 * t.2.2 = n)).card

/-- `np = ∏ binomial(2 + s(k), 2)` over the signature of `n`. -/
def np (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, (2 + n.factorization p).choose 2

/-- `ntp = ∏ floor((s(k) - (s(k) mod 3)) / s(k))` over the signature of `n`. -/
def ntp (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, (n.factorization p - n.factorization p % 3) / n.factorization p

/-- `nsq = ∏ (floor(s(k) / 2) + 1)` over the signature of `n`. -/
def nsq (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, (n.factorization p / 2 + 1)

/-- Biegstraaten's conjecture, in both of its displayed forms. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = (np n + 3 * (nsq n - ntp n) + 5 * ntp n) / 6 ∧
      a n = (np n + 3 * nsq n + 2 * ntp n) / 6 := by
  sorry

end OMA.S_oeis_a034836
