import Mathlib

/-!
# A064671: base 4 biquanimous strings of length n

Source: https://oeis.org/A064671

`a(n)` (offset 1) is the number of n-digit base 4 biquanimous numbers, with leading zeros
allowed but not the all-zero string. A number is biquanimous (A064544) if its digits can be
split into two groups with the same sum. The entry records the conjectures (Colin Barker, 2017)

  `a(n) = (2^n-2) * (1+2^n-n) / 2`, and
  `a(n) = 10*a(n-1) - 37*a(n-2) + 64*a(n-3) - 52*a(n-4) + 16*a(n-5)` for `n > 5`.

## Encoding

* An n-digit base 4 string with leading zeros allowed is a function `f : Fin n → Fin 4`
  (digit `i` is `f i`); the all-zero string is `f = 0`.
* The digits split into two groups with equal sum when some set `S` of positions satisfies
  `Sum_{i ∈ S} f i = Sum_{i ∉ S} f i` (digits read as natural numbers).
* Both conjectured identities are stated over `ℤ`; `/` is integer division (the product
  `(2^n - 2) * (1 + 2^n - n)` is even for `n ≥ 1`).
-/

namespace OMA.S_oeis_a064671

/-- `a n` is the number of strings `f` of `n` base 4 digits, not all zero, whose digits can be
split into two groups with the same sum (A064671). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 4)).filter
    (fun f => f ≠ 0 ∧ ∃ S : Finset (Fin n), ∑ i ∈ S, (f i : ℕ) = ∑ i ∈ Sᶜ, (f i : ℕ))).card

/-- **Barker's conjectures for A064671**: `a(n) = (2^n-2) * (1+2^n-n) / 2` for `n ≥ 1`, and
`a(n) = 10*a(n-1) - 37*a(n-2) + 64*a(n-3) - 52*a(n-4) + 16*a(n-5)` for `n > 5`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = (2 ^ n - 2) * (1 + 2 ^ n - n) / 2) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10 * a (n - 1) - 37 * a (n - 2) + 64 * a (n - 3) -
      52 * a (n - 4) + 16 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a064671
