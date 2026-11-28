import Mathlib

/-!
# A176477: a(1)=2; for n >= 2, (2n+1)^3*a(n) = 32n^3*a(n-1) + (21n^3 + 22n^2 + 8n + 1)*binomial(2n-1,n)^4.

Source: https://oeis.org/A176477
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, Apr 06 2010, from the entry):
1. each term a(n) is a positive integer;
2. a(n) is odd if and only if n = 2, 2^2, 2^3, ...;
3. for any prime p > 5,
   Sum_{k=0..p-1} (21k^3 + 22k^2 + 8k + 1)*binomial(2k,k)^7/256^k == p^3 (mod p^8).
(A further series identity mentioned in the entry is not stated here.)

Formalization notes:
* a(n) is defined in ℚ by the recurrence in the name (offset 1; the value at 0 is unused).
* Conjecture 2 is stated for the integer values: whenever a(n) = m with m ∈ ℕ, m is odd iff
  n = 2^k for some k ≥ 1.
* In conjecture 3 the denominators 256^k are units modulo p; multiplying by 256^(p-1), the
  congruence is stated in ℤ as
  p^8 | Sum_{k<p} (21k^3+22k^2+8k+1) C(2k,k)^7 256^(p-1-k) - p^3 256^(p-1).
* Controls (computed): a(1..5) = 2, 181, 23488, 3625081, 619898336, as in the entry; for n < 40
  every a(n) is a positive integer, odd exactly at n = 2, 4, 8, 16, 32; conjecture 3 holds for
  7 ≤ p < 40.
-/

namespace OMA.S_oeis_a176477

/-- A176477, defined in `ℚ` by its recurrence. -/
def a : ℕ → ℚ
  | 0 => 0
  | 1 => 2
  | (n + 2) =>
    (32 * ((n + 2 : ℕ) : ℚ) ^ 3 * a (n + 1) +
        (21 * ((n + 2 : ℕ) : ℚ) ^ 3 + 22 * ((n + 2 : ℕ) : ℚ) ^ 2 + 8 * ((n + 2 : ℕ) : ℚ) + 1) *
          (((2 * (n + 2) - 1).choose (n + 2) : ℕ) : ℚ) ^ 4) /
      (2 * ((n + 2 : ℕ) : ℚ) + 1) ^ 3

/-- Sun's three conjectures. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ a n = m) ∧
      (∀ n m : ℕ, 1 ≤ n → a n = m → (Odd m ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k)) ∧
      ∀ p : ℕ, p.Prime → 5 < p →
        ((p : ℤ) ^ 8 ∣ (∑ k ∈ Finset.range p,
            ((21 * k ^ 3 + 22 * k ^ 2 + 8 * k + 1) * ((2 * k).choose k) ^ 7 * 256 ^ (p - 1 - k) : ℕ) : ℤ) -
          (p : ℤ) ^ 3 * 256 ^ (p - 1)) := by
  sorry

end OMA.S_oeis_a176477
