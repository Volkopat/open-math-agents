import Mathlib

/-!
# A004981: a(n) = (2^n/n!) * Product_{k=0..n-1} (4*k + 1).

Source: https://oeis.org/A004981
Credit: @divmxnd0x

Conjecture (Peter Bala, Dec 22 2019, stated in A004981): `a(p n) ≡ a(n) (mod p^2)` for every
prime `p ≡ 1 (mod 4)` and all positive integers `n`.

Formalization notes:
* `a n = 2^n (1·5·9···(4n-3)) / n!`; the division is exact (the terms `1, 2, 10, 60, 390, ...`
  are integers), so it is taken in `ℕ`.
-/

namespace OMA.S_oeis_a004981

/-- A004981(n) = (2^n / n!) ∏_{k=0}^{n-1} (4k + 1). -/
def a (n : ℕ) : ℕ := 2 ^ n * (∏ k ∈ Finset.range n, (4 * k + 1)) / n.factorial

/-- Bala's congruence for primes `p ≡ 1 (mod 4)`. -/
theorem main : ∀ p n : ℕ, p.Prime → p % 4 = 1 → 0 < n → a (p * n) ≡ a n [MOD p ^ 2] := by
  sorry

end OMA.S_oeis_a004981
