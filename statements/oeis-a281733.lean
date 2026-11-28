import Mathlib

/-!
# A281733: the positive integers T_i of Sun (2013)

Source: https://oeis.org/A281733
Credit: @rpabani

Conjecture (Sun 2013, Conjecture 4, as quoted in OEIS A281733): T_p == -2 (mod p) for any prime p.

The source defines T_i through a power series identity and also gives the closed form
a(n) = 16^(n-1) * binomial(3*n-2, 2*n-1) / n (Sarah Selkirk, 2020), offset 1. The closed form is
used here. It reproduces the listed terms 1, 32, 1792, 122880, 9371648, and the division is exact
because binomial(3*n-2, 2*n-1) / n = binomial(3*n-2, n-1) / n is an integer (OEIS A006013).
-/

namespace OMA.S_oeis_a281733

/-- `T n` is OEIS A281733 (offset 1), by its closed form. -/
def T (n : ℕ) : ℕ := 16 ^ (n - 1) * Nat.choose (3 * n - 2) (2 * n - 1) / n

theorem main : ∀ p : ℕ, p.Prime → (T p : ℤ) ≡ -2 [ZMOD (p : ℤ)] := by
  sorry

end OMA.S_oeis_a281733
