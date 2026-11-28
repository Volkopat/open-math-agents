import Mathlib

/-!
# OEIS A113052

Source: https://oeis.org/A113052 (OEIS Foundation, CC BY-SA 4.0).
Credit: @bcrowther86-eng

A113052(n) = binomial(5n, n)/(4n + 1) mod 5, the Fuss-Catalan numbers of order 5 reduced mod 5.
Data (from n = 0): 1, 1, 0, 0, 0, 0, 1, 0, ...

The entry states:
Conjecture: for p prime, mod(C(pn,n)/((p-1)n+1),p) is the indicator function of the sequence
(p^k-1)/(p-1).

`C(pn, n)` is always divisible by `(p-1)n + 1` (it is `(p-1)n + 1` times the Fuss-Catalan number),
so `/` below is exact division. The sequence `(p^k - 1)/(p - 1)`, `k ≥ 0`, is `0, 1, p + 1, ...`
(the repunits in base `p`), and `n = 0` belongs to it, matching `a(0) = 1`.
-/

namespace OMA.S_oeis_a113052

/-- The Fuss-Catalan number `C(pn, n) / ((p-1)n + 1)`. -/
def fussCatalan (p n : ℕ) : ℕ := Nat.choose (p * n) n / ((p - 1) * n + 1)

theorem main : ∀ p n : ℕ, p.Prime →
    ((∃ k : ℕ, n = (p ^ k - 1) / (p - 1)) → fussCatalan p n % p = 1) ∧
    ((¬ ∃ k : ℕ, n = (p ^ k - 1) / (p - 1)) → fussCatalan p n % p = 0) := by
  sorry

end OMA.S_oeis_a113052
