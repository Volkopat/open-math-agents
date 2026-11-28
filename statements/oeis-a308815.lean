import Mathlib

/-!
# A308815: `16^n * Sum_{i=0..n} (-2)^i * binomial(n, i) * Catalan(2n-i)`

Source: https://oeis.org/A308815 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

Offset `0`, data `1, 0, 512, 32768, 3014656, 285212672, 28521267200, ...`.

Note on the sign: the OEIS name prints `a(n) = 16^n*Sum_{i=0..n} 2^i*binomial(n, i)*Catalan(2*n-i)`,
but that formula gives `1, 64, 10752, ...`, which does not match the listed data. The data, and
the conjectured recurrence below, match `(-2)^i` in place of `2^i` (for example
`a(1) = 16*(Catalan(2) - 2*Catalan(1)) = 0`). We formalize the sequence with the sign `(-2)^i`
that matches the data.

Conjecture (R. J. Mathar, Jan 27 2020): `a(n)` is D-finite with recurrence
`n*(2*n+1)*a(n) -32*(9*n-4)*(n-1)*a(n-1) +1024*(3*n^2-23*n+29)*a(n-2)
 +65536*(n-2)*(2*n-5)*a(n-3) = 0`, for `n ≥ 3` (the indices where `a(n-3)` is defined).
-/

namespace OMA.S_oeis_a308815

/-- A308815 (with the sign that matches the OEIS data):
`a(n) = 16^n * ∑_{i=0..n} (-2)^i * C(n,i) * Catalan(2n-i)`. -/
def a (n : ℕ) : ℤ :=
  16 ^ n * ∑ i ∈ Finset.range (n + 1), (-2 : ℤ) ^ i * (n.choose i : ℤ) * (catalan (2 * n - i) : ℤ)

/-- Conjecture (R. J. Mathar): the order-3 recurrence of A308815, for `n ≥ 3`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      (n : ℤ) * (2 * n + 1) * a n - 32 * (9 * (n : ℤ) - 4) * (n - 1) * a (n - 1)
        + 1024 * (3 * (n : ℤ) ^ 2 - 23 * n + 29) * a (n - 2)
        + 65536 * ((n : ℤ) - 2) * (2 * n - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a308815
