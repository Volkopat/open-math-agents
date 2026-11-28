import Mathlib

/-!
# A220947: Least prime p such that sum_{k=0}^n F(k+1)*x^{n-k} is irreducible modulo p, where F(j) denotes the Fibonacci number A000045(j).

Source: https://oeis.org/A220947
Credit: @eltociear

For `n ≥ 1` let `f_n(x) = ∑_{k=0}^n F(k+1) x^(n-k)`, where `F` is the Fibonacci sequence
(`F(1) = F(2) = 1`); it is monic of degree `n` (`f_2 = x^2 + x + 2`). `a(n)` (offset 1) is the
least prime `p` such that `f_n` is irreducible modulo `p` (`a(2) = 3`: `x^2 + x + 2` is reducible
modulo `2` but irreducible modulo `3`). The entry conjectures (Zhi-Wei Sun):

  a(n) <= n^2+12 for all n>0.

`main` states the equivalent form: for every `n ≥ 1` there is a prime `p ≤ n^2 + 12` such that
`f_n` reduced modulo `p` is irreducible in `(ZMod p)[X]`. (The least such prime is then also
`≤ n^2 + 12`, and conversely.) `Nat.fib (k + 1)` is `F(k+1)`.
-/

namespace OMA.S_oeis_a220947

open Polynomial

/-- `f_n(x) = ∑_{k=0}^n F(k+1) x^(n-k)` with coefficients reduced modulo `p`. -/
noncomputable def f (p n : ℕ) : (ZMod p)[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((Nat.fib (k + 1) : ℕ) : ZMod p) * X ^ (n - k)

/-- The conjecture in OEIS A220947: for every `n ≥ 1` some prime `p ≤ n^2 + 12` makes `f_n`
irreducible modulo `p`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ p ≤ n ^ 2 + 12 ∧ Irreducible (f p n) := by
  sorry

end OMA.S_oeis_a220947
-- ci: re-run check-proof
