import Mathlib

/-!
# A220949: least prime p such that Sum_{k=0..n} (2k+1)*x^(n-k) is irreducible modulo p

Source: https://oeis.org/A220949

A220949 (offset 1): `a(n)` is the least prime `p` such that `Sum_{k=0..n} (2k+1)*x^(n-k)` is
irreducible modulo `p`: 2, 2, 3, 2, 5, 3, 71, 23, 11, 2, …  For example `a(5) = 5` since
`x^5 + 3*x^4 + 5*x^3 + 7*x^2 + 9*x + 11` is irreducible modulo 5 but reducible modulo 2 and 3.
The entry notes that `a(7) = 71 = 7^2 + 22`.

Conjecture (Zhi-Wei Sun, Apr 07 2013): `a(n) ≤ n^2 + 22` for all `n > 0`.

Since `a(n)` is the least prime `p` modulo which the polynomial is irreducible, the bound
`a(n) ≤ n^2 + 22` holds exactly when some such prime is at most `n^2 + 22`, and the conjecture
is stated in that form. The entry's remark about similar conjectures with `(2k+1)^m` is a
separate claim and is not part of this statement.

Conventions: `P n` is the polynomial `Sum_{k=0..n} (2k+1)*x^(n-k)` with integer coefficients;
its reduction modulo `p` is its image under `Int.castRingHom (ZMod p)`, and irreducibility
modulo `p` is `Irreducible` in the polynomial ring over `ZMod p`.
-/

namespace OMA.S_oeis_a220949

/-- The integer polynomial `Sum_{k=0..n} (2k+1)*x^(n-k)`. -/
noncomputable def P (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (2 * (k : ℤ) + 1) * Polynomial.X ^ (n - k)

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ p : ℕ, Nat.Prime p ∧ p ≤ n ^ 2 + 22 ∧
        Irreducible ((P n).map (Int.castRingHom (ZMod p))) := by
  sorry

end OMA.S_oeis_a220949
