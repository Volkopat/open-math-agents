import Mathlib

/-!
# A341063: a(n) = Sum_{i+j<=m+1} t_i * t_j, where t_1 < ... < t_m are the totatives of n.

Source: https://oeis.org/A341063
Credit: @ceejcake

Conjecture (OEIS A341063): If `p` and `q` are distinct primes, then
`a(p*q) = (p^2-p)*(q^2-q)*(p^2*q^2-p^2*q-p*q^2+p*q+2*p+2*q)/24`.

Formalization notes:
* The sequence has offset `1` (`n ≥ 1`).
* `totatives n` lists the integers `1 ≤ k ≤ n` with `Nat.Coprime k n` in strictly increasing order
  `t_1 < ... < t_m` (for `n = 1`, `totatives 1 = [1]` and `a 1 = 1`).
* Under 0-based indexing (`i, j : Fin m`), the 1-based condition `(i + 1) + (j + 1) ≤ m + 1` is
  equivalently `i.1 + j.1 < m`, summing over all ordered pairs `(i, j)` satisfying this inequality
  (e.g., for `n = 8`, `totatives 8 = [1, 3, 5, 7]` and
  `a 8 = 1*(1+3+5+7) + 3*(1+3+5) + 5*(1+3) + 7*1 = 70`).
* The conjectured formula is stated in `ℤ` cleared of the denominator `24` (`24 * (a (p * q) : ℤ) = ...`),
  avoiding both truncated `ℕ` subtraction and integer floor division.
* Initial values for `n = 1, 2, ..., 12`:
  `a(n) = 1, 1, 5, 7, 35, 11, 126, 70, 177, 90, 715, 142, ...`.
-/

namespace OMA.S_oeis_a341063

/-- The totatives of `n`, i.e., integers `1 ≤ k ≤ n` coprime to `n`, in strictly increasing order. -/
def totatives (n : ℕ) : List ℕ :=
  (List.range' 1 n).filter (fun k => decide (Nat.Coprime k n))

/-- `a n = ∑_{i+j ≤ m+1} t_i * t_j` where `t_1 < ... < t_m` are the totatives of `n`
(equivalently `∑_{i+j < m} t[i] * t[j]` under 0-based indexing). -/
def a (n : ℕ) : ℕ :=
  let t := totatives n
  ∑ i : Fin t.length, ∑ j : Fin t.length, if i.1 + j.1 < t.length then t[i] * t[j] else 0

/-- OEIS A341063 conjecture: for distinct primes `p` and `q`,
`24 * a(p * q) = (p^2 - p) * (q^2 - q) * (p^2 * q^2 - p^2 * q - p * q^2 + p * q + 2 * p + 2 * q)`. -/
theorem main :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      24 * (a (p * q) : ℤ) =
        ((p : ℤ) ^ 2 - p) * ((q : ℤ) ^ 2 - q) *
          ((p : ℤ) ^ 2 * (q : ℤ) ^ 2 - (p : ℤ) ^ 2 * q - p * (q : ℤ) ^ 2 +
            p * q + 2 * p + 2 * q) := by
  sorry

end OMA.S_oeis_a341063
