import Mathlib

/-!
# OEIS A080253

Number of elements in the Coxeter complex of type `B_n` (or `C_n`):
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * A001333(j + 1)`,
where `A001333` is the numerator sequence of continued fraction convergents to `sqrt(2)`
(`A001333(0) = 1`, `A001333(1) = 1`, `A001333(m + 2) = 2 * A001333(m + 1) + A001333(m)`).

Conjecture (Peter Bala):
For every `k >= 1`, the sequence obtained by reducing `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a080253

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A001333 (`1, 1, 3, 7, 17, 41, ...`). -/
def pellNum : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | m + 2 => 2 * pellNum (m + 1) + pellNum m

/-- Sequence A080253: `a(n) = Sum_{j = 0..n} S(n, j) * j! * pellNum(j + 1)`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * pellNum (j + 1)

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a080253
