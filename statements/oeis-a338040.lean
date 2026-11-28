import Mathlib

/-!
# OEIS A338040

Expansion of e.g.f. `Sum_{j >= 0} 4^j * (exp(j * x) - 1)^j`:
`a(n) = Sum_{j = 0..n} 4^j * j^n * j! * S(n, j)`.

Conjecture (Peter Bala):
Let `p` be prime. The sequence obtained by reducing `a(n)` modulo `p` for `n >= 1` is purely
periodic with period dividing `p - 1` (`a(n + (p - 1)) ≡ a(n) [MOD p]`).
-/

namespace OMA.S_oeis_a338040

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A338040: `a(n) = Sum_{j = 0..n} 4^j * j^n * j! * S(n, j)`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), 4 ^ j * j ^ n * j.factorial * stirling2 n j

theorem main :
    ∀ p n : ℕ, p.Prime → 1 ≤ n → a (n + (p - 1)) ≡ a n [MOD p] := by
  sorry

end OMA.S_oeis_a338040
