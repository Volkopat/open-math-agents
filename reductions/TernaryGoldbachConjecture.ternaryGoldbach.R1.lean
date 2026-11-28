import FormalConjectures.Wikipedia.GoldbachConjecture

-- Reduction TernaryGoldbachConjecture.ternaryGoldbach.R1 of the ternary Goldbach conjecture
-- Credit: @pyaf

/-!
Helfgott's proof of the ternary Goldbach conjecture, split into its three published inputs.

* `H1`: the analytic theorem (H. A. Helfgott, The ternary Goldbach problem, arXiv:1501.05438,
  Main Theorem): every odd `n ≥ 10 ^ 27` is a sum of three primes.
* `H2`: binary Goldbach up to `4 * 10 ^ 18` (T. Oliveira e Silva, S. Herzog, S. Pardi,
  Math. Comp. 83 (2014), 2033–2060).
* `H3`: the prime ladder (H. A. Helfgott, D. J. Platt, Numerical verification of the ternary
  Goldbach conjecture up to 8.875e30, Exp. Math. 22 (2013)): below `10 ^ 27` every window of
  length `4 * 10 ^ 18 - 4` contains a prime.

Proved here: an odd `n` below `10 ^ 27` is `3 + (n - 3)` when `n - 3 ≤ 4 * 10 ^ 18`, and otherwise
`p + (n - p)` with `p` a ladder prime in `[n - 4 * 10 ^ 18, n - 4]`, the even remainder `n - p`
being a sum of two primes by `H2`.
-/

namespace OMA.R_TernaryGoldbachConjecture_ternaryGoldbach_R1

/-- Helfgott's analytic theorem. -/
def H1 : Prop :=
  ∀ n : ℕ, 10 ^ 27 ≤ n → Odd n → ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

/-- Binary Goldbach up to `4 * 10 ^ 18`. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ 4 * 10 ^ 18 → Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- Prime gaps below `10 ^ 27` are less than `4 * 10 ^ 18 - 4`. -/
def H3 : Prop :=
  ∀ x : ℕ, 4 * 10 ^ 18 ≤ x → x ≤ 10 ^ 27 → ∃ p, Nat.Prime p ∧ p ≤ x ∧ x ≤ p + (4 * 10 ^ 18 - 4)

theorem main : H1 → H2 → H3 → type_of% @TernaryGoldbachConjecture.ternaryGoldbach := by
  intro h1 h2 h3 n hn hodd
  by_cases hbig : 10 ^ 27 ≤ n
  · exact h1 n hbig hodd
  obtain ⟨k, rfl⟩ := hodd
  by_cases hsmall : 2 * k + 1 - 3 ≤ 4 * 10 ^ 18
  · obtain ⟨q, r, hq, hr, hqr⟩ := h2 (2 * k + 1 - 3) (by omega) hsmall ⟨k - 1, by omega⟩
    exact ⟨3, q, r, Nat.prime_three, hq, hr, by omega⟩
  obtain ⟨p, hp, hpx, hxp⟩ := h3 (2 * k + 1 - 4) (by omega) (by omega)
  obtain ⟨j, rfl⟩ := hp.eq_two_or_odd'.resolve_left (by omega)
  obtain ⟨q, r, hq, hr, hqr⟩ := h2 (2 * k + 1 - (2 * j + 1)) (by omega) (by omega) ⟨k - j, by omega⟩
  exact ⟨2 * j + 1, q, r, hp, hq, hr, by omega⟩

end OMA.R_TernaryGoldbachConjecture_ternaryGoldbach_R1
