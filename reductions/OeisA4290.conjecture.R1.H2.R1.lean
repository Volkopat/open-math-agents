import OMAReductions.R_OeisA4290_conjecture_R1

-- Reduction OeisA4290.conjecture.R1.H2.R1 of step OeisA4290.conjecture.R1.H2
-- Credit: @marcusbuffett

/-!
# Two provable families in the non-coprime case of Radcliffe's question on A004290

The parent step asks, for every `n < 10^k - 1` sharing a factor with `10`, for a positive multiple
of `n` with decimal digits `0` and `1` below the repunit `(10^(9k) - 1) / 9`.

Write such an `n` as a divisor of `10^e * d` with `e > 0` (so `e` bounds the exponents of `2` and
`5` in `n`, and `d` carries the part coprime to `10`).

* `H1` (digit stacking, shifted). If `d` divides `10^t - 1` and `9t + e ≤ 9k`: stack the decimal
  digits of `d` in `9` blocks of length `t`, which gives a 0/1 multiple of `d` with at most `9t`
  digits, and append `e` zeros. This contains the family `n = 8 * (10^(k-1) - 1)`, for which the
  least 0/1 multiple has `9k - 6` digits, the largest value found among all `n < 10^k - 1` for
  `k ≤ 4`.
* `H2` (short repunits, shifted). If `9d` divides `10^t - 1` and `t + e ≤ 9k`: the repunit with
  `t` digits followed by `e` zeros.
* `H3` is everything else in the non-coprime case, and stays open.

`main` is the case distinction.
-/

namespace OMA.R_OeisA4290_conjecture_R1_H2_R1

/-- Digit stacking followed by `e` zeros. -/
def H1 : Prop :=
  ∀ k n d e t : ℕ, 0 < n → n < 10 ^ k - 1 → 0 < e → 0 < t →
    n ∣ 10 ^ e * d → d ∣ 10 ^ t - 1 → 9 * t + e ≤ 9 * k →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

/-- A repunit followed by `e` zeros. -/
def H2 : Prop :=
  ∀ k n d e t : ℕ, 0 < n → n < 10 ^ k - 1 → 0 < e → 0 < t →
    n ∣ 10 ^ e * d → 9 * d ∣ 10 ^ t - 1 → t + e ≤ 9 * k →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

/-- The open remainder of the non-coprime case. -/
def H3 : Prop :=
  ∀ k n : ℕ, 0 < n → n < 10 ^ k - 1 → ¬ Nat.Coprime n 10 →
    (∀ d e t : ℕ, 0 < e → 0 < t → n ∣ 10 ^ e * d → d ∣ 10 ^ t - 1 → ¬ 9 * t + e ≤ 9 * k) →
    (∀ d e t : ℕ, 0 < e → 0 < t → n ∣ 10 ^ e * d → 9 * d ∣ 10 ^ t - 1 → ¬ t + e ≤ 9 * k) →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

theorem main : H1 → H2 → H3 → OMA.R_OeisA4290_conjecture_R1.H2 := by
  intro h1 h2 h3 k n hn hlt hco
  by_cases c1 : ∃ d e t : ℕ, 0 < e ∧ 0 < t ∧ n ∣ 10 ^ e * d ∧ d ∣ 10 ^ t - 1 ∧ 9 * t + e ≤ 9 * k
  · obtain ⟨d, e, t, he, ht, hnd, hd, hle⟩ := c1
    exact h1 k n d e t hn hlt he ht hnd hd hle
  by_cases c2 : ∃ d e t : ℕ, 0 < e ∧ 0 < t ∧ n ∣ 10 ^ e * d ∧ 9 * d ∣ 10 ^ t - 1 ∧ t + e ≤ 9 * k
  · obtain ⟨d, e, t, he, ht, hnd, hd, hle⟩ := c2
    exact h2 k n d e t hn hlt he ht hnd hd hle
  exact h3 k n hn hlt hco
    (fun d e t he ht hnd hd hle => c1 ⟨d, e, t, he, ht, hnd, hd, hle⟩)
    (fun d e t he ht hnd hd hle => c2 ⟨d, e, t, he, ht, hnd, hd, hle⟩)

end OMA.R_OeisA4290_conjecture_R1_H2_R1
