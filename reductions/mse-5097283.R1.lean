import OMAStatements.S_mse_5097283

-- Reduction mse-5097283.R1 of Are $1,2,5,10$ the only solutions of $3^{n+1} \pmod {2^n} > 2^n-1.5^n$?
-- Credit: @futurum-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# From a real inequality to a finite check plus an integer tail

Multiplying by `2^n > 0`, the inequality `(3^(n+1) mod 2^n) > 2^n - (3/2)^n` is equivalent to the
natural-number inequality `4^n < (3^(n+1) mod 2^n) * 2^n + 3^n` (lemma `key`).

* `H1`: for `1 ≤ n ≤ 5000` the natural-number inequality holds exactly for `n = 1, 2, 5, 10`
  (a finite computation).
* `H2`: for `n > 5000` it never holds, i.e. `(3^(n+1) mod 2^n) * 2^n + 3^n ≤ 4^n`. Equivalently
  `2^n - (3^(n+1) mod 2^n) ≥ (3/2)^n`: the distance from `3 (3/2)^n` up to the next integer is at
  least `(3/4)^n`. Mahler-type bounds give this only for all sufficiently large `n`, ineffectively.
-/

namespace OMA.R_mse_5097283_R1

/-- The finite range `1 ≤ n ≤ 5000`, in natural-number form. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 5000 →
    (4 ^ n < 3 ^ (n + 1) % 2 ^ n * 2 ^ n + 3 ^ n ↔ n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 10)

/-- The open tail `n > 5000`, in natural-number form. -/
def H2 : Prop :=
  ∀ n : ℕ, 5000 < n → 3 ^ (n + 1) % 2 ^ n * 2 ^ n + 3 ^ n ≤ 4 ^ n

lemma key (n r : ℕ) : ((r : ℝ) > 2 ^ n - (3 / 2 : ℝ) ^ n) ↔ 4 ^ n < r * 2 ^ n + 3 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have e : (3 / 2 : ℝ) ^ n = 3 ^ n / 2 ^ n := by rw [div_pow]
  have e4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [gt_iff_lt, e, sub_lt_iff_lt_add, ← @Nat.cast_lt ℝ]
  push_cast
  rw [e4]
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h h2
    rw [add_mul, div_mul_cancel₀ _ h2.ne'] at this
    linarith
  · intro h
    by_contra hc
    have := mul_le_mul_of_nonneg_right (not_lt.mp hc) h2.le
    rw [add_mul, div_mul_cancel₀ _ h2.ne'] at this
    linarith

theorem main : H1 → H2 → type_of% @OMA.S_mse_5097283.main := by
  intro h1 h2 n hn
  rw [key n]
  rcases le_or_gt n 5000 with h | h
  · exact h1 n hn h
  · have h' := h2 n h
    constructor
    · intro hc
      exact absurd hc (not_lt.mpr h')
    · rintro (rfl | rfl | rfl | rfl) <;> omega

end OMA.R_mse_5097283_R1
