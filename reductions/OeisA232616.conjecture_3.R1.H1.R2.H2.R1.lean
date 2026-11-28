import OMAReductions.R_OeisA232616_conjecture_3_R1_H1_R2
import Mathlib

-- Reduction OeisA232616.conjecture_3.R1.H1.R2.H2.R1 of step OeisA232616.conjecture_3.R1.H1.R2.H2
-- Credit: @rickmanelius

/-!
# A232616, conjecture 3, `x` odd and `x + n ≡ 0 (mod 4)`: the sieve modulo `15`

The step asks that `x^n + n ≠ z^2` for odd `x > 1` that is not a square, `z > 1` and odd
`n > 1` with `x + n ≡ 0 (mod 4)`.

Proved below, with no hypothesis, from Fermat's little theorem (`fermat_three`, `fermat_five`):

* `pow_mod_three`: since `n` is odd, `x^n ≡ x (mod 3)`, so `z^2 ≡ x + n (mod 3)` and
  `x + n ≢ 2 (mod 3)`;
* `pow_mod_five` and `pow_mod_five_three`: `x + n ≡ 0 (mod 4)` ties `n` modulo `4` to `x`. For
  `x ≡ 3 (mod 4)`, `n ≡ 1 (mod 4)` and `x^n ≡ x (mod 5)`; for `x ≡ 1 (mod 4)`, `n ≡ 3 (mod 4)`
  and `x^n ≡ x^3 (mod 5)`. Since squares modulo `5` are `0, 1, 4` (`sq_mod_five`), `x + n`,
  respectively `x^3 + n`, is not `2` or `3` modulo `5`.

Each hypothesis is the step restricted to one class of `x` modulo `4`, with these residues.

* `H1`: `x ≡ 1 (mod 4)`.
* `H2`: `x ≡ 3 (mod 4)`.
-/

namespace OMA.R_OeisA232616_conjecture_3_R1_H1_R2_H2_R1


/-- Fermat for `3`: `x^3 ≡ x (mod 3)`. -/
lemma fermat_three (x : ℕ) : x ^ 3 % 3 = x % 3 := by
  rw [Nat.pow_mod]
  have hlt : x % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases h : x % 3 <;> norm_num

/-- Fermat for `5`: `x^5 ≡ x (mod 5)`. -/
lemma fermat_five (x : ℕ) : x ^ 5 % 5 = x % 5 := by
  rw [Nat.pow_mod]
  have hlt : x % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases h : x % 5 <;> norm_num

/-- For odd exponents, `x^(2k+1) ≡ x (mod 3)`. -/
lemma pow_mod_three (x k : ℕ) : x ^ (2 * k + 1) % 3 = x % 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : x ^ (2 * (k + 1) + 1) = x ^ (2 * k + 1) * x ^ 2 := by ring
    rw [h, Nat.mul_mod, ih, ← Nat.mul_mod, show x * x ^ 2 = x ^ 3 by ring, fermat_three]

/-- For exponents `≡ 1 (mod 4)`, `x^(4k+1) ≡ x (mod 5)`. -/
lemma pow_mod_five (x k : ℕ) : x ^ (4 * k + 1) % 5 = x % 5 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : x ^ (4 * (k + 1) + 1) = x ^ (4 * k + 1) * x ^ 4 := by ring
    rw [h, Nat.mul_mod, ih, ← Nat.mul_mod, show x * x ^ 4 = x ^ 5 by ring, fermat_five]

/-- For exponents `≡ 3 (mod 4)`, `x^(4k+3) ≡ x^3 (mod 5)`. -/
lemma pow_mod_five_three (x k : ℕ) : x ^ (4 * k + 3) % 5 = x ^ 3 % 5 := by
  have h : x ^ (4 * k + 3) = x ^ (4 * k + 1) * x ^ 2 := by ring
  rw [h, Nat.mul_mod, pow_mod_five, ← Nat.mul_mod, show x * x ^ 2 = x ^ 3 by ring]

/-- Squares modulo `3` are `0` or `1`. -/
lemma sq_mod_three (z : ℕ) : z ^ 2 % 3 = 0 ∨ z ^ 2 % 3 = 1 := by
  rw [Nat.pow_mod]
  have hlt : z % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases h : z % 3 <;> norm_num

/-- Squares modulo `5` are `0`, `1` or `4`. -/
lemma sq_mod_five (z : ℕ) : z ^ 2 % 5 = 0 ∨ z ^ 2 % 5 = 1 ∨ z ^ 2 % 5 = 4 := by
  rw [Nat.pow_mod]
  have hlt : z % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases h : z % 5 <;> norm_num

/-- The step for `x ≡ 1 (mod 4)`, with `x + n ≢ 2 (mod 3)` and `x^3 + n ≡ 0, 1` or
`4 (mod 5)`. -/
def H1 : Prop := ∀ x z n : ℕ, 1 < x → 1 < z → 1 < n → ¬ 2 ∣ n → Odd x → (x + n) % 4 = 0 →
    ¬ IsSquare x → x % 4 = 1 → ((x + n) % 3 = 0 ∨ (x + n) % 3 = 1) →
    ((x ^ 3 + n) % 5 = 0 ∨ (x ^ 3 + n) % 5 = 1 ∨ (x ^ 3 + n) % 5 = 4) → x ^ n + n ≠ z ^ 2

/-- The step for `x ≡ 3 (mod 4)`, with `x + n ≢ 2 (mod 3)` and `x + n ≡ 0, 1` or
`4 (mod 5)`. -/
def H2 : Prop := ∀ x z n : ℕ, 1 < x → 1 < z → 1 < n → ¬ 2 ∣ n → Odd x → (x + n) % 4 = 0 →
    ¬ IsSquare x → x % 4 = 3 → ((x + n) % 3 = 0 ∨ (x + n) % 3 = 1) →
    ((x + n) % 5 = 0 ∨ (x + n) % 5 = 1 ∨ (x + n) % 5 = 4) → x ^ n + n ≠ z ^ 2

theorem main : H1 → H2 → OMA.R_OeisA232616_conjecture_3_R1_H1_R2.H2 := by
  intro h1 h2 x z n hx hz hn hn2 hxo hx4 hxsq heq
  have hx3 : x ^ n % 3 = x % 3 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [hk]
    exact pow_mod_three x k
  have hz3 := sq_mod_three z
  have hz5 := sq_mod_five z
  have hm3 : (x + n) % 3 = 0 ∨ (x + n) % 3 = 1 := by
    have e := heq
    generalize x ^ n = A at hx3 e
    generalize z ^ 2 = B at hz3 e
    omega
  have hxm : x % 4 = 1 ∨ x % 4 = 3 := by
    obtain ⟨k, hk⟩ := hxo
    omega
  rcases hxm with hxm | hxm
  · have hx5 : x ^ n % 5 = x ^ 3 % 5 := by
      obtain ⟨j, hj⟩ : ∃ j, n = 4 * j + 3 := ⟨n / 4, by omega⟩
      rw [hj]
      exact pow_mod_five_three x j
    have hm5 : (x ^ 3 + n) % 5 = 0 ∨ (x ^ 3 + n) % 5 = 1 ∨ (x ^ 3 + n) % 5 = 4 := by
      have e := heq
      generalize x ^ n = A at hx5 e
      generalize x ^ 3 = C at hx5 ⊢
      generalize z ^ 2 = B at hz5 e
      omega
    exact h1 x z n hx hz hn hn2 hxo hx4 hxsq hxm hm3 hm5 heq
  · have hx5 : x ^ n % 5 = x % 5 := by
      obtain ⟨j, hj⟩ : ∃ j, n = 4 * j + 1 := ⟨n / 4, by omega⟩
      rw [hj]
      exact pow_mod_five x j
    have hm5 : (x + n) % 5 = 0 ∨ (x + n) % 5 = 1 ∨ (x + n) % 5 = 4 := by
      have e := heq
      generalize x ^ n = A at hx5 e
      generalize z ^ 2 = B at hz5 e
      omega
    exact h2 x z n hx hz hn hn2 hxo hx4 hxsq hxm hm3 hm5 heq

end OMA.R_OeisA232616_conjecture_3_R1_H1_R2_H2_R1
