import FormalConjectures.OEIS.«64313»

-- Reduction OeisA64313.conjecture.R1 of Integer part of area of a regular polygon — conjecture
-- Credit: @mbilenko03

/-!
# Area of the regular `n`-gon with unit side: an analytic bound plus a Diophantine bound

Put `B n = n^2 / (4π) - π / 12`. With `x = π / n` the area is `n^2 / (4π) * (x cot x)`, and
`x cot x = 1 - x^2/3 - x^4/45 - 2x^6/945 - …` (all later coefficients negative), so
`area n = B n - π^3 / (180 n^2) - …`. Numerically `(B n - area n) * n^2` decreases from
`0.1790…` at `n = 5` to `π^3/180 = 0.17226…`.

* `H1` (analytic): for `n ≥ 5`, `B n - 181/1000/n^2 < area n < B n`.
* `H2` (open core, Diophantine): for `n ≥ 5`, the fractional part of `B n` is at least
  `181/1000/n^2`. Numerically `fract (B n) * n^2 > 0.183` for every `5 ≤ n ≤ 10^8`.

Together they pin `⌊area n⌋ = ⌊B n⌋`. The cases `n = 3, 4` use the file's values `a 3 = 0`,
`a 4 = 1` and bounds on `π`.
-/

namespace OMA.R_OeisA64313_conjecture_R1

open OeisA64313

/-- Analytic: for `n ≥ 5` the area lies strictly between `B n - 0.181 / n^2` and `B n`. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    (n : ℝ) ^ 2 / (4 * Real.pi) - Real.pi / 12 - 181 / 1000 / (n : ℝ) ^ 2 < area n ∧
      area n < (n : ℝ) ^ 2 / (4 * Real.pi) - Real.pi / 12

/-- Open core: for `n ≥ 5` the fractional part of `n^2 / (4π) - π / 12` is at least
`0.181 / n^2`. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    181 / 1000 / (n : ℝ) ^ 2 ≤ Int.fract ((n : ℝ) ^ 2 / (4 * Real.pi) - Real.pi / 12)

theorem main : H1 → H2 → type_of% @OeisA64313.conjecture := by
  intro h1 h2 n hn
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
  · rw [a_3]
    have hf : Int.floor (((3 : ℕ) : ℝ) ^ 2 / (4 * Real.pi) - Real.pi / 12) = 0 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor
      · rw [sub_nonneg, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
      · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]; nlinarith
    rw [hf]; rfl
  · rw [a_4]
    have hf : Int.floor (((4 : ℕ) : ℝ) ^ 2 / (4 * Real.pi) - Real.pi / 12) = 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]; nlinarith
      · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]; nlinarith
    rw [hf]; rfl
  · obtain ⟨hlo, hhi⟩ := h1 n h5
    have hfr := h2 n h5
    set B : ℝ := (n : ℝ) ^ 2 / (4 * Real.pi) - Real.pi / 12 with hB
    have hfl : Int.floor (area n) = Int.floor B := by
      rw [Int.floor_eq_iff]
      constructor
      · have := Int.self_sub_floor B
        rw [Int.fract] at hfr
        linarith
      · linarith [Int.lt_floor_add_one B]
    rw [a, hfl]

end OMA.R_OeisA64313_conjecture_R1
