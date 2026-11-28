import OMAStatements.S_mse_3358067

-- Reduction mse-3358067.R1 of: there is no n ≠ 3 with arctan 1 + ⋯ + arctan n = kπ/2.
-- Credit: @futurum-dev

/-!
# From a sum of arctangents to a square product

Write `θₙ = arctan 1 + ⋯ + arctan n` and `Qₙ = (1² + 1)(2² + 1)⋯(n² + 1)`. Since
`cos (arctan m) = 1 / √(1 + m²)` and `sin (arctan m) = m / √(1 + m²)`, the angle addition formulas
give, by induction, integers `A, B` with `√Qₙ cos θₙ = A`, `√Qₙ sin θₙ = B` and `Qₙ = A² + B²`
(`A + Bi = (1 + i)(1 + 2i)⋯(1 + ni)`). If `θₙ = kπ/2` then `2AB = Qₙ sin (kπ) = 0`, so `Qₙ` is the
square of an integer. Hence the problem follows from: `Qₙ` is a square only for `n = 3`
(for `n = 1, 2` the products `2` and `10` are checked directly).

* `H1`: `Qₙ` is not a square for `4 ≤ n ≤ 200` (a finite check: some `j ≤ n` has a prime
  factor `p > 2n` of `j² + 1`, which then divides `Qₙ` exactly once).
* `H2`: `Qₙ` is not a square for `n > 200`. This is the tail of Cilleruelo's theorem
  (J. Cilleruelo, *Squares in (1² + 1)⋯(n² + 1)*, J. Number Theory 128 (2008) 2488–2491).
-/

namespace OMA.R_mse_3358067_R1

open Real Finset

/-- The product `(1² + 1)(2² + 1)⋯(n² + 1)` is not a square for `4 ≤ n ≤ 200`. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ 200 → ¬ IsSquare (∏ j ∈ Finset.Icc 1 n, (j ^ 2 + 1))

/-- The product `(1² + 1)(2² + 1)⋯(n² + 1)` is not a square for `n > 200` (Cilleruelo). -/
def H2 : Prop :=
  ∀ n : ℕ, 200 < n → ¬ IsSquare (∏ j ∈ Finset.Icc 1 n, (j ^ 2 + 1))

lemma key (n : ℕ) : ∃ A B : ℤ,
    √((∏ j ∈ Finset.Icc 1 n, (j ^ 2 + 1) : ℕ) : ℝ) *
        cos (∑ j ∈ Finset.Icc 1 n, arctan (j : ℝ)) = A ∧
    √((∏ j ∈ Finset.Icc 1 n, (j ^ 2 + 1) : ℕ) : ℝ) *
        sin (∑ j ∈ Finset.Icc 1 n, arctan (j : ℝ)) = B ∧
    ((∏ j ∈ Finset.Icc 1 n, (j ^ 2 + 1) : ℕ) : ℤ) = A ^ 2 + B ^ 2 := by
  induction n with
  | zero => exact ⟨1, 0, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨A, B, hA, hB, hQ⟩ := ih
    refine ⟨A - (n + 1) * B, B + (n + 1) * A, ?_, ?_, ?_⟩
    · rw [Finset.prod_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      push_cast at hA hB ⊢
      have hm : (0 : ℝ) < 1 + ((n : ℝ) + 1) ^ 2 := by positivity
      have hs : √(1 + ((n : ℝ) + 1) ^ 2) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
      rw [Real.sqrt_mul (by positivity), cos_add, cos_arctan, sin_arctan, add_comm (((n:ℝ)+1)^2) 1]
      field_simp
      linear_combination hA - ((n:ℝ) + 1) * hB
    · rw [Finset.prod_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      push_cast at hA hB ⊢
      have hm : (0 : ℝ) < 1 + ((n : ℝ) + 1) ^ 2 := by positivity
      have hs : √(1 + ((n : ℝ) + 1) ^ 2) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
      rw [Real.sqrt_mul (by positivity), sin_add, cos_arctan, sin_arctan, add_comm (((n:ℝ)+1)^2) 1]
      field_simp
      linear_combination hB + ((n:ℝ) + 1) * hA
    · rw [Finset.prod_Icc_succ_top (by omega)]
      push_cast at hQ ⊢
      rw [hQ]
      ring

lemma square_of_eq (n : ℕ) (k : ℤ) (hk : ∑ j ∈ Finset.Icc 1 n, arctan (j : ℝ) = k * π / 2) :
    IsSquare (∏ j ∈ Finset.Icc 1 n, (j ^ 2 + 1)) := by
  obtain ⟨A, B, hA, hB, hQ⟩ := key n
  set Q : ℕ := ∏ j ∈ Finset.Icc 1 n, (j ^ 2 + 1) with hQdef
  set θ := ∑ j ∈ Finset.Icc 1 n, arctan (j : ℝ)
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg _
  have hAB : ((A * B : ℤ) : ℝ) = 0 := by
    have h2 : sin (2 * θ) = 0 := by
      rw [hk, show 2 * ((k : ℝ) * π / 2) = (k : ℝ) * π by ring]
      exact Real.sin_int_mul_pi k
    rw [Real.sin_two_mul] at h2
    have hsq : √(Q : ℝ) * √(Q : ℝ) = Q := Real.mul_self_sqrt hQ0
    push_cast
    rw [← hA, ← hB]
    calc √(Q : ℝ) * cos θ * (√(Q : ℝ) * sin θ) = (√(Q : ℝ) * √(Q : ℝ)) * (sin θ * cos θ) := by
          ring
      _ = 0 := by
          have : sin θ * cos θ = 0 := by linarith [h2]
          rw [this, mul_zero]
  have hAB' : A * B = 0 := by exact_mod_cast hAB
  rcases mul_eq_zero.1 hAB' with h | h
  · refine ⟨B.natAbs, ?_⟩
    have : (Q : ℤ) = ((B.natAbs * B.natAbs : ℕ) : ℤ) := by
      rw [hQ, h, Int.natAbs_mul_self]
      ring
    exact_mod_cast this
  · refine ⟨A.natAbs, ?_⟩
    have : (Q : ℤ) = ((A.natAbs * A.natAbs : ℕ) : ℤ) := by
      rw [hQ, h, Int.natAbs_mul_self]
      ring
    exact_mod_cast this

lemma not_square_small (r : ℕ) (hr : r = 2 ∨ r = 10) : ¬ IsSquare r := by
  rintro ⟨m, hm⟩
  have : m ≤ 4 := by rcases hr with rfl | rfl <;> nlinarith
  interval_cases m <;> omega

theorem main : H1 → H2 → type_of% @OMA.S_mse_3358067.main := by
  intro h1 h2 n hn h3 ⟨k, hk⟩
  have hsq := square_of_eq n k hk
  by_cases hsmall : n ≤ 2
  · have hr : (∏ j ∈ Finset.Icc 1 n, (j ^ 2 + 1)) = 2 ∨
        (∏ j ∈ Finset.Icc 1 n, (j ^ 2 + 1)) = 10 := by
      interval_cases n <;> decide
    exact not_square_small _ hr hsq
  · by_cases hmid : n ≤ 200
    · exact h1 n (by omega) hmid hsq
    · exact h2 n (by omega) hsq

end OMA.R_mse_3358067_R1
