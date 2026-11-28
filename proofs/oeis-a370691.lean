import OMAStatements.S_oeis_a370691
import Mathlib

-- Disproof of the A370691 conjecture under both offsets.
-- A128507(n) is the denominator of the rational sum Q n = Sum_{k=0..n} chi(k)/(2k+1)^3, chi = [1, 1, -1, -1]
-- (period 4), because S(2k, √2) = chi(k) (from S(j+4, √2) = -S(j, √2)). Literal offset: T(1, 2) = 1, A128507(1) = 27.
-- Shifted offset at n = 57: 23^3 divides T(58, 2) but not A128507(57) (the unsigned and signed sums of
-- 1/j^3 over j = 1, 3, 5 differ mod 23: 1 + 1/27 + 1/125 = 14, 1 + 1/27 - 1/125 = 0). The two denominators are
-- evaluated by the kernel (decide +kernel, no native code).

namespace OMA.A370691Proof

open OMA.S_oeis_a370691 Polynomial

/-- The sign pattern `[1, 1, -1, -1]` of period 4. -/
def chi (k : ℕ) : ℚ := if k % 4 < 2 then 1 else -1

/-- The rational twin of `r n`. -/
def Q (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), chi k / (2 * (k : ℚ) + 1) ^ 3

theorem chi_add_two (k : ℕ) : chi (k + 2) = - chi k := by
  unfold chi
  by_cases h : k % 4 < 2
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega), neg_neg]

/-- `S(n + 4, √2) = -S(n, √2)`, from the recursion and `√2 ^ 2 = 2`. -/
theorem S_eval_add_four (n : ℤ) :
    (Chebyshev.S ℝ (n + 4)).eval (Real.sqrt 2) = - (Chebyshev.S ℝ n).eval (Real.sqrt 2) := by
  have hx : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e2 := congrArg (eval (Real.sqrt 2)) (Chebyshev.S_add_two ℝ n)
  have e3 := congrArg (eval (Real.sqrt 2)) (Chebyshev.S_add_two ℝ (n + 1))
  have e4 := congrArg (eval (Real.sqrt 2)) (Chebyshev.S_add_two ℝ (n + 2))
  simp only [eval_sub, eval_mul, eval_X] at e2 e3 e4
  rw [show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at e3
  rw [show n + 2 + 2 = n + 4 by ring, show n + 2 + 1 = n + 3 by ring] at e4
  linear_combination e4 + Real.sqrt 2 * e3 + e2 + (Chebyshev.S ℝ (n + 2)).eval (Real.sqrt 2) * hx

/-- `S(2k, √2)` is the period-4 sign `[1, 1, -1, -1]`. -/
theorem S_eval_even : ∀ k : ℕ, (Chebyshev.S ℝ (2 * (k : ℤ))).eval (Real.sqrt 2) = ((chi k : ℚ) : ℝ)
  | 0 => by simp [chi]
  | 1 => by
      have hx : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      rw [show (2 : ℤ) * ((1 : ℕ) : ℤ) = 2 by norm_num, Chebyshev.S_two]
      norm_num [chi, hx]
  | k + 2 => by
      rw [show (2 : ℤ) * ((k + 2 : ℕ) : ℤ) = 2 * (k : ℤ) + 4 by push_cast; ring,
        S_eval_add_four, S_eval_even k, chi_add_two, Rat.cast_neg]

theorem r_eq (n : ℕ) : r n = ((Q n : ℚ) : ℝ) := by
  unfold r Q
  push_cast
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [S_eval_even k]

theorem A128507_eq (n : ℕ) : A128507 n = (Q n).den := by
  have hex : ∃ q : ℚ, (q : ℝ) = r n := ⟨Q n, (r_eq n).symm⟩
  unfold A128507
  rw [dif_pos hex]
  have hq : ((hex.choose : ℚ) : ℝ) = ((Q n : ℚ) : ℝ) := hex.choose_spec.trans (r_eq n)
  rw [Rat.cast_injective hq]

/-- Literal offset: `T(1, 2) = 1` but `A128507(1) = 27`. -/
theorem left_ne : T 1 2 ≠ A128507 1 := by
  rw [A128507_eq]
  decide +kernel

/-- Shifted offset: `23 ^ 3 ∣ T(58, 2)` but `23 ^ 3 ∤ A128507(57)`, so they differ. -/
theorem right_ne : T (57 + 1) 2 ≠ A128507 57 := by
  rw [A128507_eq]
  decide +kernel

end OMA.A370691Proof

/-- The conjecture fails under both offsets: `T(1, 2) = 1 ≠ 27 = A128507(1)`, and `T(58, 2) ≠ A128507(57)`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a370691.main) := by
  rintro (h | h)
  · exact OMA.A370691Proof.left_ne (h 1)
  · exact OMA.A370691Proof.right_ne (h 57)
