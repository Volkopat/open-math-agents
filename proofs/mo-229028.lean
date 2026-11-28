import OMAStatements.S_mo_229028
import Mathlib

/-!
MathOverflow 229028: `p = 1 + x + x^2` has the log-concave coefficient sequence `(1, 1, 1)`, but
`p(0)^(1/2) p(1/5)^(1/2) = sqrt(31/25) > 111/100 = p(1/10)`.
-/

namespace OMA.P229028

open Polynomial

/-- `1 + x + x^2`. -/
noncomputable def p : ℝ[X] := 1 + X + X ^ 2

lemma coeff_p (k : ℕ) : p.coeff k = if k ≤ 2 then 1 else 0 := by
  rcases Nat.lt_or_ge k 3 with h | h
  · interval_cases k <;> simp [p, coeff_one, coeff_X, coeff_X_pow]
  · rw [if_neg (by omega)]
    simp only [p, coeff_add, coeff_one, coeff_X, coeff_X_pow]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

lemma nonneg : ∀ k, 0 ≤ p.coeff k := by
  intro k; rw [coeff_p]; split_ifs <;> norm_num

lemma logconc : ∀ k, 1 ≤ k → p.coeff (k - 1) * p.coeff (k + 1) ≤ p.coeff k ^ 2 := by
  intro k hk
  rw [coeff_p, coeff_p, coeff_p]
  split_ifs <;> first | omega | norm_num

lemma fails : ¬ (p.eval 0 ^ (1 - (1 / 2 : ℝ)) * p.eval (1 / 5) ^ (1 / 2 : ℝ) ≤
    p.eval ((1 - 1 / 2) * 0 + 1 / 2 * (1 / 5))) := by
  have e0 : p.eval 0 = 1 := by simp [p]
  have e1 : p.eval (1 / 5) = 31 / 25 := by simp [p]; norm_num
  have e2 : p.eval ((1 - 1 / 2) * 0 + 1 / 2 * (1 / 5)) = 111 / 100 := by simp [p]; norm_num
  rw [e0, e1, e2, Real.one_rpow, one_mul, ← Real.sqrt_eq_rpow, not_le]
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

theorem disproof_aux :
    ¬ ∀ p : ℝ[X], (∀ k, 0 ≤ p.coeff k) →
      (∀ k, 1 ≤ k → p.coeff (k - 1) * p.coeff (k + 1) ≤ p.coeff k ^ 2) →
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        p.eval x ^ (1 - t) * p.eval y ^ t ≤ p.eval ((1 - t) * x + t * y) := by
  intro h
  exact fails (h p nonneg logconc 0 (1 / 5) le_rfl (by norm_num) (1 / 2) (by norm_num)
    (by norm_num))

end OMA.P229028

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_229028.main) := OMA.P229028.disproof_aux
