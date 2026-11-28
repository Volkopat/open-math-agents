import OMAStatements.S_mo_389561
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_389561.main := fun n F _ _ _ hc => by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, hc, pow_succ, pow_mul]; norm_num [Nat.mul_mod, Nat.pow_mod]
  have K (a b : F) (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
    by_contra hab
    have : b ≠ 0 := fun hb => hab ⟨by simpa [hb] using h, hb⟩
    exact hns ⟨a / b, by field_simp; linear_combination -h⟩
  refine ⟨fun x y => ⟨fun h => ?_, fun ⟨hx, hy⟩ => ?_⟩, fun x y z hne => ⟨fun h => ?_, fun ⟨hx, hy, _⟩ => ?_⟩⟩
  · have := K x (y - 1) (by linear_combination h - y * h3); exact ⟨this.1, sub_eq_zero.1 this.2⟩
  · subst hx hy; linear_combination h3
  · obtain ⟨hx, e⟩ := K x (y - z) (by linear_combination h - y * z * h3)
    obtain rfl := sub_eq_zero.1 e
    exact ⟨hx, rfl, fun hz => by simp_all⟩
  · subst hx hy; linear_combination y ^ 2 * h3
