import OMAStatements.S_mse_3767162
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mse_3767162.main := by
  rintro n ⟨a, b, h⟩
  obtain rfl | hn := n.eq_zero_or_pos
  · exact ⟨0, 0, rfl⟩
  have : (n : ℚ) * (a.den * b.den) ^ 2 = (a.num * b.den) ^ 2 + (b.num * a.den) ^ 2 := by
    rw [h, ← a.mul_den_eq_num, ← b.mul_den_eq_num]; ring
  have hN := Nat.eq_sq_add_sq_iff.1 ⟨(a.num * b.den).natAbs, (b.num * a.den).natAbs, by zify; simp only [sq_abs]; exact_mod_cast this⟩
  obtain ⟨x, y, h⟩ := Nat.eq_sq_add_sq_iff.2 fun q hq h3 => by
    have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    have := hN q (by rw [Nat.primeFactors_mul hn.ne' (by positivity)]; exact Finset.mem_union_left _ hq) h3
    rw [padicValNat.mul hn.ne' (by positivity), padicValNat.pow] at this
    simpa [parity_simps] using this
  exact ⟨x, y, by exact_mod_cast h⟩
