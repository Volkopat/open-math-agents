import OMAStatements.S_oeis_a273798
import Mathlib

open OMA.S_oeis_a273798 in
theorem OMA.solution : type_of% @OMA.S_oeis_a273798.main := by
  rintro x ⟨m, p, hp, hpm, rfl⟩
  have hx : 0 < 2 ^ m * p := Nat.mul_pos (by positivity) hp.pos
  refine ⟨hx, ?_⟩
  have hv : m ≤ (2 ^ m * p).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hx.ne').1 (dvd_mul_right _ _)
  have h1 : oddPart (2 ^ m * p) ≤ p := by
    unfold oddPart
    calc 2 ^ m * p / 2 ^ (2 ^ m * p).factorization 2 ≤ 2 ^ m * p / 2 ^ m :=
          Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hv) (by positivity)
      _ = p := by rw [Nat.mul_div_cancel_left p (by positivity)]
  calc oddPart (2 ^ m * p) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h1 2
    _ = p * p := sq p
    _ ≤ 2 ^ m * p := Nat.mul_le_mul_right p hpm.le
