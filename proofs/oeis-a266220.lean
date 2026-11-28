import OMAStatements.S_oeis_a266220
import Mathlib

-- Credit: @oh-meh
open OMA.S_oeis_a266220

private theorem first (i : ℤ) : black 1 i = decide (i ≠ 1) := by
  apply Bool.eq_iff_iff.mpr
  simp [black]
  omega

private theorem rows (k : ℕ) :
    (∀ i, black (2*k+2) i = false) ∧ (∀ i, black (2*k+3) i = true) := by
  induction k with
  | zero =>
    have h (i : ℤ) : black 2 i = false := by
      rw [show 2 = 1 + 1 by omega, black]
      simp [first]
      omega
    exact ⟨h, fun i => by rw [show 3 = 2 + 1 by omega, black]; simp [h]⟩
  | succ k ih =>
    have h (i : ℤ) : black (2*(k+1)+2) i = false := by
      rw [show 2*(k+1)+2 = (2*k+3)+1 by omega, black]
      simp [ih.2]
    refine ⟨h, fun i => ?_⟩
    rw [black]
    simp [h]

private theorem counts (k : ℕ) :
    blackCount (2*k+2) = 0 ∧ blackCount (2*k+3) = 2*(2*(k : ℤ)+3)+1 := by
  constructor <;> simp [blackCount, (rows k).1, (rows k).2]

private theorem formula (n : ℕ) (hn : 2 ≤ n) :
    2 * blackCount n = (1-(-1 : ℤ)^n) * (2*(n : ℤ)+1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show 2+m = 2*k+2 by omega, (counts k).1, pow_add, pow_mul]
    norm_num
  · rw [show 2+m = 2*k+3 by omega, (counts k).2, pow_add, pow_mul]
    push_cast
    norm_num

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    blackCount n = 2*blackCount (n-2) - blackCount (n-4) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 6+k-2 = 4+k by omega, show 6+k-4 = 2+k by omega]
  have h₁ := formula (6+k) (by omega)
  have h₂ := formula (4+k) (by omega)
  have h₃ := formula (2+k) (by omega)
  simp only [pow_add, Nat.cast_add, Nat.cast_ofNat] at h₁ h₂ h₃
  norm_num at h₁ h₂ h₃
  linarith

open PowerSeries in
private theorem generating :
    mk blackCount * ((1-X)^2 * (1+X)^2 : ℤ⟦X⟧) =
      1+2*X-2*X^2+3*X^3+X^4-X^5 := by
  let F := mk blackCount
  change F * _ = _
  rw [show F * ((1-X)^2 * (1+X)^2) = F - 2*(F*X^2) + F*X^4 by ring]
  ext n
  simp only [map_add, map_sub, show (3 : ℤ⟦X⟧) = 2+1 by norm_num, add_mul,
    two_mul, one_mul, coeff_mul_X_pow', F, coeff_mk, coeff_one, coeff_X, coeff_X_pow]
  by_cases hn : n < 6
  · interval_cases n <;> decide +kernel
  · have h := recurrence n (by omega)
    simp [show 2 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega]
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a266220.main :=
  ⟨formula, recurrence, generating⟩
