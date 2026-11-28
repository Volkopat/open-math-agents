import OMAStatements.S_oeis_a267921

-- Credit: @DavidHallgren
namespace Rule243Proof

open OMA.S_oeis_a267921 PowerSeries

private theorem rule_formula (l c r : Bool) : rule l c r = (l || !c) := by
  cases l <;> cases c <;> cases r <;> decide

/-- At time n+1 the unique off cell is at position n on the full integer line. -/
private theorem row_shape (n : ℕ) (x : ℤ) : state (n+1) x = decide (x ≠ (n : ℤ)) := by
  induction n generalizing x with
  | zero =>
    simp only [state, step, initial, rule_formula, Nat.cast_zero]
    by_cases h : x = 0 <;> simp [h]
  | succ n ih =>
    change rule _ _ _ = _
    rw [rule_formula, ih, ih]
    by_cases h : x - 1 = (n : ℤ)
    · have hs : x = ((n+1 : ℕ) : ℤ) := by omega
      simp [hs]
    · have hs : x ≠ (n : ℤ) + 1 := by omega
      simp [h, hs]

private theorem encode_ones (g : Row) (l : ℤ) (m : ℕ)
    (h : ∀ i : ℕ, i < m → g (l + i) = true) : encode g l m + 1 = 2^m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have prev := ih (fun i hi => h i (by omega))
    simp only [encode, h k (by omega), bit, if_true, pow_succ]
    omega

/-- The cropped binary word consists of 2n+1 ones followed by 01 at time n+1. -/
private theorem value (n : ℕ) : a (n+1) + 3 = 8 * 4^n := by
  let l : ℤ := -((n+1 : ℕ) : ℤ)
  let m := 2*n+1
  have ones := encode_ones (state (n+1)) l m (by
    intro i hi
    rw [row_shape]
    simp only [decide_eq_true_eq]
    dsimp [m] at hi; dsimp [l]; omega)
  have hole : state (n+1) (l + m) = false := by
    rw [row_shape]; simp [l,m]; omega
  have last : state (n+1) (l + ((m+1 : ℕ) : ℤ)) = true := by
    rw [row_shape]; simp [l,m]; omega
  have powm : 2^m = 2*4^n := by
    dsimp [m]; rw [pow_succ, pow_mul]; ring
  change encode (state (n+1)) l (2*(n+1)+1) + 3 = _
  rw [show 2*(n+1)+1 = m+1+1 by dsimp [m]; omega]
  simp only [encode, hole, last, bit, if_true, Bool.false_eq_true, if_false]
  omega

private theorem recurrence (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 5*(a (n-1) : ℤ) - 4*(a (n-2) : ℤ) := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+3 := ⟨n-3,by omega⟩
  have hv (j : ℕ) : (a (j+1) : ℤ) + 3 = 8 * (4 : ℤ)^j := by
    exact_mod_cast value j
  have h0 := hv k
  have h1 : (a (k+2) : ℤ) + 3 = 8 * (4 : ℤ)^(k+1) := hv (k+1)
  have h2 : (a (k+3) : ℤ) + 3 = 8 * (4 : ℤ)^(k+2) := hv (k+2)
  rw [pow_succ] at h1
  rw [pow_succ, pow_succ] at h2
  change (a (k+3) : ℤ) = 5*(a (k+2) : ℤ) - 4*(a (k+1) : ℤ)
  linarith only [h0, h1, h2]

private theorem generating_function :
    series * ((1-X)*(1-4*X)) = 1 + 8*X^2 := by
  have h : series * ((1-X)*(1-4*X)) =
      series - C (5 : ℤ) * (series * X) + C (4 : ℤ) * (series * X^2) := by
    rw [map_ofNat C 5, map_ofNat C 4]
    ring
  have h8 : C (8 : ℤ) = (8 : PowerSeries ℤ) := map_ofNat C 8
  rw [h, ← h8]
  ext n
  simp only [map_add, map_sub]
  rw [coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_one]
  have a0 : a 0 = 1 := by decide
  have a1 : a 1 = 5 := by decide
  have a2 : a 2 = 29 := by decide
  rcases n with _ | _ | _ | k
  · norm_num [coeff_zero_mul_X, series, coeff_mk, a0]
  · norm_num [coeff_succ_mul_X, series, coeff_mk, a0, a1]
  · norm_num [coeff_succ_mul_X, series, coeff_mk, a0, a1, a2]
  · have hr := recurrence (k+3) (by omega)
    change (a (k+3) : ℤ) = 5*(a (k+2) : ℤ) - 4*(a (k+1) : ℤ) at hr
    simp [coeff_succ_mul_X, series, show 2 ≤ k+1+1+1 by omega, show k+1+1+1 ≠ 2 by omega]
    linarith only [hr]

end Rule243Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267921.main :=
  ⟨Rule243Proof.recurrence, Rule243Proof.generating_function⟩
