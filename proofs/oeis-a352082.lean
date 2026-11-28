import OMAStatements.S_oeis_a352082
import Mathlib

/-! Proof of the A352082 zeta identity. For even n = 2m the Riemann zeta term vanishes and the
classical Hurwitz zeta at m + 1 is zeta(-n) minus the powers 1..m. For odd n = 2m + 1 the point
m + 3/2 is 1/2 on the circle, and B(n+1, 1/2) = (2^(-n) - 1) B(n+1) cancels the zeta term. -/

namespace OMA.Helpers

open OMA.S_oeis_a352082 Finset

/-- An integer point of the line is zero on the unit circle. -/
theorem a352082_circle_int (m : ℕ) : ((((m : ℝ) + 1 : ℝ)) : UnitAddCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m + 1, by simp⟩

/-- The point `m + 3/2` is the point `1/2` of the unit circle. -/
theorem a352082_circle_half (m : ℕ) :
    ((((m : ℝ) + 3 / 2 : ℝ)) : UnitAddCircle) = ((2⁻¹ : ℝ) : UnitAddCircle) := by
  have h : ((m : ℝ) + 3 / 2) = 2⁻¹ + ((m : ℝ) + 1) := by ring
  rw [h, AddCircle.coe_add, a352082_circle_int, add_zero]

/-- Evaluating a Bernoulli polynomial at a real point, in `ℂ`. -/
theorem a352082_bern_eval (k : ℕ) (x : ℝ) :
    ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((x : ℝ) : ℂ) =
      ((bernoulliFun k x : ℝ) : ℂ) := by
  simp only [bernoulliFun, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  push_cast
  rfl

theorem a352082_cpow (x : ℝ) (n : ℕ) : ((x : ℝ) : ℂ) ^ (-(-(n : ℂ))) = ((x : ℝ) : ℂ) ^ n := by
  rw [neg_neg, Complex.cpow_natCast]

/-- The even case `n = 2 m`, `m ≥ 1`. -/
theorem a352082_even (m : ℕ) (hm : 1 ≤ m) :
    (a (2 * m) : ℂ) = (1 - 2 ^ (2 * m)) * riemannZeta (-((2 * m : ℕ) : ℂ))
      - 2 ^ (2 * m) * hurwitzZetaClassical (-((2 * m : ℕ) : ℂ)) (((2 * m : ℕ) : ℝ) / 2 + 1) := by
  have hq : ((2 * m : ℕ) : ℝ) / 2 + 1 = (m : ℝ) + 1 := by push_cast; ring
  have hz : riemannZeta (-((2 * m : ℕ) : ℂ)) = 0 := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h2 : -(((2 * (m' + 1)) : ℕ) : ℂ) = -2 * ((m' : ℂ) + 1) := by push_cast; ring
    rw [h2]
    exact riemannZeta_neg_two_mul_nat_add_one m'
  have hc : ⌈(m : ℝ) + 1⌉₊ = m + 1 := by
    have h1 : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h1, Nat.ceil_natCast]
  unfold hurwitzZetaClassical
  rw [hq, a352082_circle_int, HurwitzZeta.hurwitzZeta_zero, hz, hc, Nat.add_sub_cancel]
  have hS : ∑ k ∈ Icc 1 m, (((m : ℝ) + 1 - (k : ℝ) : ℝ) : ℂ) ^ (-(-((2 * m : ℕ) : ℂ))) =
      ∑ k ∈ range m, (((m : ℝ) + 1 - ((1 + k : ℕ) : ℝ) : ℝ) : ℂ) ^ (2 * m) := by
    have hI : Icc 1 m = Ico 1 (m + 1) := by
      ext x
      simp only [mem_Icc, mem_Ico]
      omega
    rw [hI, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine sum_congr rfl fun k _ => ?_
    rw [a352082_cpow]
  have hA : (a (2 * m) : ℂ) =
      ∑ k ∈ range m, (2 : ℂ) ^ (2 * m) *
        (((m : ℝ) + 1 - ((1 + k : ℕ) : ℝ) : ℝ) : ℂ) ^ (2 * m) := by
    unfold a
    rw [show 2 * m / 2 = m by omega, sum_range_succ, Nat.cast_add, Nat.cast_sum]
    have h0 : (((2 * m - 2 * m) ^ (2 * m) : ℕ) : ℂ) = 0 := by
      rw [Nat.sub_self, zero_pow (by omega), Nat.cast_zero]
    rw [h0, add_zero]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [← mul_pow, Nat.cast_pow]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hS, hA, ← mul_sum]
  ring

/-- The odd case `n = 2 m + 1`. -/
theorem a352082_odd (m : ℕ) :
    (a (2 * m + 1) : ℂ) = (1 - 2 ^ (2 * m + 1)) * riemannZeta (-((2 * m + 1 : ℕ) : ℂ))
      - 2 ^ (2 * m + 1) *
        hurwitzZetaClassical (-((2 * m + 1 : ℕ) : ℂ)) (((2 * m + 1 : ℕ) : ℝ) / 2 + 1) := by
  have hq : ((2 * m + 1 : ℕ) : ℝ) / 2 + 1 = (m : ℝ) + 3 / 2 := by push_cast; ring
  have hc : ⌈(m : ℝ) + 3 / 2⌉₊ = m + 2 := by
    rw [Nat.ceil_eq_iff (by omega)]
    constructor <;> push_cast <;> linarith
  have hhalf : (2⁻¹ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hH := HurwitzZeta.hurwitzZeta_neg_nat (k := 2 * m + 1) (by omega) hhalf
  rw [a352082_bern_eval, bernoulliFun_eval_half] at hH
  have hZ := riemannZeta_neg_nat_eq_bernoulli (2 * m + 1)
  unfold hurwitzZetaClassical
  rw [hq, a352082_circle_half, hH, hZ, hc, show m + 2 - 1 = m + 1 by omega]
  have hS : ∑ k ∈ Icc 1 (m + 1),
      (((m : ℝ) + 3 / 2 - (k : ℝ) : ℝ) : ℂ) ^ (-(-((2 * m + 1 : ℕ) : ℂ))) =
      ∑ k ∈ range (m + 1), (((m : ℝ) + 3 / 2 - ((1 + k : ℕ) : ℝ) : ℝ) : ℂ) ^ (2 * m + 1) := by
    have hI : Icc 1 (m + 1) = Ico 1 (m + 2) := by
      ext x
      simp only [mem_Icc, mem_Ico]
      omega
    rw [hI, sum_Ico_eq_sum_range, show m + 2 - 1 = m + 1 by omega]
    refine sum_congr rfl fun k _ => ?_
    rw [a352082_cpow]
  have hA : (a (2 * m + 1) : ℂ) =
      ∑ k ∈ range (m + 1), (2 : ℂ) ^ (2 * m + 1) *
        (((m : ℝ) + 3 / 2 - ((1 + k : ℕ) : ℝ) : ℝ) : ℂ) ^ (2 * m + 1) := by
    unfold a
    rw [show (2 * m + 1) / 2 = m by omega, Nat.cast_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [← mul_pow, Nat.cast_pow]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hS, ← mul_sum] at *
  rw [hA]
  have hpow : ((-1 : ℂ)) ^ (2 * m + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hpow]
  have hn : ((2 * m + 1 : ℕ) : ℂ) + 1 ≠ 0 := by
    have : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  push_cast
  field_simp
  ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a352082.main := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · exact OMA.Helpers.a352082_even m (by omega)
  · exact OMA.Helpers.a352082_odd m
