import OMAStatements.S_oeis_a242817
import Mathlib

-- Problem: A242817: a(n) = B(n,n), where B(n,x) = Sum_{k=0..n} Stirling2(n,k)*x^k are the Bell polynomials (also known as exponential polynomials or Touchard polynomials).
-- Upstream: formal-conjectures statements/oeis-a242817.lean:0 (declaration OMA.S_oeis_a242817.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Dobinski's formula for every real x. First, k^m is the sum over j of Stirling2(m,j) times the
falling factorial k (k-1) ... (k-j+1), by induction on m. Second, the series of
(falling factorial of k of length j) x^k / k! has sum x^j e^x, by shifting the index by j.
Summing the second fact against the first gives
sum_k k^m x^k / k! = e^x sum_j Stirling2(m,j) x^j, and x = m = n is the statement. -/

namespace A242817Aux

open OMA.S_oeis_a242817

theorem mul_desc (k j : ℕ) :
    k * k.descFactorial j = k.descFactorial (j + 1) + j * k.descFactorial j := by
  rw [Nat.descFactorial_succ]
  rcases Nat.lt_or_ge k j with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
    simp
  · have : k = (k - j) + j := by omega
    nth_rw 1 [this]
    ring

theorem pow_expand (m k : ℕ) :
    k ^ m = ∑ j ∈ Finset.range (m + 1), Nat.stirlingSecond m j * k.descFactorial j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : k ^ (m + 1) = ∑ j ∈ Finset.range (m + 1),
        Nat.stirlingSecond m j * (k.descFactorial (j + 1) + j * k.descFactorial j) := by
      rw [pow_succ, ih, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_desc]
      ring
    have h2 : ∑ j ∈ Finset.range (m + 1), Nat.stirlingSecond m j * (j * k.descFactorial j) =
        ∑ i ∈ Finset.range (m + 1),
          (i + 1) * Nat.stirlingSecond m (i + 1) * k.descFactorial (i + 1) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ (fun i =>
        (i + 1) * Nat.stirlingSecond m (i + 1) * k.descFactorial (i + 1)),
        Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_add_one m)]
      simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h3 : ∑ j ∈ Finset.range (m + 1),
        Nat.stirlingSecond m j * (k.descFactorial (j + 1) + j * k.descFactorial j) =
        ∑ j ∈ Finset.range (m + 1), Nat.stirlingSecond m j * k.descFactorial (j + 1) +
          ∑ j ∈ Finset.range (m + 1), Nat.stirlingSecond m j * (j * k.descFactorial j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hz : Nat.stirlingSecond (m + 1) 0 = 0 := Nat.stirlingSecond_succ_zero m
    rw [Finset.sum_range_succ' (fun j => Nat.stirlingSecond (m + 1) j * k.descFactorial j), hz,
      Nat.zero_mul, Nat.add_zero, h1, h3, h2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.stirlingSecond_succ_succ]
    ring

theorem hasSum_desc (x : ℝ) (j : ℕ) :
    HasSum (fun k : ℕ => (k.descFactorial j : ℝ) * x ^ k / (k.factorial : ℝ))
      (x ^ j * Real.exp x) := by
  have hexp : HasSum (fun i : ℕ => x ^ i / (i.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hterm : ∀ i : ℕ, ((i + j).descFactorial j : ℝ) * x ^ (i + j) / ((i + j).factorial : ℝ) =
      x ^ j * (x ^ i / (i.factorial : ℝ)) := by
    intro i
    have hf : (i.factorial : ℝ) * ((i + j).descFactorial j : ℝ) = ((i + j).factorial : ℝ) := by
      have := Nat.factorial_mul_descFactorial (Nat.le_add_left j i)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hi : (i.factorial : ℝ) ≠ 0 := by positivity
    have hd : ((i + j).descFactorial j : ℝ) ≠ 0 := by
      have : (i + j).descFactorial j ≠ 0 := by
        rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
        omega
      exact_mod_cast this
    rw [← hf, pow_add]
    field_simp
  have hshift : HasSum (fun i : ℕ => ((i + j).descFactorial j : ℝ) * x ^ (i + j) /
      ((i + j).factorial : ℝ)) (x ^ j * Real.exp x) := by
    have h := hexp.mul_left (x ^ j)
    simpa only [hterm] using h
  have hzero : ∑ i ∈ Finset.range j,
      ((i.descFactorial j : ℝ) * x ^ i / (i.factorial : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hi)]
    simp
  have h := (hasSum_nat_add_iff
    (f := fun k : ℕ => (k.descFactorial j : ℝ) * x ^ k / (k.factorial : ℝ)) j).mp hshift
  rw [hzero, add_zero] at h
  exact h

theorem dobinski (x : ℝ) (m : ℕ) :
    HasSum (fun k : ℕ => (k : ℝ) ^ m * x ^ k / (k.factorial : ℝ))
      (∑ j ∈ Finset.range (m + 1), (Nat.stirlingSecond m j : ℝ) * (x ^ j * Real.exp x)) := by
  have hj : ∀ j ∈ Finset.range (m + 1),
      HasSum (fun k : ℕ => (Nat.stirlingSecond m j : ℝ) *
        ((k.descFactorial j : ℝ) * x ^ k / (k.factorial : ℝ)))
        ((Nat.stirlingSecond m j : ℝ) * (x ^ j * Real.exp x)) := by
    intro j _
    exact (hasSum_desc x j).mul_left (Nat.stirlingSecond m j : ℝ)
  have h := hasSum_sum hj
  convert h using 1
  ext k
  have hp : (k : ℝ) ^ m = ∑ j ∈ Finset.range (m + 1),
      (Nat.stirlingSecond m j : ℝ) * (k.descFactorial j : ℝ) := by
    exact_mod_cast pow_expand m k
  rw [hp, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end A242817Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a242817.main := by
  intro n _
  have h := (A242817Aux.dobinski (n : ℝ) n).tsum_eq
  rw [h]
  unfold OMA.S_oeis_a242817.a
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring
