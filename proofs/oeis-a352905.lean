import OMAStatements.S_oeis_a352905
import Mathlib

-- Problem: A352905: Expansion of e.g.f. sin(x) * exp(exp(x) - 1).
-- Upstream: formal-conjectures statements/oeis-a352905.lean:0 (declaration OMA.S_oeis_a352905.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Dobinski's formula sum_k k^m / k! = e Bell(m) is proved first (through the expansion of k^m in
falling factorials). Expanding (k - i)^n - (k + i)^n by the binomial theorem gives the sum over m
of ((-i)^m - i^m) binomial(n,m) k^(n-m), so the right side of the conjecture is the sum over m of
w(m) binomial(n,m) Bell(n-m) with w(m) = i ((-i)^m - i^m) / 2. Finally w(2t) = 0 and
w(2t+1) = (-1)^t, which is the formula defining a(n). -/

namespace A352905Aux

open OMA.S_oeis_a352905

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


theorem hasSum_bell (m : ℕ) :
    HasSum (fun k : ℕ => ((k : ℂ)) ^ m / (k.factorial : ℂ)) ((bell m : ℂ) * (Real.exp 1 : ℂ)) := by
  have h := dobinski 1 m
  have h' : HasSum (fun k : ℕ => (k : ℝ) ^ m / (k.factorial : ℝ)) ((bell m : ℝ) * Real.exp 1) := by
    have e : (∑ j ∈ Finset.range (m + 1), (Nat.stirlingSecond m j : ℝ) * ((1 : ℝ) ^ j * Real.exp 1)) =
        (bell m : ℝ) * Real.exp 1 := by
      unfold bell
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e] at h
    simpa using h
  have h2 := Complex.hasSum_ofReal.mpr h'
  simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.ofReal_mul] using h2

/-- The weight w(m) = i ((-i)^m - i^m) / 2. -/
noncomputable def w (m : ℕ) : ℂ := Complex.I * ((-Complex.I) ^ m - Complex.I ^ m) / 2

theorem w_even (t : ℕ) : w (2 * t) = 0 := by
  unfold w
  rw [pow_mul, pow_mul, neg_sq]
  ring

theorem w_odd (t : ℕ) : w (2 * t + 1) = (-1) ^ t := by
  unfold w
  rw [pow_succ, pow_succ, pow_mul, pow_mul, neg_sq, Complex.I_sq]
  have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(-1 : ℂ) ^ t) * h

theorem odd_sum (F : ℕ → ℂ) (hF : ∀ t, F (2 * t) = 0) (N : ℕ) :
    ∑ r ∈ Finset.range (2 * N), F r = ∑ t ∈ Finset.range N, F (2 * t + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : 2 * (N + 1) = 2 * N + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, hF N, add_zero,
      Finset.sum_range_succ]

theorem expand (n k : ℕ) :
    ((k : ℂ) - Complex.I) ^ n - ((k : ℂ) + Complex.I) ^ n =
      ∑ m ∈ Finset.range (n + 1),
        ((-Complex.I) ^ m - Complex.I ^ m) * (n.choose m : ℂ) * (k : ℂ) ^ (n - m) := by
  have h1 : ((k : ℂ) - Complex.I) = -Complex.I + (k : ℂ) := by ring
  have h2 : ((k : ℂ) + Complex.I) = Complex.I + (k : ℂ) := by ring
  rw [h1, h2, add_pow, add_pow, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem hasSum_main (n : ℕ) :
    HasSum (fun k : ℕ => (((k : ℂ) - Complex.I) ^ n - ((k : ℂ) + Complex.I) ^ n) /
        (k.factorial : ℂ))
      (∑ m ∈ Finset.range (n + 1), ((-Complex.I) ^ m - Complex.I ^ m) * (n.choose m : ℂ) *
        ((bell (n - m) : ℂ) * (Real.exp 1 : ℂ))) := by
  have hj : ∀ m ∈ Finset.range (n + 1),
      HasSum (fun k : ℕ => ((-Complex.I) ^ m - Complex.I ^ m) * (n.choose m : ℂ) *
        ((k : ℂ) ^ (n - m) / (k.factorial : ℂ)))
        (((-Complex.I) ^ m - Complex.I ^ m) * (n.choose m : ℂ) *
          ((bell (n - m) : ℂ) * (Real.exp 1 : ℂ))) := by
    intro m _
    exact (hasSum_bell (n - m)).mul_left _
  have h := hasSum_sum hj
  convert h using 1
  ext k
  rw [expand, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem weighted (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), w m * (n.choose m : ℂ) * (bell (n - m) : ℂ) = ((a n : ℤ) : ℂ) := by
  set N := (n - 1) / 2 + 1 with hN
  have hsub : Finset.range (n + 1) ⊆ Finset.range (2 * (N + 1)) := by
    intro r hr
    simp only [Finset.mem_range] at hr ⊢
    omega
  have hzero : ∀ r ∈ Finset.range (2 * (N + 1)), r ∉ Finset.range (n + 1) →
      w r * (n.choose r : ℂ) * (bell (n - r) : ℂ) = 0 := by
    intro r _ hr
    simp only [Finset.mem_range, not_lt] at hr
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hlast : w (2 * N + 1) * (n.choose (2 * N + 1) : ℂ) * (bell (n - (2 * N + 1)) : ℂ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [Finset.sum_subset hsub hzero,
    odd_sum (fun r => w r * (n.choose r : ℂ) * (bell (n - r) : ℂ)) (fun t => by
      simp only [w_even, zero_mul]) (N + 1), Finset.sum_range_succ, hlast, add_zero]
  unfold a
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  rw [w_odd]
  have e : n - (2 * t + 1) = n - 2 * t - 1 := by omega
  rw [e]

end A352905Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a352905.main := by
  intro n
  rw [(A352905Aux.hasSum_main n).tsum_eq, ← A352905Aux.weighted n, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hE : (Real.exp 1 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos 1).ne'
  unfold A352905Aux.w
  field_simp
