import OMAStatements.S_oeis_a375948

namespace OMA.S_oeis_a375948

open PowerSeries

lemma coeff_egf_mul (f g : ℕ → ℚ) (n : ℕ) :
    coeff n ((PowerSeries.mk fun k => f k / (k.factorial : ℚ)) *
      (PowerSeries.mk fun k => g k / (k.factorial : ℚ))) =
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * f k * g (n - k)) / (n.factorial : ℚ) := by
  rw [coeff_mul]
  simp only [coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (f i / (i.factorial : ℚ)) * (g j / (j.factorial : ℚ))), Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h := Nat.choose_mul_factorial_mul_factorial hk'
  have h' : ((n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ)) = (n.factorial : ℚ) := by
    exact_mod_cast h
  rw [← h']
  have : (k.factorial : ℚ) ≠ 0 := by positivity
  have : ((n - k).factorial : ℚ) ≠ 0 := by positivity
  have : (n.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
  field_simp

lemma h3 : (3 : ℚ⟦X⟧) = PowerSeries.C 3 := (map_ofNat PowerSeries.C 3).symm
lemma h2 : (2 : ℚ⟦X⟧) = PowerSeries.C 2 := (map_ofNat PowerSeries.C 2).symm

lemma D_egf : (3 - 2 * PowerSeries.exp ℚ : ℚ⟦X⟧) =
    PowerSeries.mk fun k => ((if k = 0 then (3 : ℚ) else 0) - 2) / (k.factorial : ℚ) := by
  ext n
  rw [h3, h2, map_sub, coeff_C_mul, coeff_C, coeff_exp, coeff_mk]
  by_cases hn : n = 0 <;> simp [hn, div_eq_mul_inv]

lemma three_egf : (3 * PowerSeries.exp ℚ : ℚ⟦X⟧) =
    PowerSeries.mk fun k => (3 : ℚ) / (k.factorial : ℚ) := by
  ext n
  rw [h3, coeff_C_mul, coeff_exp, coeff_mk]
  simp [div_eq_mul_inv]

def T (a : ℕ → ℚ) (n : ℕ) : ℚ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℚ) * a j
def U (a : ℕ → ℚ) (n : ℕ) : ℚ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℚ) * a (j + 1)

lemma T_succ (a : ℕ → ℚ) (m : ℕ) : T a (m + 1) = T a m + U a m := by
  unfold T U
  rw [Finset.sum_range_succ' _ (m + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have h2 : ∑ j ∈ Finset.range (m + 1), (m.choose (j + 1) : ℚ) * a (j + 1) + a 0 =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℚ) * a j := by
    rw [Finset.sum_range_succ' (fun j => (m.choose j : ℚ) * a j) m,
      Finset.sum_range_succ (fun j => (m.choose (j + 1) : ℚ) * a (j + 1)) m]
    simp
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  rw [← h2]; ring

lemma ode (a : ℕ → ℚ) (ha : IsA375948 a) (n : ℕ) :
    3 * a (n + 1) = 2 * U a n + 3 * T a n := by
  obtain ⟨h0, hG⟩ := ha
  set G : ℚ⟦X⟧ := PowerSeries.mk fun n => a n / (n.factorial : ℚ) with hGdef
  set D : ℚ⟦X⟧ := 3 - 2 * PowerSeries.exp ℚ with hD
  have hG0 : G ≠ 0 := by
    intro h; rw [h] at hG; simp at hG
  have hD0 : D ≠ 0 := by
    intro h; rw [h] at hG; simp at hG
  have hG3 : G * G * (D * D * D) = 1 := by rw [← hG]; ring
  have hd := congrArg (d⁄dX ℚ) hG3
  have hD' : d⁄dX ℚ D = - 2 * PowerSeries.exp ℚ := by
    rw [hD, h3, h2, map_sub, Derivation.leibniz]
    simp [derivative_exp, derivative_C]
  simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, hD'] at hd
  have key : d⁄dX ℚ G * D = G * (3 * PowerSeries.exp ℚ) := by
    have h1 : (G * D ^ 2) * (2 * (d⁄dX ℚ G * D) - 6 * PowerSeries.exp ℚ * G) = 0 := by
      linear_combination hd
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (mul_ne_zero hG0 (pow_ne_zero 2 hD0))
    · have h4 : 2 * (d⁄dX ℚ G * D - G * (3 * PowerSeries.exp ℚ)) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 (by rw [h2]; intro h6; have := congrArg (PowerSeries.coeff 0) h6; simp at this)
      · linear_combination h5
  have hc := congrArg (coeff n) key
  have hG' : d⁄dX ℚ G = PowerSeries.mk fun k => a (k + 1) / (k.factorial : ℚ) := by
    ext k
    rw [coeff_derivative]
    simp only [hGdef, coeff_mk]
    rw [Nat.factorial_succ]
    push_cast
    have : (k.factorial : ℚ) ≠ 0 := by positivity
    have : ((k : ℚ) + 1) ≠ 0 := by positivity
    field_simp
  have e1 := coeff_egf_mul (fun k => a (k + 1)) (fun k => (if k = 0 then (3 : ℚ) else 0) - 2) n
  have e2 := coeff_egf_mul a (fun _ => (3 : ℚ)) n
  rw [hG', hD, D_egf, three_egf, hGdef] at hc
  rw [e1, e2] at hc
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [div_left_inj' hn] at hc
  have s1 : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a (k + 1) *
      ((if n - k = 0 then (3 : ℚ) else 0) - 2) = 3 * a (n + 1) - 2 * U a n := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    unfold U
    rw [Finset.mul_sum]
    have : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a (k + 1) * (if n - k = 0 then (3 : ℚ) else 0)
        = 3 * a (n + 1) := by
      rw [Finset.sum_eq_single n]
      · simp; ring
      · intro k hk hkn
        have : n - k ≠ 0 := by
          have := Finset.mem_range.mp hk; omega
        simp [this]
      · intro h; exact absurd (Finset.self_mem_range_succ n) h
    rw [this]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have s2 : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a k * (3 : ℚ) = 3 * T a n := by
    unfold T
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [s1, s2] at hc
  linarith

lemma b_eq (a b : ℕ → ℚ) (hb0 : b 0 = 1) (ha0 : a 0 = 1)
    (hb : ∀ n : ℕ, 0 < n →
      b n = b (n - 1) + ∑ j ∈ Finset.range n, ((n - 1).choose j : ℚ) * a (j + 1)) :
    ∀ n, b n = T a n := by
  intro n
  induction n with
  | zero => simp [hb0, T, ha0]
  | succ m ih =>
    rw [hb (m + 1) (by omega), Nat.add_sub_cancel, T_succ, ih]
    rfl

theorem mainAux (a b : ℕ → ℚ) (ha : IsA375948 a) (hb0 : b 0 = 1)
    (hb : ∀ n : ℕ, 0 < n →
      b n = b (n - 1) + ∑ j ∈ Finset.range n, ((n - 1).choose j : ℚ) * a (j + 1)) :
    ∀ n : ℕ, 0 < n →
      a n = b (n - 1) + 2 * ∑ j ∈ Finset.range n, (n.choose j : ℚ) * a j := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, b_eq a b hb0 ha.1 hb m]
  have h := ode a ha m
  have hT := T_succ a m
  have hsum : ∑ j ∈ Finset.range (m + 1), ((m + 1).choose j : ℚ) * a j = T a (m + 1) - a (m + 1) := by
    unfold T
    rw [Finset.sum_range_succ _ (m + 1)]
    simp
  rw [hsum]
  linarith

end OMA.S_oeis_a375948

theorem OMA.solution : type_of% @OMA.S_oeis_a375948.main := fun a b ha hb0 hb => OMA.S_oeis_a375948.mainAux a b ha hb0 hb
