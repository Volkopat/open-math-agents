import OMAStatements.S_oeis_a048331

namespace OMA.S_oeis_a048331



/-- The conjecture (the recurrence). -/
def Conjecture : Prop := ∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 7 * a (n - 5) - 6 * a (n - 10)

/-- The base-6 repunit `1 + 6 + … + 6^(k-1)`. -/
def R (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, 6 ^ i

theorem R_succ (k : ℕ) : R (k + 1) = 6 * R k + 1 := by
  unfold R
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

theorem R_pos (k : ℕ) (hk : 1 ≤ k) : 1 ≤ R k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [R_succ]
  omega

theorem ofDigits_replicate (k d : ℕ) : Nat.ofDigits 6 (List.replicate k d) = d * R k := by
  induction k with
  | zero => simp [R]
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, R_succ]
    ring

theorem digits_rep (k d : ℕ) (hd1 : 1 ≤ d) (hd6 : d < 6) :
    Nat.digits 6 (d * R k) = List.replicate k d := by
  rw [← ofDigits_replicate]
  apply Nat.digits_ofDigits 6 (by norm_num)
  · intro l hl
    rw [List.eq_of_mem_replicate hl]
    exact hd6
  · intro h
    rw [List.getLast_replicate]
    omega

/-- The enumeration: `f 0 = 0`, `f (5q + r + 1) = (r + 1) * R (q + 1)` for `r < 5`. -/
def f (j : ℕ) : ℕ := if j = 0 then 0 else ((j - 1) % 5 + 1) * R ((j - 1) / 5 + 1)

theorem f_rep (j : ℕ) : Rep (f j) := by
  unfold f
  split_ifs with h
  · intro x hx
    simp at hx
  · intro x hx y hy
    rw [digits_rep _ _ (by omega) (by omega)] at hx hy
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]

theorem f_surj (m : ℕ) (hm : Rep m) : ∃ j, f j = m := by
  by_cases h0 : m = 0
  · exact ⟨0, by simp [f, h0]⟩
  have hne : Nat.digits 6 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr h0
  obtain ⟨d, L', hdL⟩ : ∃ d L', Nat.digits 6 m = d :: L' := by
    cases hc : Nat.digits 6 m with
    | nil => exact absurd hc hne
    | cons d L' => exact ⟨d, L', rfl⟩
  have hall : ∀ x ∈ Nat.digits 6 m, x = d := fun x hx => hm x hx d (by rw [hdL]; simp)
  obtain ⟨k, hk'⟩ : ∃ k, (Nat.digits 6 m).length = k := ⟨_, rfl⟩
  have hrep : Nat.digits 6 m = List.replicate k d := by
    rw [← hk']
    exact List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  have hd6 : d < 6 := Nat.digits_lt_base (by norm_num) (by rw [hdL]; simp)
  have hk : 1 ≤ k := by
    rw [← hk', hdL]
    simp
  have hm' : m = d * R k := by
    conv_lhs => rw [← Nat.ofDigits_digits 6 m, hrep]
    rw [ofDigits_replicate]
  have hd0 : d ≠ 0 := fun h => h0 (by rw [hm', h, zero_mul])
  refine ⟨5 * (k - 1) + (d - 1) + 1, ?_⟩
  unfold f
  rw [if_neg (by omega), hm']
  have e1 : (5 * (k - 1) + (d - 1) + 1 - 1) % 5 = d - 1 := by omega
  have e2 : (5 * (k - 1) + (d - 1) + 1 - 1) / 5 = k - 1 := by omega
  rw [e1, e2, show d - 1 + 1 = d by omega, show k - 1 + 1 = k by omega]

theorem f_lt_succ (j : ℕ) : f j < f (j + 1) := by
  unfold f
  by_cases hj : j = 0
  · subst hj
    simp [R]
  · rw [if_neg hj, if_neg (by omega)]
    have hR := R_pos ((j - 1) / 5 + 1) (by omega)
    by_cases hr : (j - 1) % 5 < 4
    · have e1 : (j + 1 - 1) % 5 = (j - 1) % 5 + 1 := by omega
      have e2 : (j + 1 - 1) / 5 = (j - 1) / 5 := by omega
      rw [e1, e2]
      nlinarith
    · have e1 : (j + 1 - 1) % 5 = 0 := by omega
      have e2 : (j + 1 - 1) / 5 = (j - 1) / 5 + 1 := by omega
      have e3 : (j - 1) % 5 = 4 := by omega
      rw [e1, e2, e3, R_succ ((j - 1) / 5 + 1)]
      omega

theorem f_strictMono : StrictMono f := strictMono_nat_of_lt_succ f_lt_succ

theorem Rep_infinite : (Set.ofPred Rep).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  have h1 : N + 1 ≤ f (N + 1) := f_strictMono.le_apply
  have := hN (show f (N + 1) ∈ Set.ofPred Rep from f_rep (N + 1))
  omega

theorem f_eq_nth (n : ℕ) : f n = Nat.nth Rep n := by
  have hall : ∀ n, n ∈ {n : ℕ | ∀ hf : (Set.ofPred Rep).Finite, n < hf.toFinset.card} :=
    fun n hf => absurd hf Rep_infinite
  refine Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hall n)
  · intro m hm
    obtain ⟨j, hj⟩ := f_surj m hm
    exact ⟨j, hall j, hj⟩
  · intro j _
    exact f_rep j
  · intro x _ y _ hxy
    exact f_strictMono hxy

theorem conjecture_true : Conjecture := by
  intro n hn
  rw [a, a, a, ← f_eq_nth, ← f_eq_nth, ← f_eq_nth]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
  rw [show j + 10 - 5 = j + 5 by omega, show j + 10 - 10 = j by omega]
  by_cases hj : j = 0
  · subst hj
    simp [f, R, Finset.sum_range_succ]
  · unfold f
    rw [if_neg (by omega), if_neg (by omega), if_neg hj]
    have e1 : (j + 10 - 1) % 5 = (j - 1) % 5 := by omega
    have e2 : (j + 5 - 1) % 5 = (j - 1) % 5 := by omega
    have e3 : (j + 10 - 1) / 5 = (j - 1) / 5 + 2 := by omega
    have e4 : (j + 5 - 1) / 5 = (j - 1) / 5 + 1 := by omega
    rw [e1, e2, e3, e4, show (j - 1) / 5 + 2 + 1 = ((j - 1) / 5 + 1) + 1 + 1 by ring,
      R_succ (((j - 1) / 5 + 1) + 1), R_succ ((j - 1) / 5 + 1)]
    push_cast
    ring

/-- Control: the first terms listed in the entry. -/
theorem first_terms : a 0 = 0 ∧ a 1 = 1 ∧ a 5 = 5 ∧ a 6 = 7 ∧ a 10 = 35 ∧ a 11 = 43 ∧
    a 15 = 215 := by
  simp only [a, ← f_eq_nth]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The terms `a(0..9)`, used for the low coefficients of the g.f. -/
theorem low_terms : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 4 ∧ a 5 = 5 ∧ a 6 = 7 ∧
    a 7 = 14 ∧ a 8 = 21 ∧ a 9 = 28 := by
  simp only [a, ← f_eq_nth]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

open PowerSeries in
/-- Mathar's g.f. as an identity of formal power series: from `x^10` on the coefficients of the
product are the recurrence, below they are `a(0..9)`. -/
theorem gf_identity :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (6 * X ^ 5 - 1)) =
      X * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4) := by
  have hN : (X * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4) : ℚ⟦X⟧) =
      C 1 * X ^ 1 + C 2 * X ^ 2 + C 3 * X ^ 3 + C 4 * X ^ 4 + C 5 * X ^ 5 := by
    simp only [map_ofNat, map_one]
    ring
  have e : ∀ A : ℚ⟦X⟧, A * ((X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (6 * X ^ 5 - 1)) =
      A - C 7 * (A * X ^ 5) + C 6 * (A * X ^ 10) := by
    intro A
    simp only [map_ofNat]
    ring
  rw [hN, e]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 10 with hn | hn
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := low_terms
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] <;> norm_num
  · have hr : (a n : ℚ) = 7 * a (n - 5) - 6 * a (n - 10) := by
      exact_mod_cast conjecture_true n hn
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 10 ≤ n by omega, show n - 1 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      show n - 5 ≠ 0 by omega, if_true, if_false]
    linarith

end OMA.S_oeis_a048331

theorem OMA.solution : type_of% @OMA.S_oeis_a048331.main :=
  ⟨OMA.S_oeis_a048331.gf_identity, OMA.S_oeis_a048331.conjecture_true⟩
