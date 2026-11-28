import OMAStatements.S_oeis_a048330

-- Original proof by @jleguina.

namespace OMA.S_oeis_a048330

/-- The conjecture (the recurrence). -/
def Conjecture : Prop := ∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 6 * a (n - 4) - 5 * a (n - 8)

/-- The base-5 repunit `1 + 5 + … + 5^(k-1)`. -/
def R (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, 5 ^ i

theorem R_succ (k : ℕ) : R (k + 1) = 5 * R k + 1 := by
  unfold R
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

theorem R_pos (k : ℕ) (hk : 1 ≤ k) : 1 ≤ R k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [R_succ]
  omega

theorem ofDigits_replicate (k d : ℕ) : Nat.ofDigits 5 (List.replicate k d) = d * R k := by
  induction k with
  | zero => simp [R]
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, R_succ]
    ring

theorem digits_rep (k d : ℕ) (hd1 : 1 ≤ d) (hd5 : d < 5) :
    Nat.digits 5 (d * R k) = List.replicate k d := by
  rw [← ofDigits_replicate]
  apply Nat.digits_ofDigits 5 (by norm_num)
  · intro l hl
    rw [List.eq_of_mem_replicate hl]
    exact hd5
  · intro h
    rw [List.getLast_replicate]
    omega

/-- The enumeration: `f 0 = 0`, `f (4q + r + 1) = (r + 1) * R (q + 1)` for `r < 4`. -/
def f (j : ℕ) : ℕ := if j = 0 then 0 else ((j - 1) % 4 + 1) * R ((j - 1) / 4 + 1)

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
  have hne : Nat.digits 5 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr h0
  obtain ⟨d, L', hdL⟩ : ∃ d L', Nat.digits 5 m = d :: L' := by
    cases hc : Nat.digits 5 m with
    | nil => exact absurd hc hne
    | cons d L' => exact ⟨d, L', rfl⟩
  have hall : ∀ x ∈ Nat.digits 5 m, x = d := fun x hx => hm x hx d (by rw [hdL]; simp)
  obtain ⟨k, hk'⟩ : ∃ k, (Nat.digits 5 m).length = k := ⟨_, rfl⟩
  have hrep : Nat.digits 5 m = List.replicate k d := by
    rw [← hk']
    exact List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  have hd5 : d < 5 := Nat.digits_lt_base (by norm_num) (by rw [hdL]; simp)
  have hk : 1 ≤ k := by
    rw [← hk', hdL]
    simp
  have hm' : m = d * R k := by
    conv_lhs => rw [← Nat.ofDigits_digits 5 m, hrep]
    rw [ofDigits_replicate]
  have hd0 : d ≠ 0 := fun h => h0 (by rw [hm', h, zero_mul])
  refine ⟨4 * (k - 1) + (d - 1) + 1, ?_⟩
  unfold f
  rw [if_neg (by omega), hm']
  have e1 : (4 * (k - 1) + (d - 1) + 1 - 1) % 4 = d - 1 := by omega
  have e2 : (4 * (k - 1) + (d - 1) + 1 - 1) / 4 = k - 1 := by omega
  rw [e1, e2, show d - 1 + 1 = d by omega, show k - 1 + 1 = k by omega]

theorem f_lt_succ (j : ℕ) : f j < f (j + 1) := by
  unfold f
  by_cases hj : j = 0
  · subst hj
    simp [R]
  · rw [if_neg hj, if_neg (by omega)]
    have hR := R_pos ((j - 1) / 4 + 1) (by omega)
    by_cases hr : (j - 1) % 4 < 3
    · have e1 : (j + 1 - 1) % 4 = (j - 1) % 4 + 1 := by omega
      have e2 : (j + 1 - 1) / 4 = (j - 1) / 4 := by omega
      rw [e1, e2]
      nlinarith
    · have e1 : (j + 1 - 1) % 4 = 0 := by omega
      have e2 : (j + 1 - 1) / 4 = (j - 1) / 4 + 1 := by omega
      have e3 : (j - 1) % 4 = 3 := by omega
      rw [e1, e2, e3, R_succ ((j - 1) / 4 + 1)]
      omega

theorem f_strictMono : StrictMono f := strictMono_nat_of_lt_succ f_lt_succ

theorem Rep_infinite : (Set.ofPred Rep).Infinite :=
  (Set.infinite_range_of_injective f_strictMono.injective).mono (Set.range_subset_iff.2 f_rep)

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

/-- Append one more copy of the same base-five digit. -/
theorem f_step (j : ℕ) (hj : 0 < j) : f (j + 4) = 5 * f j + ((j - 1) % 4 + 1) := by
  unfold f
  rw [if_neg (by omega), if_neg (by omega),
    show (j + 4 - 1) % 4 = (j - 1) % 4 by omega,
    show (j + 4 - 1) / 4 + 1 = (j - 1) / 4 + 1 + 1 by omega, R_succ]
  ring

theorem conjecture_true : Conjecture := by
  intro n hn
  rw [a, a, a, ← f_eq_nth, ← f_eq_nth, ← f_eq_nth]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
  rw [show j + 8 - 4 = j + 4 by omega, show j + 8 - 8 = j by omega]
  by_cases hj : j = 0
  · subst hj
    simp [f, R, Finset.sum_range_succ]
  · have h1 := f_step j (by omega)
    have h2 := f_step (j + 4) (by omega)
    rw [show j + 4 + 4 = j + 8 by omega, show (j + 4 - 1) % 4 = (j - 1) % 4 by omega] at h2
    apply eq_sub_iff_add_eq.mpr
    exact_mod_cast (show f (j + 8) + 5 * f j = 6 * f (j + 4) by omega)

/-- Control: the first terms listed in the entry. -/
theorem first_terms : a 0 = 0 ∧ a 1 = 1 ∧ a 4 = 4 ∧ a 5 = 6 ∧ a 8 = 24 ∧ a 9 = 31 ∧
    a 12 = 124 ∧ a 13 = 156 ∧ a 20 = 3124 := by
  simp only [a, ← f_eq_nth]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

open PowerSeries in
/-- Mathar's g.f. as an identity of formal power series: from `x^8` on the coefficients of the
product are the recurrence, below they are `a(0..7)`. -/
theorem gf_identity :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) * (1 + X) * (X ^ 2 + 1) * (5 * X ^ 4 - 1)) =
      X * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3) := by
  have hN : (X * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3) : ℚ⟦X⟧) =
      C 1 * X ^ 1 + C 2 * X ^ 2 + C 3 * X ^ 3 + C 4 * X ^ 4 := by
    simp only [map_ofNat, map_one]
    ring
  have e : ∀ A : ℚ⟦X⟧, A * ((X - 1) * (1 + X) * (X ^ 2 + 1) * (5 * X ^ 4 - 1)) =
      A - C 6 * (A * X ^ 4) + C 5 * (A * X ^ 8) := by
    intro A
    simp only [map_ofNat]
    ring
  rw [hN, e]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> norm_num [a, ← f_eq_nth, f, R, Finset.sum_range_succ]
  · have hr : (a n : ℚ) = 6 * a (n - 4) - 5 * a (n - 8) := by
      exact_mod_cast conjecture_true n hn
    simp (disch := omega) [hn, if_neg, if_pos]
    linarith

end OMA.S_oeis_a048330

theorem OMA.solution : type_of% @OMA.S_oeis_a048330.main :=
  ⟨OMA.S_oeis_a048330.gf_identity, OMA.S_oeis_a048330.conjecture_true⟩
