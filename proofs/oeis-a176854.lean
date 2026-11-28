import OMAStatements.S_oeis_a176854

-- Mathar's conjecture on the quadratic convolution sequence A176854.
-- Credit: @DrSubspace

open PowerSeries OMA.S_oeis_a176854

namespace OMA.A176854

lemma list_length (n : ℕ) : (aList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [aList, ih]

lemma list_coeff (n i : ℕ) (hi : i ≤ n) : (aList n).getD i 0 = a i := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    by_cases h : i = n + 1
    · subst i; rfl
    · have hi' : i ≤ n := by omega
      cases n with
      | zero =>
        obtain rfl : i = 0 := by omega
        rfl
      | succ n =>
        rw [aList, List.getD_append _ _ _ _ (by rw [list_length]; omega)]
        exact ih hi'

lemma convolution (n : ℕ) :
    a (n+1) = (∑ j ∈ Finset.range (n+1), a j * a (n-j)) - (n+1 : ℤ) := by
  cases n with
  | zero => decide
  | succ n =>
    change (aList (n+2)).getD (n+2) 0 = _
    rw [aList, List.getD_append_right _ _ _ _ (by rw [list_length])]
    simp only [list_length, Nat.sub_self, List.getD_cons_zero]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [list_coeff _ _ (by omega), list_coeff _ _ (by omega)]

noncomputable def F : ℤ⟦X⟧ := mk a

lemma quadratic : (1-X)^2 * (F-1-X*F^2) = -(X : ℤ⟦X⟧) := by
  let H : ℤ⟦X⟧ := mk (fun n => (n : ℤ)+1)
  let L : ℤ⟦X⟧ := mk (fun _ => 1)
  have hF : F = 1 + X * (F*F-H) := by
    ext n
    cases n with
    | zero => simp [F, coeff_zero_eq_constantCoeff, a, aList]
    | succ n =>
      rw [map_add, coeff_succ_X_mul, map_sub, coeff_mul]
      simp only [coeff_one, Nat.succ_ne_zero, if_false, zero_add, F, H, coeff_mk,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simpa only [coeff_mk] using convolution n
  have hH : (1-X)*H=L := by
    ext n
    cases n with
    | zero => simp [sub_mul, H, L, coeff_zero_eq_constantCoeff]
    | succ n => simp [sub_mul, H, L, coeff_succ_X_mul, coeff_mk]
  have hL : (1-X)*L=1 := by
    ext n
    cases n with
    | zero => simp [sub_mul, L, coeff_zero_eq_constantCoeff]
    | succ n => simp [sub_mul, L, coeff_succ_X_mul, coeff_mk, coeff_one]
  linear_combination (1-X)^2*hF - X*(1-X)*hH - X*hL

lemma differential :
    let U := X * derivative ℤ F
    U+F + X*((-7:ℤ) • U - (5:ℤ) • F + X*((19:ℤ) • U + (9:ℤ) • F +
      X*((-17:ℤ) • U - (11:ℤ) • F + X*((4:ℤ) • U + (2:ℤ) • F)))) =
      1 + X*((-5:ℤ) • (1:ℤ⟦X⟧) + X*((3:ℤ) • (1:ℤ⟦X⟧) - X)) := by
  let S : ℤ⟦X⟧ := (1-X)*(1-2*X*F)
  let P : ℤ⟦X⟧ := 1-6*X+13*X^2-4*X^3
  have hs : S^2 = P := by
    dsimp [S,P]
    linear_combination -4*X*quadratic
  have hd := congrArg (derivative ℤ) hs
  simp only [Derivation.leibniz_pow, smul_eq_mul] at hd
  have h : 2 * P * derivative ℤ S = S * derivative ℤ P := by
    rw [← hd, ← hs]
    simp
    ring
  dsimp [S,P] at h
  simp [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, derivative_X] at h
  have d2 : derivative ℤ (2 : ℤ⟦X⟧) = 0 := (derivative ℤ).map_natCast 2
  have d4 : derivative ℤ (4 : ℤ⟦X⟧) = 0 := (derivative ℤ).map_natCast 4
  have d6 : derivative ℤ (6 : ℤ⟦X⟧) = 0 := (derivative ℤ).map_natCast 6
  have d13 : derivative ℤ (13 : ℤ⟦X⟧) = 0 := (derivative ℤ).map_natCast 13
  rw [d2, d4, d6, d13] at h
  dsimp
  simp only [zsmul_eq_mul]
  apply mul_left_cancel₀ (a := (4 : ℤ⟦X⟧)) (by
    intro h₀
    have := congrArg (constantCoeff (R := ℤ)) h₀
    have hc : constantCoeff (4 : ℤ⟦X⟧) = (4 : ℤ) := map_natCast _ 4
    rw [hc, map_zero] at this
    norm_num at this)
  linear_combination -h

end OMA.A176854

theorem OMA.solution : type_of% @OMA.S_oeis_a176854.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
  have hu (j : ℕ) : coeff j (X * derivative ℤ OMA.A176854.F) = (j:ℤ)*a j := by
    cases j with
    | zero => simp [coeff_zero_eq_constantCoeff]
    | succ j =>
      rw [coeff_succ_X_mul, coeff_derivative]
      simp [OMA.A176854.F, coeff_mk, mul_comm]
  have h := congrArg (coeff (k+4)) OMA.A176854.differential
  generalize he : X * derivative ℤ OMA.A176854.F = W at h
  have hw (j : ℕ) : coeff j W = (j:ℤ)*a j := he ▸ hu j
  simp only [map_add, map_sub, map_zsmul, coeff_succ_X_mul, hw] at h
  simp [coeff_succ_X_mul, hw, OMA.A176854.F, coeff_mk, coeff_one, coeff_X] at h
  simp
  push_cast at h ⊢
  linear_combination h
