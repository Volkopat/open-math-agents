import OMAStatements.S_oeis_a205343

/-!
# Excursions of length five with nonzero bounded steps

Write the six heights as (0,x,y,z,t,0). Fixing y and z separates the choices
of x and t. We sum these choices over all pairs, then subtract the diagonal
and the two orientations of pairs more than n apart.
-/

namespace OMA.A205343

open Finset OMA.S_oeis_a205343

private abbrev edge (n u v : ℕ) : Prop := u ≠ v ∧ u ≤ v + n ∧ v ≤ u + n

private theorem edge_iff (n u v : ℕ) :
    (u ≠ v ∧ |(u : ℤ) - v| ≤ n) ↔ edge n u v := by
  rw [abs_le]
  unfold edge
  omega

private theorem chain (n : ℕ) (f : Fin 6 → ℕ) :
    f ∈ arrays n ↔ f 0 = 0 ∧ f 5 = 0 ∧ edge n (f 0) (f 1) ∧ edge n (f 1) (f 2) ∧
      edge n (f 2) (f 3) ∧ edge n (f 3) (f 4) ∧ edge n (f 4) (f 5) := by
  simp only [arrays, Set.mem_ofPred_eq, edge_iff]
  constructor
  · rintro ⟨h0, h5, h⟩
    exact ⟨h0, h5, h 0 1 rfl, h 1 2 rfl, h 2 3 rfl, h 3 4 rfl, h 4 5 rfl⟩
  · rintro ⟨h0, h5, h01, h12, h23, h34, h45⟩
    refine ⟨h0, h5, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | assumption | norm_num at hij

private def encode : ((ℕ × ℕ) × (ℕ × ℕ)) ↪ (Fin 6 → ℕ) where
  toFun p := ![0, p.2.1, p.1.1, p.1.2, p.2.2, 0]
  inj' := by
    rintro ⟨⟨y,z⟩,x,t⟩ ⟨⟨y',z'⟩,x',t'⟩ h
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    change x = x' at h1
    change y = y' at h2
    change z = z' at h3
    change t = t' at h4
    simp [h1, h2, h3, h4]

private def tuples (n : ℕ) :=
  (((range (2*n+1) ×ˢ range (2*n+1)) ×ˢ (Icc 1 n ×ˢ Icc 1 n))).filter
    fun p => edge n p.1.1 p.1.2 ∧ edge n p.2.1 p.1.1 ∧ edge n p.2.2 p.1.2

private theorem array_set (n : ℕ) : arrays n = ↑((tuples n).map encode) := by
  ext f
  rw [chain]
  simp only [mem_coe, mem_map, tuples, mem_filter, mem_product, mem_range, mem_Icc]
  constructor
  · rintro ⟨h0, h5, h01, h12, h23, h34, h45⟩
    refine ⟨((f 2, f 3), (f 1, f 4)), ?_, ?_⟩
    · dsimp [edge] at *
      omega
    · funext i
      fin_cases i <;> first | rfl | exact h0.symm | exact h5.symm
  · rintro ⟨⟨⟨y,z⟩,x,t⟩, h, rfl⟩
    change 0 = 0 ∧ 0 = 0 ∧ edge n 0 x ∧ edge n x y ∧ edge n y z ∧ edge n z t ∧ edge n t 0
    dsimp [edge] at h ⊢
    omega

/-- Number of possible intermediate heights on a two-step walk from 0 to y. -/
private def c (n y : ℕ) : ℚ :=
  ∑ x ∈ Icc 1 n, if edge n x y then 1 else 0

private theorem central_count (n : ℕ) : (a n : ℚ) =
    ∑ y ∈ range (2*n+1), ∑ z ∈ range (2*n+1),
      if edge n y z then c n y * c n z else 0 := by
  rw [a, array_set, Set.ncard_coe_finset, card_map, tuples, card_filter]
  push_cast
  simp only [sum_product]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  by_cases h : edge n y z
  · rw [if_pos h, c, c, sum_mul_sum]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro t _
    split_ifs <;> first | (exfalso; tauto) | norm_num
  · simp [h]

private theorem c_zero (n : ℕ) : c n 0 = n := by
  have e : (Icc 1 n).filter (fun x => edge n x 0) = Icc 1 n := by
    ext x
    simp only [mem_filter, mem_Icc, edge]
    omega
  simp [c, sum_boole, e, Nat.card_Icc]

private theorem c_low {n y : ℕ} (hy : 1 ≤ y) (hn : y ≤ n) : c n y = (n : ℚ) - 1 := by
  have e : (Icc 1 n).filter (fun x => edge n x y) = (Icc 1 n).erase y := by
    ext x
    simp only [mem_filter, mem_erase, mem_Icc, edge]
    omega
  rw [c, sum_boole, e, card_erase_of_mem (mem_Icc.mpr ⟨hy, hn⟩), Nat.card_Icc]
  simp [Nat.cast_sub (show 1 ≤ n by omega)]

private theorem c_high {n j : ℕ} (hj : j < n) : c n (n+1+j) = (n : ℚ) - j := by
  have e : (Icc 1 n).filter (fun x => edge n x (n+1+j)) = Icc (j+1) n := by
    ext x
    simp only [mem_filter, mem_Icc, edge]
    omega
  rw [c, sum_boole, e, Nat.card_Icc, show n+1-(j+1) = n-j by omega,
    Nat.cast_sub (by omega)]

private abbrev heights (n : ℕ) := range (2*n+1)

private theorem split_heights (n : ℕ) (f : ℕ → ℚ) :
    ∑ y ∈ heights n, f y =
      f 0 + (∑ i ∈ range n, f (i+1)) + ∑ j ∈ range n, f (n+1+j) := by
  unfold heights
  rw [show 2*n+1 = (n+1)+n by omega, sum_range_add, sum_range_succ']
  ring

private theorem sum_weights (n : ℕ) (f : ℚ → ℚ) :
    ∑ y ∈ heights n, f (c n y) =
      f n + n * f ((n : ℚ)-1) + ∑ j ∈ range n, f ((n : ℚ)-j) := by
  rw [split_heights, c_zero]
  have lo : ∀ i ∈ range n, f (c n (i+1)) = f ((n : ℚ)-1) := by
    intro i hi
    rw [c_low (by omega) (mem_range.mp hi)]
  have hi : ∀ j ∈ range n, f (c n (n+1+j)) = f ((n : ℚ)-j) := by
    intro j hj
    rw [c_high (mem_range.mp hj)]
  rw [sum_congr rfl lo, sum_congr rfl hi]
  simp [nsmul_eq_mul]

private def far (n y z : ℕ) : ℚ :=
  if y+n < z then c n y * c n z else 0

private theorem edge_weight (n y z : ℕ) :
    (if edge n y z then c n y * c n z else 0) =
      c n y * c n z - (if y = z then (c n y)^2 else 0) - far n y z - far n z y := by
  by_cases e : y = z
  · subst z
    simp [edge, far, pow_two]
  · simp only [if_neg e, sub_zero, far, edge]
    split_ifs <;> first | (exfalso; omega) | ring

private def farColumn (n z : ℕ) : ℚ := ∑ y ∈ heights n, far n y z

/-- Subtract equal heights and the two possible orientations of an oversized middle step. -/
private theorem separate_count (n : ℕ) :
    (a n : ℚ) = (∑ y ∈ heights n, c n y)^2 - (∑ y ∈ heights n, (c n y)^2) -
      2 * ∑ z ∈ heights n, farColumn n z := by
  rw [central_count]
  change (∑ y ∈ heights n, ∑ z ∈ heights n, _) = _
  simp_rw [edge_weight]
  simp only [sum_sub_distrib]
  have total : (∑ y ∈ heights n, ∑ z ∈ heights n, c n y * c n z) =
      (∑ y ∈ heights n, c n y)^2 := by rw [pow_two, sum_mul_sum]
  have diag : (∑ y ∈ heights n, ∑ z ∈ heights n, if y = z then (c n y)^2 else 0) =
      ∑ y ∈ heights n, (c n y)^2 := by
    apply sum_congr rfl
    intro y hy
    simp [hy]
  have swap : (∑ y ∈ heights n, ∑ z ∈ heights n, far n y z) =
      ∑ z ∈ heights n, ∑ y ∈ heights n, far n y z := sum_comm
  rw [total, diag, swap]
  unfold farColumn
  ring

private theorem far_low {n z : ℕ} (hz : z ≤ n) : farColumn n z = 0 := by
  unfold farColumn
  apply sum_eq_zero
  intro y _
  exact if_neg (by omega)

/-- For upper height n+1+j, the disallowed lower heights are exactly 0 through j. -/
private theorem far_high {n j : ℕ} (hj : j < n) :
    farColumn n (n+1+j) = ((n : ℚ) + j * ((n : ℚ)-1)) * ((n : ℚ)-j) := by
  have e : (heights n).filter (fun y => y+n < n+1+j) = range (j+1) := by
    ext y
    simp only [heights, mem_filter, mem_range]
    omega
  unfold farColumn far
  rw [← sum_filter, e, ← sum_mul, c_high hj, sum_range_succ', c_zero]
  have h : ∀ i ∈ range j, c n (i+1) = (n : ℚ)-1 := by
    intro i hi
    have := mem_range.mp hi
    exact c_low (by omega) (by omega)
  rw [sum_congr rfl h]
  rw [sum_const, card_range, nsmul_eq_mul]
  ring

private def firstMoment (n : ℕ) : ℚ := ∑ j ∈ range n, ((n : ℚ)-j)
private def secondMoment (n : ℕ) : ℚ := ∑ j ∈ range n, ((n : ℚ)-j)^2

private theorem far_sum (n : ℕ) : (∑ z ∈ heights n, farColumn n z) =
    (n : ℚ)^2 * firstMoment n - ((n : ℚ)-1) * secondMoment n := by
  rw [split_heights, far_low (Nat.zero_le n)]
  have lo : ∀ i ∈ range n, farColumn n (i+1) = 0 := by
    intro i hi
    exact far_low (mem_range.mp hi)
  have hi : ∀ j ∈ range n, farColumn n (n+1+j) =
      (n : ℚ)^2 * ((n : ℚ)-j) - ((n : ℚ)-1)*((n : ℚ)-j)^2 := by
    intro j hj
    rw [far_high (mem_range.mp hj)]
    ring
  rw [sum_congr rfl lo, sum_congr rfl hi, sum_sub_distrib, ← mul_sum, ← mul_sum]
  simp [firstMoment, secondMoment]

private theorem moments (n : ℕ) :
    firstMoment n = (n : ℚ)*(n+1)/2 ∧ secondMoment n = (n : ℚ)*(n+1)*(2*n+1)/6 := by
  induction n with
  | zero => norm_num [firstMoment, secondMoment]
  | succ n ih =>
    have h1 : firstMoment (n+1) = firstMoment n + ((n : ℚ)+1) := by
      simp only [firstMoment, sum_range_succ', Nat.cast_add, Nat.cast_one, Nat.cast_zero,
        sub_zero, add_sub_add_right_eq_sub]
    have h2 : secondMoment (n+1) = secondMoment n + ((n : ℚ)+1)^2 := by
      simp only [secondMoment, sum_range_succ', Nat.cast_add, Nat.cast_one, Nat.cast_zero,
        sub_zero, add_sub_add_right_eq_sub]
    rw [h1, h2, ih.1, ih.2]
    push_cast
    constructor <;> ring

/-- Hardin's empirical quartic from the entry. -/
def polynomial (n : ℕ) : ℚ :=
  (23*(n : ℚ)^4 - 6*(n : ℚ)^3 + (n : ℚ)^2 - 18*n)/12

theorem count_polynomial (n : ℕ) : (a n : ℚ) = polynomial n := by
  have s1 := sum_weights n (fun x => x)
  have s2 := sum_weights n (fun x => x^2)
  change (∑ y ∈ heights n, c n y) = (n : ℚ) + n * ((n : ℚ)-1) + firstMoment n at s1
  change (∑ y ∈ heights n, (c n y)^2) =
      (n : ℚ)^2 + n * ((n : ℚ)-1)^2 + secondMoment n at s2
  rw [separate_count, s1, s2, far_sum, (moments n).1, (moments n).2]
  unfold polynomial
  ring

private theorem fifth_difference (n : ℕ) (hn : 5 ≤ n) :
    polynomial n = 5 * polynomial (n-1) - 10 * polynomial (n-2) +
      10 * polynomial (n-3) - 5 * polynomial (n-4) + polynomial (n-5) := by
  simp (disch := omega) only [polynomial, Nat.cast_sub, Nat.cast_one, Nat.cast_ofNat]
  ring

private theorem series :
    (PowerSeries.mk fun n => polynomial n) * (1 - PowerSeries.X)^5 =
      2 * PowerSeries.X^2 * (12 + 9*PowerSeries.X + 2*PowerSeries.X^2) := by
  let X : PowerSeries ℚ := PowerSeries.X
  let F : PowerSeries ℚ := PowerSeries.mk fun n => polynomial n
  change F*(1-X)^5 = 2*X^2*(12+9*X+2*X^2)
  have den : F*(1-X)^5 = F - (5 : ℤ) • (F*X^1) + (10 : ℤ) • (F*X^2) -
      (10 : ℤ) • (F*X^3) + (5 : ℤ) • (F*X^4) - F*X^5 := by
    simp [zsmul_eq_mul]; ring
  have num : 2*X^2*(12+9*X+2*X^2) =
      (24 : ℤ) • X^2 + (18 : ℤ) • X^3 + (4 : ℤ) • X^4 := by
    simp [zsmul_eq_mul]; ring
  rw [den, num]
  apply PowerSeries.ext
  intro n
  simp only [F, X, map_sub, map_add, map_zsmul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  by_cases hn : n < 5
  · interval_cases n <;> norm_num [polynomial, zsmul_eq_mul]
  · simp (disch := omega) only [if_pos, if_neg, zsmul_eq_mul, Int.cast_ofNat,
      mul_zero, add_zero]
    linarith only [fifth_difference n (by omega)]

end OMA.A205343

open OMA.S_oeis_a205343 OMA.A205343 in
theorem OMA.solution : type_of% @OMA.S_oeis_a205343.main := by
  constructor
  · have hf : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = polynomial := by
      funext n
      by_cases h : n = 0
      · subst n; norm_num [polynomial]
      · rw [if_neg h, count_polynomial]
    rw [hf]
    exact series
  · intro n hn
    have h : (a n : ℚ) = 5 * (a (n-1) : ℚ) - 10 * (a (n-2) : ℚ) +
        10 * (a (n-3) : ℚ) - 5 * (a (n-4) : ℚ) + (a (n-5) : ℚ) := by
      simp only [count_polynomial]
      exact fifth_difference n (by omega)
    exact_mod_cast h
