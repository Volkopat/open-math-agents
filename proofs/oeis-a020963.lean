import OMAStatements.S_oeis_a020963

namespace OMA.S_oeis_a020963

open PowerSeries


noncomputable def u : ℝ := 1 + Real.sqrt 2
noncomputable def v : ℝ := 1 - Real.sqrt 2

/-- One term: b(m) = floor(2 u^m). -/
noncomputable def b (m : ℤ) : ℤ := ⌊2 * u ^ m⌋

lemma sqrt2_bounds : (1.4 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.5 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

lemma u_gt : (2 : ℝ) < u := by unfold u; linarith [sqrt2_bounds.1]

lemma b_neg (m : ℤ) (hm : m ≤ -1) : b m = 0 := by
  have hu := u_gt
  have hpos : (0 : ℝ) < u := by linarith
  have hle : u ^ m ≤ u ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by linarith) hm
  have hinv : u ^ (-1 : ℤ) = u⁻¹ := zpow_neg_one u
  have hlt : 2 * u⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hpos]
    unfold u; linarith [sqrt2_bounds.1]
  unfold b
  rw [Int.floor_eq_iff]
  constructor
  · push_cast
    have : 0 < u ^ m := zpow_pos hpos m
    linarith
  · push_cast
    rw [hinv] at hle
    linarith

lemma b_zero : b 0 = 2 := by simp [b]

lemma summable_terms (n : ℕ) :
    Summable (fun j : ℕ => ⌊2 * (1 + Real.sqrt 2) ^ ((n : ℤ) - ((j : ℤ) + 1))⌋) := by
  apply summable_of_finite_support
  apply (Set.finite_Iio n).subset
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj
  simp only [Set.mem_Iio]
  by_contra hjn
  apply hj
  have := b_neg ((n : ℤ) - ((j : ℤ) + 1)) (by omega)
  exact this

lemma a_succ (n : ℕ) : a (n + 1) = b n + a n := by
  unfold a
  rw [(summable_terms (n + 1)).tsum_eq_zero_add]
  congr 1
  · simp only [b, u]
    congr 2
    push_cast
    ring_nf
  · congr 1
    ext j
    congr 3
    push_cast
    ring

lemma a_zero : a 0 = 0 := by
  unfold a
  have : ∀ j : ℕ, ⌊2 * (1 + Real.sqrt 2) ^ (((0 : ℕ) : ℤ) - ((j : ℤ) + 1))⌋ = 0 := fun j =>
    b_neg _ (by omega)
  exact (tsum_congr this).trans tsum_zero

/-- Q(m) = 2 (u^m + v^m). -/
def Q : ℕ → ℤ
  | 0 => 4
  | 1 => 4
  | m + 2 => 2 * Q (m + 1) + Q m

lemma Q_cast (m : ℕ) : (Q m : ℝ) = 2 * (u ^ m + v ^ m) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hu : u ^ 2 = 2 * u + 1 := by unfold u; nlinarith
  have hv : v ^ 2 = 2 * v + 1 := by unfold v; nlinarith
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · norm_num [Q]
    · simp only [Q, pow_one]; unfold u v; push_cast; ring
    · rw [Q]
      push_cast
      rw [ih (m + 1) (by omega), ih m (by omega), pow_add u m 2, pow_add v m 2, hu, hv]
      ring

lemma v_bounds : -(1 / 2 : ℝ) < v ∧ v < 0 := by
  unfold v; constructor <;> linarith [sqrt2_bounds.1, sqrt2_bounds.2]

/-- For m >= 1, b(m) = Q(m) - 1 when m is even and Q(m) when m is odd. -/
lemma b_pos (m : ℕ) (hm : 1 ≤ m) : b m = Q m - (if m % 2 = 0 then 1 else 0) := by
  obtain ⟨hv1, hv2⟩ := v_bounds
  have habs : |v| < 1 / 2 := by rw [abs_of_neg hv2]; linarith
  have hpow : |v| ^ m ≤ |v| := by
    calc |v| ^ m = |v| ^ (m - 1) * |v| := by rw [← pow_succ, Nat.sub_add_cancel hm]
      _ ≤ 1 * |v| := by gcongr; exact pow_le_one₀ (abs_nonneg v) (by linarith)
      _ = |v| := one_mul _
  have hsmall : |2 * v ^ m| < 1 := by
    rw [abs_mul, abs_pow]; norm_num; linarith
  have hQ := Q_cast m
  have h2u : 2 * u ^ (m : ℤ) = (Q m : ℝ) - 2 * v ^ m := by
    rw [zpow_natCast, hQ]; ring
  unfold b
  rw [h2u, Int.floor_eq_iff]
  rcases Nat.even_or_odd m with he | ho
  · have hpos : 0 < v ^ m := he.pow_pos (ne_of_lt hv2)
    have : m % 2 = 0 := Nat.even_iff.mp he
    rw [if_pos this]
    have := (abs_lt.mp hsmall)
    push_cast
    constructor <;> linarith
  · have hneg : v ^ m < 0 := ho.pow_neg hv2
    have : m % 2 ≠ 0 := by rw [Nat.odd_iff] at ho; omega
    rw [if_neg this]
    have := (abs_lt.mp hsmall)
    push_cast
    constructor <;> linarith

lemma b_rec (m : ℕ) (hm : 1 ≤ m) :
    b (m + 4 : ℕ) - 2 * b (m + 3 : ℕ) - 2 * b (m + 2 : ℕ) + 2 * b (m + 1 : ℕ) + b m = 0 := by
  rw [b_pos _ (by omega), b_pos _ (by omega), b_pos _ (by omega), b_pos _ (by omega), b_pos _ hm]
  have q4 : Q (m + 4) = 2 * Q (m + 3) + Q (m + 2) := rfl
  have q3 : Q (m + 3) = 2 * Q (m + 2) + Q (m + 1) := rfl
  have q2 : Q (m + 2) = 2 * Q (m + 1) + Q m := rfl
  have e1 : (m + 4) % 2 = m % 2 := by omega
  have e2 : (m + 2) % 2 = m % 2 := by omega
  have e3 : (m + 3) % 2 = (m + 1) % 2 := by omega
  rw [e1, e2, e3, q4, q3, q2]
  split_ifs <;> ring

/-- Wu's recurrence: a(n) = 3a(n-1) - 4a(n-3) + a(n-4) + a(n-5) for n > 5. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    a n = 3 * a (n - 1) - 4 * a (n - 3) + a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h := b_rec (m + 1) (by omega)
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 3 = m + 3 by omega,
    show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
  have s5 := a_succ (m + 5)
  have s4 := a_succ (m + 4)
  have s3 := a_succ (m + 3)
  have s2 := a_succ (m + 2)
  have s1 := a_succ (m + 1)
  rw [show m + 1 + 4 = m + 5 by omega, show m + 1 + 3 = m + 4 by omega,
    show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at h
  push_cast at h s1 s2 s3 s4 s5
  linarith

lemma a_vals : a 1 = 2 ∧ a 2 = 6 ∧ a 3 = 17 ∧ a 4 = 45 ∧ a 5 = 112 := by
  have b1 := b_pos 1 (by norm_num)
  have b2 := b_pos 2 (by norm_num)
  have b3 := b_pos 3 (by norm_num)
  have b4 := b_pos 4 (by norm_num)
  have h1 := a_succ 0
  have h2 := a_succ 1
  have h3 := a_succ 2
  have h4 := a_succ 3
  have h5 := a_succ 4
  simp only [Q] at b1 b2 b3 b4
  norm_num at b1 b2 b3 b4
  push_cast at h1 h2 h3 h4 h5
  rw [a_zero, b_zero] at h1
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Wu's g.f., as A(x) * ((x-1)^2 (x+1)(x^2+2x-1)) = x (x^4 - 2x^3 + x^2 - 2) in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) ^ 2 * (X + 1) * (X ^ 2 + 2 * X - 1)) = X * (X ^ 4 - 2 * X ^ 3 + X ^ 2 - 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hD : ((X - 1) ^ 2 * (X + 1) * (X ^ 2 + 2 * X - 1) : ℚ⟦X⟧) =
      -1 + C (3 : ℚ) * X ^ 1 - C (4 : ℚ) * X ^ 3 + X ^ 4 + X ^ 5 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4]
    ring
  have hN : (X * (X ^ 4 - 2 * X ^ 3 + X ^ 2 - 2) : ℚ⟦X⟧) =
      -(C (2 : ℚ) * X ^ 1) + X ^ 3 - C (2 : ℚ) * X ^ 4 + X ^ 5 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
    ring
  have e : A * (-1 + C (3 : ℚ) * X ^ 1 - C (4 : ℚ) * X ^ 3 + X ^ 4 + X ^ 5) =
      -A + C (3 : ℚ) * (A * X ^ 1) - C (4 : ℚ) * (A * X ^ 3) + A * X ^ 4 + A * X ^ 5 := by ring
  rw [hD, hN, e]
  obtain ⟨v1, v2, v3, v4, v5⟩ := a_vals
  ext n
  simp only [map_sub, map_neg, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5] <;> norm_num
  · have hr := recurrence n (by omega)
    simp only [coeff_C, show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega, if_true, show n ≠ 0 by omega, show n - 1 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, if_false]
    rw [hr]
    push_cast
    ring

/-- Both of Wu's conjectures. -/
theorem conjecture : (∀ n : ℕ, 5 < n → a n = 3 * a (n - 1) - 4 * a (n - 3) + a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) ^ 2 * (X + 1) * (X ^ 2 + 2 * X - 1)) = X * (X ^ 4 - 2 * X ^ 3 + X ^ 2 - 2) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a020963

theorem OMA.solution : type_of% @OMA.S_oeis_a020963.main :=
  OMA.S_oeis_a020963.conjecture
