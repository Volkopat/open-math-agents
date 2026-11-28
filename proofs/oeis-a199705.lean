import OMAStatements.S_oeis_a199705

namespace OMA.S_oeis_a199705


/-- The admissible first entries for middle entry `y`. -/
noncomputable def c (n : ℕ) (y : ℤ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n).filter
    (fun x => -(n : ℤ) ≤ x + y ∧ x + y ≤ n ∧ x ≠ y ∧ x + 2 * y ≠ 0)).card

lemma a_eq_sum (n : ℕ) : a n = ∑ y ∈ Finset.Icc (-(n : ℤ)) n, c n y := by
  unfold a
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℤ × ℤ × ℤ => p.2.1)
    (t := Finset.Icc (-(n : ℤ)) n)]
  · refine Finset.sum_congr rfl fun y hy => ?_
    unfold c
    refine Finset.card_nbij' (fun p => p.1) (fun x => (x, y, -x - y)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.coe_filter,
        Set.mem_setOf_eq] at hp ⊢
      obtain ⟨⟨⟨h1, h2, h3⟩, h4, h5, h6⟩, h7⟩ := hp
      subst h7
      refine ⟨h1, by omega, by omega, h5, by omega⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.coe_filter,
        Set.mem_setOf_eq] at hx ⊢
      obtain ⟨h1, h2, h3, h4, h5⟩ := hx
      exact ⟨⟨⟨h1, Finset.mem_Icc.mp hy, by omega, by omega⟩, by ring, h4, by omega⟩, trivial⟩
    · intro p hp
      obtain ⟨u, v, w⟩ := p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.coe_filter,
        Set.mem_setOf_eq] at hp
      obtain ⟨⟨_, h4, _, _⟩, h7⟩ := hp
      show (u, y, -u - y) = (u, v, w)
      have hw : w = -u - y := by omega
      have hv : v = y := by simpa using h7
      rw [hv, hw]
    · intro x _
      rfl
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product] at hp ⊢
    exact hp.1.2.1

/-- Closed form of `c n y` for `|y| ≤ n`. -/
lemma c_eq (n : ℕ) (y : ℤ) (hy1 : -(n : ℤ) ≤ y) (hy2 : y ≤ n) :
    (c n y : ℤ) = 2 * n + 1 - |y| - (if 2 * |y| ≤ n then 2 else 0) + (if y = 0 then 1 else 0) := by
  unfold c
  -- the admissible `x` are `[lo, hi]` minus the bad points `y` and `-2y`
  obtain ⟨lo, hi, hlohi, hIccdef, hlen⟩ : ∃ lo hi : ℤ, lo ≤ hi + 1 ∧
      (∀ x : ℤ, ((-(n : ℤ) ≤ x ∧ x ≤ n) ∧ -(n : ℤ) ≤ x + y ∧ x + y ≤ n) ↔ (lo ≤ x ∧ x ≤ hi)) ∧
      hi + 1 - lo = 2 * n + 1 - |y| := by
    rcases le_or_gt 0 y with h0 | h0
    · exact ⟨-(n : ℤ), n - y, by omega, fun x => by omega, by rw [abs_of_nonneg h0]; ring⟩
    · exact ⟨-(n : ℤ) - y, n, by omega, fun x => by omega, by rw [abs_of_neg h0]; ring⟩
  have hset : (Finset.Icc (-(n : ℤ)) n).filter
      (fun x => -(n : ℤ) ≤ x + y ∧ x + y ≤ n ∧ x ≠ y ∧ x + 2 * y ≠ 0) =
      (Finset.Icc lo hi).filter (fun x => ¬ (x = y ∨ x + 2 * y = 0)) := by
    ext x
    have := hIccdef x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨this.mp ⟨h1, h2, h3⟩, by omega⟩
    · rintro ⟨h1, h2⟩
      have := this.mpr h1
      exact ⟨this.1, this.2.1, this.2.2, by omega, by omega⟩
  have hs := Finset.card_filter_add_card_filter_not (s := Finset.Icc lo hi)
    (fun x => x = y ∨ x + 2 * y = 0)
  have hyin : 2 * |y| ≤ n → (lo ≤ y ∧ y ≤ hi) ∧ (lo ≤ -2 * y ∧ -2 * y ≤ hi) := by
    intro h
    have hy' := abs_le.mp (show |y| ≤ n by omega)
    have h2 : -(n : ℤ) ≤ 2 * y ∧ 2 * y ≤ n := by
      constructor <;> cases abs_cases y <;> omega
    exact ⟨(hIccdef y).mp ⟨⟨hy1, hy2⟩, by omega, by omega⟩,
      (hIccdef (-2 * y)).mp ⟨⟨by omega, by omega⟩, by omega, by omega⟩⟩
  have hyout : ¬ (2 * |y| ≤ n) → ∀ x, (lo ≤ x ∧ x ≤ hi) → ¬ (x = y ∨ x + 2 * y = 0) := by
    intro h x hx hxy
    have h2 : ¬ (-(n : ℤ) ≤ 2 * y ∧ 2 * y ≤ n) := by
      intro h'
      apply h
      cases abs_cases y <;> omega
    have := (hIccdef x).mpr hx
    rcases hxy with rfl | hx2
    · exact h2 ⟨by omega, by omega⟩
    · exact h2 ⟨by omega, by omega⟩
  have hb : (((Finset.Icc lo hi).filter (fun x => x = y ∨ x + 2 * y = 0)).card : ℤ) =
      (if 2 * |y| ≤ n then 2 else 0) - (if y = 0 then 1 else 0) := by
    by_cases h2 : 2 * |y| ≤ n
    · obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hyin h2
      by_cases h0 : y = 0
      · subst h0
        have : (Finset.Icc lo hi).filter (fun x => x = 0 ∨ x + 2 * 0 = 0) = {0} := by
          ext x; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]; omega
        rw [this, if_pos h2]; simp
      · have : (Finset.Icc lo hi).filter (fun x => x = y ∨ x + 2 * y = 0) = {y, -2 * y} := by
          ext x; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
            Finset.mem_singleton]; omega
        rw [this, Finset.card_pair (by omega), if_pos h2, if_neg h0]; norm_num
    · have : (Finset.Icc lo hi).filter (fun x => x = y ∨ x + 2 * y = 0) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
        intro h1 h1'
        exact hyout h2 x h1 h1'
      have hy0 : y ≠ 0 := by intro h; subst h; simp at h2
      rw [this, if_neg h2, if_neg hy0]; simp
  have hcard : ((Finset.Icc lo hi).card : ℤ) = 2 * n + 1 - |y| := by
    rw [Int.card_Icc, ← hlen]; omega
  rw [hset]
  omega

/-- The closed form of `c`, as a function. -/
def f (m : ℕ) (y : ℤ) : ℤ :=
  2 * m + 1 - |y| - (if 2 * |y| ≤ m then 2 else 0) + (if y = 0 then 1 else 0)

lemma a_eq_range (m : ℕ) : (a m : ℤ) = ∑ k ∈ Finset.range (2 * m + 1), f m ((k : ℤ) - m) := by
  rw [a_eq_sum]
  push_cast
  rw [Finset.sum_congr rfl fun y hy => c_eq m y (Finset.mem_Icc.mp hy).1 (Finset.mem_Icc.mp hy).2]
  refine Finset.sum_nbij' (fun y => (y + m).toNat) (fun k => (k : ℤ) - m) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_Icc, Finset.mem_range] at hy ⊢
    omega
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
    omega
  · intro y hy
    simp only [Finset.mem_Icc] at hy
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    omega
  · intro y hy
    simp only [Finset.mem_Icc] at hy
    rw [show ((y + m).toNat : ℤ) - m = y by omega]
    rfl

lemma f_succ (n : ℕ) (y : ℤ) :
    f (n + 1) y = f n y + 2 - (if 2 * |y| = n + 1 then 2 else 0) := by
  unfold f
  push_cast
  split_ifs <;> omega

lemma count_half (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1), (if 2 * |(k : ℤ) - n| = n + 1 then (2 : ℤ) else 0) =
      if n % 2 = 1 then 4 else 0 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have : (Finset.range (2 * n + 1)).filter (fun k : ℕ => 2 * |(k : ℤ) - n| = n + 1) = ∅ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
      intro _ hk
      cases abs_cases ((k : ℤ) - n) <;> omega
    rw [this, if_neg (by omega)]; simp
  · have : (Finset.range (2 * n + 1)).filter (fun k : ℕ => 2 * |(k : ℤ) - n| = n + 1) =
        {n - (n + 1) / 2, n + (n + 1) / 2} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hk, h2⟩
        cases abs_cases ((k : ℤ) - n) <;> omega
      · rintro (rfl | rfl)
        · refine ⟨by omega, ?_⟩
          rw [abs_of_nonpos (by omega)]; omega
        · refine ⟨by omega, ?_⟩
          rw [abs_of_nonneg (by omega)]; omega
    rw [this, Finset.card_pair (by omega), if_pos h]; norm_num

/-- `a(n+1) = a(n) + 6n + 6 - 4 [n odd]`. -/
lemma a_succ (n : ℕ) : (a (n + 1) : ℤ) = a n + 6 * n + 6 - (if n % 2 = 1 then 4 else 0) := by
  rw [a_eq_range, a_eq_range, show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring,
    Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∑ k ∈ Finset.range (2 * n + 1), f (n + 1) (((k + 1 : ℕ) : ℤ) - (n + 1 : ℕ)) =
      ∑ k ∈ Finset.range (2 * n + 1), f n ((k : ℤ) - n) + 2 * (2 * n + 1) - (if n % 2 = 1 then 4 else 0) := by
    rw [← count_half n]
    have e : ∀ k ∈ Finset.range (2 * n + 1), f (n + 1) (((k + 1 : ℕ) : ℤ) - (n + 1 : ℕ)) =
        f n ((k : ℤ) - n) + 2 - (if 2 * |(k : ℤ) - n| = n + 1 then 2 else 0) := by
      intro k _
      rw [show (((k + 1 : ℕ) : ℤ) - (n + 1 : ℕ)) = (k : ℤ) - n by push_cast; ring, f_succ]
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  rw [hmid]
  have h0 : f (n + 1) (((0 : ℕ) : ℤ) - (n + 1 : ℕ)) = n + 2 := by
    unfold f
    push_cast
    rw [abs_of_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
  have htop : f (n + 1) (((2 * n + 1 + 1 : ℕ) : ℤ) - (n + 1 : ℕ)) = n + 2 := by
    unfold f
    push_cast
    rw [abs_of_pos (by omega), if_neg (by omega), if_neg (by omega)]; ring
  rw [h0, htop]
  ring

/-- Barker's formulas: `a(n) = n + 3n^2` for even `n`, `a(n) = 2 + n + 3n^2` for odd `n`. -/
theorem formula (n : ℕ) : (a n : ℤ) = n + 3 * n ^ 2 + (if n % 2 = 1 then 2 else 0) := by
  induction n with
  | zero => rw [a_eq_range]; simp [f]
  | succ n ih =>
    rw [a_succ, ih]
    push_cast
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; ring
    · rw [if_pos h, if_pos h, if_neg (by omega)]; ring

theorem even_formula (n : ℕ) (he : n % 2 = 0) : (a n : ℤ) = n + 3 * n ^ 2 := by
  rw [formula, if_neg (by omega)]; ring

theorem odd_formula (n : ℕ) (ho : n % 2 = 1) : (a n : ℤ) = 2 + n + 3 * n ^ 2 := by
  rw [formula, if_pos ho]; ring

open PowerSeries in
/-- Barker's g.f. `2x(3 + x + 2x^2)/((1-x)^3(1+x))` (offset 1; `a 0 = 0`), in `ℚ⟦X⟧`. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (2 * X * (3 + X + 2 * X ^ 2)) * ((1 - X) ^ 3 * (1 + X))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hden : constantCoeff ((1 - X) ^ 3 * (1 + X) : ℚ⟦X⟧) ≠ 0 := by simp
  have hq : ∀ n, (a n : ℚ) = n + 3 * n ^ 2 + (if n % 2 = 1 then 2 else 0) := by
    intro n; have := formula n; split_ifs at this ⊢ <;> exact_mod_cast this
  have key : A * ((1 - X) ^ 3 * (1 + X)) =
      X ^ 1 + X ^ 1 + X ^ 1 + X ^ 1 + X ^ 1 + X ^ 1 + X ^ 2 + X ^ 2 + X ^ 3 + X ^ 3 + X ^ 3
        + X ^ 3 := by
    have e1 : A * ((1 - X) ^ 3 * (1 + X)) =
        A - A * X ^ 1 - A * X ^ 1 + A * X ^ 3 + A * X ^ 3 - A * X ^ 4 := by ring
    rw [e1]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_X_pow, A, coeff_mk]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [hq] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, if_false]
      rw [hq n, hq (n - 1), hq (n - 3), hq (n - 4)]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega,
        show m + 4 - 4 = m by omega]
      push_cast
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)]; ring
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; ring
  have hN : (2 * X * (3 + X + 2 * X ^ 2) : ℚ⟦X⟧) =
      X ^ 1 + X ^ 1 + X ^ 1 + X ^ 1 + X ^ 1 + X ^ 1 + X ^ 2 + X ^ 2 + X ^ 3 + X ^ 3 + X ^ 3
        + X ^ 3 := by ring
  rw [hN, ← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

end OMA.S_oeis_a199705

theorem OMA.solution : type_of% @OMA.S_oeis_a199705.main :=
  ⟨OMA.S_oeis_a199705.gf, fun n _ he => OMA.S_oeis_a199705.even_formula n he,
    fun n _ ho => OMA.S_oeis_a199705.odd_formula n ho⟩
