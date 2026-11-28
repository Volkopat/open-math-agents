import OMAStatements.S_oeis_a154145

namespace OMA.S_oeis_a154145

open PowerSeries



/-- The positive solutions of X^2 + 119 = 8Y^2 in increasing order: four chains of
(X, Y) -> (3X + 8Y, X + 3Y), started at (3, 4), (9, 5), (13, 6), (23, 9) and interleaved. -/
def XY : ℕ → ℕ × ℕ
  | 0 => (3, 4)
  | 1 => (9, 5)
  | 2 => (13, 6)
  | 3 => (23, 9)
  | j + 4 => (3 * (XY j).1 + 8 * (XY j).2, (XY j).1 + 3 * (XY j).2)

theorem XY_add_four (j : ℕ) :
    XY (j + 4) = (3 * (XY j).1 + 8 * (XY j).2, (XY j).1 + 3 * (XY j).2) := by
  rw [XY]

theorem pell (j : ℕ) : (XY j).1 ^ 2 + 119 = 8 * (XY j).2 ^ 2 := by
  have key : ∀ j, (XY j).1 ^ 2 + 119 = 8 * (XY j).2 ^ 2 ∧
      (XY (j + 1)).1 ^ 2 + 119 = 8 * (XY (j + 1)).2 ^ 2 ∧
      (XY (j + 2)).1 ^ 2 + 119 = 8 * (XY (j + 2)).2 ^ 2 ∧
      (XY (j + 3)).1 ^ 2 + 119 = 8 * (XY (j + 3)).2 ^ 2 := by
    intro j
    induction j with
    | zero => exact ⟨rfl, rfl, rfl, rfl⟩
    | succ j ih =>
      refine ⟨ih.2.1, ih.2.2.1, ih.2.2.2, ?_⟩
      rw [show j + 1 + 3 = j + 4 by ring, XY_add_four]
      nlinarith [ih.1]
  exact (key j).1

theorem odd_X (j : ℕ) : (XY j).1 % 2 = 1 := by
  have key : ∀ j, (XY j).1 % 2 = 1 ∧ (XY (j + 1)).1 % 2 = 1 ∧ (XY (j + 2)).1 % 2 = 1 ∧
      (XY (j + 3)).1 % 2 = 1 := by
    intro j
    induction j with
    | zero => exact ⟨rfl, rfl, rfl, rfl⟩
    | succ j ih =>
      refine ⟨ih.2.1, ih.2.2.1, ih.2.2.2, ?_⟩
      rw [show j + 1 + 3 = j + 4 by ring, XY_add_four]
      simp only
      omega
  exact (key j).1

theorem mono (j : ℕ) : (XY j).1 < (XY (j + 1)).1 ∧ (XY j).2 < (XY (j + 1)).2 := by
  have key : ∀ j, ((XY j).1 < (XY (j + 1)).1 ∧ (XY j).2 < (XY (j + 1)).2) ∧
      ((XY (j + 1)).1 < (XY (j + 2)).1 ∧ (XY (j + 1)).2 < (XY (j + 2)).2) ∧
      ((XY (j + 2)).1 < (XY (j + 3)).1 ∧ (XY (j + 2)).2 < (XY (j + 3)).2) ∧
      ((XY (j + 3)).1 < (XY (j + 4)).1 ∧ (XY (j + 3)).2 < (XY (j + 4)).2) := by
    intro j
    induction j with
    | zero =>
      exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
    | succ j ih =>
      refine ⟨ih.2.1, ih.2.2.1, ih.2.2.2, ?_⟩
      rw [show j + 1 + 3 = j + 4 by ring, show j + 1 + 4 = (j + 1) + 4 by ring,
        XY_add_four (j + 1), XY_add_four j]
      simp only
      constructor <;> omega
  exact (key j).1

/-- Every solution in natural numbers is in the list. -/
theorem complete (Y : ℕ) : ∀ X : ℕ, X ^ 2 + 119 = 8 * Y ^ 2 → ∃ j, XY j = (X, Y) := by
  induction Y using Nat.strong_induction_on with
  | _ Y ih =>
    intro X h
    rcases Nat.lt_or_ge Y 12 with hY | hY
    · have hX : X < 30 := by nlinarith
      interval_cases Y <;> interval_cases X <;>
        first
        | exact ⟨0, rfl⟩
        | exact ⟨1, rfl⟩
        | exact ⟨2, rfl⟩
        | exact ⟨3, rfl⟩
        | (exfalso; revert h; decide)
    · have h1 : 8 * Y < 3 * X := by
        by_contra hc
        push_neg at hc
        nlinarith [Nat.mul_le_mul hc hc]
      have h2 : 2 * Y < X := by nlinarith
      have h3 : X < 3 * Y := by nlinarith
      have hp : (3 * X - 8 * Y) ^ 2 + 119 = 8 * (3 * Y - X) ^ 2 := by
        zify [h1.le, h3.le]
        push_cast
        nlinarith [h]
      obtain ⟨j, hj⟩ := ih (3 * Y - X) (by omega) (3 * X - 8 * Y) hp
      refine ⟨j + 4, ?_⟩
      rw [XY_add_four, hj]
      simp only [Prod.mk.injEq]
      omega

/-- The j-th term, j >= 0: k_j = X_j / 2 (X_j = 2 k_j + 1). -/
def f (j : ℕ) : ℕ := (XY j).1 / 2

theorem P_f (j : ℕ) : P (f j) := by
  refine ⟨(XY j).2, ?_⟩
  have hp := pell j
  have ho := odd_X j
  unfold f
  set X := (XY j).1
  set Y := (XY j).2
  obtain ⟨k, hk⟩ : ∃ k, X = 2 * k + 1 := ⟨X / 2, by omega⟩
  rw [hk, show (2 * k + 1) / 2 = k by omega]
  rw [hk] at hp
  have he : k * (k + 1) = 2 * (k * (k + 1) / 2) :=
    (Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd).symm
  have e2 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [e2] at hp
  generalize k * (k + 1) / 2 = T at he hp ⊢
  generalize k * (k + 1) = U at he hp
  generalize Y ^ 2 = M at hp ⊢
  omega

theorem P_iff (k : ℕ) : P k ↔ ∃ j, f j = k := by
  constructor
  · rintro ⟨m, hm⟩
    have he : k * (k + 1) = 2 * (k * (k + 1) / 2) :=
      (Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd).symm
    have hp : (2 * k + 1) ^ 2 + 119 = 8 * m ^ 2 := by
      have e2 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      rw [e2]
      generalize k * (k + 1) / 2 = T at he hm
      generalize k * (k + 1) = U at he
      generalize m ^ 2 = M at hm ⊢
      omega
    obtain ⟨j, hj⟩ := complete m (2 * k + 1) hp
    refine ⟨j, ?_⟩
    unfold f
    rw [hj]
    omega
  · rintro ⟨j, rfl⟩
    exact P_f j

theorem f_strictMono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h1 := (mono j).1
  have o1 := odd_X j
  have o2 := odd_X (j + 1)
  unfold f
  omega

theorem P_infinite : (Set.ofPred P).Infinite :=
  Set.infinite_of_injective_forall_mem f_strictMono.injective (fun j => P_f j)

theorem nth_eq (j : ℕ) : Nat.nth P j = f j := by
  have hS : ∀ n : ℕ, n ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred P), n < hf.toFinset.card } :=
    fun n hf => absurd hf P_infinite
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hS j)).symm
  · intro k hk
    obtain ⟨i, hi⟩ := (P_iff k).1 hk
    exact ⟨i, hS i, hi⟩
  · intro i _
    exact P_f i
  · intro i _ j _ hij
    exact f_strictMono hij

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = f (n - 1) := by
  rw [a, nth_eq]

/-- X_(j+8) = 6 X_(j+4) - X_j. -/
theorem X_rec (j : ℕ) : ((XY (j + 8)).1 : ℤ) = 6 * (XY (j + 4)).1 - (XY j).1 := by
  rw [show j + 8 = (j + 4) + 4 by ring, XY_add_four (j + 4), XY_add_four j]
  simp only
  push_cast
  ring

theorem f_rec (j : ℕ) : (f (j + 8) : ℤ) = 6 * f (j + 4) - f j + 2 := by
  have h := X_rec j
  have o0 := odd_X j
  have o4 := odd_X (j + 4)
  have o8 := odd_X (j + 8)
  unfold f
  omega

/-- The conjectured recurrence (for n > 9, where all terms are defined). -/
theorem recurrence (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = a (n - 1) + 6 * a (n - 4) - 6 * a (n - 5) - a (n - 8) + a (n - 9) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega),
    a_eq _ (by omega), a_eq _ (by omega)]
  simp only [show m + 10 - 1 = m + 9 by omega, show m + 9 - 1 = m + 8 by omega,
    show m + 10 - 4 - 1 = m + 5 by omega, show m + 10 - 5 - 1 = m + 4 by omega,
    show m + 10 - 8 - 1 = m + 1 by omega, show m + 10 - 9 - 1 = m by omega]
  have r1 := f_rec (m + 1)
  have r0 := f_rec m
  rw [show m + 1 + 8 = m + 9 by ring, show m + 1 + 4 = m + 5 by ring] at r1
  linarith

/-- Controls: the entry's terms a(1..12). -/
theorem controls : a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 6 ∧ a 4 = 11 ∧ a 5 = 20 ∧ a 6 = 33 ∧ a 7 = 43 ∧
    a 8 = 70 ∧ a 9 = 121 ∧ a 10 = 196 ∧ a 11 = 254 ∧ a 12 = 411 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_eq _ (by norm_num)] <;> rfl

/-- The g.f. with the denominator (1 - x)(x^4 - 2x^2 - 1)(x^4 + 2x^2 - 1) cleared. -/
theorem gfD : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (X ^ 4 - 2 * X ^ 2 - 1) * (X ^ 4 + 2 * X ^ 2 - 1)) =
      X + 3 * X ^ 2 + 2 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6 - 2 * X ^ 7 - 3 * X ^ 8 -
        2 * X ^ 9 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have c2 : (C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat C 2
  have c3 : (C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat C 3
  have c5 : (C (5 : ℚ) : PowerSeries ℚ) = 5 := map_ofNat C 5
  have c6 : (C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat C 6
  have hD : A * ((1 - X) * (X ^ 4 - 2 * X ^ 2 - 1) * (X ^ 4 + 2 * X ^ 2 - 1)) =
      A - A * X ^ 1 - C 6 * (A * X ^ 4) + C 6 * (A * X ^ 5) + A * X ^ 8 - A * X ^ 9 := by
    rw [c6]; ring
  have hN : (X + 3 * X ^ 2 + 2 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6 - 2 * X ^ 7 -
      3 * X ^ 8 - 2 * X ^ 9 : PowerSeries ℚ) = X ^ 1 + X ^ 2 * C 3 + X ^ 3 * C 2 + X ^ 4 * C 5 +
      X ^ 5 * C 3 - X ^ 6 * C 5 - X ^ 7 * C 2 - X ^ 8 * C 3 - X ^ 9 * C 2 := by
    rw [c2, c3, c5]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_X_pow]
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, -⟩ := controls
  rcases Nat.lt_or_ge n 10 with h | h
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
  · have r := recurrence n (by omega)
    have rq : (a n : ℚ) = a (n - 1) + 6 * a (n - 4) - 6 * a (n - 5) - a (n - 8) + a (n - 9) := by
      exact_mod_cast r
    simp only [show 1 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
      show 8 ≤ n by omega, show 9 ≤ n by omega, if_true, show n ≠ 0 by omega,
      show n - 1 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
      show n - 8 ≠ 0 by omega, show n - 9 ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega,
      if_false]
    linear_combination rq

/-- The first conjectured g.f., with its denominator as written cleared. -/
theorem gf1 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((X - 1) * (X ^ 4 + 2 * X ^ 2 - 1) * (X ^ 4 - 2 * X ^ 2 - 1)) =
      X * (-1 - 3 * X - 2 * X ^ 2 - 5 * X ^ 3 - 3 * X ^ 4 + 5 * X ^ 5 + 2 * X ^ 6 + 3 * X ^ 7 +
        2 * X ^ 8) := by
  rw [show ((X - 1) * (X ^ 4 + 2 * X ^ 2 - 1) * (X ^ 4 - 2 * X ^ 2 - 1) : PowerSeries ℚ) =
      -((1 - X) * (X ^ 4 - 2 * X ^ 2 - 1) * (X ^ 4 + 2 * X ^ 2 - 1)) by ring, mul_neg, gfD]
  ring

/-- The second conjectured g.f., the partial fraction form. -/
theorem gf2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
    C (1 / 2 : ℚ) * (4 + (7 + 4 * X + 16 * X ^ 2 + 11 * X ^ 3) * (X ^ 4 - 2 * X ^ 2 - 1)⁻¹ +
      (X - 1)⁻¹ + (-4 - 7 * X - 3 * X ^ 2 - 2 * X ^ 3) * (X ^ 4 + 2 * X ^ 2 - 1)⁻¹) := by
  set D : PowerSeries ℚ := (1 - X) * (X ^ 4 - 2 * X ^ 2 - 1) * (X ^ 4 + 2 * X ^ 2 - 1) with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp [hD] at this
  have i1 : (X - 1 : PowerSeries ℚ)⁻¹ * (X - 1) = 1 := PowerSeries.inv_mul_cancel _ (by simp)
  have i2 : (X ^ 4 + 2 * X ^ 2 - 1 : PowerSeries ℚ)⁻¹ * (X ^ 4 + 2 * X ^ 2 - 1) = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp)
  have i3 : (X ^ 4 - 2 * X ^ 2 - 1 : PowerSeries ℚ)⁻¹ * (X ^ 4 - 2 * X ^ 2 - 1) = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp)
  have half : (C (1 / 2 : ℚ) : PowerSeries ℚ) * 2 = 1 := by
    rw [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  apply mul_right_cancel₀ hD0
  rw [gfD]
  calc X + 3 * X ^ 2 + 2 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6 - 2 * X ^ 7 - 3 * X ^ 8 -
        2 * X ^ 9
      = (C (1 / 2 : ℚ) * 2) * (X + 3 * X ^ 2 + 2 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 - 5 * X ^ 6 -
          2 * X ^ 7 - 3 * X ^ 8 - 2 * X ^ 9) := by
        rw [half, one_mul]
    _ = C (1 / 2 : ℚ) * (4 * D + (7 + 4 * X + 16 * X ^ 2 + 11 * X ^ 3) *
          ((X ^ 4 - 2 * X ^ 2 - 1)⁻¹ * (X ^ 4 - 2 * X ^ 2 - 1)) * ((1 - X) * (X ^ 4 + 2 * X ^ 2 - 1)) +
          ((X - 1)⁻¹ * (X - 1)) * (-(X ^ 4 - 2 * X ^ 2 - 1) * (X ^ 4 + 2 * X ^ 2 - 1)) +
          (-4 - 7 * X - 3 * X ^ 2 - 2 * X ^ 3) * ((X ^ 4 + 2 * X ^ 2 - 1)⁻¹ *
            (X ^ 4 + 2 * X ^ 2 - 1)) * ((1 - X) * (X ^ 4 - 2 * X ^ 2 - 1))) := by
        rw [i1, i2, i3, hD]; ring
    _ = C (1 / 2 : ℚ) * (4 + (7 + 4 * X + 16 * X ^ 2 + 11 * X ^ 3) * (X ^ 4 - 2 * X ^ 2 - 1)⁻¹ +
          (X - 1)⁻¹ + (-4 - 7 * X - 3 * X ^ 2 - 2 * X ^ 3) * (X ^ 4 + 2 * X ^ 2 - 1)⁻¹) * D := by
        rw [hD]; ring

/-- The three conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 9 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 4) - 6 * a (n - 5) - a (n - 8) + a (n - 9)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) * (X ^ 4 + 2 * X ^ 2 - 1) * (X ^ 4 - 2 * X ^ 2 - 1)) =
        X * (-1 - 3 * X - 2 * X ^ 2 - 5 * X ^ 3 - 3 * X ^ 4 + 5 * X ^ 5 + 2 * X ^ 6 +
          3 * X ^ 7 + 2 * X ^ 8) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (4 + (7 + 4 * X + 16 * X ^ 2 + 11 * X ^ 3) * (X ^ 4 - 2 * X ^ 2 - 1)⁻¹ +
        (X - 1)⁻¹ + (-4 - 7 * X - 3 * X ^ 2 - 2 * X ^ 3) * (X ^ 4 + 2 * X ^ 2 - 1)⁻¹) :=
  ⟨recurrence, gf1, gf2⟩

end OMA.S_oeis_a154145

theorem OMA.solution : type_of% @OMA.S_oeis_a154145.main :=
  OMA.S_oeis_a154145.conjecture
