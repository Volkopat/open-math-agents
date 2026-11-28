import OMAStatements.S_oeis_a154150

namespace OMA.S_oeis_a154150

open PowerSeries



/-- The positive solutions of X^2 + 191 = 8Y^2 in increasing order: two chains of
(X, Y) -> (3X + 8Y, X + 3Y), started at (3, 5) and (31, 12) and interleaved. -/
def XY : ℕ → ℕ × ℕ
  | 0 => (3, 5)
  | 1 => (31, 12)
  | j + 2 => (3 * (XY j).1 + 8 * (XY j).2, (XY j).1 + 3 * (XY j).2)

theorem XY_add_two (j : ℕ) :
    XY (j + 2) = (3 * (XY j).1 + 8 * (XY j).2, (XY j).1 + 3 * (XY j).2) := by
  rw [XY]

theorem pell (j : ℕ) : (XY j).1 ^ 2 + 191 = 8 * (XY j).2 ^ 2 := by
  have key : ∀ j, (XY j).1 ^ 2 + 191 = 8 * (XY j).2 ^ 2 ∧
      (XY (j + 1)).1 ^ 2 + 191 = 8 * (XY (j + 1)).2 ^ 2 := by
    intro j
    induction j with
    | zero => exact ⟨rfl, rfl⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [XY_add_two]
      nlinarith [ih.1]
  exact (key j).1

theorem odd_X (j : ℕ) : (XY j).1 % 2 = 1 := by
  have key : ∀ j, (XY j).1 % 2 = 1 ∧ (XY (j + 1)).1 % 2 = 1 := by
    intro j
    induction j with
    | zero => exact ⟨rfl, rfl⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [XY_add_two]
      simp only
      omega
  exact (key j).1

theorem mono (j : ℕ) : (XY j).1 < (XY (j + 1)).1 ∧ (XY j).2 < (XY (j + 1)).2 := by
  have key : ∀ j, ((XY j).1 < (XY (j + 1)).1 ∧ (XY j).2 < (XY (j + 1)).2) ∧
      ((XY (j + 1)).1 < (XY (j + 2)).1 ∧ (XY (j + 1)).2 < (XY (j + 2)).2) := by
    intro j
    induction j with
    | zero => exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [XY_add_two (j + 1), XY_add_two j]
      simp only
      constructor <;> omega
  exact (key j).1

/-- Every solution in natural numbers is in the list. -/
theorem complete (Y : ℕ) : ∀ X : ℕ, X ^ 2 + 191 = 8 * Y ^ 2 → ∃ j, XY j = (X, Y) := by
  induction Y using Nat.strong_induction_on with
  | _ Y ih =>
    intro X h
    rcases Nat.lt_or_ge Y 15 with hY | hY
    · have hX : X < 40 := by nlinarith
      interval_cases Y <;> interval_cases X <;>
        first
        | exact ⟨0, rfl⟩
        | exact ⟨1, rfl⟩
        | (exfalso; revert h; decide)
    · have h1 : 8 * Y < 3 * X := by
        by_contra hc
        push_neg at hc
        nlinarith [Nat.mul_le_mul hc hc]
      have h2 : 2 * Y < X := by nlinarith
      have h3 : X < 3 * Y := by nlinarith
      have hp : (3 * X - 8 * Y) ^ 2 + 191 = 8 * (3 * Y - X) ^ 2 := by
        zify [h1.le, h3.le]
        push_cast
        nlinarith [h]
      obtain ⟨j, hj⟩ := ih (3 * Y - X) (by omega) (3 * X - 8 * Y) hp
      refine ⟨j + 2, ?_⟩
      rw [XY_add_two, hj]
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
    have hp : (2 * k + 1) ^ 2 + 191 = 8 * m ^ 2 := by
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

/-- X_{j+4} = 6 X_{j+2} - X_j. -/
theorem X_rec (j : ℕ) : ((XY (j + 4)).1 : ℤ) = 6 * (XY (j + 2)).1 - (XY j).1 := by
  rw [show j + 4 = (j + 2) + 2 by ring, XY_add_two (j + 2), XY_add_two j]
  simp only
  push_cast
  ring

theorem f_rec (j : ℕ) : (f (j + 4) : ℤ) = 6 * f (j + 2) - f j + 2 := by
  have h := X_rec j
  have o0 := odd_X j
  have o2 := odd_X (j + 2)
  have o4 := odd_X (j + 4)
  unfold f
  omega

/-- The conjectured recurrence (for n > 5, where all terms are defined). -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega),
    a_eq _ (by omega), a_eq _ (by omega)]
  simp only [show m + 6 - 1 = m + 5 by omega, show m + 5 - 1 = m + 4 by omega,
    show m + 6 - 2 - 1 = m + 3 by omega, show m + 6 - 3 - 1 = m + 2 by omega,
    show m + 6 - 4 - 1 = m + 1 by omega, show m + 6 - 5 - 1 = m by omega]
  have r1 := f_rec (m + 1)
  have r0 := f_rec m
  rw [show m + 1 + 4 = m + 5 by ring, show m + 1 + 2 = m + 3 by ring] at r1
  linarith

/-- Controls: the entry's terms a(1..10). -/
theorem controls : a 1 = 1 ∧ a 2 = 15 ∧ a 3 = 24 ∧ a 4 = 94 ∧ a 5 = 145 ∧ a 6 = 551 ∧
    a 7 = 848 ∧ a 8 = 3214 ∧ a 9 = 4945 ∧ a 10 = 18735 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_eq _ (by norm_num)] <;> rfl

/-- The g.f. with the denominator (1 - x)(x^2 - 2x - 1)(x^2 + 2x - 1) cleared. -/
theorem gfD : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
      X + 14 * X ^ 2 + 3 * X ^ 3 - 14 * X ^ 4 - 2 * X ^ 5 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have c2 : (C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat C 2
  have c3 : (C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat C 3
  have c6 : (C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat C 6
  have c14 : (C (14 : ℚ) : PowerSeries ℚ) = 14 := map_ofNat C 14
  have hD : A * ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
      A - A * X ^ 1 - C 6 * (A * X ^ 2) + C 6 * (A * X ^ 3) + A * X ^ 4 - A * X ^ 5 := by
    rw [c6]; ring
  have hN : (X + 14 * X ^ 2 + 3 * X ^ 3 - 14 * X ^ 4 - 2 * X ^ 5 : PowerSeries ℚ) =
      X ^ 1 + X ^ 2 * C 14 + X ^ 3 * C 3 - X ^ 4 * C 14 - X ^ 5 * C 2 := by
    rw [c2, c3, c14]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_X_pow]
  obtain ⟨v1, v2, v3, v4, v5, -⟩ := controls
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> simp [v1, v2, v3, v4, v5] <;> norm_num
  · have r := recurrence n (by omega)
    have rq : (a n : ℚ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5) := by
      exact_mod_cast r
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show n ≠ 0 by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      if_false]
    linear_combination rq

/-- The first conjectured g.f., with its denominator as written cleared. -/
theorem gf1 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
      X * (-1 - 14 * X - 3 * X ^ 2 + 14 * X ^ 3 + 2 * X ^ 4) := by
  rw [show ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) : PowerSeries ℚ) =
      -((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) by ring, mul_neg, gfD]
  ring

/-- The second conjectured g.f., the partial fraction form. -/
theorem gf2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
    C (1 / 2 : ℚ) * (4 + (X - 1)⁻¹ + (10 + 27 * X) * (X ^ 2 - 2 * X - 1)⁻¹ +
      (-7 + 4 * X) * (X ^ 2 + 2 * X - 1)⁻¹) := by
  set D : PowerSeries ℚ := (1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp [hD] at this
  have i1 : (X - 1 : PowerSeries ℚ)⁻¹ * (X - 1) = 1 := PowerSeries.inv_mul_cancel _ (by simp)
  have i2 : (X ^ 2 + 2 * X - 1 : PowerSeries ℚ)⁻¹ * (X ^ 2 + 2 * X - 1) = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp)
  have i3 : (X ^ 2 - 2 * X - 1 : PowerSeries ℚ)⁻¹ * (X ^ 2 - 2 * X - 1) = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp)
  have half : (C (1 / 2 : ℚ) : PowerSeries ℚ) * 2 = 1 := by
    rw [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  apply mul_right_cancel₀ hD0
  rw [gfD]
  calc X + 14 * X ^ 2 + 3 * X ^ 3 - 14 * X ^ 4 - 2 * X ^ 5
      = (C (1 / 2 : ℚ) * 2) * (X + 14 * X ^ 2 + 3 * X ^ 3 - 14 * X ^ 4 - 2 * X ^ 5) := by
        rw [half, one_mul]
    _ = C (1 / 2 : ℚ) * (4 * D + ((X - 1)⁻¹ * (X - 1)) * (-(X ^ 2 - 2 * X - 1) *
          (X ^ 2 + 2 * X - 1)) + (10 + 27 * X) * ((X ^ 2 - 2 * X - 1)⁻¹ * (X ^ 2 - 2 * X - 1)) *
          ((1 - X) * (X ^ 2 + 2 * X - 1)) + (-7 + 4 * X) *
          ((X ^ 2 + 2 * X - 1)⁻¹ * (X ^ 2 + 2 * X - 1)) * ((1 - X) * (X ^ 2 - 2 * X - 1))) := by
        rw [i1, i2, i3, hD]; ring
    _ = C (1 / 2 : ℚ) * (4 + (X - 1)⁻¹ + (10 + 27 * X) * (X ^ 2 - 2 * X - 1)⁻¹ +
          (-7 + 4 * X) * (X ^ 2 + 2 * X - 1)⁻¹) * D := by
        rw [hD]; ring

/-- The three conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (-1 - 14 * X - 3 * X ^ 2 + 14 * X ^ 3 + 2 * X ^ 4) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (4 + (X - 1)⁻¹ + (10 + 27 * X) * (X ^ 2 - 2 * X - 1)⁻¹ +
        (-7 + 4 * X) * (X ^ 2 + 2 * X - 1)⁻¹) :=
  ⟨recurrence, gf1, gf2⟩

end OMA.S_oeis_a154150

theorem OMA.solution : type_of% @OMA.S_oeis_a154150.main :=
  OMA.S_oeis_a154150.conjecture
