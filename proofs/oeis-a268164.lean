import OMAStatements.S_oeis_a268164

namespace OMA.S_oeis_a268164

open PowerSeries





/-- Number of columns of length m that pass the scan from the state (r, p). -/
def N (r : Option (Fin 4)) (p : Fin 4) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 4, if ok r p (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 4) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 4, f (List.ofFn x) =
      ∑ c : Fin 4, ∑ y : Fin m → Fin 4, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 4).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (r : Option (Fin 4)) (p : Fin 4) : N r p 0 = 1 := by
  simp [N, ok]

theorem N_succ (r : Option (Fin 4)) (p : Fin 4) (m : ℕ) :
    N r p (m + 1) = ∑ c : Fin 4, if c = p then
      (if (r.all fun v => decide (c = v + 1)) = true then N (some c) c m else 0) else N r c m := by
  have h := sum_cons m (fun l => if ok r p l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c = p
  · subst hc
    by_cases hr : (r.all fun v => decide (c = v + 1)) = true
    · simp [ok, hr]
    · simp [ok, hr]
  · simp [ok, hc]

/-- The counts by state: (from no repeat yet, and from a repeat r with p - r = 0, 1, or 2 or 3). -/
def st : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 1, 1)
  | m + 1 => (3 * (st m).1 + (st m).2.1, (st m).2.2.1 + 2 * (st m).2.2.2,
      2 * (st m).2.1 + 2 * (st m).2.2.2, (st m).2.1 + (st m).2.2.1 + (st m).2.2.2)

def Bv (m : ℕ) (v p : Fin 4) : ℕ :=
  if p = v then (st m).2.1 else if p = v + 1 then (st m).2.2.1 else (st m).2.2.2

theorem N_eq (m : ℕ) :
    (∀ p, N none p m = (st m).1) ∧ (∀ v p, N (some v) p m = Bv m v p) := by
  induction m with
  | zero =>
    refine ⟨fun p => ?_, fun v p => ?_⟩
    · rw [N_zero]; rfl
    · rw [N_zero]; simp [Bv, st]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun p => ?_, fun v p => ?_⟩
    · rw [N_succ]
      simp only [Option.all_none, if_true, h1, h2]
      fin_cases p <;> simp [Fin.sum_univ_four, Bv, st] <;> omega
    · rw [N_succ]
      simp only [Option.all_some, h2]
      fin_cases v <;> fin_cases p <;> simp [Fin.sum_univ_four, Bv, st] <;> omega

theorem a_succ (n : ℕ) : a (n + 1) = (st n).1 := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_four]
  simp only [valid]
  simp
  rw [← (N_eq n).1 0, N, Finset.card_filter]

theorem A_rec (m : ℕ) :
    ((st (m + 3)).1 : ℤ) = 5 * (st (m + 2)).1 - 2 * (st (m + 1)).1 - 12 * (st m).1 := by
  simp only [st]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = 5 * a (n - 1) - 2 * a (n - 2) - 12 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : a (m + 4) = (st (m + 3)).1 := a_succ (m + 3)
  have e2 : a (m + 4 - 1) = (st (m + 2)).1 := by
    rw [show m + 4 - 1 = m + 2 + 1 by omega]; exact a_succ _
  have e3 : a (m + 4 - 2) = (st (m + 1)).1 := by
    rw [show m + 4 - 2 = m + 1 + 1 by omega]; exact a_succ _
  have e4 : a (m + 4 - 3) = (st m).1 := by
    rw [show m + 4 - 3 = m + 1 by omega]; exact a_succ _
  rw [e1, e2, e3, e4]
  exact A_rec m

theorem a_one : a 1 = 1 := by rw [a_succ]; rfl
theorem a_two : a 2 = 4 := by rw [a_succ]; rfl
theorem a_three : a 3 = 15 := by rw [a_succ]; rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x(1 - x - 3x^2)/((1 - 3x)(1 - 2x - 4x^2)), in Q[[x]]. -/
theorem gf_eq : gf = X * (1 - X - 3 * X ^ 2) * ((1 - 3 * X) * (1 - 2 * X - 4 * X ^ 2))⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - 3 * X) * (1 - 2 * X - 4 * X ^ 2) with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  have key : gf * D = X * (1 - X - 3 * X ^ 2) := by
    have e : gf * D = gf - C 5 * (gf * X ^ 1) + C 2 * (gf * X ^ 2) + C 12 * (gf * X ^ 3) := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) * (1 - X - 3 * X ^ 2) = X ^ 1 - X ^ 2 - C 3 * X ^ 3 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    have h1 : (a 1 : ℚ) = 1 := by exact_mod_cast a_one
    have h2 : (a 2 : ℚ) = 4 := by exact_mod_cast a_two
    have h3 : (a 3 : ℚ) = 15 := by exact_mod_cast a_three
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [h1, h2, h3] <;> norm_num
    · have hr := recurrence n hn
      have hq : (a n : ℚ) = 5 * a (n - 1) - 2 * a (n - 2) - 12 * a (n - 3) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
        show n ≠ 0 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
        show n - 3 ≠ 0 by omega, if_false, show n ≠ 1 by omega, show n ≠ 2 by omega, coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- (1 + sqrt 5)^m = U(m) + V(m) sqrt 5 and (1 - sqrt 5)^m = U(m) - V(m) sqrt 5. -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | m + 1 => ((uv m).1 + 5 * (uv m).2, (uv m).1 + (uv m).2)

theorem s5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)

theorem pow_plus (m : ℕ) :
    (1 + Real.sqrt 5) ^ m = (uv m).1 + (uv m).2 * Real.sqrt 5 := by
  induction m with
  | zero => simp [uv]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [uv]
    push_cast
    linear_combination ((uv m).2 : ℝ) * s5

theorem pow_minus (m : ℕ) :
    (1 - Real.sqrt 5) ^ m = (uv m).1 - (uv m).2 * Real.sqrt 5 := by
  induction m with
  | zero => simp [uv]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [uv]
    push_cast
    linear_combination ((uv m).2 : ℝ) * s5

/-- 4 a(m + 1) = -4 * 3^(m + 1) + 5 U(m + 1) + 11 V(m + 1). -/
def G (m : ℕ) : ℤ := -4 * 3 ^ (m + 1) + 5 * (uv (m + 1)).1 + 11 * (uv (m + 1)).2

theorem G_rec (m : ℕ) : G (m + 3) = 5 * G (m + 2) - 2 * G (m + 1) - 12 * G m := by
  simp only [G, uv]
  ring

theorem closed_int (m : ℕ) :
    4 * ((st m).1 : ℤ) = G m ∧ 4 * ((st (m + 1)).1 : ℤ) = G (m + 1) ∧
      4 * ((st (m + 2)).1 : ℤ) = G (m + 2) := by
  induction m with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> decide
  | succ m ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    show 4 * ((st (m + 3)).1 : ℤ) = G (m + 3)
    rw [A_rec m]
    linear_combination 5 * h2 - 2 * h1 - 12 * h0 - G_rec m

theorem closed_form (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) = -3 ^ n + (5 / 8 - 11 / (8 * Real.sqrt 5)) * (1 - Real.sqrt 5) ^ n +
      1 / 40 * (1 + Real.sqrt 5) ^ n * (25 + 11 * Real.sqrt 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hA := (closed_int m).1
  rw [← a_succ] at hA
  unfold G at hA
  have hA' : 4 * (a (m + 1) : ℝ) =
      -4 * 3 ^ (m + 1) + 5 * ((uv (m + 1)).1 : ℝ) + 11 * ((uv (m + 1)).2 : ℝ) := by
    exact_mod_cast hA
  have hpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hinv : 11 / (8 * Real.sqrt 5) = 11 * Real.sqrt 5 / 40 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    linear_combination (-88 : ℝ) * s5
  rw [hinv, pow_plus, pow_minus]
  linear_combination (1 / 4 : ℝ) * hA' - (11 / 20 : ℝ) * ((uv (m + 1)).2 : ℝ) * s5

/-- Both of Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    gf = X * (1 - X - 3 * X ^ 2) * ((1 - 3 * X) * (1 - 2 * X - 4 * X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = -3 ^ n + (5 / 8 - 11 / (8 * Real.sqrt 5)) * (1 - Real.sqrt 5) ^ n +
      1 / 40 * (1 + Real.sqrt 5) ^ n * (25 + 11 * Real.sqrt 5) :=
  ⟨gf_eq, closed_form⟩

/-- Controls: a(1..5) = 1, 4, 15, 55, 197, the entry's data (a(1..3) also by direct count). -/
example : a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 15 ∧ a 4 = 55 ∧ a 5 = 197 := by
  refine ⟨a_one, a_two, a_three, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

example : a 3 = 15 := by decide

end OMA.S_oeis_a268164

theorem OMA.solution : type_of% @OMA.S_oeis_a268164.main :=
  OMA.S_oeis_a268164.conjecture
