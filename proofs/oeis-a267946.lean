import OMAStatements.S_oeis_a267946

namespace OMA.S_oeis_a267946

open PowerSeries





/-- Number of columns of length m that pass the scan from the state (r, p). -/
def N (r : Option (Fin 3)) (p : Fin 3) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 3, if ok r p (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 3) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 3, f (List.ofFn x) =
      ∑ c : Fin 3, ∑ y : Fin m → Fin 3, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (r : Option (Fin 3)) (p : Fin 3) : N r p 0 = 1 := by
  simp [N, ok]

theorem N_succ (r : Option (Fin 3)) (p : Fin 3) (m : ℕ) :
    N r p (m + 1) = ∑ c : Fin 3, if c = p then
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

/-- The counts by state: from no repeat yet, and from a repeat r with p - r = 0, 1 or 2. -/
def st : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 1, 1)
  | m + 1 => (2 * (st m).1 + (st m).2.1, (st m).2.2.1 + (st m).2.2.2,
      2 * (st m).2.1 + (st m).2.2.2, (st m).2.1 + (st m).2.2.1)

def Bv (m : ℕ) (v p : Fin 3) : ℕ :=
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
      fin_cases p <;> simp [Fin.sum_univ_three, Bv, st] <;> omega
    · rw [N_succ]
      simp only [Option.all_some, h2]
      fin_cases v <;> fin_cases p <;> simp [Fin.sum_univ_three, Bv, st] <;> omega

theorem a_succ (n : ℕ) : a (n + 1) = (st n).1 := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_three]
  simp only [valid]
  simp
  rw [← (N_eq n).1 0, N, Finset.card_filter]

theorem A_rec (m : ℕ) :
    ((st (m + 3)).1 : ℤ) = 3 * (st (m + 2)).1 + (st (m + 1)).1 - 6 * (st m).1 := by
  simp only [st]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = 3 * a (n - 1) + a (n - 2) - 6 * a (n - 3) := by
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
theorem a_two : a 2 = 3 := by rw [a_succ]; rfl
theorem a_three : a 3 = 8 := by rw [a_succ]; rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x(1 - 2x^2)/((1 - 2x)(1 - x - 3x^2)), in Q[[x]]. -/
theorem gf_eq : gf = X * (1 - 2 * X ^ 2) * ((1 - 2 * X) * (1 - X - 3 * X ^ 2))⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - 2 * X) * (1 - X - 3 * X ^ 2) with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  have key : gf * D = X * (1 - 2 * X ^ 2) := by
    have e : gf * D = gf - C 3 * (gf * X ^ 1) - (gf * X ^ 2) + C 6 * (gf * X ^ 3) := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) * (1 - 2 * X ^ 2) = X ^ 1 - C 2 * X ^ 3 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    have h1 : (a 1 : ℚ) = 1 := by exact_mod_cast a_one
    have h2 : (a 2 : ℚ) = 3 := by exact_mod_cast a_two
    have h3 : (a 3 : ℚ) = 8 := by exact_mod_cast a_three
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [h1, h2, h3] <;> norm_num
    · have hr := recurrence n hn
      have hq : (a n : ℚ) = 3 * a (n - 1) + a (n - 2) - 6 * a (n - 3) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
        show n ≠ 0 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
        show n - 3 ≠ 0 by omega, if_false, show n ≠ 1 by omega, show n ≠ 3 by omega, coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- (1 + sqrt 13)^m = P(m) + Q(m) sqrt 13 and (1 - sqrt 13)^m = P(m) - Q(m) sqrt 13. -/
def pq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | m + 1 => ((pq m).1 + 13 * (pq m).2, (pq m).1 + (pq m).2)

theorem s13 : Real.sqrt 13 * Real.sqrt 13 = 13 := Real.mul_self_sqrt (by norm_num)

theorem pow_plus (m : ℕ) :
    (1 + Real.sqrt 13) ^ m = (pq m).1 + (pq m).2 * Real.sqrt 13 := by
  induction m with
  | zero => simp [pq]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [pq]
    push_cast
    linear_combination ((pq m).2 : ℝ) * s13

theorem pow_minus (m : ℕ) :
    (1 - Real.sqrt 13) ^ m = (pq m).1 - (pq m).2 * Real.sqrt 13 := by
  induction m with
  | zero => simp [pq]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [pq]
    push_cast
    linear_combination ((pq m).2 : ℝ) * s13

/-- 39 * 2^(m + 1) * a(m + 1) = -39 * 4^(m + 1) + 52 P(m + 1) + 182 Q(m + 1). -/
def G (m : ℕ) : ℤ := -39 * 4 ^ (m + 1) + 52 * (pq (m + 1)).1 + 182 * (pq (m + 1)).2

theorem G_rec (m : ℕ) : G (m + 3) = 6 * G (m + 2) + 4 * G (m + 1) - 48 * G m := by
  simp only [G, pq]
  ring

theorem closed_int (m : ℕ) :
    39 * 2 ^ (m + 1) * ((st m).1 : ℤ) = G m ∧
      39 * 2 ^ (m + 2) * ((st (m + 1)).1 : ℤ) = G (m + 1) ∧
      39 * 2 ^ (m + 3) * ((st (m + 2)).1 : ℤ) = G (m + 2) := by
  induction m with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> decide
  | succ m ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    show 39 * 2 ^ (m + 4) * ((st (m + 3)).1 : ℤ) = G (m + 3)
    rw [A_rec m, G_rec m, ← h0, ← h1, ← h2]
    ring

theorem closed_form (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) = 2 ^ (-(n : ℤ)) * (-39 * 4 ^ n + (26 - 7 * Real.sqrt 13) * (1 - Real.sqrt 13) ^ n +
      (1 + Real.sqrt 13) ^ n * (26 + 7 * Real.sqrt 13)) / 39 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hA := (closed_int m).1
  rw [← a_succ] at hA
  unfold G at hA
  have hA' : 39 * 2 ^ (m + 1) * (a (m + 1) : ℝ) =
      -39 * 4 ^ (m + 1) + 52 * ((pq (m + 1)).1 : ℝ) + 182 * ((pq (m + 1)).2 : ℝ) := by
    exact_mod_cast hA
  have h2 : (2 : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) = 1 / 2 ^ (m + 1) := by
    rw [zpow_neg, zpow_natCast, one_div]
  have hpos : (0 : ℝ) < 2 ^ (m + 1) := by positivity
  rw [h2, pow_plus, pow_minus]
  field_simp
  linear_combination hA' - (14 : ℝ) * ((pq (m + 1)).2 : ℝ) * s13

/-- Both of Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    gf = X * (1 - 2 * X ^ 2) * ((1 - 2 * X) * (1 - X - 3 * X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 2 ^ (-(n : ℤ)) * (-39 * 4 ^ n +
      (26 - 7 * Real.sqrt 13) * (1 - Real.sqrt 13) ^ n +
      (1 + Real.sqrt 13) ^ n * (26 + 7 * Real.sqrt 13)) / 39 :=
  ⟨gf_eq, closed_form⟩

/-- Controls: a(1..15), the entry's data. -/
example : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 8 ∧ a 4 = 21 ∧ a 5 = 53 ∧ a 6 = 132 ∧ a 7 = 323 ∧
    a 8 = 783 ∧ a 9 = 1880 ∧ a 10 = 4485 ∧ a 11 = 10637 ∧ a 12 = 25116 ∧ a 13 = 59075 ∧
    a 14 = 138519 ∧ a 15 = 323936 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

/-- Control by direct enumeration of the 81 columns of length 4. -/
example : a 4 = 21 := by decide

end OMA.S_oeis_a267946

theorem OMA.solution : type_of% @OMA.S_oeis_a267946.main :=
  OMA.S_oeis_a267946.conjecture
