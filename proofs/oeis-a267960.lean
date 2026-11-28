import OMAStatements.S_oeis_a267960

namespace OMA.S_oeis_a267960

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
      (if (r.all fun v => decide (v < c)) = true then N (some c) c m else 0) else N r c m := by
  have h := sum_cons m (fun l => if ok r p l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c = p
  · subst hc
    by_cases hr : (r.all fun v => decide (v < c)) = true
    · simp [ok, hr]
    · simp [ok, hr]
  · simp [ok, hc]

/-- The counts by class of states: x0, x1, x2 from (none, p) with p = 0, 1, 2; y00, y01, y02 from
(some 0, p); y1 from (some 1, 0) and (some 1, 1); y12 from (some 1, 2); z from (some 2, p). -/
structure S where
  x0 : ℕ
  x1 : ℕ
  x2 : ℕ
  y00 : ℕ
  y01 : ℕ
  y02 : ℕ
  y1 : ℕ
  y12 : ℕ
  z : ℕ

def st : ℕ → S
  | 0 => ⟨1, 1, 1, 1, 1, 1, 1, 1, 1⟩
  | m + 1 =>
    let s := st m
    ⟨s.y00 + s.x1 + s.x2, s.y1 + s.x0 + s.x2, s.z + s.x0 + s.x1, s.y01 + s.y02,
      s.y1 + s.y00 + s.y02, s.z + s.y00 + s.y01, s.y1 + s.y12, s.z + 2 * s.y1, 2 * s.z⟩

def Xv (m : ℕ) (p : Fin 3) : ℕ :=
  if p = 0 then (st m).x0 else if p = 1 then (st m).x1 else (st m).x2

def Bv (m : ℕ) (v p : Fin 3) : ℕ :=
  if v = 0 then (if p = 0 then (st m).y00 else if p = 1 then (st m).y01 else (st m).y02)
  else if v = 1 then (if p = 2 then (st m).y12 else (st m).y1) else (st m).z

theorem N_eq (m : ℕ) :
    (∀ p, N none p m = Xv m p) ∧ (∀ v p, N (some v) p m = Bv m v p) := by
  induction m with
  | zero =>
    refine ⟨fun p => ?_, fun v p => ?_⟩
    · rw [N_zero]; simp [Xv, st]
    · rw [N_zero]; simp [Bv, st]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun p => ?_, fun v p => ?_⟩
    · rw [N_succ]
      simp only [Option.all_none, if_true, h1, h2]
      fin_cases p <;> simp [Fin.sum_univ_three, Bv, Xv, st] <;> omega
    · rw [N_succ]
      simp only [Option.all_some, h2]
      fin_cases v <;> fin_cases p <;> simp [Fin.sum_univ_three, Bv, Xv, st] <;> omega

/-- The sum over the first element. -/
def T (m : ℕ) : ℕ := (st m).x0 + (st m).x1 + (st m).x2

theorem a_succ (n : ℕ) : a (n + 1) = T n := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_three]
  have e : ∀ c : Fin 3,
      (∑ y : Fin n → Fin 3, if valid (c :: List.ofFn y) = true then 1 else 0) = N none c n :=
    fun c => rfl
  rw [e 0, e 1, e 2, (N_eq n).1 0, (N_eq n).1 1, (N_eq n).1 2]
  simp [Xv, T]

theorem T_rec (m : ℕ) :
    (T (m + 6) : ℤ) = 6 * T (m + 5) - 9 * T (m + 4) - 8 * T (m + 3) + 24 * T (m + 2) -
      16 * T m := by
  simp only [T, st]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℤ) = 6 * a (n - 1) - 9 * a (n - 2) - 8 * a (n - 3) + 24 * a (n - 4) - 16 * a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 5 + 1 by omega, show m + 7 - 2 = m + 4 + 1 by omega,
    show m + 7 - 3 = m + 3 + 1 by omega, show m + 7 - 4 = m + 2 + 1 by omega,
    show m + 7 - 6 = m + 1 by omega, show m + 7 = m + 6 + 1 by omega]
  simp only [a_succ]
  exact T_rec m

theorem a_vals : a 1 = 3 ∧ a 2 = 9 ∧ a 3 = 24 ∧ a 4 = 63 ∧ a 5 = 159 ∧ a 6 = 394 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f. -/
theorem gf_eq : gf = X * (3 - 9 * X - 3 * X ^ 2 + 24 * X ^ 3 - 3 * X ^ 4 - 17 * X ^ 5) *
    ((1 + X) ^ 2 * (1 - 2 * X) ^ 4)⁻¹ := by
  set D : ℚ⟦X⟧ := (1 + X) ^ 2 * (1 - 2 * X) ^ 4 with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := a_vals
  have key : gf * D = X * (3 - 9 * X - 3 * X ^ 2 + 24 * X ^ 3 - 3 * X ^ 4 - 17 * X ^ 5) := by
    have e : gf * D = gf - C 6 * (gf * X ^ 1) + C 9 * (gf * X ^ 2) + C 8 * (gf * X ^ 3) -
        C 24 * (gf * X ^ 4) + C 16 * (gf * X ^ 6) := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) * (3 - 9 * X - 3 * X ^ 2 + 24 * X ^ 3 - 3 * X ^ 4 - 17 * X ^ 5) =
        C 3 * X ^ 1 - C 9 * X ^ 2 - C 3 * X ^ 3 + C 24 * X ^ 4 - C 3 * X ^ 5 - C 17 * X ^ 6 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6] <;> norm_num
    · have hr := recurrence n hn
      have hq : (a n : ℚ) = 6 * a (n - 1) - 9 * a (n - 2) - 8 * a (n - 3) + 24 * a (n - 4) -
          16 * a (n - 6) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, if_true,
        show n ≠ 0 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
        show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
        show n - 6 ≠ 0 by omega, if_false,
        show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
        show n ≠ 5 by omega, show n ≠ 6 by omega, coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- 7776 a(n) = 2^n (9n^3 + 396n^2 + 4005n + 7622) + (-1)^n (96n + 640). -/
def F (n : ℕ) : ℤ :=
  2 ^ n * (9 * n * (n * (n + 44) + 445) + 7622) + (-1) ^ n * (96 * n + 640)

theorem F_rec (m : ℕ) :
    F (m + 7) = 6 * F (m + 6) - 9 * F (m + 5) - 8 * F (m + 4) + 24 * F (m + 3) - 16 * F (m + 1) := by
  simp only [F]
  push_cast
  ring

theorem closed_int (m : ℕ) :
    7776 * (a (m + 1) : ℤ) = F (m + 1) ∧ 7776 * (a (m + 2) : ℤ) = F (m + 2) ∧
      7776 * (a (m + 3) : ℤ) = F (m + 3) ∧ 7776 * (a (m + 4) : ℤ) = F (m + 4) ∧
      7776 * (a (m + 5) : ℤ) = F (m + 5) ∧ 7776 * (a (m + 6) : ℤ) = F (m + 6) := by
  induction m with
  | zero =>
    obtain ⟨v1, v2, v3, v4, v5, v6⟩ := a_vals
    simp only [zero_add, v1, v2, v3, v4, v5, v6, F]
    norm_num
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    refine ⟨h2, h3, h4, h5, h6, ?_⟩
    have hr := recurrence (m + 7) (by omega)
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 6 = m + 1 by omega] at hr
    show 7776 * (a (m + 7) : ℤ) = F (m + 7)
    rw [hr, F_rec]
    linear_combination 6 * h6 - 9 * h5 - 8 * h4 + 24 * h3 - 16 * h1

theorem closed_even (n : ℕ) (h1 : 1 ≤ n) (he : Even n) :
    (a n : ℚ) = (96 * n + 2 ^ n * (9 * n * (n * (n + 44) + 445) + 7622) + 640) / 7776 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (closed_int m).1
  have hq : 7776 * (a (m + 1) : ℚ) = (F (m + 1) : ℚ) := by exact_mod_cast h
  simp only [F] at hq
  push_cast at hq
  rw [Even.neg_one_pow he] at hq
  push_cast
  linear_combination hq / 7776

theorem closed_odd (n : ℕ) (h1 : 1 ≤ n) (ho : Odd n) :
    (a n : ℚ) = (2 ^ n * (9 * n * (n * (n + 44) + 445) + 7622) - 32 * (3 * n + 20)) / 7776 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (closed_int m).1
  have hq : 7776 * (a (m + 1) : ℚ) = (F (m + 1) : ℚ) := by exact_mod_cast h
  simp only [F] at hq
  push_cast at hq
  rw [Odd.neg_one_pow ho] at hq
  push_cast
  linear_combination hq / 7776

/-- Barker's three conjectures. -/
theorem conjecture :
    gf = X * (3 - 9 * X - 3 * X ^ 2 + 24 * X ^ 3 - 3 * X ^ 4 - 17 * X ^ 5) *
      ((1 + X) ^ 2 * (1 - 2 * X) ^ 4)⁻¹ ∧
    (∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = (96 * n + 2 ^ n * (9 * n * (n * (n + 44) + 445) + 7622) + 640) / 7776) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n →
      (a n : ℚ) = (2 ^ n * (9 * n * (n * (n + 44) + 445) + 7622) - 32 * (3 * n + 20)) / 7776) :=
  ⟨gf_eq, closed_even, closed_odd⟩

/-- Controls: a(1..14), the entry's data. -/
example : a 1 = 3 ∧ a 2 = 9 ∧ a 3 = 24 ∧ a 4 = 63 ∧ a 5 = 159 ∧ a 6 = 394 ∧ a 7 = 957 ∧
    a 8 = 2292 ∧ a 9 = 5419 ∧ a 10 = 12678 ∧ a 11 = 29385 ∧ a 12 = 67560 ∧ a 13 = 154215 ∧
    a 14 = 349770 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

/-- Control by direct enumeration of the 81 columns of length 4. -/
example : a 4 = 63 := by decide

end OMA.S_oeis_a267960

theorem OMA.solution : type_of% @OMA.S_oeis_a267960.main :=
  OMA.S_oeis_a267960.conjecture
