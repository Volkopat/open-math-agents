import OMAStatements.S_oeis_a267905

namespace OMA.S_oeis_a267905

open PowerSeries





/-- Number of columns of length m that pass the scan from the state (r, p, k). -/
def N (r : Option (Fin 3)) (p : Fin 3) (k m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 3, if ok r p k (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 3) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 3, f (List.ofFn x) =
      ∑ c : Fin 3, ∑ y : Fin m → Fin 3, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (r : Option (Fin 3)) (p : Fin 3) (k : ℕ) : N r p k 0 = 1 := by
  simp [N, ok]

theorem N_succ (r : Option (Fin 3)) (p : Fin 3) (k m : ℕ) :
    N r p k (m + 1) = ∑ c : Fin 3, if c.val ≤ k then (if c = p then
      (if (r.all fun v => decide (c = v)) = true then N (some c) c k m else 0)
      else N r c (max k (c.val + 1)) m) else 0 := by
  have h := sum_cons m (fun l => if ok r p k l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hk : c.val ≤ k
  · by_cases hc : c = p
    · subst hc
      by_cases hr : (r.all fun v => decide (c = v)) = true
      · simp [ok, hk, hr]
      · simp [ok, hk, hr]
    · simp [ok, hk, hc]
  · simp [ok, hk]

/-- The counts by state, as a tuple (E, A, B, C, D): E from (none, 0, 1), A from (none, p, k)
with k >= 2, B from (some v, v, k) with k >= 2, C from (some v, p, k) with p ≠ v and k >= 2,
D from (some 0, 0, 1). -/
def st : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 1, 1, 1)
  | m + 1 => ((st m).2.2.2.2 + (st m).2.1, 2 * (st m).2.1 + (st m).2.2.1,
      (st m).2.2.1 + 2 * (st m).2.2.2.1, (st m).2.2.1 + (st m).2.2.2.1,
      (st m).2.2.2.2 + (st m).2.2.2.1)

def E (m : ℕ) : ℕ := (st m).1
def A (m : ℕ) : ℕ := (st m).2.1
def B (m : ℕ) : ℕ := (st m).2.2.1
def C (m : ℕ) : ℕ := (st m).2.2.2.1
def D (m : ℕ) : ℕ := (st m).2.2.2.2

theorem E_succ (m : ℕ) : E (m + 1) = D m + A m := rfl
theorem A_succ (m : ℕ) : A (m + 1) = 2 * A m + B m := rfl
theorem B_succ (m : ℕ) : B (m + 1) = B m + 2 * C m := rfl
theorem C_succ (m : ℕ) : C (m + 1) = B m + C m := rfl
theorem D_succ (m : ℕ) : D (m + 1) = D m + C m := rfl

theorem N_eq (m : ℕ) :
    N none 0 1 m = E m ∧ (∀ p k, 2 ≤ k → N none p k m = A m) ∧
      (∀ v k, 2 ≤ k → N (some v) v k m = B m) ∧
      (∀ v p k, 2 ≤ k → p ≠ v → N (some v) p k m = C m) ∧ N (some 0) 0 1 m = D m := by
  induction m with
  | zero =>
    refine ⟨?_, fun p k _ => ?_, fun v k _ => ?_, fun v p k _ _ => ?_, ?_⟩ <;> rw [N_zero] <;> rfl
  | succ m ih =>
    obtain ⟨hE, hA, hB, hC, hD⟩ := ih
    refine ⟨?_, fun p k hk => ?_, fun v k hk => ?_, fun v p k hk hpv => ?_, ?_⟩
    · rw [N_succ, Fin.sum_univ_three, E_succ]
      simp [hD, hA 1 2 (le_refl 2)]
    · rw [N_succ, Fin.sum_univ_three, A_succ]
      have k0 : (0 : Fin 3).val ≤ k := by simp
      have k1 : (1 : Fin 3).val ≤ k := by simp; omega
      have k2 : (2 : Fin 3).val ≤ k := by simp; omega
      simp only [k0, k1, k2, if_true]
      fin_cases p <;>
        simp [hB _ k hk, hA _ (max k _) (le_max_of_le_left hk)] <;> ring
    · rw [N_succ, Fin.sum_univ_three, B_succ]
      have k0 : (0 : Fin 3).val ≤ k := by simp
      have k1 : (1 : Fin 3).val ≤ k := by simp; omega
      have k2 : (2 : Fin 3).val ≤ k := by simp; omega
      simp only [k0, k1, k2, if_true]
      fin_cases v <;>
        simp [hB _ k hk, hC _ _ (max k _) (le_max_of_le_left hk)] <;> ring
    · rw [N_succ, Fin.sum_univ_three, C_succ]
      have k0 : (0 : Fin 3).val ≤ k := by simp
      have k1 : (1 : Fin 3).val ≤ k := by simp; omega
      have k2 : (2 : Fin 3).val ≤ k := by simp; omega
      simp only [k0, k1, k2, if_true]
      fin_cases v <;> fin_cases p <;> simp at hpv ⊢ <;>
        simp [hB _ (max k _) (le_max_of_le_left hk), hC _ _ (max k _) (le_max_of_le_left hk)] <;>
        ring
    · rw [N_succ, Fin.sum_univ_three, D_succ]
      simp [hD, hC 0 1 2 (le_refl 2) (by decide)]

theorem a_succ (n : ℕ) : a (n + 1) = E n := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_three]
  simp only [valid]
  simp
  rw [← (N_eq n).1, N, Finset.card_filter]

/-- (1 + sqrt 2)^m = U(m) + V(m) sqrt 2, and (1 - sqrt 2)^m = U(m) - V(m) sqrt 2. -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | m + 1 => ((uv m).1 + 2 * (uv m).2, (uv m).1 + (uv m).2)

theorem s2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem pow_plus (m : ℕ) :
    (1 + Real.sqrt 2) ^ m = (uv m).1 + (uv m).2 * Real.sqrt 2 := by
  induction m with
  | zero => simp [uv]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [uv]
    push_cast
    linear_combination ((uv m).2 : ℝ) * s2

theorem pow_minus (m : ℕ) :
    (1 - Real.sqrt 2) ^ m = (uv m).1 - (uv m).2 * Real.sqrt 2 := by
  induction m with
  | zero => simp [uv]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [uv]
    push_cast
    linear_combination ((uv m).2 : ℝ) * s2

theorem U_rec (m : ℕ) : (uv (m + 2)).1 = 2 * (uv (m + 1)).1 + (uv m).1 := by
  simp only [uv]
  ring

/-- Closed forms of the five counts. -/
theorem closed_int (m : ℕ) :
    2 * (E m : ℤ) = (uv (m + 2)).1 - 2 ^ (m + 1) + 1 ∧ (A m : ℤ) = (uv (m + 2)).1 - 2 ^ (m + 1) ∧
      (B m : ℤ) = (uv (m + 1)).1 ∧ (C m : ℤ) = (uv (m + 1)).2 ∧
      2 * (D m : ℤ) = (uv (m + 1)).1 + 1 := by
  induction m with
  | zero => refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  | succ m ih =>
    obtain ⟨hE, hA, hB, hC, hD⟩ := ih
    have u3 := U_rec (m + 1)
    have u2 : (uv (m + 2)).1 = (uv (m + 1)).1 + 2 * (uv (m + 1)).2 := rfl
    have v2 : (uv (m + 2)).2 = (uv (m + 1)).1 + (uv (m + 1)).2 := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [E_succ]; push_cast
      rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring, u3]
      linear_combination hD + 2 * hA
    · rw [A_succ]; push_cast
      rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring, u3]
      linear_combination 2 * hA + hB
    · rw [B_succ]; push_cast
      rw [show m + 1 + 1 = m + 2 by ring, u2]
      linear_combination hB + 2 * hC
    · rw [C_succ]; push_cast
      rw [show m + 1 + 1 = m + 2 by ring, v2]
      linear_combination hB + hC
    · rw [D_succ]; push_cast
      rw [show m + 1 + 1 = m + 2 by ring, u2]
      linear_combination hD + 2 * hC

/-- 2 a(n) = U(n + 1) - 2^n + 1 for n >= 1. -/
theorem a_closed (n : ℕ) (hn : 1 ≤ n) : 2 * (a n : ℤ) = (uv (n + 1)).1 - 2 ^ n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]
  exact (closed_int m).1

theorem recurrence (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) = 5 * a (n - 1) - 7 * a (n - 2) + a (n - 3) + 2 * a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  have h5 : 2 * (a (m + 5) : ℤ) = (uv (m + 6)).1 - 2 ^ (m + 5) + 1 := a_closed (m + 5) (by omega)
  have h4 : 2 * (a (m + 4) : ℤ) = (uv (m + 5)).1 - 2 ^ (m + 4) + 1 := a_closed (m + 4) (by omega)
  have h3 : 2 * (a (m + 3) : ℤ) = (uv (m + 4)).1 - 2 ^ (m + 3) + 1 := a_closed (m + 3) (by omega)
  have h2 : 2 * (a (m + 2) : ℤ) = (uv (m + 3)).1 - 2 ^ (m + 2) + 1 := a_closed (m + 2) (by omega)
  have h1 : 2 * (a (m + 1) : ℤ) = (uv (m + 2)).1 - 2 ^ (m + 1) + 1 := a_closed (m + 1) (by omega)
  have r6 : (uv (m + 6)).1 = 2 * (uv (m + 5)).1 + (uv (m + 4)).1 := U_rec (m + 4)
  have r5 : (uv (m + 5)).1 = 2 * (uv (m + 4)).1 + (uv (m + 3)).1 := U_rec (m + 3)
  have r4 : (uv (m + 4)).1 = 2 * (uv (m + 3)).1 + (uv (m + 2)).1 := U_rec (m + 2)
  have key : 2 * ((a (m + 5) : ℤ) - (5 * a (m + 4) - 7 * a (m + 3) + a (m + 2) +
      2 * a (m + 1))) = 0 := by
    linear_combination h5 - 5 * h4 + 7 * h3 - h2 - 2 * h1 + r6 - 3 * r5 + 2 * r4
  omega

theorem a_one : a 1 = 1 := by rw [a_succ]; rfl
theorem a_two : a 2 = 2 := by rw [a_succ]; rfl
theorem a_three : a 3 = 5 := by rw [a_succ]; rfl
theorem a_four : a 4 = 13 := by rw [a_succ]; rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x(1 - 3x + 2x^2 + x^3)/((1 - x)(1 - 2x)(1 - 2x - x^2)), in Q[[x]]. -/
theorem gf_eq :
    gf = X * (1 - 3 * X + 2 * X ^ 2 + X ^ 3) * ((1 - X) * (1 - 2 * X) * (1 - 2 * X - X ^ 2))⁻¹ := by
  set Dn : ℚ⟦X⟧ := (1 - X) * (1 - 2 * X) * (1 - 2 * X - X ^ 2) with hDn
  have hden : constantCoeff Dn ≠ 0 := by rw [hDn]; simp
  have key : gf * Dn = X * (1 - 3 * X + 2 * X ^ 2 + X ^ 3) := by
    have e : gf * Dn = gf - PowerSeries.C 5 * (gf * X ^ 1) + PowerSeries.C 7 * (gf * X ^ 2) -
        gf * X ^ 3 - PowerSeries.C 2 * (gf * X ^ 4) := by
      rw [hDn]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) * (1 - 3 * X + 2 * X ^ 2 + X ^ 3) =
        X ^ 1 - PowerSeries.C 3 * X ^ 2 + PowerSeries.C 2 * X ^ 3 + X ^ 4 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    have h1 : (a 1 : ℚ) = 1 := by exact_mod_cast a_one
    have h2 : (a 2 : ℚ) = 2 := by exact_mod_cast a_two
    have h3 : (a 3 : ℚ) = 5 := by exact_mod_cast a_three
    have h4 : (a 4 : ℚ) = 13 := by exact_mod_cast a_four
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [h1, h2, h3, h4] <;> norm_num
    · have hr := recurrence n hn
      have hq : (a n : ℚ) = 5 * a (n - 1) - 7 * a (n - 2) + a (n - 3) + 2 * a (n - 4) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, if_true, show n ≠ 0 by omega, show n - 1 ≠ 0 by omega,
        show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, if_false,
        show n ≠ 1 by omega, show n ≠ 4 by omega, PowerSeries.coeff_C]
      linarith
  calc gf = gf * (Dn * Dn⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * Dn) * Dn⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- Barker's closed form, for n >= 1. -/
theorem closed_form (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) = ((1 - Real.sqrt 2) ^ (1 + n) + (1 + Real.sqrt 2) ^ (1 + n) - 2 * (2 ^ n - 1)) / 4 := by
  have h := a_closed n hn
  have h' : 2 * (a n : ℝ) = ((uv (n + 1)).1 : ℝ) - 2 ^ n + 1 := by exact_mod_cast h
  rw [show 1 + n = n + 1 by ring, pow_plus, pow_minus]
  linear_combination (1 / 2 : ℝ) * h'

/-- Both of Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    gf = X * (1 - 3 * X + 2 * X ^ 2 + X ^ 3) * ((1 - X) * (1 - 2 * X) * (1 - 2 * X - X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((1 - Real.sqrt 2) ^ (1 + n) + (1 + Real.sqrt 2) ^ (1 + n) - 2 * (2 ^ n - 1)) / 4 :=
  ⟨gf_eq, closed_form⟩

/-- Controls: a(1..13), the entry's data. -/
example : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 5 ∧ a 4 = 13 ∧ a 5 = 34 ∧ a 6 = 88 ∧ a 7 = 225 ∧
    a 8 = 569 ∧ a 9 = 1426 ∧ a 10 = 3548 ∧ a 11 = 8777 ∧ a 12 = 21613 ∧ a 13 = 53026 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

/-- Control by direct enumeration of the 81 columns of length 4. -/
example : a 4 = 13 := by decide

end OMA.S_oeis_a267905

theorem OMA.solution : type_of% @OMA.S_oeis_a267905.main :=
  OMA.S_oeis_a267905.conjecture
