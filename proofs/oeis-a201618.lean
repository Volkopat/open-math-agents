import OMAStatements.S_oeis_a201618

namespace OMA.S_oeis_a201618

open PowerSeries





/-- Number of columns of length m that pass the scan from the state (p, s). -/
def N (p : Fin 4) (s : Bool) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 4, if ok p s (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 4) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 4, f (List.ofFn x) =
      ∑ c : Fin 4, ∑ y : Fin m → Fin 4, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 4).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (p : Fin 4) (s : Bool) : N p s 0 = if s = true then 1 else 0 := by
  cases s <;> simp [N, ok]

theorem N_succ (p : Fin 4) (s : Bool) (m : ℕ) :
    N p s (m + 1) = ∑ c : Fin 4, if p ≤ c then (if c = p then N c true m else
      (if s = true then N c false m else 0)) else 0 := by
  have h := sum_cons m (fun l => if ok p s l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hpc : p ≤ c
  · by_cases hc : c = p
    · subst hc
      simp [ok]
    · cases s <;> simp [ok, hpc, hc]
  · simp [ok, hpc]

/-- Counts by state: t i from (i, true) and f i from (i, false). -/
structure S where
  t0 : ℕ
  t1 : ℕ
  t2 : ℕ
  t3 : ℕ
  f0 : ℕ
  f1 : ℕ
  f2 : ℕ
  f3 : ℕ

def st : ℕ → S
  | 0 => ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
  | m + 1 =>
    let s := st m
    ⟨s.t0 + s.f1 + s.f2 + s.f3, s.t1 + s.f2 + s.f3, s.t2 + s.f3, s.t3, s.t0, s.t1, s.t2, s.t3⟩

def Tv (m : ℕ) (p : Fin 4) : ℕ :=
  if p = 0 then (st m).t0 else if p = 1 then (st m).t1 else if p = 2 then (st m).t2 else (st m).t3

def Fv (m : ℕ) (p : Fin 4) : ℕ :=
  if p = 0 then (st m).f0 else if p = 1 then (st m).f1 else if p = 2 then (st m).f2 else (st m).f3

theorem N_eq (m : ℕ) : ∀ p, N p true m = Tv m p ∧ N p false m = Fv m p := by
  induction m with
  | zero => intro p; fin_cases p <;> simp [N_zero, Tv, Fv, st]
  | succ m ih =>
    intro p
    have ht : ∀ q, N q true m = Tv m q := fun q => (ih q).1
    have hf : ∀ q, N q false m = Fv m q := fun q => (ih q).2
    constructor
    · rw [N_succ]
      fin_cases p <;> simp [Fin.sum_univ_four, ht, hf, Tv, Fv, st] <;> ring
    · rw [N_succ]
      fin_cases p <;> simp [Fin.sum_univ_four, ht, hf, Tv, Fv, st]

/-- The sum over the first element. -/
def T (m : ℕ) : ℕ := (st m).f0 + (st m).f1 + (st m).f2 + (st m).f3

theorem a_succ (n : ℕ) : a (n + 1) = T n := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_four]
  have e : ∀ c : Fin 4,
      (∑ y : Fin n → Fin 4, if valid (c :: List.ofFn y) = true then 1 else 0) = N c false n :=
    fun c => rfl
  rw [e 0, e 1, e 2, e 3, (N_eq n 0).2, (N_eq n 1).2, (N_eq n 2).2, (N_eq n 3).2]
  simp [Fv, T]

theorem T_rec (m : ℕ) :
    (T (m + 8) : ℤ) = 4 * T (m + 7) - 6 * T (m + 6) + 4 * T (m + 5) - T (m + 4) := by
  simp only [T, st]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  rw [show m + 9 - 1 = m + 7 + 1 by omega, show m + 9 - 2 = m + 6 + 1 by omega,
    show m + 9 - 3 = m + 5 + 1 by omega, show m + 9 - 4 = m + 4 + 1 by omega,
    show m + 9 = m + 8 + 1 by omega]
  simp only [a_succ]
  exact T_rec m

theorem a_vals : a 1 = 0 ∧ a 2 = 4 ∧ a 3 = 4 ∧ a 4 = 10 ∧ a 5 = 16 ∧ a 6 = 26 ∧ a 7 = 40 ∧
    a 8 = 59 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x^2(2 - 2x + x^2)(2 - 4x + 4x^2 - 2x^3 + x^4)/(1 - x)^4, in Q[[x]]. -/
theorem gf_eq : gf = X ^ 2 * (2 - 2 * X + X ^ 2) * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) *
    ((1 - X) ^ 4)⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - X) ^ 4 with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := a_vals
  have key : gf * D = X ^ 2 * (2 - 2 * X + X ^ 2) * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) := by
    have e : gf * D = gf - C 4 * (gf * X ^ 1) + C 6 * (gf * X ^ 2) - C 4 * (gf * X ^ 3) +
        gf * X ^ 4 := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) ^ 2 * (2 - 2 * X + X ^ 2) * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) =
        C 4 * X ^ 2 - C 12 * X ^ 3 + C 18 * X ^ 4 - C 16 * X ^ 5 + C 10 * X ^ 6 - C 4 * X ^ 7 +
          X ^ 8 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 9 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8] <;> norm_num
    · have hr := recurrence n (by omega)
      have hq : (a n : ℚ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
        show 8 ≤ n by omega, if_true, show n ≠ 0 by omega, show n - 1 ≠ 0 by omega,
        show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
        show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega,
        show n - 8 ≠ 0 by omega, if_false, show n ≠ 8 by omega, coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- Both of Barker's conjectures: the g.f. and the recurrence for n > 8. -/
theorem conjecture :
    gf = X ^ 2 * (2 - 2 * X + X ^ 2) * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) *
      ((1 - X) ^ 4)⁻¹ ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) :=
  ⟨gf_eq, recurrence⟩

/-- Controls: a(1..20), the entry's data. -/
example : a 1 = 0 ∧ a 2 = 4 ∧ a 3 = 4 ∧ a 4 = 10 ∧ a 5 = 16 ∧ a 6 = 26 ∧ a 7 = 40 ∧
    a 8 = 59 ∧ a 9 = 84 ∧ a 10 = 116 ∧ a 11 = 156 ∧ a 12 = 205 ∧ a 13 = 264 ∧ a 14 = 334 ∧
    a 15 = 416 ∧ a 16 = 511 ∧ a 17 = 620 ∧ a 18 = 744 ∧ a 19 = 884 ∧ a 20 = 1041 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [a_succ] <;> rfl

/-- Control by direct enumeration of the 256 columns of length 4. -/
example : a 4 = 10 := by decide

end OMA.S_oeis_a201618

theorem OMA.solution : type_of% @OMA.S_oeis_a201618.main :=
  OMA.S_oeis_a201618.conjecture
