import OMAStatements.S_oeis_a204519

-- Problem: A204519: Square root of floor(A055851(n)/6).
-- Upstream: formal-conjectures statements/oeis-a204519.lean:0 (declaration OMA.S_oeis_a204519.main)
-- Credit: @lettucrisp (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.A204519Proof

open OMA.S_oeis_a204519 PowerSeries

/-- Multiplication by the unit `5 + 2√6` on `x + y√6`. -/
def U (p : ℕ × ℕ) : ℕ × ℕ := (5 * p.1 + 12 * p.2, 2 * p.1 + 5 * p.2)

/-- The solutions `(x, y)` of `6y² ≤ x² < 6y² + 6`, in increasing order. -/
def g : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (2, 0)
  | 3 => (3, 1)
  | k + 4 => U (g (k + 1))

lemma g_succ4 (k : ℕ) : g (k + 4) = U (g (k + 1)) := by
  rw [g]

lemma g_inv (k : ℕ) : 6 * (g k).2 ^ 2 ≤ (g k).1 ^ 2 ∧ (g k).1 ^ 2 < 6 * (g k).2 ^ 2 + 6 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [g]
    | 1, _ => simp [g]
    | 2, _ => simp [g]
    | 3, _ => simp [g]
    | k + 4, ih =>
      obtain ⟨h1, h2⟩ := ih (k + 1) (by omega)
      rw [g_succ4]
      simp only [U]
      constructor <;> nlinarith

lemma g_mono (k : ℕ) : (g k).1 < (g (k + 1)).1 ∧ (g k).2 ≤ (g (k + 1)).2 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [g]
    | 1, _ => simp [g]
    | 2, _ => simp [g]
    | 3, _ => simp [g, U]
    | k + 4, ih =>
      obtain ⟨h1, h2⟩ := ih (k + 1) (by omega)
      rw [g_succ4, show k + 4 + 1 = (k + 1) + 4 by omega, g_succ4]
      simp only [U]
      constructor <;> omega

lemma g_complete (x : ℕ) : ∀ y : ℕ, 6 * y ^ 2 ≤ x ^ 2 → x ^ 2 < 6 * y ^ 2 + 6 →
    ∃ k, g k = (x, y) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro y h1 h2
  by_cases hy : y ≤ 1
  · have hx : x ≤ 3 := by nlinarith
    interval_cases y <;> interval_cases x
    all_goals first
      | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
      | (revert h1 h2; norm_num)
  · push Not at hy
    have hA : 12 * y ≤ 5 * x := by nlinarith
    have hB : 2 * x ≤ 5 * y := by nlinarith
    have hC : x < 3 * y := by nlinarith
    have h1' : 6 * (5 * y - 2 * x) ^ 2 ≤ (5 * x - 12 * y) ^ 2 := by
      zify [hA, hB] at h1 h2 ⊢
      nlinarith
    have h2' : (5 * x - 12 * y) ^ 2 < 6 * (5 * y - 2 * x) ^ 2 + 6 := by
      zify [hA, hB] at h1 h2 ⊢
      nlinarith
    obtain ⟨k, hk⟩ := ih (5 * x - 12 * y) (by omega) (5 * y - 2 * x) h1' h2'
    rcases k with _ | j
    · simp only [g, Prod.mk.injEq] at hk
      omega
    · refine ⟨j + 4, ?_⟩
      rw [g_succ4, hk]
      simp only [U, Prod.mk.injEq]
      omega

/-- The predicate of A055851. -/
abbrev P : ℕ → Prop := fun m => IsSquare m ∧ IsSquare (m / 6)

lemma g_fst_strictMono : StrictMono fun k => (g k).1 :=
  strictMono_nat_of_lt_succ fun k => (g_mono k).1

lemma f_strictMono : StrictMono fun k => (g k).1 ^ 2 := by
  intro i j hij
  exact Nat.pow_lt_pow_left (g_fst_strictMono hij) (by norm_num)

lemma div_six (k : ℕ) : (g k).1 ^ 2 / 6 = (g k).2 ^ 2 := by
  obtain ⟨h1, h2⟩ := g_inv k
  generalize (g k).1 ^ 2 = X at h1 h2 ⊢
  generalize (g k).2 ^ 2 = Y at h1 h2 ⊢
  omega

lemma P_f (k : ℕ) : P ((g k).1 ^ 2) := by
  refine ⟨⟨(g k).1, sq _⟩, ?_⟩
  rw [div_six]
  exact ⟨(g k).2, sq _⟩

lemma P_surj {m : ℕ} (hm : P m) : ∃ k, (g k).1 ^ 2 = m := by
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := hm
  have h1 : 6 * s ^ 2 ≤ r ^ 2 := by
    have := Nat.div_mul_le_self m 6
    rw [hs] at this; rw [hr] at this; nlinarith
  have h2 : r ^ 2 < 6 * s ^ 2 + 6 := by
    have := Nat.lt_div_mul_add (a := m) (b := 6) (by norm_num)
    rw [hs] at this; rw [hr] at this; nlinarith
  obtain ⟨k, hk⟩ := g_complete r s h1 h2
  exact ⟨k, by rw [hk, hr]; ring⟩

lemma P_infinite : (Set.ofPred P).Infinite := by
  have : Set.range (fun k => (g k).1 ^ 2) ⊆ Set.ofPred P := by
    rintro _ ⟨k, rfl⟩; exact P_f k
  exact Set.Infinite.mono this (Set.infinite_range_of_injective f_strictMono.injective)

lemma nth_P (k : ℕ) : Nat.nth P k = (g k).1 ^ 2 := by
  have hall : ∀ n : ℕ, n ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred P), n < hf.toFinset.card } :=
    fun n hf => absurd hf P_infinite
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (fun k => (g k).1 ^ 2) ?_ ?_ ?_
    (hall k)).symm
  · intro m hm
    obtain ⟨k, hk⟩ := P_surj hm
    exact ⟨k, hall k, hk⟩
  · intro k _; exact P_f k
  · intro i _ j _ hij; exact f_strictMono hij

lemma a_succ (n : ℕ) : a (n + 1) = (g n).2 := by
  simp only [a, A055851, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero n)]
  rw [nth_P, div_six, Nat.sqrt_eq']

lemma rec_g (j : ℕ) : (g (j + 7)).2 + (g (j + 1)).2 = 10 * (g (j + 4)).2 := by
  rw [show j + 7 = (j + 3) + 4 by omega, g_succ4, show j + 3 + 1 = j + 4 by omega, g_succ4]
  simp only [U]
  omega

lemma recurrence (n : ℕ) (hn : 8 ≤ n) : (a n : ℤ) = 10 * a (n - 3) - a (n - 6) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
  rw [show j + 8 - 3 = (j + 4) + 1 by omega, show j + 8 - 6 = (j + 1) + 1 by omega,
    show j + 8 = (j + 7) + 1 by omega, a_succ, a_succ, a_succ]
  have := rec_g j
  omega

lemma small_a : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 1 ∧ a 5 = 2 ∧ a 6 = 4 ∧
    a 7 = 11 := by
  refine ⟨by simp [a], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [g, U] using a_succ 0
  · simpa [g, U] using a_succ 1
  · simpa [g, U] using a_succ 2
  · simpa [g, U] using a_succ 3
  · simpa [g, U] using a_succ 4
  · simpa [g, U] using a_succ 5
  · simpa [g, U] using a_succ 6

lemma coeff_lhs (F : PowerSeries ℤ) (n : ℕ) :
    coeff n ((X ^ 6 - 10 * X ^ 3 + 1) * F) =
      (if 6 ≤ n then coeff (n - 6) F else 0) - 10 * (if 3 ≤ n then coeff (n - 3) F else 0)
        + coeff n F := by
  have h10 : (10 : PowerSeries ℤ) = C 10 := by simp
  rw [show (X ^ 6 - 10 * X ^ 3 + 1 : PowerSeries ℤ) * F = X ^ 6 * F - C 10 * (X ^ 3 * F) + F by
    rw [h10]; ring]
  rw [map_add, map_sub, coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']

lemma coeff_rhs (n : ℕ) :
    coeff n (X ^ 4 * (X ^ 3 + 4 * X ^ 2 + 2 * X + 1) : PowerSeries ℤ) =
      (if n = 7 then 1 else 0) + (if n = 6 then 4 else 0) + (if n = 5 then 2 else 0)
        + (if n = 4 then 1 else 0) := by
  have h4 : (4 : PowerSeries ℤ) = C 4 := by simp
  have h2 : (2 : PowerSeries ℤ) = C 2 := by simp
  rw [show (X ^ 4 * (X ^ 3 + 4 * X ^ 2 + 2 * X + 1) : PowerSeries ℤ) =
      X ^ 7 + C 4 * X ^ 6 + C 2 * X ^ 5 + X ^ 4 by rw [h4, h2]; ring]
  simp only [map_add, coeff_X_pow, coeff_C_mul_X_pow]

end OMA.A204519Proof

open OMA.A204519Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a204519.main := by
  refine ⟨recurrence, ?_⟩
  ext n
  rw [coeff_lhs, coeff_rhs]
  simp only [PowerSeries.coeff_mk]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := small_a
  by_cases hn : 8 ≤ n
  · have := recurrence n hn
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    omega
  · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]
