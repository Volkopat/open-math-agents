import OMAStatements.S_oeis_a034108

namespace OMA.S_oeis_a034108


/-- The computable form of that digit. -/
def dig (m : ℕ) : ℕ := Nat.sqrt (100 * m) % 10

theorem sqrt_100 (m : ℕ) : Nat.sqrt (100 * m) / 10 = Nat.sqrt m := by
  have h1 := Nat.sqrt_le' m
  have h2 := Nat.lt_succ_sqrt' m
  have a1 : 10 * Nat.sqrt m ≤ Nat.sqrt (100 * m) := Nat.le_sqrt'.mpr (by nlinarith)
  have a2 : Nat.sqrt (100 * m) < 10 * Nat.sqrt m + 10 := Nat.sqrt_lt'.mpr (by nlinarith)
  omega

theorem digit_eq (m : ℕ) : digit m = dig m := by
  unfold digit dig
  have h1 : (⌊Real.sqrt m⌋ : ℤ) = Nat.sqrt m := Real.floor_real_sqrt_eq_nat_sqrt
  have hs : Real.sqrt ((100 * m : ℕ) : ℝ) = 10 * Real.sqrt m := by
    rw [show ((100 * m : ℕ) : ℝ) = 10 ^ 2 * (m : ℝ) by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have h2 : ⌊10 * Real.sqrt m⌋ = (Nat.sqrt (100 * m) : ℤ) := by
    rw [← hs, Real.floor_real_sqrt_eq_nat_sqrt]
  rw [Int.fract, mul_sub, show (10 : ℝ) * (⌊Real.sqrt m⌋ : ℝ) = ((10 * ⌊Real.sqrt m⌋ : ℤ) : ℝ) by
    push_cast; ring, Int.floor_sub_intCast, h2, h1]
  have h3 := sqrt_100 m
  have h4 := Nat.mod_add_div (Nat.sqrt (100 * m)) 10
  omega

/-- The first term of a run: `m` has digit 2 and `m - 1` does not. -/
def Q (m : ℕ) : Prop := 0 < m ∧ dig m = 2 ∧ dig (m - 1) ≠ 2

instance : DecidablePred Q := fun m => by unfold Q dig; infer_instance


theorem runStart_eq : RunStart = Q := by
  funext m
  apply propext
  unfold RunStart Q
  rw [digit_eq, digit_eq]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by exact_mod_cast h1, fun h => h2 (by exact_mod_cast h)⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by exact_mod_cast h1, fun h => h2 (by exact_mod_cast h)⟩


/-- The conjecture (the recurrence). -/
def Conjecture : Prop :=
  ∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 5) - 2 * a (n - 6) + a (n - 7)

theorem dig_two_iff (m : ℕ) :
    dig m = 2 ↔ ∃ k, (10 * k + 2) ^ 2 ≤ 100 * m ∧ 100 * m < (10 * k + 3) ^ 2 := by
  unfold dig
  constructor
  · intro h
    refine ⟨Nat.sqrt (100 * m) / 10, ?_, ?_⟩
    · have := Nat.sqrt_le' (100 * m)
      have e : 10 * (Nat.sqrt (100 * m) / 10) + 2 = Nat.sqrt (100 * m) := by omega
      rw [e]
      exact this
    · have := Nat.lt_succ_sqrt' (100 * m)
      have e : 10 * (Nat.sqrt (100 * m) / 10) + 3 = Nat.sqrt (100 * m) + 1 := by omega
      rw [e]
      exact this
  · rintro ⟨k, h1, h2⟩
    have hs1 : 10 * k + 2 ≤ Nat.sqrt (100 * m) := Nat.le_sqrt'.mpr h1
    have hs2 : Nat.sqrt (100 * m) < 10 * k + 3 := Nat.sqrt_lt'.mpr h2
    omega

/-- The first element of the run with integer part `k`: `k^2 + ⌈(40k+4)/100⌉`. -/
def M (k : ℕ) : ℕ := k ^ 2 + (40 * k + 103) / 100

theorem sq2 (k : ℕ) : (10 * k + 2) ^ 2 = 100 * k ^ 2 + 40 * k + 4 := by ring
theorem sq3 (k : ℕ) : (10 * k + 3) ^ 2 = 100 * k ^ 2 + 60 * k + 9 := by ring

theorem Q_M (k : ℕ) (hk : k = 2 ∨ 4 ≤ k) : Q (M k) := by
  have hk1 : 1 ≤ k := by omega
  unfold Q
  refine ⟨?_, (dig_two_iff _).mpr ⟨k, ?_, ?_⟩, ?_⟩
  · unfold M
    have : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · unfold M
    rw [sq2]
    omega
  · unfold M
    rw [sq3]
    rcases hk with rfl | hk
    · norm_num
    · by_cases h4 : k = 4
      · subst h4
        norm_num
      · omega
  · intro h
    obtain ⟨j, h1, h2⟩ := (dig_two_iff _).mp h
    have hM1 : 100 * (M k - 1) < (10 * k + 2) ^ 2 := by
      unfold M
      rw [sq2]
      omega
    have hjk : 10 * j + 2 < 10 * k + 2 :=
      (Nat.pow_lt_pow_iff_left (by norm_num)).mp (lt_of_le_of_lt h1 hM1)
    have h3 : (10 * j + 3) ^ 2 ≤ (10 * k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : (10 * k) ^ 2 ≤ 100 * (M k - 1) := by
      unfold M
      have : (10 * k) ^ 2 = 100 * k ^ 2 := by ring
      rw [this]
      omega
    omega

theorem Q_imp (m : ℕ) (hm : Q m) : ∃ k, (k = 2 ∨ 4 ≤ k) ∧ m = M k := by
  obtain ⟨h0, hd, hd1⟩ := hm
  obtain ⟨k, h1, h2⟩ := (dig_two_iff m).mp hd
  rw [sq2] at h1
  rw [sq3] at h2
  have hge : M k ≤ m := by
    unfold M
    omega
  have heq : m = M k := by
    by_contra hne
    apply hd1
    apply (dig_two_iff _).mpr
    refine ⟨k, ?_, ?_⟩
    · rw [sq2]
      simp only [M] at hge hne
      omega
    · rw [sq3]
      omega
  refine ⟨k, ?_, heq⟩
  by_contra hk
  have : k = 0 ∨ k = 1 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl <;> norm_num at h1 h2 <;> omega

/-- The enumeration of the run starts. -/
def g (j : ℕ) : ℕ := if j = 0 then M 2 else M (j + 3)

theorem M_lt (k : ℕ) : M k < M (k + 1) := by
  unfold M
  have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
  rw [this]
  omega

theorem M_mono : StrictMono M := strictMono_nat_of_lt_succ M_lt

theorem g_strictMono : StrictMono g := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold g
  by_cases hj : j = 0
  · subst hj
    simp only [if_true, show (0 + 1 = 0) = False by simp, if_false]
    exact M_mono (by norm_num)
  · rw [if_neg hj, if_neg (by omega)]
    exact M_mono (by omega)

theorem g_Q (j : ℕ) : Q (g j) := by
  unfold g
  split_ifs
  · exact Q_M 2 (Or.inl rfl)
  · exact Q_M _ (Or.inr (by omega))

theorem Q_infinite : (Set.ofPred Q).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  have h1 : N + 1 ≤ g (N + 1) := g_strictMono.le_apply
  have := hN (show g (N + 1) ∈ Set.ofPred Q from g_Q (N + 1))
  omega

theorem g_eq_nth (n : ℕ) : g n = Nat.nth Q n := by
  have hall : ∀ n, n ∈ {n : ℕ | ∀ hf : (Set.ofPred Q).Finite, n < hf.toFinset.card} :=
    fun n hf => absurd hf Q_infinite
  refine Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn g ?_ ?_ ?_ (hall n)
  · intro m hm
    obtain ⟨k, hk, rfl⟩ := Q_imp m hm
    rcases hk with rfl | hk
    · exact ⟨0, hall 0, by simp [g]⟩
    · exact ⟨k - 3, hall _, by unfold g; rw [if_neg (by omega), show k - 3 + 3 = k by omega]⟩
  · intro j _
    exact g_Q j
  · intro x _ y _ hxy
    exact g_strictMono hxy

theorem a_eq (n : ℕ) (hn : 2 ≤ n) : a n = M (n + 2) := by
  rw [a, runStart_eq, ← g_eq_nth]
  unfold g
  rw [if_neg (by omega), show n - 1 + 3 = n + 2 by omega]

theorem M_add_five (k : ℕ) : M (k + 5) = M k + 10 * k + 27 := by
  unfold M
  have : (k + 5) ^ 2 = k ^ 2 + 10 * k + 25 := by ring
  rw [this]
  omega

theorem conjecture_true : Conjecture := by
  intro n hn
  rw [a_eq n (by omega), a_eq (n - 1) (by omega), a_eq (n - 2) (by omega), a_eq (n - 5) (by omega),
    a_eq (n - 6) (by omega), a_eq (n - 7) (by omega)]
  have e1 : M (n + 2) = M (n - 5 + 2) + 10 * (n - 5 + 2) + 27 := by
    rw [← M_add_five]; congr 1; omega
  have e2 : M (n - 1 + 2) = M (n - 6 + 2) + 10 * (n - 6 + 2) + 27 := by
    rw [← M_add_five]; congr 1; omega
  have e3 : M (n - 2 + 2) = M (n - 7 + 2) + 10 * (n - 7 + 2) + 27 := by
    rw [← M_add_five]; congr 1; omega
  rw [e1, e2, e3]
  have h5 : n - 5 + 2 = n - 3 := by omega
  have h6 : n - 6 + 2 = n - 4 := by omega
  have h7 : n - 7 + 2 = n - 5 := by omega
  rw [h5, h6, h7]
  push_cast [show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega]
  ring

/-- Control: the first terms listed in the entry. -/
theorem first_terms : a 1 = 5 ∧ a 2 = 18 ∧ a 3 = 28 ∧ a 4 = 39 ∧ a 5 = 52 ∧ a 6 = 68 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a, runStart_eq, ← g_eq_nth]
    decide
  all_goals (rw [a_eq _ (by norm_num)]; decide)

/-- The terms `a(7)` and `a(8)`, used with `first_terms` for the low coefficients of the g.f. -/
theorem low_terms : a 7 = 85 ∧ a 8 = 105 := by
  refine ⟨?_, ?_⟩ <;> (rw [a_eq _ (by norm_num)]; decide)

open PowerSeries in
/-- Wu's g.f. as an identity of formal power series: from `x^9` on the coefficients of the
product are the recurrence, below they are `a(1..8)`. -/
theorem gf_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((X - 1) ^ 3 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X * (-6 * X ^ 7 + 7 * X ^ 6 + 2 * X ^ 5 - 2 * X ^ 4 - X ^ 3 + 3 * X ^ 2 - 8 * X - 5) := by
  have hN : (X * (-6 * X ^ 7 + 7 * X ^ 6 + 2 * X ^ 5 - 2 * X ^ 4 - X ^ 3 + 3 * X ^ 2 - 8 * X - 5) :
      ℚ⟦X⟧) = C 7 * X ^ 7 + C 2 * X ^ 6 + C 3 * X ^ 3 - C 6 * X ^ 8 - C 2 * X ^ 5 - C 1 * X ^ 4 -
        C 8 * X ^ 2 - C 5 * X ^ 1 := by
    simp only [map_ofNat, map_one]
    ring
  have e : ∀ A : ℚ⟦X⟧, A * ((X - 1) ^ 3 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      A * X ^ 7 - C 2 * (A * X ^ 6) + A * X ^ 5 - A * X ^ 2 + C 2 * (A * X ^ 1) - A := by
    intro A
    simp only [map_ofNat]
    ring
  rw [hN, e]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := first_terms
    obtain ⟨h7, h8⟩ := low_terms
    interval_cases n <;> simp [h1, h2, h3, h4, h5, h6, h7, h8] <;> norm_num
  · have hr : (a n : ℚ) = 2 * a (n - 1) - a (n - 2) + a (n - 5) - 2 * a (n - 6) + a (n - 7) := by
      exact_mod_cast conjecture_true n hn
    simp only [show n ≠ 0 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
      show 8 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
      show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega, show n - 8 ≠ 0 by omega, if_true,
      if_false]
    linarith

end OMA.S_oeis_a034108

theorem OMA.solution : type_of% @OMA.S_oeis_a034108.main :=
  ⟨OMA.S_oeis_a034108.conjecture_true, OMA.S_oeis_a034108.gf_identity⟩
