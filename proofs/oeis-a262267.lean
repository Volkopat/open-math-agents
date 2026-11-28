import OMAStatements.S_oeis_a262267

-- Problem: A262267: Number of (n+2) X (1+2) 0..1 arrays with each row and column divisible by 5, read as a binary number with top and left being the most significant bits.
-- Upstream: formal-conjectures statements/oeis-a262267.lean:0 (declaration OMA.S_oeis_a262267.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a row x y z of bits is divisible by 5 iff y = 0 and z = x, so a good array is
-- (b, 0, b) for a column b of bits with 5 dividing its value. Reversing b and reading it in
-- base 2 (finFunctionFinEquiv) maps these bijectively onto the multiples of 5 below 2^(n+2),
-- so a(n) = (2^(n+2) + 4) / 5. As 2^(4k) = 1 mod 5, 5 a(n) = 2^(n+2) + 1, 2, 4, 3 for
-- n = 0, 1, 2, 3 mod 4, which gives the closed form (I^4 = 1), and a linear recurrence that
-- gives the g.f. by comparing coefficients.

open OMA.S_oeis_a262267 in
theorem OMA.solution : type_of% @OMA.S_oeis_a262267.main := by
  have hrow : ∀ x y z : Fin 2, (5 ∣ 4 * (x : ℕ) + 2 * (y : ℕ) + (z : ℕ) ↔ y = 0 ∧ z = x) := by
    decide
  have hcount : ∀ N : ℕ, ((Finset.range N).filter (fun m => 5 ∣ m)).card = (N + 4) / 5 := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hk : 5 ∣ k
      · rw [if_pos hk, Finset.card_insert_of_notMem
          (show k ∉ (Finset.range k).filter (fun m => 5 ∣ m) by simp), ih]
        omega
      · rw [if_neg hk, ih]
        omega
  have hA : ∀ n, a n = (2 ^ (n + 2) + 4) / 5 := by
    intro n
    obtain ⟨V, hV⟩ : ∃ V : (Fin (n + 2) → Fin 2) → ℕ,
        ∀ b, V b = ∑ i : Fin (n + 2), (b i : ℕ) * 2 ^ (n + 1 - (i : ℕ)) := ⟨_, fun _ => rfl⟩
    have hcol : ∀ (b : Fin (n + 2) → Fin 2) (c : Fin 3),
        colVal n (fun r c' => if c' = 1 then 0 else b r) c = if c = 1 then 0 else V b := by
      intro b c
      by_cases hc : c = 1
      · rw [if_pos hc]
        unfold colVal
        simp [hc]
      · rw [if_neg hc, hV]
        unfold colVal
        simp [hc]
    have step1 : a n = (Finset.univ.filter (fun b : Fin (n + 2) → Fin 2 => 5 ∣ V b)).card := by
      unfold a
      refine Finset.card_bij' (fun (M : Fin (n + 2) → Fin 3 → Fin 2) _ => fun r => M r 0)
        (fun (b : Fin (n + 2) → Fin 2) _ => fun (r : Fin (n + 2)) (c : Fin 3) =>
          if c = 1 then (0 : Fin 2) else b r) ?_ ?_ ?_ ?_
      · intro M hM
        have hM' : (∀ i, 5 ∣ rowVal n M i) ∧ (∀ j, 5 ∣ colVal n M j) :=
          (Finset.mem_filter.mp hM).2
        have h5 : 5 ∣ V (fun r => M r 0) := by
          rw [hV]
          exact hM'.2 0
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h5⟩
      · intro b hb
        have hb' : 5 ∣ V b := (Finset.mem_filter.mp hb).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_, fun c => ?_⟩
        · unfold rowVal
          refine (hrow _ _ _).mpr ⟨?_, ?_⟩
          · show (if (1 : Fin 3) = 1 then (0 : Fin 2) else b i) = 0
            exact if_pos (rfl : (1 : Fin 3) = 1)
          · show (if (2 : Fin 3) = 1 then (0 : Fin 2) else b i) =
              (if (0 : Fin 3) = 1 then (0 : Fin 2) else b i)
            rw [if_neg (show (2 : Fin 3) ≠ 1 by decide), if_neg (show (0 : Fin 3) ≠ 1 by decide)]
        · rw [hcol b c]
          by_cases hc : c = 1
          · rw [if_pos hc]
            exact dvd_zero 5
          · rw [if_neg hc]
            exact hb'
      · intro M hM
        have hM' : (∀ i, 5 ∣ rowVal n M i) ∧ (∀ j, 5 ∣ colVal n M j) :=
          (Finset.mem_filter.mp hM).2
        funext r c
        have h := (hrow (M r 0) (M r 1) (M r 2)).mp (hM'.1 r)
        show (if c = 1 then (0 : Fin 2) else M r 0) = M r c
        rcases (show ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) c with rfl | rfl | rfl
        · exact if_neg (show (0 : Fin 3) ≠ 1 by decide)
        · rw [if_pos (rfl : (1 : Fin 3) = 1), h.1]
        · rw [if_neg (show (2 : Fin 3) ≠ 1 by decide), h.2]
      · intro b _
        funext r
        show (if (0 : Fin 3) = 1 then (0 : Fin 2) else b r) = b r
        exact if_neg (show (0 : Fin 3) ≠ 1 by decide)
    have hrev : ∀ i : Fin (n + 2), n + 1 - ((Fin.rev i : Fin (n + 2)) : ℕ) = (i : ℕ) := by
      intro i
      have hi := i.isLt
      rw [Fin.val_rev]
      omega
    obtain ⟨F, hF⟩ : ∃ F : (Fin (n + 2) → Fin 2) ≃ Fin (2 ^ (n + 2)), ∀ b, (F b : ℕ) = V b := by
      refine ⟨(Equiv.mk (fun (b : Fin (n + 2) → Fin 2) (r : Fin (n + 2)) => b (Fin.rev r))
        (fun (b : Fin (n + 2) → Fin 2) (r : Fin (n + 2)) => b (Fin.rev r))
        (fun b => funext fun r => by simp only [Fin.rev_rev])
        (fun b => funext fun r => by simp only [Fin.rev_rev])).trans finFunctionFinEquiv,
        fun b => ?_⟩
      show (finFunctionFinEquiv (fun r => b (Fin.rev r)) : ℕ) = V b
      rw [finFunctionFinEquiv_apply, hV]
      exact Fintype.sum_bijective Fin.rev Fin.rev_bijective _ _ (fun i => by simp only [hrev])
    have step2 : (Finset.univ.filter (fun b : Fin (n + 2) → Fin 2 => 5 ∣ V b)).card =
        ((Finset.range (2 ^ (n + 2))).filter (fun m => 5 ∣ m)).card := by
      refine Finset.card_bij' (fun b _ => (F b : ℕ))
        (fun m hm => F.symm ⟨m, Finset.mem_range.mp (Finset.mem_filter.mp hm).1⟩) ?_ ?_ ?_ ?_
      · intro b hb
        have h5 : 5 ∣ (F b : ℕ) := by
          rw [hF]
          exact (Finset.mem_filter.mp hb).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (F b).isLt, h5⟩
      · intro m hm
        have hm' := Finset.mem_filter.mp hm
        have h5 : 5 ∣ V (F.symm ⟨m, Finset.mem_range.mp hm'.1⟩) := by
          rw [← hF, Equiv.apply_symm_apply]
          exact hm'.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h5⟩
      · intro b _
        exact F.symm_apply_apply b
      · intro m _
        exact congrArg Fin.val (F.apply_symm_apply _)
    rw [step1, step2, hcount]
  have h16 : ∀ k : ℕ, 2 ^ (4 * k) % 5 = 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show 4 * (k + 1) = 4 * k + 4 by ring, pow_add, show (2 : ℕ) ^ 4 = 16 by norm_num]
      omega
  have hrecN : ∀ j : ℕ, a (j + 5) + 3 * a (j + 3) + 2 * a (j + 1) =
      3 * a (j + 4) + 3 * a (j + 2) := by
    intro j
    rw [hA (j + 5), hA (j + 4), hA (j + 3), hA (j + 2), hA (j + 1),
      show 2 ^ (j + 5 + 2) = 2 ^ j * 128 by ring, show 2 ^ (j + 4 + 2) = 2 ^ j * 64 by ring,
      show 2 ^ (j + 3 + 2) = 2 ^ j * 32 by ring, show 2 ^ (j + 2 + 2) = 2 ^ j * 16 by ring,
      show 2 ^ (j + 1 + 2) = 2 ^ j * 8 by ring]
    obtain ⟨Y, hY⟩ : ∃ Y, 2 ^ j = Y := ⟨_, rfl⟩
    rw [hY]
    rcases (show Y % 5 = 0 ∨ Y % 5 = 1 ∨ Y % 5 = 2 ∨ Y % 5 = 3 ∨ Y % 5 = 4 by omega) with
      h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
  have hrecQ : ∀ j : ℕ, (a (j + 5) : ℚ) - 3 * a (j + 4) + 3 * a (j + 3) - 3 * a (j + 2) +
      2 * a (j + 1) = 0 := by
    intro j
    have h : (a (j + 5) : ℚ) + 3 * a (j + 3) + 2 * a (j + 1) =
        3 * a (j + 4) + 3 * a (j + 2) := by
      exact_mod_cast hrecN j
    linarith
  have a1 : a 1 = 2 := (hA 1).trans (by norm_num)
  have a2 : a 2 = 4 := (hA 2).trans (by norm_num)
  have a3 : a 3 = 7 := (hA 3).trans (by norm_num)
  have a4 : a 4 = 13 := (hA 4).trans (by norm_num)
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]
    norm_num
  have hIp : ∀ k r : ℕ, Complex.I ^ (4 * k + r) = Complex.I ^ r := by
    intro k r
    rw [pow_add, pow_mul, hI4, one_pow, one_mul]
  have hnIp : ∀ k r : ℕ, (-Complex.I) ^ (4 * k + r) = (-Complex.I) ^ r := by
    intro k r
    rw [pow_add, pow_mul, show (-Complex.I) ^ 4 = Complex.I ^ 4 by ring, hI4, one_pow, one_mul]
  have hC : ∀ n : ℕ, (a n : ℂ) = 1 / 2 + 2 ^ (2 + n) / 5 -
      (1 / 20 - Complex.I / 20) *
        ((1 + 2 * Complex.I) * (-Complex.I) ^ n + (2 + Complex.I) * Complex.I ^ n) := by
    intro n
    obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + r :=
      ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
    rw [hIp k r, hnIp k r]
    have hX := h16 k
    have hc := hA (4 * k + r)
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [show 2 ^ (4 * k + 0 + 2) = 2 ^ (4 * k) * 4 by ring] at hc
      have hn : 5 * a (4 * k + 0) = 2 ^ (4 * k) * 4 + 1 := by omega
      have hnC : (5 : ℂ) * (a (4 * k + 0) : ℂ) = 2 ^ (4 * k) * 4 + 1 := by exact_mod_cast hn
      linear_combination (1 / 5 : ℂ) * hnC + (-3 / 20 : ℂ) * Complex.I_sq
    · rw [show 2 ^ (4 * k + 1 + 2) = 2 ^ (4 * k) * 8 by ring] at hc
      have hn : 5 * a (4 * k + 1) = 2 ^ (4 * k) * 8 + 2 := by omega
      have hnC : (5 : ℂ) * (a (4 * k + 1) : ℂ) = 2 ^ (4 * k) * 8 + 2 := by exact_mod_cast hn
      linear_combination (1 / 5 : ℂ) * hnC + ((Complex.I - 2) / 20) * Complex.I_sq
    · rw [show 2 ^ (4 * k + 2 + 2) = 2 ^ (4 * k) * 16 by ring] at hc
      have hn : 5 * a (4 * k + 2) = 2 ^ (4 * k) * 16 + 4 := by omega
      have hnC : (5 : ℂ) * (a (4 * k + 2) : ℂ) = 2 ^ (4 * k) * 16 + 4 := by exact_mod_cast hn
      linear_combination (1 / 5 : ℂ) * hnC + ((6 - 3 * Complex.I ^ 2) / 20) * Complex.I_sq
    · rw [show 2 ^ (4 * k + 3 + 2) = 2 ^ (4 * k) * 32 by ring] at hc
      have hn : 5 * a (4 * k + 3) = 2 ^ (4 * k) * 32 + 3 := by omega
      have hnC : (5 : ℂ) * (a (4 * k + 3) : ℂ) = 2 ^ (4 * k) * 32 + 3 := by exact_mod_cast hn
      linear_combination (1 / 5 : ℂ) * hnC +
        ((Complex.I ^ 3 - 2 * Complex.I ^ 2 + 2) / 20) * Complex.I_sq
  have hAD : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
      ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X ^ 2)) =
      2 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 := by
    have e : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X ^ 2)) =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
            (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
            (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 2)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
            (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 3)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
            (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 4) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
      ring
    have e2 : (2 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 :
        PowerSeries ℚ) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * PowerSeries.X ^ 1
          + PowerSeries.X ^ 2
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * PowerSeries.X ^ 3 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m
      · norm_num [a1]
      · norm_num [a1, a2]
      · norm_num [a1, a2, a3]
      · norm_num [a1, a2, a3, a4]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
      rw [if_pos (show 1 ≤ j + 4 by omega), if_pos (show 2 ≤ j + 4 by omega),
        if_pos (show 3 ≤ j + 4 by omega), if_pos (show 4 ≤ j + 4 by omega),
        if_neg (show ¬ (j + 4 = 0) by omega), if_pos (show 1 ≤ j + 4 by omega),
        if_neg (show ¬ (j + 4 - 1 = 0) by omega), if_neg (show ¬ (j + 4 = 2) by omega),
        if_pos (show 3 ≤ j + 4 by omega), if_neg (show ¬ (j + 4 - 3 = 0) by omega),
        show j + 4 - 1 + 1 = j + 4 by omega, show j + 4 - 2 + 1 = j + 3 by omega,
        show j + 4 - 3 + 1 = j + 2 by omega, show j + 4 - 4 + 1 = j + 1 by omega,
        show j + 4 + 1 = j + 5 by omega]
      linarith [hrecQ j]
  refine ⟨?_, fun n _ => hC n⟩
  rw [mul_assoc, hAD]
