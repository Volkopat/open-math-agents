import OMAStatements.S_oeis_a356360

-- Problem: A356360: Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+1))))).
-- Upstream: formal-conjectures statements/oeis-a356360.lean:0 (declaration OMA.S_oeis_a356360.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with T k = 0! + 1! + ... + (k-1)!, the fold over the levels 2, ..., k + 2 with x at
-- the bottom equals 2((k+2)x - (k+3)(k+1)) / ((k+2) T(k+1) x - (k+3)(k+1) T k) (induction on k,
-- peeling off the lowest level; every intermediate value is nonzero). For n = k + 3 this gives
-- cf n = B / (2k+5) with 2B = (2k+5) T k + (k+2)(k+4) k!, so a n = (2k+5) / gcd(2k+5, B).
-- A prime p = 2k+5 divides none of k+2, k+4, k!, hence not B: a n = p. A composite 2k+5 >= 15
-- divides k! (a product d*e of odd factors with d < e <= k, or d*d | d*(2d) with 2d <= k),
-- hence B: a n = 1. For n = 5, B = 33 and a 5 = 9 / 3 = 3.

open OMA.S_oeis_a356360 in
theorem OMA.solution : type_of% @OMA.S_oeis_a356360.main := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ, ∀ k, T k = ∑ i ∈ Finset.range k, i.factorial :=
    ⟨_, fun _ => rfl⟩
  have TN : ∀ k : ℕ, T (k + 1) = T k + k.factorial := by
    intro k
    rw [hT (k + 1), hT k, Finset.sum_range_succ]
  have T1 : ∀ k : ℕ, (T (k + 1) : ℚ) = (T k : ℚ) + (k.factorial : ℚ) := by
    intro k
    rw [TN k, Nat.cast_add]
  have T0 : T 0 = 0 := by
    rw [hT 0, Finset.sum_range_zero]
  have T1n : T 1 = 1 := by
    rw [hT 1, Finset.sum_range_one, Nat.factorial_zero]
  have T2 : T 2 = 2 := by
    rw [hT 2]
    decide
  -- one level peeled off at the bottom
  have STEP : ∀ (k : ℕ) (x : ℚ), x ≠ 0 →
      (List.range' 2 (k + 1 + 1)).foldr (fun (j : ℕ) (x : ℚ) => (j : ℚ) - ((j : ℚ) + 1) / x) x =
        (List.range' 2 (k + 1)).foldr (fun (j : ℕ) (x : ℚ) => (j : ℚ) - ((j : ℚ) + 1) / x)
          ((((k : ℚ) + 3) * x - ((k : ℚ) + 4)) / x) := by
    intro k x hx0
    rw [List.range'_concat]
    simp only [List.foldr_append, List.foldr_cons, List.foldr_nil]
    congr 1
    rw [eq_div_iff hx0, sub_mul, div_mul_cancel₀ _ hx0]
    push_cast
    ring
  -- the value of the fold over the levels 2, ..., k + 2 with x at the bottom
  have CF : ∀ (k : ℕ) (x : ℚ), ((k : ℚ) + 3) * ((k : ℚ) + 1) < ((k : ℚ) + 2) * x →
      (List.range' 2 (k + 1)).foldr (fun (j : ℕ) (x : ℚ) => (j : ℚ) - ((j : ℚ) + 1) / x) x =
        2 * (((k : ℚ) + 2) * x - ((k : ℚ) + 3) * ((k : ℚ) + 1)) /
          (((k : ℚ) + 2) * (T (k + 1) : ℚ) * x - ((k : ℚ) + 3) * ((k : ℚ) + 1) * (T k : ℚ)) := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        norm_num at hx
      have hD0 : (((0 : ℕ) : ℚ) + 2) * (T (0 + 1) : ℚ) * x -
          (((0 : ℕ) : ℚ) + 3) * (((0 : ℕ) : ℚ) + 1) * (T 0 : ℚ) = 2 * x := by
        rw [T1 0, T0, Nat.factorial_zero]
        norm_num
      rw [hD0, List.range'_succ, List.range'_zero]
      simp only [List.foldr_cons, List.foldr_nil]
      push_cast
      field
    | succ k ih =>
      intro x hx
      push_cast at hx
      have hxpos : 0 < x := by
        nlinarith [hx, (Nat.cast_nonneg k : (0 : ℚ) ≤ k)]
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      rw [STEP k x hx0]
      have hc : ((k : ℚ) + 3) * ((k : ℚ) + 1) <
          ((k : ℚ) + 2) * ((((k : ℚ) + 3) * x - ((k : ℚ) + 4)) / x) := by
        rw [mul_div_assoc', lt_div_iff₀ hxpos]
        nlinarith [hx, (Nat.cast_nonneg k : (0 : ℚ) ≤ k)]
      rw [ih _ hc]
      have hyx : (((k : ℚ) + 3) * x - ((k : ℚ) + 4)) / x * x = ((k : ℚ) + 3) * x - ((k : ℚ) + 4) :=
        div_mul_cancel₀ _ hx0
      have hN : 2 * (((k : ℚ) + 2) * ((((k : ℚ) + 3) * x - ((k : ℚ) + 4)) / x) -
          ((k : ℚ) + 3) * ((k : ℚ) + 1)) * x =
          2 * ((((k + 1 : ℕ) : ℚ) + 2) * x - (((k + 1 : ℕ) : ℚ) + 3) * (((k + 1 : ℕ) : ℚ) + 1)) := by
        push_cast
        linear_combination 2 * ((k : ℚ) + 2) * hyx
      have hD : (((k : ℚ) + 2) * (T (k + 1) : ℚ) * ((((k : ℚ) + 3) * x - ((k : ℚ) + 4)) / x) -
          ((k : ℚ) + 3) * ((k : ℚ) + 1) * (T k : ℚ)) * x =
          (((k + 1 : ℕ) : ℚ) + 2) * (T (k + 1 + 1) : ℚ) * x -
            (((k + 1 : ℕ) : ℚ) + 3) * (((k + 1 : ℕ) : ℚ) + 1) * (T (k + 1) : ℚ) := by
        rw [T1 (k + 1), Nat.factorial_succ]
        push_cast
        linear_combination ((k : ℚ) + 2) * (T (k + 1) : ℚ) * hyx +
          ((k : ℚ) + 3) * ((k : ℚ) + 1) * x * T1 k
      rw [← mul_div_mul_right _ _ hx0, hN, hD]
  -- the denominator of b / m
  have DEN : ∀ b m : ℕ, m ≠ 0 → ((b : ℚ) / (m : ℚ)).den = m / m.gcd b := by
    intro b m hm
    have h := Rat.den_mkRat (b : ℤ) m
    rw [Rat.mkRat_eq_div, if_neg hm] at h
    simpa using h
  -- the fold in cf runs over the levels cast to ℚ; the same fold over the levels in ℕ
  have BR : ∀ (m : ℕ) (x : ℚ),
      (List.range' 2 m).foldr (fun j x => (j : ℚ) - ((j : ℚ) + 1) / x) x =
        (List.range' 2 m).foldr (fun (j : ℕ) (x : ℚ) => (j : ℚ) - ((j : ℚ) + 1) / x) x := by
    intro m x
    generalize List.range' 2 m = l
    induction l with
    | nil => rfl
    | cons c l ih => exact congrArg (fun y => (c : ℚ) - ((c : ℚ) + 1) / y) ih
  -- cf (k + 3) = B / (2k + 5)
  have CFV : ∀ k B : ℕ, 2 * B = (2 * k + 5) * T k + (k + 2) * (k + 4) * k.factorial →
      cf (k + 3) = (B : ℚ) / ((2 * k + 5 : ℕ) : ℚ) := by
    intro k B hB
    have hBq : (2 : ℚ) * (B : ℚ) = (2 * (k : ℚ) + 5) * (T k : ℚ) +
        ((k : ℚ) + 2) * ((k : ℚ) + 4) * (k.factorial : ℚ) := by
      exact_mod_cast hB
    have hc : ((k : ℚ) + 3) * ((k : ℚ) + 1) < ((k : ℚ) + 2) * (((k + 3 : ℕ) : ℚ) + 1) := by
      push_cast
      nlinarith [(Nat.cast_nonneg k : (0 : ℚ) ≤ k)]
    unfold cf
    rw [show k + 3 - 2 = k + 1 by omega, BR, CF k _ hc, T1 k, one_div_div,
      div_eq_div_iff (by push_cast; ring_nf; positivity) (by positivity)]
    push_cast
    linear_combination (-(2 * (k : ℚ) + 5)) * hBq
  -- T k is even for k >= 2, and so is 2B
  have Tev : ∀ k : ℕ, 2 ≤ k → 2 ∣ T k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp [T2]
    | succ k hk ih =>
      rw [TN k]
      exact dvd_add ih (Nat.dvd_factorial (by norm_num) hk)
  have Eev : ∀ k : ℕ, 2 ∣ (2 * k + 5) * T k + (k + 2) * (k + 4) * k.factorial := by
    intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · rw [T0]
        decide
      · rw [T1n]
        decide
    · exact dvd_add (Dvd.dvd.mul_left (Tev k hk) _)
        (Dvd.dvd.mul_left (Nat.dvd_factorial (by norm_num) hk) _)
  have AV : ∀ k : ℕ, ∃ B : ℕ, 2 * B = (2 * k + 5) * T k + (k + 2) * (k + 4) * k.factorial ∧
      a (k + 3) = (2 * k + 5) / (2 * k + 5).gcd B := by
    intro k
    obtain ⟨B, hB⟩ := Eev k
    refine ⟨B, hB.symm, ?_⟩
    unfold a
    rw [CFV k B hB.symm, DEN B (2 * k + 5) (by omega)]
  -- a composite odd number 2k + 5 >= 15 divides k!
  have key : ∀ d e n : ℕ, 0 < d → d < e → e ≤ n → d * e ∣ Nat.factorial n := by
    intro d e n hd hde hen
    have h1 : d ∣ Nat.factorial (e - 1) := Nat.dvd_factorial hd (by omega)
    have h2 : Nat.factorial (e - 1) * e = Nat.factorial e := by
      rw [mul_comm]
      exact Nat.mul_factorial_pred (by omega)
    have h3 : d * e ∣ Nat.factorial e := by
      rw [← h2]
      exact mul_dvd_mul_right h1 e
    exact h3.trans (Nat.factorial_dvd_factorial hen)
  have COMP : ∀ k : ℕ, 5 ≤ k → ¬ (2 * k + 5).Prime → (2 * k + 5) ∣ k.factorial := by
    intro k hk hnp
    obtain ⟨d, ⟨e, he⟩, hd2, hdm⟩ := Nat.exists_dvd_of_not_prime2 (by omega : 2 ≤ 2 * k + 5) hnp
    have hdo : ¬ 2 ∣ d := by
      intro h2
      have h2' : 2 ∣ 2 * k + 5 := by
        rw [he]
        exact Dvd.dvd.mul_right h2 e
      omega
    have heo : ¬ 2 ∣ e := by
      intro h2
      have h2' : 2 ∣ 2 * k + 5 := by
        rw [he]
        exact Dvd.dvd.mul_left h2 d
      omega
    have he2 : 2 ≤ e := by
      by_contra hlt
      have hle : d * e ≤ d * 1 := Nat.mul_le_mul_left d (by omega)
      omega
    have hd3 : 3 ≤ d := by omega
    have he3 : 3 ≤ e := by omega
    have hA : 3 * e ≤ d * e := Nat.mul_le_mul_right e hd3
    have hB : d * 3 ≤ d * e := Nat.mul_le_mul_left d he3
    rw [he]
    rcases Nat.lt_trichotomy d e with hlt | heq | hgt
    · exact key d e k (by omega) hlt (by omega)
    · subst heq
      have hd5 : 5 ≤ d := by
        by_contra h4
        have h3' : d = 3 := by omega
        subst h3'
        omega
      have hC : 5 * d ≤ d * d := Nat.mul_le_mul_right d hd5
      have hdd : d * d ∣ d * (2 * d) := mul_dvd_mul_left d (dvd_mul_left d 2)
      exact hdd.trans (key d (2 * d) k (by omega) (by omega) (by omega))
    · rw [mul_comm]
      exact key e d k (by omega) hgt (by omega)
  -- the formula line, with n = k + 3
  have P2 : ∀ k : ℕ, k ≠ 2 → ((2 * k + 5).Prime → a (k + 3) = 2 * k + 5) ∧
      (¬ (2 * k + 5).Prime → a (k + 3) = 1) := by
    intro k hk2
    obtain ⟨B, hB, hA⟩ := AV k
    refine ⟨fun hp => ?_, fun hnp => ?_⟩
    · have hnd : ¬ (2 * k + 5) ∣ B := by
        intro hdB
        have h1 : (2 * k + 5) ∣ (2 * k + 5) * T k + (k + 2) * (k + 4) * k.factorial := by
          rw [← hB]
          exact Dvd.dvd.mul_left hdB 2
        have h2 : (2 * k + 5) ∣ (k + 2) * (k + 4) * k.factorial :=
          (Nat.dvd_add_right (dvd_mul_right (2 * k + 5) (T k))).mp h1
        rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
        · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
          · have h5 := Nat.le_of_dvd (by omega) h4
            omega
          · have h5 := Nat.le_of_dvd (by omega) h4
            omega
        · have h5 := (Nat.Prime.dvd_factorial hp).mp h3
          omega
      have hcop : Nat.Coprime (2 * k + 5) B := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
      rw [hA, Nat.Coprime.gcd_eq_one hcop, Nat.div_one]
    · have hk5 : 5 ≤ k := by
        by_contra hlt
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl
        · exact hnp (by norm_num)
        · exact hnp (by norm_num)
        · exact hnp (by norm_num)
        · exact hnp (by norm_num)
      have hdk := COMP k hk5 hnp
      have h1 : (2 * k + 5) ∣ 2 * B := by
        rw [hB]
        exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_left hdk _)
      have hc2 : Nat.Coprime (2 * k + 5) 2 :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega))
      have h2 : (2 * k + 5) ∣ B := Nat.Coprime.dvd_of_dvd_mul_left hc2 h1
      rw [hA, Nat.gcd_eq_left h2, Nat.div_self (by omega)]
  -- the exceptional value a 5 = 3
  have A5 : a 5 = 3 := by
    obtain ⟨B, hB, hA⟩ := AV 2
    rw [T2, Nat.factorial_two] at hB
    have hB' : B = 33 := by omega
    rw [hB'] at hA
    have hA5 : a 5 = (2 * 2 + 5) / (2 * 2 + 5).gcd 33 := hA
    rw [hA5]
    norm_num
  refine ⟨fun n hn => ?_, fun n hn h5 => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    by_cases hk2 : k = 2
    · subst hk2
      right
      rw [show (2 : ℕ) + 3 = 5 from rfl, A5]
      exact Nat.prime_three
    · obtain ⟨hP, hC⟩ := P2 k hk2
      by_cases hp : (2 * k + 5).Prime
      · right
        rw [hP hp]
        exact hp
      · left
        exact hC hp
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have hk2 : k ≠ 2 := by omega
    rw [show 2 * (k + 3) - 1 = 2 * k + 5 by omega]
    exact P2 k hk2
