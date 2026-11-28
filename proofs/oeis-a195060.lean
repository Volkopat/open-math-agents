import OMAStatements.S_oeis_a195060

-- Problem: A195060: Numbers on the main diagonals and on the axes (x,y) in the square spiral whose vertices are the generalized pentagonal numbers A001318.
-- Upstream: formal-conjectures statements/oeis-a195060.lean:0 (declaration OMA.S_oeis_a195060.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the union in increasing order is f(0) = 0, f(4k+1) = floor(3(k+1)^2/2),
-- f(4k+2) = (k+1)(3k+4)/2, f(4k+3) = 3(k+1)(k+2)/2, f(4k+4) = (k+2)(3k+5)/2: f is strictly
-- increasing and its range is the union, so a = f (Nat.nth_comp_of_strictMono). For m >= 1,
-- 2(f(m+8) - f(m)) = 3m + c with c = 22, 21, 20, 21 for m = 0, 1, 2, 3 mod 4, which gives the
-- recurrence for n >= 13 by four cases; the g.f. follows by comparing coefficients.

open OMA.S_oeis_a195060 in
theorem OMA.solution : type_of% @OMA.S_oeis_a195060.main := by
  obtain ⟨f, f0, fA, fB, fC, fD⟩ : ∃ f : ℕ → ℕ, f 0 = 0 ∧
      (∀ k, f (4 * k + 4) = (k + 2) * (3 * k + 5) / 2) ∧
      (∀ k, f (4 * k + 1) = 3 * (k + 1) ^ 2 / 2) ∧
      (∀ k, f (4 * k + 2) = (k + 1) * (3 * k + 4) / 2) ∧
      (∀ k, f (4 * k + 3) = 3 * (k + 1) * (k + 1 + 1) / 2) := by
    refine ⟨fun n => if n = 0 then 0 else if n % 4 = 0 then (n / 4 + 1) * (3 * (n / 4) + 2) / 2
      else if n % 4 = 1 then 3 * (n / 4 + 1) ^ 2 / 2
      else if n % 4 = 2 then (n / 4 + 1) * (3 * (n / 4) + 4) / 2
      else 3 * (n / 4 + 1) * (n / 4 + 1 + 1) / 2, by simp, ?_, ?_, ?_, ?_⟩
    · intro k
      beta_reduce
      rw [if_neg (show ¬(4 * k + 4 = 0) by omega), if_pos (show (4 * k + 4) % 4 = 0 by omega),
        show (4 * k + 4) / 4 = k + 1 by omega,
        show (k + 1 + 1) * (3 * (k + 1) + 2) = (k + 2) * (3 * k + 5) by ring]
    · intro k
      beta_reduce
      rw [if_neg (show ¬(4 * k + 1 = 0) by omega), if_neg (show ¬((4 * k + 1) % 4 = 0) by omega),
        if_pos (show (4 * k + 1) % 4 = 1 by omega), show (4 * k + 1) / 4 = k by omega]
    · intro k
      beta_reduce
      rw [if_neg (show ¬(4 * k + 2 = 0) by omega), if_neg (show ¬((4 * k + 2) % 4 = 0) by omega),
        if_neg (show ¬((4 * k + 2) % 4 = 1) by omega), if_pos (show (4 * k + 2) % 4 = 2 by omega),
        show (4 * k + 2) / 4 = k by omega]
    · intro k
      beta_reduce
      rw [if_neg (show ¬(4 * k + 3 = 0) by omega), if_neg (show ¬((4 * k + 3) % 4 = 0) by omega),
        if_neg (show ¬((4 * k + 3) % 4 = 1) by omega),
        if_neg (show ¬((4 * k + 3) % 4 = 2) by omega), show (4 * k + 3) / 4 = k by omega]
  -- the three products are even
  have ev1 : ∀ k : ℕ, 2 * ((k + 2) * (3 * k + 5) / 2) = (k + 2) * (3 * k + 5) := by
    intro k
    have h : (k + 2) * (3 * k + 5) % 2 = 0 := by
      rw [Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [show (k + 2) % 2 = 0 by omega, zero_mul, Nat.zero_mod]
      · rw [show (3 * k + 5) % 2 = 0 by omega, mul_zero, Nat.zero_mod]
    have h2 := Nat.div_add_mod ((k + 2) * (3 * k + 5)) 2
    rw [h, add_zero] at h2
    exact h2
  have ev2 : ∀ k : ℕ, 2 * ((k + 1) * (3 * k + 4) / 2) = (k + 1) * (3 * k + 4) := by
    intro k
    have h : (k + 1) * (3 * k + 4) % 2 = 0 := by
      rw [Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [show (3 * k + 4) % 2 = 0 by omega, mul_zero, Nat.zero_mod]
      · rw [show (k + 1) % 2 = 0 by omega, zero_mul, Nat.zero_mod]
    have h2 := Nat.div_add_mod ((k + 1) * (3 * k + 4)) 2
    rw [h, add_zero] at h2
    exact h2
  have ev3 : ∀ k : ℕ, 2 * (3 * (k + 1) * (k + 1 + 1) / 2) = 3 * (k + 1) * (k + 1 + 1) := by
    intro k
    have h : 3 * (k + 1) * (k + 1 + 1) % 2 = 0 := by
      rw [Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [show (k + 1 + 1) % 2 = 0 by omega, mul_zero, Nat.zero_mod]
      · rw [show 3 * (k + 1) % 2 = 0 by omega, zero_mul, Nat.zero_mod]
    have h2 := Nat.div_add_mod (3 * (k + 1) * (k + 1 + 1)) 2
    rw [h, add_zero] at h2
    exact h2
  -- small values
  have v1 : f 1 = 1 := by simpa using fB 0
  have v2 : f 2 = 2 := by simpa using fC 0
  have v3 : f 3 = 3 := by simpa using fD 0
  have v4 : f 4 = 5 := by simpa using fA 0
  have v5 : f 5 = 6 := by simpa using fB 1
  have v6 : f 6 = 7 := by simpa using fC 1
  have v7 : f 7 = 9 := by simpa using fD 1
  have v8 : f 8 = 12 := by simpa using fA 1
  have v9 : f 9 = 13 := by simpa using fB 2
  have v10 : f 10 = 15 := by simpa using fC 2
  have v11 : f 11 = 18 := by simpa using fD 2
  have v12 : f 12 = 22 := by simpa using fA 2
  -- f is strictly increasing
  have hmono : StrictMono f := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    obtain ⟨k, rfl | rfl | rfl | rfl⟩ :
        ∃ k, n = 4 * k ∨ n = 4 * k + 1 ∨ n = 4 * k + 2 ∨ n = 4 * k + 3 := ⟨n / 4, by omega⟩
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        norm_num [f0, v1]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [show 4 * (j + 1) = 4 * j + 4 by ring, show 4 * j + 4 + 1 = 4 * (j + 1) + 1 by ring,
          fA j, fB (j + 1)]
        have e := ev1 j
        have r : 3 * (j + 1 + 1) ^ 2 = (j + 2) * (3 * j + 5) + (j + 2) := by ring
        generalize (j + 2) * (3 * j + 5) = A at e r ⊢
        generalize (j + 1 + 1) ^ 2 = Q at r ⊢
        omega
    · rw [show 4 * k + 1 + 1 = 4 * k + 2 by ring, fB k, fC k]
      have e := ev2 k
      have r : (k + 1) * (3 * k + 4) = 3 * (k + 1) ^ 2 + (k + 1) := by ring
      generalize (k + 1) * (3 * k + 4) = A at e r ⊢
      generalize (k + 1) ^ 2 = Q at r ⊢
      omega
    · rw [show 4 * k + 2 + 1 = 4 * k + 3 by ring, fC k, fD k]
      have e := ev2 k
      have e' := ev3 k
      have r : 3 * (k + 1) * (k + 1 + 1) = (k + 1) * (3 * k + 4) + 2 * (k + 1) := by ring
      generalize (k + 1) * (3 * k + 4) = A at e r ⊢
      generalize 3 * (k + 1) * (k + 1 + 1) = B at e' r ⊢
      omega
    · rw [show 4 * k + 3 + 1 = 4 * k + 4 by ring, fD k, fA k]
      have e := ev3 k
      have e' := ev1 k
      have r : (k + 2) * (3 * k + 5) = 3 * (k + 1) * (k + 1 + 1) + 2 * (k + 2) := by ring
      generalize 3 * (k + 1) * (k + 1 + 1) = B at e r ⊢
      generalize (k + 2) * (3 * k + 5) = A at e' r ⊢
      omega
  -- every value of f lies in the union
  have hall : ∀ i, IsGenPent (f i) ∨ IsConcHex (f i) ∨ IsTriMatch (f i) := by
    intro i
    unfold IsGenPent IsConcHex IsTriMatch
    obtain ⟨k, rfl | rfl | rfl | rfl⟩ :
        ∃ k, i = 4 * k ∨ i = 4 * k + 1 ∨ i = 4 * k + 2 ∨ i = 4 * k + 3 := ⟨i / 4, by omega⟩
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        left
        exact ⟨0, by simp [f0]⟩
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        left
        refine ⟨(j : ℤ) + 2, ?_⟩
        rw [show 4 * (j + 1) = 4 * j + 4 by ring, fA j]
        have e := ev1 j
        generalize (j + 2) * (3 * j + 5) / 2 = Y at e ⊢
        have e' : ((2 * Y : ℕ) : ℤ) = (((j + 2) * (3 * j + 5) : ℕ) : ℤ) := by
          rw [e]
        push_cast at e'
        linear_combination e'
    · right
      left
      exact ⟨k + 1, fB k⟩
    · left
      refine ⟨-((k : ℤ) + 1), ?_⟩
      rw [fC k]
      have e := ev2 k
      generalize (k + 1) * (3 * k + 4) / 2 = Y at e ⊢
      have e' : ((2 * Y : ℕ) : ℤ) = (((k + 1) * (3 * k + 4) : ℕ) : ℤ) := by
        rw [e]
      push_cast at e'
      linear_combination e'
    · right
      right
      exact ⟨k + 1, fD k⟩
  -- every element of the union is a value of f
  have h0 : ∀ x, (IsGenPent x ∨ IsConcHex x ∨ IsTriMatch x) → x ∈ Set.range f := by
    intro x hx
    unfold IsGenPent IsConcHex IsTriMatch at hx
    rcases hx with ⟨m, hm⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩
    · obtain ⟨t, rfl | rfl⟩ := Int.eq_nat_or_neg m
      · rcases t with _ | _ | j
        · refine Set.mem_range.mpr ⟨0, ?_⟩
          rw [f0]
          push_cast at hm
          omega
        · refine Set.mem_range.mpr ⟨1, ?_⟩
          rw [v1]
          push_cast at hm
          omega
        · refine Set.mem_range.mpr ⟨4 * j + 4, ?_⟩
          rw [fA j]
          have h2 : ((2 * x : ℕ) : ℤ) = (((j + 2) * (3 * j + 5) : ℕ) : ℤ) := by
            push_cast at hm ⊢
            linear_combination hm
          have h3 : 2 * x = (j + 2) * (3 * j + 5) := by exact_mod_cast h2
          generalize (j + 2) * (3 * j + 5) = A at h3 ⊢
          omega
      · rcases t with _ | j
        · refine Set.mem_range.mpr ⟨0, ?_⟩
          rw [f0]
          push_cast at hm
          omega
        · refine Set.mem_range.mpr ⟨4 * j + 2, ?_⟩
          rw [fC j]
          have h2 : ((2 * x : ℕ) : ℤ) = (((j + 1) * (3 * j + 4) : ℕ) : ℤ) := by
            push_cast at hm ⊢
            linear_combination hm
          have h3 : 2 * x = (j + 1) * (3 * j + 4) := by exact_mod_cast h2
          generalize (j + 1) * (3 * j + 4) = A at h3 ⊢
          omega
    · rcases n with _ | j
      · exact Set.mem_range.mpr ⟨0, by simp [f0]⟩
      · exact Set.mem_range.mpr ⟨4 * j + 1, fB j⟩
    · rcases n with _ | j
      · exact Set.mem_range.mpr ⟨0, by simp [f0]⟩
      · exact Set.mem_range.mpr ⟨4 * j + 3, fD j⟩
  have hinf : (Set.ofPred (fun x => IsGenPent x ∨ IsConcHex x ∨ IsTriMatch x)).Infinite := by
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hmono.injective)
    rintro _ ⟨i, rfl⟩
    exact hall i
  have ha : ∀ n : ℕ, a n = f n := by
    intro n
    have h : f (Nat.nth (fun i => IsGenPent (f i) ∨ IsConcHex (f i) ∨ IsTriMatch (f i)) n) =
        Nat.nth (fun x => IsGenPent x ∨ IsConcHex x ∨ IsTriMatch x) n :=
      Nat.nth_comp_of_strictMono (p := fun x => IsGenPent x ∨ IsConcHex x ∨ IsTriMatch x)
        (n := n) hmono h0 (fun hfi => absurd hfi hinf)
    rw [Nat.nth_of_forall (fun k _ => hall k)] at h
    exact h.symm
  -- 2 (f(m+8) - f(m)) = 3m + c(m mod 4) for m >= 1
  have D0 : ∀ m, m % 4 = 0 → 1 ≤ m → 2 * f (m + 8) = 2 * f m + (3 * m + 22) := by
    intro m hm hm1
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 4 := ⟨m / 4 - 1, by omega⟩
    rw [show 4 * k + 4 + 8 = 4 * (k + 2) + 4 by ring, fA (k + 2), fA k]
    have e1 := ev1 (k + 2)
    have e2 := ev1 k
    have r : (k + 2 + 2) * (3 * (k + 2) + 5) = (k + 2) * (3 * k + 5) + (12 * k + 34) := by ring
    generalize (k + 2 + 2) * (3 * (k + 2) + 5) = A at e1 r ⊢
    generalize (k + 2) * (3 * k + 5) = B at e2 r ⊢
    omega
  have D1 : ∀ m, m % 4 = 1 → 2 * f (m + 8) = 2 * f m + (3 * m + 21) := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 1 := ⟨m / 4, by omega⟩
    rw [show 4 * k + 1 + 8 = 4 * (k + 2) + 1 by ring, fB (k + 2), fB k,
      show 3 * (k + 2 + 1) ^ 2 = 3 * (k + 1) ^ 2 + 2 * (6 * k + 12) by ring]
    generalize (k + 1) ^ 2 = Q
    omega
  have D2 : ∀ m, m % 4 = 2 → 2 * f (m + 8) = 2 * f m + (3 * m + 20) := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 2 := ⟨m / 4, by omega⟩
    rw [show 4 * k + 2 + 8 = 4 * (k + 2) + 2 by ring, fC (k + 2), fC k]
    have e1 := ev2 (k + 2)
    have e2 := ev2 k
    have r : (k + 2 + 1) * (3 * (k + 2) + 4) = (k + 1) * (3 * k + 4) + (12 * k + 26) := by ring
    generalize (k + 2 + 1) * (3 * (k + 2) + 4) = A at e1 r ⊢
    generalize (k + 1) * (3 * k + 4) = B at e2 r ⊢
    omega
  have D3 : ∀ m, m % 4 = 3 → 2 * f (m + 8) = 2 * f m + (3 * m + 21) := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 3 := ⟨m / 4, by omega⟩
    rw [show 4 * k + 3 + 8 = 4 * (k + 2) + 3 by ring, fD (k + 2), fD k]
    have e1 := ev3 (k + 2)
    have e2 := ev3 k
    have r : 3 * (k + 2 + 1) * (k + 2 + 1 + 1) = 3 * (k + 1) * (k + 1 + 1) + (12 * k + 30) := by
      ring
    generalize 3 * (k + 2 + 1) * (k + 2 + 1 + 1) = A at e1 r ⊢
    generalize 3 * (k + 1) * (k + 1 + 1) = B at e2 r ⊢
    omega
  have hrec : ∀ n : ℕ, 13 ≤ n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) -
      a (n - 4) + a (n - 8) - 2 * a (n - 9) + 2 * a (n - 10) - 2 * a (n - 11) + a (n - 12) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 13 := ⟨n - 13, by omega⟩
    rw [show j + 13 - 1 = j + 4 + 8 by omega, show j + 13 - 2 = j + 3 + 8 by omega,
      show j + 13 - 3 = j + 2 + 8 by omega, show j + 13 - 4 = j + 1 + 8 by omega,
      show j + 13 - 8 = j + 5 by omega, show j + 13 - 9 = j + 4 by omega,
      show j + 13 - 10 = j + 3 by omega, show j + 13 - 11 = j + 2 by omega,
      show j + 13 - 12 = j + 1 by omega, show j + 13 = j + 5 + 8 by omega,
      ha (j + 5 + 8), ha (j + 4 + 8), ha (j + 3 + 8), ha (j + 2 + 8), ha (j + 1 + 8),
      ha (j + 5), ha (j + 4), ha (j + 3), ha (j + 2), ha (j + 1)]
    rcases (by omega : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3) with h | h | h | h
    · have e1 := D1 (j + 1) (by omega)
      have e2 := D2 (j + 2) (by omega)
      have e3 := D3 (j + 3) (by omega)
      have e4 := D0 (j + 4) (by omega) (by omega)
      have e5 := D1 (j + 5) (by omega)
      omega
    · have e1 := D2 (j + 1) (by omega)
      have e2 := D3 (j + 2) (by omega)
      have e3 := D0 (j + 3) (by omega) (by omega)
      have e4 := D1 (j + 4) (by omega)
      have e5 := D2 (j + 5) (by omega)
      omega
    · have e1 := D3 (j + 1) (by omega)
      have e2 := D0 (j + 2) (by omega) (by omega)
      have e3 := D1 (j + 3) (by omega)
      have e4 := D2 (j + 4) (by omega)
      have e5 := D3 (j + 5) (by omega)
      omega
    · have e1 := D0 (j + 1) (by omega) (by omega)
      have e2 := D1 (j + 2) (by omega)
      have e3 := D2 (j + 3) (by omega)
      have e4 := D3 (j + 4) (by omega)
      have e5 := D0 (j + 5) (by omega) (by omega)
      omega
  refine ⟨hrec, ?_⟩
  have e1 : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 + PowerSeries.X) * (PowerSeries.X ^ 4 + 1) * (PowerSeries.X ^ 2 + 1) ^ 2 *
        (PowerSeries.X - 1) ^ 3) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
        + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 8
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 10)
        + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 12
        - PowerSeries.mk (fun n => (a n : ℚ))
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 9)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 11) := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have e2 : (-PowerSeries.X * (1 + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 - PowerSeries.X ^ 4 +
      PowerSeries.X ^ 5 + PowerSeries.X ^ 7 - 2 * PowerSeries.X ^ 8 + PowerSeries.X ^ 11 +
      2 * PowerSeries.X ^ 9 - 2 * PowerSeries.X ^ 10) : PowerSeries ℚ) =
      PowerSeries.X ^ 5 + PowerSeries.X ^ 9 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        + PowerSeries.X ^ 11 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        - PowerSeries.X ^ 1 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4 - PowerSeries.X ^ 6
        - PowerSeries.X ^ 8 - PowerSeries.X ^ 10 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        - PowerSeries.X ^ 12 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  rw [e1, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 13 with hm | hm
  · interval_cases m <;> norm_num [ha, f0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 13 := ⟨m - 13, by omega⟩
    have hz := hrec (k + 13) (by omega)
    rw [if_pos (show 1 ≤ k + 13 by omega), if_pos (show 3 ≤ k + 13 by omega),
      if_pos (show 8 ≤ k + 13 by omega), if_pos (show 10 ≤ k + 13 by omega),
      if_pos (show 12 ≤ k + 13 by omega), if_pos (show 2 ≤ k + 13 by omega),
      if_pos (show 4 ≤ k + 13 by omega), if_pos (show 9 ≤ k + 13 by omega),
      if_pos (show 11 ≤ k + 13 by omega),
      if_neg (show ¬(k + 13 = 5) by omega), if_neg (show ¬(k + 13 = 9) by omega),
      if_neg (show ¬(k + 13 = 11) by omega), if_neg (show ¬(k + 13 = 1) by omega),
      if_neg (show ¬(k + 13 = 3) by omega), if_neg (show ¬(k + 13 = 4) by omega),
      if_neg (show ¬(k + 13 = 6) by omega), if_neg (show ¬(k + 13 = 8) by omega),
      if_neg (show ¬(k + 13 = 10) by omega), if_neg (show ¬(k + 13 = 12) by omega)]
    rw [show k + 13 - 1 = k + 12 by omega, show k + 13 - 2 = k + 11 by omega,
      show k + 13 - 3 = k + 10 by omega, show k + 13 - 4 = k + 9 by omega,
      show k + 13 - 8 = k + 5 by omega, show k + 13 - 9 = k + 4 by omega,
      show k + 13 - 10 = k + 3 by omega, show k + 13 - 11 = k + 2 by omega,
      show k + 13 - 12 = k + 1 by omega] at hz ⊢
    have hq : (a (k + 13) : ℚ) = 2 * a (k + 12) - 2 * a (k + 11) + 2 * a (k + 10) - a (k + 9) +
        a (k + 5) - 2 * a (k + 4) + 2 * a (k + 3) - 2 * a (k + 2) + a (k + 1) := by
      exact_mod_cast hz
    linear_combination (-1 : ℚ) * hq
