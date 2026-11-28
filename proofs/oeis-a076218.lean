import OMAStatements.S_oeis_a076218

-- Problem: A076218: Numbers n such that 2*n^2 - 3*n + 1 is a square.
-- Upstream: formal-conjectures statements/oeis-a076218.lean:0 (declaration OMA.S_oeis_a076218.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if n^2 + b^2 = c^2 with b >= 1, write c = b + 1 + d; then
-- n^2 = 2b(1+d) + (1+d)^2, which gives A055524(2u+1) = 2u^2 + 2u + 1 and, since d must be odd
-- for even n, A055524(2u) = u^2 + 1. Each parity class takes a value at most once, so x occurs
-- twice iff x = k^2 + 1 = 2j^2 + 2j + 1, that is, x - 1 = k^2 and 2x - 1 = (2j+1)^2. And
-- 2x^2 - 3x + 1 = (x - 1)(2x - 1) with coprime factors is a square iff both factors are.

open OMA.S_oeis_a076218 in
theorem OMA.solution : type_of% @OMA.S_oeis_a076218.main := by
  have tri : ∀ n b c : ℕ, 0 < n → n ^ 2 + b ^ 2 = c ^ 2 →
      ∃ d : ℕ, c = b + 1 + d ∧ n ^ 2 = 2 * b * (1 + d) + (1 + d) ^ 2 := by
    intro n b c hn h
    have hbc : b < c := by
      by_contra hcon
      have h1 : c ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : 0 < n ^ 2 := pow_pos hn 2
      omega
    obtain ⟨d, rfl⟩ : ∃ d, c = b + 1 + d := ⟨c - b - 1, by omega⟩
    refine ⟨d, rfl, ?_⟩
    have e : (b + 1 + d) ^ 2 = b ^ 2 + (2 * b * (1 + d) + (1 + d) ^ 2) := by ring
    omega
  have hO : ∀ u : ℕ, 1 ≤ u → A055524 (2 * u + 1) = 2 * u ^ 2 + 2 * u + 1 := by
    intro u hu
    unfold A055524
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨2 * u ^ 2 + 2 * u, by omega, by ring⟩
    · rw [mem_upperBounds]
      rintro c ⟨b, hb, h⟩
      obtain ⟨d, rfl, h2⟩ := tri (2 * u + 1) b c (by omega) h
      have e1 : (2 * u + 1) ^ 2 = 4 * u ^ 2 + 4 * u + 1 := by ring
      have e2 : 2 * b * (1 + d) + (1 + d) ^ 2 = 2 * b + 2 * (b * d) + 1 + 2 * d + d ^ 2 := by
        ring
      omega
  have hE : ∀ u : ℕ, 2 ≤ u → A055524 (2 * u) = u ^ 2 + 1 := by
    intro u hu
    unfold A055524
    apply IsGreatest.csSup_eq
    constructor
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
      refine ⟨w * (w + 2), Nat.mul_pos (by omega) (by omega), by ring⟩
    · rw [mem_upperBounds]
      rintro c ⟨b, hb, h⟩
      obtain ⟨d, rfl, h2⟩ := tri (2 * u) b c (by omega) h
      have e1 : (2 * u) ^ 2 = 4 * u ^ 2 := by ring
      rcases Nat.even_or_odd' d with ⟨e, rfl | rfl⟩
      · exfalso
        have e2 : 2 * b * (1 + 2 * e) + (1 + 2 * e) ^ 2 =
            2 * b + 4 * (b * e) + 1 + 4 * e + 4 * e ^ 2 := by ring
        omega
      · have e2 : 2 * b * (1 + (2 * e + 1)) + (1 + (2 * e + 1)) ^ 2 =
            4 * b + 4 * (b * e) + 4 + 8 * e + 4 * e ^ 2 := by ring
        omega
  have sqinj : ∀ u v : ℕ, u ^ 2 = v ^ 2 → u = v := by
    intro u v h
    rcases lt_trichotomy u v with h1 | h1 | h1
    · have h3 := Nat.pow_lt_pow_left h1 (show 2 ≠ 0 by norm_num)
      omega
    · exact h1
    · have h3 := Nat.pow_lt_pow_left h1 (show 2 ≠ 0 by norm_num)
      omega
  have oinj : ∀ u v : ℕ, 2 * u ^ 2 + 2 * u + 1 = 2 * v ^ 2 + 2 * v + 1 → u = v := by
    intro u v h
    rcases lt_trichotomy u v with h1 | h1 | h1
    · have h3 := Nat.pow_lt_pow_left h1 (show 2 ≠ 0 by norm_num)
      omega
    · exact h1
    · have h3 := Nat.pow_lt_pow_left h1 (show 2 ≠ 0 by norm_num)
      omega
  intro x hx
  have key : ∀ k j : ℕ, x = k ^ 2 + 1 → x = 2 * j ^ 2 + 2 * j + 1 → IsTerm x := by
    intro k j hk hj
    refine ⟨(2 * (j : ℤ) + 1) * k, ?_⟩
    have hk' : (x : ℤ) = (k : ℤ) ^ 2 + 1 := by exact_mod_cast hk
    have hj' : (x : ℤ) = 2 * (j : ℤ) ^ 2 + 2 * j + 1 := by exact_mod_cast hj
    linear_combination (2 * (x : ℤ) - 1) * hk' + 2 * (k : ℤ) ^ 2 * hj'
  constructor
  · intro h2
    obtain ⟨t1, t2, hne, hS⟩ := Set.ncard_eq_two.mp h2
    have m1 : 3 ≤ t1 ∧ A055524 t1 = x := by
      have h3 : t1 ∈ {t : ℕ | 3 ≤ t ∧ A055524 t = x} := by
        rw [hS]
        exact Set.mem_insert t1 {t2}
      exact h3
    have m2 : 3 ≤ t2 ∧ A055524 t2 = x := by
      have h3 : t2 ∈ {t : ℕ | 3 ≤ t ∧ A055524 t = x} := by
        rw [hS]
        exact Set.mem_insert_of_mem t1 (Set.mem_singleton t2)
      exact h3
    obtain ⟨m1a, m1b⟩ := m1
    obtain ⟨m2a, m2b⟩ := m2
    rcases Nat.even_or_odd' t1 with ⟨u1, rfl | rfl⟩
    · rw [hE u1 (by omega)] at m1b
      rcases Nat.even_or_odd' t2 with ⟨u2, rfl | rfl⟩
      · exfalso
        rw [hE u2 (by omega)] at m2b
        have h4 := sqinj u1 u2 (by omega)
        omega
      · rw [hO u2 (by omega)] at m2b
        exact key u1 u2 m1b.symm m2b.symm
    · rw [hO u1 (by omega)] at m1b
      rcases Nat.even_or_odd' t2 with ⟨u2, rfl | rfl⟩
      · rw [hE u2 (by omega)] at m2b
        exact key u2 u1 m2b.symm m1b.symm
      · exfalso
        rw [hO u2 (by omega)] at m2b
        have h4 := oinj u1 u2 (by omega)
        omega
  · intro hT
    obtain ⟨s, hs⟩ := hT
    have hprod : ((x : ℤ) - 1) * (2 * x - 1) = s ^ 2 := by linear_combination hs
    have hprod' : (2 * (x : ℤ) - 1) * (x - 1) = s ^ 2 := by linear_combination hs
    have hcop : IsCoprime ((x : ℤ) - 1) (2 * x - 1) := ⟨-2, 1, by ring⟩
    obtain ⟨k0, hk0⟩ := Int.sq_of_isCoprime hcop hprod
    obtain ⟨m0, hm0⟩ := Int.sq_of_isCoprime hcop.symm hprod'
    have hx1 : (2 : ℤ) ≤ x := by exact_mod_cast hx
    have hk : (x : ℤ) - 1 = k0 ^ 2 := by
      rcases hk0 with h | h
      · exact h
      · exfalso
        have h5 := sq_nonneg k0
        linarith
    have hm : 2 * (x : ℤ) - 1 = m0 ^ 2 := by
      rcases hm0 with h | h
      · exact h
      · exfalso
        have h5 := sq_nonneg m0
        linarith
    obtain ⟨k, hkk⟩ : ∃ k : ℕ, (k : ℤ) ^ 2 = k0 ^ 2 := ⟨k0.natAbs, Int.natAbs_sq k0⟩
    obtain ⟨m, hmm⟩ : ∃ m : ℕ, (m : ℤ) ^ 2 = m0 ^ 2 := ⟨m0.natAbs, Int.natAbs_sq m0⟩
    have hxk : x = k ^ 2 + 1 := by
      have h1 : (x : ℤ) = (k : ℤ) ^ 2 + 1 := by linarith
      exact_mod_cast h1
    have hxm : 2 * x = m ^ 2 + 1 := by
      have h1 : 2 * (x : ℤ) = (m : ℤ) ^ 2 + 1 := by linarith
      exact_mod_cast h1
    obtain ⟨j, hj⟩ : ∃ j, m = 2 * j + 1 := by
      rcases Nat.even_or_odd' m with ⟨e, rfl | rfl⟩
      · exfalso
        have e1 : (2 * e) ^ 2 = 4 * e ^ 2 := by ring
        omega
      · exact ⟨e, rfl⟩
    rw [hj] at hxm
    have hxj : x = 2 * j ^ 2 + 2 * j + 1 := by
      have e1 : (2 * j + 1) ^ 2 = 4 * j ^ 2 + 4 * j + 1 := by ring
      omega
    have hj1 : 1 ≤ j := by
      by_contra hcon
      have hj0 : j = 0 := by omega
      subst hj0
      norm_num at hxj
      omega
    have hk2 : 2 ≤ k := by
      by_contra hcon
      have h1 : k ^ 2 ≤ 1 := by
        have h6 := Nat.pow_le_pow_left (show k ≤ 1 by omega) 2
        rwa [one_pow] at h6
      omega
    have hset : {t : ℕ | 3 ≤ t ∧ A055524 t = x} = {2 * k, 2 * j + 1} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ht, hAt⟩
        rcases Nat.even_or_odd' t with ⟨u, rfl | rfl⟩
        · left
          rw [hE u (by omega)] at hAt
          have h7 := sqinj u k (by omega)
          omega
        · right
          rw [hO u (by omega)] at hAt
          have h7 := oinj u j (by omega)
          omega
      · rintro (rfl | rfl)
        · refine ⟨by omega, ?_⟩
          rw [hE k hk2]
          omega
        · refine ⟨by omega, ?_⟩
          rw [hO j hj1]
          omega
    rw [hset]
    exact Set.ncard_pair (by omega)
