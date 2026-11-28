import OMAStatements.S_oeis_a253238

-- Disproof at n = 10404 = 102^2 > 3319: a(10404) = 1, the only representation being
-- 10404 = 7^3 + 10061. For a square q = x^2 < 10404 the difference 10404 - x^2 =
-- (102 - x)(102 + x) is composite (also for x = 101: 203 = 7 * 29); for q = m^k with k odd,
-- k >= 3, one has m <= 21 and k <= 13, and every case other than 7^3 gives a composite
-- difference. (The OEIS entry also records a(1771561) = 0 against the weaker conjecture.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a253238.main) := by
  intro h
  have h1 := h 10404 (by norm_num)
  have hsub : {q : ℕ | q < 10404 ∧ (∃ m k : ℕ, 2 ≤ m ∧ 2 ≤ k ∧ m ^ k = q) ∧
      (10404 - q).Prime} ⊆ {343} := by
    rintro q ⟨hq, ⟨m, k, hm, hk, rfl⟩, hp⟩
    simp only [Set.mem_singleton_iff]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exfalso
      have hx : m ^ (j + j) = (m ^ j) ^ 2 := by ring
      rw [hx] at hq hp
      generalize m ^ j = x at hq hp
      have hx2 : x ≤ 101 := by nlinarith
      interval_cases x <;> (revert hp; norm_num)
    · have hm21 : m ≤ 21 := by
        by_contra hc
        push_neg at hc
        have h3 : 22 ^ 3 ≤ m ^ (2 * j + 1) :=
          calc 22 ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left hc 3
            _ ≤ m ^ (2 * j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        norm_num at h3
        omega
      have hk13 : 2 * j + 1 ≤ 13 := by
        by_contra hc
        push_neg at hc
        have h14 : 2 ^ 14 ≤ m ^ (2 * j + 1) :=
          calc 2 ^ 14 ≤ 2 ^ (2 * j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ ≤ m ^ (2 * j + 1) := Nat.pow_le_pow_left hm _
        norm_num at h14
        omega
      have hj6 : j ≤ 6 := by omega
      have hj1 : 1 ≤ j := by omega
      interval_cases m <;> interval_cases j <;> (revert hq hp; norm_num)
  have hle : {q : ℕ | q < 10404 ∧ (∃ m k : ℕ, 2 ≤ m ∧ 2 ≤ k ∧ m ^ k = q) ∧
      (10404 - q).Prime}.ncard ≤ 1 := by
    calc _ ≤ ({343} : Set ℕ).ncard := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      _ = 1 := Set.ncard_singleton _
  unfold OMA.S_oeis_a253238.a at h1
  omega
