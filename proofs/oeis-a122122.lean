import OMAStatements.S_oeis_a122122

namespace OMA.P_oeis_a122122

open OMA.S_oeis_a122122

lemma a_succ (j : ℕ) :
    a (j + 1) = ((j : ℚ) + 3) / 8 * (4 : ℚ) ^ (j + 1)
      - ((j : ℚ) + 1) * (4 * (j : ℚ) + 1) / (4 * (2 * (j : ℚ) + 1)) *
        (Nat.centralBinom (j + 1) : ℚ) := by
  unfold a
  rw [if_neg (Nat.succ_ne_zero j), Nat.centralBinom_eq_two_mul_choose]
  have hz : (4 : ℚ) ^ (((j + 1 : ℕ) : ℤ) - 2) = (4 : ℚ) ^ (j + 1) / 16 := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast]
    norm_num
  rw [hz]
  have h1 : (1 : ℚ) - 2 * ((j + 1 : ℕ) : ℚ) ≠ 0 := by
    push_cast
    nlinarith [(j.cast_nonneg : (0 : ℚ) ≤ j)]
  have h2 : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

lemma cb (k : ℕ) :
    (Nat.centralBinom (k + 1) : ℚ) = 2 * (2 * (k : ℚ) + 1) / ((k : ℚ) + 1) *
      (Nat.centralBinom k : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  have h' : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) =
      2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) := by exact_mod_cast h
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  linear_combination h'

end OMA.P_oeis_a122122

theorem OMA.solution : type_of% @OMA.S_oeis_a122122.main := by
  constructor
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    have e : j + 2 - 1 = j + 1 := by omega
    rw [e, show j + 2 + 1 = (j + 2) + 1 by rfl, OMA.P_oeis_a122122.a_succ (j + 2),
      show j + 2 = (j + 1) + 1 by rfl, OMA.P_oeis_a122122.a_succ (j + 1),
      OMA.P_oeis_a122122.a_succ j, OMA.P_oeis_a122122.cb (j + 1 + 1),
      OMA.P_oeis_a122122.cb (j + 1)]
    push_cast
    have h1 : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
    have h2 : (2 * ((j : ℚ) + 1) + 1) ≠ 0 := by positivity
    have h3 : (2 * ((j : ℚ) + 1 + 1) + 1) ≠ 0 := by positivity
    have h4 : ((j : ℚ) + 1 + 1) ≠ 0 := by positivity
    have h5 : ((j : ℚ) + 1 + 1 + 1) ≠ 0 := by positivity
    have h6 : ((j : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have ha : ∀ m : ℕ, OMA.S_oeis_a122122.a (j + m + 1) = ((j : ℚ) + m + 3) / 8 * (4 : ℚ) ^ (j + m + 1)
        - ((j : ℚ) + m + 1) * (4 * ((j : ℚ) + m) + 1) / (4 * (2 * ((j : ℚ) + m) + 1)) *
          (Nat.centralBinom (j + m + 1) : ℚ) := by
      intro m
      rw [OMA.P_oeis_a122122.a_succ (j + m)]
      push_cast
      ring
    have hb : ∀ m : ℕ, (Nat.centralBinom (j + m + 1 + 1) : ℚ) =
        2 * (2 * ((j : ℚ) + m + 1) + 1) / ((j : ℚ) + m + 1 + 1) *
          (Nat.centralBinom (j + m + 1) : ℚ) := by
      intro m
      rw [OMA.P_oeis_a122122.cb (j + m + 1)]
      push_cast
      ring
    rw [show j + 4 - 1 = j + 2 + 1 by omega, show j + 4 - 2 = j + 1 + 1 by omega,
      show j + 4 - 3 = j + 0 + 1 by omega, show j + 4 = j + 3 + 1 by omega,
      show j + 3 + 1 + 1 = j + 4 + 1 by omega]
    rw [ha 4, ha 3, ha 2, ha 1, ha 0]
    rw [show j + 4 + 1 = j + 3 + 1 + 1 by omega, hb 3,
      show j + 3 + 1 = j + 2 + 1 + 1 by omega, hb 2,
      show j + 2 + 1 = j + 1 + 1 + 1 by omega, hb 1,
      show j + 1 + 1 = j + 0 + 1 + 1 by omega, hb 0]
    push_cast
    have h1 : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
    have h2 : (2 * ((j : ℚ) + 1) + 1) ≠ 0 := by positivity
    have h3 : (2 * ((j : ℚ) + 2) + 1) ≠ 0 := by positivity
    have h4 : (2 * ((j : ℚ) + 3) + 1) ≠ 0 := by positivity
    have h5 : (2 * ((j : ℚ) + 4) + 1) ≠ 0 := by positivity
    have h6 : ((j : ℚ) + 1 + 1) ≠ 0 := by positivity
    have h7 : ((j : ℚ) + 1 + 1 + 1) ≠ 0 := by positivity
    have h8 : ((j : ℚ) + 2 + 1 + 1) ≠ 0 := by positivity
    have h9 : ((j : ℚ) + 3 + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring
