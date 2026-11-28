import OMAStatements.S_oeis_a047239

namespace OMA.S_oeis_a047239


theorem a_mod (n : ℕ) (hn : 1 ≤ n) : a n % 6 = 1 ∨ a n % 6 = 2 := by
  unfold a; split_ifs <;> omega

theorem strictMono : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold a
  split_ifs <;> omega

/-- The conjecture: for every `n ≥ 2`, `a(n)` is the least candidate. -/
theorem conjecture (n : ℕ) (hn : 2 ≤ n) : IsLeast {m | Cand n m} (a n) := by
  constructor
  · refine ⟨?_, strictMono (by omega), ?_⟩
    · have := a_mod n (by omega); omega
    · intro i j k hi hij hjk hkn
      have h1 := a_mod i hi
      have h2 := a_mod j (by omega)
      have h3 := a_mod k (by omega)
      have h4 := a_mod n (by omega)
      omega
  · intro m ⟨_, hlo, hno⟩
    by_contra hlt
    push_neg at hlt
    have a1 : a 1 = 1 := rfl
    have a2 : a 2 = 2 := rfl
    rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
    · -- n = 2t: nothing strictly between a(n-1) and a(n)
      have e1 : a (n - 1) = 6 * t - 5 := by
        unfold a; split_ifs <;> omega
      have e2 : a n = 6 * t - 4 := by
        unfold a; split_ifs <;> omega
      omega
    · -- n = 2t+1 with t ≥ 1
      have e0 : a (2 * t - 1) = 6 * t - 5 := by
        unfold a; split_ifs <;> omega
      have e1 : a (2 * t) = 6 * t - 4 := by
        unfold a; split_ifs <;> omega
      have e1' : a (n - 1) = 6 * t - 4 := by rw [show n - 1 = 2 * t by omega, e1]
      have e2 : a n = 6 * t + 1 := by
        unfold a; split_ifs <;> omega
      rw [e1'] at hlo
      rw [e2] at hlt
      have hm : m = 6 * t - 3 ∨ m = 6 * t - 2 ∨ m = 6 * t - 1 ∨ m = 6 * t := by omega
      rcases hm with h | h | h | h
      · exact hno 1 1 (2 * t - 1) le_rfl le_rfl (by omega) (by omega) (by rw [a1, e0]; omega)
      · exact hno 1 1 (2 * t) le_rfl le_rfl (by omega) (by omega) (by rw [a1, e1]; omega)
      · exact hno 1 2 (2 * t) le_rfl (by norm_num) (by omega) (by omega) (by rw [a1, a2, e1]; omega)
      · exact hno 2 2 (2 * t) (by norm_num) le_rfl (by omega) (by omega) (by rw [a2, e1]; omega)

end OMA.S_oeis_a047239

theorem OMA.solution : type_of% @OMA.S_oeis_a047239.main :=
  fun n hn => OMA.S_oeis_a047239.conjecture n hn
