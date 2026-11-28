import OMAStatements.S_oeis_a277223

namespace OMA.P_oeis_a277223

open OMA.S_oeis_a277223

/-- Digit sum with explicit fuel, by structural recursion (kernel friendly). -/
def dsF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, m => m % 10 + dsF f (m / 10)

theorem digitsum_step (m : ℕ) : digitsum m = m % 10 + digitsum (m / 10) := by
  unfold digitsum
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp
  · rw [Nat.digits_def' (by norm_num) h, List.sum_cons]

theorem digitsum_eq_dsF : ∀ f m : ℕ, m < 10 ^ f → digitsum m = dsF f m
  | 0, m, h => by
    have hm : m = 0 := by simpa using h
    subst hm
    simp [digitsum, dsF]
  | f + 1, m, h => by
    rw [digitsum_step, dsF, digitsum_eq_dsF f (m / 10)]
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    rw [pow_succ] at h
    exact h

/-- The counterexample. -/
def N : ℕ := 8181818181818181818181818181818181818181818181818182

theorem N_lt : N < 10 ^ 52 := by
  unfold N
  norm_num

theorem bound_N_le : bound N ≤ 972 := by
  unfold bound
  have h : (Nat.digits 10 N).length ≤ 52 :=
    (Nat.digits_length_le_iff (by norm_num) N).mpr N_lt
  omega

theorem check_dsF : ∀ k < 961, dsF 60 ((k + 12) * N) ≠ k + 12 := by
  unfold N
  decide +kernel

theorem no_large (k : ℕ) (h12 : 12 ≤ k) (hk : k ≤ 972) : digitsum (k * N) ≠ k := by
  have hlt : k * N < 10 ^ 60 := by
    have := N_lt
    calc k * N < 973 * 10 ^ 52 := by
          have : k * N ≤ 972 * N := Nat.mul_le_mul_right N hk
          omega
      _ ≤ 10 ^ 60 := by norm_num
  rw [digitsum_eq_dsF 60 _ hlt]
  have := check_dsF (k - 12) (by omega)
  rwa [Nat.sub_add_cancel h12] at this

theorem digitsum_11N : digitsum (11 * N) = 11 := by
  rw [digitsum_eq_dsF 60 _ (by unfold N; norm_num)]
  unfold N
  decide +kernel

theorem a_N : a N = 11 := by
  unfold a
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    show k ≤ 11
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkb, hkd⟩ := hk
    have hb := bound_N_le
    by_contra hcon
    exact no_large k (by omega) (by omega) hkd
  · have hmem : 11 ∈ (Finset.range (bound N + 1)).filter fun k => digitsum (k * N) = k := by
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, digitsum_11N⟩
      unfold bound
      omega
    exact Finset.le_sup (f := id) hmem

end OMA.P_oeis_a277223

open OMA.P_oeis_a277223 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a277223.main) := by
  intro h
  have hN : 1 ≤ N := by unfold N; norm_num
  have := h N hN (by rw [a_N]; norm_num)
  rw [a_N] at this
  omega
