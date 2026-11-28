import OMAStatements.S_oeis_a256012

namespace OMA.P_oeis_a256012

/-- A multiple of `4` is not squarefree. -/
theorem not_squarefree_of_four_dvd {k : ℕ} (hk : 4 ∣ k) : ¬ Squarefree k := by
  intro h
  have h2 : (2 : ℕ) * 2 ∣ k := by simpa using hk
  have := Nat.isUnit_iff.mp (h 2 h2)
  omega

/-- A multiple of `9` is not squarefree. -/
theorem not_squarefree_of_nine_dvd {k : ℕ} (hk : 9 ∣ k) : ¬ Squarefree k := by
  intro h
  have h3 : (3 : ℕ) * 3 ∣ k := by simpa using hk
  have := Nat.isUnit_iff.mp (h 3 h3)
  omega

/-- A one-part witness. -/
theorem mem_single {n : ℕ} (hn : 1 ≤ n) (hns : ¬ Squarefree n) :
    ({n} : Finset ℕ) ∈ (Finset.Icc 1 n).powerset.filter
      fun s => (∀ k ∈ s, ¬ Squarefree k) ∧ ∑ k ∈ s, k = n := by
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff,
    Finset.mem_Icc, Finset.mem_singleton, forall_eq, Finset.sum_singleton]
  exact ⟨⟨hn, le_refl n⟩, hns, by trivial⟩

/-- A two-part witness. -/
theorem mem_pair {n x y : ℕ} (hxy : x ≠ y) (hx : 1 ≤ x) (hy : 1 ≤ y) (hs : x + y = n)
    (hnx : ¬ Squarefree x) (hny : ¬ Squarefree y) :
    ({x, y} : Finset ℕ) ∈ (Finset.Icc 1 n).powerset.filter
      fun s => (∀ k ∈ s, ¬ Squarefree k) ∧ ∑ k ∈ s, k = n := by
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [Finset.mem_Icc]
    rcases hk with rfl | rfl <;> omega
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hnx
    · exact hny
  · rw [Finset.sum_pair hxy]
    exact hs

end OMA.P_oeis_a256012

open OMA.P_oeis_a256012 in
theorem OMA.solution : type_of% @OMA.S_oeis_a256012.main := by
  intro n hn
  unfold OMA.S_oeis_a256012.a
  apply Finset.card_pos.mpr
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · -- n ≡ 0 (mod 4): the single part n
    exact ⟨{n}, mem_single (by omega) (not_squarefree_of_four_dvd (by omega))⟩
  · -- n ≡ 1 (mod 4): parts 9 and n - 9
    exact ⟨{9, n - 9}, mem_pair (by omega) (by omega) (by omega) (by omega)
      (not_squarefree_of_nine_dvd (by norm_num)) (not_squarefree_of_four_dvd (by omega))⟩
  · -- n ≡ 2 (mod 4): parts 18 and n - 18
    exact ⟨{18, n - 18}, mem_pair (by omega) (by omega) (by omega) (by omega)
      (not_squarefree_of_nine_dvd (by norm_num)) (not_squarefree_of_four_dvd (by omega))⟩
  · -- n ≡ 3 (mod 4): the single part 27 if n = 27, else parts 27 and n - 27
    by_cases h27 : n = 27
    · subst h27
      exact ⟨{27}, mem_single (by norm_num) (not_squarefree_of_nine_dvd (by norm_num))⟩
    · exact ⟨{27, n - 27}, mem_pair (by omega) (by omega) (by omega) (by omega)
        (not_squarefree_of_nine_dvd (by norm_num)) (not_squarefree_of_four_dvd (by omega))⟩
