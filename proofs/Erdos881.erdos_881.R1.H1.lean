import OMAReductions.R_Erdos881_erdos_881_R1

-- Credit: @Haruzame0
-- The reduction suggests removing a tail of multiples of three.

open Filter Set
open scoped Pointwise

theorem OMA.solution : OMA.R_Erdos881_erdos_881_R1.H1 := by
  intro k A hA hk
  have hk1 : k = 1 := by
    have h0 := hA.1.ne_zero
    omega
  subst k
  have htail : ∀ᶠ n in atTop, n ∈ A := by
    have h := hA.1
    change ∀ᶠ n in Filter.cofinite, n ∈ (1 : ℕ) • A at h
    rw [Filter.cofinite_eq_atTop, one_nsmul] at h
    exact h
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp htail
  let b (t : ℕ) := 3 * (M + t)
  have hb : Function.Injective b := by
    intro t u heq
    change 3 * (M + t) = 3 * (M + u) at heq
    omega
  refine ⟨Set.range b, ?_, Set.infinite_range_of_injective hb, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hM _ (show M ≤ b t by dsimp [b]; omega)
  change ∀ᶠ n in Filter.cofinite, n ∈ (2 : ℕ) • (A \ Set.range b)
  rw [Filter.cofinite_eq_atTop, two_nsmul]
  have hmem (z : ℕ) (hz : M ≤ z) (hz3 : z % 3 ≠ 0) : z ∈ A \ Set.range b := by
    refine ⟨hM z hz, ?_⟩
    rintro ⟨t, rfl⟩
    exact hz3 (by dsimp [b]; omega)
  filter_upwards [eventually_ge_atTop (4 * M + 2)] with n hn
  let x := if n % 3 = 1 then 3 * M + 2 else 3 * M + 1
  have hx : M ≤ x := by dsimp [x]; split <;> omega
  have hx3 : x % 3 ≠ 0 := by dsimp [x]; split <;> omega
  have hy : M ≤ n - x := by dsimp [x]; split <;> omega
  have hy3 : (n - x) % 3 ≠ 0 := by dsimp [x]; split <;> omega
  have hle : x ≤ n := by dsimp [x]; split <;> omega
  exact ⟨x, hmem x hx hx3, n - x, hmem _ hy hy3, Nat.add_sub_of_le hle⟩
