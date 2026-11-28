import OMAStatements.S_oeis_a324298

-- Credit: @oh-meh
open OMA.S_oeis_a324298 Filter Topology

private theorem progression (t : ℕ) : IsTerm (6*t+3) := by
  exact ⟨0,t,by ring⟩

private theorem infinitely_many : (Set.ofPred IsTerm).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  exact ⟨6*n+3, progression n, by omega⟩

private theorem bounded_gap (i : ℕ) :
    Nat.nth IsTerm (i+1) ≤ Nat.nth IsTerm i + 6 := by
  let b := Nat.nth IsTerm i
  let t := (b+3)/6
  have lo : b<6*t+3 := by dsimp [t]; omega
  have hi : 6*t+3≤b+6 := by dsimp [t]; omega
  obtain ⟨j,_,hj⟩ := Nat.exists_lt_card_nth_eq (progression t)
  have hij : i<j := (Nat.nth_lt_nth infinitely_many).mp (hj ▸ lo)
  exact (Nat.nth_monotone infinitely_many hij).trans (hj ▸ hi)

theorem OMA.solution : type_of% @OMA.S_oeis_a324298.main := by
  have hb (n : ℕ) : n-1 ≤ a n := (Nat.nth_strictMono infinitely_many).id_le _
  have ha : Tendsto (fun n : ℕ => (a n:ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    apply tendsto_atTop.mpr
    intro m
    filter_upwards [eventually_ge_atTop (m+1)] with n hn
    exact le_trans (by omega : m≤n-1) (hb n)
  have hlow : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hup : Tendsto (fun n : ℕ => (1:ℝ)+6*(a n:ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using hlow.add ((tendsto_inv_atTop_zero.comp ha).const_mul 6)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup
  all_goals
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : (0:ℝ)<a n := by exact_mod_cast (show 0<a n by have := hb n; omega)
    have hle : (a n:ℝ) ≤ a (n+1) := by
      exact_mod_cast (Nat.nth_monotone infinitely_many (by omega : n-1≤n+1-1))
    have hgap : (a (n+1):ℝ) ≤ a n+6 := by
      have h := bounded_gap (n-1)
      rw [show n-1+1=n+1-1 by omega] at h
      exact_mod_cast h
    first
    | exact (le_div_iff₀ hpos).mpr (by simpa using hle)
    | rw [div_le_iff₀ hpos]; field_simp; linarith
