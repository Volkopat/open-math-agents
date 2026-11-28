import OMAStatements.S_oeis_a389425

namespace OMA.S_oeis_a389425

open Filter Topology

lemma good_prog (i : ℕ) : eligible (35*i + 16) := by
  have h7 : 7 ∣ 6*(35*i + 16)-5 := ⟨30*i+13, by omega⟩
  have h5 : 5 ∣ 6*(35*i + 16)-1 := ⟨42*i+19, by omega⟩
  exact ⟨by omega, Nat.not_prime_of_dvd_of_lt h7 (by decide) (by omega),
    by omega, Nat.not_prime_of_dvd_of_lt h5 (by decide) (by omega)⟩

lemma eligible_inf : (Set.ofPred eligible).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 35*i+16)
    (fun x y h => by change 35*x+16 = 35*y+16 at h; omega) good_prog

lemma term_le (i : ℕ) : term i ≤ 35*i+16 := by
  apply Nat.nth_le_of_strictMonoOn_of_mapsTo (fun j : ℕ => 35*j+16)
  · exact fun j _ => good_prog j
  · intro x _ y _ h
    change 35*x+16 < 35*y+16
    omega

lemma monotone_term : StrictMono term := Nat.nth_strictMono eligible_inf

lemma next_of_eligible (i : ℕ) (h : eligible (term i + 1)) : term (i+1) = term i+1 := by
  classical
  have hc := Nat.count_nth_succ_of_infinite eligible_inf i
  change Nat.count eligible (term i + 1) = i+1 at hc
  rw [← hc]
  exact Nat.nth_count h

noncomputable def witnessPrime (i : ℕ) : ℕ :=
  if (6*term i+1).Prime then 6*term i+1 else 6*term i+5

lemma witness_bounds (i : ℕ) :
    6*term i+1 ≤ witnessPrime i ∧ witnessPrime i ≤ 6*term i+5 := by
  unfold witnessPrime
  split <;> omega

lemma prime_on_gap {i : ℕ} (h : term (i+1) - term i ≠ 1) : (witnessPrime i).Prime := by
  have ht := Nat.nth_mem_of_infinite eligible_inf i
  change eligible (term i) at ht
  obtain ⟨hmin, _, _, _⟩ := ht
  unfold witnessPrime
  split_ifs with hp
  · exact hp
  · by_contra hq
    have hgood : eligible (term i+1) := by
      unfold eligible
      rw [show 6*(term i+1)-5 = 6*term i+1 by omega,
        show 6*(term i+1)-1 = 6*term i+5 by omega]
      exact ⟨by omega, hp, by omega, hq⟩
    have he := next_of_eligible i hgood
    omega

lemma exceptional_bound (N : ℕ) :
    N - units N ≤ Nat.primeCounting (400*N) := by
  classical
  let gaps := (Finset.range N).filter (fun i => term (i+1)-term i ≠ 1)
  have hsplit : gaps.card + units N = N := by
    unfold units
    dsimp [gaps]
    simpa [add_comm] using (Finset.card_filter_add_card_filter_not
      (s := Finset.range N) (p := fun i => term (i+1)-term i = 1))
  have hcount : Nat.primeCounting (400*N) =
      ((Finset.range (400*N+1)).filter Nat.Prime).card := Nat.count_eq_card_filter_range _ _
  rw [hcount, show N - units N = gaps.card by omega]
  apply Finset.card_le_card_of_injOn witnessPrime
  · intro i hi
    obtain ⟨hiN, hg⟩ := Finset.mem_filter.mp hi
    have hlt := Finset.mem_range.mp hiN
    have hb := (witness_bounds i).2
    have hv := term_le i
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), prime_on_gap hg⟩
  · intro i _ j _ he
    have hi := witness_bounds i
    have hj := witness_bounds j
    rcases lt_trichotomy i j with h | h | h
    · have := monotone_term h
      omega
    · exact h
    · have := monotone_term h
      omega

lemma prime_ratio : Tendsto (fun N : ℕ => (Nat.primeCounting (400*N) : ℝ) / N) atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ => (400 : ℝ) * N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp hx
  have hlim : Tendsto (fun N : ℕ => ((Real.log 4+1)*400) / Real.log (400*(N:ℝ)))
      atTop (𝓝 0) := hlog.const_div_atTop _
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ hlim
  have hcheb := hx.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  filter_upwards [hcheb, eventually_ge_atTop 1] with n hc hn
  have hpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfloor : ⌊400*(n:ℝ)⌋₊ = 400*n := by
    exact_mod_cast Nat.floor_natCast (400*n)
  rw [hfloor] at hc
  apply (div_le_iff₀ hpos).2
  calc
    _ ≤ (Real.log 4 + 1) * (400*(n:ℝ)) / Real.log (400*(n:ℝ)) := hc
    _ = _ := by ring

theorem solution : Tendsto (fun N : ℕ => (units N : ℝ) / N) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n : ℕ => 1 - (Nat.primeCounting (400*n) : ℝ)/n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub prime_ratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hu : units n ≤ n := by
      classical
      exact (Finset.card_filter_le ..).trans_eq (Finset.card_range _)
    have hb := exceptional_bound n
    have hz : (n:ℝ) - units n ≤ Nat.primeCounting (400*n) := by
      have hh : ((n - units n : ℕ) : ℝ) ≤ Nat.primeCounting (400*n) := by exact_mod_cast hb
      rwa [Nat.cast_sub hu] at hh
    have hpos : 0 < (n : ℝ) := by exact_mod_cast hn
    apply (le_div_iff₀ hpos).2
    rw [sub_mul, div_mul_cancel₀ _ hpos.ne']
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hu : units n ≤ n := by
      classical
      exact (Finset.card_filter_le ..).trans_eq (Finset.card_range _)
    apply (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ) < n)).2
    simpa using (show (units n : ℝ) ≤ n by exact_mod_cast hu)

end OMA.S_oeis_a389425

theorem OMA.solution : type_of% @OMA.S_oeis_a389425.main :=
  OMA.S_oeis_a389425.solution
