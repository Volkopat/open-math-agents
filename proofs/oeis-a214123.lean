import OMAStatements.S_oeis_a214123

lemma a_eq_one {n : ℕ} (hn : 2 ≤ n) (hp : (2 * n - 1).Prime) : OMA.S_oeis_a214123.a n = 1 := by
  unfold OMA.S_oeis_a214123.a
  have hmem : (1 : ℕ) ∈ {k : ℕ | 0 < k ∧ (n + k * (n - 1)).Prime} := by
    refine ⟨Nat.one_pos, ?_⟩
    have : n + 1 * (n - 1) = 2 * n - 1 := by omega
    rw [this]; exact hp
  have hle := Nat.sInf_le hmem
  have hin := Nat.sInf_mem ⟨1, hmem⟩
  have := hin.1
  omega

lemma a_half {p : ℕ} (hp : p.Prime) (h2 : 2 < p) : OMA.S_oeis_a214123.a ((p + 1) / 2) = 1 := by
  have hodd := hp.eq_two_or_odd
  apply a_eq_one (by omega)
  have : 2 * ((p + 1) / 2) - 1 = p := by omega
  rw [this]; exact hp

theorem OMA.solution : type_of% @OMA.S_oeis_a214123.main := by
  refine ⟨fun n hn hp => a_eq_one hn hp, fun p hp h2 => a_half hp h2, fun htw => ?_⟩
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, ⟨hp, hp2⟩, hpN⟩ := htw.exists_gt (2 * N + 3)
  have hodd := hp.eq_two_or_odd
  refine ⟨(p + 1) / 2, ⟨by omega, a_half hp (by omega), ?_⟩, by omega⟩
  have : (p + 1) / 2 + 1 = (p + 2 + 1) / 2 := by omega
  rw [this]
  exact a_half hp2 (by omega)
