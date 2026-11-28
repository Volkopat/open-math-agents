import OMAStatements.S_oeis_a261702

-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)

open OMA.S_oeis_a261702

theorem exists_elig (s : Finset ℕ) : ∃ k, eligible s k := by
  by_cases h1 : 1 ∈ s
  · have hex : ∃ j : ℕ, 2 ^ j ∉ s := by
      by_contra hcon
      push Not at hcon
      have hinj : Function.Injective (fun j : ℕ => 2 ^ j) := Nat.pow_right_injective le_rfl
      exact Set.infinite_range_of_injective hinj (s.finite_toSet.subset (by rintro _ ⟨j, rfl⟩; exact hcon j))
    classical
    let j := Nat.find hex
    have hj : 2 ^ j ∉ s := Nat.find_spec hex
    have hj0 : j ≠ 0 := by
      intro h0
      apply hj
      rw [h0]
      simpa using h1
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hmem : 2 ^ i ∈ s := by
      by_contra hn
      have := Nat.find_min hex (show i < j by omega)
      exact this hn
    refine ⟨2 ^ j, by positivity, hj, Or.inr ?_⟩
    have : step (2 ^ j) = 2 ^ i := by
      unfold step
      rw [hi, pow_succ]
      have : (2 ^ i * 2) % 2 = 0 := by simp
      rw [if_pos this]
      omega
    rw [this]; exact hmem
  · exact ⟨1, by norm_num, h1, Or.inl rfl⟩

theorem pick_elig (s : Finset ℕ) : eligible s (pick s) := by
  classical
  unfold pick
  rw [dif_pos (exists_elig s)]
  exact Nat.find_spec (exists_elig s)

theorem pick_le (s : Finset ℕ) (k : ℕ) (hk : eligible s k) : pick s ≤ k := by
  classical
  unfold pick
  rw [dif_pos ⟨k, hk⟩]
  exact Nat.find_min' _ hk

theorem seen_succ (n : ℕ) : seen (n+1) = insert (term n) (seen n) := rfl

theorem seen_mono {n m : ℕ} (h : n ≤ m) : seen n ⊆ seen m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [seen_succ]; exact Finset.subset_insert _ _)

theorem term_notin (n : ℕ) : term n ∉ seen n := (pick_elig (seen n)).2.1

theorem term_pos (n : ℕ) : 0 < term n := (pick_elig (seen n)).1

theorem term_mem {n m : ℕ} (h : n < m) : term n ∈ seen m := by
  apply seen_mono h
  rw [seen_succ]; exact Finset.mem_insert_self _ _

theorem term_inj : Function.Injective term := by
  have key : ∀ a b, a < b → term a ≠ term b := by
    intro a b hab h
    have := term_mem hab
    rw [h] at this
    exact term_notin b this
  intro a b h
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact absurd h (key a b h1)
  · exact h1
  · exact absurd h.symm (key b a h1)

theorem mem_seen : ∀ n k, k ∈ seen n → ∃ m, term m = k := by
  intro n
  induction n with
  | zero => intro k hk; simp [seen] at hk
  | succ n ih =>
    intro k hk
    rw [seen_succ, Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact ⟨n, rfl⟩
    · exact ih k hk

theorem hit (k : ℕ) (hk : 0 < k) (N : ℕ) (h : ∀ n, N ≤ n → (k = 1 ∨ step k ∈ seen n)) :
    ∃ m, term m = k := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ n, N ≤ n → term n ≤ k := by
    intro n hn
    apply pick_le
    refine ⟨hk, ?_, h n hn⟩
    intro hm
    obtain ⟨m, hm'⟩ := mem_seen n k hm
    exact hcon m hm'
  have hinf : (Set.Icc 1 k).Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun n => term (n + N))
    · intro a b hab
      have := term_inj hab
      omega
    · intro n
      exact ⟨term_pos _, hall _ (by omega)⟩
  exact hinf (Set.finite_Icc 1 k)

theorem step_pos (k : ℕ) (hk : 0 < k) : 0 < step k := by
  unfold step
  split_ifs <;> omega

theorem reach_term (k : ℕ) (hr : ReachesOne k) : 0 < k → ∃ n, term n = k := by
  induction hr with
  | one => intro _; exact hit 1 (by norm_num) 0 (fun n _ => Or.inl rfl)
  | @back k hr ih =>
    intro hk
    obtain ⟨m, hm⟩ := ih (step_pos k hk)
    refine hit k hk (m+1) (fun n hn => Or.inr ?_)
    apply seen_mono hn
    rw [← hm]
    exact term_mem (Nat.lt_succ_self m)

theorem OMA.solution : type_of% @OMA.S_oeis_a261702.main := by
  intro hC
  exact ⟨term_inj, term_pos, fun k hk => reach_term k (hC k hk) hk⟩
