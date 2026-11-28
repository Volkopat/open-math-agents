import OMAStatements.S_oeis_a073608

namespace BC4A

open OMA.S_oeis_a073608

noncomputable def T (m : ℕ) : Set ℕ :=
  {x : ℕ | ∀ k (hk : k < m + 1), ∀ v : ℕ, seq k = some v → v < x ∧ IsPrimePow (x - v)}

theorem mem_T {m x : ℕ} :
    x ∈ T m ↔ ∀ k, k < m + 1 → ∀ v : ℕ, seq k = some v → v < x ∧ IsPrimePow (x - v) :=
  Iff.rfl

theorem seq_zero : seq 0 = some 1 := by
  first
  | (rw [seq, Nat.strongRecOn, WellFounded.fix_eq] <;> rfl)
  | (unfold seq Nat.strongRecOn; rw [WellFounded.fix_eq] <;> rfl)
  | (simp only [seq, Nat.strongRecOn]; rw [WellFounded.fix_eq] <;> rfl)

theorem seq_succ_pos (m : ℕ) (h : (∀ k, k < m + 1 → (seq k).isSome) ∧ (T m).Nonempty) :
    seq (m + 1) = some (sInf (T m)) := by
  first
  | rw [seq, Nat.strongRecOn, WellFounded.fix_eq]
  | (unfold seq Nat.strongRecOn; rw [WellFounded.fix_eq])
  | (simp only [seq, Nat.strongRecOn]; rw [WellFounded.fix_eq])
  first
  | exact if_pos h
  | (dsimp only; split_ifs with hc <;> first | rfl | exact absurd h hc)
  | (simp only []; split_ifs with hc <;> first | rfl | exact absurd h hc)

theorem seq_succ_neg (m : ℕ) (h : ¬ ((∀ k, k < m + 1 → (seq k).isSome) ∧ (T m).Nonempty)) :
    seq (m + 1) = none := by
  first
  | rw [seq, Nat.strongRecOn, WellFounded.fix_eq]
  | (unfold seq Nat.strongRecOn; rw [WellFounded.fix_eq])
  | (simp only [seq, Nat.strongRecOn]; rw [WellFounded.fix_eq])
  first
  | exact if_neg h
  | (dsimp only; split_ifs with hc <;> first | rfl | exact absurd hc h)
  | (simp only []; split_ifs with hc <;> first | rfl | exact absurd hc h)

theorem get_val {k v c : ℕ} (hc : seq k = some c) (hv : seq k = some v) : v = c := by
  rw [hc] at hv
  exact (Option.some.inj hv).symm

theorem some_of_eq {k c : ℕ} (hc : seq k = some c) : (seq k).isSome := by
  simp [hc]

theorem not_pp_mod4 (n : ℕ) (h4 : n % 4 = 2) (h2 : 2 < n) : ¬ IsPrimePow n := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, rfl⟩
  have h2p : 2 ∣ p ^ k := by omega
  have hp2 : p = 2 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2p)).symm
  subst hp2
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases j with _ | j
  · norm_num at h2
  · have h4d : 4 ∣ 2 ^ (j + 1 + 1) := ⟨2 ^ j, by ring⟩
    omega

theorem pp_two : IsPrimePow (2 : ℕ) := Nat.prime_two.isPrimePow
theorem pp_three : IsPrimePow (3 : ℕ) := Nat.prime_three.isPrimePow
theorem pp_four : IsPrimePow (4 : ℕ) := ⟨2, 2, Nat.prime_two.prime, by norm_num, by norm_num⟩
theorem pp_five : IsPrimePow (5 : ℕ) := Nat.Prime.isPrimePow (by norm_num)
theorem pp_seven : IsPrimePow (7 : ℕ) := Nat.Prime.isPrimePow (by norm_num)
theorem pp_nine : IsPrimePow (9 : ℕ) := ⟨3, 2, Nat.prime_three.prime, by norm_num, by norm_num⟩
theorem pp_eleven : IsPrimePow (11 : ℕ) := Nat.Prime.isPrimePow (by norm_num)
theorem npp_one : ¬ IsPrimePow (1 : ℕ) := not_isPrimePow_one
theorem npp_six : ¬ IsPrimePow (6 : ℕ) := not_pp_mod4 6 (by norm_num) (by norm_num)
theorem npp_ten : ¬ IsPrimePow (10 : ℕ) := not_pp_mod4 10 (by norm_num) (by norm_num)

/- seq 1 = 3 -/
theorem all0 : ∀ k, k < 0 + 1 → (seq k).isSome := by
  intro k hk
  obtain rfl : k = 0 := by omega
  exact some_of_eq seq_zero

theorem mem0 : 3 ∈ T 0 := by
  rw [mem_T]
  intro k hk v hv
  obtain rfl : k = 0 := by omega
  obtain rfl := get_val seq_zero hv
  exact ⟨by norm_num, pp_two⟩

theorem low0 : ∀ x, x ∈ T 0 → 3 ≤ x := by
  intro x hx
  rw [mem_T] at hx
  have h0 := hx 0 (by norm_num) 1 seq_zero
  have h0' : 1 < x := h0.1
  by_contra hlt
  obtain rfl : x = 2 := by omega
  exact npp_one h0.2

theorem inf0 : sInf (T 0) = 3 := by
  first
  | exact le_antisymm (Nat.sInf_le mem0) (low0 _ (Nat.sInf_mem ⟨3, mem0⟩))
  | exact IsLeast.csInf_eq ⟨mem0, fun x hx => low0 x hx⟩

theorem seq_one : seq 1 = some 3 := by
  have h := seq_succ_pos 0 ⟨all0, 3, mem0⟩
  rw [inf0] at h
  exact h

/- seq 2 = 5 -/
theorem all1 : ∀ k, k < 1 + 1 → (seq k).isSome := by
  intro k hk
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · exact some_of_eq seq_zero
  · exact some_of_eq seq_one

theorem mem1 : 5 ∈ T 1 := by
  rw [mem_T]
  intro k hk v hv
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · obtain rfl := get_val seq_zero hv
    exact ⟨by norm_num, pp_four⟩
  · obtain rfl := get_val seq_one hv
    exact ⟨by norm_num, pp_two⟩

theorem low1 : ∀ x, x ∈ T 1 → 5 ≤ x := by
  intro x hx
  rw [mem_T] at hx
  have h1 := hx 1 (by norm_num) 3 seq_one
  have h1' : 3 < x := h1.1
  by_contra hlt
  obtain rfl : x = 4 := by omega
  exact npp_one h1.2

theorem inf1 : sInf (T 1) = 5 := by
  first
  | exact le_antisymm (Nat.sInf_le mem1) (low1 _ (Nat.sInf_mem ⟨5, mem1⟩))
  | exact IsLeast.csInf_eq ⟨mem1, fun x hx => low1 x hx⟩

theorem seq_two : seq 2 = some 5 := by
  have h := seq_succ_pos 1 ⟨all1, 5, mem1⟩
  rw [inf1] at h
  exact h

/- seq 3 = 8 -/
theorem all2 : ∀ k, k < 2 + 1 → (seq k).isSome := by
  intro k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · exact some_of_eq seq_zero
  · exact some_of_eq seq_one
  · exact some_of_eq seq_two

theorem mem2 : 8 ∈ T 2 := by
  rw [mem_T]
  intro k hk v hv
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · obtain rfl := get_val seq_zero hv
    exact ⟨by norm_num, pp_seven⟩
  · obtain rfl := get_val seq_one hv
    exact ⟨by norm_num, pp_five⟩
  · obtain rfl := get_val seq_two hv
    exact ⟨by norm_num, pp_three⟩

theorem low2 : ∀ x, x ∈ T 2 → 8 ≤ x := by
  intro x hx
  rw [mem_T] at hx
  have h0 := hx 0 (by norm_num) 1 seq_zero
  have h2 := hx 2 (by norm_num) 5 seq_two
  have h2' : 5 < x := h2.1
  by_contra hlt
  rcases (show x = 6 ∨ x = 7 by omega) with rfl | rfl
  · exact npp_one h2.2
  · exact npp_six h0.2

theorem inf2 : sInf (T 2) = 8 := by
  first
  | exact le_antisymm (Nat.sInf_le mem2) (low2 _ (Nat.sInf_mem ⟨8, mem2⟩))
  | exact IsLeast.csInf_eq ⟨mem2, fun x hx => low2 x hx⟩

theorem seq_three : seq 3 = some 8 := by
  have h := seq_succ_pos 2 ⟨all2, 8, mem2⟩
  rw [inf2] at h
  exact h

/- seq 4 = 10 -/
theorem all3 : ∀ k, k < 3 + 1 → (seq k).isSome := by
  intro k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · exact some_of_eq seq_zero
  · exact some_of_eq seq_one
  · exact some_of_eq seq_two
  · exact some_of_eq seq_three

theorem mem3 : 10 ∈ T 3 := by
  rw [mem_T]
  intro k hk v hv
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · obtain rfl := get_val seq_zero hv
    exact ⟨by norm_num, pp_nine⟩
  · obtain rfl := get_val seq_one hv
    exact ⟨by norm_num, pp_seven⟩
  · obtain rfl := get_val seq_two hv
    exact ⟨by norm_num, pp_five⟩
  · obtain rfl := get_val seq_three hv
    exact ⟨by norm_num, pp_two⟩

theorem low3 : ∀ x, x ∈ T 3 → 10 ≤ x := by
  intro x hx
  rw [mem_T] at hx
  have h1 := hx 1 (by norm_num) 3 seq_one
  have h3 := hx 3 (by norm_num) 8 seq_three
  have h3' : 8 < x := h3.1
  by_contra hlt
  obtain rfl : x = 9 := by omega
  exact npp_six h1.2

theorem inf3 : sInf (T 3) = 10 := by
  first
  | exact le_antisymm (Nat.sInf_le mem3) (low3 _ (Nat.sInf_mem ⟨10, mem3⟩))
  | exact IsLeast.csInf_eq ⟨mem3, fun x hx => low3 x hx⟩

theorem seq_four : seq 4 = some 10 := by
  have h := seq_succ_pos 3 ⟨all3, 10, mem3⟩
  rw [inf3] at h
  exact h

/- seq 5 = 12 -/
theorem all4 : ∀ k, k < 4 + 1 → (seq k).isSome := by
  intro k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact some_of_eq seq_zero
  · exact some_of_eq seq_one
  · exact some_of_eq seq_two
  · exact some_of_eq seq_three
  · exact some_of_eq seq_four

theorem mem4 : 12 ∈ T 4 := by
  rw [mem_T]
  intro k hk v hv
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · obtain rfl := get_val seq_zero hv
    exact ⟨by norm_num, pp_eleven⟩
  · obtain rfl := get_val seq_one hv
    exact ⟨by norm_num, pp_nine⟩
  · obtain rfl := get_val seq_two hv
    exact ⟨by norm_num, pp_seven⟩
  · obtain rfl := get_val seq_three hv
    exact ⟨by norm_num, pp_four⟩
  · obtain rfl := get_val seq_four hv
    exact ⟨by norm_num, pp_two⟩

theorem low4 : ∀ x, x ∈ T 4 → 12 ≤ x := by
  intro x hx
  rw [mem_T] at hx
  have h0 := hx 0 (by norm_num) 1 seq_zero
  have h4 := hx 4 (by norm_num) 10 seq_four
  have h4' : 10 < x := h4.1
  by_contra hlt
  obtain rfl : x = 11 := by omega
  exact npp_ten h0.2

theorem inf4 : sInf (T 4) = 12 := by
  first
  | exact le_antisymm (Nat.sInf_le mem4) (low4 _ (Nat.sInf_mem ⟨12, mem4⟩))
  | exact IsLeast.csInf_eq ⟨mem4, fun x hx => low4 x hx⟩

theorem seq_five : seq 5 = some 12 := by
  have h := seq_succ_pos 4 ⟨all4, 12, mem4⟩
  rw [inf4] at h
  exact h

/- no sixth term: for x > 12, one of x - 3, x - 5, x - 8, x - 10 is 2 mod 4 and larger than 2 -/
theorem T5_empty : ¬ (T 5).Nonempty := by
  rintro ⟨x, hx⟩
  rw [mem_T] at hx
  have h1 := hx 1 (by norm_num) 3 seq_one
  have h2 := hx 2 (by norm_num) 5 seq_two
  have h3 := hx 3 (by norm_num) 8 seq_three
  have h4 := hx 4 (by norm_num) 10 seq_four
  have h5 := hx 5 (by norm_num) 12 seq_five
  have hx12 : 12 < x := h5.1
  rcases (show (x - 3) % 4 = 2 ∨ (x - 5) % 4 = 2 ∨ (x - 8) % 4 = 2 ∨ (x - 10) % 4 = 2 by omega)
    with h | h | h | h
  · exact not_pp_mod4 _ h (by omega) h1.2
  · exact not_pp_mod4 _ h (by omega) h2.2
  · exact not_pp_mod4 _ h (by omega) h3.2
  · exact not_pp_mod4 _ h (by omega) h4.2

theorem seq_six : seq 6 = none := by
  have h := seq_succ_neg 5 (fun hc => T5_empty hc.2)
  exact h

theorem seq_ge_six (n : ℕ) (hn : 6 ≤ n) : seq n = none := by
  rcases Nat.eq_or_lt_of_le hn with h | h
  · rw [← h]
    exact seq_six
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    apply seq_succ_neg m
    intro hc
    have h6 := hc.1 6 (by omega)
    rw [seq_six] at h6
    simp at h6

theorem bound : ∀ n v : ℕ, seq n = some v → v ≤ 12 := by
  intro n v hv
  rcases Nat.lt_or_ge n 6 with hn | hn
  · rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · have := get_val seq_zero hv
      omega
    · have := get_val seq_one hv
      omega
    · have := get_val seq_two hv
      omega
    · have := get_val seq_three hv
      omega
    · have := get_val seq_four hv
      omega
    · have := get_val seq_five hv
      omega
  · rw [seq_ge_six n hn] at hv
    simp at hv

end BC4A

theorem OMA.solution : type_of% @OMA.S_oeis_a073608.main := ⟨12, BC4A.bound⟩
