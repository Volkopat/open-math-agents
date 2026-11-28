import OMAStatements.S_oeis_a375852

-- Problem: A375852: Numbers congruent to {0, 1, 3, 6, 7, 9, 12, 15} mod 18.
-- Upstream: formal-conjectures statements/oeis-a375852.lean:0 (declaration OMA.S_oeis_a375852.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: n = 3t+2, n = 6s+4 and n = 18q+13 are impure (explicit preimages 2t+1, 2s+1 and
-- 16q+11 after 2, 1 and 5 steps), so pure numbers have residues in S. The blue numbers of the
-- coloring are exactly the positive pure numbers: an impure n is reached from a least start N0,
-- which is pure, and along a shortest path from N0 to n every iterate exceeds N0.

namespace H15A375852

open OMA.S_oeis_a375852

theorem T_odd (m : ℕ) : T (2 * m + 1) = 6 * m + 4 := by
  unfold T
  rw [if_neg (show ¬ ((2 * m + 1) % 2 = 0) by omega)]
  ring

theorem T_even (m : ℕ) : T (2 * m) = m := by
  unfold T
  rw [if_pos (show (2 * m) % 2 = 0 by omega)]
  omega

theorem T_zero_iter (k : ℕ) : T^[k] 0 = 0 :=
  Function.iterate_fixed (by unfold T; simp) k

theorem not_pure_3 (t : ℕ) : ¬ isPure (3 * t + 2) := by
  intro h
  unfold isPure at h
  have hc : T^[2] (2 * t + 1) = 3 * t + 2 := by
    show T (T (2 * t + 1)) = 3 * t + 2
    rw [T_odd, show 6 * t + 4 = 2 * (3 * t + 2) by ring, T_even]
  exact h (2 * t + 1) (by omega) 2 hc

theorem not_pure_6 (s : ℕ) : ¬ isPure (6 * s + 4) := by
  intro h
  unfold isPure at h
  have hc : T^[1] (2 * s + 1) = 6 * s + 4 := by
    show T (2 * s + 1) = 6 * s + 4
    exact T_odd s
  exact h (2 * s + 1) (by omega) 1 hc

theorem not_pure_13 (q : ℕ) : ¬ isPure (18 * q + 13) := by
  intro h
  unfold isPure at h
  have hc : T^[5] (16 * q + 11) = 18 * q + 13 := by
    show T (T (T (T (T (16 * q + 11))))) = 18 * q + 13
    rw [show 16 * q + 11 = 2 * (8 * q + 5) + 1 by ring, T_odd,
      show 6 * (8 * q + 5) + 4 = 2 * (24 * q + 17) by ring, T_even,
      show 24 * q + 17 = 2 * (12 * q + 8) + 1 by ring, T_odd,
      show 6 * (12 * q + 8) + 4 = 2 * (36 * q + 26) by ring, T_even,
      show 36 * q + 26 = 2 * (18 * q + 13) by ring, T_even]
  exact h (16 * q + 11) (by omega) 5 hc

theorem pure_zero (n : ℕ) (h : n = 0) : isPure n := by
  subst h
  unfold isPure
  intro N hN
  exact absurd hN (Nat.not_lt_zero N)

theorem pure_mem (n : ℕ) (h : isPure n) : n % 18 ∈ S := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 18 ∧ n = 18 * q + r :=
    ⟨n / 18, n % 18, Nat.mod_lt n (by norm_num), (Nat.div_add_mod n 18).symm⟩
  rw [show (18 * q + r) % 18 = r by omega]
  interval_cases r
  · simp [S]
  · simp [S]
  · have h' : isPure (3 * (6 * q) + 2) := by rwa [show 3 * (6 * q) + 2 = 18 * q + 2 by ring]
    exact (not_pure_3 _ h').elim
  · simp [S]
  · have h' : isPure (6 * (3 * q) + 4) := by rwa [show 6 * (3 * q) + 4 = 18 * q + 4 by ring]
    exact (not_pure_6 _ h').elim
  · have h' : isPure (3 * (6 * q + 1) + 2) := by
      rwa [show 3 * (6 * q + 1) + 2 = 18 * q + 5 by ring]
    exact (not_pure_3 _ h').elim
  · simp [S]
  · simp [S]
  · have h' : isPure (3 * (6 * q + 2) + 2) := by
      rwa [show 3 * (6 * q + 2) + 2 = 18 * q + 8 by ring]
    exact (not_pure_3 _ h').elim
  · simp [S]
  · have h' : isPure (6 * (3 * q + 1) + 4) := by
      rwa [show 6 * (3 * q + 1) + 4 = 18 * q + 10 by ring]
    exact (not_pure_6 _ h').elim
  · have h' : isPure (3 * (6 * q + 3) + 2) := by
      rwa [show 3 * (6 * q + 3) + 2 = 18 * q + 11 by ring]
    exact (not_pure_3 _ h').elim
  · simp [S]
  · exact (not_pure_13 q h).elim
  · have h' : isPure (3 * (6 * q + 4) + 2) := by
      rwa [show 3 * (6 * q + 4) + 2 = 18 * q + 14 by ring]
    exact (not_pure_3 _ h').elim
  · simp [S]
  · have h' : isPure (6 * (3 * q + 2) + 4) := by
      rwa [show 6 * (3 * q + 2) + 4 = 18 * q + 16 by ring]
    exact (not_pure_6 _ h').elim
  · have h' : isPure (3 * (6 * q + 5) + 2) := by
      rwa [show 3 * (6 * q + 5) + 2 = 18 * q + 17 by ring]
    exact (not_pure_3 _ h').elim

theorem exists_min (P : ℕ → Prop) (h : ∃ M, P M) : ∃ M, P M ∧ ∀ M', P M' → M ≤ M' := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun M' hM' => Nat.find_min' h hM'⟩

theorem core (n : ℕ) (hn : 1 ≤ n) :
    isPure n ↔ ¬ ∃ i < n, (1 ≤ i ∧ isPure i) ∧
      ∃ j, 1 ≤ j ∧ T^[j] i = n ∧ ∀ l, 1 ≤ l → l ≤ j → i < T^[l] i := by
  constructor
  · intro hp hex
    unfold isPure at hp
    obtain ⟨i, hi, -, j, -, hj, -⟩ := hex
    exact hp i hi j hj
  · intro h
    unfold isPure
    intro N hN k hk
    obtain ⟨N0, hP0, hmin⟩ := exists_min (fun M => ∃ k, T^[k] M = n) ⟨N, k, hk⟩
    obtain ⟨k0, hk0⟩ : ∃ k, T^[k] N0 = n := hP0
    have hN0n : N0 < n := lt_of_le_of_lt (hmin N ⟨k, hk⟩) hN
    have hN01 : 1 ≤ N0 := by
      rcases Nat.eq_zero_or_pos N0 with h0 | h0
      · rw [h0, T_zero_iter] at hk0
        omega
      · omega
    have hpure0 : isPure N0 := by
      unfold isPure
      intro M hM k' hk'
      have hk2 : T^[k0 + k'] M = n := by
        rw [Function.iterate_add_apply, hk', hk0]
      have h3 := hmin M ⟨k0 + k', hk2⟩
      omega
    obtain ⟨K, hPK, hKmin⟩ := exists_min (fun k => T^[k] N0 = n) ⟨k0, hk0⟩
    have hK : T^[K] N0 = n := hPK
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · rw [h0, Function.iterate_zero_apply] at hK
        omega
      · omega
    have hstay : ∀ l, 1 ≤ l → l ≤ K → N0 < T^[l] N0 := by
      intro l hl1 hlK
      by_contra hle
      have hle' : T^[l] N0 ≤ N0 := Nat.le_of_not_lt hle
      rcases Nat.lt_or_ge l K with hlt | hge
      · have hsplit : T^[K - l] (T^[l] N0) = n := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlK]
          exact hK
        rcases Nat.lt_or_ge (T^[l] N0) N0 with h2 | h2
        · have h3 := hmin (T^[l] N0) ⟨K - l, hsplit⟩
          omega
        · have heq : T^[l] N0 = N0 := le_antisymm hle' h2
          rw [heq] at hsplit
          have h3 := hKmin (K - l) hsplit
          omega
      · have hlK' : l = K := le_antisymm hlK hge
        rw [hlK', hK] at hle'
        omega
    exact h ⟨N0, hN0n, ⟨hN01, hpure0⟩, K, hK1, hK, hstay⟩

theorem col_iff (blue : ℕ → Prop) (hb : IsColoring blue) (n : ℕ) :
    blue n ↔ (1 ≤ n ∧ isPure n) := by
  unfold IsColoring at hb
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hb n]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, (core n h1).2 ?_⟩
      rintro ⟨i, hi, ⟨hi1, hip⟩, hR⟩
      exact h2 ⟨i, hi, (ih i hi).2 ⟨hi1, hip⟩, hR⟩
    · rintro ⟨h1, hp⟩
      refine ⟨h1, ?_⟩
      rintro ⟨i, hi, hbi, hR⟩
      exact (core n h1).1 hp ⟨i, hi, (ih i hi).1 hbi, hR⟩

end H15A375852

open OMA.S_oeis_a375852 in
theorem OMA.solution : type_of% @OMA.S_oeis_a375852.main := by
  refine ⟨⟨fun n => 1 ≤ n ∧ isPure n, ?_⟩, ?_⟩
  · unfold IsColoring
    intro n
    constructor
    · rintro ⟨h1, hp⟩
      exact ⟨h1, (H15A375852.core n h1).1 hp⟩
    · rintro ⟨h1, hn⟩
      exact ⟨h1, (H15A375852.core n h1).2 hn⟩
  · intro blue hb
    have hc := H15A375852.col_iff blue hb
    ext n
    show n % 18 ∈ S ↔ isPure n ∨ A309180 blue n
    unfold A309180
    rw [hc n]
    have hmem := H15A375852.pure_mem n
    constructor
    · intro hS
      by_cases hp : isPure n
      · exact Or.inl hp
      · right
        have h1 : 1 ≤ n := by
          rcases Nat.eq_zero_or_pos n with h | h
          · exact absurd (H15A375852.pure_zero n h) hp
          · omega
        exact ⟨h1, Or.inl ⟨hS, fun h' => hp h'.2⟩⟩
    · rintro (hp | ⟨_, ⟨hS, _⟩ | ⟨hS, _, hp⟩⟩)
      · exact hmem hp
      · exact hS
      · exact absurd (hmem hp) hS
