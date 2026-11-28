import OMAStatements.S_oeis_a376357

-- Problem: A376357: Positions of numbers in A007961 that end in 0.
-- Upstream: formal-conjectures statements/oeis-a376357.lean:0 (declaration OMA.S_oeis_a376357.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: D r b is the remainder of r after the greedy steps for the place values
-- (b+1)^2, ..., 2^2. For n >= 1 the last decimal digit of A007961(n) is D n n, which is at most 3,
-- and D (n+1) (n+1) is either D n n + 1 or 0. So every four consecutive numbers after any n
-- contain a term, which bounds the gaps by 4; the gaps 1, 2, 3, 4 occur at 8-9, 34-36, 13-16
-- and 4-8.

namespace S07A376357

open OMA.S_oeis_a376357

/-- D r b: the remainder of r after the greedy steps for the place values (b+1)^2, ..., 2^2. -/
def D : ℕ → ℕ → ℕ
  | r, 0 => r
  | r, b + 1 => D (r % (b + 2) ^ 2) b

theorem D_zero (r : ℕ) : D r 0 = r := rfl

theorem D_succ (r b : ℕ) : D r (b + 1) = D (r % (b + 2) ^ 2) b := rfl

theorem D_zero_r : ∀ b : ℕ, D 0 b = 0
  | 0 => rfl
  | b + 1 => by
    rw [D_succ, Nat.zero_mod]
    exact D_zero_r b

theorem D_lt : ∀ b r : ℕ, D r (b + 1) < 4
  | 0, r => by
    rw [D_succ, D_zero]
    have h4 : (0 + 2) ^ 2 = 4 := by norm_num
    rw [h4]
    omega
  | b + 1, r => by
    rw [D_succ]
    exact D_lt b _

theorem D_step : ∀ b r : ℕ, D (r + 1) b = D r b + 1 ∨ D (r + 1) b = 0
  | 0, r => Or.inl rfl
  | b + 1, r => by
    rw [D_succ, D_succ]
    have hq : 1 < (b + 2) ^ 2 :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ b + 2 by omega) 2)
    have hlt : r % (b + 2) ^ 2 < (b + 2) ^ 2 := Nat.mod_lt _ (by omega)
    have hadd : (r + 1) % (b + 2) ^ 2 = (r % (b + 2) ^ 2 + 1) % (b + 2) ^ 2 := by
      rw [Nat.add_mod r 1, Nat.mod_eq_of_lt hq]
    rcases Nat.lt_or_ge (r % (b + 2) ^ 2 + 1) ((b + 2) ^ 2) with h | h
    · rw [hadd, Nat.mod_eq_of_lt h]
      exact D_step b (r % (b + 2) ^ 2)
    · right
      have he : r % (b + 2) ^ 2 + 1 = (b + 2) ^ 2 := by omega
      rw [hadd, he, Nat.mod_self]
      exact D_zero_r b

theorem D_stable (r b : ℕ) (h : r < (b + 2) ^ 2) : ∀ k : ℕ, D r (b + k) = D r b
  | 0 => rfl
  | k + 1 => by
    have h2 : (b + 2) ^ 2 ≤ (b + k + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rw [show b + (k + 1) = b + k + 1 by omega, D_succ,
      Nat.mod_eq_of_lt (show r < (b + k + 2) ^ 2 by omega)]
    exact D_stable r b h k

theorem rep_mod : ∀ b r : ℕ, rep r (b + 1) % 10 = D r b % 10
  | 0, r => by
    have e : rep r (0 + 1) = r / (0 + 1) ^ 2 * 10 ^ 0 + rep (r % (0 + 1) ^ 2) 0 := rfl
    have e0 : rep (r % (0 + 1) ^ 2) 0 = 0 := rfl
    rw [e, e0, D_zero]
    simp
  | b + 1, r => by
    have e : rep r (b + 1 + 1) =
        r / (b + 2) ^ 2 * 10 ^ (b + 1) + rep (r % (b + 2) ^ 2) (b + 1) := rfl
    have e10 : r / (b + 2) ^ 2 * 10 ^ (b + 1) = 10 * (r / (b + 2) ^ 2 * 10 ^ b) := by ring
    rw [e, e10, D_succ, ← rep_mod b (r % (b + 2) ^ 2)]
    omega

theorem last_digit (n : ℕ) (hn : 1 ≤ n) : A007961 n % 10 = D n n := by
  have hs : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
  have h0 : n < (Nat.sqrt n + 1) ^ 2 := Nat.sqrt_lt'.mp (by omega)
  have hlt : n < (Nat.sqrt n - 1 + 2) ^ 2 := by
    rw [show Nat.sqrt n - 1 + 2 = Nat.sqrt n + 1 by omega]
    exact h0
  have hk : Nat.sqrt n - 1 + (n - (Nat.sqrt n - 1)) = n := by
    have := Nat.sqrt_le_self n
    omega
  have hst : D n n = D n (Nat.sqrt n - 1) := by
    have h := D_stable n (Nat.sqrt n - 1) hlt (n - (Nat.sqrt n - 1))
    rw [hk] at h
    exact h
  have hrep : A007961 n = rep n (Nat.sqrt n - 1 + 1) := by
    unfold A007961
    rw [show Nat.sqrt n - 1 + 1 = Nat.sqrt n by omega]
  have hsmall : D n (Nat.sqrt n - 1) < 10 := by
    rcases Nat.lt_or_ge 1 (Nat.sqrt n) with h1 | h1
    · obtain ⟨c, hc⟩ : ∃ c, Nat.sqrt n - 1 = c + 1 := ⟨Nat.sqrt n - 2, by omega⟩
      rw [hc]
      have := D_lt c n
      omega
    · have h1' : Nat.sqrt n = 1 := by omega
      have h3 := Nat.le_three_of_sqrt_eq_one h1'
      rw [h1', Nat.sub_self, D_zero]
      omega
  rw [hrep, rep_mod, hst, Nat.mod_eq_of_lt hsmall]

theorem Dnn_lt (n : ℕ) (hn : 1 ≤ n) : D n n < 4 := by
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
  exact D_lt c (c + 1)

theorem E_step (n m : ℕ) (hm : m = n + 1) : D m m = D n n + 1 ∨ D m m = 0 := by
  subst hm
  have h2 : n < (n + 2) ^ 2 := by nlinarith [Nat.zero_le n]
  have hs : D n (n + 1) = D n n := D_stable n n h2 1
  rw [← hs]
  exact D_step (n + 1) n

theorem window (n : ℕ) : ∃ j, n < j ∧ j ≤ n + 4 ∧ D j j = 0 := by
  have b4 := Dnn_lt (n + 4) (by omega)
  have s1 := E_step n (n + 1) rfl
  have s2 := E_step (n + 1) (n + 2) rfl
  have s3 := E_step (n + 2) (n + 3) rfl
  have s4 := E_step (n + 3) (n + 4) rfl
  by_cases h1 : D (n + 1) (n + 1) = 0
  · exact ⟨n + 1, by omega, by omega, h1⟩
  by_cases h2 : D (n + 2) (n + 2) = 0
  · exact ⟨n + 2, by omega, by omega, h2⟩
  by_cases h3 : D (n + 3) (n + 3) = 0
  · exact ⟨n + 3, by omega, by omega, h3⟩
  refine ⟨n + 4, by omega, by omega, ?_⟩
  omega

/-- The predicate of the statement. -/
abbrev P (m : ℕ) : Prop := 1 ≤ m ∧ A007961 m % 10 = 0

theorem P_iff (m : ℕ) : P m ↔ 1 ≤ m ∧ D m m = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [← last_digit m h1]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [last_digit m h1]
    exact h2

theorem pval (m : ℕ) (h1 : 1 ≤ m) (h : D m m = 0) : P m := (P_iff m).2 ⟨h1, h⟩

theorem npval (m : ℕ) (h : D m m ≠ 0) : ¬ P m := fun hp => h ((P_iff m).1 hp).2

theorem P_infinite : (Set.ofPred P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨j, hj1, -, hj3⟩ := window N
  exact ⟨j, pval j (by omega) hj3, hj1⟩

theorem a_succ (k : ℕ) : a (k + 1) = Nat.nth P k := by
  show Nat.nth P (k + 1 - 1) = Nat.nth P k
  rw [Nat.add_sub_cancel]

theorem a_succ_succ (k : ℕ) : a (k + 1 + 1) = Nat.nth P (k + 1) := a_succ (k + 1)

theorem gap (k : ℕ) : Nat.nth P k < Nat.nth P (k + 1) ∧ Nat.nth P (k + 1) ≤ Nat.nth P k + 4 := by
  have hlt : Nat.nth P k < Nat.nth P (k + 1) :=
    Nat.nth_strictMono P_infinite (show k < k + 1 by omega)
  refine ⟨hlt, ?_⟩
  obtain ⟨j, hj1, hj2, hj3⟩ := window (Nat.nth P k)
  have hPj : P j := pval j (by omega) hj3
  by_contra hcon
  have h1 : j < Nat.nth P (k + 1) := by omega
  have h2 := Nat.le_nth_of_lt_nth_succ h1 hPj
  omega

theorem consec (m m' : ℕ) (hm : P m) (hm' : P m') (hlt : m < m')
    (hgap : ∀ j, m < j → j < m' → ¬ P j) : ∃ n, 1 ≤ n ∧ a (n + 1) - a n = m' - m := by
  have hr : m ∈ Set.range (Nat.nth P) := by
    rw [Nat.range_nth_of_infinite P_infinite]
    exact hm
  obtain ⟨k, hk⟩ := Set.mem_range.mp hr
  have h1 : Nat.nth P k < Nat.nth P (k + 1) :=
    Nat.nth_strictMono P_infinite (show k < k + 1 by omega)
  have h2 : P (Nat.nth P (k + 1)) := Nat.nth_mem_of_infinite P_infinite (k + 1)
  have h3 : m' ≤ Nat.nth P (k + 1) := by
    by_contra hc
    exact hgap _ (by omega) (by omega) h2
  have h4 : Nat.nth P (k + 1) ≤ m' := by
    by_contra hc
    have h5 := Nat.le_nth_of_lt_nth_succ (show m' < Nat.nth P (k + 1) by omega) hm'
    omega
  refine ⟨k + 1, by omega, ?_⟩
  rw [a_succ_succ, a_succ]
  omega

theorem p4 : P 4 := pval 4 (by norm_num) (by decide)
theorem p8 : P 8 := pval 8 (by norm_num) (by decide)
theorem p9 : P 9 := pval 9 (by norm_num) (by decide)
theorem p13 : P 13 := pval 13 (by norm_num) (by decide)
theorem p16 : P 16 := pval 16 (by norm_num) (by decide)
theorem p34 : P 34 := pval 34 (by norm_num) (by decide)
theorem p36 : P 36 := pval 36 (by norm_num) (by decide)

theorem gap8 : ∀ j, 8 < j → j < 9 → ¬ P j := fun j h1 h2 _ => by omega

theorem gap34 : ∀ j, 34 < j → j < 36 → ¬ P j := by
  intro j h1 h2
  obtain rfl : j = 35 := by omega
  exact npval 35 (by decide)

theorem gap13 : ∀ j, 13 < j → j < 16 → ¬ P j := by
  intro j h1 h2
  interval_cases j
  · exact npval 14 (by decide)
  · exact npval 15 (by decide)

theorem gap4 : ∀ j, 4 < j → j < 8 → ¬ P j := by
  intro j h1 h2
  interval_cases j
  · exact npval 5 (by decide)
  · exact npval 6 (by decide)
  · exact npval 7 (by decide)

theorem main_proof : {d : ℕ | ∃ n : ℕ, 1 ≤ n ∧ a (n + 1) - a n = d} = {1, 2, 3, 4} := by
  apply Set.ext
  intro d
  constructor
  · rintro ⟨n, hn, hd⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [a_succ_succ, a_succ] at hd
    obtain ⟨g1, g2⟩ := gap k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact consec 8 9 p8 p9 (by norm_num) gap8
    · exact consec 34 36 p34 p36 (by norm_num) gap34
    · exact consec 13 16 p13 p16 (by norm_num) gap13
    · exact consec 4 8 p4 p8 (by norm_num) gap4

end S07A376357

theorem OMA.solution : type_of% @OMA.S_oeis_a376357.main := S07A376357.main_proof