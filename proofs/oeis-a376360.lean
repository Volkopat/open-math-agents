import OMAStatements.S_oeis_a376360

-- Problem: A376360: Positions of numbers in A007961 that end in 3.
-- Upstream: formal-conjectures statements/oeis-a376360.lean:0 (declaration OMA.S_oeis_a376360.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Disproof idea: For n >= 1 the last decimal digit of A007961(n) is E(n) = D n n, which satisfies
-- the shift invariance E(k^2 + r) = E(r) for k >= 3 and r <= 2*k. This shows A376360 is infinite
-- (via k^2 + 3) and reduces the window [336391, 336403] in at most four shift steps to values
-- below 9, certifying that 336391 and 336403 are consecutive terms of A376360 with difference 12,
-- which is not in {4, 5, 6, 7, 8, 9, 10, 11, 13}.

namespace A1A376360

open OMA.S_oeis_a376360

/-- D r b: the remainder of r after the greedy steps for the place values (b+1)^2, ..., 2^2. -/
def D : ℕ → ℕ → ℕ
  | r, 0 => r
  | r, b + 1 => D (r % (b + 2) ^ 2) b

theorem D_zero (r : ℕ) : D r 0 = r := rfl

theorem D_succ (r b : ℕ) : D r (b + 1) = D (r % (b + 2) ^ 2) b := rfl

theorem D_lt : ∀ b r : ℕ, D r (b + 1) < 4
  | 0, r => by
    rw [D_succ, D_zero]
    have h4 : (0 + 2) ^ 2 = 4 := by norm_num
    rw [h4]
    omega
  | b + 1, r => by
    rw [D_succ]
    exact D_lt b _

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

/-- E n: shorthand for D n n, equal to the last decimal digit of A007961(n) for n >= 1. -/
def E (n : ℕ) : ℕ := D n n

theorem E_shift (k r : ℕ) (hk : 3 ≤ k) (hr : r ≤ 2 * k) : E (k ^ 2 + r) = E r := by
  unfold E
  have hkr : k ^ 2 + r < (k - 1 + 2) ^ 2 := by
    rw [show k - 1 + 2 = k + 1 by omega]
    nlinarith
  have hge : k - 1 ≤ k ^ 2 + r := by
    have : k ≤ k ^ 2 := by nlinarith
    omega
  have h1 : D (k ^ 2 + r) (k ^ 2 + r) = D (k ^ 2 + r) (k - 1) := by
    have h := D_stable (k ^ 2 + r) (k - 1) hkr (k ^ 2 + r - (k - 1))
    rw [show k - 1 + (k ^ 2 + r - (k - 1)) = k ^ 2 + r by omega] at h
    exact h
  have h2 : D (k ^ 2 + r) (k - 1) = D r (k - 2) := by
    rw [show k - 1 = k - 2 + 1 by omega, D_succ, show k - 2 + 2 = k by omega]
    have hrlt : r < k ^ 2 := by nlinarith
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hrlt]
  rw [h1, h2]
  rcases le_total r (k - 2) with hle | hle
  · have hr1 : r < (r + 2) ^ 2 := by nlinarith
    have h := D_stable r r hr1 (k - 2 - r)
    rw [show r + (k - 2 - r) = k - 2 by omega] at h
    exact h
  · have hr2 : r < (k - 2 + 2) ^ 2 := by
      rw [show k - 2 + 2 = k by omega]
      nlinarith
    have h := D_stable r (k - 2) hr2 (r - (k - 2))
    rw [show k - 2 + (r - (k - 2)) = r by omega] at h
    exact h.symm

theorem E_step_eq (n k r : ℕ) (hk : 3 ≤ k) (hr : r ≤ 2 * k) (hn : n = k ^ 2 + r) :
    E n = E r := by
  rw [hn]
  exact E_shift k r hk hr

theorem e0 : E 0 = 0 := by decide
theorem e1 : E 1 = 1 := by decide
theorem e2 : E 2 = 2 := by decide
theorem e3 : E 3 = 3 := by decide
theorem e4 : E 4 = 0 := by decide
theorem e5 : E 5 = 1 := by decide

/-- The predicate of the statement. -/
abbrev P (m : ℕ) : Prop := 1 ≤ m ∧ A007961 m % 10 = 3

theorem P_iff (m : ℕ) : P m ↔ 1 ≤ m ∧ E m = 3 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    unfold E
    rw [← last_digit m h1]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [last_digit m h1]
    exact h2

theorem pval (m : ℕ) (h1 : 1 ≤ m) (h : E m = 3) : P m := (P_iff m).2 ⟨h1, h⟩

theorem npval (m : ℕ) (h : E m ≠ 3) : ¬ P m := fun hp => h ((P_iff m).1 hp).2

theorem P_infinite : (Set.ofPred P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨(N + 3) ^ 2 + 3, ?_, ?_⟩
  · apply pval _ (by nlinarith)
    rw [E_shift (N + 3) 3 (by omega) (by omega)]
    exact e3
  · nlinarith

theorem a_succ (k : ℕ) : a (k + 1) = Nat.nth P k := by
  show Nat.nth P (k + 1 - 1) = Nat.nth P k
  rw [Nat.add_sub_cancel]

theorem a_succ_succ (k : ℕ) : a (k + 1 + 1) = Nat.nth P (k + 1) := a_succ (k + 1)

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

theorem p_lo : P 336391 := by
  apply pval 336391 (by norm_num)
  rw [E_step_eq _ 579 1150 (by norm_num) (by norm_num) (by norm_num),
      E_step_eq _ 33 61 (by norm_num) (by norm_num) (by norm_num),
      E_step_eq _ 7 12 (by norm_num) (by norm_num) (by norm_num),
      E_step_eq _ 3 3 (by norm_num) (by norm_num) (by norm_num)]
  exact e3

theorem p_hi : P 336403 := by
  apply pval 336403 (by norm_num)
  rw [E_step_eq _ 580 3 (by norm_num) (by norm_num) (by norm_num)]
  exact e3

theorem gap_inner : ∀ j, 336391 < j → j < 336403 → ¬ P j := by
  intro j hj1 hj2
  obtain ⟨d, hd1, hd2, rfl⟩ : ∃ d, 1 ≤ d ∧ d ≤ 11 ∧ j = 336391 + d :=
    ⟨j - 336391, by omega, by omega, by omega⟩
  interval_cases d
  · apply npval
    rw [E_step_eq _ 579 1151 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 33 62 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 7 13 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 3 4 (by norm_num) (by norm_num) (by norm_num), e4]
    decide
  · apply npval
    rw [E_step_eq _ 579 1152 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 33 63 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 7 14 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 3 5 (by norm_num) (by norm_num) (by norm_num), e5]
    decide
  · apply npval
    rw [E_step_eq _ 579 1153 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 33 64 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 8 0 (by norm_num) (by norm_num) (by norm_num), e0]
    decide
  · apply npval
    rw [E_step_eq _ 579 1154 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 33 65 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 8 1 (by norm_num) (by norm_num) (by norm_num), e1]
    decide
  · apply npval
    rw [E_step_eq _ 579 1155 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 33 66 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 8 2 (by norm_num) (by norm_num) (by norm_num), e2]
    decide
  · apply npval
    rw [E_step_eq _ 579 1156 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 34 0 (by norm_num) (by norm_num) (by norm_num), e0]
    decide
  · apply npval
    rw [E_step_eq _ 579 1157 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 34 1 (by norm_num) (by norm_num) (by norm_num), e1]
    decide
  · apply npval
    rw [E_step_eq _ 579 1158 (by norm_num) (by norm_num) (by norm_num),
        E_step_eq _ 34 2 (by norm_num) (by norm_num) (by norm_num), e2]
    decide
  · apply npval
    rw [E_step_eq _ 580 0 (by norm_num) (by norm_num) (by norm_num), e0]
    decide
  · apply npval
    rw [E_step_eq _ 580 1 (by norm_num) (by norm_num) (by norm_num), e1]
    decide
  · apply npval
    rw [E_step_eq _ 580 2 (by norm_num) (by norm_num) (by norm_num), e2]
    decide

theorem main_disproof :
    ¬ ({d : ℕ | ∃ n : ℕ, 1 ≤ n ∧ a (n + 1) - a n = d} = {4, 5, 6, 7, 8, 9, 10, 11, 13}) := by
  intro hmain
  have h12 : 12 ∈ {d : ℕ | ∃ n : ℕ, 1 ≤ n ∧ a (n + 1) - a n = d} := by
    obtain ⟨n, hn1, hn2⟩ := consec 336391 336403 p_lo p_hi (by norm_num) gap_inner
    exact ⟨n, hn1, hn2.trans (by norm_num)⟩
  rw [hmain] at h12
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h12
  omega

end A1A376360

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a376360.main) := A1A376360.main_disproof
