import OMAStatements.S_oeis_a298113

-- Problem: A298113: Solution b( ) of the complementary equation a(n) = a(1)*b(n) - a(0)*b(n-1) + 4*n, where a(0) = 1, a(1) = 2, b(0) = 3, b(1) = 4, b(2) = 5, and (b(n)) is the increasing sequence of positive integers not in (a(n)).  See Comments.
-- Upstream: formal-conjectures statements/oeis-a298113.lean:0 (declaration OMA.S_oeis_a298113.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: build the pair. b(0) = 3 and b(n+1) = b(n) + 1, plus 1 when b(n) + 1 = a(j) for some
-- 2 <= j <= n, where a(0) = 1, a(1) = 2, a(j) = 2 b(j) - b(j-1) + 4 j (j >= 2). Then b steps by 1
-- or 2, a steps by at least 4 from j = 2 on and a(j) >= b(j) + 9, which gives both monotonicity
-- and the complementarity. This pair has b(7) = 10, and 10 - 7 sqrt 2 < 1/2 since
-- sqrt 2 > 19/14.

namespace P1A298113

/-- hitB f t m: some j < m with 2 <= j has 2 f(j) - f(j-1) + 4 j = t. -/
def hitB (f : ℕ → ℕ) (t : ℕ) : ℕ → Bool
  | 0 => false
  | k + 1 => (decide (2 ≤ k) && decide (2 * f k - f (k - 1) + 4 * k = t)) || hitB f t k

theorem hitB_iff (f : ℕ → ℕ) (t m : ℕ) :
    hitB f t m = true ↔ ∃ j, j < m ∧ 2 ≤ j ∧ 2 * f j - f (j - 1) + 4 * j = t := by
  induction m with
  | zero =>
    constructor
    · intro h
      simp [hitB] at h
    · rintro ⟨j, hj, -⟩
      omega
  | succ k ih =>
    simp only [hitB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨j, hj, h3, h4⟩)
      · exact ⟨k, by omega, h1, h2⟩
      · exact ⟨j, by omega, h3, h4⟩
    · rintro ⟨j, hj, h3, h4⟩
      rcases Nat.lt_or_ge j k with h | h
      · exact Or.inr ⟨j, h, h3, h4⟩
      · obtain rfl : j = k := by omega
        exact Or.inl ⟨h3, h4⟩

/-- bt n agrees with b on 0..n. -/
def bt : ℕ → ℕ → ℕ
  | 0 => fun _ => 3
  | n + 1 => fun i => if i ≤ n then bt n i else
      bt n n + 1 + (if hitB (bt n) (bt n n + 1) (n + 1) = true then 1 else 0)

/-- The sequence b. -/
def seqB (n : ℕ) : ℕ := bt n n

/-- The sequence a. -/
def seqA (n : ℕ) : ℕ := if n = 0 then 1 else if n = 1 then 2 else 2 * seqB n - seqB (n - 1) + 4 * n

theorem bt_succ (n i : ℕ) : bt (n + 1) i = if i ≤ n then bt n i else
    bt n n + 1 + (if hitB (bt n) (bt n n + 1) (n + 1) = true then 1 else 0) := rfl

theorem bt_eq (n i : ℕ) (h : i ≤ n) : bt n i = seqB i := by
  induction n generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    by_cases hi : i ≤ n
    · rw [bt_succ, if_pos hi]
      exact ih i hi
    · obtain rfl : i = n + 1 := by omega
      rfl

theorem B_succ (n : ℕ) : seqB (n + 1) =
    seqB n + 1 + (if hitB seqB (seqB n + 1) (n + 1) = true then 1 else 0) := by
  have h1 : seqB (n + 1) =
      bt n n + 1 + (if hitB (bt n) (bt n n + 1) (n + 1) = true then 1 else 0) := by
    show bt (n + 1) (n + 1) = _
    rw [bt_succ, if_neg (show ¬(n + 1 ≤ n) by omega)]
  have hc : hitB (bt n) (bt n n + 1) (n + 1) = hitB seqB (seqB n + 1) (n + 1) := by
    rw [Bool.eq_iff_iff, hitB_iff, hitB_iff]
    apply exists_congr
    intro j
    apply and_congr_right
    intro hj
    rw [bt_eq n j (by omega), bt_eq n (j - 1) (by omega), bt_eq n n le_rfl]
  rw [h1, hc, bt_eq n n le_rfl]

theorem B1 : seqB 1 = 4 := by decide +kernel

theorem B2 : seqB 2 = 5 := by decide +kernel

theorem B7 : seqB 7 = 10 := by decide +kernel

theorem B_lt (n : ℕ) : seqB n < seqB (n + 1) := by
  rw [B_succ n]
  split_ifs <;> omega

theorem B_le (n : ℕ) : seqB (n + 1) ≤ seqB n + 2 := by
  rw [B_succ n]
  split_ifs <;> omega

theorem B_mono : StrictMono seqB := strictMono_nat_of_lt_succ B_lt

theorem B_ge (n : ℕ) : n + 3 ≤ seqB n := by
  induction n with
  | zero =>
    show 0 + 3 ≤ 3
    omega
  | succ n ih =>
    have := B_lt n
    omega

theorem A0 : seqA 0 = 1 := by simp [seqA]

theorem A1 : seqA 1 = 2 := by simp [seqA]

theorem A_ge2 (n : ℕ) (h : 2 ≤ n) : seqA n = 2 * seqB n - seqB (n - 1) + 4 * n := by
  unfold seqA
  rw [if_neg (show ¬(n = 0) by omega), if_neg (show ¬(n = 1) by omega)]

theorem A_big (n : ℕ) (h : 2 ≤ n) : seqB n + 9 ≤ seqA n := by
  rw [A_ge2 n h]
  have h1 := B_lt (n - 1)
  rw [show n - 1 + 1 = n by omega] at h1
  omega

theorem A_gap (n : ℕ) (h : 2 ≤ n) : seqA n + 4 ≤ seqA (n + 1) := by
  rw [A_ge2 n h, A_ge2 (n + 1) (by omega)]
  have h1 := B_lt (n - 1)
  have h2 := B_le (n - 1)
  have h3 := B_lt n
  rw [show n - 1 + 1 = n by omega] at h1 h2
  rw [show n + 1 - 1 = n by omega]
  omega

theorem A_lt (n : ℕ) : seqA n < seqA (n + 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · show seqA 0 < seqA 1
      decide +kernel
    · show seqA 1 < seqA 2
      decide +kernel
  · have := A_gap n h
    omega

theorem A_mono : StrictMono seqA := strictMono_nat_of_lt_succ A_lt

theorem eqnAB : ∀ n : ℕ, 2 ≤ n →
    (seqA n : ℤ) = seqA 1 * seqB n - seqA 0 * seqB (n - 1) + 4 * n := by
  intro n hn
  have e := A_ge2 n hn
  have h1 := B_lt (n - 1)
  rw [show n - 1 + 1 = n by omega] at h1
  have e2 : seqA n + seqB (n - 1) = 2 * seqB n + 4 * n := by omega
  have e3 : (seqA n : ℤ) + seqB (n - 1) = 2 * seqB n + 4 * n := by exact_mod_cast e2
  rw [A0, A1]
  push_cast
  linear_combination e3

theorem hit_iff (n : ℕ) :
    hitB seqB (seqB n + 1) (n + 1) = true ↔ seqB n + 1 ∈ Set.range seqA := by
  rw [hitB_iff]
  constructor
  · rintro ⟨j, _, hj2, hj⟩
    exact ⟨j, by rw [A_ge2 j hj2]; exact hj⟩
  · rintro ⟨j, hj⟩
    have hB := B_ge n
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with hlt | hge
      · exfalso
        interval_cases j
        · rw [A0] at hj
          omega
        · rw [A1] at hj
          omega
      · exact hge
    have hjn : j ≤ n := by
      by_contra hgt
      have h1 := A_big j hj2
      have h2 : seqB (n + 1) ≤ seqB j := B_mono.monotone (by omega)
      have h3 := B_lt n
      omega
    refine ⟨j, by omega, hj2, ?_⟩
    rw [← A_ge2 j hj2]
    exact hj

theorem skip_yes (n : ℕ) (h : seqB n + 1 ∈ Set.range seqA) : seqB (n + 1) = seqB n + 2 := by
  have e := B_succ n
  rw [if_pos ((hit_iff n).mpr h)] at e
  omega

theorem skip_no (n : ℕ) (h : seqB n + 1 ∉ Set.range seqA) : seqB (n + 1) = seqB n + 1 := by
  have e := B_succ n
  rw [if_neg (fun h' => h ((hit_iff n).mp h'))] at e
  omega

theorem coverB (i : ℕ) :
    ∀ m : ℕ, 3 ≤ m → m < seqB (i + 1) → m ∈ Set.range seqB ∨ m ∈ Set.range seqA := by
  induction i with
  | zero =>
    show ∀ m : ℕ, 3 ≤ m → m < seqB 1 → m ∈ Set.range seqB ∨ m ∈ Set.range seqA
    intro m h3 hlt
    rw [B1] at hlt
    left
    refine ⟨0, ?_⟩
    show 3 = m
    omega
  | succ i ih =>
    intro m h3 hlt
    rcases Nat.lt_or_ge m (seqB (i + 1)) with h1 | h1
    · exact ih m h3 h1
    · have hle := B_le (i + 1)
      rcases Nat.eq_or_lt_of_le h1 with h2 | h2
      · left
        exact ⟨i + 1, h2⟩
      · right
        have hm : m = seqB (i + 1) + 1 := by omega
        by_contra hna
        rw [hm] at hna
        have e := skip_no (i + 1) hna
        omega

theorem complB (m : ℕ) (hm : 1 ≤ m) : m ∈ Set.range seqB ↔ m ∉ Set.range seqA := by
  constructor
  · rintro ⟨i, rfl⟩ ⟨j, hj⟩
    have hBi := B_ge i
    rcases Nat.lt_or_ge j 2 with hlt | hj2
    · interval_cases j
      · rw [A0] at hj
        omega
      · rw [A1] at hj
        omega
    · rcases Nat.lt_or_ge j i with hji | hij
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        by_cases hk : seqB k + 1 ∈ Set.range seqA
        · have e := skip_yes k hk
          obtain ⟨j', hj'⟩ := hk
          have hBk := B_ge k
          have hj'2 : 2 ≤ j' := by
            rcases Nat.lt_or_ge j' 2 with hlt' | hge'
            · exfalso
              interval_cases j'
              · rw [A0] at hj'
                omega
              · rw [A1] at hj'
                omega
            · exact hge'
          have hlt : j' < j := by
            by_contra hc
            have h6 := A_mono.monotone (show j ≤ j' by omega)
            omega
          have h4 := A_gap j' hj'2
          have h5 : seqA (j' + 1) ≤ seqA j := A_mono.monotone (by omega)
          omega
        · have e := skip_no k hk
          exact hk ⟨j, by rw [hj, e]⟩
      · have h1 := A_big j hj2
        have h2 : seqB i ≤ seqB j := B_mono.monotone hij
        omega
  · intro hna
    have hm3 : 3 ≤ m := by
      by_contra hlt
      have hlt' : m < 3 := by omega
      interval_cases m
      · exact hna ⟨0, A0⟩
      · exact hna ⟨1, A1⟩
    have hbig : m < seqB (m + 1) := by
      have := B_ge (m + 1)
      omega
    rcases coverB m m hm3 hbig with h | h
    · exact h
    · exact absurd h hna

end P1A298113

open OMA.S_oeis_a298113 P1A298113 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298113.main) := by
  intro H
  have hsol : IsSolution seqA seqB := by
    unfold IsSolution
    exact ⟨A0, A1, rfl, B1, B2, eqnAB, A_mono, B_mono, complB⟩
  have h7 := (H seqA seqB hsol 7 (by norm_num)).1
  rw [B7] at h7
  have hs : (19 / 14 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 19 / 14)]
    norm_num
  push_cast at h7
  linarith
