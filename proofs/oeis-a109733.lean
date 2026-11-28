import OMAStatements.S_oeis_a109733

-- Problem: A109733: Sequence is its own base-10 ASCII representation.
-- Upstream: formal-conjectures statements/oeis-a109733.lean:0 (declaration OMA.S_oeis_a109733.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: every term is 48 + (a digit), so 48 <= a(n) <= 57 and every term has two digits.
-- Hence a(2j+1) = 48 + a(j+1)/10 and a(2j+2) = 48 + (a(j+1) mod 10). Then a(2m+1) is 52 or 53,
-- so a(4m+1) = 53 and a(8m+2) = 51; a(4m+2) is 50 or 51, so a(8m+3) = 53. The witness for
-- existence is the sequence defined by this recursion from a(1) = 53.

open OMA.S_oeis_a109733

theorem S03a109733_two (x : ℕ) (h1 : 10 ≤ x) (h2 : x < 100) :
    (Nat.digits 10 x).reverse = [x / 10, x % 10] := by
  have e1 : Nat.digits 10 x = x % 10 :: Nat.digits 10 (x / 10) :=
    Nat.digits_def' (by norm_num) (by omega)
  have e2 : Nat.digits 10 (x / 10) = x / 10 % 10 :: Nat.digits 10 (x / 10 / 10) :=
    Nat.digits_def' (by norm_num) (by omega)
  have e3 : x / 10 / 10 = 0 := by omega
  have e4 : x / 10 % 10 = x / 10 := by omega
  rw [e1, e2, e3, e4, Nat.digits_zero]
  rfl

theorem S03a109733_getD_lt : ∀ l : List ℕ, (∀ x ∈ l, x < 10) → ∀ i : ℕ, l.getD i 0 < 10 := by
  intro l
  induction l with
  | nil =>
    intro _ i
    simp
  | cons y t ih =>
    intro hl i
    cases i with
    | zero =>
      rw [List.getD_cons_zero]
      exact hl y (by simp)
    | succ i =>
      rw [List.getD_cons_succ]
      exact ih (fun x hx => hl x (by simp [hx])) i

theorem S03a109733_mem (a : ℕ → ℕ) (n : ℕ) : ∀ x ∈ digitString a n, x < 10 := by
  induction n with
  | zero =>
    intro x hx
    simp [digitString] at hx
  | succ n ih =>
    intro x hx
    have e : digitString a (n + 1) = digitString a n ++ (Nat.digits 10 (a (n + 1))).reverse :=
      rfl
    rw [e, List.mem_append, List.mem_reverse] at hx
    rcases hx with hx | hx
    · exact ih x hx
    · exact Nat.digits_lt_base (by norm_num) hx

theorem S03a109733_bound (a : ℕ → ℕ) (hS : SelfASCII a) (i : ℕ) (hi : 1 ≤ i) :
    48 ≤ a i ∧ a i ≤ 57 := by
  have h := hS i hi
  have h2 := S03a109733_getD_lt (digitString a i) (S03a109733_mem a i) (i - 1)
  omega

theorem S03a109733_ds (a : ℕ → ℕ) (hB : ∀ i, 1 ≤ i → 10 ≤ a i ∧ a i < 100) (n : ℕ) :
    (digitString a n).length = 2 * n ∧ ∀ j, j < n →
      (digitString a n).getD (2 * j) 0 = a (j + 1) / 10 ∧
      (digitString a n).getD (2 * j + 1) 0 = a (j + 1) % 10 := by
  induction n with
  | zero =>
    refine ⟨by simp [digitString], ?_⟩
    intro j hj
    omega
  | succ n ih =>
    obtain ⟨ihl, ihg⟩ := ih
    obtain ⟨b1, b2⟩ := hB (n + 1) (by omega)
    have e : digitString a (n + 1) = digitString a n ++ [a (n + 1) / 10, a (n + 1) % 10] := by
      show digitString a n ++ (Nat.digits 10 (a (n + 1))).reverse = _
      rw [S03a109733_two (a (n + 1)) b1 b2]
    refine ⟨?_, ?_⟩
    · have h1 := congrArg List.length e
      have h2 : (digitString a n ++ [a (n + 1) / 10, a (n + 1) % 10]).length =
          (digitString a n).length + 2 := by
        simp
      omega
    · intro j hj
      rw [e]
      rcases Nat.lt_or_ge j n with hjn | hjn
      · rw [List.getD_append (digitString a n) [a (n + 1) / 10, a (n + 1) % 10] 0 (2 * j)
            (by omega),
          List.getD_append (digitString a n) [a (n + 1) / 10, a (n + 1) % 10] 0 (2 * j + 1)
            (by omega)]
        exact ihg j hjn
      · have hjeq : j = n := by omega
        rw [hjeq,
          List.getD_append_right (digitString a n) [a (n + 1) / 10, a (n + 1) % 10] 0 (2 * n)
            (by omega),
          List.getD_append_right (digitString a n) [a (n + 1) / 10, a (n + 1) % 10] 0 (2 * n + 1)
            (by omega),
          ihl, Nat.sub_self, show 2 * n + 1 - 2 * n = 1 by omega]
        exact ⟨rfl, rfl⟩

/-- The witness: a(1) = 53, a(2j+2) = 48 + (a(j+1) mod 10), a(2j+1) = 48 + a(j+1)/10. -/
def S03a109733_A : ℕ → ℕ
  | 0 => 0
  | 1 => 53
  | n + 2 =>
    if n % 2 = 0 then 48 + S03a109733_A (n / 2 + 1) % 10
    else 48 + S03a109733_A ((n + 3) / 2) / 10

theorem S03a109733_A_even (j : ℕ) :
    S03a109733_A (2 * j + 2) = 48 + S03a109733_A (j + 1) % 10 := by
  rw [S03a109733_A.eq_3 (2 * j), if_pos (show 2 * j % 2 = 0 by omega),
    show 2 * j / 2 + 1 = j + 1 by omega]

theorem S03a109733_A_odd (j : ℕ) :
    S03a109733_A (2 * j + 1) = 48 + S03a109733_A (j + 1) / 10 := by
  cases j with
  | zero => simp [S03a109733_A]
  | succ i =>
    rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by omega, S03a109733_A.eq_3 (2 * i + 1),
      if_neg (show ¬ ((2 * i + 1) % 2 = 0) by omega),
      show (2 * i + 1 + 3) / 2 = i + 1 + 1 by omega]

theorem S03a109733_A_bound : ∀ N i : ℕ, 1 ≤ i → i ≤ N →
    48 ≤ S03a109733_A i ∧ S03a109733_A i ≤ 57 := by
  intro N
  induction N with
  | zero =>
    intro i h1 h2
    omega
  | succ N ih =>
    intro i h1 h2
    rcases Nat.lt_or_ge i (N + 1) with h3 | h3
    · exact ih i h1 (by omega)
    · obtain ⟨j, hj | hj⟩ : ∃ j, i = 2 * j + 1 ∨ i = 2 * j + 2 := ⟨(i - 1) / 2, by omega⟩
      · subst hj
        rw [S03a109733_A_odd j]
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0
          simp [S03a109733_A]
        · have h4 := ih (j + 1) (by omega) (by omega)
          omega
      · subst hj
        rw [S03a109733_A_even j]
        omega

theorem S03a109733_A_self : SelfASCII S03a109733_A := by
  intro n hn
  have hB : ∀ i, 1 ≤ i → 10 ≤ S03a109733_A i ∧ S03a109733_A i < 100 := by
    intro i hi
    have h4 := S03a109733_A_bound i i hi le_rfl
    omega
  obtain ⟨j, hj | hj⟩ : ∃ j, n = 2 * j + 1 ∨ n = 2 * j + 2 := ⟨(n - 1) / 2, by omega⟩
  · subst hj
    rw [Nat.add_sub_cancel, ((S03a109733_ds S03a109733_A hB (2 * j + 1)).2 j (by omega)).1]
    exact S03a109733_A_odd j
  · subst hj
    rw [show 2 * j + 2 - 1 = 2 * j + 1 by omega,
      ((S03a109733_ds S03a109733_A hB (2 * j + 2)).2 j (by omega)).2]
    exact S03a109733_A_even j

theorem OMA.solution : type_of% @OMA.S_oeis_a109733.main := by
  refine ⟨⟨S03a109733_A, S03a109733_A_self⟩, ?_⟩
  intro a hS n _
  have hB : ∀ i, 1 ≤ i → 48 ≤ a i ∧ a i ≤ 57 := fun i hi => S03a109733_bound a hS i hi
  have hB' : ∀ i, 1 ≤ i → 10 ≤ a i ∧ a i < 100 := by
    intro i hi
    have h4 := hB i hi
    omega
  have R1 : ∀ j, a (2 * j + 1) = 48 + a (j + 1) / 10 := by
    intro j
    have h := hS (2 * j + 1) (by omega)
    rw [Nat.add_sub_cancel, ((S03a109733_ds a hB' (2 * j + 1)).2 j (by omega)).1] at h
    exact h
  have R2 : ∀ j, a (2 * j + 2) = 48 + a (j + 1) % 10 := by
    intro j
    have h := hS (2 * j + 2) (by omega)
    rw [show 2 * j + 2 - 1 = 2 * j + 1 by omega,
      ((S03a109733_ds a hB' (2 * j + 2)).2 j (by omega)).2] at h
    exact h
  have CA : ∀ m, a (4 * m + 1) = 53 := by
    intro m
    have h1 := R1 (2 * m)
    have h2 := R1 m
    have h3 := hB (m + 1) (by omega)
    rw [show 2 * (2 * m) + 1 = 4 * m + 1 by omega] at h1
    omega
  have CB : ∀ m, a (8 * m + 3) = 53 := by
    intro m
    have h1 := R1 (4 * m + 1)
    have h2 := R2 (2 * m)
    have h3 := R1 m
    have h4 := hB (m + 1) (by omega)
    rw [show 2 * (4 * m + 1) + 1 = 8 * m + 3 by omega, show 4 * m + 1 + 1 = 4 * m + 2 by omega]
      at h1
    rw [show 2 * (2 * m) + 2 = 4 * m + 2 by omega] at h2
    omega
  have CC : ∀ m, a (8 * m + 2) = 51 := by
    intro m
    have h1 := R2 (4 * m)
    have h2 := CA m
    rw [show 2 * (4 * m) + 2 = 8 * m + 2 by omega] at h1
    omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | h | h
    · have h5 := CA (2 * (n / 8))
      rw [show 4 * (2 * (n / 8)) + 1 = n by omega] at h5
      exact h5
    · have h5 := CB (n / 8)
      rw [show 8 * (n / 8) + 3 = n by omega] at h5
      exact h5
    · have h5 := CA (2 * (n / 8) + 1)
      rw [show 4 * (2 * (n / 8) + 1) + 1 = n by omega] at h5
      exact h5
  · have h5 := CC (n / 8)
    rw [show 8 * (n / 8) + 2 = n by omega] at h5
    exact h5
