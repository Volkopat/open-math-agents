import OMAStatements.S_oeis_a159021

-- Problem: OEIS A159021, Librandi's conjecture: the square terms are (7*2^k)^2
-- Statement: statements/oeis-a159021.lean (declaration OMA.S_oeis_a159021.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. The terms a(0..6) are 19, 23, 27, 32, 37, 43, 49, and only 49 = 7^2 is a square.
-- From a(7) = 56 on, with M = 7*2^k, each term is m^2 + 2M - m or m^2 + 2M for some m with
-- M <= m <= 2M: the step from m^2 + 2M - m adds m and gives m^2 + 2M, and the step from
-- m^2 + 2M adds m and gives (m+1)^2 + 2M - (m+1). At m = 2M the term is the square (2M)^2 and
-- the same pattern starts again with 2M in the place of M. A term m^2 + r with 0 < r <= 2m is
-- not a square, so the square terms are the numbers (2M)^2 = (7*2^(k+1))^2.

namespace OMA.A159021

open OMA.S_oeis_a159021

lemma sqrt_of (m r : ℕ) (h : r ≤ 2 * m) : Nat.sqrt (m ^ 2 + r) = m := by
  symm
  rw [Nat.eq_sqrt']
  constructor <;> nlinarith

lemma not_sq (m x : ℕ) (h1 : m ^ 2 < x) (h2 : x < (m + 1) ^ 2) : ¬ IsSquare x := by
  rintro ⟨t, rfl⟩
  have h3 : m < t := by nlinarith
  have h4 : t < m + 1 := by nlinarith
  omega

lemma step (n x m r : ℕ) (hx : a n = x) (h : x = m ^ 2 + r) (hr : r ≤ 2 * m) :
    a (n + 1) = x + m := by
  have h1 : a (n + 1) = a n + Nat.sqrt (a n) := rfl
  rw [h1, hx, h, sqrt_of m r hr]

lemma values : a 0 = 19 ∧ a 1 = 23 ∧ a 2 = 27 ∧ a 3 = 32 ∧ a 4 = 37 ∧ a 5 = 43 ∧ a 6 = 49
    ∧ a 7 = 56 := by
  have h0 : a 0 = 19 := rfl
  have h1 : a 1 = 23 := step 0 19 4 3 h0 (by norm_num) (by norm_num)
  have h2 : a 2 = 27 := step 1 23 4 7 h1 (by norm_num) (by norm_num)
  have h3 : a 3 = 32 := step 2 27 5 2 h2 (by norm_num) (by norm_num)
  have h4 : a 4 = 37 := step 3 32 5 7 h3 (by norm_num) (by norm_num)
  have h5 : a 5 = 43 := step 4 37 6 1 h4 (by norm_num) (by norm_num)
  have h6 : a 6 = 49 := step 5 43 6 7 h5 (by norm_num) (by norm_num)
  have h7 : a 7 = 56 := step 6 49 7 0 h6 (by norm_num) (by norm_num)
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- The state of the sequence from index 7 on. With `M = 7 * 2 ^ k` and `M ≤ m ≤ 2 M`, the term
is `m ^ 2 + 2 M - m`, or it is `m ^ 2 + 2 M` with `m < 2 M`. -/
def Inv (x : ℕ) : Prop :=
  ∃ k m : ℕ, 7 * 2 ^ k ≤ m ∧ m ≤ 2 * (7 * 2 ^ k) ∧
    (x + m = m ^ 2 + 2 * (7 * 2 ^ k) ∨ (m < 2 * (7 * 2 ^ k) ∧ x = m ^ 2 + 2 * (7 * 2 ^ k)))

lemma inv_step (x : ℕ) (h : Inv x) : Inv (x + Nat.sqrt x) := by
  obtain ⟨k, m, h1, h2, h3 | ⟨h3, h4⟩⟩ := h
  · by_cases hm : m = 2 * (7 * 2 ^ k)
    · -- a square: the next phase starts
      have hx : x = m ^ 2 := by omega
      have hs : Nat.sqrt x = m := by
        rw [hx]
        have := sqrt_of m 0 (by omega)
        simpa using this
      refine ⟨k + 1, m, ?_, ?_, Or.inl ?_⟩
      · rw [pow_succ]
        omega
      · rw [pow_succ]
        omega
      · rw [hs, hx, pow_succ]
        omega
    · have hlt : m < 2 * (7 * 2 ^ k) := by omega
      have hx : x = m ^ 2 + (2 * (7 * 2 ^ k) - m) := by omega
      have hs : Nat.sqrt x = m := by
        rw [hx]
        exact sqrt_of m _ (by omega)
      refine ⟨k, m, h1, h2, Or.inr ⟨hlt, ?_⟩⟩
      rw [hs]
      omega
  · have hs : Nat.sqrt x = m := by
      rw [h4]
      exact sqrt_of m _ (by omega)
    refine ⟨k, m + 1, by omega, by omega, Or.inl ?_⟩
    rw [hs, h4]
    ring

lemma inv_all (j : ℕ) : Inv (a (7 + j)) := by
  induction j with
  | zero =>
    refine ⟨0, 7, by norm_num, by norm_num, Or.inl ?_⟩
    have : a 7 = 56 := values.2.2.2.2.2.2.2
    rw [Nat.add_zero, this]
    norm_num
  | succ j ih =>
    have : a (7 + (j + 1)) = a (7 + j) + Nat.sqrt (a (7 + j)) := rfl
    rw [this]
    exact inv_step _ ih

lemma inv_square (x : ℕ) (h : Inv x) (hsq : IsSquare x) : ∃ k : ℕ, x = (7 * 2 ^ k) ^ 2 := by
  obtain ⟨k, m, h1, h2, h3 | ⟨h3, h4⟩⟩ := h
  · by_cases hm : m = 2 * (7 * 2 ^ k)
    · refine ⟨k + 1, ?_⟩
      have hx : x = m ^ 2 := by omega
      rw [hx, hm, pow_succ]
      ring
    · exfalso
      have hpos : 0 < 7 * 2 ^ k := by positivity
      refine not_sq m x ?_ ?_ hsq
      · omega
      · have : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
        omega
  · exfalso
    have hpos : 0 < 7 * 2 ^ k := by positivity
    refine not_sq m x ?_ ?_ hsq
    · omega
    · have : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
      omega

theorem result (n : ℕ) (hsq : IsSquare (a n)) : ∃ k : ℕ, a n = (7 * 2 ^ k) ^ 2 := by
  by_cases hn : 7 ≤ n
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact inv_square _ (inv_all j) hsq
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := values
    have hlt : n < 7 := by omega
    interval_cases n
    · rw [h0] at hsq
      exact absurd hsq (not_sq 4 19 (by norm_num) (by norm_num))
    · rw [h1] at hsq
      exact absurd hsq (not_sq 4 23 (by norm_num) (by norm_num))
    · rw [h2] at hsq
      exact absurd hsq (not_sq 5 27 (by norm_num) (by norm_num))
    · rw [h3] at hsq
      exact absurd hsq (not_sq 5 32 (by norm_num) (by norm_num))
    · rw [h4] at hsq
      exact absurd hsq (not_sq 6 37 (by norm_num) (by norm_num))
    · rw [h5] at hsq
      exact absurd hsq (not_sq 6 43 (by norm_num) (by norm_num))
    · exact ⟨0, by rw [h6]; norm_num⟩

end OMA.A159021

theorem OMA.solution : type_of% @OMA.S_oeis_a159021.main :=
  fun n hsq => OMA.A159021.result n hsq
