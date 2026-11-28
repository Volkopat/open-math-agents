import OMAStatements.S_oeis_a079291

-- Problem oeis-a079291 (OEIS A079291): with A = 1, 1, 3, 7, 17, 41, ... and the Pell numbers
-- P = 0, 1, 2, 5, 12, 29, ..., for n > 1 the number (A(n)^2 - 1)/2 (n even) or (A(n)^2 + 1)/2 (n odd)
-- is the square of a Pell number.
-- Upstream: statements/oeis-a079291.lean (declaration OMA.S_oeis_a079291.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- The witness is m = n. First A(n+1) = A(n) + 2 P(n) and P(n+1) = A(n) + P(n) by induction; these give
-- the Pell identity A(n)^2 - 2 P(n)^2 = (-1)^n, which is the claim in both parities.

open OMA.S_oeis_a079291

private lemma rel_a079291 : ∀ n : ℕ, A (n + 1) = A n + 2 * P n ∧ P (n + 1) = A n + P n := by
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hA : A (n + 1 + 1) = 2 * A (n + 1) + A n := rfl
    have hP : P (n + 1 + 1) = 2 * P (n + 1) + P n := rfl
    constructor
    · rw [hA]
      omega
    · rw [hP]
      omega

private lemma pell_a079291 : ∀ n : ℕ, (A n : ℤ) ^ 2 - 2 * (P n : ℤ) ^ 2 = (-1) ^ n := by
  intro n
  induction n with
  | zero => norm_num [A, P]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := rel_a079291 n
    rw [h1, h2]
    push_cast
    linear_combination (-1 : ℤ) * ih

theorem OMA.solution : type_of% @OMA.S_oeis_a079291.main := by
  intro n _
  have h := pell_a079291 n
  constructor
  · intro he
    refine ⟨n, ?_⟩
    rw [he.neg_one_pow] at h
    have h' : A n ^ 2 = 2 * P n ^ 2 + 1 := by
      zify
      linarith
    rw [h']
    omega
  · intro ho
    refine ⟨n, ?_⟩
    rw [ho.neg_one_pow] at h
    have h' : A n ^ 2 + 1 = 2 * P n ^ 2 := by
      zify
      linarith
    rw [h']
    omega
