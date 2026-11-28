import OMAStatements.S_oeis_a330904

-- Problem: A330904: No five consecutive integers have matching binary and balanced ternary digit sums.
-- Upstream: statements/oeis-a330904.lean (declaration OMA.S_oeis_a330904.main)
-- Credit: @anthill24 (the owner of the agent is credited as the solver)

namespace OMA_oeis_a330904

open OMA.S_oeis_a330904

private lemma balancedTernaryDigitSum_mod_two (n : ℕ) :
    balancedTernaryDigitSum n % 2 = (n : ℤ) % 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold balancedTernaryDigitSum
    by_cases h1 : n ≤ 1
    · simp only [h1, ↓reduceDIte]
    · simp only [h1, ↓reduceDIte]
      by_cases h2 : n % 3 = 2
      · simp only [h2, ↓reduceIte]
        have hlt : n / 3 + 1 < n := by omega
        have hih := ih (n / 3 + 1) hlt
        omega
      · simp only [h2, ↓reduceIte]
        have hlt : n / 3 < n := by omega
        have hih := ih (n / 3) hlt
        omega

private lemma digits_two_count_one_mul_two (k : ℕ) :
    (Nat.digits 2 (2 * k)).count 1 = (Nat.digits 2 k).count 1 := by
  cases k with
  | zero => simp
  | succ m =>
    have hpos : 0 < 2 * (m + 1) := by omega
    rw [Nat.digits_def' (by decide : 1 < 2) hpos]
    have hmod : (2 * (m + 1)) % 2 = 0 := by omega
    have hdiv : (2 * (m + 1)) / 2 = m + 1 := by omega
    rw [hmod, hdiv]
    simp

private lemma digits_two_count_one_pair (k : ℕ) :
    (Nat.digits 2 (4 * k + 1)).count 1 = (Nat.digits 2 (4 * k + 2)).count 1 := by
  have h1 : Nat.digits 2 (4 * k + 1) = 1 :: Nat.digits 2 (2 * k) := by
    rw [Nat.digits_def' (by decide : 1 < 2) (by omega)]
    have hmod : (4 * k + 1) % 2 = 1 := by omega
    have hdiv : (4 * k + 1) / 2 = 2 * k := by omega
    rw [hmod, hdiv]
  have h2 : Nat.digits 2 (4 * k + 2) = 0 :: Nat.digits 2 (2 * k + 1) := by
    rw [Nat.digits_def' (by decide : 1 < 2) (by omega)]
    have hmod : (4 * k + 2) % 2 = 0 := by omega
    have hdiv : (4 * k + 2) / 2 = 2 * k + 1 := by omega
    rw [hmod, hdiv]
  have h3 : Nat.digits 2 (2 * k + 1) = 1 :: Nat.digits 2 k := by
    rw [Nat.digits_def' (by decide : 1 < 2) (by omega)]
    have hmod : (2 * k + 1) % 2 = 1 := by omega
    have hdiv : (2 * k + 1) / 2 = k := by omega
    rw [hmod, hdiv]
  rw [h1, h2, h3]
  simp [digits_two_count_one_mul_two]

private lemma not_pair (k : ℕ) :
    ¬ (MatchingDigitSums (4 * k + 1) ∧ MatchingDigitSums (4 * k + 2)) := by
  rintro ⟨hm1, hm2⟩
  unfold MatchingDigitSums at hm1 hm2
  have hcnt := digits_two_count_one_pair k
  have heq : balancedTernaryDigitSum (4 * k + 1) = balancedTernaryDigitSum (4 * k + 2) := by
    omega
  have hp1 := balancedTernaryDigitSum_mod_two (4 * k + 1)
  have hp2 := balancedTernaryDigitSum_mod_two (4 * k + 2)
  omega

private lemma main_proof (n : ℕ) : ¬ (∀ i : Fin 5, MatchingDigitSums (n + i.val)) := by
  intro h
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with hr | hr | hr | hr
  · refine not_pair (n / 4) ⟨?_, ?_⟩
    · have e : 4 * (n / 4) + 1 = n + 1 := by omega
      rw [e]; exact h ⟨1, by decide⟩
    · have e : 4 * (n / 4) + 2 = n + 2 := by omega
      rw [e]; exact h ⟨2, by decide⟩
  · refine not_pair (n / 4) ⟨?_, ?_⟩
    · have e : 4 * (n / 4) + 1 = n + 0 := by omega
      rw [e]; exact h ⟨0, by decide⟩
    · have e : 4 * (n / 4) + 2 = n + 1 := by omega
      rw [e]; exact h ⟨1, by decide⟩
  · refine not_pair (n / 4 + 1) ⟨?_, ?_⟩
    · have e : 4 * (n / 4 + 1) + 1 = n + 3 := by omega
      rw [e]; exact h ⟨3, by decide⟩
    · have e : 4 * (n / 4 + 1) + 2 = n + 4 := by omega
      rw [e]; exact h ⟨4, by decide⟩
  · refine not_pair (n / 4 + 1) ⟨?_, ?_⟩
    · have e : 4 * (n / 4 + 1) + 1 = n + 2 := by omega
      rw [e]; exact h ⟨2, by decide⟩
    · have e : 4 * (n / 4 + 1) + 2 = n + 3 := by omega
      rw [e]; exact h ⟨3, by decide⟩

end OMA_oeis_a330904

theorem OMA.solution : type_of% @OMA.S_oeis_a330904.main :=
  OMA_oeis_a330904.main_proof
