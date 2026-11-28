import OMAStatements.S_oeis_a090072

/-!
Duplicate the digits of 10001 with a separation of 26 decimal places. The
first 53 terms of its trajectory fit in those places, so the two copies
run in parallel through the twelfth palindrome. The finite certificate below
checks these steps against the original definition of digit reversal.
-/

namespace DuplicatedPalindrome

open OMA.S_oeis_a090072

private def original : List ℕ :=
  [
    10001, 20002, 40004, 80008,
    160016, 770077, 1540154, 6050605,
    11111111, 22222222, 44444444, 88888888,
    177777776, 855555547, 1601111105, 6612222166,
    13224444332, 36568886563, 73137773126, 135275546263,
    497921118794, 995732248588, 1881574486187, 9698419238068,
    18306748387037, 91385133147418, 172859266305737, 910362929264008,
    1710825858527027, 8918084443807198, 17835167888615396, 87186856764769267,
    163483603530637445, 708219638837021806, 1316340377673934613, 4480734145404370744,
    8951468190818741588, 17802946371737383186, 85941320089102304057, 160981640287104619015,
    671898042069150808076, 1342706094029391706252, 3868778033234297778683, 7737555957557606557366,
    14375112025115202114743, 49116232276267223272084, 97143464552534446533278, 184377028996059992967457,
    939146328946759813740938, 1778193647904409637382877, 9561031016948507101301648, 18022062034007003202603307,
    88352682264077046228625388]

private def value (i : ℕ) : ℕ := (10 ^ 26 + 1) * original[i]?.getD 0

private def indices : Finset ℕ := {0, 1, 2, 3, 5, 8, 9, 10, 11, 15, 17, 52}

private def digitsUpTo : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => if n = 0 then [] else n % 10 :: digitsUpTo k (n / 10)

private theorem digits_correct (k n : ℕ) (h : n < 10 ^ k) :
    digitsUpTo k n = Nat.digits 10 n := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using h
    simp [this, digitsUpTo]
  | succ k ih =>
    by_cases hz : n = 0
    · simp [hz, digitsUpTo]
    · rw [digitsUpTo, if_neg hz, Nat.digits_def' (by decide) (Nat.pos_of_ne_zero hz)]
      congr 1
      apply ih
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [pow_succ] using h)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem next_checks : ∀ i : Fin 52,
    value i.val < 10 ^ 55 ∧
    value (i.val + 1) = value i.val + Nat.ofDigits 10 (digitsUpTo 55 (value i.val)).reverse := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem palindrome_checks : ∀ i : Fin 53, i.val ∈ indices →
    value i.val < 10 ^ 55 ∧ (digitsUpTo 55 (value i.val)).reverse = digitsUpTo 55 (value i.val) := by
  decide

private theorem reaches (i : ℕ) (hi : i ≤ 52) : revAdd^[i] (value 0) = value i := by
  induction i with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    obtain ⟨bound, step⟩ := next_checks ⟨k, by omega⟩
    change value (k + 1) = value k + Nat.ofDigits 10 (digitsUpTo 55 (value k)).reverse at step
    rw [digits_correct _ _ bound] at step
    exact step.symm

private theorem hits : (indices : Set ℕ) ⊆ palindromeSteps (value 0) := by
  intro i hi
  have hb : indices ⊆ Finset.range 53 := by decide
  have hlt := Finset.mem_range.mp (hb hi)
  obtain ⟨bound, pal⟩ := palindrome_checks ⟨i, hlt⟩ hi
  change (digitsUpTo 55 (value i)).reverse = digitsUpTo 55 (value i) at pal
  rw [digits_correct _ _ bound] at pal
  change isPalindrome (revAdd^[i] (value 0))
  rw [reaches i (by omega)]
  exact pal

end DuplicatedPalindrome

open OMA.S_oeis_a090072 DuplicatedPalindrome

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a090072.main) := by
  intro claim
  have positive : 1 ≤ value 0 := by decide
  obtain ⟨finite, upper⟩ := claim.1 _ positive
  have lower := Set.ncard_le_ncard hits finite
  rw [Set.ncard_coe_finset, show indices.card = 12 by decide] at lower
  have alternatives := (claim.2 _ positive).mp (le_antisymm upper lower)
  have different : value 0 ≠ 10000 ∧ value 0 ≠ 10001 := by decide
  exact alternatives.elim different.1 different.2
