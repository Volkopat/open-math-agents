import OMAStatements.S_oeis_a259661

-- Problem: A259661: Binary representation of the middle column of the 'Rule 54' elementary cellular automaton starting with a single ON (black) cell.
-- Upstream: formal-conjectures statements/oeis-a259661.lean:0 (declaration OMA.S_oeis_a259661.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof sketch. By induction on t, cell 54 t i is ON iff |i| <= t and either t is even and
i - t = 0 mod 4, or t is odd and i - t is not 1 mod 4 (rule 54 is c xor (l or r)).
So the middle column is 1, 1, 0, 0 repeating, a(n+1) = 10 a(n) + c(n+1), and the
four-term recurrence and the generating function follow from the periodicity of c.
-/

namespace OMA.P_oeis_a259661

open OMA.S_oeis_a259661 PowerSeries

lemma rule54 (l c r : Bool) : ruleOut 54 l c r = xor c (l || r) := by
  cases l <;> cases c <;> cases r <;> decide

def P54 (t : ℕ) (i : ℤ) : Bool :=
  decide (-(t : ℤ) ≤ i ∧ i ≤ t ∧
    ((t % 2 = 0 ∧ (i - t) % 4 = 0) ∨ (t % 2 = 1 ∧ (i - t) % 4 ≠ 1)))

lemma cell54 (t : ℕ) : ∀ i : ℤ, cell 54 t i = P54 t i := by
  induction t with
  | zero =>
    intro i
    simp only [cell, P54]
    by_cases h : i = 0
    · subst h
      decide
    · rw [decide_eq_false h]
      symm
      rw [decide_eq_false_iff_not]
      omega
  | succ t ih =>
    intro i
    simp only [cell, rule54]
    rw [ih (i - 1), ih i, ih (i + 1)]
    cases hA : P54 t (i - 1) <;> cases hB : P54 t i <;> cases hC : P54 t (i + 1) <;>
      simp only [P54, decide_eq_true_eq, decide_eq_false_iff_not] at hA hB hC ⊢ <;>
      simp only [Bool.or_true, Bool.or_false, Bool.xor_true, Bool.xor_false, Bool.not_true,
        Bool.not_false] <;>
      first
      | (symm; rw [decide_eq_true_iff]; push_cast; omega)
      | (symm; rw [decide_eq_false_iff_not]; push_cast; omega)

lemma mid (t : ℕ) : cell 54 t 0 = decide (t % 4 = 0 ∨ t % 4 = 1) := by
  rw [cell54]
  simp only [P54]
  by_cases h : t % 4 = 0 ∨ t % 4 = 1
  · rw [decide_eq_true h, decide_eq_true_iff]
    omega
  · rw [decide_eq_false h, decide_eq_false_iff_not]
    omega

/-- the digit sequence 1, 1, 0, 0, 1, 1, 0, 0, ... -/
def c (t : ℕ) : ℤ := if t % 4 = 0 ∨ t % 4 = 1 then 1 else 0

lemma a_eq (n : ℕ) : a n = ∑ t ∈ Finset.range (n + 1), c t * 10 ^ (n - t) := by
  unfold a
  apply Finset.sum_congr rfl
  intro t _
  rw [mid]
  unfold c
  by_cases h : t % 4 = 0 ∨ t % 4 = 1
  · rw [decide_eq_true h, if_pos rfl, if_pos h, one_mul]
  · rw [decide_eq_false h, if_neg (by decide), if_neg h, zero_mul]

lemma a_succ (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  rw [a_eq, a_eq, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  rw [show n + 1 - t = (n - t) + 1 by omega, pow_succ]
  ring

lemma a_zero : a 0 = 1 := by
  rw [a_eq, Finset.sum_range_one]
  norm_num [c]

lemma c_period (m : ℕ) : c (m + 4) - c (m + 3) + c (m + 2) - c (m + 1) = 0 := by
  unfold c
  split_ifs <;> omega

lemma rec4 (m : ℕ) :
    a (m + 4) = 11 * a (m + 3) - 11 * a (m + 2) + 11 * a (m + 1) - 10 * a m := by
  have h1 := a_succ m
  have h2 := a_succ (m + 1)
  have h3 := a_succ (m + 2)
  have h4 := a_succ (m + 3)
  have hc := c_period m
  linear_combination h4 - h3 + h2 - h1 + hc

lemma part1 : ∀ n > 3, a n = 11 * a (n - 1) - 11 * a (n - 2) + 11 * a (n - 3) - 10 * a (n - 4) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simpa using rec4 m

lemma part2 :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 10 * X) * (1 + X ^ 2)) = 1 := by
  rw [show ((1 : PowerSeries ℚ) - X) * (1 - 10 * X) * (1 + X ^ 2) =
    1 - 11 * X + 11 * X ^ 2 - 11 * X ^ 3 + 10 * X ^ 4 by ring]
  ext (_ | _ | _ | _ | m) <;> simp [mul_sub, mul_add, ← map_ofNat C, ← mul_assoc, coeff_mul_X_pow',
    mul_comm _ (C _), coeff_one, show a 0 = 1 by decide, show a 1 = 11 by decide,
    show a 2 = 110 by decide, show a 3 = 1100 by decide] <;>
    (try rw [show _ + 1 + 1 + 1 + 1 = _ + 4 from rfl, rec4]) <;> push_cast <;> ring

end OMA.P_oeis_a259661

theorem OMA.solution : type_of% @OMA.S_oeis_a259661.main :=
  ⟨OMA.P_oeis_a259661.part1, OMA.P_oeis_a259661.part2⟩
