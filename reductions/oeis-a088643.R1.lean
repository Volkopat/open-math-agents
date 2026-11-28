import OMAStatements.S_oeis_a088643

/-!
For OEIS A088643, when the two largest entries sum to a prime, the larger row
is the smaller row with one entry prepended. A least counterexample must
therefore have composite predecessor sum. The two remaining cases distinguish
even and odd starting entries.
-/

namespace OMA.R_oeis_a088643_R1

open OMA.S_oeis_a088643 (next build row)

/-- Adding a used top entry has no effect once the old top also occurs in the row. -/
lemma next_prefixed (n : ℕ) (r : List ℕ) (hn : n ∈ r) :
    next (n + 1) ((n + 1) :: r) = next n r := by
  have last_eq : ((n + 1) :: r).getLast! = r.getLast! := by
    cases r with
    | nil => simp at hn
    | cons => rfl
  have range_eq : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
    simp [List.range_succ]
  unfold next
  rw [range_eq, last_eq]
  simp only [List.filter_cons]
  simp only [List.mem_cons, hn, or_true, not_true_eq_false, false_and, and_false,
    decide_false, Bool.false_eq_true, if_false]
  apply congrArg List.head?
  apply List.filter_congr
  intro m hm
  have hm_lt : m < n := List.mem_range.mp (List.mem_reverse.mp hm)
  have hm_ne : m ≠ n + 1 := by omega
  simp [hm_ne]

/-- With the same number of moves left, both walks append the same entries. -/
lemma build_prefixed (n fuel : ℕ) (r : List ℕ) (hn : n ∈ r) :
    build (n + 1) fuel ((n + 1) :: r) = (n + 1) :: build n fuel r := by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
    simp only [build, next_prefixed n r hn]
    cases h : next n r with
    | none => rfl
    | some m => exact ih (r ++ [m]) (by simp [hn])

/-- A prime sum makes the largest available candidate the first move. -/
lemma next_first (n : ℕ) (hn : 1 ≤ n) (hp : (2 * n + 1).Prime) :
    next (n + 1) [n + 1] = some n := by
  have hsum : (n + (n + 1)).Prime := by rwa [show n + (n + 1) = 2 * n + 1 by omega]
  simp [next, List.range_succ, hn, hsum]

/-- The full list identity, including the order in which the entries appear. -/
theorem row_prepend_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : (2 * n + 1).Prime) :
    row (n + 1) = (n + 1) :: row n := by
  simp only [row, build, next_first n hn hp]
  exact build_prefixed n n [n] (by simp)

lemma complete_succ_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : (2 * n + 1).Prime)
    (hrow : (row n).toFinset = Finset.Icc 1 n) :
    (row (n + 1)).toFinset = Finset.Icc 1 (n + 1) := by
  rw [row_prepend_of_prime n hn hp, List.toFinset_cons, hrow]
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

/-- At the first incomplete row after row one, the two largest entries have composite sum. -/
theorem first_failure_not_prime (n : ℕ) (hn : 1 ≤ n)
    (hrow : (row n).toFinset = Finset.Icc 1 n)
    (hfail : (row (n + 1)).toFinset ≠ Finset.Icc 1 (n + 1)) : ¬ (2 * n + 1).Prime :=
  fun hp => hfail (complete_succ_of_prime n hn hp hrow)

/-- Coverage at even starts where the two largest entries have composite sum. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ (2 * n + 1).Prime → Even (n + 1) →
    (row (n + 1)).toFinset = Finset.Icc 1 (n + 1)

/-- Coverage at odd starts where the two largest entries have composite sum. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ (2 * n + 1).Prime → Odd (n + 1) →
    (row (n + 1)).toFinset = Finset.Icc 1 (n + 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a088643.main := by
  intro he ho m
  induction m with
  | zero => omega
  | succ n ih =>
    intro _
    by_cases hn : n = 0
    · subst n
      decide
    have hpos : 1 ≤ n := by omega
    by_cases hp : (2 * n + 1).Prime
    · exact complete_succ_of_prime n hpos hp (ih hpos)
    · rcases Nat.even_or_odd (n + 1) with h | h
      · exact he n hpos hp h
      · exact ho n hpos hp h

end OMA.R_oeis_a088643_R1
