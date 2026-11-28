import OMAStatements.S_oeis_a286807

-- Based on @jleguina's original verified proof. Track weighted word length directly.

namespace OMA.S_oeis_a286807

open Finset





/-- The tokens: `true` is 1, `false` is 10. -/
def tok : Bool → List ℕ
  | true => [1]
  | false => [1, 0]

/-- The words made of tokens. -/
def flat (ts : List Bool) : List ℕ := ts.flatMap tok

/-- The mapping on tokens: 1 -> 10 1, 10 -> 10 10. -/
def tau : Bool → List Bool
  | true => [false, true]
  | false => [false, false]

lemma step_flat : ∀ ts : List Bool, step (flat ts) = flat (ts.flatMap tau)
  | [] => rfl
  | true :: ts => by
    show step (1 :: flat ts) = [1, 0] ++ ([1] ++ flat (ts.flatMap tau))
    rw [step, step_flat ts]
    rfl
  | false :: ts => by
    show step (1 :: 0 :: flat ts) = [1, 0] ++ ([1, 0] ++ flat (ts.flatMap tau))
    rw [step]
    have h0 : step (0 :: flat ts) = 0 :: step (flat ts) := by
      cases ts with
      | nil => rfl
      | cons b ts => cases b <;> rfl
    rw [h0, step_flat ts]
    rfl

/-- The token words of the iterates. -/
def R : ℕ → List Bool
  | 0 => []
  | n + 1 => true :: (R n).flatMap tau

lemma iter_eq (n : ℕ) : iter n = [0, 0] ++ flat (R n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iter, Function.iterate_succ_apply', ← iter, ih]
    show step (0 :: 0 :: flat (R n)) = _
    rw [step, step_flat]
    rfl

lemma count_true_and_length_tau (ts : List Bool) :
    (ts.flatMap tau).count true = ts.count true ∧
      (flat (ts.flatMap tau)).length = 2 * (flat ts).length + ts.count true := by
  induction ts with
  | nil => decide
  | cons b ts ih =>
    obtain ⟨hc, hl⟩ := ih
    cases b <;> simp [flat, tok, tau] at * <;> omega

lemma length_iter (n : ℕ) : (iter n).length + n = 2 ^ (n + 1) := by
  have h (k : ℕ) : (R k).count true = k ∧ (flat (R k)).length + k + 2 = 2 ^ (k + 1) := by
    induction k with
    | zero => decide
    | succ k ih =>
      obtain ⟨ht, hd⟩ := count_true_and_length_tau (R k)
      simp [R, flat, tok, pow_succ' 2 (k + 1)] at *
      omega
  rw [iter_eq, List.length_append]
  have := (h n).2
  simp only [List.length_cons, List.length_nil]
  omega

lemma A132045_succ (m : ℕ) : A132045 (m + 1) + (m + 1) = 2 ^ (m + 1) + 1 := by
  unfold A132045
  have hsum : ∑ k ∈ range (m + 2), (m + 1).choose k = 2 ^ (m + 1) := Nat.sum_range_choose (m + 1)
  rw [sum_range_succ, sum_range_succ'] at hsum ⊢
  simp only [T, true_or, or_true, if_true, Nat.choose_self,
    Nat.choose_zero_right] at hsum ⊢
  have hmid : ∀ k ∈ range m, T (m + 1) (k + 1) + 1 = (m + 1).choose (k + 1) := by
    intro k hk
    have hk' := mem_range.mp hk
    unfold T
    rw [if_neg (by omega)]
    have : 0 < (m + 1).choose (k + 1) := Nat.choose_pos (by omega)
    omega
  have hmid' : (∑ k ∈ range m, T (m + 1) (k + 1)) + m = ∑ k ∈ range m, (m + 1).choose (k + 1) := by
    rw [← sum_congr rfl hmid, sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
  simp only [T] at hmid'
  omega

/-- Kimberling's conjecture: the n-th iterate (counting 00 as the first) has A132045(n) letters. -/
theorem conjecture : ∀ n : ℕ, 1 ≤ n → (iter (n - 1)).length = A132045 n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := length_iter m
  have h2 := A132045_succ m
  rw [show m + 1 - 1 = m by omega]
  omega

/-- Controls: the iterates 00, 001, 001101, 0011011010101 listed in the entry, and A132045(0..6) =
1, 2, 3, 6, 13, 28, 59. -/
example : iter 0 = [0, 0] ∧ iter 1 = [0, 0, 1] ∧ iter 2 = [0, 0, 1, 1, 0, 1] ∧
    iter 3 = [0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] ∧
    (List.range 7).map A132045 = [1, 2, 3, 6, 13, 28, 59] := by
  decide +kernel

end OMA.S_oeis_a286807

theorem OMA.solution : type_of% @OMA.S_oeis_a286807.main :=
  OMA.S_oeis_a286807.conjecture
