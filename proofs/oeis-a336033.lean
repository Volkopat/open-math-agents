import OMAStatements.S_oeis_a336033
import Mathlib

/-!
# OEIS A336033: A336033(n) equals the y value of A340488 at index n, for every n >= 1

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Let x be A340488 and y its y sequence, so x(1) = 0 and x(j+1) = x(j) XOR y(j), i.e. y(j) = x(j) XOR
x(j+1). For 1 <= k < n the XOR telescopes: y(k) XOR ... XOR y(n-1) = x(k) XOR x(n). So that block
has XOR 0 exactly when x(k) = x(n), and y(n) is the number of k < n with y(k) XOR ... XOR y(n-1) =
0. That is the defining recurrence of A336033, whose terms are determined by the earlier ones; since
y(1) = 0 = a(1), strong induction gives a(n) = y(n) for all n.
-/

open OMA.S_oeis_a336033

namespace OMA.A336033Proof

lemma xPrefix_length (n : ℕ) : (xPrefix n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [xPrefix, List.length_append, List.length_singleton] using congrArg (· + 1) ih

lemma x_step (n : ℕ) : x (n + 2) = x (n + 1) ^^^ y (n + 1) := by
  unfold x y
  simp only [Nat.add_sub_cancel, xPrefix]
  rw [List.getD_append_right _ _ _ _ (by simp [xPrefix_length])]
  simp [x, xPrefix_length]

lemma xPrefix_succ (n : ℕ) : xPrefix (n + 1) = xPrefix n ++ [x (n + 1)] := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [x_step]
    rfl

lemma xPrefix_map (n : ℕ) :
    xPrefix n = (List.range n).map (fun i => x (i + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xPrefix_succ, ih, List.range_succ, List.map_append]
    rfl

lemma y_succ (n : ℕ) : y (n + 1) = (xPrefix n).count (x (n + 1)) := by
  unfold y
  rw [Nat.add_sub_cancel, xPrefix_succ]
  have ht : (xPrefix n ++ [x (n + 1)]).take n = xPrefix n := by
    simpa only [xPrefix_length] using
      (List.take_left (l₁ := xPrefix n) (l₂ := [x (n + 1)]))
  rw [ht]

lemma y_xor (n : ℕ) : y (n + 1) = x (n + 1) ^^^ x (n + 2) := by
  rw [x_step, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

lemma xor_cancel (u v : ℕ) : u ^^^ v ^^^ v = u := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

lemma telescope (m j c : ℕ) :
    ((List.range' j m).map (fun t => y (t + 1))).foldl (· ^^^ ·) c =
      c ^^^ x (j + 1) ^^^ x (j + m + 1) := by
  induction m generalizing j c with
  | zero => simp
  | succ m ih =>
    rw [List.range'_succ, List.map_cons, List.foldl_cons, ih, y_xor]
    simp only [← Nat.xor_assoc, xor_cancel]
    congr 2
    omega

lemma suffix_xor (n j : ℕ) (hj : j ≤ n) :
    (((List.range n).map (fun i => y (i + 1))).drop j).foldl (· ^^^ ·) 0 =
      x (j + 1) ^^^ x (n + 1) := by
  rw [← List.map_drop, List.range_eq_range', List.drop_range']
  simp only [Nat.mul_one, Nat.zero_add, telescope, Nat.zero_xor]
  congr 2
  omega

lemma suffix_count (n : ℕ) :
    ((List.range n).filter (fun j =>
      (((List.range n).map (fun i => y (i + 1))).drop j).foldl (· ^^^ ·) 0 = 0)).length =
      y (n + 1) := by
  rw [y_succ, xPrefix_map, List.count_eq_countP, List.countP_map,
    List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt (List.mem_range.mp hj)
  apply Bool.eq_iff_iff.mpr
  simp [suffix_xor n j hjn]

lemma aPrefix_map (n : ℕ) :
    aPrefix n = (List.range n).map (fun i => y (i + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [aPrefix, ih, suffix_count, List.range_succ, List.map_append]
    rfl

end OMA.A336033Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a336033.main := by
  intro n hn
  rw [a, OMA.A336033Proof.aPrefix_map]
  rw [List.getD_eq_getElem _ _ (by simpa using (show n - 1 < n by omega))]
  simp only [List.getElem_map, List.getElem_range]
  congr 1
  omega
