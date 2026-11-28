import OMAStatements.S_oeis_a173951
import Mathlib

namespace OMA.S_oeis_a173951.Sol

open OMA.S_oeis_a173951

lemma b_eq (n : ℕ) : b n + 4 = 4 * 9 ^ n := by
  induction n with
  | zero => simp [b]
  | succ n ih => simp only [b, pow_succ]; omega

lemma ofDigits_rep (k : ℕ) : Nat.ofDigits 3 (List.replicate k 2) + 1 = 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    omega

/-- Little-endian digits of `b (m+1)`. -/
def L (m : ℕ) : List ℕ := [2, 1] ++ List.replicate (2 * m) 2 ++ [0, 1]

lemma ofDigits_L (m : ℕ) : Nat.ofDigits 3 (L m) = b (m + 1) := by
  have h1 := b_eq (m + 1)
  have h2 := ofDigits_rep (2 * m)
  simp only [L, Nat.ofDigits_append, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, Nat.ofDigits_cons, Nat.ofDigits_nil] at *
  have h3 : (9 : ℕ) ^ (m + 1) = 9 * 3 ^ (2 * m) := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h3] at h1
  have h4 : (3 : ℕ) ^ (0 + 1 + 1 + 2 * m) = 9 * 3 ^ (2 * m) := by
    rw [show 0 + 1 + 1 + 2 * m = 2 * m + 2 by omega, pow_add]; norm_num; ring
  rw [h4]
  have h5 : (3 : ℕ) ^ (0 + 1 + 1) = 9 := by norm_num
  rw [h5]
  nlinarith

lemma digits_b (m : ℕ) : Nat.digits 3 (b (m + 1)) = L m := by
  rw [← ofDigits_L]
  apply Nat.digits_ofDigits _ (by norm_num)
  · intro l hl
    simp only [L, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil,
      or_false] at hl
    rcases hl with ((h | h) | ⟨-, h⟩) | h | h <;> omega
  · intro _
    simp [L]

lemma rev_val (m : ℕ) : Nat.ofDigits 3 (L m).reverse = 2 * b (m + 1) := by
  have h1 := b_eq (m + 1)
  have h2 := ofDigits_rep (2 * m)
  have hr : (L m).reverse = [1, 0] ++ List.replicate (2 * m) 2 ++ [1, 2] := by
    simp [L, List.reverse_replicate]
  rw [hr]
  simp only [Nat.ofDigits_append, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, Nat.ofDigits_cons, Nat.ofDigits_nil] at *
  have h3 : (9 : ℕ) ^ (m + 1) = 9 * 3 ^ (2 * m) := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h3] at h1
  have h4 : (3 : ℕ) ^ (0 + 1 + 1 + 2 * m) = 9 * 3 ^ (2 * m) := by
    rw [show 0 + 1 + 1 + 2 * m = 2 * m + 2 by omega, pow_add]; norm_num; ring
  rw [h4]
  have h5 : (3 : ℕ) ^ (0 + 1 + 1) = 9 := by norm_num
  rw [h5]
  nlinarith

theorem sol : ∀ n : ℕ, 1 ≤ n → b n ∈ A173951 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_⟩
  · have := b_eq (m + 1)
    have : 4 ≤ 4 * 9 ^ (m + 1) - 4 := by
      have : 9 ≤ 9 ^ (m + 1) := Nat.le_self_pow (by omega) 9
      omega
    omega
  · rw [digits_b, rev_val]

end OMA.S_oeis_a173951.Sol

theorem OMA.solution : type_of% @OMA.S_oeis_a173951.main := OMA.S_oeis_a173951.Sol.sol
