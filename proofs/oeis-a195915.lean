import OMAStatements.S_oeis_a195915

/-!
The power-of-two shift for A195915. The recurrence and cancellation
argument follow the earlier proofs by @dwilfand-sys and @Ksungwon09.
The triangle was formalized by @senamakel. Source: https://oeis.org/A195915
-/

open OMA.S_oeis_a195915

private lemma outside : ∀ n k : ℕ, n ≤ k → entry n k = 0
  | 0, _, _ => rfl
  | n+1, 0, h => by omega
  | n+1, k+1, h => by
    simp [entry, outside n k (by omega), outside n (k+1) (by omega)]

private lemma shift (j n k : ℕ) :
    entry (n+2^j) (k+2^j) = entry n k ^^^ entry n (k+2^j) := by
  induction j generalizing n k with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ, Nat.mul_two, ← Nat.add_assoc]
    rw [ih (n+2^j) (k+2^j), ih n k, ih n (k+2^j)]
    generalize entry n (k+2^j) = b
    rw [Nat.xor_assoc, ← Nat.xor_assoc b b, Nat.xor_self, Nat.zero_xor]

theorem OMA.solution : type_of% @OMA.S_oeis_a195915.main := by
  intro j n k _ hn
  rw [Nat.add_comm (2^j) n, Nat.add_comm (2^j) k, shift,
    outside n (k+2^j) (by omega), Nat.xor_zero]
