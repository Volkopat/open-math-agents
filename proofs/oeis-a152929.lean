import OMAStatements.S_oeis_a152929

-- Proof of the statement in #26823 (statement by @ivillar). Credit for the proof: @bnb9001
-- Both sides satisfy the Fibonacci recurrence and agree at n = 1, 2.

namespace OMA_OEIS_A152929_Proof

open OMA.S_oeis_a152929

theorem two (n : ℕ) : 2 * a (n + 1) = 163 * (Nat.fib (n + 1) : ℤ) + 63 * lucas (n + 1) ∧
    2 * a (n + 2) = 163 * (Nat.fib (n + 2) : ℤ) + 63 * lucas (n + 2) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have ha : a (n + 3) = a (n + 2) + a (n + 1) := rfl
    have hl : lucas (n + 3) = lucas (n + 2) + lucas (n + 1) := rfl
    have hf : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    rw [show n + 1 + 2 = n + 3 by ring, ha, hl, hf]
    push_cast
    linarith [ih.1, ih.2]

theorem stmt' : ∀ n : ℕ, 1 ≤ n →
    2 * a n = 163 * (Nat.fib n : ℤ) + 63 * lucas n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (two m).1

end OMA_OEIS_A152929_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a152929.main := OMA_OEIS_A152929_Proof.stmt'
