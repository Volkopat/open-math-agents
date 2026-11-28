import OMAStatements.S_oeis_a001354
import Mathlib

/-!
# A001354: coordination sequence of the `3⁷` tessellation and even-indexed Fibonacci numbers

Both `coordination (k + 1)` and `7 * F(2k + 2)` satisfy `u(k + 2) = 3 u(k + 1) - u(k)`
(for Fibonacci numbers this is `F(m + 4) + F(m) = 3 F(m + 2)`) and they agree for `k = 0, 1`
(`7 = 7 F(2)`, `21 = 7 F(4)`).  The second claim is `F(2k + 2) = F(2k) + F(2k + 1)`.
-/

namespace OMA.S_oeis_a001354

/-- `F(m + 4) + F(m) = 3 F(m + 2)`. -/
lemma fib_add_four (m : ℕ) : Nat.fib (m + 4) + Nat.fib m = 3 * Nat.fib (m + 2) := by
  have h1 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have h2 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have h3 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
  omega

/-- `coordination (k + 1) = 7 F(2k + 2)`. -/
lemma coordination_succ (k : ℕ) : coordination (k + 1) = 7 * Nat.fib (2 * k + 2) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have hrec : coordination (k + 3) = 3 * coordination (k + 2) - coordination (k + 1) := rfl
    have h := fib_add_four (2 * k + 2)
    have e1 : 2 * (k + 1) + 2 = 2 * k + 2 + 2 := by ring
    have e2 : 2 * (k + 1 + 1) + 2 = 2 * k + 2 + 4 := by ring
    rw [e1] at ih2
    rw [e2, hrec, ih1, ih2]
    omega

end OMA.S_oeis_a001354

open OMA.S_oeis_a001354 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001354.main := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 := coordination_succ j
  have h2 := coordination_succ (j + 1)
  have e1 : 2 * (j + 1) = 2 * j + 2 := by ring
  have e2 : 2 * (j + 1) + 2 = 2 * j + 2 + 2 := by ring
  have hf : Nat.fib (2 * j + 2 + 2) = Nat.fib (2 * j + 2) + Nat.fib (2 * j + 2 + 1) :=
    Nat.fib_add_two
  rw [e2] at h2
  rw [e1]
  exact ⟨h1, by omega⟩
