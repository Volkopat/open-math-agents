import OMAStatements.S_oeis_a163250
import Mathlib

/-
A163250: a(n) = Fib(n+6) - (n^2 + 4n + 8), with natural-number subtraction, satisfies
a(n) = (n-1)^2 + a(n-1) + a(n-2) for n > 2.

- fib_ge: Fib(n+6) >= n^2 + 4n + 8 for all n (induction on n, two values at a time), so the
  subtraction never truncates.
- Then write n = m + 2, use Fib(m+8) = Fib(m+6) + Fib(m+7), and the rest is linear arithmetic
  once the squares are expanded.
-/

namespace OMA.P163250

lemma fib_ge : ∀ n : ℕ, n ^ 2 + 4 * n + 8 ≤ Nat.fib (n + 6) ∧
    (n + 1) ^ 2 + 4 * (n + 1) + 8 ≤ Nat.fib (n + 7) := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have h : Nat.fib (n + 8) = Nat.fib (n + 6) + Nat.fib (n + 7) := Nat.fib_add_two
    rw [show n + 1 + 7 = n + 8 by omega, h]
    nlinarith [h1, h2]

lemma main' (a : ℕ → ℕ) (ha : ∀ n, a n = Nat.fib (n + 6) - (n ^ 2 + 4 * n + 8)) :
    ∀ n : ℕ, n > 2 → a n = (n - 1) ^ 2 + a (n - 1) + a (n - 2) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h8 : Nat.fib (m + 8) = Nat.fib (m + 6) + Nat.fib (m + 7) := Nat.fib_add_two
  obtain ⟨b6, b7⟩ := fib_ge m
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, ha, ha, ha,
    show m + 2 + 6 = m + 8 by omega, show m + 1 + 6 = m + 7 by omega, h8]
  have e1 : (m + 2) ^ 2 = m ^ 2 + 4 * m + 4 := by ring
  have e2 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
  rw [e1, e2]
  rw [e2] at b7
  generalize m ^ 2 = s at b6 b7 ⊢
  omega

end OMA.P163250

theorem OMA.solution : type_of% @OMA.S_oeis_a163250.main :=
  OMA.P163250.main' OMA.S_oeis_a163250.a (fun _ => rfl)
