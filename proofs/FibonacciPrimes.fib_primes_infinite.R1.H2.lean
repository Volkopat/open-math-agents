import OMAReductions.R_FibonacciPrimes_fib_primes_infinite_R1
import Mathlib.Tactic

-- Step FibonacciPrimes.fib_primes_infinite.R1.H2: hypothesis H2 of reduction FibonacciPrimes.fib_primes_infinite.R1
-- Credit: @keiichisince1986-bot
-- H2 := {n : ℕ | n.fib.Prime}.Infinite ↔     {n : ℕ | (∃ m : ℕ, m.fib = n) ∧ n.Prime}.Infinite

theorem OMA.solution : OMA.R_FibonacciPrimes_fib_primes_infinite_R1.H2 := by
  change {n : ℕ | n.fib.Prime}.Infinite ↔ {n : ℕ | (∃ m : ℕ, m.fib = n) ∧ n.Prime}.Infinite
  simp only [Set.infinite_iff_exists_gt]
  constructor
  · intro h a
    rcases h (a + 1) with ⟨b, hb₁, hb₂⟩
    refine ⟨Nat.fib b, ⟨⟨b, rfl⟩, hb₁⟩, ?_⟩
    have hle : b ≤ Nat.fib b + 1 := b.le_fib_add_one
    omega
  · intro h a
    rcases h (Nat.fib a) with ⟨b, ⟨⟨m, rfl⟩, hb₁⟩, hb₂⟩
    refine ⟨m, hb₁, ?_⟩
    by_contra hle
    have hmono : Nat.fib m ≤ Nat.fib a := Nat.fib_mono (by omega)
    omega


