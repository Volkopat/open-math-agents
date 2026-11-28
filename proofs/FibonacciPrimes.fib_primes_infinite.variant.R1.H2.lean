import OMAReductions.R_FibonacciPrimes_fib_primes_infinite_variant_R1

/-!
Proof of `OMA.R_FibonacciPrimes_fib_primes_infinite_variant_R1.H2`.
Every index satisfies `b ≤ fib b + 1`; this is Mathlib's `Nat.le_fib_add_one`, proved by
induction from `fib (n + 2) = fib n + fib (n + 1)`.
-/

theorem OMA.solution : OMA.R_FibonacciPrimes_fib_primes_infinite_variant_R1.H2 :=
  Nat.le_fib_add_one
