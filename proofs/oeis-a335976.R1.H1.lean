import OMAReductions.R_oeis_a335976_R1

/-!
Proof of `OMA.R_oeis_a335976_R1.H1`.
This is the classical law of apparition for Fibonacci numbers: for a prime `q ≠ 2, 5`,
`q` divides `F (q - 1)` when `5` is a square modulo `q`, and `F (q + 1)` otherwise. It is the
lemma `fibonacci_prime_law` proved (via Binet's formula and Frobenius) in the reduction file.
-/

theorem OMA.solution : OMA.R_oeis_a335976_R1.H1 :=
  fun q hq h2 h5 => OMA.R_oeis_a335976_R1.fibonacci_prime_law q hq h2 h5
