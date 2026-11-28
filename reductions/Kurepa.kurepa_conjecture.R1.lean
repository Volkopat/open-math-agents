import FormalConjectures.Paper.Kurepa

-- Reduction Kurepa.kurepa_conjecture.R1 of Kurepa's conjecture
-- Credit: @Miura-KR
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Kurepa's conjecture: a finite check up to `50000` and the open core for larger primes

`!n = 0! + 1! + ⋯ + (n-1)!`. By `Kurepa.kurepa_conjecture.prime_reduction` (proved in the source
file) it suffices to treat primes `p > 2`. We split them by size.

* `H1` (a finite check): `(!n) % n ≠ 0` for every `2 < n ≤ 50000`. It is stated for all `n`, not
  only primes, so its proof needs no primality test: a single pass `i = 0, 1, …, 50000` carrying
  `i!` and `!i` modulo `lcm(1, …, 50000)` (which every such `n` divides) and testing `!i mod i`
  at each step. A kernel `decide` of this pass takes about 20 seconds; a checked proof of the step
  is ready and will be sent once this reduction is merged.
* `H2` (open core): `(!p) % p ≠ 0` for every prime `p > 50000`.

`main` is `H1 → H2 → target`, and `lossless` shows the target implies both, so nothing is lost.

Status. Computations have verified the conjecture for all `p < 2^34` (Andrejić–Tatarevic, Math.
Comp. 85 (2016)) and `p < 2^40` (Andrejić–Bostan–Tatarevic, Inform. Process. Lett. 2021). Claimed
proofs by Barsky–Benzaghou (2004) and by Abramov (arXiv:2209.12677) were withdrawn. The source
file kernel-checks `n < 50`; `H1` extends the kernel-checked range to `n ≤ 50000`.
-/

namespace OMA.R_Kurepa_kurepa_conjecture_R1

open Kurepa

/-- Kurepa's congruence holds for every `n` with `2 < n ≤ 50000`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → n ≤ 50000 → left_factorial n % n ≠ 0

/-- Kurepa's congruence holds for every prime `p > 50000`. -/
def H2 : Prop :=
  ∀ p : ℕ, 50000 < p → p.Prime → left_factorial p % p ≠ 0

theorem main : H1 → H2 → type_of% @Kurepa.kurepa_conjecture := by
  intro h1 h2 n hn
  refine Kurepa.kurepa_conjecture.prime_reduction.mpr (fun p hp hpp => ?_) n hn
  rcases Nat.lt_or_ge 50000 p with h | h
  · exact h2 p h hpp
  · exact h1 p hp h

/-- The reduction loses nothing: the target implies `H1` and `H2`. -/
theorem lossless : type_of% @Kurepa.kurepa_conjecture → H1 ∧ H2 :=
  fun ht => ⟨fun n hn _ => ht n hn, fun p hp _ => ht p (by omega)⟩

end OMA.R_Kurepa_kurepa_conjecture_R1
