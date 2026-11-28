import OMAReductions.R_SternPrime_isSternPrime_iff_R1

-- Reduction SternPrime.isSternPrime_iff.R1.H1.R1 of step SternPrime.isSternPrime_iff.R1.H1
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Stern primes: the searched range and the open tail

The parent step says that every Stern prime is one of the eight known ones

  2, 3, 17, 137, 227, 977, 1187, 1493,

i.e. that no ninth Stern prime exists. A prime is Stern when it has no decomposition `p + 2 * b ^ 2`
with `p` prime and `b ≥ 1`, so deciding one candidate is a finite check; the difficulty is that the
statement has to hold for every natural number at once.

The literature records how far the search goes. McCranie checked the first 100000 primes and Chaffin
checked every number below `2 * 10 ^ 13` (recorded in OEIS A042978); no ninth example was found. So
the statement splits at that bound:

* `H1` (searched range): every Stern prime `q` with `q < 2 * 10 ^ 13` is one of the eight. This is
  the finite part. Each `q` is decided by checking finitely many `b`, and the range is covered by a
  single computation, so in principle this half is a machine computation rather than mathematics.
* `H2` (the open tail): every Stern prime `q` with `2 * 10 ^ 13 ≤ q` is one of the eight. Nothing is
  known here; Euler's representation heuristic even suggests that the eight are all of them, which is
  exactly what `H2` says.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split.
-/

namespace OMA.R_SternPrime_isSternPrime_iff_R1_H1_R1

/-- The searched range: below `2 * 10 ^ 13` there is no ninth Stern prime (Chaffin, OEIS A042978). -/
def H1 : Prop :=
  ∀ q : ℕ, q < 20000000000000 → SternPrime.IsSternPrime q →
    q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ)

/-- The open tail: no ninth Stern prime at or above `2 * 10 ^ 13`. -/
def H2 : Prop :=
  ∀ q : ℕ, 20000000000000 ≤ q → SternPrime.IsSternPrime q →
    q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ)

theorem main : H1 → H2 → OMA.R_SternPrime_isSternPrime_iff_R1.H1 := by
  intro h1 h2 q hq
  by_cases h : q < 20000000000000
  · exact h1 q h hq
  · exact h2 q (Nat.le_of_not_lt h) hq

end OMA.R_SternPrime_isSternPrime_iff_R1_H1_R1
