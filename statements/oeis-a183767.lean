import Mathlib

/-!
# A183767: 1/32 the number of (n+1) X 5 binary arrays with equal numbers of 2 X 2 subblocks with sum mod two being 0 and 1.

Source: https://oeis.org/A183767
Credit: @ceejcake

Formalizes Conjecture 1 of Peter Bala (Mar 11 2025) for OEIS A183767 (offset 1):
`a(n) = 2^n * binomial(4*n, 2*n)` for all `n ≥ 1`.
(The entry also lists a second Chebyshev polynomial conjecture, which is not included here.)

Conventions:
* An `(n + 1) × 5` binary array is modeled as `B : Fin (n + 1) → Fin 5 → ZMod 2`.
* Each `2 × 2` subblock indexed by `p : Fin n × Fin 4` has mod-2 sum
  `subblockParity n B p ∈ ZMod 2`.
* `rawCount n` counts arrays `B` for which the number of `2 × 2` subblocks with mod-2 sum `0`
  equals the number with mod-2 sum `1`.
* `a n = rawCount n / 32` (exact integer division since `32 ∣ rawCount n`).
* Matches OEIS A183767 DATA: `a(1) = 12`, `a(2) = 280`, `a(3) = 7392`, ...
-/

namespace OMA.S_oeis_a183767

/-- The `2 × 2` subblock mod-2 sum matrix of an `(n + 1) × 5` binary array. -/
def subblockParity (n : ℕ) (B : Fin (n + 1) → Fin 5 → ZMod 2) : Fin n × Fin 4 → ZMod 2 :=
  fun p => B ⟨p.1.1, by omega⟩ ⟨p.2.1, by omega⟩ + B ⟨p.1.1 + 1, by omega⟩ ⟨p.2.1, by omega⟩ +
    B ⟨p.1.1, by omega⟩ ⟨p.2.1 + 1, by omega⟩ + B ⟨p.1.1 + 1, by omega⟩ ⟨p.2.1 + 1, by omega⟩

/-- Number of `(n + 1) × 5` binary arrays with equal numbers of `2 × 2` subblocks having mod-2
sum `0` and `1`. -/
def rawCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun B : Fin (n + 1) → Fin 5 → ZMod 2 =>
    (Finset.univ.filter fun p : Fin n × Fin 4 => subblockParity n B p = 0).card =
    (Finset.univ.filter fun p : Fin n × Fin 4 => subblockParity n B p = 1).card).card

/-- OEIS A183767 (offset 1): `1/32` the number of valid `(n + 1) × 5` binary arrays. -/
def a (n : ℕ) : ℕ :=
  rawCount n / 32

/-- Conjecture 1 (Peter Bala, Mar 11 2025, OEIS A183767):
`a(n) = 2^n * binomial(4*n, 2*n)` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 2 ^ n * (4 * n).choose (2 * n) := by
  sorry

end OMA.S_oeis_a183767
