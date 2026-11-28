import OMAStatements.S_mo_214595
import Mathlib

-- Reduction mo-214595.R1 of Between Fermat's primes and the twin primes.
-- Credit: @marcusbuffett

/-!
# Covering congruences leave only exponents `r ≡ 3 (mod 6)`

For `N_k(r) = 10^(2^r) + k`, `k ∈ {1, 3, 7, 9}`, three small primes rule out every `r ≥ 2`
outside one residue class modulo 6 (classical covering-congruence argument):

* `r` even, `r ≥ 2`: `2^r ≡ 4 (mod 6)` and `10` has order `6` modulo `7`, so
  `10^(2^r) ≡ 10^4 ≡ 4 (mod 7)` and `7 ∣ 10^(2^r) + 3`.
* `r ≡ 5 (mod 6)`: `2^r ≡ 14 (mod 18)` and `10` has order `18` modulo `19`, so
  `10^(2^r) ≡ 10^14 ≡ 16 (mod 19)` and `19 ∣ 10^(2^r) + 3`.
* `r ≡ 1 (mod 6)`, `r ≥ 7`: `2^r ≡ 16 (mod 112)` and `10` has order `112` modulo `113`, so
  `10^(2^r) ≡ 10^16 ≡ 106 (mod 113)` and `113 ∣ 10^(2^r) + 7`.

* `H1` (proved in the step): for `r ≥ 2` with `r % 6 ≠ 3` one of the four numbers is composite.
* `H2` (open core): only finitely many `r ≡ 3 (mod 6)` make all four numbers prime.

`r = 0` and `r = 1` (giving `11, 13, 17, 19` and `101, 103, 107, 109`) are the known examples;
this is the covering part of the problem, not progress on the open class `r ≡ 3 (mod 6)`.
-/

namespace OMA.R_mo_214595_R1

/-- Covering congruences by `7`, `19` and `113` (classical, elementary). -/
def H1 : Prop :=
  ∀ r : ℕ, 2 ≤ r → r % 6 ≠ 3 → ∃ k ∈ ({1, 3, 7, 9} : Finset ℕ), ¬ (10 ^ 2 ^ r + k).Prime

/-- The open core: finitely many `r ≡ 3 (mod 6)` with all four numbers prime. -/
def H2 : Prop :=
  Set.Finite {r : ℕ | r % 6 = 3 ∧ ∀ k ∈ ({1, 3, 7, 9} : Finset ℕ), (10 ^ 2 ^ r + k).Prime}

theorem main : H1 → H2 → type_of% @OMA.S_mo_214595.main := by
  intro h1 h2
  refine ((h2.insert 1).insert 0).subset ?_
  intro r hr
  simp only [Set.mem_ofPred_eq] at hr
  simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
  by_cases hr2 : r < 2
  · omega
  · right; right
    refine ⟨?_, hr⟩
    by_contra h6
    obtain ⟨k, hk, hnp⟩ := h1 r (by omega) h6
    exact hnp (hr k hk)

end OMA.R_mo_214595_R1
