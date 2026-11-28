import OMAReductions.R_Fermat_fermat_number_are_composite_R1

-- Reduction Fermat.fermat_number_are_composite.R1.H2.R1 of step Fermat.fermat_number_are_composite.R1.H2
-- Credit: @marcusbuffett

/-!
# Composite Fermat numbers beyond `F_19`: the cases with a small known factor, and the open rest

The parent step says that `F_n = 2^(2^n) + 1` is composite for every `n ≥ 20`.

* `H1` (known cases): `F_n` is composite for the 52 values of `n` between `21` and `298` listed
  in the statement. Each has a known factor of the form `k * 2^m + 1` (Fermat number factoring
  status, Keller's tables); the factors used were recomputed for this file. Proving `H1` means
  checking `2^(2^n) ≡ -1` modulo the factor, by `n` modular squarings.
* `H2`: the remaining `n ≥ 20`. This is open: for instance `F_20` and `F_24` are known to be
  composite only through Pépin's test and no factor is known, and nothing is known for most
  large `n`.
-/

namespace OMA.R_Fermat_fermat_number_are_composite_R1_H2_R1

/-- The listed Fermat numbers are composite. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 36, 37, 38, 39, 42, 43, 48, 52, 55, 58, 61, 62, 63, 64, 66, 71, 72, 73, 75, 77, 81, 91, 99, 107, 117, 122, 125, 142, 144, 146, 147, 150, 207, 226, 228, 250, 255, 267, 268, 284, 298} : Finset ℕ) →
    ¬ Prime n.fermatNumber

/-- The open part: every other `n ≥ 20`. -/
def H2 : Prop :=
  ∀ n : ℕ, 20 ≤ n → n ∉ ({21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 36, 37, 38, 39, 42, 43, 48, 52, 55, 58, 61, 62, 63, 64, 66, 71, 72, 73, 75, 77, 81, 91, 99, 107, 117, 122, 125, 142, 144, 146, 147, 150, 207, 226, 228, 250, 255, 267, 268, 284, 298} : Finset ℕ) →
    ¬ Prime n.fermatNumber

theorem main : H1 → H2 → OMA.R_Fermat_fermat_number_are_composite_R1.H2 := by
  intro h1 h2 n hn
  by_cases hmem : n ∈ ({21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 36, 37, 38, 39, 42, 43, 48, 52, 55, 58, 61, 62, 63, 64, 66, 71, 72, 73, 75, 77, 81, 91, 99, 107, 117, 122, 125, 142, 144, 146, 147, 150, 207, 226, 228, 250, 255, 267, 268, 284, 298} : Finset ℕ)
  · exact h1 n hmem
  · exact h2 n hn hmem

end OMA.R_Fermat_fermat_number_are_composite_R1_H2_R1
