import Mathlib

/-!
# Parseval's identity for the negacyclic polynomial ring

Source: https://mathoverflow.net/questions/487715 . The question asks for the
first identity in the proof of Lemma 6 of the May 2023 HAETAE specification,
https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/round-1/spec-files/haetae-spec-web.pdf .
With n a power of two, we evaluate at the n odd powers of a primitive 2n-th
root. The polynomial remainder gives the coefficient vector in ℤ[X]/(Xⁿ+1).
The squared coefficient norm of a vector is the sum of those of its entries.

Credit: @connoranderson
-/

namespace OMA.S_mo_487715
open Polynomial

noncomputable def frequency (ζ : ℂ) (i : ℕ) : ℂ := ζ^(2*i+1)

noncomputable def representative (n : ℕ) (f : ℤ[X]) : ℤ[X] := f %ₘ (X^n+1)

noncomputable def coefficientNormSq (n : ℕ) (f : ℤ[X]) : ℝ :=
  ∑ j ∈ Finset.range n, ‖(f.coeff j : ℂ)‖^2

theorem main : ∀ d : ℕ, let n := 2^d
    ∀ ζ : ℂ, IsPrimitiveRoot ζ (2*n) →
      (∀ i < n, IsPrimitiveRoot (frequency ζ i) (2*n)) ∧
      (∀ z : ℂ, z^n = -1 ↔ ∃ i < n, frequency ζ i = z) ∧
      ∀ m : ℕ, ∀ s : Fin m → ℤ[X], ∀ c : ℤ[X],
        (n:ℝ) * ∑ i, coefficientNormSq n (representative n (c*s i)) =
          ∑ j ∈ Finset.range n, ‖aeval (frequency ζ j) c‖^2 *
            ∑ i, ‖aeval (frequency ζ j) (s i)‖^2 := by
  sorry

end OMA.S_mo_487715
