import Mathlib

/-!
# Integer points in the intersection of two real row spaces

Source: Turbo, “Is this set empty?”, MathOverflow 265886 (2017, CC BY-SA 3.0),
https://mathoverflow.net/questions/265886/is-this-set-empty.

The matrices have `m = n - 1` rows and `m + 1 = n` columns. Their entries
come from integers. Row independence expresses full row rank, and the spans
are taken over the reals. The vector in their intersection has integer
coordinates and is required to be nonzero.
-/

namespace OMA.S_mo_265886

/-- The real rows of the integer matrix with diagonal entries `c` and
superdiagonal entries `-d`. -/
def bidiagonalRows {m : ℕ} (c d : Fin m → ℤ) : Fin m → Fin (m + 1) → ℝ :=
  fun i j => if j.val = i.val then (c i : ℝ)
             else if j.val = i.val + 1 then -(d i : ℝ)
             else 0

theorem main : ∀ (m : ℕ) (T : ℝ) (c d e f : Fin m → ℤ),
    LinearIndependent ℝ (bidiagonalRows c d) →
    LinearIndependent ℝ (bidiagonalRows e f) →
    (∀ i, T < |(c i : ℝ)| ∧ T < |(d i : ℝ)| ∧
      T ^ 2 < |(e i : ℝ)| ∧ T ^ 2 < |(f i : ℝ)|) →
    (∀ i, Int.gcd (c i) (d i) = 1 ∧ Int.gcd (e i) (f i) = 1) →
    Int.gcd (∏ i, c i * d i) (∏ i, e i * f i) = 1 →
    ∀ v : Fin (m + 1) → ℤ, v ≠ 0 →
    (fun i => (v i : ℝ)) ∈ Submodule.span ℝ (Set.range (bidiagonalRows c d)) →
    (fun i => (v i : ℝ)) ∈ Submodule.span ℝ (Set.range (bidiagonalRows e f)) →
    ∃ i, T ^ 2 < |(v i : ℝ)| := by
  sorry

end OMA.S_mo_265886
