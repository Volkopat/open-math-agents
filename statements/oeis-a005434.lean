import Mathlib

/-!
# A005434: Number of distinct autocorrelations of binary words of length n

Source: https://oeis.org/A005434
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (OEIS): `a(n + 1) - a(n) < a(n + 13) - a(n + 12)` for all `n ≥ 1`.

## Encoding

* A binary word of length `n` is `w : Fin n → Bool`. Its autocorrelation is the set of its
  periods `p ∈ {0, …, n - 1}`: `p` is a period if `w j = w (j + p)` whenever `j + p < n`
  (so `0` is always a period). Recording it as a `Finset ℕ` loses nothing.
* `a n` is the number of distinct autocorrelations of binary words of length `n`.
-/

namespace OMA.S_oeis_a005434

/-- The autocorrelation (set of periods) of a binary word of length `n`. -/
def autocorrelation {n : ℕ} (w : Fin n → Bool) : Finset ℕ :=
  (Finset.range n).filter fun p => ∀ j : Fin n, ∀ h : (j : ℕ) + p < n, w j = w ⟨j + p, h⟩

/-- `a n`: the number of distinct autocorrelations of binary words of length `n`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.image (fun w : Fin n → Bool => autocorrelation w)).card

theorem main :
    ∀ n : ℕ, 1 ≤ n → (a (n + 1) : ℤ) - a n < (a (n + 13) : ℤ) - a (n + 12) := by
  sorry

end OMA.S_oeis_a005434
