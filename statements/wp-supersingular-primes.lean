import Mathlib

/-!
# Lang–Trotter conjecture on supersingular primes

Source: https://en.wikipedia.org/wiki/Supersingular_prime_(algebraic_number_theory)
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Lang and Trotter's conjecture: for an elliptic curve `E` over `ℚ` without complex
multiplication, the number of supersingular primes `p ≤ X` of `E` is within a constant multiple
of `√X / ln X`.

## Encoding

* `E` is given by a short Weierstrass equation `y² = x³ + A x + B` with `A, B ∈ ℤ` and
  `4A³ + 27B² ≠ 0`; every elliptic curve over `ℚ` has such a model, and changing the model only
  changes finitely many primes.
* Only primes `p ≥ 5` not dividing `4A³ + 27B²` are counted (finitely many exceptions, which do
  not affect the asymptotic statement). Such a `p` is supersingular iff `a_p = 0`, i.e.
  `#E(𝔽_p) = p + 1`, i.e. the affine equation has exactly `p` solutions in `𝔽_p²`.
* `E` has CM iff its `j`-invariant `1728 · 4A³ / (4A³ + 27B²)` is one of the 13 rational CM
  `j`-invariants (class number one orders).
* "Within a constant multiple" is read as `Θ`: there are constants `0 < c₁ ≤ c₂` with
  `c₁ √X / log X ≤ π_ss(X) ≤ c₂ √X / log X` for all large `X`.
-/

namespace OMA.S_wp_supersingular_primes

open Filter

/-- The thirteen `j`-invariants of elliptic curves over `ℚ` with complex multiplication. -/
def cmJ : Set ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -884736, -12288000, 16581375, -884736000,
    -147197952000, -262537412640768000}

/-- The `j`-invariant of `y² = x³ + A x + B`. -/
def jInv (A B : ℤ) : ℚ := 1728 * (4 * (A : ℚ) ^ 3) / (4 * (A : ℚ) ^ 3 + 27 * (B : ℚ) ^ 2)

/-- `p ≥ 5` is a prime of good reduction at which `y² = x³ + A x + B` is supersingular. -/
def IsSupersingular (A B : ℤ) (p : ℕ) : Prop :=
  p.Prime ∧ 5 ≤ p ∧ ¬ (p : ℤ) ∣ 4 * A ^ 3 + 27 * B ^ 2 ∧
    Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + A * xy.1 + B} = p

/-- The number of supersingular primes `p ≤ X`. -/
noncomputable def piSS (A B : ℤ) (X : ℝ) : ℕ :=
  Nat.card {p : ℕ // (p : ℝ) ≤ X ∧ IsSupersingular A B p}

theorem main :
    ∀ A B : ℤ, 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 → jInv A B ∉ cmJ →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ᶠ X in atTop,
        c₁ * Real.sqrt X / Real.log X ≤ piSS A B X ∧
          (piSS A B X : ℝ) ≤ c₂ * Real.sqrt X / Real.log X := by
  sorry

end OMA.S_wp_supersingular_primes
