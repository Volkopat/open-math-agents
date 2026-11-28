import Mathlib

/-!
# Long rainbow arithmetic progressions

Source: https://www.openproblemgarden.org/op/long_rainbow_arithemtic_progressions
(J. Fox, V. Jungić, M. Mahdian, J. Nešetřil, R. Radoičić)
Credit: @ishaanzee

For `k ∈ ℕ` let `T_k` denote the minimal number `t ∈ ℕ` such that there is a rainbow `AP(k)` in
every equinumerous `t`-coloring of `{1, 2, …, tn}` for every `n ∈ ℕ`.

**Conjecture.** For all `k ≥ 3`, `T_k = Θ(k²)`.

A `t`-coloring of `{1, 2, …, tn}` is equinumerous if each color is used `n` times; an arithmetic
progression is rainbow if no two of its terms have the same color. It is known that
`⌊k²/4⌋ < T_k ≤ k(k-1)²/2`, so `T_k` is well defined.

Formalization:
* `{1, …, tn}` is represented by `Fin (t * n)` (the element `i` stands for `i + 1`), a
  `t`-coloring by `c : Fin (t * n) → Fin t`, and "equinumerous" says every color class has
  exactly `n` elements.
* An `AP(k)` is `a, a + d, …, a + (k - 1) d` with common difference `d ≥ 1`, all inside the
  interval; it is rainbow when `i ↦ c (a + i d)` is injective on `Fin k`.
* "For every `n ∈ ℕ`" means every `n ≥ 1` (for `n = 0` the interval is empty).
* `T_k = Θ(k²)` for `k ≥ 3`: there are constants `0 < c₁, c₂` with `c₁ k² ≤ T_k ≤ c₂ k²` for all
  `k ≥ 3`.
-/

namespace OMA.S_opg_long_rainbow_arithemtic_progressions

/-- Every equinumerous `t`-coloring of `{1, …, tn}`, for every `n ≥ 1`, contains a rainbow
arithmetic progression of length `k`. -/
def ForcesRainbowAP (k t : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ c : Fin (t * n) → Fin t,
    (∀ col : Fin t, (Finset.univ.filter fun i => c i = col).card = n) →
    ∃ a d : ℕ, 1 ≤ d ∧ ∃ h : a + (k - 1) * d < t * n,
      Function.Injective fun i : Fin k =>
        c ⟨a + i * d, lt_of_le_of_lt (by
          have := Nat.mul_le_mul_right d (Nat.le_sub_one_of_lt i.isLt)
          omega) h⟩

/-- `T_k`: the least `t` forcing a rainbow `AP(k)` in every equinumerous `t`-coloring. -/
noncomputable def T (k : ℕ) : ℕ := sInf {t : ℕ | ForcesRainbowAP k t}

/-- **Conjecture** (Fox–Jungić–Mahdian–Nešetřil–Radoičić): `T_k = Θ(k²)` for `k ≥ 3`. -/
theorem main : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 3 ≤ k →
    c₁ * (k : ℝ) ^ 2 ≤ (T k : ℝ) ∧ (T k : ℝ) ≤ c₂ * (k : ℝ) ^ 2 := by
  sorry

end OMA.S_opg_long_rainbow_arithemtic_progressions
