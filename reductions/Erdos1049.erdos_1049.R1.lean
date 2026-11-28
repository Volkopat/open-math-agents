import FormalConjectures.ErdosProblems.«1049»

/-!
Reduction Erdos1049.erdos_1049.R1 of Erdős Problem 1049 (Chowla's conjecture: for rational
`t > 1` the Lambert series `∑ 1/(t^n - 1) = ∑ τ(n)/t^n` is irrational).

Split by the shape of the rational number `t > 1`:
* `H1` is the integer case `t ∈ ℤ`, `t ≥ 2`. This was proved by Erdős
  (On arithmetical properties of Lambert series, J. Indian Math. Soc. 1948); it is the upstream
  variant `erdos_1049.variants.geq_2_integer` and is not in Mathlib.
* `H2` is the non-integer case (`t` rational, `t > 1`, `t` not an integer), the genuinely open
  part of the conjecture.
Neither case implies the other. `main` splits on whether `t` equals an integer `m`; in that case
`m > 1` forces `m ≥ 2` and the real casts agree.
-/

-- Credit: @sntntHb

namespace OMA.R_Erdos1049_erdos_1049_R1

/-- Erdős (1948): the integer case. -/
def H1 : Prop :=
  ∀ t : ℤ, t ≥ 2 → Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1))

/-- The open part: rational `t > 1` that is not an integer. -/
def H2 : Prop :=
  ∀ t : ℚ, t > 1 → (∀ m : ℤ, t ≠ (m : ℚ)) →
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1))

theorem main : H1 → H2 → type_of% @Erdos1049.erdos_1049 := by
  intro h1 h2 t ht
  by_cases hint : ∃ m : ℤ, t = (m : ℚ)
  · obtain ⟨m, rfl⟩ := hint
    have hm : (1 : ℚ) < (m : ℚ) := ht
    have hm2 : m ≥ 2 := by
      have : (1 : ℤ) < m := by exact_mod_cast hm
      omega
    have key := (show H1 from h1) m hm2
    simpa [Rat.cast_intCast] using key
  · push_neg at hint
    exact (show H2 from h2) t ht hint

end OMA.R_Erdos1049_erdos_1049_R1
