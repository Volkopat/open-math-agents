import OMAStatements.S_oeis_a008749
import Mathlib

/-!
# OEIS A008749: first differences of the coefficients of `(1 + x⁶)/((1 - x)(1 - x²)(1 - x³))`

Since `(1 - x)(1 - x²)(1 - x³) = 1 - x - x² + x⁴ + x⁵ - x⁶`, the hypothesis says, coefficient by
coefficient,

  `f(m) = f(m-1) + f(m-2) - f(m-4) - f(m-5) + f(m-6) + [m = 0] + [m = 6]`.

This gives `f(0), …, f(6) = 1, 1, 2, 3, 4, 5, 8` and, for `k ≥ 0`,
`f(k+7) - f(k+6) = (f(k+5) - f(k+3)) - (f(k+2) - f(k+1))`.

The claim `f(n+1) = f(n) + b(n)` follows by strong induction: the first seven cases are the
values above, and the step is the identity `b(k+6) = b(k+4) + b(k+3) - b(k+1)`, which is checked
by cases on `k mod 6`.
-/

open PowerSeries OMA.S_oeis_a008749

namespace OMA.A008749

/-- The coefficient of `xⁿ` in `c xⁱ φ`. -/
lemma coeff_term (c : ℤ) (i n : ℕ) (φ : ℤ⟦X⟧) :
    coeff n (((c : ℤ) : ℤ⟦X⟧) * X ^ i * φ) = if i ≤ n then c * coeff (n - i) φ else 0 := by
  rw [mul_assoc, ← eq_intCast (C : ℤ →+* ℤ⟦X⟧) c, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

/-- The identity satisfied by the conjectured differences. -/
lemma bSeq_id (k : ℕ) :
    (bSeq (k + 6) : ℤ) = bSeq (k + 4) + bSeq (k + 3) - bSeq (k + 1) := by
  have e : ∀ j, bSeq (j + 1) = 2 * (j / 6) + 1 + if (j + 2) % 6 = 0 then 2 else 0 :=
    fun j => rfl
  rw [show k + 6 = (k + 5) + 1 from rfl, e, show k + 4 = (k + 3) + 1 from rfl, e,
    show k + 3 = (k + 2) + 1 from rfl, e, e]
  push_cast
  split_ifs <;> omega

end OMA.A008749

open OMA.A008749 in
theorem OMA.solution : type_of% @OMA.S_oeis_a008749.main := by
  intro f h
  -- the hypothesis, term by term
  have hT : ((1 : ℤ) : ℤ⟦X⟧) * X ^ 0 * f + (((-1) : ℤ) : ℤ⟦X⟧) * X ^ 1 * f
      + (((-1) : ℤ) : ℤ⟦X⟧) * X ^ 2 * f + ((1 : ℤ) : ℤ⟦X⟧) * X ^ 4 * f
      + ((1 : ℤ) : ℤ⟦X⟧) * X ^ 5 * f + (((-1) : ℤ) : ℤ⟦X⟧) * X ^ 6 * f
      = ((1 : ℤ) : ℤ⟦X⟧) * X ^ 0 * 1 + ((1 : ℤ) : ℤ⟦X⟧) * X ^ 6 * 1 := by
    linear_combination (norm := (push_cast; ring)) h
  have key : ∀ m : ℕ,
      (if 0 ≤ m then 1 * coeff (m - 0) f else 0) + (if 1 ≤ m then -1 * coeff (m - 1) f else 0)
        + (if 2 ≤ m then -1 * coeff (m - 2) f else 0) + (if 4 ≤ m then 1 * coeff (m - 4) f else 0)
        + (if 5 ≤ m then 1 * coeff (m - 5) f else 0) + (if 6 ≤ m then -1 * coeff (m - 6) f else 0)
      = (if 0 ≤ m then 1 * (if m - 0 = 0 then (1 : ℤ) else 0) else 0)
        + (if 6 ≤ m then 1 * (if m - 6 = 0 then (1 : ℤ) else 0) else 0) := by
    intro m
    have hm := congrArg (coeff m) hT
    simpa only [map_add, coeff_term, coeff_one] using hm
  -- the first values
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  have h4 := key 4
  have h5 := key 5
  have h6 := key 6
  norm_num [-PowerSeries.coeff_zero_eq_constantCoeff] at h0 h1 h2 h3 h4 h5 h6
  -- the recurrence beyond the degree of the right-hand side
  have hrec : ∀ k : ℕ, coeff (k + 7) f
      = coeff (k + 6) f + coeff (k + 5) f - coeff (k + 3) f - coeff (k + 2) f
        + coeff (k + 1) f := by
    intro k
    have hk := key (k + 7)
    simp at hk
    linarith
  refine ⟨by linarith, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 6 with hn | hn
    · -- the first six differences
      have hb : bSeq 0 = 0 ∧ bSeq 1 = 1 ∧ bSeq 2 = 1 ∧ bSeq 3 = 1 ∧ bSeq 4 = 1 ∧ bSeq 5 = 3 := by
        decide
      obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hb
      interval_cases n
      · rw [b0]; push_cast; linarith
      · rw [b1]; push_cast; linarith
      · rw [b2]; push_cast; linarith
      · rw [b3]; push_cast; linarith
      · rw [b4]; push_cast; linarith
      · rw [b5]; push_cast; linarith
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have i4 := ih (k + 4) (by omega)
      have i3 := ih (k + 3) (by omega)
      have i1 := ih (k + 1) (by omega)
      have hid := bSeq_id k
      rw [show k + 6 + 1 = k + 7 by omega, hrec k]
      rw [show k + 4 + 1 = k + 5 by omega] at i4
      rw [show k + 3 + 1 = k + 4 by omega] at i3
      rw [show k + 1 + 1 = k + 2 by omega] at i1
      linarith
