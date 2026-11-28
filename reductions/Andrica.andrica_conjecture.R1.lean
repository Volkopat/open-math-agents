import FormalConjectures.Wikipedia.Andrica
import Mathlib

-- Reduction Andrica.andrica_conjecture.R1 of Andrica's conjecture
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Andrica's conjecture from the two halves of Oppermann's conjecture

* `H1`: for every `x ≥ 2` there is a prime strictly between `x (x - 1)` and `x ^ 2`
  (first half of Oppermann's conjecture, catalogued as `Oppermann.oppermann_conjecture.parts.i`).
* `H2`: for every `x ≥ 2` there is a prime strictly between `x ^ 2` and `x (x + 1)`
  (second half, `Oppermann.oppermann_conjecture.parts.ii`).

Both halves already have reductions in this repository whose finite ranges `x ≤ 1000` are
settled, so only their large-`x` parts remain open.

Sketch of `main` (the classical passage Oppermann ⇒ Andrica; the same elementary argument
appears in the merged step of the variant `ferreira_large_n`): let `p = p_n`,
`x = ⌊√p⌋ ≥ 1`, so `x ^ 2 ≤ p < (x + 1) ^ 2`. Apply `H1`, `H2` at `x + 1 ≥ 2`.
If `p < x (x + 1)`, the `H1` prime `q ∈ (x (x + 1), (x + 1) ^ 2)` exceeds `p`, so
`p_{n+1} ≤ q < (x + 1) ^ 2 ≤ (√p + 1) ^ 2`. Otherwise the `H2` prime
`q ∈ ((x + 1) ^ 2, (x + 1) (x + 2))` exceeds `p`, so
`p_{n+1} + 1 ≤ (x + 1) (x + 2) = x (x + 1) + 2 x + 2 ≤ p + 2 x + 2 < p + 2 √p + 1 + 1`
as `x < √p`. In both cases `√p_{n+1} < √p + 1`.
-/

namespace OMA.R_Andrica_andrica_conjecture_R1

/-- First half of Oppermann's conjecture. -/
def H1 : Prop :=
  ∀ x : ℕ, 2 ≤ x → ∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime

/-- Second half of Oppermann's conjecture. -/
def H2 : Prop :=
  ∀ x : ℕ, 2 ≤ x → ∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime

/-- Any prime above `p_n` is at least `p_{n+1}`. -/
lemma nth_succ_le_of_prime (n q : ℕ) (hq : q.Prime) (hlt : n.nth Nat.Prime < q) :
    (n + 1).nth Nat.Prime ≤ q := by
  have hinf := Nat.infinite_setOfPred_prime
  have hc : Nat.count Nat.Prime (n.nth Nat.Prime + 1) = n + 1 := by
    rw [Nat.count_succ, Nat.count_nth_of_infinite hinf, if_pos (Nat.prime_nth_prime n)]
  have hle : n + 1 ≤ Nat.count Nat.Prime q := hc ▸ Nat.count_monotone _ hlt
  calc (n + 1).nth Nat.Prime ≤ (Nat.count Nat.Prime q).nth Nat.Prime :=
        Nat.nth_monotone hinf hle
    _ = q := Nat.nth_count hq

theorem main : H1 → H2 → type_of% @Andrica.andrica_conjecture := by
  intro h1 h2 n
  have hp2 := (Nat.prime_nth_prime n).two_le
  set p := n.nth Nat.Prime with hp
  set x := Nat.sqrt p with hx
  have hxl : x ^ 2 ≤ p := Nat.sqrt_le' p
  have hxu : p < (x + 1) ^ 2 := Nat.lt_succ_sqrt' p
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hxu; omega
    · exact h
  obtain ⟨q1, hq1, hq1p⟩ := h1 (x + 1) (by omega)
  obtain ⟨q2, hq2, hq2p⟩ := h2 (x + 1) (by omega)
  rw [Finset.mem_Ioo, Nat.add_sub_cancel] at hq1
  rw [Finset.mem_Ioo] at hq2
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsx : (x : ℝ) ≤ Real.sqrt p := Real.nat_sqrt_le_real_sqrt
  rw [sub_lt_iff_lt_add, Real.sqrt_lt' (by positivity)]
  by_cases hc : p < x * (x + 1)
  · have hn := nth_succ_le_of_prime n q1 hq1p (by nlinarith)
    have h3 : (n + 1).nth Nat.Prime < (x + 1) ^ 2 := lt_of_le_of_lt hn hq1.2
    have h3R : (((n + 1).nth Nat.Prime : ℕ) : ℝ) < ((x : ℝ) + 1) ^ 2 := by exact_mod_cast h3
    nlinarith
  · push Not at hc
    have hn := nth_succ_le_of_prime n q2 hq2p (by nlinarith)
    have h3 : (n + 1).nth Nat.Prime + 1 ≤ (x + 1) * (x + 1 + 1) := by omega
    have h3R : (((n + 1).nth Nat.Prime : ℕ) : ℝ) + 1 ≤ ((x : ℝ) + 1) * ((x : ℝ) + 1 + 1) := by
      exact_mod_cast h3
    have hcR : (x : ℝ) * ((x : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hc
    have hxs : (x : ℝ) < Real.sqrt p := by
      rw [Real.lt_sqrt (Nat.cast_nonneg _)]
      have : x ^ 2 < p := by nlinarith
      exact_mod_cast this
    nlinarith

end OMA.R_Andrica_andrica_conjecture_R1
