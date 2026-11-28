import FormalConjectures.ErdosProblems.«409»
import Mathlib

section
open Nat Finset Real

/-!
# Erdős 409: the iteration `n ↦ φ(n) + 1` reaches a prime within `4√n` steps

A composite `n` has a prime factor `p` with `p * p ≤ n`, and the `n / p` multiples of `p` below
`n` are not coprime to `n`. So `φ(n) + n / p ≤ n`: a step from a composite number subtracts at
least `√n - 1`. Induction gives a prime after `i` steps with `i * i ≤ 16 * n`, hence the number
of steps is `o(n)`.
-/

namespace Erdos409Sqrt

/-- The multiples of a divisor `p > 1` of `n` below `n` are not coprime to `n`. -/
theorem totient_add_div_le {n p : ℕ} (hp : 1 < p) (hpn : p ∣ n) :
    totient n + n / p ≤ n := by
  classical
  have hp0 : 0 < p := by omega
  have hsub : (range n).filter (Nat.Coprime n) ∪
      (range (n / p)).image (fun j => p * j) ⊆ range n := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact (mem_filter.mp ha).1
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
      have hj' : j < n / p := mem_range.mp hj
      have hlt : p * j < p * (n / p) := Nat.mul_lt_mul_of_pos_left hj' hp0
      rw [Nat.mul_div_cancel' hpn] at hlt
      exact mem_range.mpr hlt
  have hdisj : Disjoint ((range n).filter (Nat.Coprime n))
      ((range (n / p)).image (fun j => p * j)) := by
    rw [disjoint_left]
    intro a ha hb
    obtain ⟨j, -, rfl⟩ := mem_image.mp hb
    have hco : Nat.gcd n (p * j) = 1 := (mem_filter.mp ha).2
    have h1 : p ∣ Nat.gcd n (p * j) := Nat.dvd_gcd hpn (Dvd.intro j rfl)
    rw [hco] at h1
    have := le_of_dvd Nat.one_pos h1
    omega
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_range,
    Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp0 h),
    card_range, ← totient_eq_card_coprime] at hcard
  exact hcard

/-- From every positive `n` the iteration reaches a prime after `i` steps with `i * i ≤ 16 * n`. -/
theorem exists_iterate_prime (n : ℕ) (hn : 0 < n) :
    ∃ i, i * i ≤ 16 * n ∧ ((fun x => totient x + 1)^[i] n).Prime := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hp : n.Prime
    · exact ⟨0, by omega, by simpa using hp⟩
    · rcases (by omega : n = 1 ∨ 1 < n) with h1 | h1
      · subst h1
        exact ⟨1, by norm_num, by norm_num [Function.iterate_one, totient_one]⟩
      · have hpp : n.minFac.Prime := minFac_prime (by omega)
        have hpn : n.minFac ∣ n := minFac_dvd n
        have hsq : n.minFac ^ 2 ≤ n := minFac_sq_le_self hn hp
        have hk : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hpn
        have hbound : totient n + n / n.minFac ≤ n := totient_add_div_le hpp.one_lt hpn
        have hp2 : 2 ≤ n.minFac := hpp.two_le
        generalize n.minFac = p at *
        generalize hkdef : n / p = k at *
        have hpk : p ≤ k := by
          by_contra hlt
          push Not at hlt
          nlinarith
        have hnk : n ≤ k * k := by nlinarith
        by_cases hk3 : k < 3
        · have hk2 : k = 2 := by omega
          have hp2' : p = 2 := by omega
          have hn4 : n = 4 := by subst hk2 hp2'; omega
          subst hn4
          exact ⟨1, by norm_num, by decide⟩
        · obtain ⟨j, hj, hjp⟩ := ih (totient n + 1) (by omega) (by omega)
          refine ⟨j + 1, ?_, ?_⟩
          · have hj4 : j ≤ 4 * k := by
              by_contra hlt
              push Not at hlt
              nlinarith
            nlinarith
          · rw [Function.iterate_succ_apply]
            exact hjp

end Erdos409Sqrt

noncomputable def OMA.answer : ℕ → ℝ := fun n => (n : ℝ)

theorem OMA.solution : Erdos409.erdos_409.parts.i.isLittleO.answer = OMA.answer →
    type_of% @Erdos409.erdos_409.parts.i.isLittleO := by
  intro hans c h
  rw [hans]
  have hc : ∀ n > 0, (c n : ℝ) ^ 2 ≤ 16 * n := by
    intro n hn
    obtain ⟨i, hi, hip⟩ := Erdos409Sqrt.exists_iterate_prime n hn
    have hle : c n ≤ i := (h n hn).2 hip
    have hnat : c n * c n ≤ 16 * n := le_trans (Nat.mul_le_mul hle hle) hi
    have hreal : ((c n * c n : ℕ) : ℝ) ≤ ((16 * n : ℕ) : ℝ) := cast_le.mpr hnat
    push_cast at hreal
    nlinarith
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop (ceil (16 / ε ^ 2) + 1)] with n hn
  have hn0 : 0 < n := by omega
  have hnreal : 16 / ε ^ 2 ≤ (n : ℝ) := by
    have h1 : (16 / ε ^ 2 : ℝ) ≤ ceil (16 / ε ^ 2) := le_ceil _
    have h2 : ((ceil (16 / ε ^ 2) : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : ceil (16 / ε ^ 2) ≤ n)
    linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have h16 : 16 ≤ ε ^ 2 * n := by
    rw [div_le_iff₀ hε2] at hnreal
    linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hcn : (0 : ℝ) ≤ c n := cast_nonneg _
  simp only [OMA.answer, norm_eq_abs, abs_of_nonneg hcn, abs_of_nonneg hnpos.le]
  by_contra hlt
  push Not at hlt
  have hsq := hc n hn0
  nlinarith [mul_pos hε hnpos]

end
