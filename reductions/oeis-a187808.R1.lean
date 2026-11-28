import OMAStatements.S_oeis_a187808
import Mathlib.Tactic

/-!
In Sun's four-prime conjecture, the witness also gives a term counted by A187808.
Only ten indices need separate positivity witnesses. For an odd index the
four-prime witness must be odd, and for either parity it is nonzero modulo 3.
Source: https://oeis.org/A187808
-/

namespace OMA.R_oeis_a187808_R1

open Finset

private theorem positive_of_witness (n k : ℕ) (hk : k < n)
    (h1 : (2 * k + 3).Prime) (h2 : (n * (n - k) - 1).Prime)
    (h3 : (n * (n + k) - 1).Prime) : 0 < OMA.S_oeis_a187808.a n :=
  Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, h1, h2, h3⟩⟩

/-- Indices at which the four-prime claim does not supply a witness. -/
def H1 : Prop :=
  ∀ n ∈ ({2, 3, 4, 5, 9, 191, 329, 641, 711, 979} : Finset ℕ),
    0 < OMA.S_oeis_a187808.a n

/-- Four-prime witnesses at even indices. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 < n → n % 2 = 0 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ k % 3 ≠ 0 ∧
      (2 * k - 3).Prime ∧ (2 * k + 3).Prime ∧
      (n * (n - k) - 1).Prime ∧ (n * (n + k) - 1).Prime

/-- Four-prime witnesses at odd indices, with the necessary parity of the witness. -/
def H3 : Prop :=
  ∀ n : ℕ, 5 < n → n % 2 = 1 → n ∉ ({9, 191, 329, 641, 711, 979} : Finset ℕ) →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ k % 2 = 1 ∧ k % 3 ≠ 0 ∧
      (2 * k - 3).Prime ∧ (2 * k + 3).Prime ∧
      (n * (n - k) - 1).Prime ∧ (n * (n + k) - 1).Prime

theorem exceptional_cases : H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_of_witness 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_of_witness 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_of_witness 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_of_witness 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_of_witness 9 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_of_witness 191 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_of_witness 329 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_of_witness 641 259 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_of_witness 711 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_of_witness 979 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem witness_mod_three {k : ℕ} (hk : 0 < k) (hp : (2 * k + 3).Prime) :
    k % 3 ≠ 0 := by
  intro h
  have hdiv : 3 ∣ 2 * k + 3 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  rcases (Nat.dvd_prime hp).mp hdiv with heq | heq <;> omega

private theorem witness_mod_two {n k : ℕ} (hn : 5 < n) (hn2 : n % 2 = 1)
    (hp : (n * (n + k) - 1).Prime) : k % 2 = 1 := by
  by_contra! h
  have hk2 : k % 2 = 0 := by omega
  have hmod : n * (n + k) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.add_mod n k, hn2, hk2]
  have hdiv : 2 ∣ n * (n + k) - 1 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hlower : n ≤ n * (n + k) := Nat.le_mul_of_pos_right n (by omega)
  rcases (Nat.dvd_prime hp).mp hdiv with heq | heq <;> omega

theorem four_primes_iff :
    (∀ n : ℕ, 5 < n → n ∉ ({9, 191, 329, 641, 711, 979} : Finset ℕ) →
      ∃ k : ℕ, 0 < k ∧ k < n ∧ (2 * k - 3).Prime ∧ (2 * k + 3).Prime ∧
        (n * (n - k) - 1).Prime ∧ (n * (n + k) - 1).Prime) ↔ H2 ∧ H3 := by
  constructor
  · intro h
    constructor
    · intro n hn hn2
      have hnex : n ∉ ({9, 191, 329, 641, 711, 979} : Finset ℕ) := by
        intro he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      obtain ⟨k, hk, hkn, hm, hp, hl, hr⟩ := h n hn hnex
      exact ⟨k, hk, hkn, witness_mod_three hk hp, hm, hp, hl, hr⟩
    · intro n hn hn2 hnex
      obtain ⟨k, hk, hkn, hm, hp, hl, hr⟩ := h n hn hnex
      exact ⟨k, hk, hkn, witness_mod_two hn hn2 hr, witness_mod_three hk hp, hm, hp, hl, hr⟩
  · rintro ⟨heven, hodd⟩ n hn hnex
    by_cases hn2 : n % 2 = 0
    · obtain ⟨k, hk, hkn, _, hm, hp, hl, hr⟩ := heven n hn hn2
      exact ⟨k, hk, hkn, hm, hp, hl, hr⟩
    · obtain ⟨k, hk, hkn, _, _, hm, hp, hl, hr⟩ := hodd n hn (by omega) hnex
      exact ⟨k, hk, hkn, hm, hp, hl, hr⟩

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a187808.main := by
  intro hsmall heven hodd
  have hquad := four_primes_iff.mpr ⟨heven, hodd⟩
  refine ⟨?_, hquad⟩
  intro n hn
  by_cases hbad : n ∈ ({2, 3, 4, 5, 9, 191, 329, 641, 711, 979} : Finset ℕ)
  · exact hsmall n hbad
  have hn5 : 5 < n := by
    by_contra! h
    interval_cases n <;> simp at hbad
  have hnex : n ∉ ({9, 191, 329, 641, 711, 979} : Finset ℕ) := by
    intro hex
    apply hbad
    simp only [Finset.mem_insert, Finset.mem_singleton] at hex ⊢
    tauto
  obtain ⟨k, _, hkn, _, hp, hl, hr⟩ := hquad n hn5 hnex
  exact positive_of_witness n k hkn hp hl hr

end OMA.R_oeis_a187808_R1
