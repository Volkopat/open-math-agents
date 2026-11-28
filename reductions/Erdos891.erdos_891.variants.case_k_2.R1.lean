import FormalConjectures.ErdosProblems.«891»

-- Reduction Erdos891.erdos_891.variants.case_k_2.R1 of the case k = 2 of Erdős Problem 891
-- Source: https://www.erdosproblems.com/891
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 891 for `k = 2` from the windows around `3`-smooth numbers

Every window of `6` consecutive integers contains a multiple `M` of `6`. Since `2 ∣ M` and
`3 ∣ M`, either `M` has at least `3` prime factors, or `M = 2 ^ a * 3 ^ b` with `a, b ≥ 1`.
So only the six windows `[M - i, M - i + 6)`, `i ≤ 5`, around such `M` matter. There are only
`O((log x) ^ 2)` such `M` up to `x`.

* `H1` (elementary, difference of squares): for large `M`, the number `M - 2`, `M - 3` or
  `M - 4` has at least `3` prime factors when `M / 2`, `M / 3` or `M / 4` is a square. Indeed
  `M - c = c * (x - 1) * (x + 1)` when `M = c * x ^ 2`. This settles the windows with `3 ≤ i`
  when `a + b` is odd, and the windows with `4 ≤ i` when `a` and `b` are even.
* `H2` (open): the windows with `3 ≤ i ≤ 5` when `a` and `b` are odd.
* `H3` (open): the window with `i = 3` when `a` and `b` are even.
* `H4` (open): the windows with `i ≤ 2`.

`H2`, `H3` and `H4` are the conjecture restricted to the windows that `H1` does not settle, so
no strength is lost: the conjecture implies all three.
-/

namespace OMA.R_Erdos891_erdos_891_variants_case_k_2_R1

open Finset Filter
open scoped ArithmeticFunction.omega

/-- Difference of squares: `M - c` has `ω ≥ 3` when `M / c` is a square, for `c = 2, 3, 4`. -/
def H1 : Prop :=
  ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b →
    (Odd a → Even b → 3 ≤ ω (M - 2)) ∧ (Even a → Odd b → 3 ≤ ω (M - 3)) ∧
      (Even a → Even b → 3 ≤ ω (M - 4))

/-- The windows that start at `M - 3`, `M - 4` or `M - 5`, for `a` and `b` odd. -/
def H2 : Prop :=
  ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b → Odd a → Odd b →
    ∀ i : ℕ, 3 ≤ i → i ≤ 5 → ∃ m ∈ Ico (M - i) (M - i + 6), 3 ≤ ω m

/-- The window that starts at `M - 3`, for `a` and `b` even. -/
def H3 : Prop :=
  ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b → Even a → Even b →
    ∃ m ∈ Ico (M - 3) (M + 3), 3 ≤ ω m

/-- The windows that start at `M`, `M - 1` or `M - 2`. -/
def H4 : Prop :=
  ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b →
    ∀ i : ℕ, i ≤ 2 → ∃ m ∈ Ico (M - i) (M - i + 6), 3 ≤ ω m

/-- Every window of `6` consecutive integers contains a multiple of `6`. -/
lemma exists_multiple_six (n : ℕ) : ∃ M ∈ Ico n (n + 6), 6 ∣ M := by
  refine ⟨6 * ((n + 5) / 6), mem_Ico.mpr ⟨?_, ?_⟩, dvd_mul_right _ _⟩ <;> omega

/-- A positive multiple of `6` with at most `2` prime factors is `2 ^ a * 3 ^ b`. -/
lemma smooth_of_omega_le (M : ℕ) (hM : 0 < M) (h6 : 6 ∣ M) (hω : ω M ≤ 2) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ M = 2 ^ a * 3 ^ b := by
  have h2 : 2 ∣ M := by omega
  have h3 : 3 ∣ M := by omega
  have hcard : ω M = M.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]
  have hsub : ({2, 3} : Finset ℕ) ⊆ M.primeFactors := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hM.ne'⟩
    · rw [mem_singleton.mp hp]
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, hM.ne'⟩
  have hpf : M.primeFactors = {2, 3} :=
    (eq_of_subset_of_card_le hsub (by rw [← hcard, card_pair (by norm_num)]; exact hω)).symm
  refine ⟨M.factorization 2, M.factorization 3,
    Nat.prime_two.factorization_pos_of_dvd hM.ne' h2,
    Nat.prime_three.factorization_pos_of_dvd hM.ne' h3, ?_⟩
  have hprod := Nat.prod_factorization_pow_eq_self hM.ne'
  rw [Finsupp.prod, Nat.support_factorization, hpf, prod_pair (by norm_num)] at hprod
  exact hprod.symm

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos891.erdos_891.variants.case_k_2 := by
  intro h1 h2 h3 h4
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp h1
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp h2
  obtain ⟨K₃, hK₃⟩ := eventually_atTop.mp h3
  obtain ⟨K₄, hK₄⟩ := eventually_atTop.mp h4
  filter_upwards [eventually_ge_atTop K₁, eventually_ge_atTop K₂, eventually_ge_atTop K₃,
    eventually_ge_atTop K₄, eventually_ge_atTop 1] with n hn₁ hn₂ hn₃ hn₄ hn
  obtain ⟨M, hM, h6⟩ := exists_multiple_six n
  obtain ⟨hnM, hMn⟩ := mem_Ico.mp hM
  by_cases hω : 3 ≤ ω M
  · exact ⟨M, hM, hω⟩
  obtain ⟨a, b, ha, hb, hab⟩ := smooth_of_omega_le M (by omega) h6 (by omega)
  -- the window is `[M - i, M - i + 6)` with `i = M - n`
  have hi : n = M - (M - n) := by omega
  by_cases c : M - n ≤ 2
  · obtain ⟨m, hm, hωm⟩ := hK₄ M (by omega) a b ha hb hab (M - n) c
    exact ⟨m, by rwa [← hi] at hm, hωm⟩
  obtain ⟨h12, h13, h14⟩ := hK₁ M (by omega) a b ha hb hab
  rcases Nat.even_or_odd a with hpa | hpa <;> rcases Nat.even_or_odd b with hpb | hpb
  · by_cases c3 : M - n = 3
    · obtain ⟨m, hm, hωm⟩ := hK₃ M (by omega) a b ha hb hab hpa hpb
      obtain ⟨hm₁, hm₂⟩ := mem_Ico.mp hm
      exact ⟨m, mem_Ico.mpr ⟨by omega, by omega⟩, hωm⟩
    · exact ⟨M - 4, mem_Ico.mpr ⟨by omega, by omega⟩, h14 hpa hpb⟩
  · exact ⟨M - 3, mem_Ico.mpr ⟨by omega, by omega⟩, h13 hpa hpb⟩
  · exact ⟨M - 2, mem_Ico.mpr ⟨by omega, by omega⟩, h12 hpa hpb⟩
  · obtain ⟨m, hm, hωm⟩ := hK₂ M (by omega) a b ha hb hab hpa hpb (M - n) (by omega) (by omega)
    exact ⟨m, by rwa [← hi] at hm, hωm⟩

end OMA.R_Erdos891_erdos_891_variants_case_k_2_R1
