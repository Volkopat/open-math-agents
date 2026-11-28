import OMAStatements.S_oeis_a039825

/-! The Euler summation and Gauss product reduce the support question to triangular numbers. -/

namespace OMA.R_oeis_a039825_R1

open OMA.S_oeis_a039825
open PowerSeries Classical

private theorem triangle_succ (n : ℕ) :
    (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + n + 1 := by
  have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
  rw [h]
  omega

private theorem triangle_strictMono : StrictMono (fun n : ℕ => n * (n + 1) / 2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [triangle_succ]
  omega

private theorem triangle_ge_three {n : ℕ} (hn : 2 ≤ n) : 3 ≤ n * (n + 1) / 2 :=
  triangle_strictMono.monotone hn

private theorem exponent_of_triangle (n : ℕ) : a n = (n * (n + 1) / 2 + 4) / 2 := by
  unfold a
  have hprod : n ^ 2 + n = n * (n + 1) := by ring
  have he := Nat.even_iff.mp (Nat.even_mul_succ_self n)
  rw [hprod]
  omega

private theorem neighboring_triangles (m : ℕ) (hm : 0 < m) :
    ¬ ((∃ n : ℕ, n * (n + 1) / 2 = 2 * m + 1) ∧
       (∃ n : ℕ, n * (n + 1) / 2 = 2 * m)) := by
  rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
  have hx1 : 1 ≤ x := by
    by_contra! h
    have hx0 : x = 0 := by omega
    subst x
    simp at hx
    omega
  have hxy : x < y := triangle_strictMono.lt_iff_lt.mp (by omega)
  have hh := triangle_strictMono.monotone (show x + 1 ≤ y by omega)
  change (x + 1) * (x + 1 + 1) / 2 ≤ y * (y + 1) / 2 at hh
  rw [triangle_succ, hx, hy] at hh
  omega

private theorem exponent_iff_adjacent (m : ℕ) (hm : 0 < m) :
    (∃ n : ℕ, 2 ≤ n ∧ a n = m + 2) ↔
      (∃ n : ℕ, n * (n + 1) / 2 = 2 * m + 1) ∨ (∃ n : ℕ, n * (n + 1) / 2 = 2 * m) := by
  constructor
  · rintro ⟨n, hn, he⟩
    rw [exponent_of_triangle] at he
    by_cases he' : n * (n + 1) / 2 = 2 * m + 1
    · exact Or.inl ⟨n, he'⟩
    · exact Or.inr ⟨n, by omega⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    all_goals
      have hN : 2 ≤ n := by
        by_contra! h
        interval_cases n <;> norm_num at hn <;> omega
      exact ⟨n, hN, by rw [exponent_of_triangle, hn]; omega⟩

private theorem support_after_difference (m : ℕ) :
    (if ∃ n : ℕ, n * (n + 1) / 2 = 2 * m + 1 then (1 : ℚ) else 0) -
      (if ∃ n : ℕ, n * (n + 1) / 2 = 2 * m then 1 else 0) ≠ 0 ↔
      ∃ n : ℕ, 2 ≤ n ∧ a n = m + 2 := by
  by_cases hm : m = 0
  · subst m
    have h0 : ∃ n : ℕ, n * (n + 1) / 2 = 2 * 0 := ⟨0, by decide⟩
    have h1 : ∃ n : ℕ, n * (n + 1) / 2 = 2 * 0 + 1 := ⟨1, by decide⟩
    rw [if_pos h1, if_pos h0, sub_self]
    constructor
    · intro h
      exact (h rfl).elim
    · rintro ⟨n, hn, he⟩
      have ht := triangle_ge_three hn
      rw [exponent_of_triangle] at he
      omega
  · rw [exponent_iff_adjacent m (by omega)]
    have hd := neighboring_triangles m (by omega)
    by_cases h₁ : ∃ n : ℕ, n * (n + 1) / 2 = 2 * m + 1 <;>
      by_cases h₀ : ∃ n : ℕ, n * (n + 1) / 2 = 2 * m
    · exact (hd ⟨h₁, h₀⟩).elim
    · norm_num [h₁, h₀]
    · norm_num [h₁, h₀]
    · norm_num [h₁, h₀]

private theorem small_coeff (m : ℕ) (hm : m < 2) : coeffAt m = 0 := by
  unfold coeffAt
  apply Finset.sum_eq_zero
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  rw [Polynomial.coeff_X_pow_mul']
  simp [show ¬ 3 * n ≤ m by omega]

/-- The finite coefficient form of the odd-index Euler summation after `q = X²`. -/
def H1 : Prop :=
  ∀ m : ℕ,
    let P : ℚ⟦X⟧ := ∏ j ∈ Finset.range (m + 2), (1 - X ^ (2 * (j + 1)))
    let Q : ℚ⟦X⟧ := ∏ j ∈ Finset.range (m + 2), (1 - X ^ (2 * j + 1))
    (coeffAt (m + 2) : ℚ) = coeff (2 * m + 1) ((1 - X) * (P * Q⁻¹))

/-- Gauss's triangular-number identity in degrees unaffected by truncation. -/
def H2 : Prop :=
  ∀ m i : ℕ, i ≤ 2 * m →
    let P : ℚ⟦X⟧ := ∏ j ∈ Finset.range m, (1 - X ^ (2 * (j + 1)))
    let Q : ℚ⟦X⟧ := ∏ j ∈ Finset.range m, (1 - X ^ (2 * j + 1))
    coeff i (P * Q⁻¹) = (if ∃ n : ℕ, n * (n + 1) / 2 = i then (1 : ℚ) else 0)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a039825.main := by
  intro hEuler hGauss m
  by_cases hm : m < 2
  · rw [small_coeff m hm]
    constructor
    · simp
    · rintro ⟨n, hn, he⟩
      have hTri := triangle_ge_three hn
      rw [exponent_of_triangle] at he
      omega
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 2 := ⟨m - 2, by omega⟩
    have hEq := hEuler j
    dsimp only at hEq
    rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul,
      hGauss (j + 2) (2 * j + 1) (by omega), hGauss (j + 2) (2 * j) (by omega)] at hEq
    have hCast : ((coeffAt (j + 2) : ℚ) ≠ 0) ↔ ∃ n : ℕ, 2 ≤ n ∧ a n = j + 2 := by
      rw [hEq]
      exact support_after_difference j
    exact_mod_cast hCast

end OMA.R_oeis_a039825_R1
