import OMAStatements.S_mo_331428
import Mathlib

open OMA.S_mo_331428 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_331428.main) := by
  intro h
  obtain ⟨α, β, γ, M₁, N₁, M₂, N₂, hdet, hid⟩ :=
    h 1 0 0 (-1) 0 (by norm_num)
  have hc (t : ℝ) (ht : γ * t + 1 ≠ 0) :
      (α * t + β)^3 * ((α - γ) * t + (β - 1)) =
        (M₁ + N₁ * t^2) * (M₂ + N₂ * t^2) := by
    let x := (α * t + β) / (γ * t + 1)
    have hx : x^2 * (x^2 - x) =
        (M₁ + N₁ * t^2) * (M₂ + N₂ * t^2) / (γ * t + 1)^4 := by
      simpa [x, sub_eq_add_neg] using hid t ht
    have hmul : x * (γ * t + 1) = α * t + β := div_mul_cancel₀ _ ht
    calc
      (α * t + β)^3 * ((α - γ) * t + (β - 1)) =
          (α * t + β)^3 * ((α * t + β) - (γ * t + 1)) := by ring
      _ = x^2 * (x^2 - x) * (γ * t + 1)^4 := by
        rw [← hmul]
        ring
      _ = (M₁ + N₁ * t^2) * (M₂ + N₂ * t^2) := by
        rw [hx, div_mul_cancel₀ _ (pow_ne_zero _ ht)]
  let c₁ := β^2 * (3 * α * (β-1) + β * (α-γ))
  let c₃ := α^2 * (α * (β-1) + 3 * β * (α-γ))
  have odd (t : ℝ) (ht : γ*t+1 ≠ 0) (hnt : γ*(-t)+1 ≠ 0) :
      t * (c₁ + t^2 * c₃) = 0 := by
    dsimp [c₁, c₃]
    linear_combination (hc t ht - hc (-t) hnt) / 2
  let u : ℝ := if γ = 0 then 1 else 2 / γ
  have hu : u ≠ 0 := by
    dsimp [u]
    split_ifs with h
    · norm_num
    · exact div_ne_zero (by norm_num) h
  have hγu : γ * u = 0 ∨ γ * u = 2 := by
    by_cases h : γ = 0
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [u, h, mul_div_cancel₀])
  have first : c₁ + u^2 * c₃ = 0 := by
    apply (mul_eq_zero.mp (odd u ?_ ?_)).resolve_left hu
    all_goals rcases hγu with hz | hz <;> nlinarith
  have second : c₁ + (2*u)^2 * c₃ = 0 := by
    apply (mul_eq_zero.mp (odd (2*u) ?_ ?_)).resolve_left (mul_ne_zero (by norm_num) hu)
    all_goals rcases hγu with hz | hz <;> nlinarith
  have hz : 3 * u^2 * c₃ = 0 := by linear_combination second - first
  have hc₃ : c₃ = 0 :=
    (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero _ hu))
  have hc₁ : c₁ = 0 := by simpa [hc₃] using first
  by_cases hα : α = 0
  · have hβγ : β * γ ≠ 0 := by simpa [hα] using hdet
    have bad : β^2 * (β * γ) = 0 := by
      dsimp [c₁] at hc₁
      rw [hα] at hc₁
      linear_combination -hc₁
    exact (mul_ne_zero (pow_ne_zero _ (fun hb => hβγ (by simp [hb]))) hβγ) bad
  by_cases hβ : β = 0
  · have bad : α^3 = 0 := by
      dsimp [c₃] at hc₃
      rw [hβ] at hc₃
      linear_combination -hc₃
    exact pow_ne_zero _ hα bad
  have e₁ := (mul_eq_zero.mp hc₁).resolve_left (pow_ne_zero _ hβ)
  have e₃ := (mul_eq_zero.mp hc₃).resolve_left (pow_ne_zero _ hα)
  have b1 : α * (β - 1) = 0 := by linear_combination (3 * e₁ - e₃) / 8
  have a1 : β * (α - γ) = 0 := by linear_combination (3 * e₃ - e₁) / 8
  have hβ1 := sub_eq_zero.mp ((mul_eq_zero.mp b1).resolve_left hα)
  have hαγ := sub_eq_zero.mp ((mul_eq_zero.mp a1).resolve_left hβ)
  exact hdet (by simp [hβ1, hαγ])