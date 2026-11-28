import FormalConjectures.ErdosProblems.«482»

/-! Closed forms for both parities of Stoll's recurrence in base g. -/

open Erdos482

theorem OMA.solution : type_of% @Erdos482.erdos_482.variants.stoll_explicit := by
  intro g hg t ht htg ε hlo hhi
  let a := (g : ℝ) / (((g : ℝ) - 1) * (t + g))
  let b := ((g : ℝ) - 1) * (t + g)
  let u := generalRecurrence g a b ε
  let x (n : ℕ) := (t + g) * (g : ℝ) ^ n / g
  have hg₂ : 2 ≤ (g : ℝ) := by exact_mod_cast hg
  have hg₀ : 0 < (g : ℝ) := by linarith
  have hgm : (g : ℝ) - 1 ≠ 0 := by linarith
  have hden : 0 < b := mul_pos (by linarith) (by linarith)
  have hlo' : -1 ≤ ε * g := (div_le_iff₀ hg₀).mp hlo
  have hhi' : ε * g < (g + 1) * (g - 2) := (lt_div_iff₀ hg₀).mp hhi
  have hrep (n : ℕ) : ∃ q : ℤ, ((g : ℝ) - 1) * q + 1 = (g : ℝ) ^ n := by
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih => obtain ⟨q, hq⟩ := ih; exact ⟨g * q + 1, by push_cast; rw [pow_succ, ← hq]; ring⟩
  have heven (n : ℕ) : u (2 * n) = ⌊x n⌋ := by
    induction n with
    | zero =>
      change (1 : ℤ) = ⌊(t + g) * (g : ℝ) ^ 0 / g⌋
      symm; rw [pow_zero, mul_one, Int.floor_eq_iff, le_div_iff₀ hg₀, div_lt_iff₀ hg₀]
      exact ⟨by norm_num; linarith, by norm_num; linarith⟩
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      change generalRecurrence g a b ε (2 * n + 1 + 1) = _
      rw [generalRecurrence, if_neg (by simp : ¬ Even (2 * n + 1))]
      dsimp only [u] at ih; rw [generalRecurrence, if_pos (even_two_mul n), ih]
      obtain ⟨q, hq⟩ := hrep n
      have hodd : ⌊a * ((⌊x n⌋ : ℝ) + ε)⌋ = q := by
        have hx : (g : ℝ) * x n = (((g : ℝ) - 1) * q + 1) * (t + g) := by
          rw [hq]; dsimp [x]; field_simp [hg₀.ne']
        rw [show a * ((⌊x n⌋ : ℝ) + ε) = g * ((⌊x n⌋ : ℝ) + ε) / b by dsimp [a, b]; ring,
          Int.floor_eq_iff, le_div_iff₀ hden, div_lt_iff₀ hden]
        have h1 := mul_lt_mul_of_pos_left (Int.sub_one_lt_floor (x n)) hg₀
        have h2 := mul_le_mul_of_nonneg_left (Int.floor_le (x n)) hg₀.le
        have h3 := mul_nonneg (sub_nonneg.2 ht) (sub_nonneg.2 hg₂)
        exact ⟨by nlinarith only [hx, hlo', ht, h1], by nlinarith only [hx, hhi', h2, h3]⟩
      rw [hodd]; congr 1
      calc b * ((q : ℝ) + 1 / ((g : ℝ) - 1)) = (t + g) * (((g : ℝ) - 1) * q + 1) := by
            dsimp [b]; field_simp [hgm]
        _ = x (n + 1) := by rw [hq]; dsimp [x]; rw [pow_succ]; field_simp [hg₀.ne']
  change ∀ n : ℕ, u (2 * n + 2) - (g : ℤ) * u (2 * n) =
    ⌊t * (g : ℝ) ^ n⌋ - (g : ℤ) * ⌊t * (g : ℝ) ^ n / g⌋
  intro n
  rw [show 2 * n + 2 = 2 * (n + 1) by omega, heven, heven,
    show x (n + 1) = t * (g : ℝ) ^ n + ((g : ℤ) ^ (n + 1) : ℤ) by
      dsimp [x]; push_cast; rw [pow_succ]; field_simp [hg₀.ne'],
    show x n = t * (g : ℝ) ^ n / g + ((g : ℤ) ^ n : ℤ) by
      dsimp [x]; push_cast; field_simp [hg₀.ne'],
    Int.floor_add_intCast, Int.floor_add_intCast, pow_succ]
  ring
