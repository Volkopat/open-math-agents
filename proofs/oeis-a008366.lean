import OMAStatements.S_oeis_a008366
import Mathlib

open Finset

private lemma rough_tenth_sum (n : ℕ) :
    ∃ Q : ℤ, 66 * ((∑ k ∈ Icc 1 n, k ^ 10 : ℕ) : ℤ) =
      (n : ℤ) * ((n : ℤ) * Q + 5) := by
  let q (x : ℤ) := 6*x^9 + 33*x^8 + 55*x^7 - 66*x^5 + 66*x^3 - 33*x
  refine ⟨q n, ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n+1), Nat.cast_add, mul_add, ih]
    push_cast
    dsimp [q]
    ring

private lemma rough_twelfth_sum (n : ℕ) :
    ∃ Q : ℤ, 2730 * ((∑ k ∈ Icc 1 n, k ^ 12 : ℕ) : ℤ) =
      (n : ℤ) * ((n : ℤ) * Q + (-691)) := by
  let q (x : ℤ) :=
    210*x^11 + 1365*x^10 + 2730*x^9 - 5005*x^7 + 8580*x^5 - 9009*x^3 + 4550*x
  refine ⟨q n, ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n+1), Nat.cast_add, mul_add, ih]
    push_cast
    dsimp [q]
    ring


/-- In a cleared power-sum formula, the denominator detects divisibility when the
constant coefficient of the quotient polynomial is coprime to that denominator. -/
private lemma rough_sum_dvd_iff {n D S : ℕ} {P b : ℤ} (hn : 0 < n)
    (hcop : IsCoprime (D : ℤ) b)
    (hformula : (D : ℤ) * S = n * ((n : ℤ) * P + b)) :
    n ∣ S ↔ n.Coprime D := by
  constructor
  · rintro ⟨k, rfl⟩
    push_cast at hformula
    have hcancel : (D : ℤ) * k = n * P + b := by
      apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn.ne')
      calc
        _ = (D : ℤ) * ((n : ℤ) * k) := by ring
        _ = _ := hformula
    obtain ⟨u, v, huv⟩ := hcop
    apply Nat.isCoprime_iff_coprime.mp
    refine ⟨-v * P, u + v * k, ?_⟩
    linear_combination huv + v * hcancel
  · intro hc
    have hdvd : (n : ℤ) ∣ (D : ℤ) * S := ⟨_, hformula⟩
    exact_mod_cast hc.isCoprime.dvd_of_dvd_mul_left hdvd


private lemma oma_rough_factors {n : ℕ} (hn : 1 < n) :
    (n.Coprime 66 ∧ n.Coprime 2730) ↔ 17 ≤ n.minFac := by
  constructor
  · rintro ⟨h₁,h₂⟩
    by_contra! hsmall
    have classifies : ∀ p : Fin 17, p.val.Prime → (p.val ∣ 66 ∨ p.val ∣ 2730) := by decide
    have hp := Nat.minFac_prime (ne_of_gt hn)
    rcases classifies ⟨n.minFac, hsmall⟩ hp with d | d
    · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨_, hp, Nat.minFac_dvd _, d⟩ h₁
    · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨_, hp, Nat.minFac_dvd _, d⟩ h₂
  · intro hrough
    have small {p : ℕ} (hp : p ≠ 0) (hlt : p < 17) : n.Coprime p :=
      Nat.coprime_of_lt_minFac hp (hlt.trans_le hrough)
    change n.Coprime (2 * 3 * 11) ∧ n.Coprime (2 * 3 * 5 * 7 * 13)
    simp only [Nat.coprime_mul_iff_right]
    repeat' apply And.intro
    all_goals apply small <;> decide


theorem OMA.solution : type_of% @OMA.S_oeis_a008366.main := by
  intro n hn
  obtain ⟨Q, hQ⟩ := rough_tenth_sum n
  obtain ⟨R, hR⟩ := rough_twelfth_sum n
  have hc₁ : IsCoprime (66 : ℤ) 5 := ⟨1, -13, by norm_num⟩
  have hc₂ : IsCoprime (2730 : ℤ) (-691) := by norm_num
  rw [rough_sum_dvd_iff (D := 66) (by omega) hc₁ hQ,
    rough_sum_dvd_iff (D := 2730) (by omega) hc₂ hR]
  exact oma_rough_factors hn
