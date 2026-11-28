import FormalConjectures.Wikipedia.EllipticCurveRank

/-! Finite moment argument for Bhargava and Shankar's rank-zero-or-one bound.
The odd 5-Selmer ranks contribute four units of size beyond the baseline one.
Every Mordell–Weil rank at least two contributes a further 24 units. -/

namespace OMA.R_EllipticCurveRank_RatEllipticCurve__08375_le_density_rank_zero_one_R1

open Finset Filter
open EllipticCurveRank EllipticCurveRank.RatEllipticCurve
open scoped BigOperators

private theorem charge (r s : ℕ) (hrs : r ≤ s) :
    25 + 4 * (if Odd s then 1 else 0) - 24 * (if r = 0 ∨ r = 1 then 1 else 0) ≤
      (5 : ℝ) ^ s := by
  by_cases hr : r = 0 ∨ r = 1
  · simp only [hr, if_true]
    by_cases hs : Odd s
    · have hs1 : 1 ≤ s := by
        by_contra! hn
        have : s = 0 := by omega
        simp [this] at hs
      rw [if_pos hs]
      calc _ = (5 : ℝ) ^ (1 : ℕ) := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hs1
    · rw [if_neg hs]
      calc _ = (5 : ℝ) ^ (0 : ℕ) := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.zero_le s)
  · simp only [hr, if_false, mul_zero, sub_zero]
    have h₂ : 2 ≤ s := by omega
    by_cases hs : Odd s
    · have h₃ : 3 ≤ s := by
        by_contra! hn
        have heq : s = 2 := by omega
        subst s
        exact (by decide : ¬ Odd (2 : ℕ)) hs
      rw [if_pos hs]
      calc _ ≤ (5 : ℝ) ^ (3 : ℕ) := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) h₃
    · rw [if_neg hs]
      calc _ = (5 : ℝ) ^ (2 : ℕ) := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) h₂

private theorem finite_density
    (T : Finset RatEllipticCurve) (s : RatEllipticCurve → ℕ)
    (dominate : ∀ E ∈ T, E.rank ≤ s E)
    (hmean : (∑ E ∈ T, (5 : ℝ) ^ s E) ≤ 6.00001 * (T.card : ℝ))
    (hodd : 0.27504 * (T.card : ℝ) ≤ ((T.filter fun E ↦ Odd (s E)).card : ℝ)) :
    0.8375 * (T.card : ℝ) ≤ ((T.filter fun E ↦ E.rank = 0 ∨ E.rank = 1).card : ℝ) := by
  let G := T.filter fun E ↦ E.rank = 0 ∨ E.rank = 1
  let O := T.filter fun E ↦ Odd (s E)
  have odds : (∑ E ∈ T, if Odd (s E) then (1 : ℝ) else 0) = (O.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [O]
  have goods : (∑ E ∈ T, if E.rank = 0 ∨ E.rank = 1 then (1 : ℝ) else 0) = (G.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [G]
  let weight (E : RatEllipticCurve) : ℝ :=
    25 + 4 * (if Odd (s E) then 1 else 0) - 24 * (if E.rank = 0 ∨ E.rank = 1 then 1 else 0)
  have hsum : (∑ E ∈ T, weight E) =
      25 * (T.card : ℝ) + 4 * (O.card : ℝ) - 24 * (G.card : ℝ) := by
    dsimp [weight]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, odds, goods]
    simp [mul_comm]
  have cost : 25 * (T.card : ℝ) + 4 * (O.card : ℝ) - 24 * (G.card : ℝ) ≤
      ∑ E ∈ T, (5 : ℝ) ^ s E := by
    rw [← hsum]
    exact Finset.sum_le_sum fun E hE ↦ charge E.rank (s E) (dominate E hE)
  change 0.8375 * (T.card : ℝ) ≤ (G.card : ℝ)
  have pos : 0 ≤ (T.card : ℝ) := by positivity
  linarith [cost, hmean, show 0.27504 * (T.card : ℝ) ≤ (O.card : ℝ) from hodd]

/-- The height-bounded reduced Weierstrass models form nonempty finite sets at large heights. -/
def H1 : Prop :=
  ∀ᶠ H : ℕ in atTop, (heightLE H).Finite ∧ (heightLE H).Nonempty

/-- The two required 5-Selmer statistics, with rational slack.
The global mean comes from Bhargava–Shankar's Theorem 1. The odd
population uses Theorem 6 together with the Selmer parity theorem. -/
def H2 : Prop :=
  ∃ s : RatEllipticCurve → ℕ, (∀ E, E.rank ≤ s E) ∧
    ∀ᶠ H : ℕ in atTop, ∀ T : Finset RatEllipticCurve, (T : Set RatEllipticCurve) = heightLE H →
      (∑ E ∈ T, (5 : ℝ) ^ s E) ≤ 6.00001 * (T.card : ℝ) ∧
      0.27504 * (T.card : ℝ) ≤ ((T.filter fun E ↦ Odd (s E)).card : ℝ)

theorem main : H1 → H2 → type_of% @EllipticCurveRank.RatEllipticCurve._08375_le_density_rank_zero_one := by
  intro finite statistics
  obtain ⟨s, hrank, hm⟩ := statistics
  have ev : ∀ᶠ H : ℕ in atTop,
      (0.8375 : ℝ) ≤
        ({E ∈ heightLE H | E.rank = 0 ∨ E.rank = 1}.ncard / (heightLE H).ncard : ℝ) := by
    filter_upwards [finite, hm] with H hH hdata
    obtain ⟨hf, hn⟩ := hH
    let T := hf.toFinset
    have hT : (T : Set RatEllipticCurve) = heightLE H := Set.Finite.coe_toFinset hf
    obtain ⟨hmean, hodd⟩ := hdata T hT
    have result := finite_density T s (fun E _ ↦ hrank E) hmean hodd
    have cardHeight : (heightLE H).ncard = T.card := Set.ncard_eq_toFinset_card _ hf
    have goodSet : (↑(T.filter fun E ↦ E.rank = 0 ∨ E.rank = 1) : Set RatEllipticCurve) =
        {E ∈ heightLE H | E.rank = 0 ∨ E.rank = 1} := by
      ext E
      simp [T]
    have cardGood := Set.ncard_coe_finset (T.filter fun E ↦ E.rank = 0 ∨ E.rank = 1)
    rw [goodSet] at cardGood
    rw [cardHeight, cardGood]
    have hpos : 0 < (T.card : ℝ) := by
      obtain ⟨E, hE⟩ := hn
      refine Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨E, ?_⟩)
      show E ∈ (T : Set RatEllipticCurve)
      rwa [hT]
    exact (le_div_iff₀ hpos).2 result
  apply le_liminf_of_le _ ev
  apply isCoboundedUnder_ge_of_eventually_le atTop (x := (1 : ℝ))
  filter_upwards [finite] with H hH
  apply div_le_one_of_le₀ _ (by positivity)
  have sub : {E ∈ heightLE H | E.rank = 0 ∨ E.rank = 1} ⊆ heightLE H :=
    fun _ hE ↦ hE.1
  exact_mod_cast Set.ncard_le_ncard sub hH.1

end OMA.R_EllipticCurveRank_RatEllipticCurve__08375_le_density_rank_zero_one_R1
