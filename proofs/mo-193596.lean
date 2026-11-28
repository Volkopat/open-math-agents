import OMAStatements.S_mo_193596
import Mathlib

-- Problem: mo-193596, the stationary distribution of the chain r -> r + a_j (mod 5), with j
-- uniform among k prices not all divisible by 5, is uniform.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Stationarity says pi(s) = (1/k) sum_j pi(s - a_j). Let s0 maximize pi. If pi(s) = pi(s0),
-- then the average of the values pi(s - a_j) <= pi(s0) equals pi(s0), so pi(s - a_j) = pi(s0)
-- for every j. Taking a price d = a_j not divisible by 5 and iterating, pi(s0 - t d) = pi(s0)
-- for all t; since d generates Z/5, pi is constant, hence equal to 1/5.

namespace MO193596

theorem cover : ∀ d s₀ x : ZMod 5, d ≠ 0 → ∃ t : Fin 5, s₀ - (t : ℕ) • d = x := by
  decide

end MO193596

theorem OMA.solution : type_of% @OMA.S_mo_193596.main := by
  rintro k a ⟨j₀, hj₀⟩ π _ hsum hst s
  have hkpos : 0 < k := Fin.pos j₀
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have inner : ∀ (s : ZMod 5) (j : Fin k),
      ∑ r : ZMod 5, π r * (if r + (a j : ZMod 5) = s then (1 : ℝ) else 0) =
        π (s - (a j : ZMod 5)) := by
    intro s j
    rw [Finset.sum_eq_single (s - (a j : ZMod 5))]
    · rw [if_pos (sub_add_cancel s _), mul_one]
    · intro r _ hr
      rw [if_neg, mul_zero]
      intro h
      exact hr (eq_sub_of_add_eq h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have L : ∀ s : ZMod 5,
      ∑ r, π r * (((Finset.univ.filter (fun j => r + (a j : ZMod 5) = s)).card : ℝ) / k) =
        (∑ j, π (s - (a j : ZMod 5))) / k := by
    intro s
    calc ∑ r, π r * (((Finset.univ.filter (fun j => r + (a j : ZMod 5) = s)).card : ℝ) / k)
        = ∑ r, (∑ j : Fin k, π r * (if r + (a j : ZMod 5) = s then (1 : ℝ) else 0)) / k := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [Finset.card_filter, Nat.cast_sum, ← mul_div_assoc, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl (fun j _ => ?_)
          split_ifs <;> simp
      _ = (∑ j : Fin k, ∑ r, π r * (if r + (a j : ZMod 5) = s then (1 : ℝ) else 0)) / k := by
          rw [← Finset.sum_div, Finset.sum_comm]
      _ = (∑ j, π (s - (a j : ZMod 5))) / k := by
          congr 1
          exact Finset.sum_congr rfl (fun j _ => inner s j)
  have hst' : ∀ s : ZMod 5, ∑ j, π (s - (a j : ZMod 5)) = π s * k := by
    intro s
    exact (div_eq_iff hk).mp ((L s).symm.trans (hst s))
  obtain ⟨s₀, -, hmax⟩ := Finset.exists_max_image Finset.univ π ⟨0, Finset.mem_univ 0⟩
  have step : ∀ s, π s = π s₀ → ∀ j, π (s - (a j : ZMod 5)) = π s₀ := by
    intro s hs j
    have h2 : ∑ j : Fin k, π (s - (a j : ZMod 5)) = ∑ _j : Fin k, π s₀ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hst' s, hs,
        mul_comm]
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hmax _ (Finset.mem_univ _))).mp h2 j
      (Finset.mem_univ j)
  have hd : (a j₀ : ZMod 5) ≠ 0 := by
    intro h0
    exact hj₀ ((CharP.cast_eq_zero_iff (ZMod 5) 5 (a j₀)).mp h0)
  have iter : ∀ t : ℕ, π (s₀ - t • (a j₀ : ZMod 5)) = π s₀ := by
    intro t
    induction t with
    | zero => rw [zero_smul, sub_zero]
    | succ t ih =>
      rw [succ_nsmul, ← sub_sub]
      exact step _ ih j₀
  have hconst : ∀ x, π x = π s₀ := by
    intro x
    obtain ⟨t, ht⟩ := MO193596.cover (a j₀ : ZMod 5) s₀ x hd
    rw [← ht]
    exact iter t
  have h5 : ∑ x : ZMod 5, π x = 5 * π s₀ := by
    rw [Finset.sum_congr rfl (fun x _ => hconst x), Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul]
    norm_num
  rw [h5] at hsum
  rw [hconst s]
  linarith
