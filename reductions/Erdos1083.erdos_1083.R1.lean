import FormalConjectures.ErdosProblems.«1083»
import Mathlib

-- Reduction Erdos1083.erdos_1083.R1 of Erdős Problem 1083
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Distinct distances in dimension `d ≥ 3`: the upper half is Erdős's lattice

Let `f_d(n)` be the least number of distinct distances among `n` points of `ℝ ^ d`. The target
asks for `f_d(n) = n ^ (2 / d - o(1))` for every `d ≥ 3`.

This file proves, with no hypothesis:

* Erdős's lattice bound [Er46b]: if `n ≤ m ^ d`, then `n` points of the grid `{0, …, m - 1} ^ d`
  have all squared distances in `{1, …, d m ^ 2}`, so `f_d(n) ≤ d m ^ 2 + 1`; with
  `m = ⌈n ^ (1 / d)⌉` this gives `f_d(n) ≤ (4 d + 1) n ^ (2 / d)` for every `n ≥ 1`;
* the packaging of the target: with `o(n) = 2 / d - log f_d(n) / log n` one has
  `f_d(n) = n ^ (2 / d - o(n))` exactly for large `n`, and `o(n) → 0` follows from the upper bound
  together with a lower bound `n ^ (2 / d - ε) ≤ f_d(n)` for every `ε > 0`.

What is left is that lower bound, the open half of the problem, split by dimension: `d = 3` (H1)
and `d ≥ 4` (H2). The best known lower bounds, by Solymosi and Vu [SoVu08], have the exponent
`2 / d - 2 / (d (d + 2))`.
-/

namespace OMA.R_Erdos1083_erdos_1083_R1

open Filter Asymptotics
open scoped EuclideanGeometry

/-- The lower bound in dimension 3: for every `ε > 0`, every set of `n` points of `ℝ ^ 3` with
`n` large determines at least `n ^ (2 / 3 - ε)` distinct distances. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ ((2 : ℝ) / 3 - ε) ≤ (minimalDistinctDistances (ℝ^3) n : ℝ)

/-- The lower bound in dimension `d ≥ 4`: for every `ε > 0`, every set of `n` points of `ℝ ^ d`
with `n` large determines at least `n ^ (2 / d - ε)` distinct distances. -/
def H2 : Prop :=
  ∀ d : ℕ, 4 ≤ d → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ ((2 : ℝ) / (d : ℝ) - ε) ≤ (minimalDistinctDistances (ℝ^d) n : ℝ)

/-- The squared distance between two points of the grid `{0, …, m - 1} ^ d` is a natural number
at most `d m ^ 2`. -/
lemma grid_dist (d m : ℕ) (c c' : Fin d → Fin m) :
    ∃ s : ℕ, s ≤ d * m ^ 2 ∧
      dist (WithLp.toLp 2 (fun i => ((c i : ℕ) : ℝ)) : ℝ^d)
        (WithLp.toLp 2 (fun i => ((c' i : ℕ) : ℝ))) = Real.sqrt s := by
  refine ⟨∑ i, (Int.natAbs (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ))) ^ 2, ?_, ?_⟩
  · have hle : ∀ i, (Int.natAbs (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ))) ^ 2 ≤ m ^ 2 := by
      intro i
      have h1 := (c i).isLt
      have h2 := (c' i).isLt
      have : Int.natAbs (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)) ≤ m := by omega
      exact Nat.pow_le_pow_left this 2
    calc ∑ i, (Int.natAbs (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ))) ^ 2
        ≤ ∑ _i : Fin d, m ^ 2 := Finset.sum_le_sum (fun i _ => hle i)
      _ = d * m ^ 2 := by simp
  · rw [EuclideanSpace.dist_eq]
    congr 1
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.dist_eq, Nat.cast_natAbs, Int.cast_abs]
    simp only [sq_abs]
    push_cast
    ring

/-- The grid map `{0, …, m - 1} ^ d → ℝ ^ d` is injective. -/
lemma grid_injective (d m : ℕ) :
    Function.Injective (fun c : Fin d → Fin m => (WithLp.toLp 2 (fun i => ((c i : ℕ) : ℝ)) : ℝ^d)) := by
  intro c c' h
  funext i
  have := congrArg (fun x : ℝ^d => x.ofLp i) h
  simp only at this
  exact Fin.ext (by exact_mod_cast this)

/-- Erdős's lattice bound: if `n ≤ m ^ d`, then some `n` points of the grid `{0, …, m - 1} ^ d`
determine at most `d m ^ 2 + 1` distances. -/
lemma minimalDistinctDistances_le (d m n : ℕ) (h : n ≤ m ^ d) :
    minimalDistinctDistances (ℝ^d) n ≤ d * m ^ 2 + 1 := by
  classical
  set G : Finset (ℝ^d) := Finset.univ.image
    (fun c : Fin d → Fin m => (WithLp.toLp 2 (fun i => ((c i : ℕ) : ℝ)) : ℝ^d)) with hGdef
  have hG : G.card = m ^ d := by
    rw [hGdef, Finset.card_image_of_injective _ (grid_injective d m)]
    simp
  obtain ⟨P, hPG, hP⟩ := Finset.exists_subset_card_eq (hG ▸ h)
  have hdd : distinctDistances P ≤ d * m ^ 2 + 1 := by
    unfold distinctDistances distanceSet
    calc (P.offDiag.image fun pair : ℝ^d × ℝ^d => dist pair.1 pair.2).card
        ≤ ((Finset.range (d * m ^ 2 + 1)).image (fun s : ℕ => Real.sqrt s)).card := by
          apply Finset.card_le_card
          intro r hr
          rw [Finset.mem_image] at hr
          obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hr
          rw [Finset.mem_offDiag] at hxy
          obtain ⟨hx, hy, -⟩ := hxy
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp (hPG hx)
          obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp (hPG hy)
          obtain ⟨s, hs, hd⟩ := grid_dist d m c c'
          rw [Finset.mem_image]
          exact ⟨s, Finset.mem_range.mpr (by omega), hd.symm⟩
      _ ≤ (Finset.range (d * m ^ 2 + 1)).card := Finset.card_image_le
      _ = d * m ^ 2 + 1 := Finset.card_range _
  unfold minimalDistinctDistances
  refine le_trans (Nat.sInf_le ?_) hdd
  exact ⟨P, hP, rfl⟩

/-- The upper bound `f_d(n) ≤ (4 d + 1) n ^ (2 / d)` for `n ≥ 1`. -/
lemma minimalDistinctDistances_le_rpow (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (minimalDistinctDistances (ℝ^d) n : ℝ) ≤ (4 * d + 1) * (n : ℝ) ^ ((2 : ℝ) / d) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) ≤ n := by positivity
  set t : ℝ := (n : ℝ) ^ ((1 : ℝ) / d) with htdef
  have ht1 : 1 ≤ t := Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  set m := ⌈t⌉₊ with hmdef
  have hmt : (m : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
  have htm : t ≤ m := Nat.le_ceil t
  have htd : t ^ d = n := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0, one_div_mul_cancel hdpos.ne',
      Real.rpow_one]
  have hnm : n ≤ m ^ d := by
    have h2 : t ^ d ≤ (m : ℝ) ^ d := pow_le_pow_left₀ (by linarith) htm d
    rw [htd] at h2
    exact_mod_cast h2
  have key := minimalDistinctDistances_le d m n hnm
  have ht2 : (n : ℝ) ^ ((2 : ℝ) / d) = t ^ 2 := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0]
    congr 1
    push_cast
    ring
  have hkey : (minimalDistinctDistances (ℝ^d) n : ℝ) ≤ d * (m : ℝ) ^ 2 + 1 := by
    exact_mod_cast key
  rw [ht2]
  have hm2 : (m : ℝ) ≤ 2 * t := by linarith
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hsq : (m : ℝ) ^ 2 ≤ (2 * t) ^ 2 := pow_le_pow_left₀ hm0 hm2 2
  have ht2' : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ ht1
  nlinarith

/-- Packaging the two bounds as `f_d(n) = n ^ (2 / d - o(n))` with `o(n) → 0`. -/
lemma exists_littleO (d : ℕ) (hd : 1 ≤ d) (f : ℕ → ℕ) (C : ℝ) (hC : 0 < C)
    (hU : ∀ n : ℕ, 1 ≤ n → (f n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / d))
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((2 : ℝ) / d - ε) ≤ f n) :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop, (f n : ℝ) = (n : ℝ) ^ ((2 : ℝ) / (d : ℝ) - o n) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogtend : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun n => (2 : ℝ) / d - Real.log (f n) / Real.log n, ?_, ?_⟩
  · rw [show (1 : ℕ → ℝ) = fun _ => (1 : ℝ) from rfl, Asymptotics.isLittleO_one_iff]
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · -- lower side, from the upper bound on `f`
      filter_upwards [hlogtend.eventually_gt_atTop (max 1 (Real.log C / (-a))),
        eventually_ge_atTop 2] with n hn h2
      have hn1 : (1 : ℝ) < n := by exact_mod_cast h2
      have hlogpos : 0 < Real.log n := Real.log_pos hn1
      have hnpos : (0 : ℝ) < n := by linarith
      rcases Nat.eq_zero_or_pos (f n) with h0 | hfpos
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero, zero_div, sub_zero]
        have : (0 : ℝ) < 2 / d := by positivity
        linarith
      · have hf : (0 : ℝ) < f n := by exact_mod_cast hfpos
        have hup := hU n (by omega)
        have hlogf : Real.log (f n) ≤ Real.log C + (2 / d) * Real.log n := by
          have := Real.log_le_log hf hup
          rwa [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hnpos _).ne', Real.log_rpow hnpos] at this
        have hdiv : Real.log (f n) / Real.log n ≤ Real.log C / Real.log n + 2 / d := by
          rw [div_le_iff₀ hlogpos, add_mul, div_mul_cancel₀ _ hlogpos.ne']
          linarith
        have hCn : Real.log C / Real.log n < -a := by
          rw [div_lt_iff₀ hlogpos]
          have h1 : Real.log C / (-a) < Real.log n := lt_of_le_of_lt (le_max_right _ _) hn
          have hna : 0 < -a := by linarith
          rw [div_lt_iff₀ hna] at h1
          linarith
        linarith
    · -- upper side, from the lower bound hypothesis
      filter_upwards [hL (a / 2) (by linarith), eventually_ge_atTop 2] with n hn h2
      have hn1 : (1 : ℝ) < n := by exact_mod_cast h2
      have hlogpos : 0 < Real.log n := Real.log_pos hn1
      have hnpos : (0 : ℝ) < n := by linarith
      have hrpos : 0 < (n : ℝ) ^ ((2 : ℝ) / d - a / 2) := Real.rpow_pos_of_pos hnpos _
      have hlogf : ((2 : ℝ) / d - a / 2) * Real.log n ≤ Real.log (f n) := by
        have := Real.log_le_log hrpos hn
        rwa [Real.log_rpow hnpos] at this
      have hdiv : (2 : ℝ) / d - a / 2 ≤ Real.log (f n) / Real.log n := by
        rw [le_div_iff₀ hlogpos]
        linarith
      linarith
  · filter_upwards [hL 1 one_pos, eventually_ge_atTop 2] with n hn h2
    have hn1 : (1 : ℝ) < n := by exact_mod_cast h2
    have hnpos : (0 : ℝ) < n := by linarith
    have hfpos : (0 : ℝ) < f n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hn
    have hlog : Real.log n ≠ 0 := (Real.log_pos hn1).ne'
    rw [show (2 : ℝ) / d - ((2 : ℝ) / d - Real.log (f n) / Real.log n)
        = Real.log (f n) / Real.log n by ring,
      Real.rpow_def_of_pos hnpos, mul_div_cancel₀ _ hlog, Real.exp_log hfpos]

theorem main : H1 → H2 → type_of% @Erdos1083.erdos_1083 := by
  intro h1 h2 d hd
  have hd1 : 1 ≤ d := by omega
  have hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((2 : ℝ) / d - ε) ≤ (minimalDistinctDistances (ℝ^d) n : ℝ) := by
    rcases Nat.lt_or_ge d 4 with h | h
    · have h3 : d = 3 := by omega
      subst h3
      intro ε hε
      simpa using h1 ε hε
    · exact h2 d h
  exact exists_littleO d hd1 (fun n => minimalDistinctDistances (ℝ^d) n) (4 * d + 1)
    (by positivity) (fun n hn => minimalDistinctDistances_le_rpow d n hd1 hn) hL

end OMA.R_Erdos1083_erdos_1083_R1
