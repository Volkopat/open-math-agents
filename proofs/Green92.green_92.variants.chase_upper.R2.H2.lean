import OMAReductions.R_Green92_green_92_variants_chase_upper_R2

/-!
# A finite maximum-likelihood decoder for trace reconstruction

At a sample where the decoder chooses a competing string, that string has likelihood at least
as large as the true string's likelihood. The square root of their likelihood ratio then
bounds the indicator of that error. Its average factors over independently chosen masks,
with each single-coordinate factor equal to the affinity of the two trace distributions.
-/

namespace OMA.Green92Affinity

open Finset
open scoped Classical

variable {X S O : Type*} [Fintype S] [DecidableEq O]

private noncomputable def count (trace : X → S → O) (x : X) (w : O) : ℝ :=
  ((univ.filter fun s => trace x s = w).card : ℝ)

private theorem count_nonneg (trace : X → S → O) (x : X) (w : O) :
    0 ≤ count trace x w :=
  Nat.cast_nonneg _

private theorem count_pos (trace : X → S → O) (x : X) (s : S) :
    0 < count trace x (trace x s) := by
  unfold count
  exact Nat.cast_pos.mpr (card_pos.mpr ⟨s, mem_filter.mpr ⟨mem_univ s, rfl⟩⟩)

private noncomputable def likelihood (trace : X → S → O) {m : ℕ}
    (o : Fin m → O) (x : X) : ℝ :=
  ∏ j, count trace x (o j)

private noncomputable def ratio (trace : X → S → O) (x y : X) (s : S) : ℝ :=
  Real.sqrt (count trace y (trace x s) / count trace x (trace x s))

private theorem sum_ratio (trace : X → S → O) [Nonempty S] (x y : X) :
    (∑ s, ratio trace x y s) = (Fintype.card S : ℝ) *
      ∑ w ∈ univ.image (trace x),
        Real.sqrt (count trace x w / Fintype.card S) *
          Real.sqrt (count trace y w / Fintype.card S) := by
  let q : ℝ := Fintype.card S
  have hq : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  rw [mul_sum]
  rw [← sum_fiberwise_of_maps_to (fun s _ => mem_image_of_mem (trace x) (mem_univ s))
    (ratio trace x y)]
  apply sum_congr rfl
  intro w hw
  have hconst : (∑ s ∈ univ.filter (fun s => trace x s = w), ratio trace x y s) =
      count trace x w * Real.sqrt (count trace y w / count trace x w) := by
    calc
      _ = ∑ _s ∈ univ.filter (fun s => trace x s = w),
          Real.sqrt (count trace y w / count trace x w) :=
        sum_congr rfl fun s hs => by simp only [ratio, (mem_filter.mp hs).2]
      _ = _ := by simp only [sum_const, nsmul_eq_mul, count]
  rw [hconst]
  obtain ⟨s, _, rfl⟩ := mem_image.mp hw
  have hx := count_pos trace x s
  have hy := count_nonneg trace y (trace x s)
  change _ = q * (Real.sqrt (count trace x (trace x s) / q) *
    Real.sqrt (count trace y (trace x s) / q))
  have hxs := Real.mul_self_sqrt hx.le
  have hqs := Real.mul_self_sqrt hq.le
  have hxs0 := (Real.sqrt_pos.2 hx).ne'
  simp only [Real.sqrt_div hy, Real.sqrt_div hx.le]
  rw [div_mul_div_comm, hqs, mul_div_cancel₀ _ hq.ne', ← mul_div_assoc, div_eq_iff hxs0]
  linear_combination -Real.sqrt (count trace y (trace x s)) * hxs

private theorem product_ratio_ge_one (trace : X → S → O) {m : ℕ} (x y : X)
    (u : Fin m → S)
    (h : likelihood trace (fun j => trace x (u j)) x ≤
      likelihood trace (fun j => trace x (u j)) y) :
    1 ≤ ∏ j, ratio trace x y (u j) := by
  change 1 ≤ ∏ j, Real.sqrt (count trace y (trace x (u j)) / count trace x (trace x (u j)))
  rw [← Real.sqrt_prod _ (fun j _ =>
    div_nonneg (count_nonneg trace y _) (count_nonneg trace x _)), prod_div_distrib,
    Real.one_le_sqrt]
  exact (one_le_div (prod_pos fun j _ => count_pos trace x (u j))).2 h

private theorem competitor_card [DecidableEq X] (trace : X → S → O) [Nonempty S] {m : ℕ}
    (R : (Fin m → O) → X)
    (hR : ∀ o x, likelihood trace o x ≤ likelihood trace o (R o))
    (x y : X) :
    ((univ.filter (fun u : Fin m → S => R (fun j => trace x (u j)) = y)).card : ℝ) ≤
      (Fintype.card (Fin m → S) : ℝ) *
        (∑ w ∈ univ.image (trace x),
          Real.sqrt (count trace x w / Fintype.card S) *
            Real.sqrt (count trace y w / Fintype.card S)) ^ m := by
  let B := univ.filter (fun u : Fin m → S => R (fun j => trace x (u j)) = y)
  calc
    (B.card : ℝ) = ∑ _ ∈ B, (1 : ℝ) := by simp
    _ ≤ ∑ u ∈ B, ∏ j, ratio trace x y (u j) :=
      sum_le_sum fun u hu => product_ratio_ge_one trace x y u (by
        simpa only [(mem_filter.mp hu).2] using hR (fun j => trace x (u j)) x)
    _ ≤ ∑ u : Fin m → S, ∏ j, ratio trace x y (u j) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ =>
        prod_nonneg fun _ _ => Real.sqrt_nonneg _
    _ = (∑ s, ratio trace x y s) ^ m := by
      rw [sum_pow', Fintype.piFinset_univ]
    _ = _ := by rw [sum_ratio, mul_pow, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

private theorem decoder [Fintype X] [DecidableEq X] [Nonempty X] [Nonempty S]
    (trace : X → S → O) (m : ℕ) :
    ∃ R : (Fin m → O) → X, ∀ x,
      1 - (∑ y ∈ univ.erase x, (∑ w ∈ univ.image (trace x),
        Real.sqrt (count trace x w / Fintype.card S) *
          Real.sqrt (count trace y w / Fintype.card S)) ^ m) ≤
      ((univ.filter (fun u : Fin m → S => R (fun j => trace x (u j)) = x)).card : ℝ) /
        Fintype.card (Fin m → S) := by
  have exists_winner (o : Fin m → O) : ∃ z, ∀ x, likelihood trace o x ≤ likelihood trace o z := by
    obtain ⟨z, _, hz⟩ := univ.exists_max_image (likelihood trace o) univ_nonempty
    exact ⟨z, fun x => hz x (mem_univ x)⟩
  choose R hR using exists_winner
  refine ⟨R, fun x => ?_⟩
  let good := univ.filter (fun u : Fin m → S => R (fun j => trace x (u j)) = x)
  let bad := univ.filter (fun u : Fin m → S => R (fun j => trace x (u j)) ≠ x)
  let W (y : X) := univ.filter (fun u : Fin m → S => R (fun j => trace x (u j)) = y)
  have hsplit : good.card + bad.card = Fintype.card (Fin m → S) := by
    rw [show good.card + bad.card = univ.card from card_filter_add_card_filter_not .., card_univ]
  have hcover : bad ⊆ (univ.erase x).biUnion W := by
    intro u hu
    have hne : R (fun j => trace x (u j)) ≠ x := (mem_filter.mp hu).2
    exact mem_biUnion.mpr ⟨_, mem_erase.mpr ⟨hne, mem_univ _⟩,
      mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  have hb : (bad.card : ℝ) ≤ ∑ y ∈ univ.erase x, ((W y).card : ℝ) := by
    exact_mod_cast (card_le_card hcover).trans card_biUnion_le
  have hsum := hb.trans (sum_le_sum fun y (_ : y ∈ univ.erase x) =>
    competitor_card trace R hR x y)
  rw [← mul_sum] at hsum
  have hcard : (0 : ℝ) < Fintype.card (Fin m → S) := by exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hcard).2
  change _ ≤ (good.card : ℝ)
  have hsplitR : (good.card : ℝ) + bad.card = Fintype.card (Fin m → S) := by
    exact_mod_cast hsplit
  nlinarith only [hsplitR, hsum]

end OMA.Green92Affinity

theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_upper_R2.H2 := by
  intro n m
  simpa only [OMA.Green92Affinity.count, Finset.card_univ, Green92.successProb]
    using OMA.Green92Affinity.decoder (@Green92.trace n) m
