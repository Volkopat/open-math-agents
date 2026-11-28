import OMAStatements.S_mo_371820
import Mathlib

open Finset Set OMA.S_mo_371820

private theorem concaveIndividual {b : ℝ} (hb : 0 < b) :
    ConcaveOn ℝ (Ici 0) (individual b) := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a c ha hc hac
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  let z := a*x + c*y
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have dx : 0 < 1 + b*x := by positivity
  have dy : 0 < 1 + b*y := by positivity
  have dz : 0 < 1 + b*z := by positivity
  let f := fun t : ℝ => 1+t/(1+b*t)
  have fx : 0 < f x := by dsimp [f]; positivity
  have fy : 0 < f y := by dsimp [f]; positivity
  have fz : 0 < f z := by dsimp [f]; positivity
  have mix : a*f x + c*f y ≤ f z := by
    have hident : f z - (a*f x + c*f y) =
        (a*c*b*(x-y)^2) / ((1+b*x)*(1+b*y)*(1+b*z)) := by
      have he : c = 1 - a := by linarith
      subst c
      dsimp [f, z] at *
      field_simp [dx.ne', dy.ne', dz.ne']
      ring
    rw [← sub_nonneg, hident]
    positivity
  change a * Real.log (f x) + c * Real.log (f y) ≤ Real.log (f z)
  refine (strictConcaveOn_log_Ioi.concaveOn.2 (show f x ∈ Set.Ioi 0 from fx)
    (show f y ∈ Set.Ioi 0 from fy) ha hc hac).trans ?_
  have hmix : 0 < a*f x + c*f y := by
    rcases eq_or_lt_of_le ha with h | h
    · have hc' : c = 1 := by linarith
      simp [← h, hc', fy]
    · exact add_pos_of_pos_of_nonneg (mul_pos h fx) (mul_nonneg hc fy.le)
  exact Real.log_le_log hmix mix

theorem OMA.solution : type_of% @OMA.S_mo_371820.main := by
  classical
  intro m n A p β hβ
  have hconv : Convex ℝ (feasible A p) := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hx₁, hx₂⟩ := hx
    obtain ⟨hy₁, hy₂⟩ := hy
    constructor
    · intro i
      change 0 ≤ a*x i + b*y i
      exact add_nonneg (mul_nonneg ha (hx₁ i)) (mul_nonneg hb (hy₁ i))
    · intro k
      change (∑ i, A k i * (a*x i + b*y i)) ≤ p k
      calc
        _ = a*(∑ i, A k i*x i) + b*(∑ i, A k i*y i) := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          apply sum_congr rfl
          intro i _
          ring
        _ ≤ a*p k + b*p k := add_le_add (mul_le_mul_of_nonneg_left (hx₂ k) ha)
          (mul_le_mul_of_nonneg_left (hy₂ k) hb)
        _ = p k := by rw [← add_mul, hab, one_mul]
  refine ⟨⟨hconv, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    change a*(∑ i, individual (β i i) (x i)) + b*(∑ i, individual (β i i) (y i)) ≤
      ∑ i, individual (β i i) (a*x i + b*y i)
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro i _
    exact (concaveIndividual (hβ i i)).2 (show x i ∈ Set.Ici 0 from hx.1 i)
      (show y i ∈ Set.Ici 0 from hy.1 i) ha hb hab
  · intro x hx
    have x0 (i : Fin n) : 0 ≤ x i := hx.1 i
    have d0 (i : Fin n) : 0 < 1 + β i i * x i :=
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (hβ i i).le (x0 i))
    have hsum (i : Fin n) : β i i * x i ≤ ∑ j, β j i * x j := by
      exact single_le_sum (fun j _ => mul_nonneg (hβ j i).le (x0 j)) (mem_univ i)
    constructor
    · apply sum_le_sum
      intro i _
      have hd : 0 < 1 + ∑ j, β j i*x j := by linarith [d0 i, hsum i]
      have hdiv : x i / (1 + ∑ j, β j i*x j) ≤ x i / (1 + β i i*x i) :=
        div_le_div_of_nonneg_left (x0 i) (d0 i) (by linarith [hsum i])
      exact Real.log_le_log (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (x0 i) hd.le)) (by linarith)
    · intro hx0
      obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
        by_contra! h
        apply hx0
        ext i
        exact le_antisymm (h i) (x0 i)
      have hterm (j : Fin n) : individual (β j j) (x j) ≤ Real.log (1 + x j) := by
        apply Real.log_le_log (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (x0 j) (d0 j).le))
        have h := (div_le_iff₀ (d0 j)).2 (show x j ≤ x j * (1 + β j j*x j) by
          nlinarith [mul_nonneg (hβ j j).le (sq_nonneg (x j))])
        linarith
      have hlt : individual (β i i) (x i) < Real.log (1 + x i) := by
        apply Real.log_lt_log (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (x0 i) (d0 i).le))
        have h := (div_lt_iff₀ (d0 i)).2 (show x i < x i * (1 + β i i*x i) by
          nlinarith [mul_pos (hβ i i) (sq_pos_of_pos hi)])
        linarith
      exact sum_lt_sum (fun j _ => hterm j) ⟨i, mem_univ i, hlt⟩
  · intro h hz hbound i t ht
    let x : Allocation n := Function.update 0 i t
    have xi : x i = t := by simp [x]
    have xj (j : Fin n) (hj : j ≠ i) : x j = 0 := by simp [x, Function.update_of_ne hj]
    have axis : rate β x = individual (β i i) t := by
      unfold rate
      rw [sum_eq_single i]
      · have eq : (∑ j, β j i*x j) = β i i*t := by
          rw [sum_eq_single i]
          · rw [xi]
          · intro j _ hj
            simp [xj j hj]
          · simp
        rw [xi, eq]
        rfl
      · intro j _ hj
        simp [xj j hj]
      · simp
    have haxis : (∑ j, h j (x j)) = h i t := by
      rw [sum_eq_single i]
      · rw [xi]
      · intro j _ hj
        rw [xj j hj, hz j]
      · simp
    have hnonneg : ∀ j, 0 ≤ x j := by
      intro j
      by_cases hj : j = i
      · rwa [hj, xi]
      · rw [xj j hj]
    simpa only [axis, haxis] using hbound x hnonneg