import OMAReductions.R_Erdos100_erdos_100_variants_guth_katz_R1

/-! The finite Cauchy–Schwarz step of the Elekes–Sharir approach to
Guth–Katz. Equal-displacement configurations inject into triples of points.
The two other parts of the equal-distance count are split at half-turns. -/

namespace OMA.R_Erdos100_erdos_100_variants_guth_katz_R1_H1_R1

open Finset Filter Asymptotics
open scoped Classical

private theorem energy_cs {X Y : Type*} (P : Finset X) (f : X → Y) :
    P.card^2 ≤ (P.image f).card *
      ((P ×ˢ P).filter (fun q ↦ f q.1 = f q.2)).card := by
  classical
  let D := P.image f
  let E := (P ×ˢ P).filter (fun q ↦ f q.1 = f q.2)
  let c (d : Y) := (P.filter (fun q ↦ f q = d)).card
  have total : P.card = ∑ d ∈ D, c d := card_eq_sum_card_image f P
  have fibre (d : Y) : E.filter (fun q ↦ f q.1 = d) =
      (P.filter (fun q ↦ f q = d)) ×ˢ (P.filter (fun q ↦ f q = d)) := by
    ext q
    simp only [E, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨hp,hq⟩,he⟩,hd⟩
      exact ⟨⟨hp,hd⟩,⟨hq,he.symm.trans hd⟩⟩
    · rintro ⟨⟨hp,hd⟩,⟨hq,hd'⟩⟩
      exact ⟨⟨⟨hp,hq⟩,hd.trans hd'.symm⟩,hd⟩
  have second : E.card = ∑ d ∈ D, c d ^ 2 := by
    calc
      _ = ∑ d ∈ D, (E.filter (fun q ↦ f q.1 = d)).card :=
        card_eq_sum_card_fiberwise fun q hq ↦ mem_image_of_mem f
          (mem_product.mp (mem_filter.mp hq).1).1
      _ = _ := by
        apply sum_congr rfl
        intro d _
        rw [fibre, card_product, pow_two]
  have cs := sum_mul_sq_le_sq_mul_sq (R := ℕ) D (fun _ ↦ 1) c
  change P.card^2 ≤ D.card * E.card
  rw [total, second]
  simpa using cs

private theorem equal_displacement_count (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    let P := A.offDiag
    ((P ×ˢ P).filter (fun q ↦ q.1.2 - q.1.1 = q.2.2 - q.2.1)).card ≤ A.card^3 := by
  classical
  dsimp only
  rw [pow_succ, pow_two, ← card_product, ← card_product]
  apply card_le_card_of_injOn (fun q ↦ (q.1, q.2.1))
  · intro q hq
    obtain ⟨hp,hq⟩ := mem_product.mp (mem_filter.mp hq).1
    exact mem_product.mpr
      ⟨mem_product.mpr ⟨(mem_offDiag.mp hp).1, (mem_offDiag.mp hp).2.1⟩,
        (mem_offDiag.mp hq).1⟩
  · intro q hq q' hq' heq
    change (q.1, q.2.1) = (q'.1, q'.2.1) at heq
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj heq
    have hqE := (mem_filter.mp hq).2
    have hq'E := (mem_filter.mp hq').2
    rw [h₁, h₂] at hqE
    have h₃ : q.2.2 = q'.2.2 := sub_left_inj.mp (hqE.symm.trans hq'E)
    exact Prod.ext h₁ (Prod.ext h₂ h₃)

private theorem minimum_attained (n : ℕ) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧ distinctDistances A =
      minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n := by
  classical
  let e : ℕ ↪ EuclideanSpace ℝ (Fin 2) :=
    ⟨fun i ↦ WithLp.toLp 2 (fun _ : Fin 2 ↦ (i : ℝ)), by
      intro i j h
      have hcast : (i : ℝ) = (j : ℝ) :=
        congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x (0 : Fin 2)) h
      exact_mod_cast hcast⟩
  let A := (range n).map e
  let S := {d : ℕ | ∃ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = n ∧
    distinctDistances B = d}
  have hn : S.Nonempty := ⟨distinctDistances A, A, by simp [A], rfl⟩
  exact Nat.sInf_mem hn

/-- Equal-length pairs of directed segments with reversed displacements. -/
def H1 : Prop :=
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    let P := A.offDiag
    ((P ×ˢ P).filter (fun q ↦ q.1.2 - q.1.1 = -(q.2.2 - q.2.1))).card ≤ A.card^3

/-- The Guth–Katz energy estimate for the other rotations. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 2 ≤ A.card →
    let P := A.offDiag
    let w (q : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) := q.2 - q.1
    (((P ×ˢ P).filter (fun q ↦ dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧
      w q.1 ≠ w q.2 ∧ w q.1 ≠ -w q.2)).card : ℝ) ≤
      C * (A.card : ℝ)^3 * Real.log (A.card : ℝ)

theorem main : H1 → H2 → OMA.R_Erdos100_erdos_100_variants_guth_katz_R1.H1 := by
  classical
  intro halfturn bound
  obtain ⟨C, hC, bound⟩ := bound
  refine IsBigO.of_bound (4 * (C + 2)) ?_
  have Llarge : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)).eventually
        (eventually_ge_atTop _)
  filter_upwards [Llarge, eventually_ge_atTop (2 : ℕ)] with n hL hn
  obtain ⟨A, hA, hmin⟩ := minimum_attained n
  let P := A.offDiag
  let f (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) := dist s.1 s.2
  let w (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) := s.2 - s.1
  let E := (P ×ˢ P).filter (fun q ↦ f q.1 = f q.2)
  let T := (P ×ˢ P).filter (fun q ↦ w q.1 = w q.2)
  let U := (P ×ˢ P).filter (fun q ↦ w q.1 = -w q.2)
  let R := (P ×ˢ P).filter (fun q ↦ f q.1 = f q.2 ∧
    w q.1 ≠ w q.2 ∧ w q.1 ≠ -w q.2)
  have sub : E ⊆ T ∪ U ∪ R := by
    intro q hq
    obtain ⟨hp, hdist⟩ := mem_filter.mp hq
    by_cases he : w q.1 = w q.2
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp,he⟩))
    by_cases hs : w q.1 = -w q.2
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hp,hs⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,hdist,he,hs⟩)
  have hCard : E.card ≤ T.card + U.card + R.card :=
    (card_le_card sub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hT : (T.card : ℝ) ≤ (n : ℝ)^3 := by
    rw [← hA]
    exact_mod_cast equal_displacement_count A
  have hU : (U.card : ℝ) ≤ (n : ℝ)^3 := by
    rw [← hA]
    exact_mod_cast halfturn A
  have hR : (R.card : ℝ) ≤ C * (n : ℝ)^3 * Real.log (n : ℝ) := by
    rw [← hA]
    exact bound A (hA.symm ▸ hn)
  have hE : (E.card : ℝ) ≤ (C + 2) * (n : ℝ)^3 * Real.log (n : ℝ) := by
    have he : (E.card : ℝ) ≤ (T.card : ℝ) + U.card + R.card := by exact_mod_cast hCard
    have hd : 2 * (n : ℝ)^3 ≤ 2 * (n : ℝ)^3 * Real.log (n : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * (n : ℝ)^3 by positivity)
    linarith only [he,hT,hU,hR,hd]
  have hcs : (P.card : ℝ)^2 ≤ (distinctDistances A : ℝ) * (E.card : ℝ) := by
    have cs : P.card^2 ≤ distinctDistances A * E.card := energy_cs P f
    exact_mod_cast cs
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (P.card : ℝ) = (n : ℝ) * n - n := by
    have hP : P.card = n * n - n := by simp [P, offDiag_card, hA]
    rw [hP, Nat.cast_sub (by nlinarith : n ≤ n * n), Nat.cast_mul]
  have hhalf : (n : ℝ)^2 / 2 ≤ P.card := by
    rw [hp]
    have : 0 ≤ (n : ℝ) * ((n : ℝ) - 2) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hnR)
    nlinarith
  have hsquare : ((n : ℝ)^2 / 2)^2 ≤ (P.card : ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) hhalf 2
  have hprod : ((n : ℝ)^2 / 2)^2 ≤
      (distinctDistances A : ℝ) * ((C + 2) * (n : ℝ)^3 * Real.log (n : ℝ)) :=
    hsquare.trans (hcs.trans (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)))
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hnRpos : 0 < (n : ℝ) := by linarith
  change ‖(n : ℝ) / Real.log (n : ℝ)‖ ≤
    (4 * (C + 2)) * ‖(minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n : ℝ)‖
  rw [← hmin, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) hlogpos.le),
    abs_of_nonneg (Nat.cast_nonneg (distinctDistances A) : (0 : ℝ) ≤ distinctDistances A)]
  apply (div_le_iff₀ hlogpos).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos hnRpos 3)).mp
  nlinarith only [hprod]

end OMA.R_Erdos100_erdos_100_variants_guth_katz_R1_H1_R1
