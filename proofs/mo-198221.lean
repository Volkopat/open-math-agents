import OMAStatements.S_mo_198221

namespace OMA.S_mo_198221
open Finset
open scoped RealInnerProductSpace
noncomputable section

private def orient (z : Plane) : Plane := ‖z‖⁻¹ • z

private theorem orient_norm (z : Plane) : ‖orient z‖ ≤ 1 := by
  by_cases hz : z=0
  · simp [hz,orient]
  · simp [orient,norm_smul,norm_ne_zero_iff.mpr hz]

private theorem orient_eval (z : Plane) : ⟪orient z,z⟫ = ‖z‖ := by
  by_cases hz : z=0
  · simp [hz]
  · rw [orient,real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp

private def linearScore {n : ℕ} (u : Directions n) (x : Configuration n) : ℝ :=
  ∑ i, ∑ j, ⟪u i j,x i-x j⟫

private theorem rearrange {n : ℕ} (u : Directions n) (x : Configuration n) :
    linearScore u x = ∑ i, ⟪resultant u i,x i⟫ := by
  simp only [linearScore,resultant,inner_sub_right,sum_inner,inner_sub_left,Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

private theorem belowEnergy {n : ℕ} (u : Directions n) (hu : withinDisk u) (x : Configuration n) :
    linearScore u x ≤ energy x := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hu i j))

private theorem belowScore {n : ℕ} {C : Set Plane} {p : Plane → Plane} (hp : supportChoice C p)
    (u : Directions n) (x : Configuration n) (hx : ∀ i, x i ∈ C) :
    linearScore u x ≤ score p u := by
  rw [rearrange]
  exact Finset.sum_le_sum (fun i _ => (hp _).2 _ (hx i))

private theorem score_le {n : ℕ} (p : Plane → Plane) (u : Directions n) (hu : withinDisk u) :
    score p u ≤ energy (picked p u) := by
  simpa [rearrange,score] using belowEnergy u hu (picked p u)

private def fromPoints {n : ℕ} (x : Configuration n) : Directions n := fun i j => orient (x i-x j)

private theorem recover {n : ℕ} (x : Configuration n) : linearScore (fromPoints x) x = energy x := by
  simp [linearScore,energy,fromPoints,orient_eval]

private theorem exactPick {n : ℕ} {C : Set Plane} (hC : IsCompact C) (h0 : C.Nonempty)
    {p : Plane → Plane} (hp : supportChoice C p) :
    (∃ u : Directions n, withinDisk u ∧ ∀ v : Directions n, withinDisk v → score p v ≤ score p u) ∧
    (∀ u : Directions n, withinDisk u → (∀ v : Directions n, withinDisk v → score p v ≤ score p u) →
      energy (picked p u) = score p u ∧ ∀ x : Configuration n, (∀ i, x i ∈ C) →
      energy x ≤ energy (picked p u)) := by
  have bound (u : Directions n) (hmax : ∀ v : Directions n, withinDisk v → score p v ≤ score p u)
      (x : Configuration n) (hx : ∀ i, x i ∈ C) : energy x ≤ score p u :=
    (recover x ▸ belowScore hp (fromPoints x) x hx).trans (hmax _ (fun i j => orient_norm _))
  constructor
  · let K := Set.univ.pi (fun _ : Fin n => C)
    have hk : IsCompact K := isCompact_univ_pi (fun _ => hC)
    obtain ⟨z,hz⟩ := h0
    have hK : K.Nonempty := ⟨fun _ => z,fun _ _ => hz⟩
    have hc : Continuous (energy (n := n)) := by unfold energy; fun_prop
    obtain ⟨x,hx,hxmax⟩ := hk.exists_isMaxOn hK hc.continuousOn
    refine ⟨fromPoints x,fun i j => orient_norm _,fun v hv => ?_⟩
    have hx' (i : Fin n) := hx i (Set.mem_univ _)
    calc
      score p v ≤ energy (picked p v) := score_le _ _ hv
      _ ≤ energy x := hxmax (fun i _ => (hp _).1)
      _ = linearScore (fromPoints x) x := (recover x).symm
      _ ≤ score p (fromPoints x) := belowScore hp _ _ hx'
  · intro u hu hmax
    have he := score_le p u hu
    exact ⟨le_antisymm (bound u hmax _ (fun i => (hp _).1)) he,
      fun x hx => (bound u hmax x hx).trans he⟩

end
end OMA.S_mo_198221

namespace OMA.S_mo_198221
open Finset
open scoped RealInnerProductSpace
noncomputable section

private theorem net_exists (ε : ℝ) (h : 0 < ε) : ∃ D : Finset Plane, directionNet ε D := by
  classical
  obtain ⟨t,hts,ht,cover⟩ := (isCompact_closedBall (0 : Plane) 1).finite_cover_balls h
  refine ⟨ht.toFinset,fun d hd => ?_,fun z hz => ?_⟩
  · simpa using hts (ht.mem_toFinset.mp hd)
  · have hz' : z ∈ Metric.closedBall (0 : Plane) 1 := by simpa using hz
    obtain ⟨d,hd,hzd⟩ := Set.mem_iUnion₂.mp (cover hz')
    exact ⟨d,ht.mem_toFinset.mpr hd,(Metric.mem_ball.mp hzd).le⟩

private theorem netPick {n : ℕ} {C : Set Plane} {p : Plane → Plane} (hp : supportChoice C p)
    (ε : ℝ) (D : Finset Plane) (hD : directionNet ε D) :
    (∃ u : Directions n, uses D u ∧ ∀ v : Directions n, uses D v → score p v ≤ score p u) ∧
    ∀ u : Directions n, uses D u → (∀ v : Directions n, uses D v → score p v ≤ score p u) →
      ∀ x : Configuration n, (∀ i, x i ∈ C) → (1-ε)*energy x ≤ energy (picked p u) := by
  classical
  constructor
  · obtain ⟨d,hd,_⟩ := hD.2 0 (by simp)
    let : Nonempty ↥D := ⟨⟨d,hd⟩⟩
    let val (w : Fin n → Fin n → ↥D) : Directions n := fun i j => (w i j).val
    obtain ⟨w,_,hw⟩ := Finset.exists_max_image Finset.univ (fun w => score p (val w)) Finset.univ_nonempty
    refine ⟨val w,fun i j => (w i j).property,fun v hv => ?_⟩
    exact hw (fun i j => ⟨v i j,hv i j⟩) (Finset.mem_univ _)
  · intro u hu hmax x hx
    have hex (i j : Fin n) := hD.2 (orient (x i-x j)) (orient_norm _)
    choose a ha hnear using hex
    have hpair (i j : Fin n) : (1-ε)*‖x i-x j‖ ≤ ⟪a i j,x i-x j⟫ := by
      have hb := (real_inner_le_norm (orient (x i-x j)-a i j) (x i-x j)).trans
        (mul_le_mul_of_nonneg_right (show ‖orient (x i-x j)-a i j‖ ≤ ε by
          simpa only [dist_eq_norm] using hnear i j) (norm_nonneg _))
      rw [inner_sub_left,orient_eval] at hb
      linarith
    calc
      (1-ε)*energy x ≤ linearScore a x := by
        simp only [energy,linearScore,Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
      _ ≤ score p a := belowScore hp _ _ hx
      _ ≤ score p u := hmax _ ha
      _ ≤ energy (picked p u) := score_le _ _ (fun i j => hD.1 _ (hu i j))

end
end OMA.S_mo_198221

open OMA.S_mo_198221
open scoped RealInnerProductSpace
noncomputable section

theorem OMA.solution : type_of% @OMA.S_mo_198221.main := by
  refine ⟨net_exists,fun C hC h0 => ?_⟩
  have h (b : Plane) : ∃ y ∈ C, ∀ z ∈ C, ⟪b,z⟫ ≤ ⟪b,y⟫ := by
    have hc : Continuous (fun z : Plane => ⟪b,z⟫) := by fun_prop
    obtain ⟨y,hy,hm⟩ := hC.exists_isMaxOn h0 hc.continuousOn
    exact ⟨y,hy,fun _ hz => hm hz⟩
  choose p hmem hmax using h
  have hp : supportChoice C p := fun b => ⟨hmem b,hmax b⟩
  exact ⟨p,hp,fun n => ⟨exactPick hC h0 hp,fun ε D => netPick hp ε D⟩⟩

end
