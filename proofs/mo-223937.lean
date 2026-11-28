import OMAStatements.S_mo_223937

namespace OMA.S_mo_223937
open Finset

lemma atom_perm {n : ℕ} (V : Fin n → Fin n → ℝ) (z : ℝ) (hz : 0≤z)
    (hV : ∀ i j, 0≤V i j) (hr : ∀ i, ∑ j, V i j = z)
    (hc : ∀ j, ∑ i, V i j = z) (hdis : ∀ i j k, j≠k → V i j * V i k=0) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i j, V i j = if σ i=j then z else 0 := by
  classical
  rcases hz.eq_or_lt with rfl | hpos
  · refine ⟨Equiv.refl _, fun i j => ?_⟩
    have h := Finset.single_le_sum (s := Finset.univ) (f := V i)
      (fun k _ => hV i k) (Finset.mem_univ j)
    split_ifs <;> exact le_antisymm (h.trans_eq (hr i)) (hV i j)
  · have hrow (i : Fin n) : ∃ j, V i j ≠ 0 := by
      by_contra! h
      have hz0 := hr i
      simp [h] at hz0
      linarith
    choose f hf using hrow
    have hoff (i j : Fin n) (h : f i ≠ j) : V i j = 0 :=
      (mul_eq_zero.mp (hdis i (f i) j h)).resolve_left (hf i)
    have hon (i : Fin n) : V i (f i) = z := by
      rw [← hr i, Finset.sum_eq_single (f i)]
      · intro j _ hji
        exact hoff i j hji.symm
      · simp
    have hsur : Function.Surjective f := by
      intro j
      by_contra! h
      have hz0 := hc j
      simp [fun i => hoff i j (h i)] at hz0
      linarith
    refine ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hsur, hsur⟩, ?_⟩
    intro i j
    change V i j = if f i = j then z else 0
    split_ifs with h
    · simpa [← h] using hon i
    · exact hoff i j h

end OMA.S_mo_223937

namespace OMA.S_mo_223937
open Finset

private lemma cycleSums {B C D : Type} [Fintype B] [Fintype C] [Fintype D]
    (f : B → C → D → ℝ) : (∑ j,∑ k,∑ a, f j k a) = ∑ a,∑ j,∑ k, f j k a := by
  calc _ = ∑ j,∑ a,∑ k, f j k a := sum_congr rfl (fun _ _ => sum_comm)
    _ = _ := sum_comm

lemma defect_gram {n : ℕ} {A : Type} [Fintype A] (v : Idx n → A → ℝ) (b : Fin n → Idx n) :
    defect (gram v) b = ∑ a, ((∑ j, v (b j) a) - v none a)^2 := by
  unfold defect gram
  rw [cycleSums, sum_comm (f:=fun j a => v (b j) a * v none a), mul_sum]
  rw [← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  simp only [← mul_sum,← sum_mul]
  ring

lemma project_gram {n : ℕ} {A : Type} [Fintype A] (X : Mat n) (v : Idx n → A → ℝ)
    (s : A → Equiv.Perm (Fin n))
    (hv : ∀ a i j, v (cell i j) a = if s a i=j then v none a else 0) :
    project X (gram v) = ∑ a, (v none a)^2 • orbit X (s a) := by
  classical
  ext i k
  simp only [project,gram,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,orbit,mul_sum]
  rw [cycleSums]
  apply sum_congr rfl
  intro a _
  simp [hv,mul_ite,ite_mul,sq]
  ring

end OMA.S_mo_223937

namespace OMA.S_mo_223937
open Finset

lemma lift_of_mem {n : ℕ} (X Y : Mat n) (hY : Y ∈ convexHull ℝ (Set.range (orbit X))) :
    ∃ M : Lift n, feasible M ∧ Y=project X M := by
  classical
  obtain ⟨A,inst,w,B,hw,hsum,hB,hY⟩ := mem_convexHull_iff_exists_fintype.mp hY
  choose s hs using hB
  let v (u : Idx n) (a : A) : ℝ := match u with
    | none => Real.sqrt (w a)
    | some (i,j) => if s a i=j then Real.sqrt (w a) else 0
  have h0 (u : Idx n) (a : A) : 0 ≤ v u a := by
    cases u with
    | none => exact Real.sqrt_nonneg _
    | some p => dsimp [v]; split_ifs <;> positivity
  have hv (a : A) (i j : Fin n) : v (cell i j) a = if s a i=j then v none a else 0 := rfl
  have hsqr (a : A) : (v none a)^2 = w a := Real.sq_sqrt (hw a)
  refine ⟨gram v,⟨⟨A,inst,v,h0,rfl⟩,?_,?_,?_,?_⟩,?_⟩
  · simpa only [gram,←sq,hsqr] using hsum
  · intro i
    rw [defect_gram]
    simp [hv]
  · intro j
    rw [defect_gram]
    simp [hv,←Equiv.eq_symm_apply]
  · intro i j k hjk
    apply sum_eq_zero
    intro a _
    change v (cell i j) a * v (cell i k) a = 0
    rw [hv,hv]
    split_ifs <;> simp_all
  · rw [project_gram X v s hv]
    simpa only [hsqr,hs] using hY.symm

lemma mem_of_lift {n : ℕ} (X : Mat n) (M : Lift n) (hM : feasible M) :
    project X M ∈ convexHull ℝ (Set.range (orbit X)) := by
  classical
  obtain ⟨⟨A,inst,v,hv,rfl⟩,hunit,hr,hc,hd⟩ := hM
  have zerodefect (b : Fin n → Idx n) (h : defect (gram v) b=0) (a : A) :
      ∑ j, v (b j) a = v none a := by
    rw [defect_gram] at h
    have := (sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg _)).mp h a (mem_univ a)
    nlinarith
  have hz (a : A) (i j k : Fin n) (hjk : j≠k) : v (cell i j) a * v (cell i k) a = 0 := by
    apply (sum_eq_zero_iff_of_nonneg (fun (a : A) _ => mul_nonneg (hv (cell i j) a) (hv (cell i k) a))).mp
      (hd i j k hjk) a (mem_univ a)
  choose s hS using fun a : A => atom_perm (fun i j => v (cell i j) a) (v none a) (hv none a)
    (fun i j => hv (cell i j) a) (fun i => zerodefect _ (hr i) a)
    (fun j => zerodefect _ (hc j) a) (hz a)
  apply mem_convexHull_of_exists_fintype (fun a => (v none a)^2) (fun a => orbit X (s a))
    (fun _ => sq_nonneg _) _ (fun a => Set.mem_range_self (s a))
  · exact (project_gram X v s hS).symm
  · simpa only [gram,←sq] using hunit

end OMA.S_mo_223937

theorem OMA.solution : type_of% @OMA.S_mo_223937.main := by
  intro n X Y
  exact ⟨OMA.S_mo_223937.lift_of_mem X Y,fun ⟨M,hM,he⟩ => he ▸ OMA.S_mo_223937.mem_of_lift X M hM⟩
