import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1
import Mathlib

/-! The order-nine and order-ten patterns in Brandt, Brinkmann and
Harmuth, "The generation of maximal triangle-free graphs" (1998), each
have a vertex at which four missing edges meet. A triangle-free host
with a vertex of degree at least n-1 already contains the required
complement embedding. This leaves maximum degrees seven and eight.

Lean formalization by @KoaOkano. The target masks are from the
upstream table formalized by @physbuzz. -/
namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1_H3_R1
open SimpleGraph
open scoped Classical

private def Found {n N : ℕ} (m : ℕ) (C : SimpleGraph (Fin N)) : Prop :=
  ∃ f : Fin n ↪ Fin N, ∀ i j, i < j →
    m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j)

private def missing {n : ℕ} (m : ℕ) (i j : Fin n) : Bool :=
  m.testBit ((min i j).val*n+(max i j).val)

private def holes {n : ℕ} (m : ℕ) (p : Fin n) : Finset {i : Fin n // i ≠ p} :=
  Finset.univ.filter fun i => missing m p i.1

private theorem independent {n N m : ℕ} {C : SimpleGraph (Fin N)}
    (S : Finset (Fin N)) (card : n ≤ S.card) (ind : C.IsIndepSet (S : Set _)) :
    Found (n:=n) m C := by
  classical
  obtain ⟨A, sub, eq⟩ := Finset.exists_subset_card_eq card
  let e : Fin n ≃ A := Fintype.equivOfCardEq (by simp [eq])
  let f : Fin n ↪ Fin N := e.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨f,?_⟩
  intro i j _ _ adj
  exact ind (sub (e i).2) (sub (e j).2) adj.ne adj

private theorem star {n N m : ℕ} (p : Fin n) (C : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (size : S.card+1=n) (ind : C.IsIndepSet (S : Set _))
    (y : Fin N) (out : y ∉ S)
    (few : (S.filter (C.Adj y)).card ≤ (holes m p).card) : Found (n:=n) m C := by
  classical
  let A := {i : Fin n // i ≠ p}
  let e : A ≃ S := Fintype.equivOfCardEq (by
    change Fintype.card {i : Fin n // ¬ i=p} = _
    rw [Fintype.card_subtype_compl]
    simp
    omega)
  let contacts : Finset A := Finset.univ.filter fun i => C.Adj y (e i).1
  have bound : contacts.card ≤ (S.filter (C.Adj y)).card := by
    apply Finset.card_le_card_of_injOn (fun i : A => (e i).1)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨(e i).2,(Finset.mem_filter.mp hi).2⟩
    · exact (Subtype.val_injective.comp e.injective).injOn
  obtain ⟨selected,sub,num⟩ := Finset.exists_subset_card_eq (bound.trans few)
  obtain ⟨perm,eq⟩ := Equiv.Perm.exists_map_finset_eq contacts selected num.symm
  let place (i : A) := (e (perm.symm i)).1
  have inS (i : A) : place i ∈ S := (e _).2
  have allowed (i : A) (adj : C.Adj y (place i)) : missing m p i.1=true := by
    have hit : perm.symm i ∈ contacts := Finset.mem_filter.mpr ⟨Finset.mem_univ _,adj⟩
    have chosen : i ∈ selected := eq ▸ Finset.mem_map.mpr ⟨perm.symm i,hit,perm.apply_symm_apply i⟩
    exact (Finset.mem_filter.mp (sub chosen)).2
  let put (i : Fin n) := if h : i=p then y else place ⟨i,h⟩
  have inj : Function.Injective put := by
    intro i j h
    by_cases hi : i=p <;> by_cases hj : j=p
    · exact hi.trans hj.symm
    · simp only [put,dif_pos hi,dif_neg hj] at h
      exact (out (h ▸ inS ⟨j,hj⟩)).elim
    · simp only [put,dif_neg hi,dif_pos hj] at h
      exact (out (h ▸ inS ⟨i,hi⟩)).elim
    · simp only [put,dif_neg hi,dif_neg hj] at h
      exact congrArg Subtype.val (perm.symm.injective (e.injective (Subtype.ext h)))
  refine ⟨⟨put,inj⟩,?_⟩
  intro i j lt no adj
  change C.Adj (put i) (put j) at adj
  have absent : missing m i j=false := by simpa [missing,min_eq_left lt.le,max_eq_right lt.le] using no
  by_cases hi : i=p
  · subst i
    have hj : j≠p := lt.ne'
    simp only [put,dif_pos rfl,dif_neg hj] at adj
    simpa [absent] using allowed ⟨j,hj⟩ adj
  by_cases hj : j=p
  · subst j
    simp only [put,dif_neg hi,dif_pos rfl] at adj
    have yes := allowed ⟨i,hi⟩ adj.symm
    have present : missing m i p=true := by
      simpa only [missing,min_comm p i,max_comm p i] using yes
    simp [absent] at present
  · simp only [put,dif_neg hi,dif_neg hj] at adj
    exact ind (inS ⟨i,hi⟩) (inS ⟨j,hj⟩) adj.ne adj

private theorem highDegree {n m : ℕ} (p : Fin n) (threshold : n ≤ 2*(holes m p).card+2)
    (C : SimpleGraph (Fin (2*n-1))) (ht : C.CliqueFree 3) (v : Fin (2*n-1))
    (high : n ≤ C.degree v+1) : Found (n:=n) m C := by
  classical
  let S := C.neighborFinset v
  have size : S.card = C.degree v := C.card_neighborFinset_eq_degree v
  have ind : C.IsIndepSet (S : Set _) := by
    simpa [S] using C.isIndepSet_neighborSet_of_triangleFree ht v
  by_cases many : n ≤ S.card
  · exact independent S many ind
  have exactSize : S.card+1=n := by omega
  by_cases good : ∃ y ∉ S, (S.filter (C.Adj y)).card ≤ (holes m p).card
  · obtain ⟨y,out,few⟩ := good
    exact star p C S exactSize ind y out few
  push Not at good
  have outside : C.IsIndepSet (Sᶜ : Finset _) := by
    intro x hx y hy ne adj
    let a := S.filter (C.Adj x)
    let b := S.filter (C.Adj y)
    have dis : Disjoint a b := by
      apply Finset.disjoint_left.mpr
      intro z hxz hyz
      exact C.isIndepSet_neighborSet_of_triangleFree ht z
        (Finset.mem_filter.mp hxz).2.symm (Finset.mem_filter.mp hyz).2.symm ne adj
    have total : a.card+b.card ≤ S.card := by
      rw [← Finset.card_union_of_disjoint dis]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    have ax : (holes m p).card < a.card := good x (Finset.mem_compl.mp hx)
    have by' : (holes m p).card < b.card := good y (Finset.mem_compl.mp hy)
    omega
  apply independent Sᶜ _ outside
  rw [Finset.card_compl,Fintype.card_fin]
  omega

/-- The remaining order-nine case has maximum degree at most seven. -/
def H1 : Prop := ∀ C : SimpleGraph (Fin 17), C.CliqueFree 3 →
  (∀ v, C.degree v ≤ 7) → ∃ f : Fin 9 ↪ Fin 17, ∀ i j, i<j →
    (2251801971660822 : ℕ).testBit (i.val*9+j.val)=false → ¬ C.Adj (f i) (f j)

/-- The remaining order-ten case has maximum degree at most eight. -/
def H2 : Prop := ∀ C : SimpleGraph (Fin 19), C.CliqueFree 3 →
  (∀ v, C.degree v ≤ 8) → ∃ f : Fin 10 ↪ Fin 19, ∀ i j, i<j →
    (618970019714747783169716278 : ℕ).testBit (i.val*10+j.val)=false → ¬ C.Adj (f i) (f j)

theorem main : H1 → H2 → OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1.H3 := by
  intro nine ten t
  fin_cases t
  · change ∀ C : SimpleGraph (Fin 17), C.CliqueFree 3 → Found (n:=9) 2251801971660822 C
    intro C ht
    by_cases bounded : ∀ v, C.degree v ≤ 7
    · exact nine C ht bounded
    push Not at bounded
    obtain ⟨v,hv⟩ := bounded
    exact highDegree (n:=9) (m:=2251801971660822) 2 (by decide) C ht v (by omega)
  · change ∀ C : SimpleGraph (Fin 19), C.CliqueFree 3 → Found (n:=10) 618970019714747783169716278 C
    intro C ht
    by_cases bounded : ∀ v, C.degree v ≤ 8
    · exact ten C ht bounded
    push Not at bounded
    obtain ⟨v,hv⟩ := bounded
    exact highDegree (n:=10) (m:=618970019714747783169716278) 0 (by decide) C ht v (by omega)

end OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1_H3_R1
