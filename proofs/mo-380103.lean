import OMAStatements.S_mo_380103

namespace OMA.S_mo_380103
open Matrix Finset Unitary
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private lemma trace_rank (M : Matrix ι ι ℝ) (h : M.IsHermitian) :
    M.trace^2 ≤ (M.rank : ℝ)*(M*M).trace := by
  classical
  let e := h.eigenvalues
  let S := univ.filter (fun i => e i ≠ 0)
  have ht : M.trace = ∑ i ∈ S,e i := by
    rw [h.trace_eq_sum_eigenvalues]
    simp [S,sum_filter,e]
    apply sum_congr rfl
    intro i _
    split <;> simp_all
  have hr : M.rank=S.card := by
    rw [h.rank_eq_card_non_zero_eigs]
    simp [S,e,Fintype.card_subtype]
  have hsq : (M*M).trace=∑ i ∈ S,(e i)^2 := by
    let D := diagonal (RCLike.ofReal ∘ e : ι → ℝ)
    have hM : M=conjStarAlgAut ℝ _ h.eigenvectorUnitary D := h.spectral_theorem
    have hh : M*M=conjStarAlgAut ℝ _ h.eigenvectorUnitary (D*D) := by rw [map_mul,←hM]
    rw [hh,conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,one_mul]
    simp [D,diagonal_mul_diagonal,trace_diagonal,S,sum_filter,e,pow_two]
    apply sum_congr rfl
    intro i _
    by_cases hi : h.eigenvalues i=0 <;> simp [hi]
  rw [ht,hr,hsq]
  simpa using sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) e
end OMA.S_mo_380103

namespace OMA.S_mo_380103
open Matrix Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
lemma real_bound (G : SimpleGraph ι) [DecidableRel G.Adj] (K : ι → ℕ) (k : ℕ)
    (hk : 0<k) (hl : ∀ i,k≤K i) (hd : degrees G K) :
    Fintype.card ι*k ≤ (mat ℝ G K).rank*(k+2) := by
  classical
  let m := mat ℝ G K
  let s (i : ι) : ℝ := (Real.sqrt (K i : ℝ))⁻¹
  let T := diagonal s*m*diagonal s
  have ki (i : ι) : 0<(K i : ℝ) := by exact_mod_cast hk.trans_le (hl i)
  have k0 : 0<(k:ℝ) := by exact_mod_cast hk
  have hs (i : ι) : (s i)^2=(K i : ℝ)⁻¹ := by
    simp only [s,inv_pow,Real.sq_sqrt (ki i).le]
  have diagval (i : ι) : T i i=1 := by
    simp [T,m,mat,mul_diagonal,diagonal_mul,SimpleGraph.adjMatrix_apply]
    have ht := hs i
    field_simp [ne_of_gt (ki i)] at ht
    nlinarith
  have off {i j : ι} (h : i≠j) : T i j=if G.Adj i j then s i*s j else 0 := by
    by_cases ha : G.Adj i j <;> simp [T,m,mat,mul_diagonal,diagonal_mul,diagonal_apply_ne _ h,
      SimpleGraph.adjMatrix_apply,ha]
  have hsym (i j : ι) : T j i=T i j := by
    by_cases hij : i=j
    · subst j; rfl
    · rw [off hij,off (Ne.symm hij)]
      simp [G.adj_comm j i,mul_comm]
  have hT : T.IsHermitian := by ext i j; simpa [Matrix.conjTranspose_apply] using hsym i j
  have htr : T.trace=(Fintype.card ι : ℝ) := by simp [trace,Matrix.diag,diagval]
  have hrow (i : ι) : (∑ j,(T i j)^2) ≤ 1+2/(k:ℝ) := by
    calc
      (∑ j,(T i j)^2) ≤ ∑ j, ((if i=j then 1 else 0 : ℝ) +
          (if G.Adj i j then (K i : ℝ)⁻¹*(k:ℝ)⁻¹ else 0)) := by
        apply sum_le_sum
        intro j _
        by_cases hij : i=j
        · subst j; simp [diagval]
        · rw [off hij]
          by_cases hadj : G.Adj i j
          · simp [hij,hadj,mul_pow,hs]
            exact mul_le_mul_of_nonneg_left (by exact inv_anti₀ k0 (by exact_mod_cast hl j)) (inv_nonneg.mpr (ki i).le)
          · simp [hij,hadj]
      _ = 1+2/(k:ℝ) := by
        have h0 : (∑ j : ι, (if i=j then 1 else 0 : ℝ))=1 := by simp
        have h1 : (∑ j : ι, (if G.Adj i j then (K i:ℝ)⁻¹*(k:ℝ)⁻¹ else 0)) =
            ((univ.filter (G.Adj i)).card:ℝ)*((K i:ℝ)⁻¹*(k:ℝ)⁻¹) := by
          rw [←sum_filter]; simp
        rw [sum_add_distrib,h0,h1,hd i]
        push_cast
        field_simp [ne_of_gt (ki i),ne_of_gt k0]
  have hsq : (T*T).trace ≤ (Fintype.card ι : ℝ)*(1+2/(k:ℝ)) := by
    calc (T*T).trace = ∑ i, ∑ j,(T i j)^2 := by
           simp only [trace,Matrix.diag,mul_apply,pow_two]
           exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => congrArg (T i j * ·) (hsym i j)
         _ ≤ ∑ _i:ι,(1+2/(k:ℝ)) := sum_le_sum fun i _ => hrow i
         _ = _ := by simp; ring
  have hr : T.rank ≤ m.rank :=
    (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have h := trace_rank T hT
  rw [htr] at h
  have h1 := h.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg T.rank))
  have h2 : (Fintype.card ι : ℝ)^2 ≤ (m.rank:ℝ)*((Fintype.card ι : ℝ)*(1+2/(k:ℝ))) :=
    h1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (by positivity))
  by_cases he : Fintype.card ι=0
  · simp [he]
  · have hn : 0<(Fintype.card ι:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero he
    have h3 : (Fintype.card ι:ℝ) ≤ (m.rank:ℝ)*(1+2/(k:ℝ)) := by
      apply le_of_mul_le_mul_left (a:=(Fintype.card ι:ℝ)) _ hn
      nlinarith only [h2]
    field_simp [ne_of_gt k0] at h3
    exact_mod_cast h3
end OMA.S_mo_380103

namespace OMA.S_mo_380103
open Matrix Finset

lemma card_le_rank_mul_support {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    [DecidableEq K] (M : Matrix ι κ K) (d : ℕ)
    (hc : ∀ j, ∃ i, M i j ≠ 0) (hr : ∀ i, (univ.filter (fun j => M i j ≠ 0)).card ≤ d) :
    Fintype.card κ ≤ M.rank * d := by
  classical
  obtain ⟨I,hI,hmax⟩ := exists_maximal_linearIndepOn K M.row
  let s := I.toFinset
  let B := M.submatrix (fun i : s => (i : ι)) id
  have hB : LinearIndependent K B.row := by
    change LinearIndepOn K M.row (s : Set ι)
    simpa only [s,Set.coe_toFinset] using hI
  have hs : s.card ≤ M.rank := by
    have h := M.rank_submatrix_le (fun i : s => (i : ι)) id
    change B.rank ≤ M.rank at h
    simpa [hB.rank_matrix] using h
  let S (i : ι) := univ.filter fun j => M i j ≠ 0
  have hcover : s.biUnion S = univ := by
    apply eq_univ_of_forall
    intro j
    by_contra hj
    have hz (i) (hi : i∈I) : M i j = 0 := by
      by_contra h
      exact hj (mem_biUnion.mpr ⟨i,by simpa [s] using hi,by simpa [S] using h⟩)
    have hspan : Submodule.span K (M.row '' I) ≤ LinearMap.ker (LinearMap.proj j : (κ→K) →ₗ[K] K) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,hi,rfl⟩
      exact hz i hi
    obtain ⟨i,hi⟩ := hc j
    by_cases h : i∈I
    · exact hi (hz i h)
    · obtain ⟨c,hc',hmem⟩ := hmax i h
      have hmul : c*M i j=0 := hspan hmem
      exact hi ((mul_eq_zero.mp hmul).resolve_left hc')
  calc
    Fintype.card κ = (s.biUnion S).card := by rw [hcover,card_univ]
    _ ≤ s.card*d := card_biUnion_le_card_mul s S d (fun i _ => hr i)
    _ ≤ M.rank*d := Nat.mul_le_mul_right d hs
end OMA.S_mo_380103

namespace OMA.S_mo_380103
open Matrix Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
lemma mod_bound (G : SimpleGraph ι) [DecidableRel G.Adj] (K : ι → ℕ)
    (u p : ℕ) [Fact p.Prime] (hp : ∀ i,0<K i) (hu : ∀ i,K i≤u) (hd : degrees G K) :
    Fintype.card ι ≤ (mat (ZMod p) G K).rank*(2*u+1) := by
  classical
  apply card_le_rank_mul_support
  · intro j
    have hp' : 0<(univ.filter (G.Adj j)).card := by rw [hd j]; have := hp j; omega
    obtain ⟨i,hi⟩ := card_pos.mp hp'
    have ha : G.Adj i j := (mem_filter.mp hi).2.symm
    exact ⟨i,by simp [mat,SimpleGraph.adjMatrix_apply,diagonal_apply_ne _ ha.ne,ha]⟩
  · intro i
    let S := univ.filter (G.Adj i)
    have h : univ.filter (fun j => mat (ZMod p) G K i j ≠ 0) ⊆ insert i S := by
      intro j hj
      by_cases he : i=j
      · subst j; simp
      · by_contra hn
        have hna : ¬G.Adj i j := fun hij => hn (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,hij⟩))
        exact (mem_filter.mp hj).2 (by simp [mat,diagonal_apply_ne _ he,SimpleGraph.adjMatrix_apply,hna])
    have h₁ := card_le_card h
    have h₂ := card_insert_le i S
    have h₃ : S.card=2*K i := hd i
    have h₄ := hu i
    omega
end OMA.S_mo_380103

namespace OMA.S_mo_380103
open Matrix Finset

private lemma part_count {h s k : ℕ} (i : Fin h × Fin s × Fin k) :
    (univ.filter ((partGraph h s k).Adj i)).card=(s-1)*k := by
  have he : univ.filter ((partGraph h s k).Adj i) = {i.1} ×ˢ ((univ.erase i.2.1) ×ˢ univ) := by
    ext j
    obtain ⟨a,b,c⟩ := j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_erase, and_true]
    change (i.1=a ∧ i.2.1≠b) ↔ (a=i.1 ∧ b≠i.2.1)
    tauto
  rw [he]
  simp [card_erase_of_mem]

lemma bip_blocks (h p : ℕ) [Fact p.Prime] :
    degrees (partGraph h 2 (2*p)) (fun _=>p) ∧
      (mat (ZMod p) (partGraph h 2 (2*p)) (fun _=>p)).rank ≤ 2*h := by
  constructor
  · intro i; change _ = 2*p; rw [part_count]; simp
  let V := Fin h × Fin 2 × Fin (2*p)
  let D := Fin h × Fin 2
  let L : Matrix V D (ZMod p) := fun i j => if i.1=j.1 ∧ i.2.1≠j.2 then 1 else 0
  let R : Matrix D V (ZMod p) := fun u j => if u=(j.1,j.2.1) then 1 else 0
  have he : mat (ZMod p) (partGraph h 2 (2*p)) (fun _=>p) = L*R := by
    ext i j
    change (if i=j then (p:ZMod p) else 0) + (if i.1=j.1 ∧ i.2.1≠j.2.1 then 1 else 0)
      = ∑ u:D, L i u * (if u=(j.1,j.2.1) then 1 else 0)
    simp [mul_ite,L]
  rw [he]
  simpa [D,Nat.mul_comm] using (Matrix.rank_mul_le_left L R).trans L.rank_le_card_width

private lemma block_contrib {h s k : ℕ} (x : Fin h) (i : Fin s) (z : Fin k) (d : Fin h)
    (f : Fin s→ℝ) :
    (∑ v : Fin h × Fin s × Fin k, (partGraph h s k).adjMatrix ℝ (x,i,z) v*
      (if v.1=d then f v.2.1 else 0)) =
    if x=d then (k:ℝ)*∑ j : Fin s, (if i=j then 0 else f j) else 0 := by
  have hrow (a : Fin h) (j : Fin s) (r : Fin k) :
      (partGraph h s k).adjMatrix ℝ (x,i,z) (a,j,r)*(if a=d then f j else 0) =
      if a=x then (if x=d then (if i=j then 0 else f j) else 0) else 0 := by
    change ((if x=a ∧ i≠j then 1 else 0) : ℝ)*_ = _
    by_cases ha : a=x
    · subst a; split_ifs <;> simp_all
    · simp [ha, Ne.symm ha]
  simp only [Fintype.sum_prod_type,hrow,sum_const,nsmul_eq_mul]
  by_cases hx : x=d
  · simp [hx,Finset.mul_sum, Finset.sum_ite_irrel, mul_ite]
  · simp [hx]

lemma trip_blocks (h k : ℕ) (hk : 0<k) :
    degrees (partGraph h 3 k) (fun _=>k) ∧
      (mat ℝ (partGraph h 3 k) (fun _=>k)).rank+2*h ≤ 3*h*k := by
  constructor
  · intro i; rw [part_count]
  let V := Fin h × Fin 3 × Fin k
  let D := Fin h × Fin 2
  let B : Fin 3→Fin 2→ℝ := ![![1,0],![0,1],![-1,-1]]
  let N : Matrix V D ℝ := fun i j => if i.1=j.1 then B i.2.1 j.2 else 0
  let J (j : D) : V := (j.1, j.2.castLE (by decide), ⟨0,hk⟩)
  let C : Matrix D V ℝ := fun i v => if v=J i then 1 else 0
  let M := mat ℝ (partGraph h 3 k) (fun _=>k)
  have hCN : C*N=1 := by
    ext i j
    obtain ⟨a,u⟩ := i
    obtain ⟨b,v⟩ := j
    change (∑ w : V, (if w=J (a,u) then (1:ℝ) else 0)*N w (b,v)) =
      (1:Matrix D D ℝ) (a,u) (b,v)
    simp only [ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,if_true]
    fin_cases u <;> fin_cases v <;> by_cases he : a=b <;> simp [J,N,B, Matrix.one_apply,he]
  have hN : 2*h ≤ N.rank := by
    have hh := (Matrix.rank_mul_le_right C N)
    rw [hCN,Matrix.rank_one] at hh
    simpa [D,Nat.mul_comm] using hh
  have hMN : M*N=0 := by
    change (diagonal _ + _)*N=0
    rw [Matrix.add_mul]
    ext v j
    obtain ⟨x,i,z⟩ := v
    obtain ⟨d,l⟩ := j
    rw [Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_apply]
    change (k:ℝ)*(if x=d then B i l else 0) + (∑ v : Fin h × Fin 3 × Fin k,
      (partGraph h 3 k).adjMatrix ℝ (x,i,z) v*(if v.1=d then B v.2.1 l else 0)) = 0
    rw [block_contrib x i z d (fun s => B s l)]
    by_cases hx : x=d
    · fin_cases i <;> fin_cases l <;> simp [hx,B,Fin.sum_univ_three]
    · simp [hx]
  have hh := Matrix.rank_add_rank_le_card_of_mul_eq_zero hMN
  have hw : M.rank+N.rank ≤ 3*h*k := by simpa [V,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
  exact (Nat.add_le_add_left hN M.rank).trans hw
end OMA.S_mo_380103

namespace OMA.S_mo_380103
open Matrix Finset
lemma bip_lower (h p : ℕ) [Fact p.Prime]
    (hd : degrees (partGraph h 2 (2*p)) (fun _ => p)) :
    2*h ≤ (mat (ZMod p) (partGraph h 2 (2*p)) (fun _ => p)).rank := by
  classical
  let G := partGraph h 2 (2*p)
  let M := mat (ZMod p) G (fun _ => p)
  have hM (i j) : M i j=if G.Adj i j then 1 else 0 := by
    simp [M,mat,SimpleGraph.adjMatrix_apply]
  have hN := card_le_rank_mul_support M (2*p) (by
    intro j
    have hpos : 0 < (univ.filter (G.Adj j)).card := by rw [hd j]; have := Fact.out (p:=p.Prime); exact Nat.mul_pos (by decide) this.pos
    obtain ⟨i,hi⟩ := card_pos.mp hpos
    have ha : G.Adj i j := (mem_filter.mp hi).2.symm
    exact ⟨i,by simp [hM,ha]⟩) (by
    intro i
    have hs : univ.filter (fun j => M i j≠0)=univ.filter (G.Adj i) := by
      ext j; by_cases ha : G.Adj i j <;> simp [hM,ha]
    rw [hs,hd i])
  simp only [Fintype.card_prod,Fintype.card_fin] at hN
  have hp0 : 0<p := (Fact.out (p:=p.Prime)).pos
  change 2*h ≤ M.rank
  apply Nat.le_of_mul_le_mul_right (c:=2*p) _ (by omega)
  calc (2*h)*(2*p) = h*(2*(2*p)) := by ring
       _ ≤ _ := hN
end OMA.S_mo_380103

open OMA.S_mo_380103
theorem OMA.solution : type_of% @OMA.S_mo_380103.main := by
  refine ⟨fun _ _ _ => real_bound,fun _ _ _ => mod_bound,trip_blocks,?_⟩
  intro h p hp
  obtain ⟨hd,hr⟩ := bip_blocks h p
  exact ⟨hd,le_antisymm hr (bip_lower h p hd)⟩
