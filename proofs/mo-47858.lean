import OMAStatements.S_mo_47858

namespace OMA.S_mo_47858
open Matrix Polynomial Finset

private lemma integral_characteristic {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ P : ℤ[X], P.Monic ∧ P.map (Int.castRingHom ℝ) = characteristic G := by
  classical
  refine ⟨(G.lapMatrix ℤ).charpoly, Matrix.charpoly_monic _, ?_⟩
  rw [← Matrix.charpoly_map,characteristic]
  congr 1
  ext i j
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
    diagonal_apply]

private lemma negative_next {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ k : ℤ, - (characteristic G).nextCoeff = 2*(k:ℝ) := by
  classical
  refine ⟨G.edgeFinset.card, ?_⟩
  change -(G.lapMatrix ℝ).charpoly.nextCoeff = _
  rw [← Matrix.trace_eq_neg_charpoly_nextCoeff]
  change (∑ i, ((G.lapMatrix ℝ) i i)) = _
  simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix, diagonal_apply_eq,
    SimpleGraph.adjMatrix_apply]
  simp_rw [if_neg (G.loopless.irrefl _),sub_zero]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

private lemma integral_real_rational (P : ℤ[X]) (hm : P.Monic) (r : ℚ)
    (hr : (P.map (Int.castRingHom ℝ)).eval (r:ℝ)=0) : ∃ u : ℤ, (r:ℝ) = u := by
  have h : IsIntegral ℤ r := by
    refine ⟨P,hm,?_⟩
    apply (Rat.castHom ℝ).injective
    rw [Polynomial.hom_eval₂,map_zero]
    rw [show (Rat.castHom ℝ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℝ from Subsingleton.elim _ _]
    exact (Polynomial.eval_map ..).symm.trans hr
  obtain ⟨u,hu⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp h
  exact ⟨u, by rw [←hu]; simp⟩

private lemma integer_replacement {n : ℕ} (G H : SimpleGraph (Fin n)) (a b : ℝ)
    (R : ℝ[X]) (hR : R.Monic) (hg : characteristic G=(X-C a)*R)
    (hh : characteristic H=(X-C b)*R) :
    (∃ k : ℤ, b-a=2*(k:ℝ)) ∧ (a≠b → ∃ u v : ℤ, a=(u:ℝ) ∧ b=(v:ℝ)) := by
  obtain ⟨k,hk⟩ := negative_next G
  obtain ⟨l,hl⟩ := negative_next H
  rw [hg,(monic_X_sub_C a).nextCoeff_mul hR] at hk
  rw [hh,(monic_X_sub_C b).nextCoeff_mul hR] at hl
  simp only [nextCoeff_X_sub_C] at hk hl
  let d : ℤ := 2*(l-k)
  have hd : b-a=(d:ℝ) := by dsimp [d]; push_cast; linarith
  constructor
  · exact ⟨l-k, by simpa [d] using hd⟩
  intro hab
  have hd0 : d ≠ 0 := by intro he; rw [he,Int.cast_zero] at hd; exact hab (sub_eq_zero.mp hd).symm
  obtain ⟨P,hmP,hP⟩ := integral_characteristic G
  obtain ⟨Q,_,hQ⟩ := integral_characteristic H
  let T : ℚ[X] := C ((d:ℚ)⁻¹) * (P-Q).map (Int.castRingHom ℚ)
  have hT : T.map (Rat.castHom ℝ) = R := by
    have hdiff : P.map (Int.castRingHom ℝ) - Q.map (Int.castRingHom ℝ) = C (d:ℝ)*R := by
      rw [hP,hQ,hg,hh,← hd,C_sub]
      ring
    simp only [T,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_sub,Polynomial.map_map,
      map_inv₀,map_intCast]
    rw [show (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ from Subsingleton.elim _ _,
      hdiff,←mul_assoc,←C_mul,inv_mul_cancel₀ (by exact_mod_cast hd0),C_1,one_mul]
  let r : ℚ := T.nextCoeff + 2*k
  have hr : (r:ℝ) = a := by
    have ht := congrArg Polynomial.nextCoeff hT
    rw [Polynomial.nextCoeff_map (Rat.castHom ℝ).injective] at ht
    change (T.nextCoeff:ℝ) = R.nextCoeff at ht
    dsimp [r]
    push_cast
    linarith
  obtain ⟨u,hu⟩ := integral_real_rational P hmP r (by rw [hP,hg,hr]; simp)
  refine ⟨u,u+d,hr ▸ hu, ?_⟩
  push_cast
  linarith

end OMA.S_mo_47858
namespace OMA.S_mo_47858
open Matrix Polynomial SimpleGraph Finset
private lemma path_triangle :
    ∃ G H : SimpleGraph (Fin 3), G.Connected ∧ H.Connected ∧
      characteristic G = X*(X-1)*(X-3) ∧ characteristic H = X*(X-3)^2 := by
  classical
  refine ⟨pathGraph 3, completeGraph _,pathGraph_connected 2,connected_top,?_⟩
  have dp (i : Fin 3) : (pathGraph 3).degree i = if i=1 then 2 else 1 := by
    calc
      _ = ∑ j : Fin 3, (if (pathGraph 3).Adj i j then (1:ℕ) else 0) :=
        (pathGraph 3).degree_eq_sum_if_adj i
      _ = _ := by rw [Fin.sum_univ_three]; fin_cases i <;> norm_num [pathGraph_adj,SimpleGraph.top_adj,Fin.ext_iff,Fin.isValue]
  have dk (i : Fin 3) (ft : Fintype ((completeGraph (Fin 3)).neighborSet i)) :
      @SimpleGraph.degree _ (completeGraph (Fin 3)) i ft = 2 := by
    have hn := SimpleGraph.complete_graph_degree (V:=Fin 3) i
    convert hn using 1
    · congr 1
      exact Subsingleton.elim _ _
    · decide
  constructor <;>
    norm_num [characteristic,Matrix.charpoly,Matrix.det_fin_three,Matrix.charmatrix_apply,
      SimpleGraph.lapMatrix,SimpleGraph.degMatrix,diagonal_apply,SimpleGraph.adjMatrix_apply,
      dp,dk,pathGraph_adj,SimpleGraph.top_adj,Fin.ext_iff,Fin.isValue,map_ofNat] <;> ring
end OMA.S_mo_47858
namespace OMA.S_mo_47858
open Finset Matrix Polynomial

private def contrast (j i : ℕ) : ℝ :=
  if i<j then 1 else if i=j then -(j:ℝ) else 0

private lemma contrast_prefix (m j : ℕ) :
    ∑ i ∈ range m, contrast j i = if m≤j then (m:ℝ) else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ,ih]
    unfold contrast
    split_ifs <;> push_cast <;> first | solve | omega | (subst_vars; ring)

private noncomputable def cliqueProjection {N : ℕ} (p : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i.val<p then (if i=j then 1 else 0) -
    (if j.val<p then (p:ℝ)⁻¹ else 0) else 0

private lemma trunc_sum {p N : ℕ} (hp : p≤N) (f : ℕ→ℝ) :
    (∑ i : Fin N, if i.val<p then f i.val else 0) = ∑ i ∈ range p, f i := by
  rw [Fin.sum_univ_eq_sum_range fun i => if i<p then f i else 0]
  calc
    _ = ∑ i ∈ range p, (if i<p then f i else 0) := (sum_subset (range_mono hp)
      (by intro i _ hi; simp_all)).symm
    _ = _ := sum_congr rfl fun i hi => if_pos (mem_range.mp hi)

private lemma prefix_action {N : ℕ} (p : ℕ) (hp : p≤N) (f : ℕ→ℝ) (i : Fin N) :
    (cliqueProjection p *ᵥ (fun s => f s.val)) i =
      if i.val<p then f i.val - (p:ℝ)⁻¹*(∑ s ∈ range p,f s) else 0 := by
  by_cases hi : i.val<p
  · simp only [mulVec,dotProduct,cliqueProjection,hi,if_true,sub_mul,ite_mul,one_mul,zero_mul,
      sum_sub_distrib,sum_ite_eq,mem_univ]
    rw [←trunc_sum hp f,Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro j _
    split_ifs <;> simp_all
  · simp [mulVec,dotProduct,cliqueProjection,hi]

private lemma prefix_contrast {N : ℕ} (j p : ℕ) (hp : p≤N) (hp0 : 0<p) (i : Fin N) :
    (cliqueProjection p *ᵥ (fun s => contrast j s.val)) i = if j<p then contrast j i.val else 0 := by
  rw [prefix_action p hp,contrast_prefix]
  by_cases hj : j<p
  · simp only [hj,if_true,not_le.mpr hj,if_false,mul_zero,sub_zero]
    by_cases hi : i.val<p
    · simp [hi]
    · simp [hi,contrast,show ¬i.val<j by omega,show i.val≠j by omega]
  · have hj' := Nat.le_of_not_gt hj
    simp only [hj,if_false,hj',if_true]
    by_cases hi : i.val<p
    · simp [hi,contrast,show i.val<j by omega,ne_of_gt (Nat.cast_pos.mpr hp0 : (0:ℝ)<p)]
    · simp [hi]

private lemma prefix_const {N : ℕ} (p : ℕ) (hp : p≤N) (hp0 : 0<p) :
    cliqueProjection p *ᵥ (fun _ : Fin N => (1:ℝ)) = 0 := by
  ext1 i
  rw [prefix_action p hp (fun _ => 1)]
  simp [ne_of_gt (Nat.cast_pos.mpr hp0 : (0:ℝ)<p)]

end OMA.S_mo_47858
namespace OMA.S_mo_47858
open Matrix Finset Polynomial

private def modes (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j.val=0 then 1 else contrast j.val i.val

private lemma modes_orthog_lt {N : ℕ} (i j : Fin N) (hij : i<j) :
    ((modes N)ᵀ * modes N) i j = 0 := by
  have hj : j.val≠0 := by have h := hij; change i.val<j.val at h; omega
  change ∑ l : Fin N, modes N l i * modes N l j = 0
  by_cases hi : i.val=0
  · simp only [modes,hi,hj,if_true,if_false,one_mul]
    rw [Fin.sum_univ_eq_sum_range (contrast j.val),contrast_prefix,if_neg (by omega)]
  · simp only [modes,hi,hj,if_false]
    calc
      _ = ∑ l : Fin N, contrast i.val l.val := by
        apply sum_congr rfl
        intro l _
        by_cases h : l.val ≤ i.val
        · rw [show contrast j.val l.val = 1 by
                exact if_pos (Nat.lt_of_le_of_lt h hij),mul_one]
        · rw [show contrast i.val l.val = 0 by
                simp [contrast,show ¬(l.val < i.val) by omega,show l.val≠i.val by omega],zero_mul]
      _ = 0 := by rw [Fin.sum_univ_eq_sum_range (contrast i.val),contrast_prefix,if_neg (by omega)]

private lemma modes_unit (N : ℕ) : IsUnit (modes N) := by
  let M := modes N
  let D := Mᵀ*M
  have hgram : D = diagonal (fun i => D i i) := by
    ext i j
    rcases lt_trichotomy i j with h|rfl|h
    · rw [diagonal_apply_ne _ h.ne]
      exact modes_orthog_lt i j h
    · simp
    · rw [diagonal_apply_ne _ h.ne']
      have hs : Dᵀ = D := by simp [D,transpose_mul]
      exact (congrFun (congrFun hs j) i).trans (modes_orthog_lt j i h)
  have hd (i : Fin N) : 0<D i i := by
    change 0 < ∑ l : Fin N, modes N l i * modes N l i
    apply sum_pos'
    · intro l _
      exact mul_self_nonneg _
    · let l : Fin N := ⟨0,Nat.zero_lt_of_lt i.isLt⟩
      refine ⟨l,mem_univ _,?_⟩
      have h : modes N l i=1 := by
        by_cases hi : i.val=0
        · simp [modes,hi]
        · simp [modes,hi,contrast,l,Nat.pos_of_ne_zero hi]
      simp [h]
  have hdet : D.det≠0 := by
    calc
      D.det = (diagonal (fun i => D i i)).det := congrArg Matrix.det hgram
      _ = ∏ i, D i i := det_diagonal
      _ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hd i).ne'
  change (Mᵀ * M).det ≠ 0 at hdet
  rw [Matrix.det_mul,Matrix.det_transpose] at hdet
  exact (M.isUnit_iff_isUnit_det).mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hdet).1)

end OMA.S_mo_47858
namespace OMA.S_mo_47858
open Finset Matrix Polynomial

private lemma tail_sum (f : ℕ→ℝ) (a b : ℕ) :
    ∑ k ∈ range b, (if a≤k then f k-f (k+1) else 0) =
      if a≤b then f a-f b else 0 := by
  induction b with
  | zero => by_cases h : a=0 <;> simp [h]
  | succ b ih =>
    rw [sum_range_succ,ih]
    by_cases ha : a≤b
    · simp [ha,ha.trans (Nat.le_succ b)]
    · by_cases h : a=b+1
      · simp [h]
      · simp [ha,show ¬a≤b+1 by omega]

private lemma weighted (n : ℕ) (v : Fin n → ℝ) (hv : Antitone v) (hpos : ∀ i, 0<v i) :
    ∃ L : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, L.IsSymm ∧
      (∀ i j, i≠j → L i j<0) ∧ (∀ i, ∑ j,L i j=0) ∧
      L.charpoly = X * ∏ i, (X-C (v i)) := by
  let f (k : ℕ) := if h : k<n then v ⟨k,h⟩ else 0
  let c (k : ℕ) := f k-f (k+1)
  have hc (k : ℕ) : 0≤c k := by
    dsimp [c,f]
    split_ifs with h h' h'
    · exact sub_nonneg.mpr (hv (show (⟨k,h⟩ : Fin n) ≤ ⟨k+1,h'⟩ from Nat.le_succ k))
    · simpa using (hpos ⟨k,h⟩).le
    · omega
    · simp
  let L : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    ∑ k ∈ range n, c k • cliqueProjection (k+2)
  refine ⟨L,?_,?_,?_,?_⟩
  · ext i j
    simp only [L,transpose_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    exact sum_congr rfl fun k _ => by
      congr 1
      simp only [cliqueProjection]
      split_ifs <;> grind
  · intro i j hij
    have hn : 0<n := by
      by_contra! hz
      obtain rfl := Nat.eq_zero_of_le_zero hz
      exact hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))
    simp only [L,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    apply Finset.sum_neg'
    · intro k _
      apply mul_nonpos_of_nonneg_of_nonpos (hc k)
      unfold cliqueProjection
      simp only [hij,if_false,zero_sub]
      split_ifs <;> simp
      positivity
    · refine ⟨n-1,mem_range.mpr (by omega),?_⟩
      have h : n-1+2 = n+1 := by omega
      have hc' : 0<c (n-1) := by simpa [c,f,show n-1<n by omega,show n-1+1=n by omega] using hpos ⟨n-1,by omega⟩
      rw [h]
      apply mul_neg_of_pos_of_neg hc'
      simp [cliqueProjection,i.isLt,j.isLt,hij]
      positivity
  · intro i
    have ho : L *ᵥ (fun _ => (1:ℝ)) = 0 := by
      rw [show L = _ from rfl, Matrix.sum_mulVec]
      apply sum_eq_zero
      intro k hk
      rw [Matrix.smul_mulVec,prefix_const _ (by have := mem_range.mp hk; omega) (by omega),smul_zero]
    simpa [Matrix.mulVec,dotProduct] using congrFun ho i
  · let M := modes (n+1)
    let w (j : Fin (n+1)) := if j.val=0 then 0 else f (j.val-1)
    have hLM : L*M = M*diagonal w := by
      ext i j
      rw [Matrix.mul_diagonal]
      change (L *ᵥ (fun s => modes (n+1) s j)) i = modes (n+1) i j * w j
      by_cases hj : j.val=0
      · simp only [modes,hj,w,if_true,mul_zero,L,Matrix.sum_mulVec,Finset.sum_apply]
        apply sum_eq_zero
        intro k hk
        rw [Matrix.smul_mulVec,prefix_const _ (by have := mem_range.mp hk; omega) (by omega),smul_zero,Pi.zero_apply]
      · simp only [modes,hj,w,if_false,L,Matrix.sum_mulVec,Finset.sum_apply,Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul]
        calc
          _ = ∑ k ∈ range n, (if j.val-1 ≤ k then f k-f (k+1) else 0) * contrast j.val i.val := by
            apply sum_congr rfl
            intro k hk
            rw [prefix_contrast _ _ (by have := mem_range.mp hk; omega) (by omega)]
            dsimp [c]
            split_ifs <;> first | omega | simp
          _ = _ := by rw [←Finset.sum_mul,tail_sum,if_pos (by have := j.isLt; omega)]; simp [f,mul_comm]
    obtain ⟨U,hU⟩ := modes_unit (n+1)
    have hchar : L.charpoly = (diagonal w).charpoly := by
      have hLM' : L*(U:Matrix (Fin (n+1)) (Fin (n+1)) ℝ) = (U:Matrix (Fin (n+1)) (Fin (n+1)) ℝ)*diagonal w := by simpa only [hU] using hLM
      have hL : L= (U:Matrix (Fin (n+1)) (Fin (n+1)) ℝ) * diagonal w * (U:Matrix (Fin (n+1)) (Fin (n+1)) ℝ)⁻¹ := by
        rw [←hLM',Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp U.isUnit),mul_one]
      rw [hL,Matrix.charpoly_units_conj]
    rw [hchar,Matrix.charpoly_diagonal,Fin.prod_univ_succ]
    simp [w,f]

end OMA.S_mo_47858

open OMA.S_mo_47858 in
theorem OMA.solution : type_of% @OMA.S_mo_47858.main :=
  ⟨@integer_replacement, path_triangle, weighted⟩
