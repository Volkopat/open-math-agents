import FormalConjectures.ErdosProblems.«210»

/-!
# Böröczky configurations in an affine chart

The two families are points `(t²,t)` on a parabola and points `(-1,w)` on a
line. Parameterize the two families by equally spaced angles. The secant from
indices `i` and `j` passes through line point `i+j` modulo the family size.
Thus every ordinary line is among the tangent candidates indexed by `i`.
-/

namespace OMA.Ordinary
open Real Finset EuclideanGeometry Filter
open scoped Topology
noncomputable section

private def angle {m : ℕ} (c : ℝ) (i : Fin m) : ℝ := ((i.val : ℝ)+c) / m * π - π / 2

private lemma angle_mem {m : ℕ} {c : ℝ} (hc : 0 < c) (hc' : c < 1) (i : Fin m) :
    angle c i ∈ Set.Ioo (-(π/2)) (π/2) := by
  have hm : (0:ℝ) < m := by exact_mod_cast (show 0 < m from Nat.zero_lt_of_lt i.isLt)
  have hil : (i.val:ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  unfold angle
  constructor
  · linarith [mul_pos (div_pos (by positivity : 0 < (i.val:ℝ)+c) hm) pi_pos]
  · have hh : ((i.val:ℝ)+c)/m < 1 := (div_lt_one hm).mpr (by linarith)
    linarith [mul_lt_mul_of_pos_right hh pi_pos]

private def t {m : ℕ} (i : Fin m) := tan (angle (1/4) i)
private def w {m : ℕ} (i : Fin m) := tan (angle (1/2) i)
private def P {m : ℕ} (i : Fin m) : ℝ² := !₂[(t i)^2,t i]
private def Q {m : ℕ} (i : Fin m) : ℝ² := !₂[(-1:ℝ),w i]

private lemma param_inj {m : ℕ} {c : ℝ} (hc : 0<c) (hc' : c<1) :
    Function.Injective (fun i : Fin m => tan (angle c i)) := by
  intro i j he
  have hm : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  have e := strictMonoOn_tan.injOn (angle_mem hc hc' i) (angle_mem hc hc' j) he
  unfold angle at e
  apply Fin.ext
  exact_mod_cast add_right_cancel ((div_left_inj' hm).mp ((mul_left_inj' pi_ne_zero).mp (sub_left_inj.mp e)))

private lemma pinj {m : ℕ} : Function.Injective (P (m := m)) := by
  intro i j e
  apply param_inj (c := 1/4) (by norm_num) (by norm_num)
  simpa [P,t] using congrArg (fun z : ℝ² => z 1) e

private lemma qinj {m : ℕ} : Function.Injective (Q (m := m)) := by
  intro i j e
  apply param_inj (c := 1/2) (by norm_num) (by norm_num)
  simpa [Q,w] using congrArg (fun z : ℝ² => z 1) e

private lemma pq_ne {m : ℕ} (i j : Fin m) : P i ≠ Q j := by
  intro e
  have he : (t i)^2 = -1 := by simpa [P,Q] using congrArg (fun z : ℝ² => z 0) e
  nlinarith [sq_nonneg (t i)]

private lemma secant_eq {m : ℕ} (i j : Fin m) :
    (t i + t j) * w (i+j) = t i*t j - 1 := by
  let a := angle (1/4) i
  let b := angle (1/4) j
  let s := angle (1/2) (i+j) + π/2
  have ha : cos a ≠ 0 := (cos_pos_of_mem_Ioo (angle_mem (by norm_num) (by norm_num) i)).ne'
  have hb : cos b ≠ 0 := (cos_pos_of_mem_Ioo (angle_mem (by norm_num) (by norm_num) j)).ne'
  have hs : sin s ≠ 0 := by
    simpa [s, sin_add_pi_div_two] using
      (cos_pos_of_mem_Ioo (angle_mem (c := 1/2) (by norm_num) (by norm_num) (i+j))).ne'
  have hm : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  have eq : a+b=s ∨ a+b=s-π := by
    dsimp [a,b,s,angle]
    rw [Fin.val_add_eq_ite]
    split_ifs with h
    · left
      rw [Nat.cast_sub (by omega),Nat.cast_add]
      field_simp
      ring
    · right
      push_cast
      ring
  have htr : sin (a+b)*cos s = cos (a+b)*sin s := by
    rcases eq with h|h <;> rw [h] <;> simp [sin_sub_pi,cos_sub_pi,mul_comm]
  rw [sin_add a b,cos_add a b] at htr
  have hw : w (i+j) = -cos s / sin s := by
    change tan (angle (1/2) (i+j)) = _
    rw [show angle (1/2) (i+j) = s-π/2 by dsimp [s]; ring,
      tan_eq_sin_div_cos,sin_sub_pi_div_two,cos_sub_pi_div_two]
  change (tan a + tan b) * w (i+j) = tan a*tan b-1
  rw [hw,tan_eq_sin_div_cos,tan_eq_sin_div_cos]
  field_simp
  linear_combination -htr

private def pt (a b y : ℝ) : ℝ² := !₂[a*y+b,y]

private lemma mem_graph {a b u v : ℝ} (huv : u ≠ v) (z : ℝ²) :
    z ∈ line[ℝ,pt a b u,pt a b v] ↔ z 0 = a * z 1 + b := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨c,rfl⟩
    simp [AffineMap.lineMap_apply,pt]
    ring
  · intro he
    refine ⟨(z 1-u)/(v-u),?_⟩
    have hn : v-u ≠ 0 := sub_ne_zero.mpr huv.symm
    ext i
    fin_cases i <;> simp [AffineMap.lineMap_apply,pt,he] <;> field_simp <;> ring

private lemma vertex_on_chord {m : ℕ} (i j : Fin m) :
    P i = pt (t i+t j) (-t i*t j) (t i) := by
  ext k; fin_cases k <;> simp [P,pt] <;> ring

private lemma dir_on_chord {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    Q (i+j) ∈ line[ℝ,P i,P j] := by
  have hi := vertex_on_chord i j
  have hj := vertex_on_chord j i
  rw [add_comm (t j) (t i),show -t j*t i = -t i*t j by ring] at hj
  rw [hi,hj,mem_graph (show t i ≠ t j from fun e => hij (param_inj (c:=1/4) (by norm_num) (by norm_num) e))]
  simp [Q]
  linarith [secant_eq i j]

private lemma axis {m : ℕ} {i j : Fin m} (hij : i ≠ j) (z : ℝ²) :
    z ∈ line[ℝ,Q i,Q j] ↔ z 0 = -1 := by
  have hq (a : Fin m) : Q a = pt 0 (-1) (w a) := by simp [Q,pt]
  rw [hq,hq,mem_graph (show w i ≠ w j from fun e => hij (param_inj (c:=1/2) (by norm_num) (by norm_num) e))]
  simp

private lemma construction (m : ℕ) (hm : 3 ≤ m) : Erdos210.f (m+m) ≤ m := by
  classical
  letI : NeZero m := ⟨by omega⟩
  let V := (univ : Finset (Fin m)).image P
  let W := (univ : Finset (Fin m)).image Q
  let S := V ∪ W
  let T := (univ : Finset (Fin m)).image (fun i => line[ℝ,P i,Q (i+i)])
  have cv : V.card = m := by simp [V,card_image_of_injective _ pinj]
  have cw : W.card = m := by simp [W,card_image_of_injective _ qinj]
  have dis : Disjoint V W := by
    simp only [disjoint_left,V,W,mem_image,mem_univ,true_and]
    rintro _ ⟨i,rfl⟩ ⟨j,he⟩
    exact pq_ne i j he.symm
  have cs : S.card = m+m := by rw [show S=V ∪ W from rfl,card_union_of_disjoint dis,cv,cw]
  have hp (i : Fin m) : P i ∈ S := mem_union_left _ (mem_image_of_mem _ (mem_univ _))
  have hq (i : Fin m) : Q i ∈ S := mem_union_right _ (mem_image_of_mem _ (mem_univ _))
  let i0 : Fin m := ⟨0,by omega⟩
  let i1 : Fin m := ⟨1,by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0,i1] at this
  have nc : ¬ Collinear ℝ (S : Set ℝ²) := by
    intro h
    have hm0 := h.mem_affineSpan_of_mem_of_ne (hq i0) (hq i1) (hp i0) (qinj.ne h01)
    have e := (axis h01 (P i0)).mp hm0
    simp [P] at e
    nlinarith [sq_nonneg (t i0)]
  refine (Erdos210.f_le cs nc).trans ((card_le_card (show ordinaryLines S ⊆ T from ?_)).trans ?_)
  · intro L hL
    obtain ⟨⟨a,ha,b,hb,hab,hlab⟩,hcard⟩ := mem_ordinaryLines.mp hL
    let U := S.filter (fun z => z ∈ L)
    have hlim {a b c : ℝ²} (aS : a ∈ S) (bS : b ∈ S) (cS : c ∈ S)
        (aL : a ∈ L) (bL : b ∈ L) (cL : c ∈ L) (ab : a ≠ b) : c=a ∨ c=b := by
      have hsub : {a,b} ⊆ U := by
        simp [U,insert_subset_iff,singleton_subset_iff,aS,aL,bS,bL]
      have he : {a,b} = U := eq_of_subset_of_card_le hsub (by simpa [U,hcard,ab])
      have hx : c ∈ U := mem_filter.mpr ⟨cS,cL⟩
      simpa [← he] using hx
    have mixed (i j : Fin m) (he : line[ℝ,P i,Q j] = L) : L ∈ T := by
      by_cases ht : j=i+i
      · exact mem_image.mpr ⟨i,mem_univ _,ht ▸ he⟩
      let k := j-i
      have hk : i+k=j := by dsimp [k]; abel
      have hki : i ≠ k := fun h => ht (by simpa [← h] using hk.symm)
      have hdir : Q j ∈ line[ℝ,P i,P k] := hk ▸ dir_on_chord hki
      have hsame := affineSpan_pair_eq_of_mem_of_mem_of_ne
        (left_mem_affineSpan_pair ℝ (P i) (P k)) hdir (pq_ne i j)
      have pk : P k ∈ L := by rw [← he,hsame]; exact right_mem_affineSpan_pair _ _ _
      have hh := hlim (hp i) (hq j) (hp k) (he ▸ left_mem_affineSpan_pair _ _ _)
        (he ▸ right_mem_affineSpan_pair _ _ _) pk (pq_ne i j)
      exact (hh.elim (fun h => hki (pinj h.symm)) (pq_ne k j)).elim
    have param (z : ℝ²) (hz : z ∈ S) : (∃ i : Fin m, P i = z) ∨ ∃ i : Fin m, Q i = z := by
      simpa [S,V,W] using hz
    rcases param a ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ <;> rcases param b hb with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · have hij : i ≠ j := fun he => hab (congrArg P he)
      subst L
      have h := hlim (hp i) (hp j) (hq (i+j)) (left_mem_affineSpan_pair _ _ _)
        (right_mem_affineSpan_pair _ _ _) (dir_on_chord hij) hab
      exact (h.elim (pq_ne _ _).symm (pq_ne _ _).symm).elim
    · exact mixed i j hlab
    · exact mixed j i (by rwa [AffineSubspace.affineSpan_pair_comm])
    · have hij : i ≠ j := fun he => hab (congrArg Q he)
      have hsub : W ⊆ U := by
        intro z hz
        obtain ⟨k,_,rfl⟩ := mem_image.mp hz
        apply mem_filter.mpr
        exact ⟨hq k,hlab ▸ (axis hij (Q k)).mpr (by simp [Q])⟩
      have hle := card_le_card hsub
      change W.card ≤ (S.filter _).card at hle
      rw [cw,hcard] at hle
      omega
  · exact (card_image_le).trans (by simp)

end
end OMA.Ordinary

theorem OMA.solution : type_of% @Erdos210.erdos_210.variants.even_upper_bound := by
  filter_upwards [Filter.eventually_ge_atTop 6] with n hn
  rintro ⟨m,rfl⟩
  have := OMA.Ordinary.construction m (by omega)
  omega
