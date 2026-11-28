import OMAStatements.S_mo_355729

namespace OMA.S_mo_355729
open Matrix Finset Set
lemma continuous_product (l n : ℕ) : Continuous (@orderedProduct l n) := by
  have h (a : List (Fin l)) : Continuous (fun Q : Fin l → Mat n => (a.map Q).prod) := by
    induction a with
    | nil => simpa using (continuous_const : Continuous (fun _ : Fin l → Mat n => (1:Mat n)))
    | cons i a ih =>
      simp only [List.map_cons,List.prod_cons]
      fun_prop
  convert h (List.ofFn (fun i : Fin l => i)).reverse using 1
  funext Q
  simp [orderedProduct,List.map_reverse,List.map_ofFn,Function.comp_def]
lemma continuous_loss {m n : ℕ} (X Y : Family m n) : Continuous (loss X Y) := by
  unfold loss
  fun_prop
lemma compact_sublevel {m n : ℕ} (X Y : Family m n) (hX : ∀ i,IsUnit (X i)) (c : ℝ) :
    IsCompact {Q | feasible Q ∧ loss X Y Q ≤ c} := by
  let S : Set (Family m n) := {Q | feasible Q ∧ loss X Y Q ≤ c}
  have hc : IsClosed S := (isClosed_eq (continuous_product _ _) continuous_const).inter
    (isClosed_le (continuous_loss X Y) continuous_const)
  let B : Set (Family m n) := {R | ∀ k i j, R k i j ∈ Icc (-c-1) (c+1)}
  have hB : IsCompact B := isCompact_pi_infinite fun _ => isCompact_Icc.matrix
  let back (R : Family m n) : Family m n := fun k => (R k+Y k)*(X k)⁻¹
  have hback : Continuous back := by unfold back; fun_prop
  apply (hB.image hback).of_isClosed_subset hc
  intro Q hQ
  let R (k) := Q k*X k-Y k
  have hsq (k : Fin (m+1)) (i j : Fin n) : (R k i j)^2 ≤ c := by
    apply le_trans _ hQ.2
    unfold loss
    calc (R k i j)^2 ≤ ∑ z,(R k i z)^2 := single_le_sum (f := fun z => (R k i z)^2) (fun z _ => sq_nonneg _) (mem_univ j)
         _ ≤ ∑ y,∑ z,(R k y z)^2 := single_le_sum (f := fun y => ∑ z,(R k y z)^2) (fun y _ => sum_nonneg fun z _ => sq_nonneg _) (mem_univ i)
         _ ≤ ∑ x,∑ y,∑ z,(R x y z)^2 := single_le_sum (f := fun x => ∑ y,∑ z,(R x y z)^2)
                 (fun x _ => sum_nonneg fun y _ => sum_nonneg fun z _ => sq_nonneg _) (mem_univ k)
  refine ⟨R,fun k i j => ?_,?_⟩
  · constructor <;> nlinarith [hsq k i j,sq_nonneg (R k i j-1/2),sq_nonneg (R k i j+1/2)]
  · funext k
    dsimp [back,R]
    rw [sub_add_cancel,Matrix.mul_nonsing_inv_cancel_right _ _ ((X k).isUnit_iff_isUnit_det.mp (hX k))]
lemma exists_optimum {m n : ℕ} (X Y : Family m n) (hX : ∀ i,IsUnit (X i)) :
    ∃ Q, feasible Q ∧ ∀ Z,feasible Z → loss X Y Q ≤ loss X Y Z := by
  let O : Family m n := fun _ => 1
  have ho : feasible O := by simp [feasible,orderedProduct,O,List.ofFn_const]
  let S : Set (Family m n) := {Q | feasible Q ∧ loss X Y Q ≤ loss X Y O}
  have hO : O ∈ S := ⟨ho,le_rfl⟩
  obtain ⟨Q,hQ,hm⟩ := (compact_sublevel X Y hX (loss X Y O)).exists_isMinOn
    ⟨O,hO⟩ (continuous_loss X Y).continuousOn
  refine ⟨Q,hQ.1,fun Z hZ => ?_⟩
  by_cases h : loss X Y Z ≤ loss X Y O
  · exact hm ⟨hZ,h⟩
  · exact hQ.2.trans (le_of_not_ge h)
end OMA.S_mo_355729

namespace OMA.S_mo_355729
open Matrix Filter Set Topology
private lemma prod_last {m n : ℕ} (Z : Family m n) :
    orderedProduct Z=Z (Fin.last m)*orderedProduct (fun k => Z k.castSucc) := by
  unfold orderedProduct
  rw [List.ofFn_succ' Z,List.concat_eq_append,List.reverse_append]
  simp
lemma candidate_feasible {m n : ℕ} (q : RatPrefix m n) : feasible (candidate q) := by
  unfold candidate completePrefix
  split_ifs with h
  · simp [feasible,orderedProduct]
  · rw [feasible,prod_last]
    simp only [Fin.snoc_last,Fin.snoc_castSucc]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)
private lemma cast_dense {m n : ℕ} : DenseRange (@castPrefix m n) :=
  DenseRange.piMap fun _ => DenseRange.piMap fun _ => DenseRange.piMap fun _ => Rat.denseRange_cast
lemma feasible_approx {m n : ℕ} (cp : Continuous (@orderedProduct m n)) (Z : Family m n) (hz : feasible Z)
    (U : Set (Family m n)) (hU : U ∈ 𝓝 Z) : ∃ q : RatPrefix m n,candidate q ∈ U := by
  let w (k : Fin m) := Z k.castSucc
  have hprod : Z (Fin.last m)*orderedProduct w=1 := (prod_last Z).symm.trans hz
  have hdet : (orderedProduct w).det ≠ 0 := by
    have h := congrArg Matrix.det hprod
    rw [Matrix.det_mul,Matrix.det_one] at h
    exact right_ne_zero_of_mul_eq_one h
  have hi := Matrix.inv_eq_left_inv hprod
  have hs : Fin.snoc w (orderedProduct w)⁻¹=Z := by
    rw [hi]
    exact Fin.snoc_init_self _
  let F (v : Fin m → Mat n) : Family m n := Fin.snoc v (orderedProduct v)⁻¹
  have hcont : ContinuousAt F w := by
    apply continuousAt_pi.mpr
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · change ContinuousAt (fun v : Fin m → Mat n => Fin.snoc (α:=fun _ => Mat n) v (orderedProduct v)⁻¹ (Fin.last m)) w
      simp only [Fin.snoc_last]
      apply (continuousAt_matrix_inv _ ?_).comp cp.continuousAt
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    · change ContinuousAt (fun v : Fin m → Mat n => Fin.snoc (α:=fun _ => Mat n) v (orderedProduct v)⁻¹ j.castSucc) w
      simp only [Fin.snoc_castSucc]
      exact (continuous_apply j).continuousAt
  have hc : ContinuousAt completePrefix w := by
    apply (continuousAt_congr (g:=F) ?_).mpr hcont
    filter_upwards [cp.matrix_det.continuousAt.eventually_ne hdet] with v hv
    simp [completePrefix,F,hv]
  have he : completePrefix w=Z := by simpa [completePrefix,hdet] using hs
  obtain ⟨q,hq⟩ := cast_dense.mem_nhds (hc.preimage_mem_nhds (he.symm ▸ hU))
  exact ⟨q,hq⟩
end OMA.S_mo_355729

namespace OMA.S_mo_355729
open Matrix Filter Set Topology
variable {m n : ℕ}
private lemma best_le (X Y : Family m n) (e : ℕ → RatPrefix m n) {k N : ℕ} (hk : k≤N) :
    bestThrough X Y e N ≤ loss X Y (candidate (e k)) := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by omega),rfl⟩
lemma best_index (X Y : Family m n) (e : ℕ → RatPrefix m n) (N : ℕ) :
    ∃ k≤N,bestThrough X Y e N=loss X Y (candidate (e k)) := by
  have h := Finset.min'_mem ((Finset.range (N+1)).image (fun k => loss X Y (candidate (e k)))) (by simp)
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp h
  exact ⟨k,by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk,he.symm⟩
lemma best_converges (X Y Z : Family m n) (hz : feasible Z)
    (ho : ∀ W,feasible W → loss X Y Z ≤ loss X Y W)
    (e : ℕ → RatPrefix m n) (he : Function.Surjective e) :
    Tendsto (bestThrough X Y e) atTop (𝓝 (loss X Y Z)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    apply Filter.Eventually.of_forall
    intro N
    obtain ⟨k,_,hk⟩ := best_index X Y e N
    rw [hk]
    exact hb.trans_le (ho _ (candidate_feasible _))
  · intro b hb
    have hU : {W | loss X Y W<b} ∈ 𝓝 Z := (continuous_loss X Y).continuousAt.eventually_lt continuousAt_const hb
    obtain ⟨q,hq⟩ := feasible_approx (continuous_product m n) Z hz _ hU
    obtain ⟨k,rfl⟩ := he q
    exact (eventually_ge_atTop k).mono fun N hN => (best_le X Y e hN).trans_lt hq
lemma best_subsequence (X Y Z : Family m n) (hX : ∀ k,IsUnit (X k)) (hz : feasible Z)
    (ho : ∀ W,feasible W → loss X Y Z ≤ loss X Y W)
    (e : ℕ → RatPrefix m n) (he : Function.Surjective e) (v : ℕ → ℕ)
    (hv : ∀ N,loss X Y (candidate (e (v N)))=bestThrough X Y e N) :
    ∃ W : Family m n, feasible W ∧ (∀ V,feasible V → loss X Y W ≤ loss X Y V) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun N => candidate (e (v (φ N)))) atTop (𝓝 W) := by
  let _ : FirstCountableTopology (Family m n) := inferInstanceAs (FirstCountableTopology (Fin (m+1) → Fin n → Fin n → ℝ))
  let seq (N : ℕ) := candidate (e (v N))
  have hmem (N : ℕ) : seq N ∈ {W | feasible W ∧ loss X Y W ≤ loss X Y (candidate (e 0))} :=
    ⟨candidate_feasible _,(hv N).le.trans (best_le X Y e (Nat.zero_le N))⟩
  obtain ⟨W,hW,φ,hφ,hlim⟩ := (compact_sublevel X Y hX _).tendsto_subseq hmem
  have ha : Tendsto (fun N => loss X Y (seq (φ N))) atTop (𝓝 (loss X Y W)) :=
    (continuous_loss X Y).continuousAt.tendsto.comp hlim
  have hb : Tendsto (fun N => loss X Y (seq (φ N))) atTop (𝓝 (loss X Y Z)) := by
    simpa only [seq,hv,Function.comp_def] using (best_converges X Y Z hz ho e he).comp hφ.tendsto_atTop
  have heq := tendsto_nhds_unique ha hb
  exact ⟨W,hW.1,fun V hV => heq.le.trans (ho V hV),φ,hφ,hlim⟩
end OMA.S_mo_355729

open OMA.S_mo_355729
theorem OMA.solution : type_of% @OMA.S_mo_355729.main := by
  refine ⟨fun m n => exists_surjective_nat (Fin m → Fin n → Fin n → ℚ),fun _ _ => candidate_feasible,?_⟩
  intro m n X Y hX
  obtain ⟨Z,hz,ho⟩ := exists_optimum X Y hX
  exact ⟨compact_sublevel X Y hX,Z,hz,ho,fun e he => ⟨best_index X Y e,
    best_converges X Y Z hz ho e he,best_subsequence X Y Z hX hz ho e he⟩⟩
