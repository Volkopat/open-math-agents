import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1

/-! The cyclotomic automorphism of exponent m+1 on a regular 2m-gon separates vertices and chords by parity. -/

namespace Erdos1082Descent

open Polynomial OMA.R_Erdos1082_erdos_1082_parts_i_R1
open scoped Polynomial

lemma linear_chord_bound {L : Type*} [Field L] [CharZero L] (S : Finset L) (u v k : L) (hn : u ≠ 0 ∨ v ≠ 0 ∨ k ≠ 0)
    (hs : ∀ z ∈ S, z ≠ 0 ∧ u*z + v/z + k = 0) : S.card ≤ 2 := by
  classical
  let P : Polynomial L := C u*X^2 + C k*X + C v
  have hne : P ≠ 0 := by
    intro he
    have h0 := congrArg (fun f : Polynomial L => f.coeff 0) he
    have h1 := congrArg (fun f : Polynomial L => f.coeff 1) he
    have h2 := congrArg (fun f : Polynomial L => f.coeff 2) he
    simp [P,coeff_X_pow,coeff_X,coeff_C] at h0 h1 h2
    tauto
  have hdeg : P.natDegree ≤ 2 := by dsimp [P]; compute_degree
  have hsub : S ⊆ P.roots.toFinset := by
    intro z hz
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hne).mpr
    obtain ⟨hnz,he⟩ := hs z hz
    change eval z P = 0
    simp only [P,eval_add,eval_mul,eval_C,eval_X,eval_pow]
    field_simp [hnz] at he
    linear_combination he
  exact (Finset.card_le_card hsub).trans <| (Multiset.toFinset_card_le _).trans <| (card_roots' P).trans hdeg

lemma chord_ratio_distance (p : ℂ) (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle) = T)
    (z : Circle) (h : dist p (z : ℂ) ∈ distanceSet T) :
    ∃ w ∈ T, dist p (z : ℂ) = dist (w : ℂ) 1 := by
  classical
  obtain ⟨⟨x,y⟩,hxy,he⟩ := Finset.mem_image.mp h
  obtain ⟨hx,hy,_⟩ := Finset.mem_offDiag.mp hxy
  have hmem (w : Circle) : w ∈ H ↔ w ∈ T := by change w ∈ (H : Set Circle) ↔ _; rw [hT]; rfl
  refine ⟨x/y, (hmem _).mp (H.div_mem ((hmem _).mpr hx) ((hmem _).mpr hy)), ?_⟩
  rw [←he]
  change dist (x : ℂ) (y : ℂ) = dist ((x : ℂ)/(y : ℂ)) 1
  rw [dist_eq_norm,dist_eq_norm,div_sub_one (Circle.coe_ne_zero _),norm_div,Circle.norm_coe,div_one]

lemma cyclic_chord_data_linked (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle) = T)
    (p : ℂ) (hp : p ≠ 0) (hnorm : ‖p‖ ≠ 1) (S : Finset Circle) (hST : S ⊆ T)
    (hin : ∀ z ∈ S, dist p (z : ℂ) ∈ distanceSet T) (hS : 2 < S.card)
    (a : ℕ) (ha : a.Coprime T.card) :
    ∃ (K : IntermediateField ℚ ℂ) (σ : K →+* K) (P : Finset K) (u v k : K),
      P.image (fun z : K => (z : ℂ)) = S.image (fun z : Circle => (z : ℂ)) ∧
      (u : ℂ) = starRingEnd ℂ p ∧ (v : ℂ) = p ∧ (k : ℂ) = 1-(Complex.normSq p : ℂ) ∧
      S.card = P.card ∧ u ≠ 0 ∧ v ≠ 0 ∧ k ≠ 0 ∧ k = 1-u*v ∧ ∀ z ∈ P,
      z ≠ 0 ∧ z^T.card = 1 ∧ σ z = z^a ∧ ∃ w : K, w ≠ 0 ∧ w^T.card = 1 ∧ σ w = w^a ∧
      w + w⁻¹ = u*z + v/z + k ∧ ∃ w₀ ∈ T, (w : ℂ) = (w₀ : ℂ) ∧ dist p (z : ℂ) = dist (w₀ : ℂ) 1 := by
  classical
  have : NeZero T.card := ⟨by have := Finset.card_le_card hST; omega⟩
  obtain ⟨K,hK,σ,hσ⟩ := automorphism_on_roots T.card a ha
  let u := starRingEnd ℂ p
  let v := p
  let k := 1-(Complex.normSq p : ℂ)
  have hmem (z : Circle) (hz : z ∈ T) : (z : ℂ) ∈ K := hK _ (finite_subgroup_root T H hT z hz)
  have hval (z : Circle) (hz : z ∈ S) : u*(z : ℂ)^2 + k*(z : ℂ) + v ∈ K := by
    obtain ⟨w,hw,he⟩ := chord_ratio p T H hT z (hin z hz)
    have hm := K.mul_mem (K.add_mem (hmem w hw) (K.inv_mem (hmem w hw))) (hmem z (hST hz))
    have heq : u*(z : ℂ)^2 + k*(z : ℂ) + v = ((w : ℂ)+(w : ℂ)⁻¹)*(z : ℂ) := by
      rw [he]; dsimp [u,v,k]; field_simp [Circle.coe_ne_zero]; ring
    rwa [heq]
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp hS
  obtain ⟨hu,hv,hk⟩ := interpolated_coefficients K.toSubfield u v k x y z
    (hmem x (hST hx)) (hmem y (hST hy)) (hmem z (hST hz))
    (Circle.coe_injective.ne hxy) (Circle.coe_injective.ne hyz) (Circle.coe_injective.ne hxz)
    (hval x hx) (hval y hy) (hval z hz)
  let lift (z : S) : K := ⟨(z.1 : ℂ),hmem z.1 (hST z.2)⟩
  let P := S.attach.image lift
  have hlift : Function.Injective lift := fun _ _ h => Subtype.ext (Circle.coe_injective (congrArg ((↑) : K → ℂ) h))
  have hP : P.card = S.card := by dsimp [P]; rw [Finset.card_image_of_injective _ hlift,Finset.card_attach]
  have hlink : P.image (fun z : K => (z : ℂ)) = S.image (fun z : Circle => (z : ℂ)) := by
    ext x
    constructor
    · intro h
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_image.mpr ⟨j.1,j.2,rfl⟩
    · intro h
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨lift ⟨z,hz⟩,Finset.mem_image.mpr ⟨⟨z,hz⟩,Finset.mem_attach _ _,rfl⟩,rfl⟩
  refine ⟨K,σ,P,⟨u,hu⟩,⟨v,hv⟩,⟨k,hk⟩,hlink,rfl,rfl,rfl,hP.symm,?_,?_,?_,?_,?_⟩
  · intro he
    have : u = 0 := congrArg ((↑) : K → ℂ) he
    exact hp ((map_eq_zero (starRingEnd ℂ)).mp this)
  · exact fun he => hp (congrArg ((↑) : K → ℂ) he)
  · intro he
    have h0 : k = 0 := congrArg ((↑) : K → ℂ) he
    have h1 : (Complex.normSq p : ℂ) = 1 := (sub_eq_zero.mp h0).symm
    have h2 : Complex.normSq p = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    exact hnorm (by nlinarith [norm_nonneg p])
  · apply Subtype.ext
    change 1-(Complex.normSq p : ℂ) = 1 - starRingEnd ℂ p*p
    rw [Complex.normSq_eq_conj_mul_self]
  · intro t ht
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨w,hw,hd⟩ := chord_ratio_distance p T H hT j.1 (hin j.1 j.2)
    have he := chord_equation p j.1 w hd
    let wK : K := ⟨(w : ℂ),hmem w hw⟩
    have hroot : lift j ^ T.card = 1 := Subtype.ext (finite_subgroup_root _ _ hT j.1 (hST j.2))
    have wroot : wK ^ T.card = 1 := Subtype.ext (finite_subgroup_root _ _ hT w hw)
    exact ⟨(fun h => (Circle.coe_ne_zero j.1) (congrArg ((↑) : K → ℂ) h)),hroot,hσ _ hroot,
      wK,(fun h => (Circle.coe_ne_zero w) (congrArg ((↑) : K → ℂ) h)),wroot,hσ _ wroot,Subtype.ext he,w,hw,rfl,hd⟩


lemma parity_constraint {L : Type*} [Field L] [CharZero L] (σ : L →+* L) (u v k z w s t : L)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (hz : z ≠ 0) (hw : w ≠ 0)
    (hsz : σ z = s*z) (htw : σ w=t*w) (he : w+w⁻¹=u*z+v/z+k) :
    (t*u-s*σ u)*z + (t*v-s*σ v)/z + (t*k - σ k) = 0 := by
  have hh := congrArg σ he
  simp only [map_add,map_mul,map_inv₀,map_div₀,hsz,htw] at hh
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp at hh ⊢ <;> field_simp [hw,hz] at he hh ⊢ <;>
    apply (mul_left_inj' hw).mp <;>
    first | linear_combination hh-he | linear_combination hh+he | linear_combination he-hh | linear_combination -hh-he


lemma exceptional_signs {L : Type*} [Field L] [CharZero L] (σ : L →+* L) (u v k s t : L)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (hk : k = 1-u*v) (h0 : k ≠ 0)
    (hU : t*u-s*σ u = 0) (hV : t*v-s*σ v=0) (hK : t*k-σ k = 0) :
    t = 1 ∧ σ u = s*u ∧ σ v = s*v ∧ σ k = k := by
  have he : σ k = 1-σ u * σ v := by rw [hk,map_sub,map_one,map_mul]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp at hU hV hK ⊢ <;>
    grind

lemma exceptional_wrong_parity {L : Type*} [Field L] [CharZero L] (σ : L →+* L) (u v k z w s : L)
    (hs : s = 1 ∨ s = -1) (hnz : z ≠ 0) (hnw : w ≠ 0) (hk : k ≠ 0)
    (hU : σ u=s*u) (hV : σ v=s*v) (hK : σ k=k)
    (hzw : w+w⁻¹ = u*z+v/z+k) (hsz : σ z=(-s)*z) (hsw : σ w=w ∨ σ w=-w) :
    u*z+v/z=0 := by
  rcases hsw with hw | hw
  · have hh := parity_constraint σ u v k z w (-s) 1 (by rcases hs with rfl | rfl <;> simp)
      (Or.inl rfl) hnz hnw hsz (by simpa using hw) hzw
    rw [hU,hV,hK] at hh
    rcases hs with rfl | rfl <;> simp at hh <;> field_simp [hnz] at hh ⊢ <;> first | linear_combination hh/2 | linear_combination -hh/2
  · have hh := parity_constraint σ u v k z w (-s) (-1) (by rcases hs with rfl | rfl <;> simp)
      (Or.inr rfl) hnz hnw hsz (by simpa using hw) hzw
    rw [hU,hV,hK] at hh
    rcases hs with rfl | rfl <;> simp at hh <;> grind

lemma exceptional_wrong_chord {L : Type*} [Field L] [CharZero L] (σ : L →+* L) (u v k z w s : L)
    (hs : s = 1 ∨ s = -1) (hz : z ≠ 0) (hw : w ≠ 0) (hU : σ u=s*u)
    (hV : σ v=s*v) (hK : σ k=k) (hzw : w+w⁻¹=u*z+v/z+k) (hsz : σ z=s*z) (hsw : σ w=-w) :
    u*z+v/z+k=0 := by
  have hh := parity_constraint σ u v k z w s (-1) hs (Or.inr rfl) hz hw hsz (by simpa using hsw) hzw
  rw [hU,hV,hK] at hh
  rcases hs with rfl | rfl <;> simp at hh <;> field_simp [hz] at hh ⊢ <;> first | linear_combination hh/2 | linear_combination -hh/2

lemma parity_majority {L : Type*} [Field L] [CharZero L] [DecidableEq L] (P : Finset L) (σ : L →+* L)
    (w : L → L) (u v k : L) (hu : u ≠ 0) (hk : k ≠ 0) (hrel : k=1-u*v)
    (m : ℕ) (hsize : 8 < P.card)
    (hl : ∀ z ∈ P, z ≠ 0 ∧ z^(2*m)=1 ∧ σ z=z^(m+1) ∧
      w z ≠ 0 ∧ (w z)^(2*m)=1 ∧ σ (w z)=(w z)^(m+1) ∧ w z+(w z)⁻¹=u*z+v/z+k) :
    ∃ s : L, (s = 1 ∨ s = -1) ∧
      P.card ≤ (P.filter (fun z => z^m=s ∧ (w z)^m=1)).card + 4 := by
  classical
  let cls (z : L) : Bool × Bool := (decide (z^m=1), decide (w z ^ m = 1))
  let eps (b : Bool) : L := if b then 1 else -1
  have signs (b : Bool) : eps b = 1 ∨ eps b = -1 := by cases b <;> simp [eps]
  have power (z : L) (hz : z^(2*m) = 1) : z^m = eps (decide (z^m=1)) := by
    have hs : (z^m)^2 = 1 := by rwa [←pow_mul,Nat.mul_comm]
    rcases sq_eq_one_iff.mp hs with hh | hh <;> simp [hh,eps]
  obtain ⟨b,_,hb⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun z (_ : z ∈ P) => Finset.mem_univ (cls z))
    (show (Finset.univ : Finset (Bool × Bool)).card * 2 < P.card by simpa using hsize)
  let s := eps b.1
  let t := eps b.2
  have hident : t*u-s*σ u=0 ∧ t*v-s*σ v=0 ∧ t*k-σ k=0 := by
    by_contra! hn
    have hcoeff : t*u-s*σ u≠0 ∨ t*v-s*σ v≠0 ∨ t*k-σ k≠0 := by tauto
    have hbound := linear_chord_bound (P.filter (fun z => cls z=b)) _ _ _ hcoeff (by
      intro z hz
      obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
      obtain ⟨hnz,hr,hsz,hnw,hrw,hsw,hd⟩ := hl z hz
      have h1 : z^m = s := (power _ hr).trans (congrArg (fun j => eps j.1) he)
      have h2 : (w z)^m = t := (power _ hrw).trans (congrArg (fun j => eps j.2) he)
      exact ⟨hnz,parity_constraint σ u v k z (w z) s t (signs _) (signs _) hnz hnw
        (by rw [hsz,pow_succ,h1]) (by rw [hsw,pow_succ,h2]) hd⟩)
    omega
  obtain ⟨_,hU,hV,hK⟩ := exceptional_signs σ u v k s t (signs _) (signs _) hrel hk hident.1 hident.2.1 hident.2.2
  let good := P.filter (fun z => z^m=s ∧ (w z)^m=1)
  let B := P.filter (fun z => u*z+v/z=0)
  let C := P.filter (fun z => u*z+v/z+k=0)
  have hB : B.card ≤ 2 := linear_chord_bound B u v 0 (Or.inl hu) (by
    intro z hz
    obtain ⟨hz,hz'⟩ := Finset.mem_filter.mp hz
    exact ⟨(hl _ hz).1, by simpa using hz'⟩)
  have hC : C.card ≤ 2 := linear_chord_bound C u v k (Or.inl hu) (by
    intro z hz
    obtain ⟨hz,hz'⟩ := Finset.mem_filter.mp hz
    exact ⟨(hl _ hz).1,hz'⟩)
  have hsub : P ⊆ good ∪ B ∪ C := by
    intro z hz
    obtain ⟨hnz,hr,hsz,hnw,hrw,hsw,hd⟩ := hl z hz
    have h1 := (power _ hr).symm ▸ signs (decide (z^m=1))
    have h2 := (power _ hrw).symm ▸ signs (decide ((w z)^m=1))
    by_cases ha : z^m=s
    · by_cases h : (w z)^m=1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,ha,h⟩))
      · have hw' := h2.resolve_left h
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,
          exceptional_wrong_chord σ u v k z (w z) s (signs _) hnz hnw hU hV hK hd
            (by rw [hsz,pow_succ,ha]) (by rw [hsw,pow_succ,hw']; ring)⟩)
    · have hneg : z^m = -s := by have hsign : s=1 ∨ s= -1 := signs _; rcases hsign with h|h <;> rcases h1 with hr|hr <;> grind
      have hw' : σ (w z) = w z ∨ σ (w z) = -(w z) := by
        rcases h2 with h|h <;> simp [hsw,pow_succ,h]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,
        exceptional_wrong_parity σ u v k z (w z) s (signs _) hnz hnw hk hU hV hK hd
          (by rw [hsz,pow_succ,hneg]) hw'⟩))
  have hh := Finset.card_le_card hsub
  have hbc := Finset.card_union_le (good ∪ B) C
  have hbb := Finset.card_union_le good B
  exact ⟨s,signs _,by change P.card ≤ good.card+4; omega⟩

lemma polygon_fiber_pow (T : Finset Circle) (m : ℕ) (hm : 0 < m) (b : ℂ) :
    (T.filter (fun z : Circle => (z : ℂ)^m=b)).card ≤ m := by
  classical
  let S := T.filter (fun z : Circle => (z : ℂ)^m=b)
  let Q : ℂ[X] := X^m-C b
  have hQ : Q ≠ 0 := X_pow_sub_C_ne_zero hm _
  have hsub : S.image (fun z : Circle => (z : ℂ)) ⊆ Q.roots.toFinset := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hQ).mpr
    change eval _ Q = 0
    simp [Q,(Finset.mem_filter.mp hz).2]
  have hle := (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (card_roots' Q))
  have he : (S.image (fun z : Circle => (z : ℂ))).card = S.card :=
    Finset.card_image_of_injective S (fun z w h => Circle.coe_injective h)
  rw [he] at hle
  have hdeg : Q.natDegree = m := natDegree_X_pow_sub_C
  exact hle.trans_eq hdeg

lemma half_subgroup (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle) = T)
    (m : ℕ) (hm : 0 < m) (hM : T.card=2*m) :
    ∃ G : Subgroup Circle, (G : Set Circle) = ↑(T.filter (fun z : Circle => (z : ℂ)^m=1)) ∧
      (T.filter (fun z : Circle => (z : ℂ)^m=1)).card = m := by
  classical
  let G := H ⊓ (powMonoidHom m : Circle →* Circle).ker
  have hmem (z : Circle) : z ∈ H ↔ z ∈ T := by change z ∈ (H : Set Circle) ↔ _; rw [hT]; rfl
  refine ⟨G,?_,?_⟩
  · ext z
    change (z ∈ H ∧ z^m=1) ↔ z ∈ T.filter (fun z : Circle => (z : ℂ)^m=1)
    rw [Finset.mem_filter,hmem]
    constructor
    · rintro ⟨hz,h⟩; exact ⟨hz,by simpa using congrArg ((↑) : Circle → ℂ) h⟩
    · rintro ⟨hz,h⟩; exact ⟨hz,Circle.coe_injective (by simpa using h)⟩
  · have hroot (z : Circle) (hz : z ∈ T) : (z : ℂ)^m=1 ∨ (z : ℂ)^m = -1 := by
      apply sq_eq_one_iff.mp
      rw [←pow_mul,Nat.mul_comm,←hM]
      have e : H ≃ T := Equiv.subtypeEquivRight (fun x => hmem x)
      have hn : Nat.card H = T.card := (Nat.card_congr e).trans (Nat.card_eq_finsetCard T)
      let h : H := ⟨z,(hmem z).mpr hz⟩
      have hh := pow_card_eq_one' (x := h)
      rw [hn] at hh
      exact congrArg (fun y : H => (y.1 : ℂ)) hh
    have heq : T.filter (fun z : Circle => ¬ (z : ℂ)^m=1) = T.filter (fun z : Circle => (z : ℂ)^m = -1) := by
      apply Finset.filter_congr
      intro z hz
      rcases hroot z hz with h | h <;> rw [h] <;> norm_num
    have hab := Finset.card_filter_add_card_filter_not (s := T) (fun z : Circle => (z : ℂ)^m=1)
    rw [heq] at hab
    have h1 := polygon_fiber_pow T m hm 1
    have hn := polygon_fiber_pow T m hm (-1)
    omega

lemma descend_even (m : ℕ) (hm : 16 ≤ m) (heven : Even m) (T : Finset Circle) (H : Subgroup Circle)
    (hT : (H : Set Circle) = T) (hM : T.card = 2*m) (q : ℂ) (hp : q ≠ 0) (hn : ‖q‖ ≠ 1)
    (hbig : T.card < 2 * (T.filter (fun z : Circle => dist q (z : ℂ) ∈ distanceSet T)).card) :
    ∃ (V : Finset Circle) (G : Subgroup Circle) (p : ℂ), (G : Set Circle) = V ∧ V.card = m ∧
      p ≠ 0 ∧ ‖p‖ ≠ 1 ∧ V.card < 2 * (V.filter (fun z : Circle => dist p (z : ℂ) ∈ distanceSet V)).card := by
  classical
  let S := T.filter (fun z : Circle => dist q (z : ℂ) ∈ distanceSet T)
  have hS : m < S.card := by change T.card < 2*S.card at hbig; omega
  have hcop : (m+1).Coprime T.card := by
    rw [hM,Nat.coprime_mul_iff_right]
    constructor
    · rw [Nat.coprime_two_right]
      obtain ⟨j,hj⟩ := heven
      exact ⟨j,by omega⟩
    · rw [Nat.add_comm,Nat.coprime_add_self_left]; simp
  obtain ⟨K,σ,P,u,v,k,hlink,_,_,_,hcard,hu,_,hk,hrel,hl⟩ := cyclic_chord_data_linked T H hT q hp hn S
    (Finset.filter_subset _ _) (fun _ hz => (Finset.mem_filter.mp hz).2) (by omega) (m+1) hcop
  let w (z : K) := if h : z ∈ P then ((hl z h).2.2.2).choose else 0
  have hw (z : K) (hz : z ∈ P) : w z ≠ 0 ∧ (w z)^T.card = 1 ∧ σ (w z) = (w z)^(m+1) ∧
      w z + (w z)⁻¹ = u*z + v/z + k ∧ ∃ w₀ ∈ T, (w z : ℂ) = (w₀ : ℂ) ∧ dist q (z : ℂ) = dist (w₀ : ℂ) 1 := by
    simpa [w,hz] using ((hl z hz).2.2.2).choose_spec
  obtain ⟨s,hs,hgood⟩ := parity_majority P σ w u v k hu hk hrel m (by omega) (by
    intro z hz
    obtain ⟨hnz,hr,ha,_⟩ := hl z hz
    obtain ⟨hnw,hrw,haw,hd,_⟩ := hw z hz
    exact ⟨hnz,hM ▸ hr,ha,hnw,hM ▸ hrw,haw,hd⟩)
  let A := P.filter (fun z => z^m=s ∧ (w z)^m=1)
  change P.card ≤ A.card + 4 at hgood
  have hpoint (z : K) (hz : z ∈ P) : ∃ a ∈ S, (a : ℂ)=(z : ℂ) := by
    have ht : (z : ℂ) ∈ P.image (fun z : K => (z : ℂ)) := Finset.mem_image_of_mem _ hz
    rwa [hlink,Finset.mem_image] at ht
  let pt (z : A) : Circle := (hpoint z.1 (Finset.mem_filter.mp z.2).1).choose
  have hpt (z : A) : pt z ∈ S ∧ ((pt z : Circle) : ℂ)=(z.1 : ℂ) :=
    (hpoint z.1 (Finset.mem_filter.mp z.2).1).choose_spec
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  let B : Circle := pt ⟨b,hb⟩
  have hB : (B : ℂ)^m=(s : ℂ) := by
    rw [(hpt ⟨b,hb⟩).2]; exact congrArg ((↑) : K → ℂ) (Finset.mem_filter.mp hb).2.1
  let V := T.filter (fun z : Circle => (z : ℂ)^m=1)
  obtain ⟨G,hG,hV⟩ := half_subgroup T H hT m (by omega) hM
  have hHmem (z : Circle) : z ∈ H ↔ z ∈ T := by change z ∈ (H : Set Circle) ↔ _; rw [hT]; rfl
  have hone : (1 : Circle) ∈ V := Finset.mem_filter.mpr ⟨(hHmem _).mp H.one_mem,by simp⟩
  let f (z : A) := pt z / B
  have hf : Function.Injective f := by
    intro z y he
    have hh : pt z = pt y := div_left_injective he
    have hval := congrArg ((↑) : Circle → ℂ) hh
    rw [(hpt z).2,(hpt y).2] at hval
    exact Subtype.ext (Subtype.ext hval)
  have hsub : A.attach.image f ⊆ V.filter (fun z : Circle => dist (q/(B:ℂ)) (z : ℂ) ∈ distanceSet V) := by
    intro y hy
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hzP,hzpow,hwzpow⟩ := Finset.mem_filter.mp z.2
    have hzS := (hpt z).1
    have hBS := (hpt ⟨b,hb⟩).1
    have htoT {c : Circle} (hc : c ∈ S) : c ∈ T := (Finset.mem_filter.mp hc).1
    have hfv : f z ∈ V := Finset.mem_filter.mpr ⟨(hHmem _).mp (H.div_mem ((hHmem _).mpr (htoT hzS)) ((hHmem _).mpr (htoT hBS))),by
      change ((pt z : ℂ)/(B : ℂ))^m = 1
      rw [div_pow,hB,(hpt z).2]
      have he : (z.1 : ℂ)^m=(s:ℂ) := congrArg ((↑) : K → ℂ) hzpow
      rw [he,div_self]; rcases hs with rfl|rfl <;> simp⟩
    apply Finset.mem_filter.mpr ⟨hfv,?_⟩
    obtain ⟨c,hc,hcw,hd⟩ := (hw z.1 hzP).2.2.2.2
    have hcV : c ∈ V := Finset.mem_filter.mpr ⟨hc,by rw [←hcw]; exact congrArg ((↑) : K → ℂ) hwzpow⟩
    have hqd : dist (q/(B:ℂ)) ((f z : Circle) : ℂ) = dist q (z.1 : ℂ) := by
      change dist (q/(B:ℂ)) ((pt z : ℂ)/(B:ℂ)) = _
      rw [dist_eq_norm,←sub_div,norm_div,Circle.norm_coe,div_one,(hpt z).2,dist_eq_norm]
    rw [hqd,hd]
    have hcne : c ≠ 1 := by
      intro he
      rw [he] at hd
      change dist q (z.1 : ℂ) = dist (1 : ℂ) 1 at hd
      rw [dist_self] at hd
      have hx := congrArg norm (dist_eq_zero.mp hd)
      rw [←(hpt z).2,Circle.norm_coe] at hx
      exact hn hx
    exact Finset.mem_image.mpr ⟨(c,1),Finset.mem_offDiag.mpr ⟨hcV,hone,hcne⟩,rfl⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf,Finset.card_attach] at hle
  refine ⟨V,G,q/(B:ℂ),hG,hV,div_ne_zero hp (Circle.coe_ne_zero _),by simpa [norm_div,Circle.norm_coe] using hn,?_⟩
  change V.card=m at hV
  omega

end Erdos1082Descent

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1.H4 := Erdos1082Descent.descend_even
