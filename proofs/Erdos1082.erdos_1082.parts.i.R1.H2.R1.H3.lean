import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Distance families of a regular polygon

Two points at distinct positive radii determine two families of distances to the vertices of a
regular polygon. We count coincidences using a Laurent equation in two roots of unity. Projection
of the coefficients to a cyclotomic field allows its Galois group to act on the equation. A
coprime exponent m gives a polynomial of degree at most 4m in the first coordinate. At even
orders, the half-turn Galois action also yields an order-independent bound of 36 on this count.
The use of squaring and sign changes is related to the method of F. Beukers and C. J. Smyth,
*Cyclotomic points on curves*, sections 3.5 and 4.1,
https://webhomes.maths.ed.ac.uk/~chris/preprints/beukers_smyth.pdf.

The counting argument gives the stated inequality and a quadratic lower bound for distinct
distances when a second nonconcentric circle contains enough points.
-/

open Polynomial OMA.R_Erdos1082_erdos_1082_parts_i_R1

namespace Erdos1082GeneralCurve

lemma normalized_trace_poly {L : Type*} [Field L] (u v k h : L) :
    ∀ m : ℕ, ∃ P : Polynomial L, P.natDegree≤2*m ∧ P.coeff 0=(if m=0 then 2 else u^m) ∧
      P.coeff 1=(m:L)*u^(m-1)*k ∧ ∀ z w : L, z≠0 → w≠0 → w+h/w=u/z+v*z+k →
        P.eval z=z^m*(w^m+(h/w)^m)
  | 0 => by refine ⟨C 2,by simp,by simp,by simp,?_⟩; intro z w hz hw he; simp; ring
  | 1 => by
    let F : Polynomial L := C u+C k*X+C v*X^2
    refine ⟨F,by dsimp [F]; compute_degree,by simp [F,mul_coeff_zero],
      by simp [F,mul_coeff_one,coeff_X_pow],?_⟩
    intro z w hz hw he
    simp only [F,eval_add,eval_mul,eval_C,eval_X,eval_pow,pow_one]
    rw [he]; field_simp [hz]; ring
  | n+2 => by
    obtain ⟨P,hP,P₀,P₁,hPv⟩ := normalized_trace_poly u v k h n
    obtain ⟨Q,hQ,Q₀,Q₁,hQv⟩ := normalized_trace_poly u v k h (n+1)
    let F : Polynomial L := C u+C k*X+C v*X^2
    have hF : F.natDegree≤2 := by dsimp [F]; compute_degree
    have F₀ : F.coeff 0=u := by simp [F,mul_coeff_zero]
    have F₁ : F.coeff 1=k := by simp [F,mul_coeff_one,coeff_X_pow]
    let R := F*Q-C h*X^2*P
    refine ⟨R,?_,?_,?_,?_⟩
    · have h₁ := (natDegree_mul_le (p:=F) (q:=Q)).trans (Nat.add_le_add hF hQ)
      have hc : (C h*(X:Polynomial L)^2).natDegree≤2 := by compute_degree
      have h₂ := (natDegree_mul_le (p:=C h*X^2) (q:=P)).trans (Nat.add_le_add hc hP)
      exact (natDegree_sub_le ..).trans (max_le (by omega) (by omega))
    · simp only [R,coeff_sub,mul_coeff_zero,F₀,Q₀,Nat.add_eq_zero_iff,Nat.succ_ne_self, and_false,if_false]
      simp [coeff_X_pow,pow_succ]; ring
    · simp only [R,coeff_sub,mul_coeff_one,mul_coeff_zero,F₀,F₁,Q₀,Q₁]
      simp [coeff_X_pow,pow_succ]; ring
    · intro z w hz hw he
      simp only [R,eval_sub,eval_mul,eval_C,eval_pow,eval_X,hPv _ _ hz hw he,hQv _ _ hz hw he]
      have hFe : F.eval z=(w+h/w)*z := by
        simp only [F,eval_add,eval_mul,eval_C,eval_X,eval_pow]
        rw [he]; field_simp [hz]; ring
      rw [hFe]
      have hprod : w*(h/w)=h := by field_simp
      calc
        _ = z^(n+2)*((w+h/w)*(w^(n+1)+(h/w)^(n+1))-(w*(h/w))*(w^n+(h/w)^n)) := by rw [hprod]; ring
        _ = _ := by ring


set_option maxHeartbeats 1100000 in
lemma power_trace_bound {L : Type*} [Field L] [CharZero L] (S : Finset L)
    (m : ℕ) (hm : 2 ≤ m) (u v k h U V K H : L) (hu : u≠0) (hk : k≠0) (hh : h≠0) (hH : H≠0)
    (hs : ∀ z∈S, z≠0 ∧ ∃ w : L, w≠0 ∧ w+h/w=u/z+v*z+k ∧
      w^m+H/w^m=U/z^m+V*z^m+K) : S.card≤4*m := by
  classical
  obtain ⟨P,hP,P₀,P₁,heval⟩ := normalized_trace_poly u v k h m
  have hm0 : m≠0 := by omega
  have hm1 : m≠1 := by omega
  have h2m0 : 2*m≠0 := by omega
  have h2m1 : 2*m≠1 := by omega
  rw [if_neg hm0] at P₀
  let α := u^m
  let β := (m:L)*u^(m-1)*k
  have hα : α≠0 := pow_ne_zero _ hu
  have hβ : β≠0 := mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hm0) (pow_ne_zero _ hu)) hk
  let a := U-α
  let δ := H-h^m
  let B : Polynomial L := C U+C K*X^m+C V*X^(2*m)-P
  have B₀ : B.coeff 0=a := by simp [B,a,α,P₀,coeff_C_mul,coeff_X_pow,hm0,h2m0,Ne.symm hm0,Ne.symm h2m0]
  have B₁ : B.coeff 1= -β := by simp [B,β,P₁,coeff_C_mul,coeff_X_pow,hm1,h2m1,Ne.symm hm1,Ne.symm h2m1]
  have hB : B.natDegree≤2*m := by
    dsimp only [B]
    compute_degree <;> omega
  have hB₀ : B≠0 := by intro he; rw [he,coeff_zero] at B₁; exact hβ (neg_eq_zero.mp B₁.symm)
  let R : Polynomial L := C δ*B*P-C (δ^2)*X^(2*m)-C (h^m)*B^2
  have hR : R.natDegree≤4*m := by
    dsimp only [R]
    compute_degree <;> omega
  have hR₀ : R.coeff 0=δ*a*α-h^m*a^2 := by
    simp only [R,coeff_sub,mul_coeff_zero,coeff_C_zero,coeff_X_pow,B₀,P₀,pow_two]
    simp [α,mul_coeff_zero,B₀,h2m0,hm0,Ne.symm h2m0]
  have hR₁ : R.coeff 1=δ*(a*β-β*α)+2*h^m*a*β := by
    simp only [R,pow_two,coeff_sub,mul_coeff_one,mul_coeff_zero,coeff_C,coeff_X_pow,B₀,B₁,P₀,P₁,Ne.symm h2m1,Ne.symm h2m0,if_false,if_true,one_ne_zero,zero_ne_one]
    dsimp only [α,β]; ring
  have hne : R≠0 := by
    intro hzero
    by_cases hd : δ=0
    · have hp : C (h^m)*B^2≠0 := mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ hh)) (pow_ne_zero _ hB₀)
      simp [R,hd,hh,hB₀] at hzero
    rw [hzero,coeff_zero] at hR₀ hR₁
    by_cases ha : a=0
    · rw [ha] at hR₁
      have hz : δ*β*α=0 := by linear_combination hR₁
      exact (mul_ne_zero (mul_ne_zero hd hβ) hα) hz
    have ht : δ*α=h^m*a := by
      apply (mul_left_inj' ha).mp
      linear_combination -hR₀
    have he : a*β*H=0 := by
      dsimp only [δ] at hR₁ ht
      linear_combination -hR₁+β*ht
    exact (mul_ne_zero (mul_ne_zero ha hβ) hH) he
  have hsub : S⊆R.roots.toFinset := by
    intro z hz
    obtain ⟨hz,w,hw,hl,hm'⟩ := hs z hz
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hne).mpr
    have hz' := pow_ne_zero m hz
    have hw' := pow_ne_zero m hw
    have hPe := heval z w hz hw hl
    have hBe : B.eval z=z^m*(δ/w^m) := by
      simp only [B,eval_sub,eval_add,eval_mul,eval_C,eval_pow,eval_X,hPe]
      have he : U+K*z^m+V*z^(2*m)=z^m*(w^m+H/w^m) := by rw [hm',show 2*m=m+m by omega,pow_add]; field_simp [hz']; ring
      rw [he,div_pow]
      dsimp only [δ]; field_simp [hw']; ring
    change R.eval z=0
    simp only [R,eval_sub,eval_mul,eval_C,eval_X,eval_pow,hBe,hPe,div_pow]
    rw [show 2*m=m+m by omega,pow_add]
    dsimp only [δ]; field_simp [hw']; ring
  exact (Finset.card_le_card hsub).trans <| (Multiset.toFinset_card_le _).trans <| (card_roots' R).trans hR


lemma coprime_laurent_points (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (m : ℕ) (hm2 : 2 ≤ m) (hcop : m.Coprime T.card) (a b k c d : ℂ) (ha : a≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (S : Finset Circle) (hST : S⊆T)
    (hm : ∀ z∈S, ∃ w∈T, c*(w:ℂ)+d/(w:ℂ)=a/(z:ℂ)+b*(z:ℂ)+k) : S.card≤4*m := by
  classical
  by_cases he : T.card=0
  · have := Finset.card_le_card hST; omega
  let : NeZero T.card := ⟨he⟩
  obtain ⟨K,hroots,σ,hσ⟩ := automorphism_on_roots T.card m hcop
  have hmem (z : Circle) (hz : z∈T) : (z:ℂ)∈K := hroots _ (finite_subgroup_root _ _ hT z hz)
  let M : Finset ℂ := {a,k,c,d}
  have hn (v : M) : v.1≠0 := by
    have ht := v.2
    simp only [M,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with he|he|he|he <;> rw [he] <;> assumption
  obtain ⟨F,hF⟩ := Module.exists_dual_forall_apply_ne_zero (K:=K) (fun v : M => v.1) hn
  have hfa : F a≠0 := hF ⟨a,by simp [M]⟩
  have hfk : F k≠0 := hF ⟨k,by simp [M]⟩
  have hfc : F c≠0 := hF ⟨c,by simp [M]⟩
  have hfd : F d≠0 := hF ⟨d,by simp [M]⟩
  let u := F a/F c
  let v := F b/F c
  let κ := F k/F c
  let h := F d/F c
  have hu : u≠0 := div_ne_zero hfa hfc
  have hk' : κ≠0 := div_ne_zero hfk hfc
  have hh : h≠0 := div_ne_zero hfd hfc
  let lift (z : S) : K := ⟨(z.1:ℂ),hmem _ (hST z.2)⟩
  let P := S.attach.image lift
  have hlift : Function.Injective lift := fun _ _ he => Subtype.ext (Circle.coe_injective (congrArg ((↑):K→ℂ) he))
  have hsize : P.card=S.card := by dsimp only [P]; rw [Finset.card_image_of_injective _ hlift,Finset.card_attach]
  rw [←hsize]
  apply power_trace_bound P m hm2 u v κ h (σ u) (σ v) (σ κ) (σ h) hu hk' hh ((_root_.map_ne_zero _).mpr hh)
  intro z hz
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨w,hw,he⟩ := hm z.1 z.2
  let W : K := ⟨(w:ℂ),hmem _ hw⟩
  have hrz : (lift z)^T.card=1 := Subtype.ext (finite_subgroup_root _ _ hT z.1 (hST z.2))
  have hrw : W^T.card=1 := Subtype.ext (finite_subgroup_root _ _ hT w hw)
  have hz0 : lift z≠0 := fun hh => Circle.coe_ne_zero z.1 (congrArg ((↑):K→ℂ) hh)
  have hw0 : W≠0 := fun hh => Circle.coe_ne_zero w (congrArg ((↑):K→ℂ) hh)
  have he' : W • c + W⁻¹ • d = (lift z)⁻¹ • a + lift z • b+k := by
    change (w:ℂ)*c+(w:ℂ)⁻¹*d=(z.1:ℂ)⁻¹*a+(z.1:ℂ)*b+k
    simpa only [div_eq_mul_inv,mul_comm] using he
  have lin := congrArg F he'
  simp only [map_add,LinearMap.map_smul,smul_eq_mul] at lin
  have eqn : W+h/W = u/lift z+v*lift z+κ := by
    dsimp only [h,u,v,κ]
    field_simp [hfc,hw0,hz0] at lin ⊢
    linear_combination lin
  refine ⟨hz0,W,hw0,eqn,?_⟩
  simpa only [map_add,map_mul,map_div₀,hσ (lift z) hrz,hσ W hrw] using congrArg σ eqn

lemma orbit_norm (c p : ℂ) (z : Circle) :
    ((‖c+p*(z:ℂ)‖^2:ℝ):ℂ) = (Complex.normSq c:ℂ)+(Complex.normSq p:ℂ)+
        (starRingEnd ℂ c*p)*(z:ℂ)+(c*starRingEnd ℂ p)/(z:ℂ) := by
  rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self,
    map_add,map_mul,←Circle.coe_inv_eq_conj,Circle.coe_inv]
  field_simp [Circle.coe_ne_zero z]
  ring


lemma orbit_fiber_card (T : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) (r : ℝ) :
    (T.filter fun z : Circle => ‖c+p*(z:ℂ)‖=r).card ≤ 2 := by
  classical
  let q := -c/p
  apply (Finset.card_le_card (t := T.filter fun z : Circle => dist q (z:ℂ)=r/‖p‖) ?_).trans
    (circle_fibers T q (div_ne_zero (neg_ne_zero.mpr hc) hp) _)
  intro z hz
  obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨hz,?_⟩
  have heq : q-(z:ℂ) = -(c+p*(z:ℂ))/p := by dsimp [q]; field_simp; ring
  rw [dist_eq_norm,heq,norm_div,norm_neg,he]

lemma orbit_image_size (S : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) :
    S.card ≤ 2*(S.image fun z : Circle => ‖c+p*(z:ℂ)‖).card := by
  classical
  by_contra! h
  obtain ⟨r,_,hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun z (hz : z∈S) => Finset.mem_image_of_mem (fun z : Circle => ‖c+p*(z:ℂ)‖) hz)
    (show (S.image fun z : Circle => ‖c+p*(z:ℂ)‖).card*2<S.card by omega)
  exact (not_lt_of_ge (orbit_fiber_card S c p hc hp r)) hr



lemma unconditional_orbit_intersection (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (m : ℕ) (hm : 2 ≤ m) (hcop : m.Coprime T.card) (c p q : ℂ) (hc : c≠0) (hp : p≠0) (hq : q≠0) (hn : ‖p‖≠‖q‖) :
    (T.filter fun z : Circle => ‖c+p*(z:ℂ)‖∈T.image (fun w : Circle => ‖c+q*(w:ℂ)‖)).card≤4*m := by
  classical
  have hnorm : (Complex.normSq p:ℂ)≠(Complex.normSq q:ℂ) := by
    intro he
    have hh := Complex.ofReal_injective he
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hh
    exact hn (by nlinarith [norm_nonneg p,norm_nonneg q])
  apply coprime_laurent_points T H hT m hm hcop (c*starRingEnd ℂ p) (starRingEnd ℂ c*p)
    ((Complex.normSq p:ℂ)-(Complex.normSq q:ℂ)) (starRingEnd ℂ c*q) (c*starRingEnd ℂ q)
    (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hp)) (sub_ne_zero.mpr hnorm)
    (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) hq) (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hq))
    _ (Finset.filter_subset _ _)
  intro z hz
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hz).2
  refine ⟨w,hw,?_⟩
  have hh := congrArg (fun t : ℝ => ((t^2:ℝ):ℂ)) he
  rw [orbit_norm,orbit_norm] at hh
  linear_combination hh


lemma count_few_overlaps {ι α β : Type*} (I : Finset ι) (S : Finset α) (f : ι→α→β) (m : ℕ)
    [DecidableEq ι] [DecidableEq β]
    (hf : ∀ i∈I, ∀ W⊆S, W.card≤2*(W.image (f i)).card)
    (hc : ∀ i∈I, ∀ j∈I, i≠j → (S.filter fun x => f i x∈S.image (f j)).card≤4*m) :
    I.card*S.card+(2*m)*I.card≤2*(I.biUnion fun i => S.image (f i)).card+(2*m)*I.card*I.card := by
  classical
  let D (J : Finset ι) := J.biUnion fun i => S.image (f i)
  suffices hall : ∀ J⊆I, J.card*S.card+(2*m)*J.card≤2*(D J).card+(2*m)*J.card*J.card from hall I (Finset.Subset.refl _)
  intro J
  induction J using Finset.induction_on with
  | empty => simp [D]
  | @insert i J hi ih =>
    intro hJI
    have hiI := hJI (Finset.mem_insert_self _ _)
    have hJI' : J⊆I := (Finset.subset_insert _ _).trans hJI
    have ih' := ih hJI'
    let W := S.filter fun x => f i x∉D J
    let Q (j : ι) := S.filter fun x => f i x∈S.image (f j)
    have hsub : (S.filter fun x => f i x∈D J)⊆J.biUnion Q := by
      intro x hx
      obtain ⟨hx,hx'⟩ := Finset.mem_filter.mp hx
      obtain ⟨j,hj,hj'⟩ := Finset.mem_biUnion.mp hx'
      exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨hx,hj'⟩⟩
    have hbound : (J.biUnion Q).card≤J.card*(4*m) := by
      calc
        _ ≤ ∑ j∈J,(Q j).card := Finset.card_biUnion_le
        _ ≤ ∑ _∈J,(4*m) := Finset.sum_le_sum (fun j hj => hc i hiI j (hJI' hj) (fun h => hi (h ▸ hj)))
        _ = _ := by simp
    have hmatched := (Finset.card_le_card hsub).trans hbound
    have hrem := Finset.card_filter_add_card_filter_not (s:=S) (fun x => f i x∈D J)
    change (S.filter fun x => f i x∈D J).card+W.card=S.card at hrem
    have hf' := hf i hiI W (Finset.filter_subset _ _)
    have hd : Disjoint (W.image (f i)) (D J) := Finset.disjoint_left.mpr (by
      intro y hy hd
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2 hd)
    have hsub' : W.image (f i) ∪ D J ⊆ D (insert i J) := by
      change _ ⊆ (insert i J).biUnion _
      rw [Finset.biUnion_insert]
      exact Finset.union_subset_union_left (Finset.image_subset_image (Finset.filter_subset _ _))
    have hc' := Finset.card_le_card hsub'
    rw [Finset.card_union_of_disjoint hd] at hc'
    rw [Finset.card_insert_of_notMem hi]
    nlinarith


lemma regular_radial_bound (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (m : ℕ) (hm2 : 2 ≤ m) (hcop : m.Coprime T.card) (A P : Finset ℂ) (hPA : P⊆A) (hTA : ∀ z∈T, (z:ℂ)∈A)
    (hp : ∀ p∈P, p≠0 ∧ ‖p‖≠1) (hr : Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ)) :
    P.card*T.card+(2*m)*P.card≤2*distinctDistances A+(2*m)*P.card*P.card := by
  classical
  let f (p : ℂ) (z : Circle) := ‖(-1:ℂ)+p*(z:ℂ)‖
  have hsum := count_few_overlaps P T f m
    (fun p he W _ => orbit_image_size W (-1) p (by norm_num) (hp p he).1)
    (fun p hp' q hq hne => unconditional_orbit_intersection T H hT m hm2 hcop (-1) p q (by norm_num)
      (hp p hp').1 (hp q hq).1 (fun h => hne (hr hp' hq h)))
  have hs : (P.biUnion fun p => T.image (f p)) ⊆ distanceSet A := by
    intro r hr
    obtain ⟨p,hp',hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
    have hm (z : Circle) : z∈H ↔ z∈T := by change z∈(H:Set Circle) ↔ _; rw [hT]; rfl
    have hzA := hTA z⁻¹ ((hm _).mp (H.inv_mem ((hm _).mpr hz)))
    have hne : p≠(z⁻¹:Circle) := fun he => (hp p hp').2 (by rw [he,Circle.norm_coe])
    refine Finset.mem_image.mpr ⟨(p,((z⁻¹:Circle):ℂ)),Finset.mem_offDiag.mpr ⟨hPA hp',hzA,hne⟩,?_⟩
    change dist p ((z⁻¹:Circle):ℂ)=f p z
    rw [dist_eq_norm,Circle.coe_inv]
    have he : (-1:ℂ)+p*(z:ℂ)=(p-(z:ℂ)⁻¹)*(z:ℂ) := by field_simp [Circle.coe_ne_zero z]; ring
    dsimp only [f]
    rw [he,norm_mul,Circle.norm_coe,mul_one]
  have hb := Finset.card_le_card hs
  change P.card*T.card+(2*m)*P.card≤2*(distanceSet A).card+(2*m)*P.card*P.card
  omega



end Erdos1082GeneralCurve

namespace Erdos1082Uniform

lemma zero_poly_of_points {L : Type*} [Field L] (S : Finset L) (n : ℕ) (P : Polynomial L)
    (hsize : n<S.card) (hdeg : P.natDegree≤n) (hz : ∀ z∈S,P.eval z=0) : P=0 := by
  classical
  by_contra hn
  have hsub : S⊆P.roots.toFinset := fun z he => Multiset.mem_toFinset.mpr ((mem_roots hn).mpr (hz z he))
  have hh := (Finset.card_le_card hsub).trans <| (Multiset.toFinset_card_le _).trans <| (card_roots' P).trans hdeg
  omega

lemma linear_trace_rigidity {L : Type*} [Field L] [CharZero L] (S : Finset L) (hsz : 4<S.card)
    (u v k h U V K H : L) (hu : u≠0) (hv : v≠0) (hk : k≠0)
    (hs : ∀ z∈S, z≠0 ∧ ∃ w : L, w≠0 ∧ w+h/w=u/z+v*z+k ∧ w+H/w=U/z+V*z+K) :
    H=h ∧ U=u ∧ V=v ∧ K=k := by
  classical
  let a := U-u
  let b := V-v
  let c := K-k
  let δ := H-h
  have eqs (z : L) (hz : z∈S) : z≠0 ∧ ∃ w : L, w≠0 ∧ w+h/w=u/z+v*z+k ∧ a/z+b*z+c=δ/w := by
    obtain ⟨hz,w,hw,h₁,h₂⟩ := hs z hz
    refine ⟨hz,w,hw,h₁,?_⟩
    dsimp only [a,b,c,δ]; linear_combination h₁ - h₂
  by_cases hd : δ=0
  · let P : Polynomial L := C a+C c*X+C b*X^2
    have hp := zero_poly_of_points S 2 P (by omega) (by dsimp [P]; compute_degree) (by
      intro z hz
      obtain ⟨hz,w,hw,_,he⟩ := eqs z hz
      rw [hd,zero_div] at he
      simp only [P,eval_add,eval_C,eval_mul,eval_X,eval_pow]
      field_simp [hz] at he
      linear_combination he)
    have h₀ := congrArg (fun Q : Polynomial L => Q.coeff 0) hp
    have h₁ := congrArg (fun Q : Polynomial L => Q.coeff 1) hp
    have h₂ := congrArg (fun Q : Polynomial L => Q.coeff 2) hp
    simp only [P,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C,coeff_zero] at h₀ h₁ h₂
    norm_num at h₀ h₁ h₂
    exact ⟨sub_eq_zero.mp hd,sub_eq_zero.mp h₀,sub_eq_zero.mp h₂,sub_eq_zero.mp h₁⟩
  let A := δ*u-h*a
  let B := δ*v-h*b
  let Cc := δ*k-h*c
  let Q : Polynomial L := C (a*A)+C (a*Cc+c*A)*X+C (a*B+b*A+c*Cc-δ^2)*X^2+
    C (b*Cc+c*B)*X^3+C (b*B)*X^4
  have hQ := zero_poly_of_points S 4 Q hsz (by dsimp [Q]; compute_degree) (by
    intro z hz
    obtain ⟨hz,w,hw,he,hdw⟩ := eqs z hz
    have other : A/z+B*z+Cc=δ*w := by
      calc
        _=δ*(u/z+v*z+k)-h*(a/z+b*z+c) := by dsimp only [A,B,Cc] <;> ring
        _=_ := by rw [←he,hdw] <;> ring
    have prod : (a/z+b*z+c)*(A/z+B*z+Cc)=δ^2 := by rw [hdw,other]; field_simp [hw] <;> ring
    simp only [Q,eval_add,eval_mul,eval_C,eval_X,eval_pow]
    field_simp [hz] at prod
    linear_combination prod)
  have e₀ := congrArg (fun Q : Polynomial L => Q.coeff 0) hQ
  have e₁ := congrArg (fun Q : Polynomial L => Q.coeff 1) hQ
  have e₂ := congrArg (fun Q : Polynomial L => Q.coeff 2) hQ
  have e₃ := congrArg (fun Q : Polynomial L => Q.coeff 3) hQ
  have e₄ := congrArg (fun Q : Polynomial L => Q.coeff 4) hQ
  simp only [Q,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C,coeff_zero] at e₀ e₁ e₂ e₃ e₄
  norm_num at e₀ e₁ e₂ e₃ e₄
  have neq (x y z : L) (hx : x≠0) (he : z=δ*x-h*y) : z+h*y≠0 := by rw [he]; simpa using mul_ne_zero hd hx
  have ha := neq u a A hu rfl
  have hb := neq v b B hv rfl
  have hcc := neq k c Cc hk rfl
  have splitrow (a A c Cc : L) (zero : a*A=0) (lin : a*Cc+c*A=0) (hn : A+h*a≠0) :
      (a=0 ∧ c=0) ∨ (A=0 ∧ Cc=0) := by
    rcases mul_eq_zero.mp zero with ha|hA
    · left
      have hA' : A≠0 := by simpa [ha] using hn
      have hc : c*A=0 := by simpa [ha] using lin
      exact ⟨ha,(mul_eq_zero.mp hc).resolve_right hA'⟩
    · right
      have ha' : a≠0 := fun he => hn (by simp [hA,he])
      have hc : a*Cc=0 := by simpa [hA] using lin
      exact ⟨hA,(mul_eq_zero.mp hc).resolve_left ha'⟩
  exfalso
  rcases splitrow a A c Cc (mul_eq_zero.mpr e₀) e₁ ha with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;>
    rcases splitrow b B c Cc (mul_eq_zero.mpr e₄) e₃ hb with ⟨h₃,h₄⟩|⟨h₃,h₄⟩ <;>
    simp_all [h₁,h₂,h₃,h₄]


lemma projected_nonzero_relation {ι : Type*} [Fintype ι] (K : IntermediateField ℚ ℂ) (z w : ι→K)
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (hnzw : ∀ i, z i≠0 ∧ w i≠0)
    (he : ∀ i, c*(w i:ℂ)+d/(w i:ℂ)=a/(z i:ℂ)+b*(z i:ℂ)+k)
    (hgood : ∀ i, a/(z i:ℂ)+b*(z i:ℂ)≠0 ∧ a/(z i:ℂ)+b*(z i:ℂ)+k≠0) :
    ∃ u v κ h : K, u≠0 ∧ v≠0 ∧ κ≠0 ∧ h≠0 ∧ ∀ i,
      w i+h/w i=u/z i+v*z i+κ ∧ u/z i+v*z i≠0 ∧ u/z i+v*z i+κ≠0 := by
  classical
  let X (i : ι) := a/(z i:ℂ)+b*(z i:ℂ)
  let M : Finset ℂ := ({a,b,k,c,d} ∪ Finset.univ.image X ∪ Finset.univ.image (fun i => X i+k)).erase 0
  obtain ⟨F,hF⟩ := Module.exists_dual_forall_apply_ne_zero (K:=K) (fun x : M => x.1)
    (fun x => (Finset.mem_erase.mp x.2).1)
  have hfa : F a≠0 := hF ⟨a,by simp [M,ha]⟩
  have hfb : F b≠0 := hF ⟨b,by simp [M,hb]⟩
  have hfk : F k≠0 := hF ⟨k,by simp [M,hk]⟩
  have hfc : F c≠0 := hF ⟨c,by simp [M,hc]⟩
  have hfd : F d≠0 := hF ⟨d,by simp [M,hd]⟩
  let u := F a/F c
  let v := F b/F c
  let κ := F k/F c
  let h := F d/F c
  refine ⟨u,v,κ,h,div_ne_zero hfa hfc,div_ne_zero hfb hfc,div_ne_zero hfk hfc,div_ne_zero hfd hfc,?_⟩
  intro i
  obtain ⟨hz,hw⟩ := hnzw i
  have hfx : F (X i)≠0 := hF ⟨X i,Finset.mem_erase.mpr ⟨(hgood i).1,
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem X (Finset.mem_univ i)))⟩⟩
  have hfy : F (X i+k)≠0 := hF ⟨X i+k,Finset.mem_erase.mpr ⟨(hgood i).2,
    Finset.mem_union_right _ (Finset.mem_image_of_mem (fun j => X j+k) (Finset.mem_univ i))⟩⟩
  have heX : X i = (z i)⁻¹ • a + z i • b := by
    change a/(z i:ℂ)+b*(z i:ℂ)=(z i:ℂ)⁻¹*a+(z i:ℂ)*b
    simp only [div_eq_mul_inv,mul_comm]
  have hlin : F (X i) = F c*(u/z i+v*z i) := by
    rw [heX,map_add,LinearMap.map_smul,LinearMap.map_smul,smul_eq_mul,smul_eq_mul]
    dsimp only [u,v]
    field_simp [hfc,hz] <;> ring
  have hlin' : F (X i+k)=F c*(u/z i+v*z i+κ) := by
    rw [map_add,hlin]
    dsimp only [κ]; field_simp [hfc] <;> ring
  have heY : X i+k = w i • c+(w i)⁻¹ • d := by
    change a/(z i:ℂ)+b*(z i:ℂ)+k=(w i:ℂ)*c+(w i:ℂ)⁻¹*d
    simpa only [div_eq_mul_inv,mul_comm] using (he i).symm
  have hrel : w i+h/w i=u/z i+v*z i+κ := by
    apply (mul_right_inj' hfc).mp
    rw [←hlin',heY,map_add,LinearMap.map_smul,LinearMap.map_smul,smul_eq_mul,smul_eq_mul]
    dsimp only [h]; field_simp [hfc,hw] <;> ring
  exact ⟨hrel,fun e => hfx (by rw [hlin,e,mul_zero]),fun e => hfy (by rw [hlin',e,mul_zero])⟩


lemma signed_conjugate {L : Type*} [Field L] (σ : L→+*L) (z w u v k h e f : L) (m : ℕ)
    (he : e=1 ∨ e= -1) (hf : f=1 ∨ f= -1) (hz : σ z=e*z^m) (hw : σ w=f*w^m)
    (hrel : w+h/w=u/z+v*z+k) :
    w^m+σ h/w^m=(f*e*σ u)/z^m+(f*e*σ v)*z^m+f*σ k := by
  have hh := congrArg σ hrel
  simp only [map_add,map_mul,map_div₀,hz,hw] at hh
  rcases he with rfl|rfl <;> rcases hf with rfl|rfl <;> simp at hh ⊢ <;>
    first | linear_combination hh | linear_combination -hh

lemma unique_sign_pattern {L : Type*} [Field L] [CharZero L] (b d : Bool×Bool)
    (x k y K : L) (hx : x≠0) (hy : x+k≠0) (hk : k≠0)
    (h₁ : x=(if b.2 then 1 else -1)*(if b.1 then 1 else -1)*y)
    (h₂ : k=(if b.2 then 1 else -1)*K)
    (h₃ : x+k=(if d.2 then 1 else -1)*(if d.1 then 1 else -1)*y+(if d.2 then 1 else -1)*K) : b=d := by
  rcases b with ⟨b,c⟩
  rcases d with ⟨d,e⟩
  cases b <;> cases c <;> cases d <;> cases e <;> first | rfl | skip
  all_goals
    exfalso
    simp only [Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul,mul_one,neg_neg,neg_mul,mul_neg] at h₁ h₂ h₃
    subst x
    subst k
    first
    | apply hx; linear_combination (1/2)*h₃
    | apply hx; linear_combination -(1/2)*h₃
    | apply hy; linear_combination (1/2)*h₃
    | apply hy; linear_combination -(1/2)*h₃
    | apply hk; linear_combination (1/2)*h₃
    | apply hk; linear_combination -(1/2)*h₃

lemma projected_data {ι : Type*} [Fintype ι] (n r : ℕ) [NeZero n] (hcop : r.Coprime n)
    (z w : ι→ℂ) (iz : Function.Injective z) (hz : ∀ i, (z i)^n=1) (hw : ∀ i,(w i)^n=1)
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (he : ∀ i, c*w i+d/w i=a/z i+b*z i+k)
    (hg : ∀ i, a/z i+b*z i≠0 ∧ a/z i+b*z i+k≠0) :
    ∃ (K : IntermediateField ℚ ℂ) (σ : K→+*K) (Z W : ι→K) (U V C D : K),
      Function.Injective Z ∧ U≠0 ∧ V≠0 ∧ C≠0 ∧ D≠0 ∧ ∀ i,
        (Z i:ℂ)=z i ∧ (W i:ℂ)=w i ∧ Z i≠0 ∧ W i≠0 ∧ Z i^n=1 ∧ W i^n=1 ∧
        σ (Z i)=(Z i)^r ∧ σ (W i)=(W i)^r ∧
        W i+D/W i=U/Z i+V*Z i+C ∧ U/Z i+V*Z i≠0 ∧ U/Z i+V*Z i+C≠0 := by
  classical
  obtain ⟨K,hK,σ,hσ⟩ := automorphism_on_roots n r hcop
  let Z (i : ι) : K := ⟨z i,hK _ (hz i)⟩
  let W (i : ι) : K := ⟨w i,hK _ (hw i)⟩
  have zroot (i : ι) : Z i^n=1 := Subtype.ext (hz i)
  have wroot (i : ι) : W i^n=1 := Subtype.ext (hw i)
  have hzw (i : ι) : Z i≠0 ∧ W i≠0 := by
    refine ⟨fun he => ?_,fun he => ?_⟩
    · have hh := zroot i; simp [he,NeZero.ne n] at hh
    · have hh := wroot i; simp [he,NeZero.ne n] at hh
  obtain ⟨U,V,C,D,hU,hV,hC,hD,hs⟩ := projected_nonzero_relation K Z W a b k c d ha hb hk hc hd hzw he hg
  refine ⟨K,σ,Z,W,U,V,C,D,(fun _ _ h => iz (congrArg ((↑):K→ℂ) h)),hU,hV,hC,hD,?_⟩
  intro i
  exact ⟨rfl,rfl,(hzw i).1,(hzw i).2,zroot i,wroot i,hσ _ (zroot i),hσ _ (wroot i),hs i⟩


set_option maxHeartbeats 2400000 in
lemma nonexceptional_torsion {ι : Type*} [Fintype ι] (n : ℕ) (hn : 0<n)
    (z w : ι→ℂ) (iz : Function.Injective z) (hz : ∀ i,z i^n=1) (hw : ∀ i,w i^n=1)
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (he : ∀ i,c*w i+d/w i=a/z i+b*z i+k) (hg : ∀ i,a/z i+b*z i≠0 ∧ a/z i+b*z i+k≠0) :
    Fintype.card ι≤32 := by
  classical
  induction n using Nat.strong_induction_on generalizing z w a b k c d with
  | h n ih =>
    by_contra! hbig
    let : NeZero n := ⟨by omega⟩
    by_cases heven : Even n
    · obtain ⟨m,hm⟩ := heven
      have hn2 : n=2*m := by omega
      let r := if Even m then 1 else 2
      have hcop : (m+r).Coprime n := by
        rw [hn2,Nat.coprime_mul_iff_right]
        by_cases hme : Even m
        · rw [show r=1 by simp [r,hme]]
          constructor
          · rw [Nat.coprime_two_right]; obtain ⟨j,hj⟩ := hme; exact ⟨j,by omega⟩
          · rw [Nat.add_comm,Nat.coprime_add_self_left]; simp
        · rw [show r=2 by simp [r,hme]]
          have ho : Odd m := Nat.not_even_iff_odd.mp hme
          constructor
          · rw [Nat.coprime_two_right]; obtain ⟨j,hj⟩ := ho; exact ⟨j+1,by omega⟩
          · rw [Nat.add_comm,Nat.coprime_add_self_left,Nat.coprime_two_left]; exact ho
      obtain ⟨K,σ,Z,W,U,V,C,D,iZ,hU,hV,hC,hD,data⟩ := projected_data n (m+r) hcop z w iz hz hw a b k c d ha hb hk hc hd he hg
      let eps (b : Bool) : K := if b then 1 else -1
      let cls (i : ι) := (decide (Z i^m=1),decide (W i^m=1))
      have epssign (b : Bool) : eps b=1 ∨ eps b= -1 := by cases b <;> simp [eps]
      have power (x : K) (hx : x^n=1) : x^m=eps (decide (x^m=1)) := by
        have hh : (x^m)^2=1 := by rwa [←pow_mul,Nat.mul_comm,←hn2]
        rcases sq_eq_one_iff.mp hh with he|he <;> simp [he,eps]
      have eqZ (i : ι) : Z i^m=eps (cls i).1 := power _ (data i).2.2.2.2.1
      have eqW (i : ι) : W i^m=eps (cls i).2 := power _ (data i).2.2.2.2.2.1
      have signrel (i : ι) : W i^r+σ D/W i^r =
          (eps (cls i).2*eps (cls i).1*σ U)/Z i^r+(eps (cls i).2*eps (cls i).1*σ V)*Z i^r+eps (cls i).2*σ C := by
        obtain ⟨_,_,_,_,_,_,hσz,hσw,hrel,_,_⟩ := data i
        apply signed_conjugate σ _ _ _ _ _ _ _ _ _ (epssign _) (epssign _) _ _ hrel
        · rw [hσz,pow_add,eqZ]
        · rw [hσw,pow_add,eqW]
      obtain ⟨B,_,hB⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s:=Finset.univ) (fun i (_ : i∈(Finset.univ:Finset ι)) => Finset.mem_univ (cls i))
        (show (Finset.univ:Finset (Bool×Bool)).card*8<(Finset.univ:Finset ι).card by simpa using hbig)
      let I := Finset.univ.filter (fun i => cls i=B)
      let S := I.image Z
      have hsize : 8<S.card := by simpa [S,I,Finset.card_image_of_injective _ iZ] using hB
      let U' := eps B.2*eps B.1*σ U
      let V' := eps B.2*eps B.1*σ V
      let C' := eps B.2*σ C
      have hmatches (x : K) (hx : x∈S) : x≠0 ∧ ∃ y : K, y≠0 ∧ y+D/y=U/x+V*x+C ∧ y^r+σ D/y^r=U'/x^r+V'*x^r+C' := by
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨_,_,hz',hw',_,_,_,_,hh,_,_⟩ := data i
        exact ⟨hz',W i,hw',hh,by simpa only [U',V',C',(Finset.mem_filter.mp hi).2] using signrel i⟩
      by_cases hme : Even m
      · have hr : r=1 := by simp [r,hme]
        have hrig := linear_trace_rigidity S (by omega) U V C D U' V' C' (σ D) hU hV hC
          (fun x hx => by simpa [hr] using hmatches x hx)
        obtain ⟨hD',hU',hV',hC'⟩ := hrig
        have hclass (i : ι) : B=cls i := by
          obtain ⟨_,_,_,_,_,_,_,_,hrel,hx,hy⟩ := data i
          let X := U/Z i+V*Z i
          let Y := (σ U)/Z i+(σ V)*Z i
          apply unique_sign_pattern B (cls i) X C Y (σ C) hx hy hC
          · change U/Z i+V*Z i=eps B.2*eps B.1*((σ U)/Z i+(σ V)*Z i)
            calc
              _=U'/Z i+V'*Z i := by rw [hU',hV']
              _=_ := by dsimp only [U',V']; ring
          · exact hC'.symm
          · change X+C=eps (cls i).2*eps (cls i).1*Y+eps (cls i).2*σ C
            dsimp only [X,Y]
            have hh := signrel i
            rw [hr,pow_one,pow_one,hD',hrel] at hh
            linear_combination hh
        obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (show 0<Fintype.card ι by omega)
        have cz (i : ι) : z i^m=z i₀^m := by
          have hh := (eqZ i).trans ((congrArg (fun b : Bool×Bool => eps b.1) ((hclass i).symm.trans (hclass i₀))).trans (eqZ i₀).symm)
          simpa only [IntermediateField.coe_pow,(data i).1,(data i₀).1] using congrArg ((↑):K→ℂ) hh
        have cw (i : ι) : w i^m=w i₀^m := by
          have hh := (eqW i).trans ((congrArg (fun b : Bool×Bool => eps b.2) ((hclass i).symm.trans (hclass i₀))).trans (eqW i₀).symm)
          simpa only [IntermediateField.coe_pow,(data i).2.1,(data i₀).2.1] using congrArg ((↑):K→ℂ) hh
        have zne (i : ι) : z i≠0 := by intro hh; have h := hz i; simp [hh,NeZero.ne n] at h
        have wne (i : ι) : w i≠0 := by intro hh; have h := hw i; simp [hh,NeZero.ne n] at h
        let z' (i : ι) := z i/z i₀
        let w' (i : ι) := w i/w i₀
        have hx (i : ι) : (a/z i₀)/z' i+(b*z i₀)*z' i=a/z i+b*z i := by
          dsimp only [z']; field_simp [zne i,zne i₀] <;> ring
        have hy (i : ι) : (c*w i₀)*w' i+(d/w i₀)/w' i=c*w i+d/w i := by
          dsimp only [w']; field_simp [wne i,wne i₀] <;> ring
        apply (not_lt_of_ge (ih m (by omega) (by omega) z' w'
          (fun _ _ h => iz ((div_left_inj' (zne i₀)).mp h))
          (fun i => by dsimp only [z']; rw [div_pow,cz i,div_self (pow_ne_zero _ (zne i₀))])
          (fun i => by dsimp only [w']; rw [div_pow,cw i,div_self (pow_ne_zero _ (wne i₀))])
          (a/z i₀) (b*z i₀) k (c*w i₀) (d/w i₀) (div_ne_zero ha (zne i₀)) (mul_ne_zero hb (zne i₀))
          hk (mul_ne_zero hc (wne i₀)) (div_ne_zero hd (wne i₀))
          (fun i => by rw [hx,hy,he]) (fun i => by rw [hx]; exact hg i))) hbig
      · have hr : r=2 := by simp [r,hme]
        have hbound := Erdos1082GeneralCurve.power_trace_bound S 2 (by decide) U V C D U' V' C' (σ D)
          hU hC hD ((_root_.map_ne_zero _).mpr hD) (fun x hx => by simpa [hr] using hmatches x hx)
        omega
    · have hcop := (Nat.not_even_iff_odd.mp heven).coprime_two_left
      obtain ⟨K,σ,Z,W,U,V,C,D,iZ,hU,hV,hC,hD,data⟩ := projected_data n 2 hcop z w iz hz hw a b k c d ha hb hk hc hd he hg
      let S := Finset.univ.image Z
      have hsize : S.card=Fintype.card ι := by simp [S,Finset.card_image_of_injective _ iZ]
      have hbound := Erdos1082GeneralCurve.power_trace_bound S 2 (by decide) U V C D (σ U) (σ V) (σ C) (σ D)
        hU hC hD ((_root_.map_ne_zero _).mpr hD) (by
          intro x hx
          obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨_,_,hz,hw,_,_,hσz,hσw,he,_,_⟩ := data i
          exact ⟨hz,W i,hw,he,by simpa only [map_add,map_div₀,map_mul,hσz,hσw] using congrArg σ he⟩)
      omega


lemma all_torsion_points (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (a b k c d : ℂ) (ha : a≠0) (hb : b≠0) (hk : k≠0) (hc : c≠0) (hd : d≠0)
    (S : Finset Circle) (hST : S⊆T) (hm : ∀ z∈S,∃ w∈T,c*(w:ℂ)+d/(w:ℂ)=a/(z:ℂ)+b*(z:ℂ)+k) :
    S.card≤36 := by
  classical
  by_cases hn : T.card=0
  · have := Finset.card_le_card hST; omega
  let X (z : Circle) := a/(z:ℂ)+b*(z:ℂ)
  let F (r : ℂ) := S.filter fun z => X z=r
  have few (r : ℂ) : (F r).card≤2 := by
    let P : Polynomial ℂ := C a-C r*Polynomial.X+C b*Polynomial.X^2
    have hp : P≠0 := by intro he; have h := congrArg (fun Q : Polynomial ℂ => Q.coeff 0) he; simpa [P,mul_coeff_zero,ha] using h
    have deg : P.natDegree≤2 := by dsimp [P]; compute_degree
    let J := (F r).image (fun z : Circle => (z:ℂ))
    have hsub : J⊆P.roots.toFinset := by
      intro z hz
      obtain ⟨z,hzF,rfl⟩ := Finset.mem_image.mp hz
      have he := (Finset.mem_filter.mp hzF).2
      change a/(z:ℂ)+b*(z:ℂ)=r at he
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots hp).mpr
      change P.eval (z:ℂ)=0
      simp only [P,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow]
      field_simp [Circle.coe_ne_zero z] at he
      linear_combination he
    have hj := (Finset.card_le_card hsub).trans <| (Multiset.toFinset_card_le _).trans <| (card_roots' P).trans deg
    have hi : Function.Injective (fun z : Circle => (z:ℂ)) := Circle.coe_injective
    have hcard : J.card=(F r).card := Finset.card_image_of_injective (F r) hi
    exact (le_of_eq hcard.symm).trans hj
  let G := S.filter fun z => X z≠0 ∧ X z+k≠0
  have hsub : S⊆G∪F 0∪F (-k) := by
    intro z hz
    by_cases h : X z=0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,h⟩))
    by_cases h' : X z+k=0
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,eq_neg_of_add_eq_zero_left h'⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,h,h'⟩))
  have wit (j : G) := hm j.1 (Finset.mem_filter.mp j.2).1
  let w (j : G) := (wit j).choose
  have hG := nonexceptional_torsion T.card (by omega) (fun j : G => (j.1:ℂ)) (fun j => (w j:ℂ))
    (fun _ _ he => Subtype.ext (Circle.coe_injective he)) (fun j => finite_subgroup_root _ _ hT _ (hST (Finset.mem_filter.mp j.2).1))
    (fun j => finite_subgroup_root _ _ hT _ (wit j).choose_spec.1) a b k c d ha hb hk hc hd
    (fun j => (wit j).choose_spec.2) (fun j => (Finset.mem_filter.mp j.2).2)
  rw [Fintype.card_coe] at hG
  have h := Finset.card_le_card hsub
  have := Finset.card_union_le (G∪F 0) (F (-k))
  have := Finset.card_union_le G (F 0)
  have := few 0; have := few (-k); omega


lemma orbit_norm (c p : ℂ) (z : Circle) :
    ((‖c+p*(z:ℂ)‖^2:ℝ):ℂ) = (Complex.normSq c:ℂ)+(Complex.normSq p:ℂ)+
        (starRingEnd ℂ c*p)*(z:ℂ)+(c*starRingEnd ℂ p)/(z:ℂ) := by
  rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self,
    map_add,map_mul,←Circle.coe_inv_eq_conj,Circle.coe_inv]
  field_simp [Circle.coe_ne_zero z]
  ring


lemma orbit_fiber_card (T : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) (r : ℝ) :
    (T.filter fun z : Circle => ‖c+p*(z:ℂ)‖=r).card ≤ 2 := by
  classical
  let q := -c/p
  apply (Finset.card_le_card (t := T.filter fun z : Circle => dist q (z:ℂ)=r/‖p‖) ?_).trans
    (circle_fibers T q (div_ne_zero (neg_ne_zero.mpr hc) hp) _)
  intro z hz
  obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨hz,?_⟩
  have heq : q-(z:ℂ) = -(c+p*(z:ℂ))/p := by dsimp [q]; field_simp; ring
  rw [dist_eq_norm,heq,norm_div,norm_neg,he]

lemma orbit_image_size (S : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) :
    S.card ≤ 2*(S.image fun z : Circle => ‖c+p*(z:ℂ)‖).card := by
  classical
  by_contra! h
  obtain ⟨r,_,hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun z (hz : z∈S) => Finset.mem_image_of_mem (fun z : Circle => ‖c+p*(z:ℂ)‖) hz)
    (show (S.image fun z : Circle => ‖c+p*(z:ℂ)‖).card*2<S.card by omega)
  exact (not_lt_of_ge (orbit_fiber_card S c p hc hp r)) hr



lemma uniform_orbit_intersection (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (c p q : ℂ) (hc : c≠0) (hp : p≠0) (hq : q≠0) (hn : ‖p‖≠‖q‖) :
    (T.filter fun z : Circle => ‖c+p*(z:ℂ)‖∈T.image (fun w : Circle => ‖c+q*(w:ℂ)‖)).card≤36 := by
  classical
  have hnorm : (Complex.normSq p:ℂ)≠(Complex.normSq q:ℂ) := by
    intro he
    have hh := Complex.ofReal_injective he
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hh
    exact hn (by nlinarith [norm_nonneg p,norm_nonneg q])
  apply all_torsion_points T H hT (c*starRingEnd ℂ p) (starRingEnd ℂ c*p)
    ((Complex.normSq p:ℂ)-(Complex.normSq q:ℂ)) (starRingEnd ℂ c*q) (c*starRingEnd ℂ q)
    (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hp)) (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) hp) (sub_ne_zero.mpr hnorm)
    (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) hq) (mul_ne_zero hc ((_root_.map_ne_zero _).mpr hq))
    _ (Finset.filter_subset _ _)
  intro z hz
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hz).2
  refine ⟨w,hw,?_⟩
  have hh := congrArg (fun t : ℝ => ((t^2:ℝ):ℂ)) he
  rw [orbit_norm,orbit_norm] at hh
  linear_combination hh


lemma uniform_regular_radial_bound (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (A P : Finset ℂ) (hPA : P⊆A) (hTA : ∀ z∈T, (z:ℂ)∈A)
    (hp : ∀ p∈P, p≠0 ∧ ‖p‖≠1) (hr : Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ)) :
    P.card*T.card+18*P.card≤2*distinctDistances A+18*P.card*P.card := by
  classical
  let f (p : ℂ) (z : Circle) := ‖(-1:ℂ)+p*(z:ℂ)‖
  have hsum := Erdos1082GeneralCurve.count_few_overlaps P T f 9
    (fun p he W _ => orbit_image_size W (-1) p (by norm_num) (hp p he).1)
    (fun p hp' q hq hne => uniform_orbit_intersection T H hT (-1) p q (by norm_num)
      (hp p hp').1 (hp q hq).1 (fun h => hne (hr hp' hq h)))
  have hs : (P.biUnion fun p => T.image (f p)) ⊆ distanceSet A := by
    intro r hr
    obtain ⟨p,hp',hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
    have hm (z : Circle) : z∈H ↔ z∈T := by change z∈(H:Set Circle) ↔ _; rw [hT]; rfl
    have hzA := hTA z⁻¹ ((hm _).mp (H.inv_mem ((hm _).mpr hz)))
    have hne : p≠(z⁻¹:Circle) := fun he => (hp p hp').2 (by rw [he,Circle.norm_coe])
    refine Finset.mem_image.mpr ⟨(p,((z⁻¹:Circle):ℂ)),Finset.mem_offDiag.mpr ⟨hPA hp',hzA,hne⟩,?_⟩
    change dist p ((z⁻¹:Circle):ℂ)=f p z
    rw [dist_eq_norm,Circle.coe_inv]
    have he : (-1:ℂ)+p*(z:ℂ)=(p-(z:ℂ)⁻¹)*(z:ℂ) := by field_simp [Circle.coe_ne_zero z]; ring
    dsimp only [f]
    rw [he,norm_mul,Circle.norm_coe,mul_one]
  have hb := Finset.card_le_card hs
  change P.card*T.card+18*P.card≤2*(distanceSet A).card+18*P.card*P.card
  norm_num at hsum
  omega


lemma bounded_regular_radial (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (m : ℕ) (hm2 : 2 ≤ m) (hcop : m.Coprime T.card) (A P : Finset ℂ) (hPA : P⊆A) (hTA : ∀ z∈T, (z:ℂ)∈A)
    (hp : ∀ p∈P, p≠0 ∧ ‖p‖≠1) (hr : Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ)) :
    P.card*T.card+(2*min m 9)*P.card≤2*distinctDistances A+(2*min m 9)*P.card*P.card := by
  classical
  let f (p : ℂ) (z : Circle) := ‖(-1:ℂ)+p*(z:ℂ)‖
  have hsum := Erdos1082GeneralCurve.count_few_overlaps P T f (min m 9)
    (fun p he W _ => orbit_image_size W (-1) p (by norm_num) (hp p he).1)
    (fun p hp' q hq hne => by
      have h₁ := Erdos1082GeneralCurve.unconditional_orbit_intersection T H hT m hm2 hcop (-1) p q (by norm_num)
        (hp p hp').1 (hp q hq).1 (fun h => hne (hr hp' hq h))
      have h₂ := uniform_orbit_intersection T H hT (-1) p q (by norm_num)
        (hp p hp').1 (hp q hq).1 (fun h => hne (hr hp' hq h))
      change (T.filter fun z => f p z∈T.image (f q)).card≤4*m at h₁
      change (T.filter fun z => f p z∈T.image (f q)).card≤36 at h₂
      omega)
  have hs : (P.biUnion fun p => T.image (f p)) ⊆ distanceSet A := by
    intro r hr
    obtain ⟨p,hp',hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
    have hm (z : Circle) : z∈H ↔ z∈T := by change z∈(H:Set Circle) ↔ _; rw [hT]; rfl
    have hzA := hTA z⁻¹ ((hm _).mp (H.inv_mem ((hm _).mpr hz)))
    have hne : p≠(z⁻¹:Circle) := fun he => (hp p hp').2 (by rw [he,Circle.norm_coe])
    refine Finset.mem_image.mpr ⟨(p,((z⁻¹:Circle):ℂ)),Finset.mem_offDiag.mpr ⟨hPA hp',hzA,hne⟩,?_⟩
    change dist p ((z⁻¹:Circle):ℂ)=f p z
    rw [dist_eq_norm,Circle.coe_inv]
    have he : (-1:ℂ)+p*(z:ℂ)=(p-(z:ℂ)⁻¹)*(z:ℂ) := by field_simp [Circle.coe_ne_zero z]; ring
    dsimp only [f]
    rw [he,norm_mul,Circle.norm_coe,mul_one]
  have hb := Finset.card_le_card hs
  change P.card*T.card+(2*min m 9)*P.card≤2*(distanceSet A).card+(2*min m 9)*P.card*P.card
  omega


lemma second_circle_selection (U : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) (k : ℕ)
    (hsize : 2*k+3≤U.card) :
    ∃ P⊆U.image (fun z : Circle => c+p*(z:ℂ)), P.card=k ∧ (∀ q∈P,q≠0 ∧ ‖q‖≠1) ∧
      Set.InjOn (fun q : ℂ => ‖q‖) (P:Set ℂ) := by
  classical
  let g (z : Circle) := c+p*(z:ℂ)
  let B := U.filter fun z => g z≠0 ∧ ‖g z‖≠1
  let D := B.image (fun z => ‖g z‖)
  have hsub : U ⊆ B ∪ U.filter (fun z => ‖g z‖=0) ∪ U.filter (fun z => ‖g z‖=1) := by
    intro z hz
    by_cases he : g z=0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,by simp [he]⟩))
    by_cases hn : ‖g z‖=1
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,hn⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,he,hn⟩))
  have hB : U.card≤B.card+4 := by
    have := Finset.card_le_card hsub
    have := Finset.card_union_le (B ∪ U.filter (fun z => ‖g z‖=0)) (U.filter (fun z => ‖g z‖=1))
    have := Finset.card_union_le B (U.filter (fun z => ‖g z‖=0))
    have h₀ := orbit_fiber_card U c p hc hp 0
    have h₁ := orbit_fiber_card U c p hc hp 1
    change (U.filter fun z => ‖g z‖=0).card≤2 at h₀
    change (U.filter fun z => ‖g z‖=1).card≤2 at h₁
    omega
  have hD := orbit_image_size B c p hc hp
  change B.card≤2*D.card at hD
  obtain ⟨J,hJD,hJ⟩ := Finset.exists_subset_card_eq (show k≤D.card by omega)
  have hpre (r : J) : ∃ z∈B, ‖g z‖=r.1 := Finset.mem_image.mp (hJD r.2)
  let sel (r : J) := g ((hpre r).choose)
  have hnorm (r : J) : ‖sel r‖=r.1 := (hpre r).choose_spec.2
  have hin (r : J) := (hpre r).choose_spec.1
  let P := J.attach.image sel
  refine ⟨P,?_,?_,?_,?_⟩
  · rintro q h
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp (hin r)).1
  · dsimp only [P]
    rw [Finset.card_image_of_injective _ (fun r s he => Subtype.ext
      ((hnorm r).symm.trans ((congrArg norm he).trans (hnorm s)))),Finset.card_attach,hJ]
  · rintro q h
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp (hin r)).2
  · intro q hq s hs he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
    exact congrArg sel (Subtype.ext ((hnorm i).symm.trans (he.trans (hnorm j))))

lemma uniform_nonconcentric_radial_count (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (U : Finset Circle) (c p : ℂ) (hc : c≠0) (hp : p≠0) (k : ℕ) (hsize : 2*k+3≤U.card) :
    k*T.card+18*k≤2*distinctDistances (T.image (fun z : Circle => (z:ℂ)) ∪ U.image (fun z : Circle => c+p*(z:ℂ)))+18*k*k := by
  classical
  obtain ⟨P,hP,hcard,hgood,hinj⟩ := second_circle_selection U c p hc hp k hsize
  have hh := uniform_regular_radial_bound T H hT _ P (hP.trans (Finset.subset_union_right (s₁:=T.image (fun z : Circle => (z:ℂ))) ..))
    (fun z hz => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz)) hgood hinj
  simpa [hcard] using hh


lemma uniform_quadratic_distances (T : Finset Circle) (H : Subgroup Circle) (hT : (H:Set Circle)=T)
    (U : Finset Circle)
    (hsize : 2*(T.card/36)+5≤U.card) (c p : ℂ) (hc : c≠0) (hp : p≠0) :
    T.card^2+36*T.card≤144*distinctDistances
      (T.image (fun z : Circle => (z:ℂ)) ∪ U.image (fun z : Circle => c+p*(z:ℂ))) := by
  let t := T.card/36
  let r := T.card%36
  have hd := Nat.div_add_mod T.card 36
  change 36*t+r=T.card at hd
  have hr : r < 36 := Nat.mod_lt _ (by omega)
  have h := uniform_nonconcentric_radial_count T H hT U c p hc hp (t+1) (by dsimp [t]; omega)
  have hh := Nat.mul_le_mul_left 72 h
  rw [←hd] at hh ⊢
  have ha := Nat.mul_le_mul_left r (show r≤36 by omega)
  nlinarith

end Erdos1082Uniform

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.H3 := by
  intro T G hT m hm hcop A P
  exact Erdos1082Uniform.bounded_regular_radial T G hT m hm hcop A P
