import OMAStatements.S_mo_301126

/-!
Sihuang Hu posed the problem in https://mathoverflow.net/questions/301126.
River Li's partial answer (https://mathoverflow.net/a/333885, CC BY-SA 4.0)
reduced it to maximizing the cubic and bounded the number of distinct values
of an optimizer by four. The cubic-root perturbation below also applies to
a repeated upper value and to a lower endpoint. It yields an exact finite test.
-/

namespace OMA.S_mo_301126

private lemma triple {a b c u : ℝ} (hab : a < b) (hbc : b ≤ c) (hcu : c < u) :
    ∃ x y z : ℝ, a < x ∧ x < y ∧ y < z ∧ z < u ∧
      x+y+z = a+b+c ∧ x^2+y^2+z^2 = a^2+b^2+c^2 ∧
      a^3+b^3+c^3 < x^3+y^3+z^3 := by
  let h := (a+b)/2
  have hah : a < h := by dsimp [h]; linarith
  have hhb : h < b := by dsimp [h]; linarith
  let f := fun t : ℝ => (t-a)*(t-b)*(t-c)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have ha : f a = 0 := by simp [f]
  have hc : f c = 0 := by simp [f]
  have hfh : 0 < f h := by
    dsimp [f]
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (sub_pos.mpr hah) (sub_neg.mpr hhb))
      (sub_neg.mpr (hhb.trans_le hbc))
  have hfu : 0 < f u := by
    dsimp [f]
    exact mul_pos (mul_pos (sub_pos.mpr ((hab.trans_le hbc).trans hcu))
      (sub_pos.mpr (hbc.trans_lt hcu))) (sub_pos.mpr hcu)
  obtain ⟨e,he,he'⟩ := exists_between (lt_min hfh hfu)
  obtain ⟨x,⟨hax,hxh⟩,hx⟩ := intermediate_value_Ioo hah.le hf.continuousOn
    (show e ∈ Set.Ioo (f a) (f h) from ⟨ha ▸ he, he'.trans_le (min_le_left ..)⟩)
  obtain ⟨y,⟨hhy,hyc⟩,hy⟩ := intermediate_value_Ioo' (hhb.trans_le hbc).le hf.continuousOn
    (show e ∈ Set.Ioo (f c) (f h) from ⟨hc ▸ he, he'.trans_le (min_le_left ..)⟩)
  obtain ⟨z,⟨hcz,hzu⟩,hz⟩ := intermediate_value_Ioo hcu.le hf.continuousOn
    (show e ∈ Set.Ioo (f c) (f u) from ⟨hc ▸ he, he'.trans_le (min_le_right ..)⟩)
  let S := a+b+c
  let Q := a*b+a*c+b*c
  let T := a*b*c+e
  have root (t : ℝ) (ht : f t = e) : t^3-S*t^2+Q*t-T=0 := by
    dsimp [f] at ht
    dsimp [S,Q,T]
    linear_combination ht
  have diff (v w : ℝ) (hv : f v = e) (hw : f w = e) (hvw : v < w) :
      v^2+v*w+w^2-S*(v+w)+Q=0 := by
    apply (mul_eq_zero.mp (show (v-w)*(v^2+v*w+w^2-S*(v+w)+Q)=0 by
      linear_combination root v hv - root w hw)).resolve_left (sub_ne_zero.mpr hvw.ne)
  have hxy := hxh.trans hhy
  have hyz := hyc.trans hcz
  have dxy := diff x y hx hy hxy
  have dxz := diff x z hx hz (hxy.trans hyz)
  have hS : x+y+z=S := sub_eq_zero.mp <| (mul_eq_zero.mp
    (show (y-z)*(x+y+z-S)=0 by linear_combination dxy-dxz)).resolve_left (sub_ne_zero.mpr hyz.ne)
  have hQ : x*y+x*z+y*z=Q := by
    rw [← hS] at dxy
    linear_combination -dxy
  have hT : x*y*z=T := by
    have g := root x hx
    rw [← hS,← hQ] at g
    linear_combination g
  refine ⟨x,y,z,hax,hxy,hyz,hzu,hS,?_,?_⟩
  · dsimp [S,Q] at hS hQ
    linear_combination (x+y+z+(a+b+c))*hS - 2*hQ
  · have hcube : x^3+y^3+z^3 - (a^3+b^3+c^3)=3*e := by
      dsimp [S,Q,T] at hS hQ hT
      linear_combination ((x+y+z)^2+(x+y+z)*(a+b+c)+(a+b+c)^2-3*(x*y+x*z+y*z))*hS - 3*(a+b+c)*hQ + 3*hT
    linarith

end OMA.S_mo_301126
namespace OMA.S_mo_301126

private lemma sum_replace {m : ℕ} (f : ℝ → ℝ) (x : Fin m → ℝ) (i : Fin m) (v : ℝ) :
    (∑ j, f (Function.update x i v j)) = (∑ j, f (x j))-f (x i)+f v := by
  classical
  change ∑ j, (f ∘ Function.update x i v) j = _
  rw [Function.comp_update,Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have h := Finset.sum_erase_add Finset.univ (f ∘ x) (Finset.mem_univ i)
  dsimp only [Function.comp_apply] at *
  linarith

private lemma improved {m : ℕ} (x : Fin m → ℝ) (u : ℝ)
    (hx : ∀ i, x i ∈ Set.Icc 0 u) (i j k : Fin m) (hij : x i < x j)
    (hjk : x j ≤ x k) (hku : x k < u) (hne : j ≠ k) :
    ∃ w : Fin m → ℝ, (∀ i, w i ∈ Set.Icc 0 u) ∧
      (∑ i, w i) = ∑ i, x i ∧ (∑ i, (w i)^2) = ∑ i, (x i)^2 ∧
      (∑ i, (x i)^3) < ∑ i, (w i)^3 := by
  classical
  obtain ⟨a,b,c,ha,hab,hbc,hcu,hs,hq,ht⟩ := triple hij hjk hku
  have hji : j ≠ i := fun h => hij.ne (congrArg x h.symm)
  have hki : k ≠ i := fun h => (hij.trans_le hjk).ne (congrArg x h.symm)
  let w := Function.update (Function.update (Function.update x i a) j b) k c
  have sums (f : ℝ → ℝ) : (∑ t, f (w t)) =
      (∑ t, f (x t))-f (x i)-f (x j)-f (x k)+f a+f b+f c := by
    dsimp only [w]
    simp only [sum_replace,Function.update_of_ne hne.symm,Function.update_of_ne hki,
      Function.update_of_ne hji]
    ring
  refine ⟨w,?_,?_,?_,?_⟩
  · intro t
    by_cases htk : t=k
    · subst t
      simpa [w] using (show c ∈ Set.Icc 0 u from
        ⟨(hx i).1.trans (ha.trans (hab.trans hbc)).le,hcu.le⟩)
    by_cases htj : t=j
    · subst t
      simpa [w,htk] using (show b ∈ Set.Icc 0 u from
        ⟨(hx i).1.trans (ha.trans hab).le,(hbc.trans hcu).le⟩)
    by_cases hti : t=i
    · subst t
      simpa [w,htk,htj] using (show a ∈ Set.Icc 0 u from
        ⟨(hx i).1.trans ha.le,(hab.trans (hbc.trans hcu)).le⟩)
    simpa [w,htk,htj,hti] using hx t
  · have h := sums id
    simp only [id_eq] at h
    linarith
  · have h := sums (fun y => y^2)
    linarith
  · have h := sums (fun y => y^3)
    linarith

private lemma max_shape {m : ℕ} (hm : 0 < m) {u : ℝ} (input : Fin m → ℝ)
    (hi : ∀ i, input i ∈ Set.Icc 0 u) :
    ∃ (x : Fin m → ℝ) (s : ℝ) (j : Fin m), (∀ i, x i ∈ Set.Icc 0 u) ∧
      (∑ i, x i) = ∑ i, input i ∧ (∑ i, (x i)^2) = ∑ i, (input i)^2 ∧
      (∑ i, (input i)^3) ≤ ∑ i, (x i)^3 ∧ 0 ≤ s ∧ s ≤ x j ∧
      ∀ i, i ≠ j → x i = s ∨ x i = u := by
  classical
  let box := Set.Icc (0 : Fin m → ℝ) (fun _ => u)
  let K := box ∩ {x : Fin m → ℝ | ∑ i, x i = ∑ i, input i} ∩
    {x : Fin m → ℝ | ∑ i, (x i)^2 = ∑ i, (input i)^2}
  have inK : input ∈ K := ⟨⟨⟨fun i => (hi i).1,fun i => (hi i).2⟩,rfl⟩,rfl⟩
  have hcompact : IsCompact K := by
    apply (isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)).inter_right
    exact isClosed_eq (by fun_prop) continuous_const
  obtain ⟨x,hx,hmax⟩ := hcompact.exists_isMaxOn ⟨input,inK⟩
    (show ContinuousOn (fun x : Fin m → ℝ => ∑ i, (x i)^3) K by fun_prop)
  have hbox (i : Fin m) : x i ∈ Set.Icc 0 u := ⟨hx.1.1.1 i,hx.1.1.2 i⟩
  obtain ⟨i,_,hmin⟩ := Finset.univ.exists_min_image x
    ⟨(⟨0,hm⟩ : Fin m),Finset.mem_univ _⟩
  have hmi (t : Fin m) : x i ≤ x t := hmin t (Finset.mem_univ t)
  have unique (j k : Fin m) (hj : x i < x j ∧ x j < u) (hk : x i < x k ∧ x k < u) : j=k := by
    by_contra hne
    have ordered (a b : Fin m) (ha : x i < x a) (hab : x a ≤ x b) (hb : x b < u)
        (hne : a ≠ b) : False := by
      obtain ⟨w,hw,h1,h2,h3⟩ := improved x u hbox i a b ha hab hb hne
      have hwK : w ∈ K := ⟨⟨⟨fun t => (hw t).1,fun t => (hw t).2⟩,h1.trans hx.1.2⟩,h2.trans hx.2⟩
      exact h3.not_ge (hmax hwK)
    rcases le_total (x j) (x k) with h | h
    · exact ordered j k hj.1 h hk.2 hne
    · exact ordered k j hk.1 h hj.2 (Ne.symm hne)
  by_cases ex : ∃ j, x i < x j ∧ x j < u
  · obtain ⟨j,hj⟩ := ex
    refine ⟨x,x i,j,hbox,hx.1.2,hx.2,hmax inK,(hbox i).1,hmi j,?_⟩
    intro t ht
    by_contra! h
    exact ht (unique t j ⟨(hmi t).lt_of_ne h.1.symm,(hbox t).2.lt_of_ne h.2⟩ hj)
  · refine ⟨x,x i,i,hbox,hx.1.2,hx.2,hmax inK,(hbox i).1,le_rfl,?_⟩
    intro t _
    by_contra! h
    exact ex ⟨t,(hmi t).lt_of_ne h.1.symm,(hbox t).2.lt_of_ne h.2⟩

end OMA.S_mo_301126
namespace OMA.S_mo_301126

private lemma canonical {m r : ℕ} {s v u a₁ a₂ a₃ : ℝ} (hu : u = 1/4)
    (hs : 0 ≤ s) (hsv : s ≤ v) (hv : v ≤ u)
    (h1 : r*s+v+(m-1-r : ℕ)*u=a₁)
    (h2 : r*s^2+v^2+(m-1-r : ℕ)*u^2=a₂)
    (h3 : a₃ ≤ r*s^3+v^3+(m-1-r : ℕ)*u^3) : candidate m r a₁ a₂ a₃ := by
  subst u
  by_cases hr : r=0
  · subst r
    simp only [Nat.cast_zero,zero_mul,zero_add] at h1 h2 h3
    have e : a₁-(m-1-0 : ℕ)*(1/4:ℝ) = v := by linarith
    simp only [candidate,Nat.cast_zero,zero_add,mul_zero,zero_mul,add_zero,div_zero,
      Real.sqrt_zero,sub_zero,div_one,e]
    exact ⟨hs.trans hsv,le_rfl,hv,h1,h2,h3⟩
  have hr' : (r:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hp : (r:ℝ)+1 ≠ 0 := by positivity
  let z : ℝ := (m-1-r : ℕ)
  have ea : a₁-z*(1/4) = r*s+v := by dsimp [z]; linarith
  have eb : a₂-z*(1/4)^2 = r*s^2+v^2 := by dsimp [z]; linarith
  have ed : (((r+1:ℝ)*(r*s^2+v^2)-(r*s+v)^2)/r) = (v-s)^2 := by
    field_simp; ring
  have el : (r*s+v-(v-s))/(r+1)=s := (div_eq_iff hp).mpr (by ring)
  have ev : (r*s+v+r*(v-s))/(r+1)=v := (div_eq_iff hp).mpr (by ring)
  change (let w := a₁-z*(1/4); let q := a₂-z*(1/4)^2
          let d := Real.sqrt (((r+1:ℝ)*q-w^2)/r)
          let l := (w-d)/(r+1); let t := (w+r*d)/(r+1)
          0 ≤ l ∧ l ≤ t ∧ t ≤ 1/4 ∧ r*l+t+z*(1/4)=a₁ ∧
          r*l^2+t^2+z*(1/4)^2=a₂ ∧ a₃ ≤ r*l^3+t^3+z*(1/4)^3)
  simp only [ea,eb,ed,Real.sqrt_sq (sub_nonneg.mpr hsv),el,ev]
  exact ⟨hs,hsv,hv,h1,h2,h3⟩

private lemma count_shape {m : ℕ} {u s : ℝ} (x : Fin m → ℝ) (j : Fin m)
    (h : ∀ i, i ≠ j → x i = s ∨ x i = u) :
    ∃ r : Fin m, ∀ f : ℝ → ℝ, (∑ i, f (x i)) =
      r.val*f s+f (x j)+(m-1-r.val : ℕ)*f u := by
  classical
  let A := Finset.univ.erase j
  let B := A.filter (fun i => x i=s)
  let D := A.filter (fun i => ¬x i=s)
  have hcard : B.card+D.card = m-1 := by
    calc
      _ = A.card := Finset.card_filter_add_card_filter_not .. 
      _ = _ := by simp [A]
  have hm := j.isLt
  have hz : D.card = m-1-B.card := by omega
  refine ⟨⟨B.card,by omega⟩,fun f => ?_⟩
  have Bval (i) (hi : i ∈ B) : f (x i) = f s := congrArg f (Finset.mem_filter.mp hi).2
  have Dval (i) (hi : i ∈ D) : f (x i) = f u := by
    have e := Finset.mem_filter.mp hi
    exact congrArg f ((h i (Finset.mem_erase.mp e.1).1).resolve_left e.2)
  have eq1 : ∑ i ∈ B, f (x i) = B.card*f s := by
    rw [Finset.sum_congr rfl Bval,Finset.sum_const,nsmul_eq_mul]
  have eq2 : ∑ i ∈ D, f (x i) = D.card*f u := by
    rw [Finset.sum_congr rfl Dval,Finset.sum_const,nsmul_eq_mul]
  have e := Finset.sum_filter_add_sum_filter_not A (fun i => x i=s) (fun i => f (x i))
  change (∑ i ∈ B, f (x i)) + (∑ i ∈ D, f (x i)) = ∑ i ∈ A, f (x i) at e
  rw [eq1,eq2,hz] at e
  have g := Finset.sum_erase_add Finset.univ (fun i => f (x i)) (Finset.mem_univ j)
  change (∑ i ∈ A, f (x i))+f (x j) = _ at g
  rw [← e] at g
  linarith

private lemma realize {m : ℕ} (r : Fin m) {l v u : ℝ}
    (hl : 0 ≤ l) (hlv : l ≤ v) (hvu : v ≤ u) :
    ∃ x : Fin m → ℝ, (∀ i, x i ∈ Set.Icc 0 u) ∧ ∀ f : ℝ → ℝ,
      (∑ i, f (x i)) = r.val*f l+f v+(m-1-r.val : ℕ)*f u := by
  classical
  let I := Fin r.val ⊕ (Unit ⊕ Fin (m-1-r.val))
  have hr := r.isLt
  have hI : Fintype.card (Fin m) = Fintype.card I := by
    simp only [I,Fintype.card_fin,Fintype.card_sum,Fintype.card_unit]
    omega
  let e := Fintype.equivOfCardEq hI
  let y : I → ℝ := Sum.elim (fun _ => l) (Sum.elim (fun _ => v) (fun _ => u))
  refine ⟨fun i => y (e i),?_,fun f => ?_⟩
  · intro i
    change y (e i) ∈ Set.Icc 0 u
    generalize e i = w
    rcases w with a | (_ | b)
    · exact ⟨hl,hlv.trans hvu⟩
    · exact ⟨hl.trans hlv,hvu⟩
    · exact ⟨hl.trans (hlv.trans hvu),le_rfl⟩
  · calc
      _ = ∑ i : I, f (y i) := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by
        simp [I,y,Fintype.sum_sum_type]
        ring

end OMA.S_mo_301126
open OMA.S_mo_301126 in
theorem OMA.solution : type_of% @OMA.S_mo_301126.main := by
  intro m hm a₁ a₂ a₃ _ _ _
  constructor
  · rintro ⟨input,hi,h1,h2,h3⟩
    obtain ⟨x,s,j,hbox,hsum,hsq,hcube,hs,hsv,hshape⟩ := max_shape hm input hi
    obtain ⟨r,hr⟩ := count_shape x j hshape
    refine ⟨r,canonical (u := 1/4) rfl hs hsv (hbox j).2 ?_ ?_ ?_⟩
    · exact (hr id).symm.trans (hsum.trans h1)
    · exact (hr (fun t => t^2)).symm.trans (hsq.trans h2)
    · exact (h3.trans hcube).trans_eq (hr (fun t => t^3))
  · rintro ⟨r,hr⟩
    unfold candidate at hr
    dsimp only at hr
    obtain ⟨hl,hlv,hvu,h1,h2,h3⟩ := hr
    obtain ⟨x,hx,he⟩ := realize r hl hlv hvu
    exact ⟨x,hx,(he id).trans h1,(he (fun t => t^2)).trans h2,
      h3.trans_eq (he (fun t => t^3)).symm⟩
