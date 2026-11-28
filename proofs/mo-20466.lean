import OMAStatements.S_mo_20466

/-!
This shortening adapts @connoranderson's complete earlier proof:
https://github.com/connoranderson/open-math-agents/blob/cb3343b5ef6dd0d10dbac173d82a9239eb3005e2/proofs/mo-20466.lean,
linked from statement PR #27913. The current proof by @Solfanbtc (PR #31702)
was also reviewed. The intersection of half-spaces, its boundary-height
obstruction, and the interpolation section are retained from the earlier proof.
The new proof uses convexity of an interval, the square/absolute-value API,
and the infinitude of a nontrivial preconnected set in a T1 space.

Original question: gondolier, https://mathoverflow.net/questions/20466,
CC BY-SA 2.5.
-/

/-! Compact convex counterexample and line-valued positive result for gondolier’s
MathOverflow question 20466. Credit: @connoranderson. -/

namespace OMA.S_mo_20466
open Set
abbrev Space := (ℝ × ℝ) × ℝ

private def K : Set Space :=
  {p | p.1.2 ∈ Icc 0 1} ∩ {p | p.2 ∈ Icc 0 1} ∩
    ⋂ a : Ici (0:ℝ), {p | 2*(a:ℝ)*p.1.1 ≤ p.1.2 + (a:ℝ)^2*p.2} ∩
      {p | -(2*(a:ℝ)*p.1.1) ≤ p.1.2 + (a:ℝ)^2*(1-p.2)}

private lemma mem_K (p : Space) : p ∈ K ↔ (p.1.2 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 1) ∧
    ∀ a : Ici (0:ℝ), 2*(a:ℝ)*p.1.1 ≤ p.1.2 + (a:ℝ)^2*p.2 ∧
      -(2*(a:ℝ)*p.1.1) ≤ p.1.2 + (a:ℝ)^2*(1-p.2) := by
  simp only [K,mem_inter_iff,mem_iInter,mem_ofPred_eq]

private lemma compact_K : IsCompact K := by
  have hc : IsClosed K := by
    apply IsClosed.inter
    · exact (isClosed_Icc.preimage (continuous_snd.comp continuous_fst)).inter (isClosed_Icc.preimage continuous_snd)
    · apply isClosed_iInter
      intro a
      exact (isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop))
  apply (isCompact_Icc (a:=(((-1,0),0):Space)) (b:=(((1,1),1):Space))).of_isClosed_subset hc
  intro p hp
  obtain ⟨⟨hy,ht⟩,hh⟩ := (mem_K _).mp hp
  have h := hh ⟨1,by norm_num⟩
  change 2*1*p.1.1 ≤ p.1.2+1^2*p.2 ∧ -(2*1*p.1.1) ≤ p.1.2+1^2*(1-p.2) at h
  exact ⟨⟨⟨by linarith [h.2,hy.2,ht.1],hy.1⟩,ht.1⟩,
    ⟨⟨by linarith [h.1,hy.2,ht.2],hy.2⟩,ht.2⟩⟩

private lemma convex_K : Convex ℝ K := by
  intro p hp q hq α β hα hβ hab
  obtain ⟨⟨py,pt⟩,P⟩ := (mem_K _).mp hp
  obtain ⟨⟨qy,qt⟩,Q⟩ := (mem_K _).mp hq
  apply (mem_K _).mpr
  simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mem_Icc]
  have bound (x y : ℝ) (hx : x∈Icc 0 1) (hy : y∈Icc 0 1) : α*x+β*y ∈ Icc 0 1 :=
    convex_Icc (0:ℝ) 1 hx hy hα hβ hab
  refine ⟨⟨bound _ _ py qy,bound _ _ pt qt⟩, fun a => ⟨?_,?_⟩⟩
  · nlinarith [mul_nonneg hα (sub_nonneg.mpr (P a).1), mul_nonneg hβ (sub_nonneg.mpr (Q a).1)]
  · have hw := congrArg (fun x : ℝ => (a:ℝ)^2*x) hab
    nlinarith [mul_nonneg hα (sub_nonneg.mpr (P a).2), mul_nonneg hβ (sub_nonneg.mpr (Q a).2)]

private lemma curve_mem (x : ℝ) (hx : x ∈ Icc (-1) 1) :
    ((x,x^2),if 0≤x then 1 else 0) ∈ K := by
  have hy : x^2 ∈ Icc (0:ℝ) 1 := ⟨sq_nonneg _,(sq_le_one_iff_abs_le_one x).mpr (abs_le.mpr hx)⟩
  apply (mem_K _).mpr
  split_ifs with h
  · refine ⟨⟨hy,by norm_num⟩, fun a => ⟨?_,?_⟩⟩
    · dsimp; nlinarith [sq_nonneg ((a:ℝ)-x)]
    · dsimp; nlinarith [mul_nonneg (show 0≤(a:ℝ) from a.property) h,sq_nonneg x]
  · refine ⟨⟨hy,by norm_num⟩, fun a => ⟨?_,?_⟩⟩
    · dsimp; nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0≤(a:ℝ) from a.property) (le_of_not_ge h),sq_nonneg x]
    · dsimp; nlinarith [sq_nonneg ((a:ℝ)+x)]

private lemma unique_height (x t : ℝ) (h : ((x,x^2),t) ∈ K) :
    (0<x → t=1) ∧ (x<0 → t=0) := by
  obtain ⟨⟨_,ht⟩,hh⟩ := (mem_K _).mp h
  constructor
  · intro hx
    have H := (hh ⟨x,hx.le⟩).1
    change 2*x*x ≤ x^2+x^2*t at H
    have := sq_pos_of_pos hx
    by_contra hn
    nlinarith [mul_pos this (sub_pos.mpr (lt_of_le_of_ne ht.2 hn))]
  · intro hx
    have H := (hh ⟨-x,neg_nonneg.mpr hx.le⟩).2
    change -(2*(-x)*x) ≤ x^2+(-x)^2*(1-t) at H
    have := sq_pos_of_ne_zero hx.ne
    by_contra hn
    nlinarith [mul_pos this (lt_of_le_of_ne ht.1 (Ne.symm hn))]

private lemma no_section : ¬ HasSection K Prod.fst := by
  rintro ⟨g,hg,h⟩
  let z (t : Icc (-1:ℝ) 1) : Prod.fst '' K :=
    ⟨((t:ℝ),(t:ℝ)^2), ⟨_,curve_mem t t.property,rfl⟩⟩
  let height (t : Icc (-1:ℝ) 1) : ℝ := (g (z t)).2
  have hz : Continuous z := Continuous.subtype_mk (by fun_prop) _
  have hc : Continuous height := continuous_snd.comp (hg.comp hz)
  have hu (t : Icc (-1:ℝ) 1) : (0<(t:ℝ) → height t=1) ∧ ((t:ℝ)<0 → height t=0) := by
    have hh := (h (z t)).1
    have he := (h (z t)).2
    change (g (z t)).1 = ((t:ℝ),(t:ℝ)^2) at he
    apply unique_height
    change ((⟨(t:ℝ),(t:ℝ)^2⟩),(g (z t)).2) ∈ K
    rw [←he,Prod.eta]; exact hh
  let lo : Icc (-1:ℝ) 1 := ⟨-1,by norm_num⟩
  let hi : Icc (-1:ℝ) 1 := ⟨1,by norm_num⟩
  have h₀ : (0:ℝ) ∈ range height := ⟨lo,(hu lo).2 (by norm_num [lo])⟩
  have h₁ : (1:ℝ) ∈ range height := ⟨hi,(hu hi).1 (by norm_num [hi])⟩
  let : PreconnectedSpace (Icc (-1:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  have hf : (range height).Finite := by
    apply (Set.toFinite {0,1,height ⟨0,by norm_num⟩}).subset
    rintro _ ⟨t,rfl⟩
    rcases lt_trichotomy (t:ℝ) 0 with hn | hz | hp
    · simp [(hu t).2 hn]
    · have : t = ⟨0,by norm_num⟩ := Subtype.ext hz
      simp [this]
    · simp [(hu t).1 hp]
  exact hf.not_infinite ((isPreconnected_range hc).infinite_of_nontrivial
    ⟨0,h₀,1,h₁,by norm_num⟩)

private lemma line_section (n : ℕ) (S : Set (Fin n → ℝ)) (hS : S.Nonempty)
    (hK : IsCompact S) (hC : Convex ℝ S) (f : (Fin n → ℝ) →L[ℝ] ℝ) : HasSection S f := by
  obtain ⟨u,hu,hmin⟩ := hK.exists_isMinOn hS f.continuous.continuousOn
  obtain ⟨w,hw,hmax⟩ := hK.exists_isMaxOn hS f.continuous.continuousOn
  have bounds (x : f '' S) : f u ≤ (x:ℝ) ∧ (x:ℝ) ≤ f w := by
    rcases x with ⟨_,y,hy,rfl⟩; exact ⟨hmin hy,hmax hy⟩
  by_cases he : f u=f w
  · exact ⟨fun _ => u,continuous_const, fun x => ⟨hu,by linarith [(bounds x).1,(bounds x).2]⟩⟩
  have hd : 0 < f w - f u := sub_pos.mpr (lt_of_le_of_ne (hmin hw) he)
  let t (x : f '' S) : ℝ := ((x:ℝ)-f u)/(f w-f u)
  refine ⟨fun x => (1-t x) • u + t x • w,by dsimp [t]; fun_prop, fun x => ⟨?_,?_⟩⟩
  · have h₀ : 0 ≤ t x := div_nonneg (sub_nonneg.mpr (bounds x).1) hd.le
    have h₁ : t x ≤ 1 := (div_le_one hd).mpr (by linarith [(bounds x).2])
    exact hC hu hw (sub_nonneg.mpr h₁) h₀ (by ring)
  · simp only [map_add,map_smul,smul_eq_mul,t]
    field_simp [hd.ne']; ring

end OMA.S_mo_20466

theorem OMA.solution : type_of% @OMA.S_mo_20466.main := by
  refine ⟨⟨OMA.S_mo_20466.K,⟨_,OMA.S_mo_20466.curve_mem 0 (by norm_num)⟩,
    OMA.S_mo_20466.compact_K,OMA.S_mo_20466.convex_K,OMA.S_mo_20466.no_section⟩,
    OMA.S_mo_20466.line_section⟩
