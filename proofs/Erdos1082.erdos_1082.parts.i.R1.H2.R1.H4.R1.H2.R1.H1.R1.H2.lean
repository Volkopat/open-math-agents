import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H1_R1

/-!
# Impossible five-point three-distance patterns, part 1

The three fixed anchors and the last two points give three Gram identities. Noncollinearity makes every triangle area factor nonzero. The displayed polynomial combinations eliminate the listed patterns.
-/

namespace Erdos1082Ten


open EuclideanGeometry

def dsq (p q : ℝ²) := (p 0 - q 0)^2 + (p 1-q 1)^2

lemma dsq_eq (p q : ℝ²) : dsq p q=dist p q^2 := by
  rw [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]
  simp [dsq,Real.dist_eq]

def cross (o e f : ℝ²) := (e 0-o 0)*(f 1-o 1)-(e 1-o 1)*(f 0-o 0)

lemma collinear_of_cross_zero (o e f : ℝ²) (hoe : o≠e) (he : cross o e f=0) :
    Collinear ℝ ({o,e,f}:Set ℝ²) := by
  apply (collinear_iff_of_mem (k:=ℝ) (Set.mem_insert o ({e,f}:Set ℝ²))).mpr
  refine ⟨e-o,?_⟩
  intro x hx
  rcases hx with h|h|h
  · exact ⟨0,by simp [h]⟩
  · exact ⟨1,by simp [h]⟩
  have hx' : x=f := h
  subst x
  dsimp [cross] at he
  have hev (i : Fin 2) (k : ℝ) : (k • (e-o) +ᵥ o) i=k*(e i-o i)+o i := rfl
  by_cases h₀ : e 0-o 0=0
  · have h₁ : e 1-o 1≠0 := by
      intro he
      apply hoe
      ext i
      fin_cases i <;> dsimp at * <;> linarith
    refine ⟨(f 1-o 1)/(e 1-o 1),?_⟩
    ext i
    rw [hev]
    fin_cases i
    · change f 0=(f 1-o 1)/(e 1-o 1)*(e 0-o 0)+o 0
      rw [h₀,mul_zero,zero_add]
      have hh : f 0-o 0=0 := (mul_eq_zero.mp (by linear_combination -he+ (f 1-o 1)*h₀ : (e 1-o 1)*(f 0-o 0)=0)).resolve_left h₁
      linarith
    · change f 1=(f 1-o 1)/(e 1-o 1)*(e 1-o 1)+o 1
      field_simp; ring
  · refine ⟨(f 0-o 0)/(e 0-o 0),?_⟩
    ext i
    rw [hev]
    fin_cases i
    · change f 0=(f 0-o 0)/(e 0-o 0)*(e 0-o 0)+o 0
      field_simp; ring
    · change f 1=(f 0-o 0)/(e 0-o 0)*(e 1-o 1)+o 1
      field_simp
      linear_combination he

def area (a b c : ℝ) := 4*a*b-(a+b-c)^2

def gram (a b c d₀ d₁ d₂ e₀ e₁ e₂ h : ℝ) : ℝ :=
  let g := a+b-c
  let u := a+d₀-d₁
  let v := b+d₀-d₂
  let w := a+e₀-e₁
  let z := b+e₀-e₂
  2*b*u*w-g*(u*z+v*w)+2*a*v*z-area a b c*(d₀+e₀-h)

lemma area_identity (o e f : ℝ²) (s : ℝ) :
    area (s*dsq o e) (s*dsq o f) (s*dsq e f)=4*(s*cross o e f)^2 := by
  unfold area dsq cross
  ring

lemma area_ne (o e f : ℝ²) (s : ℝ) (hs : s≠0) (hoe : o≠e)
    (hn : ¬Collinear ℝ ({o,e,f}:Set ℝ²)) :
    area (s*dsq o e) (s*dsq o f) (s*dsq e f)≠0 := by
  rw [area_identity]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero hs (fun he => hn (collinear_of_cross_zero o e f hoe he))))

lemma gram_identity (o e f x y : ℝ²) (s : ℝ) :
    gram (s*dsq o e) (s*dsq o f) (s*dsq e f)
      (s*dsq o x) (s*dsq e x) (s*dsq f x) (s*dsq o y) (s*dsq e y) (s*dsq f y) (s*dsq x y)=0 := by
  unfold gram area dsq
  ring


open EuclideanGeometry
def colorCode (c : Fin 10→Fin 3) : ℕ := (c 0).val*19683+(c 1).val*6561+(c 2).val*2187+(c 3).val*729+(c 4).val*243+(c 5).val*81+(c 6).val*27+(c 7).val*9+(c 8).val*3+(c 9).val*1
def slot : Fin 5→Fin 5→Fin 10 := ![![0,0,1,2,3],![0,0,4,5,6],![1,4,0,7,8],![2,5,7,0,9],![3,6,8,9,0]]
def palette3 (x y : ℝ) : Fin 3→ℝ := ![1,x,y]

def baseD (c : Fin 10→Fin 3) (x y : ℝ) (i j : Fin 5) := palette3 x y (c (slot i j))

def threeGram (d : Fin 5→Fin 5→ℝ) (i j : Fin 5) :=
  gram (d 0 1) (d 0 2) (d 1 2) (d 0 i) (d 1 i) (d 2 i) (d 0 j) (d 1 j) (d 2 j) (if i=j then 0 else d i j)

def admissible (c : Fin 10→Fin 3) (x y : ℝ) :=
  let d := baseD c x y
  (x≠0 ∧ y≠0 ∧ x-1≠0 ∧ y-1≠0 ∧ x-y≠0) ∧
    (∀ i j k : Fin 5, i<j → j<k → area (d i j) (d i k) (d j k)≠0) ∧
    threeGram d 3 3=0 ∧ threeGram d 3 4=0 ∧ threeGram d 4 4=0

lemma build_admissible (c : Fin 10→Fin 3) (x y s : ℝ) (p : Fin 5→ℝ²) (hp : Function.Injective p) (hs : s≠0)
    (hcol : ∀ i j k : Fin 5, i≠j → j≠k → i≠k → ¬Collinear ℝ ({p i,p j,p k}:Set ℝ²))
    (hc : ∀ i j, i≠j → baseD c x y i j=s*dsq (p i) (p j))
    (he : x≠0 ∧ y≠0 ∧ x-1≠0 ∧ y-1≠0 ∧ x-y≠0) : admissible c x y := by
  refine ⟨he,?_,?_,?_,?_⟩
  · intro i j k hij hjk
    rw [hc _ _ hij.ne,hc _ _ (hij.trans hjk).ne,hc _ _ hjk.ne]
    exact area_ne _ _ _ s hs (fun h => hij.ne (hp h)) (hcol _ _ _ hij.ne hjk.ne (hij.trans hjk).ne)
  · have hv := gram_identity (p 0) (p 1) (p 2) (p 3) (p 3) s
    rw [←hc 0 1 (by decide),←hc 0 2 (by decide),←hc 1 2 (by decide),←hc 0 3 (by decide),←hc 1 3 (by decide),←hc 2 3 (by decide)] at hv
    have hzero : dsq (p 3) (p 3)=0 := by simp [dsq]
    rw [hzero,mul_zero] at hv
    exact hv
  · have hv := gram_identity (p 0) (p 1) (p 2) (p 3) (p 4) s
    rw [←hc 0 1 (by decide),←hc 0 2 (by decide),←hc 1 2 (by decide),←hc 0 3 (by decide),←hc 1 3 (by decide),←hc 2 3 (by decide),←hc 0 4 (by decide),←hc 1 4 (by decide),←hc 2 4 (by decide),←hc 3 4 (by decide)] at hv
    exact hv
  · have hv := gram_identity (p 0) (p 1) (p 2) (p 4) (p 4) s
    rw [←hc 0 1 (by decide),←hc 0 2 (by decide),←hc 1 2 (by decide),←hc 0 4 (by decide),←hc 1 4 (by decide),←hc 2 4 (by decide)] at hv
    have hzero : dsq (p 4) (p 4)=0 := by simp [dsq]
    rw [hzero,mul_zero] at hv
    exact hv

def edges5 : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

lemma match_edges {B : Finset ℝ²} {T : Finset ℝ} (p : Fin 5≃B) (r : Fin 3≃T) (c : Fin 10→Fin 3)
    (h : ∀ k, dist (p (edges5 k).1).1 (p (edges5 k).2).1=(r (c k)).1) :
    ∀ i j : Fin 5, i≠j → (r (c (slot i j))).1=dist (p i).1 (p j).1 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact (h 0).symm
  · exact (h 1).symm
  · exact (h 2).symm
  · exact (h 3).symm
  · exact (h 0).symm.trans (dist_comm ..)
  · exact False.elim (hij rfl)
  · exact (h 4).symm
  · exact (h 5).symm
  · exact (h 6).symm
  · exact (h 1).symm.trans (dist_comm ..)
  · exact (h 4).symm.trans (dist_comm ..)
  · exact False.elim (hij rfl)
  · exact (h 7).symm
  · exact (h 8).symm
  · exact (h 2).symm.trans (dist_comm ..)
  · exact (h 5).symm.trans (dist_comm ..)
  · exact (h 7).symm.trans (dist_comm ..)
  · exact False.elim (hij rfl)
  · exact (h 9).symm
  · exact (h 3).symm.trans (dist_comm ..)
  · exact (h 6).symm.trans (dist_comm ..)
  · exact (h 8).symm.trans (dist_comm ..)
  · exact (h 9).symm.trans (dist_comm ..)
  · exact False.elim (hij rfl)

lemma scaled_sq_inj {s a b : ℝ} (hs : s≠0) (ha : 0<a) (hb : 0<b) (h : s*a^2=s*b^2) : a=b := by
  have he := mul_left_cancel₀ hs h
  have hsum : 0<a+b := add_pos ha hb
  have hprod : (a-b)*(a+b)=0 := by linear_combination he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum.ne')

lemma distanceSet_pos {A : Finset ℝ²} {d : ℝ} (hd : d∈distanceSet A) : 0<d := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hd
  exact dist_pos.mpr (Finset.mem_offDiag.mp hab).2.2

lemma given_colors (B : Finset ℝ²) (hn : NonTrilinear (B:Set ℝ²))
    (p : Fin 5≃B) (r : Fin 3≃distanceSet B) (c : Fin 10→Fin 3)
    (h : ∀ k, dist (p (edges5 k).1).1 (p (edges5 k).2).1=(r (c k)).1) :
    ∃ s x y : ℝ, 0<s ∧ admissible c x y ∧ (∀ i : Fin 3, palette3 x y i=s*(r i).1^2) ∧
      ∀ i j, i≠j → baseD c x y i j=s*dsq (p i).1 (p j).1 := by
  let s := ((r 0).1^2)⁻¹
  let f (d : ℝ) := s*d^2
  let x := f (r 1).1
  let y := f (r 2).1
  have rpos (i : Fin 3) := distanceSet_pos (r i).2
  have hs : 0<s := inv_pos.mpr (sq_pos_of_pos (rpos 0))
  have one : f (r 0).1=1 := by dsimp [f,s]; field_simp [(rpos 0).ne']
  have rmap (i : Fin 3) : palette3 x y i=f (r i).1 := by fin_cases i <;> first | exact one.symm | rfl
  have hr := match_edges p r c h
  have hc (i j : Fin 5) (hij : i≠j) : baseD c x y i j=s*dsq (p i).1 (p j).1 := by
    change palette3 x y (c (slot i j))=_
    rw [rmap,hr i j hij,dsq_eq]
  have vi : Function.Injective (fun i : Fin 3 => f (r i).1) := fun i j e =>
    r.injective (Subtype.ext (scaled_sq_inj hs.ne' (rpos i) (rpos j) e))
  have hpos (i : Fin 3) : 0<f (r i).1 := mul_pos hs (sq_pos_of_pos (rpos i))
  have xy : x≠0 ∧ y≠0 ∧ x-1≠0 ∧ y-1≠0 ∧ x-y≠0 := by
    refine ⟨(hpos 1).ne',(hpos 2).ne',sub_ne_zero.mpr ?_,sub_ne_zero.mpr ?_,sub_ne_zero.mpr ?_⟩
    · intro e; exact (by decide : (1:Fin 3)≠0) (vi (e.trans one.symm))
    · intro e; exact (by decide : (2:Fin 3)≠0) (vi (e.trans one.symm))
    · intro e; exact (by decide : (1:Fin 3)≠2) (vi e)
  have pi : Function.Injective (fun i : Fin 5 => (p i).1) := fun _ _ e => p.injective (Subtype.ext e)
  refine ⟨s,x,y,hs,build_admissible c x y s _ pi hs.ne' ?_ hc xy,rmap,hc⟩
  intro i j k hij hjk hik
  exact hn (p i).2 (p j).2 (p k).2 (fun e => hij (pi e)) (fun e => hjk (pi e)) (fun e => hik (pi e))

lemma injective_colorCode : Function.Injective colorCode := by
  intro c d h
  unfold colorCode at h
  have a0 := (c 0).isLt
  have b0 := (d 0).isLt
  have a1 := (c 1).isLt
  have b1 := (d 1).isLt
  have a2 := (c 2).isLt
  have b2 := (d 2).isLt
  have a3 := (c 3).isLt
  have b3 := (d 3).isLt
  have a4 := (c 4).isLt
  have b4 := (d 4).isLt
  have a5 := (c 5).isLt
  have b5 := (d 5).isLt
  have a6 := (c 6).isLt
  have b6 := (d 6).isLt
  have a7 := (c 7).isLt
  have b7 := (d 7).isLt
  have a8 := (c 8).isLt
  have b8 := (d 8).isLt
  have a9 := (c 9).isLt
  have b9 := (d 9).isLt
  have h0 : c 0=d 0 := by apply Fin.ext; omega
  rw [h0] at h
  have h1 : c 1=d 1 := by apply Fin.ext; omega
  rw [h1] at h
  have h2 : c 2=d 2 := by apply Fin.ext; omega
  rw [h2] at h
  have h3 : c 3=d 3 := by apply Fin.ext; omega
  rw [h3] at h
  have h4 : c 4=d 4 := by apply Fin.ext; omega
  rw [h4] at h
  have h5 : c 5=d 5 := by apply Fin.ext; omega
  rw [h5] at h
  have h6 : c 6=d 6 := by apply Fin.ext; omega
  rw [h6] at h
  have h7 : c 7=d 7 := by apply Fin.ext; omega
  rw [h7] at h
  have h8 : c 8=d 8 := by apply Fin.ext; omega
  rw [h8] at h
  have h9 : c 9=d 9 := by apply Fin.ext; omega
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
private lemma base_0000000000 (x y : ℝ) (g0 : (-4:ℝ)=0) (g1 : (-1:ℝ)=0) (g2 : (-4:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : (3:ℝ)≠0) (_n8 : (3:ℝ)≠0) (_n9 : (3:ℝ)≠0) (_n10 : (3:ℝ)≠0) (_n11 : (3:ℝ)≠0) (_n12 : (3:ℝ)≠0) (_n13 : (3:ℝ)≠0) (_n14 : (3:ℝ)≠0) : False := by
  have h1 : (1:ℝ)=0 := by linear_combination (-1/4)*g0
  have h2 : (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : (1:ℝ)=0 := by linear_combination (-1/4)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0000000001 (x y : ℝ) (g0 : (-4:ℝ)=0) (g1 : 3*x - (4:ℝ)=0) (g2 : (-4:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : (3:ℝ)≠0) (_n8 : (3:ℝ)≠0) (_n9 : (3:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : (3:ℝ)≠0) (_n12 : (3:ℝ)≠0) (_n13 : -x^2 + 4*x≠0) (_n14 : -x^2 + 4*x≠0) : False := by
  have h1 : (1:ℝ)=0 := by linear_combination (-1/4)*g0
  have h2 : x - 4/(3:ℝ)=0 := by linear_combination (1/3)*g1
  have h3 : (1:ℝ)=0 := by linear_combination (-1/4)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h1
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0000000011 (x y : ℝ) (g0 : (-4:ℝ)=0) (g1 : 2*x - (3:ℝ)=0) (g2 : 2*x^2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : (3:ℝ)≠0) (_n8 : (3:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : (3:ℝ)≠0) (_n12 : -x^2 + 4*x≠0) (n13 : -x^2 + 4*x≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h1 : (1:ℝ)=0 := by linear_combination (-1/4)*g0
  have h2 : x - 3/(2:ℝ)=0 := by linear_combination (1/2)*g1
  have h4 : x≠0 := by
    intro he
    apply n13
    linear_combination (4 - x)*he
  have h5 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h3 := (mul_eq_zero.mp h5).resolve_left h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h1
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  norm_num at h6



private lemma base_0000000012 (x y : ℝ) (g0 : (-4:ℝ)=0) (g1 : -x + 3*y - (3:ℝ)=0) (g2 : 2*x^2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : (3:ℝ)≠0) (_n8 : (3:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : (3:ℝ)≠0) (n12 : -x^2 + 4*x≠0) (_n13 : -y^2 + 4*y≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : (1:ℝ)=0 := by linear_combination (-1/4)*g0
  have h2 : x - 3*y + (3:ℝ)=0 := by linear_combination (-1)*g1
  have h4 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h5 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h3 := (mul_eq_zero.mp h5).resolve_left h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h1
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  norm_num at h6



private lemma base_0000000111 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : 2*x^2 - 3*x=0) (g2 : 2*x^2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : (3:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 4*x≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 4*x≠0) (n14 : 3*x^2≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (3*x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x - 3/2)=0 := by linear_combination (1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left h2
  have h8 : (1:ℝ)=0 := by linear_combination (2/3)*h4 + (-2/3)*h6
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0000000112 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : 2*x^2 - 6*x + 3*y=0) (g2 : 2*x^2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : (3:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : -x^2 + 4*x≠0) (n12 : -x^2 + 4*x≠0) (_n13 : -y^2 + 4*y≠0) (n14 : 4*x*y - y^2≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 - 3*x + 3*y/(2:ℝ)=0 := by linear_combination (1/2)*g1
  have h6 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h5 := (mul_eq_zero.mp h6).resolve_left h2
  have h7 : y=0 := by linear_combination (2/3)*h4 + (-2*x/3)*h5
  have h9 : y≠0 := by
    intro he
    apply n14
    linear_combination (4*x - y)*he
  have h10 : ((y))*(1)=0 := by linear_combination (1)*h7
  have h8 := (mul_eq_zero.mp h10).resolve_left h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h11
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  norm_num at h11



private lemma base_0000001011 (x y : ℝ) (g0 : (-4:ℝ)=0) (_g1 : x - (2:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : (3:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : (3:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h1 : (1:ℝ)=0 := by linear_combination (-1/4)*g0
  have h2 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : (1:ℝ)=0 := by linear_combination (1)*h1
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  norm_num at h3



private lemma base_0000001012 (x y : ℝ) (g0 : (-4:ℝ)=0) (g1 : -2*x + 3*y - (2:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : (3:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : (3:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : (1:ℝ)=0 := by linear_combination (-1/4)*g0
  have h2 : x - 3*y/2 + (1:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h1
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0000001100 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -x^2=0) (g2 : 2*x^2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : (3:ℝ)≠0) (_n10 : (3:ℝ)≠0) (_n11 : -x^2 + 4*x≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 4*x≠0) (n14 : -x^2 + 4*x≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x) * (x))*(1)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left (mul_ne_zero h2 h2)
  have h7 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left h2
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0000001101 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -x^2 + 3*x - (3:ℝ)=0) (g2 : 2*x^2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : (3:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 4*x≠0) (n12 : -x^2 + 4*x≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 - 3*x + (3:ℝ)=0 := by linear_combination (-1)*g1
  have h6 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h5 := (mul_eq_zero.mp h6).resolve_left h2
  have h7 : (1:ℝ)=0 := by linear_combination (1/3)*h4 + (-x/3)*h5
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0000001102 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -x^2 + 3*y - (3:ℝ)=0) (g2 : 2*x^2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : (3:ℝ)≠0) (n10 : -y^2 + 4*y≠0) (_n11 : -x^2 + 4*x≠0) (n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 - 3*y + (3:ℝ)=0 := by linear_combination (-1)*g1
  have h6 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h5 := (mul_eq_zero.mp h6).resolve_left h2
  have h7 : x - (3:ℝ)=0 := by linear_combination (1)*h5
  have h8 : y - (4:ℝ)=0 := by linear_combination (-1/3)*h4 + (x/3 + 1)*h5
  have h9 : x - (3:ℝ)=0 := by linear_combination (1)*h7
  have h11 : y - (4:ℝ)≠0 := by
    intro he
    apply n10
    linear_combination (-y)*he
  have h12 : ((y - 4))*(1)=0 := by linear_combination (1)*h8
  have h10 := (mul_eq_zero.mp h12).resolve_left h11
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h10
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  have h15 : (1:ℝ)=0 := by linear_combination (1)*h14
  norm_num at h13



private lemma base_0000001111 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : x^2 - 2*x=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 4*x≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (n14 : 3*x^2≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (3*x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x - 2)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-1)*h1 + (1)*h4
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0000001112 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (_g1 : x^2 - 5*x + 3*y=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -y^2 + 4*y≠0) (n11 : -x^2 + 4*x≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*x*y - y^2≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n11
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h5 : (1:ℝ)=0 := by linear_combination (x/2 - 1/2)*h1 + (-1/2)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0000001122 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -x^2 + 2*x*y - 2*x=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : -x^2 + 4*x≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x - 2*y + 2)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (2*y/3 - 1)*h1 + (4*x/9 - 2*y/9 - 7/9)*h4 + (-4/9)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0000001200 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : -x*y=0) (g2 : 2*x^2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : (3:ℝ)≠0) (_n10 : (3:ℝ)≠0) (_n11 : -y^2 + 4*y≠0) (_n12 : -x^2 + 4*x≠0) (n13 : -x^2 + 4*x≠0) (n14 : -y^2 + 4*y≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (4 - y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : x≠0 := by
    intro he
    apply n13
    linear_combination (4 - x)*he
  have h6 : ((y) * (x))*(1)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h6).resolve_left (mul_ne_zero h2 h5)
  have h8 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h7 := (mul_eq_zero.mp h8).resolve_left h5
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0000001201 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : -x*y + 3*x - (3:ℝ)=0) (g2 : 2*x^2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : (3:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (n11 : -y^2 + 4*y≠0) (n12 : -x^2 + 4*x≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4 - y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x*y - 3*x + (3:ℝ)=0 := by linear_combination (-1)*g1
  have h6 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h7 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h5 := (mul_eq_zero.mp h7).resolve_left h6
  have h8 : (1:ℝ)=0 := by linear_combination (-x/3)*h1 + (1/3)*h4
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0000001211 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : x*y - 2*y=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -y^2 + 4*y≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (n14 : 4*x*y - y^2≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (4*x - y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x - 2)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (x/3 - 2/3)*h4 + (-1/3)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0000001212 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : x*y - 3*x + y=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -y^2 + 4*y≠0) (n11 : -y^2 + 4*y≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4 - y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h5 : (1:ℝ)=0 := by linear_combination (-x/3 - 1/3)*h1 + (1/3)*g1
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma shape_0000000000 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,0,0,0,0] x y) : False := by
  apply base_0000000000 x y
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 1 1 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000000001 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,0,0,0,1] x y) : False := by
  apply base_0000000001 x y
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 1 1 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000000011 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,0,0,1,1] x y) : False := by
  apply base_0000000011 x y
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 1 1 x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000000012 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,0,0,1,2] x y) : False := by
  apply base_0000000012 x y
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 1 1 x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000000111 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,0,1,1,1] x y) : False := by
  apply base_0000000111 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 1 x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000000112 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,0,1,1,2] x y) : False := by
  apply base_0000000112 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 1 x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001011 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,0,1,1] x y) : False := by
  apply base_0000001011 x y
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 1 x x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001012 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,0,1,2] x y) : False := by
  apply base_0000001012 x y
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 1 x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001100 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,1,0,0] x y) : False := by
  apply base_0000001100 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 x 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x 1 1 x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001101 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,1,0,1] x y) : False := by
  apply base_0000001101 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 x 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x 1 1 x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001102 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,1,0,2] x y) : False := by
  apply base_0000001102 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 x 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x 1 1 x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001111 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,1,1,1] x y) : False := by
  apply base_0000001111 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 x x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001112 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,1,1,2] x y) : False := by
  apply base_0000001112 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001122 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,1,2,2] x y) : False := by
  apply base_0000001122 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x 1 x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001200 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,2,0,0] x y) : False := by
  apply base_0000001200 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y 1 x 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x 1 1 x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001201 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,2,0,1] x y) : False := by
  apply base_0000001201 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y 1 x 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x 1 1 x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001211 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,2,1,1] x y) : False := by
  apply base_0000001211 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y 1 x x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000001212 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,2,1,2] x y) : False := by
  apply base_0000001212 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y 1 x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma base_0000001222 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : -x*y + 2*y^2 - 2*y=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : -y^2 + 4*y≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : 3*y^2≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (3*y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x - 2*y + 2)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : x - (4:ℝ)=0 := by linear_combination (2)*h1 + (1)*h4
  have h8 : y - (3:ℝ)=0 := by linear_combination (1)*h1
  have h10 : x - (4:ℝ)≠0 := by
    intro he
    apply n7
    linear_combination (-x)*he
  have h11 : ((x - 4))*(1)=0 := by linear_combination (1)*h7
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h12 : y - (3:ℝ)=0 := by linear_combination (1)*h8
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  have h15 : (1:ℝ)=0 := by linear_combination (1)*h14
  norm_num at h13



private lemma base_0000011110 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : 2*x^2 - 8*x + (5:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : (3:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 4*x + 5/(2:ℝ)=0 := by linear_combination (1/2)*g1
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (2/3)*h2 + (-2/3)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0000011111 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : 2*x^2 - 5*x + (2:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 3*x^2≠0) (_n14 : 3*x^2≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 5*x/2 + (1:ℝ)=0 := by linear_combination (1/2)*g1
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (8/3 - 2*x/3)*h2 + (2*x/3 - 5/3)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0000011112 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : 2*x^2 - 8*x + 3*y + (2:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 4*x*y - y^2≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 4*x + 3*y/2 + (1:ℝ)=0 := by linear_combination (1/2)*g1
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : y=0 := by linear_combination (2/3)*h2 + (-2/3)*h3
  have h6 : y≠0 := by
    intro he
    apply n14
    linear_combination (4*x - y)*he
  have h7 : ((y))*(1)=0 := by linear_combination (1)*h4
  have h5 := (mul_eq_zero.mp h7).resolve_left h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0000011121 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : x^2 + x*y - 3*x - 2*y + (2:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 3*x^2≠0) (_n14 : 4*x*y - y^2≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : (1:ℝ)=0 := by linear_combination (-5*x*y^2/27 + 11*x*y/27 - 11*x/27 + 5*y^3/54 - 31*y^2/54 + 85*y/54 - 5/54)*h1 + (5*x*y^2/54 - 11*x*y/54 + 11*x/54 - 5*y^3/54 + 13*y^2/27 - 89*y/54 + 29/18)*g1 + (5*x*y^2/54 - 11*x*y/54 + 11*x/54 - 5*y^2/27 + 37*y/54 - 115/54)*h2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  norm_num at h3



private lemma base_0000011122 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : x^2 + x*y - 6*x + y + (2:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : (1:ℝ)=0 := by linear_combination (2*x^2*y/9 - 2*x^2/9 - 5*x*y/9 + 5*x/9 - y^3/18 + 4*y^2/9 + y/9 - 5/2)*h1 + (-x^2*y/9 + x^2/9 + x*y^2/18 + 5*x*y/18 - x/3 + y^3/18 - 7*y^2/18 + 4/3)*g1 + (-x^2*y/9 + x^2/9 - x*y^2/18 + 5*x*y/18 - 2*x/9 - y^2/18 + 2*y/9 + 5/6)*h2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  norm_num at h3



private lemma base_0000011220 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (5:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : (3:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y - 2*x + y^2 - 2*y + 5/(2:ℝ)=0 := by linear_combination (1/2)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (2/3)*h2 + (-2/3)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0000011221 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : 2*x^2 - 2*x*y - x + 2*y^2 - 4*y + (2:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 3*x^2≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y - x/2 + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x=0 := by linear_combination (2/3)*h2 + (-2/3)*h3
  have h5 : y^2 - 2*y + (1:ℝ)=0 := by linear_combination (-2*x/3 + 2*y/3 + 4/3)*h2 + (2*x/3 - 2*y/3 - 1/3)*h3
  have h7 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h8 : ((x))*(1)=0 := by linear_combination (1)*h4
  have h6 := (mul_eq_zero.mp h8).resolve_left h7
  have h10 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h11 : ((y - 1) * (y - 1))*(1)=0 := by linear_combination (1)*h5
  have h9 := (mul_eq_zero.mp h11).resolve_left (mul_ne_zero h10 h10)
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma base_0000012121 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : 2*x*y - x - 4*y + (2:ℝ)=0) (g2 : 2*y^2 - 8*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -y^2 + 4*y≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (_n14 : 4*x*y - y^2≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x*y - x/2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g1
  have h3 : y^2 - 4*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-1/3)*h1 + (4*x*y/9 - 14*x/9 - 8*y/9 + 28/9)*h2 + (-4*x^2/9 + 16*x/9 - 16/9)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0000012210 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 + 4*x*y - 4*x - y^2 - 4*y + (5:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -y^2 + 4*y≠0) (n8 : -y^2 + 4*y≠0) (n9 : -x^2 + 4*x≠0) (_n10 : (3:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 4*x*y + 4*x + y^2 + 4*y - (5:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : 2*x + y^3 - 6*y^2 + 7*y - (2:ℝ)=0 := by linear_combination (x/3 - y/3)*h2 + (-x/3 + 4*y/3 - 2)*h3
  have h5 : y^4 - 8*y^3 + 19*y^2 - 12*y=0 := by linear_combination (x*y/3 - 2*x/3 - y^2/3 + 2*y/3 + 2/3)*h2 + (-x*y/3 + 2*x/3 + 4*y^2/3 - 14*y/3 + 10/3)*h3
  have h6 : x + y^3/2 - 3*y^2 + 7*y/2 - (1:ℝ)=0 := by linear_combination (1/2)*h4
  have h8 : y - (4:ℝ)≠0 := by
    intro he
    apply n8
    linear_combination (-y)*he
  have h9 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h10 : y≠0 := by
    intro he
    apply n8
    linear_combination (4 - y)*he
  have h11 : ((y - 4) * (y - 1) * (y))*(y - 3)=0 := by linear_combination (1)*h5
  have h7 := (mul_eq_zero.mp h11).resolve_left (mul_ne_zero (mul_ne_zero h8 h9) h10)
  have h12 : x - (4:ℝ)=0 := by linear_combination (1)*h6 + (-y^2/2 + 3*y/2 + 1)*h7
  have h14 : x - (4:ℝ)≠0 := by
    intro he
    apply n9
    linear_combination (-x)*he
  have h15 : ((x - 4))*(1)=0 := by linear_combination (1)*h12
  have h13 := (mul_eq_zero.mp h15).resolve_left h14
  have h16 : (1:ℝ)=0 := by linear_combination (1)*h13
  have h17 : (1:ℝ)=0 := by linear_combination (1)*h16
  have h18 : (1:ℝ)=0 := by linear_combination (1)*h17
  norm_num at h16



private lemma base_0000111111 (x y : ℝ) (g0 : 2*x^3 - 6*x^2=0) (g1 : x^3 - 2*x^2=0) (g2 : 2*x^3 - 6*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 3*x^2≠0) (_n12 : 3*x^2≠0) (_n13 : 3*x^2≠0) (n14 : 3*x^2≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (3*x)*he
  have h3 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((x) * (x))*(x - 2)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left (mul_ne_zero h2 h2)
  have h7 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left (mul_ne_zero h2 h2)
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h4 + (-1)*h6
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0000111112 (x y : ℝ) (g0 : 2*x^3 - 6*x^2=0) (g1 : 2*x^3 - x^2*y - 6*x^2 + 4*x*y=0) (g2 : 2*x^3 - 6*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : 3*x^2≠0) (n12 : 3*x^2≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 4*x*y - y^2≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (3*x)*he
  have h3 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((x))*(x^2 - x*y/2 - 3*x + 2*y)=0 := by linear_combination (1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left (mul_ne_zero h2 h2)
  have h8 : y=0 := by linear_combination (2)*h4 + (-2*x + y)*h6
  have h10 : y≠0 := by
    intro he
    apply n14
    linear_combination (4*x - y)*he
  have h11 : ((y))*(1)=0 := by linear_combination (1)*h8
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma base_0000111122 (x y : ℝ) (g0 : 2*x^3 - 6*x^2=0) (g1 : x^3 - 4*x^2 + 2*x*y=0) (g2 : 2*x^2*y - 8*x*y + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : 3*x^2≠0) (_n12 : 4*x*y - y^2≠0) (n13 : 4*x*y - y^2≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h3 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((x))*(x^2 - 4*x + 2*y)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : y≠0 := by
    intro he
    apply n13
    linear_combination (4*x - y)*he
  have h8 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g2
  have h6 := (mul_eq_zero.mp h8).resolve_left h7
  have h9 : (1:ℝ)=0 := by linear_combination (x/3 - 1/3)*h1 + (1/3)*h4 + (-2/3)*h6
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0000111222 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : x^2*y - 4*x*y + 2*y^2=0) (g2 : 2*x^2*y - 8*x*y + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : 4*x*y - y^2≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 3*y^2≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (3*y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x^2 - 4*x + 2*y)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left h2
  have h8 : x^2 - 4*x=0 := by linear_combination (-1)*h4 + (2)*h6
  have h9 : y=0 := by linear_combination (1)*h4 + (-1)*h6
  have h11 : x≠0 := by
    intro he
    apply n7
    linear_combination (4 - x)*he
  have h12 : x - (4:ℝ)≠0 := by
    intro he
    apply n7
    linear_combination (-x)*he
  have h13 : ((x) * (x - 4))*(1)=0 := by linear_combination (1)*h8
  have h10 := (mul_eq_zero.mp h13).resolve_left (mul_ne_zero h11 h12)
  have h15 : ((y))*(1)=0 := by linear_combination (1)*h9
  have h14 := (mul_eq_zero.mp h15).resolve_left h2
  have h16 : (1:ℝ)=0 := by linear_combination (1)*h10
  have h17 : (1:ℝ)=0 := by linear_combination (1)*h16
  have h18 : (1:ℝ)=0 := by linear_combination (1)*h17
  norm_num at h16



private lemma base_0000112211 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : x*y^2 - 2*y^2=0) (g2 : 2*x^2*y - 8*x*y + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -y^2 + 4*y≠0) (n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : 4*x*y - y^2≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 4*x*y - y^2≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y) * (y))*(x - 2)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left (mul_ne_zero h2 h2)
  have h7 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left h2
  have h8 : x - (2:ℝ)=0 := by linear_combination (1)*h4
  have h9 : y - (4:ℝ)=0 := by linear_combination (2 - x)*h4 + (1)*h6
  have h10 : x - (2:ℝ)=0 := by linear_combination (1)*h8
  have h12 : y - (4:ℝ)≠0 := by
    intro he
    apply n8
    linear_combination (-y)*he
  have h13 : ((y - 4))*(1)=0 := by linear_combination (1)*h9
  have h11 := (mul_eq_zero.mp h13).resolve_left h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h11
  have h15 : (1:ℝ)=0 := by linear_combination (1)*h14
  have h16 : (1:ℝ)=0 := by linear_combination (1)*h15
  norm_num at h14



private lemma shape_0000001222 (x y : ℝ) (ha : admissible ![0,0,0,0,0,0,1,2,2,2] x y) : False := by
  apply base_0000001222 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y 1 x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000011110 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,1,1,1,0] x y) : False := by
  apply base_0000011110 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000011111 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,1,1,1,1] x y) : False := by
  apply base_0000011111 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000011112 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,1,1,1,2] x y) : False := by
  apply base_0000011112 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000011121 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,1,1,2,1] x y) : False := by
  apply base_0000011121 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000011122 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,1,1,2,2] x y) : False := by
  apply base_0000011122 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000011220 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,1,2,2,0] x y) : False := by
  apply base_0000011220 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 x y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000011221 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,1,2,2,1] x y) : False := by
  apply base_0000011221 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 x y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000012121 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,2,1,2,1] x y) : False := by
  apply base_0000012121 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 y y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y y 1 y y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000012210 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,2,2,1,0] x y) : False := by
  apply base_0000012210 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 y x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y x 1 y x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000111111 (x y : ℝ) (ha : admissible ![0,0,0,0,1,1,1,1,1,1] x y) : False := by
  apply base_0000111111 x y
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x 1 x x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000111112 (x y : ℝ) (ha : admissible ![0,0,0,0,1,1,1,1,1,2] x y) : False := by
  apply base_0000111112 x y
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x 1 x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000111122 (x y : ℝ) (ha : admissible ![0,0,0,0,1,1,1,1,2,2] x y) : False := by
  apply base_0000111122 x y
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x 1 x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000111222 (x y : ℝ) (ha : admissible ![0,0,0,0,1,1,1,2,2,2] x y) : False := by
  apply base_0000111222 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y 1 x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000112211 (x y : ℝ) (ha : admissible ![0,0,0,0,1,1,2,2,1,1] x y) : False := by
  apply base_0000112211 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y 1 y x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y x 1 y x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma base_0001001012 (x y : ℝ) (g0 : (-4:ℝ)=0) (g1 : -3*x + 3*y - (1:ℝ)=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : (3:ℝ)≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : (3:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : (1:ℝ)=0 := by linear_combination (-1/4)*g0
  have h2 : x - y + 1/(3:ℝ)=0 := by linear_combination (-1/3)*g1
  have h3 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h1
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001001022 (x y : ℝ) (g0 : (-4:ℝ)=0) (g1 : -2*x + 2*y - (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : (3:ℝ)≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : (3:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : (1:ℝ)=0 := by linear_combination (-1/4)*g0
  have h2 : x - y + 1/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h1
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001001100 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -2*x^2 + x=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 4*x≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 4*x≠0) (n14 : -x^2 + 4*x≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x - 1/2)=0 := by linear_combination (-1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-2/5)*h1 + (2/5)*h4
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001001101 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -2*x^2 + 4*x - (3:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 4*x≠0) (n12 : -x^2 + 4*x≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 - 2*x + 3/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h5 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (x/2 - 1/2)*h1 + (-1/2)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001001102 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -2*x^2 + x + 3*y - (3:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 4*x≠0) (n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 - x/2 - 3*y/2 + 3/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h5 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (x/2 - 1/2)*h1 + (-1/2)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001001112 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -4*x + 3*y=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n11 : -x^2 + 4*x≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*x*y - y^2≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n11
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x - 3*y/(4:ℝ)=0 := by linear_combination (-1/4)*g1
  have h5 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (-3/8)*h1 + (3/8)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001001122 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -2*x^2 + 2*x*y - x=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 4*x≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x - y + 1/2)=0 := by linear_combination (-1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-4/11)*h1 + (4*x/33 - 4*y/33 + 2/33)*h4 + (-4/33)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001001200 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : -2*x*y + y=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -y^2 + 4*y≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 4*x≠0) (n14 : -y^2 + 4*y≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (4 - y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x - 1/2)=0 := by linear_combination (-1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (4*x/3 - 14/3)*h4 + (-4/3)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001001201 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : -2*x*y + 3*x + y - (3:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (n11 : -y^2 + 4*y≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4 - y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x*y - 3*x/2 - y/2 + 3/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h5 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (2*x^2/3 - 3*x + 4/3)*h1 + (8/3 - 2*x/3)*h4 + (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001001202 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : -2*x*y + 4*y - (3:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n11 : -y^2 + 4*y≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4 - y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x*y - 2*y + 3/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h5 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (-4*x^2/33 + 6*x/11 - 20/33)*h1 + (4*x/33 - 10/33)*h4 + (-4/11)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001001212 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : -3*x + 2*y=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n11 : -y^2 + 4*y≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4 - y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x - 2*y/(3:ℝ)=0 := by linear_combination (-1/3)*g1
  have h5 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (-2/5)*h1 + (-3/5)*h4 + (3/5)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001001222 (x y : ℝ) (g0 : 2*y^2 - 6*y=0) (g1 : -2*x*y + 2*y^2 - y=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -y^2 + 4*y≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : 3*y^2≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (3*y)*he
  have h3 : ((y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x - y + 1/2)=0 := by linear_combination (-1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-4*x/27 + 4*y/27 - 14/27)*h1 + (4*x/27 - 22/27)*h4 + (-4/27)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001002100 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -x^2 - x*y + x=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 4*x≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : -y^2 + 4*y≠0) (n14 : -x^2 + 4*x≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x + y - 1)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (y/6 - 1/2)*h1 + (-x/18 - y/18 + 5/9)*h4 + (1/18)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001002101 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -x^2 - x*y + 4*x - (3:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (n11 : -x^2 + 4*x≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n11
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 + x*y - 4*x + (3:ℝ)=0 := by linear_combination (-1)*g1
  have h5 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (x*y/12 - 2*x/3 + y^2/12 - y/4 + 1/6)*h1 + (5/12 - y/12)*h4 + (1/4)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  norm_num at h6



private lemma base_0001002102 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -x^2 - x*y + x + 3*y - (3:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n11 : -x^2 + 4*x≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : 4*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n11
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 + x*y - x - 3*y + (3:ℝ)=0 := by linear_combination (-1)*g1
  have h5 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (-x/9 - y/9 - 2/9)*h1 + (1/9)*h4
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  norm_num at h6



private lemma base_0001002111 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : x^2 - x*y - x=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 4*x≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : 3*x^2≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (3*x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x - y - 1)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-1/2)*h1 + (x/6 - y/6 + 1/3)*h4 + (-1/6)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001002112 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : x^2 - x*y - 4*x + 3*y=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n11 : -x^2 + 4*x≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*y - (1:ℝ)≠0) (_n14 : 4*x*y - y^2≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n11
    linear_combination (4 - x)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h5 : (1:ℝ)=0 := by linear_combination (x/3 - y/3 - 1/3)*h1 + (-1/3)*g1
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001002122 (x y : ℝ) (g0 : 2*x^2 - 6*x=0) (g1 : -x^2 + x*y - x=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 4*x≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : 4*y - (1:ℝ)≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x - y + 1)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-1/3)*h1 + (x/9 - y/9 + 1/9)*h4 + (-1/9)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma shape_0001001012 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,0,1,2] x y) : False := by
  apply base_0001001012 x y
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 x x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x x x x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001022 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,0,2,2] x y) : False := by
  apply base_0001001022 x y
  · have hg : gram 1 1 1 1 1 1 1 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 1 x x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001100 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,1,0,0] x y) : False := by
  apply base_0001001100 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x x 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x 1 x x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001101 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,1,0,1] x y) : False := by
  apply base_0001001101 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x x 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x 1 x x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001102 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,1,0,2] x y) : False := by
  apply base_0001001102 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x x 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x 1 x x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001112 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,1,1,2] x y) : False := by
  apply base_0001001112 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x x x x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001122 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,1,2,2] x y) : False := by
  apply base_0001001122 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001200 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,2,0,0] x y) : False := by
  apply base_0001001200 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y x x 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x 1 x x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001201 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,2,0,1] x y) : False := by
  apply base_0001001201 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y x x 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x 1 x x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001202 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,2,0,2] x y) : False := by
  apply base_0001001202 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y x x 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x 1 x x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001212 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,2,1,2] x y) : False := by
  apply base_0001001212 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y x x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x x x x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001001222 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,1,2,2,2] x y) : False := by
  apply base_0001001222 x y
  · have hg : gram 1 1 1 1 1 y 1 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 y x x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001002100 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,2,1,0,0] x y) : False := by
  apply base_0001002100 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x y 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y 1 x y 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001002101 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,2,1,0,1] x y) : False := by
  apply base_0001002101 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x y 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y 1 x y 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001002102 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,2,1,0,2] x y) : False := by
  apply base_0001002102 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x y 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y 1 x y 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001002111 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,2,1,1,1] x y) : False := by
  apply base_0001002111 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x y x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y x x y x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001002112 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,2,1,1,2] x y) : False := by
  apply base_0001002112 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x y x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y x x y x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001002122 (x y : ℝ) (ha : admissible ![0,0,0,1,0,0,2,1,2,2] x y) : False := by
  apply base_0001002122 x y
  · have hg : gram 1 1 1 1 1 x 1 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 1 x x y y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma base_0001010110 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -x^2 - 2*x + (2:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 4*x≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 + 2*x - (2:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (2*x/9 - 7/9)*h2 + (-2*x/9 - 5/9)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001010111 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -x^2 + x - (1:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 3*x^2≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x + (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (4/3 - x/3)*h2 + (x/3 - 1/3)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001010120 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -2*x^2 + x*y - 2*y + (2:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : -x^2 + 4*x≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y/2 + y - (1:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-x*y^2/27 + 11*x*y/27 - x/2 + 2*y^3/27 - 2*y^2/3 + 43*y/27)*h1 + (2*x*y^2/27 - 22*x*y/27 + x - 2*y^3/27 + 10*y^2/27 + 11*y/9 - 2)*h2 + (-x*y^2/27 + 11*x*y/27 - x/2 + 2*y^2/27 - 10*y/27 - 1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001010121 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -2*x^2 + x*y + 3*x - 2*y - (1:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*x*y - y^2≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y/2 - 3*x/2 + y + 1/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (x^2/6 - 11*x*y/18 + 11*x/18 + 5*y^2/9 - 23*y/18 - 23/18)*h1 + (-x^2/3 + 8*x*y/9 - 5*x/9 - 5*y^2/9 - y/9 + 8/3)*h2 + (x^2/6 - 5*x*y/18 + 4*x/9 + 5*y/9 + 17/18)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001010122 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -2*x^2 + x*y + y - (1:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y/2 - y/2 + 1/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (x*y^2/18 - 4*x*y/9 + 4*x/9 - y^3/9 + y^2/2 - 5*y/18 + 8/9)*h1 + (-x*y^2/9 + 8*x*y/9 - 8*x/9 + y^3/9 - 2*y^2/9 - 22*y/9 + 10/3)*h2 + (x*y^2/18 - 4*x*y/9 + 4*x/9 + y^2/18 + y/18 - 14/9)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001010222 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 - 2*x*y + 2*x + 2*y^2 - y - (1:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n12 : -y^2 + 4*y≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : 3*y^2≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 + 2*x*y - 2*x - 2*y^2 + y + (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x^2 - 2*x - y + (1:ℝ)=0 := by linear_combination (1/3)*h2 + (2/3)*h3
  have h5 : x*y - y^2 + y=0 := by linear_combination (1/3)*h2 + (-1/3)*h3
  have h6 : y^3 - 5*y^2 + 4*y=0 := by linear_combination (1 - x/3)*h2 + (x/3 + y - 1)*h3
  have h7 : x^2 - 2*x - y + (1:ℝ)=0 := by linear_combination (1)*h4
  have h9 : y≠0 := by
    intro he
    apply n14
    linear_combination (3*y)*he
  have h10 : ((y))*(x - y + 1)=0 := by linear_combination (1)*h5
  have h8 := (mul_eq_zero.mp h10).resolve_left h9
  have h12 : y - (4:ℝ)≠0 := by
    intro he
    apply n12
    linear_combination (-y)*he
  have h13 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h14 : ((y - 4) * (y - 1) * (y))*(1)=0 := by linear_combination (1)*h6
  have h11 := (mul_eq_zero.mp h14).resolve_left (mul_ne_zero (mul_ne_zero h12 h13) h9)
  have h15 : (1:ℝ)=0 := by linear_combination (1)*h11
  have h16 : (1:ℝ)=0 := by linear_combination (1)*h15
  have h17 : (1:ℝ)=0 := by linear_combination (1)*h16
  norm_num at h15



private lemma base_0001011110 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : 4 - 5*x=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x - 4/(5:ℝ)=0 := by linear_combination (-1/5)*g1
  have h3 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-15/7)*h2 + (15/7)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001011112 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -5*x + 3*y + (1:ℝ)=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (_n14 : 4*x*y - y^2≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x - 3*y/5 - 1/(5:ℝ)=0 := by linear_combination (-1/5)*g1
  have h3 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-9/2)*h1 + (9*x/2 - 33/2)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001011120 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -x^2 + x*y - 3*x - 2*y + (4:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y + 3*x + 2*y - (4:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (x^2/6 - 17*x*y/72 + 29*x/24 + 5*y^2/72 - 31*y/72 - 15/8)*h1 + (-x^2/3 + 11*x*y/36 + 5*x/4 - 5*y^2/72 - 13*y/24 - 1/2)*h2 + (x^2/6 - 5*x*y/72 - 11*x/24 + 5*y/36 + 7/8)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001011122 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -x^2 + x*y - 3*x + y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y + 3*x - y - (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-x^2/3 + 19*x*y/36 - 65*x/36 - 7*y^2/36 + 10*y/9 - 35/18)*h1 + (2*x^2/3 - 13*x*y/18 - 31*x/18 + 7*y^2/36 + 37*y/36 - 4/3)*h2 + (-x^2/3 + 7*x*y/36 - 17*x/36 + 7*y/36 + 29/18)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001011200 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : x^2 - 2*x*y - 3*x + y + (2:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : -y^2 + 4*y≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : (1:ℝ)=0 := by linear_combination (-2*x*y^2/27 + 10*x*y/27 - x/9 + y^2/27 - 7*y/54 - 1/9)*h1 + (x*y^2/27 - 5*x*y/27 + x/18 - y^3/27 + 13*y^2/54 - y/2 + 5/6)*g1 + (x*y^2/27 - 5*x*y/27 + x/18 + y^3/27 - y^2/6 + 2*y/27 - 5/9)*h2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  norm_num at h3



private lemma base_0001011202 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : x^2 - 2*x*y - 3*x + 4*y - (1:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : 4*x*y - y^2≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : (1:ℝ)=0 := by linear_combination (8*x*y^2/27 - 32*x*y/27 + 38*x/27 - 16*y^2/27 + 64*y/27 - 112/27)*h1 + (-4*x*y^2/27 + 16*x*y/27 - 19*x/27 + 4*y^3/27 - 22*y^2/27 + 52*y/27 - 14/9)*g1 + (-4*x*y^2/27 + 16*x*y/27 - 19*x/27 - 4*y^3/27 + 26*y^2/27 - 68*y/27 + 97/27)*h2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  norm_num at h3



private lemma shape_0001010110 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,0,1,1,0] x y) : False := by
  apply base_0001010110 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x 1 x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x 1 x x 1 x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001010111 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,0,1,1,1] x y) : False := by
  apply base_0001010111 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x 1 x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x 1 x x 1 x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001010120 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,0,1,2,0] x y) : False := by
  apply base_0001010120 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x 1 y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x 1 y x 1 y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001010121 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,0,1,2,1] x y) : False := by
  apply base_0001010121 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x 1 y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x 1 y x 1 y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001010122 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,0,1,2,2] x y) : False := by
  apply base_0001010122 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x 1 y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x 1 y x 1 y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001010222 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,0,2,2,2] x y) : False := by
  apply base_0001010222 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x 1 y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x 1 y x 1 y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001011110 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,1,1,0] x y) : False := by
  apply base_0001011110 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x x x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x x x x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001011112 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,1,1,2] x y) : False := by
  apply base_0001011112 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x x x x x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001011120 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,1,2,0] x y) : False := by
  apply base_0001011120 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x x y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001011122 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,1,2,2] x y) : False := by
  apply base_0001011122 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001011200 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,2,0,0] x y) : False := by
  apply base_0001011200 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x x 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x 1 x x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001011202 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,2,0,2] x y) : False := by
  apply base_0001011202 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x x 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x 1 x x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


end Erdos1082Ten

open Erdos1082Ten EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H1_R1.H2 := by
  intro B hn _ _ p r c hc hh
  obtain ⟨s,x,y,_,H,_,_⟩ := given_colors B hn p r c hc
  change colorCode c∈([0,1,4,5,13,14,31,32,36,37,38,40,41,44,45,46,49,50,53,120,121,122,124,125,132,133,151,156,364,365,368,377,400,761,764,765,766,767,770,773,774,775,776,779,782,792,793,794,796,797,800,822,823,825,826,827,836,849,851,852,854,855,857]:List ℕ) at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq
  · have cc : c=![0,0,0,0,0,0,0,0,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000000000 x y H
  · have cc : c=![0,0,0,0,0,0,0,0,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000000001 x y H
  · have cc : c=![0,0,0,0,0,0,0,0,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000000011 x y H
  · have cc : c=![0,0,0,0,0,0,0,0,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000000012 x y H
  · have cc : c=![0,0,0,0,0,0,0,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000000111 x y H
  · have cc : c=![0,0,0,0,0,0,0,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000000112 x y H
  · have cc : c=![0,0,0,0,0,0,1,0,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001011 x y H
  · have cc : c=![0,0,0,0,0,0,1,0,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001012 x y H
  · have cc : c=![0,0,0,0,0,0,1,1,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001100 x y H
  · have cc : c=![0,0,0,0,0,0,1,1,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001101 x y H
  · have cc : c=![0,0,0,0,0,0,1,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001102 x y H
  · have cc : c=![0,0,0,0,0,0,1,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001111 x y H
  · have cc : c=![0,0,0,0,0,0,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001112 x y H
  · have cc : c=![0,0,0,0,0,0,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001122 x y H
  · have cc : c=![0,0,0,0,0,0,1,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001200 x y H
  · have cc : c=![0,0,0,0,0,0,1,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001201 x y H
  · have cc : c=![0,0,0,0,0,0,1,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001211 x y H
  · have cc : c=![0,0,0,0,0,0,1,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001212 x y H
  · have cc : c=![0,0,0,0,0,0,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000001222 x y H
  · have cc : c=![0,0,0,0,0,1,1,1,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000011110 x y H
  · have cc : c=![0,0,0,0,0,1,1,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000011111 x y H
  · have cc : c=![0,0,0,0,0,1,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000011112 x y H
  · have cc : c=![0,0,0,0,0,1,1,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000011121 x y H
  · have cc : c=![0,0,0,0,0,1,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000011122 x y H
  · have cc : c=![0,0,0,0,0,1,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000011220 x y H
  · have cc : c=![0,0,0,0,0,1,1,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000011221 x y H
  · have cc : c=![0,0,0,0,0,1,2,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000012121 x y H
  · have cc : c=![0,0,0,0,0,1,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000012210 x y H
  · have cc : c=![0,0,0,0,1,1,1,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000111111 x y H
  · have cc : c=![0,0,0,0,1,1,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000111112 x y H
  · have cc : c=![0,0,0,0,1,1,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000111122 x y H
  · have cc : c=![0,0,0,0,1,1,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000111222 x y H
  · have cc : c=![0,0,0,0,1,1,2,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0000112211 x y H
  · have cc : c=![0,0,0,1,0,0,1,0,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001012 x y H
  · have cc : c=![0,0,0,1,0,0,1,0,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001022 x y H
  · have cc : c=![0,0,0,1,0,0,1,1,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001100 x y H
  · have cc : c=![0,0,0,1,0,0,1,1,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001101 x y H
  · have cc : c=![0,0,0,1,0,0,1,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001102 x y H
  · have cc : c=![0,0,0,1,0,0,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001112 x y H
  · have cc : c=![0,0,0,1,0,0,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001122 x y H
  · have cc : c=![0,0,0,1,0,0,1,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001200 x y H
  · have cc : c=![0,0,0,1,0,0,1,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001201 x y H
  · have cc : c=![0,0,0,1,0,0,1,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001202 x y H
  · have cc : c=![0,0,0,1,0,0,1,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001212 x y H
  · have cc : c=![0,0,0,1,0,0,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001001222 x y H
  · have cc : c=![0,0,0,1,0,0,2,1,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001002100 x y H
  · have cc : c=![0,0,0,1,0,0,2,1,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001002101 x y H
  · have cc : c=![0,0,0,1,0,0,2,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001002102 x y H
  · have cc : c=![0,0,0,1,0,0,2,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001002111 x y H
  · have cc : c=![0,0,0,1,0,0,2,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001002112 x y H
  · have cc : c=![0,0,0,1,0,0,2,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001002122 x y H
  · have cc : c=![0,0,0,1,0,1,0,1,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001010110 x y H
  · have cc : c=![0,0,0,1,0,1,0,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001010111 x y H
  · have cc : c=![0,0,0,1,0,1,0,1,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001010120 x y H
  · have cc : c=![0,0,0,1,0,1,0,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001010121 x y H
  · have cc : c=![0,0,0,1,0,1,0,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001010122 x y H
  · have cc : c=![0,0,0,1,0,1,0,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001010222 x y H
  · have cc : c=![0,0,0,1,0,1,1,1,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011110 x y H
  · have cc : c=![0,0,0,1,0,1,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011112 x y H
  · have cc : c=![0,0,0,1,0,1,1,1,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011120 x y H
  · have cc : c=![0,0,0,1,0,1,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011122 x y H
  · have cc : c=![0,0,0,1,0,1,1,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011200 x y H
  · have cc : c=![0,0,0,1,0,1,1,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011202 x y H
