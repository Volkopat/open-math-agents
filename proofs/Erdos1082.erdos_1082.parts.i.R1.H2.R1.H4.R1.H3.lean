import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1
/-!
# Uniqueness of a two-distance five-point completion

Three colors suffice for the distances of any diameter-free five-vertex subset of a ten-point
four-distance configuration. We minimize the ternary code over permutations and classify the
patterns using at most two colors. Only the pentagon is realizable. The three squared distances
to noncollinear anchors fix a point uniquely. Its distances to the fourth shared vertex exclude
all profiles except that of the original fifth vertex.

The code-minimization and Gram identities below check the finite classification directly.
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


abbrev Triple := ℝ×ℝ×ℝ

def dataTriple (s : ℝ) (o e f x : ℝ²) : Triple := (s*dsq o x,s*dsq e x,s*dsq f x)

def locus (a b c : ℝ) (p : Triple) := gram a b c p.1 p.2.1 p.2.2 p.1 p.2.1 p.2.2 0

def sep4 (a b c : ℝ) (p q : Triple) :=
  let u := (p.1-p.2.1)-(q.1-q.2.1)
  let v := (p.1-p.2.2)-(q.1-q.2.2)
  2*b*u*u-2*(a+b-c)*u*v+2*a*v*v

def edge4 (a b c : ℝ) (p q : Triple) (x y t : ℝ) :=
  let d := 2*area a b c
  let l := sep4 a b c p q
  (l-d)*(l-d*x)*(l-d*y)*(l-d*t)

lemma geom_locus (s : ℝ) (o e f x : ℝ²) :
    locus (s*dsq o e) (s*dsq o f) (s*dsq e f) (dataTriple s o e f x)=0 := by
  have h := gram_identity o e f x x s
  simpa [locus,dataTriple,dsq] using h

lemma geom_sep4 (s : ℝ) (o e f x y : ℝ²) :
    sep4 (s*dsq o e) (s*dsq o f) (s*dsq e f) (dataTriple s o e f x) (dataTriple s o e f y)=
    2*area (s*dsq o e) (s*dsq o f) (s*dsq e f)*(s*dsq x y) := by
  unfold sep4 dataTriple dsq area
  ring

lemma geom_edge4 (s : ℝ) (o e f u v : ℝ²) (x y t : ℝ)
    (h : s*dsq u v=1 ∨ s*dsq u v=x ∨ s*dsq u v=y ∨ s*dsq u v=t) :
    edge4 (s*dsq o e) (s*dsq o f) (s*dsq e f) (dataTriple s o e f u) (dataTriple s o e f v) x y t=0 := by
  unfold edge4
  rw [geom_sep4]
  rcases h with h|h|h|h <;> rw [h] <;> ring

lemma geom_injective (s : ℝ) (hs : s≠0) (o e f : ℝ²) (hoe : o≠e)
    (hn : ¬Collinear ℝ ({o,e,f}:Set ℝ²)) : Function.Injective (dataTriple s o e f) := by
  intro x y he
  have hh := geom_sep4 s o e f x y
  rw [he] at hh
  simp [sep4] at hh
  have h0 := area_ne o e f s hs hoe hn
  have hz := (hh.resolve_left h0).resolve_left hs
  rw [dsq_eq] at hz
  exact dist_eq_zero.mp (sq_eq_zero_iff.mp hz)

def palette4 (x y t : ℝ) : Fin 4→ℝ := ![1,x,y,t]

def profile4 (x y t : ℝ) (k : Fin 64) : Triple :=
  (palette4 x y t ⟨k.val/16,by omega⟩,palette4 x y t ⟨k.val/4%4,by omega⟩,palette4 x y t ⟨k.val%4,by omega⟩)

lemma profile4_surjective (x y t : ℝ) (a b c : Fin 4) :
    ∃ k : Fin 64, profile4 x y t k=(palette4 x y t a,palette4 x y t b,palette4 x y t c) := by
  let k : Fin 64 := ⟨16*a.val+4*b.val+c.val,by omega⟩
  have ha : k.val/16=a.val := by dsimp [k]; omega
  have hb : k.val/4%4=b.val := by dsimp [k]; omega
  have hc : k.val%4=c.val := by dsimp [k]; omega
  exact ⟨k, by simp [profile4,ha,hb,hc]⟩

def cell (a b c : ℝ) (p q r : Triple) (x y t : ℝ) :=
  locus a b c p=0 ∧ edge4 a b c p q x y t=0 ∧ edge4 a b c p r x y t=0


open EuclideanGeometry
def colorCode (c : Fin 10→Fin 3) : ℕ := (c 0).val*19683+(c 1).val*6561+(c 2).val*2187+(c 3).val*729+(c 4).val*243+(c 5).val*81+(c 6).val*27+(c 7).val*9+(c 8).val*3+(c 9).val*1
def slot : Fin 5→Fin 5→Fin 10 := ![![0,0,1,2,3],![0,0,4,5,6],![1,4,0,7,8],![2,5,7,0,9],![3,6,8,9,0]]
def permColors (c : Fin 10→Fin 3) (p : Fin 5→Fin 5) (s : Fin 3→Fin 3) : Fin 10→Fin 3 := ![s (c (slot (p 0) (p 1))),s (c (slot (p 0) (p 2))),s (c (slot (p 0) (p 3))),s (c (slot (p 0) (p 4))),s (c (slot (p 1) (p 2))),s (c (slot (p 1) (p 3))),s (c (slot (p 1) (p 4))),s (c (slot (p 2) (p 3))),s (c (slot (p 2) (p 4))),s (c (slot (p 3) (p 4)))]
def minimalColor (c : Fin 10→Fin 3) := ∀ (p : Fin 5→Fin 5) (s : Fin 3→Fin 3), Function.Injective p → Function.Injective s → colorCode c≤colorCode (permColors c p s)
def baseCodes : List ℕ := [0,1,4,5,13,14,31,32,36,37,38,40,41,44,45,46,49,50,53,120,121,122,123,124,125,132,133,151,156,157,364,365,368,377,400,401,761,764,765,766,767,770,773,774,775,776,779,782,792,793,794,796,797,800,822,823,824,825,826,827,834,835,836,849,851,852,853,854,855,857,858,860,861,862,863,879,880,881,882,883,885,886,887,888,889,890,912,913,939,941,942,943,969,970,1062,1064,1070,1071,1072,1073,1075,1076,1079,1100,1106,1124,1125,1126,1127,1129,1130,1152,1153,1155,1157,1158,1159,1185,1212,1213,1395,1396,3048,3050,3072,3074,3075,3194,3195,3197,3203,3206,3231,3233,3234,3236,3237,3399,3437,3440,3801,3961]

lemma slot_symm (i j : Fin 5) : slot i j=slot j i := by decide +revert

lemma perm_slot (c : Fin 10→Fin 3) (p : Fin 5→Fin 5) (s : Fin 3→Fin 3) (i j : Fin 5) (h : i≠j) :
    permColors c p s (slot i j)=s (c (slot (p i) (p j))) := by
  fin_cases i <;> fin_cases j <;> first | exact False.elim (h rfl) | rfl | exact congrArg (fun k => s (c k)) (slot_symm _ _)

lemma lookup_sym (k : Fin 5→Fin 5→Fin 3) (hs : ∀ i j,k i j=k j i) (i j : Fin 5) (h : i≠j) :
    (![k 0 1,k 0 2,k 0 3,k 0 4,k 1 2,k 1 3,k 1 4,k 2 3,k 2 4,k 3 4] : Fin 10→Fin 3) (slot i j)=k i j := by
  fin_cases i <;> fin_cases j <;> first | exact False.elim (h rfl) | rfl | exact hs _ _

def realizes (B : Finset ℝ²) (D : Finset ℝ) (c : Fin 10→Fin 3) :=
  ∃ (v : Fin 5≃B) (r : Fin 3≃D), ∀ i j : Fin 5, i≠j →
    (r (c (slot i j))).1=dist (v i).1 (v j).1

lemma minimal_realization (B : Finset ℝ²) (D : Finset ℝ) (hB : B.card=5) (hD : D.card=3)
    (hBD : ∀ x∈B, ∀ y∈B, x≠y → dist x y∈D) : ∃ c, realizes B D c ∧ minimalColor c := by
  classical
  let V := (B.equivFinOfCardEq hB).symm
  let R := (D.equivFinOfCardEq hD).symm
  let k (i j : Fin 5) := if h : i≠j then R.symm ⟨dist (V i).1 (V j).1,hBD _ (V i).2 _ (V j).2
    (fun he => h (V.injective (Subtype.ext he)))⟩ else 0
  have sym (i j : Fin 5) : k i j=k j i := by
    by_cases he : i=j
    · subst j; rfl
    · have hf : j≠i := Ne.symm he
      simp only [k,dif_pos he,dif_pos hf]
      apply congrArg R.symm
      apply Subtype.ext
      exact dist_comm ..
  let c₀ : Fin 10→Fin 3 := ![k 0 1,k 0 2,k 0 3,k 0 4,k 1 2,k 1 3,k 1 4,k 2 3,k 2 4,k 3 4]
  have hlookup (i j : Fin 5) (hij : i≠j) : c₀ (slot i j)=k i j := by
    apply lookup_sym k sym i j hij
  let L := Finset.univ.filter (realizes B D)
  have h₀ : realizes B D c₀ := by
    refine ⟨V,R,?_⟩
    intro i j hij
    rw [hlookup _ _ hij]
    simp [k,hij]
  have hl : L.Nonempty := ⟨c₀,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h₀⟩⟩
  obtain ⟨c,hc,hm⟩ := Finset.exists_min_image L colorCode hl
  have hreal := (Finset.mem_filter.mp hc).2
  refine ⟨c,hreal,?_⟩
  rintro p s hp hs
  let P : Fin 5≃Fin 5 := Equiv.ofBijective p ⟨hp,Finite.injective_iff_surjective.mp hp⟩
  let S : Fin 3≃Fin 3 := Equiv.ofBijective s ⟨hs,Finite.injective_iff_surjective.mp hs⟩
  apply hm
  apply Finset.mem_filter.mpr
  obtain ⟨v,r,hr⟩ := hreal
  refine ⟨Finset.mem_univ _,P.trans v,S.symm.trans r,?_⟩
  intro i j hij
  rw [perm_slot _ _ _ _ _ hij]
  change (r (S.symm (S (c (slot (p i) (p j)))))).1=dist (v (p i)).1 (v (p j)).1
  rw [S.symm_apply_apply]
  exact hr _ _ (fun he => hij (hp he))

def palette3 (x y : ℝ) : Fin 3→ℝ := ![1,x,y]

def baseD (c : Fin 10→Fin 3) (x y : ℝ) (i j : Fin 5) := palette3 x y (c (slot i j))

def baseT (c : Fin 10→Fin 3) (x y : ℝ) (i : Fin 5) : Triple :=
  (baseD c x y 0 i,baseD c x y 1 i,baseD c x y 2 i)

def threeGram (d : Fin 5→Fin 5→ℝ) (i j : Fin 5) :=
  gram (d 0 1) (d 0 2) (d 1 2) (d 0 i) (d 1 i) (d 2 i) (d 0 j) (d 1 j) (d 2 j) (if i=j then 0 else d i j)

def admissible (c : Fin 10→Fin 3) (x y : ℝ) :=
  let d := baseD c x y
  (x≠0 ∧ y≠0 ∧ x-1≠0 ∧ y-1≠0 ∧ x-y≠0) ∧
    (∀ i j k : Fin 5, i<j → j<k → area (d i j) (d i k) (d j k)≠0) ∧
    threeGram d 3 3=0 ∧ threeGram d 3 4=0 ∧ threeGram d 4 4=0

def hasExtension (c : Fin 10→Fin 3) (x y t : ℝ) :=
  let d := baseD c x y
  ∃ g : Fin 5→Fin 64, Function.Injective g ∧
    (∀ i, cell (d 0 1) (d 0 2) (d 1 2) (profile4 x y t (g i)) (baseT c x y 3) (baseT c x y 4) x y t) ∧
    (∀ i j, i≠j → edge4 (d 0 1) (d 0 2) (d 1 2) (profile4 x y t (g i)) (profile4 x y t (g j)) x y t=0)

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

lemma palette4_or (x y t : ℝ) (k : Fin 4) :
    palette4 x y t k=1 ∨ palette4 x y t k=x ∨ palette4 x y t k=y ∨ palette4 x y t k=t := by
  fin_cases k <;> simp [palette4]

lemma build_extension (c : Fin 10→Fin 3) (x y t s : ℝ) (p q : Fin 5→ℝ²) (hq : Function.Injective q)
    (hs : s≠0) (hoe : p 0≠p 1) (hn : ¬Collinear ℝ ({p 0,p 1,p 2}:Set ℝ²))
    (hb : ∀ i j, i≠j → baseD c x y i j=s*dsq (p i) (p j))
    (hd : ∀ i j, ∃ k, s*dsq (p i) (q j)=palette4 x y t k)
    (he : ∀ i j, i≠j → ∃ k, s*dsq (q i) (q j)=palette4 x y t k) : hasExtension c x y t := by
  classical
  have hp (j : Fin 5) : ∃ k, profile4 x y t k=dataTriple s (p 0) (p 1) (p 2) (q j) := by
    obtain ⟨a,ha⟩ := hd 0 j
    obtain ⟨b,hb⟩ := hd 1 j
    obtain ⟨k,hk⟩ := hd 2 j
    rw [dataTriple,ha,hb,hk]
    exact profile4_surjective x y t a b k
  let g (i : Fin 5) := (hp i).choose
  have gg (i : Fin 5) : profile4 x y t (g i)=dataTriple s (p 0) (p 1) (p 2) (q i) := (hp i).choose_spec
  have h03 : baseT c x y 3=dataTriple s (p 0) (p 1) (p 2) (p 3) := by
    simp only [baseT,dataTriple,hb 0 3 (by decide),hb 1 3 (by decide),hb 2 3 (by decide)]
  have h04 : baseT c x y 4=dataTriple s (p 0) (p 1) (p 2) (p 4) := by
    simp only [baseT,dataTriple,hb 0 4 (by decide),hb 1 4 (by decide),hb 2 4 (by decide)]
  have hrev (u v : ℝ²) : dsq u v=dsq v u := by rw [dsq_eq,dsq_eq,dist_comm]
  have hpoint (i j : Fin 5) : s*dsq (q i) (p j)=1 ∨ s*dsq (q i) (p j)=x ∨
      s*dsq (q i) (p j)=y ∨ s*dsq (q i) (p j)=t := by
    obtain ⟨k,hk⟩ := hd j i
    rw [hrev,hk]
    exact palette4_or x y t k
  refine ⟨g,?_,?_,?_⟩
  · intro i j hij
    apply hq
    apply geom_injective s hs (p 0) (p 1) (p 2) hoe hn
    rw [←gg,←gg,hij]
  · intro i
    rw [gg,h03,h04,hb 0 1 (by decide),hb 0 2 (by decide),hb 1 2 (by decide)]
    exact ⟨geom_locus ..,geom_edge4 _ _ _ _ _ _ _ _ _ (hpoint i 3),geom_edge4 _ _ _ _ _ _ _ _ _ (hpoint i 4)⟩
  · intro i j hij
    rw [gg,gg,hb 0 1 (by decide),hb 0 2 (by decide),hb 1 2 (by decide)]
    apply geom_edge4
    obtain ⟨k,hk⟩ := he i j hij
    rw [hk]
    exact palette4_or x y t k


lemma normalized_five (A B : Finset ℝ²) (M : ℝ) (hM : M∈distanceSet A) (hBA : B⊆A)
    (hA : A.card=10) (hB : B.card=5) (hD : distinctDistances A=4)
    (hnc : NonTrilinear (A:Set ℝ²)) (hdiam : ∀ u∈B, ∀ v∈B, dist u v<M) :
    ∃ (c : Fin 10→Fin 3) (p : Fin 5≃B) (s x y t : ℝ),
      s≠0 ∧ minimalColor c ∧ admissible c x y ∧ hasExtension c x y t ∧
      t-1≠0 ∧ t-x≠0 ∧ t-y≠0 ∧ t≠0 ∧
      ∀ i j, i≠j → baseD c x y i j=s*dsq (p i).1 (p j).1 := by
  classical
  let D := (distanceSet A).erase M
  have hd : D.card=3 := by dsimp [D]; rw [Finset.card_erase_of_mem hM]; change distinctDistances A-1=3; omega
  have hBD (u : ℝ²) (hu : u∈B) (v : ℝ²) (hv : v∈B) (hne : u≠v) : dist u v∈D :=
    Finset.mem_erase.mpr ⟨(hdiam u hu v hv).ne,OMA.R_Erdos1082_erdos_1082_parts_i_R1.dist_mem (hBA hu) (hBA hv) hne⟩
  obtain ⟨c,⟨p,r,hcr⟩,hmin⟩ := minimal_realization B D hB hd hBD
  have hpos (d : ℝ) (h : d∈distanceSet A) : 0<d := by
    obtain ⟨⟨u,v⟩,hu,rfl⟩ := Finset.mem_image.mp h
    exact dist_pos.mpr (Finset.mem_offDiag.mp hu).2.2
  have rpos (i : Fin 3) := hpos (r i).1 (Finset.mem_erase.mp (r i).2).2
  let s := ((r 0).1^2)⁻¹
  let f (d : ℝ) := s*d^2
  have hs : 0<s := inv_pos.mpr (sq_pos_of_pos (rpos 0))
  have inj (a b : ℝ) (ha : 0<a) (hb : 0<b) (h : f a=f b) : a=b := by
    have hh := mul_left_cancel₀ hs.ne' h
    have hsum : 0<a+b := by positivity
    have hprod : (a-b)*(a+b)=0 := by linear_combination hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum.ne')
  let x := f (r 1).1
  let y := f (r 2).1
  let t := f M
  have one : f (r 0).1=1 := by dsimp [f,s]; field_simp [(rpos 0).ne']
  have rmap (i : Fin 3) : palette3 x y i=f (r i).1 := by fin_cases i <;> first | exact one.symm | rfl
  have hp (i j : Fin 5) (hij : i≠j) : baseD c x y i j=s*dsq (p i).1 (p j).1 := by
    change palette3 x y (c (slot i j))=_
    rw [rmap,hcr i j hij,dsq_eq]
  have valin : Function.Injective (fun i : Fin 3 => f (r i).1) := by
    intro i j he
    exact r.injective (Subtype.ext (inj _ _ (rpos i) (rpos j) he))
  have hrpos (i : Fin 3) : 0<f (r i).1 := mul_pos hs (sq_pos_of_pos (rpos i))
  have xy : x≠0 ∧ y≠0 ∧ x-1≠0 ∧ y-1≠0 ∧ x-y≠0 := by
    refine ⟨(hrpos 1).ne',(hrpos 2).ne',sub_ne_zero.mpr ?_,sub_ne_zero.mpr ?_,sub_ne_zero.mpr ?_⟩
    · intro e; exact (by decide : (1:Fin 3)≠0) (valin (e.trans one.symm))
    · intro e; exact (by decide : (2:Fin 3)≠0) (valin (e.trans one.symm))
    · intro e; exact (by decide : (1:Fin 3)≠2) (valin e)
  have mt (i : Fin 3) : t≠f (r i).1 := by
    intro e
    exact (Finset.mem_erase.mp (r i).2).1 (inj _ _ (hpos _ hM) (rpos i) e).symm
  have pInj : Function.Injective (fun i : Fin 5 => (p i).1) := fun _ _ e => p.injective (Subtype.ext e)
  have col (i j k : Fin 5) (hij : i≠j) (hjk : j≠k) (hik : i≠k) : ¬Collinear ℝ ({(p i).1,(p j).1,(p k).1}:Set ℝ²) :=
    hnc (hBA (p i).2) (hBA (p j).2) (hBA (p k).2) (fun e => hij (pInj e)) (fun e => hjk (pInj e)) (fun e => hik (pInj e))
  have had := build_admissible c x y s _ pInj hs.ne' col hp xy
  let C := A\B
  have hC : C.card=5 := by dsimp [C]; rw [Finset.card_sdiff_of_subset hBA,hA,hB]
  let q := (C.equivFinOfCardEq hC).symm
  have qInj : Function.Injective (fun i : Fin 5 => (q i).1) := fun _ _ e => q.injective (Subtype.ext e)
  have palette (u v : ℝ²) (hu : u∈A) (hv : v∈A) (hne : u≠v) : ∃ k, s*dsq u v=palette4 x y t k := by
    rw [dsq_eq]
    change ∃ k, f (dist u v)=palette4 x y t k
    by_cases hh : dist u v=M
    · exact ⟨3, by rw [hh]; rfl⟩
    have hds := Finset.mem_erase.mpr ⟨hh, OMA.R_Erdos1082_erdos_1082_parts_i_R1.dist_mem hu hv hne⟩
    obtain ⟨k,hk⟩ := r.surjective (⟨dist u v,hds⟩:D)
    have ek := congrArg Subtype.val hk
    change (r k).1=dist u v at ek
    rw [←ek]
    fin_cases k
    · exact ⟨0,one⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  refine ⟨c,p,s,x,y,t,hs.ne',hmin,had,?_,sub_ne_zero.mpr (fun h => mt 0 (h.trans one.symm)),
    sub_ne_zero.mpr (mt 1),sub_ne_zero.mpr (mt 2),(mul_pos hs (sq_pos_of_pos (hpos M hM))).ne',hp⟩
  apply build_extension c x y t s (fun i => (p i).1) (fun i => (q i).1) qInj hs.ne'
    (fun e => (by decide : (0:Fin 5)≠1) (pInj e)) (col 0 1 2 (by decide) (by decide) (by decide)) hp
  · intro i j
    obtain ⟨hA,hB⟩ := Finset.mem_sdiff.mp (q j).2
    exact palette _ _ (hBA (p i).2) hA (fun e => hB (e ▸ (p i).2))
  · intro i j hij
    exact palette _ _ (Finset.mem_sdiff.mp (q i).2).1 (Finset.mem_sdiff.mp (q j).2).1 (fun e => hij (qInj e))


private lemma orbit_0000000000 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=0 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000000001 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000000000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000000 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000001 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000002 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000000011 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=4 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000000012 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=5 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000010 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000011 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000012 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00000000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000000 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000001 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000002 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000000111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=13 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000000112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=14 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000000012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000010 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000011 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000012 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_00000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0000000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000000 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000001 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000002 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000000100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000001010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001011 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=31 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001012 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=32 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001010 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001011 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001012 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000000102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000100 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000101 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000102 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000001100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=36 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001101 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=37 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=38 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=40 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=41 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=44 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000001200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=45 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=46 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=49 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=50 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=53 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000010 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000011 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000012 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_0000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_000000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000001 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000002 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000011110 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=120 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=121 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=122 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000011110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000011120 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=123 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=124 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=125 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000001112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000011120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000001110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000011220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=132 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=133 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000001122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000011220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000001120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000001210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000001211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000012120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000012121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=151 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000012122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000001212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000012120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000012121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000012122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000001210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000001220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000012210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=156 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000012211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=157 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000012212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000001221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000012210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000012211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000012212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000001222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000001220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000010 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000011 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000012 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_00000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000 c h h0 h1 h2 h3 h4 e
  · exact orbit_000001 c h h0 h1 h2 h3 h4 e
  · exact orbit_000002 c h h0 h1 h2 h3 h4 e

private lemma orbit_000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_0000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000011110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000111110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=364 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000111112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=365 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000011111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000111110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000111120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=368 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000011112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000111120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000011110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000011120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000011121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=377 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000011122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000111220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00001112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000011120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00001110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00001111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00001112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000011210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000011211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000112120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000112121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000112122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,4,1,2,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000011212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000112120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000112121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000112122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000011210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000011220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000112210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000112211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=400 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000112212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=401 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000011221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000112210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000112211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000112212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000011222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![0,2,4,3,1]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00001122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000011220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00001120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00001121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00001122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000110 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000111 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000112 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_000012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000120 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000121 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000122 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000010 c h h0 h1 h2 h3 h4 e
  · exact orbit_000011 c h h0 h1 h2 h3 h4 e
  · exact orbit_000012 c h h0 h1 h2 h3 h4 e

private lemma orbit_00002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4] at hh ; omega

private lemma orbit_0000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) : colorCode c∈baseCodes := by
  have he : c 4=0 ∨ c 4=1 ∨ c 4=2 := by have hv := (c 4).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000 c h h0 h1 h2 h3 e
  · exact orbit_00001 c h h0 h1 h2 h3 e
  · exact orbit_00002 c h h0 h1 h2 h3 e

private lemma orbit_0001000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_000100100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001001010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001012 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=761 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001010 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001011 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001012 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001022 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=764 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100100 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100101 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100102 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001001100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=765 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001001101 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=766 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001001102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=767 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=770 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=773 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001001200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=774 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001001201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=775 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001001202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=776 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=779 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=782 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010010 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010011 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010012 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000100200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000100201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000100202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00010020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100200 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100201 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100202 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001002100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=792 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001002101 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=793 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001002102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=794 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001002100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001002110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001002111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=796 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001002112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=797 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001002110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001002120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001002121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001002122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=800 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001002120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_00010022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010020 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010021 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010022 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001000 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001001 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001002 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00010100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000101010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001010110 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=822 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=823 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=824 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001010110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001010120 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=825 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=826 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=827 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001010120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101010 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101011 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101012 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000101020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000101021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001010220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=834 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=835 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=836 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001010220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010100 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010101 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010102 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00010110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000101110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001011110 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=849 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![3,1,4,2,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001011112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=851 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001011120 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=852 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=853 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=854 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001011200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=855 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,1,3,0,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001011202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=857 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001011210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=858 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001011212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=860 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001011220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=861 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=862 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=863 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00010120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000101210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000101211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001012120 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=879 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=880 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=881 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001012120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001012200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=882 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=883 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,0,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000101220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001012200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001012210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=885 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=886 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=887 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001012210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001012220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=888 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=889 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=890 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001012220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001010 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001011 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001012 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00010200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00010201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000102020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001020210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=912 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001020211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=913 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001020212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000102021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001020210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001020211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001020212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000102022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00010202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000102020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010200 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010201 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010202 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00010210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00010211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000102120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001021210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=939 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001021211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001021212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=941 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000102121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001021210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001021211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001021212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001021220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=942 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001021221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=943 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001021222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,1,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000102122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001021220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001021221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001021222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000102120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00010220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00010221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000102220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000102221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001022220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=969 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001022221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=970 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001022222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,4,2,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000102222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001022220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001022221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001022222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000102220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001020 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001021 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001022 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100 c h h0 h1 h2 h3 h4 e
  · exact orbit_000101 c h h0 h1 h2 h3 h4 e
  · exact orbit_000102 c h h0 h1 h2 h3 h4 e

private lemma orbit_000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_00011100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001110100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1062 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001110101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,4,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1064 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000111011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,4,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001110120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1070 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111010 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111011 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111012 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001110200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1071 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001110201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1072 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001110202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1073 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001110210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1075 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001110212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1076 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001110220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1079 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011100 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011101 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011102 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00011110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00011111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,4,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001111200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,4,2,3,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001111201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![1,3,4,2,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001111202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1100 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001111200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001111201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001111202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000111121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,3,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001111222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1106 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001111220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001111221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001111222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00011120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000111210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000111211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001112120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1124 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001112120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001112200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1125 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001112201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1126 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001112202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1127 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001112200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001112210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1129 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001112212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1130 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001112210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001112220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,3,0]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000111222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001112220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001111 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001112 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00011200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00011201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001120200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1152 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1153 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,4,1,2,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001120200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001120210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1155 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,2,3,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001120212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1157 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000112021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001120210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001120220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1158 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1159 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,1,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001120220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000112020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011200 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011201 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011202 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00011210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00011211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000112120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001121210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001121211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001121212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,0,3]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001121210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001121211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001121212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001121220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1185 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001121221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,1,3,0,2]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001121222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,1,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001121220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001121221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001121222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000112120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00011220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00011221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000112220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000112221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001122220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1212 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001122221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1213 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001122222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,4,2,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001122220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001122221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001122222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000112220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001120 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001121 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001122 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000110 c h h0 h1 h2 h3 h4 e
  · exact orbit_000111 c h h0 h1 h2 h3 h4 e
  · exact orbit_000112 c h h0 h1 h2 h3 h4 e

private lemma orbit_000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_00012200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00012201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001220200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1395 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001220201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1396 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001220202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000122020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001220200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001220201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001220202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001220210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001220211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,2,3,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001220212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000122021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001220210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001220211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001220212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000122022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00012202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000122020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000122021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000122022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00012200 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00012201 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00012202 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00012210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00012211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000122120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001221210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001221211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001221212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000122121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001221210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001221211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001221212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000122122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00012212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000122120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000122121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000122122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00012210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00012211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00012212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_0001222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001220 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001221 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001222 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000120 c h h0 h1 h2 h3 h4 e
  · exact orbit_000121 c h h0 h1 h2 h3 h4 e
  · exact orbit_000122 c h h0 h1 h2 h3 h4 e

private lemma orbit_0001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) : colorCode c∈baseCodes := by
  have he : c 4=0 ∨ c 4=1 ∨ c 4=2 := by have hv := (c 4).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010 c h h0 h1 h2 h3 e
  · exact orbit_00011 c h h0 h1 h2 h3 e
  · exact orbit_00012 c h h0 h1 h2 h3 e

private lemma orbit_0002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) : colorCode c∈baseCodes := by
  have he : c 3=0 ∨ c 3=1 ∨ c 3=2 := by have hv := (c 3).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000 c h h0 h1 h2 e
  · exact orbit_0001 c h h0 h1 h2 e
  · exact orbit_0002 c h h0 h1 h2 e

private lemma orbit_0010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_001100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_0011010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00110110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00110111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001101120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001101121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011011220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3048 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011011221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011011222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3050 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001101122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011011220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011011221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011011222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00110112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001101120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001101121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001101122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00110110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00110120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00110121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001101220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011012210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3072 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011012211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011012212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3074 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001101221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011012210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011012211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011012212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0011012220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3075 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011012221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011012222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,0,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001101222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011012220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011012221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011012222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00110122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001101220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001101221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001101222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00110120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011010 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011011 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011012 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0011020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00110220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00110221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00110222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0011022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00110220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011020 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011021 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011022 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001100 c h h0 h1 h2 h3 h4 e
  · exact orbit_001101 c h h0 h1 h2 h3 h4 e
  · exact orbit_001102 c h h0 h1 h2 h3 h4 e

private lemma orbit_0011100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001110100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001110101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011101020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101022 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3194 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110100 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110101 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110102 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011101100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3195 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011101101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3197 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001110111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011101120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3203 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011101200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,4,3,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3206 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001110121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011101220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,2,3,0,1]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001110122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00111010 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111011 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111012 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001110200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001110201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011102020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,0,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,0,3]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001110202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110200 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110201 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110202 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_001110210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001110211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011102120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,2,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,0,3]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001110212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011102200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3231 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011102201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3233 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0011102210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3234 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011102211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3236 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0011102220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3237 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011102221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,0,3]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001110222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00111020 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111021 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111022 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011100 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011101 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011102 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0011110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00111120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00111121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011112210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011112211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011112212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,1,0]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011112210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011112211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011112212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0011112220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011112221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011112222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,0,1]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001111222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011112220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011112221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011112222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001111220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001111221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001111222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00111120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011110 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011111 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011112 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0011120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001112220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001112221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011122220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3399 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011122221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011122222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,0,4]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001112222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011122220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011122221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011122222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001112220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001112221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001112222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00111220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011120 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011121 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011122 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110 c h h0 h1 h2 h3 h4 e
  · exact orbit_001111 c h h0 h1 h2 h3 h4 e
  · exact orbit_001112 c h h0 h1 h2 h3 h4 e

private lemma orbit_0011200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001120100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,4,3,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011201020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201022 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3437 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001120102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011201020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00112010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120100 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120101 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120102 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011201100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3440 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001120110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011201100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001120111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,2,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011201120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,2,3,0,1]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001120112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011201120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00112011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_001120120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,4,3,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,4,3,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,0,4]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00112012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00112010 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00112011 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00112012 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001120200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00112020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120200 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120201 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120202 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_00112021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,2,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00112022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0011202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00112020 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00112021 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00112022 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011200 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011201 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011202 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_0011220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,0,4]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011220 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011221 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011222 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120 c h h0 h1 h2 h3 h4 e
  · exact orbit_001121 c h h0 h1 h2 h3 h4 e
  · exact orbit_001122 c h h0 h1 h2 h3 h4 e

private lemma orbit_0011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) : colorCode c∈baseCodes := by
  have he : c 4=0 ∨ c 4=1 ∨ c 4=2 := by have hv := (c 4).isLt; omega
  rcases he with e|e|e
  · exact orbit_00110 c h h0 h1 h2 h3 e
  · exact orbit_00111 c h h0 h1 h2 h3 e
  · exact orbit_00112 c h h0 h1 h2 h3 e

private lemma orbit_001200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_0012010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0012011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00120120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00120121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001201220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0012012210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3801 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0012012211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012012212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001201221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012012210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012012211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012012212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001201222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00120122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001201220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001201221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001201222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00120120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00120121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00120122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012010 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012011 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012012 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0012020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00120210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00120211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00120212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0012021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00120210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00120211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00120212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_0012022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012020 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012021 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012022 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001200 c h h0 h1 h2 h3 h4 e
  · exact orbit_001201 c h h0 h1 h2 h3 h4 e
  · exact orbit_001202 c h h0 h1 h2 h3 h4 e

private lemma orbit_0012100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0012101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001210200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001210201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001210202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001210200 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210201 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210202 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_001210210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![2,0,4,1,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001210211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001210212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001210210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012102200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![2,4,0,3,1]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012102201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=3961 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0012102202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,4,2,1,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001210220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012102200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012102201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012102202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0012102210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012102211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![2,4,1,3,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012102212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,4,2,0,1]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001210221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012102210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012102211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012102212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001210222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001210220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121020 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121021 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121022 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012100 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012101 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012102 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0012110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,4,2,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0012111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00121120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0012112200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![2,4,0,3,1]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012112201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![1,3,2,4,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012112202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![1,3,2,4,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001211220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012112200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012112201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012112202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001211221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,4,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001211222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,4,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001211220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001211221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001211222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012110 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012111 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012112 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00121200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0012120200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,4,3,2]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012120201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,4,1,2]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012120202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,4,3,2]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001212020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012120200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012120201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012120202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001212021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![2,1,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001212022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,4,3,2]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001212020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001212021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001212022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121200 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121201 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121202 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00121210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001212120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001212121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001212122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,3,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001212120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001212121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001212122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00121220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,0,4]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0012122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012120 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012121 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012122 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001210 c h h0 h1 h2 h3 h4 e
  · exact orbit_001211 c h h0 h1 h2 h3 h4 e
  · exact orbit_001212 c h h0 h1 h2 h3 h4 e

private lemma orbit_00122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4] at hh ; omega

private lemma orbit_0012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) : colorCode c∈baseCodes := by
  have he : c 4=0 ∨ c 4=1 ∨ c 4=2 := by have hv := (c 4).isLt; omega
  rcases he with e|e|e
  · exact orbit_00120 c h h0 h1 h2 h3 e
  · exact orbit_00121 c h h0 h1 h2 h3 e
  · exact orbit_00122 c h h0 h1 h2 h3 e

private lemma orbit_001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) : colorCode c∈baseCodes := by
  have he : c 3=0 ∨ c 3=1 ∨ c 3=2 := by have hv := (c 3).isLt; omega
  rcases he with e|e|e
  · exact orbit_0010 c h h0 h1 h2 e
  · exact orbit_0011 c h h0 h1 h2 e
  · exact orbit_0012 c h h0 h1 h2 e

private lemma orbit_002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2] at hh ; omega

private lemma orbit_00 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) : colorCode c∈baseCodes := by
  have he : c 2=0 ∨ c 2=1 ∨ c 2=2 := by have hv := (c 2).isLt; omega
  rcases he with e|e|e
  · exact orbit_000 c h h0 h1 e
  · exact orbit_001 c h h0 h1 e
  · exact orbit_002 c h h0 h1 e

private lemma orbit_010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2] at hh ; omega

private lemma orbit_011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2] at hh ; omega

private lemma orbit_0120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=2) (h3 : c 3=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_0121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=2) (h3 : c 3=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_0122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=2) (h3 : c 3=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=2) : colorCode c∈baseCodes := by
  have he : c 3=0 ∨ c 3=1 ∨ c 3=2 := by have hv := (c 3).isLt; omega
  rcases he with e|e|e
  · exact orbit_0120 c h h0 h1 h2 e
  · exact orbit_0121 c h h0 h1 h2 e
  · exact orbit_0122 c h h0 h1 h2 e

private lemma orbit_01 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) : colorCode c∈baseCodes := by
  have he : c 2=0 ∨ c 2=1 ∨ c 2=2 := by have hv := (c 2).isLt; omega
  rcases he with e|e|e
  · exact orbit_010 c h h0 h1 e
  · exact orbit_011 c h h0 h1 e
  · exact orbit_012 c h h0 h1 e

private lemma orbit_02 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1] at hh ; omega

private lemma orbit_0 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) : colorCode c∈baseCodes := by
  have he : c 1=0 ∨ c 1=1 ∨ c 1=2 := by have hv := (c 1).isLt; omega
  rcases he with e|e|e
  · exact orbit_00 c h h0 e
  · exact orbit_01 c h h0 e
  · exact orbit_02 c h h0 e

private lemma orbit_1 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0] at hh ; omega

private lemma orbit_2 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0] at hh ; omega

private lemma orbit_empty (c : Fin 10→Fin 3) (h : minimalColor c)  : colorCode c∈baseCodes := by
  have he : c 0=0 ∨ c 0=1 ∨ c 0=2 := by have hv := (c 0).isLt; omega
  rcases he with e|e|e
  · exact orbit_0 c h  e
  · exact orbit_1 c h  e
  · exact orbit_2 c h  e


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



private lemma base_0000001011 (x y : ℝ) (g0 : (-4:ℝ)=0) (_g1 : x - (2:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : (3:ℝ)≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : (3:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : (3:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h1 : (1:ℝ)=0 := by linear_combination (-1/4)*g0
  have h2 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : (1:ℝ)=0 := by linear_combination (1)*h1
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  norm_num at h3



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



private lemma base_0001011110 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : 4 - 5*x=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*x - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x - 4/(5:ℝ)=0 := by linear_combination (-1/5)*g1
  have h3 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-15/7)*h2 + (15/7)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



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


private lemma base_0001110100 (x y : ℝ) (g0 : 2*x^3 - 6*x^2=0) (g1 : -x^3=0) (g2 : 4*x^3 - 8*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 3*x^2≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 4*x≠0) (n14 : -x^2 + 4*x≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (4 - x)*he
  have h3 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((x) * (x) * (x))*(1)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left (mul_ne_zero (mul_ne_zero h2 h2) h2)
  have h7 : ((x) * (x))*(x - 2)=0 := by linear_combination (1/4)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left (mul_ne_zero h2 h2)
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma shape_0001110100 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,1,0,0] x y) : False := by
  apply base_0001110100 x y
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x x 1 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area x x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma base_0011101100 (x y : ℝ) (g0 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (g1 : 3*x^3 - 11*x^2 + 9*x - (2:ℝ)=0) (g2 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : 4*x - (1:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 4*x≠0) (_n14 : -x^2 + 4*x≠0) : (x^2 - 3*x + (1:ℝ)=0) := by
  have h1 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^3 - 11*x^2/3 + 3*x - 2/(3:ℝ)=0 := by linear_combination (1/3)*g1
  have h3 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x^2 - 3*x + (1:ℝ)=0 := by linear_combination (-3/5)*h2 + (3/5)*h3
  have h5 : x^2 - 3*x + (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : x^2 - 3*x + (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : x^2 - 3*x + (1:ℝ)=0 := by linear_combination (1)*h6
  exact h5



private lemma shape_0011101100 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,1,1,0,0] x y) : (x^2 - 3*x + 1=0) := by
  apply base_0011101100 x y
  · have hg : gram 1 1 x x 1 x x 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 x x x 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x x 1 x x 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
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


lemma pentagon_completion_0 (x a b c d : ℝ) (hx : x^2-3*x+1=0) (ha: a=1 ∨ a=x) (hb: b=1 ∨ b=x) (hc: c=1 ∨ c=x) (hd: d=1 ∨ d=x)
    (h₀ : gram x 1 x a b c a b c 0=0) (h₁ : gram x 1 x a b c x 1 1 d=0) : a=1 ∧ b=1 ∧ c=x := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;> rcases hd with rfl|rfl <;>
    simp only [gram,area] at h₀ h₁ <;> first | exact ⟨rfl,rfl,rfl⟩ | exfalso; grobner

lemma pentagon_completion_1 (x a b c d : ℝ) (hx : x^2-3*x+1=0) (ha: a=1 ∨ a=x) (hb: b=1 ∨ b=x) (hc: c=1 ∨ c=x) (hd: d=1 ∨ d=x)
    (h₀ : gram 1 x x a b c a b c 0=0) (h₁ : gram 1 x x a b c x 1 1 d=0) : a=1 ∧ b=x ∧ c=1 := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;> rcases hd with rfl|rfl <;>
    simp only [gram,area] at h₀ h₁ <;> first | exact ⟨rfl,rfl,rfl⟩ | exfalso; grobner

lemma pentagon_completion_2 (x a b c d : ℝ) (hx : x^2-3*x+1=0) (ha: a=1 ∨ a=x) (hb: b=1 ∨ b=x) (hc: c=1 ∨ c=x) (hd: d=1 ∨ d=x)
    (h₀ : gram 1 x 1 a b c a b c 0=0) (h₁ : gram 1 x 1 a b c x x 1 d=0) : a=1 ∧ b=x ∧ c=x := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;> rcases hd with rfl|rfl <;>
    simp only [gram,area] at h₀ h₁ <;> first | exact ⟨rfl,rfl,rfl⟩ | exfalso; grobner

lemma pentagon_completion_3 (x a b c d : ℝ) (hx : x^2-3*x+1=0) (ha: a=1 ∨ a=x) (hb: b=1 ∨ b=x) (hc: c=1 ∨ c=x) (hd: d=1 ∨ d=x)
    (h₀ : gram 1 1 x a b c a b c 0=0) (h₁ : gram 1 1 x a b c x x 1 d=0) : a=x ∧ b=1 ∧ c=x := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;> rcases hd with rfl|rfl <;>
    simp only [gram,area] at h₀ h₁ <;> first | exact ⟨rfl,rfl,rfl⟩ | exfalso; grobner

lemma pentagon_completion_4 (x a b c d : ℝ) (hx : x^2-3*x+1=0) (ha: a=1 ∨ a=x) (hb: b=1 ∨ b=x) (hc: c=1 ∨ c=x) (hd: d=1 ∨ d=x)
    (h₀ : gram 1 1 x a b c a b c 0=0) (h₁ : gram 1 1 x a b c x 1 x d=0) : a=x ∧ b=x ∧ c=1 := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;> rcases hd with rfl|rfl <;>
    simp only [gram,area] at h₀ h₁ <;> first | exact ⟨rfl,rfl,rfl⟩ | exfalso; grobner

def pent : Fin 10→Fin 3 := ![0,0,1,1,1,0,1,1,0,0]

lemma pent_two (x y : ℝ) (i j : Fin 5) : baseD pent x y i j=1 ∨ baseD pent x y i j=x := by
  fin_cases i <;> fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl

lemma pent_rest (k : Fin 5) : ∀ d : Fin 2, ∃ a b : Fin 5, a≠k ∧ b≠k ∧ a≠b ∧ (pent (slot a b)).val=d.val := by
  decide +revert

lemma dsq_self (x : ℝ²) : dsq x x=0 := by simp [dsq]
lemma dsq_comm (x y : ℝ²) : dsq x y=dsq y x := by rw [dsq_eq,dsq_eq,dist_comm]

lemma unique_pent_point (p : Fin 5→ℝ²) (s x y : ℝ) (hs : s≠0) (hp : Function.Injective p)
    (hn : ∀ i j k : Fin 5, i≠j → j≠k → i≠k → ¬Collinear ℝ ({p i,p j,p k}:Set ℝ²))
    (hd : ∀ i j : Fin 5, i≠j → baseD pent x y i j=s*dsq (p i) (p j))
    (hx : x^2-3*x+1=0) (k : Fin 5) (w : ℝ²)
    (hw : ∀ i : Fin 5, i≠k → s*dsq (p i) w=1 ∨ s*dsq (p i) w=x) : w=p k := by
  fin_cases k
  · change w=p 0
    have gg := gram_identity (p 1) (p 2) (p 3) w w s
    have ge := gram_identity (p 1) (p 2) (p 3) w (p 4) s
    have h01 : s*dsq (p 0) (p 1)=1 := (hd 0 1 (by decide)).symm
    have h02 : s*dsq (p 0) (p 2)=1 := (hd 0 2 (by decide)).symm
    have h03 : s*dsq (p 0) (p 3)=x := (hd 0 3 (by decide)).symm
    have h12 : s*dsq (p 1) (p 2)=x := (hd 1 2 (by decide)).symm
    have h13 : s*dsq (p 1) (p 3)=1 := (hd 1 3 (by decide)).symm
    have h14 : s*dsq (p 1) (p 4)=x := (hd 1 4 (by decide)).symm
    have h23 : s*dsq (p 2) (p 3)=x := (hd 2 3 (by decide)).symm
    have h24 : s*dsq (p 2) (p 4)=1 := (hd 2 4 (by decide)).symm
    have h34 : s*dsq (p 3) (p 4)=1 := (hd 3 4 (by decide)).symm
    rw [h12,h13,h23,dsq_self,mul_zero] at gg
    rw [h12,h13,h23,h14,h24,h34,dsq_comm w (p 4)] at ge
    obtain ⟨g0,g1,g2⟩ := pentagon_completion_0 x (s*dsq (p 1) w) (s*dsq (p 2) w) (s*dsq (p 3) w) (s*dsq (p 4) w) hx (hw 1 (by decide)) (hw 2 (by decide)) (hw 3 (by decide)) (hw 4 (by decide)) gg ge
    apply geom_injective s hs (p 1) (p 2) (p 3) (fun h => (by decide : (1:Fin 5)≠2) (hp h)) (hn 1 2 3 (by decide) (by decide) (by decide))
    unfold dataTriple
    rw [g0,g1,g2,dsq_comm (p 1) (p 0),h01,dsq_comm (p 2) (p 0),h02,dsq_comm (p 3) (p 0),h03]
  · change w=p 1
    have gg := gram_identity (p 0) (p 2) (p 3) w w s
    have ge := gram_identity (p 0) (p 2) (p 3) w (p 4) s
    have h01 : s*dsq (p 0) (p 1)=1 := (hd 0 1 (by decide)).symm
    have h02 : s*dsq (p 0) (p 2)=1 := (hd 0 2 (by decide)).symm
    have h03 : s*dsq (p 0) (p 3)=x := (hd 0 3 (by decide)).symm
    have h04 : s*dsq (p 0) (p 4)=x := (hd 0 4 (by decide)).symm
    have h12 : s*dsq (p 1) (p 2)=x := (hd 1 2 (by decide)).symm
    have h13 : s*dsq (p 1) (p 3)=1 := (hd 1 3 (by decide)).symm
    have h23 : s*dsq (p 2) (p 3)=x := (hd 2 3 (by decide)).symm
    have h24 : s*dsq (p 2) (p 4)=1 := (hd 2 4 (by decide)).symm
    have h34 : s*dsq (p 3) (p 4)=1 := (hd 3 4 (by decide)).symm
    rw [h02,h03,h23,dsq_self,mul_zero] at gg
    rw [h02,h03,h23,h04,h24,h34,dsq_comm w (p 4)] at ge
    obtain ⟨g0,g1,g2⟩ := pentagon_completion_1 x (s*dsq (p 0) w) (s*dsq (p 2) w) (s*dsq (p 3) w) (s*dsq (p 4) w) hx (hw 0 (by decide)) (hw 2 (by decide)) (hw 3 (by decide)) (hw 4 (by decide)) gg ge
    apply geom_injective s hs (p 0) (p 2) (p 3) (fun h => (by decide : (0:Fin 5)≠2) (hp h)) (hn 0 2 3 (by decide) (by decide) (by decide))
    unfold dataTriple
    rw [g0,g1,g2,h01,dsq_comm (p 2) (p 1),h12,dsq_comm (p 3) (p 1),h13]
  · change w=p 2
    have gg := gram_identity (p 0) (p 1) (p 3) w w s
    have ge := gram_identity (p 0) (p 1) (p 3) w (p 4) s
    have h01 : s*dsq (p 0) (p 1)=1 := (hd 0 1 (by decide)).symm
    have h02 : s*dsq (p 0) (p 2)=1 := (hd 0 2 (by decide)).symm
    have h03 : s*dsq (p 0) (p 3)=x := (hd 0 3 (by decide)).symm
    have h04 : s*dsq (p 0) (p 4)=x := (hd 0 4 (by decide)).symm
    have h12 : s*dsq (p 1) (p 2)=x := (hd 1 2 (by decide)).symm
    have h13 : s*dsq (p 1) (p 3)=1 := (hd 1 3 (by decide)).symm
    have h14 : s*dsq (p 1) (p 4)=x := (hd 1 4 (by decide)).symm
    have h23 : s*dsq (p 2) (p 3)=x := (hd 2 3 (by decide)).symm
    have h34 : s*dsq (p 3) (p 4)=1 := (hd 3 4 (by decide)).symm
    rw [h01,h03,h13,dsq_self,mul_zero] at gg
    rw [h01,h03,h13,h04,h14,h34,dsq_comm w (p 4)] at ge
    obtain ⟨g0,g1,g2⟩ := pentagon_completion_2 x (s*dsq (p 0) w) (s*dsq (p 1) w) (s*dsq (p 3) w) (s*dsq (p 4) w) hx (hw 0 (by decide)) (hw 1 (by decide)) (hw 3 (by decide)) (hw 4 (by decide)) gg ge
    apply geom_injective s hs (p 0) (p 1) (p 3) (fun h => (by decide : (0:Fin 5)≠1) (hp h)) (hn 0 1 3 (by decide) (by decide) (by decide))
    unfold dataTriple
    rw [g0,g1,g2,h02,h12,dsq_comm (p 3) (p 2),h23]
  · change w=p 3
    have gg := gram_identity (p 0) (p 1) (p 2) w w s
    have ge := gram_identity (p 0) (p 1) (p 2) w (p 4) s
    have h01 : s*dsq (p 0) (p 1)=1 := (hd 0 1 (by decide)).symm
    have h02 : s*dsq (p 0) (p 2)=1 := (hd 0 2 (by decide)).symm
    have h03 : s*dsq (p 0) (p 3)=x := (hd 0 3 (by decide)).symm
    have h04 : s*dsq (p 0) (p 4)=x := (hd 0 4 (by decide)).symm
    have h12 : s*dsq (p 1) (p 2)=x := (hd 1 2 (by decide)).symm
    have h13 : s*dsq (p 1) (p 3)=1 := (hd 1 3 (by decide)).symm
    have h14 : s*dsq (p 1) (p 4)=x := (hd 1 4 (by decide)).symm
    have h23 : s*dsq (p 2) (p 3)=x := (hd 2 3 (by decide)).symm
    have h24 : s*dsq (p 2) (p 4)=1 := (hd 2 4 (by decide)).symm
    rw [h01,h02,h12,dsq_self,mul_zero] at gg
    rw [h01,h02,h12,h04,h14,h24,dsq_comm w (p 4)] at ge
    obtain ⟨g0,g1,g2⟩ := pentagon_completion_3 x (s*dsq (p 0) w) (s*dsq (p 1) w) (s*dsq (p 2) w) (s*dsq (p 4) w) hx (hw 0 (by decide)) (hw 1 (by decide)) (hw 2 (by decide)) (hw 4 (by decide)) gg ge
    apply geom_injective s hs (p 0) (p 1) (p 2) (fun h => (by decide : (0:Fin 5)≠1) (hp h)) (hn 0 1 2 (by decide) (by decide) (by decide))
    unfold dataTriple
    rw [g0,g1,g2,h03,h13,h23]
  · change w=p 4
    have gg := gram_identity (p 0) (p 1) (p 2) w w s
    have ge := gram_identity (p 0) (p 1) (p 2) w (p 3) s
    have h01 : s*dsq (p 0) (p 1)=1 := (hd 0 1 (by decide)).symm
    have h02 : s*dsq (p 0) (p 2)=1 := (hd 0 2 (by decide)).symm
    have h03 : s*dsq (p 0) (p 3)=x := (hd 0 3 (by decide)).symm
    have h04 : s*dsq (p 0) (p 4)=x := (hd 0 4 (by decide)).symm
    have h12 : s*dsq (p 1) (p 2)=x := (hd 1 2 (by decide)).symm
    have h13 : s*dsq (p 1) (p 3)=1 := (hd 1 3 (by decide)).symm
    have h14 : s*dsq (p 1) (p 4)=x := (hd 1 4 (by decide)).symm
    have h23 : s*dsq (p 2) (p 3)=x := (hd 2 3 (by decide)).symm
    have h24 : s*dsq (p 2) (p 4)=1 := (hd 2 4 (by decide)).symm
    rw [h01,h02,h12,dsq_self,mul_zero] at gg
    rw [h01,h02,h12,h03,h13,h23,dsq_comm w (p 3)] at ge
    obtain ⟨g0,g1,g2⟩ := pentagon_completion_4 x (s*dsq (p 0) w) (s*dsq (p 1) w) (s*dsq (p 2) w) (s*dsq (p 3) w) hx (hw 0 (by decide)) (hw 1 (by decide)) (hw 2 (by decide)) (hw 3 (by decide)) gg ge
    apply geom_injective s hs (p 0) (p 1) (p 2) (fun h => (by decide : (0:Fin 5)≠1) (hp h)) (hn 0 1 2 (by decide) (by decide) (by decide))
    unfold dataTriple
    rw [g0,g1,g2,h04,h14,h24]


def PentReal (B : Finset ℝ²) :=
  ∃ (p : Fin 5≃B) (s x y : ℝ), s≠0 ∧ x≠1 ∧ x^2-3*x+1=0 ∧
    ∀ i j, i≠j → baseD pent x y i j=s*dsq (p i).1 (p j).1

lemma pent_image (B : Finset ℝ²) (p : Fin 5≃B) (s x y : ℝ)
    (h : ∀ i j, i≠j → baseD pent x y i j=s*dsq (p i).1 (p j).1) (d : ℝ) (hd : d∈distanceSet B) :
    s*d^2=1 ∨ s*d^2=x := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨ha,hb,hne⟩ := Finset.mem_offDiag.mp hab
  obtain ⟨i,hi⟩ := p.surjective (⟨a,ha⟩:B)
  obtain ⟨j,hj⟩ := p.surjective (⟨b,hb⟩:B)
  have hpi : (p i).1=a := congrArg Subtype.val hi
  have hpj : (p j).1=b := congrArg Subtype.val hj
  have hij : i≠j := by rintro rfl; exact hne (hpi.symm.trans hpj)
  have he := h i j hij
  rw [hpi,hpj,dsq_eq] at he
  change s*dist a b^2=1 ∨ s*dist a b^2=x
  rw [←he]
  exact pent_two x y i j

lemma pent_at_most_two (B : Finset ℝ²) (hB : PentReal B) : (distanceSet B).card≤2 := by
  classical
  obtain ⟨p,s,x,y,hs,_,_,hc⟩ := hB
  let f (d : ℝ) := s*d^2
  have hsub : (distanceSet B).image f⊆{1,x} := by
    intro v hv
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hv
    simpa only [Finset.mem_insert,Finset.mem_singleton] using pent_image B p s x y hc d hd
  have hpos (d : ℝ) (hd : d∈distanceSet B) : 0<d := by
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hd
    exact dist_pos.mpr (Finset.mem_offDiag.mp hab).2.2
  have hinj : Set.InjOn f (distanceSet B:Set ℝ) := by
    intro a ha b hb h
    have hh := mul_left_cancel₀ hs h
    have hsum : 0<a+b := add_pos (hpos _ ha) (hpos _ hb)
    have hprod : (a-b)*(a+b)=0 := by linear_combination hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum.ne')
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hh
  exact hh.trans (Finset.card_insert_le .. |>.trans (by simp))

lemma pent_rest_two (B : Finset ℝ²) (p : Fin 5≃B) (s x y : ℝ) (hx : x≠1)
    (h : ∀ i j, i≠j → baseD pent x y i j=s*dsq (p i).1 (p j).1) (v : B) :
    2≤(distanceSet (B.erase v.1)).card := by
  classical
  let k := p.symm v
  have root (j : Fin 2) :
      ∃ d∈distanceSet (B.erase v.1), s*d^2=palette3 x y ⟨j.val,by omega⟩ := by
    obtain ⟨a,b,ha,hb,hab,cl⟩ := pent_rest k j
    have hmem (i : Fin 5) (hi : i≠k) : (p i).1∈B.erase v.1 := by
      refine Finset.mem_erase.mpr ⟨?_,(p i).2⟩
      intro he
      apply hi
      apply p.injective
      simpa [k] using (Subtype.ext he : p i=v)
    have hne : (p a).1≠(p b).1 := fun he => hab (p.injective (Subtype.ext he))
    refine ⟨dist (p a).1 (p b).1,OMA.R_Erdos1082_erdos_1082_parts_i_R1.dist_mem (hmem a ha) (hmem b hb) hne,?_⟩
    rw [←dsq_eq,←h _ _ hab]
    exact congrArg (palette3 x y) (Fin.ext cl)
  obtain ⟨a,ha,h₀⟩ := root 0
  obtain ⟨b,hb,h₁⟩ := root 1
  have hne : a≠b := by rintro rfl; exact hx (h₁.symm.trans h₀)
  have hsub : ({a,b}:Finset ℝ)⊆distanceSet (B.erase v.1) := by
    intro r hr
    rcases Finset.mem_insert.mp hr with eq|eq
    · exact eq ▸ ha
    · exact (Finset.mem_singleton.mp eq) ▸ hb
  have hh := Finset.card_le_card hsub
  simpa [hne] using hh

lemma colliding_pentagons (A B : Finset ℝ²) (hBA : B⊆A) (hn : NonTrilinear (A:Set ℝ²)) (hB : PentReal B)
    (w v : ℝ²) (hw : w∉B) (hv : v∈B) (hnew : PentReal (insert w (B.erase v))) : False := by
  classical
  obtain ⟨p,s,x,y,hs,hx,he,hd⟩ := hB
  let k := p.symm ⟨v,hv⟩
  have hk : (p k).1=v := congrArg Subtype.val (p.apply_symm_apply ⟨v,hv⟩)
  have hsub : distanceSet (B.erase v)⊆distanceSet (insert w (B.erase v)) :=
    OMA.R_Erdos1082_erdos_1082_parts_i_R1.distanceSet_mono (Finset.subset_insert _ _)
  have heq := Finset.eq_of_subset_of_card_le hsub ((pent_at_most_two _ hnew).trans (pent_rest_two B p s x y hx hd ⟨v,hv⟩))
  have inj : Function.Injective (fun i : Fin 5 => (p i).1) := fun _ _ e => p.injective (Subtype.ext e)
  have col (i j k : Fin 5) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
      ¬Collinear ℝ ({(p i).1,(p j).1,(p k).1}:Set ℝ²) :=
    hn (hBA (p i).2) (hBA (p j).2) (hBA (p k).2) (fun e => hij (inj e)) (fun e => hjk (inj e)) (fun e => hik (inj e))
  have eh : w=(p k).1 := by
    apply unique_pent_point (fun i => (p i).1) s x y hs inj col hd he k w
    · intro i hi
      have hmem : (p i).1∈B.erase v := Finset.mem_erase.mpr ⟨fun ee => hi (inj (ee.trans hk.symm)),(p i).2⟩
      have hg : dist (p i).1 w∈distanceSet (insert w (B.erase v)) :=
        OMA.R_Erdos1082_erdos_1082_parts_i_R1.dist_mem (Finset.mem_insert_of_mem hmem) (Finset.mem_insert_self ..) (fun eq => hw (eq ▸ (p i).2))
      rw [←heq] at hg
      rw [dsq_eq]
      exact pent_image B p s x y hd _ (OMA.R_Erdos1082_erdos_1082_parts_i_R1.distanceSet_mono (Finset.erase_subset _ _) hg)
  exact hw (eh.symm ▸ (p k).2)


def uses_three (c : Fin 10→Fin 3) := ∀ d : Fin 3, ∃ i j : Fin 5, i≠j ∧ c (slot i j)=d

lemma misses_color (B : Finset ℝ²) (c : Fin 10→Fin 3) (s x y : ℝ) (H : admissible c x y)
    (p : Fin 5≃B) (hd : ∀ i j, i≠j → baseD c x y i j=s*dsq (p i).1 (p j).1)
    (hB : distinctDistances B≤2) : ¬uses_three c := by
  classical
  intro hh
  let V := (distanceSet B).image (fun d => s*d^2)
  have reach (d : Fin 3) : palette3 x y d∈V := by
    obtain ⟨i,j,hij,hc⟩ := hh d
    have he := hd i j hij
    change palette3 x y (c (slot i j))=_ at he
    rw [hc,dsq_eq] at he
    apply Finset.mem_image.mpr
    exact ⟨dist (p i).1 (p j).1,OMA.R_Erdos1082_erdos_1082_parts_i_R1.dist_mem (p i).2 (p j).2
      (fun e => hij (p.injective (Subtype.ext e))),he.symm⟩
  have hsub : ({1,x,y}:Finset ℝ)⊆V := by
    intro z hz
    rcases Finset.mem_insert.mp hz with he|hz
    · exact he ▸ reach 0
    rcases Finset.mem_insert.mp hz with he|hz
    · exact he ▸ reach 1
    · exact (Finset.mem_singleton.mp hz) ▸ reach 2
  have hx : x≠1 := fun he => H.1.2.2.1 (sub_eq_zero.mpr he)
  have hy : y≠1 := fun he => H.1.2.2.2.1 (sub_eq_zero.mpr he)
  have hxy : x≠y := fun he => H.1.2.2.2.2 (sub_eq_zero.mpr he)
  have size : ({1,x,y}:Finset ℝ).card=3 := by simp [Ne.symm hx,Ne.symm hy,hxy]
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [size] at hc
  exact (by omega : ¬ 3≤distinctDistances B) hc

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
lemma two_color_pent (c : Fin 10→Fin 3) (x y : ℝ) (hm : minimalColor c) (H : admissible c x y)
    (hmiss : ¬uses_three c) : c=pent := by
  have hh := orbit_empty c hm
  simp only [baseCodes,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq
  · have cc : c=![0,0,0,0,0,0,0,0,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000000000 x y H)
  · have cc : c=![0,0,0,0,0,0,0,0,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000000001 x y H)
  · have cc : c=![0,0,0,0,0,0,0,0,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000000011 x y H)
  · have cc : c=![0,0,0,0,0,0,0,0,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,0,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000000111 x y H)
  · have cc : c=![0,0,0,0,0,0,0,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,1,0,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000001011 x y H)
  · have cc : c=![0,0,0,0,0,0,1,0,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,1,1,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000001100 x y H)
  · have cc : c=![0,0,0,0,0,0,1,1,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000001101 x y H)
  · have cc : c=![0,0,0,0,0,0,1,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,1,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000001111 x y H)
  · have cc : c=![0,0,0,0,0,0,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,1,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,1,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,1,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,1,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,0,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,1,1,1,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000011110 x y H)
  · have cc : c=![0,0,0,0,0,1,1,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000011111 x y H)
  · have cc : c=![0,0,0,0,0,1,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,1,1,1,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,1,1,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,1,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,1,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,1,1,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,1,2,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,1,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,0,1,2,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,1,1,1,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0000111111 x y H)
  · have cc : c=![0,0,0,0,1,1,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,1,1,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,1,1,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,1,1,2,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,0,1,1,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,0,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,0,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,1,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0001001100 x y H)
  · have cc : c=![0,0,0,1,0,0,1,1,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0001001101 x y H)
  · have cc : c=![0,0,0,1,0,0,1,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,2,1,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,2,1,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,2,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,2,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,2,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,0,2,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,0,1,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0001010110 x y H)
  · have cc : c=![0,0,0,1,0,1,0,1,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0001010111 x y H)
  · have cc : c=![0,0,0,1,0,1,0,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,0,1,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,0,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,0,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,0,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,0,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,0,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,1,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0001011110 x y H)
  · have cc : c=![0,0,0,1,0,1,1,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,1,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,1,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,1,2,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,2,0,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,2,0,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,2,1,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,2,1,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,2,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,2,1,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,2,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,0,2,2,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,0,1,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (shape_0001110100 x y H)
  · have cc : c=![0,0,0,1,1,1,0,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,0,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,0,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,0,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,0,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,0,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,0,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,0,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,1,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,2,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,2,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,2,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,2,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,2,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,1,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,2,0,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,2,0,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,2,0,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,2,0,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,2,0,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,2,0,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,2,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,2,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,1,2,2,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,2,2,0,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,0,1,2,2,0,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,0,1,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,0,1,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,0,1,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,0,1,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,0,1,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,0,1,0,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,0,1,1,0,0] := injective_colorCode (eq.trans (by decide))
    exact cc
  · have cc : c=![0,0,1,1,1,0,1,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,0,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,0,1,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,0,2,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,0,2,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,0,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,0,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,0,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,1,2,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,2,0,1,0,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,1,2,0,1,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,2,0,1,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))
  · have cc : c=![0,0,1,2,1,0,2,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact False.elim (hmiss (by unfold uses_three; decide))

lemma two_color_realization (A B : Finset ℝ²) (M : ℝ) (hm : M∈distanceSet A) (hB : B⊆A)
    (hA : A.card=10) (hsize : B.card=5) (hd : distinctDistances A=4) (hn : NonTrilinear (A:Set ℝ²))
    (hf : ∀ a∈B, ∀ b∈B, dist a b<M) (htwo : distinctDistances B≤2) : PentReal B := by
  obtain ⟨c,p,s,x,y,_,hs,hmin,had,_,_,_,_,_,hc⟩ := normalized_five A B M hm hB hA hsize hd hn hf
  have he := two_color_pent c x y hmin had (misses_color B c s x y had p hc htwo)
  subst c
  exact ⟨p,s,x,y,hs,fun e => had.1.2.2.1 (sub_eq_zero.mpr e),shape_0011101100 x y had,hc⟩

end Erdos1082Ten

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1.H3 := by
  classical
  intro A hn hA hd M hm B hBA hB hf htwo w hw hwB v hv hf' htwo'
  let T := insert w (B.erase v)
  have hT : T.card=5 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem (fun h => hwB (Finset.mem_erase.mp h).2),Finset.card_erase_of_mem hv,hB]
  have hTA : T⊆A := by
    intro u hu
    rcases Finset.mem_insert.mp hu with he|h
    · exact he ▸ hw
    · exact hBA (Finset.mem_erase.mp h).2
  exact Erdos1082Ten.colliding_pentagons A B hBA hn
    (Erdos1082Ten.two_color_realization A B M hm hBA hA hB hd hn hf htwo) w v hwB hv
    (Erdos1082Ten.two_color_realization A T M hm hTA hA hT hd hn hf' htwo')
