import OMAStatements.S_mo_453796

namespace OMA.S_mo_453796
open Finset
private lemma ratio_limit {B T : ℝ} (hB : 0<B) (ht : 0≤T) :
    -(B+T^2)/Real.sqrt B ≤ -2*T ∧ (-(B+T^2)/Real.sqrt B = -2*T ↔ B=T^2)
    := by
  have h := Real.sq_sqrt hB.le
  have hp := Real.sqrt_pos.mpr hB
  constructor
  · rw [div_le_iff₀ hp]
    nlinarith [sq_nonneg (Real.sqrt B-T)]
  · rw [div_eq_iff hp.ne']
    constructor
    · intro he
      have hz : (Real.sqrt B-T)^2=0 := by nlinarith
      have h0 := sq_eq_zero_iff.mp hz
      nlinarith
    · intro he
      rw [he,Real.sqrt_sq ht]
      ring

private lemma reduction (n : ℕ) (u : Fin n→ℕ) (hn : 0<n) :
    (∀ i,α u i<0 ∧ 0<β u i) ∧
    (∀ S : Finset (Fin n⊕Fin n), S.card=n →
      ratio (fun i => (α u i:ℝ)) (fun i => (β u i:ℝ)) S ≤ -2*(size u:ℝ)) ∧
    ((∃ T : Finset (Fin n), 2*(∑ i∈T,u i)=∑ i,u i) ↔
      ∃ S : Finset (Fin n⊕Fin n), S.card=n ∧
        ratio (fun i => (α u i:ℝ)) (fun i => (β u i:ℝ)) S = -2*(size u:ℝ)) := by
  classical
  let H := 1+∑ i,u i
  let w : Fin n⊕Fin n→ℕ := Sum.elim u (fun _ => 0)
  let T := size u
  have ht : 0<T := by dsimp [T,size]; positivity
  have hβ (i) : 0<β u i := by unfold β;exact Nat.mul_pos ht (by omega)
  have hα (i) : α u i<0 := by
    have h : (0:ℤ)<β u i := by exact_mod_cast hβ i
    unfold α
    have : (0:ℤ)≤(n:ℤ)*(1+((∑ j,u j:ℕ):ℤ))^2 := by positivity
    linarith
  have hwt (S : Finset (Fin n⊕Fin n)) : (∑ i∈S,w i)=∑ i∈S.toLeft,u i := by
    conv_lhs => rw [← S.toLeft_disjSum_toRight]
    simp [Finset.sum_disjSum,w]
  have hsum (S : Finset (Fin n⊕Fin n)) (hs : S.card=n) :
      (∑ i∈S,β u i)=T*(n+2*n*(∑ i∈S.toLeft,u i)) := by
    simp only [β, ← Finset.mul_sum,Finset.sum_add_distrib, sum_const,nsmul_eq_mul,mul_one,hs]
    rw [← hwt]
    rfl
  have hkey (S : Finset (Fin n⊕Fin n)) (hs : S.card=n) :
      ratio (fun i => (α u i:ℝ)) (fun i => (β u i:ℝ)) S ≤ -2*(size u:ℝ) ∧
       (ratio (fun i => (α u i:ℝ)) (fun i => (β u i:ℝ)) S = -2*(size u:ℝ) ↔
          2*(∑ i∈S.toLeft,u i)=∑ i,u i) := by
    have hp : 0 < ∑ i∈S,β u i := Finset.sum_pos (fun i _ => hβ i) (card_pos.mp (hs.symm ▸ hn))
    have hnum : (∑ i∈S,(α u i:ℝ)) = -((∑ i∈S,(β u i:ℝ))+(T:ℝ)^2) := by
      simp only [α,Int.cast_sub,Int.cast_neg,Int.cast_natCast,Int.cast_mul,Int.cast_pow,Int.cast_add,
        Int.cast_one,Finset.sum_sub_distrib,Finset.sum_neg_distrib,Finset.sum_const,nsmul_eq_mul,hs,T,size]
      push_cast
      ring
    have hbr : 0<∑ i∈S,(β u i:ℝ) := by exact_mod_cast hp
    simp only [ratio,hnum]
    obtain ⟨hl,he⟩:=ratio_limit (T:=(T:ℝ)) hbr (by exact_mod_cast ht.le)
    refine ⟨hl,he.trans ?_⟩
    have hh : ((∑ i∈S,(β u i:ℝ))=(T:ℝ)^2) ↔ (∑ i∈S,β u i)=T^2 := by norm_cast
    rw [hh,hsum S hs,pow_two,mul_right_inj' ht.ne']
    change n+2*n*(∑ i∈S.toLeft,u i)=n*(1+∑ i,u i) ↔ _
    rw [Nat.mul_add,Nat.mul_one,Nat.add_left_cancel_iff,show 2*n*(∑ i∈S.toLeft,u i)=
      n*(2*(∑ i∈S.toLeft,u i)) by ring,mul_right_inj' hn.ne']
  refine ⟨fun i => ⟨hα i,hβ i⟩,fun S hS => (hkey S hS).1,?_⟩
  constructor
  · rintro ⟨s,hs⟩
    let S := s.disjSum sᶜ
    have hc : S.card=n := by
      have hc : s.card≤n := by simpa using Finset.card_le_univ s
      simp [S,Finset.card_compl]
      omega
    exact ⟨S,hc,(hkey S hc).2.mpr (by simpa [S] using hs)⟩
  · rintro ⟨S,hs,h⟩
    exact ⟨S.toLeft,(hkey S hs).2.mp h⟩


private lemma top_iff {n k} (hk : 0<k) (f : Fin n→ℝ) {S : Finset (Fin n)} (hs : S.card=k) :
    Top k f S ↔ ∀ T : Finset (Fin n), T.card=k → ∑ i∈T,f i ≤ ∑ i∈S,f i := by
  classical
  constructor
  · rintro ⟨_,h⟩ T hT
    obtain ⟨z,hz,hm⟩ := S.exists_min_image f (Finset.card_pos.mp (hs ▸ hk))
    have he (i : Fin n) : (if i∈T then f i-f z else 0) ≤ (if i∈S then f i-f z else 0) := by
      by_cases hi : i∈T <;> by_cases hj : i∈S <;> simp [hi,hj,hm i,h z hz i]
    have hj := Finset.sum_le_sum (s:=univ) fun i _ => he i
    simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_sub_distrib,Finset.sum_const,
      nsmul_eq_mul,hT,hs] at hj
    linarith
  · intro h
    refine ⟨hs,?_⟩
    intro i hi j hj
    have hij : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have he : (insert j (S.erase i)).card = k := by simp [hij,hi,hs];omega
    have hu := h (insert j (S.erase i)) he
    rw [Finset.sum_insert hij] at hu
    linarith [Finset.add_sum_erase S f hi]

private lemma tops_exist {n k} (hk : 0<k) (hn : k≤n) (f : Fin n→ℝ) :
    ∃ S, Top k f S := by
  classical
  let L := (univ : Finset (Fin n)).powersetCard k
  have hL : L.Nonempty := by
    apply card_pos.mp
    simpa [L] using Nat.choose_pos hn
  obtain ⟨S,hs,h⟩ := L.exists_max_image (fun S => ∑ i∈S,f i) hL
  have hc := (Finset.mem_powersetCard.mp hs).2
  exact ⟨S,(top_iff hk f hc).mpr fun T hT => h T (Finset.mem_powersetCard.mpr ⟨subset_univ _,hT⟩)⟩

private lemma tangent {n k} {a b : Fin n→ℝ} (hb : ∀ i,0<b i) (hk : 0<k)
    {S : Finset (Fin n)} (hS : S.card=k) (h0 : 0≤ratio a b S)
    (hopt : ∀ T : Finset (Fin n), T.card=k → ratio a b T≤ratio a b S) :
    ∃ t : ℝ, 0≤t ∧ ∀ T : Finset (Fin n), Top k (score a b t) T → ratio a b T=ratio a b S := by
  classical
  let A (T : Finset (Fin n)) := ∑ i∈T,a i
  let B (T : Finset (Fin n)) := ∑ i∈T,b i
  let q := ratio a b S
  let u := Real.sqrt (B S)
  have hp {T : Finset (Fin n)} (hT : T.card=k) : 0 < B T :=
    Finset.sum_pos (fun i _ => hb i) (card_pos.mp (hT ▸ hk))
  have hu : 0<u := Real.sqrt_pos.mpr (hp hS)
  have hsq : u^2=B S := Real.sq_sqrt (hp hS).le
  have hA : A S=q*u := (div_mul_cancel₀ (A S) hu.ne').symm
  let t:=q/(2*u)
  have ht : 0≤t := div_nonneg h0 (by positivity)
  have htu : t*(2*u)=q := div_mul_cancel₀ _ (by positivity)
  have raw (T : Finset (Fin n)) (hT : T.card=k) :
      A T ≤ q*Real.sqrt (B T) := (div_le_iff₀ (Real.sqrt_pos.mpr (hp hT))).mp (hopt T hT)
  have bound (T : Finset (Fin n)) (hT : T.card=k) :
      q*Real.sqrt (B T) ≤ A S+t*(B T-B S) := by
    let y:=Real.sqrt (B T)
    have hyy : y^2=B T := Real.sq_sqrt (hp hT).le
    change q*y ≤ _
    rw [hA,← hsq,← hyy,← htu]
    nlinarith only [mul_nonneg ht (sq_nonneg (y-u))]
  refine ⟨t,ht,?_⟩
  intro T htop
  have hlin := (top_iff hk (score a b t) htop.1).mp htop S hS
  simp only [score,Finset.sum_sub_distrib, ← Finset.mul_sum] at hlin
  change A S-t*B S≤A T-t*B T at hlin
  apply le_antisymm (hopt T htop.1)
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (hp htop.1))).mpr
  change q*Real.sqrt (B T)≤A T
  linarith [bound T htop.1]


private lemma representative {n} (a b : Fin n→ℝ) (t : ℝ) (ht : 0≤t) :
    ∃ s∈samples a b, ∀ x∈breaks a b, (x<t ↔ x<s) ∧ (t<x ↔ s<x) := by
  classical
  let E := breaks a b
  have hz : 0∈E := Finset.mem_insert_self _ _
  by_cases h : t∈E
  · refine ⟨t,?_,fun _ _ => ⟨Iff.rfl,Iff.rfl⟩⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
  let below := E.filter (· ≤ t)
  have hne : below.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨hz,ht⟩⟩
  let p := below.max' hne
  obtain ⟨hpE,hpt⟩ := Finset.mem_filter.mp (Finset.max'_mem below hne)
  have hp : p<t := lt_of_le_of_ne hpt (fun hh => h (hh ▸ hpE))
  have hleft (x : ℝ) (he : x∈E) (hx : x≤t) : x≤p :=
    Finset.le_max' below _ (Finset.mem_filter.mpr ⟨he,hx⟩)
  let above := E.filter (t<·)
  by_cases hn : above.Nonempty
  · let q:=above.min' hn
    obtain ⟨hqE,htq⟩ := Finset.mem_filter.mp (Finset.min'_mem above hn)
    have hq : t<q := htq
    have hright (x : ℝ) (he : x∈E) (hx : t<x) : q≤x :=
      Finset.min'_le above _ (Finset.mem_filter.mpr ⟨he,hx⟩)
    refine ⟨(p+q)/2,Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(p,q),Finset.mem_product.mpr ⟨hpE,hqE⟩,rfl⟩),?_⟩
    intro x he
    have hx : x≠t := fun hxt => h (hxt ▸ he)
    rcases lt_or_gt_of_ne hx with hlo|hhi
    · have hx' := hleft x he hlo.le
      constructor <;> constructor <;> intro _ <;> linarith
    · have hx' := hright x he hhi
      constructor <;> constructor <;> intro _ <;> linarith
  · refine ⟨p+1,Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hpE,rfl⟩)),?_⟩
    intro x he
    have hx : x≤t := le_of_not_gt fun hh => hn ⟨x,Finset.mem_filter.mpr ⟨he,hh⟩⟩
    have hx' := hleft x he hx
    constructor <;> constructor <;> intro _ <;> linarith

private lemma same_scores {n} (a b : Fin n→ℝ) {t s : ℝ}
    (h : ∀ x∈breaks a b, (x<t ↔ x<s) ∧ (t<x ↔ s<x)) (i j : Fin n) :
    score a b t i ≤ score a b t j ↔ score a b s i ≤ score a b s j := by
  let u:=a i-a j
  let v:=b i-b j
  have he : u/v∈breaks a b := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(i,j),mem_univ _,rfl⟩)
  obtain ⟨hlo,hhi⟩:=h _ he
  have eq (r : ℝ) : score a b r i ≤ score a b r j ↔ u ≤ r*v := by
    dsimp [score,u,v]
    constructor <;> intro h <;> linarith
  rw [eq,eq]
  rcases lt_trichotomy v 0 with hv|hv|hv
  · have heq (r : ℝ) : u≤r*v ↔ r≤u/v := (le_div_iff_of_neg hv).symm
    rw [heq,heq,← not_lt,← not_lt]
    exact not_congr hlo
  · simp [hv]
  · rw [← div_le_iff₀ hv,← div_le_iff₀ hv,← not_lt,← not_lt]
    exact not_congr hhi

private lemma sample_bound {n} (a b : Fin n→ℝ) :
    (samples a b).card≤2*(n^2+1)+(n^2+1)^2 := by
  classical
  let E:=breaks a b
  have he : E.card≤n^2+1 := by
    apply (Finset.card_insert_le ..).trans
    gcongr
    simpa [sq] using (Finset.card_image_le (f:=fun p : Fin n×Fin n => (a p.1-a p.2)/(b p.1-b p.2))
      (s:=univ))
  have h1 := Finset.card_union_le (E ∪ E.image (fun x => x+1)) ((E ×ˢ E).image (fun p => (p.1+p.2)/2))
  have h2 := Finset.card_union_le E (E.image (fun x => x+1))
  have h3 := Finset.card_image_le (s:=E) (f:=fun x => x+1)
  have h4 := Finset.card_image_le (s:=E ×ˢ E) (f:=fun p => (p.1+p.2)/2)
  simp only [Finset.card_product] at h4
  change (E ∪ E.image _ ∪ (E ×ˢ E).image _).card≤_
  have hsq := Nat.mul_le_mul he he
  nlinarith

end OMA.S_mo_453796
open Finset OMA.S_mo_453796
theorem OMA.solution : type_of% @OMA.S_mo_453796.main := by
  refine ⟨reduction,fun n k => ⟨by simp,Nat.choose_le_pow n k⟩,?_⟩
  intro n k a b hk hn hb hpos
  refine ⟨sample_bound a b,⟨fun t => (tops_exist hk hn (score a b t)).choose,fun t => (tops_exist hk hn (score a b t)).choose_spec⟩,?_⟩
  intro pick htop
  classical
  let L := (univ : Finset (Fin n)).powersetCard k
  have hL : L.Nonempty := by apply card_pos.mp;simpa [L] using Nat.choose_pos hn
  obtain ⟨S,hS,hmax⟩:=L.exists_max_image (ratio a b) hL
  have hopt (T : Finset (Fin n)) (ht : T.card=k) : ratio a b T≤ratio a b S :=
    hmax T (mem_powersetCard.mpr ⟨subset_univ _,ht⟩)
  obtain ⟨T,hT,hnn⟩:=hpos
  have hnon : 0≤ratio a b S := (div_nonneg hnn (Real.sqrt_nonneg _)).trans (hopt T hT)
  obtain ⟨t,ht,h⟩:=tangent hb hk (mem_powersetCard.mp hS).2 hnon hopt
  obtain ⟨s,hs,hr⟩:=representative a b t ht
  have he : Top k (score a b t) (pick s) :=
    ⟨(htop s).1, fun i hi j hj => (same_scores a b hr j i).mpr ((htop s).2 i hi j hj)⟩
  exact ⟨s,hs,fun T hT => (hopt T hT).trans_eq (h _ he).symm⟩
