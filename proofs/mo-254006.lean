import OMAStatements.S_mo_254006
namespace OMA.S_mo_254006
open Finset
private lemma sq_balance {d : ℕ} (u v : V d) (h : perp u v) :
    ∑ i, (u i+v i)^2 = ∑ i, (u i-v i)^2 := by
  calc
    _ = ∑ i, ((u i-v i)^2 + 4*(u i*v i)) := by apply sum_congr rfl; intro i _; ring
    _ = _ := by rw [sum_add_distrib,← mul_sum,show ∑ i, u i*v i=0 from h];ring

private lemma taxicab_lb {m : ℕ} (u v : V (m+1)) (hu : lp 1 u=1) (hv : lp 1 v=1)
    (h : perp u v) : 2/(1+Real.sqrt m) ≤ lp 1 (u-v) := by
  classical
  simp only [lp,one_div_one,Real.rpow_one,Pi.sub_apply] at hu hv ⊢
  let x := fun i => |u i+v i|
  let y := fun i => |u i-v i|
  have heq : ∑ i, x i^2 = ∑ i, y i^2 := by simpa [x,y,sq_abs] using sq_balance u v h
  have hex : ∃ j, x j ≤ y j := by
    by_contra! hf
    have hlt : ∑ i, y i^2 < ∑ i, x i^2 := by
      apply sum_lt_sum_of_nonempty
      · simp
      · intro i _; exact sq_lt_sq' (by dsimp [x,y]; linarith [abs_nonneg (u i-v i),hf i]) (hf i)
    linarith
  obtain ⟨j,hj⟩ := hex
  let s := (univ : Finset (Fin (m+1))).erase j
  have hc : s.card=m := by simp [s]
  have h2 : ∑ i ∈ s,x i^2 ≤ (∑ i,y i)^2 := calc
    _ ≤ ∑ i, x i^2 := sum_le_univ_sum_of_nonneg (fun i => sq_nonneg (x i))
    _ = _ := heq
    _ ≤ _ := sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
  have cs : (∑ i ∈ s, x i)^2 ≤ m * (∑ i,y i)^2 := by
    simpa [hc] using (sq_sum_le_card_mul_sum_sq (s:=s) (f:=x)).trans
      (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  have hys : 0 ≤ ∑ i,y i := sum_nonneg fun _ _ => abs_nonneg _
  have hs : ∑ i ∈ s,x i ≤ Real.sqrt m * ∑ i,y i := by
    have hpos := mul_nonneg (Real.sqrt_nonneg (m:ℝ)) hys
    have hsq := Real.sq_sqrt (Nat.cast_nonneg m)
    have eq : (Real.sqrt m * ∑ i,y i)^2 = m*(∑ i,y i)^2 := by rw [mul_pow,hsq]
    nlinarith
  have per (i : Fin (m+1)) : |u i|+|v i| = max (x i) (y i) := by
    dsimp [x,y]
    rw [abs_eq_max_neg, abs_eq_max_neg, abs_eq_max_neg, abs_eq_max_neg]
    grind
  have hmax : (∑ i, max (x i) (y i)) ≤ (∑ i ∈ s, x i) + ∑ i,y i := by
    rw [← sum_erase_add _ _ (mem_univ j),max_eq_right hj,← sum_erase_add _ y (mem_univ j)]
    change (∑ i ∈ s, max (x i) (y i)) + y j ≤ _
    have hle : (∑ i ∈ s, max (x i) (y i)) ≤ (∑ i ∈ s,x i)+(∑ i ∈ s,y i) := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun i _ => max_le (by linarith [show 0≤y i from abs_nonneg _]) (by linarith [show 0≤x i from abs_nonneg _])
    change _ ≤ (∑ i ∈ s,x i)+((∑ i ∈ s,y i)+y j)
    linarith
  have hxys : ∑ i,max (x i) (y i) = 2 := by simp_rw [← per];rw [sum_add_distrib,hu,hv];norm_num
  apply (div_le_iff₀ (by positivity : 0<1+Real.sqrt (m:ℝ))).mpr
  change 2 ≤ (∑ i, y i)*(1+Real.sqrt m)
  linarith
private lemma lp_scale {d} {p : ℝ} (hp : 0<p) (c : ℝ) (u : V d) :
    lp p (fun i => c*u i) = |c| * lp p u := by
  unfold lp
  simp_rw [abs_mul,Real.mul_rpow (abs_nonneg c) (abs_nonneg _),← mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _)
    (sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg (u i)) _)),← Real.rpow_mul (abs_nonneg c)]
  simp [hp.ne']

private lemma pow_sum_bound {d} (s : Finset (Fin d)) (a : V d) (ha : ∀ i, 0≤a i)
    {t : ℝ} (ht : 1≤t) : ∑ i ∈ s,(a i)^t ≤ (∑ i ∈ s, a i)^t := by
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow (by linarith : t≠0)]
  | insert i s hi ih =>
    rw [sum_insert hi,sum_insert hi]
    exact (show (a i)^t+∑ j ∈ s,(a j)^t ≤ (a i)^t+(∑ j ∈ s,a j)^t by linarith).trans
      (Real.add_rpow_le_rpow_add (ha i) (sum_nonneg fun j _ => ha j) ht)

private lemma lp_compare {d} {p q : ℝ} (hp : 0<p) (hpq : p≤q) (u : V d) :
    lp q u ≤ lp p u ∧ lp p u ≤ (d:ℝ)^(1/p-1/q)*lp q u := by
  let a : V d := fun i => |u i|^p
  have ha (i) : 0≤a i := Real.rpow_nonneg (abs_nonneg _) _
  have hsum : 0≤∑ i, a i := sum_nonneg fun i _ => ha i
  have hq : 0<q := hp.trans_le hpq
  have ht : 1≤q/p := (le_div_iff₀ hp).2 (by simpa using hpq)
  have ind (i) : (a i)^(q/p) = |u i|^q := by
    rw [show a i= |u i|^p from rfl,← Real.rpow_mul (abs_nonneg _),show p*(q/p)=q by field_simp]
  have e : (∑ i,(a i)^(q/p))^(1/q) = lp q u := by simp_rw [ind];rfl
  have hlow := Real.rpow_le_rpow (sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _)
    (pow_sum_bound univ a ha ht) (by positivity : 0≤1/q)
  have hhi0 := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg univ (f:=a) ht (fun i _ => ha i)
  have hhi := Real.rpow_le_rpow (Real.rpow_nonneg hsum _) hhi0 (by positivity : 0≤1/q)
  rw [← Real.rpow_mul hsum,show q/p*(1/q)=1/p by field_simp] at hlow hhi
  rw [e] at hlow
  rw [Real.mul_rpow (by positivity) (sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _),
    ← Real.rpow_mul (by positivity),e,show (q/p-1)*(1/q) = 1/p-1/q by field_simp] at hhi
  exact ⟨hlow,by simpa only [lp,a,card_univ,Fintype.card_fin] using hhi⟩

private lemma general_lower {m} {p : ℝ} (hp : 1≤p) (u v : V (m+1))
    (hu : lp p u=1) (h : perp u v) :
    2/(1+((m+1:ℕ):ℝ)^|1/p-1/2|) ≤ lp p (u-v) := by
  let x : V (m+1) := fun i => u i+v i
  let y : V (m+1) := fun i => u i-v i
  have hp' : 0<p := by linarith
  have heq : lp 2 x = lp 2 y := by
    simp only [lp,Real.rpow_two,sq_abs,x,y,sq_balance u v h]
  have hx : lp p x ≤ ((m+1:ℕ):ℝ)^|1/p-1/2| *lp p y := by
    rcases le_total p 2 with hl|hl
    · rw [abs_of_nonneg (by have := one_div_le_one_div_of_le hp' hl;linarith)]
      exact (lp_compare hp' hl x).2.trans (by rw [heq];gcongr;exact (lp_compare hp' hl y).1)
    · rw [abs_of_nonpos (by have := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hl;linarith),neg_sub]
      exact (lp_compare (by norm_num : (0:ℝ)<2) hl x).1.trans (by rw [heq];exact (lp_compare (by norm_num : (0:ℝ)<2) hl y).2)
  have ht := Real.Lp_add_le univ x y hp
  change lp p (fun i => x i + y i) ≤ lp p x+lp p y at ht
  rw [show (fun i => x i+y i)=(fun i => 2*u i) by funext i;dsimp [x,y];ring,
    lp_scale hp',hu] at ht
  norm_num at ht
  apply (div_le_iff₀ (by positivity)).2
  change 2 ≤ lp p y*(1+_)
  linarith
private def spike (m : ℕ) (a b : ℝ) : V (m+1) := Fin.cases a (fun _ => b)

private lemma spike_lp (m : ℕ) (a b p : ℝ) :
    lp p (spike m a b) = (|a|^p + (m:ℝ)*|b|^p)^(1/p) := by
  simp [lp,spike,Fin.sum_univ_succ]

private lemma spike_perp (m : ℕ) (a b c e : ℝ) (h : a*c+(m:ℝ)*(b*e)=0) :
    perp (spike m a b) (spike m c e) := by simpa [perp,spike,Fin.sum_univ_succ] using h

private lemma spike_sub (m : ℕ) (a b c e : ℝ) :
    spike m a b - spike m c e = spike m (a-c) (b-e) := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private lemma normalized {d : ℕ} {p D : ℝ} (hp : 0<p) (hD : 0<D) (u v : V d)
    (hu : lp p u=D) (hv : lp p v=D) (h : perp u v) (hs : lp p (u-v)=2) :
    2/D ∈ distances d p := by
  refine ⟨fun i => D⁻¹*u i, fun i => D⁻¹*v i, ?_, ?_, ?_, ?_⟩
  · rw [lp_scale hp,abs_of_pos (inv_pos.mpr hD),hu,inv_mul_cancel₀ hD.ne']
  · rw [lp_scale hp,abs_of_pos (inv_pos.mpr hD),hv,inv_mul_cancel₀ hD.ne']
  · change ∑ i, D⁻¹*u i*(D⁻¹*v i)=0
    simpa only [← mul_sum,show ∑ i, u i*v i=0 from h,mul_zero] using
      (sum_congr (s₁:=univ) rfl (fun (i : Fin d) _ =>
        show D⁻¹*u i*(D⁻¹*v i)=(D⁻¹*D⁻¹)*(u i*v i) by ring))
  · rw [show (fun i => D⁻¹*u i)-(fun i => D⁻¹*v i)=(fun i => D⁻¹*((u-v) i)) by funext i;simp [mul_sub],
      lp_scale hp,hs,abs_of_pos (inv_pos.mpr hD),div_eq_mul_inv,mul_comm]

private lemma head_witness (m : ℕ) (hm : 0 < m) {p : ℝ} (hp : 0<p) :
    2/(1+(m:ℝ)^(1-p/2))^(1/p) ∈ distances (m+1) p := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  let b : ℝ := (m:ℝ)^(-(1/2:ℝ))
  have hb : 0<b := Real.rpow_pos_of_pos hm' _
  have bpow (t : ℝ) : b^t = (m:ℝ)^(-t/2) := by
    rw [show b=(m:ℝ)^(-(1/2:ℝ)) from rfl,← Real.rpow_mul hm'.le];congr 1;ring
  have bcoef (t : ℝ) : (m:ℝ)*b^t = (m:ℝ)^(1-t/2) := by
    rw [bpow,sub_eq_add_neg,← neg_div,Real.rpow_add hm',Real.rpow_one]
  apply normalized hp (by positivity) (spike m 1 b) (spike m (-1) b)
  · rw [spike_lp,abs_of_pos hb,bcoef];norm_num
  · rw [spike_lp,abs_of_pos hb,bcoef];norm_num
  · apply spike_perp
    have h2 := bcoef 2
    norm_num [Real.rpow_two] at h2
    nlinarith
  · rw [spike_sub,spike_lp];norm_num [Real.zero_rpow hp.ne',← Real.rpow_mul (by norm_num : (0:ℝ)≤2),hp.ne']

private lemma tail_witness (m : ℕ) (hm : 0 < m) {p : ℝ} (hp : 0<p) :
    2/(1+(m:ℝ)^(p/2-1))^(1/p) ∈ distances (m+1) p := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  let a : ℝ := (m:ℝ)^(1/2-1/p)
  let b : ℝ := (m:ℝ)^(-1/p)
  have ha : 0<a := Real.rpow_pos_of_pos hm' _
  have hb : 0<b := Real.rpow_pos_of_pos hm' _
  have apow (t : ℝ) : a^t = (m:ℝ)^(t/2-t/p) := by
    rw [show a=(m:ℝ)^(1/2-1/p) from rfl,← Real.rpow_mul hm'.le];congr 1;ring
  have bcoef (t : ℝ) : (m:ℝ)*b^t = (m:ℝ)^(1-t/p) := by
    rw [show b=(m:ℝ)^(-1/p) from rfl,← Real.rpow_mul hm'.le,show 1-t/p=1+(-1/p*t) by ring,Real.rpow_add hm',Real.rpow_one]
  have bp : (m:ℝ)*b^p = 1 := by rw [bcoef,div_self hp.ne',sub_self,Real.rpow_zero]
  have ap : a^p = (m:ℝ)^(p/2-1) := by rw [apow,div_self hp.ne']
  apply normalized hp (by positivity) (spike m a b) (spike m a (-b))
  · rw [spike_lp,abs_of_pos ha,abs_of_pos hb,bp,ap,add_comm]
  · rw [spike_lp,abs_of_pos ha,abs_neg,abs_of_pos hb,bp,ap,add_comm]
  · apply spike_perp
    have h2 : a^2 = (m:ℝ)*b^2 := by
      rw [← Real.rpow_two a,← Real.rpow_two b,apow,bcoef];norm_num
    nlinarith
  · rw [spike_sub,spike_lp,sub_self,abs_zero,Real.zero_rpow hp.ne',zero_add,sub_neg_eq_add,
      ← two_mul,abs_mul,abs_of_pos hb,abs_of_pos (by norm_num : (0:ℝ)<2),Real.mul_rpow (by norm_num) hb.le,
      mul_left_comm,bp,mul_one,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    simp [hp.ne']

private lemma upper {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0<p) :
    2/(1+(m:ℝ)^|1-p/2|)^(1/p) ∈ distances (m+1) p := by
  rcases le_total p 2 with hl|hl
  · rw [abs_of_nonneg (by linarith)];exact head_witness m hm hp
  · rw [abs_of_nonpos (by linarith),neg_sub];exact tail_witness m hm hp
open Filter Topology
private lemma finite_bounds {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 1≤p) :
    2/(1+((m+1:ℕ):ℝ)^|1/p-1/2|) ≤ sInf (distances (m+1) p) ∧
    sInf (distances (m+1) p) ≤ 2/(1+(m:ℝ)^|1-p/2|)^(1/p) := by
  have hu := upper hm (show 0<p by linarith)
  have lb {r} (hr : r∈distances (m+1) p) : 2/(1+((m+1:ℕ):ℝ)^|1/p-1/2|) ≤ r := by
    obtain ⟨u,v,hp₁,_,horth,rfl⟩ := hr
    exact general_lower hp u v hp₁ horth
  exact ⟨le_csInf ⟨_,hu⟩ (fun _ h => lb h),csInf_le ⟨_,fun _ h => lb h⟩ hu⟩

private lemma asymptotic {p : ℝ} (hp : 1≤p) (hne : p≠2) :
    Tendsto (fun m : ℕ => ((m+1:ℕ):ℝ)^|1/p-1/2| * sInf (distances (m+1) p)) atTop (𝓝 2) := by
  let β := |1/p-1/2|
  have hp0 : 0<p := by linarith
  have hβ : 0<β := abs_pos.mpr (fun h => hne (by field_simp at h;linarith))
  have hprod : |1-p/2|=β*p := by
    rw [show 1-p/2=(1/p-1/2)*p by field_simp,abs_mul,abs_of_pos hp0]
  have ht : Tendsto (fun m : ℕ => ((m+1:ℕ):ℝ)^β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hl : Tendsto (fun m : ℕ => 2/(1+(((m+1:ℕ):ℝ)^β)⁻¹)) atTop (𝓝 2) := by
    have hi := ht.inv_tendsto_atTop
    have h₁ : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h₂ : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have H := h₂.div (h₁.add hi) (by norm_num : (1:ℝ)+0≠0)
    rw [add_zero,div_one] at H
    exact H
  have hratio : Tendsto (fun m : ℕ => ((m:ℝ)+1)/(m:ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (1:ℝ)).inv₀ one_ne_zero
  have hh : Tendsto (fun m : ℕ => 2*(((m:ℝ)+1)/m)^β) atTop (𝓝 2) := by
    simpa using (hratio.rpow_const (p:=β) (.inl one_ne_zero)).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hpos : 0<((m+1:ℕ):ℝ)^β := by positivity
    have lo := mul_le_mul_of_nonneg_left (finite_bounds hm hp).1 hpos.le
    change ((m+1:ℕ):ℝ)^β * (2/(1+((m+1:ℕ):ℝ)^β)) ≤ _ at lo
    refine le_trans (le_of_eq ?_) lo
    field_simp
    ring
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hm0 : 0<(m:ℝ) := by exact_mod_cast hm
    have hi := mul_le_mul_of_nonneg_left (finite_bounds hm hp).2
      (show 0≤((m+1:ℕ):ℝ)^β by positivity)
    apply hi.trans
    have hden : (m:ℝ)^β ≤ (1+(m:ℝ)^|1-p/2|)^(1/p) := calc
      _ = ((m:ℝ)^|1-p/2|)^(1/p) := by rw [hprod,← Real.rpow_mul hm0.le,show β*p*(1/p)=β by field_simp]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    rw [Real.div_rpow (by positivity) hm0.le,Nat.cast_add_one]
    calc
      _ ≤ ((m:ℝ)+1)^β*(2/(m:ℝ)^β) := by gcongr
      _ = _ := by ring
private lemma one_exact {m : ℕ} (hm : 0 < m) :
    IsLeast (distances (m+1) 1) (2/(1+Real.sqrt m)) := by
  constructor
  · have e := head_witness m hm (p:=1) (by norm_num)
    norm_num [show (1:ℝ)-1/2=1/2 by norm_num,← Real.sqrt_eq_rpow] at e
    exact e
  · rintro s ⟨u,v,hu,hv,h,rfl⟩
    exact taxicab_lb u v hu hv h

private lemma lp_two_sq {d} (u : V d) : (lp 2 u)^2 = ∑ i, (u i)^2 := by
  simp only [lp,Real.rpow_two,sq_abs,←Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (sum_nonneg (fun i _ => sq_nonneg (u i)))
private lemma two_exact {m : ℕ} (hm : 0 < m) : distances (m+1) 2 = {Real.sqrt 2} := by
  ext s
  constructor
  · rintro ⟨u,v,hu,hv,h,rfl⟩
    have he : ∑ i, ((u-v) i)^2 = ∑ i,(u i)^2 + ∑ i,(v i)^2 := by
      calc
        _ = ∑ i, ((u i)^2+(v i)^2-2*(u i*v i)) := by apply sum_congr rfl; intro i _; simp only [Pi.sub_apply];ring
        _ = _ := by rw [sum_sub_distrib,sum_add_distrib,← mul_sum,show ∑ i, u i*v i=0 from h];ring
    rw [←lp_two_sq,←lp_two_sq,←lp_two_sq,hu,hv] at he
    change lp 2 (u-v) = Real.sqrt 2
    have hn : 0≤lp 2 (u-v) := Real.rpow_nonneg (sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) _
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  · rintro rfl
    have e := head_witness m hm (p:=2) (by norm_num)
    norm_num [←Real.sqrt_eq_rpow] at e
    convert e using 1

private lemma zero_limit {p : ℝ} (hp : 1≤p) (hne : p≠2) :
    Tendsto (fun m : ℕ => sInf (distances (m+1) p)) atTop (𝓝 0) := by
  have hβ : 0 < |1/p-1/2| := abs_pos.mpr (fun h => hne (by field_simp at h;linarith))
  have ht := (tendsto_rpow_atTop hβ).comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hlim := (asymptotic hp hne).mul ht.inv_tendsto_atTop
  rw [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards with m
  change ((m+1:ℕ):ℝ)^|1/p-1/2| * _ * (((m+1:ℕ):ℝ)^|1/p-1/2|)⁻¹ = _
  field_simp
/-- In the plane the comparison argument in Porto's question is sharp. -/
private lemma plane_exact {p : ℝ} (hp : 1≤p) :
    IsLeast (distances 2 p) (min ((2:ℝ)^(1/p)) ((2:ℝ)^(1-1/p))) := by
  have hp0 : 0<p := by linarith
  have hpos (u : V 2) (q : ℝ) : 0≤lp q u := Real.rpow_nonneg (sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) _
  have h₁ : 2^(1/p:ℝ) ∈ distances 2 p := by
    refine ⟨spike 1 1 0,spike 1 0 1,?_,?_,spike_perp _ _ _ _ _ (by norm_num),?_⟩ <;>
      (simp [spike_sub,spike_lp,Real.zero_rpow hp0.ne'] <;> norm_num)
  have h₂ : 2^(1-1/p:ℝ) ∈ distances 2 p := by
    have h := head_witness 1 (by decide) hp0
    convert h using 1
    norm_num [Real.rpow_sub (by norm_num : (0:ℝ)<2)]
  refine ⟨by rcases le_total ((2:ℝ)^(1/p)) ((2:ℝ)^(1-1/p)) with h|h
             · rwa [min_eq_left h]
             · rwa [min_eq_right h], ?_⟩
  rintro s ⟨u,v,hu,hv,h,rfl⟩
  have he : (lp 2 (u-v))^2 = (lp 2 u)^2+(lp 2 v)^2 := by
    rw [lp_two_sq,lp_two_sq,lp_two_sq,←sum_add_distrib]
    simp only [Pi.sub_apply]
    calc
      _ = ∑ i, ((u i)^2+(v i)^2 - 2*(u i*v i)) := by apply sum_congr rfl;intro i _;ring
      _ = _ := by rw [sum_sub_distrib,←mul_sum,show ∑ i, u i*v i=0 from h];ring
  rcases le_total p 2 with hl|hl
  · let c := (2:ℝ)^(1/p-1/2)
    have hc : 0<c := Real.rpow_pos_of_pos (by norm_num) _
    have lo (w : V 2) (hw : lp p w=1) : 1 ≤ c*lp 2 w := by
      have := (lp_compare hp0 hl w).2
      simpa only [hw,Nat.cast_ofNat] using this
    have u₀ := lo u hu
    have v₀ := lo v hv
    have du := (lp_compare hp0 hl (u-v)).1
    have le : Real.sqrt 2 ≤ c*lp 2 (u-v) := by
      have e : (c*lp 2 (u-v))^2=(c*lp 2 u)^2+(c*lp 2 v)^2 := by simp only [mul_pow,←mul_add,he]
      have zn := mul_nonneg hc.le (hpos (u-v) 2)
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),sq_nonneg (c*lp 2 u-1),sq_nonneg (c*lp 2 v-1),Real.sqrt_nonneg 2]
    have hc2 : 2^(1-1/p:ℝ)*c = Real.sqrt 2 := by
      dsimp [c];rw [←Real.rpow_add (by norm_num : (0:ℝ)<2),Real.sqrt_eq_rpow];congr 1;ring
    exact min_le_right _ _ |>.trans ((le_of_mul_le_mul_right (by rw [hc2];simpa [mul_comm] using le) hc).trans du)
  · let c := (2:ℝ)^(1/2-1/p)
    have hc : 0<c := Real.rpow_pos_of_pos (by norm_num) _
    have lo (w : V 2) (hw : lp p w=1) : 1≤lp 2 w := by simpa only [←hw] using (lp_compare (by norm_num : (0:ℝ)<2) hl w).1
    have u₀ := lo u hu
    have v₀ := lo v hv
    have le : Real.sqrt 2 ≤ lp 2 (u-v) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),sq_nonneg (lp 2 u-1),sq_nonneg (lp 2 v-1),hpos (u-v) 2,Real.sqrt_nonneg 2]
    have du : lp 2 (u-v) ≤ c*lp p (u-v) := by simpa only [Nat.cast_ofNat] using (lp_compare (by norm_num : (0:ℝ)<2) hl (u-v)).2
    have hc2 : 2^(1/p:ℝ)*c = Real.sqrt 2 := by
      dsimp [c];rw [←Real.rpow_add (by norm_num : (0:ℝ)<2),Real.sqrt_eq_rpow];congr 1;ring
    apply (min_le_left _ _).trans
    apply le_of_mul_le_mul_right _ hc
    rw [hc2,mul_comm]
    exact le.trans du
end OMA.S_mo_254006
open OMA.S_mo_254006
theorem OMA.solution : type_of% @OMA.S_mo_254006.main := by
  refine ⟨fun _ hp => plane_exact hp,fun _ hm => one_exact hm,?_,fun _ hm => two_exact hm,
    fun _ _ hm hp => ⟨(finite_bounds hm hp).1,upper hm (by linarith)⟩,
    fun _ hp hne => ⟨asymptotic hp hne,zero_limit hp hne⟩⟩
  intro m hm
  rw [(one_exact (show 0 < m by omega)).csInf_eq]
  have e : 1 < (m:ℝ) := by exact_mod_cast hm
  apply (div_lt_iff₀ (by positivity)).2
  have h := (Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) e)
  simpa using (show (2:ℝ)<1*(1+Real.sqrt m) by rw [Real.sqrt_one] at h;linarith)
