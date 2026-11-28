import OMAStatements.S_mo_254125
namespace OMA.S_mo_254125
open Finset
private def win (M t i : ℕ) : Prop := i ≤ t ∧ t < i+M
private instance (M t i : ℕ) : Decidable (win M t i) := by unfold win;infer_instance

private lemma comm3 (s a b : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ t ∈ s, ∑ i ∈ a, ∑ j ∈ b, f t i j =
      ∑ i ∈ a, ∑ j ∈ b, ∑ t ∈ s, f t i j := by
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_comm

private lemma window_count (N M i j : ℕ) (hi : i < N) (hj : j < N) :
    ((range (N+M-1)).filter (fun t => win M t i ∧ win M t j)).card =
      ((range M).filter (fun l => near (l+1) i j)).card := by
  have e₁ : (range (N+M-1)).filter (fun t => win M t i ∧ win M t j) =
      Ico (max i j) (min i j+M) := by
    apply Finset.ext; intro t
    rw [Finset.mem_filter,mem_range,mem_Ico]
    unfold win;omega
  have e₂ : (range M).filter (fun l => near (l+1) i j) = Ico (max i j-min i j) M := by
    ext l;simp [near];omega
  rw [e₁,e₂,Nat.card_Ico,Nat.card_Ico]
  omega

private lemma window_total (N M : ℕ) (x : ℕ → ℝ) :
    (∑ t ∈ range (N+M-1), ∑ i ∈ range N, if win M t i then x i else 0) =
      M * ∑ i ∈ range N,x i := by
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro i hi
  have e : (range (N+M-1)).filter (fun t => win M t i) = Ico i (i+M) := by
    apply Finset.ext; intro t
    rw [Finset.mem_filter,mem_range,mem_Ico]
    have := mem_range.mp hi
    unfold win;omega
  rw [←sum_filter,e,sum_const,Nat.card_Ico]
  simp
private lemma window_square (N M : ℕ) (x : ℕ → ℝ) :
    (∑ t ∈ range (N+M-1), (∑ i ∈ range N, if win M t i then x i else 0)^2) =
      ∑ l ∈ range M,band N (l+1) x := by
  simp only [pow_two,sum_mul,mul_sum,band]
  rw [comm3 (range (N+M-1)) (range N) (range N),comm3 (range M) (range N) (range N)]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have e (t : ℕ) : (if win M t j then x j else 0)*(if win M t i then x i else 0) =
      if win M t i ∧ win M t j then x i*x j else 0 := by
    by_cases h : win M t i <;> by_cases k : win M t j <;> simp [h,k,mul_comm]
  simp_rw [e]
  rw [←sum_filter,←sum_filter,sum_const,sum_const,window_count N M i j (mem_range.mp hi) (mem_range.mp hj)]

private lemma triangle (M : ℕ) : (∑ l ∈ range M,((l:ℝ)+1))*2 = M*(M+1) := by
    induction M with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ,Nat.cast_add_one]
      linarith only [show (k:ℝ)*(k+1) = (∑ l ∈ range k, ((l:ℝ)+1))*2 from ih.symm]

private lemma band_lower {N M : ℕ} (hN : 0 < N) (hM : 0 < M) {q : ℝ} (hq : feasible N M q) :
    (2*(M:ℝ)/(M+1))*((N:ℝ)/(N+((M:ℝ)-1))) ≤ q := by
  obtain ⟨x,_,hs,hb⟩ := hq
  let a (t : ℕ) := ∑ i ∈ range N,if win M t i then x i else 0
  have cs := sq_sum_le_card_mul_sum_sq (s:=range (N+M-1)) (f:=a)
  simp only [a,window_square,window_total,hs,card_range,Nat.cast_sub (show 1 ≤ N+M by omega),Nat.cast_add,Nat.cast_one] at cs
  have hsum := sum_le_sum (s:=range M) (fun l hl => hb (l+1) (by omega) (by have := mem_range.mp hl;omega))
  have tri := triangle M
  simp only [Nat.cast_add_one,←mul_sum] at hsum
  have hn0 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have H := cs.trans (mul_le_mul_of_nonneg_left hsum (by linarith [Nat.cast_nonneg (α:=ℝ) M]))
  have n0 : 0 < (N:ℝ) := by exact_mod_cast hN
  have m0 : 0 < (M:ℝ) := by exact_mod_cast hM
  have hm1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  rw [div_mul_div_comm,div_le_iff₀ (mul_pos (by positivity) (by linarith))]
  apply (le_of_mul_le_mul_left (a:=(N:ℝ)*M) _ (mul_pos n0 m0))
  nlinarith only [H,congrArg (fun z:ℝ => q*N*((N:ℝ)+M-1)*z) tri]
private def pairSum (N m : ℕ) (x y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, if near m i j then x i*y j else 0

private lemma pair_symm (N m : ℕ) (x y : ℕ → ℝ) : pairSum N m x y = pairSum N m y x := by
  unfold pairSum
  rw [sum_comm]
  simp only [near,max_comm,min_comm,mul_comm]

private lemma pair_comb (N m : ℕ) (x y z : ℕ → ℝ) (a b : ℝ) :
    pairSum N m (fun i => a*x i+b*y i) z = a*pairSum N m x z + b*pairSum N m y z := by
  unfold pairSum
  simp only [mul_sum,←sum_add_distrib]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by by_cases h : near m i j <;> simp [h] <;> ring

private def indic (S : Finset ℕ) (i : ℕ) : ℝ := if i∈S then 1 else 0

private lemma row_card (N m i : ℕ) (hm : 0 < m) :
    ((range N).filter (fun j => near m i j)).card ≤ 2*m-1 := by
  have hsub : (range N).filter (fun j => near m i j) ⊆ Ico (i+1-m) (i+m) := by
    intro j hj; have h := (mem_filter.mp hj).2
    simp only [near] at h
    rw [mem_Ico]; omega
  have h := card_le_card hsub
  rw [Nat.card_Ico] at h
  omega

private lemma pair_ones (N m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ range N) :
    pairSum N m (indic S) (fun _ => 1) ≤ S.card * (2*(m:ℝ)-1) := by
  unfold pairSum
  have line (i : ℕ) : (∑ j ∈ range N, if near m i j then indic S i*1 else 0) ≤
      if i∈S then 2*(m:ℝ)-1 else 0 := by
    by_cases h : i∈S
    · simp only [indic,h,if_true,mul_one,sum_boole]
      have h' : (( (range N).filter (fun j => near m i j)).card:ℝ)+1 ≤ 2*(m:ℝ) := by
        exact_mod_cast (show ((range N).filter (fun j => near m i j)).card+1 ≤ 2*m by have := row_card N m i hm;omega)
      linarith
    · simp [indic,h]
  have H := sum_le_sum (s:=range N) fun i _ => line i
  rwa [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr hS,sum_const,nsmul_eq_mul] at H

private lemma pair_diag (N m : ℕ) (S : Finset ℕ) (hS : S ⊆ range N)
    (hsep : ∀ i∈S, ∀ j∈S, near m i j → i=j) (hm : 0 < m) :
    pairSum N m (indic S) (indic S) = (S.card : ℝ) := by
  have entry (i j : ℕ) : (if near m i j then indic S i*indic S j else 0) =
      if j=i then indic S i else 0 := by
    by_cases hi : i∈S <;> by_cases hj : j∈S <;> by_cases h : j=i <;> by_cases k : near m i j <;>
      simp_all [indic,near] <;> grind
  simp only [pairSum,entry,sum_ite_eq',mem_range]
  simp only [←mem_range,Finset.sum_congr rfl (fun i (hi : i∈range N) => if_pos hi),indic,sum_boole,
    filter_mem_eq_inter,inter_eq_right.mpr hS]

private lemma spike_bound (N m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ range N)
    (hsep : ∀ i∈S, ∀ j∈S, near m i j → i=j) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    band N m (fun i => a+b*indic S i) ≤
      (2*(m:ℝ)-1)*((N:ℝ)*a^2+2*S.card*a*b) + S.card*b^2 := by
  let one : ℕ → ℝ := fun _ => 1
  let x : ℕ → ℝ := fun i => a*one i+b*indic S i
  have hconstant : pairSum N m one one ≤ N*(2*(m:ℝ)-1) := by
    have h := pair_ones N m hm (range N) (by rfl)
    convert h using 1
    · apply sum_congr rfl;intro i hi;simp [one,indic,hi]
    · simp
  have hcross := pair_ones N m hm S hS
  have hdi := pair_diag N m S hS hsep hm
  change pairSum N m (fun i => a+b*indic S i) (fun i => a+b*indic S i) ≤ _
  rw [show (fun i => a+b*indic S i)=x by funext i;simp [x,one]]
  rw [show pairSum N m x x = a*pairSum N m one x+b*pairSum N m (indic S) x from pair_comb ..,
    pair_symm N m one x,pair_symm N m (indic S) x,
    show pairSum N m x one = _ from pair_comb N m one (indic S) one a b,
    show pairSum N m x (indic S) = _ from pair_comb N m one (indic S) (indic S) a b,
    pair_symm N m one (indic S),hdi]
  change pairSum N m (indic S) one ≤ S.card*(2*(m:ℝ)-1) at hcross
  nlinarith only [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hconstant),
    mul_nonneg (mul_nonneg ha hb) (sub_nonneg.mpr hcross)]
private lemma spikes_data (N M : ℕ) (hn : 0 < N) (hm : 0 < M) :
    spikes N M ⊆ range N ∧ (spikes N M).card = (N-1)/M+1 ∧ N ≤ (spikes N M).card*M ∧
      (∀ i∈spikes N M, ∀ j∈spikes N M, near M i j → i=j) := by
  have hc : (spikes N M).card=(N-1)/M+1 := by
    rw [spikes,card_image_of_injective _ (fun i j h => Nat.eq_of_mul_eq_mul_right hm h),card_range]
  refine ⟨?_,hc,?_,?_⟩
  · intro i hi
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hi
    have hle : r ≤ (N-1)/M := by have := mem_range.mp hr;omega
    have H := (Nat.le_div_iff_mul_le hm).mp hle
    apply mem_range.mpr;omega
  · rw [hc]
    have h := (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self ((N-1)/M))
    change N-1 < ((N-1)/M+1)*M at h
    omega
  · intro i hi j hj hh
    obtain ⟨r,_,rfl⟩ := mem_image.mp hi
    obtain ⟨s,_,rfl⟩ := mem_image.mp hj
    rcases lt_trichotomy r s with h|rfl|h
    · have H := Nat.mul_le_mul_right M (Nat.succ_le_iff.mpr h)
      rw [Nat.succ_mul] at H
      dsimp [near] at hh;omega
    · rfl
    · have H := Nat.mul_le_mul_right M (Nat.succ_le_iff.mpr h)
      rw [Nat.succ_mul] at H
      dsimp [near] at hh;omega

private lemma family_meets (N M : ℕ) (hn : 0 < N) (hm : 0 < M) :
    meets N M (2*(M:ℝ)/(M+1)) (profile N M) := by
  obtain ⟨hsub,hcard,hNK,hsep⟩ := spikes_data N M hn hm
  let S := spikes N M
  let K : ℝ := S.card
  let r := Real.sqrt (K/(N+K))
  let a := 1-r
  let b := N/K*r
  have hk : 0<K := by dsimp [K,S];rw [hcard];positivity
  have hn' : 0<(N:ℝ) := by exact_mod_cast hn
  have hm' : 0<(M:ℝ) := by exact_mod_cast hm
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2=K/(N+K) := Real.sq_sqrt (by positivity)
  have hrle : r ≤ 1 := by
    have h : K/(N+K) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  have ha : 0 ≤ a := by dsimp [a];linarith
  have hb : 0 ≤ b := by dsimp [b];positivity
  change S ⊆ range N at hsub
  change N ≤ S.card*M at hNK
  have hprof : profile N M = (fun i => a+b*indic S i) := by rfl
  rw [hprof]
  have en : (N:ℝ)*a+K*b=N := by dsimp [a,b];field_simp;ring
  have e₂ : K*b^2=(N:ℝ)^2/(N+K) := by
    dsimp [b];rw [mul_pow,hr2];field_simp
  have e₁ : (N:ℝ)*a^2+2*K*a*b=(N:ℝ)^2/(N+K) := calc
    _ = (N:ℝ)*(1-r^2) := by dsimp [a,b];field_simp;ring
    _ = _ := by rw [hr2];field_simp;ring
  refine ⟨fun i _ => add_nonneg ha (mul_nonneg hb (by dsimp [indic];split_ifs <;> norm_num)),?_,?_⟩
  · simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,← mul_sum,indic,sum_boole,
      filter_mem_eq_inter,inter_eq_right.mpr hsub]
    change N*a + b*K=N
    linarith only [en]
  · intro m hm₁ hm₂
    have hnear : ∀ i∈S, ∀ j∈S, near m i j → i=j := fun i hi j hj h => hsep i hi j hj (by
      dsimp [near] at h ⊢;omega)
    have h0 := spike_bound N m hm₁ S hsub hnear a b ha hb
    change band N m (fun i => a+b*indic S i) ≤ _ at h0
    change band N m _ ≤ (2*(m:ℝ)-1)*((N:ℝ)*a^2+2*K*a*b)+K*b^2 at h0
    rw [e₁,e₂] at h0
    refine h0.trans ?_
    have hnK : (N:ℝ) ≤ K*M := by dsimp [K];exact_mod_cast hNK
    have hratio : (N:ℝ)/(N+K) ≤ M/(M+1:ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)];linarith
    have he := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2*(N:ℝ)*m by positivity)
    convert he using 1 <;> ring
private lemma band_one (N : ℕ) (x : ℕ → ℝ) : band N 1 x = ∑ i ∈ range N, (x i)^2 := by
  have e (i j : ℕ) : near 1 i j ↔ j=i := by unfold near;omega
  simp only [band,e,sum_ite_eq',mem_range]
  exact sum_congr rfl fun i hi => by simp [mem_range.mp hi,pow_two]

private lemma moment_bounds {N M : ℕ} (hn : 0 < N) (hm : 0 < M) {q : ℝ} {x}
    (hx : meets N M q x) :
    ((M:ℝ)^2*((N:ℝ)/(N+((M:ℝ)-1))) - q*(M*(M+1:ℝ)/2-1) ≤
      (∑ i ∈ range N,(x i)^2)/(N:ℝ)) ∧ (∑ i ∈ range N,(x i)^2)/(N:ℝ) ≤ q := by
  obtain ⟨_,hs,hb⟩ := hx
  have n0 : 0<(N:ℝ) := by exact_mod_cast hn
  have m1 : (1:ℝ) ≤ M := by exact_mod_cast hm
  have W : 0<(N:ℝ)+(M-1) := by linarith
  have cs := sq_sum_le_card_mul_sum_sq (s:=range (N+M-1))
    (f:=fun t => ∑ i ∈ range N,if win M t i then x i else 0)
  simp only [window_square,window_total,hs,card_range,Nat.cast_sub (show 1 ≤ N+M by omega),Nat.cast_add,Nat.cast_one] at cs
  let d (l : ℕ) := q*N*((l:ℝ)+1)-band N (l+1) x
  have hd {l} (hl : l∈range M) : 0 ≤ d l := by
    have H := hb (l+1) (by omega) (by have := mem_range.mp hl;omega)
    simp only [Nat.cast_add_one] at H
    exact sub_nonneg.mpr H
  have elt := single_le_sum (f:=d) (fun l hl => hd hl) (show 0 ∈ range M from mem_range.mpr hm)
  simp only [d,Nat.cast_zero,zero_add,mul_one,band_one,sum_sub_distrib,←mul_sum] at elt
  have ht : ∑ l ∈ range M, ((l:ℝ)+1) = (M:ℝ)*(M+1)/2 := by linarith [triangle M]
  rw [ht] at elt
  have hbig : (M:ℝ)^2*N^2/((N:ℝ)+(M-1)) ≤ ∑ l ∈ range M,band N (l+1) x := by
    rw [div_le_iff₀ W]
    nlinarith only [cs]
  constructor
  · rw [le_div_iff₀ n0]
    have e : (M:ℝ)^2*((N:ℝ)/(N+((M:ℝ)-1)))*N = M^2*N^2/((N:ℝ)+(M-1)) := by ring
    rw [sub_mul,e]
    linarith
  · rw [div_le_iff₀ n0]
    simpa only [band_one,Nat.cast_one,mul_one] using hb 1 (by decide) hm

private lemma moment_limit (M : ℕ) (hm : 0 < M) (q : ℕ → ℝ) (x : ℕ → ℕ → ℝ)
    (hx : ∀ N, 0 < N → meets N M (q N) (x N))
    (hq : Filter.Tendsto q Filter.atTop (nhds (2*(M:ℝ)/(M+1)))) :
    Filter.Tendsto (fun N : ℕ => (∑ i ∈ range N,(x N i)^2)/(N:ℝ))
      Filter.atTop (nhds (2*(M:ℝ)/(M+1))) := by
  have h := ((tendsto_natCast_div_add_atTop ((M:ℝ)-1)).const_mul ((M:ℝ)^2)).sub
    (hq.mul_const ((M:ℝ)*(M+1)/2-1))
  have eval : (M:ℝ)^2*1-2*M/(M+1)*(M*(M+1)/2-1)=2*M/(M+1) := by field_simp;ring
  rw [eval] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h hq
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hn using (moment_bounds hn hm (hx N hn)).1
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hn using (moment_bounds hn hm (hx N hn)).2
private lemma spike_gap {k M : ℕ} (hk : 0 < k) (hm : 2 ≤ M) :
    profile (k*M) M 0 - profile (k*M) M 1 = (M:ℝ)/Real.sqrt (M+1) := by
  have hm0 : 0 < M := by omega
  have hm1 : 1 < M := by omega
  have hkM := Nat.mul_pos hk hm0
  have hc : (spikes (k*M) M).card=k := by
    rw [(spikes_data _ _ hkM hm0).2.1]
    have t : (k*M-1)/M=k-1 := by
      apply Nat.div_eq_of_lt_le
      all_goals rcases k with _|k <;> simp_all [Nat.succ_mul] <;> omega
    omega
  have h₀ : 0∈spikes (k*M) M := by
    unfold spikes
    exact mem_image.mpr ⟨0,mem_range.mpr (Nat.succ_pos _),by simp⟩
  have h₁ : 1∉spikes (k*M) M := by
    intro h
    obtain ⟨j,_,hj⟩ := mem_image.mp h
    rcases j with _|j
    · simp at hj
    · rw [Nat.succ_mul] at hj;omega
  simp only [profile,h₀,h₁,hc,if_true,if_false,mul_one,mul_zero,add_zero,Nat.cast_mul]
  have hk' : 0<(k:ℝ) := by exact_mod_cast hk
  have eq : (k:ℝ)/(k*M+k) = 1/(M+1) := by field_simp
  rw [eq,Real.sqrt_div (by positivity),Real.sqrt_one]
  field_simp
  <;> ring

private lemma opt_bounds (N M : ℕ) (hn : 0 < N) (hm : 0 < M) :
    (2*(M:ℝ)/(M+1))*((N:ℝ)/(N+((M:ℝ)-1))) ≤ optimum N M ∧
      optimum N M ≤ 2*(M:ℝ)/(M+1) := by
  let q : ℝ := 2*M/(M+1)
  have hq : feasible N M q := ⟨_,family_meets _ _ hn hm⟩
  exact ⟨le_csInf ⟨_,hq⟩ (by intro b hb;exact band_lower hn hm hb),
    csInf_le ⟨_,fun _ hb => band_lower hn hm hb⟩ hq⟩
open Filter Topology
private lemma fixed_limit (M : ℕ) (hm : 0 < M) :
    Tendsto (fun N : ℕ => optimum N M) atTop (𝓝 (2*(M:ℝ)/(M+1))) := by
  have h := (tendsto_natCast_div_add_atTop ((M:ℝ)-1)).const_mul (2*(M:ℝ)/(M+1))
  rw [mul_one] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with N hN using (opt_bounds N M hN hm).1
  · filter_upwards [eventually_gt_atTop 0] with N hN using (opt_bounds N M hN hm).2

private lemma large_bands : Tendsto (fun M : ℕ => 2*(M:ℝ)/(M+1)) atTop (𝓝 2) := by
  have h := (tendsto_natCast_div_add_atTop (1:ℝ)).const_mul 2
  simpa only [mul_one,mul_div_assoc] using h

private lemma joint_limit (B : ℕ → ℕ) (hB : Tendsto B atTop atTop) :
    Tendsto (fun N : ℕ => optimum N (B N)) atTop (𝓝 2) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨M,hm,hMa⟩ := ((eventually_gt_atTop 0).and (large_bands.eventually (lt_mem_nhds ha))).exists
    have hclose := (fixed_limit M hm).eventually (lt_mem_nhds hMa)
    filter_upwards [hclose,eventually_gt_atTop 0,hB.eventually (eventually_ge_atTop M)] with N hN₁ hn hBN
    refine hN₁.trans_le ?_
    have hB₀ := hm.trans_le hBN
    have hne : ({q | feasible N (B N) q} : Set ℝ).Nonempty := ⟨_,_,family_meets N (B N) hn hB₀⟩
    apply le_csInf hne
    rintro q ⟨x,hx,hs,hb⟩
    apply csInf_le
    · exact ⟨_,fun _ h => band_lower hn hm h⟩
    · exact ⟨x,hx,hs,fun m hm₁ hm₂ => hb m hm₁ (hm₂.trans hBN)⟩
  · intro a ha
    filter_upwards [eventually_gt_atTop 0,hB.eventually (eventually_gt_atTop 0)] with N hn hB₀
    refine ((opt_bounds N (B N) hn hB₀).2.trans ?_).trans_lt ha
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
end OMA.S_mo_254125
open OMA.S_mo_254125 Filter Topology
theorem OMA.solution : type_of% @OMA.S_mo_254125.main := by
  exact ⟨fun N M hN hM => ⟨(opt_bounds N M hN hM).1,(opt_bounds N M hN hM).2,
      family_meets N M hN hM⟩,fixed_limit,large_bands,joint_limit,moment_limit,fun _ _ hk hm => spike_gap hk hm⟩
