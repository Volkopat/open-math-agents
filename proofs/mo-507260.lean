import OMAStatements.S_mo_507260

namespace OMA.S_mo_507260
open Set Function
private lemma diff_deriv {N h : ℝ} (hh : 0≤h) (m : ℕ) {f g : ℝ→ℝ}
    (hd : ∀ t ∈ Icc 0 N, HasDerivWithinAt f (g t) (Icc 0 N) t) :
    ∀ t ∈ Icc 0 (N-(m:ℝ)*h), HasDerivWithinAt ((fwdDiff h)^[m] f)
      (((fwdDiff h)^[m] g) t) (Icc 0 (N-(m:ℝ)*h)) t := by
  induction m with
  | zero => simpa using hd
  | succ m ih =>
    intro t ht
    have sub : Icc 0 (N-((m+1:ℕ):ℝ)*h) ⊆ Icc 0 (N-(m:ℝ)*h) := by
      intro y hy
      have := hy.2
      push_cast at this
      exact ⟨hy.1,by linarith⟩
    have shift : MapsTo (fun y : ℝ => y+h) (Icc 0 (N-((m+1:ℕ):ℝ)*h)) (Icc 0 (N-(m:ℝ)*h)) := by
      intro y hy
      have := hy.2
      push_cast at this
      exact ⟨add_nonneg hy.1 hh,by linarith⟩
    have hs := (ih (t+h) (shift ht)).comp t ((hasDerivWithinAt_id _ _).add_const h) shift
    have hn := hs.sub ((ih t (sub ht)).mono sub)
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change HasDerivWithinAt (fun z => (fwdDiff h)^[m] f (z+h)-(fwdDiff h)^[m] f z) ((fwdDiff h)^[m] g (t+h)-(fwdDiff h)^[m] g t) _ _
    simpa only [Function.comp_def,Pi.sub_def,id_eq,mul_one] using hn
lemma analytic_diff {N x h L : ℝ} (k : ℕ) (f : ℝ→ℝ) (hN : 0<N)
    (hf : ContDiffOn ℝ k f (Icc 0 N))
    (hl : ∀ u ∈ Icc 0 N, ∀ v ∈ Icc 0 N,
      |iteratedDerivWithin k f (Icc 0 N) u-iteratedDerivWithin k f (Icc 0 N) v| ≤ L*|u-v|)
    (hh : 0≤h) (_hL : 0≤L) (hx : 0≤x) (hend : x+(k+1)*h ≤ N) :
    |(fwdDiff h)^[k+1] f x| ≤ h^(k+1)*L := by
  induction k generalizing x f with
  | zero =>
    simp only [Nat.cast_zero,zero_add,one_mul] at hend
    have h' := hl (x+h) ⟨by linarith,hend⟩ x ⟨hx,by linarith⟩
    simpa [fwdDiff,abs_of_nonneg hh,mul_comm] using h'
  | succ k ih =>
    have hd : ∀ t ∈ Icc 0 N, HasDerivWithinAt f (derivWithin f (Icc 0 N) t) (Icc 0 N) t :=
      fun t ht => (hf.differentiableOn (by norm_cast) t ht).hasDerivWithinAt
    let p := (fwdDiff h)^[k+1] f
    let q := (fwdDiff h)^[k+1] (derivWithin f (Icc 0 N))
    let T := Icc 0 (N-((k+1:ℕ):ℝ)*h)
    have hp : ∀ t ∈ T, HasDerivWithinAt p (q t) T t := diff_deriv hh _ hd
    have ht : Icc x (x+h) ⊆ T := by
      intro t ht
      have h1 := ht.2
      have he := hend
      change t ∈ Icc 0 (N-((k+1:ℕ):ℝ)*h)
      push_cast at he ⊢
      exact ⟨hx.trans ht.1,by linarith⟩
    have hpc : ContinuousOn p (Icc x (x+h)) := ContinuousOn.mono (s := T) (fun t h => (hp t h).continuousWithinAt) ht
    by_cases hzero : h=0
    · subst h
      simp [Function.iterate_succ_apply',fwdDiff]
    have hpos := lt_of_le_of_ne hh (Ne.symm hzero)
    have hd' (t : ℝ) (ht' : t∈Ioo x (x+h)) : HasDerivAt p (q t) t :=
      ((hp t (ht (Ioo_subset_Icc_self ht'))).mono ht).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)
    obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope p q (show x<x+h by linarith) hpc hd'
    have hcd : ContDiffOn ℝ k (derivWithin f (Icc 0 N)) (Icc 0 N) :=
      hf.derivWithin (uniqueDiffOn_Icc hN) (by norm_cast)
    have hlast : ∀ u ∈ Icc 0 N, ∀ v ∈ Icc 0 N,
        |iteratedDerivWithin k (derivWithin f (Icc 0 N)) (Icc 0 N) u -
          iteratedDerivWithin k (derivWithin f (Icc 0 N)) (Icc 0 N) v| ≤ L*|u-v| := by
      simpa only [iteratedDerivWithin_succ'] using hl
    have hc0 := ht (Ioo_subset_Icc_self hc)
    have hcN : c+((k:ℝ)+1)*h ≤ N := by
      have h' := hc0.2
      change c ≤ N-((k+1:ℕ):ℝ)*h at h'
      push_cast at h'
      linarith
    have hbound : |q c| ≤ h^(k+1)*L := ih _ hcd hlast hc0.1 hcN
    have he' : p (x+h)-p x=q c*h := by
      rw [show x+h-x=h by ring] at he
      exact ((eq_div_iff hzero).mp he).symm
    rw [Function.iterate_succ_apply']
    change |p (x+h)-p x| ≤ _
    rw [he',abs_mul,abs_of_nonneg hh]
    calc _ ≤ (h^(k+1)*L)*h := mul_le_mul_of_nonneg_right hbound hh
         _ = _ := by rw [pow_succ h (k+1)]; ring
end OMA.S_mo_507260

namespace OMA.S_mo_507260
private noncomputable def stencil (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  g x + 2*g (x+1/2) - g (x+1) - 4*g (x+3/2) - g (x+2) + 2*g (x+5/2) + g (x+3)
private theorem stencil_identity (f : ℝ → ℝ) (x : ℝ) :
    (fwdDiff (1:ℝ))^[4] f x = stencil ((fwdDiff (1/2:ℝ))^[2] f) x := by
  norm_num [stencil,Function.iterate_succ_apply',fwdDiff,add_assoc]
  ring
private theorem stencil_bound (g : ℝ → ℝ) (x M : ℝ)
    (h : ∀ j : ℕ, j≤6 → |g (x+j/2)| ≤ M) : |stencil g x| ≤ 12*M := by
  have h0 := abs_le.mp (h 0 (by decide))
  have h1 := abs_le.mp (h 1 (by decide))
  have h2 := abs_le.mp (h 2 (by decide))
  have h3 := abs_le.mp (h 3 (by decide))
  have h4 := abs_le.mp (h 4 (by decide))
  have h5 := abs_le.mp (h 5 (by decide))
  have h6 := abs_le.mp (h 6 (by decide))
  norm_num at h0 h1 h2 h3 h4 h5 h6
  unfold stencil
  apply abs_le.mpr
  constructor <;> linarith
private theorem diff_comm (a b : ℝ) :
    Function.Commute (fwdDiff a : (ℝ → ℝ) → _) (fwdDiff b) := by
  intro f
  funext x
  simp only [fwdDiff]
  rw [show x+a+b=x+b+a by ring]
  ring
theorem filter_bound (s : ℕ) (f : ℝ → ℝ) (x B : ℝ)
    (h : ∀ j : ℕ, j≤6*s → |(fwdDiff (1/2:ℝ))^[2*s] f (x+j/2)| ≤ B) :
    |(fwdDiff (1:ℝ))^[4*s] f x| ≤ 12^s*B := by
  induction s generalizing f x with
  | zero => simpa using h 0 (by simp)
  | succ s ih =>
    rw [show 4*(s+1)=4+4*s by omega,Function.iterate_add_apply,stencil_identity]
    rw [show 12^(s+1)*B=12*(12^s*B) by ring]
    apply stencil_bound
    intro j hj
    rw [((diff_comm (1/2:ℝ) 1).iterate_iterate 2 (4*s)) f]
    apply ih
    intro i hi
    have hb := h (i+j) (by omega)
    rw [show 2*(s+1)=2*s+2 by omega,Function.iterate_add_apply] at hb
    convert hb using 2
    push_cast
    ring
end OMA.S_mo_507260

namespace OMA.S_mo_507260
private theorem diff_alternating (h d i : ℕ) :
    (fwdDiff h)^[d] alternating i = (((-1:ℝ)^h)-1)^d * (-1)^i := by
  induction d generalizing i with
  | zero => simp [alternating]
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    change (fwdDiff h)^[d] alternating (i+h) - (fwdDiff h)^[d] alternating i = _
    rw [ih,ih,pow_add,pow_succ]
    ring
theorem data_bound (s : ℕ) (hs : 1 ≤ s) : discreteBound (2*s-1) (4*s+1) alternating (4^s) := by
  intro i h hi hh _
  rw [show 2*s-1+1=2*s by omega,diff_alternating,abs_mul]
  simp only [abs_pow,abs_neg,abs_one,one_pow,mul_one]
  have hbase : |(-1:ℝ)^h-1|≤2 := by
    have ht := abs_sub_le ((-1:ℝ)^h) 0 1
    norm_num at ht ⊢
    exact ht
  calc
    _ ≤ (2:ℝ)^(2*s) := pow_le_pow_left₀ (abs_nonneg _) hbase _
    _ = 4^s := by rw [pow_mul]; norm_num
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by exact_mod_cast hh))
private theorem sample_diff (f : ℝ → ℝ) (n : ℕ) (hf : ∀ i : ℕ, 1 ≤ i → i ≤ n → f i = alternating i)
    (d i : ℕ) (hi : 1 ≤ i) (hle : i+d ≤ n) :
    (fwdDiff (1:ℝ))^[d] f i = (fwdDiff (1:ℕ))^[d] alternating i := by
  induction d generalizing i with
  | zero => exact hf i hi (by omega)
  | succ d ih =>
    simp only [Function.iterate_succ_apply',fwdDiff]
    rw [←Nat.cast_add_one,ih (i+1) (by omega) (by omega),ih i hi (by omega)]
theorem high_sample (s : ℕ) (f : ℝ → ℝ)
    (hf : ∀ i : ℕ, 1 ≤ i → i ≤ 4*s+1 → f i = alternating i) :
    |(fwdDiff (1:ℝ))^[4*s] f 1|=16^s := by
  have hd := sample_diff f (4*s+1) hf (4*s) 1 (by decide) (by omega)
  rw [Nat.cast_one] at hd
  rw [hd,diff_alternating,abs_mul,abs_pow,pow_mul]
  norm_num
theorem extension_exists (k n : ℕ) (hn : 0 < n) : ∃ L, extensionBound k n alternating L := by
  let f : ℝ → ℝ := fun x => Real.cos (x*Real.pi)
  have hc : ContDiffOn ℝ (k+1 : ℕ) f (Set.Icc 0 (n:ℝ)) := by dsimp [f]; fun_prop
  have hd := (contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin
    (uniqueDiffOn_Icc (by exact_mod_cast hn : (0:ℝ)<n))).mp hc
  obtain ⟨L,hL⟩ := hd.2.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  refine ⟨L,L.coe_nonneg,f,hd.1,fun i _ _ => Real.cos_nat_mul_pi i,?_⟩
  intro x hx y hy
  simpa [Real.dist_eq] using hL.dist_le_mul x hx y hy
end OMA.S_mo_507260

open OMA.S_mo_507260

theorem OMA.solution : type_of% @OMA.S_mo_507260.main := by
  have lower (s : ℕ) (hs : 1 ≤ s) (L : ℝ)
      (he : extensionBound (2*s-1) (4*s+1) alternating L) : (16/3:ℝ)^s ≤ L := by
    obtain ⟨hL,f,hf,hsamp,hder⟩ := he
    have e : 2*s-1+1=2*s := by omega
    have half (j : ℕ) (hj : j≤6*s) :
        |(fwdDiff (1/2:ℝ))^[2*s] f (1+j/2)| ≤ (1/2:ℝ)^(2*s)*L := by
      have hn : (0:ℝ)<(4*s+1:ℕ) := by positivity
      have hcast : ((2*s-1:ℕ):ℝ)+1=2*(s:ℝ) := by exact_mod_cast e
      have hj' : (j:ℝ)≤6*(s:ℝ) := by exact_mod_cast hj
      have hd := analytic_diff (N:=((4*s+1:ℕ):ℝ)) (x:=(1+(j:ℝ)/2)) (h:=(1/2:ℝ))
        (L:=L) (2*s-1) f hn hf hder (by norm_num) hL (by positivity) (by push_cast; linarith)
      simpa only [e] using hd
    have hh := filter_bound s f 1 ((1/2:ℝ)^(2*s)*L) half
    rw [high_sample s f hsamp] at hh
    have ident : (12:ℝ)^s*((1/2:ℝ)^(2*s)*L) = 3^s*L := by
      rw [pow_mul,←mul_assoc,←mul_pow]
      norm_num
    rw [ident] at hh
    rw [div_pow]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have allBounds (s : ℕ) (hs : 1 ≤ s) :=
    And.intro (data_bound s hs) (And.intro (extension_exists (2*s-1) (4*s+1) (by omega)) (lower s hs))
  refine ⟨allBounds,?_⟩
  intro C hC
  obtain ⟨s,hs⟩ := pow_unbounded_of_one_lt C (by norm_num : 1 < (4/3:ℝ))
  have spos : 1 ≤ s := by
    by_contra! h
    have : s=0 := by omega
    simp [this] at hs
    linarith
  have hb := allBounds s spos
  have he : C*4^s < (16/3:ℝ)^s := by
    calc
      _ < (4/3:ℝ)^s*4^s := mul_lt_mul_of_pos_right hs (by positivity)
      _ = _ := by rw [←mul_pow]; norm_num
  refine ⟨2*s-1,4*s+1,alternating,4^s,(16/3:ℝ)^s-C*4^s,by omega,by positivity,
    sub_pos.mpr he,hb.1,hb.2.1,?_⟩
  intro L h
  linarith [hb.2.2 L h]
