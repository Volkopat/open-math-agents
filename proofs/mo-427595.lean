import OMAStatements.S_mo_427595
/-!
The counterexample uses the constant function 1/2 and takes r=2. At odd
dyadic stages it lowers just the middle coefficient. The height of the
middle basis polynomial makes the resulting approximation error quadratic
in the size of the individual coefficient change.
-/
namespace OMA.S_mo_427595

private noncomputable def mass (m : ℕ) : ℝ := m.centralBinom/(4:ℝ)^m

private theorem mass_nonneg (m : ℕ) : 0 ≤ mass m := by unfold mass; positivity

private theorem mass_rec (m : ℕ) :
    (2*((m:ℝ)+1))*mass (m+1)=(2*(m:ℝ)+1)*mass m := by
  have hh : ((m:ℝ)+1)*(m+1).centralBinom = 2*(2*(m:ℝ)+1)*m.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ m
  unfold mass
  rw [pow_succ]
  field_simp
  linear_combination 2*hh

/-- A squared Wallis-type bound for the normalized central binomial coefficient. -/
private theorem mass_sq (m : ℕ) : (mass m)^2*((m:ℝ)+1) ≤ 1 := by
  induction m with
  | zero => norm_num [mass]
  | succ m ih =>
    push_cast
    let t : ℝ := 2*((m:ℝ)+1)
    apply le_of_mul_le_mul_left (a := t^2) _ (by dsimp [t]; positivity)
    calc
      t^2*((mass (m+1))^2*((m:ℝ)+1+1)) =
          ((2*(m:ℝ)+1)*mass m)^2*((m:ℝ)+1+1) := by rw [← mass_rec]; dsimp [t]; ring
      _ ≤ t^2*((mass m)^2*((m:ℝ)+1)) := by
        dsimp [t]; nlinarith [mul_nonneg (sq_nonneg (mass m)) (show (0:ℝ) ≤ 3*m+2 by positivity)]
      _ ≤ t^2*1 := mul_le_mul_of_nonneg_left ih (sq_nonneg _)

theorem central_basis_bound (k : ℕ) {x : ℝ} (hx : x ∈ interval) :
    0 ≤ basis (2*2^(2*k)) (2^(2*k)) x ∧
    basis (2*2^(2*k)) (2^(2*k)) x ≤ 1/(2:ℝ)^k := by
  let m : ℕ := 2^(2*k)
  have hcast : (m:ℝ) = ((2:ℝ)^k)^2 := by dsimp [m]; push_cast; rw [Nat.mul_comm 2 k,pow_mul]
  have hx0 := hx.1
  have hx1 := hx.2
  change 0 ≤ basis (2*m) m x ∧ basis (2*m) m x ≤ _
  have hb : basis (2*m) m x = (m.centralBinom:ℝ)*(x*(1-x))^m := by
    rw [basis,show 2*m-m=m by omega,mul_pow,Nat.centralBinom_eq_two_mul_choose]; ring
  rw [hb]
  constructor
  · positivity
  · calc
      (m.centralBinom:ℝ)*(x*(1-x))^m ≤ (m.centralBinom:ℝ)*(1/4:ℝ)^m := by
        gcongr
        nlinarith [sq_nonneg (x-1/2)]
      _ = mass m := by simp [mass,div_eq_mul_inv]
      _ ≤ 1/(2:ℝ)^k := by
        rw [le_div_iff₀ (by positivity)]
        have hh := mass_sq m
        rw [hcast] at hh
        have hs : (mass m*(2:ℝ)^k)^2 ≤ 1 := by nlinarith [sq_nonneg (mass m)]
        nlinarith [sq_nonneg (mass m*(2:ℝ)^k-1)]


open Set Filter Finset
open scoped Topology

noncomputable def amp (i : ℕ) : ℝ := 1/(2:ℝ)^(i/2)

/-- Odd stages change one sample. Even stages reproduce every input. -/
noncomputable def W (i : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  g x - if i%2=1 ∧ x=1/2 then amp i else 0

noncomputable def flat : ℝ → ℝ := fun _ => 1/2

private theorem amp_nonneg (i : ℕ) : 0 ≤ amp i := by unfold amp; positivity

theorem W_bounded (i : ℕ) (g : ℝ → ℝ) (hg : ContinuousOn g interval) :
    BddAbove ((fun x => |W i g x|) '' interval) := by
  obtain ⟨B,hB⟩ := (isCompact_Icc.image_of_continuousOn hg.abs).bddAbove
  refine ⟨B+amp i,?_⟩
  rintro a ⟨x,hx,rfl⟩
  have hgx : |g x| ≤ B := hB ⟨x,hx,rfl⟩
  change |g x - (if i%2=1 ∧ x=1/2 then amp i else 0)| ≤ B+amp i
  split_ifs
  · calc
      |g x-amp i| ≤ |g x|+|amp i| := abs_sub _ _
      _ ≤ B+amp i := by rw [abs_of_nonneg (amp_nonneg _)]; linarith
  · simpa using hgx.trans (le_add_of_nonneg_right (amp_nonneg i))

theorem W_uniform (g : ℝ → ℝ) : TendstoUniformlyOn (fun i => W i g) g atTop interval := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (1/ε) (by norm_num : (1:ℝ)<2)
  filter_upwards [eventually_ge_atTop (2*n)] with i hi
  intro x hx
  have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : n ≤ i/2)
  have hlt : amp i < ε := by
    rw [amp,div_lt_iff₀ (by positivity)]
    exact (div_lt_iff₀ hε).mp (hn.trans_le hpow) |> fun h => by linarith
  simp only [W,Real.dist_eq]
  split_ifs <;> simp [abs_of_nonneg (amp_nonneg _),hlt,hε]

theorem flat_maps : MapsTo flat interval (Ioo 0 1) := by intro x hx; norm_num [flat]
theorem flat_smooth : smoothControl 2 flat (1/2) := by
  refine ⟨contDiffOn_const, ?_, ?_⟩
  · exact ⟨0,by decide,0,by norm_num [interval],by norm_num [flat]⟩
  · rintro z ⟨j,hj,x,hx,rfl⟩
    unfold flat
    rw [iteratedDerivWithin_const]
    split_ifs <;> norm_num

theorem basis_sum (n : ℕ) (x : ℝ) : ∑ j ∈ range (n+1),basis n j x = 1 := by
  have h := add_pow x (1-x) n
  simpa [basis,mul_comm,mul_left_comm,mul_assoc] using h.symm

theorem elevated_flat (n k : ℕ) (hk : k ≤ 2*n) : elevated n k flat=1/2 := by
  have hd : ((2*n).choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  unfold elevated
  apply (div_eq_iff hd).mpr
  have h : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, (n.choose p.1:ℝ)*(n.choose p.2:ℝ)) =
      ((2*n).choose k:ℝ) := by
    exact_mod_cast (by simpa [two_mul] using (Nat.add_choose_eq n n k).symm :
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,n.choose p.1*n.choose p.2=(2*n).choose k)
  simp only [flat,← sum_mul,h,mul_comm]


private theorem approx_flat (i : ℕ) (x : ℝ) (hx : x ∈ interval) :
    |flat x-bernstein (2^i) (W i flat) x| ≤ 4*(1/2)/(2^i:ℝ)^(((2:ℕ):ℝ)/2) := by
  have hn := basis_sum (2^i) x
  by_cases he : i%2=0
  · have h : W i flat=flat := by funext t; simp [W,he]
    rw [h,bernstein]
    simp only [flat,← Finset.mul_sum,hn,mul_one,sub_self,abs_zero]
    positivity
  · obtain ⟨k,rfl⟩ := Nat.odd_iff.mpr (by omega : i%2=1)
    let m : ℕ := 2^(2*k)
    have hm : 0 < m := by dsimp [m]; positivity
    have hdeg : 2^(2*k+1)=2*m := by dsimp [m]; ring
    have hep : (2*k+1)%2=1 := by omega
    have ha : amp (2*k+1) = 1/(2:ℝ)^k := by simp [amp,show (2*k+1)/2=k by omega]
    have hcenter (j : ℕ) : ((j:ℝ)/(2*m:ℕ)=1/2) ↔ j=m := by
      rw [div_eq_iff (by positivity)]
      push_cast
      rw [show (1/2:ℝ)*(2*(m:ℝ))=(m:ℝ) by ring]
      exact Nat.cast_inj
    have hv (j : ℕ) : W (2*k+1) flat ((j:ℝ)/(2*m:ℕ)) =
        1/2 - if j=m then 1/(2:ℝ)^k else 0 := by
      simp only [W,flat,hep,true_and,hcenter,ha]
    rw [hdeg] at hn
    rw [hdeg,bernstein]
    simp only [hv,sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,hn,mul_one,flat]
    have hsum : (∑ j ∈ Finset.range (2*m+1),
        (if j=m then 1/(2:ℝ)^k else 0)*basis (2*m) j x) =
        (1/(2:ℝ)^k)*basis (2*m) m x := by
      rw [Finset.sum_eq_single m]
      · simp
      · intro b hb hne; simp [hne]
      · intro h; simp at h; omega
    rw [hsum]
    obtain ⟨hb0,hb⟩ := central_basis_bound k hx
    change 0 ≤ basis (2*m) m x at hb0
    change basis (2*m) m x ≤ _ at hb
    rw [sub_sub_cancel,abs_of_nonneg (mul_nonneg (by positivity) hb0)]
    norm_num
    calc
      (2^k:ℝ)⁻¹*basis (2*m) m x ≤ (2^k:ℝ)⁻¹*(1/(2:ℝ)^k) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by rw [show (2:ℝ)^(2*k+1) = 2*((2:ℝ)^k)^2 by ring]; field_simp

end OMA.S_mo_427595
open OMA.S_mo_427595

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_427595.main) := by
  intro h
  obtain ⟨C,hC,hgood⟩ := h 2 W 4 (by decide) (by norm_num) W_bounded
  have hp := hgood flat (1/2) flat_maps (.inl flat_smooth) (W_uniform flat) approx_flat
  obtain ⟨j,hj⟩ := pow_unbounded_of_one_lt C (by norm_num : (1:ℝ)<2)
  let m : ℕ := 2^(2*j)
  have hm : 0 < m := by dsimp [m]; positivity
  have hh := hp (2*j) m (by dsimp [m]; omega)
  have old : W (2*j) flat=flat := by funext x; simp [W]
  rw [old,elevated_flat _ _ (by dsimp [m]; omega)] at hh
  have hcast : (m:ℝ)=(2:ℝ)^(2*j) := by simp [m]
  have hmid : (m:ℝ)/(2*2^(2*j):ℝ)=1/2 := by rw [hcast]; field_simp
  have hnew : (2*j+1)%2=1 := by omega
  rw [hmid] at hh
  simp only [W,hnew,true_and,if_true,amp,show (2*j+1)/2=j by omega,flat] at hh
  norm_num at hh
  rw [show (2:ℝ)^(2*j)=((2:ℝ)^j)^2 by ring] at hh
  have hp : 0<(2:ℝ)^j := by positivity
  field_simp at hh
  nlinarith [mul_pos hp (sub_pos.mpr hj)]
