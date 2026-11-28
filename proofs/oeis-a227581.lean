import OMAStatements.S_oeis_a227581
import Mathlib

-- Clark Kimberling (OEIS A227581, 2013). The companion A227582 floor was
-- previously verified by AlphaProof Nexus. The triangular approximation is
-- Ramanujan's expansion of harmonic numbers; cf. Mark Villarino (2008).
-- Credit: @Aryan-Poonacha
namespace HarmonicDiagonal

open Real Filter Topology
open OMA.S_oeis_a227581

private noncomputable def lo (z : ℝ) := z/2 - z^2/12
private noncomputable def hi (z : ℝ) := lo z + z^4/120
private noncomputable def tlo (z : ℝ) := z/6 - z^2/30
private noncomputable def thi (z : ℝ) := tlo z + 4*z^3/315

private lemma positive_from_deriv {f : ℝ → ℝ} (hf : f 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) (hd : ∀ x ∈ Set.Icc 0 s,
      ∃ v : ℝ, HasDerivAt f v x ∧ 0 ≤ v) : 0 ≤ f s := by
  have H : MonotoneOn f (Set.Icc 0 s) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x hx => (hd x hx).choose_spec.1.continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).choose_spec.1.differentiableAt.differentiableWithinAt)
      (fun x hx => by
        obtain ⟨v,hv,hp⟩ := hd x (interior_subset hx)
        simpa only [hv.deriv] using hp)
  simpa only [hf] using H (Set.left_mem_Icc.mpr hs) (Set.right_mem_Icc.mpr hs) hs

private lemma d_lo (z : ℝ) : HasDerivAt lo (1/2 - 2*z/12) z := by
  have h := hasDerivAt_id' z
  convert ((h.div_const 2).fun_sub ((h.pow 2).div_const 12)) using 1 <;> first | rfl | ring

private lemma d_tlo (z : ℝ) : HasDerivAt tlo (1/6 - 2*z/30) z := by
  have h := hasDerivAt_id' z
  convert ((h.div_const 6).fun_sub ((h.pow 2).div_const 30)) using 1 <;> first | rfl | ring

private lemma d_hi (z : ℝ) : HasDerivAt hi (1/2 - 2*z/12 + 4*z^3/120) z := by
  have h := hasDerivAt_id' z
  convert (((h.div_const 2).fun_sub ((h.pow 2).div_const 12))).fun_add ((h.pow 4).div_const 120) using 1 <;> first | rfl | ring

private lemma d_thi (z : ℝ) : HasDerivAt thi (1/6 - 2*z/30 + 12*z^2/315) z := by
  have h := hasDerivAt_id' z
  convert (((h.div_const 6).fun_sub ((h.pow 2).div_const 30))).fun_add (((h.pow 3).const_mul 4).div_const 315) using 1 <;> first | rfl | ring

private lemma step_lo (s : ℝ) (hs : 0 ≤ s) (hs' : s < 1) :
    lo (s) - lo (s/(1+s)) ≤ log (1+s) - s/(1+s) := by
  apply sub_nonneg.mp
  apply positive_from_deriv (f := fun s => (log (1+s) - s/(1+s)) - (lo (s) - lo (s/(1+s)))) (by norm_num [lo,hi,tlo,thi]) hs
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hp : 0 < 1+x := by linarith [hx.1]
  have hm : 0 < 1-x := by linarith [hx.2]
  have h := hasDerivAt_id' x
  have dp := h.const_add 1
  have dm := h.const_sub 1
  have hd1 := h.fun_div dp hp.ne'
  have de := (dp.log hp.ne').fun_sub hd1
  have dc := (d_lo x).fun_sub ((d_lo _).comp x hd1)
  refine ⟨x^4/(6*(1+x)^3), ?_, ?_⟩
  · convert de.fun_sub dc using 1
    all_goals try rfl
    all_goals field_simp [hp.ne',hm.ne']
    all_goals ring
  · positivity

private lemma step_hi (s : ℝ) (hs : 0 ≤ s) (hs' : s < 1) :
    log (1+s) - s/(1+s) ≤ hi (s) - hi (s/(1+s)) := by
  apply sub_nonneg.mp
  apply positive_from_deriv (f := fun s => (hi (s) - hi (s/(1+s))) - (log (1+s) - s/(1+s))) (by norm_num [lo,hi,tlo,thi]) hs
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hp : 0 < 1+x := by linarith [hx.1]
  have hm : 0 < 1-x := by linarith [hx.2]
  have h := hasDerivAt_id' x
  have dp := h.const_add 1
  have dm := h.const_sub 1
  have hd1 := h.fun_div dp hp.ne'
  have de := (dp.log hp.ne').fun_sub hd1
  have dc := (d_hi x).fun_sub ((d_hi _).comp x hd1)
  refine ⟨x^6*(5+5*x+x^2)/(30*(1+x)^5), ?_, ?_⟩
  · convert dc.fun_sub de using 1
    all_goals try rfl
    all_goals field_simp [hp.ne',hm.ne']
    all_goals ring
  · positivity

private lemma step_tlo (s : ℝ) (hs : 0 ≤ s) (hs' : s < 1) :
    tlo (s^2/(1-s)) - tlo (s^2/(1+s)) ≤ (log (1+s) - log (1-s))/2 - s := by
  apply sub_nonneg.mp
  apply positive_from_deriv (f := fun s => ((log (1+s) - log (1-s))/2 - s) - (tlo (s^2/(1-s)) - tlo (s^2/(1+s)))) (by norm_num [lo,hi,tlo,thi]) hs
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hp : 0 < 1+x := by linarith [hx.1]
  have hm : 0 < 1-x := by linarith [hx.2]
  have h := hasDerivAt_id' x
  have dp := h.const_add 1
  have dm := h.const_sub 1
  have de := (((dp.log hp.ne').fun_sub (dm.log hm.ne')).div_const 2).fun_sub h
  have hd0 := (h.pow 2).fun_div dm hm.ne'
  have hd1 := (h.pow 2).fun_div dp hp.ne'
  have dc := ((d_tlo _).comp x hd0).fun_sub ((d_tlo _).comp x hd1)
  refine ⟨8*x^6/(15*(1-x)^3*(1+x)^3), ?_, ?_⟩
  · convert de.fun_sub dc using 1
    all_goals try rfl
    all_goals simp only [Pi.pow_apply]
    all_goals field_simp [hp.ne',hm.ne']
    all_goals ring
  · positivity

private lemma step_thi (s : ℝ) (hs : 0 ≤ s) (hs' : s < 1) :
    (log (1+s) - log (1-s))/2 - s ≤ thi (s^2/(1-s)) - thi (s^2/(1+s)) := by
  apply sub_nonneg.mp
  apply positive_from_deriv (f := fun s => (thi (s^2/(1-s)) - thi (s^2/(1+s))) - ((log (1+s) - log (1-s))/2 - s)) (by norm_num [lo,hi,tlo,thi]) hs
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hp : 0 < 1+x := by linarith [hx.1]
  have hm : 0 < 1-x := by linarith [hx.2]
  have h := hasDerivAt_id' x
  have dp := h.const_add 1
  have dm := h.const_sub 1
  have de := (((dp.log hp.ne').fun_sub (dm.log hm.ne')).div_const 2).fun_sub h
  have hd0 := (h.pow 2).fun_div dm hm.ne'
  have hd1 := (h.pow 2).fun_div dp hp.ne'
  have dc := ((d_thi _).comp x hd0).fun_sub ((d_thi _).comp x hd1)
  refine ⟨8*x^8*(9-x^2)/(105*(1-x)^4*(1+x)^4), ?_, ?_⟩
  · convert dc.fun_sub de using 1
    all_goals try rfl
    all_goals simp only [Pi.pow_apply]
    all_goals field_simp [hp.ne',hm.ne']
    all_goals ring
  · have : 0 ≤ 9-x^2 := by nlinarith [hx.1,hx.2,sq_nonneg (x-1), mul_nonneg hx.1 hm.le]
    positivity

private noncomputable def ordE (n : ℕ) : ℝ := (harmonic n : ℝ) - log n
private noncomputable def triE (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - (log n + log (n+1))/2
private noncomputable def z (n : ℕ) : ℝ := 1/(n:ℝ)
private noncomputable def tz (n : ℕ) : ℝ := 1/((n:ℝ)*(n+1))

private lemma ord_step (n : ℕ) (hn : 2 ≤ n) :
    lo (z n) - lo (z (n+1)) ≤ ordE n - ordE (n+1) ∧
    ordE n - ordE (n+1) ≤ hi (z n) - hi (z (n+1)) := by
  have hp : 1 < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hz : 0 ≤ z n := by unfold z; positivity
  have hz' : z n < 1 := by unfold z; rw [div_lt_one (by linarith)]; linarith
  have ha : z n / (1+z n) = z (n+1) := by
    unfold z
    push_cast
    field_simp
  have hb : 1+z n = ((n:ℝ)+1)/n := by unfold z; field_simp
  have he : log (1+z n) - z n/(1+z n) = ordE n - ordE (n+1) := by
    rw [ha,hb,Real.log_div (by positivity) (by positivity)]
    simp [ordE,z,harmonic_succ]
    ring
  rw [ha] at he
  simpa only [ha,he] using And.intro (step_lo (z n) hz hz') (step_hi (z n) hz hz')

private lemma tri_step (n : ℕ) (hn : 2 ≤ n) :
    tlo (tz n) - tlo (tz (n+1)) ≤ triE n - triE (n+1) ∧
    triE n - triE (n+1) ≤ thi (tz n) - thi (tz (n+1)) := by
  have hp : 1 < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  let s : ℝ := 1/(n+1)
  have hz : 0 ≤ s := by dsimp [s]; positivity
  have hz' : s < 1 := by dsimp [s]; rw [div_lt_one (by positivity)]; linarith
  have hm : 1-s = n/((n:ℝ)+1) := by dsimp [s]; field_simp; ring
  have hp' : 1+s = ((n:ℝ)+2)/(n+1) := by dsimp [s]; field_simp; ring
  have ha : s^2/(1-s) = tz n := by rw [hm]; dsimp [s,tz]; field_simp
  have hb : s^2/(1+s) = tz (n+1) := by rw [hp']; dsimp [s,tz]; push_cast; field_simp; ring
  have he : (log (1+s) - log (1-s))/2 - s = triE n - triE (n+1) := by
    rw [hp',hm,Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity)]
    simp [triE,harmonic_succ,s]
    ring
  simpa only [ha,hb,he] using And.intro (step_tlo s hz hz') (step_thi s hz hz')

private lemma z_lim : Tendsto z atTop (𝓝 0) := by
  exact tendsto_one_div_atTop_nhds_zero_nat

private lemma tz_lim : Tendsto tz atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa [Function.comp_def,z] using z_lim.comp (tendsto_add_atTop_nat 1)
  unfold tz
  simpa [z,one_div,mul_inv_rev,mul_comm] using z_lim.mul h

private lemma tri_lim : Tendsto triE atTop (𝓝 eulerMascheroniConstant) := by
  have h : Tendsto (fun n : ℕ => log (1 + z n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_log (x:=1) one_ne_zero).tendsto.comp
      (show Tendsto (fun n : ℕ => 1+z n) atTop (𝓝 1) by simpa using tendsto_const_nhds.add z_lim)
  have h' := Real.tendsto_harmonic_sub_log.sub (h.div_const 2)
  apply (show Tendsto (fun n : ℕ => (harmonic n : ℝ) - log n - log (1+z n)/2)
      atTop (𝓝 eulerMascheroniConstant) by simpa using h').congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb : 1+z n = ((n:ℝ)+1)/n := by unfold z; field_simp
  rw [hb,Real.log_div (by positivity) hp.ne']
  unfold triE
  ring

private lemma enclose {e a b : ℕ → ℝ} (he : Tendsto e atTop (𝓝 eulerMascheroniConstant))
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ n, 2 ≤ n → a n - a (n+1) ≤ e n - e (n+1) ∧
        e n - e (n+1) ≤ b n - b (n+1)) (n : ℕ) (hn : 2 ≤ n) :
    a n ≤ e n - eulerMascheroniConstant ∧ e n - eulerMascheroniConstant ≤ b n := by
  have H (j : ℕ) : e (n+j) - a (n+j) ≤ e n - a n ∧ e n - b n ≤ e (n+j) - b (n+j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨h1,h2⟩ := h (n+j) (by omega)
      rw [← Nat.add_assoc]
      exact ⟨by linarith [ih.1],by linarith [ih.2]⟩
  have hlim (g : ℕ → ℝ) (hg : Tendsto g atTop (𝓝 0)) :
      Tendsto (fun j => e (n+j) - g (n+j)) atTop (𝓝 eulerMascheroniConstant) := by
    simpa [Function.comp_def,Nat.add_comm] using (he.sub hg).comp (tendsto_add_atTop_nat n)
  have h1 := le_of_tendsto (hlim a ha) (Eventually.of_forall (fun j => (H j).1))
  have h2 := ge_of_tendsto (hlim b hb) (Eventually.of_forall (fun j => (H j).2))
  exact ⟨by linarith,by linarith⟩

private lemma ord_bounds (n : ℕ) (hn : 2 ≤ n) :
    lo (z n) ≤ ordE n - eulerMascheroniConstant ∧ ordE n - eulerMascheroniConstant ≤ hi (z n) := by
  apply enclose Real.tendsto_harmonic_sub_log _ _ ord_step n hn
  · simpa [lo] using (z_lim.div_const 2).sub ((z_lim.pow 2).div_const 12)
  · simpa [hi,lo] using ((z_lim.div_const 2).sub ((z_lim.pow 2).div_const 12)).add
      ((z_lim.pow 4).div_const 120)

private lemma tri_bounds (n : ℕ) (hn : 2 ≤ n) :
    tlo (tz n) ≤ triE n - eulerMascheroniConstant ∧ triE n - eulerMascheroniConstant ≤ thi (tz n) := by
  apply enclose tri_lim _ _ tri_step n hn
  · simpa [tlo] using (tz_lim.div_const 6).sub ((tz_lim.pow 2).div_const 30)
  · simpa [thi,tlo] using ((tz_lim.div_const 6).sub ((tz_lim.pow 2).div_const 30)).add
      (((tz_lim.pow 3).const_mul 4).div_const 315)
private lemma gap (n : ℕ) (hn : 1 ≤ n) :
    let N := n*n+n
    let f := eulerMascheroniConstant - 2*(harmonic n : ℝ) + (harmonic N : ℝ)
    1/(6*(N:ℝ)+1) < f ∧ f < 1/(6*(N:ℝ)) := by
  dsimp only
  by_cases hn1 : n=1
  · subst n
    have hh := ord_bounds 8 (by decide)
    have he : log 8 = 3 * log 2 := by simpa only [show (2:ℝ)^3=8 by norm_num, Nat.cast_ofNat] using (Real.log_pow 2 3)
    norm_num [lo,hi,z,ordE,he,harmonic_succ,harmonic] at hh ⊢
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,hh.1,hh.2]
  have hn2 : 2 ≤ n := by omega
  let N := n*n+n
  have hN : 6 ≤ N := by dsimp [N]; nlinarith
  have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hc : (N:ℝ) = (n:ℝ)*(n+1) := by dsimp [N]; push_cast; ring
  have htr := tri_bounds n hn2
  have hor := ord_bounds N (by omega)
  have hz : tz n = z N := by unfold tz z; rw [hc]
  rw [hz] at htr
  have hid : eulerMascheroniConstant - 2*(harmonic n : ℝ) + (harmonic N : ℝ) =
      (ordE N - eulerMascheroniConstant) - 2*(triE n - eulerMascheroniConstant) := by
    unfold ordE triE
    rw [hc,Real.log_mul hp.ne' (by positivity)]
    ring
  change 1/(6*(N:ℝ)+1) < _ ∧ _ < 1/(6*(N:ℝ))
  rw [hid]
  have h6 : 6 ≤ (N:ℝ) := by exact_mod_cast hN
  have hl : 1/(6*(N:ℝ)+1) < lo (z N) - 2*thi (z N) := by
    unfold lo thi tlo z
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ (N:ℝ)-6 by linarith) (show 0 ≤ 84*(N:ℝ)+291 by positivity)]
  have hu : hi (z N) - 2*tlo (z N) < 1/(6*(N:ℝ)) := by
    unfold hi lo tlo z
    field_simp
    nlinarith [sq_nonneg ((N:ℝ)-1)]
  exact ⟨by linarith [hor.1,htr.2],by linarith [hor.2,htr.1]⟩

private def coeff (j : ℕ) : ℤ := ((6*j^2+18*j+11)/5 : ℕ)

private lemma coeff_five (j : ℕ) : coeff (j+5) = coeff j + 12*j + 48 := by
  have eq : 6*(j+5)^2+18*(j+5)+11 = 6*j^2+18*j+11 + 5*(12*j+48) := by ring
  unfold coeff
  rw [eq, Nat.add_mul_div_left _ _ (by decide : 0 < 5)]
  push_cast
  ring

private lemma base_sol (j : ℕ) :
    a227582Recurrence.mkSol ![2, 7, 14, 23, 35, 50, 67] j = coeff j := by
  symm
  apply a227582Recurrence.eq_mk_of_is_sol_of_eq_init
  · intro k
    change coeff (k+7) = ∑ i : Fin 7, ![(1:ℤ),-2,1,0,0,-1,2] i * coeff (k+i.val)
    simp [Fin.sum_univ_succ, Fin.val_succ]
    have a := coeff_five k
    have b := coeff_five (k+1)
    have c := coeff_five (k+2)
    push_cast at b c
    simp only [Nat.add_assoc] at a b c
    norm_num at a b c
    omega
  · intro i
    change Fin 7 at i
    fin_cases i <;> norm_num [coeff]

private lemma a_value (n : ℕ) (hn : 1 ≤ n) :
    a227582 n = (6*(n*n+n)-1)/5 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  have he : 6*((j+1)*(j+1)+(j+1))-1 = 6*j^2+18*j+11 := by
    have : 6*((j+1)*(j+1)+(j+1)) = 6*j^2+18*j+12 := by ring
    omega
  simp only [a227582,Nat.succ_ne_zero,if_false,Nat.succ_sub_one,base_sol,coeff,Int.toNat_natCast,he]

private lemma harm_mono : Monotone (fun n : ℕ => (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ]
  push_cast
  exact le_add_of_nonneg_right (by positivity)

end HarmonicDiagonal

open HarmonicDiagonal OMA.S_oeis_a227581 Real

theorem OMA.solution : type_of% @OMA.S_oeis_a227581.main := by
  intro n hn
  let N := n*n+n
  let f := eulerMascheroniConstant - 2*(harmonic n : ℝ) + (harmonic N : ℝ)
  let g := 2*(harmonic n : ℝ) - (harmonic (N-1) : ℝ) - eulerMascheroniConstant
  have hN : 0 < N := by dsimp [N]; omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  obtain ⟨hfL,hfU⟩ := gap n hn
  change 1/(6*(N:ℝ)+1) < f at hfL
  change f < 1/(6*(N:ℝ)) at hfU
  have hf : 0 < f := lt_trans (by positivity) hfL
  have hsum : f+g = 1/N := by
    have h := harmonic_succ (N-1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ N)] at h
    have h' := congrArg (fun s : ℚ => (s:ℝ)) h
    push_cast at h'
    dsimp [f,g]
    rw [one_div]
    linarith
  have hgL : 5/(6*(N:ℝ)) < g := by
    have h : 1/(N:ℝ) - 1/(6*N) = 5/(6*N) := by field_simp; ring
    linarith
  have hg : 0 < g := lt_trans (by positivity) hgL
  have hgU : g < 5/(6*(N:ℝ)-1) := by
    have hn1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
    have h : 1/(N:ℝ) - 1/(6*N+1) < 5/(6*N-1) := by
      have hp : 0 < 6*(N:ℝ)-1 := by linarith
      apply (lt_div_iff₀ hp).2
      field_simp
      nlinarith
    linarith
  have hup : 2*(harmonic n : ℝ) - (harmonic N : ℝ) < eulerMascheroniConstant := by
    dsimp [f] at hf
    linarith
  have hlo : eulerMascheroniConstant < 2*(harmonic n:ℝ) - (harmonic (N-1):ℝ) := by
    dsimp [g] at hg
    linarith
  refine ⟨?_,⟨hup,hlo⟩,?_,?_⟩
  · let S : Set ℕ := {k | (harmonic n:ℝ)+(harmonic n:ℝ)-(harmonic (n*n+k):ℝ) < eulerMascheroniConstant}
    change sInf S = n
    have hm : n ∈ S := by simpa [S,N,two_mul] using hup
    apply le_antisymm (Nat.sInf_le hm)
    by_contra! h
    have hs := Nat.sInf_mem (⟨n,hm⟩ : S.Nonempty)
    change (harmonic n:ℝ)+(harmonic n:ℝ)-(harmonic (n*n+sInf S):ℝ) < eulerMascheroniConstant at hs
    have hle : n*n+sInf S ≤ N-1 := by dsimp [N]; omega
    linarith [harm_mono hle]
  · rw [show 6*n*(n+1)=6*N by dsimp [N]; ring]
    change ⌊1/f⌋₊ = 6*N
    rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 1/f)]
    push_cast
    constructor
    · apply (le_div_iff₀ hf).2
      exact (lt_div_iff₀' (by positivity)).1 hfU |>.le
    · apply (div_lt_iff₀' hf).2
      exact (div_lt_iff₀ (by positivity)).1 hfL
  · rw [a_value n hn]
    change ⌊1/g⌋₊ = (6*N-1)/5
    let b := (6*N-1)/5
    have h1 : 5*b ≤ 6*N-1 := by dsimp [b]; omega
    have h2 : 6*N ≤ 5*(b+1) := by dsimp [b]; omega
    have ha : 5*(b:ℝ) ≤ 6*(N:ℝ)-1 := by
      have hx : 5*(b:ℝ)+1 ≤ 6*(N:ℝ) := by exact_mod_cast (show 5*b+1 ≤ 6*N by omega)
      linarith
    have hb : 6*(N:ℝ) ≤ 5*((b:ℝ)+1) := by exact_mod_cast h2
    have hh : 1 ≤ (N:ℝ) := by exact_mod_cast hN
    rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 1/g)]
    change (b:ℝ) ≤ 1/g ∧ 1/g < (b:ℝ)+1
    constructor
    · apply (le_div_iff₀ hg).2
      have hc := (lt_div_iff₀ (by linarith : 0 < 6*(N:ℝ)-1)).1 hgU
      nlinarith [mul_le_mul_of_nonneg_right ha hg.le]
    · apply (div_lt_iff₀' hg).2
      have hc := (div_lt_iff₀ (by positivity : 0 < 6*(N:ℝ))).1 hgL
      nlinarith [mul_le_mul_of_nonneg_right hb hg.le]
