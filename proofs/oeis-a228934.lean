import OMAStatements.S_oeis_a228934

namespace OMA.S_oeis_a228934

private def u (t : ℝ) := 2*t-t^2
private noncomputable def v (t : ℝ) := t*(1-t)^2/2

private def State (t : ℝ) (q : ℤ) := 0<t ∧ t<1/16 ∧ 2*(q:ℝ)*t=1+t^2

private theorem below_round {z w : ℝ} (q : ℤ) (hz : 0 < |z|) (hw : 0<w) (hgap : 2*w < |z|)
    (he : (q:ℝ)*|z|+w=1) : magnitude z=q := by
  rw [magnitude,round_eq_iff]
  constructor
  · apply (le_div_iff₀ hz).mpr; nlinarith
  · apply (div_lt_iff₀ hz).mpr; nlinarith

private theorem u_pos {t : ℝ} (hp : 0<t) (ht : t<1) : 0<u t := by
  unfold u
  nlinarith [mul_pos hp (by linarith : 0<1-t)]

private theorem advance {t : ℝ} {q : ℤ} (h : State t q) :
    State (t^2) (2*q^2-1) := by
  obtain ⟨hp,ht,he⟩ := h
  refine ⟨sq_pos_of_pos hp,by nlinarith [mul_pos hp (by linarith : 0<1-t)],?_⟩
  push_cast
  have hh := congrArg (fun x:ℝ => x^2) he
  nlinarith only [hh]

private theorem two_steps {t : ℝ} {q : ℤ} (h : State t q) :
    digit (-u t) = -q ∧ step (-u t) = -v t ∧
    digit (-v t) = -(4*(q+1)) ∧ step (-v t) = -u (t^2) := by
  obtain ⟨hp,ht,he⟩ := h
  have ht1 : t<1 := by linarith
  have hu := u_pos hp ht1
  have hv : 0<v t := by unfold v; positivity
  have htp := sq_pos_of_pos hp
  have hts : t^2<t := by nlinarith [mul_pos hp (by linarith : 0<1-t)]
  have hw := u_pos htp (by linarith : t^2<1)
  have h1 : (q:ℝ)*u t+v t=1 := by unfold u v; linear_combination (1-t/2)*he
  have h2 : ((4*(q+1):ℤ):ℝ)*v t + u (t^2)=1 := by
    push_cast; unfold u v; linear_combination (1-t)^2 * he
  have hvsmall : 2*v t<u t := by
    unfold u v
    nlinarith [mul_pos hp (by linarith : 0<1+t-t^2)]
  have hwsmall : 2*u (t^2)<v t := by
    have h4 : 4*t^2 < t/4 := by nlinarith [mul_pos hp (by linarith : 0<1/16-t)]
    have h5 : t/4 < v t := by
      unfold v
      nlinarith [mul_pos hp (by nlinarith [sq_nonneg t] : 0 < (1-t)^2-1/2)]
    unfold u
    nlinarith [sq_nonneg (t^2)]
  have mag1 : magnitude (-u t)=q := below_round q (by simpa only [abs_neg,abs_of_pos hu] using hu) hv (by simpa only [abs_neg,abs_of_pos hu] using hvsmall) (by simpa only [abs_neg,abs_of_pos hu] using h1)
  have mag2 : magnitude (-v t)=4*(q+1) := below_round _ (by simpa only [abs_neg,abs_of_pos hv] using hv) hw (by simpa only [abs_neg,abs_of_pos hv] using hwsmall) (by simpa only [abs_neg,abs_of_pos hv] using h2)
  refine ⟨by simp [digit,neg_lt_zero.mpr hu,mag1],?_,
    by simp [digit,neg_lt_zero.mpr hv,mag2],?_⟩
  · rw [step,mag1,abs_neg,abs_of_pos hu]; linear_combination h1
  · rw [step,mag2,abs_neg,abs_of_pos hv]; linear_combination h2

private theorem initial : a 4 = -99 ∧
    ∃ t, State t 199 ∧ residual 4 = -u t := by
  let s := Real.sqrt 44
  have hs : s^2=44 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ s := Real.sqrt_nonneg _
  have hlo : 6633249580710799/1000000000000000 < s := by nlinarith
  have hhi : s < 6633249580710800/1000000000000000 := by nlinarith
  have h0 : residual 0=s-6 := rfl
  have hpos0 : 0<residual 0 := by rw [h0]; linarith
  have hq0 : magnitude (residual 0)=2 := by
    rw [magnitude,round_eq_iff,abs_of_pos hpos0,h0]
    constructor
    · apply (le_div_iff₀ (by linarith : 0<s-6)).mpr; norm_num; linarith
    · apply (div_lt_iff₀ (by linarith : 0<s-6)).mpr; norm_num; linarith
  have h1 : residual 1=2*s-13 := by
    change step (residual 0)=_
    rw [step,abs_of_pos hpos0,hq0,h0]; push_cast; ring
  have hpos1 : 0<residual 1 := by rw [h1]; linarith
  have hq1 : magnitude (residual 1)=4 := by
    rw [magnitude,round_eq_iff,abs_of_pos hpos1,h1]
    constructor
    · apply (le_div_iff₀ (by linarith : 0<2*s-13)).mpr; norm_num; linarith
    · apply (div_lt_iff₀ (by linarith : 0<2*s-13)).mpr; norm_num; linarith
  have h2 : residual 2=8*s-53 := by
    change step (residual 1)=_
    rw [step,abs_of_pos hpos1,hq1,h1]; push_cast; ring
  have hpos2 : 0<residual 2 := by rw [h2]; linarith
  have hq2 : magnitude (residual 2)=15 := by
    rw [magnitude,round_eq_iff,abs_of_pos hpos2,h2]
    constructor
    · apply (le_div_iff₀ (by linarith : 0<8*s-53)).mpr; norm_num; linarith
    · apply (div_lt_iff₀ (by linarith : 0<8*s-53)).mpr; norm_num; linarith
  have h3 : residual 3=120*s-796 := by
    change step (residual 2)=_
    rw [step,abs_of_pos hpos2,hq2,h2]; push_cast; ring
  have hneg3 : residual 3<0 := by rw [h3]; linarith
  have hq3 : magnitude (residual 3)=99 := by
    rw [magnitude,round_eq_iff,abs_of_neg hneg3,h3]
    constructor
    · apply (le_div_iff₀ (by linarith : 0< -(120*s-796))).mpr; norm_num; linarith
    · apply (div_lt_iff₀ (by linarith : 0< -(120*s-796))).mpr; norm_num; linarith
  refine ⟨by change digit (residual 3) = _; simp [digit,hneg3,hq3],199-30*s,
    ⟨by linarith,by linarith,by push_cast; nlinarith⟩,?_⟩
  change step (residual 3) = _
  rw [step,abs_of_neg hneg3,hq3,h3]
  unfold u
  push_cast
  nlinarith

private theorem states (k : ℕ) : ∃ t q, State t q ∧ residual (2*k+4) = -u t := by
  induction k with
  | zero =>
    obtain ⟨t,ht,he⟩ := initial.2
    exact ⟨t,199,ht,he⟩
  | succ k ih =>
    obtain ⟨t,q,ht,he⟩ := ih
    obtain ⟨_,hstep,_,hstep'⟩ := two_steps ht
    refine ⟨t^2,2*q^2-1,advance ht,?_⟩
    rw [show 2*(k+1)+4=(2*k+4+1)+1 by omega,residual,residual,he,hstep,hstep']

private theorem digits (k : ℕ) : ∃ q : ℤ, 0<q ∧ a (2*k+5) = -q ∧
    a (2*k+6) = -(4*(q+1)) ∧ a (2*k+7) = -(2*q^2-1) := by
  obtain ⟨t,q,ht,he⟩ := states k
  obtain ⟨ha,hstep,hb,hstep'⟩ := two_steps ht
  have hpos : 0 < (q:ℝ) := by
    by_contra! hn
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hn ht.1.le,ht.2.2,sq_nonneg t]
  refine ⟨q,by exact_mod_cast hpos,?_,?_,?_⟩
  · simpa [a,he] using ha
  · change digit (step (residual (2*k+4)))=_
    rw [he,hstep,hb]
  · change digit (step (step (residual (2*k+4))))=_
    rw [he,hstep,hstep',(two_steps (advance ht)).1]

end OMA.S_oeis_a228934

open OMA.S_oeis_a228934 in
theorem OMA.solution : type_of% @OMA.S_oeis_a228934.main := by
  constructor
  · intro n hn
    by_cases h4 : n=4
    · rw [h4,initial.1]; decide
    let k := (n-5)/2
    obtain ⟨q,hq,ho,he,_⟩ := digits k
    rcases (by dsimp [k]; omega : n=2*k+5 ∨ n=2*k+6) with h|h <;> rw [h]
    · rw [ho]; omega
    · rw [he]; omega
  · intro n hn
    let k := n-3
    obtain ⟨q,_,ho,he,hs⟩ := digits k
    rw [show 2*n=2*k+6 by dsimp [k]; omega]
    simp only [show 2*k+6-1=2*k+5 by omega,show 2*k+6+1=2*k+7 by omega,ho,he,hs]
    constructor <;> ring
