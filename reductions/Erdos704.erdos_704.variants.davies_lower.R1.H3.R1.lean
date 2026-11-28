import OMAReductions.R_Erdos704_erdos_704_variants_davies_lower_R1

/-! # Higher-dimensional radial transference

Reduction of Davies's Theorem 6.3 to the torsion filter and the spherical
approximation in Lemmas 6.1 and 6.2 of arXiv:2610.12301. We prove the
simultaneous integral positioning by a scaled Householder reflection, deduce
nonnegativity of the constant from Fourier decay, and combine the two
estimates with the weighted exceptional-set bound.
-/

-- Credit: @AlfredMelson

namespace OMA.R_Erdos704_erdos_704_variants_davies_lower_R1_H3_R1
open Finset Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology FourierTransform Real

theorem position {n : ℕ} (W : Finset (Fin (n+1) → ℤ)) (h : ∀ w ∈ W, w ≠ 0) :
    ∃ (L : ℤ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ), 0 < L ∧
      (∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) = L^2 * (w ⬝ᵥ w)) ∧
      ∀ w ∈ W, (A *ᵥ w) 0 ≠ 0 := by
  let form (w : Fin (n+1) → ℤ) : MvPolynomial (Fin n) ℤ :=
    ((∑ i : Fin n, X i ^ 2) - 1) * C (w 0) -
      2 * ∑ i : Fin n, X i * C (w i.succ)

  have evalForm (w : Fin (n+1) → ℤ) (u : Fin n → ℤ) :
      eval u (form w) = ((∑ i, u i ^ 2)-1)*w 0 - 2*∑ i, u i*w i.succ := by
    simp [form]

  have form_ne (w : Fin (n+1) → ℤ) (hn : w ≠ 0) : form w ≠ 0 := by
    intro h
    have z (u : Fin n → ℤ) := congrArg (eval u) h
    apply hn
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · have hz := z 0
      rw [evalForm] at hz
      simpa using hz
    · have hz := z (fun j => if j = i then 1 else 0)
      simp [evalForm, ite_pow, zero_pow, ite_mul] at hz
      simpa using hz

  have simultaneous (W : Finset (Fin (n+1) → ℤ)) (h : ∀ w ∈ W, w ≠ 0) :
      ∃ u : Fin n → ℤ, ∀ w ∈ W, eval u (form w) ≠ 0 := by
    classical
    by_contra! fail
    have vanish : (∏ w ∈ W, form w) = 0 := by
      apply MvPolynomial.funext
      intro u
      obtain ⟨w, hw, he⟩ := fail u
      simpa using Finset.prod_eq_zero hw he
    exact (Finset.prod_ne_zero_iff.mpr (fun w hw => form_ne w (h w hw))) vanish
  let reflection (v : Fin (n+1) → ℤ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
    (v ⬝ᵥ v) • 1 - (2 : ℤ) • vecMulVec v v

  have action (v w : Fin (n+1) → ℤ) :
      reflection v *ᵥ w = (v ⬝ᵥ v) • w - (2 * (v ⬝ᵥ w)) • v := by
    dsimp only [reflection]
    rw [sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec]
    ext i
    simp [mul_assoc]

  have normScale (v w : Fin (n+1) → ℤ) :
      (reflection v *ᵥ w) ⬝ᵥ (reflection v *ᵥ w) = (v ⬝ᵥ v)^2 * (w ⬝ᵥ w) := by
    simp only [action, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    rw [dotProduct_comm w v]
    ring
  obtain ⟨u,hu⟩ := simultaneous W h
  let v : Fin (n+1) → ℤ := Fin.cons 1 u
  have dot (w) : v ⬝ᵥ w = w 0 + ∑ i, u i * w i.succ := by
    simp [dotProduct,Fin.sum_univ_succ,v]
  have self : v ⬝ᵥ v = 1 + ∑ i, u i^2 := by simp [dot,v,pow_two]
  refine ⟨_, reflection v, ?_, normScale v, ?_⟩
  · rw [self]
    positivity
  · intro w hw
    have he := hu w hw
    rw [evalForm] at he
    rw [action]
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,self,dot]
    have hv : v 0 = 1 := rfl
    rw [hv]
    intro eq
    apply he
    linarith

theorem decay (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun t : ℝ => ∫ u in (-1:ℝ)..1, Real.cos (2*Real.pi*t*u)*g u) atTop (𝓝 0) := by
  classical
  let S := Ioc (-1:ℝ) 1
  let f : ℝ → ℂ := S.indicator fun u => (g u : ℂ)
  have hm : MeasurableSet S := measurableSet_Ioc
  have h := (Real.tendsto_integral_exp_smul_cocompact f).mono_left atTop_le_cocompact
  have hr := (Complex.continuous_re.tendsto 0).comp h
  change Tendsto _ atTop (𝓝 (0:ℝ)) at hr
  convert hr using 1
  funext t
  change _ = (∫ u : ℝ, Real.fourierChar (-(u*t)) • f u).re
  have eq : (fun u : ℝ => Real.fourierChar (-(u*t)) • f u) =
      S.indicator (fun u => (Complex.exp ((2*Real.pi*(-(u*t)):ℝ)*Complex.I)) * (g u : ℂ)) := by
    funext u
    by_cases hu : u ∈ S <;> simp [f,hu,Circle.smul_def,Real.fourierChar_apply]
  rw [eq,integral_indicator hm, intervalIntegral.integral_of_le (by norm_num)]
  let b (u : ℝ) := Complex.exp ((2*Real.pi*(-(u*t)):ℝ)*Complex.I) * (g u : ℂ)
  have hb : Continuous b := by dsimp [b]; fun_prop
  have hi : IntegrableOn b S := hb.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  change _ = (∫ u in S, b u).re
  change _ = RCLike.re (∫ u in S, b u)
  rw [← integral_re hi]
  apply setIntegral_congr_fun hm
  intro u _
  change _ = (Complex.exp (↑(2*Real.pi*(-(u*t))) * Complex.I) * (g u : ℂ)).re
  rw [Complex.mul_re,Complex.exp_re]
  simp [mul_left_comm,mul_comm,mul_assoc]

theorem averageLower {I : Type*} [Fintype I] [Nonempty I] (bad : Finset I)
    (g : I → ℝ) (D M ε : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (small : 2*D*M < ε) (frac : (bad.card:ℝ) ≤ D*Fintype.card I)
    (good : ∀ i ∉ bad, -(D*M) ≤ g i) (rough : ∀ i ∈ bad, -M ≤ g i) :
    0 < ε + (1/(Fintype.card I:ℝ))*∑ i, g i := by
  classical
  let N : ℝ := Fintype.card I
  have hn : 0 < N := by dsimp [N]; exact_mod_cast (Fintype.card_pos (α := I))
  have lo (i : I) : -(D*M) - (if i ∈ bad then M else 0) ≤ g i := by
    by_cases hi : i ∈ bad
    · simp only [hi,if_true]; linarith [rough i hi, mul_nonneg hD hM]
    · simpa [hi] using good i hi
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => lo i)
  simp [sum_sub_distrib] at hsum
  have hbad := mul_le_mul_of_nonneg_right frac hM
  change 0 < ε + (1/N)*_
  rw [one_div, ← div_eq_inv_mul]
  suffices H : -ε < (∑ i, g i) / N by linarith
  apply (lt_div_iff₀ hn).mpr
  dsimp [N] at *
  nlinarith [mul_lt_mul_of_pos_right small hn]

/-- Davies Lemma 6.1: an integer similitude filter for nonzero torsion points. -/
def H1 : Prop := ∀ d : ℕ, 5 ≤ d →
  let sq (w : (Fin d → ℤ)) : ℝ := ∑ i, (w i : ℝ)^2
  let Sim (L : ℕ) (A : (Matrix (Fin d) (Fin d) ℤ)) := ∀ w : (Fin d → ℤ), sq (A *ᵥ w) = (L:ℝ)^2 * sq w
  let pull (A : (Matrix (Fin d) (Fin d) ℤ)) (θ : Fin d → ℝ) (j : Fin d) := ∑ i, (A i j : ℝ)*θ i
  let Good (q : ℕ) (γ : ℝ) (θ : Fin d → ℝ) :=
    ∀ v : (Fin d → ℤ), (∃ i, ¬ (q:ℤ) ∣ v i) → γ^2 ≤ ∑ i, (θ i - (v i:ℝ)/q)^2
  ∀ q : ℕ, 0 < q → ∀ δ : ℝ, 0 < δ →
    ∃ (L m : ℕ) (B : Fin m → (Matrix (Fin d) (Fin d) ℤ)) (γ : ℝ), 0 < L ∧ 0 < m ∧ 0 < γ ∧
    (∀ i, Sim L (B i)) ∧ ∀ θ, ∃ bad : Finset (Fin m),
      (bad.card:ℝ) ≤ δ*m ∧ ∀ i ∉ bad, Good q γ (pull (B i) θ)

/-- Davies Lemma 6.2: simultaneous radial approximation away from nonzero torsion. -/
def H2 : Prop := ∀ d : ℕ, 5 ≤ d →
  let sq (w : (Fin d → ℤ)) : ℝ := ∑ i, (w i : ℝ)^2
  let Sim (L : ℕ) (A : (Matrix (Fin d) (Fin d) ℤ)) := ∀ w : (Fin d → ℤ), sq (A *ᵥ w) = (L:ℝ)^2 * sq w
  let phase (w : (Fin d → ℤ)) (θ : Fin d → ℝ) :=
    Real.cos (2*Real.pi*∑ i, (w i : ℝ)*θ i)

  let Good (q : ℕ) (γ : ℝ) (θ : Fin d → ℝ) :=
    ∀ v : (Fin d → ℤ), (∃ i, ¬ (q:ℤ) ∣ v i) → γ^2 ≤ ∑ i, (θ i - (v i:ℝ)/q)^2
  let omegaD (d : ℕ) (t : ℝ) : ℝ :=
    (∫ u in (-1:ℝ)..1, Real.cos (2*Real.pi*t*u)*(1-u^2)^(((d:ℝ)-3)/2)) /
    (∫ u in (-1:ℝ)..1, (1-u^2)^(((d:ℝ)-3)/2))
  ∀ (W : Finset ((Fin d → ℤ))) (δ : ℝ), 0 < δ →
    (∀ w ∈ W, ∃ i : Fin d, i.val < 4 ∧ w i ≠ 0) →
    ∃ q : ℕ, 0 < q ∧ ∀ γ : ℝ, 0 < γ →
      ∃ (L j : ℕ) (G : Fin j → (Matrix (Fin d) (Fin d) ℤ)) (neg : Fin j → Fin j),
        0 < L ∧ 0 < j ∧ Function.Involutive neg ∧ (∀ i, G (neg i) = -(G i)) ∧
        (∀ i, Sim L (G i)) ∧ ∀ θ, Good q γ θ →
        ∃ τ : ℝ, 0 ≤ τ ∧ ∀ w ∈ W,
          |(1/(j:ℝ))* (∑ i, phase (G i *ᵥ w) θ) - omegaD d (Real.sqrt (sq w)*τ)| ≤ δ

lemma boundedAverage {j : ℕ} (hj : 0 < j) (f : Fin j → ℝ) (h : ∀ i, |f i| ≤ 1) :
    |(1/(j:ℝ)) * ∑ i, f i| ≤ 1 := by
  have hj' : 0 < (j:ℝ) := by exact_mod_cast hj
  rw [abs_mul, abs_of_pos (by positivity),one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ hj').mpr
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin j, (1:ℝ) := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

lemma lowerWeighted {α : Type*} (W : Finset α) (c k r : α → ℝ) (δ z : ℝ)
    (close : ∀ i ∈ W, |k i - r i| ≤ δ) (pos : 0 ≤ z + ∑ i ∈ W, c i * r i) :
    -(δ * ∑ i ∈ W, |c i|) ≤ z + ∑ i ∈ W, c i * k i := by
  have h (i) (hi : i ∈ W) : -(δ*|c i|) ≤ c i*k i - c i*r i := by
    have h1 := mul_le_mul_of_nonneg_left (close i hi) (abs_nonneg (c i))
    rw [← abs_mul] at h1
    have h2 := (abs_le.mp h1).1
    linarith only [h2, mul_sub (c i) (k i) (r i),mul_comm δ |c i|]
  have hh := Finset.sum_le_sum h
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hh
  linarith


theorem main : H1 → H2 → OMA.R_Erdos704_erdos_704_variants_davies_lower_R1.H3 := by
  classical
  let sq {d : ℕ} (w : (Fin d → ℤ)) : ℝ := ∑ i, (w i : ℝ)^2
  let Sim {d : ℕ} (L : ℕ) (A : (Matrix (Fin d) (Fin d) ℤ)) := ∀ w : (Fin d → ℤ), sq (A *ᵥ w) = (L:ℝ)^2 * sq w
  let pull {d : ℕ} (A : (Matrix (Fin d) (Fin d) ℤ)) (θ : Fin d → ℝ) (j : Fin d) := ∑ i, (A i j : ℝ)*θ i
  let phase {d : ℕ} (w : (Fin d → ℤ)) (θ : Fin d → ℝ) :=
    Real.cos (2*Real.pi*∑ i, (w i : ℝ)*θ i)

  let Good {d : ℕ} (q : ℕ) (γ : ℝ) (θ : Fin d → ℝ) :=
    ∀ v : (Fin d → ℤ), (∃ i, ¬ (q:ℤ) ∣ v i) → γ^2 ≤ ∑ i, (θ i - (v i:ℝ)/q)^2
  let omegaD (d : ℕ) (t : ℝ) : ℝ :=
    (∫ u in (-1:ℝ)..1, Real.cos (2*Real.pi*t*u)*(1-u^2)^(((d:ℝ)-3)/2)) /
    (∫ u in (-1:ℝ)..1, (1-u^2)^(((d:ℝ)-3)/2))
  have limit (d : ℕ) (hd : 5 ≤ d) : Tendsto (omegaD d) atTop (𝓝 0) := by
    have hd' : 5 ≤ (d:ℝ) := by exact_mod_cast hd
    have hc := (Real.continuous_rpow_const (by linarith : 0 ≤ ((d:ℝ)-3)/2)).comp
      (show Continuous (fun u : ℝ => 1-u^2) by fun_prop)
    unfold omegaD
    simpa [omegaD] using (decay _ hc).div_const (∫ u in (-1:ℝ)..1, (1-u^2)^(((d:ℝ)-3)/2))

  have nonneg {ι : Type} (d : ℕ) (hd : 5 ≤ d) (W : Finset ι) (r c : ι → ℝ)
      (hr : ∀ i ∈ W, 0 < r i) (cInf : ℝ)
      (hf : ∀ t : ℝ, 0 ≤ t → 0 ≤ cInf + ∑ i ∈ W, c i * omegaD d (r i * t)) : 0 ≤ cInf := by
    have hi (i) (h : i ∈ W) : Tendsto (fun t : ℝ => c i * omegaD d (r i * t)) atTop (𝓝 (0:ℝ)) := by
      simpa using ((limit d hd).comp (tendsto_id.const_mul_atTop (hr i h))).const_mul (c i)
    have hs := tendsto_finsetSum W hi
    have hh : Tendsto (fun t : ℝ => cInf + ∑ i ∈ W, c i * omegaD d (r i * t)) atTop (𝓝 cInf) := by
      simpa using hs.const_add cInf
    apply ge_of_tendsto hh
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht using hf t ht
  have phase_pull {d : ℕ} (A : (Matrix (Fin d) (Fin d) ℤ)) (w : (Fin d → ℤ)) (θ) : phase (A *ᵥ w) θ = phase w (pull A θ) := by
    unfold phase pull
    congr 2
    simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

  have sim_mul {d L K : ℕ} {A B : (Matrix (Fin d) (Fin d) ℤ)} (a : Sim L A) (b : Sim K B) : Sim (L*K) (A*B) := by
    intro w
    rw [← mulVec_mulVec, a, b]
    push_cast
    ring

  have sq_pos {d : ℕ} {w : (Fin d → ℤ)} (h : w ≠ 0) : 0 < sq w := by
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by simpa [funext_iff] using h
    apply Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, mem_univ _, ?_⟩
    exact sq_pos_of_ne_zero (by exact_mod_cast hi)
  have normalizedPosition {n : ℕ} (W : Finset ((Fin (n+1) → ℤ))) (h : ∀ w ∈ W, w ≠ 0) :
      ∃ (l : ℕ) (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℤ)), 0 < l ∧ Sim l A ∧ ∀ w ∈ W, (A *ᵥ w) 0 ≠ 0 := by
    obtain ⟨L,A,hL,hs,hp⟩ := position W h
    refine ⟨L.toNat,A,by omega, ?_,hp⟩
    intro w
    have eq := hs w
    simp only [dotProduct, ← pow_two] at eq
    have lift : (L.toNat:ℝ) = (L:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hL.le
    rw [lift]
    unfold sq
    exact_mod_cast eq
  intro filterH arcH d hd
  cases d with
  | zero => omega
  | succ n =>
    let d := n+1
    dsimp only
    intro W z c hn hf ε he
    obtain ⟨l,A,hl,hA,hproj⟩ := normalizedPosition W hn
    let M := ∑ w ∈ W, |c w|
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
    let δ := ε/(4*(M+1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hsmall : 2*δ*M < ε := by
      have hr : δ*(4*(M+1)) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith [mul_nonneg hδ.le hM]
    let AW := W.image (A *ᵥ ·)
    obtain ⟨q,hq,hq'⟩ := arcH d hd AW δ hδ (by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨0,by simp [d],hproj w hw⟩)
    obtain ⟨b,m,B,γ,hb,hm,hγ,hB,hfilter⟩ := filterH d hd q hq δ hδ
    obtain ⟨k,j,G,neg,hk,hj,hneg,hsign,hG,harc⟩ := hq' γ hγ
    have hz : 0 ≤ z := nonneg d hd W (fun w => Real.sqrt (sq w)) c
      (fun w hw => Real.sqrt_pos.2 (sq_pos (hn w hw))) z hf
    let e := Fintype.equivFin (Fin m × Fin j)
    let family (p : Fin m × Fin j) := B p.1 * (G p.2 * A)
    let flip (p : Fin m × Fin j) := (p.1,neg p.2)
    refine ⟨b*(k*l),_,fun t => family (e.symm t),fun t => e (flip (e.symm t)),
      by positivity, by simpa using Nat.mul_pos hm hj, ?_, ?_, ?_, ?_⟩
    · intro t
      simp [flip,hneg (e.symm t).2]
    · intro t
      simp [family,flip,hsign]
    · intro t
      exact sim_mul (hB _) (sim_mul (hG _) hA)
    · intro θ
      let K (i : Fin m) (w : (Fin d → ℤ)) :=
        (1/(j:ℝ)) * ∑ a, phase (G a *ᵥ (A *ᵥ w)) (pull (B i) θ)
      let F (i : Fin m) := z + ∑ w ∈ W, c w * K i w
      obtain ⟨bad,hfrac,hgood⟩ := hfilter θ
      have rough (i : Fin m) : -M ≤ F i := by
        have hh := lowerWeighted W c (K i) (fun _ => 0) 1 z (fun w _ => by
          simp only [sub_zero]
          exact boundedAverage hj _ (fun a => abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)) (by simpa using hz)
        simpa [M,F] using hh
      have good (i) (hi : i ∉ bad) : -(δ*M) ≤ F i := by
        obtain ⟨τ,hτ,happrox⟩ := harc _ (hgood i hi)
        apply lowerWeighted W c (K i) (fun w => omegaD d (Real.sqrt (sq w)*((l:ℝ)*τ))) δ z
        · intro w hw
          have H := happrox (A *ᵥ w) (Finset.mem_image_of_mem _ hw)
          change |K i w - omegaD d (Real.sqrt (sq (A *ᵥ w)) * τ)| ≤ δ at H
          rw [hA w,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)] at H
          simpa [K,mul_assoc,mul_left_comm,mul_comm] using H
        · exact hf _ (by positivity)
      let _ : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
      have total := averageLower bad F δ M ε hδ.le hM hsmall
        (by simpa using hfrac) good (fun i _ => rough i)
      change 0 < z + ε + (1/_) * ∑ t, ∑ w ∈ W, c w * phase (family (e.symm t) *ᵥ w) θ
      rw [show (∑ t, ∑ w ∈ W, c w * phase (family (e.symm t) *ᵥ w) θ) =
        ∑ p : Fin m × Fin j, ∑ w ∈ W, c w * phase (family p *ᵥ w) θ from e.symm.sum_comp (fun p => ∑ w ∈ W, c w * phase (family p *ᵥ w) θ)]
      simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Fintype.sum_prod_type] at *
      simp only [F,K,Finset.sum_add_distrib,Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at total
      have hsum (i : Fin m) :
          (∑ w ∈ W, c w * ((1/(j:ℝ))*∑ a, phase (G a *ᵥ (A *ᵥ w)) (pull (B i) θ))) =
          (1/(j:ℝ))*∑ a, ∑ w ∈ W, c w * phase (family (i,a) *ᵥ w) θ := by
        rw [Finset.sum_comm (s:=Finset.univ) (t:=W),Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        simp only [family, ← mulVec_mulVec,phase_pull (B i),Finset.mul_sum]
        ring
      simp_rw [hsum] at total
      rw [← Finset.mul_sum] at total
      have hm' : (m:ℝ) ≠ 0 := by positivity
      have hj' : (j:ℝ) ≠ 0 := by positivity
      convert total using 1
      field_simp
      ring
end OMA.R_Erdos704_erdos_704_variants_davies_lower_R1_H3_R1
