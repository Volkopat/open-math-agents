import OMAStatements.S_mo_308231

/-! An elementary proof for the Poisson maximum. The public discussion cites Theorem 2
of “Ultra log-concavity of discrete order statistics”; here the proof uses the Poisson
recurrence and finite differences of powers directly. -/

namespace OMA.S_mo_308231
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The difference quotient of the (k+1)-st power. -/
private def sec : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | k+1, a, b => a^(k+1) + b*sec k a b

private lemma diff_pow (k : ℕ) (a b : ℝ) : a^(k+1)-b^(k+1)=(a-b)*sec k a b := by
  induction k with
  | zero => simp [sec]
  | succ k ih =>
    simp only [sec]
    calc
      _ = (a-b)*a^(k+1) + b*(a^(k+1)-b^(k+1)) := by ring
      _ = _ := by rw [ih]; ring

private lemma sec_pos (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ sec k a b := by
  induction k with
  | zero => simp [sec]
  | succ k ih => simpa only [sec] using add_nonneg (pow_nonneg ha _) (mul_nonneg hb ih)

private lemma sec_mono (k : ℕ) {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a≤c) (hbd : b≤d) :
    sec k a b ≤ sec k c d := by
  induction k with
  | zero => simp [sec]
  | succ k ih =>
    exact add_le_add (pow_le_pow_left₀ ha hac _) (mul_le_mul hbd ih (sec_pos _ ha hb) (hb.trans hbd))

private lemma sec_scale (k : ℕ) (r a b : ℝ) : sec k (r*a) (r*b)=r^k*sec k a b := by
  induction k with
  | zero => simp [sec]
  | succ k ih => rw [sec,sec,ih,mul_pow,pow_succ r]; ring

private lemma sec_concave (k : ℕ) {A B C D : ℝ} (hA : 0≤A) (hB : 0<B) (hC : 0≤C)
    (hD : 0≤D) (h₁ : A*C≤B^2) (h₂ : B*D≤C^2) :
    sec k B A * sec k D C ≤ sec k C B ^ 2 := by
  let r := C/B
  have hr : 0 ≤ r := div_nonneg hC hB.le
  have hBC : r*B=C := by dsimp [r]; field_simp
  have hAB : r*A≤B := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_le_iff₀ hB]
    nlinarith
  have hCD : D≤r*C := by
    dsimp [r]
    rw [div_mul_eq_mul_div,le_div_iff₀ hB]
    nlinarith
  have hL : r^k * sec k B A ≤ sec k C B := by
    rw [← sec_scale]
    exact sec_mono k (mul_nonneg hr hB.le) (mul_nonneg hr hA) hBC.le hAB
  have hR : sec k D C ≤ r^k * sec k C B := by
    rw [← sec_scale]
    exact sec_mono k hD hC hCD hBC.ge
  calc
    _ ≤ sec k B A * (r^k*sec k C B) := mul_le_mul_of_nonneg_left hR (sec_pos _ hB.le hA)
    _ = (r^k * sec k B A)*sec k C B := by ring
    _ ≤ _ := by simpa [sq] using mul_le_mul_of_nonneg_right hL (sec_pos k hC hB.le)

private noncomputable def p (l : ℝ≥0) (j : ℕ) := (poissonMeasure l).real {j}
private noncomputable def F (l : ℝ≥0) (j : ℕ) := (poissonMeasure l).real (Iio j)

private lemma succ_F (l : ℝ≥0) (j : ℕ) : F l (j+1) = F l j + p l j := by
  have he : Iio (j+1) = Iio j ∪ {j} := by
    ext i
    simp only [mem_Iio,mem_union,mem_singleton_iff]
    omega
  rw [F,he,measureReal_union]
  · rfl
  · simp
  · simp

private lemma pos_F (l : ℝ≥0) (hl : 0<l) (j : ℕ) : 0<F l (j+1) := by
  rw [succ_F]
  exact add_pos_of_nonneg_of_pos measureReal_nonneg (poissonMeasure_real_singleton_pos _ hl)

private lemma rate (l : ℝ≥0) (j : ℕ) : ((j:ℝ)+1)*p l (j+1) = (l:ℝ)*p l j := by
  simp only [p,poissonMeasure_real_singleton,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one,pow_succ]
  field_simp

private lemma p_concave (l : ℝ≥0) (j : ℕ) : p l j * p l (j+2) ≤ p l (j+1)^2 := by
  have h := rate l (j+1)
  push_cast at h
  have h' := rate l j
  apply le_of_mul_le_mul_left (a := (j:ℝ)+1+1) _ (by positivity)
  calc
    _ = p l j * (((j:ℝ)+1+1)*p l (j+2)) := by ring
    _ = ((j:ℝ)+1)*p l (j+1)^2 := by rw [h]; linear_combination -(p l (j+1))*h'
    _ ≤ _ := by nlinarith [sq_nonneg (p l (j+1))]

private lemma F_concave (l : ℝ≥0) (j : ℕ) : F l j * F l (j+2) ≤ F l (j+1)^2 := by
  have hrate (t : ℕ) : (l:ℝ)*F l t ≤ t*F l (t+1) := by
    induction t with
    | zero => simp [F]
    | succ t ih =>
      have h := rate l t
      have hF : 0 ≤ F l (t+1) := measureReal_nonneg
      rw [succ_F l (t+1),succ_F l t] at *
      push_cast
      nlinarith
  have hF : (l:ℝ)*F l j ≤ ((j:ℝ)+1)*F l (j+1) := by
    nlinarith [hrate j,show 0≤F l (j+1) from measureReal_nonneg]
  have hb : F l j * p l (j+1) ≤ F l (j+1)*p l j := by
    apply le_of_mul_le_mul_left (a := (j:ℝ)+1) _ (by positivity)
    calc
      _ = F l j * (((j:ℝ)+1)*p l (j+1)) := by ring
      _ = ((l:ℝ)*F l j)*p l j := by rw [rate]; ring
      _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hF (show 0≤p l j from measureReal_nonneg)
  rw [succ_F l (j+1)]
  rw [succ_F l j] at hb ⊢
  nlinarith

end OMA.S_mo_308231

namespace OMA.S_mo_308231
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
private lemma supremum_mass {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (l : ℝ≥0) (k : ℕ) (X : Fin (k+1) → Ω → ℕ) (hm : ∀ i, Measurable (X i))
    (hi : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = poissonMeasure l) (j : ℕ) :
    μ.real {ω | Finset.univ.sup (fun i => X i ω) = j} =
      ((poissonMeasure l).real (Iio (j+1)))^(k+1) - ((poissonMeasure l).real (Iio j))^(k+1) := by
  let M (ω : Ω) := Finset.univ.sup (fun i => X i ω)
  have sets (j : ℕ) : {ω | M ω < j} = ⋂ i ∈ (Finset.univ : Finset (Fin (k+1))), X i ⁻¹' Iio j := by
    ext ω
    simp [M,← Finset.sup'_eq_sup Finset.univ_nonempty,Finset.sup'_lt_iff]
  have meas (t : ℕ) : MeasurableSet {ω | M ω < t} := by
    rw [sets]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hm i measurableSet_Iio
  have cdf (t : ℕ) : μ.real {ω | M ω < t} = ((poissonMeasure l).real (Iio t))^(k+1) := by
    rw [sets, measureReal_def,hi.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => Iio t)
      (fun _ _ => measurableSet_Iio), ENNReal.toReal_prod]
    have hmap (i : Fin (k+1)) : μ (X i ⁻¹' Iio t) = poissonMeasure l (Iio t) := by
      rw [← Measure.map_apply (hm i) measurableSet_Iio, hlaw]
    simp [hmap,measureReal_def]
  change μ.real {ω | M ω = j} = _
  have he : {ω | M ω = j} = {ω | M ω < j+1} \ {ω | M ω < j} := by
    ext ω
    simp only [mem_ofPred_eq,mem_sdiff]
    omega
  have hsub : {ω | M ω < j} ⊆ {ω | M ω < j+1} := fun _ h => Nat.lt_trans h (Nat.lt_succ_self _)
  rw [he,measureReal_sdiff hsub (meas j),cdf,cdf]

end OMA.S_mo_308231

theorem OMA.solution : type_of% @OMA.S_mo_308231.main := by
  intro Ω _ μ _ l n X hl hn hm hi hlaw j
  cases n with
  | zero => omega
  | succ k =>
    let p := OMA.S_mo_308231.p l
    let F := OMA.S_mo_308231.F l
    let s (t : ℕ) := OMA.S_mo_308231.sec k (F (t+1)) (F t)
    have val (t : ℕ) : μ.real {ω | Finset.univ.sup (fun i => X i ω) = t} = p t * s t := by
      rw [OMA.S_mo_308231.supremum_mass μ l k X hm hi hlaw t]
      change F (t+1)^(k+1)-F t^(k+1)=p t*s t
      rw [OMA.S_mo_308231.diff_pow]
      congr 1
      change OMA.S_mo_308231.F l (t+1) - OMA.S_mo_308231.F l t = _
      rw [OMA.S_mo_308231.succ_F]
      ring
    have hs : s j * s (j+2) ≤ s (j+1)^2 := OMA.S_mo_308231.sec_concave k
      (by exact MeasureTheory.measureReal_nonneg : 0 ≤ F j) (OMA.S_mo_308231.pos_F _ hl j)
      (by exact MeasureTheory.measureReal_nonneg : 0 ≤ F (j+2))
      (by exact MeasureTheory.measureReal_nonneg : 0 ≤ F (j+3))
      (OMA.S_mo_308231.F_concave _ j) (OMA.S_mo_308231.F_concave _ (j+1))
    have hp := OMA.S_mo_308231.p_concave l j
    have hnn (t : ℕ) : 0 ≤ s t := OMA.S_mo_308231.sec_pos k
      MeasureTheory.measureReal_nonneg MeasureTheory.measureReal_nonneg
    rw [val,val,val]
    calc
      _ = (p j * p (j+2)) * (s j*s (j+2)) := by ring
      _ ≤ (p (j+1))^2 * (s (j+1))^2 := mul_le_mul hp hs (mul_nonneg (hnn _) (hnn _)) (sq_nonneg _)
      _ = _ := by ring
