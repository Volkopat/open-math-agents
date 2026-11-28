import OMAStatements.S_oeis_a278897
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Vandermonde

/-!
Dobiński's identity realizes the entries as positive sums of the kernels
k^((i+j)^2). For positive k the kernel is diagonal factors times
exp(2 log(k) i j). Expanding the exponential gives a sum of squares.
The k = 2 summand is strictly positive by Vandermonde injectivity.
-/

namespace OMA.S_oeis_a278897

open Finset Matrix

private theorem summable_finite {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) : Summable (fun k => ∑ i ∈ s, f i k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact summable_zero
  | insert a s ha ih =>
    have hsa : Summable (f a) := hf a (mem_insert_self _ _)
    have hs : Summable (fun k => ∑ i ∈ s, f i k) := ih (fun i hi => hf i (mem_insert_of_mem hi))
    simpa only [sum_insert ha] using hsa.add hs

private theorem tsum_finite {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    (∑' k, ∑ i ∈ s, f i k) = ∑ i ∈ s, ∑' k, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hsa : Summable (f a) := hf a (mem_insert_self _ _)
    have hsf (i : ι) (hi : i ∈ s) := hf i (mem_insert_of_mem hi)
    have hs := summable_finite s f hsf
    simp only [sum_insert ha]
    rw [hsa.tsum_add hs, ih hsf]

private theorem exp_series (x : ℝ) : Real.exp x = ∑' k : ℕ, x^k / (k.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

private noncomputable def poissonTerm (n k : ℕ) : ℝ := (k : ℝ)^n / (k.factorial : ℝ)

private theorem poisson_step (n k : ℕ) :
    poissonTerm (n+1) (k+1) =
      ∑ i ∈ range (n+1), (n.choose i : ℝ)*poissonTerm (n-i) k := by
  have h : (k : ℝ)+1 ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hb : ((k : ℝ)+1)^n =
      ∑ i ∈ range (n+1), (n.choose i : ℝ)*(k : ℝ)^(n-i) := by
    rw [add_comm, add_pow]
    simp [mul_comm]
  unfold poissonTerm
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ,
    show ((k : ℝ)+1)^n*((k : ℝ)+1)/(((k : ℝ)+1)*(k.factorial : ℝ)) =
      ((k : ℝ)+1)^n/(k.factorial : ℝ) by field_simp <;> ring,
    hb, sum_div]
  apply sum_congr rfl
  intro i _
  ring

private theorem summable_poisson (n : ℕ) : Summable (poissonTerm n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have h : poissonTerm 0 = fun k => (1 : ℝ)/(k.factorial : ℝ) := by
        funext k
        simp only [poissonTerm,pow_zero]
      rw [h]
      simpa only [one_pow] using Real.summable_pow_div_factorial 1
    | succ n =>
      apply (summable_nat_add_iff 1).mp
      simp only [poisson_step]
      apply summable_finite (range (n+1)) (fun i k => (n.choose i : ℝ)*poissonTerm (n-i) k)
      intro i hi
      exact (ih (n-i) (by omega)).mul_left _

private theorem dobinski (n : ℕ) :
    Real.exp 1*(Nat.bell n : ℝ) = ∑' k, poissonTerm n k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [exp_series, poissonTerm]
    | succ n =>
      rw [(summable_poisson (n+1)).tsum_eq_zero_add]
      simp only [poissonTerm, Nat.cast_zero, zero_pow (Nat.succ_ne_zero _), zero_div, zero_add]
      change Real.exp 1*(Nat.bell (n+1) : ℝ) = ∑' k, poissonTerm (n+1) (k+1)
      simp only [poisson_step]
      rw [tsum_finite (range (n+1)) (fun i k => (n.choose i : ℝ)*poissonTerm (n-i) k)
        (fun i _ => (summable_poisson (n-i)).mul_left _)]
      simp_rw [Summable.tsum_mul_left _ (summable_poisson _), ← ih _ (Nat.lt_succ_of_le (Nat.sub_le _ _))]
      have h : Iic n = range (n+1) := by
        ext i
        simp only [mem_Iic, mem_range]
        omega
      rw [Nat.bell_succ, h, Nat.cast_sum, mul_sum]
      apply sum_congr rfl
      intro i _
      push_cast
      ring


private noncomputable def expForm {n : ℕ} (v : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, v i * v j * Real.exp (t * (i.val : ℝ) * (j.val : ℝ))

private noncomputable def expTerm {n : ℕ} (v : Fin n → ℝ) (t : ℝ) (d : ℕ) : ℝ :=
  (t^d / (d.factorial : ℝ)) * (∑ i, v i * (i.val : ℝ)^d)^2

private theorem exp_term_expand {n : ℕ} (v : Fin n → ℝ) (t : ℝ) (d : ℕ) :
    expTerm v t d =
      ∑ i, ∑ j, v i * v j * ((t * (i.val : ℝ) * (j.val : ℝ))^d / (d.factorial : ℝ)) := by
  unfold expTerm
  rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  rw [mul_pow, mul_pow]
  ring

private theorem exp_term_sum {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    Summable (expTerm v t) ∧ (∑' d, expTerm v t d) = expForm v t := by
  let f (i j : Fin n) (d : ℕ) :=
    v i*v j*((t*(i.val : ℝ)*(j.val : ℝ))^d/(d.factorial : ℝ))
  have hs (i j : Fin n) : Summable (f i j) :=
    (Real.summable_pow_div_factorial _).mul_left _
  have hi (i : Fin n) : Summable (fun d => ∑ j, f i j d) :=
    summable_finite univ (f i) (fun j _ => hs i j)
  constructor
  · have hf : expTerm v t = fun d => ∑ i, ∑ j, f i j d := by
      funext d
      exact exp_term_expand v t d
    rw [hf]
    exact summable_finite univ (fun i d => ∑ j, f i j d) (fun i _ => hi i)
  · simp_rw [exp_term_expand]
    rw [tsum_finite univ (fun i d => ∑ j, f i j d) (fun i _ => hi i)]
    unfold expForm
    apply sum_congr rfl
    intro i _
    rw [tsum_finite univ (f i) (fun j _ => hs i j)]
    apply sum_congr rfl
    intro j _
    dsimp [f]
    rw [Summable.tsum_mul_left _ (Real.summable_pow_div_factorial _), ← exp_series]

private theorem exp_term_nonneg {n : ℕ} (v : Fin n → ℝ) (t : ℝ) (ht : 0 ≤ t) (d : ℕ) :
    0 ≤ expTerm v t d := by
  unfold expTerm
  exact mul_nonneg (div_nonneg (pow_nonneg ht _) (by positivity)) (sq_nonneg _)

private theorem exp_form_nonneg {n : ℕ} (v : Fin n → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ expForm v t := by
  rw [← (exp_term_sum v t).2]
  exact tsum_nonneg (exp_term_nonneg v t ht)

private theorem exp_form_pos {n : ℕ} (v : Fin n → ℝ) (t : ℝ) (ht : 0 < t) (hv : v ≠ 0) :
    0 < expForm v t := by
  classical
  have h : ∃ d : Fin n, (∑ i : Fin n, v i * (i.val : ℝ)^d.val) ≠ 0 := by
    by_contra! hn
    apply hv
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := fun i : Fin n => (i.val : ℝ))
    · intro i j hcast
      change (i.val : ℝ) = (j.val : ℝ) at hcast
      exact Fin.ext (by exact_mod_cast hcast)
    · exact hn
  obtain ⟨d,hd⟩ := h
  have hpos : 0 < expTerm v t d.val := by
    unfold expTerm
    exact mul_pos (div_pos (pow_pos ht _) (by positivity)) (sq_pos_of_ne_zero hd)
  obtain ⟨hs,he⟩ := exp_term_sum v t
  rw [←he]
  exact hpos.trans_le (hs.le_tsum d.val (fun j _ => exp_term_nonneg v t ht.le j))

private noncomputable def kernel {n : ℕ} (v : Fin n → ℝ) (r : ℕ) : ℝ :=
  ∑ i, ∑ j, v i * v j * (r : ℝ)^((i.val+j.val)^2)

private noncomputable def weight {n : ℕ} (v : Fin n → ℝ) (r : ℕ) (i : Fin n) : ℝ :=
  v i*(r:ℝ)^(i.val^2)

private theorem kernel_eq_exp {n : ℕ} (v : Fin n → ℝ) (r : ℕ) (hr : 0 < r) :
    kernel v r = expForm (weight v r) (2*Real.log (r:ℝ)) := by
  unfold kernel expForm
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  have harg : 2 * Real.log (r:ℝ) * (i.val:ℝ) * (j.val:ℝ) =
      ((2*i.val*j.val : ℕ) : ℝ)*Real.log (r:ℝ) := by
    push_cast
    ring
  rw [harg, Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hr),
    show (i.val+j.val)^2=i.val^2+j.val^2+2*i.val*j.val by ring]
  simp only [pow_add, weight]
  ring

private theorem kernel_zero {n : ℕ} (v : Fin n → ℝ) :
    kernel v 0 = (∑ i, v i * (if i.val=0 then (1:ℝ) else 0))^2 := by
  unfold kernel
  rw [pow_two, Finset.sum_mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  simp only [Nat.cast_zero]
  by_cases hi : i.val=0 <;> by_cases hj : j.val=0
  · simp [hi,hj]
  · have he : (i.val+j.val)^2 ≠ 0 := by positivity
    simp [hi,hj,zero_pow he]
  · have he : (i.val+j.val)^2 ≠ 0 := by positivity
    simp [hi,hj,zero_pow he]
  · have he : (i.val+j.val)^2 ≠ 0 := by positivity
    simp [hi,hj,zero_pow he]

private theorem kernel_nonneg {n : ℕ} (v : Fin n → ℝ) (r : ℕ) : 0 ≤ kernel v r := by
  by_cases h : r=0
  · subst r
    rw [kernel_zero]
    positivity
  · rw [kernel_eq_exp v r (by omega)]
    have hr : (1:ℝ) ≤ r := by exact_mod_cast (show 1≤r by omega)
    exact exp_form_nonneg _ _ (mul_nonneg (by positivity) (Real.log_nonneg hr))

private theorem kernel_two_pos {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < kernel v 2 := by
  rw [kernel_eq_exp v 2 (by decide)]
  have ht : 0 < 2*Real.log ((2:ℕ):ℝ) :=
    mul_pos (by positivity) (Real.log_pos (by norm_num))
  refine exp_form_pos _ _ ht ?_
  intro h
  apply hv
  funext i
  have hi := congrFun h i
  change v i * ((2:ℕ):ℝ)^(i.val^2) = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_right (by positivity)


private noncomputable def bellForm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i*v j*(Nat.bell ((i.val+j.val)^2) : ℝ)

private theorem kernel_div {n : ℕ} (v : Fin n → ℝ) (r : ℕ) :
    kernel v r/(r.factorial : ℝ) =
      ∑ i, ∑ j, v i*v j*poissonTerm ((i.val+j.val)^2) r := by
  unfold kernel poissonTerm
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  rw [sum_div]
  apply sum_congr rfl
  intro j _
  ring

private theorem bell_kernel_sum {n : ℕ} (v : Fin n → ℝ) :
    Summable (fun r => kernel v r/(r.factorial : ℝ)) ∧
      (∑' r, kernel v r/(r.factorial : ℝ)) = Real.exp 1*bellForm v := by
  let f (i j : Fin n) (r : ℕ) := v i*v j*poissonTerm ((i.val+j.val)^2) r
  have hs (i j : Fin n) : Summable (f i j) := (summable_poisson _).mul_left _
  have hi (i : Fin n) : Summable (fun r => ∑ j, f i j r) :=
    summable_finite univ (f i) (fun j _ => hs i j)
  constructor
  · simp_rw [kernel_div]
    exact summable_finite univ (fun i r => ∑ j, f i j r) (fun i _ => hi i)
  · simp_rw [kernel_div]
    rw [tsum_finite univ (fun i r => ∑ j, f i j r) (fun i _ => hi i)]
    unfold bellForm
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [tsum_finite univ (f i) (fun j _ => hs i j), mul_sum]
    apply sum_congr rfl
    intro j _
    dsimp [f]
    rw [Summable.tsum_mul_left _ (summable_poisson _), ← dobinski]
    ring

private theorem bell_form_pos {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < bellForm v := by
  obtain ⟨hs,ht⟩ := bell_kernel_sum v
  have hpos : 0 < kernel v 2/(Nat.factorial 2 : ℝ) := div_pos (kernel_two_pos v hv) (by positivity)
  have hle := hs.le_tsum 2 (fun r _ => div_nonneg (kernel_nonneg v r) (by positivity))
  rw [ht] at hle
  exact (mul_pos_iff_of_pos_left (Real.exp_pos 1)).1 (hpos.trans_le hle)

private theorem bell_det_pos (n : ℕ) : 0 < (hankel n).det := by
  let M := (Int.castRingHom ℝ).mapMatrix (hankel n)
  have he (i j : Fin n) : M i j = (Nat.bell ((i.val+j.val)^2) : ℝ) := by
    simp [M, hankel]
  have hp : M.PosDef := by
    try rw [Matrix.posDef_iff_dotProduct_mulVec]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      rw [he,he,add_comm j.val i.val]
      simp
    · intro v hv
      have hform : dotProduct (star v) (M *ᵥ v) = bellForm v := by
        unfold dotProduct Matrix.mulVec bellForm
        apply sum_congr rfl
        intro i _
        change star v i * (∑ j, M i j*v j) = _
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        rw [he]
        simp only [Pi.star_apply, star_trivial]
        ring
      rw [hform]
      exact bell_form_pos v hv
  have h := hp.det_pos
  have hmap := (Int.castRingHom ℝ).map_det (hankel n)
  change ((hankel n).det : ℝ) = M.det at hmap
  rw [← hmap] at h
  exact_mod_cast h

end OMA.S_oeis_a278897

theorem OMA.solution : type_of% @OMA.S_oeis_a278897.main :=
  OMA.S_oeis_a278897.bell_det_pos
