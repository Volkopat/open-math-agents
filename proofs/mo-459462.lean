import OMAStatements.S_mo_459462
import Mathlib

/-!
Credited port of @connoranderson's complete public proof, linked from merged statement
PR #23735 and desk DONE note #108701, pinned at:
https://github.com/connoranderson/open-math-agents/blob/9826a3f58243c902152e1d878dd6cd367ac9f7b1/proofs/mo-459462.lean
All mathematical code is retained unchanged. This integrates existing proof work,
not a claim of a new mathematical discovery. Original problem and the cited
connection to Efron's monotonicity theorem are credited below.
-/

/-!
# The associated Stirling ratio

Problem by János Engländer, https://mathoverflow.net/questions/459462.
The fixed-block-count likelihood-ratio inequality is related to Bradley
Efron’s monotonicity theorem for sums of log-concave variables (1965,
https://www.jstor.org/stable/2238092). We prove it directly by
symmetrizing two-by-two minors of the convolution kernel. In the comparison
from k blocks to k+1 blocks, the singleton term gives strict decrease
through the last positive ratio.
-/

namespace OMA.S_mo_459462
open PowerSeries Finset
noncomputable section

def NN (f : PowerSeries ℚ) := ∀ n, 0 ≤ coeff n f
def LR (f g : PowerSeries ℚ) := ∀ i j, i≤j → coeff i f*coeff j g ≤ coeff i g*coeff j f
def ker (g : PowerSeries ℚ) (i j : ℕ) : ℚ := if i≤j then coeff (j-i) g else 0
def TP (g : PowerSeries ℚ) := ∀ i j u v, i≤j → u≤v →
  ker g i v * ker g j u ≤ ker g i u * ker g j v

lemma nn_blocks (s : ℕ) : NN (blocks s) := by
  intro n;simp only [blocks,coeff_mk];split <;> positivity

lemma nn_mul {f g : PowerSeries ℚ} (hf : NN f) (hg : NN g) : NN (f*g) := by
  intro n;rw [coeff_mul];exact sum_nonneg fun q _ => mul_nonneg (hf _) (hg _)

lemma nn_pow {f : PowerSeries ℚ} (h : NN f) (k : ℕ) : NN (f^k) := by
  induction k with
  | zero => intro n;simp [coeff_one];split <;> positivity
  | succ k ih => rw [pow_succ];exact nn_mul ih h

lemma coeff_padded (f g : PowerSeries ℚ) (n N : ℕ) (hn : n≤N) :
    coeff n (f*g)=∑ i ∈ range (N+1), coeff i f * ker g i n := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc _ = ∑ i ∈ range (n+1), coeff i f * ker g i n := by
         apply sum_congr rfl;intro i hi
         rw [ker,if_pos (Nat.le_of_lt_succ (mem_range.mp hi))]
       _ = _ := sum_subset (range_mono (by omega)) (fun i _ hi => by
         have : ¬ i≤n := by simpa using hi
         simp [ker,this])

private lemma kernel_order (f g : ℕ → ℚ) (K : ℕ → ℕ → ℚ)
    (hf : ∀ i j, i≤j → f i*g j ≤ g i*f j)
    (hK : ∀ i j u v, i≤j → u≤v → K i v*K j u ≤ K i u*K j v)
    (S : Finset ℕ) (u v : ℕ) (hu : u≤v) :
    (∑ i ∈ S, f i*K i u)*(∑ i ∈ S, g i*K i v) ≤
      (∑ i ∈ S, g i*K i u)*(∑ i ∈ S, f i*K i v) := by
  let T (i j : ℕ) := (g i*f j-f i*g j)*(K i u*K j v-K i v*K j u)
  have hp (i j : ℕ) : 0≤T i j := by
    rcases le_total i j with hij|hji
    · exact mul_nonneg (sub_nonneg.mpr (hf _ _ hij)) (sub_nonneg.mpr (hK _ _ _ _ hij hu))
    · apply mul_nonneg_of_nonpos_of_nonpos
      · exact sub_nonpos.mpr (by simpa only [mul_comm] using hf _ _ hji)
      · exact sub_nonpos.mpr (by simpa only [mul_comm] using hK _ _ _ _ hji hu)
  have hn := sum_nonneg (s := S) (fun i _ => sum_nonneg (s := S) (fun j _ => hp i j))
  have hsum : (∑ i ∈ S, ∑ j ∈ S, T i j)=
      2*((∑ i ∈ S, g i*K i u)*(∑ i ∈ S, f i*K i v)-
         (∑ i ∈ S, f i*K i u)*(∑ i ∈ S, g i*K i v)) := by
    calc _ = ∑ i ∈ S, ∑ j ∈ S,
        ((g i*K i u)*(f j*K j v)-(g i*K i v)*(f j*K j u)-
         (f i*K i u)*(g j*K j v)+(f i*K i v)*(g j*K j u)) := by
          apply sum_congr rfl;intro i _
          apply sum_congr rfl;intro j _;dsimp [T];ring
         _ = _ := by
            simp only [sum_add_distrib,sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul]
            ring
  rw [hsum] at hn;linarith

lemma lr_mul_right {f g k : PowerSeries ℚ} (h : LR f g) (ht : TP k) :
    LR (f*k) (g*k) := by
  intro i j hij
  rw [coeff_padded f k i j hij,coeff_padded g k j j le_rfl,coeff_padded g k i j hij,
    coeff_padded f k j j le_rfl]
  exact kernel_order _ _ _ h ht _ _ _ hij

lemma factorial_cross (a b d : ℕ) (hab : a≤b) :
    (a+d).factorial*b.factorial ≤ a.factorial*(b+d).factorial := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ,Nat.add_succ,Nat.factorial_succ,Nat.factorial_succ (b+d)]
    calc _ = (a+d+1)*((a+d).factorial*b.factorial) := by ring
         _ ≤ (b+d+1)*(a.factorial*(b+d).factorial) := Nat.mul_le_mul (by omega) ih
         _ = _ := by ring

lemma tp_blocks (s : ℕ) : TP (blocks s) := by
  have hk (i j : ℕ) : ker (blocks s) i j =
      if i+s ≤ j then ((j-i).factorial:ℚ)⁻¹ else 0 := by
    simp only [ker,blocks,coeff_mk]
    split_ifs <;> first | rfl | omega
  intro i j u v hij huv
  simp only [hk]
  by_cases hju : j+s ≤ u
  · have hiu : i+s ≤ u := by omega
    have hiv : i+s ≤ v := by omega
    have hjv : j+s ≤ v := by omega
    simp only [if_pos hju,if_pos hiu,if_pos hiv,if_pos hjv]
    rw [← mul_inv,← mul_inv]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    have h := factorial_cross (u-j) (v-j) (j-i) (by omega)
    rw [show u-j+(j-i)=u-i by omega,show v-j+(j-i)=v-i by omega] at h
    exact_mod_cast h.trans_eq (Nat.mul_comm _ _)
  · rw [if_neg hju,mul_zero];split_ifs <;> positivity

end
end OMA.S_mo_459462

namespace OMA.S_mo_459462
open PowerSeries Finset
noncomputable section

lemma lr_base : LR (blocks 2) (blocks 1) := by
  intro i j hij
  simp only [blocks,coeff_mk]
  split_ifs <;> simp_all <;> first | positivity | omega

lemma coeff_blocks_le (j : ℕ) : coeff j (blocks 2) ≤ coeff j (blocks 1) := by
  simp only [blocks,coeff_mk]
  split_ifs <;> first | positivity | exact le_rfl | omega

lemma coeff_mul_le {f g f' g' : PowerSeries ℚ} (hf : NN f) (hg : NN g) (_hg' : NN g')
    (hf₁ : ∀ j, coeff j f ≤ coeff j f') (hg₁ : ∀ j, coeff j g ≤ coeff j g') (n : ℕ) :
    coeff n (f*g) ≤ coeff n (f'*g') := by
  rw [coeff_mul,coeff_mul]
  refine sum_le_sum fun x _ => ?_
  exact mul_le_mul (hf₁ _) (hg₁ _) (hg _) ((hf _).trans (hf₁ _))

lemma coeff_power_le (k j : ℕ) : coeff j ((blocks 2)^k) ≤ coeff j ((blocks 1)^k) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,pow_succ]
    exact coeff_mul_le (nn_pow (nn_blocks _) _) (nn_blocks _) (nn_blocks _) ih coeff_blocks_le _

lemma lr_trans {f g h : PowerSeries ℚ} (hf : NN f) (hg : NN g) (hh : NN h)
    (hfg : LR f g) (hgh : LR g h) (hle : ∀ i, coeff i f ≤ coeff i g) : LR f h := by
  intro i j hij
  have a := hfg i j hij
  have b := hgh i j hij
  by_cases hz : coeff j g=0
  · rw [hz, mul_zero] at b
    have hzero := (b.antisymm (mul_nonneg (hg i) (hh j))).trans rfl
    rcases mul_eq_zero.mp hzero with hi|hj
    · have hf0 := (hle i).trans_eq hi
      nlinarith [mul_nonneg (hh i) (hf j),mul_nonpos_of_nonpos_of_nonneg hf0 (hh j)]
    · rw [hj,mul_zero];exact mul_nonneg (hh _) (hf _)
  · have hp : 0<coeff j g := lt_of_le_of_ne (hg _) (Ne.symm hz)
    apply (le_of_mul_le_mul_right _ hp)
    nlinarith only [mul_le_mul_of_nonneg_right a (hh j),mul_le_mul_of_nonneg_left b (hf j)]

lemma lr_with_ordinary (k : ℕ) : LR ((blocks 2)*(blocks 1)^k) ((blocks 1)*(blocks 1)^k) := by
  induction k with
  | zero => simpa using lr_base
  | succ k ih => simpa only [pow_succ,← mul_assoc] using lr_mul_right ih (tp_blocks 1)

lemma lr_powers (k : ℕ) : LR ((blocks 2)^k) ((blocks 1)^k) := by
  induction k with
  | zero => intro i j _;simp
  | succ k ih =>
    rw [pow_succ,pow_succ]
    have hmid : LR ((blocks 1)^k*blocks 2) ((blocks 1)^k*blocks 1) := by
      simpa only [mul_comm] using lr_with_ordinary k
    exact lr_trans (nn_mul (nn_pow (nn_blocks _) _) (nn_blocks _))
      (nn_mul (nn_pow (nn_blocks _) _) (nn_blocks _)) (nn_mul (nn_pow (nn_blocks _) _) (nn_blocks _))
      (lr_mul_right ih (tp_blocks 2)) hmid
      (coeff_mul_le (nn_pow (nn_blocks _) _) (nn_blocks _) (nn_blocks _) (coeff_power_le k) (fun _ => le_rfl))

lemma coeff_vanish (s k n : ℕ) (h : n<s*k) : coeff n ((blocks s)^k)=0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [pow_succ,coeff_mul]
    apply sum_eq_zero
    intro x hx
    have e := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    by_cases h₁ : x.1<s*k
    · rw [ih _ h₁,zero_mul]
    · have h₂ : ¬ s≤x.2 := by rw [Nat.mul_succ] at h;omega
      simp [blocks,h₂]

lemma coeff_positive (s k n : ℕ) (hk : 0 < k) (h : s*k≤n) : 0<coeff n ((blocks s)^k) := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simpa [blocks,show s≤n by simpa using h] using (show 0<(n.factorial:ℚ)⁻¹ by positivity)
    | succ k =>
      rw [pow_succ,coeff_mul]
      refine sum_pos' (fun x _ => mul_nonneg (nn_pow (nn_blocks _) _ _) (nn_blocks _ _)) ?_
      refine ⟨(n-s,s),Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.sub_add_cancel (by rw [Nat.mul_succ] at h;omega)),?_⟩
      apply mul_pos (ih _ (by omega) (by rw [Nat.mul_succ] at h;omega))
      simp [blocks, Nat.factorial_pos]

end
end OMA.S_mo_459462

namespace OMA.S_mo_459462
open PowerSeries
noncomputable section
private lemma derivative_blocks : derivative ℚ (blocks 1) = 1+blocks 1 := by
  have e : blocks 1 = exp ℚ-1 := by
    ext n
    cases n <;> simp [blocks,coeff_one,one_div]
  rw [e,map_sub,derivative_exp,derivative_one]
  ring

private lemma associated_step (n k : ℕ) :
    associated 1 (n+1) (k+1)=((k:ℚ)+1)*associated 1 n (k+1)+associated 1 n k := by
  have e : derivative ℚ ((blocks 1)^(k+1)) = (k+1) • ((blocks 1)^k+(blocks 1)^(k+1)) := by
    rw [Derivation.leibniz_pow,derivative_blocks]
    simp only [Nat.add_sub_cancel,smul_eq_mul,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    ring
  have h := congrArg (coeff (R:=ℚ) n) e
  rw [coeff_derivative,map_nsmul,map_add,nsmul_eq_mul,Nat.cast_add_one] at h
  simp only [associated,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one]
  field_simp
  linear_combination h

lemma ordinary (n k : ℕ) : associated 1 n k=(Nat.stirlingSecond n k:ℚ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [associated]
    | succ k => simp [associated,coeff_vanish 1 (k+1) 0 (by omega)]
  | succ n ih =>
    cases k with
    | zero => simp [associated,coeff_one]
    | succ k =>
      rw [associated_step,ih,ih,Nat.stirlingSecond_succ_succ]
      push_cast
      ring
end
end OMA.S_mo_459462

namespace OMA.S_mo_459462
open PowerSeries Finset
noncomputable section

lemma normalized_ratio (n k : ℕ) :
    ratio n k = coeff n ((blocks 2)^k)/coeff n ((blocks 1)^k) := by
  rw [ratio,← ordinary n k]
  exact mul_div_mul_left _ _ (show (n.factorial:ℚ)/(k.factorial:ℚ)≠0 by positivity)

private lemma next_coeff (s n k : ℕ) : coeff n ((blocks s)^(k+1)) =
    ∑ j ∈ range (n+1), coeff j (blocks s)*coeff (n-j) ((blocks s)^k) := by
  rw [pow_succ',coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma ratio_strict (n k : ℕ) (hk : 0<k) (hkn : k<n) (ht : 2*k≤n) :
    ratio n (k+1)<ratio n k := by
  rw [normalized_ratio,normalized_ratio]
  apply (div_lt_div_iff₀ (coeff_positive 1 (k+1) n (by omega) (by omega))
    (coeff_positive 1 k n hk (by omega))).mpr
  rw [next_coeff 2 n k,next_coeff 1 n k,mul_comm (coeff n ((blocks 2)^k)),
      Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_lt_sum
  · intro j _
    calc _ = coeff j (blocks 2) * (coeff (n-j) ((blocks 2)^k)*coeff n ((blocks 1)^k)) := by ring
         _ ≤ coeff j (blocks 1) * (coeff (n-j) ((blocks 1)^k)*coeff n ((blocks 2)^k)) :=
           mul_le_mul (coeff_blocks_le j) (lr_powers k (n-j) n (Nat.sub_le _ _))
             (mul_nonneg (nn_pow (nn_blocks _) _ _) (nn_pow (nn_blocks _) _ _)) (nn_blocks _ _)
         _ = _ := by ring
  · refine ⟨1,mem_range.mpr (by omega),?_⟩
    have a := coeff_positive 1 k (n-1) hk (by omega)
    have b := coeff_positive 2 k n hk ht
    have a1 : coeff 1 (blocks 1)=1 := by norm_num [blocks]
    have a2 : coeff 1 (blocks 2)=0 := by norm_num [blocks]
    rw [a1,a2,zero_mul,zero_mul,one_mul]
    exact mul_pos a b

theorem solution : (∀ n k : ℕ, associated 1 n k=(Nat.stirlingSecond n k:ℚ)) ∧
    ∀ n k : ℕ, 2 ≤ n → 0 < k → k < n →
      (ratio n (k+1) ≤ ratio n k ∧ (ratio n (k+1) < ratio n k ↔ 2*k ≤ n) ∧
       (n < 2*k → ratio n k=0)) := by
  refine ⟨ordinary,?_⟩
  intro n k _ hk hkn
  by_cases h : 2*k≤n
  · have hs := ratio_strict n k hk hkn h
    exact ⟨hs.le,iff_of_true hs h,by omega⟩
  · have hz (j : ℕ) (hj : n<2*j) : ratio n j=0 := by
      rw [normalized_ratio,coeff_vanish 2 j n hj,zero_div]
    rw [hz k (by omega),hz (k+1) (by omega)]
    simp [h]

end
end OMA.S_mo_459462

theorem OMA.solution : type_of% @OMA.S_mo_459462.main := OMA.S_mo_459462.solution

