import OMAStatements.S_mo_491017
import Mathlib
/-!
# Proof of Kurkov's vector algorithm

For pass d, multiply the current polynomial-valued series by its d-th rational
factor. Its coefficient recursion uses the prefix sums of strictly earlier
new entries. Induction on the number of in-place updates identifies the
coordinates with these coefficients and proves stabilization in each degree.
-/
namespace OMA.S_mo_491017
open PowerSeries
noncomputable section

def ones : R⟦X⟧ := mk (fun _ => 1)

lemma ones_cancel : ones * (1-X)=1 := by
  ext k
  rw [mul_sub,mul_one,map_sub]
  cases k with
  | zero => norm_num [ones,coeff_zero_eq_constantCoeff_apply]
  | succ k => simp [ones,coeff_succ_mul_X,coeff_one]

lemma coeff_prefix (P : R⟦X⟧) (n : ℕ) :
    coeff n (P*ones)=∑ k ∈ Finset.range (n+1), coeff k P := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [ones]

lemma pass_equation (P : R⟦X⟧) (d : ℕ) :
    P*factor (d+1)=P + X^(d+1)*(C Polynomial.X*((P*factor (d+1))*ones)) := by
  let denom : R⟦X⟧ := 1-X-C Polynomial.X*X^(d+1)
  have hd : constantCoeff denom = ((1 : Rˣ) : R) := by simp [denom]
  have hi := mul_invOfUnit denom 1 hd
  have h₁ : (P*factor (d+1))*denom = P*(1-X) := by
    change (P*((1-X)*invOfUnit denom 1))*denom=P*(1-X)
    calc _ = (P*(1-X))*(denom * invOfUnit denom 1) := by ring
         _ = _ := by rw [hi,mul_one]
  have h₂ := congrArg (fun p => ones*p) h₁
  dsimp only [denom] at h₂
  linear_combination (norm := ring_nf) h₂ + (P - P*factor (d+1))*ones_cancel

lemma coeff_pass (P : R⟦X⟧) (d j : ℕ) :
    coeff j (P*factor (d+1)) = coeff j P +
      if d+1 ≤ j then Polynomial.X*∑ k ∈ Finset.range (j-(d+1)+1),
        coeff k (P*factor (d+1)) else 0 := by
  conv_lhs => rw [pass_equation]
  simp only [map_add,coeff_X_pow_mul',coeff_C_mul,coeff_prefix]

end
end OMA.S_mo_491017

namespace OMA.S_mo_491017
open PowerSeries
noncomputable section

lemma sweep_correct (P : R⟦X⟧) (v : ℕ → R) (m d : ℕ)
    (hv : ∀ j < m, v j = coeff j P) (t : ℕ) (ht : t ≤ m) (j : ℕ) :
    sweep (d+1) v t j = if j<t then coeff j (P*factor (d+1)) else v j := by
  induction t generalizing j with
  | zero => simp [sweep]
  | succ t ih =>
    have ht' : t ≤ m := by omega
    by_cases hj : j=t
    · subst j
      rw [sweep,Function.update_self,ih ht',if_neg (lt_irrefl _),if_pos (Nat.lt_succ_self t),hv _ (by omega)]
      conv_rhs => rw [coeff_pass]
      by_cases hd : d+1 ≤ t
      · simp only [if_pos hd,add_right_inj]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [ih ht',if_pos (by omega)]
      · simp [hd]
    · rw [sweep,Function.update_of_ne hj,ih ht']
      by_cases h : j<t <;> simp [h,show (j<t+1) ↔ j<t by omega]

def initialProduct (d : ℕ) : R⟦X⟧ := ∏ i ∈ Finset.range d, factor (i+1)

lemma vector_correct (m d : ℕ) : ∀ j < m, vector m d j = coeff j (initialProduct d) := by
  induction d with
  | zero => intro j _;simp [vector,initialProduct,coeff_one]
  | succ d ih =>
    intro j hj
    rw [vector,sweep_correct (initialProduct d) _ m d ih m le_rfl j,if_pos hj]
    simp [initialProduct,Finset.prod_range_succ]

lemma partial_stable (j N : ℕ) (h : j ≤ N) : coeff j (initialProduct N)=coeff j (initialProduct j) := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N h ih =>
    have hp : initialProduct (N+1)=initialProduct N*factor (N+1) := Finset.prod_range_succ _ _
    rw [hp,coeff_pass,if_neg (by omega),add_zero,ih]

lemma solution_all (m j N : ℕ) (hj : j < m) (hN : j ≤ N) :
    vector m (m-1) j = coeff j (∏ i ∈ Finset.range N, factor (i+1)) :=
  (vector_correct m _ j hj).trans ((partial_stable j _ (by omega)).trans (partial_stable j N hN).symm)

end
end OMA.S_mo_491017
theorem OMA.solution : type_of% @OMA.S_mo_491017.main := OMA.S_mo_491017.solution_all
