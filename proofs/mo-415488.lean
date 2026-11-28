import OMAStatements.S_mo_415488

/-!
Complete proof by @connoranderson, linked from statement PR #25857 and desk DONE #118432.
Pinned companion: https://github.com/connoranderson/open-math-agents/blob/dcbcb0d2cedfad50529c148173d0b59ba086973d/proofs/mo-415488.lean
All mathematical code is retained unchanged. This port adds attribution and current-checker validation.
Source: BharatRam, https://mathoverflow.net/questions/415488 (CC BY-SA 4.0).
Credit Christian Remling for the deterministic block construction in the source discussion.
The statistical assertion uses uniform coordinate permutations relative to a fixed diagonal basis,
not an unspecified or Haar-random matrix model. Port: @rodolfoquint; no new discovery claimed.
-/

namespace OMA.S_mo_415488
open Matrix Finset
open scoped Matrix.Norms.L2Operator

private lemma fro_trace {n : ℕ} (A : Sq (Fin n)) : froSq A = (A * star A).trace.re := by
  simp only [froSq,Matrix.trace,Matrix.diag,Matrix.mul_apply,star_eq_conjTranspose,
    conjTranspose_apply,Complex.star_def,Complex.mul_conj',Complex.re_sum,←Complex.ofReal_pow,Complex.ofReal_re]

private lemma fro_unitaries {n : ℕ} (U V : unitaryGroup (Fin n) ℂ) (T : Sq (Fin n)) :
    froSq (star (U:Sq (Fin n))*T*(V:Sq (Fin n))) = froSq T := by
  have hU : (U:Sq (Fin n))*star (U:Sq (Fin n)) = 1 := Unitary.coe_mul_star_self U
  have hV : (V:Sq (Fin n))*star (V:Sq (Fin n)) = 1 := Unitary.coe_mul_star_self V
  rw [fro_trace,fro_trace,star_mul,star_mul,star_star]
  have h : (star (U:Sq (Fin n))*T*V)*(star (V:Sq (Fin n))*(star T*U)) =
        star (U:Sq (Fin n))*(T*star T)*U := by
    calc _ = star (U:Sq (Fin n))*T*((V:Sq (Fin n))*star (V:Sq (Fin n)))*star T*U := by simp only [mul_assoc]
      _ = _ := by rw [hV,mul_one];simp only [mul_assoc]
  rw [h,trace_mul_cycle,hU,one_mul]

end OMA.S_mo_415488

namespace OMA.S_mo_415488
open Matrix Finset
open scoped Matrix.Norms.L2Operator

private lemma fro_sub {n : ℕ} (A B : Sq (Fin n)) : froSq (A-B) ≤ 2*(froSq A+froSq B) := by
  have h (i j : Fin n) : ‖A i j - B i j‖ ^ 2 ≤ 2*(‖A i j‖^2+‖B i j‖^2) := by
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (A i j) (B i j)) 2
    nlinarith [sq_nonneg (‖A i j‖ - ‖B i j‖)]
  calc froSq (A-B) ≤ ∑ i, ∑ j, 2*(‖A i j‖^2+‖B i j‖^2) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => h i j))
    _ = _ := by simp only [←mul_sum,sum_add_distrib,froSq]

private lemma unit_left {n : ℕ} (U : unitaryGroup (Fin n) ℂ) (T : Sq (Fin n)) :
    froSq ((U:Sq (Fin n))*T) = froSq T := by simpa using fro_unitaries (star U) 1 T

private lemma unit_right {n : ℕ} (U : unitaryGroup (Fin n) ℂ) (T : Sq (Fin n)) :
    froSq (T*(U:Sq (Fin n))) = froSq T := by simpa using fro_unitaries 1 U T

lemma deterministic (n : ℕ) (U V : unitaryGroup (Fin n) ℂ) :
    froSq (commutator (U:Sq (Fin n)) V) ≤ 4*min (froSq ((U:Sq (Fin n))-1)) (froSq ((V:Sq (Fin n))-1)) := by
  let A : Sq (Fin n) := U
  let B : Sq (Fin n) := V
  have hu : commutator A B = (A-1)*B-B*(A-1) := by simp [commutator,sub_mul,mul_sub]
  have hv : commutator A B = A*(B-1)-(B-1)*A := by simp [commutator,sub_mul,mul_sub]
  have hU := fro_sub ((A-1)*B) (B*(A-1))
  rw [unit_right V,unit_left V,←hu] at hU
  have hV := fro_sub (A*(B-1)) ((B-1)*A)
  rw [unit_left U,unit_right U,←hv] at hV
  change froSq (commutator A B) ≤ 4*min _ _
  rcases le_total (froSq (A-1)) (froSq (B-1)) with h|h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

end OMA.S_mo_415488

namespace OMA.S_mo_415488
open Matrix Finset

private noncomputable def pauliBlocks (k : ℕ) (M : Sq (Fin 2)) (N : Sq (Fin (k*k))) :
    Sq (Axis k) := fromBlocks (blockDiagonal (fun _ : Fin k => M)) 0 0 N

private lemma blocks_mul (k : ℕ) (M M' : Sq (Fin 2)) (N N' : Sq (Fin (k*k))) :
    pauliBlocks k M N * pauliBlocks k M' N' = pauliBlocks k (M*M') (N*N') := by
  simp [pauliBlocks, fromBlocks_multiply, ← blockDiagonal_mul]

private lemma blocks_star (k : ℕ) (M : Sq (Fin 2)) (N : Sq (Fin (k*k))) :
    star (pauliBlocks k M N) = pauliBlocks k (star M) (star N) := by
  simp [pauliBlocks, Matrix.star_eq_conjTranspose, fromBlocks_conjTranspose, blockDiagonal_conjTranspose]

private lemma blocks_one (k : ℕ) : pauliBlocks k 1 1 = 1 := by
  unfold pauliBlocks
  rw [show (fun _ : Fin k => (1 : Sq (Fin 2))) = 1 from rfl, blockDiagonal_one, fromBlocks_one]

private lemma blocks_sub (k : ℕ) (M M' : Sq (Fin 2)) (N N' : Sq (Fin (k*k))) :
    pauliBlocks k M N - pauliBlocks k M' N' = pauliBlocks k (M-M') (N-N') := by
  ext i j
  cases i <;> cases j
  · simp only [pauliBlocks, Matrix.sub_apply, fromBlocks_apply₁₁, blockDiagonal_apply]
    split_ifs <;> simp
  · simp [pauliBlocks]
  · simp [pauliBlocks]
  · simp [pauliBlocks]

private lemma blocks_fro (k : ℕ) (M : Sq (Fin 2)) :
    froSq (pauliBlocks k M 0) = (k:ℝ)*froSq M := by
  simp [pauliBlocks, froSq, Fintype.sum_sum_type, Fintype.sum_prod_type, blockDiagonal_apply,
    apply_ite, ite_pow]
  ring

private def spinZ : Sq (Fin 2) := !![1,0;0,-1]
private def spinX : Sq (Fin 2) := !![0,1;1,0]

private lemma spin_unit (M : Sq (Fin 2)) (hm : M=spinZ ∨ M=spinX) :
    M*star M = 1 := by
  rcases hm with rfl|rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [spinZ,spinX,Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

lemma block_example (k : ℕ) : ∃ A B : unitaryGroup (Axis k) ℂ,
      froSq ((A:Sq (Axis k))-1)=4*(k:ℝ) ∧ froSq ((B:Sq (Axis k))-1)=4*(k:ℝ) ∧
        froSq (commutator (A:Sq (Axis k)) (B:Sq (Axis k)))=8*(k:ℝ) := by
  have hu (M : Sq (Fin 2)) (hm : M=spinZ ∨ M=spinX) :
      pauliBlocks k M 1 ∈ unitaryGroup (Axis k) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, blocks_star, blocks_mul, spin_unit M hm]
    simpa using blocks_one k
  refine ⟨⟨pauliBlocks k spinZ 1, hu _ (Or.inl rfl)⟩,
    ⟨pauliBlocks k spinX 1, hu _ (Or.inr rfl)⟩, ?_⟩
  change froSq (pauliBlocks k spinZ 1-1)=_ ∧ froSq (pauliBlocks k spinX 1-1)=_ ∧
    froSq (pauliBlocks k spinZ 1 * pauliBlocks k spinX 1 -
      pauliBlocks k spinX 1 * pauliBlocks k spinZ 1)=_
  simp only [← blocks_one k, blocks_mul, blocks_sub, one_mul, sub_self, blocks_fro]
  norm_num [froSq, spinZ, spinX, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Complex.norm_ofNat, mul_comm]

end OMA.S_mo_415488

namespace OMA.S_mo_415488
open Finset

private lemma pair_perm {n : ℕ} (i j a b : Fin n) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin n), σ i = a ∧ σ j = b := by
  let τ := Equiv.swap i a
  have ht : τ i = a := Equiv.swap_apply_left _ _
  have hja : a ≠ τ j := ht ▸ τ.injective.ne hij
  refine ⟨τ.trans (Equiv.swap (τ j) b),?_,?_⟩
  · simp only [Equiv.trans_apply,ht,Equiv.swap_apply_of_ne_of_ne hja hab]
  · exact Equiv.swap_apply_left _ _

lemma perm_off (n : ℕ) (hn : 2≤n) (f g : Fin n → Fin n → ℝ) (hf : ∀ i, f i i=0) :
    (∑ σ : Equiv.Perm (Fin n), ∑ i, ∑ j, f i j * g (σ i) (σ j)) /
      (Fintype.card (Equiv.Perm (Fin n)):ℝ) =
    ((∑ i,∑ j, f i j) * (∑ i,∑ j, if i=j then 0 else g i j)) /
      ((n:ℝ)*(n-1)) := by
  classical
  let G (i j : Fin n) := if i=j then 0 else g i j
  let H (i j : Fin n) := ∑ σ : Equiv.Perm (Fin n), G (σ i) (σ j)
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have hab : a ≠ b := fun h => by have := congrArg Fin.val h; contradiction
  let K := H a b
  have hu (i j : Fin n) (h : i ≠ j) : H i j = K := by
    obtain ⟨τ,h₁,h₂⟩ := pair_perm i j a b h hab
    have eq := Equiv.sum_comp (Equiv.mulRight τ) (fun σ : Equiv.Perm (Fin n) => G (σ i) (σ j))
    simpa only [Equiv.coe_mulRight,Equiv.Perm.mul_apply,h₁,h₂,H,K] using eq.symm
  have hz (i : Fin n) : H i i = 0 := by simp [H,G]
  have hrow (i : Fin n) : ∑ j, H i j = ((n:ℝ)-1)*K := by
    calc (∑ j, H i j) = ∑ j, (K - if j=i then K else 0) := by
           apply sum_congr rfl
           intro j _
           by_cases e : i=j
           · subst j; simp [hz]
           · simp [Ne.symm e,hu i j e]
      _ = _ := by simp [sum_sub_distrib]; ring
  have hperm (σ : Equiv.Perm (Fin n)) :
      ∑ i, ∑ j, G (σ i) (σ j) = ∑ i, ∑ j, G i j := by
    simp_rw [Equiv.sum_comp σ (G (σ _))]
    exact Equiv.sum_comp σ (fun i => ∑ j, G i j)
  have rate : (n:ℝ)*(n-1)*K =
      (Fintype.card (Equiv.Perm (Fin n)):ℝ)*(∑ i, ∑ j,G i j) := by
    calc (n:ℝ)*(n-1)*K = ∑ i, ∑ j,H i j := by simp [hrow];ring
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ i, ∑ j,G (σ i) (σ j) := by
        unfold H
        simp_rw [sum_comm (s:=univ (α:=Fin n)) (t:=univ (α:=Equiv.Perm (Fin n)))]
      _ = _ := by simp [hperm]
  have hfg (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
      f i j * g (σ i) (σ j) = f i j * G (σ i) (σ j) := by
    by_cases e : i=j
    · subst j; simp [hf]
    · simp [G,σ.injective.ne e]
  have lhs : (∑ σ : Equiv.Perm (Fin n), ∑ i, ∑ j, f i j * g (σ i) (σ j)) = (∑ i,∑ j,f i j)*K := by
    simp_rw [hfg, sum_comm (s:=univ (α:=Equiv.Perm (Fin n))) (t:=univ (α:=Fin n))]
    simp_rw [←mul_sum]
    change (∑ i,∑ j, f i j * H i j) = _
    simp only [sum_mul]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    by_cases e : i=j
    · subst j; simp [hf]
    · rw [hu i j e]
  change _ = ((∑ i,∑ j, f i j) * (∑ i,∑ j, G i j)) / _
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  rw [lhs,div_eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (mul_ne_zero (by linarith) (by linarith))]
  linear_combination (∑ i,∑ j, f i j)*rate

end OMA.S_mo_415488

namespace OMA.S_mo_415488
open Finset Matrix
open scoped InnerProductSpace

private lemma energy {n : ℕ} (a : Fin n → ℂ) :
    (∑ i,∑ j, ‖a i-a j‖^2) ≤ 2*(n:ℝ)*froSq (diagonal a-1) := by
  let b (i : Fin n) := a i - 1
  have hdiag : froSq (diagonal a-1)=∑ i, ‖b i‖^2 := by
    have he (i j : Fin n) : ‖(diagonal a-1) i j‖^2 = if j=i then ‖b i‖^2 else 0 := by
      by_cases h : j=i
      · subst j; simp [b]
      · simp [Matrix.sub_apply,h,Ne.symm h]
    unfold froSq
    simp_rw [he]
    simp
  have hdiff (i j : Fin n) : a i-a j = b i-b j := by dsimp [b]; ring
  rw [hdiag]
  simp_rw [hdiff,norm_sub_sq_real]
  simp only [sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    ←mul_sum,←inner_sum,←sum_inner,real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖∑ i,b i‖]

lemma statistical (n : ℕ) (hn : 2≤n) (a : Fin n → ℂ) (B : Sq (Fin n)) :
    meanComm a B =
      (∑ i,∑ j, ‖a i-a j‖^2) * (∑ i,∑ j, if i=j then 0 else ‖B i j‖^2) /
        ((n:ℝ)*(n-1)) ∧
    meanComm a B ≤ 2/((n:ℝ)-1) * froSq (diagonal a-1) * froSq (B-1) := by
  have hcomm (σ : Equiv.Perm (Fin n)) (i j : Fin n) : (commutator (diagonal a) (B.submatrix σ σ)) i j =
      (a i - a j)*B (σ i) (σ j) := by
    simp [commutator,diagonal_mul,mul_diagonal,sub_mul,mul_comm]
  have havg := perm_off n hn (fun i j => ‖a i-a j‖^2) (fun i j => ‖B i j‖^2) (by simp)
  have heq : meanComm a B =
      (∑ i,∑ j, ‖a i-a j‖^2) * (∑ i,∑ j, if i=j then 0 else ‖B i j‖^2) /
        ((n:ℝ)*(n-1)) := by
    simpa only [meanComm,froSq,hcomm,norm_mul,mul_pow] using havg
  refine ⟨heq,?_⟩
  have hoff : (∑ i,∑ j, if i=j then 0 else ‖B i j‖^2) ≤ froSq (B-1) := by
    apply sum_le_sum; intro i _
    apply sum_le_sum; intro j _
    by_cases h : i=j
    · simp [h]
    · simp [h,Matrix.sub_apply]
  have hN : 0 < (n:ℝ)-1 := by
    apply sub_pos.mpr
    exact_mod_cast (show 1<n by omega)
  have hn' : (0:ℝ) < n := by linarith
  rw [heq]
  calc _ ≤ (2*(n:ℝ)*froSq (diagonal a-1)) * froSq (B-1) / ((n:ℝ)*(n-1)) := by
         apply div_le_div_of_nonneg_right _ (mul_nonneg hn'.le hN.le)
         apply mul_le_mul (energy a) hoff
         · apply sum_nonneg; intro i _; apply sum_nonneg; intro j _; split_ifs <;> positivity
         · unfold froSq; positivity
    _ = _ := by field_simp

end OMA.S_mo_415488

open OMA.S_mo_415488

theorem OMA.solution : type_of% @OMA.S_mo_415488.main :=
  ⟨deterministic,block_example,statistical⟩
