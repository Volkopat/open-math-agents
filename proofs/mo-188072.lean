import OMAStatements.S_mo_188072

namespace OMA.S_mo_188072
open Finset Matrix
private lemma inv_mono {n} {P : Mat n} (hP : P ∈ rowStochastic ℝ (Fin n))
    {ε : ℝ} (hε : 0 < ε) (he : ε ≤ 1) (f : Fin n → ℝ)
    (h : 0 ≤ (1-(1-ε) • P) *ᵥ f) : 0 ≤ f := by
  intro j
  let : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨i,_,hi⟩ := univ.exists_min_image f univ_nonempty
  have hw : f i ≤ (P *ᵥ f) i := by
    calc f i = ∑ k,P i k*f i := by rw [←sum_mul,sum_row_of_mem_rowStochastic hP,one_mul]
         _ ≤ _ := sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hi k (mem_univ _)) (nonneg_of_mem_rowStochastic hP))
  have hz := h i
  simp only [sub_mulVec,one_mulVec,smul_mulVec,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Pi.zero_apply] at hz
  have hn := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr he)
  exact (nonneg_of_mul_nonneg_left (by linarith : 0 ≤ f i*ε) hε).trans (hi j (mem_univ _))
lemma optimum {n : ℕ} (P : Mat n) (π : Fin n → ℝ) (ε C : ℝ) (hP : P ∈ rowStochastic ℝ (Fin n))
    (hε : 0 < ε) (he : ε ≤ 1) : ((∀ u, admissible P ε u → ∀ j,C*π j ≤ u j) ↔
      ∀ i j,C*π j ≤ resolvent P ε i j) := by
  let M : Mat n := 1-(1-ε) • P
  let R := resolvent P ε
  have hd : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    obtain ⟨f,hf,heq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    apply hf
    have h₁ := inv_mono hP hε he f (heq.ge)
    have h₂ := inv_mono hP hε he (-f) (show 0 ≤ M *ᵥ (-f) by rw [Matrix.mulVec_neg,heq,neg_zero])
    exact le_antisymm (neg_nonneg.mp h₂) h₁
  have hrm : R*M=ε • (1:Mat n) := by
    change (ε • M⁻¹)*M=_
    rw [smul_mul_assoc,nonsing_inv_mul _ hd]
  have hnn (i j : Fin n) : 0 ≤ R i j := by
    have hv : M *ᵥ (fun k => M⁻¹ k j) = fun k => (1:Mat n) k j := by
      funext a
      exact congrArg (fun T : Mat n => T a j) (M.mul_nonsing_inv hd)
    have hp : 0 ≤ M *ᵥ (fun k => M⁻¹ k j) := by rw [hv]; intro k; simp [Matrix.one_apply]; positivity
    exact mul_nonneg hε.le (inv_mono hP hε he _ hp i)
  have hOne : M *ᵥ 1=ε • (1:Fin n → ℝ) := by
    ext i
    simp [M,sub_mulVec,smul_mulVec,one_vecMul_of_mem_rowStochastic hP]
  have hR : R ∈ rowStochastic ℝ (Fin n) := by
    refine mem_rowStochastic.mpr ⟨hnn,?_⟩
    have h := congrArg (fun T : Mat n => T *ᵥ 1) hrm
    change (R*M) *ᵥ 1=(ε • (1:Mat n)) *ᵥ 1 at h
    rw [←mulVec_mulVec,hOne,mulVec_smul,smul_mulVec,one_mulVec] at h
    ext i
    exact (mul_left_cancel₀ hε.ne' (congrFun h i))
  constructor
  · intro H i j
    apply H (R i) _ j
    refine ⟨⟨hnn i,sum_row_of_mem_rowStochastic hR i⟩,fun k => ?_⟩
    have h := congrArg (fun T : Mat n => T i k) hrm
    change ((R i) ᵥ* M) k=(ε • (1:Mat n)) i k at h
    simp only [M,vecMul_sub,vecMul_one,vecMul_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      Matrix.smul_apply] at h
    have h01 : 0 ≤ (1:Mat n) i k := by simp [Matrix.one_apply]; positivity
    linarith [mul_nonneg hε.le h01]
  · intro H u hu j
    let v : Fin n → ℝ := ε⁻¹ • (u ᵥ* M)
    have hv i : 0 ≤ v i := by
      change 0 ≤ ε⁻¹*((u ᵥ* M) i)
      simp only [M,vecMul_sub,vecMul_one,vecMul_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr hε.le) (sub_nonneg.mpr (hu.2 i))
    have hu' : v ᵥ* R=u := by
      change (ε⁻¹ • (u ᵥ* M)) ᵥ* (ε • M⁻¹)=u
      rw [smul_vecMul,vecMul_smul,vecMul_vecMul,M.mul_nonsing_inv hd,vecMul_one,←mul_smul,
        inv_mul_cancel₀ hε.ne',one_smul]
    have hvs : ∑ i,v i=1 := by
      rw [←hu.1.2,←hu']
      simp only [vecMul,dotProduct,sum_comm (f := fun j i => v i*R i j),←mul_sum,
        sum_row_of_mem_rowStochastic hR,mul_one]
    calc C*π j = ∑ i,v i*(C*π j) := by rw [←sum_mul,hvs,one_mul]
         _ ≤ (v ᵥ* R) j := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (H i j) (hv i))
         _ = _ := congrFun hu' j
end OMA.S_mo_188072
namespace OMA.S_mo_188072
open Matrix Finset
private lemma rev_pow {n} {P : Mat n} {π} (h : reversible P π) (t) (i j : Fin n) :
    π i*(P^t) i j=π j*(P^t) j i := by
  have hu : SemiconjBy (diagonal π) P P.transpose := by
    ext x y
    simp [diagonal_mul,mul_diagonal,h.2.2.2 x y,mul_comm]
  have hr := congrArg (fun M : Mat n => M i j) (hu.pow_right t).eq
  simpa [diagonal_mul,mul_diagonal,←transpose_pow,mul_comm] using hr
private lemma scalar_overlap (p a b : ℝ) (hp : 0<p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    p-max (p-a) 0-max (p-b) 0 ≤ a*b/p := by
  apply (le_div_iff₀ hp).mpr
  rcases le_total p a with h|h <;> rcases le_total p b with h'|h'
  · rw [max_eq_right (by linarith),max_eq_right (by linarith)]
    nlinarith [mul_le_mul h h' hp.le ha]
  · rw [max_eq_right (by linarith),max_eq_left (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hb]
  · rw [max_eq_left (by linarith),max_eq_right (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h') ha]
  · rw [max_eq_left (by linarith),max_eq_left (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr h')]
private lemma mixed_minor {n} {P : Mat n} {π} (h : reversible P π) {t}
    (hm : mixed P π t) (i j : Fin n) : π j/2 ≤ (P^(2*t)) i j := by
  let Q := P^t
  have hQ : Q ∈ rowStochastic ℝ (Fin n) := (rowStochastic ℝ (Fin n)).pow_mem h.1 _
  have hh (k : Fin n) := scalar_overlap (π k) (Q i k) (Q j k) (h.2.2.1 _)
    (nonneg_of_mem_rowStochastic hQ) (nonneg_of_mem_rowStochastic hQ)
  have hs := sum_le_sum (s := univ) (fun k _ => hh k)
  simp only [sum_sub_distrib,h.2.1.2] at hs
  have hi := hm i
  have hj := hm j
  change (∑ k,max (π k-Q i k) 0) ≤ _ at hi
  change (∑ k,max (π k-Q j k) 0) ≤ _ at hj
  have hhalf : (1/2:ℝ) ≤ ∑ k,Q i k*Q j k/π k := by linarith
  rw [two_mul,pow_add]
  change π j/2 ≤ (Q*Q) i j
  calc π j/2 ≤ (∑ k,Q i k*Q j k/π k)*π j := by
         nlinarith [mul_le_mul_of_nonneg_right hhalf (h.2.2.1 j).le]
       _ = _ := by
         rw [sum_mul,Matrix.mul_apply]
         apply sum_congr rfl
         intro k _
         have hd : π k*Q k j=π j*Q j k := rev_pow h t k j
         field_simp [(h.2.2.1 k).ne']
         linear_combination -(Q i k)*hd
lemma mixing_bound {n} (P : Mat n) (π u : Fin n → ℝ) (t : ℕ) (ε : ℝ)
    (hp : reversible P π) (hu : admissible P ε u) (_hε : 0 ≤ ε) (he : ε ≤ 1)
    (hm : mixed P π t) (j : Fin n) : (1-ε)^(2*t)*π j/2 ≤ u j := by
  have hb : 0 ≤ 1-ε := sub_nonneg.mpr he
  have hi (k : ℕ) (l : Fin n) : (1-ε)^k*(u ᵥ* (P^k)) l ≤ u l := by
    induction k generalizing l with
    | zero => simp
    | succ k ih =>
      rw [pow_succ P,←Matrix.vecMul_vecMul,pow_succ]
      calc _ = (1-ε)*(∑ i, ((1-ε)^k*(u ᵥ* P^k) i)*P i l) := by
                 simp [vecMul,dotProduct,mul_sum,mul_assoc,mul_left_comm,mul_comm]
           _ ≤ (1-ε)*(u ᵥ* P) l := by
                 apply mul_le_mul_of_nonneg_left _ hb
                 exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (ih i) (nonneg_of_mem_rowStochastic hp.1))
           _ ≤ _ := hu.2 _
  have hc := sum_le_sum (s := univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (mixed_minor hp hm i j) (hu.1.1 i))
  rw [←sum_mul,hu.1.2,one_mul] at hc
  calc _ = (1-ε)^(2*t)*(π j/2) := by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hc (pow_nonneg hb (2*t))).trans (hi (2*t) j)
end OMA.S_mo_188072
namespace OMA.S_mo_188072
open Matrix Finset
private def up {N : ℕ} (i : Fin (N+1)) : Fin (N+1) := ⟨min (i.val+1) N,by omega⟩
private def dn {N : ℕ} (i : Fin (N+1)) : Fin (N+1) := ⟨i.val-1,by omega⟩
private noncomputable def K (N : ℕ) : Mat (N+1) := fun i j =>
  (if i=j then 22/32 else 0) + (if up i=j then 1/32 else 0) + (if dn i=j then 9/32 else 0)
private lemma K_nonneg (N) (i j : Fin (N+1)) : 0 ≤ K N i j := by
  unfold K
  positivity
private lemma K_sum (N) (i : Fin (N+1)) : ∑ j,K N i j=1 := by
  simp [K,sum_add_distrib]
  norm_num
private lemma K_apply (N) (f : Fin (N+1) → ℝ) (i) :
    (K N *ᵥ f) i = (22*f i + f (up i) + 9*f (dn i))/32 := by
  simp [K,mulVec,dotProduct,add_mul,sum_add_distrib,ite_mul]
  ring
private noncomputable def rat (N : ℕ) (i : Fin (N+1)) : ℝ := (1/9:ℝ)^i.val
private lemma bal_raw {N} (i j : Fin (N+1)) : rat N i*K N i j=rat N j*K N j i := by
  by_cases hij : i=j
  · subst j; rfl
  have step {x y : Fin (N+1)} (h : x ≠ y) : (up x=y ↔ x.val+1=y.val) ∧ (dn x=y ↔ y.val+1=x.val) := by
    have hne : x.val ≠ y.val := fun hh => h (Fin.ext hh)
    simp only [up,dn,Fin.ext_iff]
    omega
  simp only [K,if_neg hij,if_neg (Ne.symm hij),zero_add,
    (step hij).1,(step hij).2,(step (Ne.symm hij)).1,(step (Ne.symm hij)).2]
  rcases lt_trichotomy (i.val+1) j.val with h|h|h
  · simp only [if_neg (by omega : i.val+1 ≠ j.val),if_neg (by omega : j.val+1 ≠ i.val)]
    ring
  · simp only [if_pos h,if_neg (by omega : j.val+1 ≠ i.val),add_zero,zero_add,rat]
    rw [← h,pow_succ]; ring
  · by_cases h' : j.val+1=i.val
    · simp only [if_pos h',if_neg (by omega : i.val+1 ≠ j.val),add_zero,zero_add,rat]
      rw [← h',pow_succ]; ring
    · simp [h',show i.val+1 ≠ j.val by omega]
private noncomputable def normLaw {N : ℕ} (a : Fin (N+1) → ℝ) (i) := a i/(∑ j,a j)
private lemma sum_pos {N : ℕ} {a : Fin (N+1) → ℝ} (ha : ∀ i,0<a i) : 0<∑ i,a i :=
  Finset.sum_pos (fun i _ => ha i) univ_nonempty
private lemma normProb {N : ℕ} {a : Fin (N+1) → ℝ} (ha : ∀ i,0<a i) : prob (normLaw a) :=
  ⟨fun i => div_nonneg (ha i).le (sum_pos ha).le, by
    simp only [normLaw,←sum_div,div_self (sum_pos ha).ne']⟩
private lemma reversible_K (N : ℕ) : reversible (K N) (normLaw (rat N)) := by
  have hr i : 0<rat N i := by unfold rat; positivity
  refine ⟨mem_rowStochastic_iff_sum.mpr ⟨K_nonneg _,K_sum _⟩,normProb hr,
    fun i => div_pos (hr i) (sum_pos hr),fun i j => ?_⟩
  unfold normLaw
  rw [div_mul_eq_mul_div,bal_raw,←div_mul_eq_mul_div]
private lemma K_lazy (N) (i : Fin (N+1)) : 1/2 ≤ K N i i := by
  simp only [K,ite_true]
  split <;> split <;> norm_num
private lemma tilted (N : ℕ) {ε : ℝ} (hε : 0 < ε) (he : ε < 1) :
    admissible (K N) ε (normLaw (fun i => rat N i*(1-ε)^i.val)) := by
  let b := 1-ε
  have hb : 0<b := sub_pos.mpr he
  have hb1 : b<1 := by dsimp [b]; linarith
  let w (i : Fin (N+1)) := rat N i*b^i.val
  have hw i : 0<w i := by dsimp [w,rat]; positivity
  refine ⟨normProb hw,fun j => ?_⟩
  change b*(∑ i,(w i/(∑ k,w k))*K N i j) ≤ w j/(∑ k,w k)
  simp_rw [div_mul_eq_mul_div]
  rw [←sum_div,←mul_div_assoc,div_le_div_iff_of_pos_right (sum_pos hw),mul_sum]
  calc _ ≤ ∑ i,w j*K N j i := by
         apply sum_le_sum
         intro i _
         by_cases hk : K N i j=0
         · rw [hk,mul_zero,mul_zero]
           exact mul_nonneg (hw j).le (K_nonneg _ _ _)
         have hij : j.val ≤ i.val+1 := by
           by_contra! h
           have h₁ : i ≠ j := fun h' => by subst j; omega
           have h₂ : up i ≠ j := fun h' => by have := congrArg Fin.val h'; dsimp [up] at this; omega
           have h₃ : dn i ≠ j := fun h' => by have := congrArg Fin.val h'; dsimp [dn] at this; omega
           exact hk (by simp [K,h₁,h₂,h₃])
         have hpow := pow_le_pow_of_le_one hb.le hb1.le hij
         have hfactor : 0 ≤ rat N j*K N j i := mul_nonneg (by unfold rat; positivity) (K_nonneg _ _ _)
         calc b*(w i*K N i j) = (rat N i*K N i j)*b^(i.val+1) := by simp [w,pow_succ]; ring
              _ = (rat N j*K N j i)*b^(i.val+1) := by rw [bal_raw]
              _ ≤ (rat N j*K N j i)*b^j.val := mul_le_mul_of_nonneg_left hpow hfactor
              _ = _ := by dsimp [w]; ring
       _ = _ := by rw [←mul_sum,K_sum,mul_one]
end OMA.S_mo_188072
namespace OMA.S_mo_188072
open Matrix Finset
private lemma path_gap {N : ℕ} (hN : 0<N) : gap (K N) (1/8) := by
  intro θ f hf he
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let d (i : Fin N) := f i.succ-f i.castSucc
  let w (i : Fin N) := |d i|/(3:ℝ)^i.val
  obtain ⟨k,_,hmax⟩ := univ.exists_max_image w univ_nonempty
  have hle (i : Fin N) : |d i| ≤ w k*3^i.val :=
    (div_le_iff₀ (by positivity : (0:ℝ)<3^i.val)).mp (hmax i (mem_univ _))
  have hw : 0<w k := by
    by_contra! h
    have hz (i : Fin N) : d i=0 := by
      apply abs_eq_zero.mp
      apply le_antisymm _ (abs_nonneg _)
      exact (hle i).trans (mul_nonpos_of_nonpos_of_nonneg h (by positivity))
    have heq (i : Fin (N+1)) : f i=f 0 := by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => exact (sub_eq_zero.mp (hz i)).trans ih
    obtain ⟨i,j,hij⟩ := hf
    exact hij ((heq i).trans (heq j).symm)
  have hk : |d k|=w k*3^k.val := (div_mul_cancel₀ _ (by positivity : (3:ℝ)^k.val ≠ 0)).symm
  have hp : 0 < |d k| := by rw [hk]; positivity
  have hU : |f (up k.succ)-f (up k.castSucc)| ≤ 3*|d k| := by
    by_cases hnext : k.val+1<N
    · let a : Fin N := ⟨k.val+1,hnext⟩
      have hu₁ : up k.succ=a.succ := by ext; simp [up,a]; omega
      have hu₂ : up k.castSucc=a.castSucc := by ext; simp [up,a]
      rw [hu₁,hu₂,hk]
      calc |d a| ≤ w k*3^a.val := hle a
           _ = _ := by simp [a,pow_succ]; ring
    · have hu : up k.succ=up k.castSucc := by ext; simp [up]; omega
      rw [hu,sub_self,abs_zero]
      positivity
  have hD : |f (dn k.succ)-f (dn k.castSucc)| ≤ |d k|/3 := by
    by_cases hprev : 0<k.val
    · let a : Fin N := ⟨k.val-1,by omega⟩
      have hu₁ : dn k.succ=a.succ := by ext; simp [dn,a]; omega
      have hu₂ : dn k.castSucc=a.castSucc := by ext; simp [dn,a]
      have hh : k.val=a.val+1 := by dsimp [a]; omega
      rw [hu₁,hu₂,hk,hh,pow_succ]
      calc |d a| ≤ w k*3^a.val := hle a
           _ = _ := by ring
    · have hh : dn k.succ=dn k.castSucc := by ext; simp [dn]; omega
      rw [hh,sub_self,abs_zero]
      positivity
  have h₁ := congrFun he k.succ
  have h₂ := congrFun he k.castSucc
  rw [K_apply] at h₁ h₂
  simp only [Pi.smul_apply,smul_eq_mul] at h₁ h₂
  have heq : 32*θ*d k = 22*d k + (f (up k.succ)-f (up k.castSucc)) +
      9*(f (dn k.succ)-f (dn k.castSucc)) := by
    dsimp [d]
    linarith
  have hh : 32 * |θ| * |d k| ≤ 28*|d k| := by
    calc _ = |32*θ*d k| := by simp [abs_mul]
         _ = _ := congrArg abs heq
         _ ≤ |22*d k + (f (up k.succ)-f (up k.castSucc))| +
           |9*(f (dn k.succ)-f (dn k.castSucc))| := abs_add_le _ _
         _ ≤ (|22*d k| + |f (up k.succ)-f (up k.castSucc)|) +
           |9*(f (dn k.succ)-f (dn k.castSucc))| := by gcongr; exact abs_add_le _ _
         _ ≤ _ := by rw [abs_mul,abs_mul]; norm_num; linarith
  have := (mul_le_mul_iff_left₀ hp).mp hh
  linarith
end OMA.S_mo_188072
namespace OMA.S_mo_188072
open Matrix Finset
private lemma escape (ε C : ℝ) (hε : 0<ε) (he : ε<1) (hC : 0<C) :
    ∃ (n : ℕ) (P : Mat n) (π u : Fin n → ℝ), reversible P π ∧
      (∀ i,1/2 ≤ P i i) ∧ gap P (1/8) ∧ admissible P ε u ∧ ∃ j,u j < C*π j := by
  let b := 1-ε
  have hb : 0<b := sub_pos.mpr he
  have hb1 : b<1 := by dsimp [b]; linarith
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (by positivity : 0<C/2) hb1
  let N := k+1
  have hn : 0<N := by omega
  have hh : b^N<C/2 := (pow_le_pow_of_le_one hb.le hb1.le (show k ≤ N by omega)).trans_lt hk
  let w (i : Fin (N+1)) := rat N i*b^i.val
  have hw (i) : 0<w i := by dsimp [w,rat]; positivity
  let j := Fin.last N
  refine ⟨N+1,K N,normLaw (rat N),normLaw w,reversible_K _,K_lazy _,path_gap hn,
    tilted N hε he,j,?_⟩
  have hsum : (∑ i,rat N i) ≤ 2 := by
    change (∑ i : Fin (N+1),(1/9:ℝ)^i.val) ≤ 2
    rw [Fin.sum_univ_eq_sum_range]
    have ha := geom_sum_mul (1/9:ℝ) (N+1)
    have hb' : 0 ≤ (1/9:ℝ)^(N+1) := by positivity
    linarith
  have hnorm : 1 ≤ ∑ i,w i := by
    calc 1 = w 0 := by simp [w,rat]
         _ ≤ _ := single_le_sum (fun i _ => (hw i).le) (mem_univ _)
  have hp : 0<rat N j := by dsimp [rat]; positivity
  have hfull : 0<∑ i,rat N i := sum_pos fun i => by dsimp [rat]; positivity
  change rat N j*b^N/(∑ i,w i) < C*(rat N j/(∑ i,rat N i))
  rw [←mul_div_assoc,div_lt_div_iff₀ (sum_pos hw) hfull]
  calc rat N j*b^N*(∑ i,rat N i) ≤ rat N j*b^N*2 :=
         mul_le_mul_of_nonneg_left hsum (mul_nonneg hp.le (pow_nonneg hb.le _))
       _ < C*rat N j := by nlinarith [mul_lt_mul_of_pos_left hh hp]
       _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hC.le hp.le) hnorm
end OMA.S_mo_188072
theorem OMA.solution : type_of% @OMA.S_mo_188072.main := by
  refine ⟨OMA.S_mo_188072.optimum,?_,OMA.S_mo_188072.escape⟩
  · intro n P π u t ε hp hu hε he hm j
    have h := OMA.S_mo_188072.mixing_bound P π u t ε hp hu hε he hm j
    refine ⟨h,fun ht => ?_⟩
    have hb := one_add_mul_le_pow (by linarith : -2 ≤ -ε) (2*t)
    push_cast at hb
    rw [←sub_eq_add_neg] at hb
    have hf : (4/5:ℝ) ≤ (1-ε)^(2*t) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hf (hp.2.2.1 j).le]
