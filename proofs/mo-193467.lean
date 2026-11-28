import OMAStatements.S_mo_193467

namespace OMA.S_mo_193467
open Matrix Finset

private lemma constant_of_reverse {n : ℕ} (a b : Vec n) (ha : Antitone a) (hb : Antitone b)
    (ht : ∑ i, opposite a b i = ∑ i, aligned a b i) :
    (∀ i j,a i=a j) ∨ (∀ i j,b i=b j) := by
  classical
  let d (i : Fin n) := (a i-a i.rev)*(b i-b i.rev)
  have hd (i : Fin n) : 0≤d i := by
    rcases le_total i i.rev with h|h
    · exact mul_nonneg (sub_nonneg.mpr (ha h)) (sub_nonneg.mpr (hb h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (ha h)) (sub_nonpos.mpr (hb h))
  have h1 := Equiv.sum_comp (@Fin.revPerm n) (fun i => a i * b i)
  have h2 := Equiv.sum_comp (@Fin.revPerm n) (fun i => a i * b i.rev)
  simp only [Fin.revPerm_apply,Fin.rev_rev] at h1 h2
  have hz : ∑ i,d i=0 := by
    change ∑ i, a i*b i.rev = ∑ i,a i*b i at ht
    simp only [d,sub_mul,mul_sub,sum_sub_distrib]
    linarith
  have hi := (sum_eq_zero_iff_of_nonneg (fun i _ => hd i)).mp hz
  cases n with
  | zero => exact Or.inl (fun i => Fin.elim0 i)
  | succ k =>
    have h := hi (0:Fin (k+1)) (mem_univ _)
    change (a 0-a (Fin.rev 0))*(b 0-b (Fin.rev 0))=0 at h
    rw [Fin.rev_zero] at h
    have cst (u : Vec (k+1)) (hu : Antitone u) (hu' : u 0-u (Fin.last k)=0) : ∀ i j,u i=u j := by
      intro i j
      have := hu (Fin.zero_le i)
      have := hu (Fin.le_last i)
      have := hu (Fin.zero_le j)
      have := hu (Fin.le_last j)
      linarith
    exact (mul_eq_zero.mp h).imp (cst a ha) (cst b hb)

lemma strong_case {n : ℕ} (a b c : Vec n) (ha : Antitone a) (hb : Antitone b)
    (_hc : Antitone c) (h : strongBounds a b c) :
    ((∀ i j,a i=a j) ∨ (∀ i j,b i=b j)) ∧ c=aligned a b ∧ realizes a b c := by
  classical
  have hconst := constant_of_reverse a b ha hb (h.2.1.trans h.2.2)
  obtain ⟨π,hπ⟩ : ∃ π : Equiv.Perm (Fin n), ∀ i, opposite a b (π i)=aligned a b i := by
    rcases hconst with h1|h2
    · exact ⟨Fin.revPerm,fun i => by simp [opposite,aligned,h1 i.rev i]⟩
    · exact ⟨Equiv.refl _,fun i => by simp [opposite,aligned,h2 i.rev i]⟩
  have heq (S : Finset (Fin n)) (k : ℕ)
      (hS : S=univ.filter (fun i : Fin n => i.val<k)) (hcard : S.card=k) :
      (∑ i ∈ S,c i) = ∑ i ∈ S,aligned a b i := by
    have hu := h.1.2 k
    have hl := h.1.1 (S.map π.toEmbedding)
    rw [Finset.card_map,hcard,Finset.sum_map] at hl
    simp only [Equiv.toEmbedding_apply,hπ] at hl
    simp only [prefixSum,←hS] at hu hl
    exact le_antisymm hu hl
  have hvec : c=aligned a b := by
    funext i
    have hi := heq (Iic i) (i.val+1) (by ext j; simp) (Fin.card_Iic _)
    have hlo := heq (Iio i) i.val (by ext j; simp) (Fin.card_Iio _)
    rw [← Finset.Iio_insert,Finset.sum_insert (by simp),Finset.sum_insert (by simp)] at hi
    linarith
  refine ⟨hconst,hvec,1,?_⟩
  intro t
  rw [hvec]
  change (t • (1:Mat n)-((1:Mat n)*diagonal a*(1:Mat n)ᵀ)*diagonal b).det = _
  simp only [one_mul,transpose_one,mul_one,diagonal_mul_diagonal]
  rw [←diagonal_one,←diagonal_smul,diagonal_sub, det_diagonal]
  simp [aligned]

end OMA.S_mo_193467

namespace OMA.S_mo_193467
open Matrix Finset
private def lo (a b : Vec 2) := a 0*b 1+a 1*b 0
private def hi (a b : Vec 2) := a 0*b 0+a 1*b 1

private lemma det_two_shift (M : Mat 2) (t : ℝ) :
    (t • (1:Mat 2)-M).det = t^2-t*(M 0 0+M 1 1)+M.det := by
  simp [Matrix.det_fin_two]
  ring

private lemma trace_det_pair (a b : Vec 2) (O : unitary (Mat 2)) :
    let Q := (O:Mat 2)
    let M := (Q*diagonal a*Qᵀ)*diagonal b
    M.det = (a 0*a 1)*(b 0*b 1) ∧
      M 0 0+M 1 1=lo a b+(Q 0 0)^2*(hi a b-lo a b) ∧ Q 0 0 ^ 2 ≤ 1 := by
  dsimp only
  let Q := (O:Mat 2)
  have h1 : Q*Qᵀ=1 := by simpa [Q,Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem O.property
  have h2 : Qᵀ*Q=1 := by simpa [Q,Matrix.star_eq_conjTranspose] using Unitary.star_mul_self_of_mem O.property
  have row (i : Fin 2) : Q i 0^2 + Q i 1^2=1 := by
    simpa [Matrix.mul_apply,Fin.sum_univ_two,pow_two] using congrFun (congrFun h1 i) i
  have col (i : Fin 2) : Q 0 i^2 + Q 1 i^2=1 := by
    simpa [Matrix.mul_apply,Fin.sum_univ_two,pow_two] using congrFun (congrFun h2 i) i
  have hdet := congrArg Matrix.det h1
  simp only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at hdet
  constructor
  · simp only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal,Fin.prod_univ_two]
    change Q.det * (a 0*a 1) * Q.det * (b 0*b 1)=_
    linear_combination (a 0*a 1*(b 0*b 1))*hdet
  have r01 : Q 0 1^2=1-Q 0 0^2 := by linarith only [row 0]
  have r10 : Q 1 0^2=1-Q 0 0^2 := by linarith only [col 0]
  have r11 : Q 1 1^2=Q 0 0^2 := by linarith only [row 1,r10]
  constructor
  · change ((Q*diagonal a*Qᵀ)*diagonal b) 0 0+((Q*diagonal a*Qᵀ)*diagonal b) 1 1 = _
    simp [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two,lo,hi,Matrix.diagonal_apply]
    change _ = a 0*b 1 + a 1*b 0 + Q 0 0^2*((a 0*b 0+a 1*b 1)-(a 0*b 1+a 1*b 0))
    linear_combination (a 1*b 0)*r01 + (a 0*b 1)*r10 + (a 1*b 1)*r11
  · change Q 0 0^2≤1
    linarith only [row 0,sq_nonneg (Q 0 1)]

private lemma realize_weight {s : ℝ} (hs : 0 ≤ s) (ht : s ≤ 1) :
    ∃ O : unitary (Mat 2), (O:Mat 2) 0 0 ^ 2 = s := by
  let x := Real.sqrt s
  let y := Real.sqrt (1-s)
  let Q : Mat 2 := !![x,-y;y,x]
  have hx : x^2=s := Real.sq_sqrt hs
  have hy : y^2=1-s := Real.sq_sqrt (by linarith)
  have hQ : Qᵀ*Q=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Q,Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith
  exact ⟨⟨Q,Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hQ)⟩,hx⟩

lemma two_case (a b c : Vec 2) (ha : Antitone a) (hb : Antitone b) :
    realizes a b c ↔ c 0*c 1=(a 0*a 1)*(b 0*b 1) ∧
      a 0*b 1+a 1*b 0 ≤ c 0+c 1 ∧ c 0+c 1 ≤ a 0*b 0+a 1*b 1 := by
  have hgap : 0≤hi a b-lo a b := by
    have h := mul_nonneg (sub_nonneg.mpr (ha (show (0:Fin 2)≤1 by decide)))
      (sub_nonneg.mpr (hb (show (0:Fin 2)≤1 by decide)))
    dsimp [lo,hi]
    linarith
  constructor
  · rintro ⟨O,hO⟩
    obtain ⟨hd,htr,hu⟩ := trace_det_pair a b O
    have h0 := hO 0
    have h1 := hO 1
    rw [det_two_shift,Fin.prod_univ_two,hd,htr] at h0 h1
    change _ ∧ lo a b≤c 0+c 1 ∧ c 0+c 1≤hi a b
    have hprod : c 0*c 1=(a 0*a 1)*(b 0*b 1) := by nlinarith only [h0]
    have hsum : c 0+c 1=lo a b+(O:Mat 2) 0 0^2*(hi a b-lo a b) := by nlinarith only [hprod,h1]
    refine ⟨hprod,?_,?_⟩ <;> rw [hsum]
    · linarith only [mul_nonneg (sq_nonneg ((O:Mat 2) 0 0)) hgap]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr hu) hgap]
  · rintro ⟨hprod,hlo,hhi⟩
    change lo a b≤_ at hlo
    change _≤hi a b at hhi
    obtain ⟨u,hu,hv,hvalue⟩ : ∃ u : ℝ, 0≤u ∧ u≤1 ∧ c 0+c 1=lo a b+u*(hi a b-lo a b) := by
      rcases hgap.eq_or_lt with h|h
      · exact ⟨0,by norm_num,by norm_num,by linarith⟩
      · refine ⟨(c 0+c 1-lo a b)/(hi a b-lo a b),div_nonneg (by linarith) h.le,?_,?_⟩
        · apply (div_le_iff₀ h).2
          linarith
        · field_simp
          ring
    obtain ⟨O,hO⟩ := realize_weight hu hv
    refine ⟨O,fun t => ?_⟩
    obtain ⟨hd,htr,_⟩ := trace_det_pair a b O
    rw [det_two_shift,Fin.prod_univ_two,hd,htr,hO,←hvalue,←hprod]
    ring

end OMA.S_mo_193467

namespace OMA.S_mo_193467
open Matrix Finset
private lemma weak_log_example : weakBounds leftSpec rightSpec productSpec ∧
    logBounds leftSpec rightSpec productSpec := by
  have hl (S : Finset (Fin 3)) :
      (∑ i ∈ S,opposite leftSpec rightSpec i) ≤ prefixSum productSpec S.card ∧
      (∏ i ∈ S,opposite leftSpec rightSpec i) ≤ prefixProd productSpec S.card := by
    fin_cases S <;> norm_num [opposite,prefixSum,prefixProd,leftSpec,rightSpec,productSpec,
      Finset.sum_filter,Finset.prod_filter,Fin.sum_univ_succ,Fin.prod_univ_succ,Fin.rev]
  have hu (k : ℕ) :
      prefixSum productSpec k ≤ prefixSum (aligned leftSpec rightSpec) k ∧
      prefixProd productSpec k ≤ prefixProd (aligned leftSpec rightSpec) k := by
    by_cases hk : k≤3
    · interval_cases k <;> norm_num [prefixSum,prefixProd,aligned,leftSpec,rightSpec,productSpec,
        Finset.sum_filter,Finset.prod_filter,Fin.sum_univ_succ,Fin.prod_univ_succ]
    · have he : univ.filter (fun i : Fin 3 => i.val<k)=univ := by
        apply filter_true_of_mem
        intro i _
        omega
      norm_num [prefixSum,prefixProd,he,Fin.sum_univ_succ,Fin.prod_univ_succ,aligned,leftSpec,rightSpec,productSpec]
  refine ⟨⟨fun S => (hl S).1,fun k => (hu k).1⟩,fun S => (hl S).2,fun k => (hu k).2,?_⟩
  norm_num [Fin.prod_univ_succ,aligned,leftSpec,rightSpec,productSpec]
end OMA.S_mo_193467

namespace OMA.S_mo_193467
private lemma orders :
    Antitone leftSpec ∧ Antitone rightSpec ∧ Antitone productSpec ∧
    (∀ i,0<leftSpec i) ∧ (∀ i,0<rightSpec i) ∧ (∀ i,0<productSpec i) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | intro i j h
      fin_cases i <;> fin_cases j <;> norm_num [Fin.le_def,leftSpec,rightSpec,productSpec] at *
    | intro i
      fin_cases i <;> norm_num [leftSpec,rightSpec,productSpec]
end OMA.S_mo_193467

namespace OMA.S_mo_193467
open Matrix Finset
private lemma impossible : ¬realizes leftSpec rightSpec productSpec := by
  rintro ⟨O,hO⟩
  let M : Mat 3 := O
  have hu : M*Mᵀ=1 := O.property.2
  have hd (i j : Fin 3) : (M*diagonal leftSpec*Mᵀ) i j =
      (if i=j then 1 else 0)+8*M i 0*M j 0 := by
    have h := congrArg (fun N : Mat 3 => N i j) hu
    simp only [Matrix.mul_apply,Fin.sum_univ_three,transpose_apply,one_apply] at h
    rw [Matrix.mul_apply]
    norm_num [Fin.sum_univ_three,mul_diagonal,transpose_apply,
      show leftSpec 0=9 from rfl,show leftSpec 1=1 from rfl,show leftSpec 2=1 from rfl]
    linarith
  have h := hO 4
  change ((4:ℝ) • (1:Mat 3) - (M*diagonal leftSpec*Mᵀ)*diagonal rightSpec).det = _ at h
  rw [Matrix.det_fin_three] at h
  have h02 : (0 : Fin 3)≠2 := by decide
  have h12 : (1 : Fin 3)≠2 := by decide
  norm_num [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.mul_diagonal,hd,h02,h12,h02.symm,h12.symm,
    Matrix.one_apply,show rightSpec 0=4 from rfl,show rightSpec 1=3 from rfl,show rightSpec 2=1 from rfl,
    productSpec,Fin.prod_univ_succ] at h
  ring_nf at h
  nlinarith [sq_nonneg (M 0 0)]
end OMA.S_mo_193467

open OMA.S_mo_193467
theorem OMA.solution : type_of% @OMA.S_mo_193467.main := by
  refine ⟨fun _ a b c ha hb hc _ _ _ h => strong_case a b c ha hb hc h,?_,two_case⟩
  obtain ⟨ha,hb,hc,pa,pb,pc⟩ := OMA.S_mo_193467.orders
  exact ⟨ha,hb,hc,pa,pb,pc,OMA.S_mo_193467.weak_log_example.1,
    OMA.S_mo_193467.weak_log_example.2,OMA.S_mo_193467.impossible⟩
