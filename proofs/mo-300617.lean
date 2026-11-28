import OMAStatements.S_mo_300617

namespace OMA.S_mo_300617
open Matrix
open scoped Matrix.Norms.L2Operator
open Finset WithLp

private lemma row_only {n : ℕ} {J : Sq (Fin n)} (hJ : primaryUpper J)
    (y : Fin n → ℂ) (i : Fin n) (h : ∀ j, i<j → J i i=J j j → y j=0) :
    (J *ᵥ y) i=J i i*y i := by
  classical
  change (∑ j, J i j*y j)=J i i*y i
  refine sum_eq_single i (fun j _ hji => ?_) (by simp)
  by_cases hj : J i j=0
  · simp [hj]
  · obtain ⟨hij,he⟩ := hJ i j hji.symm hj
    simp [h j hij he]

private lemma eigen_support {n : ℕ} {J : Sq (Fin n)} (hJ : primaryUpper J)
    (y : Fin n → ℂ) (b : ℂ) (hb : b≠0) (hy : J *ᵥ y=b • y) :
    ∀ i, J i i=0 → y i=0 := by
  intro i
  induction hd : n-i.val using Nat.strong_induction_on generalizing i with
  | h d ih =>
    intro h0
    have hrow := row_only hJ y i (by
      intro j hij he
      exact ih (n-j.val) (by omega) j rfl (he ▸ h0))
    rw [hy,h0,zero_mul] at hrow
    exact (mul_eq_zero.mp hrow).resolve_left hb

private lemma strip_support {n : ℕ} {J : Sq (Fin n)} (hJ : primaryUpper J)
    (y : Fin n → ℂ) (hy : ∀ i, J i i≠0 → (J *ᵥ y) i=0) :
    ∀ i, J i i≠0 → y i=0 := by
  intro i
  induction hd : n-i.val using Nat.strong_induction_on generalizing i with
  | h d ih =>
    intro h0
    have hrow := row_only hJ y i (by
      intro j hij he
      exact ih (n-j.val) (by omega) j rfl (he ▸ h0))
    rw [hy i h0] at hrow
    exact (mul_eq_zero.mp hrow.symm).resolve_left h0

private lemma nil_support {n : ℕ} {J : Sq (Fin n)} (hJ : primaryUpper J)
    (k : ℕ) (y : Fin n → ℂ) (hy : J^k *ᵥ y=0) : ∀ i, J i i≠0 → y i=0 := by
  induction k generalizing y with
  | zero => exact fun i _ => congrFun (by simpa using hy : y=0) i
  | succ k ih =>
    rw [pow_succ,← mulVec_mulVec] at hy
    exact strip_support hJ y (ih _ hy)

private lemma two_norm_mono {ι : Type} [Fintype ι] (x y : ι → ℂ)
    (h : ∀ i, ‖x i‖≤‖y i‖) : ‖toLp 2 x‖≤‖toLp 2 y‖ := by
  rw [EuclideanSpace.norm_eq,EuclideanSpace.norm_eq]
  exact Real.sqrt_le_sqrt (sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2))

private lemma op_bound {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (M : Matrix ι κ ℂ) (x : κ → ℂ) :
    ‖toLp 2 (M *ᵥ x)‖ ≤ ‖M‖ * ‖toLp 2 x‖ := M.l2_opNorm_mulVec (toLp 2 x)

set_option maxHeartbeats 800000 in
private lemma separation {ι : Type} [Fintype ι] [DecidableEq ι] {A : Sq ι}
    (v z : ι → ℂ) (b : ℂ) (hb : b≠0) (hv : A *ᵥ v=b • v)
    (k : ℕ) (hz : A^k *ᵥ z=0) (hd : ‖toLp 2 (v-z)‖≤1) :
    lower A ‖toLp 2 v‖ := by
  intro V W J hVW hWV hAV hJ
  have hWA : W*A=J*W := by
    calc W*A=W*A*(V*W) := by rw [hVW,Matrix.mul_one]
         _ = W*(A*V)*W := by simp [Matrix.mul_assoc]
         _ = J*W := by rw [hAV,← Matrix.mul_assoc,hWV,Matrix.one_mul]
  have hyv : J *ᵥ (W *ᵥ v)=b • (W *ᵥ v) := by
    rw [mulVec_mulVec,← hWA,← mulVec_mulVec,hv,mulVec_smul]
  have hwk (s : ℕ) : W*A^s=J^s*W := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ,pow_succ,← Matrix.mul_assoc,ih,Matrix.mul_assoc,hWA,← Matrix.mul_assoc]
  have hyz : J^k *ᵥ (W *ᵥ z)=0 := by
    rw [mulVec_mulVec,← hwk,← mulVec_mulVec,hz,mulVec_zero]
  have hy : ‖toLp 2 (W *ᵥ v)‖≤‖toLp 2 (W *ᵥ (v-z))‖ := by
    apply two_norm_mono
    intro i
    rw [mulVec_sub, Pi.sub_apply]
    by_cases hi : J i i=0
    · rw [eigen_support hJ _ b hb hyv i hi]
      simpa only [norm_zero] using (norm_nonneg (0-(W *ᵥ z) i))
    · simp [nil_support hJ k _ hyz i hi]
  have hvw : V *ᵥ (W *ᵥ v)=v := by simp [mulVec_mulVec,hVW]
  calc ‖toLp 2 v‖ = ‖toLp 2 (V *ᵥ (W *ᵥ v))‖ := by rw [hvw]
       _ ≤ ‖V‖* ‖toLp 2 (W *ᵥ v)‖ := op_bound V _
       _ ≤ ‖V‖* ‖toLp 2 (W *ᵥ (v-z))‖ := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
       _ ≤ ‖V‖* (‖W‖* ‖toLp 2 (v-z)‖) := mul_le_mul_of_nonneg_left
         (op_bound W (v-z)) (norm_nonneg _)
       _ ≤ ‖V‖*‖W‖ := (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hd) (norm_nonneg _))

open Finset WithLp
private lemma entry_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : Sq ι) (i j : ι) :
    ‖T i j‖≤‖T‖ := by
  let x : EuclideanSpace ℂ ι := PiLp.single 2 j 1
  have hx : ‖x‖=1 := by simp [x]
  have h := (PiLp.norm_apply_le (toLp 2 (T *ᵥ x)) i).trans (T.l2_opNorm_mulVec x)
  simpa [hx,x,PiLp.single_apply, mulVec, dotProduct, Pi.single_apply] using h

private lemma large_mode {ι : Type} [Fintype ι] [DecidableEq ι] (T : Sq ι)
    (hs : T.IsHermitian) (i j : ι) (F : ℝ) (hF : 0<F) (hentry : F≤‖T i j‖) :
    ∃ (u : ℂ) (w : ι → ℂ) (c : ι),
      F≤‖u‖ ∧ T *ᵥ w=u • w ∧ ‖toLp 2 w‖=1 ∧ 1≤(Fintype.card ι:ℝ)*‖w c‖ := by
  classical
  let u := fun i => (hs.eigenvalues i:ℂ)
  have hspec : ‖T‖=‖u‖ := by
    calc ‖T‖ = ‖Unitary.conjStarAlgAut ℂ _ hs.eigenvectorUnitary (diagonal u)‖ := by
           exact congrArg norm hs.spectral_theorem
         _ = _ := by simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
             CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
  obtain ⟨l,hl⟩ : ∃ l,F≤‖u l‖ := by
    by_contra! h
    have ht := (pi_norm_lt_iff hF).mpr h
    linarith [entry_le T i j]
  let w := hs.eigenvectorBasis l
  have hw : ‖w‖=1 := hs.eigenvectorBasis.norm_eq_one l
  obtain ⟨c,_,hc⟩ := exists_max_image univ (fun q => ‖w q‖) ⟨i,mem_univ _⟩
  refine ⟨u l,⇑w,c,hl,?_,hw,?_⟩
  · rw [hs.mulVec_eigenvectorBasis]
    ext q
    exact Complex.real_smul
  have hsq := EuclideanSpace.norm_sq_eq w
  rw [hw,one_pow] at hsq
  calc (1:ℝ)=∑ q,‖w q‖^2 := hsq
       _ ≤ ∑ _ : ι,‖w c‖ := sum_le_sum (fun q _ => by
         have hq := PiLp.norm_apply_le w q
         rw [hw] at hq
         exact (by nlinarith [norm_nonneg (w q)] : ‖w q‖^2 ≤ ‖w q‖) |>.trans
           (hc q (mem_univ q)))
       _ = _ := by simp

namespace Triangular
open Matrix Finset
open scoped Matrix.Norms.L2Operator
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def binary {n : ℕ} (A : Mat n) : Prop := ∀ i j, A i j=0 ∨ A i j=1
def mass {n : ℕ} (A : Mat n) : ℝ := ∑ i,∑ j,A i j
def unitUpper {n : ℕ} (A : Mat n) : Prop :=
  binary A ∧ (∀ i, A i i=1) ∧ (∀ (i j : Fin n), j < i → A i j = 0)
def fibEnvelope (n : ℕ) : Mat n := fun i j =>
  if i=j then 1 else if i<j then (Nat.fib (j.val-i.val):ℝ) else 0
def extreme (n : ℕ) : Mat n := fun i j =>
  if i=j ∨ (i<j ∧ (j.val-i.val)%2=1) then 1 else 0
def signs (n : ℕ) : Mat n := Matrix.diagonal fun i => (-1:ℝ)^i.val
lemma extreme_upper (n : ℕ) : unitUpper (extreme n) := by
  refine ⟨fun i j => ?_,fun i => by simp [extreme],fun i j h => ?_⟩
  · unfold extreme
    split <;> simp
  · simp [extreme,ne_of_gt h,not_lt_of_gt h]

lemma signs_sq (n : ℕ) : signs n * signs n = 1 := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [signs, ← pow_add,← two_mul,pow_mul]
  · simp [signs,h]

private def fibTerm (g : ℕ) : ℝ := if g=0 then 1 else (Nat.fib g : ℝ)
private def oddBand (n : ℕ) : Mat n := fun i j =>
  if i < j ∧ (j.val-i.val)%2=1 then 1 else 0

private lemma odd_fib_sum (g : ℕ) :
    (∑ d ∈ range g, if (g-d)%2=1 then fibTerm d else 0) = Nat.fib g := by
  induction g using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num [fibTerm]
  | more g h _ =>
    rw [sum_range_succ,sum_range_succ,Nat.fib_add_two,Nat.cast_add]
    have he (d : ℕ) (hd : d ∈ range g) : (g+2-d)%2 = (g-d)%2 := by
      have := mem_range.mp hd
      omega
    rw [sum_congr rfl (fun d hd => if_congr (by rw [he d hd]) rfl rfl),h]
    have h1 : g+2-g=2 := by omega
    have h2 : g+2-(g+1)=1 := by omega
    simp [h1,h2,fibTerm]

private lemma sign_conjugate (n : ℕ) :
    signs n * extreme n * signs n = 1-oddBand n := by
  ext i j
  simp only [signs,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.sub_apply]
  by_cases h : i=j
  · subst j
    simp [extreme,oddBand,← pow_add,← two_mul,pow_mul]
  · by_cases hb : i<j ∧ (j.val-i.val)%2=1
    · have hsum : j.val=i.val+(j.val-i.val) := by have := hb.1; omega
      have hneg : (-1:ℝ)^(j.val-i.val) = -1 := by
        rw [neg_one_pow_eq_pow_mod_two, hb.2]; norm_num
      simp only [extreme,hb,oddBand,Matrix.one_apply,h,if_false,zero_sub]
      rw [hsum,pow_add]
      rcases neg_one_pow_eq_or ℝ i.val with hp|hp <;> rw [hp,hneg] <;> norm_num
    · simp [extreme,oddBand,h,hb]

private lemma above_sum (n : ℕ) (i j : Fin n) :
    (oddBand n * fibEnvelope n) i j = (Nat.fib (j.val-i.val) : ℝ) := by
  classical
  rw [Matrix.mul_apply]
  have zero_out (k : Fin n) (hk : k ∉ Ioc i j) :
      oddBand n i k * fibEnvelope n k j = 0 := by
    by_cases hik : i < k
    · have hkj : j < k := by simpa [hik,not_le] using hk
      simp [fibEnvelope,hkj.ne',not_lt_of_gt hkj]
    · simp [oddBand,hik]
  rw [← sum_subset (subset_univ (Ioc i j)) (fun k _ hk => zero_out k hk)]
  rw [← odd_fib_sum]
  refine sum_bij (fun k _ => j.val-k.val) ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hi,hj⟩ := mem_Ioc.mp hk
    apply mem_range.mpr
    omega
  · intro k hk l hl he
    obtain ⟨_,hkj⟩ := mem_Ioc.mp hk
    obtain ⟨_,hlj⟩ := mem_Ioc.mp hl
    exact Fin.ext (by omega)
  · intro d hd
    have hd' := mem_range.mp hd
    refine ⟨⟨j.val-d,by omega⟩,mem_Ioc.mpr ⟨?_,?_⟩,?_⟩
    · change i.val < j.val-d
      omega
    · change j.val-d ≤ j.val
      omega
    · change j.val-(j.val-d)=d
      omega
  · intro k hk
    obtain ⟨hi,hj⟩ := mem_Ioc.mp hk
    have he : j.val-i.val-(j.val-k.val) = k.val-i.val := by omega
    rw [he]
    by_cases hkj : k=j
    · subst j
      by_cases ho : (k.val-i.val)%2 = 1 <;> simp [oddBand,hi,ho,fibEnvelope,fibTerm]
    · have hlt := lt_of_le_of_ne hj hkj
      have hne : j.val-k.val ≠ 0 := by omega
      by_cases ho : (k.val-i.val)%2 = 1 <;> simp [oddBand,hi,ho,fibEnvelope,hkj,hlt,fibTerm,hne]

lemma extreme_inverse (n : ℕ) :
    extreme n * (signs n * fibEnvelope n * signs n) = 1 := by
  have h : (1-oddBand n)*fibEnvelope n = 1 := by
    rw [sub_mul,one_mul]
    ext i j
    rw [Matrix.sub_apply,above_sum]
    rcases lt_trichotomy i j with hij|rfl|hji
    · simp [fibEnvelope,hij.ne,hij]
    · simp [fibEnvelope]
    · have he : j.val-i.val=0 := by omega
      simp [fibEnvelope,hji.ne',not_lt_of_gt hji,he]
  have hh := congrArg (fun M : Mat n => signs n*M*signs n) h
  rw [← sign_conjugate] at hh
  simpa only [← Matrix.mul_assoc,signs_sq,Matrix.one_mul,Matrix.mul_one] using hh

end Triangular

open Finset WithLp
private lemma dilation (p : ℕ) :
    ∃ (B : Sq (Fin (p+2) ⊕ Fin (p+2))) (u : ℂ) (w : Fin (p+2) ⊕ Fin (p+2) → ℂ)
        (c : Fin (p+2) ⊕ Fin (p+2)),
      (∀ i j,B i j=0 ∨ B i j=1) ∧ (Nat.fib (p+1):ℝ)≤‖u‖ ∧ u≠0 ∧
      B *ᵥ w=u⁻¹ • w ∧ ‖toLp 2 w‖=1 ∧ 1≤((2*(p+2):ℕ):ℝ)*‖w c‖ := by
  classical
  let m := p+2
  let D : Sq (Fin m) := (Triangular.extreme m).map Complex.ofRealHom
  let E : Sq (Fin m) :=
    (Triangular.signs m * Triangular.fibEnvelope m * Triangular.signs m).map Complex.ofRealHom
  have hDE : D*E=1 := by
    simpa [D,E,Matrix.map_one] using congrArg (fun P : Triangular.Mat m =>
      P.map Complex.ofRealHom) (Triangular.extreme_inverse m)
  have hED : E*D=1 := mul_eq_one_comm.mp hDE
  let B : Sq (Fin m ⊕ Fin m) := fromBlocks 0 D Dᴴ 0
  let T : Sq (Fin m ⊕ Fin m) := fromBlocks 0 Eᴴ E 0
  have hT : T.IsHermitian := by simp [T,IsHermitian,fromBlocks_conjTranspose]
  have hBT : B*T=1 := by
    have hed : Dᴴ*Eᴴ=1 := by
      simpa only [conjTranspose_mul,conjTranspose_one] using congrArg Matrix.conjTranspose hED
    simp [B,T,fromBlocks_multiply,hDE,hed,fromBlocks_one]
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨p+1, by omega⟩
  have hab : a<b := by change 0<p+1; omega
  have hF : (0:ℝ)<Nat.fib (p+1) := by exact_mod_cast Nat.fib_pos.mpr (by omega : 0<p+1)
  have he : ‖T (.inr a) (.inl b)‖ = (Nat.fib (p+1):ℝ) := by
    change ‖(E a b)‖=_
    have hfib : Triangular.fibEnvelope m a b = (Nat.fib (p+1):ℝ) := by
      simp only [Triangular.fibEnvelope,if_neg hab.ne,if_pos hab]
      rfl
    simp only [E,Matrix.map_apply,Complex.ofRealHom_eq_coe,Triangular.signs,Matrix.mul_diagonal,
      Matrix.diagonal_mul,hfib,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_pow]
    simp
  obtain ⟨u,w,c,hu,hTw,hw,hc⟩ := large_mode T hT (.inr a) (.inl b) _ hF he.ge
  have hu0 : u≠0 := norm_pos_iff.mp (hF.trans_le hu)
  have hBw : B *ᵥ w = u⁻¹ • w := by
    have h : u • (B *ᵥ w) = w := by
      rw [← mulVec_smul, ← hTw, mulVec_mulVec,hBT,one_mulVec]
    calc B *ᵥ w=u⁻¹ • (u • (B *ᵥ w)) := (inv_smul_smul₀ hu0 _).symm
         _ = _ := congrArg (fun z => u⁻¹ • z) h
  refine ⟨B,u,w,c,?_,hu,hu0,hBw,hw,?_⟩
  · have hb (i j : Fin m) : D i j=0 ∨ D i j=1 := by
      obtain h|h := (Triangular.extreme_upper m).1 i j <;> simp [D,Matrix.map_apply,h]
    intro i j
    rcases i with i|i <;> rcases j with j|j
    · simp [B]
    · exact hb i j
    · obtain h|h := hb j i <;> simp [B,conjTranspose_apply,h]
    · simp [B]
  · simpa [m,two_mul] using hc

open Finset WithLp
private def tip {m : ℕ} {ι : Type} (c : ι) (i : Fin m) : Fin m ⊕ ι :=
  if h : i.val+1 < m then Sum.inl ⟨i.val+1,h⟩ else Sum.inr c
private def attach {m : ℕ} {ι : Type} [DecidableEq ι] (B : Sq ι) (c : ι) :
    Sq (Fin m ⊕ ι) := fun i j => match i with
  | .inl a => if j=tip c a then 1 else 0
  | .inr b => match j with
    | .inl _ => 0
    | .inr e => B b e

private lemma attach_left {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Sq ι) (c : ι) (x : Fin m ⊕ ι → ℂ) (i : Fin m) :
    (attach B c *ᵥ x) (.inl i)=x (tip c i) := by
  classical
  change (∑ j,(if j=tip c i then (1:ℂ) else 0)*x j)=_
  simp [ite_mul]
private lemma attach_right {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Sq ι) (c : ι) (x : Fin m ⊕ ι → ℂ) (i : ι) :
    (attach B c *ᵥ x) (.inr i)=(B *ᵥ (x ∘ Sum.inr)) i := by
  simp [mulVec,dotProduct,Fintype.sum_sum_type,attach]

private lemma attach_nil {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Sq ι) (c : ι) (a : Fin m → ℂ) :
    attach B c ^ m *ᵥ (Sum.elim a 0)=0 := by
  classical
  let z := Sum.elim a (0 : ι → ℂ)
  have aux (k : ℕ) :
      (∀ i : Fin m,(attach B c ^ k *ᵥ z) (.inl i)=
        if h : i.val+k < m then a ⟨i.val+k,h⟩ else 0) ∧
      (∀ j : ι,(attach B c ^ k *ᵥ z) (.inr j)=0) := by
    induction k with
    | zero => simp [z]
    | succ k ih =>
      rw [pow_succ',← mulVec_mulVec]
      constructor
      · intro i
        rw [attach_left]
        by_cases h : i.val+1 < m
        · rw [tip,dif_pos h,ih.1]
          simp only [show i.val+1+k=i.val+(k+1) by omega]
        · have hk : ¬i.val+(k+1) < m := by omega
          simp [tip,h,ih.2,hk]
      · intro j
        rw [attach_right]
        have hz : (attach B c ^ k *ᵥ z) ∘ Sum.inr=0 := funext ih.2
        simp [hz]
  funext i
  rcases i with i|j
  · simpa using (aux m).1 i
  · exact (aux m).2 j

private lemma attach_bound {m : ℕ} (hm : 0 < m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Sq ι) (u : ℂ) (hu : u≠0) (w : ι → ℂ) (c : ι)
    (hw : B *ᵥ w=u⁻¹ • w) (hn : ‖toLp 2 w‖=1) :
    lower (attach (m:=m) B c) (‖u‖^m*‖w c‖) := by
  classical
  let a := fun i : Fin m => u^(m-i.val)*w c
  let v := Sum.elim a w
  let z := Sum.elim a (0 : ι → ℂ)
  have hv : attach B c *ᵥ v=u⁻¹ • v := by
    funext i
    rcases i with i|j
    · rw [attach_left]
      change v (tip c i)=u⁻¹*(u^(m-i.val)*w c)
      have hh : m-i.val=(m-(i.val+1))+1 := by omega
      rw [hh,pow_succ']
      field_simp
      by_cases hi : i.val+1 < m
      · simp [tip,hi,v,a]
      · have he : m-(i.val+1)=0 := by omega
        simp [tip,hi,he,v]
    · rw [attach_right]
      exact congrFun hw j
  have hdiff : v-z=Sum.elim (0 : Fin m → ℂ) w := by
    funext i
    rcases i with i|j <;> simp [v,z]
  have hn' : ‖toLp 2 (v-z)‖≤1 := by
    rw [hdiff,← hn]
    simp [EuclideanSpace.norm_eq,Fintype.sum_sum_type]
  have hs := separation v z u⁻¹ (inv_ne_zero hu) hv m (attach_nil B c a) hn'
  have hentry : ‖u‖^m*‖w c‖≤‖toLp 2 v‖ := by
    have he := PiLp.norm_apply_le (toLp 2 v) (Sum.inl (⟨0,hm⟩ : Fin m))
    simpa [v,a,norm_mul,norm_pow] using he
  exact fun V W J hvw hwv hav hj => hentry.trans (hs V W J hvw hwv hav hj)

open WithLp
private lemma family (p : ℕ) : ∃ A : Sq (Axis (p+2)), binary A ∧
    lower A ((Nat.fib (p+1):ℝ)^(p+2)/(2*(p+2):ℕ)) := by
  obtain ⟨B,u,w,c,hbin,hu,hu0,hw,hn,hc⟩ := dilation p
  let m := p+2
  let A := attach (m:=m) B c
  refine ⟨A,?_,?_⟩
  · intro i j
    rcases i with i|i
    · by_cases hj : j=tip c i <;> simp [A,attach,hj]
    · rcases j with j|j
      · simp [A,attach]
      · exact hbin i j
  have hs := attach_bound (m:=m) (by omega) B u hu0 w c hw hn
  have hpos : 0<((2*(p+2):ℕ):ℝ) := by positivity
  have hcoord := (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hc)
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.fib (p+1)) : (0:ℝ)≤_) hu m
  intro V W J hVW hWV hAV hJ
  refine le_trans ?_ (hs V W J hVW hWV hAV hJ)
  rw [div_eq_mul_one_div]
  exact mul_le_mul hp hcoord (by positivity) (by positivity)

private lemma answer : type_of% @OMA.S_mo_300617.main := by
  refine ⟨family,?_⟩
  obtain ⟨A,hA,hl⟩ := family 98
  refine ⟨A,hA,?_⟩
  intro V W J hVW hWV hAV hJ
  apply le_trans _ (hl V W J hVW hWV hAV hJ)
  change (300:ℝ)^300+1 ≤ (Nat.fib 99:ℝ)^100/200
  apply (le_div_iff₀ (by norm_num)).mpr
  have hf : (300:ℝ)^4≤(Nat.fib 99:ℝ) := by norm_num
  have h1 : (1:ℝ)≤300^300 := one_le_pow₀ (by norm_num) 
  have h2 : (400:ℝ)≤300^100 := le_trans (by norm_num : (400:ℝ)≤300^2)
    (pow_le_pow_right₀ (by norm_num) (by decide))
  have hs (x : ℝ) (hx : 1≤x) : (x+1)*200≤x*400 := by linarith
  calc ((300:ℝ)^300+1)*200 ≤ 300^300*400 := hs _ h1
       _ ≤ 300^300*300^100 := mul_le_mul_of_nonneg_left h2 (by positivity)
       _ = (300^4)^100 := by rw [← pow_add,← pow_mul]
       _ ≤ _ := pow_le_pow_left₀ (by positivity) hf 100

end OMA.S_mo_300617
open OMA.S_mo_300617 in
theorem OMA.solution : type_of% @OMA.S_mo_300617.main := answer

