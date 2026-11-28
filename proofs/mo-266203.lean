import OMAStatements.S_mo_266203

namespace OMA.S_mo_266203
open Matrix Finset

lemma had_bound_index {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℝ)
    (hn : 0 < Fintype.card ι) (hsign : ∀ i j, H i j=1 ∨ H i j= -1) :
    H.det^2 ≤ (Fintype.card ι : ℝ)^(Fintype.card ι) ∧
      (H.det^2=(Fintype.card ι : ℝ)^(Fintype.card ι) ↔
        H*Hᵀ=(Fintype.card ι : ℝ) • 1) := by
  classical
  let N := Fintype.card ι
  have hN : (0:ℝ)<N := by exact_mod_cast hn
  let G := H*Hᵀ
  have hg : G.PosSemidef := by simpa [G] using posSemidef_self_mul_conjTranspose H
  let e := hg.1.eigenvalues
  have he i : 0≤e i := hg.eigenvalues_nonneg i
  have hd : H.det^2=∏ i,e i := by
    calc H.det^2 = G.det := by simp [G,det_mul,pow_two]
         _ = _ := by simpa [e] using hg.1.det_eq_prod_eigenvalues
  have hdiag i : G i i=(N:ℝ) := by
    change (∑ j,H i j * H i j) = N
    have hsq j : H i j * H i j=1 := by rcases hsign i j with h|h <;> simp [h]
    simp [hsq,N]
  have hsum : ∑ i,e i=(N:ℝ)*N := by
    calc ∑ i,e i = G.trace := by simpa [e] using hg.1.trace_eq_sum_eigenvalues.symm
         _ = _ := by simp [Matrix.trace,Matrix.diag,hdiag,N]
  let w := fun _ : ι => (N:ℝ)⁻¹
  have hw i : 0 < w i := inv_pos.mpr hN
  have h1 : ∑ i,w i=1 := by simp [w,N, hN.ne' ]
  have hmean : ∑ i,w i * e i=(N:ℝ) := by
    simp only [w, ← Finset.mul_sum, hsum]
    field_simp
  have hgeom : (∏ i,e i ^ w i)=(H.det^2)^((N:ℝ)⁻¹) := by
    rw [hd]
    exact Real.finsetProd_rpow univ e (fun i _ => he i) _
  have hle := Real.geom_mean_le_arith_mean_weighted univ w e
    (fun i _ => (hw i).le) h1 (fun i _ => he i)
  rw [hgeom,hmean] at hle
  have hn0 := Nat.ne_of_gt hn
  constructor
  · have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (sq_nonneg _) _) hle N
    rwa [Real.rpow_inv_natCast_pow (sq_nonneg _) hn0] at hpow
  constructor
  · intro h
    have hEq : ∏ i,e i ^ w i = ∑ i,w i * e i := by
      rw [hgeom,hmean,h,Real.pow_rpow_inv_natCast hN.le hn0]
    have heq := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' univ w e
      (fun i _ => hw i) h1 (fun i _ => he i)).mp hEq
    have econ : e = fun _ => (N:ℝ) := funext fun i => (heq i (mem_univ i)).trans hmean
    have hspec : G = Unitary.conjStarAlgAut ℝ _ hg.1.eigenvectorUnitary (diagonal e) := by
      simpa [e] using hg.1.spectral_theorem
    have hsc : diagonal e=(N:ℝ) • (1 : Matrix ι ι ℝ) := by
      ext i j
      by_cases hij : i=j <;> simp [econ,hij]
    rw [hsc,map_smul,map_one] at hspec
    exact hspec
  · intro h
    simpa [det_mul,det_smul,pow_two] using congrArg Matrix.det h

lemma had_bound {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0<n)
    (hsign : ∀ i j, H i j=1 ∨ H i j= -1) :
    H.det^2 ≤ (n:ℝ)^n ∧ (H.det^2=(n:ℝ)^n ↔ H*Hᵀ=(n:ℝ) • 1) := by
  simpa using had_bound_index H (by simpa using hn) hsign

end OMA.S_mo_266203

namespace OMA.S_mo_266203
open Matrix
private abbrev topIndex {n : ℕ} : Unit ⊕ Fin n := Sum.inl ()
private lemma top_minor {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) :
    ((border 1 N).updateRow topIndex (Pi.single topIndex 1)).det = N.det := by
  have he : (border 1 N).updateRow topIndex (Pi.single topIndex 1) =
      Matrix.fromBlocks (1 : Matrix Unit Unit ℝ) 0 (Matrix.of fun _ _ => 1) N := by
    ext i j
    rcases i with _|i <;> rcases j with _|j <;>
      simp [border,topIndex,Matrix.updateRow,Function.update,Matrix.fromBlocks]
  rw [he,Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,one_mul]
lemma border_det_affine {n : ℕ} (u : ℝ) (N : Matrix (Fin n) (Fin n) ℝ) :
    (border u N).det = (border 1 N).det + (u-1)*N.det := by
  let H := border 1 N
  let e : Unit ⊕ Fin n → ℝ := Pi.single topIndex 1
  have he : border u N = H.updateRow topIndex (H topIndex + (u-1) • e) := by
    ext i j
    rcases i with _|i <;> rcases j with _|j <;>
      simp [H,border,topIndex,e,Matrix.updateRow,Function.update,Matrix.fromBlocks]
  rw [he,Matrix.det_updateRow_add,Matrix.det_updateRow_smul,top_minor]
  simp [H]
lemma hadamard_minor {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (hH : border 1 N * (border 1 N)ᵀ = ((n+1:ℕ):ℝ) • 1) :
    N.det = (border 1 N).det/(n+1) := by
  let H := border 1 N
  have he : ((n+1:ℕ):ℝ) • H.adjugate = H.det • Hᵀ := by
    calc _ = H.adjugate * (((n+1:ℕ):ℝ) • 1) := by rw [Matrix.mul_smul,Matrix.mul_one]
         _ = H.adjugate * (H*Hᵀ) := by rw [hH]
         _ = _ := by rw [←Matrix.mul_assoc,Matrix.adjugate_mul,Matrix.smul_mul,Matrix.one_mul]
  have h := congrArg (fun M : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ => M topIndex topIndex) he
  change ((n+1:ℕ):ℝ)*H.adjugate topIndex topIndex=H.det*H topIndex topIndex at h
  rw [Matrix.adjugate_apply,top_minor] at h
  change ((n+1:ℕ):ℝ)*N.det=H.det*1 at h
  apply (eq_div_iff (by positivity)).mpr
  push_cast at h
  linarith
lemma value_det {n : ℕ} (x : ℝ) (a : Matrix (Fin n) (Fin n) Bool) (hx : 1<x) :
    |(value x a).det| = ((x-1)/2)^n / ((x-1)/(x+1)) * |(border ((x-1)/(x+1)) (signCore a)).det| := by
  let u := (x-1)/(x+1)
  have hu : 0<u := div_pos (sub_pos.mpr hx) (by linarith)
  let B : Matrix Unit (Fin n) ℝ := Matrix.of fun _ _ => u⁻¹
  let C : Matrix (Fin n) Unit ℝ := Matrix.of fun _ _ => 1
  let K := Matrix.fromBlocks (1 : Matrix Unit Unit ℝ) B C (signCore a)
  have hK : border u (signCore a) = K.updateRow topIndex (u • K topIndex) := by
    ext i j
    rcases i with _|i <;> rcases j with _|j <;>
      simp [border,K,B,C,topIndex,Matrix.updateRow,Function.update,Matrix.fromBlocks,hu.ne']
  have hdet : (border u (signCore a)).det=u*K.det := by
    rw [hK,Matrix.det_updateRow_smul]
    simp
  have hv : value x a = (-(x-1)/2) • (signCore a - C*B) := by
    ext i j
    change (if a i j then x else 1) = (-(x-1)/2)*((if a i j then -1 else 1)-(C*B) i j)
    rw [Matrix.mul_apply, Fintype.sum_unique]
    simp only [C,B,Matrix.of_apply,one_mul,u]
    split <;> field_simp [show x+1 ≠ 0 by linarith,show x-1 ≠ 0 by linarith] <;> ring
  change |(value x a).det| = ((x-1)/2)^n/u*|(border u (signCore a)).det|
  rw [hv,Matrix.det_smul,←Matrix.det_fromBlocks_one₁₁ B C (signCore a),hdet,abs_mul,abs_mul,
    abs_pow,abs_div,abs_neg,abs_of_pos (sub_pos.mpr hx),abs_of_pos hu]
  simp only [abs_of_pos (by norm_num : (0:ℝ)<2),Fintype.card_fin]
  change ((x-1)/2)^n*|K.det| = ((x-1)/2)^n/u*(u*|K.det|)
  field_simp
end OMA.S_mo_266203

namespace OMA.S_mo_266203
open Matrix Filter
theorem det_bound {n : ℕ} (a : Matrix (Fin n) (Fin n) Bool) :
    (border 1 (signCore a)).det^2 ≤ ((n+1:ℕ):ℝ)^(n+1) ∧
    ((border 1 (signCore a)).det^2 = ((n+1:ℕ):ℝ)^(n+1) ↔ extremalGram a) := by
  have hs (i j : Unit ⊕ Fin n) : border 1 (signCore a) i j = 1 ∨ border 1 (signCore a) i j = -1 := by
    cases i with
    | inl i => cases j <;> exact Or.inl rfl
    | inr i =>
      cases j with
      | inl j => exact Or.inl rfl
      | inr j => cases h : a i j <;> simp [border,signCore,fromBlocks,h]
  have hb := had_bound_index (border 1 (signCore a)) (by simp) hs
  simpa [extremalGram,Nat.add_comm] using hb
private theorem affine_abs {n : ℕ} (hn : 0 < n) (x : ℝ) (a : Matrix (Fin n) (Fin n) Bool) (hx : 1<x) :
    |(value x a).det| = (x-1)^(n-1)/2^n *
      |(x+1)*(border 1 (signCore a)).det - 2*(signCore a).det| := by
  rw [value_det x a hx,border_det_affine]
  have hu : 0 < x+1 := by linarith
  have ht : 0 < x-1 := by linarith
  have eq₁ (D E : ℝ) : D + ((x-1)/(x+1)-1)*E = ((x+1)*D-2*E)/(x+1) := by
    field_simp
    ring
  have hpow : (x-1)^n=(x-1)^(n-1)*(x-1) := by rw [←pow_succ,show n-1+1=n by omega]
  rw [eq₁,abs_div,abs_of_pos hu,div_pow,hpow]
  field_simp
theorem formula {n : ℕ} (hn : 0<n) (a : Matrix (Fin n) (Fin n) Bool)
    (ha : extremalGram a) (x : ℝ) (hx : 1<x) : |(value x a).det| =
      |(border 1 (signCore a)).det|/2^n * (x-1)^(n-1) * (x+((n:ℝ)-1)/(n+1)) := by
  rw [affine_abs hn x a hx,hadamard_minor _ ha]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < x+((n:ℝ)-1)/(n+1) := by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hd (D : ℝ) : (x+1)*D-2*(D/(n+1)) = (x+((n:ℝ)-1)/(n+1))*D := by field_simp; ring
  rw [hd,abs_mul,abs_of_pos hpos]
  ring
private theorem eventual_linear (a b c d : ℝ) (hab : |a| < |b|) :
    ∀ᶠ x : ℝ in atTop, |(x+1)*a-2*c| < |(x+1)*b-2*d| := by
  filter_upwards [eventually_gt_atTop (2*(|c|+|d|)/(|b|-|a|)),eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hpos : 0 < x+1 := by linarith
  have h := (div_lt_iff₀ (sub_pos.mpr hab)).mp hx
  have h₁ := abs_sub_le ((x+1)*a) 0 (2*c)
  have h₂ := abs_add_le ((x+1)*b-2*d) (2*d)
  rw [sub_add_cancel] at h₂
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_pos hpos,abs_of_pos (by norm_num : (0:ℝ)<2)] at h₁ h₂
  linarith
theorem generic_optimum {n : ℕ} (hn : 0<n) (a : Matrix (Fin n) (Fin n) Bool) (ha : extremalGram a) :
    ∀ᶠ x : ℝ in atTop, ∀ b : Matrix (Fin n) (Fin n) Bool,
        |(value x b).det| ≤ |(value x a).det| ∧ (|(value x b).det| = |(value x a).det| ↔ extremalGram b) := by
  classical
  apply Filter.eventually_all.mpr
  intro b
  have hA := (det_bound a).2.mpr ha
  by_cases hB : extremalGram b
  · have hsq := (det_bound b).2.mpr hB
    have heq : |(border 1 (signCore b)).det| = |(border 1 (signCore a)).det| := by
      nlinarith [sq_abs (border 1 (signCore a)).det,sq_abs (border 1 (signCore b)).det,
        abs_nonneg (border 1 (signCore b)).det,abs_nonneg (border 1 (signCore a)).det]
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    rw [formula hn a ha x hx,formula hn b hB x hx,heq]
    simp [hB]
  · have hstrict := lt_of_le_of_ne (det_bound b).1 (fun he => hB ((det_bound b).2.mp he))
    have hlt : |(border 1 (signCore b)).det| < |(border 1 (signCore a)).det| := by
      rwa [←hA,sq_lt_sq] at hstrict
    filter_upwards [eventual_linear _ _ (signCore b).det (signCore a).det hlt,eventually_gt_atTop (1:ℝ)] with x hx hx1
    rw [affine_abs hn x a hx1,affine_abs hn x b hx1]
    have hc : 0 < (x-1)^(n-1)/(2:ℝ)^n := by positivity
    have hfinal := mul_lt_mul_of_pos_left hx hc
    exact ⟨hfinal.le,iff_of_false hfinal.ne hB⟩
end OMA.S_mo_266203

namespace OMA.S_mo_266203
open Matrix
private def masks : Fin 15 → ℕ :=
  ![21845,26214,30771,13176,7725,19230,11595,32640,10965,6630,1971,19704,25005,13470,21195]
def exampleCore : Matrix (Fin 15) (Fin 15) Bool := fun i j => (masks i).testBit j.val
private def rowFlip {n : ℕ} (a : Matrix (Fin n) (Fin n) Bool) : Prop :=
  ∃ i, ∀ j, j ≠ i → ∃ k, ∀ c, xor (a i c) (a j c) = a k c
private theorem rowFlip_transpose {n : ℕ} {a : Matrix (Fin n) (Fin n) Bool}
    (ha : rowFlip a) (hs : symmetrizable a) : rowFlip aᵀ := by
  obtain ⟨i,hi⟩ := ha
  obtain ⟨p,q,hpq⟩ := hs
  have swap (u v : Fin n) : a u v = a (p (q.symm v)) (q (p.symm u)) := by
    simpa using hpq (p.symm u) (q.symm v)
  refine ⟨q (p.symm i), ?_⟩
  intro j hj
  have hne : p (q.symm j) ≠ i := by
    intro he
    apply hj
    rw [←he]
    simp
  obtain ⟨k,hk⟩ := hi (p (q.symm j)) hne
  refine ⟨q (p.symm k),?_⟩
  intro c
  change xor (a c (q (p.symm i))) (a c j) = a c (q (p.symm k))
  rw [swap c (q (p.symm i)),swap c j,swap c (q (p.symm k))]
  simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] using hk (q (p.symm c))
private def signedExample : Matrix (Unit ⊕ Fin 15) (Unit ⊕ Fin 15) ℤ :=
  Matrix.fromBlocks (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
    (fun i j => if exampleCore i j then -1 else 1)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked_gram : ∀ i j, (∑ k, signedExample i k * signedExample j k) =
    (if i=j then 16 else 0) := by decide
theorem exampleGram : extremalGram exampleCore := by
  have he (i j : Unit ⊕ Fin 15) : border 1 (signCore exampleCore) i j = (signedExample i j : ℝ) := by
    cases i <;> cases j <;> simp [border,signedExample,signCore,fromBlocks]
  ext i j
  simp only [mul_apply,transpose_apply,he,Matrix.smul_apply,smul_eq_mul,one_apply]
  have hh := checked_gram i j
  by_cases hij : i=j
  · simp only [if_pos hij,mul_one] at hh ⊢
    exact_mod_cast hh
  · simp only [if_neg hij,mul_zero] at hh ⊢
    exact_mod_cast hh
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def flipTest {n : ℕ} (a : Matrix (Fin n) (Fin n) Bool) : Bool :=
  (List.finRange n).any fun i => (List.finRange n).all fun j =>
    decide (i=j) || (List.finRange n).any fun k => (List.finRange n).all fun c =>
      (xor (a i c) (a j c) == a k c)
private theorem flipTest_correct {n : ℕ} (a : Matrix (Fin n) (Fin n) Bool) :
    flipTest a = true ↔ rowFlip a := by
  simp [flipTest,rowFlip,or_iff_not_imp_left,ne_comm]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem example_asymmetric : ¬ symmetrizable exampleCore := by
  have hr : rowFlip exampleCore := (flipTest_correct _).mp (by decide)
  have hc : ¬rowFlip exampleCoreᵀ := fun h =>
    (show flipTest exampleCoreᵀ ≠ true by decide) ((flipTest_correct _).mpr h)
  exact fun h => hc (rowFlip_transpose hr h)
end OMA.S_mo_266203

open OMA.S_mo_266203
open Matrix

theorem OMA.solution : type_of% @OMA.S_mo_266203.main := by
  refine ⟨fun n hn a ha => ⟨formula hn a ha,generic_optimum hn a ha⟩,exampleCore,exampleGram,example_asymmetric,?_⟩
  intro x hx
  rw [formula (by decide) exampleCore exampleGram x hx]
  have hs : (border 1 (signCore exampleCore)).det^2 = 16^16 :=
    (det_bound exampleCore).2.mpr exampleGram
  have ha : |(border 1 (signCore exampleCore)).det| = 4294967296 := by
    nlinarith [sq_abs (border 1 (signCore exampleCore)).det,abs_nonneg (border 1 (signCore exampleCore)).det]
  rw [ha]
  norm_num
  ring
