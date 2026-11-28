import OMAStatements.S_mo_210790

namespace OMA.S_mo_210790
open Finset
private def coin (b : Bool) : ℝ := if b then 1 else -1
private def row {n : ℕ} (a : Fin n → ℝ) (ε : Fin n → Bool) : ℝ := ∑ j, a j * coin (ε j)
private lemma cube_split {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    ∑ ε, f ε = (∑ ε : Fin n → Bool, f (Fin.cons true ε)) +
      ∑ ε : Fin n → Bool, f (Fin.cons false ε) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f,
    Fintype.sum_prod_type,Fintype.sum_bool]
  rfl
private lemma row_cons {n : ℕ} (a : Fin (n+1) → ℝ) (b : Bool) (ε : Fin n → Bool) :
    row a (Fin.cons b ε) = a 0 * coin b + row (fun i => a i.succ) ε := by
  simp [row,Fin.sum_univ_succ]
private lemma coin_moments (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, a i=1 ∨ a i= -1) (z : ℝ) :
    (∑ ε, (z+row a ε)^2) = 2^n * (z^2+n) ∧
    (∑ ε, (z+row a ε)^4) = 2^n * (z^4 + 6*n*z^2 + 3*(n:ℝ)^2 - 2*n) := by
  induction n generalizing z with
  | zero => simp [row]
  | succ n ih =>
    have ih' := ih (a := fun i => a i.succ) (fun i => ha i.succ)
    rw [cube_split,cube_split (fun ε => (z+row a ε)^4)]
    simp only [row_cons,coin,ite_true,ite_false,Bool.false_eq_true,mul_one,mul_neg,
      ← add_assoc]
    rw [(ih' (z+a 0)).1,(ih' (z+ -(a 0))).1,
      (ih' (z+a 0)).2,(ih' (z+ -(a 0))).2]
    rcases ha 0 with h|h <;> rw [h] <;> push_cast <;> rw [pow_succ] <;> constructor <;> ring
private lemma row_abs {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, a i=1 ∨ a i= -1) :
    2^n * (Real.sqrt n / 2) ≤ ∑ ε, |row a ε| := by
  by_cases hn : n=0
  · subst n
    simp [row]
  let s := Real.sqrt (n:ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have hs2 : s^2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hpoint (t : ℝ) : 12*s^2*t^2-t^4 ≤ 16*s^3*|t| := by
    have h := mul_nonneg (mul_nonneg (abs_nonneg t) (sq_nonneg (|t|-2*s)))
      (show 0 ≤ |t|+4*s by positivity)
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht] at h ⊢
      linarith
    · rw [abs_of_neg (lt_of_not_ge ht)] at h ⊢
      linarith
  have hall := Finset.sum_le_sum (s := (univ:Finset (Fin n → Bool))) (fun ε _ => hpoint (row a ε))
  simp only [sum_sub_distrib,←mul_sum] at hall
  obtain ⟨h2,h4⟩ := coin_moments n a ha 0
  norm_num at h2 h4
  rw [h2,h4,←hs2] at hall
  change 2^n*(s/2) ≤ _
  apply le_of_mul_le_mul_left (a := 16*s^3) _ (by positivity)
  calc 16*s^3*(2^n*(s/2)) ≤ 12*s^2*(2^n*s^2)-2^n*(3*(s^2)^2-2*s^2) := by
         have : 0 ≤ (2:ℝ)^n*s^4+2*(2:ℝ)^n*s^2 := by positivity
         linarith
       _ ≤ _ := hall
lemma sign_lower {n : ℕ} (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j=1 ∨ A i j= -1) :
    ∃ x y : Fin n → ℝ, (∀ i, x i=1 ∨ x i= -1) ∧ (∀ j, y j=1 ∨ y j= -1) ∧
      (n:ℝ)*Real.sqrt n/2 ≤ ∑ i,∑ j,x i*A i j*y j := by
  have hall := Finset.sum_le_sum (s := (univ:Finset (Fin n))) (fun i _ => row_abs (A i) (hA i))
  rw [Finset.sum_comm] at hall
  have h' : ∑ _ : Fin n → Bool, ((n:ℝ)*Real.sqrt n/2) ≤ ∑ ε,∑ i,|row (A i) ε| := by
    simpa [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using hall
  obtain ⟨ε,_,he⟩ := Finset.exists_le_of_sum_le univ_nonempty h'
  let x (i : Fin n) : ℝ := if 0 ≤ row (A i) ε then 1 else -1
  refine ⟨x,fun j => coin (ε j),fun i => ?_,fun j => ?_,he.trans_eq ?_⟩
  · dsimp [x]
    split <;> simp
  · change coin (ε j)=1 ∨ coin (ε j)= -1
    cases h : ε j <;> simp [coin]
  · apply sum_congr rfl
    intro i _
    simp_rw [mul_assoc]
    rw [← mul_sum]
    change |row (A i) ε|=x i*row (A i) ε
    by_cases hi : 0 ≤ row (A i) ε <;> simp [x,hi,abs_of_nonneg,abs_of_neg,lt_of_not_ge]
end OMA.S_mo_210790

namespace OMA.S_mo_210790
open Matrix
private lemma split_sign {n : ℕ} (x : V n) (hx : ∀ i,sign (x i)) :
    ∃ p q : V n, cube p ∧ cube q ∧ x=p-q := by
  let p (i : Fin n) : ℝ := if x i=1 then 1 else 0
  let q (i : Fin n) : ℝ := if x i=1 then 0 else 1
  refine ⟨p,q,fun i => ?_,fun i => ?_,?_⟩
  · by_cases h:x i=1 <;> simp [p,h]
  · by_cases h:x i=1 <;> simp [q,h]
  · funext i
    rcases hx i with h|h <;> norm_num [p,q,h]
lemma universal_bound {n : ℕ} (f : Form n) (d : ℝ)
    (hd : ∀ x y : V n,cube x → cube y → |value f x y|≤d)
    (h : ∃ x y : V n, (∀ i,sign (x i)) ∧ (∀ i,sign (y i)) ∧
      (n:ℝ)*Real.sqrt n/2 ≤ ∑ i,∑ j,x i*f.cross i j*y j) :
    (n:ℝ)*Real.sqrt n ≤ 8*d := by
  obtain ⟨x,y,hx,hy,hxy⟩ := h
  obtain ⟨a,b,ha,hb,rfl⟩ := split_sign x hx
  obtain ⟨c,e,hc,he,rfl⟩ := split_sign y hy
  have crossEq (x y : V n) : (∑ i,∑ j,x i*f.cross i j*y j) = x ⬝ᵥ (f.cross *ᵥ y) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
  rw [crossEq] at hxy
  have hid : (a-b) ⬝ᵥ (f.cross *ᵥ (c-e)) = value f a c-value f a e-value f b c+value f b e := by
    simp only [value,sub_dotProduct,mulVec_sub,dotProduct_sub]
    ring
  rw [hid] at hxy
  linarith [(abs_le.mp (hd a c ha hc)).2,(abs_le.mp (hd a e ha he)).1,
    (abs_le.mp (hd b c hb hc)).1,(abs_le.mp (hd b e hb he)).2]
lemma evaluated_entry {n : ℕ} (f : Form n) (i j : Fin n) :
    evaluated f i j=f.leftSq i+f.rightSq j+f.cross i j := by
  have evalPure (M : Sq n) (d : V n) (k : Fin n) : pureForm M d (Pi.single k 1)=d k := by
    simp only [pureForm,mulVec_single_one,single_one_dotProduct,Matrix.col_apply]
    simp [Pi.single_apply,mul_ite]
  change value f _ _=_
  rw [value,evalPure,evalPure,mulVec_single_one,single_one_dotProduct]
  rfl
end OMA.S_mo_210790

namespace OMA.S_mo_210790
open Matrix
open scoped Kronecker
private lemma had_sym (k : ℕ) : ∃ H : Sq (2^k), H.IsHadamard ∧ H.IsSymm := by
  classical
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]
  have hb : B.IsHadamard := by
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [B,unitary]
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [B,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [B,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  have hs : B.IsSymm := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  induction k with
  | zero =>
    change ∃ H : Sq 1,H.IsHadamard ∧ H.IsSymm
    refine ⟨(1 : Sq 1),⟨?_,?_,?_⟩,Matrix.isSymm_one⟩
    · intro i j
      have h : i=j := Subsingleton.elim _ _
      change (1 : Matrix (Fin 1) (Fin 1) ℝ) i j ∈ unitary ℝ
      rw [Matrix.one_apply,if_pos h]
      exact one_mem _
    · simp
    · simp
  | succ k ih =>
    obtain ⟨A,hA,hAs⟩ := ih
    let e : Fin (2^k) × Fin 2 ≃ Fin (2^(k+1)) := finProdFinEquiv.trans (finCongr (pow_succ 2 k).symm)
    refine ⟨Matrix.reindex e e (A ⊗ₖ B),(hA.kronecker hb).reindex e e,?_⟩
    ext i j
    change A (e.symm j).1 (e.symm i).1 * B (e.symm j).2 (e.symm i).2 =
      A (e.symm i).1 (e.symm j).1 * B (e.symm i).2 (e.symm j).2
    rw [hAs.apply,hs.apply]
private lemma had_sign {n : ℕ} {H : Sq n} (h : H.IsHadamard) (i j : Fin n) : sign (H i j) := by
  have e := (h.apply_mem i j).1
  simp only [star_trivial] at e
  exact sq_eq_one_iff.mp (by simpa [pow_two] using e)
end OMA.S_mo_210790

namespace OMA.S_mo_210790
open Matrix
private lemma cube_sq_le {n : ℕ} (x : V n) (hx : cube x) : ∑ i,x i^2 ≤ (n:ℝ) := by
  calc _ ≤ ∑ _ : Fin n,(1:ℝ) := Finset.sum_le_sum fun i _ => by rcases hx i with h|h <;> norm_num [h]
       _ = _ := by simp
private lemma had_energy {n : ℕ} {H : Sq n} (h : H.IsHadamard) (y : V n) :
    ∑ i,((H *ᵥ y) i)^2 = (n:ℝ) * ∑ i,(y i)^2 := by
  have hh : Hᵀ*H=(n:ℝ) • 1 := by simpa [conjTranspose_eq_transpose_of_trivial] using h.conjTranspose_mul
  have v := dotProduct_transpose_mulVec H y (H *ᵥ y)
  rw [mulVec_mulVec,hh,smul_mulVec,one_mulVec,dotProduct_smul] at v
  simpa only [dotProduct,←pow_two,smul_eq_mul] using v.symm
private lemma had_bilin {n : ℕ} {H : Sq n} (h : H.IsHadamard) {x y : V n} (hx : cube x) (hy : cube y) :
    |x ⬝ᵥ (H *ᵥ y)| ≤ (n:ℝ)*Real.sqrt n := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (H *ᵥ y)
  rw [had_energy h] at hCS
  have hupper := mul_le_mul (cube_sq_le x hx) (mul_le_mul_of_nonneg_left (cube_sq_le y hy) (Nat.cast_nonneg n))
    (mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg fun i _ => sq_nonneg (y i))) (Nat.cast_nonneg n)
  apply abs_le_of_sq_le_sq _ (by positivity)
  change (∑ i,x i*(H *ᵥ y) i)^2 ≤ _
  calc _ ≤ _ := hCS.trans hupper
       _ = _ := by rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]; ring
private lemma diag_bound {n : ℕ} (d x : V n) (hd : ∀ i,|d i| ≤ 1) (hx : cube x) :
    |∑ i,d i*x i^2| ≤ (n:ℝ) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (g:=fun _ : Fin n => (1:ℝ)) (fun i _ => ?_)).trans (by simp)
  rcases hx i with e|e
  · simp [e]
  · simpa [e] using hd i
private lemma pure_bound {n : ℕ} {H : Sq n} (h : H.IsHadamard) {d x : V n}
    (hd : ∀ i,|d i| ≤ 1) (hx : cube x) :
    |pureForm H d x| ≤ ((n:ℝ)*Real.sqrt n + n)/2+n := by
  have hh := had_bilin h hx hx
  have he := diag_bound (fun i => H i i) x (fun i => by rcases had_sign h i i with v|v <;> norm_num [v]) hx
  have hf := diag_bound d x hd hx
  rw [pureForm]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hh).1,(abs_le.mp hh).2,(abs_le.mp he).1,(abs_le.mp he).2,
    (abs_le.mp hf).1,(abs_le.mp hf).2]
end OMA.S_mo_210790

namespace OMA.S_mo_210790
open Matrix
lemma optimal_examples (k : ℕ) (s : ℝ) (hs : s=0 ∨ s=1) :
    ∃ f : Form (2^k), admissible f ∧
      (∀ i,f.leftSq i=s ∧ f.rightSq i= -s) ∧
      (evaluated f).rank=2^k ∧
      ∀ x y,cube x → cube y → |value f x y| ≤ 5*(2^k : ℕ)*Real.sqrt (2^k : ℕ) := by
  let n := 2^k
  have hn : 0 < n := pow_pos (by decide : 0<2) k
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  obtain ⟨H,hH,hS⟩ := had_sym k
  let f : Form n := ⟨H,H,H,fun _ => s,fun _ => -s⟩
  have hE : evaluated f=H := by
    ext i j
    rw [evaluated_entry]
    change s + -s + H i j=H i j
    ring
  refine ⟨f,⟨hS,hS,fun i j _ => ⟨had_sign hH i j,had_sign hH i j⟩,had_sign hH,?_⟩,
    fun i => ⟨rfl,rfl⟩,?_,?_⟩
  · rcases hs with h|h
    · right; intro i; simp [f,h]
    · left; intro i; simp [f,h,sign]
  · rw [hE]
    have hdet := hH.det_ne_zero (by simp)
    simpa using H.rank_of_isUnit (H.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  · intro x y hx hy
    have hp : ∀ i : Fin n,|s|≤1 := fun _ => by rcases hs with h|h <;> norm_num [h]
    have hq : ∀ i : Fin n,|-s|≤1 := fun i => by simpa using hp i
    have hl := pure_bound hH hp hx
    have hr := pure_bound hH hq hy
    have hb := had_bilin hH hx hy
    have ht : (n:ℝ)≤(n:ℝ)*Real.sqrt n := by
      have hroot : (1:ℝ) ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn'
      simpa using mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg n)
    change |pureForm H (fun _ => s) x + pureForm H (fun _ => -s) y + x ⬝ᵥ (H *ᵥ y)| ≤
        5*(n:ℝ)*Real.sqrt n
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hl).1,(abs_le.mp hl).2,(abs_le.mp hr).1,(abs_le.mp hr).2,
      (abs_le.mp hb).1,(abs_le.mp hb).2]
end OMA.S_mo_210790

open OMA.S_mo_210790
theorem OMA.solution : type_of% @OMA.S_mo_210790.main := by
  refine ⟨fun _ => evaluated_entry,?_,optimal_examples⟩
  intro n f hf d hd
  have h := universal_bound f d hd (sign_lower f.cross hf.2.2.2.1)
  have hr : ((evaluated f).rank:ℝ) ≤ n := by
    exact_mod_cast (show (evaluated f).rank ≤ n by simpa using (evaluated f).rank_le_card_width)
  exact ⟨h,(mul_le_mul hr (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (Nat.cast_nonneg n)).trans h⟩
