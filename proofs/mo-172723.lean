import OMAStatements.S_mo_172723
import Mathlib

/-!
Swap the first coordinate with the uniform unit vector on the remaining square
number of coordinates. A block has an absolute cube score bounded uniformly
below, although every entry in its first row tends to zero. Taking sufficiently
many independent blocks disproves the proposed polynomial diagonal bound.
This uses the average absolute product in Scott Aaronson’s original question
(https://mathoverflow.net/q/172723).
-/
open scoped BigOperators Matrix
open Matrix Finset
noncomputable section
namespace CubeWitness

def sign (b : Bool) : ℝ := if b then 1 else -1

lemma sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]

def total {m : ℕ} (x : Fin m → Bool) : ℝ := ∑ i, sign (x i)

private lemma splitMean (m : ℕ) (f : ℝ → ℝ) :
    (𝔼 x : Fin (m+1) → Bool, f (total x)) =
      𝔼 z : Fin m → Bool, (f (total z + 1) + f (total z - 1))/2 := by
  let e := Fin.consEquiv (fun _ : Fin (m+1) => Bool)
  calc
    _ = 𝔼 p : Bool × (Fin m → Bool), f (total (e p)) :=
      (Fintype.expect_equiv e _ _ (fun _ => rfl)).symm
    _ = 𝔼 z : Fin m → Bool, 𝔼 b : Bool, f (total (Fin.cons b z)) := by
      rw [← Finset.expect_comm, ← Finset.expect_product']; rfl
    _ = _ := by
      apply Finset.expect_congr rfl
      intro z _
      simp [Finset.expect, NNRat.smul_def, total, Fin.sum_univ_succ, sign,
        add_comm, sub_eq_add_neg]
      ring

/-- Second and fourth moments of a sum of independent uniform signs. -/
lemma moments (m : ℕ) :
    (𝔼 x : Fin m → Bool, (total x)^2) = m ∧
    (𝔼 x : Fin m → Bool, (total x)^4) = 3*(m:ℝ)^2-2*m := by
  induction m with
  | zero => simp [total]
  | succ m ih =>
    constructor
    · rw [splitMean m (fun t => t^2)]
      simp_rw [show ∀ t : ℝ, ((t+1)^2+(t-1)^2)/2=t^2+1 by intro t; ring]
      rw [Finset.expect_add_distrib, ih.1, Fintype.expect_const]; push_cast; ring
    · rw [splitMean m (fun t => t^4)]
      simp_rw [show ∀ t : ℝ, ((t+1)^4+(t-1)^4)/2=t^4+6*t^2+1 by intro t; ring]
      rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
        ih.1, ih.2, Fintype.expect_const]; push_cast; ring

abbrev Size (a : ℕ) := Fin (a^2+1)
def direction (a : ℕ) : Size a → ℝ := Fin.cons 1 (fun _ => -(a:ℝ)⁻¹)

/-- The reflection across the hyperplane perpendicular to the difference
of the distinguished basis vector and the uniform unit vector. -/
def block (a : ℕ) : Matrix (Size a) (Size a) ℝ :=
  1 - Matrix.vecMulVec (direction a) (direction a)

lemma orth (a : ℕ) (ha : 0 < a) : (block a).transpose * block a = 1 := by
  have hd : direction a ⬝ᵥ direction a = 2 := by
    simp [dotProduct, Fin.sum_univ_succ, direction]
    field_simp; ring
  rw [block, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_vecMulVec,
    sub_mul]
  simp only [mul_sub, one_mul, mul_one, Matrix.vecMulVec_mul_vecMulVec, hd]
  ext i j
  simp [Matrix.vecMulVec_apply]
  ring

lemma blockEntry (a : ℕ) (ha : 1 ≤ a) (i j : Size a) : |block a i j| ≤ 1 := by
  have h : (1:ℝ) ≤ a := by exact_mod_cast ha
  have lo : (0:ℝ) ≤ (a:ℝ)⁻¹ := by positivity
  have hi : (a:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 h
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [block, direction, Matrix.one_apply, Matrix.vecMulVec_apply, abs_le, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _)] <;>
    (try split_ifs) <;> (try constructor) <;> nlinarith [mul_nonneg lo (sub_nonneg.mpr hi), sq_nonneg ((a:ℝ)⁻¹)]
lemma centerEntry (a : ℕ) (j : Size a) : |block a 0 j| ≤ (a:ℝ)⁻¹ := by
  cases j using Fin.cases <;> simp [block, direction, Matrix.vecMulVec_apply, Ne.symm (Fin.succ_ne_zero _)]

lemma action (a : ℕ) (b : Bool) (x : Fin (a^2) → Bool) :
    (block a).mulVec (fun i => sign (Fin.cons (α := fun _ => Bool) b x i)) =
      Fin.cons (α := fun _ => ℝ) (total x / a) (fun i => sign (x i) + (sign b - total x / a)/a) := by
  let v := fun i : Size a => sign (Fin.cons (α := fun _ => Bool) b x i)
  have hd : direction a ⬝ᵥ v = sign b - total x / a := by
    simp [dotProduct, direction, Fin.sum_univ_succ, v, total, ← Finset.mul_sum, div_eq_mul_inv]
    ring
  change (block a).mulVec v = _
  rw [block, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, hd]
  funext i
  cases i using Fin.cases
  all_goals simp [direction, v, div_eq_mul_inv]
  all_goals ring

private lemma expLower {s : ℝ} (hs : |s| ≤ 1/2) :
    Real.exp (s - 2*s^2) ≤ 1+s := by
  have h := abs_le.mp hs
  have hpos : 0 < 1+s := by linarith
  apply (Real.le_log_iff_exp_le hpos).1
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos hpos)
  have hdiv : (1:ℝ)/(1+s) ≤ 1-(s-2*s^2) := (div_le_iff₀ hpos).2 (by
    nlinarith [mul_nonneg (sq_nonneg s) (show 0 ≤ 1+2*s by linarith)])
  rw [one_div] at hdiv
  linarith

def sample (a : ℕ) (b : Bool) (x : Fin (a^2) → Bool) : ℝ :=
  let y := total x / a
  |y| * ∏ i, |sign (x i) + (sign b-y)/a|

/-- This polynomial is positive only for moderate values of the normalized
sign sum. Its expectation is bounded below by the moment identities. -/
def weight (y : ℝ) : ℝ := y^2 - 1/4 - y^4/16

private lemma sampleLower (a : ℕ) (ha : 10 ≤ a) (b : Bool) (x : Fin (a^2) → Bool) :
    (Real.exp (-70)/32) * weight (total x / a) ≤ sample a b x := by
  let y := total x / a
  let t := (sign b-y)/a
  have ha' : (10:ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0:ℝ) < a := by linarith
  have hsign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
  have hyid : total x = (a:ℝ)*y := by dsimp [y]; field_simp
  change (Real.exp (-70)/32)*weight y ≤ |y| *∏ i, |sign (x i)+t|
  by_cases hw : weight y ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hw).trans (by positivity)
  have hy2 : (1/4:ℝ) ≤ y^2 := by dsimp [weight] at hw; nlinarith [sq_nonneg (y^2)]
  have hy4 : y^2 ≤ 16 := by
    by_contra! h
    dsimp [weight] at hw
    nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr h.le)]
  have hylo : 1/2 ≤ |y| := by nlinarith [sq_abs y, abs_nonneg y]
  have hyhi : |y| ≤ 4 := by nlinarith [sq_abs y, abs_nonneg y]
  have hc : |sign b-y| ≤ 5 := by calc
    _ ≤ |sign b|+|y| := abs_sub _ _
    _ ≤ _ := by rw [hsign]; linarith
  have ht : |t| ≤ 1/2 := by
    rw [show |t|=|sign b-y|/a by simp [t, abs_div], div_le_iff₀ ha0]; linarith
  have htot : -70 ≤ ∑ i, (sign (x i)*t - 2*(sign (x i)*t)^2) := by
    simp only [mul_pow, sign_sq, one_mul, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    change -70 ≤ total x * t - (a:ℝ)^2 * 2 * t^2
    have ht' : (a:ℝ)*t = sign b-y := by dsimp [t]; field_simp
    have he : total x*t - (a:ℝ)^2*2*t^2 = y*(sign b-y)-2*(sign b-y)^2 := by
      rw [hyid, ← ht']; ring
    rw [he]
    have hsq : (sign b-y)^2 ≤ 25 := by nlinarith [sq_abs (sign b-y), abs_nonneg (sign b-y)]
    have hp : |y*(sign b-y)| ≤ 20 := by rw [abs_mul]; linarith [mul_le_mul hyhi hc (abs_nonneg _) (by norm_num)]
    nlinarith [(abs_le.mp hp).1]
  have hprod : Real.exp (-70) ≤ ∏ i, |sign (x i)+t| := by
    apply (Real.exp_le_exp.mpr htot).trans
    rw [Real.exp_sum]
    apply Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
    intro i _
    apply (expLower (s := sign (x i)*t) (by simpa [abs_mul, hsign] using ht)).trans
    cases e : x i <;> simp [sign] <;> rw [abs_le] at ht <;> grind [le_abs_self, neg_le_abs]
  have hh := mul_le_mul hylo hprod (Real.exp_pos _).le (abs_nonneg y)
  have hwmax : weight y ≤ 16 := by dsimp [weight]; nlinarith [sq_nonneg (y^2)]
  exact (show (Real.exp (-70)/32)*weight y ≤ (1/2)*Real.exp (-70) by
    nlinarith [mul_nonneg (Real.exp_pos (-70)).le (sub_nonneg.mpr hwmax)]).trans hh

lemma meanSample (a : ℕ) (ha : 10 ≤ a) (b : Bool) :
    Real.exp (-70)/64 ≤ 𝔼 x, sample a b x := by
  have hA : (0:ℝ) < a := by exact_mod_cast (show 0<a by omega)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun x _ => sampleLower a ha b x)
  have h2 : (𝔼 x : Fin (a^2) → Bool, (total x / a)^2) = 1 := by
    simp only [div_eq_mul_inv, mul_pow, ← Finset.expect_mul, (moments (a^2)).1, Nat.cast_pow]
    field_simp
  have h4 : (𝔼 x : Fin (a^2) → Bool, (total x / a)^4) ≤ 3 := by
    simp only [div_eq_mul_inv, mul_pow, ← Finset.expect_mul, (moments (a^2)).2, Nat.cast_pow]
    field_simp
    nlinarith [sq_nonneg (a:ℝ)]
  simp only [weight, ← Finset.mul_expect, Finset.expect_sub_distrib, Fintype.expect_const,
    ← Finset.expect_div, h2] at h
  apply le_trans _ h
  nlinarith [mul_nonneg (Real.exp_pos (-70)).le (sub_nonneg.mpr h4), Real.exp_pos (-70)]

def score {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℝ) : ℝ :=
  𝔼 x : I → Bool, |∏ i, (M *ᵥ (sign ∘ x)) i|

lemma meanProd {I : Type} [Fintype I] (k : ℕ) (g : I → ℝ) :
    (𝔼 x : Fin k → I, ∏ j, g (x j)) = (𝔼 y, g y)^k := by
  classical
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.prod_sum]
  simp [div_pow]

/-- Independence makes the absolute cube score multiplicative across blocks. -/
lemma blockScore {I : Type} [Fintype I] [DecidableEq I] (k : ℕ) (M : Matrix I I ℝ) :
    score (blockDiagonal (fun _ : Fin k => M)) = (score M)^k := by
  classical
  let e : (Fin k → I → Bool) ≃ (I × Fin k → Bool) :=
    ⟨fun x i => x i.2 i.1, fun x j i => x (i,j), by intro; rfl, by intro; rfl⟩
  unfold score
  rw [←meanProd k (fun x : I → Bool => |∏ i, (M *ᵥ (sign ∘ x)) i|)]
  symm
  apply Fintype.expect_equiv e
  intro x
  have hrow (i : I) (j : Fin k) :
      (blockDiagonal (fun _ : Fin k => M) *ᵥ (sign ∘ e x)) (i,j) =
      (M *ᵥ (sign ∘ x j)) i := by
    simp [mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, e, ite_mul]
  rw [Fintype.prod_prod_type, Finset.prod_comm, Finset.abs_prod]
  simp_rw [hrow]

lemma scoreReindex {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (e : I ≃ J) (M : Matrix J J ℝ) :
    score (M.submatrix e e) = score M := by
  apply Fintype.expect_equiv (e.arrowCongr (Equiv.refl Bool))
  intro x
  rw [Matrix.submatrix_mulVec_equiv]
  congr 1
  exact e.prod_comp _

lemma pairOrth {I : Type} [Fintype I] [DecidableEq I] (k : ℕ) {M : Matrix I I ℝ}
    (h : M.transpose * M = 1) :
    (blockDiagonal (fun _ : Fin k => M)).transpose * blockDiagonal (fun _ : Fin k => M) = 1 := by
  rw [blockDiagonal_transpose, ←blockDiagonal_mul]
  simp_rw [h]
  ext ⟨i,j⟩ ⟨l,t⟩
  by_cases hj : j=t <;> by_cases hi : i=l <;> simp [blockDiagonal_apply, Matrix.one_apply, hj, hi]

/-- Every transversal uses one small entry from the distinguished row of each block. -/
lemma rowsBound (m k : ℕ) (M : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hc : ∀ j, |M 0 j| ≤ u) (hb : ∀ i j, |M i j| ≤ 1)
    (f : Fin (m+1) × Fin k → Fin (m+1) × Fin k) :
    |∏ i, blockDiagonal (fun _ : Fin k => M) i (f i)| ≤ u^k := by
  rw [Finset.abs_prod, Fintype.prod_prod_type, Finset.prod_comm]
  calc
    _ ≤ ∏ _j : Fin k, ∏ i : Fin (m+1), (if i=0 then u else 1) := by
      apply Finset.prod_le_prod (fun _ _ => Finset.prod_nonneg (fun _ _ => abs_nonneg _))
      intro j _
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro i _
      rw [blockDiagonal_apply]
      by_cases hj : j=(f (i,j)).2
      · rw [if_pos hj]
        split_ifs with h
        · simpa [h] using hc (f (i,j)).1
        · exact hb _ _
      · rw [if_neg hj, abs_zero]
        split_ifs <;> positivity
    _ = _ := by simp

lemma orthReindex {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (M : Matrix J J ℝ) (h : M.transpose * M = 1) :
    (M.submatrix e e).transpose * (M.submatrix e e) = 1 := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, h, Matrix.submatrix_one_equiv]


private lemma blockMean (a : ℕ) (ha : 10 ≤ a) : Real.exp (-70)/64 ≤ score (block a) := by
  let e := Fin.consEquiv (fun _ : Size a => Bool)
  have hs : score (block a) = 𝔼 p : Bool × (Fin (a^2) → Bool), sample a p.1 p.2 := by
    unfold score
    symm
    apply Fintype.expect_equiv e
    intro p
    change sample a p.1 p.2 = |∏ i, ((block a).mulVec (fun j => sign (Fin.cons (α := fun _ => Bool) p.1 p.2 j))) i|
    rw [action, Fin.prod_univ_succ]
    simp [sample, abs_mul, Finset.abs_prod]
  rw [hs]
  change _ ≤ 𝔼 p ∈ Finset.univ ×ˢ Finset.univ, sample a p.1 p.2
  rw [Finset.expect_product']
  exact (Fintype.expect_const (ι := Bool) (Real.exp (-70)/64)) ▸ Finset.expect_le_expect (fun b _ => meanSample a ha b)

private lemma concreteScore {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    OMA.S_mo_172723.cubeScore M = score M := by
  rw [score, Fintype.expect_eq_sum_div_card]
  simp [OMA.S_mo_172723.cubeScore, sign, Function.comp_def]

end CubeWitness
open CubeWitness

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_172723.main) := by
  classical
  intro claim
  obtain ⟨D, _, bound⟩ := claim 1 (by norm_num)
  obtain ⟨d, hd⟩ := exists_nat_ge D
  let k := 4*d+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  let c : ℝ := Real.exp (-70)/64
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨r, hr⟩ := exists_nat_ge (c^k)⁻¹
  let a := max 10 (max (2*k) r)
  have ha : 10 ≤ a := le_max_left ..
  have hka : 2*k ≤ a := (le_max_left ..).trans (le_max_right ..)
  have hra : r ≤ a := (le_max_right ..).trans (le_max_right ..)
  let n := (a^2+1)*k
  have ha1 : 1 < a := by omega
  have han : a ≤ n := by
    have hh : a ≤ a^2+1 := by nlinarith only [ha1]
    exact hh.trans (Nat.le_mul_of_pos_right _ hk)
  have hn : 2 ≤ n := by omega
  have hn4 : n ≤ a^4 := by
    have hp : 1 ≤ a^2 := Nat.one_le_pow 2 a (by omega)
    calc
      n ≤ (2*a^2)*k := Nat.mul_le_mul_right _ (by omega)
      _ = a^2*(2*k) := by ring
      _ ≤ a^2*a := Nat.mul_le_mul_left _ hka
      _ = a^3 := by ring
      _ ≤ a^4 := Nat.pow_le_pow_right (by omega) (by decide)
  let B := Matrix.blockDiagonal (fun _ : Fin k => block a)
  let e : Fin n ≃ Size a × Fin k := (Fintype.equivFinOfCardEq (by simp [Size, n])).symm
  let O := B.submatrix e e
  have ho : O.transpose * O = 1 := orthReindex e B (pairOrth k (orth a (by omega)))
  have hs : c^k ≤ OMA.S_mo_172723.cubeScore O := by
    rw [concreteScore, show score O = score B from scoreReindex e B, blockScore]
    exact pow_le_pow_left₀ hc.le (blockMean a ha) _
  have Hn : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have Ha : (1:ℝ)<a := by exact_mod_cast ha1
  have hscore : (n:ℝ)^(-(1:ℝ)) ≤ OMA.S_mo_172723.cubeScore O := by
    rw [Real.rpow_neg Hn.le, Real.rpow_one]
    apply le_trans _ hs
    apply (inv_le_comm₀ Hn (pow_pos hc _)).2
    exact hr.trans (by exact_mod_cast hra.trans han)
  obtain ⟨σ, hσ⟩ := bound n hn O ho hscore
  have Hrow : |∏ i, O i (σ i)| ≤ ((a:ℝ)⁻¹)^k := by
    have h := rowsBound (a^2) k (block a) (a:ℝ)⁻¹ (by positivity) (centerEntry a)
      (blockEntry a (by omega)) (fun z => e (σ (e.symm z)))
    simpa [O, B, Matrix.submatrix_apply, ← e.prod_comp] using h
  have hbase : (n:ℝ)^D < (a:ℝ)^k := by
    calc
      _ ≤ (n:ℝ)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n by omega)) hd
      _ = (n:ℝ)^d := Real.rpow_natCast ..
      _ ≤ ((a:ℝ)^4)^d := pow_le_pow_left₀ Hn.le (by exact_mod_cast hn4) _
      _ = (a:ℝ)^(4*d) := (pow_mul ..).symm
      _ < (a:ℝ)^k := pow_lt_pow_right₀ Ha (by dsimp [k]; omega)
  change (n:ℝ)^(-D) ≤ |∏ i, O i (σ i)| at hσ
  rw [Real.rpow_neg Hn.le] at hσ
  rw [inv_pow] at Hrow
  exact (not_le_of_gt ((inv_lt_inv₀ (pow_pos (by linarith : (0:ℝ)<a) k) (Real.rpow_pos_of_pos Hn D)).2 hbase)) (hσ.trans Hrow)
