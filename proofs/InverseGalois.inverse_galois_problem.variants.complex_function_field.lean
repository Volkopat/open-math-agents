import FormalConjectures.Wikipedia.InverseGalois

/-!
Proof of the Inverse Galois Problem over `K(t)` for any algebraically closed field `K`
of characteristic `0` (`InverseGalois.inverse_galois_problem.variants.complex_function_field`).
Strategy B: weighted `ℓ¹(ℤ, ℂ[G])` analytic patching + Cauchy polynomiality + `ACF_isComplete`.
-/

namespace StrategyBPart1a
open scoped BigOperators Topology NNReal ENNReal

/- Section 1: Group algebra `GroupAlg G` with `ℓ¹` norm -/

structure GroupAlg (G : Type) where
  coeff : G → ℂ

namespace GroupAlg

variable {G : Type}

lemma ext {a b : GroupAlg G} (h : ∀ x, a.coeff x = b.coeff x) : a = b := by
  cases a; cases b; congr; funext x; exact h x

instance : Zero (GroupAlg G) := ⟨⟨fun _ => 0⟩⟩
instance : Add (GroupAlg G) := ⟨fun a b => ⟨fun x => a.coeff x + b.coeff x⟩⟩
instance : Neg (GroupAlg G) := ⟨fun a => ⟨fun x => -a.coeff x⟩⟩
instance : Sub (GroupAlg G) := ⟨fun a b => ⟨fun x => a.coeff x - b.coeff x⟩⟩
instance : SMul ℂ (GroupAlg G) := ⟨fun c a => ⟨fun x => c * a.coeff x⟩⟩
instance : SMul ℝ (GroupAlg G) := ⟨fun c a => ⟨fun x => (c : ℂ) * a.coeff x⟩⟩

@[simp] lemma zero_coeff (x : G) : (0 : GroupAlg G).coeff x = 0 := rfl
@[simp] lemma add_coeff (a b : GroupAlg G) (x : G) : (a + b).coeff x = a.coeff x + b.coeff x := rfl
@[simp] lemma neg_coeff (a : GroupAlg G) (x : G) : (-a).coeff x = -a.coeff x := rfl
@[simp] lemma sub_coeff (a b : GroupAlg G) (x : G) : (a - b).coeff x = a.coeff x - b.coeff x := rfl
@[simp] lemma smul_coeff (c : ℂ) (a : GroupAlg G) (x : G) : (c • a).coeff x = c * a.coeff x := rfl
@[simp] lemma rsmul_coeff (c : ℝ) (a : GroupAlg G) (x : G) :
    (c • a).coeff x = (c : ℂ) * a.coeff x := rfl

instance : AddCommGroup (GroupAlg G) where
  add_assoc a b c := ext fun x => add_assoc _ _ _
  zero_add a := ext fun x => zero_add _
  add_zero a := ext fun x => add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := ext fun x => neg_add_cancel _
  add_comm a b := ext fun x => add_comm _ _
  sub_eq_add_neg a b := ext fun x => sub_eq_add_neg _ _

instance : Module ℂ (GroupAlg G) where
  one_smul a := ext fun x => one_mul _
  mul_smul c d a := ext fun x => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add c a b := ext fun x => mul_add _ _ _
  add_smul c d a := ext fun x => add_mul _ _ _
  zero_smul a := ext fun x => zero_mul _

instance : Module ℝ (GroupAlg G) where
  one_smul a := ext fun x => by simp
  mul_smul c d a := ext fun x => by simp [mul_assoc]
  smul_zero _ := ext fun _ => by simp
  smul_add c a b := ext fun x => by simp [mul_add]
  add_smul c d a := ext fun x => by simp [add_mul]
  zero_smul a := ext fun x => by simp

instance : IsScalarTower ℝ ℂ (GroupAlg G) where
  smul_assoc r c a := ext fun x => by
    simp only [rsmul_coeff, smul_coeff, Algebra.smul_def, Complex.coe_algebraMap, mul_assoc]

lemma sum_coeff {ι : Type*} (s : Finset ι) (f : ι → GroupAlg G) (x : G) :
    (∑ i ∈ s, f i).coeff x = ∑ i ∈ s, (f i).coeff x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

section NormSection

variable [Fintype G]

noncomputable instance : Norm (GroupAlg G) := ⟨fun a => ∑ x : G, ‖a.coeff x‖⟩

lemma norm_def (a : GroupAlg G) : ‖a‖ = ∑ x : G, ‖a.coeff x‖ := rfl

noncomputable def normedCore : NormedSpace.Core ℂ (GroupAlg G) where
  norm_nonneg a := Finset.sum_nonneg fun _ _ => norm_nonneg _
  norm_eq_zero_iff a := by
    simp only [norm_def]
    constructor
    · intro h
      apply ext; intro x
      have hle := Finset.single_le_sum (f := fun y : G => ‖a.coeff y‖)
        (fun y _ => norm_nonneg _) (Finset.mem_univ x)
      rw [h] at hle
      exact norm_le_zero_iff.1 hle
    · rintro rfl; simp
  norm_smul c a := by
    simp only [norm_def, smul_coeff, norm_mul, ← Finset.mul_sum]
  norm_triangle a b := by
    simp only [norm_def, add_coeff]
    exact (Finset.sum_le_sum fun x _ => norm_add_le _ _).trans_eq Finset.sum_add_distrib

noncomputable instance : NormedAddCommGroup (GroupAlg G) :=
  NormedAddCommGroup.ofCore normedCore

noncomputable instance : NormedSpace ℂ (GroupAlg G) :=
  NormedSpace.ofCore normedCore

noncomputable instance : NormedSpace ℝ (GroupAlg G) where
  norm_smul_le c a := by
    change ∑ x : G, ‖(c : ℂ) * a.coeff x‖ ≤ ‖c‖ * ∑ x : G, ‖a.coeff x‖
    simp only [norm_mul, Complex.norm_real, ← Finset.mul_sum]
    exact le_rfl

lemma norm_coeff_le (a : GroupAlg G) (x : G) : ‖a.coeff x‖ ≤ ‖a‖ :=
  Finset.single_le_sum (f := fun y : G => ‖a.coeff y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ x)

def toFunLinearEquiv : GroupAlg G ≃ₗ[ℂ] (G → ℂ) where
  toFun := GroupAlg.coeff
  invFun := GroupAlg.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : FiniteDimensional ℂ (GroupAlg G) :=
  FiniteDimensional.of_injective (toFunLinearEquiv (G := G)).toLinearMap
    (toFunLinearEquiv (G := G)).injective

instance : CompleteSpace (GroupAlg G) :=
  FiniteDimensional.complete ℂ (GroupAlg G)

def aug (c : GroupAlg G) : ℂ := ∑ x : G, c.coeff x

@[simp] lemma aug_zero : aug (0 : GroupAlg G) = 0 := by simp [aug]
@[simp] lemma aug_add (c d : GroupAlg G) : aug (c + d) = aug c + aug d := by
  simp [aug, Finset.sum_add_distrib]
@[simp] lemma aug_sub (c d : GroupAlg G) : aug (c - d) = aug c - aug d := by
  simp [aug, Finset.sum_sub_distrib]
@[simp] lemma aug_smul (a : ℂ) (c : GroupAlg G) : aug (a • c) = a * aug c := by
  simp [aug, Finset.mul_sum]
@[simp] lemma aug_rsmul (a : ℝ) (c : GroupAlg G) : aug (a • c) = (a : ℂ) * aug c := by
  simp [aug, Finset.mul_sum]

lemma aug_sum {ι : Type*} (s : Finset ι) (f : ι → GroupAlg G) :
    aug (∑ i ∈ s, f i) = ∑ i ∈ s, aug (f i) := by
  simp only [aug, sum_coeff]
  exact Finset.sum_comm

lemma norm_aug_le (c : GroupAlg G) : ‖aug c‖ ≤ ‖c‖ :=
  norm_sum_le _ _

end NormSection

section FiniteGroup

variable [Fintype G] [Group G] [DecidableEq G]

instance : One (GroupAlg G) := ⟨⟨fun x => if x = 1 then 1 else 0⟩⟩
instance : Mul (GroupAlg G) :=
  ⟨fun a b => ⟨fun w => ∑ y : G, a.coeff y * b.coeff (y⁻¹ * w)⟩⟩

@[simp] lemma one_coeff (x : G) : (1 : GroupAlg G).coeff x = if x = 1 then 1 else 0 := rfl
@[simp] lemma mul_coeff (a b : GroupAlg G) (w : G) :
    (a * b).coeff w = ∑ y : G, a.coeff y * b.coeff (y⁻¹ * w) := rfl

instance : Ring (GroupAlg G) where
  mul_assoc a b c := ext fun w => by
    simp only [mul_coeff, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ fun y => ?_
    simp [mul_assoc]
  one_mul a := ext fun w => by
    simp [mul_coeff]
  mul_one a := ext fun w => by
    simp only [mul_coeff, one_coeff, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single w]
    · simp
    · intro y _ hy; rw [if_neg]; intro h
      exact hy (inv_mul_eq_one.1 h)
    · intro h; exact absurd (Finset.mem_univ w) h
  left_distrib a b c := ext fun w => by
    simp only [mul_coeff, add_coeff, mul_add, Finset.sum_add_distrib]
  right_distrib a b c := ext fun w => by
    simp only [mul_coeff, add_coeff, add_mul, Finset.sum_add_distrib]
  zero_mul a := ext fun w => by simp [mul_coeff]
  mul_zero a := ext fun w => by simp [mul_coeff]

instance : IsScalarTower ℂ (GroupAlg G) (GroupAlg G) where
  smul_assoc c a b := ext fun w => by
    simp only [smul_eq_mul, smul_coeff, mul_coeff, Finset.mul_sum, mul_assoc]

instance : SMulCommClass ℂ (GroupAlg G) (GroupAlg G) where
  smul_comm c a b := ext fun w => by
    simp only [smul_eq_mul, smul_coeff, mul_coeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring

noncomputable instance : NormedRing (GroupAlg G) where
  dist_eq x y := NormedAddCommGroup.dist_eq x y
  norm_mul_le a b := by
    calc ‖a * b‖ = ∑ w : G, ‖∑ y : G, a.coeff y * b.coeff (y⁻¹ * w)‖ := rfl
      _ ≤ ∑ w : G, ∑ y : G, ‖a.coeff y‖ * ‖b.coeff (y⁻¹ * w)‖ :=
          Finset.sum_le_sum fun w _ => (norm_sum_le _ _).trans (by simp)
      _ = ∑ y : G, ‖a.coeff y‖ * ∑ w : G, ‖b.coeff (y⁻¹ * w)‖ := by
          rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
      _ = ∑ y : G, ‖a.coeff y‖ * ∑ z : G, ‖b.coeff z‖ := by
          congr 1; ext y; congr 1
          exact Fintype.sum_equiv (Equiv.mulLeft y⁻¹) _ _ (fun _ => rfl)
      _ = ‖a‖ * ‖b‖ := (Finset.sum_mul _ _ _).symm

instance : NormOneClass (GroupAlg G) where
  norm_one := by
    change ∑ x : G, ‖(1 : GroupAlg G).coeff x‖ = 1
    simp only [one_coeff]
    rw [Finset.sum_eq_single (1 : G)]
    · simp
    · intro x _ hx; simp [hx]
    · intro h; exact absurd (Finset.mem_univ 1) h

def single (x : G) (a : ℂ) : GroupAlg G :=
  ⟨fun y => if y = x then a else 0⟩

@[simp] lemma single_coeff (x y : G) (a : ℂ) :
    (single x a).coeff y = if y = x then a else 0 := rfl

lemma norm_single (x : G) (a : ℂ) : ‖single x a‖ = ‖a‖ := by
  change ∑ y : G, ‖(single x a).coeff y‖ = ‖a‖
  simp only [single_coeff]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ x) h

@[simp] lemma aug_one : aug (1 : GroupAlg G) = 1 := by simp [aug]
@[simp] lemma aug_single (x : G) (a : ℂ) : aug (single x a) = a := by simp [aug, single_coeff]

lemma aug_mul (c d : GroupAlg G) : aug (c * d) = aug c * aug d := by
  simp only [aug, mul_coeff]
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft y⁻¹) _ _ fun _ => rfl

-- Right-convolution action on (G → ℂ) and left-permutation action rho
def convAct (c : GroupAlg G) (v : G → ℂ) : G → ℂ :=
  fun x => ∑ y : G, c.coeff y * v (x * y)

def rho (g : G) (v : G → ℂ) : G → ℂ :=
  fun x => v (g⁻¹ * x)

lemma convAct_one (v : G → ℂ) : convAct (1 : GroupAlg G) v = v := by
  ext x; simp [convAct]

lemma convAct_mul (c d : GroupAlg G) (v : G → ℂ) :
    convAct (c * d) v = convAct c (convAct d v) := by
  ext x
  simp only [convAct, mul_coeff, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Fintype.sum_equiv (Equiv.mulLeft y⁻¹) _ _ fun w => ?_
  simp [mul_assoc]

lemma convAct_add (c d : GroupAlg G) (v : G → ℂ) :
    convAct (c + d) v = convAct c v + convAct d v := by
  ext x; simp [convAct, add_mul, Finset.sum_add_distrib]

lemma convAct_smul (a : ℂ) (c : GroupAlg G) (v : G → ℂ) :
    convAct (a • c) v = a • convAct c v := by
  ext x; simp [convAct, Finset.mul_sum, mul_assoc]

lemma convAct_sum {ι : Type*} (s : Finset ι) (f : ι → GroupAlg G) (v : G → ℂ) (x : G) :
    convAct (∑ i ∈ s, f i) v x = ∑ i ∈ s, convAct (f i) v x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [convAct]
  | insert a s ha ih => simp [Finset.sum_insert ha, convAct_add, ih]

lemma convAct_single (y : G) (a : ℂ) (v : G → ℂ) (x : G) :
    convAct (single y a) v x = a * v (x * y) := by
  simp [convAct, single_coeff]

lemma convAct_comm_rho (c : GroupAlg G) (g : G) (v : G → ℂ) :
    convAct c (rho g v) = rho g (convAct c v) := by
  ext x; simp [convAct, rho, mul_assoc]

lemma convAct_const_one (c : GroupAlg G) : convAct c (fun _ => 1) = fun _ => aug c := by
  ext x; simp [convAct, aug]

-- Primitive root of unity and orthogonal Fourier idempotents for g : G
noncomputable def zeta (g : G) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ))

lemma orderOf_pos_of_fintype (g : G) : 0 < orderOf g :=
  orderOf_pos g

lemma zeta_ne_zero (g : G) : zeta g ≠ 0 := Complex.exp_ne_zero _

lemma norm_zeta (g : G) : ‖zeta g‖ = 1 := by
  rw [zeta]
  have h : (2 * Real.pi * Complex.I / (orderOf g : ℂ)) =
      (((2 * Real.pi / (orderOf g : ℝ) : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma zeta_pow_orderOf (g : G) : zeta g ^ orderOf g = 1 := by
  rw [zeta, ← Complex.exp_nat_mul]
  have hn : (orderOf g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (orderOf_pos_of_fintype g).ne'
  have h : (orderOf g : ℂ) * (2 * Real.pi * Complex.I / (orderOf g : ℂ)) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [h, Complex.exp_two_pi_mul_I]

lemma zeta_zpow_ne_one (g : G) {k : ℤ} (hndvd : ¬ ((orderOf g : ℤ) ∣ k)) :
    zeta g ^ k ≠ 1 := by
  intro heq
  rw [zeta, ← Complex.exp_int_mul, Complex.exp_eq_one_iff] at heq
  rcases heq with ⟨m, hm⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hn : (orderOf g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (orderOf_pos_of_fintype g).ne'
  have h1 : (k : ℂ) = (m : ℂ) * (orderOf g : ℂ) := by
    have h2 : (k : ℂ) / (orderOf g : ℂ) * (2 * Real.pi * Complex.I) =
        (m : ℂ) * (2 * Real.pi * Complex.I) := by
      calc (k : ℂ) / (orderOf g : ℂ) * (2 * Real.pi * Complex.I)
          = (k : ℂ) * (2 * Real.pi * Complex.I / (orderOf g : ℂ)) := by ring
        _ = (m : ℂ) * (2 * Real.pi * Complex.I) := hm
    have h3 : (k : ℂ) / (orderOf g : ℂ) = (m : ℂ) := mul_right_cancel₀ hpi h2
    exact (div_eq_iff hn).1 h3
  have h4 : k = m * (orderOf g : ℤ) := by
    exact_mod_cast h1
  exact hndvd ⟨m, by rw [h4, mul_comm]⟩

lemma sum_zeta_zpow (g : G) (k : ℤ) :
    ∑ j : Fin (orderOf g), (zeta g ^ k) ^ j.1 =
      if (orderOf g : ℤ) ∣ k then (orderOf g : ℂ) else 0 := by
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have h1 : zeta g ^ ((orderOf g : ℤ) * m) = 1 := by
      rw [zpow_mul, zpow_natCast, zeta_pow_orderOf, one_zpow]
    simp [h1]
  · have hne : zeta g ^ k ≠ 1 := zeta_zpow_ne_one g hdvd
    have hgeom : (zeta g ^ k - 1) * ∑ j : Fin (orderOf g), (zeta g ^ k) ^ j.1 =
        (zeta g ^ k) ^ orderOf g - 1 := by
      rw [Fin.sum_univ_eq_sum_range, mul_comm, geom_sum_mul]
    have hpow : (zeta g ^ k) ^ orderOf g = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, zeta_pow_orderOf, one_zpow]
    rw [hpow, sub_self] at hgeom
    exact (mul_eq_zero.1 hgeom).resolve_left (sub_ne_zero.2 hne)

noncomputable def idem (g : G) (k : Fin (orderOf g)) : GroupAlg G :=
  ∑ j : Fin (orderOf g), single (g ^ j.1) ((orderOf g : ℂ)⁻¹ * (zeta g) ^ (k.1 * j.1))

lemma norm_idem_le (g : G) (k : Fin (orderOf g)) : ‖idem g k‖ ≤ 1 := by
  have hn : (0 : ℝ) < (orderOf g : ℝ) := Nat.cast_pos.2 (orderOf_pos_of_fintype g)
  calc ‖idem g k‖ ≤ ∑ j : Fin (orderOf g), ‖single (g ^ j.1) ((orderOf g : ℂ)⁻¹ * (zeta g) ^ (k.1 * j.1))‖ :=
        norm_sum_le _ _
    _ = ∑ _j : Fin (orderOf g), (orderOf g : ℝ)⁻¹ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_single, norm_mul, norm_inv, Complex.norm_natCast, norm_pow, norm_zeta, one_pow, mul_one]
    _ = 1 := by simp [hn.ne']

lemma sum_idem (g : G) : ∑ k : Fin (orderOf g), idem g k = 1 := by
  apply ext; intro x
  simp only [sum_coeff, idem, single_coeff]
  rw [Finset.sum_comm]
  have hterm : ∀ j : Fin (orderOf g),
      (∑ k : Fin (orderOf g), if x = g ^ j.1 then (orderOf g : ℂ)⁻¹ * zeta g ^ (k.1 * j.1) else 0) =
      if j.1 = 0 then (if x = 1 then 1 else 0) else 0 := by
    intro j
    by_cases hx : x = g ^ j.1
    · simp only [hx, ite_true, ← Finset.mul_sum]
      have hpow : ∀ k : Fin (orderOf g), zeta g ^ (k.1 * j.1) = (zeta g ^ (j.1 : ℤ)) ^ k.1 := by
        intro k; rw [zpow_natCast, ← pow_mul, mul_comm]
      simp_rw [hpow, sum_zeta_zpow]
      by_cases hj : j.1 = 0
      · simp only [hj, pow_zero, ite_true, Nat.cast_zero, dvd_zero]
        have hn : (orderOf g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (orderOf_pos_of_fintype g).ne'
        exact inv_mul_cancel₀ hn
      · have hndvd : ¬ ((orderOf g : ℤ) ∣ (j.1 : ℤ)) := by
          intro h; have hle := Int.le_of_dvd (by omega) h; omega
        simp [hj, hndvd]
    · simp only [hx, ite_false, Finset.sum_const_zero]
      by_cases hj : j.1 = 0
      · rw [if_pos hj, if_neg]
        rwa [hj, pow_zero] at hx
      · rw [if_neg hj]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (⟨0, orderOf_pos_of_fintype g⟩ : Fin (orderOf g))]
  · simp
  · intro j _ hj; rw [if_neg]; intro h0; exact hj (Fin.ext h0)
  · intro h; exact absurd (Finset.mem_univ _) h

lemma aug_idem (g : G) (k : Fin (orderOf g)) :
    aug (idem g k) = if k.1 = 0 then 1 else 0 := by
  simp only [idem, aug_sum, aug_single, ← Finset.mul_sum]
  have hpow : ∀ j : Fin (orderOf g), zeta g ^ (k.1 * j.1) = (zeta g ^ (k.1 : ℤ)) ^ j.1 := by
    intro j; rw [zpow_natCast, ← pow_mul]
  simp_rw [hpow, sum_zeta_zpow]
  by_cases hk : k.1 = 0
  · simp only [hk, ite_true, Nat.cast_zero, dvd_zero]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 (orderOf_pos_of_fintype g).ne')
  · have hndvd : ¬ ((orderOf g : ℤ) ∣ (k.1 : ℤ)) := by
      intro h; have hle := Int.le_of_dvd (by omega) h; omega
    simp [hk, hndvd]

lemma convAct_idem_mul_g (g : G) (k : Fin (orderOf g)) (v : G → ℂ) (x : G) :
    convAct (idem g k) v (x * g) =
      zeta g ^ (-(k.1 : ℤ)) * convAct (idem g k) v x := by
  let n := orderOf g
  have hn_pos : 0 < n := orderOf_pos_of_fintype g
  simp only [idem, convAct_sum, convAct_single]
  rw [Finset.mul_sum]
  let σ : Fin n ≃ Fin n := {
    toFun := fun j => ⟨(j.1 + 1) % n, Nat.mod_lt _ hn_pos⟩
    invFun := fun j => ⟨if j.1 = 0 then n - 1 else j.1 - 1, by split_ifs <;> omega⟩
    left_inv := fun j => by
      ext; dsimp only
      by_cases hj : j.1 + 1 < n
      · simp [Nat.mod_eq_of_lt hj]
      · have hjeq : j.1 + 1 = n := by omega
        simp [hjeq]; omega
    right_inv := fun j => by
      ext; dsimp only
      split_ifs with hj
      · have h1 : n - 1 + 1 = n := by omega
        rw [h1, Nat.mod_self, hj]
      · have h1 : j.1 - 1 + 1 = j.1 := by omega
        rw [h1, Nat.mod_eq_of_lt j.2]
  }
  refine Fintype.sum_equiv σ _ _ fun j => ?_
  have hpow_g : g * g ^ j.1 = g ^ (σ j).1 := by
    rw [← pow_succ']
    by_cases hj : j.1 + 1 < n
    · have h1 : (σ j).1 = j.1 + 1 := Nat.mod_eq_of_lt hj
      rw [h1]
    · have hjeq : j.1 + 1 = n := by omega
      have h1 : (σ j).1 = 0 := by show (j.1 + 1) % n = 0; rw [hjeq, Nat.mod_self]
      rw [h1, hjeq, pow_zero]
      exact pow_orderOf_eq_one g
  rw [mul_assoc x g (g ^ j.1), hpow_g]
  have hpow_z : zeta g ^ (k.1 * j.1) = zeta g ^ (-(k.1 : ℤ)) * zeta g ^ (k.1 * (σ j).1) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (zeta_ne_zero g)]
    by_cases hj : j.1 + 1 < n
    · have h1 : (σ j).1 = j.1 + 1 := Nat.mod_eq_of_lt hj
      rw [h1]; congr 1; push_cast; ring
    · have hjeq : j.1 + 1 = n := by omega
      have h1 : (σ j).1 = 0 := by show (j.1 + 1) % n = 0; rw [hjeq, Nat.mod_self]
      rw [h1, mul_zero, Nat.cast_zero, add_zero]
      have hdiff : -(k.1 : ℤ) = (k.1 * j.1 : ℕ) + (orderOf g : ℤ) * (-(k.1 : ℤ)) := by
        have hjeq' : (j.1 : ℤ) + 1 = (orderOf g : ℤ) := by exact_mod_cast hjeq
        push_cast; nlinarith
      have hzo : zeta g ^ (orderOf g : ℤ) = 1 := by rw [zpow_natCast]; exact zeta_pow_orderOf g
      rw [hdiff, zpow_add₀ (zeta_ne_zero g), zpow_mul, hzo, one_zpow, mul_one]
  calc (orderOf g : ℂ)⁻¹ * zeta g ^ (k.1 * j.1) * v (x * g ^ (σ j).1)
      = (orderOf g : ℂ)⁻¹ * (zeta g ^ (-(k.1 : ℤ)) * zeta g ^ (k.1 * (σ j).1)) * v (x * g ^ (σ j).1) := by
          rw [hpow_z]
    _ = zeta g ^ (-(k.1 : ℤ)) * ((orderOf g : ℂ)⁻¹ * zeta g ^ (k.1 * (σ j).1) * v (x * g ^ (σ j).1)) := by
          ring

lemma convAct_idem_mul_g_pow (g : G) (k : Fin (orderOf g)) (v : G → ℂ) (x : G) (m : ℕ) :
    convAct (idem g k) v (x * g ^ m) =
      zeta g ^ (-(k.1 * m : ℤ)) * convAct (idem g k) v x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, convAct_idem_mul_g, ih, ← mul_assoc, ← zpow_add₀ (zeta_ne_zero g)]
    congr 2; push_cast; ring

noncomputable def mElem (g : G) (φ : ℂ) : GroupAlg G :=
  ∑ k : Fin (orderOf g), φ ^ k.1 • idem g k

lemma aug_mElem (g : G) (φ : ℂ) : aug (mElem g φ) = 1 := by
  simp only [mElem, aug_sum, aug_smul, aug_idem]
  rw [Finset.sum_eq_single (⟨0, orderOf_pos_of_fintype g⟩ : Fin (orderOf g))]
  · simp
  · intro k _ hk; rw [if_neg (fun h0 => hk (Fin.ext h0)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def mulLoc (g : G) (u : ℂ) (v w : G → ℂ) : G → ℂ :=
  fun x => ∑ k : Fin (orderOf g), ∑ l : Fin (orderOf g),
    (if k.1 + l.1 < orderOf g then (1 : ℂ) else u) *
      convAct (idem g k) v x * convAct (idem g l) w x

lemma convAct_mElem_mulLoc (g : G) (φ : ℂ) (v w : G → ℂ) :
    convAct (mElem g φ) (mulLoc g (φ ^ orderOf g) v w) =
      fun x => convAct (mElem g φ) v x * convAct (mElem g φ) w x := by
  set n := orderOf g
  have hn_pos : 0 < n := orderOf_pos_of_fintype g
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn_pos.ne'
  ext x
  have hproj : ∀ (m k l : Fin n),
      convAct (idem g m) (fun y => convAct (idem g k) v y * convAct (idem g l) w y) x =
        (if (n : ℤ) ∣ ((m.1 : ℤ) - k.1 - l.1) then 1 else 0) *
          convAct (idem g k) v x * convAct (idem g l) w x := by
    intro m k l
    conv_lhs => rw [idem]; simp only [convAct_sum, convAct_single]
    have hstep : ∀ j : Fin n,
        (n : ℂ)⁻¹ * zeta g ^ (m.1 * j.1) *
          (convAct (idem g k) v (x * g ^ j.1) * convAct (idem g l) w (x * g ^ j.1)) =
        (n : ℂ)⁻¹ * ((zeta g ^ ((m.1 : ℤ) - k.1 - l.1)) ^ j.1 *
          (convAct (idem g k) v x * convAct (idem g l) w x)) := by
      intro j
      rw [convAct_idem_mul_g_pow, convAct_idem_mul_g_pow]
      have hz : zeta g ^ (m.1 * j.1) * (zeta g ^ (-(k.1 * j.1 : ℤ)) * zeta g ^ (-(l.1 * j.1 : ℤ))) =
          (zeta g ^ ((m.1 : ℤ) - k.1 - l.1)) ^ j.1 := by
        rw [← zpow_natCast, ← zpow_add₀ (zeta_ne_zero g), ← zpow_add₀ (zeta_ne_zero g),
          ← zpow_natCast, ← zpow_mul]
        congr 1; push_cast; ring
      calc (n : ℂ)⁻¹ * zeta g ^ (m.1 * j.1) *
              (zeta g ^ (-(k.1 * j.1 : ℤ)) * convAct (idem g k) v x *
                (zeta g ^ (-(l.1 * j.1 : ℤ)) * convAct (idem g l) w x))
          = (n : ℂ)⁻¹ * ((zeta g ^ (m.1 * j.1) * (zeta g ^ (-(k.1 * j.1 : ℤ)) * zeta g ^ (-(l.1 * j.1 : ℤ)))) *
              (convAct (idem g k) v x * convAct (idem g l) w x)) := by ring
        _ = _ := by rw [hz]
    rw [Finset.sum_congr rfl fun j _ => hstep j]
    rw [← Finset.mul_sum, ← Finset.sum_mul, sum_zeta_zpow]
    split_ifs with hdvd
    · rw [← mul_assoc, inv_mul_cancel₀ hn_ne, one_mul, one_mul]
    · simp
  simp only [mElem, convAct_sum, convAct_smul, Pi.smul_apply, smul_eq_mul]
  have hlin : ∀ (m : Fin n),
      convAct (idem g m) (mulLoc g (φ ^ n) v w) x =
        ∑ k : Fin n, ∑ l : Fin n,
          (if k.1 + l.1 < n then (1 : ℂ) else φ ^ n) *
            convAct (idem g m) (fun y => convAct (idem g k) v y * convAct (idem g l) w y) x := by
    intro m
    conv_lhs => rw [convAct]
    simp only [mulLoc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [convAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  simp_rw [hlin, hproj, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext k
    rw [Finset.sum_comm]
  have hinner : ∀ (k l : Fin n),
      (∑ m : Fin n, φ ^ m.1 * ((if k.1 + l.1 < n then (1 : ℂ) else φ ^ n) *
        ((if (n : ℤ) ∣ ((m.1 : ℤ) - k.1 - l.1) then (1 : ℂ) else 0) *
          convAct (idem g k) v x * convAct (idem g l) w x))) =
      (φ ^ k.1 * convAct (idem g k) v x) * (φ ^ l.1 * convAct (idem g l) w x) := by
    intro k l
    let m₀ : Fin n := ⟨(k.1 + l.1) % n, Nat.mod_lt _ hn_pos⟩
    rw [Finset.sum_eq_single m₀]
    · have hdvd : (n : ℤ) ∣ ((m₀.1 : ℤ) - k.1 - l.1) := by
        refine ⟨-(((k.1 + l.1) / n : ℕ) : ℤ), ?_⟩
        have hdiv := Nat.div_add_mod (k.1 + l.1) n
        have hdiv' : (n : ℤ) * (((k.1 + l.1) / n : ℕ) : ℤ) + (m₀.1 : ℤ) = (k.1 : ℤ) + (l.1 : ℤ) := by
          exact_mod_cast hdiv
        linarith
      rw [if_pos hdvd]
      have hpow : φ ^ m₀.1 * (if k.1 + l.1 < n then (1 : ℂ) else φ ^ n) = φ ^ k.1 * φ ^ l.1 := by
        rw [← pow_add]
        split_ifs with hlt
        · rw [mul_one]; congr 1; exact Nat.mod_eq_of_lt hlt
        · rw [← pow_add]; congr 1
          have hk := k.2; have hl := l.2
          have hq : (k.1 + l.1) / n = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
          have hdiv := Nat.div_add_mod (k.1 + l.1) n
          rw [hq, mul_one] at hdiv
          show (k.1 + l.1) % n + n = k.1 + l.1
          omega
      calc φ ^ m₀.1 * ((if k.1 + l.1 < n then (1 : ℂ) else φ ^ n) *
              (1 * convAct (idem g k) v x * convAct (idem g l) w x))
          = (φ ^ m₀.1 * (if k.1 + l.1 < n then (1 : ℂ) else φ ^ n)) *
              (convAct (idem g k) v x * convAct (idem g l) w x) := by ring
        _ = (φ ^ k.1 * φ ^ l.1) * (convAct (idem g k) v x * convAct (idem g l) w x) := by rw [hpow]
        _ = (φ ^ k.1 * convAct (idem g k) v x) * (φ ^ l.1 * convAct (idem g l) w x) := by ring
    · intro m _ hm
      have hndvd : ¬ ((n : ℤ) ∣ ((m.1 : ℤ) - k.1 - l.1)) := by
        rintro ⟨q, hq⟩
        apply hm; ext
        have h1 : (m.1 : ℤ) % (n : ℤ) = ((k.1 + l.1 : ℤ)) % (n : ℤ) := by
          have : (m.1 : ℤ) = (k.1 + l.1 : ℤ) + (n : ℤ) * q := by linarith
          rw [this, Int.add_mul_emod_self_left]
        have h2 : (m.1 : ℤ) % (n : ℤ) = (m.1 : ℤ) := Int.emod_eq_of_lt (by omega) (by exact_mod_cast m.2)
        have h3 : ((k.1 + l.1 : ℤ)) % (n : ℤ) = (m₀.1 : ℤ) := by exact_mod_cast rfl
        exact_mod_cast h2.symm.trans (h1.trans h3)
      rw [if_neg hndvd]; ring
    · intro h; exact absurd (Finset.mem_univ m₀) h
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hinner k l]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => (Finset.sum_mul _ _ _).symm

end FiniteGroup

end GroupAlg

/- Section 2: Weighted Laurent Banach algebra `W A = lp (fun _ : ℤ => A) 1` (`r₀ = 5/4`) -/

noncomputable def r₀ : ℝ := 5 / 4

lemma hr₀_pos : (0 : ℝ) < r₀ := by norm_num [r₀]
lemma hr₀_gt_one : (1 : ℝ) < r₀ := by norm_num [r₀]
lemma hr₀_inv_pos : (0 : ℝ) < r₀⁻¹ := inv_pos.2 hr₀_pos

abbrev W (A : Type*) [NormedAddCommGroup A] := lp (fun _ : ℤ => A) 1

section WeightedLaurent

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

lemma w_norm_eq_tsum (f : W A) : ‖f‖ = ∑' n : ℤ, ‖f n‖ := by
  have h := lp.norm_eq_tsum_rpow (p := 1) (by norm_num) f
  simpa using h

lemma w_summable_norm (f : W A) : Summable (fun n : ℤ => ‖f n‖) := by
  have h := (lp.memℓp f).summable (p := 1) (by norm_num)
  simpa using h

lemma w_memℓp_of_summable {g : ℤ → A} (hg : Summable (fun n : ℤ => ‖g n‖)) :
    Memℓp g 1 := by
  rw [memℓp_gen_iff (by norm_num)]
  simpa using hg

noncomputable def wOfSummable (g : ℤ → A) (hg : Summable (fun n : ℤ => ‖g n‖)) : W A :=
  ⟨g, w_memℓp_of_summable hg⟩

@[simp] lemma wOfSummable_apply (g : ℤ → A) (hg : Summable (fun n : ℤ => ‖g n‖)) (n : ℤ) :
    (wOfSummable g hg) n = g n := rfl

noncomputable def wCoeff (f : W A) (n : ℤ) : A :=
  ((r₀⁻¹ ^ n.natAbs : ℝ) : ℂ) • f n

lemma norm_wCoeff (f : W A) (n : ℤ) : ‖wCoeff f n‖ = r₀⁻¹ ^ n.natAbs * ‖f n‖ := by
  rw [wCoeff, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hr₀_inv_pos.le _)]

lemma wCoeff_eq_smul_inv (f : W A) (n : ℤ) :
    ((r₀ ^ n.natAbs : ℝ) : ℂ) • wCoeff f n = f n := by
  rw [wCoeff, smul_smul]
  have h : ((r₀ ^ n.natAbs : ℝ) : ℂ) * ((r₀⁻¹ ^ n.natAbs : ℝ) : ℂ) = 1 := by
    norm_cast
    rw [← mul_pow, mul_inv_cancel₀ hr₀_pos.ne', one_pow]
  rw [h, one_smul]

noncomputable def wOne : W A := lp.single 1 (0 : ℤ) (1 : A)

lemma norm_wOne : ‖(wOne : W A)‖ = 1 := by
  rw [wOne, lp.norm_single (by norm_num), norm_one]

lemma wOne_apply (n : ℤ) : (wOne : W A) n = if n = 0 then 1 else 0 := by
  simp [wOne, lp.single_apply, Pi.single_apply]

lemma wCoeff_wOne (n : ℤ) : wCoeff (wOne : W A) n = if n = 0 then 1 else 0 := by
  rw [wCoeff, wOne_apply]
  split_ifs with h
  · subst h; simp
  · simp

noncomputable def mulWeight (n k : ℤ) : ℝ :=
  r₀ ^ ((n.natAbs : ℤ) - (k.natAbs : ℤ) - ((n - k).natAbs : ℤ))

lemma mulWeight_pos (n k : ℤ) : 0 < mulWeight n k :=
  zpow_pos hr₀_pos _

lemma mulWeight_le_one (n k : ℤ) : mulWeight n k ≤ 1 := by
  have hexp : (n.natAbs : ℤ) - (k.natAbs : ℤ) - ((n - k).natAbs : ℤ) ≤ 0 := by
    have htri : n.natAbs ≤ k.natAbs + (n - k).natAbs := by
      have : n = k + (n - k) := by ring
      conv_lhs => rw [this]
      exact Int.natAbs_add_le k (n - k)
    omega
  exact zpow_le_one_of_nonpos₀ hr₀_gt_one.le hexp

lemma mulWeight_eq_ratio (n k : ℤ) :
    mulWeight n k = r₀ ^ n.natAbs * r₀⁻¹ ^ k.natAbs * r₀⁻¹ ^ (n - k).natAbs := by
  rw [mulWeight, zpow_sub₀ hr₀_pos.ne', zpow_sub₀ hr₀_pos.ne', zpow_natCast, zpow_natCast,
    zpow_natCast]
  simp [div_eq_mul_inv, inv_pow, mul_assoc]

lemma summable_norm_wMul_row (f g : W A) (n : ℤ) :
    Summable (fun k : ℤ => ‖((mulWeight n k : ℝ) : ℂ) • (f k * g (n - k))‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((w_summable_norm f).mul_right ‖g‖)
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (mulWeight_pos n k).le]
  calc mulWeight n k * ‖f k * g (n - k)‖
      ≤ 1 * (‖f k‖ * ‖g (n - k)‖) :=
        mul_le_mul (mulWeight_le_one n k) (norm_mul_le _ _) (norm_nonneg _) zero_le_one
    _ ≤ ‖f k‖ * ‖g‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) g (n - k)) (norm_nonneg _)

lemma summable_wMul_row (f g : W A) (n : ℤ) :
    Summable (fun k : ℤ => ((mulWeight n k : ℝ) : ℂ) • (f k * g (n - k))) :=
  (summable_norm_wMul_row f g n).of_norm

lemma summable_wMul_outer (f g : W A) :
    Summable (fun n : ℤ => ‖∑' k : ℤ, ((mulWeight n k : ℝ) : ℂ) • (f k * g (n - k))‖) := by
  have hprod : Summable (fun p : ℤ × ℤ => ‖f p.1‖ * ‖g p.2‖) :=
    (w_summable_norm f).mul_of_nonneg (w_summable_norm g) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let e : ℤ × ℤ ≃ ℤ × ℤ := {
    toFun := fun p => (p.1 + p.2, p.1)
    invFun := fun q => (q.2, q.1 - q.2)
    left_inv := fun ⟨a, b⟩ => by simp
    right_inv := fun ⟨n, k⟩ => by simp
  }
  have hprod' : Summable (fun q : ℤ × ℤ => ‖f q.2‖ * ‖g (q.1 - q.2)‖) := by
    have := hprod.comp_injective e.symm.injective
    simpa [Function.comp_def, e] using this
  have houter : Summable (fun n : ℤ => ∑' k : ℤ, ‖f k‖ * ‖g (n - k)‖) := hprod'.prod
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) houter
  have hrow : Summable (fun k : ℤ => ‖f k‖ * ‖g (n - k)‖) := hprod'.prod_factor n
  calc ‖∑' k : ℤ, ((mulWeight n k : ℝ) : ℂ) • (f k * g (n - k))‖
      ≤ ∑' k : ℤ, ‖((mulWeight n k : ℝ) : ℂ) • (f k * g (n - k))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_wMul_row f g n)
    _ ≤ ∑' k : ℤ, ‖f k‖ * ‖g (n - k)‖ := by
        refine Summable.tsum_le_tsum (fun k => ?_) (summable_norm_wMul_row f g n) hrow
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (mulWeight_pos n k).le]
        exact (mul_le_mul (mulWeight_le_one n k) (norm_mul_le _ _) (norm_nonneg _) zero_le_one).trans
          (by rw [one_mul])

noncomputable def wMul (f g : W A) : W A :=
  wOfSummable (fun n : ℤ => ∑' k : ℤ, ((mulWeight n k : ℝ) : ℂ) • (f k * g (n - k)))
    (summable_wMul_outer f g)

lemma wMul_apply (f g : W A) (n : ℤ) :
    (wMul f g) n = ∑' k : ℤ, ((mulWeight n k : ℝ) : ℂ) • (f k * g (n - k)) := rfl

lemma wCoeff_wMul (f g : W A) (n : ℤ) :
    wCoeff (wMul f g) n = ∑' k : ℤ, wCoeff f k * wCoeff g (n - k) := by
  rw [wCoeff, wMul_apply]
  have h1 := ((summable_wMul_row f g n).hasSum.const_smul ((r₀⁻¹ ^ n.natAbs : ℝ) : ℂ)).tsum_eq
  rw [← h1]
  congr 1; funext k
  rw [smul_smul, wCoeff, wCoeff, smul_mul_smul_comm]
  congr 1
  norm_cast
  rw [mulWeight_eq_ratio]
  have hcancel : r₀⁻¹ ^ n.natAbs * r₀ ^ n.natAbs = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr₀_pos.ne', one_pow]
  calc r₀⁻¹ ^ n.natAbs * (r₀ ^ n.natAbs * r₀⁻¹ ^ k.natAbs * r₀⁻¹ ^ (n - k).natAbs)
      = (r₀⁻¹ ^ n.natAbs * r₀ ^ n.natAbs) * (r₀⁻¹ ^ k.natAbs * r₀⁻¹ ^ (n - k).natAbs) := by ring
    _ = r₀⁻¹ ^ k.natAbs * r₀⁻¹ ^ (n - k).natAbs := by rw [hcancel, one_mul]

lemma norm_wMul_le (f g : W A) : ‖wMul f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [w_norm_eq_tsum, w_norm_eq_tsum, w_norm_eq_tsum]
  have hprod : Summable (fun p : ℤ × ℤ => ‖f p.1‖ * ‖g p.2‖) :=
    (w_summable_norm f).mul_of_nonneg (w_summable_norm g) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let e : ℤ × ℤ ≃ ℤ × ℤ := {
    toFun := fun p => (p.1 + p.2, p.1)
    invFun := fun q => (q.2, q.1 - q.2)
    left_inv := fun ⟨a, b⟩ => by simp
    right_inv := fun ⟨n, k⟩ => by simp
  }
  have hprod' : Summable (fun q : ℤ × ℤ => ‖f q.2‖ * ‖g (q.1 - q.2)‖) := by
    have := hprod.comp_injective e.symm.injective
    simpa [Function.comp_def, e] using this
  have houter : Summable (fun n : ℤ => ∑' k : ℤ, ‖f k‖ * ‖g (n - k)‖) := hprod'.prod
  calc ∑' n : ℤ, ‖(wMul f g) n‖
      ≤ ∑' n : ℤ, ∑' k : ℤ, ‖f k‖ * ‖g (n - k)‖ := by
        refine Summable.tsum_le_tsum (fun n => ?_) (w_summable_norm (wMul f g)) houter
        have hrow : Summable (fun k : ℤ => ‖f k‖ * ‖g (n - k)‖) := hprod'.prod_factor n
        calc ‖(wMul f g) n‖ ≤ ∑' k : ℤ, ‖((mulWeight n k : ℝ) : ℂ) • (f k * g (n - k))‖ :=
              norm_tsum_le_tsum_norm (summable_norm_wMul_row f g n)
          _ ≤ ∑' k : ℤ, ‖f k‖ * ‖g (n - k)‖ := by
              refine Summable.tsum_le_tsum (fun k => ?_) (summable_norm_wMul_row f g n) hrow
              rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (mulWeight_pos n k).le]
              exact (mul_le_mul (mulWeight_le_one n k) (norm_mul_le _ _) (norm_nonneg _) zero_le_one).trans
                (by rw [one_mul])
    _ = ∑' q : ℤ × ℤ, ‖f q.2‖ * ‖g (q.1 - q.2)‖ := hprod'.tsum_prod.symm
    _ = ∑' p : ℤ × ℤ, ‖f p.1‖ * ‖g p.2‖ := by
        rw [← Equiv.tsum_eq e (fun q : ℤ × ℤ => ‖f q.2‖ * ‖g (q.1 - q.2)‖)]
        congr 1; funext ⟨a, b⟩; simp [e]
    _ = (∑' a : ℤ, ‖f a‖) * (∑' b : ℤ, ‖g b‖) :=
        ((w_summable_norm f).hasSum.mul (w_summable_norm g).hasSum hprod).tsum_eq

lemma wMul_one (f : W A) : wMul f wOne = f := by
  ext n
  rw [wMul_apply, tsum_eq_single n]
  · simp [wOne_apply, mulWeight]
  · intro k hk
    have hnk : n - k ≠ 0 := sub_ne_zero.2 hk.symm
    simp [wOne_apply, hnk]

lemma one_wMul (f : W A) : wMul wOne f = f := by
  ext n
  rw [wMul_apply, tsum_eq_single (0 : ℤ)]
  · simp [wOne_apply, mulWeight]
  · intro k hk; simp [wOne_apply, hk]

lemma wMul_add (f g h : W A) : wMul f (g + h) = wMul f g + wMul f h := by
  ext n
  simp only [lp.coeFn_add, Pi.add_apply, wMul_apply, mul_add, smul_add]
  exact (summable_wMul_row f g n).tsum_add (summable_wMul_row f h n)

lemma add_wMul (f g h : W A) : wMul (f + g) h = wMul f h + wMul g h := by
  ext n
  simp only [lp.coeFn_add, Pi.add_apply, wMul_apply, add_mul, smul_add]
  exact (summable_wMul_row f h n).tsum_add (summable_wMul_row g h n)

lemma wMul_sub (f g h : W A) : wMul f (g - h) = wMul f g - wMul f h := by
  ext n
  simp only [lp.coeFn_sub, Pi.sub_apply, wMul_apply, mul_sub, smul_sub]
  exact (summable_wMul_row f g n).tsum_sub (summable_wMul_row f h n)

lemma sub_wMul (f g h : W A) : wMul (f - g) h = wMul f h - wMul g h := by
  ext n
  simp only [lp.coeFn_sub, Pi.sub_apply, wMul_apply, sub_mul, smul_sub]
  exact (summable_wMul_row f h n).tsum_sub (summable_wMul_row g h n)

lemma smul_wMul (c : ℂ) (f g : W A) : wMul (c • f) g = c • wMul f g := by
  ext n
  simp only [lp.coeFn_smul, Pi.smul_apply, wMul_apply]
  have h1 := ((summable_wMul_row f g n).hasSum.const_smul c).tsum_eq
  rw [← h1]
  congr 1; funext k
  rw [smul_mul_assoc, smul_comm]

lemma wMul_smul (c : ℂ) (f g : W A) : wMul f (c • g) = c • wMul f g := by
  ext n
  simp only [lp.coeFn_smul, Pi.smul_apply, wMul_apply]
  have h1 := ((summable_wMul_row f g n).hasSum.const_smul c).tsum_eq
  rw [← h1]
  congr 1; funext k
  rw [mul_smul_comm, smul_comm]

lemma wMul_zero (f : W A) : wMul f 0 = 0 := by
  ext n; simp [wMul_apply]

lemma zero_wMul (f : W A) : wMul 0 f = 0 := by
  ext n; simp [wMul_apply]

noncomputable def wPow (f : W A) : ℕ → W A
  | 0 => wOne
  | k + 1 => wMul (wPow f k) f

lemma norm_wPow_le (f : W A) (k : ℕ) : ‖wPow f k‖ ≤ ‖f‖ ^ k := by
  induction k with
  | zero => simp [wPow, norm_wOne]
  | succ k ih =>
    rw [wPow, pow_succ]
    exact (norm_wMul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

-- Evaluation on the annulus r₀⁻¹ ≤ ‖w‖ ≤ r₀
lemma norm_zpow_smul_wCoeff_le (f : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) (n : ℤ) :
    ‖w ^ n • wCoeff f n‖ ≤ ‖f n‖ := by
  rw [norm_smul, norm_zpow, norm_wCoeff, ← mul_assoc]
  have hle : ‖w‖ ^ n * r₀⁻¹ ^ n.natAbs ≤ 1 := by
    cases n with
    | ofNat k =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast, Int.natAbs_natCast, ← mul_pow]
      have h1 : ‖w‖ * r₀⁻¹ ≤ 1 := by
        calc ‖w‖ * r₀⁻¹ ≤ r₀ * r₀⁻¹ := mul_le_mul_of_nonneg_right hhi hr₀_inv_pos.le
          _ = 1 := mul_inv_cancel₀ hr₀_pos.ne'
      exact pow_le_one₀ (mul_nonneg (norm_nonneg w) hr₀_inv_pos.le) h1
    | negSucc k =>
      simp only [zpow_negSucc, Int.natAbs_negSucc, ← inv_pow, ← mul_pow]
      have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hr₀_inv_pos hlo
      have h1 : ‖w‖⁻¹ * r₀⁻¹ ≤ 1 := by
        have hinv : ‖w‖⁻¹ ≤ r₀ := by
          rw [inv_le_comm₀ hwpos hr₀_pos]; exact hlo
        calc ‖w‖⁻¹ * r₀⁻¹ ≤ r₀ * r₀⁻¹ := mul_le_mul_of_nonneg_right hinv hr₀_inv_pos.le
          _ = 1 := mul_inv_cancel₀ hr₀_pos.ne'
      exact pow_le_one₀ (mul_nonneg (inv_nonneg.2 (norm_nonneg w)) hr₀_inv_pos.le) h1
  calc ‖w‖ ^ n * r₀⁻¹ ^ n.natAbs * ‖f n‖ ≤ 1 * ‖f n‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = ‖f n‖ := one_mul _

lemma summable_norm_wEval (f : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    Summable (fun n : ℤ => ‖w ^ n • wCoeff f n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_zpow_smul_wCoeff_le f hlo hhi)
    (w_summable_norm f)

lemma summable_wEval (f : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    Summable (fun n : ℤ => w ^ n • wCoeff f n) :=
  (summable_norm_wEval f hlo hhi).of_norm

noncomputable def wEval (f : W A) (w : ℂ) : A :=
  ∑' n : ℤ, w ^ n • wCoeff f n

lemma norm_wEval_le (f : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    ‖wEval f w‖ ≤ ‖f‖ := by
  rw [wEval, w_norm_eq_tsum]
  exact (norm_tsum_le_tsum_norm (summable_norm_wEval f hlo hhi)).trans
    (Summable.tsum_le_tsum (norm_zpow_smul_wCoeff_le f hlo hhi) (summable_norm_wEval f hlo hhi)
      (w_summable_norm f))

lemma wEval_one (w : ℂ) : wEval (wOne : W A) w = 1 := by
  rw [wEval, tsum_eq_single (0 : ℤ)]
  · simp [wCoeff_wOne]
  · intro n hn; simp [wCoeff_wOne, hn]

lemma wEval_add (f g : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (f + g) w = wEval f w + wEval g w := by
  simp only [wEval, wCoeff, lp.coeFn_add, Pi.add_apply, smul_add]
  exact (summable_wEval f hlo hhi).tsum_add (summable_wEval g hlo hhi)

lemma wEval_sub (f g : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (f - g) w = wEval f w - wEval g w := by
  simp only [wEval, wCoeff, lp.coeFn_sub, Pi.sub_apply, smul_sub]
  exact (summable_wEval f hlo hhi).tsum_sub (summable_wEval g hlo hhi)

lemma wEval_smul (c : ℂ) (f : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (c • f) w = c • wEval f w := by
  have h1 := ((summable_wEval f hlo hhi).hasSum.const_smul c).tsum_eq
  rw [wEval, wEval, ← h1]
  congr 1; funext n
  simp only [wCoeff, lp.coeFn_smul, Pi.smul_apply]
  rw [smul_comm c, smul_comm c]

lemma wEval_wMul (f g : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (wMul f g) w = wEval f w * wEval g w := by
  have hw0 : w ≠ 0 := by
    intro hz; rw [hz, norm_zero] at hlo; linarith [hr₀_inv_pos]
  have hprod_norm : Summable (fun p : ℤ × ℤ => ‖(w ^ p.1 • wCoeff f p.1) * (w ^ p.2 • wCoeff g p.2)‖) := by
    have h1 : Summable (fun p : ℤ × ℤ => ‖f p.1‖ * ‖g p.2‖) :=
      (w_summable_norm f).mul_of_nonneg (w_summable_norm g) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) h1
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_zpow_smul_wCoeff_le f hlo hhi p.1)
      (norm_zpow_smul_wCoeff_le g hlo hhi p.2) (norm_nonneg _) (norm_nonneg _))
  have hprod : Summable (fun p : ℤ × ℤ => (w ^ p.1 • wCoeff f p.1) * (w ^ p.2 • wCoeff g p.2)) :=
    hprod_norm.of_norm
  let e : ℤ × ℤ ≃ ℤ × ℤ := {
    toFun := fun p => (p.1 + p.2, p.1)
    invFun := fun q => (q.2, q.1 - q.2)
    left_inv := fun ⟨a, b⟩ => by simp
    right_inv := fun ⟨n, k⟩ => by simp
  }
  have hprod' : Summable (fun q : ℤ × ℤ => (w ^ q.2 • wCoeff f q.2) * (w ^ (q.1 - q.2) • wCoeff g (q.1 - q.2))) := by
    have := hprod.comp_injective e.symm.injective
    simpa [Function.comp_def, e] using this
  have hmul : wEval f w * wEval g w =
      ∑' p : ℤ × ℤ, (w ^ p.1 • wCoeff f p.1) * (w ^ p.2 • wCoeff g p.2) :=
    ((summable_wEval f hlo hhi).hasSum.mul (summable_wEval g hlo hhi).hasSum hprod).tsum_eq.symm
  rw [hmul, ← Equiv.tsum_eq e.symm (fun p : ℤ × ℤ =>
      (w ^ p.1 • wCoeff f p.1) * (w ^ p.2 • wCoeff g p.2))]
  simp only [e, Equiv.coe_fn_symm_mk]
  rw [hprod'.tsum_prod]
  simp only [wEval, wCoeff_wMul]
  congr 1; funext n
  have hrow_coeff : Summable (fun k : ℤ => wCoeff f k * wCoeff g (n - k)) := by
    have h1 := ((summable_wMul_row f g n).hasSum.const_smul ((r₀⁻¹ ^ n.natAbs : ℝ) : ℂ)).summable
    refine h1.congr fun k => ?_
    rw [smul_smul, wCoeff, wCoeff, smul_mul_smul_comm]
    congr 1; norm_cast; rw [mulWeight_eq_ratio]
    have hcancel : r₀⁻¹ ^ n.natAbs * r₀ ^ n.natAbs = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hr₀_pos.ne', one_pow]
    calc r₀⁻¹ ^ n.natAbs * (r₀ ^ n.natAbs * r₀⁻¹ ^ k.natAbs * r₀⁻¹ ^ (n - k).natAbs)
        = (r₀⁻¹ ^ n.natAbs * r₀ ^ n.natAbs) * (r₀⁻¹ ^ k.natAbs * r₀⁻¹ ^ (n - k).natAbs) := by ring
      _ = r₀⁻¹ ^ k.natAbs * r₀⁻¹ ^ (n - k).natAbs := by rw [hcancel, one_mul]
  rw [← (hrow_coeff.hasSum.const_smul (w ^ n)).tsum_eq]
  congr 1; funext k
  rw [smul_mul_smul_comm, ← zpow_add₀ hw0, add_sub_cancel]

lemma wEval_wPow (f : W A) (k : ℕ) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (wPow f k) w = (wEval f w) ^ k := by
  induction k with
  | zero => simp [wPow, wEval_one]
  | succ k ih => rw [wPow, pow_succ, wEval_wMul _ _ hlo hhi, ih]

noncomputable def wEvalCLM (w : ℂ) (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) : W A →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := fun f => wEval f w
      map_add' := fun f g => wEval_add f g hlo hhi
      map_smul' := fun c f => wEval_smul c f hlo hhi }
    1
    (fun f => by simpa using norm_wEval_le f hlo hhi)

lemma wEval_tsum {ι : Type*} (u : ι → W A) (hu : Summable u)
    {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (∑' k, u k) w = ∑' k, wEval (u k) w :=
  (wEvalCLM w hlo hhi).map_tsum hu

/- Section 3: Analyticity of power series, `wPos`, `wNeg`, and `wShift` -/

lemma differentiableOn_tsum_pow {c : ℕ → A} {R : ℝ} (hR : 0 < R)
    (hc : Summable (fun n : ℕ => R ^ n * ‖c n‖)) :
    DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, w ^ n • c n) (Metric.ball 0 R) := by
  let p : FormalMultilinearSeries ℂ ℂ A :=
    fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n)
  have hnorm_p : ∀ n : ℕ, ‖p n‖ ≤ ‖c n‖ := fun n => by
    simp only [p, ContinuousMultilinearMap.norm_mkPiRing]
    exact le_rfl
  have hbound : ∃ C : ℝ, ∀ n : ℕ, ‖p n‖ * R ^ n ≤ C := by
    refine ⟨∑' n : ℕ, R ^ n * ‖c n‖, fun n => ?_⟩
    calc ‖p n‖ * R ^ n ≤ R ^ n * ‖c n‖ := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hnorm_p n) (pow_nonneg hR.le n)
      _ ≤ ∑' m : ℕ, R ^ m * ‖c m‖ :=
          Summable.le_tsum hc n (fun m _ => mul_nonneg (pow_nonneg hR.le m) (norm_nonneg _))
  obtain ⟨C, hC⟩ := hbound
  have hrad : (ENNReal.ofReal R) ≤ p.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound p C fun n => ?_
    rw [Real.coe_toNNReal R hR.le]
    exact hC n
  have hps : HasFPowerSeriesOnBall (fun w : ℂ => p.sum w) p 0 (ENNReal.ofReal R) :=
    (p.hasFPowerSeriesOnBall (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hR) hrad)).mono
      (ENNReal.ofReal_pos.2 hR) hrad
  have heq : Set.EqOn (fun w : ℂ => ∑' n : ℕ, w ^ n • c n) (fun w : ℂ => p.sum w)
      (Metric.ball 0 R) := by
    intro w _
    simp only [FormalMultilinearSeries.sum, p, ContinuousMultilinearMap.mkPiRing_apply,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hball : Metric.ball (0 : ℂ) R = Metric.eball (0 : ℂ) (ENNReal.ofReal R) := by
    ext z
    simp only [Metric.mem_ball, Metric.mem_eball, edist_dist]
    rw [ENNReal.ofReal_lt_ofReal_iff hR]
  rw [hball]
  exact hps.differentiableOn.congr fun z hz => heq (by rwa [hball])

def IsNonneg (f : W A) : Prop := ∀ n : ℤ, n < 0 → f n = 0
def IsStrictNeg (f : W A) : Prop := ∀ n : ℤ, 0 ≤ n → f n = 0

lemma isNonneg_wOne : IsNonneg (wOne : W A) := fun n hn => by
  simp [wOne_apply, ne_of_lt hn]

lemma isNonneg_wMul {f g : W A} (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (wMul f g) := by
  intro n hn
  rw [wMul_apply]
  have hz : (fun k : ℤ => ((mulWeight n k : ℝ) : ℂ) • (f k * g (n - k))) = fun _ => 0 := by
    funext k
    by_cases hk : k < 0
    · simp [hf k hk]
    · have hnk : n - k < 0 := by omega
      simp [hg (n - k) hnk]
  rw [hz, tsum_zero]

lemma isNonneg_wPow {f : W A} (hf : IsNonneg f) (k : ℕ) : IsNonneg (wPow f k) := by
  induction k with
  | zero => exact isNonneg_wOne
  | succ k ih => exact isNonneg_wMul ih hf

noncomputable def wEvalNonneg (f : W A) (w : ℂ) : A :=
  ∑' n : ℕ, w ^ n • wCoeff f n

noncomputable def wEvalNeg (f : W A) (w : ℂ) : A :=
  ∑' m : ℕ, (w⁻¹) ^ (m + 1) • wCoeff f (-(m + 1 : ℤ))

lemma norm_pow_smul_wCoeff_le (f : W A) {w : ℂ} (hw : ‖w‖ ≤ r₀) (n : ℕ) :
    ‖w ^ n • wCoeff f n‖ ≤ ‖f (n : ℤ)‖ := by
  rw [norm_smul, norm_pow, norm_wCoeff, Int.natAbs_natCast, ← mul_assoc, ← mul_pow]
  have h1 : ‖w‖ * r₀⁻¹ ≤ 1 := by
    calc ‖w‖ * r₀⁻¹ ≤ r₀ * r₀⁻¹ := mul_le_mul_of_nonneg_right hw hr₀_inv_pos.le
      _ = 1 := mul_inv_cancel₀ hr₀_pos.ne'
  calc (‖w‖ * r₀⁻¹) ^ n * ‖f (n : ℤ)‖ ≤ 1 * ‖f (n : ℤ)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (mul_nonneg (norm_nonneg w) hr₀_inv_pos.le) h1) (norm_nonneg _)
    _ = ‖f (n : ℤ)‖ := one_mul _

lemma summable_norm_wEvalNonneg (f : W A) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    Summable (fun n : ℕ => ‖w ^ n • wCoeff f n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_pow_smul_wCoeff_le f hw)
    ((w_summable_norm f).comp_injective Nat.cast_injective)

lemma summable_wEvalNonneg (f : W A) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    Summable (fun n : ℕ => w ^ n • wCoeff f n) :=
  (summable_norm_wEvalNonneg f hw).of_norm

lemma norm_wEvalNonneg_le (f : W A) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    ‖wEvalNonneg f w‖ ≤ ‖f‖ := by
  have hsub : Summable (fun n : ℕ => ‖f (n : ℤ)‖) :=
    (w_summable_norm f).comp_injective Nat.cast_injective
  have hle1 : ‖wEvalNonneg f w‖ ≤ ∑' n : ℕ, ‖f (n : ℤ)‖ :=
    (norm_tsum_le_tsum_norm (summable_norm_wEvalNonneg f hw)).trans
      (Summable.tsum_le_tsum (norm_pow_smul_wCoeff_le f hw) (summable_norm_wEvalNonneg f hw) hsub)
  rw [w_norm_eq_tsum]
  exact hle1.trans (tsum_comp_le_tsum_of_inj (w_summable_norm f) (fun _ => norm_nonneg _) Nat.cast_injective)

lemma wEvalNonneg_eq_wEval {f : W A} (hf : IsNonneg f) {w : ℂ}
    (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEvalNonneg f w = wEval f w := by
  rw [wEvalNonneg, wEval]
  have hzero : ∀ n : ℤ, n ∉ Set.range (Nat.cast : ℕ → ℤ) → w ^ n • wCoeff f n = 0 := by
    intro n hn
    have hneg : n < 0 := by
      by_contra hge
      push Not at hge
      exact hn ⟨n.toNat, Int.toNat_of_nonneg hge⟩
    simp [wCoeff, hf n hneg]
  rw [← tsum_subtype_eq_of_support_subset (s := Set.range (Nat.cast : ℕ → ℤ))
    (fun n hn => by by_contra hnot; exact hn (hzero n hnot))]
  rw [← Equiv.tsum_eq (Equiv.ofInjective (Nat.cast : ℕ → ℤ) Nat.cast_injective)
    (fun x : Set.range (Nat.cast : ℕ → ℤ) => w ^ (x : ℤ) • wCoeff f x)]
  congr 1

lemma wEvalNonneg_one (w : ℂ) : wEvalNonneg (wOne : W A) w = 1 := by
  rw [wEvalNonneg, tsum_eq_single 0]
  · simp [wCoeff_wOne]
  · intro n hn; simp [wCoeff_wOne, hn]

lemma wEvalNonneg_wMul {f g : W A} (hf : IsNonneg f) (hg : IsNonneg g) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    wEvalNonneg (wMul f g) w = wEvalNonneg f w * wEvalNonneg g w := by
  have hprod_norm : Summable (fun p : ℕ × ℕ => ‖(w ^ p.1 • wCoeff f p.1) * (w ^ p.2 • wCoeff g p.2)‖) := by
    have h1 : Summable (fun p : ℕ × ℕ => ‖f (p.1 : ℤ)‖ * ‖g (p.2 : ℤ)‖) :=
      ((w_summable_norm f).comp_injective Nat.cast_injective).mul_of_nonneg
        ((w_summable_norm g).comp_injective Nat.cast_injective)
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) h1
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_pow_smul_wCoeff_le f hw p.1)
      (norm_pow_smul_wCoeff_le g hw p.2) (norm_nonneg _) (norm_nonneg _))
  have hprod := hprod_norm.of_norm
  let e : (Σ n : ℕ, Fin (n + 1)) ≃ ℕ × ℕ := {
    toFun := fun x => (x.2.1, x.1 - x.2.1)
    invFun := fun p => ⟨p.1 + p.2, ⟨p.1, by omega⟩⟩
    left_inv := fun ⟨n, ⟨k, hk⟩⟩ => by
      have h1 : k + (n - k) = n := by omega
      exact Sigma.ext h1 ((Fin.heq_ext_iff (congrArg (· + 1) h1)).2 rfl)
    right_inv := fun ⟨a, b⟩ => by simp
  }
  have hmul : wEvalNonneg f w * wEvalNonneg g w =
      ∑' p : ℕ × ℕ, (w ^ p.1 • wCoeff f p.1) * (w ^ p.2 • wCoeff g p.2) :=
    ((summable_wEvalNonneg f hw).hasSum.mul (summable_wEvalNonneg g hw).hasSum hprod).tsum_eq.symm
  rw [hmul, ← Equiv.tsum_eq e]
  simp only [e, Equiv.coe_fn_mk]
  have hsigma : Summable (fun x : Σ n : ℕ, Fin (n + 1) =>
      (w ^ x.2.1 • wCoeff f x.2.1) * (w ^ (x.1 - x.2.1) • wCoeff g (x.1 - x.2.1 : ℕ))) := by
    simpa [Function.comp_def, e] using hprod.comp_injective e.injective
  rw [hsigma.tsum_sigma]
  rw [wEvalNonneg]
  congr 1; funext n
  rw [tsum_fintype, wCoeff_wMul]
  have hfin : ∑' k : ℤ, wCoeff f k * wCoeff g ((n : ℤ) - k) =
      ∑ k : Fin (n + 1), wCoeff f (k.1 : ℤ) * wCoeff g ((n - k.1 : ℕ) : ℤ) := by
    rw [tsum_eq_sum (s := (Finset.range (n + 1)).image (Nat.cast : ℕ → ℤ))]
    · rw [Finset.sum_image (fun a _ b _ h => Nat.cast_injective h), ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsub : (n : ℤ) - (k.1 : ℤ) = ((n - k.1 : ℕ) : ℤ) := by omega
      rw [hsub]
    · intro k hk
      by_cases hneg : k < 0
      · simp [wCoeff, hf k hneg]
      · have hgt : (n : ℤ) < k := by
          by_contra hle
          push Not at hle hneg
          exact hk (Finset.mem_image.2 ⟨k.toNat, Finset.mem_range.2 (by omega), Int.toNat_of_nonneg hneg⟩)
        have hsub : (n : ℤ) - k < 0 := by omega
        simp [wCoeff, hg ((n : ℤ) - k) hsub]
  rw [hfin, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_smul_comm, ← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.1 k.2)]

lemma differentiableOn_wEvalNonneg (f : W A) :
    DifferentiableOn ℂ (wEvalNonneg f) (Metric.ball 0 r₀) := by
  refine differentiableOn_tsum_pow hr₀_pos ?_
  have hsub : Summable (fun n : ℕ => ‖f (n : ℤ)‖) :=
    (w_summable_norm f).comp_injective Nat.cast_injective
  refine hsub.congr fun n => ?_
  rw [norm_wCoeff, Int.natAbs_natCast, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr₀_pos.ne', one_pow, one_mul]

lemma neg_succ_injective : Function.Injective (fun m : ℕ => (-(m + 1 : ℤ))) := by
  intro a b h
  have h1 : (a : ℤ) = (b : ℤ) := by linarith
  exact_mod_cast h1

lemma norm_inv_pow_smul_wCoeff_le (f : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (m : ℕ) :
    ‖(w⁻¹) ^ (m + 1) • wCoeff f (-(m + 1 : ℤ))‖ ≤ ‖f (-(m + 1 : ℤ))‖ := by
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hr₀_inv_pos hlo
  have hinv : ‖w‖⁻¹ ≤ r₀ := (inv_le_comm₀ hwpos hr₀_pos).2 hlo
  rw [norm_smul, norm_pow, norm_inv, norm_wCoeff, Int.natAbs_neg]
  have habs : ((m + 1 : ℤ)).natAbs = m + 1 := by omega
  rw [habs, ← mul_assoc, ← mul_pow]
  have h1 : ‖w‖⁻¹ * r₀⁻¹ ≤ 1 := by
    calc ‖w‖⁻¹ * r₀⁻¹ ≤ r₀ * r₀⁻¹ := mul_le_mul_of_nonneg_right hinv hr₀_inv_pos.le
      _ = 1 := mul_inv_cancel₀ hr₀_pos.ne'
  calc (‖w‖⁻¹ * r₀⁻¹) ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖
      ≤ 1 * ‖f (-(m + 1 : ℤ))‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (mul_nonneg (inv_nonneg.2 (norm_nonneg w)) hr₀_inv_pos.le) h1)
          (norm_nonneg _)
    _ = ‖f (-(m + 1 : ℤ))‖ := one_mul _

lemma summable_norm_wEvalNeg (f : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) :
    Summable (fun m : ℕ => ‖(w⁻¹) ^ (m + 1) • wCoeff f (-(m + 1 : ℤ))‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_inv_pow_smul_wCoeff_le f hlo)
    ((w_summable_norm f).comp_injective neg_succ_injective)

lemma summable_wEvalNeg (f : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) :
    Summable (fun m : ℕ => (w⁻¹) ^ (m + 1) • wCoeff f (-(m + 1 : ℤ))) :=
  (summable_norm_wEvalNeg f hlo).of_norm

lemma norm_wEvalNeg_le (f : W A) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) :
    ‖wEvalNeg f w‖ ≤ ‖f‖ := by
  have hsub : Summable (fun m : ℕ => ‖f (-(m + 1 : ℤ))‖) :=
    (w_summable_norm f).comp_injective neg_succ_injective
  have hle1 : ‖wEvalNeg f w‖ ≤ ∑' m : ℕ, ‖f (-(m + 1 : ℤ))‖ :=
    (norm_tsum_le_tsum_norm (summable_norm_wEvalNeg f hlo)).trans
      (Summable.tsum_le_tsum (norm_inv_pow_smul_wCoeff_le f hlo) (summable_norm_wEvalNeg f hlo) hsub)
  rw [w_norm_eq_tsum]
  exact hle1.trans (tsum_comp_le_tsum_of_inj (w_summable_norm f) (fun _ => norm_nonneg _) neg_succ_injective)

lemma wEvalNeg_eq_wEval {f : W A} (hf : IsStrictNeg f) {w : ℂ}
    (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEvalNeg f w = wEval f w := by
  rw [wEvalNeg, wEval]
  let emb : ℕ → ℤ := fun m => -(m + 1 : ℤ)
  have hemb : Function.Injective emb := neg_succ_injective
  have hzero : ∀ n : ℤ, n ∉ Set.range emb → w ^ n • wCoeff f n = 0 := by
    intro n hn
    have hnn : 0 ≤ n := by
      by_contra hlt
      push Not at hlt
      exact hn ⟨(-n - 1).toNat, by dsimp [emb]; omega⟩
    simp [wCoeff, hf n hnn]
  rw [← tsum_subtype_eq_of_support_subset (s := Set.range emb)
    (fun n hn => by by_contra hnot; exact hn (hzero n hnot))]
  rw [← Equiv.tsum_eq (Equiv.ofInjective emb hemb)
    (fun x : Set.range emb => w ^ (x : ℤ) • wCoeff f x)]
  congr 1; funext m
  have hzpow : (w⁻¹) ^ (m + 1) = w ^ (-(m + 1 : ℤ)) := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]; rfl
  simp only [Equiv.ofInjective_apply, emb, hzpow]

lemma differentiableOn_wEvalNeg (f : W A) :
    DifferentiableOn ℂ (wEvalNeg f) {w : ℂ | r₀⁻¹ < ‖w‖} := by
  let c : ℕ → A := fun n => match n with | 0 => 0 | m + 1 => wCoeff f (-(m + 1 : ℤ))
  have hc : Summable (fun n : ℕ => r₀ ^ n * ‖c n‖) := by
    have hsub : Summable (fun m : ℕ => ‖f (-(m + 1 : ℤ))‖) :=
      (w_summable_norm f).comp_injective neg_succ_injective
    rw [← summable_nat_add_iff 1]
    refine hsub.congr fun m => ?_
    simp only [c, norm_wCoeff, Int.natAbs_neg]
    have habs : ((m + 1 : ℤ)).natAbs = m + 1 := by omega
    rw [habs, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr₀_pos.ne', one_pow, one_mul]
  have hdiff_h : DifferentiableOn ℂ (fun u : ℂ => ∑' n : ℕ, u ^ n • c n) (Metric.ball 0 r₀) :=
    differentiableOn_tsum_pow hr₀_pos hc
  have heq : ∀ w : ℂ, r₀⁻¹ < ‖w‖ → wEvalNeg f w = ∑' n : ℕ, (w⁻¹) ^ n • c n := by
    intro w hw
    have hsum : Summable (fun n : ℕ => (w⁻¹) ^ n • c n) := by
      rw [← summable_nat_add_iff 1]
      exact summable_wEvalNeg f hw.le
    rw [hsum.tsum_eq_zero_add]
    simp [c, wEvalNeg]
  intro w hw
  have hw0 : w ≠ 0 := by
    intro hz; rw [Set.mem_setOf_eq, hz, norm_zero] at hw; linarith [hr₀_inv_pos]
  have hmem : w⁻¹ ∈ Metric.ball (0 : ℂ) r₀ := by
    rw [Metric.mem_ball, dist_zero_right, norm_inv]
    rw [Set.mem_setOf_eq] at hw
    exact (inv_lt_comm₀ (norm_pos_iff.2 hw0) hr₀_pos).2 hw
  have hcomp : DifferentiableAt ℂ (fun z : ℂ => (fun u : ℂ => ∑' n : ℕ, u ^ n • c n) z⁻¹) w :=
    (hdiff_h.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).comp w (differentiableAt_inv hw0)
  refine hcomp.differentiableWithinAt.congr (fun z hz => heq z hz) (heq w hw)

-- Splitting projections wPos and wNeg
lemma summable_wPos (f : W A) : Summable (fun n : ℤ => ‖if 0 ≤ n then f n else 0‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by split_ifs <;> simp) (w_summable_norm f)

lemma summable_wNeg (f : W A) : Summable (fun n : ℤ => ‖if n < 0 then f n else 0‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by split_ifs <;> simp) (w_summable_norm f)

noncomputable def wPos (f : W A) : W A :=
  wOfSummable (fun n : ℤ => if 0 ≤ n then f n else 0) (summable_wPos f)

noncomputable def wNeg (f : W A) : W A :=
  wOfSummable (fun n : ℤ => if n < 0 then f n else 0) (summable_wNeg f)

lemma wPos_add_wNeg (f : W A) : wPos f + wNeg f = f := by
  ext n; simp only [lp.coeFn_add, Pi.add_apply, wPos, wNeg, wOfSummable_apply]
  split_ifs <;> first | omega | simp

lemma norm_wPos_le (f : W A) : ‖wPos f‖ ≤ ‖f‖ := by
  rw [w_norm_eq_tsum, w_norm_eq_tsum]
  exact Summable.tsum_le_tsum (fun n => by simp [wPos]; split_ifs <;> simp)
    (w_summable_norm (wPos f)) (w_summable_norm f)

lemma norm_wNeg_le (f : W A) : ‖wNeg f‖ ≤ ‖f‖ := by
  rw [w_norm_eq_tsum, w_norm_eq_tsum]
  exact Summable.tsum_le_tsum (fun n => by simp [wNeg]; split_ifs <;> simp)
    (w_summable_norm (wNeg f)) (w_summable_norm f)

lemma isNonneg_wPos (f : W A) : IsNonneg (wPos f) := fun n hn => by
  simp [wPos, not_le.2 hn]

lemma isStrictNeg_wNeg (f : W A) : IsStrictNeg (wNeg f) := fun n hn => by
  simp [wNeg, not_lt.2 hn]

lemma wPos_sub (f g : W A) : wPos (f - g) = wPos f - wPos g := by
  ext n; simp only [lp.coeFn_sub, Pi.sub_apply, wPos, wOfSummable_apply]; split_ifs <;> simp

lemma wNeg_sub (f g : W A) : wNeg (f - g) = wNeg f - wNeg g := by
  ext n; simp only [lp.coeFn_sub, Pi.sub_apply, wNeg, wOfSummable_apply]; split_ifs <;> simp

-- Hockey-stick identity and negative binomial series over any complete NormedField
lemma sum_choose_add (m n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), Nat.choose (m + j) j = Nat.choose (m + 1 + n) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : m + 1 + (n + 1) = (m + 1 + n) + 1 := by omega
    have h2 : m + (n + 1) = m + 1 + n := by omega
    rw [h1, h2, Nat.choose_succ_succ, add_comm]

lemma norm_natCast_le_self {𝕜 : Type*} [NormedField 𝕜] (n : ℕ) : ‖(n : 𝕜)‖ ≤ (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ]
    exact (norm_add_le _ _).trans (by rw [norm_one]; linarith)

lemma hasSum_choose_pow_and_summable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] (m : ℕ)
    {u : 𝕜} (hu : ‖u‖ < 1) :
    HasSum (fun k : ℕ => (Nat.choose (m + k) k : 𝕜) * u ^ k) ((1 - u)⁻¹ ^ (m + 1)) ∧
    Summable (fun k : ℕ => (Nat.choose (m + k) k : ℝ) * ‖u‖ ^ k) := by
  let e : (Σ k : ℕ, Fin (k + 1)) ≃ ℕ × ℕ := {
    toFun := fun x => (x.2.1, x.1 - x.2.1)
    invFun := fun p => ⟨p.1 + p.2, ⟨p.1, by omega⟩⟩
    left_inv := fun ⟨k, ⟨j, hj⟩⟩ => by
      have h1 : j + (k - j) = k := by omega
      exact Sigma.ext h1 ((Fin.heq_ext_iff (congrArg (· + 1) h1)).2 rfl)
    right_inv := fun ⟨a, b⟩ => by simp
  }
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa [Nat.choose_self] using hasSum_geometric_of_norm_lt_one hu
    · simpa [Nat.choose_self] using summable_geometric_of_lt_one (norm_nonneg u) hu
  | succ m ih =>
    rcases ih with ⟨ih_sum, ih_norm⟩
    have hg : HasSum (fun j : ℕ => u ^ j) (1 - u)⁻¹ := hasSum_geometric_of_norm_lt_one hu
    have hgn : Summable (fun j : ℕ => ‖u‖ ^ j) := summable_geometric_of_lt_one (norm_nonneg u) hu
    have hprod_r : Summable (fun p : ℕ × ℕ => ((Nat.choose (m + p.1) p.1 : ℝ) * ‖u‖ ^ p.1) * ‖u‖ ^ p.2) :=
      ih_norm.mul_of_nonneg hgn
        (fun _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg u) _))
        (fun _ => pow_nonneg (norm_nonneg u) _)
    have hsigma_r : Summable (fun x : Σ k : ℕ, Fin (k + 1) =>
        ((Nat.choose (m + x.2.1) x.2.1 : ℝ) * ‖u‖ ^ x.2.1) * ‖u‖ ^ (x.1 - x.2.1)) := by
      have := hprod_r.comp_injective e.injective
      simpa [Function.comp_def, e] using this
    have hnorm_succ : Summable (fun k : ℕ => (Nat.choose (m + 1 + k) k : ℝ) * ‖u‖ ^ k) := by
      have h1 : Summable (fun k : ℕ => ∑' j : Fin (k + 1),
          ((Nat.choose (m + j.1) j.1 : ℝ) * ‖u‖ ^ j.1) * ‖u‖ ^ (k - j.1)) := hsigma_r.sigma
      refine h1.congr fun k => ?_
      rw [tsum_fintype]
      have hterm : ∀ j : Fin (k + 1),
          ((Nat.choose (m + j.1) j.1 : ℝ) * ‖u‖ ^ j.1) * ‖u‖ ^ (k - j.1) =
          (Nat.choose (m + j.1) j.1 : ℝ) * ‖u‖ ^ k := fun j => by
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.1 j.2)]
      simp_rw [hterm]
      rw [← Finset.sum_mul, ← Nat.cast_sum,
        Fin.sum_univ_eq_sum_range (fun j => (m + j).choose j), sum_choose_add]
    have hprod_k : Summable (fun p : ℕ × ℕ =>
        ((Nat.choose (m + p.1) p.1 : 𝕜) * u ^ p.1) * u ^ p.2) := by
      refine Summable.of_norm_bounded hprod_r fun p => ?_
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_natCast_le_self _) (pow_nonneg (norm_nonneg u) _))
        (pow_nonneg (norm_nonneg u) _)
    have hhs_prod : HasSum (fun p : ℕ × ℕ =>
        ((Nat.choose (m + p.1) p.1 : 𝕜) * u ^ p.1) * u ^ p.2) ((1 - u)⁻¹ ^ (m + 2)) := by
      rw [pow_succ]
      exact ih_sum.mul hg hprod_k
    have hhs_sigma : HasSum (fun x : Σ k : ℕ, Fin (k + 1) =>
        ((Nat.choose (m + x.2.1) x.2.1 : 𝕜) * u ^ x.2.1) * u ^ (x.1 - x.2.1))
        ((1 - u)⁻¹ ^ (m + 2)) := by
      have h1 := (Equiv.hasSum_iff e).2 hhs_prod
      exact h1.congr_fun fun x => by rfl
    have hhs_succ : HasSum (fun k : ℕ => (Nat.choose (m + 1 + k) k : 𝕜) * u ^ k)
        ((1 - u)⁻¹ ^ (m + 2)) := by
      refine hhs_sigma.sigma fun k => ?_
      have hfin_eq : (∑ j : Fin (k + 1),
          ((Nat.choose (m + j.1) j.1 : 𝕜) * u ^ j.1) * u ^ (k - j.1)) =
          (Nat.choose (m + 1 + k) k : 𝕜) * u ^ k := by
        have hterm : ∀ j : Fin (k + 1),
            ((Nat.choose (m + j.1) j.1 : 𝕜) * u ^ j.1) * u ^ (k - j.1) =
            (Nat.choose (m + j.1) j.1 : 𝕜) * u ^ k := fun j => by
          rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.1 j.2)]
        simp_rw [hterm]
        rw [← Finset.sum_mul, ← Nat.cast_sum,
          Fin.sum_univ_eq_sum_range (fun j => (m + j).choose j), sum_choose_add]
      rw [← hfin_eq]
      exact hasSum_fintype _
    exact ⟨hhs_succ, hnorm_succ⟩

lemma hasSum_choose_pow {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] (m : ℕ)
    {u : 𝕜} (hu : ‖u‖ < 1) :
    HasSum (fun k : ℕ => (Nat.choose (m + k) k : 𝕜) * u ^ k) ((1 - u)⁻¹ ^ (m + 1)) :=
  (hasSum_choose_pow_and_summable m hu).1

lemma hasSum_shift_term {d w : ℂ} (hwd : ‖w‖ < ‖d‖) (m : ℕ) :
    HasSum (fun k : ℕ => ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) * d⁻¹ ^ (m + 1 + k)) * w ^ k)
      ((d + w)⁻¹ ^ (m + 1)) := by
  have hd0 : d ≠ 0 := by
    intro hz; rw [hz, norm_zero] at hwd; linarith [norm_nonneg w]
  have hu : ‖-(w / d)‖ < 1 := by
    rw [norm_neg, norm_div]
    exact (div_lt_one (norm_pos_iff.2 hd0)).2 hwd
  have h1 := (hasSum_choose_pow m hu).mul_left (d⁻¹ ^ (m + 1))
  have hrhs : d⁻¹ ^ (m + 1) * (1 - -(w / d))⁻¹ ^ (m + 1) = (d + w)⁻¹ ^ (m + 1) := by
    rw [← mul_pow, ← mul_inv, sub_neg_eq_add]
    congr 1; congr 1
    field_simp
  rw [hrhs] at h1
  refine h1.congr_fun fun k => ?_
  rw [neg_eq_neg_one_mul (w / d), mul_pow, div_eq_mul_inv, mul_pow, pow_add]
  ring

section ShiftOp

variable {d : ℂ}

lemma shift_term_norm_eq (hd : 1 < r₀ * (‖d‖ - r₀)) (f : W A) (k m : ℕ) :
    ‖(((r₀ ^ k : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) * d⁻¹ ^ (m + 1 + k))) •
        wCoeff f (-(m + 1 : ℤ))‖ =
      ((Nat.choose (m + k) k : ℝ) * (r₀ / ‖d‖) ^ k) * ((r₀ * ‖d‖)⁻¹ ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖) := by
  have hd_gt : r₀ < ‖d‖ := by nlinarith [hr₀_pos]
  have hdpos : 0 < ‖d‖ := lt_trans hr₀_pos hd_gt
  rw [norm_smul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg hr₀_pos.le k), norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast, norm_pow, norm_inv, norm_wCoeff, Int.natAbs_neg]
  have habs : ((m + 1 : ℤ)).natAbs = m + 1 := by omega
  rw [habs, pow_add, div_pow, mul_inv, mul_pow]
  ring

lemma shift_summable_prod (hd : 1 < r₀ * (‖d‖ - r₀)) (f : W A) :
    Summable (fun p : ℕ × ℕ =>
      ‖(((r₀ ^ p.1 : ℝ) : ℂ) * ((-1 : ℂ) ^ p.1 * (Nat.choose (p.2 + p.1) p.1 : ℂ) *
        d⁻¹ ^ (p.2 + 1 + p.1))) • wCoeff f (-(p.2 + 1 : ℤ))‖) := by
  have hd_gt : r₀ < ‖d‖ := by nlinarith [hr₀_pos]
  have hdpos : 0 < ‖d‖ := lt_trans hr₀_pos hd_gt
  have hratio : r₀ / ‖d‖ < 1 := (div_lt_one hdpos).2 hd_gt
  have hsub : Summable (fun m : ℕ => ‖f (-(m + 1 : ℤ))‖) :=
    (w_summable_norm f).comp_injective neg_succ_injective
  let g : ℕ × ℕ → ℝ := fun p =>
    ((Nat.choose (p.2 + p.1) p.1 : ℝ) * (r₀ / ‖d‖) ^ p.1) *
      ((r₀ * ‖d‖)⁻¹ ^ (p.2 + 1) * ‖f (-(p.2 + 1 : ℤ))‖)
  suffices hg : Summable g by
    refine hg.congr fun p => (shift_term_norm_eq hd f p.1 p.2).symm
  have hinner : ∀ m : ℕ, HasSum (fun k : ℕ => g (k, m))
      ((r₀ * (‖d‖ - r₀))⁻¹ ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖) := fun m => by
    have hhs := hasSum_choose_pow (𝕜 := ℝ) m (u := r₀ / ‖d‖) (by
      rw [Real.norm_of_nonneg (div_nonneg hr₀_pos.le hdpos.le)]; exact hratio)
    have h1 := hhs.mul_right ((r₀ * ‖d‖)⁻¹ ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖)
    have hval : (1 - r₀ / ‖d‖)⁻¹ ^ (m + 1) * ((r₀ * ‖d‖)⁻¹ ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖) =
        (r₀ * (‖d‖ - r₀))⁻¹ ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖ := by
      rw [← mul_assoc, ← mul_pow, ← mul_inv]
      congr 1; congr 1; congr 1
      have hne : ‖d‖ ≠ 0 := hdpos.ne'
      field_simp
    rwa [hval] at h1
  have houter : Summable (fun m : ℕ => (r₀ * (‖d‖ - r₀))⁻¹ ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg (inv_nonneg.2 (by linarith)) _) (norm_nonneg _))
      (fun m => ?_) (hsub.mul_left (r₀ * (‖d‖ - r₀))⁻¹)
    have hle1 : (r₀ * (‖d‖ - r₀))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd.le
    have hpow : (r₀ * (‖d‖ - r₀))⁻¹ ^ (m + 1) ≤ (r₀ * (‖d‖ - r₀))⁻¹ := by
      rw [pow_succ']
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (inv_nonneg.2 (by linarith)) hle1)
        (inv_nonneg.2 (by linarith))).trans (by rw [mul_one])
    exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
  have hcomm : Summable (fun q : ℕ × ℕ => g (q.2, q.1)) := by
    rw [summable_prod_of_nonneg (fun q => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg hr₀_pos.le hdpos.le) _))
      (mul_nonneg (pow_nonneg (inv_nonneg.2 (mul_nonneg hr₀_pos.le hdpos.le)) _) (norm_nonneg _)))]
    exact ⟨fun m => (hinner m).summable, houter.congr fun m => ((hinner m).tsum_eq).symm⟩
  simpa [Function.comp_def] using hcomm.comp_injective (Equiv.prodComm ℕ ℕ).injective

noncomputable def wShiftFun (hd : 1 < r₀ * (‖d‖ - r₀)) (f : W A) (n : ℤ) : A :=
  match n with
  | Int.ofNat k =>
      ∑' m : ℕ, (((r₀ ^ k : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) *
        d⁻¹ ^ (m + 1 + k))) • wCoeff f (-(m + 1 : ℤ))
  | Int.negSucc _ => 0

lemma summable_wShiftFun (hd : 1 < r₀ * (‖d‖ - r₀)) (f : W A) :
    Summable (fun n : ℤ => ‖wShiftFun hd f n‖) := by
  have hprod := shift_summable_prod hd f
  have hnat : Summable (fun k : ℕ => ‖wShiftFun hd f (k : ℤ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hprod.prod
    exact norm_tsum_le_tsum_norm (hprod.prod_factor k)
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨hnat, ?_⟩
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  have hk0 : k ≠ 0 := by simpa using hk
  cases k with
  | zero => exact absurd rfl hk0
  | succ m =>
    change ‖wShiftFun hd f (Int.negSucc m)‖ = 0
    simp [wShiftFun]

noncomputable def wShift (hd : 1 < r₀ * (‖d‖ - r₀)) (f : W A) : W A :=
  wOfSummable (wShiftFun hd f) (summable_wShiftFun hd f)

lemma isNonneg_wShift (hd : 1 < r₀ * (‖d‖ - r₀)) (f : W A) : IsNonneg (wShift hd f) := by
  intro n hn
  cases n with
  | ofNat k => change (k : ℤ) < 0 at hn; omega
  | negSucc m => rfl

lemma wShift_sub (hd : 1 < r₀ * (‖d‖ - r₀)) (f g : W A) :
    wShift hd (f - g) = wShift hd f - wShift hd g := by
  ext n
  cases n with
  | negSucc m => simp [wShift, wShiftFun]
  | ofNat k =>
    simp only [lp.coeFn_sub, Pi.sub_apply, wShift, wOfSummable_apply, wShiftFun]
    have hf := ((shift_summable_prod hd f).prod_factor k).of_norm
    have hg := ((shift_summable_prod hd g).prod_factor k).of_norm
    have hsub : (fun m : ℕ => (((r₀ ^ k : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) *
        d⁻¹ ^ (m + 1 + k))) • wCoeff (f - g) (-(m + 1 : ℤ))) =
        (fun m : ℕ => (((r₀ ^ k : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) *
          d⁻¹ ^ (m + 1 + k))) • wCoeff f (-(m + 1 : ℤ)) -
          (((r₀ ^ k : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) *
            d⁻¹ ^ (m + 1 + k))) • wCoeff g (-(m + 1 : ℤ))) := by
      funext m
      simp only [wCoeff, lp.coeFn_sub, Pi.sub_apply, smul_sub]
    rw [hsub]
    exact hf.tsum_sub hg

lemma norm_wShift_le (hd : 1 < r₀ * (‖d‖ - r₀)) (f : W A) :
    ‖wShift hd f‖ ≤ (r₀ * (‖d‖ - r₀))⁻¹ * ‖f‖ := by
  have hd_gt : r₀ < ‖d‖ := by nlinarith [hr₀_pos]
  have hdpos : 0 < ‖d‖ := lt_trans hr₀_pos hd_gt
  have hratio : r₀ / ‖d‖ < 1 := (div_lt_one hdpos).2 hd_gt
  have hprod := shift_summable_prod hd f
  have htsum_eq : ‖wShift hd f‖ = ∑' k : ℕ, ‖wShiftFun hd f (k : ℤ)‖ := by
    rw [w_norm_eq_tsum]
    have hzero : ∀ n : ℤ, n ∉ Set.range (Nat.cast : ℕ → ℤ) → ‖(wShift hd f) n‖ = 0 := by
      intro n hn
      have hneg : n < 0 := by
        by_contra hge; push Not at hge; exact hn ⟨n.toNat, Int.toNat_of_nonneg hge⟩
      simp [isNonneg_wShift hd f n hneg]
    rw [← tsum_subtype_eq_of_support_subset (s := Set.range (Nat.cast : ℕ → ℤ))
      (fun n hn => by by_contra hnot; exact hn (hzero n hnot))]
    rw [← Equiv.tsum_eq (Equiv.ofInjective (Nat.cast : ℕ → ℤ) Nat.cast_injective)
      (fun x : Set.range (Nat.cast : ℕ → ℤ) => ‖(wShift hd f) x‖)]
    congr 1
  rw [htsum_eq]
  have hle1 : ∑' k : ℕ, ‖wShiftFun hd f (k : ℤ)‖ ≤
      ∑' p : ℕ × ℕ, ‖(((r₀ ^ p.1 : ℝ) : ℂ) * ((-1 : ℂ) ^ p.1 * (Nat.choose (p.2 + p.1) p.1 : ℂ) *
        d⁻¹ ^ (p.2 + 1 + p.1))) • wCoeff f (-(p.2 + 1 : ℤ))‖ := by
    rw [hprod.tsum_prod]
    refine Summable.tsum_le_tsum (fun k => ?_)
      ((summable_wShiftFun hd f).comp_injective Nat.cast_injective) hprod.prod
    exact norm_tsum_le_tsum_norm (hprod.prod_factor k)
  have hcomm_sum : (∑' p : ℕ × ℕ, ‖(((r₀ ^ p.1 : ℝ) : ℂ) * ((-1 : ℂ) ^ p.1 *
      (Nat.choose (p.2 + p.1) p.1 : ℂ) * d⁻¹ ^ (p.2 + 1 + p.1))) • wCoeff f (-(p.2 + 1 : ℤ))‖) =
      ∑' m : ℕ, (r₀ * (‖d‖ - r₀))⁻¹ ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖ := by
    have hprod_swap := hprod.comp_injective (Equiv.prodComm ℕ ℕ).injective
    dsimp only [Function.comp_def, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at hprod_swap
    rw [← Equiv.tsum_eq (Equiv.prodComm ℕ ℕ)]
    dsimp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hprod_swap.tsum_prod]
    congr 1; funext m
    simp only [shift_term_norm_eq hd f]
    have hhs := hasSum_choose_pow (𝕜 := ℝ) m (u := r₀ / ‖d‖) (by
      rw [Real.norm_of_nonneg (div_nonneg hr₀_pos.le hdpos.le)]; exact hratio)
    rw [tsum_mul_right, hhs.tsum_eq, ← mul_assoc, ← mul_pow, ← mul_inv]
    congr 1; congr 1; congr 1
    have hne : ‖d‖ ≠ 0 := hdpos.ne'
    field_simp
  have hsub : Summable (fun m : ℕ => ‖f (-(m + 1 : ℤ))‖) :=
    (w_summable_norm f).comp_injective neg_succ_injective
  have hle2 : ∑' m : ℕ, (r₀ * (‖d‖ - r₀))⁻¹ ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖ ≤
      (r₀ * (‖d‖ - r₀))⁻¹ * ∑' m : ℕ, ‖f (-(m + 1 : ℤ))‖ := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun m => ?_) ?_ (hsub.mul_left _)
    · have hle1' : (r₀ * (‖d‖ - r₀))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd.le
      have hpow : (r₀ * (‖d‖ - r₀))⁻¹ ^ (m + 1) ≤ (r₀ * (‖d‖ - r₀))⁻¹ := by
        rw [pow_succ']
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (inv_nonneg.2 (by linarith)) hle1')
          (inv_nonneg.2 (by linarith))).trans (by rw [mul_one])
      exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    · refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (pow_nonneg (inv_nonneg.2 (by linarith)) _) (norm_nonneg _))
        (fun m => ?_) (hsub.mul_left ((r₀ * (‖d‖ - r₀))⁻¹))
      have hle1' : (r₀ * (‖d‖ - r₀))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd.le
      have hpow : (r₀ * (‖d‖ - r₀))⁻¹ ^ (m + 1) ≤ (r₀ * (‖d‖ - r₀))⁻¹ := by
        rw [pow_succ']
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (inv_nonneg.2 (by linarith)) hle1')
          (inv_nonneg.2 (by linarith))).trans (by rw [mul_one])
      exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
  have hle3 : ∑' m : ℕ, ‖f (-(m + 1 : ℤ))‖ ≤ ‖f‖ := by
    rw [w_norm_eq_tsum]
    exact tsum_comp_le_tsum_of_inj (w_summable_norm f) (fun _ => norm_nonneg _) neg_succ_injective
  calc ∑' k : ℕ, ‖wShiftFun hd f (k : ℤ)‖
      ≤ ∑' m : ℕ, (r₀ * (‖d‖ - r₀))⁻¹ ^ (m + 1) * ‖f (-(m + 1 : ℤ))‖ := hle1.trans_eq hcomm_sum
    _ ≤ (r₀ * (‖d‖ - r₀))⁻¹ * ∑' m : ℕ, ‖f (-(m + 1 : ℤ))‖ := hle2
    _ ≤ (r₀ * (‖d‖ - r₀))⁻¹ * ‖f‖ := mul_le_mul_of_nonneg_left hle3 (inv_nonneg.2 (by linarith))

lemma wEvalNonneg_wShift (hd : 1 < r₀ * (‖d‖ - r₀)) (f : W A) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    wEvalNonneg (wShift hd f) w = wEvalNeg f (d + w) := by
  have hd_gt : r₀ < ‖d‖ := by nlinarith [hr₀_pos]
  have hwd : ‖w‖ < ‖d‖ := lt_of_le_of_lt hw hd_gt
  have hprod_norm : Summable (fun p : ℕ × ℕ =>
      ‖(w ^ p.1 * ((-1 : ℂ) ^ p.1 * (Nat.choose (p.2 + p.1) p.1 : ℂ) *
        d⁻¹ ^ (p.2 + 1 + p.1))) • wCoeff f (-(p.2 + 1 : ℤ))‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (shift_summable_prod hd f)
    simp only [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hr₀_pos.le _),
      norm_pow]
    gcongr
  have hprod := hprod_norm.of_norm
  rw [wEvalNonneg]
  have hterm : ∀ k : ℕ, w ^ k • wCoeff (wShift hd f) k =
      ∑' m : ℕ, (w ^ k * ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) *
        d⁻¹ ^ (m + 1 + k))) • wCoeff f (-(m + 1 : ℤ)) := fun k => by
    have hrow := ((shift_summable_prod hd f).prod_factor k).of_norm
    rw [wCoeff, wShift, wOfSummable_apply, Int.natAbs_natCast]
    change w ^ k • ((r₀⁻¹ ^ k : ℝ) : ℂ) •
      (∑' m : ℕ, (((r₀ ^ k : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) *
        d⁻¹ ^ (m + 1 + k))) • wCoeff f (-(m + 1 : ℤ))) = _
    have h1 := (hrow.hasSum.const_smul (w ^ k * ((r₀⁻¹ ^ k : ℝ) : ℂ))).tsum_eq
    rw [smul_smul, ← h1]
    congr 1; funext m
    rw [smul_smul]
    congr 1
    have hcancel : ((r₀⁻¹ ^ k : ℝ) : ℂ) * ((r₀ ^ k : ℝ) : ℂ) = 1 := by
      norm_cast; rw [← mul_pow, inv_mul_cancel₀ hr₀_pos.ne', one_pow]
    calc w ^ k * ((r₀⁻¹ ^ k : ℝ) : ℂ) *
            (((r₀ ^ k : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) * d⁻¹ ^ (m + 1 + k)))
        = w ^ k * (((r₀⁻¹ ^ k : ℝ) : ℂ) * ((r₀ ^ k : ℝ) : ℂ)) *
            ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) * d⁻¹ ^ (m + 1 + k)) := by ring
      _ = w ^ k * ((-1 : ℂ) ^ k * (Nat.choose (m + k) k : ℂ) * d⁻¹ ^ (m + 1 + k)) := by
            rw [hcancel, mul_one]
  simp_rw [hterm]
  rw [← hprod.tsum_prod]
  rw [← Equiv.tsum_eq (Equiv.prodComm ℕ ℕ)]
  dsimp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  have hprod_swap := hprod.comp_injective (Equiv.prodComm ℕ ℕ).injective
  dsimp only [Function.comp_def, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at hprod_swap
  rw [hprod_swap.tsum_prod]
  rw [wEvalNeg]
  congr 1; funext m
  have hhs := (hasSum_shift_term hwd m).smul_const (wCoeff f (-(m + 1 : ℤ)))
  refine HasSum.tsum_eq ?_
  refine hhs.congr_fun fun k => ?_
  congr 1; ring

end ShiftOp

/- Section 4: Multi-disk splitting operators `Q_+` and `Q_-` on `Fin r → W A` -/

section MultiDisk

variable {r : ℕ}

noncomputable def center (r : ℕ) (i : Fin r) : ℂ := ((100 * r * i.1 : ℕ) : ℂ)

lemma dist_center_ge (hr : 1 ≤ r) {i j : Fin r} (hij : i ≠ j) :
    (100 * r : ℝ) ≤ ‖center r i - center r j‖ := by
  have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  rw [center, center]
  have hcast : ((100 * r * i.1 : ℕ) : ℂ) - ((100 * r * j.1 : ℕ) : ℂ) =
      (((100 * r * (i.1 : ℤ) - 100 * r * (j.1 : ℤ) : ℤ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hdiff : (1 : ℝ) ≤ |((i.1 : ℝ) - (j.1 : ℝ))| := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast (by omega : i.1 + 1 ≤ j.1)
      rw [abs_of_neg (by linarith)]; linarith
    · have h1 : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by exact_mod_cast (by omega : j.1 + 1 ≤ i.1)
      rw [abs_of_pos (by linarith)]; linarith
  have h1 : (100 * (r : ℝ)) * 1 ≤ |((100 * r * (i.1 : ℤ) - 100 * r * (j.1 : ℤ) : ℤ) : ℝ)| := by
    have hfac : ((100 * r * (i.1 : ℤ) - 100 * r * (j.1 : ℤ) : ℤ) : ℝ) =
        (100 * (r : ℝ)) * ((i.1 : ℝ) - (j.1 : ℝ)) := by push_cast; ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hdiff (by positivity)
  linarith

lemma shift_cond_center (hr : 1 ≤ r) {i j : Fin r} (hij : i ≠ j) :
    (100 * r : ℝ) ≤ r₀ * (‖center r i - center r j‖ - r₀) := by
  have hdist := dist_center_ge hr hij
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  rw [r₀] at *
  nlinarith

lemma shift_cond_gt_one (hr : 1 ≤ r) {i j : Fin r} (hij : i ≠ j) :
    1 < r₀ * (‖center r i - center r j‖ - r₀) := by
  have h := shift_cond_center hr hij
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  linarith

noncomputable def QNeg (hr : 1 ≤ r) (F : Fin r → W A) (i : Fin r) : W A :=
  wNeg (F i) + ∑ j : Fin r, if hij : i = j then 0 else wShift (shift_cond_gt_one hr hij) (F j)

noncomputable def QPos (hr : 1 ≤ r) (F : Fin r → W A) (i : Fin r) : W A :=
  F i - QNeg hr F i

lemma QPos_add_QNeg (hr : 1 ≤ r) (F : Fin r → W A) (i : Fin r) :
    QPos hr F i + QNeg hr F i = F i := sub_add_cancel _ _

lemma QPos_eq (hr : 1 ≤ r) (F : Fin r → W A) (i : Fin r) :
    QPos hr F i = wPos (F i) -
      ∑ j : Fin r, if hij : i = j then 0 else wShift (shift_cond_gt_one hr hij) (F j) := by
  rw [QPos, QNeg]
  have h := wPos_add_wNeg (F i)
  calc F i - (wNeg (F i) + ∑ j : Fin r, if hij : i = j then 0 else wShift (shift_cond_gt_one hr hij) (F j))
      = (wPos (F i) + wNeg (F i)) -
          (wNeg (F i) + ∑ j : Fin r, if hij : i = j then 0 else wShift (shift_cond_gt_one hr hij) (F j)) := by
            rw [h]
    _ = wPos (F i) - ∑ j : Fin r, if hij : i = j then 0 else wShift (shift_cond_gt_one hr hij) (F j) := by
            abel

lemma isNonneg_QPos (hr : 1 ≤ r) (F : Fin r → W A) (i : Fin r) :
    IsNonneg (QPos hr F i) := by
  rw [QPos_eq]
  intro n hn
  simp only [lp.coeFn_sub, Pi.sub_apply, isNonneg_wPos (F i) n hn, zero_sub, neg_eq_zero]
  have hsum : ∀ (s : Finset (Fin r)),
      (∑ j ∈ s, if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (F j)) n = 0 := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, lp.coeFn_add, Pi.add_apply, ih, add_zero]
      split_ifs with h
      · simp
      · exact isNonneg_wShift _ _ n hn
  exact hsum Finset.univ

lemma QPos_sub (hr : 1 ≤ r) (F G : Fin r → W A) (i : Fin r) :
    QPos hr (F - G) i = QPos hr F i - QPos hr G i := by
  rw [QPos_eq, QPos_eq, QPos_eq, Pi.sub_apply, wPos_sub]
  have hsum : (∑ j : Fin r, if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) ((F - G) j)) =
      (∑ j : Fin r, if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (F j)) -
      (∑ j : Fin r, if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (G j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp
    · exact wShift_sub _ (F j) (G j)
  rw [hsum]; abel

lemma norm_QPos_le (hr : 1 ≤ r) (F : Fin r → W A) :
    ‖QPos hr F‖ ≤ 2 * ‖F‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg F))]
  intro i
  rw [QPos_eq]
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 (by omega)
  have hsum_le : ‖∑ j : Fin r, if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (F j)‖ ≤
      ‖F‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j : Fin r,
        ‖if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (F j)‖ ≤
          (100 * (r : ℝ))⁻¹ * ‖F‖ := fun j => by
      split_ifs with hij
      · rw [norm_zero]; positivity
      · have h1 := norm_wShift_le (shift_cond_gt_one hr hij) (F j)
        have h2 : (r₀ * (‖center r i - center r j‖ - r₀))⁻¹ ≤ (100 * (r : ℝ))⁻¹ :=
          inv_anti₀ (by positivity) (shift_cond_center hr hij)
        have h3 : ‖F j‖ ≤ ‖F‖ := norm_le_pi_norm F j
        calc ‖wShift (shift_cond_gt_one hr hij) (F j)‖
            ≤ (r₀ * (‖center r i - center r j‖ - r₀))⁻¹ * ‖F j‖ := h1
          _ ≤ (100 * (r : ℝ))⁻¹ * ‖F‖ :=
              mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
    calc ∑ j : Fin r, ‖if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (F j)‖
        ≤ ∑ _j : Fin r, (100 * (r : ℝ))⁻¹ * ‖F‖ := Finset.sum_le_sum fun j _ => hterm j
      _ = (r : ℝ) * ((100 * (r : ℝ))⁻¹ * ‖F‖) := by simp
      _ = (100 : ℝ)⁻¹ * ‖F‖ := by field_simp
      _ ≤ ‖F‖ := by linarith [norm_nonneg F]
  calc ‖wPos (F i) - ∑ j : Fin r, if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (F j)‖
      ≤ ‖wPos (F i)‖ + ‖∑ j : Fin r, if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (F j)‖ :=
        norm_sub_le _ _
    _ ≤ ‖F‖ + ‖F‖ := add_le_add ((norm_wPos_le (F i)).trans (norm_le_pi_norm F i)) hsum_le
    _ = 2 * ‖F‖ := by ring

noncomputable def QNegGlob (F : Fin r → W A) (z : ℂ) : A :=
  ∑ j : Fin r, wEvalNeg (F j) (z - center r j)

lemma wEval_QNeg_eq_QNegGlob (hr : 1 ≤ r) (F : Fin r → W A) (i : Fin r) {z : ℂ}
    (hlo : r₀⁻¹ ≤ ‖z - center r i‖) (hhi : ‖z - center r i‖ ≤ r₀) :
    wEval (QNeg hr F i) (z - center r i) = QNegGlob F z := by
  rw [QNeg, wEval_add _ _ hlo hhi, QNegGlob]
  have hterm1 : wEval (wNeg (F i)) (z - center r i) = wEvalNeg (F i) (z - center r i) := by
    rw [← wEvalNeg_eq_wEval (isStrictNeg_wNeg (F i)) hlo hhi]
    rw [wEvalNeg, wEvalNeg]
    congr 1; funext m
    have hlt : -(m + 1 : ℤ) < 0 := by omega
    simp only [wCoeff, wNeg, wOfSummable_apply, if_pos hlt]
  have hsum : wEval (∑ j : Fin r, if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (F j))
      (z - center r i) =
      ∑ j : Fin r, if i = j then 0 else wEvalNeg (F j) (z - center r j) := by
    rw [show wEval (∑ j : Fin r, if hij : i = j then (0 : W A) else wShift (shift_cond_gt_one hr hij) (F j))
        (z - center r i) = (wEvalCLM (z - center r i) hlo hhi) _ from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp
    · change wEval (wShift (shift_cond_gt_one hr hij) (F j)) (z - center r i) = _
      rw [← wEvalNonneg_eq_wEval (isNonneg_wShift _ _) hlo hhi,
        wEvalNonneg_wShift (shift_cond_gt_one hr hij) (F j) hhi]
      congr 1; ring
  rw [hterm1, hsum, ← Finset.add_sum_erase Finset.univ (fun j => wEvalNeg (F j) (z - center r j))
    (Finset.mem_univ i)]
  congr 1
  rw [← Finset.add_sum_erase Finset.univ (fun j => if i = j then (0 : A) else wEvalNeg (F j) (z - center r j))
    (Finset.mem_univ i)]
  simp only [ite_true, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_neg (Finset.ne_of_mem_erase hj).symm]

end MultiDisk

end WeightedLaurent

end StrategyBPart1a

namespace StrategyBPart1b
open scoped BigOperators Topology NNReal ENNReal
open Filter Set Metric

/- 1. Cauchy estimate -> entire function with O(1 + |z|^r) bound is a polynomial of degree ≤ r -/

lemma exists_poly_of_entire_poly_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℕ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖ ^ r)) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, p.eval z = f z := by
  have hderiv0 : ∀ n : ℕ, r < n → iteratedDeriv n f 0 = 0 := by
    intro n hn
    rw [← norm_eq_zero]
    refine le_antisymm ?_ (norm_nonneg _)
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    rw [zero_add]
    -- Choose R ≥ max 1 (2 * n! * C / δ + 1)
    let R : ℝ := max 1 (2 * (n.factorial : ℝ) * C / δ + 1)
    have hR1 : 1 ≤ R := le_max_left _ _
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hRbig : 2 * (n.factorial : ℝ) * C / δ < R := by
      have h1 : 2 * (n.factorial : ℝ) * C / δ + 1 ≤ R := le_max_right _ _
      linarith
    have hsphere : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ 2 * C * R ^ r := by
      intro z hz
      have hzn : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
      have h1 : (1 : ℝ) ≤ R ^ r := one_le_pow₀ hR1
      calc ‖f z‖ ≤ C * (1 + ‖z‖ ^ r) := hC z
        _ = C * (1 + R ^ r) := by rw [hzn]
        _ ≤ C * (R ^ r + R ^ r) := by gcongr
        _ = 2 * C * R ^ r := by ring
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hRpos
      hf.diffContOnCl hsphere
    have hpow : R ^ r * R ≤ R ^ n := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hR1 (by omega)
    have hRn : 0 < R ^ n := pow_pos hRpos n
    calc ‖iteratedDeriv n f 0‖
        ≤ (n.factorial : ℝ) * (2 * C * R ^ r) / R ^ n := hcauchy
      _ ≤ (n.factorial : ℝ) * (2 * C * R ^ r) / (R ^ r * R) := by
          gcongr
      _ = 2 * (n.factorial : ℝ) * C / R := by
          have hRr : R ^ r ≠ 0 := (pow_pos hRpos r).ne'
          field_simp
      _ ≤ δ := by
          rw [div_le_iff₀ hRpos]
          have hmul := (div_lt_iff₀ hδ).1 hRbig
          linarith
  let p : Polynomial ℂ :=
    ∑ n ∈ Finset.range (r + 1), Polynomial.C ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0) * Polynomial.X ^ n
  refine ⟨p, fun z => ?_⟩
  rw [← Complex.taylorSeries_eq_of_entire' hf (c := 0) (z := z)]
  simp only [sub_zero, p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [tsum_eq_sum (s := Finset.range (r + 1))]
  intro n hn
  rw [Finset.mem_range] at hn
  rw [hderiv0 n (by omega), mul_zero, zero_mul]

/- 2. Differentiability of inverse in a NormedRing -/

lemma differentiableOn_inv_of_normedRing {A : Type*} [NormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {U : Set ℂ} (hU : IsOpen U) {g h : ℂ → A}
    (hg : DifferentiableOn ℂ g U) (hh_cont : ContinuousOn h U)
    (hgh : ∀ z ∈ U, g z * h z = 1) (hhg : ∀ z ∈ U, h z * g z = 1) :
    DifferentiableOn ℂ h U := by
  intro z hz
  have hgz : DifferentiableAt ℂ g z := hg.differentiableAt (hU.mem_nhds hz)
  have hhz_cont : ContinuousAt h z := hh_cont.continuousAt (hU.mem_nhds hz)
  have hslope_g : Tendsto (fun w : ℂ => (w - z)⁻¹ • (g w - g z)) (𝓝[≠] z) (𝓝 (deriv g z)) := by
    have h1 := hasDerivAt_iff_tendsto_slope.1 hgz.hasDerivAt
    exact h1.congr fun w => slope_def_module g z w
  have hslope_h : Tendsto (fun w : ℂ => (w - z)⁻¹ • (h w - h z)) (𝓝[≠] z)
      (𝓝 (-(h z * deriv g z * h z))) := by
    have h_ev : (fun w : ℂ => (w - z)⁻¹ • (h w - h z)) =ᶠ[𝓝[≠] z]
        (fun w : ℂ => -(h z * ((w - z)⁻¹ • (g w - g z)) * h w)) := by
      filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hz)] with w hw
      have hdiff : h w - h z = -(h z * (g w - g z) * h w) := by
        calc h w - h z = (h z * g z) * h w - h z * (g w * h w) := by
              rw [hhg z hz, hgh w hw, one_mul, mul_one]
          _ = -(h z * (g w - g z) * h w) := by noncomm_ring
      rw [hdiff, smul_neg, mul_smul_comm, smul_mul_assoc]
    have htend : Tendsto (fun w : ℂ => -(h z * ((w - z)⁻¹ • (g w - g z)) * h w)) (𝓝[≠] z)
        (𝓝 (-(h z * deriv g z * h z))) := by
      have hhw : Tendsto h (𝓝[≠] z) (𝓝 (h z)) := hhz_cont.tendsto.mono_left nhdsWithin_le_nhds
      exact (((tendsto_const_nhds.mul hslope_g).mul hhw).neg)
    exact htend.congr' h_ev.symm
  have hhasDeriv : HasDerivAt h (-(h z * deriv g z * h z)) z := by
    rw [hasDerivAt_iff_tendsto_slope]
    exact hslope_h.congr fun w => (slope_def_module h z w).symm
  exact hhasDeriv.differentiableAt.differentiableWithinAt

/- 3. Log series and log(u⁻¹) = -log u on Re > 0 -/

lemma complex_exp_tsum_logSeries {u : ℂ} (hu : ‖u‖ < 1) :
    Complex.exp (∑' m : ℕ, ((m + 1 : ℂ)⁻¹ * u ^ (m + 1))) = (1 - u)⁻¹ := by
  have hhs := Complex.hasSum_taylorSeries_neg_log' hu
  have hts : ∑' m : ℕ, ((m + 1 : ℂ)⁻¹ * u ^ (m + 1)) = -Complex.log (1 - u) := by
    rw [← hhs.tsum_eq]
    congr 1; funext m; ring
  have hne : 1 - u ≠ 0 := by
    intro h
    have h1 : u = 1 := (sub_eq_zero.1 h).symm
    rw [h1, norm_one] at hu
    exact lt_irrefl 1 hu
  rw [hts, Complex.exp_neg, Complex.exp_log hne]

lemma complex_log_inv_of_re_pos {u : ℂ} (hu : 0 < u.re) :
    Complex.log u⁻¹ = -Complex.log u := by
  have hu0 : u ≠ 0 := by intro h; rw [h, Complex.zero_re] at hu; linarith
  have harg : u.arg ≠ Real.pi := by
    intro hpi
    have hre := Complex.cos_arg hu0
    rw [hpi, Real.cos_pi] at hre
    have hpos : 0 < u.re / ‖u‖ := div_pos hu (norm_pos_iff.2 hu0)
    linarith
  apply Complex.ext
  · simp [Complex.log_re, Real.log_inv]
  · simp [Complex.log_im, Complex.arg_inv, if_neg harg]

/- 4. Analytic asymptotic vanishing lemma for IsDomain L -/

lemma re_div_pos_of_re_neg {w : ℂ} {ε : ℝ} (hw : w.re < 0) (hε : 0 < ε) :
    0 < (w / (w - (ε : ℂ))).re := by
  have hne : w - (ε : ℂ) ≠ 0 := by
    intro h
    have hre := congr_arg Complex.re h
    simp at hre
    linarith
  rw [Complex.div_re]
  have hnorm_pos : 0 < Complex.normSq (w - (ε : ℂ)) := Complex.normSq_pos.2 hne
  have hnum_pos : 0 < w.re * (w - (ε : ℂ)).re + w.im * (w - (ε : ℂ)).im := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    nlinarith
  have h1 : w.re * (w - (ε : ℂ)).re / Complex.normSq (w - (ε : ℂ)) +
      w.im * (w - (ε : ℂ)).im / Complex.normSq (w - (ε : ℂ)) =
      (w.re * (w - (ε : ℂ)).re + w.im * (w - (ε : ℂ)).im) / Complex.normSq (w - (ε : ℂ)) := by
    rw [← add_div]
  rw [h1]
  exact div_pos hnum_pos hnorm_pos

lemma forall_eq_zero_of_sum_psi_eq_zero {a ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1 / 4)
    {n : ℕ} (hn : 1 ≤ n)
    {f : Fin n → ℂ → ℂ}
    (hf : ∀ k : Fin n, DifferentiableOn ℂ (f k) (Metric.ball (a : ℂ) (5 / 4)))
    (hsum : ∀ z ∈ Metric.ball ((a : ℂ) - 1) (1 / 10),
      ∑ k : Fin n, f k z *
        (Complex.exp ((n : ℂ)⁻¹ * Complex.log ((z - (a : ℂ)) / (z - ((a : ℂ) + (ε : ℂ)))))) ^ k.1 = 0) :
    ∀ k : Fin n, ∀ z ∈ Metric.ball (a : ℂ) (5 / 4), f k z = 0 := by
  let ψ : ℂ → ℂ := fun z =>
    Complex.exp ((n : ℂ)⁻¹ * Complex.log ((z - (a : ℂ)) / (z - ((a : ℂ) + (ε : ℂ)))))
  let H : Set ℂ := {z : ℂ | z ∈ Metric.ball (a : ℂ) (5 / 4) ∧ (z - (a : ℂ)).re < 0}
  have hH_open : IsOpen H :=
    Metric.isOpen_ball.inter (isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const)) continuous_const)
  have hH_conv : Convex ℝ H := by
    refine (convex_ball (a : ℂ) (5 / 4)).inter ?_
    intro x hx y hy c d hc hd hcd
    change (c • x + d • y - (a : ℂ)).re < 0
    have hx' : (x - (a : ℂ)).re < 0 := hx
    have hy' : (y - (a : ℂ)).re < 0 := hy
    simp only [Complex.sub_re, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hx' hy' ⊢
    rcases hc.eq_or_lt with rfl | hc'
    · have hd1 : d = 1 := by linarith
      rw [hd1]; linarith
    · have h1 : c * (x.re - a) < 0 := mul_neg_of_pos_of_neg hc' hx'
      have h2 : d * (y.re - a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd hy'.le
      have h3 : c * x.re + d * y.re - a = c * (x.re - a) + d * (y.re - a) := by
        linear_combination a * hcd
      linarith
  have hH_conn : IsPreconnected H := hH_conv.isPreconnected
  have hB_sub : Metric.ball ((a : ℂ) - 1) (1 / 10) ⊆ H := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : ‖z - (a : ℂ)‖ < 5 / 4 := by
      have htri : z - (a : ℂ) = (z - ((a : ℂ) - 1)) + (-1) := by ring
      rw [htri]
      calc ‖(z - ((a : ℂ) - 1)) + (-1)‖ ≤ ‖z - ((a : ℂ) - 1)‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
        _ < 1 / 10 + 1 := by simp; linarith
        _ < 5 / 4 := by norm_num
    have h2 : (z - (a : ℂ)).re < 0 := by
      have habs : |(z - ((a : ℂ) - 1)).re| ≤ ‖z - ((a : ℂ) - 1)‖ := Complex.abs_re_le_norm _
      have hre : (z - ((a : ℂ) - 1)).re = (z - (a : ℂ)).re + 1 := by simp; ring
      rw [hre] at habs
      linarith [(abs_le.1 habs).2]
    exact ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact h1, h2⟩
  have hψ_diff : DifferentiableOn ℂ ψ H := by
    intro z hz
    have hre : 0 < ((z - (a : ℂ)) / (z - ((a : ℂ) + (ε : ℂ)))).re := by
      have heq : z - ((a : ℂ) + (ε : ℂ)) = (z - (a : ℂ)) - (ε : ℂ) := by ring
      rw [heq]; exact re_div_pos_of_re_neg hz.2 hε
    have hslit : (z - (a : ℂ)) / (z - ((a : ℂ) + (ε : ℂ))) ∈ Complex.slitPlane :=
      Or.inl hre
    have hne : z - ((a : ℂ) + (ε : ℂ)) ≠ 0 := by
      intro h0
      have hre0 := congr_arg Complex.re h0
      have hre_z : (z - (a : ℂ)).re < 0 := hz.2
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre0 hre_z
      linarith
    have hq : DifferentiableAt ℂ (fun w : ℂ => (w - (a : ℂ)) / (w - ((a : ℂ) + (ε : ℂ)))) z :=
      (differentiableAt_id.sub (differentiableAt_const _)).div
        (differentiableAt_id.sub (differentiableAt_const _)) hne
    have hlog : DifferentiableAt ℂ (fun w : ℂ => Complex.log ((w - (a : ℂ)) / (w - ((a : ℂ) + (ε : ℂ))))) z :=
      DifferentiableAt.comp (f := fun w : ℂ => (w - (a : ℂ)) / (w - ((a : ℂ) + (ε : ℂ))))
        (g := Complex.log) z (Complex.differentiableAt_log hslit) hq
    have hexp : DifferentiableAt ℂ ψ z :=
      DifferentiableAt.comp (g := Complex.exp) z Complex.differentiableAt_exp
        ((differentiableAt_const _).mul hlog)
    exact hexp.differentiableWithinAt
  have hF_diff : DifferentiableOn ℂ (fun z => ∑ k : Fin n, f k z * ψ z ^ k.1) H := by
    have h1 : DifferentiableOn ℂ (∑ k : Fin n, fun z => f k z * ψ z ^ k.1) H :=
      DifferentiableOn.sum fun k _ => ((hf k).mono (fun z hz => hz.1)).mul (hψ_diff.pow k.1)
    exact h1.congr fun z _ => by simp [Finset.sum_apply]
  have hF_anal : AnalyticOnNhd ℂ (fun z => ∑ k : Fin n, f k z * ψ z ^ k.1) H :=
    hF_diff.analyticOnNhd hH_open
  have hF_zero_H : ∀ z ∈ H, ∑ k : Fin n, f k z * ψ z ^ k.1 = 0 := by
    have hpt : (a : ℂ) - 1 ∈ H := hB_sub (Metric.mem_ball_self (by norm_num))
    have hev : (fun z => ∑ k : Fin n, f k z * ψ z ^ k.1) =ᶠ[𝓝 ((a : ℂ) - 1)] 0 := by
      filter_upwards [Metric.ball_mem_nhds ((a : ℂ) - 1) (by norm_num : (0 : ℝ) < 1 / 10)] with z hz
      exact hsum z hz
    exact fun z hz => hF_anal.eqOn_zero_of_preconnected_of_eventuallyEq_zero hH_conn hpt hev hz
  -- Now prove by contradiction that every f k ≡ 0 on Metric.ball a (5/4)
  by_contra hnot
  push Not at hnot
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun k => ∃ z ∈ Metric.ball (a : ℂ) (5 / 4), f k z ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨k, z, hz, hne⟩ := hnot
    exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, z, hz, hne⟩⟩
  have hord : ∀ k : Fin n, k ∈ S →
      ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g (a : ℂ) ∧ g (a : ℂ) ≠ 0 ∧
        ∀ᶠ z in 𝓝 (a : ℂ), f k z = (z - (a : ℂ)) ^ m * g z := by
    intro k hk
    have hanal_ball : AnalyticOnNhd ℂ (f k) (Metric.ball (a : ℂ) (5 / 4)) :=
      (hf k).analyticOnNhd Metric.isOpen_ball
    have ha_mem : (a : ℂ) ∈ Metric.ball (a : ℂ) (5 / 4) := Metric.mem_ball_self (by norm_num)
    have hanal_a : AnalyticAt ℂ (f k) (a : ℂ) := hanal_ball (a : ℂ) ha_mem
    have hnot_ev : ¬ (f k =ᶠ[𝓝 (a : ℂ)] 0) := by
      intro hev
      obtain ⟨z, hz, hne⟩ := (Finset.mem_filter.1 hk).2
      exact hne (hanal_ball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball _ _).isPreconnected ha_mem hev hz)
    obtain ⟨m, g, hg_an, hg_ne, hfg⟩ := hanal_a.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnot_ev
    exact ⟨m, g, hg_an, hg_ne, by simpa [smul_eq_mul] using hfg⟩
  -- Pick m_k, g_k for all k ∈ S
  let m : Fin n → ℕ := fun k => if hk : k ∈ S then (hord k hk).choose else 0
  let g : Fin n → ℂ → ℂ := fun k => if hk : k ∈ S then (hord k hk).choose_spec.choose else 0
  have hg_an : ∀ k ∈ S, AnalyticAt ℂ (g k) (a : ℂ) := fun k hk => by
    simp only [g, dif_pos hk]; exact (hord k hk).choose_spec.choose_spec.1
  have hg_ne : ∀ k ∈ S, g k (a : ℂ) ≠ 0 := fun k hk => by
    simp only [g, dif_pos hk]; exact (hord k hk).choose_spec.choose_spec.2.1
  have hfg : ∀ k ∈ S, ∀ᶠ z in 𝓝 (a : ℂ), f k z = (z - (a : ℂ)) ^ (m k) * g k z := fun k hk => by
    simp only [m, g, dif_pos hk]; exact (hord k hk).choose_spec.choose_spec.2.2
  have hf_off : ∀ k : Fin n, k ∉ S → ∀ z ∈ Metric.ball (a : ℂ) (5 / 4), f k z = 0 := by
    intro k hk z hz
    by_contra hne
    exact hk (Finset.mem_filter.2 ⟨Finset.mem_univ k, z, hz, hne⟩)
  -- Pick k₀ ∈ S minimizing n * m k + k.1
  obtain ⟨k₀, hk₀S, hk₀min⟩ := Finset.exists_min_image S (fun k => n * m k + k.1) hS
  have hk₀_strict : ∀ k ∈ S, k ≠ k₀ → n * m k₀ + k₀.1 < n * m k + k.1 := by
    intro k hk hne
    have hle := hk₀min k hk
    refine lt_of_le_of_ne hle fun heq => ?_
    have hmod := congr_arg (· % n) heq
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt k₀.2, Nat.mod_eq_of_lt k.2] at hmod
    exact hne (Fin.ext hmod.symm)
  -- Evaluate along z(s) = a - s^n for s ∈ (0, 1), s → 0⁺
  let zpath : ℝ → ℂ := fun s => (a : ℂ) - ((s ^ n : ℝ) : ℂ)
  have hzpath_tend : Tendsto zpath (𝓝[>] (0 : ℝ)) (𝓝 (a : ℂ)) := by
    have h1 : Tendsto (fun s : ℝ => s ^ n) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have h0 : (0 : ℝ) ^ n = 0 := zero_pow (by omega)
      have hc : Tendsto (fun s : ℝ => s ^ n) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ n)) :=
        (continuous_pow n).tendsto 0
      rw [h0] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun s : ℝ => ((s ^ n : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h1
    simpa [zpath] using tendsto_const_nhds.sub h2
  have hmem_H : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), zpath s ∈ H ∧ 0 < s ∧ s < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with s ⟨hs0, hs1⟩
    have hsn_pos : 0 < s ^ n := pow_pos hs0 n
    have hsn_lt : s ^ n < 1 := pow_lt_one₀ hs0.le hs1 (by omega)
    refine ⟨⟨?_, ?_⟩, hs0, hs1⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : zpath s - (a : ℂ) = -((s ^ n : ℝ) : ℂ) := by simp [zpath]
      rw [hdiff, norm_neg, Complex.norm_real, Real.norm_of_nonneg hsn_pos.le]
      linarith
    · have hre : (zpath s - (a : ℂ)).re = -(s ^ n) := by
        simp only [zpath, sub_sub_cancel_left, Complex.neg_re, Complex.ofReal_re]
      rw [hre]; linarith
  have hψ_path : ∀ s : ℝ, 0 < s → s < 1 →
      ψ (zpath s) = ((s * (s ^ n + ε) ^ (-(n : ℝ)⁻¹) : ℝ) : ℂ) := by
    intro s hs0 _
    have hsn_pos : 0 < s ^ n := pow_pos hs0 n
    have hden_pos : 0 < s ^ n + ε := by linarith
    have hquot : (zpath s - (a : ℂ)) / (zpath s - ((a : ℂ) + (ε : ℂ))) =
        ((s ^ n / (s ^ n + ε) : ℝ) : ℂ) := by
      have h1 : zpath s - (a : ℂ) = -((s ^ n : ℝ) : ℂ) := by simp [zpath]
      have h2 : zpath s - ((a : ℂ) + (ε : ℂ)) = -(((s ^ n + ε : ℝ) : ℂ)) := by
        simp [zpath]; ring
      rw [h1, h2, neg_div_neg_eq, Complex.ofReal_div]
    dsimp only [ψ]
    rw [hquot, ← Complex.ofReal_log (div_nonneg hsn_pos.le hden_pos.le)]
    have hcast : (n : ℂ)⁻¹ * ((Real.log (s ^ n / (s ^ n + ε)) : ℝ) : ℂ) =
        (((n : ℝ)⁻¹ * Real.log (s ^ n / (s ^ n + ε)) : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, ← Complex.ofReal_exp]
    congr 1
    rw [mul_comm, ← Real.rpow_def_of_pos (div_pos hsn_pos hden_pos),
      Real.div_rpow hsn_pos.le hden_pos.le,
      div_eq_mul_inv, ← Real.rpow_neg hden_pos.le]
    congr 1
    rw [← Real.rpow_natCast s n, ← Real.rpow_mul hs0.le,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 (by omega)), Real.rpow_one]
  let M : ℕ := n * m k₀ + k₀.1
  have hterm_tend : ∀ k ∈ S,
      Tendsto (fun s : ℝ => f k (zpath s) * ψ (zpath s) ^ k.1 / ((s : ℂ) ^ M))
        (𝓝[>] (0 : ℝ))
        (𝓝 (if k = k₀ then (-1 : ℂ) ^ m k₀ * g k₀ (a : ℂ) *
              (((ε ^ (-(n : ℝ)⁻¹)) ^ k₀.1 : ℝ) : ℂ) else 0)) := by
    intro k hk
    have hev_k : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
        f k (zpath s) * ψ (zpath s) ^ k.1 / ((s : ℂ) ^ M) =
        (-1 : ℂ) ^ m k * g k (zpath s) * ((((s ^ n + ε) ^ (-(n : ℝ)⁻¹)) ^ k.1 : ℝ) : ℂ) *
          ((s : ℂ) ^ (n * m k + k.1 - M)) := by
      filter_upwards [hmem_H, hzpath_tend.eventually (hfg k hk)] with s ⟨_, hs0, hs1⟩ hfk
      rw [hfk, hψ_path s hs0 hs1]
      have hdiff : zpath s - (a : ℂ) = (-1 : ℂ) * ((s : ℂ) ^ n) := by
        simp [zpath]
      rw [hdiff, mul_pow, ← pow_mul]
      have hcast_p : (((s * (s ^ n + ε) ^ (-(n : ℝ)⁻¹) : ℝ) : ℂ)) ^ k.1 =
          (s : ℂ) ^ k.1 * ((((s ^ n + ε) ^ (-(n : ℝ)⁻¹)) ^ k.1 : ℝ) : ℂ) := by
        push_cast; rw [mul_pow]
      rw [hcast_p]
      have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
      have hMle : M ≤ n * m k + k.1 := hk₀min k hk
      have hpow_split : (s : ℂ) ^ (n * m k) * (s : ℂ) ^ k.1 =
          (s : ℂ) ^ M * (s : ℂ) ^ (n * m k + k.1 - M) := by
        rw [← pow_add, ← pow_add, Nat.add_sub_of_le hMle]
      calc (-1 : ℂ) ^ m k * (s : ℂ) ^ (n * m k) * g k (zpath s) *
              ((s : ℂ) ^ k.1 * ((((s ^ n + ε) ^ (-(n : ℝ)⁻¹)) ^ k.1 : ℝ) : ℂ)) / (s : ℂ) ^ M
          = (-1 : ℂ) ^ m k * g k (zpath s) * ((((s ^ n + ε) ^ (-(n : ℝ)⁻¹)) ^ k.1 : ℝ) : ℂ) *
              (((s : ℂ) ^ (n * m k) * (s : ℂ) ^ k.1) / (s : ℂ) ^ M) := by ring
        _ = (-1 : ℂ) ^ m k * g k (zpath s) * ((((s ^ n + ε) ^ (-(n : ℝ)⁻¹)) ^ k.1 : ℝ) : ℂ) *
              (s : ℂ) ^ (n * m k + k.1 - M) := by
                rw [hpow_split, mul_div_cancel_left₀ _ (pow_ne_zero M hsne)]
    have hg_tend : Tendsto (fun s : ℝ => g k (zpath s)) (𝓝[>] (0 : ℝ)) (𝓝 (g k (a : ℂ))) :=
      (hg_an k hk).continuousAt.tendsto.comp hzpath_tend
    have hε_tend : Tendsto (fun s : ℝ => ((((s ^ n + ε) ^ (-(n : ℝ)⁻¹)) ^ k.1 : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((((ε ^ (-(n : ℝ)⁻¹)) ^ k.1 : ℝ) : ℂ))) := by
      have h1 : Tendsto (fun s : ℝ => s ^ n + ε) (𝓝[>] (0 : ℝ)) (𝓝 ε) := by
        have h0 : (0 : ℝ) ^ n = 0 := zero_pow (by omega)
        have hc : Tendsto (fun s : ℝ => s ^ n) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ n)) :=
          (continuous_pow n).tendsto 0
        rw [h0] at hc
        simpa using (hc.mono_left nhdsWithin_le_nhds).add (tendsto_const_nhds (x := ε))
      have h2 : Tendsto (fun s : ℝ => ((s ^ n + ε) ^ (-(n : ℝ)⁻¹)) ^ k.1) (𝓝[>] (0 : ℝ))
          (𝓝 ((ε ^ (-(n : ℝ)⁻¹)) ^ k.1)) :=
        (((Real.continuousAt_rpow_const ε (-(n : ℝ)⁻¹) (Or.inl hε.ne')).pow k.1).tendsto).comp h1
      exact (Complex.continuous_ofReal.tendsto _).comp h2
    have hpow_tend : Tendsto (fun s : ℝ => (s : ℂ) ^ (n * m k + k.1 - M)) (𝓝[>] (0 : ℝ))
        (𝓝 (if k = k₀ then 1 else 0)) := by
      split_ifs with heq
      · subst heq
        have h0 : n * m k + k.1 - M = 0 := Nat.sub_self M
        simp [h0]
      · have hpos : 0 < n * m k + k.1 - M := Nat.sub_pos_of_lt (hk₀_strict k hk heq)
        have h0 : (0 : ℂ) ^ (n * m k + k.1 - M) = 0 := zero_pow hpos.ne'
        have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
        have hp : Tendsto (fun z : ℂ => z ^ (n * m k + k.1 - M)) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
          simpa [h0] using (continuous_pow (n * m k + k.1 - M)).tendsto (0 : ℂ)
        exact hp.comp hc
    have hlim := (((tendsto_const_nhds (x := (-1 : ℂ) ^ m k)).mul hg_tend).mul hε_tend).mul hpow_tend
    refine (hlim.congr' (hev_k.mono fun s hs => hs.symm)).trans ?_
    split_ifs with heq
    · subst heq; simp
    · simp
  have hsum_tend := tendsto_finsetSum S hterm_tend
  have hsum_zero : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      (∑ k ∈ S, f k (zpath s) * ψ (zpath s) ^ k.1 / ((s : ℂ) ^ M)) = 0 := by
    filter_upwards [hmem_H] with s ⟨hsH, _, _⟩
    rw [← Finset.sum_div]
    have hall : ∑ k ∈ S, f k (zpath s) * ψ (zpath s) ^ k.1 =
        ∑ k : Fin n, f k (zpath s) * ψ (zpath s) ^ k.1 := by
      refine (Finset.sum_subset (Finset.subset_univ S) fun k _ hk => ?_)
      rw [hf_off k hk (zpath s) hsH.1, zero_mul]
    rw [hall, hF_zero_H (zpath s) hsH, zero_div]
  have hzero_tend : Tendsto (fun s : ℝ => ∑ k ∈ S, f k (zpath s) * ψ (zpath s) ^ k.1 / ((s : ℂ) ^ M))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hsum_zero.mono fun s hs => hs.symm)
  have heq0 := tendsto_nhds_unique hzero_tend hsum_tend
  rw [Finset.sum_ite_eq' S k₀, if_pos hk₀S] at heq0
  have hne_rhs : (-1 : ℂ) ^ m k₀ * g k₀ (a : ℂ) * (((ε ^ (-(n : ℝ)⁻¹)) ^ k₀.1 : ℝ) : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hg_ne k₀ hk₀S)) ?_
    exact Complex.ofReal_ne_zero.2 (pow_ne_zero _ (Real.rpow_pos_of_pos hε _).ne')
  exact hne_rhs heq0.symm

end StrategyBPart1b

namespace StrategyBPart1c

open scoped BigOperators Topology NNReal ENNReal
open Filter Set Metric StrategyBPart1a StrategyBPart1b

/- Section 1: Additional `W A`, `GroupAlg`, and Neumann-series helpers -/

lemma differentiableOn_finset_sum {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Finset ι} {f : ι → ℂ → E} {U : Set ℂ}
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun z => ∑ i ∈ s, f i z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h3 : (fun z => ∑ i ∈ insert a s, f i z) = (f a + fun z => ∑ i ∈ s, f i z) :=
      funext fun z => by simp [Finset.sum_insert ha]
    rw [h3]
    exact h1.add h2

section ExtraW

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

lemma wEvalNonneg_add (f g : W A) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    wEvalNonneg (f + g) w = wEvalNonneg f w + wEvalNonneg g w := by
  simp only [wEvalNonneg, wCoeff, lp.coeFn_add, Pi.add_apply, smul_add]
  exact (summable_wEvalNonneg f hw).tsum_add (summable_wEvalNonneg g hw)

lemma wEvalNonneg_sub (f g : W A) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    wEvalNonneg (f - g) w = wEvalNonneg f w - wEvalNonneg g w := by
  simp only [wEvalNonneg, wCoeff, lp.coeFn_sub, Pi.sub_apply, smul_sub]
  exact (summable_wEvalNonneg f hw).tsum_sub (summable_wEvalNonneg g hw)

lemma wEvalNonneg_smul (c : ℂ) (f : W A) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    wEvalNonneg (c • f) w = c • wEvalNonneg f w := by
  have h1 := ((summable_wEvalNonneg f hw).hasSum.const_smul c).tsum_eq
  rw [wEvalNonneg, wEvalNonneg, ← h1]
  congr 1; funext n
  simp only [wCoeff, lp.coeFn_smul, Pi.smul_apply]
  rw [smul_comm c, smul_comm c]

lemma wEvalNonneg_wPow {f : W A} (hf : IsNonneg f) (k : ℕ) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    wEvalNonneg (wPow f k) w = (wEvalNonneg f w) ^ k := by
  induction k with
  | zero => simp [wPow, wEvalNonneg_one]
  | succ k ih =>
    rw [wPow, pow_succ, wEvalNonneg_wMul (isNonneg_wPow hf k) hf hw, ih]

noncomputable def wEvalNonnegCLM (w : ℂ) (hw : ‖w‖ ≤ r₀) : W A →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := fun f => wEvalNonneg f w
      map_add' := fun f g => wEvalNonneg_add f g hw
      map_smul' := fun c f => wEvalNonneg_smul c f hw }
    1
    (fun f => by simpa using norm_wEvalNonneg_le f hw)

lemma wEvalNonneg_tsum {ι : Type*} (u : ι → W A) (hu : Summable u) {w : ℂ} (hw : ‖w‖ ≤ r₀) :
    wEvalNonneg (∑' k, u k) w = ∑' k, wEvalNonneg (u k) w :=
  (wEvalNonnegCLM w hw).map_tsum hu

noncomputable def wCoordCLM (n : ℤ) : W A →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := fun f => f n
      map_add' := fun f g => by simp
      map_smul' := fun c f => by simp }
    1
    (fun f => by
      change ‖f n‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact lp.norm_apply_le_norm (by norm_num) f n)

lemma w_apply_tsum {ι : Type*} (u : ι → W A) (hu : Summable u) (n : ℤ) :
    (∑' k, u k) n = ∑' k, (u k) n :=
  (wCoordCLM n).map_tsum hu

lemma isNonneg_tsum {ι : Type*} (u : ι → W A) (hu : Summable u) (hnn : ∀ k, IsNonneg (u k)) :
    IsNonneg (∑' k, u k) := by
  intro n hn
  rw [w_apply_tsum u hu n]
  have h0 : ∀ k, u k n = 0 := fun k => hnn k n hn
  simp_rw [h0]
  exact tsum_zero

lemma wEval_finset_sum {ι : Type*} (s : Finset ι) (u : ι → W A)
    {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (∑ k ∈ s, u k) w = ∑ k ∈ s, wEval (u k) w :=
  map_sum (wEvalCLM w hlo hhi) u s

end ExtraW

lemma summable_pow_of_norm_lt_one {A : Type*} [NormedRing A] [NormOneClass A] [CompleteSpace A]
    {u : A} (hu : ‖u‖ < 1) : Summable (fun m : ℕ => u ^ m) := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg u) hu) fun m => ?_
  cases m with
  | zero => simp
  | succ k => exact norm_pow_le' u (Nat.succ_pos k)

lemma one_sub_mul_tsum_pow {A : Type*} [NormedRing A] [NormOneClass A] [CompleteSpace A]
    {u : A} (hu : ‖u‖ < 1) :
    (1 - u) * (∑' m : ℕ, u ^ m) = 1 := by
  have hs := summable_pow_of_norm_lt_one hu
  have hmul : u * (∑' m : ℕ, u ^ m) = ∑' m : ℕ, u ^ (m + 1) := by
    rw [← (hs.hasSum.mul_left u).tsum_eq]
    congr 1; funext m; rw [pow_succ']
  rw [sub_mul, one_mul, hmul, hs.tsum_eq_zero_add, pow_zero, add_sub_cancel_right]

lemma tsum_pow_mul_one_sub {A : Type*} [NormedRing A] [NormOneClass A] [CompleteSpace A]
    {u : A} (hu : ‖u‖ < 1) :
    (∑' m : ℕ, u ^ m) * (1 - u) = 1 := by
  have hs := summable_pow_of_norm_lt_one hu
  have hmul : (∑' m : ℕ, u ^ m) * u = ∑' m : ℕ, u ^ (m + 1) := by
    rw [← (hs.hasSum.mul_right u).tsum_eq]
    congr 1; funext m; rw [pow_succ]
  rw [mul_sub, mul_one, hmul, hs.tsum_eq_zero_add, pow_zero, add_sub_cancel_right]

lemma norm_tsum_pow_le {A : Type*} [NormedRing A] [NormOneClass A] [CompleteSpace A]
    {u : A} (hu : ‖u‖ < 1) :
    ‖∑' m : ℕ, u ^ m‖ ≤ (1 - ‖u‖)⁻¹ := by
  have hgeom := summable_geometric_of_lt_one (norm_nonneg u) hu
  have hnorm : Summable (fun m : ℕ => ‖u ^ m‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => by cases m with | zero => simp | succ k => exact norm_pow_le' u (Nat.succ_pos k))
      hgeom
  calc ‖∑' m : ℕ, u ^ m‖ ≤ ∑' m : ℕ, ‖u ^ m‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, ‖u‖ ^ m := Summable.tsum_le_tsum
        (fun m => by cases m with | zero => simp | succ k => exact norm_pow_le' u (Nat.succ_pos k))
        hnorm hgeom
    _ = (1 - ‖u‖)⁻¹ := tsum_geometric_of_lt_one (norm_nonneg u) hu

section ExtraGroupAlg

variable {G : Type} [Fintype G] [Group G] [DecidableEq G]

noncomputable def coeffCLM (x : G) : GroupAlg G →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun c => c.coeff x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1
    (fun c => by simpa using GroupAlg.norm_coeff_le c x)

noncomputable def augCLM : GroupAlg G →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun c => GroupAlg.aug c
      map_add' := fun a b => GroupAlg.aug_add a b
      map_smul' := fun s a => GroupAlg.aug_smul s a }
    1
    (fun c => by simpa using GroupAlg.norm_aug_le c)

lemma aug_wMul_zero_of_left {d e : W (GroupAlg G)} (hd : ∀ n : ℤ, GroupAlg.aug (d n) = 0) (n : ℤ) :
    GroupAlg.aug ((wMul d e) n) = 0 := by
  rw [wMul_apply]
  change (augCLM (G := G)) (∑' k : ℤ, ((mulWeight n k : ℝ) : ℂ) • (d k * e (n - k))) = 0
  rw [augCLM.map_tsum (summable_wMul_row d e n)]
  have h0 : ∀ k : ℤ, (augCLM (G := G)) (((mulWeight n k : ℝ) : ℂ) • (d k * e (n - k))) = 0 := fun k => by
    change GroupAlg.aug (((mulWeight n k : ℝ) : ℂ) • (d k * e (n - k))) = 0
    rw [GroupAlg.aug_smul, GroupAlg.aug_mul, hd k, zero_mul, mul_zero]
  simp_rw [h0]
  exact tsum_zero

lemma aug_wEvalNeg_zero {f : W (GroupAlg G)} (hf : ∀ n : ℤ, GroupAlg.aug (f n) = 0)
    {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) :
    GroupAlg.aug (wEvalNeg f w) = 0 := by
  rw [wEvalNeg]
  change (augCLM (G := G)) (∑' m : ℕ, (w⁻¹) ^ (m + 1) • wCoeff f (-(m + 1 : ℤ))) = 0
  rw [augCLM.map_tsum (summable_wEvalNeg f hlo)]
  have h0 : ∀ m : ℕ, (augCLM (G := G)) ((w⁻¹) ^ (m + 1) • wCoeff f (-(m + 1 : ℤ))) = 0 := fun m => by
    change GroupAlg.aug ((w⁻¹) ^ (m + 1) • wCoeff f (-(m + 1 : ℤ))) = 0
    rw [wCoeff, GroupAlg.aug_smul, GroupAlg.aug_smul, hf _, mul_zero, mul_zero]
  simp_rw [h0]
  exact tsum_zero

lemma convAct_differentiableOn {U : Set ℂ} {B : ℂ → GroupAlg G} {v : G → ℂ → ℂ}
    (hB : DifferentiableOn ℂ B U) (hv : ∀ y : G, DifferentiableOn ℂ (v y) U) (x : G) :
    DifferentiableOn ℂ (fun z => GroupAlg.convAct (B z) (fun y => v y z) x) U := by
  simp only [GroupAlg.convAct]
  refine differentiableOn_finset_sum fun u _ => ?_
  have h1 : DifferentiableOn ℂ (fun z => (B z).coeff u) U := fun z hz =>
    (coeffCLM u).differentiableAt.comp_differentiableWithinAt z (hB z hz)
  exact h1.mul (hv (x * u))

lemma norm_convAct_le (c : GroupAlg G) (v : G → ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y : G, ‖v y‖ ≤ M) (x : G) :
    ‖GroupAlg.convAct c v x‖ ≤ ‖c‖ * M := by
  rw [GroupAlg.convAct, GroupAlg.norm_def, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM (x * u)) (norm_nonneg _)

def eBasis (x : G) : G → ℂ := fun y => if y = x then 1 else 0

lemma eBasis_expand (v : G → ℂ) (y : G) :
    v y = ∑ x : G, v x * eBasis x y := by
  rw [Finset.sum_eq_single y]
  · simp [eBasis]
  · intro x _ hx; simp [eBasis, hx.symm]
  · intro h; exact absurd (Finset.mem_univ y) h

lemma convAct_expand (c : GroupAlg G) (v : G → ℂ) (t : G) :
    GroupAlg.convAct c v t = ∑ x : G, v x * GroupAlg.convAct c (eBasis x) t := by
  simp only [GroupAlg.convAct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  calc c.coeff u * v (t * u) = c.coeff u * ∑ x : G, v x * eBasis x (t * u) := by
        rw [← eBasis_expand]
    _ = ∑ x : G, v x * (c.coeff u * eBasis x (t * u)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring

lemma rho_eBasis (h x : G) : GroupAlg.rho h (eBasis x) = eBasis (h * x) := by
  funext y
  simp only [GroupAlg.rho, eBasis]
  by_cases hy : h⁻¹ * y = x
  · rw [if_pos hy, if_pos (by rw [← hy, mul_inv_cancel_left])]
  · rw [if_neg hy, if_neg (fun heq => hy (by rw [heq, inv_mul_cancel_left]))]

end ExtraGroupAlg

/- Section 2: `logSeries`, `wExp`, and `wTensor` -/

noncomputable def logSeriesFun (ε : ℝ) (n : ℤ) : ℂ :=
  match n with
  | Int.ofNat _ => 0
  | Int.negSucc m => ((r₀ ^ (m + 1) : ℝ) : ℂ) * (((m + 1 : ℂ)⁻¹) * (ε : ℂ) ^ (m + 1))

lemma summable_logSeriesFun {ε : ℝ} (hε0 : 0 < ε) (hε : r₀ * ε < 1) :
    Summable (fun n : ℤ => ‖logSeriesFun ε n‖) := by
  have hr0 := hr₀_pos
  have hneg : Summable (fun m : ℕ => ‖logSeriesFun ε (Int.negSucc m)‖) := by
    have hgeom : Summable (fun m : ℕ => (r₀ * ε) ^ (m + 1)) :=
      (summable_geometric_of_lt_one (mul_nonneg hr0.le hε0.le) hε).comp_injective (fun _ _ h => by omega)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hgeom
    simp only [logSeriesFun, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hr0.le _),
      norm_inv, norm_pow, Real.norm_of_nonneg hε0.le]
    have h1m : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hle : ((m + 1 : ℝ))⁻¹ * ε ^ (m + 1) ≤ 1 * ε ^ (m + 1) :=
      mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ h1m) (pow_nonneg hε0.le _)
    calc r₀ ^ (m + 1) * (‖(m + 1 : ℂ)‖⁻¹ * ε ^ (m + 1))
        = r₀ ^ (m + 1) * (((m + 1 : ℝ))⁻¹ * ε ^ (m + 1)) := by
            congr 2; have : (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; rfl
            rw [this, Complex.norm_natCast]; push_cast; rfl
      _ ≤ r₀ ^ (m + 1) * (1 * ε ^ (m + 1)) := mul_le_mul_of_nonneg_left hle (pow_nonneg hr0.le _)
      _ = (r₀ * ε) ^ (m + 1) := by rw [one_mul, mul_pow]
  refine (summable_int_iff_summable_nat_and_neg.2 ⟨?_, ?_⟩)
  · have h0 : (fun k : ℕ => ‖logSeriesFun ε (k : ℤ)‖) = fun _ => 0 := by
      funext k; change ‖logSeriesFun ε (Int.ofNat k)‖ = 0; simp [logSeriesFun]
    rw [h0]; exact summable_zero
  · have h1 : Summable (fun m : ℕ => ‖logSeriesFun ε (-(m + 1 : ℤ))‖) := by
      refine hneg.congr fun m => ?_
      congr 2
    rw [← summable_nat_add_iff 1]
    refine h1.congr fun m => ?_
    congr 2

noncomputable def logSeries {ε : ℝ} (hε0 : 0 < ε) (hε : r₀ * ε < 1) : W ℂ :=
  wOfSummable (logSeriesFun ε) (summable_logSeriesFun hε0 hε)

lemma norm_logSeries_le {ε : ℝ} (hε0 : 0 < ε) (hε : r₀ * ε ≤ 1 / 2) :
    ‖logSeries hε0 (lt_of_le_of_lt hε (by norm_num))‖ ≤ 2 * r₀ * ε := by
  have hr0 := hr₀_pos
  have hε_lt : r₀ * ε < 1 := lt_of_le_of_lt hε (by norm_num)
  rw [w_norm_eq_tsum]
  have hzero : ∀ n : ℤ, n ∉ Set.range (fun m : ℕ => (-(m + 1 : ℤ))) →
      ‖logSeries hε0 hε_lt n‖ = 0 := by
    intro n hn
    cases n with
    | ofNat k => change ‖logSeriesFun ε (Int.ofNat k)‖ = 0; simp [logSeriesFun]
    | negSucc m => exact absurd ⟨m, rfl⟩ hn
  rw [← tsum_subtype_eq_of_support_subset (s := Set.range (fun m : ℕ => (-(m + 1 : ℤ))))
    (fun n hn => by by_contra hnot; exact hn (hzero n hnot))]
  rw [← Equiv.tsum_eq (Equiv.ofInjective (fun m : ℕ => (-(m + 1 : ℤ))) neg_succ_injective)
    (fun x : Set.range (fun m : ℕ => (-(m + 1 : ℤ))) => ‖logSeries hε0 hε_lt x‖)]
  have hgeom : Summable (fun m : ℕ => (r₀ * ε) ^ (m + 1)) :=
    (summable_geometric_of_lt_one (mul_nonneg hr0.le hε0.le) hε_lt).comp_injective (fun _ _ h => by omega)
  have hle : ∀ m : ℕ, ‖logSeries hε0 hε_lt (-(m + 1 : ℤ))‖ ≤ (r₀ * ε) ^ (m + 1) := by
    intro m
    change ‖logSeriesFun ε (Int.negSucc m)‖ ≤ (r₀ * ε) ^ (m + 1)
    simp only [logSeriesFun, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hr0.le _),
      norm_inv, norm_pow, Real.norm_of_nonneg hε0.le]
    have hnormm : ‖(m + 1 : ℂ)‖ = (m + 1 : ℝ) := by
      have : (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_natCast]; push_cast; rfl
    rw [hnormm]
    have h1m : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hinv : ((m + 1 : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1m
    calc r₀ ^ (m + 1) * (((m + 1 : ℝ))⁻¹ * ε ^ (m + 1))
        ≤ r₀ ^ (m + 1) * (1 * ε ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv (pow_nonneg hε0.le _)) (pow_nonneg hr0.le _)
      _ = (r₀ * ε) ^ (m + 1) := by rw [one_mul, mul_pow]
  have hsub : Summable (fun m : ℕ => ‖logSeries hε0 hε_lt (-(m + 1 : ℤ))‖) :=
    (w_summable_norm _).comp_injective neg_succ_injective
  have hsum_eq : (∑' m : ℕ, (r₀ * ε) ^ (m + 1)) = (r₀ * ε) * (1 - r₀ * ε)⁻¹ := by
    have h1 : (fun m : ℕ => (r₀ * ε) ^ (m + 1)) = fun m => (r₀ * ε) * (r₀ * ε) ^ m := by
      funext m; rw [pow_succ']
    rw [h1, tsum_mul_left, tsum_geometric_of_lt_one (mul_nonneg hr0.le hε0.le) hε_lt]
  calc ∑' m : ℕ, ‖logSeries hε0 hε_lt ((Equiv.ofInjective _ neg_succ_injective) m)‖
      ≤ ∑' m : ℕ, (r₀ * ε) ^ (m + 1) := by
        refine Summable.tsum_le_tsum (fun m => hle m) hsub hgeom
    _ = (r₀ * ε) * (1 - r₀ * ε)⁻¹ := hsum_eq
    _ ≤ (r₀ * ε) * 2 := by
        have hinv_le : (1 - r₀ * ε)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        exact mul_le_mul_of_nonneg_left hinv_le (mul_nonneg hr0.le hε0.le)
    _ = 2 * r₀ * ε := by ring

lemma wEval_logSeries {ε : ℝ} (hε0 : 0 < ε) (hε : r₀ * ε < 1) {w : ℂ}
    (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (logSeries hε0 hε) w = -Complex.log (1 - (ε : ℂ) / w) := by
  have hw0 : w ≠ 0 := by intro hz; rw [hz, norm_zero] at hlo; linarith [hr₀_inv_pos]
  rw [wEval]
  have hzero : ∀ n : ℤ, n ∉ Set.range (fun m : ℕ => (-(m + 1 : ℤ))) →
      w ^ n • wCoeff (logSeries hε0 hε) n = 0 := by
    intro n hn
    cases n with
    | ofNat k =>
      change w ^ (k : ℤ) • (((r₀⁻¹ ^ k : ℝ) : ℂ) • logSeriesFun ε (Int.ofNat k)) = 0
      simp [logSeriesFun]
    | negSucc m => exact absurd ⟨m, rfl⟩ hn
  rw [← tsum_subtype_eq_of_support_subset (s := Set.range (fun m : ℕ => (-(m + 1 : ℤ))))
    (fun n hn => by by_contra hnot; exact hn (hzero n hnot))]
  rw [← Equiv.tsum_eq (Equiv.ofInjective (fun m : ℕ => (-(m + 1 : ℤ))) neg_succ_injective)
    (fun x : Set.range (fun m : ℕ => (-(m + 1 : ℤ))) => w ^ (x : ℤ) • wCoeff (logSeries hε0 hε) x)]
  have hterm : ∀ m : ℕ,
      w ^ (-(m + 1 : ℤ)) • wCoeff (logSeries hε0 hε) (-(m + 1 : ℤ)) =
      ((ε : ℂ) / w) ^ (m + 1) / (m + 1 : ℂ) := by
    intro m
    have hnat : (-(m + 1 : ℤ)).natAbs = m + 1 := by omega
    rw [wCoeff, hnat]
    change w ^ (-(m + 1 : ℤ)) * (((r₀⁻¹ ^ (m + 1) : ℝ) : ℂ) * logSeriesFun ε (Int.negSucc m)) = _
    simp only [logSeriesFun]
    have hr0_cancel : ((r₀⁻¹ ^ (m + 1) : ℝ) : ℂ) * ((r₀ ^ (m + 1) : ℝ) : ℂ) = 1 := by
      norm_cast; rw [← mul_pow, inv_mul_cancel₀ hr₀_pos.ne', one_pow]
    have hwpow : w ^ (-(m + 1 : ℤ)) = (w⁻¹) ^ (m + 1) := by
      have hm1 : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [zpow_neg, hm1, zpow_natCast, inv_pow]
    rw [← mul_assoc ((r₀⁻¹ ^ (m + 1) : ℝ) : ℂ), hr0_cancel, one_mul, hwpow, div_eq_mul_inv,
      div_eq_mul_inv, mul_pow]
    ring
  have hnorm_lt : ‖(ε : ℂ) / w‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hε0.le]
    have hinv : ‖w‖⁻¹ ≤ r₀ := (inv_le_comm₀ (lt_of_lt_of_le hr₀_inv_pos hlo) hr₀_pos).2 hlo
    calc ε / ‖w‖ = ε * ‖w‖⁻¹ := div_eq_mul_inv _ _
      _ ≤ ε * r₀ := mul_le_mul_of_nonneg_left hinv hε0.le
      _ = r₀ * ε := mul_comm _ _
      _ < 1 := hε
  have hhs := Complex.hasSum_taylorSeries_neg_log' hnorm_lt
  rw [← hhs.tsum_eq]
  congr 1; funext m
  exact hterm m

noncomputable def wExp (x : W ℂ) : W ℂ :=
  ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • wPow x m

lemma summable_norm_wExp {x : W ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    Summable (fun m : ℕ => ‖((m.factorial : ℂ)⁻¹) • wPow x m‖) := by
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_geometric_of_lt_one (norm_nonneg x) hx1)
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hfac : (m.factorial : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos m)
  calc (m.factorial : ℝ)⁻¹ * ‖wPow x m‖ ≤ 1 * ‖x‖ ^ m :=
        mul_le_mul hfac (norm_wPow_le x m) (norm_nonneg _) zero_le_one
    _ = ‖x‖ ^ m := one_mul _

lemma summable_wExp {x : W ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    Summable (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • wPow x m) :=
  (summable_norm_wExp hx).of_norm

lemma wExp_zero : wExp (0 : W ℂ) = wOne := by
  rw [wExp, tsum_eq_single 0]
  · simp [wPow]
  · intro m hm
    cases m with
    | zero => exact absurd rfl hm
    | succ k => simp [wPow, wMul_zero]

lemma norm_wExp_sub_one_le {x : W ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    ‖wExp x - wOne‖ ≤ 2 * ‖x‖ := by
  have hs := summable_wExp hx
  have hsn := summable_norm_wExp hx
  have hsub : wExp x - wOne = ∑' m : ℕ, (((m + 1).factorial : ℂ)⁻¹) • wPow x (m + 1) := by
    rw [wExp, hs.tsum_eq_zero_add]
    simp [wPow]
  rw [hsub]
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  have hgeom : Summable (fun m : ℕ => ‖x‖ ^ (m + 1)) :=
    (summable_geometric_of_lt_one (norm_nonneg x) hx1).comp_injective (fun _ _ h => by omega)
  have hsn' : Summable (fun m : ℕ => ‖(((m + 1).factorial : ℂ)⁻¹) • wPow x (m + 1)‖) :=
    hsn.comp_injective (fun _ _ h => by omega)
  have hsum_eq : (∑' m : ℕ, ‖x‖ ^ (m + 1)) = ‖x‖ * (1 - ‖x‖)⁻¹ := by
    have h1 : (fun m : ℕ => ‖x‖ ^ (m + 1)) = fun m => ‖x‖ * ‖x‖ ^ m := by
      funext m; rw [pow_succ']
    rw [h1, tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg x) hx1]
  calc ‖∑' m : ℕ, (((m + 1).factorial : ℂ)⁻¹) • wPow x (m + 1)‖
      ≤ ∑' m : ℕ, ‖(((m + 1).factorial : ℂ)⁻¹) • wPow x (m + 1)‖ := norm_tsum_le_tsum_norm hsn'
    _ ≤ ∑' m : ℕ, ‖x‖ ^ (m + 1) := by
        refine Summable.tsum_le_tsum (fun m => ?_) hsn' hgeom
        rw [norm_smul, norm_inv, Complex.norm_natCast]
        have hfac : ((m + 1).factorial : ℝ)⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (m + 1))
        exact (mul_le_mul hfac (norm_wPow_le x (m + 1)) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
    _ = ‖x‖ * (1 - ‖x‖)⁻¹ := hsum_eq
    _ ≤ ‖x‖ * 2 := by
        have hinv : (1 - ‖x‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        exact mul_le_mul_of_nonneg_left hinv (norm_nonneg x)
    _ = 2 * ‖x‖ := mul_comm _ _

lemma wEval_wExp {x : W ℂ} (hx : ‖x‖ ≤ 1 / 2) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (wExp x) w = Complex.exp (wEval x w) := by
  rw [wExp, wEval_tsum _ (summable_wExp hx) hlo hhi]
  have hexp : Complex.exp (wEval x w) = ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) * (wEval x w) ^ m := by
    simpa [smul_eq_mul] using
      congr_fun (Complex.exp_eq_exp_ℂ.trans (NormedSpace.exp_eq_tsum (𝕂 := ℂ))) (wEval x w)
  rw [hexp]
  congr 1; funext m
  rw [wEval_smul _ _ hlo hhi, wEval_wPow _ _ hlo hhi, smul_eq_mul]

section Tensor

variable {G : Type} [Fintype G] [Group G] [DecidableEq G]

noncomputable def wTensor (f : W ℂ) (c : GroupAlg G) : W (GroupAlg G) :=
  wOfSummable (fun n : ℤ => f n • c) (by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((w_summable_norm f).mul_right ‖c‖)
    rw [norm_smul])

lemma wTensor_apply (f : W ℂ) (c : GroupAlg G) (n : ℤ) :
    wTensor f c n = f n • c := rfl

lemma norm_wTensor_le (f : W ℂ) (c : GroupAlg G) :
    ‖wTensor f c‖ ≤ ‖f‖ * ‖c‖ := by
  rw [w_norm_eq_tsum, w_norm_eq_tsum, ← tsum_mul_right]
  refine le_of_eq ?_
  congr 1; funext n
  exact norm_smul (f n) c

lemma wTensor_sub (f g : W ℂ) (c : GroupAlg G) :
    wTensor (f - g) c = wTensor f c - wTensor g c := by
  ext n; simp [wTensor_apply, sub_smul]

lemma wTensor_zero (c : GroupAlg G) : wTensor 0 c = 0 := by
  ext n; simp [wTensor_apply]

lemma aug_wTensor (f : W ℂ) (c : GroupAlg G) (n : ℤ) :
    GroupAlg.aug (wTensor f c n) = f n * GroupAlg.aug c := by
  rw [wTensor_apply, GroupAlg.aug_smul]

lemma sum_wTensor_wOne {ι : Type*} (s : Finset ι) (c : ι → GroupAlg G) (hsum : ∑ k ∈ s, c k = 1) :
    ∑ k ∈ s, wTensor (wOne : W ℂ) (c k) = (wOne : W (GroupAlg G)) := by
  ext n
  have heval : ∀ (t : Finset ι), (∑ k ∈ t, wTensor (wOne : W ℂ) (c k)) n =
      ∑ k ∈ t, wTensor (wOne : W ℂ) (c k) n := by
    intro t
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, lp.coeFn_add, Pi.add_apply, ih]
  rw [heval s]
  simp only [wTensor_apply, wOne_apply]
  split_ifs with hn
  · simp [hsum]
  · simp

lemma wEval_wTensor (f : W ℂ) (c : GroupAlg G) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (A := GroupAlg G) (wTensor f c) w = (wEval (A := ℂ) f w) • c := by
  rw [wEval, wEval, ← (summable_wEval f hlo hhi).tsum_smul_const c]
  refine tsum_congr fun n => ?_
  rw [wCoeff, wCoeff, wTensor_apply]
  change w ^ n • (((r₀⁻¹ ^ n.natAbs : ℝ) : ℂ) • (f n • c)) = (w ^ n * (((r₀⁻¹ ^ n.natAbs : ℝ) : ℂ) * f n)) • c
  rw [smul_smul, smul_smul, mul_assoc]

end Tensor

/- Section 3: Analytic Patching & Construction of the `RatFunc ℂ`-Algebra `LAlg G` -/

section ComplexRealization

variable (G : Type) [Fintype G] [Group G] [DecidableEq G]

noncomputable def rCard : ℕ := Fintype.card G

lemma hrCard : 1 ≤ rCard G := Fintype.card_pos

noncomputable def eG : Fin (rCard G) ≃ G := (Fintype.equivFin G).symm

noncomputable def gElem (i : Fin (rCard G)) : G := eG G i

noncomputable def εVal : ℝ := (100 * ((rCard G : ℝ) ^ 2))⁻¹

lemma hεVal_pos : 0 < εVal G := by
  rw [εVal]
  have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
  positivity

lemma hεVal_mul_r₀_le : r₀ * εVal G ≤ (80 * (rCard G : ℝ) ^ 2)⁻¹ := by
  rw [εVal, r₀]
  have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
  have hpos : (0 : ℝ) < (rCard G : ℝ) ^ 2 := by positivity
  rw [mul_inv, show (5 / 4 : ℝ) * ((100 : ℝ)⁻¹ * ((rCard G : ℝ) ^ 2)⁻¹) =
      (80 * (rCard G : ℝ) ^ 2)⁻¹ by field_simp; ring]

lemma hεVal_mul_r₀_le_half : r₀ * εVal G ≤ 1 / 2 := by
  have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
  have h1 : (1 : ℝ) ≤ (rCard G : ℝ) ^ 2 := by nlinarith
  have h2 : (80 * (rCard G : ℝ) ^ 2)⁻¹ ≤ (80 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) (by linarith)
  linarith [hεVal_mul_r₀_le G]

lemma hεVal_mul_r₀_lt_one : r₀ * εVal G < 1 :=
  lt_of_le_of_lt (hεVal_mul_r₀_le_half G) (by norm_num)

lemma hεVal_lt_quarter : εVal G < 1 / 4 := by
  have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
  have h1 : (1 : ℝ) ≤ (rCard G : ℝ) ^ 2 := by nlinarith
  have h2 : (80 * (rCard G : ℝ) ^ 2)⁻¹ ≤ (80 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) (by linarith)
  have h3 := hεVal_mul_r₀_le G
  rw [r₀] at h3
  linarith

noncomputable def logSer : W ℂ :=
  logSeries (hεVal_pos G) (hεVal_mul_r₀_lt_one G)

lemma norm_logSer_le : ‖logSer G‖ ≤ (40 * (rCard G : ℝ) ^ 2)⁻¹ := by
  rw [logSer]
  have h1 := norm_logSeries_le (hεVal_pos G) (hεVal_mul_r₀_le_half G)
  have h2 := hεVal_mul_r₀_le G
  have heq : 2 * (80 * (rCard G : ℝ) ^ 2)⁻¹ = (40 * (rCard G : ℝ) ^ 2)⁻¹ := by
    have hr : (0 : ℝ) < rCard G := by exact_mod_cast hrCard G
    field_simp; ring
  linarith

noncomputable def phiPowArg (i : Fin (rCard G)) (k : Fin (orderOf (gElem G i))) : W ℂ :=
  (((k.1 : ℂ) / (orderOf (gElem G i) : ℂ))) • logSer G

lemma norm_phiPowArg_le (i : Fin (rCard G)) (k : Fin (orderOf (gElem G i))) :
    ‖phiPowArg G i k‖ ≤ (40 * (rCard G : ℝ) ^ 2)⁻¹ := by
  rw [phiPowArg, norm_smul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hle1 : (k.1 : ℝ) / (orderOf (gElem G i) : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < orderOf (gElem G i) := by
      exact_mod_cast GroupAlg.orderOf_pos_of_fintype (gElem G i)
    rw [div_le_one hpos]
    exact_mod_cast k.2.le
  calc (k.1 : ℝ) / (orderOf (gElem G i) : ℝ) * ‖logSer G‖
      ≤ 1 * (40 * (rCard G : ℝ) ^ 2)⁻¹ :=
        mul_le_mul hle1 (norm_logSer_le G) (norm_nonneg _) zero_le_one
    _ = (40 * (rCard G : ℝ) ^ 2)⁻¹ := one_mul _

lemma norm_phiPowArg_le_half (i : Fin (rCard G)) (k : Fin (orderOf (gElem G i))) :
    ‖phiPowArg G i k‖ ≤ 1 / 2 := by
  have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
  have h1 : (40 * (rCard G : ℝ) ^ 2)⁻¹ ≤ (40 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) (by nlinarith)
  linarith [norm_phiPowArg_le G i k]

noncomputable def phiPowSer (i : Fin (rCard G)) (k : Fin (orderOf (gElem G i))) : W ℂ :=
  wExp (phiPowArg G i k)

lemma norm_phiPowSer_sub_one_le (i : Fin (rCard G)) (k : Fin (orderOf (gElem G i))) :
    ‖phiPowSer G i k - wOne‖ ≤ (20 * (rCard G : ℝ) ^ 2)⁻¹ := by
  rw [phiPowSer]
  have h1 := norm_wExp_sub_one_le (norm_phiPowArg_le_half G i k)
  have h2 := norm_phiPowArg_le G i k
  have hr : (0 : ℝ) < rCard G := by exact_mod_cast hrCard G
  have heq : 2 * (40 * (rCard G : ℝ) ^ 2)⁻¹ = (20 * (rCard G : ℝ) ^ 2)⁻¹ := by
    field_simp; ring
  linarith

noncomputable def phiVal (i : Fin (rCard G)) (w : ℂ) : ℂ :=
  Complex.exp ((orderOf (gElem G i) : ℂ)⁻¹ * (-Complex.log (1 - (εVal G : ℂ) / w)))

lemma wEval_phiPowSer (i : Fin (rCard G)) (k : Fin (orderOf (gElem G i)))
    {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (phiPowSer G i k) w = (phiVal G i w) ^ k.1 := by
  rw [phiPowSer, wEval_wExp (norm_phiPowArg_le_half G i k) hlo hhi, phiPowArg,
    wEval_smul _ _ hlo hhi, smul_eq_mul, logSer, wEval_logSeries _ _ hlo hhi, phiVal,
    ← Complex.exp_nat_mul]
  congr 1; ring

lemma phiVal_pow_orderOf (i : Fin (rCard G)) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) :
    (phiVal G i w) ^ (orderOf (gElem G i)) = w / (w - (εVal G : ℂ)) := by
  have hw0 : w ≠ 0 := by intro hz; rw [hz, norm_zero] at hlo; linarith [hr₀_inv_pos]
  have hn_ne : (orderOf (gElem G i) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (GroupAlg.orderOf_pos_of_fintype (gElem G i)).ne'
  rw [phiVal, ← Complex.exp_nat_mul, ← mul_assoc, mul_inv_cancel₀ hn_ne, one_mul]
  have hnorm_lt : ‖(εVal G : ℂ) / w‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hεVal_pos G).le]
    have hinv : ‖w‖⁻¹ ≤ r₀ := (inv_le_comm₀ (lt_of_lt_of_le hr₀_inv_pos hlo) hr₀_pos).2 hlo
    calc εVal G / ‖w‖ = εVal G * ‖w‖⁻¹ := div_eq_mul_inv _ _
      _ ≤ εVal G * r₀ := mul_le_mul_of_nonneg_left hinv (hεVal_pos G).le
      _ = r₀ * εVal G := mul_comm _ _
      _ < 1 := hεVal_mul_r₀_lt_one G
  have hne1 : 1 - (εVal G : ℂ) / w ≠ 0 := by
    intro h
    have heq : (εVal G : ℂ) / w = 1 := (sub_eq_zero.1 h).symm
    rw [heq, norm_one] at hnorm_lt
    exact lt_irrefl 1 hnorm_lt
  rw [Complex.exp_neg, Complex.exp_log hne1]
  have hne2 : w - (εVal G : ℂ) ≠ 0 := by
    intro h; apply hne1
    rw [sub_eq_zero.1 h, div_self (Complex.ofReal_ne_zero.2 (hεVal_pos G).ne'), sub_self]
  field_simp

noncomputable def MSer (i : Fin (rCard G)) : W (GroupAlg G) :=
  ∑ k : Fin (orderOf (gElem G i)), wTensor (phiPowSer G i k) (GroupAlg.idem (gElem G i) k)

noncomputable def ΔSer (i : Fin (rCard G)) : W (GroupAlg G) :=
  MSer G i - wOne

lemma ΔSer_eq_sum (i : Fin (rCard G)) :
    ΔSer G i = ∑ k : Fin (orderOf (gElem G i)),
      wTensor (phiPowSer G i k - wOne) (GroupAlg.idem (gElem G i) k) := by
  rw [ΔSer, MSer]
  have h1 : (wOne : W (GroupAlg G)) =
      ∑ k : Fin (orderOf (gElem G i)), wTensor (wOne : W ℂ) (GroupAlg.idem (gElem G i) k) :=
    (sum_wTensor_wOne Finset.univ _ (GroupAlg.sum_idem (gElem G i))).symm
  conv_lhs => rw [h1]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => (wTensor_sub _ _ _).symm

lemma norm_ΔSer_apply_le (i : Fin (rCard G)) :
    ‖ΔSer G i‖ ≤ (20 * (rCard G : ℝ))⁻¹ := by
  rw [ΔSer_eq_sum]
  have hord_le : (orderOf (gElem G i) : ℝ) ≤ (rCard G : ℝ) := by
    exact_mod_cast orderOf_le_card_univ (x := gElem G i)
  have hr_pos : (0 : ℝ) < rCard G := by exact_mod_cast hrCard G
  calc ‖∑ k : Fin (orderOf (gElem G i)),
          wTensor (phiPowSer G i k - wOne) (GroupAlg.idem (gElem G i) k)‖
      ≤ ∑ k : Fin (orderOf (gElem G i)),
          ‖wTensor (phiPowSer G i k - wOne) (GroupAlg.idem (gElem G i) k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin (orderOf (gElem G i)), (20 * (rCard G : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc ‖wTensor (phiPowSer G i k - wOne) (GroupAlg.idem (gElem G i) k)‖
            ≤ ‖phiPowSer G i k - wOne‖ * ‖GroupAlg.idem (gElem G i) k‖ := norm_wTensor_le _ _
          _ ≤ (20 * (rCard G : ℝ) ^ 2)⁻¹ * 1 :=
              mul_le_mul (norm_phiPowSer_sub_one_le G i k)
                (GroupAlg.norm_idem_le (gElem G i) k) (norm_nonneg _) (by positivity)
          _ = (20 * (rCard G : ℝ) ^ 2)⁻¹ := mul_one _
    _ = (orderOf (gElem G i) : ℝ) * (20 * (rCard G : ℝ) ^ 2)⁻¹ := by simp
    _ ≤ (rCard G : ℝ) * (20 * (rCard G : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hord_le (by positivity)
    _ = (20 * (rCard G : ℝ))⁻¹ := by field_simp

lemma aug_ΔSer (i : Fin (rCard G)) (n : ℤ) :
    GroupAlg.aug ((ΔSer G i) n) = 0 := by
  rw [ΔSer_eq_sum]
  have heval : (∑ k : Fin (orderOf (gElem G i)),
      wTensor (phiPowSer G i k - wOne) (GroupAlg.idem (gElem G i) k)) n =
      ∑ k : Fin (orderOf (gElem G i)),
        wTensor (phiPowSer G i k - wOne) (GroupAlg.idem (gElem G i) k) n := by
    change (wCoordCLM n) _ = _; rw [map_sum]; rfl
  rw [heval, GroupAlg.aug_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [aug_wTensor]
  by_cases hk0 : k.1 = 0
  · have harg0 : phiPowArg G i k = 0 := by simp [phiPowArg, hk0]
    have hphi1 : phiPowSer G i k = wOne := by rw [phiPowSer, harg0, wExp_zero]
    rw [hphi1, sub_self]; simp
  · rw [GroupAlg.aug_idem, if_neg hk0, mul_zero]

lemma wEval_MSer (i : Fin (rCard G)) {w : ℂ} (hlo : r₀⁻¹ ≤ ‖w‖) (hhi : ‖w‖ ≤ r₀) :
    wEval (MSer G i) w = GroupAlg.mElem (gElem G i) (phiVal G i w) := by
  rw [MSer, wEval_finset_sum _ _ hlo hhi, GroupAlg.mElem]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wEval_wTensor _ _ hlo hhi, wEval_phiPowSer G i k hlo hhi]

/- Contraction operator T and unique fixed point FSol -/

noncomputable def TOp (F : Fin (rCard G) → W (GroupAlg G)) : Fin (rCard G) → W (GroupAlg G) :=
  fun i => ΔSer G i - wMul (ΔSer G i) (QPos (hrCard G) F i)

lemma contracting_TOp : ContractingWith ⟨1 / 4, by norm_num⟩ (TOp G) := by
  refine ⟨by exact_mod_cast (by norm_num : (1 / 4 : ℝ) < 1), LipschitzWith.of_dist_le_mul fun F₁ F₂ => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  change ‖TOp G F₁ - TOp G F₂‖ ≤ (1 / 4 : ℝ) * ‖F₁ - F₂‖
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))]
  intro i
  have hdiff : (TOp G F₁ - TOp G F₂) i = -(wMul (ΔSer G i) (QPos (hrCard G) (F₁ - F₂) i)) := by
    simp only [Pi.sub_apply, TOp, QPos_sub, wMul_sub]
    abel
  rw [hdiff, norm_neg]
  have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
  have hΔ : ‖ΔSer G i‖ ≤ (20 : ℝ)⁻¹ :=
    (norm_ΔSer_apply_le G i).trans (inv_anti₀ (by norm_num) (by linarith))
  have hQ : ‖QPos (hrCard G) (F₁ - F₂) i‖ ≤ 2 * ‖F₁ - F₂‖ :=
    (norm_le_pi_norm _ i).trans (norm_QPos_le (hrCard G) (F₁ - F₂))
  calc ‖wMul (ΔSer G i) (QPos (hrCard G) (F₁ - F₂) i)‖
      ≤ ‖ΔSer G i‖ * ‖QPos (hrCard G) (F₁ - F₂) i‖ := norm_wMul_le _ _
    _ ≤ (20 : ℝ)⁻¹ * (2 * ‖F₁ - F₂‖) := mul_le_mul hΔ hQ (norm_nonneg _) (by norm_num)
    _ ≤ (1 / 4 : ℝ) * ‖F₁ - F₂‖ := by linarith [norm_nonneg (F₁ - F₂)]

noncomputable def FSol : Fin (rCard G) → W (GroupAlg G) :=
  (contracting_TOp G).fixedPoint (TOp G)

lemma FSol_eq (i : Fin (rCard G)) :
    FSol G i = ΔSer G i - wMul (ΔSer G i) (QPos (hrCard G) (FSol G) i) :=
  congr_fun (contracting_TOp G).fixedPoint_isFixedPt.symm i

lemma norm_FSol_le : ‖FSol G‖ ≤ (18 * (rCard G : ℝ))⁻¹ := by
  have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
  have hstep : ‖FSol G‖ ≤ (20 * (rCard G : ℝ))⁻¹ + (1 / 10 : ℝ) * ‖FSol G‖ := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [FSol_eq G i]
    have hΔ1 : ‖ΔSer G i‖ ≤ (20 * (rCard G : ℝ))⁻¹ := norm_ΔSer_apply_le G i
    have hΔ2 : ‖ΔSer G i‖ ≤ (20 : ℝ)⁻¹ := hΔ1.trans (inv_anti₀ (by norm_num) (by linarith))
    have hQ : ‖QPos (hrCard G) (FSol G) i‖ ≤ 2 * ‖FSol G‖ :=
      (norm_le_pi_norm _ i).trans (norm_QPos_le (hrCard G) (FSol G))
    calc ‖ΔSer G i - wMul (ΔSer G i) (QPos (hrCard G) (FSol G) i)‖
        ≤ ‖ΔSer G i‖ + ‖wMul (ΔSer G i) (QPos (hrCard G) (FSol G) i)‖ := norm_sub_le _ _
      _ ≤ (20 * (rCard G : ℝ))⁻¹ + ‖ΔSer G i‖ * ‖QPos (hrCard G) (FSol G) i‖ :=
          add_le_add hΔ1 (norm_wMul_le _ _)
      _ ≤ (20 * (rCard G : ℝ))⁻¹ + (20 : ℝ)⁻¹ * (2 * ‖FSol G‖) :=
          add_le_add le_rfl (mul_le_mul hΔ2 hQ (norm_nonneg _) (by norm_num))
      _ = (20 * (rCard G : ℝ))⁻¹ + (1 / 10 : ℝ) * ‖FSol G‖ := by ring
  have hr_pos : (0 : ℝ) < rCard G := by linarith
  have heq : (9 / 10 : ℝ) * (18 * (rCard G : ℝ))⁻¹ = (20 * (rCard G : ℝ))⁻¹ := by
    field_simp; ring
  linarith

lemma norm_QPos_FSol_le (i : Fin (rCard G)) :
    ‖QPos (hrCard G) (FSol G) i‖ ≤ 1 / 9 := by
  have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
  have h1 : ‖QPos (hrCard G) (FSol G) i‖ ≤ 2 * (18 * (rCard G : ℝ))⁻¹ :=
    ((norm_le_pi_norm _ i).trans (norm_QPos_le (hrCard G) (FSol G))).trans
      (mul_le_mul_of_nonneg_left (norm_FSol_le G) (by norm_num))
  have h2 : (18 * (rCard G : ℝ))⁻¹ ≤ (18 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
  linarith

lemma aug_FSol (i : Fin (rCard G)) (n : ℤ) :
    GroupAlg.aug ((FSol G i) n) = 0 := by
  rw [FSol_eq G i]
  change GroupAlg.aug ((ΔSer G i) n - (wMul (ΔSer G i) (QPos (hrCard G) (FSol G) i)) n) = 0
  rw [GroupAlg.aug_sub, aug_ΔSer G i n, aug_wMul_zero_of_left (aug_ΔSer G i) n, sub_zero]

/- Local factors A_i, A_i⁻¹ on D_i and global factor B_0, B_0⁻¹ on U_0 -/

noncomputable def ASer (i : Fin (rCard G)) : W (GroupAlg G) :=
  wOne - QPos (hrCard G) (FSol G) i

lemma isNonneg_ASer (i : Fin (rCard G)) : IsNonneg (ASer G i) := by
  intro n hn
  simp only [ASer, lp.coeFn_sub, Pi.sub_apply, isNonneg_wOne n hn,
    isNonneg_QPos (hrCard G) (FSol G) i n hn, sub_self]

lemma summable_wPow_QPos (i : Fin (rCard G)) :
    Summable (fun m : ℕ => wPow (QPos (hrCard G) (FSol G) i) m) := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 9 : ℝ) < 1))
    fun m => (norm_wPow_le _ m).trans (pow_le_pow_left₀ (norm_nonneg _) (norm_QPos_FSol_le G i) m)

noncomputable def AInvSer (i : Fin (rCard G)) : W (GroupAlg G) :=
  ∑' m : ℕ, wPow (QPos (hrCard G) (FSol G) i) m

lemma isNonneg_AInvSer (i : Fin (rCard G)) : IsNonneg (AInvSer G i) :=
  isNonneg_tsum _ (summable_wPow_QPos G i) (fun m => isNonneg_wPow (isNonneg_QPos _ _ i) m)

noncomputable def AFun (i : Fin (rCard G)) (z : ℂ) : GroupAlg G :=
  wEvalNonneg (ASer G i) (z - center (rCard G) i)

noncomputable def AInvFun (i : Fin (rCard G)) (z : ℂ) : GroupAlg G :=
  wEvalNonneg (AInvSer G i) (z - center (rCard G) i)

lemma differentiableOn_AFun (i : Fin (rCard G)) :
    DifferentiableOn ℂ (AFun G i) (Metric.ball (center (rCard G) i) r₀) := by
  refine (differentiableOn_wEvalNonneg (ASer G i)).comp
    (differentiableOn_id.sub (differentiableOn_const _)) fun z hz => ?_
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  exact mem_ball_iff_norm.1 hz

lemma differentiableOn_AInvFun (i : Fin (rCard G)) :
    DifferentiableOn ℂ (AInvFun G i) (Metric.ball (center (rCard G) i) r₀) := by
  refine (differentiableOn_wEvalNonneg (AInvSer G i)).comp
    (differentiableOn_id.sub (differentiableOn_const _)) fun z hz => ?_
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  exact mem_ball_iff_norm.1 hz

lemma AFun_mul_AInvFun (i : Fin (rCard G)) {z : ℂ} (hz : z ∈ Metric.ball (center (rCard G) i) r₀) :
    AFun G i z * AInvFun G i z = 1 := by
  have hw : ‖z - center (rCard G) i‖ ≤ r₀ := (mem_ball_iff_norm.1 hz).le
  rw [AFun, AInvFun, ASer, AInvSer, wEvalNonneg_sub _ _ hw, wEvalNonneg_one,
    wEvalNonneg_tsum _ (summable_wPow_QPos G i) hw]
  have heq : (∑' m : ℕ, wEvalNonneg (wPow (QPos (hrCard G) (FSol G) i) m) (z - center (rCard G) i)) =
      ∑' m : ℕ, (wEvalNonneg (QPos (hrCard G) (FSol G) i) (z - center (rCard G) i)) ^ m := by
    congr 1; funext m
    exact wEvalNonneg_wPow (isNonneg_QPos _ _ i) m hw
  rw [heq]
  exact one_sub_mul_tsum_pow ((norm_wEvalNonneg_le _ hw).trans_lt ((norm_QPos_FSol_le G i).trans_lt (by norm_num)))

lemma AInvFun_mul_AFun (i : Fin (rCard G)) {z : ℂ} (hz : z ∈ Metric.ball (center (rCard G) i) r₀) :
    AInvFun G i z * AFun G i z = 1 := by
  have hw : ‖z - center (rCard G) i‖ ≤ r₀ := (mem_ball_iff_norm.1 hz).le
  rw [AFun, AInvFun, ASer, AInvSer, wEvalNonneg_sub _ _ hw, wEvalNonneg_one,
    wEvalNonneg_tsum _ (summable_wPow_QPos G i) hw]
  have heq : (∑' m : ℕ, wEvalNonneg (wPow (QPos (hrCard G) (FSol G) i) m) (z - center (rCard G) i)) =
      ∑' m : ℕ, (wEvalNonneg (QPos (hrCard G) (FSol G) i) (z - center (rCard G) i)) ^ m := by
    congr 1; funext m
    exact wEvalNonneg_wPow (isNonneg_QPos _ _ i) m hw
  rw [heq]
  exact tsum_pow_mul_one_sub ((norm_wEvalNonneg_le _ hw).trans_lt ((norm_QPos_FSol_le G i).trans_lt (by norm_num)))

def U0 : Set ℂ := {z : ℂ | ∀ j : Fin (rCard G), r₀⁻¹ < ‖z - center (rCard G) j‖}

lemma isOpen_U0 : IsOpen (U0 G) := by
  have heq : U0 G = ⋂ j : Fin (rCard G), {z : ℂ | r₀⁻¹ < ‖z - center (rCard G) j‖} := by
    ext z; simp [U0]
  rw [heq]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))

noncomputable def BFun (z : ℂ) : GroupAlg G :=
  1 + QNegGlob (FSol G) z

noncomputable def BInvFun (z : ℂ) : GroupAlg G :=
  ∑' m : ℕ, (-QNegGlob (FSol G) z) ^ m

lemma norm_QNegGlob_FSol_le {z : ℂ} (hz : z ∈ U0 G) :
    ‖QNegGlob (FSol G) z‖ ≤ 1 / 18 := by
  rw [QNegGlob]
  have hr_pos : (0 : ℝ) < rCard G := by exact_mod_cast hrCard G
  calc ‖∑ j : Fin (rCard G), wEvalNeg (FSol G j) (z - center (rCard G) j)‖
      ≤ ∑ j : Fin (rCard G), ‖wEvalNeg (FSol G j) (z - center (rCard G) j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (rCard G), (18 * (rCard G : ℝ))⁻¹ := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact (norm_wEvalNeg_le _ (hz j).le).trans ((norm_le_pi_norm _ j).trans (norm_FSol_le G))
    _ = (rCard G : ℝ) * (18 * (rCard G : ℝ))⁻¹ := by simp
    _ = 1 / 18 := by field_simp

lemma norm_BFun_le {z : ℂ} (hz : z ∈ U0 G) : ‖BFun G z‖ ≤ 2 := by
  rw [BFun]
  calc ‖1 + QNegGlob (FSol G) z‖ ≤ ‖(1 : GroupAlg G)‖ + ‖QNegGlob (FSol G) z‖ := norm_add_le _ _
    _ ≤ 1 + 1 / 18 := by rw [norm_one]; linarith [norm_QNegGlob_FSol_le G hz]
    _ ≤ 2 := by norm_num

lemma norm_BInvFun_le {z : ℂ} (hz : z ∈ U0 G) : ‖BInvFun G z‖ ≤ 2 := by
  rw [BInvFun]
  have hlt : ‖-QNegGlob (FSol G) z‖ < 1 := by
    rw [norm_neg]; linarith [norm_QNegGlob_FSol_le G hz]
  have h1 := norm_tsum_pow_le hlt
  have h2 : (1 - ‖-QNegGlob (FSol G) z‖)⁻¹ ≤ 2 := by
    rw [norm_neg]
    rw [inv_le_comm₀ (by linarith [norm_QNegGlob_FSol_le G hz]) (by norm_num)]
    linarith [norm_QNegGlob_FSol_le G hz]
  exact h1.trans h2

lemma BFun_mul_BInvFun {z : ℂ} (hz : z ∈ U0 G) :
    BFun G z * BInvFun G z = 1 := by
  have heq : BFun G z = 1 - (-QNegGlob (FSol G) z) := by simp [BFun]
  rw [heq, BInvFun]
  exact one_sub_mul_tsum_pow (by rw [norm_neg]; linarith [norm_QNegGlob_FSol_le G hz])

lemma BInvFun_mul_BFun {z : ℂ} (hz : z ∈ U0 G) :
    BInvFun G z * BFun G z = 1 := by
  have heq : BFun G z = 1 - (-QNegGlob (FSol G) z) := by simp [BFun]
  rw [heq, BInvFun]
  exact tsum_pow_mul_one_sub (by rw [norm_neg]; linarith [norm_QNegGlob_FSol_le G hz])

lemma aug_BFun {z : ℂ} (hz : z ∈ U0 G) : GroupAlg.aug (BFun G z) = 1 := by
  rw [BFun, GroupAlg.aug_add, GroupAlg.aug_one, QNegGlob, GroupAlg.aug_sum]
  have h0 : ∑ j : Fin (rCard G), GroupAlg.aug (wEvalNeg (FSol G j) (z - center (rCard G) j)) = 0 :=
    Finset.sum_eq_zero fun j _ => aug_wEvalNeg_zero (aug_FSol G j) (hz j).le
  rw [h0, add_zero]

lemma differentiableOn_BFun : DifferentiableOn ℂ (BFun G) (U0 G) := by
  refine (differentiableOn_const (1 : GroupAlg G)).add ?_
  change DifferentiableOn ℂ (fun z => ∑ j : Fin (rCard G), wEvalNeg (FSol G j) (z - center (rCard G) j)) (U0 G)
  refine differentiableOn_finset_sum fun j _ => ?_
  refine (differentiableOn_wEvalNeg (FSol G j)).comp
    (differentiableOn_id.sub (differentiableOn_const _)) fun z hz => ?_
  exact hz j

lemma continuousOn_BInvFun : ContinuousOn (BInvFun G) (U0 G) := by
  have hQ_cont : ContinuousOn (fun z => -QNegGlob (FSol G) z) (U0 G) := by
    have hB : ContinuousOn (BFun G) (U0 G) := (differentiableOn_BFun G).continuousOn
    have heq : (fun z => -QNegGlob (FSol G) z) = fun z => 1 - BFun G z := by
      funext z; rw [BFun]; abel
    rw [heq]
    exact continuousOn_const.sub hB
  refine continuousOn_tsum (u := fun m : ℕ => (1 / 18 : ℝ) ^ m)
    (fun m => hQ_cont.pow m)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (fun m z hz => ?_)
  cases m with
  | zero => simp
  | succ k =>
    refine (norm_pow_le' _ (Nat.succ_pos k)).trans ?_
    rw [norm_neg]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_QNegGlob_FSol_le G hz) _

lemma differentiableOn_BInvFun : DifferentiableOn ℂ (BInvFun G) (U0 G) :=
  differentiableOn_inv_of_normedRing (isOpen_U0 G) (differentiableOn_BFun G)
    (continuousOn_BInvFun G) (fun _ hz => BFun_mul_BInvFun G hz) (fun _ hz => BInvFun_mul_BFun G hz)

/- Patching identity on U0 ∩ D_i -/

lemma patching_on_overlap (i : Fin (rCard G)) {z : ℂ}
    (hz0 : z ∈ U0 G) (hzi : z ∈ Metric.ball (center (rCard G) i) r₀) :
    BFun G z = GroupAlg.mElem (gElem G i) (phiVal G i (z - center (rCard G) i)) * AFun G i z := by
  have hlo : r₀⁻¹ ≤ ‖z - center (rCard G) i‖ := (hz0 i).le
  have hhi : ‖z - center (rCard G) i‖ ≤ r₀ := (mem_ball_iff_norm.1 hzi).le
  have halg : wMul (MSer G i) (ASer G i) = wOne + QNeg (hrCard G) (FSol G) i := by
    have hM : MSer G i = wOne + ΔSer G i := by rw [ΔSer]; abel
    rw [hM, ASer, add_wMul, wMul_sub, wMul_sub, one_wMul, one_wMul, wMul_one]
    have hF := FSol_eq G i
    have hQ := QPos_add_QNeg (hrCard G) (FSol G) i
    calc (wOne - QPos (hrCard G) (FSol G) i) + (ΔSer G i - wMul (ΔSer G i) (QPos (hrCard G) (FSol G) i))
        = wOne + (FSol G i - QPos (hrCard G) (FSol G) i) := by rw [← hF]; abel
      _ = wOne + QNeg (hrCard G) (FSol G) i := by rw [← hQ]; abel
  have heval := congr_arg (fun f => wEval f (z - center (rCard G) i)) halg
  rw [wEval_wMul _ _ hlo hhi, wEval_MSer G i hlo hhi,
    ← wEvalNonneg_eq_wEval (isNonneg_ASer G i) hlo hhi,
    wEval_add _ _ hlo hhi, wEval_one, wEval_QNeg_eq_QNegGlob (hrCard G) (FSol G) i hlo hhi] at heval
  exact heval.symm

/- Section 4: Global Entire Structure Constants & Polynomials `pPoly` -/

noncomputable def bPt (i : Fin (rCard G)) : ℂ := center (rCard G) i + (εVal G : ℂ)

noncomputable def qPoly : Polynomial ℂ :=
  ∏ i : Fin (rCard G), (Polynomial.X - Polynomial.C (bPt G i))

lemma qPoly_monic : (qPoly G).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _

lemma qPoly_ne_zero : qPoly G ≠ 0 := (qPoly_monic G).ne_zero

lemma qPoly_eval (z : ℂ) : (qPoly G).eval z = ∏ i : Fin (rCard G), (z - bPt G i) := by
  simp [qPoly, Polynomial.eval_prod]

noncomputable def qRest (i : Fin (rCard G)) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, (z - bPt G j)

lemma qPoly_eval_split (i : Fin (rCard G)) (z : ℂ) :
    (qPoly G).eval z = (z - bPt G i) * qRest G i z := by
  rw [qPoly_eval, qRest]
  exact (Finset.mul_prod_erase Finset.univ (fun j => z - bPt G j) (Finset.mem_univ i)).symm

noncomputable def μ0 (z : ℂ) (v w : G → ℂ) : G → ℂ :=
  GroupAlg.convAct (BInvFun G z) (fun t => GroupAlg.convAct (BFun G z) v t * GroupAlg.convAct (BFun G z) w t)

noncomputable def P0 (x y u : G) (z : ℂ) : ℂ :=
  (qPoly G).eval z * μ0 G z (eBasis x) (eBasis y) u

noncomputable def mulLocReg (i : Fin (rCard G)) (z : ℂ) (v w : G → ℂ) : G → ℂ :=
  fun t => ∑ k : Fin (orderOf (gElem G i)), ∑ l : Fin (orderOf (gElem G i)),
    (if k.1 + l.1 < orderOf (gElem G i) then z - bPt G i else z - center (rCard G) i) *
      (GroupAlg.convAct (GroupAlg.idem (gElem G i) k) v t *
       GroupAlg.convAct (GroupAlg.idem (gElem G i) l) w t)

lemma mulLocReg_eq (i : Fin (rCard G)) {z : ℂ} (hz : z ≠ bPt G i) (v w : G → ℂ) (t : G) :
    mulLocReg G i z v w t =
      (z - bPt G i) * GroupAlg.mulLoc (gElem G i) ((z - center (rCard G) i) / (z - bPt G i)) v w t := by
  have hne : z - bPt G i ≠ 0 := sub_ne_zero.2 hz
  simp only [mulLocReg, GroupAlg.mulLoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs with hlt
  · ring
  · field_simp

noncomputable def PLoc (i : Fin (rCard G)) (x y u : G) (z : ℂ) : ℂ :=
  qRest G i z *
    GroupAlg.convAct (AInvFun G i z)
      (mulLocReg G i z (GroupAlg.convAct (AFun G i z) (eBasis x))
        (GroupAlg.convAct (AFun G i z) (eBasis y))) u

lemma P0_eq_PLoc_on_overlap (i : Fin (rCard G)) (x y u : G) {z : ℂ}
    (hz0 : z ∈ U0 G) (hzi : z ∈ Metric.ball (center (rCard G) i) r₀) :
    P0 G x y u z = PLoc G i x y u z := by
  have hlo : r₀⁻¹ ≤ ‖z - center (rCard G) i‖ := (hz0 i).le
  have hz_ne_b : z ≠ bPt G i := by
    intro heq
    have hnorm : ‖z - center (rCard G) i‖ = εVal G := by
      rw [heq, bPt, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (hεVal_pos G).le]
    have hlt := hεVal_lt_quarter G
    rw [r₀] at hlo
    linarith
  have hpatch := patching_on_overlap G i hz0 hzi
  set φ := phiVal G i (z - center (rCard G) i)
  have hφ_pow : φ ^ orderOf (gElem G i) = (z - center (rCard G) i) / (z - bPt G i) := by
    have h1 := phiVal_pow_orderOf G i hlo
    have h2 : (z - center (rCard G) i) - (εVal G : ℂ) = z - bPt G i := by rw [bPt]; ring
    rw [h2] at h1
    exact h1
  -- Apply convAct (BFun G z) to the unregularized local product and compare with μ0
  have hvec_eq : GroupAlg.convAct (AInvFun G i z)
      (GroupAlg.mulLoc (gElem G i) (φ ^ orderOf (gElem G i))
        (GroupAlg.convAct (AFun G i z) (eBasis x))
        (GroupAlg.convAct (AFun G i z) (eBasis y))) =
      μ0 G z (eBasis x) (eBasis y) := by
    have hstep1 : GroupAlg.convAct (BFun G z)
        (GroupAlg.convAct (AInvFun G i z)
          (GroupAlg.mulLoc (gElem G i) (φ ^ orderOf (gElem G i))
            (GroupAlg.convAct (AFun G i z) (eBasis x))
            (GroupAlg.convAct (AFun G i z) (eBasis y)))) =
        fun t => GroupAlg.convAct (BFun G z) (eBasis x) t *
          GroupAlg.convAct (BFun G z) (eBasis y) t := by
      rw [← GroupAlg.convAct_mul, hpatch, mul_assoc, AFun_mul_AInvFun G i hzi, mul_one,
        GroupAlg.convAct_mElem_mulLoc]
      funext t
      rw [← GroupAlg.convAct_mul, ← GroupAlg.convAct_mul, ← hpatch]
    calc GroupAlg.convAct (AInvFun G i z)
            (GroupAlg.mulLoc (gElem G i) (φ ^ orderOf (gElem G i))
              (GroupAlg.convAct (AFun G i z) (eBasis x))
              (GroupAlg.convAct (AFun G i z) (eBasis y)))
        = GroupAlg.convAct (BInvFun G z * BFun G z) _ := by
            rw [BInvFun_mul_BFun G hz0, GroupAlg.convAct_one]
      _ = GroupAlg.convAct (BInvFun G z) (GroupAlg.convAct (BFun G z) _) :=
            GroupAlg.convAct_mul _ _ _
      _ = μ0 G z (eBasis x) (eBasis y) := by rw [hstep1]; rfl
  rw [P0, qPoly_eval_split G i z, PLoc]
  have hlin : GroupAlg.convAct (AInvFun G i z)
      (mulLocReg G i z (GroupAlg.convAct (AFun G i z) (eBasis x))
        (GroupAlg.convAct (AFun G i z) (eBasis y))) u =
      (z - bPt G i) *
        GroupAlg.convAct (AInvFun G i z)
          (GroupAlg.mulLoc (gElem G i) (φ ^ orderOf (gElem G i))
            (GroupAlg.convAct (AFun G i z) (eBasis x))
            (GroupAlg.convAct (AFun G i z) (eBasis y))) u := by
    simp only [GroupAlg.convAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mulLocReg_eq G i hz_ne_b, ← hφ_pow]
    ring
  rw [hlin, hvec_eq]
  ring

lemma disks_disjoint {i j : Fin (rCard G)} (hij : i ≠ j) {z : ℂ}
    (hi : z ∈ Metric.ball (center (rCard G) i) r₀) (hj : z ∈ Metric.ball (center (rCard G) j) r₀) :
    False := by
  have h1 : ‖z - center (rCard G) i‖ < r₀ := mem_ball_iff_norm.1 hi
  have h2 : ‖z - center (rCard G) j‖ < r₀ := mem_ball_iff_norm.1 hj
  have hdist := dist_center_ge (hrCard G) hij
  have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
  have htri : ‖center (rCard G) i - center (rCard G) j‖ ≤
      ‖z - center (rCard G) i‖ + ‖z - center (rCard G) j‖ := by
    have heq : center (rCard G) i - center (rCard G) j =
        -(z - center (rCard G) i) + (z - center (rCard G) j) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans (by rw [norm_neg])
  rw [r₀] at h1 h2
  linarith

lemma mem_U0_or_ball (z : ℂ) :
    z ∈ U0 G ∨ ∃ i : Fin (rCard G), z ∈ Metric.ball (center (rCard G) i) r₀ := by
  by_cases h : z ∈ U0 G
  · exact Or.inl h
  · right
    simp only [U0, Set.mem_setOf_eq, not_forall, not_lt] at h
    obtain ⟨i, hi⟩ := h
    refine ⟨i, Metric.mem_ball.2 ?_⟩
    rw [dist_eq_norm]
    have hlt : r₀⁻¹ < r₀ := by rw [r₀]; norm_num
    exact lt_of_le_of_lt hi hlt

open Classical in
noncomputable def PGlob (x y u : G) (z : ℂ) : ℂ :=
  if h : ∃ i : Fin (rCard G), z ∈ Metric.ball (center (rCard G) i) r₀ then
    PLoc G h.choose x y u z
  else
    P0 G x y u z

lemma PGlob_eq_PLoc (i : Fin (rCard G)) (x y u : G) {z : ℂ}
    (hzi : z ∈ Metric.ball (center (rCard G) i) r₀) :
    PGlob G x y u z = PLoc G i x y u z := by
  have hex : ∃ j : Fin (rCard G), z ∈ Metric.ball (center (rCard G) j) r₀ := ⟨i, hzi⟩
  simp only [PGlob, dif_pos hex]
  have heq : hex.choose = i := by
    by_contra hne
    exact disks_disjoint G hne hex.choose_spec hzi
  rw [heq]

lemma PGlob_eq_P0 (x y u : G) {z : ℂ} (hz0 : z ∈ U0 G) :
    PGlob G x y u z = P0 G x y u z := by
  by_cases hex : ∃ i : Fin (rCard G), z ∈ Metric.ball (center (rCard G) i) r₀
  · simp only [PGlob, dif_pos hex]
    exact (P0_eq_PLoc_on_overlap G hex.choose x y u hz0 hex.choose_spec).symm
  · simp only [PGlob, dif_neg hex]

lemma differentiableOn_P0 (x y u : G) : DifferentiableOn ℂ (P0 G x y u) (U0 G) := by
  have hq : DifferentiableOn ℂ (fun z => (qPoly G).eval z) (U0 G) :=
    (qPoly G).differentiable.differentiableOn
  have hBx : ∀ t : G, DifferentiableOn ℂ (fun z => GroupAlg.convAct (BFun G z) (eBasis x) t) (U0 G) :=
    fun t => convAct_differentiableOn (differentiableOn_BFun G) (fun _ => differentiableOn_const _) t
  have hBy : ∀ t : G, DifferentiableOn ℂ (fun z => GroupAlg.convAct (BFun G z) (eBasis y) t) (U0 G) :=
    fun t => convAct_differentiableOn (differentiableOn_BFun G) (fun _ => differentiableOn_const _) t
  have hμ : DifferentiableOn ℂ (fun z => μ0 G z (eBasis x) (eBasis y) u) (U0 G) :=
    convAct_differentiableOn (differentiableOn_BInvFun G) (fun t => (hBx t).mul (hBy t)) u
  exact hq.mul hμ

lemma differentiableOn_PLoc (i : Fin (rCard G)) (x y u : G) :
    DifferentiableOn ℂ (PLoc G i x y u) (Metric.ball (center (rCard G) i) r₀) := by
  set D := Metric.ball (center (rCard G) i) r₀
  have hqr : DifferentiableOn ℂ (qRest G i) D := by
    have hprod : ∀ s : Finset (Fin (rCard G)),
        DifferentiableOn ℂ (fun z => ∏ j ∈ s, (z - bPt G j)) D := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [differentiableOn_const]
      | insert a s ha ih =>
        have h3 : (fun z => ∏ j ∈ insert a s, (z - bPt G j)) =
            ((id - fun _ => bPt G a) * fun z => ∏ j ∈ s, (z - bPt G j)) :=
          funext fun z => by simp [Finset.prod_insert ha]
        rw [h3]
        exact (differentiableOn_id.sub (differentiableOn_const _)).mul ih
    exact hprod _
  have hAx : ∀ t : G, DifferentiableOn ℂ (fun z => GroupAlg.convAct (AFun G i z) (eBasis x) t) D :=
    fun t => convAct_differentiableOn (differentiableOn_AFun G i) (fun _ => differentiableOn_const _) t
  have hAy : ∀ t : G, DifferentiableOn ℂ (fun z => GroupAlg.convAct (AFun G i z) (eBasis y) t) D :=
    fun t => convAct_differentiableOn (differentiableOn_AFun G i) (fun _ => differentiableOn_const _) t
  have hml : ∀ t : G, DifferentiableOn ℂ (fun z =>
      mulLocReg G i z (GroupAlg.convAct (AFun G i z) (eBasis x))
        (GroupAlg.convAct (AFun G i z) (eBasis y)) t) D := fun t => by
    simp only [mulLocReg]
    refine differentiableOn_finset_sum fun k _ => differentiableOn_finset_sum fun l _ => ?_
    have hcoeff : DifferentiableOn ℂ (fun z =>
        if k.1 + l.1 < orderOf (gElem G i) then z - bPt G i else z - center (rCard G) i) D := by
      split_ifs <;> exact differentiableOn_id.sub (differentiableOn_const _)
    have hfk : DifferentiableOn ℂ (fun z =>
        GroupAlg.convAct (GroupAlg.idem (gElem G i) k) (GroupAlg.convAct (AFun G i z) (eBasis x)) t) D :=
      convAct_differentiableOn (differentiableOn_const _) hAx t
    have hfl : DifferentiableOn ℂ (fun z =>
        GroupAlg.convAct (GroupAlg.idem (gElem G i) l) (GroupAlg.convAct (AFun G i z) (eBasis y)) t) D :=
      convAct_differentiableOn (differentiableOn_const _) hAy t
    exact hcoeff.mul (hfk.mul hfl)
  exact hqr.mul (convAct_differentiableOn (differentiableOn_AInvFun G i) hml u)

lemma differentiable_PGlob (x y u : G) : Differentiable ℂ (PGlob G x y u) := by
  intro z
  rcases mem_U0_or_ball G z with hz0 | ⟨i, hzi⟩
  · have hev : PGlob G x y u =ᶠ[𝓝 z] P0 G x y u := by
      filter_upwards [(isOpen_U0 G).mem_nhds hz0] with w hw
      exact PGlob_eq_P0 G x y u hw
    exact ((differentiableOn_P0 G x y u).differentiableAt ((isOpen_U0 G).mem_nhds hz0)).congr_of_eventuallyEq hev
  · have hev : PGlob G x y u =ᶠ[𝓝 z] PLoc G i x y u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzi] with w hw
      exact PGlob_eq_PLoc G i x y u hw
    exact ((differentiableOn_PLoc G i x y u).differentiableAt (Metric.isOpen_ball.mem_nhds hzi)).congr_of_eventuallyEq hev

lemma exists_poly_bound_PGlob (x y u : G) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, ‖PGlob G x y u z‖ ≤ C * (1 + ‖z‖ ^ rCard G) := by
  -- Bound on U0
  let Cq : ℝ := ∏ i : Fin (rCard G), (1 + ‖bPt G i‖)
  have hCq_pos : 0 ≤ Cq := Finset.prod_nonneg fun i _ => by positivity
  have hq_bound : ∀ z : ℂ, ‖(qPoly G).eval z‖ ≤ Cq * 2 ^ rCard G * (1 + ‖z‖ ^ rCard G) := by
    intro z
    rw [qPoly_eval, norm_prod]
    have hprod_le : ∏ i : Fin (rCard G), ‖z - bPt G i‖ ≤ Cq * (1 + ‖z‖) ^ rCard G := by
      calc ∏ i : Fin (rCard G), ‖z - bPt G i‖
          ≤ ∏ i : Fin (rCard G), ((1 + ‖bPt G i‖) * (1 + ‖z‖)) := by
            refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
            have h1 : ‖z - bPt G i‖ ≤ ‖z‖ + ‖bPt G i‖ := norm_sub_le _ _
            nlinarith [norm_nonneg z, norm_nonneg (bPt G i)]
        _ = Cq * (1 + ‖z‖) ^ rCard G := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpow_le : (1 + ‖z‖) ^ rCard G ≤ 2 ^ rCard G * (1 + ‖z‖ ^ rCard G) := by
      have h1 : 1 + ‖z‖ ≤ 2 * max 1 ‖z‖ := by
        rcases le_total 1 ‖z‖ with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith
      calc (1 + ‖z‖) ^ rCard G ≤ (2 * max 1 ‖z‖) ^ rCard G :=
            pow_le_pow_left₀ (by positivity) h1 _
        _ = 2 ^ rCard G * (max 1 ‖z‖) ^ rCard G := mul_pow _ _ _
        _ ≤ 2 ^ rCard G * (1 + ‖z‖ ^ rCard G) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rcases le_total 1 ‖z‖ with h | h
            · rw [max_eq_right h]; linarith
            · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (norm_nonneg z) (rCard G)]
    calc ∏ i : Fin (rCard G), ‖z - bPt G i‖ ≤ Cq * (1 + ‖z‖) ^ rCard G := hprod_le
      _ ≤ Cq * (2 ^ rCard G * (1 + ‖z‖ ^ rCard G)) := mul_le_mul_of_nonneg_left hpow_le hCq_pos
      _ = Cq * 2 ^ rCard G * (1 + ‖z‖ ^ rCard G) := by ring
  let C0 : ℝ := 8 * (Cq * 2 ^ rCard G)
  have hU0_bound : ∀ z ∈ U0 G, ‖PGlob G x y u z‖ ≤ C0 * (1 + ‖z‖ ^ rCard G) := by
    intro z hz0
    rw [PGlob_eq_P0 G x y u hz0, P0, norm_mul]
    have he_le : ∀ (a : G) (t : G), ‖eBasis a t‖ ≤ 1 := fun a t => by
      simp only [eBasis]; split_ifs <;> simp
    have hBx : ∀ t : G, ‖GroupAlg.convAct (BFun G z) (eBasis x) t‖ ≤ 2 := fun t =>
      (norm_convAct_le _ _ zero_le_one (he_le x) t).trans (by linarith [norm_BFun_le G hz0])
    have hBy : ∀ t : G, ‖GroupAlg.convAct (BFun G z) (eBasis y) t‖ ≤ 2 := fun t =>
      (norm_convAct_le _ _ zero_le_one (he_le y) t).trans (by linarith [norm_BFun_le G hz0])
    have hprod_le : ∀ t : G, ‖GroupAlg.convAct (BFun G z) (eBasis x) t *
        GroupAlg.convAct (BFun G z) (eBasis y) t‖ ≤ 4 := fun t => by
      rw [norm_mul]
      exact (mul_le_mul (hBx t) (hBy t) (norm_nonneg _) (by norm_num)).trans (by norm_num)
    have hμ_le : ‖μ0 G z (eBasis x) (eBasis y) u‖ ≤ 8 :=
      (norm_convAct_le _ _ (by norm_num) hprod_le u).trans (by linarith [norm_BInvFun_le G hz0])
    calc ‖(qPoly G).eval z‖ * ‖μ0 G z (eBasis x) (eBasis y) u‖
        ≤ (Cq * 2 ^ rCard G * (1 + ‖z‖ ^ rCard G)) * 8 :=
          mul_le_mul (hq_bound z) hμ_le (norm_nonneg _) (by positivity)
      _ = C0 * (1 + ‖z‖ ^ rCard G) := by ring
  -- Compact bound on closedBall 0 (100 * r^2 + 2)
  let Rbig : ℝ := 100 * (rCard G : ℝ) ^ 2 + 2
  have hcont : Continuous (fun z => ‖PGlob G x y u z‖) :=
    continuous_norm.comp (differentiable_PGlob G x y u).continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) Rbig).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C0 (max M 0), le_trans (le_max_right M 0) (le_max_right C0 _), fun z => ?_⟩
  rcases mem_U0_or_ball G z with hz0 | ⟨i, hzi⟩
  · exact (hU0_bound z hz0).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hmem : z ∈ Metric.closedBall (0 : ℂ) Rbig := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖z - center (rCard G) i‖ < r₀ := mem_ball_iff_norm.1 hzi
      have hc : ‖center (rCard G) i‖ ≤ 100 * (rCard G : ℝ) ^ 2 := by
        rw [StrategyBPart1a.center, Complex.norm_natCast]
        have hi : (i.1 : ℝ) ≤ (rCard G : ℝ) := by exact_mod_cast i.2.le
        have hr_nn : (0 : ℝ) ≤ rCard G := Nat.cast_nonneg _
        push_cast
        nlinarith
      have htri : ‖z‖ ≤ ‖z - center (rCard G) i‖ + ‖center (rCard G) i‖ := by
        simpa [sub_add_cancel] using norm_add_le (z - center (rCard G) i) (center (rCard G) i)
      rw [r₀] at h1
      linarith
    have hMz : ‖PGlob G x y u z‖ ≤ M := by
      have h1 := hM z hmem
      rwa [Real.norm_of_nonneg (norm_nonneg _)] at h1
    have hge1 : 1 ≤ 1 + ‖z‖ ^ rCard G := by linarith [pow_nonneg (norm_nonneg z) (rCard G)]
    have hCge : M ≤ max C0 (max M 0) := le_trans (le_max_left M 0) (le_max_right C0 _)
    have hC0 : 0 ≤ max C0 (max M 0) := le_trans (le_max_right M 0) (le_max_right C0 _)
    calc ‖PGlob G x y u z‖ ≤ max C0 (max M 0) := hMz.trans hCge
      _ = max C0 (max M 0) * 1 := (mul_one _).symm
      _ ≤ max C0 (max M 0) * (1 + ‖z‖ ^ rCard G) := mul_le_mul_of_nonneg_left hge1 hC0

noncomputable def pPoly (x y u : G) : Polynomial ℂ :=
  let h := exists_poly_bound_PGlob G x y u
  (exists_poly_of_entire_poly_bound (differentiable_PGlob G x y u) h.choose_spec.1 h.choose_spec.2).choose

lemma eval_pPoly (x y u : G) (z : ℂ) : (pPoly G x y u).eval z = PGlob G x y u z := by
  let h := exists_poly_bound_PGlob G x y u
  exact (exists_poly_of_entire_poly_bound (differentiable_PGlob G x y u) h.choose_spec.1 h.choose_spec.2).choose_spec z

/- Infinite upper half-plane Ubig ⊆ U0 and polynomial identities -/

def Ubig : Set ℂ := {z : ℂ | 2 < z.im}

lemma isOpen_Ubig : IsOpen Ubig :=
  isOpen_lt continuous_const Complex.continuous_im

lemma convex_Ubig : Convex ℝ Ubig := by
  intro x hx y hy c d hc hd hcd
  change 2 < (c • x + d • y).im
  have hx' : 2 < x.im := hx
  have hy' : 2 < y.im := hy
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  rcases hc.eq_or_lt with rfl | hc'
  · have hd1 : d = 1 := by linarith
    rw [hd1]; linarith
  · have h1 : 0 < c * (x.im - 2) := mul_pos hc' (by linarith)
    have h2 : 0 ≤ d * (y.im - 2) := mul_nonneg hd (by linarith)
    have h3 : c * x.im + d * y.im - 2 = c * (x.im - 2) + d * (y.im - 2) := by
      linear_combination 2 * hcd
    linarith

lemma Ubig_subset_U0 : Ubig ⊆ U0 G := by
  intro z hz j
  have him : (z - center (rCard G) j).im = z.im := by
    simp [StrategyBPart1a.center]
  have h1 : 2 < |(z - center (rCard G) j).im| := by
    rw [him, abs_of_pos (lt_trans (by norm_num) hz)]; exact hz
  have h2 : |(z - center (rCard G) j).im| ≤ ‖z - center (rCard G) j‖ := Complex.abs_im_le_norm _
  have h3 : r₀⁻¹ < 2 := by rw [r₀]; norm_num
  linarith

lemma qPoly_eval_ne_zero_of_Ubig {z : ℂ} (hz : z ∈ Ubig) : (qPoly G).eval z ≠ 0 := by
  rw [qPoly_eval]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  intro h
  have him := congr_arg Complex.im h
  simp only [bPt, StrategyBPart1a.center, Complex.sub_im, Complex.add_im, Complex.natCast_im,
    Complex.ofReal_im, add_zero, sub_zero, Complex.zero_im] at him
  have hz' : 2 < z.im := hz
  linarith

lemma poly_eq_zero_of_eval_Ubig {p : Polynomial ℂ} (hp : ∀ z ∈ Ubig, p.eval z = 0) : p = 0 := by
  by_contra hne
  have hfin : (p.roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
  have hinf : Ubig.Infinite := by
    refine Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => ((n + 3 : ℝ) : ℂ) * Complex.I) ?_ ?_
    · intro a b hab
      have him := congr_arg Complex.im hab
      simp at him
      exact_mod_cast him
    · intro n
      change 2 < (((n + 3 : ℝ) : ℂ) * Complex.I).im
      simp; linarith
  obtain ⟨z, hzU, hznot⟩ := (hinf.sdiff hfin).nonempty
  exact hznot (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hne).2 (hp z hzU)))

lemma μ0_comm (z : ℂ) (v w : G → ℂ) : μ0 G z v w = μ0 G z w v := by
  simp only [μ0, mul_comm]

lemma convAct_BFun_μ0 {z : ℂ} (hz0 : z ∈ U0 G) (v w : G → ℂ) (t : G) :
    GroupAlg.convAct (BFun G z) (μ0 G z v w) t =
      GroupAlg.convAct (BFun G z) v t * GroupAlg.convAct (BFun G z) w t := by
  rw [μ0, ← GroupAlg.convAct_mul, BFun_mul_BInvFun G hz0, GroupAlg.convAct_one]

lemma μ0_assoc {z : ℂ} (hz0 : z ∈ U0 G) (u v w : G → ℂ) :
    μ0 G z (μ0 G z u v) w = μ0 G z u (μ0 G z v w) := by
  conv_lhs => rw [μ0]
  conv_rhs => rw [μ0]
  congr 1; funext t
  rw [convAct_BFun_μ0 G hz0, convAct_BFun_μ0 G hz0, mul_assoc]

lemma μ0_expand (z : ℂ) (v w : G → ℂ) (u : G) :
    μ0 G z v w u = ∑ x : G, ∑ y : G, v x * w y * μ0 G z (eBasis x) (eBasis y) u := by
  simp only [μ0]
  conv_lhs => rw [GroupAlg.convAct]
  simp_rw [convAct_expand (BFun G z) v, convAct_expand (BFun G z) w]
  calc ∑ t : G, (BInvFun G z).coeff t *
          ((∑ x : G, v x * GroupAlg.convAct (BFun G z) (eBasis x) (u * t)) *
           (∑ y : G, w y * GroupAlg.convAct (BFun G z) (eBasis y) (u * t)))
      = ∑ t : G, ∑ x : G, ∑ y : G,
          v x * w y * ((BInvFun G z).coeff t *
            (GroupAlg.convAct (BFun G z) (eBasis x) (u * t) *
             GroupAlg.convAct (BFun G z) (eBasis y) (u * t))) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ x : G, ∑ y : G, v x * w y *
          ∑ t : G, (BInvFun G z).coeff t *
            (GroupAlg.convAct (BFun G z) (eBasis x) (u * t) *
             GroupAlg.convAct (BFun G z) (eBasis y) (u * t)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ x : G, ∑ y : G, v x * w y *
          GroupAlg.convAct (BInvFun G z)
            (fun t => GroupAlg.convAct (BFun G z) (eBasis x) t *
              GroupAlg.convAct (BFun G z) (eBasis y) t) u := rfl

lemma pPoly_comm (x y u : G) : pPoly G x y u = pPoly G y x u := by
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_eval_Ubig fun z hz => ?_
  rw [Polynomial.eval_sub, eval_pPoly, eval_pPoly,
    PGlob_eq_P0 G x y u (Ubig_subset_U0 G hz),
    PGlob_eq_P0 G y x u (Ubig_subset_U0 G hz),
    P0, P0, μ0_comm, sub_self]

lemma pPoly_assoc (x y w u : G) :
    ∑ s : G, pPoly G x y s * pPoly G s w u = ∑ s : G, pPoly G x s u * pPoly G y w s := by
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_eval_Ubig fun z hz => ?_
  have hz0 : z ∈ U0 G := Ubig_subset_U0 G hz
  simp only [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    eval_pPoly, PGlob_eq_P0 G _ _ _ hz0, P0]
  have hLHS : (∑ s : G, (qPoly G).eval z * μ0 G z (eBasis x) (eBasis y) s *
        ((qPoly G).eval z * μ0 G z (eBasis s) (eBasis w) u)) =
      (qPoly G).eval z * (qPoly G).eval z * μ0 G z (μ0 G z (eBasis x) (eBasis y)) (eBasis w) u := by
    rw [μ0_expand G z (μ0 G z (eBasis x) (eBasis y)) (eBasis w) u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single w]
    · simp [eBasis]; ring
    · intro a _ ha; simp [eBasis, ha]
    · intro h; exact absurd (Finset.mem_univ w) h
  have hRHS : (∑ s : G, (qPoly G).eval z * μ0 G z (eBasis x) (eBasis s) u *
        ((qPoly G).eval z * μ0 G z (eBasis y) (eBasis w) s)) =
      (qPoly G).eval z * (qPoly G).eval z * μ0 G z (eBasis x) (μ0 G z (eBasis y) (eBasis w)) u := by
    symm
    rw [μ0_expand G z (eBasis x) (μ0 G z (eBasis y) (eBasis w)) u]
    rw [Finset.sum_eq_single x]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => by simp [eBasis]; ring
    · intro a _ ha
      refine Finset.sum_eq_zero fun s _ => by simp [eBasis, ha]
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hLHS, hRHS, μ0_assoc G hz0, sub_self]

lemma pPoly_sum_one (x u : G) :
    ∑ y : G, pPoly G x y u = if u = x then qPoly G else 0 := by
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_eval_Ubig fun z hz => ?_
  have hz0 : z ∈ U0 G := Ubig_subset_U0 G hz
  simp only [Polynomial.eval_sub, Polynomial.eval_finsetSum, eval_pPoly,
    PGlob_eq_P0 G _ _ _ hz0, P0]
  have hLHS : ∑ y : G, (qPoly G).eval z * μ0 G z (eBasis x) (eBasis y) u =
      (qPoly G).eval z * μ0 G z (eBasis x) (fun _ => 1) u := by
    rw [← Finset.mul_sum]; congr 1
    symm
    rw [μ0_expand G z (eBasis x) (fun _ => 1) u]
    rw [Finset.sum_eq_single x]
    · refine Finset.sum_congr rfl fun y _ => by simp [eBasis]
    · intro a _ ha
      refine Finset.sum_eq_zero fun y _ => by simp [eBasis, ha]
    · intro h; exact absurd (Finset.mem_univ x) h
  have hμ1 : μ0 G z (eBasis x) (fun _ => 1) u = eBasis x u := by
    have h1 : GroupAlg.convAct (BFun G z) (fun _ => 1) = fun _ => 1 := by
      rw [GroupAlg.convAct_const_one, aug_BFun G hz0]
    simp only [μ0, h1, mul_one]
    rw [← GroupAlg.convAct_mul, BInvFun_mul_BFun G hz0, GroupAlg.convAct_one]
  rw [hLHS, hμ1, eBasis]
  split_ifs <;> simp

lemma pPoly_equivariant (h x y u : G) :
    pPoly G (h * x) (h * y) (h * u) = pPoly G x y u := by
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_eval_Ubig fun z hz => ?_
  have hz0 : z ∈ U0 G := Ubig_subset_U0 G hz
  simp only [Polynomial.eval_sub, eval_pPoly, PGlob_eq_P0 G _ _ _ hz0, P0]
  have hμ : μ0 G z (eBasis (h * x)) (eBasis (h * y)) (h * u) = μ0 G z (eBasis x) (eBasis y) u := by
    rw [← rho_eBasis h x, ← rho_eBasis h y]
    simp only [μ0, GroupAlg.convAct_comm_rho]
    have hprod : (fun t => GroupAlg.rho h (GroupAlg.convAct (BFun G z) (eBasis x)) t *
        GroupAlg.rho h (GroupAlg.convAct (BFun G z) (eBasis y)) t) =
        GroupAlg.rho h (fun t => GroupAlg.convAct (BFun G z) (eBasis x) t *
          GroupAlg.convAct (BFun G z) (eBasis y) t) := rfl
    rw [hprod, GroupAlg.convAct_comm_rho]
    simp [GroupAlg.rho]
  rw [hμ, sub_self]

/- Section 5: The `RatFunc ℂ`-Algebra `LAlg G`, `G`-Action, and `IsDomain (LAlg G)` -/

structure LAlg where
  val : G → RatFunc ℂ

lemma LAlg.ext {a b : LAlg G} (h : ∀ x : G, a.val x = b.val x) : a = b := by
  cases a; cases b; congr; funext x; exact h x

noncomputable def qRat : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (qPoly G)

lemma qRat_ne_zero : qRat G ≠ 0 := by
  intro h
  rw [qRat] at h
  exact qPoly_ne_zero G (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by rw [h, map_zero]))

noncomputable def pRat (x y u : G) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (pPoly G x y u)

lemma pRat_comm (x y u : G) : pRat G x y u = pRat G y x u := by
  simp only [pRat, pPoly_comm]

lemma pRat_assoc (x y w u : G) :
    ∑ s : G, pRat G x y s * pRat G s w u = ∑ s : G, pRat G x s u * pRat G y w s := by
  have h := congr_arg (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (pPoly_assoc G x y w u)
  simpa only [map_sum, map_mul, pRat] using h

lemma pRat_sum_one (x u : G) :
    ∑ y : G, pRat G x y u = if u = x then qRat G else 0 := by
  have h := congr_arg (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (pPoly_sum_one G x u)
  simp only [map_sum] at h
  change ∑ y : G, algebraMap (Polynomial ℂ) (RatFunc ℂ) (pPoly G x y u) = _
  rw [h]
  split_ifs <;> simp [qRat]

lemma pRat_equivariant (h x y u : G) :
    pRat G (h * x) (h * y) (h * u) = pRat G x y u := by
  simp only [pRat, pPoly_equivariant]

noncomputable instance : Zero (LAlg G) := ⟨⟨fun _ => 0⟩⟩
noncomputable instance : One (LAlg G) := ⟨⟨fun _ => 1⟩⟩
noncomputable instance : Add (LAlg G) := ⟨fun a b => ⟨fun x => a.val x + b.val x⟩⟩
noncomputable instance : Neg (LAlg G) := ⟨fun a => ⟨fun x => -a.val x⟩⟩
noncomputable instance : Sub (LAlg G) := ⟨fun a b => ⟨fun x => a.val x - b.val x⟩⟩
noncomputable instance : Mul (LAlg G) :=
  ⟨fun a b => ⟨fun u => (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * a.val x * b.val y⟩⟩
noncomputable instance : SMul (RatFunc ℂ) (LAlg G) := ⟨fun r a => ⟨fun x => r * a.val x⟩⟩

set_option maxHeartbeats 400000 in
noncomputable instance : CommRing (LAlg G) where
  add_assoc a b c := LAlg.ext G fun x => add_assoc _ _ _
  zero_add a := LAlg.ext G fun x => zero_add _
  add_zero a := LAlg.ext G fun x => add_zero _
  add_comm a b := LAlg.ext G fun x => add_comm _ _
  neg_add_cancel a := LAlg.ext G fun x => neg_add_cancel _
  sub_eq_add_neg a b := LAlg.ext G fun x => sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_mul a := LAlg.ext G fun u => by
    change (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * 0 * a.val y = 0
    simp
  mul_zero a := LAlg.ext G fun u => by
    change (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * a.val x * 0 = 0
    simp
  left_distrib a b c := LAlg.ext G fun u => by
    change (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * a.val x * (b.val y + c.val y) =
      (qRat G)⁻¹ * (∑ x : G, ∑ y : G, pRat G x y u * a.val x * b.val y) +
      (qRat G)⁻¹ * (∑ x : G, ∑ y : G, pRat G x y u * a.val x * c.val y)
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1; refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => by ring
  right_distrib a b c := LAlg.ext G fun u => by
    change (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * (a.val x + b.val x) * c.val y =
      (qRat G)⁻¹ * (∑ x : G, ∑ y : G, pRat G x y u * a.val x * c.val y) +
      (qRat G)⁻¹ * (∑ x : G, ∑ y : G, pRat G x y u * b.val x * c.val y)
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1; refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => by ring
  mul_comm a b := LAlg.ext G fun u => by
    change (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * a.val x * b.val y =
      (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * b.val x * a.val y
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    rw [pRat_comm G x y u]; ring
  mul_one a := LAlg.ext G fun u => by
    change (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * a.val x * 1 = a.val u
    have hsum : ∑ x : G, ∑ y : G, pRat G x y u * a.val x * 1 = qRat G * a.val u := by
      have h1 : ∀ x : G, ∑ y : G, pRat G x y u * a.val x * 1 =
          (if u = x then qRat G else 0) * a.val x := fun x => by
        simp_rw [mul_one]
        rw [← Finset.sum_mul, pRat_sum_one]
      simp_rw [h1]
      rw [Finset.sum_eq_single u]
      · simp
      · intro x _ hx; rw [if_neg hx.symm, zero_mul]
      · intro h; exact absurd (Finset.mem_univ u) h
    rw [hsum, ← mul_assoc, inv_mul_cancel₀ (qRat_ne_zero G), one_mul]
  one_mul a := LAlg.ext G fun u => by
    change (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * 1 * a.val y = a.val u
    rw [Finset.sum_comm]
    have hsum : ∑ y : G, ∑ x : G, pRat G x y u * 1 * a.val y = qRat G * a.val u := by
      have h1 : ∀ y : G, ∑ x : G, pRat G x y u * 1 * a.val y =
          (if u = y then qRat G else 0) * a.val y := fun y => by
        simp_rw [mul_one, pRat_comm G _ y u]
        rw [← Finset.sum_mul, pRat_sum_one]
      simp_rw [h1]
      rw [Finset.sum_eq_single u]
      · simp
      · intro y _ hy; rw [if_neg hy.symm, zero_mul]
      · intro h; exact absurd (Finset.mem_univ u) h
    rw [hsum, ← mul_assoc, inv_mul_cancel₀ (qRat_ne_zero G), one_mul]
  mul_assoc a b c := LAlg.ext G fun u => by
    change (qRat G)⁻¹ * ∑ s : G, ∑ w : G,
        pRat G s w u * ((qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y s * a.val x * b.val y) * c.val w =
      (qRat G)⁻¹ * ∑ x : G, ∑ s : G,
        pRat G x s u * a.val x * ((qRat G)⁻¹ * ∑ y : G, ∑ w : G, pRat G y w s * b.val y * c.val w)
    have hL : (qRat G)⁻¹ * ∑ s : G, ∑ w : G,
        pRat G s w u * ((qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y s * a.val x * b.val y) * c.val w =
        (qRat G)⁻¹ * (qRat G)⁻¹ * ∑ x : G, ∑ y : G, ∑ w : G,
          (∑ s : G, pRat G x y s * pRat G s w u) * (a.val x * b.val y * c.val w) := by
      have h1 : ∀ s w : G,
          pRat G s w u * ((qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y s * a.val x * b.val y) * c.val w =
          (qRat G)⁻¹ * ∑ x : G, ∑ y : G, (pRat G x y s * pRat G s w u) * (a.val x * b.val y * c.val w) :=
        fun s w => by
          have h2 : pRat G s w u * ((qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y s * a.val x * b.val y) * c.val w =
              (qRat G)⁻¹ * (pRat G s w u * c.val w * ∑ x : G, ∑ y : G, pRat G x y s * a.val x * b.val y) := by ring
          rw [h2, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => by ring
      simp_rw [h1, ← Finset.mul_sum]
      rw [← mul_assoc]
      congr 1
      calc ∑ s : G, ∑ w : G, ∑ x : G, ∑ y : G,
              (pRat G x y s * pRat G s w u) * (a.val x * b.val y * c.val w)
          = ∑ s : G, ∑ x : G, ∑ y : G, ∑ w : G,
              (pRat G x y s * pRat G s w u) * (a.val x * b.val y * c.val w) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ x : G, ∑ y : G, ∑ w : G, ∑ s : G,
              (pRat G x y s * pRat G s w u) * (a.val x * b.val y * c.val w) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y _ => Finset.sum_comm
        _ = ∑ x : G, ∑ y : G, ∑ w : G,
              (∑ s : G, pRat G x y s * pRat G s w u) * (a.val x * b.val y * c.val w) := by
            refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
              Finset.sum_congr rfl fun w _ => (Finset.sum_mul _ _ _).symm
    have hR : (qRat G)⁻¹ * ∑ x : G, ∑ s : G,
        pRat G x s u * a.val x * ((qRat G)⁻¹ * ∑ y : G, ∑ w : G, pRat G y w s * b.val y * c.val w) =
        (qRat G)⁻¹ * (qRat G)⁻¹ * ∑ x : G, ∑ y : G, ∑ w : G,
          (∑ s : G, pRat G x s u * pRat G y w s) * (a.val x * b.val y * c.val w) := by
      have h1 : ∀ x s : G,
          pRat G x s u * a.val x * ((qRat G)⁻¹ * ∑ y : G, ∑ w : G, pRat G y w s * b.val y * c.val w) =
          (qRat G)⁻¹ * ∑ y : G, ∑ w : G, (pRat G x s u * pRat G y w s) * (a.val x * b.val y * c.val w) :=
        fun x s => by
          have h2 : pRat G x s u * a.val x * ((qRat G)⁻¹ * ∑ y : G, ∑ w : G, pRat G y w s * b.val y * c.val w) =
              (qRat G)⁻¹ * (pRat G x s u * a.val x * ∑ y : G, ∑ w : G, pRat G y w s * b.val y * c.val w) := by ring
          rw [h2, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => by ring
      simp_rw [h1, ← Finset.mul_sum]
      rw [← mul_assoc]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => (Finset.sum_mul _ _ _).symm
    rw [hL, hR]
    exact congr_arg ((qRat G)⁻¹ * (qRat G)⁻¹ * ·)
      (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun w _ => by rw [pRat_assoc])

noncomputable instance : Algebra (RatFunc ℂ) (LAlg G) where
  algebraMap := {
    toFun := fun r => ⟨fun _ => r⟩
    map_one' := rfl
    map_mul' := fun r s => LAlg.ext G fun u => by
      change r * s = (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * r * s
      have h1 : ∑ x : G, ∑ y : G, pRat G x y u * r * s =
          (∑ x : G, ∑ y : G, pRat G x y u) * (r * s) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => by ring
      have h2 : ∑ x : G, ∑ y : G, pRat G x y u = qRat G := by
        simp_rw [pRat_sum_one]
        rw [Finset.sum_eq_single u]
        · simp
        · intro x _ hx; rw [if_neg hx.symm]
        · intro h; exact absurd (Finset.mem_univ u) h
      rw [h1, h2, ← mul_assoc, inv_mul_cancel₀ (qRat_ne_zero G), one_mul]
    map_zero' := rfl
    map_add' := fun _ _ => rfl
  }
  commutes' := fun _ _ => mul_comm _ _
  smul_def' := fun r a => LAlg.ext G fun u => by
    change r * a.val u = (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * r * a.val y
    rw [Finset.sum_comm]
    have hsum : ∑ y : G, ∑ x : G, pRat G x y u * r * a.val y = qRat G * (r * a.val u) := by
      have h1 : ∀ y : G, ∑ x : G, pRat G x y u * r * a.val y =
          (if u = y then qRat G else 0) * (r * a.val y) := fun y => by
        calc ∑ x : G, pRat G x y u * r * a.val y
            = (∑ x : G, pRat G y x u) * (r * a.val y) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun x _ => by rw [pRat_comm G x y u]; ring
          _ = (if u = y then qRat G else 0) * (r * a.val y) := by rw [pRat_sum_one]
      simp_rw [h1]
      rw [Finset.sum_eq_single u]
      · simp
      · intro y _ hy; rw [if_neg hy.symm, zero_mul]
      · intro h; exact absurd (Finset.mem_univ u) h
    rw [hsum, ← mul_assoc, inv_mul_cancel₀ (qRat_ne_zero G), one_mul]

noncomputable def LAlgLinearEquiv : LAlg G ≃ₗ[RatFunc ℂ] (G → RatFunc ℂ) where
  toFun := LAlg.val
  invFun := LAlg.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

instance : FiniteDimensional (RatFunc ℂ) (LAlg G) :=
  Module.Finite.equiv (LAlgLinearEquiv G).symm

lemma finrank_LAlg : Module.finrank (RatFunc ℂ) (LAlg G) = Fintype.card G := by
  rw [(LAlgLinearEquiv G).finrank_eq, Module.finrank_pi]

noncomputable def rhoAlgEquiv (h : G) : LAlg G ≃ₐ[RatFunc ℂ] LAlg G where
  toFun a := ⟨fun x => a.val (h⁻¹ * x)⟩
  invFun a := ⟨fun x => a.val (h * x)⟩
  left_inv a := LAlg.ext G fun x => by simp
  right_inv a := LAlg.ext G fun x => by simp
  map_add' _ _ := rfl
  map_mul' a b := LAlg.ext G fun u => by
    change (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y (h⁻¹ * u) * a.val x * b.val y =
      (qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * a.val (h⁻¹ * x) * b.val (h⁻¹ * y)
    refine congr_arg ((qRat G)⁻¹ * ·) ?_
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun x => ?_
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun y => ?_
    change pRat G x y (h⁻¹ * u) * a.val x * b.val y =
      pRat G (h * x) (h * y) u * a.val (h⁻¹ * (h * x)) * b.val (h⁻¹ * (h * y))
    have hp : pRat G (h * x) (h * y) u = pRat G x y (h⁻¹ * u) := by
      have := pRat_equivariant G h x y (h⁻¹ * u)
      simpa using this
    rw [hp, inv_mul_cancel_left, inv_mul_cancel_left]
  commutes' _ := rfl

noncomputable def rhoHom : G →* (LAlg G ≃ₐ[RatFunc ℂ] LAlg G) where
  toFun := rhoAlgEquiv G
  map_one' := by ext a; exact LAlg.ext G fun x => by simp [rhoAlgEquiv]
  map_mul' h₁ h₂ := by
    ext a
    exact LAlg.ext G fun x => by
      change a.val ((h₁ * h₂)⁻¹ * x) = a.val (h₂⁻¹ * (h₁⁻¹ * x))
      rw [mul_inv_rev, mul_assoc]

lemma rhoHom_injective : Function.Injective (rhoHom G) := by
  intro h₁ h₂ heq
  let e1 : LAlg G := ⟨fun x => if x = 1 then 1 else 0⟩
  have hval := congr_arg (fun σ : LAlg G ≃ₐ[RatFunc ℂ] LAlg G => (σ e1).val h₁) heq
  simp only [rhoHom, MonoidHom.coe_mk, OneHom.coe_mk, rhoAlgEquiv, AlgEquiv.coe_mk,
    Equiv.coe_fn_mk, e1, inv_mul_cancel, ite_true] at hval
  by_contra hne
  have hne' : h₂⁻¹ * h₁ ≠ 1 := fun h => hne (by
    have := congr_arg (h₂ * ·) h; simpa using this)
  rw [if_neg hne'] at hval
  exact one_ne_zero hval

/- Section 6: `IsDomain (LAlg G)` via Two-Strip Analytic Continuation & `forall_eq_zero_of_sum_psi_eq_zero` -/

noncomputable def polyMul (v w : G → Polynomial ℂ) (u : G) : Polynomial ℂ :=
  ∑ x : G, ∑ y : G, pPoly G x y u * v x * w y

lemma eval_polyMul_convAct (v w : G → Polynomial ℂ) {z : ℂ} (hz0 : z ∈ U0 G) (t : G) :
    GroupAlg.convAct (BFun G z) (fun u => (polyMul G v w u).eval z) t =
      (qPoly G).eval z *
        (GroupAlg.convAct (BFun G z) (fun x => (v x).eval z) t *
         GroupAlg.convAct (BFun G z) (fun y => (w y).eval z) t) := by
  have hev : (fun u => (polyMul G v w u).eval z) =
      fun u => (qPoly G).eval z * μ0 G z (fun x => (v x).eval z) (fun y => (w y).eval z) u := by
    funext u
    simp only [polyMul, Polynomial.eval_finsetSum, Polynomial.eval_mul, eval_pPoly,
      PGlob_eq_P0 G _ _ _ hz0, P0]
    rw [μ0_expand G z (fun x => (v x).eval z) (fun y => (w y).eval z) u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  rw [hev]
  have hsmul : GroupAlg.convAct (BFun G z)
      (fun u => (qPoly G).eval z * μ0 G z (fun x => (v x).eval z) (fun y => (w y).eval z) u) t =
      (qPoly G).eval z *
        GroupAlg.convAct (BFun G z) (μ0 G z (fun x => (v x).eval z) (fun y => (w y).eval z)) t := by
    simp only [GroupAlg.convAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => by ring
  rw [hsmul, convAct_BFun_μ0 G hz0]

noncomputable def vTilde (v : G → Polynomial ℂ) (x : G) (z : ℂ) : ℂ :=
  GroupAlg.convAct (BFun G z) (fun y => (v y).eval z) x

lemma differentiableOn_vTilde (v : G → Polynomial ℂ) (x : G) :
    DifferentiableOn ℂ (vTilde G v x) (U0 G) :=
  convAct_differentiableOn (differentiableOn_BFun G)
    (fun y => (v y).differentiable.differentiableOn) x

def VStrip (i : Fin (rCard G)) : Set ℂ :=
  {z : ℂ | |z.re - (((100 * rCard G * i.1 : ℕ) : ℝ) - 1)| < 1 / 10}

lemma isOpen_VStrip (i : Fin (rCard G)) : IsOpen (VStrip G i) :=
  isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const)) continuous_const

lemma convex_VStrip (i : Fin (rCard G)) : Convex ℝ (VStrip G i) := by
  intro x hx y hy c d hc hd hcd
  set a₀ : ℝ := ((100 * rCard G * i.1 : ℕ) : ℝ) - 1
  change |(c • x + d • y).re - a₀| < 1 / 10
  have hx' : |x.re - a₀| < 1 / 10 := hx
  have hy' : |y.re - a₀| < 1 / 10 := hy
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have heq : c * x.re + d * y.re - a₀ = c * (x.re - a₀) + d * (y.re - a₀) := by
    linear_combination a₀ * hcd
  rw [heq]
  have htri : |c * (x.re - a₀) + d * (y.re - a₀)| ≤ c * |x.re - a₀| + d * |y.re - a₀| := by
    calc |c * (x.re - a₀) + d * (y.re - a₀)|
        ≤ |c * (x.re - a₀)| + |d * (y.re - a₀)| := abs_add_le _ _
      _ = c * |x.re - a₀| + d * |y.re - a₀| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hd]
  have hlt : c * |x.re - a₀| + d * |y.re - a₀| < 1 / 10 := by
    rcases hc.eq_or_lt with rfl | hc'
    · have hd1 : d = 1 := by linarith
      rw [hd1]; linarith
    · have h1 : c * (|x.re - a₀| - 1 / 10) < 0 := mul_neg_of_pos_of_neg hc' (by linarith)
      have h2 : d * (|y.re - a₀| - 1 / 10) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd (by linarith)
      have h3 : c * |x.re - a₀| + d * |y.re - a₀| - 1 / 10 =
          c * (|x.re - a₀| - 1 / 10) + d * (|y.re - a₀| - 1 / 10) := by
        linear_combination (1 / 10 : ℝ) * hcd
      linarith
  exact lt_of_le_of_lt htri hlt

lemma VStrip_subset_U0 (i : Fin (rCard G)) : VStrip G i ⊆ U0 G := by
  intro z hz j
  set a_i : ℝ := ((100 * rCard G * i.1 : ℕ) : ℝ)
  set a_j : ℝ := ((100 * rCard G * j.1 : ℕ) : ℝ)
  have hre_sub : (z - center (rCard G) j).re = z.re - a_j := by
    simp [StrategyBPart1a.center, a_j]
  have habs_z : |z.re - (a_i - 1)| < 1 / 10 := hz
  have hle_norm : |z.re - a_j| ≤ ‖z - center (rCard G) j‖ := by
    rw [← hre_sub]; exact Complex.abs_re_le_norm _
  have hr₀_inv : r₀⁻¹ = 4 / 5 := by rw [r₀]; norm_num
  rw [hr₀_inv]
  by_cases hij : j = i
  · subst hij
    have h1 : z.re - a_i < -(9 / 10 : ℝ) := by linarith [(abs_lt.1 habs_z).2]
    have h2 : 9 / 10 < |z.re - a_i| := by
      rw [abs_of_neg (by linarith)]; linarith
    linarith
  · have hdist : 100 * (rCard G : ℝ) ≤ |a_i - a_j| := by
      have hd := dist_center_ge (hrCard G) (Ne.symm hij)
      have hceq : center (rCard G) i - center (rCard G) j = ((a_i - a_j : ℝ) : ℂ) := by
        simp [StrategyBPart1a.center, a_i, a_j]
      rw [hceq, Complex.norm_real, Real.norm_eq_abs] at hd
      exact hd
    have hr : (1 : ℝ) ≤ rCard G := by exact_mod_cast hrCard G
    have hza : |z.re - a_i| < 11 / 10 := by
      have h1 := abs_lt.1 habs_z
      rw [abs_lt]; constructor <;> linarith
    have htri : |a_i - a_j| ≤ |z.re - a_i| + |z.re - a_j| := by
      have heq : a_i - a_j = -(z.re - a_i) + (z.re - a_j) := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    linarith

lemma vTilde_zero_mul_g (v : G → Polynomial ℂ) (x : G) (i : Fin (rCard G))
    (hx : ∀ z ∈ Ubig, vTilde G v x z = 0) :
    ∀ z ∈ Ubig, vTilde G v (x * gElem G i) z = 0 := by
  set a_i : ℝ := ((100 * rCard G * i.1 : ℕ) : ℝ)
  have ha_cast : (a_i : ℂ) = center (rCard G) i := by simp [a_i, StrategyBPart1a.center]
  -- Step 1: Propagate vTilde v x = 0 from Ubig to VStrip i
  let z₁ : ℂ := ⟨a_i - 1, 3⟩
  have hz₁_Ubig : z₁ ∈ Ubig := by change 2 < (3 : ℝ); norm_num
  have hz₁_V : z₁ ∈ VStrip G i := by change |(a_i - 1) - (a_i - 1)| < 1 / 10; simp
  have hvx_V : ∀ z ∈ VStrip G i, vTilde G v x z = 0 := by
    have hanal : AnalyticOnNhd ℂ (vTilde G v x) (VStrip G i) :=
      ((differentiableOn_vTilde G v x).mono (VStrip_subset_U0 G i)).analyticOnNhd (isOpen_VStrip G i)
    have hev : vTilde G v x =ᶠ[𝓝 z₁] 0 := by
      filter_upwards [isOpen_Ubig.mem_nhds hz₁_Ubig] with z hz
      exact hx z hz
    exact fun z hz => hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_VStrip G i).isPreconnected hz₁_V hev hz
  -- Step 2: Check B_test := ball (a_i - 1) (1/10) ⊆ VStrip i and ⊆ ball (center i) r₀
  set Btest := Metric.ball ((a_i : ℂ) - 1) (1 / 10)
  have hBtest_V : Btest ⊆ VStrip G i := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre : (z - ((a_i : ℂ) - 1)).re = z.re - (a_i - 1) := by simp
    have h1 := Complex.abs_re_le_norm (z - ((a_i : ℂ) - 1))
    rw [hre] at h1
    exact lt_of_le_of_lt h1 hz
  have hBtest_D : Btest ⊆ Metric.ball (center (rCard G) i) r₀ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rw [← ha_cast]
    have htri : z - (a_i : ℂ) = (z - ((a_i : ℂ) - 1)) + (-1 : ℂ) := by ring
    rw [htri]
    calc ‖(z - ((a_i : ℂ) - 1)) + (-1 : ℂ)‖ ≤ ‖z - ((a_i : ℂ) - 1)‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
      _ < 1 / 10 + 1 := by simp; linarith
      _ < r₀ := by rw [r₀]; norm_num
  -- Step 3: Define f_k on ball (a_i) (5/4) and apply forall_eq_zero_of_sum_psi_eq_zero
  set n := orderOf (gElem G i)
  let f : Fin n → ℂ → ℂ := fun k z =>
    GroupAlg.convAct (GroupAlg.idem (gElem G i) k)
      (GroupAlg.convAct (AFun G i z) (fun y => (v y).eval z)) x
  have hf_diff : ∀ k : Fin n, DifferentiableOn ℂ (f k) (Metric.ball (a_i : ℂ) (5 / 4)) := fun k => by
    have hD : Metric.ball (a_i : ℂ) (5 / 4) = Metric.ball (center (rCard G) i) r₀ := by
      rw [ha_cast, r₀]
    rw [hD]
    have hA : ∀ t : G, DifferentiableOn ℂ
        (fun z => GroupAlg.convAct (AFun G i z) (fun y => (v y).eval z) t)
        (Metric.ball (center (rCard G) i) r₀) :=
      fun t => convAct_differentiableOn (differentiableOn_AFun G i)
        (fun y => (v y).differentiable.differentiableOn) t
    exact convAct_differentiableOn (differentiableOn_const _) hA x
  have hphi_eq_psi : ∀ z ∈ Btest,
      phiVal G i (z - center (rCard G) i) =
      Complex.exp ((n : ℂ)⁻¹ * Complex.log ((z - (a_i : ℂ)) / (z - ((a_i : ℂ) + (εVal G : ℂ))))) := by
    intro z hz
    rw [phiVal, ← ha_cast]
    congr 2
    set w := z - (a_i : ℂ)
    have hw_re : w.re < 0 := by
      have hzV : |z.re - (a_i - 1)| < 1 / 10 := hBtest_V hz
      have h1 : w.re = z.re - a_i := by simp [w]
      linarith [(abs_lt.1 hzV).2]
    have hre_pos : 0 < (w / (w - (εVal G : ℂ))).re := re_div_pos_of_re_neg hw_re (hεVal_pos G)
    have hw0 : w ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hw_re; linarith
    have hinv_eq : 1 - (εVal G : ℂ) / w = (w / (w - (εVal G : ℂ)))⁻¹ := by
      rw [inv_div]
      field_simp
    have hden_eq : z - ((a_i : ℂ) + (εVal G : ℂ)) = w - (εVal G : ℂ) := by simp [w]; ring
    rw [hinv_eq, complex_log_inv_of_re_pos hre_pos, neg_neg, hden_eq]
  have hsum_zero : ∀ z ∈ Btest,
      ∑ k : Fin n, f k z *
        (Complex.exp ((n : ℂ)⁻¹ * Complex.log ((z - (a_i : ℂ)) / (z - ((a_i : ℂ) + (εVal G : ℂ)))))) ^ k.1 = 0 := by
    intro z hz
    have hz0 : z ∈ U0 G := VStrip_subset_U0 G i (hBtest_V hz)
    have hzi : z ∈ Metric.ball (center (rCard G) i) r₀ := hBtest_D hz
    have h0 : vTilde G v x z = 0 := hvx_V z (hBtest_V hz)
    rw [vTilde, patching_on_overlap G i hz0 hzi, GroupAlg.convAct_mul, GroupAlg.mElem,
      GroupAlg.convAct_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GroupAlg.convAct_smul, Pi.smul_apply, smul_eq_mul, hphi_eq_psi z hz, mul_comm]
  have hf_all_zero : ∀ k : Fin n, ∀ z ∈ Metric.ball (a_i : ℂ) (5 / 4), f k z = 0 :=
    forall_eq_zero_of_sum_psi_eq_zero (hεVal_pos G) (hεVal_lt_quarter G)
      (GroupAlg.orderOf_pos_of_fintype (gElem G i)) hf_diff hsum_zero
  -- Step 4: Deduce vTilde v (x * g_i) = 0 on Btest
  have hvxg_Btest : ∀ z ∈ Btest, vTilde G v (x * gElem G i) z = 0 := by
    intro z hz
    have hz0 : z ∈ U0 G := VStrip_subset_U0 G i (hBtest_V hz)
    have hzi : z ∈ Metric.ball (center (rCard G) i) r₀ := hBtest_D hz
    rw [vTilde, patching_on_overlap G i hz0 hzi, GroupAlg.convAct_mul, GroupAlg.mElem,
      GroupAlg.convAct_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [GroupAlg.convAct_smul, Pi.smul_apply, smul_eq_mul, GroupAlg.convAct_idem_mul_g]
    have hzi' : z ∈ Metric.ball (a_i : ℂ) (5 / 4) := by simpa [ha_cast, r₀] using hzi
    have hfk0 : f k z = 0 := hf_all_zero k z hzi'
    change _ * (_ * f k z) = 0
    rw [hfk0, mul_zero, mul_zero]
  -- Step 5: Propagate vTilde v (x * g_i) = 0 from Btest -> VStrip i -> Ubig
  have hvxg_V : ∀ z ∈ VStrip G i, vTilde G v (x * gElem G i) z = 0 := by
    have hanal : AnalyticOnNhd ℂ (vTilde G v (x * gElem G i)) (VStrip G i) :=
      ((differentiableOn_vTilde G v (x * gElem G i)).mono (VStrip_subset_U0 G i)).analyticOnNhd
        (isOpen_VStrip G i)
    have hpt : ((a_i : ℂ) - 1) ∈ VStrip G i := hBtest_V (Metric.mem_ball_self (by norm_num))
    have hev : vTilde G v (x * gElem G i) =ᶠ[𝓝 ((a_i : ℂ) - 1)] 0 := by
      filter_upwards [Metric.ball_mem_nhds ((a_i : ℂ) - 1) (by norm_num : (0 : ℝ) < 1 / 10)] with z hz
      exact hvxg_Btest z hz
    exact fun z hz => hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_VStrip G i).isPreconnected hpt hev hz
  have hanal_Ubig : AnalyticOnNhd ℂ (vTilde G v (x * gElem G i)) Ubig :=
    ((differentiableOn_vTilde G v (x * gElem G i)).mono (Ubig_subset_U0 G)).analyticOnNhd isOpen_Ubig
  have hev_Ubig : vTilde G v (x * gElem G i) =ᶠ[𝓝 z₁] 0 := by
    filter_upwards [(isOpen_VStrip G i).mem_nhds hz₁_V] with z hz
    exact hvxg_V z hz
  exact fun z hz => hanal_Ubig.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    convex_Ubig.isPreconnected hz₁_Ubig hev_Ubig hz

lemma poly_eq_zero_of_vTilde_zero (v : G → Polynomial ℂ) (x : G)
    (hx : ∀ z ∈ Ubig, vTilde G v x z = 0) :
    ∀ y : G, v y = 0 := by
  have hall : ∀ t : G, ∀ z ∈ Ubig, vTilde G v t z = 0 := by
    intro t
    let i : Fin (rCard G) := (eG G).symm (x⁻¹ * t)
    have ht : x * gElem G i = t := by
      simp [gElem, i]
    rw [← ht]
    exact vTilde_zero_mul_g G v x i hx
  intro y
  refine poly_eq_zero_of_eval_Ubig fun z hz => ?_
  have hz0 : z ∈ U0 G := Ubig_subset_U0 G hz
  have h0 : GroupAlg.convAct (BFun G z) (fun t => (v t).eval z) = 0 := by
    funext t; exact hall t z hz
  have h1 : (fun t => (v t).eval z) =
      GroupAlg.convAct (BInvFun G z) (GroupAlg.convAct (BFun G z) (fun t => (v t).eval z)) := by
    rw [← GroupAlg.convAct_mul, BInvFun_mul_BFun G hz0, GroupAlg.convAct_one]
  have h2 := congr_fun h1 y
  rw [h0] at h2
  simpa [GroupAlg.convAct] using h2

instance : Nontrivial (LAlg G) :=
  ⟨⟨1, 0, fun h => one_ne_zero (congr_fun (congr_arg LAlg.val h) (1 : G))⟩⟩

instance : NoZeroDivisors (LAlg G) := ⟨fun {a b} hab => by
  -- Clear denominators of a and b
  let Da : Polynomial ℂ := ∏ x : G, (a.val x).denom
  let Db : Polynomial ℂ := ∏ x : G, (b.val x).denom
  have hDa : Da ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => RatFunc.denom_ne_zero (a.val x)
  have hDb : Db ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => RatFunc.denom_ne_zero (b.val x)
  have hDa_rat : algebraMap (Polynomial ℂ) (RatFunc ℂ) Da ≠ 0 := fun h =>
    hDa (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by rw [h, map_zero]))
  have hDb_rat : algebraMap (Polynomial ℂ) (RatFunc ℂ) Db ≠ 0 := fun h =>
    hDb (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by rw [h, map_zero]))
  let v : G → Polynomial ℂ := fun x => (a.val x).num * ∏ y ∈ Finset.univ.erase x, (a.val y).denom
  let w : G → Polynomial ℂ := fun x => (b.val x).num * ∏ y ∈ Finset.univ.erase x, (b.val y).denom
  have hv_eq : ∀ x : G, algebraMap (Polynomial ℂ) (RatFunc ℂ) (v x) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) Da * a.val x := fun x => by
    have hsplit : Da = (a.val x).denom * ∏ y ∈ Finset.univ.erase x, (a.val y).denom :=
      (Finset.mul_prod_erase Finset.univ (fun y => (a.val y).denom) (Finset.mem_univ x)).symm
    have hden_ne : algebraMap (Polynomial ℂ) (RatFunc ℂ) (a.val x).denom ≠ 0 := fun h =>
      RatFunc.denom_ne_zero (a.val x)
        (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by rw [h, map_zero]))
    have hnd := RatFunc.num_div_denom (a.val x)
    have hmul_a : algebraMap (Polynomial ℂ) (RatFunc ℂ) (a.val x).num =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (a.val x).denom * a.val x := by
      have h1 := congr_arg (algebraMap (Polynomial ℂ) (RatFunc ℂ) (a.val x).denom * ·) hnd
      rwa [mul_div_cancel₀ _ hden_ne] at h1
    calc algebraMap (Polynomial ℂ) (RatFunc ℂ) (v x)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (a.val x).num *
            algebraMap (Polynomial ℂ) (RatFunc ℂ) (∏ y ∈ Finset.univ.erase x, (a.val y).denom) := by
          simp [v]
      _ = (algebraMap (Polynomial ℂ) (RatFunc ℂ) (a.val x).denom * a.val x) *
            algebraMap (Polynomial ℂ) (RatFunc ℂ) (∏ y ∈ Finset.univ.erase x, (a.val y).denom) := by
          rw [hmul_a]
      _ = algebraMap (Polynomial ℂ) (RatFunc ℂ) Da * a.val x := by
          rw [hsplit, map_mul]; ring
  have hw_eq : ∀ x : G, algebraMap (Polynomial ℂ) (RatFunc ℂ) (w x) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) Db * b.val x := fun x => by
    have hsplit : Db = (b.val x).denom * ∏ y ∈ Finset.univ.erase x, (b.val y).denom :=
      (Finset.mul_prod_erase Finset.univ (fun y => (b.val y).denom) (Finset.mem_univ x)).symm
    have hden_ne : algebraMap (Polynomial ℂ) (RatFunc ℂ) (b.val x).denom ≠ 0 := fun h =>
      RatFunc.denom_ne_zero (b.val x)
        (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by rw [h, map_zero]))
    have hnd := RatFunc.num_div_denom (b.val x)
    have hmul_b : algebraMap (Polynomial ℂ) (RatFunc ℂ) (b.val x).num =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (b.val x).denom * b.val x := by
      have h1 := congr_arg (algebraMap (Polynomial ℂ) (RatFunc ℂ) (b.val x).denom * ·) hnd
      rwa [mul_div_cancel₀ _ hden_ne] at h1
    calc algebraMap (Polynomial ℂ) (RatFunc ℂ) (w x)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (b.val x).num *
            algebraMap (Polynomial ℂ) (RatFunc ℂ) (∏ y ∈ Finset.univ.erase x, (b.val y).denom) := by
          simp [w]
      _ = (algebraMap (Polynomial ℂ) (RatFunc ℂ) (b.val x).denom * b.val x) *
            algebraMap (Polynomial ℂ) (RatFunc ℂ) (∏ y ∈ Finset.univ.erase x, (b.val y).denom) := by
          rw [hmul_b]
      _ = algebraMap (Polynomial ℂ) (RatFunc ℂ) Db * b.val x := by
          rw [hsplit, map_mul]; ring
  have hpolyMul_zero : ∀ u : G, polyMul G v w u = 0 := by
    intro u
    refine IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) ?_
    rw [map_zero]
    have hab_u : (a * b).val u = 0 := congr_fun (congr_arg LAlg.val hab) u
    change algebraMap (Polynomial ℂ) (RatFunc ℂ) (∑ x : G, ∑ y : G, pPoly G x y u * v x * w y) = 0
    simp only [map_sum, map_mul, hv_eq, hw_eq]
    have hfactor : (∑ x : G, ∑ y : G,
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (pPoly G x y u) *
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) Da * a.val x) *
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) Db * b.val y)) =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) Da * algebraMap (Polynomial ℂ) (RatFunc ℂ) Db *
          qRat G * (a * b).val u := by
      change _ = algebraMap (Polynomial ℂ) (RatFunc ℂ) Da * algebraMap (Polynomial ℂ) (RatFunc ℂ) Db *
          qRat G * ((qRat G)⁻¹ * ∑ x : G, ∑ y : G, pRat G x y u * a.val x * b.val y)
      rw [mul_assoc _ (qRat G), ← mul_assoc (qRat G), mul_inv_cancel₀ (qRat_ne_zero G), one_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => by simp only [pRat]; ring
    rw [hfactor, hab_u, mul_zero]
  -- Pointwise product vTilde v 1 z * vTilde w 1 z = 0 on Ubig
  have hprod_zero : ∀ z ∈ Ubig, vTilde G v 1 z * vTilde G w 1 z = 0 := by
    intro z hz
    have h1 := eval_polyMul_convAct G v w (Ubig_subset_U0 G hz) 1
    have h0 : (fun u => (polyMul G v w u).eval z) = 0 := by
      funext u; rw [hpolyMul_zero u, Polynomial.eval_zero]; rfl
    rw [h0] at h1
    have hconv0 : GroupAlg.convAct (BFun G z) 0 1 = 0 := by simp [GroupAlg.convAct]
    rw [hconv0] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (qPoly_eval_ne_zero_of_Ubig G hz)
  by_cases hv1 : ∀ z ∈ Ubig, vTilde G v 1 z = 0
  · left
    have hv0 := poly_eq_zero_of_vTilde_zero G v 1 hv1
    refine LAlg.ext G fun x => ?_
    have h := hv_eq x
    rw [hv0 x, map_zero] at h
    exact (mul_eq_zero.1 h.symm).resolve_left hDa_rat
  · right
    push Not at hv1
    obtain ⟨z₀, hz₀, hne⟩ := hv1
    have hw1 : ∀ z ∈ Ubig, vTilde G w 1 z = 0 := by
      have hcont_v : ContinuousAt (vTilde G v 1) z₀ :=
        ((differentiableOn_vTilde G v 1).mono (Ubig_subset_U0 G)).continuousOn.continuousAt
          (isOpen_Ubig.mem_nhds hz₀)
      have hne_ev : ∀ᶠ z in 𝓝 z₀, vTilde G v 1 z ≠ 0 :=
        hcont_v.eventually_ne hne
      have hev_w : vTilde G w 1 =ᶠ[𝓝 z₀] 0 := by
        filter_upwards [isOpen_Ubig.mem_nhds hz₀, hne_ev] with z hz hvne
        exact (mul_eq_zero.1 (hprod_zero z hz)).resolve_left hvne
      have hanal_w : AnalyticOnNhd ℂ (vTilde G w 1) Ubig :=
        ((differentiableOn_vTilde G w 1).mono (Ubig_subset_U0 G)).analyticOnNhd isOpen_Ubig
      exact fun z hz => hanal_w.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        convex_Ubig.isPreconnected hz₀ hev_w hz
    have hw0 := poly_eq_zero_of_vTilde_zero G w 1 hw1
    refine LAlg.ext G fun x => ?_
    have h := hw_eq x
    rw [hw0 x, map_zero] at h
    exact (mul_eq_zero.1 h.symm).resolve_left hDb_rat⟩

instance : IsDomain (LAlg G) := NoZeroDivisors.to_isDomain (LAlg G)

end ComplexRealization

/- Section 7: Final Part I Theorem `realize_complex` -/

theorem realize_complex (G : Type) [Fintype G] [Group G] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L)
      (_ : IsGalois (RatFunc ℂ) L) (_ : FiniteDimensional (RatFunc ℂ) L),
      Nonempty (G ≃* (L ≃ₐ[RatFunc ℂ] L)) := by
  classical
  let _ : Algebra.IsIntegral (RatFunc ℂ) (LAlg G) := Algebra.IsIntegral.of_finite _ _
  have hinj : Function.Injective (algebraMap (RatFunc ℂ) (LAlg G)) := by
    intro r s h
    exact congr_fun (congr_arg LAlg.val h) (1 : G)
  have hisField : IsField (LAlg G) :=
    (Algebra.IsIntegral.isField_iff_isField (R := RatFunc ℂ) (S := LAlg G) hinj).1
      (Field.toIsField (RatFunc ℂ))
  let _ : Field (LAlg G) := hisField.toField
  have hfinrank : Module.finrank (RatFunc ℂ) (LAlg G) = Fintype.card G := finrank_LAlg G
  have hautG_inj : Function.Injective (rhoHom G) := rhoHom_injective G
  have : Finite (LAlg G ≃ₐ[RatFunc ℂ] LAlg G) := inferInstance
  have hle1 : Fintype.card G ≤ Nat.card (LAlg G ≃ₐ[RatFunc ℂ] LAlg G) := by
    have hN' : Fintype.card G = Nat.card G := (Nat.card_eq_fintype_card).symm
    rw [hN']
    exact Nat.card_le_card_of_injective (rhoHom G) hautG_inj
  have hle2 : Nat.card (LAlg G ≃ₐ[RatFunc ℂ] LAlg G) ≤ Fintype.card G := by
    have hmul := Module.finrank_mul_finrank (RatFunc ℂ)
      (IntermediateField.fixedField (⊤ : Subgroup (LAlg G ≃ₐ[RatFunc ℂ] LAlg G))) (LAlg G)
    rw [hfinrank, IntermediateField.finrank_fixedField_eq_card] at hmul
    have hpos : 0 < Module.finrank (RatFunc ℂ)
        (IntermediateField.fixedField (⊤ : Subgroup (LAlg G ≃ₐ[RatFunc ℂ] LAlg G))) :=
      Module.finrank_pos
    have htop : Nat.card (⊤ : Subgroup (LAlg G ≃ₐ[RatFunc ℂ] LAlg G)) =
        Nat.card (LAlg G ≃ₐ[RatFunc ℂ] LAlg G) :=
      Nat.card_congr {
        toFun := fun σ => σ.1
        invFun := fun σ => ⟨σ, Subgroup.mem_top σ⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
      }
    rw [htop] at hmul
    nlinarith
  have hcard_eq : Nat.card (LAlg G ≃ₐ[RatFunc ℂ] LAlg G) = Module.finrank (RatFunc ℂ) (LAlg G) := by
    omega
  have : IsGalois (RatFunc ℂ) (LAlg G) := IsGalois.of_card_aut_eq_finrank (RatFunc ℂ) (LAlg G) hcard_eq
  let _ : Fintype (LAlg G ≃ₐ[RatFunc ℂ] LAlg G) := Fintype.ofFinite _
  have hautG_bij : Function.Bijective (rhoHom G) :=
    (Fintype.bijective_iff_injective_and_card (rhoHom G)).2
      ⟨hautG_inj, by
        have h2 : Fintype.card (LAlg G ≃ₐ[RatFunc ℂ] LAlg G) =
            Nat.card (LAlg G ≃ₐ[RatFunc ℂ] LAlg G) := (Nat.card_eq_fintype_card).symm
        omega⟩
  exact ⟨LAlg G, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨MulEquiv.ofBijective (rhoHom G) hautG_bij⟩⟩

end StrategyBPart1c

namespace StrategyBPart2
open Polynomial FirstOrder Language FirstOrder.Ring FirstOrder.Field IntermediateField

-- Helper: transport IsRealizable along a MulEquiv
lemma isRealizable_of_mulEquiv {F G H : Type*} [Field F] [Group G] [Group H]
    (e : G ≃* H) (hG : InverseGalois.IsRealizable F G) : InverseGalois.IsRealizable F H := by
  obtain ⟨r⟩ := hG.exists_realization
  exact ⟨⟨{
    L := r.L
    to_field := r.to_field
    to_algebra := r.to_algebra
    to_isGalois := r.to_isGalois
    iso := e.symm.trans r.iso
  }⟩⟩

-- Helper: trivial group is realizable over any field
lemma isRealizable_of_subsingleton {F G : Type*} [Field F] [Group G] [Subsingleton G] :
    InverseGalois.IsRealizable F G := by
  have : Subsingleton (F ≃ₐ[F] F) := ⟨fun f g => by
    ext x
    have hf : f x = x := by simpa using f.commutes x
    have hg : g x = x := by simpa using g.commutes x
    rw [hf, hg]⟩
  exact ⟨⟨{
    L := F
    to_field := inferInstance
    to_algebra := Algebra.id F
    to_isGalois := inferInstance
    iso := {
      toFun := fun _ => 1
      invFun := fun _ => 1
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_mul' := fun _ _ => (mul_one _).symm
    }
  }⟩⟩

-- Helper: BoundedDeg predicate for bivariate polynomials R[t][X]
def BoundedDeg {R : Type*} [Semiring R] (M_X M_t : ℕ) (P : R[X][X]) : Prop :=
  (∀ i > M_X, P.coeff i = 0) ∧ (∀ i, ∀ j > M_t, (P.coeff i).coeff j = 0)

lemma BoundedDeg.mono {R : Type*} [Semiring R] {M_X M_X' M_t M_t' : ℕ} {P : R[X][X]}
    (h : BoundedDeg M_X M_t P) (hX : M_X ≤ M_X') (ht : M_t ≤ M_t') :
    BoundedDeg M_X' M_t' P :=
  ⟨fun i hi => h.1 i (lt_of_le_of_lt hX hi), fun i j hj => h.2 i j (lt_of_le_of_lt ht hj)⟩

lemma BoundedDeg.map {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    {M_X M_t : ℕ} {P : R[X][X]} (h : BoundedDeg M_X M_t P) :
    BoundedDeg M_X M_t (P.map (Polynomial.mapRingHom φ)) := by
  refine ⟨fun i hi => ?_, fun i j hj => ?_⟩
  · rw [coeff_map, h.1 i hi, map_zero]
  · rw [coeff_map, coe_mapRingHom, coeff_map, h.2 i j hj, map_zero]

lemma BoundedDeg.ext {R : Type*} [Semiring R] {M_X M_t : ℕ} {P Q : R[X][X]}
    (hP : BoundedDeg M_X M_t P) (hQ : BoundedDeg M_X M_t Q)
    (h : ∀ i ≤ M_X, ∀ j ≤ M_t, (P.coeff i).coeff j = (Q.coeff i).coeff j) : P = Q := by
  ext i j
  by_cases hi : i ≤ M_X
  · by_cases hj : j ≤ M_t
    · exact h i hi j hj
    · rw [hP.2 i j (not_le.1 hj), hQ.2 i j (not_le.1 hj)]
  · rw [hP.1 i (not_le.1 hi), hQ.1 i (not_le.1 hi)]

lemma BoundedDeg.zero {R : Type*} [Semiring R] (M_X M_t : ℕ) : BoundedDeg M_X M_t (0 : R[X][X]) :=
  ⟨fun _ _ => by simp, fun _ _ _ => by simp⟩

lemma BoundedDeg.one {R : Type*} [Semiring R] (M_X M_t : ℕ) : BoundedDeg M_X M_t (1 : R[X][X]) := by
  refine ⟨fun i hi => ?_, fun i j hj => ?_⟩
  · rw [coeff_one, if_neg (by omega)]
  · by_cases hi : i = 0
    · subst hi; rw [coeff_one_zero, coeff_one, if_neg (by omega)]
    · rw [coeff_one, if_neg hi, coeff_zero]

lemma BoundedDeg.add {R : Type*} [Semiring R] {M_X M_t : ℕ} {P Q : R[X][X]}
    (hP : BoundedDeg M_X M_t P) (hQ : BoundedDeg M_X M_t Q) :
    BoundedDeg M_X M_t (P + Q) :=
  ⟨fun i hi => by simp [hP.1 i hi, hQ.1 i hi],
   fun i j hj => by simp [hP.2 i j hj, hQ.2 i j hj]⟩

lemma BoundedDeg.sub {R : Type*} [Ring R] {M_X M_t : ℕ} {P Q : R[X][X]}
    (hP : BoundedDeg M_X M_t P) (hQ : BoundedDeg M_X M_t Q) :
    BoundedDeg M_X M_t (P - Q) :=
  ⟨fun i hi => by simp [hP.1 i hi, hQ.1 i hi],
   fun i j hj => by simp [hP.2 i j hj, hQ.2 i j hj]⟩

lemma BoundedDeg.sum {R ι : Type*} [Semiring R] {s : Finset ι} {M_X M_t : ℕ}
    {f : ι → R[X][X]} (hf : ∀ a ∈ s, BoundedDeg M_X M_t (f a)) :
    BoundedDeg M_X M_t (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BoundedDeg.zero M_X M_t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

lemma BoundedDeg.mul {R : Type*} [Semiring R] {M1 M2 D1 D2 : ℕ} {P Q : R[X][X]}
    (hP : BoundedDeg M1 D1 P) (hQ : BoundedDeg M2 D2 Q) :
    BoundedDeg (M1 + M2) (D1 + D2) (P * Q) := by
  refine ⟨fun i hi => ?_, fun i j hj => ?_⟩
  · rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro xy hxy
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
    by_cases h1 : xy.1 > M1
    · rw [hP.1 xy.1 h1, zero_mul]
    · have h2 : xy.2 > M2 := by omega
      rw [hQ.1 xy.2 h2, mul_zero]
  · rw [coeff_mul, finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro xy _
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ab hab
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    by_cases h1 : ab.1 > D1
    · rw [hP.2 xy.1 ab.1 h1, zero_mul]
    · have h2 : ab.2 > D2 := by omega
      rw [hQ.2 xy.2 ab.2 h2, mul_zero]

lemma BoundedDeg.pow {R : Type*} [Semiring R] {M D : ℕ} {P : R[X][X]}
    (hP : BoundedDeg M D P) (k : ℕ) : BoundedDeg (k * M) (k * D) (P ^ k) := by
  induction k with
  | zero => simpa using BoundedDeg.one 0 0
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul, Nat.succ_mul]
    exact ih.mul hP

lemma BoundedDeg.C_poly {R : Type*} [Semiring R] {D : ℕ} {p : R[X]}
    (hp : ∀ j > D, p.coeff j = 0) : BoundedDeg 0 D (C p) := by
  refine ⟨fun i hi => ?_, fun i j hj => ?_⟩
  · rw [coeff_C, if_neg (by omega)]
  · by_cases hi : i = 0
    · subst hi; rw [coeff_C_zero]; exact hp j hj
    · rw [coeff_C, if_neg hi, coeff_zero]

lemma BoundedDeg.X_pow {R : Type*} [Semiring R] (N : ℕ) : BoundedDeg N 0 (X ^ N : R[X][X]) := by
  refine ⟨fun i hi => ?_, fun i j hj => ?_⟩
  · rw [coeff_X_pow, if_neg (by omega)]
  · rw [coeff_X_pow]
    split_ifs
    · rw [coeff_one, if_neg (by omega)]
    · rw [coeff_zero]

-- Max t-degree of a polynomial in K[t][X]
noncomputable def polyDegT {R : Type*} [Semiring R] (p : R[X][X]) : ℕ :=
  p.support.sup (fun i => (p.coeff i).natDegree)

lemma natDegree_coeff_le_polyDegT {R : Type*} [Semiring R] (p : R[X][X]) (i : ℕ) :
    (p.coeff i).natDegree ≤ polyDegT p := by
  by_cases hi : i ∈ p.support
  · exact Finset.le_sup (f := fun i => (p.coeff i).natDegree) hi
  · rw [mem_support_iff, not_not] at hi
    simp [hi]

lemma polyDegT_le_iff {R : Type*} [Semiring R] {p : R[X][X]} {D : ℕ} :
    polyDegT p ≤ D ↔ ∀ i, (p.coeff i).natDegree ≤ D := by
  constructor
  · intro h i; exact (natDegree_coeff_le_polyDegT p i).trans h
  · intro h; exact Finset.sup_le (fun i _ => h i)

-- Key 10-line degree bound: polyDegT (g * h) = polyDegT g + polyDegT h for nonzero g, h over a domain
lemma polyDegT_mul {K : Type*} [CommRing K] [IsDomain K] {g h : K[X][X]}
    (hg : g ≠ 0) (hh : h ≠ 0) : polyDegT (g * h) = polyDegT g + polyDegT h := by
  apply le_antisymm
  · rw [polyDegT_le_iff]
    intro n
    rw [coeff_mul]
    refine (natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun xy _ => ?_⟩
    exact natDegree_mul_le.trans
      (add_le_add (natDegree_coeff_le_polyDegT g xy.1) (natDegree_coeff_le_polyDegT h xy.2))
  · have hg_ne : g.support.Nonempty := support_nonempty.2 hg
    have hh_ne : h.support.Nonempty := support_nonempty.2 hh
    obtain ⟨i₁, hi₁, hdeg_i₁⟩ := Finset.exists_mem_eq_sup g.support hg_ne (fun i => (g.coeff i).natDegree)
    obtain ⟨j₁, hj₁, hdeg_j₁⟩ := Finset.exists_mem_eq_sup h.support hh_ne (fun j => (h.coeff j).natDegree)
    let Sg := g.support.filter (fun i => (g.coeff i).natDegree = polyDegT g)
    let Sh := h.support.filter (fun j => (h.coeff j).natDegree = polyDegT h)
    have hSg : Sg.Nonempty := ⟨i₁, Finset.mem_filter.2 ⟨hi₁, hdeg_i₁.symm⟩⟩
    have hSh : Sh.Nonempty := ⟨j₁, Finset.mem_filter.2 ⟨hj₁, hdeg_j₁.symm⟩⟩
    let i₀ := Sg.max' hSg
    let j₀ := Sh.max' hSh
    have hi₀_mem : i₀ ∈ Sg := Finset.max'_mem Sg hSg
    have hj₀_mem : j₀ ∈ Sh := Finset.max'_mem Sh hSh
    have hi₀_ne : g.coeff i₀ ≠ 0 := mem_support_iff.1 (Finset.mem_filter.1 hi₀_mem).1
    have hj₀_ne : h.coeff j₀ ≠ 0 := mem_support_iff.1 (Finset.mem_filter.1 hj₀_mem).1
    have hi₀_deg : (g.coeff i₀).natDegree = polyDegT g := (Finset.mem_filter.1 hi₀_mem).2
    have hj₀_deg : (h.coeff j₀).natDegree = polyDegT h := (Finset.mem_filter.1 hj₀_mem).2
    have hlead : (g.coeff i₀ * h.coeff j₀).natDegree = polyDegT g + polyDegT h := by
      rw [natDegree_mul hi₀_ne hj₀_ne, hi₀_deg, hj₀_deg]
    let S := Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)
    have hmem : (i₀, j₀) ∈ S := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    have h_eq : (g * h).coeff (i₀ + j₀) = g.coeff i₀ * h.coeff j₀ +
        ∑ xy ∈ S.erase (i₀, j₀), g.coeff xy.1 * h.coeff xy.2 := by
      rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have hrest_lt : (∑ xy ∈ S.erase (i₀, j₀),
        g.coeff xy.1 * h.coeff xy.2).degree < (g.coeff i₀ * h.coeff j₀).degree := by
      have hprod_ne : g.coeff i₀ * h.coeff j₀ ≠ 0 := mul_ne_zero hi₀_ne hj₀_ne
      rw [degree_eq_natDegree hprod_ne, hlead]
      refine (degree_sum_le _ _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro xy hxy
      have hxy_ne : xy ≠ (i₀, j₀) := (Finset.mem_erase.1 hxy).1
      have hxy_sum : xy.1 + xy.2 = i₀ + j₀ :=
        Finset.HasAntidiagonal.mem_antidiagonal.1 (Finset.mem_erase.1 hxy).2
      by_cases hzero : g.coeff xy.1 * h.coeff xy.2 = 0
      · rw [hzero, degree_zero]; exact WithBot.bot_lt_coe _
      · have h1ne : g.coeff xy.1 ≠ 0 := left_ne_zero_of_mul hzero
        have h2ne : h.coeff xy.2 ≠ 0 := right_ne_zero_of_mul hzero
        rw [degree_eq_natDegree hzero, natDegree_mul h1ne h2ne]
        suffices hnat : (g.coeff xy.1).natDegree + (h.coeff xy.2).natDegree < polyDegT g + polyDegT h by
          exact_mod_cast hnat
        by_cases hgt : i₀ < xy.1
        · have hlt : (g.coeff xy.1).natDegree < polyDegT g := by
            have hle := natDegree_coeff_le_polyDegT g xy.1
            refine lt_of_le_of_ne hle (fun heq => ?_)
            have hmem' : xy.1 ∈ Sg := Finset.mem_filter.2 ⟨mem_support_iff.2 h1ne, heq⟩
            exact not_le_of_gt hgt (Finset.le_max' Sg xy.1 hmem')
          exact add_lt_add_of_lt_of_le hlt (natDegree_coeff_le_polyDegT h xy.2)
        · have hgt2 : j₀ < xy.2 := by
            by_contra hle2
            have heq1 : xy.1 = i₀ := by omega
            have heq2 : xy.2 = j₀ := by omega
            exact hxy_ne (Prod.ext heq1 heq2)
          have hlt : (h.coeff xy.2).natDegree < polyDegT h := by
            have hle := natDegree_coeff_le_polyDegT h xy.2
            refine lt_of_le_of_ne hle (fun heq => ?_)
            have hmem' : xy.2 ∈ Sh := Finset.mem_filter.2 ⟨mem_support_iff.2 h2ne, heq⟩
            exact not_le_of_gt hgt2 (Finset.le_max' Sh xy.2 hmem')
          exact add_lt_add_of_le_of_lt (natDegree_coeff_le_polyDegT g xy.1) hlt
    have hdeg_eq : ((g * h).coeff (i₀ + j₀)).natDegree = polyDegT g + polyDegT h := by
      have hprod_ne : g.coeff i₀ * h.coeff j₀ ≠ 0 := mul_ne_zero hi₀_ne hj₀_ne
      have hdeg := degree_add_eq_left_of_degree_lt hrest_lt
      rw [← h_eq] at hdeg
      have hne_sum : (g * h).coeff (i₀ + j₀) ≠ 0 := by
        intro hz; rw [hz, degree_zero] at hdeg
        exact absurd hdeg.symm (by rw [degree_eq_natDegree hprod_ne]; exact WithBot.coe_ne_bot)
      rw [degree_eq_natDegree hne_sum, degree_eq_natDegree hprod_ne] at hdeg
      have hdeg' : ((g * h).coeff (i₀ + j₀)).natDegree = (g.coeff i₀ * h.coeff j₀).natDegree := by
        exact_mod_cast hdeg
      rw [hdeg', hlead]
    rw [← hdeg_eq]
    exact natDegree_coeff_le_polyDegT (g * h) (i₀ + j₀)

-- Monic Gauss's lemma via IsIntegrallyClosed K[X] + Polynomial.isIntegral_coeff_of_dvd
lemma exists_monic_lift_of_dvd_map {K : Type*} [Field K] {f : K[X][X]} (hf : f.Monic)
    {g₀ : (RatFunc K)[X]} (hg₀ : g₀.Monic)
    (hdvd : g₀ ∣ f.map (algebraMap K[X] (RatFunc K))) :
    ∃ g : K[X][X], g.Monic ∧ g.map (algebraMap K[X] (RatFunc K)) = g₀ := by
  have hcoeff : ∀ i, ∃ c : K[X], algebraMap K[X] (RatFunc K) c = g₀.coeff i := by
    intro i
    have hint : IsIntegral K[X] (g₀.coeff i) :=
      Polynomial.isIntegral_coeff_of_dvd f g₀ hf hg₀ hdvd i
    exact (IsIntegrallyClosed.isIntegral_iff (R := K[X]) (K := RatFunc K)).1 hint
  choose c hc using hcoeff
  let g : K[X][X] := ∑ i ∈ Finset.range (g₀.natDegree + 1), C (c i) * X ^ i
  have hmap : g.map (algebraMap K[X] (RatFunc K)) = g₀ := by
    ext i
    simp only [g, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
      finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hi
    · exact hc i
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hmonic : g.Monic := by
    have hinj := IsFractionRing.injective K[X] (RatFunc K)
    rw [Polynomial.Monic, ← hinj.eq_iff, map_one]
    change algebraMap K[X] (RatFunc K) (g.coeff g.natDegree) = 1
    rw [← coeff_map, ← natDegree_map_eq_of_injective hinj, hmap]
    exact hg₀.leadingCoeff
  exact ⟨g, hmonic, hmap⟩

lemma irreducible_map_of_no_bounded_monic_factor {K : Type*} [Field K]
    {f : K[X][X]} (hf : f.Monic) (hfdeg : 1 ≤ f.natDegree) {D : ℕ} (hfD : polyDegT f ≤ D)
    (hno : ∀ g h : K[X][X], g.Monic → h.Monic → 1 ≤ g.natDegree → g.natDegree < f.natDegree →
      polyDegT g ≤ D → polyDegT h ≤ D → f ≠ g * h) :
    Irreducible (f.map (algebraMap K[X] (RatFunc K))) := by
  set φ := algebraMap K[X] (RatFunc K)
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] (RatFunc K)
  have hfm : (f.map φ).Monic := hf.map φ
  have hfdeg' : (f.map φ).natDegree = f.natDegree := natDegree_map_eq_of_injective hinj _
  refine ⟨?_, ?_⟩
  · intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  · intro a b hab
    by_contra hnot
    push Not at hnot
    have ha0 : a ≠ 0 := by rintro rfl; simp only [zero_mul] at hab; exact hfm.ne_zero hab
    have hb0 : b ≠ 0 := by rintro rfl; simp only [mul_zero] at hab; exact hfm.ne_zero hab
    have ha_pos : 1 ≤ a.natDegree := by
      by_contra hlt
      have h0 : a.natDegree = 0 := by omega
      exact hnot.1 (isUnit_iff_degree_eq_zero.2 (by rw [degree_eq_natDegree ha0, h0]; rfl))
    have hb_pos : 1 ≤ b.natDegree := by
      by_contra hlt
      have h0 : b.natDegree = 0 := by omega
      exact hnot.2 (isUnit_iff_degree_eq_zero.2 (by rw [degree_eq_natDegree hb0, h0]; rfl))
    let g₀ := C a.leadingCoeff⁻¹ * a
    let h₀ := C b.leadingCoeff⁻¹ * b
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, ← hab, hfm.leadingCoeff]
    have hg₀ : g₀.Monic := by
      rw [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C,
        inv_mul_cancel₀ (leadingCoeff_ne_zero.2 ha0)]
    have hh₀ : h₀.Monic := by
      rw [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C,
        inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hb0)]
    have hmul₀ : f.map φ = g₀ * h₀ := by
      have hinv1 : a.leadingCoeff⁻¹ * b.leadingCoeff⁻¹ = 1 := by
        rw [← mul_inv, hlc, inv_one]
      calc f.map φ = a * b := hab
        _ = C (a.leadingCoeff⁻¹ * b.leadingCoeff⁻¹) * (a * b) := by
            rw [hinv1, map_one, one_mul]
        _ = g₀ * h₀ := by simp only [g₀, h₀, map_mul]; ring
    obtain ⟨g, hg, hgm⟩ := exists_monic_lift_of_dvd_map hf hg₀ ⟨h₀, hmul₀⟩
    obtain ⟨h, hh, hhm⟩ := exists_monic_lift_of_dvd_map hf hh₀ ⟨g₀, hmul₀.trans (mul_comm _ _)⟩
    have hfg : f = g * h := by
      apply Polynomial.map_injective φ hinj
      rw [Polynomial.map_mul, hgm, hhm, hmul₀]
    have hg_deg : g.natDegree = a.natDegree := by
      rw [← natDegree_map_eq_of_injective hinj g, hgm]
      exact natDegree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.2 ha0))
    have hh_deg : h.natDegree = b.natDegree := by
      rw [← natDegree_map_eq_of_injective hinj h, hhm]
      exact natDegree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.2 hb0))
    have hsum_deg : a.natDegree + b.natDegree = f.natDegree := by
      rw [← natDegree_mul ha0 hb0, ← hab, hfdeg']
    have hDsum : polyDegT g + polyDegT h ≤ D := by
      rw [← polyDegT_mul hg.ne_zero hh.ne_zero, ← hfg]; exact hfD
    exact hno g h hg hh (by omega) (by omega) (by omega) (by omega) hfg

-- Generic polynomial builders over any CommRing R
noncomputable def mkPolyT {R : Type*} [Semiring R] {D : ℕ} (c : Fin (D + 1) → R) : R[X] :=
  ∑ j : Fin (D + 1), C (c j) * X ^ j.1

noncomputable def mkPolyTX {R : Type*} [Semiring R] {M D : ℕ}
    (c : Fin M → Fin (D + 1) → R) : R[X][X] :=
  ∑ k : Fin M, C (mkPolyT (c k)) * X ^ k.1

noncomputable def mkMonicPolyTX {R : Type*} [Semiring R] {N D : ℕ}
    (c : Fin N → Fin (D + 1) → R) : R[X][X] :=
  X ^ N + mkPolyTX c

lemma map_mkPolyT {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) {D : ℕ}
    (c : Fin (D + 1) → R) :
    (mkPolyT c).map φ = mkPolyT (fun j => φ (c j)) := by
  simp [mkPolyT, Polynomial.map_sum]

lemma map_mkPolyTX {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) {M D : ℕ}
    (c : Fin M → Fin (D + 1) → R) :
    (mkPolyTX c).map (Polynomial.mapRingHom φ) = mkPolyTX (fun k j => φ (c k j)) := by
  simp [mkPolyTX, Polynomial.map_sum, map_mkPolyT]

lemma map_mkMonicPolyTX {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) {N D : ℕ}
    (c : Fin N → Fin (D + 1) → R) :
    (mkMonicPolyTX c).map (Polynomial.mapRingHom φ) = mkMonicPolyTX (fun k j => φ (c k j)) := by
  simp [mkMonicPolyTX, map_mkPolyTX]

lemma coeff_mkPolyT {R : Type*} [Semiring R] {D : ℕ} (c : Fin (D + 1) → R) (j : ℕ) :
    (mkPolyT c).coeff j = if h : j < D + 1 then c ⟨j, h⟩ else 0 := by
  simp only [mkPolyT, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro heq; exact hb (Fin.ext heq.symm)
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]; omega

lemma coeff_mkPolyTX {R : Type*} [Semiring R] {M D : ℕ}
    (c : Fin M → Fin (D + 1) → R) (k : ℕ) :
    (mkPolyTX c).coeff k = if h : k < M then mkPolyT (c ⟨k, h⟩) else 0 := by
  simp only [mkPolyTX, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro heq; exact hb (Fin.ext heq.symm)
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]; omega

lemma boundedDeg_mkPolyTX {R : Type*} [Semiring R] {M D : ℕ}
    (c : Fin M → Fin (D + 1) → R) : BoundedDeg M D (mkPolyTX c) := by
  refine ⟨fun i hi => ?_, fun i j hj => ?_⟩
  · rw [coeff_mkPolyTX, dif_neg (by omega)]
  · rw [coeff_mkPolyTX]
    split_ifs with hi
    · rw [coeff_mkPolyT, dif_neg (by omega)]
    · rw [coeff_zero]

lemma boundedDeg_mkPolyTX_pred {R : Type*} [Semiring R] {M D : ℕ}
    (c : Fin (M + 1) → Fin (D + 1) → R) : BoundedDeg M D (mkPolyTX c) := by
  refine ⟨fun i hi => ?_, fun i j hj => ?_⟩
  · rw [coeff_mkPolyTX, dif_neg (by omega)]
  · rw [coeff_mkPolyTX]
    split_ifs with hi
    · rw [coeff_mkPolyT, dif_neg (by omega)]
    · rw [coeff_zero]

lemma boundedDeg_mkMonicPolyTX {R : Type*} [Semiring R] {N D : ℕ}
    (c : Fin N → Fin (D + 1) → R) : BoundedDeg N D (mkMonicPolyTX c) := by
  rw [mkMonicPolyTX]
  exact ((BoundedDeg.X_pow (R := R) N).mono le_rfl (Nat.zero_le D)).add (boundedDeg_mkPolyTX (R := R) c)

lemma monic_mkMonicPolyTX {R : Type*} [Semiring R] [Nontrivial R] {N D : ℕ}
    (c : Fin N → Fin (D + 1) → R) : (mkMonicPolyTX c).Monic := by
  rw [mkMonicPolyTX]
  refine (monic_X_pow N).add_of_left ?_
  rw [degree_X_pow]
  refine (degree_lt_iff_coeff_zero _ _).2 (fun m hm => ?_)
  rw [coeff_mkPolyTX, dif_neg (by omega)]

lemma natDegree_mkMonicPolyTX {R : Type*} [Semiring R] [Nontrivial R] {N D : ℕ}
    (c : Fin N → Fin (D + 1) → R) : (mkMonicPolyTX c).natDegree = N := by
  apply le_antisymm
  · exact natDegree_le_iff_coeff_eq_zero.2 (fun i hi => (boundedDeg_mkMonicPolyTX c).1 i hi)
  · refine le_natDegree_of_ne_zero ?_
    rw [mkMonicPolyTX, coeff_add, coeff_X_pow_self, coeff_mkPolyTX, dif_neg (lt_irrefl N), add_zero]
    exact one_ne_zero

lemma polyDegT_mkMonicPolyTX_le {R : Type*} [Semiring R] {N D : ℕ}
    (c : Fin N → Fin (D + 1) → R) : polyDegT (mkMonicPolyTX c) ≤ D := by
  rw [polyDegT_le_iff]
  intro i
  exact natDegree_le_iff_coeff_eq_zero.2 (fun j hj => (boundedDeg_mkMonicPolyTX c).2 i j hj)

lemma mkPolyT_of_natDegree_le {R : Type*} [Semiring R] {D : ℕ} {p : R[X]}
    (hp : p.natDegree ≤ D) : mkPolyT (fun j : Fin (D + 1) => p.coeff j.1) = p := by
  ext j
  rw [coeff_mkPolyT]
  split_ifs with hj
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

lemma mkPolyTX_of_bounded {R : Type*} [Semiring R] {M D : ℕ} {p : R[X][X]}
    (hX : ∀ i ≥ M, p.coeff i = 0) (hD : polyDegT p ≤ D) :
    mkPolyTX (fun (k : Fin M) (j : Fin (D + 1)) => (p.coeff k.1).coeff j.1) = p := by
  ext k j
  rw [coeff_mkPolyTX]
  split_ifs with hk
  · rw [coeff_mkPolyT]
    split_ifs with hj
    · rfl
    · exact (coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt ((natDegree_coeff_le_polyDegT p k).trans hD) (by omega))).symm
  · rw [hX k (by omega), coeff_zero]

lemma mkMonicPolyTX_of_monic {R : Type*} [Semiring R] {N D : ℕ} {p : R[X][X]}
    (hm : p.Monic) (hdeg : p.natDegree = N) (hD : polyDegT p ≤ D) :
    mkMonicPolyTX (fun (k : Fin N) (j : Fin (D + 1)) => (p.coeff k.1).coeff j.1) = p := by
  ext k j
  rw [mkMonicPolyTX, coeff_add, coeff_X_pow, coeff_mkPolyTX]
  by_cases hlt : k < N
  · rw [if_neg (by omega), zero_add, dif_pos hlt, coeff_mkPolyT]
    split_ifs with hj
    · rfl
    · exact (coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt ((natDegree_coeff_le_polyDegT p k).trans hD) (by omega))).symm
  · by_cases heq : k = N
    · subst heq
      rw [if_pos rfl, dif_neg (lt_irrefl _), add_zero]
      have hlc : p.coeff k = 1 := by rw [← hdeg]; exact hm.leadingCoeff
      rw [hlc]
    · rw [if_neg heq, dif_neg hlt, add_zero, coeff_zero]
      have hk_gt : p.natDegree < k := by omega
      rw [coeff_eq_zero_of_natDegree_lt hk_gt, coeff_zero]

-- First-order polynomial equality formula over FreeCommRing α
noncomputable def evalHom {α K : Type*} [CommRing K] (v : α → K) :
    (FreeCommRing α)[X][X] →+* K[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (FreeCommRing.lift v))

noncomputable def polyEqFormula {α : Type*} (M_X M_t : ℕ)
    (P Q : (FreeCommRing α)[X][X]) : Language.ring.Formula α :=
  Formula.iInf (fun i : Fin (M_X + 1) => Formula.iInf (fun j : Fin (M_t + 1) =>
    Term.equal (termOfFreeCommRing ((P.coeff i.1).coeff j.1))
               (termOfFreeCommRing ((Q.coeff i.1).coeff j.1))))

lemma realize_polyEqFormula {α K : Type*} [CommRing K] [CompatibleRing K]
    {M_X M_t : ℕ} {P Q : (FreeCommRing α)[X][X]}
    (hP : BoundedDeg M_X M_t P) (hQ : BoundedDeg M_X M_t Q) (v : α → K) :
    (polyEqFormula M_X M_t P Q).Realize v ↔ evalHom v P = evalHom v Q := by
  simp only [polyEqFormula, Formula.realize_iInf]
  simp only [Term.equal, Formula.Realize, BoundedFormula.realize_bdEqual,
    Term.realize_relabel, Sum.elim_comp_inl, realize_termOfFreeCommRing]
  constructor
  · intro h
    apply BoundedDeg.ext (hP.map _) (hQ.map _)
    intro i hi j hj
    have hij := h ⟨i, by omega⟩ ⟨j, by omega⟩
    simpa [evalHom, coeff_map] using hij
  · intro h i j
    have hij := congr_arg (fun p : K[X][X] => (p.coeff i.1).coeff j.1) h
    simpa [evalHom, coeff_map] using hij

-- Witness variable indexing type (all in Type 0 for G : Type 0)
inductive WitnessVar (G : Type) (N D D' M_W D_W M_U D_U : ℕ) : Type
  | f : Fin N → Fin (D + 1) → WitnessVar G N D D' M_W D_W M_U D_U
  | Q : Fin (D' + 1) → WitnessVar G N D D' M_W D_W M_U D_U
  | R : G → Fin N → Fin (D' + 1) → WitnessVar G N D D' M_W D_W M_U D_U
  | W : G → Fin (M_W + 1) → Fin (D_W + 1) → WitnessVar G N D D' M_W D_W M_U D_U
  | U : G → G → Fin (M_U + 1) → Fin (D_U + 1) → WitnessVar G N D D' M_W D_W M_U D_U

instance finite_witnessVar (G : Type) [Finite G] (N D D' M_W D_W M_U D_U : ℕ) :
    Finite (WitnessVar G N D D' M_W D_W M_U D_U) := by
  let enc : WitnessVar G N D D' M_W D_W M_U D_U →
      (Fin N × Fin (D + 1)) ⊕ Fin (D' + 1) ⊕ (G × Fin N × Fin (D' + 1)) ⊕
      (G × Fin (M_W + 1) × Fin (D_W + 1)) ⊕ (G × G × Fin (M_U + 1) × Fin (D_U + 1))
    | .f k j => Sum.inl (k, j)
    | .Q j => Sum.inr (Sum.inl j)
    | .R g k j => Sum.inr (Sum.inr (Sum.inl (g, k, j)))
    | .W g k j => Sum.inr (Sum.inr (Sum.inr (Sum.inl (g, k, j))))
    | .U g h k j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (g, h, k, j))))
  refine Finite.of_injective enc ?_
  rintro (_ | _ | _ | _ | _) (_ | _ | _ | _ | _) h <;> simp_all [enc]

abbrev FactorVar (N D : ℕ) (m : Fin (N - 1)) : Type :=
  (Fin (m.1 + 1) × Fin (D + 1)) ⊕ (Fin (N - (m.1 + 1)) × Fin (D + 1))

-- Generic homogenized substitution: ∑_{k=0}^{N} (P.coeff k) * Q^(N - k) * R^k
noncomputable def homSubst {R : Type*} [CommRing R] (N : ℕ) (P : R[X][X])
    (Q : R[X]) (S : R[X][X]) : R[X][X] :=
  ∑ k ∈ Finset.range (N + 1), C (P.coeff k * Q ^ (N - k)) * S ^ k

lemma map_homSubst {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ℕ) (P : R[X][X]) (Q : R[X]) (T : R[X][X]) :
    (homSubst N P Q T).map (Polynomial.mapRingHom φ) =
      homSubst N (P.map (Polynomial.mapRingHom φ)) (Q.map φ) (T.map (Polynomial.mapRingHom φ)) := by
  simp [homSubst, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow]

lemma boundedDeg_homSubst {R : Type*} [CommRing R] {N D D' M_S : ℕ}
    {P : R[X][X]} {Q : R[X]} {S : R[X][X]}
    (hP : BoundedDeg N D P) (hQ : ∀ j > D', Q.coeff j = 0) (hS : BoundedDeg M_S D' S) :
    BoundedDeg (N * M_S) (D + N * D') (homSubst N P Q S) := by
  apply BoundedDeg.sum
  intro k hk
  rw [Finset.mem_range] at hk
  have hQpow : ∀ j > (N - k) * D', (Q ^ (N - k)).coeff j = 0 := by
    have h1 := (BoundedDeg.C_poly hQ).pow (N - k)
    intro j hj
    have h2 := h1.2 0 j hj
    simpa [← map_pow, coeff_C_zero] using h2
  have hC : BoundedDeg 0 (D + (N - k) * D') (C (P.coeff k * Q ^ (N - k))) := by
    have h1 := BoundedDeg.C_poly (hP.2 k)
    have h2 := BoundedDeg.C_poly hQpow
    simpa [map_mul] using h1.mul h2
  have hSk := hS.pow k
  have hmul := hC.mul hSk
  refine hmul.mono ?_ ?_
  · rw [zero_add]; exact Nat.mul_le_mul_right M_S (by omega)
  · have : (N - k) * D' + k * D' = N * D' := by rw [← add_mul, Nat.sub_add_cancel (by omega)]
    omega

-- Build the Galois witness first-order sentence
section SentenceDef

variable (G : Type) [Fintype G] [Group G] [DecidableEq G]
variable (N D D' M_W D_W M_U D_U : ℕ)

abbrev WVar := Empty ⊕ WitnessVar G N D D' M_W D_W M_U D_U

noncomputable def genF : (FreeCommRing (WVar G N D D' M_W D_W M_U D_U))[X][X] :=
  mkMonicPolyTX (fun k j => FreeCommRing.of (Sum.inr (.f k j)))

noncomputable def genQ : (FreeCommRing (WVar G N D D' M_W D_W M_U D_U))[X] :=
  mkPolyT (fun j => FreeCommRing.of (Sum.inr (.Q j)))

noncomputable def genR (g : G) : (FreeCommRing (WVar G N D D' M_W D_W M_U D_U))[X][X] :=
  mkPolyTX (fun k j => FreeCommRing.of (Sum.inr (.R g k j)))

noncomputable def genW (g : G) : (FreeCommRing (WVar G N D D' M_W D_W M_U D_U))[X][X] :=
  mkPolyTX (fun k j => FreeCommRing.of (Sum.inr (.W g k j)))

noncomputable def genU (g h : G) : (FreeCommRing (WVar G N D D' M_W D_W M_U D_U))[X][X] :=
  mkPolyTX (fun k j => FreeCommRing.of (Sum.inr (.U g h k j)))

noncomputable def irredBody (m : Fin (N - 1)) :
    Language.ring.Formula (WVar G N D D' M_W D_W M_U D_U ⊕ FactorVar N D m) :=
  let liftF : (FreeCommRing (WVar G N D D' M_W D_W M_U D_U ⊕ FactorVar N D m))[X][X] :=
    (genF G N D D' M_W D_W M_U D_U).map (Polynomial.mapRingHom (FreeCommRing.map Sum.inl))
  let genG : (FreeCommRing (WVar G N D D' M_W D_W M_U D_U ⊕ FactorVar N D m))[X][X] :=
    mkMonicPolyTX (fun k j => FreeCommRing.of (Sum.inr (Sum.inl (k, j))))
  let genH : (FreeCommRing (WVar G N D D' M_W D_W M_U D_U ⊕ FactorVar N D m))[X][X] :=
    mkMonicPolyTX (fun k j => FreeCommRing.of (Sum.inr (Sum.inr (k, j))))
  ∼ (polyEqFormula N (D + D) liftF (genG * genH))

noncomputable def witnessBody : Language.ring.Formula (WVar G N D D' M_W D_W M_U D_U) :=
  let hQne : Language.ring.Formula (WVar G N D D' M_W D_W M_U D_U) :=
    Formula.iSup (fun j : Fin (D' + 1) =>
      ∼ (Term.equal (termOfFreeCommRing (FreeCommRing.of (Sum.inr (WitnessVar.Q j)))) 0))
  let hIrred : Language.ring.Formula (WVar G N D D' M_W D_W M_U D_U) :=
    Formula.iInf (fun m : Fin (N - 1) =>
      (irredBody G N D D' M_W D_W M_U D_U m).iAlls (FactorVar N D m))
  let hRoot : Language.ring.Formula (WVar G N D D' M_W D_W M_U D_U) :=
    Formula.iInf (fun g : G => polyEqFormula (max (N * N) (N + M_W)) (max (D + N * D') (D + D_W))
      (homSubst N (genF G N D D' M_W D_W M_U D_U) (genQ G N D D' M_W D_W M_U D_U)
        (genR G N D D' M_W D_W M_U D_U g))
      (genF G N D D' M_W D_W M_U D_U * genW G N D D' M_W D_W M_U D_U g))
  let hMul : Language.ring.Formula (WVar G N D D' M_W D_W M_U D_U) :=
    Formula.iInf (fun g : G => Formula.iInf (fun h : G =>
      polyEqFormula (max (N * N) (N + M_U)) (max (D' + N * D') (D + D_U))
        (C ((genQ G N D D' M_W D_W M_U D_U) ^ N) * genR G N D D' M_W D_W M_U D_U (g * h) -
          homSubst N (genR G N D D' M_W D_W M_U D_U h) (genQ G N D D' M_W D_W M_U D_U)
            (genR G N D D' M_W D_W M_U D_U g))
        (genF G N D D' M_W D_W M_U D_U * genU G N D D' M_W D_W M_U D_U g h)))
  let hDist : Language.ring.Formula (WVar G N D D' M_W D_W M_U D_U) :=
    Formula.iInf (fun p : { p : G × G // p.1 ≠ p.2 } =>
      Formula.iSup (fun k : Fin N => Formula.iSup (fun j : Fin (D' + 1) =>
        ∼ (Term.equal (termOfFreeCommRing (FreeCommRing.of (Sum.inr (WitnessVar.R p.1.1 k j))))
                      (termOfFreeCommRing (FreeCommRing.of (Sum.inr (WitnessVar.R p.1.2 k j))))))))
  hQne ⊓ hIrred ⊓ hRoot ⊓ hMul ⊓ hDist

noncomputable def galoisSentence : Language.ring.Sentence :=
  (witnessBody G N D D' M_W D_W M_U D_U).iExs (WitnessVar G N D D' M_W D_W M_U D_U)

end SentenceDef

-- Realization equivalence for galoisSentence over any field K
structure GaloisWitness (G : Type) [Group G] (K : Type*) [Field K] (N D D' M_W D_W M_U D_U : ℕ) where
  f : K[X][X]
  Q : K[X]
  R : G → K[X][X]
  W : G → K[X][X]
  U : G → G → K[X][X]
  hf_monic : f.Monic
  hf_deg : f.natDegree = N
  hf_D : polyDegT f ≤ D
  hQ_ne : Q ≠ 0
  hQ_deg : Q.natDegree ≤ D'
  hR_degX : ∀ g i, N ≤ i → (R g).coeff i = 0
  hR_D : ∀ g, polyDegT (R g) ≤ D'
  hW_degX : ∀ g, (W g).natDegree ≤ M_W
  hW_D : ∀ g, polyDegT (W g) ≤ D_W
  hU_degX : ∀ g h, (U g h).natDegree ≤ M_U
  hU_D : ∀ g h, polyDegT (U g h) ≤ D_U
  hIrred : ∀ g h : K[X][X], g.Monic → h.Monic → 1 ≤ g.natDegree → g.natDegree < N →
    polyDegT g ≤ D → polyDegT h ≤ D → f ≠ g * h
  hRoot : ∀ g, homSubst N f Q (R g) = f * W g
  hMul : ∀ g h, C (Q ^ N) * R (g * h) - homSubst N (R h) Q (R g) = f * U g h
  hDist : ∀ g h, g ≠ h → R g ≠ R h

lemma realize_galoisSentence_iff {G : Type} [Fintype G] [Group G] [DecidableEq G]
    {K : Type*} [Field K] [CompatibleRing K]
    {N D D' M_W D_W M_U D_U : ℕ} (hN : 1 ≤ N) :
    K ⊨ galoisSentence G N D D' M_W D_W M_U D_U ↔
      Nonempty (GaloisWitness G K N D D' M_W D_W M_U D_U) := by
  have hbd_f : BoundedDeg N D (genF G N D D' M_W D_W M_U D_U) := boundedDeg_mkMonicPolyTX _
  have hbd_Q : ∀ j > D', (genQ G N D D' M_W D_W M_U D_U).coeff j = 0 := fun j hj => by
    rw [genQ, coeff_mkPolyT, dif_neg (by omega)]
  have hbd_R : ∀ g, BoundedDeg N D' (genR G N D D' M_W D_W M_U D_U g) := fun g =>
    boundedDeg_mkPolyTX _
  have hbd_W : ∀ g, BoundedDeg M_W D_W (genW G N D D' M_W D_W M_U D_U g) := fun g =>
    boundedDeg_mkPolyTX_pred _
  have hbd_U : ∀ g h, BoundedDeg M_U D_U (genU G N D D' M_W D_W M_U D_U g h) := fun g h =>
    boundedDeg_mkPolyTX_pred _
  have hbd_rootL : ∀ g, BoundedDeg (max (N * N) (N + M_W)) (max (D + N * D') (D + D_W))
      (homSubst N (genF G N D D' M_W D_W M_U D_U) (genQ G N D D' M_W D_W M_U D_U)
        (genR G N D D' M_W D_W M_U D_U g)) := fun g =>
    (boundedDeg_homSubst hbd_f hbd_Q (hbd_R g)).mono (le_max_left _ _) (le_max_left _ _)
  have hbd_rootR : ∀ g, BoundedDeg (max (N * N) (N + M_W)) (max (D + N * D') (D + D_W))
      (genF G N D D' M_W D_W M_U D_U * genW G N D D' M_W D_W M_U D_U g) := fun g =>
    (hbd_f.mul (hbd_W g)).mono (le_max_right _ _) (le_max_right _ _)
  have hbd_mulL : ∀ g h, BoundedDeg (max (N * N) (N + M_U)) (max (D' + N * D') (D + D_U))
      (C ((genQ G N D D' M_W D_W M_U D_U) ^ N) * genR G N D D' M_W D_W M_U D_U (g * h) -
        homSubst N (genR G N D D' M_W D_W M_U D_U h) (genQ G N D D' M_W D_W M_U D_U)
          (genR G N D D' M_W D_W M_U D_U g)) := fun g h => by
    have h1 : BoundedDeg (0 + N) (N * D' + D')
        (C ((genQ G N D D' M_W D_W M_U D_U) ^ N) * genR G N D D' M_W D_W M_U D_U (g * h)) := by
      have hQp : BoundedDeg 0 (N * D') (C ((genQ G N D D' M_W D_W M_U D_U) ^ N)) := by
        simpa [map_pow] using (BoundedDeg.C_poly hbd_Q).pow N
      exact hQp.mul (hbd_R (g * h))
    have h1' : BoundedDeg (N * N) (D' + N * D')
        (C ((genQ G N D D' M_W D_W M_U D_U) ^ N) * genR G N D D' M_W D_W M_U D_U (g * h)) :=
      h1.mono (by rw [zero_add]; exact Nat.le_mul_of_pos_left N (by omega)) (by omega)
    have h2 : BoundedDeg (N * N) (D' + N * D')
        (homSubst N (genR G N D D' M_W D_W M_U D_U h) (genQ G N D D' M_W D_W M_U D_U)
          (genR G N D D' M_W D_W M_U D_U g)) :=
      boundedDeg_homSubst (hbd_R h) hbd_Q (hbd_R g)
    exact (h1'.sub h2).mono (le_max_left _ _) (le_max_left _ _)
  have hbd_mulR : ∀ g h, BoundedDeg (max (N * N) (N + M_U)) (max (D' + N * D') (D + D_U))
      (genF G N D D' M_W D_W M_U D_U * genU G N D D' M_W D_W M_U D_U g h) := fun g h =>
    (hbd_f.mul (hbd_U g h)).mono (le_max_right _ _) (le_max_right _ _)
  have hreal_irred : ∀ (v : WVar G N D D' M_W D_W M_U D_U → K) (m : Fin (N - 1)),
      ((irredBody G N D D' M_W D_W M_U D_U m).iAlls (FactorVar N D m)).Realize v ↔
      ∀ (g h : K[X][X]), g.Monic → h.Monic → g.natDegree = m.1 + 1 →
        h.natDegree = N - (m.1 + 1) → polyDegT g ≤ D → polyDegT h ≤ D →
        evalHom v (genF G N D D' M_W D_W M_U D_U) ≠ g * h := by
    intro v m
    rw [Formula.realize_iAlls]
    let inlMap : FreeCommRing (WVar G N D D' M_W D_W M_U D_U) →+*
        FreeCommRing (WVar G N D D' M_W D_W M_U D_U ⊕ FactorVar N D m) :=
      FreeCommRing.map Sum.inl
    have hbd_lift : BoundedDeg N (D + D)
        ((genF G N D D' M_W D_W M_U D_U).map (Polynomial.mapRingHom inlMap)) :=
      (hbd_f.map inlMap).mono le_rfl (Nat.le_add_right D D)
    have hbd_prod : BoundedDeg N (D + D)
        (mkMonicPolyTX (fun (k : Fin (m.1 + 1)) (j : Fin (D + 1)) =>
            FreeCommRing.of (Sum.inr (Sum.inl (k, j)) :
              WVar G N D D' M_W D_W M_U D_U ⊕ FactorVar N D m)) *
          mkMonicPolyTX (fun (k : Fin (N - (m.1 + 1))) (j : Fin (D + 1)) =>
            FreeCommRing.of (Sum.inr (Sum.inr (k, j))))) := by
      have hm_le : m.1 + 1 + (N - (m.1 + 1)) = N := by omega
      have h1 := (boundedDeg_mkMonicPolyTX (R := FreeCommRing (WVar G N D D' M_W D_W M_U D_U ⊕ FactorVar N D m))
        (fun (k : Fin (m.1 + 1)) (j : Fin (D + 1)) => FreeCommRing.of (Sum.inr (Sum.inl (k, j))))).mul
        (boundedDeg_mkMonicPolyTX (fun (k : Fin (N - (m.1 + 1))) (j : Fin (D + 1)) =>
          FreeCommRing.of (Sum.inr (Sum.inr (k, j)))))
      rwa [hm_le] at h1
    have hstep : ∀ w : FactorVar N D m → K,
        (irredBody G N D D' M_W D_W M_U D_U m).Realize (Sum.elim v w) ↔
        evalHom v (genF G N D D' M_W D_W M_U D_U) ≠
          mkMonicPolyTX (fun k j => w (Sum.inl (k, j))) *
          mkMonicPolyTX (fun k j => w (Sum.inr (k, j))) := by
      intro w
      rw [irredBody, Formula.realize_not, realize_polyEqFormula hbd_lift hbd_prod]
      have hlhs : evalHom (Sum.elim v w)
          ((genF G N D D' M_W D_W M_U D_U).map (Polynomial.mapRingHom inlMap)) =
          evalHom v (genF G N D D' M_W D_W M_U D_U) := by
        simp [evalHom, genF, inlMap, map_mkMonicPolyTX]
      have hrhs : evalHom (Sum.elim v w)
          (mkMonicPolyTX (fun (k : Fin (m.1 + 1)) (j : Fin (D + 1)) =>
              FreeCommRing.of (Sum.inr (Sum.inl (k, j)) :
                WVar G N D D' M_W D_W M_U D_U ⊕ FactorVar N D m)) *
            mkMonicPolyTX (fun (k : Fin (N - (m.1 + 1))) (j : Fin (D + 1)) =>
              FreeCommRing.of (Sum.inr (Sum.inr (k, j))))) =
          mkMonicPolyTX (fun k j => w (Sum.inl (k, j))) *
          mkMonicPolyTX (fun k j => w (Sum.inr (k, j))) := by
        simp [evalHom, map_mkMonicPolyTX]
      rw [hlhs, hrhs]
    simp_rw [hstep]
    constructor
    · intro h g h' hg hh' hgdeg hhdeg hgD hhD
      let w : FactorVar N D m → K := fun
        | Sum.inl (k, j) => (g.coeff k.1).coeff j.1
        | Sum.inr (k, j) => (h'.coeff k.1).coeff j.1
      have hw := h w
      rw [mkMonicPolyTX_of_monic hg hgdeg hgD, mkMonicPolyTX_of_monic hh' hhdeg hhD] at hw
      exact hw
    · intro h w
      exact h _ _ (monic_mkMonicPolyTX _) (monic_mkMonicPolyTX _)
        (natDegree_mkMonicPolyTX _) (natDegree_mkMonicPolyTX _)
        (polyDegT_mkMonicPolyTX_le _) (polyDegT_mkMonicPolyTX_le _)
  -- Main iff
  rw [Sentence.Realize, galoisSentence, Formula.realize_iExs]
  have hbody : ∀ w : WitnessVar G N D D' M_W D_W M_U D_U → K,
      let v : WVar G N D D' M_W D_W M_U D_U → K := Sum.elim default w
      (witnessBody G N D D' M_W D_W M_U D_U).Realize v ↔
        ((∃ j : Fin (D' + 1), w (.Q j) ≠ 0) ∧
         (∀ m : Fin (N - 1),
           ((irredBody G N D D' M_W D_W M_U D_U m).iAlls (FactorVar N D m)).Realize v) ∧
         (∀ g : G, evalHom v (homSubst N (genF G N D D' M_W D_W M_U D_U)
             (genQ G N D D' M_W D_W M_U D_U) (genR G N D D' M_W D_W M_U D_U g)) =
           evalHom v (genF G N D D' M_W D_W M_U D_U * genW G N D D' M_W D_W M_U D_U g)) ∧
         (∀ g h : G, evalHom v (C ((genQ G N D D' M_W D_W M_U D_U) ^ N) *
             genR G N D D' M_W D_W M_U D_U (g * h) -
             homSubst N (genR G N D D' M_W D_W M_U D_U h) (genQ G N D D' M_W D_W M_U D_U)
               (genR G N D D' M_W D_W M_U D_U g)) =
           evalHom v (genF G N D D' M_W D_W M_U D_U * genU G N D D' M_W D_W M_U D_U g h)) ∧
         (∀ p : { p : G × G // p.1 ≠ p.2 }, ∃ (k : Fin N) (j : Fin (D' + 1)),
           w (.R p.1.1 k j) ≠ w (.R p.1.2 k j))) := by
    intro w
    dsimp only [witnessBody]
    simp only [Formula.realize_inf, Formula.realize_iInf, Formula.realize_iSup, Formula.realize_not]
    have hQ' : ∀ j : Fin (D' + 1),
        (Term.equal (termOfFreeCommRing (FreeCommRing.of (Sum.inr (WitnessVar.Q j) :
          WVar G N D D' M_W D_W M_U D_U))) 0).Realize (Sum.elim default w) ↔ w (.Q j) = 0 := by
      intro j
      simp [Term.equal, Formula.Realize, BoundedFormula.realize_bdEqual]
    have hD' : ∀ (p : { p : G × G // p.1 ≠ p.2 }) (k : Fin N) (j : Fin (D' + 1)),
        (Term.equal
          (termOfFreeCommRing (FreeCommRing.of (Sum.inr (WitnessVar.R p.1.1 k j) :
            WVar G N D D' M_W D_W M_U D_U)))
          (termOfFreeCommRing (FreeCommRing.of (Sum.inr (WitnessVar.R p.1.2 k j) :
            WVar G N D D' M_W D_W M_U D_U)))).Realize (Sum.elim default w) ↔
          w (.R p.1.1 k j) = w (.R p.1.2 k j) := by
      intro p k j
      simp [Term.equal, Formula.Realize, BoundedFormula.realize_bdEqual]
    have hR' : ∀ g, (polyEqFormula (max (N * N) (N + M_W)) (max (D + N * D') (D + D_W))
      (homSubst N (genF G N D D' M_W D_W M_U D_U) (genQ G N D D' M_W D_W M_U D_U)
        (genR G N D D' M_W D_W M_U D_U g))
      (genF G N D D' M_W D_W M_U D_U * genW G N D D' M_W D_W M_U D_U g)).Realize (Sum.elim default w) ↔ _ :=
      fun g => realize_polyEqFormula (hbd_rootL g) (hbd_rootR g) _
    have hM' : ∀ g h, (polyEqFormula (max (N * N) (N + M_U)) (max (D' + N * D') (D + D_U))
      (C ((genQ G N D D' M_W D_W M_U D_U) ^ N) * genR G N D D' M_W D_W M_U D_U (g * h) -
        homSubst N (genR G N D D' M_W D_W M_U D_U h) (genQ G N D D' M_W D_W M_U D_U)
          (genR G N D D' M_W D_W M_U D_U g))
      (genF G N D D' M_W D_W M_U D_U * genU G N D D' M_W D_W M_U D_U g h)).Realize (Sum.elim default w) ↔ _ :=
      fun g h => realize_polyEqFormula (hbd_mulL g h) (hbd_mulR g h) _
    simp only [hQ', hD', hR', hM', and_assoc]
  constructor
  · rintro ⟨w, hw⟩
    have ⟨hQ, hIr, hRt, hMl, hDs⟩ := (hbody w).1 hw
    let v : WVar G N D D' M_W D_W M_U D_U → K := Sum.elim default w
    have hfev : evalHom v (genF G N D D' M_W D_W M_U D_U) =
        mkMonicPolyTX (fun k j => w (.f k j)) := by
      rw [evalHom, coe_mapRingHom, genF, map_mkMonicPolyTX]; simp [v]
    have hQev : (genQ G N D D' M_W D_W M_U D_U).map (FreeCommRing.lift v) =
        mkPolyT (fun j => w (.Q j)) := by
      rw [genQ, map_mkPolyT]; simp [v]
    have hRev : ∀ g, evalHom v (genR G N D D' M_W D_W M_U D_U g) =
        mkPolyTX (fun k j => w (.R g k j)) := fun g => by
      rw [evalHom, coe_mapRingHom, genR, map_mkPolyTX]; simp [v]
    have hWev : ∀ g, evalHom v (genW G N D D' M_W D_W M_U D_U g) =
        mkPolyTX (fun k j => w (.W g k j)) := fun g => by
      rw [evalHom, coe_mapRingHom, genW, map_mkPolyTX]; simp [v]
    have hUev : ∀ g h, evalHom v (genU G N D D' M_W D_W M_U D_U g h) =
        mkPolyTX (fun k j => w (.U g h k j)) := fun g h => by
      rw [evalHom, coe_mapRingHom, genU, map_mkPolyTX]; simp [v]
    refine ⟨{
      f := mkMonicPolyTX (fun k j => w (.f k j))
      Q := mkPolyT (fun j => w (.Q j))
      R := fun g => mkPolyTX (fun k j => w (.R g k j))
      W := fun g => mkPolyTX (fun k j => w (.W g k j))
      U := fun g h => mkPolyTX (fun k j => w (.U g h k j))
      hf_monic := monic_mkMonicPolyTX _
      hf_deg := natDegree_mkMonicPolyTX _
      hf_D := polyDegT_mkMonicPolyTX_le _
      hQ_ne := by
        obtain ⟨j, hj⟩ := hQ
        intro hz
        have := congr_arg (fun p : K[X] => p.coeff j.1) hz
        rw [coeff_mkPolyT, dif_pos j.2, coeff_zero] at this
        exact hj this
      hQ_deg := natDegree_le_iff_coeff_eq_zero.2 (fun j hj => by
        rw [coeff_mkPolyT, dif_neg (by omega)])
      hR_degX := fun g i hi => by rw [coeff_mkPolyTX, dif_neg (by omega)]
      hR_D := fun g => polyDegT_le_iff.2 (fun i =>
        natDegree_le_iff_coeff_eq_zero.2 (fun j hj => (boundedDeg_mkPolyTX _).2 i j hj))
      hW_degX := fun g => natDegree_le_iff_coeff_eq_zero.2 (fun i hi =>
        (boundedDeg_mkPolyTX_pred _).1 i hi)
      hW_D := fun g => polyDegT_le_iff.2 (fun i =>
        natDegree_le_iff_coeff_eq_zero.2 (fun j hj => (boundedDeg_mkPolyTX_pred _).2 i j hj))
      hU_degX := fun g h => natDegree_le_iff_coeff_eq_zero.2 (fun i hi =>
        (boundedDeg_mkPolyTX_pred _).1 i hi)
      hU_D := fun g h => polyDegT_le_iff.2 (fun i =>
        natDegree_le_iff_coeff_eq_zero.2 (fun j hj => (boundedDeg_mkPolyTX_pred _).2 i j hj))
      hIrred := fun g h hg hh hg1 hglt hgD hhD hmul => by
        have hsum : g.natDegree + h.natDegree = N := by
          rw [← natDegree_mul hg.ne_zero hh.ne_zero, ← hmul, natDegree_mkMonicPolyTX]
        let m : Fin (N - 1) := ⟨g.natDegree - 1, by omega⟩
        have h1 := (hreal_irred v m).1 (hIr m) g h hg hh (by simp [m]; omega) (by simp [m]; omega) hgD hhD
        rw [hfev] at h1
        exact h1 hmul
      hRoot := fun g => by
        have h1 := hRt g
        have hL : evalHom v (homSubst N (genF G N D D' M_W D_W M_U D_U)
            (genQ G N D D' M_W D_W M_U D_U) (genR G N D D' M_W D_W M_U D_U g)) =
            homSubst N (evalHom v (genF G N D D' M_W D_W M_U D_U))
              ((genQ G N D D' M_W D_W M_U D_U).map (FreeCommRing.lift v))
              (evalHom v (genR G N D D' M_W D_W M_U D_U g)) :=
          map_homSubst (FreeCommRing.lift v) N _ _ _
        rw [hL, map_mul, hfev, hQev, hRev, hWev] at h1
        exact h1
      hMul := fun g h => by
        have h1 := hMl g h
        have hL1 : evalHom v (C ((genQ G N D D' M_W D_W M_U D_U) ^ N)) =
            C (((genQ G N D D' M_W D_W M_U D_U).map (FreeCommRing.lift v)) ^ N) := by
          simp [evalHom]
        have hL2 : evalHom v (homSubst N (genR G N D D' M_W D_W M_U D_U h)
            (genQ G N D D' M_W D_W M_U D_U) (genR G N D D' M_W D_W M_U D_U g)) =
            homSubst N (evalHom v (genR G N D D' M_W D_W M_U D_U h))
              ((genQ G N D D' M_W D_W M_U D_U).map (FreeCommRing.lift v))
              (evalHom v (genR G N D D' M_W D_W M_U D_U g)) :=
          map_homSubst (FreeCommRing.lift v) N _ _ _
        rw [map_sub, map_mul, hL1, hL2, map_mul, hfev, hQev, hRev, hRev, hRev, hUev] at h1
        exact h1
      hDist := fun g h hgh heq => by
        obtain ⟨k, j, hne⟩ := hDs ⟨(g, h), hgh⟩
        have := congr_arg (fun p : K[X][X] => (p.coeff k.1).coeff j.1) heq
        simp only [coeff_mkPolyTX, dif_pos k.2, coeff_mkPolyT, dif_pos j.2] at this
        exact hne this
    }⟩
  · rintro ⟨wit⟩
    let w : WitnessVar G N D D' M_W D_W M_U D_U → K
      | .f k j => (wit.f.coeff k.1).coeff j.1
      | .Q j => wit.Q.coeff j.1
      | .R g k j => ((wit.R g).coeff k.1).coeff j.1
      | .W g k j => ((wit.W g).coeff k.1).coeff j.1
      | .U g h k j => ((wit.U g h).coeff k.1).coeff j.1
    let v : WVar G N D D' M_W D_W M_U D_U → K := Sum.elim default w
    have hfev : evalHom v (genF G N D D' M_W D_W M_U D_U) = wit.f := by
      have h1 : evalHom v (genF G N D D' M_W D_W M_U D_U) =
          mkMonicPolyTX (fun (k : Fin N) (j : Fin (D + 1)) => (wit.f.coeff k.1).coeff j.1) := by
        rw [evalHom, coe_mapRingHom, genF, map_mkMonicPolyTX]
        congr 1; funext k j; simp [v, w]
      rw [h1]
      exact mkMonicPolyTX_of_monic wit.hf_monic wit.hf_deg wit.hf_D
    have hQev : (genQ G N D D' M_W D_W M_U D_U).map (FreeCommRing.lift v) = wit.Q := by
      have h1 : (genQ G N D D' M_W D_W M_U D_U).map (FreeCommRing.lift v) =
          mkPolyT (fun (j : Fin (D' + 1)) => wit.Q.coeff j.1) := by
        rw [genQ, map_mkPolyT]
        congr 1; funext j; simp [v, w]
      rw [h1]
      exact mkPolyT_of_natDegree_le wit.hQ_deg
    have hRev : ∀ g, evalHom v (genR G N D D' M_W D_W M_U D_U g) = wit.R g := fun g => by
      have h1 : evalHom v (genR G N D D' M_W D_W M_U D_U g) =
          mkPolyTX (fun (k : Fin N) (j : Fin (D' + 1)) => ((wit.R g).coeff k.1).coeff j.1) := by
        rw [evalHom, coe_mapRingHom, genR, map_mkPolyTX]
        congr 1; funext k j; simp [v, w]
      rw [h1]
      exact mkPolyTX_of_bounded (wit.hR_degX g) (wit.hR_D g)
    have hWev : ∀ g, evalHom v (genW G N D D' M_W D_W M_U D_U g) = wit.W g := fun g => by
      have h1 : evalHom v (genW G N D D' M_W D_W M_U D_U g) =
          mkPolyTX (fun (k : Fin (M_W + 1)) (j : Fin (D_W + 1)) => ((wit.W g).coeff k.1).coeff j.1) := by
        rw [evalHom, coe_mapRingHom, genW, map_mkPolyTX]
        congr 1; funext k j; simp [v, w]
      rw [h1]
      exact mkPolyTX_of_bounded (fun i hi => coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (wit.hW_degX g) hi)) (wit.hW_D g)
    have hUev : ∀ g h, evalHom v (genU G N D D' M_W D_W M_U D_U g h) = wit.U g h := fun g h => by
      have h1 : evalHom v (genU G N D D' M_W D_W M_U D_U g h) =
          mkPolyTX (fun (k : Fin (M_U + 1)) (j : Fin (D_U + 1)) => ((wit.U g h).coeff k.1).coeff j.1) := by
        rw [evalHom, coe_mapRingHom, genU, map_mkPolyTX]
        congr 1; funext k j; simp [v, w]
      rw [h1]
      exact mkPolyTX_of_bounded (fun i hi => coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (wit.hU_degX g h) hi)) (wit.hU_D g h)
    refine ⟨w, (hbody w).2 ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · by_contra hzero
      push Not at hzero
      apply wit.hQ_ne
      ext j
      by_cases hj : j < D' + 1
      · exact hzero ⟨j, hj⟩
      · have hQd := wit.hQ_deg; exact coeff_eq_zero_of_natDegree_lt (by omega)
    · intro m
      rw [hreal_irred v m, hfev]
      intro g h hg hh hgdeg _ hgD hhD
      exact wit.hIrred g h hg hh (by omega) (by omega) hgD hhD
    · intro g
      have hL : evalHom v (homSubst N (genF G N D D' M_W D_W M_U D_U)
          (genQ G N D D' M_W D_W M_U D_U) (genR G N D D' M_W D_W M_U D_U g)) =
          homSubst N (evalHom v (genF G N D D' M_W D_W M_U D_U))
            ((genQ G N D D' M_W D_W M_U D_U).map (FreeCommRing.lift v))
            (evalHom v (genR G N D D' M_W D_W M_U D_U g)) :=
        map_homSubst (FreeCommRing.lift v) N _ _ _
      rw [hL, map_mul, hfev, hQev, hRev, hWev]
      exact wit.hRoot g
    · intro g h
      have hL1 : evalHom v (C ((genQ G N D D' M_W D_W M_U D_U) ^ N)) =
          C (((genQ G N D D' M_W D_W M_U D_U).map (FreeCommRing.lift v)) ^ N) := by
        simp [evalHom]
      have hL2 : evalHom v (homSubst N (genR G N D D' M_W D_W M_U D_U h)
          (genQ G N D D' M_W D_W M_U D_U) (genR G N D D' M_W D_W M_U D_U g)) =
          homSubst N (evalHom v (genR G N D D' M_W D_W M_U D_U h))
            ((genQ G N D D' M_W D_W M_U D_U).map (FreeCommRing.lift v))
            (evalHom v (genR G N D D' M_W D_W M_U D_U g)) :=
        map_homSubst (FreeCommRing.lift v) N _ _ _
      rw [map_sub, map_mul, hL1, hL2, map_mul, hfev, hQev, hRev, hRev, hRev, hUev]
      exact wit.hMul g h
    · rintro ⟨⟨g, h⟩, hgh⟩
      by_contra hall
      push Not at hall
      apply wit.hDist g h hgh
      ext k j
      by_cases hk : k < N
      · by_cases hj : j < D' + 1
        · exact hall ⟨k, hk⟩ ⟨j, hj⟩
        · rw [coeff_eq_zero_of_natDegree_lt
                (lt_of_le_of_lt ((natDegree_coeff_le_polyDegT _ k).trans (wit.hR_D g)) (by omega)),
              coeff_eq_zero_of_natDegree_lt
                (lt_of_le_of_lt ((natDegree_coeff_le_polyDegT _ k).trans (wit.hR_D h)) (by omega))]
      · rw [wit.hR_degX g k (by omega), wit.hR_degX h k (by omega)]

-- Evaluate homSubst in any field extension
lemma aeval_homSubst {K L : Type*} [Field K] [Field L] [Algebra (RatFunc K) L]
    (N : ℕ) (P : K[X][X]) (Q : K[X]) (S : K[X][X]) (α : L)
    (hPdeg : ∀ i > N, P.coeff i = 0) (hQ : algebraMap K[X] (RatFunc K) Q ≠ 0) :
    let φ := algebraMap K[X] (RatFunc K)
    let q : L := algebraMap (RatFunc K) L (φ Q)
    let s : L := aeval α (S.map φ)
    aeval α ((homSubst N P Q S).map φ) = q ^ N * aeval (s / q) (P.map φ) := by
  intro φ q s
  have hq : q ≠ 0 := by
    simp only [q]
    intro hz
    exact hQ ((RingHom.injective (algebraMap (RatFunc K) L)) (hz.trans (map_zero _).symm))
  rw [homSubst, Polynomial.map_sum, map_sum]
  have hPsum : P.map φ = ∑ k ∈ Finset.range (N + 1), C (φ (P.coeff k)) * X ^ k := by
    ext k
    simp only [coeff_map, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hk
    · rfl
    · rw [hPdeg k (by omega), map_zero]
  conv_rhs => rw [hPsum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  simp only [Polynomial.map_mul, map_C, Polynomial.map_pow, map_mul, aeval_C, map_pow, aeval_X,
    div_pow]
  have hsub : N - k + k = N := Nat.sub_add_cancel (by omega)
  have hqk : q ^ k ≠ 0 := pow_ne_zero k hq
  calc (algebraMap (RatFunc K) L) (φ (P.coeff k)) * q ^ (N - k) * s ^ k
      = (algebraMap (RatFunc K) L) (φ (P.coeff k)) * (q ^ (N - k) * q ^ k) * (s ^ k / q ^ k) := by
          field_simp
    _ = q ^ N * ((algebraMap (RatFunc K) L) (φ (P.coeff k)) * (s ^ k / q ^ k)) := by
          rw [← pow_add, hsub]; ring

-- Extract GaloisWitness from a finite Galois extension L / RatFunc K with iso : G ≃* Gal(L / RatFunc K)
set_option maxHeartbeats 600000 in
lemma exists_galoisWitness_of_realization {G : Type} [Fintype G] [Group G] [DecidableEq G]
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra (RatFunc K) L]
    [IsGalois (RatFunc K) L] [FiniteDimensional (RatFunc K) L]
    (_hG : 1 ≤ Fintype.card G) (iso : G ≃* (L ≃ₐ[RatFunc K] L)) :
    ∃ (D D' M_W D_W M_U D_U : ℕ),
      Nonempty (GaloisWitness G K (Fintype.card G) D D' M_W D_W M_U D_U) := by
  set F := RatFunc K
  set N := Fintype.card G
  set φ := algebraMap K[X] F
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] F
  have hfinrank : Module.finrank F L = N := by
    have hcard := IsGalois.card_aut_eq_finrank F L
    rw [← hcard]
    have heq := Nat.card_congr iso.toEquiv
    rw [Nat.card_eq_fintype_card] at heq
    exact heq.symm
  -- Primitive element θ of L / F
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F L
  have hmin_int : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  -- Scale θ by a common denominator d ∈ K[X] \ {0} so minpoly F θ' lifts to monic f ∈ K[X][X]
  let m := minpoly F θ
  have hm_monic : m.Monic := minpoly.monic hmin_int
  have hm_deg : m.natDegree = N := by
    let hpb := IntermediateField.adjoin.powerBasis hmin_int
    have htop : Module.finrank F (F⟮θ⟯) = N := by
      rw [hθ]; exact (IntermediateField.topEquiv.toLinearEquiv.finrank_eq).trans hfinrank
    have h1 : Module.finrank F (F⟮θ⟯) = m.natDegree := by
      rw [hpb.finrank]; exact IntermediateField.adjoin.powerBasis_dim hmin_int
    omega
  -- For each k < N, write m.coeff k = φ (a k) / φ (b k) with b k ≠ 0 using RatFunc.num / RatFunc.denom
  let a : Fin N → K[X] := fun k => (m.coeff k.1).num
  let b : Fin N → K[X] := fun k => (m.coeff k.1).denom
  have hb_ne : ∀ k : Fin N, b k ≠ 0 := fun k => RatFunc.denom_ne_zero _
  have hmb : ∀ k : Fin N, m.coeff k.1 = φ (a k) / φ (b k) := fun k =>
    (RatFunc.num_div_denom _).symm
  let d : K[X] := ∏ k : Fin N, b k
  have hd_ne : d ≠ 0 := Finset.prod_ne_zero_iff.2 (fun k _ => hb_ne k)
  have hφd_ne : φ d ≠ 0 := by simpa [map_zero] using hinj.ne hd_ne
  let θ' : L := (algebraMap F L (φ d)) * θ
  -- Construct monic f ∈ K[X][X] of degree N annihilating θ'
  let d_div : Fin N → K[X] := fun k => ∏ j ∈ Finset.univ.erase k, b j
  have hd_eq : ∀ k : Fin N, b k * d_div k = d := fun k =>
    Finset.mul_prod_erase Finset.univ b (Finset.mem_univ k)
  let f : K[X][X] := X ^ N + ∑ k : Fin N, C (a k * d_div k * d ^ (N - 1 - k.1)) * X ^ k.1
  have hf_monic : f.Monic := by
    refine (monic_X_pow N).add_of_left ?_
    rw [degree_X_pow]
    refine (degree_lt_iff_coeff_zero _ _).2 (fun i hi => ?_)
    simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    apply Finset.sum_eq_zero; intro k _; rw [if_neg]; omega
  have hf_deg : f.natDegree = N := by
    apply le_antisymm
    · refine natDegree_le_iff_coeff_eq_zero.2 (fun i hi => ?_)
      simp only [f, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul, mul_ite, mul_one,
        mul_zero, if_neg (by omega : i ≠ N), zero_add]
      apply Finset.sum_eq_zero; intro k _; rw [if_neg]; omega
    · refine le_natDegree_of_ne_zero ?_
      simp only [f, coeff_add, coeff_X_pow_self, finsetSum_coeff, coeff_C_mul, coeff_X_pow,
        mul_ite, mul_one, mul_zero]
      have h0 : ∑ k : Fin N, (if N = k.1 then a k * d_div k * d ^ (N - 1 - k.1) else 0) = 0 :=
        Finset.sum_eq_zero (fun k _ => if_neg (by omega))
      rw [h0, add_zero]; exact one_ne_zero
  have hf_root : aeval θ' (f.map φ) = 0 := by
    have hm_sum : m = X ^ N + ∑ k : Fin N, C (m.coeff k.1) * X ^ k.1 := by
      ext i
      simp only [coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul, mul_ite, mul_one, mul_zero]
      by_cases hi : i < N
      · rw [if_neg (by omega), zero_add, Finset.sum_eq_single ⟨i, hi⟩]
        · simp
        · intro k _ hk; rw [if_neg]; intro heq; exact hk (Fin.ext heq.symm)
        · intro habs; exact absurd (Finset.mem_univ _) habs
      · by_cases heq : i = N
        · subst heq
          rw [if_pos rfl, Finset.sum_eq_zero (fun k _ => if_neg (by omega)), add_zero]
          rw [← hm_deg]; exact hm_monic.leadingCoeff
        · rw [if_neg heq, Finset.sum_eq_zero (fun k _ => if_neg (by omega)), add_zero]
          exact coeff_eq_zero_of_natDegree_lt (by omega)
    have hzero : aeval θ m = 0 := minpoly.aeval F θ
    have hmul0 : (algebraMap F L (φ d)) ^ N * aeval θ m = 0 := by rw [hzero, mul_zero]
    rw [← hmul0]
    conv_rhs => rw [hm_sum]
    simp only [f, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
      Polynomial.map_mul, map_C, map_add, map_pow, map_sum, map_mul, aeval_X, aeval_C,
      mul_add, Finset.mul_sum, θ', mul_pow]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hbk_ne : φ (b k) ≠ 0 := by simpa [map_zero] using hinj.ne (hb_ne k)
    have hcoef : φ (a k) * φ (d_div k) * φ d ^ (N - 1 - k.1) = m.coeff k.1 * (φ d) ^ (N - k.1) := by
      rw [hmb k, div_mul_eq_mul_div, eq_div_iff hbk_ne]
      have h1 : N - k.1 = 1 + (N - 1 - k.1) := by omega
      rw [h1, pow_add, pow_one]
      have hdeq : φ (b k) * φ (d_div k) = φ d := by rw [← map_mul, hd_eq k]
      calc φ (a k) * φ (d_div k) * φ d ^ (N - 1 - k.1) * φ (b k)
          = φ (a k) * (φ (b k) * φ (d_div k)) * φ d ^ (N - 1 - k.1) := by ring
        _ = φ (a k) * φ d * φ d ^ (N - 1 - k.1) := by rw [hdeq]
        _ = φ (a k) * (φ d * φ d ^ (N - 1 - k.1)) := by ring
    have hcoefL : algebraMap F L (φ (a k)) * algebraMap F L (φ (d_div k)) *
        algebraMap F L (φ d) ^ (N - 1 - k.1) =
        algebraMap F L (m.coeff k.1) * algebraMap F L (φ d) ^ (N - k.1) := by
      simpa only [map_mul, map_pow] using congr_arg (algebraMap F L) hcoef
    rw [hcoefL]
    have hsub : N - k.1 + k.1 = N := by omega
    calc algebraMap F L (m.coeff k.1) * algebraMap F L (φ d) ^ (N - k.1) *
            (algebraMap F L (φ d) ^ k.1 * θ ^ k.1)
        = algebraMap F L (m.coeff k.1) * (algebraMap F L (φ d) ^ (N - k.1) *
            algebraMap F L (φ d) ^ k.1) * θ ^ k.1 := by ring
      _ = algebraMap F L (φ d) ^ N * (algebraMap F L (m.coeff k.1) * θ ^ k.1) := by
            rw [← pow_add, hsub]; ring
  -- θ' is also a primitive element of L / F
  have hθ'_prim : F⟮θ'⟯ = ⊤ := by
    rw [eq_top_iff, ← hθ]
    rw [IntermediateField.adjoin_simple_le_iff]
    have hmem : θ' ∈ F⟮θ'⟯ := IntermediateField.mem_adjoin_simple_self F θ'
    have hinv : (φ d)⁻¹ • θ' ∈ F⟮θ'⟯ := Subalgebra.smul_mem _ hmem (φ d)⁻¹
    have heq : (φ d)⁻¹ • θ' = θ := by
      simp only [θ', Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hφd_ne, map_one,
        one_mul]
    rwa [heq] at hinv
  have hθ'_int : IsIntegral F θ' := Algebra.IsIntegral.isIntegral θ'
  have hmin_eq : minpoly F θ' = f.map φ := by
    have hdvd : minpoly F θ' ∣ f.map φ := minpoly.dvd F θ' hf_root
    have hdeg1 : (minpoly F θ').natDegree = N := by
      let hpb := IntermediateField.adjoin.powerBasis hθ'_int
      have htop : Module.finrank F (F⟮θ'⟯) = N := by
        rw [hθ'_prim]; exact (IntermediateField.topEquiv.toLinearEquiv.finrank_eq).trans hfinrank
      have h1 : Module.finrank F (F⟮θ'⟯) = (minpoly F θ').natDegree := by
        rw [hpb.finrank]; exact IntermediateField.adjoin.powerBasis_dim hθ'_int
      omega
    have hdeg2 : (f.map φ).natDegree = N := (natDegree_map_eq_of_injective hinj f).trans hf_deg
    obtain ⟨q, hq⟩ := hdvd
    have hq_ne : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact (hf_monic.map φ).ne_zero hq
    have hq_deg : q.natDegree = 0 := by
      have hsum := natDegree_mul (minpoly.monic hθ'_int).ne_zero hq_ne
      rw [← hq, hdeg1, hdeg2] at hsum; omega
    have hq_monic : q.Monic := by
      rw [Polynomial.Monic]
      have hlc : (minpoly F θ').leadingCoeff * q.leadingCoeff = 1 := by
        rw [← leadingCoeff_mul, ← hq]; exact (hf_monic.map φ).leadingCoeff
      rw [(minpoly.monic hθ'_int).leadingCoeff, one_mul] at hlc
      exact hlc
    have hq1 : q = 1 := by
      rw [eq_C_of_natDegree_eq_zero hq_deg]
      have : q.coeff 0 = 1 := by rw [← hq_deg]; exact hq_monic.leadingCoeff
      rw [this, map_one]
    rw [hq, hq1, mul_one]
  have hf_irred : Irreducible (f.map φ) := by
    rw [← hmin_eq]; exact minpoly.irreducible hθ'_int
  -- Express every σ_g(θ') in the power basis 1, θ', ..., θ'^(N-1)
  let pb := (IntermediateField.adjoin.powerBasis hθ'_int).map
    ((IntermediateField.equivOfEq hθ'_prim).trans IntermediateField.topEquiv)
  have hpb_dim : pb.dim = N := by
    have h := pb.finrank
    omega
  have hpb_gen : pb.gen = θ' := rfl
  have hexpr : ∀ g : G, ∃ c : Fin N → F, iso g θ' = ∑ k : Fin N, algebraMap F L (c k) * θ' ^ k.1 := by
    intro g
    let coeffs := pb.basis.repr (iso g θ')
    refine ⟨fun k => coeffs ⟨k.1, by omega⟩, ?_⟩
    have hsum := pb.basis.sum_repr (iso g θ')
    rw [← hsum]
    refine Finset.sum_equiv (Fin.castOrderIso hpb_dim).toEquiv (by simp) ?_
    intro k _
    simp [coeffs, pb.basis_eq_pow, hpb_gen, Algebra.smul_def]
  choose c hc using hexpr
  -- Clear denominators across all g : G and k : Fin N with a single Q ∈ K[X] \ {0}
  let p : G → Fin N → K[X] := fun g k => (c g k).num
  let q : G → Fin N → K[X] := fun g k => (c g k).denom
  have hq_ne : ∀ (g : G) (k : Fin N), q g k ≠ 0 := fun g k => RatFunc.denom_ne_zero _
  have hcq : ∀ (g : G) (k : Fin N), c g k = φ (p g k) / φ (q g k) := fun g k =>
    (RatFunc.num_div_denom _).symm
  let Q : K[X] := ∏ gk : G × Fin N, q gk.1 gk.2
  have hQ_ne : Q ≠ 0 := Finset.prod_ne_zero_iff.2 (fun gk _ => hq_ne gk.1 gk.2)
  have hφQ_ne : φ Q ≠ 0 := by simpa [map_zero] using hinj.ne hQ_ne
  let Q_div : G → Fin N → K[X] := fun g k => ∏ gk ∈ Finset.univ.erase (g, k), q gk.1 gk.2
  have hQ_eq : ∀ g k, q g k * Q_div g k = Q := fun g k =>
    Finset.mul_prod_erase Finset.univ (fun gk : G × Fin N => q gk.1 gk.2) (Finset.mem_univ (g, k))
  let R : G → K[X][X] := fun g => ∑ k : Fin N, C (p g k * Q_div g k) * X ^ k.1
  have hR_degX : ∀ g i, N ≤ i → (R g).coeff i = 0 := fun g i hi => by
    simp only [R, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    exact Finset.sum_eq_zero (fun k _ => if_neg (by omega))
  have hR_eval : ∀ g : G, iso g θ' = aeval θ' ((R g).map φ) / algebraMap F L (φ Q) := by
    intro g
    have hQ_L : algebraMap F L (φ Q) ≠ 0 := by
      intro hz; exact hφQ_ne ((RingHom.injective (algebraMap F L)) (hz.trans (map_zero _).symm))
    rw [eq_div_iff hQ_L, hc g, Finset.sum_mul]
    simp only [R, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
      map_sum, map_mul, aeval_C, map_pow, aeval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hcoef : c g k * φ Q = φ (p g k) * φ (Q_div g k) := by
      have hq_ne' : φ (q g k) ≠ 0 := by simpa [map_zero] using hinj.ne (hq_ne g k)
      rw [hcq g k, div_mul_eq_mul_div, div_eq_iff hq_ne', ← hQ_eq g k, map_mul]
      ring
    calc algebraMap F L (c g k) * θ' ^ k.1 * algebraMap F L (φ Q)
        = algebraMap F L (c g k * φ Q) * θ' ^ k.1 := by rw [map_mul]; ring
      _ = algebraMap F L (φ (p g k)) * algebraMap F L (φ (Q_div g k)) * θ' ^ k.1 := by
          rw [hcoef, map_mul]
  -- Helper: any P ∈ K[X][X] with aeval θ' (P.map φ) = 0 is divisible by monic f in K[X][X]
  have hdvd_f : ∀ P : K[X][X], aeval θ' (P.map φ) = 0 → ∃ W : K[X][X], P = f * W := by
    intro P hP
    refine ⟨P /ₘ f, ?_⟩
    have hmod := modByMonic_add_div P f
    have hmod0 : P %ₘ f = 0 := by
      apply Polynomial.map_injective φ hinj
      rw [Polynomial.map_zero]
      have hd1 : f.map φ ∣ P.map φ := by rw [← hmin_eq]; exact minpoly.dvd F θ' hP
      have hd2 : f.map φ ∣ (P %ₘ f).map φ := by
        have hmap_eq : (P %ₘ f).map φ + f.map φ * (P /ₘ f).map φ = P.map φ := by
          rw [← Polynomial.map_mul, ← Polynomial.map_add, hmod]
        have : (P %ₘ f).map φ = P.map φ - f.map φ * (P /ₘ f).map φ := eq_sub_of_add_eq hmap_eq
        rw [this]
        exact dvd_sub hd1 (dvd_mul_right _ _)
      by_contra hne
      have hle := natDegree_le_of_dvd hd2 hne
      have hne0 : P %ₘ f ≠ 0 := fun hz => hne (by rw [hz, Polynomial.map_zero])
      have hlt : ((P %ₘ f).map φ).natDegree < (f.map φ).natDegree := by
        rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj]
        have hdeg_lt : (P %ₘ f).degree < f.degree := degree_modByMonic_lt P hf_monic
        rw [degree_eq_natDegree hne0, degree_eq_natDegree hf_monic.ne_zero] at hdeg_lt
        exact_mod_cast hdeg_lt
      omega
    rw [hmod0, zero_add] at hmod
    exact hmod.symm
  -- Build W g
  have hW_ex : ∀ g : G, ∃ W : K[X][X], homSubst N f Q (R g) = f * W := by
    intro g
    apply hdvd_f
    rw [aeval_homSubst N f Q (R g) θ' (fun i hi => coeff_eq_zero_of_natDegree_lt (by omega)) hφQ_ne]
    rw [← hR_eval g]
    have h0 : aeval (iso g θ') (f.map φ) = 0 := by
      rw [← AlgEquiv.coe_toAlgHom, aeval_algHom_apply, hf_root, map_zero]
    rw [h0, mul_zero]
  choose W hW using hW_ex
  -- Build U g h
  have hU_ex : ∀ g h : G, ∃ U : K[X][X], C (Q ^ N) * R (g * h) - homSubst N (R h) Q (R g) = f * U := by
    intro g h
    apply hdvd_f
    rw [Polynomial.map_sub, Polynomial.map_mul, map_C, map_pow, map_sub, map_mul,
      aeval_C, map_pow, aeval_homSubst N (R h) Q (R g) θ' (fun i hi => hR_degX h i (by omega)) hφQ_ne]
    have hQ_L : algebraMap F L (φ Q) ≠ 0 := by
      intro hz; exact hφQ_ne ((RingHom.injective (algebraMap F L)) (hz.trans (map_zero _).symm))
    have hcomp : iso (g * h) θ' = iso g (iso h θ') := by simp [map_mul]
    rw [hR_eval (g * h), hR_eval h, map_div₀, AlgEquiv.commutes] at hcomp
    have hmap_aeval : iso g (aeval θ' ((R h).map φ)) = aeval (iso g θ') ((R h).map φ) := by
      exact (aeval_algHom_apply (iso g).toAlgHom θ' ((R h).map φ)).symm
    rw [hmap_aeval, hR_eval g] at hcomp
    have hcancel : aeval θ' ((R (g * h)).map φ) =
        aeval (aeval θ' ((R g).map φ) / algebraMap F L (φ Q)) ((R h).map φ) := by
      exact (div_left_inj' hQ_L).1 hcomp
    rw [hcancel, sub_self]
  choose U hU using hU_ex
  -- Distinctness of R g
  have hDist : ∀ g h : G, g ≠ h → R g ≠ R h := by
    intro g h hgh heq
    apply hgh
    apply iso.injective
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ F⟮θ'⟯ := by rw [hθ'_prim]; trivial
    have hsame : iso g θ' = iso h θ' := by rw [hR_eval g, hR_eval h, heq]
    have hsub : ∀ y ∈ F⟮θ'⟯, iso g y = iso h y := by
      intro y hy
      let eqSet : IntermediateField F L := {
        carrier := { y : L | iso g y = iso h y }
        add_mem' := fun ha hb => by simp at ha hb ⊢; rw [ha, hb]
        zero_mem' := by simp
        mul_mem' := fun ha hb => by simp at ha hb ⊢; rw [ha, hb]
        one_mem' := by simp
        algebraMap_mem' := fun c => by
          show iso g (algebraMap F L c) = iso h (algebraMap F L c)
          rw [AlgEquiv.commutes, AlgEquiv.commutes]
        inv_mem' := fun ha => by simp at ha ⊢
      }
      have hle : F⟮θ'⟯ ≤ eqSet := IntermediateField.adjoin_simple_le_iff.2 hsame
      exact hle hy
    exact hsub x hx
  -- Choose concrete degree bounds from the witness
  let D := polyDegT f
  let D' := max Q.natDegree (Finset.univ.sup (fun g : G => polyDegT (R g)))
  let M_W := Finset.univ.sup (fun g : G => (W g).natDegree)
  let D_W := Finset.univ.sup (fun g : G => polyDegT (W g))
  let M_U := Finset.univ.sup (fun gh : G × G => (U gh.1 gh.2).natDegree)
  let D_U := Finset.univ.sup (fun gh : G × G => polyDegT (U gh.1 gh.2))
  refine ⟨D, D', M_W, D_W, M_U, D_U, ⟨{
    f := f
    Q := Q
    R := R
    W := W
    U := U
    hf_monic := hf_monic
    hf_deg := hf_deg
    hf_D := le_rfl
    hQ_ne := hQ_ne
    hQ_deg := le_max_left _ _
    hR_degX := hR_degX
    hR_D := fun g => le_trans (Finset.le_sup (f := fun g : G => polyDegT (R g)) (Finset.mem_univ g))
      (le_max_right _ _)
    hW_degX := fun g => Finset.le_sup (f := fun g : G => (W g).natDegree) (Finset.mem_univ g)
    hW_D := fun g => Finset.le_sup (f := fun g : G => polyDegT (W g)) (Finset.mem_univ g)
    hU_degX := fun g h =>
      Finset.le_sup (f := fun gh : G × G => (U gh.1 gh.2).natDegree) (Finset.mem_univ (g, h))
    hU_D := fun g h =>
      Finset.le_sup (f := fun gh : G × G => polyDegT (U gh.1 gh.2)) (Finset.mem_univ (g, h))
    hIrred := fun g h hg hh hg1 hglt _ _ hmul => by
      have hmap : f.map φ = g.map φ * h.map φ := by rw [← Polynomial.map_mul, hmul]
      rcases hf_irred.isUnit_or_isUnit hmap with hu | hu
      · have h0 := natDegree_eq_zero_of_isUnit hu
        rw [natDegree_map_eq_of_injective hinj] at h0; omega
      · have h0 := natDegree_eq_zero_of_isUnit hu
        rw [natDegree_map_eq_of_injective hinj] at h0
        have hsum : g.natDegree + h.natDegree = N := by
          rw [← natDegree_mul hg.ne_zero hh.ne_zero, ← hmul, hf_deg]
        omega
    hRoot := hW
    hMul := hU
    hDist := hDist
  }⟩⟩

-- Reconstruct GaloisRealization (RatFunc K) G from GaloisWitness over any field K
lemma galoisRealization_of_witness {G : Type} [Fintype G] [Group G] [DecidableEq G]
    {K : Type*} [Field K] {D D' M_W D_W M_U D_U : ℕ} (hG : 1 ≤ Fintype.card G)
    (wit : GaloisWitness G K (Fintype.card G) D D' M_W D_W M_U D_U) :
    InverseGalois.IsRealizable (RatFunc K) G := by
  set F := RatFunc K
  set φ := algebraMap K[X] F
  set N := Fintype.card G
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] F
  have hQ_ne : φ wit.Q ≠ 0 := by simpa [map_zero] using hinj.ne wit.hQ_ne
  let fF : F[X] := wit.f.map φ
  have hf_irred : Irreducible fF :=
    irreducible_map_of_no_bounded_monic_factor wit.hf_monic (by rw [wit.hf_deg]; exact hG)
      wit.hf_D (by rw [wit.hf_deg]; exact wit.hIrred)
  have : Fact (Irreducible fF) := ⟨hf_irred⟩
  let L := AdjoinRoot fF
  let α : L := AdjoinRoot.root fF
  have hfF_deg : fF.natDegree = N := (natDegree_map_eq_of_injective hinj _).trans wit.hf_deg
  have hfinrank : Module.finrank F L = N := by
    let hpb := AdjoinRoot.powerBasis hf_irred.ne_zero
    have h1 : Module.finrank F L = fF.natDegree := by
      rw [hpb.finrank]; exact AdjoinRoot.powerBasis_dim hf_irred.ne_zero
    omega
  have : FiniteDimensional F L := Module.finite_of_finrank_pos (by omega)
  have hQ_L : algebraMap F L (φ wit.Q) ≠ 0 := by
    intro hz; exact hQ_ne ((RingHom.injective (algebraMap F L)) (hz.trans (map_zero _).symm))
  have hfF_root : aeval α fF = 0 := by
    rw [aeval_def]; exact AdjoinRoot.eval₂_root fF
  -- Build F-algebra endomorphisms σ_g : L →ₐ[F] L
  have hroot_g : ∀ g : G, aeval (aeval α ((wit.R g).map φ) / algebraMap F L (φ wit.Q)) fF = 0 := by
    intro g
    have h1 := congr_arg (fun P : K[X][X] => aeval α (P.map φ)) (wit.hRoot g)
    rw [aeval_homSubst N wit.f wit.Q (wit.R g) α
      (fun i hi => coeff_eq_zero_of_natDegree_lt (by rw [wit.hf_deg]; omega)) hQ_ne] at h1
    rw [Polynomial.map_mul, map_mul] at h1
    change algebraMap F L (φ wit.Q) ^ N *
        aeval (aeval α ((wit.R g).map φ) / algebraMap F L (φ wit.Q)) fF =
        aeval α fF * aeval α ((wit.W g).map φ) at h1
    rw [hfF_root, zero_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero N hQ_L)
  let endG : G → (L →ₐ[F] L) := fun g =>
    AdjoinRoot.liftAlgHom fF (Algebra.ofId F L) _ (hroot_g g)
  have hendG_root : ∀ g : G, endG g α = aeval α ((wit.R g).map φ) / algebraMap F L (φ wit.Q) :=
    fun g => AdjoinRoot.liftAlgHom_root _ _ _ _
  -- Check endG (g * h) = (endG g).comp (endG h)
  have hendG_mul : ∀ g h : G, endG (g * h) = (endG g).comp (endG h) := by
    intro g h
    apply AdjoinRoot.algHom_ext
    change endG (g * h) α = endG g (endG h α)
    rw [hendG_root (g * h), hendG_root h, map_div₀, AlgHom.commutes]
    have hmap_aeval : endG g (aeval α ((wit.R h).map φ)) = aeval (endG g α) ((wit.R h).map φ) :=
      (aeval_algHom_apply (endG g) α ((wit.R h).map φ)).symm
    rw [hmap_aeval, hendG_root g]
    have h1 := congr_arg (fun P : K[X][X] => aeval α (P.map φ)) (wit.hMul g h)
    rw [Polynomial.map_sub, Polynomial.map_mul, map_C, map_pow, map_sub, map_mul,
      aeval_C, map_pow,
      aeval_homSubst N (wit.R h) wit.Q (wit.R g) α
        (fun i hi => wit.hR_degX h i (by omega)) hQ_ne,
      Polynomial.map_mul, map_mul] at h1
    change algebraMap F L (φ wit.Q) ^ N * aeval α ((wit.R (g * h)).map φ) -
        algebraMap F L (φ wit.Q) ^ N *
          aeval (aeval α ((wit.R g).map φ) / algebraMap F L (φ wit.Q)) ((wit.R h).map φ) =
        aeval α fF * aeval α ((wit.U g h).map φ) at h1
    rw [hfF_root, zero_mul] at h1
    have h2 : algebraMap F L (φ wit.Q) ^ N * aeval α ((wit.R (g * h)).map φ) =
        algebraMap F L (φ wit.Q) ^ N *
          aeval (aeval α ((wit.R g).map φ) / algebraMap F L (φ wit.Q)) ((wit.R h).map φ) :=
      sub_eq_zero.1 h1
    have h3 := mul_left_cancel₀ (pow_ne_zero N hQ_L) h2
    rw [h3]
  -- Every F-alg endomorphism of finite-dimensional field L is bijective, so endG 1 = id!
  have hendG_bij : ∀ g : G, Function.Bijective (endG g) := fun g =>
    ⟨(endG g).toRingHom.injective,
      LinearMap.surjective_of_injective (f := (endG g).toLinearMap) (endG g).toRingHom.injective⟩
  have hendG_one : endG 1 = AlgHom.id F L := by
    have hidem : (endG 1).comp (endG 1) = endG 1 := by rw [← hendG_mul 1 1, mul_one]
    apply AlgHom.ext; intro x
    obtain ⟨y, rfl⟩ := (hendG_bij 1).2 x
    exact congr_arg (fun f : L →ₐ[F] L => f y) hidem
  -- Upgrade endG to MonoidHom G →* (L ≃ₐ[F] L)
  let autG : G →* (L ≃ₐ[F] L) := {
    toFun := fun g => AlgEquiv.ofAlgHom (endG g) (endG g⁻¹)
      (by rw [← hendG_mul, mul_inv_cancel, hendG_one])
      (by rw [← hendG_mul, inv_mul_cancel, hendG_one])
    map_one' := by ext x; simp [hendG_one]
    map_mul' := fun g h => by ext x; simp [hendG_mul]
  }
  -- Injectivity of autG
  have hautG_inj : Function.Injective autG := by
    intro g h heq
    by_contra hne
    have hα : endG g α = endG h α := congr_arg (fun σ : L ≃ₐ[F] L => σ α) heq
    rw [hendG_root g, hendG_root h, div_left_inj' hQ_L] at hα
    have hsub0 : aeval α (((wit.R g - wit.R h).map φ)) = 0 := by
      rw [Polynomial.map_sub, map_sub, hα, sub_self]
    have hdvd : fF ∣ (wit.R g - wit.R h).map φ := by
      have hm : minpoly F α = fF := by
        obtain ⟨q, hq⟩ := minpoly.dvd F α hfF_root
        have hmin_irred := minpoly.irreducible (Algebra.IsIntegral.isIntegral (R := F) α)
        have hmon1 := minpoly.monic (Algebra.IsIntegral.isIntegral (R := F) α)
        have hmon2 : fF.Monic := wit.hf_monic.map φ
        have hqu : IsUnit q := (hf_irred.isUnit_or_isUnit hq).resolve_left hmin_irred.not_isUnit
        have hq0 : q.natDegree = 0 := natDegree_eq_zero_of_isUnit hqu
        have hqlc : q.leadingCoeff = 1 := by
          have hlc : (minpoly F α).leadingCoeff * q.leadingCoeff = 1 := by
            rw [← leadingCoeff_mul, ← hq]; exact hmon2.leadingCoeff
          rwa [hmon1.leadingCoeff, one_mul] at hlc
        have hq1 : q = 1 := by
          rw [eq_C_of_natDegree_eq_zero hq0]
          have : q.coeff 0 = 1 := by rw [← hq0]; exact hqlc
          rw [this, map_one]
        rw [hq1, mul_one] at hq; exact hq.symm
      rw [← hm]; exact minpoly.dvd F α hsub0
    have hdiff_ne : (wit.R g - wit.R h).map φ ≠ 0 := by
      intro hz
      have h0 : wit.R g - wit.R h = 0 := Polynomial.map_injective φ hinj (by rw [hz, Polynomial.map_zero])
      exact wit.hDist g h hne (sub_eq_zero.1 h0)
    have hle := natDegree_le_of_dvd hdvd hdiff_ne
    have hdiff0 : wit.R g - wit.R h ≠ 0 := fun hz => hdiff_ne (by rw [hz, Polynomial.map_zero])
    have hlt : ((wit.R g - wit.R h).map φ).natDegree < N := by
      rw [natDegree_map_eq_of_injective hinj]
      refine (natDegree_lt_iff_degree_lt hdiff0).2 ?_
      rw [degree_lt_iff_coeff_zero]
      intro i hi
      rw [coeff_sub, wit.hR_degX g i hi, wit.hR_degX h i hi, sub_self]
    omega
  -- Card bound: N = card G ≤ Nat.card (L ≃ₐ[F] L) ≤ finrank F L = N
  have : Finite (L ≃ₐ[F] L) := inferInstance
  have hle1 : N ≤ Nat.card (L ≃ₐ[F] L) := by
    have hN' : N = Nat.card G := (Nat.card_eq_fintype_card).symm
    rw [hN']
    exact Nat.card_le_card_of_injective autG hautG_inj
  have hle2 : Nat.card (L ≃ₐ[F] L) ≤ N := by
    have hmul := Module.finrank_mul_finrank F (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[F] L))) L
    rw [hfinrank, IntermediateField.finrank_fixedField_eq_card] at hmul
    have hpos : 0 < Module.finrank F (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[F] L))) :=
      Module.finrank_pos
    have htop : Nat.card (⊤ : Subgroup (L ≃ₐ[F] L)) = Nat.card (L ≃ₐ[F] L) :=
      Nat.card_congr {
        toFun := fun σ => σ.1
        invFun := fun σ => ⟨σ, Subgroup.mem_top σ⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
      }
    rw [htop] at hmul
    nlinarith
  have hcard_eq : Nat.card (L ≃ₐ[F] L) = Module.finrank F L := by omega
  have : IsGalois F L := IsGalois.of_card_aut_eq_finrank F L hcard_eq
  let _ : Fintype (L ≃ₐ[F] L) := Fintype.ofFinite _
  have hautG_bij : Function.Bijective autG :=
    (Fintype.bijective_iff_injective_and_card autG).2
      ⟨hautG_inj, by
        have h1 : Fintype.card G = N := rfl
        have h2 : Fintype.card (L ≃ₐ[F] L) = Nat.card (L ≃ₐ[F] L) := (Nat.card_eq_fintype_card).symm
        omega⟩
  exact ⟨⟨{
    L := L
    to_field := inferInstance
    to_algebra := inferInstance
    to_isGalois := inferInstance
    iso := MulEquiv.ofBijective autG hautG_bij
  }⟩⟩

-- Wrapper type in Type 0 with no preexisting Mul instance
structure SmallGroup (n : ℕ) : Type where
  val : Fin n

-- Helper: transfer for G0 : Type 0 directly
lemma transfer_realizable_type0 {G0 : Type} {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Fintype G0] [Group G0]
    (hC : ∀ (H : Type) [Fintype H] [Group H],
      ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L)
        (_ : IsGalois (RatFunc ℂ) L) (_ : FiniteDimensional (RatFunc ℂ) L),
        Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L))) :
    InverseGalois.IsRealizable (RatFunc K) G0 := by
  classical
  have hG0 : 1 ≤ Fintype.card G0 := Fintype.card_pos
  obtain ⟨LC, _, _, _, _, ⟨isoC⟩⟩ := hC G0
  obtain ⟨D, D', M_W, D_W, M_U, D_U, hwitC⟩ :=
    exists_galoisWitness_of_realization hG0 isoC
  let _ : CompatibleRing ℂ := compatibleRingOfRing ℂ
  let _ : CompatibleRing K := compatibleRingOfRing K
  have hsentC : ℂ ⊨ galoisSentence G0 (Fintype.card G0) D D' M_W D_W M_U D_U :=
    (realize_galoisSentence_iff hG0).2 hwitC
  have hcomp := FirstOrder.Field.ACF_isComplete (Or.inr rfl)
  have hsentK : K ⊨ galoisSentence G0 (Fintype.card G0) D D' M_W D_W M_U D_U :=
    (hcomp.realize_sentence_iff _ K).2 ((hcomp.realize_sentence_iff _ ℂ).1 hsentC)
  obtain ⟨witK⟩ := (realize_galoisSentence_iff hG0).1 hsentK
  exact galoisRealization_of_witness hG0 witK

-- Main Part II Theorem: ACF_isComplete transfer from ℂ to any algebraically closed char 0 field K!
theorem transfer_realizable {G K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Fintype G] [Group G]
    (hC : ∀ (H : Type) [Fintype H] [Group H],
      ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L)
        (_ : IsGalois (RatFunc ℂ) L) (_ : FiniteDimensional (RatFunc ℂ) L),
        Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L))) :
    InverseGalois.IsRealizable (RatFunc K) G := by
  by_cases hsub : Subsingleton G
  · exact isRealizable_of_subsingleton
  · classical
    let e0 : G ≃ SmallGroup (Fintype.card G) :=
      (Fintype.equivFin G).trans
        { toFun := SmallGroup.mk, invFun := SmallGroup.val,
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    let _ : Fintype (SmallGroup (Fintype.card G)) := Fintype.ofEquiv G e0
    let _ : Group (SmallGroup (Fintype.card G)) := {
      mul := fun x y => e0 (e0.symm x * e0.symm y)
      one := e0 1
      inv := fun x => e0 (e0.symm x)⁻¹
      mul_assoc := fun a b c => by
        show e0 (e0.symm (e0 (e0.symm a * e0.symm b)) * e0.symm c) =
             e0 (e0.symm a * e0.symm (e0 (e0.symm b * e0.symm c)))
        simp [mul_assoc]
      one_mul := fun a => by
        show e0 (e0.symm (e0 1) * e0.symm a) = a
        simp
      mul_one := fun a => by
        show e0 (e0.symm a * e0.symm (e0 1)) = a
        simp
      inv_mul_cancel := fun a => by
        show e0 (e0.symm (e0 (e0.symm a)⁻¹) * e0.symm a) = e0 1
        simp
    }
    let emul : G ≃* SmallGroup (Fintype.card G) := {
      toEquiv := e0
      map_mul' := fun x y => by show e0 (x * y) = e0 (e0.symm (e0 x) * e0.symm (e0 y)); simp
    }
    exact isRealizable_of_mulEquiv emul.symm (transfer_realizable_type0 hC)

end StrategyBPart2

theorem OMA.solution : type_of% @InverseGalois.inverse_galois_problem.variants.complex_function_field := by
  intro G K _ _ _ _ _
  exact StrategyBPart2.transfer_realizable StrategyBPart1c.realize_complex
