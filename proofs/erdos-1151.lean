import OMAStatements.S_erdos_1151

-- Problem: Erdős Problem 1151
-- Credit: @Brean0
-- Primitive-row block-spike construction with Mobius cancellation and a width-independent
-- total-variation tail bound.

namespace OMA.Erdos1151

open Polynomial Filter Finset Topology
open scoped BigOperators
open OMA.S_erdos_1151

/-! ### Section 1: Chebyshev angles, nodes, and primitive-row arithmetic -/

private noncomputable def chebAngle (n : ℕ) (i : Fin n) : ℝ :=
  (2 * (i : ℝ) + 1) * Real.pi / (2 * n)

private lemma chebNode_eq_cos (n : ℕ) (i : Fin n) :
    chebNode n i = Real.cos (chebAngle n i) := rfl

private lemma chebAngle_pos {n : ℕ} (i : Fin n) : 0 < chebAngle n i := by
  have hn : 0 < n := Nat.pos_of_ne_zero (Fin.pos i).ne'
  dsimp [chebAngle]
  positivity

private lemma chebAngle_lt_pi {n : ℕ} (i : Fin n) : chebAngle n i < Real.pi := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (Fin.pos i).ne')
  have hi : (2 * (i : ℝ) + 1) < 2 * n := by
    have hlt : i.val < n := i.isLt
    exact_mod_cast (show 2 * i.val + 1 < 2 * n by omega)
  dsimp [chebAngle]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

private lemma chebAngle_mem_Icc {n : ℕ} (i : Fin n) :
    chebAngle n i ∈ Set.Icc 0 Real.pi :=
  ⟨(chebAngle_pos i).le, (chebAngle_lt_pi i).le⟩

private lemma chebAngle_strictMono (n : ℕ) : StrictMono (chebAngle n) := by
  intro i j hij
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (Fin.pos i).ne')
  dsimp [chebAngle]
  apply div_lt_div_of_pos_right _ (by positivity)
  have hlt : (i : ℝ) < j := by exact_mod_cast hij
  nlinarith [Real.pi_pos]

private lemma chebNode_injective (n : ℕ) : Function.Injective (chebNode n) := by
  intro i j hij
  have h1 : chebAngle n i = chebAngle n j :=
    Real.injOn_cos (chebAngle_mem_Icc i) (chebAngle_mem_Icc j) hij
  exact (chebAngle_strictMono n).injective h1

private lemma chebNode_eq_iff {n m : ℕ} (i : Fin n) (j : Fin m) :
    chebNode n i = chebNode m j ↔ (2 * i.val + 1) * m = (2 * j.val + 1) * n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (Fin.pos i).ne')
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (Fin.pos j).ne')
  constructor
  · intro h
    have ha : chebAngle n i = chebAngle m j :=
      Real.injOn_cos (chebAngle_mem_Icc i) (chebAngle_mem_Icc j) h
    dsimp [chebAngle] at ha
    have hcancel : (2 * (i : ℝ) + 1) * m = (2 * (j : ℝ) + 1) * n := by
      have hne1 : (2 * (n : ℝ)) ≠ 0 := by positivity
      have hne2 : (2 * (m : ℝ)) ≠ 0 := by positivity
      field_simp [hne1, hne2] at ha
      rw [ha]
      ring
    exact_mod_cast hcancel
  · intro h
    rw [chebNode_eq_cos, chebNode_eq_cos]
    congr 1
    dsimp [chebAngle]
    have hR : (2 * (i : ℝ) + 1) * m = (2 * (j : ℝ) + 1) * n := by exact_mod_cast h
    have hne1 : (2 * (n : ℝ)) ≠ 0 := by positivity
    have hne2 : (2 * (m : ℝ)) ≠ 0 := by positivity
    field_simp [hne1, hne2]
    nlinarith

private lemma cos_add_nat_mul_two_pi (x : ℝ) (k : ℕ) :
    Real.cos (x + k * (2 * Real.pi)) = Real.cos x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, Real.cos_add_two_pi, ih]

private lemma reduce_odd_angle (p q : ℕ) (hp : Odd p) (hq : Odd q) :
    ∃ p' : ℕ, Odd p' ∧ 1 ≤ p' ∧ p' ≤ q ∧
      Real.cos (Real.pi * p / q) = Real.cos (Real.pi * p' / q) := by
  have hqpos : 0 < q := hq.pos
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
  set k := p / (2 * q)
  set r := p % (2 * q)
  have hdiv : p = 2 * q * k + r := (Nat.div_add_mod p (2 * q)).symm
  have hrlt : r < 2 * q := Nat.mod_lt p (by omega)
  have hrodd : Odd r := by
    obtain ⟨t, ht⟩ := hp
    have h1 : 2 * t + 1 = 2 * (q * k) + r := by rw [← ht, hdiv]; ring
    refine ⟨t - q * k, ?_⟩
    omega
  by_cases hrq : r ≤ q
  · refine ⟨r, hrodd, hrodd.pos, hrq, ?_⟩
    have harg : Real.pi * (p : ℝ) / q = Real.pi * (r : ℝ) / q + (k : ℝ) * (2 * Real.pi) := by
      have hpR : (p : ℝ) = 2 * (q : ℝ) * (k : ℝ) + (r : ℝ) := by exact_mod_cast hdiv
      rw [hpR]
      field_simp [hqR]
      ring
    rw [harg, cos_add_nat_mul_two_pi]
  · set p' := 2 * q - r
    have hp'odd : Odd p' := by
      obtain ⟨t, ht⟩ := hrodd
      refine ⟨q - t - 1, ?_⟩
      omega
    refine ⟨p', hp'odd, hp'odd.pos, by omega, ?_⟩
    have harg : Real.pi * (p : ℝ) / q = -(Real.pi * (p' : ℝ) / q) + ((k + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
      have hpR : (p : ℝ) = 2 * (q : ℝ) * (k : ℝ) + (r : ℝ) := by exact_mod_cast hdiv
      have hrp' : (p' : ℝ) = 2 * (q : ℝ) - (r : ℝ) := by
        dsimp [p']
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hpR, hrp']
      push_cast
      field_simp [hqR]
      ring
    rw [harg, cos_add_nat_mul_two_pi, Real.cos_neg]

private lemma chebNode_ne_cos_odd (n : ℕ) (i : Fin n) {p' q : ℕ}
    (_hp' : Odd p') (hq : Odd q) (_hp1 : 1 ≤ p') (hpq : p' ≤ q) :
    Real.cos (Real.pi * p' / q) ≠ chebNode n i := by
  intro heq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (Fin.pos i).ne')
  have hθ0_mem : Real.pi * p' / q ∈ Set.Icc 0 Real.pi := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hqpos]
    have hpqR : (p' : ℝ) ≤ q := by exact_mod_cast hpq
    nlinarith [Real.pi_pos]
  have hang : Real.pi * p' / q = chebAngle n i :=
    Real.injOn_cos hθ0_mem (chebAngle_mem_Icc i) heq
  dsimp [chebAngle] at hang
  have hmul : (2 * (n : ℝ)) * (p' : ℝ) = (2 * (i : ℝ) + 1) * (q : ℝ) := by
    have hne1 : (2 * (n : ℝ)) ≠ 0 := by positivity
    have hne2 : (q : ℝ) ≠ 0 := by positivity
    field_simp [hne1, hne2] at hang
    nlinarith [Real.pi_pos]
  have hnat : 2 * n * p' = (2 * i.val + 1) * q := by exact_mod_cast hmul
  have hi_odd : Odd (2 * i.val + 1) := ⟨i.val, rfl⟩
  have hodd : Odd ((2 * i.val + 1) * q) := hi_odd.mul hq
  rw [← hnat] at hodd
  have heven : Even (2 * n * p') := ⟨n * p', by ring⟩
  exact (Nat.not_even_iff_odd.mpr hodd) heven

private def IsPrim (n : ℕ) (i : Fin n) : Prop :=
  Nat.Coprime (2 * i.val + 1) n

private instance (n : ℕ) (i : Fin n) : Decidable (IsPrim n i) :=
  inferInstanceAs (Decidable (Nat.Coprime (2 * i.val + 1) n))

private lemma chebNode_eq_of_isPrim {n m : ℕ} {i : Fin n} (hprim : IsPrim n i)
    {j : Fin m} (heq : chebNode m j = chebNode n i) :
    ∃ c : ℕ, Odd c ∧ m = c * n ∧ 2 * j.val + 1 = c * (2 * i.val + 1) := by
  have hEq : (2 * j.val + 1) * n = (2 * i.val + 1) * m := (chebNode_eq_iff j i).mp heq
  have hdvd : n ∣ m := by
    have h1 : n ∣ (2 * i.val + 1) * m := ⟨2 * j.val + 1, by linarith⟩
    exact hprim.symm.dvd_of_dvd_mul_left h1
  obtain ⟨c, hc⟩ := hdvd
  have hn : 0 < n := Nat.pos_of_ne_zero (Fin.pos i).ne'
  have hmul : (2 * j.val + 1) * n = (c * (2 * i.val + 1)) * n := by
    rw [hEq, hc]; ring
  have hidx : 2 * j.val + 1 = c * (2 * i.val + 1) := Nat.eq_of_mul_eq_mul_right hn hmul
  have hcodd : Odd c := by
    by_contra hnot
    obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hnot
    have : 2 * j.val + 1 = 2 * (t * (2 * i.val + 1)) := by rw [hidx, ht]; ring
    omega
  exact ⟨c, hcodd, by rw [hc, mul_comm], hidx⟩

/-! ### Section 2: Exact Chebyshev Lagrange weights and odd-multiple scaling -/

private noncomputable def chebWeight (n : ℕ) (i : Fin n) (θ₀ : ℝ) : ℝ :=
  (-1 : ℝ) ^ i.val * Real.sin (chebAngle n i) * Real.cos (n * θ₀) /
    (n * (Real.cos θ₀ - Real.cos (chebAngle n i)))

private lemma sin_odd_mul_pi_div_two (i : ℕ) :
    Real.sin ((2 * (i : ℝ) + 1) * Real.pi / 2) = (-1 : ℝ) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h : (2 * ((i + 1 : ℕ) : ℝ) + 1) * Real.pi / 2 =
        (2 * (i : ℝ) + 1) * Real.pi / 2 + Real.pi := by
      push_cast; ring
    rw [h, Real.sin_add_pi, ih, pow_succ]
    ring

private lemma T_eq_C_mul_nodal (n : ℕ) :
    Polynomial.Chebyshev.T ℝ (n : ℤ) =
      C (Polynomial.Chebyshev.T ℝ (n : ℤ)).leadingCoeff *
        Lagrange.nodal Finset.univ (chebNode n) := by
  have himg : (Finset.range n).image (fun k : ℕ => Real.cos ((2 * k + 1) * Real.pi / (2 * n))) =
      Finset.univ.image (chebNode n) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and, chebNode]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
  have hroots : (Polynomial.Chebyshev.T ℝ (n : ℤ)).roots =
      (Finset.univ.image (chebNode n)).val := by
    rw [Polynomial.Chebyshev.roots_T_real n, himg]
  have hcard : Multiset.card (Polynomial.Chebyshev.T ℝ (n : ℤ)).roots =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).natDegree := by
    rw [hroots, Finset.card_val, Finset.card_image_of_injective _ (chebNode_injective n),
      Finset.card_univ, Fintype.card_fin, Polynomial.Chebyshev.natDegree_T]
    simp
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hprod : ((Polynomial.Chebyshev.T ℝ (n : ℤ)).roots.map (fun a => X - C a)).prod =
      Lagrange.nodal Finset.univ (chebNode n) := by
    rw [hroots]
    change (∏ x ∈ Finset.univ.image (chebNode n), (X - C x)) =
      ∏ i ∈ Finset.univ, (X - C (chebNode n i))
    rw [Finset.prod_image (fun a _ b _ h => chebNode_injective n h)]
  rw [hprod] at hfac
  exact hfac.symm

private lemma eval_basis_chebNode (n : ℕ) (hn : 0 < n) (i : Fin n) (θ₀ : ℝ)
    (hne : ∀ j : Fin n, Real.cos θ₀ ≠ chebNode n j) :
    (Lagrange.basis Finset.univ (chebNode n) i).eval (Real.cos θ₀) = chebWeight n i θ₀ := by
  set T_n := Polynomial.Chebyshev.T ℝ (n : ℤ)
  set c := T_n.leadingCoeff
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr (Polynomial.Chebyshev.T_ne_zero ℝ (n : ℤ))
  have hT : T_n = C c * Lagrange.nodal Finset.univ (chebNode n) := T_eq_C_mul_nodal n
  have hT_eval : c * (Lagrange.nodal Finset.univ (chebNode n)).eval (Real.cos θ₀) =
      Real.cos (n * θ₀) := by
    have h1 := congrArg (Polynomial.eval (Real.cos θ₀)) hT
    rw [eval_mul, eval_C] at h1
    rw [← h1]
    exact Polynomial.Chebyshev.T_real_cos (n := (n : ℤ)) (θ := θ₀)
  have hderiv : Polynomial.derivative T_n =
      C c * Polynomial.derivative (Lagrange.nodal Finset.univ (chebNode n)) := by
    rw [hT, derivative_mul, derivative_C, zero_mul, zero_add]
  have hderiv_eval : c * (Lagrange.nodal (Finset.univ.erase i) (chebNode n)).eval (chebNode n i) =
      (Polynomial.derivative T_n).eval (chebNode n i) := by
    have h1 := congrArg (Polynomial.eval (chebNode n i)) hderiv
    rw [eval_mul, eval_C, Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i)] at h1
    exact h1.symm
  have hsin_pos : 0 < Real.sin (chebAngle n i) :=
    Real.sin_pos_of_pos_of_lt_pi (chebAngle_pos i) (chebAngle_lt_pi i)
  have hT_deriv_val : (Polynomial.derivative T_n).eval (chebNode n i) * Real.sin (chebAngle n i) =
      (n : ℝ) * (-1 : ℝ) ^ i.val := by
    have hU := Polynomial.Chebyshev.T_derivative_eq_U (R := ℝ) (n : ℤ)
    have h1 : (Polynomial.derivative T_n).eval (chebNode n i) =
        (n : ℝ) * (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval (Real.cos (chebAngle n i)) := by
      dsimp [T_n]
      rw [hU, eval_mul, eval_intCast, Int.cast_natCast, chebNode_eq_cos]
    rw [h1, mul_assoc]
    have hUcos := Polynomial.Chebyshev.U_real_cos (n := (n : ℤ) - 1) (θ := chebAngle n i)
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] at hUcos
    rw [hUcos]
    have harg : (n : ℝ) * chebAngle n i = (2 * (i : ℝ) + 1) * Real.pi / 2 := by
      dsimp [chebAngle]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnR]
    rw [harg, sin_odd_mul_pi_div_two]
  have hnw_inv : Lagrange.nodalWeight Finset.univ (chebNode n) i =
      ((Lagrange.nodal (Finset.univ.erase i) (chebNode n)).eval (chebNode n i))⁻¹ := by
    simp [Lagrange.nodalWeight, Lagrange.eval_nodal]
  have hnodal_ne : (Lagrange.nodal (Finset.univ.erase i) (chebNode n)).eval (chebNode n i) ≠ 0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro j hj heq
    exact (Finset.mem_erase.mp hj).1 (chebNode_injective n heq).symm
  have hsub_ne : Real.cos θ₀ - chebNode n i ≠ 0 := sub_ne_zero.mpr (hne i)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow_ne : (-1 : ℝ) ^ i.val ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Lagrange.eval_basis_not_at_node (Finset.mem_univ i) (hne i), hnw_inv]
  dsimp [chebWeight]
  rw [← chebNode_eq_cos]
  have h1 : c * (Lagrange.nodal (Finset.univ.erase i) (chebNode n)).eval (chebNode n i) *
      Real.sin (chebAngle n i) = (n : ℝ) * (-1 : ℝ) ^ i.val := by
    rw [hderiv_eval, hT_deriv_val]
  have hdiv : (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  field_simp [hnodal_ne, hsub_ne, hnR]
  have hkey : (Lagrange.nodal Finset.univ (chebNode n)).eval (Real.cos θ₀) * (n : ℝ) =
      (-1 : ℝ) ^ i.val * Real.sin (chebAngle n i) * Real.cos (↑n * θ₀) *
        (Lagrange.nodal (Finset.univ.erase i) (chebNode n)).eval (chebNode n i) := by
    apply mul_left_cancel₀ hc
    calc
      c * ((Lagrange.nodal Finset.univ (chebNode n)).eval (Real.cos θ₀) * (n : ℝ))
          = (c * (Lagrange.nodal Finset.univ (chebNode n)).eval (Real.cos θ₀)) * (n : ℝ) := by ring
      _ = Real.cos (↑n * θ₀) * (n : ℝ) := by rw [hT_eval]
      _ = Real.cos (↑n * θ₀) * ((n : ℝ) * (-1 : ℝ) ^ i.val) * (-1 : ℝ) ^ i.val := by
            calc Real.cos (↑n * θ₀) * (n : ℝ)
                = Real.cos (↑n * θ₀) * (n : ℝ) * ((-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val) := by rw [hdiv, mul_one]
              _ = _ := by ring
      _ = Real.cos (↑n * θ₀) *
            (c * (Lagrange.nodal (Finset.univ.erase i) (chebNode n)).eval (chebNode n i) *
              Real.sin (chebAngle n i)) * (-1 : ℝ) ^ i.val := by rw [h1]
      _ = c * ((-1 : ℝ) ^ i.val * Real.sin (chebAngle n i) * Real.cos (↑n * θ₀) *
            (Lagrange.nodal (Finset.univ.erase i) (chebNode n)).eval (chebNode n i)) := by ring
  linarith

private lemma eval_chebInterp_eq_sum (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n) (θ₀ : ℝ)
    (hne : ∀ j : Fin n, Real.cos θ₀ ≠ chebNode n j) :
    (chebInterp f n).eval (Real.cos θ₀) =
      ∑ i : Fin n, chebWeight n i θ₀ * f (chebNode n i) := by
  dsimp [chebInterp]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_basis_chebNode n hn i θ₀ hne, mul_comm]

private lemma eval_chebInterp_const (c : ℝ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (chebInterp (fun _ => c) n).eval x = c := by
  dsimp [chebInterp]
  have h1 : (fun _ : Fin n => c) = c • (1 : Fin n → ℝ) := by ext; simp
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [h1, LinearMap.map_smul, Lagrange.interpolate_one (chebNode_injective n).injOn hne,
    eval_smul, eval_one, smul_eq_mul, mul_one]

private lemma eval_chebInterp_add (f g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    (chebInterp (fun t => f t + g t) n).eval x =
      (chebInterp f n).eval x + (chebInterp g n).eval x := by
  dsimp [chebInterp]
  have h : (fun i : Fin n => f (chebNode n i) + g (chebNode n i)) =
      (fun i => f (chebNode n i)) + (fun i => g (chebNode n i)) := rfl
  rw [h, LinearMap.map_add, eval_add]

private lemma eval_chebInterp_smul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    (chebInterp (fun t => c * f t) n).eval x = c * (chebInterp f n).eval x := by
  dsimp [chebInterp]
  have h : (fun i : Fin n => c * f (chebNode n i)) = c • (fun i => f (chebNode n i)) := rfl
  rw [h, LinearMap.map_smul, eval_smul, smul_eq_mul]

private lemma eval_chebInterp_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ)
    (n : ℕ) (x : ℝ) :
    (chebInterp (fun t => ∑ a ∈ s, F a t) n).eval x =
      ∑ a ∈ s, (chebInterp (F a) n).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [chebInterp, Lagrange.interpolate_apply]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [eval_chebInterp_add, ih]

private lemma eval_chebInterp_congr {f g : ℝ → ℝ} {n : ℕ}
    (h : ∀ i : Fin n, f (chebNode n i) = g (chebNode n i)) (x : ℝ) :
    (chebInterp f n).eval x = (chebInterp g n).eval x := by
  dsimp [chebInterp]
  have hfun : (fun i : Fin n => f (chebNode n i)) = (fun i : Fin n => g (chebNode n i)) :=
    funext h
  rw [hfun]

private noncomputable def chi4 (d : ℕ) : ℝ := (-1 : ℝ) ^ (d / 2)

private lemma chi4_one : chi4 1 = 1 := by simp [chi4]

private lemma abs_chi4 (d : ℕ) : |chi4 d| = 1 := by
  simp [chi4]

private lemma chi4_mul_of_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    chi4 (a * b) = chi4 a * chi4 b := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  dsimp [chi4]
  have h1 : (2 * u + 1) / 2 = u := by omega
  have h2 : (2 * v + 1) / 2 = v := by omega
  have h3 : ((2 * u + 1) * (2 * v + 1)) / 2 = 2 * (u * v) + u + v := by
    have : (2 * u + 1) * (2 * v + 1) = 2 * (2 * (u * v) + u + v) + 1 := by ring
    omega
  rw [h1, h2, h3, pow_add, pow_add, pow_mul]
  norm_num

private lemma cos_mul_pow_two_mul_odd (d k p' q : ℕ) (hk : 1 ≤ k) (hq : 0 < q) :
    Real.cos ((d * (2 ^ k * q) : ℕ) * (Real.pi * p' / q)) = 1 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ, mul_comm]
  have harg : ((d * (2 ^ k * q) : ℕ) : ℝ) * (Real.pi * p' / q) =
      0 + ((d * 2 ^ (k - 1) * p' : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [h2k]
    push_cast
    field_simp [hqR]
    ring
  rw [harg, cos_add_nat_mul_two_pi, Real.cos_zero]

private lemma chebWeight_odd_mul {d k p' q : ℕ} (hd : Odd d) (hk : 1 ≤ k) (hq : 0 < q)
    {N : ℕ} (hN : N = 2 ^ k * q) (i : Fin N) (j : Fin (d * N))
    (hidx : 2 * j.val + 1 = d * (2 * i.val + 1)) :
    chebWeight (d * N) j (Real.pi * p' / q) =
      (chi4 d / d) * chebWeight N i (Real.pi * p' / q) := by
  have hdpos : 0 < d := hd.pos
  have hNpos : 0 < N := by rw [hN]; positivity
  have hang : chebAngle (d * N) j = chebAngle N i := by
    dsimp [chebAngle]
    have hidxR : (2 * (j : ℝ) + 1) = (d : ℝ) * (2 * (i : ℝ) + 1) := by exact_mod_cast hidx
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    rw [hidxR]
    push_cast
    field_simp [hdR, hNR]
  have hcos1 : Real.cos (((d * N : ℕ) : ℝ) * (Real.pi * p' / q)) = 1 := by
    rw [hN]; exact cos_mul_pow_two_mul_odd d k p' q hk hq
  have hcos2 : Real.cos ((N : ℝ) * (Real.pi * p' / q)) = 1 := by
    have := cos_mul_pow_two_mul_odd 1 k p' q hk hq
    simpa [hN] using this
  have hsign : (-1 : ℝ) ^ j.val = chi4 d * (-1 : ℝ) ^ i.val := by
    obtain ⟨u, rfl⟩ := hd
    have hj2 : 2 * j.val + 1 = 2 * (2 * (u * i.val) + i.val + u) + 1 := by rw [hidx]; ring
    have hj : j.val = 2 * (u * i.val) + i.val + u := by omega
    have hu : (2 * u + 1) / 2 = u := by omega
    rw [hj, chi4, hu, pow_add, pow_add, pow_mul]
    norm_num
    ring
  dsimp [chebWeight]
  rw [hang, hcos1, hcos2, hsign]
  push_cast
  rw [div_mul_div_comm]
  congr 1 <;> ring

/-! ### Section 3: Divergence of primitive-node Lebesgue sums -/

private lemma sin_ge_half_sin_mid {θ₀ θ : ℝ} (_hθ₀_pos : 0 < θ₀) (hθ₀_le : θ₀ ≤ Real.pi)
    (hθ_lo : θ₀ / 2 ≤ θ) (hθ_hi : θ < θ₀) :
    (1 / 2 : ℝ) * Real.sin ((θ₀ + θ) / 2) ≤ Real.sin θ := by
  by_cases h1 : Real.pi / 2 ≤ θ
  · have hsin_le : Real.sin ((θ₀ + θ) / 2) ≤ Real.sin θ := by
      rw [← Real.sin_pi_sub ((θ₀ + θ) / 2), ← Real.sin_pi_sub θ]
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith
      · linarith
      · linarith
    have hnonneg : 0 ≤ Real.sin ((θ₀ + θ) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    linarith
  · push Not at h1
    by_cases h2 : Real.pi / 4 ≤ θ
    · have hsin4 : (1 / 2 : ℝ) ≤ Real.sin θ := by
        have hsin_le : Real.sin (Real.pi / 4) ≤ Real.sin θ :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) h2
        rw [Real.sin_pi_div_four] at hsin_le
        have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        linarith
      have hmid_le : Real.sin ((θ₀ + θ) / 2) ≤ 1 := Real.sin_le_one _
      linarith
    · push Not at h2
      have hmid_le_2θ : (θ₀ + θ) / 2 ≤ 2 * θ := by linarith
      have h2θ_le : 2 * θ ≤ Real.pi / 2 := by linarith
      have hsin_le : Real.sin ((θ₀ + θ) / 2) ≤ Real.sin (2 * θ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h2θ_le hmid_le_2θ
      rw [Real.sin_two_mul] at hsin_le
      have hsin_nonneg : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one _
      nlinarith

private lemma abs_chebWeight_ge {n : ℕ} (hn : 0 < n) {p' q : ℕ} (hp' : 1 ≤ p') (hpq : p' ≤ q)
    (hcos : Real.cos ((n : ℝ) * (Real.pi * p' / q)) = 1) (i : Fin n)
    (hlo : (Real.pi * p' / q) / 2 ≤ chebAngle n i) (hhi : chebAngle n i < Real.pi * p' / q) :
    1 / (2 * (n : ℝ) * (Real.pi * p' / q - chebAngle n i)) ≤
      |chebWeight n i (Real.pi * p' / q)| := by
  set θ₀ := Real.pi * p' / q
  set θ := chebAngle n i
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hp'.trans hpq))
  have hθ₀_pos : 0 < θ₀ := by dsimp [θ₀]; positivity
  have hθ₀_le : θ₀ ≤ Real.pi := by
    dsimp [θ₀]
    rw [div_le_iff₀ hqpos]
    have : (p' : ℝ) ≤ q := by exact_mod_cast hpq
    nlinarith [Real.pi_pos]
  have hdiff_pos : 0 < θ₀ - θ := by linarith
  have hmid_pos : 0 < Real.sin ((θ₀ + θ) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hhalf_pos : 0 < Real.sin ((θ₀ - θ) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hhalf_le : Real.sin ((θ₀ - θ) / 2) ≤ (θ₀ - θ) / 2 :=
    Real.sin_le (by linarith)
  have hsin_ge := sin_ge_half_sin_mid hθ₀_pos hθ₀_le hlo hhi
  have hcos_sub : Real.cos θ - Real.cos θ₀ =
      2 * Real.sin ((θ₀ + θ) / 2) * Real.sin ((θ₀ - θ) / 2) := by
    rw [Real.cos_sub_cos]
    have h1 : (θ + θ₀) / 2 = (θ₀ + θ) / 2 := by ring
    have h2 : (θ - θ₀) / 2 = -((θ₀ - θ) / 2) := by ring
    rw [h1, h2, Real.sin_neg]
    ring
  have hcos_pos : 0 < Real.cos θ - Real.cos θ₀ := by rw [hcos_sub]; positivity
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (chebAngle_pos i) (chebAngle_lt_pi i)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hweight : |chebWeight n i θ₀| = Real.sin θ / ((n : ℝ) * (Real.cos θ - Real.cos θ₀)) := by
    dsimp [chebWeight]
    rw [hcos, mul_one, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hsin_pos, abs_mul, abs_of_pos hnR, abs_sub_comm, abs_of_pos hcos_pos]
  rw [hweight, hcos_sub]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * ((n : ℝ) * (2 * Real.sin ((θ₀ + θ) / 2) * Real.sin ((θ₀ - θ) / 2)))
      ≤ (n : ℝ) * (2 * Real.sin ((θ₀ + θ) / 2) * ((θ₀ - θ) / 2)) := by
        nlinarith [mul_le_mul_of_nonneg_left hhalf_le hmid_pos.le]
    _ = ((1 / 2 : ℝ) * Real.sin ((θ₀ + θ) / 2)) * (2 * (n : ℝ) * (θ₀ - θ)) := by ring
    _ ≤ Real.sin θ * (2 * (n : ℝ) * (θ₀ - θ)) :=
        mul_le_mul_of_nonneg_right hsin_ge (by positivity)

private lemma coprime_two_mul_mul_add_one (t d k q : ℕ) :
    Nat.Coprime (2 * (t * (d * q)) + 1) (d * (2 ^ k * q)) := by
  have h1 : Nat.Coprime (2 * (t * (d * q)) + 1) (2 ^ k) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right]
    exact ⟨t * (d * q), rfl⟩
  have h2 : Nat.Coprime (2 * (t * (d * q)) + 1) (d * q) := by
    have hmod : (2 * (t * (d * q)) + 1) % (d * q) = 1 % (d * q) := by
      rw [show 2 * (t * (d * q)) + 1 = (2 * t) * (d * q) + 1 by ring]
      exact Nat.mul_add_mod_self_right (2 * t) (d * q) 1
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, hmod, ← Nat.gcd_rec]
    simp
  have h3 : d * (2 ^ k * q) = 2 ^ k * (d * q) := by ring
  rw [h3]
  exact h1.mul_right h2

private lemma prim_lebesgue_term_ge {p' q K R k d r : ℕ}
    (hqpos : 0 < q) (hp1 : 1 ≤ p') (hpq : p' ≤ q)
    (hk1 : 1 ≤ k) (hkR : 4 * q * (R + 2) ≤ 2 ^ k)
    (hdpos : 0 < d) (hdK : d ≤ K) (hr : r < R)
    (i : Fin (d * (2 ^ k * q)))
    (hival : i.val = ((p' * 2 ^ k - 1) / q - r) * (d * q)) :
    (1 : ℝ) / (2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) * (1 / ((r : ℝ) + 1)) ≤
      |chebWeight (d * (2 ^ k * q)) i (Real.pi * p' / q)| := by
  let m := d * (2 ^ k * q)
  let tmax := (p' * 2 ^ k - 1) / q
  have hmpos : 0 < m := by dsimp [m]; positivity
  have htmax_hi : tmax * q ≤ p' * 2 ^ k - 1 := Nat.div_mul_le_self _ _
  have htmax_lo : p' * 2 ^ k - 1 < (tmax + 1) * q := by
    have h1 := Nat.lt_div_mul_add (a := p' * 2 ^ k - 1) hqpos
    change p' * 2 ^ k - 1 < tmax * q + q at h1
    rwa [add_mul, one_mul]
  have hp2k_pos : 1 ≤ p' * 2 ^ k := by
    have : 1 * 1 ≤ p' * 2 ^ k := Nat.mul_le_mul hp1 (Nat.one_le_two_pow)
    simpa using this
  have hR_le_tmax : R ≤ tmax := by
    have h1 : (R + 1) * q ≤ p' * 2 ^ k - 1 := by
      have h3 : 2 ^ k ≤ p' * 2 ^ k := Nat.le_mul_of_pos_left _ hp1
      have h4 : (R + 1) * q + 1 ≤ 4 * q * (R + 2) := by nlinarith
      omega
    have h2 : R + 1 ≤ tmax := (Nat.le_div_iff_mul_le hqpos).mpr h1
    omega
  have hcos : Real.cos ((m : ℝ) * (Real.pi * p' / q)) = 1 :=
    cos_mul_pow_two_mul_odd d k p' q hk1 hqpos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hhi : chebAngle m i < Real.pi * p' / q := by
    dsimp [chebAngle]
    rw [hival]
    have h1 : (2 * ((tmax - r) * (d * q)) + 1) * q < 2 * m * p' := by
      have ht1 : (tmax - r) * q ≤ p' * 2 ^ k - 1 :=
        (Nat.mul_le_mul_right q (Nat.sub_le _ _)).trans htmax_hi
      have hcalc : (2 * ((tmax - r) * (d * q)) + 1) * q =
          2 * d * q * ((tmax - r) * q) + q := by ring
      have hmcalc : 2 * m * p' = 2 * d * q * (p' * 2 ^ k) := by dsimp [m]; ring
      rw [hcalc, hmcalc]
      have : 2 * d * q * ((tmax - r) * q) + q ≤ 2 * d * q * (p' * 2 ^ k - 1) + q := by gcongr
      have : 2 * d * q * (p' * 2 ^ k - 1) + 2 * d * q = 2 * d * q * (p' * 2 ^ k) := by
        rw [← Nat.mul_add_one, Nat.sub_add_cancel hp2k_pos]
      have hqlt : q < 2 * d * q := by nlinarith
      omega
    have h1R : (2 * (((tmax - r) * (d * q) : ℕ) : ℝ) + 1) * (q : ℝ) <
        2 * (m : ℝ) * (p' : ℝ) := by exact_mod_cast h1
    rw [div_lt_div_iff₀ (by positivity) hqR]
    nlinarith [Real.pi_pos]
  have hlo : (Real.pi * p' / q) / 2 ≤ chebAngle m i := by
    dsimp [chebAngle]
    rw [hival]
    have h1 : m * p' ≤ (2 * ((tmax - r) * (d * q)) + 1) * q := by
      have hA : p' * 2 ^ k ≤ 2 * ((tmax - r) * q) := by
        have h2r : 2 * ((r + 1) * q) ≤ 2 ^ k := by
          have : 2 * ((r + 1) * q) ≤ 4 * q * (R + 2) := by nlinarith
          omega
        have h3 : (tmax - r) * q + (r + 1) * q = (tmax + 1) * q := by
          rw [← Nat.add_mul]; congr 1; omega
        have h4 : p' * 2 ^ k ≤ (tmax + 1) * q := by omega
        have h5 : 2 ^ k ≤ p' * 2 ^ k := Nat.le_mul_of_pos_left _ hp1
        omega
      have hmcalc : m * p' = d * q * (p' * 2 ^ k) := by dsimp [m]; ring
      have hrhs : (2 * ((tmax - r) * (d * q)) + 1) * q =
          d * q * (2 * ((tmax - r) * q)) + q := by ring
      rw [hmcalc, hrhs]
      calc d * q * (p' * 2 ^ k) ≤ d * q * (2 * ((tmax - r) * q)) :=
            Nat.mul_le_mul_left _ hA
        _ ≤ d * q * (2 * ((tmax - r) * q)) + q := Nat.le_add_right _ _
    have h1R : (m : ℝ) * (p' : ℝ) ≤ (2 * (((tmax - r) * (d * q) : ℕ) : ℝ) + 1) * (q : ℝ) := by
      exact_mod_cast h1
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos]
  have hgap : 2 * (m : ℝ) * (Real.pi * p' / q - chebAngle m i) ≤
      2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi * ((r : ℝ) + 1) := by
    dsimp [chebAngle]
    rw [hival]
    have h2m_ne : (2 * (m : ℝ)) ≠ 0 := by positivity
    have h1 : 2 * (m : ℝ) * (Real.pi * p' / q - (2 * (((tmax - r) * (d * q) : ℕ) : ℝ) + 1) * Real.pi / (2 * m)) =
        Real.pi * (2 * (d : ℝ) * ((p' * 2 ^ k : ℕ) : ℝ) - (2 * (((tmax - r) * (d * q) : ℕ) : ℝ) + 1)) := by
      have hmcast : (m : ℝ) = (d : ℝ) * ((2 ^ k : ℕ) : ℝ) * (q : ℝ) := by
        dsimp [m]; push_cast; ring
      field_simp [hqR, h2m_ne]
      rw [hmcast]
      push_cast
      ring
    rw [h1]
    have hnat : p' * 2 ^ k ≤ (tmax - r) * q + (r + 1) * q := by
      have : (tmax - r) * q + (r + 1) * q = (tmax + 1) * q := by
        rw [← Nat.add_mul]; congr 1; omega
      omega
    have hnatR : ((p' * 2 ^ k : ℕ) : ℝ) ≤ (((tmax - r) * q : ℕ) : ℝ) + (((r + 1) * q : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hdK_R : (d : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast (show d ≤ K + 1 by omega)
    have hdiff_le : 2 * (d : ℝ) * ((p' * 2 ^ k : ℕ) : ℝ) -
        (2 * (((tmax - r) * (d * q) : ℕ) : ℝ) + 1) ≤
        2 * (d : ℝ) * (q : ℝ) * ((r : ℝ) + 1) := by
      push_cast at hnatR ⊢
      nlinarith [hdR, hqR]
    have hstep : 2 * (d : ℝ) * (q : ℝ) * ((r : ℝ) + 1) ≤
        2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * ((r : ℝ) + 1) := by
      gcongr
    nlinarith [Real.pi_pos]
  have hlow := abs_chebWeight_ge hmpos hp1 hpq hcos i hlo hhi
  have hpos_lhs : 0 < 2 * (m : ℝ) * (Real.pi * p' / q - chebAngle m i) := by
    have : 0 < Real.pi * p' / q - chebAngle m i := by linarith
    positivity
  have hinv : 1 / (2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi * ((r : ℝ) + 1)) ≤
      1 / (2 * (m : ℝ) * (Real.pi * p' / q - chebAngle m i)) :=
    one_div_le_one_div_of_le hpos_lhs hgap
  have hrew : (1 : ℝ) / (2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) * (1 / ((r : ℝ) + 1)) =
      1 / (2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi * ((r : ℝ) + 1)) := by
    rw [div_mul_div_comm, one_mul]
  rw [hrew]
  exact hinv.trans hlow

private lemma prim_lebesgue_ge {p' q : ℕ} (_hp' : Odd p') (hq : Odd q)
    (hp1 : 1 ≤ p') (hpq : p' ≤ q) (M_min K : ℕ) (B : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ M_min < 2 ^ k * q ∧ ∀ d : ℕ, Odd d → d ≤ K →
      B ≤ ∑ i ∈ Finset.univ.filter (IsPrim (d * (2 ^ k * q))),
        |chebWeight (d * (2 ^ k * q)) i (Real.pi * p' / q)| := by
  have hqpos : 0 < q := hq.pos
  have htend := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop
    (max 1 (B * (2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi))))
  set k := max (max 1 M_min) (4 * q * (R + 2))
  have hk : 1 ≤ k ∧ M_min < 2 ^ k * q ∧ 4 * q * (R + 2) ≤ 2 ^ k := by
    have hk1 : 1 ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
    have hMle : M_min ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
    have hRle : 4 * q * (R + 2) ≤ k := le_max_right _ _
    have hlt : k < 2 ^ k := Nat.lt_two_pow_self
    have hmul : 2 ^ k ≤ 2 ^ k * q := Nat.le_mul_of_pos_right _ hqpos
    exact ⟨hk1, by omega, by omega⟩
  refine ⟨k, hk.1, hk.2.1, fun d hd hdK => ?_⟩
  set m := d * (2 ^ k * q)
  have hdpos : 0 < d := hd.pos
  have hmpos : 0 < m := by dsimp [m]; positivity
  set tmax := (p' * 2 ^ k - 1) / q
  have htmax_hi : tmax * q ≤ p' * 2 ^ k - 1 := Nat.div_mul_le_self _ _
  have hp2k_pos : 1 ≤ p' * 2 ^ k := by
    have : 1 * 1 ≤ p' * 2 ^ k := Nat.mul_le_mul hp1 (Nat.one_le_two_pow)
    simpa using this
  have hR_le_tmax : R ≤ tmax := by
    have h1 : (R + 1) * q ≤ p' * 2 ^ k - 1 := by
      have h2 : 4 * q * (R + 2) ≤ 2 ^ k := hk.2.2
      have h3 : 2 ^ k ≤ p' * 2 ^ k := Nat.le_mul_of_pos_left _ hp1
      have h4 : (R + 1) * q + 1 ≤ 4 * q * (R + 2) := by nlinarith
      omega
    have h2 : R + 1 ≤ tmax := (Nat.le_div_iff_mul_le hqpos).mpr h1
    omega
  have hi_lt (r : ℕ) (_hr : r < R) : (tmax - r) * (d * q) < m := by
    have h1 : (tmax - r) * q ≤ tmax * q := Nat.mul_le_mul_right q (Nat.sub_le _ _)
    have h2 : tmax * q < q * 2 ^ k := by
      have : p' * 2 ^ k ≤ q * 2 ^ k := Nat.mul_le_mul_right _ hpq
      omega
    have h3 : (tmax - r) * (d * q) = d * ((tmax - r) * q) := by ring
    have h4 : m = d * (q * 2 ^ k) := by dsimp [m]; ring
    rw [h3, h4]
    exact Nat.mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 h2) hdpos
  let f : ℕ → Fin m := fun r =>
    if hr : r < R then ⟨(tmax - r) * (d * q), hi_lt r hr⟩ else ⟨0, hmpos⟩
  have hf_mem : ∀ r ∈ Finset.range R, f r ∈ Finset.univ.filter (IsPrim m) := by
    intro r hr
    have hr' : r < R := Finset.mem_range.mp hr
    simp only [f, dif_pos hr', Finset.mem_filter, Finset.mem_univ, true_and, IsPrim, m]
    exact coprime_two_mul_mul_add_one (tmax - r) d k q
  have hf_inj : Set.InjOn f (Finset.range R : Set ℕ) := by
    intro r1 hr1 r2 hr2 heq
    have hr1' : r1 < R := Finset.mem_range.mp hr1
    have hr2' : r2 < R := Finset.mem_range.mp hr2
    simp only [f, dif_pos hr1', dif_pos hr2', Fin.mk.injEq] at heq
    have hdqpos : 0 < d * q := Nat.mul_pos hdpos hqpos
    have hsub : tmax - r1 = tmax - r2 := Nat.eq_of_mul_eq_mul_right hdqpos heq
    omega
  have hsum_ge : ∑ r ∈ Finset.range R, |chebWeight m (f r) (Real.pi * p' / q)| ≤
      ∑ i ∈ Finset.univ.filter (IsPrim m), |chebWeight m i (Real.pi * p' / q)| := by
    have himg_sum : ∑ i ∈ (Finset.range R).image f, |chebWeight m i (Real.pi * p' / q)| =
        ∑ r ∈ Finset.range R, |chebWeight m (f r) (Real.pi * p' / q)| :=
      Finset.sum_image (f := fun i => |chebWeight m i (Real.pi * p' / q)|)
        (fun a ha b hb h => hf_inj ha hb h)
    rw [← himg_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr hf_mem) (fun _ _ _ => abs_nonneg _)
  have hterm_ge : ∀ r ∈ Finset.range R,
      (1 : ℝ) / (2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) * (1 / ((r : ℝ) + 1)) ≤
        |chebWeight m (f r) (Real.pi * p' / q)| := by
    intro r hr
    have hr' : r < R := Finset.mem_range.mp hr
    exact prim_lebesgue_term_ge hqpos hp1 hpq hk.1 hk.2.2 hdpos hdK hr' (f r)
      (by simp [f, dif_pos hr', tmax])
  calc B ≤ (1 : ℝ) / (2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) *
          (∑ r ∈ Finset.range R, (1 : ℝ) / ((r : ℝ) + 1)) := by
        have hR' := hR R le_rfl
        have hmax : B * (2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) ≤
            ∑ r ∈ Finset.range R, (1 : ℝ) / ((r : ℝ) + 1) :=
          (le_max_right _ _).trans hR'
        have hposC : 0 < 2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi := by positivity
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hposC]
        exact hmax
    _ = ∑ r ∈ Finset.range R,
          (1 : ℝ) / (2 * ((K + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) * (1 / ((r : ℝ) + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ Finset.range R, |chebWeight m (f r) (Real.pi * p' / q)| :=
        Finset.sum_le_sum hterm_ge
    _ ≤ ∑ i ∈ Finset.univ.filter (IsPrim m), |chebWeight m i (Real.pi * p' / q)| := hsum_ge

/-! ### Section 4: Width-independent total-variation tail bound for a tent function -/

private noncomputable def tent (c r x : ℝ) : ℝ :=
  max 0 (1 - |x - c| / r)

private lemma tent_continuous (c r : ℝ) : Continuous (tent c r) := by
  unfold tent
  fun_prop

private lemma tent_self {c r : ℝ} (_hr : 0 < r) : tent c r c = 1 := by
  simp [tent]

private lemma tent_nonneg (c r x : ℝ) : 0 ≤ tent c r x := le_max_left _ _

private lemma tent_le_one {c r : ℝ} (hr : 0 < r) (x : ℝ) : tent c r x ≤ 1 := by
  unfold tent
  apply max_le (by norm_num)
  have : 0 ≤ |x - c| / r := div_nonneg (abs_nonneg _) hr.le
  linarith

private lemma tent_eq_zero_of_le {c r x : ℝ} (hr : 0 < r) (h : r ≤ |x - c|) :
    tent c r x = 0 := by
  unfold tent
  apply max_eq_left
  have : 1 ≤ |x - c| / r := (one_le_div hr).mpr h
  linarith

private lemma abs_sub_lt_of_tent_ne_zero {c r x : ℝ} (hr : 0 < r) (h : tent c r x ≠ 0) :
    |x - c| < r := by
  by_contra! hge
  exact h (tent_eq_zero_of_le hr hge)

private lemma tent_mono_le {c r x y : ℝ} (hr : 0 < r) (hxy : x ≤ y) (hyc : y ≤ c) :
    tent c r x ≤ tent c r y := by
  unfold tent
  apply max_le_max_left
  have h1 : |y - c| = c - y := by rw [abs_of_nonpos (by linarith)]; ring
  have h2 : |x - c| = c - x := by rw [abs_of_nonpos (by linarith)]; ring
  rw [h1, h2]
  have : (c - y) / r ≤ (c - x) / r := div_le_div_of_nonneg_right (by linarith) hr.le
  linarith

private lemma tent_anti_ge {c r x y : ℝ} (hr : 0 < r) (hcx : c ≤ x) (hxy : x ≤ y) :
    tent c r y ≤ tent c r x := by
  unfold tent
  apply max_le_max_left
  have h1 : |y - c| = y - c := abs_of_nonneg (by linarith)
  have h2 : |x - c| = x - c := abs_of_nonneg (by linarith)
  rw [h1, h2]
  have : (x - c) / r ≤ (y - c) / r := div_le_div_of_nonneg_right (by linarith) hr.le
  linarith

private lemma abs_alternating_sum_range_le (b : ℕ → ℝ) (m : ℕ) (B : ℝ)
    (hB : ∀ i < m, |b i| ≤ B) (hB0 : 0 ≤ B) :
    |∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * b i| ≤
      B + ∑ i ∈ Finset.range (m - 1), |b i - b (i + 1)| := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- m = k + k
    subst hk
    have hev : ∑ i ∈ Finset.range (k + k), (-1 : ℝ) ^ i * b i =
        ∑ j ∈ Finset.range k, (b (2 * j) - b (2 * j + 1)) := by
      clear hB
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show k + 1 + (k + 1) = (k + k) + 1 + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
        have h1 : (-1 : ℝ) ^ (k + k) = 1 := by
          rw [← two_mul, pow_mul]; norm_num
        have h2 : (-1 : ℝ) ^ (k + k + 1) = -1 := by
          rw [pow_succ, h1]; ring
        rw [h1, h2, show k + k = 2 * k by omega]
        ring
    rw [hev]
    have htri := Finset.abs_sum_le_sum_abs (fun j => b (2 * j) - b (2 * j + 1)) (Finset.range k)
    have hsub : ∑ j ∈ Finset.range k, |b (2 * j) - b (2 * j + 1)| ≤
        ∑ i ∈ Finset.range (k + k - 1), |b i - b (i + 1)| := by
      have hinj : Set.InjOn (fun j => 2 * j) (Finset.range k : Set ℕ) :=
        fun a _ b _ h => by dsimp at h; omega
      rw [← Finset.sum_image hinj (f := fun i => |b i - b (i + 1)|)]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        have hj' := Finset.mem_range.mp hj
        exact Finset.mem_range.mpr (by omega)
      · intro _ _ _; exact abs_nonneg _
    linarith
  · -- m = 2 * k + 1
    subst hk
    have hodd : ∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * b i =
        (∑ j ∈ Finset.range k, (b (2 * j) - b (2 * j + 1))) + b (2 * k) := by
      clear hB
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
        have h1 : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
          rw [pow_succ, pow_mul]; norm_num
        have h2 : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := by
          rw [pow_succ, h1]; ring
        rw [h1, h2, show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
        ring
    rw [hodd]
    have h1 := abs_add_le (∑ j ∈ Finset.range k, (b (2 * j) - b (2 * j + 1))) (b (2 * k))
    have h2 := Finset.abs_sum_le_sum_abs (fun j => b (2 * j) - b (2 * j + 1)) (Finset.range k)
    have h3 : |b (2 * k)| ≤ B := hB (2 * k) (by omega)
    have hsub : ∑ j ∈ Finset.range k, |b (2 * j) - b (2 * j + 1)| ≤
        ∑ i ∈ Finset.range (2 * k + 1 - 1), |b i - b (i + 1)| := by
      have hinj : Set.InjOn (fun j => 2 * j) (Finset.range k : Set ℕ) :=
        fun a _ b _ h => by dsimp at h; omega
      rw [← Finset.sum_image hinj (f := fun i => |b i - b (i + 1)|)]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        have hj' := Finset.mem_range.mp hj
        exact Finset.mem_range.mpr (by omega)
      · intro _ _ _; exact abs_nonneg _
    linarith

private lemma sum_abs_sub_monotone (y : ℕ → ℝ) (m : ℕ) (h0 : ∀ i, 0 ≤ y i) (h1 : ∀ i, y i ≤ 1)
    (hmono : ∀ i < m, y i ≤ y (i + 1)) :
    ∑ i ∈ Finset.range m, |y i - y (i + 1)| ≤ 1 := by
  have heq : ∑ i ∈ Finset.range m, |y i - y (i + 1)| =
      ∑ i ∈ Finset.range m, (y (i + 1) - y i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hle := hmono i (Finset.mem_range.mp hi)
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [heq, Finset.sum_range_sub y m]
  linarith [h0 0, h1 m]

private lemma sum_abs_sub_antitone (y : ℕ → ℝ) (m : ℕ) (h0 : ∀ i, 0 ≤ y i) (h1 : ∀ i, y i ≤ 1)
    (hanti : ∀ i < m, y (i + 1) ≤ y i) :
    ∑ i ∈ Finset.range m, |y i - y (i + 1)| ≤ 1 := by
  have heq : ∑ i ∈ Finset.range m, |y i - y (i + 1)| =
      ∑ i ∈ Finset.range m, (y i - y (i + 1)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hle := hanti i (Finset.mem_range.mp hi)
    exact abs_of_nonneg (by linarith)
  rw [heq]
  have htel : ∑ i ∈ Finset.range m, (y i - y (i + 1)) = y 0 - y m := by
    have := Finset.sum_range_sub (fun i => -y i) m
    simpa [sub_eq_add_neg, add_comm] using this
  rw [htel]
  linarith [h0 m, h1 0]

private lemma sum_abs_sub_unimodal (y : ℕ → ℝ) (m k : ℕ) (hk : k ≤ m)
    (h0 : ∀ i, 0 ≤ y i) (h1 : ∀ i, y i ≤ 1)
    (hinc : ∀ i < k, y i ≤ y (i + 1))
    (hdec : ∀ i, k < i → i < m → y (i + 1) ≤ y i) :
    ∑ i ∈ Finset.range m, |y i - y (i + 1)| ≤ 3 := by
  by_cases hkm : k = m
  · subst hkm
    exact (sum_abs_sub_monotone y k h0 h1 hinc).trans (by norm_num)
  · have hlt : k < m := lt_of_le_of_ne hk hkm
    -- Split range m into range k, {k}, and Ico (k+1) m
    have hsplit1 : ∑ i ∈ Finset.range m, |y i - y (i + 1)| =
        (∑ i ∈ Finset.range (k + 1), |y i - y (i + 1)|) +
          ∑ i ∈ Finset.Ico (k + 1) m, |y i - y (i + 1)| := by
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ m)]
    rw [hsplit1, Finset.sum_range_succ]
    have hpart1 : ∑ i ∈ Finset.range k, |y i - y (i + 1)| ≤ 1 :=
      sum_abs_sub_monotone y k h0 h1 hinc
    have hmid : |y k - y (k + 1)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [h0 k, h1 k, h0 (k + 1), h1 (k + 1)]
    have hpart2 : ∑ i ∈ Finset.Ico (k + 1) m, |y i - y (i + 1)| ≤ 1 := by
      have hshift : ∑ i ∈ Finset.Ico (k + 1) m, |y i - y (i + 1)| =
          ∑ j ∈ Finset.range (m - (k + 1)), |y (k + 1 + j) - y (k + 1 + j + 1)| := by
        rw [Finset.sum_Ico_eq_sum_range]
      rw [hshift]
      apply sum_abs_sub_antitone (fun j => y (k + 1 + j)) (m - (k + 1))
        (fun j => h0 _) (fun j => h1 _)
      intro j hj
      have hj' : k + 1 + j < m := by omega
      have hgt : k < k + 1 + j := by omega
      simpa only [show k + 1 + (j + 1) = k + 1 + j + 1 by omega] using hdec (k + 1 + j) hgt hj'
    linarith

private lemma tent_tv_bound {c r : ℝ} (hr : 0 < r) {θ₀ : ℝ}
    (hδ : 2 * r ≤ |Real.cos θ₀ - c|)
    {m : ℕ} (hm : 0 < m)
    (hne : ∀ j : Fin m, Real.cos θ₀ ≠ chebNode m j) :
    |(chebInterp (tent c r) m).eval (Real.cos θ₀)| ≤
      (1 / (m : ℝ)) * (8 / |Real.cos θ₀ - c| + 12 * Real.pi / |Real.cos θ₀ - c| ^ 2) := by
  set δ := |Real.cos θ₀ - c|
  have hδpos : 0 < δ := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [eval_chebInterp_eq_sum (tent c r) m hm θ₀ hne]
  let θ : ℕ → ℝ := fun i => (2 * (i : ℝ) + 1) * Real.pi / (2 * m)
  let u : ℝ → ℝ := fun t => Real.sin t / (Real.cos θ₀ - Real.cos t)
  let y : ℕ → ℝ := fun i => tent c r (Real.cos (θ i))
  let b : ℕ → ℝ := fun i => u (θ i) * y i
  have hsum_eq : ∑ i : Fin m, chebWeight m i θ₀ * tent c r (chebNode m i) =
      (Real.cos (m * θ₀) / m) * ∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * b i := by
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsub : Real.cos θ₀ - Real.cos (θ i.val) ≠ 0 := sub_ne_zero.mpr (hne i)
    dsimp [chebWeight, chebNode, chebAngle, b, u, y, θ]
    field_simp [hmR.ne', hsub]
  rw [hsum_eq, abs_mul, abs_div, abs_of_pos hmR]
  have hcos_le : |Real.cos (m * θ₀)| ≤ 1 := Real.abs_cos_le_one _
  -- Bound |u (θ i)| ≤ 2 / δ whenever y i ≠ 0
  have hu_le : ∀ i, y i ≠ 0 → |u (θ i)| ≤ 2 / δ := by
    intro i hy
    have hlt : |Real.cos (θ i) - c| < r := abs_sub_lt_of_tent_ne_zero hr hy
    have hden : δ / 2 ≤ |Real.cos θ₀ - Real.cos (θ i)| := by
      have htri : |Real.cos θ₀ - c| ≤ |Real.cos θ₀ - Real.cos (θ i)| + |Real.cos (θ i) - c| := by
        simpa [sub_add_sub_cancel] using abs_add_le (Real.cos θ₀ - Real.cos (θ i)) (Real.cos (θ i) - c)
      linarith
    dsimp [u]
    rw [abs_div]
    calc |Real.sin (θ i)| / |Real.cos θ₀ - Real.cos (θ i)|
        ≤ 1 / (δ / 2) := by
          apply div_le_div₀ (by norm_num) (Real.abs_sin_le_one _) (by positivity) hden
      _ = 2 / δ := by field_simp
  -- Bound |b i| ≤ 2 / δ for all i
  have hb_le : ∀ i, |b i| ≤ 2 / δ := by
    intro i
    by_cases hy : y i = 0
    · simp [b, hy]; positivity
    · rw [show b i = u (θ i) * y i from rfl, abs_mul]
      have hy0 : 0 ≤ y i := tent_nonneg _ _ _
      have hy1 : y i ≤ 1 := tent_le_one hr _
      rw [abs_of_nonneg hy0]
      calc |u (θ i)| * y i ≤ (2 / δ) * 1 := mul_le_mul (hu_le i hy) hy1 hy0 (by positivity)
        _ = 2 / δ := mul_one _
  -- Bound |u (θ i) - u (θ (i + 1))| ≤ 12 / δ^2 * (θ (i + 1) - θ i) when both y i ≠ 0 and y (i+1) ≠ 0
  have hu_lip : ∀ i, y i ≠ 0 → y (i + 1) ≠ 0 →
      |u (θ i) - u (θ (i + 1))| ≤ (12 / δ ^ 2) * (θ (i + 1) - θ i) := by
    intro i hy1 hy2
    have hden1 : δ / 2 ≤ |Real.cos θ₀ - Real.cos (θ i)| := by
      have hlt := abs_sub_lt_of_tent_ne_zero hr hy1
      have htri : |Real.cos θ₀ - c| ≤ |Real.cos θ₀ - Real.cos (θ i)| + |Real.cos (θ i) - c| := by
        simpa [sub_add_sub_cancel] using abs_add_le (Real.cos θ₀ - Real.cos (θ i)) (Real.cos (θ i) - c)
      linarith
    have hden2 : δ / 2 ≤ |Real.cos θ₀ - Real.cos (θ (i + 1))| := by
      have hlt := abs_sub_lt_of_tent_ne_zero hr hy2
      have htri : |Real.cos θ₀ - c| ≤ |Real.cos θ₀ - Real.cos (θ (i + 1))| + |Real.cos (θ (i + 1)) - c| := by
        simpa [sub_add_sub_cancel] using abs_add_le (Real.cos θ₀ - Real.cos (θ (i + 1))) (Real.cos (θ (i + 1)) - c)
      linarith
    have hne1 : Real.cos θ₀ - Real.cos (θ i) ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le (by positivity) hden1)
    have hne2 : Real.cos θ₀ - Real.cos (θ (i + 1)) ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le (by positivity) hden2)
    have hθ_inc : θ i ≤ θ (i + 1) := by
      dsimp [θ]; push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [Real.pi_pos]
    have hsin_lip : |Real.sin (θ i) - Real.sin (θ (i + 1))| ≤ θ (i + 1) - θ i := by
      calc |Real.sin (θ i) - Real.sin (θ (i + 1))|
          ≤ |θ i - θ (i + 1)| := Real.abs_sin_sub_sin_le (θ i) (θ (i + 1))
        _ = θ (i + 1) - θ i := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have hcos_lip : |Real.cos (θ i) - Real.cos (θ (i + 1))| ≤ θ (i + 1) - θ i := by
      calc |Real.cos (θ i) - Real.cos (θ (i + 1))|
          ≤ |θ i - θ (i + 1)| := Real.abs_cos_sub_cos_le (θ i) (θ (i + 1))
        _ = θ (i + 1) - θ i := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have hsub_eq : u (θ i) - u (θ (i + 1)) =
        ((Real.sin (θ i) - Real.sin (θ (i + 1))) * (Real.cos θ₀ - Real.cos (θ (i + 1))) +
          Real.sin (θ (i + 1)) * (Real.cos (θ i) - Real.cos (θ (i + 1)))) /
          ((Real.cos θ₀ - Real.cos (θ i)) * (Real.cos θ₀ - Real.cos (θ (i + 1)))) := by
      dsimp [u]
      field_simp [hne1, hne2]
      ring
    rw [hsub_eq, abs_div, abs_mul]
    have hnum : |(Real.sin (θ i) - Real.sin (θ (i + 1))) * (Real.cos θ₀ - Real.cos (θ (i + 1))) +
        Real.sin (θ (i + 1)) * (Real.cos (θ i) - Real.cos (θ (i + 1)))| ≤
        3 * (θ (i + 1) - θ i) := by
      calc _ ≤ |(Real.sin (θ i) - Real.sin (θ (i + 1))) * (Real.cos θ₀ - Real.cos (θ (i + 1)))| +
              |Real.sin (θ (i + 1)) * (Real.cos (θ i) - Real.cos (θ (i + 1)))| := abs_add_le _ _
        _ = |Real.sin (θ i) - Real.sin (θ (i + 1))| * |Real.cos θ₀ - Real.cos (θ (i + 1))| +
              |Real.sin (θ (i + 1))| * |Real.cos (θ i) - Real.cos (θ (i + 1))| := by
            rw [abs_mul, abs_mul]
        _ ≤ (θ (i + 1) - θ i) * 2 + 1 * (θ (i + 1) - θ i) := by
            have hc2 : |Real.cos θ₀ - Real.cos (θ (i + 1))| ≤ 2 := by
              calc |Real.cos θ₀ - Real.cos (θ (i + 1))|
                  ≤ |Real.cos θ₀| + |Real.cos (θ (i + 1))| := abs_sub _ _
                _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
                _ = 2 := by norm_num
            exact add_le_add
              (mul_le_mul hsin_lip hc2 (abs_nonneg _) (by linarith))
              (mul_le_mul (Real.abs_sin_le_one _) hcos_lip (abs_nonneg _) (by norm_num))
        _ = 3 * (θ (i + 1) - θ i) := by ring
    have hden_prod : δ ^ 2 / 4 ≤ |Real.cos θ₀ - Real.cos (θ i)| * |Real.cos θ₀ - Real.cos (θ (i + 1))| := by
      calc δ ^ 2 / 4 = (δ / 2) * (δ / 2) := by ring
        _ ≤ _ := mul_le_mul hden1 hden2 (by positivity) (by positivity)
    calc _ ≤ (3 * (θ (i + 1) - θ i)) / (δ ^ 2 / 4) :=
          div_le_div₀ (by linarith) hnum (by positivity) hden_prod
      _ = (12 / δ ^ 2) * (θ (i + 1) - θ i) := by field_simp; ring
  -- Pointwise difference bound for b i - b (i + 1)
  have hstep : ∀ i, |b i - b (i + 1)| ≤
      (2 / δ) * |y i - y (i + 1)| + (12 / δ ^ 2) * (θ (i + 1) - θ i) := by
    intro i
    have hθ_inc : 0 ≤ θ (i + 1) - θ i := by
      dsimp [θ]; push_cast
      have : (2 * (i : ℝ) + 1) * Real.pi / (2 * m) ≤ (2 * ((i : ℝ) + 1) + 1) * Real.pi / (2 * m) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [Real.pi_pos]
      linarith
    by_cases hy1 : y i = 0
    · by_cases hy2 : y (i + 1) = 0
      · simp only [b, hy1, hy2, mul_zero, sub_self, abs_zero, zero_add]
        positivity
      · simp only [b, hy1, mul_zero, zero_sub, abs_neg, abs_mul]
        have hy2pos : 0 ≤ y (i + 1) := tent_nonneg _ _ _
        rw [abs_of_nonneg hy2pos]
        have h1 : |u (θ (i + 1))| * y (i + 1) ≤ (2 / δ) * y (i + 1) :=
          mul_le_mul_of_nonneg_right (hu_le (i + 1) hy2) hy2pos
        linarith [show 0 ≤ (12 / δ ^ 2) * (θ (i + 1) - θ i) by positivity]
    · by_cases hy2 : y (i + 1) = 0
      · simp only [b, hy2, mul_zero, sub_zero, abs_mul]
        have hy1pos : 0 ≤ y i := tent_nonneg _ _ _
        rw [abs_of_nonneg hy1pos]
        have h1 : |u (θ i)| * y i ≤ (2 / δ) * y i :=
          mul_le_mul_of_nonneg_right (hu_le i hy1) hy1pos
        linarith [show 0 ≤ (12 / δ ^ 2) * (θ (i + 1) - θ i) by positivity]
      · have hsplit : b i - b (i + 1) =
            u (θ i) * (y i - y (i + 1)) + (u (θ i) - u (θ (i + 1))) * y (i + 1) := by
          dsimp [b]; ring
        rw [hsplit]
        have hy20 : 0 ≤ y (i + 1) := tent_nonneg _ _ _
        have hy21 : y (i + 1) ≤ 1 := tent_le_one hr _
        calc _ ≤ |u (θ i) * (y i - y (i + 1))| + |(u (θ i) - u (θ (i + 1))) * y (i + 1)| := abs_add_le _ _
          _ = |u (θ i)| * |y i - y (i + 1)| + |u (θ i) - u (θ (i + 1))| * y (i + 1) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hy20]
          _ ≤ (2 / δ) * |y i - y (i + 1)| + ((12 / δ ^ 2) * (θ (i + 1) - θ i)) * 1 := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right (hu_le i hy1) (abs_nonneg _))
                (mul_le_mul (hu_lip i hy1 hy2) hy21 hy20 (by positivity))
          _ = _ := by ring
  -- Bound ∑_{i < m - 1} |y i - y (i + 1)| ≤ 3 via unimodality
  have hy_tv : ∑ i ∈ Finset.range (m - 1), |y i - y (i + 1)| ≤ 3 := by
    have hcos_anti : ∀ i < m - 1, Real.cos (θ (i + 1)) ≤ Real.cos (θ i) := by
      intro i hi
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · dsimp [θ]; positivity
      · exact (chebAngle_lt_pi (⟨i + 1, by omega⟩ : Fin m)).le
      · dsimp [θ]; push_cast
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [Real.pi_pos]
    -- Let k be the number of indices i ∈ range (m - 1) with c ≤ cos (θ (i + 1))
    -- Actually easier: let k = min of {i < m | cos (θ i) < c} or m - 1
    classical
    by_cases hex : ∃ i < m - 1, Real.cos (θ (i + 1)) < c
    · set k := Nat.find hex
      have hk_spec : k < m - 1 ∧ Real.cos (θ (k + 1)) < c := Nat.find_spec hex
      apply sum_abs_sub_unimodal y (m - 1) k hk_spec.1.le
        (fun i => tent_nonneg _ _ _) (fun i => tent_le_one hr _)
      · intro i hik
        have hnot := Nat.find_min hex hik
        push Not at hnot
        have hge : c ≤ Real.cos (θ (i + 1)) := hnot (lt_trans hik hk_spec.1)
        exact tent_anti_ge hr hge (hcos_anti i (lt_trans hik hk_spec.1))
      · intro i hki him
        have hle_k : Real.cos (θ i) ≤ Real.cos (θ (k + 1)) := by
          have hk1_le : k + 1 ≤ i := hki
          have : ∀ j, k + 1 ≤ j → j < m → Real.cos (θ j) ≤ Real.cos (θ (k + 1)) := by
            intro j hj hjm
            induction j with
            | zero => omega
            | succ j ih =>
              by_cases hjeq : k + 1 = j + 1
              · rw [hjeq]
              · exact (hcos_anti j (by omega)).trans (ih (by omega) (by omega))
          exact this i hk1_le (by omega)
        exact tent_mono_le hr (hcos_anti i him) (hle_k.trans hk_spec.2.le)
    · push Not at hex
      apply (sum_abs_sub_monotone y (m - 1)
        (fun i => tent_nonneg _ _ _) (fun i => tent_le_one hr _) _).trans (by norm_num)
      intro i hi
      exact tent_anti_ge hr (hex i hi) (hcos_anti i hi)
  -- Bound ∑_{i < m - 1} (θ (i + 1) - θ i) ≤ π
  have hθ_sum : ∑ i ∈ Finset.range (m - 1), (θ (i + 1) - θ i) ≤ Real.pi := by
    rw [Finset.sum_range_sub θ (m - 1)]
    have hlo : 0 ≤ θ 0 := by dsimp [θ]; positivity
    have hhi : θ (m - 1) ≤ Real.pi := by
      have := chebAngle_lt_pi (⟨m - 1, by omega⟩ : Fin m)
      exact this.le
    linarith
  have halt := abs_alternating_sum_range_le b m (2 / δ) (fun i _ => hb_le i) (by positivity)
  have htv : ∑ i ∈ Finset.range (m - 1), |b i - b (i + 1)| ≤
      (2 / δ) * 3 + (12 / δ ^ 2) * Real.pi := by
    calc ∑ i ∈ Finset.range (m - 1), |b i - b (i + 1)|
        ≤ ∑ i ∈ Finset.range (m - 1), ((2 / δ) * |y i - y (i + 1)| + (12 / δ ^ 2) * (θ (i + 1) - θ i)) :=
          Finset.sum_le_sum (fun i _ => hstep i)
      _ = (2 / δ) * (∑ i ∈ Finset.range (m - 1), |y i - y (i + 1)|) +
          (12 / δ ^ 2) * (∑ i ∈ Finset.range (m - 1), (θ (i + 1) - θ i)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (2 / δ) * 3 + (12 / δ ^ 2) * Real.pi := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hy_tv (by positivity))
            (mul_le_mul_of_nonneg_left hθ_sum (by positivity))
  have htot : |∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * b i| ≤
      8 / δ + 12 * Real.pi / δ ^ 2 := by
    have : 2 / δ + ((2 / δ) * 3 + (12 / δ ^ 2) * Real.pi) = 8 / δ + 12 * Real.pi / δ ^ 2 := by ring
    linarith
  calc |Real.cos (↑m * θ₀)| / (m : ℝ) * |∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * b i|
      ≤ (1 / (m : ℝ)) * (8 / δ + 12 * Real.pi / δ ^ 2) := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hcos_le hmR.le
        · exact htot
        · exact abs_nonneg _
        · positivity

/-! ### Section 5: Divisor bound, Mobius cancellation, and single-stage block-spike lemma -/

private lemma card_divisors_le_two_mul_sqrt (D : ℕ) :
    (D.divisors.card : ℝ) ≤ 2 * Real.sqrt (D : ℝ) := by
  by_cases hD : D = 0
  · subst hD; simp
  have hDpos : 0 < D := Nat.pos_of_ne_zero hD
  set s := Nat.sqrt D
  have hsub : D.divisors ⊆ Finset.Icc 1 s ∪ (Finset.Icc 1 s).image (fun d => D / d) := by
    intro d hd
    have hmem := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hmem.1 hDpos
    by_cases hds : d ≤ s
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hdpos, hds⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨D / d, Finset.mem_Icc.mpr ⟨?_, ?_⟩, Nat.div_div_self hmem.1 hD⟩
      · exact Nat.div_pos (Nat.le_of_dvd hDpos hmem.1) hdpos
      · have hmul : d * (D / d) = D := Nat.mul_div_cancel' hmem.1
        have hs1 : s + 1 ≤ d := by omega
        have hsq : D < (s + 1) * (s + 1) := Nat.lt_succ_sqrt D
        have : (D / d) < s + 1 := by nlinarith
        omega
  have hcard : D.divisors.card ≤ 2 * s := by
    calc D.divisors.card
        ≤ (Finset.Icc 1 s ∪ (Finset.Icc 1 s).image (fun d => D / d)).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 s).card + ((Finset.Icc 1 s).image (fun d => D / d)).card := Finset.card_union_le _ _
      _ ≤ (Finset.Icc 1 s).card + (Finset.Icc 1 s).card := Nat.add_le_add_left Finset.card_image_le _
      _ = 2 * s := by simp [Nat.card_Icc]; omega
  have hs_le : (s : ℝ) ≤ Real.sqrt (D : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _), sq]
    exact_mod_cast Nat.sqrt_le D
  have hcardR : (D.divisors.card : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hcard
  linarith

private lemma sum_divisors_moebius_real (D : ℕ) (_hD : 0 < D) :
    ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) = if D = 1 then 1 else 0 := by
  have hZ : ∑ d ∈ D.divisors, ArithmeticFunction.moebius d = if D = 1 then 1 else 0 := by
    have h1 := congrFun (congrArg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) D
    rw [ArithmeticFunction.coe_mul_zeta_apply] at h1
    simpa [ArithmeticFunction.one_apply] using h1
  have hR : ((∑ d ∈ D.divisors, ArithmeticFunction.moebius d : ℤ) : ℝ) =
      ((if D = 1 then (1 : ℤ) else 0 : ℤ) : ℝ) := congrArg (Int.cast (R := ℝ)) hZ
  push_cast at hR
  split_ifs at hR ⊢ <;> simpa using hR

private lemma exists_pos_lt_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) : ∃ r : ℝ, 0 < r ∧ ∀ a ∈ s, r ≤ f a := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨a, ha, hmin⟩ := s.exists_min_image f hs
    exact ⟨f a, hf a ha, fun b hb => hmin b hb⟩
  · refine ⟨1, zero_lt_one, fun a ha => (hs ⟨a, ha⟩).elim⟩

private noncomputable def stageBumpFun (N : ℕ)
    (Pairs : Finset ((d : ℕ) × Fin (d * N)))
    (ht : ((d : ℕ) × Fin (d * N)) → ℝ) (r x : ℝ) : ℝ :=
  ∑ a ∈ Pairs, ht a * tent (chebNode (a.1 * N) a.2) r x

private lemma stageBumpFun_continuous (N : ℕ)
    (Pairs : Finset ((d : ℕ) × Fin (d * N)))
    (ht : ((d : ℕ) × Fin (d * N)) → ℝ) (r : ℝ) :
    Continuous (stageBumpFun N Pairs ht r) := by
  unfold stageBumpFun
  exact continuous_finsetSum Pairs fun a _ =>
    continuous_const.mul (tent_continuous (chebNode (a.1 * N) a.2) r)

private lemma exists_stage_radius (N M : ℕ) (x₀ : ℝ)
    (Pairs : Finset ((d : ℕ) × Fin (d * N)))
    (hpt_inj : Set.InjOn (fun a : (d : ℕ) × Fin (d * N) => chebNode (a.1 * N) a.2) (Pairs : Set _))
    (hpt_ne_x0 : ∀ a ∈ Pairs, x₀ ≠ chebNode (a.1 * N) a.2) :
    ∃ r : ℝ, 0 < r ∧
      (∀ a ∈ Pairs, 2 * r ≤ |x₀ - chebNode (a.1 * N) a.2|) ∧
      (∀ a ∈ Pairs, ∀ b ∈ Pairs, b ≠ a →
        2 * r ≤ |chebNode (b.1 * N) b.2 - chebNode (a.1 * N) a.2|) ∧
      (∀ n, 1 ≤ n → n ≤ M → ∀ j : Fin n, ∀ a ∈ Pairs,
        chebNode n j ≠ chebNode (a.1 * N) a.2 → r ≤ |chebNode n j - chebNode (a.1 * N) a.2|) := by
  classical
  obtain ⟨r1, hr1_pos, hr1_le⟩ := exists_pos_lt_finset Pairs
    (fun a => |x₀ - chebNode (a.1 * N) a.2| / 2)
    (fun a ha => div_pos (abs_pos.mpr (sub_ne_zero.mpr (hpt_ne_x0 a ha))) two_pos)
  let DiffPairs := (Pairs ×ˢ Pairs).filter (fun p => p.1 ≠ p.2)
  obtain ⟨r2, hr2_pos, hr2_le⟩ := exists_pos_lt_finset DiffPairs
    (fun p => |chebNode (p.1.1 * N) p.1.2 - chebNode (p.2.1 * N) p.2.2| / 2)
    (fun p hp => by
      have ⟨hprod, hne⟩ := Finset.mem_filter.mp hp
      have ⟨ha, hb⟩ := Finset.mem_product.mp hprod
      have hptne : chebNode (p.1.1 * N) p.1.2 ≠ chebNode (p.2.1 * N) p.2.2 :=
        fun h => hne (hpt_inj ha hb h)
      exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hptne)) two_pos)
  let AllNodes : Finset ((n : ℕ) × Fin n) := (Finset.Icc 1 M).sigma (fun _ => Finset.univ)
  let NonHit := (AllNodes ×ˢ Pairs).filter (fun p => chebNode p.1.1 p.1.2 ≠ chebNode (p.2.1 * N) p.2.2)
  obtain ⟨r3, hr3_pos, hr3_le⟩ := exists_pos_lt_finset NonHit
    (fun p => |chebNode p.1.1 p.1.2 - chebNode (p.2.1 * N) p.2.2|)
    (fun p hp => abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2))
  refine ⟨min r1 (min r2 r3), lt_min hr1_pos (lt_min hr2_pos hr3_pos), ?_, ?_, ?_⟩
  · intro a ha
    have h1 : min r1 (min r2 r3) ≤ |x₀ - chebNode (a.1 * N) a.2| / 2 :=
      (min_le_left _ _).trans (hr1_le a ha)
    linarith
  · intro a ha b hb hba
    have hmem : (b, a) ∈ DiffPairs :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hba⟩
    have h2 : min r1 (min r2 r3) ≤ |chebNode (b.1 * N) b.2 - chebNode (a.1 * N) a.2| / 2 :=
      ((min_le_right _ _).trans (min_le_left _ _)).trans (hr2_le (b, a) hmem)
    linarith
  · intro n hn1 hnM j a ha hne
    have hmem : ((⟨n, j⟩ : (n : ℕ) × Fin n), a) ∈ NonHit := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ha⟩, hne⟩
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnM⟩, Finset.mem_univ _⟩
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (hr3_le (⟨n, j⟩, a) hmem)

private lemma stageBumpFun_bound (N : ℕ)
    (Pairs : Finset ((d : ℕ) × Fin (d * N)))
    (ht : ((d : ℕ) × Fin (d * N)) → ℝ) {r ε : ℝ} (hr_pos : 0 < r) (hε : 0 < ε)
    (hht : ∀ a ∈ Pairs, |ht a| ≤ ε)
    (hdist2 : ∀ a ∈ Pairs, ∀ b ∈ Pairs, b ≠ a →
      2 * r ≤ |chebNode (b.1 * N) b.2 - chebNode (a.1 * N) a.2|) :
    ∀ x, |stageBumpFun N Pairs ht r x| ≤ ε := by
  intro x
  by_cases hex : ∃ a ∈ Pairs, tent (chebNode (a.1 * N) a.2) r x ≠ 0
  · obtain ⟨a, ha, hne⟩ := hex
    have huniq : ∀ b ∈ Pairs, b ≠ a → ht b * tent (chebNode (b.1 * N) b.2) r x = 0 := by
      intro b hb hba
      have hxa : |x - chebNode (a.1 * N) a.2| < r := abs_sub_lt_of_tent_ne_zero hr_pos hne
      have hdist := hdist2 a ha b hb hba
      have hxb : r ≤ |x - chebNode (b.1 * N) b.2| := by
        have htri : |chebNode (b.1 * N) b.2 - chebNode (a.1 * N) a.2| ≤
            |x - chebNode (b.1 * N) b.2| + |x - chebNode (a.1 * N) a.2| := by
          have := abs_sub_le (chebNode (b.1 * N) b.2) x (chebNode (a.1 * N) a.2)
          rwa [abs_sub_comm (chebNode (b.1 * N) b.2) x] at this
        linarith
      rw [tent_eq_zero_of_le hr_pos hxb, mul_zero]
    have hsum : stageBumpFun N Pairs ht r x = ht a * tent (chebNode (a.1 * N) a.2) r x := by
      unfold stageBumpFun
      rw [Finset.sum_eq_single a huniq (fun h => (h ha).elim)]
    rw [hsum, abs_mul, abs_of_nonneg (tent_nonneg _ _ _)]
    calc |ht a| * tent (chebNode (a.1 * N) a.2) r x ≤ ε * 1 :=
          mul_le_mul (hht a ha) (tent_le_one hr_pos _) (tent_nonneg _ _ _) hε.le
      _ = ε := mul_one ε
  · push Not at hex
    have hzero : stageBumpFun N Pairs ht r x = 0 := by
      unfold stageBumpFun
      exact Finset.sum_eq_zero fun a ha => by rw [hex a ha, mul_zero]
    rw [hzero, abs_zero]
    exact hε.le

private lemma stageBumpFun_at_node (N M : ℕ)
    (Pairs : Finset ((d : ℕ) × Fin (d * N)))
    (ht : ((d : ℕ) × Fin (d * N)) → ℝ) {r : ℝ} (hr_pos : 0 < r)
    (hsep : ∀ n, 1 ≤ n → n ≤ M → ∀ j : Fin n, ∀ a ∈ Pairs,
      chebNode n j ≠ chebNode (a.1 * N) a.2 → r ≤ |chebNode n j - chebNode (a.1 * N) a.2|)
    (n : ℕ) (hn1 : 1 ≤ n) (hnM : n ≤ M) (j : Fin n)
    (hnone : ∀ a ∈ Pairs, chebNode n j ≠ chebNode (a.1 * N) a.2) :
    stageBumpFun N Pairs ht r (chebNode n j) = 0 := by
  unfold stageBumpFun
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [tent_eq_zero_of_le hr_pos (hsep n hn1 hnM j a ha (hnone a ha)), mul_zero]

private lemma stageBumpFun_at_pair (N M : ℕ)
    (Pairs : Finset ((d : ℕ) × Fin (d * N)))
    (ht : ((d : ℕ) × Fin (d * N)) → ℝ) {r : ℝ} (hr_pos : 0 < r)
    (hpt_inj : Set.InjOn (fun a : (d : ℕ) × Fin (d * N) => chebNode (a.1 * N) a.2) (Pairs : Set _))
    (hsep : ∀ n, 1 ≤ n → n ≤ M → ∀ j : Fin n, ∀ a ∈ Pairs,
      chebNode n j ≠ chebNode (a.1 * N) a.2 → r ≤ |chebNode n j - chebNode (a.1 * N) a.2|)
    (n : ℕ) (hn1 : 1 ≤ n) (hnM : n ≤ M) (j : Fin n) (a : (d : ℕ) × Fin (d * N))
    (ha : a ∈ Pairs) (heq : chebNode n j = chebNode (a.1 * N) a.2) :
    stageBumpFun N Pairs ht r (chebNode n j) = ht a := by
  unfold stageBumpFun
  rw [Finset.sum_eq_single a]
  · rw [heq, tent_self hr_pos, mul_one]
  · intro b hb hba
    have hne : chebNode n j ≠ chebNode (b.1 * N) b.2 := by
      rw [heq]; exact fun h => hba (hpt_inj hb ha h.symm)
    rw [tent_eq_zero_of_le hr_pos (hsep n hn1 hnM j b hb hne), mul_zero]
  · intro h; exact (h ha).elim

private lemma stageBumpFun_eval_exact {p' q : ℕ} (hp' : Odd p') (hq : Odd q)
    (hp1 : 1 ≤ p') (hpq : p' ≤ q)
    (N M : ℕ) (Pairs : Finset ((d : ℕ) × Fin (d * N)))
    (ht : ((d : ℕ) × Fin (d * N)) → ℝ) {r : ℝ} (hr_pos : 0 < r)
    (hpt_inj : Set.InjOn (fun a : (d : ℕ) × Fin (d * N) => chebNode (a.1 * N) a.2) (Pairs : Set _))
    (hsep : ∀ n, 1 ≤ n → n ≤ M → ∀ j : Fin n, ∀ a ∈ Pairs,
      chebNode n j ≠ chebNode (a.1 * N) a.2 → r ≤ |chebNode n j - chebNode (a.1 * N) a.2|)
    (n : ℕ) (hn1 : 1 ≤ n) (hnM : n ≤ M) :
    (chebInterp (stageBumpFun N Pairs ht r) n).eval (Real.cos (Real.pi * p' / q)) =
      ∑ a ∈ Pairs, if h : ∃ j : Fin n, chebNode n j = chebNode (a.1 * N) a.2 then
        chebWeight n h.choose (Real.pi * p' / q) * ht a else 0 := by
  classical
  set θ₀ := Real.pi * p' / q
  have hne_x0 : ∀ j : Fin n, Real.cos θ₀ ≠ chebNode n j :=
    fun j => chebNode_ne_cos_odd n j hp' hq hp1 hpq
  rw [eval_chebInterp_eq_sum (stageBumpFun N Pairs ht r) n hn1 θ₀ hne_x0]
  have hpart : ∑ j : Fin n, chebWeight n j θ₀ * stageBumpFun N Pairs ht r (chebNode n j) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => ∃ a ∈ Pairs, chebNode n j = chebNode (a.1 * N) a.2),
        chebWeight n j θ₀ * stageBumpFun N Pairs ht r (chebNode n j) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hnot
    rw [Finset.mem_filter] at hnot
    push Not at hnot
    rw [stageBumpFun_at_node N M Pairs ht hr_pos hsep n hn1 hnM j (hnot (Finset.mem_univ j)), mul_zero]
  rw [hpart]
  have hpart2 : (∑ a ∈ Pairs, if h : ∃ j : Fin n, chebNode n j = chebNode (a.1 * N) a.2 then
        chebWeight n h.choose θ₀ * ht a else 0) =
      ∑ a ∈ Pairs.filter (fun a => ∃ j : Fin n, chebNode n j = chebNode (a.1 * N) a.2),
        if h : ∃ j : Fin n, chebNode n j = chebNode (a.1 * N) a.2 then
          chebWeight n h.choose θ₀ * ht a else 0 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hnot
    rw [Finset.mem_filter] at hnot
    have hno : ¬ ∃ j : Fin n, chebNode n j = chebNode (a.1 * N) a.2 := fun h => hnot ⟨ha, h⟩
    simp [hno]
  rw [hpart2]
  refine Finset.sum_bij'
    (fun j hj => (Finset.mem_filter.mp hj).2.choose)
    (fun a ha => (Finset.mem_filter.mp ha).2.choose)
    ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hspec := (Finset.mem_filter.mp hj).2.choose_spec
    exact Finset.mem_filter.mpr ⟨hspec.1, ⟨j, hspec.2⟩⟩
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, ha'.1, ha'.2.choose_spec⟩⟩
  · intro j hj
    have hspec := (Finset.mem_filter.mp hj).2.choose_spec
    set a := (Finset.mem_filter.mp hj).2.choose
    have ha_hit : ∃ j' : Fin n, chebNode n j' = chebNode (a.1 * N) a.2 := ⟨j, hspec.2⟩
    exact chebNode_injective n (ha_hit.choose_spec.trans hspec.2.symm)
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    set j := ha'.2.choose
    have hj_spec := ha'.2.choose_spec
    have hj_hit : ∃ a' ∈ Pairs, chebNode n j = chebNode (a'.1 * N) a'.2 := ⟨a, ha'.1, hj_spec⟩
    have hspec := hj_hit.choose_spec
    exact hpt_inj hspec.1 ha'.1 (hspec.2.symm.trans hj_spec)
  · intro j hj
    have hspec := (Finset.mem_filter.mp hj).2.choose_spec
    set a := (Finset.mem_filter.mp hj).2.choose
    have ha_hit : ∃ j' : Fin n, chebNode n j' = chebNode (a.1 * N) a.2 := ⟨j, hspec.2⟩
    rw [dif_pos ha_hit]
    have hj_eq : ha_hit.choose = j := chebNode_injective n (ha_hit.choose_spec.trans hspec.2.symm)
    rw [hj_eq, stageBumpFun_at_pair N M Pairs ht hr_pos hpt_inj hsep n hn1 hnM j a hspec.1 hspec.2]

private lemma stageBumpFun_eval_odd_mul {p' q k K : ℕ} (hq : Odd q) (hk1 : 1 ≤ k)
    (v : ℝ) (coeff : (d : ℕ) → Fin (d * (2 ^ k * q)) → ℝ)
    (hcoeff_sum : ∀ d ∈ (Finset.Icc 1 K).filter Odd,
      ∑ i ∈ Finset.univ.filter (IsPrim (d * (2 ^ k * q))),
        chebWeight (d * (2 ^ k * q)) i (Real.pi * p' / q) * coeff d i =
        (ArithmeticFunction.moebius d : ℝ) * chi4 d / d * v)
    (D : ℕ) (hDodd : Odd D) :
    (∑ a ∈ ((Finset.Icc 1 K).filter Odd).sigma
        (fun d => Finset.univ.filter (IsPrim (d * (2 ^ k * q)))),
      if h : ∃ j : Fin (D * (2 ^ k * q)), chebNode (D * (2 ^ k * q)) j = chebNode (a.1 * (2 ^ k * q)) a.2
      then chebWeight (D * (2 ^ k * q)) h.choose (Real.pi * p' / q) * coeff a.1 a.2 else 0) =
      (chi4 D / D) * v * ∑ d ∈ D.divisors.filter (· ≤ K), (ArithmeticFunction.moebius d : ℝ) := by
  classical
  let θ₀ := Real.pi * p' / q
  let N := 2 ^ k * q
  let Dset := (Finset.Icc 1 K).filter Odd
  have hqpos : 0 < q := hq.pos
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hDpos : 0 < D := hDodd.pos
  rw [Finset.sum_sigma]
  change (∑ d ∈ Dset, ∑ i ∈ Finset.univ.filter (IsPrim (d * N)),
      if h : ∃ j : Fin (D * N), chebNode (D * N) j = chebNode (d * N) i then
        chebWeight (D * N) h.choose θ₀ * coeff d i else 0) = _
  have hinner : ∀ d ∈ Dset,
      (∑ i ∈ Finset.univ.filter (IsPrim (d * N)),
        if h : ∃ j : Fin (D * N), chebNode (D * N) j = chebNode (d * N) i then
          chebWeight (D * N) h.choose θ₀ * coeff d i else 0) =
      if d ∣ D then (chi4 (D / d) / (D / d : ℕ)) *
        ((ArithmeticFunction.moebius d : ℝ) * chi4 d / d * v) else 0 := by
    intro d hd
    have hd_odd : Odd d := (Finset.mem_filter.mp hd).2
    have hd_pos : 0 < d := hd_odd.pos
    split_ifs with hdvd
    · set c := D / d
      have hcD : c * d = D := Nat.div_mul_cancel hdvd
      have hcodd : Odd c := by
        by_contra hnot
        obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hnot
        have : Even D := ⟨t * d, by rw [← hcD, ht]; ring⟩
        exact (Nat.not_even_iff_odd.mpr hDodd) this
      have hterm : ∀ i ∈ Finset.univ.filter (IsPrim (d * N)),
          (if h : ∃ j : Fin (D * N), chebNode (D * N) j = chebNode (d * N) i then
            chebWeight (D * N) h.choose θ₀ * coeff d i else 0) =
          (chi4 c / (c : ℝ)) * (chebWeight (d * N) i θ₀ * coeff d i) := by
        intro i _
        have hidx_lt : (c * (2 * i.val + 1) - 1) / 2 < D * N := by
          have h1 : 2 * i.val + 1 < 2 * (d * N) := by have := i.isLt; omega
          have h2 : c * (2 * i.val + 1) < c * (2 * (d * N)) :=
            Nat.mul_lt_mul_of_pos_left h1 hcodd.pos
          have h3 : c * (2 * (d * N)) = 2 * (D * N) := by rw [← hcD]; ring
          have h4 : c * (2 * i.val + 1) < 2 * (D * N) := h3 ▸ h2
          omega
        let j0 : Fin (D * N) := ⟨(c * (2 * i.val + 1) - 1) / 2, hidx_lt⟩
        have hj0_idx : 2 * j0.val + 1 = c * (2 * i.val + 1) := by
          have hi_odd : Odd (2 * i.val + 1) := ⟨i.val, rfl⟩
          obtain ⟨t, ht_eq⟩ := hcodd.mul hi_odd
          dsimp [j0]
          rw [ht_eq]
          omega
        have hj0_eq : chebNode (D * N) j0 = chebNode (d * N) i := by
          rw [chebNode_eq_iff, hj0_idx, ← hcD]
          ring
        have hex : ∃ j : Fin (D * N), chebNode (D * N) j = chebNode (d * N) i := ⟨j0, hj0_eq⟩
        rw [dif_pos hex]
        have hch : hex.choose = j0 := chebNode_injective (D * N) (hex.choose_spec.trans hj0_eq.symm)
        rw [hch]
        have hang : chebAngle (D * N) j0 = chebAngle (d * N) i := by
          dsimp [chebAngle]
          have h1 : (2 * (j0 : ℝ) + 1) = (c : ℝ) * (2 * (i : ℝ) + 1) := by exact_mod_cast hj0_idx
          have h2 : ((D * N : ℕ) : ℝ) = (c : ℝ) * ((d * N : ℕ) : ℝ) := by
            have : D * N = c * (d * N) := by rw [← hcD]; ring
            exact_mod_cast this
          have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hcodd.pos.ne'
          have hdNR : ((d * N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hd_pos hNpos).ne'
          rw [h1, h2]
          field_simp [hcR, hdNR]
        have hcosD : Real.cos (((D * N : ℕ) : ℝ) * θ₀) = 1 :=
          cos_mul_pow_two_mul_odd D k p' q hk1 hqpos
        have hcosd : Real.cos (((d * N : ℕ) : ℝ) * θ₀) = 1 :=
          cos_mul_pow_two_mul_odd d k p' q hk1 hqpos
        have hsign : (-1 : ℝ) ^ j0.val = chi4 c * (-1 : ℝ) ^ i.val := by
          obtain ⟨u, hu_eq⟩ := hcodd
          have hj2 : 2 * j0.val + 1 = 2 * (2 * (u * i.val) + i.val + u) + 1 := by
            rw [hj0_idx, hu_eq]; ring
          have hjval : j0.val = 2 * (u * i.val) + i.val + u := by omega
          have hu : (2 * u + 1) / 2 = u := by omega
          rw [hjval, chi4, hu_eq, hu, pow_add, pow_add, pow_mul]
          norm_num
          ring
        have hw_rel : chebWeight (D * N) j0 θ₀ = (chi4 c / (c : ℝ)) * chebWeight (d * N) i θ₀ := by
          dsimp [chebWeight]
          rw [hang, hcosD, hcosd, hsign]
          have hDNcast : ((D * N : ℕ) : ℝ) = (c : ℝ) * ((d * N : ℕ) : ℝ) := by
            have : D * N = c * (d * N) := by rw [← hcD]; ring
            exact_mod_cast this
          rw [hDNcast, div_mul_div_comm]
          congr 1 <;> ring
        rw [hw_rel]
        ring
      have hcs : ∑ i ∈ Finset.univ.filter (IsPrim (d * N)), chebWeight (d * N) i θ₀ * coeff d i =
          (ArithmeticFunction.moebius d : ℝ) * chi4 d / d * v := hcoeff_sum d hd
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hcs]
    · refine Finset.sum_eq_zero fun i hi => ?_
      have hprim : IsPrim (d * N) i := (Finset.mem_filter.mp hi).2
      have hno : ¬ ∃ j : Fin (D * N), chebNode (D * N) j = chebNode (d * N) i := by
        rintro ⟨j, hj⟩
        obtain ⟨c, _, hDN, _⟩ := chebNode_eq_of_isPrim hprim hj
        have hdvd_D : d ∣ D := by
          have : D * N = (c * d) * N := by rw [hDN]; ring
          have hDc : D = c * d := Nat.eq_of_mul_eq_mul_right hNpos this
          exact ⟨c, by rw [hDc, mul_comm]⟩
        exact hdvd hdvd_D
      simp [hno]
  rw [Finset.sum_congr rfl hinner]
  have hset : Dset.filter (· ∣ D) = D.divisors.filter (· ≤ K) := by
    ext d
    simp only [Finset.mem_filter, Dset, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨_, hdK⟩, _⟩, hdvd⟩
      exact ⟨⟨hdvd, hDpos.ne'⟩, hdK⟩
    · rintro ⟨⟨hdvd, _⟩, hdK⟩
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hDpos
      have hd_odd : Odd d := by
        obtain ⟨c, hc⟩ := hdvd
        by_contra hnot
        obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hnot
        exact (Nat.not_even_iff_odd.mpr hDodd) ⟨t * c, by rw [hc, ht]; ring⟩
      exact ⟨⟨⟨hd_pos, hdK⟩, hd_odd⟩, hdvd⟩
  rw [← Finset.sum_filter, hset, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have ⟨hdiv, _⟩ := Finset.mem_filter.mp hd
  have hdvd : d ∣ D := (Nat.mem_divisors.mp hdiv).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hDpos
  have hd_odd : Odd d := by
    obtain ⟨c, hc⟩ := hdvd
    by_contra hnot
    obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hnot
    exact (Nat.not_even_iff_odd.mpr hDodd) ⟨t * c, by rw [hc, ht]; ring⟩
  have hc_odd : Odd (D / d) := by
    have hmul := Nat.div_mul_cancel hdvd
    by_contra hnot
    obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hnot
    exact (Nat.not_even_iff_odd.mpr hDodd) ⟨t * d, by rw [← hmul, ht]; ring⟩
  have hchi : chi4 (D / d) * chi4 d = chi4 D := by
    rw [← chi4_mul_of_odd hc_odd hd_odd, Nat.div_mul_cancel hdvd]
  have hmulR : ((D / d : ℕ) : ℝ) * (d : ℝ) = (D : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hcR : ((D / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hc_odd.pos.ne'
  calc (chi4 (D / d) / ((D / d : ℕ) : ℝ)) * ((ArithmeticFunction.moebius d : ℝ) * chi4 d / d * v)
      = (chi4 (D / d) * chi4 d) / (((D / d : ℕ) : ℝ) * d) * v * (ArithmeticFunction.moebius d : ℝ) := by
        field_simp [hcR, hdR]
    _ = chi4 D / D * v * (ArithmeticFunction.moebius d : ℝ) := by rw [hchi, hmulR]

private lemma stageBumpFun_tv_bound {p' q : ℕ} (hp' : Odd p') (hq : Odd q)
    (hp1 : 1 ≤ p') (hpq : p' ≤ q)
    (N : ℕ) (Pairs : Finset ((d : ℕ) × Fin (d * N)))
    (ht : ((d : ℕ) × Fin (d * N)) → ℝ) {r : ℝ} (hr_pos : 0 < r)
    (hdist1 : ∀ a ∈ Pairs, 2 * r ≤ |Real.cos (Real.pi * p' / q) - chebNode (a.1 * N) a.2|)
    (n : ℕ) (hn : 0 < n) :
    |(chebInterp (stageBumpFun N Pairs ht r) n).eval (Real.cos (Real.pi * p' / q))| ≤
      (∑ a ∈ Pairs, |ht a| * (8 / |Real.cos (Real.pi * p' / q) - chebNode (a.1 * N) a.2| +
        12 * Real.pi / |Real.cos (Real.pi * p' / q) - chebNode (a.1 * N) a.2| ^ 2)) / (n : ℝ) := by
  set x₀ := Real.cos (Real.pi * p' / q)
  have hne_x0 : ∀ j : Fin n, Real.cos (Real.pi * p' / q) ≠ chebNode n j :=
    fun j => chebNode_ne_cos_odd n j hp' hq hp1 hpq
  unfold stageBumpFun
  rw [eval_chebInterp_finset_sum]
  calc |∑ a ∈ Pairs, (chebInterp (fun t => ht a * tent (chebNode (a.1 * N) a.2) r t) n).eval x₀|
      ≤ ∑ a ∈ Pairs, |(chebInterp (fun t => ht a * tent (chebNode (a.1 * N) a.2) r t) n).eval x₀| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ Pairs, |ht a| * |(chebInterp (tent (chebNode (a.1 * N) a.2) r) n).eval x₀| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [eval_chebInterp_smul, abs_mul]
    _ ≤ ∑ a ∈ Pairs, |ht a| * ((1 / (n : ℝ)) *
          (8 / |x₀ - chebNode (a.1 * N) a.2| + 12 * Real.pi / |x₀ - chebNode (a.1 * N) a.2| ^ 2)) := by
        refine Finset.sum_le_sum fun a ha => ?_
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact tent_tv_bound hr_pos (hdist1 a ha) hn hne_x0
    _ = (∑ a ∈ Pairs, |ht a| * (8 / |x₀ - chebNode (a.1 * N) a.2| +
          12 * Real.pi / |x₀ - chebNode (a.1 * N) a.2| ^ 2)) / (n : ℝ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring

private lemma exists_stage_bump {p' q : ℕ} (hp' : Odd p') (hq : Odd q)
    (hp1 : 1 ≤ p') (hpq : p' ≤ q)
    (M_prev : ℕ) (v ε η C_prev : ℝ)
    (hv : |v| ≤ 2) (hε : 0 < ε) (hη : 0 < η) (_hCprev : 0 ≤ C_prev) :
    ∃ (N M : ℕ) (C_cur : ℝ) (g : ℝ → ℝ),
      M_prev < N ∧ N < M ∧ 0 ≤ C_cur ∧
      Continuous g ∧
      (∀ x, |g x| ≤ ε) ∧
      (∀ n, 0 < n → n ≤ M_prev → ∀ i : Fin n, g (chebNode n i) = 0) ∧
      (chebInterp g N).eval (Real.cos (Real.pi * p' / q)) = v ∧
      (∀ n, M_prev < n → n ≤ M → n ≠ N →
        |(chebInterp g n).eval (Real.cos (Real.pi * p' / q))| ≤ η) ∧
      (∀ n, 0 < n → |(chebInterp g n).eval (Real.cos (Real.pi * p' / q))| ≤ C_cur / n) ∧
      (C_prev + C_cur) / M ≤ η := by
  classical
  set θ₀ := Real.pi * p' / q
  set x₀ := Real.cos θ₀
  have hqpos : 0 < q := hq.pos
  -- Choose K large enough that 4 / sqrt(K) <= eta (and K >= 1)
  obtain ⟨K, hK1, hKbound⟩ : ∃ K : ℕ, 1 ≤ K ∧ 4 / Real.sqrt (K : ℝ) ≤ η := by
    obtain ⟨K0, hK0⟩ := exists_nat_gt ((4 / η) ^ 2)
    refine ⟨max 1 K0, le_max_left _ _, ?_⟩
    have hKpos : (0 : ℝ) < (max 1 K0 : ℕ) := by positivity
    have hsq : (4 / η) ^ 2 < ((max 1 K0 : ℕ) : ℝ) :=
      lt_of_lt_of_le hK0 (by exact_mod_cast le_max_right 1 K0)
    have hrt : 4 / η ≤ Real.sqrt ((max 1 K0 : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by positivity) hKpos.le]
      exact hsq.le
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hKpos)]
    have := (div_le_iff₀ hη).mp hrt
    linarith
  -- Choose k >= 1 large enough that N = 2^k * q > M_prev and all primitive Lebesgue sums >= 2 / eps
  obtain ⟨k, hk1, hNgt, hkleb⟩ := prim_lebesgue_ge hp' hq hp1 hpq M_prev K (2 / ε)
  set N := 2 ^ k * q
  have hNpos : 0 < N := by dsimp [N]; positivity
  let Dset : Finset ℕ := (Finset.Icc 1 K).filter Odd
  let target (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ) * chi4 d / d * v
  let Lsum (d : ℕ) : ℝ := ∑ i ∈ Finset.univ.filter (IsPrim (d * N)), |chebWeight (d * N) i θ₀|
  have hLsum_ge : ∀ d ∈ Dset, 2 / ε ≤ Lsum d := by
    intro d hd
    have ⟨hIcc, hodd⟩ := Finset.mem_filter.mp hd
    exact hkleb d hodd (Finset.mem_Icc.mp hIcc).2
  have htarget_le : ∀ d ∈ Dset, |target d| ≤ 2 := by
    intro d hd
    have hIcc := (Finset.mem_filter.mp hd).1
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hIcc).1
    dsimp [target]
    rw [abs_mul, abs_div, abs_mul, abs_chi4, mul_one, abs_of_pos (by linarith : (0 : ℝ) < d)]
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hdiv_le : |(ArithmeticFunction.moebius d : ℝ)| / d ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hmu.trans hd1
    calc |(ArithmeticFunction.moebius d : ℝ)| / d * |v| ≤ 1 * 2 :=
          mul_le_mul hdiv_le hv (abs_nonneg _) zero_le_one
      _ = 2 := one_mul 2
  let coeff (d : ℕ) (i : Fin (d * N)) : ℝ :=
    (target d / Lsum d) * (if 0 ≤ chebWeight (d * N) i θ₀ then 1 else -1)
  have hcoeff_le : ∀ d ∈ Dset, ∀ i : Fin (d * N), |coeff d i| ≤ ε := by
    intro d hd i
    have hL : 2 / ε ≤ Lsum d := hLsum_ge d hd
    have hLpos : 0 < Lsum d := lt_of_lt_of_le (by positivity) hL
    have ht : |target d| ≤ 2 := htarget_le d hd
    dsimp [coeff]
    rw [abs_mul, abs_div, abs_of_pos hLpos]
    have hsgn : |(if 0 ≤ chebWeight (d * N) i θ₀ then (1 : ℝ) else -1)| = 1 := by
      split_ifs <;> norm_num
    rw [hsgn, mul_one, div_le_iff₀ hLpos]
    have h2 : 2 ≤ ε * Lsum d := by
      have := (div_le_iff₀ hε).mp hL
      linarith
    linarith
  have hcoeff_sum : ∀ d ∈ Dset,
      ∑ i ∈ Finset.univ.filter (IsPrim (d * N)), chebWeight (d * N) i θ₀ * coeff d i = target d := by
    intro d hd
    have hLpos : 0 < Lsum d := lt_of_lt_of_le (by positivity) (hLsum_ge d hd)
    have hrew : ∀ i ∈ Finset.univ.filter (IsPrim (d * N)),
        chebWeight (d * N) i θ₀ * coeff d i = (target d / Lsum d) * |chebWeight (d * N) i θ₀| := by
      intro i _
      dsimp [coeff]
      split_ifs with hw
      · rw [abs_of_nonneg hw]; ring
      · push Not at hw; rw [abs_of_neg hw]; ring
    rw [Finset.sum_congr rfl hrew, ← Finset.mul_sum]
    change (target d / Lsum d) * Lsum d = target d
    exact div_mul_cancel₀ _ hLpos.ne'
  let Pairs : Finset ((d : ℕ) × Fin (d * N)) :=
    Dset.sigma (fun d => Finset.univ.filter (IsPrim (d * N)))
  let ht : ((d : ℕ) × Fin (d * N)) → ℝ := fun a => coeff a.1 a.2
  have hpt_inj : Set.InjOn (fun a : (d : ℕ) × Fin (d * N) => chebNode (a.1 * N) a.2) (Pairs : Set _) := by
    intro a ha b hb heq
    have ha' := Finset.mem_sigma.mp ha
    have hb' := Finset.mem_sigma.mp hb
    have hpa : IsPrim (a.1 * N) a.2 := (Finset.mem_filter.mp ha'.2).2
    have hpb : IsPrim (b.1 * N) b.2 := (Finset.mem_filter.mp hb'.2).2
    obtain ⟨c1, _, hc1, _⟩ := chebNode_eq_of_isPrim hpa heq.symm
    obtain ⟨c2, _, hc2, _⟩ := chebNode_eq_of_isPrim hpb heq
    have hd1 : a.1 * N ∣ b.1 * N := ⟨c1, by rw [hc1, mul_comm]⟩
    have hd2 : b.1 * N ∣ a.1 * N := ⟨c2, by rw [hc2, mul_comm]⟩
    have heq_ord : a.1 * N = b.1 * N := Nat.dvd_antisymm hd1 hd2
    have heq_d : a.1 = b.1 := Nat.eq_of_mul_eq_mul_right hNpos heq_ord
    cases a with
    | mk d1 i1 =>
      cases b with
      | mk d2 i2 =>
        dsimp at heq_d heq
        subst heq_d
        congr 1
        exact chebNode_injective (d1 * N) heq
  have hpt_ne_x0 : ∀ a ∈ Pairs, x₀ ≠ chebNode (a.1 * N) a.2 := fun a _ =>
    chebNode_ne_cos_odd (a.1 * N) a.2 hp' hq hp1 hpq
  let C_cur : ℝ := ∑ a ∈ Pairs, |ht a| *
    (8 / |x₀ - chebNode (a.1 * N) a.2| + 12 * Real.pi / |x₀ - chebNode (a.1 * N) a.2| ^ 2)
  have hCcur_nonneg : 0 ≤ C_cur := by
    apply Finset.sum_nonneg
    intro a ha
    have : 0 < |x₀ - chebNode (a.1 * N) a.2| := abs_pos.mpr (sub_ne_zero.mpr (hpt_ne_x0 a ha))
    positivity
  obtain ⟨M0, hM0⟩ := exists_nat_gt ((C_prev + C_cur) / η)
  set M := max (N + 1) M0
  have hNM : N < M := lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_left _ _)
  have hMpos : 0 < M := lt_trans hNpos hNM
  have hCM : (C_prev + C_cur) / (M : ℝ) ≤ η := by
    have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
    have hle : (C_prev + C_cur) / η ≤ (M : ℝ) :=
      le_trans hM0.le (by exact_mod_cast le_max_right (N + 1) M0)
    rw [div_le_iff₀ hMR]
    have := (div_le_iff₀ hη).mp hle
    linarith
  obtain ⟨r, hr_pos, hdist1, hdist2, hsep⟩ := exists_stage_radius N M x₀ Pairs hpt_inj hpt_ne_x0
  let g : ℝ → ℝ := stageBumpFun N Pairs ht r
  have hg_eval_odd : ∀ D : ℕ, Odd D → D * N ≤ M →
      (chebInterp g (D * N)).eval x₀ =
        (chi4 D / D) * v * ∑ d ∈ D.divisors.filter (· ≤ K), (ArithmeticFunction.moebius d : ℝ) := by
    intro D hDodd hDNM
    have hDNpos : 1 ≤ D * N := Nat.mul_pos hDodd.pos hNpos
    rw [stageBumpFun_eval_exact hp' hq hp1 hpq N M Pairs ht hr_pos hpt_inj hsep (D * N) hDNpos hDNM]
    exact stageBumpFun_eval_odd_mul hq hk1 v coeff hcoeff_sum D hDodd
  refine ⟨N, M, C_cur, g, hNgt, hNM, hCcur_nonneg,
    stageBumpFun_continuous N Pairs ht r,
    stageBumpFun_bound N Pairs ht hr_pos hε (fun a ha => hcoeff_le a.1 (Finset.mem_sigma.mp ha).1 a.2) hdist2,
    ?_, ?_, ?_,
    fun n hn => stageBumpFun_tv_bound hp' hq hp1 hpq N Pairs ht hr_pos hdist1 n hn,
    hCM⟩
  · -- g vanishes on all nodes of order n ≤ M_prev
    intro n hn hnM j
    apply stageBumpFun_at_node N M Pairs ht hr_pos hsep n hn (by omega) j
    intro a ha heq
    have ha' := Finset.mem_sigma.mp ha
    have hpa : IsPrim (a.1 * N) a.2 := (Finset.mem_filter.mp ha'.2).2
    obtain ⟨c, hcodd, hnc, _⟩ := chebNode_eq_of_isPrim hpa heq
    have hc1 : 1 ≤ c := hcodd.pos
    have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha'.1).1).1
    have : N ≤ n := by
      calc N = 1 * (1 * N) := by ring
        _ ≤ c * (a.1 * N) := Nat.mul_le_mul hc1 (Nat.mul_le_mul_right N ha1)
        _ = n := hnc.symm
    omega
  · -- (chebInterp g N).eval x₀ = v
    have h1 := hg_eval_odd 1 odd_one (by rw [one_mul]; exact hNM.le)
    rw [one_mul] at h1
    rw [h1, chi4_one]
    have hdiv1 : (Nat.divisors 1).filter (· ≤ K) = {1} := by
      ext d; simp only [Finset.mem_filter, Nat.divisors_one, Finset.mem_singleton]
      exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hK1⟩⟩
    rw [hdiv1, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one]
    simp
  · -- For M_prev < n ≤ M with n ≠ N: |(chebInterp g n).eval x₀| ≤ η
    intro n hnlo hnhi hneN
    have hn1 : 1 ≤ n := by omega
    by_cases hmult : ∃ D : ℕ, Odd D ∧ n = D * N
    · obtain ⟨D, hDodd, rfl⟩ := hmult
      have hDne1 : D ≠ 1 := fun h => hneN (by rw [h, one_mul])
      have hDpos : 0 < D := hDodd.pos
      rw [hg_eval_odd D hDodd hnhi]
      by_cases hDK : D ≤ K
      · have hfilt : D.divisors.filter (· ≤ K) = D.divisors := by
          apply Finset.filter_eq_self.mpr
          intro d hd
          exact (Nat.le_of_dvd hDpos (Nat.mem_divisors.mp hd).1).trans hDK
        rw [hfilt, sum_divisors_moebius_real D hDpos, if_neg hDne1, mul_zero, abs_zero]
        exact hη.le
      · push Not at hDK
        have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
        have hsum_le : |∑ d ∈ D.divisors.filter (· ≤ K), (ArithmeticFunction.moebius d : ℝ)| ≤
            2 * Real.sqrt (D : ℝ) := by
          calc |∑ d ∈ D.divisors.filter (· ≤ K), (ArithmeticFunction.moebius d : ℝ)|
              ≤ ∑ d ∈ D.divisors.filter (· ≤ K), |(ArithmeticFunction.moebius d : ℝ)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _d ∈ D.divisors.filter (· ≤ K), (1 : ℝ) :=
                Finset.sum_le_sum fun d _ => by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
            _ = ((D.divisors.filter (· ≤ K)).card : ℝ) := by simp
            _ ≤ (D.divisors.card : ℝ) := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
            _ ≤ 2 * Real.sqrt (D : ℝ) := card_divisors_le_two_mul_sqrt D
        rw [abs_mul, abs_mul, abs_div, abs_chi4, abs_of_pos hDR]
        have hsqrtD_pos : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr hDR
        have hsqrt_le : Real.sqrt (K : ℝ) ≤ Real.sqrt (D : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hDK.le)
        calc 1 / (D : ℝ) * |v| * |∑ d ∈ D.divisors.filter (· ≤ K), (ArithmeticFunction.moebius d : ℝ)|
            ≤ 1 / (D : ℝ) * 2 * (2 * Real.sqrt (D : ℝ)) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hv (by positivity)) hsum_le (abs_nonneg _) (by positivity)
          _ = 4 / Real.sqrt (D : ℝ) := by
              have hsq : Real.sqrt (D : ℝ) * Real.sqrt (D : ℝ) = (D : ℝ) := Real.mul_self_sqrt hDR.le
              field_simp [hDR.ne', hsqrtD_pos.ne']
              nlinarith
          _ ≤ 4 / Real.sqrt (K : ℝ) := by
              apply div_le_div_of_nonneg_left (by norm_num)
                (Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1))) hsqrt_le
          _ ≤ η := hKbound
    · rw [stageBumpFun_eval_exact hp' hq hp1 hpq N M Pairs ht hr_pos hpt_inj hsep n hn1 hnhi]
      have hzero : ∑ a ∈ Pairs, (if h : ∃ j : Fin n, chebNode n j = chebNode (a.1 * N) a.2 then
          chebWeight n h.choose θ₀ * ht a else 0) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        have hno : ¬ ∃ j : Fin n, chebNode n j = chebNode (a.1 * N) a.2 := by
          rintro ⟨j, hj⟩
          have ha' := Finset.mem_sigma.mp ha
          have hpa : IsPrim (a.1 * N) a.2 := (Finset.mem_filter.mp ha'.2).2
          have ha_odd : Odd a.1 := (Finset.mem_filter.mp ha'.1).2
          obtain ⟨c, hcodd, hnc, _⟩ := chebNode_eq_of_isPrim hpa hj
          exact hmult ⟨c * a.1, hcodd.mul ha_odd, by rw [hnc]; ring⟩
        simp [hno]
      rw [hzero, abs_zero]
      exact hη.le

/-! ### Section 6: Dense target sequence, recursive construction, and cluster-point equality -/

private lemma exists_dense_cluster_seq (A : Set ℝ) (_hA_closed : IsClosed A) (hA_ne : A.Nonempty) :
    ∃ a : ℕ → ℝ, (∀ m, a m ∈ A) ∧ ∀ y ∈ A, ∀ ε > 0, ∀ B : ℕ, ∃ m ≥ B, |a m - y| < ε := by
  have : Nonempty A := hA_ne.to_subtype
  obtain ⟨s, hs_count, hs_dense⟩ := TopologicalSpace.exists_countable_dense A
  have hs_ne : s.Nonempty := hs_dense.nonempty
  obtain ⟨d, hd_surj⟩ := hs_count.exists_eq_range hs_ne
  let a : ℕ → ℝ := fun m => (d (Nat.unpair m).1).val
  refine ⟨a, fun m => (d (Nat.unpair m).1).property, ?_⟩
  intro y hy ε hε B
  have hy_mem : (⟨y, hy⟩ : A) ∈ closure s := hs_dense ⟨y, hy⟩
  rw [Metric.mem_closure_iff] at hy_mem
  obtain ⟨z, hz_mem, hz_dist⟩ := hy_mem ε hε
  rw [hd_surj] at hz_mem
  obtain ⟨k, rfl⟩ := hz_mem
  set m := Nat.pair k B
  have hmB : B ≤ m := Nat.right_le_pair k B
  refine ⟨m, hmB, ?_⟩
  have h1 : a m = (d k).val := by simp [a, m, Nat.unpair_pair]
  rw [h1]
  have hdist : dist (d k).val y < ε := by
    simpa [Subtype.dist_eq, dist_comm] using hz_dist
  rwa [Real.dist_eq] at hdist

private structure Stage (p' q : ℕ) (M_prev : ℕ) (v ε η C_prev : ℝ) where
  N : ℕ
  M : ℕ
  C_cur : ℝ
  g : ℝ → ℝ
  hNgt : M_prev < N
  hNM : N < M
  hCcur : 0 ≤ C_cur
  hcont : Continuous g
  hbound : ∀ x, |g x| ≤ ε
  hzero : ∀ n, 0 < n → n ≤ M_prev → ∀ i : Fin n, g (chebNode n i) = 0
  hevalN : (chebInterp g N).eval (Real.cos (Real.pi * p' / q)) = v
  hsmall : ∀ n, M_prev < n → n ≤ M → n ≠ N →
    |(chebInterp g n).eval (Real.cos (Real.pi * p' / q))| ≤ η
  htail : ∀ n, 0 < n → |(chebInterp g n).eval (Real.cos (Real.pi * p' / q))| ≤ C_cur / n
  hCM : (C_prev + C_cur) / M ≤ η

private noncomputable def mkStage {p' q : ℕ} (hp' : Odd p') (hq : Odd q)
    (hp1 : 1 ≤ p') (hpq : p' ≤ q)
    (M_prev : ℕ) (v ε η C_prev : ℝ)
    (hv : |v| ≤ 2) (hε : 0 < ε) (hη : 0 < η) (hCprev : 0 ≤ C_prev) :
    Stage p' q M_prev v ε η C_prev :=
  let h := exists_stage_bump hp' hq hp1 hpq M_prev v ε η C_prev hv hε hη hCprev
  let N := h.choose
  let h1 := h.choose_spec
  let M := h1.choose
  let h2 := h1.choose_spec
  let C_cur := h2.choose
  let h3 := h2.choose_spec
  let g := h3.choose
  let h4 := h3.choose_spec
  ⟨N, M, C_cur, g, h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2.1, h4.2.2.2.2.2.1,
    h4.2.2.2.2.2.2.1, h4.2.2.2.2.2.2.2.1, h4.2.2.2.2.2.2.2.2.1, h4.2.2.2.2.2.2.2.2.2⟩

private structure RecState (p' q : ℕ) where
  N : ℕ
  M : ℕ
  C_acc : ℝ
  g : ℝ → ℝ
  hCacc : 0 ≤ C_acc

theorem solution : type_of% @OMA.S_erdos_1151.main := by
  intro p q hp hq A hA_closed hA_ne hA_sub
  obtain ⟨p', hp', hp1, hpq, hcos_eq⟩ := reduce_odd_angle p q hp hq
  rw [hcos_eq]
  set x₀ := Real.cos (Real.pi * p' / q)
  obtain ⟨a, ha_mem, ha_dense⟩ := exists_dense_cluster_seq A hA_closed hA_ne
  have ha_abs : ∀ m, |a m - a 0| ≤ 2 := by
    intro m
    have h1 := Set.mem_Icc.mp (hA_sub (ha_mem m))
    have h2 := Set.mem_Icc.mp (hA_sub (ha_mem 0))
    rw [abs_le]
    constructor <;> linarith
  let ε : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ (m + 2)
  let η : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ (m + 3)
  have hε_pos : ∀ m, 0 < ε m := fun m => by dsimp [ε]; positivity
  have hη_pos : ∀ m, 0 < η m := fun m => by dsimp [η]; positivity
  -- Recursively define the stage sequence with bundled proofs
  let state : ℕ → RecState p' q := fun m =>
    Nat.rec
      (let st0 := mkStage hp' hq hp1 hpq 0 (a 0 - a 0) (ε 0) (η 0) 0
        (ha_abs 0) (hε_pos 0) (hη_pos 0) le_rfl
       ⟨st0.N, st0.M, st0.C_cur, st0.g, st0.hCcur⟩)
      (fun k prev =>
       let stk := mkStage hp' hq hp1 hpq prev.M (a (k + 1) - a 0) (ε (k + 1)) (η (k + 1)) prev.C_acc
        (ha_abs (k + 1)) (hε_pos (k + 1)) (hη_pos (k + 1)) prev.hCacc
       ⟨stk.N, stk.M, prev.C_acc + stk.C_cur, stk.g, add_nonneg prev.hCacc stk.hCcur⟩)
      m
  let Mprev : ℕ → ℕ := fun m => match m with | 0 => 0 | k + 1 => (state k).M
  let Cprev : ℕ → ℝ := fun m => match m with | 0 => 0 | k + 1 => (state k).C_acc
  have hCprev_nonneg : ∀ m, 0 ≤ Cprev m := by
    intro m; cases m with
    | zero => exact le_rfl
    | succ k => exact (state k).hCacc
  let st : (m : ℕ) → Stage p' q (Mprev m) (a m - a 0) (ε m) (η m) (Cprev m) :=
    fun m => mkStage hp' hq hp1 hpq (Mprev m) (a m - a 0) (ε m) (η m) (Cprev m)
      (ha_abs m) (hε_pos m) (hη_pos m) (hCprev_nonneg m)
  have hstate_N : ∀ m, (state m).N = (st m).N := by
    intro m; cases m <;> rfl
  have hstate_M : ∀ m, (state m).M = (st m).M := by
    intro m; cases m <;> rfl
  have hstate_g : ∀ m, (state m).g = (st m).g := by
    intro m; cases m <;> rfl
  have hstate_C : ∀ m, (state m).C_acc = Cprev m + (st m).C_cur := by
    intro m; cases m with
    | zero => dsimp [state, Cprev, st]; ring
    | succ k => rfl
  -- Monotonicity of M
  have hM_strictMono : StrictMono (fun m => (st m).M) := by
    apply strictMono_nat_of_lt_succ
    intro m
    have h1 : (st m).M < (st (m + 1)).N := by
      simpa [Mprev, hstate_M] using (st (m + 1)).hNgt
    exact lt_trans h1 (st (m + 1)).hNM
  have hMprev_le_M : ∀ j m, j < m → (st j).M ≤ Mprev m := by
    intro j m hjm
    cases m with
    | zero => omega
    | succ k =>
      dsimp [Mprev]
      rw [hstate_M]
      exact hM_strictMono.monotone (by omega)
  have hCacc_eq : ∀ m, (state m).C_acc = ∑ j ∈ Finset.range (m + 1), (st j).C_cur := by
    intro m
    induction m with
    | zero =>
      rw [hstate_C 0, Finset.sum_range_one]
      dsimp [Cprev]
      ring
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
  -- Define f(x) = a 0 + ∑' m, (st m).g x
  let f : ℝ → ℝ := fun x => a 0 + ∑' m : ℕ, (st m).g x
  have hsum_eps : Summable ε := by
    have h1 : Summable (fun m : ℕ => ((1 / 2 : ℝ) ^ 2) * (1 / 2 : ℝ) ^ m) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine h1.congr fun m => ?_
    dsimp [ε]
    rw [pow_add, mul_comm]
  have hf_cont : Continuous f := by
    refine continuous_const.add ?_
    apply continuous_tsum (fun m => (st m).hcont) hsum_eps
    intro m x
    simpa [Real.norm_eq_abs] using (st m).hbound x
  refine ⟨f, hf_cont.continuousOn, ?_⟩
  -- For any n ≥ 1, find the unique stage m with Mprev m < n ≤ (st m).M
  have hex_stage : ∀ n, 1 ≤ n → ∃ m : ℕ, Mprev m < n ∧ n ≤ (st m).M := by
    intro n hn
    have hex : ∃ m : ℕ, n ≤ (st m).M := by
      have hge : ∀ k, k ≤ (st k).M := hM_strictMono.id_le
      exact ⟨n, hge n⟩
    set m := Nat.find hex
    refine ⟨m, ?_, Nat.find_spec hex⟩
    cases hm : m with
    | zero => dsimp [Mprev]; omega
    | succ k =>
      dsimp [Mprev]
      rw [hstate_M]
      have hlt : k < Nat.find hex := by change k < m; rw [hm]; exact Nat.lt_succ_self k
      have := Nat.find_min hex hlt
      omega
  -- Exact evaluation of (chebInterp f n).eval x₀ at stage m
  have hf_eval_stage : ∀ n m, 1 ≤ n → Mprev m < n → n ≤ (st m).M →
      (chebInterp f n).eval x₀ =
        a 0 + ∑ j ∈ Finset.range (m + 1), (chebInterp (st j).g n).eval x₀ := by
    intro n m hn hlo hhi
    have hf_eq : ∀ i : Fin n,
        f (chebNode n i) = a 0 + ∑ j ∈ Finset.range (m + 1), (st j).g (chebNode n i) := by
      intro i
      dsimp [f]
      congr 1
      rw [tsum_eq_sum]
      intro j hj
      have hjm : m < j := by
        rw [Finset.mem_range] at hj; omega
      have hle : n ≤ Mprev j := hhi.trans (hMprev_le_M m j hjm)
      exact (st j).hzero n hn hle i
    rw [eval_chebInterp_congr (g := fun t => a 0 + ∑ j ∈ Finset.range (m + 1), (st j).g t) hf_eq x₀,
      eval_chebInterp_add, eval_chebInterp_const (a 0) n hn x₀, eval_chebInterp_finset_sum]
  -- Bound the tail ∑_{j < m} (chebInterp (st j).g n).eval x₀ for Mprev m < n
  have hprev_tail : ∀ n m, 1 ≤ n → Mprev m < n →
      |∑ j ∈ Finset.range m, (chebInterp (st j).g n).eval x₀| ≤ (1 / 2 : ℝ) ^ (m + 2) := by
    intro n m hn hlo
    cases m with
    | zero => simp
    | succ k =>
      have hkM : (st k).M < n := by simpa [Mprev, hstate_M] using hlo
      have hkMpos : 0 < (st k).M := lt_trans (lt_of_le_of_lt (Nat.zero_le _) (st k).hNgt) (st k).hNM
      have hkMR : (0 : ℝ) < (st k).M := by exact_mod_cast hkMpos
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      calc |∑ j ∈ Finset.range (k + 1), (chebInterp (st j).g n).eval x₀|
          ≤ ∑ j ∈ Finset.range (k + 1), |(chebInterp (st j).g n).eval x₀| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range (k + 1), (st j).C_cur / (n : ℝ) :=
            Finset.sum_le_sum fun j _ => (st j).htail n hn
        _ = (∑ j ∈ Finset.range (k + 1), (st j).C_cur) / (n : ℝ) := by rw [Finset.sum_div]
        _ = (Cprev k + (st k).C_cur) / (n : ℝ) := by rw [← hCacc_eq k, hstate_C k]
        _ ≤ (Cprev k + (st k).C_cur) / ((st k).M : ℝ) := by
            apply div_le_div_of_nonneg_left (add_nonneg (hCprev_nonneg k) (st k).hCcur) hkMR
            exact_mod_cast hkM.le
        _ ≤ η k := (st k).hCM
        _ = (1 / 2 : ℝ) ^ (k + 1 + 2) := by dsimp [η]
  -- Prove the exact equality of cluster points!
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor
  · -- MapClusterPt y atTop ... → y ∈ A
    intro hcl
    by_contra hyA
    have hopen : IsOpen Aᶜ := hA_closed.isOpen_compl
    obtain ⟨δ, hδpos, hball⟩ := Metric.isOpen_iff.mp hopen y hyA
    -- Pick m₀ so that (1/2)^(m₀ + 1) < δ / 2
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, (1 / 2 : ℝ) ^ (m₀ + 1) < δ / 2 := by
      have htend : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) atTop (𝓝 0) := by
        simpa [pow_succ] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2 : ℝ)
      exact (htend.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 2))).exists
    -- For all n > (st m₀).M, |(chebInterp f n).eval x₀ - y| ≥ δ / 2
    have hfar : ∀ n, (st m₀).M < n → δ / 2 ≤ |(chebInterp f n).eval x₀ - y| := by
      intro n hn
      have hn1 : 1 ≤ n := by
        have : 0 < (st m₀).M := lt_trans (lt_of_le_of_lt (Nat.zero_le _) (st m₀).hNgt) (st m₀).hNM
        omega
      obtain ⟨m, hlo, hhi⟩ := hex_stage n hn1
      have hm_gt : m₀ < m := by
        by_contra! hle
        have : (st m).M ≤ (st m₀).M := hM_strictMono.monotone hle
        omega
      have hpow_le : (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ (m₀ + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      rw [hf_eval_stage n m hn1 hlo hhi, Finset.sum_range_succ]
      have htail := hprev_tail n m hn1 hlo
      by_cases hnN : n = (st m).N
      · -- Near a m ∈ A
        subst hnN
        rw [(st m).hevalN]
        have hclose : |(a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀ +
            (a m - a 0))) - a m| ≤ (1 / 2 : ℝ) ^ (m + 2) := by
          have : a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀ +
              (a m - a 0)) - a m = ∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀ := by ring
          rw [this]
          exact htail
        have hdistA : δ ≤ |a m - y| := by
          by_contra! hlt
          have hmem : a m ∈ Metric.ball y δ := by
            rw [Metric.mem_ball, Real.dist_eq]; exact hlt
          exact hball hmem (ha_mem m)
        have htri : |a m - y| ≤
            |(a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀ + (a m - a 0))) - y| +
            |(a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀ + (a m - a 0))) - a m| := by
          have h1 := abs_sub_le (a m) (a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀ + (a m - a 0))) y
          rw [abs_sub_comm (a m) (a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀ + (a m - a 0))), add_comm] at h1
          exact h1
        have hpow2 : (1 / 2 : ℝ) ^ (m + 2) ≤ (1 / 2 : ℝ) ^ (m + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        linarith
      · -- Near a 0 ∈ A
        have hsm := (st m).hsmall n hlo hhi hnN
        have hclose : |(a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g n).eval x₀ +
            (chebInterp (st m).g n).eval x₀)) - a 0| ≤ (1 / 2 : ℝ) ^ (m + 1) := by
          have : a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g n).eval x₀ +
              (chebInterp (st m).g n).eval x₀) - a 0 =
              (∑ j ∈ Finset.range m, (chebInterp (st j).g n).eval x₀) +
              (chebInterp (st m).g n).eval x₀ := by ring
          rw [this]
          have hsum_pows : (1 / 2 : ℝ) ^ (m + 2) + (1 / 2 : ℝ) ^ (m + 3) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
            have h1 : (1 / 2 : ℝ) ^ (m + 2) = (1 / 2 : ℝ) ^ (m + 1) * (1 / 2) := by rw [pow_succ]
            have h2 : (1 / 2 : ℝ) ^ (m + 3) = (1 / 2 : ℝ) ^ (m + 1) * (1 / 4) := by
              rw [show m + 3 = (m + 1) + 2 by omega, pow_add]; norm_num
            have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (m + 1) := by positivity
            linarith
          calc _ ≤ |∑ j ∈ Finset.range m, (chebInterp (st j).g n).eval x₀| +
                |(chebInterp (st m).g n).eval x₀| := abs_add_le _ _
            _ ≤ (1 / 2 : ℝ) ^ (m + 2) + η m := add_le_add htail hsm
            _ ≤ (1 / 2 : ℝ) ^ (m + 1) := hsum_pows
        have hdistA : δ ≤ |a 0 - y| := by
          by_contra! hlt
          have hmem : a 0 ∈ Metric.ball y δ := by
            rw [Metric.mem_ball, Real.dist_eq]; exact hlt
          exact hball hmem (ha_mem 0)
        have htri : |a 0 - y| ≤
            |(a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g n).eval x₀ + (chebInterp (st m).g n).eval x₀)) - y| +
            |(a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g n).eval x₀ + (chebInterp (st m).g n).eval x₀)) - a 0| := by
          have h1 := abs_sub_le (a 0) (a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g n).eval x₀ + (chebInterp (st m).g n).eval x₀)) y
          rw [abs_sub_comm (a 0) (a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g n).eval x₀ + (chebInterp (st m).g n).eval x₀)), add_comm] at h1
          exact h1
        linarith
    have hfreq := (mapClusterPt_iff_frequently.mp hcl) (Metric.ball y (δ / 2))
      (Metric.ball_mem_nhds y (by positivity))
    rw [Filter.frequently_atTop] at hfreq
    obtain ⟨n, hn, hball_n⟩ := hfreq ((st m₀).M + 1)
    rw [Metric.mem_ball, Real.dist_eq] at hball_n
    linarith [hfar n (by omega)]
  · -- y ∈ A → MapClusterPt y atTop ...
    intro hy
    rw [mapClusterPt_iff_frequently]
    intro s hs
    obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.mp hs
    rw [Filter.frequently_atTop]
    intro B
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, (1 / 2 : ℝ) ^ (m₀ + 2) < δ / 2 := by
      have htend : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 2)) atTop (𝓝 0) := by
        have hrew : (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 2)) =
            (fun m : ℕ => (1 / 2 : ℝ) ^ m * ((1 / 2 : ℝ) ^ 2)) :=
          funext fun m => pow_add (1 / 2 : ℝ) m 2
        rw [hrew]
        have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ((1 / 2 : ℝ) ^ 2)
        rwa [zero_mul] at hlim
      exact (htend.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 2))).exists
    obtain ⟨m, hm_ge, ha_close⟩ := ha_dense y hy (δ / 2) (by positivity) (max (B + 1) m₀)
    have hN_ge : B ≤ (st m).N := by
      have hmB : B + 1 ≤ m := le_trans (le_max_left _ _) hm_ge
      have hMprev_ge : m - 1 ≤ Mprev m := by
        cases m with
        | zero => omega
        | succ k =>
          dsimp [Mprev]
          rw [hstate_M]
          exact hM_strictMono.id_le k
      have hlt := (st m).hNgt
      omega
    refine ⟨(st m).N, hN_ge, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have hN1 : 1 ≤ (st m).N := lt_of_le_of_lt (Nat.zero_le _) (st m).hNgt
    rw [hf_eval_stage (st m).N m hN1 (st m).hNgt (st m).hNM.le, Finset.sum_range_succ, (st m).hevalN]
    have htail := hprev_tail (st m).N m hN1 (st m).hNgt
    have hpow : (1 / 2 : ℝ) ^ (m + 2) ≤ (1 / 2 : ℝ) ^ (m₀ + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by have := le_trans (le_max_right _ _) hm_ge; omega)
    have heq : a 0 + (∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀ + (a m - a 0)) - y =
        (∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀) + (a m - y) := by ring
    rw [heq]
    calc _ ≤ |∑ j ∈ Finset.range m, (chebInterp (st j).g (st m).N).eval x₀| + |a m - y| := abs_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add (lt_of_le_of_lt (htail.trans hpow) hm₀) ha_close
      _ = δ := add_halves δ

end OMA.Erdos1151

theorem OMA.solution : type_of% @OMA.S_erdos_1151.main :=
  OMA.Erdos1151.solution
