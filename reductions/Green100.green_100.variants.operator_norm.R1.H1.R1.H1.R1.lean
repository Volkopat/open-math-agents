import OMAReductions.R_Green100_green_100_variants_operator_norm_R1_H1_R1
import Mathlib

/-!
Reduction of `Green100.green_100.variants.operator_norm.R1.H1.R1.H1` (Property (FH) and finite
generation of `ℤ³ ⋊ SL(3, ℤ)`) to two classical theorems:
1. `H1`: Carter-Keller (1983) bounded elementary generation of `SL(3, ℤ)` by transvections.
2. `H2`: Burger (1991) / Shalom (1999) relative Property (FH) for `(SL(2, ℤ) ⋊ ℤ², ℤ²)`.

In `main`, we construct the natural action of `SL(3, ℤ)` on `Multiplicative (Fin 3 → ℤ)`,
prove `Countable` and `Group.FG` of `B = ℤ³ ⋊ SL(3, ℤ)` from `H1`, embed five copies of
`ℤ² ⋊ SL(2, ℤ)` into `B` (two lattice blocks and three cyclically conjugated upper-column blocks)
to uniformly bound any 1-cocycle on `ℤ³` and on all six elementary root subgroups via `H2`,
extend the uniform bound to all of `B` via `H1`, and deduce existence of a fixed point by the
Bruhat-Tits Chebyshev center theorem on Hilbert spaces.
-/

open Filter
open scoped Topology

namespace OMA.R_Green100_green_100_variants_operator_norm_R1_H1_R1_H1_R1

/- Carter-Keller (1983): bounded generation of SL(3, ℤ) by elementary transvections. -/
def H1 : Prop :=
  ∃ N : ℕ, ∀ A : Matrix.SpecialLinearGroup (Fin 3) ℤ,
    ∃ l : List (Fin 3 × Fin 3 × ℤ),
      l.length ≤ N ∧
      (∀ e ∈ l, e.1 ≠ e.2.1) ∧
      (A : Matrix (Fin 3) (Fin 3) ℤ) = (l.map fun e => Matrix.transvection e.1 e.2.1 e.2.2).prod

/- Burger (1991) / Shalom (1999): relative Property (FH) for (SL(2, ℤ) ⋊ ℤ², ℤ²),
every Hilbert 1-cocycle of ℤ² ⋊ SL(2, ℤ) is bounded on the normal subgroup ℤ². -/
def H2 : Prop :=
  ∀ (a₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ →* MulAut (Multiplicative (Fin 2 → ℤ))),
    (∀ g x, Multiplicative.toAdd (a₂ g x) = (g : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd x)) →
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (ρ : (Multiplicative (Fin 2 → ℤ) ⋊[a₂] Matrix.SpecialLinearGroup (Fin 2) ℤ) →* E ≃ₗᵢ[ℂ] E)
      (c : (Multiplicative (Fin 2 → ℤ) ⋊[a₂] Matrix.SpecialLinearGroup (Fin 2) ℤ) → E),
      (∀ g h, c (g * h) = c g + ρ g (c h)) →
      ∃ M : ℝ, ∀ x : Multiplicative (Fin 2 → ℤ), ‖c (SemidirectProduct.inl x)‖ ≤ M

/- Bruhat-Tits / Chebyshev center lemma: every bounded 1-cocycle into a Hilbert space is a coboundary. -/
lemma chebyshev_center_of_bdd_cocycle {B E : Type} [Group B]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : B →* E ≃ₗᵢ[ℂ] E) (c : B → E) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (R : ℝ) (hR : ∀ g : B, ‖c g‖ ≤ R) :
    ∃ v : E, ∀ g : B, c g = ρ g v - v := by
  let rad : E → ℝ := fun x => ⨆ g : B, ‖c g - x‖ ^ 2
  have hbdd : ∀ x : E, BddAbove (Set.range fun g : B => ‖c g - x‖ ^ 2) := by
    intro x
    refine ⟨(R + ‖x‖) ^ 2, ?_⟩
    rintro _ ⟨g, rfl⟩
    have hle : ‖c g - x‖ ≤ R + ‖x‖ := (norm_sub_le (c g) x).trans (add_le_add (hR g) le_rfl)
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hrad_ge : ∀ (x : E) (g : B), ‖c g - x‖ ^ 2 ≤ rad x := fun x g => le_ciSup (hbdd x) g
  have hrad_nonneg : ∀ x : E, 0 ≤ rad x := fun x => (sq_nonneg _).trans (hrad_ge x 1)
  have hbdd_inf : BddBelow (Set.range rad) := ⟨0, by rintro _ ⟨x, rfl⟩; exact hrad_nonneg x⟩
  let r : ℝ := ⨅ x : E, rad x
  have hr_le : ∀ x : E, r ≤ rad x := fun x => ciInf_le hbdd_inf x
  have hpara : ∀ x y : E, ‖x - y‖ ^ 2 ≤ 2 * (rad x - r) + 2 * (rad y - r) := by
    intro x y
    let m : E := (2 : ℂ)⁻¹ • (x + y)
    have hrad_m : rad m ≤ (rad x + rad y) / 2 - ‖x - y‖ ^ 2 / 4 := by
      refine ciSup_le fun g => ?_
      have hpl := parallelogram_law_with_norm ℂ (c g - x) (c g - y)
      have hadd : (c g - x) + (c g - y) = (2 : ℂ) • (c g - m) := by
        simp only [m, smul_sub, smul_smul, mul_inv_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul,
          two_smul]
        abel
      have hsub : (c g - x) - (c g - y) = -(x - y) := by abel
      rw [hadd, hsub, norm_smul, norm_neg] at hpl
      have h2n : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [h2n, mul_pow] at hpl
      have hx := hrad_ge x g
      have hy := hrad_ge y g
      linarith
    have hrm := hr_le m
    linarith
  have hex_seq : ∀ k : ℕ, ∃ x : E, rad x < r + ((k : ℝ) + 1)⁻¹ := by
    intro k
    by_contra hno
    push Not at hno
    have hle : r + ((k : ℝ) + 1)⁻¹ ≤ r := le_ciInf hno
    have hpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    linarith
  choose seq hseq using hex_seq
  have hCauchy : CauchySeq seq := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε ^ 2)
    refine ⟨N, fun k hk j hj => ?_⟩
    rw [dist_eq_norm]
    have hN_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h1 : ((k : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ :=
      inv_anti₀ hN_pos (by exact_mod_cast Nat.add_le_add_right hk 1)
    have h2 : ((j : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ :=
      inv_anti₀ hN_pos (by exact_mod_cast Nat.add_le_add_right hj 1)
    have hsq : ‖seq k - seq j‖ ^ 2 < 4 * ((N : ℝ) + 1)⁻¹ := by
      have hp := hpara (seq k) (seq j)
      have hsk := hseq k
      have hsj := hseq j
      linarith
    have hlt_eps : 4 * ((N : ℝ) + 1)⁻¹ < ε ^ 2 := by
      have hN1 : 4 / ε ^ 2 < (N : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ (sq_pos_of_pos hε)] at hN1
      rw [mul_inv_lt_iff₀ hN_pos]
      linarith
    have hsq2 : ‖seq k - seq j‖ ^ 2 < ε ^ 2 := hsq.trans hlt_eps
    nlinarith [norm_nonneg (seq k - seq j)]
  obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hrad_x₀ : rad x₀ ≤ r := by
    refine ciSup_le fun g => ?_
    have ht_lhs : Tendsto (fun k => ‖c g - seq k‖ ^ 2) atTop (𝓝 (‖c g - x₀‖ ^ 2)) :=
      (((continuous_const.sub continuous_id).norm.pow 2).continuousAt.tendsto).comp hx₀
    have ht_rhs : Tendsto (fun k : ℕ => r + ((k : ℝ) + 1)⁻¹) atTop (𝓝 r) := by
      have h0 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).congr fun k => one_div ((k : ℝ) + 1)
      simpa using tendsto_const_nhds.add h0
    refine le_of_tendsto_of_tendsto ht_lhs ht_rhs (Eventually.of_forall fun k => ?_)
    exact (hrad_ge (seq k) g).trans (hseq k).le
  refine ⟨-x₀, fun g => ?_⟩
  let y : E := ρ g x₀ + c g
  have hrad_y : rad y ≤ r := by
    refine ciSup_le fun h => ?_
    have hcg : c h = c g + ρ g (c (g⁻¹ * h)) := by
      have h1 := hc g (g⁻¹ * h)
      rwa [mul_inv_cancel_left] at h1
    have hdiff : c h - y = ρ g (c (g⁻¹ * h) - x₀) := by
      rw [hcg, map_sub]
      simp only [y]
      abel
    rw [hdiff, (ρ g).norm_map]
    exact (hrad_ge x₀ (g⁻¹ * h)).trans hrad_x₀
  have hxy0 : ‖x₀ - y‖ ^ 2 ≤ 0 := by
    have hp := hpara x₀ y
    linarith
  have hxy : x₀ = y := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hxy0 (sq_nonneg _))))
  rw [map_neg]
  have hy_eq : ρ g x₀ + c g = x₀ := hxy.symm
  calc c g = x₀ - ρ g x₀ := eq_sub_of_add_eq' hy_eq
    _ = -ρ g x₀ - -x₀ := by abel

/- Natural action of SL(d, ℤ) on Multiplicative (Fin d → ℤ) by matrix-vector multiplication. -/
lemma exists_sl_action (d : ℕ) :
    ∃ a : Matrix.SpecialLinearGroup (Fin d) ℤ →* MulAut (Multiplicative (Fin d → ℤ)),
      ∀ g x, Multiplicative.toAdd (a g x) =
        (g : Matrix (Fin d) (Fin d) ℤ).mulVec (Multiplicative.toAdd x) := by
  have hmul : ∀ (g h : Matrix.SpecialLinearGroup (Fin d) ℤ) (v : Fin d → ℤ),
      ((g * h : Matrix.SpecialLinearGroup (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℤ).mulVec v =
        (g : Matrix (Fin d) (Fin d) ℤ).mulVec ((h : Matrix (Fin d) (Fin d) ℤ).mulVec v) := by
    intro g h v
    exact (Matrix.mulVec_mulVec v (g : Matrix (Fin d) (Fin d) ℤ) (h : Matrix (Fin d) (Fin d) ℤ)).symm
  have hone : ∀ v : Fin d → ℤ,
      ((1 : Matrix.SpecialLinearGroup (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℤ).mulVec v = v :=
    fun v => Matrix.one_mulVec v
  refine ⟨{
    toFun := fun g =>
      { toFun := fun x => Multiplicative.ofAdd ((g : Matrix (Fin d) (Fin d) ℤ).mulVec (Multiplicative.toAdd x))
        invFun := fun x => Multiplicative.ofAdd (((g⁻¹ : Matrix.SpecialLinearGroup (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℤ).mulVec (Multiplicative.toAdd x))
        left_inv := fun x => by
          change Multiplicative.ofAdd (((g⁻¹ : Matrix.SpecialLinearGroup (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℤ).mulVec
            ((g : Matrix (Fin d) (Fin d) ℤ).mulVec (Multiplicative.toAdd x))) = x
          rw [← hmul g⁻¹ g, inv_mul_cancel, hone]
          rfl
        right_inv := fun x => by
          change Multiplicative.ofAdd ((g : Matrix (Fin d) (Fin d) ℤ).mulVec
            (((g⁻¹ : Matrix.SpecialLinearGroup (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℤ).mulVec (Multiplicative.toAdd x))) = x
          rw [← hmul g g⁻¹, mul_inv_cancel, hone]
          rfl
        map_mul' := fun x y => by
          change Multiplicative.ofAdd ((g : Matrix (Fin d) (Fin d) ℤ).mulVec
            (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
          rw [Matrix.mulVec_add, ofAdd_add] }
    map_one' := by
      ext x i
      exact congrFun (hone (Multiplicative.toAdd x)) i
    map_mul' := fun g h => by
      ext x i
      exact congrFun (hmul g h (Multiplicative.toAdd x)) i }, fun _ _ => rfl⟩

/- Transvection powers in SL(3, ℤ). -/
lemma transvection_zpow_eq {i j : Fin 3} (hij : i ≠ j) (k : ℤ)
    (E Ek : Matrix.SpecialLinearGroup (Fin 3) ℤ)
    (hE : (E : Matrix (Fin 3) (Fin 3) ℤ) = Matrix.transvection i j 1)
    (hEk : (Ek : Matrix (Fin 3) (Fin 3) ℤ) = Matrix.transvection i j k) :
    E ^ k = Ek := by
  have hinv_mat : ((E⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
      Matrix.transvection i j (-1) := by
    let Eneg : Matrix.SpecialLinearGroup (Fin 3) ℤ :=
      ⟨Matrix.transvection i j (-1), Matrix.det_transvection_of_ne i j hij (-1)⟩
    have hEq : E⁻¹ = Eneg := by
      apply inv_eq_of_mul_eq_one_right
      ext a b
      change ((E : Matrix (Fin 3) (Fin 3) ℤ) * (Eneg : Matrix (Fin 3) (Fin 3) ℤ)) a b =
        (1 : Matrix (Fin 3) (Fin 3) ℤ) a b
      rw [hE]
      change (Matrix.transvection i j (1 : ℤ) * Matrix.transvection i j (-1 : ℤ)) a b = _
      rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero]
    rw [hEq]
  have hpow : ∀ m : ℤ,
      ((E ^ m : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
        Matrix.transvection i j m := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      rw [zpow_zero, Matrix.transvection_zero]
      rfl
    | succ n ih =>
      rw [zpow_add_one]
      change ((E ^ (n : ℤ) : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
          (E : Matrix (Fin 3) (Fin 3) ℤ) = _
      rw [ih, hE, Matrix.transvection_mul_transvection_same i j hij]
    | pred n ih =>
      rw [zpow_sub_one]
      change ((E ^ (-(n : ℤ)) : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
          ((E⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = _
      rw [ih, hinv_mat, Matrix.transvection_mul_transvection_same i j hij, sub_eq_add_neg]
  ext a b
  exact congrFun (congrFun ((hpow k).trans hEk.symm) a) b

/- Finite generation of ℤ³ ⋊ SL(3, ℤ) from elementary generation of SL(3, ℤ). -/
lemma fg_of_elem_gen
    (a₃ : Matrix.SpecialLinearGroup (Fin 3) ℤ →* MulAut (Multiplicative (Fin 3 → ℤ)))
    (hH1 : H1) :
    Group.FG (Multiplicative (Fin 3 → ℤ) ⋊[a₃] Matrix.SpecialLinearGroup (Fin 3) ℤ) := by
  classical
  let B := Multiplicative (Fin 3 → ℤ) ⋊[a₃] Matrix.SpecialLinearGroup (Fin 3) ℤ
  let mkSL3 (A : Matrix (Fin 3) (Fin 3) ℤ) (h : A.det = 1) : Matrix.SpecialLinearGroup (Fin 3) ℤ := ⟨A, h⟩
  let S₁ : Finset B := Finset.univ.image fun i : Fin 3 =>
    SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i (1 : ℤ)))
  let pairs : Finset (Fin 3 × Fin 3) := Finset.univ.filter fun p => p.1 ≠ p.2
  let S₂ : Finset B := pairs.attach.image fun p =>
    SemidirectProduct.inr (mkSL3 (Matrix.transvection p.1.1 p.1.2 1)
      (Matrix.det_transvection_of_ne p.1.1 p.1.2
        ((Finset.mem_filter.mp (show p.1 ∈ Finset.univ.filter (fun q : Fin 3 × Fin 3 => q.1 ≠ q.2) from p.2)).2) 1))
  refine ⟨⟨S₁ ∪ S₂, ?_⟩⟩
  rw [eq_top_iff]
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  have hleft : SemidirectProduct.inl g.left ∈ Subgroup.closure (↑(S₁ ∪ S₂) : Set B) := by
    let v : Fin 3 → ℤ := Multiplicative.toAdd g.left
    have hv_eq : g.left = Multiplicative.ofAdd (Pi.single (0 : Fin 3) (v 0)) *
        Multiplicative.ofAdd (Pi.single (1 : Fin 3) (v 1)) *
        Multiplicative.ofAdd (Pi.single (2 : Fin 3) (v 2)) := by
      apply Multiplicative.toAdd.injective
      change v = Pi.single (0 : Fin 3) (v 0) + Pi.single (1 : Fin 3) (v 1) + Pi.single (2 : Fin 3) (v 2)
      ext i
      fin_cases i <;> simp
    have hsingle : ∀ (i : Fin 3) (k : ℤ),
        SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i k)) ∈
          Subgroup.closure (↑(S₁ ∪ S₂) : Set B) := by
      intro i k
      have hpow : (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) : B) ^ k =
          SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i k)) := by
        rw [← map_zpow]
        congr 1
        apply Multiplicative.toAdd.injective
        change k • (Pi.single i (1 : ℤ) : Fin 3 → ℤ) = (Pi.single i k : Fin 3 → ℤ)
        ext j
        by_cases hji : j = i
        · subst hji; simp
        · simp [Pi.single_eq_of_ne hji]
      rw [← hpow]
      refine Subgroup.zpow_mem _ (Subgroup.subset_closure ?_) k
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [hv_eq, map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsingle 0 (v 0)) (hsingle 1 (v 1))) (hsingle 2 (v 2))
  have hright : SemidirectProduct.inr g.right ∈ Subgroup.closure (↑(S₁ ∪ S₂) : Set B) := by
    obtain ⟨_, hgen⟩ := hH1
    obtain ⟨l, _, hne, hprod⟩ := hgen g.right
    have hl_mem : ∀ (l' : List (Fin 3 × Fin 3 × ℤ)), (∀ e ∈ l', e.1 ≠ e.2.1) →
        ∀ (M : Matrix.SpecialLinearGroup (Fin 3) ℤ),
          (M : Matrix (Fin 3) (Fin 3) ℤ) =
            (l'.map fun e => Matrix.transvection e.1 e.2.1 e.2.2).prod →
          SemidirectProduct.inr M ∈ Subgroup.closure (↑(S₁ ∪ S₂) : Set B) := by
      intro l'
      induction l' with
      | nil =>
        intro _ M hM
        have hM1 : M = 1 := by
          ext a b
          simpa using congrFun (congrFun hM a) b
        rw [hM1, map_one]
        exact Subgroup.one_mem _
      | cons e t ih =>
        intro hne' M hM
        have he_ne : e.1 ≠ e.2.1 := hne' e (by simp)
        have ht_ne : ∀ x ∈ t, x.1 ≠ x.2.1 := fun x hx => hne' x (by simp [hx])
        let E : Matrix.SpecialLinearGroup (Fin 3) ℤ :=
          mkSL3 (Matrix.transvection e.1 e.2.1 e.2.2) (Matrix.det_transvection_of_ne e.1 e.2.1 he_ne e.2.2)
        let E1 : Matrix.SpecialLinearGroup (Fin 3) ℤ :=
          mkSL3 (Matrix.transvection e.1 e.2.1 1) (Matrix.det_transvection_of_ne e.1 e.2.1 he_ne 1)
        let T : Matrix.SpecialLinearGroup (Fin 3) ℤ := E⁻¹ * M
        have hT_eq : (T : Matrix (Fin 3) (Fin 3) ℤ) =
            (t.map fun x => Matrix.transvection x.1 x.2.1 x.2.2).prod := by
          have hEinv : ((E⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
              (E : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
            change ((E⁻¹ * E : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = 1
            rw [inv_mul_cancel]; rfl
          calc (T : Matrix (Fin 3) (Fin 3) ℤ)
              = ((E⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
                  (M : Matrix (Fin 3) (Fin 3) ℤ) := rfl
            _ = ((E⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
                  ((E : Matrix (Fin 3) (Fin 3) ℤ) *
                    (t.map fun x => Matrix.transvection x.1 x.2.1 x.2.2).prod) := by
                rw [hM, List.map_cons, List.prod_cons]
            _ = (t.map fun x => Matrix.transvection x.1 x.2.1 x.2.2).prod := by
                rw [← Matrix.mul_assoc, hEinv, Matrix.one_mul]
        have hM_eq : M = E * T := by simp [T]
        rw [hM_eq, map_mul]
        have hE_mem : SemidirectProduct.inr E ∈ Subgroup.closure (↑(S₁ ∪ S₂) : Set B) := by
          have hEz : E = E1 ^ e.2.2 := (transvection_zpow_eq he_ne e.2.2 E1 E rfl rfl).symm
          rw [hEz, map_zpow]
          refine Subgroup.zpow_mem _ (Subgroup.subset_closure ?_) e.2.2
          simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
          right
          refine Finset.mem_image.mpr ⟨⟨(e.1, e.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_ne⟩⟩,
            Finset.mem_attach _ _, rfl⟩
        exact Subgroup.mul_mem _ hE_mem (ih ht_ne T hT_eq)
    exact hl_mem l hne g.right hprod
  exact Subgroup.mul_mem _ hleft hright

/- Lattice block embeddings of ℤ² ⋊ SL(2, ℤ) into ℤ³ ⋊ SL(3, ℤ) on coordinates {0,1} and {1,2}. -/
lemma exists_lattice_embeddings
    (a₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ →* MulAut (Multiplicative (Fin 2 → ℤ)))
    (ha₂ : ∀ g x, Multiplicative.toAdd (a₂ g x) =
      (g : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd x))
    (a₃ : Matrix.SpecialLinearGroup (Fin 3) ℤ →* MulAut (Multiplicative (Fin 3 → ℤ)))
    (ha₃ : ∀ g x, Multiplicative.toAdd (a₃ g x) =
      (g : Matrix (Fin 3) (Fin 3) ℤ).mulVec (Multiplicative.toAdd x)) :
    (∃ f₁ : (Multiplicative (Fin 2 → ℤ) ⋊[a₂] Matrix.SpecialLinearGroup (Fin 2) ℤ) →*
        (Multiplicative (Fin 3 → ℤ) ⋊[a₃] Matrix.SpecialLinearGroup (Fin 3) ℤ),
      ∀ x : Fin 2 → ℤ,
        f₁ (SemidirectProduct.inl (Multiplicative.ofAdd x)) =
          SemidirectProduct.inl (Multiplicative.ofAdd ![x 0, x 1, 0])) ∧
    (∃ f₂ : (Multiplicative (Fin 2 → ℤ) ⋊[a₂] Matrix.SpecialLinearGroup (Fin 2) ℤ) →*
        (Multiplicative (Fin 3 → ℤ) ⋊[a₃] Matrix.SpecialLinearGroup (Fin 3) ℤ),
      ∀ x : Fin 2 → ℤ,
        f₂ (SemidirectProduct.inl (Multiplicative.ofAdd x)) =
          SemidirectProduct.inl (Multiplicative.ofAdd ![0, x 0, x 1])) := by
  have hdet1 : ∀ a b c d : ℤ, a * d - b * c = 1 →
      Matrix.det (![![a, b, 0], ![c, d, 0], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    intro a b c d h
    have hM := Matrix.det_fin_three (Matrix.of ![![a, b, 0], ![c, d, 0], ![0, 0, 1]])
    simp at hM
    exact hM.trans h
  have hdet2 : ∀ a b c d : ℤ, a * d - b * c = 1 →
      Matrix.det (![![1, 0, 0], ![0, a, b], ![0, c, d]] : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    intro a b c d h
    have hM := Matrix.det_fin_three (Matrix.of ![![1, 0, 0], ![0, a, b], ![0, c, d]])
    simp at hM
    exact hM.trans h
  have hmv1 : ∀ (a b c d u v : ℤ) (i : Fin 3),
      Matrix.mulVec (![![a, b, 0], ![c, d, 0], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) ℤ) ![u, v, 0] i =
        ![a * u + b * v, c * u + d * v, 0] i := by
    intro a b c d u v i
    unfold Matrix.mulVec dotProduct
    rw [Fin.sum_univ_three]
    fin_cases i <;> simp
  have hmv2 : ∀ (a b c d u v : ℤ) (i : Fin 3),
      Matrix.mulVec (![![1, 0, 0], ![0, a, b], ![0, c, d]] : Matrix (Fin 3) (Fin 3) ℤ) ![0, u, v] i =
        ![0, a * u + b * v, c * u + d * v] i := by
    intro a b c d u v i
    unfold Matrix.mulVec dotProduct
    rw [Fin.sum_univ_three]
    fin_cases i <;> simp
  constructor
  · let embM₁ : Matrix.SpecialLinearGroup (Fin 2) ℤ → Matrix.SpecialLinearGroup (Fin 3) ℤ :=
      fun A =>
        let f : Fin 2 → Fin 2 → ℤ := (A : Matrix (Fin 2) (Fin 2) ℤ)
        ⟨![![f 0 0, f 0 1, 0], ![f 1 0, f 1 1, 0], ![0, 0, 1]],
          hdet1 (f 0 0) (f 0 1) (f 1 0) (f 1 1) (by
            have hA := Matrix.SpecialLinearGroup.det_coe A
            rw [Matrix.det_fin_two] at hA
            exact hA)⟩
    refine ⟨{
      toFun := fun p =>
        ⟨Multiplicative.ofAdd ![Multiplicative.toAdd p.left 0, Multiplicative.toAdd p.left 1, 0],
         embM₁ p.right⟩
      map_one' := by
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          ext i; fin_cases i <;> rfl
        · ext a b; fin_cases a <;> fin_cases b <;> rfl
      map_mul' := fun p q => by
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          change ![Multiplicative.toAdd (p * q).left 0, Multiplicative.toAdd (p * q).left 1, 0] =
            ![Multiplicative.toAdd p.left 0, Multiplicative.toAdd p.left 1, 0] +
            Multiplicative.toAdd (a₃ (embM₁ p.right)
              (Multiplicative.ofAdd ![Multiplicative.toAdd q.left 0, Multiplicative.toAdd q.left 1, 0]))
          rw [SemidirectProduct.mul_left, toAdd_mul, ha₂, ha₃]
          let fp : Fin 2 → Fin 2 → ℤ := (p.right : Matrix (Fin 2) (Fin 2) ℤ)
          have hv : ∀ j : Fin 2, ((p.right : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd q.left)) j =
              fp j 0 * Multiplicative.toAdd q.left 0 +
              fp j 1 * Multiplicative.toAdd q.left 1 :=
            fun j => by rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          ext i
          change ![Multiplicative.toAdd p.left 0 + ((p.right : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd q.left)) 0,
                   Multiplicative.toAdd p.left 1 + ((p.right : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd q.left)) 1, 0] i =
            ![Multiplicative.toAdd p.left 0, Multiplicative.toAdd p.left 1, 0] i +
            Matrix.mulVec (![![fp 0 0, fp 0 1, 0], ![fp 1 0, fp 1 1, 0], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) ℤ)
              ![Multiplicative.toAdd q.left 0, Multiplicative.toAdd q.left 1, 0] i
          rw [hmv1]
          fin_cases i
          · change Multiplicative.toAdd p.left 0 + _ = _; rw [hv 0]; simp
          · change Multiplicative.toAdd p.left 1 + _ = _; rw [hv 1]; simp
          · simp
        · ext a b
          change (embM₁ (p.right * q.right) : Matrix (Fin 3) (Fin 3) ℤ) a b =
            ((embM₁ p.right : Matrix (Fin 3) (Fin 3) ℤ) * (embM₁ q.right : Matrix (Fin 3) (Fin 3) ℤ)) a b
          have hmul2 : ∀ i j : Fin 2,
              ((p.right : Matrix (Fin 2) (Fin 2) ℤ) * (q.right : Matrix (Fin 2) (Fin 2) ℤ)) i j =
                (p.right : Matrix (Fin 2) (Fin 2) ℤ) i 0 * (q.right : Matrix (Fin 2) (Fin 2) ℤ) 0 j +
                (p.right : Matrix (Fin 2) (Fin 2) ℤ) i 1 * (q.right : Matrix (Fin 2) (Fin 2) ℤ) 1 j :=
            fun i j => by rw [Matrix.mul_apply, Fin.sum_univ_two]
          rw [Matrix.mul_apply, Fin.sum_univ_three]
          dsimp only [embM₁]
          fin_cases a <;> fin_cases b <;> simp <;> (try rw [hmul2]) <;> ring }, ?_⟩
    intro x
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      ext i; fin_cases i <;> rfl
    · ext a b; fin_cases a <;> fin_cases b <;> rfl
  · let embM₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ → Matrix.SpecialLinearGroup (Fin 3) ℤ :=
      fun A =>
        let f : Fin 2 → Fin 2 → ℤ := (A : Matrix (Fin 2) (Fin 2) ℤ)
        ⟨![![1, 0, 0], ![0, f 0 0, f 0 1], ![0, f 1 0, f 1 1]],
          hdet2 (f 0 0) (f 0 1) (f 1 0) (f 1 1) (by
            have hA := Matrix.SpecialLinearGroup.det_coe A
            rw [Matrix.det_fin_two] at hA
            exact hA)⟩
    refine ⟨{
      toFun := fun p =>
        ⟨Multiplicative.ofAdd ![0, Multiplicative.toAdd p.left 0, Multiplicative.toAdd p.left 1],
         embM₂ p.right⟩
      map_one' := by
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          ext i; fin_cases i <;> rfl
        · ext a b; fin_cases a <;> fin_cases b <;> rfl
      map_mul' := fun p q => by
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          change ![0, Multiplicative.toAdd (p * q).left 0, Multiplicative.toAdd (p * q).left 1] =
            ![0, Multiplicative.toAdd p.left 0, Multiplicative.toAdd p.left 1] +
            Multiplicative.toAdd (a₃ (embM₂ p.right)
              (Multiplicative.ofAdd ![0, Multiplicative.toAdd q.left 0, Multiplicative.toAdd q.left 1]))
          rw [SemidirectProduct.mul_left, toAdd_mul, ha₂, ha₃]
          let fp : Fin 2 → Fin 2 → ℤ := (p.right : Matrix (Fin 2) (Fin 2) ℤ)
          have hv : ∀ j : Fin 2, ((p.right : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd q.left)) j =
              fp j 0 * Multiplicative.toAdd q.left 0 +
              fp j 1 * Multiplicative.toAdd q.left 1 :=
            fun j => by rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          ext i
          change ![0, Multiplicative.toAdd p.left 0 + ((p.right : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd q.left)) 0,
                   Multiplicative.toAdd p.left 1 + ((p.right : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd q.left)) 1] i =
            ![0, Multiplicative.toAdd p.left 0, Multiplicative.toAdd p.left 1] i +
            Matrix.mulVec (![![1, 0, 0], ![0, fp 0 0, fp 0 1], ![0, fp 1 0, fp 1 1]] : Matrix (Fin 3) (Fin 3) ℤ)
              ![0, Multiplicative.toAdd q.left 0, Multiplicative.toAdd q.left 1] i
          rw [hmv2]
          fin_cases i
          · simp
          · change Multiplicative.toAdd p.left 0 + _ = _; rw [hv 0]; simp
          · change Multiplicative.toAdd p.left 1 + _ = _; rw [hv 1]; simp
        · ext a b
          change (embM₂ (p.right * q.right) : Matrix (Fin 3) (Fin 3) ℤ) a b =
            ((embM₂ p.right : Matrix (Fin 3) (Fin 3) ℤ) * (embM₂ q.right : Matrix (Fin 3) (Fin 3) ℤ)) a b
          have hmul2 : ∀ i j : Fin 2,
              ((p.right : Matrix (Fin 2) (Fin 2) ℤ) * (q.right : Matrix (Fin 2) (Fin 2) ℤ)) i j =
                (p.right : Matrix (Fin 2) (Fin 2) ℤ) i 0 * (q.right : Matrix (Fin 2) (Fin 2) ℤ) 0 j +
                (p.right : Matrix (Fin 2) (Fin 2) ℤ) i 1 * (q.right : Matrix (Fin 2) (Fin 2) ℤ) 1 j :=
            fun i j => by rw [Matrix.mul_apply, Fin.sum_univ_two]
          rw [Matrix.mul_apply, Fin.sum_univ_three]
          dsimp only [embM₂]
          fin_cases a <;> fin_cases b <;> simp <;> (try rw [hmul2]) <;> ring }, ?_⟩
    intro x
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      ext i; fin_cases i <;> rfl
    · ext a b; fin_cases a <;> fin_cases b <;> rfl

/- Upper-left SL(2, ℤ) + right-column ℤ² embedding into SL(3, ℤ), hitting transvections (0,2) and (1,2). -/
lemma exists_col_embedding
    (a₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ →* MulAut (Multiplicative (Fin 2 → ℤ)))
    (ha₂ : ∀ g x, Multiplicative.toAdd (a₂ g x) =
      (g : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd x)) :
    ∃ φ : (Multiplicative (Fin 2 → ℤ) ⋊[a₂] Matrix.SpecialLinearGroup (Fin 2) ℤ) →*
        Matrix.SpecialLinearGroup (Fin 3) ℤ,
      (∀ k : ℤ, (φ (SemidirectProduct.inl (Multiplicative.ofAdd ![k, 0])) : Matrix (Fin 3) (Fin 3) ℤ) =
        Matrix.transvection 0 2 k) ∧
      (∀ k : ℤ, (φ (SemidirectProduct.inl (Multiplicative.ofAdd ![0, k])) : Matrix (Fin 3) (Fin 3) ℤ) =
        Matrix.transvection 1 2 k) := by
  have hdet3 : ∀ a b c d x y : ℤ, a * d - b * c = 1 →
      Matrix.det (![![a, b, x], ![c, d, y], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    intro a b c d x y h
    have hM := Matrix.det_fin_three (Matrix.of ![![a, b, x], ![c, d, y], ![0, 0, 1]])
    simp at hM
    exact hM.trans h
  let toMat : (Multiplicative (Fin 2 → ℤ) ⋊[a₂] Matrix.SpecialLinearGroup (Fin 2) ℤ) →
      Matrix.SpecialLinearGroup (Fin 3) ℤ := fun p =>
    let f : Fin 2 → Fin 2 → ℤ := (p.right : Matrix (Fin 2) (Fin 2) ℤ)
    ⟨![![f 0 0, f 0 1, Multiplicative.toAdd p.left 0],
       ![f 1 0, f 1 1, Multiplicative.toAdd p.left 1],
       ![0, 0, 1]],
      hdet3 (f 0 0) (f 0 1) (f 1 0) (f 1 1)
        (Multiplicative.toAdd p.left 0) (Multiplicative.toAdd p.left 1) (by
          have hA := Matrix.SpecialLinearGroup.det_coe p.right
          rw [Matrix.det_fin_two] at hA
          exact hA)⟩
  refine ⟨{
    toFun := toMat
    map_one' := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    map_mul' := fun p q => by
      ext a b
      change (toMat (p * q) : Matrix (Fin 3) (Fin 3) ℤ) a b =
        ((toMat p : Matrix (Fin 3) (Fin 3) ℤ) * (toMat q : Matrix (Fin 3) (Fin 3) ℤ)) a b
      have hmul2 : ∀ i j : Fin 2,
          ((p.right : Matrix (Fin 2) (Fin 2) ℤ) * (q.right : Matrix (Fin 2) (Fin 2) ℤ)) i j =
            (p.right : Matrix (Fin 2) (Fin 2) ℤ) i 0 * (q.right : Matrix (Fin 2) (Fin 2) ℤ) 0 j +
            (p.right : Matrix (Fin 2) (Fin 2) ℤ) i 1 * (q.right : Matrix (Fin 2) (Fin 2) ℤ) 1 j :=
        fun i j => by rw [Matrix.mul_apply, Fin.sum_univ_two]
      rw [Matrix.mul_apply, Fin.sum_univ_three]
      dsimp only [toMat]
      fin_cases a <;> fin_cases b <;> simp <;>
        (try (rw [ha₂]; simp)) <;> (try rw [hmul2]) <;> ring }, ?_, ?_⟩
  · intro k
    ext a b
    change (toMat (SemidirectProduct.inl (Multiplicative.ofAdd ![k, 0])) : Matrix (Fin 3) (Fin 3) ℤ) a b =
      Matrix.transvection 0 2 k a b
    rw [Matrix.transvection]
    dsimp only [toMat]
    fin_cases a <;> fin_cases b <;> simp
  · intro k
    ext a b
    change (toMat (SemidirectProduct.inl (Multiplicative.ofAdd ![0, k])) : Matrix (Fin 3) (Fin 3) ℤ) a b =
      Matrix.transvection 1 2 k a b
    rw [Matrix.transvection]
    dsimp only [toMat]
    fin_cases a <;> fin_cases b <;> simp

/- Cyclic conjugation of transvections (0,2) and (1,2) hits all six elementary root subgroups. -/
lemma exists_cyclic_shift_sl3 :
    ∃ P : Matrix.SpecialLinearGroup (Fin 3) ℤ,
      (∀ (E : Matrix.SpecialLinearGroup (Fin 3) ℤ) (k : ℤ),
        (E : Matrix (Fin 3) (Fin 3) ℤ) = Matrix.transvection 0 2 k →
        ((P * E * P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
          Matrix.transvection 1 0 k) ∧
      (∀ (E : Matrix.SpecialLinearGroup (Fin 3) ℤ) (k : ℤ),
        (E : Matrix (Fin 3) (Fin 3) ℤ) = Matrix.transvection 1 2 k →
        ((P * E * P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
          Matrix.transvection 2 0 k) ∧
      (∀ (E : Matrix.SpecialLinearGroup (Fin 3) ℤ) (k : ℤ),
        (E : Matrix (Fin 3) (Fin 3) ℤ) = Matrix.transvection 0 2 k →
        ((P⁻¹ * E * P : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
          Matrix.transvection 2 1 k) ∧
      (∀ (E : Matrix.SpecialLinearGroup (Fin 3) ℤ) (k : ℤ),
        (E : Matrix (Fin 3) (Fin 3) ℤ) = Matrix.transvection 1 2 k →
        ((P⁻¹ * E * P : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
          Matrix.transvection 0 1 k) := by
  let Pm : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]
  let Qm : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]
  have hPdet : Pm.det = 1 := by decide
  have hQdet : Qm.det = 1 := by decide
  have hPQ : Pm * Qm = 1 := by ext a b; fin_cases a <;> fin_cases b <;> decide
  have hQP : Qm * Pm = 1 := by ext a b; fin_cases a <;> fin_cases b <;> decide
  let P : Matrix.SpecialLinearGroup (Fin 3) ℤ := ⟨Pm, hPdet⟩
  let Q : Matrix.SpecialLinearGroup (Fin 3) ℤ := ⟨Qm, hQdet⟩
  have hPinv : P⁻¹ = Q := by
    apply inv_eq_of_mul_eq_one_right
    ext a b
    exact congrFun (congrFun hPQ a) b
  have hsingle_conj : ∀ (A B : Matrix (Fin 3) (Fin 3) ℤ) (i j a b : Fin 3) (k : ℤ),
      (A * Matrix.single i j k * B) a b = A a i * B j b * k := by
    intro A B i j a b k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.single_apply]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · split_ifs with h
        · ring
        · exact absurd ⟨rfl, rfl⟩ h
      · intro y _ hyi
        split_ifs with h
        · rcases h with ⟨rfl, _⟩; exact absurd rfl hyi
        · ring
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro x _ hxj
      rw [Finset.sum_eq_zero]
      · ring
      · intro y _
        split_ifs with h
        · rcases h with ⟨_, rfl⟩; exact absurd rfl hxj
        · ring
    · intro h; exact absurd (Finset.mem_univ j) h
  have hconj : ∀ (A B : Matrix (Fin 3) (Fin 3) ℤ) (i j i' j' : Fin 3) (k : ℤ),
      A * B = 1 →
      (∀ a b : Fin 3, A a i * B j b = if i' = a ∧ j' = b then 1 else 0) →
      A * Matrix.transvection i j k * B = Matrix.transvection i' j' k := by
    intro A B i j i' j' k hAB hentry
    rw [Matrix.transvection, Matrix.transvection, mul_add, mul_one, add_mul, hAB]
    congr 1
    ext a b
    rw [hsingle_conj, hentry a b, Matrix.single_apply]
    split_ifs <;> ring
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro E k hE; rw [hPinv]
    change Pm * (E : Matrix (Fin 3) (Fin 3) ℤ) * Qm = _
    rw [hE]; exact hconj Pm Qm 0 2 1 0 k hPQ (fun a b => by fin_cases a <;> fin_cases b <;> decide)
  · intro E k hE; rw [hPinv]
    change Pm * (E : Matrix (Fin 3) (Fin 3) ℤ) * Qm = _
    rw [hE]; exact hconj Pm Qm 1 2 2 0 k hPQ (fun a b => by fin_cases a <;> fin_cases b <;> decide)
  · intro E k hE; rw [hPinv]
    change Qm * (E : Matrix (Fin 3) (Fin 3) ℤ) * Pm = _
    rw [hE]; exact hconj Qm Pm 0 2 2 1 k hQP (fun a b => by fin_cases a <;> fin_cases b <;> decide)
  · intro E k hE; rw [hPinv]
    change Qm * (E : Matrix (Fin 3) (Fin 3) ℤ) * Pm = _
    rw [hE]; exact hconj Qm Pm 1 2 0 1 k hQP (fun a b => by fin_cases a <;> fin_cases b <;> decide)

theorem main : H1 → H2 → OMA.R_Green100_green_100_variants_operator_norm_R1_H1_R1.H1 := by
  intro hH1 hH2
  obtain ⟨a₂, ha₂⟩ := exists_sl_action 2
  obtain ⟨a₃, ha₃⟩ := exists_sl_action 3
  have hcount : Countable (Matrix.SpecialLinearGroup (Fin 3) ℤ) := by
    have : Countable (Matrix (Fin 3) (Fin 3) ℤ) := by
      change Countable (Fin 3 → Fin 3 → ℤ)
      infer_instance
    change Countable { A : Matrix (Fin 3) (Fin 3) ℤ // A.det = 1 }
    exact Subtype.countable
  refine ⟨Matrix.SpecialLinearGroup (Fin 3) ℤ, inferInstance, hcount, a₃, fg_of_elem_gen a₃ hH1, ?_⟩
  intro E _ _ _ ρ c hc
  obtain ⟨f₁, hf₁⟩ := (exists_lattice_embeddings a₂ ha₂ a₃ ha₃).1
  obtain ⟨f₂, hf₂⟩ := (exists_lattice_embeddings a₂ ha₂ a₃ ha₃).2
  obtain ⟨M₁, hM₁⟩ := hH2 a₂ ha₂ E (ρ.comp f₁) (c ∘ f₁)
    (fun g h => by simp only [Function.comp_apply, map_mul, MonoidHom.comp_apply]; exact hc (f₁ g) (f₁ h))
  obtain ⟨M₂, hM₂⟩ := hH2 a₂ ha₂ E (ρ.comp f₂) (c ∘ f₂)
    (fun g h => by simp only [Function.comp_apply, map_mul, MonoidHom.comp_apply]; exact hc (f₂ g) (f₂ h))
  have hlat_bdd : ∀ x : Multiplicative (Fin 3 → ℤ), ‖c (SemidirectProduct.inl x)‖ ≤ M₁ + M₂ := by
    intro x
    let v : Fin 3 → ℤ := Multiplicative.toAdd x
    have hx_split : x = Multiplicative.ofAdd ![v 0, v 1, 0] * Multiplicative.ofAdd ![0, 0, v 2] := by
      apply Multiplicative.toAdd.injective
      change v = ![v 0, v 1, 0] + ![0, 0, v 2]
      ext i; fin_cases i <;> simp
    rw [hx_split, map_mul, hc]
    have hb1 : ‖c (SemidirectProduct.inl (Multiplicative.ofAdd ![v 0, v 1, 0]))‖ ≤ M₁ := by
      have h := hM₁ (Multiplicative.ofAdd ![v 0, v 1])
      simpa only [Function.comp_apply, hf₁, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using h
    have hb2 : ‖c (SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, v 2]))‖ ≤ M₂ := by
      have h := hM₂ (Multiplicative.ofAdd ![0, v 2])
      simpa only [Function.comp_apply, hf₂, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using h
    calc ‖c (SemidirectProduct.inl (Multiplicative.ofAdd ![v 0, v 1, 0])) +
            ρ (SemidirectProduct.inl (Multiplicative.ofAdd ![v 0, v 1, 0]))
              (c (SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, v 2])))‖
        ≤ ‖c (SemidirectProduct.inl (Multiplicative.ofAdd ![v 0, v 1, 0]))‖ +
            ‖ρ (SemidirectProduct.inl (Multiplicative.ofAdd ![v 0, v 1, 0]))
              (c (SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, v 2])))‖ := norm_add_le _ _
      _ = ‖c (SemidirectProduct.inl (Multiplicative.ofAdd ![v 0, v 1, 0]))‖ +
            ‖c (SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, v 2]))‖ := by rw [(ρ _).norm_map]
      _ ≤ M₁ + M₂ := add_le_add hb1 hb2
  obtain ⟨φ, hφ02, hφ12⟩ := exists_col_embedding a₂ ha₂
  obtain ⟨P, hP02, hP12, hPi02, hPi12⟩ := exists_cyclic_shift_sl3
  let ψ₀ := SemidirectProduct.inr (N := Multiplicative (Fin 3 → ℤ)) (φ := a₃) |>.comp φ
  let ψ₁ := SemidirectProduct.inr (N := Multiplicative (Fin 3 → ℤ)) (φ := a₃) |>.comp
    ((MulAut.conj P).toMonoidHom.comp φ)
  let ψ₂ := SemidirectProduct.inr (N := Multiplicative (Fin 3 → ℤ)) (φ := a₃) |>.comp
    ((MulAut.conj P⁻¹).toMonoidHom.comp φ)
  obtain ⟨Ma, hMa⟩ := hH2 a₂ ha₂ E (ρ.comp ψ₀) (c ∘ ψ₀)
    (fun g h => by simp only [Function.comp_apply, map_mul, MonoidHom.comp_apply]; exact hc (ψ₀ g) (ψ₀ h))
  obtain ⟨Mb, hMb⟩ := hH2 a₂ ha₂ E (ρ.comp ψ₁) (c ∘ ψ₁)
    (fun g h => by simp only [Function.comp_apply, map_mul, MonoidHom.comp_apply]; exact hc (ψ₁ g) (ψ₁ h))
  obtain ⟨Mc, hMc⟩ := hH2 a₂ ha₂ E (ρ.comp ψ₂) (c ∘ ψ₂)
    (fun g h => by simp only [Function.comp_apply, map_mul, MonoidHom.comp_apply]; exact hc (ψ₂ g) (ψ₂ h))
  let Me : ℝ := max (max (max Ma Mb) Mc) 0
  have hMe0 : 0 ≤ Me := le_max_right _ _
  have helem_bdd : ∀ (i j : Fin 3) (_ : i ≠ j) (k : ℤ) (T : Matrix.SpecialLinearGroup (Fin 3) ℤ),
      (T : Matrix (Fin 3) (Fin 3) ℤ) = Matrix.transvection i j k →
      ‖c (SemidirectProduct.inr T)‖ ≤ Me := by
    intro i j hij k T hT
    have hMa_le : Ma ≤ Me := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    have hMb_le : Mb ≤ Me := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    have hMc_le : Mc ≤ Me := le_trans (le_max_right _ _) (le_max_left _ _)
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · have hEq : ψ₂ (SemidirectProduct.inl (Multiplicative.ofAdd ![0, k])) = SemidirectProduct.inr T := by
        show SemidirectProduct.inr ((MulAut.conj P⁻¹) (φ (SemidirectProduct.inl (Multiplicative.ofAdd ![0, k])))) =
          SemidirectProduct.inr T
        congr 1
        rw [MulAut.conj_apply, inv_inv]
        ext a b
        exact congrFun (congrFun ((hPi12 _ k (hφ12 k)).trans hT.symm) a) b
      rw [← hEq]; exact (hMc (Multiplicative.ofAdd ![0, k])).trans hMc_le
    · have hEq : ψ₀ (SemidirectProduct.inl (Multiplicative.ofAdd ![k, 0])) = SemidirectProduct.inr T := by
        show SemidirectProduct.inr (φ (SemidirectProduct.inl (Multiplicative.ofAdd ![k, 0]))) =
          SemidirectProduct.inr T
        congr 1
        ext a b
        exact congrFun (congrFun ((hφ02 k).trans hT.symm) a) b
      rw [← hEq]; exact (hMa (Multiplicative.ofAdd ![k, 0])).trans hMa_le
    · have hEq : ψ₁ (SemidirectProduct.inl (Multiplicative.ofAdd ![k, 0])) = SemidirectProduct.inr T := by
        show SemidirectProduct.inr ((MulAut.conj P) (φ (SemidirectProduct.inl (Multiplicative.ofAdd ![k, 0])))) =
          SemidirectProduct.inr T
        congr 1
        rw [MulAut.conj_apply]
        ext a b
        exact congrFun (congrFun ((hP02 _ k (hφ02 k)).trans hT.symm) a) b
      rw [← hEq]; exact (hMb (Multiplicative.ofAdd ![k, 0])).trans hMb_le
    · exact absurd rfl hij
    · have hEq : ψ₀ (SemidirectProduct.inl (Multiplicative.ofAdd ![0, k])) = SemidirectProduct.inr T := by
        show SemidirectProduct.inr (φ (SemidirectProduct.inl (Multiplicative.ofAdd ![0, k]))) =
          SemidirectProduct.inr T
        congr 1
        ext a b
        exact congrFun (congrFun ((hφ12 k).trans hT.symm) a) b
      rw [← hEq]; exact (hMa (Multiplicative.ofAdd ![0, k])).trans hMa_le
    · have hEq : ψ₁ (SemidirectProduct.inl (Multiplicative.ofAdd ![0, k])) = SemidirectProduct.inr T := by
        show SemidirectProduct.inr ((MulAut.conj P) (φ (SemidirectProduct.inl (Multiplicative.ofAdd ![0, k])))) =
          SemidirectProduct.inr T
        congr 1
        rw [MulAut.conj_apply]
        ext a b
        exact congrFun (congrFun ((hP12 _ k (hφ12 k)).trans hT.symm) a) b
      rw [← hEq]; exact (hMb (Multiplicative.ofAdd ![0, k])).trans hMb_le
    · have hEq : ψ₂ (SemidirectProduct.inl (Multiplicative.ofAdd ![k, 0])) = SemidirectProduct.inr T := by
        show SemidirectProduct.inr ((MulAut.conj P⁻¹) (φ (SemidirectProduct.inl (Multiplicative.ofAdd ![k, 0])))) =
          SemidirectProduct.inr T
        congr 1
        rw [MulAut.conj_apply, inv_inv]
        ext a b
        exact congrFun (congrFun ((hPi02 _ k (hφ02 k)).trans hT.symm) a) b
      rw [← hEq]; exact (hMc (Multiplicative.ofAdd ![k, 0])).trans hMc_le
    · exact absurd rfl hij
  obtain ⟨N, hN_gen⟩ := hH1
  have hc1 : c 1 = 0 := by
    have h1 := hc 1 1
    rw [mul_one, map_one] at h1
    change c 1 = c 1 + c 1 at h1
    have := sub_eq_zero.mpr h1.symm
    simpa using this
  have hlist_bdd : ∀ (l : List (Fin 3 × Fin 3 × ℤ)), (∀ e ∈ l, e.1 ≠ e.2.1) →
      ∀ (A : Matrix.SpecialLinearGroup (Fin 3) ℤ),
        (A : Matrix (Fin 3) (Fin 3) ℤ) =
          (l.map fun e => Matrix.transvection e.1 e.2.1 e.2.2).prod →
        ‖c (SemidirectProduct.inr A)‖ ≤ (l.length : ℝ) * Me := by
    intro l
    induction l with
    | nil =>
      intro _ A hA
      have hA1 : A = 1 := by
        ext a b
        simpa using congrFun (congrFun hA a) b
      rw [hA1, map_one, hc1, norm_zero]
      simp
    | cons e t ih =>
      intro hne A hA
      have he_ne : e.1 ≠ e.2.1 := hne e (by simp)
      have ht_ne : ∀ x ∈ t, x.1 ≠ x.2.1 := fun x hx => hne x (by simp [hx])
      let E : Matrix.SpecialLinearGroup (Fin 3) ℤ :=
        ⟨Matrix.transvection e.1 e.2.1 e.2.2, Matrix.det_transvection_of_ne e.1 e.2.1 he_ne e.2.2⟩
      let T : Matrix.SpecialLinearGroup (Fin 3) ℤ := E⁻¹ * A
      have hT_eq : (T : Matrix (Fin 3) (Fin 3) ℤ) =
          (t.map fun x => Matrix.transvection x.1 x.2.1 x.2.2).prod := by
        have hEinv : ((E⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
            (E : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
          change ((E⁻¹ * E : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = 1
          rw [inv_mul_cancel]; rfl
        calc (T : Matrix (Fin 3) (Fin 3) ℤ)
            = ((E⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
                (A : Matrix (Fin 3) (Fin 3) ℤ) := rfl
          _ = ((E⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
                ((E : Matrix (Fin 3) (Fin 3) ℤ) *
                  (t.map fun x => Matrix.transvection x.1 x.2.1 x.2.2).prod) := by
              rw [hA, List.map_cons, List.prod_cons]
          _ = (t.map fun x => Matrix.transvection x.1 x.2.1 x.2.2).prod := by
              rw [← Matrix.mul_assoc, hEinv, Matrix.one_mul]
      have hA_eq : A = E * T := by simp [T]
      rw [hA_eq, map_mul, hc, List.length_cons, Nat.cast_add, Nat.cast_one]
      have hEb : ‖c (SemidirectProduct.inr E)‖ ≤ Me := helem_bdd e.1 e.2.1 he_ne e.2.2 E rfl
      have hTb : ‖c (SemidirectProduct.inr T)‖ ≤ (t.length : ℝ) * Me := ih ht_ne T hT_eq
      calc ‖c (SemidirectProduct.inr E) + ρ (SemidirectProduct.inr E) (c (SemidirectProduct.inr T))‖
          ≤ ‖c (SemidirectProduct.inr E)‖ +
              ‖ρ (SemidirectProduct.inr E) (c (SemidirectProduct.inr T))‖ := norm_add_le _ _
        _ = ‖c (SemidirectProduct.inr E)‖ + ‖c (SemidirectProduct.inr T)‖ := by rw [(ρ _).norm_map]
        _ ≤ Me + (t.length : ℝ) * Me := add_le_add hEb hTb
        _ = ((t.length : ℝ) + 1) * Me := by ring
  have hsl_bdd : ∀ A : Matrix.SpecialLinearGroup (Fin 3) ℤ,
      ‖c (SemidirectProduct.inr A)‖ ≤ (N : ℝ) * Me := by
    intro A
    obtain ⟨l, hlen, hne, hprod⟩ := hN_gen A
    exact (hlist_bdd l hne A hprod).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlen) hMe0)
  have hfull_bdd : ∀ g : Multiplicative (Fin 3 → ℤ) ⋊[a₃] Matrix.SpecialLinearGroup (Fin 3) ℤ,
      ‖c g‖ ≤ (M₁ + M₂) + (N : ℝ) * Me := by
    intro g
    rw [← SemidirectProduct.inl_left_mul_inr_right g, hc]
    calc ‖c (SemidirectProduct.inl g.left) +
            ρ (SemidirectProduct.inl g.left) (c (SemidirectProduct.inr g.right))‖
        ≤ ‖c (SemidirectProduct.inl g.left)‖ +
            ‖ρ (SemidirectProduct.inl g.left) (c (SemidirectProduct.inr g.right))‖ := norm_add_le _ _
      _ = ‖c (SemidirectProduct.inl g.left)‖ + ‖c (SemidirectProduct.inr g.right)‖ := by rw [(ρ _).norm_map]
      _ ≤ (M₁ + M₂) + (N : ℝ) * Me := add_le_add (hlat_bdd g.left) (hsl_bdd g.right)
  exact chebyshev_center_of_bdd_cocycle ρ c hc ((M₁ + M₂) + (N : ℝ) * Me) hfull_bdd

end OMA.R_Green100_green_100_variants_operator_norm_R1_H1_R1_H1_R1
