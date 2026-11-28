import OMAStatements.S_mo_245516

-- Credit: @Pixelstorm44
namespace OMA.R_mo_245516_R1

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem coordinate {x : ℕ → X} (i : ℕ) (hx : ‖x i‖ = 1)
    (hr : 1 ≤ ‖((Submodule.span ℝ (x '' {j | j ≠ i})).topologicalClosure).mkQ (x i)‖) :
    ∃ f : X →L[ℝ] ℝ, ‖f‖ = 1 ∧ ∀ j, f (x j) = if i = j then 1 else 0 := by
  let K := (Submodule.span ℝ (x '' {j | j ≠ i})).topologicalClosure
  have hq : ‖K.mkQ (x i)‖ = 1 :=
    le_antisymm ((Submodule.Quotient.norm_mk_le K (x i)).trans hx.le) hr
  obtain ⟨g, hg, hval⟩ := exists_dual_vector ℝ (K.mkQ (x i)) (by rw [hq]; norm_num)
  let f := g.comp K.mkQL
  have hself : f (x i) = 1 := hval.trans (by simpa using hq)
  have hupper : ‖f‖ ≤ 1 := by
    apply f.opNorm_le_bound (by norm_num)
    intro v
    calc
      ‖f v‖ ≤ ‖g‖ * ‖K.mkQ v‖ := g.le_opNorm _
      _ ≤ 1 * ‖v‖ := by rw [hg]; exact mul_le_mul_of_nonneg_left
                                      (Submodule.Quotient.norm_mk_le K v) zero_le_one
  refine ⟨f, le_antisymm hupper ?_, ?_⟩
  · simpa [hself, hx] using f.le_opNorm (x i)
  · intro j
    split_ifs with hij
    · simpa [← hij] using hself
    · have hj : x j ∈ K := Submodule.le_topologicalClosure _ <|
        Submodule.subset_span ⟨j, Ne.symm hij, rfl⟩
      have hz : K.mkQ (x j) = 0 := (Submodule.Quotient.mk_eq_zero K).2 hj
      change g (K.mkQ (x j)) = 0
      simp [hz]

/-- Removing the first n coordinates maps the whole space into its closed tail span.
Only a finite sum is used, so no convergence of partial sums is assumed. -/
private theorem mem_tail_of_vanishing {x : ℕ → X} {f : ℕ → X →L[ℝ] ℝ}
    (hd : Dense (Submodule.span ℝ (Set.range x) : Set X))
    (hb : ∀ i j, f i (x j) = if i = j then 1 else 0)
    {v : X} (hv : ∀ i, f i v = 0) (n : ℕ) : v ∈ (Submodule.span ℝ (x '' Set.Ici n)).topologicalClosure := by
  classical
  let T : X →L[ℝ] X := ContinuousLinearMap.id ℝ X -
    ∑ i ∈ Finset.range n, (f i).smulRight (x i)
  have heval (w : X) : T w = w - ∑ i ∈ Finset.range n, f i w • x i := by
    simp [T]
  have hmap (j : ℕ) : T (x j) ∈ (Submodule.span ℝ (x '' Set.Ici n)).topologicalClosure := by
    rw [heval]
    by_cases hj : j < n
    · simp [hb, ite_smul, Finset.mem_range, hj]
    · have hzero (i : ℕ) (hi : i ∈ Finset.range n) : f i (x j) • x i = 0 := by
        have hij : i ≠ j := by intro he; exact hj (he ▸ Finset.mem_range.mp hi)
        simp [hb, hij]
      rw [Finset.sum_eq_zero hzero, sub_zero]
      exact Submodule.le_topologicalClosure _ <| Submodule.subset_span ⟨j, Nat.le_of_not_gt hj, rfl⟩
  let S := ((Submodule.span ℝ (x '' Set.Ici n)).topologicalClosure).comap T.toLinearMap
  have hspan : Submodule.span ℝ (Set.range x) ≤ S :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hmap j)
  have hc : IsClosed (S : Set X) :=
    (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hm : T v ∈ (Submodule.span ℝ (x '' Set.Ici n)).topologicalClosure := closure_minimal hspan hc (hd v)
  simpa [heval, hv] using hm

/-- Affine separation on finite linear combinations also holds on the closed
deleted span. Taking almost minimal representatives gives the quotient bound. -/
private theorem radius_of_tests {x : ℕ → X} {i : ℕ}
    (ht : ∀ c : ℕ →₀ ℝ, c i = 0 → 1 ≤ ‖x i - c.sum (fun j a => a • x j)‖) :
    1 ≤ ‖(Submodule.span ℝ (x '' {j | j ≠ i})).topologicalClosure.mkQ (x i)‖ := by
  let S := Submodule.span ℝ (x '' {j | j ≠ i})
  let K := S.topologicalClosure
  have hspan : (S : Set X) ⊆ {w : X | 1 ≤ ‖x i - w‖} := by
    intro w hw
    obtain ⟨c, hc, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hw
    apply ht
    exact (Finsupp.mem_supported' ℝ _).mp hc i (by simp)
  have hK : (K : Set X) ⊆ {w : X | 1 ≤ ‖x i - w‖} :=
    closure_minimal hspan (isClosed_le continuous_const (continuous_const.sub continuous_id).norm)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u, hu, hnorm⟩ := Submodule.Quotient.norm_mk_lt (K.mkQ (x i)) hε
  have hmem : x i - u ∈ K := (Submodule.Quotient.eq K).mp hu.symm
  have hdist : 1 ≤ ‖x i - (x i - u)‖ := hK hmem
  exact (show 1 ≤ ‖u‖ by simpa using hdist).trans hnorm.le

private theorem separation_of_coordinate {y : ℕ → X} {i : ℕ} {c : ℕ →₀ ℝ}
    (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (hi : f (y i) = 1)
    (hz : ∀ j ∈ c.support, f (y j) = 0) :
    1 ≤ ‖y i - c.sum (fun j a => a • y j)‖ := by
  have he : f (c.sum (fun j a => a • y j)) = 0 := by
    rw [Finsupp.sum, map_sum]
    exact Finset.sum_eq_zero fun j hj => by simp [hz j hj]
  have h := f.le_opNorm (y i - c.sum (fun j a => a • y j))
  rw [map_sub, he, hi, sub_zero, norm_one] at h
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) hf)

/-- Finite Auerbach systems. In a finite-dimensional subspace these can be
obtained by maximizing the absolute determinant on a product of unit balls. -/
def H1 : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X], ¬ FiniteDimensional ℝ X →
    ∀ s : Finset ℕ, ∃ y : ℕ → X, (∀ j ∈ s, ‖y j‖ = 1) ∧
      ∀ i ∈ s, ∃ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧
        ∀ j ∈ s, f (y j) = if i = j then 1 else 0

/-- Compact selection for finite affine separation tests. A test consists of
a distinguished index, coefficients vanishing there, and a radius below one.
The compact family is fixed before the finite list of tests is chosen. -/
def H2 : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X], ¬ FiniteDimensional ℝ X →
    ∃ K : Set (ℕ → X), IsCompact K ∧
      (∀ x ∈ K, Dense (Submodule.span ℝ (Set.range x) : Set X) ∧
        (∀ i, ‖x i‖ = 1) ∧ (∀ v : X,
          (∀ n : ℕ, v ∈ (Submodule.span ℝ (x '' Set.Ici n)).topologicalClosure) → v = 0)) ∧
      ∀ F : Finset (ℕ × (ℕ →₀ ℝ) × Set.Ioo (0 : ℝ) 1),
        (∃ y : ℕ → X, ∀ p ∈ F, p.2.1 p.1 = 0 →
          ‖y p.1‖ = 1 ∧ 1 ≤ ‖y p.1 - p.2.1.sum (fun j a => a • y j)‖) →
        ∃ x ∈ K, ∀ p ∈ F, p.2.1 p.1 = 0 →
          (p.2.2 : ℝ) ≤ ‖x p.1 - p.2.1.sum (fun j a => a • x j)‖

theorem main : H1 → H2 → type_of% @OMA.S_mo_245516.main := by
  classical
  intro finiteFrames selectFamily X _ _ _ _ hdim
  obtain ⟨K, hcompact, hgood, hselect⟩ := selectFamily X hdim
  let Test := ℕ × (ℕ →₀ ℝ) × Set.Ioo (0 : ℝ) 1
  let passes (p : Test) : Set (ℕ → X) :=
    {x | p.2.1 p.1 = 0 → (p.2.2 : ℝ) ≤ ‖x p.1 - p.2.1.sum (fun j a => a • x j)‖}
  have hclosed (p : Test) : IsClosed (passes p) := by
    by_cases hp : p.2.1 p.1 = 0
    · simp only [passes, hp, true_implies, Finsupp.sum]
      apply isClosed_le continuous_const
      exact ((continuous_apply p.1).sub (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).const_smul _)).norm
    · simp [passes, hp]
  have hfinite (F : Finset Test) : (K ∩ ⋂ p ∈ F, passes p).Nonempty := by
    let s := F.biUnion (fun p => insert p.1 p.2.1.support)
    obtain ⟨y, hy, hfun⟩ := finiteFrames X hdim s
    obtain ⟨x, hx, hp⟩ := hselect F (by
      refine ⟨y, ?_⟩
      intro p hF hzero
      have hs : insert p.1 p.2.1.support ⊆ s :=
        Finset.subset_biUnion_of_mem (fun q : Test => insert q.1 q.2.1.support) hF
      have hi := hs (Finset.mem_insert_self _ _)
      obtain ⟨f, hf, hfy⟩ := hfun p.1 hi
      refine ⟨hy _ hi, ?_⟩
      apply separation_of_coordinate f hf (by simp [hfy _ hi])
      intro j hj
      have hne : p.1 ≠ j := fun h => Finsupp.mem_support_iff.mp hj (h ▸ hzero)
      simp [hfy j (hs (Finset.mem_insert_of_mem hj)), hne])
    exact ⟨x, hx, Set.mem_iInter₂.mpr hp⟩
  obtain ⟨x, hxK, hall⟩ := hcompact.inter_iInter_nonempty passes hclosed hfinite
  obtain ⟨hd, hx, htail⟩ := hgood x hxK
  have hr (i : ℕ) (c : ℕ →₀ ℝ) (hc : c i = 0) : 1 ≤ ‖x i - c.sum (fun j a => a • x j)‖ := by
    by_contra! h
    obtain ⟨r, hlt, h1⟩ := exists_between h
    let p : Test := (i, c, ⟨r, (norm_nonneg _).trans_lt hlt, h1⟩)
    exact hlt.not_ge (Set.mem_iInter.mp hall p hc)
  choose f hn hb using fun i => coordinate i (hx i) (radius_of_tests (hr i))
  exact ⟨x, f, hd, hb, fun v hv => htail v (mem_tail_of_vanishing hd hb hv),
    fun i => ⟨hx i, hn i⟩⟩


/-- An actual basis supplies both finite frames and a singleton compact family.
Thus the compact selection requirement is also necessary. -/
theorem necessary (basisExists : type_of% @OMA.S_mo_245516.main) : H1 ∧ H2 := by
  constructor
  · intro X _ _ _ _ hdim s
    obtain ⟨x, f, _, hb, _, hn⟩ := basisExists X hdim
    exact ⟨x, fun i _ => (hn i).1, fun i _ =>
      ⟨f i, (hn i).2.le, fun j _ => hb i j⟩⟩
  · intro X _ _ _ _ hdim
    obtain ⟨x, f, hd, hb, ht, hn⟩ := basisExists X hdim
    refine ⟨{x}, isCompact_singleton, ?_, ?_⟩
    · intro w hw
      have hwx : w = x := hw
      subst w
      refine ⟨hd, fun i => (hn i).1, fun v hv => ht v fun i => ?_⟩
      have hker : (Submodule.span ℝ (x '' Set.Ici (i+1))).topologicalClosure ≤
          (f i).ker := by
        apply Submodule.topologicalClosure_minimal _ _ (f i).isClosed_ker
        apply Submodule.span_le.mpr
        rintro _ ⟨j, hj, rfl⟩
        have hij : i ≠ j := Nat.ne_of_lt (show i < j from hj)
        change f i (x j) = 0
        simp [hb, hij]
      exact hker (hv (i+1))
    · intro F _
      refine ⟨x, Set.mem_singleton _, ?_⟩
      intro p _ hzero
      apply p.2.2.property.2.le.trans
      apply separation_of_coordinate (f p.1) (hn p.1).2.le (by simp [hb])
      intro j hj
      have hij : p.1 ≠ j := fun h => Finsupp.mem_support_iff.mp hj (h ▸ hzero)
      simp [hb, hij]

end OMA.R_mo_245516_R1
