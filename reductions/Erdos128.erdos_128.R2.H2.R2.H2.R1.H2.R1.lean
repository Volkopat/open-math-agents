import OMAReductions.R_Erdos128_erdos_128_R2_H2_R2_H2_R1

/-!
# Reduction Erdos128.erdos_128.R2.H2.R2.H2.R1.H2.R1 of Erdos128.erdos_128.R2.H2.R2.H2.R1.H2

Reduces the weighted fractional sparse-half problem on higher Vega graphs `Υᵢ⁰⁰` (`i ≥ 3`)
by proving directly inside `main` (zero `sorry`):
1. Random-half cutoff (`random_half_sparse`): if `25 * Q(w) ≤ 4`, then `s = (1/2) * w` succeeds.
2. Independent-set `≥ 1/2` cutoff (`indep_ge_half_sparse`): any independent set of weight `≥ 1/2`
   gives an edge-free sparse half `Q(s) = 0`.
3. Continuous Razborov Theorem A (`continuous_razborov_two_fifths`): for ANY finite weighted
   triangle-free graph `(V, R, w)`, if any independent set has weight `≥ 2/5`, then a fractional
   sparse half `s` with `25 * Q(s) ≤ 1` exists. Hence every counterexample satisfies
   `w(I) < 2/5` for every independent set `I` (in particular every vertex neighborhood has
   weighted degree `< 2/5`).
4. Exact Vega involution symmetry `τ₁` (`vega_tau1_symmetry`): swaps `B₀ = {0, 2, 4, 7}` and
   `B₁ = {1, 3, 5, 6}` while fixing `Fin (3 * i - 1)` pointwise, preserving all constraints and
   forcing `w(B₀) ≤ w(B₁)`.
5. Exact zero-weight core folds `Υ_{i+1}⁰⁰ → Υᵢ⁰⁰` (`i ≥ 3`) via `hom_pullback_sparse_half`:
   whenever any vertex of `P₂` or any interior vertex of `P₀` or `P₁` has weight `0`, the graph
   homomorphically folds onto `Υᵢ⁰⁰` fixing `Fin 8` pointwise, preserving all gadget weights and
   pulling back any sparse half without increasing quadratic cost. By strong induction on `i ≥ 3`,
   every `i ≥ 4` instance reduces to strictly positive core weights on `P₂ ∪ P₀° ∪ P₁°`.

Splits the remaining instances cleanly into 3 strictly reduced hypotheses:
- `H1`: Base 16-vertex Vega graph `Υ₃⁰⁰` (`i = 3`) with `4 < 25 * Q(w)`, `w(B₀) ≤ w(B₁)`,
  and `w(I) < 2/5` for all independent sets `I`.
- `H2`: Higher Vega graphs `Υᵢ⁰⁰` (`i ≥ 4`) in the gadget-heavy regime `w(Γᵢ) ≤ 1/2`, with
  strictly positive core weights on `P₂ ∪ P₀° ∪ P₁°`, `4 < 25 * Q(w)`, `w(B₀) ≤ w(B₁)`,
  and `w(I) < 2/5` for all independent sets `I`.
- `H3`: Higher Vega graphs `Υᵢ⁰⁰` (`i ≥ 4`) in the Andrásfai-heavy regime `1/2 < w(Γᵢ)`, with
  the same strictly positive core weights and structural cuts.
-/

-- Credit: @sanchan

namespace OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1_H2_R1

open scoped Classical

def H1 : Prop :=
  let adj : Fin 8 ⊕ Fin 8 → Fin 8 ⊕ Fin 8 → Prop := fun x y =>
    match x, y with
    | Sum.inl p, Sum.inl q =>
        3 ≤ (q.val + 8 - p.val) % 8 ∧ (q.val + 8 - p.val) % 8 ≤ 5
    | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
        ((t.val = 0 ∨ t.val = 3) ∧ p.val < 3) ∨
        ((t.val = 4 ∨ t.val = 1) ∧ 3 ≤ p.val ∧ p.val < 6) ∨
        ((t.val = 2 ∨ t.val = 5) ∧ 6 ≤ p.val)
    | Sum.inr t₁, Sum.inr t₂ =>
        (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
        (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
        (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
        (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
        (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
  ∀ w : Fin 8 ⊕ Fin 8 → ℝ,
    (∀ z, 0 ≤ w z) → (∑ z, w z) = 1 →
    0 < w (Sum.inr 0) + w (Sum.inr 1) →
    0 < w (Sum.inr 3) + w (Sum.inr 4) →
    0 < w (Sum.inr 1) + w (Sum.inr 6) →
    0 < w (Sum.inr 4) + w (Sum.inr 7) →
    w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 4) + w (Sum.inr 7) ≤
      w (Sum.inr 1) + w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 6) →
    4 < 25 * (∑ x, ∑ y, if adj x y then w x * w y else 0) →
    (∀ I : Finset (Fin 8 ⊕ Fin 8), (∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) → (∑ z ∈ I, w z) < 2 / 5) →
    ∃ s : Fin 8 ⊕ Fin 8 → ℝ,
      (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x, ∑ y, if adj x y then s x * s y else 0) ≤ 1

def H2 : Prop :=
  ∀ (i : ℕ), 4 ≤ i →
    let adj : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    ∀ w : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
      (∀ z, 0 ≤ w z) → (∑ z, w z) = 1 →
      0 < w (Sum.inr 0) + w (Sum.inr 1) →
      0 < w (Sum.inr 3) + w (Sum.inr 4) →
      0 < w (Sum.inr 1) + w (Sum.inr 6) →
      0 < w (Sum.inr 4) + w (Sum.inr 7) →
      w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 4) + w (Sum.inr 7) ≤
        w (Sum.inr 1) + w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 6) →
      (∑ p : Fin (3 * i - 1), w (Sum.inl p)) ≤ 1 / 2 →
      (∀ p : Fin (3 * i - 1), (1 ≤ p.val ∧ p.val < i - 1) ∨ (i + 1 ≤ p.val ∧ p.val < 2 * i - 1) ∨
        2 * i ≤ p.val → 0 < w (Sum.inl p)) →
      4 < 25 * (∑ x, ∑ y, if adj x y then w x * w y else 0) →
      (∀ I : Finset (Fin (3 * i - 1) ⊕ Fin 8),
        (∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) → (∑ z ∈ I, w z) < 2 / 5) →
      ∃ s : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
        (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
        25 * (∑ x, ∑ y, if adj x y then s x * s y else 0) ≤ 1

def H3 : Prop :=
  ∀ (i : ℕ), 4 ≤ i →
    let adj : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    ∀ w : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
      (∀ z, 0 ≤ w z) → (∑ z, w z) = 1 →
      0 < w (Sum.inr 0) + w (Sum.inr 1) →
      0 < w (Sum.inr 3) + w (Sum.inr 4) →
      0 < w (Sum.inr 1) + w (Sum.inr 6) →
      0 < w (Sum.inr 4) + w (Sum.inr 7) →
      w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 4) + w (Sum.inr 7) ≤
        w (Sum.inr 1) + w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 6) →
      1 / 2 < (∑ p : Fin (3 * i - 1), w (Sum.inl p)) →
      (∀ p : Fin (3 * i - 1), (1 ≤ p.val ∧ p.val < i - 1) ∨ (i + 1 ≤ p.val ∧ p.val < 2 * i - 1) ∨
        2 * i ≤ p.val → 0 < w (Sum.inl p)) →
      4 < 25 * (∑ x, ∑ y, if adj x y then w x * w y else 0) →
      (∀ I : Finset (Fin (3 * i - 1) ⊕ Fin 8),
        (∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) → (∑ z ∈ I, w z) < 2 / 5) →
      ∃ s : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
        (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
        25 * (∑ x, ∑ y, if adj x y then s x * s y else 0) ≤ 1

/- ### Part 1: General Weighted Fractional Sparse-Half Theorems -/

theorem random_half_sparse {V : Type*} [Fintype V]
    (R : V → V → Prop) [DecidableRel R]
    (w : V → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hwsum : (∑ z, w z) = 1)
    (hQ : 25 * (∑ x : V, ∑ y : V, if R x y then w x * w y else 0) ≤ 4) :
    ∃ s : V → ℝ, (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x : V, ∑ y : V, if R x y then s x * s y else 0) ≤ 1 := by
  refine ⟨fun z => (1 / 2) * w z, fun z => ⟨by linarith [hw0 z], by linarith [hw0 z]⟩, ?_, ?_⟩
  · rw [← Finset.mul_sum, hwsum]; ring
  · have hscale : (∑ x : V, ∑ y : V, if R x y then ((1 / 2) * w x) * ((1 / 2) * w y) else 0) =
        (1 / 4) * (∑ x : V, ∑ y : V, if R x y then w x * w y else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> ring
    rw [hscale]
    linarith

theorem indep_ge_half_sparse {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R]
    (w : V → ℝ) (hw0 : ∀ z, 0 ≤ w z)
    (I : Finset V) (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ R x y) (hIw : 1 / 2 ≤ ∑ z ∈ I, w z) :
    ∃ s : V → ℝ, (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x : V, ∑ y : V, if R x y then s x * s y else 0) ≤ 1 := by
  set α := ∑ z ∈ I, w z
  have hα_pos : 0 < α := by linarith
  have hc0 : 0 ≤ 1 / (2 * α) := by positivity
  have hc1 : 1 / (2 * α) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  refine ⟨fun z => if z ∈ I then (1 / (2 * α)) * w z else 0, ?_, ?_, ?_⟩
  · intro z
    dsimp only
    split_ifs
    · exact ⟨mul_nonneg hc0 (hw0 z), by nlinarith [hw0 z]⟩
    · exact ⟨le_refl 0, hw0 z⟩
  · rw [← Finset.sum_filter]
    have hfilt : Finset.univ.filter (fun z => z ∈ I) = I := by
      ext z; simp
    rw [hfilt, ← Finset.mul_sum]
    change (1 / (2 * α)) * α = 1 / 2
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    field_simp
  · have hzero : (∑ x : V, ∑ y : V,
        if R x y then (if x ∈ I then (1 / (2 * α)) * w x else 0) *
          (if y ∈ I then (1 / (2 * α)) * w y else 0) else 0) = 0 := by
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
      split_ifs with hR hx hy
      · exact False.elim (hI x hx y hy hR)
      · ring
      · ring
      · ring
      · rfl
    rw [hzero]
    norm_num

theorem continuous_razborov_two_fifths {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R]
    (hSymm : ∀ x y, R x y → R y x)
    (hTF : ∀ x y z, R x y → R y z → ¬ R x z)
    (w : V → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hwsum : (∑ z, w z) = 1)
    (I₀ : Finset V) (hI₀ : ∀ x ∈ I₀, ∀ y ∈ I₀, ¬ R x y) (hI₀w : 2 / 5 ≤ ∑ z ∈ I₀, w z) :
    ∃ s : V → ℝ, (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x : V, ∑ y : V, if R x y then s x * s y else 0) ≤ 1 := by
  let indepSet : Finset (Finset V) :=
    Finset.univ.filter (fun S : Finset V => ∀ x ∈ S, ∀ y ∈ S, ¬ R x y)
  have hI₀_mem : I₀ ∈ indepSet := by
    simp only [indepSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hI₀
  obtain ⟨I, hI_mem, hI_max⟩ :=
    Finset.exists_max_image indepSet (fun S => ∑ z ∈ S, w z) ⟨I₀, hI₀_mem⟩
  have hI : ∀ x ∈ I, ∀ y ∈ I, ¬ R x y := (Finset.mem_filter.mp hI_mem).2
  have hα_max : ∀ S : Finset V, (∀ x ∈ S, ∀ y ∈ S, ¬ R x y) → (∑ z ∈ S, w z) ≤ ∑ z ∈ I, w z := by
    intro S hS
    exact hI_max S (by simp only [indepSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact hS)
  set α := ∑ z ∈ I, w z
  have hα_ge : 2 / 5 ≤ α := le_trans hI₀w (hα_max I₀ hI₀)
  by_cases hα_half : 1 / 2 ≤ α
  · exact indep_ge_half_sparse R w hw0 I hI hα_half
  push Not at hα_half
  set r := 1 / 2 - α with hr_def
  have hr_pos : 0 < r := by linarith
  have h25αr : 25 * (α * r) ≤ 1 := by
    have hsq : 0 ≤ (α - 2 / 5) * (α - 1 / 10) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  let degA : Finset V → V → ℝ := fun A v => ∑ x ∈ A, if R v x then w x else 0
  let R1 : Finset V := (Finset.univ \ I).filter (fun v => α < 2 * degA I v)
  let R0 : Finset V := (Finset.univ \ I).filter (fun v => ¬ (α < 2 * degA I v))
  have hR1_sub : R1 ⊆ Finset.univ \ I := Finset.filter_subset _ _
  have hR0_sub : R0 ⊆ Finset.univ \ I := Finset.filter_subset _ _
  have hdisj_IR1 : Disjoint I R1 :=
    Finset.disjoint_left.mpr fun x hxI hxR1 => (Finset.mem_sdiff.mp (hR1_sub hxR1)).2 hxI
  have hdisj_IR0 : Disjoint I R0 :=
    Finset.disjoint_left.mpr fun x hxI hxR0 => (Finset.mem_sdiff.mp (hR0_sub hxR0)).2 hxI
  have hdisj_R1R0 : Disjoint R1 R0 :=
    Finset.disjoint_left.mpr fun x hx1 hx0 =>
      (Finset.mem_filter.mp hx0).2 (Finset.mem_filter.mp hx1).2
  have hunion_R : R1 ∪ R0 = Finset.univ \ I := by
    ext x
    simp only [R1, R0, Finset.mem_union, Finset.mem_filter]
    tauto
  have hR1_indep : ∀ u ∈ R1, ∀ v ∈ R1, ¬ R u v := by
    intro u hu v hv huv
    have hu' : α < 2 * degA I u := (Finset.mem_filter.mp hu).2
    have hv' : α < 2 * degA I v := (Finset.mem_filter.mp hv).2
    have hsum_le : degA I u + degA I v ≤ α := by
      dsimp only [degA, α]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs with hux hvx
      · exact False.elim (hTF u x v hux (hSymm v x hvx) huv)
      · linarith [hw0 x]
      · linarith [hw0 x]
      · linarith [hw0 x]
    linarith
  set m1 := ∑ z ∈ R1, w z
  set m0 := ∑ z ∈ R0, w z
  have hm1_le : m1 ≤ α := hα_max R1 hR1_indep
  set r1 := 1 / 2 - m1 with hr1_def
  have hr1_ge : r ≤ r1 := by linarith
  have hr1_pos : 0 < r1 := by linarith
  have hpart : α + m1 + m0 = 1 := by
    have h1 : m1 + m0 = ∑ z ∈ Finset.univ \ I, w z := by
      rw [← Finset.sum_union hdisj_R1R0, hunion_R]
    have h2 : α + ∑ z ∈ Finset.univ \ I, w z = ∑ z : V, w z := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ I)]
    linarith
  have hm0_eq : m0 = r + r1 := by linarith
  have hm0_pos : 0 < m0 := by linarith
  have hr_le_m0 : r ≤ m0 := by linarith
  have hr1_le_m0 : r1 ≤ m0 := by linarith
  -- Reusable mixture evaluation lemma for independent A disjoint from B
  have hmix : ∀ (A B : Finset V), Disjoint A B → (∀ x ∈ A, ∀ y ∈ A, ¬ R x y) →
      ∀ (c : ℝ), 0 ≤ c → c ≤ 1 →
      (∑ z ∈ A, w z) + c * (∑ z ∈ B, w z) = 1 / 2 →
      2 * c * (∑ v ∈ B, w v * degA A v) +
        c ^ 2 * (∑ u ∈ B, ∑ v ∈ B, if R u v then w u * w v else 0) ≤ α * r →
      ∃ s : V → ℝ, (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
        25 * (∑ x : V, ∑ y : V, if R x y then s x * s y else 0) ≤ 1 := by
    intro A B hAB hA c hc0 hc1 hsum hcost
    let s : V → ℝ := fun z => if z ∈ A then w z else if z ∈ B then c * w z else 0
    refine ⟨s, ?_, ?_, ?_⟩
    · intro z
      dsimp only [s]
      split_ifs
      · exact ⟨hw0 z, le_refl _⟩
      · exact ⟨mul_nonneg hc0 (hw0 z), by nlinarith [hw0 z]⟩
      · exact ⟨le_refl 0, hw0 z⟩
    · have hs_supp : ∑ z : V, s z = ∑ z ∈ A ∪ B, s z := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun z _ hz => ?_
        simp only [Finset.mem_union, not_or] at hz
        simp only [s, if_neg hz.1, if_neg hz.2]
      rw [hs_supp, Finset.sum_union hAB]
      have hSA : ∑ z ∈ A, s z = ∑ z ∈ A, w z :=
        Finset.sum_congr rfl fun z hz => by simp only [s, if_pos hz]
      have hSB : ∑ z ∈ B, s z = c * ∑ z ∈ B, w z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z hz => ?_
        have hzA : z ∉ A := Finset.disjoint_right.mp hAB hz
        simp only [s, if_neg hzA, if_pos hz]
      rw [hSA, hSB, hsum]
    · have hQ_eq : (∑ x : V, ∑ y : V, if R x y then s x * s y else 0) =
          2 * c * (∑ v ∈ B, w v * degA A v) +
            c ^ 2 * (∑ u ∈ B, ∑ v ∈ B, if R u v then w u * w v else 0) := by
        have hsupp_xy : (∑ x : V, ∑ y : V, if R x y then s x * s y else 0) =
            ∑ x ∈ A ∪ B, ∑ y ∈ A ∪ B, if R x y then s x * s y else 0 := by
          symm
          refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) ?_ ?_
          · intro x hx
            have hx' : x ∉ A ∧ x ∉ B := by simpa [Finset.mem_sdiff, Finset.mem_union, not_or] using hx
            refine Finset.sum_eq_zero fun y _ => ?_
            simp only [s, if_neg hx'.1, if_neg hx'.2, zero_mul, ite_self]
          · intro x _
            refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
            simp only [Finset.mem_union, not_or] at hy
            simp only [s, if_neg hy.1, if_neg hy.2, mul_zero, ite_self]
        rw [hsupp_xy, Finset.sum_union hAB]
        simp_rw [Finset.sum_union hAB]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hAA : (∑ x ∈ A, ∑ y ∈ A, if R x y then s x * s y else 0) = 0 :=
          Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => if_neg (hA x hx y hy)
        have hBA : (∑ v ∈ B, ∑ x ∈ A, if R v x then s v * s x else 0) =
            c * (∑ v ∈ B, w v * degA A v) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v hv => ?_
          have hvA : v ∉ A := Finset.disjoint_right.mp hAB hv
          dsimp only [degA]
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          simp only [s, if_neg hvA, if_pos hv, if_pos hx]
          split_ifs <;> ring
        have hAB_term : (∑ x ∈ A, ∑ v ∈ B, if R x v then s x * s v else 0) =
            c * (∑ v ∈ B, w v * degA A v) := by
          rw [Finset.sum_comm, ← hBA]
          refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun x _ => ?_
          by_cases h : R x v
          · rw [if_pos h, if_pos (hSymm x v h), mul_comm]
          · rw [if_neg h, if_neg (fun h' => h (hSymm v x h'))]
        have hBB : (∑ u ∈ B, ∑ v ∈ B, if R u v then s u * s v else 0) =
            c ^ 2 * (∑ u ∈ B, ∑ v ∈ B, if R u v then w u * w v else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v hv => ?_
          have huA : u ∉ A := Finset.disjoint_right.mp hAB hu
          have hvA : v ∉ A := Finset.disjoint_right.mp hAB hv
          simp only [s, if_neg huA, if_pos hu, if_neg hvA, if_pos hv]
          split_ifs <;> ring
        rw [hAA, hAB_term, hBA, hBB]
        ring
      rw [hQ_eq]
      linarith
  -- Maximize independent subset J ⊆ R0
  let indepR0 : Finset (Finset V) :=
    R0.powerset.filter (fun S : Finset V => ∀ x ∈ S, ∀ y ∈ S, ¬ R x y)
  have hempty_mem : (∅ : Finset V) ∈ indepR0 := by
    simp only [indepR0, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, by simp⟩
  obtain ⟨J, hJ_mem, hJ_max⟩ :=
    Finset.exists_max_image indepR0 (fun S => ∑ z ∈ S, w z) ⟨∅, hempty_mem⟩
  have hJ_sub : J ⊆ R0 := Finset.mem_powerset.mp (Finset.mem_filter.mp hJ_mem).1
  have hJ_indep : ∀ x ∈ J, ∀ y ∈ J, ¬ R x y := (Finset.mem_filter.mp hJ_mem).2
  set β := ∑ z ∈ J, w z
  by_cases hrβ : r ≤ β
  · -- Case r ≤ β: mix I with scaled J
    have hβ_pos : 0 < β := by linarith
    have hc0 : 0 ≤ r / β := div_nonneg (le_of_lt hr_pos) (le_of_lt hβ_pos)
    have hc1 : r / β ≤ 1 := (div_le_one hβ_pos).mpr hrβ
    have hdisj_IJ : Disjoint I J := Finset.disjoint_of_subset_right hJ_sub hdisj_IR0
    have hsum_IJ : α + (r / β) * β = 1 / 2 := by
      have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
      field_simp; linarith
    have hJJ_zero : (∑ u ∈ J, ∑ v ∈ J, if R u v then w u * w v else 0) = 0 :=
      Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => if_neg (hJ_indep u hu v hv)
    have hIJ_cost : 2 * (r / β) * (∑ v ∈ J, w v * degA I v) +
        (r / β) ^ 2 * (∑ u ∈ J, ∑ v ∈ J, if R u v then w u * w v else 0) ≤ α * r := by
      rw [hJJ_zero, mul_zero, add_zero]
      have hdeg_le : 2 * (∑ v ∈ J, w v * degA I v) ≤ β * α := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun v hv => ?_
        have hvR0 : v ∈ R0 := hJ_sub hv
        have h2d : 2 * degA I v ≤ α := by
          have := (Finset.mem_filter.mp hvR0).2
          linarith
        nlinarith [hw0 v]
      have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
      have h1 : 2 * (r / β) * (∑ v ∈ J, w v * degA I v) = (r / β) * (2 * (∑ v ∈ J, w v * degA I v)) := by ring
      rw [h1]
      calc (r / β) * (2 * (∑ v ∈ J, w v * degA I v))
          ≤ (r / β) * (β * α) := mul_le_mul_of_nonneg_left hdeg_le hc0
        _ = α * r := by field_simp
    exact hmix I J hdisj_IJ hI (r / β) hc0 hc1 hsum_IJ hIJ_cost
  · -- Case β < r: exact algebraic contradiction between (I, R0) and (R1, R0)
    push Not at hrβ
    set e1 := ∑ v ∈ R0, w v * degA I v
    set e2 := ∑ v ∈ R0, w v * degA R1 v
    set d0 := ∑ u ∈ R0, ∑ v ∈ R0, if R u v then w u * w v else 0
    -- (F1): e1 + e2 + d0 ≤ m0 * α
    have hF1 : e1 + e2 + d0 ≤ m0 * α := by
      have hd0_eq : d0 = ∑ v ∈ R0, w v * degA R0 v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        dsimp only [degA]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        split_ifs <;> ring
      rw [hd0_eq]
      dsimp only [e1, e2, m0]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      have htot : degA I v + degA R1 v + degA R0 v ≤ α := by
        dsimp only [degA]
        rw [add_assoc, ← Finset.sum_union hdisj_R1R0, hunion_R,
            ← Finset.sum_union Finset.disjoint_sdiff,
            Finset.union_sdiff_of_subset (Finset.subset_univ I), ← Finset.sum_filter]
        refine hα_max (Finset.univ.filter (R v)) fun x hx y hy hxy => ?_
        exact hTF x v y (hSymm v x (Finset.mem_filter.mp hx).2) (Finset.mem_filter.mp hy).2 hxy
      nlinarith [hw0 v]
    -- (F2): e1 ≤ α * r
    have hF2 : e1 ≤ α * r := by
      have he1_swap : e1 = ∑ x ∈ I, w x * (∑ v ∈ R0.filter (R x), w v) := by
        dsimp only [e1, degA]
        have h1 : (∑ v ∈ R0, w v * ∑ x ∈ I, if R v x then w x else 0) =
            ∑ v ∈ R0, ∑ x ∈ I, if R v x then w v * w x else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          split_ifs <;> ring
        rw [h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter (s := R0)]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases h : R v x
        · rw [if_pos h, if_pos (hSymm v x h), mul_comm]
        · rw [if_neg h, if_neg (fun h' => h (hSymm x v h'))]
      rw [he1_swap]
      dsimp only [α]
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun x _ => ?_
      have hNx_mem : R0.filter (R x) ∈ indepR0 := by
        simp only [indepR0, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.filter_subset _ _, fun u hu v hv huv => ?_⟩
        exact hTF u x v (hSymm x u hu.2) hv.2 huv
      have hNx_le : (∑ v ∈ R0.filter (R x), w v) ≤ r := le_trans (hJ_max _ hNx_mem) (le_of_lt hrβ)
      exact mul_le_mul_of_nonneg_left hNx_le (hw0 x)
    -- Test mixture (I, R0, r / m0)
    by_cases hcost1 : 2 * (r / m0) * e1 + (r / m0) ^ 2 * d0 ≤ α * r
    · have hsum1 : α + (r / m0) * m0 = 1 / 2 := by
        have hm0_ne : m0 ≠ 0 := ne_of_gt hm0_pos
        field_simp; linarith
      exact hmix I R0 hdisj_IR0 hI (r / m0)
        (div_nonneg (le_of_lt hr_pos) (le_of_lt hm0_pos))
        ((div_le_one hm0_pos).mpr hr_le_m0) hsum1 hcost1
    -- Test mixture (R1, R0, r1 / m0)
    by_cases hcost2 : 2 * (r1 / m0) * e2 + (r1 / m0) ^ 2 * d0 ≤ α * r
    · have hsum2 : m1 + (r1 / m0) * m0 = 1 / 2 := by
        have hm0_ne : m0 ≠ 0 := ne_of_gt hm0_pos
        field_simp; linarith
      exact hmix R1 R0 hdisj_R1R0 hR1_indep (r1 / m0)
        (div_nonneg (le_of_lt hr1_pos) (le_of_lt hm0_pos))
        ((div_le_one hm0_pos).mpr hr1_le_m0) hsum2 hcost2
    -- Both mixtures fail: exact algebraic identity contradiction
    push Not at hcost1 hcost2
    have hm0_ne : m0 ≠ 0 := ne_of_gt hm0_pos
    have hF3 : α * m0 ^ 2 < 2 * m0 * e1 + r * d0 := by
      have hm : α * r * m0 ^ 2 < (2 * (r / m0) * e1 + (r / m0) ^ 2 * d0) * m0 ^ 2 :=
        mul_lt_mul_of_pos_right hcost1 (pow_pos hm0_pos 2)
      have hsimp : (2 * (r / m0) * e1 + (r / m0) ^ 2 * d0) * m0 ^ 2 = r * (2 * m0 * e1 + r * d0) := by
        field_simp
      rw [hsimp] at hm
      nlinarith
    have hF4 : α * r * m0 ^ 2 < 2 * r1 * m0 * e2 + r1 ^ 2 * d0 := by
      have hm : α * r * m0 ^ 2 < (2 * (r1 / m0) * e2 + (r1 / m0) ^ 2 * d0) * m0 ^ 2 :=
        mul_lt_mul_of_pos_right hcost2 (pow_pos hm0_pos 2)
      have hsimp : (2 * (r1 / m0) * e2 + (r1 / m0) ^ 2 * d0) * m0 ^ 2 = 2 * r1 * m0 * e2 + r1 ^ 2 * d0 := by
        field_simp
      linarith
    have hcomb :
        (r1 * (2 * r + r1)) * (2 * m0 * e1 + r * d0 - α * m0 ^ 2) +
        r * (2 * r1 * m0 * e2 + r1 ^ 2 * d0 - α * r * m0 ^ 2) +
        (2 * r * r1 * m0) * (m0 * α - e1 - e2 - d0) +
        (2 * r1 * m0 ^ 2) * (α * r - e1) =
        -(α * m0 ^ 2 * (r1 - r) ^ 2) := by
      rw [hm0_eq]; ring
    have ht1 : 0 < (r1 * (2 * r + r1)) * (2 * m0 * e1 + r * d0 - α * m0 ^ 2) :=
      mul_pos (mul_pos hr1_pos (add_pos (mul_pos zero_lt_two hr_pos) hr1_pos)) (sub_pos.mpr hF3)
    have ht2 : 0 < r * (2 * r1 * m0 * e2 + r1 ^ 2 * d0 - α * r * m0 ^ 2) :=
      mul_pos hr_pos (sub_pos.mpr hF4)
    have ht3 : 0 ≤ (2 * r * r1 * m0) * (m0 * α - e1 - e2 - d0) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (le_of_lt hr_pos)) (le_of_lt hr1_pos)) (le_of_lt hm0_pos))
        (by linarith [hF1])
    have ht4 : 0 ≤ (2 * r1 * m0 ^ 2) * (α * r - e1) :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (le_of_lt hr1_pos)) (sq_nonneg m0)) (sub_nonneg.mpr hF2)
    have hα_pos : 0 < α := lt_of_lt_of_le (by norm_num) hα_ge
    have hrhs : -(α * m0 ^ 2 * (r1 - r) ^ 2) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg (mul_nonneg (le_of_lt hα_pos) (sq_nonneg m0)) (sq_nonneg (r1 - r)))
    linarith [hcomb, ht1, ht2, ht3, ht4, hrhs]

theorem hom_pullback_sparse_half {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂]
    (R₁ : V₁ → V₁ → Prop) [DecidableRel R₁]
    (R₂ : V₂ → V₂ → Prop) [DecidableRel R₂]
    (w : V₁ → ℝ) (hw0 : ∀ z, 0 ≤ w z)
    (z₀ : V₁)
    (φ : V₁ → V₂)
    (hφ : ∀ x y, x ≠ z₀ → y ≠ z₀ → R₁ x y → R₂ (φ x) (φ y))
    (hsol : ∃ s' : V₂ → ℝ,
      (∀ b, 0 ≤ s' b ∧ s' b ≤ ∑ x ∈ Finset.univ.filter (fun x => x ≠ z₀ ∧ φ x = b), w x) ∧
      (∑ b, s' b) = 1 / 2 ∧
      25 * (∑ a : V₂, ∑ b : V₂, if R₂ a b then s' a * s' b else 0) ≤ 1) :
    ∃ s : V₁ → ℝ, (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x : V₁, ∑ y : V₁, if R₁ x y then s x * s y else 0) ≤ 1 := by
  obtain ⟨s', hs'01, hs'sum, hs'quad⟩ := hsol
  let W : V₂ → ℝ := fun b => ∑ x ∈ Finset.univ.filter (fun x => x ≠ z₀ ∧ φ x = b), w x
  have hW0 : ∀ b, 0 ≤ W b := fun b => Finset.sum_nonneg fun x _ => hw0 x
  let s : V₁ → ℝ := fun x => if x = z₀ ∨ W (φ x) = 0 then 0 else (w x / W (φ x)) * s' (φ x)
  have hs0 : ∀ x, 0 ≤ s x := by
    intro x
    dsimp only [s]
    split_ifs with h
    · exact le_refl 0
    · push Not at h
      have hWpos : 0 < W (φ x) := lt_of_le_of_ne (hW0 (φ x)) (Ne.symm h.2)
      exact mul_nonneg (div_nonneg (hw0 x) (le_of_lt hWpos)) (hs'01 (φ x)).1
  have hs_le : ∀ x, s x ≤ w x := by
    intro x
    dsimp only [s]
    split_ifs with h
    · exact hw0 x
    · push Not at h
      have hWpos : 0 < W (φ x) := lt_of_le_of_ne (hW0 (φ x)) (Ne.symm h.2)
      have hratio : s' (φ x) / W (φ x) ≤ 1 := (div_le_one hWpos).mpr (hs'01 (φ x)).2
      calc (w x / W (φ x)) * s' (φ x)
          = w x * (s' (φ x) / W (φ x)) := by ring
        _ ≤ w x * 1 := mul_le_mul_of_nonneg_left hratio (hw0 x)
        _ = w x := mul_one _
  have hfiber_s : ∀ b : V₂, (∑ x ∈ Finset.univ.filter (fun x => x ≠ z₀ ∧ φ x = b), s x) = s' b := by
    intro b
    by_cases hWb : W b = 0
    · have hs'b : s' b = 0 := le_antisymm (hWb ▸ (hs'01 b).2) (hs'01 b).1
      rw [hs'b]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hφx : φ x = b := (Finset.mem_filter.mp hx).2.2
      simp only [s, hφx, hWb, or_true, ite_true]
    · have hterm : ∀ x ∈ Finset.univ.filter (fun x => x ≠ z₀ ∧ φ x = b),
          s x = w x * (s' b / W b) := by
        intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        have hcond : ¬ (x = z₀ ∨ W (φ x) = 0) := by
          rw [hx'.2]; exact not_or.mpr ⟨hx'.1, hWb⟩
        simp only [s, if_neg hcond, hx'.2]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      change W b * (s' b / W b) = s' b
      field_simp
  have hfiber_sum : ∀ f : V₁ → ℝ, f z₀ = 0 →
      (∑ x : V₁, f x) = ∑ b : V₂, ∑ x ∈ Finset.univ.filter (fun x => x ≠ z₀ ∧ φ x = b), f x := by
    intro f hfz₀
    have h1 : ∑ x : V₁, f x = ∑ x ∈ Finset.univ.erase z₀, f x := by
      rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ z₀), hfz₀, zero_add]
    rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := φ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x
    simp [and_comm]
  refine ⟨s, fun z => ⟨hs0 z, hs_le z⟩, ?_, ?_⟩
  · rw [hfiber_sum s (by simp [s])]
    simp_rw [hfiber_s]
    exact hs'sum
  · have hstep : (∑ x : V₁, ∑ y : V₁, if R₁ x y then s x * s y else 0) ≤
        ∑ x : V₁, ∑ y : V₁, if R₂ (φ x) (φ y) then s x * s y else 0 := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
      by_cases hx : x = z₀
      · subst hx; simp [s]
      by_cases hy : y = z₀
      · subst hy; simp [s]
      split_ifs with h1 h2
      · exact le_refl _
      · exact False.elim (h2 (hφ x y hx hy h1))
      · exact mul_nonneg (hs0 x) (hs0 y)
      · exact le_refl 0
    have hpull : (∑ x : V₁, ∑ y : V₁, if R₂ (φ x) (φ y) then s x * s y else 0) =
        ∑ a : V₂, ∑ b : V₂, if R₂ a b then s' a * s' b else 0 := by
      rw [hfiber_sum (fun x => ∑ y : V₁, if R₂ (φ x) (φ y) then s x * s y else 0)
            (Finset.sum_eq_zero fun y _ => by simp [s])]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hinner : ∀ x ∈ Finset.univ.filter (fun x => x ≠ z₀ ∧ φ x = a),
          (∑ y : V₁, if R₂ (φ x) (φ y) then s x * s y else 0) =
            ∑ b : V₂, if R₂ a b then s x * s' b else 0 := by
        intro x hx
        have hxa : φ x = a := (Finset.mem_filter.mp hx).2.2
        rw [hfiber_sum (fun y => if R₂ (φ x) (φ y) then s x * s y else 0) (by simp [s])]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hconst : ∀ y ∈ Finset.univ.filter (fun y => y ≠ z₀ ∧ φ y = b),
            (if R₂ (φ x) (φ y) then s x * s y else 0) =
              if R₂ a b then s x * s y else 0 := by
          intro y hy
          rw [hxa, (Finset.mem_filter.mp hy).2.2]
        rw [Finset.sum_congr rfl hconst]
        by_cases hR : R₂ a b
        · simp only [if_pos hR, ← Finset.mul_sum, hfiber_s b]
        · simp only [if_neg hR, Finset.sum_const_zero]
      rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hR : R₂ a b
      · simp only [if_pos hR, ← Finset.sum_mul, hfiber_s a]
      · simp only [if_neg hR, Finset.sum_const_zero]
    linarith

/- ### Part 2: Vega Graph `Υᵢ⁰⁰` Structure, `τ₁` Symmetry, and Zero-Weight Core Folds -/

lemma mod_diff_eq (m a b : ℕ) (ha : a < m) (hb : b < m) :
    (b + m - a) % m = if a ≤ b then b - a else b + m - a := by
  split_ifs with h
  · have heq : b + m - a = (b - a) + m := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

lemma fin8_adj_symm (t₁ t₂ : Fin 8) :
    ((t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
     (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
     (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
     (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
     (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) →
    ((t₂.val < 6 ∧ t₁.val < 6 ∧ ((t₂.val + 1) % 6 = t₁.val ∨ (t₁.val + 1) % 6 = t₂.val)) ∨
     (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
     (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
     (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)) ∨
     (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6))) := by
  omega

lemma fin8_adj_tf (t₁ t₂ t₃ : Fin 8) :
    ((t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
     (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
     (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
     (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
     (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) →
    ((t₂.val < 6 ∧ t₃.val < 6 ∧ ((t₂.val + 1) % 6 = t₃.val ∨ (t₃.val + 1) % 6 = t₂.val)) ∨
     (t₂.val = 6 ∧ (t₃.val = 0 ∨ t₃.val = 4 ∨ t₃.val = 2 ∨ t₃.val = 7)) ∨
     (t₃.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
     (t₂.val = 7 ∧ (t₃.val = 3 ∨ t₃.val = 1 ∨ t₃.val = 5 ∨ t₃.val = 6)) ∨
     (t₃.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6))) →
    ¬ ((t₁.val < 6 ∧ t₃.val < 6 ∧ ((t₁.val + 1) % 6 = t₃.val ∨ (t₃.val + 1) % 6 = t₁.val)) ∨
       (t₁.val = 6 ∧ (t₃.val = 0 ∨ t₃.val = 4 ∨ t₃.val = 2 ∨ t₃.val = 7)) ∨
       (t₃.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
       (t₁.val = 7 ∧ (t₃.val = 3 ∨ t₃.val = 1 ∨ t₃.val = 5 ∨ t₃.val = 6)) ∨
       (t₃.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) := by
  omega

lemma vega_adj_symm (i : ℕ) (hi : 2 ≤ i) :
    let adj : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    ∀ x y, adj x y → adj y x := by
  intro adj x y hxy
  cases x with
  | inl p =>
    cases y with
    | inl q =>
      dsimp only [adj] at hxy ⊢
      rw [mod_diff_eq (3 * i - 1) p.val q.val p.isLt q.isLt] at hxy
      rw [mod_diff_eq (3 * i - 1) q.val p.val q.isLt p.isLt]
      split_ifs at hxy ⊢ <;> omega
    | inr t => exact hxy
  | inr t₁ =>
    cases y with
    | inl p => exact hxy
    | inr t₂ => exact fin8_adj_symm t₁ t₂ hxy

lemma vega_adj_tf (i : ℕ) (hi : 2 ≤ i) :
    let adj : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    ∀ x y z, adj x y → adj y z → ¬ adj x z := by
  intro adj x y z hxy hyz hxz
  cases x with
  | inl p =>
    cases y with
    | inl q =>
      cases z with
      | inl r =>
        dsimp only [adj] at hxy hyz hxz
        rw [mod_diff_eq (3 * i - 1) p.val q.val p.isLt q.isLt] at hxy
        rw [mod_diff_eq (3 * i - 1) q.val r.val q.isLt r.isLt] at hyz
        rw [mod_diff_eq (3 * i - 1) p.val r.val p.isLt r.isLt] at hxz
        split_ifs at hxy hyz hxz <;> omega
      | inr t =>
        dsimp only [adj] at hxy hyz hxz
        rw [mod_diff_eq (3 * i - 1) p.val q.val p.isLt q.isLt] at hxy
        split_ifs at hxy <;> omega
    | inr t =>
      cases z with
      | inl r =>
        dsimp only [adj] at hxy hyz hxz
        rw [mod_diff_eq (3 * i - 1) p.val r.val p.isLt r.isLt] at hxz
        split_ifs at hxz <;> omega
      | inr t₂ =>
        dsimp only [adj] at hxy hyz hxz
        rcases hxy with ⟨ht1, hp1⟩ | ⟨ht1, hp1⟩ | ⟨ht1, hp1⟩ <;>
        rcases hxz with ⟨ht2, hp2⟩ | ⟨ht2, hp2⟩ | ⟨ht2, hp2⟩ <;>
        omega
  | inr t₁ =>
    cases y with
    | inl q =>
      cases z with
      | inl r =>
        dsimp only [adj] at hxy hyz hxz
        rw [mod_diff_eq (3 * i - 1) q.val r.val q.isLt r.isLt] at hyz
        split_ifs at hyz <;> omega
      | inr t₂ =>
        dsimp only [adj] at hxy hyz hxz
        rcases hxy with ⟨ht1, hq1⟩ | ⟨ht1, hq1⟩ | ⟨ht1, hq1⟩ <;>
        rcases hyz with ⟨ht2, hq2⟩ | ⟨ht2, hq2⟩ | ⟨ht2, hq2⟩ <;>
        omega
    | inr t₂ =>
      cases z with
      | inl r =>
        dsimp only [adj] at hxy hyz hxz
        rcases hyz with ⟨ht2, hr2⟩ | ⟨ht2, hr2⟩ | ⟨ht2, hr2⟩ <;>
        rcases hxz with ⟨ht1, hr1⟩ | ⟨ht1, hr1⟩ | ⟨ht1, hr1⟩ <;>
        omega
      | inr t₃ =>
        exact fin8_adj_tf t₁ t₂ t₃ hxy hyz hxz

lemma fin8_tau1_adj (t₁ t₂ : Fin 8) :
    let τ : Fin 8 → Fin 8 := fun t =>
      if t.val < 6 then ⟨(t.val + 3) % 6, by omega⟩
      else if t.val = 6 then ⟨7, by omega⟩
      else ⟨6, by omega⟩
    ((t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
     (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
     (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
     (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
     (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) ↔
    (((τ t₁).val < 6 ∧ (τ t₂).val < 6 ∧
        (((τ t₁).val + 1) % 6 = (τ t₂).val ∨ ((τ t₂).val + 1) % 6 = (τ t₁).val)) ∨
     ((τ t₁).val = 6 ∧ ((τ t₂).val = 0 ∨ (τ t₂).val = 4 ∨ (τ t₂).val = 2 ∨ (τ t₂).val = 7)) ∨
     ((τ t₂).val = 6 ∧ ((τ t₁).val = 0 ∨ (τ t₁).val = 4 ∨ (τ t₁).val = 2 ∨ (τ t₁).val = 7)) ∨
     ((τ t₁).val = 7 ∧ ((τ t₂).val = 3 ∨ (τ t₂).val = 1 ∨ (τ t₂).val = 5 ∨ (τ t₂).val = 6)) ∨
     ((τ t₂).val = 7 ∧ ((τ t₁).val = 3 ∨ (τ t₁).val = 1 ∨ (τ t₁).val = 5 ∨ (τ t₁).val = 6))) := by
  intro τ
  fin_cases t₁ <;> fin_cases t₂ <;> simp [τ]

lemma vega_tau1_symmetry (i : ℕ) :
    let adj : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    ∀ w : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
      (∀ z, 0 ≤ w z) → (∑ z, w z) = 1 →
      0 < w (Sum.inr 0) + w (Sum.inr 1) →
      0 < w (Sum.inr 3) + w (Sum.inr 4) →
      0 < w (Sum.inr 1) + w (Sum.inr 6) →
      0 < w (Sum.inr 4) + w (Sum.inr 7) →
      w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 4) + w (Sum.inr 7) < 2 / 5 →
      w (Sum.inr 1) + w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 6) < 2 / 5 →
      (∀ w' : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
        (∀ z, 0 ≤ w' z) → (∑ z, w' z) = 1 →
        0 < w' (Sum.inr 0) + w' (Sum.inr 1) →
        0 < w' (Sum.inr 3) + w' (Sum.inr 4) →
        0 < w' (Sum.inr 1) + w' (Sum.inr 6) →
        0 < w' (Sum.inr 4) + w' (Sum.inr 7) →
        w' (Sum.inr 0) + w' (Sum.inr 2) + w' (Sum.inr 4) + w' (Sum.inr 7) < 2 / 5 →
        w' (Sum.inr 1) + w' (Sum.inr 3) + w' (Sum.inr 5) + w' (Sum.inr 6) < 2 / 5 →
        w' (Sum.inr 0) + w' (Sum.inr 2) + w' (Sum.inr 4) + w' (Sum.inr 7) ≤
          w' (Sum.inr 1) + w' (Sum.inr 3) + w' (Sum.inr 5) + w' (Sum.inr 6) →
        ∃ s : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
          (∀ z, 0 ≤ s z ∧ s z ≤ w' z) ∧ (∑ z, s z) = 1 / 2 ∧
          25 * (∑ x, ∑ y, if adj x y then s x * s y else 0) ≤ 1) →
      ∃ s : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
        (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
        25 * (∑ x, ∑ y, if adj x y then s x * s y else 0) ≤ 1 := by
  intro adj w hw0 hwsum h01 h34 h16 h47 hB0 hB1 hord
  by_cases hle : w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 4) + w (Sum.inr 7) ≤
      w (Sum.inr 1) + w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 6)
  · exact hord w hw0 hwsum h01 h34 h16 h47 hB0 hB1 hle
  push Not at hle
  let τ8 : Fin 8 → Fin 8 := fun t =>
    if t.val < 6 then ⟨(t.val + 3) % 6, by omega⟩
    else if t.val = 6 then ⟨7, by omega⟩
    else ⟨6, by omega⟩
  let τ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 := fun z =>
    match z with
    | Sum.inl p => Sum.inl p
    | Sum.inr t => Sum.inr (τ8 t)
  have hτ_inv : Function.Involutive τ := by
    intro z
    cases z with
    | inl p => rfl
    | inr t =>
      dsimp only [τ]
      congr 1
      fin_cases t <;> simp [τ8]
  let e : (Fin (3 * i - 1) ⊕ Fin 8) ≃ (Fin (3 * i - 1) ⊕ Fin 8) := hτ_inv.toPerm τ
  have hτ_adj : ∀ x y, adj x y ↔ adj (τ x) (τ y) := by
    intro x y
    cases x with
    | inl p =>
      cases y with
      | inl q => exact Iff.rfl
      | inr t =>
        dsimp only [adj, τ, τ8]
        fin_cases t <;> simp
    | inr t₁ =>
      cases y with
      | inl p =>
        dsimp only [adj, τ, τ8]
        fin_cases t₁ <;> simp
      | inr t₂ => exact fin8_tau1_adj t₁ t₂
  let w' : Fin (3 * i - 1) ⊕ Fin 8 → ℝ := fun z => w (τ z)
  have hw'sum : (∑ z, w' z) = 1 := by
    simpa only [w', e, Function.Involutive.coe_toPerm] using
      (Equiv.sum_comp e w).trans hwsum
  have hv0 : w' (Sum.inr 0) = w (Sum.inr 3) := rfl
  have hv1 : w' (Sum.inr 1) = w (Sum.inr 4) := rfl
  have hv2 : w' (Sum.inr 2) = w (Sum.inr 5) := rfl
  have hv3 : w' (Sum.inr 3) = w (Sum.inr 0) := rfl
  have hv4 : w' (Sum.inr 4) = w (Sum.inr 1) := rfl
  have hv5 : w' (Sum.inr 5) = w (Sum.inr 2) := rfl
  have hv6 : w' (Sum.inr 6) = w (Sum.inr 7) := rfl
  have hv7 : w' (Sum.inr 7) = w (Sum.inr 6) := rfl
  obtain ⟨s', hs'01, hs'sum, hs'quad⟩ := hord w' (fun z => hw0 (τ z)) hw'sum
    (by rw [hv0, hv1]; exact h34)
    (by rw [hv3, hv4]; exact h01)
    (by rw [hv1, hv6]; exact h47)
    (by rw [hv4, hv7]; exact h16)
    (by rw [hv0, hv2, hv4, hv7]; linarith)
    (by rw [hv1, hv3, hv5, hv6]; linarith)
    (by rw [hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7]; linarith)
  refine ⟨fun z => s' (τ z), ?_, ?_, ?_⟩
  · intro z
    have h := hs'01 (τ z)
    simpa only [w', hτ_inv z] using h
  · simpa only [e, Function.Involutive.coe_toPerm] using
      (Equiv.sum_comp e s').trans hs'sum
  · have hq : (∑ x, ∑ y, if adj x y then s' (τ x) * s' (τ y) else 0) =
        ∑ x, ∑ y, if adj x y then s' x * s' y else 0 := by
      have h1 : (∑ x, ∑ y, if adj x y then s' (τ x) * s' (τ y) else 0) =
          ∑ x, ∑ y, if adj (τ x) (τ y) then s' (τ x) * s' (τ y) else 0 := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        by_cases h : adj x y
        · rw [if_pos h, if_pos ((hτ_adj x y).mp h)]
        · rw [if_neg h, if_neg (fun h' => h ((hτ_adj x y).mpr h'))]
      rw [h1]
      calc (∑ x, ∑ y, if adj (τ x) (τ y) then s' (τ x) * s' (τ y) else 0)
          = ∑ x, ∑ y, if adj (e x) (e y) then s' (e x) * s' (e y) else 0 := rfl
        _ = ∑ x, ∑ y, if adj (e x) y then s' (e x) * s' y else 0 := by
            refine Finset.sum_congr rfl fun x _ => Equiv.sum_comp e (fun y => if adj (e x) y then s' (e x) * s' y else 0)
        _ = ∑ x, ∑ y, if adj x y then s' x * s' y else 0 :=
            Equiv.sum_comp e (fun x => ∑ y, if adj x y then s' x * s' y else 0)
    rw [hq]
    exact hs'quad

/- Exact zero-weight core fold: deleting any vertex `P₂(k)` (`0 ≤ k < i`) or interior
   `P₀(k)` / `P₁(k)` (`1 ≤ k < i`) in `Υ_{i+1}⁰⁰` (`i ≥ 3`) homomorphically maps into `Υᵢ⁰⁰`
   while fixing `Fin 8` pointwise. -/

lemma andrasfai_band_iff (i : ℕ) (hi : 2 ≤ i) (p q : Fin (3 * i - 1)) :
    (i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
     (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1) ↔
    ((p.val < i ∧ i ≤ q.val ∧ q.val < 2 * i ∧ p.val ≤ q.val - i) ∨
     (i ≤ p.val ∧ p.val < 2 * i ∧ q.val < i ∧ q.val ≤ p.val - i) ∨
     (i ≤ p.val ∧ p.val < 2 * i ∧ 2 * i ≤ q.val ∧ p.val - i ≤ q.val - 2 * i) ∨
     (2 * i ≤ p.val ∧ i ≤ q.val ∧ q.val < 2 * i ∧ q.val - i ≤ p.val - 2 * i) ∨
     (2 * i ≤ p.val ∧ q.val < i ∧ p.val - 2 * i < q.val) ∨
     (p.val < i ∧ 2 * i ≤ q.val ∧ q.val - 2 * i < p.val)) := by
  rw [mod_diff_eq (3 * i - 1) p.val q.val p.isLt q.isLt]
  have hp := p.isLt
  have hq := q.isLt
  split_ifs <;> omega

lemma vega_core_fold_step (i : ℕ) (hi : 3 ≤ i) :
    let adj₁ : Fin (3 * (i + 1) - 1) ⊕ Fin 8 → Fin (3 * (i + 1) - 1) ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q =>
          (i + 1) ≤ (q.val + (3 * (i + 1) - 1) - p.val) % (3 * (i + 1) - 1) ∧
          (q.val + (3 * (i + 1) - 1) - p.val) % (3 * (i + 1) - 1) ≤ 2 * (i + 1) - 1
      | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i + 1) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i + 1 ≤ p.val ∧ p.val < 2 * (i + 1)) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * (i + 1) ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    let adj₀ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    ∀ (p₀ : Fin (3 * (i + 1) - 1)),
      ((1 ≤ p₀.val ∧ p₀.val < i) ∨
       (i + 2 ≤ p₀.val ∧ p₀.val < 2 * (i + 1) - 1) ∨
       2 * (i + 1) ≤ p₀.val) →
      ∃ φ : Fin (3 * (i + 1) - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8,
        (∀ p, ∃ q, φ (Sum.inl p) = Sum.inl q) ∧
        (∀ t, φ (Sum.inr t) = Sum.inr t) ∧
        (∀ x y, x ≠ Sum.inl p₀ → y ≠ Sum.inl p₀ → adj₁ x y → adj₀ (φ x) (φ y)) := by
  intro adj₁ adj₀ p₀ hp₀
  rcases hp₀ with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | hp2
  · -- Case 1: interior P₀(k), 1 ≤ k < i
    set k := p₀.val
    let f : Fin (3 * (i + 1) - 1) → Fin (3 * i - 1) := fun p =>
      if h0 : p.val < i + 1 then
        ⟨if p.val < k then p.val else p.val - 1, by split_ifs <;> omega⟩
      else if h1 : p.val < 2 * (i + 1) then
        ⟨i + (if p.val - (i + 1) < k then p.val - (i + 1) else p.val - (i + 1) - 1), by split_ifs <;> omega⟩
      else
        ⟨2 * i + (if p.val - 2 * (i + 1) < k then p.val - 2 * (i + 1) else p.val - 2 * (i + 1) - 1), by split_ifs <;> omega⟩
    have hf0 : ∀ p : Fin (3 * (i + 1) - 1), p.val < i + 1 →
        (f p).val = if p.val < k then p.val else p.val - 1 := fun p hp => by simp only [f, dif_pos hp]
    have hf1 : ∀ p : Fin (3 * (i + 1) - 1), i + 1 ≤ p.val → p.val < 2 * (i + 1) →
        (f p).val = i + (if p.val - (i + 1) < k then p.val - (i + 1) else p.val - (i + 1) - 1) :=
      fun p h1 h2 => by simp only [f, dif_neg (show ¬ p.val < i + 1 by omega), dif_pos h2]
    have hf2 : ∀ p : Fin (3 * (i + 1) - 1), 2 * (i + 1) ≤ p.val →
        (f p).val = 2 * i + (if p.val - 2 * (i + 1) < k then p.val - 2 * (i + 1) else p.val - 2 * (i + 1) - 1) :=
      fun p h1 => by simp only [f, dif_neg (show ¬ p.val < i + 1 by omega), dif_neg (show ¬ p.val < 2 * (i + 1) by omega)]
    refine ⟨fun x => match x with | Sum.inl p => Sum.inl (f p) | Sum.inr t => Sum.inr t,
      fun p => ⟨f p, rfl⟩, fun t => rfl, ?_⟩
    intro x y hx hy hxy
    cases x with
    | inl p =>
      cases y with
      | inl q =>
        have hpk : p.val ≠ k := fun h => hx (congrArg Sum.inl (Fin.ext h))
        have hqk : q.val ≠ k := fun h => hy (congrArg Sum.inl (Fin.ext h))
        dsimp only [adj₁, adj₀] at hxy ⊢
        rw [andrasfai_band_iff (i + 1) (by omega) p q] at hxy
        rw [andrasfai_band_iff i (by omega) (f p) (f q)]
        rcases hxy with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
                        ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have e1 := hf0 p h1; have e2 := hf1 q h2 h3
          left; split_ifs at e1 e2 <;> omega
        · have e1 := hf1 p h1 h2; have e2 := hf0 q h3
          right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf1 p h1 h2; have e2 := hf2 q h3
          right; right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf2 p h1; have e2 := hf1 q h2 h3
          right; right; right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf2 p h1; have e2 := hf0 q h2
          right; right; right; right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf0 p h1; have e2 := hf2 q h2
          right; right; right; right; right; split_ifs at e1 e2 <;> omega
      | inr t =>
        dsimp only [adj₁, adj₀] at hxy ⊢
        rcases hxy with ⟨ht, hp⟩ | ⟨ht, hp1, hp2⟩ | ⟨ht, hp⟩
        · have e := hf0 p hp; left; split_ifs at e <;> omega
        · have e := hf1 p hp1 hp2; right; left; split_ifs at e <;> omega
        · have e := hf2 p hp; right; right; split_ifs at e <;> omega
    | inr t₁ =>
      cases y with
      | inl q =>
        dsimp only [adj₁, adj₀] at hxy ⊢
        rcases hxy with ⟨ht, hq⟩ | ⟨ht, hq1, hq2⟩ | ⟨ht, hq⟩
        · have e := hf0 q hq; left; split_ifs at e <;> omega
        · have e := hf1 q hq1 hq2; right; left; split_ifs at e <;> omega
        · have e := hf2 q hq; right; right; split_ifs at e <;> omega
      | inr t₂ => exact hxy
  · -- Case 2: interior P₁(k), 1 ≤ k < i where p₀.val = (i + 1) + k
    set k := p₀.val - (i + 1)
    have hk1 : 1 ≤ k := by omega
    have hk2 : k < i := by omega
    let f : Fin (3 * (i + 1) - 1) → Fin (3 * i - 1) := fun p =>
      if h0 : p.val < i + 1 then
        ⟨if p.val ≤ k then p.val else p.val - 1, by split_ifs <;> omega⟩
      else if h1 : p.val < 2 * (i + 1) then
        ⟨i + (if p.val - (i + 1) < k then p.val - (i + 1) else p.val - (i + 1) - 1), by split_ifs <;> omega⟩
      else
        ⟨2 * i + (if p.val - 2 * (i + 1) < k then p.val - 2 * (i + 1) else p.val - 2 * (i + 1) - 1), by split_ifs <;> omega⟩
    have hf0 : ∀ p : Fin (3 * (i + 1) - 1), p.val < i + 1 →
        (f p).val = if p.val ≤ k then p.val else p.val - 1 := fun p hp => by simp only [f, dif_pos hp]
    have hf1 : ∀ p : Fin (3 * (i + 1) - 1), i + 1 ≤ p.val → p.val < 2 * (i + 1) →
        (f p).val = i + (if p.val - (i + 1) < k then p.val - (i + 1) else p.val - (i + 1) - 1) :=
      fun p h1 h2 => by simp only [f, dif_neg (show ¬ p.val < i + 1 by omega), dif_pos h2]
    have hf2 : ∀ p : Fin (3 * (i + 1) - 1), 2 * (i + 1) ≤ p.val →
        (f p).val = 2 * i + (if p.val - 2 * (i + 1) < k then p.val - 2 * (i + 1) else p.val - 2 * (i + 1) - 1) :=
      fun p h1 => by simp only [f, dif_neg (show ¬ p.val < i + 1 by omega), dif_neg (show ¬ p.val < 2 * (i + 1) by omega)]
    refine ⟨fun x => match x with | Sum.inl p => Sum.inl (f p) | Sum.inr t => Sum.inr t,
      fun p => ⟨f p, rfl⟩, fun t => rfl, ?_⟩
    intro x y hx hy hxy
    cases x with
    | inl p =>
      cases y with
      | inl q =>
        have hpk : p.val ≠ i + 1 + k := fun h => hx (congrArg Sum.inl (Fin.ext (by omega)))
        have hqk : q.val ≠ i + 1 + k := fun h => hy (congrArg Sum.inl (Fin.ext (by omega)))
        dsimp only [adj₁, adj₀] at hxy ⊢
        rw [andrasfai_band_iff (i + 1) (by omega) p q] at hxy
        rw [andrasfai_band_iff i (by omega) (f p) (f q)]
        rcases hxy with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
                        ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have e1 := hf0 p h1; have e2 := hf1 q h2 h3
          left; split_ifs at e1 e2 <;> omega
        · have e1 := hf1 p h1 h2; have e2 := hf0 q h3
          right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf1 p h1 h2; have e2 := hf2 q h3
          right; right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf2 p h1; have e2 := hf1 q h2 h3
          right; right; right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf2 p h1; have e2 := hf0 q h2
          right; right; right; right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf0 p h1; have e2 := hf2 q h2
          right; right; right; right; right; split_ifs at e1 e2 <;> omega
      | inr t =>
        dsimp only [adj₁, adj₀] at hxy ⊢
        rcases hxy with ⟨ht, hp⟩ | ⟨ht, hp1, hp2⟩ | ⟨ht, hp⟩
        · have e := hf0 p hp; left; split_ifs at e <;> omega
        · have e := hf1 p hp1 hp2; right; left; split_ifs at e <;> omega
        · have e := hf2 p hp; right; right; split_ifs at e <;> omega
    | inr t₁ =>
      cases y with
      | inl q =>
        dsimp only [adj₁, adj₀] at hxy ⊢
        rcases hxy with ⟨ht, hq⟩ | ⟨ht, hq1, hq2⟩ | ⟨ht, hq⟩
        · have e := hf0 q hq; left; split_ifs at e <;> omega
        · have e := hf1 q hq1 hq2; right; left; split_ifs at e <;> omega
        · have e := hf2 q hq; right; right; split_ifs at e <;> omega
      | inr t₂ => exact hxy
  · -- Case 3: any P₂(k), 0 ≤ k < i where p₀.val = 2 * (i + 1) + k
    set k := p₀.val - 2 * (i + 1)
    have hk2 : k < i := by omega
    let f : Fin (3 * (i + 1) - 1) → Fin (3 * i - 1) := fun p =>
      if h0 : p.val < i + 1 then
        ⟨if p.val ≤ k then p.val else p.val - 1, by split_ifs <;> omega⟩
      else if h1 : p.val < 2 * (i + 1) then
        ⟨i + (if p.val - (i + 1) ≤ k then p.val - (i + 1) else p.val - (i + 1) - 1), by split_ifs <;> omega⟩
      else
        ⟨2 * i + (if p.val - 2 * (i + 1) < k then p.val - 2 * (i + 1) else p.val - 2 * (i + 1) - 1), by split_ifs <;> omega⟩
    have hf0 : ∀ p : Fin (3 * (i + 1) - 1), p.val < i + 1 →
        (f p).val = if p.val ≤ k then p.val else p.val - 1 := fun p hp => by simp only [f, dif_pos hp]
    have hf1 : ∀ p : Fin (3 * (i + 1) - 1), i + 1 ≤ p.val → p.val < 2 * (i + 1) →
        (f p).val = i + (if p.val - (i + 1) ≤ k then p.val - (i + 1) else p.val - (i + 1) - 1) :=
      fun p h1 h2 => by simp only [f, dif_neg (show ¬ p.val < i + 1 by omega), dif_pos h2]
    have hf2 : ∀ p : Fin (3 * (i + 1) - 1), 2 * (i + 1) ≤ p.val →
        (f p).val = 2 * i + (if p.val - 2 * (i + 1) < k then p.val - 2 * (i + 1) else p.val - 2 * (i + 1) - 1) :=
      fun p h1 => by simp only [f, dif_neg (show ¬ p.val < i + 1 by omega), dif_neg (show ¬ p.val < 2 * (i + 1) by omega)]
    refine ⟨fun x => match x with | Sum.inl p => Sum.inl (f p) | Sum.inr t => Sum.inr t,
      fun p => ⟨f p, rfl⟩, fun t => rfl, ?_⟩
    intro x y hx hy hxy
    cases x with
    | inl p =>
      cases y with
      | inl q =>
        have hpk : p.val ≠ 2 * (i + 1) + k := fun h => hx (congrArg Sum.inl (Fin.ext (by omega)))
        have hqk : q.val ≠ 2 * (i + 1) + k := fun h => hy (congrArg Sum.inl (Fin.ext (by omega)))
        dsimp only [adj₁, adj₀] at hxy ⊢
        rw [andrasfai_band_iff (i + 1) (by omega) p q] at hxy
        rw [andrasfai_band_iff i (by omega) (f p) (f q)]
        rcases hxy with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
                        ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have e1 := hf0 p h1; have e2 := hf1 q h2 h3
          left; split_ifs at e1 e2 <;> omega
        · have e1 := hf1 p h1 h2; have e2 := hf0 q h3
          right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf1 p h1 h2; have e2 := hf2 q h3
          right; right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf2 p h1; have e2 := hf1 q h2 h3
          right; right; right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf2 p h1; have e2 := hf0 q h2
          right; right; right; right; left; split_ifs at e1 e2 <;> omega
        · have e1 := hf0 p h1; have e2 := hf2 q h2
          right; right; right; right; right; split_ifs at e1 e2 <;> omega
      | inr t =>
        dsimp only [adj₁, adj₀] at hxy ⊢
        rcases hxy with ⟨ht, hp⟩ | ⟨ht, hp1, hp2⟩ | ⟨ht, hp⟩
        · have e := hf0 p hp; left; split_ifs at e <;> omega
        · have e := hf1 p hp1 hp2; right; left; split_ifs at e <;> omega
        · have e := hf2 p hp; right; right; split_ifs at e <;> omega
    | inr t₁ =>
      cases y with
      | inl q =>
        dsimp only [adj₁, adj₀] at hxy ⊢
        rcases hxy with ⟨ht, hq⟩ | ⟨ht, hq1, hq2⟩ | ⟨ht, hq⟩
        · have e := hf0 q hq; left; split_ifs at e <;> omega
        · have e := hf1 q hq1 hq2; right; left; split_ifs at e <;> omega
        · have e := hf2 q hq; right; right; split_ifs at e <;> omega
      | inr t₂ => exact hxy

/- ### Part 3: Main Reduction Theorem -/

theorem main : H1 → H2 → H3 → OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1.H2 := by
  intro hH1 hH2 hH3 i hi3
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro w hw0 hwsum h01 h34 h16 h47 hB0 hB1
    let adj : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    suffices hgoal : ∃ s : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
        (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧ (∑ z, s z) = 1 / 2 ∧
        25 * (∑ x, ∑ y, if adj x y then s x * s y else 0) ≤ 1 by
      obtain ⟨s, hs01, hssum, hsq⟩ := hgoal
      refine ⟨s, hs01, hssum, ?_⟩
      convert hsq using 2
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      cases x <;> cases y <;> (dsimp only [adj]; split_ifs <;> rfl)
    -- Apply exact involution symmetry τ₁ to reduce WLOG to w(B₀) ≤ w(B₁)
    refine vega_tau1_symmetry i w hw0 hwsum h01 h34 h16 h47 hB0 hB1 ?_
    intro w hw0 hwsum h01 h34 h16 h47 hB0 hB1 hB0_le_B1
    -- Step 1: Random-half cutoff
    by_cases hQ : 25 * (∑ x, ∑ y, if adj x y then w x * w y else 0) ≤ 4
    · exact random_half_sparse adj w hw0 hwsum hQ
    push Not at hQ
    -- Step 2: Continuous Razborov Theorem A cutoff
    by_cases hInd : ∃ I : Finset (Fin (3 * i - 1) ⊕ Fin 8),
        (∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) ∧ 2 / 5 ≤ ∑ z ∈ I, w z
    · obtain ⟨I₀, hI₀, hI₀w⟩ := hInd
      exact continuous_razborov_two_fifths adj
        (vega_adj_symm i (by omega)) (vega_adj_tf i (by omega))
        w hw0 hwsum I₀ hI₀ hI₀w
    have hInd_lt : ∀ I : Finset (Fin (3 * i - 1) ⊕ Fin 8),
        (∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) → (∑ z ∈ I, w z) < 2 / 5 := by
      intro I hI
      by_contra hge
      push Not at hge
      exact hInd ⟨I, hI, hge⟩
    -- Step 3: Base case i = 3 -> H1
    by_cases hi3_eq : i = 3
    · subst hi3_eq
      obtain ⟨s, hs01, hssum, hsq⟩ := hH1 w hw0 hwsum h01 h34 h16 h47 hB0_le_B1
        (by
          refine lt_of_lt_of_eq hQ (congrArg (25 * ·) ?_)
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          cases x <;> cases y <;> rfl)
        (fun I hI => hInd_lt I (fun x hx y hy h => hI x hx y hy (by cases x <;> cases y <;> exact h)))
      refine ⟨s, hs01, hssum, ?_⟩
      refine le_trans (le_of_eq (congrArg (25 * ·) ?_)) hsq
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      cases x <;> cases y <;> rfl
    -- Step 4: i ≥ 4 -> fold any zero-weight core vertex down to i - 1, else split into H2 / H3
    have hi4 : 4 ≤ i := by omega
    by_cases hcore : ∀ p : Fin (3 * i - 1),
        (1 ≤ p.val ∧ p.val < i - 1) ∨ (i + 1 ≤ p.val ∧ p.val < 2 * i - 1) ∨ 2 * i ≤ p.val →
        0 < w (Sum.inl p)
    · -- Strictly positive core: split on w(Γᵢ) ≤ 1/2 vs 1/2 < w(Γᵢ)
      by_cases hG : (∑ p : Fin (3 * i - 1), w (Sum.inl p)) ≤ 1 / 2
      · exact hH2 i hi4 w hw0 hwsum h01 h34 h16 h47 hB0_le_B1 hG hcore hQ hInd_lt
      · push Not at hG
        exact hH3 i hi4 w hw0 hwsum h01 h34 h16 h47 hB0_le_B1 hG hcore hQ hInd_lt
    · -- Some core vertex p₀ has weight 0: fold Υᵢ⁰⁰ → Υ_{i-1}⁰⁰ and apply strong IH
      push Not at hcore
      obtain ⟨p₀, hp₀_core, hp₀_le⟩ := hcore
      have hp₀_zero : w (Sum.inl p₀) = 0 := le_antisymm hp₀_le (hw0 (Sum.inl p₀))
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hk3 : 3 ≤ k := by omega
      have hp₀_core' : (1 ≤ p₀.val ∧ p₀.val < k) ∨
          (k + 2 ≤ p₀.val ∧ p₀.val < 2 * (k + 1) - 1) ∨
          2 * (k + 1) ≤ p₀.val := by
        rcases hp₀_core with ⟨a, b⟩ | ⟨a, b⟩ | a
        · left; omega
        · right; left; omega
        · right; right; omega
      obtain ⟨φ, hφ_inl, hφ_inr, hφ_adj⟩ := vega_core_fold_step k hk3 p₀ hp₀_core'
      let adj₀ : Fin (3 * k - 1) ⊕ Fin 8 → Fin (3 * k - 1) ⊕ Fin 8 → Prop := fun x y =>
        match x, y with
        | Sum.inl p, Sum.inl q =>
            k ≤ (q.val + (3 * k - 1) - p.val) % (3 * k - 1) ∧
            (q.val + (3 * k - 1) - p.val) % (3 * k - 1) ≤ 2 * k - 1
        | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < k) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ k ≤ p.val ∧ p.val < 2 * k) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * k ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ =>
            (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
            (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
            (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
            (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
            (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
      let w' : Fin (3 * k - 1) ⊕ Fin 8 → ℝ := fun b =>
        ∑ x ∈ Finset.univ.filter (fun x => x ≠ Sum.inl p₀ ∧ φ x = b), w x
      have hw'0 : ∀ b, 0 ≤ w' b := fun b => Finset.sum_nonneg fun x _ => hw0 x
      have hw'sum : (∑ b, w' b) = 1 := by
        have h1 : (∑ x, w x) = ∑ x ∈ Finset.univ.erase (Sum.inl p₀), w x := by
          rw [← Finset.add_sum_erase Finset.univ w (Finset.mem_univ (Sum.inl p₀)), hp₀_zero, zero_add]
        have h2 : (∑ x ∈ Finset.univ.erase (Sum.inl p₀), w x) = ∑ b, w' b := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr ?_ (fun _ _ => rfl)
          ext x; simp [and_comm]
        linarith
      have hw'_inr : ∀ t : Fin 8, w' (Sum.inr t) = w (Sum.inr t) := by
        intro t
        have hfilt : Finset.univ.filter (fun x => x ≠ Sum.inl p₀ ∧ φ x = Sum.inr t) = {Sum.inr t} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨_, hfx⟩
            cases x with
            | inl p =>
              obtain ⟨q, hq⟩ := hφ_inl p
              rw [hq] at hfx
              exact absurd hfx (by simp)
            | inr t' =>
              rw [hφ_inr t'] at hfx
              exact congrArg Sum.inr (Sum.inr.inj hfx)
          · rintro rfl
            exact ⟨by simp, hφ_inr t⟩
        simp only [w', hfilt, Finset.sum_singleton]
      obtain ⟨s', hs'01, hs'sum, hs'quad⟩ := ih k (by omega) hk3 w' hw'0 hw'sum
        (by rw [hw'_inr, hw'_inr]; exact h01)
        (by rw [hw'_inr, hw'_inr]; exact h34)
        (by rw [hw'_inr, hw'_inr]; exact h16)
        (by rw [hw'_inr, hw'_inr]; exact h47)
        (by simp only [hw'_inr]; exact hB0)
        (by simp only [hw'_inr]; exact hB1)
      have hs'quad' : 25 * (∑ a, ∑ b, if adj₀ a b then s' a * s' b else 0) ≤ 1 := by
        convert hs'quad using 2
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        cases x <;> cases y <;> (dsimp only [adj₀]; split_ifs <;> rfl)
      exact hom_pullback_sparse_half adj adj₀ w hw0 (Sum.inl p₀) φ
        (fun x y hx hy h => by
          have h' := hφ_adj x y hx hy (by cases x <;> cases y <;> exact h)
          cases hfx : φ x <;> cases hfy : φ y <;> (rw [hfx, hfy] at h'; exact h'))
        ⟨s', hs'01, hs'sum, hs'quad'⟩

end OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1_H2_R1
