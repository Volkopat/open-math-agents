import OMAStatements.S_opg_edge_antipodal_colorings_of_cubes
import Mathlib

/-!
Norine's antipodal-colouring theorem (edge-antipodal colourings of cubes), following
V. Djaljapayan, Antipodal paths: a short proof by counting intersections (arXiv:2611.16243),
which reproves the theorem of H. Wu and N. Yang (arXiv:2607.19276).
Part B (namespace NorineB): no antipodally swapped pair-labelling of Q_K exists (discrete
Borsuk-Ulam parity argument). Part A (namespace Norine): a counterexample colouring yields one.
-/

/-!
# Blueprint for the core lemma of Norine's theorem (Djaljapayan, arXiv:2611.16243)

Every statement below is FIXED. Workers prove exactly one `sorry` each, in their own copy of this
file, without changing any definition or statement (helper lemmas may be added above the target).

Paper ↔ Lean:
* cube `Q_K`, vertices `V K = Fin K → Bool`; `flip x c` changes coordinate `c`; `anti` flips all.
* labels are pairs `p = (a, b)`, `a ≠ b`; `vec p = e_a - e_b ∈ ℝ^K`.
* functionals `ℓ₁, …, ℓ_d` are `ℓ 0, …, ℓ (d-1)` (0-indexed), `d = K - 1`; `ℓ a ⬝ᵥ w`.
* `H_i` (paper) = `{w | InH ℓ i w}` = common kernel of `ℓ 0, …, ℓ (i-1)`.
* `Beta ℓ i S` : `conv S` meets `H_i \ {0}`;  `Alpha ℓ i S` : `conv S` meets `H_i⁺ = {ℓ_{i+1} > 0}`
  (paper's `ℓ_{i+1}` is `ℓ i`).
-/

namespace NorineB

open Matrix Finset Classical

/-! ## Geometry -/

/-- `vec (a, b) = e_a - e_b`. -/
noncomputable def vec {K : ℕ} (p : Fin K × Fin K) : Fin K → ℝ :=
  Pi.single p.1 1 - Pi.single p.2 1

/-- The set of vectors of a tuple of labels. -/
def S {K m : ℕ} (p : Fin m → Fin K × Fin K) : Set (Fin K → ℝ) := Set.range fun j => vec (p j)

def InH {K : ℕ} (ℓ : ℕ → Fin K → ℝ) (i : ℕ) (w : Fin K → ℝ) : Prop := ∀ a < i, ℓ a ⬝ᵥ w = 0

def Beta {K : ℕ} (ℓ : ℕ → Fin K → ℝ) (i : ℕ) (X : Set (Fin K → ℝ)) : Prop :=
  ∃ w ∈ convexHull ℝ X, InH ℓ i w ∧ w ≠ 0

def Alpha {K : ℕ} (ℓ : ℕ → Fin K → ℝ) (i : ℕ) (X : Set (Fin K → ℝ)) : Prop :=
  ∃ w ∈ convexHull ℝ X, InH ℓ i w ∧ 0 < ℓ i ⬝ᵥ w

/-- Genericity (paper (3)): for every linearly independent tuple of `s ≤ K - 1` label vectors, the
`s × s` matrix `(ℓ a (u b))` of the first `s` functionals is nonsingular. -/
def Generic (K : ℕ) (ℓ : ℕ → Fin K → ℝ) : Prop :=
  ∀ (s : ℕ) (p : Fin s → Fin K × Fin K), s ≤ K - 1 → (∀ j, (p j).1 ≠ (p j).2) →
    LinearIndependent ℝ (fun j => vec (p j)) →
    (Matrix.of fun a b : Fin s => ℓ a ⬝ᵥ vec (p b)).det ≠ 0

/-- Consecutive labels share their first or their second entry. -/
def ConsecShare {K m : ℕ} (p : Fin m → Fin K × Fin K) : Prop :=
  ∀ (j : ℕ) (h : j + 1 < m), (p ⟨j, by omega⟩).1 = (p ⟨j + 1, h⟩).1 ∨
    (p ⟨j, by omega⟩).2 = (p ⟨j + 1, h⟩).2

lemma rd_image_card {α : Type*} [DecidableEq α] (g : ℕ → α) (n : ℕ) :
    ((range (n + 1)).image g).card ≤ 1 + ((range n).filter fun j => g (j + 1) ≠ g j).card := by
  have hsub : (range (n + 1)).image g ⊆
      insert (g 0) (((range n).filter fun j => g (j + 1) ≠ g j).image fun j => g (j + 1)) := by
    intro x hx
    simp only [mem_image, mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    induction k with
    | zero => exact mem_insert_self _ _
    | succ k ih =>
      by_cases h : g (k + 1) = g k
      · rw [h]; exact ih (by omega)
      · apply mem_insert_of_mem
        exact mem_image.2 ⟨k, mem_filter.2 ⟨mem_range.2 (by omega), h⟩, rfl⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_insert_le _ _
    _ ≤ _ := by
      have := card_image_le (s := (range n).filter fun j => g (j + 1) ≠ g j) (f := fun j => g (j + 1))
      omega

lemma rd_vec_apply {K : ℕ} (p : Fin K × Fin K) (c : Fin K) :
    vec p c = (if p.1 = c then 1 else 0) - (if p.2 = c then 1 else 0) := by
  simp [vec, Pi.single_apply, eq_comm]

lemma rd_finrank {K : ℕ} (X : Set (Fin K → ℝ)) (U : Finset (Fin K)) (c0 : Fin K) (hc0 : c0 ∈ U)
    (hX : ∀ x ∈ X, ∃ a ∈ U, ∃ b ∈ U, x = Pi.single a 1 - Pi.single b 1) :
    Module.finrank ℝ (Submodule.span ℝ X) + 1 ≤ U.card := by
  set T : Finset (Fin K → ℝ) := (U.erase c0).image fun c => Pi.single c 1 - Pi.single c0 1
  have key : ∀ a ∈ U, (Pi.single a 1 - Pi.single c0 1 : Fin K → ℝ) ∈ Submodule.span ℝ (T : Set _) := by
    intro a ha
    by_cases h : a = c0
    · subst h; simp
    · apply Submodule.subset_span
      simp only [T, coe_image, coe_erase, Set.mem_image]
      exact ⟨a, ⟨ha, h⟩, rfl⟩
  have hle : Submodule.span ℝ X ≤ Submodule.span ℝ (T : Set _) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hX x hx
    have := Submodule.sub_mem _ (key a ha) (key b hb)
    simpa using this
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank ℝ (Submodule.span ℝ (T : Set (Fin K → ℝ))) ≤ T.card :=
    finrank_span_finset_le_card T
  have h3 : T.card ≤ (U.erase c0).card := card_image_le
  have h4 := card_erase_add_one hc0
  omega

/-- **B1 (Lemma 2.1).** If `0 ∈ conv{u_1..u_m}` for a consecutively-sharing label tuple, then
`dim span ≤ m - 2`. -/
theorem rank_drop {K m : ℕ} (p : Fin m → Fin K × Fin K) (hne : ∀ j, (p j).1 ≠ (p j).2)
    (hcons : ConsecShare p) (h0 : (0 : Fin K → ℝ) ∈ convexHull ℝ (S p)) :
    Module.finrank ℝ (Submodule.span ℝ (S p)) + 2 ≤ m := by
  have h0' := h0
  rw [S, convexHull_range_eq_exists_affineCombination] at h0'
  obtain ⟨s, w, hw0, hw1, hcomb⟩ := h0'
  rw [affineCombination_eq_linear_combination _ _ _ hw1] at hcomb
  obtain ⟨h, hs, hpos⟩ : ∃ h ∈ s, 0 < w h := by
    by_contra hc
    push Not at hc
    have : ∑ i ∈ s, w i ≤ 0 := sum_nonpos hc
    linarith
  have hm : 0 < m := Fin.pos h
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  let g1 : ℕ → Fin K := fun k => (p ⟨min k n, by omega⟩).1
  let g2 : ℕ → Fin K := fun k => (p ⟨min k n, by omega⟩).2
  have hg1 : ∀ j : Fin (n + 1), g1 j = (p j).1 := by
    intro j; have e : min (j : ℕ) n = j := by omega
    simp only [g1, e]
  have hg2 : ∀ j : Fin (n + 1), g2 j = (p j).2 := by
    intro j; have e : min (j : ℕ) n = j := by omega
    simp only [g2, e]
  set A := (range (n + 1)).image g1 with hAdef
  set B := (range (n + 1)).image g2 with hBdef
  have hA : ∀ j : Fin (n + 1), (p j).1 ∈ A := fun j =>
    mem_image.2 ⟨j, mem_range.2 j.2, hg1 j⟩
  have hB : ∀ j : Fin (n + 1), (p j).2 ∈ B := fun j =>
    mem_image.2 ⟨j, mem_range.2 j.2, hg2 j⟩
  have hAmem : ∀ x ∈ A, ∃ j : Fin (n + 1), (p j).1 = x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
    exact ⟨_, rfl⟩
  have hBmem : ∀ x ∈ B, ∃ j : Fin (n + 1), (p j).2 = x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
    exact ⟨_, rfl⟩
  have hcoord : ∀ c, ∑ i ∈ s, w i * vec (p i) c = 0 := by
    intro c
    have := congrFun hcomb c
    simpa [Finset.sum_apply] using this
  -- a_h ∈ B
  have haB : (p h).1 ∈ B := by
    by_contra hn
    have hz : ∀ i ∈ s, (p i).2 ≠ (p h).1 := fun i _ e => hn (e ▸ hB i)
    have hle := Finset.single_le_sum (f := fun i => w i * vec (p i) (p h).1)
      (fun i hi => by
        simp only [rd_vec_apply, if_neg (hz i hi)]
        exact mul_nonneg (hw0 i hi) (by split_ifs <;> norm_num)) hs
    have := hcoord (p h).1
    simp only [rd_vec_apply, if_neg (hz h hs), if_true] at hle this
    linarith
  have hbA : (p h).2 ∈ A := by
    by_contra hn
    have hz : ∀ i ∈ s, (p i).1 ≠ (p h).2 := fun i _ e => hn (e ▸ hA i)
    have hle := Finset.single_le_sum (f := fun i => -(w i * vec (p i) (p h).2))
      (fun i hi => by
        simp only [rd_vec_apply, if_neg (hz i hi)]
        have := hw0 i hi
        split_ifs <;> nlinarith) hs
    have := hcoord (p h).2
    rw [← neg_eq_zero, ← Finset.sum_neg_distrib] at this
    simp only [rd_vec_apply, if_neg (hz h hs), if_true] at hle this
    linarith
  have hinter : 2 ≤ (A ∩ B).card := by
    have hsub : ({(p h).1, (p h).2} : Finset (Fin K)) ⊆ A ∩ B := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_inter.2 ⟨hA h, haB⟩
      · exact mem_inter.2 ⟨hbA, hB h⟩
    have := card_le_card hsub
    rwa [card_pair (hne h)] at this
  -- counting
  set cA := (range n).filter fun j => g1 (j + 1) ≠ g1 j
  set cB := (range n).filter fun j => g2 (j + 1) ≠ g2 j
  have hcardA : A.card ≤ 1 + cA.card := rd_image_card g1 n
  have hcardB : B.card ≤ 1 + cB.card := rd_image_card g2 n
  have hdisj : cA ∩ cB = ∅ := by
    ext j
    simp only [cA, cB, mem_inter, mem_filter, mem_range, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hj, h1⟩, -, h2⟩
    have hj1 := hg1 ⟨j, by omega⟩
    have hj1' := hg1 ⟨j + 1, by omega⟩
    have hj2 := hg2 ⟨j, by omega⟩
    have hj2' := hg2 ⟨j + 1, by omega⟩
    simp only at hj1 hj1' hj2 hj2'
    rcases hcons j (by omega) with e | e
    · exact h1 (by rw [hj1, hj1', e])
    · exact h2 (by rw [hj2, hj2', e])
  have hcAB : cA.card + cB.card ≤ n := by
    have e := card_union_add_card_inter cA cB
    rw [hdisj, card_empty] at e
    have : cA ∪ cB ⊆ range n := union_subset (filter_subset _ _) (filter_subset _ _)
    have := card_le_card this
    rw [card_range] at this
    omega
  have hU := card_union_add_card_inter A B
  have hfr := rd_finrank (S p) (A ∪ B) (p h).1 (mem_union_left _ (hA h)) (by
    rintro x ⟨j, rfl⟩
    exact ⟨_, mem_union_left _ (hA j), _, mem_union_right _ (hB j), rfl⟩)
  omega

/-! ## B2 helpers -/

lemma gram_det_ne_zero {s K : ℕ} (u : Fin s → Fin K → ℝ) (hu : LinearIndependent ℝ u) :
    (Matrix.of fun a b : Fin s => u a ⬝ᵥ u b).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h
  set w : Fin K → ℝ := ∑ b, v b • u b with hw
  have h1 : ∀ a, u a ⬝ᵥ w = 0 := by
    intro a
    have := congrFun hv a
    simp only [mulVec, dotProduct, of_apply, Pi.zero_apply] at this
    rw [hw, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
    simpa [dotProduct, mul_comm] using this
  have h2 : w ⬝ᵥ w = 0 := by
    have : w ⬝ᵥ w = ∑ b, v b * (u b ⬝ᵥ w) := by
      conv_lhs => rw [hw]
      rw [sum_dotProduct]
      simp [smul_dotProduct]; rfl
    rw [this]; simp [h1]
  have h3 : w = 0 := dotProduct_self_eq_zero.1 h2
  apply hv0
  funext b
  exact (Fintype.linearIndependent_iff.1 hu) v (by rw [← hw]; exact h3) b

noncomputable def Dpoly {K s : ℕ} (p : Fin s → Fin K × Fin K) : MvPolynomial (ℕ × Fin K) ℝ :=
  (Matrix.of fun a b : Fin s => ∑ c, MvPolynomial.X ((a : ℕ), c) * MvPolynomial.C (vec (p b) c)).det

lemma eval_Dpoly {K s : ℕ} (p : Fin s → Fin K × Fin K) (x : ℕ × Fin K → ℝ) :
    MvPolynomial.eval x (Dpoly p) =
      (Matrix.of fun a b : Fin s => (fun c => x ((a : ℕ), c)) ⬝ᵥ vec (p b)).det := by
  rw [Dpoly, RingHom.map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply, dotProduct]


lemma Dpoly_ne_zero {K s : ℕ} (p : Fin s → Fin K × Fin K)
    (hp : LinearIndependent ℝ (fun j => vec (p j))) : Dpoly p ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval
    (fun ac : ℕ × Fin K => if hs : ac.1 < s then vec (p ⟨ac.1, hs⟩) ac.2 else 0)) h
  rw [eval_Dpoly, map_zero] at this
  apply gram_det_ne_zero _ hp
  rw [← this]
  congr 1
  ext a b
  simp [dotProduct]

/-- **B2.** Generic functionals exist. -/
theorem exists_generic (K : ℕ) : ∃ ℓ : ℕ → Fin K → ℝ, Generic K ℓ := by
  let P : MvPolynomial (ℕ × Fin K) ℝ := ∏ s ∈ range (K + 1), ∏ p : Fin s → Fin K × Fin K,
    if LinearIndependent ℝ (fun j => vec (p j)) then Dpoly p else 1
  have hP : P ≠ 0 := by
    refine prod_ne_zero_iff.2 fun s _ => prod_ne_zero_iff.2 fun p _ => ?_
    split_ifs with h
    · exact Dpoly_ne_zero p h
    · exact one_ne_zero
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x P ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hP (MvPolynomial.funext fun x => by simpa using hc x)
  refine ⟨fun a c => x (a, c), fun s p hs _ hli => ?_⟩
  have hsK : s ∈ range (K + 1) := mem_range.2 (by omega)
  simp only [P, map_prod] at hx
  have h1 := (prod_ne_zero_iff.1 hx) s hsK
  have h2 := (prod_ne_zero_iff.1 h1) p (mem_univ _)
  rw [if_pos hli, eval_Dpoly] at h2
  exact h2


/-! ### Helpers for B3 / B5 -/

lemma vec_swap {K : ℕ} (q : Fin K × Fin K) : vec q.swap = - vec q := by
  simp [vec]

lemma vec_sum {K : ℕ} (q : Fin K × Fin K) : ∑ c, vec q c = 0 := by
  simp [vec, Finset.sum_sub_distrib]

lemma finrank_span_S_le {K n : ℕ} (q : Fin n → Fin K × Fin K) :
    Module.finrank ℝ (Submodule.span ℝ (S q)) ≤ K - 1 := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have := Submodule.finrank_le (Submodule.span ℝ (S q))
    rw [Module.finrank_fin_fun] at this
    omega
  · let f : (Fin K → ℝ) →ₗ[ℝ] ℝ := ∑ c, LinearMap.proj c
    have hle : Submodule.span ℝ (S q) ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp [f, vec_sum]
    have hne : Submodule.span ℝ (S q) ≠ ⊤ := by
      intro htop
      have : (Pi.single (⟨0, hK⟩ : Fin K) (1 : ℝ) : Fin K → ℝ) ∈ LinearMap.ker f :=
        hle (htop ▸ Submodule.mem_top)
      simp [f] at this
    have := Submodule.finrank_lt hne
    simp at this
    omega

lemma convexHull_subset_span' {K : ℕ} (X : Set (Fin K → ℝ)) :
    convexHull ℝ X ⊆ (Submodule.span ℝ X : Set (Fin K → ℝ)) :=
  convexHull_min Submodule.subset_span (Submodule.span ℝ X).convex

/-- Paper (4): the first `h ≥ dim U` functionals are jointly injective on `U = span`. -/
lemma key {K n : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) (q : Fin n → Fin K × Fin K)
    (hne : ∀ j, (q j).1 ≠ (q j).2) (h : ℕ)
    (hr : Module.finrank ℝ (Submodule.span ℝ (S q)) ≤ h) (w : Fin K → ℝ)
    (hw : w ∈ Submodule.span ℝ (S q)) (hH : InH ℓ h w) : w = 0 := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ (fun j => vec (q j))
  have : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  set r := Fintype.card κ with hr_def
  let e : Fin r ≃ κ := (Fintype.equivFin κ).symm
  let p : Fin r → Fin K × Fin K := fun b => q (a (e b))
  have hli' : LinearIndependent ℝ (fun b => vec (p b)) := hli.comp e e.injective
  have hspan' : Submodule.span ℝ (Set.range fun b => vec (p b)) = Submodule.span ℝ (S q) := by
    show _ = Submodule.span ℝ (Set.range fun j => vec (q j))
    rw [← hspan]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, p]
    constructor
    · rintro ⟨b, rfl⟩; exact ⟨e b, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨e.symm k, by simp⟩
  have hrank : r = Module.finrank ℝ (Submodule.span ℝ (S q)) := by
    rw [← hspan', finrank_span_eq_card hli']
    simp
  have hrK : r ≤ K - 1 := hrank ▸ finrank_span_S_le q
  have hdet := hℓ r p hrK (fun b => hne _) hli'
  rw [← hspan', Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, rfl⟩ := hw
  have hc : (Matrix.of fun a b : Fin r => ℓ a ⬝ᵥ vec (p b)) *ᵥ c = 0 := by
    funext a
    have := hH a (by omega)
    simp only [Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
    rw [dotProduct_sum] at this
    simp only [dotProduct_smul, smul_eq_mul] at this
    rw [← this]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun b _ => by ring
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet hc
  simp [this]

lemma mem_hull_swap {K m : ℕ} (p : Fin m → Fin K × Fin K) (w : Fin K → ℝ) :
    w ∈ convexHull ℝ (S (Prod.swap ∘ p)) ↔ -w ∈ convexHull ℝ (S p) := by
  have : S (Prod.swap ∘ p) = -S p := by
    ext x
    simp only [S, Set.mem_range, Function.comp_apply, vec_swap, Set.mem_neg]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨j, by simp⟩
    · rintro ⟨j, hj⟩; exact ⟨j, by rw [hj, neg_neg]⟩
  rw [this, convexHull_neg, Set.mem_neg]

lemma InH_neg {K : ℕ} {ℓ : ℕ → Fin K → ℝ} {i : ℕ} {w : Fin K → ℝ} (h : InH ℓ i w) :
    InH ℓ i (-w) := fun a ha => by simp [h a ha]

/-- If `0` lies in the hull of a family of vectors, the family is dependent. -/
lemma not_li_of_zero_mem {K m : ℕ} (u : Fin m → (Fin K → ℝ))
    (h0 : (0 : Fin K → ℝ) ∈ convexHull ℝ (Set.range u)) : ¬ LinearIndependent ℝ u := by
  intro hli
  have hrange : Set.range u = ((Finset.univ.image u : Finset _) : Set (Fin K → ℝ)) := by simp
  rw [hrange, Finset.mem_convexHull'] at h0
  obtain ⟨t, -, ht1, ht0⟩ := h0
  rw [Finset.sum_image (fun x _ y _ hxy => hli.injective hxy)] at ht1 ht0
  have := Fintype.linearIndependent_iff.mp hli (fun j => t (u j)) ht0
  simp [this] at ht1
/-- **B3 (Lemma 2.2).** For `i + 1` label vectors (`i < d`): the hull meets at most one of the two
open half-spaces `H_i^±`, and meets `H_i \ {0}` iff it meets one of them. (`Prod.swap` negates
`vec`.) -/
theorem sign_split {K : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) {i : ℕ} (hi : i < K - 1)
    (p : Fin (i + 1) → Fin K × Fin K) (hne : ∀ j, (p j).1 ≠ (p j).2) :
    ¬ (Alpha ℓ i (S p) ∧ Alpha ℓ i (S (Prod.swap ∘ p))) ∧
      (Beta ℓ i (S p) ↔ Alpha ℓ i (S p) ∨ Alpha ℓ i (S (Prod.swap ∘ p))) := by
  have hU : Module.finrank ℝ (Submodule.span ℝ (S p)) ≤ i + 1 := by
    have := finrank_range_le_card (R := ℝ) (fun j => vec (p j))
    rw [Fintype.card_fin] at this
    exact this
  have hnz : ∀ w ∈ convexHull ℝ (S p), InH ℓ i w → ℓ i ⬝ᵥ w = 0 → w = 0 :=
    fun w hw hH h0 => key hℓ p hne (i + 1) hU w (convexHull_subset_span' _ hw) (fun a ha => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
      · exact hH a ha
      · exact h0)
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨w1, hw1, hH1, h1⟩, ⟨w2', hw2', hH2', h2'⟩⟩
    rw [mem_hull_swap] at hw2'
    have hH2 := InH_neg hH2'
    set w2 := -w2' with hw2_def
    set A := ℓ i ⬝ᵥ w1 with hA
    set B := -(ℓ i ⬝ᵥ w2) with hB
    have hBpos : 0 < B := by simp [hB, w2, dotProduct_neg]; exact h2'
    have hv : B • w1 + A • w2 = 0 := by
      apply key hℓ p hne (i + 1) hU
      · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (convexHull_subset_span' _ hw1))
          (Submodule.smul_mem _ _ (convexHull_subset_span' _ hw2'))
      · intro a ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
        · simp [dotProduct_add, dotProduct_smul, hH1 a ha, hH2 a ha]
        · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hA, hB]
          ring
    have h0 : (0 : Fin K → ℝ) ∈ convexHull ℝ (S p) := by
      have hAB : 0 < A + B := by linarith
      have := (convex_convexHull ℝ (S p)) hw1 hw2' (a := B / (A + B)) (b := A / (A + B))
        (by positivity) (by positivity) (by rw [← add_div, add_comm B A, div_self hAB.ne'])
      convert this using 1
      rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, hv, smul_zero]
    have hdep := not_li_of_zero_mem (fun j => vec (p j)) h0
    have hr : Module.finrank ℝ (Submodule.span ℝ (S p)) ≤ i := by
      by_contra hc
      apply hdep
      rw [linearIndependent_iff_card_eq_finrank_span]
      simp only [Fintype.card_fin, Set.finrank]
      show i + 1 = Module.finrank ℝ (Submodule.span ℝ (S p))
      omega
    have := key hℓ p hne i hr w1 (convexHull_subset_span' _ hw1) hH1
    have h1' : 0 < ℓ i ⬝ᵥ w1 := h1
    rw [this] at h1'
    simp at h1'
  · constructor
    · rintro ⟨w, hw, hH, hw0⟩
      rcases lt_trichotomy (ℓ i ⬝ᵥ w) 0 with h | h | h
      · right
        exact ⟨-w, (mem_hull_swap p _).mpr (by simpa using hw), InH_neg hH,
          by simp [dotProduct_neg]; linarith⟩
      · exact absurd (hnz w hw hH h) hw0
      · left
        exact ⟨w, hw, hH, h⟩
    · rintro (⟨w, hw, hH, h⟩ | ⟨w, hw, hH, h⟩)
      · exact ⟨w, hw, hH, fun h0 => by simp [h0] at h⟩
      · refine ⟨-w, (mem_hull_swap p w).mp hw, InH_neg hH, fun h0 => ?_⟩
        have : w = 0 := neg_eq_zero.mp h0
        simp [this] at h

/-! ### Helpers copied from sign_split.lean -/

/-! ### Helpers for B4 (local parity) -/

/-- Linear combination of the label vectors with coefficients `t`. -/
noncomputable def wt {K m : ℕ} (p : Fin m → Fin K × Fin K) (t : Fin m → ℝ) : Fin K → ℝ :=
  ∑ j, t j • vec (p j)

lemma wt_add {K m : ℕ} (p : Fin m → Fin K × Fin K) (t t' : Fin m → ℝ) :
    wt p (t + t') = wt p t + wt p t' := by
  simp [wt, add_smul, Finset.sum_add_distrib]

lemma wt_sub {K m : ℕ} (p : Fin m → Fin K × Fin K) (t t' : Fin m → ℝ) :
    wt p (t - t') = wt p t - wt p t' := by
  simp [wt, sub_smul, Finset.sum_sub_distrib]

lemma wt_smul {K m : ℕ} (p : Fin m → Fin K × Fin K) (r : ℝ) (t : Fin m → ℝ) :
    wt p (r • t) = r • wt p t := by
  simp [wt, Finset.smul_sum, smul_smul]

lemma wt_insertNth {K m : ℕ} (p : Fin (m + 1) → Fin K × Fin K) (s : Fin (m + 1)) (a : ℝ)
    (x : Fin m → ℝ) : wt p (Fin.insertNth s a x) = a • vec (p s) + wt (p ∘ s.succAbove) x := by
  simp [wt, Fin.sum_univ_succAbove _ s]

lemma wt_of_zero {K m : ℕ} (p : Fin (m + 1) → Fin K × Fin K) (t : Fin (m + 1) → ℝ)
    (s : Fin (m + 1)) (hs : t s = 0) : wt p t = wt (p ∘ s.succAbove) (t ∘ s.succAbove) := by
  simp [wt, Fin.sum_univ_succAbove _ s, hs]

lemma dot_wt {K m : ℕ} (p : Fin m → Fin K × Fin K) (t : Fin m → ℝ) (v : Fin K → ℝ) :
    v ⬝ᵥ wt p t = ∑ j, t j * (v ⬝ᵥ vec (p j)) := by
  simp [wt, dotProduct_sum, dotProduct_smul]

lemma mem_hull_range {K n : ℕ} (v : Fin n → (Fin K → ℝ)) (y : Fin K → ℝ) :
    y ∈ convexHull ℝ (Set.range v) ↔
      ∃ μ : Fin n → ℝ, (∀ j, 0 ≤ μ j) ∧ ∑ j, μ j = 1 ∧ ∑ j, μ j • v j = y := by
  constructor
  · intro hy
    rw [convexHull_range_eq_exists_affineCombination] at hy
    obtain ⟨s, w, hw0, hw1, rfl⟩ := hy
    refine ⟨fun j => if j ∈ s then w j else 0, ?_, ?_, ?_⟩
    · intro j
      show 0 ≤ (if j ∈ s then w j else 0)
      split_ifs with h
      exacts [hw0 j h, le_rfl]
    · rw [Finset.sum_ite_mem, Finset.univ_inter, hw1]
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1]
      simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
  · rintro ⟨μ, h0, h1, rfl⟩
    exact mem_convexHull_of_exists_fintype μ v h0 h1 (fun j => ⟨j, rfl⟩) rfl

lemma sum_pos_of_wt_ne {K m : ℕ} (p : Fin m → Fin K × Fin K) (t : Fin m → ℝ)
    (h0 : ∀ j, 0 ≤ t j) (hw : wt p t ≠ 0) : 0 < ∑ j, t j := by
  rcases (Finset.sum_nonneg fun j _ => h0 j).lt_or_eq with h | h
  · exact h
  · exfalso; apply hw
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h0 j).1 h.symm
    simp [wt, this]

lemma alpha_iff {K i : ℕ} {ℓ : ℕ → Fin K → ℝ} (p : Fin (i + 2) → Fin K × Fin K)
    (s : Fin (i + 2)) :
    Alpha ℓ i (S (p ∘ s.succAbove)) ↔
      ∃ t : Fin (i + 2) → ℝ, (∀ j, 0 ≤ t j) ∧ t s = 0 ∧ InH ℓ i (wt p t) ∧
        ℓ i ⬝ᵥ wt p t = 1 := by
  constructor
  · rintro ⟨y, hy, hH, hpos⟩
    obtain ⟨μ, h0, h1, hμ⟩ := (mem_hull_range _ _).1 hy
    have hwy : wt p (Fin.insertNth s 0 μ) = y := by
      rw [wt_insertNth, zero_smul, zero_add, ← hμ]; rfl
    refine ⟨(ℓ i ⬝ᵥ y)⁻¹ • Fin.insertNth s 0 μ, ?_, by simp, ?_, ?_⟩
    · intro j
      refine Fin.succAboveCases s ?_ (fun j => ?_) j
      · simp
      · simp only [Pi.smul_apply, Fin.insertNth_apply_succAbove, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 hpos.le) (h0 j)
    · intro a ha
      rw [wt_smul, hwy, dotProduct_smul, hH a ha, smul_zero]
    · rw [wt_smul, hwy, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hpos.ne']
  · rintro ⟨t, h0, hs, hH, h1⟩
    have hne : wt p t ≠ 0 := by intro h; rw [h] at h1; simp at h1
    have hσ := sum_pos_of_wt_ne p t h0 hne
    set σ := ∑ j, t j
    refine ⟨σ⁻¹ • wt p t, ?_, ?_, ?_⟩
    · refine (mem_hull_range _ _).2 ?_
      refine ⟨fun j => σ⁻¹ * t (s.succAbove j), fun j => mul_nonneg (inv_nonneg.2 hσ.le) (h0 _),
        ?_, ?_⟩
      · rw [← Finset.mul_sum]
        have : ∑ j, t (s.succAbove j) = σ := by
          simp only [σ]; rw [Fin.sum_univ_succAbove _ s, hs, zero_add]
        rw [this, inv_mul_cancel₀ hσ.ne']
      · rw [wt_of_zero p t s hs, wt, Finset.smul_sum]
        simp [smul_smul]
    · intro a ha; rw [dotProduct_smul, hH a ha, smul_zero]
    · rw [dotProduct_smul, h1, smul_eq_mul, mul_one]; exact inv_pos.2 hσ

lemma beta_iff {K m h : ℕ} {ℓ : ℕ → Fin K → ℝ} (p : Fin m → Fin K × Fin K) :
    Beta ℓ h (S p) ↔ ∃ c : Fin m → ℝ, (∀ j, 0 ≤ c j) ∧ InH ℓ h (wt p c) ∧ wt p c ≠ 0 := by
  constructor
  · rintro ⟨y, hy, hH, hne⟩
    obtain ⟨μ, h0, -, rfl⟩ := (mem_hull_range _ _).1 hy
    exact ⟨μ, h0, hH, hne⟩
  · rintro ⟨c, h0, hH, hne⟩
    have hσ := sum_pos_of_wt_ne p c h0 hne
    refine ⟨(∑ j, c j)⁻¹ • wt p c, ?_, ?_, ?_⟩
    · refine (mem_hull_range _ _).2 ?_
      refine ⟨fun j => (∑ j, c j)⁻¹ * c j, fun j => mul_nonneg (inv_nonneg.2 hσ.le) (h0 _),
        ?_, ?_⟩
      · rw [← Finset.mul_sum, inv_mul_cancel₀ hσ.ne']
      · rw [wt, Finset.smul_sum]; simp [smul_smul]
    · intro a ha; rw [dotProduct_smul, hH a ha, smul_zero]
    · exact smul_ne_zero (inv_ne_zero hσ.ne') hne

/-- Paper (4), support form: a combination supported on `≤ h` label vectors lying in `H_h` is 0. -/
lemma key_supp {K m : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) (p : Fin m → Fin K × Fin K)
    (hne : ∀ j, (p j).1 ≠ (p j).2) (T : Finset (Fin m)) (t : Fin m → ℝ)
    (ht : ∀ j ∉ T, t j = 0) (h : ℕ) (hT : T.card ≤ h) (hH : InH ℓ h (wt p t)) : wt p t = 0 := by
  let e := T.equivFin
  let q : Fin T.card → Fin K × Fin K := fun b => p (e.symm b)
  refine key hℓ q (fun b => hne _) h ?_ _ ?_ hH
  · calc Module.finrank ℝ (Submodule.span ℝ (S q)) ≤ Fintype.card (Fin T.card) :=
          finrank_range_le_card _
      _ ≤ h := by simpa using hT
  · refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j ∈ T
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e ⟨j, hj⟩, by simp [q]⟩)
    · simp [ht j hj]

lemma no_rel {K m : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) (p : Fin m → Fin K × Fin K)
    (hne : ∀ j, (p j).1 ≠ (p j).2) (x : Fin m → ℝ) (h : ℕ) (hm : m ≤ h + 1)
    (hH : InH ℓ h (wt p x)) (hx : wt p x ≠ 0) (G : Fin m → ℝ) (hG : wt p G = 0) (L : Fin m)
    (hL : G L ≠ 0) : False := by
  apply hx
  have hx' : wt p (x - (x L / G L) • G) = wt p x := by
    rw [wt_sub, wt_smul, hG, smul_zero, sub_zero]
  rw [← hx']
  refine key_supp hℓ p hne (Finset.univ.erase L) _ ?_ h ?_ (hx' ▸ hH)
  · intro j hj
    have : j = L := by simpa using hj
    subst this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega

lemma li_of {K m : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) (q : Fin m → Fin K × Fin K)
    (hne : ∀ j, (q j).1 ≠ (q j).2) (x : Fin m → ℝ) (h : ℕ) (hm : m ≤ h + 1)
    (hH : InH ℓ h (wt q x)) (hx : wt q x ≠ 0) : LinearIndependent ℝ (fun j => vec (q j)) := by
  by_contra hli
  rw [Fintype.not_linearIndependent_iff] at hli
  obtain ⟨g, hg, L, hL⟩ := hli
  exact no_rel hℓ q hne x h hm hH hx g hg L hL

lemma li_sub {K n : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) (p : Fin (n + 1) → Fin K × Fin K)
    (hne : ∀ j, (p j).1 ≠ (p j).2) (x : Fin (n + 1) → ℝ) (h : ℕ) (hm : n + 1 ≤ h + 1)
    (hH : InH ℓ h (wt p x)) (hx : wt p x ≠ 0) (s : Fin (n + 1)) :
    LinearIndependent ℝ (fun j => vec ((p ∘ s.succAbove) j)) := by
  by_contra hli
  rw [Fintype.not_linearIndependent_iff] at hli
  obtain ⟨g, hg, l, hl⟩ := hli
  refine no_rel hℓ p hne x h hm hH hx (Fin.insertNth s 0 g) ?_ (s.succAbove l) ?_
  · rw [wt_insertNth, zero_smul, zero_add]; exact hg
  · simpa using hl

lemma solve {K n : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) (q : Fin n → Fin K × Fin K)
    (hne : ∀ j, (q j).1 ≠ (q j).2) (hn : n ≤ K - 1)
    (hli : LinearIndependent ℝ fun j => vec (q j)) (y : Fin n → ℝ) :
    ∃ x : Fin n → ℝ, ∀ a : Fin n, ℓ a ⬝ᵥ wt q x = y a := by
  have hdet := hℓ n q hn hne hli
  set A := Matrix.of fun a b : Fin n => ℓ a ⬝ᵥ vec (q b)
  refine ⟨A⁻¹ *ᵥ y, fun a => ?_⟩
  have h1 : A *ᵥ (A⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  conv_rhs => rw [← h1]
  rw [dot_wt]
  simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma ker_zero {K i : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) (p : Fin (i + 2) → Fin K × Fin K)
    (hne : ∀ j, (p j).1 ≠ (p j).2) (k : Fin (i + 2))
    (hli : LinearIndependent ℝ (fun j => vec ((p ∘ k.succAbove) j))) (d : Fin (i + 2) → ℝ)
    (hdk : d k = 0) (hH : InH ℓ (i + 1) (wt p d)) : d = 0 := by
  have h0 : wt p d = 0 := by
    refine key_supp hℓ p hne (Finset.univ.erase k) d ?_ (i + 1) ?_ hH
    · intro j hj
      have : j = k := by simpa using hj
      rw [this, hdk]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
  rw [wt_of_zero p d k hdk] at h0
  have := Fintype.linearIndependent_iff.1 hli (d ∘ k.succAbove) h0
  funext j
  refine Fin.succAboveCases k ?_ (fun j => ?_) j
  · exact hdk
  · exact this j

/-- **B4 (Lemma 2.3).** Local parity: for `i + 2` consecutively-sharing labels (`i < d`), the number
of one-point deletions whose hull meets `H_i⁺` is odd iff the full hull meets `H_{i+1} \ {0}`. -/
theorem local_parity {K : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) {i : ℕ} (hi : i < K - 1)
    (p : Fin (i + 2) → Fin K × Fin K) (hne : ∀ j, (p j).1 ≠ (p j).2) (hcons : ConsecShare p) :
    ((univ.filter fun s : Fin (i + 2) => Alpha ℓ i (S (p ∘ s.succAbove))).card : ZMod 2) =
      if Beta ℓ (i + 1) (S p) then 1 else 0 := by
  classical
  have hi1 : i + 1 ≤ K - 1 := hi
  -- a point of `J` has at most one zero coordinate
  have hzero : ∀ t : Fin (i + 2) → ℝ, ℓ i ⬝ᵥ wt p t = 1 → InH ℓ i (wt p t) →
      ∀ s1 s2, t s1 = 0 → t s2 = 0 → s1 = s2 := by
    intro t h1 hH s1 s2 hs1 hs2
    by_contra h12
    have : wt p t = 0 := by
      refine key_supp hℓ p hne ((univ.erase s1).erase s2) t ?_ i ?_ hH
      · intro j hj
        simp only [mem_erase, mem_univ, and_true, not_and_or, not_not] at hj
        rcases hj with h | h
        · rw [h, hs2]
        · rw [h, hs1]
      · rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm h12, mem_univ _⟩),
          card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
        omega
    rw [this] at h1; simp at h1
  by_cases hEne : (univ.filter fun s : Fin (i + 2) => Alpha ℓ i (S (p ∘ s.succAbove))).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hEne, if_neg]
    · simp
    intro hB
    obtain ⟨c, hc0, hcH, hcne⟩ := (beta_iff p).1 hB
    have hcpos : ∀ j, 0 < c j := by
      intro j
      rcases (hc0 j).lt_or_eq with h | h
      · exact h
      exfalso; apply hcne
      refine key_supp hℓ p hne (univ.erase j) c ?_ (i + 1) ?_ hcH
      · intro j' hj'
        have : j' = j := by simpa using hj'
        rw [this, h]
      · rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
        omega
    have hli := li_sub hℓ p hne c (i + 1) le_rfl hcH hcne (Fin.last (i + 1))
    obtain ⟨x, hx⟩ := solve hℓ (p ∘ (Fin.last (i + 1)).succAbove) (fun _ => hne _) hi1 hli
      (Pi.single (Fin.last i) 1)
    set t0 : Fin (i + 2) → ℝ := Fin.insertNth (α := fun _ => ℝ) (Fin.last (i + 1)) 0 x with ht0def
    have hw0 : wt p t0 = wt (p ∘ (Fin.last (i + 1)).succAbove) x := by
      rw [ht0def, wt_insertNth, zero_smul, zero_add]
    obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image univ (fun j => -t0 j / c j) univ_nonempty
    set lam := -t0 j0 / c j0 with hlam
    set t := t0 + lam • c with htdef
    have ht : ∀ j, 0 ≤ t j := by
      intro j
      have h1 : -t0 j / c j ≤ lam := hj0 j (mem_univ _)
      rw [div_le_iff₀ (hcpos j)] at h1
      simp only [htdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have htj0 : t j0 = 0 := by
      have hcj := (hcpos j0).ne'
      simp only [htdef, hlam, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    have hwt : wt p t = wt p t0 + lam • wt p c := by rw [htdef, wt_add, wt_smul]
    have hJ1 : InH ℓ i (wt p t) := by
      intro a ha
      rw [hwt, dotProduct_add, dotProduct_smul, hcH a (by omega), smul_zero, add_zero, hw0]
      have := hx ⟨a, by omega⟩
      simp only at this
      rw [this, Pi.single_apply, if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hJ2 : ℓ i ⬝ᵥ wt p t = 1 := by
      rw [hwt, dotProduct_add, dotProduct_smul, hcH i (by omega), smul_zero, add_zero, hw0]
      have := hx (Fin.last i)
      simp only [Fin.val_last] at this
      rw [this]
      simp
    apply hEne
    exact ⟨j0, mem_filter.2 ⟨mem_univ _, (alpha_iff p j0).2 ⟨t, ht, htj0, hJ1, hJ2⟩⟩⟩
  · obtain ⟨k, hk⟩ := hEne
    have hkA := (mem_filter.1 hk).2
    obtain ⟨tk, htk0, htkk, htkH, htk1⟩ := (alpha_iff p k).1 hkA
    have hli : LinearIndependent ℝ (fun j => vec ((p ∘ k.succAbove) j)) := by
      refine li_of hℓ (p ∘ k.succAbove) (fun _ => hne _) (tk ∘ k.succAbove) i (by omega)
        ?_ ?_
      · rw [← wt_of_zero p tk k htkk]; exact htkH
      · rw [← wt_of_zero p tk k htkk]
        intro h; rw [h] at htk1; simp at htk1
    obtain ⟨x, hx⟩ := solve hℓ (p ∘ k.succAbove) (fun _ => hne _) hi1 hli
      (fun a => -(ℓ a ⬝ᵥ vec (p k)))
    set c : Fin (i + 2) → ℝ := Fin.insertNth (α := fun _ => ℝ) k 1 x with hcdef
    have hck : c k = 1 := by simp [hcdef]
    have hcH : InH ℓ (i + 1) (wt p c) := by
      intro a ha
      rw [hcdef, wt_insertNth, one_smul, dotProduct_add]
      have := hx ⟨a, ha⟩
      simp only at this
      rw [this]; ring
    have hline : ∀ t, InH ℓ i (wt p t) → ℓ i ⬝ᵥ wt p t = 1 → t = tk + t k • c := by
      intro t hH h1
      have := ker_zero hℓ p hne k hli (t - (tk + t k • c)) (by simp [htkk, hck]) ?_
      · exact sub_eq_zero.1 this
      · intro a ha
        rw [wt_sub, wt_add, wt_smul, dotProduct_sub, dotProduct_add, dotProduct_smul,
          hcH a ha, smul_zero, add_zero]
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | ha
        · rw [hH a ha, htkH a ha, sub_zero]
        · subst ha; rw [h1, htk1, sub_self]
    have htkpos : ∀ j, j ≠ k → 0 < tk j := fun j hj =>
      lt_of_le_of_ne (htk0 j) (fun h => hj (hzero tk htk1 htkH j k h.symm htkk))
    by_cases hcpos : ∀ j, 0 ≤ c j
    · have hE1 : (univ.filter fun s : Fin (i + 2) => Alpha ℓ i (S (p ∘ s.succAbove))) = {k} := by
        ext s
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hs
          obtain ⟨t, ht0, hts, htH, ht1⟩ := (alpha_iff p s).1 hs
          by_contra hsk
          have e1 := congrFun (hline t htH ht1) s
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1
          have : 0 < tk s + t k * c s :=
            add_pos_of_pos_of_nonneg (htkpos s hsk) (mul_nonneg (ht0 k) (hcpos s))
          linarith
        · rintro rfl; exact hkA
      have hB : Beta ℓ (i + 1) (S p) := by
        refine (beta_iff p).2 ⟨c, hcpos, hcH, ?_⟩
        intro h0
        have hσ : 0 < ∑ j, c j := by
          have := Finset.single_le_sum (fun j _ => hcpos j) (mem_univ k)
          rw [hck] at this; linarith
        have h0mem : (0 : Fin K → ℝ) ∈ convexHull ℝ (S p) := by
          refine (mem_hull_range _ _).2 ⟨fun j => (∑ j, c j)⁻¹ * c j,
            fun j => mul_nonneg (inv_nonneg.2 hσ.le) (hcpos j), ?_, ?_⟩
          · rw [← Finset.mul_sum, inv_mul_cancel₀ hσ.ne']
          · have : ∑ j, ((∑ j, c j)⁻¹ * c j) • vec (p j) = (∑ j, c j)⁻¹ • wt p c := by
              rw [wt, Finset.smul_sum]; simp [smul_smul]
            rw [this, h0, smul_zero]
        have hrd := rank_drop p hne hcons h0mem
        have hrank : i + 1 ≤ Module.finrank ℝ (Submodule.span ℝ (S p)) := by
          have h1 := finrank_span_eq_card hli
          calc i + 1 = Module.finrank ℝ (Submodule.span ℝ
                (Set.range fun j => vec ((p ∘ k.succAbove) j))) := by
                rw [h1, Fintype.card_fin]
            _ ≤ _ := by
                apply Submodule.finrank_mono
                apply Submodule.span_mono
                rintro _ ⟨j, rfl⟩
                exact ⟨k.succAbove j, rfl⟩
        omega
      rw [hE1, if_pos hB]
      simp
    · push Not at hcpos
      obtain ⟨jn, hjn⟩ := hcpos
      have hnB : ¬ Beta ℓ (i + 1) (S p) := by
        intro hB
        obtain ⟨c', hc'0, hc'H, hc'ne⟩ := (beta_iff p).1 hB
        have hc' : c' = c' k • c := by
          have := ker_zero hℓ p hne k hli (c' - c' k • c) (by simp [hck]) (by
            intro a ha
            rw [wt_sub, wt_smul, dotProduct_sub, dotProduct_smul, hc'H a ha, hcH a ha]
            simp)
          exact sub_eq_zero.1 this
        have h1 := hc'0 jn
        rw [hc'] at h1
        simp only [Pi.smul_apply, smul_eq_mul] at h1
        have hk0 : c' k = 0 := by
          rcases (hc'0 k).lt_or_eq with h | h
          · nlinarith
          · exact h.symm
        apply hc'ne
        rw [hc', hk0, zero_smul]
        simp [wt]
      obtain ⟨js, hjsN, hjs⟩ := Finset.exists_min_image (univ.filter fun j => c j < 0)
        (fun j => tk j / -c j) ⟨jn, mem_filter.2 ⟨mem_univ _, hjn⟩⟩
      have hjs_neg : c js < 0 := (mem_filter.1 hjsN).2
      have hjsk : js ≠ k := by
        rintro rfl; rw [hck] at hjs_neg; norm_num at hjs_neg
      set lam := tk js / -c js with hlam
      have hlam0 : 0 ≤ lam := div_nonneg (htk0 js) (by linarith)
      set ts := tk + lam • c with htsdef
      have hts0 : ∀ j, 0 ≤ ts j := by
        intro j
        simp only [htsdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hj : c j < 0
        · have := hjs j (mem_filter.2 ⟨mem_univ _, hj⟩)
          rw [le_div_iff₀ (by linarith)] at this
          linarith
        · push Not at hj
          nlinarith [htk0 j]
      have htsjs : ts js = 0 := by
        have hcj := hjs_neg.ne
        simp only [htsdef, hlam, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      have hwts : wt p ts = wt p tk + lam • wt p c := by rw [htsdef, wt_add, wt_smul]
      have htsH : InH ℓ i (wt p ts) := by
        intro a ha
        rw [hwts, dotProduct_add, dotProduct_smul, hcH a (by omega), htkH a ha]
        simp
      have hts1 : ℓ i ⬝ᵥ wt p ts = 1 := by
        rw [hwts, dotProduct_add, dotProduct_smul, hcH i (by omega), htk1]
        simp
      have hE2 : (univ.filter fun s : Fin (i + 2) => Alpha ℓ i (S (p ∘ s.succAbove))) =
          {k, js} := by
        ext s
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · intro hs
          obtain ⟨t, ht0, hts, htH, ht1⟩ := (alpha_iff p s).1 hs
          have hl := hline t htH ht1
          rcases (ht0 k).lt_or_eq with hpos | hz
          · right
            have e1 := congrFun hl s
            have e2 := congrFun hl js
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
            have hsk : s ≠ k := by
              rintro rfl; linarith
            have htks := htkpos s hsk
            have hcs : c s < 0 := by
              by_contra hcs; push Not at hcs
              nlinarith
            have hge : lam ≤ tk s / -c s := hjs s (mem_filter.2 ⟨mem_univ _, hcs⟩)
            have htk_eq : t k = tk s / -c s := by
              rw [eq_div_iff (by linarith)]; linarith
            have hle : t k ≤ lam := by
              rw [hlam, le_div_iff₀ (by linarith)]
              nlinarith [ht0 js]
            have hkl : t k = lam := le_antisymm hle (htk_eq ▸ hge)
            have htts : t = ts := by rw [hl, hkl]
            exact hzero ts hts1 htsH s js (htts ▸ hts) htsjs
          · left
            have htt : t = tk := by rw [hl, ← hz, zero_smul, add_zero]
            exact hzero tk htk1 htkH s k (htt ▸ hts) htkk
        · rintro (rfl | rfl)
          · exact hkA
          · exact (alpha_iff p _).2 ⟨ts, hts0, htsjs, htsH, hts1⟩
      rw [hE2, if_neg hnB, card_pair hjsk.symm]
      rfl

/-- **B5.** `H_d = {0}` on label vectors: no hull of label vectors meets `H_{K-1} \ {0}`. -/
theorem top_trivial {K m : ℕ} {ℓ : ℕ → Fin K → ℝ} (hℓ : Generic K ℓ) (hK : 2 ≤ K)
    (p : Fin m → Fin K × Fin K) (hne : ∀ j, (p j).1 ≠ (p j).2) : ¬ Beta ℓ (K - 1) (S p) := by
  rintro ⟨w, hw, hH, hw0⟩
  exact hw0 (key hℓ p hne (K - 1) (finrank_span_S_le p) w (convexHull_subset_span' _ hw) hH)

/-! ## Combinatorics of faces and monotone paths -/

abbrev V (K : ℕ) := Fin K → Bool

def anti {K : ℕ} (x : V K) : V K := fun c => !x c

def flip {K : ℕ} (x : V K) (c : Fin K) : V K := Function.update x c (!x c)

/-- Fixed bits of the alternating face with free set `T`: reading the coordinates outside `T` in
increasing order, the fixed bits are `0, 1, 0, 1, …` (`false, true, …`). Bits on `T` are `false`. -/
def altBase {K : ℕ} (T : Finset (Fin K)) : V K := fun c =>
  if c ∈ T then false else decide (Odd ((Tᶜ.filter (· < c)).card))

/-- The monotone path with order `σ` in the face with fixed bits `b` (outside `range σ`): its
`j`-th vertex has the first `j` free coordinates `σ 0, …, σ (j-1)` set to `true`, the other free
coordinates `false`, and agrees with `b` off `range σ`. -/
def pathOf {K i : ℕ} (b : V K) (σ : Fin i ↪ Fin K) : Fin (i + 1) → V K := fun j c =>
  if ∃ k : Fin i, k.val < j.val ∧ σ k = c then true else if c ∈ Set.range σ then false else b c

/-- Consecutive vertices of `x` differ by a single coordinate flip. -/
def IsWalk {K n : ℕ} (x : Fin n → V K) : Prop :=
  ∀ (j : ℕ) (h : j + 1 < n), ∃ c, x ⟨j + 1, h⟩ = flip (x ⟨j, by omega⟩) c

lemma pathOf_succ {K i : ℕ} (b : V K) (σ : Fin (i + 1) ↪ Fin K) (j : Fin (i + 1)) :
    pathOf b σ j.succ = pathOf (Function.update b (σ 0) true) ((Fin.succEmb i).trans σ) j := by
  funext c
  simp only [pathOf, Function.Embedding.trans_apply, Fin.coe_succEmb, Set.mem_range, Fin.val_succ]
  by_cases hc : c = σ 0
  · subst hc
    have h1 : ∃ k : Fin (i+1), k.val < j.val + 1 ∧ σ k = σ 0 := ⟨0, by simp⟩
    have h2 : ¬ ∃ k : Fin i, k.val < j.val ∧ σ k.succ = σ 0 := by
      rintro ⟨k, -, hk⟩; exact Fin.succ_ne_zero k (σ.injective hk)
    have h3 : ¬ ∃ k : Fin i, σ k.succ = σ 0 := by
      rintro ⟨k, hk⟩; exact Fin.succ_ne_zero k (σ.injective hk)
    simp
  · have e1 : (∃ k : Fin (i+1), k.val < j.val + 1 ∧ σ k = c) ↔
        ∃ k : Fin i, k.val < j.val ∧ σ k.succ = c := by
      constructor
      · rintro ⟨k, hk, rfl⟩
        cases k using Fin.cases with
        | zero => exact absurd rfl hc
        | succ k => exact ⟨k, by simpa using hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨k.succ, by simpa using hk, rfl⟩
    have e2 : (∃ k : Fin (i+1), σ k = c) ↔ ∃ k : Fin i, σ k.succ = c := by
      constructor
      · rintro ⟨k, rfl⟩
        cases k using Fin.cases with
        | zero => exact absurd rfl hc
        | succ k => exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩; exact ⟨k.succ, rfl⟩
    simp only [e1, e2, Function.update_of_ne hc]

lemma pathOf_castSucc {K i : ℕ} (b : V K) (σ : Fin (i + 1) ↪ Fin K) (j : Fin (i + 1)) :
    pathOf b σ j.castSucc =
      pathOf (Function.update b (σ (Fin.last i)) false) (Fin.castSuccEmb.trans σ) j := by
  funext c
  simp only [pathOf, Function.Embedding.trans_apply, Fin.coe_castSuccEmb, Set.mem_range,
    Fin.val_castSucc]
  have e1 : (∃ k : Fin (i+1), k.val < j.val ∧ σ k = c) ↔
      ∃ k : Fin i, k.val < j.val ∧ σ k.castSucc = c := by
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k.val, by omega⟩, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k.castSucc, by simpa using hk, rfl⟩
  simp only [e1]
  by_cases hc : c = σ (Fin.last i)
  · subst hc
    have h2 : ¬ ∃ k : Fin i, k.val < j.val ∧ σ k.castSucc = σ (Fin.last i) := by
      rintro ⟨k, -, hk⟩; exact Fin.castSucc_ne_last k (σ.injective hk)
    have h3 : ¬ ∃ k : Fin i, σ k.castSucc = σ (Fin.last i) := by
      rintro ⟨k, hk⟩; exact Fin.castSucc_ne_last k (σ.injective hk)
    simp
  · have e2 : (∃ k : Fin (i+1), σ k = c) ↔ ∃ k : Fin i, σ k.castSucc = c := by
      constructor
      · rintro ⟨k, rfl⟩
        cases k using Fin.lastCases with
        | last => exact absurd rfl hc
        | cast k => exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩; exact ⟨k.castSucc, rfl⟩
    simp only [e2, Function.update_of_ne hc]

/-- swap of adjacent positions -/
def swapEmb {K i : ℕ} (k : Fin i) (σ : Fin (i + 1) ↪ Fin K) : Fin (i + 1) ↪ Fin K :=
  (Equiv.swap k.castSucc k.succ).toEmbedding.trans σ

lemma pathOf_swapEmb {K i : ℕ} (b : V K) (k : Fin i) (σ : Fin (i + 1) ↪ Fin K) (v : Fin (i + 2))
    (hv : v.val ≠ k.val + 1) : pathOf b (swapEmb k σ) v = pathOf b σ v := by
  funext c
  have hr : Set.range (swapEmb k σ) = Set.range σ := by
    show Set.range (σ ∘ Equiv.swap k.castSucc k.succ) = _
    rw [EquivLike.range_comp]
  have key : ∀ m : Fin (i + 1), ((Equiv.swap k.castSucc k.succ m).val < v.val ↔ m.val < v.val) := by
    intro m
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; simp; omega
    · subst h2; simp; omega
    · rfl
  have e1 : (∃ m : Fin (i+1), m.val < v.val ∧ swapEmb k σ m = c) ↔
      ∃ m : Fin (i+1), m.val < v.val ∧ σ m = c := by
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨_, (key m).2 hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨Equiv.swap k.castSucc k.succ m, ?_, ?_⟩
      · have := key (Equiv.swap k.castSucc k.succ m)
        rw [Equiv.swap_apply_self] at this; exact this.1 hm
      · simp [swapEmb]
  simp only [pathOf]
  simp only [e1, hr]


lemma range_swapEmb {K i : ℕ} (k : Fin i) (σ : Fin (i + 1) ↪ Fin K) :
    Set.range (swapEmb k σ) = Set.range σ := by
  show Set.range (σ ∘ Equiv.swap k.castSucc k.succ) = _
  rw [EquivLike.range_comp]

lemma interior_sum {K i : ℕ} (A : (Fin (i + 1) → V K) → Prop) (b : V K) (T : Set (Fin K))
    (k : Fin i) :
    ∑ σ : Fin (i + 1) ↪ Fin K, (if Set.range σ = T then
      (if A (pathOf b σ ∘ (k.castSucc.succ).succAbove) then 1 else 0) else 0 : ZMod 2) = 0 := by
  have hf : ∀ σ : Fin (i + 1) ↪ Fin K,
      pathOf b (swapEmb k σ) ∘ (k.castSucc.succ).succAbove = pathOf b σ ∘ (k.castSucc.succ).succAbove := by
    intro σ; funext j
    apply pathOf_swapEmb
    intro h
    apply Fin.succAbove_ne (k.castSucc.succ) j
    ext; simp [h]
  refine Finset.sum_involution (fun σ _ => swapEmb k σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro σ _
    simp only [range_swapEmb, hf]
    exact CharTwo.add_self_eq_zero _
  · intro σ _ _ h
    have := congrArg (fun f => f k.castSucc) h
    simp only [swapEmb, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Equiv.swap_apply_left] at this
    exact Fin.castSucc_lt_succ.ne (σ.injective this).symm
  · intro σ _
    ext x; simp [swapEmb]

lemma range_succ_eq {K i : ℕ} (σ : Fin (i + 1) ↪ Fin K) :
    Set.range σ = insert (σ 0) (Set.range ((Fin.succEmb i).trans σ)) := by
  conv_lhs => rw [← Fin.cons_self_tail (σ : Fin (i+1) → Fin K)]
  rw [Fin.range_cons]; rfl

lemma range_castSucc_eq {K i : ℕ} (σ : Fin (i + 1) ↪ Fin K) :
    Set.range σ = insert (σ (Fin.last i)) (Set.range (Fin.castSuccEmb.trans σ)) := by
  conv_lhs => rw [← Fin.snoc_init_self (σ : Fin (i+1) → Fin K)]
  rw [Fin.range_snoc]; rfl

lemma first_sum {K i : ℕ} (G : Fin K → (Fin i ↪ Fin K) → ZMod 2) (T : Finset (Fin K)) :
    ∑ σ : Fin (i + 1) ↪ Fin K, (if Set.range σ = (T : Set (Fin K)) then
      G (σ 0) ((Fin.succEmb i).trans σ) else 0) =
    ∑ c ∈ T, ∑ τ : Fin i ↪ Fin K, (if Set.range τ = ((T.erase c : Finset (Fin K)) : Set (Fin K))
      then G c τ else 0) := by
  rw [← Finset.sum_filter]
  simp_rw [← Finset.sum_filter]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun σ _ => ⟨σ 0, (Fin.succEmb i).trans σ⟩)
    (fun x hx => ⟨Fin.cons x.1 x.2, Fin.cons_injective_of_injective ?_ x.2.injective⟩)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [hx.2]; simp
  · intro σ hσ
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    have hr := range_succ_eq σ
    have hn : σ 0 ∉ Set.range ((Fin.succEmb i).trans σ) := by
      rintro ⟨k, hk⟩
      exact Fin.succ_ne_zero k (σ.injective hk)
    refine ⟨?_, ?_⟩
    · rw [← Finset.mem_coe, ← hσ]; exact ⟨0, rfl⟩
    · rw [Finset.coe_erase, ← hσ, hr, Set.insert_sdiff_self_of_notMem hn]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    simp only [Function.Embedding.coeFn_mk, Fin.range_cons, hx.2, Finset.coe_erase]
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem (by simpa using hx.1)]
  · intro σ _
    ext x
    cases x using Fin.cases <;> simp
  · intro x _
    refine Sigma.ext (by simp) (heq_of_eq ?_)
    ext y; simp

lemma last_sum {K i : ℕ} (G : Fin K → (Fin i ↪ Fin K) → ZMod 2) (T : Finset (Fin K)) :
    ∑ σ : Fin (i + 1) ↪ Fin K, (if Set.range σ = (T : Set (Fin K)) then
      G (σ (Fin.last i)) (Fin.castSuccEmb.trans σ) else 0) =
    ∑ c ∈ T, ∑ τ : Fin i ↪ Fin K, (if Set.range τ = ((T.erase c : Finset (Fin K)) : Set (Fin K))
      then G c τ else 0) := by
  rw [← Finset.sum_filter]
  simp_rw [← Finset.sum_filter]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun σ _ => ⟨σ (Fin.last i), Fin.castSuccEmb.trans σ⟩)
    (fun x hx => ⟨Fin.snoc x.2 x.1, Fin.snoc_injective_of_injective x.2.injective ?_⟩)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [hx.2]; simp
  · intro σ hσ
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    have hr := range_castSucc_eq σ
    have hn : σ (Fin.last i) ∉ Set.range (Fin.castSuccEmb.trans σ) := by
      rintro ⟨k, hk⟩
      exact Fin.castSucc_ne_last k (σ.injective hk)
    refine ⟨?_, ?_⟩
    · rw [← Finset.mem_coe, ← hσ]; exact ⟨_, rfl⟩
    · rw [Finset.coe_erase, ← hσ, hr, Set.insert_sdiff_self_of_notMem hn]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    simp only [Function.Embedding.coeFn_mk, Fin.range_snoc, hx.2, Finset.coe_erase]
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem (by simpa using hx.1)]
  · intro σ _
    ext x
    cases x using Fin.lastCases <;> simp
  · intro x _
    refine Sigma.ext (by simp) (heq_of_eq ?_)
    ext y; simp


/-- **C-a (Proposition 3.1, summed over a face).** Deleting an interior vertex of a monotone path
cancels in pairs; deleting the first (resp. last) vertex gives a monotone path of the facet with the
first (resp. last) flipped coordinate fixed to `true` (resp. `false`). Valid for any predicate `A`. -/
theorem path_sum {K i : ℕ} (A : (Fin (i + 1) → V K) → Prop) (b : V K) (T : Finset (Fin K))
    (hT : T.card = i + 1) :
    (∑ σ : Fin (i + 1) ↪ Fin K, if Set.range σ = (T : Set (Fin K)) then
        ((univ.filter fun s : Fin (i + 2) => A (pathOf b σ ∘ s.succAbove)).card : ZMod 2) else 0) =
      ∑ c ∈ T, ∑ τ : Fin i ↪ Fin K, if Set.range τ = ((T.erase c : Finset (Fin K)) : Set (Fin K))
        then ((if A (pathOf (Function.update b c true) τ) then 1 else 0) +
              (if A (pathOf (Function.update b c false) τ) then 1 else 0) : ZMod 2) else 0 := by
  have hsplit : ∀ σ : Fin (i + 1) ↪ Fin K,
      ((univ.filter fun s : Fin (i + 2) => A (pathOf b σ ∘ s.succAbove)).card : ZMod 2) =
        (if A (pathOf (Function.update b (σ 0) true) ((Fin.succEmb i).trans σ)) then 1 else 0) +
        (if A (pathOf (Function.update b (σ (Fin.last i)) false) (Fin.castSuccEmb.trans σ))
          then 1 else 0) +
        ∑ k : Fin i, (if A (pathOf b σ ∘ (k.castSucc.succ).succAbove) then 1 else 0) := by
    intro σ
    rw [Finset.natCast_card_filter, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    have h0 : pathOf b σ ∘ (0 : Fin (i + 2)).succAbove =
        pathOf (Function.update b (σ 0) true) ((Fin.succEmb i).trans σ) := by
      funext j; exact pathOf_succ b σ j
    have hl : pathOf b σ ∘ ((Fin.last i).succ).succAbove =
        pathOf (Function.update b (σ (Fin.last i)) false) (Fin.castSuccEmb.trans σ) := by
      funext j; rw [Fin.succ_last, Fin.succAbove_last]; exact pathOf_castSucc b σ j
    rw [h0, hl]; ring
  have hL : ∀ σ : Fin (i + 1) ↪ Fin K,
      (if Set.range σ = (T : Set (Fin K)) then
        ((univ.filter fun s : Fin (i + 2) => A (pathOf b σ ∘ s.succAbove)).card : ZMod 2) else 0) =
      (if Set.range σ = (T : Set (Fin K)) then
        (if A (pathOf (Function.update b (σ 0) true) ((Fin.succEmb i).trans σ)) then 1 else 0)
        else 0) +
      (if Set.range σ = (T : Set (Fin K)) then
        (if A (pathOf (Function.update b (σ (Fin.last i)) false) (Fin.castSuccEmb.trans σ))
          then 1 else 0) else 0) +
      ∑ k : Fin i, (if Set.range σ = (T : Set (Fin K)) then
        (if A (pathOf b σ ∘ (k.castSucc.succ).succAbove) then 1 else 0) else 0) := by
    intro σ
    by_cases h : Set.range σ = (T : Set (Fin K))
    · simp only [if_pos h]; exact hsplit σ
    · simp only [if_neg h, Finset.sum_const_zero, add_zero]
  simp_rw [hL, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := (univ : Finset (Fin (i + 1) ↪ Fin K)))]
  simp_rw [interior_sum, Finset.sum_const_zero, add_zero]
  rw [first_sum (fun c τ => if A (pathOf (Function.update b c true) τ) then 1 else 0) T,
    last_sum (fun c τ => if A (pathOf (Function.update b c false) τ) then 1 else 0) T,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  split_ifs <;> simp

theorem facet_count_key {α : Type*} [LinearOrder α] (d : α → Prop) (R : Finset α) :
    ((R.filter fun c => ∀ e ∈ R, (e < c → ¬ d e) ∧ (c < e → d e)).card : ZMod 2) =
      (if ∀ e ∈ R, ¬ d e then 1 else 0) + (if ∀ e ∈ R, d e then 1 else 0) := by
  induction R using Finset.induction_on_min with
  | empty => simp; decide
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hA : (∀ e ∈ insert a s, (e < a → ¬ d e) ∧ (a < e → d e)) ↔ ∀ e ∈ s, d e := by
      constructor
      · intro h e he
        exact (h e (mem_insert_of_mem he)).2 (ha e he)
      · intro h e he
        rcases mem_insert.1 he with rfl | he
        · simp
        · exact ⟨fun h' => absurd (ha e he) (not_lt.2 h'.le), fun _ => h e he⟩
    have hS : (s.filter fun c => ∀ e ∈ insert a s, (e < c → ¬ d e) ∧ (c < e → d e)) =
        if d a then ∅ else s.filter fun c => ∀ e ∈ s, (e < c → ¬ d e) ∧ (c < e → d e) := by
      split_ifs with hda
      · ext c
        simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hc h
        exact (h a (mem_insert_self a s)).1 (ha c hc) hda
      · apply filter_congr
        intro c hc
        constructor
        · intro h e he; exact h e (mem_insert_of_mem he)
        · intro h e he
          rcases mem_insert.1 he with rfl | he
          · exact ⟨fun _ => hda, fun h' => absurd (ha c hc) (not_lt.2 h'.le)⟩
          · exact h e he
    rw [filter_insert, hS]
    have hcard : ((if (∀ e ∈ insert a s, (e < a → ¬ d e) ∧ (a < e → d e)) then
        insert a (if d a then ∅ else s.filter fun c => ∀ e ∈ s, (e < c → ¬ d e) ∧ (c < e → d e))
        else (if d a then ∅ else s.filter fun c => ∀ e ∈ s, (e < c → ¬ d e) ∧ (c < e → d e))).card
          : ZMod 2) = (if ∀ e ∈ s, d e then 1 else 0) +
            (if d a then 0 else ((s.filter fun c => ∀ e ∈ s, (e < c → ¬ d e) ∧ (c < e → d e)).card : ZMod 2)) := by
      simp only [hA]
      split_ifs <;> simp_all [card_insert_of_notMem]
      all_goals ring
    rw [hcard, ih]
    simp only [forall_mem_insert]
    split_ifs <;> first | decide | (exfalso; simp_all)

theorem altBase_insert {K : ℕ} (T : Finset (Fin K)) (c e : Fin K) (hcT : c ∉ T) (heT : e ∉ T)
    (hec : e ≠ c) :
    altBase (insert c T) e = if c < e then !altBase T e else altBase T e := by
  have he' : e ∉ insert c T := by simp [heT, hec]
  simp only [altBase, he', heT, if_false, compl_insert, filter_erase]
  split_ifs with hce
  · have hm : c ∈ Tᶜ.filter (· < e) := by
      simp only [mem_filter, mem_compl]
      exact ⟨hcT, hce⟩
    rw [card_erase_of_mem hm]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (card_ne_zero_of_mem hm)
    rw [hk]
    simp only [Nat.succ_sub_one, Nat.odd_add_one, ← Nat.not_even_iff_odd, decide_not, Bool.not_not, Nat.succ_eq_add_one]
  · rw [erase_eq_of_notMem]
    simp [hce]

/-- **C-b (Lemma 3.2).** A face with free set `T` (`|T| = i`, `i + 2 ≤ K`) and fixed bits `g` is a
facet of an odd number of alternating `(i+1)`-faces iff it or its antipode is alternating. -/
theorem facet_count {K i : ℕ} (T : Finset (Fin K)) (hT : T.card = i) (hK : i + 2 ≤ K) (g : V K) :
    (((Tᶜ).filter fun c => ∀ e, e ∉ insert c T → g e = altBase (insert c T) e).card : ZMod 2) =
      if (∀ e, e ∉ T → g e = altBase T e) ∨ (∀ e, e ∉ T → g e = !altBase T e) then 1 else 0 := by
  have hne : (Tᶜ).Nonempty := by
    rw [← card_pos, card_compl, Fintype.card_fin]; omega
  have hfilt : ((Tᶜ).filter fun c => ∀ e, e ∉ insert c T → g e = altBase (insert c T) e) =
      (Tᶜ).filter fun c => ∀ e ∈ Tᶜ, (e < c → ¬ g e ≠ altBase T e) ∧ (c < e → g e ≠ altBase T e) := by
    apply filter_congr
    intro c hc
    rw [mem_compl] at hc
    constructor
    · intro h e he
      rw [mem_compl] at he
      refine ⟨fun hec => ?_, fun hce => ?_⟩
      · have := h e (by simp [he, hec.ne])
        rw [altBase_insert T c e hc he hec.ne, if_neg (not_lt.2 hec.le)] at this
        exact not_not.2 this
      · have := h e (by simp [he, hce.ne'])
        rw [altBase_insert T c e hc he hce.ne', if_pos hce] at this
        rw [this]; cases altBase T e <;> simp
    · intro h e he
      simp only [mem_insert, not_or] at he
      rcases lt_or_gt_of_ne he.1 with hec | hce
      · rw [altBase_insert T c e hc he.2 he.1, if_neg (not_lt.2 hec.le)]
        exact not_not.1 ((h e (mem_compl.2 he.2)).1 hec)
      · rw [altBase_insert T c e hc he.2 he.1, if_pos hce]
        have := (h e (mem_compl.2 he.2)).2 hce
        revert this; cases g e <;> cases altBase T e <;> simp
  rw [hfilt]
  have hk := facet_count_key (fun e => g e ≠ altBase T e) Tᶜ
  refine Eq.trans (b := (if ∀ e ∈ Tᶜ, ¬ g e ≠ altBase T e then (1 : ZMod 2) else 0) +
    (if ∀ e ∈ Tᶜ, g e ≠ altBase T e then 1 else 0)) ?_ ?_
  · convert hk
  have hA : (∀ e, e ∉ T → g e = altBase T e) ↔ ∀ e ∈ Tᶜ, ¬ g e ≠ altBase T e := by
    simp [mem_compl]
  have hB : (∀ e, e ∉ T → g e = !altBase T e) ↔ ∀ e ∈ Tᶜ, g e ≠ altBase T e := by
    refine forall_congr' fun e => ?_
    rw [mem_compl]
    refine imp_congr_right fun _ => ?_
    cases g e <;> cases altBase T e <;> simp
  obtain ⟨x, hx⟩ := hne
  by_cases h1 : ∀ e ∈ Tᶜ, ¬ g e ≠ altBase T e
  · have h2 : ¬ ∀ e ∈ Tᶜ, g e ≠ altBase T e := fun h => h1 x hx (h x hx)
    rw [if_pos h1, if_neg h2, if_pos (Or.inl (hA.2 h1))]; simp
  · rw [if_neg h1]
    by_cases h2 : ∀ e ∈ Tᶜ, g e ≠ altBase T e
    · rw [if_pos h2, if_pos (Or.inr (hB.2 h2))]; simp
    · rw [if_neg h2, if_neg (by rw [hA, hB]; tauto)]; simp

/-! ## Helpers for `comb` -/

theorem isWalk_pathOf {K i : ℕ} (b : V K) (σ : Fin i ↪ Fin K) : IsWalk (pathOf b σ) := by
  intro j hj
  refine ⟨σ ⟨j, by omega⟩, ?_⟩
  funext c
  by_cases hc : c = σ ⟨j, by omega⟩
  · subst hc
    simp only [flip, Function.update_self, pathOf]
    have h1 : ∃ k : Fin i, k.val < j + 1 ∧ σ k = σ ⟨j, by omega⟩ := ⟨⟨j, by omega⟩, by simp, rfl⟩
    have h2 : ¬ ∃ k : Fin i, k.val < j ∧ σ k = σ ⟨j, by omega⟩ := by
      rintro ⟨k, hk, hk'⟩
      have := σ.injective hk'
      rw [Fin.ext_iff] at this; simp at this; omega
    rw [if_pos h1, if_neg h2]; simp
  · simp only [flip, Function.update_of_ne hc, pathOf]
    have : (∃ k : Fin i, k.val < j + 1 ∧ σ k = c) ↔ (∃ k : Fin i, k.val < j ∧ σ k = c) := by
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨k, ?_, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
        · exact h
        · exact absurd (congrArg σ (Fin.ext h)) hc
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩
    simp only [this]

/-- `τ` reversed. -/
def revEmb {K i : ℕ} (τ : Fin i ↪ Fin K) : Fin i ↪ Fin K := Fin.revPerm.toEmbedding.trans τ

@[simp] lemma revEmb_apply {K i : ℕ} (τ : Fin i ↪ Fin K) (k : Fin i) : revEmb τ k = τ k.rev := rfl

lemma revEmb_revEmb {K i : ℕ} (τ : Fin i ↪ Fin K) : revEmb (revEmb τ) = τ := by
  ext k; simp

lemma range_revEmb {K i : ℕ} (τ : Fin i ↪ Fin K) : Set.range (revEmb τ) = Set.range τ := by
  ext c; constructor
  · rintro ⟨k, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨k.rev, by simp⟩

lemma map_revEmb {K i : ℕ} (τ : Fin i ↪ Fin K) : univ.map (revEmb τ) = univ.map τ := by
  apply Finset.coe_injective; simp [range_revEmb]

/-- The antipodal fixed-bit pattern (normalised to `false` on `U`). -/
def gstar {K : ℕ} (U : Finset (Fin K)) : V K := fun e => if e ∈ U then false else !altBase U e

lemma pathOf_gstar {K i : ℕ} (τ : Fin i ↪ Fin K) :
    pathOf (gstar (univ.map τ)) τ =
      fun j => anti (pathOf (altBase (univ.map τ)) (revEmb τ) j.rev) := by
  funext j c
  simp only [pathOf, anti, range_revEmb, revEmb_apply]
  by_cases hc : c ∈ Set.range τ
  · obtain ⟨m, rfl⟩ := hc
    have e1 : (∃ k : Fin i, k.val < j.val ∧ τ k = τ m) ↔ m.val < j.val := by
      constructor
      · rintro ⟨k, hk, h⟩; rw [τ.injective h] at hk; exact hk
      · intro h; exact ⟨m, h, rfl⟩
    have e2 : (∃ k : Fin i, k.val < j.rev.val ∧ τ k.rev = τ m) ↔ ¬ m.val < j.val := by
      constructor
      · rintro ⟨k, hk, h⟩
        have := τ.injective h; subst this
        simp [Fin.val_rev] at hk ⊢; omega
      · intro h; refine ⟨m.rev, ?_, by simp⟩
        simp [Fin.val_rev] at h ⊢; omega
    simp only [e1, e2]
    by_cases h : m.val < j.val <;> simp [h]
  · have e1 : ¬ ∃ k : Fin i, k.val < j.val ∧ τ k = c := fun ⟨k, _, h⟩ => hc ⟨k, h⟩
    have e2 : ¬ ∃ k : Fin i, k.val < j.rev.val ∧ τ k.rev = c := fun ⟨k, _, h⟩ => hc ⟨_, h⟩
    have hU : c ∉ univ.map τ := by simpa using hc
    simp only [e1, e2, if_false]
    simp [hc, gstar, hU]

lemma altBase_of_mem {K : ℕ} {T : Finset (Fin K)} {e : Fin K} (h : e ∈ T) : altBase T e = false := by
  simp [altBase, h]

lemma fiber_card {K : ℕ} (U : Finset (Fin K)) (g : V K) (hg : ∀ e ∈ U, g e = false) :
    ((Uᶜ ×ˢ (univ : Finset Bool)).filter
        (fun x => Function.update (altBase (insert x.1 U)) x.1 x.2 = g)).card =
      ((Uᶜ).filter fun c => ∀ e, e ∉ insert c U → g e = altBase (insert c U) e).card := by
  apply Finset.card_nbij' (fun x => x.1) (fun c => (c, g c))
  · rintro ⟨c, v⟩ hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_univ,
      and_true] at hx ⊢
    obtain ⟨hc, rfl⟩ := hx
    refine ⟨hc, fun e he => ?_⟩
    have : e ≠ c := fun h => he (h ▸ Finset.mem_insert_self _ _)
    rw [Function.update_of_ne this]
  · intro c hc
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_univ,
      and_true] at hc ⊢
    refine ⟨hc.1, ?_⟩
    funext e
    by_cases hec : e = c
    · subst hec; simp
    · rw [Function.update_of_ne hec]
      by_cases heU : e ∈ U
      · rw [hg e heU, altBase_of_mem (Finset.mem_insert_of_mem heU)]
      · exact (hc.2 e (by simp [hec, heU])).symm
  · rintro ⟨c, v⟩ hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx
    have := congrFun hx.2 c
    simp at this
    simp [this]
  · intro c _; rfl

lemma fiber_sum {K i : ℕ} (U : Finset (Fin K)) (hU : U.card = i) (hK : i + 2 ≤ K)
    (F : V K → ZMod 2) :
    ∑ c ∈ Uᶜ, (F (Function.update (altBase (insert c U)) c true) +
        F (Function.update (altBase (insert c U)) c false)) = F (altBase U) + F (gstar U) := by
  set φ : Fin K × Bool → V K := fun x => Function.update (altBase (insert x.1 U)) x.1 x.2
  set N : Finset (V K) := univ.filter (fun g : V K => ∀ e ∈ U, g e = false)
  have h1 : ∑ c ∈ Uᶜ, (F (Function.update (altBase (insert c U)) c true) +
        F (Function.update (altBase (insert c U)) c false)) =
      ∑ x ∈ Uᶜ ×ˢ (univ : Finset Bool), F (φ x) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fintype.sum_bool]
  have hmaps : ∀ x ∈ Uᶜ ×ˢ (univ : Finset Bool), φ x ∈ N := by
    rintro ⟨c, v⟩ hx
    simp only [Finset.mem_product, Finset.mem_compl] at hx
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and, φ]
    intro e he
    have : e ≠ c := fun h => hx.1 (h ▸ he)
    rw [Function.update_of_ne this, altBase_of_mem (Finset.mem_insert_of_mem he)]
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
  have h2 : ∀ g ∈ N, ∑ x ∈ (Uᶜ ×ˢ (univ : Finset Bool)).filter (fun x => φ x = g), F (φ x) =
      if (∀ e, e ∉ U → g e = altBase U e) ∨ (∀ e, e ∉ U → g e = !altBase U e) then F g else 0 := by
    intro g hg
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul]
    simp only [φ]
    rw [fiber_card U g hg, facet_count U hU hK g]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
  have hne : altBase U ≠ gstar U := by
    have : Uᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
      intro h; have := congrArg Finset.card h; simp at this; omega
    obtain ⟨e, he⟩ := this
    rw [Finset.mem_compl] at he
    intro h; have := congrFun h e; simp [gstar, he] at this
  have h3 : N.filter (fun g => (∀ e, e ∉ U → g e = altBase U e) ∨
      (∀ e, e ∉ U → g e = !altBase U e)) = {altBase U, gstar U} := by
    ext g
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hg, h | h⟩
      · left; funext e; by_cases he : e ∈ U
        · rw [hg e he, altBase_of_mem he]
        · exact h e he
      · right; funext e; by_cases he : e ∈ U
        · simp [hg e he, gstar, he]
        · simp [h e he, gstar, he]
    · rintro (rfl | rfl)
      · exact ⟨fun e he => altBase_of_mem he, Or.inl fun _ _ => rfl⟩
      · exact ⟨fun e he => by simp [gstar, he], Or.inr fun e he => by simp [gstar, he]⟩
  rw [h3, Finset.sum_pair hne]

lemma range_eq_iff {K n : ℕ} (σ : Fin n ↪ Fin K) (T : Finset (Fin K)) :
    Set.range σ = (T : Set (Fin K)) ↔ univ.map σ = T := by
  rw [← Finset.coe_inj]; simp

lemma mem_erase_iff' {K : ℕ} (T U : Finset (Fin K)) (c : Fin K) :
    (c ∈ T ∧ U = T.erase c) ↔ (c ∉ U ∧ T = insert c U) := by
  constructor
  · rintro ⟨hc, rfl⟩; exact ⟨Finset.notMem_erase _ _, (Finset.insert_erase hc).symm⟩
  · rintro ⟨hc, rfl⟩; exact ⟨Finset.mem_insert_self _ _, (Finset.erase_insert hc).symm⟩

lemma ind_xor {P Q R : Prop} (h : R ↔ (P ↔ ¬ Q)) :
    (if R then 1 else 0 : ZMod 2) = (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp_all; decide

/-- Regrouping a sum over embeddings by their range, followed by `path_sum`. -/
lemma regroup {K i : ℕ} (A : (Fin (i + 1) → V K) → Prop) :
    (∑ σ : Fin (i + 1) ↪ Fin K,
      ((univ.filter fun s : Fin (i + 2) =>
        A (pathOf (altBase (univ.map σ)) σ ∘ s.succAbove)).card : ZMod 2)) =
    ∑ T : Finset (Fin K), ∑ c ∈ T, ∑ τ : Fin i ↪ Fin K,
      if Set.range τ = ((T.erase c : Finset (Fin K)) : Set (Fin K))
        then ((if A (pathOf (Function.update (altBase T) c true) τ) then 1 else 0) +
              (if A (pathOf (Function.update (altBase T) c false) τ) then 1 else 0) : ZMod 2)
        else 0 := by
  have h1 : (∑ σ : Fin (i + 1) ↪ Fin K,
      ((univ.filter fun s : Fin (i + 2) =>
        A (pathOf (altBase (univ.map σ)) σ ∘ s.succAbove)).card : ZMod 2)) =
      ∑ T : Finset (Fin K), ∑ σ : Fin (i + 1) ↪ Fin K, if Set.range σ = (T : Set (Fin K)) then
        ((univ.filter fun s : Fin (i + 2) => A (pathOf (altBase T) σ ∘ s.succAbove)).card : ZMod 2)
        else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [range_eq_iff]
    rw [Finset.sum_ite_eq]; simp
  rw [h1]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : T.card = i + 1
  · exact path_sum A (altBase T) T hT
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro c hc
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [if_neg]
      intro h
      rw [range_eq_iff] at h
      have h2 := congrArg Finset.card h
      rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, Finset.card_erase_of_mem hc] at h2
      have : 0 < T.card := Finset.card_pos.mpr ⟨c, hc⟩
      omega
    · intro σ _
      rw [if_neg]
      intro h
      rw [range_eq_iff] at h
      apply hT; rw [← h]; simp

/-- Swapping to a sum over `τ` and reindexing `(T, c) ↦ (insert c U, c)`. -/
lemma reindex {K i : ℕ} (h : Finset (Fin K) → Fin K → (Fin i ↪ Fin K) → ZMod 2) :
    ∑ T : Finset (Fin K), ∑ c ∈ T, ∑ τ : Fin i ↪ Fin K,
      (if Set.range τ = ((T.erase c : Finset (Fin K)) : Set (Fin K)) then h T c τ else 0) =
    ∑ τ : Fin i ↪ Fin K, ∑ c ∈ (univ.map τ)ᶜ, h (insert c (univ.map τ)) c τ := by
  have e1 : ∀ T : Finset (Fin K), ∑ c ∈ T, ∑ τ : Fin i ↪ Fin K,
      (if Set.range τ = ((T.erase c : Finset (Fin K)) : Set (Fin K)) then h T c τ else 0) =
      ∑ τ : Fin i ↪ Fin K, ∑ c : Fin K,
      (if c ∈ T ∧ univ.map τ = T.erase c then h T c τ else 0) := by
    intro T
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ T)]
    rw [Finset.sum_eq_zero (s := univ.filter (fun c => c ∉ T)) (fun c hc => by
      rw [if_neg]; rintro ⟨h1, _⟩; exact (Finset.mem_filter.mp hc).2 h1)]
    rw [add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [range_eq_iff, hc, true_and]
  rw [Finset.sum_congr rfl fun T _ => e1 T, Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm]
  rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ (univ.map τ)ᶜ)]
  rw [Finset.sum_eq_zero (s := univ.filter (fun c => c ∉ (univ.map τ)ᶜ)), add_zero]
  · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_compl] at hc
    simp only [and_comm (a := c ∈ _), eq_comm (a := univ.map τ)]
    have : ∀ T : Finset (Fin K), (T.erase c = univ.map τ ∧ c ∈ T) ↔ T = insert c (univ.map τ) := by
      intro T
      rw [and_comm, eq_comm, mem_erase_iff']; simp [hc]
    simp only [this]
    rw [Finset.sum_ite_eq']; simp
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_compl, not_not, Finset.mem_univ, true_and] at hc
    refine Finset.sum_eq_zero fun T _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact ((mem_erase_iff' T _ c).mp ⟨h1, h2⟩).1 hc

lemma c_step {K : ℕ} (A B : (i : ℕ) → (Fin (i + 1) → V K) → Prop)
    (C1 : ∀ i, i < K - 1 → ∀ x : Fin (i + 1) → V K, IsWalk x →
      (B i x ↔ (A i x ↔ ¬ A i (fun j => anti (x j.rev)))))
    (C2 : ∀ i, i < K - 1 → ∀ x : Fin (i + 2) → V K, IsWalk x →
      ((univ.filter fun s : Fin (i + 2) => A i (x ∘ s.succAbove)).card : ZMod 2) =
        if B (i + 1) x then 1 else 0)
    (i : ℕ) (hi : i < K - 1) :
    (∑ σ : Fin (i + 1) ↪ Fin K,
      (if B (i + 1) (pathOf (altBase (univ.map σ)) σ) then 1 else 0 : ZMod 2)) =
    ∑ τ : Fin i ↪ Fin K, (if B i (pathOf (altBase (univ.map τ)) τ) then 1 else 0 : ZMod 2) := by
  have hK : i + 2 ≤ K := by omega
  have s1 : (∑ σ : Fin (i + 1) ↪ Fin K,
      (if B (i + 1) (pathOf (altBase (univ.map σ)) σ) then 1 else 0 : ZMod 2)) =
      ∑ σ : Fin (i + 1) ↪ Fin K,
      ((univ.filter fun s : Fin (i + 2) =>
        A i (pathOf (altBase (univ.map σ)) σ ∘ s.succAbove)).card : ZMod 2) :=
    Finset.sum_congr rfl fun σ _ => (C2 i hi _ (isWalk_pathOf _ σ)).symm
  rw [s1, regroup (A i), reindex (i := i) (fun T c τ =>
    ((if A i (pathOf (Function.update (altBase T) c true) τ) then 1 else 0) +
     (if A i (pathOf (Function.update (altBase T) c false) τ) then 1 else 0) : ZMod 2))]
  have s2 : ∀ τ : Fin i ↪ Fin K, ∑ c ∈ (univ.map τ)ᶜ,
      ((if A i (pathOf (Function.update (altBase (insert c (univ.map τ))) c true) τ) then 1 else 0) +
       (if A i (pathOf (Function.update (altBase (insert c (univ.map τ))) c false) τ) then 1 else 0)
        : ZMod 2) =
      (if A i (pathOf (altBase (univ.map τ)) τ) then 1 else 0) +
      (if A i (fun j => anti (pathOf (altBase (univ.map (revEmb τ))) (revEmb τ) j.rev))
        then 1 else 0) := by
    intro τ
    rw [fiber_sum (univ.map τ) (by simp) hK (fun g => if A i (pathOf g τ) then 1 else 0)]
    simp only [pathOf_gstar, map_revEmb]
  rw [Finset.sum_congr rfl fun τ _ => s2 τ, Finset.sum_add_distrib]
  have hinv : Function.Involutive (revEmb : (Fin i ↪ Fin K) → (Fin i ↪ Fin K)) := revEmb_revEmb
  rw [Fintype.sum_bijective _ hinv.bijective
    (fun τ => (if A i (fun j => anti (pathOf (altBase (univ.map (revEmb τ))) (revEmb τ) j.rev))
        then 1 else 0 : ZMod 2))
    (fun τ => (if A i (fun j => anti (pathOf (altBase (univ.map τ)) τ j.rev)) then 1 else 0))
    (fun _ => rfl), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact (ind_xor (C1 i hi _ (isWalk_pathOf _ τ))).symm

-- HELPERS_END

/-- **C-c (assembly).** Abstract parity argument: predicates `A i`, `B i` on vertex tuples
satisfying the four axioms below are impossible. (`B i` is the hull meets `H_i \ {0}`, `A i` is
the hull meets `H_i⁺`.) -/
theorem comb {K : ℕ} (hK : 2 ≤ K) (A B : (i : ℕ) → (Fin (i + 1) → V K) → Prop)
    (C1 : ∀ i, i < K - 1 → ∀ x : Fin (i + 1) → V K, IsWalk x →
      (B i x ↔ (A i x ↔ ¬ A i (fun j => anti (x j.rev)))))
    (C2 : ∀ i, i < K - 1 → ∀ x : Fin (i + 2) → V K, IsWalk x →
      ((univ.filter fun s : Fin (i + 2) => A i (x ∘ s.succAbove)).card : ZMod 2) =
        if B (i + 1) x then 1 else 0)
    (C3 : ∀ x : Fin 1 → V K, B 0 x)
    (C4 : ∀ x : Fin (K - 1 + 1) → V K, ¬ B (K - 1) x) : False := by
  have h0 : (∑ σ : Fin 0 ↪ Fin K,
      (if B 0 (pathOf (altBase (univ.map σ)) σ) then 1 else 0 : ZMod 2)) = 1 := by
    rw [Finset.sum_congr rfl fun σ _ => if_pos (C3 _)]
    simp [Finset.sum_const]
  have hall : ∀ n, n ≤ K - 1 → (∑ σ : Fin n ↪ Fin K,
      (if B n (pathOf (altBase (univ.map σ)) σ) then 1 else 0 : ZMod 2)) = 1 := by
    intro n
    induction n with
    | zero => intro _; exact h0
    | succ n ih =>
      intro hn
      rw [c_step A B C1 C2 n (by omega)]
      exact ih (by omega)
  have h1 := hall (K - 1) le_rfl
  rw [Finset.sum_eq_zero fun σ _ => if_neg (C4 _)] at h1
  exact zero_ne_one h1


/-! ## Glue: the core lemma from the blueprint -/

lemma glue_vec_ne_zero {K : ℕ} {p : Fin K × Fin K} (h : p.1 ≠ p.2) : vec p ≠ 0 := by
  intro h0
  have := congrFun h0 p.1
  simp [vec, h] at this

lemma glue_S_comp_rev {K i : ℕ} (f : Fin (i + 1) → Fin K × Fin K) : S (fun j => f j.rev) = S f := by
  ext w; constructor
  · rintro ⟨j, rfl⟩; exact ⟨j.rev, rfl⟩
  · rintro ⟨j, rfl⟩; exact ⟨j.rev, by simp⟩

theorem core' (K : ℕ) (hK : 2 ≤ K) (q : V K → Fin K × Fin K)
    (h1 : ∀ x, (q x).1 ≠ (q x).2) (h2 : ∀ x, q (anti x) = (q x).swap)
    (h3 : ∀ x c, (q x).1 = (q (flip x c)).1 ∨ (q x).2 = (q (flip x c)).2) : False := by
  obtain ⟨ℓ, hℓ⟩ := exists_generic K
  have walk_cons : ∀ {n} (x : Fin n → V K), IsWalk x → ConsecShare (q ∘ x) := by
    intro n x hx j h
    obtain ⟨c, hc⟩ := hx j h
    simp only [Function.comp, hc]
    exact h3 _ c
  refine comb hK (fun i x => Alpha ℓ i (S (q ∘ x))) (fun i x => Beta ℓ i (S (q ∘ x)))
    ?_ ?_ ?_ ?_
  · intro i hi x _
    obtain ⟨hnot, hiff⟩ := sign_split hℓ hi (q ∘ x) (fun j => h1 _)
    have hsw : S (q ∘ fun j : Fin (i + 1) => anti (x j.rev)) = S (Prod.swap ∘ q ∘ x) := by
      have : (q ∘ fun j : Fin (i + 1) => anti (x j.rev)) =
          fun j : Fin (i + 1) => (Prod.swap ∘ q ∘ x) j.rev := by
        funext j; simp [h2]
      rw [this, glue_S_comp_rev]
    simp only [hsw]
    tauto
  · intro i hi x hx
    exact local_parity hℓ hi (q ∘ x) (fun j => h1 _) (walk_cons x hx)
  · intro x
    refine ⟨vec (q (x 0)), subset_convexHull ℝ _ ⟨0, rfl⟩, fun a ha => absurd ha (Nat.not_lt_zero a),
      glue_vec_ne_zero (h1 _)⟩
  · intro x
    exact top_trivial hℓ hK (q ∘ x) (fun j => h1 _)

end NorineB

namespace Norine

/-- Vertices of the `n`-cube. -/
abbrev V (n : ℕ) := Fin n → Bool

/-- The hypercube graph `Q_n`: adjacent iff the vertices differ in exactly one coordinate. -/
def cube (n : ℕ) : SimpleGraph (V n) :=
  SimpleGraph.fromRel fun x y => hammingDist x y = 1

/-- The antipode: flip every bit. -/
def anti {n : ℕ} (x : V n) : V n := fun i => !x i

@[simp] lemma anti_anti {n : ℕ} (x : V n) : anti (anti x) = x := by
  funext i; simp [anti]

/-- An edge colouring (`true` = red) is antipodal if antipodal edges get opposite colours. -/
def IsAntipodal {n : ℕ} (c : Sym2 (V n) → Bool) : Prop :=
  ∀ x y, (cube n).Adj x y → c s(anti x, anti y) = !c s(x, y)

/-- The red spanning subgraph. -/
def red {n : ℕ} (c : Sym2 (V n) → Bool) : SimpleGraph (V n) :=
  SimpleGraph.fromRel fun x y => (cube n).Adj x y ∧ c s(x, y) = true

lemma red_adj {n : ℕ} {c : Sym2 (V n) → Bool} {x y : V n} :
    (red c).Adj x y ↔ (cube n).Adj x y ∧ c s(x, y) = true := by
  simp only [red, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  · intro h; exact ⟨h.1.ne, Or.inl h⟩

lemma adj_iff {n : ℕ} {x y : V n} :
    (cube n).Adj x y ↔ ∃ j, x j ≠ y j ∧ ∀ i, i ≠ j → x i = y i := by
  constructor
  · rintro ⟨-, h | h⟩
    · obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h
      refine ⟨j, ?_, fun i hi => ?_⟩
      · have : j ∈ Finset.univ.filter (fun i => x i ≠ y i) := hj ▸ Finset.mem_singleton_self j
        simpa using this
      · by_contra hne
        have : i ∈ Finset.univ.filter (fun i => x i ≠ y i) := by simpa using hne
        rw [hj] at this; exact hi (Finset.mem_singleton.1 this)
    · obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h
      refine ⟨j, ?_, fun i hi => ?_⟩
      · have : j ∈ Finset.univ.filter (fun i => y i ≠ x i) := hj ▸ Finset.mem_singleton_self j
        simpa [eq_comm] using this
      · by_contra hne
        have : i ∈ Finset.univ.filter (fun i => y i ≠ x i) := by simpa [eq_comm] using hne
        rw [hj] at this; exact hi (Finset.mem_singleton.1 this)
  · rintro ⟨j, hj, h⟩
    refine ⟨fun hxy => hj (hxy ▸ rfl), Or.inl (Finset.card_eq_one.2 ⟨j, ?_⟩)⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hi => by_contra fun hij => hi (h i hij), fun hi => hi ▸ hj⟩

lemma adj_anti {n : ℕ} {x y : V n} (h : (cube n).Adj x y) : (cube n).Adj (anti x) (anti y) := by
  obtain ⟨j, hj, hi⟩ := adj_iff.1 h
  exact adj_iff.2 ⟨j, by simpa [anti] using hj, fun i hij => by simp [anti, hi i hij]⟩

/-- **Part B (core lemma).** There is no labelling of `Q_K` by ordered pairs of distinct labels
from `Fin K` that is antipodally swapped and in which adjacent vertices share an entry. -/
theorem core (K : ℕ) (hK : 2 ≤ K) (q : V K → Fin K × Fin K)
    (h1 : ∀ x, (q x).1 ≠ (q x).2) (h2 : ∀ x, q (anti x) = (q x).swap)
    (h3 : ∀ x y, (cube K).Adj x y → (q x).1 = (q y).1 ∨ (q x).2 = (q y).2) : False := by
  refine NorineB.core' K hK q h1 h2 (fun x c => h3 x (NorineB.flip x c) ?_)
  refine adj_iff.2 ⟨c, by simp [NorineB.flip], fun i hi => ?_⟩
  simp [NorineB.flip, Function.update_of_ne hi]

/-- **Norine's theorem** (reduced to `core`): every antipodal colouring of `Q_n`, `n ≥ 2`, has a
vertex joined to its antipode by a red path. -/
theorem norine (n : ℕ) (_hn : 2 ≤ n) (c : Sym2 (V n) → Bool) (hc : IsAntipodal c) :
    ∃ x, (red c).Reachable x (anti x) := by
  classical
  by_contra hno
  push Not at hno
  set G := red c
  set r := Fintype.card G.ConnectedComponent
  set K := max (max n r) 2
  have hnK : n ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hrK : r ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  -- component index, as an element of `Fin K`
  let idx : V n → Fin K := fun y => Fin.castLE hrK (Fintype.equivFin _ (G.connectedComponentMk y))
  have idx_eq : ∀ y z, idx y = idx z → G.Reachable y z := by
    intro y z h
    have := (Fintype.equivFin _).injective (Fin.castLE_injective hrK h)
    exact SimpleGraph.ConnectedComponent.eq.1 this
  -- projection onto the first `n` coordinates
  let π : V K → V n := fun x i => x (Fin.castLE hnK i)
  have π_anti : ∀ x, π (anti x) = anti (π x) := fun x => rfl
  let q : V K → Fin K × Fin K := fun x => (idx (π x), idx (anti (π x)))
  refine core K (le_max_right _ _) q ?_ ?_ ?_
  · intro x h
    exact hno (π x) (idx_eq _ _ h)
  · intro x
    simp [q, π_anti]
  · intro x y hxy
    obtain ⟨j, hj, hi⟩ := adj_iff.1 hxy
    by_cases hjn : ∃ i : Fin n, Fin.castLE hnK i = j
    · obtain ⟨i0, rfl⟩ := hjn
      have hadj : (cube n).Adj (π x) (π y) := by
        refine adj_iff.2 ⟨i0, hj, fun i hi0 => hi _ ?_⟩
        exact fun h => hi0 (Fin.castLE_injective hnK h)
      cases hcol : c s(π x, π y)
      · -- blue edge: its antipodal edge is red, so the second entries agree
        right
        have hred : G.Adj (anti (π x)) (anti (π y)) :=
          red_adj.2 ⟨adj_anti hadj, by rw [hc _ _ hadj, hcol]; rfl⟩
        show idx (anti (π x)) = idx (anti (π y))
        simp only [idx, SimpleGraph.ConnectedComponent.eq.2 hred.reachable]
      · -- red edge: the first entries agree
        left
        have hred : G.Adj (π x) (π y) := red_adj.2 ⟨hadj, hcol⟩
        show idx (π x) = idx (π y)
        simp only [idx, SimpleGraph.ConnectedComponent.eq.2 hred.reachable]
    · push Not at hjn
      have : π x = π y := funext fun i => hi _ (hjn i)
      left
      show idx (π x) = idx (π y)
      rw [this]



end Norine

open Norine in
theorem OMA.solution : type_of% @OMA.S_opg_edge_antipodal_colorings_of_cubes.main := by
  intro d hd φ hφ
  have hcube : OMA.S_opg_edge_antipodal_colorings_of_cubes.cube d = Norine.cube d := by
    ext x y; simp [OMA.S_opg_edge_antipodal_colorings_of_cubes.cube, Norine.cube, hammingDist]
  have hc : IsAntipodal φ := by
    intro x y hxy
    have h := hφ s(x, y) (by rw [hcube]; exact hxy)
    simp only [Sym2.map_mk] at h
    change φ s(anti x, anti y) ≠ φ s(x, y) at h
    cases hx : φ s(x, y) <;> cases ha : φ s(anti x, anti y) <;> simp_all
  obtain ⟨v, hv⟩ := norine d hd φ hc
  obtain ⟨w⟩ := hv
  let w' := w.toPath
  have hle : red φ ≤ OMA.S_opg_edge_antipodal_colorings_of_cubes.cube d := fun x y h => by
    rw [hcube]; exact (red_adj.1 h).1
  refine ⟨v, (w'.1).mapLe hle, true, ?_, ?_⟩
  · exact (SimpleGraph.Walk.isPath_mapLe hle).2 w'.2
  · intro e he
    erw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    have := (w'.1).edges_subset_edgeSet he'
    induction e' using Sym2.ind with
    | h a b => simpa using (red_adj.1 this).2
