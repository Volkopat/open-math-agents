import OMAStatements.S_opg_laplacian_degrees_of_a_graph

-- Problem: Laplacian Degrees of a Graph
-- Upstream: formal-conjectures statements/opg-laplacian-degrees-of-a-graph.lean:0 (declaration OMA.S_opg_laplacian_degrees_of_a_graph.main)
-- Credit: @mburv (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof of Guo's conjecture (Brouwer–Haemers 2008): for a connected graph, `μ_k ≥ d_k - k + 2`.

Self-contained argument, using only a one-sided Courant–Fischer bound:
* Spectral side: if `x` is orthogonal to the first `k - 1` eigenvectors of the Laplacian `L`,
  then `xᵀLx ≤ μ_k ‖x‖²` and `‖Lx‖² ≤ μ_k xᵀLx` (eigenvalues are nonnegative).
* Fewer than `n` linear constraints have a nonzero common solution.
* `S` = `k` vertices of degree `≥ d = d_k`, `q = d - k + 2`.
  - `q ≤ 0`: trivial.
  - `q ≥ 2`: a vector `x` supported on `S` and orthogonal to the first `k - 1` eigenvectors has
    constant sign on `S` and satisfies `‖Lx‖² ≥ q xᵀLx > 0`, contradicting `μ_k < q`.
  - `q = 1`: two such vectors (one supported on `S`, one on `S - {v₀} + {w}`) combine into a vector
    `z` with `z_w > 0`, `z ≤ 0` on `S` and a zero on `S`, for which `zᵀLz ≥ ‖z‖²`.
-/
open Matrix Finset

namespace LapProof

/-- Spectral one-sided Courant–Fischer facts. -/
theorem spectral_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = m) (hpos : ∀ x, 0 ≤ inner ℝ (T x) x) (j : Fin m) (x : E)
    (hx : ∀ i : Fin m, i < j → inner ℝ (hT.eigenvectorBasis hn i) x = 0) :
    inner ℝ (T x) x ≤ hT.eigenvalues hn j * ‖x‖ ^ 2 ∧
      ‖T x‖ ^ 2 ≤ hT.eigenvalues hn j * inner ℝ (T x) x := by
  set b := hT.eigenvectorBasis hn
  set μ := hT.eigenvalues hn
  have hb : ∀ i, inner ℝ (b i) (T x) = μ i * inner ℝ (b i) x := by
    intro i
    rw [← hT, hT.apply_eigenvectorBasis, real_inner_smul_left]
    rfl
  have hμ0 : ∀ i, 0 ≤ μ i := by
    intro i
    have h := hpos (b i)
    rw [hT.apply_eigenvectorBasis, real_inner_smul_left, real_inner_self_eq_norm_sq,
      b.orthonormal.1 i] at h
    simpa using h
  have hQ : inner ℝ (T x) x = ∑ i, μ i * inner ℝ (b i) x ^ 2 := by
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, hb]; ring
  have hN : ‖x‖ ^ 2 = ∑ i, inner ℝ (b i) x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm]; ring
  have hTN : ‖T x‖ ^ 2 = ∑ i, μ i ^ 2 * inner ℝ (b i) x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, hb]; ring
  have key : ∀ i, μ i * inner ℝ (b i) x ^ 2 ≤ μ j * inner ℝ (b i) x ^ 2 ∧
      μ i ^ 2 * inner ℝ (b i) x ^ 2 ≤ μ j * (μ i * inner ℝ (b i) x ^ 2) := by
    intro i
    rcases lt_or_ge i j with h | h
    · simp [hx i h]
    · have hle : μ i ≤ μ j := hT.eigenvalues_antitone hn h
      have h0 := hμ0 i
      have hs := sq_nonneg (inner ℝ (b i) x)
      constructor
      · exact mul_le_mul_of_nonneg_right hle hs
      · nlinarith [mul_le_mul_of_nonneg_right hle (mul_nonneg h0 hs)]
  refine ⟨?_, ?_⟩
  · rw [hQ, hN, Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => (key i).1
  · rw [hTN, hQ, Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => (key i).2

theorem exists_ne_zero_of_constraints {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} (φ : ι → E →ₗ[ℝ] ℝ) (C : Finset ι)
    (h : C.card < Module.finrank ℝ E) : ∃ x : E, x ≠ 0 ∧ ∀ i ∈ C, φ i x = 0 := by
  let f : E →ₗ[ℝ] (C → ℝ) := LinearMap.pi fun i : C => φ i
  have hk : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hk
  refine ⟨x, hx0, fun i hi => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
  simpa [f] using this

end LapProof
open Matrix Finset

namespace LapProof

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Laplacian quadratic form. -/
noncomputable def Qf (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x)

theorem Qf_edge (x : Fin n → ℝ) :
    Qf G x = (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
  rw [Qf, ← SimpleGraph.lapMatrix_toLinearMap₂', Matrix.toLinearMap₂'_apply']

theorem Qf_deg (x : Fin n → ℝ) :
    Qf G x = ∑ i, (G.degree i : ℝ) * x i ^ 2 -
      ∑ i, ∑ j, if G.Adj i j then x i * x j else 0 := by
  rw [Qf, dotProduct, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SimpleGraph.lapMatrix_mulVec_apply, mul_sub, Finset.mul_sum, ← Finset.sum_filter]
  simp only [SimpleGraph.neighborFinset_eq_filter]
  ring

theorem Qf_nonneg (x : Fin n → ℝ) : 0 ≤ Qf G x := by
  rw [Qf_edge]
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs <;> positivity

/-- Lower bound for vectors supported on a set of high-degree vertices. -/
theorem Qf_ge_of_support (W : Finset (Fin n)) (d : ℝ) (hdeg : ∀ u ∈ W, d ≤ G.degree u)
    (x : Fin n → ℝ) (hx : ∀ u ∉ W, x u = 0) :
    (d - W.card + 1) * ∑ i, x i ^ 2 ≤ Qf G x := by
  classical
  rw [Qf_deg]
  -- restrict cross terms to W × W
  have h1 : ∀ i j, (if G.Adj i j then x i * x j else 0) =
      if G.Adj i j ∧ i ∈ W ∧ j ∈ W then x i * x j else 0 := by
    intro i j
    by_cases hi : i ∈ W <;> by_cases hj : j ∈ W <;> simp [hi, hj, hx]
  have h2 : ∀ i j, (if G.Adj i j ∧ i ∈ W ∧ j ∈ W then x i * x j else 0) ≤
      (if G.Adj i j ∧ i ∈ W ∧ j ∈ W then x i ^ 2 / 2 else 0) +
      (if G.Adj j i ∧ j ∈ W ∧ i ∈ W then x j ^ 2 / 2 else 0) := by
    intro i j
    by_cases h : G.Adj i j ∧ i ∈ W ∧ j ∈ W
    · have h' : G.Adj j i ∧ j ∈ W ∧ i ∈ W := ⟨h.1.symm, h.2.2, h.2.1⟩
      rw [if_pos h, if_pos h, if_pos h']
      nlinarith [sq_nonneg (x i - x j)]
    · have h' : ¬ (G.Adj j i ∧ j ∈ W ∧ i ∈ W) := fun h' => h ⟨h'.1.symm, h'.2.2, h'.2.1⟩
      simp [h, h']
  have h3 : (∑ i, ∑ j, if G.Adj i j then x i * x j else 0) ≤
      ∑ i, ∑ j, (if G.Adj i j ∧ i ∈ W ∧ j ∈ W then x i ^ 2 else 0) := by
    calc (∑ i, ∑ j, if G.Adj i j then x i * x j else 0)
        ≤ ∑ i, ∑ j, ((if G.Adj i j ∧ i ∈ W ∧ j ∈ W then x i ^ 2 / 2 else 0) +
            (if G.Adj j i ∧ j ∈ W ∧ i ∈ W then x j ^ 2 / 2 else 0)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (h1 i j).symm ▸ h2 i j
      _ = ∑ i, ∑ j, (if G.Adj i j ∧ i ∈ W ∧ j ∈ W then x i ^ 2 / 2 else 0) +
            ∑ i, ∑ j, (if G.Adj j i ∧ j ∈ W ∧ i ∈ W then x j ^ 2 / 2 else 0) := by
          simp only [Finset.sum_add_distrib]
      _ = ∑ i, ∑ j, (if G.Adj i j ∧ i ∈ W ∧ j ∈ W then x i ^ 2 else 0) := by
          rw [Finset.sum_comm (f := fun i j => if G.Adj j i ∧ j ∈ W ∧ i ∈ W then x j ^ 2 / 2 else 0),
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> ring
  have h4 : ∀ i, (∑ j, (if G.Adj i j ∧ i ∈ W ∧ j ∈ W then x i ^ 2 else 0)) ≤
      ((W.card : ℝ) - 1) * (if i ∈ W then x i ^ 2 else 0) := by
    intro i
    by_cases hi : i ∈ W
    · simp only [hi, true_and, if_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hsub : (Finset.univ.filter fun j => G.Adj i j ∧ j ∈ W) ⊆ W.erase i := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Finset.mem_erase.mpr ⟨fun h => by subst h; exact G.irrefl hj.1, hj.2⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hi] at hc
      have hW : 1 ≤ W.card := Finset.card_pos.mpr ⟨i, hi⟩
      have : ((Finset.univ.filter fun j => G.Adj i j ∧ j ∈ W).card : ℝ) ≤ (W.card : ℝ) - 1 := by
        have : ((W.card - 1 : ℕ) : ℝ) = (W.card : ℝ) - 1 := by push_cast [Nat.cast_sub hW]; ring
        rw [← this]; exact_mod_cast hc
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    · simp [hi]
  have h5 : ∀ i, (d - W.card + 1) * x i ^ 2 ≤ (G.degree i : ℝ) * x i ^ 2 -
      ((W.card : ℝ) - 1) * (if i ∈ W then x i ^ 2 else 0) := by
    intro i
    by_cases hi : i ∈ W
    · simp only [hi, if_true]
      nlinarith [hdeg i hi, sq_nonneg (x i)]
    · simp [hi, hx i hi]
  calc (d - W.card + 1) * ∑ i, x i ^ 2 = ∑ i, (d - W.card + 1) * x i ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i, ((G.degree i : ℝ) * x i ^ 2 -
          ((W.card : ℝ) - 1) * (if i ∈ W then x i ^ 2 else 0)) := Finset.sum_le_sum fun i _ => h5 i
    _ ≤ ∑ i, (G.degree i : ℝ) * x i ^ 2 - ∑ i, ∑ j, (if G.Adj i j ∧ i ∈ W ∧ j ∈ W then x i ^ 2 else 0) := by
        rw [Finset.sum_sub_distrib]
        linarith [Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h4 i]
    _ ≤ _ := by linarith

/-- positive and negative parts. -/
def posPart' (x : Fin n → ℝ) : Fin n → ℝ := fun i => max (x i) 0
def negPart' (x : Fin n → ℝ) : Fin n → ℝ := fun i => max (-x i) 0

theorem sq_split (s : ℝ) : s ^ 2 = max s 0 ^ 2 + max (-s) 0 ^ 2 := by
  rcases le_total s 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem edge_split (s t : ℝ) :
    (max s 0 - max t 0) ^ 2 + (max (-s) 0 - max (-t) 0) ^ 2 ≤ (s - t) ^ 2 := by
  rcases le_total s 0 with h | h <;> rcases le_total t 0 with h' | h'
  · rw [max_eq_right h, max_eq_right h', max_eq_left (by linarith : (0:ℝ) ≤ -s),
      max_eq_left (by linarith : (0:ℝ) ≤ -t)]; nlinarith
  · rw [max_eq_right h, max_eq_left h', max_eq_left (by linarith : (0:ℝ) ≤ -s),
      max_eq_right (by linarith : -t ≤ 0)]; nlinarith
  · rw [max_eq_left h, max_eq_right h', max_eq_right (by linarith : -s ≤ 0),
      max_eq_left (by linarith : (0:ℝ) ≤ -t)]; nlinarith
  · rw [max_eq_left h, max_eq_left h', max_eq_right (by linarith : -s ≤ 0),
      max_eq_right (by linarith : -t ≤ 0)]; nlinarith

theorem Qf_split (x : Fin n → ℝ) : Qf G (posPart' x) + Qf G (negPart' x) ≤ Qf G x := by
  rw [Qf_edge, Qf_edge, Qf_edge, ← add_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · exact edge_split _ _
  · simp

theorem norm_split (x : Fin n → ℝ) :
    ∑ i, x i ^ 2 = ∑ i, posPart' x i ^ 2 + ∑ i, negPart' x i ^ 2 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => sq_split _

/-- Sign lemma. -/
theorem sign_lemma (S : Finset (Fin n)) (d : ℝ) (hdeg : ∀ u ∈ S, d ≤ G.degree u)
    (x : Fin n → ℝ) (hx : ∀ u ∉ S, x u = 0)
    (hQ : Qf G x < (d - S.card + 2) * ∑ i, x i ^ 2) :
    (∀ v ∈ S, 0 < x v) ∨ (∀ v ∈ S, x v < 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨v, hv, hv0⟩, ⟨v', hv', hv0'⟩⟩ := hcon
  have hp := Qf_ge_of_support G (S.erase v) d (fun u hu => hdeg u (Finset.mem_of_mem_erase hu))
    (posPart' x) (by
      intro u hu
      simp only [posPart']
      by_cases huv : u = v
      · subst huv; exact max_eq_right hv0
      · have : u ∉ S := fun h => hu (Finset.mem_erase.mpr ⟨huv, h⟩)
        rw [hx u this]; simp)
  have hn := Qf_ge_of_support G (S.erase v') d (fun u hu => hdeg u (Finset.mem_of_mem_erase hu))
    (negPart' x) (by
      intro u hu
      simp only [negPart']
      by_cases huv : u = v'
      · subst huv; exact max_eq_right (by linarith)
      · have : u ∉ S := fun h => hu (Finset.mem_erase.mpr ⟨huv, h⟩)
        rw [hx u this]; simp)
  rw [Finset.card_erase_of_mem hv] at hp
  rw [Finset.card_erase_of_mem hv'] at hn
  have hS : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
  have hc : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by push_cast [Nat.cast_sub hS]; ring
  rw [hc] at hp hn
  have e : d - ((S.card : ℝ) - 1) + 1 = d - S.card + 2 := by ring
  rw [e] at hp hn
  have := Qf_split G x
  rw [norm_split x, mul_add] at hQ
  linarith


theorem card_out_ge (S : Finset (Fin n)) (v : Fin n) (hv : v ∈ S) :
    (G.degree v : ℝ) - (S.card - 1) ≤ ((Sᶜ.filter fun u => G.Adj u v).card : ℝ) := by
  classical
  have hdeg : G.degree v = (S.filter fun u => G.Adj u v).card + (Sᶜ.filter fun u => G.Adj u v).card := by
    rw [← G.card_neighborFinset_eq_degree, ← Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter disjoint_compl_right)]
    congr 1
    ext u
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_filter, Finset.mem_compl]
    constructor
    · intro h; by_cases hu : u ∈ S
      · exact Or.inl ⟨hu, h.symm⟩
      · exact Or.inr ⟨hu, h.symm⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h.symm
  have hsub : (S.filter fun u => G.Adj u v) ⊆ S.erase v := by
    intro u hu
    simp only [Finset.mem_filter] at hu
    exact Finset.mem_erase.mpr ⟨fun h => by subst h; exact G.irrefl hu.2, hu.1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hv] at hc
  have hS : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
  have hc' : ((S.filter fun u => G.Adj u v).card : ℝ) ≤ (S.card : ℝ) - 1 := by
    have : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by push_cast [Nat.cast_sub hS]; ring
    rw [← this]; exact_mod_cast hc
  have : (G.degree v : ℝ) = ((S.filter fun u => G.Adj u v).card : ℝ) +
      ((Sᶜ.filter fun u => G.Adj u v).card : ℝ) := by exact_mod_cast hdeg
  linarith

/-- Case `q ≥ 2`. -/
theorem case1 (S : Finset (Fin n)) (d : ℝ) (hdeg : ∀ u ∈ S, d ≤ G.degree u)
    (hr : 1 ≤ d - S.card + 1)
    (x : Fin n → ℝ) (hx : ∀ u ∉ S, x u = 0) (hpos : ∀ v ∈ S, 0 < x v) :
    (d - S.card + 1 + 1) * Qf G x ≤ ∑ u, (G.lapMatrix ℝ *ᵥ x) u ^ 2 ∧
      (d - S.card + 1) * ∑ i, x i ^ 2 ≤ Qf G x := by
  classical
  set r := d - S.card + 1 with hrdef
  set y := G.lapMatrix ℝ *ᵥ x with hy
  have hnn : ∀ u, 0 ≤ x u := by
    intro u; by_cases hu : u ∈ S
    · exact (hpos u hu).le
    · rw [hx u hu]
  have hiii : r * ∑ i, x i ^ 2 ≤ Qf G x := Qf_ge_of_support G S d hdeg x hx
  refine ⟨?_, hiii⟩
  set a := ∑ u ∈ S, y u ^ 2
  set o := ∑ u ∈ Sᶜ, y u ^ 2
  have hsplit : ∑ u, y u ^ 2 = a + o := (Finset.sum_add_sum_compl S _).symm
  have hQ : Qf G x = ∑ u ∈ S, x u * y u := by
    rw [Qf, dotProduct, ← Finset.sum_add_sum_compl S]
    have : ∑ u ∈ Sᶜ, x u * y u = 0 :=
      Finset.sum_eq_zero fun u hu => by rw [hx u (Finset.mem_compl.mp hu)]; ring
    rw [this, add_zero]
  have hN : ∑ i, x i ^ 2 = ∑ u ∈ S, x u ^ 2 := by
    rw [← Finset.sum_add_sum_compl S]
    have : ∑ u ∈ Sᶜ, x u ^ 2 = 0 :=
      Finset.sum_eq_zero fun u hu => by rw [hx u (Finset.mem_compl.mp hu)]; ring
    rw [this, add_zero]
  have hiv : 0 ≤ a - 2 * r * Qf G x + r ^ 2 * ∑ i, x i ^ 2 := by
    have : 0 ≤ ∑ u ∈ S, (y u - r * x u) ^ 2 := Finset.sum_nonneg fun u _ => sq_nonneg _
    have e : ∑ u ∈ S, (y u - r * x u) ^ 2 = a - 2 * r * Qf G x + r ^ 2 * ∑ i, x i ^ 2 := by
      rw [hQ, hN, Finset.mul_sum, Finset.mul_sum]
      simp only [a, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    linarith
  -- outside rows
  have hi : ∑ u ∈ Sᶜ, ∑ v, (if G.Adj u v then x v ^ 2 else 0) ≤ o := by
    refine Finset.sum_le_sum fun u hu => ?_
    have hyu : y u = - ∑ v ∈ G.neighborFinset u, x v := by
      rw [hy, SimpleGraph.lapMatrix_mulVec_apply, hx u (Finset.mem_compl.mp hu)]; ring
    rw [hyu, neg_sq, ← Finset.sum_filter]
    simp only [SimpleGraph.neighborFinset_eq_filter]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun v _ => hnn v
  have hii : r * ∑ i, x i ^ 2 ≤ ∑ u ∈ Sᶜ, ∑ v, (if G.Adj u v then x v ^ 2 else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hv : v ∈ S
    · have := card_out_ge G S v hv
      have := hdeg v hv
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    · rw [hx v hv]; simp
  have hrQ : 0 ≤ (r - 1) * (Qf G x - r * ∑ i, x i ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hsplit]
  nlinarith

end LapProof

namespace LapProof
open Matrix Finset

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem case2_core (S : Finset (Fin n)) (w : Fin n) (hw : w ∉ S) (hwdeg : 1 ≤ G.degree w)
    (hdeg : ∀ u ∈ S, (S.card : ℝ) - 1 ≤ G.degree u)
    (z : Fin n → ℝ) (hz : ∀ u, u ∉ S → u ≠ w → z u = 0) (hzw : 0 < z w)
    (hzS : ∀ v ∈ S, z v ≤ 0) (v1 : Fin n) (hv1 : v1 ∈ S) (hz1 : z v1 = 0) :
    ∑ i, z i ^ 2 ≤ Qf G z := by
  have hp := Qf_ge_of_support G {w} 1 (by
      intro u hu; rw [Finset.mem_singleton] at hu; subst hu; exact_mod_cast hwdeg)
    (posPart' z) (by
      intro u hu
      rw [Finset.mem_singleton] at hu
      simp only [posPart']
      by_cases huS : u ∈ S
      · exact max_eq_right (hzS u huS)
      · rw [hz u huS hu]; simp)
  have hn := Qf_ge_of_support G (S.erase v1) ((S.card : ℝ) - 1)
    (fun u hu => hdeg u (Finset.mem_of_mem_erase hu))
    (negPart' z) (by
      intro u hu
      simp only [negPart']
      by_cases huv : u = v1
      · subst huv; rw [hz1]; simp
      · by_cases huw : u = w
        · subst huw; exact max_eq_right (by linarith)
        · have : u ∉ S := fun h => hu (Finset.mem_erase.mpr ⟨huv, h⟩)
          rw [hz u this huw]; simp)
  rw [Finset.card_erase_of_mem hv1] at hn
  have hS : 1 ≤ S.card := Finset.card_pos.mpr ⟨v1, hv1⟩
  have hc : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by push_cast [Nat.cast_sub hS]; ring
  rw [hc] at hn
  simp only [Finset.card_singleton, Nat.cast_one] at hp
  have := Qf_split G z
  rw [norm_split z]
  linarith

theorem exists_highdeg (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ S : Finset (Fin n), S.card = k ∧
      ∀ v ∈ S, OMA.S_opg_laplacian_degrees_of_a_graph.kthLargestDegree G k ≤ G.degree v := by
  classical
  set m := Finset.univ.val.map fun v => G.degree v
  set l := m.sort (· ≥ ·) with hl
  have hlen : l.length = n := by simp [l, m]
  have hd : OMA.S_opg_laplacian_degrees_of_a_graph.kthLargestDegree G k = l[k - 1]'(by omega) := by
    rw [OMA.S_opg_laplacian_degrees_of_a_graph.kthLargestDegree, List.getD_eq_getElem]
  set d := OMA.S_opg_laplacian_degrees_of_a_graph.kthLargestDegree G k
  have hpw : List.Pairwise (· ≥ ·) l := Multiset.pairwise_sort _ _
  have htake : ∀ x ∈ l.take k, d ≤ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take, hd]
    have hik : i < k := by simp at hi; omega
    rcases Nat.lt_or_ge i (k - 1) with h | h
    · exact List.pairwise_iff_getElem.mp hpw i (k - 1) (by omega) (by omega) h
    · have : i = k - 1 := by omega
      subst this; exact le_rfl
  have hcount : k ≤ l.countP (fun x => decide (d ≤ x)) := by
    have h1 : (l.take k).countP (fun x => decide (d ≤ x)) = (l.take k).length :=
      List.countP_eq_length.mpr (fun x hx => by simpa using htake x hx)
    have h2 := (List.take_sublist k l).countP_le (p := fun x => decide (d ≤ x))
    rw [h1, List.length_take] at h2
    omega
  have hcard : (Finset.univ.filter fun v => d ≤ G.degree v).card =
      l.countP (fun x => decide (d ≤ x)) := by
    rw [← Multiset.coe_countP, hl, Multiset.sort_eq, Multiset.countP_map]
    rfl
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (s := Finset.univ.filter fun v => d ≤ G.degree v)
    (n := k) (by omega)
  exact ⟨S, hSc, fun v hv => by simpa using hS hv⟩

end LapProof

theorem LapProof.Qf_neg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (f : Fin n → ℝ) :
    LapProof.Qf G (-f) = LapProof.Qf G f := by
  simp [LapProof.Qf, Matrix.mulVec_neg]

theorem LapProof.sumsq_neg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (f : Fin n → ℝ) :
    ∑ i, (G.lapMatrix ℝ *ᵥ (-f)) i ^ 2 = ∑ i, (G.lapMatrix ℝ *ᵥ f) i ^ 2 := by
  simp [Matrix.mulVec_neg]

open LapProof Matrix Finset in
theorem OMA.solution : type_of% @OMA.S_opg_laplacian_degrees_of_a_graph.main := by
  intro n G _ hconn k hk1 hkn
  obtain ⟨S, hScard, hSdeg⟩ := exists_highdeg G k hk1 (by omega)
  set d := OMA.S_opg_laplacian_degrees_of_a_graph.kthLargestDegree G k with hd
  have hL : (G.lapMatrix ℝ).IsHermitian := (SimpleGraph.posSemidef_lapMatrix ℝ G).isHermitian
  have hT : (toEuclideanLin (G.lapMatrix ℝ)).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hL
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) :=
    finrank_euclideanSpace
  set μ := hT.eigenvalues hfin with hμdef
  set b := hT.eigenvectorBasis hfin with hbdef
  have hjm : k - 1 < Fintype.card (Fin n) := by simp; omega
  set j : Fin (Fintype.card (Fin n)) := ⟨k - 1, hjm⟩ with hjdef
  have hev : OMA.S_opg_laplacian_degrees_of_a_graph.laplacianEigenvalue G k = μ j := by
    unfold OMA.S_opg_laplacian_degrees_of_a_graph.laplacianEigenvalue
    have : (G.lapMatrix ℝ).charpoly.roots = (G.lapMatrix ℝ).charpoly.roots.map RCLike.re := by
      simp
    rw [this, hL.sort_roots_charpoly_eq_eigenvalues₀,
      List.getD_eq_getElem _ _ (by simpa using hjm), List.getElem_ofFn]
    rfl
  have hQx : ∀ x : EuclideanSpace ℝ (Fin n),
      inner ℝ (toEuclideanLin (G.lapMatrix ℝ) x) x = Qf G x.ofLp := by
    intro x
    rw [toEuclideanLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp [Qf]
  have hNx : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 = ∑ i, x.ofLp i ^ 2 := by
    intro x; rw [EuclideanSpace.norm_sq_eq]; simp
  have hTx : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖toEuclideanLin (G.lapMatrix ℝ) x‖ ^ 2 = ∑ i, (G.lapMatrix ℝ *ᵥ x.ofLp) i ^ 2 := by
    intro x; rw [EuclideanSpace.norm_sq_eq]; simp [toEuclideanLin_apply]
  have hpos : ∀ x, 0 ≤ inner ℝ (toEuclideanLin (G.lapMatrix ℝ) x) x :=
    fun x => (hQx x) ▸ Qf_nonneg G _
  have spec : ∀ x : EuclideanSpace ℝ (Fin n), (∀ i, i < j → inner ℝ (b i) x = 0) →
      Qf G x.ofLp ≤ μ j * ∑ i, x.ofLp i ^ 2 ∧
        ∑ i, (G.lapMatrix ℝ *ᵥ x.ofLp) i ^ 2 ≤ μ j * Qf G x.ofLp := by
    intro x hx
    have := spectral_bound _ hT hfin hpos j x hx
    rw [hQx, hNx, hTx] at this
    exact this
  have hμ0 : 0 ≤ μ j := by
    have h := hpos (b j)
    rw [hT.apply_eigenvectorBasis, real_inner_smul_left, real_inner_self_eq_norm_sq,
      b.orthonormal.1 j] at h
    simpa using h
  have exists_x : ∀ Z : Finset (Fin n), k - 1 + Z.card < n →
      ∃ x : EuclideanSpace ℝ (Fin n), x ≠ 0 ∧ (∀ i, i < j → inner ℝ (b i) x = 0) ∧
        ∀ u ∈ Z, x.ofLp u = 0 := by
    intro Z hZ
    obtain ⟨x, hx0, hx⟩ := exists_ne_zero_of_constraints (E := EuclideanSpace ℝ (Fin n))
      (ι := Fin (Fintype.card (Fin n)) ⊕ Fin n)
      (fun s => Sum.elim (fun i => (innerSL ℝ (b i)).toLinearMap)
        (fun u => (EuclideanSpace.proj u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).toLinearMap) s)
      ((Finset.Iio j).disjSum Z)
      (by rw [Finset.card_disjSum, Fin.card_Iio, finrank_euclideanSpace_fin]; simpa [j] using hZ)
    refine ⟨x, hx0, fun i hi => ?_, fun u hu => ?_⟩
    · have := hx (Sum.inl i) (by simp [hi]); simpa using this
    · have := hx (Sum.inr u) (by simp [hu]); simpa using this
  have hNpos : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → 0 < ∑ i, x.ofLp i ^ 2 := by
    intro x hx; rw [← hNx]; have := norm_pos_iff.mpr hx; positivity
  rw [hev]
  by_contra hlt
  push Not at hlt
  have hdegR : ∀ u ∈ S, (d : ℝ) ≤ G.degree u := fun u hu => by exact_mod_cast hSdeg u hu
  have hSc : Sᶜ.card = n - k := by rw [Finset.card_compl, hScard]; simp
  rcases Nat.lt_or_ge d k with hdk | hdk
  · rcases Nat.lt_or_ge (d + 1) k with hdk2 | hdk2
    · have : (d : ℝ) + 2 ≤ k := by exact_mod_cast hdk2
      linarith
    · have hkd : k = d + 1 := by omega
      have hkdR : (k : ℝ) = d + 1 := by exact_mod_cast hkd
      have hμ1 : μ j < 1 := by linarith
      have hdeg2 : ∀ u ∈ S, (S.card : ℝ) - 1 ≤ G.degree u := by
        intro u hu; rw [hScard]; have := hdegR u hu; linarith
      obtain ⟨w, hw⟩ : Sᶜ.Nonempty := by rw [← Finset.card_pos, hSc]; omega
      have hwS : w ∉ S := Finset.mem_compl.mp hw
      obtain ⟨v0, hv0⟩ : S.Nonempty := by rw [← Finset.card_pos, hScard]; omega
      have hwdeg : 1 ≤ G.degree w :=
        (hconn.preconnected w v0).degree_pos_left (fun h => hwS (h ▸ hv0))
      obtain ⟨y0, hy0, hy0c, hy0Z⟩ := exists_x Sᶜ (by rw [hSc]; omega)
      have hy0S : ∀ u ∉ S, y0.ofLp u = 0 := fun u hu => hy0Z u (Finset.mem_compl.mpr hu)
      obtain ⟨y, hyc, hyS, hypos⟩ : ∃ y : EuclideanSpace ℝ (Fin n),
          (∀ i, i < j → inner ℝ (b i) y = 0) ∧ (∀ u ∉ S, y.ofLp u = 0) ∧
            ∀ v ∈ S, 0 < y.ofLp v := by
        have hQ : Qf G y0.ofLp < ((d : ℝ) - S.card + 2) * ∑ i, y0.ofLp i ^ 2 := by
          have h1 := (spec y0 hy0c).1
          have h2 := hNpos y0 hy0
          have : (d : ℝ) - S.card + 2 = 1 := by rw [hScard, hkdR]; ring
          rw [this]; nlinarith
        rcases sign_lemma G S d hdegR _ hy0S hQ with h | h
        · exact ⟨y0, hy0c, hy0S, h⟩
        · refine ⟨-y0, fun i hi => by rw [inner_neg_right, hy0c i hi, neg_zero],
            fun u hu => by simp [hy0S u hu], fun v hv => by simpa using h v hv⟩
      obtain ⟨x0, hx0, hx0c, hx0Z⟩ := exists_x (insert v0 (Sᶜ.erase w)) (by
        rw [Finset.card_insert_of_notMem (by simp [hv0]), Finset.card_erase_of_mem hw, hSc]
        omega)
      have hx0S : ∀ u, u ∉ S → u ≠ w → x0.ofLp u = 0 :=
        fun u hu huw => hx0Z u (by simp [hu, huw])
      have hx0v0 : x0.ofLp v0 = 0 := hx0Z v0 (by simp)
      have hx0w : x0.ofLp w ≠ 0 := by
        intro h0
        have hsupp : ∀ u ∉ S.erase v0, x0.ofLp u = 0 := by
          intro u hu
          by_cases huv : u = v0
          · rw [huv, hx0v0]
          by_cases huw : u = w
          · rw [huw, h0]
          exact hx0S u (fun h => hu (Finset.mem_erase.mpr ⟨huv, h⟩)) huw
        have := Qf_ge_of_support G (S.erase v0) ((S.card : ℝ) - 1)
          (fun u hu => hdeg2 u (Finset.mem_of_mem_erase hu)) _ hsupp
        rw [Finset.card_erase_of_mem hv0] at this
        have hS1 : 1 ≤ S.card := by omega
        have hc : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
          push_cast [Nat.cast_sub hS1]; ring
        rw [hc] at this
        have h1 := (spec x0 hx0c).1
        have h2 := hNpos x0 hx0
        nlinarith
      obtain ⟨xx, hxxc, hxxS, hxxw⟩ : ∃ xx : EuclideanSpace ℝ (Fin n),
          (∀ i, i < j → inner ℝ (b i) xx = 0) ∧ (∀ u, u ∉ S → u ≠ w → xx.ofLp u = 0) ∧
            0 < xx.ofLp w := by
        rcases lt_or_gt_of_ne hx0w with h | h
        · exact ⟨-x0, fun i hi => by rw [inner_neg_right, hx0c i hi, neg_zero],
            fun u hu huw => by simp [hx0S u hu huw], by simpa using h⟩
        · exact ⟨x0, hx0c, hx0S, h⟩
      have hSne : S.Nonempty := ⟨v0, hv0⟩
      obtain ⟨v1, hv1, hv1t⟩ := Finset.exists_mem_eq_inf' hSne (fun v => -xx.ofLp v / y.ofLp v)
      set t := S.inf' hSne (fun v => -xx.ofLp v / y.ofLp v) with ht
      set z := xx + t • y with hz
      have hzf : ∀ u, z.ofLp u = xx.ofLp u + t * y.ofLp u := fun u => by simp [z]
      have hzc : ∀ i, i < j → inner ℝ (b i) z = 0 := fun i hi => by
        rw [hz, inner_add_right, inner_smul_right, hxxc i hi, hyc i hi]; ring
      have hzw : 0 < z.ofLp w := by rw [hzf, hyS w hwS]; simpa using hxxw
      have hzS : ∀ v ∈ S, z.ofLp v ≤ 0 := by
        intro v hv
        have h1 : t ≤ -xx.ofLp v / y.ofLp v := Finset.inf'_le _ hv
        have h2 := hypos v hv
        rw [hzf]
        rw [le_div_iff₀ h2] at h1
        linarith
      have hz1 : z.ofLp v1 = 0 := by
        have h2 := hypos v1 hv1
        rw [hzf, hv1t]
        field_simp
        ring
      have hzne : z ≠ 0 := fun h => by rw [h] at hzw; simp at hzw
      have hcore := case2_core G S w hwS hwdeg hdeg2 z.ofLp
        (fun u hu huw => by rw [hzf, hxxS u hu huw, hyS u hu]; ring) hzw hzS v1 hv1 hz1
      have h1 := (spec z hzc).1
      have h2 := hNpos z hzne
      nlinarith
  · obtain ⟨x0, hx0, hx0c, hx0Z⟩ := exists_x Sᶜ (by rw [hSc]; omega)
    have hx0S : ∀ u ∉ S, x0.ofLp u = 0 := fun u hu => hx0Z u (Finset.mem_compl.mpr hu)
    have hkdR : (k : ℝ) ≤ d := by exact_mod_cast hdk
    have hr : (1 : ℝ) ≤ d - S.card + 1 := by rw [hScard]; linarith
    have hQ : Qf G x0.ofLp < ((d : ℝ) - S.card + 2) * ∑ i, x0.ofLp i ^ 2 := by
      have h1 := (spec x0 hx0c).1
      have h2 := hNpos x0 hx0
      have : μ j < (d : ℝ) - S.card + 2 := by rw [hScard]; linarith
      nlinarith
    have key : ∀ f : Fin n → ℝ, (∀ u ∉ S, f u = 0) → (∀ v ∈ S, 0 < f v) →
        ∑ i, (G.lapMatrix ℝ *ᵥ f) i ^ 2 ≤ μ j * Qf G f → False := by
      intro f hf hfpos hspec
      obtain ⟨h1, h2⟩ := case1 G S d hdegR hr f hf hfpos
      obtain ⟨v0, hv0⟩ : S.Nonempty := by rw [← Finset.card_pos, hScard]; omega
      have hN : 0 < ∑ i, f i ^ 2 := lt_of_lt_of_le (by have := hfpos v0 hv0; positivity)
        (Finset.single_le_sum (fun i _ => sq_nonneg (f i)) (Finset.mem_univ v0))
      have hμq : μ j < d - S.card + 1 + 1 := by rw [hScard]; linarith
      have hQpos : 0 < Qf G f := by nlinarith
      nlinarith
    rcases sign_lemma G S d hdegR _ hx0S hQ with h | h
    · exact key _ hx0S h (spec x0 hx0c).2
    · refine key (-x0.ofLp) (fun u hu => by simp [hx0S u hu]) (fun v hv => by simpa using h v hv) ?_
      rw [Qf_neg, sumsq_neg]
      exact (spec x0 hx0c).2
