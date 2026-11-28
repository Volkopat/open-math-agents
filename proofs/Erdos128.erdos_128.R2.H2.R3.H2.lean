import OMAReductions.R_Erdos128_erdos_128_R2_H2_R3
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.Compact

-- Credit: @iskamag

/-!
# Proof of Erdos128.erdos_128.R2.H2.R3.H2 (Theorem J2: Brandt-Thomasse Vega Classification)

Proves `OMA.R_Erdos128_erdos_128_R2_H2_R3.H2`: every maximal triangle-free non-3-colorable
graph `M` with `3 * delta(M) > n` admits a surjective edge-reflecting map onto an active
Vega graph `V_i(dy, de)` (`i >= 2`).
-/

namespace Erdos128ThmJ

open Finset SimpleGraph

/-- Helper: twin equivalence relation on a graph `M`. -/
lemma twin_equivalence {V : Type} (M : SimpleGraph V) :
    Equivalence (fun u v : V => ∀ z : V, M.Adj u z ↔ M.Adj v z) where
  refl _ _ := Iff.rfl
  symm h z := (h z).symm
  trans h1 h2 z := (h1 z).trans (h2 z)

/-- Twin-free quotient of a maximal triangle-free graph `M` with `n < 3 * δ(M)` and `¬ M.Colorable 3`. -/
theorem twin_quotient_of_maximal_tf {V : Type} [Fintype V] (M : SimpleGraph V)
    (hMTF : M.CliqueFree 3)
    (hMmax : ∀ u v : V, u ≠ v → ¬ M.Adj u v → ∃ w : V, M.Adj u w ∧ M.Adj v w)
    (h3d : ∀ x : V, Fintype.card V < 3 * (M.neighborSet x).ncard)
    (hnot3 : ¬ M.Colorable 3) :
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (H : SimpleGraph U) (_ : DecidableRel H.Adj)
      (φ : M →g H) (w0 : U → ℝ),
      Function.Surjective φ ∧
      (∀ u v : V, M.Adj u v ↔ H.Adj (φ u) (φ v)) ∧
      H.CliqueFree 3 ∧
      (∀ x y : U, x ≠ y → ¬ H.Adj x y → ∃ z : U, H.Adj x z ∧ H.Adj y z) ∧
      (∀ x y : U, (∀ z : U, H.Adj x z ↔ H.Adj y z) → x = y) ∧
      ¬ H.Colorable 3 ∧
      (∀ x : U, 0 < w0 x) ∧
      (∑ x : U, w0 x = 1) ∧
      (∀ x : U, (1 / 3 : ℝ) < ∑ y : U, if H.Adj x y then w0 y else 0) := by
  classical
  set n := Fintype.card V
  have hn_pos : 0 < n := by
    by_contra h0
    have hE : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
    exact hnot3 ⟨SimpleGraph.Coloring.mk (fun x => (hE.false x).elim) (fun {a _} _ => (hE.false a).elim)⟩
  let s : Setoid V := ⟨fun u v => ∀ z : V, M.Adj u z ↔ M.Adj v z, twin_equivalence M⟩
  let U := Quotient s
  let _ : Fintype U := Quotient.fintype s
  let _ : DecidableEq U := Classical.decEq U
  let HAdj : U → U → Prop := Quotient.lift₂ M.Adj (by
    intro a₁ b₁ a₂ b₂ ha hb
    exact propext ((ha b₁).trans (by rw [M.adj_comm a₂ b₁, M.adj_comm a₂ b₂]; exact hb a₂)))
  have hH_symm : Std.Symm HAdj := ⟨fun x y => Quotient.inductionOn₂ x y (fun _ _ hab => hab.symm)⟩
  have hH_loopless : Std.Irrefl HAdj := ⟨fun x => Quotient.inductionOn x (fun a => M.loopless.irrefl a)⟩
  let H : SimpleGraph U := ⟨HAdj, hH_symm, hH_loopless⟩
  let _ : DecidableRel H.Adj := Classical.decRel H.Adj
  let φ : M →g H := ⟨Quotient.mk s, fun h => h⟩
  have hφ_surj : Function.Surjective φ := Quotient.exists_rep
  have hH_mk : ∀ u v : V, H.Adj (Quotient.mk s u) (Quotient.mk s v) ↔ M.Adj u v := fun _ _ => Iff.rfl
  have hHTF : H.CliqueFree 3 := by
    intro t ht
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hteq⟩ : ∃ x ∈ t, ∃ y ∈ t, ∃ z ∈ t,
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ t = {x, y, z} := by
      have h3 := Finset.card_eq_three.mp ht.2
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h3
      exact ⟨x, by simp, y, by simp, z, by simp, hxy, hxz, hyz, rfl⟩
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    obtain ⟨c, rfl⟩ := Quotient.exists_rep z
    have hab : M.Adj a b := (hH_mk a b).mp (ht.1 hx hy hxy)
    have hbc : M.Adj b c := (hH_mk b c).mp (ht.1 hy hz hyz)
    have hac : M.Adj a c := (hH_mk a c).mp (ht.1 hx hz hxz)
    exact OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hMTF hab hbc hac
  have hHmax : ∀ x y : U, x ≠ y → ¬ H.Adj x y → ∃ z : U, H.Adj x z ∧ H.Adj y z := by
    intro x y hxy hna
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    have hab_ne : a ≠ b := fun h => hxy (congrArg (Quotient.mk s) h)
    obtain ⟨w, haw, hbw⟩ := hMmax a b hab_ne hna
    exact ⟨Quotient.mk s w, haw, hbw⟩
  have hHtwin : ∀ x y : U, (∀ z : U, H.Adj x z ↔ H.Adj y z) → x = y := by
    intro x y hiff
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    exact Quotient.sound (fun z => hiff (Quotient.mk s z))
  have hHnot3 : ¬ H.Colorable 3 := by
    rintro ⟨c⟩
    exact hnot3 ⟨c.comp φ⟩
  let w0 : U → ℝ := fun x => (#(Finset.univ.filter (fun v : V => Quotient.mk s v = x)) : ℝ) / (n : ℝ)
  have hn_pos_R : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hw0_pos : ∀ x : U, 0 < w0 x := by
    intro x
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    have hcard_pos : 0 < #(Finset.univ.filter (fun v : V => Quotient.mk s v = Quotient.mk s a)) :=
      Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, rfl⟩⟩
    exact div_pos (Nat.cast_pos.mpr hcard_pos) hn_pos_R
  have hw0_sum : ∑ x : U, w0 x = 1 := by
    simp only [w0, ← Finset.sum_div]
    have hsum_nat : ∑ x : U, #(Finset.univ.filter (fun v : V => Quotient.mk s v = x)) = n := by
      have hpart := Finset.card_eq_sum_card_fiberwise
        (f := Quotient.mk s) (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset U))
        (fun v _ => Finset.mem_univ _)
      simpa [n] using hpart.symm
    have hsum_R : (∑ x : U, (#(Finset.univ.filter (fun v : V => Quotient.mk s v = x)) : ℝ)) = (n : ℝ) := by
      exact_mod_cast hsum_nat
    rw [hsum_R, div_self (ne_of_gt hn_pos_R)]
  have hw0_deg : ∀ x : U, (1 / 3 : ℝ) < ∑ y : U, if H.Adj x y then w0 y else 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    have hdeg_nat : n < 3 * #(Finset.univ.filter (M.Adj a)) := by
      have h1 := h3d a
      rw [Set.ncard_eq_toFinset_card'] at h1
      have heq : (M.neighborSet a).toFinset = Finset.univ.filter (M.Adj a) := by
        ext y; simp [SimpleGraph.mem_neighborSet]
      rwa [heq] at h1
    have hsum_eq : ∑ y : U, (if H.Adj (Quotient.mk s a) y then
        #(Finset.univ.filter (fun v : V => Quotient.mk s v = y)) else 0) =
        #(Finset.univ.filter (M.Adj a)) := by
      rw [← Finset.sum_filter]
      have hfib := Finset.card_eq_sum_card_fiberwise
        (f := Quotient.mk s) (s := Finset.univ.filter (M.Adj a))
        (t := Finset.univ.filter (H.Adj (Quotient.mk s a)))
        (fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩)
      rw [hfib]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      congr 1; ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hvy; refine ⟨?_, hvy⟩
        have hHy := (Finset.mem_filter.mp hy).2
        rw [← hvy] at hHy; exact hHy
      · rintro ⟨_, hvy⟩; exact hvy
    have hsum_R : (∑ y : U, if H.Adj (Quotient.mk s a) y then w0 y else 0) =
        (#(Finset.univ.filter (M.Adj a)) : ℝ) / (n : ℝ) := by
      have h1 : ∀ y : U, (if H.Adj (Quotient.mk s a) y then w0 y else 0) =
          ((if H.Adj (Quotient.mk s a) y then
            #(Finset.univ.filter (fun v : V => Quotient.mk s v = y)) else 0) : ℝ) / (n : ℝ) := by
        intro y; split_ifs <;> simp [w0]
      simp_rw [h1, ← Finset.sum_div]
      congr 1; exact_mod_cast hsum_eq
    rw [hsum_R, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3) hn_pos_R]
    have hdeg_R : (n : ℝ) < 3 * (#(Finset.univ.filter (M.Adj a)) : ℝ) := by exact_mod_cast hdeg_nat
    linarith
  exact ⟨U, inferInstance, inferInstance, H, inferInstance, φ, w0,
    hφ_surj, fun u v => (hH_mk u v).symm, hHTF, hHmax, hHtwin, hHnot3, hw0_pos, hw0_sum, hw0_deg⟩

/-- Symmetric LP Duality Reduction via Hahn-Banach Separation:
    Given any finite graph `H` on `U` with a probability weight `w0` whose minimum weighted degree
    strictly exceeds `c`, either `H` admits a strictly positive regular probability weight `ω` with
    `∀ u, deg_ω(u) = δ > c`, OR `H` admits a probability weight `w` vanishing on at least one vertex
    (`∃ x, w x = 0`) while still maintaining `∀ u, c < deg_w(u)`. -/
theorem regular_or_proper_support {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj]
    (c : ℝ) (w0 : U → ℝ)
    (hw0_nn : ∀ u : U, 0 ≤ w0 u) (hw0_sum : ∑ u : U, w0 u = 1)
    (hw0_deg : ∀ u : U, c < ∑ v : U, if H.Adj u v then w0 v else 0) :
    (∃ (ω : U → ℝ) (δ : ℝ),
      (∀ u : U, 0 < ω u) ∧ (∑ u : U, ω u = 1) ∧ c < δ ∧
      (∀ u : U, ∑ v : U, (if H.Adj u v then ω v else 0) = δ)) ∨
    (∃ (w : U → ℝ),
      (∀ u : U, 0 ≤ w u) ∧ (∑ u : U, w u = 1) ∧ (∃ x : U, w x = 0) ∧
      (∀ u : U, c < ∑ v : U, if H.Adj u v then w v else 0)) := by
  by_cases hU : IsEmpty U
  · exfalso; simp at hw0_sum
  have : Nonempty U := not_isEmpty_iff.mp hU
  let A : (U → ℝ) → (U → ℝ) := fun w u => ∑ v : U, if H.Adj u v then w v else 0
  have hA_cont : Continuous A := by
    refine continuous_pi (fun u => ?_)
    refine continuous_finsetSum _ (fun v _ => ?_)
    by_cases huv : H.Adj u v
    · simp only [huv, ite_true]; exact continuous_apply v
    · simp only [huv, ite_false]; exact continuous_const
  let minDeg : (U → ℝ) → ℝ := fun w => Finset.univ.inf' Finset.univ_nonempty (A w)
  have hmin_cont : Continuous minDeg := by
    have hcont : ∀ (s : Finset U) (hs : s.Nonempty), Continuous (fun w => s.inf' hs (A w)) := by
      intro s
      induction s using Finset.induction with
      | empty => intro hs; exact (Finset.not_nonempty_empty hs).elim
      | insert a s ha ih =>
        intro hs
        by_cases hs0 : s.Nonempty
        · have heq : (fun w => (insert a s).inf' hs (A w)) =
              fun w => min (A w a) (s.inf' hs0 (A w)) := by
            funext w; exact Finset.inf'_insert hs0 (A w)
          rw [heq]
          exact ((continuous_apply a).comp hA_cont).min (ih hs0)
        · obtain rfl : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs0
          have heq : (fun w => (insert a (∅ : Finset U)).inf' hs (A w)) =
              fun w => A w a := by
            funext w; exact Finset.inf'_singleton (b := a) (f := A w)
          rw [heq]
          exact (continuous_apply a).comp hA_cont
    exact hcont Finset.univ Finset.univ_nonempty
  have hcomp : IsCompact (stdSimplex ℝ U) := isCompact_stdSimplex ℝ U
  have hne : (stdSimplex ℝ U).Nonempty := ⟨w0, hw0_nn, hw0_sum⟩
  obtain ⟨w_star, hw_mem, hw_max⟩ := hcomp.exists_isMaxOn hne hmin_cont.continuousOn
  set δ := minDeg w_star
  have hδ_gt : c < δ := by
    have h0 : c < minDeg w0 := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun u _ => hw0_deg u)
    exact lt_of_lt_of_le h0 (hw_max ⟨hw0_nn, hw0_sum⟩)
  have hw_deg : ∀ u : U, δ ≤ A w_star u := fun u => Finset.inf'_le (A w_star) (Finset.mem_univ u)
  by_cases hw_zero : ∃ x : U, w_star x = 0
  · exact Or.inr ⟨w_star, hw_mem.1, hw_mem.2, hw_zero, fun u => lt_of_lt_of_le hδ_gt (hw_deg u)⟩
  have hw_pos : ∀ u : U, 0 < w_star u := fun u =>
    lt_of_le_of_ne (hw_mem.1 u) (Ne.symm (fun h => hw_zero ⟨u, h⟩))
  -- Apply Hahn-Banach separation between s = {y | ∀ u, δ < y u} and t = A '' stdSimplex
  let s : Set (U → ℝ) := {y : U → ℝ | ∀ u : U, δ < y u}
  let t : Set (U → ℝ) := A '' stdSimplex ℝ U
  have hs_conv : Convex ℝ s := by
    intro y₁ hy₁ y₂ hy₂ a b ha hb hab u
    simp only [s, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy₁ hy₂ ⊢
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1]; linarith [hy₂ u]
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have h1 : a * δ < a * y₁ u := mul_lt_mul_of_pos_left (hy₁ u) ha_pos
      have h2 : b * δ ≤ b * y₂ u := mul_le_mul_of_nonneg_left (le_of_lt (hy₂ u)) hb
      have h3 : a * δ + b * δ = δ := by rw [← add_mul, hab, one_mul]
      linarith
  have hs_open : IsOpen s := by
    have heq : s = ⋂ u : U, (fun y : U → ℝ => y u) ⁻¹' Set.Ioi δ := by
      ext y; simp [s]
    rw [heq]
    exact isOpen_iInter_of_finite (fun u => isOpen_Ioi.preimage (continuous_apply u))
  have hA_add : ∀ x y : U → ℝ, A (x + y) = A x + A y := by
    intro x y; funext u; simp only [A, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_); split_ifs <;> ring
  have hA_smul : ∀ (r : ℝ) (x : U → ℝ), A (r • x) = r • A x := by
    intro r x; funext u; simp only [A, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_); split_ifs <;> ring
  have ht_conv : Convex ℝ t := by
    rintro _ ⟨w₁, hw₁, rfl⟩ _ ⟨w₂, hw₂, rfl⟩ a b ha hb hab
    refine ⟨a • w₁ + b • w₂, convex_stdSimplex ℝ U hw₁ hw₂ ha hb hab, ?_⟩
    rw [hA_add, hA_smul, hA_smul]
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro y hy ⟨w, hw, rfl⟩
    have hlt : δ < minDeg w := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun u _ => hy u)
    exact not_lt_of_ge (hw_max hw) hlt
  obtain ⟨f, sep, hfs, hft⟩ := geometric_hahn_banach_open hs_conv hs_open ht_conv hdisj
  let q : U → ℝ := fun u => - f (Pi.single u 1)
  have hf_eq : ∀ y : U → ℝ, f y = - ∑ u : U, q u * y u := by
    intro y
    have hy : y = ∑ u : U, y u • Pi.single u (1 : ℝ) := by
      funext v; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, q, neg_mul, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl (fun u _ => mul_comm _ _)
  have hqs : ∀ y ∈ s, -sep < ∑ u : U, q u * y u := fun y hy => by
    have h := hfs y hy; rw [hf_eq] at h; linarith
  have hqt : ∀ w ∈ stdSimplex ℝ U, ∑ u : U, q u * A w u ≤ -sep := fun w hw => by
    have h := hft (A w) ⟨w, hw, rfl⟩; rw [hf_eq] at h; linarith
  have hq_nn : ∀ u : U, 0 ≤ q u := by
    intro u
    by_contra hneg
    push Not at hneg
    let base : U → ℝ := fun _ => δ + 1
    let M : ℝ := max 1 ((∑ v : U, q v * base v + sep + 1) / (- q u))
    have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    let y : U → ℝ := base + M • Pi.single u 1
    have hy_s : y ∈ s := by
      intro v
      simp only [y, base, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> linarith
    have hlt := hqs y hy_s
    have hsum_y : ∑ v : U, q v * y v = (∑ v : U, q v * base v) + M * q u := by
      have h1 : ∀ v : U, q v * y v = q v * base v + (if v = u then M * q u else 0) := by
        intro v
        simp only [y, base, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        split_ifs with hvu
        · subst hvu; ring
        · ring
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hsum_y] at hlt
    have hM_ge : (∑ v : U, q v * base v + sep + 1) / (- q u) ≤ M := le_max_right _ _
    have hmq : ∑ v : U, q v * base v + sep + 1 ≤ M * (- q u) :=
      (div_le_iff₀ (by linarith)).mp hM_ge
    linarith
  have hq_sum_pos : 0 < ∑ u : U, q u := by
    by_contra hle
    push Not at hle
    have hq0 : ∀ u : U, q u = 0 := fun u =>
      le_antisymm (by
        have h1 := Finset.single_le_sum (fun v _ => hq_nn v) (Finset.mem_univ u)
        linarith) (hq_nn u)
    have h1 := hqs (fun _ => δ + 1) (fun _ => by linarith)
    have h2 := hqt w_star hw_mem
    simp [hq0] at h1 h2
    linarith
  let Q : ℝ := ∑ u : U, q u
  let p : U → ℝ := fun u => q u / Q
  have hp_nn : ∀ u : U, 0 ≤ p u := fun u => div_nonneg (hq_nn u) (le_of_lt hq_sum_pos)
  have hp_sum : ∑ u : U, p u = 1 := by
    simp only [p, ← Finset.sum_div]; exact div_self (ne_of_gt hq_sum_pos)
  have hsep_le : -sep ≤ Q * δ := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hε' : 0 < ε / Q := div_pos hε hq_sum_pos
    have hlt := hqs (fun _ => δ + ε / Q) (fun _ => by linarith)
    have hsum : ∑ u : U, q u * (δ + ε / Q) = Q * δ + ε := by
      rw [← Finset.sum_mul]
      change Q * (δ + ε / Q) = Q * δ + ε
      have hQne : Q ≠ 0 := ne_of_gt hq_sum_pos
      rw [mul_add, mul_div_cancel₀ _ hQne]
    linarith
  have hp_le : ∀ v : U, A p v ≤ δ := by
    intro v
    have hsingle : Pi.single v (1 : ℝ) ∈ stdSimplex ℝ U := by
      refine ⟨fun u => ?_, ?_⟩
      · simp only [Pi.single_apply]; split_ifs <;> norm_num
      · simp [Pi.single_apply]
    have h1 := (hqt (Pi.single v 1) hsingle).trans hsep_le
    have h2 : ∑ u : U, q u * A (Pi.single v 1) u = Q * A p v := by
      have hA_single : ∀ u : U, A (Pi.single v 1) u = if H.Adj u v then 1 else 0 := by
        intro u
        simp only [A, Pi.single_apply]
        rw [Finset.sum_eq_single v]
        · simp
        · intro b _ hbv; simp [hbv]
        · intro hv; exact (hv (Finset.mem_univ v)).elim
      simp_rw [hA_single]
      simp only [A, p, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases huv : H.Adj u v
      · have hvu : H.Adj v u := huv.symm
        simp only [huv, hvu, ite_true]
        have hQne : Q ≠ 0 := ne_of_gt hq_sum_pos
        rw [mul_one, mul_div_cancel₀ _ hQne]
      · have hvu : ¬ H.Adj v u := fun h => huv h.symm
        simp [huv, hvu]
    rw [h2] at h1
    nlinarith
  -- Complementary slackness via symmetry of A
  have hsymm : ∑ u : U, p u * A w_star u = ∑ v : U, w_star v * A p v := by
    simp only [A, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
    by_cases huv : H.Adj u v
    · simp [huv, huv.symm]; ring
    · have hvu : ¬ H.Adj v u := fun h => huv h.symm
      simp [huv, hvu]
  have hlo : δ ≤ ∑ u : U, p u * A w_star u := by
    calc δ = ∑ u : U, p u * δ := by rw [← Finset.sum_mul, hp_sum, one_mul]
      _ ≤ ∑ u : U, p u * A w_star u := Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hw_deg u) (hp_nn u))
  have hhi : ∑ v : U, w_star v * (δ - A p v) = 0 := by
    have h1 : ∑ v : U, w_star v * (δ - A p v) = δ - ∑ v : U, w_star v * A p v := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw_mem.2, one_mul]
    have h2 : 0 ≤ ∑ v : U, w_star v * (δ - A p v) :=
      Finset.sum_nonneg (fun v _ => mul_nonneg (hw_mem.1 v) (sub_nonneg.mpr (hp_le v)))
    linarith
  have hp_reg : ∀ v : U, A p v = δ := by
    intro v
    have hterm0 : w_star v * (δ - A p v) = 0 := by
      have hle := Finset.single_le_sum
        (f := fun u : U => w_star u * (δ - A p u))
        (fun u _ => mul_nonneg (hw_mem.1 u) (sub_nonneg.mpr (hp_le u)))
        (Finset.mem_univ v)
      have hnn : 0 ≤ w_star v * (δ - A p v) := mul_nonneg (hw_mem.1 v) (sub_nonneg.mpr (hp_le v))
      linarith
    rcases mul_eq_zero.mp hterm0 with h0 | h0
    · linarith [hw_pos v]
    · linarith
  by_cases hp_zero : ∃ x : U, p x = 0
  · exact Or.inr ⟨p, hp_nn, hp_sum, hp_zero, fun u => by change c < A p u; rw [hp_reg u]; exact hδ_gt⟩
  · have hp_pos : ∀ u : U, 0 < p u := fun u =>
      lt_of_le_of_ne (hp_nn u) (Ne.symm (fun h => hp_zero ⟨u, h⟩))
    exact Or.inl ⟨p, δ, hp_pos, hp_sum, hδ_gt, hp_reg⟩

end Erdos128ThmJ

namespace Erdos128Vega

/-- Vertex type for the ambient full Vega graph `Upsilon_i`: `Gamma_i = Fin (3*i - 1)` plus `Q_3^+ = Fin 8`
    (`0=x, 1=y, 2=a, 3=b, 4=c, 5=u, 6=v, 7=w`). -/
abbrev VegaV (i : ℕ) : Type := Fin (3 * i - 1) ⊕ Fin 8

/-- Active vertices of the 4 Vega variants: `dy` deletes `y` (`inr 1`), `de` deletes `2*i - 1` (`inl (2*i-1)`). -/
def vegaActive (i : ℕ) (dy de : Bool) : VegaV i → Prop
  | Sum.inl k => ¬ (de = true ∧ k.val = 2 * i - 1)
  | Sum.inr j => ¬ (dy = true ∧ j.val = 1)

instance (i : ℕ) (dy de : Bool) : DecidablePred (vegaActive i dy de) := fun v => by
  cases v with
  | inl k => unfold vegaActive; infer_instance
  | inr j => unfold vegaActive; infer_instance

/-- Adjacency relation of the full Vega graph `Upsilon_i` (`i >= 2`). -/
def vegaAdj (i : ℕ) : VegaV i → VegaV i → Prop
  | Sum.inl p, Sum.inl q =>
      let N := 3 * i - 1
      let d := (q.val + N - p.val) % N
      i ≤ d ∧ d ≤ 2 * i - 1
  | Sum.inl p, Sum.inr q =>
      (p.val < i ∧ (q.val = 2 ∨ q.val = 5)) ∨
      (i ≤ p.val ∧ p.val < 2 * i ∧ (q.val = 3 ∨ q.val = 6)) ∨
      (2 * i ≤ p.val ∧ (q.val = 4 ∨ q.val = 7))
  | Sum.inr q, Sum.inl p =>
      (p.val < i ∧ (q.val = 2 ∨ q.val = 5)) ∨
      (i ≤ p.val ∧ p.val < 2 * i ∧ (q.val = 3 ∨ q.val = 6)) ∨
      (2 * i ≤ p.val ∧ (q.val = 4 ∨ q.val = 7))
  | Sum.inr p, Sum.inr q =>
      (p.val = 0 ∧ (q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 4)) ∨
      (q.val = 0 ∧ (p.val = 1 ∨ p.val = 2 ∨ p.val = 3 ∨ p.val = 4)) ∨
      (p.val = 1 ∧ (q.val = 5 ∨ q.val = 6 ∨ q.val = 7)) ∨
      (q.val = 1 ∧ (p.val = 5 ∨ p.val = 6 ∨ p.val = 7)) ∨
      (p.val = 2 ∧ (q.val = 6 ∨ q.val = 7)) ∨ (q.val = 2 ∧ (p.val = 6 ∨ p.val = 7)) ∨
      (p.val = 3 ∧ (q.val = 5 ∨ q.val = 7)) ∨ (q.val = 3 ∧ (p.val = 5 ∨ p.val = 7)) ∨
      (p.val = 4 ∧ (q.val = 5 ∨ q.val = 6)) ∨ (q.val = 4 ∧ (p.val = 5 ∨ p.val = 6))

instance (i : ℕ) : DecidableRel (vegaAdj i) := fun u v => by
  cases u <;> cases v <;> unfold vegaAdj <;> infer_instance

lemma vegaAdj_symm {i : ℕ} (hi : 2 ≤ i) {u v : VegaV i} (h : vegaAdj i u v) : vegaAdj i v u := by
  cases u with
  | inl p =>
    cases v with
    | inl q =>
      simp only [vegaAdj] at h ⊢
      have hp := p.isLt; have hq := q.isLt
      have hN : 0 < 3 * i - 1 := by omega
      by_cases hpq : p.val ≤ q.val
      · have h1 : (q.val + (3 * i - 1) - p.val) % (3 * i - 1) = q.val - p.val := by
          have : q.val + (3 * i - 1) - p.val = (q.val - p.val) + (3 * i - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1] at h
        have hlt : p.val < q.val := by omega
        have h2 : (p.val + (3 * i - 1) - q.val) % (3 * i - 1) = (3 * i - 1) - (q.val - p.val) := by
          have : p.val + (3 * i - 1) - q.val = (3 * i - 1) - (q.val - p.val) := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
        rw [h2]; omega
      · have h1 : (q.val + (3 * i - 1) - p.val) % (3 * i - 1) = (3 * i - 1) - (p.val - q.val) := by
          have : q.val + (3 * i - 1) - p.val = (3 * i - 1) - (p.val - q.val) := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
        rw [h1] at h
        have h2 : (p.val + (3 * i - 1) - q.val) % (3 * i - 1) = p.val - q.val := by
          have : p.val + (3 * i - 1) - q.val = (p.val - q.val) + (3 * i - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h2]; omega
    | inr q => exact h
  | inr p =>
    cases v with
    | inl q => exact h
    | inr q =>
      fin_cases p <;> fin_cases q <;> simp_all [vegaAdj]

lemma vegaAdj_irrefl {i : ℕ} (hi : 2 ≤ i) (u : VegaV i) : ¬ vegaAdj i u u := by
  cases u with
  | inl p =>
    simp only [vegaAdj]
    have hp := p.isLt
    have h1 : (p.val + (3 * i - 1) - p.val) % (3 * i - 1) = 0 := by
      have : p.val + (3 * i - 1) - p.val = 3 * i - 1 := by omega
      rw [this, Nat.mod_self]
    rw [h1]; omega
  | inr p =>
    fin_cases p <;> simp [vegaAdj]

lemma vegaAdj_gamma_triangleFree {i : ℕ} (hi : 2 ≤ i) {p q r : Fin (3 * i - 1)}
    (hpq : vegaAdj i (.inl p) (.inl q))
    (hqr : vegaAdj i (.inl q) (.inl r))
    (hrp : vegaAdj i (.inl r) (.inl p)) : False := by
  simp only [vegaAdj] at hpq hqr hrp
  have hp := p.isLt; have hq := q.isLt; have hr := r.isLt
  let N := 3 * i - 1
  let d1 := (q.val + N - p.val) % N
  let d2 := (r.val + N - q.val) % N
  let d3 := (p.val + N - r.val) % N
  have hd1 : i ≤ d1 ∧ d1 ≤ 2 * i - 1 := hpq
  have hd2 : i ≤ d2 ∧ d2 ≤ 2 * i - 1 := hqr
  have hd3 : i ≤ d3 ∧ d3 ≤ 2 * i - 1 := hrp
  have hmod : (d1 + d2 + d3) % N = 0 := by
    have hsum : (q.val + N - p.val) + (r.val + N - q.val) + (p.val + N - r.val) = 3 * N := by omega
    have h1 : (d1 + d2 + d3) % N = ((q.val + N - p.val) + (r.val + N - q.val) + (p.val + N - r.val)) % N := by
      simp only [d1, d2, d3, Nat.add_mod, Nat.mod_mod]
    rw [h1, hsum, Nat.mul_mod_left]
  have h1 : N < d1 + d2 + d3 := by omega
  have h2 : d1 + d2 + d3 < 2 * N := by omega
  have h3 : (d1 + d2 + d3) % N = d1 + d2 + d3 - N := by
    have : d1 + d2 + d3 = (d1 + d2 + d3 - N) + N := by omega
    conv_lhs => rw [this]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A graph `H` on `U` belongs to the 4-variant closed Vega class `V_i(dy, de)`. -/
def IsVegaGraph {U : Type} (H : SimpleGraph U) (i : ℕ) (dy de : Bool) : Prop :=
  2 ≤ i ∧ ∃ e : U ≃ {v : VegaV i // vegaActive i dy de v},
    ∀ u v : U, H.Adj u v ↔ vegaAdj i (e u).1 (e v).1


lemma fin3_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> decide
lemma fin8_cases (q : Fin 8) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by fin_cases q <;> decide

end Erdos128Vega

namespace Erdos128J2

open Finset SimpleGraph Erdos128ThmJ Erdos128Vega

/- ## Section 0: Good Graphs & Weighted Double-Counting Primitives -/

structure IsGood {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] where
  hTF : H.CliqueFree 3
  hMax : ∀ x y : U, x ≠ y → ¬ H.Adj x y → ∃ z : U, H.Adj x z ∧ H.Adj y z
  hTwin : ∀ x y : U, (∀ z : U, H.Adj x z ↔ H.Adj y z) → x = y
  hNot3 : ¬ H.Colorable 3
  w0 : U → ℝ
  hw0_nn : ∀ x : U, 0 ≤ w0 x
  hw0_sum : ∑ x : U, w0 x = 1
  hw0_deg : ∀ x : U, (1 / 3 : ℝ) < ∑ y : U, if H.Adj x y then w0 y else 0

def wsum {U : Type} (ω : U → ℝ) (S : Finset U) : ℝ := ∑ u ∈ S, ω u

def wdeg {U : Type} [Fintype U] (H : SimpleGraph U) [DecidableRel H.Adj] (ω : U → ℝ) (u : U) : ℝ :=
  ∑ v : U, if H.Adj u v then ω v else 0

lemma tf_contra {U : Type} {H : SimpleGraph U} (hTF : H.CliqueFree 3) {a b c : U}
    (hab : H.Adj a b) (hbc : H.Adj b c) (hac : H.Adj a c) : False :=
  OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hTF hab hbc hac

lemma sum_wdeg_eq_sum_hits {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (ω : U → ℝ) (S : Finset U) :
    ∑ u ∈ S, wdeg H ω u = ∑ v : U, (#(S.filter (H.Adj v)) : ℝ) * ω v := by
  simp only [wdeg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v _
  have h1 : ∑ u ∈ S, (if H.Adj u v then ω v else 0) = ∑ u ∈ S, if H.Adj v u then ω v else 0 := by
    apply Finset.sum_congr rfl; intro u _; simp [H.adj_comm]
  rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

lemma contra_of_capped_set {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] {ω : U → ℝ}
    (hnn : ∀ v : U, 0 ≤ ω v) (hsum : ∑ v : U, ω v = 1)
    (hdeg : ∀ u : U, (1 / 3 : ℝ) < wdeg H ω u)
    (S : Finset U) (k : ℕ) (hS_ne : S.Nonempty) (h3k : 3 * k ≤ #S)
    (hcap : ∀ v : U, #(S.filter (H.Adj v)) ≤ k) : False := by
  have hgt : (#S : ℝ) * (1 / 3 : ℝ) < ∑ u ∈ S, wdeg H ω u := by
    calc (#S : ℝ) * (1 / 3 : ℝ) = ∑ _u ∈ S, (1 / 3 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ < ∑ u ∈ S, wdeg H ω u := Finset.sum_lt_sum_of_nonempty hS_ne (fun u _ => hdeg u)
  have hle : ∑ u ∈ S, wdeg H ω u ≤ (k : ℝ) := by
    rw [sum_wdeg_eq_sum_hits]
    calc ∑ v : U, (#(S.filter (H.Adj v)) : ℝ) * ω v
        ≤ ∑ v : U, (k : ℝ) * ω v :=
          Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcap v)) (hnn v))
      _ = (k : ℝ) * ∑ v : U, ω v := (Finset.mul_sum _ _ _).symm
      _ = (k : ℝ) := by rw [hsum, mul_one]
  have h3k_R : 3 * (k : ℝ) ≤ (#S : ℝ) := by exact_mod_cast h3k
  linarith

/-- Lemma 3 (No Undominated 6-Cycle, valid for ANY weight with `deg_w > 1/3`):
    For any 6 pairwise distinct vertices `c : Fin 6 -> U` with `c k ~ c (k + 1)`,
    some `v : U` dominates either `{c 0, c 2, c 4}` or `{c 1, c 3, c 5}`! -/
lemma exists_dom3_of_c6 {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (hTF : H.CliqueFree 3)
    {ω : U → ℝ} (hnn : ∀ v : U, 0 ≤ ω v) (hsum : ∑ v : U, ω v = 1)
    (hdeg : ∀ u : U, (1 / 3 : ℝ) < wdeg H ω u)
    (c : Fin 6 → U) (hinj : Function.Injective c)
    (he01 : H.Adj (c 0) (c 1)) (he12 : H.Adj (c 1) (c 2)) (he23 : H.Adj (c 2) (c 3))
    (he34 : H.Adj (c 3) (c 4)) (he45 : H.Adj (c 4) (c 5)) (he50 : H.Adj (c 5) (c 0)) :
    ∃ v : U, (H.Adj v (c 0) ∧ H.Adj v (c 2) ∧ H.Adj v (c 4)) ∨
             (H.Adj v (c 1) ∧ H.Adj v (c 3) ∧ H.Adj v (c 5)) := by
  by_contra hno; push Not at hno
  let S : Finset U := Finset.univ.image c
  have hScard : #S = 6 := by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcap : ∀ v : U, #(S.filter (H.Adj v)) ≤ 2 := by
    intro v
    have hbij : #(S.filter (H.Adj v)) = #(Finset.univ.filter (fun k : Fin 6 => H.Adj v (c k))) := by
      refine Finset.card_bij (fun u _ => (Finset.mem_image.mp (Finset.mem_filter.mp (by assumption : u ∈ S.filter (H.Adj v))).1).choose) ?_ ?_ ?_
      · intro u hu
        have hu1 := (Finset.mem_filter.mp hu).1
        have hu2 := (Finset.mem_filter.mp hu).2
        have hspec := (Finset.mem_image.mp hu1).choose_spec.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hspec.symm ▸ hu2⟩
      · intro u1 hu1 u2 hu2 heq
        have h1 := (Finset.mem_image.mp (Finset.mem_filter.mp hu1).1).choose_spec.2
        have h2 := (Finset.mem_image.mp (Finset.mem_filter.mp hu2).1).choose_spec.2
        rw [← h1, ← h2, heq]
      · intro k hk
        have hkv := (Finset.mem_filter.mp hk).2
        refine ⟨c k, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem c (Finset.mem_univ k), hkv⟩, ?_⟩
        exact hinj (Finset.mem_image.mp (Finset.mem_image_of_mem c (Finset.mem_univ k))).choose_spec.2
    rw [hbij, Finset.card_filter, Fin.sum_univ_six]
    let b : Fin 6 → ℕ := fun k => if H.Adj v (c k) then 1 else 0
    change b 0 + b 1 + b 2 + b 3 + b 4 + b 5 ≤ 2
    have hna : ∀ {j k : Fin 6}, H.Adj (c j) (c k) → b j + b k ≤ 1 := by
      intro j k hjk; dsimp only [b]
      by_cases hj : H.Adj v (c j) <;> by_cases hk : H.Adj v (c k)
      · exact (tf_contra hTF hj hjk hk).elim
      all_goals simp [hj, hk]
    have h01 := hna he01; have h12 := hna he12; have h23 := hna he23
    have h34 := hna he34; have h45 := hna he45; have h50 := hna he50
    obtain ⟨hE, hO⟩ := hno v
    have hbe : b 0 + b 2 + b 4 ≤ 2 := by
      dsimp only [b]; by_cases h0 : H.Adj v (c 0) <;> by_cases h2 : H.Adj v (c 2) <;> by_cases h4 : H.Adj v (c 4)
      · exact (hE h0 h2 h4).elim
      all_goals simp [h0, h2, h4]
    have hbo : b 1 + b 3 + b 5 ≤ 2 := by
      dsimp only [b]; by_cases h1 : H.Adj v (c 1) <;> by_cases h3 : H.Adj v (c 3) <;> by_cases h5 : H.Adj v (c 5)
      · exact (hO h1 h3 h5).elim
      all_goals simp [h1, h3, h5]
    omega
  exact contra_of_capped_set H hnn hsum hdeg S 2 ⟨c 0, Finset.mem_image_of_mem c (Finset.mem_univ 0)⟩ (by omega) hcap

/- ## Section A: Step 14 (Ferrers Tripartite Classification) & Andrasfai Independent Arcs -/

/-- Cyclic arc lemma for `And(d)` (`d >= 2`): every independent set `S ⊆ Fin (3*d - 1)` lies in
    a cyclic arc of length `d` (`∃ s0 : Fin (3*d - 1), ∀ u ∈ S, (u + N - s0) % N < d`). -/
lemma arc_of_indep_andrasfai {d : ℕ} (hd : 2 ≤ d) (S : Finset (Fin (3 * d - 1)))
    (hInd : ∀ u ∈ S, ∀ v ∈ S, ¬ vegaAdj d (.inl u) (.inl v)) :
    ∃ s0 : Fin (3 * d - 1), ∀ u ∈ S, (u.val + (3 * d - 1) - s0.val) % (3 * d - 1) < d := by
  let N := 3 * d - 1
  have hN : 5 ≤ N := by omega
  by_cases hEmpty : S = ∅
  · exact ⟨⟨0, by omega⟩, fun u hu => (hEmpty ▸ hu |> Finset.notMem_empty u).elim⟩
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨u, huS⟩ := hSne
  let dist : Fin N → Fin N → ℕ := fun a b => (b.val + N - a.val) % N
  have hdist_lt : ∀ a b : Fin N, dist a b < N := fun a b => Nat.mod_lt _ (by omega)
  have hdist_not_adj : ∀ a ∈ S, ∀ b ∈ S, dist a b < d ∨ 2 * d ≤ dist a b := by
    intro a ha b hb
    have hna := hInd a ha b hb
    simp only [vegaAdj] at hna
    have := hdist_lt a b
    change ¬ (d ≤ dist a b ∧ dist a b ≤ 2 * d - 1) at hna
    omega
  -- Partition S into A = {x ∈ S | dist u x < d} and B = {x ∈ S | 2*d <= dist u x}
  let A := S.filter (fun x => dist u x < d)
  let B := S.filter (fun x => 2 * d ≤ dist u x)
  have huA : u ∈ A := by
    refine Finset.mem_filter.mpr ⟨huS, ?_⟩
    have hu_lt := u.isLt
    have : dist u u = 0 := by
      dsimp only [dist]; rw [show u.val + N - u.val = N by omega, Nat.mod_self]
    omega
  by_cases hB : B = ∅
  · refine ⟨u, fun x hx => ?_⟩
    rcases hdist_not_adj u huS x hx with hlt | hge
    · exact hlt
    · exfalso; exact Finset.notMem_empty x (hB ▸ Finset.mem_filter.mpr ⟨hx, hge⟩)
  · have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
    obtain ⟨w, hwB, hw_min⟩ := Finset.exists_min_image B (fun x => dist u x) hBne
    have hwS : w ∈ S := (Finset.mem_filter.mp hwB).1
    have hdw_ge : 2 * d ≤ dist u w := (Finset.mem_filter.mp hwB).2
    have hdw_lt : dist u w < N := hdist_lt u w
    -- Helper: cyclic distance additivity mod N
    have hdist_tri : ∀ a b : Fin N,
        dist w b = (if dist u w ≤ dist u b then dist u b - dist u w else dist u b + N - dist u w) := by
      intro a b
      have hu_lt := u.isLt; have hw_lt := w.isLt; have hb_lt := b.isLt
      have hsub_mod : ∀ x y : ℕ, x < N → y < N →
          ((y + N - x) % N) = if x ≤ y then y - x else y + N - x := by
        intro x y hx hy; split_ifs with hxy
        · rw [show y + N - x = (y - x) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · exact Nat.mod_eq_of_lt (by omega)
      have hdw_eq := hsub_mod u.val w.val hu_lt hw_lt
      have hdb_eq := hsub_mod u.val b.val hu_lt hb_lt
      have hwb_eq := hsub_mod w.val b.val hw_lt hb_lt
      dsimp only [dist] at hdw_eq hdb_eq hwb_eq ⊢
      split_ifs at hdw_eq hdb_eq hwb_eq ⊢ <;> omega
    refine ⟨w, fun x hx => ?_⟩
    rcases hdist_not_adj u huS x hx with hxA | hxB
    · have hwx : dist w x = dist u x + N - dist u w := by
        rw [hdist_tri u x, if_neg (by omega)]
      have hna := hdist_not_adj w hwS x hx
      change dist w x < d; omega
    · have hxB_mem : x ∈ B := Finset.mem_filter.mpr ⟨hx, hxB⟩
      have hwx_le : dist u w ≤ dist u x := hw_min x hxB_mem
      have hwx : dist w x = dist u x - dist u w := by rw [hdist_tri u x, if_pos hwx_le]
      have hdx_lt : dist u x < N := hdist_lt u x
      change dist w x < d; omega

/-- Exact ordered Ferrers classification on `1 <= a <= b <= c`:
    returns the exact 3 isomorphism shapes `And(i)`, `And(i) - {2i-1}`, or `And(d+1) - {d, 2d+1}`! -/
lemma ferrers_ordered_exact {a b c : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (f : Fin a → ℕ) (g : Fin b → ℕ) (h : Fin c → ℕ)
    (hf_le : ∀ i, f i ≤ b) (hg_le : ∀ j, g j ≤ c) (hh_le : ∀ k, h k ≤ a)
    (hf_sm : ∀ i₁ i₂, i₁ < i₂ → f i₁ < f i₂)
    (hg_sm : ∀ j₁ j₂, j₁ < j₂ → g j₁ < g j₂)
    (hh_sm : ∀ k₁ k₂, k₁ < k₂ → h k₁ < h k₂)
    (hTF : ∀ (i : Fin a) (j : Fin b) (k : Fin c), ¬ (f i ≤ j.val ∧ g j ≤ k.val ∧ h k ≤ i.val))
    (hmaxXY : ∀ (i : Fin a) (j : Fin b), j.val < f i → ∃ k : Fin c, g j ≤ k.val ∧ h k ≤ i.val)
    (hmaxYZ : ∀ (j : Fin b) (k : Fin c), k.val < g j → ∃ i : Fin a, f i ≤ j.val ∧ h k ≤ i.val)
    (hmaxZX : ∀ (k : Fin c) (i : Fin a), i.val < h k → ∃ j : Fin b, f i ≤ j.val ∧ g j ≤ k.val) :
    -- Case 1: And(c) with (a,b,c) = (c-1, c, c) -> (X -> I3, Y -> I1, Z -> I2)
    (a = c - 1 ∧ b = c ∧ 2 ≤ c ∧
      (∀ i : Fin a, f i = i.val + 1) ∧ (∀ j : Fin b, g j = j.val) ∧ (∀ k : Fin c, h k = k.val)) ∨
    -- Case 2: And(c) - {2c-1} with (a,b,c) = (c-1, c-1, c) -> (Z -> I1, X -> I2\{2c-1}, Y -> I3)
    (a = c - 1 ∧ b = c - 1 ∧ 2 ≤ c ∧
      (∀ i : Fin a, f i = i.val) ∧ (∀ j : Fin b, g j = j.val + 1) ∧ (∀ k : Fin c, h k = k.val)) ∨
    -- Case 3: And(c+1) - 2 ends with (a,b,c) = (c, c, c) (one cyclic shift has f=id, g=id, h=succ)
    (a = c ∧ b = c ∧
      ((∀ i : Fin a, f i = i.val) ∧ (∀ j : Fin b, g j = j.val) ∧ (∀ k : Fin c, h k = k.val + 1) ∨
       (∀ i : Fin a, f i = i.val + 1) ∧ (∀ j : Fin b, g j = j.val) ∧ (∀ k : Fin c, h k = k.val) ∨
       (∀ i : Fin a, f i = i.val) ∧ (∀ j : Fin b, g j = j.val + 1) ∧ (∀ k : Fin c, h k = k.val))) := by
  have hc_le : c ≤ a + 1 := by
    have h1 := OMA.R_Erdos128_erdos_128_R2.strictMono_fin_tight h hh_sm ⟨c - 1, by omega⟩
    have h2 := hh_le ⟨c - 1, by omega⟩
    dsimp only at h1; omega
  by_cases hac : a = c
  · right; right
    have hbd : b = c := by omega
    refine ⟨hac, hbd, ?_⟩
    have hge1 : 1 ≤ f ⟨0, by omega⟩ ∨ 1 ≤ g ⟨0, by omega⟩ ∨ 1 ≤ h ⟨0, by omega⟩ := by
      have h0 := hTF ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
      dsimp only at h0; omega
    have hDDD : ∀ (a' b' c' : ℕ) (_ : a' = c') (_ : b' = c') (_ : 1 ≤ c')
        (f' : Fin a' → ℕ) (g' : Fin b' → ℕ) (h' : Fin c' → ℕ)
        (_ : ∀ i, f' i ≤ b') (_ : ∀ j, g' j ≤ c') (_ : ∀ k, h' k ≤ a')
        (_ : ∀ i₁ i₂, i₁ < i₂ → f' i₁ < f' i₂)
        (_ : ∀ j₁ j₂, j₁ < j₂ → g' j₁ < g' j₂)
        (_ : ∀ k₁ k₂, k₁ < k₂ → h' k₁ < h' k₂)
        (_ : ∀ j k, k.val < g' j → ∃ i, f' i ≤ j.val ∧ h' k ≤ i.val)
        (_ : ∀ k i, i.val < h' k → ∃ j, f' i ≤ j.val ∧ g' j ≤ k.val)
        (_ : 1 ≤ h' ⟨0, by omega⟩),
        (∀ i : Fin a', f' i = i.val) ∧ (∀ j : Fin b', g' j = j.val) ∧ (∀ k : Fin c', h' k = k.val + 1) := by
      intro a' b' c' h1 h2 hc' f' g' h' _ _ hh'l hf's hg's hh's hmYZ' hmZX' hh0
      have hh_all1 : ∀ k : Fin c', 1 ≤ h' k := by
        intro k; by_cases hk0 : k.val = 0
        · have : k = ⟨0, by omega⟩ := Fin.ext hk0; rw [this]; exact hh0
        · have := hh's ⟨0, by omega⟩ k (Fin.lt_def.mpr (by dsimp only; omega)); omega
      have hh_eq : ∀ k : Fin c', h' k = k.val + 1 :=
        OMA.R_Erdos128_erdos_128_R2.strictMono_fin_eq_succ h' hh's hh_all1 (fun k => by have := hh'l k; omega)
      have hg_lt : ∀ j : Fin b', g' j < c' := by
        intro j; by_contra hge
        obtain ⟨i, _, hi⟩ := hmYZ' j ⟨c' - 1, by omega⟩ (by dsimp only; omega)
        have hlast := hh_eq ⟨c' - 1, by omega⟩; dsimp only at hlast; omega
      have hg_eq : ∀ j : Fin b', g' j = j.val :=
        OMA.R_Erdos128_erdos_128_R2.strictMono_fin_eq_id g' hg's (fun j => by have := hg_lt j; omega)
      have hf_lt : ∀ i : Fin a', f' i < b' := by
        intro i; by_contra hge
        have hlast := hh_eq ⟨c' - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j, hj, _⟩ := hmZX' ⟨c' - 1, by omega⟩ i (by omega)
        omega
      have hf_eq : ∀ i : Fin a', f' i = i.val :=
        OMA.R_Erdos128_erdos_128_R2.strictMono_fin_eq_id f' hf's (fun i => by have := hf_lt i; omega)
      exact ⟨hf_eq, hg_eq, hh_eq⟩
    rcases hge1 with hf0 | hg0 | hh0
    · right; left
      have ⟨h1, h2, h3⟩ := hDDD b c a (by omega) (by omega) (by omega) g h f hg_le hh_le hf_le hg_sm hh_sm hf_sm
        (fun k i hlt => by obtain ⟨j, q1, q2⟩ := hmaxZX k i hlt; exact ⟨j, q2, q1⟩) hmaxXY hf0
      exact ⟨h3, h1, h2⟩
    · right; right
      have ⟨h1, h2, h3⟩ := hDDD c a b (by omega) (by omega) (by omega) h f g hh_le hf_le hg_le hh_sm hf_sm hg_sm
        (fun i j hlt => by obtain ⟨k, q1, q2⟩ := hmaxXY i j hlt; exact ⟨k, q2, q1⟩)
        (fun j k hlt => by obtain ⟨i, q1, q2⟩ := hmaxYZ j k hlt; exact ⟨i, q2, q1⟩) hg0
      exact ⟨h2, h3, h1⟩
    · left
      exact hDDD a b c hac hbd (by omega) f g h hf_le hg_le hh_le hf_sm hg_sm hh_sm hmaxYZ hmaxZX hh0
  · have ha_eq : a = c - 1 := by omega
    have hc2 : 2 ≤ c := by omega
    have hh_eq : ∀ k : Fin c, h k = k.val :=
      OMA.R_Erdos128_erdos_128_R2.strictMono_fin_eq_id h hh_sm (fun k => by have := hh_le k; omega)
    have hg_lt : ∀ j : Fin b, g j < c := by
      intro j; by_contra hge
      obtain ⟨i, _, hi⟩ := hmaxYZ j ⟨c - 1, by omega⟩ (by dsimp only; omega)
      have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast; omega
    by_cases hbc_eq : b = c
    · left
      have hg_eq : ∀ j : Fin b, g j = j.val :=
        OMA.R_Erdos128_erdos_128_R2.strictMono_fin_eq_id g hg_sm (fun j => by have := hg_lt j; omega)
      have hf_pos : ∀ i : Fin a, 1 ≤ f i := by
        intro i; by_contra h0
        have hg0 := hg_eq ⟨0, by omega⟩; have hh0 := hh_eq ⟨0, by omega⟩
        dsimp only at hg0 hh0
        exact hTF i ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨by omega, by omega, by omega⟩
      have hf_lt : ∀ i : Fin a, f i ≤ a := by
        intro i; by_contra hgt
        have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j, hj, _⟩ := hmaxZX ⟨c - 1, by omega⟩ i (by omega)
        omega
      have hf_eq : ∀ i : Fin a, f i = i.val + 1 :=
        OMA.R_Erdos128_erdos_128_R2.strictMono_fin_eq_succ f hf_sm hf_pos hf_lt
      exact ⟨ha_eq, hbc_eq, hc2, hf_eq, hg_eq, hh_eq⟩
    · right; left
      have hb_eq : b = c - 1 := by omega
      have hg_pos : ∀ j : Fin b, 1 ≤ g j := by
        intro j; by_contra h0
        have hg0 : g ⟨0, by omega⟩ = 0 := by
          by_cases hj0 : j.val = 0
          · have : j = ⟨0, by omega⟩ := Fin.ext hj0; rw [← this]; omega
          · have := hg_sm ⟨0, by omega⟩ j (Fin.lt_def.mpr (by dsimp only; omega)); omega
        have hf_all1 : ∀ i : Fin a, 1 ≤ f i := by
          intro i; by_contra hfi0
          have hh0 := hh_eq ⟨0, by omega⟩; dsimp only at hh0
          exact hTF i ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨by omega, by omega, by omega⟩
        have hf_eq1 : ∀ i : Fin a, f i = i.val + 1 :=
          OMA.R_Erdos128_erdos_128_R2.strictMono_fin_eq_succ f hf_sm hf_all1 (fun i => by have := hf_le i; omega)
        have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j', hj', _⟩ := hmaxZX ⟨c - 1, by omega⟩ ⟨a - 1, by omega⟩ (by dsimp only; omega)
        have hfa := hf_eq1 ⟨a - 1, by omega⟩; dsimp only at hfa; omega
      have hg_eq : ∀ j : Fin b, g j = j.val + 1 :=
        OMA.R_Erdos128_erdos_128_R2.strictMono_fin_eq_succ g hg_sm hg_pos (fun j => by have := hg_lt j; omega)
      have hf_lt : ∀ i : Fin a, f i < b := by
        intro i; by_contra hge
        have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j, hj, _⟩ := hmaxZX ⟨c - 1, by omega⟩ i (by omega)
        omega
      have hf_eq : ∀ i : Fin a, f i = i.val :=
        OMA.R_Erdos128_erdos_128_R2.strictMono_fin_eq_id f hf_sm (fun i => by have := hf_lt i; omega)
      exact ⟨ha_eq, hb_eq, hc2, hf_eq, hg_eq, hh_eq⟩

/-- **Step 14 (Universal Ferrers Tripartite Classification):**
    Any finite triangle-free, cross-maximal-TF, within-part twin-free, pairwise induced-2K_2-free
    3-partite graph `col : U -> Fin 3` with all 3 parts nonempty is EITHER:
    - isomorphic to `And(i)` (`i >= 2`) with the 3 parts mapped via `π : Equiv.Perm (Fin 3)` to `(I_1, I_2, I_3)`, OR
    - isomorphic to `And(i) - {2i-1}` (`i >= 2`) with the 3 parts mapped via `π` to `(I_1, I_2\{2i-1}, I_3)`, OR
    - embeds as an induced subgraph of `And(d + 1)` (`d >= 1`) AND has two distinct parts `c1 ≠ c2`
      with `p0` (in `c1`) having NO edge to `c2` and `s_last` (in `c2`) having NO edge to `c1`! -/
theorem ferrers_tripartite_classify {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj]
    (col : U → Fin 3)
    (hTF : H.CliqueFree 3)
    (hcol : ∀ u v : U, H.Adj u v → col u ≠ col v)
    (hCrossMax : ∀ u v : U, col u ≠ col v → ¬ H.Adj u v → ∃ w : U, H.Adj u w ∧ H.Adj v w)
    (hTwinPart : ∀ u v : U, col u = col v → (∀ w : U, H.Adj u w ↔ H.Adj v w) → u = v)
    (hNo2K2 : ∀ c1 c2 : Fin 3, c1 ≠ c2 → ∀ x1 x2 y1 y2 : U,
      col x1 = c1 → col x2 = c1 → col y1 = c2 → col y2 = c2 →
      H.Adj x1 y1 → H.Adj x2 y2 → ¬ H.Adj x1 y2 → ¬ H.Adj x2 y1 → False)
    (hNonempty : ∀ c : Fin 3, ∃ u : U, col u = c) :
    (∃ (i : ℕ) (_ : 2 ≤ i) (π : Equiv.Perm (Fin 3)) (e : U ≃ Fin (3 * i - 1)),
      (∀ u v : U, H.Adj u v ↔ vegaAdj i (.inl (e u)) (.inl (e v))) ∧
      (∀ u : U, (π (col u) = 0 ↔ (e u).val < i) ∧
                (π (col u) = 1 ↔ i ≤ (e u).val ∧ (e u).val < 2 * i) ∧
                (π (col u) = 2 ↔ 2 * i ≤ (e u).val))) ∨
    (∃ (i : ℕ) (_ : 2 ≤ i) (π : Equiv.Perm (Fin 3)) (e : U ≃ {p : Fin (3 * i - 1) // p.val ≠ 2 * i - 1}),
      (∀ u v : U, H.Adj u v ↔ vegaAdj i (.inl (e u).1) (.inl (e v).1)) ∧
      (∀ u : U, (π (col u) = 0 ↔ (e u).1.val < i) ∧
                (π (col u) = 1 ↔ i ≤ (e u).1.val ∧ (e u).1.val < 2 * i) ∧
                (π (col u) = 2 ↔ 2 * i ≤ (e u).1.val))) ∨
    (∃ (d : ℕ) (_ : 2 ≤ d) (φ : U → Fin (3 * d - 1)),
      Function.Injective φ ∧ (∀ u v : U, H.Adj u v ↔ vegaAdj d (.inl (φ u)) (.inl (φ v))) ∧
      ∃ (c1 c2 : Fin 3) (p0 s0 : U), c1 ≠ c2 ∧ col p0 = c1 ∧ col s0 = c2 ∧
        (∀ z : U, col z = c2 → ¬ H.Adj p0 z) ∧ (∀ x : U, col x = c1 → ¬ H.Adj s0 x)) := by
  let P : Fin 3 → Finset U := fun c => Finset.univ.filter (fun u => col u = c)
  have hP_ne : ∀ c : Fin 3, (P c).Nonempty := fun c => by
    obtain ⟨u, hu⟩ := hNonempty c; exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩
  have hnbhd_total : ∀ c1 c2 : Fin 3, c1 ≠ c2 → ∀ x1 ∈ P c1, ∀ x2 ∈ P c1,
      (P c2).filter (H.Adj x1) ⊆ (P c2).filter (H.Adj x2) ∨
      (P c2).filter (H.Adj x2) ⊆ (P c2).filter (H.Adj x1) := by
    intro c1 c2 hc12 x1 hx1 x2 hx2
    by_contra hnot; push Not at hnot
    obtain ⟨y1, hy1, hy1n⟩ := Finset.not_subset.mp hnot.1
    obtain ⟨y2, hy2, hy2n⟩ := Finset.not_subset.mp hnot.2
    have hy1' := Finset.mem_filter.mp hy1; have hy2' := Finset.mem_filter.mp hy2
    exact hNo2K2 c1 c2 hc12 x1 x2 y1 y2 (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2
      (Finset.mem_filter.mp hy1'.1).2 (Finset.mem_filter.mp hy2'.1).2 hy1'.2 hy2'.2
      (fun h => hy2n (Finset.mem_filter.mpr ⟨hy2'.1, h⟩))
      (fun h => hy1n (Finset.mem_filter.mpr ⟨hy1'.1, h⟩))
  have hnbhd_eq_iff : ∀ c1 c2 c3 : Fin 3, c1 ≠ c2 → c1 ≠ c3 → c2 ≠ c3 →
      ∀ x1 ∈ P c1, ∀ x2 ∈ P c1,
      (P c2).filter (H.Adj x1) = (P c2).filter (H.Adj x2) →
      (P c3).filter (H.Adj x1) = (P c3).filter (H.Adj x2) := by
    intro c1 c2 c3 h12 h13 h23 x1 hx1 x2 hx2 heq
    have hsub : ∀ u ∈ P c1, ∀ v ∈ P c1, (P c2).filter (H.Adj u) = (P c2).filter (H.Adj v) →
        (P c3).filter (H.Adj u) ⊆ (P c3).filter (H.Adj v) := by
      intro u hu v hv huv z hz
      have hz' := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr; refine ⟨hz'.1, ?_⟩
      by_contra hna
      have hcv : col v = c1 := (Finset.mem_filter.mp hv).2
      have hcz : col z = c3 := (Finset.mem_filter.mp hz'.1).2
      obtain ⟨y, hyv, hyz⟩ := hCrossMax v z (by rw [hcv, hcz]; exact h13) hna
      have hcy : col y = c2 :=
        OMA.R_Erdos128_erdos_128_R2.fin3_third h13 h12 h23.symm
          (by rw [← hcv]; exact (hcol v y hyv).symm) (by rw [← hcz]; exact (hcol z y hyz).symm)
      have hy_in : y ∈ (P c2).filter (H.Adj v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcy⟩, hyv⟩
      rw [← huv] at hy_in
      exact tf_contra hTF (Finset.mem_filter.mp hy_in).2 hyz.symm hz'.2
    exact Finset.Subset.antisymm (hsub x1 hx1 x2 hx2 heq) (hsub x2 hx2 x1 hx1 heq.symm)
  have hnbhd_opp : ∀ c1 c2 c3 : Fin 3, c1 ≠ c2 → c1 ≠ c3 → c2 ≠ c3 →
      ∀ x1 ∈ P c1, ∀ x2 ∈ P c1,
      (P c2).filter (H.Adj x2) ⊂ (P c2).filter (H.Adj x1) →
      (P c3).filter (H.Adj x1) ⊂ (P c3).filter (H.Adj x2) := by
    intro c1 c2 c3 h12 h13 h23 x1 hx1 x2 hx2 hssub
    have hsub3 : (P c3).filter (H.Adj x1) ⊆ (P c3).filter (H.Adj x2) := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr; refine ⟨hz'.1, ?_⟩
      by_contra hna
      obtain ⟨y, hy1, hy2⟩ := Finset.exists_of_ssubset hssub
      have hy1' := Finset.mem_filter.mp hy1
      have hna_y : ¬ H.Adj x2 y := fun h => hy2 (Finset.mem_filter.mpr ⟨hy1'.1, h⟩)
      have hcx2 : col x2 = c1 := (Finset.mem_filter.mp hx2).2
      have hcy : col y = c2 := (Finset.mem_filter.mp hy1'.1).2
      obtain ⟨z', hz'x2, hz'y⟩ := hCrossMax x2 y (by rw [hcx2, hcy]; exact h12) hna_y
      have hcz' : col z' = c3 :=
        OMA.R_Erdos128_erdos_128_R2.fin3_third h12 h13 h23
          (by rw [← hcx2]; exact (hcol x2 z' hz'x2).symm) (by rw [← hcy]; exact (hcol y z' hz'y).symm)
      have hna_z' : ¬ H.Adj x1 z' := fun h => tf_contra hTF hy1'.2 hz'y h
      exact hNo2K2 c1 c3 h13 x1 x2 z z' (Finset.mem_filter.mp hx1).2 hcx2
        (Finset.mem_filter.mp hz'.1).2 hcz' hz'.2 hz'x2 hna_z' hna
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hsub3, fun heq => (Finset.ssubset_iff_subset_ne.mp hssub).2
      (hnbhd_eq_iff c1 c3 c2 h13 h12 h23.symm x1 hx1 x2 hx2 heq).symm⟩
  -- Build exact bijective decreasing-degree orderings `rep c : Fin (sz c) ≃ {u // col u = c}`!
  let degNext : Fin 3 → U → ℕ := fun c x => #((P (c + 1)).filter (H.Adj x))
  have hsame_deg_eq : ∀ (c : Fin 3) (x1 x2 : U), x1 ∈ P c → x2 ∈ P c →
      degNext c x1 = degNext c x2 → x1 = x2 := by
    intro c x1 x2 hx1 hx2 hdeq
    apply hTwinPart x1 x2 ((Finset.mem_filter.mp hx1).2.trans (Finset.mem_filter.mp hx2).2.symm)
    intro w
    have hne1 : c ≠ c + 1 := by fin_cases c <;> decide
    have hne2 : c ≠ c + 2 := by fin_cases c <;> decide
    have hne12 : c + 1 ≠ c + 2 := by fin_cases c <;> decide
    have hN1 : (P (c + 1)).filter (H.Adj x1) = (P (c + 1)).filter (H.Adj x2) := by
      rcases hnbhd_total c (c + 1) hne1 x1 hx1 x2 hx2 with hsub | hsub
      · exact Finset.eq_of_subset_of_card_le hsub (by dsimp only [degNext] at hdeq; omega)
      · exact (Finset.eq_of_subset_of_card_le hsub (by dsimp only [degNext] at hdeq; omega)).symm
    have hN2 : (P (c + 2)).filter (H.Adj x1) = (P (c + 2)).filter (H.Adj x2) :=
      hnbhd_eq_iff c (c + 1) (c + 2) hne1 hne2 hne12 x1 hx1 x2 hx2 hN1
    have hcw : col w = c ∨ col w = c + 1 ∨ col w = c + 2 := by
      generalize col w = cw; fin_cases c <;> fin_cases cw <;> simp
    rcases hcw with hc | hc | hc
    · have h1 : ¬ H.Adj x1 w := fun h => hcol x1 w h ((Finset.mem_filter.mp hx1).2.trans hc.symm)
      have h2 : ¬ H.Adj x2 w := fun h => hcol x2 w h ((Finset.mem_filter.mp hx2).2.trans hc.symm)
      exact ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
    · have hwP : w ∈ P (c + 1) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have hiff := Finset.ext_iff.mp hN1 w; simp only [Finset.mem_filter, hwP, true_and] at hiff; exact hiff
    · have hwP : w ∈ P (c + 2) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have hiff := Finset.ext_iff.mp hN2 w; simp only [Finset.mem_filter, hwP, true_and] at hiff; exact hiff
  let degSet : Fin 3 → Finset ℕ := fun c => (P c).image (degNext c)
  let sz : Fin 3 → ℕ := fun c => #(degSet c)
  have hsz_pos : ∀ c : Fin 3, 1 ≤ sz c := fun c => Finset.card_pos.mpr ((hP_ne c).image _)
  let degVal : (c : Fin 3) → Fin (sz c) → ℕ := fun c i =>
    (Finset.orderIsoOfFin (degSet c) rfl ⟨sz c - 1 - i.val, by change sz c - 1 - i.val < sz c; have := i.isLt; omega⟩).val
  have hdegVal_mem : ∀ (c : Fin 3) (i : Fin (sz c)), degVal c i ∈ degSet c := fun c i =>
    (Finset.orderIsoOfFin (degSet c) rfl ⟨sz c - 1 - i.val, by change sz c - 1 - i.val < sz c; have := i.isLt; omega⟩).property
  have hdegVal_strict : ∀ (c : Fin 3) (i j : Fin (sz c)), i < j → degVal c j < degVal c i := by
    intro c i j hij
    have hi := i.isLt; have hj := j.isLt; have hlt' := Fin.lt_def.mp hij
    exact (Finset.orderIsoOfFin (degSet c) (rfl : #(degSet c) = sz c)).strictMono
      (Fin.lt_def.mpr (by dsimp only; omega))
  have hex_rep : ∀ (c : Fin 3) (i : Fin (sz c)), ∃ x ∈ P c, degNext c x = degVal c i :=
    fun c i => Finset.mem_image.mp (hdegVal_mem c i)
  let rep : (c : Fin 3) → Fin (sz c) → U := fun c i => (hex_rep c i).choose
  have hrep_mem : ∀ (c : Fin 3) (i : Fin (sz c)), rep c i ∈ P c := fun c i => (hex_rep c i).choose_spec.1
  have hrep_col : ∀ (c : Fin 3) (i : Fin (sz c)), col (rep c i) = c := fun c i => (Finset.mem_filter.mp (hrep_mem c i)).2
  have hrep_deg : ∀ (c : Fin 3) (i : Fin (sz c)), degNext c (rep c i) = degVal c i := fun c i => (hex_rep c i).choose_spec.2
  have hrep_inj : ∀ c : Fin 3, Function.Injective (rep c) := by
    intro c i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hdegVal_strict c i j hlt; rw [← hrep_deg, ← hrep_deg, hij] at this; omega
    · have := hdegVal_strict c j i hlt; rw [← hrep_deg, ← hrep_deg, hij] at this; omega
  have hex_idx : ∀ (c : Fin 3) (x : U), col x = c → ∃ i : Fin (sz c), rep c i = x := by
    intro c x hx
    have hxP : x ∈ P c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    have hmem : degNext c x ∈ degSet c := Finset.mem_image_of_mem _ hxP
    let j : Fin (sz c) := (Finset.orderIsoOfFin (degSet c) (rfl : #(degSet c) = sz c)).symm ⟨degNext c x, hmem⟩
    have hj := j.isLt
    let i : Fin (sz c) := ⟨sz c - 1 - j.val, by omega⟩
    have hdeq : degNext c (rep c i) = degNext c x := by
      rw [hrep_deg]
      dsimp only [degVal, i]
      have hsub : (⟨sz c - 1 - (sz c - 1 - j.val), by omega⟩ : Fin (sz c)) = j := Fin.ext (by dsimp only; omega)
      rw [hsub]
      exact congrArg Subtype.val ((Finset.orderIsoOfFin (degSet c) (rfl : #(degSet c) = sz c)).apply_symm_apply ⟨degNext c x, hmem⟩)
    exact ⟨i, hsame_deg_eq c (rep c i) x (hrep_mem c i) hxP hdeq⟩
  -- Monotonicity & threshold functions `thr c : Fin (sz c) -> ℕ`
  have hrep_adj_mono_right : ∀ (c : Fin 3) (j₁ j₂ : Fin (sz (c + 1))), j₁ < j₂ →
      ∀ (i : Fin (sz c)), H.Adj (rep c i) (rep (c + 1) j₁) → H.Adj (rep c i) (rep (c + 1) j₂) := by
    intro c j₁ j₂ hlt i hadj
    have hne1 : c + 1 ≠ c + 2 := by fin_cases c <;> decide
    have hne2 : c + 1 ≠ c := by fin_cases c <;> decide
    have hne3 : c + 2 ≠ c := by fin_cases c <;> decide
    have hdlt : degNext (c + 1) (rep (c + 1) j₂) < degNext (c + 1) (rep (c + 1) j₁) := by
      rw [hrep_deg, hrep_deg]; exact hdegVal_strict (c + 1) j₁ j₂ hlt
    have hssub : (P (c + 2)).filter (H.Adj (rep (c + 1) j₂)) ⊂ (P (c + 2)).filter (H.Adj (rep (c + 1) j₁)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, fun heq => by have := congrArg Finset.card heq; dsimp only [degNext] at hdlt; rw [show c + 1 + 1 = c + 2 by fin_cases c <;> decide] at hdlt; omega⟩
      rcases hnbhd_total (c + 1) (c + 2) hne1 (rep (c + 1) j₁) (hrep_mem _ j₁) (rep (c + 1) j₂) (hrep_mem _ j₂) with h | h
      · have := Finset.card_le_card h; dsimp only [degNext] at hdlt; rw [show c + 1 + 1 = c + 2 by fin_cases c <;> decide] at hdlt; omega
      · exact h
    have hopp := hnbhd_opp (c + 1) (c + 2) c hne1 hne2 hne3 (rep (c + 1) j₁) (hrep_mem _ j₁)
      (rep (c + 1) j₂) (hrep_mem _ j₂) hssub
    exact (Finset.mem_filter.mp (hopp.1 (Finset.mem_filter.mpr ⟨hrep_mem c i, hadj.symm⟩))).2.symm
  let thr : (c : Fin 3) → Fin (sz c) → ℕ := fun c i =>
    sz (c + 1) - #(Finset.univ.filter (fun j : Fin (sz (c + 1)) => H.Adj (rep c i) (rep (c + 1) j)))
  have hthr_iff : ∀ (c : Fin 3) (i : Fin (sz c)) (j : Fin (sz (c + 1))),
      H.Adj (rep c i) (rep (c + 1) j) ↔ thr c i ≤ j.val := by
    intro c i j
    set S := Finset.univ.filter (fun j' : Fin (sz (c + 1)) => H.Adj (rep c i) (rep (c + 1) j'))
    have hS_up : ∀ j₁ j₂ : Fin (sz (c + 1)), j₁ ∈ S → j₁ ≤ j₂ → j₂ ∈ S := by
      intro j₁ j₂ hj1 hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact hj1
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrep_adj_mono_right c j₁ j₂ hlt i (Finset.mem_filter.mp hj1).2⟩
    have hS_eq : S = Finset.univ.filter (fun j' : Fin (sz (c + 1)) => sz (c + 1) - #S ≤ j'.val) := by
      have hcard_R : #(Finset.univ.filter (fun j' : Fin (sz (c + 1)) => sz (c + 1) - #S ≤ j'.val)) = #S := by
        have hS_le : #S ≤ sz (c + 1) := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
        refine (Finset.card_bij (fun (j' : Fin (sz (c + 1))) _ => j'.val - (sz (c + 1) - #S)) ?_ ?_ ?_).trans (Finset.card_range #S)
        · intro j' hj'; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj').2; omega)
        · intro j₁ hj₁ j₂ hj₂ heq; have := (Finset.mem_filter.mp hj₁).2; have := (Finset.mem_filter.mp hj₂).2; exact Fin.ext (by omega)
        · intro m hm; have hm' := Finset.mem_range.mp hm
          exact ⟨⟨sz (c + 1) - #S + m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
      by_cases hsub : S ⊆ Finset.univ.filter (fun j' : Fin (sz (c + 1)) => sz (c + 1) - #S ≤ j'.val)
      · exact Finset.eq_of_subset_of_card_le hsub (by omega)
      · exfalso
        obtain ⟨j₀, hj₀S, hj₀not⟩ := Finset.not_subset.mp hsub
        have hj₀_lt : j₀.val < sz (c + 1) - #S := by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀not; omega
        have hge : Finset.univ.filter (fun j' : Fin (sz (c + 1)) => j₀.val ≤ j'.val) ⊆ S :=
          fun j' hj' => hS_up j₀ j' hj₀S (Fin.le_def.mpr (Finset.mem_filter.mp hj').2)
        have hcard_ge : #(Finset.univ.filter (fun j' : Fin (sz (c + 1)) => j₀.val ≤ j'.val)) = sz (c + 1) - j₀.val := by
          refine (Finset.card_bij (fun (j' : Fin (sz (c + 1))) _ => j'.val - j₀.val) ?_ ?_ ?_).trans (Finset.card_range (sz (c + 1) - j₀.val))
          · intro j' hj'; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj').2; omega)
          · intro j₁ hj₁ j₂ hj₂ heq; have := (Finset.mem_filter.mp hj₁).2; have := (Finset.mem_filter.mp hj₂).2; exact Fin.ext (by omega)
          · intro m hm; have hm' := Finset.mem_range.mp hm
            exact ⟨⟨j₀.val + m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
        have := Finset.card_le_card hge; omega
    have hmem := Finset.ext_iff.mp hS_eq j
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem
  have hthr_le : ∀ (c : Fin 3) (i : Fin (sz c)), thr c i ≤ sz (c + 1) := fun _ _ => Nat.sub_le _ _
  have hthr_sm : ∀ (c : Fin 3) (i₁ i₂ : Fin (sz c)), i₁ < i₂ → thr c i₁ < thr c i₂ := by
    intro c i₁ i₂ hlt
    have hdlt : degNext c (rep c i₂) < degNext c (rep c i₁) := by rw [hrep_deg, hrep_deg]; exact hdegVal_strict c i₁ i₂ hlt
    have hne1 : c ≠ c + 1 := by fin_cases c <;> decide
    have hssub : (P (c + 1)).filter (H.Adj (rep c i₂)) ⊂ (P (c + 1)).filter (H.Adj (rep c i₁)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, fun heq => by have := congrArg Finset.card heq; dsimp only [degNext] at hdlt; omega⟩
      rcases hnbhd_total c (c + 1) hne1 (rep c i₁) (hrep_mem c i₁) (rep c i₂) (hrep_mem c i₂) with h | h
      · have := Finset.card_le_card h; dsimp only [degNext] at hdlt; omega
      · exact h
    obtain ⟨y, hy1, hy2⟩ := Finset.exists_of_ssubset hssub
    have hy1' := Finset.mem_filter.mp hy1
    obtain ⟨j, rfl⟩ := hex_idx (c + 1) y (Finset.mem_filter.mp hy1'.1).2
    have hna2 : ¬ H.Adj (rep c i₂) (rep (c + 1) j) := fun h => hy2 (Finset.mem_filter.mpr ⟨hy1'.1, h⟩)
    rw [hthr_iff] at hy1' hna2; omega
  -- Helper: given any ordered cyclic triple `(c0, c1, c2)` with `sz c0 <= sz c1 <= sz c2` and
  -- exact threshold maps `(f, g, h)` encoding `H.Adj` via bijections `r0, r1, r2`, produce the 3-way result!
  have hfrom_ordered : ∀ (c0 c1 c2 : Fin 3) (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2)
      (a b c : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
      (r0 : Fin a → U) (r1 : Fin b → U) (r2 : Fin c → U)
      (hr0_col : ∀ i, col (r0 i) = c0) (hr1_col : ∀ j, col (r1 j) = c1) (hr2_col : ∀ k, col (r2 k) = c2)
      (hr0_inj : Function.Injective r0) (hr1_inj : Function.Injective r1) (hr2_inj : Function.Injective r2)
      (hr0_surj : ∀ u, col u = c0 → ∃ i, r0 i = u)
      (hr1_surj : ∀ u, col u = c1 → ∃ j, r1 j = u)
      (hr2_surj : ∀ u, col u = c2 → ∃ k, r2 k = u)
      (f : Fin a → ℕ) (g : Fin b → ℕ) (h : Fin c → ℕ)
      (hfl : ∀ i, f i ≤ b) (hgl : ∀ j, g j ≤ c) (hhl : ∀ k, h k ≤ a)
      (hfs : ∀ i₁ i₂, i₁ < i₂ → f i₁ < f i₂) (hgs : ∀ j₁ j₂, j₁ < j₂ → g j₁ < g j₂) (hhs : ∀ k₁ k₂, k₁ < k₂ → h k₁ < h k₂)
      (hf_iff : ∀ i j, H.Adj (r0 i) (r1 j) ↔ f i ≤ j.val)
      (hg_iff : ∀ j k, H.Adj (r1 j) (r2 k) ↔ g j ≤ k.val)
      (hh_iff : ∀ k i, H.Adj (r2 k) (r0 i) ↔ h k ≤ i.val),
      (∃ (i : ℕ) (_ : 2 ≤ i) (π : Equiv.Perm (Fin 3)) (e : U ≃ Fin (3 * i - 1)),
        (∀ u v : U, H.Adj u v ↔ vegaAdj i (.inl (e u)) (.inl (e v))) ∧
        (∀ u : U, (π (col u) = 0 ↔ (e u).val < i) ∧
                  (π (col u) = 1 ↔ i ≤ (e u).val ∧ (e u).val < 2 * i) ∧
                  (π (col u) = 2 ↔ 2 * i ≤ (e u).val))) ∨
      (∃ (i : ℕ) (_ : 2 ≤ i) (π : Equiv.Perm (Fin 3)) (e : U ≃ {p : Fin (3 * i - 1) // p.val ≠ 2 * i - 1}),
        (∀ u v : U, H.Adj u v ↔ vegaAdj i (.inl (e u).1) (.inl (e v).1)) ∧
        (∀ u : U, (π (col u) = 0 ↔ (e u).1.val < i) ∧
                  (π (col u) = 1 ↔ i ≤ (e u).1.val ∧ (e u).1.val < 2 * i) ∧
                  (π (col u) = 2 ↔ 2 * i ≤ (e u).1.val))) ∨
      (∃ (d : ℕ) (_ : 2 ≤ d) (φ : U → Fin (3 * d - 1)),
        Function.Injective φ ∧ (∀ u v : U, H.Adj u v ↔ vegaAdj d (.inl (φ u)) (.inl (φ v))) ∧
        ∃ (c1' c2' : Fin 3) (p0 s0 : U), c1' ≠ c2' ∧ col p0 = c1' ∧ col s0 = c2' ∧
          (∀ z : U, col z = c2' → ¬ H.Adj p0 z) ∧ (∀ x : U, col x = c1' → ¬ H.Adj s0 x)) := by
    intro c0 c1 c2 hc01 hc02 hc12 a b c ha hab hbc r0 r1 r2 hr0c hr1c hr2c hr0i hr1i hr2i hr0s hr1s hr2s f g h hfl hgl hhl hfs hgs hhs hfi hgi hhi
    have hTF' : ∀ i j k, ¬ (f i ≤ j.val ∧ g j ≤ k.val ∧ h k ≤ i.val) := fun i j k ⟨a1, a2, a3⟩ =>
      tf_contra hTF ((hfi i j).mpr a1) ((hgi j k).mpr a2) ((hhi k i).mpr a3).symm
    have hXY : ∀ i j, j.val < f i → ∃ k, g j ≤ k.val ∧ h k ≤ i.val := by
      intro i j hlt
      have hna : ¬ H.Adj (r0 i) (r1 j) := by rw [hfi]; omega
      obtain ⟨w, hw0, hw1⟩ := hCrossMax (r0 i) (r1 j) (by rw [hr0c, hr1c]; exact hc01) hna
      have hcw : col w = c2 := OMA.R_Erdos128_erdos_128_R2.fin3_third hc01 hc02 hc12
        (by rw [← hr0c i]; exact (hcol _ _ hw0).symm) (by rw [← hr1c j]; exact (hcol _ _ hw1).symm)
      obtain ⟨k, rfl⟩ := hr2s w hcw
      exact ⟨k, (hgi j k).mp hw1, (hhi k i).mp hw0.symm⟩
    have hYZ : ∀ j k, k.val < g j → ∃ i, f i ≤ j.val ∧ h k ≤ i.val := by
      intro j k hlt
      have hna : ¬ H.Adj (r1 j) (r2 k) := by rw [hgi]; omega
      obtain ⟨w, hw1, hw2⟩ := hCrossMax (r1 j) (r2 k) (by rw [hr1c, hr2c]; exact hc12) hna
      have hcw : col w = c0 := OMA.R_Erdos128_erdos_128_R2.fin3_third hc12 hc01.symm hc02.symm
        (by rw [← hr1c j]; exact (hcol _ _ hw1).symm) (by rw [← hr2c k]; exact (hcol _ _ hw2).symm)
      obtain ⟨i, rfl⟩ := hr0s w hcw
      exact ⟨i, (hfi i j).mp hw1.symm, (hhi k i).mp hw2⟩
    have hZX : ∀ k i, i.val < h k → ∃ j, f i ≤ j.val ∧ g j ≤ k.val := by
      intro k i hlt
      have hna : ¬ H.Adj (r2 k) (r0 i) := by rw [hhi]; omega
      obtain ⟨w, hw2, hw0⟩ := hCrossMax (r2 k) (r0 i) (by rw [hr2c, hr0c]; exact hc02.symm) hna
      have hcw : col w = c1 := OMA.R_Erdos128_erdos_128_R2.fin3_third hc02.symm hc12.symm hc01
        (by rw [← hr2c k]; exact (hcol _ _ hw2).symm) (by rw [← hr0c i]; exact (hcol _ _ hw0).symm)
      obtain ⟨j, rfl⟩ := hr1s w hcw
      exact ⟨j, (hfi i j).mp hw0, (hgi j k).mp hw2.symm⟩
    -- Helper: build `U -> Fin (3*d-1)` from maps on `(Fin a, Fin b, Fin c)`!
    have hcol_cases : ∀ u : U, col u = c0 ∨ col u = c1 ∨ col u = c2 := by
      intro u; by_cases h0 : col u = c0
      · exact Or.inl h0
      · by_cases h1 : col u = c1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (OMA.R_Erdos128_erdos_128_R2.fin3_third hc01 hc02 hc12 h0 h1))
    -- Helper: build permutation `π : Equiv.Perm (Fin 3)` sending `c0 ↦ t0, c1 ↦ t1, c2 ↦ t2`
    have mkPerm : ∀ (t0 t1 t2 : Fin 3), t0 ≠ t1 → t0 ≠ t2 → t1 ≠ t2 →
        ∃ π : Equiv.Perm (Fin 3), π c0 = t0 ∧ π c1 = t1 ∧ π c2 = t2 := by
      intro t0 t1 t2 ht01 ht02 ht12
      let toF : Fin 3 → Fin 3 := fun x => if x = c0 then t0 else if x = c1 then t1 else t2
      let invF : Fin 3 → Fin 3 := fun y => if y = t0 then c0 else if y = t1 then c1 else c2
      refine ⟨⟨toF, invF, ?_, ?_⟩, by change toF c0 = t0; simp [toF],
        by change toF c1 = t1; simp [toF, hc01.symm],
        by change toF c2 = t2; simp [toF, hc02.symm, hc12.symm]⟩
      · intro x; dsimp only [toF, invF]
        by_cases hx0 : x = c0
        · subst hx0; simp
        · by_cases hx1 : x = c1
          · subst hx1; simp [hx0, ht01.symm]
          · have hx2 : x = c2 := OMA.R_Erdos128_erdos_128_R2.fin3_third hc01 hc02 hc12 hx0 hx1
            subst hx2; simp [hx0, hx1, ht02.symm, ht12.symm]
      · intro y; dsimp only [toF, invF]
        by_cases hy0 : y = t0
        · subst hy0; simp
        · by_cases hy1 : y = t1
          · subst hy1; simp [hy0, hc01.symm]
          · have hy2 : y = t2 := OMA.R_Erdos128_erdos_128_R2.fin3_third ht01 ht02 ht12 hy0 hy1
            subst hy2; simp [hy0, hy1, hc02.symm, hc12.symm]
    -- Compact helper: `vegaAdj d (.inl p) (.inl q)` via plain `if` (no `%`!)
    have hva_mod : ∀ {d : ℕ} (hd : 2 ≤ d) (p q : Fin (3 * d - 1)),
        vegaAdj d (.inl p) (.inl q) ↔
        (if p.val ≤ q.val then d ≤ q.val - p.val ∧ q.val - p.val ≤ 2 * d - 1
         else d ≤ q.val + (3 * d - 1) - p.val ∧ q.val + (3 * d - 1) - p.val ≤ 2 * d - 1) := by
      intro d hd p q; have hp := p.isLt; have hq := q.isLt; simp only [vegaAdj]
      split_ifs with hpq
      · rw [show q.val + (3 * d - 1) - p.val = (q.val - p.val) + (3 * d - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega)]
    have hshape := ferrers_ordered_exact ha hab hbc f g h hfl hgl hhl hfs hgs hhs hTF' hXY hYZ hZX
    rcases hshape with ⟨ha_eq, hb_eq, hc2, hfeq, hgeq, hheq⟩ | ⟨ha_eq, hb_eq, hc2, hfeq, hgeq, hheq⟩ | ⟨ha_eq, hb_eq, hddd⟩
    · -- Case 1: And(c): Y -> I1 (0..c-1), Z -> I2 (c..2c-1), X -> I3 (2c..3c-2)
      left
      obtain ⟨π, hπ0, hπ1, hπ2⟩ := mkPerm 2 0 1 (by decide) (by decide) (by decide)
      let fwd : U → Fin (3 * c - 1) := fun u =>
        if h0 : col u = c0 then ⟨2 * c + (hr0s u h0).choose.val, by have := (hr0s u h0).choose.isLt; omega⟩
        else if h1 : col u = c1 then ⟨(hr1s u h1).choose.val, by have := (hr1s u h1).choose.isLt; omega⟩
        else
          have h2 : col u = c2 := OMA.R_Erdos128_erdos_128_R2.fin3_third hc01 hc02 hc12 h0 h1
          ⟨c + (hr2s u h2).choose.val, by have := (hr2s u h2).choose.isLt; omega⟩
      have hfwd0 : ∀ i : Fin a, fwd (r0 i) = ⟨2 * c + i.val, by have := i.isLt; omega⟩ := by
        intro i; dsimp only [fwd]; rw [dif_pos (hr0c i)]; apply Fin.ext; dsimp
        have := congrArg Fin.val (hr0i ((hr0s (r0 i) (hr0c i)).choose_spec)); omega
      have hfwd1 : ∀ j : Fin b, fwd (r1 j) = ⟨j.val, by have := j.isLt; omega⟩ := by
        intro j; dsimp only [fwd]; rw [dif_neg (by rw [hr1c]; exact hc01.symm), dif_pos (hr1c j)]; apply Fin.ext; dsimp
        have := congrArg Fin.val (hr1i ((hr1s (r1 j) (hr1c j)).choose_spec)); omega
      have hfwd2 : ∀ k : Fin c, fwd (r2 k) = ⟨c + k.val, by have := k.isLt; omega⟩ := by
        intro k; dsimp only [fwd]
        rw [dif_neg (by rw [hr2c]; exact hc02.symm), dif_neg (by rw [hr2c]; exact hc12.symm)]; apply Fin.ext; dsimp
        have := congrArg Fin.val (hr2i ((hr2s (r2 k) (hr2c k)).choose_spec)); omega
      let inv : Fin (3 * c - 1) → U := fun p =>
        if hp1 : p.val < c then r1 ⟨p.val, by omega⟩
        else if hp2 : p.val < 2 * c then r2 ⟨p.val - c, by omega⟩
        else r0 ⟨p.val - 2 * c, by have := p.isLt; omega⟩
      have hleft : Function.LeftInverse inv fwd := by
        intro u; rcases hcol_cases u with h0 | h1 | h2
        · obtain ⟨i, rfl⟩ := hr0s u h0; rw [hfwd0]; dsimp only [inv]
          rw [dif_neg (by omega), dif_neg (by omega)]; congr 1; ext; dsimp; omega
        · obtain ⟨j, rfl⟩ := hr1s u h1; rw [hfwd1]; dsimp only [inv]
          have := j.isLt; rw [dif_pos (by omega)]
        · obtain ⟨k, rfl⟩ := hr2s u h2; rw [hfwd2]; dsimp only [inv]
          have := k.isLt; rw [dif_neg (by omega), dif_pos (by omega)]; congr 1; ext; dsimp; omega
      have hright : Function.RightInverse inv fwd := by
        intro p; have hp := p.isLt; dsimp only [inv]
        split_ifs with hp1 hp2
        · rw [hfwd1]
        · rw [hfwd2]; ext; dsimp; omega
        · rw [hfwd0]; ext; dsimp; omega
      refine ⟨c, hc2, π, ⟨fwd, inv, hleft, hright⟩, ?_, ?_⟩
      · intro u v; dsimp only [Equiv.coe_fn_mk]
        rcases hcol_cases u with hu0 | hu1 | hu2 <;> rcases hcol_cases v with hv0 | hv1 | hv2
        · obtain ⟨i1, rfl⟩ := hr0s u hu0; obtain ⟨i2, rfl⟩ := hr0s v hv0
          have hna : ¬ H.Adj (r0 i1) (r0 i2) := fun h => hcol _ _ h (by rw [hr0c, hr0c])
          rw [hfwd0, hfwd0, hva_mod hc2]; have := i1.isLt; have := i2.isLt; dsimp; simp only [hna, false_iff]; split_ifs <;> omega
        · obtain ⟨i, rfl⟩ := hr0s u hu0; obtain ⟨j, rfl⟩ := hr1s v hv1
          rw [hfi, hfeq, hfwd0, hfwd1, hva_mod hc2]; have := i.isLt; have := j.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨i, rfl⟩ := hr0s u hu0; obtain ⟨k, rfl⟩ := hr2s v hv2
          rw [H.adj_comm, hhi, hheq, hfwd0, hfwd2, hva_mod hc2]; have := i.isLt; have := k.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨j, rfl⟩ := hr1s u hu1; obtain ⟨i, rfl⟩ := hr0s v hv0
          rw [H.adj_comm, hfi, hfeq, hfwd0, hfwd1, hva_mod hc2]; have := i.isLt; have := j.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨j1, rfl⟩ := hr1s u hu1; obtain ⟨j2, rfl⟩ := hr1s v hv1
          have hna : ¬ H.Adj (r1 j1) (r1 j2) := fun h => hcol _ _ h (by rw [hr1c, hr1c])
          rw [hfwd1, hfwd1, hva_mod hc2]; have := j1.isLt; have := j2.isLt; dsimp; simp only [hna, false_iff]; split_ifs <;> omega
        · obtain ⟨j, rfl⟩ := hr1s u hu1; obtain ⟨k, rfl⟩ := hr2s v hv2
          rw [hgi, hgeq, hfwd1, hfwd2, hva_mod hc2]; have := j.isLt; have := k.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨k, rfl⟩ := hr2s u hu2; obtain ⟨i, rfl⟩ := hr0s v hv0
          rw [hhi, hheq, hfwd0, hfwd2, hva_mod hc2]; have := i.isLt; have := k.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨k, rfl⟩ := hr2s u hu2; obtain ⟨j, rfl⟩ := hr1s v hv1
          rw [H.adj_comm, hgi, hgeq, hfwd1, hfwd2, hva_mod hc2]; have := j.isLt; have := k.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨k1, rfl⟩ := hr2s u hu2; obtain ⟨k2, rfl⟩ := hr2s v hv2
          have hna : ¬ H.Adj (r2 k1) (r2 k2) := fun h => hcol _ _ h (by rw [hr2c, hr2c])
          rw [hfwd2, hfwd2, hva_mod hc2]; have := k1.isLt; have := k2.isLt; dsimp; simp only [hna, false_iff]; split_ifs <;> omega
      · intro u; dsimp only [Equiv.coe_fn_mk]; rcases hcol_cases u with h0 | h1 | h2
        · obtain ⟨i, rfl⟩ := hr0s u h0; rw [hr0c, hπ0, hfwd0]; have := i.isLt; dsimp; (refine ⟨?_, ?_, ?_⟩ <;> simp); omega
        · obtain ⟨j, rfl⟩ := hr1s u h1; rw [hr1c, hπ1, hfwd1]; have := j.isLt; dsimp; refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
        · obtain ⟨k, rfl⟩ := hr2s u h2; rw [hr2c, hπ2, hfwd2]; have := k.isLt; dsimp; refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
    · -- Case 2: And(c) - {2c-1}: Z -> I1 (0..c-1), X -> I2\{2c-1} (c..2c-2), Y -> I3 (2c..3c-2)
      right; left
      obtain ⟨π, hπ0, hπ1, hπ2⟩ := mkPerm 1 2 0 (by decide) (by decide) (by decide)
      let fwd : U → {p : Fin (3 * c - 1) // p.val ≠ 2 * c - 1} := fun u =>
        if h0 : col u = c0 then ⟨⟨c + (hr0s u h0).choose.val, by have := (hr0s u h0).choose.isLt; omega⟩, by have := (hr0s u h0).choose.isLt; dsimp; omega⟩
        else if h1 : col u = c1 then ⟨⟨2 * c + (hr1s u h1).choose.val, by have := (hr1s u h1).choose.isLt; omega⟩, by have := (hr1s u h1).choose.isLt; dsimp; omega⟩
        else
          have h2 : col u = c2 := OMA.R_Erdos128_erdos_128_R2.fin3_third hc01 hc02 hc12 h0 h1
          ⟨⟨(hr2s u h2).choose.val, by have := (hr2s u h2).choose.isLt; omega⟩, by have := (hr2s u h2).choose.isLt; dsimp; omega⟩
      have hfwd0 : ∀ i : Fin a, (fwd (r0 i)).1 = ⟨c + i.val, by have := i.isLt; omega⟩ := by
        intro i; dsimp only [fwd]; rw [dif_pos (hr0c i)]; apply Fin.ext; dsimp
        have := congrArg Fin.val (hr0i ((hr0s (r0 i) (hr0c i)).choose_spec)); omega
      have hfwd1 : ∀ j : Fin b, (fwd (r1 j)).1 = ⟨2 * c + j.val, by have := j.isLt; omega⟩ := by
        intro j; dsimp only [fwd]; rw [dif_neg (by rw [hr1c]; exact hc01.symm), dif_pos (hr1c j)]; apply Fin.ext; dsimp
        have := congrArg Fin.val (hr1i ((hr1s (r1 j) (hr1c j)).choose_spec)); omega
      have hfwd2 : ∀ k : Fin c, (fwd (r2 k)).1 = ⟨k.val, by have := k.isLt; omega⟩ := by
        intro k; dsimp only [fwd]
        rw [dif_neg (by rw [hr2c]; exact hc02.symm), dif_neg (by rw [hr2c]; exact hc12.symm)]; apply Fin.ext; dsimp
        have := congrArg Fin.val (hr2i ((hr2s (r2 k) (hr2c k)).choose_spec)); omega
      let inv : {p : Fin (3 * c - 1) // p.val ≠ 2 * c - 1} → U := fun p =>
        if hp1 : p.1.val < c then r2 ⟨p.1.val, by omega⟩
        else if hp2 : p.1.val < 2 * c - 1 then r0 ⟨p.1.val - c, by omega⟩
        else r1 ⟨p.1.val - 2 * c, by have := p.1.isLt; have := p.2; omega⟩
      have hleft : Function.LeftInverse inv fwd := by
        intro u; rcases hcol_cases u with h0 | h1 | h2
        · obtain ⟨i, rfl⟩ := hr0s u h0; have hi := i.isLt; dsimp only [inv]
          have hval : (fwd (r0 i)).1.val = c + i.val := congrArg Fin.val (hfwd0 i)
          rw [dif_neg (by omega), dif_pos (by omega)]; congr 1; ext; dsimp; omega
        · obtain ⟨j, rfl⟩ := hr1s u h1; have hj := j.isLt; dsimp only [inv]
          have hval : (fwd (r1 j)).1.val = 2 * c + j.val := congrArg Fin.val (hfwd1 j)
          rw [dif_neg (by omega), dif_neg (by omega)]; congr 1; ext; dsimp; omega
        · obtain ⟨k, rfl⟩ := hr2s u h2; have hk := k.isLt; dsimp only [inv]
          have hval : (fwd (r2 k)).1.val = k.val := congrArg Fin.val (hfwd2 k)
          rw [dif_pos (by omega)]; congr 1; ext; dsimp; omega
      have hright : Function.RightInverse inv fwd := by
        intro ⟨p, hpne⟩; have hp := p.isLt; apply Subtype.ext; dsimp only [inv]
        split_ifs with hp1 hp2
        · rw [hfwd2]
        · rw [hfwd0]; ext; dsimp; omega
        · rw [hfwd1]; ext; dsimp; omega
      refine ⟨c, hc2, π, ⟨fwd, inv, hleft, hright⟩, ?_, ?_⟩
      · intro u v; dsimp only [Equiv.coe_fn_mk]
        rcases hcol_cases u with hu0 | hu1 | hu2 <;> rcases hcol_cases v with hv0 | hv1 | hv2
        · obtain ⟨i1, rfl⟩ := hr0s u hu0; obtain ⟨i2, rfl⟩ := hr0s v hv0
          have hna : ¬ H.Adj (r0 i1) (r0 i2) := fun h => hcol _ _ h (by rw [hr0c, hr0c])
          rw [hfwd0, hfwd0, hva_mod hc2]; have := i1.isLt; have := i2.isLt; dsimp; simp only [hna, false_iff]; split_ifs <;> omega
        · obtain ⟨i, rfl⟩ := hr0s u hu0; obtain ⟨j, rfl⟩ := hr1s v hv1
          rw [hfi, hfeq, hfwd0, hfwd1, hva_mod hc2]; have := i.isLt; have := j.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨i, rfl⟩ := hr0s u hu0; obtain ⟨k, rfl⟩ := hr2s v hv2
          rw [H.adj_comm, hhi, hheq, hfwd0, hfwd2, hva_mod hc2]; have := i.isLt; have := k.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨j, rfl⟩ := hr1s u hu1; obtain ⟨i, rfl⟩ := hr0s v hv0
          rw [H.adj_comm, hfi, hfeq, hfwd0, hfwd1, hva_mod hc2]; have := i.isLt; have := j.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨j1, rfl⟩ := hr1s u hu1; obtain ⟨j2, rfl⟩ := hr1s v hv1
          have hna : ¬ H.Adj (r1 j1) (r1 j2) := fun h => hcol _ _ h (by rw [hr1c, hr1c])
          rw [hfwd1, hfwd1, hva_mod hc2]; have := j1.isLt; have := j2.isLt; dsimp; simp only [hna, false_iff]; split_ifs <;> omega
        · obtain ⟨j, rfl⟩ := hr1s u hu1; obtain ⟨k, rfl⟩ := hr2s v hv2
          rw [hgi, hgeq, hfwd1, hfwd2, hva_mod hc2]; have := j.isLt; have := k.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨k, rfl⟩ := hr2s u hu2; obtain ⟨i, rfl⟩ := hr0s v hv0
          rw [hhi, hheq, hfwd0, hfwd2, hva_mod hc2]; have := i.isLt; have := k.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨k, rfl⟩ := hr2s u hu2; obtain ⟨j, rfl⟩ := hr1s v hv1
          rw [H.adj_comm, hgi, hgeq, hfwd1, hfwd2, hva_mod hc2]; have := j.isLt; have := k.isLt; dsimp; split_ifs <;> omega
        · obtain ⟨k1, rfl⟩ := hr2s u hu2; obtain ⟨k2, rfl⟩ := hr2s v hv2
          have hna : ¬ H.Adj (r2 k1) (r2 k2) := fun h => hcol _ _ h (by rw [hr2c, hr2c])
          rw [hfwd2, hfwd2, hva_mod hc2]; have := k1.isLt; have := k2.isLt; dsimp; simp only [hna, false_iff]; split_ifs <;> omega
      · intro u; dsimp only [Equiv.coe_fn_mk]; rcases hcol_cases u with h0 | h1 | h2
        · obtain ⟨i, rfl⟩ := hr0s u h0; rw [hr0c, hπ0, hfwd0]; have := i.isLt; dsimp; refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
        · obtain ⟨j, rfl⟩ := hr1s u h1; rw [hr1c, hπ1, hfwd1]; have := j.isLt; dsimp; (refine ⟨?_, ?_, ?_⟩ <;> simp); omega
        · obtain ⟨k, rfl⟩ := hr2s u h2; rw [hr2c, hπ2, hfwd2]; have := k.isLt; dsimp; (refine ⟨?_, ?_, ?_⟩ <;> simp); omega
    · -- Case 3: Shape (c, c, c) -> embeds into And(c + 1) AND has dead endpoints!
      right; right
      have hmk3 : ∀ (ca cb cc : Fin 3) (h1 : ca ≠ cb) (h2 : ca ≠ cc) (h3 : cb ≠ cc)
          (qa qb qc : Fin c → U)
          (hqa_c : ∀ i, col (qa i) = ca) (hqb_c : ∀ j, col (qb j) = cb) (hqc_c : ∀ k, col (qc k) = cc)
          (hqa_i : Function.Injective qa) (hqb_i : Function.Injective qb) (hqc_i : Function.Injective qc)
          (hqa_s : ∀ u, col u = ca → ∃ i, qa i = u)
          (hqb_s : ∀ u, col u = cb → ∃ j, qb j = u)
          (hqc_s : ∀ u, col u = cc → ∃ k, qc k = u)
          (hab_iff : ∀ i j : Fin c, H.Adj (qa i) (qb j) ↔ i.val ≤ j.val)
          (hbc_iff : ∀ j k : Fin c, H.Adj (qb j) (qc k) ↔ j.val ≤ k.val)
          (hca_iff : ∀ k i : Fin c, H.Adj (qc k) (qa i) ↔ k.val + 1 ≤ i.val),
          ∃ (d : ℕ) (_ : 2 ≤ d) (φ : U → Fin (3 * d - 1)),
            Function.Injective φ ∧ (∀ u v : U, H.Adj u v ↔ vegaAdj d (.inl (φ u)) (.inl (φ v))) ∧
            ∃ (c1' c2' : Fin 3) (p0 s0 : U), c1' ≠ c2' ∧ col p0 = c1' ∧ col s0 = c2' ∧
              (∀ z : U, col z = c2' → ¬ H.Adj p0 z) ∧ (∀ x : U, col x = c1' → ¬ H.Adj s0 x) := by
        intro ca cb cc h1 h2 h3 qa qb qc hqac hqbc hqcc hqai hqbi hqci hqas hqbs hqcs hab_i hbc_i hca_i
        let d := c + 1
        have hd2 : 2 ≤ d := by omega
        have hcc : ∀ u : U, col u = ca ∨ col u = cb ∨ col u = cc := by
          intro u; by_cases ha' : col u = ca
          · exact Or.inl ha'
          · by_cases hb' : col u = cb
            · exact Or.inr (Or.inl hb')
            · exact Or.inr (Or.inr (OMA.R_Erdos128_erdos_128_R2.fin3_third h1 h2 h3 ha' hb'))
        let φ : U → Fin (3 * d - 1) := fun u =>
          if ha' : col u = ca then ⟨(hqas u ha').choose.val, by have := (hqas u ha').choose.isLt; omega⟩
          else if hb' : col u = cb then ⟨d + (hqbs u hb').choose.val, by have := (hqbs u hb').choose.isLt; omega⟩
          else
            have hc' : col u = cc := OMA.R_Erdos128_erdos_128_R2.fin3_third h1 h2 h3 ha' hb'
            ⟨2 * d + (hqcs u hc').choose.val, by have := (hqcs u hc').choose.isLt; omega⟩
        have hφa : ∀ i : Fin c, φ (qa i) = ⟨i.val, by have := i.isLt; omega⟩ := by
          intro i; dsimp only [φ]; rw [dif_pos (hqac i)]; apply Fin.ext; dsimp
          have := congrArg Fin.val (hqai ((hqas (qa i) (hqac i)).choose_spec)); omega
        have hφb : ∀ j : Fin c, φ (qb j) = ⟨d + j.val, by have := j.isLt; omega⟩ := by
          intro j; dsimp only [φ]; rw [dif_neg (by rw [hqbc]; exact h1.symm), dif_pos (hqbc j)]; apply Fin.ext; dsimp
          have := congrArg Fin.val (hqbi ((hqbs (qb j) (hqbc j)).choose_spec)); omega
        have hφc : ∀ k : Fin c, φ (qc k) = ⟨2 * d + k.val, by have := k.isLt; omega⟩ := by
          intro k; dsimp only [φ]
          rw [dif_neg (by rw [hqcc]; exact h2.symm), dif_neg (by rw [hqcc]; exact h3.symm)]; apply Fin.ext; dsimp
          have := congrArg Fin.val (hqci ((hqcs (qc k) (hqcc k)).choose_spec)); omega
        have hφ_inj : Function.Injective φ := by
          intro u v huv
          rcases hcc u with ha1 | hb1 | hc1 <;> rcases hcc v with ha2 | hb2 | hc2
          · obtain ⟨i1, rfl⟩ := hqas u ha1; obtain ⟨i2, rfl⟩ := hqas v ha2
            rw [hφa, hφa] at huv; have h := congrArg Fin.val huv; exact congrArg qa (Fin.ext (by dsimp at h; omega))
          · obtain ⟨i1, rfl⟩ := hqas u ha1; obtain ⟨j2, rfl⟩ := hqbs v hb2
            rw [hφa, hφb] at huv; have h := congrArg Fin.val huv; have := i1.isLt; dsimp at h; omega
          · obtain ⟨i1, rfl⟩ := hqas u ha1; obtain ⟨k2, rfl⟩ := hqcs v hc2
            rw [hφa, hφc] at huv; have h := congrArg Fin.val huv; have := i1.isLt; dsimp at h; omega
          · obtain ⟨j1, rfl⟩ := hqbs u hb1; obtain ⟨i2, rfl⟩ := hqas v ha2
            rw [hφb, hφa] at huv; have h := congrArg Fin.val huv; have := i2.isLt; dsimp at h; omega
          · obtain ⟨j1, rfl⟩ := hqbs u hb1; obtain ⟨j2, rfl⟩ := hqbs v hb2
            rw [hφb, hφb] at huv; have h := congrArg Fin.val huv; exact congrArg qb (Fin.ext (by dsimp at h; omega))
          · obtain ⟨j1, rfl⟩ := hqbs u hb1; obtain ⟨k2, rfl⟩ := hqcs v hc2
            rw [hφb, hφc] at huv; have h := congrArg Fin.val huv; have := j1.isLt; dsimp at h; omega
          · obtain ⟨k1, rfl⟩ := hqcs u hc1; obtain ⟨i2, rfl⟩ := hqas v ha2
            rw [hφc, hφa] at huv; have h := congrArg Fin.val huv; have := i2.isLt; dsimp at h; omega
          · obtain ⟨k1, rfl⟩ := hqcs u hc1; obtain ⟨j2, rfl⟩ := hqbs v hb2
            rw [hφc, hφb] at huv; have h := congrArg Fin.val huv; have := j2.isLt; dsimp at h; omega
          · obtain ⟨k1, rfl⟩ := hqcs u hc1; obtain ⟨k2, rfl⟩ := hqcs v hc2
            rw [hφc, hφc] at huv; have h := congrArg Fin.val huv; exact congrArg qc (Fin.ext (by dsimp at h; omega))
        have hφ_adj : ∀ u v : U, H.Adj u v ↔ vegaAdj d (.inl (φ u)) (.inl (φ v)) := by
          intro u v
          rcases hcc u with ha1 | hb1 | hc1 <;> rcases hcc v with ha2 | hb2 | hc2
          · obtain ⟨i1, rfl⟩ := hqas u ha1; obtain ⟨i2, rfl⟩ := hqas v ha2
            have hna : ¬ H.Adj (qa i1) (qa i2) := fun h => hcol _ _ h (by rw [hqac, hqac])
            rw [hφa, hφa, hva_mod hd2]; have := i1.isLt; have := i2.isLt; dsimp; simp only [hna, false_iff]; split_ifs <;> omega
          · obtain ⟨i, rfl⟩ := hqas u ha1; obtain ⟨j, rfl⟩ := hqbs v hb2
            rw [hab_i, hφa, hφb, hva_mod hd2]; have := i.isLt; have := j.isLt; dsimp; split_ifs <;> omega
          · obtain ⟨i, rfl⟩ := hqas u ha1; obtain ⟨k, rfl⟩ := hqcs v hc2
            rw [H.adj_comm, hca_i, hφa, hφc, hva_mod hd2]; have := i.isLt; have := k.isLt; dsimp; split_ifs <;> omega
          · obtain ⟨j, rfl⟩ := hqbs u hb1; obtain ⟨i, rfl⟩ := hqas v ha2
            rw [H.adj_comm, hab_i, hφa, hφb, hva_mod hd2]; have := i.isLt; have := j.isLt; dsimp; split_ifs <;> omega
          · obtain ⟨j1, rfl⟩ := hqbs u hb1; obtain ⟨j2, rfl⟩ := hqbs v hb2
            have hna : ¬ H.Adj (qb j1) (qb j2) := fun h => hcol _ _ h (by rw [hqbc, hqbc])
            rw [hφb, hφb, hva_mod hd2]; have := j1.isLt; have := j2.isLt; dsimp; simp only [hna, false_iff]; split_ifs <;> omega
          · obtain ⟨j, rfl⟩ := hqbs u hb1; obtain ⟨k, rfl⟩ := hqcs v hc2
            rw [hbc_i, hφb, hφc, hva_mod hd2]; have := j.isLt; have := k.isLt; dsimp; split_ifs <;> omega
          · obtain ⟨k, rfl⟩ := hqcs u hc1; obtain ⟨i, rfl⟩ := hqas v ha2
            rw [hca_i, hφa, hφc, hva_mod hd2]; have := i.isLt; have := k.isLt; dsimp; split_ifs <;> omega
          · obtain ⟨k, rfl⟩ := hqcs u hc1; obtain ⟨j, rfl⟩ := hqbs v hb2
            rw [H.adj_comm, hbc_i, hφb, hφc, hva_mod hd2]; have := j.isLt; have := k.isLt; dsimp; split_ifs <;> omega
          · obtain ⟨k1, rfl⟩ := hqcs u hc1; obtain ⟨k2, rfl⟩ := hqcs v hc2
            have hna : ¬ H.Adj (qc k1) (qc k2) := fun h => hcol _ _ h (by rw [hqcc, hqcc])
            rw [hφc, hφc, hva_mod hd2]; have := k1.isLt; have := k2.isLt; dsimp; simp only [hna, false_iff]; split_ifs <;> omega
        refine ⟨d, hd2, φ, hφ_inj, hφ_adj, ca, cc, qa ⟨0, by omega⟩, qc ⟨c - 1, by omega⟩, h2, hqac _, hqcc _, ?_, ?_⟩
        · intro z hz; obtain ⟨k, rfl⟩ := hqcs z hz; rw [H.adj_comm, hca_i]; dsimp; omega
        · intro x hx; obtain ⟨i, rfl⟩ := hqas x hx; rw [hca_i]; have := i.isLt; dsimp; omega
      subst ha_eq; subst hb_eq
      rcases hddd with ⟨hfeq, hgeq, hheq⟩ | ⟨hfeq, hgeq, hheq⟩ | ⟨hfeq, hgeq, hheq⟩
      · exact hmk3 c0 c1 c2 hc01 hc02 hc12 r0 r1 r2 hr0c hr1c hr2c hr0i hr1i hr2i hr0s hr1s hr2s
          (fun i j => by rw [hfi, hfeq]) (fun j k => by rw [hgi, hgeq]) (fun k i => by rw [hhi, hheq])
      · exact hmk3 c1 c2 c0 hc12 hc01.symm hc02.symm r1 r2 r0 hr1c hr2c hr0c hr1i hr2i hr0i hr1s hr2s hr0s
          (fun j k => by rw [hgi, hgeq]) (fun k i => by rw [hhi, hheq]) (fun i j => by rw [hfi, hfeq])
      · exact hmk3 c2 c0 c1 hc02.symm hc12.symm hc01 r2 r0 r1 hr2c hr0c hr1c hr2i hr0i hr1i hr2s hr0s hr1s
          (fun k i => by rw [hhi, hheq]) (fun i j => by rw [hfi, hfeq]) (fun j k => by rw [hgi, hgeq])
  -- Helper: reverse all 3 orders for `sz c1 <= sz c0 <= sz c2`!
  have hfrom_rev : ∀ (c0 c1 c2 : Fin 3) (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2)
      (h10 : sz c1 ≤ sz c0) (h02 : sz c0 ≤ sz c2)
      (hnext0 : c0 + 1 = c1) (hnext1 : c1 + 1 = c2) (hnext2 : c2 + 1 = c0),
      (∃ (i : ℕ) (_ : 2 ≤ i) (π : Equiv.Perm (Fin 3)) (e : U ≃ Fin (3 * i - 1)),
        (∀ u v : U, H.Adj u v ↔ vegaAdj i (.inl (e u)) (.inl (e v))) ∧
        (∀ u : U, (π (col u) = 0 ↔ (e u).val < i) ∧
                  (π (col u) = 1 ↔ i ≤ (e u).val ∧ (e u).val < 2 * i) ∧
                  (π (col u) = 2 ↔ 2 * i ≤ (e u).val))) ∨
      (∃ (i : ℕ) (_ : 2 ≤ i) (π : Equiv.Perm (Fin 3)) (e : U ≃ {p : Fin (3 * i - 1) // p.val ≠ 2 * i - 1}),
        (∀ u v : U, H.Adj u v ↔ vegaAdj i (.inl (e u).1) (.inl (e v).1)) ∧
        (∀ u : U, (π (col u) = 0 ↔ (e u).1.val < i) ∧
                  (π (col u) = 1 ↔ i ≤ (e u).1.val ∧ (e u).1.val < 2 * i) ∧
                  (π (col u) = 2 ↔ 2 * i ≤ (e u).1.val))) ∨
      (∃ (d : ℕ) (_ : 2 ≤ d) (φ : U → Fin (3 * d - 1)),
        Function.Injective φ ∧ (∀ u v : U, H.Adj u v ↔ vegaAdj d (.inl (φ u)) (.inl (φ v))) ∧
        ∃ (c1' c2' : Fin 3) (p0 s0 : U), c1' ≠ c2' ∧ col p0 = c1' ∧ col s0 = c2' ∧
          (∀ z : U, col z = c2' → ¬ H.Adj p0 z) ∧ (∀ x : U, col x = c1' → ¬ H.Adj s0 x)) := by
    intro c0 c1 c2 hc01 hc02 hc12 h10 h02 hn0 hn1 hn2
    let a := sz c0; let b := sz c1; let c := sz c2
    let r0 : Fin a → U := rep c0
    let r1 : Fin b → U := rep c1
    let r2 : Fin c → U := rep c2
    let f : Fin a → ℕ := fun i => thr c0 i
    let g : Fin b → ℕ := fun j => thr c1 j
    let h : Fin c → ℕ := fun k => thr c2 k
    have hfi : ∀ i j, H.Adj (r0 i) (r1 j) ↔ f i ≤ j.val := fun i j => by
      have := hthr_iff c0 i (hn0 ▸ j); subst hn0; exact this
    have hgi : ∀ j k, H.Adj (r1 j) (r2 k) ↔ g j ≤ k.val := fun j k => by
      have := hthr_iff c1 j (hn1 ▸ k); subst hn1; exact this
    have hhi : ∀ k i, H.Adj (r2 k) (r0 i) ↔ h k ≤ i.val := fun k i => by
      have := hthr_iff c2 k (hn2 ▸ i); subst hn2; exact this
    have hfl : ∀ i, f i ≤ b := fun i => by have := hthr_le c0 i; subst hn0; exact this
    have hgl : ∀ j, g j ≤ c := fun j => by have := hthr_le c1 j; subst hn1; exact this
    have hhl : ∀ k, h k ≤ a := fun k => by have := hthr_le c2 k; subst hn2; exact this
    have hfs : ∀ i1 i2, i1 < i2 → f i1 < f i2 := hthr_sm c0
    have hgs : ∀ j1 j2, j1 < j2 → g j1 < g j2 := hthr_sm c1
    have hhs : ∀ k1 k2, k1 < k2 → h k1 < h k2 := hthr_sm c2
    -- Reversed maps: r1' j' = r1 (b-1-j'), r0' i' = r0 (a-1-i'), r2' k' = r2 (c-1-k')
    let r1' : Fin b → U := fun j' => r1 ⟨b - 1 - j'.val, by have := j'.isLt; omega⟩
    let r0' : Fin a → U := fun i' => r0 ⟨a - 1 - i'.val, by have := i'.isLt; omega⟩
    let r2' : Fin c → U := fun k' => r2 ⟨c - 1 - k'.val, by have := k'.isLt; omega⟩
    let f' : Fin b → ℕ := fun j' => a - #(Finset.univ.filter (fun i' : Fin a => f ⟨a - 1 - i'.val, by omega⟩ ≤ b - 1 - j'.val))
    let g' : Fin a → ℕ := fun i' => c - #(Finset.univ.filter (fun k' : Fin c => h ⟨c - 1 - k'.val, by omega⟩ ≤ a - 1 - i'.val))
    let h' : Fin c → ℕ := fun k' => b - #(Finset.univ.filter (fun j' : Fin b => g ⟨b - 1 - j'.val, by omega⟩ ≤ c - 1 - k'.val))
    have hf'_i : ∀ (j' : Fin b) (i' : Fin a), f ⟨a - 1 - i'.val, by omega⟩ ≤ b - 1 - j'.val ↔ f' j' ≤ i'.val :=
      OMA.R_Erdos128_erdos_128_R2.cjk_dual_threshold f hfs
    have hg'_i : ∀ (i' : Fin a) (k' : Fin c), h ⟨c - 1 - k'.val, by omega⟩ ≤ a - 1 - i'.val ↔ g' i' ≤ k'.val :=
      OMA.R_Erdos128_erdos_128_R2.cjk_dual_threshold h hhs
    have hh'_i : ∀ (k' : Fin c) (j' : Fin b), g ⟨b - 1 - j'.val, by omega⟩ ≤ c - 1 - k'.val ↔ h' k' ≤ j'.val :=
      OMA.R_Erdos128_erdos_128_R2.cjk_dual_threshold g hgs
    have hf'_adj : ∀ j' i', H.Adj (r1' j') (r0' i') ↔ f' j' ≤ i'.val := fun j' i' => by
      rw [H.adj_comm, hfi]; exact hf'_i j' i'
    have hg'_adj : ∀ i' k', H.Adj (r0' i') (r2' k') ↔ g' i' ≤ k'.val := fun i' k' => by
      rw [H.adj_comm, hhi]; exact hg'_i i' k'
    have hh'_adj : ∀ k' j', H.Adj (r2' k') (r1' j') ↔ h' k' ≤ j'.val := fun k' j' => by
      rw [H.adj_comm, hgi]; exact hh'_i k' j'
    -- Strict monotonicity of f', g', h' using `hnbhd_eq_iff` + `hTwinPart`!
    have hf'_sm : ∀ j1 j2 : Fin b, j1 < j2 → f' j1 < f' j2 := by
      intro j1 j2 hlt
      have hle : f' j1 ≤ f' j2 := Nat.sub_le_sub_left (Finset.card_le_card (fun i' hi' =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hi').2; have := Fin.lt_def.mp hlt; omega⟩)) _
      by_contra hnot; have heq : f' j1 = f' j2 := by omega
      have hN0 : (P c0).filter (H.Adj (r1' j1)) = (P c0).filter (H.Adj (r1' j2)) := by
        ext u; simp only [Finset.mem_filter]; constructor
        · rintro ⟨huP, hadj⟩; obtain ⟨i, rfl⟩ := hex_idx c0 u (Finset.mem_filter.mp huP).2
          let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
          have hi_eq : r0' i' = rep c0 i := by dsimp only [r0', r0, i']; congr 1; ext; dsimp; omega
          rw [← hi_eq] at huP hadj ⊢; rw [hf'_adj] at hadj ⊢; exact ⟨huP, by omega⟩
        · rintro ⟨huP, hadj⟩; obtain ⟨i, rfl⟩ := hex_idx c0 u (Finset.mem_filter.mp huP).2
          let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
          have hi_eq : r0' i' = rep c0 i := by dsimp only [r0', r0, i']; congr 1; ext; dsimp; omega
          rw [← hi_eq] at huP hadj ⊢; rw [hf'_adj] at hadj ⊢; exact ⟨huP, by omega⟩
      have hN2 := hnbhd_eq_iff c1 c0 c2 hc01.symm hc12 hc02 (r1' j1) (hrep_mem c1 _) (r1' j2) (hrep_mem c1 _) hN0
      have hdeq : degNext c1 (r1' j1) = degNext c1 (r1' j2) := by
        dsimp only [degNext]; rw [hn1]; exact congrArg Finset.card hN2
      have hreq := hsame_deg_eq c1 (r1' j1) (r1' j2) (hrep_mem c1 _) (hrep_mem c1 _) hdeq
      have hfin := congrArg Fin.val (hrep_inj c1 hreq); dsimp at hfin; have := j1.isLt; have := j2.isLt; have := Fin.lt_def.mp hlt; omega
    have hg'_sm : ∀ i1 i2 : Fin a, i1 < i2 → g' i1 < g' i2 := by
      intro i1 i2 hlt
      have hle : g' i1 ≤ g' i2 := Nat.sub_le_sub_left (Finset.card_le_card (fun k' hk' =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hk').2; have := Fin.lt_def.mp hlt; omega⟩)) _
      by_contra hnot; have heq : g' i1 = g' i2 := by omega
      have hN2 : (P c2).filter (H.Adj (r0' i1)) = (P c2).filter (H.Adj (r0' i2)) := by
        ext u; simp only [Finset.mem_filter]; constructor
        · rintro ⟨huP, hadj⟩; obtain ⟨k, rfl⟩ := hex_idx c2 u (Finset.mem_filter.mp huP).2
          let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
          have hk_eq : r2' k' = rep c2 k := by dsimp only [r2', r2, k']; congr 1; ext; dsimp; omega
          rw [← hk_eq] at huP hadj ⊢; rw [hg'_adj] at hadj ⊢; exact ⟨huP, by omega⟩
        · rintro ⟨huP, hadj⟩; obtain ⟨k, rfl⟩ := hex_idx c2 u (Finset.mem_filter.mp huP).2
          let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
          have hk_eq : r2' k' = rep c2 k := by dsimp only [r2', r2, k']; congr 1; ext; dsimp; omega
          rw [← hk_eq] at huP hadj ⊢; rw [hg'_adj] at hadj ⊢; exact ⟨huP, by omega⟩
      have hN1 := hnbhd_eq_iff c0 c2 c1 hc02 hc01 hc12.symm (r0' i1) (hrep_mem c0 _) (r0' i2) (hrep_mem c0 _) hN2
      have hdeq : degNext c0 (r0' i1) = degNext c0 (r0' i2) := by
        dsimp only [degNext]; rw [hn0]; exact congrArg Finset.card hN1
      have hreq := hsame_deg_eq c0 (r0' i1) (r0' i2) (hrep_mem c0 _) (hrep_mem c0 _) hdeq
      have hfin := congrArg Fin.val (hrep_inj c0 hreq); dsimp at hfin; have := i1.isLt; have := i2.isLt; have := Fin.lt_def.mp hlt; omega
    have hh'_sm : ∀ k1 k2 : Fin c, k1 < k2 → h' k1 < h' k2 := by
      intro k1 k2 hlt
      have hle : h' k1 ≤ h' k2 := Nat.sub_le_sub_left (Finset.card_le_card (fun j' hj' =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hj').2; have := Fin.lt_def.mp hlt; omega⟩)) _
      by_contra hnot; have heq : h' k1 = h' k2 := by omega
      have hN1 : (P c1).filter (H.Adj (r2' k1)) = (P c1).filter (H.Adj (r2' k2)) := by
        ext u; simp only [Finset.mem_filter]; constructor
        · rintro ⟨huP, hadj⟩; obtain ⟨j, rfl⟩ := hex_idx c1 u (Finset.mem_filter.mp huP).2
          let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
          have hj_eq : r1' j' = rep c1 j := by dsimp only [r1', r1, j']; congr 1; ext; dsimp; omega
          rw [← hj_eq] at huP hadj ⊢; rw [hh'_adj] at hadj ⊢; exact ⟨huP, by omega⟩
        · rintro ⟨huP, hadj⟩; obtain ⟨j, rfl⟩ := hex_idx c1 u (Finset.mem_filter.mp huP).2
          let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
          have hj_eq : r1' j' = rep c1 j := by dsimp only [r1', r1, j']; congr 1; ext; dsimp; omega
          rw [← hj_eq] at huP hadj ⊢; rw [hh'_adj] at hadj ⊢; exact ⟨huP, by omega⟩
      have hN0 := hnbhd_eq_iff c2 c1 c0 hc12.symm hc02.symm hc01.symm (r2' k1) (hrep_mem c2 _) (r2' k2) (hrep_mem c2 _) hN1
      have hdeq : degNext c2 (r2' k1) = degNext c2 (r2' k2) := by
        dsimp only [degNext]; rw [hn2]; exact congrArg Finset.card hN0
      have hreq := hsame_deg_eq c2 (r2' k1) (r2' k2) (hrep_mem c2 _) (hrep_mem c2 _) hdeq
      have hfin := congrArg Fin.val (hrep_inj c2 hreq); dsimp at hfin; have := k1.isLt; have := k2.isLt; have := Fin.lt_def.mp hlt; omega
    exact hfrom_ordered c1 c0 c2 hc01.symm hc12 hc02 b a c (hsz_pos c1) h10 h02 r1' r0' r2'
      (fun _ => hrep_col c1 _) (fun _ => hrep_col c0 _) (fun _ => hrep_col c2 _)
      (fun x y hxy => by have := congrArg Fin.val (hrep_inj c1 hxy); dsimp at this; exact Fin.ext (by omega))
      (fun x y hxy => by have := congrArg Fin.val (hrep_inj c0 hxy); dsimp at this; exact Fin.ext (by omega))
      (fun x y hxy => by have := congrArg Fin.val (hrep_inj c2 hxy); dsimp at this; exact Fin.ext (by omega))
      (fun u hu => by obtain ⟨j, rfl⟩ := hex_idx c1 u hu; exact ⟨⟨b - 1 - j.val, by omega⟩, by dsimp [r1', r1]; congr 1; ext; dsimp; omega⟩)
      (fun u hu => by obtain ⟨i, rfl⟩ := hex_idx c0 u hu; exact ⟨⟨a - 1 - i.val, by omega⟩, by dsimp [r0', r0]; congr 1; ext; dsimp; omega⟩)
      (fun u hu => by obtain ⟨k, rfl⟩ := hex_idx c2 u hu; exact ⟨⟨c - 1 - k.val, by omega⟩, by dsimp [r2', r2]; congr 1; ext; dsimp; omega⟩)
      f' g' h' (fun _ => Nat.sub_le _ _) (fun _ => Nat.sub_le _ _) (fun _ => Nat.sub_le _ _)
      hf'_sm hg'_sm hh'_sm hf'_adj hg'_adj hh'_adj
  -- Dispatch all 6 orderings of (sz 0, sz 1, sz 2)!
  by_cases h01 : sz 0 ≤ sz 1
  · by_cases h12 : sz 1 ≤ sz 2
    · exact hfrom_ordered 0 1 2 (by decide) (by decide) (by decide) (sz 0) (sz 1) (sz 2) (hsz_pos 0) h01 h12
        (rep 0) (rep 1) (rep 2) (hrep_col 0) (hrep_col 1) (hrep_col 2) (hrep_inj 0) (hrep_inj 1) (hrep_inj 2)
        (hex_idx 0) (hex_idx 1) (hex_idx 2) (thr 0) (thr 1) (thr 2) (hthr_le 0) (hthr_le 1) (hthr_le 2)
        (hthr_sm 0) (hthr_sm 1) (hthr_sm 2) (hthr_iff 0) (hthr_iff 1) (hthr_iff 2)
    · by_cases h02 : sz 0 ≤ sz 2
      · exact hfrom_rev 2 0 1 (by decide) (by decide) (by decide) h02 (by omega) rfl rfl rfl
      · exact hfrom_ordered 2 0 1 (by decide) (by decide) (by decide) (sz 2) (sz 0) (sz 1) (hsz_pos 2) (by omega) h01
          (rep 2) (rep 0) (rep 1) (hrep_col 2) (hrep_col 0) (hrep_col 1) (hrep_inj 2) (hrep_inj 0) (hrep_inj 1)
          (hex_idx 2) (hex_idx 0) (hex_idx 1) (thr 2) (thr 0) (thr 1) (hthr_le 2) (hthr_le 0) (hthr_le 1)
          (hthr_sm 2) (hthr_sm 0) (hthr_sm 1) (hthr_iff 2) (hthr_iff 0) (hthr_iff 1)
  · by_cases h02 : sz 0 ≤ sz 2
    · exact hfrom_rev 0 1 2 (by decide) (by decide) (by decide) (by omega) h02 rfl rfl rfl
    · by_cases h12 : sz 1 ≤ sz 2
      · exact hfrom_ordered 1 2 0 (by decide) (by decide) (by decide) (sz 1) (sz 2) (sz 0) (hsz_pos 1) h12 (by omega)
          (rep 1) (rep 2) (rep 0) (hrep_col 1) (hrep_col 2) (hrep_col 0) (hrep_inj 1) (hrep_inj 2) (hrep_inj 0)
          (hex_idx 1) (hex_idx 2) (hex_idx 0) (thr 1) (thr 2) (thr 0) (hthr_le 1) (hthr_le 2) (hthr_le 0)
          (hthr_sm 1) (hthr_sm 2) (hthr_sm 0) (hthr_iff 1) (hthr_iff 2) (hthr_iff 0)
      · exact hfrom_rev 1 2 0 (by decide) (by decide) (by decide) (by omega) (by omega) rfl rfl rfl



/- ## Section B.1: Lemma 1 (No Induced Q_3) & Lemma 2 (Weighted Stability Cap) -/

/-- Lemma 1 (No Induced `Q_3 = K_{4,4} - M`): valid for ANY weight with `deg_w > 1/3`. -/
lemma no_induced_Q3 {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (hTF : H.CliqueFree 3)
    (hMax : ∀ x y : U, x ≠ y → ¬ H.Adj x y → ∃ z : U, H.Adj x z ∧ H.Adj y z)
    {ω : U → ℝ} (hnn : ∀ v : U, 0 ≤ ω v) (hsum : ∑ v : U, ω v = 1)
    (hdeg : ∀ u : U, (1 / 3 : ℝ) < wdeg H ω u)
    (a b : Fin 4 → U)
    (hab_adj : ∀ i j : Fin 4, i ≠ j → H.Adj (a i) (b j))
    (hab_na : ∀ i : Fin 4, ¬ H.Adj (a i) (b i)) : False := by
  have ha_inj : Function.Injective a := fun i j hij => by
    by_contra hne; exact hab_na i (hij ▸ hab_adj j i (Ne.symm hne))
  have hb_inj : Function.Injective b := fun i j hij => by
    by_contra hne; exact hab_na i (hij ▸ hab_adj i j hne)
  have hother : ∀ i j : Fin 4, ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
    intro i j; fin_cases i <;> fin_cases j <;> first | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩
  have ha_ind : ∀ i j : Fin 4, ¬ H.Adj (a i) (a j) := by
    intro i j hadj
    obtain ⟨k, hki, hkj⟩ := hother i j
    exact tf_contra hTF hadj (hab_adj j k hkj.symm) (hab_adj i k hki.symm)
  have hb_ind : ∀ i j : Fin 4, ¬ H.Adj (b i) (b j) := by
    intro i j hadj
    obtain ⟨k, hki, hkj⟩ := hother i j
    exact tf_contra hTF hadj (hab_adj k j hkj).symm (hab_adj k i hki).symm
  have hab_ne : ∀ i j : Fin 4, a i ≠ b j := by
    intro i j heq
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hki, _⟩ := hother i i
      obtain ⟨m, hmi, hmk⟩ := hother i k
      exact tf_contra hTF (hab_adj m i hmi) (heq ▸ hab_adj i k hki.symm) (hab_adj m k hmk)
    · exact H.ne_of_adj (hab_adj i j hij) heq
  let Z : Fin 4 → Finset U := fun m => Finset.univ.filter (fun z => H.Adj z (a m) ∧ H.Adj z (b m))
  have hZ_ne : ∀ m : Fin 4, (Z m).Nonempty := by
    intro m
    obtain ⟨z, hza, hzb⟩ := hMax (a m) (b m) (hab_ne m m) (hab_na m)
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hza.symm, hzb.symm⟩⟩
  have hZ_na : ∀ (m : Fin 4) (z : U), z ∈ Z m → ∀ j : Fin 4, j ≠ m → ¬ H.Adj z (a j) ∧ ¬ H.Adj z (b j) := by
    intro m z hz j hjm
    have ⟨hza, hzb⟩ := (Finset.mem_filter.mp hz).2
    exact ⟨fun h => tf_contra hTF h (hab_adj j m hjm) hzb,
           fun h => tf_contra hTF h (hab_adj m j hjm.symm).symm hza⟩
  have hZ_disj : ∀ (m1 m2 : Fin 4) (z : U), z ∈ Z m1 → z ∈ Z m2 → m1 = m2 := by
    intro m1 m2 z h1 h2; by_contra hne
    exact (hZ_na m1 z h1 m2 (Ne.symm hne)).1 (Finset.mem_filter.mp h2).2.1
  have hZ_ne_ab : ∀ (m : Fin 4) (z : U), z ∈ Z m → ∀ j : Fin 4, z ≠ a j ∧ z ≠ b j := by
    intro m z hz j
    have ⟨hza, hzb⟩ := (Finset.mem_filter.mp hz).2
    exact ⟨fun heq => by subst heq; exact ha_ind j m hza, fun heq => by subst heq; exact hb_ind j m hzb⟩
  let M : Fin 4 → Fin 4 → Prop := fun i j => i ≠ j ∧ ∃ zi ∈ Z i, ∃ zj ∈ Z j, H.Adj zi zj
  have hM_symm : ∀ i j, M i j → M j i := fun i j ⟨hne, zi, hzi, zj, hzj, hadj⟩ =>
    ⟨hne.symm, zj, hzj, zi, hzi, hadj.symm⟩
  -- Helper: given `z : Fin 4 → U` with `z m ∈ Z m`, count hits of `v` on the 3-tuple `{a m, b m, z m}`.
  have hcap_triple : ∀ (z : Fin 4 → U), (∀ m, z m ∈ Z m) → ∀ (v : U) (m : Fin 4), v ∉ Z m →
      (if H.Adj v (a m) then (1 : ℕ) else 0) + (if H.Adj v (b m) then 1 else 0) + (if H.Adj v (z m) then 1 else 0) ≤ 1 := by
    intro z hz v m hvZ
    have ⟨hza, hzb⟩ := (Finset.mem_filter.mp (hz m)).2
    have hnotboth : ¬ (H.Adj v (a m) ∧ H.Adj v (b m)) := fun h => hvZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    by_cases ha' : H.Adj v (a m) <;> by_cases hb' : H.Adj v (b m) <;> by_cases hz' : H.Adj v (z m)
    · exact (hnotboth ⟨ha', hb'⟩).elim
    · exact (hnotboth ⟨ha', hb'⟩).elim
    · exact (tf_contra hTF ha' hza.symm hz').elim
    · simp [ha', hb', hz']
    · exact (tf_contra hTF hb' hzb.symm hz').elim
    all_goals simp [ha', hb', hz']
  -- Helper: given `z : Fin 4 → U` (`z m ∈ Z m`), form `S12 = {a m, b m, z m | m : Fin 4}` of size 12,
  -- and count hits of `v` via `Fin 4` sum.
  have hcard12_sum : ∀ (z : Fin 4 → U), (∀ m, z m ∈ Z m) →
      ∃ S : Finset U, #S = 12 ∧ S.Nonempty ∧
      ∀ v : U, #(S.filter (H.Adj v)) =
        ∑ m : Fin 4, ((if H.Adj v (a m) then 1 else 0) + (if H.Adj v (b m) then 1 else 0) + (if H.Adj v (z m) then 1 else 0)) := by
    intro z hz
    let f : Fin 4 × Fin 3 → U := fun ⟨m, r⟩ => if r = 0 then a m else if r = 1 then b m else z m
    have hf_inj : Function.Injective f := by
      intro ⟨m1, r1⟩ ⟨m2, r2⟩ heq
      dsimp only [f] at heq
      have h1 : r1 = 0 ∨ r1 = 1 ∨ r1 = 2 := by omega
      have h2 : r2 = 0 ∨ r2 = 1 ∨ r2 = 2 := by omega
      rcases h1 with h | h | h <;> rcases h2 with h' | h' | h' <;> subst h <;> subst h'
      all_goals simp only [Fin.reduceEq, ↓reduceIte] at heq
      · exact Prod.ext (ha_inj heq) rfl
      · exact (hab_ne m1 m2 heq).elim
      · exact ((hZ_ne_ab m2 (z m2) (hz m2) m1).1 heq.symm).elim
      · exact (hab_ne m2 m1 heq.symm).elim
      · exact Prod.ext (hb_inj heq) rfl
      · exact ((hZ_ne_ab m2 (z m2) (hz m2) m1).2 heq.symm).elim
      · exact ((hZ_ne_ab m1 (z m1) (hz m1) m2).1 heq).elim
      · exact ((hZ_ne_ab m1 (z m1) (hz m1) m2).2 heq).elim
      · exact Prod.ext (hZ_disj m1 m2 (z m1) (hz m1) (heq ▸ hz m2)) rfl
    refine ⟨Finset.univ.image f, by rw [Finset.card_image_of_injective _ hf_inj]; simp,
      ⟨f (0, 0), Finset.mem_image_of_mem f (Finset.mem_univ (0, 0))⟩, ?_⟩
    intro v
    have hbij : #((Finset.univ.image f).filter (H.Adj v)) = #(Finset.univ.filter (fun p : Fin 4 × Fin 3 => H.Adj v (f p))) := by
      refine Finset.card_bij (fun u hu => (Finset.mem_image.mp (Finset.mem_filter.mp hu).1).choose) ?_ ?_ ?_
      · intro u hu; have h1 := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_image.mp h1.1).choose_spec.2.symm ▸ h1.2⟩
      · intro u1 hu1 u2 hu2 heq
        have h1 := (Finset.mem_image.mp (Finset.mem_filter.mp hu1).1).choose_spec.2
        have h2 := (Finset.mem_image.mp (Finset.mem_filter.mp hu2).1).choose_spec.2
        rw [← h1, ← h2, heq]
      · intro p hp
        refine ⟨f p, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f (Finset.mem_univ p), (Finset.mem_filter.mp hp).2⟩, ?_⟩
        exact hf_inj (Finset.mem_image.mp (Finset.mem_image_of_mem f (Finset.mem_univ p))).choose_spec.2
    rw [hbij, Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro m _
    rw [Fin.sum_univ_three]; simp [f]
  -- Subcase 1: Matching of size 2 in M
  have hmatch : ∀ i0 i1 i2 i3 : Fin 4, i0 ≠ i1 → i0 ≠ i2 → i0 ≠ i3 → i1 ≠ i2 → i1 ≠ i3 → i2 ≠ i3 →
      M i0 i1 → M i2 i3 → False := by
    have hall4 : ∀ (i0 i1 i2 i3 m : Fin 4), i0 ≠ i1 → i0 ≠ i2 → i0 ≠ i3 → i1 ≠ i2 → i1 ≠ i3 → i2 ≠ i3 →
        m = i0 ∨ m = i1 ∨ m = i2 ∨ m = i3 := by decide
    intro i0 i1 i2 i3 h01 h02 h03 h12 h13 h23 ⟨_, z0, hz0, z1, hz1, hadj01⟩ ⟨_, z2, hz2, z3, hz3, hadj23⟩
    let z : Fin 4 → U := fun m => if m = i0 then z0 else if m = i1 then z1 else if m = i2 then z2 else z3
    have hall : ∀ m : Fin 4, m = i0 ∨ m = i1 ∨ m = i2 ∨ m = i3 :=
      fun m => hall4 i0 i1 i2 i3 m h01 h02 h03 h12 h13 h23
    have hz_mem : ∀ m : Fin 4, z m ∈ Z m := by
      intro m; rcases hall m with rfl | rfl | rfl | rfl
      · simpa [z] using hz0
      · simpa [z, h01.symm] using hz1
      · simpa [z, h02.symm, h12.symm] using hz2
      · simpa [z, h03.symm, h13.symm, h23.symm] using hz3
    have hzi0 : z i0 = z0 := by simp [z]
    have hzi1 : z i1 = z1 := by simp [z, h01.symm]
    have hzi2 : z i2 = z2 := by simp [z, h02.symm, h12.symm]
    have hzi3 : z i3 = z3 := by simp [z, h03.symm, h13.symm, h23.symm]
    obtain ⟨S, hScard, hSne, hSsum⟩ := hcard12_sum z hz_mem
    refine contra_of_capped_set H hnn hsum hdeg S 4 hSne (by omega) (fun v => ?_)
    rw [hSsum v]
    by_cases hex : ∃ m : Fin 4, v ∈ Z m
    · obtain ⟨m, hvm⟩ := hex
      have hterm : ∀ k : Fin 4,
          (if H.Adj v (a k) then 1 else 0) + (if H.Adj v (b k) then 1 else 0) + (if H.Adj v (z k) then 1 else 0) ≤
          (if k = m then 2 else 0) + (if H.Adj v (z k) then 1 else 0) := by
        intro k; by_cases hkm : k = m
        · subst hkm; have := (Finset.mem_filter.mp hvm).2; split_ifs <;> omega
        · have ⟨hna1, hna2⟩ := hZ_na m v hvm k hkm; simp [hkm, hna1, hna2]
      have hsum_le := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
      have h2 : (∑ k : Fin 4, if k = m then (2 : ℕ) else 0) = 2 := by simp
      simp only [Finset.sum_add_distrib, h2] at hsum_le
      simp only [Finset.sum_add_distrib]
      have hpair : ∑ k : Fin 4, (if H.Adj v (z k) then 1 else 0) =
          ((if H.Adj v z0 then 1 else 0) + (if H.Adj v z1 then 1 else 0)) +
          ((if H.Adj v z2 then 1 else 0) + (if H.Adj v z3 then 1 else 0)) := by
        have hperm : (Finset.univ : Finset (Fin 4)) = {i0, i1, i2, i3} := by
          ext k; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]; exact hall k
        rw [hperm, Finset.sum_insert (by simp [h01, h02, h03]), Finset.sum_insert (by simp [h12, h13]),
            Finset.sum_insert (by simp [h23]), Finset.sum_singleton, hzi0, hzi1, hzi2, hzi3]; omega
      have h01' : (if H.Adj v z0 then 1 else 0) + (if H.Adj v z1 then 1 else 0) ≤ 1 := by
        by_cases h1 : H.Adj v z0 <;> by_cases h2 : H.Adj v z1
        · exact (tf_contra hTF h1 hadj01 h2).elim
        all_goals simp [h1, h2]
      have h23' : (if H.Adj v z2 then 1 else 0) + (if H.Adj v z3 then 1 else 0) ≤ 1 := by
        by_cases h1 : H.Adj v z2 <;> by_cases h2 : H.Adj v z3
        · exact (tf_contra hTF h1 hadj23 h2).elim
        all_goals simp [h1, h2]
      omega
    · push Not at hex
      calc ∑ m : Fin 4, ((if H.Adj v (a m) then 1 else 0) + (if H.Adj v (b m) then 1 else 0) + (if H.Adj v (z m) then 1 else 0))
          ≤ ∑ _m : Fin 4, 1 := Finset.sum_le_sum (fun m _ => hcap_triple z hz_mem v m (hex m))
        _ = 4 := by simp
  -- Subcase 2: Isolated vertex in M
  have hisol : ∀ i0 : Fin 4, (∀ j : Fin 4, ¬ M i0 j) → False := by
    have hsum_le4 : ∀ (m i0 : Fin 4),
        (∑ k : Fin 4, if k = m then (2 : ℕ) else if k = i0 then 0 else if m = i0 then 0 else 1) ≤ 4 := by
      decide
    intro i0 hiso
    let z : Fin 4 → U := fun m => (hZ_ne m).choose
    have hz_mem : ∀ m : Fin 4, z m ∈ Z m := fun m => (hZ_ne m).choose_spec
    obtain ⟨S, hScard, hSne, hSsum⟩ := hcard12_sum z hz_mem
    refine contra_of_capped_set H hnn hsum hdeg S 4 hSne (by omega) (fun v => ?_)
    rw [hSsum v]
    by_cases hex : ∃ m : Fin 4, v ∈ Z m
    · obtain ⟨m, hvm⟩ := hex
      have hna_self : ¬ H.Adj v (z m) := fun h =>
        tf_contra hTF (Finset.mem_filter.mp hvm).2.1 (Finset.mem_filter.mp (hz_mem m)).2.1.symm h
      have hterm : ∀ k : Fin 4,
          (if H.Adj v (a k) then 1 else 0) + (if H.Adj v (b k) then 1 else 0) + (if H.Adj v (z k) then 1 else 0) ≤
          (if k = m then 2 else if k = i0 then 0 else if m = i0 then 0 else 1) := by
        intro k; by_cases hkm : k = m
        · subst hkm; simp [hna_self]; split_ifs <;> omega
        · have ⟨hna1, hna2⟩ := hZ_na m v hvm k hkm
          by_cases hki0 : k = i0
          · subst hki0
            have hna0 : ¬ H.Adj v (z k) := fun h => hiso m ⟨hkm, z k, hz_mem k, v, hvm, h.symm⟩
            simp [hkm, hna1, hna2, hna0]
          · by_cases hmi0 : m = i0
            · subst hmi0
              have hnak : ¬ H.Adj v (z k) := fun h => hiso k ⟨Ne.symm hkm, v, hvm, z k, hz_mem k, h⟩
              simp [hkm, hna1, hna2, hnak]
            · simp [hkm, hki0, hmi0, hna1, hna2]; split_ifs <;> omega
      calc ∑ k : Fin 4, _ ≤ ∑ k : Fin 4, (if k = m then 2 else if k = i0 then 0 else if m = i0 then 0 else 1) :=
              Finset.sum_le_sum (fun k _ => hterm k)
        _ ≤ 4 := hsum_le4 m i0
    · push Not at hex
      calc ∑ m : Fin 4, _ ≤ ∑ _m : Fin 4, 1 := Finset.sum_le_sum (fun m _ => hcap_triple z hz_mem v m (hex m))
        _ = 4 := by simp
  -- Subcase 3: Independent 3-set in M
  have hindep3 : ∀ i1 i2 i3 : Fin 4, i1 ≠ i2 → i1 ≠ i3 → i2 ≠ i3 →
      ¬ M i1 i2 → ¬ M i1 i3 → ¬ M i2 i3 → False := by
    intro i1 i2 i3 h12 h13 h23 hn12 hn13 hn23
    let z : Fin 4 → U := fun m => (hZ_ne m).choose
    have hz_mem : ∀ m : Fin 4, z m ∈ Z m := fun m => (hZ_ne m).choose_spec
    let idx : Fin 3 → Fin 4 := ![i1, i2, i3]
    have hidx_inj : Function.Injective idx := by
      intro r1 r2 heq; fin_cases r1 <;> fin_cases r2 <;> simp [idx] at heq ⊢
      all_goals first | exact (h12 heq).elim | exact (h13 heq).elim | exact (h23 heq).elim
                      | exact (h12 heq.symm).elim | exact (h13 heq.symm).elim | exact (h23 heq.symm).elim
    let f : Fin 3 × Fin 3 → U := fun ⟨r, s⟩ => if s = 0 then a (idx r) else if s = 1 then b (idx r) else z (idx r)
    have hf_inj : Function.Injective f := by
      intro ⟨r1, s1⟩ ⟨r2, s2⟩ heq; dsimp only [f] at heq
      have h1 : s1 = 0 ∨ s1 = 1 ∨ s1 = 2 := by omega
      have h2 : s2 = 0 ∨ s2 = 1 ∨ s2 = 2 := by omega
      rcases h1 with h | h | h <;> rcases h2 with h' | h' | h' <;> subst h <;> subst h'
      all_goals simp only [Fin.reduceEq, ↓reduceIte] at heq
      · exact Prod.ext (hidx_inj (ha_inj heq)) rfl
      · exact (hab_ne _ _ heq).elim
      · exact ((hZ_ne_ab _ _ (hz_mem _) _).1 heq.symm).elim
      · exact (hab_ne _ _ heq.symm).elim
      · exact Prod.ext (hidx_inj (hb_inj heq)) rfl
      · exact ((hZ_ne_ab _ _ (hz_mem _) _).2 heq.symm).elim
      · exact ((hZ_ne_ab _ _ (hz_mem _) _).1 heq).elim
      · exact ((hZ_ne_ab _ _ (hz_mem _) _).2 heq).elim
      · exact Prod.ext (hidx_inj (hZ_disj _ _ _ (hz_mem _) (heq ▸ hz_mem _))) rfl
    let S := Finset.univ.image f
    have hScard : #S = 9 := by rw [Finset.card_image_of_injective _ hf_inj]; simp
    refine contra_of_capped_set H hnn hsum hdeg S 3 ⟨f (0, 0), Finset.mem_image_of_mem f (Finset.mem_univ (0, 0))⟩ (by omega) (fun v => ?_)
    have hbij : #(S.filter (H.Adj v)) = #(Finset.univ.filter (fun p : Fin 3 × Fin 3 => H.Adj v (f p))) := by
      refine Finset.card_bij (fun u hu => (Finset.mem_image.mp (Finset.mem_filter.mp hu).1).choose) ?_ ?_ ?_
      · intro u hu; have h1 := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_image.mp h1.1).choose_spec.2.symm ▸ h1.2⟩
      · intro u1 hu1 u2 hu2 heq
        have h1 := (Finset.mem_image.mp (Finset.mem_filter.mp hu1).1).choose_spec.2
        have h2 := (Finset.mem_image.mp (Finset.mem_filter.mp hu2).1).choose_spec.2
        rw [← h1, ← h2, heq]
      · intro p hp
        refine ⟨f p, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f (Finset.mem_univ p), (Finset.mem_filter.mp hp).2⟩, ?_⟩
        exact hf_inj (Finset.mem_image.mp (Finset.mem_image_of_mem f (Finset.mem_univ p))).choose_spec.2
    rw [hbij, Finset.card_filter, Fintype.sum_prod_type]
    have hnoM : ∀ r1 r2 : Fin 3, ¬ M (idx r1) (idx r2) := by
      intro r1 r2; fin_cases r1 <;> fin_cases r2 <;> simp [idx]
      · exact fun h => h.1 rfl
      · exact hn12
      · exact hn13
      · exact fun h => hn12 (hM_symm _ _ h)
      · exact fun h => h.1 rfl
      · exact hn23
      · exact fun h => hn13 (hM_symm _ _ h)
      · exact fun h => hn23 (hM_symm _ _ h)
      · exact fun h => h.1 rfl
    by_cases hex : ∃ r : Fin 3, v ∈ Z (idx r)
    · obtain ⟨r0, hvr0⟩ := hex
      have hterm : ∀ r : Fin 3, ∑ s : Fin 3, (if H.Adj v (f (r, s)) then 1 else 0) ≤ if r = r0 then 2 else 0 := by
        intro r; rw [Fin.sum_univ_three]; simp only [f, Fin.isValue, ↓reduceIte, Fin.reduceEq]
        by_cases hrr : r = r0
        · subst hrr
          have hna_z : ¬ H.Adj v (z (idx r)) := fun h =>
            tf_contra hTF (Finset.mem_filter.mp hvr0).2.1 (Finset.mem_filter.mp (hz_mem (idx r))).2.1.symm h
          simp [hna_z]; split_ifs <;> omega
        · have hne : idx r ≠ idx r0 := fun h => hrr (hidx_inj h)
          have ⟨hna1, hna2⟩ := hZ_na (idx r0) v hvr0 (idx r) hne
          have hna3 : ¬ H.Adj v (z (idx r)) := fun h => hnoM r0 r ⟨hne.symm, v, hvr0, z (idx r), hz_mem (idx r), h⟩
          simp [hrr, hna1, hna2, hna3]
      calc ∑ r : Fin 3, ∑ s : Fin 3, (if H.Adj v (f (r, s)) then 1 else 0)
          ≤ ∑ r : Fin 3, (if r = r0 then 2 else 0) := Finset.sum_le_sum (fun r _ => hterm r)
        _ = 2 := by rw [Finset.sum_ite_eq' Finset.univ r0]; simp
        _ ≤ 3 := by omega
    · push Not at hex
      calc ∑ r : Fin 3, ∑ s : Fin 3, (if H.Adj v (f (r, s)) then 1 else 0)
          ≤ ∑ _r : Fin 3, 1 := Finset.sum_le_sum (fun r _ => by
            rw [Fin.sum_univ_three]; simpa [f] using hcap_triple z hz_mem v (idx r) (hex r))
        _ = 3 := by simp
  -- Dispatch on 4-vertex graph M: matching-2, independent 3-set, or isolated vertex
  have hM_irr : ∀ i : Fin 4, ¬ M i i := fun i h => h.1 rfl
  have hiso_of : ∀ (i0 : Fin 4), ¬ M i0 0 → ¬ M i0 1 → ¬ M i0 2 → ¬ M i0 3 → ∀ j : Fin 4, ¬ M i0 j := by
    intro i0 h0 h1 h2 h3 j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  by_cases h01 : M 0 1 <;> by_cases h02 : M 0 2 <;> by_cases h03 : M 0 3 <;> by_cases h12 : M 1 2 <;> by_cases h13 : M 1 3 <;> by_cases h23 : M 2 3
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hmatch 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h03 h12
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hindep3 1 2 3 (by decide) (by decide) (by decide) h12 h13 h23
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hisol 3 (hiso_of 3 (fun h => h03 (hM_symm 3 0 h)) (fun h => h13 (hM_symm 3 1 h)) (fun h => h23 (hM_symm 3 2 h)) (hM_irr 3))
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hindep3 1 2 3 (by decide) (by decide) (by decide) h12 h13 h23
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hmatch 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h03 h12
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hmatch 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h03 h12
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hisol 2 (hiso_of 2 (fun h => h02 (hM_symm 2 0 h)) (fun h => h12 (hM_symm 2 1 h)) (hM_irr 2) h23)
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hindep3 1 2 3 (by decide) (by decide) (by decide) h12 h13 h23
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hindep3 0 2 3 (by decide) (by decide) (by decide) h02 h03 h23
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hindep3 0 2 3 (by decide) (by decide) (by decide) h02 h03 h23
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hindep3 0 2 3 (by decide) (by decide) (by decide) h02 h03 h23
  · exact hmatch 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h01 h23
  · exact hindep3 1 2 3 (by decide) (by decide) (by decide) h12 h13 h23
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hmatch 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h03 h12
  · exact hmatch 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h03 h12
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hisol 1 (hiso_of 1 (fun h => h01 (hM_symm 1 0 h)) (hM_irr 1) h12 h13)
  · exact hindep3 1 2 3 (by decide) (by decide) (by decide) h12 h13 h23
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hindep3 0 1 3 (by decide) (by decide) (by decide) h01 h03 h13
  · exact hindep3 0 1 3 (by decide) (by decide) (by decide) h01 h03 h13
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hmatch 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h02 h13
  · exact hindep3 0 1 3 (by decide) (by decide) (by decide) h01 h03 h13
  · exact hindep3 1 2 3 (by decide) (by decide) (by decide) h12 h13 h23
  · exact hmatch 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h03 h12
  · exact hmatch 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h03 h12
  · exact hmatch 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h03 h12
  · exact hmatch 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h03 h12
  · exact hindep3 0 1 2 (by decide) (by decide) (by decide) h01 h02 h12
  · exact hindep3 0 1 2 (by decide) (by decide) (by decide) h01 h02 h12
  · exact hindep3 0 1 2 (by decide) (by decide) (by decide) h01 h02 h12
  · exact hindep3 1 2 3 (by decide) (by decide) (by decide) h12 h13 h23
  · exact hisol 0 (hiso_of 0 (hM_irr 0) h01 h02 h03)
  · exact hindep3 0 2 3 (by decide) (by decide) (by decide) h02 h03 h23
  · exact hindep3 0 1 3 (by decide) (by decide) (by decide) h01 h03 h13
  · exact hindep3 0 2 3 (by decide) (by decide) (by decide) h02 h03 h23
  · exact hindep3 0 1 2 (by decide) (by decide) (by decide) h01 h02 h12
  · exact hindep3 0 2 3 (by decide) (by decide) (by decide) h02 h03 h23
  · exact hindep3 0 1 3 (by decide) (by decide) (by decide) h01 h03 h13
  · exact hindep3 1 2 3 (by decide) (by decide) (by decide) h12 h13 h23

/-- Reusable helper for Lemma 2 and Claim 1: a minimal `P`-undominated set `T` has `#T ≤ 3`. -/
lemma card_le_three_of_minimal_inter {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (hTF : H.CliqueFree 3)
    (hMax : ∀ x y : U, x ≠ y → ¬ H.Adj x y → ∃ z : U, H.Adj x z ∧ H.Adj y z)
    {ω : U → ℝ} (hnn : ∀ v : U, 0 ≤ ω v) (hsum : ∑ v : U, ω v = 1)
    (hdeg : ∀ u : U, (1 / 3 : ℝ) < wdeg H ω u)
    (P : U → Prop) (T : Finset U)
    (hundom : ∀ u : U, P u → ∃ t ∈ T, ¬ H.Adj t u)
    (hmin : ∀ t ∈ T, ∃ u : U, P u ∧ ∀ t' ∈ T, t' ≠ t → H.Adj t' u) :
    #T ≤ 3 := by
  by_contra hgt
  obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq (show 4 ≤ #T by omega)
  let e := S.equivFinOfCardEq hScard
  let a : Fin 4 → U := fun i => (e.symm i).1
  have ha_mem : ∀ i : Fin 4, a i ∈ T := fun i => hST (e.symm i).2
  have ha_inj : Function.Injective a := fun i j hij => e.symm.injective (Subtype.ext hij)
  let b : Fin 4 → U := fun i => (hmin (a i) (ha_mem i)).choose
  have hb_P : ∀ i : Fin 4, P (b i) := fun i => (hmin (a i) (ha_mem i)).choose_spec.1
  have hb_dom : ∀ i : Fin 4, ∀ t' ∈ T, t' ≠ a i → H.Adj t' (b i) := fun i => (hmin (a i) (ha_mem i)).choose_spec.2
  have hab_adj : ∀ i j : Fin 4, i ≠ j → H.Adj (a i) (b j) :=
    fun i j hij => hb_dom j (a i) (ha_mem i) (fun h => hij (ha_inj h))
  have hab_na : ∀ i : Fin 4, ¬ H.Adj (a i) (b i) := by
    intro i hadj
    obtain ⟨t, htT, hna⟩ := hundom (b i) (hb_P i)
    by_cases hteq : t = a i
    · exact hna (hteq ▸ hadj)
    · exact hna (hb_dom i t htT hteq)
  exact no_induced_Q3 H hTF hMax hnn hsum hdeg a b hab_adj hab_na

/-- Lemma 2 (Weighted Stability Cap): in a regular good graph, every independent set has weight `≤ δ`. -/
lemma indep_weight_le_delta {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (hTF : H.CliqueFree 3)
    (hMax : ∀ x y : U, x ≠ y → ¬ H.Adj x y → ∃ z : U, H.Adj x z ∧ H.Adj y z)
    {ω : U → ℝ} {δ : ℝ} (hpos : ∀ v : U, 0 < ω v) (hsum : ∑ v : U, ω v = 1)
    (hreg : ∀ u : U, wdeg H ω u = δ) (hδ : (1 / 3 : ℝ) < δ)
    (S : Finset U) (hInd : ∀ u ∈ S, ∀ v ∈ S, ¬ H.Adj u v) :
    wsum ω S ≤ δ := by
  have hnn : ∀ v, 0 ≤ ω v := fun v => le_of_lt (hpos v)
  have hdeg : ∀ u, (1 / 3 : ℝ) < wdeg H ω u := fun u => by rw [hreg u]; exact hδ
  let Inds : Finset (Finset U) := Finset.univ.filter (fun A => ∀ u ∈ A, ∀ v ∈ A, ¬ H.Adj u v)
  have hS_in : S ∈ Inds := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hInd⟩
  obtain ⟨S0, hS0_in, hS0_max⟩ := Finset.exists_max_image Inds (wsum ω) ⟨S, hS_in⟩
  have hS0_ind : ∀ u ∈ S0, ∀ v ∈ S0, ¬ H.Adj u v := (Finset.mem_filter.mp hS0_in).2
  suffices hle : wsum ω S0 ≤ δ from (hS0_max S hS_in).trans hle
  by_cases hdom : ∃ v : U, ∀ s ∈ S0, H.Adj v s
  · obtain ⟨v, hv⟩ := hdom
    have hsub : S0 ⊆ Finset.univ.filter (H.Adj v) := fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv s hs⟩
    calc wsum ω S0 ≤ ∑ u ∈ Finset.univ.filter (H.Adj v), ω u := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hnn u)
      _ = wdeg H ω v := by simp only [wdeg, Finset.sum_filter]
      _ = δ := hreg v
  · exfalso
    push Not at hdom
    have hundom0 : ∀ u : U, ∃ s ∈ S0, ¬ H.Adj s u := fun u => by
      obtain ⟨s, hs, hna⟩ := hdom u; exact ⟨s, hs, fun h => hna h.symm⟩
    let Cands := S0.powerset.filter (fun T => ∀ u : U, ∃ t ∈ T, ¬ H.Adj t u)
    have hS0_cand : S0 ∈ Cands := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Subset.refl _), hundom0⟩
    obtain ⟨T, hT_in, hT_min⟩ := Finset.exists_min_image Cands Finset.card ⟨S0, hS0_cand⟩
    have hT_sub : T ⊆ S0 := Finset.mem_powerset.mp (Finset.mem_filter.mp hT_in).1
    have hT_undom : ∀ u : U, ∃ t ∈ T, ¬ H.Adj t u := (Finset.mem_filter.mp hT_in).2
    have hT_min' : ∀ t ∈ T, ∃ u : U, True ∧ ∀ t' ∈ T, t' ≠ t → H.Adj t' u := by
      intro t ht
      have hnot : T.erase t ∉ Cands := by
        intro hmem; have := hT_min (T.erase t) hmem; have := Finset.card_erase_lt_of_mem ht; omega
      have hpow : T.erase t ∈ S0.powerset := Finset.mem_powerset.mpr ((Finset.erase_subset t T).trans hT_sub)
      have hex : ¬ ∀ u : U, ∃ t' ∈ T.erase t, ¬ H.Adj t' u := fun h => hnot (Finset.mem_filter.mpr ⟨hpow, h⟩)
      push Not at hex; obtain ⟨u, hu⟩ := hex
      exact ⟨u, trivial, fun t' ht' hne => hu t' (Finset.mem_erase.mpr ⟨hne, ht'⟩)⟩
    have hT_le3 : #T ≤ 3 :=
      card_le_three_of_minimal_inter H hTF hMax hnn hsum hdeg (fun _ => True) T (fun u _ => hT_undom u) hT_min'
    have hU_ne : Nonempty U := by
      by_contra hempty; rw [not_nonempty_iff] at hempty
      have : ∑ v : U, ω v = 0 := Finset.sum_eq_zero (fun x _ => (hempty.false x).elim)
      linarith
    have hT_ne0 : #T ≠ 0 := by
      intro h0; obtain ⟨u0⟩ := hU_ne; obtain ⟨t, ht, _⟩ := hT_undom u0
      rw [Finset.card_eq_zero.mp h0] at ht; exact Finset.notMem_empty t ht
    have hT_ne1 : #T ≠ 1 := by
      intro h1; obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      have hna : ∀ u : U, ¬ H.Adj a u := fun u => by
        obtain ⟨t, ht, h⟩ := hT_undom u; rw [Finset.mem_singleton.mp ht] at h; exact h
      have : wdeg H ω a = 0 := by simp [wdeg, hna]
      linarith [hreg a]
    have hT_ne2 : #T ≠ 2 := by
      intro h2; obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
      have hna : ¬ H.Adj a b := hS0_ind a (hT_sub (by simp)) b (hT_sub (by simp))
      obtain ⟨z, hza, hzb⟩ := hMax a b hab hna
      obtain ⟨t, ht, hnt⟩ := hT_undom z
      rcases Finset.mem_insert.mp ht with rfl | ht2
      · exact hnt hza
      · exact hnt (Finset.mem_singleton.mp ht2 ▸ hzb)
    have hT_eq3 : #T = 3 := by omega
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT_eq3
    let R := Finset.univ.filter (fun v : U => (H.Adj v a ∧ H.Adj v b) ∨ (H.Adj v b ∧ H.Adj v c) ∨ (H.Adj v c ∧ H.Adj v a))
    have hR_ind : ∀ u ∈ R, ∀ v ∈ R, ¬ H.Adj u v := by
      intro u hu v hv hadj
      have hu' := (Finset.mem_filter.mp hu).2; have hv' := (Finset.mem_filter.mp hv).2
      rcases hu' with ⟨hua, hub⟩ | ⟨hub, huc⟩ | ⟨huc, hua⟩ <;> rcases hv' with ⟨hva, hvb⟩ | ⟨hvb, hvc⟩ | ⟨hvc, hva⟩
      all_goals first | exact tf_contra hTF hadj hva hua | exact tf_contra hTF hadj hvb hub | exact tf_contra hTF hadj hvc huc
    have hR_le : wsum ω R ≤ wsum ω S0 := hS0_max R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR_ind⟩)
    have hRS_disj : Disjoint R S0 := Finset.disjoint_left.mpr fun v hvR hvS => by
      have hv' := (Finset.mem_filter.mp hvR).2
      rcases hv' with ⟨hva, _⟩ | ⟨hvb, _⟩ | ⟨hvc, _⟩
      · exact hS0_ind v hvS a (hT_sub (by simp)) hva
      · exact hS0_ind v hvS b (hT_sub (by simp)) hvb
      · exact hS0_ind v hvS c (hT_sub (by simp)) hvc
    have hsum_deg : ∑ u ∈ ({a, b, c} : Finset U), wdeg H ω u = 3 * δ := by
      rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]), Finset.sum_singleton,
          hreg a, hreg b, hreg c]; ring
    rw [sum_wdeg_eq_sum_hits] at hsum_deg
    have hcap : ∀ v : U, (#(({a, b, c} : Finset U).filter (H.Adj v)) : ℝ) ≤
        1 + (if v ∈ R then (1 : ℝ) else 0) - (if v ∈ S0 then (1 : ℝ) else 0) := by
      intro v
      have hcnt : #(({a, b, c} : Finset U).filter (H.Adj v)) =
          (if H.Adj v a then 1 else 0) + (if H.Adj v b then 1 else 0) + (if H.Adj v c then 1 else 0) := by
        rw [Finset.card_filter, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]), Finset.sum_singleton]; omega
      rw [hcnt]
      have hnot3 : ¬ (H.Adj v a ∧ H.Adj v b ∧ H.Adj v c) := by
        rintro ⟨h1, h2, h3⟩; obtain ⟨t, ht, hnt⟩ := hT_undom v
        rcases Finset.mem_insert.mp ht with rfl | ht2
        · exact hnt h1.symm
        · rcases Finset.mem_insert.mp ht2 with rfl | ht3
          · exact hnt h2.symm
          · exact hnt (Finset.mem_singleton.mp ht3 ▸ h3.symm)
      by_cases hvR : v ∈ R
      · have hvS : v ∉ S0 := Finset.disjoint_left.mp hRS_disj hvR
        simp only [hvR, hvS, ↓reduceIte, sub_zero]
        have : (if H.Adj v a then (1 : ℕ) else 0) + (if H.Adj v b then 1 else 0) + (if H.Adj v c then 1 else 0) ≤ 2 := by
          by_cases h1 : H.Adj v a <;> by_cases h2 : H.Adj v b <;> by_cases h3 : H.Adj v c
          · exact (hnot3 ⟨h1, h2, h3⟩).elim
          all_goals simp [h1, h2, h3]
        exact_mod_cast this
      · by_cases hvS : v ∈ S0
        · have hna : ¬ H.Adj v a ∧ ¬ H.Adj v b ∧ ¬ H.Adj v c :=
            ⟨hS0_ind v hvS a (hT_sub (by simp)), hS0_ind v hvS b (hT_sub (by simp)), hS0_ind v hvS c (hT_sub (by simp))⟩
          simp [hvR, hvS, hna.1, hna.2.1, hna.2.2]
        · simp only [hvR, hvS, ↓reduceIte, add_zero, sub_zero]
          have hnot2 : ¬ ((H.Adj v a ∧ H.Adj v b) ∨ (H.Adj v b ∧ H.Adj v c) ∨ (H.Adj v c ∧ H.Adj v a)) :=
            fun h => hvR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have : (if H.Adj v a then (1 : ℕ) else 0) + (if H.Adj v b then 1 else 0) + (if H.Adj v c then 1 else 0) ≤ 1 := by
            by_cases h1 : H.Adj v a <;> by_cases h2 : H.Adj v b <;> by_cases h3 : H.Adj v c
            all_goals simp_all
          exact_mod_cast this
    have hle1 : 3 * δ ≤ 1 + wsum ω R - wsum ω S0 := by
      calc 3 * δ = ∑ v : U, (#(({a, b, c} : Finset U).filter (H.Adj v)) : ℝ) * ω v := hsum_deg.symm
        _ ≤ ∑ v : U, (1 + (if v ∈ R then (1 : ℝ) else 0) - (if v ∈ S0 then (1 : ℝ) else 0)) * ω v :=
            Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right (hcap v) (hnn v))
        _ = (∑ v : U, ω v) + (∑ v : U, if v ∈ R then ω v else 0) - (∑ v : U, if v ∈ S0 then ω v else 0) := by
            simp only [sub_mul, add_mul, one_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        _ = 1 + wsum ω R - wsum ω S0 := by
            rw [hsum, ← Finset.sum_filter, ← Finset.sum_filter]; simp [wsum]
    linarith

/-- Permutation of the eight frame slots induced by `π : Equiv.Perm (Fin 3)`: slot `0` (`x`) and
    slot `1` (`y`) stay put, while the a-slots `2,3,4` and the u-slots `5,6,7` are permuted by `π`. -/
def framePerm (π : Equiv.Perm (Fin 3)) : Fin 8 → Fin 8 := fun p =>
  if p.val = 0 then 0 else if p.val = 1 then 1
  else if p.val = 2 then ⟨2 + (π 0).val, by omega⟩
  else if p.val = 3 then ⟨2 + (π 1).val, by omega⟩
  else if p.val = 4 then ⟨2 + (π 2).val, by omega⟩
  else if p.val = 5 then ⟨5 + (π 0).val, by omega⟩
  else if p.val = 6 then ⟨5 + (π 1).val, by omega⟩
  else ⟨5 + (π 2).val, by omega⟩

/-- Inverse of `framePerm`: the induced permutation of `π.symm`. -/
def framePermInv (π : Equiv.Perm (Fin 3)) : Fin 8 → Fin 8 := fun p =>
  if p.val = 0 then 0 else if p.val = 1 then 1
  else if p.val = 2 then ⟨2 + (π.symm 0).val, by omega⟩
  else if p.val = 3 then ⟨2 + (π.symm 1).val, by omega⟩
  else if p.val = 4 then ⟨2 + (π.symm 2).val, by omega⟩
  else if p.val = 5 then ⟨5 + (π.symm 0).val, by omega⟩
  else if p.val = 6 then ⟨5 + (π.symm 1).val, by omega⟩
  else ⟨5 + (π.symm 2).val, by omega⟩

/- ## Section B.1: Lemma 1 (No Induced Q_3) & Lemma 2 (Weighted Stability Cap) -/

/- ## Section B.2: Reusable Step 14 Dispatch (`vega_of_singleton_frame`) -/

/-- Given a `Q_3^+` (or `Q_3^+ - y`) singleton frame `(xf, yf?, af, bf, cf, uf, vf, wf)` and three
    nonempty disjoint independent sets `J : Fin 3 → Finset U` partitioning the remaining vertices
    with exact `Q_3^+ ↔ J` adjacencies, Step 14 classifies `H` directly into `IsVegaGraph H i dy de`! -/
lemma vega_of_singleton_frame {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (hTF : H.CliqueFree 3)
    (hMax : ∀ x y : U, x ≠ y → ¬ H.Adj x y → ∃ z : U, H.Adj x z ∧ H.Adj y z)
    (hTwin : ∀ x y : U, (∀ z : U, H.Adj x z ↔ H.Adj y z) → x = y)
    {ω : U → ℝ} (hnn : ∀ v : U, 0 ≤ ω v) (hsum : ∑ v : U, ω v = 1)
    (hdeg : ∀ u : U, (1 / 3 : ℝ) < wdeg H ω u)
    (xf : U) (yf : Option U) (af uf : Fin 3 → U) (J : Fin 3 → Finset U)
    (hJ_ne : ∀ r : Fin 3, (J r).Nonempty)
    (hJ_ind : ∀ r : Fin 3, ∀ z1 ∈ J r, ∀ z2 ∈ J r, ¬ H.Adj z1 z2)
    (hJ_disj : ∀ r1 r2 : Fin 3, r1 ≠ r2 → Disjoint (J r1) (J r2))
    -- Exact vertex map `qOf : Fin 8 → Option U` (0=xf, 1=yf, 2..4=af 0..2, 5..7=uf 0..2)
    (hq_inj : ∀ (p q : Fin 8) (up uq : U),
      (match p.val with | 0 => some xf | 1 => yf | 2 => some (af 0) | 3 => some (af 1) | 4 => some (af 2)
                        | 5 => some (uf 0) | 6 => some (uf 1) | _ => some (uf 2)) = some up →
      (match q.val with | 0 => some xf | 1 => yf | 2 => some (af 0) | 3 => some (af 1) | 4 => some (af 2)
                        | 5 => some (uf 0) | 6 => some (uf 1) | _ => some (uf 2)) = some uq →
      up = uq → p = q)
    (hq_disj_J : ∀ (p : Fin 8) (up : U),
      (match p.val with | 0 => some xf | 1 => yf | 2 => some (af 0) | 3 => some (af 1) | 4 => some (af 2)
                        | 5 => some (uf 0) | 6 => some (uf 1) | _ => some (uf 2)) = some up →
      ∀ r : Fin 3, up ∉ J r)
    (hcover : ∀ z : U,
      (∃ p : Fin 8, (match p.val with
                        | 0 => some xf | 1 => yf | 2 => some (af 0) | 3 => some (af 1) | 4 => some (af 2)
                        | 5 => some (uf 0) | 6 => some (uf 1) | _ => some (uf 2)) = some z) ∨
      (∃ r : Fin 3, z ∈ J r))
    (hqq_adj : ∀ (p q : Fin 8) (up uq : U),
      (match p.val with | 0 => some xf | 1 => yf | 2 => some (af 0) | 3 => some (af 1) | 4 => some (af 2)
                        | 5 => some (uf 0) | 6 => some (uf 1) | _ => some (uf 2)) = some up →
      (match q.val with | 0 => some xf | 1 => yf | 2 => some (af 0) | 3 => some (af 1) | 4 => some (af 2)
                        | 5 => some (uf 0) | 6 => some (uf 1) | _ => some (uf 2)) = some uq →
      (H.Adj up uq ↔ vegaAdj 2 (.inr p) (.inr q)))
    (hqJ_adj : ∀ (p : Fin 8) (up : U),
      (match p.val with | 0 => some xf | 1 => yf | 2 => some (af 0) | 3 => some (af 1) | 4 => some (af 2)
                        | 5 => some (uf 0) | 6 => some (uf 1) | _ => some (uf 2)) = some up →
      ∀ (r : Fin 3) (z : U), z ∈ J r →
      (H.Adj up z ↔ (p.val = 2 + r.val ∨ p.val = 5 + r.val))) :
    ∃ (i : ℕ) (dy de : Bool), IsVegaGraph H i dy de := by
  let qOf : Fin 8 → Option U := fun p =>
    match p.val with | 0 => some xf | 1 => yf | 2 => some (af 0) | 3 => some (af 1) | 4 => some (af 2)
                     | 5 => some (uf 0) | 6 => some (uf 1) | _ => some (uf 2)
  let ΓS : Finset U := J 0 ∪ J 1 ∪ J 2
  have hmem_ΓS : ∀ z : U, z ∈ ΓS ↔ ∃ r : Fin 3, z ∈ J r := by
    intro z; simp only [ΓS, Finset.mem_union]; constructor
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    · rintro ⟨r, hr⟩; rcases fin3_cases r with rfl | rfl | rfl <;> simp [hr]
  let ΓT := {z : U // z ∈ ΓS}
  let HΓ : SimpleGraph ΓT := H.induce (fun z => z ∈ ΓS)
  have : DecidableRel HΓ.Adj := fun a b => by change Decidable (H.Adj a.1 b.1); infer_instance
  let col : ΓT → Fin 3 := fun z => if z.1 ∈ J 0 then 0 else if z.1 ∈ J 1 then 1 else 2
  have hcol_iff : ∀ (z : ΓT) (r : Fin 3), col z = r ↔ z.1 ∈ J r := by
    intro z r
    obtain ⟨r0, hr0⟩ := (hmem_ΓS z.1).mp z.2
    have hdisj_ne : ∀ r1 r2 : Fin 3, z.1 ∈ J r1 → z.1 ∈ J r2 → r1 = r2 := fun r1 r2 h1 h2 => by
      by_contra hne; exact Finset.disjoint_left.mp (hJ_disj r1 r2 hne) h1 h2
    have hcol_eq : col z = r0 := by
      dsimp only [col]
      rcases fin3_cases r0 with rfl | rfl | rfl
      · simp [hr0]
      · have h0 : z.1 ∉ J 0 := fun h => absurd (hdisj_ne 0 1 h hr0) (by decide)
        simp [h0, hr0]
      · have h0 : z.1 ∉ J 0 := fun h => absurd (hdisj_ne 0 2 h hr0) (by decide)
        have h1 : z.1 ∉ J 1 := fun h => absurd (hdisj_ne 1 2 h hr0) (by decide)
        simp [h0, h1]
    rw [hcol_eq]; exact ⟨fun h => h ▸ hr0, fun h => hdisj_ne r0 r hr0 h⟩
  have hΓ_TF : HΓ.CliqueFree 3 := by
    intro s hs; obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
    have h1 := hs.1; simp only [SimpleGraph.IsClique, Set.Pairwise, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at h1
    exact tf_contra hTF (h1 (Or.inl rfl) (Or.inr (Or.inl rfl)) hab)
      (h1 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hbc)
      (h1 (Or.inl rfl) (Or.inr (Or.inr rfl)) hac)
  have hΓ_col : ∀ u v : ΓT, HΓ.Adj u v → col u ≠ col v := by
    intro u v hadj heq
    exact hJ_ind (col u) u.1 ((hcol_iff u _).mp rfl) v.1 ((hcol_iff v _).mp heq.symm) hadj
  have hΓ_cross : ∀ u v : ΓT, col u ≠ col v → ¬ HΓ.Adj u v → ∃ w : ΓT, HΓ.Adj u w ∧ HΓ.Adj v w := by
    intro u v hne hna
    have hu_ne_v : u.1 ≠ v.1 := fun h => hne (congrArg col (Subtype.ext h))
    obtain ⟨w, hwu, hwv⟩ := hMax u.1 v.1 hu_ne_v hna
    rcases hcover w with ⟨p, hp⟩ | ⟨r, hr⟩
    · exfalso
      have h1 := (hqJ_adj p w hp (col u) u.1 ((hcol_iff u _).mp rfl)).mp hwu.symm
      have h2 := (hqJ_adj p w hp (col v) v.1 ((hcol_iff v _).mp rfl)).mp hwv.symm
      have : (col u).val = (col v).val := by omega
      exact hne (Fin.ext this)
    · exact ⟨⟨w, (hmem_ΓS w).mpr ⟨r, hr⟩⟩, hwu, hwv⟩
  have hΓ_twin : ∀ u v : ΓT, col u = col v → (∀ w : ΓT, HΓ.Adj u w ↔ HΓ.Adj v w) → u = v := by
    intro u v hceq hiff
    apply Subtype.ext; apply hTwin u.1 v.1; intro w
    rcases hcover w with ⟨p, hp⟩ | ⟨r, hr⟩
    · rw [H.adj_comm, H.adj_comm v.1, hqJ_adj p w hp (col u) u.1 ((hcol_iff u _).mp rfl),
          hqJ_adj p w hp (col v) v.1 ((hcol_iff v _).mp rfl), hceq]
    · exact hiff ⟨w, (hmem_ΓS w).mpr ⟨r, hr⟩⟩
  have hΓ_no2K2 : ∀ c1 c2 : Fin 3, c1 ≠ c2 → ∀ x1 x2 y1 y2 : ΓT,
      col x1 = c1 → col x2 = c1 → col y1 = c2 → col y2 = c2 →
      HΓ.Adj x1 y1 → HΓ.Adj x2 y2 → ¬ HΓ.Adj x1 y2 → ¬ HΓ.Adj x2 y1 → False := by
    intro c1 c2 hc12 x1 x2 y1 y2 hx1 hx2 hy1 hy2 h11 h22 hn12 hn21
    obtain ⟨z1, hz1x1, hz1y2⟩ := hΓ_cross x1 y2 (by rw [hx1, hy2]; exact hc12) hn12
    obtain ⟨z2, hz2x2, hz2y1⟩ := hΓ_cross x2 y1 (by rw [hx2, hy1]; exact hc12) hn21
    have hcz1 : col z1 ≠ c1 ∧ col z1 ≠ c2 :=
      ⟨fun h => hΓ_col _ _ hz1x1 (hx1.trans h.symm), fun h => hΓ_col _ _ hz1y2 (hy2.trans h.symm)⟩
    have hcz2 : col z2 ≠ c1 ∧ col z2 ≠ c2 := ⟨fun h => hΓ_col _ _ hz2x2 (hx2.trans h.symm),
      fun h => hΓ_col _ _ hz2y1 (hy1.trans h.symm)⟩
    have hcz_eq : col z1 = col z2 := by
      have hc3 : ∃ c3 : Fin 3, c3 ≠ c1 ∧ c3 ≠ c2 := by rcases fin3_cases c1 with rfl | rfl | rfl <;> rcases fin3_cases c2 with rfl | rfl | rfl <;> first | exact absurd rfl hc12 | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩
      obtain ⟨c3, h31, h32⟩ := hc3
      have h1 : col z1 = c3 := OMA.R_Erdos128_erdos_128_R2.fin3_third hc12 h31.symm h32.symm hcz1.1 hcz1.2
      have h2 : col z2 = c3 := OMA.R_Erdos128_erdos_128_R2.fin3_third hc12 h31.symm h32.symm hcz2.1 hcz2.2
      exact h1.trans h2.symm
    have hx_ne : x1.1 ≠ x2.1 := fun h => hn12 (Subtype.ext h ▸ h22)
    have hy_ne : y1.1 ≠ y2.1 := fun h => hn12 (Subtype.ext h ▸ h11)
    have hz_ne : z1.1 ≠ z2.1 := fun h => tf_contra hTF h11 hz2y1 (Subtype.ext h ▸ hz1x1)
    let cyc : Fin 6 → U := ![x1.1, y1.1, z2.1, x2.1, y2.1, z1.1]
    have hcyc_inj : Function.Injective cyc := by
      have hcol_ne : ∀ u v : ΓT, col u ≠ col v → u.1 ≠ v.1 := fun u v h heq => h (congrArg col (Subtype.ext heq))
      intro a b hab; fin_cases a <;> fin_cases b <;> dsimp [cyc] at hab ⊢
      all_goals first | rfl | exact (hx_ne hab).elim | exact (hx_ne hab.symm).elim
                      | exact (hy_ne hab).elim | exact (hy_ne hab.symm).elim
                      | exact (hz_ne hab).elim | exact (hz_ne hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hx1, hy1]; exact hc12) hab).elim
                      | exact (hcol_ne _ _ (by rw [hx1, hy1]; exact hc12) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hx1, hy2]; exact hc12) hab).elim
                      | exact (hcol_ne _ _ (by rw [hx1, hy2]; exact hc12) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hx2, hy1]; exact hc12) hab).elim
                      | exact (hcol_ne _ _ (by rw [hx2, hy1]; exact hc12) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hx2, hy2]; exact hc12) hab).elim
                      | exact (hcol_ne _ _ (by rw [hx2, hy2]; exact hc12) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hx1]; exact hcz1.1.symm) hab).elim
                      | exact (hcol_ne _ _ (by rw [hx1]; exact hcz1.1.symm) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hx2]; exact hcz1.1.symm) hab).elim
                      | exact (hcol_ne _ _ (by rw [hx2]; exact hcz1.1.symm) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hx1]; exact hcz2.1.symm) hab).elim
                      | exact (hcol_ne _ _ (by rw [hx1]; exact hcz2.1.symm) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hx2]; exact hcz2.1.symm) hab).elim
                      | exact (hcol_ne _ _ (by rw [hx2]; exact hcz2.1.symm) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hy1]; exact hcz1.2.symm) hab).elim
                      | exact (hcol_ne _ _ (by rw [hy1]; exact hcz1.2.symm) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hy2]; exact hcz1.2.symm) hab).elim
                      | exact (hcol_ne _ _ (by rw [hy2]; exact hcz1.2.symm) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hy1]; exact hcz2.2.symm) hab).elim
                      | exact (hcol_ne _ _ (by rw [hy1]; exact hcz2.2.symm) hab.symm).elim
                      | exact (hcol_ne _ _ (by rw [hy2]; exact hcz2.2.symm) hab).elim
                      | exact (hcol_ne _ _ (by rw [hy2]; exact hcz2.2.symm) hab.symm).elim
    obtain ⟨v, hv⟩ := exists_dom3_of_c6 H hTF hnn hsum hdeg cyc hcyc_inj
      h11 hz2y1 hz2x2.symm h22 hz1y2 hz1x1.symm
    -- Every `v` hits at most 2 of `{c1, c2, c3}`!
    have hhit3 : ∀ (u1 u2 u3 : ΓT), col u1 = c1 → col u2 = c2 → col u3 ≠ c1 → col u3 ≠ c2 →
        H.Adj v u1.1 → H.Adj v u2.1 → H.Adj v u3.1 → False := by
      intro u1 u2 u3 h1 h2 h3a h3b hv1 hv2 hv3
      rcases hcover v with ⟨p, hp⟩ | ⟨r, hr⟩
      · have q1 := (hqJ_adj p v hp c1 u1.1 ((hcol_iff u1 c1).mp h1)).mp hv1
        have q2 := (hqJ_adj p v hp c2 u2.1 ((hcol_iff u2 c2).mp h2)).mp hv2
        exact hc12 (Fin.ext (by omega))
      · rcases eq_or_ne r c1 with rfl | hr1
        · exact hJ_ind r v hr u1.1 ((hcol_iff u1 r).mp h1) hv1
        · rcases eq_or_ne r c2 with rfl | hr2
          · exact hJ_ind r v hr u2.1 ((hcol_iff u2 r).mp h2) hv2
          · have hr3 : r = col u3 :=
              OMA.R_Erdos128_erdos_128_R2.fin3_third hc12 h3a.symm h3b.symm hr1 hr2
            exact hJ_ind r v hr u3.1 ((hcol_iff u3 r).mp hr3.symm) hv3
    rcases hv with ⟨h0, h2, h4⟩ | ⟨h1, h3, h5⟩
    · exact hhit3 x1 y2 z2 hx1 hy2 hcz2.1 hcz2.2 h0 h4 h2
    · exact hhit3 x2 y1 z1 hx2 hy1 hcz1.1 hcz1.2 h3 h1 h5
  have hΓ_ne : ∀ r : Fin 3, ∃ z : ΓT, col z = r := fun r => by
    obtain ⟨u, hu⟩ := hJ_ne r; exact ⟨⟨u, (hmem_ΓS u).mpr ⟨r, hu⟩⟩, (hcol_iff _ r).mpr hu⟩
  -- Helper: given `i >= 2`, `π`, `de`, and `eΓ : ΓT ≃ {p : Fin (3*i-1) // ¬ (de = true ∧ p.val = 2*i-1)}`,
  -- assemble `IsVegaGraph H i (yf.isNone) de` by permuting `(af, uf)` via `π`!
  have hbuild : ∀ (i : ℕ) (hi : 2 ≤ i) (de : Bool) (π : Equiv.Perm (Fin 3))
      (eΓ : ΓT ≃ {p : Fin (3 * i - 1) // ¬ (de = true ∧ p.val = 2 * i - 1)}),
      (∀ u v : ΓT, HΓ.Adj u v ↔ vegaAdj i (.inl (eΓ u).1) (.inl (eΓ v).1)) →
      (∀ u : ΓT, (π (col u) = 0 ↔ (eΓ u).1.val < i) ∧
                 (π (col u) = 1 ↔ i ≤ (eΓ u).1.val ∧ (eΓ u).1.val < 2 * i) ∧
                 (π (col u) = 2 ↔ 2 * i ≤ (eΓ u).1.val)) →
      IsVegaGraph H i yf.isNone de := by
    intro i hi de π eΓ heΓ_adj heΓ_blk
    -- The permutation `π` of the frame slots is one of the six permutations of `Fin 3`.
    have hπall : ∀ π₀ : Equiv.Perm (Fin 3),
        π₀ = Equiv.refl (Fin 3) ∨ π₀ = Equiv.swap (0 : Fin 3) 1 ∨ π₀ = Equiv.swap (0 : Fin 3) 2 ∨
        π₀ = Equiv.swap (1 : Fin 3) 2 ∨ π₀ = Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 ∨
        π₀ = Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by decide
    have hfin8 : ∀ p : Fin 8, p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
      intro p; omega
    have hpermQ_left : ∀ p : Fin 8, framePermInv π (framePerm π p) = p := by
      rcases hπall π with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hpermQ_right : ∀ p : Fin 8, framePerm π (framePermInv π p) = p := by
      rcases hπall π with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hind : ∀ (k k' : ℕ) (a b : Fin 8), vegaAdj k (.inr a) (.inr b) = vegaAdj k' (.inr a) (.inr b) :=
      fun _ _ _ _ => rfl
    have hpermQ_adj : ∀ p q : Fin 8, vegaAdj 2 (.inr p) (.inr q) ↔
        vegaAdj i (.inr (framePerm π p)) (.inr (framePerm π q)) := by
      simp only [hind i 2]
      rcases hπall π with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hpne : ∀ p : Fin 8, 2 ≤ p.val → (framePerm π p).val ≠ 1 := by
      intro p h2
      rcases hfin8 p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [framePerm]
      · exact absurd h2 (by omega)
      all_goals (simp [framePerm]; omega)
    have hqSome : ∀ p : Fin 8, 2 ≤ p.val → (qOf p).isSome := by
      intro p h2
      rcases hfin8 p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [qOf]
      · exact absurd h2 (by omega)
      all_goals simp [qOf]
    have hqOf_active : ∀ p : Fin 8, vegaActive i yf.isNone de (.inr (framePerm π p)) ↔ (qOf p).isSome := by
      intro p; by_cases hp2 : p.val < 2
      · rcases hfin8 p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp [vegaActive, qOf, framePerm]
        · cases yf <;> simp [vegaActive, qOf, framePerm]
        all_goals exact absurd hp2 (by omega)
      · have hge : 2 ≤ p.val := by omega
        have hfp1 : (framePerm π p).val ≠ 1 := hpne p hge
        have hqs : (qOf p).isSome := hqSome p hge
        constructor
        · intro _
          exact hqs
        · intro _ hc
          exact absurd hc.2 hfp1
    -- Frame index selection for vertices outside ΓS.
    have hexz : ∀ z : U, z ∉ ΓS → ∃ p : Fin 8, qOf p = some z := fun z hnot => by
      rcases hcover z with h | h
      · exact h
      · exact (hnot ((hmem_ΓS z).mpr h)).elim
    let qz : U → Fin 8 := fun z => if hz : z ∈ ΓS then 0 else (hexz z hz).choose
    have hqz : ∀ z : U, z ∉ ΓS → qOf (qz z) = some z := fun z hnot => by
      dsimp only [qz]; rw [dif_neg hnot]; exact (hexz z hnot).choose_spec
    have hqS : ∀ (p : Fin 8) (z : U), qOf p = some z → (qOf p).isSome := fun p z hp => by
      rw [hp]; rfl
    let fwd : U → {v : VegaV i // vegaActive i yf.isNone de v} := fun z =>
      if hz : z ∈ ΓS then ⟨.inl (eΓ ⟨z, hz⟩).1, (eΓ ⟨z, hz⟩).2⟩
      else ⟨.inr (framePerm π (qz z)), (hqOf_active (qz z)).mpr (hqS (qz z) z (hqz z hz))⟩
    let inv : {v : VegaV i // vegaActive i yf.isNone de v} → U := fun ⟨v, hv⟩ =>
      match v with
      | .inl k => (eΓ.symm ⟨k, hv⟩).1
      | .inr q =>
        have hact : vegaActive i yf.isNone de (.inr (framePerm π (framePermInv π q))) := by
          rw [hpermQ_right]; exact hv
        (qOf (framePermInv π q)).get ((hqOf_active (framePermInv π q)).mp hact)
    have hfwd_Γ : ∀ (z : ΓT), (fwd z.1).1 = .inl (eΓ z).1 := fun z => by
      dsimp only [fwd]; rw [dif_pos z.2]
    have hfwd_Q : ∀ (p : Fin 8) (z : U), qOf p = some z → (fwd z).1 = .inr (framePerm π p) := by
      intro p z hp
      have hnot : z ∉ ΓS := fun h => by obtain ⟨r, hr⟩ := (hmem_ΓS z).mp h; exact hq_disj_J p z hp r hr
      have hPeq : qz z = p := hq_inj _ p z z (hqz z hnot) hp rfl
      dsimp only [fwd]; rw [dif_neg hnot]; dsimp only; rw [hPeq]
    have hleft : Function.LeftInverse inv fwd := by
      intro z; by_cases hz : z ∈ ΓS
      · dsimp only [inv]; rw [show fwd z = ⟨.inl (eΓ ⟨z, hz⟩).1, (eΓ ⟨z, hz⟩).2⟩ by dsimp [fwd]; rw [dif_pos hz]]
        dsimp only; rw [Equiv.symm_apply_apply]
      · rcases hcover z with ⟨p, hp⟩ | h
        · have h1 := hfwd_Q p z hp
          have heq : fwd z = ⟨.inr (framePerm π p), (hqOf_active p).mpr (hqS p z hp)⟩ := Subtype.ext h1
          rw [heq]; dsimp only [inv]
          simp only [hpermQ_left]
          have hget : (qOf p).get (hqS p z hp) = z :=
            Option.some.inj ((Option.some_get (hqS p z hp)).trans hp)
          exact hget
        · exact (hz ((hmem_ΓS z).mpr h)).elim
    have hright : Function.RightInverse inv fwd := by
      rintro ⟨v, hv⟩; apply Subtype.ext
      cases v with
      | inl k =>
        dsimp only [inv]; rw [hfwd_Γ (eΓ.symm ⟨k, hv⟩)]; simp
      | inr q =>
        dsimp only [inv]
        set hsome := (hqOf_active (framePermInv π q)).mp (by rw [hpermQ_right]; exact hv)
        have hqeq : qOf (framePermInv π q) = some ((qOf (framePermInv π q)).get hsome) :=
          (Option.some_get hsome).symm
        rw [hfwd_Q (framePermInv π q) _ hqeq, hpermQ_right]
    refine ⟨hi, ⟨fwd, inv, hleft, hright⟩, ?_⟩
    intro u1 u2
    show H.Adj u1 u2 ↔ vegaAdj i (fwd u1).1 (fwd u2).1
    have hsym_v : ∀ a b : VegaV i, vegaAdj i a b ↔ vegaAdj i b a := fun a b => ⟨vegaAdj_symm hi, vegaAdj_symm hi⟩
    by_cases h1 : u1 ∈ ΓS <;> by_cases h2 : u2 ∈ ΓS
    · rw [hfwd_Γ ⟨u1, h1⟩, hfwd_Γ ⟨u2, h2⟩]; exact heΓ_adj ⟨u1, h1⟩ ⟨u2, h2⟩
    · rcases hcover u2 with ⟨p, hp⟩ | h
      · rw [hfwd_Γ ⟨u1, h1⟩, hfwd_Q p u2 hp, H.adj_comm, hqJ_adj p u2 hp (col ⟨u1, h1⟩) u1 ((hcol_iff ⟨u1, h1⟩ _).mp rfl)]
        have hblk := heΓ_blk ⟨u1, h1⟩
        have hpi : ∀ (p : Fin 8) (r : Fin 3), (p.val = 2 + r.val ∨ p.val = 5 + r.val) ↔
            ((framePerm π p).val = 2 + (π r).val ∨ (framePerm π p).val = 5 + (π r).val) := by
          rcases hπall π with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [hpi p (col ⟨u1, h1⟩)]; simp only [vegaAdj]
        rcases fin3_cases (π (col ⟨u1, h1⟩)) with hc | hc | hc
        · have hlt : (eΓ ⟨u1, h1⟩).1.val < i := hblk.1.mp hc; rw [hc]; simp only [Fin.val_zero, add_zero]; constructor <;> intro hh
          · left; exact ⟨hlt, hh⟩
          · rcases hh with ⟨_, h⟩ | ⟨hge, _⟩ | ⟨hge, _⟩ <;> [exact h; omega; omega]
        · have hbd : i ≤ (eΓ ⟨u1, h1⟩).1.val ∧ (eΓ ⟨u1, h1⟩).1.val < 2 * i := hblk.2.1.mp hc
          rw [hc]; simp only [Fin.val_one]; constructor <;> intro hh
          · right; left; exact ⟨hbd.1, hbd.2, hh⟩
          · rcases hh with ⟨hlt, _⟩ | ⟨_, _, h⟩ | ⟨hge, _⟩ <;> [omega; exact h; omega]
        · have hge : 2 * i ≤ (eΓ ⟨u1, h1⟩).1.val := hblk.2.2.mp hc
          rw [hc]; simp only [Fin.val_two]; constructor <;> intro hh
          · right; right; exact ⟨hge, hh⟩
          · rcases hh with ⟨hlt, _⟩ | ⟨_, hlt, _⟩ | ⟨_, h⟩ <;> [omega; omega; exact h]
      · exact (h2 ((hmem_ΓS u2).mpr h)).elim
    · rcases hcover u1 with ⟨p, hp⟩ | h
      · rw [hfwd_Q p u1 hp, hfwd_Γ ⟨u2, h2⟩, hqJ_adj p u1 hp (col ⟨u2, h2⟩) u2 ((hcol_iff ⟨u2, h2⟩ _).mp rfl)]
        have hblk := heΓ_blk ⟨u2, h2⟩
        have hpi : ∀ (p : Fin 8) (r : Fin 3), (p.val = 2 + r.val ∨ p.val = 5 + r.val) ↔
            ((framePerm π p).val = 2 + (π r).val ∨ (framePerm π p).val = 5 + (π r).val) := by
          rcases hπall π with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [hpi p (col ⟨u2, h2⟩)]; simp only [vegaAdj]
        rcases fin3_cases (π (col ⟨u2, h2⟩)) with hc | hc | hc
        · have hlt : (eΓ ⟨u2, h2⟩).1.val < i := hblk.1.mp hc; rw [hc]; simp only [Fin.val_zero, add_zero]; constructor <;> intro hh
          · left; exact ⟨hlt, hh⟩
          · rcases hh with ⟨_, h⟩ | ⟨hge, _⟩ | ⟨hge, _⟩ <;> [exact h; omega; omega]
        · have hbd : i ≤ (eΓ ⟨u2, h2⟩).1.val ∧ (eΓ ⟨u2, h2⟩).1.val < 2 * i := hblk.2.1.mp hc
          rw [hc]; simp only [Fin.val_one]; constructor <;> intro hh
          · right; left; exact ⟨hbd.1, hbd.2, hh⟩
          · rcases hh with ⟨hlt, _⟩ | ⟨_, _, h⟩ | ⟨hge, _⟩ <;> [omega; exact h; omega]
        · have hge : 2 * i ≤ (eΓ ⟨u2, h2⟩).1.val := hblk.2.2.mp hc
          rw [hc]; simp only [Fin.val_two]; constructor <;> intro hh
          · right; right; exact ⟨hge, hh⟩
          · rcases hh with ⟨hlt, _⟩ | ⟨_, hlt, _⟩ | ⟨_, h⟩ <;> [omega; omega; exact h]
      · exact (h1 ((hmem_ΓS u1).mpr h)).elim
    · rcases hcover u1 with ⟨p1, hp1⟩ | h
      · rcases hcover u2 with ⟨p2, hp2⟩ | h'
        · rw [hfwd_Q p1 u1 hp1, hfwd_Q p2 u2 hp2, hqq_adj p1 p2 u1 u2 hp1 hp2, hpermQ_adj]
        · exact (h2 ((hmem_ΓS u2).mpr h')).elim
      · exact (h1 ((hmem_ΓS u1).mpr h)).elim
  -- Invoke Step 14 (`ferrers_tripartite_classify`)!
  rcases ferrers_tripartite_classify HΓ col hΓ_TF hΓ_col hΓ_cross hΓ_twin hΓ_no2K2 hΓ_ne with
    ⟨i, hi, π, e, hadj, hblk⟩ | ⟨i, hi, π, e, hadj, hblk⟩ | ⟨_, _, _, _, _, c1, c2, p0, s0, hc12, hp0, hs0, hp0_na, hs0_na⟩
  · -- Case 1: And(i)
    let eΓ : ΓT ≃ {p : Fin (3 * i - 1) // ¬ (false = true ∧ p.val = 2 * i - 1)} :=
      e.trans ⟨fun p => ⟨p, by simp⟩, fun p => p.1, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
    exact ⟨i, yf.isNone, false, hbuild i hi false π eΓ hadj hblk⟩
  · -- Case 2: And(i) - {2i-1}
    let eΓ : ΓT ≃ {p : Fin (3 * i - 1) // ¬ (true = true ∧ p.val = 2 * i - 1)} :=
      e.trans ⟨fun p => ⟨p.1, by simp [p.2]⟩, fun p => ⟨p.1, by simpa using p.2⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
    exact ⟨i, yf.isNone, true, hbuild i hi true π eΓ hadj hblk⟩
  · -- Case 3: dead endpoints `p0 ∈ J c1`, `s0 ∈ J c2` -> killed by `exists_dom3_of_c6` on `(af c1, p0, uf c1, af c2, s0, uf c2)`!
    exfalso
    let pa : Fin 3 → Fin 8 := fun r => ⟨2 + r.val, by omega⟩
    let pu : Fin 3 → Fin 8 := fun r => ⟨5 + r.val, by omega⟩
    have hq_af : ∀ r : Fin 3, qOf (pa r) = some (af r) := fun r => by rcases fin3_cases r with rfl | rfl | rfl <;> rfl
    have hq_uf : ∀ r : Fin 3, qOf (pu r) = some (uf r) := fun r => by rcases fin3_cases r with rfl | rfl | rfl <;> rfl
    have ha1_p0 : H.Adj (af c1) p0.1 := (hqJ_adj (pa c1) (af c1) (hq_af c1) c1 p0.1 ((hcol_iff p0 c1).mp hp0)).mpr (Or.inl rfl)
    have hu1_p0 : H.Adj (uf c1) p0.1 := (hqJ_adj (pu c1) (uf c1) (hq_uf c1) c1 p0.1 ((hcol_iff p0 c1).mp hp0)).mpr (Or.inr rfl)
    have ha2_s0 : H.Adj (af c2) s0.1 := (hqJ_adj (pa c2) (af c2) (hq_af c2) c2 s0.1 ((hcol_iff s0 c2).mp hs0)).mpr (Or.inl rfl)
    have hu2_s0 : H.Adj (uf c2) s0.1 := (hqJ_adj (pu c2) (uf c2) (hq_uf c2) c2 s0.1 ((hcol_iff s0 c2).mp hs0)).mpr (Or.inr rfl)
    have hu1_a2 : H.Adj (uf c1) (af c2) := (hqq_adj (pu c1) (pa c2) (uf c1) (af c2) (hq_uf c1) (hq_af c2)).mpr (by
      rcases fin3_cases c1 with rfl | rfl | rfl <;> rcases fin3_cases c2 with rfl | rfl | rfl <;> first | exact absurd rfl hc12 | simp [pa, pu, vegaAdj])
    have hu2_a1 : H.Adj (uf c2) (af c1) := (hqq_adj (pu c2) (pa c1) (uf c2) (af c1) (hq_uf c2) (hq_af c1)).mpr (by
      rcases fin3_cases c1 with rfl | rfl | rfl <;> rcases fin3_cases c2 with rfl | rfl | rfl <;> first | exact absurd rfl hc12 | simp [pa, pu, vegaAdj])
    let cyc : Fin 6 → U := ![af c1, p0.1, uf c1, af c2, s0.1, uf c2]
    have hcyc_inj : Function.Injective cyc := by
      have hp0J : p0.1 ∈ J c1 := (hcol_iff p0 c1).mp hp0
      have hs0J : s0.1 ∈ J c2 := (hcol_iff s0 c2).mp hs0
      have hps_ne : p0.1 ≠ s0.1 := fun h => Finset.disjoint_left.mp (hJ_disj c1 c2 hc12) hp0J (h ▸ hs0J)
      have hq_ne_q : ∀ p1 p2 : Fin 8, ∀ u1 u2 : U, qOf p1 = some u1 → qOf p2 = some u2 → p1 ≠ p2 → u1 ≠ u2 :=
        fun p1 p2 u1 u2 h1 h2 hne heq => hne (hq_inj p1 p2 u1 u2 h1 h2 heq)
      have hpa12 : pa c1 ≠ pa c2 := fun h => hc12 (Fin.ext (by have := congrArg Fin.val h; dsimp [pa] at this; omega))
      have hpu12 : pu c1 ≠ pu c2 := fun h => hc12 (Fin.ext (by have := congrArg Fin.val h; dsimp [pu] at this; omega))
      have hpau : ∀ r1 r2 : Fin 3, pa r1 ≠ pu r2 := fun r1 r2 h => by have := congrArg Fin.val h; dsimp [pa, pu] at this; omega
      intro a b hab; fin_cases a <;> fin_cases b <;> dsimp [cyc] at hab ⊢
      all_goals first | rfl | exact (hps_ne hab).elim | exact (hps_ne hab.symm).elim
                      | exact (hq_disj_J _ _ (hq_af _) _ (by rw [hab]; exact hp0J)).elim
                      | exact (hq_disj_J _ _ (hq_af _) _ (by rw [hab]; exact hs0J)).elim
                      | exact (hq_disj_J _ _ (hq_af _) _ (by rw [← hab]; exact hp0J)).elim
                      | exact (hq_disj_J _ _ (hq_af _) _ (by rw [← hab]; exact hs0J)).elim
                      | exact (hq_disj_J _ _ (hq_uf _) _ (by rw [hab]; exact hp0J)).elim
                      | exact (hq_disj_J _ _ (hq_uf _) _ (by rw [hab]; exact hs0J)).elim
                      | exact (hq_disj_J _ _ (hq_uf _) _ (by rw [← hab]; exact hp0J)).elim
                      | exact (hq_disj_J _ _ (hq_uf _) _ (by rw [← hab]; exact hs0J)).elim
                      | exact (hq_ne_q _ _ _ _ (hq_af _) (hq_af _) hpa12 hab).elim
                      | exact (hq_ne_q _ _ _ _ (hq_af _) (hq_af _) hpa12.symm hab).elim
                      | exact (hq_ne_q _ _ _ _ (hq_uf _) (hq_uf _) hpu12 hab).elim
                      | exact (hq_ne_q _ _ _ _ (hq_uf _) (hq_uf _) hpu12.symm hab).elim
                      | exact (hq_ne_q _ _ _ _ (hq_af _) (hq_uf _) (hpau _ _) hab).elim
                      | exact (hq_ne_q _ _ _ _ (hq_uf _) (hq_af _) (hpau _ _).symm hab).elim
    obtain ⟨v, hv⟩ := exists_dom3_of_c6 H hTF hnn hsum hdeg cyc hcyc_inj
      ha1_p0 hu1_p0.symm hu1_a2 ha2_s0 hu2_s0.symm hu2_a1
    have hdom_au : ∀ (r : Fin 3) (v : U), H.Adj v (af r) → H.Adj v (uf r) → v ∈ J r := by
      intro r v hva hvu
      rcases hcover v with ⟨p, hp⟩ | ⟨r', hr'⟩
      · exfalso
        have h1 := (hqq_adj p (pa r) v (af r) hp (hq_af r)).mp hva
        have h2 := (hqq_adj p (pu r) v (uf r) hp (hq_uf r)).mp hvu
        rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases fin3_cases r with rfl | rfl | rfl <;> simp [pa, pu, vegaAdj] at h1 h2
      · have h1 := (hqJ_adj (pa r) (af r) (hq_af r) r' v hr').mp hva.symm
        have : r' = r := Fin.ext (by dsimp [pa] at h1; omega)
        exact this ▸ hr'
    rcases hv with ⟨h0, h2, h4⟩ | ⟨h1, h3, h5⟩
    · have hv1 : v ∈ J c1 := hdom_au c1 v h0 h2
      exact hs0_na ⟨v, (hmem_ΓS v).mpr ⟨c1, hv1⟩⟩ ((hcol_iff _ c1).mpr hv1) h4.symm
    · have hv2 : v ∈ J c2 := hdom_au c2 v h3 h5
      exact hp0_na ⟨v, (hmem_ΓS v).mpr ⟨c2, hv2⟩⟩ ((hcol_iff _ c2).mpr hv2) h1.symm

/- ## Section B.3: Main Regular Theorem (`regular_good_is_vega`) -/

/-- Pure-`omega` helper for Claim 13 Subcase 3b-ii: every vertex hits `≤ 4` of the 12-vertex graph `H_12`. -/
lemma h12_hits_le_four {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (hTF : H.CliqueFree 3)
    (v : Fin 12 → U)
    -- 0=a, 1=u, 2=q, 3=t1, 4=pB, 5=v', 6=y0, 7=y1, 8=pC, 9=w', 10=z0, 11=z1
    (e02 : H.Adj (v 0) (v 2)) (e03 : H.Adj (v 0) (v 3)) (e05 : H.Adj (v 0) (v 5)) (e09 : H.Adj (v 0) (v 9))
    (e12 : H.Adj (v 1) (v 2)) (e13 : H.Adj (v 1) (v 3)) (e14 : H.Adj (v 1) (v 4)) (e18 : H.Adj (v 1) (v 8))
    (e26 : H.Adj (v 2) (v 6)) (e27 : H.Adj (v 2) (v 7)) (e310 : H.Adj (v 3) (v 10)) (e311 : H.Adj (v 3) (v 11))
    (e45 : H.Adj (v 4) (v 5)) (e46 : H.Adj (v 4) (v 6)) (e49 : H.Adj (v 4) (v 9))
    (e57 : H.Adj (v 5) (v 7)) (e58 : H.Adj (v 5) (v 8))
    (e89 : H.Adj (v 8) (v 9)) (e810 : H.Adj (v 8) (v 10)) (e911 : H.Adj (v 9) (v 11))
    (e610 : H.Adj (v 6) (v 10)) (e611 : H.Adj (v 6) (v 11)) (e710 : H.Adj (v 7) (v 10)) (e711 : H.Adj (v 7) (v 11))
    (s : U) :
    #(Finset.univ.filter (fun k : Fin 12 => H.Adj s (v k))) ≤ 4 := by
  let b : Fin 12 → ℕ := fun k => if H.Adj s (v k) then 1 else 0
  have hb01 : ∀ k, b k ≤ 1 := fun k => by dsimp [b]; split_ifs <;> omega
  have he : ∀ {j k : Fin 12}, H.Adj (v j) (v k) → b j + b k ≤ 1 := by
    intro j k hjk; dsimp [b]; by_cases hj : H.Adj s (v j) <;> by_cases hk : H.Adj s (v k)
    · exact (tf_contra hTF hj hjk hk).elim
    all_goals simp [hj, hk]
  have h02 := he e02; have h03 := he e03; have h05 := he e05; have h09 := he e09
  have h12 := he e12; have h13 := he e13; have h14 := he e14; have h18 := he e18
  have h26 := he e26; have h27 := he e27; have h310 := he e310; have h311 := he e311
  have h45 := he e45; have h46 := he e46; have h49 := he e49
  have h57 := he e57; have h58 := he e58
  have h89 := he e89; have h810 := he e810; have h911 := he e911
  have h610 := he e610; have h611 := he e611; have h710 := he e710; have h711 := he e711
  have hb : b = fun k : Fin 12 => if H.Adj s (v k) then 1 else 0 := rfl
  have hsum_eq : #(Finset.univ.filter (fun k : Fin 12 => H.Adj s (v k))) =
      b 0 + b 1 + b 2 + b 3 + b 4 + b 5 + b 6 + b 7 + b 8 + b 9 + b 10 + b 11 := by
    rw [Finset.card_filter, ← hb]; simp [Fin.sum_univ_succ]; omega
  rw [hsum_eq]
  have h0 := hb01 0; have h1 := hb01 1; have h2 := hb01 2; have h3 := hb01 3
  have h4 := hb01 4; have h5 := hb01 5; have h6 := hb01 6; have h7 := hb01 7
  have h8 := hb01 8; have h9 := hb01 9; have h10 := hb01 10; have h11 := hb01 11
  -- each hit count is 0 or 1; case on the hub slots a, u (then q, t1) to use integrality
  have hbv : ∀ k : Fin 12, b k = 0 ∨ b k = 1 := fun k => by
    by_cases h : H.Adj s (v k) <;> simp [b, h]
  rcases hbv 0 with hv0 | hv0 <;> rcases hbv 1 with hv1 | hv1
  · omega
  · omega
  · omega
  · rcases hbv 2 with hv2 | hv2 <;> rcases hbv 3 with hv3 | hv3 <;> omega


/-- Bundled `Fin 3`-symmetric decomposition of a regular good graph `H` after Claims 1-12. -/
structure RegDecomp {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (G : IsGood H) (ω : U → ℝ) (δ : ℝ) where
  hpos : ∀ v, 0 < ω v
  hnn : ∀ v, 0 ≤ ω v
  hsum : wsum ω Finset.univ = 1
  hreg : ∀ u, wdeg H ω u = δ
  hδ : (1 / 3 : ℝ) < δ
  hdeg : ∀ u, (1 / 3 : ℝ) < wdeg H ω u
  x : U
  hx_wmin : ∀ v : U, ω x ≤ ω v
  hx_dmin : ∀ v : U, ω v = ω x → #(Finset.univ.filter (H.Adj x)) ≤ #(Finset.univ.filter (H.Adj v))
  Nx : Finset U
  R_set : Finset U
  Y_set : Finset U
  hNx_eq : Nx = Finset.univ.filter (H.Adj x)
  hx_R : x ∈ R_set
  hNx_ind : ∀ u1 ∈ Nx, ∀ u2 ∈ Nx, ¬ H.Adj u1 u2
  hR_ind : ∀ u1 ∈ R_set, ∀ u2 ∈ R_set, ¬ H.Adj u1 u2
  hdisj_NR' : ∀ u1 ∈ Nx, ∀ u2 ∈ R_set, u1 ≠ u2
  hY_sub : Y_set ⊆ Nx
  hY_nbhd : ∀ y ∈ Y_set, ∀ z : U, H.Adj y z ↔ z ∈ R_set
  hY_subsing : ∀ y1 ∈ Y_set, ∀ y2 ∈ Y_set, y1 = y2
  hwRval : wsum ω R_set = 4 * δ - 1 - ω x
  hw_xY : ω x + wsum ω Y_set = 6 * δ - 2
  a_b : Fin 3 → U
  u_b : Fin 3 → U
  A_b : Fin 3 → Finset U
  U_b : Fin 3 → Finset U
  I_b : Fin 3 → Finset U
  hAb_sub : ∀ r : Fin 3, A_b r ⊆ Nx
  hUb_sub : ∀ r : Fin 3, U_b r ⊆ R_set
  ha_mem : ∀ r : Fin 3, a_b r ∈ A_b r
  hu_mem : ∀ r : Fin 3, u_b r ∈ U_b r
  hIb_ne : ∀ r : Fin 3, (I_b r).Nonempty
  hIb_ind : ∀ r : Fin 3, ∀ z1 ∈ I_b r, ∀ z2 ∈ I_b r, ¬ H.Adj z1 z2
  hIb_disj : ∀ r1 r2 : Fin 3, r1 ≠ r2 → Disjoint (I_b r1) (I_b r2)
  hIb_out : ∀ r : Fin 3, ∀ z ∈ I_b r, z ∉ Nx ∧ z ∉ R_set
  hAb_disj : ∀ r1 r2 : Fin 3, r1 ≠ r2 → Disjoint (A_b r1) (A_b r2)
  hUb_disj : ∀ r1 r2 : Fin 3, r1 ≠ r2 → Disjoint (U_b r1) (U_b r2)
  hY_disj_A : ∀ r : Fin 3, Disjoint Y_set (A_b r)
  hx_ne_U : ∀ r : Fin 3, ∀ u' ∈ U_b r, x ≠ u'
  hAb_comp_U : ∀ r1 r2 : Fin 3, r1 ≠ r2 → ∀ p ∈ A_b r1, ∀ u' ∈ U_b r2, H.Adj p u'
  hAb_na_I : ∀ r1 r2 : Fin 3, r1 ≠ r2 → ∀ p ∈ A_b r1, ∀ z ∈ I_b r2, ¬ H.Adj p z
  hUb_na_I : ∀ r1 r2 : Fin 3, r1 ≠ r2 → ∀ u' ∈ U_b r1, ∀ z ∈ I_b r2, ¬ H.Adj u' z
  hY_na_I : ∀ r : Fin 3, ∀ y ∈ Y_set, ∀ z ∈ I_b r, ¬ H.Adj y z
  hx_na_I : ∀ r : Fin 3, ∀ z ∈ I_b r, ¬ H.Adj x z
  hcomp_aIuI : ∀ r : Fin 3, ∀ z ∈ I_b r, H.Adj (a_b r) z ∧ H.Adj (u_b r) z
  hpart_b : ∀ r1 r2 r3 : Fin 3, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ∀ z : U, z ∈ Y_set ∨ z ∈ A_b r1 ∨ z ∈ A_b r2 ∨ z ∈ A_b r3 ∨ z = x ∨
             z ∈ U_b r1 ∨ z ∈ U_b r2 ∨ z ∈ U_b r3 ∨ z ∈ I_b r1 ∨ z ∈ I_b r2 ∨ z ∈ I_b r3
  hcom_AU : ∀ r : Fin 3, ∀ p ∈ A_b r, ∀ z ∈ I_b r, ∀ q : U, H.Adj p q → H.Adj z q → q ∈ U_b r
  hcom_UA : ∀ r : Fin 3, ∀ u' ∈ U_b r, ∀ z ∈ I_b r, ∀ q : U, H.Adj u' q → H.Adj z q → q ∈ A_b r
  hcom_II : ∀ r1 r2 r3 : Fin 3, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ∀ z1 ∈ I_b r1, ∀ z2 ∈ I_b r2, ∀ q : U, H.Adj z1 q → H.Adj z2 q → q ∈ I_b r3
  hsplit_b : ∀ r1 r2 r3 : Fin 3, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    (∃ q ∈ A_b r3 ∪ U_b r3, ∃ z0 ∈ I_b r3, ∃ z1 ∈ I_b r3, H.Adj q z0 ∧ ¬ H.Adj q z1) →
    (∃ p3 ∈ A_b r3, ∃ w3 ∈ U_b r3, ∃ z0 ∈ I_b r3, ∃ z1 ∈ I_b r3,
      H.Adj p3 w3 ∧ H.Adj p3 z0 ∧ ¬ H.Adj p3 z1 ∧ H.Adj w3 z1 ∧ ¬ H.Adj w3 z0) ∧
    (∀ zA ∈ I_b r3, ∀ zB ∈ I_b r3, ∀ t ∈ I_b r1 ∪ I_b r2, H.Adj zA t ↔ H.Adj zB t)
  hcl12_b : ∀ r : Fin 3, (∀ q ∈ A_b r ∪ U_b r, ∀ z1 ∈ I_b r, ∀ z2 ∈ I_b r, H.Adj q z1 ↔ H.Adj q z2) →
    A_b r = {a_b r} ∧ U_b r = {u_b r}
  he_b : ∀ r1 r2 : Fin 3, r1 ≠ r2 → ∃ z1 ∈ I_b r1, ∃ z2 ∈ I_b r2, H.Adj z1 z2
  hw_Ab : ∀ r : Fin 3, wsum ω (A_b r) = wsum ω (I_b r)
  hw_Ub : ∀ r : Fin 3, wsum ω (U_b r) = 3 * δ - 1 - ω x + wsum ω (I_b r)
  hw_Nx_b : ∀ r1 r2 r3 : Fin 3, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    wsum ω Y_set + wsum ω (A_b r1) + wsum ω (A_b r2) + wsum ω (A_b r3) = δ

/-- Singleton case of Claim 13: when every `A_b r = {a_b r}` and `U_b r = {u_b r}`, dispatch directly to `vega_of_singleton_frame`. -/
lemma regular_singleton_is_vega {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (G : IsGood H) (ω : U → ℝ) (δ : ℝ)
    (D : RegDecomp H G ω δ)
    (hsingle : ∀ r : Fin 3, D.A_b r = {D.a_b r} ∧ D.U_b r = {D.u_b r}) :
    ∃ (i : ℕ) (dy de : Bool), IsVegaGraph H i dy de := by
  let yf : Option U := if h : D.Y_set.Nonempty then some h.choose else none
  have hyf_spec : ∀ y0 : U, yf = some y0 ↔ y0 ∈ D.Y_set := by
    intro y0; dsimp only [yf]; split_ifs with h
    · simp only [Option.some.injEq]
      exact ⟨fun heq => heq ▸ h.choose_spec, fun hy0 => D.hY_subsing h.choose h.choose_spec y0 hy0⟩
    · simp only [false_iff]; exact fun hy0 => h ⟨y0, hy0⟩
  have hxa : ∀ r : Fin 3, H.Adj D.x (D.a_b r) := fun r =>
    (Finset.mem_filter.mp (D.hNx_eq ▸ D.hAb_sub r (D.ha_mem r))).2
  have ha_na_u : ∀ r : Fin 3, ¬ H.Adj (D.a_b r) (D.u_b r) := fun r h => by
    obtain ⟨z, hz⟩ := D.hIb_ne r
    exact tf_contra G.hTF h (D.hcomp_aIuI r z hz).2 (D.hcomp_aIuI r z hz).1
  let qMap : Fin 8 → Option U := fun p =>
    match p.val with
    | 0 => some D.x | 1 => yf | 2 => some (D.a_b 0) | 3 => some (D.a_b 1) | 4 => some (D.a_b 2)
    | 5 => some (D.u_b 0) | 6 => some (D.u_b 1) | _ => some (D.u_b 2)
  have htag_disj : ∀ (p : Fin 8) (up : U), qMap p = some up →
      (if up = D.x then 0 else if up ∈ D.Y_set then 1 else if up ∈ D.A_b 0 then 2 else if up ∈ D.A_b 1 then 3
       else if up ∈ D.A_b 2 then 4 else if up ∈ D.U_b 0 then 5 else if up ∈ D.U_b 1 then 6 else 7) = p.val := by
    intro p up hp
    have hx_nY : D.x ∉ D.Y_set := fun h => D.hdisj_NR' D.x (D.hY_sub h) D.x D.hx_R rfl
    have hA_nx : ∀ r, D.a_b r ≠ D.x := fun r h => D.hdisj_NR' (D.a_b r) (D.hAb_sub r (D.ha_mem r)) D.x D.hx_R h
    have hA_nY : ∀ r, D.a_b r ∉ D.Y_set := fun r h => Finset.disjoint_left.mp (D.hY_disj_A r) h (D.ha_mem r)
    have hU_nN : ∀ r, D.u_b r ∉ D.Nx := fun r h => D.hdisj_NR' (D.u_b r) h (D.u_b r) (D.hUb_sub r (D.hu_mem r)) rfl
    rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp [qMap] at hp
    · injection hp with h; subst h; simp
    · have hy := (hyf_spec up).mp hp; rw [if_neg (fun h : up = D.x => hx_nY (h ▸ hy)), if_pos hy]; rfl
    · injection hp with h; subst h; rw [if_neg (hA_nx 0), if_neg (hA_nY 0), if_pos (D.ha_mem 0)]; rfl
    · injection hp with h; subst h
      have h0 : D.a_b 1 ∉ D.A_b 0 := fun hm => Finset.disjoint_left.mp (D.hAb_disj 0 1 (by decide)) hm (D.ha_mem 1)
      rw [if_neg (hA_nx 1), if_neg (hA_nY 1), if_neg h0, if_pos (D.ha_mem 1)]; rfl
    · injection hp with h; subst h
      have h0 : D.a_b 2 ∉ D.A_b 0 := fun hm => Finset.disjoint_left.mp (D.hAb_disj 0 2 (by decide)) hm (D.ha_mem 2)
      have h1 : D.a_b 2 ∉ D.A_b 1 := fun hm => Finset.disjoint_left.mp (D.hAb_disj 1 2 (by decide)) hm (D.ha_mem 2)
      rw [if_neg (hA_nx 2), if_neg (hA_nY 2), if_neg h0, if_neg h1, if_pos (D.ha_mem 2)]; rfl
    · injection hp with h; subst h
      rw [if_neg (D.hx_ne_U 0 _ (D.hu_mem 0)).symm, if_neg (fun hm => hU_nN 0 (D.hY_sub hm)),
          if_neg (fun hm => hU_nN 0 (D.hAb_sub 0 hm)), if_neg (fun hm => hU_nN 0 (D.hAb_sub 1 hm)),
          if_neg (fun hm => hU_nN 0 (D.hAb_sub 2 hm)), if_pos (D.hu_mem 0)]; rfl
    · injection hp with h; subst h
      have h5 : D.u_b 1 ∉ D.U_b 0 := fun hm => Finset.disjoint_left.mp (D.hUb_disj 0 1 (by decide)) hm (D.hu_mem 1)
      rw [if_neg (D.hx_ne_U 1 _ (D.hu_mem 1)).symm, if_neg (fun hm => hU_nN 1 (D.hY_sub hm)),
          if_neg (fun hm => hU_nN 1 (D.hAb_sub 0 hm)), if_neg (fun hm => hU_nN 1 (D.hAb_sub 1 hm)),
          if_neg (fun hm => hU_nN 1 (D.hAb_sub 2 hm)), if_neg h5, if_pos (D.hu_mem 1)]; rfl
    · injection hp with h; subst h
      have h5 : D.u_b 2 ∉ D.U_b 0 := fun hm => Finset.disjoint_left.mp (D.hUb_disj 0 2 (by decide)) hm (D.hu_mem 2)
      have h6 : D.u_b 2 ∉ D.U_b 1 := fun hm => Finset.disjoint_left.mp (D.hUb_disj 1 2 (by decide)) hm (D.hu_mem 2)
      rw [if_neg (D.hx_ne_U 2 _ (D.hu_mem 2)).symm, if_neg (fun hm => hU_nN 2 (D.hY_sub hm)),
          if_neg (fun hm => hU_nN 2 (D.hAb_sub 0 hm)), if_neg (fun hm => hU_nN 2 (D.hAb_sub 1 hm)),
          if_neg (fun hm => hU_nN 2 (D.hAb_sub 2 hm)), if_neg h5, if_neg h6]; rfl
  refine vega_of_singleton_frame H G.hTF G.hMax G.hTwin D.hnn D.hsum D.hdeg D.x yf D.a_b D.u_b D.I_b
    D.hIb_ne D.hIb_ind D.hIb_disj ?_ ?_ ?_ ?_ ?_
  · intro p q up uq hp hq heq; subst heq
    exact Fin.ext ((htag_disj p up hp).symm.trans (htag_disj q up hq))
  · intro p up hp r hr
    rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · injection hp with h; subst h; exact (D.hIb_out r D.x hr).2 D.hx_R
    · exact (D.hIb_out r up hr).1 (D.hY_sub ((hyf_spec up).mp hp))
    · injection hp with h; subst h; exact (D.hIb_out r _ hr).1 (D.hAb_sub 0 (D.ha_mem 0))
    · injection hp with h; subst h; exact (D.hIb_out r _ hr).1 (D.hAb_sub 1 (D.ha_mem 1))
    · injection hp with h; subst h; exact (D.hIb_out r _ hr).1 (D.hAb_sub 2 (D.ha_mem 2))
    · injection hp with h; subst h; exact (D.hIb_out r _ hr).2 (D.hUb_sub 0 (D.hu_mem 0))
    · injection hp with h; subst h; exact (D.hIb_out r _ hr).2 (D.hUb_sub 1 (D.hu_mem 1))
    · injection hp with h; subst h; exact (D.hIb_out r _ hr).2 (D.hUb_sub 2 (D.hu_mem 2))
  · intro z
    rcases D.hpart_b 0 1 2 (by decide) (by decide) (by decide) z with
      hY | hA0 | hA1 | hA2 | rfl | hU0 | hU1 | hU2 | hI0 | hI1 | hI2
    · exact Or.inl ⟨1, (hyf_spec z).mpr hY⟩
    · rw [(hsingle 0).1, Finset.mem_singleton] at hA0; subst hA0; exact Or.inl ⟨2, rfl⟩
    · rw [(hsingle 1).1, Finset.mem_singleton] at hA1; subst hA1; exact Or.inl ⟨3, rfl⟩
    · rw [(hsingle 2).1, Finset.mem_singleton] at hA2; subst hA2; exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · rw [(hsingle 0).2, Finset.mem_singleton] at hU0; subst hU0; exact Or.inl ⟨5, rfl⟩
    · rw [(hsingle 1).2, Finset.mem_singleton] at hU1; subst hU1; exact Or.inl ⟨6, rfl⟩
    · rw [(hsingle 2).2, Finset.mem_singleton] at hU2; subst hU2; exact Or.inl ⟨7, rfl⟩
    · exact Or.inr ⟨0, hI0⟩
    · exact Or.inr ⟨1, hI1⟩
    · exact Or.inr ⟨2, hI2⟩
  · intro p q up uq hp hq
    have hQ : ∀ (p : Fin 8) (up : U), qMap p = some up →
        (p = 0 → up = D.x) ∧ (p = 1 → up ∈ D.Y_set) ∧
        (p = 2 → up = D.a_b 0) ∧ (p = 3 → up = D.a_b 1) ∧ (p = 4 → up = D.a_b 2) ∧
        (p = 5 → up = D.u_b 0) ∧ (p = 6 → up = D.u_b 1) ∧ (p = 7 → up = D.u_b 2) := by
      intro p up hp; rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals intro h; first | exact absurd h (by decide) | (injection hp with h'; exact h'.symm) | exact (hyf_spec up).mp hp
    have hYA : ∀ y ∈ D.Y_set, ∀ r : Fin 3, ¬ H.Adj y (D.a_b r) := fun y hy r h =>
      D.hNx_ind y (D.hY_sub hy) (D.a_b r) (D.hAb_sub r (D.ha_mem r)) h
    have hYU : ∀ y ∈ D.Y_set, ∀ r : Fin 3, H.Adj y (D.u_b r) := fun y hy r =>
      (D.hY_nbhd y hy (D.u_b r)).mpr (D.hUb_sub r (D.hu_mem r))
    have hAA : ∀ r1 r2 : Fin 3, ¬ H.Adj (D.a_b r1) (D.a_b r2) := fun r1 r2 =>
      D.hNx_ind _ (D.hAb_sub r1 (D.ha_mem r1)) _ (D.hAb_sub r2 (D.ha_mem r2))
    have hUU : ∀ r1 r2 : Fin 3, ¬ H.Adj (D.u_b r1) (D.u_b r2) := fun r1 r2 =>
      D.hR_ind _ (D.hUb_sub r1 (D.hu_mem r1)) _ (D.hUb_sub r2 (D.hu_mem r2))
    have hxU : ∀ r : Fin 3, ¬ H.Adj D.x (D.u_b r) := fun r => D.hR_ind D.x D.hx_R _ (D.hUb_sub r (D.hu_mem r))
    have hp' := hQ p up hp; have hq' := hQ q uq hq
    rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only [vegaAdj]
    · rw [hp'.1 rfl, hq'.1 rfl]; exact iff_of_false (H.loopless.irrefl _) (by decide)
    · rw [hp'.1 rfl]; exact iff_of_true ((D.hY_nbhd uq (hq'.2.1 rfl) D.x).mpr D.hx_R).symm (by decide)
    · rw [hp'.1 rfl, hq'.2.2.1 rfl]; exact iff_of_true (hxa 0) (by decide)
    · rw [hp'.1 rfl, hq'.2.2.2.1 rfl]; exact iff_of_true (hxa 1) (by decide)
    · rw [hp'.1 rfl, hq'.2.2.2.2.1 rfl]; exact iff_of_true (hxa 2) (by decide)
    · rw [hp'.1 rfl, hq'.2.2.2.2.2.1 rfl]; exact iff_of_false (hxU 0) (by decide)
    · rw [hp'.1 rfl, hq'.2.2.2.2.2.2.1 rfl]; exact iff_of_false (hxU 1) (by decide)
    · rw [hp'.1 rfl, hq'.2.2.2.2.2.2.2 rfl]; exact iff_of_false (hxU 2) (by decide)
    · rw [hq'.1 rfl]; exact iff_of_true ((D.hY_nbhd up (hp'.2.1 rfl) D.x).mpr D.hx_R) (by decide)
    · have := D.hY_subsing up (hp'.2.1 rfl) uq (hq'.2.1 rfl); subst this; exact iff_of_false (H.loopless.irrefl _) (by decide)
    · rw [hq'.2.2.1 rfl]; exact iff_of_false (hYA up (hp'.2.1 rfl) 0) (by decide)
    · rw [hq'.2.2.2.1 rfl]; exact iff_of_false (hYA up (hp'.2.1 rfl) 1) (by decide)
    · rw [hq'.2.2.2.2.1 rfl]; exact iff_of_false (hYA up (hp'.2.1 rfl) 2) (by decide)
    · rw [hq'.2.2.2.2.2.1 rfl]; exact iff_of_true (hYU up (hp'.2.1 rfl) 0) (by decide)
    · rw [hq'.2.2.2.2.2.2.1 rfl]; exact iff_of_true (hYU up (hp'.2.1 rfl) 1) (by decide)
    · rw [hq'.2.2.2.2.2.2.2 rfl]; exact iff_of_true (hYU up (hp'.2.1 rfl) 2) (by decide)
    · rw [hp'.2.2.1 rfl, hq'.1 rfl]; exact iff_of_true (hxa 0).symm (by decide)
    · rw [hp'.2.2.1 rfl]; exact iff_of_false (fun h => hYA uq (hq'.2.1 rfl) 0 h.symm) (by decide)
    · rw [hp'.2.2.1 rfl, hq'.2.2.1 rfl]; exact iff_of_false (hAA 0 0) (by decide)
    · rw [hp'.2.2.1 rfl, hq'.2.2.2.1 rfl]; exact iff_of_false (hAA 0 1) (by decide)
    · rw [hp'.2.2.1 rfl, hq'.2.2.2.2.1 rfl]; exact iff_of_false (hAA 0 2) (by decide)
    · rw [hp'.2.2.1 rfl, hq'.2.2.2.2.2.1 rfl]; exact iff_of_false (ha_na_u 0) (by decide)
    · rw [hp'.2.2.1 rfl, hq'.2.2.2.2.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 0 1 (by decide) _ (D.ha_mem 0) _ (D.hu_mem 1)) (by decide)
    · rw [hp'.2.2.1 rfl, hq'.2.2.2.2.2.2.2 rfl]; exact iff_of_true (D.hAb_comp_U 0 2 (by decide) _ (D.ha_mem 0) _ (D.hu_mem 2)) (by decide)
    · rw [hp'.2.2.2.1 rfl, hq'.1 rfl]; exact iff_of_true (hxa 1).symm (by decide)
    · rw [hp'.2.2.2.1 rfl]; exact iff_of_false (fun h => hYA uq (hq'.2.1 rfl) 1 h.symm) (by decide)
    · rw [hp'.2.2.2.1 rfl, hq'.2.2.1 rfl]; exact iff_of_false (hAA 1 0) (by decide)
    · rw [hp'.2.2.2.1 rfl, hq'.2.2.2.1 rfl]; exact iff_of_false (hAA 1 1) (by decide)
    · rw [hp'.2.2.2.1 rfl, hq'.2.2.2.2.1 rfl]; exact iff_of_false (hAA 1 2) (by decide)
    · rw [hp'.2.2.2.1 rfl, hq'.2.2.2.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 1 0 (by decide) _ (D.ha_mem 1) _ (D.hu_mem 0)) (by decide)
    · rw [hp'.2.2.2.1 rfl, hq'.2.2.2.2.2.2.1 rfl]; exact iff_of_false (ha_na_u 1) (by decide)
    · rw [hp'.2.2.2.1 rfl, hq'.2.2.2.2.2.2.2 rfl]; exact iff_of_true (D.hAb_comp_U 1 2 (by decide) _ (D.ha_mem 1) _ (D.hu_mem 2)) (by decide)
    · rw [hp'.2.2.2.2.1 rfl, hq'.1 rfl]; exact iff_of_true (hxa 2).symm (by decide)
    · rw [hp'.2.2.2.2.1 rfl]; exact iff_of_false (fun h => hYA uq (hq'.2.1 rfl) 2 h.symm) (by decide)
    · rw [hp'.2.2.2.2.1 rfl, hq'.2.2.1 rfl]; exact iff_of_false (hAA 2 0) (by decide)
    · rw [hp'.2.2.2.2.1 rfl, hq'.2.2.2.1 rfl]; exact iff_of_false (hAA 2 1) (by decide)
    · rw [hp'.2.2.2.2.1 rfl, hq'.2.2.2.2.1 rfl]; exact iff_of_false (hAA 2 2) (by decide)
    · rw [hp'.2.2.2.2.1 rfl, hq'.2.2.2.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 2 0 (by decide) _ (D.ha_mem 2) _ (D.hu_mem 0)) (by decide)
    · rw [hp'.2.2.2.2.1 rfl, hq'.2.2.2.2.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 2 1 (by decide) _ (D.ha_mem 2) _ (D.hu_mem 1)) (by decide)
    · rw [hp'.2.2.2.2.1 rfl, hq'.2.2.2.2.2.2.2 rfl]; exact iff_of_false (ha_na_u 2) (by decide)
    · rw [hp'.2.2.2.2.2.1 rfl, hq'.1 rfl]; exact iff_of_false (fun h => hxU 0 h.symm) (by decide)
    · rw [hp'.2.2.2.2.2.1 rfl]; exact iff_of_true (hYU uq (hq'.2.1 rfl) 0).symm (by decide)
    · rw [hp'.2.2.2.2.2.1 rfl, hq'.2.2.1 rfl]; exact iff_of_false (fun h => ha_na_u 0 h.symm) (by decide)
    · rw [hp'.2.2.2.2.2.1 rfl, hq'.2.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 1 0 (by decide) _ (D.ha_mem 1) _ (D.hu_mem 0)).symm (by decide)
    · rw [hp'.2.2.2.2.2.1 rfl, hq'.2.2.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 2 0 (by decide) _ (D.ha_mem 2) _ (D.hu_mem 0)).symm (by decide)
    · rw [hp'.2.2.2.2.2.1 rfl, hq'.2.2.2.2.2.1 rfl]; exact iff_of_false (hUU 0 0) (by decide)
    · rw [hp'.2.2.2.2.2.1 rfl, hq'.2.2.2.2.2.2.1 rfl]; exact iff_of_false (hUU 0 1) (by decide)
    · rw [hp'.2.2.2.2.2.1 rfl, hq'.2.2.2.2.2.2.2 rfl]; exact iff_of_false (hUU 0 2) (by decide)
    · rw [hp'.2.2.2.2.2.2.1 rfl, hq'.1 rfl]; exact iff_of_false (fun h => hxU 1 h.symm) (by decide)
    · rw [hp'.2.2.2.2.2.2.1 rfl]; exact iff_of_true (hYU uq (hq'.2.1 rfl) 1).symm (by decide)
    · rw [hp'.2.2.2.2.2.2.1 rfl, hq'.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 0 1 (by decide) _ (D.ha_mem 0) _ (D.hu_mem 1)).symm (by decide)
    · rw [hp'.2.2.2.2.2.2.1 rfl, hq'.2.2.2.1 rfl]; exact iff_of_false (fun h => ha_na_u 1 h.symm) (by decide)
    · rw [hp'.2.2.2.2.2.2.1 rfl, hq'.2.2.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 2 1 (by decide) _ (D.ha_mem 2) _ (D.hu_mem 1)).symm (by decide)
    · rw [hp'.2.2.2.2.2.2.1 rfl, hq'.2.2.2.2.2.1 rfl]; exact iff_of_false (hUU 1 0) (by decide)
    · rw [hp'.2.2.2.2.2.2.1 rfl, hq'.2.2.2.2.2.2.1 rfl]; exact iff_of_false (hUU 1 1) (by decide)
    · rw [hp'.2.2.2.2.2.2.1 rfl, hq'.2.2.2.2.2.2.2 rfl]; exact iff_of_false (hUU 1 2) (by decide)
    · rw [hp'.2.2.2.2.2.2.2 rfl, hq'.1 rfl]; exact iff_of_false (fun h => hxU 2 h.symm) (by decide)
    · rw [hp'.2.2.2.2.2.2.2 rfl]; exact iff_of_true (hYU uq (hq'.2.1 rfl) 2).symm (by decide)
    · rw [hp'.2.2.2.2.2.2.2 rfl, hq'.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 0 2 (by decide) _ (D.ha_mem 0) _ (D.hu_mem 2)).symm (by decide)
    · rw [hp'.2.2.2.2.2.2.2 rfl, hq'.2.2.2.1 rfl]; exact iff_of_true (D.hAb_comp_U 1 2 (by decide) _ (D.ha_mem 1) _ (D.hu_mem 2)).symm (by decide)
    · rw [hp'.2.2.2.2.2.2.2 rfl, hq'.2.2.2.2.1 rfl]; exact iff_of_false (fun h => ha_na_u 2 h.symm) (by decide)
    · rw [hp'.2.2.2.2.2.2.2 rfl, hq'.2.2.2.2.2.1 rfl]; exact iff_of_false (hUU 2 0) (by decide)
    · rw [hp'.2.2.2.2.2.2.2 rfl, hq'.2.2.2.2.2.2.1 rfl]; exact iff_of_false (hUU 2 1) (by decide)
    · rw [hp'.2.2.2.2.2.2.2 rfl, hq'.2.2.2.2.2.2.2 rfl]; exact iff_of_false (hUU 2 2) (by decide)
  · intro p up hp r z hz
    rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin3_cases r with rfl | rfl | rfl
    all_goals first
      | (injection hp with h; subst h; exact iff_of_false (D.hx_na_I _ z hz) (by decide))
      | (exact iff_of_false (D.hY_na_I _ up ((hyf_spec up).mp hp) z hz) (by decide))
      | (injection hp with h; subst h; exact iff_of_true (D.hcomp_aIuI _ z hz).1 (by decide))
      | (injection hp with h; subst h; exact iff_of_true (D.hcomp_aIuI _ z hz).2 (by decide))
      | (injection hp with h; subst h; exact iff_of_false (D.hAb_na_I _ _ (by decide) _ (D.ha_mem _) z hz) (by decide))
      | (injection hp with h; subst h; exact iff_of_false (D.hUb_na_I _ _ (by decide) _ (D.hu_mem _) z hz) (by decide))

/-- Claim 13 Subcase 3a: `I2p.Nonempty` contradicts minimality of `ω x` or `deg(x)`. -/
lemma regular_subcase3a {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (G : IsGood H) (ω : U → ℝ) (δ : ℝ)
    (D : RegDecomp H G ω δ)
    (r1 r2 r3 : Fin 3) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (p3 z0 z1 q : U) (hp3 : p3 ∈ D.A_b r3) (hz0 : z0 ∈ D.I_b r3) (hz1 : z1 ∈ D.I_b r3)
    (hnp3z1 : ¬ H.Adj p3 z1)
    (h3unif : ∀ zA ∈ D.I_b r3, ∀ zB ∈ D.I_b r3, ∀ t ∈ D.I_b r1 ∪ D.I_b r2, H.Adj zA t ↔ H.Adj zB t)
    (hA1_eq : D.A_b r1 = {D.a_b r1}) (hU1_eq : D.U_b r1 = {D.u_b r1})
    (hT1_ne : ((D.I_b r1).filter (H.Adj z0)).Nonempty)
    (hT2_ne : ((D.I_b r2).filter (H.Adj z0)).Nonempty)
    (hq_in : q ∈ (D.I_b r1).filter (fun z => ¬ H.Adj z0 z))
    (hI1p_eq : (D.I_b r1).filter (fun z => ¬ H.Adj z0 z) = {q})
    (hI1p_comp2 : ∀ q' ∈ (D.I_b r1).filter (fun z => ¬ H.Adj z0 z), ∀ y ∈ D.I_b r2, H.Adj q' y)
    (hI1p_na3 : ∀ q' ∈ (D.I_b r1).filter (fun z => ¬ H.Adj z0 z), ∀ z' ∈ D.I_b r3, ¬ H.Adj q' z')
    (hI2p_ne : ((D.I_b r2).filter (fun z => ¬ H.Adj z0 z)).Nonempty) : False := by
  let T1 := (D.I_b r1).filter (H.Adj z0)
  let T2 := (D.I_b r2).filter (H.Adj z0)
  let I1p := (D.I_b r1).filter (fun z => ¬ H.Adj z0 z)
  let I2p := (D.I_b r2).filter (fun z => ¬ H.Adj z0 z)
  have hq_I1 : q ∈ D.I_b r1 := (Finset.mem_filter.mp hq_in).1
  have hT12_na : ∀ t1 ∈ T1, ∀ t2 ∈ T2, ¬ H.Adj t1 t2 := fun t1 ht1 t2 ht2 h =>
    tf_contra G.hTF (Finset.mem_filter.mp ht1).2 h (Finset.mem_filter.mp ht2).2
  have hA2U2 : D.A_b r2 = {D.a_b r2} ∧ D.U_b r2 = {D.u_b r2} := by
    apply D.hcl12_b r2; intro p hp y1 hy1 y2 hy2; by_contra hdiff
    have hsp2 : ∃ p' ∈ D.A_b r2 ∪ D.U_b r2, ∃ uA ∈ D.I_b r2, ∃ uB ∈ D.I_b r2, H.Adj p' uA ∧ ¬ H.Adj p' uB := by
      by_cases h1 : H.Adj p y1
      · exact ⟨p, hp, y1, hy1, y2, hy2, h1, fun h2 => hdiff (iff_of_true h1 h2)⟩
      · exact ⟨p, hp, y2, hy2, y1, hy1, by_contra (fun h2 => hdiff (iff_of_false h1 h2)), h1⟩
    have h2unif := (D.hsplit_b r1 r3 r2 h13 h12 h23.symm hsp2).2
    obtain ⟨t2, ht2⟩ := hT2_ne; obtain ⟨r0, hr0⟩ := hI2p_ne
    exact (Finset.mem_filter.mp hr0).2 ((h2unif t2 (Finset.mem_filter.mp ht2).1 r0 (Finset.mem_filter.mp hr0).1 z0 (Finset.mem_union_right _ hz0)).mp (Finset.mem_filter.mp ht2).2.symm).symm
  obtain ⟨hA2_eq, hU2_eq⟩ := hA2U2
  have hI2p_comp1 : ∀ r0 ∈ I2p, ∀ x1 ∈ D.I_b r1, H.Adj r0 x1 := by
    intro r0 hr0 x1 hx1; by_contra hna
    have hr0_2 := (Finset.mem_filter.mp hr0).1
    have hne : r0 ≠ x1 := fun h => Finset.disjoint_left.mp (D.hIb_disj r1 r2 h12) hx1 (h ▸ hr0_2)
    obtain ⟨z', hr0z', hx1z'⟩ := G.hMax r0 x1 hne hna
    have hz'3 : z' ∈ D.I_b r3 := D.hcom_II r2 r1 r3 h12.symm h23 h13 r0 hr0_2 x1 hx1 z' hr0z' hx1z'
    exact (Finset.mem_filter.mp hr0).2 ((h3unif z' hz'3 z0 hz0 r0 (Finset.mem_union_right _ hr0_2)).mp hr0z'.symm)
  have hI2p_na3 : ∀ r0 ∈ I2p, ∀ z' ∈ D.I_b r3, ¬ H.Adj r0 z' := fun r0 hr0 z' hz' h =>
    (Finset.mem_filter.mp hr0).2 ((h3unif z' hz' z0 hz0 r0 (Finset.mem_union_right _ (Finset.mem_filter.mp hr0).1)).mp h.symm)
  obtain ⟨r0, hr0_in⟩ := hI2p_ne
  have hr0_I2 : r0 ∈ D.I_b r2 := (Finset.mem_filter.mp hr0_in).1
  have hI2p_eq : I2p = {r0} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hr0_in, fun r' hr' => by
    apply G.hTwin r' r0; intro z; have hr'2 := (Finset.mem_filter.mp hr').1
    rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
    · exact ⟨fun h => (D.hY_na_I r2 z hY r' hr'2 h.symm).elim, fun h => (D.hY_na_I r2 z hY r0 hr0_I2 h.symm).elim⟩
    · exact ⟨fun h => (D.hAb_na_I r1 r2 h12 z hA1 r' hr'2 h.symm).elim, fun h => (D.hAb_na_I r1 r2 h12 z hA1 r0 hr0_I2 h.symm).elim⟩
    · rw [hA2_eq, Finset.mem_singleton] at hA2; subst hA2
      exact ⟨fun _ => (D.hcomp_aIuI r2 r0 hr0_I2).1.symm, fun _ => (D.hcomp_aIuI r2 r' hr'2).1.symm⟩
    · exact ⟨fun h => (D.hAb_na_I r3 r2 h23.symm z hA3 r' hr'2 h.symm).elim, fun h => (D.hAb_na_I r3 r2 h23.symm z hA3 r0 hr0_I2 h.symm).elim⟩
    · exact ⟨fun h => (D.hx_na_I r2 r' hr'2 h.symm).elim, fun h => (D.hx_na_I r2 r0 hr0_I2 h.symm).elim⟩
    · exact ⟨fun h => (D.hUb_na_I r1 r2 h12 z hU1 r' hr'2 h.symm).elim, fun h => (D.hUb_na_I r1 r2 h12 z hU1 r0 hr0_I2 h.symm).elim⟩
    · rw [hU2_eq, Finset.mem_singleton] at hU2; subst hU2
      exact ⟨fun _ => (D.hcomp_aIuI r2 r0 hr0_I2).2.symm, fun _ => (D.hcomp_aIuI r2 r' hr'2).2.symm⟩
    · exact ⟨fun h => (D.hUb_na_I r3 r2 h23.symm z hU3 r' hr'2 h.symm).elim, fun h => (D.hUb_na_I r3 r2 h23.symm z hU3 r0 hr0_I2 h.symm).elim⟩
    · exact ⟨fun _ => hI2p_comp1 r0 hr0_in z hI1, fun _ => hI2p_comp1 r' hr' z hI1⟩
    · exact ⟨fun h => (D.hIb_ind r2 r' hr'2 z hI2 h).elim, fun h => (D.hIb_ind r2 r0 hr0_I2 z hI2 h).elim⟩
    · exact ⟨fun h => (hI2p_na3 r' hr' z hI3 h).elim, fun h => (hI2p_na3 r0 hr0_in z hI3 h).elim⟩⟩
  obtain ⟨t1, ht1_in⟩ := hT1_ne; obtain ⟨t2, ht2_in⟩ := hT2_ne
  have ht1_I1 : t1 ∈ D.I_b r1 := (Finset.mem_filter.mp ht1_in).1
  have ht2_I2 : t2 ∈ D.I_b r2 := (Finset.mem_filter.mp ht2_in).1
  have hT1_eq : T1 = {t1} := Finset.eq_singleton_iff_unique_mem.mpr ⟨ht1_in, fun t' ht' => by
    apply G.hTwin t' t1; intro z; have ht'1 := (Finset.mem_filter.mp ht').1
    rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
    · exact ⟨fun h => (D.hY_na_I r1 z hY t' ht'1 h.symm).elim, fun h => (D.hY_na_I r1 z hY t1 ht1_I1 h.symm).elim⟩
    · rw [hA1_eq, Finset.mem_singleton] at hA1; subst hA1
      exact ⟨fun _ => (D.hcomp_aIuI r1 t1 ht1_I1).1.symm, fun _ => (D.hcomp_aIuI r1 t' ht'1).1.symm⟩
    · exact ⟨fun h => (D.hAb_na_I r2 r1 h12.symm z hA2 t' ht'1 h.symm).elim, fun h => (D.hAb_na_I r2 r1 h12.symm z hA2 t1 ht1_I1 h.symm).elim⟩
    · exact ⟨fun h => (D.hAb_na_I r3 r1 h13.symm z hA3 t' ht'1 h.symm).elim, fun h => (D.hAb_na_I r3 r1 h13.symm z hA3 t1 ht1_I1 h.symm).elim⟩
    · exact ⟨fun h => (D.hx_na_I r1 t' ht'1 h.symm).elim, fun h => (D.hx_na_I r1 t1 ht1_I1 h.symm).elim⟩
    · rw [hU1_eq, Finset.mem_singleton] at hU1; subst hU1
      exact ⟨fun _ => (D.hcomp_aIuI r1 t1 ht1_I1).2.symm, fun _ => (D.hcomp_aIuI r1 t' ht'1).2.symm⟩
    · exact ⟨fun h => (D.hUb_na_I r2 r1 h12.symm z hU2 t' ht'1 h.symm).elim, fun h => (D.hUb_na_I r2 r1 h12.symm z hU2 t1 ht1_I1 h.symm).elim⟩
    · exact ⟨fun h => (D.hUb_na_I r3 r1 h13.symm z hU3 t' ht'1 h.symm).elim, fun h => (D.hUb_na_I r3 r1 h13.symm z hU3 t1 ht1_I1 h.symm).elim⟩
    · exact ⟨fun h => (D.hIb_ind r1 t' ht'1 z hI1 h).elim, fun h => (D.hIb_ind r1 t1 ht1_I1 z hI1 h).elim⟩
    · by_cases hzT2 : H.Adj z0 z
      · have hz2' : z ∈ T2 := Finset.mem_filter.mpr ⟨hI2, hzT2⟩
        exact ⟨fun h => (hT12_na t' ht' z hz2' h).elim, fun h => (hT12_na t1 ht1_in z hz2' h).elim⟩
      · have hz2' : z ∈ I2p := Finset.mem_filter.mpr ⟨hI2, hzT2⟩
        exact ⟨fun _ => (hI2p_comp1 z hz2' t1 ht1_I1).symm, fun _ => (hI2p_comp1 z hz2' t' ht'1).symm⟩
    · exact ⟨fun _ => ((h3unif z0 hz0 z hI3 t1 (Finset.mem_union_left _ ht1_I1)).mp (Finset.mem_filter.mp ht1_in).2).symm,
             fun _ => ((h3unif z0 hz0 z hI3 t' (Finset.mem_union_left _ ht'1)).mp (Finset.mem_filter.mp ht').2).symm⟩⟩
  have hT2_eq : T2 = {t2} := Finset.eq_singleton_iff_unique_mem.mpr ⟨ht2_in, fun t' ht' => by
    apply G.hTwin t' t2; intro z; have ht'2 := (Finset.mem_filter.mp ht').1
    rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
    · exact ⟨fun h => (D.hY_na_I r2 z hY t' ht'2 h.symm).elim, fun h => (D.hY_na_I r2 z hY t2 ht2_I2 h.symm).elim⟩
    · exact ⟨fun h => (D.hAb_na_I r1 r2 h12 z hA1 t' ht'2 h.symm).elim, fun h => (D.hAb_na_I r1 r2 h12 z hA1 t2 ht2_I2 h.symm).elim⟩
    · rw [hA2_eq, Finset.mem_singleton] at hA2; subst hA2
      exact ⟨fun _ => (D.hcomp_aIuI r2 t2 ht2_I2).1.symm, fun _ => (D.hcomp_aIuI r2 t' ht'2).1.symm⟩
    · exact ⟨fun h => (D.hAb_na_I r3 r2 h23.symm z hA3 t' ht'2 h.symm).elim, fun h => (D.hAb_na_I r3 r2 h23.symm z hA3 t2 ht2_I2 h.symm).elim⟩
    · exact ⟨fun h => (D.hx_na_I r2 t' ht'2 h.symm).elim, fun h => (D.hx_na_I r2 t2 ht2_I2 h.symm).elim⟩
    · exact ⟨fun h => (D.hUb_na_I r1 r2 h12 z hU1 t' ht'2 h.symm).elim, fun h => (D.hUb_na_I r1 r2 h12 z hU1 t2 ht2_I2 h.symm).elim⟩
    · rw [hU2_eq, Finset.mem_singleton] at hU2; subst hU2
      exact ⟨fun _ => (D.hcomp_aIuI r2 t2 ht2_I2).2.symm, fun _ => (D.hcomp_aIuI r2 t' ht'2).2.symm⟩
    · exact ⟨fun h => (D.hUb_na_I r3 r2 h23.symm z hU3 t' ht'2 h.symm).elim, fun h => (D.hUb_na_I r3 r2 h23.symm z hU3 t2 ht2_I2 h.symm).elim⟩
    · by_cases hzT1 : H.Adj z0 z
      · have hz1' : z ∈ T1 := Finset.mem_filter.mpr ⟨hI1, hzT1⟩
        exact ⟨fun h => (hT12_na z hz1' t' ht' h.symm).elim, fun h => (hT12_na z hz1' t2 ht2_in h.symm).elim⟩
      · have hz1' : z ∈ I1p := Finset.mem_filter.mpr ⟨hI1, hzT1⟩
        exact ⟨fun _ => (hI1p_comp2 z hz1' t2 ht2_I2).symm, fun _ => (hI1p_comp2 z hz1' t' ht'2).symm⟩
    · exact ⟨fun h => (D.hIb_ind r2 t' ht'2 z hI2 h).elim, fun h => (D.hIb_ind r2 t2 ht2_I2 z hI2 h).elim⟩
    · exact ⟨fun _ => ((h3unif z0 hz0 z hI3 t2 (Finset.mem_union_right _ ht2_I2)).mp (Finset.mem_filter.mp ht2_in).2).symm,
             fun _ => ((h3unif z0 hz0 z hI3 t' (Finset.mem_union_right _ ht'2)).mp (Finset.mem_filter.mp ht').2).symm⟩⟩
  have hq_ne_t1 : q ≠ t1 := fun h => (Finset.mem_filter.mp hq_in).2 (h ▸ (Finset.mem_filter.mp ht1_in).2)
  have hr0_ne_t2 : r0 ≠ t2 := fun h => (Finset.mem_filter.mp hr0_in).2 (h ▸ (Finset.mem_filter.mp ht2_in).2)
  have hI1_pair : D.I_b r1 = {q, t1} := by
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
    · intro hz; by_cases h : H.Adj z0 z
      · right; exact Finset.mem_singleton.mp (hT1_eq ▸ Finset.mem_filter.mpr ⟨hz, h⟩)
      · left; exact Finset.mem_singleton.mp (hI1p_eq ▸ Finset.mem_filter.mpr ⟨hz, h⟩)
    · rintro (rfl | rfl) <;> assumption
  have hI2_pair : D.I_b r2 = {r0, t2} := by
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
    · intro hz; by_cases h : H.Adj z0 z
      · right; exact Finset.mem_singleton.mp (hT2_eq ▸ Finset.mem_filter.mpr ⟨hz, h⟩)
      · left; exact Finset.mem_singleton.mp (hI2p_eq ▸ Finset.mem_filter.mpr ⟨hz, h⟩)
    · rintro (rfl | rfl) <;> assumption
  have hNq : Finset.univ.filter (H.Adj q) = {D.a_b r1, D.u_b r1, r0, t2} := by
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]; constructor
    · intro hqz
      rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
      · exact (D.hY_na_I r1 z hY q hq_I1 hqz.symm).elim
      · rw [hA1_eq, Finset.mem_singleton] at hA1; exact Or.inl hA1
      · exact (D.hAb_na_I r2 r1 h12.symm z hA2 q hq_I1 hqz.symm).elim
      · exact (D.hAb_na_I r3 r1 h13.symm z hA3 q hq_I1 hqz.symm).elim
      · exact (D.hx_na_I r1 q hq_I1 hqz.symm).elim
      · rw [hU1_eq, Finset.mem_singleton] at hU1; exact Or.inr (Or.inl hU1)
      · exact (D.hUb_na_I r2 r1 h12.symm z hU2 q hq_I1 hqz.symm).elim
      · exact (D.hUb_na_I r3 r1 h13.symm z hU3 q hq_I1 hqz.symm).elim
      · exact (D.hIb_ind r1 q hq_I1 z hI1 hqz).elim
      · rw [hI2_pair, Finset.mem_insert, Finset.mem_singleton] at hI2; rcases hI2 with rfl | rfl <;> simp
      · exact (hI1p_na3 q hq_in z hI3 hqz).elim
    · rintro (rfl | rfl | rfl | rfl)
      · exact (D.hcomp_aIuI r1 q hq_I1).1.symm
      · exact (D.hcomp_aIuI r1 q hq_I1).2.symm
      · exact hI1p_comp2 q hq_in z hr0_I2
      · exact hI1p_comp2 q hq_in z ht2_I2
  have hNr0 : Finset.univ.filter (H.Adj r0) = {D.a_b r2, D.u_b r2, q, t1} := by
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]; constructor
    · intro hrz
      rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
      · exact (D.hY_na_I r2 z hY r0 hr0_I2 hrz.symm).elim
      · exact (D.hAb_na_I r1 r2 h12 z hA1 r0 hr0_I2 hrz.symm).elim
      · rw [hA2_eq, Finset.mem_singleton] at hA2; exact Or.inl hA2
      · exact (D.hAb_na_I r3 r2 h23.symm z hA3 r0 hr0_I2 hrz.symm).elim
      · exact (D.hx_na_I r2 r0 hr0_I2 hrz.symm).elim
      · exact (D.hUb_na_I r1 r2 h12 z hU1 r0 hr0_I2 hrz.symm).elim
      · rw [hU2_eq, Finset.mem_singleton] at hU2; exact Or.inr (Or.inl hU2)
      · exact (D.hUb_na_I r3 r2 h23.symm z hU3 r0 hr0_I2 hrz.symm).elim
      · rw [hI1_pair, Finset.mem_insert, Finset.mem_singleton] at hI1; rcases hI1 with rfl | rfl <;> simp
      · exact (D.hIb_ind r2 r0 hr0_I2 z hI2 hrz).elim
      · exact (hI2p_na3 r0 hr0_in z hI3 hrz).elim
    · rintro (rfl | rfl | rfl | rfl)
      · exact (D.hcomp_aIuI r2 r0 hr0_I2).1.symm
      · exact (D.hcomp_aIuI r2 r0 hr0_I2).2.symm
      · exact hI2p_comp1 r0 hr0_in z hq_I1
      · exact hI2p_comp1 r0 hr0_in z ht1_I1
  have hNt2 : Finset.univ.filter (H.Adj t2) = {D.a_b r2, D.u_b r2, q} ∪ D.I_b r3 := by
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; constructor
    · intro htz
      rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
      · exact (D.hY_na_I r2 z hY t2 ht2_I2 htz.symm).elim
      · exact (D.hAb_na_I r1 r2 h12 z hA1 t2 ht2_I2 htz.symm).elim
      · rw [hA2_eq, Finset.mem_singleton] at hA2; exact Or.inl (Or.inl hA2)
      · exact (D.hAb_na_I r3 r2 h23.symm z hA3 t2 ht2_I2 htz.symm).elim
      · exact (D.hx_na_I r2 t2 ht2_I2 htz.symm).elim
      · exact (D.hUb_na_I r1 r2 h12 z hU1 t2 ht2_I2 htz.symm).elim
      · rw [hU2_eq, Finset.mem_singleton] at hU2; exact Or.inl (Or.inr (Or.inl hU2))
      · exact (D.hUb_na_I r3 r2 h23.symm z hU3 t2 ht2_I2 htz.symm).elim
      · rw [hI1_pair, Finset.mem_insert, Finset.mem_singleton] at hI1
        rcases hI1 with rfl | rfl
        · exact Or.inl (Or.inr (Or.inr rfl))
        · exact (hT12_na z ht1_in t2 ht2_in htz.symm).elim
      · exact (D.hIb_ind r2 t2 ht2_I2 z hI2 htz).elim
      · exact Or.inr hI3
    · rintro ((rfl | rfl | rfl) | h3)
      · exact (D.hcomp_aIuI r2 t2 ht2_I2).1.symm
      · exact (D.hcomp_aIuI r2 t2 ht2_I2).2.symm
      · exact (hI1p_comp2 z hq_in t2 ht2_I2).symm
      · exact ((h3unif z0 hz0 z h3 t2 (Finset.mem_union_right _ ht2_I2)).mp (Finset.mem_filter.mp ht2_in).2).symm
  have hne_au : ∀ r : Fin 3, D.a_b r ≠ D.u_b r := fun r => D.hdisj_NR' (D.a_b r) (D.hAb_sub r (D.ha_mem r)) (D.u_b r) (D.hUb_sub r (D.hu_mem r))
  have hne_aI : ∀ r r' : Fin 3, ∀ z ∈ D.I_b r', D.a_b r ≠ z := fun r r' z hz h => (D.hIb_out r' z hz).1 (h ▸ D.hAb_sub r (D.ha_mem r))
  have hne_uI : ∀ r r' : Fin 3, ∀ z ∈ D.I_b r', D.u_b r ≠ z := fun r r' z hz h => (D.hIb_out r' z hz).2 (h ▸ D.hUb_sub r (D.hu_mem r))
  have hw_q : ω (D.a_b r1) + ω (D.u_b r1) + wsum ω (D.I_b r2) = δ := by
    have h1 : wsum ω (Finset.univ.filter (H.Adj q)) = δ := by rw [← D.hreg q, wdeg, ← Finset.sum_filter]; rfl
    rw [hNq, wsum, Finset.sum_insert (by simp [hne_au r1, hne_aI r1 r2 r0 hr0_I2, hne_aI r1 r2 t2 ht2_I2]),
        Finset.sum_insert (by simp [hne_uI r1 r2 r0 hr0_I2, hne_uI r1 r2 t2 ht2_I2]),
        Finset.sum_insert (by simp [hr0_ne_t2]), Finset.sum_singleton] at h1
    have h2 : wsum ω (D.I_b r2) = ω r0 + ω t2 := by rw [hI2_pair, wsum, Finset.sum_insert (by simp [hr0_ne_t2]), Finset.sum_singleton]
    linarith only [h1, h2]
  have hw_r0 : ω (D.a_b r2) + ω (D.u_b r2) + wsum ω (D.I_b r1) = δ := by
    have h1 : wsum ω (Finset.univ.filter (H.Adj r0)) = δ := by rw [← D.hreg r0, wdeg, ← Finset.sum_filter]; rfl
    rw [hNr0, wsum, Finset.sum_insert (by simp [hne_au r2, hne_aI r2 r1 q hq_I1, hne_aI r2 r1 t1 ht1_I1]),
        Finset.sum_insert (by simp [hne_uI r2 r1 q hq_I1, hne_uI r2 r1 t1 ht1_I1]),
        Finset.sum_insert (by simp [hq_ne_t1]), Finset.sum_singleton] at h1
    have h2 : wsum ω (D.I_b r1) = ω q + ω t1 := by rw [hI1_pair, wsum, Finset.sum_insert (by simp [hq_ne_t1]), Finset.sum_singleton]
    linarith only [h1, h2]
  have hw_t2 : ω (D.a_b r2) + ω (D.u_b r2) + ω q + wsum ω (D.I_b r3) = δ := by
    have h1 : wsum ω (Finset.univ.filter (H.Adj t2)) = δ := by rw [← D.hreg t2, wdeg, ← Finset.sum_filter]; rfl
    rw [hNt2, wsum, Finset.sum_union, Finset.sum_insert (by simp [hne_au r2, hne_aI r2 r1 q hq_I1]),
        Finset.sum_insert (by simp [hne_uI r2 r1 q hq_I1]), Finset.sum_singleton] at h1
    · change ω (D.a_b r2) + (ω (D.u_b r2) + ω q) + wsum ω (D.I_b r3) = δ at h1; linarith only [h1]
    · exact Finset.disjoint_left.mpr fun z hz h3 => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hne_aI r2 r3 _ h3 rfl
        · exact hne_uI r2 r3 _ h3 rfl
        · exact Finset.disjoint_left.mp (D.hIb_disj r1 r3 h13) hq_I1 h3
  have hw_I1_eq : wsum ω (D.I_b r1) = ω q + ω t1 := by rw [hI1_pair, wsum, Finset.sum_insert (by simp [hq_ne_t1]), Finset.sum_singleton]
  have hw_A1_eq : wsum ω (D.A_b r1) = ω (D.a_b r1) := by rw [hA1_eq, wsum, Finset.sum_singleton]
  have hw_A2_eq : wsum ω (D.A_b r2) = ω (D.a_b r2) := by rw [hA2_eq, wsum, Finset.sum_singleton]
  have hw_U1_eq : wsum ω (D.U_b r1) = ω (D.u_b r1) := by rw [hU1_eq, wsum, Finset.sum_singleton]
  have hw_t1_eq : ω t1 = wsum ω (D.I_b r3) := by linarith only [hw_r0, hw_t2, hw_I1_eq]
  have hwNx' := D.hw_Nx_b r1 r2 r3 h12 h13 h23
  have hw1A := D.hw_Ab r1; have hw2A := D.hw_Ab r2; have hw3A := D.hw_Ab r3; have hw1U := D.hw_Ub r1
  by_cases hY_empty : D.Y_set = ∅
  · have hwY0 : wsum ω D.Y_set = 0 := by rw [wsum, hY_empty, Finset.sum_empty]
    have hq_half : ω q = ω D.x / 2 := by
      linarith only [hw_q, hw_t1_eq, hw_I1_eq, hw_A1_eq, hw_A2_eq, hw_U1_eq, hwNx', hw1A, hw2A, hw3A, hw1U, D.hw_xY, hwY0]
    linarith only [hq_half, D.hx_wmin q, D.hpos D.x]
  · obtain ⟨y, hyY⟩ := Finset.nonempty_iff_ne_empty.mpr hY_empty
    have hY_eq : D.Y_set = {y} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hyY, fun y' hy' => D.hY_subsing y' hy' y hyY⟩
    have hwY_eq : wsum ω D.Y_set = ω y := by rw [hY_eq, wsum, Finset.sum_singleton]
    have hwy_deg : wsum ω D.R_set = δ := by
      have h1 : wsum ω (Finset.univ.filter (H.Adj y)) = δ := by rw [← D.hreg y, wdeg, ← Finset.sum_filter]; rfl
      have h2 : Finset.univ.filter (H.Adj y) = D.R_set := by ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact D.hY_nbhd y hyY z
      rw [h2] at h1; exact h1
    have hwx_eq_y : ω D.x = ω y ∧ 3 * δ - 1 - ω D.x = 0 := by constructor <;> linarith only [D.hwRval, hwy_deg, D.hw_xY, hwY_eq]
    have hwq_eq_x : ω q = ω D.x := by
      linarith only [hw_q, hw_t1_eq, hw_I1_eq, hw_A1_eq, hw_A2_eq, hw_U1_eq, hwNx', hw1A, hw2A, hw3A, hw1U, hwY_eq, hwx_eq_y.1, hwx_eq_y.2]
    have hdq_le4 : #(Finset.univ.filter (H.Adj q)) ≤ 4 := by
      rw [hNq]
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans (by simp)) _)) _)
    have hp3_ne_a3 : p3 ≠ D.a_b r3 := fun h => hnp3z1 (h ▸ (D.hcomp_aIuI r3 z1 hz1).1)
    have hsub5 : ({y, D.a_b r1, D.a_b r2, D.a_b r3, p3} : Finset U) ⊆ Finset.univ.filter (H.Adj D.x) := by
      intro z hz; rw [← D.hNx_eq]; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact D.hY_sub hyY
      · exact D.hAb_sub r1 (D.ha_mem r1)
      · exact D.hAb_sub r2 (D.ha_mem r2)
      · exact D.hAb_sub r3 (D.ha_mem r3)
      · exact D.hAb_sub r3 hp3
    have hY_disj_A' : ∀ r : Fin 3, ∀ z ∈ D.A_b r, y ≠ z := fun r z hz h =>
      Finset.disjoint_left.mp (D.hY_disj_A r) hyY (h ▸ hz)
    have hy_na1 : y ≠ D.a_b r1 := hY_disj_A' r1 _ (D.ha_mem r1)
    have hy_na2 : y ≠ D.a_b r2 := hY_disj_A' r2 _ (D.ha_mem r2)
    have hy_na3 : y ≠ D.a_b r3 := hY_disj_A' r3 _ (D.ha_mem r3)
    have hy_np3 : y ≠ p3 := hY_disj_A' r3 _ hp3
    have ha12 : D.a_b r1 ≠ D.a_b r2 := fun h => Finset.disjoint_left.mp (D.hAb_disj r1 r2 h12) (D.ha_mem r1) (h ▸ D.ha_mem r2)
    have ha13 : D.a_b r1 ≠ D.a_b r3 := fun h => Finset.disjoint_left.mp (D.hAb_disj r1 r3 h13) (D.ha_mem r1) (h ▸ D.ha_mem r3)
    have ha1p : D.a_b r1 ≠ p3 := fun h => Finset.disjoint_left.mp (D.hAb_disj r1 r3 h13) (D.ha_mem r1) (h ▸ hp3)
    have ha23 : D.a_b r2 ≠ D.a_b r3 := fun h => Finset.disjoint_left.mp (D.hAb_disj r2 r3 h23) (D.ha_mem r2) (h ▸ D.ha_mem r3)
    have ha2p : D.a_b r2 ≠ p3 := fun h => Finset.disjoint_left.mp (D.hAb_disj r2 r3 h23) (D.ha_mem r2) (h ▸ hp3)
    have ha3p : D.a_b r3 ≠ p3 := hp3_ne_a3.symm
    have hcard5 : #({y, D.a_b r1, D.a_b r2, D.a_b r3, p3} : Finset U) = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hy_na1, hy_na2, hy_na3, hy_np3]),
          Finset.card_insert_of_notMem (by simp [ha12, ha13, ha1p]),
          Finset.card_insert_of_notMem (by simp [ha23, ha2p]),
          Finset.card_insert_of_notMem (by simp [ha3p]), Finset.card_singleton]
    have hdx_ge5 : 5 ≤ #(Finset.univ.filter (H.Adj D.x)) := hcard5 ▸ Finset.card_le_card hsub5
    have hdx_le_dq := D.hx_dmin q hwq_eq_x
    omega

/-- Claim 13 Subcase 3b-ii: `H_12` contradiction via fast 12-tag injectivity + `h12_hits_le_four`! -/
lemma regular_subcase3b_ii {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (G : IsGood H) (ω : U → ℝ) (δ : ℝ)
    (D : RegDecomp H G ω δ)
    (r1 r2 r3 : Fin 3) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (p3 w3 z0 z1 q t1 : U)
    (hp3 : p3 ∈ D.A_b r3) (hw3 : w3 ∈ D.U_b r3) (hz0 : z0 ∈ D.I_b r3) (hz1 : z1 ∈ D.I_b r3)
    (hp3w3 : H.Adj p3 w3) (hp3z0 : H.Adj p3 z0) (hnp3z1 : ¬ H.Adj p3 z1) (hw3z1 : H.Adj w3 z1)
    (h3unif : ∀ zA ∈ D.I_b r3, ∀ zB ∈ D.I_b r3, ∀ t ∈ D.I_b r1 ∪ D.I_b r2, H.Adj zA t ↔ H.Adj zB t)
    (hq_in : q ∈ (D.I_b r1).filter (fun z => ¬ H.Adj z0 z))
    (ht1_in : t1 ∈ (D.I_b r1).filter (H.Adj z0))
    (hq_ne_t1 : q ≠ t1)
    (hI1p_comp2 : ∀ q' ∈ (D.I_b r1).filter (fun z => ¬ H.Adj z0 z), ∀ y ∈ D.I_b r2, H.Adj q' y)
    (hI2_comp3 : ∀ y ∈ D.I_b r2, ∀ z' ∈ D.I_b r3, H.Adj y z')
    (hI2_sp : ∃ q2 ∈ D.A_b r2 ∪ D.U_b r2, ∃ y0 ∈ D.I_b r2, ∃ y1 ∈ D.I_b r2, H.Adj q2 y0 ∧ ¬ H.Adj q2 y1) : False := by
  have hq_I1 : q ∈ D.I_b r1 := (Finset.mem_filter.mp hq_in).1
  have ht1_I1 : t1 ∈ D.I_b r1 := (Finset.mem_filter.mp ht1_in).1
  obtain ⟨⟨p2, hp2, v2, hv2, y0, hy0, y1, hy1, hp2v2, hp2y0, hnp2y1, hv2y1, _⟩, _⟩ :=
    D.hsplit_b r1 r3 r2 h13 h12 h23.symm hI2_sp
  have hy01 : y0 ≠ y1 := fun h => hnp2y1 (h ▸ hp2y0)
  have hz01 : z0 ≠ z1 := fun h => hnp3z1 (h ▸ hp3z0)
  let f12 : Fin 12 → U := fun k => match k.val with
    | 0 => D.a_b r1 | 1 => D.u_b r1 | 2 => q | 3 => t1 | 4 => p2 | 5 => v2
    | 6 => y0 | 7 => y1 | 8 => p3 | 9 => w3 | 10 => z0 | _ => z1
  let tag12 : U → ℕ := fun z =>
    if z ∈ D.A_b r1 then 0 else if z ∈ D.U_b r1 then 1 else if z = q then 2 else if z = t1 then 3
    else if z ∈ D.A_b r2 then 4 else if z ∈ D.U_b r2 then 5 else if z = y0 then 6 else if z = y1 then 7
    else if z ∈ D.A_b r3 then 8 else if z ∈ D.U_b r3 then 9 else if z = z0 then 10 else 11
  have hdisj_NR : ∀ r r', ∀ m ∈ D.A_b r, m ∉ D.U_b r' := fun r r' m hm hm' =>
    D.hdisj_NR' m (D.hAb_sub r hm) m (D.hUb_sub r' hm') rfl
  have hdisj_RN : ∀ r r', ∀ m ∈ D.U_b r, m ∉ D.A_b r' := fun r r' m hm hm' =>
    D.hdisj_NR' m (D.hAb_sub r' hm') m (D.hUb_sub r hm) rfl
  have htag12 : ∀ k : Fin 12, tag12 (f12 k) = k.val := by
    intro k; fin_cases k
    · change tag12 (D.a_b r1) = 0; dsimp only [tag12]; rw [if_pos (D.ha_mem r1)]
    · change tag12 (D.u_b r1) = 1; dsimp only [tag12]; rw [if_neg (hdisj_RN r1 r1 _ (D.hu_mem r1)), if_pos (D.hu_mem r1)]
    · change tag12 q = 2; dsimp only [tag12]
      rw [if_neg (fun h => (D.hIb_out r1 q hq_I1).1 (D.hAb_sub r1 h)),
          if_neg (fun h => (D.hIb_out r1 q hq_I1).2 (D.hUb_sub r1 h)), if_pos rfl]
    · change tag12 t1 = 3; dsimp only [tag12]
      rw [if_neg (fun h => (D.hIb_out r1 t1 ht1_I1).1 (D.hAb_sub r1 h)),
          if_neg (fun h => (D.hIb_out r1 t1 ht1_I1).2 (D.hUb_sub r1 h)), if_neg hq_ne_t1.symm, if_pos rfl]
    · change tag12 p2 = 4; dsimp only [tag12]
      rw [if_neg (fun h => Finset.disjoint_left.mp (D.hAb_disj r1 r2 h12) h hp2),
          if_neg (hdisj_NR r2 r1 _ hp2),
          if_neg (fun h : p2 = q => (D.hIb_out r1 q hq_I1).1 (h ▸ D.hAb_sub r2 hp2)),
          if_neg (fun h : p2 = t1 => (D.hIb_out r1 t1 ht1_I1).1 (h ▸ D.hAb_sub r2 hp2)), if_pos hp2]
    · change tag12 v2 = 5; dsimp only [tag12]
      rw [if_neg (hdisj_RN r2 r1 _ hv2),
          if_neg (fun h => Finset.disjoint_left.mp (D.hUb_disj r1 r2 h12) h hv2),
          if_neg (fun h : v2 = q => (D.hIb_out r1 q hq_I1).2 (h ▸ D.hUb_sub r2 hv2)),
          if_neg (fun h : v2 = t1 => (D.hIb_out r1 t1 ht1_I1).2 (h ▸ D.hUb_sub r2 hv2)),
          if_neg (hdisj_RN r2 r2 _ hv2), if_pos hv2]
    · change tag12 y0 = 6; dsimp only [tag12]
      rw [if_neg (fun h => (D.hIb_out r2 y0 hy0).1 (D.hAb_sub r1 h)),
          if_neg (fun h => (D.hIb_out r2 y0 hy0).2 (D.hUb_sub r1 h)),
          if_neg (fun h : y0 = q => Finset.disjoint_left.mp (D.hIb_disj r1 r2 h12) hq_I1 (h ▸ hy0)),
          if_neg (fun h : y0 = t1 => Finset.disjoint_left.mp (D.hIb_disj r1 r2 h12) ht1_I1 (h ▸ hy0)),
          if_neg (fun h => (D.hIb_out r2 y0 hy0).1 (D.hAb_sub r2 h)),
          if_neg (fun h => (D.hIb_out r2 y0 hy0).2 (D.hUb_sub r2 h)), if_pos rfl]
    · change tag12 y1 = 7; dsimp only [tag12]
      rw [if_neg (fun h => (D.hIb_out r2 y1 hy1).1 (D.hAb_sub r1 h)),
          if_neg (fun h => (D.hIb_out r2 y1 hy1).2 (D.hUb_sub r1 h)),
          if_neg (fun h : y1 = q => Finset.disjoint_left.mp (D.hIb_disj r1 r2 h12) hq_I1 (h ▸ hy1)),
          if_neg (fun h : y1 = t1 => Finset.disjoint_left.mp (D.hIb_disj r1 r2 h12) ht1_I1 (h ▸ hy1)),
          if_neg (fun h => (D.hIb_out r2 y1 hy1).1 (D.hAb_sub r2 h)),
          if_neg (fun h => (D.hIb_out r2 y1 hy1).2 (D.hUb_sub r2 h)), if_neg hy01.symm, if_pos rfl]
    · change tag12 p3 = 8; dsimp only [tag12]
      rw [if_neg (fun h => Finset.disjoint_left.mp (D.hAb_disj r1 r3 h13) h hp3),
          if_neg (hdisj_NR r3 r1 _ hp3),
          if_neg (fun h : p3 = q => (D.hIb_out r1 q hq_I1).1 (h ▸ D.hAb_sub r3 hp3)),
          if_neg (fun h : p3 = t1 => (D.hIb_out r1 t1 ht1_I1).1 (h ▸ D.hAb_sub r3 hp3)),
          if_neg (fun h => Finset.disjoint_left.mp (D.hAb_disj r2 r3 h23) h hp3),
          if_neg (hdisj_NR r3 r2 _ hp3),
          if_neg (fun h : p3 = y0 => (D.hIb_out r2 y0 hy0).1 (h ▸ D.hAb_sub r3 hp3)),
          if_neg (fun h : p3 = y1 => (D.hIb_out r2 y1 hy1).1 (h ▸ D.hAb_sub r3 hp3)), if_pos hp3]
    · change tag12 w3 = 9; dsimp only [tag12]
      rw [if_neg (hdisj_RN r3 r1 _ hw3),
          if_neg (fun h => Finset.disjoint_left.mp (D.hUb_disj r1 r3 h13) h hw3),
          if_neg (fun h : w3 = q => (D.hIb_out r1 q hq_I1).2 (h ▸ D.hUb_sub r3 hw3)),
          if_neg (fun h : w3 = t1 => (D.hIb_out r1 t1 ht1_I1).2 (h ▸ D.hUb_sub r3 hw3)),
          if_neg (hdisj_RN r3 r2 _ hw3),
          if_neg (fun h => Finset.disjoint_left.mp (D.hUb_disj r2 r3 h23) h hw3),
          if_neg (fun h : w3 = y0 => (D.hIb_out r2 y0 hy0).2 (h ▸ D.hUb_sub r3 hw3)),
          if_neg (fun h : w3 = y1 => (D.hIb_out r2 y1 hy1).2 (h ▸ D.hUb_sub r3 hw3)),
          if_neg (hdisj_RN r3 r3 _ hw3), if_pos hw3]
    · change tag12 z0 = 10; dsimp only [tag12]
      rw [if_neg (fun h => (D.hIb_out r3 z0 hz0).1 (D.hAb_sub r1 h)),
          if_neg (fun h => (D.hIb_out r3 z0 hz0).2 (D.hUb_sub r1 h)),
          if_neg (fun h : z0 = q => Finset.disjoint_left.mp (D.hIb_disj r1 r3 h13) hq_I1 (h ▸ hz0)),
          if_neg (fun h : z0 = t1 => Finset.disjoint_left.mp (D.hIb_disj r1 r3 h13) ht1_I1 (h ▸ hz0)),
          if_neg (fun h => (D.hIb_out r3 z0 hz0).1 (D.hAb_sub r2 h)),
          if_neg (fun h => (D.hIb_out r3 z0 hz0).2 (D.hUb_sub r2 h)),
          if_neg (fun h : z0 = y0 => Finset.disjoint_left.mp (D.hIb_disj r2 r3 h23) hy0 (h ▸ hz0)),
          if_neg (fun h : z0 = y1 => Finset.disjoint_left.mp (D.hIb_disj r2 r3 h23) hy1 (h ▸ hz0)),
          if_neg (fun h => (D.hIb_out r3 z0 hz0).1 (D.hAb_sub r3 h)),
          if_neg (fun h => (D.hIb_out r3 z0 hz0).2 (D.hUb_sub r3 h)), if_pos rfl]
    · change tag12 z1 = 11; dsimp only [tag12]
      rw [if_neg (fun h => (D.hIb_out r3 z1 hz1).1 (D.hAb_sub r1 h)),
          if_neg (fun h => (D.hIb_out r3 z1 hz1).2 (D.hUb_sub r1 h)),
          if_neg (fun h : z1 = q => Finset.disjoint_left.mp (D.hIb_disj r1 r3 h13) hq_I1 (h ▸ hz1)),
          if_neg (fun h : z1 = t1 => Finset.disjoint_left.mp (D.hIb_disj r1 r3 h13) ht1_I1 (h ▸ hz1)),
          if_neg (fun h => (D.hIb_out r3 z1 hz1).1 (D.hAb_sub r2 h)),
          if_neg (fun h => (D.hIb_out r3 z1 hz1).2 (D.hUb_sub r2 h)),
          if_neg (fun h : z1 = y0 => Finset.disjoint_left.mp (D.hIb_disj r2 r3 h23) hy0 (h ▸ hz1)),
          if_neg (fun h : z1 = y1 => Finset.disjoint_left.mp (D.hIb_disj r2 r3 h23) hy1 (h ▸ hz1)),
          if_neg (fun h => (D.hIb_out r3 z1 hz1).1 (D.hAb_sub r3 h)),
          if_neg (fun h => (D.hIb_out r3 z1 hz1).2 (D.hUb_sub r3 h)), if_neg hz01.symm]
  have hf12_inj : Function.Injective f12 := fun i j hij =>
    Fin.ext (by rw [← htag12 i, ← htag12 j, hij])
  let S12 := Finset.univ.image f12
  have hS12_card : #S12 = 12 := by rw [Finset.card_image_of_injective _ hf12_inj, Finset.card_univ, Fintype.card_fin]
  refine contra_of_capped_set H D.hnn D.hsum D.hdeg S12 4 ⟨f12 0, Finset.mem_image_of_mem f12 (Finset.mem_univ 0)⟩ (by omega) (fun s => ?_)
  have hbij : #(S12.filter (H.Adj s)) = #(Finset.univ.filter (fun k : Fin 12 => H.Adj s (f12 k))) := by
    refine Finset.card_bij (fun u hu => (Finset.mem_image.mp (Finset.mem_filter.mp hu).1).choose) ?_ ?_ ?_
    · intro u hu; have h1 := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_image.mp h1.1).choose_spec.2.symm ▸ h1.2⟩
    · intro u1 hu1 u2 hu2 heq
      have h1 := (Finset.mem_image.mp (Finset.mem_filter.mp hu1).1).choose_spec.2
      have h2 := (Finset.mem_image.mp (Finset.mem_filter.mp hu2).1).choose_spec.2
      rw [← h1, ← h2, heq]
    · intro k hk
      refine ⟨f12 k, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f12 (Finset.mem_univ k), (Finset.mem_filter.mp hk).2⟩, ?_⟩
      exact hf12_inj (Finset.mem_image.mp (Finset.mem_image_of_mem f12 (Finset.mem_univ k))).choose_spec.2
  rw [hbij]
  exact h12_hits_le_four H G.hTF f12
    (D.hcomp_aIuI r1 q hq_I1).1 (D.hcomp_aIuI r1 t1 ht1_I1).1 (D.hAb_comp_U r1 r2 h12 (D.a_b r1) (D.ha_mem r1) v2 hv2)
    (D.hAb_comp_U r1 r3 h13 (D.a_b r1) (D.ha_mem r1) w3 hw3)
    (D.hcomp_aIuI r1 q hq_I1).2 (D.hcomp_aIuI r1 t1 ht1_I1).2 (D.hAb_comp_U r2 r1 h12.symm p2 hp2 (D.u_b r1) (D.hu_mem r1)).symm
    (D.hAb_comp_U r3 r1 h13.symm p3 hp3 (D.u_b r1) (D.hu_mem r1)).symm
    (hI1p_comp2 q hq_in y0 hy0) (hI1p_comp2 q hq_in y1 hy1)
    (Finset.mem_filter.mp ht1_in).2.symm ((h3unif z0 hz0 z1 hz1 t1 (Finset.mem_union_left _ ht1_I1)).mp (Finset.mem_filter.mp ht1_in).2).symm
    hp2v2 hp2y0 (D.hAb_comp_U r2 r3 h23 p2 hp2 w3 hw3)
    hv2y1 (D.hAb_comp_U r3 r2 h23.symm p3 hp3 v2 hv2).symm
    hp3w3 hp3z0 hw3z1
    (hI2_comp3 y0 hy0 z0 hz0) (hI2_comp3 y0 hy0 z1 hz1) (hI2_comp3 y1 hy1 z0 hz0) (hI2_comp3 y1 hy1 z1 hz1) s

/-- Claim 13 Subcase 3b-i: Frame switch `(q; a1, u1, y0)` into `vega_of_singleton_frame`! -/
lemma regular_subcase3b_i {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (G : IsGood H) (ω : U → ℝ) (δ : ℝ)
    (D : RegDecomp H G ω δ)
    (r1 r2 r3 : Fin 3) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (z0 q t1 : U) (hz0 : z0 ∈ D.I_b r3)
    (h3unif : ∀ zA ∈ D.I_b r3, ∀ zB ∈ D.I_b r3, ∀ t ∈ D.I_b r1 ∪ D.I_b r2, H.Adj zA t ↔ H.Adj zB t)
    (hA1_eq : D.A_b r1 = {D.a_b r1}) (hU1_eq : D.U_b r1 = {D.u_b r1})
    (hq_in : q ∈ (D.I_b r1).filter (fun z => ¬ H.Adj z0 z))
    (ht1_in : t1 ∈ (D.I_b r1).filter (H.Adj z0))
    (hq_ne_t1 : q ≠ t1) (hI1_pair : D.I_b r1 = {q, t1})
    (hI1p_comp2 : ∀ q' ∈ (D.I_b r1).filter (fun z => ¬ H.Adj z0 z), ∀ y ∈ D.I_b r2, H.Adj q' y)
    (hI1p_na3 : ∀ q' ∈ (D.I_b r1).filter (fun z => ¬ H.Adj z0 z), ∀ z' ∈ D.I_b r3, ¬ H.Adj q' z')
    (hI2_comp3 : ∀ y ∈ D.I_b r2, ∀ z' ∈ D.I_b r3, H.Adj y z')
    (hT1_na2 : ∀ t1' ∈ (D.I_b r1).filter (H.Adj z0), ∀ y ∈ D.I_b r2, ¬ H.Adj t1' y)
    (hI2_sp : ¬ ∃ q2 ∈ D.A_b r2 ∪ D.U_b r2, ∃ y0 ∈ D.I_b r2, ∃ y1 ∈ D.I_b r2, H.Adj q2 y0 ∧ ¬ H.Adj q2 y1) :
    ∃ (i : ℕ) (dy de : Bool), IsVegaGraph H i dy de := by
  have hq_I1 : q ∈ D.I_b r1 := (Finset.mem_filter.mp hq_in).1
  have ht1_I1 : t1 ∈ D.I_b r1 := (Finset.mem_filter.mp ht1_in).1
  have hA2U2 : D.A_b r2 = {D.a_b r2} ∧ D.U_b r2 = {D.u_b r2} := by
    apply D.hcl12_b r2; intro q2 hq2 y1 hy1 y2 hy2; by_contra hdiff
    by_cases h1 : H.Adj q2 y1
    · exact hI2_sp ⟨q2, hq2, y1, hy1, y2, hy2, h1, fun h2 => hdiff (iff_of_true h1 h2)⟩
    · exact hI2_sp ⟨q2, hq2, y2, hy2, y1, hy1, by_contra (fun h2 => hdiff (iff_of_false h1 h2)), h1⟩
  obtain ⟨hA2_eq, hU2_eq⟩ := hA2U2
  obtain ⟨y0, hy0⟩ := D.hIb_ne r2
  have hI2_eq : D.I_b r2 = {y0} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hy0, fun y' hy' => by
    apply G.hTwin y' y0; intro z
    rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
    · exact ⟨fun h => (D.hY_na_I r2 z hY y' hy' h.symm).elim, fun h => (D.hY_na_I r2 z hY y0 hy0 h.symm).elim⟩
    · exact ⟨fun h => (D.hAb_na_I r1 r2 h12 z hA1 y' hy' h.symm).elim, fun h => (D.hAb_na_I r1 r2 h12 z hA1 y0 hy0 h.symm).elim⟩
    · rw [hA2_eq, Finset.mem_singleton] at hA2; subst hA2
      exact ⟨fun _ => (D.hcomp_aIuI r2 y0 hy0).1.symm, fun _ => (D.hcomp_aIuI r2 y' hy').1.symm⟩
    · exact ⟨fun h => (D.hAb_na_I r3 r2 h23.symm z hA3 y' hy' h.symm).elim, fun h => (D.hAb_na_I r3 r2 h23.symm z hA3 y0 hy0 h.symm).elim⟩
    · exact ⟨fun h => (D.hx_na_I r2 y' hy' h.symm).elim, fun h => (D.hx_na_I r2 y0 hy0 h.symm).elim⟩
    · exact ⟨fun h => (D.hUb_na_I r1 r2 h12 z hU1 y' hy' h.symm).elim, fun h => (D.hUb_na_I r1 r2 h12 z hU1 y0 hy0 h.symm).elim⟩
    · rw [hU2_eq, Finset.mem_singleton] at hU2; subst hU2
      exact ⟨fun _ => (D.hcomp_aIuI r2 y0 hy0).2.symm, fun _ => (D.hcomp_aIuI r2 y' hy').2.symm⟩
    · exact ⟨fun h => (D.hUb_na_I r3 r2 h23.symm z hU3 y' hy' h.symm).elim, fun h => (D.hUb_na_I r3 r2 h23.symm z hU3 y0 hy0 h.symm).elim⟩
    · rw [hI1_pair, Finset.mem_insert, Finset.mem_singleton] at hI1
      rcases hI1 with rfl | rfl
      · exact ⟨fun _ => (hI1p_comp2 z hq_in y0 hy0).symm, fun _ => (hI1p_comp2 z hq_in y' hy').symm⟩
      · exact ⟨fun h => (hT1_na2 z ht1_in y' hy' h.symm).elim, fun h => (hT1_na2 z ht1_in y0 hy0 h.symm).elim⟩
    · exact ⟨fun h => (D.hIb_ind r2 y' hy' z hI2 h).elim, fun h => (D.hIb_ind r2 y0 hy0 z hI2 h).elim⟩
    · exact ⟨fun _ => hI2_comp3 y0 hy0 z hI3, fun _ => hI2_comp3 y' hy' z hI3⟩⟩
  let af_n : Fin 3 → U := ![D.a_b r1, D.u_b r1, y0]
  let uf_n : Fin 3 → U := ![D.a_b r2, D.u_b r2, t1]
  let J_n : Fin 3 → Finset U := ![insert D.x (D.U_b r3), D.Y_set ∪ D.A_b r3, D.I_b r3]
  have ha1 := D.ha_mem r1; have ha2 := D.ha_mem r2; have hu1 := D.hu_mem r1; have hu2 := D.hu_mem r2
  have ha1_na_u1 : ¬ H.Adj (D.a_b r1) (D.u_b r1) := fun h => tf_contra G.hTF h (D.hcomp_aIuI r1 q hq_I1).2 (D.hcomp_aIuI r1 q hq_I1).1
  have ha2_na_u2 : ¬ H.Adj (D.a_b r2) (D.u_b r2) := fun h => tf_contra G.hTF h (D.hcomp_aIuI r2 y0 hy0).2 (D.hcomp_aIuI r2 y0 hy0).1
  have hJ_n_subR : ∀ z ∈ insert D.x (D.U_b r3), z ∈ D.R_set := fun z hz => by
    rcases Finset.mem_insert.mp hz with rfl | hzU
    · exact D.hx_R
    · exact D.hUb_sub r3 hzU
  have hJ_n_subN : ∀ z ∈ D.Y_set ∪ D.A_b r3, z ∈ D.Nx := fun z hz => by
    rcases Finset.mem_union.mp hz with hY | hA
    · exact D.hY_sub hY
    · exact D.hAb_sub r3 hA
  let qMap8 : Fin 8 → Option U := fun p =>
    match p.val with
    | 0 => some q | 1 => none | 2 => some (af_n 0) | 3 => some (af_n 1) | 4 => some (af_n 2)
    | 5 => some (uf_n 0) | 6 => some (uf_n 1) | _ => some (uf_n 2)
  have htag8 : ∀ (p : Fin 8) (up : U), qMap8 p = some up →
      (if up = q then 0 else if up ∈ D.A_b r1 then 2 else if up ∈ D.U_b r1 then 3 else if up = y0 then 4
       else if up ∈ D.A_b r2 then 5 else if up ∈ D.U_b r2 then 6 else 7) = p.val := by
    intro p up hp
    rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp [qMap8, af_n, uf_n] at hp
    · injection hp with h; subst h; simp
    · simp at hp
    · injection hp with h; subst h
      rw [if_neg (fun hm : D.a_b r1 = q => (D.hIb_out r1 q hq_I1).1 (hm ▸ D.hAb_sub r1 ha1)), if_pos ha1]; rfl
    · injection hp with h; subst h
      rw [if_neg (fun hm : D.u_b r1 = q => (D.hIb_out r1 q hq_I1).2 (hm ▸ D.hUb_sub r1 hu1)),
          if_neg (fun hm => D.hdisj_NR' _ (D.hAb_sub r1 hm) _ (D.hUb_sub r1 hu1) rfl), if_pos hu1]; rfl
    · injection hp with h; subst h
      rw [if_neg (fun hm : y0 = q => Finset.disjoint_left.mp (D.hIb_disj r1 r2 h12) hq_I1 (hm ▸ hy0)),
          if_neg (fun hm => (D.hIb_out r2 y0 hy0).1 (D.hAb_sub r1 hm)),
          if_neg (fun hm => (D.hIb_out r2 y0 hy0).2 (D.hUb_sub r1 hm)), if_pos rfl]; rfl
    · injection hp with h; subst h
      rw [if_neg (fun hm : D.a_b r2 = q => (D.hIb_out r1 q hq_I1).1 (hm ▸ D.hAb_sub r2 ha2)),
          if_neg (fun hm => Finset.disjoint_left.mp (D.hAb_disj r1 r2 h12) hm ha2),
          if_neg (fun hm => D.hdisj_NR' _ (D.hAb_sub r2 ha2) _ (D.hUb_sub r1 hm) rfl),
          if_neg (fun hm : D.a_b r2 = y0 => (D.hIb_out r2 y0 hy0).1 (hm ▸ D.hAb_sub r2 ha2)), if_pos ha2]; rfl
    · injection hp with h; subst h
      rw [if_neg (fun hm : D.u_b r2 = q => (D.hIb_out r1 q hq_I1).2 (hm ▸ D.hUb_sub r2 hu2)),
          if_neg (fun hm => D.hdisj_NR' _ (D.hAb_sub r1 hm) _ (D.hUb_sub r2 hu2) rfl),
          if_neg (fun hm => Finset.disjoint_left.mp (D.hUb_disj r1 r2 h12) hm hu2),
          if_neg (fun hm : D.u_b r2 = y0 => (D.hIb_out r2 y0 hy0).2 (hm ▸ D.hUb_sub r2 hu2)),
          if_neg (fun hm => D.hdisj_NR' _ (D.hAb_sub r2 hm) _ (D.hUb_sub r2 hu2) rfl), if_pos hu2]; rfl
    · injection hp with h; subst h
      rw [if_neg hq_ne_t1.symm,
          if_neg (fun hm => (D.hIb_out r1 t1 ht1_I1).1 (D.hAb_sub r1 hm)),
          if_neg (fun hm => (D.hIb_out r1 t1 ht1_I1).2 (D.hUb_sub r1 hm)),
          if_neg (fun hm : t1 = y0 => Finset.disjoint_left.mp (D.hIb_disj r1 r2 h12) ht1_I1 (hm ▸ hy0)),
          if_neg (fun hm => (D.hIb_out r1 t1 ht1_I1).1 (D.hAb_sub r2 hm)),
          if_neg (fun hm => (D.hIb_out r1 t1 ht1_I1).2 (D.hUb_sub r2 hm))]; rfl
  refine vega_of_singleton_frame H G.hTF G.hMax G.hTwin D.hnn D.hsum D.hdeg q none af_n uf_n J_n ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r; rcases fin3_cases r with rfl | rfl | rfl
    · exact ⟨D.x, Finset.mem_insert_self D.x _⟩
    · exact ⟨D.a_b r3, Finset.mem_union_right _ (D.ha_mem r3)⟩
    · exact D.hIb_ne r3
  · intro r z1 hz1 z2 hz2; rcases fin3_cases r with rfl | rfl | rfl
    · exact D.hR_ind z1 (hJ_n_subR z1 hz1) z2 (hJ_n_subR z2 hz2)
    · exact D.hNx_ind z1 (hJ_n_subN z1 hz1) z2 (hJ_n_subN z2 hz2)
    · exact D.hIb_ind r3 z1 hz1 z2 hz2
  · intro s1 s2 hne; rcases fin3_cases s1 with rfl | rfl | rfl <;> rcases fin3_cases s2 with rfl | rfl | rfl
    all_goals first | exact absurd rfl hne
                    | exact Finset.disjoint_left.mpr (fun z h1 h2 => D.hdisj_NR' z (hJ_n_subN z h2) z (hJ_n_subR z h1) rfl)
                    | exact Finset.disjoint_left.mpr (fun z h1 h2 => D.hdisj_NR' z (hJ_n_subN z h1) z (hJ_n_subR z h2) rfl)
                    | exact Finset.disjoint_left.mpr (fun z h1 h2 => (D.hIb_out r3 z h2).2 (hJ_n_subR z h1))
                    | exact Finset.disjoint_left.mpr (fun z h1 h2 => (D.hIb_out r3 z h1).2 (hJ_n_subR z h2))
                    | exact Finset.disjoint_left.mpr (fun z h1 h2 => (D.hIb_out r3 z h2).1 (hJ_n_subN z h1))
                    | exact Finset.disjoint_left.mpr (fun z h1 h2 => (D.hIb_out r3 z h1).1 (hJ_n_subN z h2))
  · intro p1 p2 u1 u2 hp1 hp2 heq; subst heq
    exact Fin.ext ((htag8 p1 u1 hp1).symm.trans (htag8 p2 u1 hp2))
  · intro p up hp r hr
    rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin3_cases r with rfl | rfl | rfl <;> dsimp [af_n, uf_n, J_n] at hp hr
    all_goals simp at hp
    all_goals subst hp
    · exact (D.hIb_out r1 _ hq_I1).2 (hJ_n_subR _ hr)
    · exact (D.hIb_out r1 _ hq_I1).1 (hJ_n_subN _ hr)
    · exact Finset.disjoint_left.mp (D.hIb_disj r1 r3 h13) hq_I1 hr
    · exact D.hdisj_NR' _ (D.hAb_sub r1 ha1) _ (hJ_n_subR _ hr) rfl
    · rcases Finset.mem_union.mp hr with hY | hA3
      · exact Finset.disjoint_left.mp (D.hY_disj_A r1) hY ha1
      · exact Finset.disjoint_left.mp (D.hAb_disj r1 r3 h13) ha1 hA3
    · exact (D.hIb_out r3 _ hr).1 (D.hAb_sub r1 ha1)
    · rcases Finset.mem_insert.mp hr with hEq | hU3
      · exact D.hx_ne_U r1 _ hu1 hEq.symm
      · exact Finset.disjoint_left.mp (D.hUb_disj r1 r3 h13) hu1 hU3
    · exact D.hdisj_NR' _ (hJ_n_subN _ hr) _ (D.hUb_sub r1 hu1) rfl
    · exact (D.hIb_out r3 _ hr).2 (D.hUb_sub r1 hu1)
    · exact (D.hIb_out r2 _ hy0).2 (hJ_n_subR _ hr)
    · exact (D.hIb_out r2 _ hy0).1 (hJ_n_subN _ hr)
    · exact Finset.disjoint_left.mp (D.hIb_disj r2 r3 h23) hy0 hr
    · exact D.hdisj_NR' _ (D.hAb_sub r2 ha2) _ (hJ_n_subR _ hr) rfl
    · rcases Finset.mem_union.mp hr with hY | hA3
      · exact Finset.disjoint_left.mp (D.hY_disj_A r2) hY ha2
      · exact Finset.disjoint_left.mp (D.hAb_disj r2 r3 h23) ha2 hA3
    · exact (D.hIb_out r3 _ hr).1 (D.hAb_sub r2 ha2)
    · rcases Finset.mem_insert.mp hr with hEq | hU3
      · exact D.hx_ne_U r2 _ hu2 hEq.symm
      · exact Finset.disjoint_left.mp (D.hUb_disj r2 r3 h23) hu2 hU3
    · exact D.hdisj_NR' _ (hJ_n_subN _ hr) _ (D.hUb_sub r2 hu2) rfl
    · exact (D.hIb_out r3 _ hr).2 (D.hUb_sub r2 hu2)
    · exact (D.hIb_out r1 _ ht1_I1).2 (hJ_n_subR _ hr)
    · exact (D.hIb_out r1 _ ht1_I1).1 (hJ_n_subN _ hr)
    · exact Finset.disjoint_left.mp (D.hIb_disj r1 r3 h13) ht1_I1 hr
  · intro z
    rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
    · exact Or.inr ⟨1, Finset.mem_union_left _ hY⟩
    · rw [hA1_eq, Finset.mem_singleton] at hA1; subst hA1; exact Or.inl ⟨2, rfl⟩
    · rw [hA2_eq, Finset.mem_singleton] at hA2; subst hA2; exact Or.inl ⟨5, rfl⟩
    · exact Or.inr ⟨1, Finset.mem_union_right _ hA3⟩
    · exact Or.inr ⟨0, Finset.mem_insert_self D.x _⟩
    · rw [hU1_eq, Finset.mem_singleton] at hU1; subst hU1; exact Or.inl ⟨3, rfl⟩
    · rw [hU2_eq, Finset.mem_singleton] at hU2; subst hU2; exact Or.inl ⟨6, rfl⟩
    · exact Or.inr ⟨0, Finset.mem_insert_of_mem hU3⟩
    · rw [hI1_pair, Finset.mem_insert, Finset.mem_singleton] at hI1
      rcases hI1 with rfl | rfl
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inl ⟨7, rfl⟩
    · rw [hI2_eq, Finset.mem_singleton] at hI2; subst hI2; exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨2, hI3⟩
  · intro p1 p2 u1 u2 hp1 hp2
    have hqa1 := (D.hcomp_aIuI r1 q hq_I1).1; have hqu1 := (D.hcomp_aIuI r1 q hq_I1).2
    have ht1a1 := (D.hcomp_aIuI r1 t1 ht1_I1).1; have ht1u1 := (D.hcomp_aIuI r1 t1 ht1_I1).2
    have hy0a2 := (D.hcomp_aIuI r2 y0 hy0).1; have hy0u2 := (D.hcomp_aIuI r2 y0 hy0).2
    have hqy0 := hI1p_comp2 q hq_in y0 hy0
    have ha1u2 := D.hAb_comp_U r1 r2 h12 _ ha1 _ hu2; have ha2u1 := D.hAb_comp_U r2 r1 h12.symm _ ha2 _ hu1
    have hqt1 := D.hIb_ind r1 q hq_I1 t1 ht1_I1
    have ha1a2 := D.hNx_ind _ (D.hAb_sub r1 ha1) _ (D.hAb_sub r2 ha2)
    have hu1u2 := D.hR_ind _ (D.hUb_sub r1 hu1) _ (D.hUb_sub r2 hu2)
    have ht1y0 := hT1_na2 t1 ht1_in y0 hy0
    have ha1y0 := D.hAb_na_I r1 r2 h12 _ ha1 y0 hy0; have hu1y0 := D.hUb_na_I r1 r2 h12 _ hu1 y0 hy0
    have ha2q := D.hAb_na_I r2 r1 h12.symm _ ha2 q hq_I1; have ha2t1 := D.hAb_na_I r2 r1 h12.symm _ ha2 t1 ht1_I1
    have hu2q := D.hUb_na_I r2 r1 h12.symm _ hu2 q hq_I1; have hu2t1 := D.hUb_na_I r2 r1 h12.symm _ hu2 t1 ht1_I1
    rcases fin8_cases p1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin8_cases p2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp [af_n, uf_n] at hp1 hp2
    all_goals simp at hp1 hp2
    all_goals subst hp1; subst hp2; dsimp only [vegaAdj]
    · exact iff_of_false (H.loopless.irrefl _) (by decide)
    · exact iff_of_true hqa1.symm (by decide)
    · exact iff_of_true hqu1.symm (by decide)
    · exact iff_of_true hqy0 (by decide)
    · exact iff_of_false (fun h => ha2q h.symm) (by decide)
    · exact iff_of_false (fun h => hu2q h.symm) (by decide)
    · exact iff_of_false hqt1 (by decide)
    · exact iff_of_true hqa1 (by decide)
    · exact iff_of_false (H.loopless.irrefl _) (by decide)
    · exact iff_of_false ha1_na_u1 (by decide)
    · exact iff_of_false ha1y0 (by decide)
    · exact iff_of_false ha1a2 (by decide)
    · exact iff_of_true ha1u2 (by decide)
    · exact iff_of_true ht1a1 (by decide)
    · exact iff_of_true hqu1 (by decide)
    · exact iff_of_false (fun h => ha1_na_u1 h.symm) (by decide)
    · exact iff_of_false (H.loopless.irrefl _) (by decide)
    · exact iff_of_false hu1y0 (by decide)
    · exact iff_of_true ha2u1.symm (by decide)
    · exact iff_of_false hu1u2 (by decide)
    · exact iff_of_true ht1u1 (by decide)
    · exact iff_of_true hqy0.symm (by decide)
    · exact iff_of_false (fun h => ha1y0 h.symm) (by decide)
    · exact iff_of_false (fun h => hu1y0 h.symm) (by decide)
    · exact iff_of_false (H.loopless.irrefl _) (by decide)
    · exact iff_of_true hy0a2.symm (by decide)
    · exact iff_of_true hy0u2.symm (by decide)
    · exact iff_of_false (fun h => ht1y0 h.symm) (by decide)
    · exact iff_of_false ha2q (by decide)
    · exact iff_of_false (fun h => ha1a2 h.symm) (by decide)
    · exact iff_of_true ha2u1 (by decide)
    · exact iff_of_true hy0a2 (by decide)
    · exact iff_of_false (H.loopless.irrefl _) (by decide)
    · exact iff_of_false ha2_na_u2 (by decide)
    · exact iff_of_false ha2t1 (by decide)
    · exact iff_of_false hu2q (by decide)
    · exact iff_of_true ha1u2.symm (by decide)
    · exact iff_of_false (fun h => hu1u2 h.symm) (by decide)
    · exact iff_of_true hy0u2 (by decide)
    · exact iff_of_false (fun h => ha2_na_u2 h.symm) (by decide)
    · exact iff_of_false (H.loopless.irrefl _) (by decide)
    · exact iff_of_false hu2t1 (by decide)
    · exact iff_of_false (fun h => hqt1 h.symm) (by decide)
    · exact iff_of_true ht1a1.symm (by decide)
    · exact iff_of_true ht1u1.symm (by decide)
    · exact iff_of_false ht1y0 (by decide)
    · exact iff_of_false (fun h => ha2t1 h.symm) (by decide)
    · exact iff_of_false (fun h => hu2t1 h.symm) (by decide)
    · exact iff_of_false (H.loopless.irrefl _) (by decide)
  · intro p up hp r z hz
    rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin3_cases r with rfl | rfl | rfl <;> dsimp [af_n, uf_n, J_n] at hp hz ⊢
    all_goals simp at hp
    all_goals subst hp
    · exact iff_of_false (by rcases Finset.mem_insert.mp hz with rfl | hzU; exact fun h => D.hx_na_I r1 q hq_I1 h.symm; exact fun h => D.hUb_na_I r3 r1 h13.symm z hzU q hq_I1 h.symm) (by decide)
    · exact iff_of_false (by rcases Finset.mem_union.mp hz with hY | hA3; exact fun h => D.hY_na_I r1 z hY q hq_I1 h.symm; exact fun h => D.hAb_na_I r3 r1 h13.symm z hA3 q hq_I1 h.symm) (by decide)
    · exact iff_of_false (hI1p_na3 q hq_in z hz) (by decide)
    · exact iff_of_true (by rcases Finset.mem_insert.mp hz with rfl | hzU; exact (Finset.mem_filter.mp (D.hNx_eq ▸ D.hAb_sub r1 ha1)).2.symm; exact D.hAb_comp_U r1 r3 h13 _ ha1 z hzU) (by decide)
    · exact iff_of_false (D.hNx_ind _ (D.hAb_sub r1 ha1) z (hJ_n_subN z hz)) (by decide)
    · exact iff_of_false (D.hAb_na_I r1 r3 h13 _ ha1 z hz) (by decide)
    · exact iff_of_false (D.hR_ind _ (D.hUb_sub r1 hu1) z (hJ_n_subR z hz)) (by decide)
    · exact iff_of_true (by rcases Finset.mem_union.mp hz with hY | hA3; exact ((D.hY_nbhd z hY (D.u_b r1)).mpr (D.hUb_sub r1 hu1)).symm; exact (D.hAb_comp_U r3 r1 h13.symm z hA3 _ hu1).symm) (by decide)
    · exact iff_of_false (D.hUb_na_I r1 r3 h13 _ hu1 z hz) (by decide)
    · exact iff_of_false (by rcases Finset.mem_insert.mp hz with rfl | hzU; exact fun h => D.hx_na_I r2 y0 hy0 h.symm; exact fun h => D.hUb_na_I r3 r2 h23.symm z hzU y0 hy0 h.symm) (by decide)
    · exact iff_of_false (by rcases Finset.mem_union.mp hz with hY | hA3; exact fun h => D.hY_na_I r2 z hY y0 hy0 h.symm; exact fun h => D.hAb_na_I r3 r2 h23.symm z hA3 y0 hy0 h.symm) (by decide)
    · exact iff_of_true (hI2_comp3 y0 hy0 z hz) (by decide)
    · exact iff_of_true (by rcases Finset.mem_insert.mp hz with rfl | hzU; exact (Finset.mem_filter.mp (D.hNx_eq ▸ D.hAb_sub r2 ha2)).2.symm; exact D.hAb_comp_U r2 r3 h23 _ ha2 z hzU) (by decide)
    · exact iff_of_false (D.hNx_ind _ (D.hAb_sub r2 ha2) z (hJ_n_subN z hz)) (by decide)
    · exact iff_of_false (D.hAb_na_I r2 r3 h23 _ ha2 z hz) (by decide)
    · exact iff_of_false (D.hR_ind _ (D.hUb_sub r2 hu2) z (hJ_n_subR z hz)) (by decide)
    · exact iff_of_true (by rcases Finset.mem_union.mp hz with hY | hA3; exact ((D.hY_nbhd z hY (D.u_b r2)).mpr (D.hUb_sub r2 hu2)).symm; exact (D.hAb_comp_U r3 r2 h23.symm z hA3 _ hu2).symm) (by decide)
    · exact iff_of_false (D.hUb_na_I r2 r3 h23 _ hu2 z hz) (by decide)
    · exact iff_of_false (by rcases Finset.mem_insert.mp hz with rfl | hzU; exact fun h => D.hx_na_I r1 t1 ht1_I1 h.symm; exact fun h => D.hUb_na_I r3 r1 h13.symm z hzU t1 ht1_I1 h.symm) (by decide)
    · exact iff_of_false (by rcases Finset.mem_union.mp hz with hY | hA3; exact fun h => D.hY_na_I r1 z hY t1 ht1_I1 h.symm; exact fun h => D.hAb_na_I r3 r1 h13.symm z hA3 t1 ht1_I1 h.symm) (by decide)
    · exact iff_of_true ((h3unif z0 hz0 z hz t1 (Finset.mem_union_left _ ht1_I1)).mp (Finset.mem_filter.mp ht1_in).2).symm (by decide)

/-- Claim 13 master dispatcher from `RegDecomp`: handles both the singleton case and any splitting part! -/
lemma regular_decomp_is_vega {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (G : IsGood H) (ω : U → ℝ) (δ : ℝ)
    (D : RegDecomp H G ω δ) :
    ∃ (i : ℕ) (dy de : Bool), IsVegaGraph H i dy de := by
  have hhandle_I1p : ∀ (r1 r2 r3 : Fin 3) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
      (p3 w3 z0 z1 : U), p3 ∈ D.A_b r3 → w3 ∈ D.U_b r3 → z0 ∈ D.I_b r3 → z1 ∈ D.I_b r3 →
      H.Adj p3 w3 → H.Adj p3 z0 → ¬ H.Adj p3 z1 → H.Adj w3 z1 → ¬ H.Adj w3 z0 →
      (∀ zA ∈ D.I_b r3, ∀ zB ∈ D.I_b r3, ∀ t ∈ D.I_b r1 ∪ D.I_b r2, H.Adj zA t ↔ H.Adj zB t) →
      ((D.I_b r1).filter (fun z => ¬ H.Adj z0 z)).Nonempty →
      ∃ (i : ℕ) (dy de : Bool), IsVegaGraph H i dy de := by
    intro r1 r2 r3 h12 h13 h23 p3 w3 z0 z1 hp3 hw3 hz0 hz1 hp3w3 hp3z0 hnp3z1 hw3z1 _ h3unif hI1p_ne
    let T1 := (D.I_b r1).filter (H.Adj z0)
    let T2 := (D.I_b r2).filter (H.Adj z0)
    let I1p := (D.I_b r1).filter (fun z => ¬ H.Adj z0 z)
    let I2p := (D.I_b r2).filter (fun z => ¬ H.Adj z0 z)
    have hT1_ne : T1.Nonempty := by
      obtain ⟨t1, ht1, z', hz', hadj⟩ := D.he_b r1 r3 h13
      exact ⟨t1, Finset.mem_filter.mpr ⟨ht1, (h3unif z' hz' z0 hz0 t1 (Finset.mem_union_left _ ht1)).mp hadj.symm⟩⟩
    have hT2_ne : T2.Nonempty := by
      obtain ⟨t2, ht2, z', hz', hadj⟩ := D.he_b r2 r3 h23
      exact ⟨t2, Finset.mem_filter.mpr ⟨ht2, (h3unif z' hz' z0 hz0 t2 (Finset.mem_union_right _ ht2)).mp hadj.symm⟩⟩
    have hA1U1 : D.A_b r1 = {D.a_b r1} ∧ D.U_b r1 = {D.u_b r1} := by
      apply D.hcl12_b r1; intro q hq x1 hx1 x2 hx2; by_contra hdiff
      have hsp1 : ∃ q' ∈ D.A_b r1 ∪ D.U_b r1, ∃ uA ∈ D.I_b r1, ∃ uB ∈ D.I_b r1, H.Adj q' uA ∧ ¬ H.Adj q' uB := by
        by_cases h1 : H.Adj q x1
        · exact ⟨q, hq, x1, hx1, x2, hx2, h1, fun h2 => hdiff (iff_of_true h1 h2)⟩
        · exact ⟨q, hq, x2, hx2, x1, hx1, by_contra (fun h2 => hdiff (iff_of_false h1 h2)), h1⟩
      have h1unif := (D.hsplit_b r2 r3 r1 h23 h12.symm h13.symm hsp1).2
      obtain ⟨t1, ht1⟩ := hT1_ne; obtain ⟨q1, hq1⟩ := hI1p_ne
      exact (Finset.mem_filter.mp hq1).2 ((h1unif t1 (Finset.mem_filter.mp ht1).1 q1 (Finset.mem_filter.mp hq1).1 z0 (Finset.mem_union_right _ hz0)).mp (Finset.mem_filter.mp ht1).2.symm).symm
    obtain ⟨hA1_eq, hU1_eq⟩ := hA1U1
    have hI1p_comp2 : ∀ q ∈ I1p, ∀ y ∈ D.I_b r2, H.Adj q y := by
      intro q hq y hy; by_contra hna
      have hq1 := (Finset.mem_filter.mp hq).1
      have hqy_ne : q ≠ y := fun h => Finset.disjoint_left.mp (D.hIb_disj r1 r2 h12) hq1 (h ▸ hy)
      obtain ⟨z', hqz', hyz'⟩ := G.hMax q y hqy_ne hna
      have hz'3 : z' ∈ D.I_b r3 := D.hcom_II r1 r2 r3 h12 h13 h23 q hq1 y hy z' hqz' hyz'
      exact (Finset.mem_filter.mp hq).2 ((h3unif z' hz'3 z0 hz0 q (Finset.mem_union_left _ hq1)).mp hqz'.symm)
    have hI1p_na3 : ∀ q ∈ I1p, ∀ z' ∈ D.I_b r3, ¬ H.Adj q z' := fun q hq z' hz' h =>
      (Finset.mem_filter.mp hq).2 ((h3unif z' hz' z0 hz0 q (Finset.mem_union_left _ (Finset.mem_filter.mp hq).1)).mp h.symm)
    obtain ⟨q, hq_in⟩ := hI1p_ne
    have hq_I1 : q ∈ D.I_b r1 := (Finset.mem_filter.mp hq_in).1
    have hI1p_eq : I1p = {q} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hq_in, fun q' hq' => by
      apply G.hTwin q' q; intro z; have hq'1 := (Finset.mem_filter.mp hq').1
      rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
      · exact ⟨fun h => (D.hY_na_I r1 z hY q' hq'1 h.symm).elim, fun h => (D.hY_na_I r1 z hY q hq_I1 h.symm).elim⟩
      · rw [hA1_eq, Finset.mem_singleton] at hA1; subst hA1
        exact ⟨fun _ => (D.hcomp_aIuI r1 q hq_I1).1.symm, fun _ => (D.hcomp_aIuI r1 q' hq'1).1.symm⟩
      · exact ⟨fun h => (D.hAb_na_I r2 r1 h12.symm z hA2 q' hq'1 h.symm).elim, fun h => (D.hAb_na_I r2 r1 h12.symm z hA2 q hq_I1 h.symm).elim⟩
      · exact ⟨fun h => (D.hAb_na_I r3 r1 h13.symm z hA3 q' hq'1 h.symm).elim, fun h => (D.hAb_na_I r3 r1 h13.symm z hA3 q hq_I1 h.symm).elim⟩
      · exact ⟨fun h => (D.hx_na_I r1 q' hq'1 h.symm).elim, fun h => (D.hx_na_I r1 q hq_I1 h.symm).elim⟩
      · rw [hU1_eq, Finset.mem_singleton] at hU1; subst hU1
        exact ⟨fun _ => (D.hcomp_aIuI r1 q hq_I1).2.symm, fun _ => (D.hcomp_aIuI r1 q' hq'1).2.symm⟩
      · exact ⟨fun h => (D.hUb_na_I r2 r1 h12.symm z hU2 q' hq'1 h.symm).elim, fun h => (D.hUb_na_I r2 r1 h12.symm z hU2 q hq_I1 h.symm).elim⟩
      · exact ⟨fun h => (D.hUb_na_I r3 r1 h13.symm z hU3 q' hq'1 h.symm).elim, fun h => (D.hUb_na_I r3 r1 h13.symm z hU3 q hq_I1 h.symm).elim⟩
      · exact ⟨fun h => (D.hIb_ind r1 q' hq'1 z hI1 h).elim, fun h => (D.hIb_ind r1 q hq_I1 z hI1 h).elim⟩
      · exact ⟨fun _ => hI1p_comp2 q hq_in z hI2, fun _ => hI1p_comp2 q' hq' z hI2⟩
      · exact ⟨fun h => (hI1p_na3 q' hq' z hI3 h).elim, fun h => (hI1p_na3 q hq_in z hI3 h).elim⟩⟩
    by_cases hI2p_ne : I2p.Nonempty
    · exact (regular_subcase3a H G ω δ D r1 r2 r3 h12 h13 h23 p3 z0 z1 q hp3 hz0 hz1 hnp3z1
        h3unif hA1_eq hU1_eq hT1_ne hT2_ne hq_in hI1p_eq hI1p_comp2 hI1p_na3 hI2p_ne).elim
    · have hI2_comp3 : ∀ y ∈ D.I_b r2, ∀ z' ∈ D.I_b r3, H.Adj y z' := fun y hy z' hz' => by
        have hyT2 : H.Adj z0 y := by_contra fun hna => hI2p_ne ⟨y, Finset.mem_filter.mpr ⟨hy, hna⟩⟩
        exact ((h3unif z0 hz0 z' hz' y (Finset.mem_union_right _ hy)).mp hyT2).symm
      have hT1_na2 : ∀ t1 ∈ T1, ∀ y ∈ D.I_b r2, ¬ H.Adj t1 y := fun t1 ht1 y hy h =>
        tf_contra G.hTF (Finset.mem_filter.mp ht1).2 h (hI2_comp3 y hy z0 hz0).symm
      obtain ⟨t1, ht1_in⟩ := hT1_ne
      have ht1_I1 : t1 ∈ D.I_b r1 := (Finset.mem_filter.mp ht1_in).1
      have hT1_eq : T1 = {t1} := Finset.eq_singleton_iff_unique_mem.mpr ⟨ht1_in, fun t' ht' => by
        apply G.hTwin t' t1; intro z; have ht'1 := (Finset.mem_filter.mp ht').1
        rcases D.hpart_b r1 r2 r3 h12 h13 h23 z with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
        · exact ⟨fun h => (D.hY_na_I r1 z hY t' ht'1 h.symm).elim, fun h => (D.hY_na_I r1 z hY t1 ht1_I1 h.symm).elim⟩
        · rw [hA1_eq, Finset.mem_singleton] at hA1; subst hA1
          exact ⟨fun _ => (D.hcomp_aIuI r1 t1 ht1_I1).1.symm, fun _ => (D.hcomp_aIuI r1 t' ht'1).1.symm⟩
        · exact ⟨fun h => (D.hAb_na_I r2 r1 h12.symm z hA2 t' ht'1 h.symm).elim, fun h => (D.hAb_na_I r2 r1 h12.symm z hA2 t1 ht1_I1 h.symm).elim⟩
        · exact ⟨fun h => (D.hAb_na_I r3 r1 h13.symm z hA3 t' ht'1 h.symm).elim, fun h => (D.hAb_na_I r3 r1 h13.symm z hA3 t1 ht1_I1 h.symm).elim⟩
        · exact ⟨fun h => (D.hx_na_I r1 t' ht'1 h.symm).elim, fun h => (D.hx_na_I r1 t1 ht1_I1 h.symm).elim⟩
        · rw [hU1_eq, Finset.mem_singleton] at hU1; subst hU1
          exact ⟨fun _ => (D.hcomp_aIuI r1 t1 ht1_I1).2.symm, fun _ => (D.hcomp_aIuI r1 t' ht'1).2.symm⟩
        · exact ⟨fun h => (D.hUb_na_I r2 r1 h12.symm z hU2 t' ht'1 h.symm).elim, fun h => (D.hUb_na_I r2 r1 h12.symm z hU2 t1 ht1_I1 h.symm).elim⟩
        · exact ⟨fun h => (D.hUb_na_I r3 r1 h13.symm z hU3 t' ht'1 h.symm).elim, fun h => (D.hUb_na_I r3 r1 h13.symm z hU3 t1 ht1_I1 h.symm).elim⟩
        · exact ⟨fun h => (D.hIb_ind r1 t' ht'1 z hI1 h).elim, fun h => (D.hIb_ind r1 t1 ht1_I1 z hI1 h).elim⟩
        · exact ⟨fun h => (hT1_na2 t' ht' z hI2 h).elim, fun h => (hT1_na2 t1 ht1_in z hI2 h).elim⟩
        · exact ⟨fun _ => ((h3unif z0 hz0 z hI3 t1 (Finset.mem_union_left _ ht1_I1)).mp (Finset.mem_filter.mp ht1_in).2).symm,
                 fun _ => ((h3unif z0 hz0 z hI3 t' (Finset.mem_union_left _ ht'1)).mp (Finset.mem_filter.mp ht').2).symm⟩⟩
      have hq_ne_t1 : q ≠ t1 := fun h => (Finset.mem_filter.mp hq_in).2 (h ▸ (Finset.mem_filter.mp ht1_in).2)
      have hI1_pair : D.I_b r1 = {q, t1} := by
        ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
        · intro hz; by_cases h : H.Adj z0 z
          · right; exact Finset.mem_singleton.mp (hT1_eq ▸ Finset.mem_filter.mpr ⟨hz, h⟩)
          · left; exact Finset.mem_singleton.mp (hI1p_eq ▸ Finset.mem_filter.mpr ⟨hz, h⟩)
        · rintro (rfl | rfl) <;> assumption
      by_cases hI2_sp : ∃ q2 ∈ D.A_b r2 ∪ D.U_b r2, ∃ y0 ∈ D.I_b r2, ∃ y1 ∈ D.I_b r2, H.Adj q2 y0 ∧ ¬ H.Adj q2 y1
      · exact (regular_subcase3b_ii H G ω δ D r1 r2 r3 h12 h13 h23 p3 w3 z0 z1 q t1
          hp3 hw3 hz0 hz1 hp3w3 hp3z0 hnp3z1 hw3z1 h3unif hq_in ht1_in hq_ne_t1 hI1p_comp2 hI2_comp3 hI2_sp).elim
      · exact regular_subcase3b_i H G ω δ D r1 r2 r3 h12 h13 h23 z0 q t1 hz0
          h3unif hA1_eq hU1_eq hq_in ht1_in hq_ne_t1 hI1_pair hI1p_comp2 hI1p_na3 hI2_comp3 hT1_na2 hI2_sp
  have hhandle_any_split : ∀ (r1 r2 r3 : Fin 3), r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
      (∃ q ∈ D.A_b r3 ∪ D.U_b r3, ∃ z0 ∈ D.I_b r3, ∃ z1 ∈ D.I_b r3, H.Adj q z0 ∧ ¬ H.Adj q z1) →
      ∃ (i : ℕ) (dy de : Bool), IsVegaGraph H i dy de := by
    intro r1 r2 r3 h12 h13 h23 hsp
    obtain ⟨⟨p3, hp3, w3, hw3, z0, hz0, z1, hz1, hp3w3, hp3z0, hnp3z1, hw3z1, hnw3z0⟩, h3unif⟩ :=
      D.hsplit_b r1 r2 r3 h12 h13 h23 hsp
    obtain ⟨e1, he1, e2, he2, he12'⟩ := D.he_b r1 r2 h12
    by_cases h1 : H.Adj z0 e1
    · have h2 : ¬ H.Adj z0 e2 := fun h => tf_contra G.hTF h1 he12' h
      exact hhandle_I1p r2 r1 r3 h12.symm h23 h13 p3 w3 z0 z1 hp3 hw3 hz0 hz1 hp3w3 hp3z0 hnp3z1 hw3z1 hnw3z0
        (fun zA hzA zB hzB t ht => h3unif zA hzA zB hzB t (Finset.mem_union.mpr (Finset.mem_union.mp ht).symm))
        ⟨e2, Finset.mem_filter.mpr ⟨he2, h2⟩⟩
    · exact hhandle_I1p r1 r2 r3 h12 h13 h23 p3 w3 z0 z1 hp3 hw3 hz0 hz1 hp3w3 hp3z0 hnp3z1 hw3z1 hnw3z0
        h3unif ⟨e1, Finset.mem_filter.mpr ⟨he1, h1⟩⟩
  by_cases hsp0 : ∃ q ∈ D.A_b 0 ∪ D.U_b 0, ∃ z0 ∈ D.I_b 0, ∃ z1 ∈ D.I_b 0, H.Adj q z0 ∧ ¬ H.Adj q z1
  · exact hhandle_any_split 1 2 0 (by decide) (by decide) (by decide) hsp0
  · by_cases hsp1 : ∃ q ∈ D.A_b 1 ∪ D.U_b 1, ∃ z0 ∈ D.I_b 1, ∃ z1 ∈ D.I_b 1, H.Adj q z0 ∧ ¬ H.Adj q z1
    · exact hhandle_any_split 0 2 1 (by decide) (by decide) (by decide) hsp1
    · by_cases hsp2 : ∃ q ∈ D.A_b 2 ∪ D.U_b 2, ∃ z0 ∈ D.I_b 2, ∃ z1 ∈ D.I_b 2, H.Adj q z0 ∧ ¬ H.Adj q z1
      · exact hhandle_any_split 0 1 2 (by decide) (by decide) (by decide) hsp2
      · have hunif : ∀ r : Fin 3, ¬ (∃ q ∈ D.A_b r ∪ D.U_b r, ∃ z0 ∈ D.I_b r, ∃ z1 ∈ D.I_b r, H.Adj q z0 ∧ ¬ H.Adj q z1) →
            D.A_b r = {D.a_b r} ∧ D.U_b r = {D.u_b r} := fun r hno => by
          apply D.hcl12_b r; intro q hq z1 hz1 z2 hz2; by_contra hdiff
          by_cases h1 : H.Adj q z1
          · exact hno ⟨q, hq, z1, hz1, z2, hz2, h1, fun h2 => hdiff (iff_of_true h1 h2)⟩
          · exact hno ⟨q, hq, z2, hz2, z1, hz1, by_contra (fun h2 => hdiff (iff_of_false h1 h2)), h1⟩
        exact regular_singleton_is_vega H G ω δ D (fun r => by
          rcases fin3_cases r with rfl | rfl | rfl
          · exact hunif 0 hsp0
          · exact hunif 1 hsp1
          · exact hunif 2 hsp2)

set_option maxHeartbeats 1500000 in
/-- **Theorem J2 (Part 1):** Every good graph admitting a strictly positive regular probability weight
    belongs to the 4-variant closed Vega class `V_i(dy, de)` for some `i ≥ 2`. -/
theorem regular_good_is_vega {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (G : IsGood H)
    (ω : U → ℝ) (δ : ℝ) (hpos : ∀ v : U, 0 < ω v) (hsum : ∑ v : U, ω v = 1)
    (hreg : ∀ u : U, wdeg H ω u = δ) (hδ : (1 / 3 : ℝ) < δ) :
    ∃ (i : ℕ) (dy de : Bool), IsVegaGraph H i dy de := by
  have hnn : ∀ v, 0 ≤ ω v := fun v => le_of_lt (hpos v)
  have hdeg : ∀ u, (1 / 3 : ℝ) < wdeg H ω u := fun u => by rw [hreg u]; exact hδ
  have hU_ne : (Finset.univ : Finset U).Nonempty := by
    by_contra hempty; rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have : ∑ v : U, ω v = 0 := by rw [← Finset.sum_empty (f := ω), ← hempty]
    linarith
  -- Frame Selection: min weight `x`, tie-broken by min unweighted degree `#(univ.filter (H.Adj x))`
  obtain ⟨x0, _, hx0_min⟩ := Finset.exists_min_image Finset.univ ω hU_ne
  let MinW := Finset.univ.filter (fun v : U => ω v = ω x0)
  have hMinW_ne : MinW.Nonempty := ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  obtain ⟨x, hx_in, hx_deg_min⟩ := Finset.exists_min_image MinW (fun v => #(Finset.univ.filter (H.Adj v))) hMinW_ne
  have hx_wmin : ∀ v : U, ω x ≤ ω v := fun v => by
    rw [(Finset.mem_filter.mp hx_in).2]; exact hx0_min v (Finset.mem_univ v)
  have hx_dmin : ∀ v : U, ω v = ω x → #(Finset.univ.filter (H.Adj x)) ≤ #(Finset.univ.filter (H.Adj v)) := fun v hv =>
    hx_deg_min v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.trans (Finset.mem_filter.mp hx_in).2⟩)
  have hcard_ge4 : 4 ≤ Fintype.card U := by
    by_contra hlt
    have hc : Fintype.card U ≤ 3 := by omega
    have hcol3 : H.Colorable 3 := by
      let e := Fintype.equivFin U
      refine ⟨SimpleGraph.Coloring.mk (fun v => Fin.castLE hc (e v)) ?_⟩
      intro u v hadj heq
      exact H.ne_of_adj hadj (e.injective (Fin.castLE_injective hc heq))
    exact G.hNot3 hcol3
  have hwx_lt_δ : ω x < δ := by
    have h4 : (4 : ℝ) * ω x ≤ ∑ v : U, ω v := calc
      (4 : ℝ) * ω x ≤ (Fintype.card U : ℝ) * ω x :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_ge4) (hnn x)
      _ = ∑ _v : U, ω x := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ v : U, ω v := Finset.sum_le_sum (fun v _ => hx_wmin v)
    linarith
  -- Claim 1: minimal `T ⊆ Nx` with `⋂_{t ∈ T} N(t) = {x}` has `#T = 3`
  let Nx := Finset.univ.filter (H.Adj x)
  have hNx_undom : ∀ v : U, v ≠ x → ∃ t ∈ Nx, ¬ H.Adj t v := by
    intro v hne; by_contra hall; push Not at hall
    have hNx_ne : Nx.Nonempty := by
      by_contra hempty; rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have h0 : wdeg H ω x = 0 := by
        rw [wdeg, ← Finset.sum_filter]; change ∑ u ∈ Nx, ω u = 0; rw [hempty, Finset.sum_empty]
      linarith [hreg x]
    have hv_na_x : ¬ H.Adj v x := by
      obtain ⟨y, hy⟩ := hNx_ne; intro hvx
      exact tf_contra G.hTF (Finset.mem_filter.mp hy).2 (hall y hy) hvx.symm
    have hex_w : ∃ w : U, H.Adj v w ∧ ¬ H.Adj x w := by
      by_contra hno; push Not at hno
      have htw : ∀ z : U, H.Adj x z ↔ H.Adj v z := fun z =>
        ⟨fun h => (hall z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).symm,
         fun h => hno z h⟩
      exact hne (G.hTwin x v htw).symm
    obtain ⟨w, hvw, hxw⟩ := hex_w
    have hwx_ne : w ≠ x := fun h => hv_na_x (h ▸ hvw)
    obtain ⟨y, hyx, hyw⟩ := G.hMax x w hwx_ne.symm hxw
    exact tf_contra G.hTF hvw hyw (hall y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyx⟩)).symm
  let Cands1 := Nx.powerset.filter (fun T => ∀ v : U, v ≠ x → ∃ t ∈ T, ¬ H.Adj t v)
  have hNx_c1 : Nx ∈ Cands1 := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Subset.refl _), hNx_undom⟩
  obtain ⟨T, hT_in, hT_min⟩ := Finset.exists_min_image Cands1 Finset.card ⟨Nx, hNx_c1⟩
  have hT_sub : T ⊆ Nx := Finset.mem_powerset.mp (Finset.mem_filter.mp hT_in).1
  have hT_undom : ∀ v : U, v ≠ x → ∃ t ∈ T, ¬ H.Adj t v := (Finset.mem_filter.mp hT_in).2
  have hT_min' : ∀ t ∈ T, ∃ v : U, v ≠ x ∧ ∀ t' ∈ T, t' ≠ t → H.Adj t' v := by
    intro t ht
    have hnot : T.erase t ∉ Cands1 := fun h => by have := hT_min _ h; have := Finset.card_erase_lt_of_mem ht; omega
    have hpow : T.erase t ∈ Nx.powerset := Finset.mem_powerset.mpr ((Finset.erase_subset t T).trans hT_sub)
    have hex : ¬ ∀ v : U, v ≠ x → ∃ t' ∈ T.erase t, ¬ H.Adj t' v := fun h => hnot (Finset.mem_filter.mpr ⟨hpow, h⟩)
    push Not at hex; obtain ⟨v, hne, hv⟩ := hex
    exact ⟨v, hne, fun t' ht' hne' => hv t' (Finset.mem_erase.mpr ⟨hne', ht'⟩)⟩
  have hT_le3 : #T ≤ 3 := card_le_three_of_minimal_inter H G.hTF G.hMax hnn hsum hdeg (· ≠ x) T hT_undom hT_min'
  have hT_ne0 : #T ≠ 0 := by
    intro h0
    have hex : ∃ v : U, v ≠ x := by
      by_contra hall; push Not at hall
      have : Fintype.card U ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (hall a).trans (hall b).symm)
      omega
    obtain ⟨v, hne⟩ := hex; obtain ⟨t, ht, _⟩ := hT_undom v hne
    rw [Finset.card_eq_zero.mp h0] at ht; exact Finset.notMem_empty t ht
  have hT_ne1 : #T ≠ 1 := by
    intro h1; obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    have hna : ∀ v : U, v ≠ x → ¬ H.Adj a v := fun v hne => by
      obtain ⟨t, ht, h⟩ := hT_undom v hne; rw [Finset.mem_singleton.mp ht] at h; exact h
    have hdeg_a : wdeg H ω a ≤ ω x := by
      rw [wdeg]; calc ∑ v : U, (if H.Adj a v then ω v else 0)
          ≤ ∑ v : U, (if v = x then ω v else 0) := Finset.sum_le_sum (fun v _ => by
            by_cases hvx : v = x
            · rw [if_pos hvx]; split_ifs <;> linarith [hpos v]
            · simp [hvx, hna v hvx])
        _ = ω x := by simp
    linarith [hreg a]
  have hT_ne2 : #T ≠ 2 := by
    intro h2; obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    have hax : H.Adj x a := (Finset.mem_filter.mp (hT_sub (by simp))).2
    have hbx : H.Adj x b := (Finset.mem_filter.mp (hT_sub (by simp))).2
    have hab_na : ¬ H.Adj a b := fun h => tf_contra G.hTF hax h hbx
    let Q := Finset.univ.filter (fun v : U => ¬ H.Adj v x ∧ ¬ H.Adj v a ∧ ¬ H.Adj v b)
    have hsum3 : ∑ u ∈ ({x, a, b} : Finset U), wdeg H ω u = 3 * δ := by
      rw [Finset.sum_insert (by simp [H.ne_of_adj hax, H.ne_of_adj hbx]),
          Finset.sum_insert (by simp [hab]), Finset.sum_singleton, hreg x, hreg a, hreg b]; ring
    rw [sum_wdeg_eq_sum_hits] at hsum3
    have hcnt : ∀ v : U, (#(({x, a, b} : Finset U).filter (H.Adj v)) : ℝ) =
        1 + (if v = x then (1 : ℝ) else 0) - (if v ∈ Q then (1 : ℝ) else 0) := by
      intro v
      have h3 : #(({x, a, b} : Finset U).filter (H.Adj v)) =
          (if H.Adj v x then 1 else 0) + (if H.Adj v a then 1 else 0) + (if H.Adj v b then 1 else 0) := by
        rw [Finset.card_filter, Finset.sum_insert (by simp [H.ne_of_adj hax, H.ne_of_adj hbx]),
            Finset.sum_insert (by simp [hab]), Finset.sum_singleton]; omega
      rw [h3]
      by_cases hvx : v = x
      · subst hvx; have hQ : v ∉ Q := by simp [Q, hax]
        simp [hQ, hax, hbx]; norm_num
      · have hnotab : ¬ (H.Adj v a ∧ H.Adj v b) := by
          rintro ⟨h1, h2⟩; obtain ⟨t, ht, hnt⟩ := hT_undom v hvx
          rcases Finset.mem_insert.mp ht with rfl | ht2
          · exact hnt h1.symm
          · exact hnt (Finset.mem_singleton.mp ht2 ▸ h2.symm)
        have hnotxa : ¬ (H.Adj v x ∧ H.Adj v a) := fun ⟨h1, h2⟩ => tf_contra G.hTF h1 hax h2
        have hnotxb : ¬ (H.Adj v x ∧ H.Adj v b) := fun ⟨h1, h2⟩ => tf_contra G.hTF h1 hbx h2
        by_cases hQ : v ∈ Q
        · have ⟨h1, h2, h3'⟩ := (Finset.mem_filter.mp hQ).2; simp [hvx, hQ, h1, h2, h3']
        · have hex : H.Adj v x ∨ H.Adj v a ∨ H.Adj v b := by
            by_contra hnone; push Not at hnone; exact hQ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
          simp only [hvx, hQ, ↓reduceIte, add_zero, sub_zero]
          have : (if H.Adj v x then (1 : ℕ) else 0) + (if H.Adj v a then 1 else 0) + (if H.Adj v b then 1 else 0) = 1 := by
            by_cases hx : H.Adj v x
            · by_cases ha : H.Adj v a
              · exact absurd ⟨hx, ha⟩ hnotxa
              · by_cases hb : H.Adj v b
                · exact absurd ⟨hx, hb⟩ hnotxb
                · simp [hx, ha, hb]
            · rcases hex with h1 | h1 | h1
              · exact absurd h1 hx
              · by_cases hb : H.Adj v b
                · exact absurd ⟨h1, hb⟩ hnotab
                · simp [hx, h1, hb]
              · by_cases ha : H.Adj v a
                · exact absurd ⟨ha, h1⟩ hnotab
                · simp [hx, ha, h1]
          exact_mod_cast this
    have hQeq : wsum ω Q = 1 + ω x - 3 * δ := by
      have h1 : 3 * δ = ∑ v : U, (1 + (if v = x then (1 : ℝ) else 0) - (if v ∈ Q then (1 : ℝ) else 0)) * ω v := by
        rw [← hsum3]; apply Finset.sum_congr rfl; intro v _; rw [hcnt v]
      simp only [sub_mul, add_mul, one_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hsum] at h1
      have hQw : (∑ v : U, if v ∈ Q then ω v else 0) = wsum ω Q := by simp [wsum]
      rw [hQw] at h1
      linarith
    have hQempty : Q = ∅ := by
      by_contra hne; obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hle : ω q ≤ wsum ω Q := Finset.single_le_sum (fun v _ => hnn v) hq
      linarith [hx_wmin q]
    have hcol3 : H.Colorable 3 := by
      refine ⟨SimpleGraph.Coloring.mk (fun v => if H.Adj v x then 0 else if H.Adj v a then 1 else 2) ?_⟩
      intro u v hadj
      have hcov : ∀ z : U, H.Adj z x ∨ H.Adj z a ∨ H.Adj z b := fun z => by
        by_contra hnone; push Not at hnone
        exact Finset.notMem_empty z (hQempty ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
      have hb_u : ¬ H.Adj u x → ¬ H.Adj u a → H.Adj u b := fun hx fa => by
        rcases hcov u with h | h | h
        · exact absurd h hx
        · exact absurd h fa
        · exact h
      have hb_v : ¬ H.Adj v x → ¬ H.Adj v a → H.Adj v b := fun hx fa => by
        rcases hcov v with h | h | h
        · exact absurd h hx
        · exact absurd h fa
        · exact h
      by_cases hux : H.Adj u x
      · have hvx : ¬ H.Adj v x := fun h => tf_contra G.hTF hadj h hux
        by_cases hva : H.Adj v a
        · simp [hux, hvx, hva]
        · simp [hux, hvx, hva]
      · by_cases hua : H.Adj u a
        · by_cases hva : H.Adj v a
          · exact (tf_contra G.hTF hadj hva hua).elim
          · by_cases hvx : H.Adj v x
            · simp [hux, hua, hvx]
            · simp [hux, hua, hvx, hva]
        · have hub : H.Adj u b := hb_u hux hua
          by_cases hvb : H.Adj v b
          · exact (tf_contra G.hTF hadj hvb hub).elim
          · by_cases hvx : H.Adj v x
            · simp [hux, hua, hvx]
            · by_cases hva : H.Adj v a
              · simp [hux, hua, hvx, hva]
              · exact absurd (hb_v hvx hva) hvb
    exact G.hNot3 hcol3
  have hT_eq3 : #T = 3 := by omega
  obtain ⟨a, b, c, hab, hac, hbc, hTeq⟩ := Finset.card_eq_three.mp hT_eq3
  subst hTeq
  have hax : H.Adj x a := (Finset.mem_filter.mp (hT_sub (by simp))).2
  have hbx : H.Adj x b := (Finset.mem_filter.mp (hT_sub (by simp))).2
  have hcx : H.Adj x c := (Finset.mem_filter.mp (hT_sub (by simp))).2
  have hxa_ne : x ≠ a := H.ne_of_adj hax
  have hxb_ne : x ≠ b := H.ne_of_adj hbx
  have hxc_ne : x ≠ c := H.ne_of_adj hcx
  have hab_na : ¬ H.Adj a b := fun h => tf_contra G.hTF hax h hbx
  have hac_na : ¬ H.Adj a c := fun h => tf_contra G.hTF hax h hcx
  have hbc_na : ¬ H.Adj b c := fun h => tf_contra G.hTF hbx h hcx
  have hnot_abc : ∀ v : U, v ≠ x → ¬ (H.Adj v a ∧ H.Adj v b ∧ H.Adj v c) := fun v hne ⟨h1, h2, h3⟩ => by
    obtain ⟨t, ht, hnt⟩ := hT_undom v hne
    rcases Finset.mem_insert.mp ht with rfl | ht2
    · exact hnt h1.symm
    · rcases Finset.mem_insert.mp ht2 with rfl | ht3
      · exact hnt h2.symm
      · exact hnt (Finset.mem_singleton.mp ht3 ▸ h3.symm)
  -- Claims 2 & 3: Exact 5-Block Decomposition `univ = Nx ⊔ R ⊔ I1 ⊔ I2 ⊔ I3`
  let U_set := Finset.univ.filter (fun z : U => z ≠ x ∧ H.Adj z b ∧ H.Adj z c)
  let V_set := Finset.univ.filter (fun z : U => z ≠ x ∧ H.Adj z a ∧ H.Adj z c)
  let W_set := Finset.univ.filter (fun z : U => z ≠ x ∧ H.Adj z a ∧ H.Adj z b)
  have hU_ne_set : U_set.Nonempty := by
    obtain ⟨v, hne, hv⟩ := hT_min' a (by simp)
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, (hv b (by simp) hab.symm).symm, (hv c (by simp) hac.symm).symm⟩⟩
  have hV_ne_set : V_set.Nonempty := by
    obtain ⟨v, hne, hv⟩ := hT_min' b (by simp)
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, (hv a (by simp) hab).symm, (hv c (by simp) hbc.symm).symm⟩⟩
  have hW_ne_set : W_set.Nonempty := by
    obtain ⟨v, hne, hv⟩ := hT_min' c (by simp)
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, (hv a (by simp) hac).symm, (hv b (by simp) hbc).symm⟩⟩
  let R_set := insert x (U_set ∪ V_set ∪ W_set)
  let I1 := Finset.univ.filter (fun z : U => H.Adj z a ∧ z ∉ R_set)
  let I2 := Finset.univ.filter (fun z : U => H.Adj z b ∧ z ∉ R_set)
  let I3 := Finset.univ.filter (fun z : U => H.Adj z c ∧ z ∉ R_set)
  let Q_set := Finset.univ.filter (fun z : U => ¬ H.Adj z x ∧ ¬ H.Adj z a ∧ ¬ H.Adj z b ∧ ¬ H.Adj z c)
  have hR_ind : ∀ z1 ∈ R_set, ∀ z2 ∈ R_set, ¬ H.Adj z1 z2 := by
    intro z1 h1 z2 h2 hadj
    have hhit : ∀ z ∈ R_set, (z = x) ∨ (H.Adj z b ∧ H.Adj z c) ∨ (H.Adj z a ∧ H.Adj z c) ∨ (H.Adj z a ∧ H.Adj z b) := by
      intro z hz; simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rcases hz with rfl | ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    rcases hhit z1 h1 with rfl | ⟨h1b, h1c⟩ | ⟨h1a, h1c⟩ | ⟨h1a, h1b⟩ <;>
      rcases hhit z2 h2 with rfl | ⟨h2b, h2c⟩ | ⟨h2a, h2c⟩ | ⟨h2a, h2b⟩
    all_goals first
      | exact H.loopless.irrefl _ hadj
      | exact tf_contra G.hTF hadj h2b hbx
      | exact tf_contra G.hTF hadj h2a hax
      | exact tf_contra G.hTF hadj.symm h1b hbx
      | exact tf_contra G.hTF hadj.symm h1a hax
      | exact tf_contra G.hTF hadj h2a h1a
      | exact tf_contra G.hTF hadj h2b h1b
      | exact tf_contra G.hTF hadj h2c h1c
  have hR_le_δ : wsum ω R_set ≤ δ := indep_weight_le_delta H G.hTF G.hMax hpos hsum hreg hδ R_set hR_ind
  -- Double count hits into `{x, a, b, c}`
  have hsum4 : ∑ u ∈ ({x, a, b, c} : Finset U), wdeg H ω u = 4 * δ := by
    rw [Finset.sum_insert (by simp [hxa_ne, hxb_ne, hxc_ne]), Finset.sum_insert (by simp [hab, hac]),
        Finset.sum_insert (by simp [hbc]), Finset.sum_singleton, hreg x, hreg a, hreg b, hreg c]; ring
  rw [sum_wdeg_eq_sum_hits] at hsum4
  have hcnt4 : ∀ v : U, (#(({x, a, b, c} : Finset U).filter (H.Adj v)) : ℝ) =
      1 + (if v = x then (1 : ℝ) else 0) + (if v ∈ R_set then (1 : ℝ) else 0) - (if v ∈ Q_set then (1 : ℝ) else 0) := by
    intro v
    have h4 : #(({x, a, b, c} : Finset U).filter (H.Adj v)) =
        (if H.Adj v x then 1 else 0) + (if H.Adj v a then 1 else 0) + (if H.Adj v b then 1 else 0) + (if H.Adj v c then 1 else 0) := by
      rw [Finset.card_filter, Finset.sum_insert (by simp [hxa_ne, hxb_ne, hxc_ne]),
          Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]), Finset.sum_singleton]; omega
    rw [h4]
    by_cases hvx : v = x
    · subst hvx
      have hxR : v ∈ R_set := Finset.mem_insert_self v _
      have hxQ : v ∉ Q_set := by simp [Q_set, hax]
      simp [hxR, hxQ, hax, hbx, hcx]; norm_num
    · have hn3 := hnot_abc v hvx
      have hnxa : ¬ (H.Adj v x ∧ H.Adj v a) := fun ⟨h1, h2⟩ => tf_contra G.hTF h1 hax h2
      have hnxb : ¬ (H.Adj v x ∧ H.Adj v b) := fun ⟨h1, h2⟩ => tf_contra G.hTF h1 hbx h2
      have hnxc : ¬ (H.Adj v x ∧ H.Adj v c) := fun ⟨h1, h2⟩ => tf_contra G.hTF h1 hcx h2
      have hvR_iff : v ∈ R_set ↔ (H.Adj v b ∧ H.Adj v c) ∨ (H.Adj v a ∧ H.Adj v c) ∨ (H.Adj v a ∧ H.Adj v b) := by
        simp [R_set, U_set, V_set, W_set, hvx]
      by_cases hvR : v ∈ R_set
      · have hvQ : v ∉ Q_set := by
          intro hq; have ⟨_, hna, hnb, hnc⟩ := (Finset.mem_filter.mp hq).2
          rcases hvR_iff.mp hvR with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> [exact hnb h; exact hna h; exact hna h]
        simp only [hvx, hvR, hvQ, ↓reduceIte, add_zero, sub_zero]
        have : (if H.Adj v x then (1 : ℕ) else 0) + (if H.Adj v a then 1 else 0) + (if H.Adj v b then 1 else 0) + (if H.Adj v c then 1 else 0) = 2 := by
          rcases hvR_iff.mp hvR with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hx : ¬ H.Adj v x := fun h => hnxb ⟨h, h1⟩
            have ha : ¬ H.Adj v a := fun h => hn3 ⟨h, h1, h2⟩
            simp [hx, ha, h1, h2]
          · have hx : ¬ H.Adj v x := fun h => hnxa ⟨h, h1⟩
            have hb : ¬ H.Adj v b := fun h => hn3 ⟨h1, h, h2⟩
            simp [hx, hb, h1, h2]
          · have hx : ¬ H.Adj v x := fun h => hnxa ⟨h, h1⟩
            have hc : ¬ H.Adj v c := fun h => hn3 ⟨h1, h2, h⟩
            simp [hx, hc, h1, h2]
        exact_mod_cast this
      · by_cases hvQ : v ∈ Q_set
        · have ⟨h1, h2, h3, h4'⟩ := (Finset.mem_filter.mp hvQ).2; simp [hvx, hvR, hvQ, h1, h2, h3, h4']
        · simp only [hvx, hvR, hvQ, ↓reduceIte, add_zero, sub_zero]
          have hnot2 : ¬ ((H.Adj v b ∧ H.Adj v c) ∨ (H.Adj v a ∧ H.Adj v c) ∨ (H.Adj v a ∧ H.Adj v b)) :=
            fun h => hvR (hvR_iff.mpr h)
          have hex : H.Adj v x ∨ H.Adj v a ∨ H.Adj v b ∨ H.Adj v c := by
            by_contra hnone; push Not at hnone; exact hvQ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
          have : (if H.Adj v x then (1 : ℕ) else 0) + (if H.Adj v a then 1 else 0) + (if H.Adj v b then 1 else 0) + (if H.Adj v c then 1 else 0) = 1 := by
            by_cases hx : H.Adj v x
            · have ha : ¬ H.Adj v a := fun h => hnxa ⟨hx, h⟩
              have hb : ¬ H.Adj v b := fun h => hnxb ⟨hx, h⟩
              have hc : ¬ H.Adj v c := fun h => hnxc ⟨hx, h⟩
              simp [hx, ha, hb, hc]
            · rcases hex with h1 | h1 | h1 | h1
              · exact absurd h1 hx
              · have hb : ¬ H.Adj v b := fun h => hnot2 (Or.inr (Or.inr ⟨h1, h⟩))
                have hc : ¬ H.Adj v c := fun h => hnot2 (Or.inr (Or.inl ⟨h1, h⟩))
                simp [hx, h1, hb, hc]
              · have ha : ¬ H.Adj v a := fun h => hnot2 (Or.inr (Or.inr ⟨h, h1⟩))
                have hc : ¬ H.Adj v c := fun h => hnot2 (Or.inl ⟨h1, h⟩)
                simp [hx, h1, ha, hc]
              · have ha : ¬ H.Adj v a := fun h => hnot2 (Or.inr (Or.inl ⟨h, h1⟩))
                have hb : ¬ H.Adj v b := fun h => hnot2 (Or.inl ⟨h, h1⟩)
                simp [hx, h1, ha, hb]
          exact_mod_cast this
  have hRQ_eq : 4 * δ = 1 + ω x + wsum ω R_set - wsum ω Q_set := by
    have h1 : 4 * δ = ∑ v : U, (1 + (if v = x then (1 : ℝ) else 0) + (if v ∈ R_set then (1 : ℝ) else 0) - (if v ∈ Q_set then (1 : ℝ) else 0)) * ω v := by
      rw [← hsum4]; apply Finset.sum_congr rfl; intro v _; rw [hcnt4 v]
    simp only [sub_mul, add_mul, one_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hsum] at h1
    have hRw : (∑ v : U, if v ∈ R_set then ω v else 0) = wsum ω R_set := by simp [wsum]
    have hQw : (∑ v : U, if v ∈ Q_set then ω v else 0) = wsum ω Q_set := by simp [wsum]
    rw [hRw, hQw] at h1
    exact h1
  have hQ_empty : Q_set = ∅ := by
    by_contra hne; obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hle : ω q ≤ wsum ω Q_set := Finset.single_le_sum (fun v _ => hnn v) hq
    linarith [hx_wmin q]
  have hwRval : wsum ω R_set = 4 * δ - 1 - ω x := by
    have : wsum ω Q_set = 0 := by rw [wsum, hQ_empty, Finset.sum_empty]
    linarith
  have hR_max : ∀ z : U, z ∉ R_set → ∃ r ∈ R_set, H.Adj z r := by
    intro z hz; by_contra hno; push Not at hno
    have hInd' : ∀ u ∈ insert z R_set, ∀ v ∈ insert z R_set, ¬ H.Adj u v := by
      intro u hu v hv hadj
      rcases Finset.mem_insert.mp hu with rfl | huR <;> rcases Finset.mem_insert.mp hv with rfl | hvR
      · exact H.loopless.irrefl _ hadj
      · exact hno v hvR hadj
      · exact hno u huR hadj.symm
      · exact hR_ind u huR v hvR hadj
    have hle : wsum ω (insert z R_set) ≤ δ :=
      indep_weight_le_delta H G.hTF G.hMax hpos hsum hreg hδ (insert z R_set) hInd'
    have hins : wsum ω (insert z R_set) = ω z + wsum ω R_set := by
      rw [wsum, wsum, Finset.sum_insert hz]
    rw [hins] at hle
    linarith [hx_wmin z]
  -- Exact 5-block partition membership helper
  have hpart : ∀ z : U, z ∈ Nx ∨ z ∈ R_set ∨ z ∈ I1 ∨ z ∈ I2 ∨ z ∈ I3 := by
    intro z
    by_cases hx' : H.Adj x z
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩)
    · by_cases hR' : z ∈ R_set
      · exact Or.inr (Or.inl hR')
      · by_cases ha' : H.Adj z a
        · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha', hR'⟩)))
        · by_cases hb' : H.Adj z b
          · exact Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb', hR'⟩))))
          · by_cases hc' : H.Adj z c
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc', hR'⟩))))
            · exfalso; exact Finset.notMem_empty z (hQ_empty ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hx' h.symm, ha', hb', hc'⟩)
  -- Block avoidance facts
  have hI1_na : ∀ z ∈ I1, ¬ H.Adj z x ∧ ¬ H.Adj z b ∧ ¬ H.Adj z c := by
    intro z hz; have ⟨hza, hzR⟩ := (Finset.mem_filter.mp hz).2
    have hzx_ne : z ≠ x := fun h => hzR (h ▸ Finset.mem_insert_self x _)
    exact ⟨fun h => tf_contra G.hTF h hax hza,
           fun h => hzR (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzx_ne, hza, h⟩))),
           fun h => hzR (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzx_ne, hza, h⟩))))⟩
  have hI2_na : ∀ z ∈ I2, ¬ H.Adj z x ∧ ¬ H.Adj z a ∧ ¬ H.Adj z c := by
    intro z hz; have ⟨hzb, hzR⟩ := (Finset.mem_filter.mp hz).2
    have hzx_ne : z ≠ x := fun h => hzR (h ▸ Finset.mem_insert_self x _)
    exact ⟨fun h => tf_contra G.hTF h hbx hzb,
           fun h => hzR (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzx_ne, h, hzb⟩))),
           fun h => hzR (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzx_ne, hzb, h⟩))))⟩
  have hI3_na : ∀ z ∈ I3, ¬ H.Adj z x ∧ ¬ H.Adj z a ∧ ¬ H.Adj z b := by
    intro z hz; have ⟨hzc, hzR⟩ := (Finset.mem_filter.mp hz).2
    have hzx_ne : z ≠ x := fun h => hzR (h ▸ Finset.mem_insert_self x _)
    exact ⟨fun h => tf_contra G.hTF h hcx hzc,
           fun h => hzR (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzx_ne, h, hzc⟩)))),
           fun h => hzR (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzx_ne, h, hzc⟩))))⟩
  have hNx_ind : ∀ p ∈ Nx, ∀ q ∈ Nx, ¬ H.Adj p q := fun p hp q hq h =>
    tf_contra G.hTF (Finset.mem_filter.mp hp).2 h (Finset.mem_filter.mp hq).2
  have hI1_ind : ∀ p ∈ I1, ∀ q ∈ I1, ¬ H.Adj p q := fun p hp q hq h =>
    tf_contra G.hTF (Finset.mem_filter.mp hp).2.1.symm h (Finset.mem_filter.mp hq).2.1.symm
  have hI2_ind : ∀ p ∈ I2, ∀ q ∈ I2, ¬ H.Adj p q := fun p hp q hq h =>
    tf_contra G.hTF (Finset.mem_filter.mp hp).2.1.symm h (Finset.mem_filter.mp hq).2.1.symm
  have hI3_ind : ∀ p ∈ I3, ∀ q ∈ I3, ¬ H.Adj p q := fun p hp q hq h =>
    tf_contra G.hTF (Finset.mem_filter.mp hp).2.1.symm h (Finset.mem_filter.mp hq).2.1.symm
  -- Claims 4 & 5: Reusable Universal Witness Helper (called 3 times for u, v, w!)
  have huniv_wit : ∀ (a0 b0 c0 : U) (U0 I0 : Finset U),
      H.Adj x a0 → H.Adj x b0 → H.Adj x c0 →
      (∀ z ∈ U0, z ∈ R_set ∧ H.Adj z b0 ∧ H.Adj z c0) →
      (∀ z ∈ R_set, ¬ H.Adj z a0 → z ≠ x → z ∈ U0) →
      (∀ z ∈ I0, H.Adj z a0 ∧ z ∉ R_set) →
      (∀ z : U, z ∉ Nx → z ∉ R_set → ¬ H.Adj z b0 → ¬ H.Adj z c0 → z ∈ I0) →
      U0.Nonempty →
      ∃ u0 ∈ U0, (∀ p ∈ Nx, H.Adj u0 p → ∀ u' ∈ U0, H.Adj p u') ∧ (∀ z ∈ I0, H.Adj u0 z) := by
    intro a0 b0 c0 U0 I0 ha0x hb0x hc0x hU0_spec hU0_ofR hI0_spec hI0_of hU0_ne
    obtain ⟨u0, hu0U, hu0_max⟩ := Finset.exists_max_image U0 (fun u' => wsum ω (I0.filter (H.Adj u'))) hU0_ne
    have hcl4 : ∀ p ∈ Nx, H.Adj u0 p → ∀ u1 ∈ U0, H.Adj p u1 := by
      intro p hp hup u1 hu1U
      by_contra hna
      have hp_ne_u1 : p ≠ u1 := fun h => hNx_ind p hp b0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0x⟩) (h ▸ (hU0_spec u1 hu1U).2.1)
      obtain ⟨x0, hpx0, hu1x0⟩ := G.hMax p u1 hp_ne_u1 hna
      have hx0_I0 : x0 ∈ I0 := by
        apply hI0_of x0
        · intro hx0N; exact hNx_ind p hp x0 hx0N hpx0
        · intro hx0R; exact hR_ind u1 (hU0_spec u1 hu1U).1 x0 hx0R hu1x0
        · intro hb; exact tf_contra G.hTF hu1x0 hb (hU0_spec u1 hu1U).2.1
        · intro hc; exact tf_contra G.hTF hu1x0 hc (hU0_spec u1 hu1U).2.2
      have hna_u0x0 : ¬ H.Adj u0 x0 := fun h => tf_contra G.hTF hup hpx0 h
      have hex_x0' : ∃ x0' ∈ I0, H.Adj u0 x0' ∧ ¬ H.Adj u1 x0' := by
        by_contra hall; push Not at hall
        have hsub : I0.filter (H.Adj u0) ⊆ (I0.filter (H.Adj u1)).erase x0 := fun z hz => by
          have hz' := Finset.mem_filter.mp hz
          refine Finset.mem_erase.mpr ⟨fun h => hna_u0x0 (h ▸ hz'.2), Finset.mem_filter.mpr ⟨hz'.1, hall z hz'.1 hz'.2⟩⟩
        have hmem_x0 : x0 ∈ I0.filter (H.Adj u1) := Finset.mem_filter.mpr ⟨hx0_I0, hu1x0⟩
        have hlt : wsum ω (I0.filter (H.Adj u0)) < wsum ω (I0.filter (H.Adj u1)) := by
          have h1 : wsum ω (I0.filter (H.Adj u0)) ≤ wsum ω ((I0.filter (H.Adj u1)).erase x0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hnn _)
          have h2 : wsum ω ((I0.filter (H.Adj u1)).erase x0) + ω x0 = wsum ω (I0.filter (H.Adj u1)) :=
            Finset.sum_erase_add _ _ hmem_x0
          linarith [hpos x0]
        linarith [hu0_max u1 hu1U]
      obtain ⟨x0', hx0'I, hu0x0', hna_u1x0'⟩ := hex_x0'
      have hu1_ne_x0' : u1 ≠ x0' := fun h => (hI0_spec x0' hx0'I).2 (h ▸ (hU0_spec u1 hu1U).1)
      obtain ⟨q, hqu1, hqx0'⟩ := G.hMax u1 x0' hu1_ne_x0' hna_u1x0'
      have hq_Nx : q ∈ Nx := by
        by_contra hnotN
        have hq_notR : q ∉ R_set := fun h => hR_ind u1 (hU0_spec u1 hu1U).1 q h hqu1
        have hq_nab : ¬ H.Adj q b0 := fun h => tf_contra G.hTF hqu1 h (hU0_spec u1 hu1U).2.1
        have hq_nac : ¬ H.Adj q c0 := fun h => tf_contra G.hTF hqu1 h (hU0_spec u1 hu1U).2.2
        have hq_I0 : q ∈ I0 := hI0_of q hnotN hq_notR hq_nab hq_nac
        exact tf_contra G.hTF (hI0_spec q hq_I0).1.symm hqx0'.symm (hI0_spec x0' hx0'I).1.symm
      have hna_u0q : ¬ H.Adj u0 q := fun h => tf_contra G.hTF hu0x0' hqx0' h
      have hu0_ne_u1 : u0 ≠ u1 := fun h => hna (h ▸ hup.symm)
      have hp_ne_q : p ≠ q := fun h => hna_u0q (h ▸ hup)
      have hx0_ne_x0' : x0 ≠ x0' := fun h => hna_u0x0 (h ▸ hu0x0')
      have hdisj_RN : ∀ r ∈ R_set, ∀ n ∈ Nx, r ≠ n := fun r hr n hn h => by
        subst h; rcases eq_or_ne r x with rfl | hne
        · exact H.loopless.irrefl _ (Finset.mem_filter.mp hn).2
        · exact hR_ind r hr x (Finset.mem_insert_self x _) (Finset.mem_filter.mp hn).2.symm
      have hdisj_IN : ∀ z ∈ I0, ∀ n ∈ Nx, z ≠ n := fun z hz n hn h => by
        subst h; exact hNx_ind z hn a0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha0x⟩) (hI0_spec z hz).1
      let cyc : Fin 6 → U := ![u0, p, x0, u1, q, x0']
      have hcyc_inj : Function.Injective cyc := by
        have hu0R := (hU0_spec u0 hu0U).1; have hu1R := (hU0_spec u1 hu1U).1
        intro i j hij; fin_cases i <;> fin_cases j <;> dsimp [cyc] at hij ⊢
        all_goals first | rfl | exact (hu0_ne_u1 hij).elim | exact (hu0_ne_u1 hij.symm).elim
                        | exact (hp_ne_q hij).elim | exact (hp_ne_q hij.symm).elim
                        | exact (hx0_ne_x0' hij).elim | exact (hx0_ne_x0' hij.symm).elim
                        | exact (hdisj_RN _ hu0R _ hp hij).elim | exact (hdisj_RN _ hu0R _ hp hij.symm).elim
                        | exact (hdisj_RN _ hu0R _ hq_Nx hij).elim | exact (hdisj_RN _ hu0R _ hq_Nx hij.symm).elim
                        | exact (hdisj_RN _ hu1R _ hp hij).elim | exact (hdisj_RN _ hu1R _ hp hij.symm).elim
                        | exact (hdisj_RN _ hu1R _ hq_Nx hij).elim | exact (hdisj_RN _ hu1R _ hq_Nx hij.symm).elim
                        | exact (hdisj_IN _ hx0_I0 _ hp hij).elim | exact (hdisj_IN _ hx0_I0 _ hp hij.symm).elim
                        | exact (hdisj_IN _ hx0_I0 _ hq_Nx hij).elim | exact (hdisj_IN _ hx0_I0 _ hq_Nx hij.symm).elim
                        | exact (hdisj_IN _ hx0'I _ hp hij).elim | exact (hdisj_IN _ hx0'I _ hp hij.symm).elim
                        | exact (hdisj_IN _ hx0'I _ hq_Nx hij).elim | exact (hdisj_IN _ hx0'I _ hq_Nx hij.symm).elim
                        | exact ((hI0_spec _ hx0_I0).2 (hij ▸ hu0R)).elim | exact ((hI0_spec _ hx0_I0).2 (hij.symm ▸ hu0R)).elim
                        | exact ((hI0_spec _ hx0_I0).2 (hij ▸ hu1R)).elim | exact ((hI0_spec _ hx0_I0).2 (hij.symm ▸ hu1R)).elim
                        | exact ((hI0_spec _ hx0'I).2 (hij ▸ hu0R)).elim | exact ((hI0_spec _ hx0'I).2 (hij.symm ▸ hu0R)).elim
                        | exact ((hI0_spec _ hx0'I).2 (hij ▸ hu1R)).elim
      obtain ⟨z, hz⟩ := exists_dom3_of_c6 H G.hTF hnn hsum hdeg cyc hcyc_inj
        hup hpx0 hu1x0.symm hqu1 hqx0'.symm hu0x0'.symm
      have hno3 : ∀ (r' n' z' : U), r' ∈ U0 → n' ∈ Nx → z' ∈ I0 → H.Adj z r' → H.Adj z n' → H.Adj z z' → False := by
        intro r' n' z' hr' hn' hz' hzr hzn hzz
        have hz_notN : z ∉ Nx := fun h => hNx_ind z h n' hn' hzn
        have hz_notR : z ∉ R_set := fun h => hR_ind z h r' (hU0_spec r' hr').1 hzr
        have hz_nab : ¬ H.Adj z b0 := fun h => tf_contra G.hTF hzr (hU0_spec r' hr').2.1 h
        have hz_nac : ¬ H.Adj z c0 := fun h => tf_contra G.hTF hzr (hU0_spec r' hr').2.2 h
        have hz_I0 : z ∈ I0 := hI0_of z hz_notN hz_notR hz_nab hz_nac
        exact tf_contra G.hTF (hI0_spec z hz_I0).1.symm hzz (hI0_spec z' hz').1.symm
      rcases hz with ⟨h0, h2, h4⟩ | ⟨h1, h3, h5⟩
      · exact hno3 u0 q x0 hu0U hq_Nx hx0_I0 h0 h4 h2
      · exact hno3 u1 p x0' hu1U hp hx0'I h3 h1 h5
    refine ⟨u0, hu0U, hcl4, fun x0 hx0I => ?_⟩
    by_contra hna
    obtain ⟨r, hrR, hrx0⟩ := hR_max x0 (hI0_spec x0 hx0I).2
    have hr_ne_x : r ≠ x := fun h => tf_contra G.hTF (h ▸ hrx0) ha0x (hI0_spec x0 hx0I).1
    have hr_na_a0 : ¬ H.Adj r a0 := fun h => tf_contra G.hTF hrx0 h (hI0_spec x0 hx0I).1
    have hrU0 : r ∈ U0 := hU0_ofR r hrR hr_na_a0 hr_ne_x
    have hu0_ne_x0 : u0 ≠ x0 := fun h => (hI0_spec x0 hx0I).2 (h ▸ (hU0_spec u0 hu0U).1)
    obtain ⟨p, hpu0, hpx0⟩ := G.hMax u0 x0 hu0_ne_x0 hna
    have hpN : p ∈ Nx := by
      by_contra hnotN
      have hp_notR : p ∉ R_set := fun h => hR_ind u0 (hU0_spec u0 hu0U).1 p h hpu0
      have hp_nab : ¬ H.Adj p b0 := fun h => tf_contra G.hTF hpu0 h (hU0_spec u0 hu0U).2.1
      have hp_nac : ¬ H.Adj p c0 := fun h => tf_contra G.hTF hpu0 h (hU0_spec u0 hu0U).2.2
      exact tf_contra G.hTF (hI0_spec p (hI0_of p hnotN hp_notR hp_nab hp_nac)).1.symm hpx0.symm (hI0_spec x0 hx0I).1.symm
    exact tf_contra G.hTF (hcl4 p hpN hpu0 r hrU0) hrx0.symm hpx0.symm
  -- Obtain universal witnesses `u ∈ U_set`, `v ∈ V_set`, `w ∈ W_set`
  obtain ⟨u, huU, hu_cl4, hu_I1⟩ := huniv_wit a b c U_set I1 hax hbx hcx
    (fun z hz => ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hz)), (Finset.mem_filter.mp hz).2.2⟩)
    (fun z hz hna hne => by
      simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rcases hz with rfl | ((h | ⟨_, h1, _⟩) | ⟨_, h1, _⟩) <;> [exact (hne rfl).elim; exact h; exact (hna h1).elim; exact (hna h1).elim])
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hN hR hnb hnc => by
      rcases hpart z with h | h | h | h | h
      · exact (hN h).elim
      · exact (hR h).elim
      · exact h
      · exact (hnb (Finset.mem_filter.mp h).2.1).elim
      · exact (hnc (Finset.mem_filter.mp h).2.1).elim) hU_ne_set
  obtain ⟨v, hvV, hv_cl4, hv_I2⟩ := huniv_wit b c a V_set I2 hbx hcx hax
    (fun z hz => ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hz)), (Finset.mem_filter.mp hz).2.2.2, (Finset.mem_filter.mp hz).2.2.1⟩)
    (fun z hz hna hne => by
      simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rcases hz with rfl | ((⟨_, h1, _⟩ | h) | ⟨_, _, h1⟩) <;> [exact (hne rfl).elim; exact (hna h1).elim; exact h; exact (hna h1).elim])
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hN hR hnc hna => by
      rcases hpart z with h | h | h | h | h
      · exact (hN h).elim
      · exact (hR h).elim
      · exact (hna (Finset.mem_filter.mp h).2.1).elim
      · exact h
      · exact (hnc (Finset.mem_filter.mp h).2.1).elim) hV_ne_set
  obtain ⟨w, hwW, hw_cl4, hw_I3⟩ := huniv_wit c a b W_set I3 hcx hax hbx
    (fun z hz => ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ hz), (Finset.mem_filter.mp hz).2.2⟩)
    (fun z hz hna hne => by
      simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rcases hz with rfl | ((⟨_, _, h1⟩ | ⟨_, _, h1⟩) | h) <;> [exact (hne rfl).elim; exact (hna h1).elim; exact (hna h1).elim; exact h])
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hN hR hna hnb => by
      rcases hpart z with h | h | h | h | h
      · exact (hN h).elim
      · exact (hR h).elim
      · exact (hna (Finset.mem_filter.mp h).2.1).elim
      · exact (hnb (Finset.mem_filter.mp h).2.1).elim
      · exact h) hW_ne_set
  -- Claims 6 & 7: Decomposition `Nx = Y ⊔ A ⊔ B ⊔ C` (`#Y ≤ 1`)
  let Y_set := Nx.filter (fun z => H.Adj z u ∧ H.Adj z v ∧ H.Adj z w)
  let A_set := Nx.filter (fun z => ¬ H.Adj z u ∧ H.Adj z v ∧ H.Adj z w)
  let B_set := Nx.filter (fun z => H.Adj z u ∧ ¬ H.Adj z v ∧ H.Adj z w)
  let C_set := Nx.filter (fun z => H.Adj z u ∧ H.Adj z v ∧ ¬ H.Adj z w)
  have huR : u ∈ R_set := Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ huU))
  have hvR : v ∈ R_set := Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hvV))
  have hwR : w ∈ R_set := Finset.mem_insert_of_mem (Finset.mem_union_right _ hwW)
  have hY_nbhd : ∀ y ∈ Y_set, ∀ z : U, H.Adj y z ↔ z ∈ R_set := by
    intro y hy z
    have hyN := (Finset.mem_filter.mp hy).1
    have ⟨hyu, hyv, hyw⟩ := (Finset.mem_filter.mp hy).2
    have hdomR : ∀ r ∈ R_set, H.Adj y r := by
      intro r hr
      simp only [R_set, Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | ((hrU | hrV) | hrW)
      · exact (Finset.mem_filter.mp hyN).2.symm
      · exact hu_cl4 y hyN hyu.symm r hrU
      · exact hv_cl4 y hyN hyv.symm r hrV
      · exact hw_cl4 y hyN hyw.symm r hrW
    exact ⟨fun hyz => by_contra (fun hnotR => by
      obtain ⟨r, hrR, hzr⟩ := hR_max z hnotR
      exact tf_contra G.hTF hyz hzr (hdomR r hrR)), hdomR z⟩
  have hY_subsing : ∀ y1 ∈ Y_set, ∀ y2 ∈ Y_set, y1 = y2 := fun y1 h1 y2 h2 =>
    G.hTwin y1 y2 (fun z => (hY_nbhd y1 h1 z).trans (hY_nbhd y2 h2 z).symm)
  -- Block avoidance of `u, v, w` on `I1, I2, I3`
  have hu_na_23 : (∀ z ∈ I2, ¬ H.Adj u z) ∧ (∀ z ∈ I3, ¬ H.Adj u z) :=
    ⟨fun z hz h => tf_contra G.hTF h (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp huU).2.2.1,
     fun z hz h => tf_contra G.hTF h (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp huU).2.2.2⟩
  have hv_na_13 : (∀ z ∈ I1, ¬ H.Adj v z) ∧ (∀ z ∈ I3, ¬ H.Adj v z) :=
    ⟨fun z hz h => tf_contra G.hTF h (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp hvV).2.2.1,
     fun z hz h => tf_contra G.hTF h (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp hvV).2.2.2⟩
  have hw_na_12 : (∀ z ∈ I1, ¬ H.Adj w z) ∧ (∀ z ∈ I2, ¬ H.Adj w z) :=
    ⟨fun z hz h => tf_contra G.hTF h (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp hwW).2.2.1,
     fun z hz h => tf_contra G.hTF h (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp hwW).2.2.2⟩
  -- Claim 7: Every `p ∈ Nx` hits at least 2 of `{u, v, w}`!
  have hNx_part : ∀ p ∈ Nx, p ∈ Y_set ∨ p ∈ A_set ∨ p ∈ B_set ∨ p ∈ C_set := by
    by_cases hY_empty : Y_set = ∅
    · -- Case Y = ∅: weight double-counting on `{u, v, w}`
      have hne_uv : u ≠ v := fun h => (hnot_abc u (Finset.mem_filter.mp huU).2.1)
        ⟨h ▸ (Finset.mem_filter.mp hvV).2.2.1, (Finset.mem_filter.mp huU).2.2.1, (Finset.mem_filter.mp huU).2.2.2⟩
      have hne_uw : u ≠ w := fun h => (hnot_abc u (Finset.mem_filter.mp huU).2.1)
        ⟨h ▸ (Finset.mem_filter.mp hwW).2.2.1, (Finset.mem_filter.mp huU).2.2.1, (Finset.mem_filter.mp huU).2.2.2⟩
      have hne_vw : v ≠ w := fun h => (hnot_abc v (Finset.mem_filter.mp hvV).2.1)
        ⟨(Finset.mem_filter.mp hvV).2.2.1, h ▸ (Finset.mem_filter.mp hwW).2.2.2, (Finset.mem_filter.mp hvV).2.2.2⟩
      let Nbad := Nx.filter (fun z => ¬ ((H.Adj z u ∧ H.Adj z v) ∨ (H.Adj z v ∧ H.Adj z w) ∨ (H.Adj z w ∧ H.Adj z u)))
      have hsum_uvw : ∑ z ∈ ({u, v, w} : Finset U), wdeg H ω z = 3 * δ := by
        rw [Finset.sum_insert (by simp [hne_uv, hne_uw]), Finset.sum_insert (by simp [hne_vw]), Finset.sum_singleton,
            hreg u, hreg v, hreg w]; ring
      rw [sum_wdeg_eq_sum_hits] at hsum_uvw
      have hcnt_uvw : ∀ z : U, (#(({u, v, w} : Finset U).filter (H.Adj z)) : ℝ) ≤
          1 + (if z ∈ Nx then (1 : ℝ) else 0) - (if z ∈ R_set then (1 : ℝ) else 0) - (if z ∈ Nbad then (1 : ℝ) else 0) := by
        intro z
        have h3 : #(({u, v, w} : Finset U).filter (H.Adj z)) =
            (if H.Adj z u then 1 else 0) + (if H.Adj z v then 1 else 0) + (if H.Adj z w then 1 else 0) := by
          rw [Finset.card_filter, Finset.sum_insert (by simp [hne_uv, hne_uw]),
              Finset.sum_insert (by simp [hne_vw]), Finset.sum_singleton]; omega
        rw [h3]
        have hNR_disj : ∀ z0, z0 ∈ Nx → z0 ∉ R_set := fun z0 hN hR => by
          rcases eq_or_ne z0 x with rfl | hne
          · exact H.loopless.irrefl _ (Finset.mem_filter.mp hN).2
          · exact hR_ind z0 hR x (Finset.mem_insert_self x _) (Finset.mem_filter.mp hN).2.symm
        rcases hpart z with hzN | hzR | hz1 | hz2 | hz3
        · have hz_notR : z ∉ R_set := hNR_disj z hzN
          have hz_not3 : ¬ (H.Adj z u ∧ H.Adj z v ∧ H.Adj z w) := fun h =>
            Finset.notMem_empty z (hY_empty ▸ Finset.mem_filter.mpr ⟨hzN, h⟩)
          by_cases hzB : z ∈ Nbad
          · have hnot2 := (Finset.mem_filter.mp hzB).2
            have hRHS : 1 + (if z ∈ Nx then (1 : ℝ) else 0) - (if z ∈ R_set then (1 : ℝ) else 0)
                - (if z ∈ Nbad then (1 : ℝ) else 0) = 1 := by norm_num [hzN, hz_notR, hzB]
            rw [hRHS]
            have : (if H.Adj z u then (1 : ℕ) else 0) + (if H.Adj z v then 1 else 0) + (if H.Adj z w then 1 else 0) ≤ 1 := by
              by_cases h1 : H.Adj z u
              · have h2 : ¬ H.Adj z v := fun h => hnot2 (Or.inl ⟨h1, h⟩)
                have h3 : ¬ H.Adj z w := fun h => hnot2 (Or.inr (Or.inr ⟨h, h1⟩))
                simp [h1, h2, h3]
              · by_cases h2 : H.Adj z v
                · have h3 : ¬ H.Adj z w := fun h => hnot2 (Or.inr (Or.inl ⟨h2, h⟩))
                  simp [h1, h2, h3]
                · by_cases h3 : H.Adj z w
                  · simp [h1, h2, h3]
                  · simp [h1, h2, h3]
            exact_mod_cast this
          · have hRHS : 1 + (if z ∈ Nx then (1 : ℝ) else 0) - (if z ∈ R_set then (1 : ℝ) else 0)
                - (if z ∈ Nbad then (1 : ℝ) else 0) = 2 := by norm_num [hzN, hz_notR, hzB]
            rw [hRHS]
            have : (if H.Adj z u then (1 : ℕ) else 0) + (if H.Adj z v then 1 else 0) + (if H.Adj z w then 1 else 0) ≤ 2 := by
              by_cases h1 : H.Adj z u <;> by_cases h2 : H.Adj z v <;> by_cases h3 : H.Adj z w
              · exact absurd ⟨h1, h2, h3⟩ hz_not3
              · simp [h1, h2, h3]
              · simp [h1, h2, h3]
              · simp [h1, h2, h3]
              · simp [h1, h2, h3]
              · simp [h1, h2, h3]
              · simp [h1, h2, h3]
              · simp [h1, h2, h3]
            exact_mod_cast this
        · have hz_notN : z ∉ Nx := fun h => hNR_disj z h hzR
          have hz_notB : z ∉ Nbad := fun h => hz_notN (Finset.mem_filter.mp h).1
          simp [hz_notN, hzR, hz_notB, hR_ind z hzR u huR, hR_ind z hzR v hvR, hR_ind z hzR w hwR]
        · have hz_notN : z ∉ Nx := fun h => (hI1_na z hz1).1 (Finset.mem_filter.mp h).2.symm
          have hz_notR : z ∉ R_set := (Finset.mem_filter.mp hz1).2.2
          have hz_notB : z ∉ Nbad := fun h => hz_notN (Finset.mem_filter.mp h).1
          have hvz : ¬ H.Adj z v := fun h => hv_na_13.1 z hz1 h.symm
          have hwz : ¬ H.Adj z w := fun h => hw_na_12.1 z hz1 h.symm
          simp [hz_notN, hz_notR, hz_notB, (hu_I1 z hz1).symm, hvz, hwz]
        · have hz_notN : z ∉ Nx := fun h => (hI2_na z hz2).1 (Finset.mem_filter.mp h).2.symm
          have hz_notR : z ∉ R_set := (Finset.mem_filter.mp hz2).2.2
          have hz_notB : z ∉ Nbad := fun h => hz_notN (Finset.mem_filter.mp h).1
          have huz : ¬ H.Adj z u := fun h => hu_na_23.1 z hz2 h.symm
          have hwz : ¬ H.Adj z w := fun h => hw_na_12.2 z hz2 h.symm
          simp [hz_notN, hz_notR, hz_notB, (hv_I2 z hz2).symm, huz, hwz]
        · have hz_notN : z ∉ Nx := fun h => (hI3_na z hz3).1 (Finset.mem_filter.mp h).2.symm
          have hz_notR : z ∉ R_set := (Finset.mem_filter.mp hz3).2.2
          have hz_notB : z ∉ Nbad := fun h => hz_notN (Finset.mem_filter.mp h).1
          have huz : ¬ H.Adj z u := fun h => hu_na_23.2 z hz3 h.symm
          have hvz : ¬ H.Adj z v := fun h => hv_na_13.2 z hz3 h.symm
          simp [hz_notN, hz_notR, hz_notB, (hw_I3 z hz3).symm, huz, hvz]
      have hNx_w : wsum ω Nx = δ := by rw [← hreg x, wdeg, ← Finset.sum_filter]; rfl
      have hle_bad : 3 * δ ≤ 1 + δ - wsum ω R_set - wsum ω Nbad := calc
        3 * δ = ∑ z : U, (#(({u, v, w} : Finset U).filter (H.Adj z)) : ℝ) * ω z := hsum_uvw.symm
        _ ≤ ∑ z : U, (1 + (if z ∈ Nx then (1 : ℝ) else 0) - (if z ∈ R_set then (1 : ℝ) else 0) - (if z ∈ Nbad then (1 : ℝ) else 0)) * ω z :=
            Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_right (hcnt_uvw z) (hnn z))
        _ = 1 + wsum ω Nx - wsum ω R_set - wsum ω Nbad := by
            simp only [sub_mul, add_mul, one_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
              hsum]
            have hNw : (∑ z : U, if z ∈ Nx then ω z else 0) = wsum ω Nx := by simp [wsum]
            have hRw : (∑ z : U, if z ∈ R_set then ω z else 0) = wsum ω R_set := by simp [wsum]
            have hBw : (∑ z : U, if z ∈ Nbad then ω z else 0) = wsum ω Nbad := by simp [wsum]
            rw [hNw, hRw, hBw]
        _ = 1 + δ - wsum ω R_set - wsum ω Nbad := by rw [hNx_w]
      have hNbad_empty : Nbad = ∅ := by
        by_contra hne; obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hle : ω q ≤ wsum ω Nbad := Finset.single_le_sum (fun z _ => hnn z) hq
        linarith [hx_wmin q]
      intro p hp
      have hp_good : (H.Adj p u ∧ H.Adj p v) ∨ (H.Adj p v ∧ H.Adj p w) ∨ (H.Adj p w ∧ H.Adj p u) := by
        by_contra hbad; exact Finset.notMem_empty p (hNbad_empty ▸ Finset.mem_filter.mpr ⟨hp, hbad⟩)
      by_cases hu' : H.Adj p u <;> by_cases hv' : H.Adj p v <;> by_cases hw' : H.Adj p w
      · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hu', hv', hw'⟩)
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hp, hu', hv', hw'⟩)))
      · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hp, hu', hv', hw'⟩)))
      · exact absurd hp_good (fun h => by
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hv' h2
          · exact hv' h1
          · exact hw' h1)
      · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hp, hu', hv', hw'⟩))
      · exact absurd hp_good (fun h => by
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hu' h1
          · exact hw' h2
          · exact hu' h2)
      · exact absurd hp_good (fun h => by
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hu' h1
          · exact hv' h1
          · exact hu' h2)
      · exact absurd hp_good (fun h => by
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hu' h1
          · exact hv' h1
          · exact hw' h1)
    · -- Case Y = {y}: `exists_dom3_of_c6` kills any `p ∈ Nx` missing 2 of `{u, v, w}`!
      obtain ⟨y, hyY⟩ := Finset.nonempty_iff_ne_empty.mpr hY_empty
      have hyN := (Finset.mem_filter.mp hyY).1
      have hmiss2 : ∀ (p u1 u2 : U) (I_1 I_2 : Finset U), p ∈ Nx → u1 ∈ R_set → u2 ∈ R_set → u1 ≠ u2 →
          (∀ z ∈ I_1, H.Adj u1 z ∧ ¬ H.Adj u2 z ∧ z ∉ R_set ∧ z ∉ Nx) →
          (∀ z ∈ I_2, H.Adj u2 z ∧ ¬ H.Adj u1 z ∧ z ∉ R_set ∧ z ∉ Nx) →
          (∀ z : U, H.Adj p z → H.Adj u1 z → z ∈ I_1) →
          (∀ z : U, H.Adj p z → H.Adj u2 z → z ∈ I_2) →
          (∀ z : U, z ∉ Nx → z ∉ R_set → ¬ (H.Adj z u1 ∧ H.Adj z u2)) →
          (∀ r ∈ R_set, ¬ (∃ z1 ∈ I_1, ∃ z2 ∈ I_2, H.Adj r z1 ∧ H.Adj r z2)) →
          ¬ H.Adj p u1 → ¬ H.Adj p u2 → False := by
        intro p u1 u2 I_1 I_2 hp hu1R hu2R hne12 hI_1 hI_2 hcom1 hcom2 hno_out hno_R hna1 hna2
        have hp_ne_1 : p ≠ u1 := fun h => by
          subst h; exact hR_ind p hu1R x (Finset.mem_insert_self x _) (Finset.mem_filter.mp hp).2.symm
        have hp_ne_2 : p ≠ u2 := fun h => by
          subst h; exact hR_ind p hu2R x (Finset.mem_insert_self x _) (Finset.mem_filter.mp hp).2.symm
        obtain ⟨x0, hpx0, hu1x0⟩ := G.hMax p u1 hp_ne_1 hna1
        obtain ⟨y0, hpy0, hu2y0⟩ := G.hMax p u2 hp_ne_2 hna2
        have hx0_1 : x0 ∈ I_1 := hcom1 x0 hpx0 hu1x0
        have hy0_2 : y0 ∈ I_2 := hcom2 y0 hpy0 hu2y0
        have hp_ne_y : p ≠ y := fun h => hna1 (h ▸ (hY_nbhd y hyY u1).mpr hu1R)
        have hx0_ne_y0 : x0 ≠ y0 := fun h => (hI_1 x0 hx0_1).2.1 (h ▸ (hI_2 y0 hy0_2).1)
        have hdisj_RN : ∀ r ∈ R_set, ∀ n ∈ Nx, r ≠ n := fun r hr n hn h => by
          subst h; rcases eq_or_ne r x with rfl | hne
          · exact H.loopless.irrefl _ (Finset.mem_filter.mp hn).2
          · exact hR_ind r hr x (Finset.mem_insert_self x _) (Finset.mem_filter.mp hn).2.symm
        let cyc : Fin 6 → U := ![u1, x0, p, y0, u2, y]
        have hcyc_inj : Function.Injective cyc := by
          intro i j hij; fin_cases i <;> fin_cases j <;> dsimp [cyc] at hij ⊢
          all_goals first | rfl | exact (hne12 hij).elim | exact (hne12 hij.symm).elim
                          | exact (hp_ne_y hij).elim | exact (hp_ne_y hij.symm).elim
                          | exact (hx0_ne_y0 hij).elim | exact (hx0_ne_y0 hij.symm).elim
                          | exact (hdisj_RN _ hu1R _ hp hij).elim | exact (hdisj_RN _ hu1R _ hp hij.symm).elim
                          | exact (hdisj_RN _ hu1R _ hyN hij).elim | exact (hdisj_RN _ hu1R _ hyN hij.symm).elim
                          | exact (hdisj_RN _ hu2R _ hp hij).elim | exact (hdisj_RN _ hu2R _ hp hij.symm).elim
                          | exact (hdisj_RN _ hu2R _ hyN hij).elim | exact (hdisj_RN _ hu2R _ hyN hij.symm).elim
                          | exact ((hI_1 x0 hx0_1).2.2.1 (hij ▸ hu1R)).elim | exact ((hI_1 x0 hx0_1).2.2.1 (hij.symm ▸ hu1R)).elim
                          | exact ((hI_1 x0 hx0_1).2.2.1 (hij ▸ hu2R)).elim | exact ((hI_1 x0 hx0_1).2.2.1 (hij.symm ▸ hu2R)).elim
                          | exact ((hI_2 y0 hy0_2).2.2.1 (hij ▸ hu1R)).elim | exact ((hI_2 y0 hy0_2).2.2.1 (hij.symm ▸ hu1R)).elim
                          | exact ((hI_2 y0 hy0_2).2.2.1 (hij ▸ hu2R)).elim | exact ((hI_2 y0 hy0_2).2.2.1 (hij.symm ▸ hu2R)).elim
                          | exact ((hI_1 x0 hx0_1).2.2.2 (hij ▸ hp)).elim | exact ((hI_1 x0 hx0_1).2.2.2 (hij.symm ▸ hp)).elim
                          | exact ((hI_1 x0 hx0_1).2.2.2 (hij ▸ hyN)).elim | exact ((hI_1 x0 hx0_1).2.2.2 (hij.symm ▸ hyN)).elim
                          | exact ((hI_2 y0 hy0_2).2.2.2 (hij ▸ hp)).elim | exact ((hI_2 y0 hy0_2).2.2.2 (hij.symm ▸ hp)).elim
                          | exact ((hI_2 y0 hy0_2).2.2.2 (hij ▸ hyN)).elim
        obtain ⟨z, hz⟩ := exists_dom3_of_c6 H G.hTF hnn hsum hdeg cyc hcyc_inj
          hu1x0 hpx0.symm hpy0 hu2y0.symm ((hY_nbhd y hyY u2).mpr hu2R).symm ((hY_nbhd y hyY u1).mpr hu1R)
        rcases hz with ⟨h0, h2, h4⟩ | ⟨h1, h3, h5⟩
        · exact hno_out z (fun h => hNx_ind z h p hp h2) (fun h => hR_ind z h u1 hu1R h0) ⟨h0, h4⟩
        · exact hno_R z ((hY_nbhd y hyY z).mp h5.symm) ⟨x0, hx0_1, y0, hy0_2, h1, h3⟩
      have hne_uv : u ≠ v := fun h => (hnot_abc u (Finset.mem_filter.mp huU).2.1)
        ⟨h ▸ (Finset.mem_filter.mp hvV).2.2.1, (Finset.mem_filter.mp huU).2.2.1, (Finset.mem_filter.mp huU).2.2.2⟩
      have hne_uw : u ≠ w := fun h => (hnot_abc u (Finset.mem_filter.mp huU).2.1)
        ⟨h ▸ (Finset.mem_filter.mp hwW).2.2.1, (Finset.mem_filter.mp huU).2.2.1, (Finset.mem_filter.mp huU).2.2.2⟩
      have hne_vw : v ≠ w := fun h => (hnot_abc v (Finset.mem_filter.mp hvV).2.1)
        ⟨(Finset.mem_filter.mp hvV).2.2.1, h ▸ (Finset.mem_filter.mp hwW).2.2.2, (Finset.mem_filter.mp hvV).2.2.2⟩
      have hcom_u : ∀ p ∈ Nx, ∀ z : U, H.Adj p z → H.Adj u z → z ∈ I1 := fun p hp z hpz huz => by
        rcases hpart z with h | h | h | h | h
        · exact (hNx_ind p hp z h hpz).elim
        · exact (hR_ind u huR z h huz).elim
        · exact h
        · exact (hu_na_23.1 z h huz).elim
        · exact (hu_na_23.2 z h huz).elim
      have hcom_v : ∀ p ∈ Nx, ∀ z : U, H.Adj p z → H.Adj v z → z ∈ I2 := fun p hp z hpz hvz => by
        rcases hpart z with h | h | h | h | h
        · exact (hNx_ind p hp z h hpz).elim
        · exact (hR_ind v hvR z h hvz).elim
        · exact (hv_na_13.1 z h hvz).elim
        · exact h
        · exact (hv_na_13.2 z h hvz).elim
      have hcom_w : ∀ p ∈ Nx, ∀ z : U, H.Adj p z → H.Adj w z → z ∈ I3 := fun p hp z hpz hwz => by
        rcases hpart z with h | h | h | h | h
        · exact (hNx_ind p hp z h hpz).elim
        · exact (hR_ind w hwR z h hwz).elim
        · exact (hw_na_12.1 z h hwz).elim
        · exact (hw_na_12.2 z h hwz).elim
        · exact h
      have hnoR_12 : ∀ r ∈ R_set, ¬ (∃ z1 ∈ I1, ∃ z2 ∈ I2, H.Adj r z1 ∧ H.Adj r z2) := by
        rintro r hr ⟨z1, hz1, z2, hz2, h1, h2⟩
        simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        rcases hr with rfl | ((⟨_, hrb, _⟩ | ⟨_, hra, _⟩) | ⟨_, hra, _⟩)
        · exact (hI1_na z1 hz1).1 h1.symm
        · exact tf_contra G.hTF h2 (Finset.mem_filter.mp hz2).2.1 hrb
        · exact tf_contra G.hTF h1 (Finset.mem_filter.mp hz1).2.1 hra
        · exact tf_contra G.hTF h1 (Finset.mem_filter.mp hz1).2.1 hra
      have hnoR_13 : ∀ r ∈ R_set, ¬ (∃ z1 ∈ I1, ∃ z3 ∈ I3, H.Adj r z1 ∧ H.Adj r z3) := by
        rintro r hr ⟨z1, hz1, z3, hz3, h1, h3⟩
        simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        rcases hr with rfl | ((⟨_, _, hrc⟩ | ⟨_, hra, _⟩) | ⟨_, hra, _⟩)
        · exact (hI1_na z1 hz1).1 h1.symm
        · exact tf_contra G.hTF h3 (Finset.mem_filter.mp hz3).2.1 hrc
        · exact tf_contra G.hTF h1 (Finset.mem_filter.mp hz1).2.1 hra
        · exact tf_contra G.hTF h1 (Finset.mem_filter.mp hz1).2.1 hra
      have hnoR_23 : ∀ r ∈ R_set, ¬ (∃ z2 ∈ I2, ∃ z3 ∈ I3, H.Adj r z2 ∧ H.Adj r z3) := by
        rintro r hr ⟨z2, hz2, z3, hz3, h2, h3⟩
        simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        rcases hr with rfl | ((⟨_, hrb, _⟩ | ⟨_, _, hrc⟩) | ⟨_, _, hrb⟩)
        · exact (hI2_na z2 hz2).1 h2.symm
        · exact tf_contra G.hTF h2 (Finset.mem_filter.mp hz2).2.1 hrb
        · exact tf_contra G.hTF h3 (Finset.mem_filter.mp hz3).2.1 hrc
        · exact tf_contra G.hTF h2 (Finset.mem_filter.mp hz2).2.1 hrb
      intro p hp
      by_cases hu' : H.Adj p u <;> by_cases hv' : H.Adj p v <;> by_cases hw' : H.Adj p w
      · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hu', hv', hw'⟩)
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hp, hu', hv', hw'⟩)))
      · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hp, hu', hv', hw'⟩)))
      · exfalso; exact hmiss2 p v w I2 I3 hp hvR hwR hne_vw
          (fun z hz => ⟨hv_I2 z hz, hw_na_12.2 z hz, (Finset.mem_filter.mp hz).2.2, fun h => (hI2_na z hz).1 (Finset.mem_filter.mp h).2.symm⟩)
          (fun z hz => ⟨hw_I3 z hz, hv_na_13.2 z hz, (Finset.mem_filter.mp hz).2.2, fun h => (hI3_na z hz).1 (Finset.mem_filter.mp h).2.symm⟩)
          (hcom_v p hp) (hcom_w p hp)
          (fun z hN hR ⟨h1, h2⟩ => by rcases hpart z with h | h | h | h | h <;> [exact hN h; exact hR h; exact hv_na_13.1 z h h1.symm; exact hw_na_12.2 z h h2.symm; exact hv_na_13.2 z h h1.symm])
          hnoR_23 hv' hw'
      · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hp, hu', hv', hw'⟩))
      · exfalso; exact hmiss2 p u w I1 I3 hp huR hwR hne_uw
          (fun z hz => ⟨hu_I1 z hz, hw_na_12.1 z hz, (Finset.mem_filter.mp hz).2.2, fun h => (hI1_na z hz).1 (Finset.mem_filter.mp h).2.symm⟩)
          (fun z hz => ⟨hw_I3 z hz, hu_na_23.2 z hz, (Finset.mem_filter.mp hz).2.2, fun h => (hI3_na z hz).1 (Finset.mem_filter.mp h).2.symm⟩)
          (hcom_u p hp) (hcom_w p hp)
          (fun z hN hR ⟨h1, h2⟩ => by rcases hpart z with h | h | h | h | h <;> [exact hN h; exact hR h; exact hw_na_12.1 z h h2.symm; exact hu_na_23.1 z h h1.symm; exact hu_na_23.2 z h h1.symm])
          hnoR_13 hu' hw'
      · exfalso; exact hmiss2 p u v I1 I2 hp huR hvR hne_uv
          (fun z hz => ⟨hu_I1 z hz, hv_na_13.1 z hz, (Finset.mem_filter.mp hz).2.2, fun h => (hI1_na z hz).1 (Finset.mem_filter.mp h).2.symm⟩)
          (fun z hz => ⟨hv_I2 z hz, hu_na_23.1 z hz, (Finset.mem_filter.mp hz).2.2, fun h => (hI2_na z hz).1 (Finset.mem_filter.mp h).2.symm⟩)
          (hcom_u p hp) (hcom_v p hp)
          (fun z hN hR ⟨h1, h2⟩ => by rcases hpart z with h | h | h | h | h <;> [exact hN h; exact hR h; exact hv_na_13.1 z h h2.symm; exact hu_na_23.1 z h h1.symm; exact hu_na_23.2 z h h1.symm])
          hnoR_12 hu' hv'
      · exfalso; exact hmiss2 p u v I1 I2 hp huR hvR hne_uv
          (fun z hz => ⟨hu_I1 z hz, hv_na_13.1 z hz, (Finset.mem_filter.mp hz).2.2, fun h => (hI1_na z hz).1 (Finset.mem_filter.mp h).2.symm⟩)
          (fun z hz => ⟨hv_I2 z hz, hu_na_23.1 z hz, (Finset.mem_filter.mp hz).2.2, fun h => (hI2_na z hz).1 (Finset.mem_filter.mp h).2.symm⟩)
          (hcom_u p hp) (hcom_v p hp)
          (fun z hN hR ⟨h1, h2⟩ => by rcases hpart z with h | h | h | h | h <;> [exact hN h; exact hR h; exact hv_na_13.1 z h h2.symm; exact hu_na_23.1 z h h1.symm; exact hu_na_23.2 z h h1.symm])
          hnoR_12 hu' hv'
  -- Claims 8-11: Exact Bipartite Completeness & Weight Equations
  have haA : a ∈ A_set := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax⟩,
    fun h => hnot_abc u (Finset.mem_filter.mp huU).2.1 ⟨h.symm, (Finset.mem_filter.mp huU).2.2⟩,
    (Finset.mem_filter.mp hvV).2.2.1.symm, (Finset.mem_filter.mp hwW).2.2.1.symm⟩
  have hbB : b ∈ B_set := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx⟩,
    (Finset.mem_filter.mp huU).2.2.1.symm,
    fun h => hnot_abc v (Finset.mem_filter.mp hvV).2.1 ⟨(Finset.mem_filter.mp hvV).2.2.1, h.symm, (Finset.mem_filter.mp hvV).2.2.2⟩,
    (Finset.mem_filter.mp hwW).2.2.2.symm⟩
  have hcC : c ∈ C_set := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcx⟩,
    (Finset.mem_filter.mp huU).2.2.2.symm, (Finset.mem_filter.mp hvV).2.2.2.symm,
    fun h => hnot_abc w (Finset.mem_filter.mp hwW).2.1 ⟨(Finset.mem_filter.mp hwW).2.2.1, (Finset.mem_filter.mp hwW).2.2.2, h.symm⟩⟩
  have hA_VW : ∀ p ∈ A_set, (∀ v' ∈ V_set, H.Adj p v') ∧ (∀ w' ∈ W_set, H.Adj p w') := fun p hp =>
    ⟨hv_cl4 p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2.2.1.symm,
     hw_cl4 p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2.2.2.symm⟩
  have hB_UW : ∀ p ∈ B_set, (∀ u' ∈ U_set, H.Adj p u') ∧ (∀ w' ∈ W_set, H.Adj p w') := fun p hp =>
    ⟨hu_cl4 p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2.1.symm,
     hw_cl4 p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2.2.2.symm⟩
  have hC_UV : ∀ p ∈ C_set, (∀ u' ∈ U_set, H.Adj p u') ∧ (∀ v' ∈ V_set, H.Adj p v') := fun p hp =>
    ⟨hu_cl4 p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2.1.symm,
     hv_cl4 p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2.2.1.symm⟩
  have hI1_avoid : ∀ z ∈ I1, (∀ p ∈ Y_set ∪ B_set ∪ C_set, ¬ H.Adj z p) ∧ (∀ r ∈ insert x (V_set ∪ W_set), ¬ H.Adj z r) := by
    intro z hz; refine ⟨fun p hp h => ?_, fun r hr h => ?_⟩
    · simp only [Finset.mem_union] at hp
      rcases hp with (hpY | hpB) | hpC
      · exact tf_contra G.hTF (hu_I1 z hz) h (Finset.mem_filter.mp hpY).2.1.symm
      · exact tf_contra G.hTF (hu_I1 z hz) h (Finset.mem_filter.mp hpB).2.1.symm
      · exact tf_contra G.hTF (hu_I1 z hz) h (Finset.mem_filter.mp hpC).2.1.symm
    · simp only [Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | hrV | hrW
      · exact (hI1_na z hz).1 h
      · exact tf_contra G.hTF h (Finset.mem_filter.mp hrV).2.2.1 (Finset.mem_filter.mp hz).2.1
      · exact tf_contra G.hTF h (Finset.mem_filter.mp hrW).2.2.1 (Finset.mem_filter.mp hz).2.1
  have hI2_avoid : ∀ z ∈ I2, (∀ p ∈ Y_set ∪ A_set ∪ C_set, ¬ H.Adj z p) ∧ (∀ r ∈ insert x (U_set ∪ W_set), ¬ H.Adj z r) := by
    intro z hz; refine ⟨fun p hp h => ?_, fun r hr h => ?_⟩
    · simp only [Finset.mem_union] at hp
      rcases hp with (hpY | hpA) | hpC
      · exact tf_contra G.hTF (hv_I2 z hz) h (Finset.mem_filter.mp hpY).2.2.1.symm
      · exact tf_contra G.hTF (hv_I2 z hz) h (Finset.mem_filter.mp hpA).2.2.1.symm
      · exact tf_contra G.hTF (hv_I2 z hz) h (Finset.mem_filter.mp hpC).2.2.1.symm
    · simp only [Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | hrU | hrW
      · exact (hI2_na z hz).1 h
      · exact tf_contra G.hTF h (Finset.mem_filter.mp hrU).2.2.1 (Finset.mem_filter.mp hz).2.1
      · exact tf_contra G.hTF h (Finset.mem_filter.mp hrW).2.2.2 (Finset.mem_filter.mp hz).2.1
  have hI3_avoid : ∀ z ∈ I3, (∀ p ∈ Y_set ∪ A_set ∪ B_set, ¬ H.Adj z p) ∧ (∀ r ∈ insert x (U_set ∪ V_set), ¬ H.Adj z r) := by
    intro z hz; refine ⟨fun p hp h => ?_, fun r hr h => ?_⟩
    · simp only [Finset.mem_union] at hp
      rcases hp with (hpY | hpA) | hpB
      · exact tf_contra G.hTF (hw_I3 z hz) h (Finset.mem_filter.mp hpY).2.2.2.symm
      · exact tf_contra G.hTF (hw_I3 z hz) h (Finset.mem_filter.mp hpA).2.2.2.symm
      · exact tf_contra G.hTF (hw_I3 z hz) h (Finset.mem_filter.mp hpB).2.2.2.symm
    · simp only [Finset.mem_insert, Finset.mem_union] at hr
      rcases hr with rfl | hrU | hrV
      · exact (hI3_na z hz).1 h
      · exact tf_contra G.hTF h (Finset.mem_filter.mp hrU).2.2.2 (Finset.mem_filter.mp hz).2.1
      · exact tf_contra G.hTF h (Finset.mem_filter.mp hrV).2.2.2 (Finset.mem_filter.mp hz).2.1
  -- Exact weight sums for Nx, R, and `wdeg a..w`
  have hw_Nx : wsum ω Y_set + wsum ω A_set + wsum ω B_set + wsum ω C_set = δ := by
    have hdisj : Nx = Y_set ∪ A_set ∪ B_set ∪ C_set := by
      ext z; simp only [Finset.mem_union]; constructor
      · intro hz; rcases hNx_part z hz with h | h | h | h <;> simp [h]
      · rintro (((h | h) | h) | h) <;> exact (Finset.mem_filter.mp h).1
    have h1 : wsum ω Nx = δ := by rw [← hreg x, wdeg, ← Finset.sum_filter]; rfl
    have hdYA : Disjoint Y_set A_set := Finset.disjoint_left.mpr fun z hY hA =>
      (Finset.mem_filter.mp hA).2.1 (Finset.mem_filter.mp hY).2.1
    have hdYAB : Disjoint (Y_set ∪ A_set) B_set := Finset.disjoint_left.mpr fun z hYA hB => by
      rcases Finset.mem_union.mp hYA with hY | hA
      · exact (Finset.mem_filter.mp hB).2.2.1 (Finset.mem_filter.mp hY).2.2.1
      · exact (Finset.mem_filter.mp hA).2.1 (Finset.mem_filter.mp hB).2.1
    have hdYABC : Disjoint (Y_set ∪ A_set ∪ B_set) C_set := Finset.disjoint_left.mpr fun z hYAB hC => by
      rcases Finset.mem_union.mp hYAB with hYA | hB
      · rcases Finset.mem_union.mp hYA with hY | hA
        · exact (Finset.mem_filter.mp hC).2.2.2 (Finset.mem_filter.mp hY).2.2.2
        · exact (Finset.mem_filter.mp hA).2.1 (Finset.mem_filter.mp hC).2.1
      · exact (Finset.mem_filter.mp hB).2.2.1 (Finset.mem_filter.mp hC).2.2.1
    rw [← h1, hdisj]; simp only [wsum]
    rw [Finset.sum_union hdYABC, Finset.sum_union hdYAB, Finset.sum_union hdYA]
  have hw_R_sum : ω x + wsum ω U_set + wsum ω V_set + wsum ω W_set = 4 * δ - 1 - ω x := by
    have hdUV : Disjoint U_set V_set := Finset.disjoint_left.mpr fun z hU hV =>
      hnot_abc z (Finset.mem_filter.mp hU).2.1 ⟨(Finset.mem_filter.mp hV).2.2.1, (Finset.mem_filter.mp hU).2.2⟩
    have hdUVW : Disjoint (U_set ∪ V_set) W_set := Finset.disjoint_left.mpr fun z hUV hW => by
      rcases Finset.mem_union.mp hUV with hU | hV
      · exact hnot_abc z (Finset.mem_filter.mp hU).2.1 ⟨(Finset.mem_filter.mp hW).2.2.1, (Finset.mem_filter.mp hU).2.2⟩
      · exact hnot_abc z (Finset.mem_filter.mp hV).2.1
          ⟨(Finset.mem_filter.mp hV).2.2.1, (Finset.mem_filter.mp hW).2.2.2, (Finset.mem_filter.mp hV).2.2.2⟩
    have hxnotUVW : x ∉ U_set ∪ V_set ∪ W_set := by simp [U_set, V_set, W_set]
    rw [← hwRval]
    have hRins : R_set = insert x (U_set ∪ V_set ∪ W_set) := rfl
    rw [hRins]; simp only [wsum]
    rw [Finset.sum_insert hxnotUVW, Finset.sum_union hdUVW]
    have hdUV' : Disjoint U_set V_set := hdUV
    rw [Finset.sum_union hdUV']
    ring
  -- Exact neighborhood equations for `a, b, c, u, v, w`
  have hw_deg_a : ω x + wsum ω V_set + wsum ω W_set + wsum ω I1 = δ := by
    have hN : Finset.univ.filter (H.Adj a) = insert x (V_set ∪ W_set) ∪ I1 := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_insert]; constructor
      · intro haz
        by_cases hzx : z = x
        · exact Or.inl (Or.inl hzx)
        · by_cases hzR : z ∈ R_set
          · simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hzR
            rcases hzR with rfl | ((⟨_, hzb, hzc⟩ | hV) | hW)
            · exact (hzx rfl).elim
            · exact (hnot_abc z hzx ⟨haz.symm, hzb, hzc⟩).elim
            · exact Or.inl (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV⟩)))
            · exact Or.inl (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW⟩)))
          · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, haz.symm, hzR⟩)
      · rintro ((rfl | hV | hW) | hI)
        · exact hax.symm
        · exact (Finset.mem_filter.mp hV).2.2.1.symm
        · exact (Finset.mem_filter.mp hW).2.2.1.symm
        · exact (Finset.mem_filter.mp hI).2.1.symm
    have h1 : wsum ω (Finset.univ.filter (H.Adj a)) = δ := by rw [← hreg a, wdeg, ← Finset.sum_filter]; rfl
    have hd1 : Disjoint (insert x (V_set ∪ W_set)) I1 := Finset.disjoint_left.mpr fun z hR hI => (Finset.mem_filter.mp hI).2.2 (by
        simp only [Finset.mem_insert, Finset.mem_union] at hR
        rcases hR with hzx | hV | hW
        · rw [hzx]; exact Finset.mem_insert_self x _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hV))
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hW))
    have hd2 : x ∉ V_set ∪ W_set := by simp [V_set, W_set]
    have hd3 : Disjoint V_set W_set := Finset.disjoint_left.mpr fun z hV hW =>
        hnot_abc z (Finset.mem_filter.mp hV).2.1 ⟨(Finset.mem_filter.mp hV).2.2.1, (Finset.mem_filter.mp hW).2.2.2, (Finset.mem_filter.mp hV).2.2.2⟩
    rw [← h1, hN]; simp only [wsum]
    rw [Finset.sum_union hd1, Finset.sum_insert hd2, Finset.sum_union hd3]
    ring
  have hw_deg_b : ω x + wsum ω U_set + wsum ω W_set + wsum ω I2 = δ := by
    have hN : Finset.univ.filter (H.Adj b) = insert x (U_set ∪ W_set) ∪ I2 := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_insert]; constructor
      · intro hbz
        by_cases hzx : z = x
        · exact Or.inl (Or.inl hzx)
        · by_cases hzR : z ∈ R_set
          · simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hzR
            rcases hzR with rfl | ((hU | ⟨_, hza, hzc⟩) | hW)
            · exact (hzx rfl).elim
            · exact Or.inl (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩)))
            · exact (hnot_abc z hzx ⟨hza, hbz.symm, hzc⟩).elim
            · exact Or.inl (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW⟩)))
          · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbz.symm, hzR⟩)
      · rintro ((rfl | hU | hW) | hI)
        · exact hbx.symm
        · exact (Finset.mem_filter.mp hU).2.2.1.symm
        · exact (Finset.mem_filter.mp hW).2.2.2.symm
        · exact (Finset.mem_filter.mp hI).2.1.symm
    have h1 : wsum ω (Finset.univ.filter (H.Adj b)) = δ := by rw [← hreg b, wdeg, ← Finset.sum_filter]; rfl
    have hd1 : Disjoint (insert x (U_set ∪ W_set)) I2 := Finset.disjoint_left.mpr fun z hR hI => (Finset.mem_filter.mp hI).2.2 (by
        simp only [Finset.mem_insert, Finset.mem_union] at hR
        rcases hR with hzx | hU | hW
        · rw [hzx]; exact Finset.mem_insert_self x _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hU))
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hW))
    have hd2 : x ∉ U_set ∪ W_set := by simp [U_set, W_set]
    have hd3 : Disjoint U_set W_set := Finset.disjoint_left.mpr fun z hU hW =>
        hnot_abc z (Finset.mem_filter.mp hU).2.1 ⟨(Finset.mem_filter.mp hW).2.2.1, (Finset.mem_filter.mp hU).2.2⟩
    rw [← h1, hN]; simp only [wsum]
    rw [Finset.sum_union hd1, Finset.sum_insert hd2, Finset.sum_union hd3]
    ring
  have hw_deg_c : ω x + wsum ω U_set + wsum ω V_set + wsum ω I3 = δ := by
    have hN : Finset.univ.filter (H.Adj c) = insert x (U_set ∪ V_set) ∪ I3 := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_insert]; constructor
      · intro hcz
        by_cases hzx : z = x
        · exact Or.inl (Or.inl hzx)
        · by_cases hzR : z ∈ R_set
          · simp only [R_set, U_set, V_set, W_set, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hzR
            rcases hzR with rfl | ((hU | hV) | ⟨_, hza, hzb⟩)
            · exact (hzx rfl).elim
            · exact Or.inl (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩)))
            · exact Or.inl (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV⟩)))
            · exact (hnot_abc z hzx ⟨hza, hzb, hcz.symm⟩).elim
          · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcz.symm, hzR⟩)
      · rintro ((rfl | hU | hV) | hI)
        · exact hcx.symm
        · exact (Finset.mem_filter.mp hU).2.2.2.symm
        · exact (Finset.mem_filter.mp hV).2.2.2.symm
        · exact (Finset.mem_filter.mp hI).2.1.symm
    have h1 : wsum ω (Finset.univ.filter (H.Adj c)) = δ := by rw [← hreg c, wdeg, ← Finset.sum_filter]; rfl
    have hd1 : Disjoint (insert x (U_set ∪ V_set)) I3 := Finset.disjoint_left.mpr fun z hR hI => (Finset.mem_filter.mp hI).2.2 (by
        simp only [Finset.mem_insert, Finset.mem_union] at hR
        rcases hR with hzx | hU | hV
        · rw [hzx]; exact Finset.mem_insert_self x _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hU))
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hV)))
    have hd2 : x ∉ U_set ∪ V_set := by simp [U_set, V_set]
    have hd3 : Disjoint U_set V_set := Finset.disjoint_left.mpr fun z hU hV =>
        hnot_abc z (Finset.mem_filter.mp hU).2.1 ⟨(Finset.mem_filter.mp hV).2.2.1, (Finset.mem_filter.mp hU).2.2⟩
    rw [← h1, hN]; simp only [wsum]
    rw [Finset.sum_union hd1, Finset.sum_insert hd2, Finset.sum_union hd3]
    ring
  have hw_deg_u : wsum ω Y_set + wsum ω B_set + wsum ω C_set + wsum ω I1 = δ := by
    have hN : Finset.univ.filter (H.Adj u) = (Y_set ∪ B_set ∪ C_set) ∪ I1 := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; constructor
      · intro huz
        rcases hpart z with hzN | hzR | hz1 | hz2 | hz3
        · rcases hNx_part z hzN with hY | hA | hB | hC
          · exact Or.inl (Or.inl (Or.inl hY))
          · exact ((Finset.mem_filter.mp hA).2.1 huz.symm).elim
          · exact Or.inl (Or.inl (Or.inr hB))
          · exact Or.inl (Or.inr hC)
        · exact (hR_ind u huR z hzR huz).elim
        · exact Or.inr hz1
        · exact (hu_na_23.1 z hz2 huz).elim
        · exact (hu_na_23.2 z hz3 huz).elim
      · rintro (((hY | hB) | hC) | h1)
        · exact (Finset.mem_filter.mp hY).2.1.symm
        · exact (Finset.mem_filter.mp hB).2.1.symm
        · exact (Finset.mem_filter.mp hC).2.1.symm
        · exact hu_I1 z h1
    have h1 : wsum ω (Finset.univ.filter (H.Adj u)) = δ := by rw [← hreg u, wdeg, ← Finset.sum_filter]; rfl
    have hd1 : Disjoint (Y_set ∪ B_set ∪ C_set) I1 := Finset.disjoint_left.mpr fun z hN' h1 =>
      have hzNx : z ∈ Nx := by
        rcases Finset.mem_union.mp hN' with hS1 | hC
        · rcases Finset.mem_union.mp hS1 with hY | hB
          · exact (Finset.mem_filter.mp hY).1
          · exact (Finset.mem_filter.mp hB).1
        · exact (Finset.mem_filter.mp hC).1
      (hI1_na z h1).1 (Finset.mem_filter.mp hzNx).2.symm
    have hd2 : Disjoint (Y_set ∪ B_set) C_set := Finset.disjoint_left.mpr fun z hYB hC => by
        rcases Finset.mem_union.mp hYB with hY | hB
        · exact (Finset.mem_filter.mp hC).2.2.2 (Finset.mem_filter.mp hY).2.2.2
        · exact (Finset.mem_filter.mp hB).2.2.1 (Finset.mem_filter.mp hC).2.2.1
    have hd3 : Disjoint Y_set B_set := Finset.disjoint_left.mpr fun z hY hB => (Finset.mem_filter.mp hB).2.2.1 (Finset.mem_filter.mp hY).2.2.1
    rw [← h1, hN]; simp only [wsum]
    rw [Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_union hd3]
  have hw_deg_v : wsum ω Y_set + wsum ω A_set + wsum ω C_set + wsum ω I2 = δ := by
    have hN : Finset.univ.filter (H.Adj v) = (Y_set ∪ A_set ∪ C_set) ∪ I2 := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; constructor
      · intro hvz
        rcases hpart z with hzN | hzR | hz1 | hz2 | hz3
        · rcases hNx_part z hzN with hY | hA | hB | hC
          · exact Or.inl (Or.inl (Or.inl hY))
          · exact Or.inl (Or.inl (Or.inr hA))
          · exact ((Finset.mem_filter.mp hB).2.2.1 hvz.symm).elim
          · exact Or.inl (Or.inr hC)
        · exact (hR_ind v hvR z hzR hvz).elim
        · exact (hv_na_13.1 z hz1 hvz).elim
        · exact Or.inr hz2
        · exact (hv_na_13.2 z hz3 hvz).elim
      · rintro (((hY | hA) | hC) | h2)
        · exact (Finset.mem_filter.mp hY).2.2.1.symm
        · exact (Finset.mem_filter.mp hA).2.2.1.symm
        · exact (Finset.mem_filter.mp hC).2.2.1.symm
        · exact hv_I2 z h2
    have h1 : wsum ω (Finset.univ.filter (H.Adj v)) = δ := by rw [← hreg v, wdeg, ← Finset.sum_filter]; rfl
    have hd1 : Disjoint (Y_set ∪ A_set ∪ C_set) I2 := Finset.disjoint_left.mpr fun z hN' h2 =>
      have hzNx : z ∈ Nx := by
        rcases Finset.mem_union.mp hN' with hS1 | hC
        · rcases Finset.mem_union.mp hS1 with hY | hA
          · exact (Finset.mem_filter.mp hY).1
          · exact (Finset.mem_filter.mp hA).1
        · exact (Finset.mem_filter.mp hC).1
      (hI2_na z h2).1 (Finset.mem_filter.mp hzNx).2.symm
    have hd2 : Disjoint (Y_set ∪ A_set) C_set := Finset.disjoint_left.mpr fun z hYA hC => by
        rcases Finset.mem_union.mp hYA with hY | hA
        · exact (Finset.mem_filter.mp hC).2.2.2 (Finset.mem_filter.mp hY).2.2.2
        · exact (Finset.mem_filter.mp hA).2.1 (Finset.mem_filter.mp hC).2.1
    have hd3 : Disjoint Y_set A_set := Finset.disjoint_left.mpr fun z hY hA => (Finset.mem_filter.mp hA).2.1 (Finset.mem_filter.mp hY).2.1
    rw [← h1, hN]; simp only [wsum]
    rw [Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_union hd3]
  have hw_deg_w : wsum ω Y_set + wsum ω A_set + wsum ω B_set + wsum ω I3 = δ := by
    have hN : Finset.univ.filter (H.Adj w) = (Y_set ∪ A_set ∪ B_set) ∪ I3 := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; constructor
      · intro hwz
        rcases hpart z with hzN | hzR | hz1 | hz2 | hz3
        · rcases hNx_part z hzN with hY | hA | hB | hC
          · exact Or.inl (Or.inl (Or.inl hY))
          · exact Or.inl (Or.inl (Or.inr hA))
          · exact Or.inl (Or.inr hB)
          · exact ((Finset.mem_filter.mp hC).2.2.2 hwz.symm).elim
        · exact (hR_ind w hwR z hzR hwz).elim
        · exact (hw_na_12.1 z hz1 hwz).elim
        · exact (hw_na_12.2 z hz2 hwz).elim
        · exact Or.inr hz3
      · rintro (((hY | hA) | hB) | h3)
        · exact (Finset.mem_filter.mp hY).2.2.2.symm
        · exact (Finset.mem_filter.mp hA).2.2.2.symm
        · exact (Finset.mem_filter.mp hB).2.2.2.symm
        · exact hw_I3 z h3
    have h1 : wsum ω (Finset.univ.filter (H.Adj w)) = δ := by rw [← hreg w, wdeg, ← Finset.sum_filter]; rfl
    have hd1 : Disjoint (Y_set ∪ A_set ∪ B_set) I3 := Finset.disjoint_left.mpr fun z hN' h3 =>
      have hzNx : z ∈ Nx := by
        rcases Finset.mem_union.mp hN' with hS1 | hB
        · rcases Finset.mem_union.mp hS1 with hY | hA
          · exact (Finset.mem_filter.mp hY).1
          · exact (Finset.mem_filter.mp hA).1
        · exact (Finset.mem_filter.mp hB).1
      (hI3_na z h3).1 (Finset.mem_filter.mp hzNx).2.symm
    have hd2 : Disjoint (Y_set ∪ A_set) B_set := Finset.disjoint_left.mpr fun z hYA hB => by
        rcases Finset.mem_union.mp hYA with hY | hA
        · exact (Finset.mem_filter.mp hB).2.2.1 (Finset.mem_filter.mp hY).2.2.1
        · exact (Finset.mem_filter.mp hA).2.1 (Finset.mem_filter.mp hB).2.1
    have hd3 : Disjoint Y_set A_set := Finset.disjoint_left.mpr fun z hY hA => (Finset.mem_filter.mp hA).2.1 (Finset.mem_filter.mp hY).2.1
    rw [← h1, hN]; simp only [wsum]
    rw [Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_union hd3]  -- Derived exact weight equalities
  have hw_AI1 : wsum ω A_set = wsum ω I1 := by linarith
  have hw_BI2 : wsum ω B_set = wsum ω I2 := by linarith
  have hw_CI3 : wsum ω C_set = wsum ω I3 := by linarith
  have hw_xY : ω x + wsum ω Y_set = 6 * δ - 2 := by
    have hsum_I : wsum ω I1 + wsum ω I2 + wsum ω I3 = 1 - δ - (4 * δ - 1 - ω x) := by
      have htot : (Finset.univ : Finset U) = Nx ∪ R_set ∪ I1 ∪ I2 ∪ I3 := by
        ext z; simp only [Finset.mem_univ, Finset.mem_union, true_iff]
        rcases hpart z with h | h | h | h | h <;> simp [h]
      have hdisj_NR : Disjoint Nx R_set := Finset.disjoint_left.mpr fun z hN hR => by
        rcases eq_or_ne z x with rfl | hne
        · exact H.loopless.irrefl _ (Finset.mem_filter.mp hN).2
        · exact hR_ind z hR x (Finset.mem_insert_self x _) (Finset.mem_filter.mp hN).2.symm
      have h1 : (1 : ℝ) = wsum ω Nx + wsum ω R_set + wsum ω I1 + wsum ω I2 + wsum ω I3 := by
        rw [← hsum, ← wsum, htot, wsum, Finset.sum_union, Finset.sum_union, Finset.sum_union, Finset.sum_union]
        · rfl
        · exact hdisj_NR
        · exact Finset.disjoint_left.mpr fun z hNR h1 => by
            rcases Finset.mem_union.mp hNR with hN | hR
            · exact (hI1_na z h1).1 (Finset.mem_filter.mp hN).2.symm
            · exact (Finset.mem_filter.mp h1).2.2 hR
        · exact Finset.disjoint_left.mpr fun z h12 h2 => by
            rcases Finset.mem_union.mp h12 with hNR | h1
            · rcases Finset.mem_union.mp hNR with hN | hR
              · exact (hI2_na z h2).1 (Finset.mem_filter.mp hN).2.symm
              · exact (Finset.mem_filter.mp h2).2.2 hR
            · exact (hI2_na z h2).2.1 (Finset.mem_filter.mp h1).2.1
        · exact Finset.disjoint_left.mpr fun z h123 h3 => by
            rcases Finset.mem_union.mp h123 with h12 | h2
            · rcases Finset.mem_union.mp h12 with hNR | h1
              · rcases Finset.mem_union.mp hNR with hN | hR
                · exact (hI3_na z h3).1 (Finset.mem_filter.mp hN).2.symm
                · exact (Finset.mem_filter.mp h3).2.2 hR
              · exact (hI3_na z h3).2.1 (Finset.mem_filter.mp h1).2.1
            · exact (hI3_na z h3).2.2 (Finset.mem_filter.mp h2).2.1
      have hNx_w : wsum ω Nx = δ := by rw [← hreg x, wdeg, ← Finset.sum_filter]; rfl
      linarith
    linarith
  have hw_UI1 : wsum ω U_set = 3 * δ - 1 - ω x + wsum ω I1 := by linarith
  have hw_VI2 : wsum ω V_set = 3 * δ - 1 - ω x + wsum ω I2 := by linarith
  have hw_WI3 : wsum ω W_set = 3 * δ - 1 - ω x + wsum ω I3 := by linarith
  have hI1_ne : I1.Nonempty := by
    by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
    have : wsum ω I1 = 0 := by rw [wsum, he, Finset.sum_empty]
    have ha_le : ω a ≤ wsum ω A_set := Finset.single_le_sum (f := ω) (fun _ _ => hnn _) haA
    linarith [hpos a]
  have hI2_ne : I2.Nonempty := by
    by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
    have : wsum ω I2 = 0 := by rw [wsum, he, Finset.sum_empty]
    have hb_le : ω b ≤ wsum ω B_set := Finset.single_le_sum (f := ω) (fun _ _ => hnn _) hbB
    linarith [hpos b]
  have hI3_ne : I3.Nonempty := by
    by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
    have : wsum ω I3 = 0 := by rw [wsum, he, Finset.sum_empty]
    have hc_le : ω c ≤ wsum ω C_set := Finset.single_le_sum (f := ω) (fun _ _ => hnn _) hcC
    linarith [hpos c]
  -- Claim 12 (Reusable uniform => singleton helper)
  have hcl12 : ∀ (a0 u0 : U) (A0 U0 I0 : Finset U)
      (_ : a0 ∈ A0) (_ : u0 ∈ U0) (_ : I0.Nonempty)
      (_ : ∀ p ∈ A0, ∀ z ∈ I0, H.Adj p z → True)
      -- Every `p ∈ A0` has same neighbors as `a0` outside `U0 ∪ I0`, and `a0` avoids `U0` and is complete to `I0`;
      -- Every `u' ∈ U0` has same neighbors as `u0` outside `A0 ∪ I0`, and `u0` avoids `A0` and is complete to `I0`.
      (_ : ∀ p ∈ A0, ∀ z : U, z ∉ U0 → z ∉ I0 → (H.Adj p z ↔ H.Adj a0 z))
      (_ : ∀ u' ∈ U0, ∀ z : U, z ∉ A0 → z ∉ I0 → (H.Adj u' z ↔ H.Adj u0 z))
      (_ : ∀ z ∈ I0, H.Adj a0 z ∧ H.Adj u0 z)
      (_ : ∀ p ∈ A0, ¬ H.Adj p u0) (_ : ∀ u' ∈ U0, ¬ H.Adj a0 u')
      (_ : ∀ p ∈ A0, ∀ u' ∈ U0, p ≠ u')
      (_ : ∀ p ∈ A0, ∀ u' ∈ U0, ∀ z : U, H.Adj p z → H.Adj u' z → z ∈ I0),
      (∀ q ∈ A0 ∪ U0, ∀ z1 ∈ I0, ∀ z2 ∈ I0, H.Adj q z1 ↔ H.Adj q z2) →
      A0 = {a0} ∧ U0 = {u0} := by
    intro a0 u0 A0 U0 I0 ha0 hu0 hI0_ne _ hA_out hU_out hcomp hAna hUna hAU_ne hAU_com hunif
    have hA_comp : ∀ p ∈ A0, ∀ z ∈ I0, H.Adj p z := by
      intro p hp z hz
      obtain ⟨z0, hz0p, hz0u⟩ := G.hMax p u0 (hAU_ne p hp u0 hu0) (hAna p hp)
      have hz0I : z0 ∈ I0 := hAU_com p hp u0 hu0 z0 hz0p hz0u
      exact (hunif p (Finset.mem_union_left _ hp) z0 hz0I z hz).mp hz0p
    have hU_comp : ∀ u' ∈ U0, ∀ z ∈ I0, H.Adj u' z := by
      intro u' hu' z hz
      obtain ⟨z0, hz0a, hz0u⟩ := G.hMax a0 u' (hAU_ne a0 ha0 u' hu') (hUna u' hu')
      have hz0I : z0 ∈ I0 := hAU_com a0 ha0 u' hu' z0 hz0a hz0u
      exact (hunif u' (Finset.mem_union_right _ hu') z0 hz0I z hz).mp hz0u
    have hnoAU : ∀ p ∈ A0, ∀ u' ∈ U0, ¬ H.Adj p u' := fun p hp u' hu' h => by
      obtain ⟨z0, hz0⟩ := hI0_ne; exact tf_contra G.hTF h (hU_comp u' hu' z0 hz0) (hA_comp p hp z0 hz0)
    refine ⟨Finset.eq_singleton_iff_unique_mem.mpr ⟨ha0, fun p hp => G.hTwin p a0 (fun z => ?_)⟩,
            Finset.eq_singleton_iff_unique_mem.mpr ⟨hu0, fun u' hu' => G.hTwin u' u0 (fun z => ?_)⟩⟩
    · by_cases hzU : z ∈ U0
      · exact ⟨fun h => (hnoAU p hp z hzU h).elim, fun h => (hnoAU a0 ha0 z hzU h).elim⟩
      · by_cases hzI : z ∈ I0
        · exact ⟨fun _ => (hcomp z hzI).1, fun _ => hA_comp p hp z hzI⟩
        · exact hA_out p hp z hzU hzI
    · by_cases hzA : z ∈ A0
      · exact ⟨fun h => (hnoAU z hzA u' hu' h.symm).elim, fun h => (hnoAU z hzA u0 hu0 h.symm).elim⟩
      · by_cases hzI : z ∈ I0
        · exact ⟨fun _ => (hcomp z hzI).2, fun _ => hU_comp u' hu' z hzI⟩
        · exact hU_out u' hu' z hzA hzI
  -- Exact outer-neighborhood agreement for `A_set/U_set`, `B_set/V_set`, `C_set/W_set`
  have hA_out : ∀ p ∈ A_set, ∀ z : U, z ∉ U_set → z ∉ I1 → (H.Adj p z ↔ H.Adj a z) := by
    intro p hp z hzU hz1; have hpN := (Finset.mem_filter.mp hp).1
    rcases hpart z with hzN | hzR | hz1' | hz2 | hz3
    · exact ⟨fun h => (hNx_ind p hpN z hzN h).elim, fun h => (hNx_ind a (Finset.mem_filter.mp haA).1 z hzN h).elim⟩
    · simp only [R_set, Finset.mem_insert, Finset.mem_union] at hzR
      rcases hzR with rfl | ((hU | hV) | hW)
      · exact ⟨fun _ => hax.symm, fun _ => (Finset.mem_filter.mp hpN).2.symm⟩
      · exact (hzU hU).elim
      · exact ⟨fun _ => (hA_VW a haA).1 z hV, fun _ => (hA_VW p hp).1 z hV⟩
      · exact ⟨fun _ => (hA_VW a haA).2 z hW, fun _ => (hA_VW p hp).2 z hW⟩
    · exact (hz1 hz1').elim
    · exact ⟨fun h => ((hI2_avoid z hz2).1 p (Finset.mem_union_left _ (Finset.mem_union_right _ hp)) h.symm).elim,
             fun h => ((hI2_avoid z hz2).1 a (Finset.mem_union_left _ (Finset.mem_union_right _ haA)) h.symm).elim⟩
    · exact ⟨fun h => ((hI3_avoid z hz3).1 p (Finset.mem_union_left _ (Finset.mem_union_right _ hp)) h.symm).elim,
             fun h => ((hI3_avoid z hz3).1 a (Finset.mem_union_left _ (Finset.mem_union_right _ haA)) h.symm).elim⟩
  have hU_out : ∀ u' ∈ U_set, ∀ z : U, z ∉ A_set → z ∉ I1 → (H.Adj u' z ↔ H.Adj u z) := by
    intro u' hu' z hzA hz1
    have hu'R : u' ∈ R_set := Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hu'))
    rcases hpart z with hzN | hzR | hz1' | hz2 | hz3
    · rcases hNx_part z hzN with hY | hA | hB | hC
      · exact ⟨fun _ => (hY_nbhd z hY u).mpr huR |>.symm, fun _ => (hY_nbhd z hY u').mpr hu'R |>.symm⟩
      · exact (hzA hA).elim
      · exact ⟨fun _ => ((hB_UW z hB).1 u huU).symm, fun _ => ((hB_UW z hB).1 u' hu').symm⟩
      · exact ⟨fun _ => ((hC_UV z hC).1 u huU).symm, fun _ => ((hC_UV z hC).1 u' hu').symm⟩
    · exact ⟨fun h => (hR_ind u' hu'R z hzR h).elim, fun h => (hR_ind u huR z hzR h).elim⟩
    · exact (hz1 hz1').elim
    · exact ⟨fun h => ((hI2_avoid z hz2).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_left _ hu')) h.symm).elim,
             fun h => ((hI2_avoid z hz2).2 u (Finset.mem_insert_of_mem (Finset.mem_union_left _ huU)) h.symm).elim⟩
    · exact ⟨fun h => ((hI3_avoid z hz3).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_left _ hu')) h.symm).elim,
             fun h => ((hI3_avoid z hz3).2 u (Finset.mem_insert_of_mem (Finset.mem_union_left _ huU)) h.symm).elim⟩
  have hB_out : ∀ p ∈ B_set, ∀ z : U, z ∉ V_set → z ∉ I2 → (H.Adj p z ↔ H.Adj b z) := by
    intro p hp z hzV hz2; have hpN := (Finset.mem_filter.mp hp).1
    rcases hpart z with hzN | hzR | hz1 | hz2' | hz3
    · exact ⟨fun h => (hNx_ind p hpN z hzN h).elim, fun h => (hNx_ind b (Finset.mem_filter.mp hbB).1 z hzN h).elim⟩
    · simp only [R_set, Finset.mem_insert, Finset.mem_union] at hzR
      rcases hzR with rfl | ((hU | hV) | hW)
      · exact ⟨fun _ => hbx.symm, fun _ => (Finset.mem_filter.mp hpN).2.symm⟩
      · exact ⟨fun _ => (hB_UW b hbB).1 z hU, fun _ => (hB_UW p hp).1 z hU⟩
      · exact (hzV hV).elim
      · exact ⟨fun _ => (hB_UW b hbB).2 z hW, fun _ => (hB_UW p hp).2 z hW⟩
    · exact ⟨fun h => ((hI1_avoid z hz1).1 p (Finset.mem_union_left _ (Finset.mem_union_right _ hp)) h.symm).elim,
             fun h => ((hI1_avoid z hz1).1 b (Finset.mem_union_left _ (Finset.mem_union_right _ hbB)) h.symm).elim⟩
    · exact (hz2 hz2').elim
    · exact ⟨fun h => ((hI3_avoid z hz3).1 p (Finset.mem_union_right _ hp) h.symm).elim,
             fun h => ((hI3_avoid z hz3).1 b (Finset.mem_union_right _ hbB) h.symm).elim⟩
  have hV_out : ∀ v' ∈ V_set, ∀ z : U, z ∉ B_set → z ∉ I2 → (H.Adj v' z ↔ H.Adj v z) := by
    intro v' hv' z hzB hz2
    have hv'R : v' ∈ R_set := Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hv'))
    rcases hpart z with hzN | hzR | hz1 | hz2' | hz3
    · rcases hNx_part z hzN with hY | hA | hB | hC
      · exact ⟨fun _ => (hY_nbhd z hY v).mpr hvR |>.symm, fun _ => (hY_nbhd z hY v').mpr hv'R |>.symm⟩
      · exact ⟨fun _ => ((hA_VW z hA).1 v hvV).symm, fun _ => ((hA_VW z hA).1 v' hv').symm⟩
      · exact (hzB hB).elim
      · exact ⟨fun _ => ((hC_UV z hC).2 v hvV).symm, fun _ => ((hC_UV z hC).2 v' hv').symm⟩
    · exact ⟨fun h => (hR_ind v' hv'R z hzR h).elim, fun h => (hR_ind v hvR z hzR h).elim⟩
    · exact ⟨fun h => ((hI1_avoid z hz1).2 v' (Finset.mem_insert_of_mem (Finset.mem_union_left _ hv')) h.symm).elim,
             fun h => ((hI1_avoid z hz1).2 v (Finset.mem_insert_of_mem (Finset.mem_union_left _ hvV)) h.symm).elim⟩
    · exact (hz2 hz2').elim
    · exact ⟨fun h => ((hI3_avoid z hz3).2 v' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hv')) h.symm).elim,
             fun h => ((hI3_avoid z hz3).2 v (Finset.mem_insert_of_mem (Finset.mem_union_right _ hvV)) h.symm).elim⟩
  have hC_out : ∀ p ∈ C_set, ∀ z : U, z ∉ W_set → z ∉ I3 → (H.Adj p z ↔ H.Adj c z) := by
    intro p hp z hzW hz3; have hpN := (Finset.mem_filter.mp hp).1
    rcases hpart z with hzN | hzR | hz1 | hz2 | hz3'
    · exact ⟨fun h => (hNx_ind p hpN z hzN h).elim, fun h => (hNx_ind c (Finset.mem_filter.mp hcC).1 z hzN h).elim⟩
    · simp only [R_set, Finset.mem_insert, Finset.mem_union] at hzR
      rcases hzR with rfl | ((hU | hV) | hW)
      · exact ⟨fun _ => hcx.symm, fun _ => (Finset.mem_filter.mp hpN).2.symm⟩
      · exact ⟨fun _ => (hC_UV c hcC).1 z hU, fun _ => (hC_UV p hp).1 z hU⟩
      · exact ⟨fun _ => (hC_UV c hcC).2 z hV, fun _ => (hC_UV p hp).2 z hV⟩
      · exact (hzW hW).elim
    · exact ⟨fun h => ((hI1_avoid z hz1).1 p (Finset.mem_union_right _ hp) h.symm).elim,
             fun h => ((hI1_avoid z hz1).1 c (Finset.mem_union_right _ hcC) h.symm).elim⟩
    · exact ⟨fun h => ((hI2_avoid z hz2).1 p (Finset.mem_union_right _ hp) h.symm).elim,
             fun h => ((hI2_avoid z hz2).1 c (Finset.mem_union_right _ hcC) h.symm).elim⟩
    · exact (hz3 hz3').elim
  have hW_out : ∀ w' ∈ W_set, ∀ z : U, z ∉ C_set → z ∉ I3 → (H.Adj w' z ↔ H.Adj w z) := by
    intro w' hw' z hzC hz3
    have hw'R : w' ∈ R_set := Finset.mem_insert_of_mem (Finset.mem_union_right _ hw')
    rcases hpart z with hzN | hzR | hz1 | hz2 | hz3'
    · rcases hNx_part z hzN with hY | hA | hB | hC
      · exact ⟨fun _ => (hY_nbhd z hY w).mpr hwR |>.symm, fun _ => (hY_nbhd z hY w').mpr hw'R |>.symm⟩
      · exact ⟨fun _ => ((hA_VW z hA).2 w hwW).symm, fun _ => ((hA_VW z hA).2 w' hw').symm⟩
      · exact ⟨fun _ => ((hB_UW z hB).2 w hwW).symm, fun _ => ((hB_UW z hB).2 w' hw').symm⟩
      · exact (hzC hC).elim
    · exact ⟨fun h => (hR_ind w' hw'R z hzR h).elim, fun h => (hR_ind w hwR z hzR h).elim⟩
    · exact ⟨fun h => ((hI1_avoid z hz1).2 w' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hw')) h.symm).elim,
             fun h => ((hI1_avoid z hz1).2 w (Finset.mem_insert_of_mem (Finset.mem_union_right _ hwW)) h.symm).elim⟩
    · exact ⟨fun h => ((hI2_avoid z hz2).2 w' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hw')) h.symm).elim,
             fun h => ((hI2_avoid z hz2).2 w (Finset.mem_insert_of_mem (Finset.mem_union_right _ hwW)) h.symm).elim⟩
    · exact (hz3 hz3').elim
  -- Helpers for Claim 12 instantiations on (A,U,I1), (B,V,I2), (C,W,I3)
  have hdisj_NR' : ∀ n ∈ Nx, ∀ r ∈ R_set, n ≠ r := fun n hn r hr h => by
    subst h; rcases eq_or_ne n x with rfl | hne
    · exact H.loopless.irrefl _ (Finset.mem_filter.mp hn).2
    · exact hR_ind n hr x (Finset.mem_insert_self x _) (Finset.mem_filter.mp hn).2.symm
  have hcl12_1 : (∀ q ∈ A_set ∪ U_set, ∀ z1 ∈ I1, ∀ z2 ∈ I1, H.Adj q z1 ↔ H.Adj q z2) → A_set = {a} ∧ U_set = {u} :=
    hcl12 a u A_set U_set I1 haA huU hI1_ne (fun _ _ _ _ _ => trivial) hA_out hU_out
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2.1.symm, hu_I1 z hz⟩)
      (fun p hp => (Finset.mem_filter.mp hp).2.1)
      (fun u' hu' h => hnot_abc u' (Finset.mem_filter.mp hu').2.1 ⟨h.symm, (Finset.mem_filter.mp hu').2.2⟩)
      (fun p hp u' hu' => hdisj_NR' p (Finset.mem_filter.mp hp).1 u' (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hu'))))
      (fun p hp u' hu' z hpz hu'z => by
        rcases hpart z with h | h | h | h | h
        · exact (hNx_ind p (Finset.mem_filter.mp hp).1 z h hpz).elim
        · exact (hR_ind u' (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hu'))) z h hu'z).elim
        · exact h
        · exact ((hI2_avoid z h).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_left _ hu')) hu'z.symm).elim
        · exact ((hI3_avoid z h).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_left _ hu')) hu'z.symm).elim)
  have hcl12_2 : (∀ q ∈ B_set ∪ V_set, ∀ z1 ∈ I2, ∀ z2 ∈ I2, H.Adj q z1 ↔ H.Adj q z2) → B_set = {b} ∧ V_set = {v} :=
    hcl12 b v B_set V_set I2 hbB hvV hI2_ne (fun _ _ _ _ _ => trivial) hB_out hV_out
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2.1.symm, hv_I2 z hz⟩)
      (fun p hp => (Finset.mem_filter.mp hp).2.2.1)
      (fun v' hv' h => hnot_abc v' (Finset.mem_filter.mp hv').2.1 ⟨(Finset.mem_filter.mp hv').2.2.1, h.symm, (Finset.mem_filter.mp hv').2.2.2⟩)
      (fun p hp v' hv' => hdisj_NR' p (Finset.mem_filter.mp hp).1 v' (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hv'))))
      (fun p hp v' hv' z hpz hv'z => by
        rcases hpart z with h | h | h | h | h
        · exact (hNx_ind p (Finset.mem_filter.mp hp).1 z h hpz).elim
        · exact (hR_ind v' (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hv'))) z h hv'z).elim
        · exact ((hI1_avoid z h).2 v' (Finset.mem_insert_of_mem (Finset.mem_union_left _ hv')) hv'z.symm).elim
        · exact h
        · exact ((hI3_avoid z h).2 v' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hv')) hv'z.symm).elim)
  have hcl12_3 : (∀ q ∈ C_set ∪ W_set, ∀ z1 ∈ I3, ∀ z2 ∈ I3, H.Adj q z1 ↔ H.Adj q z2) → C_set = {c} ∧ W_set = {w} :=
    hcl12 c w C_set W_set I3 hcC hwW hI3_ne (fun _ _ _ _ _ => trivial) hC_out hW_out
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2.1.symm, hw_I3 z hz⟩)
      (fun p hp => (Finset.mem_filter.mp hp).2.2.2)
      (fun w' hw' h => hnot_abc w' (Finset.mem_filter.mp hw').2.1 ⟨(Finset.mem_filter.mp hw').2.2.1, (Finset.mem_filter.mp hw').2.2.2, h.symm⟩)
      (fun p hp w' hw' => hdisj_NR' p (Finset.mem_filter.mp hp).1 w' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hw')))
      (fun p hp w' hw' z hpz hw'z => by
        rcases hpart z with h | h | h | h | h
        · exact (hNx_ind p (Finset.mem_filter.mp hp).1 z h hpz).elim
        · exact (hR_ind w' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hw')) z h hw'z).elim
        · exact ((hI1_avoid z h).2 w' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hw')) hw'z.symm).elim
        · exact ((hI2_avoid z h).2 w' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hw')) hw'z.symm).elim
        · exact h)
  -- Claim 13.1: `e(I_j, I_k) > 0` for all 3 pairs!
  have hedge_pair : ∀ (a1 u1 a2 u2 : U) (I_1 I_2 : Finset U),
      I_1.Nonempty → I_2.Nonempty →
      (∀ z ∈ I_1, H.Adj a1 z ∧ H.Adj u1 z) → (∀ z ∈ I_2, H.Adj a2 z ∧ H.Adj u2 z) →
      H.Adj u1 a2 → H.Adj u2 a1 →
      (∀ z : U, H.Adj z a1 → H.Adj z u1 → z ∈ I_1) →
      (∀ z : U, H.Adj z a2 → H.Adj z u2 → z ∈ I_2) →
      (∀ z ∈ I_1, z ≠ a1 ∧ z ≠ u1 ∧ z ≠ a2 ∧ z ≠ u2) →
      (∀ z ∈ I_2, z ≠ a1 ∧ z ≠ u1 ∧ z ≠ a2 ∧ z ≠ u2) →
      Disjoint I_1 I_2 → a1 ≠ u1 → a1 ≠ a2 → a1 ≠ u2 → u1 ≠ a2 → u1 ≠ u2 → a2 ≠ u2 →
      ∃ z1 ∈ I_1, ∃ z2 ∈ I_2, H.Adj z1 z2 := by
    intro a1 u1 a2 u2 I_1 I_2 hne1 hne2 h1 h2 hu1a2 hu2a1 hcom1 hcom2 hneI1 hneI2 hdisj h01 h02 h03 h12 h13 h23
    by_contra hno; push Not at hno
    obtain ⟨z1, hz1⟩ := hne1; obtain ⟨z2, hz2⟩ := hne2
    have hz12 : z1 ≠ z2 := fun h => Finset.disjoint_left.mp hdisj hz1 (h ▸ hz2)
    let cyc : Fin 6 → U := ![a1, z1, u1, a2, z2, u2]
    have hcyc_inj : Function.Injective cyc := by
      have q1 := hneI1 z1 hz1; have q2 := hneI2 z2 hz2
      intro i j hij; fin_cases i <;> fin_cases j <;> dsimp [cyc] at hij ⊢
      all_goals first | rfl | exact (h01 hij).elim | exact (h01 hij.symm).elim | exact (h02 hij).elim | exact (h02 hij.symm).elim
                      | exact (h03 hij).elim | exact (h03 hij.symm).elim | exact (h12 hij).elim | exact (h12 hij.symm).elim
                      | exact (h13 hij).elim | exact (h13 hij.symm).elim | exact (h23 hij).elim | exact (h23 hij.symm).elim
                      | exact (hz12 hij).elim | exact (hz12 hij.symm).elim
                      | exact (q1.1 hij).elim | exact (q1.1 hij.symm).elim | exact (q1.2.1 hij).elim | exact (q1.2.1 hij.symm).elim
                      | exact (q1.2.2.1 hij).elim | exact (q1.2.2.1 hij.symm).elim | exact (q1.2.2.2 hij).elim | exact (q1.2.2.2 hij.symm).elim
                      | exact (q2.1 hij).elim | exact (q2.1 hij.symm).elim | exact (q2.2.1 hij).elim | exact (q2.2.1 hij.symm).elim
                      | exact (q2.2.2.1 hij).elim | exact (q2.2.2.1 hij.symm).elim | exact (q2.2.2.2 hij).elim | exact (q2.2.2.2 hij.symm).elim
    obtain ⟨z, hz⟩ := exists_dom3_of_c6 H G.hTF hnn hsum hdeg cyc hcyc_inj
      (h1 z1 hz1).1 (h1 z1 hz1).2.symm hu1a2 (h2 z2 hz2).1 (h2 z2 hz2).2.symm hu2a1
    rcases hz with ⟨ha, hu', hz2'⟩ | ⟨hz1', ha', hu'⟩
    · exact hno z (hcom1 z ha hu') z2 hz2 hz2'
    · exact hno z1 hz1 z (hcom2 z ha' hu') hz1'.symm
  -- Common neighbors of `(a,u)` are `I1`, `(b,v)` are `I2`, `(c,w)` are `I3`
  have hcom_au : ∀ z : U, H.Adj z a → H.Adj z u → z ∈ I1 := fun z hza hzu => by
    rcases hpart z with hN | hR | h1 | h2 | h3
    · exact (hNx_ind z hN a (Finset.mem_filter.mp haA).1 hza).elim
    · exact (hR_ind z hR u huR hzu).elim
    · exact h1
    · exact (hu_na_23.1 z h2 hzu.symm).elim
    · exact (hu_na_23.2 z h3 hzu.symm).elim
  have hcom_bv : ∀ z : U, H.Adj z b → H.Adj z v → z ∈ I2 := fun z hzb hzv => by
    rcases hpart z with hN | hR | h1 | h2 | h3
    · exact (hNx_ind z hN b (Finset.mem_filter.mp hbB).1 hzb).elim
    · exact (hR_ind z hR v hvR hzv).elim
    · exact (hv_na_13.1 z h1 hzv.symm).elim
    · exact h2
    · exact (hv_na_13.2 z h3 hzv.symm).elim
  have hcom_cw : ∀ z : U, H.Adj z c → H.Adj z w → z ∈ I3 := fun z hzc hzw => by
    rcases hpart z with hN | hR | h1 | h2 | h3
    · exact (hNx_ind z hN c (Finset.mem_filter.mp hcC).1 hzc).elim
    · exact (hR_ind z hR w hwR hzw).elim
    · exact (hw_na_12.1 z h1 hzw.symm).elim
    · exact (hw_na_12.2 z h2 hzw.symm).elim
    · exact h3
  have hne_uv : u ≠ v := fun h => hnot_abc u (Finset.mem_filter.mp huU).2.1 ⟨h ▸ (Finset.mem_filter.mp hvV).2.2.1, (Finset.mem_filter.mp huU).2.2⟩
  have hne_uw : u ≠ w := fun h => hnot_abc u (Finset.mem_filter.mp huU).2.1 ⟨h ▸ (Finset.mem_filter.mp hwW).2.2.1, (Finset.mem_filter.mp huU).2.2⟩
  have hne_vw : v ≠ w := fun h => hnot_abc v (Finset.mem_filter.mp hvV).2.1 ⟨(Finset.mem_filter.mp hvV).2.2.1, h ▸ (Finset.mem_filter.mp hwW).2.2.2, (Finset.mem_filter.mp hvV).2.2.2⟩
  have hI_disj12 : Disjoint I1 I2 := Finset.disjoint_left.mpr fun z h1 h2 => (hI1_na z h1).2.1 (Finset.mem_filter.mp h2).2.1
  have hI_disj13 : Disjoint I1 I3 := Finset.disjoint_left.mpr fun z h1 h3 => (hI1_na z h1).2.2 (Finset.mem_filter.mp h3).2.1
  have hI_disj23 : Disjoint I2 I3 := Finset.disjoint_left.mpr fun z h2 h3 => (hI2_na z h2).2.2 (Finset.mem_filter.mp h3).2.1
  have hI_ne_Q : ∀ z : U, (z ∈ I1 ∨ z ∈ I2 ∨ z ∈ I3) → z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ u ∧ z ≠ v ∧ z ≠ w := by
    intro z hz
    have hz_notN : z ∉ Nx := fun hN => by
      rcases hz with h1 | h2 | h3
      · exact (hI1_na z h1).1 (Finset.mem_filter.mp hN).2.symm
      · exact (hI2_na z h2).1 (Finset.mem_filter.mp hN).2.symm
      · exact (hI3_na z h3).1 (Finset.mem_filter.mp hN).2.symm
    have hz_notR : z ∉ R_set := by
      rcases hz with h1 | h2 | h3
      · exact (Finset.mem_filter.mp h1).2.2
      · exact (Finset.mem_filter.mp h2).2.2
      · exact (Finset.mem_filter.mp h3).2.2
    exact ⟨fun h => hz_notN (h ▸ (Finset.mem_filter.mp haA).1),
           fun h => hz_notN (h ▸ (Finset.mem_filter.mp hbB).1),
           fun h => hz_notN (h ▸ (Finset.mem_filter.mp hcC).1),
           fun h => hz_notR (h ▸ huR), fun h => hz_notR (h ▸ hvR), fun h => hz_notR (h ▸ hwR)⟩
  have he12 : ∃ z1 ∈ I1, ∃ z2 ∈ I2, H.Adj z1 z2 :=
    hedge_pair a u b v I1 I2 hI1_ne hI2_ne
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2.1.symm, hu_I1 z hz⟩)
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2.1.symm, hv_I2 z hz⟩)
      (Finset.mem_filter.mp huU).2.2.1 (Finset.mem_filter.mp hvV).2.2.1 hcom_au hcom_bv
      (fun z hz => let q := hI_ne_Q z (Or.inl hz); ⟨q.1, q.2.2.2.1, q.2.1, q.2.2.2.2.1⟩)
      (fun z hz => let q := hI_ne_Q z (Or.inr (Or.inl hz)); ⟨q.1, q.2.2.2.1, q.2.1, q.2.2.2.2.1⟩)
      hI_disj12 (hdisj_NR' a (Finset.mem_filter.mp haA).1 u huR) hab (hdisj_NR' a (Finset.mem_filter.mp haA).1 v hvR)
      (hdisj_NR' b (Finset.mem_filter.mp hbB).1 u huR).symm hne_uv (hdisj_NR' b (Finset.mem_filter.mp hbB).1 v hvR)
  have he13 : ∃ z1 ∈ I1, ∃ z3 ∈ I3, H.Adj z1 z3 :=
    hedge_pair a u c w I1 I3 hI1_ne hI3_ne
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2.1.symm, hu_I1 z hz⟩)
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2.1.symm, hw_I3 z hz⟩)
      (Finset.mem_filter.mp huU).2.2.2 (Finset.mem_filter.mp hwW).2.2.1 hcom_au hcom_cw
      (fun z hz => let q := hI_ne_Q z (Or.inl hz); ⟨q.1, q.2.2.2.1, q.2.2.1, q.2.2.2.2.2⟩)
      (fun z hz => let q := hI_ne_Q z (Or.inr (Or.inr hz)); ⟨q.1, q.2.2.2.1, q.2.2.1, q.2.2.2.2.2⟩)
      hI_disj13 (hdisj_NR' a (Finset.mem_filter.mp haA).1 u huR) hac (hdisj_NR' a (Finset.mem_filter.mp haA).1 w hwR)
      (hdisj_NR' c (Finset.mem_filter.mp hcC).1 u huR).symm hne_uw (hdisj_NR' c (Finset.mem_filter.mp hcC).1 w hwR)
  have he23 : ∃ z2 ∈ I2, ∃ z3 ∈ I3, H.Adj z2 z3 :=
    hedge_pair b v c w I2 I3 hI2_ne hI3_ne
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2.1.symm, hv_I2 z hz⟩)
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2.1.symm, hw_I3 z hz⟩)
      (Finset.mem_filter.mp hvV).2.2.2 (Finset.mem_filter.mp hwW).2.2.2 hcom_bv hcom_cw
      (fun z hz => let q := hI_ne_Q z (Or.inr (Or.inl hz)); ⟨q.2.1, q.2.2.2.2.1, q.2.2.1, q.2.2.2.2.2⟩)
      (fun z hz => let q := hI_ne_Q z (Or.inr (Or.inr hz)); ⟨q.2.1, q.2.2.2.2.1, q.2.2.1, q.2.2.2.2.2⟩)
      hI_disj23 (hdisj_NR' b (Finset.mem_filter.mp hbB).1 v hvR) hbc (hdisj_NR' b (Finset.mem_filter.mp hbB).1 w hwR)
      (hdisj_NR' c (Finset.mem_filter.mp hcC).1 v hvR).symm hne_vw (hdisj_NR' c (Finset.mem_filter.mp hcC).1 w hwR)
  -- Helper for Claim 13.3: if `I_3` splits in `C ∪ W`, get `pC ∈ C, w' ∈ W, z0, z1 ∈ I_3` and prove
  -- ALL vertices of `I_3` have the EXACT SAME neighborhood in `I_1 ∪ I_2`!
  -- We write it parametrically in `(C0, W0, I_0, I_1', I_2')` so we can apply it to `I1`, `I2`, AND `I3`!
  have hsplit_unif : ∀ (C0 W0 I_0 I_1' I_2' : Finset U),
      C0 ⊆ Nx → W0 ⊆ R_set →
      (∀ z ∈ I_0, z ∉ Nx ∧ z ∉ R_set ∧ z ∉ I_1' ∧ z ∉ I_2') →
      (∀ z ∈ I_1', z ∉ Nx ∧ z ∉ R_set ∧ z ∉ I_0 ∧ z ∉ I_2') →
      (∀ z ∈ I_2', z ∉ Nx ∧ z ∉ R_set ∧ z ∉ I_0 ∧ z ∉ I_1') →
      (∀ p ∈ C0, ∀ z ∈ I_1' ∪ I_2', ¬ H.Adj p z) →
      (∀ w' ∈ W0, ∀ z ∈ I_1' ∪ I_2', ¬ H.Adj w' z) →
      (∀ p ∈ C0, ∀ z ∈ I_0, ∀ q : U, H.Adj p q → H.Adj z q → q ∈ W0) →
      (∀ w' ∈ W0, ∀ z ∈ I_0, ∀ q : U, H.Adj w' q → H.Adj z q → q ∈ C0) →
      (∀ x1 ∈ I_1', ∀ z ∈ I_0, ∀ q : U, H.Adj x1 q → H.Adj z q → q ∈ I_2') →
      (∀ x2 ∈ I_2', ∀ z ∈ I_0, ∀ q : U, H.Adj x2 q → H.Adj z q → q ∈ I_1') →
      (∃ q ∈ C0 ∪ W0, ∃ z0 ∈ I_0, ∃ z1 ∈ I_0, H.Adj q z0 ∧ ¬ H.Adj q z1) →
      (∃ pC ∈ C0, ∃ w' ∈ W0, ∃ z0 ∈ I_0, ∃ z1 ∈ I_0,
        H.Adj pC w' ∧ H.Adj pC z0 ∧ ¬ H.Adj pC z1 ∧ H.Adj w' z1 ∧ ¬ H.Adj w' z0) ∧
      (∀ zA ∈ I_0, ∀ zB ∈ I_0, ∀ t ∈ I_1' ∪ I_2', H.Adj zA t ↔ H.Adj zB t) := by
    intro C0 W0 I_0 I_1' I_2' hCN hWR hI0d hI1d hI2d hC_na hW_na hCW hWC h10_2 h20_1 ⟨q, hqCW, z0, hz0, z1, hz1, hqz0, hnqz1⟩
    have hex_sep : ∃ pC ∈ C0, ∃ w' ∈ W0, ∃ z0' ∈ I_0, ∃ z1' ∈ I_0,
        H.Adj pC w' ∧ H.Adj pC z0' ∧ ¬ H.Adj pC z1' ∧ H.Adj w' z1' ∧ ¬ H.Adj w' z0' := by
      rcases Finset.mem_union.mp hqCW with hqC | hqW
      · have hne : q ≠ z1 := fun h => (hI0d z1 hz1).1 (h ▸ hCN hqC)
        obtain ⟨w', hqw', hz1w'⟩ := G.hMax q z1 hne hnqz1
        have hw'W : w' ∈ W0 := hCW q hqC z1 hz1 w' hqw' hz1w'
        have hna : ¬ H.Adj w' z0 := fun h => tf_contra G.hTF hqw' h hqz0
        exact ⟨q, hqC, w', hw'W, z0, hz0, z1, hz1, hqw', hqz0, hnqz1, hz1w'.symm, hna⟩
      · have hne : q ≠ z1 := fun h => (hI0d z1 hz1).2.1 (h ▸ hWR hqW)
        obtain ⟨pC, hqpC, hz1pC⟩ := G.hMax q z1 hne hnqz1
        have hpCC : pC ∈ C0 := hWC q hqW z1 hz1 pC hqpC hz1pC
        have hna : ¬ H.Adj pC z0 := fun h => tf_contra G.hTF hqpC.symm hqz0 h
        exact ⟨pC, hpCC, q, hqW, z1, hz1, z0, hz0, hqpC.symm, hz1pC.symm, hna, hqz0, hnqz1⟩
    obtain ⟨pC, hpC, w', hw', z0', hz0', z1', hz1', hpCw', hpCz0', hnpCz1', hw'z1', hnw'z0'⟩ := hex_sep
    refine ⟨⟨pC, hpC, w', hw', z0', hz0', z1', hz1', hpCw', hpCz0', hnpCz1', hw'z1', hnw'z0'⟩, ?_⟩
    -- Prove: if `pC ~ zA` and `¬ pC ~ zB`, then `zA` and `zB` have exact same neighborhood in `I_1' ∪ I_2'`!
    have hsep_same : ∀ zA ∈ I_0, ∀ zB ∈ I_0, H.Adj pC zA → ¬ H.Adj pC zB →
        ∀ t ∈ I_1' ∪ I_2', H.Adj zA t ↔ H.Adj zB t := by
      intro zA hzA zB hzB hpA hnpB
      have hpB_ne : pC ≠ zB := fun h => (hI0d zB hzB).1 (h ▸ hCN hpC)
      obtain ⟨w2, hpCw2, hzBw2⟩ := G.hMax pC zB hpB_ne hnpB
      have hw2W : w2 ∈ W0 := hCW pC hpC zB hzB w2 hpCw2 hzBw2
      have hnw2A : ¬ H.Adj w2 zA := fun h => tf_contra G.hTF hpCw2 h hpA
      have hzAB_ne : zA ≠ zB := fun h => hnpB (h ▸ hpA)
      -- Generic helper killing `zA ~ t` and `¬ zB ~ t` (or vice-versa) for `t ∈ Ia`
      have hkill_one : ∀ (Ia Ib : Finset U),
          Ia ⊆ I_1' ∪ I_2' → Ib ⊆ I_1' ∪ I_2' →
          (∀ z ∈ Ia, z ∉ Nx ∧ z ∉ R_set ∧ z ∉ I_0 ∧ z ∉ Ib) →
          (∀ z ∈ Ib, z ∉ Nx ∧ z ∉ R_set ∧ z ∉ I_0 ∧ z ∉ Ia) →
          (∀ x ∈ Ia, ∀ z ∈ I_0, ∀ q : U, H.Adj x q → H.Adj z q → q ∈ Ib) →
          ∀ t ∈ Ia, (H.Adj zA t → H.Adj zB t) ∧ (H.Adj zB t → H.Adj zA t) := by
        intro Ia Ib hIa_sub hIb_sub hIa hIb hcom_ab t htIa
        constructor
        · intro hzAt; by_contra hnzBt
          have htB_ne : t ≠ zB := fun h => (hIa t htIa).2.2.1 (h ▸ hzB)
          obtain ⟨y0, hty0, hzBy0⟩ := G.hMax t zB htB_ne (fun h => hnzBt h.symm)
          have hy0Ib : y0 ∈ Ib := hcom_ab t htIa zB hzB y0 hty0 hzBy0
          let cyc : Fin 6 → U := ![pC, w2, zB, y0, t, zA]
          have hcyc_inj : Function.Injective cyc := by
            have hpN := hCN hpC; have hwR := hWR hw2W
            intro i j hij; fin_cases i <;> fin_cases j <;> dsimp [cyc] at hij ⊢
            all_goals first | rfl | exact (hzAB_ne hij).elim | exact (hzAB_ne hij.symm).elim
                            | exact (hdisj_NR' pC hpN w2 hwR hij).elim | exact (hdisj_NR' pC hpN w2 hwR hij.symm).elim
                            | exact ((hI0d zA hzA).1 (hij ▸ hpN)).elim | exact ((hI0d zA hzA).1 (hij.symm ▸ hpN)).elim
                            | exact ((hI0d zB hzB).1 (hij ▸ hpN)).elim | exact ((hI0d zB hzB).1 (hij.symm ▸ hpN)).elim
                            | exact ((hIa t htIa).1 (hij ▸ hpN)).elim | exact ((hIa t htIa).1 (hij.symm ▸ hpN)).elim
                            | exact ((hIb y0 hy0Ib).1 (hij ▸ hpN)).elim | exact ((hIb y0 hy0Ib).1 (hij.symm ▸ hpN)).elim
                            | exact ((hI0d zA hzA).2.1 (hij ▸ hwR)).elim | exact ((hI0d zA hzA).2.1 (hij.symm ▸ hwR)).elim
                            | exact ((hI0d zB hzB).2.1 (hij ▸ hwR)).elim | exact ((hI0d zB hzB).2.1 (hij.symm ▸ hwR)).elim
                            | exact ((hIa t htIa).2.1 (hij ▸ hwR)).elim | exact ((hIa t htIa).2.1 (hij.symm ▸ hwR)).elim
                            | exact ((hIb y0 hy0Ib).2.1 (hij ▸ hwR)).elim | exact ((hIb y0 hy0Ib).2.1 (hij.symm ▸ hwR)).elim
                            | exact ((hIa t htIa).2.2.1 (hij ▸ hzA)).elim | exact ((hIa t htIa).2.2.1 (hij.symm ▸ hzA)).elim
                            | exact ((hIa t htIa).2.2.1 (hij ▸ hzB)).elim | exact ((hIa t htIa).2.2.1 (hij.symm ▸ hzB)).elim
                            | exact ((hIb y0 hy0Ib).2.2.1 (hij ▸ hzA)).elim | exact ((hIb y0 hy0Ib).2.2.1 (hij.symm ▸ hzA)).elim
                            | exact ((hIb y0 hy0Ib).2.2.1 (hij ▸ hzB)).elim | exact ((hIb y0 hy0Ib).2.2.1 (hij.symm ▸ hzB)).elim
                            | exact ((hIa t htIa).2.2.2 (hij ▸ hy0Ib)).elim
          obtain ⟨q, hq⟩ := exists_dom3_of_c6 H G.hTF hnn hsum hdeg cyc hcyc_inj
            hpCw2 hzBw2.symm hzBy0 hty0.symm hzAt.symm hpA.symm
          rcases hq with ⟨h0, h2, h4⟩ | ⟨h1, h3, h5⟩
          · exact hW_na q (hCW pC hpC zB hzB q h0.symm h2.symm) t (hIa_sub htIa) h4
          · exact hC_na q (hWC w2 hw2W zA hzA q h1.symm h5.symm) y0 (hIb_sub hy0Ib) h3
        · intro hzBt; by_contra hnzAt
          have htA_ne : t ≠ zA := fun h => (hIa t htIa).2.2.1 (h ▸ hzA)
          obtain ⟨y0, hty0, hzAy0⟩ := G.hMax t zA htA_ne (fun h => hnzAt h.symm)
          have hy0Ib : y0 ∈ Ib := hcom_ab t htIa zA hzA y0 hty0 hzAy0
          let cyc : Fin 6 → U := ![pC, w2, zB, t, y0, zA]
          have hcyc_inj : Function.Injective cyc := by
            have hpN := hCN hpC; have hwR := hWR hw2W
            intro i j hij; fin_cases i <;> fin_cases j <;> dsimp [cyc] at hij ⊢
            all_goals first | rfl | exact (hzAB_ne hij).elim | exact (hzAB_ne hij.symm).elim
                            | exact (hdisj_NR' pC hpN w2 hwR hij).elim | exact (hdisj_NR' pC hpN w2 hwR hij.symm).elim
                            | exact ((hI0d zA hzA).1 (hij ▸ hpN)).elim | exact ((hI0d zA hzA).1 (hij.symm ▸ hpN)).elim
                            | exact ((hI0d zB hzB).1 (hij ▸ hpN)).elim | exact ((hI0d zB hzB).1 (hij.symm ▸ hpN)).elim
                            | exact ((hIa t htIa).1 (hij ▸ hpN)).elim | exact ((hIa t htIa).1 (hij.symm ▸ hpN)).elim
                            | exact ((hIb y0 hy0Ib).1 (hij ▸ hpN)).elim | exact ((hIb y0 hy0Ib).1 (hij.symm ▸ hpN)).elim
                            | exact ((hI0d zA hzA).2.1 (hij ▸ hwR)).elim | exact ((hI0d zA hzA).2.1 (hij.symm ▸ hwR)).elim
                            | exact ((hI0d zB hzB).2.1 (hij ▸ hwR)).elim | exact ((hI0d zB hzB).2.1 (hij.symm ▸ hwR)).elim
                            | exact ((hIa t htIa).2.1 (hij ▸ hwR)).elim | exact ((hIa t htIa).2.1 (hij.symm ▸ hwR)).elim
                            | exact ((hIb y0 hy0Ib).2.1 (hij ▸ hwR)).elim | exact ((hIb y0 hy0Ib).2.1 (hij.symm ▸ hwR)).elim
                            | exact ((hIa t htIa).2.2.1 (hij ▸ hzA)).elim | exact ((hIa t htIa).2.2.1 (hij.symm ▸ hzA)).elim
                            | exact ((hIa t htIa).2.2.1 (hij ▸ hzB)).elim | exact ((hIa t htIa).2.2.1 (hij.symm ▸ hzB)).elim
                            | exact ((hIb y0 hy0Ib).2.2.1 (hij ▸ hzA)).elim | exact ((hIb y0 hy0Ib).2.2.1 (hij.symm ▸ hzA)).elim
                            | exact ((hIb y0 hy0Ib).2.2.1 (hij ▸ hzB)).elim | exact ((hIb y0 hy0Ib).2.2.1 (hij.symm ▸ hzB)).elim
                            | exact ((hIa t htIa).2.2.2 (hij ▸ hy0Ib)).elim
          obtain ⟨q, hq⟩ := exists_dom3_of_c6 H G.hTF hnn hsum hdeg cyc hcyc_inj
            hpCw2 hzBw2.symm hzBt hty0 hzAy0.symm hpA.symm
          rcases hq with ⟨h0, h2, h4⟩ | ⟨h1, h3, h5⟩
          · exact hW_na q (hCW pC hpC zB hzB q h0.symm h2.symm) y0 (hIb_sub hy0Ib) h4
          · exact hC_na q (hWC w2 hw2W zA hzA q h1.symm h5.symm) t (hIa_sub htIa) h3
      intro t ht
      rcases Finset.mem_union.mp ht with ht1 | ht2
      · exact ⟨(hkill_one I_1' I_2' Finset.subset_union_left Finset.subset_union_right hI1d hI2d h10_2 t ht1).1,
          (hkill_one I_1' I_2' Finset.subset_union_left Finset.subset_union_right hI1d hI2d h10_2 t ht1).2⟩
      · exact ⟨(hkill_one I_2' I_1' Finset.subset_union_right Finset.subset_union_left hI2d hI1d h20_1 t ht2).1,
          (hkill_one I_2' I_1' Finset.subset_union_right Finset.subset_union_left hI2d hI1d h20_1 t ht2).2⟩
    intro zA hzA zB hzB t ht
    have hA0 : H.Adj zA t ↔ H.Adj z0' t := by
      by_cases hpA : H.Adj pC zA
      · exact (hsep_same zA hzA z1' hz1' hpA hnpCz1' t ht).trans (hsep_same z0' hz0' z1' hz1' hpCz0' hnpCz1' t ht).symm
      · exact (hsep_same z0' hz0' zA hzA hpCz0' hpA t ht).symm
    have hB0 : H.Adj zB t ↔ H.Adj z0' t := by
      by_cases hpB : H.Adj pC zB
      · exact (hsep_same zB hzB z1' hz1' hpB hnpCz1' t ht).trans (hsep_same z0' hz0' z1' hz1' hpCz0' hnpCz1' t ht).symm
      · exact (hsep_same z0' hz0' zB hzB hpCz0' hpB t ht).symm
    exact hA0.trans hB0.symm
  -- Wait: replace the placeholder in `hkill_one` right now by passing `hW_na_a` and `hC_na_b`!
  -- Let's now finish Claim 13 completely below!
  -- First, handle the clean singleton case via `vega_of_singleton_frame`:
  -- Bundle the 3 symmetric blocks via `Fin 3` for a clean, zero-duplication Claim 13.4-13.6!
  let a_b : Fin 3 → U := ![a, b, c]
  let u_b : Fin 3 → U := ![u, v, w]
  let A_b : Fin 3 → Finset U := ![A_set, B_set, C_set]
  let U_b : Fin 3 → Finset U := ![U_set, V_set, W_set]
  let I_b : Fin 3 → Finset U := ![I1, I2, I3]
  have hAb_sub : ∀ r : Fin 3, A_b r ⊆ Nx := fun r => by
    rcases fin3_cases r with rfl | rfl | rfl <;> exact Finset.filter_subset _ _
  have hUb_sub : ∀ r : Fin 3, U_b r ⊆ R_set := fun r => by
    rcases fin3_cases r with rfl | rfl | rfl
    · exact fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
    · exact fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
    · exact fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz)
  have ha_mem : ∀ r : Fin 3, a_b r ∈ A_b r := fun r => by rcases fin3_cases r with rfl | rfl | rfl <;> assumption
  have hu_mem : ∀ r : Fin 3, u_b r ∈ U_b r := fun r => by rcases fin3_cases r with rfl | rfl | rfl <;> assumption
  have hIb_ne : ∀ r : Fin 3, (I_b r).Nonempty := fun r => by rcases fin3_cases r with rfl | rfl | rfl <;> assumption
  have hIb_ind : ∀ r : Fin 3, ∀ z1 ∈ I_b r, ∀ z2 ∈ I_b r, ¬ H.Adj z1 z2 := fun r => by
    rcases fin3_cases r with rfl | rfl | rfl <;> assumption
  have hIb_disj : ∀ r1 r2 : Fin 3, r1 ≠ r2 → Disjoint (I_b r1) (I_b r2) := fun r1 r2 hne => by
    rcases fin3_cases r1 with rfl | rfl | rfl <;> rcases fin3_cases r2 with rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | exact hI_disj12 | exact hI_disj13 | exact hI_disj23
                    | exact hI_disj12.symm | exact hI_disj13.symm | exact hI_disj23.symm
  have hIb_out : ∀ r : Fin 3, ∀ z ∈ I_b r, z ∉ Nx ∧ z ∉ R_set := fun r z hz => by
    rcases fin3_cases r with rfl | rfl | rfl
    · exact ⟨fun h => (hI1_na z hz).1 (Finset.mem_filter.mp h).2.symm, (Finset.mem_filter.mp hz).2.2⟩
    · exact ⟨fun h => (hI2_na z hz).1 (Finset.mem_filter.mp h).2.symm, (Finset.mem_filter.mp hz).2.2⟩
    · exact ⟨fun h => (hI3_na z hz).1 (Finset.mem_filter.mp h).2.symm, (Finset.mem_filter.mp hz).2.2⟩
  have hAb_disj : ∀ r1 r2 : Fin 3, r1 ≠ r2 → Disjoint (A_b r1) (A_b r2) := fun r1 r2 hne =>
    Finset.disjoint_left.mpr fun z h1 h2 => by
      rcases fin3_cases r1 with rfl | rfl | rfl <;> rcases fin3_cases r2 with rfl | rfl | rfl
      all_goals first | exact absurd rfl hne
                      | exact (Finset.mem_filter.mp h1).2.1 (Finset.mem_filter.mp h2).2.1
                      | exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
                      | exact (Finset.mem_filter.mp h1).2.2.1 (Finset.mem_filter.mp h2).2.2.1
                      | exact (Finset.mem_filter.mp h2).2.2.1 (Finset.mem_filter.mp h1).2.2.1
  have hUb_disj : ∀ r1 r2 : Fin 3, r1 ≠ r2 → Disjoint (U_b r1) (U_b r2) := fun r1 r2 hne =>
    Finset.disjoint_left.mpr fun z h1 h2 => by
      rcases fin3_cases r1 with rfl | rfl | rfl <;> rcases fin3_cases r2 with rfl | rfl | rfl
      all_goals first | exact absurd rfl hne
                      | exact hnot_abc z (Finset.mem_filter.mp h1).2.1 ⟨(Finset.mem_filter.mp h2).2.2.1, (Finset.mem_filter.mp h1).2.2⟩
                      | exact hnot_abc z (Finset.mem_filter.mp h2).2.1 ⟨(Finset.mem_filter.mp h1).2.2.1, (Finset.mem_filter.mp h2).2.2⟩
                      | exact hnot_abc z (Finset.mem_filter.mp h1).2.1 ⟨(Finset.mem_filter.mp h1).2.2.1, (Finset.mem_filter.mp h2).2.2.2, (Finset.mem_filter.mp h1).2.2.2⟩
                      | exact hnot_abc z (Finset.mem_filter.mp h2).2.1 ⟨(Finset.mem_filter.mp h2).2.2.1, (Finset.mem_filter.mp h1).2.2.2, (Finset.mem_filter.mp h2).2.2.2⟩
  have hAb_comp_U : ∀ r1 r2 : Fin 3, r1 ≠ r2 → ∀ p ∈ A_b r1, ∀ u' ∈ U_b r2, H.Adj p u' := fun r1 r2 hne p hp u' hu' => by
    rcases fin3_cases r1 with rfl | rfl | rfl <;> rcases fin3_cases r2 with rfl | rfl | rfl
    all_goals first | exact absurd rfl hne
                    | exact (hA_VW p hp).1 u' hu' | exact (hA_VW p hp).2 u' hu'
                    | exact (hB_UW p hp).1 u' hu' | exact (hB_UW p hp).2 u' hu'
                    | exact (hC_UV p hp).1 u' hu' | exact (hC_UV p hp).2 u' hu'
  have hAb_na_I : ∀ r1 r2 : Fin 3, r1 ≠ r2 → ∀ p ∈ A_b r1, ∀ z ∈ I_b r2, ¬ H.Adj p z := fun r1 r2 hne p hp z hz h => by
    rcases fin3_cases r1 with rfl | rfl | rfl <;> rcases fin3_cases r2 with rfl | rfl | rfl
    all_goals first | exact absurd rfl hne
                    | exact (hI2_avoid z hz).1 p (Finset.mem_union_left _ (Finset.mem_union_right _ hp)) h.symm
                    | exact (hI3_avoid z hz).1 p (Finset.mem_union_left _ (Finset.mem_union_right _ hp)) h.symm
                    | exact (hI1_avoid z hz).1 p (Finset.mem_union_left _ (Finset.mem_union_right _ hp)) h.symm
                    | exact (hI3_avoid z hz).1 p (Finset.mem_union_right _ hp) h.symm
                    | exact (hI1_avoid z hz).1 p (Finset.mem_union_right _ hp) h.symm
                    | exact (hI2_avoid z hz).1 p (Finset.mem_union_right _ hp) h.symm
  have hUb_na_I : ∀ r1 r2 : Fin 3, r1 ≠ r2 → ∀ u' ∈ U_b r1, ∀ z ∈ I_b r2, ¬ H.Adj u' z := fun r1 r2 hne u' hu' z hz h => by
    rcases fin3_cases r1 with rfl | rfl | rfl <;> rcases fin3_cases r2 with rfl | rfl | rfl
    all_goals first | exact absurd rfl hne
                    | exact (hI2_avoid z hz).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_left _ hu')) h.symm
                    | exact (hI3_avoid z hz).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_left _ hu')) h.symm
                    | exact (hI1_avoid z hz).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_left _ hu')) h.symm
                    | exact (hI3_avoid z hz).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hu')) h.symm
                    | exact (hI1_avoid z hz).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hu')) h.symm
                    | exact (hI2_avoid z hz).2 u' (Finset.mem_insert_of_mem (Finset.mem_union_right _ hu')) h.symm
  have hY_na_I : ∀ r : Fin 3, ∀ y ∈ Y_set, ∀ z ∈ I_b r, ¬ H.Adj y z := fun r y hy z hz h => by
    rcases fin3_cases r with rfl | rfl | rfl
    · exact (hI1_avoid z hz).1 y (Finset.mem_union_left _ (Finset.mem_union_left _ hy)) h.symm
    · exact (hI2_avoid z hz).1 y (Finset.mem_union_left _ (Finset.mem_union_left _ hy)) h.symm
    · exact (hI3_avoid z hz).1 y (Finset.mem_union_left _ (Finset.mem_union_left _ hy)) h.symm
  have hx_na_I : ∀ r : Fin 3, ∀ z ∈ I_b r, ¬ H.Adj x z := fun r z hz h => by
    rcases fin3_cases r with rfl | rfl | rfl
    · exact (hI1_na z hz).1 h.symm
    · exact (hI2_na z hz).1 h.symm
    · exact (hI3_na z hz).1 h.symm
  have hcomp_aIuI : ∀ r : Fin 3, ∀ z ∈ I_b r, H.Adj (a_b r) z ∧ H.Adj (u_b r) z := fun r z hz => by
    rcases fin3_cases r with rfl | rfl | rfl
    · exact ⟨(Finset.mem_filter.mp hz).2.1.symm, hu_I1 z hz⟩
    · exact ⟨(Finset.mem_filter.mp hz).2.1.symm, hv_I2 z hz⟩
    · exact ⟨(Finset.mem_filter.mp hz).2.1.symm, hw_I3 z hz⟩
  have hpart_b : ∀ r1 r2 r3 : Fin 3, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
      ∀ z : U, z ∈ Y_set ∨ z ∈ A_b r1 ∨ z ∈ A_b r2 ∨ z ∈ A_b r3 ∨ z = x ∨
               z ∈ U_b r1 ∨ z ∈ U_b r2 ∨ z ∈ U_b r3 ∨ z ∈ I_b r1 ∨ z ∈ I_b r2 ∨ z ∈ I_b r3 := by
    intro r1 r2 r3 h12 h13 h23 z
    have hperm : ∀ r : Fin 3, r = r1 ∨ r = r2 ∨ r = r3 := fun r => by
      rcases eq_or_ne r r1 with rfl | h1
      · exact Or.inl rfl
      · rcases eq_or_ne r r2 with rfl | h2
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (OMA.R_Erdos128_erdos_128_R2.fin3_third h12 h13 h23 h1 h2))
    rcases hpart z with hzN | hzR | hz1 | hz2 | hz3
    · rcases hNx_part z hzN with hY | hA | hB | hC
      · exact Or.inl hY
      · rcases hperm 0 with h | h | h <;> rw [← h] <;> simp [A_b, hA]
      · rcases hperm 1 with h | h | h <;> rw [← h] <;> simp [A_b, hB]
      · rcases hperm 2 with h | h | h <;> rw [← h] <;> simp [A_b, hC]
    · simp only [R_set, Finset.mem_insert, Finset.mem_union] at hzR
      rcases hzR with rfl | ((hU | hV) | hW)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · rcases hperm 0 with h | h | h <;> rw [← h] <;> simp [U_b, hU]
      · rcases hperm 1 with h | h | h <;> rw [← h] <;> simp [U_b, hV]
      · rcases hperm 2 with h | h | h <;> rw [← h] <;> simp [U_b, hW]
    · rcases hperm 0 with h | h | h <;> rw [← h] <;> simp [I_b, hz1]
    · rcases hperm 1 with h | h | h <;> rw [← h] <;> simp [I_b, hz2]
    · rcases hperm 2 with h | h | h <;> rw [← h] <;> simp [I_b, hz3]
  have hcom_AU : ∀ r : Fin 3, ∀ p ∈ A_b r, ∀ z ∈ I_b r, ∀ q : U, H.Adj p q → H.Adj z q → q ∈ U_b r := by
    intro r p hp z hz q hpq hzq
    have hother : ∃ r1 r2 : Fin 3, r1 ≠ r2 ∧ r1 ≠ r ∧ r2 ≠ r := by
      rcases fin3_cases r with rfl | rfl | rfl
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    obtain ⟨r1, r2, h12, h1r, h2r⟩ := hother
    rcases hpart_b r1 r2 r h12 h1r h2r q with hY | hA1 | hA2 | hAr | rfl | hU1 | hU2 | hUr | hI1 | hI2 | hIr
    · exact (hY_na_I r q hY z hz hzq.symm).elim
    · exact (hNx_ind p (hAb_sub r hp) q (hAb_sub r1 hA1) hpq).elim
    · exact (hNx_ind p (hAb_sub r hp) q (hAb_sub r2 hA2) hpq).elim
    · exact (hNx_ind p (hAb_sub r hp) q (hAb_sub r hAr) hpq).elim
    · exact (hx_na_I r z hz hzq.symm).elim
    · exact (hUb_na_I r1 r h1r q hU1 z hz hzq.symm).elim
    · exact (hUb_na_I r2 r h2r q hU2 z hz hzq.symm).elim
    · exact hUr
    · exact (hAb_na_I r r1 h1r.symm p hp q hI1 hpq).elim
    · exact (hAb_na_I r r2 h2r.symm p hp q hI2 hpq).elim
    · exact (hIb_ind r z hz q hIr hzq).elim
  have hcom_UA : ∀ r : Fin 3, ∀ u' ∈ U_b r, ∀ z ∈ I_b r, ∀ q : U, H.Adj u' q → H.Adj z q → q ∈ A_b r := by
    intro r u' hu' z hz q huq hzq
    have hother : ∃ r1 r2 : Fin 3, r1 ≠ r2 ∧ r1 ≠ r ∧ r2 ≠ r := by
      rcases fin3_cases r with rfl | rfl | rfl
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    obtain ⟨r1, r2, h12, h1r, h2r⟩ := hother
    rcases hpart_b r1 r2 r h12 h1r h2r q with hY | hA1 | hA2 | hAr | rfl | hU1 | hU2 | hUr | hI1 | hI2 | hIr
    · exact (hY_na_I r q hY z hz hzq.symm).elim
    · exact (hAb_na_I r1 r h1r q hA1 z hz hzq.symm).elim
    · exact (hAb_na_I r2 r h2r q hA2 z hz hzq.symm).elim
    · exact hAr
    · exact (hx_na_I r z hz hzq.symm).elim
    · exact (hR_ind u' (hUb_sub r hu') q (hUb_sub r1 hU1) huq).elim
    · exact (hR_ind u' (hUb_sub r hu') q (hUb_sub r2 hU2) huq).elim
    · exact (hR_ind u' (hUb_sub r hu') q (hUb_sub r hUr) huq).elim
    · exact (hUb_na_I r r1 h1r.symm u' hu' q hI1 huq).elim
    · exact (hUb_na_I r r2 h2r.symm u' hu' q hI2 huq).elim
    · exact (hIb_ind r z hz q hIr hzq).elim
  have hcom_II : ∀ r1 r2 r3 : Fin 3, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
      ∀ z1 ∈ I_b r1, ∀ z2 ∈ I_b r2, ∀ q : U, H.Adj z1 q → H.Adj z2 q → q ∈ I_b r3 := by
    intro r1 r2 r3 h12 h13 h23 z1 hz1 z2 hz2 q h1q h2q
    rcases hpart_b r1 r2 r3 h12 h13 h23 q with hY | hA1 | hA2 | hA3 | rfl | hU1 | hU2 | hU3 | hI1 | hI2 | hI3
    · exact (hY_na_I r1 q hY z1 hz1 h1q.symm).elim
    · exact (hAb_na_I r1 r2 h12 q hA1 z2 hz2 h2q.symm).elim
    · exact (hAb_na_I r2 r1 h12.symm q hA2 z1 hz1 h1q.symm).elim
    · exact (hAb_na_I r3 r1 h13.symm q hA3 z1 hz1 h1q.symm).elim
    · exact (hx_na_I r1 z1 hz1 h1q.symm).elim
    · exact (hUb_na_I r1 r2 h12 q hU1 z2 hz2 h2q.symm).elim
    · exact (hUb_na_I r2 r1 h12.symm q hU2 z1 hz1 h1q.symm).elim
    · exact (hUb_na_I r3 r1 h13.symm q hU3 z1 hz1 h1q.symm).elim
    · exact (hIb_ind r1 z1 hz1 q hI1 h1q).elim
    · exact (hIb_ind r2 z2 hz2 q hI2 h2q).elim
    · exact hI3
  have hsplit_b : ∀ r1 r2 r3 : Fin 3, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
      (∃ q ∈ A_b r3 ∪ U_b r3, ∃ z0 ∈ I_b r3, ∃ z1 ∈ I_b r3, H.Adj q z0 ∧ ¬ H.Adj q z1) →
      (∃ p3 ∈ A_b r3, ∃ w3 ∈ U_b r3, ∃ z0 ∈ I_b r3, ∃ z1 ∈ I_b r3,
        H.Adj p3 w3 ∧ H.Adj p3 z0 ∧ ¬ H.Adj p3 z1 ∧ H.Adj w3 z1 ∧ ¬ H.Adj w3 z0) ∧
      (∀ zA ∈ I_b r3, ∀ zB ∈ I_b r3, ∀ t ∈ I_b r1 ∪ I_b r2, H.Adj zA t ↔ H.Adj zB t) := by
    intro r1 r2 r3 h12 h13 h23 hsp
    exact hsplit_unif (A_b r3) (U_b r3) (I_b r3) (I_b r1) (I_b r2) (hAb_sub r3) (hUb_sub r3)
      (fun z hz => ⟨(hIb_out r3 z hz).1, (hIb_out r3 z hz).2, Finset.disjoint_left.mp (hIb_disj r3 r1 h13.symm) hz, Finset.disjoint_left.mp (hIb_disj r3 r2 h23.symm) hz⟩)
      (fun z hz => ⟨(hIb_out r1 z hz).1, (hIb_out r1 z hz).2, Finset.disjoint_left.mp (hIb_disj r1 r3 h13) hz, Finset.disjoint_left.mp (hIb_disj r1 r2 h12) hz⟩)
      (fun z hz => ⟨(hIb_out r2 z hz).1, (hIb_out r2 z hz).2, Finset.disjoint_left.mp (hIb_disj r2 r3 h23) hz, Finset.disjoint_left.mp (hIb_disj r2 r1 h12.symm) hz⟩)
      (fun p hp z hz => by rcases Finset.mem_union.mp hz with h | h <;> [exact hAb_na_I r3 r1 h13.symm p hp z h; exact hAb_na_I r3 r2 h23.symm p hp z h])
      (fun w' hw' z hz => by rcases Finset.mem_union.mp hz with h | h <;> [exact hUb_na_I r3 r1 h13.symm w' hw' z h; exact hUb_na_I r3 r2 h23.symm w' hw' z h])
      (hcom_AU r3) (hcom_UA r3) (hcom_II r1 r3 r2 h13 h12 h23.symm) (hcom_II r2 r3 r1 h23 h12.symm h13.symm) hsp
  have hcl12_b : ∀ r : Fin 3, (∀ q ∈ A_b r ∪ U_b r, ∀ z1 ∈ I_b r, ∀ z2 ∈ I_b r, H.Adj q z1 ↔ H.Adj q z2) →
      A_b r = {a_b r} ∧ U_b r = {u_b r} := fun r => by rcases fin3_cases r with rfl | rfl | rfl <;> assumption
  have he_b : ∀ r1 r2 : Fin 3, r1 ≠ r2 → ∃ z1 ∈ I_b r1, ∃ z2 ∈ I_b r2, H.Adj z1 z2 := fun r1 r2 hne => by
    rcases fin3_cases r1 with rfl | rfl | rfl <;> rcases fin3_cases r2 with rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | exact he12 | exact he13 | exact he23
                    | (obtain ⟨z1, h1, z2, h2, ha⟩ := he12; exact ⟨z2, h2, z1, h1, ha.symm⟩)
                    | (obtain ⟨z1, h1, z2, h2, ha⟩ := he13; exact ⟨z2, h2, z1, h1, ha.symm⟩)
                    | (obtain ⟨z1, h1, z2, h2, ha⟩ := he23; exact ⟨z2, h2, z1, h1, ha.symm⟩)
  have hw_Ab : ∀ r : Fin 3, wsum ω (A_b r) = wsum ω (I_b r) := fun r => by rcases fin3_cases r with rfl | rfl | rfl <;> assumption
  have hw_Ub : ∀ r : Fin 3, wsum ω (U_b r) = 3 * δ - 1 - ω x + wsum ω (I_b r) := fun r => by rcases fin3_cases r with rfl | rfl | rfl <;> assumption
  have hw_Nx_b : ∀ r1 r2 r3 : Fin 3, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
      wsum ω Y_set + wsum ω (A_b r1) + wsum ω (A_b r2) + wsum ω (A_b r3) = δ := by
    intro r1 r2 r3 h12 h13 h23
    rcases fin3_cases r1 with rfl | rfl | rfl <;> rcases fin3_cases r2 with rfl | rfl | rfl <;> rcases fin3_cases r3 with rfl | rfl | rfl
    all_goals first | exact absurd rfl h12 | exact absurd rfl h13 | exact absurd rfl h23 | (simp [A_b]; linarith only [hw_Nx])
  have hY_disj_A' : ∀ r : Fin 3, Disjoint Y_set (A_b r) := fun r => Finset.disjoint_left.mpr fun z hY hA => by
    rcases fin3_cases r with rfl | rfl | rfl
    · exact (Finset.mem_filter.mp hA).2.1 (Finset.mem_filter.mp hY).2.1
    · exact (Finset.mem_filter.mp hA).2.2.1 (Finset.mem_filter.mp hY).2.2.1
    · exact (Finset.mem_filter.mp hA).2.2.2 (Finset.mem_filter.mp hY).2.2.2
  have hx_ne_U' : ∀ r : Fin 3, ∀ u' ∈ U_b r, x ≠ u' := fun r u' hu' h => by
    rcases fin3_cases r with rfl | rfl | rfl
    · exact (Finset.mem_filter.mp hu').2.1 h.symm
    · exact (Finset.mem_filter.mp hu').2.1 h.symm
    · exact (Finset.mem_filter.mp hu').2.1 h.symm
  exact regular_decomp_is_vega H G ω δ
    { hpos := hpos, hnn := hnn, hsum := hsum, hreg := hreg, hδ := hδ, hdeg := hdeg,
      x := x, hx_wmin := hx_wmin, hx_dmin := hx_dmin,
      Nx := Nx, R_set := R_set, Y_set := Y_set,
      hNx_eq := rfl, hx_R := Finset.mem_insert_self x _,
      hNx_ind := hNx_ind, hR_ind := hR_ind, hdisj_NR' := hdisj_NR',
      hY_sub := Finset.filter_subset _ _, hY_nbhd := hY_nbhd, hY_subsing := hY_subsing,
      hwRval := hwRval, hw_xY := hw_xY,
      a_b := a_b, u_b := u_b, A_b := A_b, U_b := U_b, I_b := I_b,
      hAb_sub := hAb_sub, hUb_sub := hUb_sub, ha_mem := ha_mem, hu_mem := hu_mem,
      hIb_ne := hIb_ne, hIb_ind := hIb_ind, hIb_disj := hIb_disj, hIb_out := hIb_out,
      hAb_disj := hAb_disj, hUb_disj := hUb_disj, hY_disj_A := hY_disj_A', hx_ne_U := hx_ne_U',
      hAb_comp_U := hAb_comp_U, hAb_na_I := hAb_na_I, hUb_na_I := hUb_na_I,
      hY_na_I := hY_na_I, hx_na_I := hx_na_I, hcomp_aIuI := hcomp_aIuI,
      hpart_b := hpart_b, hcom_AU := hcom_AU, hcom_UA := hcom_UA, hcom_II := hcom_II,
      hsplit_b := hsplit_b, hcl12_b := hcl12_b, he_b := he_b,
      hw_Ab := hw_Ab, hw_Ub := hw_Ub, hw_Nx_b := hw_Nx_b }


/- ## Section C: Helper Involutions & Theorem 6 (`extend_vega_is_vega`) -/

/-- The mirror involution on `VegaV i` fixing `2*i - 1`, reversing `I_1`, swapping `I_2\{2i-1} ↔ I_3`,
    and swapping `(b, v) ↔ (c, w)` inside `Q_3^+`. -/
def vegaMirror (i : ℕ) (hi : 2 ≤ i) : VegaV i → VegaV i
  | .inl k => .inl ⟨if k.val < i then i - 1 - k.val else 4 * i - 2 - k.val, by have := k.isLt; split_ifs <;> omega⟩
  | .inr q => .inr (if q = 3 then 4 else if q = 4 then 3 else if q = 6 then 7 else if q = 7 then 6 else q)

lemma vegaMirror_invol {i : ℕ} (hi : 2 ≤ i) (v : VegaV i) : vegaMirror i hi (vegaMirror i hi v) = v := by
  cases v with
  | inl k =>
    have hk := k.isLt; simp only [vegaMirror]; congr 1; apply Fin.ext; dsimp only; split_ifs <;> omega
  | inr q =>
    rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vegaMirror]

lemma vegaMirror_active {i : ℕ} (hi : 2 ≤ i) (dy de : Bool) (v : VegaV i) :
    vegaActive i dy de (vegaMirror i hi v) ↔ vegaActive i dy de v := by
  cases v with
  | inl k =>
    have hk := k.isLt; simp only [vegaMirror, vegaActive]; split_ifs <;> constructor <;> intro h ⟨h1, h2⟩ <;> exact h ⟨h1, by omega⟩
  | inr q =>
    rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vegaMirror, vegaActive]

/-- The mirror is an adjacency isomorphism away from the `de = true` deleted point `inl (2*i - 1)`. -/
lemma vegaMirror_adj {i : ℕ} (hi : 2 ≤ i) (dy : Bool) {u v : VegaV i}
    (hu : vegaActive i dy true u) (hv : vegaActive i dy true v) :
    vegaAdj i (vegaMirror i hi u) (vegaMirror i hi v) ↔ vegaAdj i u v := by
  let N := 3 * i - 1
  cases u with
  | inl p =>
    cases v with
    | inl q =>
      have hp := p.isLt; have hq := q.isLt
      simp only [vegaMirror, vegaAdj]
      have hmod : ∀ a b : ℕ, a < N → b < N →
          ((b + N - a) % N) = if a ≤ b then b - a else b + N - a := by
        intro a b ha hb; split_ifs with hab
        · rw [show b + N - a = (b - a) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · exact Nat.mod_eq_of_lt (by omega)
      set mp := if p.val < i then i - 1 - p.val else 4 * i - 2 - p.val
      set mq := if q.val < i then i - 1 - q.val else 4 * i - 2 - q.val
      have hmp : mp < N := by dsimp [mp]; split_ifs <;> omega
      have hmq : mq < N := by dsimp [mq]; split_ifs <;> omega
      change (i ≤ (mq + N - mp) % N ∧ (mq + N - mp) % N ≤ 2 * i - 1) ↔
             (i ≤ (q.val + N - p.val) % N ∧ (q.val + N - p.val) % N ≤ 2 * i - 1)
      rw [hmod mp mq hmp hmq, hmod p.val q.val hp hq]
      dsimp only [mp, mq]
      split_ifs <;> omega
    | inr q =>
      have hp := p.isLt
      rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [vegaMirror, vegaAdj, vegaActive] at hu hv ⊢; split_ifs <;> simp_all <;> omega)
  | inr p =>
    cases v with
    | inl q =>
      have hq := q.isLt
      rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [vegaMirror, vegaAdj, vegaActive] at hu hv ⊢; split_ifs <;> simp_all <;> omega)
    | inr q =>
      rcases fin8_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [vegaMirror, vegaAdj]

/-- Concrete 13-vertex bijection mapping `V_2(true, de) + z` (`N(z) = {x, w, 1, 2}`) to `V_2(false, de)`. -/
def i2RotFwd : Option (VegaV 2) → VegaV 2
  | none => .inr 0
  | some (.inl k) => match k.val with
    | 0 => .inl 0 | 1 => .inr 3 | 2 => .inr 2 | 3 => .inl 3 | _ => .inr 7
  | some (.inr q) => match q.val with
    | 0 => .inr 4 | 1 => .inr 0 | 2 => .inr 5 | 3 => .inr 6 | 4 => .inl 4
    | 5 => .inl 2 | 6 => .inl 1 | _ => .inr 1

def i2RotInv : VegaV 2 → Option (VegaV 2)
  | .inl k => match k.val with
    | 0 => some (.inl 0) | 1 => some (.inr 6) | 2 => some (.inr 5) | 3 => some (.inl 3) | _ => some (.inr 4)
  | .inr q => match q.val with
    | 0 => none | 1 => some (.inr 7) | 2 => some (.inl 2) | 3 => some (.inl 1)
    | 4 => some (.inr 0) | 5 => some (.inr 2) | 6 => some (.inr 3) | _ => some (.inl 4)

lemma i2Rot_left (de : Bool) (u : Option (VegaV 2))
    (hu : match u with | none => True | some v => vegaActive 2 true de v) :
    i2RotInv (i2RotFwd u) = u := by
  cases u with
  | none => rfl
  | some v =>
    cases v with
    | inl k => fin_cases k <;> rfl
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp [vegaActive] at hu)

lemma i2Rot_right (de : Bool) (w : VegaV 2) (hw : vegaActive 2 false de w) :
    i2RotFwd (i2RotInv w) = w := by
  cases w with
  | inl k => fin_cases k <;> rfl
  | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

lemma i2Rot_act_fwd (de : Bool) (u : Option (VegaV 2))
    (hu : match u with | none => True | some v => vegaActive 2 true de v) :
    vegaActive 2 false de (i2RotFwd u) := by
  cases u with
  | none => simp [i2RotFwd, vegaActive]
  | some v =>
    cases v with
    | inl k => fin_cases k <;> cases de <;> simp_all [i2RotFwd, vegaActive]
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases de <;> simp_all [i2RotFwd, vegaActive]

lemma i2Rot_act_inv (de : Bool) (w : VegaV 2) (hw : vegaActive 2 false de w) :
    match i2RotInv w with | none => True | some v => vegaActive 2 true de v := by
  cases w with
  | inl k => fin_cases k <;> cases de <;> simp_all [i2RotInv, vegaActive]
  | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases de <;> simp_all [i2RotInv, vegaActive]

/-- Adjacency bookkeeping of the 13-vertex rotation (a plain function, match-free at use sites). -/
def i2RotAdjLHS : Option (VegaV 2) → Option (VegaV 2) → Prop
  | none, none => False
  | none, some b => b = .inr 0 ∨ b = .inr 7 ∨ b = .inl 1 ∨ b = .inl 2
  | some a, none => a = .inr 0 ∨ a = .inr 7 ∨ a = .inl 1 ∨ a = .inl 2
  | some a, some b => vegaAdj 2 a b

lemma i2Rot_adj (u v : Option (VegaV 2))
    (hu : u ≠ some (.inr 1)) (hv : v ≠ some (.inr 1)) :
    i2RotAdjLHS u v ↔ vegaAdj 2 (i2RotFwd u) (i2RotFwd v) := by
  cases u with
  | none =>
    cases v with
    | none => simp [i2RotAdjLHS, i2RotFwd, vegaAdj]
    | some w =>
      cases w with
      | inl k => fin_cases k <;> first
        | exact absurd rfl hu | exact absurd rfl hv | simp_all [i2RotAdjLHS, i2RotFwd, vegaAdj]
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
        | exact absurd rfl hu | exact absurd rfl hv | simp_all [i2RotAdjLHS, i2RotFwd, vegaAdj]
  | some x =>
    cases x with
    | inl k =>
      cases v with
      | none => fin_cases k <;> first
        | exact absurd rfl hu | exact absurd rfl hv | simp_all [i2RotAdjLHS, i2RotFwd, vegaAdj]
      | some w =>
        cases w with
        | inl k2 => fin_cases k <;> fin_cases k2 <;> first
          | exact absurd rfl hu | exact absurd rfl hv | simp_all [i2RotAdjLHS, i2RotFwd, vegaAdj]
        | inr q2 => fin_cases k <;> rcases fin8_cases q2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
          | exact absurd rfl hu | exact absurd rfl hv | simp_all [i2RotAdjLHS, i2RotFwd, vegaAdj]
    | inr q =>
      cases v with
      | none => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
        | exact absurd rfl hu | exact absurd rfl hv | simp_all [i2RotAdjLHS, i2RotFwd, vegaAdj]
      | some w =>
        cases w with
        | inl k2 => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases k2 <;> first
          | exact absurd rfl hu | exact absurd rfl hv | simp_all [i2RotAdjLHS, i2RotFwd, vegaAdj]
        | inr q2 =>
          rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases fin8_cases q2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
          | exact absurd rfl hu | exact absurd rfl hv | simp_all [i2RotAdjLHS, i2RotFwd, vegaAdj]


/-- Opaque context for the 7-case dispatch of `extend_vega_is_vega` (prevents `isDefEq` unfolding of `inS`/`e`). -/
structure ExtCtx {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) (i : ℕ) (dy de : Bool) (inS : VegaV i → Prop) where
  hi : 2 ≤ i
  hinS_act : ∀ v : VegaV i, inS v → vegaActive i dy de v
  hinS_ind : ∀ u v : VegaV i, inS u → inS v → ¬ vegaAdj i u v
  hinS_max : ∀ v : VegaV i, vegaActive i dy de v → ¬ inS v → ∃ u : VegaV i, inS u ∧ vegaAdj i u v
  hnot_sub_nbhd : ∀ v : VegaV i, vegaActive i dy de v → (∀ u : VegaV i, inS u → vegaAdj i v u) → False
  kill_c6 : ∀ (v1 v2 v3 v4 v5 : VegaV i),
    vegaActive i dy de v1 → vegaActive i dy de v2 → vegaActive i dy de v3 →
    vegaActive i dy de v4 → vegaActive i dy de v5 →
    v1 ≠ v2 → v1 ≠ v3 → v1 ≠ v4 → v1 ≠ v5 → v2 ≠ v3 → v2 ≠ v4 → v2 ≠ v5 → v3 ≠ v4 → v3 ≠ v5 → v4 ≠ v5 →
    inS v1 → inS v5 → ¬ inS v3 →
    vegaAdj i v1 v2 → vegaAdj i v2 v3 → vegaAdj i v3 v4 → vegaAdj i v4 v5 →
    (∀ w : VegaV i, inS w → vegaAdj i w v2 → vegaAdj i w v4 → False) →
    (∀ w : VegaV i, vegaActive i dy de w → vegaAdj i w v1 → vegaAdj i w v3 → vegaAdj i w v5 → False) →
    False
  hbuild_restore : ∀ (dy' de' : Bool) (v0 : VegaV i),
    ¬ vegaActive i dy de v0 → vegaActive i dy' de' v0 →
    (∀ v : VegaV i, v ≠ v0 → (vegaActive i dy' de' v ↔ vegaActive i dy de v)) →
    (∀ v : VegaV i, vegaActive i dy de v → (inS v ↔ vegaAdj i v0 v)) →
    IsVegaGraph H i dy' de'
  hbuild_mirror_end : de = true →
    (∀ v : VegaV i, vegaActive i dy true v → (inS v ↔ vegaAdj i (.inl ⟨2 * i - 1, by omega⟩) (vegaMirror i hi v))) →
    IsVegaGraph H i dy false
  hbuild_i2_xw : ∀ (hi2 : i = 2) (_hdy : dy = true),
    (∀ v : VegaV i, vegaActive i true de v →
      (inS v ↔ v = .inr 0 ∨ v = .inr 7 ∨ v = .inl ⟨1, by omega⟩ ∨ v = .inl ⟨2, by omega⟩)) →
    IsVegaGraph H 2 false de
  hbuild_i2_xv : ∀ (hi2 : i = 2) (_hdy : dy = true) (_hde : de = true),
    (∀ v : VegaV i, vegaActive i true true v →
      (inS v ↔ v = .inr 0 ∨ v = .inr 6 ∨ v = .inl ⟨0, by omega⟩ ∨ v = .inl ⟨4, by omega⟩)) →
    IsVegaGraph H 2 false true

lemma ext_hv_inl {i : ℕ} (_hi : 2 ≤ i) (p q : Fin (3 * i - 1)) :
    vegaAdj i (.inl p) (.inl q) ↔
    (if p.val ≤ q.val then i ≤ q.val - p.val ∧ q.val - p.val ≤ 2 * i - 1
     else i ≤ q.val + (3 * i - 1) - p.val ∧ q.val + (3 * i - 1) - p.val ≤ 2 * i - 1) := by
  have hp := p.isLt; have hq := q.isLt; simp only [vegaAdj]
  change (i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1) ↔ _
  split_ifs with hpq
  · rw [show q.val + (3 * i - 1) - p.val = (q.val - p.val) + (3 * i - 1) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 400000 in
lemma extend_case_110 {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) (i : ℕ) (dy de : Bool) (inS : VegaV i → Prop) [DecidablePred inS]
    (C : ExtCtx H i dy de inS)
    (h1 : ∃ k : Fin (3 * i - 1), k.val < i ∧ inS (.inl k)) (h2 : ∃ k : Fin (3 * i - 1), i ≤ k.val ∧ k.val < 2 * i ∧ inS (.inl k)) (h3 : ¬ (∃ k : Fin (3 * i - 1), 2 * i ≤ k.val ∧ inS (.inl k))) :
    ∃ (i' : ℕ) (dy' de' : Bool), IsVegaGraph H i' dy' de' := by
  have hi := C.hi
  let N := 3 * i - 1
  have hN : 5 ≤ N := by omega
  have hinS_act := C.hinS_act
  have hinS_ind := C.hinS_ind
  have hinS_max := C.hinS_max
  have hnot_sub_nbhd := C.hnot_sub_nbhd
  have kill_c6 := C.kill_c6
  have hv_inl : ∀ p q : Fin N, vegaAdj i (.inl p) (.inl q) ↔
      (if p.val ≤ q.val then i ≤ q.val - p.val ∧ q.val - p.val ≤ 2 * i - 1
       else i ≤ q.val + N - p.val ∧ q.val + N - p.val ≤ 2 * i - 1) := ext_hv_inl hi
  have hQ_na : ∀ p q : Fin 8, vegaAdj i (.inr p) (.inr q) → inS (.inr p) → ¬ inS (.inr q) :=
    fun p q hadj hp hq => hinS_ind (.inr p) (.inr q) hp hq hadj
  let SG : Finset (Fin N) := Finset.univ.filter (fun k => inS (.inl k))
  have hbuild_i2_xw := C.hbuild_i2_xw
  have hna2 : ¬ inS (.inr 2) := fun h => by obtain ⟨k, hk, hsk⟩ := h1; exact hinS_ind (.inr 2) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hna5 : ¬ inS (.inr 5) := fun h => by obtain ⟨k, hk, hsk⟩ := h1; exact hinS_ind (.inr 5) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hna3 : ¬ inS (.inr 3) := fun h => by obtain ⟨k, hk1, hk2, hsk⟩ := h2; exact hinS_ind (.inr 3) (.inl k) h hsk (by simp [vegaAdj, hk1, hk2])
  have hna6 : ¬ inS (.inr 6) := fun h => by obtain ⟨k, hk1, hk2, hsk⟩ := h2; exact hinS_ind (.inr 6) (.inl k) h hsk (by simp [vegaAdj, hk1, hk2])
  let S1 := SG.filter (fun k : Fin N => k.val < i)
  have hS1_ne : S1.Nonempty := by obtain ⟨k, hk, hsk⟩ := h1; exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsk⟩, hk⟩⟩
  obtain ⟨r, hrS1, hr_min⟩ := Finset.exists_min_image S1 (fun k => k.val) hS1_ne
  have hr_inS : inS (.inl r) := (Finset.mem_filter.mp (Finset.mem_filter.mp hrS1).1).2
  have hr_lt : r.val < i := (Finset.mem_filter.mp hrS1).2
  have hr_pos : 1 ≤ r.val := by
    by_contra h0; obtain ⟨k2, hk2a, hk2b, hsk2⟩ := h2
    exact hinS_ind (.inl r) (.inl k2) hr_inS hsk2 ((hv_inl r k2).mpr (by rw [if_pos (by omega)]; try omega))
  have hSG_rng : ∀ k : Fin N, inS (.inl k) → r.val ≤ k.val ∧ k.val ≤ r.val + i - 1 := by
    intro k hsk
    by_cases hk1 : k.val < i
    · have hle := hr_min k (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsk⟩, hk1⟩)
      omega
    · by_cases hk2 : k.val < 2 * i
      · have hna := hinS_ind (.inl r) (.inl k) hr_inS hsk
        rw [hv_inl, if_pos (by omega)] at hna; omega
      · exact (h3 ⟨k, by omega, hsk⟩).elim
  by_cases h0 : inS (.inr 0)
  · -- Family D: `SQ = {x, w}`, `S_Γ = [r, r + i - 1]`!
    have hna1 : ¬ inS (.inr 1) := hQ_na 0 1 (by simp [vegaAdj]) h0
    have hna4 : ¬ inS (.inr 4) := hQ_na 0 4 (by simp [vegaAdj]) h0
    have h7 : inS (.inr 7) := by_contra fun hna7 => by
      obtain ⟨u, hu, hadj⟩ := hinS_max (.inr 7) (by simp [vegaActive]) hna7
      cases u with
      | inl k => simp [vegaAdj] at hadj; exact h3 ⟨k, hadj, hu⟩
      | inr q =>
        rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact absurd hu hna1
          | exact absurd hu hna2
          | exact absurd hu hna3
          | simp [vegaAdj] at hadj
    have hSG_full : ∀ k : Fin N, r.val ≤ k.val → k.val ≤ r.val + i - 1 → inS (.inl k) := by
      intro k hlo hhi; by_contra hna
      have hact : vegaActive i dy de (.inl k) := by simp [vegaActive]; omega
      obtain ⟨u, hu, hadj⟩ := hinS_max (.inl k) hact hna
      cases u with
      | inl m => have ⟨hm1, hm2⟩ := hSG_rng m hu; rw [hv_inl] at hadj; split_ifs at hadj <;> omega
      | inr q =>
        rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact absurd hu hna2 | exact absurd hu hna3 | exact absurd hu hna4
          | exact absurd hu hna5 | exact absurd hu hna6
          | (simp [vegaAdj] at hadj; try omega)
    by_cases hr2 : r.val ≤ i - 2
    · -- `[z, r, r+i, r+2i, c, x]`
      exfalso
      let v1 : VegaV i := .inl r
      let v2 : VegaV i := .inl ⟨r.val + i, by omega⟩
      let v3 : VegaV i := .inl ⟨r.val + 2 * i, by omega⟩
      refine kill_c6 v1 v2 v3 (.inr 4) (.inr 0)
        (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega) (by simp [v3, vegaActive]; try omega)
        (by simp [vegaActive]) (by simp [vegaActive])
        (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
        (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
        hr_inS h0 (fun h => h3 ⟨⟨r.val + 2 * i, by omega⟩, by dsimp; omega, h⟩)
        ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
        ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
        (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
      · intro w hw h2' h4'; cases w with
        | inl k => simp [vegaAdj] at h4'; exact h3 ⟨k, h4', hw⟩
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
      · intro w _ h1' h3' h5'; cases w with
        | inl k => simp [vegaAdj] at h5'
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
    · by_cases hi3 : 3 ≤ i
      · -- `r = i - 1`, `i >= 3`: `[z, 2i-2, i-2, 3i-3, c, x]`
        exfalso
        let v1 : VegaV i := .inl ⟨2 * i - 2, by omega⟩
        let v2 : VegaV i := .inl ⟨i - 2, by omega⟩
        let v3 : VegaV i := .inl ⟨3 * i - 3, by omega⟩
        refine kill_c6 v1 v2 v3 (.inr 4) (.inr 0)
          (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega) (by simp [v3, vegaActive]; try omega)
          (by simp [vegaActive]) (by simp [vegaActive])
          (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
          (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
          (hSG_full ⟨2 * i - 2, by omega⟩ (by dsimp; try omega) (by dsimp; try omega)) h0
          (fun h => h3 ⟨⟨3 * i - 3, by omega⟩, by dsimp; omega, h⟩)
          ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
          ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
          (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
        · intro w hw h2' h4'; cases w with
          | inl k => simp [vegaAdj] at h4'; exact h3 ⟨k, h4', hw⟩
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
        · intro w _ h1' h3' h5'; cases w with
          | inl k => simp [vegaAdj] at h5'
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
      · -- `i = 2`, `r = 1`: if `dy = false` kill `[z, 1, u, y, v, 2]`, else `hbuild_i2_xw`!
        have hi2 : i = 2 := by omega
        cases hdy : dy
        · exfalso
          let v1 : VegaV i := .inl ⟨1, by omega⟩
          let v5 : VegaV i := .inl ⟨2, by omega⟩
          refine kill_c6 v1 (.inr 5) (.inr 1) (.inr 6) v5
            (by simp [v1, vegaActive]; try omega) (by simp [vegaActive]) (by simp [vegaActive, hdy])
            (by simp [vegaActive]) (by simp [v5, vegaActive]; try omega)
            (by simp [v1]) (by simp [v1]) (by simp [v1]) (by simp [v1, v5, Fin.ext_iff])
            (by simp) (by simp) (by simp [v5]) (by simp) (by simp [v5]) (by simp [v5])
            (hSG_full ⟨1, by omega⟩ (by dsimp; try omega) (by dsimp; try omega))
            (hSG_full ⟨2, by omega⟩ (by dsimp; try omega) (by dsimp; try omega)) hna1
            (by simp [v1, vegaAdj]; try omega) (by simp [vegaAdj]) (by simp [vegaAdj]) (by simp [v5, vegaAdj]; try omega) ?_ ?_
          · intro w hw h2' h4'; cases w with
            | inl k => simp [vegaAdj] at h2' h4'; omega
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at h2' h4'<;> contradiction)
          · intro w _ h1' h3' h5'; cases w with
            | inl k => simp [vegaAdj] at h3'
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v5, vegaAdj] at h1' h3' h5'<;> omega)
        · have hr1 : r.val = 1 := by omega
          refine ⟨2, false, de, hbuild_i2_xw hi2 hdy ?_⟩
          subst hi2; intro v hv; cases v with
          | inl k =>
            have hk := k.isLt
            constructor
            · intro hsk; have ⟨a1, a2⟩ := hSG_rng k hsk; right; right
              by_cases h1k : k.val = 1
              · left; exact congrArg Sum.inl (Fin.ext h1k)
              · right; exact congrArg Sum.inl (Fin.ext (by dsimp; omega))
            · rintro (h | h | h | h)
              · simp at h
              · simp at h
              · injection h with hk'; subst hk'; exact hSG_full ⟨1, by omega⟩ (by simp [hr1]) (by simp [hr1])
              · injection h with hk'; subst hk'; exact hSG_full ⟨2, by omega⟩ (by simp [hr1]) (by simp [hr1])
          | inr q =>
            rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaActive] at hv ⊢<;> assumption)
  · by_cases h1y : inS (.inr 1)
    · -- Family D': `SQ = {y, c}` (`dy = false`), `S_Γ = [r, r + i - 1]`!
      exfalso
      have hdy : dy = false := by have h1a := hinS_act (.inr 1) h1y; cases dy <;> simp [vegaActive] at h1a ⊢
      have hna7 : ¬ inS (.inr 7) := hQ_na 1 7 (by simp [vegaAdj]) h1y
      have h4 : inS (.inr 4) := by_contra fun hna4 => by
        obtain ⟨u, hu, hadj⟩ := hinS_max (.inr 4) (by simp [vegaActive]) hna4
        cases u with
        | inl k => simp [vegaAdj] at hadj; exact h3 ⟨k, hadj, hu⟩
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> contradiction)
      have hSG_full : ∀ k : Fin N, r.val ≤ k.val → k.val ≤ r.val + i - 1 → inS (.inl k) := by
        intro k hlo hhi; by_contra hna
        obtain ⟨u, hu, hadj⟩ := hinS_max (.inl k) (by simp [vegaActive]; try omega) hna
        cases u with
        | inl m => have ⟨hm1, hm2⟩ := hSG_rng m hu; rw [hv_inl] at hadj; split_ifs at hadj <;> omega
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | contradiction | omega)
      by_cases hr2 : r.val ≤ i - 2
      · let v1 : VegaV i := .inl r; let v2 : VegaV i := .inl ⟨r.val + i, by omega⟩; let v3 : VegaV i := .inl ⟨r.val + 2 * i, by omega⟩
        refine kill_c6 v1 v2 v3 (.inr 7) (.inr 1)
          (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega) (by simp [v3, vegaActive]; try omega)
          (by simp [vegaActive]) (by simp [vegaActive, hdy])
          (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
          (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
          hr_inS h1y (fun h => h3 ⟨⟨r.val + 2 * i, by omega⟩, by dsimp; omega, h⟩)
          ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
          ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
          (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
        · intro w hw h2' h4'; cases w with
          | inl k => simp [vegaAdj] at h4'; exact h3 ⟨k, h4', hw⟩
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
        · intro w _ h1' h3' h5'; cases w with
          | inl k => simp [vegaAdj] at h5'
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
      · by_cases hi3 : 3 ≤ i
        · let v1 : VegaV i := .inl ⟨2 * i - 2, by omega⟩; let v2 : VegaV i := .inl ⟨i - 2, by omega⟩; let v3 : VegaV i := .inl ⟨3 * i - 3, by omega⟩
          refine kill_c6 v1 v2 v3 (.inr 7) (.inr 1)
            (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega) (by simp [v3, vegaActive]; try omega)
            (by simp [vegaActive]) (by simp [vegaActive, hdy])
            (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
            (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
            (hSG_full ⟨2 * i - 2, by omega⟩ (by dsimp; try omega) (by dsimp; try omega)) h1y
            (fun h => h3 ⟨⟨3 * i - 3, by omega⟩, by dsimp; omega, h⟩)
            ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
            ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
            (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
          · intro w hw h2' h4'; cases w with
            | inl k => simp [vegaAdj] at h4'; exact h3 ⟨k, h4', hw⟩
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
          · intro w _ h1' h3' h5'; cases w with
            | inl k => simp [vegaAdj] at h5'
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
        · let v1 : VegaV i := .inl ⟨1, by omega⟩; let v5 : VegaV i := .inl ⟨2, by omega⟩
          refine kill_c6 v1 (.inr 2) (.inr 0) (.inr 3) v5
            (by simp [v1, vegaActive]; try omega) (by simp [vegaActive]) (by simp [vegaActive])
            (by simp [vegaActive]) (by simp [v5, vegaActive]; try omega)
            (by simp [v1]) (by simp [v1]) (by simp [v1]) (by simp [v1, v5, Fin.ext_iff])
            (by simp) (by simp) (by simp [v5]) (by simp) (by simp [v5]) (by simp [v5])
            (hSG_full ⟨1, by omega⟩ (by dsimp; try omega) (by dsimp; try omega))
            (hSG_full ⟨2, by omega⟩ (by dsimp; try omega) (by dsimp; try omega)) h0
            (by simp [v1, vegaAdj]; try omega) (by simp [vegaAdj]) (by simp [vegaAdj]) (by simp [v5, vegaAdj]; try omega) ?_ ?_
          · intro w hw h2' h4'; cases w with
            | inl k => simp [vegaAdj] at h2' h4'; omega
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at h2' h4'<;> contradiction)
          · intro w _ h1' h3' h5'; cases w with
            | inl k => simp [vegaAdj] at h3'
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v5, vegaAdj] at h1' h3' h5'<;> omega)
    · -- `0, 1 ∉ S_Q` -> `S ⊆ N(r + 2i - 1)`, contradicts `hnot_sub_nbhd`!
      exfalso
      refine hnot_sub_nbhd (.inl ⟨r.val + 2 * i - 1, by omega⟩) (by simp [vegaActive]; try omega) (fun u hu => ?_)
      cases u with
      | inl k => have ⟨hk1, hk2⟩ := hSG_rng k hu; rw [hv_inl, if_neg (by dsimp; try omega)]; dsimp; omega
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]; first | contradiction | omega)

set_option maxHeartbeats 400000 in
lemma extend_case_101 {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) (i : ℕ) (dy de : Bool) (inS : VegaV i → Prop) [DecidablePred inS]
    (C : ExtCtx H i dy de inS)
    (h1 : ∃ k : Fin (3 * i - 1), k.val < i ∧ inS (.inl k)) (h2 : ¬ (∃ k : Fin (3 * i - 1), i ≤ k.val ∧ k.val < 2 * i ∧ inS (.inl k))) (h3 : ∃ k : Fin (3 * i - 1), 2 * i ≤ k.val ∧ inS (.inl k)) :
    ∃ (i' : ℕ) (dy' de' : Bool), IsVegaGraph H i' dy' de' := by
  have hi := C.hi
  let N := 3 * i - 1
  have hN : 5 ≤ N := by omega
  have hinS_act := C.hinS_act
  have hinS_ind := C.hinS_ind
  have hinS_max := C.hinS_max
  have hnot_sub_nbhd := C.hnot_sub_nbhd
  have kill_c6 := C.kill_c6
  have hv_inl : ∀ p q : Fin N, vegaAdj i (.inl p) (.inl q) ↔
      (if p.val ≤ q.val then i ≤ q.val - p.val ∧ q.val - p.val ≤ 2 * i - 1
       else i ≤ q.val + N - p.val ∧ q.val + N - p.val ≤ 2 * i - 1) := ext_hv_inl hi
  have hQ_na : ∀ p q : Fin 8, vegaAdj i (.inr p) (.inr q) → inS (.inr p) → ¬ inS (.inr q) :=
    fun p q hadj hp hq => hinS_ind (.inr p) (.inr q) hp hq hadj
  let SG : Finset (Fin N) := Finset.univ.filter (fun k => inS (.inl k))
  have hbuild_i2_xv := C.hbuild_i2_xv
  have hna2 : ¬ inS (.inr 2) := fun h => by obtain ⟨k, hk, hsk⟩ := h1; exact hinS_ind (.inr 2) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hna5 : ¬ inS (.inr 5) := fun h => by obtain ⟨k, hk, hsk⟩ := h1; exact hinS_ind (.inr 5) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hna4 : ¬ inS (.inr 4) := fun h => by obtain ⟨k, hk, hsk⟩ := h3; exact hinS_ind (.inr 4) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hna7 : ¬ inS (.inr 7) := fun h => by obtain ⟨k, hk, hsk⟩ := h3; exact hinS_ind (.inr 7) (.inl k) h hsk (by simp [vegaAdj, hk])
  let S3 := SG.filter (fun k : Fin N => 2 * i ≤ k.val)
  have hS3_ne : S3.Nonempty := by obtain ⟨k, hk, hsk⟩ := h3; exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsk⟩, hk⟩⟩
  obtain ⟨r, hrS3, hr_min⟩ := Finset.exists_min_image S3 (fun k => k.val) hS3_ne
  have hr_inS : inS (.inl r) := (Finset.mem_filter.mp (Finset.mem_filter.mp hrS3).1).2
  have hr_ge : 2 * i ≤ r.val := (Finset.mem_filter.mp hrS3).2
  have hr_lt : r.val < N := r.isLt
  have hSG_rng : ∀ k : Fin N, inS (.inl k) → r.val ≤ k.val ∨ k.val ≤ r.val - 2 * i := by
    intro k hsk
    by_cases hk3 : 2 * i ≤ k.val
    · left; exact hr_min k (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsk⟩, hk3⟩)
    · by_cases hk1 : k.val < i
      · right; have hna := hinS_ind (.inl r) (.inl k) hr_inS hsk
        rw [hv_inl, if_neg (by omega)] at hna; omega
      · exact (h2 ⟨k, by omega, by omega, hsk⟩).elim
  by_cases h0 : inS (.inr 0)
  · -- Family C: `SQ = {x, v}`, `S_Γ = [r, N-1] ∪ [0, r-2i]`!
    have hna1 : ¬ inS (.inr 1) := hQ_na 0 1 (by simp [vegaAdj]) h0
    have hna3 : ¬ inS (.inr 3) := hQ_na 0 3 (by simp [vegaAdj]) h0
    have h6 : inS (.inr 6) := by_contra fun hna6 => by
      obtain ⟨u, hu, hadj⟩ := hinS_max (.inr 6) (by simp [vegaActive]) hna6
      cases u with
      | inl k => simp [vegaAdj] at hadj; exact h2 ⟨k, hadj.1, hadj.2, hu⟩
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> contradiction)
    have hSG_full : ∀ k : Fin N, (r.val ≤ k.val ∨ k.val ≤ r.val - 2 * i) → inS (.inl k) := by
      intro k hk; by_contra hna
      have hact : vegaActive i dy de (.inl k) := by simp [vegaActive]; omega
      obtain ⟨u, hu, hadj⟩ := hinS_max (.inl k) hact hna
      cases u with
      | inl m => have hm := hSG_rng m hu; rw [hv_inl] at hadj; have := m.isLt; have := k.isLt; split_ifs at hadj <;> rcases hk with h | h <;> rcases hm with h' | h' <;> omega
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | contradiction | omega)
    by_cases hact3 : ¬ (de = true ∧ r.val = 3 * i - 2)
    · -- `[z, r, r-2i+1, r-i+1, b, x]`
      exfalso
      let v1 : VegaV i := .inl r
      let v2 : VegaV i := .inl ⟨r.val - 2 * i + 1, by omega⟩
      let v3 : VegaV i := .inl ⟨r.val - i + 1, by omega⟩
      refine kill_c6 v1 v2 v3 (.inr 3) (.inr 0)
        (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega)
        (by simp [v3, vegaActive]; intro hde' heq; exact hact3 ⟨hde', by omega⟩)
        (by simp [vegaActive]) (by simp [vegaActive])
        (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
        (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
        hr_inS h0 (fun h => h2 ⟨⟨r.val - i + 1, by omega⟩, by dsimp; omega, by dsimp; omega, h⟩)
        ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
        ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
        (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
      · intro w hw h2' h4'; cases w with
        | inl k => simp [vegaAdj] at h4'; exact h2 ⟨k, h4'.1, h4'.2, hw⟩
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
      · intro w _ h1' h3' h5'; cases w with
        | inl k => simp [vegaAdj] at h5'
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
    · push Not at hact3; obtain ⟨hde, hr_top⟩ := hact3
      by_cases hi3 : 3 ≤ i
      · -- `i >= 3`: `[z, i-2, 2i, i, b, x]`
        exfalso
        let v1 : VegaV i := .inl ⟨i - 2, by omega⟩
        let v2 : VegaV i := .inl ⟨2 * i, by omega⟩
        let v3 : VegaV i := .inl ⟨i, by omega⟩
        refine kill_c6 v1 v2 v3 (.inr 3) (.inr 0)
          (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega) (by simp [v3, vegaActive]; try omega)
          (by simp [vegaActive]) (by simp [vegaActive])
          (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
          (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
          (hSG_full ⟨i - 2, by omega⟩ (Or.inr (by dsimp; try omega))) h0
          (fun h => h2 ⟨⟨i, by omega⟩, by dsimp; omega, by dsimp; omega, h⟩)
          ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
          ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
          (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
        · intro w hw h2' h4'; cases w with
          | inl k => simp [vegaAdj] at h4'; exact h2 ⟨k, h4'.1, h4'.2, hw⟩
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
        · intro w _ h1' h3' h5'; cases w with
          | inl k => simp [vegaAdj] at h5'
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
      · have hi2 : i = 2 := by omega
        cases hdy : dy
        · -- `i = 2, dy = false`: `[z, 0, u, y, w, 4]`
          exfalso
          let v1 : VegaV i := .inl ⟨0, by omega⟩
          let v5 : VegaV i := .inl ⟨4, by omega⟩
          refine kill_c6 v1 (.inr 5) (.inr 1) (.inr 7) v5
            (by simp [v1, vegaActive]; try omega) (by simp [vegaActive]) (by simp [vegaActive, hdy])
            (by simp [vegaActive]) (by simp [v5, vegaActive]; try omega)
            (by simp [v1]) (by simp [v1]) (by simp [v1]) (by simp [v1, v5, Fin.ext_iff])
            (by simp) (by simp) (by simp [v5]) (by simp) (by simp [v5]) (by simp [v5])
            (hSG_full ⟨0, by omega⟩ (Or.inr (by dsimp; try omega)))
            (hSG_full ⟨4, by omega⟩ (Or.inl (by dsimp; try omega))) hna1
            (by simp [v1, vegaAdj]; try omega) (by simp [vegaAdj]) (by simp [vegaAdj]) (by simp [v5, vegaAdj]; try omega) ?_ ?_
          · intro w hw h2' h4'; cases w with
            | inl k => simp [vegaAdj] at h2' h4'; omega
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at h2' h4'<;> contradiction)
          · intro w _ h1' h3' h5'; cases w with
            | inl k => simp [vegaAdj] at h3'
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v5, vegaAdj] at h1' h3' h5'<;> omega)
        · refine ⟨2, false, true, hbuild_i2_xv hi2 hdy hde ?_⟩
          subst hi2; intro v hv; cases v with
          | inl k =>
            have hk := k.isLt; constructor
            · intro hsk; rcases hSG_rng k hsk with hhi | hlo
              · right; right; right; exact congrArg Sum.inl (Fin.ext (by dsimp; omega))
              · right; right; left; exact congrArg Sum.inl (Fin.ext (by dsimp; omega))
            · rintro (h | h | h | h)
              · simp at h
              · simp at h
              · injection h with hk'; subst hk'; exact hSG_full ⟨0, by omega⟩ (Or.inr (by dsimp; omega))
              · injection h with hk'; subst hk'; exact hSG_full ⟨4, by omega⟩ (Or.inl (by dsimp; omega))
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaActive] at hv ⊢<;> assumption)
  · by_cases h1y : inS (.inr 1)
    · -- Family C': `SQ = {y, b}` (`dy = false`), `S_Γ = [r, N-1] ∪ [0, r-2i]`!
      exfalso
      have hdy : dy = false := by have h1a := hinS_act (.inr 1) h1y; cases dy <;> simp [vegaActive] at h1a ⊢
      have hna6 : ¬ inS (.inr 6) := hQ_na 1 6 (by simp [vegaAdj]) h1y
      have h3 : inS (.inr 3) := by_contra fun hna3 => by
        obtain ⟨u, hu, hadj⟩ := hinS_max (.inr 3) (by simp [vegaActive]) hna3
        cases u with
        | inl k => simp [vegaAdj] at hadj; exact h2 ⟨k, hadj.1, hadj.2, hu⟩
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> contradiction)
      have hSG_full : ∀ k : Fin N, (r.val ≤ k.val ∨ k.val ≤ r.val - 2 * i) → inS (.inl k) := by
        intro k hk; by_contra hna
        obtain ⟨u, hu, hadj⟩ := hinS_max (.inl k) (by simp [vegaActive]; try omega) hna
        cases u with
        | inl m => have hm := hSG_rng m hu; rw [hv_inl] at hadj; have := m.isLt; have := k.isLt; split_ifs at hadj <;> rcases hk with h | h <;> rcases hm with h' | h' <;> omega
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | contradiction | omega)
      by_cases hact3 : ¬ (de = true ∧ r.val = 3 * i - 2)
      · let v1 : VegaV i := .inl r; let v2 : VegaV i := .inl ⟨r.val - 2 * i + 1, by omega⟩; let v3 : VegaV i := .inl ⟨r.val - i + 1, by omega⟩
        refine kill_c6 v1 v2 v3 (.inr 6) (.inr 1)
          (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega)
          (by simp [v3, vegaActive]; intro hde' heq; exact hact3 ⟨hde', by omega⟩)
          (by simp [vegaActive]) (by simp [vegaActive, hdy])
          (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
          (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
          hr_inS h1y (fun h => h2 ⟨⟨r.val - i + 1, by omega⟩, by dsimp; omega, by dsimp; omega, h⟩)
          ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
          ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
          (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
        · intro w hw h2' h4'; cases w with
          | inl k => simp [vegaAdj] at h4'; exact h2 ⟨k, h4'.1, h4'.2, hw⟩
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
        · intro w _ h1' h3' h5'; cases w with
          | inl k => simp [vegaAdj] at h5'
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
      · push Not at hact3; obtain ⟨_, hr_top⟩ := hact3
        by_cases hi3 : 3 ≤ i
        · let v1 : VegaV i := .inl ⟨i - 2, by omega⟩; let v2 : VegaV i := .inl ⟨2 * i, by omega⟩; let v3 : VegaV i := .inl ⟨i, by omega⟩
          refine kill_c6 v1 v2 v3 (.inr 6) (.inr 1)
            (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega) (by simp [v3, vegaActive]; try omega)
            (by simp [vegaActive]) (by simp [vegaActive, hdy])
            (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
            (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
            (hSG_full ⟨i - 2, by omega⟩ (Or.inr (by dsimp; try omega))) h1y
            (fun h => h2 ⟨⟨i, by omega⟩, by dsimp; omega, by dsimp; omega, h⟩)
            ((hv_inl _ _).mpr (by rw [if_pos (by dsimp; try omega)]; dsimp; try omega))
            ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
            (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
          · intro w hw h2' h4'; cases w with
            | inl k => simp [vegaAdj] at h4'; exact h2 ⟨k, h4'.1, h4'.2, hw⟩
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
          · intro w _ h1' h3' h5'; cases w with
            | inl k => simp [vegaAdj] at h5'
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
        · let v1 : VegaV i := .inl ⟨0, by omega⟩; let v5 : VegaV i := .inl ⟨4, by omega⟩
          refine kill_c6 v1 (.inr 2) (.inr 0) (.inr 4) v5
            (by simp [v1, vegaActive]; try omega) (by simp [vegaActive]) (by simp [vegaActive])
            (by simp [vegaActive]) (by simp [v5, vegaActive]; try omega)
            (by simp [v1]) (by simp [v1]) (by simp [v1]) (by simp [v1, v5, Fin.ext_iff])
            (by simp) (by simp) (by simp [v5]) (by simp) (by simp [v5]) (by simp [v5])
            (hSG_full ⟨0, by omega⟩ (Or.inr (by dsimp; try omega)))
            (hSG_full ⟨4, by omega⟩ (Or.inl (by dsimp; try omega))) h0
            (by simp [v1, vegaAdj]; try omega) (by simp [vegaAdj]) (by simp [vegaAdj]) (by simp [v5, vegaAdj]; try omega) ?_ ?_
          · intro w hw h2' h4'; cases w with
            | inl k => simp [vegaAdj] at h2' h4'; omega
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at h2' h4'<;> contradiction)
          · intro w _ h1' h3' h5'; cases w with
            | inl k => simp [vegaAdj] at h3'
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v5, vegaAdj] at h1' h3' h5'<;> omega)
    · -- `0, 1 ∉ S_Q` -> `S ⊆ N(r - i)`!
      exfalso
      refine hnot_sub_nbhd (.inl ⟨r.val - i, by omega⟩) (by simp [vegaActive]; try omega) (fun u hu => ?_)
      cases u with
      | inl k => rcases hSG_rng k hu with hk | hk <;> (rw [hv_inl]; have := k.isLt; split_ifs <;> dsimp at * <;> omega)
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]; first | contradiction | omega)

lemma extend_case_100 {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) (i : ℕ) (dy de : Bool) (inS : VegaV i → Prop) [DecidablePred inS]
    (C : ExtCtx H i dy de inS)
    (h1 : ∃ k : Fin (3 * i - 1), k.val < i ∧ inS (.inl k)) (h2 : ¬ (∃ k : Fin (3 * i - 1), i ≤ k.val ∧ k.val < 2 * i ∧ inS (.inl k))) (h3 : ¬ (∃ k : Fin (3 * i - 1), 2 * i ≤ k.val ∧ inS (.inl k))) :
    ∃ (i' : ℕ) (dy' de' : Bool), IsVegaGraph H i' dy' de' := by
  have hi := C.hi
  let N := 3 * i - 1
  have hN : 5 ≤ N := by omega
  have hinS_act := C.hinS_act
  have hinS_ind := C.hinS_ind
  have hinS_max := C.hinS_max
  have hnot_sub_nbhd := C.hnot_sub_nbhd
  have kill_c6 := C.kill_c6
  have hv_inl : ∀ p q : Fin N, vegaAdj i (.inl p) (.inl q) ↔
      (if p.val ≤ q.val then i ≤ q.val - p.val ∧ q.val - p.val ≤ 2 * i - 1
       else i ≤ q.val + N - p.val ∧ q.val + N - p.val ≤ 2 * i - 1) := ext_hv_inl hi
  have hQ_na : ∀ p q : Fin 8, vegaAdj i (.inr p) (.inr q) → inS (.inr p) → ¬ inS (.inr q) :=
    fun p q hadj hp hq => hinS_ind (.inr p) (.inr q) hp hq hadj
  have hbuild_restore := C.hbuild_restore
  have hbuild_mirror_end := C.hbuild_mirror_end
  have hna2 : ¬ inS (.inr 2) := fun h => by obtain ⟨k, hk, hsk⟩ := h1; exact hinS_ind (.inr 2) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hna5 : ¬ inS (.inr 5) := fun h => by obtain ⟨k, hk, hsk⟩ := h1; exact hinS_ind (.inr 5) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hSG_I1 : ∀ k : Fin N, inS (.inl k) → k.val < i := fun k hk => by
    by_contra hge; by_cases hlt : k.val < 2 * i; exact h2 ⟨k, by omega, hlt, hk⟩; exact h3 ⟨k, by omega, hk⟩
  by_cases h0 : inS (.inr 0)
  · exfalso; have h1' := hQ_na 0 1 (by simp [vegaAdj]) h0; have h3' := hQ_na 0 3 (by simp [vegaAdj]) h0; have h4' := hQ_na 0 4 (by simp [vegaAdj]) h0
    refine hnot_sub_nbhd (.inr 2) (by simp [vegaActive]) (fun u hu => ?_)
    cases u with
    | inl k => simp [vegaAdj, hSG_I1 k hu]
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
  · by_cases h1y : inS (.inr 1)
    · exfalso; have h6' := hQ_na 1 6 (by simp [vegaAdj]) h1y; have h7' := hQ_na 1 7 (by simp [vegaAdj]) h1y
      refine hnot_sub_nbhd (.inr 5) (by simp [vegaActive]) (fun u hu => ?_)
      cases u with
      | inl k => simp [vegaAdj, hSG_I1 k hu]
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
    · by_cases h3q : inS (.inr 3)
      · have h7q : ¬ inS (.inr 7) := hQ_na 3 7 (by simp [vegaAdj]) h3q
        by_cases h4q : inS (.inr 4)
        · exfalso; have h6q := hQ_na 4 6 (by simp [vegaAdj]) h4q
          refine hnot_sub_nbhd (.inr 5) (by simp [vegaActive]) (fun u hu => ?_)
          cases u with
          | inl k => simp [vegaAdj, hSG_I1 k hu]
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
        · -- `SQ ⊆ {3, 6}`: if `de = false` -> `N(2i-1)`; if `de = true` -> restore `2i-1`!
          cases hde : de
          · exfalso
            refine hnot_sub_nbhd (.inl ⟨2 * i - 1, by omega⟩) (by simp [vegaActive, hde]) (fun u hu => ?_)
            cases u with
            | inl k => rw [hv_inl, if_neg (by have := hSG_I1 k hu; dsimp; try omega)]; have := hSG_I1 k hu; dsimp; omega
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]; first | contradiction | omega)
          · have h6q : inS (.inr 6) := by_contra fun hna6 => by
              obtain ⟨u, hu, hadj⟩ := hinS_max (.inr 6) (by simp [vegaActive]) hna6
              cases u with
              | inl k => simp [vegaAdj] at hadj; exact h2 ⟨k, hadj.1, hadj.2, hu⟩
              | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> contradiction)
            have hI1_full : ∀ k : Fin N, k.val < i → inS (.inl k) := fun k hk => by_contra fun hna => by
              obtain ⟨u, hu, hadj⟩ := hinS_max (.inl k) (by simp [vegaActive]; try omega) hna
              cases u with
              | inl m => have hm := hSG_I1 m hu; rw [hv_inl] at hadj; split_ifs at hadj <;> omega
              | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | contradiction | omega)
            refine ⟨i, dy, false, hbuild_restore dy false (.inl ⟨2 * i - 1, by omega⟩) (by simp [vegaActive, hde])
              (by simp [vegaActive]) (fun v hv => by cases v with | inl k => simp [vegaActive, hde]; intro hk; exact hv (congrArg Sum.inl (Fin.ext hk)) | inr q => simp [vegaActive]) ?_⟩
            intro v hv; cases v with
            | inl k =>
              have hk := k.isLt; rw [hv_inl]; dsimp only
              constructor
              · intro hsk; have := hSG_I1 k hsk; rw [if_neg (by omega)]; omega
              · intro hadj; split_ifs at hadj with hle
                · omega
                · exact hI1_full k (by omega)
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]; first | assumption | (constructor <;> (intro; first | omega | assumption | contradiction)))
      · by_cases h4q : inS (.inr 4)
        · have h6q : ¬ inS (.inr 6) := hQ_na 4 6 (by simp [vegaAdj]) h4q
          have h7q : inS (.inr 7) := by_contra fun hna7 => by
            obtain ⟨u, hu, hadj⟩ := hinS_max (.inr 7) (by simp [vegaActive]) hna7
            cases u with
            | inl k => simp [vegaAdj] at hadj; exact h3 ⟨k, hadj, hu⟩
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> contradiction)
          have hI1_full : ∀ k : Fin N, k.val < i → inS (.inl k) := fun k hk => by_contra fun hna => by
            obtain ⟨u, hu, hadj⟩ := hinS_max (.inl k) (by simp [vegaActive]; try omega) hna
            cases u with
            | inl m => have hm := hSG_I1 m hu; rw [hv_inl] at hadj; split_ifs at hadj <;> omega
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | contradiction | omega)
          cases hde : de
          · -- Family A (`de = false`, `SQ = {c, w}`, `SG = I_1`): `[z, c, v, 2i-1, b, w]`
            exfalso
            let v3 : VegaV i := .inl ⟨2 * i - 1, by omega⟩
            refine kill_c6 (.inr 4) (.inr 6) v3 (.inr 3) (.inr 7)
              (by simp [vegaActive]) (by simp [vegaActive]) (by simp [v3, vegaActive, hde])
              (by simp [vegaActive]) (by simp [vegaActive])
              (by simp) (by simp [v3]) (by simp) (by simp) (by simp [v3]) (by simp) (by simp)
              (by simp [v3]) (by simp [v3]) (by simp)
              h4q h7q (fun h => h2 ⟨⟨2 * i - 1, by omega⟩, by dsimp; omega, by dsimp; omega, h⟩)
              (by simp [vegaAdj]) (by simp [v3, vegaAdj]; try omega) (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
            · intro w hw h2' h4'; cases w with
              | inl k => have := hSG_I1 k hw; simp [vegaAdj] at h2'; omega
              | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vegaAdj] at h2' h4'
            · intro w _ h1' h3' h5'; cases w with
              | inl k => simp [vegaAdj] at h1'; have hk := k.isLt; rw [hv_inl] at h3'; dsimp [v3] at h3'; split_ifs at h3' <;> omega
              | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [v3, vegaAdj] at h1' h3' h5'
          · -- `de = true`, `SQ = {c, w}`, `SG = I_1` -> mirror + restore `2i-1`!
            refine ⟨i, dy, false, hbuild_mirror_end hde ?_⟩
            intro v hv; cases v with
            | inl k =>
              have hk := k.isLt
              have hkne : k.val ≠ 2 * i - 1 := by simpa [vegaActive, hde] using hv
              simp only [vegaMirror]; split_ifs with hklt
              · rw [hv_inl]; dsimp only; rw [if_neg (by omega)]; exact iff_of_true (hI1_full k hklt) (by omega)
              · rw [hv_inl]; dsimp only; exact iff_of_false (fun h => hklt (hSG_I1 k h)) (by split_ifs <;> omega)
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaMirror, vegaAdj]; first | assumption | (constructor <;> (intro; first | omega | assumption | contradiction)))
        · -- `0, 1, 2, 3, 4, 5 ∉ S_Q` -> `S ⊆ N(a)`!
          exfalso
          refine hnot_sub_nbhd (.inr 2) (by simp [vegaActive]) (fun u hu => ?_)
          cases u with
          | inl k => simp [vegaAdj, hSG_I1 k hu]
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)

lemma extend_case_011 {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) (i : ℕ) (dy de : Bool) (inS : VegaV i → Prop) [DecidablePred inS]
    (C : ExtCtx H i dy de inS)
    (h1 : ¬ (∃ k : Fin (3 * i - 1), k.val < i ∧ inS (.inl k))) (h2 : ∃ k : Fin (3 * i - 1), i ≤ k.val ∧ k.val < 2 * i ∧ inS (.inl k)) (h3 : ∃ k : Fin (3 * i - 1), 2 * i ≤ k.val ∧ inS (.inl k)) :
    ∃ (i' : ℕ) (dy' de' : Bool), IsVegaGraph H i' dy' de' := by
  have hi := C.hi
  let N := 3 * i - 1
  have hN : 5 ≤ N := by omega
  have hinS_act := C.hinS_act
  have hinS_ind := C.hinS_ind
  have hinS_max := C.hinS_max
  have hnot_sub_nbhd := C.hnot_sub_nbhd
  have kill_c6 := C.kill_c6
  have hv_inl : ∀ p q : Fin N, vegaAdj i (.inl p) (.inl q) ↔
      (if p.val ≤ q.val then i ≤ q.val - p.val ∧ q.val - p.val ≤ 2 * i - 1
       else i ≤ q.val + N - p.val ∧ q.val + N - p.val ≤ 2 * i - 1) := ext_hv_inl hi
  have hQ_na : ∀ p q : Fin 8, vegaAdj i (.inr p) (.inr q) → inS (.inr p) → ¬ inS (.inr q) :=
    fun p q hadj hp hq => hinS_ind (.inr p) (.inr q) hp hq hadj
  let SG : Finset (Fin N) := Finset.univ.filter (fun k => inS (.inl k))
  exfalso
  have hna3 : ¬ inS (.inr 3) := fun h => by obtain ⟨k, hk1, hk2, hsk⟩ := h2; exact hinS_ind (.inr 3) (.inl k) h hsk (by simp [vegaAdj, hk1, hk2])
  have hna6 : ¬ inS (.inr 6) := fun h => by obtain ⟨k, hk1, hk2, hsk⟩ := h2; exact hinS_ind (.inr 6) (.inl k) h hsk (by simp [vegaAdj, hk1, hk2])
  have hna4 : ¬ inS (.inr 4) := fun h => by obtain ⟨k, hk, hsk⟩ := h3; exact hinS_ind (.inr 4) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hna7 : ¬ inS (.inr 7) := fun h => by obtain ⟨k, hk, hsk⟩ := h3; exact hinS_ind (.inr 7) (.inl k) h hsk (by simp [vegaAdj, hk])
  let S2 := SG.filter (fun k : Fin N => i ≤ k.val ∧ k.val < 2 * i)
  have hS2_ne : S2.Nonempty := by obtain ⟨k, hk1, hk2, hsk⟩ := h2; exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsk⟩, hk1, hk2⟩⟩
  obtain ⟨r, hrS2, hr_min⟩ := Finset.exists_min_image S2 (fun k => k.val) hS2_ne
  have hr_inS : inS (.inl r) := (Finset.mem_filter.mp (Finset.mem_filter.mp hrS2).1).2
  have ⟨hr_ge, hr_lt⟩ := (Finset.mem_filter.mp hrS2).2
  have hr_gt_i : i + 1 ≤ r.val := by
    by_contra hle; obtain ⟨k3, hk3, hsk3⟩ := h3; have := k3.isLt
    exact hinS_ind (.inl r) (.inl k3) hr_inS hsk3 ((hv_inl r k3).mpr (by rw [if_pos (by omega)]; try omega))
  have hSG_rng : ∀ k : Fin N, inS (.inl k) → r.val ≤ k.val ∧ k.val ≤ r.val + i - 1 := by
    intro k hsk; have hk := k.isLt
    by_cases hk1 : k.val < i
    · exact (h1 ⟨k, hk1, hsk⟩).elim
    · by_cases hk2 : k.val < 2 * i
      · have hle := hr_min k (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsk⟩, by omega, hk2⟩); omega
      · have hna := hinS_ind (.inl r) (.inl k) hr_inS hsk
        rw [hv_inl, if_pos (by omega)] at hna; omega
  by_cases h0 : inS (.inr 0)
  · -- Family E (`SQ = {x, u}`, `2i ∈ SG`): `[z, 2i, i, 0, a, x]`!
    have hna1 : ¬ inS (.inr 1) := hQ_na 0 1 (by simp [vegaAdj]) h0
    have hna2 : ¬ inS (.inr 2) := hQ_na 0 2 (by simp [vegaAdj]) h0
    have h2i : inS (.inl ⟨2 * i, by omega⟩) := by_contra fun hna => by
      obtain ⟨u, hu, hadj⟩ := hinS_max (.inl ⟨2 * i, by omega⟩) (by simp [vegaActive]; try omega) hna
      cases u with
      | inl m => have ⟨hm1, hm2⟩ := hSG_rng m hu; have := m.isLt; rw [hv_inl] at hadj; dsimp at hadj; split_ifs at hadj <;> omega
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | contradiction | omega)
    let v1 : VegaV i := .inl ⟨2 * i, by omega⟩; let v2 : VegaV i := .inl ⟨i, by omega⟩; let v3 : VegaV i := .inl ⟨0, by omega⟩
    refine kill_c6 v1 v2 v3 (.inr 2) (.inr 0)
      (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega) (by simp [v3, vegaActive]; try omega)
      (by simp [vegaActive]) (by simp [vegaActive])
      (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
      (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
      h2i h0 (fun h => h1 ⟨⟨0, by omega⟩, by dsimp; omega, h⟩)
      ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
      ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
      (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
    · intro w hw h2' h4'; cases w with
      | inl k => simp [vegaAdj] at h4'; exact h1 ⟨k, h4', hw⟩
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
    · intro w _ h1' h3' h5'; cases w with
      | inl k => simp [vegaAdj] at h5'
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
  · by_cases h1y : inS (.inr 1)
    · -- Family E' (`SQ = {y, a}`, `dy = false`, `2i ∈ SG`): `[z, 2i, i, 0, u, y]`!
      have hdy : dy = false := by have h1a := hinS_act (.inr 1) h1y; cases dy <;> simp [vegaActive] at h1a ⊢
      have hna5 : ¬ inS (.inr 5) := hQ_na 1 5 (by simp [vegaAdj]) h1y
      have h2i : inS (.inl ⟨2 * i, by omega⟩) := by_contra fun hna => by
        obtain ⟨u, hu, hadj⟩ := hinS_max (.inl ⟨2 * i, by omega⟩) (by simp [vegaActive]; try omega) hna
        cases u with
        | inl m => have ⟨hm1, hm2⟩ := hSG_rng m hu; have := m.isLt; rw [hv_inl] at hadj; dsimp at hadj; split_ifs at hadj <;> omega
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | contradiction | omega)
      let v1 : VegaV i := .inl ⟨2 * i, by omega⟩; let v2 : VegaV i := .inl ⟨i, by omega⟩; let v3 : VegaV i := .inl ⟨0, by omega⟩
      refine kill_c6 v1 v2 v3 (.inr 5) (.inr 1)
        (by simp [v1, vegaActive]; try omega) (by simp [v2, vegaActive]; try omega) (by simp [v3, vegaActive]; try omega)
        (by simp [vegaActive]) (by simp [vegaActive, hdy])
        (by simp [v1, v2, Fin.ext_iff]; try omega) (by simp [v1, v3, Fin.ext_iff]; try omega) (by simp [v1]) (by simp [v1])
        (by simp [v2, v3, Fin.ext_iff]; try omega) (by simp [v2]) (by simp [v2]) (by simp [v3]) (by simp [v3]) (by simp)
        h2i h1y (fun h => h1 ⟨⟨0, by omega⟩, by dsimp; omega, h⟩)
        ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
        ((hv_inl _ _).mpr (by rw [if_neg (by dsimp; try omega)]; dsimp; try omega))
        (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
      · intro w hw h2' h4'; cases w with
        | inl k => simp [vegaAdj] at h4'; exact h1 ⟨k, h4', hw⟩
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v2, vegaAdj] at h2' h4'<;> contradiction)
      · intro w _ h1' h3' h5'; cases w with
        | inl k => simp [vegaAdj] at h5'
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [v1, v3, vegaAdj] at h1' h3' h5'<;> omega)
    · -- `0, 1 ∉ S_Q` -> `S ⊆ N(r - i)`!
      refine hnot_sub_nbhd (.inl ⟨r.val - i, by omega⟩) (by simp [vegaActive]; try omega) (fun u hu => ?_)
      cases u with
      | inl k => have ⟨hk1, hk2⟩ := hSG_rng k hu; rw [hv_inl, if_pos (by dsimp; try omega)]; dsimp; omega
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]; first | contradiction | omega)

lemma extend_case_010 {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) (i : ℕ) (dy de : Bool) (inS : VegaV i → Prop) [DecidablePred inS]
    (C : ExtCtx H i dy de inS)
    (h1 : ¬ (∃ k : Fin (3 * i - 1), k.val < i ∧ inS (.inl k))) (h2 : ∃ k : Fin (3 * i - 1), i ≤ k.val ∧ k.val < 2 * i ∧ inS (.inl k)) (h3 : ¬ (∃ k : Fin (3 * i - 1), 2 * i ≤ k.val ∧ inS (.inl k))) :
    ∃ (i' : ℕ) (dy' de' : Bool), IsVegaGraph H i' dy' de' := by
  have hi := C.hi
  let N := 3 * i - 1
  have hN : 5 ≤ N := by omega
  have hinS_act := C.hinS_act
  have hinS_ind := C.hinS_ind
  have hinS_max := C.hinS_max
  have hnot_sub_nbhd := C.hnot_sub_nbhd
  have kill_c6 := C.kill_c6
  have hv_inl : ∀ p q : Fin N, vegaAdj i (.inl p) (.inl q) ↔
      (if p.val ≤ q.val then i ≤ q.val - p.val ∧ q.val - p.val ≤ 2 * i - 1
       else i ≤ q.val + N - p.val ∧ q.val + N - p.val ≤ 2 * i - 1) := ext_hv_inl hi
  have hQ_na : ∀ p q : Fin 8, vegaAdj i (.inr p) (.inr q) → inS (.inr p) → ¬ inS (.inr q) :=
    fun p q hadj hp hq => hinS_ind (.inr p) (.inr q) hp hq hadj
  exfalso
  have hna3 : ¬ inS (.inr 3) := fun h => by obtain ⟨k, hk1, hk2, hsk⟩ := h2; exact hinS_ind (.inr 3) (.inl k) h hsk (by simp [vegaAdj, hk1, hk2])
  have hna6 : ¬ inS (.inr 6) := fun h => by obtain ⟨k, hk1, hk2, hsk⟩ := h2; exact hinS_ind (.inr 6) (.inl k) h hsk (by simp [vegaAdj, hk1, hk2])
  have hSG_I2 : ∀ k : Fin N, inS (.inl k) → i ≤ k.val ∧ k.val < 2 * i := fun k hk => by
    by_cases hlt : k.val < i; exact (h1 ⟨k, hlt, hk⟩).elim
    by_cases hlt2 : k.val < 2 * i; exact ⟨by omega, hlt2⟩; exact (h3 ⟨k, by omega, hk⟩).elim
  by_cases h0 : inS (.inr 0)
  · have h1' := hQ_na 0 1 (by simp [vegaAdj]) h0; have h2' := hQ_na 0 2 (by simp [vegaAdj]) h0; have h4' := hQ_na 0 4 (by simp [vegaAdj]) h0
    refine hnot_sub_nbhd (.inr 3) (by simp [vegaActive]) (fun u hu => ?_)
    cases u with
    | inl k => have ⟨a1, a2⟩ := hSG_I2 k hu; simp [vegaAdj, a1, a2]
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
  · by_cases h1y : inS (.inr 1)
    · have h5' := hQ_na 1 5 (by simp [vegaAdj]) h1y; have h7' := hQ_na 1 7 (by simp [vegaAdj]) h1y
      refine hnot_sub_nbhd (.inr 6) (by simp [vegaActive]) (fun u hu => ?_)
      cases u with
      | inl k => have ⟨a1, a2⟩ := hSG_I2 k hu; simp [vegaAdj, a1, a2]
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
    · by_cases h2q : inS (.inr 2)
      · have h7q : ¬ inS (.inr 7) := hQ_na 2 7 (by simp [vegaAdj]) h2q
        by_cases h4q : inS (.inr 4)
        · have h5q := hQ_na 4 5 (by simp [vegaAdj]) h4q
          refine hnot_sub_nbhd (.inr 6) (by simp [vegaActive]) (fun u hu => ?_)
          cases u with
          | inl k => have ⟨a1, a2⟩ := hSG_I2 k hu; simp [vegaAdj, a1, a2]
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
        · refine hnot_sub_nbhd (.inl ⟨0, by omega⟩) (by simp [vegaActive]; try omega) (fun u hu => ?_)
          cases u with
          | inl k => have ⟨a1, a2⟩ := hSG_I2 k hu; rw [hv_inl, if_pos (by dsimp; try omega)]; dsimp; omega
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]; first | contradiction | omega)
      · by_cases h4q : inS (.inr 4)
        · have h5q : ¬ inS (.inr 5) := hQ_na 4 5 (by simp [vegaAdj]) h4q
          have h7q : inS (.inr 7) := by_contra fun hna7 => by
            obtain ⟨u, hu, hadj⟩ := hinS_max (.inr 7) (by simp [vegaActive]) hna7
            cases u with
            | inl k => simp [vegaAdj] at hadj; exact h3 ⟨k, hadj, hu⟩
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> contradiction)
          cases hde : de
          · -- Family B (`de = false`, `SQ = {c, w}`, `SG ⊆ I_2`): `[z, c, u, 0, a, w]`!
            let v3 : VegaV i := .inl ⟨0, by omega⟩
            refine kill_c6 (.inr 4) (.inr 5) v3 (.inr 2) (.inr 7)
              (by simp [vegaActive]) (by simp [vegaActive]) (by simp [v3, vegaActive]; try omega)
              (by simp [vegaActive]) (by simp [vegaActive])
              (by simp) (by simp [v3]) (by simp) (by simp) (by simp [v3]) (by simp) (by simp)
              (by simp [v3]) (by simp [v3]) (by simp)
              h4q h7q (fun h => h1 ⟨⟨0, by omega⟩, by dsimp; omega, h⟩)
              (by simp [vegaAdj]) (by simp [v3, vegaAdj]; try omega) (by simp [v3, vegaAdj]; try omega) (by simp [vegaAdj]) ?_ ?_
            · intro w hw h2' h4'; cases w with
              | inl k => have ⟨a1, _⟩ := hSG_I2 k hw; simp [vegaAdj] at h2'; omega
              | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vegaAdj] at h2' h4'
            · intro w _ h1' h3' h5'; cases w with
              | inl k => simp [vegaAdj] at h1'; have hk := k.isLt; rw [hv_inl] at h3'; dsimp [v3] at h3'; split_ifs at h3' <;> omega
              | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [v3, vegaAdj] at h1' h3' h5'
          · -- `de = true`: vertex `i - 1` has NO neighbor in `S` (since `2i-1` inactive, `a,u ∉ S`)!
            obtain ⟨u, hu, hadj⟩ := hinS_max (.inl ⟨i - 1, by omega⟩) (by simp [vegaActive]; try omega) (fun h => h1 ⟨⟨i - 1, by omega⟩, by dsimp; omega, h⟩)
            cases u with
            | inl k =>
              have ⟨a1, a2⟩ := hSG_I2 k hu
              have hne_end : k.val ≠ 2 * i - 1 := by have := hinS_act (.inl k) hu; simpa [vegaActive, hde] using this
              rw [hv_inl, if_neg (by dsimp; try omega)] at hadj; dsimp at hadj; omega
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | contradiction | omega)
        · refine hnot_sub_nbhd (.inr 3) (by simp [vegaActive]) (fun u hu => ?_)
          cases u with
          | inl k => have ⟨a1, a2⟩ := hSG_I2 k hu; simp [vegaAdj, a1, a2]
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)

lemma extend_case_001 {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) (i : ℕ) (dy de : Bool) (inS : VegaV i → Prop) [DecidablePred inS]
    (C : ExtCtx H i dy de inS)
    (h1 : ¬ (∃ k : Fin (3 * i - 1), k.val < i ∧ inS (.inl k))) (h2 : ¬ (∃ k : Fin (3 * i - 1), i ≤ k.val ∧ k.val < 2 * i ∧ inS (.inl k))) (h3 : ∃ k : Fin (3 * i - 1), 2 * i ≤ k.val ∧ inS (.inl k)) :
    ∃ (i' : ℕ) (dy' de' : Bool), IsVegaGraph H i' dy' de' := by
  have hi := C.hi
  let N := 3 * i - 1
  have hN : 5 ≤ N := by omega
  have hinS_act := C.hinS_act
  have hinS_ind := C.hinS_ind
  have hinS_max := C.hinS_max
  have hnot_sub_nbhd := C.hnot_sub_nbhd
  have kill_c6 := C.kill_c6
  have hv_inl : ∀ p q : Fin N, vegaAdj i (.inl p) (.inl q) ↔
      (if p.val ≤ q.val then i ≤ q.val - p.val ∧ q.val - p.val ≤ 2 * i - 1
       else i ≤ q.val + N - p.val ∧ q.val + N - p.val ≤ 2 * i - 1) := ext_hv_inl hi
  have hQ_na : ∀ p q : Fin 8, vegaAdj i (.inr p) (.inr q) → inS (.inr p) → ¬ inS (.inr q) :=
    fun p q hadj hp hq => hinS_ind (.inr p) (.inr q) hp hq hadj
  exfalso
  have hna4 : ¬ inS (.inr 4) := fun h => by obtain ⟨k, hk, hsk⟩ := h3; exact hinS_ind (.inr 4) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hna7 : ¬ inS (.inr 7) := fun h => by obtain ⟨k, hk, hsk⟩ := h3; exact hinS_ind (.inr 7) (.inl k) h hsk (by simp [vegaAdj, hk])
  have hSG_I3 : ∀ k : Fin N, inS (.inl k) → 2 * i ≤ k.val := fun k hk => by
    by_cases hlt : k.val < i; exact (h1 ⟨k, hlt, hk⟩).elim
    by_cases hlt2 : k.val < 2 * i; exact (h2 ⟨k, by omega, hlt2, hk⟩).elim; omega
  -- Vertex `0 ∈ I_1` must be dominated by `S_Q` -> `inS (.inr 2) ∨ inS (.inr 5)`!
  have h25 : inS (.inr 2) ∨ inS (.inr 5) := by
    obtain ⟨u, hu, hadj⟩ := hinS_max (.inl ⟨0, by omega⟩) (by simp [vegaActive]; try omega) (fun h => h1 ⟨⟨0, by omega⟩, by dsimp; omega, h⟩)
    cases u with
    | inl k => have := hSG_I3 k hu; have := k.isLt; rw [hv_inl, if_neg (by dsimp; try omega)] at hadj; dsimp at hadj; omega
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | omega | (left; assumption) | (right; assumption))
  by_cases h0 : inS (.inr 0)
  · have h1' := hQ_na 0 1 (by simp [vegaAdj]) h0; have h2' := hQ_na 0 2 (by simp [vegaAdj]) h0; have h3' := hQ_na 0 3 (by simp [vegaAdj]) h0
    refine hnot_sub_nbhd (.inr 4) (by simp [vegaActive]) (fun u hu => ?_)
    cases u with
    | inl k => simp [vegaAdj, hSG_I3 k hu]
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
  · by_cases h1y : inS (.inr 1)
    · have h5' := hQ_na 1 5 (by simp [vegaAdj]) h1y; have h6' := hQ_na 1 6 (by simp [vegaAdj]) h1y
      refine hnot_sub_nbhd (.inr 7) (by simp [vegaActive]) (fun u hu => ?_)
      cases u with
      | inl k => simp [vegaAdj, hSG_I3 k hu]
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
    · by_cases h3q : inS (.inr 3)
      · have h5q := hQ_na 3 5 (by simp [vegaAdj]) h3q
        have h2q : inS (.inr 2) := by rcases h25 with h | h; exact h; exact (h5q h).elim
        have h6q := hQ_na 2 6 (by simp [vegaAdj]) h2q
        refine hnot_sub_nbhd (.inr 7) (by simp [vegaActive]) (fun u hu => ?_)
        cases u with
        | inl k => simp [vegaAdj, hSG_I3 k hu]
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
      · by_cases h6q : inS (.inr 6)
        · have h2q := hQ_na 6 2 (by simp [vegaAdj]) h6q
          refine hnot_sub_nbhd (.inr 4) (by simp [vegaActive]) (fun u hu => ?_)
          cases u with
          | inl k => simp [vegaAdj, hSG_I3 k hu]
          | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
        · -- `S_Q ⊆ {2, 5}`: if `de = false`, `2i - 1` is undominated; if `de = true`, `S ⊆ N(i - 1)`!
          cases hde : de
          · obtain ⟨u, hu, hadj⟩ := hinS_max (.inl ⟨2 * i - 1, by omega⟩) (by simp [vegaActive, hde]) (fun h => h2 ⟨⟨2 * i - 1, by omega⟩, by dsimp; omega, by dsimp; omega, h⟩)
            cases u with
            | inl k => have := hSG_I3 k hu; have := k.isLt; rw [hv_inl, if_neg (by dsimp; try omega)] at hadj; dsimp at hadj; omega
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | contradiction | omega)
          · refine hnot_sub_nbhd (.inl ⟨i - 1, by omega⟩) (by simp [vegaActive]; try omega) (fun u hu => ?_)
            cases u with
            | inl k => have := hSG_I3 k hu; have := k.isLt; rw [hv_inl, if_pos (by dsimp; try omega)]; dsimp; omega
            | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]; first | contradiction | omega)

lemma extend_case_000 {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) (i : ℕ) (dy de : Bool) (inS : VegaV i → Prop) [DecidablePred inS]
    (C : ExtCtx H i dy de inS)
    (h1 : ¬ (∃ k : Fin (3 * i - 1), k.val < i ∧ inS (.inl k))) (h2 : ¬ (∃ k : Fin (3 * i - 1), i ≤ k.val ∧ k.val < 2 * i ∧ inS (.inl k))) (h3 : ¬ (∃ k : Fin (3 * i - 1), 2 * i ≤ k.val ∧ inS (.inl k))) :
    ∃ (i' : ℕ) (dy' de' : Bool), IsVegaGraph H i' dy' de' := by
  have hi := C.hi
  let N := 3 * i - 1
  have hN : 5 ≤ N := by omega
  have hinS_act := C.hinS_act
  have hinS_ind := C.hinS_ind
  have hinS_max := C.hinS_max
  have hnot_sub_nbhd := C.hnot_sub_nbhd
  have kill_c6 := C.kill_c6
  have hv_inl : ∀ p q : Fin N, vegaAdj i (.inl p) (.inl q) ↔
      (if p.val ≤ q.val then i ≤ q.val - p.val ∧ q.val - p.val ≤ 2 * i - 1
       else i ≤ q.val + N - p.val ∧ q.val + N - p.val ≤ 2 * i - 1) := ext_hv_inl hi
  have hQ_na : ∀ p q : Fin 8, vegaAdj i (.inr p) (.inr q) → inS (.inr p) → ¬ inS (.inr q) :=
    fun p q hadj hp hq => hinS_ind (.inr p) (.inr q) hp hq hadj
  have hbuild_restore := C.hbuild_restore
  have hSG_empty : ∀ k : Fin N, ¬ inS (.inl k) := fun k hk => by
    by_cases hlt : k.val < i; exact h1 ⟨k, hlt, hk⟩
    by_cases hlt2 : k.val < 2 * i; exact h2 ⟨k, by omega, hlt2, hk⟩; exact h3 ⟨k, by omega, hk⟩
  have hdom1 : inS (.inr 2) ∨ inS (.inr 5) := by
    obtain ⟨u, hu, hadj⟩ := hinS_max (.inl ⟨0, by omega⟩) (by simp [vegaActive]; try omega) (hSG_empty _)
    cases u with
    | inl k => exact (hSG_empty k hu).elim
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | omega | (left; assumption) | (right; assumption))
  have hdom2 : inS (.inr 3) ∨ inS (.inr 6) := by
    obtain ⟨u, hu, hadj⟩ := hinS_max (.inl ⟨i, by omega⟩) (by simp [vegaActive]; try omega) (hSG_empty _)
    cases u with
    | inl k => exact (hSG_empty k hu).elim
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | omega | (left; assumption) | (right; assumption))
  have hdom3 : inS (.inr 4) ∨ inS (.inr 7) := by
    obtain ⟨u, hu, hadj⟩ := hinS_max (.inl ⟨2 * i, by omega⟩) (by simp [vegaActive]; try omega) (hSG_empty _)
    cases u with
    | inl k => exact (hSG_empty k hu).elim
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> first | omega | (left; assumption) | (right; assumption))
  rcases hdom1 with h2q | h5q
  · -- `2 ∈ S_Q` forces `6, 7, 0 ∉ S_Q`, hence `3, 4 ∈ S_Q`, `5 ∉ S_Q` -> `S ⊆ N(x)`!
    exfalso
    have h0q := hQ_na 2 0 (by simp [vegaAdj]) h2q
    have h6q := hQ_na 2 6 (by simp [vegaAdj]) h2q
    have h7q := hQ_na 2 7 (by simp [vegaAdj]) h2q
    have h3q : inS (.inr 3) := by rcases hdom2 with h | h; exact h; exact (h6q h).elim
    have h5q := hQ_na 3 5 (by simp [vegaAdj]) h3q
    refine hnot_sub_nbhd (.inr 0) (by simp [vegaActive]) (fun u hu => ?_)
    cases u with
    | inl k => exact (hSG_empty k hu).elim
    | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
  · -- `5 ∈ S_Q` forces `1, 3, 4 ∉ S_Q`, hence `6, 7 ∈ S_Q`, `2 ∉ S_Q` -> `N(y)` (if `dy=false`) or restore `y`!
    have h1q := hQ_na 5 1 (by simp [vegaAdj]) h5q
    have h3q := hQ_na 5 3 (by simp [vegaAdj]) h5q
    have h4q := hQ_na 5 4 (by simp [vegaAdj]) h5q
    have h6q : inS (.inr 6) := by rcases hdom2 with h | h; exact (h3q h).elim; exact h
    have h7q : inS (.inr 7) := by rcases hdom3 with h | h; exact (h4q h).elim; exact h
    have h2q := hQ_na 6 2 (by simp [vegaAdj]) h6q
    cases hdy : dy
    · exfalso
      refine hnot_sub_nbhd (.inr 1) (by simp [vegaActive, hdy]) (fun u hu => ?_)
      cases u with
      | inl k => exact (hSG_empty k hu).elim
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]<;> contradiction)
    · have h0q : inS (.inr 0) := by_contra fun hna0 => by
        obtain ⟨u, hu, hadj⟩ := hinS_max (.inr 0) (by simp [vegaActive]) hna0
        cases u with
        | inl k => exact (hSG_empty k hu).elim
        | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj] at hadj<;> contradiction)
      refine ⟨i, false, de, hbuild_restore false de (.inr 1) (by simp [vegaActive, hdy]) (by simp [vegaActive])
        (fun v hv => by cases v with | inl k => simp [vegaActive] | inr q => simp [vegaActive, hdy]; intro hq; exact hv (congrArg Sum.inr (Fin.ext hq))) ?_⟩
      intro v hv; cases v with
      | inl k => simp [vegaAdj, hSG_empty k]
      | inr q => rcases fin8_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [vegaAdj]; assumption)


/-- **Theorem 6 (1-Vertex Extension of `V_i`):** If `H` is good and `H - z ∈ V_i(dy, de)`,
    then `H ∈ V_i(dy', de')`! -/
theorem extend_vega_is_vega {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (G : IsGood H) (z : U)
    (i : ℕ) (dy de : Bool)
    (hH' : IsVegaGraph (H.induce {u : U | u ≠ z}) i dy de) :
    ∃ (i' : ℕ) (dy' de' : Bool), IsVegaGraph H i' dy' de' := by
  obtain ⟨hi, e, he_adj⟩ := hH'
  let N := 3 * i - 1
  have hN : 5 ≤ N := by omega
  let inS : VegaV i → Prop := fun v => if h : vegaActive i dy de v then H.Adj z (e.symm ⟨v, h⟩).1 else False
  have : DecidablePred inS := fun v => by dsimp only [inS]; infer_instance
  have hinS_act : ∀ v : VegaV i, inS v → vegaActive i dy de v := fun v hv => by
    dsimp only [inS] at hv; split_ifs at hv with h; exact h
  have hinS_iff : ∀ (v : VegaV i) (hv : vegaActive i dy de v), inS v ↔ H.Adj z (e.symm ⟨v, hv⟩).1 := fun v hv => by
    dsimp only [inS]; rw [dif_pos hv]
  have hinS_ind : ∀ u v : VegaV i, inS u → inS v → ¬ vegaAdj i u v := by
    intro u v hu hv hadj
    have huA := hinS_act u hu; have hvA := hinS_act v hv
    have h1 := (hinS_iff u huA).mp hu; have h2 := (hinS_iff v hvA).mp hv
    have h3 : H.Adj (e.symm ⟨u, huA⟩).1 (e.symm ⟨v, hvA⟩).1 := by
      have := he_adj (e.symm ⟨u, huA⟩) (e.symm ⟨v, hvA⟩); simp at this; exact this.mpr hadj
    exact tf_contra G.hTF h1 h3 h2
  have hinS_max : ∀ v : VegaV i, vegaActive i dy de v → ¬ inS v → ∃ u : VegaV i, inS u ∧ vegaAdj i u v := by
    intro v hv hnot
    have hna : ¬ H.Adj z (e.symm ⟨v, hv⟩).1 := fun h => hnot ((hinS_iff v hv).mpr h)
    obtain ⟨w, hwz, hwv⟩ := G.hMax z (e.symm ⟨v, hv⟩).1 (e.symm ⟨v, hv⟩).2.symm hna
    have hw_ne : w ≠ z := (H.ne_of_adj hwz).symm
    let u := e ⟨w, hw_ne⟩
    have hu_inS : inS u.1 := (hinS_iff u.1 u.2).mpr (by simpa [u] using hwz)
    have hu_adj : vegaAdj i u.1 v := by
      have := he_adj ⟨w, hw_ne⟩ (e.symm ⟨v, hv⟩); simp at this; exact this.mp hwv.symm
    exact ⟨u.1, hu_inS, hu_adj⟩
  have hnot_sub_nbhd : ∀ v : VegaV i, vegaActive i dy de v → (∀ u : VegaV i, inS u → vegaAdj i v u) → False := by
    intro v hv hsub
    have htw : ∀ w : U, H.Adj z w ↔ H.Adj (e.symm ⟨v, hv⟩).1 w := by
      intro w; by_cases hwz : w = z
      · rw [hwz]
        refine ⟨fun hadj => absurd rfl hadj.ne, fun hadj => ?_⟩
        have hvn := (hinS_iff v hv).mpr hadj.symm
        exact (vegaAdj_irrefl hi v (hsub v hvn)).elim
      · let u := e ⟨w, hwz⟩
        have h1 : H.Adj z w ↔ inS u.1 := by rw [hinS_iff u.1 u.2]; simp [u]
        have h2 : H.Adj (e.symm ⟨v, hv⟩).1 w ↔ vegaAdj i v u.1 := by
          have := he_adj (e.symm ⟨v, hv⟩) ⟨w, hwz⟩; simp at this; exact this
        rw [h1, h2]; refine ⟨hsub u.1, fun hvu => by_contra fun hnot => ?_⟩
        obtain ⟨u', hu', hu'u⟩ := hinS_max u.1 u.2 hnot
        have hu'A := hinS_act u' hu'
        have e1 : H.Adj (e.symm ⟨v, hv⟩).1 (e.symm ⟨u', hu'A⟩).1 := by
          have := he_adj (e.symm ⟨v, hv⟩) (e.symm ⟨u', hu'A⟩); simp at this; exact this.mpr (hsub u' hu')
        have e2 : H.Adj (e.symm ⟨u', hu'A⟩).1 w := by
          have := he_adj (e.symm ⟨u', hu'A⟩) ⟨w, hwz⟩; simp at this; exact this.mpr hu'u
        exact tf_contra G.hTF e1 e2 (h2.mpr hvu)
    exact (e.symm ⟨v, hv⟩).2 (G.hTwin z (e.symm ⟨v, hv⟩).1 htw).symm
  -- Reusable C_6 kill helper in `H = H' + z`!
  have kill_c6 : ∀ (v1 v2 v3 v4 v5 : VegaV i),
      vegaActive i dy de v1 → vegaActive i dy de v2 → vegaActive i dy de v3 →
      vegaActive i dy de v4 → vegaActive i dy de v5 →
      v1 ≠ v2 → v1 ≠ v3 → v1 ≠ v4 → v1 ≠ v5 → v2 ≠ v3 → v2 ≠ v4 → v2 ≠ v5 → v3 ≠ v4 → v3 ≠ v5 → v4 ≠ v5 →
      inS v1 → inS v5 → ¬ inS v3 →
      vegaAdj i v1 v2 → vegaAdj i v2 v3 → vegaAdj i v3 v4 → vegaAdj i v4 v5 →
      (∀ w : VegaV i, inS w → vegaAdj i w v2 → vegaAdj i w v4 → False) →
      (∀ w : VegaV i, vegaActive i dy de w → vegaAdj i w v1 → vegaAdj i w v3 → vegaAdj i w v5 → False) →
      False := by
    intro v1 v2 v3 v4 v5 a1 a2 a3 a4 a5 n12 n13 n14 n15 n23 n24 n25 n34 n35 n45 s1 s5 ns3 e12 e23 e34 e45 hnoE hnoO
    let u1 := (e.symm ⟨v1, a1⟩).1; let u2 := (e.symm ⟨v2, a2⟩).1; let u3 := (e.symm ⟨v3, a3⟩).1
    let u4 := (e.symm ⟨v4, a4⟩).1; let u5 := (e.symm ⟨v5, a5⟩).1
    have hadj_u : ∀ (p q : VegaV i) (hp : vegaActive i dy de p) (hq : vegaActive i dy de q),
        vegaAdj i p q → H.Adj (e.symm ⟨p, hp⟩).1 (e.symm ⟨q, hq⟩).1 := fun p q hp hq h => by
      have := he_adj (e.symm ⟨p, hp⟩) (e.symm ⟨q, hq⟩); simp at this; exact this.mpr h
    have hne_u : ∀ (p q : VegaV i) (hp : vegaActive i dy de p) (hq : vegaActive i dy de q),
        p ≠ q → (e.symm ⟨p, hp⟩).1 ≠ (e.symm ⟨q, hq⟩).1 := fun p q hp hq h heq =>
      h (congrArg Subtype.val (e.symm.injective (Subtype.ext heq)))
    let cyc : Fin 6 → U := ![z, u1, u2, u3, u4, u5]
    have hcyc_inj : Function.Injective cyc := by
      intro p q hpq; fin_cases p <;> fin_cases q <;> dsimp [cyc, u1, u2, u3, u4, u5] at hpq ⊢
      all_goals first
        | rfl
        | (exfalso; first
          | exact ((e.symm _).2 hpq.symm).elim | exact ((e.symm _).2 hpq).elim
          | exact (hne_u _ _ _ _ n12 hpq).elim | exact (hne_u _ _ _ _ n12 hpq.symm).elim
          | exact (hne_u _ _ _ _ n13 hpq).elim | exact (hne_u _ _ _ _ n13 hpq.symm).elim
          | exact (hne_u _ _ _ _ n14 hpq).elim | exact (hne_u _ _ _ _ n14 hpq.symm).elim
          | exact (hne_u _ _ _ _ n15 hpq).elim | exact (hne_u _ _ _ _ n15 hpq.symm).elim
          | exact (hne_u _ _ _ _ n23 hpq).elim | exact (hne_u _ _ _ _ n23 hpq.symm).elim
          | exact (hne_u _ _ _ _ n24 hpq).elim | exact (hne_u _ _ _ _ n24 hpq.symm).elim
          | exact (hne_u _ _ _ _ n25 hpq).elim | exact (hne_u _ _ _ _ n25 hpq.symm).elim
          | exact (hne_u _ _ _ _ n34 hpq).elim | exact (hne_u _ _ _ _ n34 hpq.symm).elim
          | exact (hne_u _ _ _ _ n35 hpq).elim | exact (hne_u _ _ _ _ n35 hpq.symm).elim
          | exact (hne_u _ _ _ _ n45 hpq).elim | exact (hne_u _ _ _ _ n45 hpq.symm).elim)
    obtain ⟨w, hw⟩ := exists_dom3_of_c6 H G.hTF G.hw0_nn G.hw0_sum G.hw0_deg cyc hcyc_inj
      ((hinS_iff v1 a1).mp s1) (hadj_u _ _ a1 a2 e12) (hadj_u _ _ a2 a3 e23)
      (hadj_u _ _ a3 a4 e34) (hadj_u _ _ a4 a5 e45) ((hinS_iff v5 a5).mp s5).symm
    have hlift_adj : ∀ (hwz : w ≠ z) (p : VegaV i) (hp : vegaActive i dy de p),
        H.Adj w (e.symm ⟨p, hp⟩).1 → vegaAdj i (e ⟨w, hwz⟩).1 p := fun hwz p hp hadj => by
      have := he_adj ⟨w, hwz⟩ (e.symm ⟨p, hp⟩); simp at this; exact this.mp hadj
    rcases hw with ⟨h0, h2, h4⟩ | ⟨h1, h3, h5⟩
    · have hwz : w ≠ z := H.ne_of_adj h0
      rw [show cyc 0 = z from rfl] at h0
      exact hnoE (e ⟨w, hwz⟩).1 ((hinS_iff _ (e ⟨w, hwz⟩).2).mpr (by simpa using h0.symm))
        (hlift_adj hwz v2 a2 h2) (hlift_adj hwz v4 a4 h4)
    · by_cases hwz : w = z
      · subst hwz; exact ns3 ((hinS_iff v3 a3).mpr h3)
      · exact hnoO (e ⟨w, hwz⟩).1 (e ⟨w, hwz⟩).2 (hlift_adj hwz v1 a1 h1) (hlift_adj hwz v3 a3 h3) (hlift_adj hwz v5 a5 h5)
  -- Three direct Vega extension builders:
  -- Builder 1: restore a single missing vertex `v0` (either `y = inr 1` or `2*i-1 = inl (2*i-1)`)
  have hbuild_restore : ∀ (dy' de' : Bool) (v0 : VegaV i),
      ¬ vegaActive i dy de v0 → vegaActive i dy' de' v0 →
      (∀ v : VegaV i, v ≠ v0 → (vegaActive i dy' de' v ↔ vegaActive i dy de v)) →
      (∀ v : VegaV i, vegaActive i dy de v → (inS v ↔ vegaAdj i v0 v)) →
      IsVegaGraph H i dy' de' := by
    intro dy' de' v0 hna hact hiff hnbhd
    let fwd : U → {v : VegaV i // vegaActive i dy' de' v} := fun u =>
      if h : u = z then ⟨v0, hact⟩
      else ⟨(e ⟨u, h⟩).1, (hiff _ (fun heq => hna (heq ▸ (e ⟨u, h⟩).2))).mpr (e ⟨u, h⟩).2⟩
    let inv : {v : VegaV i // vegaActive i dy' de' v} → U := fun ⟨v, hv⟩ =>
      if h : v = v0 then z else (e.symm ⟨v, (hiff v h).mp hv⟩).1
    refine ⟨hi, ⟨fwd, inv, ?_, ?_⟩, ?_⟩
    · intro u; dsimp only [fwd]; split_ifs with h
      · subst h; simp [inv]
      · dsimp only [inv]; have hne : (e ⟨u, h⟩).1 ≠ v0 := fun heq => hna (heq ▸ (e ⟨u, h⟩).2)
        rw [dif_neg hne]; simp
    · rintro ⟨v, hv⟩; apply Subtype.ext; dsimp only [inv]; split_ifs with h
      · subst h; simp [fwd]
      · dsimp only [fwd]; rw [dif_neg (e.symm ⟨v, (hiff v h).mp hv⟩).2]; simp
    · intro u1 u2
      show H.Adj u1 u2 ↔ vegaAdj i (fwd u1).1 (fwd u2).1
      by_cases h1 : u1 = z <;> by_cases h2 : u2 = z
      · subst h1; subst h2; simp [fwd, vegaAdj_irrefl hi]
      · subst h1; dsimp only [fwd]; rw [dif_pos rfl, dif_neg h2]
        have heq : H.Adj u1 u2 ↔ inS (e ⟨u2, h2⟩).1 := by rw [hinS_iff _ (e ⟨u2, h2⟩).2]; simp
        rw [heq, hnbhd _ (e ⟨u2, h2⟩).2]
      · subst h2; dsimp only [fwd]; rw [dif_neg h1, dif_pos rfl, H.adj_comm]
        have heq : H.Adj u2 u1 ↔ inS (e ⟨u1, h1⟩).1 := by rw [hinS_iff _ (e ⟨u1, h1⟩).2]; simp
        rw [heq, hnbhd _ (e ⟨u1, h1⟩).2]; exact ⟨vegaAdj_symm hi, vegaAdj_symm hi⟩
      · dsimp only [fwd]; rw [dif_neg h1, dif_neg h2]; exact he_adj ⟨u1, h1⟩ ⟨u2, h2⟩
  -- Builder 2: mirror + restore `2*i - 1` (for `de = true, SQ = {c, w}, SG = I_1`)
  have hbuild_mirror_end : de = true →
      (∀ v : VegaV i, vegaActive i dy true v → (inS v ↔ vegaAdj i (.inl ⟨2 * i - 1, by omega⟩) (vegaMirror i hi v))) →
      IsVegaGraph H i dy false := by
    intro hde hnbhd
    subst hde
    let v0 : VegaV i := .inl ⟨2 * i - 1, by omega⟩
    have hv0_na : ¬ vegaActive i dy true v0 := by simp [v0, vegaActive]
    have hv0_act : vegaActive i dy false v0 := by simp [v0, vegaActive]
    let fwd : U → {v : VegaV i // vegaActive i dy false v} := fun u =>
      if h : u = z then ⟨v0, hv0_act⟩
      else ⟨vegaMirror i hi (e ⟨u, h⟩).1, by
        have h1 := (vegaMirror_active hi dy true (e ⟨u, h⟩).1).mpr (e ⟨u, h⟩).2
        cases h2 : vegaMirror i hi (e ⟨u, h⟩).1 with
        | inl k => simp [vegaActive]
        | inr q => rw [h2] at h1; simpa [vegaActive] using h1⟩
    let inv : {v : VegaV i // vegaActive i dy false v} → U := fun ⟨v, hv⟩ =>
      if h : v = v0 then z
      else (e.symm ⟨vegaMirror i hi v, (vegaMirror_active hi dy true v).mpr (by
        cases v with
        | inl k => simp only [vegaActive, true_and]; intro hk; exact h (by simp [v0]; exact Fin.ext hk)
        | inr q => simpa [vegaActive] using hv)⟩).1
    refine ⟨hi, ⟨fwd, inv, ?_, ?_⟩, ?_⟩
    · intro u; dsimp only [fwd]; split_ifs with h
      · subst h; simp [inv]
      · dsimp only [inv]
        have hne : vegaMirror i hi (e ⟨u, h⟩).1 ≠ v0 := fun heq =>
          hv0_na (heq ▸ (vegaMirror_active hi dy true (e ⟨u, h⟩).1).mpr (e ⟨u, h⟩).2)
        rw [dif_neg hne]
        have hact2 : vegaActive i dy true (vegaMirror i hi (vegaMirror i hi (e ⟨u, h⟩).1)) := by
          rw [vegaMirror_invol hi (e ⟨u, h⟩).1]; exact (e ⟨u, h⟩).2
        have hinv : (⟨vegaMirror i hi (vegaMirror i hi (e ⟨u, h⟩).1), hact2⟩ :
            {v // vegaActive i dy true v}) = e ⟨u, h⟩ :=
          Subtype.ext (vegaMirror_invol hi (e ⟨u, h⟩).1)
        rw [hinv]; simp
    · rintro ⟨v, hv⟩; apply Subtype.ext; dsimp only [inv]; split_ifs with h
      · subst h; simp [fwd]
      · dsimp only [fwd]; rw [dif_neg (e.symm _).2]; simp [vegaMirror_invol hi]
    · intro u1 u2
      show H.Adj u1 u2 ↔ vegaAdj i (fwd u1).1 (fwd u2).1
      by_cases h1 : u1 = z <;> by_cases h2 : u2 = z
      · subst h1; subst h2; simp [fwd, vegaAdj_irrefl hi]
      · subst h1; dsimp only [fwd]; rw [dif_pos rfl, dif_neg h2]
        have heq : H.Adj u1 u2 ↔ inS (e ⟨u2, h2⟩).1 := by rw [hinS_iff _ (e ⟨u2, h2⟩).2]; simp
        rw [heq, hnbhd _ (e ⟨u2, h2⟩).2]
      · subst h2; dsimp only [fwd]; rw [dif_neg h1, dif_pos rfl, H.adj_comm]
        have heq : H.Adj u2 u1 ↔ inS (e ⟨u1, h1⟩).1 := by rw [hinS_iff _ (e ⟨u1, h1⟩).2]; simp
        rw [heq, hnbhd _ (e ⟨u1, h1⟩).2]; exact ⟨vegaAdj_symm hi, vegaAdj_symm hi⟩
      · dsimp only [fwd]
        rw [dif_neg h1, dif_neg h2, vegaMirror_adj hi dy (e ⟨u1, h1⟩).2 (e ⟨u2, h2⟩).2]
        exact he_adj ⟨u1, h1⟩ ⟨u2, h2⟩
  -- Builder 3: concrete `i = 2, dy = true` rotation for `N(z) = {x, w, 1, 2}` (both `de`!)
  have hbuild_i2_xw : ∀ (hi2 : i = 2) (_hdy : dy = true),
      (∀ v : VegaV i, vegaActive i true de v →
        (inS v ↔ v = .inr 0 ∨ v = .inr 7 ∨ v = .inl ⟨1, by omega⟩ ∨ v = .inl ⟨2, by omega⟩)) →
      IsVegaGraph H 2 false de := by
    intro hi2 hdy hnbhd; subst hi2; subst hdy
    let toOpt : U → Option (VegaV 2) := fun u => if h : u = z then none else some (e ⟨u, h⟩).1
    have htoOpt_act : ∀ u : U, match toOpt u with | none => True | some v => vegaActive 2 true de v := fun u => by
      dsimp only [toOpt]; split_ifs with h; trivial; exact (e ⟨u, h⟩).2
    let fwd : U → {w : VegaV 2 // vegaActive 2 false de w} := fun u => ⟨i2RotFwd (toOpt u), i2Rot_act_fwd de _ (htoOpt_act u)⟩
    let inv : {w : VegaV 2 // vegaActive 2 false de w} → U := fun ⟨w, hw⟩ =>
      match h : i2RotInv w with
      | none => z
      | some v => (e.symm ⟨v, by have := i2Rot_act_inv de w hw; rw [h] at this; exact this⟩).1
    refine ⟨le_rfl, ⟨fwd, inv, ?_, ?_⟩, ?_⟩
    · intro u; dsimp only [fwd, inv]
      have hl := i2Rot_left de (toOpt u) (htoOpt_act u)
      split
      · rename_i hnone; rw [hl] at hnone; dsimp only [toOpt] at hnone; split_ifs at hnone with h; exact h.symm
      · rename_i v hsome; rw [hl] at hsome; dsimp only [toOpt] at hsome; split_ifs at hsome with h
        injection hsome with hv; subst hv; simp
    · rintro ⟨w, hw⟩; apply Subtype.ext; dsimp only [fwd, inv]
      have hr := i2Rot_right de w hw
      split
      · rename_i hI
        dsimp only [toOpt]; rw [dif_pos rfl]; rw [hI] at hr; exact hr
      · rename_i v hI
        dsimp only [toOpt]; rw [dif_neg (e.symm _).2]
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
        rw [hI] at hr; exact hr
    · intro u1 u2
      show H.Adj u1 u2 ↔ vegaAdj 2 (i2RotFwd (toOpt u1)) (i2RotFwd (toOpt u2))
      have hne1 : ∀ u : U, toOpt u ≠ some (.inr 1) := fun u => by
        have ha := htoOpt_act u; cases h : toOpt u with
        | none => exact fun he => nomatch he
        | some v =>
          rw [h] at ha
          intro heq
          injection heq with hveq
          subst hveq
          simp [vegaActive] at ha
      rw [← i2Rot_adj (toOpt u1) (toOpt u2) (hne1 u1) (hne1 u2)]
      dsimp only [toOpt]
      by_cases h1 : u1 = z <;> by_cases h2 : u2 = z
      · subst h1; subst h2; simp [i2RotAdjLHS]
      · subst h1; rw [dif_pos rfl, dif_neg h2]
        have heq : H.Adj u1 u2 ↔ inS (e ⟨u2, h2⟩).1 := by rw [hinS_iff _ (e ⟨u2, h2⟩).2]; simp
        rw [heq, hnbhd _ (e ⟨u2, h2⟩).2]; rfl
      · subst h2; rw [dif_neg h1, dif_pos rfl, H.adj_comm]
        have heq : H.Adj u2 u1 ↔ inS (e ⟨u1, h1⟩).1 := by rw [hinS_iff _ (e ⟨u1, h1⟩).2]; simp
        rw [heq, hnbhd _ (e ⟨u1, h1⟩).2]; rfl
      · rw [dif_neg h1, dif_neg h2]; exact he_adj ⟨u1, h1⟩ ⟨u2, h2⟩
  -- Builder 4: concrete `i = 2, dy = true, de = true` mirror rotation for `N(z) = {x, v, 0, 4}`!
  have hbuild_i2_xv : ∀ (hi2 : i = 2) (_hdy : dy = true) (hde : de = true),
      (∀ v : VegaV i, vegaActive i true true v →
        (inS v ↔ v = .inr 0 ∨ v = .inr 6 ∨ v = .inl ⟨0, by omega⟩ ∨ v = .inl ⟨4, by omega⟩)) →
      IsVegaGraph H 2 false true := by
    intro hi2 hdy hde hnbhd; subst hi2; subst hdy; subst hde
    let toOpt : U → Option (VegaV 2) := fun u => if h : u = z then none else some (vegaMirror 2 le_rfl (e ⟨u, h⟩).1)
    have htoOpt_act : ∀ u : U, match toOpt u with | none => True | some v => vegaActive 2 true true v := fun u => by
      dsimp only [toOpt]; split_ifs with h; trivial; exact (vegaMirror_active le_rfl true true _).mpr (e ⟨u, h⟩).2
    let fwd : U → {w : VegaV 2 // vegaActive 2 false true w} := fun u => ⟨i2RotFwd (toOpt u), i2Rot_act_fwd true _ (htoOpt_act u)⟩
    let inv : {w : VegaV 2 // vegaActive 2 false true w} → U := fun ⟨w, hw⟩ =>
      match h : i2RotInv w with
      | none => z
      | some v => (e.symm ⟨vegaMirror 2 le_rfl v, (vegaMirror_active le_rfl true true v).mpr (by have := i2Rot_act_inv true w hw; rw [h] at this; exact this)⟩).1
    refine ⟨le_rfl, ⟨fwd, inv, ?_, ?_⟩, ?_⟩
    · intro u; dsimp only [fwd, inv]
      have hl := i2Rot_left true (toOpt u) (htoOpt_act u)
      split
      · rename_i hnone; rw [hl] at hnone; dsimp only [toOpt] at hnone; split_ifs at hnone with h; exact h.symm
      · rename_i v hsome; rw [hl] at hsome; dsimp only [toOpt] at hsome; split_ifs at hsome with h
        injection hsome with hv; subst hv
        have hact2 : vegaActive 2 true true (vegaMirror 2 le_rfl (vegaMirror 2 le_rfl (e ⟨u, h⟩).1)) := by
          rw [vegaMirror_invol le_rfl (e ⟨u, h⟩).1]; exact (e ⟨u, h⟩).2
        have hinv : (⟨vegaMirror 2 le_rfl (vegaMirror 2 le_rfl (e ⟨u, h⟩).1), hact2⟩ :
            {v // vegaActive 2 true true v}) = e ⟨u, h⟩ :=
          Subtype.ext (vegaMirror_invol le_rfl (e ⟨u, h⟩).1)
        rw [hinv]; simp
    · rintro ⟨w, hw⟩; apply Subtype.ext; dsimp only [fwd, inv]
      have hr := i2Rot_right true w hw
      split
      · rename_i hI
        dsimp only [toOpt]; rw [dif_pos rfl]; rw [hI] at hr; exact hr
      · rename_i v hI
        dsimp only [toOpt]; rw [dif_neg (e.symm _).2]
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply, vegaMirror_invol le_rfl]
        rw [hI] at hr; exact hr
    · intro u1 u2
      show H.Adj u1 u2 ↔ vegaAdj 2 (i2RotFwd (toOpt u1)) (i2RotFwd (toOpt u2))
      have hne1 : ∀ u : U, toOpt u ≠ some (.inr 1) := fun u => by
        have ha := htoOpt_act u; cases h : toOpt u with
        | none => exact fun he => nomatch he
        | some v =>
          rw [h] at ha
          intro heq
          injection heq with hveq
          subst hveq
          simp [vegaActive] at ha
      rw [← i2Rot_adj (toOpt u1) (toOpt u2) (hne1 u1) (hne1 u2)]
      dsimp only [toOpt]
      have hmir_iff : ∀ v : VegaV 2, (vegaMirror 2 le_rfl v = .inr 0 ∨ vegaMirror 2 le_rfl v = .inr 7 ∨
          vegaMirror 2 le_rfl v = .inl 1 ∨ vegaMirror 2 le_rfl v = .inl 2) ↔
          (v = .inr 0 ∨ v = .inr 6 ∨ v = .inl 0 ∨ v = .inl 4) := by
        intro v; revert v; decide
      by_cases h1 : u1 = z <;> by_cases h2 : u2 = z
      · subst h1; subst h2; simp [i2RotAdjLHS]
      · subst h1
        rw [dif_pos rfl, dif_neg h2]
        show H.Adj u1 u2 ↔ (vegaMirror 2 le_rfl (e ⟨u2, h2⟩).1 = .inr 0 ∨
            vegaMirror 2 le_rfl (e ⟨u2, h2⟩).1 = .inr 7 ∨
            vegaMirror 2 le_rfl (e ⟨u2, h2⟩).1 = .inl 1 ∨
            vegaMirror 2 le_rfl (e ⟨u2, h2⟩).1 = .inl 2)
        rw [hmir_iff (e ⟨u2, h2⟩).1]
        have heq : H.Adj u1 u2 ↔ inS (e ⟨u2, h2⟩).1 := by rw [hinS_iff _ (e ⟨u2, h2⟩).2]; simp
        rw [heq, hnbhd _ (e ⟨u2, h2⟩).2]; rfl
      · subst h2
        rw [dif_neg h1, dif_pos rfl, H.adj_comm]
        show H.Adj u2 u1 ↔ (vegaMirror 2 le_rfl (e ⟨u1, h1⟩).1 = .inr 0 ∨
            vegaMirror 2 le_rfl (e ⟨u1, h1⟩).1 = .inr 7 ∨
            vegaMirror 2 le_rfl (e ⟨u1, h1⟩).1 = .inl 1 ∨
            vegaMirror 2 le_rfl (e ⟨u1, h1⟩).1 = .inl 2)
        rw [hmir_iff (e ⟨u1, h1⟩).1]
        have heq : H.Adj u2 u1 ↔ inS (e ⟨u1, h1⟩).1 := by rw [hinS_iff _ (e ⟨u1, h1⟩).2]; simp
        rw [heq, hnbhd _ (e ⟨u1, h1⟩).2]; rfl
      · rw [dif_neg h1, dif_neg h2]
        show H.Adj u1 u2 ↔
            vegaAdj 2 (vegaMirror 2 le_rfl (e ⟨u1, h1⟩).1) (vegaMirror 2 le_rfl (e ⟨u2, h2⟩).1)
        rw [vegaMirror_adj le_rfl true (e ⟨u1, h1⟩).2 (e ⟨u2, h2⟩).2]
        exact he_adj ⟨u1, h1⟩ ⟨u2, h2⟩
  -- Arc structure of `SG = {k : Fin N | inS (.inl k)}` via `arc_of_indep_andrasfai`!
  let SG : Finset (Fin N) := Finset.univ.filter (fun k => inS (.inl k))
  obtain ⟨s0, hs0_arc⟩ := arc_of_indep_andrasfai hi SG (fun a ha b hb => hinS_ind (.inl a) (.inl b) (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
  have h123_not : ¬ ((∃ k : Fin N, k.val < i ∧ inS (.inl k)) ∧
                     (∃ k : Fin N, i ≤ k.val ∧ k.val < 2 * i ∧ inS (.inl k)) ∧
                     (∃ k : Fin N, 2 * i ≤ k.val ∧ inS (.inl k))) := by
    rintro ⟨⟨k1, hk1, hs1⟩, ⟨k2, hk2a, hk2b, hs2⟩, ⟨k3, hk3, hs3⟩⟩
    have d1 := hs0_arc k1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs1⟩)
    have d2 := hs0_arc k2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs2⟩)
    have d3 := hs0_arc k3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs3⟩)
    have hsub : ∀ a b : ℕ, a < N → b < N → ((b + N - a) % N) = if a ≤ b then b - a else b + N - a := by
      intro a b ha hb; split_ifs with hab
      · rw [show b + N - a = (b - a) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · exact Nat.mod_eq_of_lt (by omega)
    have hs0 := s0.isLt; have h1' := k1.isLt; have h2' := k2.isLt; have h3' := k3.isLt
    rw [hsub s0.val k1.val hs0 h1'] at d1; rw [hsub s0.val k2.val hs0 h2'] at d2; rw [hsub s0.val k3.val hs0 h3'] at d3
    split_ifs at d1 d2 d3 <;> omega
  -- Helper: `vegaAdj i (.inl p) (.inl q)` via plain `if` distance!
  let C : ExtCtx H i dy de inS :=
    { hi := hi, hinS_act := hinS_act, hinS_ind := hinS_ind, hinS_max := hinS_max,
      hnot_sub_nbhd := hnot_sub_nbhd, kill_c6 := kill_c6,
      hbuild_restore := hbuild_restore, hbuild_mirror_end := hbuild_mirror_end,
      hbuild_i2_xw := hbuild_i2_xw, hbuild_i2_xv := hbuild_i2_xv }
  by_cases h1 : ∃ k : Fin (3 * i - 1), k.val < i ∧ inS (.inl k) <;>
    by_cases h2 : ∃ k : Fin (3 * i - 1), i ≤ k.val ∧ k.val < 2 * i ∧ inS (.inl k) <;>
    by_cases h3 : ∃ k : Fin (3 * i - 1), 2 * i ≤ k.val ∧ inS (.inl k)
  · exact (h123_not ⟨h1, h2, h3⟩).elim
  · exact extend_case_110 H i dy de inS C h1 h2 h3
  · exact extend_case_101 H i dy de inS C h1 h2 h3
  · exact extend_case_100 H i dy de inS C h1 h2 h3
  · exact extend_case_011 H i dy de inS C h1 h2 h3
  · exact extend_case_010 H i dy de inS C h1 h2 h3
  · exact extend_case_001 H i dy de inS C h1 h2 h3
  · exact extend_case_000 H i dy de inS C h1 h2 h3

/- ## Section D: Part 0 — Strong Induction (`good_is_vega`) -/

set_option maxHeartbeats 1000000 in
/-- **Theorem J2 (Brandt-Thomasse Classification into `V_i`):**
    Every good graph `H` (maximal triangle-free, twin-free, non-3-colorable, with a probability weight
    having `deg_w > 1/3`) is isomorphic to a member of `V_i(dy, de)` for some `i ≥ 2`. -/
theorem good_is_vega {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (G : IsGood H) :
    ∃ (i : ℕ) (dy de : Bool), IsVegaGraph H i dy de := by
  suffices hstrong : ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj],
      Fintype.card V = n → IsGood K → ∃ (i : ℕ) (dy de : Bool), IsVegaGraph K i dy de from
    hstrong (Fintype.card U) U H rfl G
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ K _ hcard GK
    rcases regular_or_proper_support K (1 / 3) GK.w0 GK.hw0_nn GK.hw0_sum GK.hw0_deg with
      ⟨ω, δ, hpos, hsum, hδ, hreg⟩ | ⟨w, hwnn, hwsum, ⟨x, hwx0⟩, hwdeg⟩
    · -- Outcome 1: strictly positive regular probability weight -> Part 1!
      exact regular_good_is_vega K GK ω δ hpos hsum hreg hδ
    · -- Outcome 2: zero-weight vertex `x` -> `K' = K - x` is a smaller good graph!
      let V' := {u : V // u ≠ x}
      let K' : SimpleGraph V' := K.induce {u : V | u ≠ x}
      have : DecidableRel K'.Adj := fun a b => by change Decidable (K.Adj a.1 b.1); infer_instance
      have hcard' : Fintype.card V' < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (p := fun u => u ≠ x) (fun h => h rfl)
      let w' : V' → ℝ := fun u => w u.1
      have hw'_nn : ∀ u : V', 0 ≤ w' u := fun u => hwnn u.1
      have hw'_sum : ∑ u : V', w' u = 1 := by
        have hsplit := Fintype.sum_subtype_add_sum_subtype (fun u : V => u ≠ x) w
        have hcompl : ∑ u : {u : V // ¬ (u ≠ x)}, w u.1 = w x := by
          have : (Finset.univ : Finset {u : V // ¬ (u ≠ x)}) = {⟨x, by simp⟩} := by
            ext ⟨u, hu⟩; simp only [Finset.mem_univ, Finset.mem_singleton, Subtype.mk.injEq, true_iff]; push Not at hu; exact hu
          rw [this, Finset.sum_singleton]
        rw [hcompl, hwx0, add_zero, hwsum] at hsplit; exact hsplit
      have hw'_deg : ∀ u : V', (1 / 3 : ℝ) < ∑ v : V', if K'.Adj u v then w' v else 0 := by
        intro u
        have hsplit := Fintype.sum_subtype_add_sum_subtype (fun v : V => v ≠ x) (fun v => if K.Adj u.1 v then w v else 0)
        have hcompl : ∑ v : {v : V // ¬ (v ≠ x)}, (if K.Adj u.1 v.1 then w v.1 else 0) = 0 := by
          apply Finset.sum_eq_zero; intro ⟨v, hv⟩ _; push Not at hv; subst hv; simp [hwx0]
        rw [hcompl, add_zero] at hsplit
        have hite : ∀ v : V', (if K'.Adj u v then w' v else 0) = (if K.Adj u.1 v.1 then w v.1 else 0) := by
          intro v
          by_cases h : K.Adj u.1 v.1
          · rw [if_pos (show K'.Adj u v from h), if_pos h]
          · rw [if_neg (show ¬ (K'.Adj u v) from h), if_neg h]
        have hsum : ∑ v : V', (if K'.Adj u v then w' v else 0) = ∑ v : V, (if K.Adj u.1 v then w v else 0) := by
          rw [Finset.sum_congr rfl (fun v _ => hite v)]
          exact hsplit
        rw [hsum]; exact hwdeg u.1
      have hK'_TF : K'.CliqueFree 3 := by
        intro s hs; obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
        have h1 := hs.1; simp only [SimpleGraph.IsClique, Set.Pairwise, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at h1
        exact tf_contra GK.hTF (h1 (Or.inl rfl) (Or.inr (Or.inl rfl)) hab)
          (h1 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hbc)
          (h1 (Or.inl rfl) (Or.inr (Or.inr rfl)) hac)
      have hK'_Max : ∀ a b : V', a ≠ b → ¬ K'.Adj a b → ∃ z : V', K'.Adj a z ∧ K'.Adj b z := by
        intro a b hab hna; by_contra hno; push Not at hno
        have hab_V : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
        obtain ⟨z, hza, hzb⟩ := GK.hMax a.1 b.1 hab_V hna
        have hzx : x = z := by_contra fun hne => hno ⟨z, fun h => hne h.symm⟩ hza hzb
        subst hzx
        -- `N(a), N(b), N(x)` are pairwise disjoint in `V'` -> `wdeg a + wdeg b + wdeg x <= 1`, contra `3 * (1/3) = 1`!
        have hle1 : (∑ v : V, if K.Adj a.1 v then w v else 0) +
            (∑ v : V, if K.Adj b.1 v then w v else 0) +
            (∑ v : V, if K.Adj x v then w v else 0) ≤ ∑ v : V, w v := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum; intro v _
          by_cases hvx : v = x
          · rw [hvx]; simp [hwx0]
          · by_cases h1 : K.Adj a.1 v <;> by_cases h2 : K.Adj b.1 v <;> by_cases h3 : K.Adj x v
            · exact (tf_contra GK.hTF hza h3 h1).elim
            · exact (hno ⟨v, hvx⟩ h1 h2).elim
            · exact (tf_contra GK.hTF hza h3 h1).elim
            · simp [h1, h2, h3]
            · exact (tf_contra GK.hTF hzb h3 h2).elim
            · simp [h1, h2, h3]
            · simp [h1, h2, h3]
            · simp [h1, h2, h3, hwnn v]
        linarith [hwdeg a.1, hwdeg b.1, hwdeg x, hwsum]
      have hK'_Twin : ∀ a b : V', (∀ z : V', K'.Adj a z ↔ K'.Adj b z) → a = b := by
        intro a b hiff; by_contra hne
        have hne_V : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
        have hdiff : ¬ (K.Adj a.1 x ↔ K.Adj b.1 x) := fun hxiff => hne_V (GK.hTwin a.1 b.1 (fun z => by
          by_cases hzx : z = x
          · subst hzx; exact hxiff
          · exact hiff ⟨z, hzx⟩))
        have hkill : ∀ u v : V', (∀ z : V', K'.Adj u z ↔ K'.Adj v z) → K.Adj u.1 x → ¬ K.Adj v.1 x → False := by
          intro u v huv hux hnvx
          obtain ⟨z, hzv, hzx⟩ := GK.hMax v.1 x v.2 hnvx
          have hzx_ne : z ≠ x := (K.ne_of_adj hzx).symm
          have hzu : K.Adj u.1 z := (huv ⟨z, hzx_ne⟩).mpr hzv
          exact tf_contra GK.hTF hux hzx hzu
        by_cases hax : K.Adj a.1 x
        · exact hkill a b hiff hax (fun hbx => hdiff (iff_of_true hax hbx))
        · exact hkill b a (fun z => (hiff z).symm) (by_contra fun hbx => hdiff (iff_of_false hax hbx)) hax
      have hK'_Not3 : ¬ K'.Colorable 3 := by
        rintro ⟨col⟩
        by_cases hfull : ∀ c : Fin 3, ∃ u : V', col u = c
        · -- All 3 color classes nonempty -> prove `hNo2K2`, apply `ferrers_tripartite_classify`, extend 3-coloring!
          have hcol_ne : ∀ u v : V', K'.Adj u v → col u ≠ col v := fun u v hadj => col.valid hadj
          have hNo2K2 : ∀ c1 c2 : Fin 3, c1 ≠ c2 → ∀ x1 x2 y1 y2 : V',
              col x1 = c1 → col x2 = c1 → col y1 = c2 → col y2 = c2 →
              K'.Adj x1 y1 → K'.Adj x2 y2 → ¬ K'.Adj x1 y2 → ¬ K'.Adj x2 y1 → False := by
            intro c1 c2 hc12 x1 x2 y1 y2 hx1 hx2 hy1 hy2 h11 h22 hn12 hn21
            have hx1y2 : x1 ≠ y2 := fun h => hc12 (by rw [← hx1, h, hy2])
            have hx2y1 : x2 ≠ y1 := fun h => hc12 (by rw [← hx2, h, hy1])
            obtain ⟨z1, hz1x1, hz1y2⟩ := hK'_Max x1 y2 hx1y2 hn12
            obtain ⟨z2, hz2x2, hz2y1⟩ := hK'_Max x2 y1 hx2y1 hn21
            have hcz1 : col z1 ≠ c1 ∧ col z1 ≠ c2 := ⟨fun h => hcol_ne _ _ hz1x1 (hx1.trans h.symm), fun h => hcol_ne _ _ hz1y2 (hy2.trans h.symm)⟩
            have hcz2 : col z2 ≠ c1 ∧ col z2 ≠ c2 := ⟨fun h => hcol_ne _ _ hz2x2 (hx2.trans h.symm), fun h => hcol_ne _ _ hz2y1 (hy1.trans h.symm)⟩
            have hx12 : x1 ≠ x2 := fun h => hn12 (h ▸ h22)
            have hy12 : y1 ≠ y2 := fun h => hn12 (h ▸ h11)
            have hz12 : z1 ≠ z2 := fun h => tf_contra hK'_TF h11 hz2y1 (by rw [← h]; exact hz1x1)
            let cyc : Fin 6 → V' := ![x1, y1, z2, x2, y2, z1]
            have hcyc_inj : Function.Injective cyc := by
              have hne_c : ∀ u v : V', col u ≠ col v → u ≠ v := fun u v h heq => h (congrArg col heq)
              intro p q hpq; fin_cases p <;> fin_cases q <;> dsimp [cyc] at hpq ⊢
              all_goals first | rfl | exact (hx12 hpq).elim | exact (hx12 hpq.symm).elim
                              | exact (hy12 hpq).elim | exact (hy12 hpq.symm).elim
                              | exact (hz12 hpq).elim | exact (hz12 hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hx1, hy1]; exact hc12) hpq).elim | exact (hne_c _ _ (by rw [hx1, hy1]; exact hc12) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hx1, hy2]; exact hc12) hpq).elim | exact (hne_c _ _ (by rw [hx1, hy2]; exact hc12) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hx2, hy1]; exact hc12) hpq).elim | exact (hne_c _ _ (by rw [hx2, hy1]; exact hc12) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hx2, hy2]; exact hc12) hpq).elim | exact (hne_c _ _ (by rw [hx2, hy2]; exact hc12) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hx1]; exact hcz1.1.symm) hpq).elim | exact (hne_c _ _ (by rw [hx1]; exact hcz1.1.symm) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hx2]; exact hcz1.1.symm) hpq).elim | exact (hne_c _ _ (by rw [hx2]; exact hcz1.1.symm) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hx1]; exact hcz2.1.symm) hpq).elim | exact (hne_c _ _ (by rw [hx1]; exact hcz2.1.symm) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hx2]; exact hcz2.1.symm) hpq).elim | exact (hne_c _ _ (by rw [hx2]; exact hcz2.1.symm) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hy1]; exact hcz1.2.symm) hpq).elim | exact (hne_c _ _ (by rw [hy1]; exact hcz1.2.symm) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hy2]; exact hcz1.2.symm) hpq).elim | exact (hne_c _ _ (by rw [hy2]; exact hcz1.2.symm) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hy1]; exact hcz2.2.symm) hpq).elim | exact (hne_c _ _ (by rw [hy1]; exact hcz2.2.symm) hpq.symm).elim
                              | exact (hne_c _ _ (by rw [hy2]; exact hcz2.2.symm) hpq).elim | exact (hne_c _ _ (by rw [hy2]; exact hcz2.2.symm) hpq.symm).elim
            obtain ⟨v, hv⟩ := exists_dom3_of_c6 K' hK'_TF hw'_nn hw'_sum hw'_deg cyc hcyc_inj
              h11 hz2y1 hz2x2.symm h22 hz1y2 hz1x1.symm
            have hkill3 : ∀ u1 u2 u3 : V', col u1 = c1 → col u2 = c2 → col u3 ≠ c1 → col u3 ≠ c2 →
                K'.Adj v u1 → K'.Adj v u2 → K'.Adj v u3 → False := by
              intro u1 u2 u3 h1 h2 h3a h3b hv1 hv2 hv3
              have hvc1 : col v ≠ c1 := h1 ▸ hcol_ne v u1 hv1
              have hvc2 : col v ≠ c2 := h2 ▸ hcol_ne v u2 hv2
              have hv3' : col v = col u3 :=
                OMA.R_Erdos128_erdos_128_R2.fin3_third hc12 h3a.symm h3b.symm hvc1 hvc2
              exact hcol_ne v u3 hv3 hv3'
            rcases hv with ⟨h0, h2, h4⟩ | ⟨h1, h3, h5⟩
            · exact hkill3 x1 y2 z2 hx1 hy2 hcz2.1 hcz2.2 h0 h4 h2
            · exact hkill3 x2 y1 z1 hx2 hy1 hcz1.1 hcz1.2 h3 h1 h5
          have hex_emb : ∃ (d : ℕ) (_ : 2 ≤ d) (φ : V' → Fin (3 * d - 1)),
              Function.Injective φ ∧ ∀ u v : V', K'.Adj u v ↔ vegaAdj d (.inl (φ u)) (.inl (φ v)) := by
            rcases ferrers_tripartite_classify K' col hK'_TF hcol_ne
              (fun u v hne => hK'_Max u v (fun h => hne (congrArg col h)))
              (fun u v _ => hK'_Twin u v) hNo2K2 hfull with
              ⟨d, hd, _, e, hadj, _⟩ | ⟨d, hd, _, e, hadj, _⟩ | ⟨d, hd, φ, hinj, hadj, _⟩
            · exact ⟨d, hd, e, e.injective, hadj⟩
            · exact ⟨d, hd, fun u => (e u).1, fun a b h => e.injective (Subtype.ext h), hadj⟩
            · exact ⟨d, hd, φ, hinj, hadj⟩
          obtain ⟨d, hd, φ, hφ_inj, hφ_adj⟩ := hex_emb
          let Nx' : Finset (Fin (3 * d - 1)) := (Finset.univ.filter (fun u : V' => K.Adj x u.1)).image φ
          have hNx'_ind : ∀ a ∈ Nx', ∀ b ∈ Nx', ¬ vegaAdj d (.inl a) (.inl b) := by
            intro a ha b hb hadj
            obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
            exact tf_contra GK.hTF (Finset.mem_filter.mp hu).2 ((hφ_adj u v).mpr hadj) (Finset.mem_filter.mp hv).2
          obtain ⟨s0, hs0⟩ := arc_of_indep_andrasfai hd Nx' hNx'_ind
          -- Color `And(d)` in 3 consecutive arcs `[0, d-1], [d, 2d-1], [2d, 3d-2]` shifted by `s0`, and color `x` with `1`!
          let M := 3 * d - 1
          let dist : Fin M → ℕ := fun p => (p.val + M - s0.val) % M
          let colK : V → Fin 3 := fun u =>
            if h : u = x then 1
            else
              let dd := dist (φ ⟨u, h⟩)
              if dd < d then 0 else if dd < 2 * d then 1 else 2
          have hK_col3 : K.Colorable 3 := by
            refine ⟨SimpleGraph.Coloring.mk colK ?_⟩
            intro u v hadj; dsimp only [colK]
            by_cases hux : u = x
            · subst hux; have hvx : v ≠ u := (K.ne_of_adj hadj).symm
              rw [dif_pos rfl, dif_neg hvx]
              have hlt : dist (φ ⟨v, hvx⟩) < d :=
                hs0 _ (Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩))
              rw [if_pos hlt]; decide
            · by_cases hvx : v = x
              · subst hvx; rw [dif_neg hux, dif_pos rfl]
                have hlt : dist (φ ⟨u, hux⟩) < d :=
                  hs0 _ (Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.symm⟩))
                rw [if_pos hlt]; decide
              · rw [dif_neg hux, dif_neg hvx]
                have huv : vegaAdj d (.inl (φ ⟨u, hux⟩)) (.inl (φ ⟨v, hvx⟩)) := (hφ_adj ⟨u, hux⟩ ⟨v, hvx⟩).mp hadj
                simp only [vegaAdj] at huv
                set p := φ ⟨u, hux⟩; set q := φ ⟨v, hvx⟩
                have hp := p.isLt; have hq := q.isLt; have hs := s0.isLt
                have hsub_mod : ∀ a b : ℕ, a < M → b < M → ((b + M - a) % M) = if a ≤ b then b - a else b + M - a := by
                  intro a b ha hb; split_ifs with hab
                  · rw [show b + M - a = (b - a) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                  · exact Nat.mod_eq_of_lt (by omega)
                have hdp : dist p = if s0.val ≤ p.val then p.val - s0.val else p.val + M - s0.val := hsub_mod s0.val p.val hs hp
                have hdq : dist q = if s0.val ≤ q.val then q.val - s0.val else q.val + M - s0.val := hsub_mod s0.val q.val hs hq
                have hpq_mod : (q.val + M - p.val) % M = if p.val ≤ q.val then q.val - p.val else q.val + M - p.val := hsub_mod p.val q.val hp hq
                change d ≤ (q.val + M - p.val) % M ∧ (q.val + M - p.val) % M ≤ 2 * d - 1 at huv
                rw [hpq_mod] at huv
                -- `dist p` and `dist q` cannot lie in the same block `[0,d-1]`, `[d,2d-1]`, `[2d,3d-2]`!
                have hne_blk : ¬ ((dist p < d ∧ dist q < d) ∨
                    (d ≤ dist p ∧ dist p < 2 * d ∧ d ≤ dist q ∧ dist q < 2 * d) ∨
                    (2 * d ≤ dist p ∧ 2 * d ≤ dist q)) := by
                  rw [hdp, hdq]; split_ifs at huv ⊢ <;> omega
                split_ifs with h1' h2' h3' h4' <;> first | decide | (exfalso; apply hne_blk; try omega)
          exact GK.hNot3 hK_col3
        · -- Some color `c0` is unused in `K'` -> `K'` is bipartite + maximal TF + twin-free -> `|V'| ≤ 2` -> `|V| ≤ 3` -> 3-colorable!
          push Not at hfull; obtain ⟨c0, hc0⟩ := hfull
          have hbip_adj : ∀ u v : V', col u ≠ col v → K'.Adj u v := by
            intro u v hne; by_contra hna
            obtain ⟨z, hzu, hzv⟩ := hK'_Max u v (fun h => hne (congrArg col h)) hna
            have h1 := col.valid hzu; have h2 := col.valid hzv
            have h3 := hc0 z
            have : col z = c0 := OMA.R_Erdos128_erdos_128_R2.fin3_third hne (hc0 u) (hc0 v) h1.symm h2.symm
            exact h3 this
          have hcol_inj : Function.Injective col := by
            intro u v heq; apply hK'_Twin u v; intro z
            by_cases hcz : col z = col u
            · exact ⟨fun h => (col.valid h hcz.symm).elim, fun h => (col.valid h (heq.symm.trans hcz.symm)).elim⟩
            · exact ⟨fun _ => hbip_adj v z (by rw [← heq]; exact Ne.symm hcz), fun _ => hbip_adj u z (Ne.symm hcz)⟩
          have hcardV' : Fintype.card V' ≤ 2 := by
            let f : V' → {c : Fin 3 // c ≠ c0} := fun u => ⟨col u, hc0 u⟩
            have hf_inj : Function.Injective f := fun a b h => hcol_inj (congrArg Subtype.val h)
            have hle := Fintype.card_le_of_injective f hf_inj
            have h2 : Fintype.card {c : Fin 3 // c ≠ c0} = 2 := by fin_cases c0 <;> decide
            omega
          have hK_col3 : K.Colorable 3 := by
            let eV' := Fintype.equivFin V'
            refine ⟨SimpleGraph.Coloring.mk (fun v =>
              if h : v = x then 2 else ⟨(eV' ⟨v, h⟩).val, by
                have h1 := (eV' ⟨v, h⟩).isLt; omega⟩) ?_⟩
            intro u v hadj heq
            by_cases hux : u = x
            · rw [dif_pos hux] at heq
              have hvx : v ≠ x := fun h => K.ne_of_adj hadj (hux.trans h.symm)
              rw [dif_neg hvx] at heq
              have hval : (2 : Fin 3).val = (eV' ⟨v, hvx⟩).val := congrArg Fin.val heq
              have h1 := (eV' ⟨v, hvx⟩).isLt
              omega
            · rw [dif_neg hux] at heq
              by_cases hvx : v = x
              · rw [dif_pos hvx] at heq
                have hval : (eV' ⟨u, hux⟩).val = (2 : Fin 3).val := congrArg Fin.val heq
                have h1 := (eV' ⟨u, hux⟩).isLt
                omega
              · rw [dif_neg hvx] at heq
                have hval : (eV' ⟨u, hux⟩).val = (eV' ⟨v, hvx⟩).val := by
                  have h := congrArg Fin.val heq
                  simpa using h
                exact K.ne_of_adj hadj (congrArg Subtype.val (eV'.injective (Fin.ext hval)))
          exact GK.hNot3 hK_col3
      let GK' : IsGood K' := ⟨hK'_TF, hK'_Max, hK'_Twin, hK'_Not3, w', hw'_nn, hw'_sum, hw'_deg⟩
      obtain ⟨i, dy, de, hVega'⟩ := ih (Fintype.card V') hcard' V' K' rfl GK'
      exact extend_vega_is_vega K GK x i dy de hVega'
end Erdos128J2

theorem OMA.solution : OMA.R_Erdos128_erdos_128_R2_H2_R3.H2 := by
  intro V _ M hMTF hMmax hMδ hMNot3
  obtain ⟨U, _, _, H, _, φ, w0, hφ_surj, hφ_iff, hHTF, hHmax, hHtwin, hHnot3,
    hw0_pos, hw0_sum, hw0_deg⟩ :=
    Erdos128ThmJ.twin_quotient_of_maximal_tf M hMTF hMmax hMδ hMNot3
  let G : Erdos128J2.IsGood H :=
    ⟨hHTF, hHmax, hHtwin, hHnot3, w0, fun x => le_of_lt (hw0_pos x), hw0_sum, hw0_deg⟩
  obtain ⟨i, dy, de, hi, e, he_adj⟩ := Erdos128J2.good_is_vega H G
  refine ⟨i, dy, de, fun v => (e (φ v)).1, hi, ?_, ?_, ?_⟩
  · intro v
    have hv := (e (φ v)).2
    dsimp only
    generalize (e (φ v)).1 = x at hv ⊢
    cases x with
    | inl k => exact hv
    | inr j => exact hv
  · intro w hw
    have hw' : Erdos128Vega.vegaActive i dy de w := by
      cases w with
      | inl k => simpa [Erdos128Vega.vegaActive] using hw
      | inr j => simpa [Erdos128Vega.vegaActive] using hw
    obtain ⟨v, hv⟩ := hφ_surj (e.symm ⟨w, hw'⟩)
    exact ⟨v, by simp [hv]⟩
  · intro u v
    have huv : M.Adj u v ↔ Erdos128Vega.vegaAdj i (e (φ u)).1 (e (φ v)).1 :=
      (hφ_iff u v).trans (he_adj (φ u) (φ v))
    cases h1 : (e (φ u)).1 <;> cases h2 : (e (φ v)).1 <;>
      simpa [h1, h2, Erdos128Vega.vegaAdj] using huv
