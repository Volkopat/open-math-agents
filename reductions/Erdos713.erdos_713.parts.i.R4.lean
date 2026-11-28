import FormalConjectures.ErdosProblems.«713»
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Analysis.Subadditive
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
Reduction R4 of Erdős Problem 713 (i).

Proved here: isolated vertices can be dropped; any limiting exponent lies in [1, 2) (a star or a
matching gives ex ≥ n/2, Kővári–Sós–Turán counting gives ex ≤ q n^(2-1/q)); forests satisfy
ex ≤ q n; a cyclic graph has ex(n)/n → ∞ (high-girth bounded-degree hosts), so its limiting
exponent exceeds 1; the limit for a graph with a cycle follows from limits for its cyclic
components (the largest exponent wins, forest components cost O(n)); pruning a leaf of a
connected cyclic graph changes ex by O(n), so connected cyclic graphs reduce to minimum degree 2.

What remains: a positive linear limit for isolate-free forests with at least two edges (H1), and
a power-law limit for connected cyclic bipartite graphs of minimum degree at least 2 (H2).
-/

-- Credit: @mucoucah

namespace OMA.R_Erdos713_erdos_713_parts_i_R4

open Filter SimpleGraph Finset
open scoped Classical Topology Sym2

theorem contained_in_balanced_bipartite {q : ℕ} (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) : G ⊑ completeBipartiteGraph (Fin q) (Fin q) := by
  obtain ⟨c⟩ := bip
  let f : Fin q → Fin q ⊕ Fin q := fun v => if c v = 0 then .inl v else .inr v
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro v w h
    have hc := c.valid h
    by_cases hv : c v = 0 <;> by_cases hw : c w = 0
    · exact (hc (hv.trans hw.symm)).elim
    · simp [f, hv, hw]
    · simp [f, hv, hw]
    · have hv' : c v = 1 := by exact Fin.eq_one_of_ne_zero _ hv
      have hw' : c w = 1 := by exact Fin.eq_one_of_ne_zero _ hw
      exact (hc (hv'.trans hw'.symm)).elim
  · intro v w h
    change f v = f w at h
    have hf (u) : Sum.elim id id (f u) = u := by
      by_cases hu : c u = 0 <;> simp [f, hu]
    simpa only [hf] using congrArg (Sum.elim id id) h

-- Count pairs of a vertex and an ordered tuple of distinct neighbors.
theorem rectangular_degree_count {s t n : ℕ} (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin s) (Fin t)).Free X) :
    (∑ v : Fin n, (X.degree v).descFactorial s) ≤ n ^ s * (t - 1) := by
  let R (v : Fin n) (f : Fin s ↪ Fin n) : Prop := ∀ i, X.Adj v (f i)
  have hrow (v : Fin n) :
      (univ.bipartiteAbove R v).card = (X.degree v).descFactorial s := by
    let e : (univ.bipartiteAbove R v) ≃ (Fin s ↪ X.neighborFinset v) :=
      { toFun := fun f =>
          ⟨fun i => ⟨f.val i, (mem_neighborFinset X v _).mpr (((mem_bipartiteAbove R).mp f.property).2 i)⟩,
            fun _ _ h => f.val.injective (congrArg Subtype.val h)⟩
        invFun := fun f =>
          ⟨f.trans (Function.Embedding.subtype _),
            (mem_bipartiteAbove R).mpr ⟨mem_univ _, fun i => (mem_neighborFinset X v _).mp (f i).property⟩⟩
        left_inv := fun f => Subtype.ext (Function.Embedding.ext fun _ => rfl)
        right_inv := fun f => Function.Embedding.ext fun _ => rfl }
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_fin]
    rw [Fintype.card_coe, card_neighborFinset_eq_degree]
  have hcol (f : Fin s ↪ Fin n) : (univ.bipartiteBelow R f).card ≤ t - 1 := by
    have hlt : (univ.bipartiteBelow R f).card < t := by
      by_contra! hlarge
      obtain ⟨U, hU, hcard⟩ := exists_subset_card_eq hlarge
      apply free
      apply completeBipartiteGraph_isContained_iff.mpr
      refine ⟨univ.map f, U, by simp, by simpa using hcard, ?_⟩
      intro a ha b hb
      obtain ⟨i, -, rfl⟩ := mem_map.mp (mem_coe.mp ha)
      exact (((mem_bipartiteBelow R).mp (hU (mem_coe.mp hb))).2 i).symm
    omega
  calc
    _ = ∑ v : Fin n, (univ.bipartiteAbove R v).card := by simp only [hrow]
    _ = ∑ f : Fin s ↪ Fin n, (univ.bipartiteBelow R f).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ ≤ ∑ _ : Fin s ↪ Fin n, (t - 1) := sum_le_sum (fun f _ => hcol f)
    _ = n.descFactorial s * (t - 1) := by
      simp [Fintype.card_embedding_eq]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow n s)

theorem balanced_degree_count {q n : ℕ} (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin q) (Fin q)).Free X) :
    (∑ v : Fin n, (X.degree v).descFactorial q) ≤ n ^ q * (q - 1) :=
  rectangular_degree_count X free

theorem rectangular_edge_bound {s t n : ℕ} (hs : 0 < s) (hn : 0 < n)
    (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin s) (Fin t)).Free X) {C : ℝ}
    (hC : 0 ≤ C) (ht : ((t - 1 : ℕ) : ℝ) ≤ C ^ s) :
    2 * (X.edgeFinset.card : ℝ) ≤
      C * (n : ℝ) ^ (2 - 1 / (s : ℝ)) + (s - 1 : ℕ) * (n : ℝ) := by
  have npos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let d (v : Fin n) := X.degree v + 1 - s
  have hcount : (∑ v : Fin n, (d v : ℝ) ^ s) ≤ (n : ℝ) ^ s * (t - 1 : ℕ) := by
    exact_mod_cast (sum_le_sum (fun v _ => Nat.pow_sub_le_descFactorial (X.degree v) s)).trans
      (rectangular_degree_count X free)
  let m : ℝ := (∑ v : Fin n, (d v : ℝ)) / n
  have hjensen : m ^ s ≤ (∑ v : Fin n, (d v : ℝ) ^ s) / n := by
    have hw : (∑ _ : Fin n, (1 / (n : ℝ))) = 1 := by simp [npos.ne']
    simp only [m, div_eq_inv_mul]
    simpa only [one_div, ← Finset.mul_sum] using
      Real.pow_arith_mean_le_arith_mean_pow univ (fun _ : Fin n => 1 / (n : ℝ))
        (fun v => (d v : ℝ)) (fun _ _ => by positivity) hw (fun _ _ => by positivity) s
  let β : ℝ := 1 - 1 / (s : ℝ)
  have hpowers : ((n : ℝ) ^ β) ^ s = (n : ℝ) ^ s / n := by
    have cs : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
    rw [← Real.rpow_natCast ((n : ℝ) ^ β) s, ← Real.rpow_mul npos.le]
    dsimp only [β]
    rw [sub_mul, one_mul, div_mul_cancel₀ _ cs, Real.rpow_sub npos, Real.rpow_natCast,
      Real.rpow_one]
  have havg : m ≤ C * (n : ℝ) ^ β := by
    apply le_of_pow_le_pow_left₀ hs.ne' (by positivity)
    calc
      m ^ s ≤ ((n : ℝ) ^ s * (t - 1 : ℕ)) / n :=
        hjensen.trans (div_le_div_of_nonneg_right hcount npos.le)
      _ = (t - 1 : ℕ) * ((n : ℝ) ^ s / n) := by ring
      _ ≤ (C * (n : ℝ) ^ β) ^ s := by
        rw [mul_pow, hpowers]
        exact mul_le_mul_of_nonneg_right ht (by positivity)
  have hdeg : (∑ v : Fin n, (X.degree v : ℝ)) ≤ n * m + (s - 1 : ℕ) * (n : ℝ) := by
    calc
      _ ≤ ∑ v : Fin n, ((d v : ℝ) + (s - 1 : ℕ)) := by
        apply sum_le_sum
        intro v _
        exact_mod_cast (show X.degree v ≤ d v + (s - 1) by dsimp [d]; omega)
      _ = _ := by
        simp only [m, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hhand : (∑ v : Fin n, (X.degree v : ℝ)) = 2 * X.edgeFinset.card := by
    exact_mod_cast X.sum_degrees_eq_twice_card_edges
  have hpow : (n : ℝ) * (C * (n : ℝ) ^ β) = C * (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
    rw [show (2 : ℝ) - 1 / s = 1 + β by dsimp [β]; ring, Real.rpow_add npos, Real.rpow_one]
    ring
  rw [← hhand, ← hpow]
  exact hdeg.trans (add_le_add (mul_le_mul_of_nonneg_left havg npos.le) le_rfl)

theorem balanced_edge_bound {q n : ℕ} (hq : 0 < q) (hn : 0 < n)
    (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin q) (Fin q)).Free X) :
    (X.edgeFinset.card : ℝ) ≤ q * (n : ℝ) ^ (2 - 1 / (q : ℝ)) := by
  have npos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have qpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpow : (((q - 1 : ℕ) : ℝ)) ≤ (q : ℝ) ^ q :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (le_self_pow₀ hq1 hq.ne')
  have hbound := rectangular_edge_bound hq hn X free qpos.le hqpow
  let β : ℝ := 1 - 1 / (q : ℝ)
  have hβ : 0 ≤ β := sub_nonneg.mpr ((div_le_one qpos).mpr hq1)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase := Real.one_le_rpow hn1 hβ
  have hsingle : ((q - 1 : ℕ) : ℝ) * n ≤ (q : ℝ) * (n : ℝ) ^ (2 - 1 / (q : ℝ)) := by
    rw [show (2 : ℝ) - 1 / q = 1 + β by dsimp [β]; ring, Real.rpow_add npos, Real.rpow_one,
      ← mul_assoc]
    calc
      _ ≤ (q : ℝ) * n := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ _)) (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hbase
  linarith

theorem bipartite_extremal_upper {q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) {n : ℕ} (hn : 0 < n) :
    (extremalNumber n G : ℝ) ≤ (q : ℝ) * (n : ℝ) ^ (2 - 1 / (q : ℝ)) := by
  have hcard := contained_in_balanced_bipartite G bip
  have hmono : extremalNumber n G ≤ extremalNumber n (completeBipartiteGraph (Fin q) (Fin q)) :=
    hcard.extremalNumber_le
  apply (Nat.cast_le.mpr hmono).trans
  rw [← Fintype.card_fin n, extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro X _ hfree
  rw [Fintype.card_fin]
  exact balanced_edge_bound hq hn X hfree

theorem exponent_le_bipartite_bound {q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) {α c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α)
      atTop (𝓝 c)) :
    α ≤ 2 - 1 / (q : ℝ) := by
  by_contra! hα
  let β : ℝ := 2 - 1 / (q : ℝ)
  have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - α)) atTop (𝓝 0) := by
    rw [← neg_sub]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => (q : ℝ) * (n : ℝ) ^ (β - α)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpower.const_mul (q : ℝ)
  have hle : c ≤ 0 := le_of_tendsto_of_tendsto hlim hzero (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [Real.rpow_sub hnpos, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (bipartite_extremal_upper hq G bip (by omega)) (by positivity))
  exact hc.not_ge hle
theorem consecutive_matching_degree (n : ℕ) (v : Fin n) :
    ((SimpleGraph.mk (fun v w : Fin n => v.val / 2 = w.val / 2 ∧ v ≠ w) ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩ ⟨fun _ h => h.2 rfl⟩)).degree v ≤ 1 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_le_one]
  intro a ha b hb
  have ha' : v.val / 2 = a.val / 2 ∧ v ≠ a := (mem_neighborFinset _ _ _).mp ha
  have hb' : v.val / 2 = b.val / 2 ∧ v ≠ b := (mem_neighborFinset _ _ _).mp hb
  have hna : v.val ≠ a.val := fun h => ha'.2 (Fin.ext h)
  have hnb : v.val ≠ b.val := fun h => hb'.2 (Fin.ext h)
  apply Fin.ext
  omega

theorem consecutive_matching_edges (n : ℕ) :
    n / 2 ≤ ((SimpleGraph.mk (fun v w : Fin n => v.val / 2 = w.val / 2 ∧ v ≠ w) ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩ ⟨fun _ h => h.2 rfl⟩)).edgeFinset.card := by
  let a (i : Fin (n / 2)) : Fin n := ⟨2 * i.val, by have hi := i.isLt; omega⟩
  let b (i : Fin (n / 2)) : Fin n := ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩
  have h (i) : s(a i, b i) ∈ ((SimpleGraph.mk (fun v w : Fin n => v.val / 2 = w.val / 2 ∧ v ≠ w) ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩ ⟨fun _ h => h.2 rfl⟩)).edgeFinset := by
    rw [mem_edgeFinset, mem_edgeSet]
    change (2 * i.val) / 2 = (2 * i.val + 1) / 2 ∧ a i ≠ b i
    refine ⟨by omega, ?_⟩
    intro heq
    have eq := congrArg Fin.val heq
    change 2 * i.val = 2 * i.val + 1 at eq
    omega
  let f (i : Fin (n / 2)) : ((SimpleGraph.mk (fun v w : Fin n => v.val / 2 = w.val / 2 ∧ v ≠ w) ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩ ⟨fun _ h => h.2 rfl⟩)).edgeFinset := ⟨_, h i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have eq : s(a i, b i) = s(a j, b j) := congrArg Subtype.val hij
    rcases Sym2.eq_iff.mp eq with ⟨heq, _⟩ | ⟨heq, _⟩
    · have hval := congrArg Fin.val heq
      change 2 * i.val = 2 * j.val at hval
      exact Fin.ext (by omega)
    · have hval := congrArg Fin.val heq
      change 2 * i.val = 2 * j.val + 1 at hval
      omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem star_free_of_degree_le_one {q n : ℕ} (G : SimpleGraph (Fin q))
    (edges : 2 ≤ G.edgeFinset.card) (degree : ∀ v, G.degree v ≤ 1) (r : Fin n) :
    G.Free (starGraph r) := by
  rintro ⟨f⟩
  have hcenter (v w : Fin q) (h : G.Adj v w) : f v = r ∨ f w = r :=
    (starGraph_adj.mp (f.toHom.map_adj h)).2
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < G.edgeFinset.card)
  obtain ⟨u, hu⟩ : ∃ u, f u = r := by
    induction e using Sym2.inductionOn with
    | _ v w =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      exact (hcenter v w he).elim (fun h => ⟨v, h⟩) (fun h => ⟨w, h⟩)
  have hsub : G.edgeFinset ⊆ G.incidenceFinset u := by
    intro e he
    rw [incidenceFinset_eq_filter, mem_filter]
    refine ⟨he, ?_⟩
    induction e using Sym2.inductionOn with
    | _ v w =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rcases hcenter v w he with hv | hw
      · have hv' : v = u := f.injective (hv.trans hu.symm)
        simp [hv']
      · have hw' : w = u := f.injective (hw.trans hu.symm)
        simp [hw']
  have hle := Finset.card_le_card hsub
  rw [card_incidenceFinset_eq_degree] at hle
  have hdegree := degree u
  omega

theorem extremal_linear_lower {q n : ℕ} (G : SimpleGraph (Fin q))
    (edges : 2 ≤ G.edgeFinset.card) (hn : 0 < n) : n / 2 ≤ extremalNumber n G := by
  by_cases h : ∀ v, G.degree v ≤ 1
  · let r : Fin n := ⟨0, hn⟩
    have hfree := star_free_of_degree_le_one G edges h r
    have hdegree := (starGraph r).card_incidenceFinset_eq_degree r
    have hcard : n - 1 ≤ (starGraph r).edgeFinset.card := by
      rw [degree_starGraph_center, Fintype.card_fin] at hdegree
      rw [← hdegree]
      exact Finset.card_le_card (by
        rw [incidenceFinset_eq_filter]
        exact filter_subset _ _)
    have hex := card_edgeFinset_le_extremalNumber hfree
    rw [Fintype.card_fin] at hex
    exact (by omega : n / 2 ≤ n - 1).trans (hcard.trans hex)
  · obtain ⟨v, hv⟩ := not_forall.mp h
    have hfree : G.Free ((SimpleGraph.mk (fun v w : Fin n => v.val / 2 = w.val / 2 ∧ v ≠ w) ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩ ⟨fun _ h => h.2 rfl⟩)) := by
      rintro ⟨f⟩
      exact hv ((f.degree_le v).trans (consecutive_matching_degree n (f v)))
    have hex := card_edgeFinset_le_extremalNumber hfree
    rw [Fintype.card_fin] at hex
    exact (consecutive_matching_edges n).trans hex

theorem exponent_ge_one {q : ℕ} (G : SimpleGraph (Fin q))
    (edges : 2 ≤ G.edgeFinset.card) {α c : ℝ}
    (hlim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α)
      atTop (𝓝 c)) : 1 ≤ α := by
  by_contra! hα
  have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    rw [← neg_sub]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop (𝓝 0) := by
    have hmul := hlim.mul hpower
    rw [mul_zero] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [Real.rpow_sub hnpos, Real.rpow_one, div_mul_div_comm,
      div_eq_div_iff (by positivity) hnpos.ne']
    ring
  have hle : (1 / 3 : ℝ) ≤ 0 := ge_of_tendsto hzero (by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [le_div_iff₀ hnpos]
    have hnat : n ≤ 3 * extremalNumber n G :=
      (show n ≤ 3 * (n / 2) by omega).trans
        (Nat.mul_le_mul_left 3 (extremal_linear_lower G edges (by omega)))
    have hreal : (n : ℝ) ≤ 3 * (extremalNumber n G : ℝ) := by exact_mod_cast hnat
    linarith)
  norm_num at hle

theorem connected_copy_from_left {V W Z : Type*} {G : SimpleGraph V}
    {A : SimpleGraph W} {B : SimpleGraph Z} (conn : G.Connected)
    (f : Copy G (A ⊕g B)) {u : V} {a : W} (hu : f u = Sum.inl a) : G ⊑ A := by
  let g (v : V) : W := Sum.elim id (fun _ => a) (f v)
  have hg (v : V) : f v = Sum.inl (g v) := by
    cases hv : f v with
    | inl w => simp [g, hv]
    | inr z =>
      have hpath := (conn u v).map f.toHom
      change (A ⊕g B).Reachable (f u) (f v) at hpath
      rw [hu, hv] at hpath
      exact (not_reachable_sum_inl_inr a z hpath).elim
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro v w adj
    have h := f.toHom.map_adj adj
    change (A ⊕g B).Adj (f v) (f w) at h
    rw [hg v, hg w] at h
    exact sum_adj_inl.mp h
  · intro v w eq
    change g v = g w at eq
    apply f.injective
    change f v = f w
    rw [hg v, hg w, eq]

theorem connected_free_sum {V W Z : Type*} {G : SimpleGraph V}
    {A : SimpleGraph W} {B : SimpleGraph Z} (conn : G.Connected)
    (freeA : G.Free A) (freeB : G.Free B) : G.Free (A ⊕g B) := by
  rintro ⟨f⟩
  obtain ⟨u⟩ := conn.nonempty
  cases hu : f u with
  | inl a => exact freeA (connected_copy_from_left conn f hu)
  | inr b =>
    apply freeB (connected_copy_from_left conn (Iso.sumComm.toCopy.comp f) (u := u) (a := b) ?_)
    change Sum.swap (f u) = Sum.inl b
    rw [hu]
    rfl

theorem connected_extremal_superadditive {q : ℕ} (G : SimpleGraph (Fin q))
    (conn : G.Connected) (edges : 2 ≤ G.edgeFinset.card) (m n : ℕ) :
    extremalNumber m G + extremalNumber n G ≤ extremalNumber (m + n) G := by
  have hG : G ≠ ⊥ := by
    intro heq
    rw [edgeFinset_eq_empty.mpr heq] at edges
    simp at edges
  obtain ⟨A, hAd, hA⟩ := exists_isExtremal_free (V := Fin m) hG
  obtain ⟨B, hBd, hB⟩ := exists_isExtremal_free (V := Fin n) hG
  let _ := hAd
  let _ := hBd
  calc
    extremalNumber m G + extremalNumber n G = A.edgeFinset.card + B.edgeFinset.card := by
      rw [card_edgeFinset_of_isExtremal_free hA, card_edgeFinset_of_isExtremal_free hB,
        Fintype.card_fin, Fintype.card_fin]
    _ = (A ⊕g B).edgeFinset.card := by
      rw [edgeFinset_card, edgeFinset_card, edgeFinset_card,
        Fintype.card_congr (edgeSetSumEquiv (G := A) (H := B)), Fintype.card_sum]
    _ ≤ _ := by
      simpa only [Fintype.card_sum, Fintype.card_fin] using
        card_edgeFinset_le_extremalNumber (connected_free_sum conn hA.prop hB.prop)

theorem connected_density_alternative {q : ℕ} (G : SimpleGraph (Fin q))
    (conn : G.Connected) (edges : 2 ≤ G.edgeFinset.card) :
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop (𝓝 c)) ∨
      Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop atTop := by
  let u (n : ℕ) : ℝ := -(extremalNumber n G : ℝ)
  have hadd : Subadditive u := by
    intro m n
    have h : (extremalNumber m G : ℝ) + extremalNumber n G ≤ extremalNumber (m + n) G :=
      by exact_mod_cast connected_extremal_superadditive G conn edges m n
    dsimp [u]
    linarith
  by_cases hb : BddBelow (Set.range fun n : ℕ => u n / n)
  · left
    have h2 := hadd.lim_le_div hb (by decide : (2 : ℕ) ≠ 0)
    have hlo := extremal_linear_lower G edges (by decide : 0 < (2 : ℕ))
    have hlo' : (1 : ℝ) ≤ extremalNumber 2 G := by exact_mod_cast hlo
    norm_num [u] at h2
    refine ⟨-hadd.lim, by linarith, ?_⟩
    simpa only [u, neg_div, neg_neg] using (hadd.tendsto_lim hb).neg
  · right
    apply tendsto_atTop.mpr
    intro M
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := not_bddBelow_iff.mp hb (min 0 (-M) - 1)
    have ht : min 0 (-M) - 1 < 0 := by linarith [min_le_left (0 : ℝ) (-M)]
    have hne : k ≠ 0 := by
      rintro rfl
      simp only [Nat.cast_zero, div_zero] at hk
      linarith
    filter_upwards [hadd.eventually_div_lt_of_div_lt hne hk] with n hn
    simp only [u, neg_div] at hn
    linarith [min_le_right (0 : ℝ) (-M)]

theorem tree_copies_into_high_degree {V W : Type} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (tree : T.IsTree) (X : SimpleGraph W) [DecidableRel X.Adj]
    (w : W) (degree : ∀ x, Fintype.card V ≤ X.degree x) : T ⊑ X := by
  have aux (k : ℕ) : ∀ (U : Type) [Fintype U], Fintype.card U = k →
      ∀ (S : SimpleGraph U), S.IsTree → (∀ x, k ≤ X.degree x) → S ⊑ X := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro U _ hU S hS hdeg
      rcases subsingleton_or_nontrivial U with hs | hs
      · exact ⟨⟨⟨fun _ => w, fun h => (h.ne (Subsingleton.elim _ _)).elim⟩,
          fun _ _ _ => Subsingleton.elim _ _⟩⟩
      let _ := hs
      obtain ⟨leaf, hleaf⟩ := hS.exists_vert_degree_one_of_nontrivial
      obtain ⟨parent, hparent, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hleaf
      let V' := ({leaf}ᶜ : Set U)
      let S' := S.induce V'
      have htree' : S'.IsTree := ⟨hS.connected.induce_compl_singleton_of_degree_eq_one hleaf,
        hS.isAcyclic.induce V'⟩
      have hcard : Fintype.card V' < k := by
        rw [← hU]
        exact Fintype.card_lt_of_injective_of_notMem (f := fun x : V' => x.val)
          Subtype.val_injective (b := leaf) (by simp [V'])
      obtain ⟨f⟩ := ih (Fintype.card V') hcard V' rfl S' htree'
        (fun x => hcard.le.trans (hdeg x))
      let p : V' := ⟨parent, hparent.ne.symm⟩
      let used := (univ : Finset V').map f.toEmbedding
      have hfresh : ∃ y ∈ X.neighborFinset (f p), y ∉ used := by
        by_contra! h
        have hc := Finset.card_le_card (show X.neighborFinset (f p) ⊆ used from h)
        rw [card_neighborFinset_eq_degree] at hc
        have hused : used.card = Fintype.card V' := by simp [used]
        exact hcard.not_ge ((hdeg (f p)).trans (hc.trans_eq hused))
      obtain ⟨y, hy, hynew⟩ := hfresh
      have hy' := (mem_neighborFinset X (f p) y).mp hy
      let g (v : U) : W := if h : v = leaf then y else f ⟨v, h⟩
      have g_eq (v : U) (hv : v ≠ leaf) : g v = f ⟨v, hv⟩ := by
        simp [g, hv]
      have g_leaf : g leaf = y := by simp [g]
      have g_used (v : U) (hv : v ≠ leaf) : g v ∈ used := by
        rw [g_eq v hv]
        exact mem_map.mpr ⟨⟨v, hv⟩, mem_univ _, rfl⟩
      have hleaf_adj (v : U) (hv : S.Adj leaf v) : X.Adj (g leaf) (g v) := by
        have hv' : v = parent := hu v hv
        subst v
        rw [g_leaf, g_eq parent hparent.ne.symm]
        exact hy'.symm
      refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
      · intro v u adj
        rcases eq_or_ne v leaf with rfl | hv
        · exact hleaf_adj u adj
        rcases eq_or_ne u leaf with rfl | hu'
        · exact (hleaf_adj v adj.symm).symm
        rw [g_eq v hv, g_eq u hu']
        exact f.toHom.map_adj (show S'.Adj ⟨v, hv⟩ ⟨u, hu'⟩ from adj)
      · intro v u eq
        change g v = g u at eq
        rcases eq_or_ne v leaf with rfl | hv
        · by_contra hu'
          rw [g_leaf] at eq
          exact hynew (eq ▸ g_used u (fun h => hu' h.symm))
        rcases eq_or_ne u leaf with rfl | hu'
        · rw [g_leaf] at eq
          exact (hynew (eq ▸ g_used v hv)).elim
        rw [g_eq v hv, g_eq u hu'] at eq
        exact congrArg Subtype.val (f.injective eq)
  exact aux (Fintype.card V) V rfl T tree degree

theorem forest_extremal_upper {q : ℕ} (G : SimpleGraph (Fin q))
    (forest : G.IsAcyclic) (n : ℕ) : extremalNumber n G ≤ q * n := by
  induction n with
  | zero =>
    rw [← Fintype.card_fin 0, extremalNumber_le_iff (V := Fin 0)]
    intro X _ _
    have bound := X.card_edgeFinset_le_card_choose_two
    simpa using bound
  | succ n ih =>
    rw [← Fintype.card_fin (n+1), extremalNumber_le_iff (V := Fin (n+1))]
    intro X _ free
    by_cases h : ∃ x, X.degree x < q
    · obtain ⟨x, hx⟩ := h
      have hdel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber free x
      rw [card_edgeFinset_deleteIncidenceSet, Fintype.card_fin, Nat.add_sub_cancel] at hdel
      rw [Fintype.card_fin, Nat.mul_succ]
      omega
    · have hdeg (x) : q ≤ X.degree x := Nat.le_of_not_gt (fun hx => h ⟨x, hx⟩)
      have nonempty : Nonempty (Fin q) := by
        by_contra! hempty
        have hbot : G = ⊥ := by ext v; exact (hempty.false v).elim
        exact free (by rw [hbot, bot_isContained_iff_card_le]; simp)
      obtain ⟨T, hGT, _, ht⟩ := (connected_top (V := Fin q)).exists_isTree_le_of_le_of_isAcyclic
        (show G ≤ ⊤ from le_top) forest
      have hc := tree_copies_into_high_degree T ht X (0 : Fin (n+1)) (by simpa using hdeg)
      exact (free ((IsContained.of_le hGT).trans hc)).elim

theorem contained_iff_contained_support {q n : ℕ} (G : SimpleGraph (Fin q))
    (X : SimpleGraph (Fin n)) (hn : q ≤ n) :
    G ⊑ X ↔ (G.induce G.support) ⊑ X := by
  constructor
  · exact fun h => (Copy.induce G G.support).isContained.trans h
  · rintro ⟨f⟩
    let image : Set (Fin n) := Set.range f.toEmbedding
    have himage : Fintype.card image = Fintype.card G.support :=
      Fintype.card_range f.toEmbedding
    have hcard : Fintype.card (↑G.supportᶜ : Type) ≤ Fintype.card (↑imageᶜ : Type) := by
      simpa only [Fintype.card_compl_set, Fintype.card_fin, himage] using
        Nat.sub_le_sub_right hn (Fintype.card G.support)
    let e : (↑G.supportᶜ : Type) ↪ (↑imageᶜ : Type) :=
      (Function.Embedding.nonempty_of_card_le hcard).some
    let g (v : Fin q) : Fin n :=
      if h : v ∈ G.support then f ⟨v, h⟩ else (e ⟨v, h⟩).val
    have hg (v) (hv : v ∈ G.support) : g v = f ⟨v, hv⟩ := dif_pos hv
    have hn' (v) (hv : v ∉ G.support) : g v = (e ⟨v, hv⟩).val := dif_neg hv
    refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
    · intro v w h
      rw [hg v h.mem_support_left, hg w h.mem_support_right]
      exact f.toHom.map_adj (show (G.induce G.support).Adj
        ⟨v, h.mem_support_left⟩ ⟨w, h.mem_support_right⟩ from h)
    · intro v w heq
      change g v = g w at heq
      by_cases hv : v ∈ G.support <;> by_cases hw : w ∈ G.support
      · rw [hg v hv, hg w hw] at heq
        exact congrArg Subtype.val (f.injective heq)
      · rw [hg v hv, hn' w hw] at heq
        exact ((e ⟨w, hw⟩).property ⟨⟨v, hv⟩, heq⟩).elim
      · rw [hn' v hv, hg w hw] at heq
        exact ((e ⟨v, hv⟩).property ⟨⟨w, hw⟩, heq.symm⟩).elim
      · rw [hn' v hv, hn' w hw] at heq
        exact congrArg Subtype.val (e.injective (Subtype.ext heq))

theorem extremal_eq_on_support {q n : ℕ} (G : SimpleGraph (Fin q)) (hn : q ≤ n) :
    extremalNumber n G = extremalNumber n (G.induce G.support) := by
  have hfree (X : SimpleGraph (Fin n)) : G.Free X ↔ (G.induce G.support).Free X :=
    not_congr (contained_iff_contained_support G X hn)
  have hx : (univ : Finset (SimpleGraph (Fin n))).filter (fun X => G.Free X) =
      univ.filter (fun X => (G.induce G.support).Free X) := by
    ext X
    simpa only [mem_filter, mem_univ, true_and] using hfree X
  unfold extremalNumber
  rw [hx]

theorem remove_isolated_vertices {q : ℕ} (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) :
    ∃ (k : ℕ) (H : SimpleGraph (Fin k)), H.IsBipartite ∧
      H.edgeFinset.card = G.edgeFinset.card ∧ (∀ v, ¬ H.IsIsolated v) ∧
      ∀ n ≥ q, extremalNumber n G = extremalNumber n H := by
  let k := Fintype.card G.support
  let e : G.support ≃ Fin k := Fintype.equivFin _
  let H := (G.induce G.support).comap e.symm
  let iso : H ≃g G.induce G.support := ⟨e.symm, Iff.rfl⟩
  have hBip : H.IsBipartite :=
    bip.of_hom ((Embedding.induce G.support).toHom.comp iso.toHom)
  refine ⟨k, H, hBip, iso.card_edgeFinset_eq.trans card_edgeFinset_induce_support, ?_, ?_⟩
  · intro v
    rw [← mem_support_iff_not_isIsolated]
    let u := e.symm v
    obtain ⟨w, hw⟩ := (show ∃ w, G.Adj u.val w from u.property)
    let w' : G.support := ⟨w, hw.mem_support_right⟩
    change ∃ w, H.Adj v w
    refine ⟨e w', ?_⟩
    change (G.induce G.support).Adj (e.symm v) (e.symm (e w'))
    rw [e.symm_apply_apply]
    exact hw
  · intro n hn
    rw [extremal_eq_on_support G hn, extremalNumber_congr_right iso]
theorem card_edges_eraseVertices_le_degree_sum {W : Type*} [Fintype W]
    (X : SimpleGraph W) (T : Finset W) :
    X.edgeFinset.card ≤ ((SimpleGraph.mk (fun x y => X.Adj x y ∧ x ∉ (↑T : Set W) ∧ y ∉ (↑T : Set W)) ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩ ⟨fun _ h => X.irrefl h.1⟩)).edgeFinset.card +
      ∑ v ∈ T, X.degree v := by
  induction T using Finset.induction_on with
  | empty =>
    have heq : (SimpleGraph.mk (fun x y => X.Adj x y ∧ x ∉ (↑(∅ : Finset W) : Set W) ∧ y ∉ (↑(∅ : Finset W) : Set W)) ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩ ⟨fun _ h => X.irrefl h.1⟩) = X := by
      ext a b
      simp
    rw [Finset.sum_empty, Nat.add_zero]
    apply Finset.card_le_card
    intro e he
    induction e using Sym2.ind
    simpa using he
  | @insert v T hv ih =>
    let Y := (SimpleGraph.mk (fun x y => X.Adj x y ∧ x ∉ (↑T : Set W) ∧ y ∉ (↑T : Set W)) ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩ ⟨fun _ h => X.irrefl h.1⟩)
    have heq : (SimpleGraph.mk (fun x y => X.Adj x y ∧ x ∉ (↑(insert v T) : Set W) ∧ y ∉ (↑(insert v T) : Set W)) ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩ ⟨fun _ h => X.irrefl h.1⟩) = Y.deleteIncidenceSet v := by
      ext a b
      simp only [Y, coe_insert, Set.mem_insert_iff, not_or, deleteIncidenceSet_adj]
      tauto
    have hdel : (Y.deleteIncidenceSet v).edgeFinset.card = Y.edgeFinset.card - Y.degree v := by
      convert! card_edgeFinset_deleteIncidenceSet Y v
    have hd : Y.degree v ≤ X.degree v := Y.degree_le_of_le (fun _ _ h => h.1)
    have hi : X.edgeFinset.card ≤ Y.edgeFinset.card + ∑ w ∈ T, X.degree w := ih
    simp only [heq, Finset.sum_insert hv]
    have hf : X.edgeFinset.card ≤ (Y.deleteIncidenceSet v).edgeFinset.card +
        (X.degree v + ∑ w ∈ T, X.degree w) := by
      rw [hdel]
      omega
    convert! hf

theorem card_edgeFinset_eraseVertices {W : Type*} [Fintype W]
    (X : SimpleGraph W) [DecidableRel X.Adj] (S : Finset W) :
    X.edgeFinset.card ≤ ((SimpleGraph.mk (fun x y => X.Adj x y ∧ x ∉ (↑S : Set W) ∧ y ∉ (↑S : Set W)) ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩ ⟨fun _ h => X.irrefl h.1⟩)).edgeFinset.card +
      S.card * Fintype.card W := by
  have hweight : (∑ v ∈ S, X.degree v) ≤ S.card * Fintype.card W := by
    calc
      _ ≤ ∑ _v ∈ S, Fintype.card W :=
        Finset.sum_le_sum (fun v _ => (X.degree_lt_card_verts v).le)
      _ = _ := by simp
  have h : X.edgeFinset.card ≤ ((SimpleGraph.mk (fun x y => X.Adj x y ∧ x ∉ (↑S : Set W) ∧ y ∉ (↑S : Set W)) ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩ ⟨fun _ h => X.irrefl h.1⟩)).edgeFinset.card +
      ∑ v ∈ S, X.degree v := by
    convert! card_edges_eraseVertices_le_degree_sum X S
  exact h.trans (Nat.add_le_add_left hweight _)

theorem contained_of_component_bounds {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (X : SimpleGraph W) [DecidableRel X.Adj]
    (active : ∀ v, ∃ w, H.Adj v w)
    (rich : ∀ C : H.ConnectedComponent, extremalNumber (Fintype.card W) C.toSimpleGraph +
        Fintype.card V * Fintype.card W < X.edgeFinset.card) : H ⊑ X := by
  let p := H.connectedComponentMk
  let P (s : Finset H.ConnectedComponent) : Set V := {v | p v ∈ s}
  have partialCopy (s : Finset H.ConnectedComponent) : (H.induce (P s)) ⊑ X := by
    induction s using Finset.induction_on with
    | empty =>
      have empty (v : P ∅) : False := Finset.notMem_empty _ v.property
      exact ⟨⟨⟨fun v => (empty v).elim, fun {v} _ _ => (empty v).elim⟩,
        fun v _ _ => (empty v).elim⟩⟩
    | @insert C s hC ih =>
      obtain ⟨f⟩ := ih
      let used := (univ : Finset (P s)).map f.toEmbedding
      have hused : used.card ≤ Fintype.card V := by
        simpa [used] using Fintype.card_le_of_injective (fun v : P s => v.val)
          Subtype.val_injective
      have hn := card_edgeFinset_eraseVertices X used
      have hm := Nat.mul_le_mul_right (Fintype.card W) hused
      obtain ⟨g⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset
        (G := (SimpleGraph.mk (fun x y => X.Adj x y ∧ x ∉ (↑used : Set W) ∧ y ∉ (↑used : Set W)) ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩ ⟨fun _ h => X.irrefl h.1⟩)) (H := C.toSimpleGraph) (by
          have h := rich C
          omega)
      have g_new (v : C.supp) : g v ∉ used := by
        obtain ⟨w, hw⟩ := active v.val
        have hcw := C.mem_supp_of_adj_mem_supp v.property hw
        have h := g.toHom.map_adj (show C.toSimpleGraph.Adj v ⟨w, hcw⟩ from hw)
        exact h.2.1
      have g_adj {v w : C.supp} (h : H.Adj v.val w.val) : X.Adj (g v) (g w) :=
        (g.toHom.map_adj (show C.toSimpleGraph.Adj v w from h)).1
      have memC (v : P (insert C s)) (hv : p v.val ∉ s) : v.val ∈ C.supp := by
        exact (mem_insert.mp v.property).resolve_right hv
      let k (v : P (insert C s)) : W :=
        if hv : p v.val ∈ s then f ⟨v.val, hv⟩ else g ⟨v.val, memC v hv⟩
      have k_old (v : P (insert C s)) (hv : p v.val ∈ s) : k v = f ⟨v.val, hv⟩ :=
        dif_pos hv
      have k_new (v : P (insert C s)) (hv : p v.val ∉ s) :
          k v = g ⟨v.val, memC v hv⟩ := dif_neg hv
      have k_used (v : P (insert C s)) (hv : p v.val ∈ s) : k v ∈ used := by
        rw [k_old v hv]
        exact mem_map.mpr ⟨⟨v.val, hv⟩, mem_univ _, rfl⟩
      refine ⟨⟨⟨k, ?_⟩, ?_⟩⟩
      · intro v w h
        change H.Adj v.val w.val at h
        have hp : p v.val = p w.val := ConnectedComponent.connectedComponentMk_eq_of_adj h
        by_cases hv : p v.val ∈ s
        · have hw : p w.val ∈ s := hp ▸ hv
          rw [k_old v hv, k_old w hw]
          exact f.toHom.map_adj (show (H.induce (P s)).Adj ⟨v.val, hv⟩
            ⟨w.val, hw⟩ from h)
        · have hw : p w.val ∉ s := hp ▸ hv
          rw [k_new v hv, k_new w hw]
          exact g_adj h
      · intro v w eq
        change k v = k w at eq
        by_cases hv : p v.val ∈ s <;> by_cases hw : p w.val ∈ s
        · rw [k_old v hv, k_old w hw] at eq
          exact Subtype.ext (congrArg (fun x : P s => x.val) (f.injective eq))
        · have hm := k_used v hv
          rw [eq, k_new w hw] at hm
          exact (g_new _ hm).elim
        · have hm := k_used w hw
          rw [← eq, k_new v hv] at hm
          exact (g_new _ hm).elim
        · rw [k_new v hv, k_new w hw] at eq
          exact Subtype.ext (congrArg (fun x : C.supp => x.val) (g.injective eq))
  let : Fintype H.ConnectedComponent :=
    Fintype.ofSurjective p (fun C => ⟨C.out, C.out_eq⟩)
  obtain ⟨f⟩ := partialCopy univ
  let incl (v : V) : P univ := ⟨v, mem_univ _⟩
  exact ⟨⟨⟨fun v => f (incl v), fun h => f.toHom.map_adj
    (show (H.induce (P univ)).Adj (incl _) (incl _) from h)⟩,
    fun _ _ h => congrArg Subtype.val (f.injective h)⟩⟩

theorem extremal_le_component_bound {V : Type*} [Fintype V]
    (H : SimpleGraph V) (active : ∀ v, ∃ w, H.Adj v w) (n M : ℕ)
    (bound : ∀ C : H.ConnectedComponent, extremalNumber n C.toSimpleGraph ≤ M) :
    extremalNumber n H ≤ M + Fintype.card V * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff (V := Fin n)]
  intro X _ hfree
  by_contra! h
  apply hfree (contained_of_component_bounds H X active ?_)
  intro C
  rw [Fintype.card_fin]
  rw [Fintype.card_fin] at h
  exact lt_of_le_of_lt (Nat.add_le_add_right (bound C) _) h

/-- A trail using the new edge splits at that edge into two walks in the old graph. -/
theorem trail_split_at_added_edge {V : Type*} (X : SimpleGraph V) {u v : V} :
    ∀ {a b : V} (p : (X ⊔ edge u v).Walk a b), p.IsTrail → s(u, v) ∈ p.edges →
      ∃ (x y : V) (q : X.Walk a x) (r : X.Walk y b),
        s(x, y) = s(u, v) ∧ q.length + r.length < p.length := by
  intro a b p
  induction p with
  | nil => simp
  | @cons a w b hadj p ih =>
    intro ht hm
    have hn := (Walk.isTrail_cons _ _).mp ht
    simp only [Walk.edges_cons, List.mem_cons] at hm
    rcases hm with he | he
    · have hsub : ∀ e ∈ p.edges, e ∈ X.edgeSet := by
        intro e hm
        have hmem := p.edges_subset_edgeSet hm
        rw [edgeSet_sup, Set.mem_union] at hmem
        rcases hmem with h | h
        · exact h
        · have he' := edgeSet_edge_subset h
          have heq : e = s(a, w) := (Set.mem_singleton_iff.mp he').trans he
          exact (hn.2 (heq ▸ hm)).elim
      refine ⟨a, w, Walk.nil, p.transfer X hsub, he.symm, ?_⟩
      simp
    · obtain ⟨x, y, q, r, hxy, hlen⟩ := ih hn.1 he
      have old : X.Adj a w := by
        rcases (show X.Adj a w ∨ (edge u v).Adj a w from hadj) with old | new
        · exact old
        · exact (hn.2 ((adj_edge (s := u) (t := v)).mp new |>.1 ▸ he)).elim
      exact ⟨x, y, Walk.cons old q, r, hxy, by simp only [Walk.length_cons]; omega⟩

theorem short_cycles_sup_edge {V : Type*} (X : SimpleGraph V) {k : ℕ}
    (hcycles : ∀ ⦃w⦄ (p : X.Walk w w), p.IsCycle → k < p.length)
    {u v : V} (hfar : ∀ p : X.Walk u v, k ≤ p.length) :
    ∀ ⦃w⦄ (p : (X ⊔ edge u v).Walk w w), p.IsCycle → k < p.length := by
  intro w p hp
  by_cases he : s(u, v) ∈ p.edges
  · obtain ⟨a, b, q, r, hab, hlt⟩ := trail_split_at_added_edge X p hp.isTrail he
    rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h := hfar ((r.append q).reverse)
      rw [Walk.length_reverse, Walk.length_append, Nat.add_comm] at h
      exact h.trans_lt hlt
    · have h := hfar (r.append q)
      rw [Walk.length_append, Nat.add_comm] at h
      exact h.trans_lt hlt
  · have hsub : ∀ e ∈ p.edges, e ∈ X.edgeSet := by
      intro e hm
      have he' := p.edges_subset_edgeSet hm
      rw [edgeSet_sup, Set.mem_union] at he'
      rcases he' with he' | he'
      · exact he'
      · exact (he (Set.mem_singleton_iff.mp (edgeSet_edge_subset he') ▸ hm)).elim
    simpa only [Walk.length_transfer] using hcycles (p.transfer X hsub) (hp.transfer hsub)


theorem degree_sup_edge_le {V : Type*} [Fintype V] (X : SimpleGraph V)
    {u v : V} (D : ℕ) (hdeg : ∀ w, X.degree w ≤ D)
    (hu : X.degree u < D) (hv : X.degree v < D) :
    ∀ w, (X ⊔ edge u v).degree w ≤ D := by
  intro w
  by_cases hw : w = u ∨ w = v
  · let t := if w = u then v else u
    have hs : (X ⊔ edge u v).neighborFinset w ⊆ insert t (X.neighborFinset w) := by
      intro z hz
      rw [mem_neighborFinset, sup_adj] at hz
      rcases hz with hz | hz
      · exact mem_insert_of_mem ((mem_neighborFinset _ _ _).mpr hz)
      · have h := (edge_adj u v w z).mp hz
        rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [t]
        · simp [t, hz.ne]
    have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hc
    rcases hw with rfl | rfl <;> omega
  · have hs : (X ⊔ edge u v).neighborFinset w ⊆ X.neighborFinset w := by
      intro z hz
      rw [mem_neighborFinset, sup_adj] at hz
      exact (mem_neighborFinset _ _ _).mpr (hz.resolve_right fun h =>
        hw (((edge_adj u v w z).mp h).1.imp And.left And.left))
    have hc := Finset.card_le_card hs
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hc
    exact hc.trans (hdeg w)

theorem exists_walkBall {V : Type*} [Fintype V] (X : SimpleGraph V)
    {D : ℕ} (hdeg : ∀ w, X.degree w ≤ D) : ∀ (j : ℕ) (u : V), ∃ B : Finset V,
      (∀ {v : V} (p : X.Walk u v), p.length ≤ j → v ∈ B) ∧ B.card ≤ (D + 1) ^ j := by
  intro j
  induction j with
  | zero =>
    intro u
    refine ⟨{u}, ?_, by simp⟩
    intro v p hp
    cases p with
    | nil => simp
    | cons => simp at hp
  | succ j ih =>
    intro u
    choose B hBmem hBcard using ih
    refine ⟨(insert u (X.neighborFinset u)).biUnion B, ?_, ?_⟩
    · intro v p hp
      cases p with
      | nil =>
        exact Finset.mem_biUnion.mpr ⟨u, mem_insert_self _ _, hBmem u Walk.nil (by simp)⟩
      | @cons _ w _ adj p =>
        exact Finset.mem_biUnion.mpr ⟨w, mem_insert_of_mem
          ((mem_neighborFinset _ _ _).mpr adj), hBmem w p (by simpa using hp)⟩
    · calc
        _ ≤ ∑ w ∈ insert u (X.neighborFinset u), (B w).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ insert u (X.neighborFinset u), (D + 1) ^ j :=
          Finset.sum_le_sum fun w _ => hBcard w
        _ = (insert u (X.neighborFinset u)).card * (D + 1) ^ j := by simp
        _ ≤ (D + 1) ^ (j + 1) := by
          rw [pow_succ']
          apply Nat.mul_le_mul_right
          rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
          exact Nat.succ_le_succ (hdeg u)

theorem cycle_length_le_vertices {V : Type*} [Fintype V] {X : SimpleGraph V}
    {v : V} {p : X.Walk v v} (hp : p.IsCycle) : p.length ≤ Fintype.card V := by
  have ht := hp.isPath_tail.length_lt
  rw [Walk.length_tail] at ht
  omega

theorem cyclic_extremal_degree_bound {V : Type*} [Fintype V] {H : SimpleGraph V}
    (cyclic : ¬ H.IsAcyclic) (n D : ℕ) :
    D * (n - (D + 1) ^ (Fintype.card V - 1)) ≤ 2 * extremalNumber n H := by
  let k := Fintype.card V
  let Good (X : SimpleGraph (Fin n)) : Prop :=
    (∀ w, X.degree w ≤ D) ∧ ∀ ⦃w⦄ (p : X.Walk w w), p.IsCycle → k < p.length
  have hbot : Good ⊥ := ⟨by simp, fun _ _ hc => (isAcyclic_bot _ hc).elim⟩
  obtain ⟨X, inst, hX⟩ := (exists_isExtremal_iff_exists Good).mpr ⟨⊥, hbot⟩
  obtain ⟨a, p, hp⟩ : ∃ (a : V) (p : H.Walk a a), p.IsCycle := by
    by_contra! h
    exact cyclic h
  have hlen := cycle_length_le_vertices hp
  have hk : 1 < k := by have := hp.three_le_length; omega
  have free : H.Free X := by
    rintro ⟨f⟩
    have h := hX.prop.2 (p.map f.toHom) (hp.map f.injective)
    rw [Walk.length_map] at h
    exact (not_lt_of_ge hlen) h
  have nearby (u v : Fin n) (hu : X.degree u < D) (hv : X.degree v < D) :
      ∃ q : X.Walk u v, q.length < k := by
    by_contra! hfar
    have hne : u ≠ v := by
      rintro rfl
      have hh := hfar Walk.nil
      simp at hh
      omega
    have hnadj : ¬ X.Adj u v := by
      intro h
      have hh := hfar (Walk.cons h Walk.nil)
      simp at hh
      omega
    have hy : Good (X ⊔ edge u v) := by
      refine ⟨?_, short_cycles_sup_edge X hX.prop.2 hfar⟩
      intro w
      convert! degree_sup_edge_le X (u := u) (v := v) D hX.prop.1 (by convert! hu) (by convert! hv) w
    exact (lt_sup_edge X u v hne hnadj).ne ((hX.le_iff_eq hy).mp le_sup_left)
  let low := univ.filter fun u : Fin n => X.degree u < D
  have hlow : low.card ≤ (D + 1) ^ (k - 1) := by
    by_cases h : low.Nonempty
    · obtain ⟨u, hu⟩ := h
      obtain ⟨B, hBmem, hBcard⟩ := exists_walkBall X hX.prop.1 (k - 1) u
      have hsub : low ⊆ B := by
        intro v hv
        obtain ⟨q, hq⟩ := nearby u v (mem_filter.mp hu).2 (mem_filter.mp hv).2
        exact hBmem q (by omega)
      exact (Finset.card_le_card hsub).trans hBcard
    · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty]
      exact Nat.zero_le _
  let high := univ \ low
  have hhigh : high.card = n - low.card := by simp [high, Finset.card_sdiff_of_subset]
  have hsum : D * (n - (D + 1) ^ (k - 1)) ≤ ∑ v, X.degree v := by
    calc
      _ ≤ D * high.card := by rw [hhigh]; exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hlow _)
      _ = ∑ _v ∈ high, D := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ high, X.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact Nat.le_of_not_gt fun h =>
          (Finset.mem_sdiff.mp hv).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
      _ ≤ ∑ v, X.degree v := Finset.sum_le_sum_of_subset (subset_univ _)
  rw [sum_degrees_eq_twice_card_edges] at hsum
  exact hsum.trans (Nat.mul_le_mul_left 2 (by simpa using card_edgeFinset_le_extremalNumber free))

theorem cyclic_density_diverges {V : Type*} [Fintype V] {H : SimpleGraph V}
    (cyclic : ¬ H.IsAcyclic) :
    Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  obtain ⟨D, hD⟩ := exists_nat_ge (4 * M)
  let K := (D + 1) ^ (Fintype.card V - 1)
  filter_upwards [eventually_ge_atTop (max 1 (2 * K))] with n hn
  have hlarge : 2 * K ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr ((le_max_left _ _).trans hn)
  have hb := cyclic_extremal_degree_bound cyclic n D
  change D * (n - K) ≤ _ at hb
  have hb' : D * n ≤ 4 * extremalNumber n H := calc
    _ ≤ D * (2 * (n - K)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (D * (n - K)) := by ring
    _ ≤ _ := by omega
  have hbR : (D : ℝ) * n ≤ 4 * (extremalNumber n H : ℝ) := by exact_mod_cast hb'
  apply (le_div_iff₀ hnpos).mpr
  nlinarith only [hbR, mul_le_mul_of_nonneg_right hD hnpos.le]

theorem extremal_limit_at_higher_power {V : Type*} {H : SimpleGraph V} {a b c : ℝ}
    (hab : a < b) (fit : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c)) : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (b : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop (𝓝 0) := by
    rw [← neg_sub]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  have hmul := fit.mul hpow
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Real.rpow_sub hnpos, div_mul_div_comm, mul_comm, mul_div_mul_left _ _ (by positivity)]

theorem linear_term_at_higher_power {a : ℝ} (ha : 1 < a) (K : ℝ) :
    Tendsto (fun n : ℕ => K * n / (n : ℝ) ^ a) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp
    (tendsto_natCast_atTop_atTop : Tendsto ((↑) : ℕ → ℝ) atTop atTop)
  have hmul := hpow.const_mul K
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  change K * (n : ℝ) ^ (-(a - 1)) = _
  rw [neg_sub, Real.rpow_sub hnpos, Real.rpow_one, mul_div_assoc]

theorem forest_limit_at_higher_power {V : Type*} [Fintype V] {H : SimpleGraph V}
    (forest : H.IsAcyclic) {a : ℝ} (ha : 1 < a) : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 0) := by
  let e := Fintype.equivFin V
  let J := H.comap e.symm
  let iso : J ≃g H := ⟨e.symm, Iff.rfl⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (linear_term_at_higher_power ha (Fintype.card V : ℝ))
  · intro n
    positivity
  · intro n
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← extremalNumber_congr_right iso]
    have h := forest_extremal_upper J (iso.isAcyclic_iff.mpr forest) n
    push_cast
    exact_mod_cast h

theorem exists_cyclic_component {V : Type*} {H : SimpleGraph V} (h : ¬ H.IsAcyclic) :
    ∃ C : H.ConnectedComponent, ¬ C.toSimpleGraph.IsAcyclic := by
  classical
  obtain ⟨u, p, hp⟩ : ∃ (u : V) (p : H.Walk u u), p.IsCycle := by
    by_contra! hn
    exact h hn
  let C := H.connectedComponentMk u
  have hsub : ∀ v ∈ p.support, v ∈ C.supp := by
    intro v hv
    exact ConnectedComponent.sound (p.takeUntil v hv).reachable.symm
  let q := p.induce C.supp hsub
  have hq : q.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce C.supp).toHom)
    simpa [q] using hp
  exact ⟨C, fun forest => forest q hq⟩

theorem limit_of_component_limits {V : Type*} [Fintype V] (H : SimpleGraph V)
    (active : ∀ v, ∃ w, H.Adj v w) (cyclic : ¬ H.IsAcyclic)
    (components : ∀ C : H.ConnectedComponent, ¬ C.toSimpleGraph.IsAcyclic →
      ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c)) :
    ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c) := by
  obtain ⟨C₀, hC₀⟩ := exists_cyclic_component cyclic
  let : Fintype H.ConnectedComponent :=
    Fintype.ofSurjective H.connectedComponentMk (fun C => ⟨C.out, C.out_eq⟩)
  let I : Finset H.ConnectedComponent := univ
  have hI : I.Nonempty := ⟨C₀, mem_univ _⟩
  have choices (C : H.ConnectedComponent) : ∃ a c : ℝ,
      (a = 1 ∧ C.toSimpleGraph.IsAcyclic) ∨
        (1 < a ∧ 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c)) := by
    by_cases forest : C.toSimpleGraph.IsAcyclic
    · exact ⟨1, 0, Or.inl ⟨rfl, forest⟩⟩
    · obtain ⟨a, c, hc⟩ := components C forest
      exact ⟨a, c, Or.inr hc⟩
  choose a c h using choices
  let A := I.sup' hI a
  have ha (C : H.ConnectedComponent) : a C ≤ A := Finset.le_sup' a (mem_univ C)
  have hA : 1 < A := by
    rcases h C₀ with h₀ | h₀
    · exact (hC₀ h₀.2).elim
    · exact h₀.1.trans_le (ha _)
  let d (C : H.ConnectedComponent) : ℝ := if a C = A then c C else 0
  have limits (C : H.ConnectedComponent) : Tendsto (fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ) / (n : ℝ) ^ (A : ℝ)) atTop (𝓝 (d C)) := by
    rcases h C with ⟨hc, forest⟩ | ⟨_, _, fit⟩
    · simpa [d, hc, hA.ne] using (forest_limit_at_higher_power forest hA)
    · rcases (ha C).lt_or_eq with hlt | heq
      · simpa [d, hlt.ne] using (extremal_limit_at_higher_power hlt fit)
      · simpa [d, heq] using fit
  let best := I.sup' hI d
  have hbest : 0 < best := by
    obtain ⟨C, hC, heq⟩ := I.exists_mem_eq_sup' hI a
    rcases h C with ⟨hc, _⟩ | ⟨_, hpos, _⟩
    · exact (hA.ne' (heq.trans hc)).elim
    · have hd : d C = c C := if_pos heq.symm
      exact (hd ▸ hpos).trans_le (Finset.le_sup' d hC)
  let μ (n : ℕ) := I.sup' hI (fun C => extremalNumber n C.toSimpleGraph)
  have hm (n : ℕ) : μ n ≤ extremalNumber n H := by
    apply Finset.sup'_le
    intro C _
    exact (Copy.induce H C.supp).isContained.extremalNumber_le
  have hu (n : ℕ) : extremalNumber n H ≤ μ n + Fintype.card V * n :=
    extremal_le_component_bound H active n (μ n) (fun C => Finset.le_sup' (fun C => extremalNumber n C.toSimpleGraph) (mem_univ C))
  have hsup := Tendsto.finset_sup'_nhds_apply hI (fun C _ => limits C)
  have hμ : Tendsto (fun n : ℕ => (μ n : ℝ) / (n : ℝ) ^ A) atTop (𝓝 best) := by
    apply hsup.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hpow : 0 < (n : ℝ) ^ A := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
    symm
    apply Finset.apply_sup'_eq_sup'_comp hI (fun m : ℕ => (m : ℝ) / (n : ℝ) ^ A)
    intro x y
    exact Monotone.map_sup (fun _ _ hxy => div_le_div_of_nonneg_right (by exact_mod_cast hxy)
      hpow.le) x y
  refine ⟨A, best, hA, hbest, ?_⟩
  have hsum := hμ.add (linear_term_at_higher_power hA (Fintype.card V : ℝ))
  rw [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hμ hsum
  · intro n
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hm n)) (by positivity)
  · intro n
    dsimp
    rw [← add_div]
    have hab : (extremalNumber n H : ℝ) ≤ (μ n : ℝ) + (Fintype.card V : ℝ) * n := by
      exact_mod_cast hu n
    exact div_le_div_of_nonneg_right hab (by positivity)

/-- The true labels mark vertices to place. The left labels fix boundary vertices. -/
theorem card_edgeFinset_le_extremal_of_card_le {V W : Type*} [Fintype W]
    {H : SimpleGraph V} {X : SimpleGraph W} (active : ∀ v, ∃ w, H.Adj v w)
    (free : H.Free X) {N : ℕ} (hN : Fintype.card W ≤ N) :
    X.edgeFinset.card ≤ extremalNumber N H := by
  let e : W ↪ Fin N := (Function.Embedding.nonempty_of_card_le (by simpa using hN)).some
  have hfree : H.Free (X.map e) := by
    rintro ⟨f⟩
    have hrange (v : V) : ∃ w, e w = f v := by
      obtain ⟨u, hu⟩ := active v
      obtain ⟨a, _, _, ha, _⟩ := (map_adj e X _ _).mp (f.toHom.map_adj hu)
      exact ⟨a, ha⟩
    choose g hg using hrange
    apply free
    refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
    · intro v w hw
      obtain ⟨a, b, hab, ha, hb⟩ := (map_adj e X _ _).mp (f.toHom.map_adj hw)
      exact e.injective (ha.trans (hg v).symm) ▸ e.injective (hb.trans (hg w).symm) ▸ hab
    · intro v w hw
      exact f.injective ((hg v).symm.trans ((congrArg e hw).trans (hg w)))
  have h := card_edgeFinset_le_extremalNumber hfree
  rw [Fintype.card_fin] at h
  have he : (X.map e).edgeFinset.card = X.edgeFinset.card := by
    convert! card_edgeFinset_map e X
  exact he ▸ h

theorem active_of_connected_cyclic {V : Type*} {H : SimpleGraph V}
    (conn : H.Connected) (cyclic : ¬ H.IsAcyclic) (v : V) : ∃ w, H.Adj v w := by
  rcases subsingleton_or_nontrivial V with hs | hs
  · exact (cyclic IsAcyclic.of_subsingleton).elim
  · exact conn.preconnected.exists_adj_of_nontrivial v

theorem cyclic_induce_compl_leaf {V : Type*} [Fintype V] {H : SimpleGraph V}
    (cyclic : ¬ H.IsAcyclic) {v : V} (leaf : H.degree v = 1) :
    ¬ (H.induce ({v}ᶜ : Set V)).IsAcyclic := by
  obtain ⟨u, p, hp⟩ : ∃ (u : V) (p : H.Walk u u), p.IsCycle := by
    by_contra! hn
    exact cyclic hn
  obtain ⟨w, hvw, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp leaf
  have hno : v ∉ p.support := by
    intro hv
    have hr := hp.rotate hv
    generalize p.rotate v hv = r at hr
    cases r with
    | nil => exact hr.not_nil (by simp)
    | @cons _ x _ adj t =>
      have hx := huniq x adj
      subst x
      have hn : ¬ t.Nil := Walk.not_nil_of_ne hvw.ne.symm
      have hl := t.mk_penultimate_end_mem_edges hn
      have he : t.penultimate = w := huniq _ (t.adj_of_mem_edges hl).symm
      rw [he, Sym2.eq_swap] at hl
      exact ((Walk.isTrail_cons adj t).mp hr.isTrail).2 hl
  have hsub : ∀ w ∈ p.support, w ∈ ({v}ᶜ : Set V) := by
    intro w hw
    exact fun e => hno ((Set.mem_singleton_iff.mp e) ▸ hw)
  let r := p.induce ({v}ᶜ : Set V) hsub
  have hr : r.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce _).toHom)
    simpa [r] using hp
  exact fun forest => forest r hr

theorem extend_copy_at_leaf {V W : Type*} [Fintype V] [Fintype W]
    {H : SimpleGraph V} {X : SimpleGraph W} {v : V} (leaf : H.degree v = 1)
    (hdeg : ∀ w, Fintype.card V ≤ X.degree w)
    (copy : (H.induce ({v}ᶜ : Set V)) ⊑ X) : H ⊑ X := by
  obtain ⟨p, hparent, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp leaf
  obtain ⟨f⟩ := copy
  let U : Set V := {v}ᶜ
  let parent : U := ⟨p, hparent.ne.symm⟩
  let used := univ.map f.toEmbedding
  have hsize : used.card < Fintype.card V := by
    simp only [used, Finset.card_map, Finset.card_univ]
    exact Fintype.card_lt_of_injective_of_notMem (f := fun x : U => x.val)
      Subtype.val_injective (b := v) (by simp [U])
  have hex : ∃ w ∈ X.neighborFinset (f parent), w ∉ used := by
    by_contra! h
    have hcard := Finset.card_le_card (show X.neighborFinset (f parent) ⊆ used from h)
    rw [card_neighborFinset_eq_degree] at hcard
    exact hsize.not_ge ((hdeg _).trans hcard)
  obtain ⟨y, hy, hynew⟩ := hex
  let g (u : V) : W := if hu : u = v then y else f ⟨u, hu⟩
  have hv : g v = y := by simp [g]
  have hg {u : V} (hu : u ≠ v) : g u = f ⟨u, hu⟩ := dif_neg hu
  have hadj {u : V} (h : H.Adj v u) : X.Adj (g v) (g u) := by
    have hu := huniq u h
    subst u
    rw [hv, hg hparent.ne.symm]
    exact ((mem_neighborFinset X _ _).mp hy).symm
  have hmem {u : V} (hu : u ≠ v) : g u ∈ used := by
    rw [hg hu]
    exact mem_map.mpr ⟨⟨u, hu⟩, mem_univ _, rfl⟩
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro u w h
    rcases eq_or_ne u v with rfl | hu
    · exact hadj h
    rcases eq_or_ne w v with rfl | hw
    · exact (hadj h.symm).symm
    rw [hg hu, hg hw]
    exact f.toHom.map_adj (show (H.induce U).Adj ⟨u, hu⟩ ⟨w, hw⟩ from h)
  · intro u w h
    change g u = g w at h
    by_cases hu : u = v
    · subst u
      by_cases hw : w = v
      · exact hw.symm
      · exfalso
        apply hynew
        rw [← hv, h]
        exact hmem hw
    · by_cases hw : w = v
      · subst w
        exfalso
        apply hynew
        rw [← hv, ← h]
        exact hmem hu
      · rw [hg hu, hg hw] at h
        exact congrArg Subtype.val (f.injective h)

theorem extremalNumber_monotone_active {V : Type*} {H : SimpleGraph V}
    (active : ∀ v, ∃ w, H.Adj v w) : Monotone (extremalNumber · H) := by
  intro m n hmn
  rw [← Fintype.card_fin m, extremalNumber_le_iff (V := Fin m)]
  intro X _ free
  have h := card_edgeFinset_le_extremal_of_card_le active free (Fintype.card_fin m ▸ hmn)
  convert! h

theorem extremal_le_after_leaf_pruned {V : Type*} [Fintype V] {H : SimpleGraph V}
    {v : V} (leaf : H.degree v = 1)
    (active : ∀ w, ∃ u, (H.induce ({v}ᶜ : Set V)).Adj w u) (n : ℕ) :
    extremalNumber n H ≤ extremalNumber n (H.induce ({v}ᶜ : Set V)) + Fintype.card V * n := by
  let J := H.induce ({v}ᶜ : Set V)
  induction n with
  | zero =>
    rw [← Fintype.card_fin 0, extremalNumber_le_iff (V := Fin 0)]
    intro X _ _
    have h := X.card_edgeFinset_le_card_choose_two
    simpa using h.trans (by simp : (Fintype.card (Fin 0)).choose 2 ≤ _)
  | succ n ih =>
    rw [← Fintype.card_fin (n + 1), extremalNumber_le_iff (V := Fin (n + 1))]
    intro X _ hfree
    by_cases low : ∃ w, X.degree w < Fintype.card V
    · obtain ⟨x, hx⟩ := low
      have hdel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree x
      rw [card_edgeFinset_deleteIncidenceSet, Fintype.card_fin, Nat.add_sub_cancel] at hdel
      rw [Fintype.card_fin, Nat.mul_succ]
      have hm := extremalNumber_monotone_active active (Nat.le_succ n)
      change extremalNumber n (H.induce ({v}ᶜ : Set V)) ≤
        extremalNumber (n + 1) (H.induce ({v}ᶜ : Set V)) at hm
      omega
    · have hdeg (w : Fin (n + 1)) : Fintype.card V ≤ X.degree w :=
        Nat.le_of_not_gt fun h => low ⟨w, h⟩
      by_contra! h
      have h' : extremalNumber (Fintype.card (Fin (n + 1))) J < X.edgeFinset.card :=
        lt_of_le_of_lt (Nat.le_add_right _ _) h
      have hc := IsContained.of_extremalNumber_lt_card_edgeFinset h'
      have hc' : H ⊑ X := extend_copy_at_leaf leaf (fun w => by convert! hdeg w) hc
      exact hfree hc'

theorem extremal_limit_of_leaf_pruned {V : Type*} [Fintype V] {H : SimpleGraph V}
    {v : V} (leaf : H.degree v = 1)
    (active : ∀ w, ∃ u, (H.induce ({v}ᶜ : Set V)).Adj w u) {a c : ℝ}
    (ha : 1 < a) (fit : Tendsto (fun n : ℕ => (extremalNumber n (H.induce ({v}ᶜ : Set V)) : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c) := by
  have hu := fit.add (linear_term_at_higher_power ha (Fintype.card V : ℝ))
  rw [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le fit hu
  · intro n
    have h : extremalNumber n (H.induce ({v}ᶜ : Set V)) ≤ extremalNumber n H :=
      (Copy.induce H _).isContained.extremalNumber_le
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr h) (by positivity)
  · intro n
    dsimp
    rw [← add_div]
    have h := extremal_le_after_leaf_pruned leaf active n
    have hR : (extremalNumber n H : ℝ) ≤
        (extremalNumber n (H.induce ({v}ᶜ : Set V)) : ℝ) + (Fintype.card V : ℝ) * n := by
      exact_mod_cast h
    exact div_le_div_of_nonneg_right hR (by positivity)

theorem connected_cyclic_limit_from_min_degree
    (core : ∀ {V : Type} [Fintype V] (H : SimpleGraph V), H.IsBipartite → H.Connected →
      ¬ H.IsAcyclic → (∀ v, 2 ≤ H.degree v) →
      ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c)) :
    ∀ {V : Type} [Fintype V] (H : SimpleGraph V), H.IsBipartite → H.Connected →
      ¬ H.IsAcyclic → ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c) := by
  have aux (k : ℕ) : ∀ (V : Type) [Fintype V], Fintype.card V = k →
      ∀ (H : SimpleGraph V), H.IsBipartite → H.Connected → ¬ H.IsAcyclic →
        ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro V _ hV H bip conn cyclic
      by_cases hdeg : ∀ v, 2 ≤ H.degree v
      · exact core H bip conn cyclic hdeg
      · obtain ⟨v, hv⟩ := not_forall.mp hdeg
        have hpos := (H.degree_pos_iff_exists_adj v).mpr (active_of_connected_cyclic conn cyclic v)
        have leaf : H.degree v = 1 := by omega
        let U : Set V := {v}ᶜ
        let J := H.induce U
        have hJb : J.IsBipartite := bip.of_hom ((Embedding.induce U).toHom)
        have hJconn : J.Connected := conn.induce_compl_singleton_of_degree_eq_one leaf
        have hJcyclic : ¬ J.IsAcyclic := cyclic_induce_compl_leaf cyclic leaf
        have hlt : Fintype.card U < k := by
          rw [← hV]
          exact Fintype.card_lt_of_injective_of_notMem (f := fun x : U => x.val)
            Subtype.val_injective (b := v) (by simp [U])
        obtain ⟨a, c, ha, hc, fit⟩ := ih (Fintype.card U) hlt U rfl J hJb hJconn hJcyclic
        exact ⟨a, c, ha, hc, extremal_limit_of_leaf_pruned leaf
          (active_of_connected_cyclic hJconn hJcyclic) ha fit⟩
  intro V _ H
  exact aux (Fintype.card V) V rfl H

theorem cyclic_exponent_gt_one {V : Type*} [Fintype V] {H : SimpleGraph V}
    (cyclic : ¬ H.IsAcyclic) {a c : ℝ} (fit : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (a : ℝ)) atTop (𝓝 c)) : 1 < a := by
  have impossible (d : ℝ) (lim : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ (1 : ℝ)) atTop (𝓝 d)) : False := by
    simp only [Real.rpow_one] at lim
    have low := tendsto_atTop.mp (cyclic_density_diverges cyclic) (d + 1)
    have high := (tendsto_order.mp lim).2 (d + 1) (by linarith)
    obtain ⟨_, hlo, hhi⟩ := (low.and high).exists
    exact (not_lt_of_ge hlo) hhi
  by_contra! h
  rcases h.lt_or_eq with h | rfl
  · exact impossible 0 (extremal_limit_at_higher_power h fit)
  · exact impossible c fit


def H1 : Prop := ∀ (q : ℕ) (H : SimpleGraph (Fin q)), H.IsAcyclic → (∀ v, ∃ w, H.Adj v w) →
  2 ≤ H.edgeFinset.card → (∀ n, extremalNumber n H ≤ q * n) →
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / n) atTop (𝓝 c)

def H2 : Prop := ∀ {V : Type} [Fintype V] (J : SimpleGraph V), J.IsBipartite → J.Connected →
  ¬ J.IsAcyclic → (∀ v, 2 ≤ J.degree v) →
  ∃ a c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n J : ℝ) / (n : ℝ) ^ a) atTop (𝓝 c)

theorem main : H1 → H2 → type_of% @Erdos713.erdos_713.parts.i := by
  intro h1 h2 q G bip edges
  have hq : 0 < q := by
    by_contra! hz
    have heq : q = 0 := by omega
    subst q
    have hbot : G = ⊥ := by
      ext v
      exact Fin.elim0 v
    rw [edgeFinset_eq_empty.mpr hbot] at edges
    simp at edges
  obtain ⟨k, H, hbip, hcard, hactive, hstable⟩ := remove_isolated_vertices G bip
  have hedges : 2 ≤ H.edgeFinset.card := hcard.symm ▸ edges
  have hlimit : ∃ α c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ α) atTop (𝓝 c) := by
    have active (v : Fin k) : ∃ w, H.Adj v w :=
      H.mem_support_iff_not_isIsolated.mpr (hactive v)
    by_cases forest : H.IsAcyclic
    · obtain ⟨c, hc, fit⟩ := h1 k H forest active hedges (forest_extremal_upper H forest)
      exact ⟨1, c, hc, by simpa only [Real.rpow_one] using fit⟩
    have connectedCyclic :
        ∀ {V : Type} [Fintype V] (J : SimpleGraph V), J.IsBipartite → J.Connected →
          ¬ J.IsAcyclic → ∃ a c : ℝ, 1 < a ∧ 0 < c ∧
            Tendsto (fun n : ℕ => (extremalNumber n J : ℝ) / (n : ℝ) ^ a) atTop (𝓝 c) := by
      apply connected_cyclic_limit_from_min_degree
      intro V _ J bip conn cyclic deg
      obtain ⟨a, c, hc, fit⟩ := h2 J bip conn cyclic deg
      exact ⟨a, c, cyclic_exponent_gt_one cyclic fit, hc, fit⟩
    obtain ⟨a, c, _, hc, fit⟩ :=
      limit_of_component_limits H active forest (fun C hC =>
        connectedCyclic C.toSimpleGraph (hbip.of_hom C.toSimpleGraph_hom)
          C.connected_toSimpleGraph hC)
    exact ⟨a, c, hc, fit⟩
  obtain ⟨α, c, hc, hlimH⟩ := hlimit
  have hlim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α)
      atTop (𝓝 c) := by
    apply hlimH.congr'
    filter_upwards [eventually_ge_atTop q] with n hn
    simp only [hstable n hn]
  have hα := exponent_ge_one G edges hlim
  have hup := exponent_le_bipartite_bound hq G bip hc hlim
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  refine ⟨α, c, ⟨hα, hup.trans_lt (sub_lt_self _ (one_div_pos.mpr hqpos))⟩, hc, ?_⟩
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · change Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (c * (n : ℝ) ^ α))
      atTop (𝓝 1)
    simpa only [div_div, mul_comm, div_self hc.ne'] using hlim.div_const c
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    positivity

end OMA.R_Erdos713_erdos_713_parts_i_R4
