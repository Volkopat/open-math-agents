import FormalConjectures.ErdosProblems.«1085»
import Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-! Distinct parts of a unit-distance multipartite graph span orthogonal direction spaces. -/

open Filter
open scoped EuclideanGeometry Finset InnerProductSpace Sym2 Topology

theorem OMA.unit_distance_closed_quadrilateral {d : ℕ} (a b c e : ℝ^d)
    (hac : dist a c = 1) (hae : dist a e = 1) (hbc : dist b c = 1) (hbe : dist b e = 1) :
    ⟪a - b, c - e⟫_ℝ = 0 := by
  have h : dist a c ^ 2 - dist a e ^ 2 - dist b c ^ 2 + dist b e ^ 2 = 0 := by
    simp [hac, hae, hbc, hbe]
  simp only [dist_eq_norm, norm_sub_sq_real] at h
  simp only [inner_sub_left, inner_sub_right]
  linarith

theorem OMA.unit_distance_equipartite_dimension {r d : ℕ} (hr : 1 < r)
    (v : Fin r × Fin 3 → ℝ^d) (hv : Function.Injective v)
    (hcross : ∀ (i j : Fin r) (a b : Fin 3), i ≠ j → dist (v (i, a)) (v (j, b)) = 1) :
    r * 2 ≤ d := by
  classical
  let w (i : Fin r) (k : Fin 2) : ℝ^d := v (i, k.succ) - v (i, 0)
  have hblock (i : Fin r) : LinearIndependent ℝ (w i) := by
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card
      (by simpa using hr : 1 < Fintype.card (Fin r)) i
    let point (k : Fin 3) := v (i, k)
    have hsphere : EuclideanGeometry.Cospherical (Set.range point) := by
      refine ⟨v (j, 0), 1, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact hcross i j k 0 hj.symm
    have hinj : Function.Injective point := by
      intro a b hab
      exact congrArg Prod.snd (hv hab)
    have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ point 0).mp
      (hsphere.affineIndependent (by rfl) hinj)
    exact hlin.comp (fun k : Fin 2 => ⟨k.succ, Fin.succ_ne_zero k⟩)
      (fun _ _ h => Fin.succ_injective _ (congrArg Subtype.val h))
  have hortho (i j : Fin r) (a b : Fin 2) (hij : i ≠ j) :
      ⟪w i a, w j b⟫_ℝ = 0 :=
    OMA.unit_distance_closed_quadrilateral _ _ _ _ (hcross i j a.succ b.succ hij)
      (hcross i j a.succ 0 hij) (hcross i j 0 b.succ hij) (hcross i j 0 0 hij)
  have hall : LinearIndependent ℝ (fun k : Fin r × Fin 2 => w k.1 k.2) := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg
    let z (i : Fin r) := ∑ k : Fin 2, g (i, k) • w i k
    have hzsum : ∑ i, z i = 0 := by
      simpa only [z, Fintype.sum_prod_type] using hg
    have horthz (i j : Fin r) (hij : i ≠ j) : ⟪z i, z j⟫_ℝ = 0 := by
      simp only [z, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      simp [hortho, hij]
    have hz (i : Fin r) : z i = 0 := by
      have h := congrArg (inner ℝ (z i)) hzsum
      rw [inner_sum, inner_zero_right, Finset.sum_eq_single i] at h
      · exact inner_self_eq_zero.mp h
      · exact fun j _ hji => horthz i j hji.symm
      · simp
    rintro ⟨i, k⟩
    exact Fintype.linearIndependent_iff.mp (hblock i) _ (hz i) k
  simpa only [Fintype.card_prod, Fintype.card_fin, finrank_euclideanSpace_fin]
    using hall.fintype_card_le_finrank

noncomputable def OMA.unit_dist_graph {d : ℕ} (S : Finset (ℝ^d)) : SimpleGraph S where
  Adj u v := dist (u : ℝ^d) (v : ℝ^d) = 1
  symm := ⟨fun _ _ h => (dist_comm _ _).trans h⟩
  loopless := ⟨fun u h => by simp at h⟩

theorem OMA.unit_dist_graph_free (d : ℕ) (hd : 4 ≤ d) (S : Finset (ℝ^d)) :
    (SimpleGraph.completeEquipartiteGraph (d / 2 + 1) 3).Free (OMA.unit_dist_graph S) := by
  rintro ⟨f⟩
  let v (k : Fin (d / 2 + 1) × Fin 3) : ℝ^d := f k
  have hv : Function.Injective v := fun _ _ h => f.injective (Subtype.ext h)
  have hc (i j : Fin (d / 2 + 1)) (a b : Fin 3) (hij : i ≠ j) :
      dist (v (i, a)) (v (j, b)) = 1 :=
    f.toHom.map_adj (SimpleGraph.completeEquipartiteGraph_adj.mpr hij)
  have := OMA.unit_distance_equipartite_dimension (by omega) v hv hc
  omega

open scoped Classical in
theorem OMA.unit_dist_num_le_edges (d : ℕ) (S : Finset (ℝ^d)) :
    unitDistNum S ≤ (OMA.unit_dist_graph S).edgeFinset.card := by
  classical
  unfold unitDistNum
  apply Finset.card_le_card_of_surjOn (Sym2.map (fun v : S => (v : ℝ^d)))
  intro e he
  obtain ⟨hmem, hdist⟩ := Finset.mem_filter.mp he
  have hrepr : s(e.out.1, e.out.2) = e := Quot.out_eq _
  have hp := Finset.mk_mem_sym2_iff.mp (show s(e.out.1, e.out.2) ∈ S.sym2 by rwa [hrepr])
  let x : S := ⟨e.out.1, hp.1⟩
  let y : S := ⟨e.out.2, hp.2⟩
  refine ⟨s(x, y), ?_, hrepr⟩
  exact SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (G := OMA.unit_dist_graph S)).mpr hdist)

theorem OMA.unit_dist_le_extremal (d : ℕ) (hd : 4 ≤ d) (n : ℕ) :
    Erdos1085.f d n ≤ SimpleGraph.extremalNumber n
      (SimpleGraph.completeEquipartiteGraph (d / 2 + 1) 3) := by
  classical
  unfold Erdos1085.f
  apply ciSup_le'
  intro S
  apply ciSup_le'
  intro hS
  refine (OMA.unit_dist_num_le_edges d S).trans ?_
  have hs : Fintype.card S = n := (Fintype.card_coe S).trans hS
  rw [← hs]
  exact SimpleGraph.card_edgeFinset_le_extremalNumber (OMA.unit_dist_graph_free d hd S)

theorem OMA.equipartite_extremal_quadratic (p : ℕ) (hp : 0 < p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ n : ℕ,
      (SimpleGraph.extremalNumber n (SimpleGraph.completeEquipartiteGraph (p + 1) 3) : ℝ) ≤
      (1 - 1 / (p : ℝ) + ε) / 2 * ((n : ℝ) * ((n : ℝ) + 1)) + K := by
  classical
  let H := SimpleGraph.completeEquipartiteGraph (p + 1) 3
  let c : ℝ := (1 - 1 / (p : ℝ) + ε) / 2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hq : 0 ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_iff₀ hpR, one_mul]
    exact_mod_cast hp
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hH : H ≠ ⊥ := by
    rw [ne_eq, SimpleGraph.completeEquipartiteGraph_eq_bot_iff]
    omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree hε p 3)
  let M := max 1 N
  refine ⟨(M : ℝ) ^ 2, ?_⟩
  intro n
  change (SimpleGraph.extremalNumber n H : ℝ) ≤
    c * ((n : ℝ) * ((n : ℝ) + 1)) + (M : ℝ) ^ 2
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < M
    · have hsmall : SimpleGraph.extremalNumber n H ≤ n ^ 2 := by
        rw [← Fintype.card_fin n, SimpleGraph.extremalNumber_le_iff]
        intro G _ hG
        exact G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)
      have hsq : (SimpleGraph.extremalNumber n H : ℝ) ≤ (M : ℝ) ^ 2 := by
        exact_mod_cast hsmall.trans (Nat.pow_le_pow_left hn.le 2)
      exact hsq.trans (le_add_of_nonneg_left (by positivity))
    · have hMn := le_of_not_gt hn
      have hNn : N ≤ n := (le_max_right 1 N).trans hMn
      have h1n : 1 ≤ n := (le_max_left 1 N).trans hMn
      let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
      obtain ⟨G, hDec, hG⟩ := SimpleGraph.exists_isExtremal_free (V := Fin n) hH
      let _ := hDec
      have hmin : (G.minDegree : ℝ) < (1 - 1 / (p : ℝ) + ε) * n := by
        exact lt_of_not_ge (fun h => hG.prop (hN n hNn h))
      obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
      have hedge : G.edgeFinset.card = SimpleGraph.extremalNumber n H := by
        simpa only [Fintype.card_fin] using SimpleGraph.card_edgeFinset_of_isExtremal_free hG
      have hdeleteNat : G.edgeFinset.card ≤
          SimpleGraph.extremalNumber (n - 1) H + G.degree v := by
        have hdel := SimpleGraph.card_edgeFinset_deleteIncidenceSet_le_extremalNumber hG.prop v
        rw [G.card_edgeFinset_deleteIncidenceSet v, Fintype.card_fin] at hdel
        omega
      have hdelete : (SimpleGraph.extremalNumber n H : ℝ) ≤
          (SimpleGraph.extremalNumber (n - 1) H : ℝ) + (G.minDegree : ℝ) := by
        rw [← hedge, hv]
        exact_mod_cast hdeleteNat
      have hprev := ih (n - 1) (by omega)
      rw [Nat.cast_sub h1n, Nat.cast_one] at hprev
      dsimp [c] at hprev ⊢
      nlinarith only [hdelete, hprev, hmin]

theorem OMA.unit_dist_eventual_upper (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (Erdos1085.f d n : ℝ) ≤
      (((d / 2 - 1 : ℕ) : ℝ) / (2 * ((d / 2 : ℕ) : ℝ)) + ε) * (n : ℝ) ^ 2 := by
  let p := d / 2
  have hp : 0 < p := by dsimp [p]; omega
  let c₀ : ℝ := ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ))
  let c : ℝ := (1 - 1 / (p : ℝ) + ε) / 2
  have hc : c = c₀ + ε / 2 := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simp only [c, c₀, Nat.cast_sub hp, Nat.cast_one]
    field_simp
  obtain ⟨K, hK⟩ := OMA.equipartite_extremal_quadratic p hp ε hε
  have hsmall : Tendsto (fun n : ℕ => c + c * (n : ℝ)⁻¹ + K * ((n : ℝ)⁻¹) ^ 2)
      atTop (𝓝 c) := by
    have hn := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      ((tendsto_const_nhds (x := c)).add (hn.const_mul c)).add ((hn.pow 2).const_mul K)
  have hlim : ∀ᶠ n : ℕ in atTop, c + c * (n : ℝ)⁻¹ + K * ((n : ℝ)⁻¹) ^ 2 < c₀ + ε :=
    (tendsto_order.mp hsmall).2 _ (by rw [hc]; linarith)
  filter_upwards [hlim, eventually_gt_atTop (0 : ℕ)] with n hn hpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  have hf : (Erdos1085.f d n : ℝ) ≤
      (SimpleGraph.extremalNumber n (SimpleGraph.completeEquipartiteGraph (p + 1) 3) : ℝ) := by
    exact_mod_cast OMA.unit_dist_le_extremal d hd n
  calc
    (Erdos1085.f d n : ℝ) ≤ c * ((n : ℝ) * ((n : ℝ) + 1)) + K :=
      hf.trans (hK n)
    _ = (c + c * (n : ℝ)⁻¹ + K * ((n : ℝ)⁻¹) ^ 2) * (n : ℝ) ^ 2 := by
      field_simp
    _ ≤ (c₀ + ε) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hn.le (sq_nonneg _)

theorem OMA.solution : type_of% @Erdos1085.erdos_1085.variants.upper_d4_erdos := by
  intro d hd
  let c : ℝ := ((d / 2 - 1 : ℕ) : ℝ) / (2 * ((d / 2 : ℕ) : ℝ))
  let g (n : ℕ) : ℝ := max 0 ((Erdos1085.f d n : ℝ) / (n : ℝ) ^ 2 - c)
  refine ⟨g, tendsto_order.mpr ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (le_max_left _ _))
  · intro b hb
    filter_upwards [OMA.unit_dist_eventual_upper d hd (b / 2) (by positivity),
      eventually_gt_atTop (0 : ℕ)] with n hn hpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
    have hdiv := (div_le_iff₀ (sq_pos_of_pos hnR)).mpr hn
    change (Erdos1085.f d n : ℝ) / (n : ℝ) ^ 2 ≤ c + b / 2 at hdiv
    exact max_lt_iff.mpr ⟨hb, by linarith⟩
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz : Erdos1085.f d 0 = 0 := by
        unfold Erdos1085.f
        refine Nat.eq_zero_of_le_zero (ciSup_le' fun S => ciSup_le' fun hS => ?_)
        simpa only [hS, Nat.choose_zero_succ] using unitDistNum_le_choose_two S
      simp [hz]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hmax : (Erdos1085.f d n : ℝ) / (n : ℝ) ^ 2 - c ≤ g n := le_max_right _ _
      apply (div_le_iff₀ (sq_pos_of_pos hnR)).mp
      linarith
