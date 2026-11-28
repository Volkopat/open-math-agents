import OMAStatements.S_wp_gnrs_conjecture

-- Credit: @Dolcruz
namespace OMA.R_wp_gnrs_conjecture_R1

open OMA.S_wp_gnrs_conjecture

/-- For integer lengths on graphs excluding a fixed clique minor, pack weighted cuts.
    Only adjacent pairs impose upper bounds. -/
def H1 : Prop :=
  ∀ t : ℕ, ∃ c : ℝ, 1 ≤ c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬ IsMinor (⊤ : SimpleGraph (Fin t)) G → G.Connected →
    ∀ z : Sym2 (Fin n) → ℕ,
      ∃ (S : Finset ℕ) (cut : ℕ → Fin n → Bool) (a : ℕ → ℝ),
        (∀ i ∈ S, 0 ≤ a i) ∧
        (∀ u v, weightedDist G (fun e => (z e : ℝ)) u v ≤
          ∑ i ∈ S, if cut i u = cut i v then 0 else a i) ∧
        (∀ u v, G.Adj u v →
          (∑ i ∈ S, if cut i u = cut i v then 0 else a i) ≤ c * z s(u,v))

/-- Realize a finite weighted sum of cut distances isometrically in sequence ℓ₁. -/
def H2 : Prop :=
  ∀ (n : ℕ) (S : Finset ℕ) (cut : ℕ → Fin n → Bool) (a : ℕ → ℝ),
    (∀ i ∈ S, 0 ≤ a i) →
    ∃ f : Fin n → lp (fun _ : ℕ => ℝ) 1, ∀ u v,
      ‖f u - f v‖ = ∑ i ∈ S, if cut i u = cut i v then 0 else a i

lemma integer_scale {E : Type} [Fintype E] (w : E → ℝ) :
    ∃ (r : ℝ) (z : E → ℕ), 0 < r ∧ ∀ e, 0 ≤ w e →
      r * w e ≤ (z e : ℝ) ∧ (z e : ℝ) ≤ 2 * r * w e := by
  classical
  let r := 1 + ∑ e, max 0 (w e)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r, fun e => if 0 < w e then ⌊r * w e⌋₊ + 1 else 0, hr, ?_⟩
  intro e hw
  rcases hw.eq_or_lt with he | he
  · simp [← he]
  · simp only [if_pos he, Nat.cast_add, Nat.cast_one]
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => max 0 (w j)⁻¹) (fun j _ => le_max_left _ _) (Finset.mem_univ e)
    have hinv : (w e)⁻¹ ≤ r := by
      dsimp [r]
      linarith [le_max_right 0 (w e)⁻¹]
    have hone : 1 ≤ r * w e := by
      simpa [ne_of_gt he] using mul_le_mul_of_nonneg_right hinv hw
    exact ⟨(Nat.lt_floor_add_one _).le, by
      nlinarith [Nat.floor_le (mul_nonneg hr.le hw)]⟩

lemma walk_cost_le {n : ℕ} {G : SimpleGraph (Fin n)} (w : Sym2 (Fin n) → ℝ)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) {u v : Fin n} (p : G.Walk u v) :
    weightedDist G w u v ≤ (p.edges.map w).sum := by
  apply ciInf_le _ p
  refine ⟨0, ?_⟩
  rintro _ ⟨q, rfl⟩
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact hw e (q.edges_subset_edgeSet he)

lemma extend_edges {n : ℕ} {G : SimpleGraph (Fin n)}
    (f : Fin n → lp (fun _ : ℕ => ℝ) 1) (w : Sym2 (Fin n) → ℝ) (C : ℝ)
    (h : ∀ u v, G.Adj u v → ‖f u - f v‖ ≤ C * w s(u,v))
    {u v : Fin n} (p : G.Walk u v) : ‖f u - f v‖ ≤ C * (p.edges.map w).sum := by
  induction p with
  | nil => simp
  | @cons u v x huv q ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, mul_add]
    have tri := dist_triangle (f u) (f v) (f x)
    simpa only [dist_eq_norm] using tri.trans (by
      simpa only [dist_eq_norm] using add_le_add (h u v huv) ih)

theorem main : H1 → H2 → type_of% @OMA.S_wp_gnrs_conjecture.main := by
  classical
  intro packing realize F closed omitted
  obtain ⟨t, H, hH⟩ := omitted
  obtain ⟨c, hc, pack⟩ := packing t
  refine ⟨2 * c, by linarith, ?_⟩
  intro n G hG conn w hw
  have free : ¬ IsMinor (⊤ : SimpleGraph (Fin t)) G := by
    rintro ⟨B, ne, disj, connected, adj⟩
    apply hH (closed t n H G hG ?_)
    exact ⟨B, ne, disj, connected, fun i j hij => adj i j ((SimpleGraph.top_adj i j).2 hij.ne)⟩
  obtain ⟨r, z, hr, approx⟩ := integer_scale w
  obtain ⟨S, cut, a, ha, lower, edge⟩ := pack n G free conn z
  obtain ⟨f, hf⟩ := realize n S cut a ha
  have hC : 0 < 2 * c * r := by positivity
  have edgeBound (u v) (huv : G.Adj u v) : ‖f u - f v‖ ≤ (2 * c * r) * w s(u,v) := by
    rw [hf]
    calc
      _ ≤ c * z s(u,v) := edge u v huv
      _ ≤ c * (2 * r * w s(u,v)) :=
        mul_le_mul_of_nonneg_left (approx _ (hw _ huv)).2 (by linarith)
      _ = _ := by ring
  refine ⟨f, r, hr, ?_⟩
  intro u v
  let _ : Nonempty (G.Walk u v) := conn.preconnected u v
  constructor
  · rw [hf]
    apply le_trans _ (lower u v)
    apply le_ciInf
    intro p
    calc
      _ ≤ r * (p.edges.map w).sum :=
        mul_le_mul_of_nonneg_left (walk_cost_le w hw p) hr.le
      _ = (p.edges.map (fun e => r * w e)).sum := (List.sum_map_mul_left ..).symm
      _ ≤ _ := List.sum_le_sum (fun e he => (approx e (hw _ (p.edges_subset_edgeSet he))).1)
  · rw [mul_comm (2 * c * r)]
    apply (div_le_iff₀ hC).mp
    apply le_ciInf
    intro p
    apply (div_le_iff₀ hC).mpr
    simpa only [mul_comm (2 * c * r)] using extend_edges f w _ edgeBound p

end OMA.R_wp_gnrs_conjecture_R1
