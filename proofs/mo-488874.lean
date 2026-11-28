import OMAStatements.S_mo_488874
import Mathlib

/-!
# Minimum edge count for Tanny Libman's strict degree-split condition

For odd maximum degree r ≥ 3 the sharp minimum is (r−1)(3r+1)/2.
A hub with r−1 three-vertex lobes realizes the bound. The lower bound
follows from a two-factor obstruction for degree-bounded multigraphs,
derived here directly from Mathlib's perfect-matching theorem. Each vertex
has r real or slack incidence ports and r−2 inner vertices. The slack
ports form a single clique. A canonical Tutte violator gives disjoint sets
S and T and saturated odd-boundary components. Counting their vertices
and the edges incident with T proves sharpness. Even degrees at least four
are handled by a two-factor of a doubled even-regular multigraph.

Source question: https://mathoverflow.net/questions/488874
Classical factor inequalities: L. Lovász, Subgraphs with prescribed valencies
(1970), Theorem 7.3, https://doi.org/10.1016/S0021-9800(70)80033-3.

The generic minimal-violator component lemmas and the canonicalization proof
adapt Juan Pablo Traverso Gianini's Apache-2.0 formalization of Tutte's
factor theorem. The latter is modified here to allow a clique of slack
ports and parallel real edges. Formalization source at revision
dc3bbce463c80c499d3e9fa072d13f9145d907d0:
https://github.com/jtraverso/tutte-f-factor
The Apache-2.0 notice and license are included below.
-/


namespace OMA.S_mo_488874

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
lemma Multigraph.degree_le_max (G : Multigraph V E) (c : E → ℕ) (v : V) :
    G.degree c v ≤ G.maxDegree c := Finset.le_sup (Finset.mem_univ v)

omit [Fintype V] in
lemma Multigraph.degree_pos_of_edge (G : Multigraph V E) {c : E → ℕ} {e : E} (he : 0 < c e) :
    0 < G.degree c (G.source e) := by
  apply he.trans_le
  have h := Finset.single_le_sum (f := fun t => if G.source e = G.source t ∨ G.source e = G.target t then c t else 0)
    (fun t (_ : t ∈ (Finset.univ : Finset E)) => Nat.zero_le _) (Finset.mem_univ e)
  simpa only [true_or, eq_self, if_true, degree] using h

lemma Multigraph.maxDegree_pos (G : Multigraph V E) {c : E → ℕ} (h : ∃ e, 0 < c e) :
    0 < G.maxDegree c := by
  obtain ⟨e, he⟩ := h
  exact (G.degree_pos_of_edge he).trans_le (G.degree_le_max _ _)

omit [Fintype V] in
lemma Multigraph.degree_add (G : Multigraph V E) (x y : E → ℕ)
    (he : ∀ e, x e+y e = G.multiplicity e) (v : V) :
    G.degree x v + G.degree y v = G.degree G.multiplicity v := by
  unfold degree
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split <;> simp_all

end OMA.S_mo_488874

namespace OMA.S_mo_488874

abbrev LobeV (k : ℕ) := Option (Fin (2*k) × Fin 3)
abbrev LobeE (k : ℕ) := Fin (2*k) × Fin 4

def lobes (k : ℕ) : Multigraph (LobeV k) (LobeE k) where
  source e := ![none, some (e.1,0), some (e.1,0), some (e.1,1)] e.2
  target e := ![some (e.1,0), some (e.1,1), some (e.1,2), some (e.1,2)] e.2
  no_loops := by
    rintro ⟨i,j⟩
    fin_cases j <;> simp
  multiplicity e := ![1,k,k,k+1] e.2

lemma lobes_edges (k : ℕ) : (lobes k).edges = (2*k)*(3*k+2) := by
  simp [Multigraph.edges, lobes, Fintype.sum_prod_type, Fin.sum_univ_succ]
  left
  ring

lemma lobes_degree_hub (k : ℕ) (c : LobeE k → ℕ) :
    (lobes k).degree c none = ∑ i, c (i,0) := by
  simp [Multigraph.degree, lobes, Fintype.sum_prod_type, Fin.sum_univ_succ]

lemma lobes_degree_a (k : ℕ) (c : LobeE k → ℕ) (i : Fin (2*k)) :
    (lobes k).degree c (some (i,0)) = c (i,0)+c (i,1)+c (i,2) := by
  simp [Multigraph.degree, lobes, Fintype.sum_prod_type, Fin.sum_univ_succ, ← ite_add_zero, add_assoc]

lemma lobes_degree_b (k : ℕ) (c : LobeE k → ℕ) (i : Fin (2*k)) :
    (lobes k).degree c (some (i,1)) = c (i,1)+c (i,3) := by
  simp [Multigraph.degree, lobes, Fintype.sum_prod_type, Fin.sum_univ_succ, ← ite_add_zero]

lemma lobes_degree_c (k : ℕ) (c : LobeE k → ℕ) (i : Fin (2*k)) :
    (lobes k).degree c (some (i,2)) = c (i,2)+c (i,3) := by
  simp [Multigraph.degree, lobes, Fintype.sum_prod_type, Fin.sum_univ_succ, ← ite_add_zero]

lemma lobes_sat (k : ℕ) (i : Fin (2*k)) (j : Fin 3) :
    (lobes k).degree (lobes k).multiplicity (some (i,j)) = 2*k+1 := by
  fin_cases j
  · change (lobes k).degree (lobes k).multiplicity (some (i,0)) = _
    rw [lobes_degree_a k _ i]; simp [lobes]; omega
  · change (lobes k).degree (lobes k).multiplicity (some (i,1)) = _
    rw [lobes_degree_b k _ i]; simp [lobes]; omega
  · change (lobes k).degree (lobes k).multiplicity (some (i,2)) = _
    rw [lobes_degree_c k _ i]; simp [lobes]; omega

lemma lobes_max {k : ℕ} (hk : 0 < k) : (lobes k).maxDegree (lobes k).multiplicity = 2*k+1 := by
  let i : Fin (2*k) := ⟨0, by omega⟩
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    cases v with
    | none => rw [lobes_degree_hub]; simp [lobes]
    | some a => exact (lobes_sat k a.1 a.2).le
  · rw [← lobes_sat k i 0]
    exact Multigraph.degree_le_max ..

theorem lobes_indecomposable {k : ℕ} (hk : 0 < k) : (lobes k).indecomposable := by
  intro x y he hx hy
  let G := lobes k
  let j := G.maxDegree x
  let b := G.maxDegree y
  rw [lobes_max hk]
  by_contra! hbad
  change j+b ≤ 2*k+1 at hbad
  have hjpos : 0 < j := G.maxDegree_pos hx
  have hbpos : 0 < b := G.maxDegree_pos hy
  have hd (i : Fin (2*k)) (v : Fin 3) : G.degree x (some (i,v)) = j := by
    have hv := G.degree_add x y he (some (i,v))
    have h1 : G.degree x (some (i,v)) ≤ j := G.degree_le_max _ _
    have h2 : G.degree y (some (i,v)) ≤ b := G.degree_le_max _ _
    have h3 : G.degree G.multiplicity (some (i,v)) = 2*k+1 := lobes_sat ..
    omega
  have bridge (i : Fin (2*k)) : x (i,0) = j % 2 := by
    have h0 := hd i 0
    have h1 := hd i 1
    have h2 := hd i 2
    change (lobes k).degree x _ = _ at h0 h1 h2
    rw [lobes_degree_a] at h0
    rw [lobes_degree_b] at h1
    rw [lobes_degree_c] at h2
    have hbr := he (i,0)
    change x (i,0)+y (i,0) = 1 at hbr
    omega
  by_cases hj : j % 2 = 0
  · have hblue (i : Fin (2*k)) : y (i,0) = 1 := by
      have he' := he (i,0)
      change x (i,0) + y (i,0) = 1 at he'
      rw [bridge, hj] at he'
      omega
    have hh : (lobes k).degree y none ≤ b := G.degree_le_max _ _
    rw [lobes_degree_hub] at hh
    simp [hblue] at hh
    omega
  · have hred (i : Fin (2*k)) : x (i,0) = 1 := by rw [bridge]; omega
    have hh : (lobes k).degree x none ≤ j := G.degree_le_max _ _
    rw [lobes_degree_hub] at hh
    simp [hred] at hh
    omega

/-- For each odd maximum degree at least three, a finite loopless multigraph
attains the claimed upper bound on the minimum number of edges. -/
theorem lobes_witness {k : ℕ} (hk : 0 < k) :
    (lobes k).indecomposable ∧ (lobes k).maxDegree (lobes k).multiplicity = 2*k+1 ∧
    (lobes k).edges = (2*k)*(3*k+2) :=
  ⟨lobes_indecomposable hk, lobes_max hk, lobes_edges k⟩

end OMA.S_mo_488874

namespace OMA.S_mo_488874

/-- Counts for the saturated odd-boundary components of a Lovász deficiency certificate. -/
structure BarrierCounts (ι : Type*) [Fintype ι] where
  degree : ℤ
  degree_ge : 3 ≤ degree
  leftCount : ℤ
  rightCount : ℤ
  between : ℤ
  vertices : ι → ℤ
  leftEdges : ι → ℤ
  rightEdges : ι → ℤ
  nonempty : ∀ i, 1 ≤ vertices i
  left_nonneg : ∀ i, 0 ≤ leftEdges i
  right_pos : ∀ i, 1 ≤ rightEdges i
  singleton_boundary : ∀ i, vertices i = 1 → leftEdges i + rightEdges i = degree
  pair_left_edge : ∀ i, vertices i = 2 → 1 ≤ leftEdges i
  left_capacity : between + ∑ i, leftEdges i ≤ degree * leftCount
  right_capacity : between + ∑ i, rightEdges i ≤ degree * rightCount
  obstruction : 2*leftCount + (degree-2)*rightCount < between + Fintype.card ι

/-- Every certificate requires at least 3(r−1) saturated vertices and r−1 edges to T. -/
theorem count_saturated {ι : Type*} [Fintype ι] (c : BarrierCounts ι) :
    3*(c.degree-1) ≤ ∑ i, c.vertices i ∧ c.degree-1 ≤ ∑ i, c.rightEdges i := by
  classical
  let q : ℤ := Fintype.card ι
  let d := c.rightCount - c.leftCount
  let α := c.degree*c.leftCount - c.between
  let β := c.degree*c.rightCount - c.between - q
  have hq : (∑ _ : ι, (1 : ℤ)) = q := by simp [q]
  have hal : (∑ i, c.leftEdges i) ≤ α := by dsimp [α]; linarith [c.left_capacity]
  have har : (∑ i, (c.rightEdges i-1)) ≤ β := by
    rw [Finset.sum_sub_distrib, hq]
    dsimp [β]
    linarith [c.right_capacity]
  have hα : 0 ≤ α := le_trans (Finset.sum_nonneg fun i _ => c.left_nonneg i) hal
  have hβ : 0 ≤ β := le_trans (Finset.sum_nonneg fun i _ => by linarith [c.right_pos i]) har
  have hqbig : (c.degree - 2)*d + α + 1 ≤ q := by
    dsimp [d, α, q]
    have h := c.obstruction
    nlinarith only [show 2*c.leftCount + (c.degree-2)*c.rightCount + 1 ≤ c.between + Fintype.card ι
      from h]
  have hβsmall : β ≤ 2*d-1 := by
    dsimp [β, α, d] at *
    nlinarith only [hqbig]
  have hd : 1 ≤ d := by omega
  have hqmin : c.degree-1 ≤ q := by
    nlinarith only [hqbig, hα, mul_nonneg (show 0 ≤ c.degree-2 by linarith [c.degree_ge])
      (show 0 ≤ d-1 by omega)]
  constructor
  · have hcr (i : ι) : 3 ≤ c.vertices i + c.leftEdges i + (c.rightEdges i - 1) := by
      by_cases h1 : c.vertices i = 1
      · linarith [c.singleton_boundary i h1, c.degree_ge]
      by_cases h2 : c.vertices i = 2
      · linarith [c.pair_left_edge i h2, c.right_pos i]
      have h := c.nonempty i
      have h' := c.left_nonneg i
      have h'' := c.right_pos i
      omega
    have hall := Finset.sum_le_sum (s := Finset.univ) fun i _ => hcr i
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib] at hall
    change q * 3 ≤ _ at hall
    have hvertex : (3*c.degree - 8)*d + 2*α + 4 ≤ ∑ i, c.vertices i := by
      nlinarith only [hall, hqbig, hβsmall, hal, har]
    by_cases hd2 : 2 ≤ d
    · nlinarith only [hvertex, mul_nonneg (show 0 ≤ 3*c.degree-8 by linarith [c.degree_ge])
        (show 0 ≤ d-2 by omega), hα, c.degree_ge]
    have hdone : d=1 := by omega
    by_cases ha1 : 1 ≤ α
    · rw [hdone] at hvertex
      linarith
    have ha0 : α = 0 := by omega
    have hb1 : β ≤ 1 := by omega
    have hpoint (i : ι) : (3 : ℤ) ≤ c.vertices i := by
      have hleft := (Finset.single_le_sum (f := c.leftEdges)
        (fun j _ => c.left_nonneg j) (Finset.mem_univ i)).trans hal
      have hright := (Finset.single_le_sum (f := fun j => c.rightEdges j - 1)
        (fun j _ => by linarith [c.right_pos j]) (Finset.mem_univ i)).trans har
      by_contra! hbad
      have hn := c.nonempty i
      have hcases : c.vertices i = 1 ∨ c.vertices i = 2 := by omega
      rcases hcases with h | h
      · linarith [c.singleton_boundary i h, c.degree_ge]
      · linarith [c.pair_left_edge i h]
    have hg := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hg
    change q*3 ≤ _ at hg
    linarith
  · exact hqmin.trans (hq ▸ Finset.sum_le_sum (s := Finset.univ) (fun i _ => c.right_pos i))

/-- The degree sum of any loopless multigraph with such a certificate is at least
(r−1)(3r+1), with the T-side of the cut included separately. -/
theorem degree_sum_lower_bound {ι : Type*} [Fintype ι] (c : BarrierCounts ι) (edges : ℤ)
    (hdeg : c.degree*(∑ i, c.vertices i) + (∑ i, c.rightEdges i) ≤ 2*edges) :
    (c.degree-1)*(3*c.degree+1) ≤ 2*edges := by
  obtain ⟨hv, ht⟩ := count_saturated c
  have h := mul_le_mul_of_nonneg_left hv (show 0 ≤ c.degree by linarith [c.degree_ge])
  nlinarith only [hdeg, h, ht]

end OMA.S_mo_488874

namespace OMA.S_mo_488874

open Finset

/-- In an integer-weighted regular bipartite graph of positive degree, the
positive edges contain a perfect matching. The two vertex types may differ. -/
theorem weighted_matching {I J : Type*} [Fintype I] [Fintype J] (a : I → J → ℕ)
    (d : ℕ) (hd : 0 < d) (hr : ∀ i, ∑ j, a i j = d) (hc : ∀ j, ∑ i, a i j = d) :
    ∃ p : I ≃ J, ∀ i, 0 < a i (p i) := by
  classical
  let N (i : I) := univ.filter (fun j => 0 < a i j)
  have hcard : Fintype.card I = Fintype.card J := by
    have h := Finset.sum_comm (s := (univ : Finset I)) (t := (univ : Finset J)) (f := a)
    simpa [hr, hc, hd.ne'] using h
  have hhall (s : Finset I) : s.card ≤ (s.biUnion N).card := by
    let t := s.biUnion N
    have hrow (i) (hi : i ∈ s) : ∑ j ∈ t, a i j = d := by
      rw [← hr i]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      by_contra! h
      exact hj (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨mem_univ _, by omega⟩⟩)
    have hcol (j) : ∑ i ∈ s, a i j ≤ d := by
      rw [← hc j]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
    have h := Finset.sum_le_sum (s := t) (fun j _ => hcol j)
    rw [Finset.sum_comm] at h
    apply Nat.le_of_mul_le_mul_right (c := d) _ hd
    simpa [Finset.sum_congr rfl hrow, t] using h
  obtain ⟨f, hf, hm⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hhall
  have hb := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩
  exact ⟨Equiv.ofBijective f hb, fun i => (Finset.mem_filter.mp (hm i)).2⟩

end OMA.S_mo_488874

namespace OMA.S_mo_488874

open Finset

section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The contribution at a vertex of one specified endpoint of an edge. -/
def pt (v w : V) : ℕ := if w = v then 1 else 0

lemma sum_pt (v : V) : ∑ w, pt v w = 1 := by simp [pt]

/-- Petersen's 2-factor theorem on an explicitly indexed edge set.
Incidences count both ends; in particular this lemma also permits loops. -/
theorem regular_two_factor (s t : E → V) (k : ℕ) (hk : 0 < k)
    (hreg : ∀ v, ∑ e, (pt v (s e) + pt v (t e)) = 2*k) :
    ∃ red : E → ℕ, (∀ e, red e ≤ 1) ∧
      ∀ v, ∑ e, (pt v (s e) + pt v (t e))*red e = 2 := by
  classical
  let a (e : E) (vi : V × Fin k) := pt vi.1 (s e) + pt vi.1 (t e)
  have hrow (e) : ∑ vi, a e vi = 2*k := by
    rw [Fintype.sum_prod_type]
    change (∑ v : V, ∑ _ : Fin k, (pt v (s e) + pt v (t e))) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib, pt, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [mul_comm]
  have hcol (vi : V × Fin k) : ∑ e, a e vi = 2*k := hreg _
  obtain ⟨p, hp⟩ := weighted_matching a (2*k) (by omega) hrow hcol
  let dst (e : E) := (p e).1
  let src (e : E) := if dst e = s e then t e else s e
  have hinc (e : E) (v : V) : pt v (s e) + pt v (t e) = pt v (src e) + pt v (dst e) := by
    have h := hp e
    change 0 < pt (dst e) (s e) + pt (dst e) (t e) at h
    by_cases hs : dst e = s e
    · simp [src,hs,add_comm]
    · have ht : dst e = t e := by by_contra h'; simp [pt, Ne.symm hs, Ne.symm h'] at h
      simp only [src,if_neg hs,ht]
  have hin (v : V) : ∑ e, pt v (dst e) = k := by
    calc
      ∑ e, pt v (dst e) = ∑ vi : V × Fin k, pt v vi.1 := p.sum_comp (fun vi : V × Fin k => pt v vi.1)
      _ = k := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
          ← Finset.mul_sum, sum_pt, mul_one, Nat.cast_id]
  have hout (v : V) : ∑ e, pt v (src e) = k := by
    have h := hreg v
    simp_rw [fun e => hinc e v] at h
    rw [Finset.sum_add_distrib, hin] at h
    omega
  let arcs (u v : V) := ∑ e, (pt u (src e) * pt v (dst e))
  have har (u : V) : ∑ v, arcs u v = k := by
    dsimp [arcs]
    rw [Finset.sum_comm]
    simpa [← Finset.mul_sum,pt] using hout u
  have hac (v : V) : ∑ u, arcs u v = k := by
    dsimp [arcs]
    rw [Finset.sum_comm]
    simpa [← Finset.sum_mul,pt] using hin v
  obtain ⟨q,hq⟩ := weighted_matching arcs k hk har hac
  have hex (u : V) : ∃ e, src e = u ∧ dst e = q u := by
    by_contra! h
    have hz : arcs u (q u) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      by_cases hs : src e = u <;> simp [pt,hs,h e] 
    exact (hq u).ne' hz
  choose f hsrc hdst using hex
  let red (e : E) : ℕ := ∑ u, if e = f u then 1 else 0
  refine ⟨red, ?_, ?_⟩
  · intro e
    have hinj : Function.Injective f := fun u v h => by simpa [hsrc] using congrArg src h
    by_cases h : ∃ u, e = f u
    · obtain ⟨u,rfl⟩ := h
      simp only [red,hinj.eq_iff,Finset.sum_ite_eq,mem_univ,if_true,le_refl]
    · push Not at h
      simp [red,h]
  · intro v
    simp only [red, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, if_true]
    simp_rw [fun e => hinc e v, hsrc, hdst]
    rw [Finset.sum_add_distrib, sum_pt, q.sum_comp (fun w => pt v w), sum_pt]

end
end OMA.S_mo_488874

namespace OMA.S_mo_488874
open Finset
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

omit [Fintype V] in
lemma degree_as_endpoints (G : Multigraph V E) (c : E → ℕ) (v : V) :
    G.degree c v = ∑ e, (pt v (G.source e) + pt v (G.target e))*c e := by
  apply Finset.sum_congr rfl
  intro e _
  have h := G.no_loops e
  by_cases hs : v = G.source e <;> by_cases ht : v = G.target e <;> 
    simp_all [pt, eq_comm]

/-- Double an irregular graph, joining the two copies at each vertex with enough
parallel edges to fill its degree deficit. -/
abbrev DoubleEdge (G : Multigraph V E) (k : ℕ) :=
  ((Σ e : E, Fin (G.multiplicity e)) × Bool) ⊕
  (Σ v : V, Fin (2*k - G.degree G.multiplicity v))

def doubleSrc (G : Multigraph V E) (k : ℕ) : DoubleEdge G k → V × Bool
  | .inl (⟨e,_⟩,b) => (G.source e,b)
  | .inr ⟨v,_⟩ => (v,false)

def doubleDst (G : Multigraph V E) (k : ℕ) : DoubleEdge G k → V × Bool
  | .inl (⟨e,_⟩,b) => (G.target e,b)
  | .inr ⟨v,_⟩ => (v,true)

lemma double_degree (G : Multigraph V E) (k : ℕ) (c : DoubleEdge G k → ℕ) (v : V) (b : Bool) :
    ∑ e, (pt (v,b) (doubleSrc G k e) + pt (v,b) (doubleDst G k e))*c e =
    G.degree (fun e => ∑ i, c (.inl (⟨e,i⟩,b))) v + ∑ i, c (.inr ⟨v,i⟩) := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_sigma,
    degree_as_endpoints]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases b <;> simp [doubleSrc, doubleDst, pt]
  · have ha (w : V) (i : Fin (2*k - G.degree G.multiplicity w)) :
        (pt (v,b) (doubleSrc G k (.inr ⟨w,i⟩)) + pt (v,b) (doubleDst G k (.inr ⟨w,i⟩))) *
          c (.inr ⟨w,i⟩) = (if w=v then c (.inr ⟨w,i⟩) else 0) := by
      by_cases hw : w=v <;> cases b <;> simp [doubleSrc,doubleDst,pt,hw]
    simp_rw [ha]
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ h
      simp [h]
    · simp

/-- Extract a subgraph of maximum degree at most two whose removal lowers the
maximum degree bound from 2k to 2k−2. -/
theorem even_split_bounds (G : Multigraph V E) {k : ℕ} (hk : 0 < k)
    (hmax : G.maxDegree G.multiplicity ≤ 2*k) :
    ∃ x y : E → ℕ, (∀ e, x e + y e = G.multiplicity e) ∧
      G.maxDegree x ≤ 2 ∧ G.maxDegree y ≤ 2*k-2 := by
  have hv (v : V) : G.degree G.multiplicity v ≤ 2*k := (G.degree_le_max _ _).trans hmax
  have hreg (vb : V × Bool) :
      ∑ e, (pt vb (doubleSrc G k e) + pt vb (doubleDst G k e)) = 2*k := by
    obtain ⟨v,b⟩ := vb
    have h := double_degree G k (fun _ => 1) v b
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    simpa [h] using Nat.add_sub_of_le (hv v)
  obtain ⟨red, hred, htwo⟩ := regular_two_factor (doubleSrc G k) (doubleDst G k) k hk hreg
  let x (e : E) := ∑ i, red (.inl (⟨e,i⟩,false))
  let y (e : E) := G.multiplicity e - x e
  have hle (e : E) : x e ≤ G.multiplicity e := by
    simpa [x] using (Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => hred (.inl (⟨e,i⟩,false))))
  have hadd (e : E) : x e + y e = G.multiplicity e := by dsimp [y]; have := hle e; omega
  have hpoint (v : V) : G.degree x v ≤ 2 ∧ G.degree y v ≤ 2*k-2 := by
    have ht := htwo (v,false)
    rw [double_degree] at ht
    change G.degree x v + _ = 2 at ht
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hred (.inr ⟨v,i⟩))
    simp at h
    have hp := G.degree_add x y hadd v
    have hv' := hv v
    omega
  exact ⟨x,y,hadd, Finset.sup_le (fun v _ => (hpoint v).1), Finset.sup_le (fun v _ => (hpoint v).2)⟩

lemma not_indecomposable_of_bounds (G : Multigraph V E) {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (hab : G.maxDegree G.multiplicity = a+b)
    (x y : E → ℕ) (he : ∀ e, x e + y e = G.multiplicity e)
    (hx : G.maxDegree x ≤ a) (hy : G.maxDegree y ≤ b) : ¬ G.indecomposable := by
  have ht : G.maxDegree G.multiplicity ≤ G.maxDegree x + G.maxDegree y := by
    apply Finset.sup_le
    intro v _
    rw [← G.degree_add x y he v]
    exact Nat.add_le_add (G.degree_le_max _ _) (G.degree_le_max _ _)
  rw [hab] at ht
  have hnon (c : E → ℕ) (hc : 0 < G.maxDegree c) : ∃ e, 0 < c e := by
    by_contra! h
    have hz (e : E) : c e = 0 := by have := h e; omega
    simp [Multigraph.maxDegree,Multigraph.degree,hz] at hc
  intro hi
  have h := hi x y he (hnon x (by omega)) (hnon y (by omega))
  omega

/-- Every loopless multigraph of even maximum degree at least four is decomposable. -/
theorem even_decomposable (G : Multigraph V E) {k : ℕ} (hk : 2 ≤ k)
    (hmax : G.maxDegree G.multiplicity = 2*k) : ¬ G.indecomposable := by
  obtain ⟨x,y,he,hx,hy⟩ := even_split_bounds G (by omega : 0 < k) hmax.le
  exact not_indecomposable_of_bounds G (by decide : 0<2) (by omega : 0 < 2*k-2)
    (by omega) x y he hx hy

end OMA.S_mo_488874

namespace OMA.S_mo_488874
open Finset

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq V] [Fintype K] [DecidableEq K]

/-- Number of vertices carrying a given label. -/
def population (l : V → K) (a : K) := ∑ v, pt a (l v)

/-- Number of edge copies whose arbitrarily recorded direction goes from label a to b. -/
def directedEdges (G : Multigraph V E) (l : V → K) (a b : K) : ℕ :=
  ∑ e, pt a (l (G.source e)) * pt b (l (G.target e)) * G.multiplicity e

/-- Number of crossing edge copies between different labels. An internal edge
contributes twice when both labels agree. -/
def weight (G : Multigraph V E) (l : V → K) (a b : K) : ℕ :=
  directedEdges G l a b + directedEdges G l b a

omit [Fintype V] [DecidableEq V] [Fintype K] in
lemma weight_symm (G : Multigraph V E) (l : V → K) (a b : K) :
    weight G l a b = weight G l b a := Nat.add_comm ..

lemma degree_weight (G : Multigraph V E) (l : V → K) (a : K) :
    ∑ b, weight G l a b = ∑ v, pt a (l v) * G.degree G.multiplicity v := by
  unfold weight directedEdges
  simp_rw [Finset.sum_add_distrib, degree_as_endpoints, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset K)), Finset.sum_comm (s := (univ : Finset K)),
    ← Finset.sum_add_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hl (x : K) : ∑ z, pt z x = 1 := by simp only [pt,Finset.sum_ite_eq,mem_univ,if_true]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hl, one_mul, mul_one]
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  congr 1 <;> simp [pt, mul_ite, ite_mul, Finset.sum_ite_eq]

lemma weight_row_bound (G : Multigraph V E) (l : V → K) (a : K) :
    ∑ b, weight G l a b ≤ G.maxDegree G.multiplicity * population l a := by
  rw [degree_weight, population, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [mul_comm (G.maxDegree _) _]
  exact Nat.mul_le_mul_left _ (G.degree_le_max _ _)

lemma weight_row_exact (G : Multigraph V E) (l : V → K) (a : K) {r : ℕ}
    (h : ∀ v, l v = a → G.degree G.multiplicity v = r) :
    ∑ b, weight G l a b = r * population l a := by
  rw [degree_weight, population, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : l v = a <;> simp [pt,hv,h,mul_comm]

omit [Fintype V] [DecidableEq V] in
lemma weight_total (G : Multigraph V E) (l : V → K) : ∑ a, ∑ b, weight G l a b = 2*G.edges := by
  simp only [weight, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => directedEdges G l b a)]
  have h : ∑ a, ∑ b, directedEdges G l a b = G.edges := by
    unfold directedEdges Multigraph.edges
    conv_lhs =>
      enter [2,a]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    have hl (x : K) : ∑ z, pt z x = 1 := by simp only [pt,Finset.sum_ite_eq,mem_univ,if_true]
    simp only [← Finset.sum_mul, ← Finset.mul_sum, hl, one_mul, mul_one]
  rw [h]
  omega

omit [DecidableEq V] [Fintype K] in
lemma singleton_weight (G : Multigraph V E) (l : V → K) (a : K) (h : population l a = 1) :
    weight G l a a = 0 := by
  classical
  have hp : (univ.filter (fun v => l v=a)).card = 1 := by simpa [population,pt] using h
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hp
  have hu (v) (hv : l v = a) : v=z := by
    have : v ∈ univ.filter (fun w => l w=a) := Finset.mem_filter.mpr ⟨mem_univ _,hv⟩
    simpa [hz] using this
  have hw : directedEdges G l a a = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases hs : l (G.source e) = a <;> by_cases ht : l (G.target e) = a <;> simp [pt,hs,ht]
    exact ((G.no_loops e) ((hu _ hs).trans (hu _ ht).symm)).elim
  simp [weight,hw]

end OMA.S_mo_488874

namespace OMA.S_mo_488874
open Finset

abbrev Part (I : Type*) := Option Bool ⊕ I
abbrev leftPart {I : Type*} : Part I := .inl (some false)
abbrev rightPart {I : Type*} : Part I := .inl (some true)
abbrev restPart {I : Type*} : Part I := .inl none
abbrev block {I : Type*} (i : I) : Part I := .inr i

lemma part_sum {I : Type*} [Fintype I] (f : Part I → ℕ) :
    ∑ p, f p = f leftPart + f rightPart + f restPart + ∑ i, f (block i) := by
  rw [Fintype.sum_sum_type,Fintype.sum_option]
  simp [leftPart,rightPart,restPart,block,add_comm,add_assoc]

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The deficient components of the Lovász upper-bound factor theorem, with two
distinguished vertex sets and one label for vertices in all remaining components.
Internal edges are counted twice by weight. -/
structure FactorCertificate (G : Multigraph V E) (r : ℕ) (I : Type*) [Fintype I] [DecidableEq I] where
  label : V → Part I
  nonempty_block : ∀ i, 0 < population label (block i)
  saturated : ∀ i v, label v = block i → G.degree G.multiplicity v = r
  no_rest : ∀ i, weight G label (block i) restPart = 0
  no_cross : ∀ i j, j ≠ i → weight G label (block i) (block j) = 0
  odd_right : ∀ i, Odd (weight G label (block i) rightPart)
  deficient : 2 * population label leftPart + (r-2) * population label rightPart
    < weight G label leftPart rightPart + Fintype.card I

variable {I : Type*} [Fintype I] [DecidableEq I] {G : Multigraph V E} {r : ℕ}

theorem certificate_lower_bound (hr : 3 ≤ r) (hmax : G.maxDegree G.multiplicity = r)
    (C : FactorCertificate G r I) : (r-1)*(3*r+1) ≤ 2*G.edges := by
  let w := weight G C.label
  let n := population C.label
  have hcomm (a b) : w a b = w b a := weight_symm .. 
  have hleft : w leftPart rightPart + ∑ i, w (block i) leftPart ≤ r*n leftPart := by
    have h := weight_row_bound G C.label leftPart
    change (∑ b, w leftPart b) ≤ _ at h
    rw [part_sum, hmax] at h
    change _ ≤ r*n leftPart at h
    simp_rw [fun i => hcomm (block i) leftPart]
    omega
  have hright : w leftPart rightPart + ∑ i, w (block i) rightPart ≤ r*n rightPart := by
    have h := weight_row_bound G C.label rightPart
    change (∑ b, w rightPart b) ≤ _ at h
    rw [part_sum, hmax] at h
    change _ ≤ r*n rightPart at h
    simp_rw [fun i => hcomm (block i) rightPart]
    rw [hcomm leftPart rightPart]
    omega
  have hsum (i : I) : ∑ p, w (block i) p = r*n (block i) :=
    weight_row_exact G C.label (block i) (C.saturated i)
  have hlocal (i) : w (block i) leftPart + w (block i) rightPart + w (block i) (block i)
      = r*n (block i) := by
    have h := hsum i
    have off (j : I) (hne : j ≠ i) : w (block i) (block j) = 0 := C.no_cross i j hne
    rw [part_sum, Finset.sum_eq_single i (fun j _ hji => off j hji) (by simp)] at h
    have h0 : w (block i) restPart = 0 := C.no_rest i
    omega
  have hsing (i) (hi : n (block i) = 1) :
      w (block i) leftPart + w (block i) rightPart = r := by
    have h := hlocal i
    have hh := singleton_weight G C.label (block i) hi
    change w (block i) (block i) = 0 at hh
    rw [hi, Nat.mul_one, hh, Nat.add_zero] at h
    exact h
  have hpair (i) (hi : n (block i) = 2) : 1 ≤ w (block i) leftPart := by
    have h := hlocal i
    obtain ⟨m,hm⟩ := C.odd_right i
    change w (block i) rightPart = _ at hm
    have hdiag : w (block i) (block i) = 2*directedEdges G C.label (block i) (block i) := by
      dsimp [w,weight]; omega
    rw [hi] at h
    omega
  have hrpos (i) : 1 ≤ w (block i) rightPart := by
    obtain ⟨m,hm⟩ := C.odd_right i
    change w (block i) rightPart = _ at hm
    omega
  let counts : BarrierCounts I := {
    degree := r, degree_ge := by exact_mod_cast hr,
    leftCount := n leftPart, rightCount := n rightPart, between := w leftPart rightPart,
    vertices := fun i => n (block i), leftEdges := fun i => w (block i) leftPart,
    rightEdges := fun i => w (block i) rightPart,
    nonempty := fun i => by exact_mod_cast C.nonempty_block i,
    left_nonneg := fun _ => by positivity,
    right_pos := fun i => by exact_mod_cast hrpos i,
    singleton_boundary := fun i hi => by exact_mod_cast hsing i (by exact_mod_cast hi),
    pair_left_edge := fun i hi => by exact_mod_cast hpair i (by exact_mod_cast hi),
    left_capacity := by exact_mod_cast hleft, right_capacity := by exact_mod_cast hright,
    obstruction := by
      have h := C.deficient
      change 2*n leftPart + (r-2)*n rightPart < w leftPart rightPart + _ at h
      have hcast : ((r-2 : ℕ) : ℤ) = (r : ℤ)-2 := by exact_mod_cast Nat.cast_sub (R := ℤ) (by omega : 2 ≤ r)
      rw [←hcast]
      exact_mod_cast h }
  have hhand : r * (∑ i, n (block i)) + (∑ i, w (block i) rightPart) ≤ 2 * G.edges := by
    have h := weight_total G C.label
    change (∑ a, ∑ b, w a b) = _ at h
    rw [part_sum, part_sum (fun b => w rightPart b)] at h
    simp_rw [hsum] at h
    rw [← Finset.mul_sum] at h
    simp_rw [fun i => hcomm (block i) rightPart]
    omega
  have h := degree_sum_lower_bound counts (G.edges : ℤ) (by
    dsimp [counts]
    exact_mod_cast hhand)
  dsimp [counts] at h
  have hcast : ((r-1 : ℕ) : ℤ) = (r : ℤ)-1 := by exact_mod_cast Nat.cast_sub (R := ℤ) (by omega : 1 ≤ r)
  rw [←hcast] at h
  exact_mod_cast h

end OMA.S_mo_488874

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!
# Auxiliary results on connected components for the f-factor theorem

* `FFactor.oddComponents_ncard_eq_of_label`: counting odd components via a labelling whose
  fibres are exactly the components.
* `FFactor.ncard_oddComponents_deleteVerts_le`: removing a vertex `x` from a vertex set `U`
  whose neighbours outside `U` meet at most two components of `G - U` decreases the number of
  odd components by at most one.
-/



open Finset SimpleGraph

namespace OMA.S_mo_488874.TutteLib

section Label

variable {X L : Type*} (H : SimpleGraph X) (φ : X → L)

theorem label_eq_of_reachable (h1 : ∀ x y, H.Adj x y → φ x = φ y) {x y : X}
    (h : H.Reachable x y) : φ x = φ y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (h1 _ _ ha).trans ih

open Classical in
theorem oddComponents_ncard_eq_of_label [Fintype X]
    (h1 : ∀ x y, H.Adj x y → φ x = φ y) (h2 : ∀ x y, φ x = φ y → H.Reachable x y) :
    H.oddComponents.ncard = #{l ∈ univ.image φ | Odd #{x | φ x = l}} := by
  let ψ : H.ConnectedComponent → L :=
    ConnectedComponent.lift φ (fun v w p _ => label_eq_of_reachable H φ h1 ⟨p⟩)
  have hψ : ∀ x, ψ (H.connectedComponentMk x) = φ x := fun x => rfl
  have hinj : Function.Injective ψ := by
    intro c d hcd
    induction c using ConnectedComponent.ind with | h x => ?_
    induction d using ConnectedComponent.ind with | h y => ?_
    exact ConnectedComponent.sound (h2 x y hcd)
  have hsupp : ∀ c : H.ConnectedComponent, c.supp = {x | φ x = ψ c} := by
    intro c
    induction c using ConnectedComponent.ind with | h y => ?_
    ext x
    simp only [ConnectedComponent.mem_supp_iff, Set.mem_ofPred_eq, hψ]
    constructor
    · intro h; rw [← hψ, ← hψ, h]
    · intro h; exact ConnectedComponent.sound (h2 x y h)
  have key : ∀ l, ({x | φ x = l} : Set X).ncard = #{x | φ x = l} := fun l => by
    rw [← Set.ncard_coe_finset]; simp
  rw [← Set.ncard_image_of_injective _ hinj, ← Set.ncard_coe_finset]
  congr 1
  ext l
  simp only [Set.mem_image, Set.mem_ofPred_eq, coe_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨c, hc, rfl⟩
    induction c using ConnectedComponent.ind with | h y => ?_
    refine ⟨⟨y, rfl⟩, ?_⟩
    rw [hsupp, key] at hc
    exact hc
  · rintro ⟨⟨y, rfl⟩, hodd⟩
    refine ⟨H.connectedComponentMk y, ?_, rfl⟩
    show Odd (H.connectedComponentMk y).supp.ncard
    rw [hsupp, key]
    exact hodd

end Label

section Removal

variable {W : Type*} (Γ : SimpleGraph W)

/-- The graph `Γ - U`, as in Mathlib's definition of a Tutte violator. -/
abbrev del (U : Set W) : SimpleGraph ((⊤ : Γ.Subgraph).deleteVerts U).verts :=
  ((⊤ : Γ.Subgraph).deleteVerts U).coe

@[simp] theorem mem_del_verts {U : Set W} {a : W} :
    a ∈ ((⊤ : Γ.Subgraph).deleteVerts U).verts ↔ a ∉ U := by simp

@[simp] theorem del_adj {U : Set W} {a b : ((⊤ : Γ.Subgraph).deleteVerts U).verts} :
    (del Γ U).Adj a b ↔ Γ.Adj a b := by
  constructor
  · intro h; exact Subgraph.coe_adj_sub _ _ _ h
  · intro h; exact Subgraph.deleteVerts_adj.mpr ⟨trivial, a.2.2, trivial, b.2.2, h⟩

/-- The inclusion `Γ - U → Γ - (U \ {x})`. -/
def delIncl (U : Set W) (x : W) : del Γ U →g del Γ (U \ {x}) where
  toFun a := ⟨a.1, ⟨trivial, fun h => a.2.2 h.1⟩⟩
  map_rel' h := (del_adj Γ (U := U \ {x})).mpr ((del_adj Γ (U := U)).mp h)

theorem delIncl_injective (U : Set W) (x : W) : Function.Injective (delIncl Γ U x) := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

theorem ncard_oddComponents_del_le [Finite W] (U : Set W) (x : W) (hx : x ∈ U)
    (h3 : ∀ a b c : ((⊤ : Γ.Subgraph).deleteVerts U).verts, Γ.Adj x a → Γ.Adj x b →
      Γ.Adj x c → (del Γ U).Reachable a b ∨ (del Γ U).Reachable a c ∨
        (del Γ U).Reachable b c) :
    (del Γ U).oddComponents.ncard ≤ (del Γ (U \ {x})).oddComponents.ncard + 1 := by
  classical
  set H := del Γ U
  set H' := del Γ (U \ {x})
  let ι := delIncl Γ U x
  let A : Set H.ConnectedComponent :=
    {c | ∃ a : ((⊤ : Γ.Subgraph).deleteVerts U).verts, c = H.connectedComponentMk a ∧ Γ.Adj x a}
  let B : Set H.ConnectedComponent := {c | c ∉ A ∧ Odd c.supp.ncard}
  -- `A` has at most two elements
  have hA : A.ncard ≤ 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2, c3, h1, h2, h3', h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).mp hcon
    obtain ⟨a1, rfl, ha1⟩ := h1
    obtain ⟨a2, rfl, ha2⟩ := h2
    obtain ⟨a3, rfl, ha3⟩ := h3'
    rcases h3 a1 a2 a3 ha1 ha2 ha3 with h | h | h
    · exact h12 (ConnectedComponent.sound h)
    · exact h13 (ConnectedComponent.sound h)
    · exact h23 (ConnectedComponent.sound h)
  have hsub : H.oddComponents ⊆ B ∪ A := by
    intro c hc
    by_cases hcA : c ∈ A
    · exact Or.inr hcA
    · exact Or.inl ⟨hcA, hc⟩
  have hodd1 : H.oddComponents.ncard ≤ B.ncard + 2 :=
    (Set.ncard_le_ncard hsub).trans ((Set.ncard_union_le _ _).trans (by omega))
  -- the label on `H'`
  let ψ : ((⊤ : Γ.Subgraph).deleteVerts (U \ {x})).verts → Option H.ConnectedComponent :=
    fun y => if h : y.1 ∉ U then
      (if H.connectedComponentMk ⟨y.1, by simpa using h⟩ ∈ A then none
        else some (H.connectedComponentMk ⟨y.1, by simpa using h⟩)) else none
  have hψι : ∀ a, H.connectedComponentMk a ∉ A → ψ (ι a) = some (H.connectedComponentMk a) := by
    intro a ha
    have h' : (a : W) ∉ U := a.2.2
    have e : ψ (ι a) = if H.connectedComponentMk a ∈ A then none
        else some (H.connectedComponentMk a) := dif_pos h'
    rw [e, if_neg ha]
  have hψ1 : ∀ y z, H'.Adj y z → ψ y = ψ z := by
    have key : ∀ y z : ((⊤ : Γ.Subgraph).deleteVerts (U \ {x})).verts, H'.Adj y z →
        (y : W) ∈ U → ψ y = ψ z := by
      intro y z hyz hy
      have hyx : (y : W) = x := by have := y.2; simp_all
      have hy' : ψ y = none := by simp [ψ, hy]
      rw [hy']
      by_cases hz : (z : W) ∈ U
      · simp [ψ, hz]
      · have hmem : H.connectedComponentMk ⟨z.1, by simpa using hz⟩ ∈ A :=
          ⟨⟨z.1, by simpa using hz⟩, rfl, hyx ▸ (del_adj Γ (U := U \ {x})).mp hyz⟩
        simp [ψ, hz, hmem]
    intro y z hyz
    by_cases hy : (y : W) ∈ U
    · exact key y z hyz hy
    by_cases hz : (z : W) ∈ U
    · exact (key z y hyz.symm hz).symm
    have hc : H.connectedComponentMk ⟨y.1, by simpa using hy⟩ =
        H.connectedComponentMk ⟨z.1, by simpa using hz⟩ :=
      ConnectedComponent.connectedComponentMk_eq_of_adj
        ((del_adj Γ (U := U)).mpr ((del_adj Γ (U := U \ {x})).mp hyz))
    simp only [ψ, hy, hz, not_false_eq_true, dite_true, hc]
  have hBle : B.ncard ≤ H'.oddComponents.ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun c => c.map ι)
    · intro c hc
      obtain ⟨hcA, hcodd⟩ := hc
      induction c using ConnectedComponent.ind with | h a => ?_
      change Odd (H'.connectedComponentMk (ι a)).supp.ncard
      have hsupp : (H'.connectedComponentMk (ι a)).supp = ι '' (H.connectedComponentMk a).supp := by
        ext z
        simp only [ConnectedComponent.mem_supp_iff, Set.mem_image]
        constructor
        · intro hz
          have hzψ : ψ z = some (H.connectedComponentMk a) := by
            rw [← hψι a hcA]
            exact label_eq_of_reachable H' ψ hψ1 (ConnectedComponent.exact hz)
          have hzU : (z : W) ∉ U := by
            intro h; simp [ψ, h] at hzψ
          refine ⟨⟨z.1, by simpa using hzU⟩, ?_, rfl⟩
          simp only [ψ, hzU, not_false_eq_true, dite_true] at hzψ
          split_ifs at hzψ
          exact Option.some_injective _ hzψ
        · rintro ⟨b, hb, rfl⟩
          rw [← ConnectedComponent.map_mk, ← ConnectedComponent.map_mk, hb]
      rw [hsupp, Set.ncard_image_of_injective _ (delIncl_injective Γ U x)]
      exact hcodd
    · intro c hc d hd hcd
      induction c using ConnectedComponent.ind with | h a => ?_
      induction d using ConnectedComponent.ind with | h b => ?_
      have hr : H'.Reachable (ι a) (ι b) := by
        apply ConnectedComponent.exact
        exact hcd
      have := label_eq_of_reachable H' ψ hψ1 hr
      rw [hψι a hc.1, hψι b hd.1] at this
      exact Option.some_injective _ this
  -- parity
  have hcard : Nat.card ((⊤ : Γ.Subgraph).deleteVerts (U \ {x})).verts =
      Nat.card ((⊤ : Γ.Subgraph).deleteVerts U).verts + 1 := by
    simp only [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts, Subgraph.verts_top]
    rw [show Set.univ \ (U \ {x}) = insert x (Set.univ \ U) by
      ext y; by_cases hy : y = x <;> simp [hy, hx]]
    rw [Set.ncard_insert_of_notMem (by simp [hx])]
  have hp1 := (odd_ncard_oddComponents H)
  have hp2 := (odd_ncard_oddComponents H')
  rw [hcard] at hp2
  simp only [Nat.odd_iff] at hp1 hp2
  have hpar : H'.oddComponents.ncard % 2 ≠ H.oddComponents.ncard % 2 := by
    omega
  omega

/-- The neighbours of `x` outside `U` meet at most two components of `Γ - U`. -/
def TwoComp (U : Set W) (x : W) : Prop :=
  ∀ a b c : ((⊤ : Γ.Subgraph).deleteVerts U).verts, Γ.Adj x a → Γ.Adj x b →
      Γ.Adj x c → (del Γ U).Reachable a b ∨ (del Γ U).Reachable a c ∨
        (del Γ U).Reachable b c

/-- There is a Tutte violator none of whose vertices satisfies `TwoComp`. -/
theorem exists_min_violator [Finite W] (h : ∃ U, Γ.IsTutteViolator U) :
    ∃ U, Γ.IsTutteViolator U ∧ ∀ x ∈ U, ¬ TwoComp Γ U x := by
  classical
  have hex : ∃ n, ∃ U, U.ncard = n ∧ Γ.IsTutteViolator U := by
    obtain ⟨U, hU⟩ := h; exact ⟨_, U, rfl, hU⟩
  obtain ⟨U, hUn, hU⟩ := Nat.find_spec hex
  refine ⟨U, hU, fun x hx htwo => ?_⟩
  have hle := ncard_oddComponents_del_le Γ U x hx htwo
  have hcard : (U \ {x}).ncard + 1 = U.ncard := Set.ncard_sdiff_singleton_add_one hx
  have hviol : Γ.IsTutteViolator (U \ {x}) := by
    unfold IsTutteViolator at hU ⊢
    change U.ncard < (del Γ U).oddComponents.ncard at hU
    change (U \ {x}).ncard < (del Γ (U \ {x})).oddComponents.ncard
    omega
  have := Nat.find_min' hex ⟨U \ {x}, rfl, hviol⟩
  omega

end Removal

end OMA.S_mo_488874.TutteLib

namespace OMA.S_mo_488874
open Finset SimpleGraph
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

abbrev Copy (G : Multigraph V E) := Σ e : E, Fin (G.multiplicity e)
abbrev Slack (G : Multigraph V E) (r : ℕ) := Σ v : V, Fin (r-G.degree G.multiplicity v)
abbrev Port (G : Multigraph V E) (r : ℕ) := (Copy G × Bool) ⊕ Slack G r
abbrev Inner (V : Type*) (r : ℕ) := V × Fin (r-2)
abbrev SplitNode (G : Multigraph V E) (r : ℕ) := Port G r ⊕ Inner V r

def endpoint (G : Multigraph V E) (e : Copy G) (b : Bool) : V :=
  if b then G.target e.1 else G.source e.1

def owner (G : Multigraph V E) (r : ℕ) : Port G r → V
  | .inl (e,b) => endpoint G e b
  | .inr z => z.1

def bundle (G : Multigraph V E) (r : ℕ) : Port G r → Option (Copy G)
  | .inl (e,_) => some e
  | .inr _ => none

def splitAdj (G : Multigraph V E) (r : ℕ) : SplitNode G r → SplitNode G r → Prop
  | .inl p, .inl q => p ≠ q ∧ bundle G r p = bundle G r q
  | .inl p, .inr u => owner G r p = u.1
  | .inr u, .inl p => owner G r p = u.1
  | .inr _, .inr _ => False

def splitGadget (G : Multigraph V E) (r : ℕ) : SimpleGraph (SplitNode G r) where
  Adj := splitAdj G r
  symm := by
    constructor
    rintro (p|i) (q|j) h
    · exact ⟨h.1.symm,h.2.symm⟩
    · exact h
    · exact h
    · exact h
  loopless := by constructor; rintro (p|i) h; exacts [h.1 rfl,h]

omit [Fintype V] in
lemma real_port_card (G : Multigraph V E) (v : V) :
    #{p : Copy G × Bool | endpoint G p.1 p.2 = v} = G.degree G.multiplicity v := by
  classical
  rw [card_filter, Fintype.sum_prod_type, Fintype.sum_sigma, degree_as_endpoints]
  apply sum_congr rfl
  intro e _
  simp_rw [Fintype.sum_bool]
  simp only [endpoint, Bool.false_eq_true, if_false, if_true, pt, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  simp only [Nat.cast_id]
  ring

lemma owner_card (G : Multigraph V E) {r : ℕ} (hmax : G.maxDegree G.multiplicity ≤ r) (v : V) :
    #{p : Port G r | owner G r p = v} = r := by
  classical
  rw [card_filter, Fintype.sum_sum_type]
  have hreal := real_port_card G v
  rw [card_filter] at hreal
  change (∑ p : Copy G × Bool, if endpoint G p.1 p.2 = v then 1 else 0) + _ = r
  rw [hreal, Fintype.sum_sigma]
  have h := (G.degree_le_max _ v).trans hmax
  rw [Finset.sum_eq_single v]
  · simp [owner, Nat.add_sub_of_le h]
  · intro w _ hne
    simp [owner,hne]
  · simp

end OMA.S_mo_488874

namespace OMA.S_mo_488874.Normal
open SimpleGraph TutteLib
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
omit [Fintype V]
variable {G : Multigraph V E} {r : ℕ} {U : Set (SplitNode G r)}

abbrev Fiber (G : Multigraph V E) (r : ℕ) (U : Set (SplitNode G r)) :=
  ((⊤ : (splitGadget G r).Subgraph).deleteVerts U).verts

abbrev Core (G : Multigraph V E) (r : ℕ) (U : Set (SplitNode G r)) :=
  del (splitGadget G r) U

def survivor {z : SplitNode G r} (h : z ∉ U) : Fiber G r U := ⟨z,(mem_del_verts _).mpr h⟩

lemma survived (z : Fiber G r U) : z.val ∉ U := (mem_del_verts _).mp z.prop

abbrev Minimal (G : Multigraph V E) (r : ℕ) (U : Set (SplitNode G r)) :=
  ∀ x ∈ U, ¬TwoComp (splitGadget G r) U x

lemma inner_uniform (hmin : Minimal G r U) {v : V} {i j : Fin (r-2)}
    (hi : (.inr (v,i) : SplitNode G r) ∈ U) : (.inr (v,j) : SplitNode G r) ∈ U := by
  by_contra hj
  apply hmin _ hi
  intro a b c ha hb hc
  let y := survivor hj
  have key (a : Fiber G r U) (ha : (splitGadget G r).Adj (.inr (v,i)) a) :
      (Core G r U).Reachable a y := by
    rcases a with ⟨a|q,haU⟩
    · exact Adj.reachable ((del_adj _).mpr ha)
    · exact False.elim ha
  exact Or.inl ((key a ha).trans (key b hb).symm)

def T (G : Multigraph V E) (r : ℕ) (U : Set (SplitNode G r)) (v : V) : Prop :=
  ∀ i : Fin (r-2), (.inr (v,i) : SplitNode G r) ∈ U

def S (G : Multigraph V E) (r : ℕ) (U : Set (SplitNode G r)) (v : V) : Prop :=
  ¬T G r U v ∧ ∀ p : Port G r, owner G r p = v → (.inl p : SplitNode G r) ∈ U

def W (G : Multigraph V E) (r : ℕ) (U : Set (SplitNode G r)) (v : V) : Prop :=
  ¬T G r U v ∧ ¬S G r U v

lemma inner_survives (hmin : Minimal G r U) {v : V} (hv : ¬T G r U v) (i : Fin (r-2)) :
    (.inr (v,i) : SplitNode G r) ∉ U := fun hi => hv (fun _ => inner_uniform hmin hi)

lemma external_reach {p q : Port G r} (hp : (.inl p : SplitNode G r) ∉ U)
    (hq : (.inl q : SplitNode G r) ∉ U) (h : bundle G r p = bundle G r q) :
    (Core G r U).Reachable (survivor hp) (survivor hq) := by
  by_cases heq : p=q
  · subst q
    exact Reachable.refl _
  · exact Adj.reachable ((del_adj _).mpr ⟨heq,h⟩)

lemma t_ports (hmin : Minimal G r U) {p : Port G r} (ht : T G r U (owner G r p)) :
    (.inl p : SplitNode G r) ∉ U := by
  intro hp
  apply hmin _ hp
  intro a b c ha hb hc
  left
  rcases a with ⟨a|⟨v,i⟩,haU⟩ <;> rcases b with ⟨b|⟨w,j⟩,hbU⟩
  · exact external_reach ((mem_del_verts _).mp haU) ((mem_del_verts _).mp hbU) (ha.2.symm.trans hb.2)
  · have he : owner G r p = w := hb
    exact False.elim (((mem_del_verts _).mp hbU) (he ▸ ht j))
  · have he : owner G r p = v := ha
    exact False.elim (((mem_del_verts _).mp haU) (he ▸ ht i))
  · have he : owner G r p = v := ha
    exact False.elim (((mem_del_verts _).mp haU) (he ▸ ht i))

lemma w_ports (hmin : Minimal G r U) {p : Port G r} (hw : W G r U (owner G r p)) :
    (.inl p : SplitNode G r) ∉ U := by
  intro hp
  have hn : ¬∀ t : Port G r, owner G r t = owner G r p → (.inl t : SplitNode G r) ∈ U :=
    fun h => hw.2 ⟨hw.1,h⟩
  push Not at hn
  obtain ⟨t,ht,htU⟩ := hn
  apply hmin _ hp
  let t₀ : Fiber G r U := survivor htU
  let ext (a : Fiber G r U) : Prop := ∃ q : Port G r, a.val = .inl q ∧ bundle G r q = bundle G r p
  have ext_conn {a b : Fiber G r U} (ha : ext a) (hb : ext b) : (Core G r U).Reachable a b := by
    obtain ⟨q,hq,hqp⟩ := ha
    obtain ⟨s,hs,hsp⟩ := hb
    have ha' : (.inl q : SplitNode G r) ∉ U := hq ▸ survived a
    have hb' : (.inl s : SplitNode G r) ∉ U := hs ▸ survived b
    have ea : a = survivor ha' := Subtype.ext hq
    have eb : b = survivor hb' := Subtype.ext hs
    rw [ea,eb]
    exact external_reach ha' hb' (hqp.trans hsp.symm)
  have key (a : Fiber G r U) (h : (splitGadget G r).Adj (.inl p) a) :
      ext a ∨ (Core G r U).Reachable a t₀ := by
    rcases a with ⟨q|⟨v,i⟩,haU⟩
    · exact Or.inl ⟨q,rfl,h.2.symm⟩
    · exact Or.inr (Adj.reachable ((del_adj _).mpr (ht.trans h)))
  intro a b c ha hb hc
  rcases key a ha with ha|ha <;> rcases key b hb with hb|hb <;> rcases key c hc with hc|hc <;>
    first
    | exact Or.inl (ext_conn ha hb)
    | exact Or.inr (Or.inl (ext_conn ha hc))
    | exact Or.inr (Or.inr (ext_conn hb hc))
    | exact Or.inl (ha.trans hb.symm)
    | exact Or.inr (Or.inl (ha.trans hc.symm))
    | exact Or.inr (Or.inr (hb.trans hc.symm))

end OMA.S_mo_488874.Normal

namespace OMA.S_mo_488874.Normal
open SimpleGraph TutteLib Finset
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
omit [Fintype V]
variable {G : Multigraph V E} {r : ℕ} {U : Set (SplitNode G r)}

abbrev Component (G : Multigraph V E) (r : ℕ) (U : Set (SplitNode G r)) :=
  (Core G r U).ConnectedComponent

def Lives (c : Component G r U) (z : SplitNode G r) : Prop :=
  ∃ h : z ∉ U, (Core G r U).connectedComponentMk (survivor h) = c

lemma lives_of_reach {z w : SplitNode G r} (hz : z∉U) (hw : w∉U)
    (h : (Core G r U).Reachable (survivor hz) (survivor hw)) (c : Component G r U) :
    Lives c z ↔ Lives c w := by
  have he := ConnectedComponent.sound h
  constructor
  · rintro ⟨_,hc⟩
    exact ⟨hw,he.symm.trans hc⟩
  · rintro ⟨_,hc⟩
    exact ⟨hz,he.trans hc⟩

omit [DecidableEq V] in
lemma transport_closed {H : SimpleGraph V} {P : V → Prop}
    (h : ∀ a b, H.Adj a b → P a → P b) {a b : V}
    (hc : H.connectedComponentMk a = H.connectedComponentMk b) (ha : P a) : P b := by
  obtain ⟨w⟩ := ConnectedComponent.exact hc
  clear hc
  induction w with
  | nil => exact ha
  | cons hadj _ ih => exact ih (h _ _ hadj ha)

noncomputable def home (hr : 3≤r) (hmin : Minimal G r U) (v : V) :
    Option (Component G r U) := by
  classical
  exact if hw : W G r U v then some ((Core G r U).connectedComponentMk
      (survivor (inner_survives hmin hw.1 ⟨0,by omega⟩))) else none

lemma home_spec (hr : 3≤r) (hmin : Minimal G r U) {v : V} {c : Component G r U}
    (h : home hr hmin v = some c) : W G r U v := by
  classical
  by_contra hn
  simp [home,hn] at h

lemma w_port_lives (hr : 3≤r) (hmin : Minimal G r U) {p : Port G r}
    (hw : W G r U (owner G r p)) (c : Component G r U) :
    Lives c (.inl p) ↔ home hr hmin (owner G r p) = some c := by
  classical
  let j : Fin (r-2) := ⟨0,by omega⟩
  have hi := inner_survives hmin hw.1 j
  have hp := w_ports hmin hw
  have ha : (Core G r U).Adj (survivor hp) (survivor hi) := (del_adj _).mpr rfl
  rw [lives_of_reach hp hi ha.reachable c]
  simp only [home, dif_pos hw, Option.some.injEq]
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨hi,h⟩⟩

lemma w_inner_lives (hr : 3≤r) (hmin : Minimal G r U) {v : V} (hw : W G r U v)
    (i : Fin (r-2)) (c : Component G r U) :
    Lives c (.inr (v,i)) ↔ home hr hmin v = some c := by
  have h : ¬∀ p : Port G r, owner G r p = v → (.inl p : SplitNode G r) ∈ U :=
    fun h => hw.2 ⟨hw.1,h⟩
  push Not at h
  obtain ⟨p,hp,hpU⟩ := h
  have hi := inner_survives hmin hw.1 i
  have ha : (Core G r U).Adj (survivor hi) (survivor hpU) := (del_adj _).mpr hp
  rw [lives_of_reach hi hpU ha.reachable c, w_port_lives hr hmin (hp ▸ hw),hp]

lemma w_link (hr : 3≤r) (hmin : Minimal G r U) {p q : Port G r}
    (hp : W G r U (owner G r p)) (hq : W G r U (owner G r q)) (he : bundle G r p = bundle G r q) :
    home hr hmin (owner G r p) = home hr hmin (owner G r q) := by
  classical
  have hp' := w_ports hmin hp
  have hq' := w_ports hmin hq
  let c := (Core G r U).connectedComponentMk (survivor hp')
  have ha : Lives c (.inl p) := ⟨hp',rfl⟩
  have hb := (lives_of_reach hp' hq' (external_reach hp' hq' he) c).mp ha
  exact ((w_port_lives hr hmin hp c).mp ha).trans ((w_port_lives hr hmin hq c).mp hb).symm

def real (G : Multigraph V E) (r : ℕ) (e : Copy G) (b : Bool) : SplitNode G r :=
  .inl (.inl (e,b))

lemma real_survives_iff (hmin : Minimal G r U) (e : Copy G) (b : Bool) :
    real G r e b ∉ U ↔ ¬S G r U (endpoint G e b) := by
  constructor
  · intro hn hs
    exact hn (hs.2 (.inl (e,b)) rfl)
  · intro hs
    by_cases ht : T G r U (endpoint G e b)
    · exact t_ports hmin ht
    · exact w_ports hmin ⟨ht,hs⟩

lemma real_flip_lives (hmin : Minimal G r U) {e : Copy G} {b : Bool}
    (h : ¬S G r U (endpoint G e b)) (h' : ¬S G r U (endpoint G e (!b))) (c : Component G r U) :
    Lives c (real G r e b) ↔ Lives c (real G r e (!b)) := by
  have hp := (real_survives_iff hmin e b).2 h
  have hq := (real_survives_iff hmin e (!b)).2 h'
  exact lives_of_reach hp hq (external_reach hp hq rfl) c

lemma tt_not_odd (hmin : Minimal G r U) {e : Copy G}
    (ht : ∀ b, T G r U (endpoint G e b)) {c : Component G r U}
    {b : Bool} (hc : Lives c (real G r e b)) : c ∉ (Core G r U).oddComponents := by
  classical
  have hu (b : Bool) : real G r e b ∉ U := t_ports hmin (ht b)
  let port (b : Bool) : Fiber G r U := survivor (hu b)
  have hcc (i : Bool) : (Core G r U).connectedComponentMk (port i) = c := by
    obtain ⟨_,he⟩ := hc
    exact (ConnectedComponent.sound (external_reach (hu i) (hu b) rfl)).trans he
  let P (a : Fiber G r U) := ∃ b, a = port b
  have hclosed (a z : Fiber G r U) (h : (Core G r U).Adj a z) (ha : P a) : P z := by
    obtain ⟨i,rfl⟩ := ha
    have had := (del_adj _).mp h
    rcases z with ⟨((⟨f,j⟩|s)|⟨v,k⟩),hz⟩
    · have he : some e = some f := had.2
      cases Option.some.inj he
      exact ⟨j,Subtype.ext rfl⟩
    · have he : some e = none := had.2
      contradiction
    · have he : endpoint G e i = v := had
      exact False.elim (((mem_del_verts _).mp hz) (he ▸ ht i k))
  have hs : c.supp = {port false,port true} := by
    ext z
    change (Core G r U).connectedComponentMk z = c ↔ _
    constructor
    · intro hz
      have hz' := transport_closed (P:=P) hclosed ((hcc false).trans hz.symm) ⟨false,rfl⟩
      rcases hz' with ⟨(_|_),rfl⟩ <;> simp
    · intro hz
      rcases Set.mem_insert_iff.mp hz with rfl|hz
      · exact hcc _
      · rw [Set.mem_singleton_iff.mp hz]
        exact hcc _
  have hne : port false ≠ port true := by
    intro he
    have he' := congrArg Subtype.val he
    change real G r e false = real G r e true at he'
    simp [real] at he'
  change ¬Odd c.supp.ncard
  rw [hs,Set.ncard_pair hne]
  decide

end OMA.S_mo_488874.Normal

namespace OMA.S_mo_488874.Normal
open SimpleGraph Finset
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable {G : Multigraph V E} {r : ℕ} {U : Set (SplitNode G r)}

structure Good (c : Component G r U) : Prop where
  odd : c ∈ (Core G r U).oddComponents
  no_slack : ∀ z : Slack G r, ¬Lives c (.inl (.inr z))
  no_inner : ∀ v (i : Fin (r-2)), S G r U v → ¬Lives c (.inr (v,i))
  no_crossing : ∀ (e : Copy G) (b : Bool), T G r U (endpoint G e b) →
    S G r U (endpoint G e (!b)) → ¬Lives c (real G r e b)

abbrev Index (G : Multigraph V E) (r : ℕ) (U : Set (SplitNode G r)) :=
  {c : Component G r U // Good c}

noncomputable def tag (hr : 3≤r) (hm : Minimal G r U) (v : V) : Part (Index G r U) := by
  classical
  exact if h : ∃ i : Index G r U, home hr hm v = some i.1 then block h.choose
    else if S G r U v then leftPart else if T G r U v then rightPart else restPart

lemma tag_block (hr : 3≤r) (hm : Minimal G r U) (v : V) (i : Index G r U) :
    tag hr hm v = block i ↔ home hr hm v = some i.1 := by
  classical
  by_cases h : ∃ i : Index G r U, home hr hm v = some i.1
  · simp only [tag,dif_pos h,block,Sum.inr.injEq]
    exact ⟨fun eq => eq ▸ h.choose_spec,
      fun he => Subtype.ext (Option.some.inj (h.choose_spec.symm.trans he))⟩
  · have hi : home hr hm v ≠ some i.1 := fun hi => h ⟨i,hi⟩
    by_cases hs : S G r U v <;> by_cases ht : T G r U v <;>
      simp [tag,h,hs,ht,hi,leftPart,rightPart,restPart,block]

lemma tag_left (hr : 3≤r) (hm : Minimal G r U) (v : V) :
    tag hr hm v = leftPart ↔ S G r U v := by
  classical
  by_cases h : ∃ i : Index G r U, home hr hm v = some i.1
  · obtain ⟨i,hi⟩ := h
    have hs := (home_spec hr hm hi).2
    rw [(tag_block hr hm v i).2 hi]
    simp [block,leftPart,hs]
  · by_cases hs : S G r U v <;> by_cases ht : T G r U v <;>
      simp [tag,h,hs,ht,leftPart,rightPart,restPart]

lemma tag_right (hr : 3≤r) (hm : Minimal G r U) (v : V) :
    tag hr hm v = rightPart ↔ T G r U v := by
  classical
  by_cases h : ∃ i : Index G r U, home hr hm v = some i.1
  · obtain ⟨i,hi⟩ := h
    have ht := (home_spec hr hm hi).1
    rw [(tag_block hr hm v i).2 hi]
    simp [block,rightPart,ht]
  · by_cases hs : S G r U v
    · simp [tag,h,hs,hs.1,leftPart,rightPart]
    · by_cases ht : T G r U v <;> simp [tag,h,hs,ht,rightPart,restPart]

end OMA.S_mo_488874.Normal

namespace OMA.S_mo_488874.Normal
open SimpleGraph Finset Classical
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable {G : Multigraph V E} {r : ℕ} {U : Set (SplitNode G r)}

lemma live_inner_iff (hr : 3≤r) (hm : Minimal G r U) (i : Index G r U) (v : V) (j : Fin (r-2)) :
    Lives i.val (.inr (v,j)) ↔ tag hr hm v = block i := by
  rw [tag_block]
  by_cases hs : S G r U v
  · exact iff_of_false (i.prop.no_inner v j hs) (fun h => (home_spec hr hm h).2 hs)
  by_cases ht : T G r U v
  · exact iff_of_false (fun ⟨hn,_⟩ => hn (ht j)) (fun h => (home_spec hr hm h).1 ht)
  exact w_inner_lives hr hm ⟨ht,hs⟩ j i.val

lemma live_real_iff (hr : 3≤r) (hm : Minimal G r U) (i : Index G r U) (e : Copy G) (b : Bool) :
    Lives i.val (real G r e b) ↔ tag hr hm (endpoint G e b) = block i ∨
      tag hr hm (endpoint G e b) = rightPart ∧ tag hr hm (endpoint G e (!b)) = block i := by
  rw [tag_block,tag_right,tag_block]
  by_cases ht : T G r U (endpoint G e b)
  · have hh : home hr hm (endpoint G e b) ≠ some i.val := fun h => (home_spec hr hm h).1 ht
    simp only [hh, false_or, ht, true_and]
    have hs := fun h : S G r U (endpoint G e b) => h.1 ht
    by_cases hs' : S G r U (endpoint G e (!b))
    · exact iff_of_false (i.prop.no_crossing e b ht hs') (fun h => (home_spec hr hm h).2 hs')
    by_cases ht' : T G r U (endpoint G e (!b))
    · apply iff_of_false _ (fun h => (home_spec hr hm h).1 ht')
      intro h
      have both (j : Bool) : T G r U (endpoint G e j) := by
        cases b <;> cases j <;> first | exact ht | exact ht'
      exact tt_not_odd hm both h i.prop.odd
    rw [real_flip_lives hm hs hs' i.val]
    exact w_port_lives hr hm (p:=.inl (e,!b)) ⟨ht',hs'⟩ i.val
  simp only [ht, false_and, or_false]
  by_cases hs : S G r U (endpoint G e b)
  · exact iff_of_false (fun ⟨hu,_⟩ => (real_survives_iff hm e b).mp hu hs) (fun h => (home_spec hr hm h).2 hs)
  exact w_port_lives hr hm (p:=.inl (e,b)) ⟨ht,hs⟩ i.val

lemma slack_not_block (hr : 3≤r) (hm : Minimal G r U) (i : Index G r U) (z : Slack G r) :
    tag hr hm z.1 ≠ block i := by
  intro h
  have hh := (tag_block hr hm _ _).1 h
  have hl := (w_port_lives hr hm (p:=.inr z) (home_spec hr hm hh) i.val).2 hh
  exact i.prop.no_slack z hl

lemma block_saturated (hr : 3≤r) (hm : Minimal G r U) (hg : G.maxDegree G.multiplicity ≤ r)
    (i : Index G r U) {v : V} (h : tag hr hm v = block i) : G.degree G.multiplicity v = r := by
  have hd := (G.degree_le_max _ v).trans hg
  by_contra hne
  exact slack_not_block hr hm i ⟨v,⟨0,by omega⟩⟩ h

noncomputable def flag (P : Prop) : ℕ := by classical exact if P then 1 else 0

lemma flag_pt {B : Type*} [DecidableEq B] (a b : B) : flag (b=a) = pt a b := by
  classical
  by_cases h : b=a <;> simp [flag,pt,h]

lemma lives_card (c : Component G r U) :
    c.supp.ncard = ∑ z : SplitNode G r, flag (Lives c z) := by
  classical
  let eqv : c.supp ≃ {z : SplitNode G r // Lives c z} :=
    { toFun := fun x => ⟨x.val.val, ⟨survived x.val,x.prop⟩⟩
      invFun := fun z => ⟨survivor z.prop.choose,z.prop.choose_spec⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_coe_set_eq,Nat.card_congr eqv,Nat.card_eq_fintype_card,
    Fintype.card_subtype,card_filter]
  rfl

lemma port_push (hg : G.maxDegree G.multiplicity ≤ r) (f : V → ℕ) :
    ∑ p : Port G r, f (owner G r p) = r * ∑ v, f v := by
  classical
  calc
    _ = ∑ p : Port G r, ∑ v, (if owner G r p = v then 1 else 0)*f v := by
      simp [ite_mul, Finset.sum_ite_eq]
    _ = ∑ v, (∑ p : Port G r, if owner G r p = v then 1 else 0)*f v := by
      rw [sum_comm]
      simp only [sum_mul]
    _ = _ := by
      have h (v : V) := owner_card G hg v
      simp_rw [←card_filter, h]
      rw [mul_sum]

omit [Fintype V] [DecidableEq V] in
lemma cross_port_sum {K : Type*} [DecidableEq K] (G : Multigraph V E) (l : V → K) (a b : K) :
    ∑ p : Copy G × Bool, pt a (l (endpoint G p.1 p.2)) * pt b (l (endpoint G p.1 (!p.2)))
    = weight G l a b := by
  rw [Fintype.sum_prod_type, Fintype.sum_sigma]
  simp_rw [Fintype.sum_bool]
  simp only [Bool.not_true, Bool.not_false, endpoint, Bool.false_eq_true, if_false, if_true,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  rw [weight,directedEdges,directedEdges,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  ring

omit [Fintype V] [DecidableEq V] in
lemma cross_port_card {K : Type*} [DecidableEq K] (G : Multigraph V E) (l : V → K) (a b : K) :
    #{p : Copy G × Bool | l (endpoint G p.1 p.2)=a ∧ l (endpoint G p.1 (!p.2))=b}
      = weight G l a b := by
  classical
  rw [←cross_port_sum,card_filter]
  apply sum_congr rfl
  intro p _
  by_cases ha : l (endpoint G p.1 p.2)=a <;> by_cases hb : l (endpoint G p.1 (!p.2))=b <;> simp [pt,ha,hb]

def extra {K : Type*} [DecidableEq K] (G : Multigraph V E) (r : ℕ) (l : V → K) (a b : K) :
    Port G r → ℕ
  | .inl (e,j) => pt a (l (endpoint G e j)) * pt b (l (endpoint G e (!j)))
  | .inr _ => 0

lemma port_flags (hr : 3≤r) (hm : Minimal G r U) (i : Index G r U) (p : Port G r) :
    flag (Lives i.val (.inl p)) = pt (block i) (tag hr hm (owner G r p)) +
      extra G r (tag hr hm) rightPart (block i) p := by
  classical
  rcases p with ⟨e,j⟩|z
  · change flag (Lives i.val (real G r e j)) = _
    rw [live_real_iff hr hm]
    by_cases ha : tag hr hm (endpoint G e j) = block i
    · simp [extra,owner,flag,pt,ha]
    · by_cases hb : tag hr hm (endpoint G e j) = rightPart <;>
        by_cases hc : tag hr hm (endpoint G e (!j)) = block i <;>
        simp [extra,owner,flag,pt,ha,hb,hc]
  · have hs := i.prop.no_slack z
    have ht := slack_not_block hr hm i z
    simp [extra,owner,flag,pt,hs,ht]

lemma block_card (hr : 3≤r) (hm : Minimal G r U) (hg : G.maxDegree G.multiplicity ≤ r)
    (i : Index G r U) :
    i.val.supp.ncard = (r+(r-2)) * population (tag hr hm) (block i) +
      weight G (tag hr hm) rightPart (block i) := by
  classical
  rw [lives_card, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [port_flags hr hm i,live_inner_iff hr hm i, flag_pt]
  rw [sum_add_distrib, port_push hg (fun v => pt (block i) (tag hr hm v)), Fintype.sum_sum_type]
  change r * _ + ((∑ p : Copy G × Bool, _) + ∑ _ : Slack G r, 0) + _ = _
  simp only [sum_const_zero, add_zero, extra, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]
  rw [cross_port_sum,←mul_sum,population]
  ring

end OMA.S_mo_488874.Normal

namespace OMA.S_mo_488874.Normal
open SimpleGraph Finset Classical
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable {G : Multigraph V E} {r : ℕ} {U : Set (SplitNode G r)}

lemma block_odd (hr : 3≤r) (hm : Minimal G r U) (hg : G.maxDegree G.multiplicity ≤ r)
    (i : Index G r U) : Odd (weight G (tag hr hm) (block i) rightPart) := by
  rw [weight_symm]
  have h : Odd i.val.supp.ncard := i.prop.odd
  rw [block_card hr hm hg] at h
  have hh : r+(r-2)=2*(r-1) := by omega
  rw [hh,Nat.mul_assoc] at h
  rw [Nat.odd_iff] at h ⊢
  omega

lemma block_nonempty (hr : 3≤r) (hm : Minimal G r U) (hg : G.maxDegree G.multiplicity ≤ r)
    (i : Index G r U) : 0 < population (tag hr hm) (block i) := by
  apply Nat.pos_of_ne_zero
  intro h
  have hh := weight_row_bound G (tag hr hm) (block i)
  rw [h,Nat.mul_zero] at hh
  have ht := (Finset.single_le_sum (f := weight G (tag hr hm) (block i))
    (fun a _ => Nat.zero_le _) (mem_univ rightPart)).trans hh
  have hpos := (block_odd hr hm hg i).pos
  omega

lemma adjacent_block (hr : 3≤r) (hm : Minimal G r U) (i : Index G r U) (e : Copy G) (b : Bool)
    (ha : tag hr hm (endpoint G e b) = block i)
    (hb : tag hr hm (endpoint G e (!b)) ≠ leftPart)
    (hc : tag hr hm (endpoint G e (!b)) ≠ rightPart) :
    tag hr hm (endpoint G e (!b)) = block i := by
  have hw := (tag_block hr hm _ i).mp ha
  have hw' : W G r U (endpoint G e (!b)) :=
    ⟨fun ht => hc ((tag_right hr hm _).2 ht),fun hs => hb ((tag_left hr hm _).2 hs)⟩
  have hh := w_link hr hm (p:=.inl (e,b)) (q:=.inl (e,!b)) (home_spec hr hm hw) hw' rfl
  exact (tag_block hr hm _ i).2 (hh.symm.trans hw)

lemma block_weight_zero (hr : 3≤r) (hm : Minimal G r U) (i : Index G r U) (a : Part (Index G r U))
    (hl : a ≠ leftPart) (ht : a ≠ rightPart) (hne : a ≠ block i) :
    weight G (tag hr hm) (block i) a = 0 := by
  rw [←cross_port_card,card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨e,b⟩ hh
  obtain ⟨_,h,h'⟩ := mem_filter.mp hh
  exact hne (h'.symm.trans (adjacent_block hr hm i e b h (h' ▸ hl) (h' ▸ ht)))

lemma part_pop_S (hr : 3≤r) (hm : Minimal G r U) :
    population (tag hr hm) leftPart = #{v : V | S G r U v} := by
  rw [population,card_filter]
  apply sum_congr rfl
  intro v _
  simp only [pt,tag_left]

lemma part_pop_T (hr : 3≤r) (hm : Minimal G r U) :
    population (tag hr hm) rightPart = #{v : V | T G r U v} := by
  rw [population,card_filter]
  apply sum_congr rfl
  intro v _
  simp only [pt,tag_right]

lemma cross_TS (hr : 3≤r) (hm : Minimal G r U) :
    weight G (tag hr hm) leftPart rightPart =
      #{p : Copy G × Bool | T G r U (endpoint G p.1 p.2) ∧ S G r U (endpoint G p.1 (!p.2))} := by
  rw [weight_symm,←cross_port_card]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p _
  simp only [tag_right,tag_left]

end OMA.S_mo_488874.Normal

namespace OMA.S_mo_488874.Normal
open Classical Finset SimpleGraph TutteLib
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable {G : Multigraph V E} {r : ℕ} {U : Set (SplitNode G r)}

private lemma port_count (hg : G.maxDegree G.multiplicity ≤ r) (P : V → Prop) :
    #{p : Port G r | P (owner G r p)} = r * #{v : V | P v} := by
  classical
  let t : Finset V := {v | P v}
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset (Port G r)) t (owner G r)
  simp_rw [owner_card G hg] at h
  simpa [t,mul_comm] using h.symm

omit [Fintype V] in
private lemma inl_deleted (hmin : Minimal G r U) (p : Port G r) :
    (Sum.inl p : SplitNode G r) ∈ U ↔ S G r U (owner G r p) := by
  constructor
  · intro h
    by_contra hn
    by_cases ht : T G r U (owner G r p)
    · exact t_ports hmin ht h
    · exact w_ports hmin ⟨ht,hn⟩ h
  · intro h
    exact h.2 _ rfl

omit [Fintype V] in
private lemma inr_deleted (hmin : Minimal G r U) (v : V) (i : Fin (r-2)) :
    (Sum.inr (v,i) : SplitNode G r) ∈ U ↔ T G r U v :=
  ⟨fun h _ => inner_uniform hmin h, fun ht => ht i⟩

theorem deleted_card (hg : G.maxDegree G.multiplicity ≤ r) (hmin : Minimal G r U) :
    U.ncard = r * #{v : V | S G r U v} + (r-2)*#{v : V | T G r U v} := by
  classical
  have hc : U.ncard = #{a : SplitNode G r | a ∈ U} := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext
    simp
  rw [hc, card_filter, Fintype.sum_sum_type]
  congr 1
  · simp_rw [inl_deleted hmin]
    rw [← card_filter]
    apply port_count hg
  · rw [Fintype.sum_prod_type]
    simp_rw [inr_deleted hmin]
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [card_filter, Finset.mul_sum]
    simp [mul_comm]

theorem violation_gap (hr : 3≤r) (hg : G.maxDegree G.multiplicity ≤ r)
    (hu : (splitGadget G r).IsTutteViolator U) :
    U.ncard + 2 ≤ (Core G r U).oddComponents.ncard := by
  have hport : Fintype.card (Port G r) = r * Fintype.card V := by
    simpa using port_count (G:=G) hg (fun _ => True)
  have htot : Even (Nat.card (SplitNode G r)) := by
    rw [Nat.card_eq_fintype_card,Fintype.card_sum,hport,Fintype.card_prod,Fintype.card_fin]
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 2≤r by omega)
    rw [hk]
    refine ⟨(k+1)*Fintype.card V, ?_⟩
    simp
    ring
  have hcard := Set.ncard_add_ncard_compl U
  have hc : Nat.card (Fiber G r U) = Uᶜ.ncard := by
    simp only [Fiber,Nat.card_coe_set_eq, Subgraph.deleteVerts_verts, Subgraph.verts_top,
      Set.compl_eq_univ_sdiff]
  have hp := odd_ncard_oddComponents (Core G r U)
  rw [hc] at hp
  change U.ncard < (Core G r U).oddComponents.ncard at hu
  simp only [Nat.odd_iff] at hp
  rw [Nat.even_iff] at htot
  omega

omit [Fintype V] in
private lemma charge_card {X : Type*} (s : Finset X) (node : X → SplitNode G r) :
    ({c : Component G r U | ∃ x ∈ s, Lives c (node x)} : Set _).ncard ≤ #s := by
  classical
  let A : Set (Component G r U) := {c | ∃ x ∈ s, Lives c (node x)}
  let pick (c : A) : s := ⟨c.prop.choose,c.prop.choose_spec.1⟩
  have hlive (c : A) : Lives c.1 (node (pick c)) := c.prop.choose_spec.2
  have hinj : Function.Injective pick := by
    intro c d he
    apply Subtype.ext
    obtain ⟨hc,ec⟩ := hlive c
    have hd := hlive d
    rw [← he] at hd
    obtain ⟨_,ed⟩ := hd
    exact ec.symm.trans ed
  exact (Nat.card_le_card_of_injective pick hinj).trans_eq (by simp)

theorem odd_component_bound :
    (Core G r U).oddComponents.ncard ≤ Fintype.card (Index G r U) +
      (r-2)*#{v : V | S G r U v} +
      #{p : Copy G × Bool | T G r U (endpoint G p.1 p.2) ∧ S G r U (endpoint G p.1 (!p.2))} + 1 := by
  classical
  let inn : Finset (V × Fin (r-2)) := {u | S G r U u.1}
  let cross : Finset (Copy G × Bool) := {p | T G r U (endpoint G p.1 p.2) ∧
    S G r U (endpoint G p.1 (!p.2))}
  let ok : Set (Component G r U) := {c | Good c}
  let I : Set (Component G r U) := {c | ∃ u ∈ inn, Lives c (.inr u)}
  let C : Set (Component G r U) := {c | ∃ p ∈ cross, Lives c (real G r p.1 p.2)}
  let L : Set (Component G r U) := {c | ∃ z : Slack G r, Lives c (.inl (.inr z))}
  have hL : L.ncard ≤ 1 := by
    apply Set.ncard_le_one_iff_subsingleton.mpr
    rintro c ⟨z,hz,ez⟩ d ⟨w,hw,ew⟩
    exact ez.symm.trans ((ConnectedComponent.sound (external_reach hz hw rfl)).trans ew)
  have hI : I.ncard ≤ #inn := charge_card inn Sum.inr
  have hC : C.ncard ≤ #cross := charge_card cross (fun p => real G r p.1 p.2)
  have hcov : (Core G r U).oddComponents ⊆ ok ∪ I ∪ C ∪ L := by
    intro c hc
    by_contra h
    have ho : c ∉ ok := fun hh => h (Or.inl (Or.inl (Or.inl hh)))
    apply ho
    refine ⟨hc, ?_, ?_, ?_⟩
    · intro z hz
      exact h (Or.inr ⟨z,hz⟩)
    · intro v i hv hvi
      exact h (Or.inl (Or.inl (Or.inr ⟨(v,i),by simpa [inn] using hv,hvi⟩)))
    · intro e b he he' hc'
      exact h (Or.inl (Or.inr ⟨(e,b),by simpa [cross] using And.intro he he',hc'⟩))
  have hok : ok.ncard = Fintype.card (Index G r U) := (Nat.card_eq_fintype_card (α := Index G r U))
  have hinn : #inn = (r-2)*#{v : V | S G r U v} := by
    dsimp only [inn]
    rw [card_filter, Fintype.sum_prod_type, card_filter, Finset.mul_sum]
    apply sum_congr rfl
    intro v _
    by_cases h : S G r U v <;> simp [h]
  have h1 := Set.ncard_le_ncard hcov
  have h2 := Set.ncard_union_le (ok ∪ I ∪ C) L
  have h3 := Set.ncard_union_le (ok ∪ I) C
  have h4 := Set.ncard_union_le ok I
  change (Core G r U).oddComponents.ncard ≤ Fintype.card (Index G r U) +
      (r-2)*#{v : V | S G r U v} + #cross + 1
  omega

end OMA.S_mo_488874.Normal

namespace OMA.S_mo_488874
open Finset SimpleGraph Classical

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable (G : Multigraph V E) {r : ℕ} (M : (splitGadget G r).Subgraph)

private def innerAt (v : V) (p : Port G r) : Prop :=
  ∃ i : Fin (r-2), M.Adj (.inr (v,i)) (.inl p)

private def selected (e : Copy G) : Prop :=
  M.Adj (.inl (.inl (e,false))) (.inl (.inl (e,true)))

private lemma internal_card (hM : M.IsPerfectMatching) (v : V) :
    #{p | innerAt G M v p} = r-2 := by
  classical
  have unique := Subgraph.isPerfectMatching_iff.mp hM
  let R (i : Fin (r-2)) (p : Port G r) := M.Adj (.inr (v,i)) (.inl p)
  have hrow (i : Fin (r-2)) : (∑ p : Port G r, if R i p then 1 else 0) = (1:ℕ) := by
    rw [← Finset.card_filter, Finset.card_eq_one_iff_existsUnique]
    obtain ⟨y,hy,hu⟩ := unique (.inr (v,i))
    cases y with
    | inl p =>
      refine ⟨p, by simpa [R] using hy, ?_⟩
      intro q hq
      apply Sum.inl.inj
      exact hu _ (by simpa [R] using hq)
    | inr z => exact False.elim (M.adj_sub hy)
  have hcol (p : Port G r) : (∑ i : Fin (r-2), if R i p then 1 else 0) =
      (if innerAt G M v p then 1 else 0 : ℕ) := by
    by_cases h : innerAt G M v p
    · rw [if_pos h, ← Finset.card_filter, Finset.card_eq_one_iff_existsUnique]
      obtain ⟨i,hi⟩ := h
      refine ⟨i, by simpa [R] using hi, ?_⟩
      intro j hj
      have hj' : M.Adj (.inr (v,j)) (.inl p) := by simpa [R] using hj
      exact congrArg Prod.snd (Sum.inr.inj ((unique (.inl p)).unique hj'.symm hi.symm))
    · have hn (i) : ¬R i p := fun hh => h ⟨i,hh⟩
      simp [h,hn]
  rw [card_filter]
  simp_rw [← hcol]
  rw [Finset.sum_comm]
  simp [hrow]

omit [Fintype V] in
private lemma internal_owner {v : V} {p : Port G r} (h : innerAt G M v p) :
    owner G r p = v := by
  obtain ⟨i,hi⟩ := h
  exact M.adj_sub hi

omit [Fintype V] in
private lemma real_internal (hM : M.IsPerfectMatching) (e : Copy G) (b : Bool) :
    innerAt G M (endpoint G e b) (.inl (e,b)) ↔ ¬selected G M e := by
  have unique := Subgraph.isPerfectMatching_iff.mp hM
  constructor
  · rintro ⟨i,hi⟩ he
    cases b
    · have hh := (unique (.inl (.inl (e,false)))).unique hi.symm he
      cases hh
    · have hh := (unique (.inl (.inl (e,true)))).unique hi.symm he.symm
      cases hh
  · intro hn
    obtain ⟨y,hy,_⟩ := unique (.inl (.inl (e,b)))
    rcases y with ((⟨f,c⟩|z)|⟨w,i⟩)
    · have h := M.adj_sub hy
      change (Sum.inl (e,b) : Port G r) ≠ Sum.inl (f,c) ∧ some e = some f at h
      obtain ⟨hne,he⟩ := h
      obtain rfl := Option.some.inj he
      cases b <;> cases c
      · exact (hne rfl).elim
      · exact (hn hy).elim
      · exact (hn hy.symm).elim
      · exact (hne rfl).elim
    · have h := (M.adj_sub hy).2
      cases h
    · have he : endpoint G e b = w := M.adj_sub hy
      subst w
      exact ⟨i,hy.symm⟩

omit [Fintype V] in
private lemma incidence_card (P : Copy G → Prop) [DecidablePred P] (v : V) :
    #{p : Copy G × Bool | endpoint G p.1 p.2 = v ∧ P p.1} =
      G.degree (fun e => #{i : Fin (G.multiplicity e) | P ⟨e,i⟩}) v := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_sigma, degree_as_endpoints]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  by_cases h : P ⟨e,i⟩ <;> simp [endpoint, pt, h, add_comm]

theorem perfect_split {r : ℕ} (hr : 3 ≤ r) (hg : G.maxDegree G.multiplicity = r)
    (hm : ∃ M : (splitGadget G r).Subgraph, M.IsPerfectMatching) : ¬G.indecomposable := by
  classical
  obtain ⟨M,hM⟩ := hm
  let x (e : E) := #{i : Fin (G.multiplicity e) | selected G M ⟨e,i⟩}
  let y (e : E) := #{i : Fin (G.multiplicity e) | ¬selected G M ⟨e,i⟩}
  have hadd (e : E) : x e + y e = G.multiplicity e := by
    simpa [x,y] using card_filter_add_card_filter_not (s := (univ : Finset (Fin (G.multiplicity e))))
      (fun i => selected G M ⟨e,i⟩)
  apply not_indecomposable_of_bounds G (a := 2) (b := r-2) (by omega) (by omega) (by omega) x y hadd
  · apply Finset.sup_le
    intro v _
    have ht := owner_card G hg.le v
    let D : Finset (Port G r) := {p | owner G r p = v}
    let I (p : Port G r) := innerAt G M v p
    have hi := internal_card G M hM v
    have hin : D.filter I = univ.filter I := by
      ext p
      simp only [D, mem_filter, mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨internal_owner G M h,h⟩⟩
    have hsum := card_filter_add_card_filter_not (s := D) I
    rw [hin] at hsum
    have he : #(D.filter fun p => ¬I p) ≤ 2 := by
      change #D = r at ht
      change #(univ.filter I) = r-2 at hi
      omega
    apply le_trans _ he
    rw [show G.degree x v = _ from (incidence_card G (selected G M) v).symm]
    apply Finset.card_le_card_of_injOn Sum.inl _ Sum.inl_injective.injOn
    intro p hp
    obtain ⟨hv,hs⟩ := (show endpoint G p.1 p.2 = v ∧ selected G M p.1 by simpa using hp)
    change Sum.inl p ∈ D.filter (fun q => ¬ I q)
    simp only [D, mem_filter, mem_univ, true_and]
    refine ⟨hv,?_⟩
    change ¬ innerAt G M v (.inl p)
    rw [← hv]
    exact fun h => ((real_internal G M hM p.1 p.2).mp h) hs
  · apply Finset.sup_le
    intro v _
    rw [← internal_card G M hM v, show G.degree y v = _ from
      (incidence_card G (fun e => ¬selected G M e) v).symm]
    apply Finset.card_le_card_of_injOn Sum.inl _ Sum.inl_injective.injOn
    intro p hp
    obtain ⟨hv,hs⟩ := (show endpoint G p.1 p.2 = v ∧ ¬selected G M p.1 by simpa using hp)
    change Sum.inl p ∈ univ.filter (innerAt G M v)
    simp only [mem_filter, mem_univ, true_and, ← hv]
    exact (real_internal G M hM p.1 p.2).mpr hs

end OMA.S_mo_488874

namespace OMA.S_mo_488874

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem maxDegree_le_size (G : Multigraph V E) (f : E → ℕ) :
    G.maxDegree f ≤ ∑ e, f e := by
  apply Finset.sup_le
  intro v _
  apply Finset.sum_le_sum
  intro e _
  split <;> omega

theorem two_lower (G : Multigraph V E) (hi : G.indecomposable)
    (hr : G.maxDegree G.multiplicity = 2) : 3 ≤ G.edges := by
  classical
  by_contra! ht
  have hbound := maxDegree_le_size G G.multiplicity
  change G.maxDegree G.multiplicity ≤ G.edges at hbound
  have hs : ∑ i, G.multiplicity i = 2 := show G.edges = 2 by omega
  obtain ⟨e, he⟩ : ∃ e, 0 < G.multiplicity e := by
    by_contra! hz
    simp [fun i => Nat.eq_zero_of_le_zero (hz i)] at hs
  let x : E → ℕ := fun i => if i=e then 1 else 0
  let y : E → ℕ := fun i => G.multiplicity i - x i
  have hadd (i : E) : x i + y i = G.multiplicity i := by
    by_cases h : i=e
    · subst i
      simp [x,y]
      omega
    · simp [x,y,h]
  have hx : ∑ i, x i = 1 := by simp [x]
  have hy : ∑ i, y i = 1 := by
    have hsum : (∑ i, x i) + ∑ i, y i = ∑ i, G.multiplicity i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hadd i
    omega
  exact not_indecomposable_of_bounds G (by decide : 0 < 1) (by decide : 0 < 1)
    hr x y hadd ((maxDegree_le_size G x).trans hx.le) ((maxDegree_le_size G y).trans hy.le) hi

def zeroWitness : Multigraph (Fin 1) (Fin 0) where
  source := Fin.elim0
  target := Fin.elim0
  no_loops := fun e => nomatch e
  multiplicity := Fin.elim0

def oneWitness : Multigraph (Fin 2) Unit where
  source := fun _ => 0
  target := fun _ => 1
  no_loops := by decide
  multiplicity := fun _ => 1

def triangle : Multigraph (Fin 3) (Fin 3) where
  source := id
  target := fun e => e+1
  no_loops := by decide
  multiplicity := fun _ => 1

theorem triangle_indec : triangle.indecomposable := by
  intro x y he hx hy
  let x' : Fin 3 → Fin 2 := fun i => ⟨x i, by have h := he i; change _ = 1 at h; omega⟩
  let y' : Fin 3 → Fin 2 := fun i => ⟨y i, by have h := he i; change _ = 1 at h; omega⟩
  have h : ∀ u v : Fin 3 → Fin 2,
      (∀ e, (u e).val + (v e).val = 1) → (∃ e, 0 < (u e).val) → (∃ e, 0 < (v e).val) →
      triangle.maxDegree triangle.multiplicity <
        triangle.maxDegree (fun e => (u e).val) + triangle.maxDegree (fun e => (v e).val) := by decide
  exact h x' y' he hx hy

theorem least_zero : IsLeast (counts 0) 0 := by
  refine ⟨⟨_, _, inferInstance, inferInstance, inferInstance, zeroWitness, ?_, by decide, by decide⟩,
    fun _ _ => Nat.zero_le _⟩
  rintro _ _ _ ⟨e,_⟩
  exact Fin.elim0 e

theorem least_one : IsLeast (counts 1) 1 := by
  refine ⟨⟨_, _, inferInstance, inferInstance, inferInstance, oneWitness, ?_, by decide, by decide⟩, ?_⟩
  · rintro x y he ⟨⟨⟩,hx⟩ ⟨⟨⟩,hy⟩
    change 0 < x () at hx
    change 0 < y () at hy
    have h := he ()
    change _ = 1 at h
    omega
  · rintro m ⟨V,E,iV,iE,iD,G,_,hr,hm⟩
    calc
      1 = G.maxDegree G.multiplicity := hr.symm
      _ ≤ G.edges := maxDegree_le_size G _
      _ = m := hm

theorem least_two : IsLeast (counts 2) 3 := by
  refine ⟨⟨_, _, inferInstance, inferInstance, inferInstance, triangle, triangle_indec, by decide, by decide⟩, ?_⟩
  rintro m ⟨V,E,iV,iE,iD,G,hi,hr,hm⟩
  exact hm ▸ two_lower G hi hr

theorem counts_formula_of_odd_lower
    (lower : ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
      (G : Multigraph V E) {k : ℕ}, 0 < k → G.indecomposable →
      G.maxDegree G.multiplicity = 2*k+1 → (2*k)*(3*k+2) ≤ G.edges) :
    ∀ r, match minimum r with
      | some m => IsLeast (counts r) m
      | none => counts r = ∅ := by
  intro r
  match r with
  | 0 => exact least_zero
  | 1 => exact least_one
  | 2 => exact least_two
  | j+3 =>
    change (match (if Odd (j+3) then some ((j+2)*(3*(j+3)+1)/2) else none) with
      | some m => IsLeast (counts (j+3)) m
      | none => counts (j+3) = ∅)
    by_cases h : Odd (j+3)
    · rw [if_pos h]
      obtain ⟨k,hk⟩ := h
      have hpos : 0<k := by omega
      have eq : (j+2)*(3*(j+3)+1)/2=(2*k)*(3*k+2) := by
        have h1 : j+2=2*k := by omega
        have h2 : 3*(j+3)+1=(3*k+2)*2 := by omega
        rw [h1,h2,← Nat.mul_assoc,Nat.mul_div_cancel _ (by decide : 0<2)]
      rw [eq]
      obtain ⟨hi,hm,he⟩ := lobes_witness hpos
      refine ⟨⟨_, _, inferInstance, inferInstance, inferInstance, lobes k, hi, by omega, he⟩, ?_⟩
      rintro m ⟨V,E,iV,iE,iD,G,hind,hmax,hedges⟩
      exact hedges ▸ lower G hpos hind (by omega)
    · rw [if_neg h]
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro m ⟨V,E,iV,iE,iD,G,hind,hmax,_⟩
      have he : Even (j+3) := Nat.not_odd_iff_even.mp h
      obtain ⟨k,hk⟩ := he
      exact even_decomposable G (k := k) (by omega) (by omega) hind

end OMA.S_mo_488874

namespace OMA.S_mo_488874
open SimpleGraph Finset Classical _root_.OMA.S_mo_488874.Normal

theorem obstruction_lower {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) {r : ℕ} (hr : 3≤r) (hi : G.indecomposable)
    (hg : G.maxDegree G.multiplicity = r) :
    (r-1)*(3*r+1) ≤ 2*G.edges := by
  have hv : ∃ U, (splitGadget G r).IsTutteViolator U := by
    by_contra! h
    exact perfect_split G hr hg ((SimpleGraph.tutte).2 h) hi
  obtain ⟨U,hu,hm⟩ := TutteLib.exists_min_violator _ hv
  let L := tag hr hm
  let C : FactorCertificate G r (Index G r U) := {
    label := L
    nonempty_block := block_nonempty hr hm hg.le
    saturated := fun i v h => block_saturated hr hm hg.le i h
    no_rest := fun i => block_weight_zero hr hm i restPart (by simp [restPart,leftPart]) (by simp [restPart,rightPart]) (by simp [restPart,block])
    no_cross := fun i j h => block_weight_zero hr hm i (block j) (by simp [block,leftPart])
      (by simp [block,rightPart]) (fun he => h (Sum.inr.inj he))
    odd_right := block_odd hr hm hg.le
    deficient := by
      dsimp only [L]
      rw [part_pop_S,part_pop_T,cross_TS]
      have h := (violation_gap hr hg.le hu).trans (odd_component_bound (G:=G) (r:=r) (U:=U))
      rw [deleted_card hg.le hm] at h
      have hh : r*#{v : V | S G r U v} =
        2*#{v : V | S G r U v} + (r-2)*#{v : V | S G r U v} := by
        rw [←Nat.add_mul, Nat.add_sub_of_le (by omega : 2≤r)]
      rw [hh] at h
      omega }
  exact certificate_lower_bound hr hg C

theorem complete_formula : ∀ r : ℕ,
    match minimum r with
    | some m => IsLeast (counts r) m
    | none => counts r = ∅ := by
  apply counts_formula_of_odd_lower
  intro V E iV iE iD G k hk hi hg
  have h := obstruction_lower G (by omega : 3≤2*k+1) hi hg
  have heq : ((2*k+1)-1)*(3*(2*k+1)+1) = 2*((2*k)*(3*k+2)) := by
    rw [Nat.add_sub_cancel]
    ring
  omega

end OMA.S_mo_488874

theorem OMA.solution : type_of% @OMA.S_mo_488874.main := by
  exact OMA.S_mo_488874.complete_formula

/-
Apache-2.0 license for the attributed Tutte component lemmas and adapted canonicalization.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
