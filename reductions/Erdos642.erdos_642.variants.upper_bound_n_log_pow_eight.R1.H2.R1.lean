import OMAReductions.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1

-- Reduction Erdos642.erdos_642.variants.upper_bound_n_log_pow_eight.R1.H2.R1 of step Erdos642.erdos_642.variants.upper_bound_n_log_pow_eight.R1.H2
-- Credit: @hiattco

namespace OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1_H2_R1

open Filter SimpleGraph
open scoped Classical

/-- Bipartite mixing at the scale of DMMS, Corollary 2.12 in the published paper.
The parity-compatible side carries twice the stationary mass. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ n → ∀ H : SimpleGraph (Fin m),
    H.IsBipartite →
    (∀ u v : Fin m, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) →
    Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m →
    (∀ S : Finset (Fin m), 2 * S.card ≤ m →
      (1 / (10 * Real.log n)) * (2 * (H.edgeSet.ncard : ℝ) / m) * S.card ≤
        ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ)) →
    ∃ (k : ℕ) (b : Fin m → Bool), H.Connected ∧ 0 < k ∧
      (k : ℝ) ≤ 10^10 * (Real.log n)^2 * Real.log m ∧
      (∀ v u, H.Adj v u → b v ≠ b u) ∧
      let P : Matrix (Fin m) (Fin m) ℝ := fun v u =>
        if H.Adj v u then ((H.neighborSet v).ncard : ℝ)⁻¹ else 0
      ∀ v u : Fin m,
        |(P ^ k) v u - (if (b v = b u ↔ Even k) then
          ((H.neighborSet u).ncard : ℝ) / H.edgeSet.ncard else 0)| ≤ 1 / (m : ℝ)^2

/-- The finite random-walk construction of DMMS, Section 3. A closing edge
encloses a segment whose induced edges suffice for a chord-rich cycle. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m k : ℕ, 0 < m → 0 < k → ∀ H : SimpleGraph (Fin m),
    ∀ b : Fin m → Bool, H.Connected → (∀ v u, H.Adj v u → b v ≠ b u) →
    (∀ v u : Fin m, (H.neighborSet v).ncard ≤ 100 * (H.neighborSet u).ncard) →
    (∀ v : Fin m, C * (k : ℝ)^2 ≤ ((H.neighborSet v).ncard : ℝ)) →
    C * (k : ℝ)^2 * Real.log m ≤ (m : ℝ) →
    (let P : Matrix (Fin m) (Fin m) ℝ := fun v u =>
        if H.Adj v u then ((H.neighborSet v).ncard : ℝ)⁻¹ else 0
      ∀ v u : Fin m,
        |(P ^ k) v u - (if (b v = b u ↔ Even k) then
          ((H.neighborSet u).ncard : ℝ) / H.edgeSet.ncard else 0)| ≤ 1 / (m : ℝ)^2) →
    ∃ (v u : Fin m) (p : H.Walk v u) (i j : ℕ), p.IsPath ∧
      i + 2 ≤ j ∧ j ≤ p.length ∧ H.Adj (p.getVert j) (p.getVert i) ∧
      ∃ S : Set (Fin m), (∀ x ∈ S, ∃ a, i ≤ a ∧ a ≤ j ∧ p.getVert a = x) ∧
        2 * (j - i + 1) ≤ (H.induce S).edgeSet.ncard

section
open Set
variable {V : Type*} [Finite V] {G : SimpleGraph V} {v : V}

/-- The induced edges on a cycle split disjointly into cycle edges and chords. -/
theorem induced_edge_count (c : G.Walk v v) (hc : c.IsCycle) :
    (G.induce {x | x ∈ c.support}).edgeSet.ncard =
      c.length + {e : Sym2 V | c.IsChord e}.ncard := by
  classical
  let S : Set V := {x | x ∈ c.support}
  let f : Sym2 S → Sym2 V := Sym2.map Subtype.val
  let E : Set (Sym2 V) := c.edges.toFinset
  let C : Set (Sym2 V) := {e | c.IsChord e}
  have image_eq : f '' (G.induce S).edgeSet = E ∪ C := by
    apply Set.Subset.antisymm
    · rintro _ ⟨e, he, rfl⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
        by_cases h : s(x.val,y.val) ∈ c.edges
        · exact Or.inl (List.mem_toFinset.mpr h)
        · exact Or.inr ((SimpleGraph.Walk.isChord_sym2Mk).mpr ⟨he, h, x.property, y.property⟩)
    · intro e
      induction e using Sym2.inductionOn with
      | _ x y =>
        intro he
        have data : G.Adj x y ∧ x ∈ c.support ∧ y ∈ c.support := by
          rcases he with h | h
          · have h' := List.mem_toFinset.mp h
            exact ⟨c.adj_of_mem_edges h', c.fst_mem_support_of_mem_edges h', c.snd_mem_support_of_mem_edges h'⟩
          · obtain ⟨hxy, _, hx, hy⟩ := SimpleGraph.Walk.isChord_sym2Mk.mp h
            exact ⟨hxy,hx,hy⟩
        exact ⟨s((⟨x,data.2.1⟩ : S),(⟨y,data.2.2⟩ : S)), data.1, rfl⟩
  have disj : Disjoint E C := by
    rw [Set.disjoint_left]
    intro e he hchord
    exact hchord.2.1 (List.mem_toFinset.mp he)
  have edge_count : E.ncard = c.length := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hc.edges_nodup, c.length_edges]
  change (G.induce S).edgeSet.ncard = c.length + C.ncard
  rw [← Set.ncard_image_of_injective (G.induce S).edgeSet (Sym2.map.injective Subtype.val_injective)]
  change (f '' (G.induce S).edgeSet).ncard = _
  rw [image_eq, Set.ncard_union_eq disj, edge_count]

theorem chord_count_of_dense_support (c : G.Walk v v) (hc : c.IsCycle)
    (hd : 2 * c.length ≤ (G.induce {x | x ∈ c.support}).edgeSet.ncard) :
    c.length ≤ {e : Sym2 V | c.IsChord e}.ncard := by
  rw [induced_edge_count c hc] at hd
  omega
end

section
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem close_path (p : G.Walk u v) (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (back : G.Adj v u) :
    (Walk.cons back p).IsCycle ∧ (Walk.cons back p).length = p.length+1 ∧
      ∀ x, x ∈ (Walk.cons back p).support ↔ x ∈ p.support := by
  refine ⟨Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,?_⟩,rfl,?_⟩
  · rw [Walk.tail_cons]
    exact (Walk.isPath_copy p _ _).mpr hp
  · simp only [Walk.length_cons]
    omega
  · intro x
    change x ∈ v :: p.support ↔ _
    rw [List.mem_cons]
    constructor
    · rintro (rfl | h)
      · exact p.end_mem_support
      · exact h
    · exact Or.inr

/-- Any closing edge across positions i and j keeps exactly the vertices in
    the closed index interval and contributes one additional edge. -/
theorem close_interval (p : G.Walk u v) (hp : p.IsPath) (i j : ℕ)
    (hgap : i+2 ≤ j) (hj : j ≤ p.length)
    (back : G.Adj (p.getVert j) (p.getVert i)) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = j-i+1 ∧
      ∀ x, x ∈ c.support ↔ ∃ k, i ≤ k ∧ k ≤ j ∧ p.getVert k = x := by
  let q := (p.drop i).take (j-i)
  have hq : q.IsPath := (hp.drop i).take (j-i)
  have hql : q.length = j-i := by
    simp only [q, Walk.take_length, Walk.drop_length, inf_eq_left.mpr (by omega : j-i ≤ p.length-i)]
  have hx : (p.drop i).getVert (j-i) = p.getVert j := by
    rw [Walk.drop_getVert, show i+(j-i)=j by omega]
  have hb : G.Adj ((p.drop i).getVert (j-i)) (p.getVert i) := hx ▸ back
  obtain ⟨hc,hl,hs⟩ := close_path q hq (by omega) hb
  refine ⟨_,Walk.cons hb q,hc,hl.trans (by rw [hql]),?_⟩
  intro x
  rw [hs,Walk.mem_support_iff_exists_getVert]
  constructor
  · rintro ⟨t, ht, hlen⟩
    rw [hql] at hlen
    refine ⟨i+t,by omega,by omega,?_⟩
    simpa only [q,Walk.take_getVert,inf_eq_right.mpr hlen,Walk.drop_getVert] using ht
  · rintro ⟨k,hik,hkj,hxk⟩
    refine ⟨k-i,?_,by omega⟩
    simpa only [q,Walk.take_getVert,inf_eq_right.mpr (by omega : k-i ≤ j-i),
      Walk.drop_getVert,show i+(k-i)=k by omega] using hxk


/-- The induced edges of retained vertices inject into those of the closed cycle. -/
theorem induced_count_mono [Finite V] {S T : Set V} (hs : S ⊆ T) :
    (G.induce S).edgeSet.ncard ≤ (G.induce T).edgeSet.ncard := by
  let ι : S → T := Set.inclusion hs
  apply Set.ncard_le_ncard_of_injOn (Sym2.map ι)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ a b => exact he
  · exact (Sym2.map.injective (Set.inclusion_injective hs)).injOn

theorem close_dense_interval [Finite V] (p : G.Walk u v) (hp : p.IsPath) (i j : ℕ)
    (hgap : i+2 ≤ j) (hj : j ≤ p.length) (back : G.Adj (p.getVert j) (p.getVert i))
    (S : Set V) (hS : ∀ x ∈ S, ∃ k, i ≤ k ∧ k ≤ j ∧ p.getVert k = x)
    (hd : 2*(j-i+1) ≤ (G.induce S).edgeSet.ncard) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧
      2*c.length ≤ (G.induce {x | x ∈ c.support}).edgeSet.ncard := by
  obtain ⟨z,c,hc,hlen,hsupp⟩ := close_interval p hp i j hgap hj back
  refine ⟨z,c,hc,?_⟩
  rw [hlen]
  exact hd.trans (induced_count_mono fun x hx => (hsupp x).mpr (hS x hx))
end

theorem minimum_degree_and_order {n m : ℕ} (G : SimpleGraph (Fin m)) (hm : 0 < m)
    (hreg : ∀ u v, (G.neighborSet u).ncard ≤ 100 * (G.neighborSet v).ncard)
    (havg : Real.log n ^ 7 / 600 ≤ 2 * (G.edgeSet.ncard : ℝ) / m) :
    (∀ v, Real.log n ^ 7 / 10 ^ 5 ≤ ((G.neighborSet v).ncard : ℝ)) ∧
      Real.log n ^ 7 / 10 ^ 5 ≤ (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : ∑ v, (G.neighborSet v).ncard = 2 * G.edgeSet.ncard := by
    simpa only [Set.ncard_eq_toFinset_card', ← SimpleGraph.neighborFinset_def,
      SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.edgeFinset] using
      G.sum_degrees_eq_twice_card_edges
  have hall (v : Fin m) : Real.log n ^ 7 / 10 ^ 5 ≤ ((G.neighborSet v).ncard : ℝ) := by
    have h : 2 * G.edgeSet.ncard ≤ (100 * (G.neighborSet v).ncard) * m := by
      calc
        _ = _ := hsum.symm
        _ ≤ ∑ _u : Fin m, 100 * (G.neighborSet v).ncard :=
          Finset.sum_le_sum fun u _ => hreg u v
        _ = _ := by simp [Nat.mul_comm m]
    have h' : 2 * (G.edgeSet.ncard : ℝ) / m ≤ 100 * ((G.neighborSet v).ncard : ℝ) :=
      (div_le_iff₀ hm').mpr (by exact_mod_cast h)
    have hdeg := havg.trans h'
    linarith only [hdeg, Nat.cast_nonneg (α := ℝ) (G.neighborSet v).ncard]
  refine ⟨hall, (hall ⟨0, hm⟩).trans ?_⟩
  exact_mod_cast (by simpa only [Nat.card_fin] using
    (G.neighborSet ⟨0, hm⟩).ncard_le_card : (G.neighborSet ⟨0, hm⟩).ncard ≤ m)

/-- A uniform rate for the mixing-time comparison in DMMS, Section 3.5. -/
theorem mixing_scale_mul {n m k : ℝ} (hn : 1 < n) (hm : 1 ≤ m) (hk : 0 ≤ k)
    (hsize : (Real.log n)^7 ≤ 10^5*m)
    (htime : k ≤ 10^10 * (Real.log n)^2 * Real.log m) :
    k^2 * Real.log m * (Real.log n)^2 ≤ 10^28*m := by
  let L := Real.log n
  let M := Real.log m
  have hL : 0 < L := Real.log_pos hn
  have hM : 0 ≤ M := Real.log_nonneg hm
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hpow : M^21 ≤ (Nat.factorial 21 : ℝ)*m := by
    have h := Real.pow_div_factorial_le_exp M hM 21
    rw [show Real.exp M = m from Real.exp_log hm0] at h
    exact (div_le_iff₀ (by positivity)).mp h |>.trans_eq (mul_comm ..)
  change k^2*M*L^2 ≤ (10:ℝ)^28*m
  apply le_of_pow_le_pow_left₀ (n := 7) (by decide) (by positivity)
  calc
    (k^2*M*L^2)^7 ≤ (((10:ℝ)^10*L^2*M)^2*M*L^2)^7 := by
      gcongr
    _ = (10:ℝ)^140 * (L^7)^6 * M^21 := by ring
    _ ≤ (10:ℝ)^140 * ((10:ℝ)^5*m)^6 * M^21 := by
      gcongr
    _ ≤ (10:ℝ)^140 * ((10:ℝ)^5*m)^6 * ((Nat.factorial 21:ℝ)*m) := by
      gcongr
    _ = ((10:ℝ)^170 * (Nat.factorial 21:ℝ))*m^7 := by ring
    _ ≤ ((10:ℝ)^196)*m^7 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      norm_num [Nat.factorial]
    _ = ((10:ℝ)^28*m)^7 := by ring

theorem quantitative_mixing_scale (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ m k : ℕ, 0 < m → m ≤ n →
      (Real.log n)^7/10^5 ≤ (m:ℝ) →
      (k:ℝ) ≤ 10^10*(Real.log n)^2*Real.log m →
      C*(k:ℝ)^2 ≤ (Real.log n)^7/10^5 ∧ C*(k:ℝ)^2*Real.log m ≤ (m:ℝ) := by
  let D := max 1 C
  have hD : 1 ≤ D := le_max_left _ _
  have hCD : C ≤ D := le_max_right _ _
  have hlim : Tendsto (fun n:ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop (10^28*D)] with n hn
  intro m k hm hmn hsize hk
  let L := Real.log (n:ℝ)
  let M := Real.log (m:ℝ)
  change (10:ℝ)^28*D ≤ L at hn
  change L^7/10^5 ≤ (m:ℝ) at hsize
  change (k:ℝ) ≤ 10^10*L^2*M at hk
  change C*(k:ℝ)^2 ≤ L^7/10^5 ∧ C*(k:ℝ)^2*M ≤ (m:ℝ)
  have h1L : 1 ≤ L := by nlinarith
  have hL : 0 < L := zero_lt_one.trans_le h1L
  have hm' : (1:ℝ) ≤ m := Nat.one_le_cast.mpr hm
  have hM : 0 ≤ M := Real.log_nonneg hm'
  have hML : M ≤ L := Real.log_le_log (by positivity) (Nat.cast_le.mpr hmn)
  have hD' : 0 ≤ D := zero_le_one.trans hD
  have hkk : (k:ℝ)^2 ≤ (10^10*L^2*L)^2 := by
    gcongr
    exact hk.trans (by gcongr)
  constructor
  · calc
      C*(k:ℝ)^2 ≤ D*(10^10*L^2*L)^2 :=
        mul_le_mul hCD hkk (by positivity) hD'
      _ = (10^25*D)*L^6/10^5 := by ring
      _ ≤ L*L^6/10^5 := by gcongr; nlinarith
      _ = _ := by ring
  · have hs : L^7 ≤ 10^5*(m:ℝ) := by
      simpa only [mul_comm (m:ℝ)] using (div_le_iff₀ (by norm_num : (0:ℝ)<10^5)).mp hsize
    have hmixed := mixing_scale_mul ((Real.log_pos_iff (Nat.cast_nonneg n)).mp hL)
      hm' (Nat.cast_nonneg k) hs hk
    have hscale : C ≤ L^2/10^28 := by
      apply (le_div_iff₀ (by norm_num)).mpr
      have hsq : L ≤ L^2 := by simpa only [pow_two,one_mul] using mul_le_mul_of_nonneg_right h1L hL.le
      nlinarith
    calc
      C*(k:ℝ)^2*M = C*((k:ℝ)^2*M) := by ring
      _ ≤ (L^2/10^28)*((k:ℝ)^2*M) := mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = ((k:ℝ)^2*M*L^2)/10^28 := by ring
      _ ≤ (m:ℝ) := (div_le_iff₀ (by norm_num)).mpr (hmixed.trans_eq (mul_comm ..))

theorem main : H1 → H2 → OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1.H2 := by
  intro mixing walk
  obtain ⟨C, _, build⟩ := walk
  filter_upwards [mixing, quantitative_mixing_scale C] with n hmix hscale
  intro m hm hmn H hbp hreg hdensity hexp
  obtain ⟨k, b, hconn, hk, htime, hcolor, hkernel⟩ := hmix m hm hmn H hbp hreg hdensity hexp
  obtain ⟨hdegrees, hmSize⟩ := minimum_degree_and_order H hm hreg hdensity
  obtain ⟨hkdeg, hkm⟩ := hscale m k hm hmn hmSize htime
  obtain ⟨v, u, p, i, j, hp, hij, hj, hback, S, hS, hcount⟩ :=
    build m k hm hk H b hconn hcolor hreg (fun v => hkdeg.trans (hdegrees v)) hkm hkernel
  obtain ⟨z, c, hc, hdense⟩ := close_dense_interval p hp i j hij hj hback S hS hcount
  intro hthin
  exact (Nat.not_lt_of_ge (chord_count_of_dense_support c hc hdense)) (hthin z c hc)

end OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1_H2_R1
