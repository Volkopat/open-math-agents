import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1

/-!
# A matched cut for the seven-total-color theorem

Kostochka, Discrete Mathematics 162 (1996), 199–214, Lemma 4.
https://doi.org/10.1016/0012-365X(95)00286-6

We maximize the crossing weight after removing the matching, then maximize
the full crossing weight among ties. Binary labels encode the statement that
the crossing edges span each residual component. Each edge contributes to
the score in both directions.

Credit: @witeg4
-/

namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R2
open scoped BigOperators Classical

/-- The change in the directed sum of crossing weights after a vertex flip. -/
def H1 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (m : W → W → ℕ),
    (∀ x y, m x y = m y x) → (∀ x, m x x = 0) → ∀ (c : W → Bool) (v : W),
    let score (a : W → Bool) : ℤ := ∑ x, ∑ y, if a x = a y then 0 else (m x y : ℤ)
    let side (v : W) : ℤ := ∑ y, if c v = c y then (m v y : ℤ) else 0
    score (fun x => if x = v then !(c v) else c x) - score c =
      2 * (2 * side v - ∑ y, (m v y : ℤ))

/-- Seven-color completion once a matching and a cut satisfying Lemma 4
are supplied. The strict inequality rules out two saturated endpoints
on a crossing edge outside the matching. -/
def H2 : Prop :=
  ∀ (W : Type) [Fintype W] (A : SimpleGraph W) (m : W → W → ℕ),
    (∀ x y, m x y = m y x) → (∀ x, m x x = 0) →
    (∀ x, ∑ y, m x y = 5) → (∀ x y, A.Adj x y ↔ 0 < m x y) →
    ∀ (M : A.Subgraph), M.IsPerfectMatching → ∀ (r : W → W → ℕ) (c : W → Bool),
    let inside (a : W → W → ℕ) (x : W) : ℤ :=
      ∑ y, if c x = c y then (a x y : ℤ) else 0
    (∀ x y, M.Adj x y → r x y + 1 = m x y) →
    (∀ x y, ¬ M.Adj x y → r x y = m x y) →
    (∀ v, inside m v ≤ 2) →
    (∀ d : W → Bool, (∀ x y, 0 < r x y → c x ≠ c y → d x = d y) →
        ∀ x y, 0 < r x y → d x = d y) →
    (∀ v w, c v ≠ c w → 0 < r w v → inside r v < 2 ∨ inside r w < 2) →
    ∃ (vc : W → Fin 7) (ec : W → W → Finset (Fin 7)),
      (∀ x y, ec x y = ec y x) ∧ (∀ x y, (ec x y).card = m x y) ∧
      (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ ec x y) ∧
      (∀ x y z, y ≠ z → Disjoint (ec x y) (ec x z))

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1.H3 := by
  intro exchange finish W _ A mult symMult noLoops regular support matching
  classical
  let inside (m : W → W → ℕ) (c : W → Bool) (v : W) : ℤ :=
    ∑ y, if c v = c y then (m v y : ℤ) else 0
  let margin (m : W → W → ℕ) (c : W → Bool) (v : W) : ℤ :=
    2 * inside m c v - ∑ y, (m v y : ℤ)
  let score (m : W → W → ℕ) (c : W → Bool) : ℤ :=
    ∑ x, ∑ y, if c x = c y then 0 else (m x y : ℤ)
  let flip (c : W → Bool) (v x : W) := if x = v then !(c v) else c x
  have gain (m : W → W → ℕ) (symm : ∀ x y, m x y = m y x) (loops : ∀ x, m x x = 0)
      (c : W → Bool) (v : W) : score m (flip c v) - score m c = 2 * margin m c v :=
    exchange W m symm loops c v

  have neighbor (m : W → W → ℕ) {c : W → Bool} {v w : W}
      (hne : c v ≠ c w) : margin m (flip c v) w = margin m c w + 2*(m w v : ℤ) := by
    have hw : w ≠ v := fun h => hne (congrArg c h.symm)
    have term (z : W) :
        (if flip c v w = flip c v z then (m w z : ℤ) else 0) -
        (if c w = c z then (m w z : ℤ) else 0) = if z = v then (m w v : ℤ) else 0 := by
      by_cases hz : z = v
      · subst z
        cases hv : c v <;> cases hw' : c w <;> simp_all [flip]
      · simp [flip, hw, hz]
    have gainAt : inside m (flip c v) w - inside m c w = m w v := calc
      _ = ∑ z, ((if flip c v w = flip c v z then (m w z : ℤ) else 0) -
          (if c w = c z then (m w z : ℤ) else 0)) := by simp [inside, Finset.sum_sub_distrib]
      _ = _ := by simp_rw [term]; simp
    unfold margin
    omega

  have components (m : W → W → ℕ) (c : W → Bool) (best : ∀ a, score m a ≤ score m c)
      (d : W → Bool) (hd : ∀ x y, 0 < m x y → c x ≠ c y → d x = d y) :
      ∀ x y, 0 < m x y → d x = d y := by
    intro v w hpos
    by_contra hne
    let e (x : W) := xor (c x) (d x)
    let edge (a : W → Bool) (x y : W) : ℤ := if a x = a y then 0 else m x y
    have le (x y : W) : edge c x y ≤ edge e x y := by
      by_cases hxy : 0 < m x y
      · have := hd x y hxy
        cases h1 : c x <;> cases h2 : c y <;> cases h3 : d x <;> cases h4 : d y <;>
          simp_all [edge, e]
      · have : m x y = 0 := by omega
        simp [edge, this]
    have lt : edge c v w < edge e v w := by
      have := hd v w hpos
      cases h1 : c v <;> cases h2 : c w <;> cases h3 : d v <;> cases h4 : d w <;>
        simp_all [edge, e]
    have larger : score m c < score m e := by
      change (∑ x, ∑ y, edge c x y) < ∑ x, ∑ y, edge e x y
      exact Finset.sum_lt_sum (fun x _ => Finset.sum_le_sum fun y _ => le x y)
        ⟨v, Finset.mem_univ _, Finset.sum_lt_sum (fun y _ => le v y) ⟨w, Finset.mem_univ _, lt⟩⟩
    exact (best e).not_gt larger

  have matched_partition (m r : W → W → ℕ) (mate : W → W)
      (ms : ∀ x y, m x y = m y x) (ml : ∀ x, m x x = 0)
      (rs : ∀ x y, r x y = r y x) (rl : ∀ x, r x x = 0)
      (hm : ∀ x, ∑ y, m x y = 5) (hr : ∀ x, ∑ y, r x y = 4)
      (split : ∀ x y, m x y = r x y + if y = mate x then 1 else 0) :
      ∃ c : W → Bool, (∀ v, inside m c v ≤ 2) ∧
        (∀ d : W → Bool, (∀ x y, 0 < r x y → c x ≠ c y → d x = d y) →
            ∀ x y, 0 < r x y → d x = d y) ∧
        ∀ v w, c v ≠ c w → 0 < r w v → inside r c v < 2 ∨ inside r c w < 2 := by
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (score r) Finset.univ_nonempty
    let opt := Finset.univ.filter (fun d : W → Bool => score r d = score r a)
    have haopt : a ∈ opt := by simp [opt]
    obtain ⟨c,hc,hmx⟩ := Finset.exists_max_image opt (score m) ⟨a,haopt⟩
    have hrc : score r c = score r a := (Finset.mem_filter.mp hc).2
    have maxr (d : W → Bool) : score r d ≤ score r c := hrc ▸ ha d (Finset.mem_univ _)
    have sec (d : W → Bool) (hd : score r d = score r c) : score m d ≤ score m c :=
      hmx d (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.trans hrc⟩)
    have rdeg (v : W) : (∑ y, (r v y : ℤ)) = 4 := by exact_mod_cast hr v
    have mdeg (v : W) : (∑ y, (m v y : ℤ)) = 5 := by exact_mod_cast hm v
    have bound (v : W) : inside m c v ≤ inside r c v + 1 := by
      let bonus (y : W) : ℤ := if y = mate v then 1 else 0
      have hle (y : W) : (if c v = c y then (m v y : ℤ) else 0) ≤
          (if c v = c y then (r v y : ℤ) else 0) + bonus y := by
        rw [split]
        by_cases h : c v = c y <;> by_cases hy : y = mate v <;> simp_all [bonus]
      have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hle y)
      simpa [inside, Finset.sum_add_distrib, bonus] using h
    refine ⟨c, ?_, components r c maxr, ?_⟩
    · intro v
      have rg := gain r rs rl c v
      have mg := gain m ms ml c v
      have mr := maxr (flip c v)
      by_contra! high
      have := bound v
      simp only [margin, rdeg, mdeg] at rg mg
      have tie : score r (flip c v) = score r c := by omega
      have := sec (flip c v) tie
      omega
    · intro v w hcros hp
      have rv := gain r rs rl c v
      have rvmax := maxr (flip c v)
      by_cases h : inside r c v < 2
      · exact Or.inl h
      · right
        simp only [margin, rdeg] at rv
        have tie : score r (flip c v) = score r c := by omega
        have rw' := gain r rs rl (flip c v) w
        have rwmax := maxr (flip (flip c v) w)
        have nbor := neighbor r hcros
        rw [nbor] at rw'
        simp only [margin, rdeg] at rw'
        omega

  obtain ⟨M, hM⟩ := matching
  have hu := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
  let mate (x : W) := (hu x).choose
  have adj (x y : W) : M.Adj x y ↔ y = mate x :=
    ⟨(hu x).choose_spec.2 y, fun e => e ▸ (hu x).choose_spec.1⟩
  let r (x y : W) := if M.Adj x y then mult x y-1 else mult x y
  have rs (x y : W) : r x y = r y x := by
    simp only [r, symMult x y, show M.Adj x y ↔ M.Adj y x from ⟨M.adj_symm, M.adj_symm⟩]
  have rl (x : W) : r x x = 0 := by simp [r, noLoops]
  have pos (x y : W) (h : M.Adj x y) : 0 < mult x y := (support x y).mp (M.adj_sub h)
  have split (x y : W) : mult x y = r x y + if y = mate x then 1 else 0 := by
    by_cases h : M.Adj x y
    · have := pos x y h
      simp only [r, if_pos h, if_pos ((adj x y).mp h)]; omega
    · simp [r, h, (adj x y).not.mp h]
  have hr (x : W) : ∑ y, r x y = 4 := by
    have h := regular x
    simp_rw [split x] at h
    simp [Finset.sum_add_distrib] at h
    omega
  obtain ⟨c, bound, conn, strict⟩ := matched_partition mult r mate symMult noLoops rs rl regular hr split
  apply finish W A mult symMult noLoops regular support M hM r c
  · intro x y h
    have := pos x y h
    simp [r,h]; omega
  · intro x y h
    simp [r,h]
  · exact bound
  · exact conn
  · exact strict

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R2
