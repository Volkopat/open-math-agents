import OMAReductions.R_Erdos95_erdos_95_variants_guth_katz_R1

/-!
Reduction of `OMA.R_Erdos95_erdos_95_variants_guth_katz_R1.H2` (Guth-Katz 2015, Theorem 2.11:
upper bound `C * N ^ 3 / k ^ 2` on the number of `k`-rich points in `R ^ 3` for `3 <= k <= N`
determined by at most `N ^ 2` affine lines with at most `N` lines in any affine plane).

We decompose the proof into two decoupled classical pillars:
- `H1`: Guth-Katz polynomial partitioning in `R ^ 3` (Theorem 4.1) together with the
  Szemeredi-Trotter incidence theorem for affine lines in `R ^ 3`.
- `H2`: Guth-Katz algebraic surface contained-lines bound (Section 3, Proposition 3.4) for
  `k`-rich points (`3 <= k <= N`) of at most `N ^ 2` lines all contained in the zero set of a
  single nonzero polynomial `P : MvPolynomial (Fin 3) ℝ` of degree at most `D` with `D * k <= N`
  and at most `N` lines per affine plane.

Inside this file we prove completely from scratch:
1. Uniqueness of an affine line through two distinct points in `R ^ 3` and finiteness of the
   `k`-rich point set for `k >= 2`.
2. Univariate line restriction of `P : MvPolynomial (Fin 3) ℝ` along `t -> p + t • d` with
   degree bound `q.natDegree <= P.totalDegree`, yielding Bezout on a line (`<= P.totalDegree`
   zeros for any line not contained in `Z(P)`).
3. Cell-crossing bound `<= P.totalDegree + 1` via root-rank counting on `R \ q.roots`, and
   bipartite incidence double-counting across all partitioning cells (`sum M_i <= (D + 1) * |L|`).
4. Cellular quadratic-vs-linear splitting and Cauchy-Schwarz bootstrap at `D = N / k`.
5. Sharp `k_in = max 3 ((k + 1) / 2)`, `k_out = k + 1 - k_in` zero-set decomposition avoiding
   the `k = 2` regulus obstruction, together with the transverse zero-set bound
   `|S_Z_out| <= 3 * N ^ 3 / k ^ 2` and complete assembly into `C * N ^ 3 / k ^ 2`.
-/

namespace OMA.R_Erdos95_erdos_95_variants_guth_katz_R1_H2_R1

/-- Guth-Katz (2015) Theorem 4.1 polynomial partitioning in `R ^ 3` together with the
Szemeredi-Trotter (1983) incidence theorem for affine lines in `R ^ 3`. -/
def H1 : Prop :=
  (∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (S : Finset (Fin 3 → ℝ)) (D : ℕ), 1 ≤ D →
    ∃ (P : MvPolynomial (Fin 3) ℝ) (m : ℕ) (cell : (Fin 3 → ℝ) → Fin m),
      P ≠ 0 ∧ P.totalDegree ≤ D ∧ m ≤ c₁ * D ^ 3 ∧
      (∀ i : Fin m,
        D ^ 3 * { x : Fin 3 → ℝ | x ∈ S ∧ MvPolynomial.eval x P ≠ 0 ∧ cell x = i }.ncard ≤
          c₁ * S.card) ∧
      (∀ x y : Fin 3 → ℝ,
        (∀ t : ℝ, 0 ≤ t → t ≤ 1 → MvPolynomial.eval (x + t • (y - x)) P ≠ 0) →
        cell x = cell y)) ∧
  (∃ C_ST : ℝ, 0 < C_ST ∧ ∀ (k : ℕ) (ℳ : Finset (Set (Fin 3 → ℝ))),
    2 ≤ k →
    (∀ L ∈ ℳ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
    ({ x : Fin 3 → ℝ | k ≤ { L | L ∈ ℳ ∧ x ∈ L }.ncard }.ncard : ℝ) ≤
      C_ST * ((ℳ.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (ℳ.card : ℝ) / (k : ℝ)))

/-- Guth-Katz (2015) Section 3 algebraic surface bound: at most `N ^ 2` affine lines in `R ^ 3`
all lying inside the zero set of a nonzero polynomial `P` of degree at most `D` (`D * k <= N`),
with at most `N` lines in any affine plane, determine at most `C * N ^ 3 / k ^ 2` `k`-rich points
for every `3 <= k <= N`. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N k D : ℕ) (P : MvPolynomial (Fin 3) ℝ) (ℒ : Finset (Set (Fin 3 → ℝ))),
    3 ≤ k → k ≤ N → 1 ≤ D → D * k ≤ N →
    P ≠ 0 → P.totalDegree ≤ D →
    ℒ.card ≤ N ^ 2 →
    (∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
    (∀ L ∈ ℒ, ∀ x ∈ L, MvPolynomial.eval x P = 0) →
    (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      { L | L ∈ ℒ ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.ncard ≤ N) →
    ({ x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) ≤
      C * (N : ℝ) ^ 3 / (k : ℝ) ^ 2

lemma line_eq_of_two_mem {L₁ L₂ : Set (Fin 3 → ℝ)} {p₁ d₁ p₂ d₂ x y : Fin 3 → ℝ}
    (hL₁ : L₁ = { z | ∃ t : ℝ, z = p₁ + t • d₁ })
    (hL₂ : L₂ = { z | ∃ t : ℝ, z = p₂ + t • d₂ })
    (hx1 : x ∈ L₁) (hy1 : y ∈ L₁) (hx2 : x ∈ L₂) (hy2 : y ∈ L₂) (hxy : x ≠ y) :
    L₁ = L₂ := by
  rw [hL₁] at hx1 hy1
  rw [hL₂] at hx2 hy2
  rcases hx1 with ⟨t₁, hx1⟩
  rcases hy1 with ⟨s₁, hy1⟩
  rcases hx2 with ⟨t₂, hx2⟩
  rcases hy2 with ⟨s₂, hy2⟩
  have hdiff1 : y - x = (s₁ - t₁) • d₁ := by
    ext i
    simp [hx1, hy1]
    ring
  have hdiff2 : y - x = (s₂ - t₂) • d₂ := by
    ext i
    simp [hx2, hy2]
    ring
  have hyx_ne : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hs1 : s₁ - t₁ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hdiff1
    exact hyx_ne hdiff1
  have hs2 : s₂ - t₂ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hdiff2
    exact hyx_ne hdiff2
  have hd12 : d₁ = ((s₂ - t₂) / (s₁ - t₁)) • d₂ := by
    ext i
    have hi := congrFun (hdiff1.symm.trans hdiff2) i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    field_simp
    linarith
  have hd21 : d₂ = ((s₁ - t₁) / (s₂ - t₂)) • d₁ := by
    ext i
    have hi := congrFun (hdiff2.symm.trans hdiff1) i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    field_simp
    linarith
  rw [hL₁, hL₂]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t₂ + (t - t₁) * ((s₂ - t₂) / (s₁ - t₁)), ?_⟩
    ext i
    have hx_eq := congrFun (hx1.symm.trans hx2) i
    have hd_eq := congrFun hd12 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx_eq hd_eq ⊢
    linear_combination hx_eq + (t - t₁) * hd_eq
  · rintro ⟨t, rfl⟩
    refine ⟨t₁ + (t - t₂) * ((s₁ - t₁) / (s₂ - t₂)), ?_⟩
    ext i
    have hx_eq := congrFun (hx2.symm.trans hx1) i
    have hd_eq := congrFun hd21 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx_eq hd_eq ⊢
    linear_combination hx_eq + (t - t₂) * hd_eq

lemma distinct_lines_inter_subsingleton {L₁ L₂ : Set (Fin 3 → ℝ)}
    (h1 : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L₁ = { x | ∃ t : ℝ, x = p + t • d })
    (h2 : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L₂ = { x | ∃ t : ℝ, x = p + t • d })
    (hne : L₁ ≠ L₂) :
    (L₁ ∩ L₂).Subsingleton := by
  rcases h1 with ⟨p₁, d₁, _, hL₁⟩
  rcases h2 with ⟨p₂, d₂, _, hL₂⟩
  intro x hx y hy
  by_contra hxy
  exact hne (line_eq_of_two_mem hL₁ hL₂ hx.1 hy.1 hx.2 hy.2 hxy)

lemma rich_points_finite (k : ℕ) (hk : 2 ≤ k) (ℒ : Finset (Set (Fin 3 → ℝ)))
    (hℒ : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) :
    { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.Finite := by
  classical
  let pairs : Finset (Set (Fin 3 → ℝ) × Set (Fin 3 → ℝ)) :=
    (ℒ ×ˢ ℒ).filter (fun p => p.1 ≠ p.2)
  have hsub :
      { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard } ⊆
        ⋃ p ∈ (pairs : Set (Set (Fin 3 → ℝ) × Set (Fin 3 → ℝ))), (p.1 ∩ p.2) := by
    intro x hx
    change k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard at hx
    have hcard : 2 ≤ (ℒ.filter (fun L => x ∈ L)).card := by
      have hset : { L | L ∈ ℒ ∧ x ∈ L } = ((ℒ.filter (fun L => x ∈ L)) : Set _) := by
        ext L
        simp
      rw [hset, Set.ncard_coe_finset] at hx
      omega
    have h1lt : 1 < (ℒ.filter (fun L => x ∈ L)).card := by omega
    obtain ⟨L₁, hL₁, L₂, hL₂, hne⟩ := Finset.one_lt_card.mp h1lt
    rw [Finset.mem_filter] at hL₁ hL₂
    refine Set.mem_biUnion (x := (L₁, L₂)) ?_ ⟨hL₁.2, hL₂.2⟩
    simp [pairs, hL₁.1, hL₂.1, hne]
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion pairs.finite_toSet fun p hp => ?_
  rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
  exact (distinct_lines_inter_subsingleton (hℒ p.1 hp.1.1) (hℒ p.2 hp.1.2) hp.2).finite

lemma natDegree_finset_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Polynomial ℝ) (D : ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ D) :
    (∑ i ∈ s, f i).natDegree ≤ D := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    exact max_le (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma evalLinePoly_exists (P : MvPolynomial (Fin 3) ℝ) (p d : Fin 3 → ℝ) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ P.totalDegree ∧
      ∀ t : ℝ, q.eval t = MvPolynomial.eval (p + t • d) P := by
  let lin : Fin 3 → Polynomial ℝ := fun i => Polynomial.C (p i) + Polynomial.C (d i) * Polynomial.X
  let q : Polynomial ℝ :=
    ∑ m ∈ P.support, Polynomial.C (P.coeff m) * ∏ i : Fin 3, (lin i) ^ (m i)
  have hlin_deg : ∀ i : Fin 3, (lin i).natDegree ≤ 1 := by
    intro i
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    refine max_le (by simp) ?_
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
  have hdeg : q.natDegree ≤ P.totalDegree := by
    refine natDegree_finset_sum_le P.support _ P.totalDegree fun m hm => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_prod_le Finset.univ (fun i : Fin 3 => (lin i) ^ (m i))) ?_
    have hsum_deg : (∑ i : Fin 3, ((lin i) ^ (m i)).natDegree) ≤ ∑ i : Fin 3, m i := by
      refine Finset.sum_le_sum fun i _ => ?_
      simpa only [mul_one] using Polynomial.natDegree_pow_le_of_le (m i) (hlin_deg i)
    refine le_trans hsum_deg ?_
    have hmsum : (∑ i : Fin 3, m i) = m.sum (fun _ e => e) := by
      rw [Finsupp.sum_fintype]
      intro _
      rfl
    rw [hmsum]
    exact MvPolynomial.le_totalDegree hm
  refine ⟨q, hdeg, ?_⟩
  intro t
  rw [MvPolynomial.eval_eq']
  simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_pow, lin, Polynomial.eval_add, Polynomial.eval_X]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma line_inter_zeroSet_ncard_le (P : MvPolynomial (Fin 3) ℝ) (L : Set (Fin 3 → ℝ))
    (hL : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (hnot : ¬ ∀ x ∈ L, MvPolynomial.eval x P = 0)
    (T : Finset (Fin 3 → ℝ)) :
    { x : Fin 3 → ℝ | x ∈ T ∧ x ∈ L ∧ MvPolynomial.eval x P = 0 }.ncard ≤ P.totalDegree := by
  classical
  let S₀ : Finset (Fin 3 → ℝ) := T.filter (fun x => x ∈ L ∧ MvPolynomial.eval x P = 0)
  have hS₀_eq :
      { x : Fin 3 → ℝ | x ∈ T ∧ x ∈ L ∧ MvPolynomial.eval x P = 0 } = (S₀ : Set (Fin 3 → ℝ)) := by
    ext x
    simp [S₀]
  rw [hS₀_eq, Set.ncard_coe_finset]
  rcases hL with ⟨p, d, _, hL_eq⟩
  obtain ⟨q, hq_deg, hq_eval⟩ := evalLinePoly_exists P p d
  have hq_ne : q ≠ 0 := by
    intro hq0
    apply hnot
    intro x hx
    rw [hL_eq] at hx
    rcases hx with ⟨t, rfl⟩
    rw [← hq_eval t, hq0, Polynomial.eval_zero]
  have hparam : ∀ x ∈ S₀, ∃ t : ℝ, x = p + t • d := by
    intro x hx
    have hxL : x ∈ L := (Finset.mem_filter.mp hx).2.1
    rw [hL_eq] at hxL
    exact hxL
  let tf : (Fin 3 → ℝ) → ℝ := fun x =>
    if hx : x ∈ S₀ then Classical.choose (hparam x hx) else 0
  have htf_eq : ∀ x ∈ S₀, x = p + tf x • d := by
    intro x hx
    simp only [tf, hx, dite_true]
    exact Classical.choose_spec (hparam x hx)
  have hmaps : Set.MapsTo tf (S₀ : Set (Fin 3 → ℝ)) (q.roots.toFinset : Set ℝ) := by
    intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hq_ne, Polynomial.IsRoot.def,
      hq_eval, ← htf_eq x hx]
    exact (Finset.mem_filter.mp hx).2.2
  have hinj : Set.InjOn tf (S₀ : Set (Fin 3 → ℝ)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    rw [htf_eq x hx, htf_eq y hy, hxy]
  calc
    S₀.card ≤ q.roots.toFinset.card := Finset.card_le_card_of_injOn tf hmaps hinj
    _ ≤ q.roots.card := Multiset.toFinset_card_le q.roots
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ ≤ P.totalDegree := hq_deg

lemma line_cells_ncard_le (P : MvPolynomial (Fin 3) ℝ) (L : Set (Fin 3 → ℝ))
    (hL : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (m : ℕ) (cell : (Fin 3 → ℝ) → Fin m)
    (hseg : ∀ x y : Fin 3 → ℝ,
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → MvPolynomial.eval (x + t • (y - x)) P ≠ 0) →
      cell x = cell y) :
    { i : Fin m | ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i }.ncard ≤
      P.totalDegree + 1 := by
  classical
  let C_L : Finset (Fin m) :=
    Finset.univ.filter (fun i : Fin m => ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i)
  have hCL_eq :
      { i : Fin m | ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i } = (C_L : Set (Fin m)) := by
    ext i
    simp [C_L]
  rw [hCL_eq, Set.ncard_coe_finset]
  by_cases hempty : C_L = ∅
  · simp [hempty]
  rcases hL with ⟨p, d, _, hL_eq⟩
  obtain ⟨q, hq_deg, hq_eval⟩ := evalLinePoly_exists P p d
  have hq_ne : q ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨x₀, hx₀L, hx₀P, _⟩ := (Finset.mem_filter.mp hi₀).2
    rw [hL_eq] at hx₀L
    rcases hx₀L with ⟨t₀, rfl⟩
    intro hq0
    apply hx₀P
    rw [← hq_eval t₀, hq0, Polynomial.eval_zero]
  let R : Finset ℝ := q.roots.toFinset
  have hR_card : R.card ≤ P.totalDegree :=
    le_trans (Multiset.toFinset_card_le q.roots) (le_trans (Polynomial.card_roots' q) hq_deg)
  have hsame_rank : ∀ t₁ t₂ : ℝ, q.eval t₁ ≠ 0 → q.eval t₂ ≠ 0 →
      (R.filter (fun r => r < t₁)).card = (R.filter (fun r => r < t₂)).card →
      cell (p + t₁ • d) = cell (p + t₂ • d) := by
    have haux : ∀ a b : ℝ, a ≤ b → q.eval a ≠ 0 → q.eval b ≠ 0 →
        (R.filter (fun r => r < a)).card = (R.filter (fun r => r < b)).card →
        cell (p + a • d) = cell (p + b • d) := by
      intro a b hab ha hb hrank
      refine hseg (p + a • d) (p + b • d) ?_
      intro s hs0 hs1
      have hvec :
          (p + a • d) + s • ((p + b • d) - (p + a • d)) = p + (a + s * (b - a)) • d := by
        ext j
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hvec, ← hq_eval]
      intro hzero
      let t := a + s * (b - a)
      have hta : a ≤ t := by nlinarith
      have htb : t ≤ b := by nlinarith
      have ht_mem : t ∈ R := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hq_ne, Polynomial.IsRoot.def]
        exact hzero
      have ht_ne_a : t ≠ a := fun hEq => ha (by rw [← hEq]; exact hzero)
      have ht_ne_b : t ≠ b := fun hEq => hb (by rw [← hEq]; exact hzero)
      have hsub : R.filter (fun r => r < a) ⊆ R.filter (fun r => r < b) := by
        intro r hr
        rw [Finset.mem_filter] at hr ⊢
        exact ⟨hr.1, lt_of_lt_of_le hr.2 hab⟩
      have hlt_card : (R.filter (fun r => r < a)).card < (R.filter (fun r => r < b)).card := by
        refine Finset.card_lt_card ?_
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨hsub, ?_⟩
        intro heq
        have hmem_b : t ∈ R.filter (fun r => r < b) :=
          Finset.mem_filter.mpr ⟨ht_mem, lt_of_le_of_ne htb ht_ne_b⟩
        rw [← heq, Finset.mem_filter] at hmem_b
        exact not_lt_of_ge hta hmem_b.2
      exact ne_of_lt hlt_card hrank
    intro t₁ t₂ ht₁ ht₂ hrank
    rcases le_total t₁ t₂ with hle | hle
    · exact haux t₁ t₂ hle ht₁ ht₂ hrank
    · exact (haux t₂ t₁ hle ht₂ ht₁ hrank.symm).symm
  have hwit : ∀ i ∈ C_L, ∃ t : ℝ, q.eval t ≠ 0 ∧ cell (p + t • d) = i := by
    intro i hi
    obtain ⟨x, hxL, hxP, hxcell⟩ := (Finset.mem_filter.mp hi).2
    rw [hL_eq] at hxL
    rcases hxL with ⟨t, rfl⟩
    refine ⟨t, ?_, hxcell⟩
    rw [hq_eval]
    exact hxP
  let rankMap : Fin m → Fin (R.card + 1) := fun i =>
    if hi : i ∈ C_L then
      ⟨(R.filter (fun r => r < Classical.choose (hwit i hi))).card,
        Nat.lt_succ_of_le (Finset.card_filter_le _ _)⟩
    else
      ⟨0, Nat.zero_lt_succ _⟩
  have hinj : Set.InjOn rankMap (C_L : Set (Fin m)) := by
    intro i hi j hj hij
    rw [Finset.mem_coe] at hi hj
    simp only [rankMap, hi, hj, dite_true, Fin.mk.injEq] at hij
    have hsi := Classical.choose_spec (hwit i hi)
    have hsj := Classical.choose_spec (hwit j hj)
    rw [← hsi.2, ← hsj.2]
    exact hsame_rank _ _ hsi.1 hsj.1 hij
  have hmaps : Set.MapsTo rankMap (C_L : Set (Fin m)) (Finset.univ : Finset (Fin (R.card + 1))) :=
    fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  calc
    C_L.card ≤ (Finset.univ : Finset (Fin (R.card + 1))).card :=
      Finset.card_le_card_of_injOn rankMap hmaps hinj
    _ = R.card + 1 := by simp
    _ ≤ P.totalDegree + 1 := Nat.add_le_add_right hR_card 1

lemma sum_active_lines_le (P : MvPolynomial (Fin 3) ℝ) (ℒ : Finset (Set (Fin 3 → ℝ)))
    (hℒ : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (m : ℕ) (cell : (Fin 3 → ℝ) → Fin m)
    (hseg : ∀ x y : Fin 3 → ℝ,
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → MvPolynomial.eval (x + t • (y - x)) P ≠ 0) →
      cell x = cell y) :
    (∑ i : Fin m, { L | L ∈ ℒ ∧ ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i }.ncard) ≤
      (P.totalDegree + 1) * ℒ.card := by
  classical
  have hrew : ∀ i : Fin m,
      { L | L ∈ ℒ ∧ ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i }.ncard =
        (ℒ.filter (fun L => ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i)).card := by
    intro i
    have hset :
        { L | L ∈ ℒ ∧ ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i } =
          ((ℒ.filter (fun L => ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i)) : Set _) := by
      ext L
      simp
    rw [hset, Set.ncard_coe_finset]
  simp_rw [hrew]
  have hswap :
      (∑ i : Fin m, (ℒ.filter (fun L => ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i)).card) =
        ∑ L ∈ ℒ,
          (Finset.univ.filter (fun i : Fin m => ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  calc
    (∑ L ∈ ℒ,
        (Finset.univ.filter (fun i : Fin m => ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i)).card)
        ≤ ∑ _L ∈ ℒ, (P.totalDegree + 1) := by
          refine Finset.sum_le_sum fun L hL => ?_
          have hset :
              { i : Fin m | ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i } =
                ((Finset.univ.filter
                  (fun i : Fin m => ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i)) : Set _) := by
            ext i
            simp
          rw [← Set.ncard_coe_finset, ← hset]
          exact line_cells_ncard_le P L (hℒ L hL) m cell hseg
    _ = ℒ.card * (P.totalDegree + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ = (P.totalDegree + 1) * ℒ.card := Nat.mul_comm _ _

lemma cellular_algebra_step
    {m : ℕ} {N_r k_r D_r c₁_r C_ST S_tot : ℝ}
    (hN0 : 0 ≤ N_r) (hk0 : 0 < k_r) (hD0 : 0 < D_r) (hc₁0 : 0 ≤ c₁_r)
    (hC_ST0 : 0 < C_ST) (hS0 : 0 ≤ S_tot)
    (hDk : D_r * k_r ≤ N_r) (hN_le : N_r ≤ 2 * D_r * k_r)
    (s Mv : Fin m → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hM0 : ∀ i, 0 ≤ Mv i)
    (hM_sum : (∑ i : Fin m, Mv i) ≤ 2 * D_r * N_r ^ 2)
    (hcell : ∀ i, D_r ^ 3 * s i ≤ c₁_r * S_tot)
    (hST : ∀ i, s i ≤ C_ST * (Mv i ^ 2 / k_r ^ 3 + Mv i / k_r)) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      (∑ i : Fin m, s i) ≤ Q + 4 * C_ST * N_r ^ 3 / k_r ^ 2 ∧
      Q ^ 2 ≤ 16 * c₁_r * C_ST * (N_r ^ 3 / k_r ^ 2) * S_tot := by
  classical
  let I_quad : Finset (Fin m) :=
    Finset.univ.filter (fun i : Fin m => s i ≤ 2 * C_ST * Mv i ^ 2 / k_r ^ 3)
  let I_lin : Finset (Fin m) :=
    Finset.univ.filter (fun i : Fin m => ¬ (s i ≤ 2 * C_ST * Mv i ^ 2 / k_r ^ 3))
  let Q : ℝ := ∑ i ∈ I_quad, s i
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => hs0 i
  have hsplit : (∑ i : Fin m, s i) = Q + ∑ i ∈ I_lin, s i :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin m => s i ≤ 2 * C_ST * Mv i ^ 2 / k_r ^ 3) s).symm
  have hlin_bound : (∑ i ∈ I_lin, s i) ≤ 4 * C_ST * N_r ^ 3 / k_r ^ 2 := by
    have hpt : ∀ i ∈ I_lin, s i ≤ 2 * C_ST * Mv i / k_r := by
      intro i hi
      have hnotq : ¬ (s i ≤ 2 * C_ST * Mv i ^ 2 / k_r ^ 3) := (Finset.mem_filter.mp hi).2
      have hst' : s i ≤ C_ST * Mv i ^ 2 / k_r ^ 3 + C_ST * Mv i / k_r := by
        calc
          s i ≤ C_ST * (Mv i ^ 2 / k_r ^ 3 + Mv i / k_r) := hST i
          _ = C_ST * Mv i ^ 2 / k_r ^ 3 + C_ST * Mv i / k_r := by ring
      have hgt : 2 * C_ST * Mv i ^ 2 / k_r ^ 3 < s i := lt_of_not_ge hnotq
      have h2a : 2 * C_ST * Mv i ^ 2 / k_r ^ 3 = 2 * (C_ST * Mv i ^ 2 / k_r ^ 3) := by ring
      have h2b : 2 * C_ST * Mv i / k_r = 2 * (C_ST * Mv i / k_r) := by ring
      linarith
    have hsum_le : (∑ i ∈ I_lin, s i) ≤ (2 * C_ST / k_r) * ∑ i : Fin m, Mv i := by
      calc
        (∑ i ∈ I_lin, s i) ≤ ∑ i ∈ I_lin, (2 * C_ST * Mv i / k_r) := Finset.sum_le_sum hpt
        _ = (2 * C_ST / k_r) * ∑ i ∈ I_lin, Mv i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
        _ ≤ (2 * C_ST / k_r) * ∑ i : Fin m, Mv i := by
              refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by linarith) hk0.le)
              exact Finset.sum_le_univ_sum_of_nonneg hM0
    calc
      (∑ i ∈ I_lin, s i)
          ≤ (2 * C_ST / k_r) * (2 * D_r * N_r ^ 2) :=
            le_trans hsum_le (mul_le_mul_of_nonneg_left hM_sum (div_nonneg (by linarith) hk0.le))
      _ = 4 * C_ST * (D_r * k_r) * N_r ^ 2 / k_r ^ 2 := by
            rw [div_mul_eq_mul_div, div_eq_div_iff hk0.ne' (pow_ne_zero 2 hk0.ne')]
            ring
      _ ≤ 4 * C_ST * N_r * N_r ^ 2 / k_r ^ 2 := by
            have hnum : 4 * C_ST * (D_r * k_r) * N_r ^ 2 ≤ 4 * C_ST * N_r * N_r ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hDk (by linarith))
                (sq_nonneg N_r)
            exact div_le_div_of_nonneg_right hnum (sq_nonneg k_r)
      _ = 4 * C_ST * N_r ^ 3 / k_r ^ 2 := by ring
  have hD3k3 : 0 < D_r ^ 3 * k_r ^ 3 := mul_pos (pow_pos hD0 3) (pow_pos hk0 3)
  have hrad0 : 0 ≤ 2 * c₁_r * C_ST * S_tot / (D_r ^ 3 * k_r ^ 3) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc₁0) hC_ST0.le) hS0) hD3k3.le
  let α : ℝ := Real.sqrt (2 * c₁_r * C_ST * S_tot / (D_r ^ 3 * k_r ^ 3))
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hα_sq : α ^ 2 = 2 * c₁_r * C_ST * S_tot / (D_r ^ 3 * k_r ^ 3) := Real.sq_sqrt hrad0
  have hQ_le : Q ≤ α * (2 * D_r * N_r ^ 2) := by
    have hpt : ∀ i ∈ I_quad, s i ≤ α * Mv i := by
      intro i hi
      have hq_i : s i ≤ 2 * C_ST * Mv i ^ 2 / k_r ^ 3 := (Finset.mem_filter.mp hi).2
      have hcell_i : s i ≤ c₁_r * S_tot / D_r ^ 3 :=
        (le_div_iff₀ (pow_pos hD0 3)).mpr (by linarith [hcell i])
      have hsq_le : s i ^ 2 ≤ (α * Mv i) ^ 2 := by
        rw [mul_pow, hα_sq]
        have hprod := mul_le_mul hcell_i hq_i (hs0 i) (div_nonneg (mul_nonneg hc₁0 hS0) (pow_pos hD0 3).le)
        have hrew :
            (c₁_r * S_tot / D_r ^ 3) * (2 * C_ST * Mv i ^ 2 / k_r ^ 3) =
              2 * c₁_r * C_ST * S_tot / (D_r ^ 3 * k_r ^ 3) * Mv i ^ 2 := by
          rw [div_mul_div_comm, div_mul_eq_mul_div]
          congr 1
          ring
        rw [← hrew]
        simpa only [sq] using hprod
      by_contra hlt
      have hlt' : α * Mv i < s i := lt_of_not_ge hlt
      have hsq_lt : (α * Mv i) ^ 2 < s i ^ 2 := by
        nlinarith [mul_nonneg hα0 (hM0 i)]
      exact not_lt_of_ge hsq_le hsq_lt
    calc
      Q ≤ ∑ i ∈ I_quad, (α * Mv i) := Finset.sum_le_sum hpt
      _ = α * ∑ i ∈ I_quad, Mv i := by rw [Finset.mul_sum]
      _ ≤ α * ∑ i : Fin m, Mv i := mul_le_mul_of_nonneg_left (Finset.sum_le_univ_sum_of_nonneg hM0) hα0
      _ ≤ α * (2 * D_r * N_r ^ 2) := mul_le_mul_of_nonneg_left hM_sum hα0
  have hQ_sq : Q ^ 2 ≤ 16 * c₁_r * C_ST * (N_r ^ 3 / k_r ^ 2) * S_tot := by
    have h2DN0 : 0 ≤ 2 * D_r * N_r ^ 2 := mul_nonneg (by linarith) (sq_nonneg N_r)
    have h1 : Q ^ 2 ≤ (α * (2 * D_r * N_r ^ 2)) ^ 2 := by
      nlinarith [hQ0, hQ_le, mul_nonneg hα0 h2DN0]
    rw [mul_pow, hα_sq] at h1
    have hDk3 : 0 < D_r * k_r ^ 3 := mul_pos hD0 (pow_pos hk0 3)
    have h2 :
        2 * c₁_r * C_ST * S_tot / (D_r ^ 3 * k_r ^ 3) * (2 * D_r * N_r ^ 2) ^ 2 =
          8 * c₁_r * C_ST * S_tot * N_r ^ 4 / (D_r * k_r ^ 3) := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hD3k3.ne' hDk3.ne']
      ring
    rw [h2] at h1
    have h3 :
        8 * c₁_r * C_ST * S_tot * N_r ^ 4 / (D_r * k_r ^ 3) ≤
          16 * c₁_r * C_ST * (N_r ^ 3 / k_r ^ 2) * S_tot := by
      rw [div_le_iff₀ hDk3]
      have hfactor :
          16 * c₁_r * C_ST * (N_r ^ 3 / k_r ^ 2) * S_tot * (D_r * k_r ^ 3) =
            8 * c₁_r * C_ST * S_tot * N_r ^ 3 * (2 * D_r * k_r) := by
        rw [show 16 * c₁_r * C_ST * (N_r ^ 3 / k_r ^ 2) * S_tot * (D_r * k_r ^ 3) =
            (16 * c₁_r * C_ST * N_r ^ 3 * S_tot * (D_r * k_r ^ 3)) / k_r ^ 2 by ring]
        rw [div_eq_iff (pow_ne_zero 2 hk0.ne')]
        ring
      rw [hfactor]
      have hpow : N_r ^ 4 = N_r ^ 3 * N_r := by ring
      rw [hpow, ← mul_assoc]
      have hcoef0 : 0 ≤ 8 * c₁_r * C_ST * S_tot * N_r ^ 3 :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc₁0) hC_ST0.le) hS0)
          (pow_nonneg hN0 3)
      exact mul_le_mul_of_nonneg_left hN_le hcoef0
    exact le_trans h1 h3
  refine ⟨Q, hQ0, ?_, hQ_sq⟩
  rw [hsplit]
  linarith

lemma cellular_rich_bound
    {N k D c₁ m : ℕ} {C_ST : ℝ}
    (hk : 3 ≤ k) (hD1 : 1 ≤ D) (hDk : D * k ≤ N) (hN_le : N ≤ 2 * D * k)
    (hC_ST : 0 < C_ST)
    (ℒ : Finset (Set (Fin 3 → ℝ))) (hℒ_card : ℒ.card ≤ N ^ 2)
    (hℒ : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (S_fin : Finset (Fin 3 → ℝ))
    (hS_rich : ∀ x ∈ S_fin, k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard)
    (P : MvPolynomial (Fin 3) ℝ) (hP_deg : P.totalDegree ≤ D)
    (cell : (Fin 3 → ℝ) → Fin m)
    (hcell_card : ∀ i : Fin m,
      D ^ 3 * { x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P ≠ 0 ∧ cell x = i }.ncard ≤
        c₁ * S_fin.card)
    (hseg : ∀ x y : Fin 3 → ℝ,
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → MvPolynomial.eval (x + t • (y - x)) P ≠ 0) →
      cell x = cell y)
    (hST : ∀ (k' : ℕ) (ℳ : Finset (Set (Fin 3 → ℝ))),
      2 ≤ k' →
      (∀ L ∈ ℳ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
      ({ x : Fin 3 → ℝ | k' ≤ { L | L ∈ ℳ ∧ x ∈ L }.ncard }.ncard : ℝ) ≤
        C_ST * ((ℳ.card : ℝ) ^ 2 / (k' : ℝ) ^ 3 + (ℳ.card : ℝ) / (k' : ℝ))) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      ({ x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P ≠ 0 }.ncard : ℝ) ≤
          Q + 4 * C_ST * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 ∧
      Q ^ 2 ≤ 16 * (c₁ : ℝ) * C_ST * ((N : ℝ) ^ 3 / (k : ℝ) ^ 2) * (S_fin.card : ℝ) := by
  classical
  let S_cell : Finset (Fin 3 → ℝ) := S_fin.filter (fun x => MvPolynomial.eval x P ≠ 0)
  have hScell_ncard :
      { x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P ≠ 0 }.ncard = S_cell.card := by
    have hset : { x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P ≠ 0 } = (S_cell : Set _) := by
      ext x
      simp [S_cell]
    rw [hset, Set.ncard_coe_finset]
  rw [hScell_ncard]
  let Si : Fin m → Finset (Fin 3 → ℝ) := fun i =>
    S_fin.filter (fun x => MvPolynomial.eval x P ≠ 0 ∧ cell x = i)
  let Mi : Fin m → Finset (Set (Fin 3 → ℝ)) := fun i =>
    ℒ.filter (fun L => ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i)
  have hScell_sum : S_cell.card = ∑ i : Fin m, (Si i).card := by
    have hfib := Finset.card_eq_sum_card_fiberwise (f := cell) (s := S_cell) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ext x
    simp [S_cell, Si, and_assoc]
  have hMi_sum_nat : (∑ i : Fin m, (Mi i).card) ≤ 2 * D * N ^ 2 := by
    have h1 := sum_active_lines_le P ℒ hℒ m cell hseg
    have hrew : ∀ i : Fin m,
        (Mi i).card = { L | L ∈ ℒ ∧ ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i }.ncard := by
      intro i
      have hset :
          { L | L ∈ ℒ ∧ ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i } = (Mi i : Set _) := by
        ext L
        simp [Mi]
      rw [hset, Set.ncard_coe_finset]
    simp_rw [hrew]
    have hD_add : P.totalDegree + 1 ≤ 2 * D := by omega
    calc
      (∑ i : Fin m, { L | L ∈ ℒ ∧ ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i }.ncard)
          ≤ (P.totalDegree + 1) * ℒ.card := h1
      _ ≤ (2 * D) * N ^ 2 := Nat.mul_le_mul hD_add hℒ_card
      _ = 2 * D * N ^ 2 := by ring
  have hMi_sum : (∑ i : Fin m, ((Mi i).card : ℝ)) ≤ 2 * (D : ℝ) * (N : ℝ) ^ 2 := by
    have hcast : ((∑ i : Fin m, (Mi i).card : ℕ) : ℝ) ≤ ((2 * D * N ^ 2 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hMi_sum_nat
    push_cast at hcast
    exact hcast
  have hcell_real : ∀ i : Fin m, (D : ℝ) ^ 3 * ((Si i).card : ℝ) ≤ (c₁ : ℝ) * (S_fin.card : ℝ) := by
    intro i
    have hnat := hcell_card i
    have hset_i :
        { x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P ≠ 0 ∧ cell x = i } =
          (Si i : Set _) := by
      ext x
      simp [Si]
    rw [hset_i, Set.ncard_coe_finset] at hnat
    exact_mod_cast hnat
  have hST_cell : ∀ i : Fin m,
      ((Si i).card : ℝ) ≤
        C_ST * (((Mi i).card : ℝ) ^ 2 / (k : ℝ) ^ 3 + ((Mi i).card : ℝ) / (k : ℝ)) := by
    intro i
    have hℳi_lines :
        ∀ L ∈ Mi i, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d } :=
      fun L hL => hℒ L (Finset.mem_filter.mp hL).1
    have hsub :
        (Si i : Set (Fin 3 → ℝ)) ⊆ { x : Fin 3 → ℝ | k ≤ { L | L ∈ Mi i ∧ x ∈ L }.ncard } := by
      intro x hx
      rw [Finset.mem_coe] at hx
      have hx_mem := Finset.mem_filter.mp hx
      have hx_rich := hS_rich x hx_mem.1
      have hset_eq : { L | L ∈ ℒ ∧ x ∈ L } = { L | L ∈ Mi i ∧ x ∈ L } := by
        ext L
        constructor
        · rintro ⟨hL, hxL⟩
          exact ⟨Finset.mem_filter.mpr ⟨hL, x, hxL, hx_mem.2.1, hx_mem.2.2⟩, hxL⟩
        · rintro ⟨hL, hxL⟩
          exact ⟨(Finset.mem_filter.mp hL).1, hxL⟩
      change k ≤ { L | L ∈ Mi i ∧ x ∈ L }.ncard
      rw [← hset_eq]
      exact hx_rich
    have hfin : { x : Fin 3 → ℝ | k ≤ { L | L ∈ Mi i ∧ x ∈ L }.ncard }.Finite :=
      rich_points_finite k (by omega) (Mi i) hℳi_lines
    have hncard_le : (Si i).card ≤ { x : Fin 3 → ℝ | k ≤ { L | L ∈ Mi i ∧ x ∈ L }.ncard }.ncard := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub hfin
    exact le_trans (Nat.cast_le.mpr hncard_le) (hST k (Mi i) (by omega) hℳi_lines)
  rw [hScell_sum, Nat.cast_sum]
  exact cellular_algebra_step (Nat.cast_nonneg N) (by positivity) (by positivity)
    (Nat.cast_nonneg c₁) hC_ST (Nat.cast_nonneg _)
    (by exact_mod_cast hDk) (by exact_mod_cast hN_le)
    (fun i => ((Si i).card : ℝ)) (fun i => ((Mi i).card : ℝ))
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    hMi_sum hcell_real hST_cell

lemma transverse_zeroSet_rich_bound
    {N k D : ℕ} (hk : 3 ≤ k) (hDk : D * k ≤ N)
    (P : MvPolynomial (Fin 3) ℝ) (hP_deg : P.totalDegree ≤ D)
    (ℒ : Finset (Set (Fin 3 → ℝ))) (hℒ_card : ℒ.card ≤ N ^ 2)
    (hℒ : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (S_fin : Finset (Fin 3 → ℝ)) :
    let k_in := max 3 ((k + 1) / 2)
    let k_out := k + 1 - k_in
    ({ x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P = 0 ∧
      k_out ≤ { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L }.ncard }.ncard : ℝ) ≤
      3 * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
  classical
  let k_in := max 3 ((k + 1) / 2)
  let k_out := k + 1 - k_in
  let ℒ_out := ℒ.filter (fun L => ¬ ∀ y ∈ L, MvPolynomial.eval y P = 0)
  let S_out :=
    S_fin.filter (fun x => MvPolynomial.eval x P = 0 ∧
      k_out ≤ { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L }.ncard)
  have hSout_ncard :
      { x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P = 0 ∧
        k_out ≤ { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L }.ncard }.ncard =
        S_out.card := by
    have hset :
        { x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P = 0 ∧
          k_out ≤ { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L }.ncard } =
          (S_out : Set _) := by
      ext x
      simp [S_out]
    rw [hset, Set.ncard_coe_finset]
  change (({ x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P = 0 ∧
    k_out ≤ { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L }.ncard }.ncard : ℕ) : ℝ) ≤ _
  rw [hSout_ncard]
  have hk_out_bound : k ≤ 3 * k_out := by
    dsimp only [k_out, k_in]
    omega
  have hcount : k_out * S_out.card ≤ D * ℒ_out.card := by
    have hlhs :
        k_out * S_out.card ≤ ∑ x ∈ S_out, (ℒ_out.filter (fun L => x ∈ L)).card := by
      calc
        k_out * S_out.card = S_out.card * k_out := Nat.mul_comm _ _
        _ = ∑ _x ∈ S_out, k_out := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ S_out, (ℒ_out.filter (fun L => x ∈ L)).card := by
              refine Finset.sum_le_sum fun x hx => ?_
              have hx_rich := (Finset.mem_filter.mp hx).2.2
              have hset :
                  { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L } =
                    ((ℒ_out.filter (fun L => x ∈ L)) : Set _) := by
                ext L
                simp [ℒ_out, and_assoc]
              rw [hset, Set.ncard_coe_finset] at hx_rich
              exact hx_rich
    have hswap :
        (∑ x ∈ S_out, (ℒ_out.filter (fun L => x ∈ L)).card) =
          ∑ L ∈ ℒ_out, (S_out.filter (fun x => x ∈ L)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hrhs :
        (∑ L ∈ ℒ_out, (S_out.filter (fun x => x ∈ L)).card) ≤ D * ℒ_out.card := by
      calc
        (∑ L ∈ ℒ_out, (S_out.filter (fun x => x ∈ L)).card)
            ≤ ∑ _L ∈ ℒ_out, D := by
              refine Finset.sum_le_sum fun L hL => ?_
              have hL_mem := Finset.mem_filter.mp hL
              have hsub :
                  S_out.filter (fun x => x ∈ L) ⊆
                    S_fin.filter (fun x => x ∈ L ∧ MvPolynomial.eval x P = 0) := by
                intro x hx
                rw [Finset.mem_filter] at hx ⊢
                have hxout := Finset.mem_filter.mp hx.1
                exact ⟨hxout.1, hx.2, hxout.2.1⟩
              have hset_z :
                  { x : Fin 3 → ℝ | x ∈ S_fin ∧ x ∈ L ∧ MvPolynomial.eval x P = 0 } =
                    ((S_fin.filter (fun x => x ∈ L ∧ MvPolynomial.eval x P = 0)) : Set _) := by
                ext x
                simp
              calc
                (S_out.filter (fun x => x ∈ L)).card
                    ≤ (S_fin.filter (fun x => x ∈ L ∧ MvPolynomial.eval x P = 0)).card :=
                      Finset.card_le_card hsub
                _ = { x : Fin 3 → ℝ | x ∈ S_fin ∧ x ∈ L ∧ MvPolynomial.eval x P = 0 }.ncard := by
                      rw [hset_z, Set.ncard_coe_finset]
                _ ≤ P.totalDegree := line_inter_zeroSet_ncard_le P L (hℒ L hL_mem.1) hL_mem.2 S_fin
                _ ≤ D := hP_deg
        _ = ℒ_out.card * D := by rw [Finset.sum_const, smul_eq_mul]
        _ = D * ℒ_out.card := Nat.mul_comm _ _
    exact le_trans hlhs (hswap ▸ hrhs)
  have hℒ_out_card : ℒ_out.card ≤ N ^ 2 := le_trans (Finset.card_filter_le _ _) hℒ_card
  have hnat : k ^ 2 * S_out.card ≤ 3 * N ^ 3 := by
    calc
      k ^ 2 * S_out.card = k * (k * S_out.card) := by ring
      _ ≤ k * (3 * k_out * S_out.card) :=
            Nat.mul_le_mul_left k (Nat.mul_le_mul_right S_out.card hk_out_bound)
      _ = 3 * k * (k_out * S_out.card) := by ring
      _ ≤ 3 * k * (D * ℒ_out.card) := Nat.mul_le_mul_left (3 * k) hcount
      _ = 3 * (D * k) * ℒ_out.card := by ring
      _ ≤ 3 * N * N ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hDk) hℒ_out_card
      _ = 3 * N ^ 3 := by ring
  have hreal : (k : ℝ) ^ 2 * (S_out.card : ℝ) ≤ 3 * (N : ℝ) ^ 3 := by
    exact_mod_cast hnat
  have hk_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  exact (le_div_iff₀ hk_pos).mpr (by linarith)

theorem main : H1 → H2 → OMA.R_Erdos95_erdos_95_variants_guth_katz_R1.H2 := by
  classical
  rintro ⟨⟨c₁, hc₁, hPP⟩, ⟨C_ST, hC_ST, hST⟩⟩ ⟨C₂, hC₂, hSurf⟩
  refine ⟨8 * C_ST + 6 + 8 * C₂ + 64 * (c₁ : ℝ) * C_ST, by positivity, ?_⟩
  intro N k ℒ hk3 hkN hℒ_card hℒ hplanes
  have hS_fin_proof : { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.Finite :=
    rich_points_finite k (by omega) ℒ hℒ
  let S_fin : Finset (Fin 3 → ℝ) := hS_fin_proof.toFinset
  have hS_ncard : { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard = S_fin.card :=
    Set.ncard_eq_toFinset_card _ hS_fin_proof
  rw [hS_ncard]
  have hS_rich : ∀ x ∈ S_fin, k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard := by
    intro x hx
    exact (Set.Finite.mem_toFinset hS_fin_proof).mp hx
  let D : ℕ := N / k
  have hD1 : 1 ≤ D := Nat.div_pos hkN (by omega)
  have hDk : D * k ≤ N := Nat.div_mul_le_self N k
  have hN_le : N ≤ 2 * D * k := by
    have hlt : N < (D + 1) * k := by
      simpa only [D, Nat.mul_comm] using Nat.lt_mul_div_succ N (by omega : 0 < k)
    have hD2 : D + 1 ≤ 2 * D := by omega
    have hle2 : (D + 1) * k ≤ 2 * D * k := Nat.mul_le_mul_right k hD2
    omega
  obtain ⟨P, m, cell, hP_ne, hP_deg, _, hcell_card, hseg⟩ := hPP S_fin D hD1
  obtain ⟨Q, hQ_nonneg, hScell_le, hQ_sq⟩ :=
    cellular_rich_bound hk3 hD1 hDk hN_le hC_ST ℒ hℒ_card hℒ S_fin hS_rich P hP_deg cell
      hcell_card hseg hST
  let k_in : ℕ := max 3 ((k + 1) / 2)
  let k_out : ℕ := k + 1 - k_in
  let ℒ_in : Finset (Set (Fin 3 → ℝ)) := ℒ.filter (fun L => ∀ x ∈ L, MvPolynomial.eval x P = 0)
  let ℒ_out : Finset (Set (Fin 3 → ℝ)) := ℒ.filter (fun L => ¬ ∀ x ∈ L, MvPolynomial.eval x P = 0)
  let S_cell : Finset (Fin 3 → ℝ) := S_fin.filter (fun x => MvPolynomial.eval x P ≠ 0)
  let S_out : Finset (Fin 3 → ℝ) :=
    S_fin.filter (fun x => MvPolynomial.eval x P = 0 ∧
      k_out ≤ { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L }.ncard)
  let S_in : Finset (Fin 3 → ℝ) :=
    S_fin.filter (fun x => MvPolynomial.eval x P = 0 ∧ k_in ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard)
  have hcover : S_fin ⊆ S_cell ∪ (S_out ∪ S_in) := by
    intro x hx
    by_cases hPx : MvPolynomial.eval x P = 0
    · refine Finset.mem_union_right _ ?_
      have hrich := hS_rich x hx
      have hpart :
          (ℒ.filter (fun L => x ∈ L)).card =
            (ℒ_in.filter (fun L => x ∈ L)).card + (ℒ_out.filter (fun L => x ∈ L)).card := by
        have hdisj :
            Disjoint (ℒ_in.filter (fun L => x ∈ L)) (ℒ_out.filter (fun L => x ∈ L)) := by
          rw [Finset.disjoint_left]
          intro L h1 h2
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
            (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
        have hunion :
            ℒ.filter (fun L => x ∈ L) =
              (ℒ_in.filter (fun L => x ∈ L)) ∪ (ℒ_out.filter (fun L => x ∈ L)) := by
          ext L
          simp only [Finset.mem_filter, Finset.mem_union, ℒ_in, ℒ_out]
          tauto
        rw [hunion, Finset.card_union_of_disjoint hdisj]
      have hsum_ge :
          k ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard +
              { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L }.ncard := by
        have hset0 : { L | L ∈ ℒ ∧ x ∈ L } = ((ℒ.filter (fun L => x ∈ L)) : Set _) := by
          ext L; simp
        have hset1 : { L | L ∈ ℒ_in ∧ x ∈ L } = ((ℒ_in.filter (fun L => x ∈ L)) : Set _) := by
          ext L; simp
        have hset2 :
            { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L } =
              ((ℒ_out.filter (fun L => x ∈ L)) : Set _) := by
          ext L; simp [ℒ_out, and_assoc]
        rw [hset0, Set.ncard_coe_finset] at hrich
        rw [hset1, hset2, Set.ncard_coe_finset, Set.ncard_coe_finset]
        omega
      have hcases :
          k_out ≤ { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L }.ncard ∨
            k_in ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard := by
        dsimp only [k_out, k_in]
        omega
      rcases hcases with hout | hin
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hPx, hout⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hPx, hin⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hPx⟩)
  have hcard_union : (S_fin.card : ℝ) ≤ (S_cell.card : ℝ) + (S_out.card : ℝ) + (S_in.card : ℝ) := by
    have hnat : S_fin.card ≤ S_cell.card + S_out.card + S_in.card := by
      calc
        S_fin.card ≤ (S_cell ∪ (S_out ∪ S_in)).card := Finset.card_le_card hcover
        _ ≤ S_cell.card + (S_out ∪ S_in).card := Finset.card_union_le _ _
        _ ≤ S_cell.card + (S_out.card + S_in.card) :=
              Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ = S_cell.card + S_out.card + S_in.card := by ring
    exact_mod_cast hnat
  have hScell_card_le : (S_cell.card : ℝ) ≤ Q + 4 * C_ST * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
    have hset : { x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P ≠ 0 } = (S_cell : Set _) := by
      ext x
      simp [S_cell]
    rw [hset, Set.ncard_coe_finset] at hScell_le
    exact hScell_le
  have hSout_le : (S_out.card : ℝ) ≤ 3 * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
    have h := transverse_zeroSet_rich_bound hk3 hDk P hP_deg ℒ hℒ_card hℒ S_fin
    have hset :
        { x : Fin 3 → ℝ | x ∈ S_fin ∧ MvPolynomial.eval x P = 0 ∧
          k_out ≤ { L | L ∈ ℒ ∧ (¬ ∀ y ∈ L, MvPolynomial.eval y P = 0) ∧ x ∈ L }.ncard } =
          (S_out : Set _) := by
      ext x
      simp [S_out]
    dsimp only at h
    rw [hset, Set.ncard_coe_finset] at h
    exact h
  have hSin_le : (S_in.card : ℝ) ≤ 4 * C₂ * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
    have hkin3 : 3 ≤ k_in := le_max_left 3 _
    have hkin_le_k : k_in ≤ k := by dsimp only [k_in]; omega
    have hkin_N : k_in ≤ N := le_trans hkin_le_k hkN
    have hDkin : D * k_in ≤ N := le_trans (Nat.mul_le_mul_left D hkin_le_k) hDk
    have hℒin_card : ℒ_in.card ≤ N ^ 2 := le_trans (Finset.card_filter_le _ _) hℒ_card
    have hℒin_lines :
        ∀ L ∈ ℒ_in, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d } :=
      fun L hL => hℒ L (Finset.mem_filter.mp hL).1
    have hℒin_zero : ∀ L ∈ ℒ_in, ∀ x ∈ L, MvPolynomial.eval x P = 0 :=
      fun L hL => (Finset.mem_filter.mp hL).2
    have hℒin_planes :
        ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
          { L | L ∈ ℒ_in ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.ncard ≤ N := by
      intro a b c d habc
      have hsub :
          { L | L ∈ ℒ_in ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } } ⊆
            { L | L ∈ ℒ ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } } := by
        rintro L ⟨hL, hLpl⟩
        exact ⟨(Finset.mem_filter.mp hL).1, hLpl⟩
      have hfin_pl :
          { L | L ∈ ℒ ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.Finite :=
        Set.Finite.subset ℒ.finite_toSet fun L hL => hL.1
      exact le_trans (Set.ncard_le_ncard hsub hfin_pl) (hplanes a b c d habc)
    have hsurf_bound :=
      hSurf N k_in D P ℒ_in hkin3 hkin_N hD1 hDkin hP_ne hP_deg hℒin_card hℒin_lines
        hℒin_zero hℒin_planes
    have hSin_sub :
        (S_in : Set (Fin 3 → ℝ)) ⊆ { x : Fin 3 → ℝ | k_in ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard } := by
      intro x hx
      rw [Finset.mem_coe] at hx
      exact (Finset.mem_filter.mp hx).2.2
    have hSin_fin : { x : Fin 3 → ℝ | k_in ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard }.Finite :=
      rich_points_finite k_in (by omega) ℒ_in hℒin_lines
    have hSin_ncard :
        (S_in.card : ℝ) ≤ C₂ * (N : ℝ) ^ 3 / (k_in : ℝ) ^ 2 := by
      have hnat_le : S_in.card ≤ { x : Fin 3 → ℝ | k_in ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard }.ncard := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hSin_sub hSin_fin
      exact le_trans (Nat.cast_le.mpr hnat_le) hsurf_bound
    have hk_le_2kin : (k : ℝ) ≤ 2 * (k_in : ℝ) := by
      have hnat : k ≤ 2 * k_in := by dsimp only [k_in]; omega
      exact_mod_cast hnat
    have hratio : C₂ * (N : ℝ) ^ 3 / (k_in : ℝ) ^ 2 ≤ 4 * C₂ * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
      have hkin_pos : (0 : ℝ) < (k_in : ℝ) ^ 2 := by positivity
      have hk_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ hkin_pos hk_pos]
      have hsq : (k : ℝ) ^ 2 ≤ 4 * (k_in : ℝ) ^ 2 := by nlinarith
      have hcoef : 0 ≤ C₂ * (N : ℝ) ^ 3 := by positivity
      nlinarith
    exact le_trans hSin_ncard hratio
  let A : ℝ := (4 * C_ST + 3 + 4 * C₂) * ((N : ℝ) ^ 3 / (k : ℝ) ^ 2)
  let B : ℝ := 16 * (c₁ : ℝ) * C_ST * ((N : ℝ) ^ 3 / (k : ℝ) ^ 2)
  have hA_nonneg : 0 ≤ A := by positivity
  have hB_nonneg : 0 ≤ B := by positivity
  have hS_le_QA : (S_fin.card : ℝ) ≤ Q + A := by
    have hA_eq :
        A = 4 * C_ST * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 +
            3 * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 +
            4 * C₂ * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
      dsimp only [A]
      ring
    linarith
  have hQ_sq' : Q ^ 2 ≤ B * (S_fin.card : ℝ) := hQ_sq
  have htarget_eq :
      (8 * C_ST + 6 + 8 * C₂ + 64 * (c₁ : ℝ) * C_ST) * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 =
        2 * A + 4 * B := by
    dsimp only [A, B]
    ring
  rw [htarget_eq]
  by_cases hQ : Q ≤ (S_fin.card : ℝ) / 2
  · linarith
  · have hQ_gt : (S_fin.card : ℝ) / 2 < Q := lt_of_not_ge hQ
    have hS_nonneg : (0 : ℝ) ≤ (S_fin.card : ℝ) := Nat.cast_nonneg _
    have hS_sq : ((S_fin.card : ℝ) / 2) ^ 2 ≤ B * (S_fin.card : ℝ) := by
      have h1 : ((S_fin.card : ℝ) / 2) ^ 2 ≤ Q ^ 2 := by nlinarith
      exact le_trans h1 hQ_sq'
    have hS_le_4B : (S_fin.card : ℝ) ≤ 4 * B := by
      by_cases hS0 : (S_fin.card : ℝ) = 0
      · linarith
      · have hS_pos : (0 : ℝ) < (S_fin.card : ℝ) := lt_of_le_of_ne hS_nonneg (Ne.symm hS0)
        nlinarith
    linarith

end OMA.R_Erdos95_erdos_95_variants_guth_katz_R1_H2_R1
