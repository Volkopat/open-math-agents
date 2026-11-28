import OMAReductions.R_Erdos95_erdos_95_variants_guth_katz_R1

/-!
Reduction of `Erdos95.erdos_95.variants.guth_katz.R1.H1` (Guth-Katz, *Ann. of Math.* 181 (2015),
Theorem 2.10: at most `C * N^3` 2-rich points for `<= N^2` affine lines in `R^3` with `<= N` lines
per plane and `<= 2 * N` lines per regulus) to two decoupled, unconditionally true pillars:

- `H1`: Guth-Katz Polynomial Partitioning in `R^3` (Theorem 4.1): for any finite point set
  `S : Finset (Fin 3 -> R)` and integer degree `D >= 1`, there exists a nonzero polynomial
  `P : MvPolynomial (Fin 3) R` of `totalDegree <= D` and a finite cell labeling on `R^3 \ Z(P)`
  constant along line segments disjoint from `Z(P)` such that each cell contains at most
  `C_1 * |S| / D^3` points of `S \ Z(P)`.
- `H2`: Cayley-Salmon-Monge and Ruled-Surface Decomposition on `Z(P)` (Guth-Katz 2015, Section 3):
  for any family `L_in` of affine lines contained in `Z(P)` (`P != 0`, `totalDegree <= D`) with
  `<= N` per plane and `<= 2 * N` per regulus, there exists a non-ruled/singular subfamily
  `L_nr <= L_in` of size `<= C_2 * D^2` capturing all 2-rich points of `L_in` outside at most
  `C_2 * (|L_in| * D + |L_in| * N)` ruled/cross-component 2-rich points.

In `main` and the private lemmas below, we prove completely from scratch in Lean 4:
1. Any two distinct affine lines in `R^3` meet in at most one point, yielding finiteness of the
   2-rich point set `S_2(L)` and the pairwise upper bound `|T| <= |M|^2` whenever every point of
   `T` lies on two distinct lines of `M`.
2. Univariate restriction `evalLinePoly P p d : Polynomial R` of `P : MvPolynomial (Fin 3) R` to
   an affine line `t |-> p + t * d` with `natDegree <= P.totalDegree`, proving Bezout on a line:
   a transverse line `L not<= Z(P)` meets `Z(P)` in at most `P.totalDegree` points and visits at
   most `P.totalDegree + 1` cells of `R^3 \ Z(P)` (via `Finset.orderEmbOfFin` and root separation).
3. Cellular double-counting (`s_i <= l_i^2` and `s_i <= C_1 * s / D^3` giving
   `s_cell <= 2 * sqrt(C_1) * sqrt(s) * M / sqrt(D)`) and transverse zero-set counting
   (`|S_trans| <= D * M`).
4. Strong induction on `M = |L|` proving `|S_2(L)| <= C * (M * sqrt(M) + M * N)` by setting
   `D = ceil(64 * C_1' * M^2 / s)` so that `C_2' * D^2 < M / 16 < M`, closing the recursion
   `s <= s/4 + s/4 + s/4 + s/16`, and specializing to `|L| <= N^2` to obtain `<= 2 * C * N^3`.
-/

open scoped Classical

namespace OMA.R_Erdos95_erdos_95_variants_guth_katz_R1_H1_R1

/- Guth-Katz (2015), Theorem 4.1: polynomial partitioning of a finite set in R^3 of degree <= D
with a finite cell assignment constant along every line segment disjoint from Z(P). -/
def H1 : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (S : Finset (Fin 3 → ℝ)) (D : ℕ), 1 ≤ D →
    ∃ (P : MvPolynomial (Fin 3) ℝ) (m : ℕ) (cell : (Fin 3 → ℝ) → Fin m),
      P ≠ 0 ∧ P.totalDegree ≤ D ∧
      (∀ x y : Fin 3 → ℝ,
        (∀ t ∈ Set.Icc (0 : ℝ) 1, MvPolynomial.eval (x + t • (y - x)) P ≠ 0) →
        cell x = cell y) ∧
      (∀ i : Fin m,
        ((S.filter fun x => MvPolynomial.eval x P ≠ 0 ∧ cell x = i).card : ℝ) ≤
          C₁ * (S.card : ℝ) / (D : ℝ) ^ 3)

/- Guth-Katz (2015), Section 3 (Cayley-Salmon-Monge + Ruled-Surface Decomposition): lines contained
in a degree-<= D algebraic surface Z(P) split into a non-ruled/singular subfamily of size <= C_2*D^2
and ruled lines contributing at most C_2 * (|L_in| * D + |L_in| * N) additional 2-rich points. -/
def H2 : Prop :=
  ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (N D : ℕ) (P : MvPolynomial (Fin 3) ℝ)
    (ℒ_in : Finset (Set (Fin 3 → ℝ))),
    1 ≤ N → 1 ≤ D → P ≠ 0 → P.totalDegree ≤ D →
    (∀ L ∈ ℒ_in, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
    (∀ L ∈ ℒ_in, ∀ x ∈ L, MvPolynomial.eval x P = 0) →
    (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      { L | L ∈ ℒ_in ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.ncard ≤ N) →
    (∀ L₁ L₂ L₃ : Set (Fin 3 → ℝ),
      (∀ L ∈ ({L₁, L₂, L₃} : Set (Set (Fin 3 → ℝ))),
        ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
      (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
        let pl := { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }
        ¬ (L₁ ⊆ pl ∧ L₂ ⊆ pl) ∧ ¬ (L₁ ⊆ pl ∧ L₃ ⊆ pl) ∧ ¬ (L₂ ⊆ pl ∧ L₃ ⊆ pl)) →
      { L | L ∈ ℒ_in ∧ (L ∩ L₁).Nonempty ∧ (L ∩ L₂).Nonempty ∧ (L ∩ L₃).Nonempty }.ncard ≤
        2 * N) →
    ∃ ℒ_nr : Finset (Set (Fin 3 → ℝ)), ℒ_nr ⊆ ℒ_in ∧
      (ℒ_nr.card : ℝ) ≤ C₂ * (D : ℝ) ^ 2 ∧
      ({ x : Fin 3 → ℝ |
          2 ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard ∧
          ¬ (2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard) }.ncard : ℝ) ≤
        C₂ * ((ℒ_in.card : ℝ) * (D : ℝ) + (ℒ_in.card : ℝ) * (N : ℝ))

section

private lemma line_eq_through_two_points {L : Set (Fin 3 → ℝ)} {p d x y : Fin 3 → ℝ}
    (hL : L = { z | ∃ t : ℝ, z = p + t • d })
    (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y) :
    L = { z | ∃ s : ℝ, z = x + s • (y - x) } := by
  rw [hL] at hx hy ⊢
  obtain ⟨t₁, rfl⟩ := hx
  obtain ⟨t₂, rfl⟩ := hy
  have htne : t₁ ≠ t₂ := fun h => hxy (by rw [h])
  have hsub_ne : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm htne)
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(t - t₁) / (t₂ - t₁), ?_⟩
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hsub_ne]
    ring
  · rintro ⟨s, rfl⟩
    refine ⟨t₁ + s * (t₂ - t₁), ?_⟩
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

private lemma line_inter_subsingleton {L₁ L₂ : Set (Fin 3 → ℝ)}
    (hL₁ : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L₁ = { x | ∃ t : ℝ, x = p + t • d })
    (hL₂ : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L₂ = { x | ∃ t : ℝ, x = p + t • d })
    (hne : L₁ ≠ L₂) :
    Set.Subsingleton (L₁ ∩ L₂) := by
  intro x hx y hy
  by_contra hxy
  obtain ⟨p₁, d₁, _, heq₁⟩ := hL₁
  obtain ⟨p₂, d₂, _, heq₂⟩ := hL₂
  have h1 := line_eq_through_two_points heq₁ hx.1 hy.1 hxy
  have h2 := line_eq_through_two_points heq₂ hx.2 hy.2 hxy
  exact hne (h1.trans h2.symm)

private lemma two_rich_iff_exists_pair (ℒ : Finset (Set (Fin 3 → ℝ))) (x : Fin 3 → ℝ) :
    2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard ↔ ∃ L₁ ∈ ℒ, ∃ L₂ ∈ ℒ, L₁ ≠ L₂ ∧ x ∈ L₁ ∧ x ∈ L₂ := by
  have hset : { L | L ∈ ℒ ∧ x ∈ L } = ((ℒ.filter fun L => x ∈ L) : Set (Set (Fin 3 → ℝ))) := by
    ext L
    simp
  have h2 : 2 ≤ (ℒ.filter fun L => x ∈ L).card ↔ 1 < (ℒ.filter fun L => x ∈ L).card := by omega
  rw [hset, Set.ncard_coe_finset, h2, Finset.one_lt_card_iff]
  constructor
  · rintro ⟨L₁, L₂, h₁, h₂, hne⟩
    exact ⟨L₁, (Finset.mem_filter.mp h₁).1, L₂, (Finset.mem_filter.mp h₂).1, hne,
      (Finset.mem_filter.mp h₁).2, (Finset.mem_filter.mp h₂).2⟩
  · rintro ⟨L₁, hL₁, L₂, hL₂, hne, hx₁, hx₂⟩
    exact ⟨L₁, L₂, Finset.mem_filter.mpr ⟨hL₁, hx₁⟩, Finset.mem_filter.mpr ⟨hL₂, hx₂⟩, hne⟩

private lemma finite_two_rich_points (ℒ : Finset (Set (Fin 3 → ℝ)))
    (hlines : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) :
    { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.Finite := by
  have hsub : { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard } ⊆
      ⋃ p ∈ ((ℒ ×ˢ ℒ).filter fun p => p.1 ≠ p.2), (p.1 ∩ p.2) := by
    intro x hx
    obtain ⟨L₁, hL₁, L₂, hL₂, hne, hx₁, hx₂⟩ := (two_rich_iff_exists_pair ℒ x).mp hx
    exact Set.mem_iUnion₂.mpr
      ⟨(L₁, L₂), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hL₁, hL₂⟩, hne⟩, hx₁, hx₂⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) ?_) hsub
  intro p hp
  have hmem := Finset.mem_filter.mp hp
  have hprod := Finset.mem_product.mp hmem.1
  exact (line_inter_subsingleton (hlines p.1 hprod.1) (hlines p.2 hprod.2) hmem.2).finite

private lemma card_two_rich_subset_le_sq (ℳ : Finset (Set (Fin 3 → ℝ)))
    (hlines : ∀ L ∈ ℳ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (T : Finset (Fin 3 → ℝ))
    (hT : ∀ x ∈ T, ∃ L₁ ∈ ℳ, ∃ L₂ ∈ ℳ, L₁ ≠ L₂ ∧ x ∈ L₁ ∧ x ∈ L₂) :
    T.card ≤ ℳ.card ^ 2 := by
  have hex : ∀ x : T, ∃ p : Set (Fin 3 → ℝ) × Set (Fin 3 → ℝ),
      p.1 ∈ ℳ ∧ p.2 ∈ ℳ ∧ p.1 ≠ p.2 ∧ x.1 ∈ p.1 ∧ x.1 ∈ p.2 := by
    rintro ⟨x, hx⟩
    obtain ⟨L₁, hL₁, L₂, hL₂, hne, hx₁, hx₂⟩ := hT x hx
    exact ⟨(L₁, L₂), hL₁, hL₂, hne, hx₁, hx₂⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    have hx := hf x
    have hy := hf y
    rw [← hxy] at hy
    have hsub := line_inter_subsingleton (hlines _ hx.1) (hlines _ hx.2.1) hx.2.2.1
    exact Subtype.ext (hsub ⟨hx.2.2.2.1, hx.2.2.2.2⟩ ⟨hy.2.2.2.1, hy.2.2.2.2⟩)
  have hmem : ∀ x : T, f x ∈ ℳ ×ˢ ℳ := fun x =>
    Finset.mem_product.mpr ⟨(hf x).1, (hf x).2.1⟩
  have hle : Fintype.card T ≤ (ℳ ×ˢ ℳ).card := by
    let g : T → (ℳ ×ˢ ℳ) := fun x => ⟨f x, hmem x⟩
    have hginj : Function.Injective g := fun x y h => hinj (congrArg Subtype.val h)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hginj
  rw [Fintype.card_coe, Finset.card_product, ← sq] at hle
  exact hle

private noncomputable def evalLinePoly (P : MvPolynomial (Fin 3) ℝ) (p d : Fin 3 → ℝ) :
    Polynomial ℝ :=
  MvPolynomial.aeval (fun i : Fin 3 => Polynomial.C (p i) + Polynomial.C (d i) * Polynomial.X) P

private lemma eval_evalLinePoly (P : MvPolynomial (Fin 3) ℝ) (p d : Fin 3 → ℝ) (t : ℝ) :
    (evalLinePoly P p d).eval t = MvPolynomial.eval (p + t • d) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [evalLinePoly]
  | add f g hf hg =>
    have hadd : evalLinePoly (f + g) p d = evalLinePoly f p d + evalLinePoly g p d :=
      map_add _ f g
    rw [hadd, Polynomial.eval_add, map_add, hf, hg]
  | mul_X f i hf =>
    have hmul : evalLinePoly (f * MvPolynomial.X i) p d =
        evalLinePoly f p d * (Polynomial.C (p i) + Polynomial.C (d i) * Polynomial.X) := by
      simp [evalLinePoly]
    rw [hmul, Polynomial.eval_mul, hf, map_mul, MvPolynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C,
      Polynomial.eval_X]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

private lemma natDegree_linear_le_one (a b : ℝ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  rw [Polynomial.natDegree_C]
  refine max_le (Nat.zero_le 1) ?_
  exact (Polynomial.natDegree_C_mul_le b Polynomial.X).trans (by simp)

private lemma natDegree_evalLinePoly_le (P : MvPolynomial (Fin 3) ℝ) (p d : Fin 3 → ℝ) :
    (evalLinePoly P p d).natDegree ≤ P.totalDegree := by
  let g : Fin 3 → Polynomial ℝ := fun i => Polynomial.C (p i) + Polynomial.C (d i) * Polynomial.X
  have hdecomp : evalLinePoly P p d =
      ∑ m ∈ P.support, Polynomial.C (P.coeff m) * ∏ i : Fin 3, (g i) ^ (m i) := by
    dsimp only [evalLinePoly, g]
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [hdecomp]
  have hsum_deg : ∀ (s : Finset (Fin 3 →₀ ℕ)), (∀ m ∈ s, m ∈ P.support) →
      (∑ m ∈ s, Polynomial.C (P.coeff m) * ∏ i : Fin 3, (g i) ^ (m i)).natDegree ≤ P.totalDegree := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert m s hm ih =>
      rw [Finset.sum_insert hm]
      refine (Polynomial.natDegree_add_le _ _).trans
        (max_le ?_ (ih fun m' hm' => hs m' (Finset.mem_insert_of_mem hm')))
      have hmP : m ∈ P.support := hs m (Finset.mem_insert_self m s)
      have h1 : (Polynomial.C (P.coeff m) * ∏ i : Fin 3, (g i) ^ (m i)).natDegree ≤
          (∏ i : Fin 3, (g i) ^ (m i)).natDegree := Polynomial.natDegree_C_mul_le _ _
      have h2 : (∏ i : Fin 3, (g i) ^ (m i)).natDegree ≤
          ∑ i : Fin 3, ((g i) ^ (m i)).natDegree := Polynomial.natDegree_prod_le _ _
      have h3 : ∑ i : Fin 3, ((g i) ^ (m i)).natDegree ≤ ∑ i : Fin 3, m i := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ((g i) ^ (m i)).natDegree ≤ m i * (g i).natDegree := Polynomial.natDegree_pow_le
          _ ≤ m i * 1 := Nat.mul_le_mul_left _ (natDegree_linear_le_one (p i) (d i))
          _ = m i := Nat.mul_one _
      have h4 : ∑ i : Fin 3, m i = m.sum (fun _ k => k) := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      have h5 : m.sum (fun _ k => k) ≤ P.totalDegree := MvPolynomial.le_totalDegree hmP
      omega
  exact hsum_deg P.support fun _ hm => hm

private lemma transverse_line_zeros_le (P : MvPolynomial (Fin 3) ℝ)
    {L : Set (Fin 3 → ℝ)} {p d : Fin 3 → ℝ}
    (hL : L = { x | ∃ t : ℝ, x = p + t • d })
    (htrans : ∃ x ∈ L, MvPolynomial.eval x P ≠ 0)
    (T : Finset (Fin 3 → ℝ))
    (hT : ∀ x ∈ T, x ∈ L ∧ MvPolynomial.eval x P = 0) :
    T.card ≤ P.totalDegree := by
  let q : Polynomial ℝ := evalLinePoly P p d
  have hq_ne : q ≠ 0 := by
    obtain ⟨x₀, hx₀L, hx₀ne⟩ := htrans
    rw [hL] at hx₀L
    obtain ⟨t₀, rfl⟩ := hx₀L
    intro h0
    have hev : q.eval t₀ = 0 := by rw [h0]; simp
    rw [eval_evalLinePoly] at hev
    exact hx₀ne hev
  have hex : ∀ x : T, ∃ t : ℝ, x.1 = p + t • d := by
    rintro ⟨x, hx⟩
    have hxL := (hT x hx).1
    rw [hL] at hxL
    exact hxL
  choose tOf htOf using hex
  have hinj : Function.Injective tOf := by
    intro x y hxy
    apply Subtype.ext
    rw [htOf x, htOf y, hxy]
  have hmem : ∀ x : T, tOf x ∈ q.roots.toFinset := by
    intro x
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq_ne, Polynomial.IsRoot.def]
    rw [eval_evalLinePoly, ← htOf x]
    exact (hT x.1 x.2).2
  let g : T → q.roots.toFinset := fun x => ⟨tOf x, hmem x⟩
  have hginj : Function.Injective g := fun x y h => hinj (congrArg Subtype.val h)
  have hcard1 : T.card ≤ q.roots.toFinset.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hginj
  have hcard2 : q.roots.toFinset.card ≤ q.roots.card := Multiset.toFinset_card_le _
  have hcard3 : q.roots.card ≤ q.natDegree := Polynomial.card_roots' q
  exact hcard1.trans (hcard2.trans (hcard3.trans (natDegree_evalLinePoly_le P p d)))

private lemma transverse_line_cells_le (P : MvPolynomial (Fin 3) ℝ)
    (m : ℕ) (cell : (Fin 3 → ℝ) → Fin m)
    (hseg : ∀ x y : Fin 3 → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, MvPolynomial.eval (x + t • (y - x)) P ≠ 0) →
      cell x = cell y)
    {L : Set (Fin 3 → ℝ)} {p d : Fin 3 → ℝ}
    (hL : L = { x | ∃ t : ℝ, x = p + t • d })
    (I : Finset (Fin m))
    (hI : ∀ i ∈ I, ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i) :
    I.card ≤ P.totalDegree + 1 := by
  by_cases hI0 : I.card ≤ 1
  · omega
  have hI2 : 2 ≤ I.card := by omega
  have hex_t : ∀ i : I, ∃ t : ℝ,
      MvPolynomial.eval (p + t • d) P ≠ 0 ∧ cell (p + t • d) = i.1 := by
    rintro ⟨i, hi⟩
    obtain ⟨x, hxL, hxne, hxcell⟩ := hI i hi
    rw [hL] at hxL
    obtain ⟨t, rfl⟩ := hxL
    exact ⟨t, hxne, hxcell⟩
  choose tOf htOf using hex_t
  have htOf_inj : Function.Injective tOf := by
    intro i j hij
    apply Subtype.ext
    rw [← (htOf i).2, ← (htOf j).2, hij]
  let Ts : Finset ℝ := Finset.univ.image tOf
  have hTs_card : Ts.card = I.card := by
    rw [Finset.card_image_of_injective _ htOf_inj, Finset.card_univ, Fintype.card_coe]
  let q : Polynomial ℝ := evalLinePoly P p d
  have hq_ne : q ≠ 0 := by
    have hne : I.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀⟩ := hne
    intro h0
    have hev : q.eval (tOf ⟨i₀, hi₀⟩) = 0 := by rw [h0]; simp
    rw [eval_evalLinePoly] at hev
    exact (htOf ⟨i₀, hi₀⟩).1 hev
  let emb : Fin Ts.card ↪o ℝ := Ts.orderEmbOfFin rfl
  have hemb_mem : ∀ k : Fin Ts.card, emb k ∈ Ts := fun k => Finset.orderEmbOfFin_mem Ts rfl k
  have hemb_ne0 : ∀ k : Fin Ts.card, MvPolynomial.eval (p + emb k • d) P ≠ 0 := by
    intro k
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hemb_mem k)
    rw [← hi]
    exact (htOf i).1
  have hemb_cell_inj : ∀ k₁ k₂ : Fin Ts.card, k₁ ≠ k₂ →
      cell (p + emb k₁ • d) ≠ cell (p + emb k₂ • d) := by
    intro k₁ k₂ hkne hceq
    obtain ⟨i₁, _, hi₁⟩ := Finset.mem_image.mp (hemb_mem k₁)
    obtain ⟨i₂, _, hi₂⟩ := Finset.mem_image.mp (hemb_mem k₂)
    rw [← hi₁, ← hi₂, (htOf i₁).2, (htOf i₂).2] at hceq
    have hi_eq : i₁ = i₂ := Subtype.ext hceq
    have hemb_eq : emb k₁ = emb k₂ := by rw [← hi₁, ← hi₂, hi_eq]
    exact hkne (emb.injective hemb_eq)
  have hex_root : ∀ j : Fin (Ts.card - 1),
      ∃ r : ℝ, emb ⟨j.val, by omega⟩ < r ∧ r < emb ⟨j.val + 1, by omega⟩ ∧
        q.eval r = 0 := by
    intro j
    let k₁ : Fin Ts.card := ⟨j.val, by omega⟩
    let k₂ : Fin Ts.card := ⟨j.val + 1, by omega⟩
    have hk_lt : k₁ < k₂ := Fin.mk_lt_mk.mpr (Nat.lt_succ_self j.val)
    have hlt : emb k₁ < emb k₂ := emb.strictMono hk_lt
    have hcne : cell (p + emb k₁ • d) ≠ cell (p + emb k₂ • d) :=
      hemb_cell_inj k₁ k₂ (ne_of_lt hk_lt)
    have hnot : ¬ ∀ u ∈ Set.Icc (0 : ℝ) 1,
        MvPolynomial.eval ((p + emb k₁ • d) + u • ((p + emb k₂ • d) - (p + emb k₁ • d))) P ≠ 0 :=
      fun hall => hcne (hseg _ _ hall)
    push Not at hnot
    obtain ⟨u, huIcc, hu0⟩ := hnot
    let r : ℝ := emb k₁ + u * (emb k₂ - emb k₁)
    have hpt : (p + emb k₁ • d) + u • ((p + emb k₂ • d) - (p + emb k₁ • d)) = p + r • d := by
      ext idx
      simp only [r, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hpt] at hu0
    have hr_ev : q.eval r = 0 := by rw [eval_evalLinePoly]; exact hu0
    have hr_ge : emb k₁ ≤ r := by
      dsimp only [r]
      have h1 : 0 ≤ u * (emb k₂ - emb k₁) := mul_nonneg huIcc.1 (sub_nonneg.mpr (le_of_lt hlt))
      linarith
    have hr_le : r ≤ emb k₂ := by
      dsimp only [r]
      have h1 : u * (emb k₂ - emb k₁) ≤ 1 * (emb k₂ - emb k₁) :=
        mul_le_mul_of_nonneg_right huIcc.2 (sub_nonneg.mpr (le_of_lt hlt))
      linarith
    have hr_ne1 : r ≠ emb k₁ := fun h => hemb_ne0 k₁ (by rw [← h]; exact hu0)
    have hr_ne2 : r ≠ emb k₂ := fun h => hemb_ne0 k₂ (by rw [← h]; exact hu0)
    exact ⟨r, lt_of_le_of_ne hr_ge hr_ne1.symm, lt_of_le_of_ne hr_le hr_ne2, hr_ev⟩
  choose rOf hrOf using hex_root
  have hrOf_inj : Function.Injective rOf := by
    have hmono : StrictMono rOf := by
      intro j₁ j₂ hlt
      have hle : (⟨j₁.val + 1, by omega⟩ : Fin Ts.card) ≤ ⟨j₂.val, by omega⟩ :=
        Fin.mk_le_mk.mpr hlt
      have h1 : rOf j₁ < emb ⟨j₁.val + 1, by omega⟩ := (hrOf j₁).2.1
      have h2 : emb ⟨j₁.val + 1, by omega⟩ ≤ emb ⟨j₂.val, by omega⟩ := emb.monotone hle
      have h3 : emb ⟨j₂.val, by omega⟩ < rOf j₂ := (hrOf j₂).1
      linarith
    exact hmono.injective
  have hr_mem : ∀ j : Fin (Ts.card - 1), rOf j ∈ q.roots.toFinset := by
    intro j
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq_ne, Polynomial.IsRoot.def]
    exact (hrOf j).2.2
  let g : Fin (Ts.card - 1) → q.roots.toFinset := fun j => ⟨rOf j, hr_mem j⟩
  have hginj : Function.Injective g := fun j₁ j₂ h => hrOf_inj (congrArg Subtype.val h)
  have hcard1 : Ts.card - 1 ≤ q.roots.toFinset.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective g hginj
  have hcard2 : q.roots.toFinset.card ≤ q.roots.card := Multiset.toFinset_card_le _
  have hcard3 : q.roots.card ≤ q.natDegree := Polynomial.card_roots' q
  have hcard4 : q.natDegree ≤ P.totalDegree := natDegree_evalLinePoly_le P p d
  omega

private lemma cellular_double_count
    {C₁' s : ℝ} (hC₁ : 0 < C₁') (hs : 0 < s)
    {D m : ℕ} (hD : 1 ≤ D)
    (P : MvPolynomial (Fin 3) ℝ) (hdeg : P.totalDegree ≤ D)
    (cell : (Fin 3 → ℝ) → Fin m)
    (hseg : ∀ x y : Fin 3 → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, MvPolynomial.eval (x + t • (y - x)) P ≠ 0) →
      cell x = cell y)
    (ℒ : Finset (Set (Fin 3 → ℝ)))
    (hlines : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (S : Finset (Fin 3 → ℝ))
    (hS_two : ∀ x ∈ S, ∃ L₁ ∈ ℒ, ∃ L₂ ∈ ℒ, L₁ ≠ L₂ ∧ x ∈ L₁ ∧ x ∈ L₂)
    (hcell_cap : ∀ i : Fin m,
      ((S.filter fun x => MvPolynomial.eval x P ≠ 0 ∧ cell x = i).card : ℝ) ≤
        C₁' * s / (D : ℝ) ^ 3)
    (hD_lb : 64 * C₁' * (ℒ.card : ℝ) ^ 2 / s ≤ (D : ℝ)) :
    ((S.filter fun x => MvPolynomial.eval x P ≠ 0).card : ℝ) ≤ s / 4 := by
  let Scell : Finset (Fin 3 → ℝ) := S.filter fun x => MvPolynomial.eval x P ≠ 0
  let Si : Fin m → Finset (Fin 3 → ℝ) := fun i =>
    S.filter fun x => MvPolynomial.eval x P ≠ 0 ∧ cell x = i
  let Li : Fin m → Finset (Set (Fin 3 → ℝ)) := fun i =>
    ℒ.filter fun L => ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i
  have hScell_sum : Scell.card = ∑ i : Fin m, (Si i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := cell) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ext x
    simp [Scell, Si, and_assoc]
  have hinc_sum : ∑ i : Fin m, (Li i).card ≤ (D + 1) * ℒ.card := by
    have hswap : ∑ i : Fin m, (Li i).card =
        ∑ L ∈ ℒ, ((Finset.univ : Finset (Fin m)).filter fun i =>
          ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i).card := by
      simp only [Li, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap]
    calc ∑ L ∈ ℒ, ((Finset.univ : Finset (Fin m)).filter fun i =>
            ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i).card
        ≤ ∑ _L ∈ ℒ, (D + 1) := by
          refine Finset.sum_le_sum fun L hL => ?_
          obtain ⟨p, d, _, hLeq⟩ := hlines L hL
          have h1 := transverse_line_cells_le P m cell hseg hLeq
            ((Finset.univ : Finset (Fin m)).filter fun i =>
              ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 ∧ cell x = i)
            (fun i hi => (Finset.mem_filter.mp hi).2)
          omega
      _ = (D + 1) * ℒ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hSi_le_sq : ∀ i : Fin m, (Si i).card ≤ (Li i).card ^ 2 := by
    intro i
    refine card_two_rich_subset_le_sq (Li i)
      (fun L hL => hlines L (Finset.mem_filter.mp hL).1) (Si i) ?_
    intro x hx
    obtain ⟨hxS, hxne, hxcell⟩ := Finset.mem_filter.mp hx
    obtain ⟨L₁, hL₁, L₂, hL₂, hne, hx₁, hx₂⟩ := hS_two x hxS
    exact ⟨L₁, Finset.mem_filter.mpr ⟨hL₁, x, hx₁, hxne, hxcell⟩,
      L₂, Finset.mem_filter.mpr ⟨hL₂, x, hx₂, hxne, hxcell⟩, hne, hx₁, hx₂⟩
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hrad_nn : 0 ≤ C₁' * s / (D : ℝ) ^ 3 := by positivity
  have hSi_sqrt : ∀ i : Fin m,
      ((Si i).card : ℝ) ≤ Real.sqrt (C₁' * s / (D : ℝ) ^ 3) * ((Li i).card : ℝ) := by
    intro i
    have hsq1 : ((Si i).card : ℝ) ≤ ((Li i).card : ℝ) ^ 2 := by exact_mod_cast hSi_le_sq i
    have hsq2 : ((Si i).card : ℝ) ≤ C₁' * s / (D : ℝ) ^ 3 := hcell_cap i
    have hmul : ((Si i).card : ℝ) ^ 2 ≤ (C₁' * s / (D : ℝ) ^ 3) * ((Li i).card : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul hsq2 hsq1 (Nat.cast_nonneg _) hrad_nn
    have hmul' : ((Si i).card : ℝ) ^ 2 ≤
        (Real.sqrt (C₁' * s / (D : ℝ) ^ 3) * ((Li i).card : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hrad_nn]
      exact hmul
    have hnn_rhs : 0 ≤ Real.sqrt (C₁' * s / (D : ℝ) ^ 3) * ((Li i).card : ℝ) := by positivity
    exact (abs_le_of_sq_le_sq' (by nlinarith) hnn_rhs).2
  have hScell_bound : (Scell.card : ℝ) ≤
      Real.sqrt (C₁' * s / (D : ℝ) ^ 3) * ((2 * (D : ℝ)) * (ℒ.card : ℝ)) := by
    have hsum_cast : (Scell.card : ℝ) = ∑ i : Fin m, ((Si i).card : ℝ) := by
      exact_mod_cast hScell_sum
    rw [hsum_cast]
    have h1 : ∑ i : Fin m, ((Si i).card : ℝ) ≤
        ∑ i : Fin m, Real.sqrt (C₁' * s / (D : ℝ) ^ 3) * ((Li i).card : ℝ) :=
      Finset.sum_le_sum fun i _ => hSi_sqrt i
    have h2 : ∑ i : Fin m, ((Li i).card : ℝ) ≤ (2 * (D : ℝ)) * (ℒ.card : ℝ) := by
      have hcast : ∑ i : Fin m, ((Li i).card : ℝ) ≤ (((D + 1) * ℒ.card : ℕ) : ℝ) := by
        exact_mod_cast hinc_sum
      have hD1 : ((D + 1 : ℕ) : ℝ) ≤ 2 * (D : ℝ) := by
        have hnat : D + 1 ≤ 2 * D := by omega
        exact_mod_cast hnat
      calc ∑ i : Fin m, ((Li i).card : ℝ)
          ≤ ((D + 1 : ℕ) : ℝ) * (ℒ.card : ℝ) := by simpa only [Nat.cast_mul] using hcast
        _ ≤ (2 * (D : ℝ)) * (ℒ.card : ℝ) := mul_le_mul_of_nonneg_right hD1 (Nat.cast_nonneg _)
    calc ∑ i : Fin m, ((Si i).card : ℝ)
        ≤ Real.sqrt (C₁' * s / (D : ℝ) ^ 3) * ∑ i : Fin m, ((Li i).card : ℝ) := by
          rw [Finset.mul_sum]; exact h1
      _ ≤ Real.sqrt (C₁' * s / (D : ℝ) ^ 3) * ((2 * (D : ℝ)) * (ℒ.card : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
  have hsq_cell : (Scell.card : ℝ) ^ 2 ≤ (s / 4) ^ 2 := by
    have h1 : (Scell.card : ℝ) ^ 2 ≤
        (Real.sqrt (C₁' * s / (D : ℝ) ^ 3) * ((2 * (D : ℝ)) * (ℒ.card : ℝ))) ^ 2 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hScell_bound 2
    have h2 : (Real.sqrt (C₁' * s / (D : ℝ) ^ 3) * ((2 * (D : ℝ)) * (ℒ.card : ℝ))) ^ 2 =
        (4 * C₁' * (ℒ.card : ℝ) ^ 2 / (D : ℝ)) * s := by
      rw [mul_pow, Real.sq_sqrt hrad_nn]
      field_simp [ne_of_gt hD_pos]
      ring
    have h3 : 4 * C₁' * (ℒ.card : ℝ) ^ 2 / (D : ℝ) ≤ s / 16 := by
      have hDmul : 64 * C₁' * (ℒ.card : ℝ) ^ 2 ≤ (D : ℝ) * s := (div_le_iff₀ hs).mp hD_lb
      rw [div_le_iff₀ hD_pos]
      linarith
    have h4 : (4 * C₁' * (ℒ.card : ℝ) ^ 2 / (D : ℝ)) * s ≤ (s / 16) * s :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hs)
    have h5 : (s / 16) * s = (s / 4) ^ 2 := by ring
    exact h1.trans (h2.trans_le (h4.trans_eq h5))
  exact (abs_le_of_sq_le_sq' (by nlinarith) (by positivity)).2

private lemma transverse_zero_points_le
    (P : MvPolynomial (Fin 3) ℝ) {D : ℕ} (hdeg : P.totalDegree ≤ D)
    (ℒ : Finset (Set (Fin 3 → ℝ)))
    (hlines : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (S : Finset (Fin 3 → ℝ)) :
    let ℒ_out := ℒ.filter fun L => ¬ ∀ x ∈ L, MvPolynomial.eval x P = 0
    (S.filter fun x => MvPolynomial.eval x P = 0 ∧ ∃ L ∈ ℒ_out, x ∈ L).card ≤
      D * ℒ.card := by
  intro ℒ_out
  let Strans := S.filter fun x => MvPolynomial.eval x P = 0 ∧ ∃ L ∈ ℒ_out, x ∈ L
  have hsub : Strans ⊆ ℒ_out.biUnion fun L =>
      S.filter fun x => x ∈ L ∧ MvPolynomial.eval x P = 0 := by
    intro x hx
    obtain ⟨hxS, hx0, L, hLout, hxL⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_biUnion.mpr ⟨L, hLout, Finset.mem_filter.mpr ⟨hxS, hxL, hx0⟩⟩
  calc Strans.card
      ≤ ∑ L ∈ ℒ_out, (S.filter fun x => x ∈ L ∧ MvPolynomial.eval x P = 0).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _L ∈ ℒ_out, D := by
        refine Finset.sum_le_sum fun L hL => ?_
        have hmem := Finset.mem_filter.mp hL
        obtain ⟨p, d, _, hLeq⟩ := hlines L hmem.1
        have htrans : ∃ x ∈ L, MvPolynomial.eval x P ≠ 0 := by
          have hnot := hmem.2
          push Not at hnot
          exact hnot
        have hle := transverse_line_zeros_le P hLeq htrans
          (S.filter fun x => x ∈ L ∧ MvPolynomial.eval x P = 0)
          (fun x hx => (Finset.mem_filter.mp hx).2)
        exact hle.trans hdeg
    _ = D * ℒ_out.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ D * ℒ.card := Nat.mul_le_mul_left D (Finset.card_filter_le _ _)

private lemma degree_choice_bounds
    {C₁' C₂' s : ℝ} {N M : ℕ}
    (hC₁'_ge1 : 1 ≤ C₁') (hC₂'_ge1 : 1 ≤ C₂')
    (hgt : (16 * (max (256 * C₁' * C₂') 100) ^ 2) *
      ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ)) < s)
    (hs_le_M2 : s ≤ (M : ℝ) ^ 2) :
    let D : ℕ := Nat.ceil (64 * C₁' * (M : ℝ) ^ 2 / s)
    0 < s ∧ 1 ≤ M ∧ 1 ≤ D ∧
    64 * C₁' * (M : ℝ) ^ 2 / s ≤ (D : ℝ) ∧
    (D : ℝ) < Real.sqrt (M : ℝ) / (4 * Real.sqrt C₂') ∧
    (D : ℝ) ≤ Real.sqrt (M : ℝ) ∧
    C₂' * (D : ℝ) ^ 2 < (M : ℝ) / 16 := by
  intro D
  have hC₁'_pos : 0 < C₁' := lt_of_lt_of_le one_pos hC₁'_ge1
  have hC₂'_pos : 0 < C₂' := lt_of_lt_of_le one_pos hC₂'_ge1
  let A : ℝ := max (256 * C₁' * C₂') 100
  have hA_ge100 : 100 ≤ A := le_max_right _ 100
  have hA_ge : 256 * C₁' * C₂' ≤ A := le_max_left _ 100
  let C : ℝ := 16 * A ^ 2
  have hC_pos : 0 < C := by positivity
  have hs_pos : 0 < s := lt_of_le_of_lt (by positivity) hgt
  have hM_pos_nat : 1 ≤ M := by
    by_contra hM0
    have hMeq0 : M = 0 := by omega
    rw [hMeq0] at hs_le_M2
    norm_num at hs_le_M2
    linarith
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos_nat
  have hC₂_sqrt_le : Real.sqrt C₂' ≤ C₂' := by
    have h1 := Real.sqrt_le_sqrt (show C₂' ≤ C₂' ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (le_of_lt hC₂'_pos)] at h1
  have hsqrtM_gt : 8 * Real.sqrt C₂' < Real.sqrt (M : ℝ) := by
    by_contra hle
    push Not at hle
    have h8C₂_le_C : 8 * C₂' ≤ C := by
      have : 256 * C₂' ≤ A := by nlinarith
      dsimp only [C]; nlinarith
    have hM2_le : (M : ℝ) ^ 2 ≤ C * ((M : ℝ) * Real.sqrt (M : ℝ)) := by
      have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
        Real.mul_self_sqrt (le_of_lt hM_pos)
      have hM2eq : (M : ℝ) ^ 2 = Real.sqrt (M : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ)) := by
        calc (M : ℝ) ^ 2 = (M : ℝ) * (M : ℝ) := sq (M : ℝ)
          _ = (M : ℝ) * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) := by rw [hsqM]
          _ = Real.sqrt (M : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ)) := by ring
      rw [hM2eq]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hMN_nn : 0 ≤ C * ((M : ℝ) * (N : ℝ)) := by positivity
    linarith
  have hD_lb : 64 * C₁' * (M : ℝ) ^ 2 / s ≤ (D : ℝ) := Nat.le_ceil _
  have hD_pos_nat : 1 ≤ D := Nat.ceil_pos.mpr (by positivity)
  have hD_ub : (D : ℝ) < Real.sqrt (M : ℝ) / (4 * Real.sqrt C₂') := by
    have hceil_lt : (D : ℝ) < 64 * C₁' * (M : ℝ) ^ 2 / s + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1_lt : (1 : ℝ) < Real.sqrt (M : ℝ) / (8 * Real.sqrt C₂') := by
      rw [one_lt_div (by positivity)]
      exact hsqrtM_gt
    have hterm_lt : 64 * C₁' * (M : ℝ) ^ 2 / s < Real.sqrt (M : ℝ) / (8 * Real.sqrt C₂') := by
      have hs_lb : C * ((M : ℝ) * Real.sqrt (M : ℝ)) < s := by
        have hMN_nn : 0 ≤ C * ((M : ℝ) * (N : ℝ)) := by positivity
        linarith
      have hC_bound : 64 * C₁' * (8 * Real.sqrt C₂') ≤ C := by
        have h512 : 512 * C₁' * C₂' ≤ 2 * A := by linarith
        have hmul : 64 * C₁' * (8 * Real.sqrt C₂') ≤ 512 * C₁' * C₂' := by nlinarith
        dsimp only [C]
        nlinarith
      rw [div_lt_div_iff₀ hs_pos (by positivity)]
      have hM2_eq : (M : ℝ) ^ 2 = Real.sqrt (M : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ)) := by
        have hsqM := Real.mul_self_sqrt (le_of_lt hM_pos)
        calc (M : ℝ) ^ 2 = (M : ℝ) * (M : ℝ) := sq (M : ℝ)
          _ = (M : ℝ) * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) := by rw [hsqM]
          _ = Real.sqrt (M : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ)) := by ring
      calc 64 * C₁' * (M : ℝ) ^ 2 * (8 * Real.sqrt C₂')
          = (64 * C₁' * (8 * Real.sqrt C₂')) * (((M : ℝ) * Real.sqrt (M : ℝ)) * Real.sqrt (M : ℝ)) := by
              rw [hM2_eq]; ring
        _ ≤ C * (((M : ℝ) * Real.sqrt (M : ℝ)) * Real.sqrt (M : ℝ)) :=
              mul_le_mul_of_nonneg_right hC_bound (by positivity)
        _ = (C * ((M : ℝ) * Real.sqrt (M : ℝ))) * Real.sqrt (M : ℝ) := by ring
        _ < s * Real.sqrt (M : ℝ) := mul_lt_mul_of_pos_right hs_lb (Real.sqrt_pos.mpr hM_pos)
        _ = Real.sqrt (M : ℝ) * s := mul_comm _ _
    have hhalf : Real.sqrt (M : ℝ) / (8 * Real.sqrt C₂') +
        Real.sqrt (M : ℝ) / (8 * Real.sqrt C₂') = Real.sqrt (M : ℝ) / (4 * Real.sqrt C₂') := by
      ring
    linarith
  have hD_le_sqrt : (D : ℝ) ≤ Real.sqrt (M : ℝ) := by
    have hden : (1 : ℝ) ≤ 4 * Real.sqrt C₂' := by
      have h1 : (1 : ℝ) ≤ Real.sqrt C₂' := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hC₂'_ge1
      linarith
    exact le_of_lt (lt_of_lt_of_le hD_ub (div_le_self (Real.sqrt_nonneg _) hden))
  have hC₂D2 : C₂' * (D : ℝ) ^ 2 < (M : ℝ) / 16 := by
    have hDsq : (D : ℝ) ^ 2 < (M : ℝ) / (16 * C₂') := by
      have h1 : (D : ℝ) ^ 2 < (Real.sqrt (M : ℝ) / (4 * Real.sqrt C₂')) ^ 2 :=
        pow_lt_pow_left₀ hD_ub (Nat.cast_nonneg D) (by norm_num)
      have h2 : (Real.sqrt (M : ℝ) / (4 * Real.sqrt C₂')) ^ 2 = (M : ℝ) / (16 * C₂') := by
        rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hM_pos), Real.sq_sqrt (le_of_lt hC₂'_pos)]
        ring
      exact h1.trans_eq h2
    calc C₂' * (D : ℝ) ^ 2 < C₂' * ((M : ℝ) / (16 * C₂')) :=
          mul_lt_mul_of_pos_left hDsq hC₂'_pos
      _ = (M : ℝ) / 16 := by field_simp [ne_of_gt hC₂'_pos]
  exact ⟨hs_pos, hM_pos_nat, hD_pos_nat, hD_lb, hD_ub, hD_le_sqrt, hC₂D2⟩

private lemma cover_two_rich_card_le
    (P : MvPolynomial (Fin 3) ℝ)
    (ℒ ℒ_nr : Finset (Set (Fin 3 → ℝ)))
    (hlines : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (hnr_sub : ℒ_nr ⊆ ℒ.filter fun L => ∀ x ∈ L, MvPolynomial.eval x P = 0)
    (S : Finset (Fin 3 → ℝ))
    (hS_two : ∀ x ∈ S, ∃ L₁ ∈ ℒ, ∃ L₂ ∈ ℒ, L₁ ≠ L₂ ∧ x ∈ L₁ ∧ x ∈ L₂) :
    let ℒ_in := ℒ.filter fun L => ∀ x ∈ L, MvPolynomial.eval x P = 0
    let ℒ_out := ℒ.filter fun L => ¬ ∀ x ∈ L, MvPolynomial.eval x P = 0
    S.card ≤ (S.filter fun x => MvPolynomial.eval x P ≠ 0).card +
      (S.filter fun x => MvPolynomial.eval x P = 0 ∧ ∃ L ∈ ℒ_out, x ∈ L).card +
      { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard ∧
          ¬ (2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard) }.ncard +
      { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard }.ncard := by
  intro ℒ_in ℒ_out
  let S_cell_set : Set (Fin 3 → ℝ) := (S.filter fun x => MvPolynomial.eval x P ≠ 0 : Set _)
  let S_trans_set : Set (Fin 3 → ℝ) :=
    (S.filter fun x => MvPolynomial.eval x P = 0 ∧ ∃ L ∈ ℒ_out, x ∈ L : Set _)
  let S_ruled_set : Set (Fin 3 → ℝ) :=
    { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard ∧
        ¬ (2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard) }
  let S_nr_set : Set (Fin 3 → ℝ) :=
    { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard }
  have hS_cover : (S : Set (Fin 3 → ℝ)) ⊆ S_cell_set ∪ S_trans_set ∪ S_ruled_set ∪ S_nr_set := by
    intro x hx
    have hxS : x ∈ S := Finset.mem_coe.mp hx
    by_cases hP0 : MvPolynomial.eval x P = 0
    · by_cases hout : ∃ L ∈ ℒ_out, x ∈ L
      · exact Or.inl (Or.inl (Or.inr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hxS, hP0, hout⟩))))
      · have hx_in : 2 ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard := by
          rw [two_rich_iff_exists_pair]
          obtain ⟨L₁, hL₁, L₂, hL₂, hne, hx₁, hx₂⟩ := hS_two x hxS
          have hL₁_in : L₁ ∈ ℒ_in := by
            refine Finset.mem_filter.mpr ⟨hL₁, ?_⟩
            by_contra hnot
            exact hout ⟨L₁, Finset.mem_filter.mpr ⟨hL₁, hnot⟩, hx₁⟩
          have hL₂_in : L₂ ∈ ℒ_in := by
            refine Finset.mem_filter.mpr ⟨hL₂, ?_⟩
            by_contra hnot
            exact hout ⟨L₂, Finset.mem_filter.mpr ⟨hL₂, hnot⟩, hx₂⟩
          exact ⟨L₁, hL₁_in, L₂, hL₂_in, hne, hx₁, hx₂⟩
        by_cases hnr : 2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard
        · exact Or.inr hnr
        · exact Or.inl (Or.inr ⟨hx_in, hnr⟩)
    · exact Or.inl (Or.inl (Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hxS, hP0⟩))))
  have hfin_cell : S_cell_set.Finite := Finset.finite_toSet _
  have hfin_trans : S_trans_set.Finite := Finset.finite_toSet _
  have hfin_in : { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard }.Finite :=
    finite_two_rich_points ℒ_in (fun L hL => hlines L (Finset.mem_filter.mp hL).1)
  have hfin_ruled : S_ruled_set.Finite := Set.Finite.subset hfin_in fun _ h => h.1
  have hnr_sub_L : ℒ_nr ⊆ ℒ := hnr_sub.trans (Finset.filter_subset _ _)
  have hfin_nr : S_nr_set.Finite :=
    finite_two_rich_points ℒ_nr (fun L hL => hlines L (hnr_sub_L hL))
  have h1 : (S : Set (Fin 3 → ℝ)).ncard ≤ (S_cell_set ∪ S_trans_set ∪ S_ruled_set ∪ S_nr_set).ncard :=
    Set.ncard_le_ncard hS_cover (((hfin_cell.union hfin_trans).union hfin_ruled).union hfin_nr)
  have h2 := Set.ncard_union_le (S_cell_set ∪ S_trans_set ∪ S_ruled_set) S_nr_set
  have h3 := Set.ncard_union_le (S_cell_set ∪ S_trans_set) S_ruled_set
  have h4 := Set.ncard_union_le S_cell_set S_trans_set
  rw [Set.ncard_coe_finset] at h1
  have hcell_eq : S_cell_set.ncard = (S.filter fun x => MvPolynomial.eval x P ≠ 0).card :=
    Set.ncard_coe_finset _
  have htrans_eq : S_trans_set.ncard =
      (S.filter fun x => MvPolynomial.eval x P = 0 ∧ ∃ L ∈ ℒ_out, x ∈ L).card :=
    Set.ncard_coe_finset _
  have hcomb : S.card ≤ S_cell_set.ncard + S_trans_set.ncard + S_ruled_set.ncard + S_nr_set.ncard := by
    omega
  rw [hcell_eq, htrans_eq] at hcomb
  exact hcomb

private lemma subset_plane_regulus_inherit
    {N : ℕ} {ℒ ℳ : Finset (Set (Fin 3 → ℝ))} (hsub : ℳ ⊆ ℒ)
    (hplane : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      { L | L ∈ ℒ ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.ncard ≤ N)
    (hreg : ∀ L₁ L₂ L₃ : Set (Fin 3 → ℝ),
      (∀ L ∈ ({L₁, L₂, L₃} : Set (Set (Fin 3 → ℝ))),
        ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
      (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
        let pl := { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }
        ¬ (L₁ ⊆ pl ∧ L₂ ⊆ pl) ∧ ¬ (L₁ ⊆ pl ∧ L₃ ⊆ pl) ∧ ¬ (L₂ ⊆ pl ∧ L₃ ⊆ pl)) →
      { L | L ∈ ℒ ∧ (L ∩ L₁).Nonempty ∧ (L ∩ L₂).Nonempty ∧ (L ∩ L₃).Nonempty }.ncard ≤
        2 * N) :
    (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      { L | L ∈ ℳ ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.ncard ≤ N) ∧
    (∀ L₁ L₂ L₃ : Set (Fin 3 → ℝ),
      (∀ L ∈ ({L₁, L₂, L₃} : Set (Set (Fin 3 → ℝ))),
        ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
      (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
        let pl := { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }
        ¬ (L₁ ⊆ pl ∧ L₂ ⊆ pl) ∧ ¬ (L₁ ⊆ pl ∧ L₃ ⊆ pl) ∧ ¬ (L₂ ⊆ pl ∧ L₃ ⊆ pl)) →
      { L | L ∈ ℳ ∧ (L ∩ L₁).Nonempty ∧ (L ∩ L₂).Nonempty ∧ (L ∩ L₃).Nonempty }.ncard ≤
        2 * N) := by
  refine ⟨fun a b c d habc => ?_, fun L₁ L₂ L₃ h123 hskew => ?_⟩
  · refine (Set.ncard_le_ncard ?_ ?_).trans (hplane a b c d habc)
    · intro L hL; exact ⟨hsub hL.1, hL.2⟩
    · exact Set.Finite.subset (Finset.finite_toSet ℒ) fun L hL => hL.1
  · refine (Set.ncard_le_ncard ?_ ?_).trans (hreg L₁ L₂ L₃ h123 hskew)
    · intro L hL; exact ⟨hsub hL.1, hL.2⟩
    · exact Set.Finite.subset (Finset.finite_toSet ℒ) fun L hL => hL.1

private lemma inductive_two_rich_bound
    (h1 : H1) (h2 : H2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ (M : ℕ) (ℒ : Finset (Set (Fin 3 → ℝ))),
        ℒ.card = M →
        (∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
        (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
          { L | L ∈ ℒ ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.ncard ≤ N) →
        (∀ L₁ L₂ L₃ : Set (Fin 3 → ℝ),
          (∀ L ∈ ({L₁, L₂, L₃} : Set (Set (Fin 3 → ℝ))),
            ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
          (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
            let pl := { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }
            ¬ (L₁ ⊆ pl ∧ L₂ ⊆ pl) ∧ ¬ (L₁ ⊆ pl ∧ L₃ ⊆ pl) ∧ ¬ (L₂ ⊆ pl ∧ L₃ ⊆ pl)) →
          { L | L ∈ ℒ ∧ (L ∩ L₁).Nonempty ∧ (L ∩ L₂).Nonempty ∧ (L ∩ L₃).Nonempty }.ncard ≤
            2 * N) →
        ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) ≤
          C * ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ)) := by
  obtain ⟨C₁, _, hPart⟩ := h1
  obtain ⟨C₂, _, hAlg⟩ := h2
  let C₁' : ℝ := max C₁ 1
  let C₂' : ℝ := max C₂ 1
  have hC₁'_ge1 : 1 ≤ C₁' := le_max_right C₁ 1
  have hC₂'_ge1 : 1 ≤ C₂' := le_max_right C₂ 1
  have hC₁'_pos : 0 < C₁' := lt_of_lt_of_le one_pos hC₁'_ge1
  have hC₂'_pos : 0 < C₂' := lt_of_lt_of_le one_pos hC₂'_ge1
  have hC₁_le : C₁ ≤ C₁' := le_max_left C₁ 1
  have hC₂_le : C₂ ≤ C₂' := le_max_left C₂ 1
  let A : ℝ := max (256 * C₁' * C₂') 100
  have hA_ge100 : 100 ≤ A := le_max_right _ 100
  have hA_ge : 256 * C₁' * C₂' ≤ A := le_max_left _ 100
  let C : ℝ := 16 * A ^ 2
  have hC_pos : 0 < C := by positivity
  have h4C₂_le_C : 4 * C₂' ≤ C := by
    have : 256 * C₂' ≤ A := by nlinarith
    dsimp only [C]; nlinarith
  have h4_le_C : (4 : ℝ) ≤ C := by linarith
  refine ⟨C, hC_pos, fun N hN M => ?_⟩
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro ℒ hcard hlines hplane hreg
    have hS_fin := finite_two_rich_points ℒ hlines
    let S : Finset (Fin 3 → ℝ) := hS_fin.toFinset
    have hS_ncard : ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) = (S.card : ℝ) := by
      have hnat : { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard = S.card := by
        rw [← Set.ncard_coe_finset S, Set.Finite.coe_toFinset]
      exact_mod_cast hnat
    rw [hS_ncard]
    by_contra hgt
    push Not at hgt
    let s : ℝ := (S.card : ℝ)
    have hS_two : ∀ x ∈ S, ∃ L₁ ∈ ℒ, ∃ L₂ ∈ ℒ, L₁ ≠ L₂ ∧ x ∈ L₁ ∧ x ∈ L₂ := fun x hx =>
      (two_rich_iff_exists_pair ℒ x).mp (hS_fin.mem_toFinset.mp hx)
    have hs_le_M2 : s ≤ (M : ℝ) ^ 2 := by
      have hnat := card_two_rich_subset_le_sq ℒ hlines S hS_two
      rw [hcard] at hnat
      change (S.card : ℝ) ≤ (M : ℝ) ^ 2
      exact_mod_cast hnat
    obtain ⟨hs_pos, hM_pos_nat, hD_pos_nat, hD_lb, _, hD_le_sqrt, hC₂D2⟩ :=
      degree_choice_bounds hC₁'_ge1 hC₂'_ge1 hgt hs_le_M2
    let D : ℕ := Nat.ceil (64 * C₁' * (M : ℝ) ^ 2 / s)
    obtain ⟨P, m, cell, hPne, hPdeg, hseg, hcell_cap⟩ := hPart S D hD_pos_nat
    have hScell_le : ((S.filter fun x => MvPolynomial.eval x P ≠ 0).card : ℝ) ≤ s / 4 := by
      refine cellular_double_count hC₁'_pos hs_pos hD_pos_nat P hPdeg cell hseg ℒ hlines S hS_two
        (fun i => (hcell_cap i).trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₁_le (le_of_lt hs_pos)) (by positivity))) ?_
      rw [hcard]; exact hD_lb
    let ℒ_in := ℒ.filter fun L => ∀ x ∈ L, MvPolynomial.eval x P = 0
    let ℒ_out := ℒ.filter fun L => ¬ ∀ x ∈ L, MvPolynomial.eval x P = 0
    have hStrans_le :
        ((S.filter fun x => MvPolynomial.eval x P = 0 ∧ ∃ L ∈ ℒ_out, x ∈ L).card : ℝ) ≤ s / 4 := by
      have hnat := transverse_zero_points_le P hPdeg ℒ hlines S
      rw [hcard] at hnat
      have hcast :
          ((S.filter fun x => MvPolynomial.eval x P = 0 ∧ ∃ L ∈ ℒ_out, x ∈ L).card : ℝ) ≤
            (D : ℝ) * (M : ℝ) := by exact_mod_cast hnat
      have hDM : (D : ℝ) * (M : ℝ) ≤ (M : ℝ) * Real.sqrt (M : ℝ) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hD_le_sqrt (Nat.cast_nonneg M)
      have h4M : 4 * ((M : ℝ) * Real.sqrt (M : ℝ)) ≤
          C * ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ)) := by
        have hMN_nn : 0 ≤ C * ((M : ℝ) * (N : ℝ)) := mul_nonneg (le_of_lt hC_pos)
          (mul_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg N))
        have hle := mul_le_mul_of_nonneg_right h4_le_C
          (mul_nonneg (Nat.cast_nonneg M) (Real.sqrt_nonneg (M : ℝ)))
        linarith
      linarith
    have ⟨hplane_in, hreg_in⟩ := subset_plane_regulus_inherit
      (Finset.filter_subset (fun L => ∀ x ∈ L, MvPolynomial.eval x P = 0) ℒ) hplane hreg
    obtain ⟨ℒ_nr, hnr_sub, hnr_card, hruled_bound⟩ :=
      hAlg N D P ℒ_in hN hD_pos_nat hPne hPdeg
        (fun L hL => hlines L (Finset.mem_filter.mp hL).1)
        (fun L hL => (Finset.mem_filter.mp hL).2)
        hplane_in hreg_in
    have hnr_le_M16 : (ℒ_nr.card : ℝ) ≤ (M : ℝ) / 16 :=
      le_of_lt (lt_of_le_of_lt (hnr_card.trans (mul_le_mul_of_nonneg_right hC₂_le (sq_nonneg _))) hC₂D2)
    have hnr_lt_M : ℒ_nr.card < M := by
      have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos_nat
      have hlt_real : (ℒ_nr.card : ℝ) < (M : ℝ) := by linarith
      exact_mod_cast hlt_real
    have hnr_sub_L : ℒ_nr ⊆ ℒ := hnr_sub.trans (Finset.filter_subset _ _)
    have ⟨hplane_nr, hreg_nr⟩ := subset_plane_regulus_inherit hnr_sub_L hplane hreg
    have hSnr_le : ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard }.ncard : ℝ) ≤ s / 16 := by
      have hih := ih ℒ_nr.card hnr_lt_M ℒ_nr rfl (fun L hL => hlines L (hnr_sub_L hL))
        hplane_nr hreg_nr
      have hsq_le : Real.sqrt (ℒ_nr.card : ℝ) ≤ Real.sqrt (M : ℝ) :=
        Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) M])
      have h1 : (ℒ_nr.card : ℝ) * Real.sqrt (ℒ_nr.card : ℝ) ≤ ((M : ℝ) / 16) * Real.sqrt (M : ℝ) :=
        mul_le_mul hnr_le_M16 hsq_le (Real.sqrt_nonneg _) (div_nonneg (Nat.cast_nonneg M) (by norm_num))
      have h2 : (ℒ_nr.card : ℝ) * (N : ℝ) ≤ ((M : ℝ) / 16) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hnr_le_M16 (Nat.cast_nonneg N)
      have hsum : (ℒ_nr.card : ℝ) * Real.sqrt (ℒ_nr.card : ℝ) + (ℒ_nr.card : ℝ) * (N : ℝ) ≤
          (1 / 16) * ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ)) := by linarith
      have h3 : C * ((ℒ_nr.card : ℝ) * Real.sqrt (ℒ_nr.card : ℝ) + (ℒ_nr.card : ℝ) * (N : ℝ)) ≤
          (1 / 16) * (C * ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ))) := by
        calc C * ((ℒ_nr.card : ℝ) * Real.sqrt (ℒ_nr.card : ℝ) + (ℒ_nr.card : ℝ) * (N : ℝ))
            ≤ C * ((1 / 16) * ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ))) :=
              mul_le_mul_of_nonneg_left hsum (le_of_lt hC_pos)
          _ = (1 / 16) * (C * ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ))) := by ring
      linarith
    have hSruled_le :
        ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard ∧
            ¬ (2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard) }.ncard : ℝ) ≤ s / 4 := by
      have hLin_le : (ℒ_in.card : ℝ) ≤ (M : ℝ) := by
        have hnat : ℒ_in.card ≤ M := by rw [← hcard]; exact Finset.card_filter_le _ _
        exact_mod_cast hnat
      have hMD : (ℒ_in.card : ℝ) * (D : ℝ) ≤ (M : ℝ) * Real.sqrt (M : ℝ) :=
        mul_le_mul hLin_le hD_le_sqrt (Nat.cast_nonneg D) (Nat.cast_nonneg M)
      have hMN : (ℒ_in.card : ℝ) * (N : ℝ) ≤ (M : ℝ) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hLin_le (Nat.cast_nonneg N)
      have hsum_nn : 0 ≤ (ℒ_in.card : ℝ) * (D : ℝ) + (ℒ_in.card : ℝ) * (N : ℝ) :=
        add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      have h1 : C₂ * ((ℒ_in.card : ℝ) * (D : ℝ) + (ℒ_in.card : ℝ) * (N : ℝ)) ≤
          C₂' * ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ)) :=
        mul_le_mul hC₂_le (by linarith) hsum_nn (le_of_lt hC₂'_pos)
      have hRHS_nn : 0 ≤ (M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ) :=
        add_nonneg (mul_nonneg (Nat.cast_nonneg M) (Real.sqrt_nonneg _))
          (mul_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg N))
      have h2 : 4 * (C₂' * ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ))) ≤
          C * ((M : ℝ) * Real.sqrt (M : ℝ) + (M : ℝ) * (N : ℝ)) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right h4C₂_le_C hRHS_nn
      linarith
    have htot_nat : S.card ≤ (S.filter fun x => MvPolynomial.eval x P ≠ 0).card +
        (S.filter fun x => MvPolynomial.eval x P = 0 ∧ ∃ L ∈ ℒ_out, x ∈ L).card +
        { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard ∧
            ¬ (2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard) }.ncard +
        { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard }.ncard :=
      cover_two_rich_card_le P ℒ ℒ_nr hlines hnr_sub S hS_two
    have htot_real : (S.card : ℝ) ≤ ((S.filter fun x => MvPolynomial.eval x P ≠ 0).card : ℝ) +
        ((S.filter fun x => MvPolynomial.eval x P = 0 ∧ ∃ L ∈ ℒ_out, x ∈ L).card : ℝ) +
        ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_in ∧ x ∈ L }.ncard ∧
            ¬ (2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard) }.ncard : ℝ) +
        ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ_nr ∧ x ∈ L }.ncard }.ncard : ℝ) := by
      exact_mod_cast htot_nat
    change s ≤ _ at htot_real
    linarith

end

theorem main : H1 → H2 → OMA.R_Erdos95_erdos_95_variants_guth_katz_R1.H1 := by
  intro h1 h2
  obtain ⟨C, hC_pos, hbound⟩ := inductive_two_rich_bound h1 h2
  refine ⟨2 * C, by linarith, fun N ℒ hN hcard hlines hplane hreg => ?_⟩
  have h1 := hbound N hN ℒ.card ℒ rfl hlines hplane hreg
  have hcard_real : (ℒ.card : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcard
  have hsqrt_le : Real.sqrt (ℒ.card : ℝ) ≤ (N : ℝ) := by
    have h := Real.sqrt_le_sqrt hcard_real
    rwa [Real.sqrt_sq (Nat.cast_nonneg N)] at h
  have hterm1 : (ℒ.card : ℝ) * Real.sqrt (ℒ.card : ℝ) ≤ (N : ℝ) ^ 3 := by
    calc (ℒ.card : ℝ) * Real.sqrt (ℒ.card : ℝ)
        ≤ (N : ℝ) ^ 2 * (N : ℝ) := mul_le_mul hcard_real hsqrt_le (Real.sqrt_nonneg _) (by positivity)
      _ = (N : ℝ) ^ 3 := by ring
  have hterm2 : (ℒ.card : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ 3 := by
    calc (ℒ.card : ℝ) * (N : ℝ)
        ≤ (N : ℝ) ^ 2 * (N : ℝ) := mul_le_mul_of_nonneg_right hcard_real (Nat.cast_nonneg N)
      _ = (N : ℝ) ^ 3 := by ring
  calc ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ)
      ≤ C * ((ℒ.card : ℝ) * Real.sqrt (ℒ.card : ℝ) + (ℒ.card : ℝ) * (N : ℝ)) := h1
    _ ≤ C * ((N : ℝ) ^ 3 + (N : ℝ) ^ 3) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hC_pos)
    _ = 2 * C * (N : ℝ) ^ 3 := by ring

end OMA.R_Erdos95_erdos_95_variants_guth_katz_R1_H1_R1
