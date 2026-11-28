import FormalConjectures.ErdosProblems.«95»

/-!
Reduction of `Erdos95.erdos_95.variants.guth_katz` (Guth and Katz, Ann. of Math. 181 (2015),
155-190) to the Guth-Katz 3D line-incidence bounds for 2-rich points (`H1`, Theorem 2.10) and
`k`-rich points in the range `3 <= k <= N` (`H2`, Theorem 2.11).

The Elekes-Sharir reduction is proved completely in Lean:
1. Exact identity `4 * sum_{u in distanceSet P} (distanceMultiplicity P u)^2 = |Q_ord(P)|`.
2. Decomposition into translations (`<= |P|^3`) and proper non-translation quadruples.
3. Construction of the `|P|^2`-line Elekes-Sharir family in `R^3`, injectivity, injection
   from proper non-translation quadruples into ordered intersecting pairs of distinct lines,
   and point-richness upper bound `<= |P|`.
4. Elementary proofs that every affine plane contains `<= |P|` lines of the family and every
   regulus (transversals to three pairwise skew lines) contains `<= 2 * |P|` lines of the family.
5. Double-counting intersecting line pairs by point richness `m * (m - 1) = sum_{k=2}^m 2*(k-1)`
   and telescoping the harmonic sum `sum_{k=3}^N 1/k <= Real.log N`.
-/

namespace OMA.R_Erdos95_erdos_95_variants_guth_katz_R1

open scoped EuclideanGeometry

/- === Section 1: Guth-Katz 3D Line-Incidence Hypotheses === -/

/- Guth-Katz (2015), Theorem 2.10: any family of at most `N^2` affine lines in `R^3` with at
most `N` lines in any affine plane and at most `2 * N` lines meeting any three pairwise skew
affine lines (a regulus) determines at most `C * N^3` 2-rich points. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (ℒ : Finset (Set (Fin 3 → ℝ))),
    1 ≤ N → ℒ.card ≤ N ^ 2 →
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
    ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) ≤ C * (N : ℝ) ^ 3

/- Guth-Katz (2015), Theorem 2.11: any family of at most `N^2` affine lines in `R^3` with at
most `N` lines in any affine plane determines at most `C * N^3 / k^2` `k`-rich points for
every `3 <= k <= N`. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N k : ℕ) (ℒ : Finset (Set (Fin 3 → ℝ))),
    3 ≤ k → k ≤ N → ℒ.card ≤ N ^ 2 →
    (∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
    (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      { L | L ∈ ℒ ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.ncard ≤ N) →
    ({ x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) ≤
      C * (N : ℝ) ^ 3 / (k : ℝ) ^ 2

/- === Section 2: Elementary 2D/3D Coordinate and Quadratic-Root Helpers === -/

/- Squared Euclidean distance in `R^2` in coordinates. -/
lemma dist_sq_eq (p q : ℝ²) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/- Coordinate extensionality in `R^2`. -/
lemma eq_of_coords {p q : ℝ²} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/- Coordinate extensionality in `R^3`. -/
lemma eq_fin3 {x y : Fin 3 → ℝ} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  ext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2

/- A non-degenerate real quadratic polynomial has at most two distinct roots. -/
lemma three_distinct_quad_roots_false {A B C t₁ t₂ t₃ : ℝ} (hA : A ≠ 0)
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    (hr1 : A * t₁ ^ 2 + B * t₁ + C = 0)
    (hr2 : A * t₂ ^ 2 + B * t₂ + C = 0)
    (hr3 : A * t₃ ^ 2 + B * t₃ + C = 0) : False := by
  have h12' : A * (t₁ + t₂) + B = 0 := by
    have hmul : (t₁ - t₂) * (A * (t₁ + t₂) + B) = 0 := by
      linear_combination hr1 - hr2
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h12)
  have h13' : A * (t₁ + t₃) + B = 0 := by
    have hmul : (t₁ - t₃) * (A * (t₁ + t₃) + B) = 0 := by
      linear_combination hr1 - hr3
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h13)
  have h23' : A * (t₂ - t₃) = 0 := by
    linear_combination h12' - h13'
  exact (mul_eq_zero.mp h23').elim hA (sub_ne_zero.mpr h23)

/- Uniqueness of solution to a 2x2 real linear system with nonzero determinant. -/
lemma linear2_unique {a₁ b₁ c₁ a₂ b₂ c₂ x₁ y₁ x₂ y₂ : ℝ}
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (h1 : a₁ * x₁ + b₁ * y₁ = c₁) (h2 : a₂ * x₁ + b₂ * y₁ = c₂)
    (h1' : a₁ * x₂ + b₁ * y₂ = c₁) (h2' : a₂ * x₂ + b₂ * y₂ = c₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hx : (a₁ * b₂ - a₂ * b₁) * (x₁ - x₂) = 0 := by
    linear_combination b₂ * (h1 - h1') - b₁ * (h2 - h2')
  have hy : (a₁ * b₂ - a₂ * b₁) * (y₁ - y₂) = 0 := by
    linear_combination a₁ * (h2 - h2') - a₂ * (h1 - h1')
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hdet),
    sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hdet)⟩

/- Any finite set with cardinality exceeding 2 contains three pairwise distinct elements. -/
lemma exists_three_distinct_of_two_lt_card {α : Type*} {S : Finset α} (hS : 2 < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have h1 : 1 < (S.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase a).card)
  have h2 : 0 < ((S.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hb]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp h2
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hbS : b ∈ S := (Finset.mem_erase.mp hb).2
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcS : c ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
  exact ⟨a, ha, b, hbS, c, hcS, hba.symm, hca.symm, hcb.symm⟩

/- A line and a circle in `R^2` intersect in at most 2 points of any finite set `P`. -/
lemma card_filter_line_circle_le_two (P : Finset ℝ²) (vx vy c bx by_ r : ℝ)
    (hv : vx ≠ 0 ∨ vy ≠ 0)
    [DecidablePred fun q : ℝ² =>
      vx * q 0 + vy * q 1 = c ∧ (q 0 - bx) ^ 2 + (q 1 - by_) ^ 2 = r] :
    (P.filter fun q : ℝ² =>
      vx * q 0 + vy * q 1 = c ∧ (q 0 - bx) ^ 2 + (q 1 - by_) ^ 2 = r).card ≤ 2 := by
  by_contra hgt
  have hcard : 2 < (P.filter fun q : ℝ² =>
      vx * q 0 + vy * q 1 = c ∧ (q 0 - bx) ^ 2 + (q 1 - by_) ^ 2 = r).card := by omega
  obtain ⟨q₁, hq₁, q₂, hq₂, q₃, hq₃, h12, h13, h23⟩ :=
    exists_three_distinct_of_two_lt_card hcard
  have hD_pos : 0 < vx ^ 2 + vy ^ 2 := by
    rcases hv with hv | hv
    · have : 0 < vx ^ 2 := sq_pos_of_ne_zero hv
      nlinarith [sq_nonneg vy]
    · have : 0 < vy ^ 2 := sq_pos_of_ne_zero hv
      nlinarith [sq_nonneg vx]
  have hD_ne : vx ^ 2 + vy ^ 2 ≠ 0 := ne_of_gt hD_pos
  set D : ℝ := vx ^ 2 + vy ^ 2
  set u0 : ℝ := vx * c - D * bx
  set u1 : ℝ := vy * c - D * by_
  set B : ℝ := 2 * (-vy * u0 + vx * u1)
  set C : ℝ := u0 ^ 2 + u1 ^ 2 - D ^ 2 * r
  let param : ℝ² → ℝ := fun q => -vy * q 0 + vx * q 1
  have hparam_inj : ∀ p q : ℝ², vx * p 0 + vy * p 1 = c → vx * q 0 + vy * q 1 = c →
      param p = param q → p = q := by
    intro p q hp hq hpar
    have hdet : vx * vx - (-vy) * vy ≠ 0 := by
      have : vx * vx - (-vy) * vy = D := by ring
      rw [this]
      exact hD_ne
    have hxy := linear2_unique hdet hp hpar hq rfl
    exact eq_of_coords hxy.1 hxy.2
  have hquad : ∀ q : ℝ², vx * q 0 + vy * q 1 = c → (q 0 - bx) ^ 2 + (q 1 - by_) ^ 2 = r →
      D * (param q) ^ 2 + B * (param q) + C = 0 := by
    intro q hline hcirc
    have h0 : D * q 0 = vx * c - vy * param q := by
      dsimp only [D, param]
      linear_combination vx * hline
    have h1 : D * q 1 = vy * c + vx * param q := by
      dsimp only [D, param]
      linear_combination vy * hline
    have h0' : D * (q 0 - bx) = -vy * param q + u0 := by
      dsimp only [u0]
      linarith
    have h1' : D * (q 1 - by_) = vx * param q + u1 := by
      dsimp only [u1]
      linarith
    have hsq : (-vy * param q + u0) ^ 2 + (vx * param q + u1) ^ 2 = D ^ 2 * r := by
      rw [← h0', ← h1']
      linear_combination D ^ 2 * hcirc
    dsimp only [B, C, D] at hsq ⊢
    linear_combination hsq
  have hq₁' := (Finset.mem_filter.mp hq₁).2
  have hq₂' := (Finset.mem_filter.mp hq₂).2
  have hq₃' := (Finset.mem_filter.mp hq₃).2
  exact three_distinct_quad_roots_false hD_ne
    (fun h => h12 (hparam_inj q₁ q₂ hq₁'.1 hq₂'.1 h))
    (fun h => h13 (hparam_inj q₁ q₃ hq₁'.1 hq₃'.1 h))
    (fun h => h23 (hparam_inj q₂ q₃ hq₂'.1 hq₃'.1 h))
    (hquad q₁ hq₁'.1 hq₁'.2) (hquad q₂ hq₂'.1 hq₂'.2) (hquad q₃ hq₃'.1 hq₃'.2)

/- Two circles with distinct centers in `R^2` intersect in at most 2 points of `P`. -/
lemma card_filter_two_circles_le_two (P : Finset ℝ²) (b₁ b₂ : ℝ²) (hb : b₁ ≠ b₂) (r₁ r₂ : ℝ)
    [DecidablePred fun q : ℝ² =>
      (q 0 - b₁ 0) ^ 2 + (q 1 - b₁ 1) ^ 2 = r₁ ∧
      (q 0 - b₂ 0) ^ 2 + (q 1 - b₂ 1) ^ 2 = r₂] :
    (P.filter fun q : ℝ² =>
      (q 0 - b₁ 0) ^ 2 + (q 1 - b₁ 1) ^ 2 = r₁ ∧
      (q 0 - b₂ 0) ^ 2 + (q 1 - b₂ 1) ^ 2 = r₂).card ≤ 2 := by
  classical
  set vx : ℝ := 2 * (b₂ 0 - b₁ 0)
  set vy : ℝ := 2 * (b₂ 1 - b₁ 1)
  set c : ℝ := r₁ - r₂ - (b₁ 0 ^ 2 + b₁ 1 ^ 2) + (b₂ 0 ^ 2 + b₂ 1 ^ 2)
  have hv : vx ≠ 0 ∨ vy ≠ 0 := by
    by_contra h
    have h0 : b₁ 0 = b₂ 0 := by
      have : vx = 0 := by tauto
      dsimp only [vx] at this
      linarith
    have h1 : b₁ 1 = b₂ 1 := by
      have : vy = 0 := by tauto
      dsimp only [vy] at this
      linarith
    exact hb (eq_of_coords h0 h1)
  refine le_trans (Finset.card_le_card ?_)
    (card_filter_line_circle_le_two P vx vy c (b₁ 0) (b₁ 1) r₁ hv)
  intro q hq
  obtain ⟨hqP, h1, h2⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨hqP, ?_, h1⟩
  dsimp only [vx, vy, c]
  linear_combination h1 - h2

/- Counting helper: if every `p in P` has at most `m` partners `q in P`, then at most `m * |P|`
pairs in `P x P` satisfy the relation. -/
lemma card_filter_prod_le_mul_left {α : Type*} (P : Finset α) (R : α → α → Prop) (m : ℕ)
    [inst : DecidablePred fun pq : α × α => R pq.1 pq.2]
    (h : ∀ p ∈ P, ∀ [DecidablePred fun q : α => R p q], (P.filter fun q => R p q).card ≤ m) :
    ((P ×ˢ P).filter fun pq => R pq.1 pq.2).card ≤ m * P.card := by
  rw [Finset.card_filter, Finset.sum_product]
  have hrow : ∀ p ∈ P, (∑ q ∈ P, @ite ℕ (R p q) (inst (p, q)) 1 0) ≤ m := by
    intro p hp
    let _ : DecidablePred (fun q => R p q) := fun q => inst (p, q)
    rw [← Finset.card_filter]
    exact h p hp
  calc
    ∑ p ∈ P, ∑ q ∈ P, @ite ℕ (R (p, q).1 (p, q).2) (inst (p, q)) 1 0
        ≤ ∑ _p ∈ P, m := Finset.sum_le_sum fun p hp => hrow p hp
    _ = m * P.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]

/- Symmetric counting helper fixing the second coordinate `q in P`. -/
lemma card_filter_prod_le_mul_right {α : Type*} (P : Finset α) (R : α → α → Prop) (m : ℕ)
    [inst : DecidablePred fun pq : α × α => R pq.1 pq.2]
    (h : ∀ q ∈ P, ∀ [DecidablePred fun p : α => R p q], (P.filter fun p => R p q).card ≤ m) :
    ((P ×ˢ P).filter fun pq => R pq.1 pq.2).card ≤ m * P.card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  have hcol : ∀ q ∈ P, (∑ p ∈ P, @ite ℕ (R p q) (inst (p, q)) 1 0) ≤ m := by
    intro q hq
    let _ : DecidablePred (fun p => R p q) := fun p => inst (p, q)
    rw [← Finset.card_filter]
    exact h q hq
  calc
    ∑ q ∈ P, ∑ p ∈ P, @ite ℕ (R (p, q).1 (p, q).2) (inst (p, q)) 1 0
        ≤ ∑ _q ∈ P, m := Finset.sum_le_sum fun q hq => hcol q hq
    _ = m * P.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]

/- === Section 3: The Elekes-Sharir Line Family in `R^3` === -/

/- Every Elekes-Sharir curve `L_{p,q}` is an affine line in `R^3`. -/
lemma esLine_isLine (p q : ℝ²) :
    ∃ (p₀ d : Fin 3 → ℝ), d ≠ 0 ∧
      (Set.range fun t : ℝ =>
        ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
          (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) =
        { x : Fin 3 → ℝ | ∃ t : ℝ, x = p₀ + t • d } := by
  refine ⟨![(p 0 + q 0) / 2, (p 1 + q 1) / 2, 0],
          ![-(q 1 - p 1) / 2, (q 0 - p 0) / 2, 1], ?_, ?_⟩
  · intro h
    have h2 := congr_fun h 2
    simp at h2
  · ext x
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, eq_fin3 ?_ ?_ ?_⟩ <;> simp <;> ring
    · rintro ⟨t, rfl⟩
      refine ⟨t, eq_fin3 ?_ ?_ ?_⟩ <;> simp <;> ring

/- Membership in the Elekes-Sharir line `L_{p,q}` is determined uniquely by the third coordinate. -/
lemma mem_esLine_iff (p q : ℝ²) (x : Fin 3 → ℝ) :
    x ∈ Set.range (fun t : ℝ =>
      ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
        (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ↔
      x = ![(p 0 + q 0) / 2 - x 2 * (q 1 - p 1) / 2,
            (p 1 + q 1) / 2 + x 2 * (q 0 - p 0) / 2, x 2] := by
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · intro h
    exact ⟨x 2, h.symm⟩

/- The Elekes-Sharir map `(p, q) |-> L_{p,q}` is injective. -/
lemma esLine_injective :
    Function.Injective (fun pq : ℝ² × ℝ² =>
      Set.range fun t : ℝ =>
        ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
          (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) := by
  rintro ⟨p₁, q₁⟩ ⟨p₂, q₂⟩ h
  dsimp only at h
  have h0_mem :
      ![(p₁ 0 + q₁ 0) / 2 - 0 * (q₁ 1 - p₁ 1) / 2,
        (p₁ 1 + q₁ 1) / 2 + 0 * (q₁ 0 - p₁ 0) / 2, (0 : ℝ)] ∈
      Set.range (fun t : ℝ =>
        ![(p₂ 0 + q₂ 0) / 2 - t * (q₂ 1 - p₂ 1) / 2,
          (p₂ 1 + q₂ 1) / 2 + t * (q₂ 0 - p₂ 0) / 2, t]) := by
    rw [← h]
    exact ⟨0, rfl⟩
  have h1_mem :
      ![(p₁ 0 + q₁ 0) / 2 - 1 * (q₁ 1 - p₁ 1) / 2,
        (p₁ 1 + q₁ 1) / 2 + 1 * (q₁ 0 - p₁ 0) / 2, (1 : ℝ)] ∈
      Set.range (fun t : ℝ =>
        ![(p₂ 0 + q₂ 0) / 2 - t * (q₂ 1 - p₂ 1) / 2,
          (p₂ 1 + q₂ 1) / 2 + t * (q₂ 0 - p₂ 0) / 2, t]) := by
    rw [← h]
    exact ⟨1, rfl⟩
  have h0_eq := (mem_esLine_iff p₂ q₂ _).mp h0_mem
  have h1_eq := (mem_esLine_iff p₂ q₂ _).mp h1_mem
  have h00 := congr_fun h0_eq 0
  have h01 := congr_fun h0_eq 1
  have h10 := congr_fun h1_eq 0
  have h11 := congr_fun h1_eq 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, zero_mul, one_mul] at h00 h01 h10 h11
  exact Prod.ext
    (eq_of_coords (by linarith) (by linarith))
    (eq_of_coords (by linarith) (by linarith))

/- Every proper non-translation equidistant quadruple induces an intersection of Elekes-Sharir
lines. -/
lemma esLine_inter_of_nonTrans {p₁ p₂ q₁ q₂ : ℝ²}
    (hdist : dist p₁ p₂ = dist q₁ q₂) (hnt : q₂ - q₁ ≠ p₂ - p₁) :
    ((Set.range fun t : ℝ =>
        ![(p₁ 0 + q₁ 0) / 2 - t * (q₁ 1 - p₁ 1) / 2,
          (p₁ 1 + q₁ 1) / 2 + t * (q₁ 0 - p₁ 0) / 2, t]) ∩
     (Set.range fun t : ℝ =>
        ![(p₂ 0 + q₂ 0) / 2 - t * (q₂ 1 - p₂ 1) / 2,
          (p₂ 1 + q₂ 1) / 2 + t * (q₂ 0 - p₂ 0) / 2, t])).Nonempty := by
  set u0 : ℝ := p₂ 0 - p₁ 0
  set u1 : ℝ := p₂ 1 - p₁ 1
  set v0 : ℝ := q₂ 0 - q₁ 0
  set v1 : ℝ := q₂ 1 - q₁ 1
  have hsq : u0 ^ 2 + u1 ^ 2 = v0 ^ 2 + v1 ^ 2 := by
    have hd : dist p₁ p₂ ^ 2 = dist q₁ q₂ ^ 2 := by rw [hdist]
    rw [dist_sq_eq, dist_sq_eq] at hd
    dsimp only [u0, u1, v0, v1]
    linarith
  have hne : u0 ≠ v0 ∨ u1 ≠ v1 := by
    by_contra h
    have h0 : (q₂ - q₁) 0 = (p₂ - p₁) 0 := by
      have : u0 = v0 := by tauto
      dsimp only [u0, v0] at this
      simpa using this.symm
    have h1 : (q₂ - q₁) 1 = (p₂ - p₁) 1 := by
      have : u1 = v1 := by tauto
      dsimp only [u1, v1] at this
      simpa using this.symm
    exact hnt (eq_of_coords h0 h1)
  set D : ℝ := u0 ^ 2 + u1 ^ 2 - (u0 * v0 + u1 * v1)
  have hD_pos : 0 < D := by
    have h2D : 2 * D = (u0 - v0) ^ 2 + (u1 - v1) ^ 2 := by
      dsimp only [D]
      linarith [hsq]
    have hpos : 0 < (u0 - v0) ^ 2 + (u1 - v1) ^ 2 := by
      rcases hne with hne | hne
      · have : 0 < (u0 - v0) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
        nlinarith [sq_nonneg (u1 - v1)]
      · have : 0 < (u1 - v1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
        nlinarith [sq_nonneg (u0 - v0)]
    linarith
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  set N : ℝ := u0 * v1 - u1 * v0
  set t : ℝ := N / D
  refine ⟨![(p₁ 0 + q₁ 0) / 2 - t * (q₁ 1 - p₁ 1) / 2,
            (p₁ 1 + q₁ 1) / 2 + t * (q₁ 0 - p₁ 0) / 2, t], ⟨t, rfl⟩, ⟨t, eq_fin3 ?_ ?_ ?_⟩⟩
  · simp only [Matrix.cons_val_zero]
    have hnum : D * (u0 + v0) - N * (v1 - u1) = 0 := by
      dsimp only [D, N]
      linear_combination u0 * hsq
    have hdiff : (p₂ 0 + q₂ 0) / 2 - t * (q₂ 1 - p₂ 1) / 2 -
        ((p₁ 0 + q₁ 0) / 2 - t * (q₁ 1 - p₁ 1) / 2) =
        (D * (u0 + v0) - N * (v1 - u1)) / (2 * D) := by
      dsimp only [t, u0, u1, v0, v1]
      field_simp [hD_ne]
      ring
    rw [hnum, zero_div] at hdiff
    linarith
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    have hnum : D * (u1 + v1) + N * (v0 - u0) = 0 := by
      dsimp only [D, N]
      linear_combination u1 * hsq
    have hdiff : (p₂ 1 + q₂ 1) / 2 + t * (q₂ 0 - p₂ 0) / 2 -
        ((p₁ 1 + q₁ 1) / 2 + t * (q₁ 0 - p₁ 0) / 2) =
        (D * (u1 + v1) + N * (v0 - u0)) / (2 * D) := by
      dsimp only [t, u0, u1, v0, v1]
      field_simp [hD_ne]
      ring
    rw [hnum, zero_div] at hdiff
    linarith
  · simp

/- Every point in `R^3` lies on at most `|P|` Elekes-Sharir lines of `P`. -/
lemma pointRichness_esLines_le (P : Finset ℝ²) (x : Fin 3 → ℝ)
    [DecidableEq (Set (Fin 3 → ℝ))] :
    { L : Set (Fin 3 → ℝ) |
      L ∈ (P ×ˢ P).image (fun pq : ℝ² × ℝ² =>
          Set.range fun t : ℝ =>
            ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
              (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∧
      x ∈ L }.ncard ≤ P.card := by
  let esL : ℝ² × ℝ² → Set (Fin 3 → ℝ) := fun pq =>
    Set.range fun t : ℝ =>
      ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
        (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]
  change { L : Set (Fin 3 → ℝ) | L ∈ (P ×ˢ P).image esL ∧ x ∈ L }.ncard ≤ P.card
  let _ : DecidablePred (fun pq : ℝ² × ℝ² => x ∈ esL pq) := Classical.decPred _
  have hset : { L : Set (Fin 3 → ℝ) | L ∈ (P ×ˢ P).image esL ∧ x ∈ L } =
      (((P ×ˢ P).filter fun pq => x ∈ esL pq).image esL : Finset (Set (Fin 3 → ℝ))) := by
    ext L
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨pq, hpq, rfl⟩, hx⟩
      exact ⟨pq, ⟨hpq, hx⟩, rfl⟩
    · rintro ⟨pq, ⟨hpq, hx⟩, rfl⟩
      exact ⟨⟨pq, hpq, rfl⟩, hx⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ esLine_injective]
  have hle := card_filter_prod_le_mul_left P (fun p q => x ∈ esL (p, q)) 1 (by
    intro p _ _
    refine Finset.card_le_one.mpr ?_
    intro q₁ hq₁ q₂ hq₂
    have hx₁ := (mem_esLine_iff p q₁ x).mp (Finset.mem_filter.mp hq₁).2
    have hx₂ := (mem_esLine_iff p q₂ x).mp (Finset.mem_filter.mp hq₂).2
    have h0₁ := congr_fun hx₁ 0
    have h1₁ := congr_fun hx₁ 1
    have h0₂ := congr_fun hx₂ 0
    have h1₂ := congr_fun hx₂ 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0₁ h1₁ h0₂ h1₂
    have hdet : (1 : ℝ) * 1 - (x 2) * (-(x 2)) ≠ 0 := by nlinarith [sq_nonneg (x 2)]
    have heq := linear2_unique hdet
      (c₁ := 2 * x 0 - p 0 - x 2 * p 1)
      (c₂ := 2 * x 1 - p 1 + x 2 * p 0)
      (x₁ := q₁ 0) (y₁ := q₁ 1) (x₂ := q₂ 0) (y₂ := q₂ 1)
      (by linarith) (by linarith) (by linarith) (by linarith)
    exact eq_of_coords heq.1 heq.2)
  simpa using hle

/- === Section 4: Plane and Regulus Incidence Bounds for the Elekes-Sharir Family === -/

/- Every affine plane in `R^3` contains at most `|P|` Elekes-Sharir lines of `P`. -/
lemma planeLineCount_esLines_le (P : Finset ℝ²) (a b c d : ℝ) (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    [DecidableEq (Set (Fin 3 → ℝ))] :
    { L : Set (Fin 3 → ℝ) |
      L ∈ (P ×ˢ P).image (fun pq : ℝ² × ℝ² =>
          Set.range fun t : ℝ =>
            ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
              (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∧
      L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.ncard ≤ P.card := by
  let esL : ℝ² × ℝ² → Set (Fin 3 → ℝ) := fun pq =>
    Set.range fun t : ℝ =>
      ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
        (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]
  let pl : Set (Fin 3 → ℝ) := { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }
  change { L : Set (Fin 3 → ℝ) | L ∈ (P ×ˢ P).image esL ∧ L ⊆ pl }.ncard ≤ P.card
  let _ : DecidablePred (fun pq : ℝ² × ℝ² => esL pq ⊆ pl) := Classical.decPred _
  have hset : { L : Set (Fin 3 → ℝ) | L ∈ (P ×ˢ P).image esL ∧ L ⊆ pl } =
      (((P ×ˢ P).filter fun pq => esL pq ⊆ pl).image esL : Finset (Set (Fin 3 → ℝ))) := by
    ext L
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨pq, hpq, rfl⟩, hsub⟩
      exact ⟨pq, ⟨hpq, hsub⟩, rfl⟩
    · rintro ⟨pq, ⟨hpq, hsub⟩, rfl⟩
      exact ⟨⟨pq, hpq, rfl⟩, hsub⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ esLine_injective]
  have hlin : ∀ p q : ℝ², esL (p, q) ⊆ pl →
      (a * (p 0 + q 0) + b * (p 1 + q 1) + 2 * d = 0) ∧
      (b * (q 0 - p 0) - a * (q 1 - p 1) + 2 * c = 0) := by
    intro p q hsub
    have h0 : a * ((p 0 + q 0) / 2 - 0 * (q 1 - p 1) / 2) +
        b * ((p 1 + q 1) / 2 + 0 * (q 0 - p 0) / 2) + c * 0 + d = 0 := by
      simpa [pl] using hsub ⟨0, rfl⟩
    have h1 : a * ((p 0 + q 0) / 2 - 1 * (q 1 - p 1) / 2) +
        b * ((p 1 + q 1) / 2 + 1 * (q 0 - p 0) / 2) + c * 1 + d = 0 := by
      simpa [pl] using hsub ⟨1, rfl⟩
    exact ⟨by linarith, by linarith⟩
  have hle := card_filter_prod_le_mul_left P (fun p q => esL (p, q) ⊆ pl) 1 (by
    intro p _ _
    by_cases hab : a ≠ 0 ∨ b ≠ 0
    · refine Finset.card_le_one.mpr ?_
      intro q₁ hq₁ q₂ hq₂
      obtain ⟨e₁, f₁⟩ := hlin p q₁ (Finset.mem_filter.mp hq₁).2
      obtain ⟨e₂, f₂⟩ := hlin p q₂ (Finset.mem_filter.mp hq₂).2
      have hdet : a * (-a) - b * b ≠ 0 := by
        rcases hab with ha | hb
        · have : 0 < a ^ 2 := sq_pos_of_ne_zero ha
          nlinarith [sq_nonneg b]
        · have : 0 < b ^ 2 := sq_pos_of_ne_zero hb
          nlinarith [sq_nonneg a]
      have heq := linear2_unique hdet
        (c₁ := -(a * p 0 + b * p 1 + 2 * d))
        (c₂ := -(a * p 1 - b * p 0 + 2 * c))
        (x₁ := q₁ 0) (y₁ := q₁ 1) (x₂ := q₂ 0) (y₂ := q₂ 1)
        (by linarith) (by linarith) (by linarith) (by linarith)
      exact eq_of_coords heq.1 heq.2
    · have ha : a = 0 := by tauto
      have hb : b = 0 := by tauto
      have hc : c ≠ 0 := by tauto
      have hempty : (P.filter fun q : ℝ² => esL (p, q) ⊆ pl) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro q _ hsub
        obtain ⟨_, hf⟩ := hlin p q hsub
        rw [ha, hb] at hf
        exact hc (by linarith)
      rw [hempty, Finset.card_empty]
      omega)
  simpa using hle

/- Every affine line in `R^3` is either an Elekes-Sharir line (non-horizontal) or a horizontal
line `{ x | x 2 = z0 /\ alpha * x 0 + beta * x 1 = gamma }`. -/
lemma line3_classification {L : Set (Fin 3 → ℝ)}
    (hL : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) :
    (∃ a b : ℝ²,
      L = Set.range fun t : ℝ =>
        ![(a 0 + b 0) / 2 - t * (b 1 - a 1) / 2,
          (a 1 + b 1) / 2 + t * (b 0 - a 0) / 2, t]) ∨
    (∃ z₀ α β γ : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧
      L = { x : Fin 3 → ℝ | x 2 = z₀ ∧ α * x 0 + β * x 1 = γ }) := by
  obtain ⟨p, d, hd, rfl⟩ := hL
  by_cases hd2 : d 2 ≠ 0
  · left
    set A0 : ℝ := p 0 - p 2 / d 2 * d 0
    set B0 : ℝ := d 0 / d 2
    set A1 : ℝ := p 1 - p 2 / d 2 * d 1
    set B1 : ℝ := d 1 / d 2
    let a : ℝ² := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![A0 - B1, A1 + B0]
    let b : ℝ² := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![A0 + B1, A1 - B0]
    have ha0 : a 0 = A0 - B1 := rfl
    have ha1 : a 1 = A1 + B0 := rfl
    have hb0 : b 0 = A0 + B1 := rfl
    have hb1 : b 1 = A1 - B0 := rfl
    refine ⟨a, b, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨p 2 + s * d 2, eq_fin3 ?_ ?_ ?_⟩
      · simp only [Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          ha0, ha1, hb0, hb1]
        dsimp only [A0, B0, A1, B1]
        field_simp [hd2]
        ring
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, ha0, ha1, hb0, hb1]
        dsimp only [A0, B0, A1, B1]
        field_simp [hd2]
        ring
      · simp
    · rintro ⟨t, rfl⟩
      refine ⟨(t - p 2) / d 2, eq_fin3 ?_ ?_ ?_⟩
      · simp only [Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          ha0, ha1, hb0, hb1]
        dsimp only [A0, B0, A1, B1]
        field_simp [hd2]
        ring
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, ha0, ha1, hb0, hb1]
        dsimp only [A0, B0, A1, B1]
        field_simp [hd2]
        ring
      · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp [hd2]
        ring
  · right
    have hd2' : d 2 = 0 := by tauto
    have hd01 : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
      by_contra h
      apply hd
      exact eq_fin3 (by tauto) (by tauto) hd2'
    refine ⟨p 2, -d 1, d 0, -d 1 * p 0 + d 0 * p 1, ?_, ?_⟩
    · rcases hd01 with h0 | h1
      · right; exact h0
      · left; exact neg_ne_zero.mpr h1
    · ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨s, rfl⟩
        refine ⟨by simp [hd2'], ?_⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · rintro ⟨hx2, hxy⟩
        have hD_ne : d 0 ^ 2 + d 1 ^ 2 ≠ 0 := by
          rcases hd01 with h0 | h1
          · have : 0 < d 0 ^ 2 := sq_pos_of_ne_zero h0
            nlinarith [sq_nonneg (d 1)]
          · have : 0 < d 1 ^ 2 := sq_pos_of_ne_zero h1
            nlinarith [sq_nonneg (d 0)]
        refine ⟨(d 0 * (x 0 - p 0) + d 1 * (x 1 - p 1)) / (d 0 ^ 2 + d 1 ^ 2), eq_fin3 ?_ ?_ ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp [hD_ne]
          linear_combination -d 1 * hxy
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp [hD_ne]
          linear_combination d 0 * hxy
        · simp [hd2', hx2]

/- Intersection of two Elekes-Sharir lines implies equality of squared distances. -/
lemma esLine_inter_esLine_dist_sq {p q a b : ℝ²}
    (h : ((Set.range fun t : ℝ =>
            ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
              (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ∩
          (Set.range fun t : ℝ =>
            ![(a 0 + b 0) / 2 - t * (b 1 - a 1) / 2,
              (a 1 + b 1) / 2 + t * (b 0 - a 0) / 2, t])).Nonempty) :
    (p 0 - a 0) ^ 2 + (p 1 - a 1) ^ 2 = (q 0 - b 0) ^ 2 + (q 1 - b 1) ^ 2 := by
  obtain ⟨x, hx1, hx2⟩ := h
  have h1 := (mem_esLine_iff p q x).mp hx1
  have h2 := (mem_esLine_iff a b x).mp hx2
  have heq := h1.symm.trans h2
  have h0 := congr_fun heq 0
  have h1' := congr_fun heq 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1'
  set t : ℝ := x 2
  have e0 : (p 0 - a 0) + t * (p 1 - a 1) = -(q 0 - b 0) + t * (q 1 - b 1) := by linarith
  have e1 : -t * (p 0 - a 0) + (p 1 - a 1) = -t * (q 0 - b 0) - (q 1 - b 1) := by linarith
  have hsq : (1 + t ^ 2) * ((p 0 - a 0) ^ 2 + (p 1 - a 1) ^ 2 -
      ((q 0 - b 0) ^ 2 + (q 1 - b 1) ^ 2)) = 0 := by
    have hcomb : ((p 0 - a 0) + t * (p 1 - a 1)) ^ 2 + (-t * (p 0 - a 0) + (p 1 - a 1)) ^ 2 =
        (-(q 0 - b 0) + t * (q 1 - b 1)) ^ 2 + (-t * (q 0 - b 0) - (q 1 - b 1)) ^ 2 := by
      rw [e0, e1]
    linear_combination hcomb
  have ht_pos : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hsq).resolve_left ht_pos)

/- Intersection of `L_{p,q}` with a horizontal line yields a linear equation in `(p, q)`. -/
lemma esLine_inter_horiz_eq {p q : ℝ²} {z₀ α β γ : ℝ}
    (h : ((Set.range fun t : ℝ =>
            ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
              (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ∩
          { x : Fin 3 → ℝ | x 2 = z₀ ∧ α * x 0 + β * x 1 = γ }).Nonempty) :
    (α - β * z₀) * p 0 + (β + α * z₀) * p 1 +
      (α + β * z₀) * q 0 + (β - α * z₀) * q 1 = 2 * γ := by
  obtain ⟨x, hx1, hz, hxy⟩ := h
  have h1 := (mem_esLine_iff p q x).mp hx1
  rw [hz] at h1
  have hx0 := congr_fun h1 0
  have hx1' := congr_fun h1 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx0 hx1'
  rw [hx0, hx1'] at hxy
  linarith

/- Two skew Elekes-Sharir lines have distinct parameter pairs. -/
lemma skew_esLine_ne {a₁ b₁ a₂ b₂ : ℝ²}
    (hskew : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ ((Set.range fun t : ℝ =>
            ![(a₁ 0 + b₁ 0) / 2 - t * (b₁ 1 - a₁ 1) / 2,
              (a₁ 1 + b₁ 1) / 2 + t * (b₁ 0 - a₁ 0) / 2, t]) ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         (Set.range fun t : ℝ =>
            ![(a₂ 0 + b₂ 0) / 2 - t * (b₂ 1 - a₂ 1) / 2,
              (a₂ 1 + b₂ 1) / 2 + t * (b₂ 0 - a₂ 0) / 2, t]) ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 })) :
    a₁ ≠ a₂ ∨ b₁ ≠ b₂ := by
  by_contra h
  have ha : a₁ = a₂ := by tauto
  have hb : b₁ = b₂ := by tauto
  subst ha hb
  have hsub : (Set.range fun t : ℝ =>
      ![(a₁ 0 + b₁ 0) / 2 - t * (b₁ 1 - a₁ 1) / 2,
        (a₁ 1 + b₁ 1) / 2 + t * (b₁ 0 - a₁ 0) / 2, t]) ⊆
      { x : Fin 3 → ℝ | 1 * x 0 + 0 * x 1 + ((b₁ 1 - a₁ 1) / 2) * x 2 + (-(a₁ 0 + b₁ 0) / 2) = 0 } := by
    rintro x ⟨t, rfl⟩
    simp only [Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  exact hskew 1 0 ((b₁ 1 - a₁ 1) / 2) (-(a₁ 0 + b₁ 0) / 2) (Or.inl one_ne_zero) ⟨hsub, hsub⟩

/- Two skew horizontal lines lie at distinct heights and have non-parallel directions. -/
lemma skew_horiz_cond {z₁ α₁ β₁ γ₁ z₂ α₂ β₂ γ₂ : ℝ}
    (h1 : α₁ ≠ 0 ∨ β₁ ≠ 0) (h2 : α₂ ≠ 0 ∨ β₂ ≠ 0)
    (hskew : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ ({ x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 })) :
    z₁ ≠ z₂ ∧ α₁ * β₂ - α₂ * β₁ ≠ 0 := by
  have hz : z₁ ≠ z₂ := by
    intro hzeq
    subst hzeq
    refine hskew 0 0 1 (-z₁) (Or.inr (Or.inr one_ne_zero)) ⟨?_, ?_⟩
    · intro x hx
      simp only [Set.mem_ofPred_eq]
      linarith [hx.1]
    · intro x hx
      simp only [Set.mem_ofPred_eq]
      linarith [hx.1]
  refine ⟨hz, ?_⟩
  intro hdet
  by_cases ha₁ : α₁ ≠ 0
  · have ha₂ : α₂ ≠ 0 := by
      intro h0
      rw [h0, zero_mul, sub_zero] at hdet
      have hb₂ : β₂ = 0 := (mul_eq_zero.mp hdet).resolve_left ha₁
      rcases h2 with h | h <;> contradiction
    set A : ℝ := (z₂ - z₁) * (α₁ * α₂)
    set B : ℝ := (z₂ - z₁) * (α₁ * β₂)
    set C : ℝ := -(α₁ * γ₂ - α₂ * γ₁)
    set D : ℝ := α₁ * γ₂ * z₁ - α₂ * γ₁ * z₂
    have hA : A ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hz.symm) (mul_ne_zero ha₁ ha₂)
    refine hskew A B C D (Or.inl hA) ⟨?_, ?_⟩
    · intro x hx
      simp only [Set.mem_ofPred_eq, A, B, C, D]
      linear_combination (z₂ - z₁) * α₂ * hx.2 + (z₂ - z₁) * x 1 * hdet -
        (α₁ * γ₂ - α₂ * γ₁) * hx.1
    · intro x hx
      simp only [Set.mem_ofPred_eq, A, B, C, D]
      linear_combination (z₂ - z₁) * α₁ * hx.2 - (α₁ * γ₂ - α₂ * γ₁) * hx.1
  · have ha₁' : α₁ = 0 := by tauto
    have hb₁ : β₁ ≠ 0 := by tauto
    rw [ha₁', zero_mul, zero_sub, neg_eq_zero] at hdet
    have ha₂ : α₂ = 0 := (mul_eq_zero.mp hdet).resolve_right hb₁
    have hb₂ : β₂ ≠ 0 := by tauto
    set B : ℝ := (z₂ - z₁) * (β₁ * β₂)
    set C : ℝ := -(β₁ * γ₂ - β₂ * γ₁)
    set D : ℝ := β₁ * γ₂ * z₁ - β₂ * γ₁ * z₂
    have hB : B ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hz.symm) (mul_ne_zero hb₁ hb₂)
    refine hskew 0 B C D (Or.inr (Or.inl hB)) ⟨?_, ?_⟩
    · intro x hx
      have hx2 := hx.2
      rw [ha₁', zero_mul, zero_add] at hx2
      simp only [Set.mem_ofPred_eq, B, C, D]
      linear_combination (z₂ - z₁) * β₂ * hx2 - (β₁ * γ₂ - β₂ * γ₁) * hx.1
    · intro x hx
      have hx2 := hx.2
      rw [ha₂, zero_mul, zero_add] at hx2
      simp only [Set.mem_ofPred_eq, B, C, D]
      linear_combination (z₂ - z₁) * β₁ * hx2 - (β₁ * γ₂ - β₂ * γ₁) * hx.1

/- Regulus bound Case 1: at least two of the three generating lines are non-horizontal. -/
lemma card_esLines_inter_two_nonhoriz (P : Finset ℝ²) {a₁ b₁ a₂ b₂ : ℝ²}
    (hskew : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ ((Set.range fun t : ℝ =>
            ![(a₁ 0 + b₁ 0) / 2 - t * (b₁ 1 - a₁ 1) / 2,
              (a₁ 1 + b₁ 1) / 2 + t * (b₁ 0 - a₁ 0) / 2, t]) ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         (Set.range fun t : ℝ =>
            ![(a₂ 0 + b₂ 0) / 2 - t * (b₂ 1 - a₂ 1) / 2,
              (a₂ 1 + b₂ 1) / 2 + t * (b₂ 0 - a₂ 0) / 2, t]) ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }))
    [DecidablePred fun pq : ℝ² × ℝ² =>
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       (Set.range fun t : ℝ =>
          ![(a₁ 0 + b₁ 0) / 2 - t * (b₁ 1 - a₁ 1) / 2,
            (a₁ 1 + b₁ 1) / 2 + t * (b₁ 0 - a₁ 0) / 2, t])).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       (Set.range fun t : ℝ =>
          ![(a₂ 0 + b₂ 0) / 2 - t * (b₂ 1 - a₂ 1) / 2,
            (a₂ 1 + b₂ 1) / 2 + t * (b₂ 0 - a₂ 0) / 2, t])).Nonempty] :
    ((P ×ˢ P).filter fun pq : ℝ² × ℝ² =>
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       (Set.range fun t : ℝ =>
          ![(a₁ 0 + b₁ 0) / 2 - t * (b₁ 1 - a₁ 1) / 2,
            (a₁ 1 + b₁ 1) / 2 + t * (b₁ 0 - a₁ 0) / 2, t])).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       (Set.range fun t : ℝ =>
          ![(a₂ 0 + b₂ 0) / 2 - t * (b₂ 1 - a₂ 1) / 2,
            (a₂ 1 + b₂ 1) / 2 + t * (b₂ 0 - a₂ 0) / 2, t])).Nonempty).card ≤ 2 * P.card := by
  let R : ℝ² → ℝ² → Prop := fun p q =>
    ((Set.range fun t : ℝ =>
        ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
          (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ∩
     (Set.range fun t : ℝ =>
        ![(a₁ 0 + b₁ 0) / 2 - t * (b₁ 1 - a₁ 1) / 2,
          (a₁ 1 + b₁ 1) / 2 + t * (b₁ 0 - a₁ 0) / 2, t])).Nonempty ∧
    ((Set.range fun t : ℝ =>
        ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
          (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ∩
     (Set.range fun t : ℝ =>
        ![(a₂ 0 + b₂ 0) / 2 - t * (b₂ 1 - a₂ 1) / 2,
          (a₂ 1 + b₂ 1) / 2 + t * (b₂ 0 - a₂ 0) / 2, t])).Nonempty
  rcases skew_esLine_ne hskew with ha | hb
  · refine card_filter_prod_le_mul_right P R 2 fun q _ _ => ?_
    classical
    refine le_trans (Finset.card_le_card ?_)
      (card_filter_two_circles_le_two P a₁ a₂ ha
        ((q 0 - b₁ 0) ^ 2 + (q 1 - b₁ 1) ^ 2)
        ((q 0 - b₂ 0) ^ 2 + (q 1 - b₂ 1) ^ 2))
    intro p hp
    obtain ⟨hpP, h1, h2⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpP, esLine_inter_esLine_dist_sq h1, esLine_inter_esLine_dist_sq h2⟩
  · refine card_filter_prod_le_mul_left P R 2 fun p _ _ => ?_
    classical
    refine le_trans (Finset.card_le_card ?_)
      (card_filter_two_circles_le_two P b₁ b₂ hb
        ((p 0 - a₁ 0) ^ 2 + (p 1 - a₁ 1) ^ 2)
        ((p 0 - a₂ 0) ^ 2 + (p 1 - a₂ 1) ^ 2))
    intro q hq
    obtain ⟨hqP, h1, h2⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr
      ⟨hqP, (esLine_inter_esLine_dist_sq h1).symm, (esLine_inter_esLine_dist_sq h2).symm⟩

/- Helper for two horizontal lines when at least one of the 2x2 determinants is nonzero. -/
lemma card_esLines_inter_two_horiz_of_det_ne (P : Finset ℝ²)
    {z₁ α₁ β₁ γ₁ z₂ α₂ β₂ γ₂ : ℝ}
    (hdet : (α₁ + β₁ * z₁) * (β₂ - α₂ * z₂) - (β₁ - α₁ * z₁) * (α₂ + β₂ * z₂) ≠ 0 ∨
            (α₁ - β₁ * z₁) * (β₂ + α₂ * z₂) - (β₁ + α₁ * z₁) * (α₂ - β₂ * z₂) ≠ 0)
    [DecidablePred fun pq : ℝ² × ℝ² =>
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ }).Nonempty] :
    ((P ×ˢ P).filter fun pq : ℝ² × ℝ² =>
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ }).Nonempty).card ≤ 2 * P.card := by
  let R : ℝ² → ℝ² → Prop := fun p q =>
    ((Set.range fun t : ℝ =>
        ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
          (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ∩
     { x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ }).Nonempty ∧
    ((Set.range fun t : ℝ =>
        ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
          (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ∩
     { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ }).Nonempty
  change ((P ×ˢ P).filter fun pq => R pq.1 pq.2).card ≤ 2 * P.card
  rcases hdet with hdet_v | hdet_u
  · have hdet_v' :
        (α₁ + β₁ * z₁) * (β₂ - α₂ * z₂) - (α₂ + β₂ * z₂) * (β₁ - α₁ * z₁) ≠ 0 := by
      rwa [mul_comm (α₂ + β₂ * z₂)]
    have hle := card_filter_prod_le_mul_left P R 1
      (fun p _ _ => Finset.card_le_one.mpr fun q₁ hq₁ q₂ hq₂ => by
        obtain ⟨h11, h12⟩ := (Finset.mem_filter.mp hq₁).2
        obtain ⟨h21, h22⟩ := (Finset.mem_filter.mp hq₂).2
        have e11 := esLine_inter_horiz_eq h11
        have e12 := esLine_inter_horiz_eq h12
        have e21 := esLine_inter_horiz_eq h21
        have e22 := esLine_inter_horiz_eq h22
        have heq := linear2_unique hdet_v'
          (c₁ := 2 * γ₁ - ((α₁ - β₁ * z₁) * p 0 + (β₁ + α₁ * z₁) * p 1))
          (c₂ := 2 * γ₂ - ((α₂ - β₂ * z₂) * p 0 + (β₂ + α₂ * z₂) * p 1))
          (x₁ := q₁ 0) (y₁ := q₁ 1) (x₂ := q₂ 0) (y₂ := q₂ 1)
          (by linarith) (by linarith) (by linarith) (by linarith)
        exact eq_of_coords heq.1 heq.2)
    omega
  · have hdet_u' :
        (α₁ - β₁ * z₁) * (β₂ + α₂ * z₂) - (α₂ - β₂ * z₂) * (β₁ + α₁ * z₁) ≠ 0 := by
      rwa [mul_comm (α₂ - β₂ * z₂)]
    have hle := card_filter_prod_le_mul_right P R 1
      (fun q _ _ => Finset.card_le_one.mpr fun p₁ hp₁ p₂ hp₂ => by
        obtain ⟨h11, h12⟩ := (Finset.mem_filter.mp hp₁).2
        obtain ⟨h21, h22⟩ := (Finset.mem_filter.mp hp₂).2
        have e11 := esLine_inter_horiz_eq h11
        have e12 := esLine_inter_horiz_eq h12
        have e21 := esLine_inter_horiz_eq h21
        have e22 := esLine_inter_horiz_eq h22
        have heq := linear2_unique hdet_u'
          (c₁ := 2 * γ₁ - ((α₁ + β₁ * z₁) * q 0 + (β₁ - α₁ * z₁) * q 1))
          (c₂ := 2 * γ₂ - ((α₂ + β₂ * z₂) * q 0 + (β₂ - α₂ * z₂) * q 1))
          (x₁ := p₁ 0) (y₁ := p₁ 1) (x₂ := p₂ 0) (y₂ := p₂ 1)
          (by linarith) (by linarith) (by linarith) (by linarith)
        exact eq_of_coords heq.1 heq.2)
    omega

/- Regulus bound Case 2: two skew horizontal lines and one non-horizontal line. -/
lemma card_esLines_inter_two_horiz_one_nonhoriz (P : Finset ℝ²) {a₃ b₃ : ℝ²}
    {z₁ α₁ β₁ γ₁ z₂ α₂ β₂ γ₂ : ℝ}
    (h1 : α₁ ≠ 0 ∨ β₁ ≠ 0) (h2 : α₂ ≠ 0 ∨ β₂ ≠ 0)
    (hskew12 : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ ({ x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }))
    [DecidablePred fun pq : ℝ² × ℝ² =>
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       (Set.range fun t : ℝ =>
          ![(a₃ 0 + b₃ 0) / 2 - t * (b₃ 1 - a₃ 1) / 2,
            (a₃ 1 + b₃ 1) / 2 + t * (b₃ 0 - a₃ 0) / 2, t])).Nonempty] :
    ((P ×ˢ P).filter fun pq : ℝ² × ℝ² =>
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       (Set.range fun t : ℝ =>
          ![(a₃ 0 + b₃ 0) / 2 - t * (b₃ 1 - a₃ 1) / 2,
            (a₃ 1 + b₃ 1) / 2 + t * (b₃ 0 - a₃ 0) / 2, t])).Nonempty).card ≤ 2 * P.card := by
  let R : ℝ² → ℝ² → Prop := fun p q =>
    ((Set.range fun t : ℝ =>
        ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
          (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ∩
     { x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ }).Nonempty ∧
    ((Set.range fun t : ℝ =>
        ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
          (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ∩
     { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ }).Nonempty ∧
    ((Set.range fun t : ℝ =>
        ![(p 0 + q 0) / 2 - t * (q 1 - p 1) / 2,
          (p 1 + q 1) / 2 + t * (q 0 - p 0) / 2, t]) ∩
     (Set.range fun t : ℝ =>
        ![(a₃ 0 + b₃ 0) / 2 - t * (b₃ 1 - a₃ 1) / 2,
          (a₃ 1 + b₃ 1) / 2 + t * (b₃ 0 - a₃ 0) / 2, t])).Nonempty
  by_cases hdet :
      (α₁ + β₁ * z₁) * (β₂ - α₂ * z₂) - (β₁ - α₁ * z₁) * (α₂ + β₂ * z₂) ≠ 0 ∨
      (α₁ - β₁ * z₁) * (β₂ + α₂ * z₂) - (β₁ + α₁ * z₁) * (α₂ - β₂ * z₂) ≠ 0
  · classical
    refine le_trans (Finset.card_le_card ?_)
      (card_esLines_inter_two_horiz_of_det_ne P (γ₁ := γ₁) (γ₂ := γ₂) hdet)
    intro pq hpq
    obtain ⟨hmem, h1', h2', _⟩ := Finset.mem_filter.mp hpq
    exact Finset.mem_filter.mpr ⟨hmem, h1', h2'⟩
  · have hdet_v : (α₁ + β₁ * z₁) * (β₂ - α₂ * z₂) - (β₁ - α₁ * z₁) * (α₂ + β₂ * z₂) = 0 := by
      tauto
    have hdet_u : (α₁ - β₁ * z₁) * (β₂ + α₂ * z₂) - (β₁ + α₁ * z₁) * (α₂ - β₂ * z₂) = 0 := by
      tauto
    obtain ⟨hz12, hab12⟩ := skew_horiz_cond h1 h2 hskew12
    have hY : (α₁ * α₂ + β₁ * β₂) * (z₁ - z₂) = 0 := by
      have : 2 * ((α₁ * α₂ + β₁ * β₂) * (z₁ - z₂)) = 0 := by
        linear_combination hdet_v - hdet_u
      linarith
    have horth : α₁ * α₂ + β₁ * β₂ = 0 :=
      (mul_eq_zero.mp hY).resolve_right (sub_ne_zero.mpr hz12)
    set u10 : ℝ := α₁ - β₁ * z₁
    set u11 : ℝ := β₁ + α₁ * z₁
    set v10 : ℝ := α₁ + β₁ * z₁
    set v11 : ℝ := β₁ - α₁ * z₁
    set u20 : ℝ := α₂ - β₂ * z₂
    set u21 : ℝ := β₂ + α₂ * z₂
    set v20 : ℝ := α₂ + β₂ * z₂
    set v21 : ℝ := β₂ - α₂ * z₂
    set N1 : ℝ := (α₁ ^ 2 + β₁ ^ 2) * (1 + z₁ ^ 2)
    set K : ℝ := (α₁ * β₂ - α₂ * β₁) * (z₁ - z₂)
    have hN1_pos : 0 < N1 := by
      have hab1 : 0 < α₁ ^ 2 + β₁ ^ 2 := by
        rcases h1 with h1 | h1
        · have : 0 < α₁ ^ 2 := sq_pos_of_ne_zero h1
          nlinarith [sq_nonneg β₁]
        · have : 0 < β₁ ^ 2 := sq_pos_of_ne_zero h1
          nlinarith [sq_nonneg α₁]
      have hz1 : 0 < 1 + z₁ ^ 2 := by nlinarith [sq_nonneg z₁]
      exact mul_pos hab1 hz1
    have hK_ne : K ≠ 0 := mul_ne_zero hab12 (sub_ne_zero.mpr hz12)
    have hv1_ne : v10 ≠ 0 ∨ v11 ≠ 0 := by
      have hv_sq : v10 ^ 2 + v11 ^ 2 = N1 := by dsimp only [v10, v11, N1]; ring
      by_contra h
      have h0 : v10 = 0 := by tauto
      have h1' : v11 = 0 := by tauto
      rw [h0, h1'] at hv_sq
      linarith
    have hu_dot : u10 * u20 + u11 * u21 = K := by
      dsimp only [u10, u11, u20, u21, K]
      linear_combination (1 + z₁ * z₂) * horth
    have hv_dot : v10 * v20 + v11 * v21 = -K := by
      dsimp only [v10, v11, v20, v21, K]
      linear_combination (1 + z₁ * z₂) * horth
    have hu_sq : u10 ^ 2 + u11 ^ 2 = N1 := by dsimp only [u10, u11, N1]; ring
    have hv_sq : v10 ^ 2 + v11 ^ 2 = N1 := by dsimp only [v10, v11, N1]; ring
    have hu20 : N1 * u20 = K * u10 := by
      rw [← hu_sq]
      linear_combination u10 * hu_dot - u11 * hdet_u
    have hu21 : N1 * u21 = K * u11 := by
      rw [← hu_sq]
      linear_combination u11 * hu_dot + u10 * hdet_u
    have hv20 : N1 * v20 = -K * v10 := by
      rw [← hv_sq]
      linear_combination v10 * hv_dot - v11 * hdet_v
    have hv21 : N1 * v21 = -K * v11 := by
      rw [← hv_sq]
      linear_combination v11 * hv_dot + v10 * hdet_v
    refine card_filter_prod_le_mul_left P R 2 fun p _ _ => ?_
    classical
    set c_line : ℝ := (2 * K * γ₁ - 2 * N1 * γ₂) / (2 * K)
    refine le_trans (Finset.card_le_card ?_)
      (card_filter_line_circle_le_two P v10 v11 c_line (b₃ 0) (b₃ 1)
        ((p 0 - a₃ 0) ^ 2 + (p 1 - a₃ 1) ^ 2) hv1_ne)
    intro q hq
    obtain ⟨hqP, h1', h2', h3'⟩ := Finset.mem_filter.mp hq
    have e1 := esLine_inter_horiz_eq h1'
    have e2 := esLine_inter_horiz_eq h2'
    have hcirc := (esLine_inter_esLine_dist_sq h3').symm
    have h2K_ne : 2 * K ≠ 0 := mul_ne_zero two_ne_zero hK_ne
    have hlin : (2 * K) * (v10 * q 0 + v11 * q 1) = 2 * K * γ₁ - 2 * N1 * γ₂ := by
      have e1' : u10 * p 0 + u11 * p 1 + v10 * q 0 + v11 * q 1 = 2 * γ₁ := e1
      have e2' : u20 * p 0 + u21 * p 1 + v20 * q 0 + v21 * q 1 = 2 * γ₂ := e2
      linear_combination K * e1' - N1 * e2' + p 0 * hu20 + p 1 * hu21 + q 0 * hv20 + q 1 * hv21
    refine Finset.mem_filter.mpr ⟨hqP, ?_, hcirc⟩
    dsimp only [c_line]
    rw [eq_div_iff h2K_ne, mul_comm]
    exact hlin

/- Regulus bound Case 3: all three generating lines are horizontal. -/
lemma card_esLines_inter_three_horiz (P : Finset ℝ²)
    {z₁ α₁ β₁ γ₁ z₂ α₂ β₂ γ₂ z₃ α₃ β₃ γ₃ : ℝ}
    (h1 : α₁ ≠ 0 ∨ β₁ ≠ 0) (h2 : α₂ ≠ 0 ∨ β₂ ≠ 0) (h3 : α₃ ≠ 0 ∨ β₃ ≠ 0)
    (hskew12 : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ ({ x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }))
    (hskew13 : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ ({ x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         { x : Fin 3 → ℝ | x 2 = z₃ ∧ α₃ * x 0 + β₃ * x 1 = γ₃ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }))
    (hskew23 : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ ({ x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         { x : Fin 3 → ℝ | x 2 = z₃ ∧ α₃ * x 0 + β₃ * x 1 = γ₃ } ⊆
          { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }))
    [DecidablePred fun pq : ℝ² × ℝ² =>
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₃ ∧ α₃ * x 0 + β₃ * x 1 = γ₃ }).Nonempty] :
    ((P ×ˢ P).filter fun pq : ℝ² × ℝ² =>
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₁ ∧ α₁ * x 0 + β₁ * x 1 = γ₁ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₂ ∧ α₂ * x 0 + β₂ * x 1 = γ₂ }).Nonempty ∧
      ((Set.range fun t : ℝ =>
          ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
            (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∩
       { x : Fin 3 → ℝ | x 2 = z₃ ∧ α₃ * x 0 + β₃ * x 1 = γ₃ }).Nonempty).card ≤ 2 * P.card := by
  classical
  obtain ⟨_, hab12⟩ := skew_horiz_cond h1 h2 hskew12
  obtain ⟨_, hab13⟩ := skew_horiz_cond h1 h3 hskew13
  obtain ⟨hz23, _⟩ := skew_horiz_cond h2 h3 hskew23
  by_cases hz12 : 1 + z₁ * z₂ ≠ 0
  · have hdet :
        (α₁ + β₁ * z₁) * (β₂ - α₂ * z₂) - (β₁ - α₁ * z₁) * (α₂ + β₂ * z₂) ≠ 0 ∨
        (α₁ - β₁ * z₁) * (β₂ + α₂ * z₂) - (β₁ + α₁ * z₁) * (α₂ - β₂ * z₂) ≠ 0 := by
      by_contra h
      have hv : (α₁ + β₁ * z₁) * (β₂ - α₂ * z₂) - (β₁ - α₁ * z₁) * (α₂ + β₂ * z₂) = 0 := by
        tauto
      have hu : (α₁ - β₁ * z₁) * (β₂ + α₂ * z₂) - (β₁ + α₁ * z₁) * (α₂ - β₂ * z₂) = 0 := by
        tauto
      have hsum : 2 * ((α₁ * β₂ - α₂ * β₁) * (1 + z₁ * z₂)) = 0 := by
        linear_combination hv + hu
      exact mul_ne_zero hab12 hz12 (by linarith)
    refine le_trans (Finset.card_le_card ?_)
      (card_esLines_inter_two_horiz_of_det_ne P (γ₁ := γ₁) (γ₂ := γ₂) hdet)
    intro pq hpq
    obtain ⟨hmem, h1', h2', _⟩ := Finset.mem_filter.mp hpq
    exact Finset.mem_filter.mpr ⟨hmem, h1', h2'⟩
  · have hz12' : 1 + z₁ * z₂ = 0 := by tauto
    have hz13 : 1 + z₁ * z₃ ≠ 0 := by
      intro h0
      have hmul : z₁ * (z₂ - z₃) = 0 := by linear_combination hz12' - h0
      have hz1 : z₁ ≠ 0 := by
        intro h
        rw [h, zero_mul, add_zero] at hz12'
        exact one_ne_zero hz12'
      exact hz23 (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hz1))
    have hdet :
        (α₁ + β₁ * z₁) * (β₃ - α₃ * z₃) - (β₁ - α₁ * z₁) * (α₃ + β₃ * z₃) ≠ 0 ∨
        (α₁ - β₁ * z₁) * (β₃ + α₃ * z₃) - (β₁ + α₁ * z₁) * (α₃ - β₃ * z₃) ≠ 0 := by
      by_contra h
      have hv : (α₁ + β₁ * z₁) * (β₃ - α₃ * z₃) - (β₁ - α₁ * z₁) * (α₃ + β₃ * z₃) = 0 := by
        tauto
      have hu : (α₁ - β₁ * z₁) * (β₃ + α₃ * z₃) - (β₁ + α₁ * z₁) * (α₃ - β₃ * z₃) = 0 := by
        tauto
      have hsum : 2 * ((α₁ * β₃ - α₃ * β₁) * (1 + z₁ * z₃)) = 0 := by
        linear_combination hv + hu
      exact mul_ne_zero hab13 hz13 (by linarith)
    refine le_trans (Finset.card_le_card ?_)
      (card_esLines_inter_two_horiz_of_det_ne P (γ₁ := γ₁) (γ₂ := γ₃) hdet)
    intro pq hpq
    obtain ⟨hmem, h1', _, h3'⟩ := Finset.mem_filter.mp hpq
    exact Finset.mem_filter.mpr ⟨hmem, h1', h3'⟩

/- Every regulus in `R^3` (transversals to three pairwise skew lines) contains at most `2 * |P|`
Elekes-Sharir lines of `P`. -/
lemma regulusLineCount_esLines_le (P : Finset ℝ²) (L₁ L₂ L₃ : Set (Fin 3 → ℝ))
    (hlines : ∀ L ∈ ({L₁, L₂, L₃} : Set (Set (Fin 3 → ℝ))),
      ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (hskew : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      let pl := { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }
      ¬ (L₁ ⊆ pl ∧ L₂ ⊆ pl) ∧ ¬ (L₁ ⊆ pl ∧ L₃ ⊆ pl) ∧ ¬ (L₂ ⊆ pl ∧ L₃ ⊆ pl))
    [DecidableEq (Set (Fin 3 → ℝ))] :
    { L : Set (Fin 3 → ℝ) |
      L ∈ (P ×ˢ P).image (fun pq : ℝ² × ℝ² =>
          Set.range fun t : ℝ =>
            ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
              (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]) ∧
      (L ∩ L₁).Nonempty ∧ (L ∩ L₂).Nonempty ∧ (L ∩ L₃).Nonempty }.ncard ≤ 2 * P.card := by
  let esL : ℝ² × ℝ² → Set (Fin 3 → ℝ) := fun pq =>
    Set.range fun t : ℝ =>
      ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
        (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]
  change { L : Set (Fin 3 → ℝ) |
      L ∈ (P ×ˢ P).image esL ∧
      (L ∩ L₁).Nonempty ∧ (L ∩ L₂).Nonempty ∧ (L ∩ L₃).Nonempty }.ncard ≤ 2 * P.card
  let _ : DecidablePred (fun pq : ℝ² × ℝ² =>
      (esL pq ∩ L₁).Nonempty ∧ (esL pq ∩ L₂).Nonempty ∧ (esL pq ∩ L₃).Nonempty) :=
    Classical.decPred _
  have hset : { L : Set (Fin 3 → ℝ) |
      L ∈ (P ×ˢ P).image esL ∧
      (L ∩ L₁).Nonempty ∧ (L ∩ L₂).Nonempty ∧ (L ∩ L₃).Nonempty } =
      (((P ×ˢ P).filter fun pq =>
        (esL pq ∩ L₁).Nonempty ∧ (esL pq ∩ L₂).Nonempty ∧ (esL pq ∩ L₃).Nonempty).image esL :
        Finset (Set (Fin 3 → ℝ))) := by
    ext L
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨pq, hpq, rfl⟩, hreg⟩
      exact ⟨pq, ⟨hpq, hreg⟩, rfl⟩
    · rintro ⟨pq, ⟨hpq, hreg⟩, rfl⟩
      exact ⟨⟨pq, hpq, rfl⟩, hreg⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ esLine_injective]
  have hL₁ : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L₁ = { x | ∃ t : ℝ, x = p + t • d } :=
    hlines L₁ (by simp)
  have hL₂ : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L₂ = { x | ∃ t : ℝ, x = p + t • d } :=
    hlines L₂ (by simp)
  have hL₃ : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L₃ = { x | ∃ t : ℝ, x = p + t • d } :=
    hlines L₃ (by simp)
  have h12 : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ (L₁ ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         L₂ ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }) :=
    fun a b c d h => (hskew a b c d h).1
  have h13 : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ (L₁ ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         L₃ ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }) :=
    fun a b c d h => (hskew a b c d h).2.1
  have h23 : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ¬ (L₂ ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } ∧
         L₃ ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }) :=
    fun a b c d h => (hskew a b c d h).2.2
  classical
  rcases line3_classification hL₁ with ⟨a₁, b₁, rfl⟩ | ⟨z₁, α₁, β₁, γ₁, hα₁, rfl⟩
  · rcases line3_classification hL₂ with ⟨a₂, b₂, rfl⟩ | ⟨z₂, α₂, β₂, γ₂, hα₂, rfl⟩
    · refine le_trans (Finset.card_le_card ?_) (card_esLines_inter_two_nonhoriz P h12)
      intro pq hpq
      obtain ⟨hmem, h1', h2', _⟩ := Finset.mem_filter.mp hpq
      exact Finset.mem_filter.mpr ⟨hmem, h1', h2'⟩
    · rcases line3_classification hL₃ with ⟨a₃, b₃, rfl⟩ | ⟨z₃, α₃, β₃, γ₃, hα₃, rfl⟩
      · refine le_trans (Finset.card_le_card ?_) (card_esLines_inter_two_nonhoriz P h13)
        intro pq hpq
        obtain ⟨hmem, h1', _, h3'⟩ := Finset.mem_filter.mp hpq
        exact Finset.mem_filter.mpr ⟨hmem, h1', h3'⟩
      · refine le_trans (Finset.card_le_card ?_)
          (card_esLines_inter_two_horiz_one_nonhoriz P (a₃ := a₁) (b₃ := b₁) hα₂ hα₃ h23)
        intro pq hpq
        obtain ⟨hmem, h1', h2', h3'⟩ := Finset.mem_filter.mp hpq
        exact Finset.mem_filter.mpr ⟨hmem, h2', h3', h1'⟩
  · rcases line3_classification hL₂ with ⟨a₂, b₂, rfl⟩ | ⟨z₂, α₂, β₂, γ₂, hα₂, rfl⟩
    · rcases line3_classification hL₃ with ⟨a₃, b₃, rfl⟩ | ⟨z₃, α₃, β₃, γ₃, hα₃, rfl⟩
      · refine le_trans (Finset.card_le_card ?_) (card_esLines_inter_two_nonhoriz P h23)
        intro pq hpq
        obtain ⟨hmem, _, h2', h3'⟩ := Finset.mem_filter.mp hpq
        exact Finset.mem_filter.mpr ⟨hmem, h2', h3'⟩
      · refine le_trans (Finset.card_le_card ?_)
          (card_esLines_inter_two_horiz_one_nonhoriz P (a₃ := a₂) (b₃ := b₂) hα₁ hα₃ h13)
        intro pq hpq
        obtain ⟨hmem, h1', h2', h3'⟩ := Finset.mem_filter.mp hpq
        exact Finset.mem_filter.mpr ⟨hmem, h1', h3', h2'⟩
    · rcases line3_classification hL₃ with ⟨a₃, b₃, rfl⟩ | ⟨z₃, α₃, β₃, γ₃, hα₃, rfl⟩
      · exact card_esLines_inter_two_horiz_one_nonhoriz P (a₃ := a₃) (b₃ := b₃)
          hα₁ hα₂ h12
      · exact card_esLines_inter_three_horiz P hα₁ hα₂ hα₃ h12 h13 h23

/- === Section 5: Pair-to-Richness Double-Counting and Harmonic Log Bound === -/

/- Two distinct affine lines in `R^3` intersect in at most one point. -/
lemma line3_inter_unique {L₁ L₂ : Set (Fin 3 → ℝ)} {x y : Fin 3 → ℝ}
    (hL₁ : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L₁ = { z | ∃ t : ℝ, z = p + t • d })
    (hL₂ : ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L₂ = { z | ∃ t : ℝ, z = p + t • d })
    (hne : L₁ ≠ L₂) (hx1 : x ∈ L₁) (hx2 : x ∈ L₂) (hy1 : y ∈ L₁) (hy2 : y ∈ L₂) :
    x = y := by
  by_contra hxy
  obtain ⟨p₁, d₁, _, hS₁⟩ := hL₁
  obtain ⟨p₂, d₂, _, hS₂⟩ := hL₂
  rw [hS₁] at hx1 hy1
  rw [hS₂] at hx2 hy2
  obtain ⟨t₁, rfl⟩ := hx1
  obtain ⟨t₂, ht₂⟩ := hy1
  obtain ⟨s₁, hs₁⟩ := hx2
  obtain ⟨s₂, hs₂⟩ := hy2
  have ht_ne : t₂ - t₁ ≠ 0 := by
    intro h0
    have hteq : t₂ = t₁ := sub_eq_zero.mp h0
    exact hxy (by rw [ht₂, hteq])
  have hs_ne : s₂ - s₁ ≠ 0 := by
    intro h0
    have hseq : s₂ = s₁ := sub_eq_zero.mp h0
    exact hxy (by rw [hs₁, hs₂, hseq])
  have hvec : (t₂ - t₁) • d₁ = (s₂ - s₁) • d₂ := by
    have h1 : y - (p₁ + t₁ • d₁) = (t₂ - t₁) • d₁ := by
      rw [ht₂, sub_smul]
      abel
    have h2 : y - (p₁ + t₁ • d₁) = (s₂ - s₁) • d₂ := by
      rw [hs₁, hs₂, sub_smul]
      abel
    exact h1.symm.trans h2
  have hd1_eq : d₁ = ((s₂ - s₁) / (t₂ - t₁)) • d₂ := by
    rw [div_eq_inv_mul, mul_smul, ← hvec, inv_smul_smul₀ ht_ne]
  have hd2_eq : d₂ = ((t₂ - t₁) / (s₂ - s₁)) • d₁ := by
    rw [div_eq_inv_mul, mul_smul, hvec, inv_smul_smul₀ hs_ne]
  apply hne
  rw [hS₁, hS₂]
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨s₁ + (t - t₁) * ((s₂ - s₁) / (t₂ - t₁)), ?_⟩
    have hz : p₁ + t • d₁ = (p₁ + t₁ • d₁) + (t - t₁) • d₁ := by
      rw [sub_smul]
      abel
    rw [hz, hs₁, hd1_eq, smul_smul, add_smul]
    abel
  · rintro ⟨s, rfl⟩
    refine ⟨t₁ + (s - s₁) * ((t₂ - t₁) / (s₂ - s₁)), ?_⟩
    have hz : p₂ + s • d₂ = (p₂ + s₁ • d₂) + (s - s₁) • d₂ := by
      rw [sub_smul]
      abel
    rw [hz, ← hs₁, hd2_eq, smul_smul, add_smul]
    abel

/- The set of 2-rich points of any finite family of affine lines is finite. -/
lemma richPoints_two_finite (ℒ : Finset (Set (Fin 3 → ℝ)))
    (hlines : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) :
    { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.Finite := by
  classical
  let I : Finset (Set (Fin 3 → ℝ) × Set (Fin 3 → ℝ)) :=
    ℒ.offDiag.filter fun LL => (LL.1 ∩ LL.2).Nonempty
  let pt : Set (Fin 3 → ℝ) × Set (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun LL =>
    if h : (LL.1 ∩ LL.2).Nonempty then h.choose else 0
  refine (I.image pt).finite_toSet.subset ?_
  intro x hx
  have hrich : 2 ≤ { L : Set (Fin 3 → ℝ) | L ∈ ℒ ∧ x ∈ L }.ncard := hx
  have hcard : 1 < (ℒ.filter fun L => x ∈ L).card := by
    have hset : { L : Set (Fin 3 → ℝ) | L ∈ ℒ ∧ x ∈ L } =
        (ℒ.filter fun L => x ∈ L : Finset (Set (Fin 3 → ℝ))) := by
      ext L
      simp
    rw [hset, Set.ncard_coe_finset] at hrich
    omega
  obtain ⟨L₁, hL₁, L₂, hL₂, hne⟩ := Finset.one_lt_card.mp hcard
  have hL₁' := Finset.mem_filter.mp hL₁
  have hL₂' := Finset.mem_filter.mp hL₂
  have hinter : (L₁ ∩ L₂).Nonempty := ⟨x, hL₁'.2, hL₂'.2⟩
  have hmemI : (L₁, L₂) ∈ I :=
    Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hL₁'.1, hL₂'.1, hne⟩, hinter⟩
  have hpt : pt (L₁, L₂) = x := by
    dsimp only [pt]
    simp only [hinter, ↓reduceDIte]
    exact line3_inter_unique (hlines L₁ hL₁'.1) (hlines L₂ hL₂'.1) hne
      hinter.choose_spec.1 hinter.choose_spec.2 hL₁'.2 hL₂'.2
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(L₁, L₂), hmemI, hpt⟩)

/- Exact count of ordered intersecting pairs of distinct lines in `ℒ` via point richness. -/
lemma card_intersecting_pairs_eq_sum (ℒ : Finset (Set (Fin 3 → ℝ)))
    (hlines : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    [DecidablePred fun LL : Set (Fin 3 → ℝ) × Set (Fin 3 → ℝ) => (LL.1 ∩ LL.2).Nonempty] :
    (ℒ.offDiag.filter fun LL => (LL.1 ∩ LL.2).Nonempty).card =
      ∑ x ∈ (richPoints_two_finite ℒ hlines).toFinset,
        { L | L ∈ ℒ ∧ x ∈ L }.ncard * ({ L | L ∈ ℒ ∧ x ∈ L }.ncard - 1) := by
  classical
  set I := ℒ.offDiag.filter fun LL => (LL.1 ∩ LL.2).Nonempty
  set S₂ : Finset (Fin 3 → ℝ) := (richPoints_two_finite ℒ hlines).toFinset
  let f : Set (Fin 3 → ℝ) × Set (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun LL =>
    if h : (LL.1 ∩ LL.2).Nonempty then h.choose else 0
  have hmaps : ∀ LL ∈ I, f LL ∈ S₂ := by
    intro LL hLL
    obtain ⟨hoff, hinter⟩ := Finset.mem_filter.mp hLL
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hoff
    rw [Set.Finite.mem_toFinset]
    change 2 ≤ { L : Set (Fin 3 → ℝ) | L ∈ ℒ ∧ f LL ∈ L }.ncard
    have hfx1 : f LL ∈ LL.1 := by
      dsimp only [f]
      simp only [hinter, ↓reduceDIte]
      exact hinter.choose_spec.1
    have hfx2 : f LL ∈ LL.2 := by
      dsimp only [f]
      simp only [hinter, ↓reduceDIte]
      exact hinter.choose_spec.2
    have hset : { L : Set (Fin 3 → ℝ) | L ∈ ℒ ∧ f LL ∈ L } =
        (ℒ.filter fun L => f LL ∈ L : Finset (Set (Fin 3 → ℝ))) := by
      ext L; simp
    rw [hset, Set.ncard_coe_finset]
    have hpair : ({LL.1, LL.2} : Finset (Set (Fin 3 → ℝ))) ⊆ ℒ.filter fun L => f LL ∈ L := by
      intro L hL
      simp only [Finset.mem_insert, Finset.mem_singleton] at hL
      rcases hL with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨h1, hfx1⟩
      · exact Finset.mem_filter.mpr ⟨h2, hfx2⟩
    have h2card : 2 = ({LL.1, LL.2} : Finset (Set (Fin 3 → ℝ))).card := (Finset.card_pair hne).symm
    rw [h2card]
    exact Finset.card_le_card hpair
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hfib : (I.filter fun LL => f LL = x) = (ℒ.filter fun L => x ∈ L).offDiag := by
    ext LL
    simp only [I, Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨⟨h1, h2, hne⟩, hinter⟩, hfx⟩
      have hspec := hinter.choose_spec
      have hchoose : hinter.choose = x := by
        dsimp only [f] at hfx
        simp only [hinter, ↓reduceDIte] at hfx
        exact hfx
      rw [hchoose] at hspec
      exact ⟨⟨h1, hspec.1⟩, ⟨h2, hspec.2⟩, hne⟩
    · rintro ⟨⟨h1, hx1⟩, ⟨h2, hx2⟩, hne⟩
      have hinter : (LL.1 ∩ LL.2).Nonempty := ⟨x, hx1, hx2⟩
      refine ⟨⟨⟨h1, h2, hne⟩, hinter⟩, ?_⟩
      dsimp only [f]
      simp only [hinter, ↓reduceDIte]
      exact line3_inter_unique (hlines LL.1 h1) (hlines LL.2 h2) hne
        hinter.choose_spec.1 hinter.choose_spec.2 hx1 hx2
  rw [hfib, Finset.offDiag_card]
  have hrich_eq : (ℒ.filter fun L => x ∈ L).card = { L : Set (Fin 3 → ℝ) | L ∈ ℒ ∧ x ∈ L }.ncard := by
    have hset : { L : Set (Fin 3 → ℝ) | L ∈ ℒ ∧ x ∈ L } =
        (ℒ.filter fun L => x ∈ L : Finset (Set (Fin 3 → ℝ))) := by
      ext L; simp
    rw [hset, Set.ncard_coe_finset]
  rw [hrich_eq]
  cases { L : Set (Fin 3 → ℝ) | L ∈ ℒ ∧ x ∈ L }.ncard with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega

/- Triangular-number identity `sum_{k=2}^r 2 * (k - 1) = r * (r - 1)`. -/
lemma sum_two_mul_pred_Ico (r : ℕ) :
    ∑ k ∈ Finset.Ico 2 (r + 1), 2 * (k - 1) = r * (r - 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      have hle : 2 ≤ m + 2 := by omega
      rw [Finset.sum_Ico_succ_top hle, ih]
      have h1 : m + 2 - 1 = m + 1 := by omega
      have h2 : m + 1 - 1 = m := by omega
      rw [h1, h2]
      ring

/- Abel summation rewriting `sum_{x in S2} m(x) * (m(x) - 1)` in terms of `k`-rich points. -/
lemma sum_richness_mul_pred_eq_Ico (ℒ : Finset (Set (Fin 3 → ℝ)))
    (hlines : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d })
    (N : ℕ) (hmax : ∀ x : Fin 3 → ℝ, { L | L ∈ ℒ ∧ x ∈ L }.ncard ≤ N) :
    ∑ x ∈ (richPoints_two_finite ℒ hlines).toFinset,
        { L | L ∈ ℒ ∧ x ∈ L }.ncard * ({ L | L ∈ ℒ ∧ x ∈ L }.ncard - 1) =
      ∑ k ∈ Finset.Ico 2 (N + 1),
        2 * (k - 1) * { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard := by
  classical
  set S₂ : Finset (Fin 3 → ℝ) := (richPoints_two_finite ℒ hlines).toFinset
  have h1 : ∀ x ∈ S₂,
      { L | L ∈ ℒ ∧ x ∈ L }.ncard * ({ L | L ∈ ℒ ∧ x ∈ L }.ncard - 1) =
        ∑ k ∈ Finset.Ico 2 (N + 1),
          if k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard then 2 * (k - 1) else 0 := by
    intro x _
    rw [← sum_two_mul_pred_Ico ({ L | L ∈ ℒ ∧ x ∈ L }.ncard)]
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_Ico, Finset.mem_filter]
    have hxN := hmax x
    omega
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  have hset : { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard } =
      (S₂.filter fun x => k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard : Finset (Fin 3 → ℝ)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
      S₂, Set.Finite.mem_toFinset]
    constructor
    · intro hkx
      exact ⟨le_trans hk2 hkx, hkx⟩
    · exact And.right
  rw [hset, Set.ncard_coe_finset]

/- Elementary inequality `1 / k <= log k - log (k - 1)` for `k >= 2`. -/
lemma inv_le_log_sub_log (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / (k : ℝ) ≤ Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    have : 0 < k - 1 := by omega
    exact_mod_cast this
  have hdiv_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) / (k : ℝ) := div_pos hk1_pos hk_pos
  have hlog := Real.log_le_sub_one_of_pos hdiv_pos
  rw [Real.log_div (ne_of_gt hk1_pos) (ne_of_gt hk_pos)] at hlog
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  rw [hcast] at hlog ⊢
  have hsub : ((k : ℝ) - 1) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
    field_simp [ne_of_gt hk_pos]
    ring
  rw [hsub] at hlog
  linarith

/- Telescoping harmonic bound `sum_{k=3}^N (1 / k) <= Real.log N` for all `N >= 2`. -/
lemma sum_inv_Ico_three_le_log (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico 3 (N + 1), (1 : ℝ) / (k : ℝ) ≤ Real.log (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [Nat.reduceAdd, Finset.Ico_self, Finset.sum_empty]
    exact Real.log_nonneg (by norm_num)
  | succ n hn ih =>
    have hle : 3 ≤ n + 1 := by omega
    rw [Finset.sum_Ico_succ_top hle]
    have hstep := inv_le_log_sub_log (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hstep
    linarith

/- Lower bound `1 / 2 <= Real.log N` for every integer `N >= 2`. -/
lemma half_le_log_of_two_le (N : ℕ) (hN : 2 ≤ N) :
    (1 : ℝ) / 2 ≤ Real.log (N : ℝ) := by
  have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hmono : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  exact le_trans h2 hmono

/- === Section 6: Distance Quadruples Reduction and Main Theorem === -/

/- Exact identity equating `4 * sum (distanceMultiplicity P u)^2` with the number of ordered
equidistant quadruples `(p1, p2, q1, q2)` with `p1 != p2` and `q1 != q2`. -/
lemma four_mul_sum_distanceMultiplicity_sq (P : Finset ℝ²)
    [DecidablePred fun pq : (ℝ² × ℝ²) × (ℝ² × ℝ²) =>
      dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2] :
    4 * ∑ u ∈ distanceSet P, (distanceMultiplicity P u) ^ 2 =
      ((P.offDiag ×ˢ P.offDiag).filter fun pq =>
        dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2).card := by
  classical
  set Q : Finset ((ℝ² × ℝ²) × (ℝ² × ℝ²)) :=
    (P.offDiag ×ˢ P.offDiag).filter fun pq => dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2
  have hmaps : ∀ pq ∈ Q, dist pq.1.1 pq.1.2 ∈ distanceSet P := by
    intro pq hpq
    obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hpq
    exact Finset.mem_image.mpr ⟨pq.1, (Finset.mem_product.mp hmem).1, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  set F : Finset (ℝ² × ℝ²) := P.offDiag.filter fun pair => dist pair.1 pair.2 = u
  have hfib : (Q.filter fun pq => dist pq.1.1 pq.1.2 = u) = F ×ˢ F := by
    ext pq
    simp only [Q, F, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, heq⟩, hu⟩
      exact ⟨⟨h1, hu⟩, ⟨h2, heq.symm.trans hu⟩⟩
    · rintro ⟨⟨h1, hu1⟩, ⟨h2, hu2⟩⟩
      exact ⟨⟨⟨h1, h2⟩, hu1.trans hu2.symm⟩, hu1⟩
  rw [hfib, Finset.card_product]
  have heven : 2 ∣ F.card := even_iff_two_dvd.mp (even_card_offDiag_filter_dist_eq P u)
  have hmul : 2 * distanceMultiplicity P u = F.card := by
    unfold distanceMultiplicity
    exact Nat.mul_div_cancel' heven
  calc
    4 * (distanceMultiplicity P u) ^ 2 = (2 * distanceMultiplicity P u) ^ 2 := by ring
    _ = F.card ^ 2 := by rw [hmul]
    _ = F.card * F.card := sq F.card

/- Translation quadruples (`q2 - q1 = p2 - p1`) number at most `|P|^3`. -/
lemma card_trans_quadruples_le (P : Finset ℝ²)
    [DecidablePred fun pq : (ℝ² × ℝ²) × (ℝ² × ℝ²) =>
      dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2 ∧ pq.2.2 - pq.2.1 = pq.1.2 - pq.1.1] :
    ((P.offDiag ×ˢ P.offDiag).filter fun pq =>
      dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2 ∧ pq.2.2 - pq.2.1 = pq.1.2 - pq.1.1).card ≤
        P.card ^ 3 := by
  classical
  set Q_tr := (P.offDiag ×ˢ P.offDiag).filter fun pq =>
    dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2 ∧ pq.2.2 - pq.2.1 = pq.1.2 - pq.1.1
  let proj : ((ℝ² × ℝ²) × (ℝ² × ℝ²)) → (ℝ² × ℝ² × ℝ²) :=
    fun pq => (pq.1.1, pq.1.2, pq.2.1)
  have hinj : Set.InjOn proj (Q_tr : Set ((ℝ² × ℝ²) × (ℝ² × ℝ²))) := by
    intro a ha b hb hproj
    have ha_eq : a.2.2 - a.2.1 = a.1.2 - a.1.1 := (Finset.mem_filter.mp ha).2.2
    have hb_eq : b.2.2 - b.2.1 = b.1.2 - b.1.1 := (Finset.mem_filter.mp hb).2.2
    simp only [proj, Prod.mk.injEq] at hproj
    obtain ⟨h11, h12, h21⟩ := hproj
    have h22 : a.2.2 = b.2.2 := by
      have ha' : a.2.2 = a.2.1 + (a.1.2 - a.1.1) := eq_add_of_sub_eq' ha_eq
      have hb' : b.2.2 = b.2.1 + (b.1.2 - b.1.1) := eq_add_of_sub_eq' hb_eq
      rw [ha', hb', h11, h12, h21]
    exact Prod.ext (Prod.ext h11 h12) (Prod.ext h21 h22)
  have hsub : Q_tr.image proj ⊆ P ×ˢ (P ×ˢ P) := by
    intro t ht
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hpq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    exact Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp h1).1,
      Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp h1).2.1, (Finset.mem_offDiag.mp h2).1⟩⟩
  calc
    Q_tr.card = (Q_tr.image proj).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (P ×ˢ (P ×ˢ P)).card := Finset.card_le_card hsub
    _ = P.card ^ 3 := by
      rw [Finset.card_product, Finset.card_product]
      ring

/- Proper non-translation quadruples inject into ordered intersecting pairs of Elekes-Sharir
lines of `P`. -/
lemma card_nonTrans_quadruples_le_inter_pairs (P : Finset ℝ²)
    [DecidablePred fun pq : (ℝ² × ℝ²) × (ℝ² × ℝ²) =>
      dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2 ∧ pq.2.2 - pq.2.1 ≠ pq.1.2 - pq.1.1]
    [DecidableEq (Set (Fin 3 → ℝ))]
    [DecidablePred fun LL : Set (Fin 3 → ℝ) × Set (Fin 3 → ℝ) => (LL.1 ∩ LL.2).Nonempty] :
    ((P.offDiag ×ˢ P.offDiag).filter fun pq =>
      dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2 ∧ pq.2.2 - pq.2.1 ≠ pq.1.2 - pq.1.1).card ≤
      (((P ×ˢ P).image fun pq : ℝ² × ℝ² =>
          Set.range fun t : ℝ =>
            ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
              (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]).offDiag.filter
        fun LL => (LL.1 ∩ LL.2).Nonempty).card := by
  let esL : ℝ² × ℝ² → Set (Fin 3 → ℝ) := fun pq =>
    Set.range fun t : ℝ =>
      ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
        (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]
  set Q_rot := (P.offDiag ×ˢ P.offDiag).filter fun pq =>
    dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2 ∧ pq.2.2 - pq.2.1 ≠ pq.1.2 - pq.1.1
  let mapLine : ((ℝ² × ℝ²) × (ℝ² × ℝ²)) → (Set (Fin 3 → ℝ) × Set (Fin 3 → ℝ)) :=
    fun pq => (esL (pq.1.1, pq.2.1), esL (pq.1.2, pq.2.2))
  have hinj : Function.Injective mapLine := by
    rintro ⟨⟨p₁, p₂⟩, ⟨q₁, q₂⟩⟩ ⟨⟨p₁', p₂'⟩, ⟨q₁', q₂'⟩⟩ h
    dsimp only [mapLine] at h
    obtain ⟨hfst, hsnd⟩ := Prod.mk.inj h
    have h1 := esLine_injective hfst
    have h2 := esLine_injective hsnd
    simp only [Prod.mk.injEq] at h1 h2
    exact Prod.ext (Prod.ext h1.1 h2.1) (Prod.ext h1.2 h2.2)
  have hsub : Q_rot.image mapLine ⊆
      ((P ×ˢ P).image esL).offDiag.filter fun LL => (LL.1 ∩ LL.2).Nonempty := by
    intro LL hLL
    obtain ⟨⟨⟨p₁, p₂⟩, ⟨q₁, q₂⟩⟩, hpq, rfl⟩ := Finset.mem_image.mp hLL
    obtain ⟨hmem, hdist, hnt⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hmem
    obtain ⟨hp₁, hp₂, hpne⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨hq₁, hq₂, _⟩ := Finset.mem_offDiag.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨?_, ?_, ?_⟩,
      esLine_inter_of_nonTrans hdist hnt⟩
    · exact Finset.mem_image.mpr ⟨(p₁, q₁), Finset.mem_product.mpr ⟨hp₁, hq₁⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(p₂, q₂), Finset.mem_product.mpr ⟨hp₂, hq₂⟩, rfl⟩
    · intro heq
      exact hpne (congrArg Prod.fst (esLine_injective heq))
  calc
    Q_rot.card = (Q_rot.image mapLine).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (((P ×ˢ P).image esL).offDiag.filter fun LL => (LL.1 ∩ LL.2).Nonempty).card :=
      Finset.card_le_card hsub

/- Main reduction: Guth-Katz 3D incidence bounds `H1` and `H2` imply the distinct-distances
energy bound `Erdos95.erdos_95.variants.guth_katz`. -/
theorem main : H1 → H2 → type_of% @Erdos95.erdos_95.variants.guth_katz := by
  rintro ⟨C₁, hC₁, hH1⟩ ⟨C₂, hC₂, hH2⟩
  refine ⟨(1 + 2 * C₁ + C₂) / 2, by linarith, ?_⟩
  intro P hP2
  classical
  set N : ℕ := P.card
  let esL : ℝ² × ℝ² → Set (Fin 3 → ℝ) := fun pq =>
    Set.range fun t : ℝ =>
      ![(pq.1 0 + pq.2 0) / 2 - t * (pq.2 1 - pq.1 1) / 2,
        (pq.1 1 + pq.2 1) / 2 + t * (pq.2 0 - pq.1 0) / 2, t]
  set ℒ : Finset (Set (Fin 3 → ℝ)) := (P ×ˢ P).image esL
  have hN1 : 1 ≤ N := by omega
  have hLcard : ℒ.card ≤ N ^ 2 := by
    dsimp only [ℒ, N]
    rw [Finset.card_image_of_injective _ esLine_injective, Finset.card_product, sq]
  have hlines : ∀ L ∈ ℒ, ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d } := by
    intro L hL
    obtain ⟨⟨p, q⟩, _, rfl⟩ := Finset.mem_image.mp hL
    exact esLine_isLine p q
  have hplane : ∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      { L | L ∈ ℒ ∧ L ⊆ { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 } }.ncard ≤ N := by
    intro a b c d habc
    exact planeLineCount_esLines_le P a b c d habc
  have hreg : ∀ L₁ L₂ L₃ : Set (Fin 3 → ℝ),
      (∀ L ∈ ({L₁, L₂, L₃} : Set (Set (Fin 3 → ℝ))),
        ∃ p d : Fin 3 → ℝ, d ≠ 0 ∧ L = { x | ∃ t : ℝ, x = p + t • d }) →
      (∀ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
        let pl := { x : Fin 3 → ℝ | a * x 0 + b * x 1 + c * x 2 + d = 0 }
        ¬ (L₁ ⊆ pl ∧ L₂ ⊆ pl) ∧ ¬ (L₁ ⊆ pl ∧ L₃ ⊆ pl) ∧ ¬ (L₂ ⊆ pl ∧ L₃ ⊆ pl)) →
      { L | L ∈ ℒ ∧ (L ∩ L₁).Nonempty ∧ (L ∩ L₂).Nonempty ∧ (L ∩ L₃).Nonempty }.ncard ≤
        2 * N := by
    intro L₁ L₂ L₃ hls hsk
    exact regulusLineCount_esLines_le P L₁ L₂ L₃ hls hsk
  have h2rich : ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) ≤
      C₁ * (N : ℝ) ^ 3 :=
    hH1 N ℒ hN1 hLcard hlines hplane hreg
  have hkrich : ∀ k ∈ Finset.Ico 3 (N + 1),
      ({ x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) ≤
        C₂ * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
    intro k hk
    obtain ⟨hk3, hkN⟩ := Finset.mem_Ico.mp hk
    exact hH2 N k ℒ hk3 (by omega) hLcard hlines hplane
  set Q_ord := (P.offDiag ×ˢ P.offDiag).filter fun pq =>
    dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2
  set Q_tr := (P.offDiag ×ˢ P.offDiag).filter fun pq =>
    dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2 ∧ pq.2.2 - pq.2.1 = pq.1.2 - pq.1.1
  set Q_rot := (P.offDiag ×ˢ P.offDiag).filter fun pq =>
    dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2 ∧ pq.2.2 - pq.2.1 ≠ pq.1.2 - pq.1.1
  have hQ_split : Q_ord.card ≤ Q_tr.card + Q_rot.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le Q_tr Q_rot)
    intro pq hpq
    obtain ⟨hmem, hdist⟩ := Finset.mem_filter.mp hpq
    rw [Finset.mem_union]
    by_cases htr : pq.2.2 - pq.2.1 = pq.1.2 - pq.1.1
    · exact Or.inl (Finset.mem_filter.mpr ⟨hmem, hdist, htr⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hmem, hdist, htr⟩)
  set I := ℒ.offDiag.filter fun LL => (LL.1 ∩ LL.2).Nonempty
  have hQ_nat : 4 * ∑ u ∈ distanceSet P, (distanceMultiplicity P u) ^ 2 ≤ N ^ 3 + I.card := by
    rw [four_mul_sum_distanceMultiplicity_sq P]
    exact le_trans hQ_split
      (Nat.add_le_add (card_trans_quadruples_le P) (card_nonTrans_quadruples_le_inter_pairs P))
  have hmax : ∀ x : Fin 3 → ℝ, { L | L ∈ ℒ ∧ x ∈ L }.ncard ≤ N :=
    fun x => pointRichness_esLines_le P x
  have hI_eq : I.card = ∑ k ∈ Finset.Ico 2 (N + 1),
      2 * (k - 1) * { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard := by
    rw [card_intersecting_pairs_eq_sum ℒ hlines, sum_richness_mul_pred_eq_Ico ℒ hlines N hmax]
  have hI_split : I.card =
      2 * { x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard +
        ∑ k ∈ Finset.Ico 3 (N + 1),
          2 * (k - 1) * { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard := by
    rw [hI_eq, Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < N + 1)]
  have hsum_k :
      (∑ k ∈ Finset.Ico 3 (N + 1),
        (2 * (k - 1) * { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ)) ≤
        2 * C₂ * (N : ℝ) ^ 3 * Real.log (N : ℝ) := by
    calc
      ∑ k ∈ Finset.Ico 3 (N + 1),
          (2 * (k - 1) * { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ)
          ≤ ∑ k ∈ Finset.Ico 3 (N + 1), (2 * C₂ * (N : ℝ) ^ 3) * ((1 : ℝ) / (k : ℝ)) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
            have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
            have hk_sub_le : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
              exact_mod_cast Nat.sub_le k 1
            have hbound := hkrich k hk
            have hnonneg : (0 : ℝ) ≤ (2 * ((k - 1 : ℕ) : ℝ)) := by positivity
            calc
              (2 * (k - 1) * { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ)
                  = 2 * ((k - 1 : ℕ) : ℝ) *
                      ({ x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) := by
                    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
              _ ≤ 2 * ((k - 1 : ℕ) : ℝ) * (C₂ * (N : ℝ) ^ 3 / (k : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_left hbound hnonneg
              _ ≤ 2 * (k : ℝ) * (C₂ * (N : ℝ) ^ 3 / (k : ℝ) ^ 2) := by
                    have hfac : 0 ≤ C₂ * (N : ℝ) ^ 3 / (k : ℝ) ^ 2 := by positivity
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hk_sub_le (by norm_num)) hfac
              _ = (2 * C₂ * (N : ℝ) ^ 3) * ((1 : ℝ) / (k : ℝ)) := by
                    field_simp [ne_of_gt hk_pos]
      _ = (2 * C₂ * (N : ℝ) ^ 3) * ∑ k ∈ Finset.Ico 3 (N + 1), (1 : ℝ) / (k : ℝ) := by
            rw [← Finset.mul_sum]
      _ ≤ (2 * C₂ * (N : ℝ) ^ 3) * Real.log (N : ℝ) := by
            exact mul_le_mul_of_nonneg_left (sum_inv_Ico_three_le_log N hP2) (by positivity)
  have hQ_real :
      4 * ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤
        (N : ℝ) ^ 3 + (I.card : ℝ) := by
    have hcast :
        ((4 * ∑ u ∈ distanceSet P, (distanceMultiplicity P u) ^ 2 : ℕ) : ℝ) ≤
          ((N ^ 3 + I.card : ℕ) : ℝ) := by
      exact_mod_cast hQ_nat
    push_cast at hcast
    exact hcast
  have hI_real :
      (I.card : ℝ) ≤ 2 * C₁ * (N : ℝ) ^ 3 + 2 * C₂ * (N : ℝ) ^ 3 * Real.log (N : ℝ) := by
    have hcast :
        (I.card : ℝ) =
          2 * ({ x : Fin 3 → ℝ | 2 ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) +
            ∑ k ∈ Finset.Ico 3 (N + 1),
              (2 * ((k - 1 : ℕ) : ℝ) *
                ({ x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ)) := by
      rw [hI_split]
      push_cast
      rfl
    have hsum_eq :
        ∑ k ∈ Finset.Ico 3 (N + 1),
          (2 * ((k - 1 : ℕ) : ℝ) *
            ({ x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ)) =
        ∑ k ∈ Finset.Ico 3 (N + 1),
          (2 * (k - 1) * { x : Fin 3 → ℝ | k ≤ { L | L ∈ ℒ ∧ x ∈ L }.ncard }.ncard : ℝ) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    rw [hcast, hsum_eq]
    linarith [h2rich, hsum_k]
  have hlog : (1 : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    linarith [half_le_log_of_two_le N hP2]
  have hN3_nonneg : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hbase : (1 + 2 * C₁) * (N : ℝ) ^ 3 ≤ 2 * (1 + 2 * C₁) * (N : ℝ) ^ 3 * Real.log (N : ℝ) := by
    have hcoef : 0 ≤ (1 + 2 * C₁) * (N : ℝ) ^ 3 := by
      exact mul_nonneg (by linarith) hN3_nonneg
    nlinarith
  linarith

end OMA.R_Erdos95_erdos_95_variants_guth_katz_R1
