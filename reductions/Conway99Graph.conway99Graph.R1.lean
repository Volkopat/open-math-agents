import FormalConjectures.Wikipedia.Conway99Graph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic

-- Reduction Conway99Graph.conway99Graph.R1 of Conway's 99-graph problem
-- Credit: @Cryptokraken974

namespace OMA.R_Conway99Graph_conway99Graph_R1

open SimpleGraph
open scoped BigOperators

lemma c50_local {V : Type*} (G : SimpleGraph V)
    (h : ∀ x y, G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard = 1) :
    G.LocallyLinear := by
  classical
  constructor
  · intro s hs t ht hst
    change G.IsNClique 3 s at hs
    change G.IsNClique 3 t at ht
    intro x hx y hy
    by_contra hxy
    have hAdj : G.Adj x y := hs.1 hx.1 hy.1 hxy
    obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp (h x y hAdj)
    have hdet (r : Finset V) (hr : G.IsNClique 3 r) (hx' : x ∈ r) (hy' : y ∈ r) :
        r = {x,y,w} := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        by_cases hxz : x = z
        · simp [← hxz]
        by_cases hyz : y = z
        · simp [← hyz]
        have hwz : z ∈ G.neighborSet x ∩ G.neighborSet y :=
          ⟨hr.1 hx' hz hxz, hr.1 hy' hz hyz⟩
        rw [hw] at hwz
        simp [Set.mem_singleton_iff.mp hwz]
      · rw [hr.2]
        exact (Finset.card_insert_le _ _).trans (by
          have hcard := Finset.card_insert_le y ({w} : Finset V)
          simpa using Nat.succ_le_succ hcard)
    exact hst ((hdet s hs hx.1 hy.1).trans (hdet t ht hx.2 hy.2).symm)
  · intro x y hadj
    obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp (h x y hadj)
    have hm : w ∈ G.neighborSet x ∩ G.neighborSet y := by simp [hw]
    exact ⟨{x,y,w}, is3Clique_triple_iff.mpr ⟨hadj, hm.1, hm.2⟩, by simp, by simp⟩

lemma c50_counts
    (a : Fin 99 → Fin 99 → ℤ)
    (asymm : ∀ x y, a x y = a y x)
    (a0 : ∀ x, a x x = 0)
    (abin : ∀ x y, a x y * a x y = a x y)
    (total : (∑ x, ∑ y, a x y) = 1386)
    (cap : ∀ x y, x ≠ y → (∑ z, a x z * a y z) + a x y ≤ 2) :
    ∀ x y, x ≠ y → (∑ z, a x z * a y z) + a x y = 2 := by
  classical
  let d (x : Fin 99) := ∑ y, a x y
  let c (x y : Fin 99) := ∑ z, a x z * a y z
  have dc (x : Fin 99) : c x x = d x := by simp [c, d, abin]
  have sumd : ∑ x, d x = 1386 := total
  have col (z : Fin 99) : ∑ x, a x z = d z := by
    unfold d
    exact Finset.sum_congr rfl (fun x _ ↦ asymm x z)
  have cc (x : Fin 99) : ∑ y, c x y = ∑ z, a x z * d z := by
    unfold c
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, col]
  have sq : ∑ x, ∑ y, c x y = ∑ z, d z ^ 2 := by
    simp_rw [cc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, col, pow_two]
  let slack (x y : Fin 99) := (if x = y then d x - 2 else 0) + 2 - c x y - a x y
  have nonneg (x y : Fin 99) : 0 ≤ slack x y := by
    by_cases h : x = y
    · subst y; simp [slack, dc, a0]
    · have hc := cap x y h
      change c x y + a x y ≤ 2 at hc
      simp only [slack, if_neg h]; omega
  have row (x : Fin 99) : ∑ y, slack x y = 196 - ∑ y, c x y := by
    simp only [slack, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    change d x - 2 + _ - _ - d x = _
    ring
  have tt : ∑ x, ∑ y, slack x y = 19404 - ∑ z, d z ^ 2 := by
    simp_rw [row]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sq]
    norm_num
  have lin (x : Fin 99) : (d x - 14)^2 = d x^2 - 28 * d x + 196 := by ring
  have ss : ∑ x, (d x - 14)^2 = ∑ x, d x^2 - 19404 := by
    simp_rw [lin]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sumd,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have pos : 0 ≤ ∑ x, (d x - 14)^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have zero : ∑ x, ∑ y, slack x y = 0 := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun x _ ↦
      Finset.sum_nonneg (s := Finset.univ) (fun y _ ↦ nonneg x y))
    omega
  intro x y h
  have zr := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦
    Finset.sum_nonneg (fun j _ ↦ nonneg i j))).mp zero x (Finset.mem_univ x)
  have zv := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ nonneg x j)).mp zr y (Finset.mem_univ y)
  change c x y + a x y = 2
  simp only [slack, if_neg h] at zv
  omega

/-- At 693 edges all local common-neighbor bounds are attained. -/
lemma extremal :
  ∀ G : SimpleGraph (Fin 99), G.edgeSet.ncard = 693 →
    (∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)) →
    G.LocallyLinear ∧ ∀ x y, x ≠ y → ¬ G.Adj x y →
      (G.neighborSet x ∩ G.neighborSet y).ncard = 2 := by
  classical
  intro G hsize hcap
  let c50A (G : SimpleGraph (Fin 99)) (x y : Fin 99) : ℤ := if G.Adj x y then 1 else 0
  have c50_sumA (G : SimpleGraph (Fin 99)) (hm : G.edgeSet.ncard = 693) :
      ∑ x, ∑ y, c50A G x y = 1386 := by
    classical
    have row (x : Fin 99) : ∑ y, c50A G x y = (G.degree x : ℤ) := by
      simp only [c50A, Finset.sum_boole]
      congr 2
      ext y
      simp
    simp_rw [row]
    rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
    have he : G.edgeFinset.card = 693 := by
      simpa only [← G.coe_edgeFinset, Set.ncard_coe_finset] using hm
    rw [he]
    decide
  have c50_commonA (G : SimpleGraph (Fin 99)) (x y : Fin 99) :
      ∑ z, c50A G x z * c50A G y z =
        ((G.neighborSet x ∩ G.neighborSet y).ncard : ℤ) := by
    classical
    have h (z : Fin 99) : c50A G x z * c50A G y z =
        (if G.Adj x z ∧ G.Adj y z then 1 else 0 : ℤ) := by
      by_cases hx : G.Adj x z <;> by_cases hy : G.Adj y z <;> simp [c50A, hx, hy]
    simp_rw [h]
    rw [Finset.sum_boole]
    have hset : (↑(Finset.univ.filter (fun z => G.Adj x z ∧ G.Adj y z)) : Set (Fin 99)) =
        G.neighborSet x ∩ G.neighborSet y := by ext z; simp
    rw [← hset, Set.ncard_coe_finset]
  have symm (x y : Fin 99) : c50A G x y = c50A G y x := by
    simp only [c50A, G.adj_comm x y]
  have bot (x : Fin 99) : c50A G x x = 0 := by simp [c50A]
  have idem (x y : Fin 99) : c50A G x y * c50A G x y = c50A G x y := by
    by_cases h : G.Adj x y <;> simp [c50A, h]
  have caps (x y : Fin 99) (h : x ≠ y) :
      (∑ z, c50A G x z * c50A G y z) + c50A G x y ≤ 2 := by
    rw [c50_commonA]
    obtain ⟨hn, he⟩ := hcap x y h
    by_cases hadj : G.Adj x y
    · have := he hadj
      simp only [c50A, if_pos hadj]
      omega
    · simp only [c50A, if_neg hadj]
      omega
  have counted := c50_counts (c50A G) symm bot idem (c50_sumA G hsize) caps
  constructor
  · apply c50_local
    intro x y hadj
    have h := counted x y hadj.ne
    rw [c50_commonA] at h
    simp only [c50A, if_pos hadj] at h
    omega
  · intro x y hne hnot
    have h := counted x y hne
    rw [c50_commonA] at h
    simp only [c50A, if_neg hnot] at h
    omega

theorem boundMatrix
    (A : Fin 99 → Fin 99 → ℤ) (h : ℤ)
    (sym : ∀ x y, A x y = A y x)
    (diag : ∀ x, A x x = 0)
    (bin : ∀ x y, A x y = 0 ∨ A x y = 1)
    (total : (∑ x, ∑ y, A x y) = 1386 - 2*h)
    (cap : ∀ x y, x ≠ y → (∑ z, A x z * A y z) + A x y ≤ 2) :
    ∀ x, 183 * ((∑ y, A x y) - 14) ≤ 54*h := by
  classical
  let d (x : Fin 99) := ∑ y, A x y
  let b (x : Fin 99) := d x - 14
  let c (x y : Fin 99) := ∑ z, A x z * A y z
  let t (x : Fin 99) := 196 - ∑ z, A x z * d z
  have ann (x y : Fin 99) : 0 ≤ A x y := by rcases bin x y with h|h <;> omega
  have idm (x y : Fin 99) : A x y * A x y = A x y := by
    rcases bin x y with h|h <;> simp [h]
  have diagC (x : Fin 99) : c x x = d x := by simp [c, d, idm]
  have cnn (x y : Fin 99) : 0 ≤ c x y :=
    Finset.sum_nonneg (fun z _ ↦ mul_nonneg (ann x z) (ann y z))
  have col (z : Fin 99) : ∑ x, A x z = d z := by
    exact Finset.sum_congr rfl (fun x _ ↦ sym x z)
  have sumC (x : Fin 99) : ∑ y, c x y = ∑ z, A x z * d z := by
    unfold c
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, col]
  let slack (x y : Fin 99) := (if x = y then d x - 2 else 0) + 2 - c x y - A x y
  have nsl (x y : Fin 99) : 0 ≤ slack x y := by
    by_cases h : x = y
    · subst y; simp [slack, diagC, diag]
    · have hc := cap x y h
      change c x y + A x y ≤ 2 at hc
      simp only [slack, if_neg h]; omega
  have pos (x : Fin 99) : 0 ≤ t x := by
    have row : ∑ y, slack x y = t x := by
      simp only [slack, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      change d x - 2 + _ - _ - d x = 196 - _
      rw [sumC]
      ring
    rw [← row]
    exact Finset.sum_nonneg (fun j _ ↦ nsl x j)
  have sumd : ∑ i, d i = 1386 - 2*h := total
  have sumb : ∑ i, b i = -(2*h) := by
    simp only [b, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sumd]
    ring
  have sumt : ∑ i, t i + ∑ i, (b i)^2 = 56*h := by
    have sq : ∑ i, ∑ j, A i j * d j = ∑ j, d j ^ 2 := by
      rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, col, pow_two]
    have lin (x : Fin 99) : (b x)^2 = d x^2 - 28 * d x + 196 := by unfold b; ring
    simp_rw [lin]
    simp only [t, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sq, ← Finset.mul_sum, sumd]
    ring
  have tb (i : Fin 99) : t i = -14*b i - ∑ j, A i j * b j := by
    simp only [b, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    change 196 - _ = -14*d i - -14*14 - (_ - d i * 14)
    ring
  intro i
  have neigh : ∑ j, A i j * t j = 196*b i + 14*t i - ∑ k, c i k * b k := by
    have cs : ∑ j, A i j * (∑ k, A j k * b k) = ∑ k, c i k * b k := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      unfold c
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [sym j k]
      ring
    calc
      ∑ j, A i j * t j = -14*(∑ j, A i j * b j) - ∑ k, c i k * b k := by
        conv_lhs => enter [2,j]; rw [tb j, mul_sub, mul_left_comm]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, cs]
      _ = _ := by linarith [tb i]
  have compare : ∑ j, A i j * t j ≤ ∑ j, t j := by
    apply Finset.sum_le_sum
    intro j _
    rcases bin i j with h0|h1
    · simpa only [h0, zero_mul] using pos j
    · simp [h1]
  have lower : ∑ j, (-(b j) + (if i = j then -13*b i else 0)) ≤
      ∑ j, (b j^2 - c i j*b j) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · subst j
      simp only [if_true, diagC, b]; nlinarith
    · simp only [if_neg hij, add_zero]
      have hc := cap i j hij
      change c i j + A i j ≤ 2 at hc
      have hc' : c i j ≤ 2 := by linarith [ann i j]
      by_cases hb : 0 < b j
      · have aux : 0 ≤ b j + 1 - c i j := by omega
        nlinarith [mul_nonneg (le_of_lt hb) aux]
      · by_cases hz : b j = 0
        · simp [hz]
        · have aux : b j + 1 - c i j ≤ 0 := by have := cnn i j; omega
          nlinarith [mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hb) aux]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, sumb, Finset.sum_sub_distrib] at lower
  change 183*b i ≤ 54*h
  linarith [pos i]


open scoped Classical

/-- Every admissible packing satisfies this inequality at every vertex, at every edge count. -/
theorem degreeStability (G : SimpleGraph (Fin 99))
    (hcap : ∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)) :
    ∀ x, 183*((G.degree x : ℤ)-14) ≤ 54*(693 - G.edgeSet.ncard : ℤ) := by
  classical
  let c50A (G : SimpleGraph (Fin 99)) (x y : Fin 99) : ℤ := if G.Adj x y then 1 else 0
  have row (G : SimpleGraph (Fin 99)) (x : Fin 99) : ∑ y, c50A G x y = (G.degree x : ℤ) := by
    simp only [c50A, Finset.sum_boole]
    congr 2
    ext y
    simp
  have total : ∑ x, ∑ y, c50A G x y = 1386 - 2*(693 - G.edgeSet.ncard : ℤ) := by
    simp_rw [row]
    rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
    have he : G.edgeFinset.card = G.edgeSet.ncard := by
      simp only [← G.coe_edgeFinset, Set.ncard_coe_finset]
    rw [he]
    push_cast
    ring
  have c50_commonA (G : SimpleGraph (Fin 99)) (x y : Fin 99) :
      ∑ z, c50A G x z * c50A G y z =
        ((G.neighborSet x ∩ G.neighborSet y).ncard : ℤ) := by
    classical
    have h (z : Fin 99) : c50A G x z * c50A G y z =
        (if G.Adj x z ∧ G.Adj y z then 1 else 0 : ℤ) := by
      by_cases hx : G.Adj x z <;> by_cases hy : G.Adj y z <;> simp [c50A, hx, hy]
    simp_rw [h]
    rw [Finset.sum_boole]
    have hset : (↑(Finset.univ.filter (fun z => G.Adj x z ∧ G.Adj y z)) : Set (Fin 99)) =
        G.neighborSet x ∩ G.neighborSet y := by ext z; simp
    rw [← hset, Set.ncard_coe_finset]
  have symm (x y : Fin 99) : c50A G x y = c50A G y x := by
    simp only [c50A, G.adj_comm x y]
  have bot (x : Fin 99) : c50A G x x = 0 := by simp [c50A]
  have caps (x y : Fin 99) (h : x ≠ y) :
      (∑ z, c50A G x z * c50A G y z) + c50A G x y ≤ 2 := by
    rw [c50_commonA]
    obtain ⟨hn, he⟩ := hcap x y h
    by_cases hadj : G.Adj x y
    · have := he hadj
      simp only [c50A, if_pos hadj]
      omega
    · simp only [c50A, if_neg hadj]
      omega
  have bin (x y : Fin 99) : c50A G x y = 0 ∨ c50A G x y = 1 := by
    by_cases h : G.Adj x y <;> simp [c50A, h]
  intro x
  have r := boundMatrix (c50A G) _ symm bot bin total caps x
  rwa [row] at r

/-- A packing with at least 690 edges has maximum degree at most fourteen. -/
theorem denseMaxDegree (G : SimpleGraph (Fin 99))
    (edges : 690 ≤ G.edgeSet.ncard)
    (hcap : ∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)) :
    ∀ x, G.degree x ≤ 14 := by
  intro x
  have h := degreeStability G hcap x
  omega


/-- Find a packing three edges short of the extremal edge count. -/
def H1 : Prop :=
  ∃ G : SimpleGraph (Fin 99), G.edgeSet.ncard = 690 ∧
    ∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)

/-- Augment a 690–692 edge packing whose degrees are all at most 14; denseMaxDegree proves this restriction automatically. -/
def H2 : Prop :=
  ∀ G : SimpleGraph (Fin 99), 690 ≤ G.edgeSet.ncard → G.edgeSet.ncard ≤ 692 →
    (∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)) →
    (∀ x, G.degree x ≤ 14) →
    ∃ K : SimpleGraph (Fin 99),
      (∃ u v, u ≠ v ∧ ¬ G.Adj u v ∧ K = G ⊔ SimpleGraph.edge u v) ∧
      K.edgeSet.ncard = G.edgeSet.ncard + 1 ∧
      ∀ x y, x ≠ y →
        (K.neighborSet x ∩ K.neighborSet y).ncard ≤ 2 ∧
        (K.Adj x y → (K.neighborSet x ∩ K.neighborSet y).ncard ≤ 1)

theorem main : H1 → H2 → type_of% @Conway99Graph.conway99Graph := by
  rintro ⟨G, hG, cG⟩ extend
  obtain ⟨J, _, hJ, cJ⟩ := extend G (by omega) (by omega) cG (denseMaxDegree G (by omega) cG)
  obtain ⟨K, _, hK, cK⟩ := extend J (by omega) (by omega) cJ (denseMaxDegree J (by omega) cJ)
  obtain ⟨L, _, hL, cL⟩ := extend K (by omega) (by omega) cK (denseMaxDegree K (by omega) cK)
  obtain ⟨hlin, hdiag⟩ := extremal L (by omega) cL
  exact ⟨L, hlin, fun x y hxy ↦ hdiag x y hxy⟩

end OMA.R_Conway99Graph_conway99Graph_R1
