import OMAReductions.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1

/-! The complete-host preparation for Allen--Böttcher--Clemens--Hladký--
Piguet--Taraz, Theorem 10. There is an exact edge budget and a separate
reserve of two independent leaves per parity-correction tree. The two
packing inputs distinguish even and odd host orders. -/

namespace OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1_H4_R1

open Filter Finset SimpleGraph
open scoped Classical

private theorem independent_leaves {k : ℕ} {G : SimpleGraph (Fin k)}
    (hk : 3 ≤ k) (ht : G.IsTree) :
    ∃ x y : Fin k, x ≠ y ∧ G.degree x = 1 ∧ G.degree y = 1 ∧ ¬ G.Adj x y := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨x, y, hxy, hx, hy⟩ := ht.exists_ne_and_degree_eq_one
  refine ⟨x, y, hxy, hx, hy, ?_⟩
  intro hadj
  have uniq {u v : Fin k} (hu : G.degree u = 1) (huv : G.Adj u v) :
      ∀ w : Fin k, G.Adj u w → w = v := by
    obtain ⟨z, _, hz⟩ := degree_eq_one_iff_existsUnique_adj.mp hu
    exact fun w huw ↦ (hz w huw).trans (hz v huv).symm
  have stay {u v : Fin k} (p : G.Walk u v) : u = x ∨ u = y → v = x ∨ v = y := by
    induction p with
    | nil => exact id
    | @cons u w v huw _ ih =>
      intro hu
      apply ih
      rcases hu with rfl | rfl
      · exact Or.inr (uniq hx hadj w huw)
      · exact Or.inl (uniq hy hadj.symm w huw)
  have all (w : Fin k) : w ∈ ({x, y} : Finset (Fin k)) := by
    obtain ⟨p⟩ := ht.connected.preconnected x w
    simpa only [mem_insert, mem_singleton] using stay p (Or.inl rfl)
  have hc := card_le_card (show (univ : Finset (Fin k)) ⊆ {x, y} from fun w _ ↦ all w)
  simp [hxy] at hc
  omega

private theorem edge_budget (n : ℕ) :
    (∑ k ∈ Icc 2 n, (k - 1)) = n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    by_cases hn : 2 ≤ n + 1
    · have hinterval : Icc 2 (n + 1) = insert (n + 1) (Icc 2 n) := by
        ext k
        simp only [mem_Icc, mem_insert]
        omega
      have hnot : n + 1 ∉ Icc 2 n := by simp
      rw [hinterval, sum_insert hnot, ih, Nat.choose_succ_succ]
      simp
    · have hz : n = 0 := by omega
      subst n
      decide

/-- Complete-host packing with explicit disjoint reserves at even orders. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, Even n →
    ∀ T : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧ ((T k).maxDegree : ℝ) ≤ c * (n : ℝ) / Real.log n) →
      (∑ k ∈ Icc 2 n, (T k).edgeFinset.card) = n.choose 2 →
      (∃ J K : Finset ℕ, J ⊆ Icc 3 (7 * n / 8) ∧ K ⊆ Icc 3 (7 * n / 8) ∧ Disjoint J K ∧
        J.card = n / 100000000 ∧ n + n / 100000000 ≤ 2 * K.card ∧
        (∀ k ∈ J, ∃ f : Fin (n / 100000000) × Fin 12 → Fin k, Function.Injective f ∧
          (∀ i (j : Fin 11), (T k).Adj (f (i, j.castSucc)) (f (i, j.succ))) ∧
          ∀ i j, (T k).degree (f (i, j)) = 2) ∧
        (∀ k ∈ K, ∃ x y : Fin k, x ≠ y ∧ (T k).degree x = 1 ∧
          (T k).degree y = 1 ∧ ¬ (T k).Adj x y)) →
      Erdos743.IsPacking n (Set.Icc 2 n) T

/-- Complete-host packing with explicit disjoint reserves at odd orders. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, Odd n →
    ∀ T : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧ ((T k).maxDegree : ℝ) ≤ c * (n : ℝ) / Real.log n) →
      (∑ k ∈ Icc 2 n, (T k).edgeFinset.card) = n.choose 2 →
      (∃ J K : Finset ℕ, J ⊆ Icc 3 (7 * n / 8) ∧ K ⊆ Icc 3 (7 * n / 8) ∧ Disjoint J K ∧
        J.card = n / 100000000 ∧ n + n / 100000000 ≤ 2 * K.card ∧
        (∀ k ∈ J, ∃ f : Fin (n / 100000000) × Fin 12 → Fin k, Function.Injective f ∧
          (∀ i (j : Fin 11), (T k).Adj (f (i, j.castSucc)) (f (i, j.succ))) ∧
          ∀ i j, (T k).degree (f (i, j)) = 2) ∧
        (∀ k ∈ K, ∃ x y : Fin k, x ≠ y ∧ (T k).degree x = 1 ∧
          (T k).degree y = 1 ∧ ¬ (T k).Adj x y)) →
      Erdos743.IsPacking n (Set.Icc 2 n) T

theorem main : H1 → H2 → OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1.H4 := by
  classical
  intro heven hodd
  obtain ⟨a, ha, ea⟩ := heven
  obtain ⟨b, hb, eb⟩ := hodd
  refine ⟨min a b, lt_min ha hb, ?_⟩
  filter_upwards [ea, eb, eventually_ge_atTop (100000000 : ℕ)] with n hEven hOdd hn
  intro T ht
  dsimp only
  intro hpaths
  let r := n / 100000000
  let middle := Icc 3 (7 * n / 8)
  let pathRich := (Icc ((n + 7) / 8) (7 * n / 8)).filter fun k ↦
    ∃ f : Fin r × Fin 12 → Fin k, Function.Injective f ∧
      (∀ i (j : Fin 11), (T k).Adj (f (i, j.castSucc)) (f (i, j.succ))) ∧
      ∀ i j, (T k).degree (f (i, j)) = 2
  obtain ⟨J, hJ, hJcard⟩ := exists_subset_card_eq (show r ≤ pathRich.card from hpaths)
  have hJmiddle : J ⊆ middle := by
    intro k hk
    have ⟨hl, hu⟩ := mem_Icc.mp (mem_filter.mp (hJ hk)).1
    exact mem_Icc.mpr ⟨by omega, hu⟩
  let K := middle \ J
  have hdisjoint : Disjoint J K := disjoint_sdiff
  have hKcard : n + r ≤ 2 * K.card := by
    dsimp [K, middle, r]
    rw [card_sdiff_of_subset hJmiddle, hJcard, Nat.card_Icc]
    dsimp [r]
    omega
  have reserveLeaves (k : ℕ) (hk : k ∈ K) :
      ∃ x y : Fin k, x ≠ y ∧ (T k).degree x = 1 ∧ (T k).degree y = 1 ∧ ¬ (T k).Adj x y := by
    obtain ⟨hl, hu⟩ := mem_Icc.mp (mem_sdiff.mp hk).1
    exact independent_leaves hl (ht k ⟨by omega, by omega⟩).1
  have hedge : (∑ k ∈ Icc 2 n, (T k).edgeFinset.card) = n.choose 2 := by
    calc
      _ = ∑ k ∈ Icc 2 n, (k - 1) := by
        apply sum_congr rfl
        intro k hk
        have h := (ht k (by simpa using hk)).1.card_edgeFinset
        simp only [Fintype.card_fin] at h
        omega
      _ = _ := edge_budget n
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have bounded (c : ℝ) (hc : min a b ≤ c) (k : ℕ) (hk : k ∈ Set.Icc 2 n) :
      (T k).IsTree ∧ ((T k).maxDegree : ℝ) ≤ c * (n : ℝ) / Real.log n :=
    ⟨(ht k hk).1, (ht k hk).2.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)) hlog)⟩
  rcases Nat.even_or_odd n with h | h <;>
    first
    | apply hEven h T (bounded a (min_le_left _ _)) hedge
    | apply hOdd h T (bounded b (min_le_right _ _)) hedge
  all_goals
    exact ⟨J, K, hJmiddle, sdiff_subset, hdisjoint, hJcard, hKcard,
      (fun k hk ↦ (mem_filter.mp (hJ hk)).2), reserveLeaves⟩

end OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1_H4_R1
