import FormalConjectures.ErdosProblems.«643»

/-!
# Exact extremal lower construction for Erdős Problem 643

Credit: @justusklocke-cloud
Reference: https://arxiv.org/abs/2609.37744
-/

namespace OMA.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1

open Filter
open Finset

private theorem star_union_matching_free {α : Type*} [DecidableEq α]
    {S M : Finset (Finset α)} {v : α} {t : ℕ} (ht : 0 < t)
    (hS : ∀ E ∈ S, v ∈ E) (hM : ∀ E ∈ M, v ∉ E)
    (hpair : ∀ {E F}, E ∈ M → F ∈ M → E ≠ F → Disjoint E F)
    (hU : (S ∪ M).IsUniform t) : ¬ (S ∪ M).HasRepeatedDisjointUnion := by
  rintro ⟨A, hA, B, hB, C, hC, D, hD, hAB, hCD, heq, _, _, hAC, hAD, hBC, hBD⟩
  have matching_of_avoids {E : Finset α} (hE : E ∈ S ∪ M) (hnv : v ∉ E) : E ∈ M :=
    (Finset.mem_union.mp hE).resolve_left fun h => hnv (hS E h)
  have pick_matching {X Y : Finset α} (hX : X ∈ S ∪ M) (hY : Y ∈ S ∪ M)
      (hXY : Disjoint X Y) : ∃ E ∈ M, E = X ∨ E = Y := by
    by_cases hvX : v ∈ X
    · exact ⟨Y, matching_of_avoids hY (Finset.disjoint_left.mp hXY hvX), Or.inr rfl⟩
    · exact ⟨X, matching_of_avoids hX hvX, Or.inl rfl⟩
  by_cases hv : v ∈ A ∪ B
  · obtain ⟨E, hEM, hE⟩ := pick_matching hA hB hAB
    obtain ⟨F, hFM, hF⟩ := pick_matching hC hD hCD
    have hne : E ≠ F := by
      rcases hE with rfl | rfl <;> rcases hF with rfl | rfl <;> assumption
    have hESub : E ⊆ A ∪ B := by
      rcases hE with rfl | rfl
      · exact Finset.subset_union_left
      · exact Finset.subset_union_right
    have hFSub : F ⊆ A ∪ B := by
      rw [heq]
      rcases hF with rfl | rfl
      · exact Finset.subset_union_left
      · exact Finset.subset_union_right
    have hvEF : v ∉ E ∪ F := by simp [hM E hEM, hM F hFM]
    have hle := Finset.card_le_card (Finset.insert_subset hv (Finset.union_subset hESub hFSub))
    rw [Finset.card_insert_of_notMem hvEF, Finset.card_union_of_disjoint (hpair hEM hFM hne),
      hU _ (Finset.mem_union_right S hEM), hU _ (Finset.mem_union_right S hFM),
      Finset.card_union_of_disjoint hAB, hU _ hA, hU _ hB] at hle
    omega
  · have hv' : v ∉ C ∪ D := heq ▸ hv
    have hAM := matching_of_avoids hA fun hm => hv (Finset.mem_union_left B hm)
    have hCM := matching_of_avoids hC fun hm => hv' (Finset.mem_union_left D hm)
    have hDM := matching_of_avoids hD fun hm => hv' (Finset.mem_union_right C hm)
    have hApos : 0 < A.card := (hU _ hA).symm ▸ ht
    obtain ⟨x, hxA⟩ := Finset.card_pos.mp hApos
    have hx : x ∈ C ∪ D := heq ▸ Finset.mem_union_left B hxA
    rcases Finset.mem_union.mp hx with hxC | hxD
    · exact Finset.disjoint_left.mp (hpair hAM hCM hAC) hxA hxC
    · exact Finset.disjoint_left.mp (hpair hAM hDM hAD) hxA hxD

/-- The explicit Füredi construction attains the predicted extremal quantity from below. -/
private theorem starPlusBlocksLower (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    (n - 1).choose (t - 1) + (n - 1) / t ≤
      Hypergraph.extremalNumber n t (fun H ↦ ¬ H.HasRepeatedDisjointUnion) := by
  classical
  let v : Fin n := ⟨0, hn⟩
  let m := (n - 1) / t
  have hm : m * t ≤ n - 1 := Nat.div_mul_le_self _ _
  have hbound (i : Fin m) (j : Fin t) : 1 + i.val * t + j.val < n := by
    have hi := Nat.mul_le_mul_right t (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hi
    have hj := j.isLt
    omega
  let emb (i : Fin m) : Fin t ↪ Fin n := ⟨fun j => ⟨1 + i.val * t + j.val, hbound i j⟩, by
    intro j k h
    apply Fin.ext
    have he := congrArg Fin.val h
    change 1 + i.val * t + j.val = 1 + i.val * t + k.val at he
    omega⟩
  let block (i : Fin m) : Finset (Fin n) := (Finset.univ : Finset (Fin t)).map (emb i)
  have hcard (i : Fin m) : (block i).card = t := by simp [block]
  have hav (i : Fin m) : v ∉ block i := by
    intro hi
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
    have he := congrArg Fin.val hj
    change 1 + i.val * t + j.val = 0 at he
    omega
  have disjoint_of_lt (i j : Fin m) (hij : i.val < j.val) : Disjoint (block i) (block j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hy
    have he := congrArg Fin.val (ha.trans hb.symm)
    change 1 + i.val * t + a.val = 1 + j.val * t + b.val at he
    have hle := Nat.mul_le_mul_right t (Nat.succ_le_of_lt hij)
    rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hle
    have ha' := a.isLt
    omega
  have hblocks {i j : Fin m} (hne : i ≠ j) : Disjoint (block i) (block j) := by
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact disjoint_of_lt i j h
    · exact (disjoint_of_lt j i h).symm
  have hinj : Function.Injective block := by
    intro i j he
    by_contra! hij
    have hd := hblocks hij
    rw [he] at hd
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (block j).card by rwa [hcard])
    exact Finset.disjoint_left.mp hd hx hx
  let S := ((Finset.univ : Finset (Fin n)).powersetCard t).filter fun E => {v} ⊆ E
  let M := (Finset.univ : Finset (Fin m)).image block
  have hScard : S.card = (n - 1).choose (t - 1) := by
    simpa [S] using Finset.card_filter_powersetCard_subset ({v} : Finset (Fin n))
      Finset.univ t (by simp) (by simpa using Nat.succ_le_of_lt ht)
  have hMcard : M.card = m := by simp [M, Finset.card_image_of_injective _ hinj]
  have hS (E : Finset (Fin n)) (hE : E ∈ S) : v ∈ E :=
    (Finset.mem_filter.mp hE).2 (by simp)
  have hM (E : Finset (Fin n)) (hE : E ∈ M) : v ∉ E := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hE
    exact hav i
  have hpair {E F : Finset (Fin n)} (hE : E ∈ M) (hF : F ∈ M) (hne : E ≠ F) : Disjoint E F := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hF
    exact hblocks (fun h => hne (congrArg block h))
  have hunif : (S ∪ M).IsUniform t := by
    intro E hE
    rcases Finset.mem_union.mp hE with hE | hE
    · exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hE).1).2
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hE
      exact hcard i
  have hfree := star_union_matching_free ht hS hM hpair hunif
  have hd : Disjoint S M := by
    apply Finset.disjoint_left.mpr
    intro E hES hEM
    exact hM E hEM (hS E hES)
  have htotal : (S ∪ M).card = (n - 1).choose (t - 1) + (n - 1) / t := by
    rw [Finset.card_union_of_disjoint hd, hScard, hMcard]
  by_contra! h
  have hforce : Erdos643.forcingThreshold n t ≤ (S ∪ M).card := by
    rw [htotal, Erdos643.forcingThreshold]
    omega
  exact hfree ((Erdos643.forcingThreshold_le_iff n t _).mp hforce _ hunif le_rfl)

private theorem correction_le_deficit {n c m : ℕ} (hn : 0 < n)
    (hc : 4 * c ≤ n) (hsmall : 4 * c ^ 2 * m ≤ n ^ 2) :
    2 * (c * m / n) * (c * m / n + 1) ≤ m := by
  let k := c * m / n
  have hk : k * n ≤ c * m := Nat.div_mul_le_self _ _
  have hkNext : (k + 1) * n ≤ c * m + n := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_right hk n
  have hcn := Nat.mul_le_mul_right n hc
  have hcoef : 2 * c * (c * m + n) ≤ n * n := by
    nlinarith only [hsmall, hcn]
  apply Nat.le_of_mul_le_mul_right _ (Nat.mul_pos hn hn)
  calc
    (2 * k * (k + 1)) * (n * n) = 2 * ((k * n) * ((k + 1) * n)) := by ring
    _ ≤ 2 * ((c * m) * (c * m + n)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul hk hkNext)
    _ = m * (2 * c * (c * m + n)) := by ring
    _ ≤ m * (n * n) := Nat.mul_le_mul_left m hcoef

private theorem degree_le_star {n t : ℕ} {F : Finset (Finset (Fin n))}
    (ht : 1 ≤ t) (hF : F.IsUniform t) (v : Fin n) :
    (F.filter (fun e => v ∈ e)).card ≤ (n - 1).choose (t - 1) := by
  calc
    (F.filter (fun e => v ∈ e)).card ≤
        (((Finset.univ : Finset (Fin n)).powersetCard t).filter
          (fun e => {v} ⊆ e)).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hF e he⟩,
          Finset.singleton_subset_iff.mpr hv⟩
    _ = (n - 1).choose (t - 1) := by
      simpa using Finset.card_filter_powersetCard_subset
        ({v} : Finset (Fin n)) Finset.univ t (Finset.subset_univ _) (by simpa using ht)

private theorem edge_bound {n t c : ℕ} {F : Finset (Finset (Fin n))}
    (hn : 0 < n) (ht : 2 ≤ t) (hc : 4 * c ≤ n) (hF : F.IsUniform t) (v : Fin n)
    (hsmall : 4 * c ^ 2 * ((n - 1).choose (t - 1) - (F.filter (fun e => v ∈ e)).card) ≤ n ^ 2)
    (hoff :
      let m := (n - 1).choose (t - 1) - (F.filter (fun e => v ∈ e)).card
      let k := c * m / n
      t * (F.filter (fun e => v ∉ e)).card ≤ m + (n - 1) + 2 * k * (k + 1)) :
    F.card ≤ (n - 1).choose (t - 1) + (n - 1) / t := by
  let star := (F.filter (fun e => v ∈ e)).card
  let off := (F.filter (fun e => v ∉ e)).card
  let m := (n - 1).choose (t - 1) - star
  have hcorr := correction_le_deficit hn hc hsmall
  have hoff' : t * off ≤ (n - 1) + t * m := by
    have htMul : 2 * m ≤ t * m := Nat.mul_le_mul_right m ht
    change t * off ≤ m + (n - 1) + 2 * (c * m / n) * (c * m / n + 1) at hoff
    change 2 * (c * m / n) * (c * m / n + 1) ≤ m at hcorr
    omega
  have hdiv : off ≤ ((n - 1) + t * m) / t :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [Nat.mul_comm] using hoff')
  rw [Nat.add_mul_div_left _ _ (by omega)] at hdiv
  have hstar : star ≤ (n - 1).choose (t - 1) := degree_le_star (by omega) hF v
  have hsplit : star + off = F.card := Finset.card_filter_add_card_filter_not (s := F) (fun e => v ∈ e)
  have hbase : star + m = (n - 1).choose (t - 1) := by
    dsimp only [m]
    omega
  omega

/-- A sufficiently large almost-extremal family has a vertex with small star deficit. -/
def H1 : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    ∀ F : Finset (Finset (Fin n)), F.IsUniform t → ¬ F.HasRepeatedDisjointUnion →
      (n - 1).choose (t - 1) + (n - 1) / t ≤ F.card →
      ∃ v : Fin n,
        (↑((n - 1).choose (t - 1) - (F.filter (fun e => v ∈ e)).card) : ℝ) ≤
          δ * ↑((n - 1).choose (t - 1))

/-- For a sufficiently full star, the deficit is smaller than a fixed multiple of n squared. -/
def H2 : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
    ∀ F : Finset (Finset (Fin n)), F.IsUniform t → ¬ F.HasRepeatedDisjointUnion →
      (n - 1).choose (t - 1) + (n - 1) / t ≤ F.card → ∀ v : Fin n,
        let s := (n - 1).choose (t - 1)
        let m := s - (F.filter (fun e => v ∈ e)).card
        let c := 4 * t ^ (2 * t)
        (m : ℝ) ≤ δ * (s : ℝ) → 4 * c ^ 2 * m ≤ n ^ 2

/-- With this small deficit, the off-star edges satisfy the finite degree bound from (11). -/
def H3 : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ᶠ n : ℕ in atTop,
    ∀ F : Finset (Finset (Fin n)), F.IsUniform t → ¬ F.HasRepeatedDisjointUnion →
      ∀ v : Fin n,
        let m := (n - 1).choose (t - 1) - (F.filter (fun e => v ∈ e)).card
        let c := 4 * t ^ (2 * t)
        let k := c * m / n
        4 * c ^ 2 * m ≤ n ^ 2 →
          t * (F.filter (fun e => v ∉ e)).card ≤ m + (n - 1) + 2 * k * (k + 1)

theorem main : H1 → H2 → H3 → type_of% @Erdos643.erdos_643.variants.exact_t_ge_four := by
  intro hstability hsmallDeficit hoffStar t ht
  obtain ⟨δ, hδ, hdeficit⟩ := hsmallDeficit t ht
  let c := 4 * t ^ (2 * t)
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop (4 * c),
    hstability t ht δ hδ, hdeficit, hoffStar t ht] with n hn hc hstab hsmall hoff
  have hlo := starPlusBlocksLower n t (by omega) (by omega)
  refine le_antisymm ?_ hlo
  obtain ⟨F, hF, havoids, hmax⟩ := Erdos643.exists_avoiding_maximizer n t
  have hcard : F.card = Hypergraph.extremalNumber n t (fun H => ¬ H.HasRepeatedDisjointUnion) := by
    unfold Erdos643.forcingThreshold at hmax
    omega
  have hbase : (n - 1).choose (t - 1) + (n - 1) / t ≤ F.card := by
    rw [hcard]
    exact hlo
  obtain ⟨v, hv⟩ := hstab F hF havoids hbase
  have hvsmall := hsmall F hF havoids hbase v hv
  have hvcount := hoff F hF havoids v hvsmall
  rw [← hcard]
  exact edge_bound (c := c) (by omega) (by omega) hc hF v hvsmall hvcount

end OMA.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1
