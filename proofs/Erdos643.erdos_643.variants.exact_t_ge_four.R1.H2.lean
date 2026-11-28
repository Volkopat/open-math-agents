import OMAReductions.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1
import Mathlib

/-!
# Erdős 643: the star deficit bound

The proof follows Huang–Ma–Yang, arXiv:2609.37744, Section 3.2.
The auxiliary crude bound on induced hypergraphs uses a tripartite
specialization of the charge method in arXiv:2610.34038, Section 2,
together with rainbow coloring and coordinate-shift partitioning.

Credit: @justusklocke-cloud
-/

open Finset
open scoped BigOperators

namespace Erdos643CommonFiller

open scoped BigOperators

theorem forbidden_extensions {V : Type*} [DecidableEq V] {F : Finset (Finset V)}
    (hfree : ¬ F.HasRepeatedDisjointUnion) {v : V} {S T U X : Finset V}
    (hvS : v ∉ S) (hvT : v ∉ T) (hvU : v ∉ U) (hT : T.Nonempty)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hXS : Disjoint X S) (hXT : Disjoint X T) (hXU : Disjoint X U)
    (hA : S ∪ T ∈ F) (hC : S ∪ U ∈ F) :
    ¬ (insert v (X ∪ U) ∈ F ∧ insert v (X ∪ T) ∈ F) := by
  rintro ⟨hB,hD⟩
  have hvA : v ∉ S ∪ T := by simp [hvS, hvT]
  have hvC : v ∉ S ∪ U := by simp [hvS, hvU]
  have hAB : Disjoint (S ∪ T) (insert v (X ∪ U)) := by
    simp [Finset.disjoint_insert_right, hvA, Finset.disjoint_union_left,
      Finset.disjoint_union_right, hXS.symm, hSU, hXT.symm, hTU]
  have hCD : Disjoint (S ∪ U) (insert v (X ∪ T)) := by
    simp [Finset.disjoint_insert_right, hvC, Finset.disjoint_union_left,
      Finset.disjoint_union_right, hXS.symm, hST, hXU.symm, hTU.symm]
  have heq : (S ∪ T) ∪ insert v (X ∪ U) = (S ∪ U) ∪ insert v (X ∪ T) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  obtain ⟨x, hx⟩ := hT
  have hxS : x ∉ S := fun h => Finset.disjoint_left.mp hST h hx
  have hxX : x ∉ X := fun h => Finset.disjoint_left.mp hXT h hx
  have hxU : x ∉ U := Finset.disjoint_left.mp hTU hx
  have hxv : x ≠ v := fun h => hvT (h ▸ hx)
  have hAC : S ∪ T ≠ S ∪ U := by
    intro h
    have hj : x ∈ S ∪ U := h ▸ Finset.mem_union_right S hx
    exact (Finset.mem_union.mp hj).elim hxS hxU
  have hBD : insert v (X ∪ U) ≠ insert v (X ∪ T) := by
    intro h
    have hj : x ∈ insert v (X ∪ U) := h.symm ▸
      Finset.mem_insert_of_mem (Finset.mem_union_right X hx)
    simp [hxv, hxX, hxU] at hj
  have off_ne_center {A B : Finset V} (hv : v ∉ A) : A ≠ insert v B := by
    intro h
    exact hv (h.symm ▸ Finset.mem_insert_self v B)
  exact hfree ⟨_, hA, _, hB, _, hC, _, hD, hAB, hCD, heq,
    off_ne_center hvA, off_ne_center hvC, hAC, off_ne_center hvA,
    (off_ne_center hvC).symm, hBD⟩

/-- The two sets of missing extensions cover every admissible filler. -/
theorem filler_count_le_missing {V : Type*} [DecidableEq V] {F : Finset (Finset V)}
    (hfree : ¬ F.HasRepeatedDisjointUnion) {v : V} {S T U Y : Finset V} (k : ℕ)
    (hvS : v ∉ S) (hvT : v ∉ T) (hvU : v ∉ U) (hT : T.Nonempty)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hYS : Disjoint Y S) (hYT : Disjoint Y T) (hYU : Disjoint Y U)
    (hA : S ∪ T ∈ F) (hC : S ∪ U ∈ F) :
    let P := Y.powersetCard k
    P.card ≤ (P.filter (fun X => insert v (X ∪ T) ∉ F)).card +
      (P.filter (fun X => insert v (X ∪ U) ∉ F)).card := by
  dsimp only
  let P := Y.powersetCard k
  let missT := P.filter (fun X => insert v (X ∪ T) ∉ F)
  let missU := P.filter (fun X => insert v (X ∪ U) ∉ F)
  have hcover : P ⊆ missT ∪ missU := by
    intro X hX
    have hXY := (Finset.mem_powersetCard.mp hX).1
    have hmiss := forbidden_extensions hfree hvS hvT hvU hT hST hSU hTU
      (hYS.mono_left hXY) (hYT.mono_left hXY) (hYU.mono_left hXY) hA hC
    by_cases hXT : insert v (X ∪ T) ∈ F
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hX, fun h => hmiss ⟨h, hXT⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hX, hXT⟩)
  exact (Finset.card_le_card hcover).trans (Finset.card_union_le missT missU)

/-- Count incidences between exceptional small sets and missing star links. -/
theorem exceptional_card_bound {V : Type*} [DecidableEq V] {M Q : Finset (Finset V)}
    {r i b : ℕ} (hM : ∀ A ∈ M, A.card = r) (hQ : ∀ T ∈ Q, T.card = i)
    (hmiss : ∀ T ∈ Q, b ≤ 2 * (M.filter (fun A => T ⊆ A)).card) :
    Q.card * b ≤ 2 * M.card * r.choose i := by
  have hswap : (∑ T ∈ Q, (M.filter (fun A => T ⊆ A)).card) =
      ∑ A ∈ M, (Q.filter (fun T => T ⊆ A)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hbound (A : Finset V) (hA : A ∈ M) :
      (Q.filter (fun T => T ⊆ A)).card ≤ r.choose i := by
    calc
      (Q.filter (fun T => T ⊆ A)).card ≤ (A.powersetCard i).card := by
        apply Finset.card_le_card
        intro T hT
        obtain ⟨hTQ, hTA⟩ := Finset.mem_filter.mp hT
        exact Finset.mem_powersetCard.mpr ⟨hTA, hQ T hTQ⟩
      _ = r.choose i := by rw [Finset.card_powersetCard, hM A hA]
  calc
    Q.card * b = ∑ _ ∈ Q, b := by simp
    _ ≤ ∑ T ∈ Q, 2 * (M.filter (fun A => T ⊆ A)).card := Finset.sum_le_sum hmiss
    _ = 2 * ∑ A ∈ M, (Q.filter (fun T => T ⊆ A)).card := by rw [← Finset.mul_sum, hswap]
    _ ≤ 2 * ∑ _ ∈ M, r.choose i := Nat.mul_le_mul_left 2 (Finset.sum_le_sum hbound)
    _ = 2 * M.card * r.choose i := by simp [Nat.mul_assoc]

end Erdos643CommonFiller

namespace Erdos643MissingLinkMap

/-- Adjoining the fixed remainder `T` injects missing fillers into missing star
links containing `T`. -/
theorem missing_fillers_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) {Y T : Finset α} {v : α} {k i r : ℕ}
    (hYT : Disjoint Y T) (hvY : v ∉ Y) (hvT : v ∉ T)
    (hT : T.card = i) (hki : k + i = r - 1) :
    let P := Y.powersetCard k
    let M := ((Finset.univ.erase v).powersetCard (r - 1)).filter fun A => insert v A ∉ F
    (P.filter fun X => insert v (X ∪ T) ∉ F).card ≤ (M.filter fun A => T ⊆ A).card := by
  apply Finset.card_le_card_of_injOn (fun X => X ∪ T)
  · intro X hX
    obtain ⟨hXP, hmiss⟩ := Finset.mem_filter.mp hX
    obtain ⟨hXY, hXcard⟩ := Finset.mem_powersetCard.mp hXP
    have hvX : v ∉ X := fun h => hvY (hXY h)
    have hnot : v ∉ X ∪ T := by simp [hvX, hvT]
    have hsub : X ∪ T ⊆ Finset.univ.erase v := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact hnot hx
    have hcard : (X ∪ T).card = r - 1 := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left hXY hYT), hXcard, hT, hki]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, hmiss⟩,
        Finset.subset_union_right⟩
  · intro X hX Z hZ heq
    have hXY := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hX).1).1
    have hZY := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hZ).1).1
    have hx : Disjoint X T := Finset.disjoint_of_subset_left hXY hYT
    have hz : Disjoint Z T := Finset.disjoint_of_subset_left hZY hYT
    exact Finset.disjoint_injOn_union_left T hx.symm hz.symm heq

end Erdos643MissingLinkMap

namespace Erdos643CommonFiller

/-- When two off-star edges have disjoint remainders, at least one remainder
has many missing star completions. -/
theorem disjoint_remainders_force_exceptional
    {V : Type*} [Fintype V] [DecidableEq V] {F : Finset (Finset V)} {v : V}
    {S T U : Finset V} {t i : ℕ} (hi : 1 ≤ i) (hit : i ≤ t - 1)
    (hS : S.card = t - i) (hT : T.card = i) (hU : U.card = i)
    (hvS : v ∉ S) (hvT : v ∉ T) (hvU : v ∉ U)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hfree : ¬ F.HasRepeatedDisjointUnion) (hA : S ∪ T ∈ F) (hC : S ∪ U ∈ F) :
    let M := ((Finset.univ.erase v).powersetCard (t - 1)).filter (fun E => insert v E ∉ F)
    let B := (Fintype.card V - 2 * t).choose (t - 1 - i)
    B ≤ 2 * (M.filter (fun E => T ⊆ E)).card ∨
    B ≤ 2 * (M.filter (fun E => U ⊆ E)).card := by
  let M := ((Finset.univ.erase v).powersetCard (t - 1)).filter (fun E => insert v E ∉ F)
  let k := t - 1 - i
  let B := (Fintype.card V - 2 * t).choose k
  let D := insert v ((S ∪ T) ∪ U)
  let Y := Finset.univ \ D
  have hD : D.card ≤ 2 * t := by
    have h1 := Finset.card_insert_le v ((S ∪ T) ∪ U)
    have h2 := Finset.card_union_le (S ∪ T) U
    have h3 := Finset.card_union_le S T
    change (insert v ((S ∪ T) ∪ U)).card ≤ 2 * t
    omega
  have hY : Fintype.card V - 2 * t ≤ Y.card := by
    dsimp [Y]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    exact Nat.sub_le_sub_left hD _
  have hchoose : B ≤ (Y.powersetCard k).card := by
    rw [Finset.card_powersetCard]
    exact Nat.choose_le_choose k hY
  have hYdis : Disjoint Y ((S ∪ T) ∪ U) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hy)
  obtain ⟨hYST, hYU⟩ := Finset.disjoint_union_right.mp hYdis
  obtain ⟨hYS, hYT⟩ := Finset.disjoint_union_right.mp hYST
  have hvY : v ∉ Y := by
    intro hv
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_insert_self v _)
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hmissing := hchoose.trans (filler_count_le_missing hfree k hvS hvT hvU hTne hST hSU hTU
    hYS hYT hYU hA hC)
  have hmissT := Erdos643MissingLinkMap.missing_fillers_card_le (r := t) (k := k) F hYT hvY hvT hT (by dsimp [k]; omega)
  have hmissU := Erdos643MissingLinkMap.missing_fillers_card_le (r := t) (k := k) F hYU hvY hvU hU (by dsimp [k]; omega)
  have hsum := hmissing.trans (Nat.add_le_add hmissT hmissU)
  change B ≤ (M.filter (fun E => T ⊆ E)).card + (M.filter (fun E => U ⊆ E)).card at hsum
  change B ≤ 2 * (M.filter (fun E => T ⊆ E)).card ∨ B ≤ 2 * (M.filter (fun E => U ⊆ E)).card
  omega

end Erdos643CommonFiller

namespace Erdos643ExceptionalBounds

theorem incidence_to_exceptional_bound_sharp {n t i m q : ℕ} (ht : 4 ≤ t) (hn : 6 * t ≤ n)
    (hi : i ≤ t - 1)
    (hinc : q * (n - 2 * t).choose (t - 1 - i) ≤ 2 * m * (t - 1).choose i) :
    q * n ^ (t - 1 - i) ≤ t ^ (2 * t) * m := by
  let r := t - 1
  let k := r - i
  let b := (n - 2 * t).choose k
  change q * b ≤ 2 * m * r.choose i at hinc
  change q * n ^ k ≤ t ^ (2 * t) * m
  have hk : k ≤ r := Nat.sub_le _ _
  have hr : r ≤ t := Nat.sub_le _ _
  have hbase : n ≤ 2 * ((n - 2 * t) + 1 - k) := by omega
  have hfac : ((n - 2 * t) + 1 - k) ^ k ≤ k.factorial * b := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.pow_sub_le_descFactorial _ _
  have hpowers : n ^ k ≤ 2 ^ k * (k.factorial * b) := by
    calc
      n ^ k ≤ (2 * ((n - 2 * t) + 1 - k)) ^ k := Nat.pow_le_pow_left hbase k
      _ = 2 ^ k * ((n - 2 * t) + 1 - k) ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * (k.factorial * b) := Nat.mul_le_mul_left _ hfac
  have htpos : 0 < t := by omega
  have htwo : 2 * 2 ^ k ≤ t ^ t := by
    calc
      2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ']
      _ ≤ t ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ t ^ t := Nat.pow_le_pow_right htpos (by dsimp [r] at hk; omega)
  have hfact : k.factorial ≤ t ^ k :=
    (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left (hk.trans hr) _)
  have hchoose : r.choose i ≤ t ^ i :=
    (Nat.choose_le_pow r i).trans (Nat.pow_le_pow_left hr _)
  have hparts : k.factorial * r.choose i ≤ t ^ t := by
    have hsum : k + i = r := Nat.sub_add_cancel hi
    calc
      k.factorial * r.choose i ≤ t ^ k * t ^ i := Nat.mul_le_mul hfact hchoose
      _ = t ^ r := by rw [← pow_add, hsum]
      _ ≤ t ^ t := Nat.pow_le_pow_right htpos hr
  have hcoeff : (2 * 2 ^ k) * (k.factorial * r.choose i) ≤ t ^ (2 * t) := by
    calc
      _ ≤ t ^ t * t ^ t := Nat.mul_le_mul htwo hparts
      _ = _ := by rw [← pow_add, show t + t = 2 * t by omega]
  calc
    q * n ^ k ≤ q * (2 ^ k * (k.factorial * b)) := Nat.mul_le_mul_left q hpowers
    _ = (2 ^ k * k.factorial) * (q * b) := by ring
    _ ≤ (2 ^ k * k.factorial) * (2 * m * r.choose i) := Nat.mul_le_mul_left _ hinc
    _ = ((2 * 2 ^ k) * (k.factorial * r.choose i)) * m := by ring
    _ ≤ t ^ (2 * t) * m := Nat.mul_le_mul_right m hcoeff

theorem incidence_to_exceptional_bound {n t i m q : ℕ} (ht : 4 ≤ t) (hn : 6 * t ≤ n)
    (hi : i ≤ t - 1)
    (hinc : q * (n - 2 * t).choose (t - 1 - i) ≤ 2 * m * (t - 1).choose i) :
    q * n ^ (t - 1 - i) ≤ (4 * t ^ (2 * t)) * m :=
  (incidence_to_exceptional_bound_sharp ht hn hi hinc).trans
    (Nat.mul_le_mul_right m (Nat.le_mul_of_pos_left _ (by decide)))

end Erdos643ExceptionalBounds

namespace Erdos643StarLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All links of the prescribed size away from the star center. -/
def starLinks (v : V) (r : ℕ) : Finset (Finset V) :=
  (Finset.univ.erase v).powersetCard r

/-- Links whose corresponding edge at the center is absent. -/
def missingLinks (F : Finset (Finset V)) (v : V) (t : ℕ) : Finset (Finset V) :=
  (starLinks v (t - 1)).filter fun E => insert v E ∉ F

/-- Remainders with at least half as many missing completions as the guaranteed filler count. -/
def exceptional (F : Finset (Finset V)) (v : V) (t i : ℕ) : Finset (Finset V) :=
  (starLinks v i).filter fun T =>
    (Fintype.card V - 2 * t).choose (t - 1 - i) ≤
      2 * ((missingLinks F v t).filter fun E => T ⊆ E).card

theorem missing_uniform (F : Finset (Finset V)) (v : V) (t : ℕ) :
    (missingLinks F v t).IsUniform (t - 1) := by
  intro E hE
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hE).1).2

theorem exceptional_uniform (F : Finset (Finset V)) (v : V) (t i : ℕ) :
    (exceptional F v t i).IsUniform i := by
  intro E hE
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hE).1).2

theorem missing_card {F : Finset (Finset V)} {t : ℕ} (v : V) (hF : F.IsUniform t) :
    (missingLinks F v t).card =
      (Fintype.card V - 1).choose (t - 1) - (F.filter (fun E => v ∈ E)).card := by
  let L := starLinks v (t - 1)
  have hlcard : L.card = (Fintype.card V - 1).choose (t - 1) := by
    simp [L, starLinks, Finset.card_erase_of_mem (Finset.mem_univ v)]
  have hpresent : (L.filter (fun E => insert v E ∈ F)).card =
      (F.filter (fun E => v ∈ E)).card := by
    apply Finset.card_nbij' (insert v) (fun E => E.erase v)
    · intro E hE
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hE).2, Finset.mem_insert_self _ _⟩
    · intro E hE
      obtain ⟨hEF, hv⟩ := Finset.mem_filter.mp hE
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, by simpa [Finset.insert_erase hv] using hEF⟩
      · intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
      · rw [Finset.card_erase_of_mem hv, hF E hEF]
    · intro E hE
      have hs := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hE).1).1
      apply Finset.erase_insert
      intro hv
      exact (Finset.mem_erase.mp (hs hv)).1 rfl
    · intro E hE
      exact Finset.insert_erase (Finset.mem_filter.mp hE).2
  have hsplit := Finset.card_filter_add_card_filter_not (s := L) (fun E => insert v E ∈ F)
  rw [hpresent, hlcard] at hsplit
  change (L.filter (fun E => insert v E ∉ F)).card = _
  omega

theorem exceptional_full_eq_missing (F : Finset (Finset V)) (v : V) (t : ℕ) :
    exceptional F v t (t - 1) = missingLinks F v t := by
  ext T
  constructor
  · intro hT
    obtain ⟨hbase,hcount⟩ := Finset.mem_filter.mp hT
    have hpos : 0 < ((missingLinks F v t).filter (fun E => T ⊆ E)).card := by
      have hconst : (Fintype.card V - 2 * t).choose (t - 1 - (t - 1)) = 1 := by simp
      rw [hconst] at hcount
      omega
    obtain ⟨E,hE⟩ := Finset.card_pos.mp hpos
    obtain ⟨hEM,hTE⟩ := Finset.mem_filter.mp hE
    have heq : T = E := Finset.eq_of_subset_of_card_le hTE (by
      rw [missing_uniform F v t E hEM, (Finset.mem_powersetCard.mp hbase).2])
    exact heq ▸ hEM
  · intro hT
    have htL := (Finset.mem_filter.mp hT).1
    have hpos : 0 < ((missingLinks F v t).filter (fun E => T ⊆ E)).card :=
      Finset.card_pos.mpr ⟨T,Finset.mem_filter.mpr ⟨hT,Finset.Subset.refl _⟩⟩
    refine Finset.mem_filter.mpr ⟨htL, ?_⟩
    simp only [Nat.sub_self, Nat.choose_zero_right]
    omega

end Erdos643StarLinks

namespace Erdos643DeficitStructure

open Finset Erdos643StarLinks Erdos643CommonFiller

variable {V : Type*} [Fintype V] [DecidableEq V]

def exceptionalVertices (F : Finset (Finset V)) (v : V) (t : ℕ) : Finset V :=
  (Finset.univ.erase v).filter (fun u => {u} ∈ exceptional F v t 1)

theorem exceptional_vertices_card (F : Finset (Finset V)) (v : V) (t : ℕ) :
    (exceptionalVertices F v t).card = (exceptional F v t 1).card := by
  apply Finset.card_nbij (fun u : V => ({u} : Finset V))
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u _ w _ heq
    change ({u} : Finset V) = {w} at heq
    have hu : u ∈ ({w} : Finset V) := heq ▸ Finset.mem_singleton_self u
    exact Finset.mem_singleton.mp hu
  · intro T hT
    obtain ⟨u,rfl⟩ := Finset.card_eq_one.mp (exceptional_uniform F v t 1 T hT)
    have hsubset := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1
    exact ⟨u, Finset.mem_filter.mpr ⟨hsubset (Finset.mem_singleton_self u), hT⟩, rfl⟩

theorem neighbor_count_outside_exceptional_le_one
    {F : Finset (Finset V)} {v : V} {t : ℕ} (ht : 2 ≤ t)
    (hfree : ¬ F.HasRepeatedDisjointUnion) {S : Finset V} (hS : S.card = t - 1) :
    let H := F.filter (fun E => v ∉ E)
    let U := exceptionalVertices F v t
    ((Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ H)) \ U).card ≤ 1 := by
  let H := F.filter (fun E => v ∉ E)
  let U := exceptionalVertices F v t
  change ((Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ H)) \ U).card ≤ 1
  apply Finset.card_le_one_iff.mpr
  intro x y hx hy
  by_contra hxy
  obtain ⟨hx,hxU⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hy,hyU⟩ := Finset.mem_sdiff.mp hy
  obtain ⟨hxS,hxH⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hyS,hyH⟩ := (Finset.mem_filter.mp hy).2
  obtain ⟨hxF,hvxS⟩ := Finset.mem_filter.mp hxH
  obtain ⟨hyF,hvyS⟩ := Finset.mem_filter.mp hyH
  have hvS : v ∉ S := fun h => hvxS (Finset.mem_insert_of_mem h)
  have hxv : x ≠ v := fun h => hvxS (h ▸ Finset.mem_insert_self _ _)
  have hyv : y ≠ v := fun h => hvyS (h ▸ Finset.mem_insert_self _ _)
  have hxF' : S ∪ ({x} : Finset V) ∈ F := by simpa [Finset.union_comm] using hxF
  have hyF' : S ∪ ({y} : Finset V) ∈ F := by simpa [Finset.union_comm] using hyF
  have hQ := disjoint_remainders_force_exceptional (T := ({x} : Finset V))
    (U := ({y} : Finset V)) (i := 1) (by omega) (by omega) hS (by simp) (by simp)
    hvS (by simp [Ne.symm hxv]) (by simp [Ne.symm hyv])
    (Finset.disjoint_singleton_right.mpr hxS) (Finset.disjoint_singleton_right.mpr hyS)
    (Finset.disjoint_singleton.mpr hxy) hfree hxF' hyF'
  have exceptional_of_count {u : V} (hu : u ≠ v)
      (hcount : (Fintype.card V - 2 * t).choose (t - 1 - 1) ≤
        2 * ((missingLinks F v t).filter (fun E => ({u} : Finset V) ⊆ E)).card) :
      u ∈ U := by
    have hu' : u ∈ (Finset.univ : Finset V).erase v :=
      Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩
    refine Finset.mem_filter.mpr ⟨hu', Finset.mem_filter.mpr ⟨?_, hcount⟩⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.singleton_subset_iff.mpr hu', by simp⟩
  exact hQ.elim (fun h => hxU (exceptional_of_count hxv h)) (fun h => hyU (exceptional_of_count hyv h))

end Erdos643DeficitStructure



/- Passing from the numerical star deficit in Huang–Ma–Yang to the finite bound. -/

open Filter
open scoped Topology

namespace Erdos643DeficitBridge

theorem small_deficit_of_log_bound (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ (n : ℝ) * Real.log n →
      4 * c ^ 2 * m ≤ n ^ 2 := by
  have hlim : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [mul_one, one_mul, add_zero, pow_one] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hnat := hlim.comp tendsto_natCast_atTop_atTop
  have hscaled : Tendsto
      (fun n : ℕ => (4 * (c : ℝ) ^ 2) * (Real.log n / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using hnat.const_mul (4 * (c : ℝ) ^ 2)
  have hlt : ∀ᶠ n : ℕ in atTop,
      (4 * (c : ℝ) ^ 2) * (Real.log n / (n : ℝ)) < 1 :=
    hscaled.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with n hn hnp m hm
  have hpos : (0 : ℝ) < n := by exact_mod_cast hnp
  have hnr : (4 * (c : ℝ) ^ 2) * Real.log n ≤ n := by
    rw [← mul_div_assoc] at hn
    simpa only [one_mul] using (div_lt_iff₀ hpos).mp hn |>.le
  have hreal : 4 * (c : ℝ) ^ 2 * (m : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc
      _ ≤ (4 * (c : ℝ) ^ 2) * ((n : ℝ) * Real.log n) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = (n : ℝ) * ((4 * (c : ℝ) ^ 2) * Real.log n) := by ring
      _ ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left hnr hpos.le
      _ = _ := by ring
  exact_mod_cast hreal

end Erdos643DeficitBridge


namespace Erdos643SmallDensity

theorem small_density_bounds {r : ℕ} (hr : 4 ≤ r) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {n q m : ℝ}, 0 < n → 0 ≤ q → 0 ≤ m →
        q * n ^ (r - 2) ≤ C * m → m ≤ δ * n ^ (r - 1) →
        q ≤ n / (50 * (r : ℝ) ^ (4 * r + 3)) ∧ q ^ (r - 1) ≤ m / B := by
  let k := r - 2
  let A : ℝ := 50 * (r : ℝ) ^ (4 * r + 3)
  let δ : ℝ := min 1 (min (1 / (A * C)) (1 / (B * C ^ (k + 1))))
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAC : 0 < A * C := mul_pos hA hC
  have hBC : 0 < B * C ^ (k + 1) := mul_pos hB (pow_pos hC _)
  have hδ : 0 < δ := by
    exact lt_min (by norm_num) (lt_min (one_div_pos.mpr hAC) (one_div_pos.mpr hBC))
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδA : δ ≤ 1 / (A * C) := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ 1 / (B * C ^ (k + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro n q m hn hq hm hqm hmd
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hkr : k + 1 = r - 1 := by dsimp [k]; omega
  have hqlinear : q ≤ C * δ * n := by
    apply (mul_le_mul_iff_left₀ (pow_pos hn k)).mp
    calc
      q * n ^ k ≤ C * m := hqm
      _ ≤ C * (δ * n ^ (r - 1)) := mul_le_mul_of_nonneg_left hmd hC.le
      _ = (C * δ * n) * n ^ k := by rw [← hkr, pow_succ]; ring
  have hqpower : q ^ (k + 1) ≤ ((C * δ) ^ k * C) * m := by
    calc
      q ^ (k + 1) = q * q ^ k := pow_succ' _ _
      _ ≤ q * (C * δ * n) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqlinear k) hq
      _ = (C * δ) ^ k * (q * n ^ k) := by rw [mul_pow]; ring
      _ ≤ (C * δ) ^ k * (C * m) :=
        mul_le_mul_of_nonneg_left hqm (pow_nonneg (mul_nonneg hC.le hδ.le) _)
      _ = ((C * δ) ^ k * C) * m := by ring
  have hcoefficient : ((C * δ) ^ k * C) * B ≤ 1 := by
    calc
      ((C * δ) ^ k * C) * B = δ ^ k * (B * C ^ (k + 1)) := by
        rw [mul_pow, pow_succ]
        ring
      _ ≤ δ * (B * C ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right (pow_le_of_le_one hδ.le hδone hk) hBC.le
      _ ≤ 1 := (le_div_iff₀ hBC).mp hδB
  change q ≤ n / A ∧ q ^ (r - 1) ≤ m / B
  constructor
  · apply (le_div_iff₀ hA).mpr
    have hcoefficient' := (le_div_iff₀ hAC).mp hδA
    calc
      q * A ≤ (C * δ * n) * A := mul_le_mul_of_nonneg_right hqlinear hA.le
      _ = (δ * (A * C)) * n := by ring
      _ ≤ 1 * n := mul_le_mul_of_nonneg_right hcoefficient' hn.le
      _ = n := one_mul _
  · rw [← hkr]
    apply (le_div_iff₀ hB).mpr
    calc
      q ^ (k + 1) * B ≤ (((C * δ) ^ k * C) * m) * B :=
        mul_le_mul_of_nonneg_right hqpower hB.le
      _ = (((C * δ) ^ k * C) * B) * m := by ring
      _ ≤ 1 * m := mul_le_mul_of_nonneg_right hcoefficient hm
      _ = m := one_mul _

end Erdos643SmallDensity



namespace Erdos643DeficitApplication

open Filter
open Erdos643StarLinks Erdos643DeficitStructure
open Erdos643CommonFiller Erdos643ExceptionalBounds

/-- The specialization of Lemma 3.3 needed for the exact bound. -/
def StarDeficitEstimate (K : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ᶠ n : ℕ in atTop,
    ∀ F : Finset (Finset (Fin n)), F.IsUniform t → ¬ F.HasRepeatedDisjointUnion →
      ∀ (v : Fin n) (U : Finset (Fin n)), U ⊆ Finset.univ.erase v →
        let H := F.filter (fun E => v ∉ E)
        let m := (n - 1).choose (t - 1) - (F.filter (fun E => v ∈ E)).card
        m ≤ H.card →
        (U.card : ℝ) ≤ (n : ℝ) / (50 * (t : ℝ) ^ (4 * t + 3)) →
        (U.card : ℝ) ^ (t - 1) ≤ (m : ℝ) / ((3 * t * (1 + 2 * K t) : ℕ) : ℝ) →
        (∀ S : Finset (Fin n), S.card = t - 1 →
          ((Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ H)) \ U).card ≤ 1) →
        (m : ℝ) ≤ (n : ℝ) * Real.log n

theorem H2_of_starDeficitEstimate {K : ℕ → ℕ} (hEstimate : StarDeficitEstimate K) :
    OMA.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1.H2 := by
  intro t ht
  let c := 4 * t ^ (2 * t)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcReal : 0 < (c : ℝ) := by exact_mod_cast hc
  have hbReal : (0 : ℝ) < ((3 * t * (1 + 2 * K t) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 3 * t * (1 + 2 * K t) by positivity)
  obtain ⟨δ, hδ, hdensity⟩ := Erdos643SmallDensity.small_density_bounds ht hcReal hbReal
  refine ⟨δ,hδ,?_⟩
  filter_upwards [eventually_ge_atTop (6 * t), hEstimate t ht,
    Erdos643DeficitBridge.small_deficit_of_log_bound c] with n hn hEstimate hEnd
  intro F hF hfree hLarge v
  dsimp only
  intro hNear
  let S := (n - 1).choose (t - 1)
  let H := F.filter (fun E => v ∉ E)
  let M := missingLinks F v t
  let U := exceptionalVertices F v t
  let m := S - (F.filter (fun E => v ∈ E)).card
  change (m : ℝ) ≤ δ * (S : ℝ) at hNear
  change 4 * c ^ 2 * m ≤ n ^ 2
  have hMS : M.card = m := by simpa [M,m,S] using missing_card v hF
  have hsplit : (F.filter (fun E => v ∈ E)).card + H.card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) (fun E => v ∈ E)
  have hlarge : S + (n - 1) / t ≤ F.card := hLarge
  have hmH : m ≤ H.card := by
    dsimp only [m]
    rw [Nat.sub_le_iff_le_add, Nat.add_comm, hsplit]
    exact (Nat.le_add_right _ _).trans hlarge
  have hSle : S ≤ n ^ (t - 1) :=
    (Nat.choose_le_pow (n - 1) (t - 1)).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  have hSreal : (S : ℝ) ≤ (n : ℝ) ^ (t - 1) := by exact_mod_cast hSle
  have hNear' : (m : ℝ) ≤ δ * (n : ℝ) ^ (t - 1) :=
    hNear.trans (mul_le_mul_of_nonneg_left hSreal hδ.le)
  have hinc : (exceptional F v t 1).card * (n - 2 * t).choose (t - 1 - 1) ≤
      2 * M.card * (t - 1).choose 1 := by
    apply exceptional_card_bound (missing_uniform F v t) (exceptional_uniform F v t 1)
    intro T hT
    simpa only [Fintype.card_fin] using (Finset.mem_filter.mp hT).2
  rw [hMS] at hinc
  have hq := incidence_to_exceptional_bound ht hn (show 1 ≤ t - 1 by omega) hinc
  rw [← exceptional_vertices_card F v t, show t - 1 - 1 = t - 2 by omega] at hq
  have hUbound : U.card * n ^ (t - 2) ≤ c * m := hq
  have hUboundReal : (U.card : ℝ) * (n : ℝ) ^ (t - 2) ≤ (c : ℝ) * (m : ℝ) := by
    exact_mod_cast hUbound
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hUSize,hUPower⟩ := hdensity hnpos (by positivity) (by positivity) hUboundReal hNear'
  have hUsubset : U ⊆ Finset.univ.erase v := Finset.filter_subset _ _
  have hLog : (m : ℝ) ≤ (n : ℝ) * Real.log n :=
    hEstimate F hF hfree v U hUsubset hmH hUSize hUPower
      (fun S hS => neighbor_count_outside_exceptional_le_one (by omega) hfree hS)
  exact hEnd m hLog

end Erdos643DeficitApplication



namespace Erdos643DeficitLinkDegree

open Finset Erdos643StarLinks Erdos643CommonFiller

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Remainders of size `i` that complete the fixed vertices to an off-star edge. -/
def offLinks (F : Finset (Finset V)) (v : V) (S : Finset V) (i : ℕ) :
    Finset (Finset V) :=
  (starLinks v i).filter fun T => Disjoint S T ∧ S ∪ T ∈ F ∧ v ∉ S ∪ T

/-- The largest number of ways to extend a set of size `t - i`. -/
def peak (F : Finset (Finset V)) (v : V) (t i : ℕ) : ℕ :=
  (starLinks v (t - i)).sup fun S => (offLinks F v S i).card

theorem mem_offLinks_iff {F : Finset (Finset V)} {v : V} {S T : Finset V} {i : ℕ} :
    T ∈ offLinks F v S i ↔
      T.card = i ∧ Disjoint S T ∧ S ∪ T ∈ F ∧ v ∉ S ∪ T := by
  simp only [offLinks, starLinks, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, h⟩
    exact ⟨hcard, h⟩
  · rintro ⟨hcard, hd, he, hv⟩
    have hsub : T ⊆ Finset.univ.erase v := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact hv (Finset.mem_union_right _ hx)
    exact ⟨⟨hsub, hcard⟩, hd, he, hv⟩

theorem card_offLinks_le_peak {F : Finset (Finset V)} {v : V} {S : Finset V} {t i : ℕ}
    (hS : S.card = t - i) (hv : v ∉ S) :
    (offLinks F v S i).card ≤ peak F v t i := by
  unfold peak
  apply Finset.le_sup (f := fun T => (offLinks F v T i).card)
  exact Finset.mem_powersetCard.mpr ⟨fun x hx => Finset.mem_erase.mpr
    ⟨fun heq => hv (heq ▸ hx), Finset.mem_univ _⟩, hS⟩

theorem good_remainders_intersect {F : Finset (Finset V)} {v : V} {S T W : Finset V}
    {t i : ℕ} (hi : 1 ≤ i) (hit : i ≤ t - 1) (hS : S.card = t - i)
    (hfree : ¬ F.HasRepeatedDisjointUnion)
    (hT : T ∈ offLinks F v S i \ exceptional F v t i)
    (hW : W ∈ offLinks F v S i \ exceptional F v t i) :
    ¬ Disjoint T W := by
  intro hTW
  obtain ⟨hTmem, hTgood⟩ := Finset.mem_sdiff.mp hT
  obtain ⟨hWmem, hWgood⟩ := Finset.mem_sdiff.mp hW
  obtain ⟨hTc, hST, hTE, hvST⟩ := mem_offLinks_iff.mp hTmem
  obtain ⟨hWc, hSW, hWE, hvSW⟩ := mem_offLinks_iff.mp hWmem
  have hvS : v ∉ S := fun hv => hvST (Finset.mem_union_left _ hv)
  have hvT : v ∉ T := fun hv => hvST (Finset.mem_union_right _ hv)
  have hvW : v ∉ W := fun hv => hvSW (Finset.mem_union_right _ hv)
  rcases disjoint_remainders_force_exceptional hi hit hS hTc hWc hvS hvT hvW
    hST hSW hTW hfree hTE hWE with hbad | hbad
  · exact hTgood (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hTmem).1, hbad⟩)
  · exact hWgood (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hWmem).1, hbad⟩)

/-- Fixing one vertex of a remainder injects into a link of one lower order. -/
theorem card_remainders_containing_le_peak {F : Finset (Finset V)} {v x : V}
    {S : Finset V} {t i : ℕ}
    (hi : 1 ≤ i) (hit : i ≤ t) (hS : S.card = t - i) :
    ((offLinks F v S i).filter (fun T => x ∈ T)).card ≤ peak F v t (i - 1) := by
  let K := (offLinks F v S i).filter (fun T => x ∈ T)
  change K.card ≤ _
  by_cases hk : K.Nonempty
  · obtain ⟨T₀, hT₀⟩ := hk
    obtain ⟨hT₀m, hx₀⟩ := Finset.mem_filter.mp hT₀
    obtain ⟨_, hd₀, _, hv₀⟩ := mem_offLinks_iff.mp hT₀m
    have hxS : x ∉ S := fun h => Finset.disjoint_left.mp hd₀ h hx₀
    have hv : v ∉ insert x S := by
      intro hv
      refine hv₀ ?_
      rcases Finset.mem_insert.mp hv with heq | hvs
      · exact Finset.mem_union_right _ (heq.symm ▸ hx₀)
      · exact Finset.mem_union_left _ hvs
    have hcard : (insert x S).card = t - (i - 1) := by
      rw [Finset.card_insert_of_notMem hxS, hS]
      omega
    refine (Finset.card_le_card_of_injOn (fun T => T.erase x) ?_ ?_).trans
      (card_offLinks_le_peak (F := F) (v := v) hcard hv)
    · intro T hTk
      obtain ⟨hT, hx⟩ := Finset.mem_filter.mp hTk
      obtain ⟨hc, hd, he, hvE⟩ := mem_offLinks_iff.mp hT
      have hE : insert x S ∪ T.erase x = S ∪ T := by
        rw [Finset.insert_union, ← Finset.union_insert, Finset.insert_erase hx]
      exact mem_offLinks_iff.mpr ⟨by rw [Finset.card_erase_of_mem hx, hc],
        Finset.disjoint_insert_left.mpr ⟨Finset.notMem_erase x T,
          Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd⟩,
        hE.symm ▸ he, hE.symm ▸ hvE⟩
    · intro T hT W hW heq
      have hxT := (Finset.mem_filter.mp hT).2
      have hxW := (Finset.mem_filter.mp hW).2
      change T.erase x = W.erase x at heq
      rw [← Finset.insert_erase hxT, ← Finset.insert_erase hxW, heq]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hk]

/-- A nonexceptional link can be covered by the vertices in any of its remainders. -/
theorem card_good_remainders_le {F : Finset (Finset V)} {v : V} {S : Finset V}
    {t i : ℕ} (hi : 1 ≤ i) (hit : i ≤ t - 1) (hS : S.card = t - i)
    (hfree : ¬ F.HasRepeatedDisjointUnion) :
    (offLinks F v S i \ exceptional F v t i).card ≤ i * peak F v t (i - 1) := by
  let K := offLinks F v S i
  let G := K \ exceptional F v t i
  change G.card ≤ _
  by_cases hg : G.Nonempty
  · obtain ⟨T₀, hT₀⟩ := hg
    let M (x : V) := K.filter (fun T => x ∈ T)
    have hs : G ⊆ T₀.biUnion M := by
      intro T hT
      obtain ⟨x, hx₀, hx⟩ := Finset.not_disjoint_iff.mp
        (good_remainders_intersect hi hit hS hfree hT₀ hT)
      exact Finset.mem_biUnion.mpr ⟨x, hx₀,
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hT).1, hx⟩⟩
    have hTc := (mem_offLinks_iff.mp (Finset.mem_sdiff.mp hT₀).1).1
    calc
      G.card ≤ (T₀.biUnion M).card := Finset.card_le_card hs
      _ ≤ ∑ x ∈ T₀, (M x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ T₀, peak F v t (i - 1) :=
        Finset.sum_le_sum (fun _ _ => card_remainders_containing_le_peak hi (by omega) hS)
      _ = _ := by rw [Finset.sum_const_nat (fun _ _ => rfl), hTc]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hg]

theorem peak_zero_le_one (F : Finset (Finset V)) (v : V) (t : ℕ) :
    peak F v t 0 ≤ 1 := by
  apply Finset.sup_le
  intro S _
  have hsub : offLinks F v S 0 ⊆ {∅} := by
    intro T hT
    simpa using Finset.card_eq_zero.mp (mem_offLinks_iff.mp hT).1
  simpa using Finset.card_le_card hsub

theorem peak_succ_bound {F : Finset (Finset V)} {v : V} {t i : ℕ}
    (hi : 1 ≤ i) (hit : i ≤ t - 1) (hfree : ¬ F.HasRepeatedDisjointUnion) :
    peak F v t i ≤ (exceptional F v t i).card + i * peak F v t (i - 1) := by
  apply Finset.sup_le
  intro S hS
  have hgood := card_good_remainders_le (v := v) hi hit (Finset.mem_powersetCard.mp hS).2 hfree
  have hcard := Finset.card_le_card_sdiff_add_card (s := offLinks F v S i)
    (t := exceptional F v t i)
  omega

end Erdos643DeficitLinkDegree


namespace Erdos643DeficitLinkDegree

open Finset Erdos643StarLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree recurrence with the baseline power removed before scaling. -/
theorem peak_bound_scaled {F : Finset (Finset V)} {v : V} {t n c m : ℕ}
    (htn : t ≤ n) (hfree : ¬ F.HasRepeatedDisjointUnion)
    (hQ : ∀ j, 1 ≤ j → j ≤ t - 1 →
      (exceptional F v t j).card * n ^ (t - 1 - j) ≤ c * m)
    {i : ℕ} (hi : i ≤ t - 1) :
    peak F v t i * n ^ (t - 1 - i) ≤ i * c * m + t ^ i * n ^ (t - 1 - i) := by
  let A (j : ℕ) := peak F v t j - t ^ j
  have hrestore (j : ℕ) : peak F v t j ≤ A j + t ^ j := by
    dsimp [A]
    omega
  have hscaled (j : ℕ) (hj : j ≤ t - 1) : A j * n ^ (t - 1 - j) ≤ j * c * m := by
    induction j with
    | zero =>
      have hzero := peak_zero_le_one F v t
      have hz : A 0 = 0 := by
        simp [A, Nat.sub_eq_zero_of_le hzero]
      simp [hz]
    | succ j ih =>
      have hj' : j ≤ t - 1 := by omega
      have hprev := ih hj'
      have hsucc := peak_succ_bound (v := v) (show 1 ≤ j + 1 by omega) hj hfree
      simp only [Nat.add_sub_cancel] at hsucc
      have htj : j + 1 ≤ t := by omega
      have hc : (j + 1) * t ^ j ≤ t ^ (j + 1) := by
        rw [pow_succ']
        exact Nat.mul_le_mul_right _ htj
      have hAj : A (j + 1) ≤ (exceptional F v t (j + 1)).card + (j + 1) * A j := by
        dsimp only [A]
        apply Nat.sub_le_iff_le_add.mpr
        have hprevBound := Nat.mul_le_mul_left (j + 1) (hrestore j)
        rw [Nat.mul_add] at hprevBound
        dsimp only [A] at hprevBound
        omega
      let k := t - 1 - (j + 1)
      have hk : t - 1 - j = k + 1 := by dsimp [k]; omega
      rw [hk, pow_succ'] at hprev
      change A (j + 1) * n ^ k ≤ (j + 1) * c * m
      calc
        _ ≤ ((exceptional F v t (j + 1)).card + (j + 1) * A j) * n ^ k :=
          Nat.mul_le_mul_right _ hAj
        _ = (exceptional F v t (j + 1)).card * n ^ k + (j + 1) * (A j * n ^ k) := by ring
        _ ≤ c * m + n * (A j * n ^ k) :=
          Nat.add_le_add (hQ (j + 1) (by omega) hj)
            (Nat.mul_le_mul_right _ (htj.trans htn))
        _ = c * m + A j * (n * n ^ k) := by ring
        _ ≤ c * m + j * c * m := Nat.add_le_add_left hprev _
        _ = _ := by ring
  calc
    _ ≤ (A i + t ^ i) * n ^ (t - 1 - i) := Nat.mul_le_mul_right _ (hrestore i)
    _ = A i * n ^ (t - 1 - i) + t ^ i * n ^ (t - 1 - i) := by ring
    _ ≤ _ := Nat.add_le_add_right (hscaled i hi) _

end Erdos643DeficitLinkDegree


namespace Erdos643Rectangle

theorem not_all_four_of_disjoint {V : Type*} [DecidableEq V] {F : Finset (Finset V)}
    (hfree : ¬ F.HasRepeatedDisjointUnion) {S₁ S₂ T U : Finset V}
    (hS : Disjoint S₁ S₂) (hR : Disjoint T U) (hSneq : S₁ ≠ S₂) (hRneq : T ≠ U)
    (hS₁ : Disjoint S₁ (T ∪ U)) (hS₂ : Disjoint S₂ (T ∪ U))
    (hA : S₁ ∪ T ∈ F) (hB : S₂ ∪ U ∈ F) (hC : S₁ ∪ U ∈ F) :
    S₂ ∪ T ∉ F := by
  intro hD
  have hRightT : T ⊆ T ∪ U := Finset.subset_union_left
  have hRightU : U ⊆ T ∪ U := Finset.subset_union_right
  have proj₁ {S R : Finset V} (hSd : Disjoint S (T ∪ U)) (hRsub : R ⊆ T ∪ U) :
      (S ∪ R) \ (T ∪ U) = S := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx, hn⟩
      exact hx.elim id (fun hr => (hn (Finset.mem_union.mp (hRsub hr))).elim)
    · intro hx
      exact ⟨Or.inl hx, fun hr => Finset.disjoint_left.mp hSd hx (Finset.mem_union.mpr hr)⟩
  have proj₂ {S R : Finset V} (hSd : Disjoint S (T ∪ U)) (hRsub : R ⊆ T ∪ U) :
      (S ∪ R) ∩ (T ∪ U) = R := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx, hr⟩
      exact hx.elim (fun hs => (Finset.disjoint_left.mp hSd hs (Finset.mem_union.mpr hr)).elim) id
    · intro hx
      exact ⟨Or.inr hx, Finset.mem_union.mp (hRsub hx)⟩
  have left_ne {S₁' S₂' R₁ R₂ : Finset V}
      (h₁ : Disjoint S₁' (T ∪ U)) (h₂ : Disjoint S₂' (T ∪ U))
      (hR₁ : R₁ ⊆ T ∪ U) (hR₂ : R₂ ⊆ T ∪ U) (hne : S₁' ≠ S₂') :
      S₁' ∪ R₁ ≠ S₂' ∪ R₂ := by
    intro heq
    exact hne ((proj₁ h₁ hR₁).symm.trans ((congrArg (fun E => E \ (T ∪ U)) heq).trans (proj₁ h₂ hR₂)))
  have right_ne {S₁' S₂' R₁ R₂ : Finset V}
      (h₁ : Disjoint S₁' (T ∪ U)) (h₂ : Disjoint S₂' (T ∪ U))
      (hR₁ : R₁ ⊆ T ∪ U) (hR₂ : R₂ ⊆ T ∪ U) (hne : R₁ ≠ R₂) :
      S₁' ∪ R₁ ≠ S₂' ∪ R₂ := by
    intro heq
    exact hne ((proj₂ h₁ hR₁).symm.trans ((congrArg (fun E => E ∩ (T ∪ U)) heq).trans (proj₂ h₂ hR₂)))
  obtain ⟨hS₁T,hS₁U⟩ := Finset.disjoint_union_right.mp hS₁
  obtain ⟨hS₂T,hS₂U⟩ := Finset.disjoint_union_right.mp hS₂
  have hAB : Disjoint (S₁ ∪ T) (S₂ ∪ U) := by
    simp [Finset.disjoint_union_left, Finset.disjoint_union_right, hS, hS₁U, hS₂T.symm, hR]
  have hCD : Disjoint (S₁ ∪ U) (S₂ ∪ T) := by
    simp [Finset.disjoint_union_left, Finset.disjoint_union_right, hS, hS₁T, hS₂U.symm, hR.symm]
  have hUnion : (S₁ ∪ T) ∪ (S₂ ∪ U) = (S₁ ∪ U) ∪ (S₂ ∪ T) := by
    ext x
    simp only [Finset.mem_union]
    tauto
  exact hfree ⟨_, hA, _, hB, _, hC, _, hD, hAB, hCD, hUnion,
    left_ne hS₁ hS₂ hRightT hRightU hSneq,
    left_ne hS₁ hS₂ hRightU hRightT hSneq,
    right_ne hS₁ hS₁ hRightT hRightU hRneq,
    left_ne hS₁ hS₂ hRightT hRightT hSneq,
    left_ne hS₂ hS₁ hRightU hRightU hSneq.symm,
    right_ne hS₂ hS₂ hRightU hRightT hRneq.symm⟩

end Erdos643Rectangle

namespace Erdos643

theorem card_le_three_or_common_vertex
    {α : Type*} [DecidableEq α] (H : Finset (Finset α))
    (hunif : ∀ E ∈ H, E.card = 2)
    (hinter : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).Nonempty) :
    H.card ≤ 3 ∨ ∃ x, ∀ E ∈ H, x ∈ E := by
  classical
  by_cases hsmall : H.card ≤ 3
  · exact Or.inl hsmall
  by_cases hcommon : ∃ x, ∀ E ∈ H, x ∈ E
  · exact Or.inr hcommon
  have hshared {E F : Finset α} (hE : E ∈ H) (hF : F ∈ H) (hne : E ≠ F) :
      ∃ x, x ∈ E ∧ x ∈ F := by
    obtain ⟨x, hx⟩ := hinter E hE F hF hne
    exact ⟨x, Finset.mem_inter.mp hx⟩
  have hpair {E : Finset α} (hE : E ∈ H) {x y : α} (hx : x ∈ E) (hy : y ∈ E)
      (hne : x ≠ y) : E = {x, y} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
    · rw [hunif E hE, Finset.card_pair hne]
  have horient {E : Finset α} (hE : E ∈ H) {x : α} (hx : x ∈ E) :
      ∃ a, a ≠ x ∧ E = {x, a} := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hunif E hE)
    rcases (show x = a ∨ x = b by simpa using hx) with rfl | rfl
    · exact ⟨b, hab.symm, rfl⟩
    · exact ⟨a, hab, Finset.pair_comm _ _⟩
  obtain ⟨E, hE, F, hF, hEF⟩ := Finset.one_lt_card.mp (show 1 < H.card by omega)
  obtain ⟨x, hxE, hxF⟩ := hshared hE hF hEF
  obtain ⟨a, hax, hEa⟩ := horient hE hxE
  obtain ⟨b, hbx, hFb⟩ := horient hF hxF
  have hab : a ≠ b := by
    intro heq
    apply hEF
    rw [hEa, hFb, heq]
  have havoids {K : Finset α} (hK : K ∈ H) (hxK : x ∉ K) : K = {a, b} := by
    have hKE : K ≠ E := fun heq => hxK (heq.symm ▸ hxE)
    have hKF : K ≠ F := fun heq => hxK (heq.symm ▸ hxF)
    obtain ⟨u, huK, huE⟩ := hshared hK hE hKE
    obtain ⟨v, hvK, hvF⟩ := hshared hK hF hKF
    have hua : u = a := (show u = x ∨ u = a by simpa [hEa] using huE).resolve_left
      (fun heq => hxK (heq ▸ huK))
    have hvb : v = b := (show v = x ∨ v = b by simpa [hFb] using hvF).resolve_left
      (fun heq => hxK (heq ▸ hvK))
    exact hpair hK (hua ▸ huK) (hvb ▸ hvK) hab
  have hmissing : ∃ G ∈ H, x ∉ G := by
    by_contra hm
    exact hcommon ⟨x, fun K hK => not_not.mp (fun hxK => hm ⟨K, hK, hxK⟩)⟩
  obtain ⟨G, hG, hxG⟩ := hmissing
  have hGab := havoids hG hxG
  have htriangle : H ⊆ ({{x, a}, {x, b}, {a, b}} : Finset (Finset α)) := by
    intro K hK
    by_cases hxK : x ∈ K
    · have hKG : K ≠ G := fun heq => hxG (heq ▸ hxK)
      obtain ⟨w, hwK, hwG⟩ := hshared hK hG hKG
      rcases (show w = a ∨ w = b by simpa [hGab] using hwG) with rfl | rfl
      · simp [hpair hK hxK hwK hax.symm]
      · simp [hpair hK hxK hwK hbx.symm]
    · simp [havoids hK hxK]
  exact Or.inl ((Finset.card_le_card htriangle).trans Finset.card_le_three)

end Erdos643

namespace Erdos643PathCountUpper

open Finset Erdos643StarLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem pair_form_of_mem {S : Finset V} {z : V} (hcard : S.card = 2)
    (hz : z ∈ S) : ∃ x : V, x ≠ z ∧ S = insert z {x} := by
  have hsingle : (S.erase z).card = 1 := by rw [Finset.card_erase_of_mem hz, hcard]
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hsingle
  have hxmem : x ∈ S.erase z := hx.symm ▸ Finset.mem_singleton_self x
  exact ⟨x, (Finset.mem_erase.mp hxmem).1,
    (Finset.insert_erase hz).symm.trans (congrArg (insert z) hx)⟩

/-- A pair of disjoint remainders has at most three common two-sets, or those
two-sets share a vertex and the outside-neighbor estimate bounds their number. -/
theorem common_two_sets_bound {F : Finset (Finset V)} {v : V} {t : ℕ}
    {T W U : Finset V} (ht : 4 ≤ t) (hT : T.card = t - 2) (hTW : Disjoint T W)
    (hfree : ¬ F.HasRepeatedDisjointUnion)
    (hOutside : ∀ S : Finset V, S.card = t - 1 →
      ((Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ F.filter (fun E => v ∉ E))) \ U).card ≤ 1) :
    let H := F.filter (fun E => v ∉ E)
    ((starLinks v 2).filter (fun S => Disjoint S (T ∪ W) ∧ S ∪ T ∈ H ∧ S ∪ W ∈ H)).card ≤
      U.card + 3 := by
  classical
  let H := F.filter (fun E => v ∉ E)
  let C := (starLinks v 2).filter (fun S => Disjoint S (T ∪ W) ∧ S ∪ T ∈ H ∧ S ∪ W ∈ H)
  have get {S : Finset V} (hS : S ∈ C) :
      S.card = 2 ∧ Disjoint S (T ∪ W) ∧ S ∪ T ∈ H ∧ S ∪ W ∈ H := by
    obtain ⟨hlink,hcond⟩ := Finset.mem_filter.mp hS
    exact ⟨(Finset.mem_powersetCard.mp hlink).2, hcond⟩
  have hTWne : T ≠ W := by
    intro heq
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
    exact Finset.disjoint_left.mp hTW hx (heq ▸ hx)
  have hinter (S₁ : Finset V) (h₁ : S₁ ∈ C) (S₂ : Finset V) (h₂ : S₂ ∈ C) (hne : S₁ ≠ S₂) :
      (S₁ ∩ S₂).Nonempty := by
    by_contra hno
    have hd := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hno)
    obtain ⟨_,hs₁,h₁T,h₁W⟩ := get h₁
    obtain ⟨_,hs₂,h₂T,h₂W⟩ := get h₂
    exact Erdos643Rectangle.not_all_four_of_disjoint hfree hd hTW hne hTWne hs₁ hs₂
      (Finset.mem_filter.mp h₁T).1 (Finset.mem_filter.mp h₂W).1
      (Finset.mem_filter.mp h₁W).1 (Finset.mem_filter.mp h₂T).1
  change C.card ≤ U.card + 3
  rcases Erdos643.card_le_three_or_common_vertex C (fun S hS => (get hS).1) hinter with hsmall | ⟨z,hz⟩
  · omega
  by_cases hC : C.Nonempty
  · obtain ⟨S₀,hS₀⟩ := hC
    have hzT : z ∉ T := fun h => Finset.disjoint_left.mp (get hS₀).2.1
      (hz S₀ hS₀) (Finset.mem_union_left W h)
    let S := insert z T
    have hS : S.card = t - 1 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem hzT, hT]
      omega
    let N := Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ H)
    have hnU : (N \ U).card ≤ 1 := hOutside S hS
    have hsub : N ⊆ U ∪ (N \ U) := by
      intro x hx
      by_cases h : x ∈ U
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, h⟩)
    have hN : N.card ≤ U.card + 1 :=
      ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _)).trans (Nat.add_le_add_left hnU _)
    have other (p : {P : Finset V // P ∈ C}) : ∃ x, x ≠ z ∧ p.val = insert z {x} :=
      pair_form_of_mem (get p.property).1 (hz p.val p.property)
    let f (p : {P : Finset V // P ∈ C}) := Classical.choose (other p)
    have hf (p : {P : Finset V // P ∈ C}) : f p ≠ z ∧ p.val = insert z {f p} :=
      Classical.choose_spec (other p)
    have hInjCount : C.attach.card ≤ N.card := by
      apply Finset.card_le_card_of_injOn f
      · intro p _
        have hxP : f p ∈ p.val := by rw [(hf p).2]; simp
        have hxT : f p ∉ T := fun hx =>
          Finset.disjoint_left.mp (get p.property).2.1 hxP (Finset.mem_union_left W hx)
        have hxS : f p ∉ S := by simp [S, (hf p).1, hxT]
        have hEdge : insert (f p) S = p.val ∪ T := by
          rw [(hf p).2]
          ext y
          simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
          tauto
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxS, hEdge ▸ (get p.property).2.2.1⟩
      · intro p _ q _ heq
        apply Subtype.ext
        exact (hf p).2.trans ((congrArg (fun x => insert z ({x} : Finset V)) heq).trans (hf q).2.symm)
    rw [Finset.card_attach] at hInjCount
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hC]

end Erdos643PathCountUpper

namespace Erdos643PathCountUpper

open Finset Erdos643StarLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered disjoint exceptional remainders, together with their common two-set. -/
def orderedPaths (F : Finset (Finset V)) (v : V) (t : ℕ) :
    Finset (Σ _ : Finset V × Finset V, Finset V) :=
  let Q := exceptional F v t (t - 2)
  let H := F.filter (fun E => v ∉ E)
  ((Q ×ˢ Q).filter (fun p => Disjoint p.1 p.2)).sigma fun p =>
    (starLinks v 2).filter fun S =>
      Disjoint S (p.1 ∪ p.2) ∧ S ∪ p.1 ∈ H ∧ S ∪ p.2 ∈ H

/-- Summing the common-neighborhood bound over all ordered pairs. -/
theorem ordered_paths_card_le {F : Finset (Finset V)} {v : V} {t : ℕ} {U : Finset V}
    (ht : 4 ≤ t) (hfree : ¬ F.HasRepeatedDisjointUnion)
    (hOutside : ∀ S : Finset V, S.card = t - 1 →
      ((Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ F.filter (fun E => v ∉ E))) \ U).card ≤ 1) :
    (orderedPaths F v t).card ≤ (exceptional F v t (t - 2)).card ^ 2 * (U.card + 3) := by
  classical
  unfold orderedPaths
  dsimp only
  rw [Finset.card_sigma]
  let Q := exceptional F v t (t - 2)
  let pairs := (Q ×ˢ Q).filter (fun p => Disjoint p.1 p.2)
  have hcount : pairs.card ≤ Q.card ^ 2 := by
    simpa [pairs, pow_two] using Finset.card_filter_le (s := Q ×ˢ Q) (fun p => Disjoint p.1 p.2)
  have hbound (p : Finset V × Finset V) (hp : p ∈ pairs) :
      ((starLinks v 2).filter (fun S =>
         Disjoint S (p.1 ∪ p.2) ∧ (S ∪ p.1) ∈ F.filter (fun E => v ∉ E) ∧
           (S ∪ p.2) ∈ F.filter (fun E => v ∉ E))).card ≤ U.card + 3 := by
    obtain ⟨hpQ, hdisj⟩ := Finset.mem_filter.mp hp
    exact common_two_sets_bound ht (exceptional_uniform F v t (t - 2) p.1
      (Finset.mem_product.mp hpQ).1) hdisj hfree hOutside
  calc
    _ ≤ ∑ _p ∈ pairs, (U.card + 3) := Finset.sum_le_sum hbound
    _ = pairs.card * (U.card + 3) := Finset.sum_const_nat (fun _ _ => rfl)
    _ ≤ _ := Nat.mul_le_mul_right _ hcount

end Erdos643PathCountUpper


/- Disjoint ordered pairs of exceptional remainders in a fixed link. -/

namespace Erdos643DeficitPairs

open Finset Erdos643StarLinks Erdos643DeficitLinkDegree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exceptional remainders in the off-star link of a fixed set. -/
def exceptionalLink (F : Finset (Finset V)) (v : V) (t : ℕ) (S : Finset V) (i : ℕ) :
    Finset (Finset V) :=
  (offLinks F v S i).filter fun T => T ∈ exceptional F v t i

/-- Ordered pairs of disjoint exceptional remainders in the link. -/
def pairedRemainders (F : Finset (Finset V)) (v : V) (t : ℕ) (S : Finset V) (i : ℕ) :
    Finset (Finset V × Finset V) :=
  let K := exceptionalLink F v t S i
  (K ×ˢ K).filter fun p => Disjoint p.1 p.2

/-- Count all ordered pairs, then charge every intersecting pair to a shared
vertex in its first remainder. -/
theorem paired_remainders_card_lower {F : Finset (Finset V)} {v : V} {t i : ℕ}
    {S : Finset V} (hi : 1 ≤ i) (hit : i ≤ t) (hS : S.card = t - i) :
    let K := exceptionalLink F v t S i
    (K.card : ℝ) ^ 2 - (t : ℝ) * (peak F v t (i - 1) : ℝ) * (K.card : ℝ) ≤
      ((pairedRemainders F v t S i).card : ℝ) := by
  let K := exceptionalLink F v t S i
  let Δ := peak F v t (i - 1)
  let overlaps (T : Finset V) := K.filter fun W => ¬ Disjoint T W
  have hK : K ⊆ offLinks F v S i := Finset.filter_subset _ _
  have hoverlaps (T : Finset V) (hT : T ∈ K) : (overlaps T).card ≤ i * Δ := by
    let C (x : V) := K.filter fun W => x ∈ W
    have hcover : overlaps T ⊆ T.biUnion C := by
      intro W hW
      obtain ⟨hWK, hNot⟩ := Finset.mem_filter.mp hW
      obtain ⟨x, hxT, hxW⟩ := Finset.not_disjoint_iff.mp hNot
      exact Finset.mem_biUnion.mpr ⟨x, hxT, Finset.mem_filter.mpr ⟨hWK, hxW⟩⟩
    have hC (x : V) : (C x).card ≤ Δ :=
      (Finset.card_le_card (Finset.filter_subset_filter (fun W => x ∈ W) hK)).trans
        (card_remainders_containing_le_peak hi hit hS)
    have hTc := (mem_offLinks_iff.mp (hK hT)).1
    calc
      (overlaps T).card ≤ (T.biUnion C).card := Finset.card_le_card hcover
      _ ≤ T.card * Δ := Finset.card_biUnion_le_card_mul T C Δ (fun x _ => hC x)
      _ = i * Δ := by rw [hTc]
  let bad := (K ×ˢ K).filter fun p => ¬ Disjoint p.1 p.2
  let B (T : Finset V) := (overlaps T).image fun W => (T, W)
  have hbadCover : bad ⊆ K.biUnion B := by
    rintro ⟨T, W⟩ h
    obtain ⟨hTW, hnd⟩ := Finset.mem_filter.mp h
    obtain ⟨hT, hW⟩ := Finset.mem_product.mp hTW
    exact Finset.mem_biUnion.mpr ⟨T, hT,
      Finset.mem_image.mpr ⟨W, Finset.mem_filter.mpr ⟨hW, hnd⟩, rfl⟩⟩
  have hbad : bad.card ≤ t * Δ * K.card := by
    calc
      bad.card ≤ (K.biUnion B).card := Finset.card_le_card hbadCover
      _ ≤ K.card * (i * Δ) := Finset.card_biUnion_le_card_mul K B (i * Δ)
        (fun T hT => Finset.card_image_le.trans (hoverlaps T hT))
      _ ≤ K.card * (t * Δ) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hit)
      _ = _ := Nat.mul_comm _ _
  have hsplit := Finset.card_filter_add_card_filter_not (s := K ×ˢ K)
    (fun p => Disjoint p.1 p.2)
  change (pairedRemainders F v t S i).card + bad.card = (K ×ˢ K).card at hsplit
  rw [Finset.card_product] at hsplit
  have hnat : K.card ^ 2 ≤ (pairedRemainders F v t S i).card + t * Δ * K.card := by
    rw [pow_two, ← hsplit]
    exact Nat.add_le_add_left hbad _
  apply (sub_le_iff_le_add).mpr
  exact_mod_cast hnat

end Erdos643DeficitPairs



namespace Erdos643DeficitLocalLower

open Finset Erdos643StarLinks Erdos643DeficitLinkDegree Erdos643PathCountUpper
open Erdos643DeficitPairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At a vertex, retain links whose matching star edge is present. -/
def goodLinks (F : Finset (Finset V)) (v : V) (t : ℕ) (u : V) :
    Finset (Finset V) :=
  offLinks F v {u} (t - 1) \ exceptional F v t (t - 1)

/-- A bucket of good links that all contain another given vertex. -/
def goodBucket (F : Finset (Finset V)) (v : V) (t : ℕ) (u x : V) :
    Finset (Finset V) :=
  (goodLinks F v t u).filter (fun T => x ∈ T)

theorem bucket_cover {F : Finset (Finset V)} {v u : V} {t : ℕ} {T₀ : Finset V}
    (ht : 4 ≤ t) (hfree : ¬ F.HasRepeatedDisjointUnion) (hT₀ : T₀ ∈ goodLinks F v t u) :
    (goodLinks F v t u).card ≤ ∑ x ∈ T₀, (goodBucket F v t u x).card := by
  have hsub : goodLinks F v t u ⊆ T₀.biUnion (goodBucket F v t u) := by
    intro T hT
    have hinter := good_remainders_intersect (show 1 ≤ t - 1 by omega) (le_refl (t - 1))
      (show ({u} : Finset V).card = t - (t - 1) by simp; omega) hfree hT₀ hT
    obtain ⟨x, hx₀, hx⟩ := Finset.not_disjoint_iff.mp hinter
    exact Finset.mem_biUnion.mpr ⟨x, hx₀, Finset.mem_filter.mpr ⟨hT, hx⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

theorem good_bucket_le_link {F : Finset (Finset V)} {v u x : V} {t : ℕ} (ht : 4 ≤ t) :
    (goodBucket F v t u x).card ≤ (offLinks F v (insert x {u}) (t - 2)).card := by
  apply Finset.card_le_card_of_injOn (fun T => T.erase x)
  · intro T hT
    obtain ⟨hG, hx⟩ := Finset.mem_filter.mp hT
    obtain ⟨hc, hd, he, hv⟩ := mem_offLinks_iff.mp (Finset.mem_sdiff.mp hG).1
    have hE : insert x ({u} : Finset V) ∪ T.erase x = {u} ∪ T := by
      rw [Finset.insert_union, ← Finset.union_insert, Finset.insert_erase hx]
    refine mem_offLinks_iff.mpr ⟨?_, ?_, hE.symm ▸ he, hE.symm ▸ hv⟩
    · rw [Finset.card_erase_of_mem hx, hc]
      omega
    · exact Finset.disjoint_insert_left.mpr ⟨Finset.notMem_erase x T,
        Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd⟩
  · intro T hT W hW heq
    change T.erase x = W.erase x at heq
    have hxT := (Finset.mem_filter.mp hT).2
    have hxW := (Finset.mem_filter.mp hW).2
    rw [← Finset.insert_erase hxT, ← Finset.insert_erase hxW, heq]

theorem good_bucket_le_exceptional_plus_peak {F : Finset (Finset V)} {v u x : V} {t : ℕ}
    (ht : 4 ≤ t) (hxu : x ≠ u) (hfree : ¬ F.HasRepeatedDisjointUnion) :
    (goodBucket F v t u x).card ≤
      (exceptionalLink F v t (insert x {u}) (t - 2)).card +
        t * peak F v t (t - 3) := by
  let S : Finset V := insert x {u}
  let L := offLinks F v S (t - 2)
  let Q := exceptional F v t (t - 2)
  have hS : S.card = t - (t - 2) := by
    have hc : S.card = 2 := by simp [S, hxu]
    omega
  have hGood := card_good_remainders_le (v := v) (show 1 ≤ t - 2 by omega)
    (show t - 2 ≤ t - 1 by omega) hS hfree
  have hN : t - 2 - 1 = t - 3 := by omega
  rw [hN] at hGood
  have hSplit : (L.filter (fun T => T ∈ Q)).card + (L \ Q).card = L.card := by
    rw [show L \ Q = L.filter (fun T => T ∉ Q) by ext T; simp]
    exact Finset.card_filter_add_card_filter_not (s := L) _
  change (L \ Q).card ≤ (t - 2) * peak F v t (t - 3) at hGood
  have hGood' := hGood.trans (Nat.mul_le_mul_right (peak F v t (t - 3)) (Nat.sub_le t 2))
  have hG := good_bucket_le_link (F := F) (v := v) (u := u) (x := x) ht
  change (goodBucket F v t u x).card ≤ L.card at hG
  change (goodBucket F v t u x).card ≤ (L.filter (fun T => T ∈ Q)).card +
    t * peak F v t (t - 3)
  omega

theorem bucket_pairs_le_paths {F : Finset (Finset V)} {v u : V} {t : ℕ}
    {T₀ : Finset V} (hT₀ : T₀ ∈ goodLinks F v t u) :
    (∑ x ∈ T₀, (pairedRemainders F v t (insert x {u}) (t - 2)).card) ≤
      ((orderedPaths F v t).filter (fun p => u ∈ p.2)).card := by
  let L (x : V) := pairedRemainders F v t (insert x {u}) (t - 2)
  let Q := exceptional F v t (t - 2)
  let f (a : Σ _ : V, Finset V × Finset V) :
      Σ _ : Finset V × Finset V, Finset V := ⟨a.2, insert a.1 {u}⟩
  have hne : ∀ x ∈ T₀, x ≠ u := by
    intro x hx heq
    obtain ⟨_, hd, _, _⟩ := mem_offLinks_iff.mp (Finset.mem_sdiff.mp hT₀).1
    exact Finset.disjoint_left.mp hd (by simp) (heq ▸ hx)
  change (∑ x ∈ T₀, (L x).card) ≤ _
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn f
  · rintro ⟨x, T, W⟩ ha
    obtain ⟨hx, hp⟩ := Finset.mem_sigma.mp ha
    change (T,W) ∈ ((exceptionalLink F v t (insert x {u}) (t - 2)) ×ˢ
      (exceptionalLink F v t (insert x {u}) (t - 2))).filter (fun p => Disjoint p.1 p.2) at hp
    obtain ⟨hpL, hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hT, hW⟩ := Finset.mem_product.mp hpL
    obtain ⟨hTL, hTQ⟩ := Finset.mem_filter.mp hT
    obtain ⟨hWL, hWQ⟩ := Finset.mem_filter.mp hW
    obtain ⟨_, hST, heT, hvT⟩ := mem_offLinks_iff.mp hTL
    obtain ⟨_, hSW, heW, hvW⟩ := mem_offLinks_iff.mp hWL
    let S : Finset V := insert x {u}
    have hSsub : S ⊆ Finset.univ.erase v := by
      intro y hy
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact hvT (Finset.mem_union_left _ hy)
    have hS2 : S.card = 2 := by simp [S, hne x hx]
    have hSp : S ∈ starLinks v 2 := Finset.mem_powersetCard.mpr ⟨hSsub, hS2⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, by simp [f]⟩
    change (⟨(T, W), S⟩ : Σ _ : Finset V × Finset V, Finset V) ∈ orderedPaths F v t
    apply Finset.mem_sigma.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hTQ, hWQ⟩, hd⟩,
      Finset.mem_filter.mpr ⟨hSp, Finset.disjoint_union_right.mpr ⟨hST, hSW⟩,
        Finset.mem_filter.mpr ⟨heT, hvT⟩, Finset.mem_filter.mpr ⟨heW, hvW⟩⟩⟩
  · rintro ⟨x,p⟩ hx ⟨y,q⟩ hy heq
    have hpq : p = q := congrArg Sigma.fst heq
    have hm : (insert x {u} : Finset V) = insert y {u} := congrArg
      (fun a : Σ _ : Finset V × Finset V, Finset V => a.2) heq
    have hxmem : x ∈ (insert y {u} : Finset V) := hm ▸ Finset.mem_insert_self x {u}
    have hxy : x = y := by
      rcases Finset.mem_insert.mp hxmem with h | h
      · exact h
      · exact False.elim (hne x (Finset.mem_sigma.mp hx).1 (Finset.mem_singleton.mp h))
    subst y
    subst q
    rfl

end Erdos643DeficitLocalLower



/- The ordered-pair lower bound from Claim 3.7 of Huang–Ma–Yang. -/

namespace Erdos643DeficitClaim37Algebra

open scoped BigOperators

/-- Removing at most `b` possible remainders and at most `b` partners per
remaining remainder costs at most `3 * b * g` ordered pairs. -/
theorem ordered_pairs_lower {g k a b : ℝ} (hg : 0 ≤ g) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hremove : g ≤ k + b) (hpairs : k ^ 2 - b * k ≤ a) :
    g ^ 2 - 3 * b * g ≤ a := by
  by_cases hsmall : g ≤ 2 * b
  · have hneg := mul_nonneg hg (show 0 ≤ 3 * b - g by linarith)
    nlinarith only [hneg, ha]
  · have hmono := mul_nonneg (show 0 ≤ k - (g - b) by linarith)
      (show 0 ≤ k + (g - b) - b by linarith)
    calc
      g ^ 2 - 3 * b * g ≤ (g - b) ^ 2 - b * (g - b) := by nlinarith [sq_nonneg b]
      _ ≤ k ^ 2 - b * k := by nlinarith only [hmono]
      _ ≤ a := hpairs

/-- A covered mass squared, divided by an upper bound on the number of
buckets, is bounded by the sum of squared bucket sizes. -/
theorem covered_square_div_le_sum_sq {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hcard : (s.card : ℝ) ≤ r)
    (hcover : d ≤ ∑ i ∈ s, g i) :
    d ^ 2 / r ≤ ∑ i ∈ s, (g i) ^ 2 := by
  have hcauchy : (∑ i ∈ s, g i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (g i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) g
  apply (div_le_iff₀ hr).mpr
  calc
    d ^ 2 ≤ (∑ i ∈ s, g i) ^ 2 := pow_le_pow_left₀ hd hcover _
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (g i) ^ 2 := hcauchy
    _ ≤ r * ∑ i ∈ s, (g i) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = (∑ i ∈ s, (g i) ^ 2) * r := mul_comm _ _

/-- Combining the ordered-pair bound in each bucket with Cauchy–Schwarz. -/
theorem ordered_bucket_count_lower {ι : Type*} (s : Finset ι) (g k a : ι → ℝ)
    {r d b : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hcard : (s.card : ℝ) ≤ r) (hcover : d ≤ ∑ i ∈ s, g i)
    (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ d) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hremove : ∀ i ∈ s, g i ≤ k i + b)
    (hpairs : ∀ i ∈ s, (k i) ^ 2 - b * k i ≤ a i) :
    d ^ 2 / r - 3 * b * r * d ≤ ∑ i ∈ s, a i := by
  have hsum : (∑ i ∈ s, g i) ≤ r * d := by
    calc
      (∑ i ∈ s, g i) ≤ ∑ _i ∈ s, d := Finset.sum_le_sum fun i hi => (hg i hi).2
      _ = (s.card : ℝ) * d := by simp
      _ ≤ r * d := mul_le_mul_of_nonneg_right hcard hd
  have hcost : 3 * b * (∑ i ∈ s, g i) ≤ 3 * b * (r * d) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  calc
    d ^ 2 / r - 3 * b * r * d ≤ (∑ i ∈ s, (g i) ^ 2) - 3 * b * (∑ i ∈ s, g i) := by
      rw [mul_assoc (3 * b) r d]
      exact sub_le_sub (covered_square_div_le_sum_sq s g hr hd hcard hcover) hcost
    _ = ∑ i ∈ s, ((g i) ^ 2 - 3 * b * g i) := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ ∑ i ∈ s, a i := Finset.sum_le_sum fun i hi =>
      ordered_pairs_lower (hg i hi).1 hb (ha i hi) (hremove i hi) (hpairs i hi)

/-- Summing the local lower bounds and using the two vertices of each path
gives the global lower bound, once the degree error is small relative to the
covered mass. -/
theorem ordered_total_lower {ι : Type*} (s : Finset ι) (d a : ι → ℝ)
    {r n m Δ p : ℝ} (hr : 0 < r) (hn : 0 < n) (hm : 0 ≤ m)
    (hcard : (s.card : ℝ) ≤ n)
    (hmass : m / (3 * r) ≤ ∑ i ∈ s, d i)
    (hsmall : 6 * r ^ 3 * n * Δ ≤ ∑ i ∈ s, d i)
    (hlocal : ∀ i ∈ s, (d i) ^ 2 / r - 3 * r ^ 2 * Δ * d i ≤ a i)
    (hdouble : ∑ i ∈ s, a i ≤ 2 * p) :
    m ^ 2 / (36 * r ^ 3 * n) ≤ p := by
  let D := ∑ i ∈ s, d i
  have hD : 0 ≤ D := (div_nonneg hm (by positivity)).trans hmass
  have hcs := covered_square_div_le_sum_sq s d hn hD hcard (le_refl D)
  have hprincipal : D ^ 2 / (r * n) ≤ (∑ i ∈ s, (d i) ^ 2) / r := by
    rw [mul_comm r n, ← div_div]
    exact div_le_div_of_nonneg_right hcs hr.le
  have hscaled : D ^ 2 / (r * n) - 3 * r ^ 2 * Δ * D ≤ 2 * p := by
    calc
      _ ≤ (∑ i ∈ s, (d i) ^ 2) / r - 3 * r ^ 2 * Δ * D :=
        sub_le_sub_right hprincipal _
      _ = ∑ i ∈ s, ((d i) ^ 2 / r - 3 * r ^ 2 * Δ * d i) := by
        rw [Finset.sum_sub_distrib, Finset.sum_div, ← Finset.mul_sum]
      _ ≤ ∑ i ∈ s, a i := Finset.sum_le_sum hlocal
      _ ≤ 2 * p := hdouble
  have hloss : 3 * r ^ 2 * Δ * D ≤ D ^ 2 / (2 * r * n) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = (6 * r ^ 3 * n * Δ) * D := by ring
      _ ≤ D * D := mul_le_mul_of_nonneg_right hsmall hD
      _ = D ^ 2 := (pow_two _).symm
  have hquarter : D ^ 2 / (4 * r * n) ≤ p := by
    have h1 : D ^ 2 / (r * n) = 2 * (D ^ 2 / (2 * r * n)) := by field_simp
    have h2 : D ^ 2 / (2 * r * n) = 2 * (D ^ 2 / (4 * r * n)) := by field_simp; norm_num
    linarith only [hscaled, hloss, h1, h2]
  calc
    m ^ 2 / (36 * r ^ 3 * n) = (m / (3 * r)) ^ 2 / (4 * r * n) := by field_simp; ring
    _ ≤ D ^ 2 / (4 * r * n) := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg hm (by positivity)) hmass _) (by positivity)
    _ ≤ p := hquarter

/-- A bound of the form `Δ ≤ C * m / n^2 + B` supplies the error estimate
in `ordered_total_lower` under explicit thresholds on `n` and `log n`. -/
theorem degree_error_small {r n m C B Δ D : ℝ} (hr : 0 < r) (hn : 0 < n)
    (hm : 0 ≤ m) (hnC : 36 * r ^ 4 * C ≤ n) (hnB : 36 * r ^ 4 * B ≤ Real.log n)
    (hlog : n * Real.log n ≤ m) (hΔ : Δ ≤ C * m / n ^ 2 + B)
    (hD : m / (3 * r) ≤ D) :
    6 * r ^ 3 * n * Δ ≤ D := by
  have hlinear : 36 * r ^ 4 * C * (m / n) ≤ m := by
    calc
      _ ≤ n * (m / n) := mul_le_mul_of_nonneg_right hnC (div_nonneg hm hn.le)
      _ = m := by field_simp
  have hconstant : 36 * r ^ 4 * B * n ≤ m := by
    calc
      _ ≤ Real.log n * n := mul_le_mul_of_nonneg_right hnB hn.le
      _ = n * Real.log n := mul_comm _ _
      _ ≤ m := hlog
  calc
    6 * r ^ 3 * n * Δ ≤ 6 * r ^ 3 * n * (C * m / n ^ 2 + B) :=
      mul_le_mul_of_nonneg_left hΔ (by positivity)
    _ = (36 * r ^ 4 * C * (m / n) + 36 * r ^ 4 * B * n) / (6 * r) := by
      field_simp
      ring
    _ ≤ (m + m) / (6 * r) := div_le_div_of_nonneg_right
      (add_le_add hlinear hconstant) (by positivity)
    _ = m / (3 * r) := by field_simp; ring
    _ ≤ D := hD

open Filter

/-- The degree-error estimate is uniform in every deficit above `n log n`
for all sufficiently large natural orders. -/
theorem eventually_degree_error_small {r : ℝ} (hr : 0 < r) (C B : ℝ) :
    ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n ∧
      ∀ {m Δ D : ℝ}, 0 ≤ m → (n : ℝ) * Real.log n ≤ m →
        Δ ≤ C * m / (n : ℝ) ^ 2 + B → m / (3 * r) ≤ D →
        6 * r ^ 3 * (n : ℝ) * Δ ≤ D := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hcast
  filter_upwards [hcast.eventually_gt_atTop 0, hcast.eventually_ge_atTop (36 * r ^ 4 * C),
    hlog.eventually_ge_atTop (36 * r ^ 4 * B)] with n hn hnC hnB
  exact ⟨hn, fun hm hlarge hΔ hmass => degree_error_small hr hn hm hnC hnB hlarge hΔ hmass⟩

end Erdos643DeficitClaim37Algebra





/- The incidence mass bound in Claim 3.6 of Huang–Ma–Yang. -/

open Finset
open scoped BigOperators

namespace Erdos643DeficitClaim36

/-- If each link has at most one extension outside `U`, every such extension is determined
by its erased link. Edges with two or more outside vertices contribute twice, while edges
with a single outside vertex contribute a link in `U`. -/
theorem clean_edges_incidence_bound {α : Type*} [DecidableEq α]
    (H M : Finset (Finset α)) (U : Finset α) (r : ℕ)
    (hunif : ∀ E ∈ H, E.card = r)
    (houtside : ∀ (S : Finset α), S.card = r - 1 → ∀ x y : α,
      x ∉ U → y ∉ U → x ∉ S → y ∉ S →
      insert x S ∈ H → insert y S ∈ H → x = y) :
    let B := ∑ E ∈ H, (E.filter (fun x => E.erase x ∉ M)).card
    let HI := H.filter (fun E => E ⊆ U)
    2 * H.card ≤ 2 * B + M.card + U.card.choose (r - 1) + 2 * HI.card := by
  classical
  let clean := H.filter (fun E => ∀ x ∈ E, E.erase x ∈ M)
  let dirty : Finset (Σ _ : Finset α, α) :=
    H.sigma (fun E => E.filter (fun x => E.erase x ∉ M))
  let outside : Finset (Σ _ : Finset α, α) := clean.sigma (fun E => E \ U)
  let single := clean.filter (fun E => (E \ U).card = 1)
  let inside := clean.filter (fun E => E ⊆ U)
  have hH : H.card ≤ clean.card + dirty.card := by
    have hcover : H ⊆ clean ∪ dirty.image Sigma.fst := by
      intro E hE
      by_cases hclean : ∀ x ∈ E, E.erase x ∈ M
      · exact mem_union_left _ (mem_filter.mpr ⟨hE, hclean⟩)
      · push Not at hclean
        obtain ⟨x, hx, hm⟩ := hclean
        have hdirty : (⟨E, x⟩ : Σ _ : Finset α, α) ∈ dirty :=
          mem_sigma.mpr ⟨hE, mem_filter.mpr ⟨hx, hm⟩⟩
        exact mem_union_right _ (mem_image.mpr ⟨_, hdirty, rfl⟩)
    exact (card_le_card hcover).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))
  have herase {E G : Finset α} {x y : α} (hE : E ∈ H) (hG : G ∈ H)
      (hx : x ∈ E \ U) (hy : y ∈ G \ U) (heq : E.erase x = G.erase y) :
      x = y ∧ E = G := by
    obtain ⟨hxE, hxU⟩ := mem_sdiff.mp hx
    obtain ⟨hyG, hyU⟩ := mem_sdiff.mp hy
    have hinx : insert x (E.erase x) = E := insert_erase hxE
    have hiny : insert y (E.erase x) = G := by rw [heq, insert_erase hyG]
    have hny : y ∉ E.erase x := by rw [heq]; exact notMem_erase _ _
    have hcard : (E.erase x).card = r - 1 := by rw [card_erase_of_mem hxE, hunif E hE]
    have hxy := houtside (E.erase x) hcard x y hxU hyU (notMem_erase _ _) hny
      (hinx.symm ▸ hE) (hiny.symm ▸ hG)
    exact ⟨hxy, hinx.symm.trans (hxy ▸ hiny)⟩
  have hout : outside.card ≤ M.card := by
    apply card_le_card_of_injOn (fun p => p.1.erase p.2)
    · intro p hp
      obtain ⟨hE, hx⟩ := mem_sigma.mp hp
      exact (mem_filter.mp hE).2 _ (mem_sdiff.mp hx).1
    · rintro ⟨E, x⟩ ha ⟨G, y⟩ hb heq
      obtain ⟨hE, hx⟩ := mem_sigma.mp ha
      obtain ⟨hG, hy⟩ := mem_sigma.mp hb
      obtain ⟨rfl, rfl⟩ := herase (mem_filter.mp hE).1 (mem_filter.mp hG).1 hx hy heq
      rfl
  have hsingle : single.card ≤ U.card.choose (r - 1) := by
    rw [← card_powersetCard]
    have hrep {E : Finset α} (hE : E ∈ single) :
        ∃ x ∈ E \ U, E.erase x = E ∩ U := by
      obtain ⟨x, hx⟩ := card_eq_one.mp (mem_filter.mp hE).2
      have hxEU : x ∈ E \ U := by simp [hx]
      refine ⟨x, hxEU, ?_⟩
      ext y
      simp only [mem_erase, mem_inter]
      constructor
      · rintro ⟨hyx, hyE⟩
        refine ⟨hyE, ?_⟩
        by_contra hyU
        exact hyx (by simpa [hx] using (mem_sdiff.mpr ⟨hyE, hyU⟩ : y ∈ E \ U))
      · rintro ⟨hyE, hyU⟩
        exact ⟨fun heq => (mem_sdiff.mp hxEU).2 (heq ▸ hyU), hyE⟩
    apply card_le_card_of_injOn (fun E => E ∩ U)
    · intro E hE
      obtain ⟨x, hx, heq⟩ := hrep hE
      exact mem_powersetCard.mpr ⟨inter_subset_right, by
        change (E ∩ U).card = r - 1
        rw [← heq, card_erase_of_mem (mem_sdiff.mp hx).1,
          hunif E (mem_filter.mp (mem_filter.mp hE).1).1]⟩
    · intro E hE G hG hEq
      obtain ⟨x, hx, he⟩ := hrep hE
      obtain ⟨y, hy, hg⟩ := hrep hG
      exact (herase (mem_filter.mp (mem_filter.mp hE).1).1
        (mem_filter.mp (mem_filter.mp hG).1).1 hx hy (he.trans (hEq.trans hg.symm))).2
  have hinside : inside.card ≤ (H.filter (fun E => E ⊆ U)).card := by
    apply card_le_card
    intro E hE
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hE).1).1, (mem_filter.mp hE).2⟩
  have hclean : 2 * clean.card ≤ outside.card + single.card + 2 * inside.card := by
    change _ ≤ (clean.sigma (fun E => E \ U)).card + _ + _
    rw [card_sigma]
    have hsingleSum : single.card = ∑ E ∈ clean, if (E \ U).card = 1 then 1 else 0 := by
      exact card_filter _ _
    have hinsideSum : inside.card = ∑ E ∈ clean, if E ⊆ U then 1 else 0 := by
      exact card_filter _ _
    rw [hsingleSum, hinsideSum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    calc
      2 * clean.card = ∑ _ ∈ clean, 2 := by simp [mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro E _
        by_cases hs : E ⊆ U
        · simp [hs]
        have hpos : 0 < (E \ U).card := by
          apply card_pos.mpr
          exact sdiff_nonempty.mpr hs
        by_cases h1 : (E \ U).card = 1
        · simp [h1]
        · have h2 : 2 ≤ (E \ U).card := by omega
          exact h2.trans (by simp [h1, hs])
  have hdirty : dirty.card = ∑ E ∈ H, (E.filter (fun x => E.erase x ∉ M)).card :=
    card_sigma _ _
  dsimp only
  omega

/-- Claim 3.6 with an explicit allowable cost for the edges supported on `U`. -/
theorem claim36_of_induced_cost {α : Type*} [DecidableEq α]
    (H M : Finset (Finset α)) (U : Finset α) (r : ℕ) (hr : 3 ≤ r)
    (hunif : ∀ E ∈ H, E.card = r)
    (houtside : ∀ (S : Finset α), S.card = r - 1 → ∀ x y : α,
      x ∉ U → y ∉ U → x ∉ S → y ∉ S →
      insert x S ∈ H → insert y S ∈ H → x = y)
    (hdensity : (2 * r - 1) * M.card ≤ 2 * r * H.card)
    (hsmall : 3 * r * (U.card.choose (r - 1) + 2 * (H.filter (fun E => E ⊆ U)).card) ≤
      M.card) :
    M.card ≤ 3 * r * ∑ E ∈ H, (E.filter (fun x => E.erase x ∉ M)).card := by
  have hc := clean_edges_incidence_bound H M U r hunif houtside
  dsimp only at hc
  have hdensity' : 2 * r * M.card ≤ 2 * r * H.card + M.card := by
    rw [Nat.sub_mul, Nat.one_mul] at hdensity
    omega
  have hcount := Nat.mul_le_mul_left (3 * r) hc
  have hdensityScaled := Nat.mul_le_mul_left 3 hdensity'
  have hrm := Nat.mul_le_mul_right M.card hr
  nlinarith only [hcount, hdensityScaled, hsmall, hrm]

/-- The same bound with any uniform estimate of order `U.card ^ (r - 1)`
for the induced family. -/
theorem claim36_of_induced_power_bound {α : Type*} [DecidableEq α]
    (H M : Finset (Finset α)) (U : Finset α) (r C : ℕ) (hr : 3 ≤ r)
    (hunif : ∀ E ∈ H, E.card = r)
    (houtside : ∀ (S : Finset α), S.card = r - 1 → ∀ x y : α,
      x ∉ U → y ∉ U → x ∉ S → y ∉ S →
      insert x S ∈ H → insert y S ∈ H → x = y)
    (hdensity : (2 * r - 1) * M.card ≤ 2 * r * H.card)
    (hinduced : (H.filter (fun E => E ⊆ U)).card ≤ C * U.card ^ (r - 1))
    (hsmall : 3 * r * (1 + 2 * C) * U.card ^ (r - 1) ≤ M.card) :
    M.card ≤ 3 * r * ∑ E ∈ H, (E.filter (fun x => E.erase x ∉ M)).card := by
  apply claim36_of_induced_cost H M U r hr hunif houtside hdensity
  have hcost : U.card.choose (r - 1) + 2 * (H.filter (fun E => E ⊆ U)).card ≤
      (1 + 2 * C) * U.card ^ (r - 1) := by
    nlinarith only [hinduced, Nat.choose_le_pow U.card (r - 1)]
  exact (Nat.mul_le_mul_left (3 * r) hcost).trans (by simpa [Nat.mul_assoc] using hsmall)

/-- Count nonmissing one-vertex deletions either by the edge or by the deleted vertex. -/
theorem bad_link_mass_eq_vertex_sum {α : Type*} [DecidableEq α]
    (H M : Finset (Finset α)) (W : Finset α) (hW : ∀ E ∈ H, E ⊆ W) :
    (∑ E ∈ H, (E.filter (fun x => E.erase x ∉ M)).card) =
    ∑ x ∈ W, (((H.filter (fun E => x ∈ E)).image (fun E => E.erase x)) \ M).card := by
  have himage (x : α) : ((H.filter (fun E => x ∈ E)).image (fun E => E.erase x)) \ M =
      (H.filter (fun E => x ∈ E ∧ E.erase x ∉ M)).image (fun E => E.erase x) := by
    ext S
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨E, ⟨hE, hx⟩, rfl⟩, hM⟩
      exact ⟨E, ⟨hE, hx, hM⟩, rfl⟩
    · rintro ⟨E, ⟨hE, hx, hM⟩, rfl⟩
      exact ⟨⟨E, ⟨hE, hx⟩, rfl⟩, hM⟩
  have himageCard (x : α) :
      (((H.filter (fun E => x ∈ E)).image (fun E => E.erase x)) \ M).card =
      (H.filter (fun E => x ∈ E ∧ E.erase x ∉ M)).card := by
    rw [himage]
    apply card_image_of_injOn
    intro E hE G hG heq
    have hE' := (mem_filter.mp hE).2.1
    have hG' := (mem_filter.mp hG).2.1
    change E.erase x = G.erase x at heq
    exact (insert_erase hE').symm.trans (by rw [heq, insert_erase hG'])
  classical
  calc
    _ = ∑ E ∈ H, ∑ x ∈ W, if x ∈ E ∧ E.erase x ∉ M then 1 else 0 := by
      apply sum_congr rfl
      intro E hE
      rw [← card_filter]
      congr 1
      ext x
      simp only [mem_filter]
      exact ⟨fun h => ⟨hW E hE h.1, h⟩, And.right⟩
    _ = ∑ x ∈ W, ∑ E ∈ H, if x ∈ E ∧ E.erase x ∉ M then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      rw [himageCard, card_filter]

end Erdos643DeficitClaim36


/- Counting paths by the vertices of their two-element middle sets. -/

open scoped BigOperators

namespace Erdos643DeficitMiddleCounting

/-- Reindex the number of incidences between a finite family and its middle sets. -/
theorem sum_middle_incidence_card {V P : Type*} [DecidableEq V]
    (paths : Finset P) (middle : P → Finset V) (W : Finset V) (k : ℕ)
    (hW : ∀ p ∈ paths, middle p ⊆ W) (hcard : ∀ p ∈ paths, (middle p).card = k) :
    (∑ x ∈ W, (paths.filter (fun p => x ∈ middle p)).card) = k * paths.card := by
  calc
    _ = ∑ x ∈ W, ∑ p ∈ paths, if x ∈ middle p then 1 else 0 := by
      simp only [Finset.card_filter]
    _ = ∑ p ∈ paths, ∑ x ∈ W, if x ∈ middle p then 1 else 0 := Finset.sum_comm
    _ = ∑ _p ∈ paths, k := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (hW p hp), hcard p hp]
    _ = _ := by simp [Nat.mul_comm]

/-- A path with a two-element middle set contributes two to the sum over vertices. -/
theorem sum_middle_incidence_card_two {V P : Type*} [Fintype V] [DecidableEq V]
    (paths : Finset P) (middle : P → Finset V)
    (hcard : ∀ p ∈ paths, (middle p).card = 2) :
    (∑ x ∈ Finset.univ, (paths.filter (fun p => x ∈ middle p)).card) = 2 * paths.card :=
  sum_middle_incidence_card paths middle Finset.univ 2 (fun _ _ => Finset.subset_univ _) hcard

/-- The incidence identity in the real numbers, for the quadratic estimate. -/
theorem sum_middle_incidence_card_two_real {V P : Type*} [Fintype V] [DecidableEq V]
    (paths : Finset P) (middle : P → Finset V)
    (hcard : ∀ p ∈ paths, (middle p).card = 2) :
    (∑ x ∈ Finset.univ, ((paths.filter (fun p => x ∈ middle p)).card : ℝ)) =
      2 * (paths.card : ℝ) := by
  exact_mod_cast sum_middle_incidence_card_two paths middle hcard

end Erdos643DeficitMiddleCounting


/- The numerical conclusion of the star-deficit path count in Lemma 3.3. -/

namespace Erdos643DeficitFinalAlgebra

/-- The upper and lower counts in Lemma 3.3 contradict the assumed size of the
exceptional vertex set once the order of the hypergraph exceeds the indicated
threshold. -/
theorem incompatible_path_counts {r : ℕ} (hr : 0 < r) {n m u o : ℝ}
    (hn : 600 * (r : ℝ) ^ (4 * r + 3) < n) (hm : 0 < m)
    (hu : u ≤ n / (50 * (r : ℝ) ^ (4 * r + 3)))
    (hUpper : o ≤ (r : ℝ) ^ (4 * r) * (m ^ 2 / n ^ 2) * (u + 3))
    (hLower : m ^ 2 / (40 * (r : ℝ) ^ 3 * n) ≤ o) : False := by
  let R : ℝ := (r : ℝ) ^ (4 * r)
  let D : ℝ := (r : ℝ) ^ (4 * r + 3)
  let K : ℝ := m ^ 2 / (40 * (r : ℝ) ^ 3 * n ^ 2)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hD : 0 < D := pow_pos hr' _
  have hn' : 0 < n := (mul_pos (by norm_num) hD).trans hn
  have hK : 0 < K := by dsimp [K]; positivity
  have hprod : D = R * (r : ℝ) ^ 3 := pow_add _ _ _
  have hcomp : K * n ≤ K * (40 * D * (u + 3)) := by
    calc
      K * n = m ^ 2 / (40 * (r : ℝ) ^ 3 * n) := by
        dsimp [K]
        field_simp
      _ ≤ o := hLower
      _ ≤ R * (m ^ 2 / n ^ 2) * (u + 3) := hUpper
      _ = K * (40 * D * (u + 3)) := by
        rw [hprod]
        dsimp [K]
        field_simp
  have hcount : n ≤ 40 * D * (u + 3) := (mul_le_mul_iff_right₀ hK).mp hcomp
  have hu' : u * (50 * D) ≤ n := (le_div_iff₀ (mul_pos (by norm_num) hD)).mp hu
  have hsmall : 40 * D * (u + 3) < n := by
    change 600 * D < n at hn
    nlinarith only [hu', hn]
  exact (not_lt_of_ge hcount) hsmall

/-- Conditional on the two path counts, the star deficit is at most
`n * Real.log n`. -/
theorem deficit_le_n_log_n {r : ℕ} (hr : 0 < r) {n m u : ℝ}
    (hn : 600 * (r : ℝ) ^ (4 * r + 3) < n)
    (hu : u ≤ n / (50 * (r : ℝ) ^ (4 * r + 3)))
    (hCounts : n * Real.log n < m → ∃ o : ℝ,
      o ≤ (r : ℝ) ^ (4 * r) * (m ^ 2 / n ^ 2) * (u + 3) ∧
      m ^ 2 / (40 * (r : ℝ) ^ 3 * n) ≤ o) :
    m ≤ n * Real.log n := by
  by_contra! hlarge
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpow : (1 : ℝ) ≤ (r : ℝ) ^ (4 * r + 3) := one_le_pow₀ hr'
  have hn' : 1 ≤ n := by linarith
  have hm : 0 < m := (mul_nonneg (by linarith) (Real.log_nonneg hn')).trans_lt hlarge
  obtain ⟨o, hUpper, hLower⟩ := hCounts hlarge
  exact incompatible_path_counts hr hn hm hu hUpper hLower

end Erdos643DeficitFinalAlgebra


namespace Erdos643DeficitPaths

open Finset Erdos643StarLinks Erdos643DeficitLinkDegree Erdos643PathCountUpper
open Erdos643DeficitPairs Erdos643DeficitLocalLower Erdos643DeficitClaim37Algebra

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem local_path_count {F : Finset (Finset V)} {v u : V} {t : ℕ} (ht : 4 ≤ t)
    (hfree : ¬ F.HasRepeatedDisjointUnion) :
    let d : ℝ := (goodLinks F v t u).card
    let Δ : ℝ := peak F v t (t - 3)
    d ^ 2 / (t : ℝ) - 3 * (t : ℝ) ^ 2 * Δ * d ≤
      (((orderedPaths F v t).filter (fun p => u ∈ p.2)).card : ℝ) := by
  classical
  let G := goodLinks F v t u
  let Δ : ℝ := peak F v t (t - 3)
  change (G.card : ℝ) ^ 2 / (t : ℝ) - 3 * (t : ℝ) ^ 2 * Δ * G.card ≤ _
  by_cases hG : G.Nonempty
  · obtain ⟨T₀,hT₀⟩ := hG
    have hTm := mem_offLinks_iff.mp (Finset.mem_sdiff.mp hT₀).1
    have hcx : ∀ x ∈ T₀, x ≠ u := by
      intro x hx heq
      exact Finset.disjoint_left.mp hTm.2.1 (by simp) (heq ▸ hx)
    have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hTcard : (T₀.card : ℝ) ≤ t := by
      exact_mod_cast (hTm.1.le.trans (Nat.sub_le t 1))
    let g (x : V) : ℝ := (goodBucket F v t u x).card
    let k (x : V) : ℝ := (exceptionalLink F v t (insert x {u}) (t - 2)).card
    let a (x : V) : ℝ := (pairedRemainders F v t (insert x {u}) (t - 2)).card
    have hcover : (G.card : ℝ) ≤ ∑ x ∈ T₀, g x := by
      dsimp only [G, g]
      exact_mod_cast (bucket_cover ht hfree hT₀)
    have hg : ∀ x ∈ T₀, 0 ≤ g x ∧ g x ≤ (G.card : ℝ) := by
      intro x _
      exact ⟨by dsimp [g]; positivity,
        by dsimp only [g, goodBucket, G]; exact_mod_cast (Finset.card_filter_le (s := G) (fun T => x ∈ T))⟩
    have hremove : ∀ x ∈ T₀, g x ≤ k x + (t : ℝ) * Δ := by
      intro x hx
      dsimp only [g, k, Δ]
      exact_mod_cast (good_bucket_le_exceptional_plus_peak (v := v) ht (hcx x hx) hfree)
    have hpairs : ∀ x ∈ T₀, (k x) ^ 2 - ((t : ℝ) * Δ) * k x ≤ a x := by
      intro x hx
      have hsize : (insert x ({u} : Finset V)).card = t - (t - 2) := by
        rw [Finset.card_insert_of_notMem (by simp [hcx x hx]), Finset.card_singleton]
        omega
      simpa only [show t - 2 - 1 = t - 3 by omega] using paired_remainders_card_lower
        (F := F) (v := v) (show 1 ≤ t - 2 by omega) (Nat.sub_le t 2) hsize
    have hlow := ordered_bucket_count_lower T₀ g k a htpos (by positivity)
      (show 0 ≤ (t : ℝ) * Δ by dsimp [Δ]; positivity) hTcard hcover hg
      (fun x _ => by dsimp [a]; positivity) hremove hpairs
    have hpath : (∑ x ∈ T₀, a x) ≤ (((orderedPaths F v t).filter (fun p => u ∈ p.2)).card : ℝ) := by
      dsimp only [a]
      exact_mod_cast (bucket_pairs_le_paths hT₀)
    rw [show 3 * ((t : ℝ) * Δ) * (t : ℝ) * (G.card : ℝ) =
      3 * (t : ℝ) ^ 2 * Δ * G.card by ring] at hlow
    exact hlow.trans hpath
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hG
    simp [hz]

theorem singleton_link_eq_deletions {F : Finset (Finset V)} {v u : V} {t : ℕ}
    (hF : F.IsUniform t) :
    offLinks F v {u} (t - 1) =
      ((F.filter (fun E => v ∉ E)).filter (fun E => u ∈ E)).image (fun E => E.erase u) := by
  ext T
  constructor
  · intro hT
    obtain ⟨_, hd, he, hv⟩ := mem_offLinks_iff.mp hT
    have hu : u ∉ T := fun h => Finset.disjoint_left.mp hd (by simp) h
    refine Finset.mem_image.mpr ⟨insert u T, ?_, Finset.erase_insert hu⟩
    rw [Finset.singleton_union] at he hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he, hv⟩, by simp⟩
  · intro hT
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hIn,hu⟩ := Finset.mem_filter.mp hE
    obtain ⟨hEF,hv⟩ := Finset.mem_filter.mp hIn
    have hEq : ({u} : Finset V) ∪ E.erase u = E := by
      rw [Finset.singleton_union, Finset.insert_erase hu]
    apply mem_offLinks_iff.mpr
    refine ⟨by rw [Finset.card_erase_of_mem hu, hF E hEF], ?_, hEq.symm ▸ hEF, hEq.symm ▸ hv⟩
    simp

theorem good_link_mass_eq {F : Finset (Finset V)} {v : V} {t : ℕ}
    (hF : F.IsUniform t) :
    let H := F.filter (fun E => v ∉ E)
    let M := missingLinks F v t
    (∑ E ∈ H, (E.filter (fun u => E.erase u ∉ M)).card) =
      ∑ u ∈ (Finset.univ : Finset V), (goodLinks F v t u).card := by
  dsimp only
  rw [Erdos643DeficitClaim36.bad_link_mass_eq_vertex_sum _ _ Finset.univ
    (fun E _ => Finset.subset_univ E)]
  apply Finset.sum_congr rfl
  intro u _
  simp only [goodLinks, exceptional_full_eq_missing, singleton_link_eq_deletions hF]

end Erdos643DeficitPaths


namespace Erdos643DeficitPaths

open Finset Filter Erdos643StarLinks Erdos643DeficitLinkDegree Erdos643PathCountUpper
open Erdos643DeficitLocalLower Erdos643DeficitClaim37Algebra
open Erdos643CommonFiller Erdos643ExceptionalBounds

/- A coefficient depending only on the uniformity for the induced-family edge bound. -/
def InducedBound (K : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ (n : ℕ) (U : Finset (Fin n)) (G : Finset (Finset (Fin n))),
    G.IsUniform t → ¬ G.HasRepeatedDisjointUnion → (∀ E ∈ G, E ⊆ U) →
      G.card ≤ K t * U.card ^ (t - 1)

private theorem exceptional_scaled {n t : ℕ} {F : Finset (Finset (Fin n))} {v : Fin n}
    (ht : 4 ≤ t) (hn : 6 * t ≤ n) (i : ℕ) (hi : i ≤ t - 1) :
    (exceptional F v t i).card * n ^ (t - 1 - i) ≤ t ^ (2 * t) * (missingLinks F v t).card := by
  apply incidence_to_exceptional_bound_sharp ht hn hi
  apply exceptional_card_bound (missing_uniform F v t) (exceptional_uniform F v t i)
  intro T hT
  simpa only [Fintype.card_fin] using (Finset.mem_filter.mp hT).2

theorem path_count_upper {n t : ℕ} {F : Finset (Finset (Fin n))} {v : Fin n}
    {U : Finset (Fin n)} (ht : 4 ≤ t) (hn : 6 * t ≤ n)
    (hfree : ¬ F.HasRepeatedDisjointUnion)
    (hOutside : ∀ S : Finset (Fin n), S.card = t - 1 →
      ((Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ F.filter (fun E => v ∉ E))) \ U).card ≤ 1) :
    let m : ℝ := (missingLinks F v t).card
    ((orderedPaths F v t).card : ℝ) ≤
      (t : ℝ) ^ (4 * t) * (m ^ 2 / (n : ℝ) ^ 2) * ((U.card : ℝ) + 3) := by
  dsimp only
  let m : ℝ := (missingLinks F v t).card
  let q : ℝ := (exceptional F v t (t - 2)).card
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq := exceptional_scaled (F := F) (v := v) ht hn (t - 2) (by omega)
  rw [show t - 1 - (t - 2) = 1 by omega, pow_one] at hq
  have hq' : q * (n : ℝ) ≤ (t : ℝ) ^ (2 * t) * m := by
    dsimp only [q, m]
    exact_mod_cast hq
  have hqle : q ≤ (t : ℝ) ^ (2 * t) * m / (n : ℝ) := (le_div_iff₀ hnpos).mpr hq'
  have hcount : ((orderedPaths F v t).card : ℝ) ≤ q ^ 2 * ((U.card : ℝ) + 3) := by
    dsimp only [q]
    exact_mod_cast (ordered_paths_card_le (v := v) ht hfree hOutside)
  calc
    _ ≤ q ^ 2 * ((U.card : ℝ) + 3) := hcount
    _ ≤ ((t : ℝ) ^ (2 * t) * m / (n : ℝ)) ^ 2 * ((U.card : ℝ) + 3) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by dsimp [q]; positivity) hqle _) (by positivity)
    _ = _ := by
      rw [div_pow, mul_pow, ← pow_mul]
      congr 1
      rw [show 2 * t * 2 = 4 * t by omega]
      ring

theorem path_degree_bound {n t : ℕ} {F : Finset (Finset (Fin n))} {v : Fin n}
    (ht : 4 ≤ t) (hn : 6 * t ≤ n) (hfree : ¬ F.HasRepeatedDisjointUnion) :
    (peak F v t (t - 3) : ℝ) ≤
      ((t - 3 : ℕ) : ℝ) * (t : ℝ) ^ (2 * t) * ((missingLinks F v t).card : ℝ) /
      (n : ℝ) ^ 2 + (t : ℝ) ^ (t - 3) := by
  have hbound := peak_bound_scaled (F := F) (v := v) (m := (missingLinks F v t).card)
    (c := t ^ (2 * t)) (show t ≤ n by omega) hfree
    (fun j _ hj => exceptional_scaled ht hn j hj) (i := t - 3) (by omega)
  rw [show t - 1 - (t - 3) = 2 by omega] at hbound
  have hcast : (peak F v t (t - 3) : ℝ) * (n : ℝ) ^ 2 ≤
      ((t - 3 : ℕ) : ℝ) * (t : ℝ) ^ (2 * t) * ((missingLinks F v t).card : ℝ) +
        (t : ℝ) ^ (t - 3) * (n : ℝ) ^ 2 := by exact_mod_cast hbound
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdiv := (le_div_iff₀ (pow_pos hnpos 2)).mpr hcast
  calc
    _ ≤ _ := hdiv
    _ = _ := by field_simp

theorem path_mass_lower {K : ℕ → ℕ} (hinduced : InducedBound K)
    {n t : ℕ} {F : Finset (Finset (Fin n))} {v : Fin n} {U : Finset (Fin n)}
    (ht : 4 ≤ t) (hF : F.IsUniform t) (hfree : ¬ F.HasRepeatedDisjointUnion)
    (hOutside : ∀ S : Finset (Fin n), S.card = t - 1 →
      ((Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ F.filter (fun E => v ∉ E))) \ U).card ≤ 1)
    (hm : (missingLinks F v t).card ≤ (F.filter (fun E => v ∉ E)).card)
    (hsmall : 3 * t * (1 + 2 * K t) * U.card ^ (t - 1) ≤ (missingLinks F v t).card) :
    ((missingLinks F v t).card : ℝ) / (3 * (t : ℝ)) ≤
      ∑ u ∈ (Finset.univ : Finset (Fin n)), ((goodLinks F v t u).card : ℝ) := by
  let H := F.filter (fun E => v ∉ E)
  let M := missingLinks F v t
  let I := H.filter (fun E => E ⊆ U)
  have hH : H.IsUniform t := fun E hE => hF E (Finset.mem_filter.mp hE).1
  have hIsub : I ⊆ F := fun E hE => (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1
  have hIfree : ¬ I.HasRepeatedDisjointUnion := by
    intro hI
    obtain ⟨A,hA,B,hB,C,hC,D,hD,hRest⟩ := hI
    exact hfree ⟨A,hIsub hA,B,hIsub hB,C,hIsub hC,D,hIsub hD,hRest⟩
  have hI := hinduced t ht n U I (fun E hE => hF E (hIsub hE)) hIfree
    (fun E hE => (Finset.mem_filter.mp hE).2)
  have hOut : ∀ (S : Finset (Fin n)), S.card = t - 1 → ∀ x y : Fin n,
      x ∉ U → y ∉ U → x ∉ S → y ∉ S → insert x S ∈ H → insert y S ∈ H → x = y := by
    intro S hS x y hxU hyU hxS hyS hx hy
    have hcount := hOutside S hS
    let L := (Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ H)) \ U
    have hxL : x ∈ L := Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxS, hx⟩, hxU⟩
    have hyL : y ∈ L := Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyS, hy⟩, hyU⟩
    exact Finset.card_le_one_iff.mp hcount hxL hyL
  have hden : (2 * t - 1) * M.card ≤ 2 * t * H.card :=
    (Nat.mul_le_mul_right M.card (Nat.sub_le _ _)).trans (Nat.mul_le_mul_left _ hm)
  have hmass := Erdos643DeficitClaim36.claim36_of_induced_power_bound H M U t (K t)
    (show 3 ≤ t by omega) hH hOut hden hI hsmall
  rw [good_link_mass_eq hF] at hmass
  apply (div_le_iff₀ (show (0 : ℝ) < 3 * (t : ℝ) by exact_mod_cast (show 0 < 3 * t by omega))).mpr
  rw [mul_comm]
  exact_mod_cast hmass

end Erdos643DeficitPaths


namespace Erdos643DeficitPaths

open Finset Filter Erdos643StarLinks Erdos643DeficitLinkDegree Erdos643PathCountUpper
open Erdos643DeficitLocalLower Erdos643DeficitClaim37Algebra Erdos643DeficitFinalAlgebra

/-- The full star-deficit estimate follows from a coarse bound on induced subgraphs. -/
theorem star_deficit_bound {K : ℕ → ℕ} (hinduced : InducedBound K) :
    Erdos643DeficitApplication.StarDeficitEstimate K := by
  intro t ht
  have htpos : 0 < t := by omega
  have htr : (0 : ℝ) < t := by exact_mod_cast htpos
  let C : ℝ := ((t - 3 : ℕ) : ℝ) * (t : ℝ) ^ (2 * t)
  let B : ℝ := (t : ℝ) ^ (t - 3)
  filter_upwards [eventually_ge_atTop (6 * t), eventually_gt_atTop (600 * t ^ (4 * t + 3)),
    eventually_degree_error_small htr C B] with n hn hthreshold herror
  intro F hF hfree v U _
  dsimp only
  intro hmH hU hUcost hOut
  let M := missingLinks F v t
  let m := (n - 1).choose (t - 1) - (F.filter (fun E => v ∈ E)).card
  have hM : M.card = m := by simpa [M, m] using missing_card v hF
  have hUpper := path_count_upper (v := v) ht hn hfree hOut
  change ((orderedPaths F v t).card : ℝ) ≤
    (t : ℝ) ^ (4 * t) * ((M.card : ℝ) ^ 2 / (n : ℝ) ^ 2) * ((U.card : ℝ) + 3) at hUpper
  rw [hM] at hUpper
  change (m : ℝ) ≤ (n : ℝ) * Real.log n
  refine deficit_le_n_log_n htpos (by exact_mod_cast hthreshold) hU ?_
  intro hlarge
  let P := orderedPaths F v t
  refine ⟨(P.card : ℝ), hUpper, ?_⟩
  let d (u : Fin n) : ℝ := (goodLinks F v t u).card
  let a (u : Fin n) : ℝ := ((P.filter (fun p => u ∈ p.2)).card : ℝ)
  let Δ : ℝ := peak F v t (t - 3)
  let V : Finset (Fin n) := Finset.univ
  let b : ℕ := 3 * t * (1 + 2 * K t)
  have hb' : 0 < b := by dsimp only [b]; positivity
  have hb : (0 : ℝ) < b := by exact_mod_cast hb'
  have hcostReal : (U.card : ℝ) ^ (t - 1) ≤ (m : ℝ) / (b : ℝ) := hUcost
  have hsmall : b * U.card ^ (t - 1) ≤ M.card := by
    rw [hM]
    have this := (le_div_iff₀ hb).mp hcostReal
    rw [mul_comm] at this
    exact_mod_cast this
  have hmass : (m : ℝ) / (3 * (t : ℝ)) ≤ ∑ u ∈ V, d u := by
    rw [← hM]
    exact path_mass_lower hinduced ht hF hfree hOut (hM ▸ hmH) hsmall
  have hdeg : Δ ≤ C * (m : ℝ) / (n : ℝ) ^ 2 + B := by
    have hD := path_degree_bound (v := v) ht hn hfree
    change Δ ≤ C * (M.card : ℝ) / (n : ℝ) ^ 2 + B at hD
    simpa only [hM] using hD
  have herr := herror.2 (by positivity : 0 ≤ (m : ℝ)) hlarge.le hdeg hmass
  have hlocal : ∀ u ∈ V, (d u) ^ 2 / (t : ℝ) - 3 * (t : ℝ) ^ 2 * Δ * d u ≤ a u :=
    fun u _ => local_path_count (v := v) (u := u) ht hfree
  have hmid (p) (hp : p ∈ P) : p.2.card = 2 := by
    change p ∈ orderedPaths F v t at hp
    unfold orderedPaths at hp
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).1).2
  have hdouble : (∑ u ∈ V, a u) ≤ 2 * (P.card : ℝ) :=
    (Erdos643DeficitMiddleCounting.sum_middle_incidence_card_two_real P Sigma.snd hmid).le
  have hncard : (V.card : ℝ) ≤ n := by simp [V]
  have hLower := ordered_total_lower V d a htr herror.1 (show 0 ≤ (m : ℝ) by positivity)
    hncard hmass herr hlocal hdouble
  have hden : 36 * (t : ℝ) ^ 3 * (n : ℝ) ≤ 40 * (t : ℝ) ^ 3 * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
      herror.1.le
  have hdenpos : 0 < 36 * (t : ℝ) ^ 3 * (n : ℝ) :=
    mul_pos (mul_pos (by norm_num) (pow_pos htr _)) herror.1
  exact (div_le_div_of_nonneg_left (sq_nonneg (m : ℝ)) hdenpos hden).trans hLower

theorem h2_of_induced_bound {K : ℕ → ℕ} (hinduced : InducedBound K) :
    OMA.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1.H2 :=
  Erdos643DeficitApplication.H2_of_starDeficitEstimate (star_deficit_bound hinduced)

end Erdos643DeficitPaths

/- Total charge for disjoint-union-free tripartite triples. -/

open scoped BigOperators

namespace Erdos643.CrudeBound

abbrev Triple (α : Type*) := Fin 3 → α
abbrev Alternative (α : Type*) := Fin 3 × α

variable {α : Type*} [DecidableEq α]

def alternatives [Fintype α] (H : Finset (Triple α)) (e : Triple α) : Finset (Alternative α) :=
  Finset.univ.filter fun p => p.2 ≠ e p.1 ∧ Function.update e p.1 p.2 ∈ H

def commonLink (H : Finset (Triple α)) (i : Fin 3) (x y : α) : Finset (Triple α) :=
  H.filter fun u => u i = x ∧ Function.update u i y ∈ H

def localAdj (H : Finset (Triple α)) (e : Triple α) (p q : Alternative α) : Prop :=
  p.1 ≠ q.1 ∧ Function.update (Function.update e p.1 p.2) q.1 q.2 ∈ H

def tupleDisjointUnionFree {ι : Type*} (H : Finset (ι → α)) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, ∀ g ∈ H, ∀ h ∈ H,
    (∀ i, e i ≠ f i) →
    (∀ i, (e i = g i ∧ f i = h i) ∨ (e i = h i ∧ f i = g i)) →
    (e = g ∧ f = h) ∨ (e = h ∧ f = g)

abbrev disjointUnionFree (H : Finset (Triple α)) : Prop := tupleDisjointUnionFree H

variable [Fintype α]

noncomputable def charge (H : Finset (Triple α)) (e : Triple α) : ℝ :=
  ∑ p ∈ alternatives H e, 1 / ((commonLink H p.1 (e p.1) p.2).card : ℝ)

theorem sum_charge_eq (H : Finset (Triple α)) :
    (∑ e ∈ H, charge H e) = ∑ p : Alternative α, ∑ x : α,
      if x ≠ p.2 ∧ (commonLink H p.1 x p.2).Nonempty then (1 : ℝ) else 0 := by
  classical
  simp only [charge, alternatives, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_fiberwise H (fun e => e p.1)]
  apply Finset.sum_congr rfl
  intro x _
  have hreplace : (∑ e ∈ H.filter (fun e => e p.1 = x),
      if p.2 ≠ e p.1 ∧ Function.update e p.1 p.2 ∈ H then
        1 / ((commonLink H p.1 (e p.1) p.2).card : ℝ) else 0) =
      ∑ e ∈ H.filter (fun e => e p.1 = x),
        if p.2 ≠ x ∧ Function.update e p.1 p.2 ∈ H then
          1 / ((commonLink H p.1 x p.2).card : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  rw [hreplace]
  by_cases hne : x ≠ p.2
  · simp only [ne_eq, hne, Ne.symm hne, not_false_eq_true, true_and]
    rw [← Finset.sum_filter]
    change (∑ _ ∈ (H.filter (fun e => e p.1 = x)).filter
        (fun e => Function.update e p.1 p.2 ∈ H),
      1 / ((commonLink H p.1 x p.2).card : ℝ)) = _
    rw [Finset.filter_filter]
    change (∑ _ ∈ commonLink H p.1 x p.2,
      1 / ((commonLink H p.1 x p.2).card : ℝ)) = _
    rw [Finset.sum_const, nsmul_eq_mul]
    by_cases hpositive : (commonLink H p.1 x p.2).Nonempty
    · have hcard : ((commonLink H p.1 x p.2).card : ℝ) ≠ 0 := by
        exact_mod_cast hpositive.card_ne_zero
      simp [hpositive, hcard, div_eq_mul_inv]
    · have hempty : commonLink H p.1 x p.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpositive
      simp [hempty]
  · have heq : x = p.2 := not_ne_iff.mp hne
    simp [heq]

theorem sum_charge_le (H : Finset (Triple α)) :
    (∑ e ∈ H, charge H e) ≤ 3 * (Fintype.card α : ℝ) ^ 2 := by
  classical
  rw [sum_charge_eq]
  calc
    _ ≤ ∑ _ : Alternative α, ∑ _ : α, (1 : ℝ) := by
      refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun x _ => ?_
      split <;> norm_num
    _ = _ := by simp [Fintype.card_prod, pow_two, mul_assoc]

theorem card_inactive_le (H : Finset (Triple α)) :
    (H.filter fun e => ¬ (alternatives H e).Nonempty).card ≤ (Fintype.card α) ^ 2 := by
  classical
  have hcap : (H.filter fun e => ¬ (alternatives H e).Nonempty).card ≤
      (Finset.univ : Finset (α × α)).card := by
    apply Finset.card_le_card_of_injOn (fun e : Triple α => (e 0, e 1))
    · intro e _
      exact Finset.mem_univ _
    · intro e he f hf heq
      by_contra hne
      have h0 : e 0 = f 0 := congrArg Prod.fst heq
      have h1 : e 1 = f 1 := congrArg Prod.snd heq
      have h2 : f 2 ≠ e 2 := by
        intro h
        apply hne
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h.symm
      have hup : Function.update e 2 (f 2) = f := by
        funext i
        fin_cases i
        · simpa using h0
        · simpa using h1
        · simp
      have hfH := (Finset.mem_filter.mp hf).1
      have htag : ((2 : Fin 3), f 2) ∈ alternatives H e := by
        simp [alternatives, h2, hup, hfH]
      exact (Finset.mem_filter.mp he).2 ⟨_, htag⟩
  simpa [Fintype.card_prod, pow_two] using hcap

theorem card_le_of_charge_ge_one (H : Finset (Triple α))
    (hpoint : ∀ e ∈ H, (alternatives H e).Nonempty → 1 ≤ charge H e) :
    H.card ≤ 4 * (Fintype.card α) ^ 2 := by
  classical
  let active := H.filter fun e => (alternatives H e).Nonempty
  have hactive : (active.card : ℝ) ≤ 3 * (Fintype.card α : ℝ) ^ 2 := calc
    (active.card : ℝ) = ∑ _ ∈ active, (1 : ℝ) := by simp
    _ ≤ ∑ e ∈ active, charge H e := by
      apply Finset.sum_le_sum
      intro e he
      exact hpoint e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
    _ ≤ ∑ e ∈ H, charge H e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro e _ _
      exact Finset.sum_nonneg fun _ _ => by positivity
    _ ≤ _ := sum_charge_le H
  have hactive' : active.card ≤ 3 * (Fintype.card α) ^ 2 := by exact_mod_cast hactive
  have hpartition := Finset.card_filter_add_card_filter_not (s := H)
    (fun e => (alternatives H e).Nonempty)
  have hinactive := card_inactive_le H
  change active.card + (H.filter fun e => ¬ (alternatives H e).Nonempty).card = H.card at hpartition
  omega

theorem card_sum_tuple_le_of_tripartite_bound [AddGroup α] {k C : ℕ}
    (F : Finset (Sum (Fin k) (Fin 3) → α)) (hF : tupleDisjointUnionFree F)
    (hbase : ∀ H : Finset (Triple α), disjointUnionFree H →
      H.card ≤ C * (Fintype.card α) ^ 2) :
    F.card ≤ C * (Fintype.card α) ^ (k + 2) := by
  classical
  let shift (e : Sum (Fin k) (Fin 3) → α) (i : Fin k) := e (.inl i) - e (.inr 0)
  let project (e : Sum (Fin k) (Fin 3) → α) : Triple α := fun i => e (.inr i)
  have hfiber (σ : Fin k → α) :
      (F.filter fun e => shift e = σ).card ≤ C * (Fintype.card α) ^ 2 := by
    let fiber := F.filter fun e => shift e = σ
    have hcoord {e f : Sum (Fin k) (Fin 3) → α} (he : e ∈ fiber) (hf : f ∈ fiber)
        (i : Fin k) : e (.inl i) = f (.inl i) ↔ project e 0 = project f 0 := by
      have hshift := (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
      have hi := congrFun hshift i
      change e (.inl i) - project e 0 = f (.inl i) - project f 0 at hi
      constructor
      · intro h
        rw [h] at hi
        simp only [sub_eq_add_neg] at hi
        exact neg_injective (add_left_cancel hi)
      · intro h
        rw [h] at hi
        simp only [sub_eq_add_neg] at hi
        exact add_right_cancel hi
    have hinj : Set.InjOn project fiber := by
      intro e he f hf h
      funext i
      rcases i with i | i
      · exact (hcoord he hf i).mpr (congrFun h 0)
      · exact congrFun h i
    have hfree : disjointUnionFree (fiber.image project) := by
      intro E hE G hG A hA B hB HD HUnion
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hE
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hG
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
      have hd : ∀ i, e i ≠ g i := by
        intro i
        rcases i with i | i
        · exact fun hi => HD 0 ((hcoord he hg i).mp hi)
        · exact HD i
      have hu : ∀ i, (e i = a i ∧ g i = b i) ∨ (e i = b i ∧ g i = a i) := by
        intro i
        rcases i with i | i
        · rcases HUnion 0 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact Or.inl ⟨(hcoord he ha i).mpr h₁, (hcoord hg hb i).mpr h₂⟩
          · exact Or.inr ⟨(hcoord he hb i).mpr h₁, (hcoord hg ha i).mpr h₂⟩
        · exact HUnion i
      rcases hF e (Finset.mem_filter.mp he).1 g (Finset.mem_filter.mp hg).1
          a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hd hu with
          ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg project h₁, congrArg project h₂⟩
      · exact Or.inr ⟨congrArg project h₁, congrArg project h₂⟩
    rw [← Finset.card_image_of_injOn hinj]
    exact hbase _ hfree
  have hcount := Finset.card_eq_sum_card_fiberwise (s := F) (t := Finset.univ)
    (f := shift) (fun _ _ => Finset.mem_univ _)
  calc
    F.card = ∑ σ : Fin k → α, (F.filter fun e => shift e = σ).card := hcount
    _ ≤ ∑ _ : Fin k → α, C * (Fintype.card α) ^ 2 := Finset.sum_le_sum fun σ _ => hfiber σ
    _ = _ := by simp [pow_add, Nat.mul_left_comm]

theorem card_fin_tuple_le_of_tripartite_bound [AddGroup α] {k C : ℕ}
    (F : Finset (Fin (k + 3) → α)) (hF : tupleDisjointUnionFree F)
    (hbase : ∀ H : Finset (Triple α), disjointUnionFree H →
      H.card ≤ C * (Fintype.card α) ^ 2) :
    F.card ≤ C * (Fintype.card α) ^ (k + 2) := by
  classical
  let coord : Sum (Fin k) (Fin 3) ≃ Fin (k + 3) := finSumFinEquiv
  let rearrange (e : Fin (k + 3) → α) : Sum (Fin k) (Fin 3) → α := e ∘ coord
  have hinj : Function.Injective rearrange := by
    intro e f heq
    funext i
    simpa [rearrange] using congrFun heq (coord.symm i)
  have hfree : tupleDisjointUnionFree (F.image rearrange) := by
    intro E hE G hG A hA B hB HD HUnion
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hG
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
    have hd : ∀ i, e i ≠ g i := by
      intro i
      simpa [rearrange] using HD (coord.symm i)
    have hu : ∀ i, (e i = a i ∧ g i = b i) ∨ (e i = b i ∧ g i = a i) := by
      intro i
      simpa [rearrange] using HUnion (coord.symm i)
    rcases hF e he g hg a ha b hb hd hu with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨congrArg rearrange h₁, congrArg rearrange h₂⟩
    · exact Or.inr ⟨congrArg rearrange h₁, congrArg rearrange h₂⟩
  rw [← Finset.card_image_of_injective F hinj]
  exact card_sum_tuple_le_of_tripartite_bound _ hfree hbase

end Erdos643.CrudeBound

namespace Erdos643.CrudeBound

variable {α : Type*} [DecidableEq α] [Fintype α]

private theorem reciprocal_degrees_ge_one {P I : Type*} [DecidableEq P] [DecidableEq I]
    (A : Finset P) (tag : P → I) (R : P → P → Prop) (hne : A.Nonempty)
    (hsymm : ∀ ⦃p q⦄, R p q → R q p) (hdiff : ∀ p q, R p q → tag p ≠ tag q)
    (hconcentrated : ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, R p q → R p r → tag q = tag r) :
    letI : DecidableRel R := Classical.decRel _
    1 ≤ ∑ p ∈ A, 1 / (((A.filter (R p)).card : ℝ) + 1) := by
  classical
  let neighbors (p : P) := A.filter (R p)
  let weight (p : P) : ℝ := 1 / ((neighbors p).card + 1)
  change 1 ≤ ∑ p ∈ A, weight p
  by_cases he : ∃ p ∈ A, ∃ q ∈ A, R p q
  · obtain ⟨p, hp, q, hq, hpq⟩ := he
    let active (i j : I) := A.filter fun x => tag x = i ∧ ∃ y ∈ A, tag y = j ∧ R x y
    let L := active (tag p) (tag q)
    let K := active (tag q) (tag p)
    have hpL : p ∈ L := Finset.mem_filter.mpr ⟨hp, rfl, q, hq, rfl, hpq⟩
    have hqK : q ∈ K := Finset.mem_filter.mpr ⟨hq, rfl, p, hp, rfl, hsymm hpq⟩
    have hsub (i j : I) {x : P} (hx : x ∈ active i j) : neighbors x ⊆ active j i := by
      intro y hy
      obtain ⟨hxA, hxi, z, hzA, hzj, hxz⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyA, hxy⟩ := Finset.mem_filter.mp hy
      have hyj : tag y = j := (hconcentrated x hxA y hyA z hzA hxy hxz).trans hzj
      exact Finset.mem_filter.mpr ⟨hyA, hyj, x, hxA, hxi, hsymm hxy⟩
    have hcharge (i j : I) :
        ((active i j).card : ℝ) / ((active j i).card + 1) ≤
          ∑ x ∈ active i j, weight x := by
      calc
        _ = ∑ _x ∈ active i j, 1 / (((active j i).card : ℝ) + 1) := by
          simp [div_eq_mul_inv]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro x hx
          apply one_div_le_one_div_of_le (by positivity)
          gcongr
          exact hsub i j hx
    have hdis : Disjoint L K := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      exact hdiff p q hpq
        ((Finset.mem_filter.mp hx).2.1.symm.trans (Finset.mem_filter.mp hy).2.1)
    have hcover : L ∪ K ⊆ A :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have ha : (1 : ℝ) ≤ L.card := by exact_mod_cast Finset.card_pos.mpr ⟨p, hpL⟩
    have hb : (1 : ℝ) ≤ K.card := by exact_mod_cast Finset.card_pos.mpr ⟨q, hqK⟩
    let a : ℝ := L.card
    let b : ℝ := K.card
    have hpos : 0 < (a + 1) * (b + 1) := by positivity
    have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha hb
    have hfrac : 1 ≤ a / (b + 1) + b / (a + 1) := by
      calc
        (1 : ℝ) = ((a + 1) * (b + 1)) / ((a + 1) * (b + 1)) :=
          (div_self (ne_of_gt hpos)).symm
        _ ≤ (a * (a + 1) + b * (b + 1)) / ((a + 1) * (b + 1)) := by
          apply div_le_div_of_nonneg_right _ hpos.le
          nlinarith only [hab, sq_nonneg (a - b)]
        _ = _ := by
          have ha' : (a + 1) ≠ 0 := by positivity
          have hb' : (b + 1) ≠ 0 := by positivity
          field_simp
    calc
      1 ≤ a / (b + 1) + b / (a + 1) := hfrac
      _ ≤ (∑ x ∈ L, weight x) + (∑ x ∈ K, weight x) :=
        add_le_add (hcharge _ _) (hcharge _ _)
      _ = ∑ x ∈ L ∪ K, weight x := (Finset.sum_union hdis).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by
        dsimp [weight]
        positivity
  · obtain ⟨p, hp⟩ := hne
    have hempty : neighbors p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨hqA, hpq⟩ := Finset.mem_filter.mp hq
      exact he ⟨p, hp, q, hqA, hpq⟩
    calc
      1 = weight p := by simp [weight, hempty]
      _ ≤ _ := Finset.single_le_sum (f := weight) (fun _ _ => by
        dsimp [weight]
        positivity) hp

private theorem mem_alternatives_iff {H : Finset (Triple α)} {e : Triple α}
    {p : Alternative α} :
    p ∈ alternatives H e ↔ p.2 ≠ e p.1 ∧ Function.update e p.1 p.2 ∈ H := by
  simp [alternatives]

omit [DecidableEq α] [Fintype α] in
private theorem local_adj_symm {H : Finset (Triple α)} {e : Triple α}
    {p q : Alternative α} (h : localAdj H e p q) : localAdj H e q p := by
  obtain ⟨hne, hmem⟩ := h
  exact ⟨hne.symm, Function.update_comm hne _ _ _ ▸ hmem⟩

private theorem local_adj_concentrated {H : Finset (Triple α)} {e : Triple α}
    (hfree : disjointUnionFree H) {p q r : Alternative α}
    (hp : p ∈ alternatives H e) (hq : q ∈ alternatives H e) (hr : r ∈ alternatives H e)
    (hpq : localAdj H e p q) (hpr : localAdj H e p r) : q.1 = r.1 := by
  obtain ⟨hpVal, _⟩ := mem_alternatives_iff.mp hp
  obtain ⟨hqVal, hqH⟩ := mem_alternatives_iff.mp hq
  obtain ⟨hrVal, hrH⟩ := mem_alternatives_iff.mp hr
  obtain ⟨hpq, hpqH⟩ := hpq
  obtain ⟨hpr, hprH⟩ := hpr
  by_contra hqr
  have hrq : r.1 ≠ q.1 := fun h => hqr h.symm
  let qe := Function.update e q.1 q.2
  let re := Function.update e r.1 r.2
  let pqe := Function.update (Function.update e p.1 p.2) q.1 q.2
  let pre := Function.update (Function.update e p.1 p.2) r.1 r.2
  have hcases (i : Fin 3) : i = p.1 ∨ i = q.1 ∨ i = r.1 := by omega
  have hdiag : ∀ i, qe i ≠ pre i := by
    intro i
    rcases hcases i with rfl | rfl | rfl
    · simpa [qe, pre, Function.update_of_ne hpq, Function.update_of_ne hpr] using hpVal.symm
    · simpa [qe, pre, Function.update_of_ne hqr, Function.update_of_ne hpq.symm] using hqVal
    · simpa [qe, pre, Function.update_of_ne hrq] using hrVal.symm
  have hswap : ∀ i, (qe i = pqe i ∧ pre i = re i) ∨ (qe i = re i ∧ pre i = pqe i) := by
    intro i
    rcases hcases i with rfl | rfl | rfl
    · exact Or.inr (by simp [qe, re, pre, pqe, Function.update_of_ne hpq,
        Function.update_of_ne hpr])
    · exact Or.inl (by simp [qe, re, pre, pqe, Function.update_of_ne hqr,
        Function.update_of_ne hpq.symm])
    · exact Or.inl (by simp [qe, re, pre, pqe, Function.update_of_ne hrq,
        Function.update_of_ne hpr.symm])
  rcases hfree qe hqH pre hprH pqe hpqH re hrH hdiag hswap with ⟨heq, _⟩ | ⟨heq, _⟩
  · exact hpVal.symm (by simpa [qe, pqe, Function.update_of_ne hpq] using congrFun heq p.1)
  · exact hqVal (by simpa [qe, re, Function.update_of_ne hqr] using congrFun heq q.1)

private theorem one_change_of_common_link {H : Finset (Triple α)} {e u : Triple α}
    (hfree : disjointUnionFree H) (he : e ∈ H) {p : Alternative α}
    (hp : p ∈ alternatives H e)
    (hu : u ∈ commonLink H p.1 (e p.1) p.2) {j k : Fin 3}
    (hj : u j ≠ e j) (hk : u k ≠ e k) : j = k := by
  obtain ⟨hpVal, hpH⟩ := mem_alternatives_iff.mp hp
  obtain ⟨huH, hui, hpuH⟩ := Finset.mem_filter.mp hu
  change u p.1 = e p.1 at hui
  by_contra hjk
  have hjp : j ≠ p.1 := fun h => hj (h ▸ hui)
  have hkp : k ≠ p.1 := fun h => hk (h ▸ hui)
  let pe := Function.update e p.1 p.2
  let pu := Function.update u p.1 p.2
  have hcases (i : Fin 3) : i = p.1 ∨ i = j ∨ i = k := by omega
  have hdiag : ∀ i, e i ≠ pu i := by
    intro i
    rcases hcases i with rfl | rfl | rfl
    · simpa [pu] using hpVal.symm
    · simpa [pu, Function.update_of_ne hjp] using hj.symm
    · simpa [pu, Function.update_of_ne hkp] using hk.symm
  have hswap : ∀ i, (e i = u i ∧ pu i = pe i) ∨ (e i = pe i ∧ pu i = u i) := by
    intro i
    by_cases hi : i = p.1
    · subst i
      exact Or.inl (by simpa [pu, pe] using hui.symm)
    · exact Or.inr (by simp [pu, pe, Function.update_of_ne hi])
  rcases hfree e he pu hpuH u huH pe hpH hdiag hswap with ⟨heq, _⟩ | ⟨heq, _⟩
  · exact hj.symm (congrFun heq j)
  · exact hpVal.symm (by simpa [pe] using congrFun heq p.1)

/-- A common link contains the root triple and one triple for each local neighbor. -/
theorem common_link_card_eq_one_add {H : Finset (Triple α)} {e : Triple α}
    (hfree : disjointUnionFree H) (he : e ∈ H) {p : Alternative α}
    (hp : p ∈ alternatives H e) :
    letI : DecidableRel (localAdj H e) := Classical.decRel _
    (commonLink H p.1 (e p.1) p.2).card =
      ((alternatives H e).filter (localAdj H e p)).card + 1 := by
  classical
  let N := (alternatives H e).filter (localAdj H e p)
  let extend (q : Alternative α) := Function.update e q.1 q.2
  change (commonLink H p.1 (e p.1) p.2).card = N.card + 1
  have hnot : e ∉ N.image extend := by
    intro hem
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hem
    have hqVal := (mem_alternatives_iff.mp (Finset.mem_filter.mp hq).1).1
    exact hqVal (by simpa [extend] using congrFun heq q.1)
  have hinj : Set.InjOn extend N := by
    intro q hq r hr heq
    have hqVal := (mem_alternatives_iff.mp (Finset.mem_filter.mp hq).1).1
    have hcoord : q.1 = r.1 := by
      by_contra hn
      exact hqVal (by simpa [extend, Function.update_of_ne hn] using congrFun heq q.1)
    exact Prod.ext hcoord (by simpa [extend, hcoord] using congrFun heq q.1)
  have hlink : commonLink H p.1 (e p.1) p.2 = insert e (N.image extend) := by
    ext u
    constructor
    · intro hu
      by_cases hue : u = e
      · simp [hue]
      have huH := (Finset.mem_filter.mp hu).1
      have hup := (Finset.mem_filter.mp hu).2
      have hex : ∃ j, u j ≠ e j := by
        by_contra! hEq
        exact hue (funext hEq)
      obtain ⟨j, hj⟩ := hex
      let q : Alternative α := (j, u j)
      have hcoord : p.1 ≠ q.1 := by
        change p.1 ≠ j
        intro h
        exact hj (by simpa [h] using hup.1)
      have hrepresent : extend q = u := by
        funext k
        by_cases hk : k = j
        · simp [extend, q, hk]
        · change Function.update e j (u j) k = u k
          rw [Function.update_of_ne hk]
          by_contra hbad
          exact hk (one_change_of_common_link hfree he hp hu (Ne.symm hbad) hj)
      have hq : q ∈ alternatives H e := by
        refine mem_alternatives_iff.mpr ⟨hj, ?_⟩
        change extend q ∈ H
        rw [hrepresent]
        exact huH
      have hAdj : localAdj H e p q := by
        refine ⟨hcoord, ?_⟩
        rw [Function.update_comm hcoord]
        change Function.update (extend q) p.1 p.2 ∈ H
        rw [hrepresent]
        exact hup.2
      exact Finset.mem_insert_of_mem <|
        Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hAdj⟩, hrepresent⟩
    · intro hu
      rcases Finset.mem_insert.mp hu with rfl | himage
      · exact Finset.mem_filter.mpr ⟨he, rfl, (mem_alternatives_iff.mp hp).2⟩
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp himage
      obtain ⟨hqA, hqAdj⟩ := Finset.mem_filter.mp hq
      refine Finset.mem_filter.mpr
        ⟨(mem_alternatives_iff.mp hqA).2, Function.update_of_ne hqAdj.1 _ _, ?_⟩
      change Function.update (Function.update e q.1 q.2) p.1 p.2 ∈ H
      rw [← Function.update_comm hqAdj.1]
      exact hqAdj.2
  rw [hlink, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj]

/-- Each triple admitting a one-coordinate alternative contributes at least one. -/
theorem one_le_charge_of_alternative {H : Finset (Triple α)} {e : Triple α}
    (hfree : disjointUnionFree H) (he : e ∈ H) (hA : (alternatives H e).Nonempty) :
    1 ≤ charge H e := by
  classical
  have hbound := reciprocal_degrees_ge_one (alternatives H e) Prod.fst (localAdj H e) hA
    (by intro _ _ h; exact local_adj_symm h) (fun _ _ h => h.1)
    (fun _ hp _ hq _ hr hpq hpr => local_adj_concentrated hfree hp hq hr hpq hpr)
  refine hbound.trans_eq ?_
  unfold charge
  apply Finset.sum_congr rfl
  intro p hp
  rw [common_link_card_eq_one_add hfree he hp, Nat.cast_add, Nat.cast_one]

end Erdos643.CrudeBound

/- Averaging over colorings finds a large multipartite subfamily. -/

namespace Erdos643Rainbow

open Finset
open scoped BigOperators Classical

/-- Some coloring with `r` colors is injective on at least a fraction
`1 / r^r` of the edges of an `r`-uniform family. -/
theorem exists_rainbow_subfamily {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 0 < r) {H : Finset (Finset V)} (hH : H.IsUniform r) :
    ∃ c : V → Fin r, H.card ≤ (H.filter fun (E : Finset V) => Set.InjOn c (↑E : Set V)).card * r ^ r := by
  by_cases hHne : H.Nonempty
  · let n := Fintype.card V
    let X : Finset (V → Fin r) := Finset.univ
    let count (c : V → Fin r) := (H.filter fun (E : Finset V) => Set.InjOn c (↑E : Set V)).card
    have hrn : r ≤ n := by
      obtain ⟨E, hE⟩ := hHne
      rw [← hH E hE]
      exact Finset.card_le_univ _
    have rainbow_count (E : Finset V) (hE : E ∈ H) :
        r ^ (n - r) ≤ (X.filter fun c => Set.InjOn c (↑E : Set V)).card := by
      let encode : E ≃ Fin r := Finset.equivFinOfCardEq (hH E hE)
      let Outside := {x : V // x ∉ E}
      let paint (f : Outside → Fin r) (x : V) : Fin r :=
        if hx : x ∈ E then encode ⟨x, hx⟩ else f ⟨x, hx⟩
      have hOutside : Fintype.card Outside = n - r := by
        change Fintype.card {x : V // ¬ x ∈ E} = Fintype.card V - r
        rw [Fintype.card_subtype_compl, ← hH E hE, Fintype.card_coe]
      have hcard : (Finset.univ : Finset (Outside → Fin r)).card = r ^ (n - r) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hOutside]
      rw [← hcard]
      apply Finset.card_le_card_of_injOn paint
      · intro f _
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro x hx y hy heq
        change x ∈ E at hx
        change y ∈ E at hy
        have henc : encode ⟨x, hx⟩ = encode ⟨y, hy⟩ := by
          simpa only [paint, dif_pos hx, dif_pos hy] using heq
        exact congrArg Subtype.val (encode.injective henc)
      · intro f _ g _ hfg
        funext x
        simpa only [paint, dif_neg x.property] using congrFun hfg (x : V)
    have hsum : H.card * r ^ (n - r) ≤ ∑ c ∈ X, count c := by
      calc
        H.card * r ^ (n - r) = ∑ _E ∈ H, r ^ (n - r) := by simp
        _ ≤ ∑ E ∈ H, (X.filter fun c => Set.InjOn c (↑E : Set V)).card :=
          Finset.sum_le_sum rainbow_count
        _ = ∑ c ∈ X, count c := by
          simp_rw [count, Finset.card_filter]
          exact Finset.sum_comm
    have hX : X.card = r ^ r * r ^ (n - r) := by
      dsimp [X]
      rw [Fintype.card_fun, Fintype.card_fin, ← pow_add, Nat.add_sub_cancel' hrn]
    by_contra! h
    have hXne : X.Nonempty := ⟨fun _ => ⟨0, hr⟩, Finset.mem_univ _⟩
    have hlt : (∑ c ∈ X, count c * r ^ r) < ∑ _c ∈ X, H.card :=
      Finset.sum_lt_sum_of_nonempty hXne fun c _ => h c
    rw [← Finset.sum_mul, Finset.sum_const_nat (fun _ _ => rfl)] at hlt
    have hlow : X.card * H.card ≤ (∑ c ∈ X, count c) * r ^ r := by
      calc
        X.card * H.card = (H.card * r ^ (n - r)) * r ^ r := by rw [hX]; ac_rfl
        _ ≤ _ := Nat.mul_le_mul_right _ hsum
    exact (not_lt_of_ge hlow) hlt
  · exact ⟨fun _ => ⟨0, hr⟩, by simp [Finset.not_nonempty_iff_eq_empty.mp hHne]⟩

end Erdos643Rainbow

/- Encoding each rainbow edge by its unique vertex of each color. -/

namespace Erdos643RainbowTuples

open Erdos643.CrudeBound

/-- On a rainbow edge of size `r`, each of the `r` colors occurs exactly once. -/
noncomputable def colorEquivOnEdge {V : Type*} [DecidableEq V] {r : ℕ}
    (c : V → Fin r) (E : Finset V) (hEc : E.card = r) (hEr : Set.InjOn c (E : Set V)) :
    E ≃ Fin r :=
  Equiv.ofBijective (fun x : E => c x)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun x y h => Subtype.ext (hEr x.property y.property h),
        by rw [Fintype.card_coe, hEc, Fintype.card_fin]⟩)

/-- The tuple encoding preserves the number of edges and the absence of
repeated disjoint unions. The coordinates may be relabeled by an embedding. -/
theorem exists_tuple_family_of_rainbow {V W : Type*} [DecidableEq V] [DecidableEq W]
    {r : ℕ} (hr : 0 < r) (c : V → Fin r) (emb : V ↪ W) {H : Finset (Finset V)}
    (hH : H.IsUniform r) (hrainbow : ∀ E ∈ H, Set.InjOn c (E : Set V))
    (hfree : ¬ H.HasRepeatedDisjointUnion) :
    ∃ F : Finset (Fin r → W), F.card = H.card ∧ tupleDisjointUnionFree F := by
  let colors (E : H) := colorEquivOnEdge c E.1 (hH E.1 E.2) (hrainbow E.1 E.2)
  let atColor (E : H) (i : Fin r) : V := ((colors E).symm i).1
  let tuple (E : H) (i : Fin r) : W := emb (atColor E i)
  have hmem (E : H) (x : V) : x ∈ E.1 ↔ atColor E (c x) = x := by
    constructor
    · intro hx
      exact congrArg Subtype.val ((colors E).symm_apply_apply ⟨x, hx⟩)
    · intro he
      rw [← he]
      exact ((colors E).symm (c x)).property
  have hinj : Function.Injective tuple := by
    intro E D h
    apply Subtype.ext
    ext x
    simp only [hmem]
    rw [emb.injective (congrFun h (c x))]
  let F := H.attach.image tuple
  refine ⟨F, by rw [Finset.card_image_of_injective _ hinj, Finset.card_attach], ?_⟩
  intro a ha b hb d hd e he hab hmatch
  obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨E, _, rfl⟩ := Finset.mem_image.mp he
  have matching (i : Fin r) :
      (atColor A i = atColor D i ∧ atColor B i = atColor E i) ∨
      (atColor A i = atColor E i ∧ atColor B i = atColor D i) := by
    rcases hmatch i with h | h
    · exact Or.inl ⟨emb.injective h.1, emb.injective h.2⟩
    · exact Or.inr ⟨emb.injective h.1, emb.injective h.2⟩
  have hab' (i : Fin r) : atColor A i ≠ atColor B i :=
    fun heq => hab i (congrArg (fun x => emb x) heq)
  have hde' (i : Fin r) : atColor D i ≠ atColor E i := by
    intro heq
    rcases matching i with h | h
    · exact hab' i (h.1.trans (heq.trans h.2.symm))
    · exact hab' i (h.1.trans (heq.symm.trans h.2.symm))
  have disjoint_of_coordinate_ne {I J : H} (hne : ∀ i, atColor I i ≠ atColor J i) :
      Disjoint I.1 J.1 := by
    apply Finset.disjoint_left.mpr
    intro x hxI hxJ
    exact hne (c x) (((hmem I x).mp hxI).trans ((hmem J x).mp hxJ).symm)
  have habDis := disjoint_of_coordinate_ne hab'
  have hdeDis := disjoint_of_coordinate_ne hde'
  have hunion : A.1 ∪ B.1 = D.1 ∪ E.1 := by
    ext x
    simp only [Finset.mem_union, hmem]
    rcases matching (c x) with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2, or_comm]
  have disjoint_ne {I J : H} (hdis : Disjoint I.1 J.1) : I.1 ≠ J.1 := by
    intro heq
    have hx := ((colors I).symm (⟨0, hr⟩ : Fin r)).property
    exact Finset.disjoint_left.mp hdis hx (heq ▸ hx)
  have hcancel {I J K L : H} (heq : I.1 = K.1) (hIJ : Disjoint I.1 J.1)
      (hKL : Disjoint K.1 L.1) (hu : I.1 ∪ J.1 = K.1 ∪ L.1) :
      tuple I = tuple K ∧ tuple J = tuple L := by
    rw [← heq] at hu hKL
    have hdiff := congrArg (fun S : Finset V => S \ I.1) hu
    rw [Finset.union_sdiff_cancel_left hIJ, Finset.union_sdiff_cancel_left hKL] at hdiff
    exact ⟨congrArg tuple (Subtype.ext heq), congrArg tuple (Subtype.ext hdiff)⟩
  by_contra hn
  have hswapRight : A.1 ∪ B.1 = E.1 ∪ D.1 := hunion.trans (Finset.union_comm _ _)
  have hswapLeft : B.1 ∪ A.1 = D.1 ∪ E.1 := (Finset.union_comm _ _).trans hunion
  have hswapBoth : B.1 ∪ A.1 = E.1 ∪ D.1 := (Finset.union_comm _ _).trans hswapRight
  exact hfree ⟨_, A.2, _, B.2, _, D.2, _, E.2, habDis, hdeDis, hunion,
    disjoint_ne habDis, disjoint_ne hdeDis,
    fun h => hn (Or.inl (hcancel h habDis hdeDis hunion)),
    fun h => hn (Or.inr (hcancel h habDis hdeDis.symm hswapRight)),
    fun h => hn (Or.inr (hcancel h habDis.symm hdeDis hswapLeft).symm),
    fun h => hn (Or.inl (hcancel h habDis.symm hdeDis.symm hswapBoth).symm)⟩

end Erdos643RainbowTuples

/- Transfer the ambient hypergraph bound to an arbitrary finite vertex set. -/

universe u

namespace Erdos643DeficitInducedBound

/-- Restrict the ambient vertex type to `U` before applying the bound. -/
theorem induced_bound_of_ambient_bound {K : ℕ → ℕ}
    (hambient : ∀ (α : Type u) [Fintype α] [DecidableEq α],
      ∀ t : ℕ, 4 ≤ t → ∀ H : Finset (Finset α),
        H.IsUniform t → ¬ H.HasRepeatedDisjointUnion →
          H.card ≤ K t * Fintype.card α ^ (t - 1))
    {V : Type u} [DecidableEq V] {t : ℕ} (ht : 4 ≤ t)
    {U : Finset V} {G : Finset (Finset V)} (hunif : G.IsUniform t)
    (hfree : ¬ G.HasRepeatedDisjointUnion) (hU : ∀ E ∈ G, E ⊆ U) :
    G.card ≤ K t * U.card ^ (t - 1) := by
  let inclusion : U ↪ V := Function.Embedding.subtype _
  let restrictEdge (E : Finset V) : Finset U := E.subtype (· ∈ U)
  let restricted := G.image restrictEdge
  have hmap (E : Finset V) (hE : E ∈ G) : (restrictEdge E).map inclusion = E :=
    Finset.subtype_map_of_mem (fun _ hx => hU E hE hx)
  have hmem (A : Finset U) (hA : A ∈ restricted) : A.map inclusion ∈ G := by
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hA
    simpa only [hmap E hE] using hE
  have hcard : restricted.card = G.card := by
    apply Finset.card_image_of_injOn
    intro E hE F hF heq
    exact (hmap E hE).symm.trans ((congrArg (Finset.map inclusion) heq).trans (hmap F hF))
  have hunif' : restricted.IsUniform t := by
    intro A hA
    simpa only [Finset.card_map] using hunif _ (hmem A hA)
  have hfree' : ¬ restricted.HasRepeatedDisjointUnion := by
    rintro ⟨A, hA, B, hB, C, hC, D, hD, hAB, hCD, hEq, hnAB, hnCD, hnAC, hnAD, hnBC, hnBD⟩
    have hEq' : A.map inclusion ∪ B.map inclusion = C.map inclusion ∪ D.map inclusion := by
      simpa only [Finset.map_union] using congrArg (Finset.map inclusion) hEq
    have hinj := Finset.map_injective inclusion
    exact hfree ⟨_, hmem A hA, _, hmem B hB, _, hmem C hC, _, hmem D hD,
      (Finset.disjoint_map inclusion).mpr hAB, (Finset.disjoint_map inclusion).mpr hCD,
      hEq', hinj.ne hnAB, hinj.ne hnCD, hinj.ne hnAC, hinj.ne hnAD, hinj.ne hnBC, hinj.ne hnBD⟩
  simpa only [hcard, Fintype.card_coe] using hambient U t ht restricted hunif' hfree'

end Erdos643DeficitInducedBound

/- A crude ambient bound on uniform disjoint-union-free families. -/

namespace Erdos643CrudeAmbient

open Erdos643.CrudeBound

theorem card_uniform_le (V : Type*) [Fintype V] [DecidableEq V]
    (t : ℕ) (ht : 4 ≤ t) (H : Finset (Finset V))
    (hH : H.IsUniform t) (hfree : ¬ H.HasRepeatedDisjointUnion) :
    H.card ≤ (4 * t ^ t) * Fintype.card V ^ (t - 1) := by
  classical
  by_cases hne : H.Nonempty
  · obtain ⟨k, rfl⟩ : ∃ k, t = k + 3 := ⟨t - 3, by omega⟩
    let n := Fintype.card V
    have hn : n ≠ 0 := by
      obtain ⟨E, hE⟩ := hne
      have hle := Finset.card_le_univ E
      rw [hH E hE] at hle
      change k + 3 ≤ n at hle
      omega
    let _ : NeZero n := ⟨hn⟩
    let emb : V ↪ ZMod n := (Fintype.equivOfCardEq (ZMod.card n).symm).toEmbedding
    obtain ⟨c, hcount⟩ := Erdos643Rainbow.exists_rainbow_subfamily (by omega : 0 < k + 3) hH
    let G := H.filter fun (E : Finset V) => Set.InjOn c (E : Set V)
    have hG : G.IsUniform (k + 3) := fun E hE => hH E (Finset.mem_filter.mp hE).1
    have hrainbow : ∀ E ∈ G, Set.InjOn c (E : Set V) := fun _ hE => (Finset.mem_filter.mp hE).2
    have hGfree : ¬ G.HasRepeatedDisjointUnion := by
      rintro ⟨A, hA, B, hB, C, hC, D, hD, hrest⟩
      exact hfree ⟨A, (Finset.mem_filter.mp hA).1, B, (Finset.mem_filter.mp hB).1,
        C, (Finset.mem_filter.mp hC).1, D, (Finset.mem_filter.mp hD).1, hrest⟩
    obtain ⟨F, hcard, hF⟩ := Erdos643RainbowTuples.exists_tuple_family_of_rainbow
      (by omega : 0 < k + 3) c emb hG hrainbow hGfree
    have hbound : F.card ≤ 4 * n ^ (k + 2) := by
      have htup := card_fin_tuple_le_of_tripartite_bound (C := 4) F hF fun L hL =>
        card_le_of_charge_ge_one L fun _ he hA => one_le_charge_of_alternative hL he hA
      rwa [ZMod.card] at htup
    calc
      H.card ≤ G.card * (k + 3) ^ (k + 3) := hcount
      _ = F.card * (k + 3) ^ (k + 3) := by rw [hcard]
      _ ≤ (4 * n ^ (k + 2)) * (k + 3) ^ (k + 3) := Nat.mul_le_mul_right _ hbound
      _ = _ := by change _ = (4 * (k + 3) ^ (k + 3)) * n ^ (k + 2); ac_rfl
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

end Erdos643CrudeAmbient

theorem OMA.solution : OMA.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1.H2 := by
  apply Erdos643DeficitPaths.h2_of_induced_bound (K := fun t => 4 * t ^ t)
  intro t ht _n _U _G hunif hfree hU
  exact Erdos643DeficitInducedBound.induced_bound_of_ambient_bound
    Erdos643CrudeAmbient.card_uniform_le ht hunif hfree hU
