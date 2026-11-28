import OMAReductions.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1

/-! The off-star incidence proof for Erdős 643. -/

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

theorem incidence_to_exceptional_bound {n t i m q : ℕ} (ht : 4 ≤ t) (hn : 6 * t ≤ n)
    (hi : i ≤ t - 1)
    (hinc : q * (n - 2 * t).choose (t - 1 - i) ≤ 2 * m * (t - 1).choose i) :
    q * n ^ (t - 1 - i) ≤ (4 * t ^ (2 * t)) * m := by
  let r := t - 1
  let k := r - i
  let b := (n - 2 * t).choose k
  change q * b ≤ 2 * m * r.choose i at hinc
  change q * n ^ k ≤ (4 * t ^ (2 * t)) * m
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
    _ ≤ (4 * t ^ (2 * t)) * m := Nat.mul_le_mul_right m (Nat.le_mul_of_pos_left _ (by decide))

theorem exceptional_card_le_div {n c m q k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (hb : q * n ^ k ≤ c * m) : q ≤ c * m / n := by
  have hnPow : n ≤ n ^ k := by simpa using Nat.pow_le_pow_right hn hk
  exact (Nat.le_div_iff_mul_le hn).mpr ((Nat.mul_le_mul_left q hnPow).trans hb)

theorem exceptional_card_eq_zero {n c m q k : ℕ} (hn : 0 < n) (hc : 0 < c)
    (hk : 2 ≤ k) (hsmall : 4 * c ^ 2 * m ≤ n ^ 2)
    (hb : q * n ^ k ≤ c * m) : q = 0 := by
  by_contra! hq
  have hp : n ^ 2 ≤ n ^ k := Nat.pow_le_pow_right hn hk
  have hnle : n ^ 2 ≤ c * m :=
    hp.trans ((Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hq)).trans hb)
  have hmul : (4 * c) * n ^ 2 ≤ 1 * n ^ 2 := by
    calc
      _ ≤ (4 * c) * (c * m) := Nat.mul_le_mul_left _ hnle
      _ = 4 * c ^ 2 * m := by ring
      _ ≤ _ := by simpa using hsmall
  have := Nat.le_of_mul_le_mul_right hmul (pow_pos hn 2)
  omega

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

namespace Erdos643Intersections

/-- Two distinct edges outside the star can meet in at most two vertices.
For a nonempty intersection, the common-filler rule also supplies an
exceptional remainder of size `t - (A ∩ B).card`. -/
theorem intersection_card_le_two
    {V : Type*} [DecidableEq V] {F : Finset (Finset V)} {v : V} {t : ℕ}
    {Q : ℕ → Finset (Finset V)}
    (hcommon : ∀ {S T U : Finset V} {i : ℕ}, 1 ≤ i → i ≤ t - 1 →
      S.card = t - i → T.card = i → U.card = i →
      v ∉ S → v ∉ T → v ∉ U →
      Disjoint S T → Disjoint S U → Disjoint T U →
      S ∪ T ∈ F → S ∪ U ∈ F → T ∈ Q i ∨ U ∈ Q i)
    (hempty : ∀ i, 1 ≤ i → i ≤ t - 3 → Q i = ∅)
    {A B : Finset V} (hA : A ∈ F) (hB : B ∈ F) (hvA : v ∉ A) (hvB : v ∉ B)
    (hAt : A.card = t) (hBt : B.card = t) (hAB : A ≠ B) :
    (A ∩ B).card ≤ 2 ∧
      ((A ∩ B).Nonempty →
        A \ B ∈ Q (t - (A ∩ B).card) ∨ B \ A ∈ Q (t - (A ∩ B).card)) := by
  let S := A ∩ B
  let T := A \ B
  let U := B \ A
  let i := t - S.card
  change S.card ≤ 2 ∧ (S.Nonempty → T ∈ Q i ∨ U ∈ Q i)
  by_cases hS : S.Nonempty
  · have hSA : S ⊆ A := Finset.inter_subset_left
    have hSB : S ⊆ B := Finset.inter_subset_right
    have hsmall : S.card < t := by
      by_contra! h
      exact hAB ((Finset.eq_of_subset_of_card_le hSA (by omega)).symm.trans
        (Finset.eq_of_subset_of_card_le hSB (by omega)))
    have hSpos := Finset.card_pos.mpr hS
    have hi : 1 ≤ i := by dsimp [i]; omega
    have hit : i ≤ t - 1 := by dsimp [i]; omega
    have hScard : S.card = t - i := by dsimp [i]; omega
    have hTc : T.card = i := by simp [T, i, S, Finset.card_sdiff, hAt, Finset.inter_comm]
    have hUc : U.card = i := by simp [U, i, S, Finset.card_sdiff, hBt]
    have hST : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxT
      exact (Finset.mem_sdiff.mp hxT).2 (Finset.mem_inter.mp hxS).2
    have hSU : Disjoint S U := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxU
      exact (Finset.mem_sdiff.mp hxU).2 (Finset.mem_inter.mp hxS).1
    have hTU : Disjoint T U := by
      apply Finset.disjoint_left.mpr
      intro x hxT hxU
      exact (Finset.mem_sdiff.mp hxU).2 (Finset.mem_sdiff.mp hxT).1
    have hSTA : S ∪ T = A := by
      simpa [S, T, Finset.union_comm] using Finset.sdiff_union_inter A B
    have hSUB : S ∪ U = B := by
      simpa [S, U, Finset.union_comm, Finset.inter_comm] using Finset.sdiff_union_inter B A
    have hQ := hcommon hi hit hScard hTc hUc
      (fun hv => hvA (hSA hv)) (fun hv => hvA (Finset.mem_sdiff.mp hv).1)
      (fun hv => hvB (Finset.mem_sdiff.mp hv).1) hST hSU hTU
      (hSTA.symm ▸ hA) (hSUB.symm ▸ hB)
    refine ⟨?_, fun _ => hQ⟩
    by_contra! hlarge
    rw [hempty i hi (by dsimp [i]; omega)] at hQ
    simp at hQ
  · have hzero : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hS)
    exact ⟨by omega, fun h => (hS h).elim⟩

end Erdos643Intersections

namespace Erdos643

theorem card_exceptional_incidences_le
    {α : Type*} [DecidableEq α]
    (H Qbig Qsmall : Finset (Finset α)) (k : ℕ)
    (hpair : ∀ T ∈ Qbig, T.card = k → ∀ E ∈ H, ∀ F ∈ H,
      E ≠ F → T ⊆ E → T ⊆ F → E \ T ∈ Qsmall ∨ F \ T ∈ Qsmall) :
    ((H ×ˢ Qbig).filter fun p => p.2 ⊆ p.1 ∧ p.2.card = k).card ≤
      Qbig.card * (Qsmall.card + 1) := by
  let O := (H ×ˢ Qbig).filter fun p => p.2 ⊆ p.1 ∧ p.2.card = k
  let supported (p : Finset α × Finset α) : Prop := p.1 \ p.2 ∈ Qsmall
  have ho {p : Finset α × Finset α} (hp : p ∈ O) :
      p.1 ∈ H ∧ p.2 ∈ Qbig ∧ p.2 ⊆ p.1 ∧ p.2.card = k := by
    simpa only [O, Finset.mem_filter, Finset.mem_product, and_assoc] using hp
  have hgood : (O.filter supported).card ≤ (Qsmall ×ˢ Qbig).card := by
    apply Finset.card_le_card_of_injOn (fun p => (p.1 \ p.2, p.2))
    · intro p hp
      obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_product.mpr ⟨hs, (ho hp).2.1⟩
    · rintro ⟨E, T⟩ hp ⟨F, S⟩ hq heq
      have hTS : T = S := congrArg Prod.snd heq
      subst S
      have hTE := (ho (Finset.mem_filter.mp hp).1).2.2.1
      have hTF := (ho (Finset.mem_filter.mp hq).1).2.2.1
      exact Prod.ext (Finset.superset_injOn_sdiff T hTE hTF (congrArg Prod.fst heq)) rfl
  have hbad : (O.filter fun p => ¬ supported p).card ≤ Qbig.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      exact (ho (Finset.mem_filter.mp hp).1).2.1
    · rintro ⟨E, T⟩ hp ⟨F, S⟩ hq heq
      change T = S at heq
      subst S
      obtain ⟨hp, hpnot⟩ := Finset.mem_filter.mp hp
      obtain ⟨hq, hqnot⟩ := Finset.mem_filter.mp hq
      obtain ⟨hE, hT, hTE, hk⟩ := ho hp
      obtain ⟨hF, _, hTF, _⟩ := ho hq
      refine Prod.ext ?_ rfl
      by_contra hEF
      exact (hpair T hT hk E hE F hF hEF hTE hTF).elim hpnot hqnot
  calc
    O.card = (O.filter supported).card + (O.filter fun p => ¬ supported p).card :=
      (Finset.card_filter_add_card_filter_not supported).symm
    _ ≤ (Qsmall ×ˢ Qbig).card + Qbig.card := Nat.add_le_add hgood hbad
    _ = Qbig.card * (Qsmall.card + 1) := by
      rw [Finset.card_product, Nat.mul_add, Nat.mul_one, Nat.mul_comm Qsmall.card Qbig.card]

end Erdos643

namespace Erdos643OffStarLower

/-- Count off-star vertex incidences by missing links, vertices, and exceptional remainders. -/
theorem off_star_incidence_lower {α : Type*} [Fintype α] [DecidableEq α]
    (v : α) (H M Q : Finset (Finset α)) (t : ℕ) (ht : 4 ≤ t)
    (hsize : ∀ E ∈ H, E.card = t) (hoff : ∀ E ∈ H, v ∉ E)
    (hinter : ∀ E ∈ H, ∀ G ∈ H, E ≠ G → (E ∩ G).card ≤ 2)
    (hone : ∀ E ∈ H, ∀ G ∈ H, E ≠ G → ∀ x : α,
      E ∩ G = {x} → E.erase x ∈ M ∨ G.erase x ∈ M)
    (htwo : ∀ E ∈ H, ∀ G ∈ H, E ≠ G → (E ∩ G).card = 2 →
      E \ G ∈ Q ∨ G \ E ∈ Q) :
    let O := (H ×ˢ Q).filter (fun ET => ET.2 ⊆ ET.1 ∧ ET.2.card = t - 2)
    t * H.card ≤ M.card + (Fintype.card α - 1) + 2 * O.card := by
  classical
  let O := (H ×ˢ Q).filter (fun ET => ET.2 ⊆ ET.1 ∧ ET.2.card = t - 2)
  let incidences : Finset (Σ _ : Finset α, α) := H.sigma fun E => E
  let marked := incidences.filter (fun a => a.1.erase a.2 ∈ M)
  let triples : Finset (Σ _ : Finset α × Finset α, α) :=
    O.sigma fun ET => ET.1 \ ET.2
  let assigned : Finset (Σ _ : Finset α, α) :=
    triples.image (fun a => ⟨a.1.1, a.2⟩)
  let remaining := incidences.filter (fun a => a.1.erase a.2 ∉ M ∧ a ∉ assigned)
  have hincidences : incidences.card = t * H.card := by
    change (H.sigma (fun E => E)).card = _
    rw [card_sigma]
    calc
      ∑ E ∈ H, E.card = ∑ _E ∈ H, t := sum_congr rfl hsize
      _ = t * H.card := by simp [mul_comm]
  have hmarked : marked.card ≤ M.card := by
    apply card_le_card_of_injOn (fun a => a.1.erase a.2)
    · intro a ha
      exact (mem_filter.mp ha).2
    · rintro ⟨E, x⟩ ha ⟨G, y⟩ hb heq
      obtain ⟨hE, hx⟩ := mem_sigma.mp (mem_filter.mp ha).1
      obtain ⟨hG, hy⟩ := mem_sigma.mp (mem_filter.mp hb).1
      change E.erase x = G.erase y at heq
      have hEG : E = G := by
        by_contra hne
        have hsub : E.erase x ⊆ E ∩ G := by
          intro z hz
          refine mem_inter.mpr ⟨mem_of_mem_erase hz, ?_⟩
          rw [heq] at hz
          exact mem_of_mem_erase hz
        have hle := card_le_card hsub
        rw [card_erase_of_mem hx, hsize E hE] at hle
        have := hinter E hE G hG hne
        omega
      subst G
      have hxy : x = y := by
        by_contra hne
        have hs : x ∈ E.erase y := mem_erase.mpr ⟨hne, hx⟩
        rw [← heq] at hs
        exact notMem_erase x E hs
      subst y
      rfl
  have hassigned : assigned.card ≤ 2 * O.card := by
    calc
      assigned.card ≤ triples.card := card_image_le
      _ = ∑ ET ∈ O, (ET.1 \ ET.2).card := card_sigma _ _
      _ = ∑ _ET ∈ O, 2 := by
        apply sum_congr rfl
        intro ET hET
        obtain ⟨hpair, hsub, hT⟩ := mem_filter.mp hET
        rw [card_sdiff_of_subset hsub, hsize _ (mem_product.mp hpair).1, hT]
        omega
      _ = 2 * O.card := by simp [mul_comm]
  have mem_assigned_of_diff {E G : Finset α} {x : α}
      (hE : E ∈ H) (hxE : x ∈ E) (hxG : x ∈ G) (hcard : (E ∩ G).card = 2)
      (hQ : E \ G ∈ Q) : (⟨E, x⟩ : Σ _ : Finset α, α) ∈ assigned := by
    have hdiff : E \ G = E \ (E ∩ G) := by
      ext z
      simp only [mem_sdiff, mem_inter]
      tauto
    have hT : (E \ G).card = t - 2 := by
      rw [hdiff, card_sdiff_of_subset inter_subset_left, hsize E hE, hcard]
    have hpair : (E, E \ G) ∈ O := by
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hE, hQ⟩, sdiff_subset, hT⟩
    have hx : x ∈ E \ (E \ G) :=
      mem_sdiff.mpr ⟨hxE, fun hx => (mem_sdiff.mp hx).2 hxG⟩
    have htriple : (⟨(E, E \ G), x⟩ : Σ _ : Finset α × Finset α, α) ∈ triples :=
      mem_sigma.mpr ⟨hpair, hx⟩
    exact mem_image.mpr ⟨_, htriple, rfl⟩
  have hremaining : remaining.card ≤ (Fintype.card α - 1) := by
    rw [← card_univ, ← card_erase_of_mem (mem_univ v)]
    apply card_le_card_of_injOn (fun a => a.2)
    · intro a ha
      obtain ⟨hE, hx⟩ := mem_sigma.mp (mem_filter.mp ha).1
      exact mem_erase.mpr ⟨fun heq => hoff _ hE (heq ▸ hx), mem_univ _⟩
    · rintro ⟨E, x⟩ ha ⟨G, y⟩ hb heq
      change x = y at heq
      subst y
      obtain ⟨ha, hEa, hAa⟩ := mem_filter.mp ha
      obtain ⟨hb, hEb, hAb⟩ := mem_filter.mp hb
      obtain ⟨hE, hxE⟩ := mem_sigma.mp ha
      obtain ⟨hG, hxG⟩ := mem_sigma.mp hb
      suffices E = G by subst G; rfl
      by_contra hne
      have hx : x ∈ E ∩ G := mem_inter.mpr ⟨hxE, hxG⟩
      have hpos : 0 < (E ∩ G).card := card_pos.mpr ⟨x, hx⟩
      have hle := hinter E hE G hG hne
      by_cases hcard : (E ∩ G).card = 1
      · have heq : E ∩ G = {x} := by
          symm
          apply eq_of_subset_of_card_le (singleton_subset_iff.mpr hx)
          simp [hcard]
        exact (hone E hE G hG hne x heq).elim hEa hEb
      · have hcard₂ : (E ∩ G).card = 2 := by omega
        rcases htwo E hE G hG hne hcard₂ with hQ | hQ
        · exact hAa (mem_assigned_of_diff hE hxE hxG hcard₂ hQ)
        · exact hAb (mem_assigned_of_diff hG hxG hxE (by rwa [inter_comm]) hQ)
  have hcover : incidences ⊆ marked ∪ remaining ∪ assigned := by
    intro a ha
    by_cases hm : a.1.erase a.2 ∈ M
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨ha, hm⟩))
    by_cases hA : a ∈ assigned
    · exact mem_union_right _ hA
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨ha, hm, hA⟩))
  calc
    t * H.card = incidences.card := hincidences.symm
    _ ≤ (marked ∪ remaining ∪ assigned).card := card_le_card hcover
    _ ≤ (marked ∪ remaining).card + assigned.card := card_union_le _ _
    _ ≤ M.card + (Fintype.card α - 1) + 2 * O.card := by
      have := card_union_le marked remaining
      omega

end Erdos643OffStarLower

namespace Erdos643OffStarProof

open Erdos643StarLinks
open Erdos643CommonFiller
open Erdos643ExceptionalBounds

theorem off_star_bound {n t : ℕ} (ht : 4 ≤ t) (hn : 6 * t ≤ n)
    (F : Finset (Finset (Fin n))) (hF : F.IsUniform t) (hfree : ¬ F.HasRepeatedDisjointUnion)
    (v : Fin n)
    (hsmall : 4 * (4 * t ^ (2 * t)) ^ 2 *
      ((n - 1).choose (t - 1) - (F.filter (fun e => v ∈ e)).card) ≤ n ^ 2) :
    let m := (n - 1).choose (t - 1) - (F.filter (fun e => v ∈ e)).card
    let c := 4 * t ^ (2 * t)
    let k := c * m / n
    t * (F.filter (fun e => v ∉ e)).card ≤ m + (n - 1) + 2 * k * (k + 1) := by
  let H := F.filter (fun e => v ∉ e)
  let M := missingLinks F v t
  let Q := exceptional F v t
  let m := (n - 1).choose (t - 1) - (F.filter (fun e => v ∈ e)).card
  let c := 4 * t ^ (2 * t)
  let k := c * m / n
  let O := (H ×ˢ Q (t - 2)).filter (fun ET => ET.2 ⊆ ET.1 ∧ ET.2.card = t - 2)
  change 4 * c ^ 2 * m ≤ n ^ 2 at hsmall
  have hnpos : 0 < n := by omega
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hmcard : M.card = m := by simpa [M, m] using missing_card v hF
  have hQbound (i : ℕ) (hi : i ≤ t - 1) :
      (Q i).card * n ^ (t - 1 - i) ≤ c * m := by
    have hinc : (Q i).card * (n - 2 * t).choose (t - 1 - i) ≤
        2 * M.card * (t - 1).choose i := by
      apply exceptional_card_bound (missing_uniform F v t) (exceptional_uniform F v t i)
      intro T hT
      simpa only [Fintype.card_fin] using (Finset.mem_filter.mp hT).2
    rw [hmcard] at hinc
    exact incidence_to_exceptional_bound ht hn hi hinc
  have hempty (i : ℕ) (_ : 1 ≤ i) (hi : i ≤ t - 3) : Q i = ∅ := by
    apply Finset.card_eq_zero.mp
    exact exceptional_card_eq_zero hnpos hcpos (by omega) hsmall (hQbound i (by omega))
  have hQsm : (Q 2).card ≤ k :=
    exceptional_card_le_div hnpos (by omega) (hQbound 2 (by omega))
  have hQbg : (Q (t - 2)).card ≤ k :=
    exceptional_card_le_div hnpos (by omega) (hQbound (t - 2) (by omega))
  have hcommon {S T U : Finset (Fin n)} {i : ℕ} (hi : 1 ≤ i) (hit : i ≤ t - 1)
      (hS : S.card = t - i) (hT : T.card = i) (hU : U.card = i)
      (hvS : v ∉ S) (hvT : v ∉ T) (hvU : v ∉ U)
      (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
      (hA : S ∪ T ∈ F) (hC : S ∪ U ∈ F) : T ∈ Q i ∨ U ∈ Q i := by
    have base {R : Finset (Fin n)} (hvR : v ∉ R) (hR : R.card = i) : R ∈ starLinks v i := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, hR⟩
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact hvR hx
    rcases disjoint_remainders_force_exceptional hi hit hS hT hU hvS hvT hvU
      hST hSU hTU hfree hA hC with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨base hvT hT, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨base hvU hU, h⟩)
  have hsize (E) (hE : E ∈ H) : E.card = t := hF E (Finset.mem_filter.mp hE).1
  have hoff (E) (hE : E ∈ H) : v ∉ E := (Finset.mem_filter.mp hE).2
  have hpair (E) (hE : E ∈ H) (G) (hG : G ∈ H) (hEG : E ≠ G) :
      (E ∩ G).card ≤ 2 ∧ ((E ∩ G).Nonempty →
        E \ G ∈ Q (t - (E ∩ G).card) ∨ G \ E ∈ Q (t - (E ∩ G).card)) :=
    Erdos643Intersections.intersection_card_le_two hcommon hempty
      (Finset.mem_filter.mp hE).1 (Finset.mem_filter.mp hG).1
      (hoff E hE) (hoff G hG) (hsize E hE) (hsize G hG) hEG
  have hinter (E) (hE : E ∈ H) (G) (hG : G ∈ H) (hEG : E ≠ G) :
      (E ∩ G).card ≤ 2 :=
    (hpair E hE G hG hEG).1
  have hone (E) (hE : E ∈ H) (G) (hG : G ∈ H) (hEG : E ≠ G) (x : Fin n)
      (hInt : E ∩ G = {x}) : E.erase x ∈ M ∨ G.erase x ∈ M := by
    have hne : (E ∩ G).Nonempty := hInt ▸ Finset.singleton_nonempty _
    have h := (hpair E hE G hG hEG).2 hne
    have hEerase : E \ G = E.erase x := by
      rw [← Finset.sdiff_inter_self_left E G, hInt, Finset.sdiff_singleton_eq_erase]
    have hGerase : G \ E = G.erase x := by
      rw [← Finset.sdiff_inter_self_right G E, hInt, Finset.sdiff_singleton_eq_erase]
    have hQM : Q (t - 1) = M := exceptional_full_eq_missing F v t
    rw [hInt, Finset.card_singleton, hEerase, hGerase, hQM] at h
    exact h
  have htwo (E) (hE : E ∈ H) (G) (hG : G ∈ H) (hEG : E ≠ G)
      (hInt : (E ∩ G).card = 2) : E \ G ∈ Q (t - 2) ∨ G \ E ∈ Q (t - 2) := by
    have hne : (E ∩ G).Nonempty := Finset.card_pos.mp (by omega)
    simpa only [hInt] using (hpair E hE G hG hEG).2 hne
  have hlo : t * H.card ≤ M.card + (n - 1) + 2 * O.card := by
    simpa only [Fintype.card_fin] using
      Erdos643OffStarLower.off_star_incidence_lower v H M (Q (t - 2)) t ht hsize hoff hinter hone htwo
  have hup : O.card ≤ (Q (t - 2)).card * ((Q 2).card + 1) := by
    apply Erdos643.card_exceptional_incidences_le H (Q (t - 2)) (Q 2) (t - 2)
    intro T _ hT E hE G hG hEG hTE hTG
    have hTI : T ⊆ E ∩ G := Finset.subset_inter hTE hTG
    have hcard := hinter E hE G hG hEG
    have hEq : T = E ∩ G := Finset.eq_of_subset_of_card_le hTI (by omega)
    have hne : (E ∩ G).Nonempty := by rw [← hEq]; exact Finset.card_pos.mp (by omega)
    have hr := (hpair E hE G hG hEG).2 hne
    have hindex : t - (E ∩ G).card = 2 := by rw [← hEq, hT]; omega
    rw [hindex] at hr
    simpa only [hEq, Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right] using hr
  have hquot : O.card ≤ k * (k + 1) := hup.trans (Nat.mul_le_mul hQbg (Nat.add_le_add_right hQsm 1))
  change t * H.card ≤ m + (n - 1) + 2 * k * (k + 1)
  rw [hmcard] at hlo
  rw [Nat.mul_assoc]
  exact hlo.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hquot) _)

end Erdos643OffStarProof

open Filter

theorem OMA.solution : OMA.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1.H3 := by
  intro t ht
  filter_upwards [eventually_ge_atTop (6 * t)] with n hn
  intro F hF hfree v
  exact Erdos643OffStarProof.off_star_bound ht hn F hF hfree v
