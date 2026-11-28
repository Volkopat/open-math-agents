import OMAStatements.S_oeis_a057886
import Mathlib

namespace OMA.Helpers_a057886

open OMA.S_oeis_a057886 Finset

section GF
open PowerSeries
lemma geomPS (m : ℕ) : (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) = (1 - X ^ m) * PowerSeries.mk 1 := by
  have h1 : (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) * (1 - X) = 1 - X ^ m := by
    have := geom_sum_mul (X : PowerSeries ℤ) m
    linear_combination -this
  calc (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t)
      = (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) * ((1 - X) * PowerSeries.mk 1) := by
        rw [mul_comm (1 - X), mk_one_mul_one_sub_eq_one, mul_one]
    _ = (1 - X ^ m) * PowerSeries.mk 1 := by rw [← mul_assoc, h1]

lemma card_eq_coeff (k m N : ℕ) :
    ((#{f ∈ Fintype.piFinset (fun _ : Fin k => range m) | ∑ i, f i = N} : ℕ) : ℤ) =
      coeff N ((∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) ^ k) := by
  have : (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) ^ k =
      ∏ _i : Fin k, ∑ t ∈ range m, (X : PowerSeries ℤ) ^ t := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [this, Finset.prod_univ_sum]
  simp_rw [Finset.prod_pow_eq_pow_sum, map_sum, coeff_X_pow]
  rw [Finset.sum_boole]
  congr 2
  ext f; simp [eq_comm]

lemma coeff_geom_pow (k m N : ℕ) :
    coeff N ((∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) ^ (k + 1)) =
      ∑ j ∈ range (k + 2), (-1 : ℤ) ^ j * ((k + 1).choose j : ℤ) *
        (if m * j ≤ N then ((N - m * j + k).choose k : ℤ) else 0) := by
  rw [geomPS, mul_pow, mk_one_pow_eq_mk_choose_add, sub_eq_add_neg, add_comm, add_pow,
    Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [one_pow, mul_one, neg_pow, ← pow_mul]
  have : ((-1 : PowerSeries ℤ) ^ j * X ^ (m * j) * ((k + 1).choose j : PowerSeries ℤ) *
      PowerSeries.mk fun n => ((k + n).choose k : ℤ)) =
      X ^ (m * j) * (C ((-1 : ℤ) ^ j * ((k + 1).choose j : ℤ)) *
        PowerSeries.mk fun n => ((k + n).choose k : ℤ)) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [this, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_C_mul, PowerSeries.coeff_mk, Nat.add_comm k (N - m * j)]
  · simp

end GF

lemma nd_iff (f : Fin 4 → ℕ) :
    (∀ i, f i < ∑ j ∈ univ.erase i, f j) ↔ ∀ i, 2 * f i < ∑ j, f j := by
  refine forall_congr' fun i => ?_
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]; omega

lemma Lext {n : ℕ} (f g : Quad n) : f = g ↔ ∀ i, f.1 i = g.1 i :=
  ⟨fun h i => h ▸ rfl, fun h => Subtype.ext (funext h)⟩

/-- transport a quadrilateral along a permutation of the positions -/
def perm (n : ℕ) (σ : Equiv.Perm (Fin 4)) (f : Quad n) : Quad n :=
  ⟨fun i => f.1 (σ i), by
    obtain ⟨hp, hs, hnd⟩ := f.2
    have hsum : ∑ i, f.1 (σ i) = ∑ i, f.1 i := Equiv.sum_comp σ f.1
    refine ⟨fun i => hp _, hsum.trans hs, ?_⟩
    rw [nd_iff, hsum]
    rw [nd_iff] at hnd
    exact fun i => hnd _⟩

noncomputable def e : ZMod 4 ≃+* Fin 4 := (ZMod.finEquiv 4).symm

noncomputable def act (n : ℕ) : DihedralGroup 4 → Quad n → Quad n
  | DihedralGroup.r k, f => perm n (Equiv.addRight (e k)) f
  | DihedralGroup.sr k, f => perm n (Equiv.subLeft (e k)) f

noncomputable instance instAct (n : ℕ) : MulAction (DihedralGroup 4) (Quad n) where
  smul := act n
  one_smul f := (Lext _ _).2 fun i => by
    show f.1 (i + e 0) = f.1 i
    rw [map_zero, add_zero]
  mul_smul g h f := by
    rcases g with a | a <;> rcases h with b | b <;> refine (Lext _ _).2 fun i => ?_
    · show f.1 (i + e (a + b)) = f.1 (i + e a + e b)
      rw [map_add, add_assoc]
    · show f.1 (e (b - a) - i) = f.1 (e b - (i + e a))
      rw [map_sub]; congr 1; abel
    · show f.1 (e (a + b) - i) = f.1 (e a - i + e b)
      rw [map_add]; congr 1; abel
    · show f.1 (i + e (b - a)) = f.1 (e b - (e a - i))
      rw [map_sub]; congr 1; abel

lemma smul_r (n : ℕ) (k : ZMod 4) (f : Quad n) (i : Fin 4) :
    (DihedralGroup.r k • f).1 i = f.1 (i + e k) := rfl

lemma smul_sr (n : ℕ) (k : ZMod 4) (f : Quad n) (i : Fin 4) :
    (DihedralGroup.sr k • f).1 i = f.1 (e k - i) := rfl

lemma a_eq (n : ℕ) : a n = Nat.card (MulAction.orbitRel.Quotient (DihedralGroup 4) (Quad n)) := by
  unfold a
  refine Nat.card_congr (Quot.congrRight fun f g => ?_)
  show SameQuad n f g ↔ f ∈ MulAction.orbit (DihedralGroup 4) g
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨r, hr | hr⟩
    · refine ⟨DihedralGroup.r (e.symm (-r)), (Lext _ _).2 fun i => ?_⟩
      rw [smul_r, hr, RingEquiv.apply_symm_apply]; simp
    · refine ⟨DihedralGroup.sr (e.symm r), (Lext _ _).2 fun i => ?_⟩
      rw [smul_sr, hr, RingEquiv.apply_symm_apply]; simp
  · rintro ⟨g, rfl⟩
    rcases g with k | k
    · exact ⟨-e k, Or.inl fun i => by rw [smul_r]; simp⟩
    · exact ⟨e k, Or.inr fun i => by rw [smul_sr]; simp⟩

/-- the finset model of `Quad n` -/
def SS (n : ℕ) : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ : Fin 4 => range (n + 1))

def good (n : ℕ) (f : Fin 4 → ℕ) : Prop := (∀ i, 0 < f i) ∧ ∑ i, f i = n ∧ ∀ i, 2 * f i < n

instance (n : ℕ) (f : Fin 4 → ℕ) : Decidable (good n f) := by unfold good; infer_instance

lemma quad_iff (n : ℕ) (f : Fin 4 → ℕ) :
    ((∀ i, 0 < f i) ∧ ∑ i, f i = n ∧ ∀ i, f i < ∑ j ∈ univ.erase i, f j) ↔ f ∈ SS n ∧ good n f := by
  rw [nd_iff]
  constructor
  · rintro ⟨hp, hs, hnd⟩
    refine ⟨?_, hp, hs, by rw [← hs]; exact hnd⟩
    simp only [SS, Fintype.mem_piFinset, mem_range]
    intro i
    have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  · rintro ⟨-, hp, hs, hnd⟩
    exact ⟨hp, hs, by rw [hs]; exact hnd⟩

noncomputable instance instFin (n : ℕ) : Fintype (Quad n) := by
  unfold Quad
  exact Fintype.subtype ((SS n).filter (good n)) (by intro f; rw [mem_filter, quad_iff])

lemma card_sub (n : ℕ) (P : (Fin 4 → ℕ) → Prop) [DecidablePred P] :
    Nat.card {f : Quad n // P f.1} = #{f ∈ SS n | good n f ∧ P f} := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (Equiv.subtypeEquivRight fun f => ?_))
  rw [mem_filter, quad_iff]; tauto

lemma fix_r (n : ℕ) (j : Fin 4) :
    Nat.card (MulAction.fixedBy (Quad n) (DihedralGroup.r (e.symm j))) =
      #{f ∈ SS n | good n f ∧ ∀ i, f (i + j) = f i} := by
  rw [← card_sub]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  rw [MulAction.mem_fixedBy, Lext]
  simp only [smul_r, RingEquiv.apply_symm_apply]

lemma fix_sr (n : ℕ) (j : Fin 4) :
    Nat.card (MulAction.fixedBy (Quad n) (DihedralGroup.sr (e.symm j))) =
      #{f ∈ SS n | good n f ∧ ∀ i, f (j - i) = f i} := by
  rw [← card_sub]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  rw [MulAction.mem_fixedBy, Lext]
  simp only [smul_sr, RingEquiv.apply_symm_apply]

lemma sum_D4 (F : DihedralGroup 4 → ℕ) :
    ∑ g, F g = ∑ j : Fin 4, F (DihedralGroup.r (e.symm j)) +
      ∑ j : Fin 4, F (DihedralGroup.sr (e.symm j)) := by
  rw [← DihedralGroup.equivSum.symm.sum_comp, Fintype.sum_sum_type]
  congr 1

lemma burnside (n : ℕ) :
    ∑ g : DihedralGroup 4, Nat.card (MulAction.fixedBy (Quad n) g) = a n * 8 := by
  classical
  have := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup 4) (Quad n)
  simp only [← Nat.card_eq_fintype_card] at this
  rw [this, a_eq, DihedralGroup.nat_card]

def Eset (n : ℕ) : Finset ℕ := (Icc 1 (n / 2 - 1)).filter (fun _ => n % 2 = 0)

def Vset (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1)) ×ˢ (range (n + 1))).filter (fun p => 0 < p.1 ∧ 0 < p.2.1 ∧
    0 < p.2.2 ∧ p.1 + 2 * p.2.1 + p.2.2 = n ∧ 2 * p.1 < n ∧ 2 * p.2.2 < n)

lemma mem_SS_good (n : ℕ) (f : Fin 4 → ℕ) : f ∈ SS n ∧ good n f ↔
    ((f 0 ≤ n ∧ f 1 ≤ n ∧ f 2 ≤ n ∧ f 3 ≤ n) ∧ (0 < f 0 ∧ 0 < f 1 ∧ 0 < f 2 ∧ 0 < f 3) ∧
      f 0 + f 1 + f 2 + f 3 = n ∧ (2 * f 0 < n ∧ 2 * f 1 < n ∧ 2 * f 2 < n ∧ 2 * f 3 < n)) := by
  simp only [SS, good, Fintype.mem_piFinset, mem_range, Fin.forall_fin_succ, Fin.sum_univ_four,
    Fin.isValue, IsEmpty.forall_iff, and_true, Nat.lt_succ_iff]
  rfl

lemma fixT (n : ℕ) : #{f ∈ SS n | good n f ∧ ∀ i, f (i + 0) = f i} = #{f ∈ SS n | good n f} := by
  congr 1; ext f; simp


def Cset (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun c => 4 * c = n)

lemma fixR1 (n : ℕ) : #{f ∈ SS n | good n f ∧ ∀ i, f (i + 1) = f i} = #(Cset n) := by
  refine Finset.card_nbij' (fun f => f 0) (fun p => ![p, p, p, p]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 1 = f 0 := h 0; have h1 : f 2 = f 1 := h 1; have h2 : f 3 = f 2 := h 2; have h3 : f 0 = f 3 := h 3
    simp only [Cset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range]
    omega
  · intro p hp
    simp only [Cset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range] at hp
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨((mem_SS_good n _).2 ?_).1, ((mem_SS_good n _).2 ?_).2, fun i => ?_⟩
    · simp; omega
    · simp; omega
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 1 = f 0 := h 0; have h1 : f 2 = f 1 := h 1; have h2 : f 3 = f 2 := h 2; have h3 : f 0 = f 3 := h 3
    funext i; fin_cases i <;> simp <;> omega
  · intro p hp
    simp

lemma fixR3 (n : ℕ) : #{f ∈ SS n | good n f ∧ ∀ i, f (i + 3) = f i} = #(Cset n) := by
  refine Finset.card_nbij' (fun f => f 0) (fun p => ![p, p, p, p]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 3 = f 0 := h 0; have h1 : f 0 = f 1 := h 1; have h2 : f 1 = f 2 := h 2; have h3 : f 2 = f 3 := h 3
    simp only [Cset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range]
    omega
  · intro p hp
    simp only [Cset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range] at hp
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨((mem_SS_good n _).2 ?_).1, ((mem_SS_good n _).2 ?_).2, fun i => ?_⟩
    · simp; omega
    · simp; omega
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 3 = f 0 := h 0; have h1 : f 0 = f 1 := h 1; have h2 : f 1 = f 2 := h 2; have h3 : f 2 = f 3 := h 3
    funext i; fin_cases i <;> simp <;> omega
  · intro p hp
    simp

lemma fixR2 (n : ℕ) : #{f ∈ SS n | good n f ∧ ∀ i, f (i + 2) = f i} = #(Eset n) := by
  refine Finset.card_nbij' (fun f => f 0) (fun p => ![p, n / 2 - p, p, n / 2 - p]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 2 = f 0 := h 0; have h1 : f 3 = f 1 := h 1; have h2 : f 0 = f 2 := h 2; have h3 : f 1 = f 3 := h 3
    simp only [Eset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range]
    omega
  · intro p hp
    simp only [Eset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range] at hp
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨((mem_SS_good n _).2 ?_).1, ((mem_SS_good n _).2 ?_).2, fun i => ?_⟩
    · simp; omega
    · simp; omega
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 2 = f 0 := h 0; have h1 : f 3 = f 1 := h 1; have h2 : f 0 = f 2 := h 2; have h3 : f 1 = f 3 := h 3
    funext i; fin_cases i <;> simp <;> omega
  · intro p hp
    simp

lemma fixS1 (n : ℕ) : #{f ∈ SS n | good n f ∧ ∀ i, f (1 - i) = f i} = #(Eset n) := by
  refine Finset.card_nbij' (fun f => f 0) (fun p => ![p, p, n / 2 - p, n / 2 - p]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 1 = f 0 := h 0; have h1 : f 0 = f 1 := h 1; have h2 : f 3 = f 2 := h 2; have h3 : f 2 = f 3 := h 3
    simp only [Eset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range]
    omega
  · intro p hp
    simp only [Eset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range] at hp
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨((mem_SS_good n _).2 ?_).1, ((mem_SS_good n _).2 ?_).2, fun i => ?_⟩
    · simp; omega
    · simp; omega
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 1 = f 0 := h 0; have h1 : f 0 = f 1 := h 1; have h2 : f 3 = f 2 := h 2; have h3 : f 2 = f 3 := h 3
    funext i; fin_cases i <;> simp <;> omega
  · intro p hp
    simp

lemma fixS3 (n : ℕ) : #{f ∈ SS n | good n f ∧ ∀ i, f (3 - i) = f i} = #(Eset n) := by
  refine Finset.card_nbij' (fun f => f 0) (fun p => ![p, n / 2 - p, n / 2 - p, p]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 3 = f 0 := h 0; have h1 : f 2 = f 1 := h 1; have h2 : f 1 = f 2 := h 2; have h3 : f 0 = f 3 := h 3
    simp only [Eset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range]
    omega
  · intro p hp
    simp only [Eset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range] at hp
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨((mem_SS_good n _).2 ?_).1, ((mem_SS_good n _).2 ?_).2, fun i => ?_⟩
    · simp; omega
    · simp; omega
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 3 = f 0 := h 0; have h1 : f 2 = f 1 := h 1; have h2 : f 1 = f 2 := h 2; have h3 : f 0 = f 3 := h 3
    funext i; fin_cases i <;> simp <;> omega
  · intro p hp
    simp

lemma fixS0 (n : ℕ) : #{f ∈ SS n | good n f ∧ ∀ i, f (0 - i) = f i} = #(Vset n) := by
  refine Finset.card_nbij' (fun f => (f 0, f 1, f 2)) (fun p => ![p.1, p.2.1, p.2.2, p.2.1]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 0 = f 0 := h 0; have h1 : f 3 = f 1 := h 1; have h2 : f 2 = f 2 := h 2; have h3 : f 1 = f 3 := h 3
    simp only [Vset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range]
    omega
  · intro p hp
    simp only [Vset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range] at hp
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨((mem_SS_good n _).2 ?_).1, ((mem_SS_good n _).2 ?_).2, fun i => ?_⟩
    · simp; omega
    · simp; omega
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 0 = f 0 := h 0; have h1 : f 3 = f 1 := h 1; have h2 : f 2 = f 2 := h 2; have h3 : f 1 = f 3 := h 3
    funext i; fin_cases i <;> simp <;> omega
  · intro p hp
    simp

lemma fixS2 (n : ℕ) : #{f ∈ SS n | good n f ∧ ∀ i, f (2 - i) = f i} = #(Vset n) := by
  refine Finset.card_nbij' (fun f => (f 1, f 0, f 3)) (fun p => ![p.2.1, p.1, p.2.1, p.2.2]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 2 = f 0 := h 0; have h1 : f 1 = f 1 := h 1; have h2 : f 0 = f 2 := h 2; have h3 : f 3 = f 3 := h 3
    simp only [Vset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range]
    omega
  · intro p hp
    simp only [Vset, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_product, mem_range] at hp
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨((mem_SS_good n _).2 ?_).1, ((mem_SS_good n _).2 ?_).2, fun i => ?_⟩
    · simp; omega
    · simp; omega
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    obtain ⟨hm, hg, h⟩ := hf
    have hc := (mem_SS_good n f).1 ⟨hm, hg⟩
    have h0 : f 2 = f 0 := h 0; have h1 : f 1 = f 1 := h 1; have h2 : f 0 = f 2 := h 2; have h3 : f 3 = f 3 := h 3
    funext i; fin_cases i <;> simp <;> omega
  · intro p hp
    simp

lemma card_C (n : ℕ) : #(Cset n) = if 4 ∣ n ∧ 0 < n then 1 else 0 := by
  split_ifs with h
  · obtain ⟨⟨c, rfl⟩, hpos⟩ := h
    rw [Finset.card_eq_one]; refine ⟨c, ?_⟩
    ext x; simp only [Cset, mem_filter, mem_Icc, mem_singleton]; omega
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx; simp only [Cset, mem_filter, mem_Icc] at hx
    exact h ⟨⟨x, by omega⟩, by omega⟩

lemma card_E (n : ℕ) : #(Eset n) = if n % 2 = 0 then n / 2 - 1 else 0 := by
  unfold Eset
  split_ifs with h
  · rw [Finset.filter_true_of_mem (fun _ _ => h), Nat.card_Icc]; omega
  · rw [Finset.filter_false_of_mem (fun _ _ => h)]; rfl

/-- `T n`: compositions of `n` into 4 parts each below `n / 2`. -/
lemma card_T (n : ℕ) (hn : 4 ≤ n) : #{f ∈ SS n | good n f} =
    #{g ∈ Fintype.piFinset (fun _ : Fin 4 => range ((n - 1) / 2)) | ∑ i, g i = n - 4} := by
  refine Finset.card_nbij' (fun f i => f i - 1) (fun g i => g i + 1) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    have hc := (mem_SS_good n f).1 hf
    simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_range, Fin.sum_univ_four]
    refine ⟨fun i => ?_, by omega⟩
    fin_cases i <;> simp <;> omega
  · intro g hg
    simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_range, Fin.sum_univ_four] at hg
    simp only [coe_filter, Set.mem_ofPred_eq]
    have h0 := hg.1 0; have h1 := hg.1 1; have h2 := hg.1 2; have h3 := hg.1 3
    refine (mem_SS_good n _).2 ?_
    omega
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    have hc := (mem_SS_good n f).1 hf
    funext i; fin_cases i <;> simp <;> omega
  · intro g hg; funext i; simp

lemma choose_three (b : ℕ) : ((b.choose 3 : ℕ) : ℚ) = b * (b - 1) * (b - 2) / 6 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose b 3
  have h2 := descPochhammer_eval_eq_descFactorial ℚ b 3
  rw [h, Nat.cast_mul] at h2
  simp [descPochhammer_succ_right, Nat.factorial] at h2
  linear_combination -h2 / 6

lemma T_val (n : ℕ) (hn : 4 ≤ n) : ((#{f ∈ SS n | good n f} : ℕ) : ℚ) =
    ((n - 1).choose 3 : ℚ) - 4 * ((n - 1 - (n - 1) / 2).choose 3 : ℚ) := by
  rw [card_T n hn]
  have h := card_eq_coeff 4 ((n - 1) / 2) (n - 4)
  rw [coeff_geom_pow 3] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [if_pos (show (n - 1) / 2 * 0 ≤ n - 4 by omega),
    if_neg (show ¬ ((n - 1) / 2 * 2 ≤ n - 4) by omega),
    if_neg (show ¬ ((n - 1) / 2 * 3 ≤ n - 4) by omega),
    if_neg (show ¬ ((n - 1) / 2 * (3 + 1) ≤ n - 4) by omega)] at h
  rw [show n - 4 - (n - 1) / 2 * 0 + 3 = n - 1 by omega] at h
  have h' : (((#{g ∈ Fintype.piFinset (fun _ : Fin 4 => range ((n - 1) / 2)) | ∑ i, g i = n - 4} : ℕ) : ℤ) : ℚ)
      = _ := congrArg (fun x : ℤ => (x : ℚ)) h
  push_cast at h'
  rw [h']
  simp only [show (3+1).choose 0 = 1 from rfl, show (3+1).choose 1 = 4 from rfl]
  split_ifs with hg
  · rw [show n - 4 - (n - 1) / 2 * 1 + 3 = n - 1 - (n - 1) / 2 by omega]; push_cast; ring
  · rw [Nat.choose_eq_zero_of_lt (show n - 1 - (n - 1) / 2 < 3 by omega)]; push_cast; ring


lemma V_fiber (n : ℕ) (hn : 4 ≤ n) (b : ℕ) (hb : b ∈ range ((n - 4) / 2 + 1)) :
    #{p ∈ Vset n | p.2.1 - 1 = b} =
      #{g ∈ Fintype.piFinset (fun _ : Fin 2 => range ((n - 1) / 2)) | ∑ i, g i = n - 4 - 2 * b} := by
  simp only [mem_range] at hb
  refine Finset.card_nbij' (fun p => ![p.1 - 1, p.2.2 - 1]) (fun g => (g 0 + 1, b + 1, g 1 + 1))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Vset, coe_filter, Set.mem_ofPred_eq, mem_filter, mem_product, mem_range] at hp
    simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_range, Fin.sum_univ_two]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp <;> omega
    · simp; omega
  · intro g hg
    simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_range, Fin.sum_univ_two] at hg
    have h0 := hg.1 0; have h1 := hg.1 1
    simp only [Vset, coe_filter, Set.mem_ofPred_eq, mem_filter, mem_product, mem_range]
    omega
  · intro p hp
    simp only [Vset, coe_filter, Set.mem_ofPred_eq, mem_filter, mem_product, mem_range] at hp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ext <;> simp <;> omega
  · intro g hg
    funext i; fin_cases i <;> simp

lemma V_sum (n : ℕ) (hn : 4 ≤ n) : #(Vset n) = ∑ b ∈ range ((n - 4) / 2 + 1),
    #{g ∈ Fintype.piFinset (fun _ : Fin 2 => range ((n - 1) / 2)) | ∑ i, g i = n - 4 - 2 * b} := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ × ℕ => p.2.1 - 1)
    (t := range ((n - 4) / 2 + 1))]
  · exact Finset.sum_congr rfl fun b hb => V_fiber n hn b hb
  · intro p hp
    have h := (mem_filter.1 hp).2
    show p.2.1 - 1 ∈ range ((n - 4) / 2 + 1)
    rw [mem_range]
    omega

lemma pair_count (n s : ℕ) (hn : 4 ≤ n) (hs : s ≤ n - 4) :
    ((#{g ∈ Fintype.piFinset (fun _ : Fin 2 => range ((n - 1) / 2)) | ∑ i, g i = s} : ℕ) : ℤ) =
      (s + 1 : ℤ) - 2 * (if (n - 1) / 2 ≤ s then ((s - (n - 1) / 2 : ℕ) : ℤ) + 1 else 0) := by
  rw [card_eq_coeff, coeff_geom_pow 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [if_pos (show (n - 1) / 2 * 0 ≤ s by omega), if_neg (show ¬ ((n - 1) / 2 * (1 + 1) ≤ s) by omega)]
  simp only [show (1+1).choose 0 = 1 from rfl, show (1+1).choose 1 = 2 from rfl, Nat.choose_one_right]
  by_cases h : (n - 1) / 2 ≤ s
  · rw [if_pos (show (n - 1) / 2 * 1 ≤ s by omega), if_pos h,
      show s - (n - 1) / 2 * 1 + 1 = (s - (n - 1) / 2) + 1 by omega,
      show s - (n - 1) / 2 * 0 + 1 = s + 1 by omega]
    push_cast; ring
  · rw [if_neg (show ¬ ((n - 1) / 2 * 1 ≤ s) by omega), if_neg h,
      show s - (n - 1) / 2 * 0 + 1 = s + 1 by omega]; push_cast; ring


lemma sumA (N : ℕ) : ∀ q : ℕ, 2 * q ≤ N →
    ∑ b ∈ range (q + 1), ((((N - 2 * b : ℕ) : ℤ)) + 1) = (q + 1) * (N + 1) - q * (q + 1) := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
    intro hq
    rw [sum_range_succ, ih (by omega)]
    push_cast [Nat.cast_sub (show 2 * (q + 1) ≤ N by omega)]
    ring

lemma sumB (N m : ℕ) : ∀ R : ℕ, R ≤ N + 1 → 2 * (R - 1) + m ≤ N ∨ R = 0 →
    ∑ b ∈ range R, ((((N - 2 * b - m : ℕ) : ℤ)) + 1) = R * (N - m + 1) - R * (R - 1) := by
  intro R
  induction R with
  | zero => intro _ _; simp
  | succ R ih =>
    intro h1 h2
    have h2' : 2 * R + m ≤ N := by omega
    rw [sum_range_succ, ih (by omega) (by omega)]
    push_cast [Nat.cast_sub (show 2 * R ≤ N by omega), Nat.cast_sub (show m ≤ N - 2 * R by omega),
      Nat.cast_sub (show m ≤ N by omega)]
    ring

lemma V_val (n q R : ℕ) (hn : 4 ≤ n) (hq : q = (n - 4) / 2)
    (hR : R = if (n - 1) / 2 ≤ n - 4 then (n - 4 - (n - 1) / 2) / 2 + 1 else 0) :
    ((#(Vset n) : ℕ) : ℤ) = ((q : ℤ) + 1) * ((n - 4 : ℕ) + 1) - q * (q + 1) -
      2 * ((R : ℤ) * (((n - 4 : ℕ) : ℤ) - ((n - 1) / 2 : ℕ) + 1) - R * (R - 1)) := by
  rw [V_sum n hn]
  push_cast
  rw [Finset.sum_congr rfl (fun b hb => pair_count n (n - 4 - 2 * b) hn (by omega))]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hB : ∑ b ∈ range ((n - 4) / 2 + 1), (if (n - 1) / 2 ≤ n - 4 - 2 * b then
      (((n - 4 - 2 * b - (n - 1) / 2 : ℕ) : ℤ) + 1) else 0) =
      ∑ b ∈ range R, ((((n - 4 - 2 * b - (n - 1) / 2 : ℕ) : ℤ)) + 1) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext b; simp only [mem_filter, mem_range, hR]; split_ifs <;> omega
  rw [hB, sumB (n - 4) ((n - 1) / 2) R (by rw [hR]; split_ifs <;> omega) (by rw [hR]; split_ifs <;> omega),
    hq, sumA (n - 4) ((n - 4) / 2) (by omega)]
  push_cast
  ring


lemma small_zero (n : ℕ) (hn : n < 4) (P : (Fin 4 → ℕ) → Prop) [DecidablePred P] :
    #{f ∈ SS n | good n f ∧ P f} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f hf h
  have hc := (mem_SS_good n f).1 ⟨hf, h.1⟩
  omega

lemma eight (n : ℕ) : (a n : ℤ) * 8 = #{f ∈ SS n | good n f} + 2 * #(Cset n) + 3 * #(Eset n) +
    2 * #(Vset n) := by
  have hb := burnside n
  rw [sum_D4, Fin.sum_univ_four, Fin.sum_univ_four] at hb
  simp only [fix_r, fix_sr] at hb
  rw [fixT, fixR1, fixR2, fixR3, fixS0, fixS1, fixS2, fixS3] at hb
  have := congrArg (fun x : ℕ => (x : ℤ)) hb
  push_cast at this
  linarith

noncomputable def Pq (n : ℕ) : ℚ :=
  if n % 4 = 0 then (((n : ℚ) - 1) * (((n : ℚ) - 2) * n + 18) + 18) / 96
  else if n % 4 = 1 then ((n : ℚ) ^ 3 - 7 * n + 6) / 96
  else if n % 4 = 2 then (((n : ℚ) - 1) * (((n : ℚ) - 2) * n + 18) - 18) / 96
  else ((n : ℚ) ^ 3 - 7 * n - 6) / 96

lemma res0 (j : ℕ) : (a (4 * j + 4) : ℚ) = Pq (4 * j + 4) := by
  have h8 := eight (4 * j + 4)
  have hT := T_val (4 * j + 4) (by omega)
  have hV := V_val (4 * j + 4) (2 * j) (j) (by omega) (by omega) (by split_ifs <;> omega)
  rw [card_C, card_E] at h8
  rw [if_pos ⟨⟨j + 1, by ring⟩, by omega⟩] at h8
  rw [if_pos (show (4 * j + 4) % 2 = 0 by omega), show (4 * j + 4) / 2 - 1 = 2 * j + 1 by omega] at h8
  rw [show 4 * j + 4 - 1 - (4 * j + 4 - 1) / 2 = 2 * j + 2 by omega, show 4 * j + 4 - 1 = 4 * j + 3 by omega,
    choose_three, choose_three] at hT
  rw [show 4 * j + 4 - 4 = 4 * j + 0 by omega, show (4 * j + 4 - 1) / 2 = 2 * j + 1 by omega] at hV
  have h8q := congrArg (fun x : ℤ => (x : ℚ)) h8
  have hVq := congrArg (fun x : ℤ => (x : ℚ)) hV
  push_cast at h8q hVq hT
  rw [Pq, show (4 * j + 4) % 4 = 0 by omega]
  norm_num
  rw [hT, hVq] at h8q
  linear_combination h8q / 8

lemma res1 (j : ℕ) : (a (4 * j + 4 + 1) : ℚ) = Pq (4 * j + 4 + 1) := by
  have h8 := eight (4 * j + 4 + 1)
  have hT := T_val (4 * j + 4 + 1) (by omega)
  have hV := V_val (4 * j + 4 + 1) (2 * j) (j) (by omega) (by omega) (by split_ifs <;> omega)
  rw [card_C, card_E] at h8
  rw [if_neg (by rintro ⟨⟨c, hc⟩, -⟩; omega)] at h8
  rw [if_neg (show ¬ ((4 * j + 4 + 1) % 2 = 0) by omega)] at h8
  rw [show 4 * j + 4 + 1 - 1 - (4 * j + 4 + 1 - 1) / 2 = 2 * j + 2 by omega, show 4 * j + 4 + 1 - 1 = 4 * j + 4 by omega,
    choose_three, choose_three] at hT
  rw [show 4 * j + 4 + 1 - 4 = 4 * j + 1 by omega, show (4 * j + 4 + 1 - 1) / 2 = 2 * j + 2 by omega] at hV
  have h8q := congrArg (fun x : ℤ => (x : ℚ)) h8
  have hVq := congrArg (fun x : ℤ => (x : ℚ)) hV
  push_cast at h8q hVq hT
  rw [Pq, show (4 * j + 4 + 1) % 4 = 1 by omega]
  norm_num
  rw [hT, hVq] at h8q
  linear_combination h8q / 8

lemma res2 (j : ℕ) : (a (4 * j + 4 + 2) : ℚ) = Pq (4 * j + 4 + 2) := by
  have h8 := eight (4 * j + 4 + 2)
  have hT := T_val (4 * j + 4 + 2) (by omega)
  have hV := V_val (4 * j + 4 + 2) (2 * j + 1) (j + 1) (by omega) (by omega) (by split_ifs <;> omega)
  rw [card_C, card_E] at h8
  rw [if_neg (by rintro ⟨⟨c, hc⟩, -⟩; omega)] at h8
  rw [if_pos (show (4 * j + 4 + 2) % 2 = 0 by omega), show (4 * j + 4 + 2) / 2 - 1 = 2 * j + 2 by omega] at h8
  rw [show 4 * j + 4 + 2 - 1 - (4 * j + 4 + 2 - 1) / 2 = 2 * j + 3 by omega, show 4 * j + 4 + 2 - 1 = 4 * j + 5 by omega,
    choose_three, choose_three] at hT
  rw [show 4 * j + 4 + 2 - 4 = 4 * j + 2 by omega, show (4 * j + 4 + 2 - 1) / 2 = 2 * j + 2 by omega] at hV
  have h8q := congrArg (fun x : ℤ => (x : ℚ)) h8
  have hVq := congrArg (fun x : ℤ => (x : ℚ)) hV
  push_cast at h8q hVq hT
  rw [Pq, show (4 * j + 4 + 2) % 4 = 2 by omega]
  norm_num
  rw [hT, hVq] at h8q
  linear_combination h8q / 8

lemma res3 (j : ℕ) : (a (4 * j + 4 + 3) : ℚ) = Pq (4 * j + 4 + 3) := by
  have h8 := eight (4 * j + 4 + 3)
  have hT := T_val (4 * j + 4 + 3) (by omega)
  have hV := V_val (4 * j + 4 + 3) (2 * j + 1) (j + 1) (by omega) (by omega) (by split_ifs <;> omega)
  rw [card_C, card_E] at h8
  rw [if_neg (by rintro ⟨⟨c, hc⟩, -⟩; omega)] at h8
  rw [if_neg (show ¬ ((4 * j + 4 + 3) % 2 = 0) by omega)] at h8
  rw [show 4 * j + 4 + 3 - 1 - (4 * j + 4 + 3 - 1) / 2 = 2 * j + 3 by omega, show 4 * j + 4 + 3 - 1 = 4 * j + 6 by omega,
    choose_three, choose_three] at hT
  rw [show 4 * j + 4 + 3 - 4 = 4 * j + 3 by omega, show (4 * j + 4 + 3 - 1) / 2 = 2 * j + 3 by omega] at hV
  have h8q := congrArg (fun x : ℤ => (x : ℚ)) h8
  have hVq := congrArg (fun x : ℤ => (x : ℚ)) hV
  push_cast at h8q hVq hT
  rw [Pq, show (4 * j + 4 + 3) % 4 = 3 by omega]
  norm_num
  rw [hT, hVq] at h8q
  linear_combination h8q / 8

lemma a_small (n : ℕ) (hn : n < 4) : a n = 0 := by
  have h8 := eight n
  have hT : #{f ∈ SS n | good n f} = 0 := by
    have := small_zero n hn (fun _ => True)
    simpa using this
  have hV : #(Vset n) = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp; simp only [Vset, mem_filter] at hp; omega
  rw [hT, hV, card_C, card_E] at h8
  interval_cases n <;> simp at h8 <;> omega

lemma closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = Pq n := by
  by_cases h4 : n < 4
  · rw [a_small n h4]; interval_cases n <;> norm_num [Pq]
  · obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 4 ∧ n = 4 * j + 4 + r :=
      ⟨(n - 4) / 4, (n - 4) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    interval_cases r
    · simpa using res0 j
    · exact res1 j
    · exact res2 j
    · exact res3 j

lemma trig (q r : ℕ) (hr : r < 4) :
    Real.sin (Real.pi * ((4 * q + r : ℕ) : ℝ) / 2) = ([0, 1, 0, -1] : List ℝ).getD r 0 ∧
    Real.cos (Real.pi * ((4 * q + r : ℕ) : ℝ) / 2) = ([1, 0, -1, 0] : List ℝ).getD r 0 := by
  have e : Real.pi * ((4 * q + r : ℕ) : ℝ) / 2 = r * (Real.pi / 2) + q * (2 * Real.pi) := by
    push_cast; ring
  rw [e, Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]
  interval_cases r
  · simp
  · simp
  · simp only [Nat.cast_ofNat, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]; simp
  · rw [show ((3 : ℕ) : ℝ) * (Real.pi / 2) = Real.pi / 2 + Real.pi by push_cast; ring,
      Real.sin_add_pi, Real.cos_add_pi]; simp

lemma Pq_shift (m c : ℕ) : Pq (4 * m + c) =
    if c % 4 = 0 then ((((4 * m + c : ℕ) : ℚ) - 1) * ((((4 * m + c : ℕ) : ℚ) - 2) * ((4 * m + c : ℕ) : ℚ) + 18) + 18) / 96
    else if c % 4 = 1 then ((((4 * m + c : ℕ) : ℚ)) ^ 3 - 7 * ((4 * m + c : ℕ) : ℚ) + 6) / 96
    else if c % 4 = 2 then ((((4 * m + c : ℕ) : ℚ) - 1) * ((((4 * m + c : ℕ) : ℚ) - 2) * ((4 * m + c : ℕ) : ℚ) + 18) - 18) / 96
    else ((((4 * m + c : ℕ) : ℚ)) ^ 3 - 7 * ((4 * m + c : ℕ) : ℚ) - 6) / 96 := by
  unfold Pq; rw [show (4 * m + c) % 4 = c % 4 by omega]

lemma coeff_mk_mul_X_pow (f : ℕ → ℚ) (j k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk f * PowerSeries.X ^ j) = if j ≤ k then f (k - j) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]

end OMA.Helpers_a057886

open OMA.Helpers_a057886 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a057886.main := by
  have hreal : ∀ n : ℕ, 1 ≤ n → (OMA.S_oeis_a057886.a n : ℝ) = ((Pq n : ℚ) : ℝ) := fun n hn => by
    rw [← closed n hn]; push_cast; rfl
  refine ⟨fun n hn he => ?_, fun n hn ho => ?_, ?_⟩
  · rw [hreal n hn]
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r :=
      ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
    obtain ⟨hs, hc⟩ := trig q r hr
    rw [hs, hc]
    rcases he with ⟨t, ht⟩
    interval_cases r
    · simp only [Pq, show (4 * q + 0) % 4 = 0 by omega, if_true]; push_cast; simp
    · omega
    · simp only [Pq, show (4 * q + 2) % 4 = 2 by omega]; norm_num; push_cast; ring
    · omega
  · rw [hreal n hn]
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r :=
      ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
    obtain ⟨hs, hc⟩ := trig q r hr
    rw [hs, hc]
    rcases ho with ⟨t, ht⟩
    interval_cases r
    · omega
    · simp only [Pq, show (4 * q + 1) % 4 = 1 by omega]; norm_num
    · omega
    · simp only [Pq, show (4 * q + 3) % 4 = 3 by omega]; norm_num; push_cast; ring
  · set f : ℕ → ℚ := fun n => (OMA.S_oeis_a057886.a n : ℚ) with hf
    have fv : ∀ n, 1 ≤ n → f n = Pq n := fun n hn => closed n hn
    have f0 : f 0 = 0 := by simp [hf, a_small 0 (by norm_num)]
    have e : PowerSeries.mk f * ((X - 1) ^ 4 * (X + 1) ^ 3 * (X ^ 2 + 1) : PowerSeries ℚ) =
        PowerSeries.mk f * X ^ 0 - PowerSeries.mk f * X ^ 1 - C 2 * (PowerSeries.mk f * X ^ 2) + C 2 * (PowerSeries.mk f * X ^ 3) + C 2 * (PowerSeries.mk f * X ^ 6) - C 2 * (PowerSeries.mk f * X ^ 7) - PowerSeries.mk f * X ^ 8 + PowerSeries.mk f * X ^ 9 := by
      simp only [map_ofNat]; ring
    have e2 : (X ^ 4 * (X ^ 3 - X ^ 2 + 1) : PowerSeries ℚ) = C 1 * X ^ 4 - C 1 * X ^ 6 + C 1 * X ^ 7 := by
      simp only [map_one]; ring
    rw [e, e2]
    ext k
    simp only [map_sub, map_add, coeff_C_mul_X_pow]
    simp only [coeff_C_mul, coeff_mk_mul_X_pow]
    by_cases hk : k ≤ 9
    · interval_cases k <;> simp [f0, fv, Pq] <;> norm_num
    · obtain ⟨m, hm | hm | hm | hm⟩ : ∃ m, k = 4 * m + 10 ∨ k = 4 * m + 11 ∨ k = 4 * m + 12 ∨
          k = 4 * m + 13 := ⟨(k - 10) / 4, by omega⟩
      · subst hm
        simp only [show 0 ≤ 4 * m + 10 by omega, show 1 ≤ 4 * m + 10 by omega, show 2 ≤ 4 * m + 10 by omega, show 3 ≤ 4 * m + 10 by omega, show 4 ≤ 4 * m + 10 by omega, show 5 ≤ 4 * m + 10 by omega, show 6 ≤ 4 * m + 10 by omega, show 7 ≤ 4 * m + 10 by omega, show 8 ≤ 4 * m + 10 by omega, show 9 ≤ 4 * m + 10 by omega, if_true, show 4 * m + 10 ≠ 4 by omega, show 4 * m + 10 ≠ 6 by omega, show 4 * m + 10 ≠ 7 by omega, if_false, show 4 * m + 10 - 0 = 4 * m + 10 from rfl, show 4 * m + 10 - 1 = 4 * m + 9 from rfl, show 4 * m + 10 - 2 = 4 * m + 8 from rfl, show 4 * m + 10 - 3 = 4 * m + 7 from rfl, show 4 * m + 10 - 6 = 4 * m + 4 from rfl, show 4 * m + 10 - 7 = 4 * m + 3 from rfl, show 4 * m + 10 - 8 = 4 * m + 2 from rfl, show 4 * m + 10 - 9 = 4 * m + 1 from rfl]
        rw [fv (4 * m + 10) (by omega), fv (4 * m + 9) (by omega), fv (4 * m + 8) (by omega), fv (4 * m + 7) (by omega), fv (4 * m + 4) (by omega), fv (4 * m + 3) (by omega), fv (4 * m + 2) (by omega), fv (4 * m + 1) (by omega)]
        simp only [Pq_shift]
        norm_num
        ring
      · subst hm
        simp only [show 0 ≤ 4 * m + 11 by omega, show 1 ≤ 4 * m + 11 by omega, show 2 ≤ 4 * m + 11 by omega, show 3 ≤ 4 * m + 11 by omega, show 4 ≤ 4 * m + 11 by omega, show 5 ≤ 4 * m + 11 by omega, show 6 ≤ 4 * m + 11 by omega, show 7 ≤ 4 * m + 11 by omega, show 8 ≤ 4 * m + 11 by omega, show 9 ≤ 4 * m + 11 by omega, if_true, show 4 * m + 11 ≠ 4 by omega, show 4 * m + 11 ≠ 6 by omega, show 4 * m + 11 ≠ 7 by omega, if_false, show 4 * m + 11 - 0 = 4 * m + 11 from rfl, show 4 * m + 11 - 1 = 4 * m + 10 from rfl, show 4 * m + 11 - 2 = 4 * m + 9 from rfl, show 4 * m + 11 - 3 = 4 * m + 8 from rfl, show 4 * m + 11 - 6 = 4 * m + 5 from rfl, show 4 * m + 11 - 7 = 4 * m + 4 from rfl, show 4 * m + 11 - 8 = 4 * m + 3 from rfl, show 4 * m + 11 - 9 = 4 * m + 2 from rfl]
        rw [fv (4 * m + 11) (by omega), fv (4 * m + 10) (by omega), fv (4 * m + 9) (by omega), fv (4 * m + 8) (by omega), fv (4 * m + 5) (by omega), fv (4 * m + 4) (by omega), fv (4 * m + 3) (by omega), fv (4 * m + 2) (by omega)]
        simp only [Pq_shift]
        norm_num
        ring
      · subst hm
        simp only [show 0 ≤ 4 * m + 12 by omega, show 1 ≤ 4 * m + 12 by omega, show 2 ≤ 4 * m + 12 by omega, show 3 ≤ 4 * m + 12 by omega, show 4 ≤ 4 * m + 12 by omega, show 5 ≤ 4 * m + 12 by omega, show 6 ≤ 4 * m + 12 by omega, show 7 ≤ 4 * m + 12 by omega, show 8 ≤ 4 * m + 12 by omega, show 9 ≤ 4 * m + 12 by omega, if_true, show 4 * m + 12 ≠ 4 by omega, show 4 * m + 12 ≠ 6 by omega, show 4 * m + 12 ≠ 7 by omega, if_false, show 4 * m + 12 - 0 = 4 * m + 12 from rfl, show 4 * m + 12 - 1 = 4 * m + 11 from rfl, show 4 * m + 12 - 2 = 4 * m + 10 from rfl, show 4 * m + 12 - 3 = 4 * m + 9 from rfl, show 4 * m + 12 - 6 = 4 * m + 6 from rfl, show 4 * m + 12 - 7 = 4 * m + 5 from rfl, show 4 * m + 12 - 8 = 4 * m + 4 from rfl, show 4 * m + 12 - 9 = 4 * m + 3 from rfl]
        rw [fv (4 * m + 12) (by omega), fv (4 * m + 11) (by omega), fv (4 * m + 10) (by omega), fv (4 * m + 9) (by omega), fv (4 * m + 6) (by omega), fv (4 * m + 5) (by omega), fv (4 * m + 4) (by omega), fv (4 * m + 3) (by omega)]
        simp only [Pq_shift]
        norm_num
        ring
      · subst hm
        simp only [show 0 ≤ 4 * m + 13 by omega, show 1 ≤ 4 * m + 13 by omega, show 2 ≤ 4 * m + 13 by omega, show 3 ≤ 4 * m + 13 by omega, show 4 ≤ 4 * m + 13 by omega, show 5 ≤ 4 * m + 13 by omega, show 6 ≤ 4 * m + 13 by omega, show 7 ≤ 4 * m + 13 by omega, show 8 ≤ 4 * m + 13 by omega, show 9 ≤ 4 * m + 13 by omega, if_true, show 4 * m + 13 ≠ 4 by omega, show 4 * m + 13 ≠ 6 by omega, show 4 * m + 13 ≠ 7 by omega, if_false, show 4 * m + 13 - 0 = 4 * m + 13 from rfl, show 4 * m + 13 - 1 = 4 * m + 12 from rfl, show 4 * m + 13 - 2 = 4 * m + 11 from rfl, show 4 * m + 13 - 3 = 4 * m + 10 from rfl, show 4 * m + 13 - 6 = 4 * m + 7 from rfl, show 4 * m + 13 - 7 = 4 * m + 6 from rfl, show 4 * m + 13 - 8 = 4 * m + 5 from rfl, show 4 * m + 13 - 9 = 4 * m + 4 from rfl]
        rw [fv (4 * m + 13) (by omega), fv (4 * m + 12) (by omega), fv (4 * m + 11) (by omega), fv (4 * m + 10) (by omega), fv (4 * m + 7) (by omega), fv (4 * m + 6) (by omega), fv (4 * m + 5) (by omega), fv (4 * m + 4) (by omega)]
        simp only [Pq_shift]
        norm_num
        ring
