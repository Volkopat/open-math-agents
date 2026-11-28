import OMAStatements.S_mse_2986503
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

namespace OMA.Basis2986503.Hall

open scoped Matrix

private theorem finrank_finset_sup_le {n m : ℕ}
    (V : Fin n → Submodule ℝ (Fin n → ℝ))
    (hV : ∀ j, Module.finrank ℝ (V j) = m) (S : Finset (Fin n)) :
    Module.finrank ℝ ↥(S.sup V) ≤ S.card * m := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.sup_insert, Finset.card_insert_of_notMem hk, Nat.add_mul, one_mul]
    exact (Submodule.finrank_add_le_finrank_add_finrank (V k) (S.sup V)).trans (by
      rw [hV, add_comm]
      exact Nat.add_le_add_right ih _)

theorem strictHall (n m : ℕ) (hm : 2 ≤ m) (_hmn : m < n)
    (V : Fin n → Submodule ℝ (Fin n → ℝ))
    (hV : ∀ j, Module.finrank ℝ (V j) = m)
    (hspan : ∀ S : Finset (Fin n), S.card = (n + m - 1) / m →
      (⨆ j ∈ S, V j) = ⊤)
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    S.card < Module.finrank ℝ ↥(⨆ j ∈ S, V j) := by
  classical
  set r := (n + m - 1) / m
  let d := Module.finrank ℝ ↥(S.sup V)
  have hpos : 0 < m := by omega
  have hsm : S.card < n := by
    simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
  have hrn : r ≤ n := by
    have hnm : n ≤ n * m := by simpa using Nat.mul_le_mul_left n (show 1 ≤ m by omega)
    have hlt : r < n + 1 := by
      apply (Nat.div_lt_iff_lt_mul hpos).2
      rw [Nat.add_mul, one_mul]
      omega
    omega
  have htop : Module.finrank ℝ (⊤ : Submodule ℝ (Fin n → ℝ)) = n := by
    rw [finrank_top, Module.finrank_pi, Fintype.card_fin]
  rw [← Finset.sup_eq_iSup]
  change S.card < d
  by_cases hcard : r ≤ S.card
  · obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq hcard
    have hle := Submodule.finrank_mono (Finset.sup_mono (f := V) hTS)
    rw [Finset.sup_eq_iSup, hspan T hTc, htop] at hle
    exact hsm.trans_le hle
  · have hroom : r - S.card ≤ (Finset.univ \ S).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simpa using Nat.sub_le_sub_right hrn S.card
    obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq hroom
    have hdis : Disjoint S T := by
      apply Finset.disjoint_left.2
      intro i hiS hiT
      exact (Finset.mem_sdiff.mp (hTS hiT)).2 hiS
    have hu : (S ∪ T).card = r := by
      rw [Finset.card_union_of_disjoint hdis, hTc]
      omega
    have hs := hspan (S ∪ T) hu
    rw [← Finset.sup_eq_iSup, Finset.sup_union] at hs
    have hle := Submodule.finrank_add_le_finrank_add_finrank (S.sup V) (T.sup V)
    rw [hs, htop] at hle
    have hd : n ≤ d + (r - S.card) * m :=
      hle.trans (Nat.add_le_add_left (hTc ▸ finrank_finset_sup_le V hV T) _)
    have hrm : r * m ≤ n + m - 1 := Nat.div_mul_le_self _ _
    have hSc : 0 < S.card := Finset.card_pos.mpr hne
    by_cases hs1 : S.card = 1
    · obtain ⟨i, hi⟩ := hne
      have hdim := Submodule.finrank_mono (Finset.le_sup (f := V) hi)
      rw [hV] at hdim
      change m ≤ d at hdim
      omega
    · have hsplit : (r - S.card) * m + S.card * m = r * m := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
      have hsmul : S.card * m = (S.card - 1) * m + m := by
        calc
          S.card * m = ((S.card - 1) + 1) * m := by rw [Nat.sub_add_cancel hSc]
          _ = (S.card - 1) * m + m := by rw [Nat.add_mul, one_mul]
      have hlower : (S.card - 1) * 2 ≤ (S.card - 1) * m := Nat.mul_le_mul_left _ hm
      omega

private def Walk {ι : Type*} (edge : ι → ι → Prop) (start : ι) : ℕ → ι → Prop
  | 0, x => x = start
  | k + 1, x => ∃ y, Walk edge start k y ∧ edge y x

private theorem edgeDistance {ι : Type*} (edge : ι → ι → Prop) (i : ι)
    (hr : ∀ j, ∃ k, Walk edge i k j) :
    ∃ d : ι → ℕ, (∀ a, d a = 0 ↔ a = i) ∧
      (∀ a b, edge a b → d b ≤ d a + 1) ∧
      (∀ b, d b ≠ 0 → ∃ a, d a + 1 = d b ∧ edge a b) := by
  classical
  let d : ι → ℕ := fun a => Nat.find (hr a)
  have hd (a) : Walk edge i (d a) a := Nat.find_spec (hr a)
  have hmin (a k) (h : Walk edge i k a) : d a ≤ k := Nat.find_min' (hr a) h
  refine ⟨d, ?_, ?_, ?_⟩
  · intro a
    constructor
    · intro ha
      have h := hd a
      rwa [ha] at h
    · intro ha
      subst a
      exact Nat.eq_zero_of_le_zero (hmin i 0 rfl)
  · intro a b h
    exact hmin b (d a + 1) ⟨a, hd a, h⟩
  · intro b hb
    obtain ⟨k, hk⟩ : ∃ k, d b = k + 1 := ⟨d b - 1, by omega⟩
    have h := hd b
    rw [hk] at h
    obtain ⟨a, ha, hab⟩ := h
    have hle := hmin a k ha
    have hge := hmin b (d a + 1) ⟨a, hd a, hab⟩
    exact ⟨a, by omega, hab⟩

private theorem accessible {n : ℕ} (V : Fin n → Submodule ℝ (Fin n → ℝ))
    (hHall : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
      S.card < Module.finrank ℝ ↥(⨆ a ∈ S, V a))
    (coord : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hcoord : Function.Injective coord)
    (i : Fin n) :
    ∀ j, ∃ k, Walk (fun a b => ∃ v ∈ V a, coord v b ≠ 0) i k j := by
  classical
  let edge : Fin n → Fin n → Prop := fun a b => ∃ v ∈ V a, coord v b ≠ 0
  intro j
  by_contra hj
  let S := Finset.univ.filter (fun a => ∃ k, Walk edge i k a)
  have hmem (a) : a ∈ S ↔ ∃ k, Walk edge i k a := by simp [S]
  have hi : i ∈ S := (hmem i).2 ⟨0, rfl⟩
  have hproper : S ≠ Finset.univ := by
    intro h
    apply hj
    exact (hmem j).1 (h ▸ Finset.mem_univ j)
  let P := S.sup V
  have hzero (b : Fin n) (hb : b ∉ S) (v : P) : coord v.val b = 0 := by
    let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj b).comp coord
    have hle : P ≤ f.ker := by
      apply Finset.sup_le
      intro a ha w hw
      change coord w b = 0
      by_contra hwz
      obtain ⟨k, hk⟩ := (hmem a).1 ha
      exact hb ((hmem b).2 ⟨k + 1, a, hk, w, hw, hwz⟩)
    exact hle v.property
  let restriction : P →ₗ[ℝ] (S → ℝ) :=
    LinearMap.pi fun a => (LinearMap.proj a.val).comp (coord.comp P.subtype)
  have hinj : Function.Injective restriction := by
    intro v w h
    apply Subtype.ext
    apply hcoord
    funext a
    by_cases ha : a ∈ S
    · exact congrFun h (⟨a, ha⟩ : S)
    · rw [hzero a ha v, hzero a ha w]
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi, Fintype.card_coe] at hdim
  have hstrict := hHall S ⟨i, hi⟩ hproper
  rw [← Finset.sup_eq_iSup] at hstrict
  exact (Nat.not_lt_of_ge hdim) hstrict

theorem room {n : ℕ} (V : Fin n → Submodule ℝ (Fin n → ℝ))
    (hHall : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
      S.card < Module.finrank ℝ ↥(⨆ a ∈ S, V a))
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : ∀ a, U a ∈ V a) (hdet : U.det ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, M.det ≠ 0 ∧
      (∀ a, a ≠ j → M a ∈ V a) ∧ M j ∈ V i := by
  classical
  have hunit : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  let coord := U⁻¹.vecMulLinear
  have hcoord : Function.Injective coord := by
    intro v w h
    have hv := congrArg (fun x : Fin n → ℝ => x ᵥ* U) h
    simpa [coord, Matrix.vecMul_vecMul, U.nonsing_inv_mul hunit] using hv
  let edge : Fin n → Fin n → Prop := fun a b => ∃ v ∈ V a, coord v b ≠ 0
  obtain ⟨d, hd0, hdist, hp⟩ := edgeDistance edge i (accessible V hHall coord hcoord i)
  have hwitness (b : Fin n) : ∃ a v, d b ≠ 0 →
      d a + 1 = d b ∧ v ∈ V a ∧ coord v b ≠ 0 := by
    by_cases hb : d b = 0
    · exact ⟨b, 0, fun h => (h hb).elim⟩
    · obtain ⟨a, ha, v, hv, hv'⟩ := hp b hb
      exact ⟨a, v, fun _ => ⟨ha, hv, hv'⟩⟩
  choose parent pick hpick using hwitness
  let D := d j
  have hD : 0 < D := Nat.pos_of_ne_zero fun h => hij ((hd0 j).mp h).symm
  let path : ℕ → Fin n := Nat.rec j fun _ a => parent a
  have hp0 : path 0 = j := rfl
  have hps (k : ℕ) : path (k + 1) = parent (path k) := rfl
  have hpd (k : ℕ) (hk : k ≤ D) : d (path k) + k = D := by
    induction k with
    | zero => simp [hp0, D]
    | succ k ih =>
      have hprev := ih (by omega)
      have hpos : d (path k) ≠ 0 := by omega
      rw [hps]
      have heq := (hpick (path k) hpos).1
      omega
  have hplast : path D = i := (hd0 _).mp (by have := hpd D le_rfl; omega)
  have hpinj (k l : ℕ) (hk : k ≤ D) (hl : l ≤ D) (he : path k = path l) : k = l := by
    have h₁ := hpd k hk
    have h₂ := hpd l hl
    rw [he] at h₁
    omega
  have hpick_path (k) (hk : k < D) :
      pick (path k) ∈ V (path (k + 1)) ∧ coord (pick (path k)) (path k) ≠ 0 := by
    have hd' := hpd k hk.le
    have hpos : d (path k) ≠ 0 := by omega
    rw [hps]
    exact (hpick (path k) hpos).2
  let Mid (a : Fin n) : Prop := ∃ l, 0 < l ∧ l < D ∧ path l = a
  let M : Matrix (Fin n) (Fin n) ℝ := fun (a : Fin n) =>
    if a = j then pick (path (D - 1))
    else @dite _ (Mid a) (Classical.propDecidable _) (fun h => pick (path (h.choose - 1)))
      (fun _ => U a)
  have hMj : M j = pick (path (D - 1)) := by simp [M]
  have hMfixed (a) (ha : a ≠ j) (hm : ¬ Mid a) : M a = U a := by simp [M, ha, hm]
  have hMmid (k : ℕ) (hk : k + 1 < D) : M (path (k + 1)) = pick (path k) := by
    have hne : path (k + 1) ≠ j := by
      intro h
      rw [← hp0] at h
      have := hpinj (k + 1) 0 (by omega) (by omega) h
      omega
    have hm : Mid (path (k + 1)) := ⟨k + 1, by omega, hk, rfl⟩
    have he := hpinj hm.choose (k + 1) hm.choose_spec.2.1.le hk.le hm.choose_spec.2.2
    unfold M
    simp [hne, hm, he]
  have hMperm (a) (haj : a ≠ j) : M a ∈ V a := by
    rcases em (Mid a) with ⟨l, hpos, hlt, rfl⟩ | hm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hMmid k hlt]
      exact (hpick_path k (by omega)).1
    · rw [hMfixed a haj hm]
      exact hU a
  have hMlast : M j ∈ V i := by
    rw [hMj, ← hplast]
    have h := (hpick_path (D - 1) (by omega)).1
    rwa [Nat.sub_add_cancel hD] at h
  let C := M * U⁻¹
  have hrow (a) : C a = coord (M a) := rfl
  have hid (a) : coord (U a) = (1 : Matrix (Fin n) (Fin n) ℝ) a :=
    congrFun (U.mul_nonsing_inv hunit) a
  have hkernel (x : Fin n → ℝ) (hx : C *ᵥ x = 0) : x = 0 := by
    have hfixed (a) (haj : a ≠ j) (hm : ¬ Mid a) : x a = 0 := by
      have hr : C a = (1 : Matrix (Fin n) (Fin n) ℝ) a := by
        rw [hrow, hMfixed a haj hm, hid]
      have ha := congrFun hx a
      change (C a) ⬝ᵥ x = 0 at ha
      rw [hr] at ha
      change ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) a = 0 at ha
      simpa using ha
    have hout (a) (ha : ¬ ∃ l ≤ D, path l = a) : x a = 0 := by
      apply hfixed a
      · intro he
        exact ha ⟨0, by omega, hp0.trans he.symm⟩
      · rintro ⟨l, _, hl, rfl⟩
        exact ha ⟨l, hl.le, rfl⟩
    have hback (k) (hk : k ≤ D) : ∀ l, k ≤ l → l ≤ D → x (path l) = 0 := by
      apply Nat.decreasingInduction (motive := fun k _ =>
        ∀ l, k ≤ l → l ≤ D → x (path l) = 0) ?_ ?_ hk
      · intro k hk ih l hkl hlD
        by_cases hlk : k < l
        · exact ih l (by omega) hlD
        have heq : l = k := by omega
        subst l
        have hlt : k < D := by omega
        let a := if k + 1 = D then j else path (k + 1)
        have hMa : M a = pick (path k) := by
          by_cases he : k + 1 = D
          · have hk' : D - 1 = k := by omega
            simp [a, he, hMj, hk']
          · simp [a, he, hMmid k (by omega : k + 1 < D)]
        have hh := congrFun hx a
        change (C a) ⬝ᵥ x = 0 at hh
        rw [hrow, hMa] at hh
        change (∑ b, coord (pick (path k)) b * x b) = 0 at hh
        have hsum : (∑ b, coord (pick (path k)) b * x b) =
            coord (pick (path k)) (path k) * x (path k) := by
          apply Finset.sum_eq_single (path k) _ (by simp)
          intro b _ hb
          rcases em (∃ l : ℕ, l ≤ D ∧ path l = b) with ⟨l, hl, rfl⟩ | hm
          · by_cases he : k < l
            · rw [ih l (by omega) hl, mul_zero]
            · have hlt' : l < k := by
                have hneq : l ≠ k := fun heq => hb (congrArg path heq)
                omega
              have hz : coord (pick (path k)) (path l) = 0 := by
                by_contra hne
                have hbnd := hdist (path (k + 1)) (path l) ⟨_, (hpick_path k hlt).1, hne⟩
                have h₁ := hpd (k + 1) (by omega)
                have h₂ := hpd l hl
                omega
              rw [hz, zero_mul]
          · rw [hout b hm, mul_zero]
        exact (mul_eq_zero.mp (hsum.symm.trans hh)).resolve_left (hpick_path k hlt).2
      · intro l h₁ h₂
        have he : l = D := by omega
        subst l
        apply hfixed (path D)
        · rw [hplast]
          exact hij
        · rintro ⟨k, _, hk, h⟩
          have := hpinj k D hk.le le_rfl h
          omega
    funext a
    rcases em (∃ l : ℕ, l ≤ D ∧ path l = a) with ⟨l, hl, rfl⟩ | ha
    · exact hback 0 (Nat.zero_le D) l (Nat.zero_le l) hl
    · exact hout a ha
  have hCinj : Function.Injective C.mulVec := by
    intro x y h
    apply sub_eq_zero.mp
    apply hkernel
    rw [Matrix.mulVec_sub, h, sub_self]
  refine ⟨M, ?_, hMperm, hMlast⟩
  have hCdet : C.det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det C).mp (Matrix.mulVec_injective_iff_isUnit.mp hCinj))
  intro hm
  apply hCdet
  simp [C, Matrix.det_mul, hm]

end OMA.Basis2986503.Hall

namespace OMA.Basis2986503.Rows

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

def frame (M : Mat n) (p q : Fin n) (a b : Vec n) : Mat n :=
  (M.updateRow p a).updateRow q b

theorem frame_left (M : Mat n) {p q : Fin n} (h : p ≠ q) (a b : Vec n) :
    frame M p q a b p = a := by
  simp only [frame, Matrix.updateRow_ne h, Matrix.updateRow_self]

@[simp] theorem frame_right (M : Mat n) (p q : Fin n) (a b : Vec n) :
    frame M p q a b q = b := by
  simp only [frame, Matrix.updateRow_self]

theorem frame_other (M : Mat n) {p q k : Fin n}
    (hp : k ≠ p) (hq : k ≠ q) (a b : Vec n) : frame M p q a b k = M k := by
  simp only [frame, Matrix.updateRow_ne hq, Matrix.updateRow_ne hp]

theorem frame_eq (M : Mat n) (p q : Fin n) :
    frame M p q (M p) (M q) = M := by
  simp only [frame, Matrix.updateRow_eq_self]

noncomputable def pairing (M : Mat n) {p q : Fin n} (hpq : p ≠ q) :
    Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun b := (frame M p q a b).det
      map_add' b c := Matrix.det_updateRow_add _ _ b c
      map_smul' r b := Matrix.det_updateRow_smul _ _ r b }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    change (frame M p q (a + b) c).det =
      (frame M p q a c).det + (frame M p q b c).det
    simp only [frame, Matrix.updateRow_comm M hpq, Matrix.det_updateRow_add]
  map_smul' r a := by
    apply LinearMap.ext
    intro c
    change (frame M p q (r • a) c).det = r * (frame M p q a c).det
    simp only [frame, Matrix.updateRow_comm M hpq, Matrix.det_updateRow_smul]

theorem pairing_self (M : Mat n) {p q : Fin n} (h : p ≠ q) (a : Vec n) :
    pairing M h a a = 0 := by
  change (frame M p q a a).det = 0
  exact Matrix.det_zero_of_row_eq h (by rw [frame_left M h, frame_right])

theorem pairing_reverse (M : Mat n) {p q : Fin n} (h : p ≠ q) (a b : Vec n) :
    pairing M h b a = -pairing M h a b := by
  have hz := pairing_self M h (a + b)
  simp only [map_add, LinearMap.add_apply, pairing_self] at hz
  linarith

def frozenSpan (M : Mat n) (p q : Fin n) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ (Set.range (fun k : {j : Fin n // j ≠ p ∧ j ≠ q} => M k))

theorem pairing_frozen (M : Mat n) {p q : Fin n} (hpq : p ≠ q)
    (a b : Vec n) (hb : b ∈ frozenSpan M p q) :
    pairing M hpq a b = 0 := by
  have hspan : frozenSpan M p q ≤ (pairing M hpq a).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (frame M p q a (M i)).det = 0
    exact Matrix.det_zero_of_row_eq i.property.2 (by
      rw [frame_other M i.property.1 i.property.2, frame_right])
  exact hspan hb

theorem sup_frozen (M : Mat n) {p q : Fin n} (hpq : p ≠ q)
    (F : Submodule ℝ (Vec n)) (b b' : F) (hdet : (frame M p q b b').det ≠ 0) :
    F ⊔ frozenSpan M p q = ⊤ := by
  letI : Nonempty (Fin n) := ⟨p⟩
  have h := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hsp : Submodule.span ℝ (Set.range (frame M p q b b')) = ⊤ :=
    h.span_eq_top_of_card_eq_finrank (by simp)
  have hle : Submodule.span ℝ (Set.range (frame M p q b b')) ≤ F ⊔ frozenSpan M p q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hq : i = q
    · subst i
      rw [frame_right]
      exact (show F ≤ F ⊔ frozenSpan M p q from le_sup_left) b'.property
    by_cases hp : i = p
    · subst i
      rw [frame_left M hpq]
      exact (show F ≤ F ⊔ frozenSpan M p q from le_sup_left) b.property
    rw [frame_other M hp hq]
    exact (show frozenSpan M p q ≤ F ⊔ frozenSpan M p q from le_sup_right)
      (Submodule.subset_span ⟨⟨i, hp, hq⟩, rfl⟩)
  rw [hsp] at hle
  exact top_unique hle

noncomputable def signedPairing (M : Mat n) {p q : Fin n} (hpq : p ≠ q) (s : ℝ)
    (E F : Submodule ℝ (Vec n)) : E →ₗ[ℝ] F →ₗ[ℝ] ℝ where
  toFun a := s • (pairing M hpq a).comp F.subtype
  map_add' a b := by
    ext c
    change s * pairing M hpq ((a : Vec n) + b) c =
      s * pairing M hpq a c + s * pairing M hpq b c
    simp [mul_add]
  map_smul' r a := by
    ext c
    change s * pairing M hpq (r • (a : Vec n)) c = r * (s * pairing M hpq a c)
    simp [mul_left_comm]

@[simp] theorem signedPairing_apply (M : Mat n) {p q : Fin n}
    (hpq : p ≠ q) (s : ℝ) (E F : Submodule ℝ (Vec n)) (a : E) (b : F) :
    signedPairing M hpq s E F a b = s * (frame M p q a b).det := rfl

theorem signedPairing_rank_two (M : Mat n) {p q : Fin n}
    (hpq : p ≠ q) {s : ℝ} (hs : s ≠ 0) (E F : Submodule ℝ (Vec n))
    (a a' : E) (b b' : F)
    (ha : (frame M p q a a').det ≠ 0) (hb : (frame M p q b b').det ≠ 0) :
    ∃ x y u v, signedPairing M hpq s E F x u * signedPairing M hpq s E F y v -
      signedPairing M hpq s E F x v * signedPairing M hpq s E F y u ≠ 0 := by
  have hf := sup_frozen M hpq F b b' hb
  have project (x : Vec n) : ∃ u : F, ∀ y : Vec n,
      pairing M hpq y x = pairing M hpq y u := by
    have hx : x ∈ F ⊔ frozenSpan M p q := by rw [hf]; trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨u, hu⟩, fun y => ?_⟩
    rw [map_add, pairing_frozen M hpq y v hv, add_zero]
  obtain ⟨u, hu⟩ := project a
  obtain ⟨v, hv⟩ := project a'
  refine ⟨a, a', u, v, ?_⟩
  change s * pairing M hpq a u * (s * pairing M hpq a' v) -
    s * pairing M hpq a v * (s * pairing M hpq a' u) ≠ 0
  rw [← hu a, ← hv a', ← hv a, ← hu a', pairing_self, pairing_self,
    pairing_reverse M hpq (a : Vec n) a']
  have hn : pairing M hpq a a' ≠ 0 := ha
  simp only [mul_zero, zero_sub, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero hs hn) (mul_ne_zero hs (neg_ne_zero.mpr hn))

end OMA.Basis2986503.Rows

namespace OMA.Basis2986503.Dense

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dense_ne_zero (f : E → ℝ) (hw : ∃ x, f x ≠ 0)
    (hp : ∀ x y, ∃ p : Polynomial ℝ, ∀ t : ℝ,
      p.eval t = f ((1 - t) • x + t • y)) : Dense {x | f x ≠ 0} := by
  refine dense_iff_inter_open.mpr fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨y, hy⟩ := hw
  obtain ⟨p, heval⟩ := hp x y
  have hp₁ : p.eval 1 = f y := by simpa using heval 1
  have hpne : p ≠ 0 := by
    intro hz
    exact hy (by simpa [hz] using hp₁.symm)
  let line (t : ℝ) : E := (1 - t) • x + t • y
  have hline : Continuous line :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hzero : (0 : ℝ) ∈ line ⁻¹' U := by simpa [line] using hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hline) 0 hzero
  have hinterval : Set.Ioo (-ε) ε ⊆ line ⁻¹' U := by
    simpa [Real.ball_eq_Ioo] using hball
  have hnot : ¬ Set.Ioo (-ε) ε ⊆ {t : ℝ | p.IsRoot t} := by
    intro hsubset
    exact (Set.Ioo_infinite ((neg_neg_of_pos hε).trans hε))
      ((Polynomial.finite_setOfPred_isRoot hpne).subset hsubset)
  obtain ⟨t, ht, hroot⟩ := Set.not_subset.mp hnot
  refine ⟨line t, hinterval ht, ?_⟩
  intro h
  exact hroot ((heval t).trans h)

theorem dense_common_ne_zero {ι : Type*} [Finite ι] (f : ι → E → ℝ)
    (hf : ∀ j, Continuous (f j)) (hw : ∀ j, ∃ x, f j x ≠ 0)
    (hp : ∀ j x y, ∃ p : Polynomial ℝ, ∀ t : ℝ,
      p.eval t = f j ((1 - t) • x + t • y)) : Dense {x | ∀ j, f j x ≠ 0} := by
  classical
  let instFintype := Fintype.ofFinite ι
  have hfinite (J : Finset ι) : Dense {x | ∀ j ∈ J, f j x ≠ 0} := by
    induction J using Finset.induction_on with
    | empty => simp
    | @insert j J hj ih =>
      have hset : {x : E | ∀ j' ∈ insert j J, f j' x ≠ 0} =
          {x : E | f j x ≠ 0} ∩ {x : E | ∀ j' ∈ J, f j' x ≠ 0} := by
        ext x
        simp
      rw [hset]
      exact (dense_ne_zero (f j) (hw j) (hp j)).inter_of_isOpen_left ih
        (isOpen_ne.preimage (hf j))
  simpa using hfinite Finset.univ

theorem exists_in_open {ι : Type*} [Finite ι] (f : ι → E → ℝ)
    (hf : ∀ j, Continuous (f j)) (hw : ∀ j, ∃ x, f j x ≠ 0)
    (hp : ∀ j x y, ∃ p : Polynomial ℝ, ∀ t : ℝ,
      p.eval t = f j ((1 - t) • x + t • y)) {U : Set E} (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ x ∈ U, ∀ j, f j x ≠ 0 :=
  (dense_common_ne_zero f hf hw hp).inter_open_nonempty U hU hne

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem eval_det (M : Matrix n n (Polynomial ℝ)) (t : ℝ) :
    M.det.eval t = (M.map fun p => p.eval t).det :=
  (Polynomial.evalRingHom t).map_det M

noncomputable def lineMatrix (A B : Matrix n n ℝ) : Matrix n n (Polynomial ℝ) :=
  Matrix.of fun i j =>
    (1 - Polynomial.X) * Polynomial.C (A i j) + Polynomial.X * Polynomial.C (B i j)

theorem eval_lineMatrix_det (A B : Matrix n n ℝ) (t : ℝ) :
    (lineMatrix A B).det.eval t = ((1 - t) • A + t • B).det := by
  rw [eval_det]
  congr 1
  ext i j
  simp [lineMatrix]
  exact mul_comm _ _

end OMA.Basis2986503.Dense

namespace OMA.Basis2986503.Bridge

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

private def cross (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : E) (v q : F) : E →ₗ[ℝ] ℝ :=
  B u v • B.flip q - B u q • B.flip v

private theorem cross_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u a : E) (v q : F) :
    cross B u v q a = B u v * B a q - B u q * B a v := by
  simp [cross, smul_eq_mul]

private theorem exists_cross_ne_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (a b u : E)
    (c d v : F) (hB : B a c * B b d - B a d * B b c ≠ 0) (hu : B u v ≠ 0) :
    ∃ q : F, ∃ w : E, cross B u v q w ≠ 0 := by
  by_contra! h
  have he (q : F) (w : E) : B u v * B w q = B u q * B w v := by
    have hh := h q w
    rw [cross_apply] at hh
    exact sub_eq_zero.mp hh
  have hzero : (B u v)^2 * (B a c * B b d - B a d * B b c) = 0 := by
    calc
      _ = (B u v * B a c) * (B u v * B b d) -
          (B u v * B a d) * (B u v * B b c) := by ring
      _ = 0 := by
        rw [he c a, he d b, he d a, he c b]
        ring
  exact (mul_ne_zero (pow_ne_zero _ hu) hB) hzero

private theorem exists_both_ne_zero (f g : E →ₗ[ℝ] ℝ) (u v : E)
    (hu : f u ≠ 0) (hv : g v ≠ 0) :
    ∃ w : E, f w ≠ 0 ∧ g w ≠ 0 := by
  by_cases hgu : g u = 0
  · by_cases hfv : f v = 0
    · exact ⟨u + v, by simpa only [map_add, hfv, add_zero] using hu,
        by simpa only [map_add, hgu, zero_add] using hv⟩
    · exact ⟨v, hfv, hv⟩
  · exact ⟨u, hu, hgu⟩

private theorem common_pos (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u a : E) (v q : F)
    (h : cross B u v q a ≠ 0) :
    ∃ w : F, 0 < B u w ∧ 0 < B a w := by
  let δ := cross B u v q a
  let w : F := δ • ((B a q - B u q) • v + (B u v - B a v) • q)
  have hu : B u w = δ ^ 2 := by
    simp only [w, map_add, map_smul, smul_eq_mul, δ, cross_apply]
    ring
  have ha : B a w = δ ^ 2 := by
    simp only [w, map_add, map_smul, smul_eq_mul, δ, cross_apply]
    ring
  exact ⟨w, hu.symm ▸ sq_pos_of_ne_zero h, ha.symm ▸ sq_pos_of_ne_zero h⟩

private theorem affine_pos {s t p q : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hp : 0 < p) (hq : 0 < q) : 0 < s * p + t * q := by
  rcases hs.eq_or_lt with hzero | hpos
  · have htpos : 0 < t := by linarith
    simpa only [← hzero, zero_mul, zero_add] using mul_pos htpos hq
  · exact add_pos_of_pos_of_nonneg (mul_pos hpos hp) (mul_nonneg ht hq.le)

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul ℝ F]

private theorem move_right (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : E) (v w : F)
    (hv : 0 < B u v) (hw : 0 < B u w) :
    JoinedIn {z : E × F | 0 < B z.1 z.2} (u, v) (u, w) := by
  apply JoinedIn.of_segment_subset
  rintro _ ⟨s, t, hs, ht, hst, rfl⟩
  change 0 < B (s • u + t • u) (s • v + t • w)
  rw [← add_smul, hst, one_smul]
  simpa only [map_add, map_smul, smul_eq_mul] using
    (show 0 < s * B u v + t * B u w from affine_pos hs ht hst hv hw)

private theorem move_left (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u w : E) (v : F)
    (hu : 0 < B u v) (hw : 0 < B w v) :
    JoinedIn {z : E × F | 0 < B z.1 z.2} (u, v) (w, v) := by
  apply JoinedIn.of_segment_subset
  rintro _ ⟨s, t, hs, ht, hst, rfl⟩
  change 0 < B (s • u + t • w) (s • v + t • v)
  rw [← add_smul, hst, one_smul]
  change 0 < B.flip v (s • u + t • w)
  simpa only [map_add, map_smul, smul_eq_mul, LinearMap.flip_apply] using
    (show 0 < s * B u v + t * B w v from affine_pos hs ht hst hu hw)

/-- A real bilinear form with a nonzero two-by-two minor has path-connected positive locus. -/
theorem joinedIn_pos (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (hB : ∃ (a b : E) (c d : F), B a c * B b d - B a d * B b c ≠ 0)
    (x y : E × F) (hx : 0 < B x.1 x.2) (hy : 0 < B y.1 y.2) :
    JoinedIn {z : E × F | 0 < B z.1 z.2} x y := by
  obtain ⟨a, b, c, d, hab⟩ := hB
  obtain ⟨q, u, hu⟩ := exists_cross_ne_zero B a b x.1 c d x.2 hab hx.ne'
  obtain ⟨r, v, hv⟩ := exists_cross_ne_zero B a b y.1 c d y.2 hab hy.ne'
  obtain ⟨m, hmx, hmy⟩ := exists_both_ne_zero _ _ u v hu hv
  obtain ⟨w, hxw, hmw⟩ := common_pos B x.1 m x.2 q hmx
  obtain ⟨z, hyz, hmz⟩ := common_pos B y.1 m y.2 r hmy
  exact (move_right B x.1 x.2 w hx hxw).trans
    ((move_left B x.1 m w hxw hmw).trans
      ((move_right B m w z hmw hmz).trans
        ((move_left B m y.1 z hmz hyz).trans (move_right B y.1 z y.2 hyz hy))))

end OMA.Basis2986503.Bridge

namespace OMA.Basis2986503.Sweep

open Rows

variable {N : ℕ}

private abbrev last : Fin (N + 1) := Fin.last N

abbrev Family (V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))) := ∀ i, V i

abbrev Pair (V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))) := Family V × Family V

def matrix {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (x : Family V) : Mat (N + 1) := fun i => x i

theorem continuous_matrix {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))} :
    Continuous (matrix (V := V)) := by
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (continuous_apply i)

def mix {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (k : ℕ) (x : Pair V) : Family V :=
  fun i => if i.val < k ∨ (k = N ∧ i = last) then x.2 i else x.1 i

theorem mix_zero {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (hN : N ≠ 0) (x : Pair V) : mix 0 x = x.1 := by
  funext i
  simp [mix, Ne.symm hN]

theorem mix_last {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (x : Pair V) : mix N x = x.2 := by
  funext i
  by_cases h : i = last
  · simp [mix, h]
  have hi : i.val < N := by
    have hle := i.isLt
    by_contra! hn
    apply h
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  simp [mix, hi]

theorem mix_diag {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (k : ℕ) (x : Family V) : mix k (x, x) = x := by
  funext i
  simp [mix]

theorem mix_next {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (k : Fin N) (x : Pair V) (i : Fin (N + 1))
    (hi : i ≠ k.castSucc) (hl : i ≠ last) :
    mix (k.val + 1) x i = mix k.val x i := by
  have hik : i.val ≠ k.val := fun h => hi (Fin.ext h)
  simp only [mix, hl, and_false, or_false]
  simp only [show (i.val < k.val + 1) ↔ i.val < k.val by omega]

def sample {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (k : ℕ) (D : Fin (N + 1) → Option (Vec (N + 1))) (x : Pair V) : Mat (N + 1) :=
  fun i => (D i).getD (mix k x i)

def fixedRows (p q : Fin (N + 1)) (a b : Vec (N + 1)) :
    Fin (N + 1) → Option (Vec (N + 1)) :=
  fun i => if i = q then some b else if i = p then some a else none

theorem sample_empty {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (k : ℕ) (x : Pair V) : sample k (fun _ => none) x = matrix (mix k x) := rfl

theorem sample_fixed {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (k : ℕ) (x : Pair V) (p q : Fin (N + 1)) (a b : Vec (N + 1)) :
    sample k (fixedRows p q a b) x = frame (matrix (mix k x)) p q a b := by
  ext i j
  by_cases hq : i = q
  · subst i
    simp [sample, fixedRows, frame, Matrix.updateRow_apply]
  by_cases hp : i = p
  · subst i
    simp [sample, fixedRows, frame, Matrix.updateRow_apply, hq]
  simp [sample, fixedRows, frame, Matrix.updateRow_apply, hq, hp, matrix]

theorem continuous_sample {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (k : ℕ) (D : Fin (N + 1) → Option (Vec (N + 1))) :
    Continuous (sample (V := V) k D) := by
  apply continuous_pi
  intro i
  cases hd : D i with
  | some v => simpa [sample, hd] using (continuous_const : Continuous fun _ : Pair V => v)
  | none =>
    by_cases h : i.val < k ∨ (k = N ∧ i = last)
    · simpa [sample, hd, mix, h, Function.comp_def] using
        (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd) :
          Continuous fun x : Pair V => ((x.2 i : V i) : Vec (N + 1)))
    · simpa [sample, hd, mix, h, Function.comp_def] using
        (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst) :
          Continuous fun x : Pair V => ((x.1 i : V i) : Vec (N + 1)))

theorem sample_line {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (k : ℕ) (D : Fin (N + 1) → Option (Vec (N + 1)))
    (x y : Pair V) (t : ℝ) :
    sample k D ((1 - t) • x + t • y) =
      (1 - t) • sample k D x + t • sample k D y := by
  ext i j
  cases hd : D i with
  | none =>
    by_cases h : i.val < k ∨ (k = N ∧ i = last) <;>
      simp [sample, hd, mix, h, Matrix.add_apply, Matrix.smul_apply]
  | some v =>
    simp [sample, hd, Matrix.add_apply, Matrix.smul_apply]
    ring

theorem sample_poly {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (k : ℕ) (D : Fin (N + 1) → Option (Vec (N + 1))) (x y : Pair V) :
    ∃ p : Polynomial ℝ, ∀ t : ℝ,
      p.eval t = (sample k D ((1 - t) • x + t • y)).det := by
  refine ⟨(Dense.lineMatrix (sample k D x) (sample k D y)).det, fun t => ?_⟩
  rw [Dense.eval_lineMatrix_det, sample_line]

def good (V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))) (s : ℝ) : Set (Mat (N + 1)) :=
  {M | (∀ i, M i ∈ V i) ∧ 0 < s * M.det}

noncomputable def normalize (s : ℝ) (M : Mat (N + 1)) : Mat (N + 1) :=
  if 0 < s * M.det then M else M.updateRow last (-M last)

theorem normalize_other (s : ℝ) (M : Mat (N + 1)) (i : Fin (N + 1))
    (hi : i ≠ last) : normalize s M i = M i := by
  by_cases h : 0 < s * M.det <;> simp [normalize, h, Matrix.updateRow_ne hi]

theorem normalize_good {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    {s : ℝ} (hs : s ≠ 0) (M : Mat (N + 1)) (hm : ∀ i, M i ∈ V i)
    (hdet : M.det ≠ 0) : normalize s M ∈ good V s := by
  by_cases h : 0 < s * M.det
  · simpa [normalize, good, h] using hm
  simp only [normalize, if_neg h, good, Set.mem_setOf_eq]
  constructor
  · intro i
    by_cases hi : i = last
    · subst i
      simpa only [Matrix.updateRow_self] using (V last).neg_mem (hm last)
    · simpa only [Matrix.updateRow_ne hi] using hm i
  · have heq : (M.updateRow last (-M last)).det = -M.det := by
      rw [← neg_one_smul ℝ (M last), Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
      ring
    rw [heq, mul_neg]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) (mul_ne_zero hs hdet))

theorem frame_eq_of_frozen (M Z : Mat (N + 1)) {p q : Fin (N + 1)} (hpq : p ≠ q)
    (hz : ∀ i, i ≠ p → i ≠ q → Z i = M i) :
    frame M p q (Z p) (Z q) = Z := by
  ext i j
  by_cases hiq : i = q
  · subst i
    simp
  by_cases hip : i = p
  · subst i
    rw [frame_left M hpq]
  rw [frame_other M hip hiq, hz i hip hiq]

theorem joined_two {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    {s : ℝ} (hs : s ≠ 0) (M X Y : Mat (N + 1))
    {p q : Fin (N + 1)} (hpq : p ≠ q)
    (hX : X ∈ good V s) (hY : Y ∈ good V s)
    (hx : ∀ i, i ≠ p → i ≠ q → X i = M i)
    (hy : ∀ i, i ≠ p → i ≠ q → Y i = M i)
    (a a' : V p) (b b' : V q)
    (ha : (frame M p q a a').det ≠ 0) (hb : (frame M p q b b').det ≠ 0) :
    JoinedIn (good V s) X Y := by
  let B := signedPairing M hpq s (V p) (V q)
  let embed : V p × V q → Mat (N + 1) := fun z => frame M p q z.1 z.2
  have hemb : Continuous embed := by
    change Continuous (fun z : V p × V q => (M.updateRow p z.1).updateRow q z.2)
    exact (Continuous.matrix_updateRow p continuous_const
      (continuous_subtype_val.comp continuous_fst)).matrix_updateRow q
        (continuous_subtype_val.comp continuous_snd)
  let x : V p × V q := (⟨X p, hX.1 p⟩, ⟨X q, hX.1 q⟩)
  let y : V p × V q := (⟨Y p, hY.1 p⟩, ⟨Y q, hY.1 q⟩)
  have ex : embed x = X := frame_eq_of_frozen M X hpq hx
  have ey : embed y = Y := frame_eq_of_frozen M Y hpq hy
  have hp : 0 < B x.1 x.2 := by
    change 0 < s * (embed x).det
    rw [ex]
    exact hX.2
  have hq : 0 < B y.1 y.2 := by
    change 0 < s * (embed y).det
    rw [ey]
    exact hY.2
  have hj := Bridge.joinedIn_pos B (signedPairing_rank_two M hpq hs _ _ a a' b b' ha hb) x y hp hq
  have himg : embed '' {z : V p × V q | 0 < B z.1 z.2} ⊆ good V s := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨fun i => ?_, hz⟩
    change frame M p q z.1 z.2 i ∈ V i
    by_cases hiq : i = q
    · subst i
      simpa only [frame_right] using z.2.property
    by_cases hip : i = p
    · subst i
      simpa only [frame_left M hpq] using z.1.property
    rw [frame_other M hip hiq, ← hx i hip hiq]
    exact hX.1 i
  obtain ⟨γ, hγ⟩ := hj
  have hpath : JoinedIn (good V s) (embed x) (embed y) :=
    ⟨γ.map hemb, fun t => himg ⟨γ t, hγ t, rfl⟩⟩
  simpa only [ex, ey] using hpath

end OMA.Basis2986503.Sweep

namespace OMA.Basis2986503.Sweep

open Rows

variable {N : ℕ}

private theorem last_ne_cast (i : Fin N) : i.castSucc ≠ Fin.last N :=
  fun h => (Nat.ne_of_lt i.isLt) (congrArg Fin.val h)

private def keepFrozen {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (M : Mat (N + 1)) (p q : Fin (N + 1))
    (h : ∀ j, j ≠ p → j ≠ q → M j ∈ V j) : Family V :=
  fun j => if e : j = p ∨ j = q then 0 else
    ⟨M j, h j (fun he => e (Or.inl he)) (fun he => e (Or.inr he))⟩

private theorem frozenWitness {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (i : Fin N) (M : Mat (N + 1))
    (h : ∀ j, j ≠ i.castSucc → j ≠ Fin.last N → M j ∈ V j) :
    ∃ x : Pair V, sample i.val
      (fixedRows i.castSucc (Fin.last N) (M i.castSucc) (M (Fin.last N))) x = M := by
  let y := keepFrozen M i.castSucc (Fin.last N) h
  refine ⟨(y, y), ?_⟩
  rw [sample_fixed, mix_diag]
  apply frame_eq_of_frozen _ _ (last_ne_cast i)
  intro j hj hk
  simp [matrix, y, keepFrozen, hj, hk]

private theorem joined_ball {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    {s : ℝ} {x y : Family V} {r : ℝ} (hr : 0 < r) (hy : y ∈ Metric.ball x r)
    (h : Metric.ball x r ⊆ {z | 0 < s * (matrix z).det}) :
    JoinedIn (good V s) (matrix x) (matrix y) := by
  have hx : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hj : JoinedIn (Metric.ball x r) x y :=
    ((convex_ball x r).isPathConnected ⟨x, hx⟩).joinedIn x hx y hy
  obtain ⟨γ, hγ⟩ := hj
  exact ⟨γ.map continuous_matrix, fun t => ⟨fun i => (γ t i).property, h (hγ t)⟩⟩

theorem connect {V : Fin (N + 1) → Submodule ℝ (Vec (N + 1))}
    (hN : N ≠ 0) (hHall : ∀ S : Finset (Fin (N + 1)), S.Nonempty → S ≠ Finset.univ →
      S.card < Module.finrank ℝ ↥(⨆ j ∈ S, V j))
    (U W : Mat (N + 1)) (hU : ∀ j, U j ∈ V j) (hW : ∀ j, W j ∈ V j)
    (horient : 0 < U.det * W.det) :
    ∃ s : ℝ, JoinedIn (good V s) U W := by
  have hUdet : U.det ≠ 0 := left_ne_zero_of_mul (ne_of_gt horient)
  let q := Fin.last N
  let u : Family V := fun j => ⟨U j, hU j⟩
  let w : Family V := fun j => ⟨W j, hW j⟩
  let s : ℝ := if 0 < U.det then 1 else -1
  have hs : s ≠ 0 := by dsimp [s]; split <;> norm_num
  have hsu : 0 < s * U.det := by
    dsimp [s]
    split <;> rename_i h
    · simpa using h
    · simpa using lt_of_le_of_ne (le_of_not_gt h) hUdet
  have hsw : 0 < s * W.det := by
    dsimp [s]
    split <;> rename_i h
    · have hp := pos_of_mul_pos_right horient h.le
      simpa using hp
    · have hn := neg_of_mul_pos_right horient (le_of_not_gt h)
      simpa using hn
  choose A hAdet hArow hAend using
    fun i : Fin N => Hall.room V hHall U hU hUdet i.castSucc q (last_ne_cast i)
  choose B hBdet hBrow hBend using
    fun i : Fin N => Hall.room V hHall U hU hUdet q i.castSucc (last_ne_cast i).symm
  let a (i : Fin N) : V i.castSucc := ⟨A i i.castSucc, hArow i i.castSucc (last_ne_cast i)⟩
  let a' (i : Fin N) : V i.castSucc := ⟨A i q, hAend i⟩
  let b (i : Fin N) : V q := ⟨B i i.castSucc, hBend i⟩
  let b' (i : Fin N) : V q := ⟨B i q, hBrow i q (last_ne_cast i).symm⟩
  let I := Sum (Fin (N + 1)) (Fin N × Bool)
  let atStage : I → ℕ := fun j => j.elim Fin.val (fun it => it.1.val)
  let patch : I → Fin (N + 1) → Option (Vec (N + 1)) := fun j =>
    j.elim (fun _ _ => none) (fun it =>
      if it.2 then fixedRows it.1.castSucc q (a it.1) (a' it.1)
      else fixedRows it.1.castSucc q (b it.1) (b' it.1))
  let f (j : I) (x : Pair V) := (sample (atStage j) (patch j) x).det
  have hcont : ∀ j, Continuous (f j) :=
    fun j => (continuous_sample (atStage j) (patch j)).matrix_det
  have hwit : ∀ j, ∃ x, f j x ≠ 0 := by
    intro j
    rcases j with k | ⟨i, e⟩
    · refine ⟨(u, u), ?_⟩
      change (sample k.val (fun _ => none) (u, u)).det ≠ 0
      rw [sample_empty, mix_diag]
      exact hUdet
    · cases e
      · obtain ⟨x, hx⟩ := frozenWitness (V := V) i (B i)
          (fun j hj _ => hBrow i j hj)
        refine ⟨x, ?_⟩
        change (sample i.val (fixedRows i.castSucc q (B i i.castSucc) (B i q)) x).det ≠ 0
        rw [hx]
        exact hBdet i
      · obtain ⟨x, hx⟩ := frozenWitness (V := V) i (A i)
          (fun j _ hj => hArow i j hj)
        refine ⟨x, ?_⟩
        change (sample i.val (fixedRows i.castSucc q (A i i.castSucc) (A i q)) x).det ≠ 0
        rw [hx]
        exact hAdet i
  have hpoly := fun j x y => sample_poly (V := V) (atStage j) (patch j) x y
  let O : Set (Family V) := {z | 0 < s * (matrix z).det}
  have hopen : IsOpen O :=
    isOpen_lt continuous_const (continuous_const.mul continuous_matrix.matrix_det)
  obtain ⟨r, hr, hbu⟩ := Metric.isOpen_iff.mp hopen u hsu
  obtain ⟨t, ht, hbw⟩ := Metric.isOpen_iff.mp hopen w hsw
  obtain ⟨z, hz, htests⟩ := Dense.exists_in_open f hcont hwit hpoly
    (Metric.isOpen_ball.prod Metric.isOpen_ball)
    ⟨(u, w), Metric.mem_ball_self hr, Metric.mem_ball_self ht⟩
  have hfirst : JoinedIn (good V s) U (matrix z.1) := joined_ball hr hz.1 hbu
  have hlast : JoinedIn (good V s) (matrix z.2) W := (joined_ball ht hz.2 hbw).symm
  let raw (k : ℕ) := matrix (mix k z)
  let stage (k : ℕ) := normalize s (raw k)
  have hstage (k : ℕ) (hk : k ≤ N) : stage k ∈ good V s := by
    have hd := htests (Sum.inl ⟨k, by omega⟩)
    change (raw k).det ≠ 0 at hd
    exact normalize_good hs _ (fun i => (mix k z i).property) hd
  have hzero : stage 0 = matrix z.1 := by
    simp only [stage, raw, mix_zero hN, normalize]
    exact if_pos (hbu hz.1)
  have hend : stage N = matrix z.2 := by
    simp only [stage, raw, mix_last, normalize]
    exact if_pos (hbw hz.2)
  have hstep (i : Fin N) : JoinedIn (good V s) (stage i.val) (stage (i.val + 1)) := by
    have ha := htests (Sum.inr (i, true))
    have hb := htests (Sum.inr (i, false))
    change (sample i.val (fixedRows i.castSucc q (a i) (a' i)) z).det ≠ 0 at ha
    change (sample i.val (fixedRows i.castSucc q (b i) (b' i)) z).det ≠ 0 at hb
    rw [sample_fixed] at ha hb
    refine joined_two hs (raw i.val) _ _ (last_ne_cast i)
      (hstage i.val i.isLt.le) (hstage (i.val + 1) i.isLt)
      (fun j _ hj => normalize_other s _ j hj) ?_ (a i) (a' i) (b i) (b' i) ha hb
    intro j hp hq
    rw [show stage (i.val + 1) j = raw (i.val + 1) j from normalize_other s _ j hq]
    exact congrArg (fun x : V j => (x : Vec (N + 1))) (mix_next i z j hp hq)
  have hchain (k : ℕ) (hk : k ≤ N) : JoinedIn (good V s) (stage 0) (stage k) := by
    induction k with
    | zero => exact JoinedIn.refl (hstage 0 hk)
    | succ k ih =>
      exact (ih (by omega)).trans (hstep ⟨k, by omega⟩)
  refine ⟨s, hfirst.trans ?_⟩
  have hmid := hchain N le_rfl
  rw [hzero, hend] at hmid
  exact hmid.trans hlast

end OMA.Basis2986503.Sweep

open OMA.Basis2986503 in
theorem OMA.solution : type_of% @OMA.S_mse_2986503.main := by
  intro n m hm hmn
  cases n with
  | zero => omega
  | succ N =>
    intro V hV hspan U W hU hW hdet
    have hN : N ≠ 0 := by omega
    obtain ⟨s, hjoin⟩ := Sweep.connect hN (Hall.strictHall _ m hm hmn V hV hspan)
      U W hU hW hdet
    refine ⟨hjoin.somePath, hjoin.somePath.continuous, hjoin.somePath.source,
      hjoin.somePath.target, ?_, ?_⟩
    · exact fun t j => (hjoin.somePath_mem t).1 j
    · intro t hzero
      have hpos := (hjoin.somePath_mem t).2
      rw [hzero, mul_zero] at hpos
      exact (lt_irrefl _ hpos)
