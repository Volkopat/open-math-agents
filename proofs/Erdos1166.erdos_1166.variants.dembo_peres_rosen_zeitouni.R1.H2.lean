import OMAReductions.R_Erdos1166_erdos_1166_variants_dembo_peres_rosen_zeitouni_R1

/-!
# Summable lower deviations for planar random-walk maximal local time

We prove `H2` of `Erdos1166.erdos_1166.variants.dembo_peres_rosen_zeitouni.R1` via
multiscale truncated second moment on geometrically weighted local times together with
independent block amplification.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Real
open Erdos1165 Erdos1166

namespace OMA.H2DPRZ

/-- Partial sums of a step sequence. -/
def pos (y : ℕ → ℤ × ℤ) (t : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range t, y i

/-- Shift of a step sequence by `t` steps. -/
def sh (t : ℕ) (y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ y (t + i)

/-- Sample path of steps. -/
def path {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : ℕ → ℤ × ℤ := fun i ↦ X i ω

/-- `A` depends only on the first `m` steps. -/
def Det (m : ℕ) (A : Set (ℕ → ℤ × ℤ)) : Prop :=
  ∀ y y' : ℕ → ℤ × ℤ, (∀ i < m, y i = y' i) → y ∈ A → y' ∈ A

lemma pos_zero (y : ℕ → ℤ × ℤ) : pos y 0 = 0 := by simp [pos]

lemma pos_succ (y : ℕ → ℤ × ℤ) (t : ℕ) : pos y (t + 1) = pos y t + y t :=
  Finset.sum_range_succ _ _

lemma pos_shift (y : ℕ → ℤ × ℤ) (t s : ℕ) : pos y (t + s) = pos y t + pos (sh t y) s :=
  Finset.sum_range_add _ _ _

lemma pos_congr {y y' : ℕ → ℤ × ℤ} {m t : ℕ} (h : ∀ i < m, y i = y' i) (ht : t ≤ m) :
    pos y t = pos y' t :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

lemma sh_zero (y : ℕ → ℤ × ℤ) : sh 0 y = y := funext fun i ↦ by simp [sh]

lemma sh_sh (a b : ℕ) (y : ℕ → ℤ × ℤ) : sh a (sh b y) = sh (b + a) y :=
  funext fun i ↦ by simp [sh, add_assoc]

def ext (m : ℕ) (z : Fin m → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ if h : i < m then z ⟨i, h⟩ else 0

lemma map_window {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    Measure.map (fun ω (i : Fin n) ↦ X (j + i) ω) ℙ =
      Measure.pi (fun _ : Fin n ↦ Measure.map (X 0) ℙ) := by
  have hind : ProbabilityTheory.iIndepFun (fun i : Fin n ↦ X (j + i)) ℙ :=
    hX.indep.precomp (g := fun i : Fin n ↦ j + (i : ℕ)) fun a b h ↦ Fin.ext (by simpa using h)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    fun i ↦ (hX.measurable _).aemeasurable).mp hind]
  congr 1
  funext i
  exact Eq.trans (hX.isUniform (j + i)) (Eq.symm (hX.isUniform 0))

lemma det_pre {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A)
    (j : ℕ) : {ω | sh j (path X ω) ∈ A} =
      (fun ω (i : Fin m) ↦ X (j + i) ω) ⁻¹' {z | ext m z ∈ A} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]

lemma meas_window {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (m j : ℕ) :
    Measurable (fun ω (i : Fin m) ↦ X (j + i) ω) :=
  measurable_pi_iff.mpr fun _ ↦ hX.measurable _

lemma det_meas {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A) (j : ℕ) :
    MeasurableSet {ω | sh j (path X ω) ∈ A} := by
  rw [det_pre X hA j]
  exact meas_window hX m j (Set.to_countable _).measurableSet

lemma path_eq {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (A : Set (ℕ → ℤ × ℤ)) :
    {ω | path X ω ∈ A} = {ω | sh 0 (path X ω) ∈ A} := by
  simp only [sh_zero]

lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)}
    (hA : Det m A) (j : ℕ) :
    ℙ {ω | sh j (path X ω) ∈ A} = ℙ {ω | path X ω ∈ A} := by
  have hT : MeasurableSet {z : Fin m → ℤ × ℤ | ext m z ∈ A} := (Set.to_countable _).measurableSet
  rw [path_eq, det_pre X hA, det_pre X hA, ← Measure.map_apply (meas_window hX m j) hT,
    ← Measure.map_apply (meas_window hX m 0) hT, map_window hX, map_window hX]

lemma preA {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det t A) :
    {ω | path X ω ∈ A} = (fun ω (i : Finset.range t) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : i ∈ Finset.range t then z ⟨i, h⟩ else 0) ∈ A} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [hi, path]
  · exact hA _ _ fun i hi ↦ by simp [hi, path]

lemma preB {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t s : ℕ} {B : Set (ℕ → ℤ × ℤ)} (hB : Det s B) :
    {ω | sh t (path X ω) ∈ B} = (fun ω (i : Finset.Ico t (t + s)) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then z ⟨t + i, h⟩ else 0) ∈ B} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have key : ∀ i < s, sh t (path X ω) i =
      (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then
        (fun (i : Finset.Ico t (t + s)) ↦ X i ω) ⟨t + i, h⟩ else 0) i := by
    intro i hi
    have hm : t + i ∈ Finset.Ico t (t + s) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    simp [hm, sh, path]
  constructor
  · exact hB _ _ key
  · exact hB _ _ fun i hi ↦ (key i hi).symm

lemma prob_block {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {t s : ℕ}
    {A B : Set (ℕ → ℤ × ℤ)} (hA : Det t A) (hB : Det s B) :
    ℙ {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      ℙ {ω | path X ω ∈ A} * ℙ {ω | path X ω ∈ B} := by
  have hdisj : Disjoint (Finset.range t) (Finset.Ico t (t + s)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    omega
  have hind := hX.indep.indepFun_finset (Finset.range t) (Finset.Ico t (t + s)) hdisj
    hX.measurable
  have hset : {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      {ω | path X ω ∈ A} ∩ {ω | sh t (path X ω) ∈ B} := rfl
  rw [hset, ← prob_shift hX hB t, preA X hA, preB X hB]
  exact hind.measure_inter_preimage_eq_mul _ _ (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet

lemma meas_block {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {t s : ℕ} {A B : Set (ℕ → ℤ × ℤ)}
    (hA : Det t A) (hB : Det s B) :
    MeasurableSet {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} := by
  have h1 : MeasurableSet {ω | path X ω ∈ A} := by rw [path_eq]; exact det_meas hX hA 0
  exact h1.inter (det_meas hX hB t)

/-- Number of `±1` paths of length `t` ending at `u`. -/
def c : ℕ → ℤ → ℕ
  | 0, u => if u = 0 then 1 else 0
  | t + 1, u => c t (u - 1) + c t (u + 1)

lemma c_neg : ∀ (t : ℕ) (u : ℤ), u < -(t : ℤ) → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_neg t (u - 1) (by push_cast at h; omega), c_neg t (u + 1) (by push_cast at h; omega)]

lemma c_symm : ∀ (t : ℕ) (u : ℤ), c t (-u) = c t u
  | 0, u => by simp [c]
  | t + 1, u => by
    simp only [c]
    rw [show -u - 1 = -(u + 1) by ring, show -u + 1 = -(u - 1) by ring, c_symm t, c_symm t]
    ring

lemma c_far : ∀ (t : ℕ) (a : ℤ), (t : ℤ) < |a| → c t a = 0
  | 0, a, h => by simp [c, abs_pos.mp (show 0 < |a| from h)]
  | t + 1, a, h => by
    simp only [c]
    rw [c_far t (a - 1) (by
      push_cast at h
      rcases lt_abs.mp h with hp | hn <;> apply lt_abs.mpr <;> omega),
      c_far t (a + 1) (by
      push_cast at h
      rcases lt_abs.mp h with hp | hn <;> apply lt_abs.mpr <;> omega), add_zero]

lemma c_odd : ∀ (t : ℕ) (u : ℤ), ((t : ℤ) + u) % 2 = 1 → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_odd t (u - 1) (by push_cast at h; omega), c_odd t (u + 1) (by push_cast at h; omega)]

lemma c_choose : ∀ (t i : ℕ), c t (2 * (i : ℤ) - t) = t.choose i
  | 0, i => by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [c]
    · simp [c, Nat.choose_eq_zero_of_lt h]; omega
  | t + 1, 0 => by
    simp only [c, Nat.choose_zero_right]
    rw [c_neg t _ (by push_cast; omega)]
    have := c_choose t 0
    simp only [Nat.choose_zero_right] at this
    rw [show (2 * ((0 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((0 : ℕ) : ℤ) - (t : ℤ) by
      push_cast; ring, this]
  | t + 1, i + 1 => by
    simp only [c, Nat.choose_succ_succ]
    have h1 := c_choose t i
    have h2 := c_choose t (i + 1)
    rw [show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) - 1) = 2 * (i : ℤ) - t by push_cast; ring,
      show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((i + 1 : ℕ) : ℤ) - t by
        push_cast; ring, h1, h2]

lemma c_even (j : ℕ) : c (2 * j) 0 = j.centralBinom := by
  have := c_choose (2 * j) j
  rw [show (2 * (j : ℤ) - ((2 * j : ℕ) : ℤ)) = 0 by push_cast; ring] at this
  rw [this, Nat.centralBinom_eq_two_mul_choose]

lemma c_two_mul_nat (j k : ℕ) : c (2 * j) (2 * (k : ℤ)) = (2 * j).choose (j + k) := by
  by_cases hkj : k ≤ j
  · have h := c_choose (2 * j) (j + k)
    rw [show 2 * ((j + k : ℕ) : ℤ) - ((2 * j : ℕ) : ℤ) = 2 * (k : ℤ) by push_cast; ring] at h
    exact h
  · rw [c_far (2 * j) (2 * (k : ℤ)) (by rw [abs_of_nonneg (by positivity)]; push_cast; omega),
      Nat.choose_eq_zero_of_lt (by omega)]

lemma c_two_mul (j : ℕ) (u : ℤ) : c (2 * j) (2 * u) = (2 * j).choose (j + u.natAbs) := by
  rcases le_or_gt 0 u with hu | hu
  · have h : u = (u.natAbs : ℤ) := (Int.natAbs_of_nonneg hu).symm
    conv_lhs => rw [h]
    exact c_two_mul_nat j u.natAbs
  · have h : -u = (u.natAbs : ℤ) := by omega
    rw [← c_symm, show -(2 * u) = 2 * (-u) by ring, h]
    exact c_two_mul_nat j u.natAbs

lemma c_step (t : ℕ) (a b : ℤ) :
    c (t + 1) (a + b) * c (t + 1) (a - b) =
      c t ((a - 1) + b) * c t ((a - 1) - b) + c t ((a + 1) + b) * c t ((a + 1) - b) +
      c t (a + (b - 1)) * c t (a - (b - 1)) + c t (a + (b + 1)) * c t (a - (b + 1)) := by
  simp only [c]
  rw [show a - 1 + b = a + b - 1 by ring, show a - 1 - b = a - b - 1 by ring,
    show a + 1 + b = a + b + 1 by ring, show a + 1 - b = a - b + 1 by ring,
    show a + (b - 1) = a + b - 1 by ring, show a - (b - 1) = a - b + 1 by ring,
    show a + (b + 1) = a + b + 1 by ring, show a - (b + 1) = a - b - 1 by ring]
  ring

def stepsF : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

lemma steps_eq : steps = (stepsF : Set (ℤ × ℤ)) := by
  simp [steps, stepsF]

lemma prob_step {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) (S : Set (ℤ × ℤ)) :
    ℙ (X k ⁻¹' S) = (4 : ℝ≥0∞)⁻¹ * Measure.count (steps ∩ S) := by
  have hu : Measure.map (X k) ℙ = ProbabilityTheory.cond Measure.count steps := hX.isUniform k
  rw [← Measure.map_apply (hX.measurable k) (Set.to_countable S).measurableSet, hu,
    ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet, steps_eq,
    Measure.count_apply_finset]
  rfl

lemma prob_step_eq {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) {e : ℤ × ℤ} (he : e ∈ steps) :
    ℙ (X k ⁻¹' {e}) = (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_step hX, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr he),
    Measure.count_singleton, mul_one]

lemma prob_step_bad {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) : ℙ (X k ⁻¹' stepsᶜ) = 0 := by
  rw [prob_step hX, Set.inter_compl_self, measure_empty, mul_zero]

lemma det_pos (t : ℕ) (z : ℤ × ℤ) : Det t {y | pos y t = z} := fun y y' h hy ↦ by
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [← pos_congr h le_rfl, hy]

lemma det_zero (e : ℤ × ℤ) : Det 1 {y | y 0 = e} := fun y y' h hy ↦ by
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [← h 0 one_pos, hy]

lemma prob_pos_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (x e : ℤ × ℤ)
    (he : e ∈ steps) :
    ℙ {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}} =
      ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_block hX (det_pos t (x - e)) (det_zero e)]
  congr 1
  exact prob_step_eq hX 0 he

lemma prob_pos_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t ≤
      ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞)
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      simp only [c, add_zero, sub_self, if_true, mul_one, Nat.cast_one]
      exact prob_le_one
    · have : {ω | pos (path X ω) 0 = (a, b)} = ∅ := by
        ext ω
        simp only [pos, Finset.range_zero, Finset.sum_empty, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        exact fun h' ↦ h h'.symm
      rw [this, measure_empty]
      simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hsub : {ω | pos (path X ω) (t + 1) = x} ⊆
        (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ∪ X t ⁻¹' stepsᶜ := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, pos_succ] at hω
      by_cases hs : X t ω ∈ steps
      · have hx : pos (path X ω) t = x - X t ω := by rw [← hω]; simp [path]
        have hE : ω ∈ E (X t ω) := ⟨hx, rfl⟩
        simp only [steps, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with h | h | h | h <;> rw [h] at hE <;> simp [hE]
      · exact Or.inr hs
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) ≤
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      apply le_of_eq
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have hm : ℙ {ω | pos (path X ω) (t + 1) = x} ≤
        ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) := by
      refine (measure_mono hsub).trans ?_
      refine (measure_union_le _ _).trans ?_
      rw [prob_step_bad hX t, add_zero]
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      exact measure_union_le _ _
    calc ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1)
        ≤ (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) :=
          by gcongr
      _ = ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by ring
      _ ≤ ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
        gcongr
        · refine (hE _ h1).trans ?_
          have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h2).trans ?_
          have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h3).trans ?_
          have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h4).trans ?_
          have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
      _ = ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞) := by
        rw [c_step]; push_cast; ring

lemma prob_pos_ge {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞) ≤
      ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      have : {ω | pos (path X ω) 0 = ((0 : ℤ), (0 : ℤ))} = Set.univ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, pos_zero]; rfl
      rw [this, measure_univ]
      simp [c]
    · have hc : c 0 (a + b) * c 0 (a - b) = 0 := by
        simp only [c]
        by_cases ha : a + b = 0
        · have : a - b ≠ 0 := by
            intro hb; apply h; ext <;> simp <;> omega
          simp [this]
        · simp [ha]
      rw [hc]; simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hEm : ∀ e, MeasurableSet (E e) := fun e ↦ meas_block hX (det_pos t _) (det_zero e)
    have hsub : (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ⊆
        {ω | pos (path X ω) (t + 1) = x} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, pos_succ]
      have key : ∀ e, ω ∈ E e → pos (path X ω) t + path X ω t = x := by
        rintro e ⟨h1, h2⟩
        simp only [Set.mem_ofPred_eq] at h1 h2
        have : path X ω t = e := h2
        rw [h1, this]; abel
      rcases hω with ((h | h) | h) | h <;> exact key _ h
    have hd : ∀ e e', e ≠ e' → Disjoint (E e) (E e') := by
      intro e e' hne
      rw [Set.disjoint_left]
      rintro ω ⟨-, h1⟩ ⟨-, h2⟩
      exact hne ((show path X ω t = e from h1).symm.trans h2)
    have hsum : ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) ≤
        ℙ {ω | pos (path X ω) (t + 1) = x} := by
      refine le_trans (le_of_eq ?_) (measure_mono hsub)
      rw [measure_union _ (hEm _), measure_union _ (hEm _), measure_union _ (hEm _)]
      · exact hd _ _ (by decide)
      · exact Disjoint.union_left (hd _ _ (by decide)) (hd _ _ (by decide))
      · exact Disjoint.union_left (Disjoint.union_left (hd _ _ (by decide))
          (hd _ _ (by decide))) (hd _ _ (by decide))
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) =
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    calc ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞)
        = ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
          rw [c_step]; push_cast; ring
      _ ≤ ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by
        rw [hE _ h1, hE _ h2, hE _ h3, hE _ h4]
        gcongr
        · have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
      _ = (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) := by ring
      _ ≤ ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1) := by gcongr

noncomputable def p {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (z : ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = z}).toReal

lemma p_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (z : ℤ × ℤ) (t : ℕ) :
    0 ≤ p X z t := ENNReal.toReal_nonneg

lemma p_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℤ × ℤ) (z : ℤ × ℤ) (t : ℕ) : p X z t ≤ 1 := by
  unfold p
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := (ℙ : Measure Ω)))

lemma p_count {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (a b : ℤ) (t : ℕ) :
    p X (a, b) t * 4 ^ t = (c t (a + b) : ℝ) * (c t (a - b) : ℝ) := by
  have h := le_antisymm (prob_pos_le hX t a b) (prob_pos_ge hX t a b)
  have he := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, Nat.cast_mul] at he
  simpa only [p, show (4 : ℝ≥0∞).toReal = 4 by norm_num] using he

lemma p_zero_at {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (_hX : IsSimpleRandomWalkSteps X) (z : ℤ × ℤ) :
    p X z 0 = if z = 0 then 1 else 0 := by
  unfold p
  split_ifs with hz
  · subst hz
    have : {ω : Ω | pos (path X ω) 0 = 0} = Set.univ := by
      ext ω; simp [pos_zero]
    rw [this, measure_univ, ENNReal.toReal_one]
  · have : {ω : Ω | pos (path X ω) 0 = z} = ∅ := by
      ext ω; simp [pos_zero, Ne.symm hz]
    rw [this, measure_empty, ENNReal.toReal_zero]

lemma p_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (z : ℤ × ℤ) (t : ℕ) :
    p X z (t + 1) = (1 / 4 : ℝ) * ∑ e ∈ stepsF, p X (z - e) t := by
  have h4 : (0 : ℝ) < 4 ^ (t + 1) := by positivity
  apply mul_right_cancel₀ h4.ne'
  rw [p_count hX z.1 z.2 (t + 1), ← Nat.cast_mul, c_step]
  have hs : ∑ e ∈ stepsF, p X (z - e) t =
      p X (z.1 - 1, z.2) t + p X (z.1 + 1, z.2) t +
      p X (z.1, z.2 - 1) t + p X (z.1, z.2 + 1) t := by
    have : stepsF =
        insert (1, 0) (insert (-1, 0) (insert (0, 1) {(0, -1)})) := rfl
    rw [this, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    have e1 : z - (1, 0) = (z.1 - 1, z.2) := by ext <;> simp
    have e2 : z - (-1, 0) = (z.1 + 1, z.2) := by ext <;> simp
    have e3 : z - (0, 1) = (z.1, z.2 - 1) := by ext <;> simp
    have e4 : z - (0, -1) = (z.1, z.2 + 1) := by ext <;> simp
    rw [e1, e2, e3, e4]
    ring
  rw [hs, pow_succ]
  have c1 := p_count hX (z.1 - 1) z.2 t
  have c2 := p_count hX (z.1 + 1) z.2 t
  have c3 := p_count hX z.1 (z.2 - 1) t
  have c4 := p_count hX z.1 (z.2 + 1) t
  push_cast
  linarith

lemma p_neg {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (z : ℤ × ℤ) (t : ℕ) :
    p X (-z) t = p X z t := by
  have h4 : (0 : ℝ) < 4 ^ t := by positivity
  apply mul_right_cancel₀ h4.ne'
  have h1 := p_count hX (-z.1) (-z.2) t
  have h2 := p_count hX z.1 z.2 t
  have hz : (-z.1, -z.2) = -z := by ext <;> simp
  rw [hz] at h1
  rw [h1, h2, show -z.1 + -z.2 = -(z.1 + z.2) by ring,
    show -z.1 - -z.2 = -(z.1 - z.2) by ring, c_symm, c_symm]

/-- Wallis bounds on central binomial squared. -/
lemma cb_sq_le (j : ℕ) (hj : 1 ≤ j) :
    ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j ≤ 1 / (Real.pi * j) := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.le_W j
  have h1 : Real.pi * j / (2 * j + 1) ≤ (2 * (j : ℝ) + 1) / (2 * j + 2) * (Real.pi / 2) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * (j : ℝ) + 1) * Real.pi * (2 * j + 1) =
        Real.pi * j * ((2 * j + 2) * 2) + Real.pi := by ring
    rw [this]
    linarith [Real.pi_pos]
  have h2 : Real.pi * j ≤ Real.Wallis.W j * (2 * j + 1) := by
    have := h1.trans hle
    rwa [div_le_iff₀ (by positivity)] at this
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc (j.centralBinom : ℝ) ^ 2 * (Real.pi * j)
      ≤ (j.centralBinom : ℝ) ^ 2 * (Real.Wallis.W j * (2 * j + 1)) := by gcongr
    _ = Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by ring

lemma cb_sq_ge (j : ℕ) : 1 / (Real.pi * ((j : ℝ) + 1)) ≤ ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.W_le j
  have hpi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1))
      ≤ Real.pi / 2 * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by gcongr
    _ ≤ (j.centralBinom : ℝ) ^ 2 * (Real.pi * ((j : ℝ) + 1)) := by nlinarith

/-- Binomial upper and lower Gaussian bounds around `j`. -/
lemma choose_upper_exp (j : ℕ) (hj : 1 ≤ j) :
    ∀ k : ℕ, ((2 * j).choose (j + k) : ℝ) ≤
      (j.centralBinom : ℝ) * Real.exp (-((k : ℝ) ^ 2 / (2 * j)))
  | 0 => by simp [Nat.centralBinom_eq_two_mul_choose]
  | k + 1 => by
    by_cases hkj : j ≤ k
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
      positivity
    · push Not at hkj
      have ih := choose_upper_exp j hj k
      have hj' : (0 : ℝ) < j := by exact_mod_cast hj
      have hrec := Nat.choose_succ_right_eq (2 * j) (j + k)
      have hsub : 2 * j - (j + k) = j - k := by omega
      rw [hsub] at hrec
      have hrec' : ((2 * j).choose (j + k + 1) : ℝ) * ((j + k + 1 : ℕ) : ℝ) =
          ((2 * j).choose (j + k) : ℝ) * ((j - k : ℕ) : ℝ) := by exact_mod_cast hrec
      have hpos : (0 : ℝ) < ((j + k + 1 : ℕ) : ℝ) := by positivity
      have hf : ((2 * j).choose (j + (k + 1)) : ℝ) =
          ((2 * j).choose (j + k) : ℝ) * (((j - k : ℕ) : ℝ) / ((j + k + 1 : ℕ) : ℝ)) := by
        rw [show j + (k + 1) = j + k + 1 by omega, mul_div_assoc', eq_div_iff hpos.ne']
        exact hrec'
      rw [hf]
      have hrat : (((j - k : ℕ) : ℝ) / ((j + k + 1 : ℕ) : ℝ)) ≤
          Real.exp (-((2 * (k : ℝ) + 1) / (2 * j))) := by
        have h1 : (((j - k : ℕ) : ℝ) / ((j + k + 1 : ℕ) : ℝ)) ≤
            1 - (2 * (k : ℝ) + 1) / (2 * j) := by
          rw [Nat.cast_sub hkj.le]
          push_cast
          rw [div_le_iff₀ (by positivity)]
          have hk' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
          have hmul : (1 - (2 * (k : ℝ) + 1) / (2 * j)) * (j + k + 1) =
              (j - k) + (2 * k + 1) * (j - k - 1) / (2 * j) := by
            field_simp
            ring
          rw [hmul]
          have hnn : 0 ≤ (2 * (k : ℝ) + 1) * (j - k - 1) / (2 * j) :=
            div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
          linarith
        exact h1.trans (Real.one_sub_le_exp_neg _)
      have hnn : 0 ≤ (((j - k : ℕ) : ℝ) / ((j + k + 1 : ℕ) : ℝ)) := by positivity
      calc ((2 * j).choose (j + k) : ℝ) * (((j - k : ℕ) : ℝ) / ((j + k + 1 : ℕ) : ℝ))
          ≤ ((j.centralBinom : ℝ) * Real.exp (-((k : ℝ) ^ 2 / (2 * j)))) *
              Real.exp (-((2 * (k : ℝ) + 1) / (2 * j))) :=
            mul_le_mul ih hrat hnn (by positivity)
        _ = (j.centralBinom : ℝ) * Real.exp (-(((k + 1 : ℕ) : ℝ) ^ 2 / (2 * j))) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            push_cast
            ring

lemma choose_near (j : ℕ) (hj : 1 ≤ j) :
    ∀ k : ℕ, k ≤ j →
      (j.centralBinom : ℝ) * (1 - 2 * (k : ℝ) ^ 2 / j) ≤ ((2 * j).choose (j + k) : ℝ)
  | 0, _ => by simp [Nat.centralBinom_eq_two_mul_choose]
  | k + 1, hk => by
    have ih := choose_near j hj k (by omega)
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    have hrec := Nat.choose_succ_right_eq (2 * j) (j + k)
    have hrec' : ((2 * j).choose (j + k + 1) : ℝ) * ((j + k + 1 : ℕ) : ℝ) =
        ((2 * j).choose (j + k) : ℝ) * ((j - k : ℕ) : ℝ) := by
      have : 2 * j - (j + k) = j - k := by omega
      rw [this] at hrec
      exact_mod_cast hrec
    rw [Nat.cast_sub (show k ≤ j by omega)] at hrec'
    push_cast at hrec'
    have hpos : (0 : ℝ) < j + k + 1 := by positivity
    have hcb : (0 : ℝ) ≤ j.centralBinom := by positivity
    have hf : ((2 * j).choose (j + k + 1) : ℝ) =
        ((2 * j).choose (j + k) : ℝ) * ((j - k) / (j + k + 1)) := by
      rw [mul_div_assoc', eq_div_iff hpos.ne']
      exact hrec'
    rw [show j + (k + 1) = j + k + 1 by ring, hf]
    have hρ : 1 - (2 * k + 1) / (j : ℝ) ≤ ((j : ℝ) - k) / (j + k + 1) := by
      rw [le_div_iff₀ hpos, sub_mul, div_mul_eq_mul_div, one_mul]
      have : (2 * (k : ℝ) + 1) * (j + k + 1) / j ≥ 2 * k + 1 := by
        rw [ge_iff_le, le_div_iff₀ hj']; nlinarith
      linarith
    rcases le_or_gt (1 - 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / j) 0 with hT | hT
    · have hk1 : (k : ℝ) + 1 ≤ j := by exact_mod_cast hk
      have hρ0 : 0 ≤ ((j : ℝ) - k) / (j + k + 1) := div_nonneg (by linarith) (by positivity)
      exact (mul_nonpos_of_nonneg_of_nonpos hcb hT).trans (by positivity)
    have hT' : 2 * ((k + 1 : ℕ) : ℝ) ^ 2 < j := (div_lt_one hj').mp (by linarith)
    push_cast at hT'
    have hb : 0 ≤ 1 - (2 * (k : ℝ) + 1) / j := by
      rw [sub_nonneg, div_le_one hj']; nlinarith
    calc (j.centralBinom : ℝ) * (1 - 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / j)
        ≤ (j.centralBinom : ℝ) * ((1 - 2 * (k : ℝ) ^ 2 / j) * (1 - (2 * k + 1) / (j : ℝ))) := by
          gcongr
          have e : (1 - 2 * (k : ℝ) ^ 2 / j) * (1 - (2 * k + 1) / (j : ℝ)) =
              1 - (2 * k ^ 2 + 2 * k + 1) / j + 2 * k ^ 2 / j * ((2 * k + 1) / j) := by ring
          rw [e]
          have : 0 ≤ 2 * (k : ℝ) ^ 2 / j * ((2 * k + 1) / j) := by positivity
          have h2 : (2 * (k : ℝ) ^ 2 + 2 * k + 1) / j ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / j := by
            gcongr; push_cast; nlinarith
          linarith
      _ = ((j.centralBinom : ℝ) * (1 - 2 * (k : ℝ) ^ 2 / j)) * (1 - (2 * k + 1) / (j : ℝ)) := by
          ring
      _ ≤ ((2 * j).choose (j + k) : ℝ) * (1 - (2 * k + 1) / (j : ℝ)) := by gcongr
      _ ≤ ((2 * j).choose (j + k) : ℝ) * (((j : ℝ) - k) / (j + k + 1)) := by gcongr

/-- Rotated even sublattice map `rot (u, v) = (u + v, u - v)`. -/
def rot (q : ℤ × ℤ) : ℤ × ℤ := (q.1 + q.2, q.1 - q.2)

def rnorm (q : ℤ × ℤ) : ℕ := max q.1.natAbs q.2.natAbs

lemma rot_zero : rot 0 = 0 := rfl

lemma rot_sub (q₁ q₂ : ℤ × ℤ) : rot (q₁ - q₂) = rot q₁ - rot q₂ := by
  ext <;> simp [rot] <;> ring

lemma rot_injective : Function.Injective rot := by
  intro q₁ q₂ h
  have h1 : q₁.1 + q₁.2 = q₂.1 + q₂.2 := congrArg Prod.fst h
  have h2 : q₁.1 - q₁.2 = q₂.1 - q₂.2 := congrArg Prod.snd h
  ext <;> omega

lemma p_rot_odd {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (q : ℤ × ℤ) (j : ℕ) :
    p X (rot q) (2 * j + 1) = 0 := by
  have h4 : (0 : ℝ) < 4 ^ (2 * j + 1) := by positivity
  have hc := p_count hX (q.1 + q.2) (q.1 - q.2) (2 * j + 1)
  have hsum : (q.1 + q.2) + (q.1 - q.2) = 2 * q.1 := by ring
  rw [hsum, c_odd (2 * j + 1) (2 * q.1) (by push_cast; omega)] at hc
  simp only [Nat.cast_zero, zero_mul] at hc
  exact mul_eq_zero.mp hc |>.resolve_right h4.ne'

lemma p_rot_even {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (q : ℤ × ℤ) (j : ℕ) :
    p X (rot q) (2 * j) =
      (((2 * j).choose (j + q.1.natAbs) : ℝ) * ((2 * j).choose (j + q.2.natAbs) : ℝ)) / 16 ^ j := by
  have hc := p_count hX (q.1 + q.2) (q.1 - q.2) (2 * j)
  rw [show (q.1 + q.2) + (q.1 - q.2) = 2 * q.1 by ring,
    show (q.1 + q.2) - (q.1 - q.2) = 2 * q.2 by ring,
    c_two_mul, c_two_mul, pow_mul, show (4 : ℝ) ^ 2 = 16 by norm_num] at hc
  rw [eq_div_iff (by positivity)]
  exact hc

lemma p_rot_even_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (q : ℤ × ℤ) (j : ℕ) (hj : 1 ≤ j) :
    p X (rot q) (2 * j) ≤
      (1 / (Real.pi * j)) * Real.exp (-((rnorm q : ℝ) ^ 2 / (2 * j))) := by
  rw [p_rot_even hX]
  have h1 := choose_upper_exp j hj q.1.natAbs
  have h2 := choose_upper_exp j hj q.2.natAbs
  have hmul : (((2 * j).choose (j + q.1.natAbs) : ℝ) * ((2 * j).choose (j + q.2.natAbs) : ℝ)) ≤
      (j.centralBinom : ℝ) ^ 2 *
        Real.exp (-(((q.1.natAbs : ℝ) ^ 2 + (q.2.natAbs : ℝ) ^ 2) / (2 * j))) := by
    calc (((2 * j).choose (j + q.1.natAbs) : ℝ) * ((2 * j).choose (j + q.2.natAbs) : ℝ))
        ≤ ((j.centralBinom : ℝ) * Real.exp (-((q.1.natAbs : ℝ) ^ 2 / (2 * j)))) *
            ((j.centralBinom : ℝ) * Real.exp (-((q.2.natAbs : ℝ) ^ 2 / (2 * j)))) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (j.centralBinom : ℝ) ^ 2 *
            (Real.exp (-((q.1.natAbs : ℝ) ^ 2 / (2 * j))) *
              Real.exp (-((q.2.natAbs : ℝ) ^ 2 / (2 * j)))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hr : (rnorm q : ℝ) ^ 2 ≤ (q.1.natAbs : ℝ) ^ 2 + (q.2.natAbs : ℝ) ^ 2 := by
    unfold rnorm
    rcases le_total q.1.natAbs q.2.natAbs with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (q.1.natAbs : ℝ)]
    · rw [max_eq_left h]; nlinarith [sq_nonneg (q.2.natAbs : ℝ)]
  have hexp : Real.exp (-(((q.1.natAbs : ℝ) ^ 2 + (q.2.natAbs : ℝ) ^ 2) / (2 * j))) ≤
      Real.exp (-((rnorm q : ℝ) ^ 2 / (2 * j))) := by
    apply Real.exp_le_exp.mpr
    have : ((rnorm q : ℝ) ^ 2) / (2 * j) ≤
        ((q.1.natAbs : ℝ) ^ 2 + (q.2.natAbs : ℝ) ^ 2) / (2 * j) := by gcongr
    linarith
  calc (((2 * j).choose (j + q.1.natAbs) : ℝ) * ((2 * j).choose (j + q.2.natAbs) : ℝ)) / 16 ^ j
      ≤ ((j.centralBinom : ℝ) ^ 2 *
          Real.exp (-(((q.1.natAbs : ℝ) ^ 2 + (q.2.natAbs : ℝ) ^ 2) / (2 * j)))) / 16 ^ j := by
        gcongr
    _ = ((j.centralBinom : ℝ) ^ 2 / 16 ^ j) *
          Real.exp (-(((q.1.natAbs : ℝ) ^ 2 + (q.2.natAbs : ℝ) ^ 2) / (2 * j))) := by ring
    _ ≤ (1 / (Real.pi * j)) * Real.exp (-((rnorm q : ℝ) ^ 2 / (2 * j))) :=
        mul_le_mul (cb_sq_le j hj) hexp (by positivity) (by positivity)

lemma p_rot_even_ge {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (q : ℤ × ℤ) (j : ℕ)
    (hj : 1 ≤ j) (hr : 4 * (rnorm q) ^ 2 ≤ j) :
    1 / (Real.pi * ((j : ℝ) + 1)) - 4 * (rnorm q : ℝ) ^ 2 / (Real.pi * j * ((j : ℝ) + 1)) ≤
      p X (rot q) (2 * j) := by
  rw [p_rot_even hX]
  have hr1 : q.1.natAbs ≤ rnorm q := le_max_left _ _
  have hr2 : q.2.natAbs ≤ rnorm q := le_max_right _ _
  have h1le : q.1.natAbs ≤ j := by nlinarith
  have h2le : q.2.natAbs ≤ j := by nlinarith
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have h4r : 4 * (rnorm q : ℝ) ^ 2 ≤ j := by exact_mod_cast hr
  have hc1 : (j.centralBinom : ℝ) * (1 - 2 * (rnorm q : ℝ) ^ 2 / j) ≤
      ((2 * j).choose (j + q.1.natAbs) : ℝ) := by
    refine le_trans ?_ (choose_near j hj q.1.natAbs h1le)
    gcongr
  have hc2 : (j.centralBinom : ℝ) * (1 - 2 * (rnorm q : ℝ) ^ 2 / j) ≤
      ((2 * j).choose (j + q.2.natAbs) : ℝ) := by
    refine le_trans ?_ (choose_near j hj q.2.natAbs h2le)
    gcongr
  have hpos_f : 0 ≤ 1 - 2 * (rnorm q : ℝ) ^ 2 / j := by
    rw [sub_nonneg, div_le_one hj']; linarith
  have hsq : 1 - 4 * (rnorm q : ℝ) ^ 2 / j ≤ (1 - 2 * (rnorm q : ℝ) ^ 2 / j) ^ 2 := by
    have : (1 - 2 * (rnorm q : ℝ) ^ 2 / j) ^ 2 =
        1 - 4 * (rnorm q : ℝ) ^ 2 / j + (2 * (rnorm q : ℝ) ^ 2 / j) ^ 2 := by ring
    rw [this]; linarith [sq_nonneg (2 * (rnorm q : ℝ) ^ 2 / j)]
  have hnn14 : 0 ≤ 1 - 4 * (rnorm q : ℝ) ^ 2 / j := by
    rw [sub_nonneg, div_le_one hj']; exact h4r
  have hprod : ((j.centralBinom : ℝ) ^ 2 / 16 ^ j) * (1 - 4 * (rnorm q : ℝ) ^ 2 / j) ≤
      (((2 * j).choose (j + q.1.natAbs) : ℝ) * ((2 * j).choose (j + q.2.natAbs) : ℝ)) / 16 ^ j := by
    calc ((j.centralBinom : ℝ) ^ 2 / 16 ^ j) * (1 - 4 * (rnorm q : ℝ) ^ 2 / j)
        ≤ ((j.centralBinom : ℝ) ^ 2 / 16 ^ j) * (1 - 2 * (rnorm q : ℝ) ^ 2 / j) ^ 2 := by gcongr
      _ = (((j.centralBinom : ℝ) * (1 - 2 * (rnorm q : ℝ) ^ 2 / j)) *
            ((j.centralBinom : ℝ) * (1 - 2 * (rnorm q : ℝ) ^ 2 / j))) / 16 ^ j := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul hc1 hc2 (mul_nonneg (by positivity) hpos_f) (by positivity)) (by positivity)
  refine le_trans ?_ hprod
  calc 1 / (Real.pi * ((j : ℝ) + 1)) - 4 * (rnorm q : ℝ) ^ 2 / (Real.pi * j * ((j : ℝ) + 1))
      = (1 / (Real.pi * ((j : ℝ) + 1))) * (1 - 4 * (rnorm q : ℝ) ^ 2 / j) := by
        field_simp [Real.pi_ne_zero]
    _ ≤ ((j.centralBinom : ℝ) ^ 2 / 16 ^ j) * (1 - 4 * (rnorm q : ℝ) ^ 2 / j) :=
        mul_le_mul_of_nonneg_right (cb_sq_ge j) hnn14

/-- Discounted Green function `G_s(z) = ∑_{t ≥ 0} s^t p_t(z)`. -/
noncomputable def green {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (s : ℝ) (z : ℤ × ℤ) : ℝ :=
  ∑' t : ℕ, s ^ t * p X z t

lemma summable_green {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℤ × ℤ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (z : ℤ × ℤ) :
    Summable (fun t : ℕ ↦ s ^ t * p X z t) :=
  Summable.of_nonneg_of_le (fun t ↦ mul_nonneg (pow_nonneg hs0 t) (p_nonneg X z t))
    (fun t ↦ mul_le_of_le_one_right (pow_nonneg hs0 t) (p_le_one X z t))
    (summable_geometric_of_lt_one hs0 hs1)

lemma green_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) {s : ℝ} (hs0 : 0 ≤ s)
    (z : ℤ × ℤ) : 0 ≤ green X s z :=
  tsum_nonneg fun t ↦ mul_nonneg (pow_nonneg hs0 t) (p_nonneg X z t)

lemma green_symm {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (s : ℝ) (z : ℤ × ℤ) :
    green X s (-z) = green X s z := by
  unfold green
  exact tsum_congr fun t ↦ by rw [p_neg hX]

lemma green_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (z : ℤ × ℤ) :
    green X s z = (if z = 0 then 1 else 0) +
      s * (1 / 4 : ℝ) * ∑ e ∈ stepsF, green X s (z - e) := by
  have hsum := summable_green X hs0 hs1 z
  unfold green
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, p_zero_at hX]
  congr 1
  have hstep : ∀ t : ℕ, s ^ (t + 1) * p X z (t + 1) =
      s * (1 / 4 : ℝ) * ∑ e ∈ stepsF, s ^ t * p X (z - e) t := by
    intro t
    rw [p_step hX, pow_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ ↦ by ring
  simp_rw [hstep]
  rw [tsum_mul_left, Summable.tsum_finsetSum fun e _ ↦ summable_green X hs0 hs1 (z - e)]

lemma green_rot_eq_even {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (q : ℤ × ℤ) :
    green X s (rot q) = ∑' j : ℕ, (s ^ 2) ^ j * p X (rot q) (2 * j) := by
  have hs2_nn : 0 ≤ s ^ 2 := sq_nonneg s
  have hs2_lt : s ^ 2 < 1 := pow_lt_one₀ hs0 hs1 (by decide)
  have hsum_even : Summable (fun j : ℕ ↦ (s ^ 2) ^ j * p X (rot q) (2 * j)) :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (pow_nonneg hs2_nn j) (p_nonneg X _ _))
      (fun j ↦ mul_le_of_le_one_right (pow_nonneg hs2_nn j) (p_le_one X _ _))
      (summable_geometric_of_lt_one hs2_nn hs2_lt)
  have hfun : (fun j : ℕ ↦ s ^ (2 * j) * p X (rot q) (2 * j)) =
      fun j : ℕ ↦ (s ^ 2) ^ j * p X (rot q) (2 * j) := funext fun j ↦ by rw [pow_mul]
  have he : HasSum (fun j : ℕ ↦ s ^ (2 * j) * p X (rot q) (2 * j))
      (∑' j : ℕ, (s ^ 2) ^ j * p X (rot q) (2 * j)) := hfun ▸ hsum_even.hasSum
  have ho : HasSum (fun j : ℕ ↦ s ^ (2 * j + 1) * p X (rot q) (2 * j + 1)) 0 := by
    simp [p_rot_odd hX]
  have hall := HasSum.even_add_odd (f := fun t : ℕ ↦ s ^ t * p X (rot q) t) he ho
  rw [add_zero] at hall
  exact hall.tsum_eq

/-- Uniform upper and lower bounds on `green X (1 - 1 / M) (rot q)`. -/
lemma green_zero_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 2 ≤ M) :
    green X (1 - 1 / (M : ℝ)) 0 ≤ Real.log M / Real.pi + 2 := by
  set s : ℝ := 1 - 1 / (M : ℝ)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hs0 : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_one hM0]; exact hM1
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hM0]
  have hs2_lt : s ^ 2 < 1 := pow_lt_one₀ hs0 hs1 (by decide)
  have hs2_nn : 0 ≤ s ^ 2 := sq_nonneg s
  have heq := green_rot_eq_even hX hs0 hs1 0
  rw [rot_zero] at heq
  have hsum_even : Summable (fun j : ℕ ↦ (s ^ 2) ^ j * p X 0 (2 * j)) :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (pow_nonneg hs2_nn j) (p_nonneg X 0 _))
      (fun j ↦ mul_le_of_le_one_right (pow_nonneg hs2_nn j) (p_le_one X 0 _))
      (summable_geometric_of_lt_one hs2_nn hs2_lt)
  rw [heq, hsum_even.tsum_eq_zero_add]
  have hp0 : (s ^ 2) ^ 0 * p X 0 (2 * 0) ≤ 1 := by simp [p_le_one]
  have hser := Real.hasSum_pow_div_log_of_abs_lt_one (x := s ^ 2)
    (by rwa [abs_of_nonneg hs2_nn])
  have hle_term : ∀ j : ℕ, (s ^ 2) ^ (j + 1) * p X 0 (2 * (j + 1)) ≤
      (1 / Real.pi) * ((s ^ 2) ^ (j + 1) / ((j : ℝ) + 1)) := by
    intro j
    have h := p_rot_even_le hX 0 (j + 1) (by omega)
    have h0 : rnorm 0 = 0 := rfl
    rw [rot_zero, h0] at h
    have h' : p X 0 (2 * (j + 1)) ≤ 1 / (Real.pi * ((j : ℝ) + 1)) := by simpa using h
    calc (s ^ 2) ^ (j + 1) * p X 0 (2 * (j + 1))
        ≤ (s ^ 2) ^ (j + 1) * (1 / (Real.pi * ((j : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h' (pow_nonneg hs2_nn _)
      _ = (1 / Real.pi) * ((s ^ 2) ^ (j + 1) / ((j : ℝ) + 1)) := by
          field_simp [Real.pi_ne_zero]
  have hsum_tail := ((summable_nat_add_iff 1).mpr hsum_even).tsum_le_tsum hle_term
    (hser.summable.mul_left _)
  rw [tsum_mul_left, hser.tsum_eq] at hsum_tail
  have h1s2 : 1 / (M : ℝ) ≤ 1 - s ^ 2 := by
    have : 1 - s ^ 2 = (1 / (M : ℝ)) * (2 - 1 / (M : ℝ)) := by dsimp [s]; ring
    rw [this]
    have : 1 / (M : ℝ) ≤ 1 := div_le_one_of_le₀ hM1 hM0.le
    nlinarith [one_div_pos.mpr hM0]
  have hlog : -Real.log (1 - s ^ 2) ≤ Real.log M := by
    have := Real.log_le_log (one_div_pos.mpr hM0) h1s2
    rw [one_div, Real.log_inv] at this
    linarith
  have hpi := Real.pi_pos
  have : (1 / Real.pi) * (-Real.log (1 - s ^ 2)) ≤ Real.log M / Real.pi := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hlog hpi.le
  linarith

lemma green_zero_ge {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 2 ≤ M) :
    Real.log M / Real.pi - 1 ≤ green X (1 - 1 / (M : ℝ)) 0 := by
  set s : ℝ := 1 - 1 / (M : ℝ)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hs0 : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_one hM0]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hM0]
  have hs2_lt : s ^ 2 < 1 := pow_lt_one₀ hs0 hs1 (by decide)
  have hs2_nn : 0 ≤ s ^ 2 := sq_nonneg s
  have heq := green_rot_eq_even hX hs0 hs1 0
  rw [rot_zero] at heq
  have hser := Real.hasSum_pow_div_log_of_abs_lt_one (x := s ^ 2)
    (by rwa [abs_of_nonneg hs2_nn])
  have hsum_even : Summable (fun j : ℕ ↦ (s ^ 2) ^ j * p X 0 (2 * j)) :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (pow_nonneg hs2_nn j) (p_nonneg X 0 _))
      (fun j ↦ mul_le_of_le_one_right (pow_nonneg hs2_nn j) (p_le_one X 0 _))
      (summable_geometric_of_lt_one hs2_nn hs2_lt)
  have hge_term : ∀ j : ℕ, (1 / Real.pi) * ((s ^ 2) ^ (j + 1) / ((j : ℝ) + 1)) ≤
      (s ^ 2) ^ j * p X 0 (2 * j) := by
    intro j
    have hp : 1 / (Real.pi * ((j : ℝ) + 1)) ≤ p X 0 (2 * j) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [Nat.cast_zero, zero_add, mul_one, mul_zero, p_zero_at hX, ↓reduceIte]
        rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
      · have h := p_rot_even_ge hX 0 j hj (by simp [rnorm])
        simpa [rot_zero, rnorm] using h
    calc (1 / Real.pi) * ((s ^ 2) ^ (j + 1) / ((j : ℝ) + 1))
        = (s ^ 2) ^ j * s ^ 2 * (1 / (Real.pi * ((j : ℝ) + 1))) := by
          rw [pow_succ]; field_simp [Real.pi_ne_zero]
      _ ≤ (s ^ 2) ^ j * 1 * p X 0 (2 * j) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs2_lt.le (pow_nonneg hs2_nn j)) hp
            (by positivity) (by positivity)
      _ = (s ^ 2) ^ j * p X 0 (2 * j) := by ring
  have htsum_ge := (hser.summable.mul_left _).tsum_le_tsum hge_term hsum_even
  rw [tsum_mul_left, hser.tsum_eq, ← heq] at htsum_ge
  have h1s2 : 1 - s ^ 2 ≤ 2 / (M : ℝ) := by
    have : 1 - s ^ 2 = 2 / (M : ℝ) - 1 / (M : ℝ) ^ 2 := by dsimp [s]; ring
    rw [this]; linarith [show 0 ≤ 1 / (M : ℝ) ^ 2 by positivity]
  have hpos1s2 : 0 < 1 - s ^ 2 := by linarith
  have hlog : Real.log M - Real.log 2 ≤ -Real.log (1 - s ^ 2) := by
    have := Real.log_le_log hpos1s2 h1s2
    rw [Real.log_div (by norm_num) hM0.ne'] at this
    linarith
  have hpi := Real.pi_pos
  have hlog2 : Real.log 2 / Real.pi ≤ 1 := by
    rw [div_le_one hpi]
    linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have : (Real.log M - Real.log 2) / Real.pi ≤ (1 / Real.pi) * (-Real.log (1 - s ^ 2)) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hlog hpi.le
  rw [sub_div] at this
  linarith

lemma green_rot_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 2 ≤ M)
    (q : ℤ × ℤ) (hq : 1 ≤ rnorm q) :
    green X (1 - 1 / (M : ℝ)) (rot q) ≤
      max 0 (Real.log ((M : ℝ) / (rnorm q : ℝ) ^ 2) / Real.pi) + 2 := by
  set s : ℝ := 1 - 1 / (M : ℝ)
  set r : ℕ := rnorm q
  have hr1 : 1 ≤ r := hq
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hs0 : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_one hM0]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hM0]
  have hs2_lt : s ^ 2 < 1 := pow_lt_one₀ hs0 hs1 (by decide)
  have hs2_nn : 0 ≤ s ^ 2 := sq_nonneg s
  have hpi := Real.pi_pos
  have heq := green_rot_eq_even hX hs0 hs1 q
  have hsum_even : Summable (fun j : ℕ ↦ (s ^ 2) ^ j * p X (rot q) (2 * j)) :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (pow_nonneg hs2_nn j) (p_nonneg X _ _))
      (fun j ↦ mul_le_of_le_one_right (pow_nonneg hs2_nn j) (p_le_one X _ _))
      (summable_geometric_of_lt_one hs2_nn hs2_lt)
  rw [heq, ← hsum_even.sum_add_tsum_nat_add (r ^ 2 + 1)]
  -- Prefix j = 0 .. r^2
  have hp0 : p X (rot q) 0 = 0 := by
    rw [p_zero_at hX, if_neg]
    intro hz
    have hq0 : q = 0 := rot_injective (hz.trans rot_zero.symm)
    subst hq0
    simp [r, rnorm] at hr1
  have hpref : ∑ j ∈ Finset.range (r ^ 2 + 1), (s ^ 2) ^ j * p X (rot q) (2 * j) ≤ 1 := by
    rw [Finset.sum_range_succ', pow_zero, one_mul, mul_zero, hp0, add_zero]
    have hterm : ∀ j ∈ Finset.range (r ^ 2),
        (s ^ 2) ^ (j + 1) * p X (rot q) (2 * (j + 1)) ≤ 2 / (Real.pi * (r : ℝ) ^ 2) := by
      intro j _
      have hj1 : 1 ≤ j + 1 := by omega
      have hp := p_rot_even_le hX q (j + 1) hj1
      have hexp : Real.exp (-((r : ℝ) ^ 2 / (2 * ((j + 1 : ℕ) : ℝ)))) ≤
          (2 * ((j + 1 : ℕ) : ℝ)) / (r : ℝ) ^ 2 := by
        set x := (r : ℝ) ^ 2 / (2 * ((j + 1 : ℕ) : ℝ))
        have hx : 0 < x := by positivity
        have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
        rw [Real.exp_neg, show (2 * ((j + 1 : ℕ) : ℝ)) / (r : ℝ) ^ 2 = x⁻¹ by dsimp [x]; field_simp]
        exact inv_anti₀ hx h1
      calc (s ^ 2) ^ (j + 1) * p X (rot q) (2 * (j + 1))
          ≤ 1 * ((1 / (Real.pi * ((j + 1 : ℕ) : ℝ))) *
              Real.exp (-((r : ℝ) ^ 2 / (2 * ((j + 1 : ℕ) : ℝ))))) :=
            mul_le_mul (pow_le_one₀ hs2_nn hs2_lt.le) hp (p_nonneg _ _ _) zero_le_one
        _ ≤ (1 / (Real.pi * ((j + 1 : ℕ) : ℝ))) * ((2 * ((j + 1 : ℕ) : ℝ)) / (r : ℝ) ^ 2) := by
            rw [one_mul]; gcongr
        _ = 2 / (Real.pi * (r : ℝ) ^ 2) := by field_simp [hpi.ne']
    calc ∑ j ∈ Finset.range (r ^ 2), (s ^ 2) ^ (j + 1) * p X (rot q) (2 * (j + 1))
        ≤ ∑ _ ∈ Finset.range (r ^ 2), 2 / (Real.pi * (r : ℝ) ^ 2) := Finset.sum_le_sum hterm
      _ = 2 / Real.pi := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
          field_simp [hpi.ne', hr_pos.ne']
      _ ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
  -- Tail j ≥ r^2 + 1
  have h1s2 : 1 / (M : ℝ) ≤ 1 - s ^ 2 := by
    have : 1 - s ^ 2 = (1 / (M : ℝ)) * (2 - 1 / (M : ℝ)) := by dsimp [s]; ring
    rw [this]
    have : 1 / (M : ℝ) ≤ 1 := div_le_one_of_le₀ (by linarith) hM0.le
    nlinarith [one_div_pos.mpr hM0]
  by_cases hrM : r ^ 2 ≤ M
  · have hser := Real.hasSum_pow_div_log_of_abs_lt_one (x := s ^ 2)
      (by rwa [abs_of_nonneg hs2_nn])
    have htail_le : (∑' k : ℕ, (s ^ 2) ^ (k + (r ^ 2 + 1)) * p X (rot q) (2 * (k + (r ^ 2 + 1)))) ≤
        (1 / Real.pi) * ∑' k : ℕ, (s ^ 2) ^ (k + r ^ 2 + 1) / ((k + r ^ 2 : ℕ) + 1 : ℝ) := by
      rw [← tsum_mul_left]
      refine ((summable_nat_add_iff (r ^ 2 + 1)).mpr hsum_even).tsum_le_tsum (fun k ↦ ?_)
        (((summable_nat_add_iff (r ^ 2)).mpr hser.summable).mul_left _)
      have hp := p_rot_even_le hX q (k + (r ^ 2 + 1)) (by omega)
      have hexp1 : Real.exp (-((r : ℝ) ^ 2 / (2 * ((k + (r ^ 2 + 1) : ℕ) : ℝ)))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      calc (s ^ 2) ^ (k + (r ^ 2 + 1)) * p X (rot q) (2 * (k + (r ^ 2 + 1)))
          ≤ (s ^ 2) ^ (k + (r ^ 2 + 1)) * (1 / (Real.pi * ((k + (r ^ 2 + 1) : ℕ) : ℝ)) * 1) :=
            mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left hexp1 (by positivity)))
              (pow_nonneg hs2_nn _)
        _ = (1 / Real.pi) * ((s ^ 2) ^ (k + r ^ 2 + 1) / ((k + r ^ 2 : ℕ) + 1 : ℝ)) := by
            rw [show k + (r ^ 2 + 1) = (k + r ^ 2) + 1 by omega]
            push_cast
            field_simp [hpi.ne']
    have hsplit := hser.summable.sum_add_tsum_nat_add (r ^ 2)
    rw [hser.tsum_eq] at hsplit
    have hs2_ge : ∀ m : ℕ, 1 - 2 * (m : ℝ) / M ≤ (s ^ 2) ^ m := by
      intro m
      rcases eq_or_ne m 0 with rfl | hm
      · simp
      have hsub : 1 - 2 / (M : ℝ) ≤ s ^ 2 := by
        have : s ^ 2 = 1 - 2 / (M : ℝ) + 1 / (M : ℝ) ^ 2 := by dsimp [s]; ring
        rw [this]; linarith [show (0 : ℝ) ≤ 1 / (M : ℝ) ^ 2 by positivity]
      by_cases hmM : 1 - 2 / (M : ℝ) < 0
      · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero hm
        have h2m : 2 / (M : ℝ) ≤ 2 * (m : ℝ) / M := by
          rw [div_le_div_iff_of_pos_right hM0]; linarith
        have hpow0 : 0 ≤ (s ^ 2) ^ m := pow_nonneg hs2_nn m
        linarith
      · push Not at hmM
        have hb := one_add_mul_le_pow (a := -(2 / (M : ℝ))) (by linarith) m
        calc 1 - 2 * (m : ℝ) / M = 1 + (m : ℝ) * (-(2 / (M : ℝ))) := by ring
          _ ≤ (1 + -(2 / (M : ℝ))) ^ m := hb
          _ ≤ (s ^ 2) ^ m := pow_le_pow_left₀ hmM hsub m
    have hsum_low : Real.log ((r : ℝ) ^ 2) - 2 ≤
        ∑ j ∈ Finset.range (r ^ 2), (s ^ 2) ^ (j + 1) / ((j : ℝ) + 1) := by
      have h1 : ∑ j ∈ Finset.range (r ^ 2), (1 / ((j : ℝ) + 1) - 2 / (M : ℝ)) ≤
          ∑ j ∈ Finset.range (r ^ 2), (s ^ 2) ^ (j + 1) / ((j : ℝ) + 1) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have hg := hs2_ge (j + 1)
        push_cast at hg
        calc 1 / ((j : ℝ) + 1) - 2 / (M : ℝ)
            = (1 - 2 * ((j : ℝ) + 1) / M) / ((j : ℝ) + 1) := by field_simp
          _ ≤ (s ^ 2) ^ (j + 1) / ((j : ℝ) + 1) :=
              div_le_div_of_nonneg_right hg (by positivity)
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
      have hharm : ∑ j ∈ Finset.range (r ^ 2), 1 / ((j : ℝ) + 1) = (harmonic (r ^ 2) : ℝ) := by
        simp [harmonic, Rat.cast_sum]
      rw [hharm] at h1
      have hhl := log_add_one_le_harmonic (r ^ 2)
      push_cast at hhl
      have hrM' : (r : ℝ) ^ 2 * (2 / (M : ℝ)) ≤ 2 := by
        rw [mul_div_assoc', div_le_iff₀ hM0]
        have : (r : ℝ) ^ 2 ≤ M := by exact_mod_cast hrM
        linarith
      have hlogr : Real.log ((r : ℝ) ^ 2) ≤ Real.log ((r : ℝ) ^ 2 + 1) :=
        Real.log_le_log (by positivity) (by linarith)
      push_cast at h1
      linarith
    have hlogM : -Real.log (1 - s ^ 2) ≤ Real.log M := by
      have := Real.log_le_log (one_div_pos.mpr hM0) h1s2
      rw [one_div, Real.log_inv] at this
      linarith
    have htail2 : (∑' k : ℕ, (s ^ 2) ^ (k + r ^ 2 + 1) / ((k + r ^ 2 : ℕ) + 1 : ℝ)) ≤
        Real.log ((M : ℝ) / (r : ℝ) ^ 2) + 2 := by
      rw [Real.log_div hM0.ne' (by positivity)]
      have hcongr : (∑' k : ℕ, (s ^ 2) ^ (k + r ^ 2 + 1) / ((k + r ^ 2 : ℕ) + 1 : ℝ)) =
          ∑' k : ℕ, (s ^ 2) ^ (k + r ^ 2 + 1) / (((k + r ^ 2 : ℕ) : ℝ) + 1) := rfl
      linarith [hsplit, hsum_low, hlogM]
    have htail3 : (1 / Real.pi) * (Real.log ((M : ℝ) / (r : ℝ) ^ 2) + 2) ≤
        max 0 (Real.log ((M : ℝ) / (r : ℝ) ^ 2) / Real.pi) + 1 := by
      have h2pi : 2 / Real.pi ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
      have hmax : Real.log ((M : ℝ) / (r : ℝ) ^ 2) / Real.pi ≤
          max 0 (Real.log ((M : ℝ) / (r : ℝ) ^ 2) / Real.pi) := le_max_right _ _
      have : (1 / Real.pi) * (Real.log ((M : ℝ) / (r : ℝ) ^ 2) + 2) =
          Real.log ((M : ℝ) / (r : ℝ) ^ 2) / Real.pi + 2 / Real.pi := by ring
      linarith
    have := htail_le.trans ((mul_le_mul_of_nonneg_left htail2 (by positivity)).trans htail3)
    linarith
  · push Not at hrM
    have htail_geom : (∑' k : ℕ, (s ^ 2) ^ (k + (r ^ 2 + 1)) * p X (rot q) (2 * (k + (r ^ 2 + 1)))) ≤
        (1 / (Real.pi * M)) * ∑' k : ℕ, (s ^ 2) ^ k := by
      rw [← tsum_mul_left]
      refine ((summable_nat_add_iff (r ^ 2 + 1)).mpr hsum_even).tsum_le_tsum (fun k ↦ ?_)
        ((summable_geometric_of_lt_one hs2_nn hs2_lt).mul_left _)
      have hp := p_rot_even_le hX q (k + (r ^ 2 + 1)) (by omega)
      have hexp1 : Real.exp (-((r : ℝ) ^ 2 / (2 * ((k + (r ^ 2 + 1) : ℕ) : ℝ)))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      have hm_ge : (M : ℝ) ≤ ((k + (r ^ 2 + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega)
      have hpow_le : (s ^ 2) ^ (k + (r ^ 2 + 1)) ≤ (s ^ 2) ^ k :=
        pow_le_pow_of_le_one hs2_nn hs2_lt.le (by omega)
      calc (s ^ 2) ^ (k + (r ^ 2 + 1)) * p X (rot q) (2 * (k + (r ^ 2 + 1)))
          ≤ (s ^ 2) ^ k * ((1 / (Real.pi * ((k + (r ^ 2 + 1) : ℕ) : ℝ))) * 1) :=
            mul_le_mul hpow_le (hp.trans (mul_le_mul_of_nonneg_left hexp1 (by positivity)))
              (p_nonneg _ _ _) (pow_nonneg hs2_nn k)
        _ ≤ (s ^ 2) ^ k * (1 / (Real.pi * M)) := by
            rw [mul_one]; gcongr
        _ = (1 / (Real.pi * M)) * (s ^ 2) ^ k := by ring
    rw [tsum_geometric_of_lt_one hs2_nn hs2_lt] at htail_geom
    have hpos1s2 : 0 < 1 - s ^ 2 := sub_pos.mpr hs2_lt
    have h1 : (1 / (Real.pi * M)) * (1 - s ^ 2)⁻¹ ≤ 1 := by
      have : (1 - s ^ 2)⁻¹ ≤ (M : ℝ) := by
        rw [inv_le_comm₀ hpos1s2 hM0]
        simpa [one_div] using h1s2
      calc (1 / (Real.pi * M)) * (1 - s ^ 2)⁻¹ ≤ (1 / (Real.pi * M)) * M := by gcongr
        _ = 1 / Real.pi := by field_simp [hpi.ne', hM0.ne']
        _ ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
    have hmax0 : 0 ≤ max 0 (Real.log ((M : ℝ) / (r : ℝ) ^ 2) / Real.pi) := le_max_left _ _
    linarith

lemma hasSum_tel (J : ℕ) (hJ : 1 ≤ J) :
    HasSum (fun k : ℕ ↦ 1 / (((k + J : ℕ) : ℝ) * (((k + J : ℕ) : ℝ) + 1))) (1 / (J : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k ↦ by positivity)]
  have hsum_eq : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, 1 / (((k + J : ℕ) : ℝ) * (((k + J : ℕ) : ℝ) + 1))) =
        1 / (J : ℝ) - 1 / ((n + J : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hk1 : (0 : ℝ) < ((n + J : ℕ) : ℝ) := by positivity
      have hk2 : (0 : ℝ) < ((n + J : ℕ) : ℝ) + 1 := by positivity
      have hcast : ((n + 1 + J : ℕ) : ℝ) = ((n + J : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]; field_simp [hk1.ne', hk2.ne']; ring
  simp_rw [hsum_eq]
  have htend : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n + J : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hcomp := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat (J - 1))
    refine hcomp.congr fun n ↦ ?_
    dsimp; congr 1
    have : n + (J - 1) + 1 = n + J := by omega
    exact_mod_cast this
  simpa using tendsto_const_nhds.sub htend

lemma green_rot_ge {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 2 ≤ M)
    (q : ℤ × ℤ) (hq : 1 ≤ rnorm q) :
    Real.log ((M : ℝ) / (rnorm q : ℝ) ^ 2) / Real.pi - 3 ≤
      green X (1 - 1 / (M : ℝ)) (rot q) := by
  set s : ℝ := 1 - 1 / (M : ℝ)
  set r : ℕ := rnorm q
  have hr1 : 1 ≤ r := hq
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hs0 : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_one hM0]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hM0]
  have hs2_lt : s ^ 2 < 1 := pow_lt_one₀ hs0 hs1 (by decide)
  have hs2_nn : 0 ≤ s ^ 2 := sq_nonneg s
  have hpi := Real.pi_pos
  have heq := green_rot_eq_even hX hs0 hs1 q
  have hsum_even : Summable (fun j : ℕ ↦ (s ^ 2) ^ j * p X (rot q) (2 * j)) :=
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (pow_nonneg hs2_nn j) (p_nonneg X _ _))
      (fun j ↦ mul_le_of_le_one_right (pow_nonneg hs2_nn j) (p_le_one X _ _))
      (summable_geometric_of_lt_one hs2_nn hs2_lt)
  obtain ⟨J, hJ_eq⟩ : ∃ J : ℕ, J = 4 * r ^ 2 := ⟨4 * r ^ 2, rfl⟩
  have hJ1 : 1 ≤ J := by rw [hJ_eq]; nlinarith
  have hJ_pos : (0 : ℝ) < J := by exact_mod_cast hJ1
  have htail_le_green :
      (∑' k : ℕ, (s ^ 2) ^ (k + J) * p X (rot q) (2 * (k + J))) ≤ green X s (rot q) := by
    rw [heq, ← hsum_even.sum_add_tsum_nat_add J]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦
      mul_nonneg (pow_nonneg hs2_nn j) (p_nonneg _ _ _))
  -- Lower bound each term at j = k + J
  have hser := Real.hasSum_pow_div_log_of_abs_lt_one (x := s ^ 2)
    (by rwa [abs_of_nonneg hs2_nn])
  have htel := hasSum_tel J hJ1
  have hsA : Summable (fun k : ℕ ↦
      (1 / Real.pi) * ((s ^ 2) ^ (k + J + 1) / (((k + J : ℕ) : ℝ) + 1))) :=
    ((summable_nat_add_iff J).mpr hser.summable).mul_left _
  have hsB : Summable (fun k : ℕ ↦
      ((J : ℝ) / Real.pi) * (1 / (((k + J : ℕ) : ℝ) * (((k + J : ℕ) : ℝ) + 1)))) :=
    htel.summable.mul_left _
  have hterm_ge : ∀ k : ℕ,
      (1 / Real.pi) * ((s ^ 2) ^ (k + J + 1) / (((k + J : ℕ) : ℝ) + 1)) -
        ((J : ℝ) / Real.pi) * (1 / (((k + J : ℕ) : ℝ) * (((k + J : ℕ) : ℝ) + 1))) ≤
      (s ^ 2) ^ (k + J) * p X (rot q) (2 * (k + J)) := by
    intro k
    have hp := p_rot_even_ge hX q (k + J) (by omega) (by rw [hJ_eq]; dsimp [r]; omega)
    have hmul := mul_le_mul_of_nonneg_left hp (pow_nonneg hs2_nn (k + J))
    refine le_trans ?_ hmul
    rw [mul_sub]
    have h1 : (1 / Real.pi) * ((s ^ 2) ^ (k + J + 1) / (((k + J : ℕ) : ℝ) + 1)) ≤
        (s ^ 2) ^ (k + J) * (1 / (Real.pi * (((k + J : ℕ) : ℝ) + 1))) := by
      calc (1 / Real.pi) * ((s ^ 2) ^ (k + J + 1) / (((k + J : ℕ) : ℝ) + 1))
          = (s ^ 2) ^ (k + J) * s ^ 2 * (1 / (Real.pi * (((k + J : ℕ) : ℝ) + 1))) := by
            rw [pow_succ]; field_simp [hpi.ne']
        _ ≤ (s ^ 2) ^ (k + J) * 1 * (1 / (Real.pi * (((k + J : ℕ) : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hs2_lt.le (pow_nonneg hs2_nn _)) (by positivity)
        _ = _ := by ring
    have hJ_cast : (J : ℝ) = 4 * (r : ℝ) ^ 2 := by rw [hJ_eq]; push_cast; ring
    have h2 : (s ^ 2) ^ (k + J) *
        (4 * (r : ℝ) ^ 2 / (Real.pi * ((k + J : ℕ) : ℝ) * (((k + J : ℕ) : ℝ) + 1))) ≤
        ((J : ℝ) / Real.pi) * (1 / (((k + J : ℕ) : ℝ) * (((k + J : ℕ) : ℝ) + 1))) := by
      have hpow1 : (s ^ 2) ^ (k + J) ≤ 1 := pow_le_one₀ hs2_nn hs2_lt.le
      have hk1 : (0 : ℝ) < ((k + J : ℕ) : ℝ) := by positivity
      calc (s ^ 2) ^ (k + J) *
            (4 * (r : ℝ) ^ 2 / (Real.pi * ((k + J : ℕ) : ℝ) * (((k + J : ℕ) : ℝ) + 1)))
          ≤ 1 * (4 * (r : ℝ) ^ 2 / (Real.pi * ((k + J : ℕ) : ℝ) * (((k + J : ℕ) : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_right hpow1 (by positivity)
        _ = ((J : ℝ) / Real.pi) * (1 / (((k + J : ℕ) : ℝ) * (((k + J : ℕ) : ℝ) + 1))) := by
            rw [hJ_cast]; field_simp [hpi.ne', hk1.ne']
    linarith only [h1, h2]
  have htsum := (hsA.sub hsB).tsum_le_tsum hterm_ge ((summable_nat_add_iff J).mpr hsum_even)
  rw [hsA.tsum_sub hsB, tsum_mul_left, tsum_mul_left, htel.tsum_eq] at htsum
  have hsplit := hser.summable.sum_add_tsum_nat_add J
  rw [hser.tsum_eq] at hsplit
  have hsumJ_le : ∑ j ∈ Finset.range J, (s ^ 2) ^ (j + 1) / ((j : ℝ) + 1) ≤
      1 + Real.log (J : ℝ) := by
    calc ∑ j ∈ Finset.range J, (s ^ 2) ^ (j + 1) / ((j : ℝ) + 1)
        ≤ ∑ j ∈ Finset.range J, 1 / ((j : ℝ) + 1) := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          exact div_le_div_of_nonneg_right (pow_le_one₀ hs2_nn hs2_lt.le) (by positivity)
      _ = (harmonic J : ℝ) := by simp [harmonic, Rat.cast_sum]
      _ ≤ 1 + Real.log J := harmonic_le_one_add_log J
  have h1s2 : 1 - s ^ 2 ≤ 2 / (M : ℝ) := by
    have : 1 - s ^ 2 = 2 / (M : ℝ) - 1 / (M : ℝ) ^ 2 := by dsimp [s]; ring
    rw [this]; linarith only [show 0 ≤ 1 / (M : ℝ) ^ 2 by positivity]
  have hpos1s2 : 0 < 1 - s ^ 2 := by
    have : 1 - s ^ 2 = (1 / (M : ℝ)) * (2 - 1 / (M : ℝ)) := by dsimp [s]; ring
    have h1M : 1 / (M : ℝ) ≤ 1 := div_le_one_of_le₀ (by linarith) hM0.le
    rw [this]; nlinarith [one_div_pos.mpr hM0]
  have hlogM : Real.log M - Real.log 2 ≤ -Real.log (1 - s ^ 2) := by
    have := Real.log_le_log hpos1s2 h1s2
    rw [Real.log_div (by norm_num) hM0.ne'] at this
    linarith only [this]
  have hlogJ : Real.log (J : ℝ) = 2 * Real.log 2 + Real.log ((r : ℝ) ^ 2) := by
    have : (J : ℝ) = 2 ^ 2 * (r : ℝ) ^ 2 := by rw [hJ_eq]; push_cast; ring
    rw [this, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hA_low : Real.log ((M : ℝ) / (r : ℝ) ^ 2) - (1 + 3 * Real.log 2) ≤
      ∑' k : ℕ, (s ^ 2) ^ (k + J + 1) / (((k + J : ℕ) : ℝ) + 1) := by
    rw [Real.log_div hM0.ne' (by positivity)]
    linarith only [hsplit, hsumJ_le, hlogM, hlogJ]
  have hB_eq : ((J : ℝ) / Real.pi) * (1 / (J : ℝ)) = 1 / Real.pi := by
    field_simp [hpi.ne', hJ_pos.ne']
  rw [hB_eq] at htsum
  have hc3 : (2 + 3 * Real.log 2) / Real.pi ≤ 3 := by
    rw [div_le_iff₀ hpi]
    linarith only [Real.log_two_lt_d9, Real.pi_gt_three]
  have hA_div : Real.log ((M : ℝ) / (r : ℝ) ^ 2) / Real.pi - (1 + 3 * Real.log 2) / Real.pi ≤
      (1 / Real.pi) * ∑' k : ℕ, (s ^ 2) ^ (k + J + 1) / (((k + J : ℕ) : ℝ) + 1) := by
    rw [← sub_div, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hA_low hpi.le
  have hsumc : (1 + 3 * Real.log 2) / Real.pi + 1 / Real.pi = (2 + 3 * Real.log 2) / Real.pi := by ring
  linarith only [htail_le_green, htsum, hA_div, hc3, hsumc]

/- ### Section 3: Discrete Feynman–Kac Super-Solution Bound -/

/-- Multiplicative functional `∏_{j=0}^k u(x + pos y j)`. -/
def prodWalk (u : ℤ × ℤ → ℝ) (x : ℤ × ℤ) (y : ℕ → ℤ × ℤ) : ℕ → ℝ
  | 0 => u x
  | k + 1 => u x * prodWalk u (x + y 0) (sh 1 y) k

lemma prodWalk_eq_prod (u : ℤ × ℤ → ℝ) :
    ∀ (k : ℕ) (x : ℤ × ℤ) (y : ℕ → ℤ × ℤ),
      prodWalk u x y k = ∏ j ∈ Finset.range (k + 1), u (x + pos y j)
  | 0, x, y => by simp [prodWalk, pos]
  | k + 1, x, y => by
    rw [prodWalk, prodWalk_eq_prod u k]
    conv_rhs => rw [Finset.prod_range_succ', pos_zero, add_zero, mul_comm]
    refine congrArg (u x * ·) (Finset.prod_congr rfl fun j _ ↦ ?_)
    have hp := pos_shift y 1 j
    have hp1 : pos y 1 = y 0 := by simp [pos]
    rw [Nat.add_comm j 1, hp, hp1, add_assoc]

/-- Shifted local time at `z` for walk starting at `x`. -/
def locShift (x : ℤ × ℤ) (y : ℕ → ℤ × ℤ) (k : ℕ) (z : ℤ × ℤ) : ℕ :=
  ((Finset.range (k + 1)).filter fun j ↦ x + pos y j = z).card

lemma prodWalk_eq_finset_pow {F : Finset (ℤ × ℤ)} {u : ℤ × ℤ → ℝ}
    (hu1 : ∀ z, z ∉ F → u z = 1) (x : ℤ × ℤ) (y : ℕ → ℤ × ℤ) (k : ℕ) :
    prodWalk u x y k = ∏ z ∈ F, (u z) ^ (locShift x y k z) := by
  classical
  rw [prodWalk_eq_prod]
  have hsplit : ∏ j ∈ Finset.range (k + 1), u (x + pos y j) =
      (∏ j ∈ (Finset.range (k + 1)).filter (fun j ↦ x + pos y j ∈ F), u (x + pos y j)) *
      (∏ j ∈ (Finset.range (k + 1)).filter (fun j ↦ x + pos y j ∉ F), u (x + pos y j)) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have h1 : ∏ j ∈ (Finset.range (k + 1)).filter (fun j ↦ x + pos y j ∉ F), u (x + pos y j) = 1 :=
    Finset.prod_eq_one fun j hj ↦ hu1 _ (Finset.mem_filter.mp hj).2
  rw [hsplit, h1, mul_one]
  have hbi := Finset.prod_fiberwise_of_maps_to
    (s := (Finset.range (k + 1)).filter (fun j ↦ x + pos y j ∈ F))
    (t := F) (g := fun j ↦ x + pos y j)
    (fun j hj ↦ (Finset.mem_filter.mp hj).2) (fun j ↦ u (x + pos y j))
  rw [← hbi]
  refine Finset.prod_congr rfl fun z hz ↦ ?_
  have hfilt : ((Finset.range (k + 1)).filter (fun j ↦ x + pos y j ∈ F)).filter
      (fun j ↦ x + pos y j = z) = (Finset.range (k + 1)).filter (fun j ↦ x + pos y j = z) := by
    ext j
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨⟨hr, _⟩, he⟩ ↦ ⟨hr, he⟩, fun ⟨hr, he⟩ ↦ ⟨⟨hr, he.symm ▸ hz⟩, he⟩⟩
  rw [hfilt, Finset.prod_congr rfl (fun j hj ↦ congrArg u (Finset.mem_filter.mp hj).2),
    Finset.prod_const]
  rfl

lemma prodWalk_congr (u : ℤ × ℤ → ℝ) (x : ℤ × ℤ) {k : ℕ} {y y' : ℕ → ℤ × ℤ}
    (h : ∀ i < k, y i = y' i) : prodWalk u x y k = prodWalk u x y' k := by
  rw [prodWalk_eq_prod, prodWalk_eq_prod]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [pos_congr h (by omega)]

def cons (e : ℤ × ℤ) (y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => e
  | i + 1 => y i

lemma cons_zero (e : ℤ × ℤ) (y : ℕ → ℤ × ℤ) : cons e y 0 = e := rfl

lemma sh_one_cons (e : ℤ × ℤ) (y : ℕ → ℤ × ℤ) : sh 1 (cons e y) = y :=
  funext fun i ↦ by simp [sh, cons, Nat.add_comm 1 i]

noncomputable def expWalk (u : ℤ × ℤ → ℝ) : ℕ → (ℤ × ℤ) → ℝ
  | 0, x => u x
  | k + 1, x => u x * (1 / 4 : ℝ) * ∑ e ∈ stepsF, expWalk u k (x + e)

lemma markov_chernoff {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {u : ℤ × ℤ → ℝ}
    (hu : ∀ z, 0 < u z) :
    ∀ (k : ℕ) (x : ℤ × ℤ) {A : Set (ℕ → ℤ × ℤ)} (_hA : Det k A) {B : ℝ} (_hB0 : 0 ≤ B)
      (_hBA : ∀ y ∈ A, B ≤ prodWalk u x y k),
      B * (ℙ {ω | path X ω ∈ A}).toReal ≤ expWalk u k x
  | 0, x, A, _, B, hB0, hBA => by
    by_cases hne : ∃ ω : Ω, path X ω ∈ A
    · obtain ⟨ω₀, hω₀⟩ := hne
      have hBu : B ≤ u x := hBA (path X ω₀) hω₀
      have hp1 : (ℙ {ω | path X ω ∈ A}).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := (ℙ : Measure Ω)))
      calc B * (ℙ {ω | path X ω ∈ A}).toReal ≤ B * 1 := mul_le_mul_of_nonneg_left hp1 hB0
        _ = B := mul_one B
        _ ≤ expWalk u 0 x := hBu
    · have hemp : {ω : Ω | path X ω ∈ A} = ∅ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h ↦ hne ⟨ω, h⟩
      rw [hemp, measure_empty, ENNReal.toReal_zero, mul_zero]
      exact (hu x).le
  | k + 1, x, A, hA, B, hB0, hBA => by
    let A_slice (e : ℤ × ℤ) : Set (ℕ → ℤ × ℤ) := {y' | cons e y' ∈ A}
    have hdet_slice : ∀ e, Det k (A_slice e) := fun e y₁ y₂ hy hmem ↦ by
      refine hA (cons e y₁) (cons e y₂) (fun i hi ↦ ?_) hmem
      rcases i with _ | i
      · rfl
      · exact hy i (by omega)
    have hB_slice : ∀ e, ∀ y' ∈ A_slice e, B / u x ≤ prodWalk u (x + e) y' k := by
      intro e y' hy'
      have h := hBA (cons e y') hy'
      rw [prodWalk, cons_zero, sh_one_cons] at h
      rwa [div_le_iff₀' (hu x)]
    have ih : ∀ e ∈ stepsF,
        B * (ℙ {ω | path X ω ∈ A_slice e}).toReal ≤ u x * expWalk u k (x + e) := by
      intro e _
      have h := markov_chernoff hX hu k (x + e) (hdet_slice e) (div_nonneg hB0 (hu x).le)
        (hB_slice e)
      have hmul := mul_le_mul_of_nonneg_left h (hu x).le
      rwa [← mul_assoc, mul_div_cancel₀ _ (hu x).ne'] at hmul
    let E (e : ℤ × ℤ) : Set Ω :=
      {ω | path X ω ∈ {y | y 0 = e} ∧ sh 1 (path X ω) ∈ A_slice e}
    have hsub : {ω | path X ω ∈ A} ⊆
        (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ∪ X 0 ⁻¹' stepsᶜ := by
      intro ω hω
      by_cases hs : X 0 ω ∈ steps
      · have hE : ω ∈ E (X 0 ω) := by
          refine ⟨rfl, hA (path X ω) (cons (X 0 ω) (sh 1 (path X ω))) (fun i _ ↦ ?_) hω⟩
          rcases i with _ | i
          · rfl
          · simp [cons, sh, Nat.add_comm 1 i]
        simp only [steps, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with h | h | h | h <;> rw [h] at hE <;> simp [hE]
      · exact Or.inr hs
    have hprobE : ∀ e ∈ steps, ℙ (E e) = (4 : ℝ≥0∞)⁻¹ * ℙ {ω | path X ω ∈ A_slice e} := by
      intro e he
      rw [prob_block hX (det_zero e) (hdet_slice e),
        show {ω | path X ω ∈ {y : ℕ → ℤ × ℤ | y 0 = e}} = X 0 ⁻¹' {e} from rfl,
        prob_step_eq hX 0 he]
    have hm : ℙ {ω | path X ω ∈ A} ≤
        ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) := by
      refine (measure_mono hsub).trans ?_
      refine (measure_union_le _ _).trans ?_
      rw [prob_step_bad hX 0, add_zero]
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      exact measure_union_le _ _
    have hfinE : ∀ e ∈ steps, ℙ (E e) ≠ ⊤ := fun e _ ↦ measure_ne_top ℙ _
    have hs1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have hs2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have hs3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have hs4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    have hsum_ne_top :
        ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) ≠ ⊤ := by
      simp [ENNReal.add_eq_top, hfinE _ hs1, hfinE _ hs2, hfinE _ hs3, hfinE _ hs4]
    have hm_real : (ℙ {ω | path X ω ∈ A}).toReal ≤
        (1 / 4 : ℝ) * ∑ e ∈ stepsF, (ℙ {ω | path X ω ∈ A_slice e}).toReal := by
      have htr := ENNReal.toReal_mono hsum_ne_top hm
      have hF : stepsF = insert (1, 0) (insert (-1, 0) (insert (0, 1) {(0, -1)})) := rfl
      rw [hF, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      rw [ENNReal.toReal_add (by simp [ENNReal.add_eq_top, hfinE _ hs1, hfinE _ hs2, hfinE _ hs3])
          (hfinE _ hs4),
        ENNReal.toReal_add (by simp [ENNReal.add_eq_top, hfinE _ hs1, hfinE _ hs2]) (hfinE _ hs3),
        ENNReal.toReal_add (hfinE _ hs1) (hfinE _ hs2),
        hprobE _ hs1, hprobE _ hs2, hprobE _ hs3, hprobE _ hs4] at htr
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
        show (4 : ℝ≥0∞).toReal = 4 by norm_num] at htr
      linarith
    calc B * (ℙ {ω | path X ω ∈ A}).toReal
        ≤ B * ((1 / 4 : ℝ) * ∑ e ∈ stepsF, (ℙ {ω | path X ω ∈ A_slice e}).toReal) :=
          mul_le_mul_of_nonneg_left hm_real hB0
      _ = (1 / 4 : ℝ) * ∑ e ∈ stepsF, B * (ℙ {ω | path X ω ∈ A_slice e}).toReal := by
          rw [← mul_assoc, mul_comm B, mul_assoc, Finset.mul_sum]
      _ ≤ (1 / 4 : ℝ) * ∑ e ∈ stepsF, u x * expWalk u k (x + e) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum ih) (by positivity)
      _ = expWalk u (k + 1) x := by
          rw [expWalk, ← Finset.mul_sum]; ring

lemma sum_stepsF_add_eq_sub (f : ℤ × ℤ → ℝ) (z : ℤ × ℤ) :
    ∑ e ∈ stepsF, f (z + e) = ∑ e ∈ stepsF, f (z - e) := by
  have hF : stepsF = insert (1, 0) (insert (-1, 0) (insert (0, 1) {(0, -1)})) := rfl
  rw [hF, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have e1 : z + (1, 0) = z - (-1, 0) := by ext <;> dsimp <;> omega
  have e2 : z + (-1, 0) = z - (1, 0) := by ext <;> dsimp <;> omega
  have e3 : z + (0, 1) = z - (0, -1) := by ext <;> dsimp <;> omega
  have e4 : z + (0, -1) = z - (0, 1) := by ext <;> dsimp <;> omega
  rw [e1, e2, e3, e4]
  ring

noncomputable def trialPsi {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ)
    (s : ℝ) (F : Finset (ℤ × ℤ)) (coeff : ℤ × ℤ → ℝ) (x : ℤ × ℤ) : ℝ :=
  1 / (1 - s) + ∑ z ∈ F, coeff z * green X s (x - z)

lemma trialPsi_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (F : Finset (ℤ × ℤ)) (coeff : ℤ × ℤ → ℝ) (x : ℤ × ℤ) :
    1 + s * (1 / 4 : ℝ) * ∑ e ∈ stepsF, trialPsi X s F coeff (x + e) =
      trialPsi X s F coeff x - if x ∈ F then coeff x else 0 := by
  unfold trialPsi
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.ne'
  rw [Finset.sum_add_distrib, Finset.sum_const, show stepsF.card = 4 by decide, nsmul_eq_mul,
    Finset.sum_comm]
  have hinner : ∀ z ∈ F,
      s * (1 / 4 : ℝ) * ∑ e ∈ stepsF, coeff z * green X s (x + e - z) =
        coeff z * (green X s (x - z) - if x = z then 1 else 0) := by
    intro z _
    have heq : (∑ e ∈ stepsF, coeff z * green X s (x + e - z)) =
        coeff z * ∑ e ∈ stepsF, green X s ((x - z) + e) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      have : x + e - z = (x - z) + e := by abel
      rw [this]
    rw [heq, sum_stepsF_add_eq_sub]
    have hg := green_step hX hs0 hs1 (x - z)
    have hxz : (x - z = 0) ↔ (x = z) := sub_eq_zero
    simp only [hxz] at hg
    rw [hg]; ring
  rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl hinner]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  have hdelta : (∑ z ∈ F, if x = z then coeff z else 0) = if x ∈ F then coeff x else 0 := by
    by_cases hx : x ∈ F
    · rw [if_pos hx, Finset.sum_eq_single x (fun z _ hzx ↦ if_neg hzx.symm)
        (fun hnx ↦ absurd hx hnx), if_pos rfl]
    · rw [if_neg hx]
      exact Finset.sum_eq_zero fun z hz ↦ by simp [show x ≠ z from fun h ↦ hx (h ▸ hz)]
  rw [hdelta]
  have hconst : 1 + s * (1 / 4 : ℝ) * ((4 : ℕ) * (1 / (1 - s))) = 1 / (1 - s) := by
    push_cast; field_simp [h1s]; ring
  linarith

lemma expWalk_sum_le_trialPsi {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {F : Finset (ℤ × ℤ)} {u coeff : ℤ × ℤ → ℝ}
    (hu_pos : ∀ x, 0 < u x) (hu_out : ∀ x, x ∉ F → u x = 1)
    (hpsi_nn : ∀ x, 0 ≤ trialPsi X s F coeff x)
    (hpsi_in : ∀ x ∈ F, (1 - (u x)⁻¹) * trialPsi X s F coeff x ≤ coeff x) :
    ∀ (K : ℕ) (x : ℤ × ℤ),
      (∑ k ∈ Finset.range (K + 1), s ^ k * expWalk u k x) ≤ trialPsi X s F coeff x := by
  have hsuper : ∀ x,
      u x * (1 + s * (1 / 4 : ℝ) * ∑ e ∈ stepsF, trialPsi X s F coeff (x + e)) ≤
        trialPsi X s F coeff x := by
    intro x
    rw [trialPsi_step hX hs0 hs1 F coeff x]
    by_cases hx : x ∈ F
    · rw [if_pos hx]
      have hc := hpsi_in x hx
      have h1 : trialPsi X s F coeff x - coeff x ≤ (u x)⁻¹ * trialPsi X s F coeff x := by
        linarith [show (1 - (u x)⁻¹) * trialPsi X s F coeff x =
          trialPsi X s F coeff x - (u x)⁻¹ * trialPsi X s F coeff x by ring]
      have hmul := mul_le_mul_of_nonneg_left h1 (hu_pos x).le
      rwa [← mul_assoc, mul_inv_cancel₀ (hu_pos x).ne', one_mul] at hmul
    · rw [if_neg hx, sub_zero, hu_out x hx, one_mul]
  intro K
  induction K with
  | zero =>
    intro x
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, expWalk]
    have hnn : 0 ≤ s * (1 / 4 : ℝ) * ∑ e ∈ stepsF, trialPsi X s F coeff (x + e) :=
      mul_nonneg (mul_nonneg hs0 (by positivity)) (Finset.sum_nonneg fun e _ ↦ hpsi_nn _)
    calc u x = u x * 1 := (mul_one _).symm
      _ ≤ u x * (1 + s * (1 / 4 : ℝ) * ∑ e ∈ stepsF, trialPsi X s F coeff (x + e)) :=
          mul_le_mul_of_nonneg_left (by linarith) (hu_pos x).le
      _ ≤ trialPsi X s F coeff x := hsuper x
  | succ K ih =>
    intro x
    rw [Finset.sum_range_succ', pow_zero, one_mul, expWalk]
    have hrec : (∑ k ∈ Finset.range (K + 1), s ^ (k + 1) * expWalk u (k + 1) x) =
        u x * (s * (1 / 4 : ℝ) *
          ∑ e ∈ stepsF, ∑ k ∈ Finset.range (K + 1), s ^ k * expWalk u k (x + e)) := by
      have h1 : ∀ k, s ^ (k + 1) * expWalk u (k + 1) x =
          u x * (s * (1 / 4 : ℝ)) * ∑ e ∈ stepsF, s ^ k * expWalk u k (x + e) := by
        intro k
        rw [expWalk, pow_succ]
        simp_rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ ↦ by ring
      simp_rw [h1]
      rw [← Finset.mul_sum, Finset.sum_comm, mul_assoc]
    rw [hrec]
    have hsum_le : (∑ e ∈ stepsF, ∑ k ∈ Finset.range (K + 1), s ^ k * expWalk u k (x + e)) ≤
        ∑ e ∈ stepsF, trialPsi X s F coeff (x + e) :=
      Finset.sum_le_sum fun e _ ↦ ih (x + e)
    calc u x * (s * (1 / 4 : ℝ) *
            ∑ e ∈ stepsF, ∑ k ∈ Finset.range (K + 1), s ^ k * expWalk u k (x + e)) + u x
        = u x * (1 + s * (1 / 4 : ℝ) *
            ∑ e ∈ stepsF, ∑ k ∈ Finset.range (K + 1), s ^ k * expWalk u k (x + e)) := by ring
      _ ≤ u x * (1 + s * (1 / 4 : ℝ) * ∑ e ∈ stepsF, trialPsi X s F coeff (x + e)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ 1) (hu_pos x).le
          exact mul_le_mul_of_nonneg_left hsum_le (mul_nonneg hs0 (by positivity))
      _ ≤ trialPsi X s F coeff x := hsuper x

lemma feynman_kac_chernoff {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {F : Finset (ℤ × ℤ)} {u coeff : ℤ × ℤ → ℝ}
    (hu_pos : ∀ x, 0 < u x) (hu_out : ∀ x, x ∉ F → u x = 1)
    (hpsi_nn : ∀ x, 0 ≤ trialPsi X s F coeff x)
    (hpsi_in : ∀ x ∈ F, (1 - (u x)⁻¹) * trialPsi X s F coeff x ≤ coeff x)
    {A : ℕ → Set (ℕ → ℤ × ℤ)} (hA : ∀ k, Det k (A k))
    {B : ℝ} (hB0 : 0 ≤ B) (hBA : ∀ k, ∀ y ∈ A k, B ≤ prodWalk u 0 y k) (K : ℕ) :
    B * (∑ k ∈ Finset.range (K + 1), s ^ k * (ℙ {ω | path X ω ∈ A k}).toReal) ≤
      1 / (1 - s) + ∑ z ∈ F, coeff z * green X s z := by
  rw [Finset.mul_sum]
  have hstep : ∀ k ∈ Finset.range (K + 1),
      B * (s ^ k * (ℙ {ω | path X ω ∈ A k}).toReal) ≤ s ^ k * expWalk u k 0 := by
    intro k _
    have hm := markov_chernoff hX hu_pos k 0 (hA k) hB0 (hBA k)
    calc B * (s ^ k * (ℙ {ω | path X ω ∈ A k}).toReal)
        = s ^ k * (B * (ℙ {ω | path X ω ∈ A k}).toReal) := by ring
      _ ≤ s ^ k * expWalk u k 0 := mul_le_mul_of_nonneg_left hm (pow_nonneg hs0 k)
  refine (Finset.sum_le_sum hstep).trans ?_
  refine (expWalk_sum_le_trialPsi hX hs0 hs1 hu_pos hu_out hpsi_nn hpsi_in K 0).trans ?_
  apply le_of_eq
  unfold trialPsi
  congr 1
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [zero_sub, green_symm hX]

/- ### Section 4: Single-Site Local Time Lower Bound via Renewal Identity -/

lemma locShift_zero_mono {y : ℕ → ℤ × ℤ} {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) (z : ℤ × ℤ) :
    locShift 0 y t₁ z ≤ locShift 0 y t₂ z := by
  unfold locShift
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (Nat.succ_le_succ ht)))

lemma locShift_zero_succ (y : ℕ → ℤ × ℤ) (t : ℕ) (z : ℤ × ℤ) :
    locShift 0 y (t + 1) z = locShift 0 y t z + if pos y (t + 1) = z then 1 else 0 := by
  simp only [locShift, zero_add]
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · exact Finset.card_insert_of_notMem (by simp)
  · rw [add_zero]

lemma locShift_zero_zero (y : ℕ → ℤ × ℤ) (z : ℤ × ℤ) :
    locShift 0 y 0 z = if z = 0 then 1 else 0 := by
  simp only [locShift, zero_add, Finset.range_one, Finset.filter_singleton, pos_zero]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

/-- `m`-th visit to `z` occurs at time `t`. -/
def hitAt (m : ℕ) (z : ℤ × ℤ) (t : ℕ) : Set (ℕ → ℤ × ℤ) :=
  {y | pos y t = z ∧ locShift 0 y t z = m}

/-- First return to `0` occurs at time `t ≥ 1`. -/
def retAt (t : ℕ) : Set (ℕ → ℤ × ℤ) :=
  {y | 1 ≤ t ∧ pos y t = 0 ∧ locShift 0 y t 0 = 2}

lemma det_hitAt (m : ℕ) (z : ℤ × ℤ) (t : ℕ) : Det t (hitAt m z t) := fun y y' h hy ↦ by
  rcases hy with ⟨hp, hl⟩
  refine ⟨by rw [← pos_congr h le_rfl, hp], ?_⟩
  rw [← hl]
  simp only [locShift, zero_add]
  congr 1
  refine Finset.filter_congr fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [pos_congr h (by omega)]

lemma det_retAt (t : ℕ) : Det t (retAt t) := fun y y' h hy ↦ by
  rcases hy with ⟨ht, hp, hl⟩
  refine ⟨ht, by rw [← pos_congr h le_rfl, hp], ?_⟩
  rw [← hl]
  simp only [locShift, zero_add]
  congr 1
  refine Finset.filter_congr fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [pos_congr h (by omega)]

lemma hitAt_disjoint {m : ℕ} (_hm : 1 ≤ m) (z : ℤ × ℤ) {t₁ t₂ : ℕ} (hne : t₁ ≠ t₂) :
    Disjoint (hitAt m z t₁) (hitAt m z t₂) := by
  rw [Set.disjoint_left]
  intro y h1 h2
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · have hm1 : m ≤ locShift 0 y (t₂ - 1) z := by
      rw [← h1.2]
      exact locShift_zero_mono (by omega) z
    have hsucc := locShift_zero_succ y (t₂ - 1) z
    rw [show t₂ - 1 + 1 = t₂ by omega, if_pos h2.1, h2.2] at hsucc
    omega
  · exact hne heq
  · have hm1 : m ≤ locShift 0 y (t₁ - 1) z := by
      rw [← h2.2]
      exact locShift_zero_mono (by omega) z
    have hsucc := locShift_zero_succ y (t₁ - 1) z
    rw [show t₁ - 1 + 1 = t₁ by omega, if_pos h1.1, h1.2] at hsucc
    omega

lemma retAt_disjoint {t₁ t₂ : ℕ} (hne : t₁ ≠ t₂) : Disjoint (retAt t₁) (retAt t₂) := by
  refine (hitAt_disjoint (by omega : 1 ≤ 2) 0 hne).mono ?_ ?_
  · exact fun y hy ↦ ⟨hy.2.1, hy.2.2⟩
  · exact fun y hy ↦ ⟨hy.2.1, hy.2.2⟩

lemma hitAt_subset_locShift {m : ℕ} (z : ℤ × ℤ) {t M : ℕ} (ht : t ≤ M) :
    hitAt m z t ⊆ {y | m ≤ locShift 0 y M z} := by
  intro y hy
  exact hy.2 ▸ locShift_zero_mono ht z

lemma pos_eq_biUnion_hitAt_one (z : ℤ × ℤ) (n : ℕ) :
    {y : ℕ → ℤ × ℤ | pos y n = z} =
      ⋃ t ∈ Finset.range (n + 1), {y | y ∈ hitAt 1 z t ∧ sh t y ∈ {y' | pos y' (n - t) = 0}} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · intro hn
    let S := (Finset.range (n + 1)).filter fun k ↦ pos y k = z
    have hne : S.Nonempty := ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn⟩⟩
    let t := S.min' hne
    have htS : t ∈ S := S.min'_mem hne
    have htn : t ≤ n := by have := (Finset.mem_filter.mp htS).1; rw [Finset.mem_range] at this; omega
    have hpt : pos y t = z := (Finset.mem_filter.mp htS).2
    have hfilt : (Finset.range (t + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = z) = {t} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, zero_add, Finset.mem_singleton]
      constructor
      · rintro ⟨hj, hpj⟩
        have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpj⟩
        have htj : t ≤ j := S.min'_le j hjS
        omega
      · rintro rfl
        exact ⟨by omega, hpt⟩
    refine ⟨t, by omega, ⟨hpt, ?_⟩, ?_⟩
    · simp only [locShift, hfilt, Finset.card_singleton]
    · have hsh := pos_shift y t (n - t)
      rw [show t + (n - t) = n by omega, hn, hpt] at hsh
      exact add_left_cancel (hsh.symm.trans (add_zero z).symm)
  · rintro ⟨t, ht, ⟨hpt, _⟩, hsh⟩
    have := pos_shift y t (n - t)
    rw [show t + (n - t) = n by omega, hpt, hsh, add_zero] at this
    exact this

lemma pos_zero_eq_biUnion_retAt {n : ℕ} (hn : 1 ≤ n) :
    {y : ℕ → ℤ × ℤ | pos y n = 0} =
      ⋃ t ∈ Finset.range (n + 1), {y | y ∈ retAt t ∧ sh t y ∈ {y' | pos y' (n - t) = 0}} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · intro hpn
    let S := (Finset.Icc 1 n).filter fun k ↦ pos y k = 0
    have hne : S.Nonempty := ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn, le_rfl⟩, hpn⟩⟩
    let t := S.min' hne
    have htS : t ∈ S := S.min'_mem hne
    have htIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp htS).1
    have hpt : pos y t = 0 := (Finset.mem_filter.mp htS).2
    have hfilt : (Finset.range (t + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = 0) = {0, t} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, zero_add, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hj, hpj⟩
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · exact Or.inl rfl
        · right
          have hjS : j ∈ S := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hj0, by omega⟩, hpj⟩
          have htj : t ≤ j := S.min'_le j hjS
          omega
      · rintro (rfl | rfl)
        · exact ⟨by omega, pos_zero y⟩
        · exact ⟨by omega, hpt⟩
    refine ⟨t, by omega, ⟨htIcc.1, hpt, ?_⟩, ?_⟩
    · simp only [locShift, hfilt]
      exact Finset.card_pair (by omega)
    · have hsh := pos_shift y t (n - t)
      rw [show t + (n - t) = n by omega, hpn, hpt, zero_add] at hsh
      exact hsh.symm
  · rintro ⟨t, ht, ⟨_, hpt, _⟩, hsh⟩
    have := pos_shift y t (n - t)
    rw [show t + (n - t) = n by omega, hpt, hsh, add_zero] at this
    exact this

lemma hitAt_succ_eq_biUnion {m : ℕ} (hm : 1 ≤ m) (z : ℤ × ℤ) (n : ℕ) :
    hitAt (m + 1) z n =
      ⋃ t ∈ Finset.range (n + 1), {y | y ∈ hitAt m z t ∧ sh t y ∈ retAt (n - t)} := by
  ext y
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨hpn, hln⟩
    let S := (Finset.range n).filter fun k ↦ pos y k = z
    have hfin : (Finset.range (n + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = z) =
        insert n S := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, zero_add, Finset.mem_insert, S]
      constructor
      · rintro ⟨hj, hpj⟩
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨hlt, hpj⟩
      · rintro (rfl | ⟨hlt, hpj⟩)
        · exact ⟨Nat.lt_succ_self _, hpn⟩
        · exact ⟨by omega, hpj⟩
    have hcard : S.card = m := by
      have hln' : ((Finset.range (n + 1)).filter fun j ↦ (0 : ℤ × ℤ) + pos y j = z).card = m + 1 :=
        hln
      rw [hfin, Finset.card_insert_of_notMem (by simp [S])] at hln'
      omega
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let t := S.max' hne
    have htS : t ∈ S := S.max'_mem hne
    have htn : t < n := Finset.mem_range.mp (Finset.mem_filter.mp htS).1
    have hpt : pos y t = z := (Finset.mem_filter.mp htS).2
    have hfilt_t : (Finset.range (t + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = z) = S := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, zero_add, S]
      constructor
      · rintro ⟨hj, hpj⟩
        exact ⟨by omega, hpj⟩
      · rintro ⟨hj, hpj⟩
        have hjt : j ≤ t := S.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hpj⟩)
        exact ⟨by omega, hpj⟩
    have hsh_pos : pos (sh t y) (n - t) = 0 := by
      have hsh := pos_shift y t (n - t)
      rw [show t + (n - t) = n by omega, hpn, hpt] at hsh
      exact add_left_cancel (hsh.symm.trans (add_zero z).symm)
    have hfilt_sh : (Finset.range (n - t + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos (sh t y) j = 0) =
        {0, n - t} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, zero_add, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hj, hpj⟩
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · exact Or.inl rfl
        · by_contra hne_nt
          have hj_lt : j < n - t := by omega
          have hmem : t + j ∈ S := by
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨by omega, ?_⟩
            rw [pos_shift, hpt, hpj, add_zero]
          have hle := S.le_max' (t + j) hmem
          omega
      · rintro (rfl | rfl)
        · exact ⟨by omega, pos_zero _⟩
        · exact ⟨by omega, hsh_pos⟩
    refine ⟨t, by omega, ⟨hpt, ?_⟩, ⟨by omega, hsh_pos, ?_⟩⟩
    · simp only [locShift, hfilt_t, hcard]
    · simp only [locShift, hfilt_sh]
      exact Finset.card_pair (by omega)
  · rintro ⟨t, ht, ⟨hpt, hlt⟩, ⟨hnt, hsh_pos, hsh_loc⟩⟩
    have hpn : pos y n = z := by
      rw [show n = t + (n - t) by omega, pos_shift, hpt, hsh_pos, add_zero]
    refine ⟨hpn, ?_⟩
    have hsub : {0, n - t} ⊆
        (Finset.range (n - t + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos (sh t y) j = 0) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_filter, Finset.mem_range, zero_add]
      rcases hj with rfl | rfl
      · exact ⟨by omega, pos_zero _⟩
      · exact ⟨by omega, hsh_pos⟩
    have heq_sh : (Finset.range (n - t + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos (sh t y) j = 0) =
        {0, n - t} := by
      refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
      rw [Finset.card_pair (by omega)]
      exact hsh_loc.le
    have hsplit : (Finset.range (n + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = z) =
        insert n ((Finset.range (t + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = z)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, zero_add, Finset.mem_insert]
      constructor
      · rintro ⟨hj, hpj⟩
        rcases le_or_gt j t with hjt | htj
        · exact Or.inr ⟨by omega, hpj⟩
        · left
          have hmem : j - t ∈
              (Finset.range (n - t + 1)).filter (fun i ↦ (0 : ℤ × ℤ) + pos (sh t y) i = 0) := by
            simp only [Finset.mem_filter, Finset.mem_range, zero_add]
            refine ⟨by omega, ?_⟩
            have h1 := pos_shift y t (j - t)
            rw [show t + (j - t) = j by omega, hpj, hpt] at h1
            exact add_left_cancel (h1.symm.trans (add_zero z).symm)
          rw [heq_sh, Finset.mem_insert, Finset.mem_singleton] at hmem
          omega
      · rintro (rfl | ⟨hjt, hpj⟩)
        · exact ⟨by omega, hpn⟩
        · exact ⟨by omega, hpj⟩
    have hn_not : n ∉ (Finset.range (t + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = z) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    have hcard : ((Finset.range (n + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = z)).card =
        ((Finset.range (t + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = z)).card + 1 := by
      rw [hsplit, Finset.card_insert_of_notMem hn_not]
    change ((Finset.range (n + 1)).filter (fun j ↦ (0 : ℤ × ℤ) + pos y j = z)).card = m + 1
    rw [hcard]
    exact congrArg (· + 1) hlt

noncomputable def qHit {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ)
    (m : ℕ) (z : ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | path X ω ∈ hitAt m z t}).toReal

noncomputable def qRet {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | path X ω ∈ retAt t}).toReal

lemma qHit_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (m : ℕ) (z : ℤ × ℤ) (t : ℕ) :
    0 ≤ qHit X m z t := ENNReal.toReal_nonneg

lemma qRet_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) :
    0 ≤ qRet X t := ENNReal.toReal_nonneg

lemma qRet_zero {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) : qRet X 0 = 0 := by
  have hemp : {ω : Ω | path X ω ∈ retAt 0} = ∅ := by
    ext ω; simp [retAt]
  simp [qRet, hemp]

lemma sum_qHit_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} (hm : 1 ≤ m)
    (z : ℤ × ℤ) (N : ℕ) : ∑ t ∈ Finset.range N, qHit X m z t ≤ 1 := by
  have hdisj : Set.PairwiseDisjoint (Finset.range N : Set ℕ)
      fun t ↦ {ω : Ω | path X ω ∈ hitAt m z t} := by
    intro t₁ _ t₂ _ hne
    exact (hitAt_disjoint hm z hne).preimage (path X)
  have hmeas : ∀ t ∈ Finset.range N, MeasurableSet {ω : Ω | path X ω ∈ hitAt m z t} := fun t _ ↦ by
    rw [path_eq]; exact det_meas hX (det_hitAt m z t) 0
  have hle : (∑ t ∈ Finset.range N, ℙ {ω | path X ω ∈ hitAt m z t}) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact prob_le_one
  have hfin : ∀ t ∈ Finset.range N, ℙ {ω | path X ω ∈ hitAt m z t} ≠ ⊤ :=
    fun _ _ ↦ measure_ne_top ℙ _
  have hr := ENNReal.toReal_mono ENNReal.one_ne_top hle
  rw [ENNReal.toReal_sum hfin, ENNReal.toReal_one] at hr
  exact hr

lemma summable_qHit {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} (hm : 1 ≤ m) (z : ℤ × ℤ) :
    Summable (qHit X m z) :=
  summable_of_sum_range_le (fun t ↦ qHit_nonneg X m z t) (sum_qHit_le_one hX hm z)

lemma tsum_qHit_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} (hm : 1 ≤ m) (z : ℤ × ℤ) :
    ∑' t : ℕ, qHit X m z t ≤ 1 :=
  Real.tsum_le_of_sum_range_le (fun t ↦ qHit_nonneg X m z t) (sum_qHit_le_one hX hm z)

lemma sum_qRet_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (N : ℕ) :
    ∑ t ∈ Finset.range N, qRet X t ≤ 1 := by
  have hdisj : Set.PairwiseDisjoint (Finset.range N : Set ℕ)
      fun t ↦ {ω : Ω | path X ω ∈ retAt t} := fun t₁ _ t₂ _ hne ↦
    (retAt_disjoint hne).preimage (path X)
  have hmeas : ∀ t ∈ Finset.range N, MeasurableSet {ω : Ω | path X ω ∈ retAt t} := fun t _ ↦ by
    rw [path_eq]; exact det_meas hX (det_retAt t) 0
  have hle : (∑ t ∈ Finset.range N, ℙ {ω | path X ω ∈ retAt t}) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact prob_le_one
  have hfin : ∀ t ∈ Finset.range N, ℙ {ω | path X ω ∈ retAt t} ≠ ⊤ :=
    fun _ _ ↦ measure_ne_top ℙ _
  have hr := ENNReal.toReal_mono ENNReal.one_ne_top hle
  rw [ENNReal.toReal_sum hfin, ENNReal.toReal_one] at hr
  exact hr

lemma summable_qRet {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    Summable (qRet X) :=
  summable_of_sum_range_le (fun t ↦ qRet_nonneg X t) (sum_qRet_le_one hX)

lemma p_eq_sum_hitAt_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (z : ℤ × ℤ) (n : ℕ) :
    p X z n = ∑ t ∈ Finset.range (n + 1), qHit X 1 z t * p X 0 (n - t) := by
  have hset : {ω : Ω | pos (path X ω) n = z} =
      ⋃ t ∈ Finset.range (n + 1),
        {ω | path X ω ∈ hitAt 1 z t ∧ sh t (path X ω) ∈ {y' | pos y' (n - t) = 0}} := by
    ext ω
    have := congrArg (path X ω ∈ ·) (pos_eq_biUnion_hitAt_one z n)
    simpa [Set.mem_iUnion] using this
  have hdisj : Set.PairwiseDisjoint (Finset.range (n + 1) : Set ℕ)
      (fun t ↦ {ω : Ω | path X ω ∈ hitAt 1 z t ∧ sh t (path X ω) ∈ {y' | pos y' (n - t) = 0}}) := by
    intro t₁ _ t₂ _ hne
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro ω ⟨h1, _⟩ ⟨h2, _⟩
    exact (hitAt_disjoint le_rfl z hne).notMem_of_mem_left h1 h2
  have hmeas : ∀ t ∈ Finset.range (n + 1),
      MeasurableSet {ω : Ω | path X ω ∈ hitAt 1 z t ∧ sh t (path X ω) ∈ {y' | pos y' (n - t) = 0}} :=
    fun t _ ↦ meas_block hX (det_hitAt 1 z t) (det_pos (n - t) 0)
  have hm : ℙ {ω : Ω | pos (path X ω) n = z} =
      ∑ t ∈ Finset.range (n + 1),
        ℙ {ω : Ω | path X ω ∈ hitAt 1 z t ∧ sh t (path X ω) ∈ {y' | pos y' (n - t) = 0}} := by
    rw [hset, measure_biUnion_finset hdisj hmeas]
  have hr := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top ℙ _)] at hr
  refine hr.trans (Finset.sum_congr rfl fun t _ ↦ ?_)
  rw [prob_block hX (det_hitAt 1 z t) (det_pos (n - t) 0), ENNReal.toReal_mul]
  rfl

lemma p_zero_eq_sum_retAt {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {n : ℕ} (hn : 1 ≤ n) :
    p X 0 n = ∑ t ∈ Finset.range (n + 1), qRet X t * p X 0 (n - t) := by
  have hset : {ω : Ω | pos (path X ω) n = 0} =
      ⋃ t ∈ Finset.range (n + 1),
        {ω | path X ω ∈ retAt t ∧ sh t (path X ω) ∈ {y' | pos y' (n - t) = 0}} := by
    ext ω
    have := congrArg (path X ω ∈ ·) (pos_zero_eq_biUnion_retAt hn)
    simpa [Set.mem_iUnion] using this
  have hdisj : Set.PairwiseDisjoint (Finset.range (n + 1) : Set ℕ)
      (fun t ↦ {ω : Ω | path X ω ∈ retAt t ∧ sh t (path X ω) ∈ {y' | pos y' (n - t) = 0}}) := by
    intro t₁ _ t₂ _ hne
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro ω ⟨h1, _⟩ ⟨h2, _⟩
    exact (retAt_disjoint hne).notMem_of_mem_left h1 h2
  have hmeas : ∀ t ∈ Finset.range (n + 1),
      MeasurableSet {ω : Ω | path X ω ∈ retAt t ∧ sh t (path X ω) ∈ {y' | pos y' (n - t) = 0}} :=
    fun t _ ↦ meas_block hX (det_retAt t) (det_pos (n - t) 0)
  have hm : ℙ {ω : Ω | pos (path X ω) n = 0} =
      ∑ t ∈ Finset.range (n + 1),
        ℙ {ω : Ω | path X ω ∈ retAt t ∧ sh t (path X ω) ∈ {y' | pos y' (n - t) = 0}} := by
    rw [hset, measure_biUnion_finset hdisj hmeas]
  have hr := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top ℙ _)] at hr
  refine hr.trans (Finset.sum_congr rfl fun t _ ↦ ?_)
  rw [prob_block hX (det_retAt t) (det_pos (n - t) 0), ENNReal.toReal_mul]
  rfl

lemma qHit_succ_eq_sum {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} (hm : 1 ≤ m)
    (z : ℤ × ℤ) (n : ℕ) :
    qHit X (m + 1) z n = ∑ t ∈ Finset.range (n + 1), qHit X m z t * qRet X (n - t) := by
  have hset : {ω : Ω | path X ω ∈ hitAt (m + 1) z n} =
      ⋃ t ∈ Finset.range (n + 1),
        {ω | path X ω ∈ hitAt m z t ∧ sh t (path X ω) ∈ retAt (n - t)} := by
    ext ω
    have := congrArg (path X ω ∈ ·) (hitAt_succ_eq_biUnion hm z n)
    simpa [Set.mem_iUnion] using this
  have hdisj : Set.PairwiseDisjoint (Finset.range (n + 1) : Set ℕ)
      (fun t ↦ {ω : Ω | path X ω ∈ hitAt m z t ∧ sh t (path X ω) ∈ retAt (n - t)}) := by
    intro t₁ _ t₂ _ hne
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro ω ⟨h1, _⟩ ⟨h2, _⟩
    exact (hitAt_disjoint hm z hne).notMem_of_mem_left h1 h2
  have hmeas : ∀ t ∈ Finset.range (n + 1),
      MeasurableSet {ω : Ω | path X ω ∈ hitAt m z t ∧ sh t (path X ω) ∈ retAt (n - t)} :=
    fun t _ ↦ meas_block hX (det_hitAt m z t) (det_retAt (n - t))
  have hm_eq : ℙ {ω : Ω | path X ω ∈ hitAt (m + 1) z n} =
      ∑ t ∈ Finset.range (n + 1),
        ℙ {ω : Ω | path X ω ∈ hitAt m z t ∧ sh t (path X ω) ∈ retAt (n - t)} := by
    rw [hset, measure_biUnion_finset hdisj hmeas]
  have hr := congrArg ENNReal.toReal hm_eq
  rw [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top ℙ _)] at hr
  refine hr.trans (Finset.sum_congr rfl fun t _ ↦ ?_)
  rw [prob_block hX (det_hitAt m z t) (det_retAt (n - t)), ENNReal.toReal_mul]
  rfl

noncomputable def genHit {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ)
    (s : ℝ) (m : ℕ) (z : ℤ × ℤ) : ℝ :=
  ∑' t : ℕ, s ^ t * qHit X m z t

noncomputable def genRet {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (s : ℝ) : ℝ :=
  ∑' t : ℕ, s ^ t * qRet X t

lemma summable_genHit {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {m : ℕ} (hm : 1 ≤ m) (z : ℤ × ℤ) :
    Summable (fun t : ℕ ↦ s ^ t * qHit X m z t) :=
  Summable.of_nonneg_of_le (fun t ↦ mul_nonneg (pow_nonneg hs0 t) (qHit_nonneg X m z t))
    (fun t ↦ mul_le_of_le_one_right (pow_nonneg hs0 t)
      ((summable_qHit hX hm z).le_tsum t (fun k _ ↦ qHit_nonneg X m z k) |>.trans
        (tsum_qHit_le_one hX hm z)))
    (summable_geometric_of_lt_one hs0 hs1)

lemma summable_genRet {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun t : ℕ ↦ s ^ t * qRet X t) :=
  Summable.of_nonneg_of_le (fun t ↦ mul_nonneg (pow_nonneg hs0 t) (qRet_nonneg X t))
    (fun t ↦ mul_le_of_le_one_right (pow_nonneg hs0 t)
      (((summable_qRet hX).le_tsum t (fun k _ ↦ qRet_nonneg X k)).trans
        (Real.tsum_le_of_sum_range_le (fun k ↦ qRet_nonneg X k) (sum_qRet_le_one hX))))
    (summable_geometric_of_lt_one hs0 hs1)

lemma green_eq_genHit_mul_green_zero {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (z : ℤ × ℤ) :
    green X s z = genHit X s 1 z * green X s 0 := by
  have h1 := summable_genHit hX hs0 hs1 le_rfl z
  have h2 := summable_green X hs0 hs1 0
  have hn1 : Summable (fun t ↦ ‖s ^ t * qHit X 1 z t‖) :=
    h1.congr fun t ↦ (Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs0 _) (qHit_nonneg X 1 z _))).symm
  have hn2 : Summable (fun t ↦ ‖s ^ t * p X 0 t‖) :=
    h2.congr fun t ↦ (Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs0 _) (p_nonneg X 0 _))).symm
  have hc := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hn1 hn2
  symm
  refine hc.trans (tsum_congr fun n ↦ ?_)
  rw [p_eq_sum_hitAt_one hX z n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [Finset.mem_range] at ht
  rw [show (s ^ t * qHit X 1 z t) * (s ^ (n - t) * p X 0 (n - t)) =
    (s ^ t * s ^ (n - t)) * (qHit X 1 z t * p X 0 (n - t)) by ring,
    ← pow_add, show t + (n - t) = n by omega]

lemma green_zero_eq_one_add_genRet_mul {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    green X s 0 = 1 + genRet X s * green X s 0 := by
  have h1 := summable_genRet hX hs0 hs1
  have h2 := summable_green X hs0 hs1 0
  have hn1 : Summable (fun t ↦ ‖s ^ t * qRet X t‖) :=
    h1.congr fun t ↦ (Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs0 _) (qRet_nonneg X _))).symm
  have hn2 : Summable (fun t ↦ ‖s ^ t * p X 0 t‖) :=
    h2.congr fun t ↦ (Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs0 _) (p_nonneg X 0 _))).symm
  have hc := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hn1 hn2
  have hsum_ret : (∑' n : ℕ, ∑ t ∈ Finset.range (n + 1),
      (s ^ t * qRet X t) * (s ^ (n - t) * p X 0 (n - t))) =
      ∑' n : ℕ, (if n = 0 then (0 : ℝ) else s ^ n * p X 0 n) := by
    refine tsum_congr fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [qRet_zero]
    · rw [if_neg hn.ne', p_zero_eq_sum_retAt hX hn, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht ↦ ?_
      rw [Finset.mem_range] at ht
      rw [show (s ^ t * qRet X t) * (s ^ (n - t) * p X 0 (n - t)) =
        (s ^ t * s ^ (n - t)) * (qRet X t * p X 0 (n - t)) by ring,
        ← pow_add, show t + (n - t) = n by omega]
  have hgr : green X s 0 = 1 + ∑' n : ℕ, (if n = 0 then (0 : ℝ) else s ^ n * p X 0 n) := by
    have hs_gr := (summable_green X hs0 hs1 0).tsum_eq_zero_add
    unfold green at hs_gr ⊢
    rw [hs_gr]
    simp only [pow_zero, one_mul, p_zero_at hX, ↓reduceIte]
    congr 1
    have hsum_ite : Summable (fun n : ℕ ↦ if n = 0 then (0 : ℝ) else s ^ n * p X 0 n) :=
      (summable_nat_add_iff 1).mp (((summable_nat_add_iff 1).mpr (summable_green X hs0 hs1 0)).congr
        fun n ↦ by simp)
    rw [hsum_ite.tsum_eq_zero_add, if_pos rfl, zero_add]
    exact tsum_congr fun n ↦ by simp
  conv_lhs => rw [hgr, ← hsum_ret, ← hc]
  rfl

lemma genHit_succ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {m : ℕ} (hm : 1 ≤ m) (z : ℤ × ℤ) :
    genHit X s (m + 1) z = genHit X s m z * genRet X s := by
  have h1 := summable_genHit hX hs0 hs1 hm z
  have h2 := summable_genRet hX hs0 hs1
  have hn1 : Summable (fun t ↦ ‖s ^ t * qHit X m z t‖) :=
    h1.congr fun t ↦ (Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs0 _) (qHit_nonneg X m z _))).symm
  have hn2 : Summable (fun t ↦ ‖s ^ t * qRet X t‖) :=
    h2.congr fun t ↦ (Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs0 _) (qRet_nonneg X _))).symm
  have hc := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hn1 hn2
  symm
  refine hc.trans (tsum_congr fun n ↦ ?_)
  rw [qHit_succ_eq_sum hX hm z n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [Finset.mem_range] at ht
  rw [show (s ^ t * qHit X m z t) * (s ^ (n - t) * qRet X (n - t)) =
    (s ^ t * s ^ (n - t)) * (qHit X m z t * qRet X (n - t)) by ring,
    ← pow_add, show t + (n - t) = n by omega]

lemma one_le_green_zero {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    1 ≤ green X s 0 := by
  have hs_gr := (summable_green X hs0 hs1 0).tsum_eq_zero_add
  unfold green
  rw [hs_gr]
  simp only [pow_zero, one_mul, p_zero_at hX, ↓reduceIte]
  exact le_add_of_nonneg_right (tsum_nonneg fun n ↦ mul_nonneg (pow_nonneg hs0 _) (p_nonneg X 0 _))

lemma genHit_eq {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {m : ℕ} (hm : 1 ≤ m) (z : ℤ × ℤ) :
    genHit X s m z = (green X s z / green X s 0) * (1 - 1 / green X s 0) ^ (m - 1) := by
  have hg0 : 0 < green X s 0 := lt_of_lt_of_le zero_lt_one (one_le_green_zero hX hs0 hs1)
  have h1 : genHit X s 1 z = green X s z / green X s 0 := by
    rw [eq_div_iff hg0.ne', green_eq_genHit_mul_green_zero hX hs0 hs1 z]
  have hret : genRet X s = 1 - 1 / green X s 0 := by
    have h0 := green_zero_eq_one_add_genRet_mul hX hs0 hs1
    field_simp [hg0.ne']
    linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    have hk1 : 1 ≤ k + 1 := by omega
    rw [show k + 1 + 1 = (k + 1) + 1 by omega, genHit_succ hX hs0 hs1 hk1 z, ih hk1, hret]
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]
    ring

lemma prob_locShift_ge_of_genHit {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {m : ℕ} (hm : 1 ≤ m) (z : ℤ × ℤ) (M : ℕ) :
    (green X s z / green X s 0) * (1 - 1 / green X s 0) ^ (m - 1) - s ^ (M + 1) ≤
      (ℙ {ω | m ≤ locShift 0 (path X ω) M z}).toReal := by
  rw [← genHit_eq hX hs0 hs1 hm z]
  have hsub : (⋃ t ∈ Finset.range (M + 1), {ω : Ω | path X ω ∈ hitAt m z t}) ⊆
      {ω : Ω | m ≤ locShift 0 (path X ω) M z} := by
    intro ω hω
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hω
    obtain ⟨t, ht, hmem⟩ := hω
    exact hitAt_subset_locShift z (by omega) hmem
  have hdisj : Set.PairwiseDisjoint (Finset.range (M + 1) : Set ℕ)
      fun t ↦ {ω : Ω | path X ω ∈ hitAt m z t} := fun t₁ _ t₂ _ hne ↦
    (hitAt_disjoint hm z hne).preimage (path X)
  have hmeas : ∀ t ∈ Finset.range (M + 1), MeasurableSet {ω : Ω | path X ω ∈ hitAt m z t} :=
    fun t _ ↦ by rw [path_eq]; exact det_meas hX (det_hitAt m z t) 0
  have hm_le : (∑ t ∈ Finset.range (M + 1), ℙ {ω | path X ω ∈ hitAt m z t}) ≤
      ℙ {ω | m ≤ locShift 0 (path X ω) M z} := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact measure_mono hsub
  have hr_le : ∑ t ∈ Finset.range (M + 1), qHit X m z t ≤
      (ℙ {ω | m ≤ locShift 0 (path X ω) M z}).toReal := by
    have h1 := ENNReal.toReal_mono (measure_ne_top ℙ _) hm_le
    rwa [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top ℙ _)] at h1
  have hpref : ∑ t ∈ Finset.range (M + 1), s ^ t * qHit X m z t ≤
      ∑ t ∈ Finset.range (M + 1), qHit X m z t := by
    refine Finset.sum_le_sum fun t _ ↦ ?_
    exact mul_le_of_le_one_left (qHit_nonneg X m z t) (pow_le_one₀ hs0 hs1.le)
  have htail_le : ∑' k : ℕ, s ^ (k + (M + 1)) * qHit X m z (k + (M + 1)) ≤ s ^ (M + 1) := by
    have hs_tail : Summable (fun k : ℕ ↦ s ^ (M + 1) * qHit X m z (k + (M + 1))) :=
      ((summable_nat_add_iff (M + 1)).mpr (summable_qHit hX hm z)).mul_left _
    have hterm : ∀ k : ℕ,
        s ^ (k + (M + 1)) * qHit X m z (k + (M + 1)) ≤
          s ^ (M + 1) * qHit X m z (k + (M + 1)) := by
      intro k
      refine mul_le_mul_of_nonneg_right ?_ (qHit_nonneg X m z _)
      rw [add_comm, pow_add]
      exact mul_le_of_le_one_right (pow_nonneg hs0 _) (pow_le_one₀ hs0 hs1.le)
    have hle1 := ((summable_nat_add_iff (M + 1)).mpr (summable_genHit hX hs0 hs1 hm z)).tsum_le_tsum
      hterm hs_tail
    rw [tsum_mul_left] at hle1
    have hle2 : ∑' k : ℕ, qHit X m z (k + (M + 1)) ≤ 1 := by
      have hsp := (summable_qHit hX hm z).sum_add_tsum_nat_add (M + 1)
      have hp0 : 0 ≤ ∑ t ∈ Finset.range (M + 1), qHit X m z t :=
        Finset.sum_nonneg fun t _ ↦ qHit_nonneg X m z t
      linarith [tsum_qHit_le_one hX hm z]
    calc ∑' k : ℕ, s ^ (k + (M + 1)) * qHit X m z (k + (M + 1))
        ≤ s ^ (M + 1) * ∑' k : ℕ, qHit X m z (k + (M + 1)) := hle1
      _ ≤ s ^ (M + 1) * 1 := mul_le_mul_of_nonneg_left hle2 (pow_nonneg hs0 _)
      _ = s ^ (M + 1) := mul_one _
  have hsp := (summable_genHit hX hs0 hs1 hm z).sum_add_tsum_nat_add (M + 1)
  unfold genHit
  linarith

/- ### Section 5: Geometric Perimeter Estimates and Super-Solution Chernoff Bounds -/

lemma rnorm_neg (q : ℤ × ℤ) : rnorm (-q) = rnorm q := by
  simp [rnorm]

lemma rnorm_add_le (p q : ℤ × ℤ) : rnorm (p + q) ≤ rnorm p + rnorm q := by
  unfold rnorm
  have h1 : (p + q).1.natAbs ≤ p.1.natAbs + q.1.natAbs := by
    simp only [Prod.fst_add]; exact Int.natAbs_add_le _ _
  have h2 : (p + q).2.natAbs ≤ p.2.natAbs + q.2.natAbs := by
    simp only [Prod.snd_add]; exact Int.natAbs_add_le _ _
  omega

lemma rnorm_sub_le (p q : ℤ × ℤ) : rnorm (p - q) ≤ rnorm p + rnorm q := by
  rw [sub_eq_add_neg, ← rnorm_neg q]
  exact rnorm_add_le p (-q)

lemma rnorm_eq_zero_iff (q : ℤ × ℤ) : rnorm q = 0 ↔ q = 0 := by
  unfold rnorm
  constructor
  · intro h
    have h1 : q.1.natAbs = 0 := by omega
    have h2 : q.2.natAbs = 0 := by omega
    ext <;> simp [Int.natAbs_eq_zero.mp h1, Int.natAbs_eq_zero.mp h2]
  · rintro rfl; rfl

def Q0 (Rmax : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (0 : ℤ) ((Rmax : ℤ) - 1) ×ˢ Finset.Icc (0 : ℤ) ((Rmax : ℤ) - 1)

def Qset (Rmax : ℕ) : Finset (ℤ × ℤ) := (Q0 Rmax).image rot

def P0 (p : ℤ × ℤ) (R : ℕ) (σ : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.range R).image fun j : ℕ ↦ (p.1 + σ * (R : ℤ), p.2 + (j : ℤ))

def Prot (p : ℤ × ℤ) (R : ℕ) (σ : ℤ) : Finset (ℤ × ℤ) := (P0 p R σ).image rot

def pdir (p q : ℤ × ℤ) : ℤ := if q.1 ≤ p.1 then 1 else -1

lemma Q0_card {Rmax : ℕ} (_hR : 1 ≤ Rmax) : (Q0 Rmax).card = Rmax ^ 2 := by
  unfold Q0
  rw [Finset.card_product, Int.card_Icc]
  have h : (Rmax : ℤ) - 1 + 1 - 0 = (Rmax : ℤ) := by ring
  rw [h, Int.toNat_natCast, sq]

lemma Qset_card {Rmax : ℕ} (hR : 1 ≤ Rmax) : (Qset Rmax).card = Rmax ^ 2 := by
  rw [Qset, Finset.card_image_of_injective _ rot_injective, Q0_card hR]

lemma mem_Q0_rnorm {Rmax : ℕ} {p : ℤ × ℤ} (hp : p ∈ Q0 Rmax) : rnorm p < Rmax := by
  simp only [Q0, Finset.mem_product, Finset.mem_Icc] at hp
  unfold rnorm
  omega

lemma Q0_sub_rnorm_lt {Rmax : ℕ} {p q : ℤ × ℤ} (hp : p ∈ Q0 Rmax) (hq : q ∈ Q0 Rmax) :
    rnorm (p - q) < Rmax := by
  simp only [Q0, Finset.mem_product, Finset.mem_Icc] at hp hq
  simp only [rnorm, Prod.fst_sub, Prod.snd_sub]
  omega

lemma P0_injOn (p : ℤ × ℤ) (R : ℕ) (σ : ℤ) :
    Function.Injective (fun j : ℕ ↦ (p.1 + σ * (R : ℤ), p.2 + (j : ℤ))) := by
  intro j₁ j₂ h
  have h2 := congrArg Prod.snd h
  dsimp at h2
  omega

lemma P0_card (p : ℤ × ℤ) (R : ℕ) (σ : ℤ) : (P0 p R σ).card = R := by
  rw [P0, Finset.card_image_of_injective _ (P0_injOn p R σ), Finset.card_range]

lemma Prot_card (p : ℤ × ℤ) (R : ℕ) (σ : ℤ) : (Prot p R σ).card = R := by
  rw [Prot, Finset.card_image_of_injective _ rot_injective, P0_card]

lemma mem_P0_rnorm {p : ℤ × ℤ} {R : ℕ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {z₀ : ℤ × ℤ} (hz : z₀ ∈ P0 p R σ) : rnorm (z₀ - p) = R := by
  simp only [P0, Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  unfold rnorm
  rcases hσ with rfl | rfl <;> simp <;> omega

lemma mem_P0_rnorm_sub_q {p q : ℤ × ℤ} {R : ℕ} {z₀ : ℤ × ℤ}
    (hz : z₀ ∈ P0 p R (pdir p q)) :
    R ≤ rnorm (z₀ - q) ∧ rnorm (z₀ - q) ≤ R + rnorm (p - q) := by
  have hdir : pdir p q = 1 ∨ pdir p q = -1 := by
    unfold pdir; split_ifs <;> simp
  have h1 : rnorm (z₀ - q) ≤ R + rnorm (p - q) := by
    have := rnorm_add_le (z₀ - p) (p - q)
    rw [show (z₀ - p) + (p - q) = z₀ - q by abel, mem_P0_rnorm hdir hz] at this
    exact this
  refine ⟨?_, h1⟩
  simp only [P0, Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨j, _, rfl⟩ := hz
  unfold rnorm pdir
  split_ifs <;> simp <;> omega

lemma p_not_mem_P0 (p : ℤ × ℤ) {R : ℕ} (hR : 1 ≤ R) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    p ∉ P0 p R σ := by
  intro hp
  have h := mem_P0_rnorm hσ hp
  rw [sub_self, show rnorm 0 = 0 from rfl] at h
  omega

lemma q_not_mem_P0 (p q : ℤ × ℤ) {R : ℕ} (hR : 1 ≤ R) : q ∉ P0 p R (pdir p q) := by
  intro hq
  have h := (mem_P0_rnorm_sub_q hq).1
  rw [sub_self, show rnorm 0 = 0 from rfl] at h
  omega

lemma sum_Icc_log_factorial (R : ℕ) :
    ∑ k ∈ Finset.Icc 1 R, Real.log (k : ℝ) = Real.log (R.factorial : ℝ) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ R + 1), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos R).ne'), add_comm]

lemma sum_Icc_log_div_le {R : ℕ} (hR : 1 ≤ R) :
    ∑ k ∈ Finset.Icc 1 R, Real.log ((R : ℝ) / (k : ℝ)) ≤ (R : ℝ) := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hpow := Real.pow_div_factorial_le_exp (x := (R : ℝ)) hR0.le R
  have hfac0 : (0 : ℝ) < R.factorial := by exact_mod_cast Nat.factorial_pos R
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_div (by positivity) hfac0.ne', Real.log_pow, Real.log_exp] at hlog
  have hsum : ∑ k ∈ Finset.Icc 1 R, Real.log ((R : ℝ) / (k : ℝ)) =
      (R : ℝ) * Real.log (R : ℝ) - Real.log (R.factorial : ℝ) := by
    have hcongr : ∑ k ∈ Finset.Icc 1 R, Real.log ((R : ℝ) / (k : ℝ)) =
        ∑ k ∈ Finset.Icc 1 R, (Real.log (R : ℝ) - Real.log (k : ℝ)) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_Icc] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
      exact Real.log_div hR0.ne' hk0.ne'
    rw [hcongr, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
      show R + 1 - 1 = R by omega, nsmul_eq_mul, sum_Icc_log_factorial]
  linarith

lemma green_rot_le_zero {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 2 ≤ M)
    (u : ℤ × ℤ) :
    green X (1 - 1 / (M : ℝ)) (rot u) ≤ Real.log (M : ℝ) / Real.pi + 2 := by
  by_cases hu : u = 0
  · subst hu; rw [rot_zero]; exact green_zero_le hX hM
  · have hu1 : 1 ≤ rnorm u := Nat.pos_of_ne_zero fun h0 ↦ hu ((rnorm_eq_zero_iff u).mp h0)
    have hle := green_rot_le hX hM u hu1
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hu_ge : (1 : ℝ) ≤ (rnorm u : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ rnorm u := by exact_mod_cast hu1
      nlinarith
    have hlog_le : Real.log ((M : ℝ) / (rnorm u : ℝ) ^ 2) / Real.pi ≤ Real.log (M : ℝ) / Real.pi := by
      refine div_le_div_of_nonneg_right (Real.log_le_log (by positivity) ?_) Real.pi_pos.le
      exact div_le_self hM0.le hu_ge
    have hlogM_nn : 0 ≤ Real.log (M : ℝ) / Real.pi :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))) Real.pi_pos.le
    exact hle.trans (by linarith [max_le hlogM_nn hlog_le])

lemma sum_green_P0_le_near {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 2 ≤ M)
    (p : ℤ × ℤ) {R : ℕ} (hR : 1 ≤ R) {σ : ℤ} (w₀ : ℤ × ℤ) :
    ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / (M : ℝ)) (rot (w₀ - z₀)) ≤
      (Real.log (M : ℝ) / Real.pi + 2) +
        (R : ℝ) * (max 0 (Real.log ((M : ℝ) / (R : ℝ) ^ 2) / Real.pi) + 2 + 4 / Real.pi) := by
  rw [P0, Finset.sum_image (fun a _ b _ hab ↦ P0_injOn p R σ hab)]
  set s : ℝ := 1 - 1 / (M : ℝ)
  set m₀ : ℤ := w₀.2 - p.2
  have hpi := Real.pi_pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  set B : ℝ := max 0 (Real.log ((M : ℝ) / (R : ℝ) ^ 2) / Real.pi) + 2
  have hterm : ∀ j ∈ Finset.range R,
      green X s (rot (w₀ - (p.1 + σ * (R : ℤ), p.2 + (j : ℤ)))) ≤
        (if (j : ℤ) = m₀ then Real.log (M : ℝ) / Real.pi + 2 else 0) +
          B +
          (if (j : ℤ) ≠ m₀ ∧ (m₀ - (j : ℤ)).natAbs ≤ R then
            (2 / Real.pi) * Real.log ((R : ℝ) / ((m₀ - (j : ℤ)).natAbs : ℝ)) else 0) := by
    intro j _
    by_cases hj : (j : ℤ) = m₀
    · rw [if_pos hj, if_neg (by simp [hj]), add_zero]
      have hg := green_rot_le_zero hX hM (w₀ - (p.1 + σ * (R : ℤ), p.2 + (j : ℤ)))
      have hB0 : 0 ≤ B := by dsimp [B]; positivity
      linarith
    · rw [if_neg hj, zero_add]
      set u : ℤ × ℤ := w₀ - (p.1 + σ * (R : ℤ), p.2 + (j : ℤ))
      set k : ℕ := (m₀ - (j : ℤ)).natAbs
      have hk1 : 1 ≤ k := Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hj))
      have hk_le_r : k ≤ rnorm u := by
        dsimp [k, u, rnorm, m₀]
        have : w₀.2 - (p.2 + (j : ℤ)) = (w₀.2 - p.2) - (j : ℤ) := by ring
        rw [this]
        exact le_max_right _ _
      have hr1 : 1 ≤ rnorm u := le_trans hk1 hk_le_r
      have hg := green_rot_le hX hM u hr1
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hkr : (k : ℝ) ≤ rnorm u := by exact_mod_cast hk_le_r
      have hlog_k : Real.log ((M : ℝ) / (rnorm u : ℝ) ^ 2) / Real.pi ≤
          Real.log ((M : ℝ) / (k : ℝ) ^ 2) / Real.pi := by
        refine div_le_div_of_nonneg_right (Real.log_le_log (by positivity) ?_) hpi.le
        exact div_le_div_of_nonneg_left hM0.le (by positivity) (by gcongr)
      have hlog_split : Real.log ((M : ℝ) / (k : ℝ) ^ 2) / Real.pi =
          Real.log ((M : ℝ) / (R : ℝ) ^ 2) / Real.pi +
            (2 / Real.pi) * Real.log ((R : ℝ) / (k : ℝ)) := by
        have h1 : (M : ℝ) / (k : ℝ) ^ 2 = ((M : ℝ) / (R : ℝ) ^ 2) * ((R : ℝ) / (k : ℝ)) ^ 2 := by
          field_simp [hR0.ne', hk0.ne']
        rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
        push_cast; ring
      by_cases hkR : k ≤ R
      · rw [if_pos ⟨hj, hkR⟩]
        have hRk : 1 ≤ (R : ℝ) / (k : ℝ) := (one_le_div hk0).mpr (by exact_mod_cast hkR)
        have hlogRk : 0 ≤ (2 / Real.pi) * Real.log ((R : ℝ) / (k : ℝ)) :=
          mul_nonneg (by positivity) (Real.log_nonneg hRk)
        have hmax : max 0 (Real.log ((M : ℝ) / (rnorm u : ℝ) ^ 2) / Real.pi) ≤
            max 0 (Real.log ((M : ℝ) / (R : ℝ) ^ 2) / Real.pi) +
              (2 / Real.pi) * Real.log ((R : ℝ) / (k : ℝ)) := by
          refine max_le (by linarith [le_max_left (0 : ℝ) (Real.log ((M : ℝ) / (R : ℝ) ^ 2) / Real.pi)]) ?_
          linarith [le_max_right (0 : ℝ) (Real.log ((M : ℝ) / (R : ℝ) ^ 2) / Real.pi)]
        dsimp [B]; linarith
      · rw [if_neg (by tauto), add_zero]
        have hkR' : (R : ℝ) < k := by exact_mod_cast (by omega : R < k)
        have hmax : max 0 (Real.log ((M : ℝ) / (rnorm u : ℝ) ^ 2) / Real.pi) ≤
            max 0 (Real.log ((M : ℝ) / (R : ℝ) ^ 2) / Real.pi) := by
          refine max_le (le_max_left _ _) ?_
          refine le_trans hlog_k (le_trans (div_le_div_of_nonneg_right (Real.log_le_log (by positivity) ?_) hpi.le) (le_max_right _ _))
          exact div_le_div_of_nonneg_left hM0.le (by positivity) (by gcongr)
        dsimp [B]; linarith
  have hsum_le := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum_le
  have h1_le : (∑ j ∈ Finset.range R, if (j : ℤ) = m₀ then Real.log (M : ℝ) / Real.pi + 2 else 0) ≤
      Real.log (M : ℝ) / Real.pi + 2 := by
    rw [← Finset.sum_filter]
    have hcard1 : ((Finset.range R).filter (fun j : ℕ ↦ (j : ℤ) = m₀)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
      rw [Finset.mem_filter] at ha hb
      omega
    rw [Finset.sum_const, nsmul_eq_mul]
    have hnn : 0 ≤ Real.log (M : ℝ) / Real.pi + 2 := by
      have : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
      positivity
    calc (((Finset.range R).filter (fun j : ℕ ↦ (j : ℤ) = m₀)).card : ℝ) *
          (Real.log (M : ℝ) / Real.pi + 2)
        ≤ 1 * (Real.log (M : ℝ) / Real.pi + 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard1) hnn
      _ = Real.log (M : ℝ) / Real.pi + 2 := one_mul _
  have h3_le : (∑ j ∈ Finset.range R,
      if (j : ℤ) ≠ m₀ ∧ (m₀ - (j : ℤ)).natAbs ≤ R then
        (2 / Real.pi) * Real.log ((R : ℝ) / ((m₀ - (j : ℤ)).natAbs : ℝ)) else 0) ≤
      (4 / Real.pi) * (R : ℝ) := by
    classical
    rw [← Finset.sum_filter]
    set S : Finset ℕ := (Finset.range R).filter (fun j : ℕ ↦ (j : ℤ) ≠ m₀ ∧ (m₀ - (j : ℤ)).natAbs ≤ R)
    set S₁ : Finset ℕ := S.filter (fun j : ℕ ↦ (j : ℤ) < m₀)
    set S₂ : Finset ℕ := S.filter (fun j : ℕ ↦ m₀ < (j : ℤ))
    have hS_sub : S ⊆ S₁ ∪ S₂ := by
      intro j hj
      have hjne := (Finset.mem_filter.mp hj).2.1
      rw [Finset.mem_union]
      rcases lt_trichotomy (j : ℤ) m₀ with h | h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨hj, h⟩)
      · exact absurd h hjne
      · exact Or.inr (Finset.mem_filter.mpr ⟨hj, h⟩)
    have hS_disj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      have ha := (Finset.mem_filter.mp h1).2
      have hb := (Finset.mem_filter.mp h2).2
      omega
    have hnn_term : ∀ j ∈ S₁ ∪ S₂,
        0 ≤ (2 / Real.pi) * Real.log ((R : ℝ) / ((m₀ - (j : ℤ)).natAbs : ℝ)) := by
      intro j hj
      have hjS : j ∈ S := by
        rw [Finset.mem_union] at hj
        rcases hj with h | h <;> exact (Finset.mem_filter.mp h).1
      have hj2 := (Finset.mem_filter.mp hjS).2
      have hk1 : 1 ≤ (m₀ - (j : ℤ)).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hj2.1))
      have hk0 : (0 : ℝ) < ((m₀ - (j : ℤ)).natAbs : ℝ) := by exact_mod_cast hk1
      exact mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hk0).mpr (by exact_mod_cast hj2.2)))
    have hS_le : ∑ j ∈ S, (2 / Real.pi) * Real.log ((R : ℝ) / ((m₀ - (j : ℤ)).natAbs : ℝ)) ≤
        (∑ j ∈ S₁, (2 / Real.pi) * Real.log ((R : ℝ) / ((m₀ - (j : ℤ)).natAbs : ℝ))) +
        (∑ j ∈ S₂, (2 / Real.pi) * Real.log ((R : ℝ) / ((m₀ - (j : ℤ)).natAbs : ℝ))) := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg hS_sub (fun j hj _ ↦ hnn_term j hj)).trans ?_
      rw [Finset.sum_union hS_disj]
    have h_side : ∀ (T : Finset ℕ), (∀ j ∈ T, (j : ℤ) ≠ m₀ ∧ (m₀ - (j : ℤ)).natAbs ≤ R) →
        Set.InjOn (fun j : ℕ ↦ (m₀ - (j : ℤ)).natAbs) T →
        (∑ j ∈ T, (2 / Real.pi) * Real.log ((R : ℝ) / ((m₀ - (j : ℤ)).natAbs : ℝ))) ≤
          (2 / Real.pi) * (R : ℝ) := by
      intro T hT hInj
      have himg : (∑ j ∈ T, (2 / Real.pi) * Real.log ((R : ℝ) / ((m₀ - (j : ℤ)).natAbs : ℝ))) =
          ∑ k ∈ T.image (fun j : ℕ ↦ (m₀ - (j : ℤ)).natAbs),
            (2 / Real.pi) * Real.log ((R : ℝ) / (k : ℝ)) := by
        rw [Finset.sum_image hInj]
      rw [himg]
      have hsub_Icc : T.image (fun j : ℕ ↦ (m₀ - (j : ℤ)).natAbs) ⊆ Finset.Icc 1 R := by
        intro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨j, hjT, rfl⟩ := hk
        have hj := hT j hjT
        exact Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hj.1)), hj.2⟩
      have hsum_Icc : ∑ k ∈ T.image (fun j : ℕ ↦ (m₀ - (j : ℤ)).natAbs),
            (2 / Real.pi) * Real.log ((R : ℝ) / (k : ℝ)) ≤
          ∑ k ∈ Finset.Icc 1 R, (2 / Real.pi) * Real.log ((R : ℝ) / (k : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub_Icc fun k hk _ ↦ ?_
        rw [Finset.mem_Icc] at hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
        exact mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hk0).mpr (by exact_mod_cast hk.2)))
      refine hsum_Icc.trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_Icc_log_div_le hR) (by positivity)
    have hS1_le := h_side S₁ (fun j hj ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2)
      (fun a ha b hb hab ↦ by
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        dsimp at hab
        have h1 : ((m₀ - (a : ℤ)).natAbs : ℤ) = ((m₀ - (b : ℤ)).natAbs : ℤ) := by
          exact_mod_cast hab
        rw [Int.natAbs_of_nonneg (by omega), Int.natAbs_of_nonneg (by omega)] at h1
        omega)
    have hS2_le := h_side S₂ (fun j hj ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2)
      (fun a ha b hb hab ↦ by
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        dsimp at hab
        rw [← Int.natAbs_neg (m₀ - (a : ℤ)), ← Int.natAbs_neg (m₀ - (b : ℤ))] at hab
        have h1 : (((a : ℤ) - m₀).natAbs : ℤ) = (((b : ℤ) - m₀).natAbs : ℤ) := by
          have : -(m₀ - (a : ℤ)) = (a : ℤ) - m₀ := by ring
          have : -(m₀ - (b : ℤ)) = (b : ℤ) - m₀ := by ring
          exact_mod_cast (by simpa [show -(m₀ - (a : ℤ)) = (a : ℤ) - m₀ by ring,
            show -(m₀ - (b : ℤ)) = (b : ℤ) - m₀ by ring] using hab)
        rw [Int.natAbs_of_nonneg (by omega), Int.natAbs_of_nonneg (by omega)] at h1
        omega)
    have hsum24 : (2 / Real.pi) * (R : ℝ) + (2 / Real.pi) * (R : ℝ) = (4 / Real.pi) * (R : ℝ) := by ring
    linarith only [hS_le, hS1_le, hS2_le, hsum24]
  have hB_eq : (R : ℝ) * B + (4 / Real.pi) * (R : ℝ) =
      (R : ℝ) * (max 0 (Real.log ((M : ℝ) / (R : ℝ) ^ 2) / Real.pi) + 2 + 4 / Real.pi) := by
    dsimp [B]; ring
  linarith

lemma sum_green_P0_le_far {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 2 ≤ M)
    (p : ℤ × ℤ) {R : ℕ} (hR : 1 ≤ R) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {w₀ : ℤ × ℤ} (hfar : 2 * R < rnorm (w₀ - p)) :
    ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / (M : ℝ)) (rot (w₀ - z₀)) ≤
      (R : ℝ) * (max 0 (Real.log ((M : ℝ) / (rnorm (w₀ - p) : ℝ) ^ 2) / Real.pi) + 3) := by
  set D : ℕ := rnorm (w₀ - p)
  have hD1 : 1 ≤ D := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hpi := Real.pi_pos
  have hterm : ∀ z₀ ∈ P0 p R σ,
      green X (1 - 1 / (M : ℝ)) (rot (w₀ - z₀)) ≤
        max 0 (Real.log ((M : ℝ) / (D : ℝ) ^ 2) / Real.pi) + 3 := by
    intro z₀ hz₀
    have hzp := mem_P0_rnorm hσ hz₀
    have htri := rnorm_add_le (w₀ - z₀) (z₀ - p)
    rw [show (w₀ - z₀) + (z₀ - p) = w₀ - p by abel, hzp] at htri
    have hle_D2 : D ≤ 2 * rnorm (w₀ - z₀) := by omega
    have hr1 : 1 ≤ rnorm (w₀ - z₀) := by omega
    have hg := green_rot_le hX hM (w₀ - z₀) hr1
    have hD_le : (D : ℝ) ≤ 2 * (rnorm (w₀ - z₀) : ℝ) := by exact_mod_cast hle_D2
    have hlog_le : Real.log ((M : ℝ) / (rnorm (w₀ - z₀) : ℝ) ^ 2) / Real.pi ≤
        Real.log ((M : ℝ) / (D : ℝ) ^ 2) / Real.pi + 1 := by
      have hdiv : (M : ℝ) / (rnorm (w₀ - z₀) : ℝ) ^ 2 ≤ 4 * ((M : ℝ) / (D : ℝ) ^ 2) := by
        rw [div_le_iff₀ (by positivity)]
        have hr0 : (0 : ℝ) < rnorm (w₀ - z₀) := by exact_mod_cast hr1
        calc (M : ℝ) = (M : ℝ) / (D : ℝ) ^ 2 * (D : ℝ) ^ 2 := by
              have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
              field_simp [hD0.ne']
          _ ≤ (M : ℝ) / (D : ℝ) ^ 2 * (2 * (rnorm (w₀ - z₀) : ℝ)) ^ 2 := by gcongr
          _ = 4 * ((M : ℝ) / (D : ℝ) ^ 2) * (rnorm (w₀ - z₀) : ℝ) ^ 2 := by ring
      have h1 := Real.log_le_log (by positivity) hdiv
      rw [Real.log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h1
      have h2pi : 2 * Real.log 2 / Real.pi ≤ 1 := by
        rw [div_le_one hpi]; linarith [Real.log_two_lt_d9, Real.pi_gt_three]
      have h1d := div_le_div_of_nonneg_right h1 hpi.le
      rw [add_div] at h1d
      push_cast at h1d
      linarith
    have hmax : max 0 (Real.log ((M : ℝ) / (rnorm (w₀ - z₀) : ℝ) ^ 2) / Real.pi) ≤
        max 0 (Real.log ((M : ℝ) / (D : ℝ) ^ 2) / Real.pi) + 1 :=
      max_le (by linarith [le_max_left (0 : ℝ) (Real.log ((M : ℝ) / (D : ℝ) ^ 2) / Real.pi)])
        (by linarith [le_max_right (0 : ℝ) (Real.log ((M : ℝ) / (D : ℝ) ^ 2) / Real.pi)])
    linarith
  calc ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / (M : ℝ)) (rot (w₀ - z₀))
      ≤ ∑ _ ∈ P0 p R σ, (max 0 (Real.log ((M : ℝ) / (D : ℝ) ^ 2) / Real.pi) + 3) :=
        Finset.sum_le_sum hterm
    _ = (R : ℝ) * (max 0 (Real.log ((M : ℝ) / (D : ℝ) ^ 2) / Real.pi) + 3) := by
        rw [Finset.sum_const, P0_card, nsmul_eq_mul]

lemma rot_even_iff (w : ℤ × ℤ) : (∃ w₀ : ℤ × ℤ, rot w₀ = w) ↔ (w.1 + w.2) % 2 = 0 := by
  constructor
  · rintro ⟨w₀, rfl⟩
    dsimp [rot]; omega
  · intro h
    refine ⟨((w.1 + w.2) / 2, (w.1 - w.2) / 2), ?_⟩
    ext <;> dsimp [rot] <;> omega

lemma trialPsi_nonneg_of_rot {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {F₀ : Finset (ℤ × ℤ)} {coeff : ℤ × ℤ → ℝ}
    (hrot : ∀ w₀ : ℤ × ℤ, 0 ≤ trialPsi X s (F₀.image rot) coeff (rot w₀))
    (w : ℤ × ℤ) : 0 ≤ trialPsi X s (F₀.image rot) coeff w := by
  by_cases hev : (w.1 + w.2) % 2 = 0
  · obtain ⟨w₀, hw₀⟩ := (rot_even_iff w).mpr hev
    rw [← hw₀]; exact hrot w₀
  · have hnot : w ∉ F₀.image rot := by
      intro hw
      rw [Finset.mem_image] at hw
      obtain ⟨z₀, _, hz₀⟩ := hw
      exact hev ((rot_even_iff w).mp ⟨z₀, hz₀⟩)
    have hstep := trialPsi_step hX hs0 hs1 (F₀.image rot) coeff w
    rw [if_neg hnot, sub_zero] at hstep
    rw [← hstep]
    refine add_nonneg zero_le_one (mul_nonneg (mul_nonneg hs0 (by positivity))
      (Finset.sum_nonneg fun e he ↦ ?_))
    have hev_e : ((w + e).1 + (w + e).2) % 2 = 0 := by
      have hF : stepsF = insert (1, 0) (insert (-1, 0) (insert (0, 1) {(0, -1)})) := rfl
      rw [hF] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> dsimp <;> omega
    obtain ⟨w₀, hw₀⟩ := (rot_even_iff (w + e)).mpr hev_e
    rw [← hw₀]; exact hrot w₀

lemma one_sub_inv_pow_ge (M : ℕ) (hM : 1 ≤ M) :
    (Real.exp 1)⁻¹ ≤ (1 - 1 / ((M : ℝ) + 1)) ^ M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : 1 - 1 / ((M : ℝ) + 1) = (M : ℝ) / ((M : ℝ) + 1) := by field_simp; ring
  rw [h1]
  have hinv : ((M : ℝ) + 1) / (M : ℝ) ≤ Real.exp (1 / (M : ℝ)) := by
    have : ((M : ℝ) + 1) / (M : ℝ) = 1 / (M : ℝ) + 1 := by field_simp; ring
    rw [this]; exact Real.add_one_le_exp _
  have hpow : (((M : ℝ) + 1) / (M : ℝ)) ^ M ≤ Real.exp 1 := by
    calc (((M : ℝ) + 1) / (M : ℝ)) ^ M ≤ (Real.exp (1 / (M : ℝ))) ^ M :=
          pow_le_pow_left₀ (by positivity) hinv M
      _ = Real.exp ((M : ℝ) * (1 / (M : ℝ))) := by rw [← Real.exp_nat_mul]
      _ = Real.exp 1 := by congr 1; field_simp [hM0.ne']
  have hpos : (0 : ℝ) < ((M : ℝ) / ((M : ℝ) + 1)) ^ M := by positivity
  rw [show (((M : ℝ) / ((M : ℝ) + 1)) ^ M) = ((((M : ℝ) + 1) / (M : ℝ)) ^ M)⁻¹ by
    rw [← inv_pow, inv_div]]
  exact inv_anti₀ (by positivity) hpow

lemma det_locShift (M : ℕ) (z : ℤ × ℤ) (y y' : ℕ → ℤ × ℤ) (h : ∀ i < M, y i = y' i) :
    locShift 0 y M z = locShift 0 y' M z := by
  simp only [locShift, zero_add]
  congr 1
  refine Finset.filter_congr fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [pos_congr h (by omega)]

/-- Part A Chernoff bound: upper bound on `P(v1 <= L(rot p) /\ v3 <= sum_{z in Prot} L(z))`. -/
lemma prob_locShift_bad_P0_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 25 ≤ M)
    (p : ℤ × ℤ) {R : ℕ} (hR : 1 ≤ R) (hR2 : R ^ 2 ≤ M + 1) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {c₁ c₃ : ℝ} (hc₁ : 0 < c₁) (hc₃ : 0 ≤ c₃) {v₁ v₃ : ℝ} (_hv₁ : 0 ≤ v₁) (_hv₃ : 0 ≤ v₃) :
    let M₁ : ℝ := (M : ℝ) + 1
    let L : ℝ := Real.log M₁ / Real.pi
    let γ : ℝ := Real.log (M₁ / (R : ℝ) ^ 2) / Real.log M₁
    let ψ_x : ℝ := 1 + c₁ + c₃ * γ + (2 * c₁ + 2 * c₃) / L
    let ψ_z : ℝ := 1 + (c₁ + c₃) * γ + (2 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L
    (ℙ {ω | v₁ ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        v₃ ≤ ∑ z ∈ Prot p R σ, (locShift 0 (path X ω) M z : ℝ)}).toReal ≤
      Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) *
        Real.exp (-(v₁ * (c₁ / (L * ψ_x)) + v₃ * (c₃ / ((R : ℝ) * L * ψ_z)))) := by
  intro M₁ L γ ψ_x ψ_z
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hpi := Real.pi_pos
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (this.trans hM1_ge)
  have hL_ge : 3 / 4 ≤ L := by
    dsimp [L]; rw [le_div_iff₀ hpi]; linarith [Real.pi_lt_four]
  have hL0 : 0 < L := by linarith
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hM1_cast : ((M + 1 : ℕ) : ℝ) = M₁ := by dsimp [M₁]; push_cast; ring
  have hγ_nn : 0 ≤ γ := by
    dsimp [γ]
    refine div_nonneg (Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)) (by linarith)
    rw [← hM1_cast]; exact_mod_cast hR2
  have hγ_le1 : γ ≤ 1 := by
    dsimp [γ]
    rw [div_le_one (by linarith)]
    exact Real.log_le_log (by positivity) (div_le_self (by linarith) (by exact_mod_cast (by nlinarith : 1 ≤ R ^ 2)))
  have hψx_pos : 0 < ψ_x := by dsimp [ψ_x]; positivity
  have hψx_ge : c₁ < L * ψ_x := by
    have h1 : c₁ + 2 * c₁ / L ≤ ψ_x := by
      dsimp [ψ_x]
      rw [add_div]
      have : 0 ≤ c₃ * γ := mul_nonneg hc₃ hγ_nn
      have : 0 ≤ 2 * c₃ / L := by positivity
      linarith
    have h2 : L * (c₁ + 2 * c₁ / L) = L * c₁ + 2 * c₁ := by field_simp [hL0.ne']
    have h3 : L * (c₁ + 2 * c₁ / L) ≤ L * ψ_x := mul_le_mul_of_nonneg_left h1 hL0.le
    nlinarith only [hc₁, hL_ge, h2, h3]
  have hψz_pos : 0 < ψ_z := by dsimp [ψ_z]; positivity
  have hψz_ge : c₃ < (R : ℝ) * L * ψ_z := by
    have h1 : 1 + 6 * c₃ / L ≤ ψ_z := by
      dsimp [ψ_z]
      simp only [add_div]
      have : 0 ≤ (c₁ + c₃) * γ := mul_nonneg (by linarith) hγ_nn
      have : 0 ≤ 2 * c₁ / L := by positivity
      have : 0 ≤ c₃ * (L + 2) / (R : ℝ) / L := by positivity
      linarith
    have h2 : (R : ℝ) * L * (1 + 6 * c₃ / L) = (R : ℝ) * L + 6 * (R : ℝ) * c₃ := by
      field_simp [hL0.ne']
    have h3 : (R : ℝ) * L * (1 + 6 * c₃ / L) ≤ (R : ℝ) * L * ψ_z :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hR0.le hL0.le)
    have hRc : c₃ ≤ (R : ℝ) * c₃ := le_mul_of_one_le_left hc₃ (by exact_mod_cast hR)
    nlinarith only [hc₃, hR0, hL_ge, h2, h3, hRc]
  set τ_x : ℝ := c₁ / (L * ψ_x)
  set τ_z : ℝ := c₃ / ((R : ℝ) * L * ψ_z)
  have hτx0 : 0 < τ_x := div_pos hc₁ (by linarith)
  have hτx1 : τ_x < 1 := (div_lt_one (by linarith)).mpr hψx_ge
  have hτz0 : 0 ≤ τ_z := div_nonneg hc₃ (by positivity)
  have hτz1 : τ_z < 1 := (div_lt_one (by positivity)).mpr hψz_ge
  let F : Finset (ℤ × ℤ) := insert (rot p) (Prot p R σ)
  let coeff : ℤ × ℤ → ℝ := fun z ↦
    if z = rot p then M₁ * c₁ / L
    else if z ∈ Prot p R σ then M₁ * c₃ / ((R : ℝ) * L) else 0
  let u : ℤ × ℤ → ℝ := fun z ↦
    if z = rot p then (1 - τ_x)⁻¹
    else if z ∈ Prot p R σ then (1 - τ_z)⁻¹ else 1
  have hu_pos : ∀ z, 0 < u z := fun z ↦ by
    dsimp [u]
    split_ifs <;> [exact inv_pos.mpr (by linarith); exact inv_pos.mpr (by linarith); exact zero_lt_one]
  have hu_out : ∀ z, z ∉ F → u z = 1 := fun z hz ↦ by
    dsimp [u, F] at hz ⊢
    rw [Finset.mem_insert, not_or] at hz
    rw [if_neg hz.1, if_neg hz.2]
  have hcoeff_nn : ∀ z, 0 ≤ coeff z := fun z ↦ by
    dsimp [coeff]; split_ifs <;> positivity
  set s : ℝ := 1 - 1 / M₁
  have hs0 : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr (by linarith : 0 < M₁)]
  have h1s : 1 / (1 - s) = M₁ := by dsimp [s]; field_simp; ring
  have hpsi_nn : ∀ w, 0 ≤ trialPsi X s F coeff w := fun w ↦ by
    unfold trialPsi
    refine add_nonneg (by rw [h1s]; positivity) (Finset.sum_nonneg fun z _ ↦ ?_)
    exact mul_nonneg (hcoeff_nn z) (green_nonneg X hs0 _)
  have hp_not_mem : rot p ∉ Prot p R σ := by
    intro hmem
    rw [Prot, Finset.mem_image] at hmem
    obtain ⟨p', hp', heq⟩ := hmem
    exact p_not_mem_P0 p hR hσ (rot_injective heq ▸ hp')
  have hProt_ne : ∀ z ∈ Prot p R σ, z ≠ rot p := fun z hz heq ↦ hp_not_mem (heq ▸ hz)
  have hs_eq : s = 1 - 1 / ((M + 1 : ℕ) : ℝ) := by dsimp [s]; rw [hM1_cast]
  have hL_cast : Real.log ((M + 1 : ℕ) : ℝ) / Real.pi = L := by dsimp [L]; rw [hM1_cast]
  have heq_γL : Real.log (M₁ / (R : ℝ) ^ 2) / Real.pi = γ * L := by
    dsimp [γ, L]; field_simp
  have heq_γL_cast : Real.log (((M + 1 : ℕ) : ℝ) / (R : ℝ) ^ 2) / Real.pi = γ * L := by
    rw [hM1_cast, heq_γL]
  have hpsi_in : ∀ z ∈ F, (1 - (u z)⁻¹) * trialPsi X s F coeff z ≤ coeff z := by
    intro z hz
    have hsum_F : ∑ w ∈ F, coeff w * green X s (z - w) =
        (M₁ * c₁ / L) * green X s (z - rot p) +
          (M₁ * c₃ / ((R : ℝ) * L)) * ∑ w ∈ Prot p R σ, green X s (z - w) := by
      dsimp [F]
      rw [Finset.sum_insert hp_not_mem]
      congr 1
      · dsimp [coeff]; rw [if_pos rfl]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w hw ↦ ?_
        dsimp [coeff]; rw [if_neg (hProt_ne w hw), if_pos hw]
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hzP
    · have h1u : 1 - (u (rot p))⁻¹ = τ_x := by
        dsimp [u]; rw [if_pos rfl, inv_inv]; ring
      have hg0 : green X s (rot p - rot p) ≤ L + 2 := by
        rw [sub_self, hs_eq]
        simpa [hL_cast] using green_zero_le hX (by omega : 2 ≤ M + 1)
      have hgP : ∑ w ∈ Prot p R σ, green X s (rot p - w) ≤ (R : ℝ) * (γ * L + 2) := by
        rw [Prot, Finset.sum_image (fun a _ b _ hab ↦ rot_injective hab)]
        calc ∑ z₀ ∈ P0 p R σ, green X s (rot p - rot z₀)
            ≤ ∑ _ ∈ P0 p R σ, (γ * L + 2) := by
              refine Finset.sum_le_sum fun z₀ hz₀ ↦ ?_
              rw [← rot_sub, hs_eq]
              have hr1 : 1 ≤ rnorm (p - z₀) := by
                rw [show p - z₀ = -(z₀ - p) by abel, rnorm_neg, mem_P0_rnorm hσ hz₀]; exact hR
              have hgle := green_rot_le hX (by omega : 2 ≤ M + 1) (p - z₀) hr1
              have hr_eq : rnorm (p - z₀) = R := by
                rw [show p - z₀ = -(z₀ - p) by abel, rnorm_neg, mem_P0_rnorm hσ hz₀]
              rwa [hr_eq, heq_γL_cast, max_eq_right (mul_nonneg hγ_nn hL0.le)] at hgle
          _ = (R : ℝ) * (γ * L + 2) := by rw [Finset.sum_const, P0_card, nsmul_eq_mul]
      have hpsi_le : trialPsi X s F coeff (rot p) ≤ M₁ * ψ_x := by
        unfold trialPsi
        rw [h1s, hsum_F]
        have hc1' : 0 ≤ M₁ * c₁ / L := by positivity
        have hc3' : 0 ≤ M₁ * c₃ / ((R : ℝ) * L) := by positivity
        calc M₁ + ((M₁ * c₁ / L) * green X s (rot p - rot p) +
              (M₁ * c₃ / ((R : ℝ) * L)) * ∑ w ∈ Prot p R σ, green X s (rot p - w))
            ≤ M₁ + ((M₁ * c₁ / L) * (L + 2) +
                (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (γ * L + 2))) := by gcongr
          _ = M₁ * ψ_x := by dsimp [ψ_x]; field_simp [hL0.ne', hR0.ne']; ring
      rw [h1u]
      calc τ_x * trialPsi X s F coeff (rot p) ≤ τ_x * (M₁ * ψ_x) :=
            mul_le_mul_of_nonneg_left hpsi_le hτx0.le
        _ = (M₁ * c₁ / L) * (ψ_x / ψ_x) := by dsimp [τ_x]; ring
        _ = M₁ * c₁ / L := by rw [div_self hψx_pos.ne', mul_one]
        _ = coeff (rot p) := by dsimp [coeff]; rw [if_pos rfl]
    · have hzne := hProt_ne z hzP
      have h1u : 1 - (u z)⁻¹ = τ_z := by
        dsimp [u]; rw [if_neg hzne, if_pos hzP, inv_inv]; ring
      have hzP_mem := hzP
      rw [Prot, Finset.mem_image] at hzP
      obtain ⟨z₀, hz₀, rfl⟩ := hzP
      have hgzp : green X s (rot z₀ - rot p) ≤ γ * L + 2 := by
        rw [← rot_sub, hs_eq]
        have hr1 : 1 ≤ rnorm (z₀ - p) := by
          rw [mem_P0_rnorm hσ hz₀]; exact hR
        have hgle := green_rot_le hX (by omega : 2 ≤ M + 1) (z₀ - p) hr1
        rwa [mem_P0_rnorm hσ hz₀, heq_γL_cast, max_eq_right (mul_nonneg hγ_nn hL0.le)] at hgle
      have hgzP : ∑ w ∈ Prot p R σ, green X s (rot z₀ - w) ≤
          (L + 2) + (R : ℝ) * (γ * L + 4) := by
        rw [Prot, Finset.sum_image (fun a _ b _ hab ↦ rot_injective hab)]
        have hnear := sum_green_P0_le_near hX (by omega : 2 ≤ M + 1) p hR (σ := σ) z₀
        have hsum_eq : ∑ w₀ ∈ P0 p R σ, green X s (rot z₀ - rot w₀) =
            ∑ w₀ ∈ P0 p R σ, green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (z₀ - w₀)) :=
          Finset.sum_congr rfl fun w₀ _ ↦ by rw [← rot_sub, hs_eq]
        rw [hsum_eq]
        rw [hL_cast, heq_γL_cast, max_eq_right (mul_nonneg hγ_nn hL0.le)] at hnear
        have h4pi : γ * L + 2 + 4 / Real.pi ≤ γ * L + 4 := by
          have : 4 / Real.pi ≤ 2 := by rw [div_le_iff₀ hpi]; linarith only [Real.pi_gt_three]
          linarith only [this]
        exact hnear.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h4pi hR0.le))
      have hpsi_le : trialPsi X s F coeff (rot z₀) ≤ M₁ * ψ_z := by
        unfold trialPsi
        rw [h1s, hsum_F]
        have hc1' : 0 ≤ M₁ * c₁ / L := by positivity
        have hc3' : 0 ≤ M₁ * c₃ / ((R : ℝ) * L) := by positivity
        calc M₁ + ((M₁ * c₁ / L) * green X s (rot z₀ - rot p) +
              (M₁ * c₃ / ((R : ℝ) * L)) * ∑ w ∈ Prot p R σ, green X s (rot z₀ - w))
            ≤ M₁ + ((M₁ * c₁ / L) * (γ * L + 2) +
                (M₁ * c₃ / ((R : ℝ) * L)) * ((L + 2) + (R : ℝ) * (γ * L + 4))) := by gcongr
          _ = M₁ * (1 + (c₁ + c₃) * γ + (2 * c₁ + 4 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L) := by
              field_simp [hL0.ne', hR0.ne']; ring
          _ ≤ M₁ * ψ_z := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              dsimp [ψ_z]
              gcongr
              linarith
      rw [h1u]
      calc τ_z * trialPsi X s F coeff (rot z₀) ≤ τ_z * (M₁ * ψ_z) :=
            mul_le_mul_of_nonneg_left hpsi_le hτz0
        _ = (M₁ * c₃ / ((R : ℝ) * L)) * (ψ_z / ψ_z) := by dsimp [τ_z]; ring
        _ = M₁ * c₃ / ((R : ℝ) * L) := by rw [div_self hψz_pos.ne', mul_one]
        _ = coeff (rot z₀) := by dsimp [coeff]; rw [if_neg hzne, if_pos hzP_mem]
  let A_bad : Set (ℕ → ℤ × ℤ) :=
    {y | v₁ ≤ (locShift 0 y M (rot p) : ℝ) ∧ v₃ ≤ ∑ z ∈ Prot p R σ, (locShift 0 y M z : ℝ)}
  let B : ℝ := Real.exp (v₁ * τ_x + v₃ * τ_z)
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hBA_k : ∀ k : ℕ, ∀ y : ℕ → ℤ × ℤ,
      v₁ ≤ (locShift 0 y k (rot p) : ℝ) →
      v₃ ≤ (∑ z ∈ Prot p R σ, (locShift 0 y k z : ℝ)) →
      B ≤ prodWalk u 0 y k := by
    intro k y hy1 hy3
    rw [prodWalk_eq_finset_pow hu_out]
    dsimp [F]
    rw [Finset.prod_insert hp_not_mem]
    have hexp_x : Real.exp (v₁ * τ_x) ≤ (u (rot p)) ^ locShift 0 y k (rot p) := by
      have h1 : Real.exp τ_x ≤ u (rot p) := by
        dsimp [u]; rw [if_pos rfl]
        have h1m : 0 < 1 - τ_x := by linarith
        exact (by rw [← inv_inv (Real.exp τ_x), ← Real.exp_neg]; exact inv_anti₀ h1m (Real.one_sub_le_exp_neg τ_x))
      calc Real.exp (v₁ * τ_x) ≤ Real.exp ((locShift 0 y k (rot p) : ℝ) * τ_x) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hy1 hτx0.le)
        _ = (Real.exp τ_x) ^ locShift 0 y k (rot p) := by rw [Real.exp_nat_mul]
        _ ≤ (u (rot p)) ^ locShift 0 y k (rot p) :=
            pow_le_pow_left₀ (Real.exp_pos _).le h1 _
    have hexp_P : Real.exp (v₃ * τ_z) ≤ ∏ z ∈ Prot p R σ, (u z) ^ locShift 0 y k z := by
      have h_each : ∀ z ∈ Prot p R σ,
          Real.exp ((locShift 0 y k z : ℝ) * τ_z) ≤ (u z) ^ locShift 0 y k z := by
        intro z hz
        have h1 : Real.exp τ_z ≤ u z := by
          dsimp [u]; rw [if_neg (hProt_ne z hz), if_pos hz]
          have h1m : 0 < 1 - τ_z := by linarith
          exact (by rw [← inv_inv (Real.exp τ_z), ← Real.exp_neg]; exact inv_anti₀ h1m (Real.one_sub_le_exp_neg τ_z))
        rw [Real.exp_nat_mul]
        exact pow_le_pow_left₀ (Real.exp_pos _).le h1 _
      calc Real.exp (v₃ * τ_z)
          ≤ Real.exp ((∑ z ∈ Prot p R σ, (locShift 0 y k z : ℝ)) * τ_z) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hy3 hτz0)
        _ = Real.exp (∑ z ∈ Prot p R σ, (locShift 0 y k z : ℝ) * τ_z) := by
            rw [Finset.sum_mul]
        _ = ∏ z ∈ Prot p R σ, Real.exp ((locShift 0 y k z : ℝ) * τ_z) := by
            rw [Real.exp_sum]
        _ ≤ ∏ z ∈ Prot p R σ, (u z) ^ locShift 0 y k z :=
            Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le) h_each
    calc B = Real.exp (v₁ * τ_x) * Real.exp (v₃ * τ_z) := Real.exp_add _ _
      _ ≤ (u (rot p)) ^ locShift 0 y k (rot p) * ∏ z ∈ Prot p R σ, (u z) ^ locShift 0 y k z :=
          mul_le_mul hexp_x hexp_P (Real.exp_pos _).le (pow_nonneg (hu_pos _).le _)
  let A_seq : ℕ → Set (ℕ → ℤ × ℤ) := fun k ↦
    if M ≤ k then
      {y | v₁ ≤ (locShift 0 y k (rot p) : ℝ) ∧ v₃ ≤ ∑ z ∈ Prot p R σ, (locShift 0 y k z : ℝ)}
    else ∅
  have hA_det : ∀ k, Det k (A_seq k) := fun k ↦ by
    dsimp [A_seq]
    split_ifs with hk
    · intro y y' h hy
      refine ⟨?_, ?_⟩
      · rw [← det_locShift k (rot p) y y' h]; exact hy.1
      · refine le_trans hy.2 (le_of_eq (Finset.sum_congr rfl fun z _ ↦ ?_))
        rw [det_locShift k z y y' h]
    · exact fun _ _ _ hmem ↦ False.elim hmem
  have hA_B : ∀ k, ∀ y ∈ A_seq k, B ≤ prodWalk u 0 y k := fun k y hy ↦ by
    dsimp [A_seq] at hy
    split_ifs at hy with hk
    · exact hBA_k k y hy.1 hy.2
    · exact False.elim hy
  have hfk := feynman_kac_chernoff hX hs0 hs1 hu_pos hu_out hpsi_nn hpsi_in hA_det hB0 hA_B (2 * M)
  have hsub_icc : Finset.Icc M (2 * M) ⊆ Finset.range (2 * M + 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact Finset.mem_range.mpr (by omega)
  have hsub_A : ∀ k ∈ Finset.Icc M (2 * M),
      (ℙ {ω | path X ω ∈ A_bad}).toReal ≤ (ℙ {ω | path X ω ∈ A_seq k}).toReal := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hset_sub : {ω : Ω | path X ω ∈ A_bad} ⊆ {ω : Ω | path X ω ∈ A_seq k} := by
      intro ω hω
      dsimp only [A_seq, A_bad, Set.mem_ofPred_eq] at hω ⊢
      rw [if_pos hk.1]
      refine ⟨hω.1.trans (by exact_mod_cast locShift_zero_mono hk.1 (rot p)), ?_⟩
      refine hω.2.trans (Finset.sum_le_sum fun z _ ↦ ?_)
      exact_mod_cast locShift_zero_mono hk.1 z
    exact ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hset_sub)
  have hs2M : (Real.exp 1)⁻¹ ^ 2 ≤ s ^ (2 * M) := by
    rw [mul_comm 2 M, pow_mul, hs_eq]
    have h1 : (Real.exp 1)⁻¹ ≤ (1 - 1 / ((M + 1 : ℕ) : ℝ)) ^ M := by
      simpa [Nat.cast_add, Nat.cast_one] using one_sub_inv_pow_ge M (by omega)
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hs_k : ∀ k ∈ Finset.Icc M (2 * M), Real.exp (-2) ≤ s ^ k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    calc Real.exp (-2) = (Real.exp 1)⁻¹ ^ 2 := by
          rw [inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]; norm_num
      _ ≤ s ^ (2 * M) := hs2M
      _ ≤ s ^ k := pow_le_pow_of_le_one hs0 hs1.le hk.2
  have hsum_lower : B * (M₁ * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_bad}).toReal) ≤
      B * ∑ k ∈ Finset.range (2 * M + 1), s ^ k * (ℙ {ω | path X ω ∈ A_seq k}).toReal := by
    refine mul_le_mul_of_nonneg_left ?_ hB0
    calc M₁ * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_bad}).toReal
        = ∑ _ ∈ Finset.Icc M (2 * M), Real.exp (-2) * (ℙ {ω | path X ω ∈ A_bad}).toReal := by
          rw [Finset.sum_const, Nat.card_Icc, show 2 * M + 1 - M = M + 1 by omega, nsmul_eq_mul,
            hM1_cast]; ring
      _ ≤ ∑ k ∈ Finset.Icc M (2 * M), s ^ k * (ℙ {ω | path X ω ∈ A_seq k}).toReal := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          exact mul_le_mul (hs_k k hk) (hsub_A k hk) ENNReal.toReal_nonneg (pow_nonneg hs0 k)
      _ ≤ ∑ k ∈ Finset.range (2 * M + 1), s ^ k * (ℙ {ω | path X ω ∈ A_seq k}).toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_icc fun k _ _ ↦
            mul_nonneg (pow_nonneg hs0 k) ENNReal.toReal_nonneg
  have hrhs : 1 / (1 - s) + ∑ z ∈ F, coeff z * green X s z ≤ M₁ * (1 + 4 * c₁ + 4 * c₃) := by
    have hL4 : L + 2 ≤ 4 * L := by linarith
    have hgz : ∀ z ∈ F, green X s z ≤ L + 2 := by
      intro z hz
      dsimp [F] at hz
      rw [Finset.mem_insert] at hz
      have hrot : ∃ u₀ : ℤ × ℤ, rot u₀ = z := by
        rcases hz with rfl | hzP
        · exact ⟨p, rfl⟩
        · rw [Prot, Finset.mem_image] at hzP; obtain ⟨z₀, _, rfl⟩ := hzP; exact ⟨z₀, rfl⟩
      obtain ⟨u₀, rfl⟩ := hrot
      rw [hs_eq]
      simpa [hM1_cast, L] using green_rot_le_zero hX (by omega : 2 ≤ M + 1) u₀
    have hsum_bd : ∑ z ∈ F, coeff z * green X s z ≤
        (M₁ * c₁ / L) * (4 * L) + (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (4 * L)) := by
      dsimp [F]
      rw [Finset.sum_insert hp_not_mem]
      refine add_le_add ?_ ?_
      · dsimp [coeff]; rw [if_pos rfl]
        exact mul_le_mul_of_nonneg_left ((hgz _ (Finset.mem_insert_self _ _)).trans hL4) (by positivity)
      · calc ∑ z ∈ Prot p R σ, coeff z * green X s z
            ≤ ∑ z ∈ Prot p R σ, (M₁ * c₃ / ((R : ℝ) * L)) * (4 * L) := by
              refine Finset.sum_le_sum fun z hz ↦ ?_
              dsimp [coeff]; rw [if_neg (hProt_ne z hz), if_pos hz]
              exact mul_le_mul_of_nonneg_left
                ((hgz z (Finset.mem_insert_of_mem hz)).trans hL4) (by positivity)
          _ = (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (4 * L)) := by
              rw [Finset.sum_const, Prot_card, nsmul_eq_mul]; ring
    rw [h1s]
    calc M₁ + ∑ z ∈ F, coeff z * green X s z
        ≤ M₁ + ((M₁ * c₁ / L) * (4 * L) + (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (4 * L))) := by
          linarith
      _ = M₁ * (1 + 4 * c₁ + 4 * c₃) := by field_simp [hL0.ne', hR0.ne']; ring
  have hcomb : M₁ * (B * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_bad}).toReal) ≤
      M₁ * (1 + 4 * c₁ + 4 * c₃) := by
    calc M₁ * (B * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_bad}).toReal)
        = B * (M₁ * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_bad}).toReal) := by ring
      _ ≤ M₁ * (1 + 4 * c₁ + 4 * c₃) := hsum_lower.trans (hfk.trans hrhs)
  have hcomb' := le_of_mul_le_mul_left hcomb (by linarith : 0 < M₁)
  have hB_pos : 0 < B * Real.exp (-2) := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hfinal : (ℙ {ω | path X ω ∈ A_bad}).toReal ≤
      Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) * B⁻¹ := by
    have hmul : (ℙ {ω | path X ω ∈ A_bad}).toReal * (B * Real.exp (-2)) ≤ 1 + 4 * c₁ + 4 * c₃ := by
      linarith only [hcomb']
    calc (ℙ {ω | path X ω ∈ A_bad}).toReal
        ≤ (1 + 4 * c₁ + 4 * c₃) / (B * Real.exp (-2)) := (le_div_iff₀ hB_pos).mpr hmul
      _ = Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) * B⁻¹ := by
          rw [div_eq_mul_inv, mul_inv, Real.exp_neg, inv_inv]; ring
  rw [show B⁻¹ = Real.exp (-(v₁ * τ_x + v₃ * τ_z)) from (Real.exp_neg _).symm] at hfinal
  exact hfinal

/-- Part B 2-point Chernoff bound: upper bound on `P(v1 <= L(rot p) /\ v1 <= L(rot q))`. -/
lemma prob_locShift_two_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 25 ≤ M)
    {p q : ℤ × ℤ} (hpq : p ≠ q) {c₁ : ℝ} (hc₁ : 0 < c₁) {v₁ : ℝ} (_hv₁ : 0 ≤ v₁) :
    let M₁ : ℝ := (M : ℝ) + 1
    let L : ℝ := Real.log M₁ / Real.pi
    let γd : ℝ := max 0 (Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.log M₁)
    let ψ₂ : ℝ := 1 + c₁ * (1 + γd) + 4 * c₁ / L
    (ℙ {ω | v₁ ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        v₁ ≤ (locShift 0 (path X ω) M (rot q) : ℝ)}).toReal ≤
      Real.exp 2 * (1 + 8 * c₁) * Real.exp (-(2 * v₁ * (c₁ / (L * ψ₂)))) := by
  intro M₁ L γd ψ₂
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hpi := Real.pi_pos
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (this.trans hM1_ge)
  have hL_ge : 3 / 4 ≤ L := by
    dsimp [L]; rw [le_div_iff₀ hpi]; linarith [Real.pi_lt_four]
  have hL0 : 0 < L := by linarith
  have hγd_nn : 0 ≤ γd := le_max_left _ _
  have hψ2_pos : 0 < ψ₂ := by dsimp [ψ₂]; positivity
  have hψ2_ge : c₁ < L * ψ₂ := by
    have h1 : c₁ + 4 * c₁ / L ≤ ψ₂ := by
      dsimp [ψ₂]
      have : 0 ≤ c₁ * γd := mul_nonneg hc₁.le hγd_nn
      linarith
    have h2 : L * (c₁ + 4 * c₁ / L) = L * c₁ + 4 * c₁ := by field_simp [hL0.ne']
    have h3 : L * (c₁ + 4 * c₁ / L) ≤ L * ψ₂ := mul_le_mul_of_nonneg_left h1 hL0.le
    nlinarith only [hc₁, hL_ge, h2, h3]
  set τ : ℝ := c₁ / (L * ψ₂)
  have hτ0 : 0 < τ := div_pos hc₁ (by linarith)
  have hτ1 : τ < 1 := (div_lt_one (by linarith)).mpr hψ2_ge
  have hne_rot : rot p ≠ rot q := fun h ↦ hpq (rot_injective h)
  let F : Finset (ℤ × ℤ) := {rot p, rot q}
  let coeff : ℤ × ℤ → ℝ := fun z ↦ if z = rot p ∨ z = rot q then M₁ * c₁ / L else 0
  let u : ℤ × ℤ → ℝ := fun z ↦ if z = rot p ∨ z = rot q then (1 - τ)⁻¹ else 1
  have hu_pos : ∀ z, 0 < u z := fun z ↦ by
    dsimp [u]; split_ifs <;> [exact inv_pos.mpr (by linarith); exact zero_lt_one]
  have hu_out : ∀ z, z ∉ F → u z = 1 := fun z hz ↦ by
    dsimp [u, F] at hz ⊢
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [if_neg hz]
  set s : ℝ := 1 - 1 / M₁
  have hs0 : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr (by linarith : 0 < M₁)]
  have h1s : 1 / (1 - s) = M₁ := by dsimp [s]; field_simp; ring
  have hM1_cast : (M + 1 : ℕ) = M₁ := by dsimp [M₁]; push_cast; ring
  have hs_eq : s = 1 - 1 / ((M + 1 : ℕ) : ℝ) := by dsimp [s]; rw [hM1_cast]
  have hpsi_nn : ∀ w, 0 ≤ trialPsi X s F coeff w := fun w ↦ by
    unfold trialPsi
    refine add_nonneg (by rw [h1s]; positivity) (Finset.sum_nonneg fun z _ ↦ ?_)
    have hc_nn : 0 ≤ coeff z := by dsimp [coeff]; split_ifs <;> positivity
    exact mul_nonneg hc_nn (green_nonneg X hs0 _)
  have hd1 : 1 ≤ rnorm (p - q) :=
    Nat.pos_of_ne_zero fun h0 ↦ hpq (sub_eq_zero.mp ((rnorm_eq_zero_iff (p - q)).mp h0))
  have hγd_L : max 0 (Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.pi) = γd * L := by
    have h1 : Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.pi =
        (Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.log M₁) * L := by
      dsimp [L]; field_simp
    rw [h1]
    dsimp [γd]
    rw [max_mul_of_nonneg _ _ hL0.le, zero_mul]
  have hL_cast : Real.log ((M + 1 : ℕ) : ℝ) / Real.pi = L := by dsimp [L]; rw [hM1_cast]
  have hγd_L_cast : max 0 (Real.log (((M + 1 : ℕ) : ℝ) / (rnorm (p - q) : ℝ) ^ 2) / Real.pi) = γd * L := by
    rw [hM1_cast, hγd_L]
  have hpsi_in : ∀ z ∈ F, (1 - (u z)⁻¹) * trialPsi X s F coeff z ≤ coeff z := by
    intro z hz
    have hsum_F : ∑ w ∈ F, coeff w * green X s (z - w) =
        (M₁ * c₁ / L) * (green X s (z - rot p) + green X s (z - rot q)) := by
      dsimp [F]
      rw [Finset.sum_pair hne_rot]
      dsimp [coeff]
      rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
      ring
    have hz_or : z = rot p ∨ z = rot q := by simpa [F] using hz
    have h1u : 1 - (u z)⁻¹ = τ := by dsimp [u]; rw [if_pos hz_or, inv_inv]; ring
    have hg_sum : green X s (z - rot p) + green X s (z - rot q) ≤ (L + 2) + (γd * L + 2) := by
      rcases hz_or with rfl | rfl
      · rw [sub_self, hs_eq, ← rot_sub]
        have hg0 := green_zero_le hX (by omega : 2 ≤ M + 1)
        have hgd := green_rot_le hX (by omega : 2 ≤ M + 1) (p - q) hd1
        rw [hL_cast] at hg0
        rw [hγd_L_cast] at hgd
        linarith only [hg0, hgd]
      · rw [sub_self, hs_eq, ← rot_sub]
        have hg0 := green_zero_le hX (by omega : 2 ≤ M + 1)
        have hd1' : 1 ≤ rnorm (q - p) := by rw [show q - p = -(p - q) by abel, rnorm_neg]; exact hd1
        have hgd := green_rot_le hX (by omega : 2 ≤ M + 1) (q - p) hd1'
        have hr_eq : rnorm (q - p) = rnorm (p - q) := by rw [show q - p = -(p - q) by abel, rnorm_neg]
        rw [hr_eq, hγd_L_cast] at hgd
        rw [hL_cast] at hg0
        linarith only [hg0, hgd]
    have hpsi_le : trialPsi X s F coeff z ≤ M₁ * ψ₂ := by
      unfold trialPsi
      rw [h1s, hsum_F]
      have hc1' : 0 ≤ M₁ * c₁ / L := by positivity
      calc M₁ + (M₁ * c₁ / L) * (green X s (z - rot p) + green X s (z - rot q))
          ≤ M₁ + (M₁ * c₁ / L) * ((L + 2) + (γd * L + 2)) := by gcongr
        _ = M₁ * ψ₂ := by dsimp [ψ₂]; field_simp [hL0.ne']; ring
    rw [h1u]
    calc τ * trialPsi X s F coeff z ≤ τ * (M₁ * ψ₂) := mul_le_mul_of_nonneg_left hpsi_le hτ0.le
      _ = (M₁ * c₁ / L) * (ψ₂ / ψ₂) := by dsimp [τ]; ring
      _ = M₁ * c₁ / L := by rw [div_self hψ2_pos.ne', mul_one]
      _ = coeff z := by dsimp [coeff]; rw [if_pos hz_or]
  let A_two : Set (ℕ → ℤ × ℤ) :=
    {y | v₁ ≤ (locShift 0 y M (rot p) : ℝ) ∧ v₁ ≤ (locShift 0 y M (rot q) : ℝ)}
  let B : ℝ := Real.exp (2 * v₁ * τ)
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hBA_k : ∀ k : ℕ, ∀ y : ℕ → ℤ × ℤ,
      v₁ ≤ (locShift 0 y k (rot p) : ℝ) → v₁ ≤ (locShift 0 y k (rot q) : ℝ) →
      B ≤ prodWalk u 0 y k := by
    intro k y hy1 hy2
    rw [prodWalk_eq_finset_pow hu_out]
    dsimp [F]
    rw [Finset.prod_pair hne_rot]
    have hexp_1 : ∀ z, z = rot p ∨ z = rot q →
        ∀ l : ℕ, v₁ ≤ (l : ℝ) → Real.exp (v₁ * τ) ≤ (u z) ^ l := by
      intro z hz l hl
      have h1 : Real.exp τ ≤ u z := by
        dsimp [u]; rw [if_pos hz]
        have h1m : 0 < 1 - τ := by linarith
        rw [← inv_inv (Real.exp τ), ← Real.exp_neg]
        exact inv_anti₀ h1m (Real.one_sub_le_exp_neg τ)
      calc Real.exp (v₁ * τ) ≤ Real.exp ((l : ℝ) * τ) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hl hτ0.le)
        _ = (Real.exp τ) ^ l := by rw [Real.exp_nat_mul]
        _ ≤ (u z) ^ l := pow_le_pow_left₀ (Real.exp_pos _).le h1 _
    calc B = Real.exp (v₁ * τ) * Real.exp (v₁ * τ) := by
          dsimp [B]; rw [← Real.exp_add]; congr 1; ring
      _ ≤ (u (rot p)) ^ locShift 0 y k (rot p) * (u (rot q)) ^ locShift 0 y k (rot q) :=
          mul_le_mul (hexp_1 (rot p) (Or.inl rfl) _ hy1) (hexp_1 (rot q) (Or.inr rfl) _ hy2)
            (Real.exp_pos _).le (pow_nonneg (hu_pos _).le _)
  let A_seq : ℕ → Set (ℕ → ℤ × ℤ) := fun k ↦
    if M ≤ k then {y | v₁ ≤ (locShift 0 y k (rot p) : ℝ) ∧ v₁ ≤ (locShift 0 y k (rot q) : ℝ)} else ∅
  have hA_det : ∀ k, Det k (A_seq k) := fun k ↦ by
    dsimp [A_seq]
    split_ifs with hk
    · intro y y' h hy
      refine ⟨?_, ?_⟩
      · rw [← det_locShift k (rot p) y y' h]; exact hy.1
      · rw [← det_locShift k (rot q) y y' h]; exact hy.2
    · exact fun _ _ _ hmem ↦ False.elim hmem
  have hA_B : ∀ k, ∀ y ∈ A_seq k, B ≤ prodWalk u 0 y k := fun k y hy ↦ by
    dsimp [A_seq] at hy
    split_ifs at hy with hk
    · exact hBA_k k y hy.1 hy.2
    · exact False.elim hy
  have hfk := feynman_kac_chernoff hX hs0 hs1 hu_pos hu_out hpsi_nn hpsi_in hA_det hB0 hA_B (2 * M)
  have hsub_icc : Finset.Icc M (2 * M) ⊆ Finset.range (2 * M + 1) := fun k hk ↦ by
    rw [Finset.mem_Icc] at hk; exact Finset.mem_range.mpr (by omega)
  have hsub_A : ∀ k ∈ Finset.Icc M (2 * M),
      (ℙ {ω | path X ω ∈ A_two}).toReal ≤ (ℙ {ω | path X ω ∈ A_seq k}).toReal := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hset_sub : {ω : Ω | path X ω ∈ A_two} ⊆ {ω : Ω | path X ω ∈ A_seq k} := by
      intro ω hω
      dsimp only [A_seq, A_two, Set.mem_ofPred_eq] at hω ⊢
      rw [if_pos hk.1]
      exact ⟨hω.1.trans (by exact_mod_cast locShift_zero_mono hk.1 (rot p)),
        hω.2.trans (by exact_mod_cast locShift_zero_mono hk.1 (rot q))⟩
    exact ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hset_sub)
  have hs2M : (Real.exp 1)⁻¹ ^ 2 ≤ s ^ (2 * M) := by
    rw [mul_comm 2 M, pow_mul, hs_eq]
    have h1 : (Real.exp 1)⁻¹ ≤ (1 - 1 / ((M + 1 : ℕ) : ℝ)) ^ M := by
      simpa [Nat.cast_add, Nat.cast_one] using one_sub_inv_pow_ge M (by omega)
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hs_k : ∀ k ∈ Finset.Icc M (2 * M), Real.exp (-2) ≤ s ^ k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    calc Real.exp (-2) = (Real.exp 1)⁻¹ ^ 2 := by
          rw [inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]; norm_num
      _ ≤ s ^ (2 * M) := hs2M
      _ ≤ s ^ k := pow_le_pow_of_le_one hs0 hs1.le hk.2
  have hsum_lower : B * (M₁ * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_two}).toReal) ≤
      B * ∑ k ∈ Finset.range (2 * M + 1), s ^ k * (ℙ {ω | path X ω ∈ A_seq k}).toReal := by
    refine mul_le_mul_of_nonneg_left ?_ hB0
    calc M₁ * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_two}).toReal
        = ∑ _ ∈ Finset.Icc M (2 * M), Real.exp (-2) * (ℙ {ω | path X ω ∈ A_two}).toReal := by
          rw [Finset.sum_const, Nat.card_Icc, show 2 * M + 1 - M = M + 1 by omega, nsmul_eq_mul,
            hM1_cast]; ring
      _ ≤ ∑ k ∈ Finset.Icc M (2 * M), s ^ k * (ℙ {ω | path X ω ∈ A_seq k}).toReal := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          exact mul_le_mul (hs_k k hk) (hsub_A k hk) ENNReal.toReal_nonneg (pow_nonneg hs0 k)
      _ ≤ ∑ k ∈ Finset.range (2 * M + 1), s ^ k * (ℙ {ω | path X ω ∈ A_seq k}).toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_icc fun k _ _ ↦
            mul_nonneg (pow_nonneg hs0 k) ENNReal.toReal_nonneg
  have hrhs : 1 / (1 - s) + ∑ z ∈ F, coeff z * green X s z ≤ M₁ * (1 + 8 * c₁) := by
    have hL4 : L + 2 ≤ 4 * L := by linarith
    have hgp : green X s (rot p) ≤ 4 * L := by
      rw [hs_eq]
      have h0 := green_rot_le_zero hX (by omega : 2 ≤ M + 1) p
      rw [hL_cast] at h0
      exact h0.trans hL4
    have hgq : green X s (rot q) ≤ 4 * L := by
      rw [hs_eq]
      have h0 := green_rot_le_zero hX (by omega : 2 ≤ M + 1) q
      rw [hL_cast] at h0
      exact h0.trans hL4
    dsimp [F]
    rw [h1s, Finset.sum_pair hne_rot]
    dsimp [coeff]; rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
    calc M₁ + (M₁ * c₁ / L * green X s (rot p) + M₁ * c₁ / L * green X s (rot q))
        ≤ M₁ + (M₁ * c₁ / L * (4 * L) + M₁ * c₁ / L * (4 * L)) := by gcongr
      _ = M₁ * (1 + 8 * c₁) := by field_simp [hL0.ne']; ring
  have hcomb : M₁ * (B * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_two}).toReal) ≤
      M₁ * (1 + 8 * c₁) := by
    calc M₁ * (B * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_two}).toReal)
        = B * (M₁ * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_two}).toReal) := by ring
      _ ≤ M₁ * (1 + 8 * c₁) := hsum_lower.trans (hfk.trans hrhs)
  have hcomb' := le_of_mul_le_mul_left hcomb (by linarith : 0 < M₁)
  have hB_pos : 0 < B * Real.exp (-2) := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hfinal : (ℙ {ω | path X ω ∈ A_two}).toReal ≤ Real.exp 2 * (1 + 8 * c₁) * B⁻¹ := by
    have hmul : (ℙ {ω | path X ω ∈ A_two}).toReal * (B * Real.exp (-2)) ≤ 1 + 8 * c₁ := by
      linarith only [hcomb']
    calc (ℙ {ω | path X ω ∈ A_two}).toReal
        ≤ (1 + 8 * c₁) / (B * Real.exp (-2)) := (le_div_iff₀ hB_pos).mpr hmul
      _ = Real.exp 2 * (1 + 8 * c₁) * B⁻¹ := by
          rw [div_eq_mul_inv, mul_inv, Real.exp_neg, inv_inv]; ring
  rw [show B⁻¹ = Real.exp (-(2 * v₁ * τ)) from (Real.exp_neg _).symm] at hfinal
  exact hfinal

/-- Helper lower bound for `trialPsi` in `prob_locShift_two_good_le`. -/
lemma prob_locShift_two_good_psi_rot_ge {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 25 ≤ M)
    {p q : ℤ × ℤ} (hpq : p ≠ q) {R : ℕ} (hR : 1 ≤ R)
    (hdR : rnorm (p - q) ≤ R) (h3R : (3 * R) ^ 2 ≤ M + 1)
    {c₁ ρ : ℝ} (hc₁ : 0 < c₁) (hρ0 : 0 ≤ ρ) (hρ2 : ρ < 2)
    (hL_big : 10 * c₁ + 6 * (ρ * c₁) + (ρ * c₁) * (Real.log ((M : ℝ) + 1) / Real.pi + 2) / (R : ℝ) ≤
      Real.log ((M : ℝ) + 1) / Real.pi / 2) (w₀ : ℤ × ℤ) :
    let M₁ : ℝ := (M : ℝ) + 1
    let L : ℝ := Real.log M₁ / Real.pi
    let c₃ : ℝ := ρ * c₁
    let σ : ℤ := pdir p q
    let F : Finset (ℤ × ℤ) := insert (rot p) (insert (rot q) (Prot p R σ))
    let coeff : ℤ × ℤ → ℝ := fun z ↦
      if z = rot p ∨ z = rot q then M₁ * c₁ / L
      else if z ∈ Prot p R σ then -(M₁ * c₃ / ((R : ℝ) * L)) else 0
    M₁ / 2 ≤ trialPsi X (1 - 1 / M₁) F coeff (rot w₀) := by
  intro M₁ L c₃ σ F coeff
  set s : ℝ := 1 - 1 / M₁
  set γ : ℝ := Real.log (M₁ / (R : ℝ) ^ 2) / Real.log M₁
  have hσ : σ = 1 ∨ σ = -1 := by dsimp [σ, pdir]; split_ifs <;> simp
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hpi := Real.pi_pos
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith only [hM1_ge])).mpr (this.trans hM1_ge)
  have hL_ge : 3 / 4 ≤ L := by
    dsimp [L]; rw [le_div_iff₀ hpi]; linarith only [hlogM1, Real.pi_lt_four]
  have hL0 : 0 < L := by linarith only [hL_ge]
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hc₃ : 0 ≤ c₃ := mul_nonneg hρ0 hc₁.le
  have hR2 : R ^ 2 ≤ M + 1 := le_trans (by nlinarith) h3R
  have hM1_cast : ((M + 1 : ℕ) : ℝ) = M₁ := by dsimp [M₁]; push_cast; ring
  have hγ_nn : 0 ≤ γ := by
    dsimp [γ]
    refine div_nonneg (Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)) (by linarith only [hlogM1])
    rw [← hM1_cast]; exact_mod_cast hR2
  have hγ_le1 : γ ≤ 1 := by
    dsimp [γ]; rw [div_le_one (by linarith only [hlogM1])]
    exact Real.log_le_log (by positivity)
      (div_le_self (by linarith only [hM1_ge]) (by exact_mod_cast (by nlinarith : 1 ≤ R ^ 2)))
  have h2c_ge : 0 ≤ 2 * c₁ - c₃ := by
    have : 2 * c₁ - c₃ = (2 - ρ) * c₁ := by dsimp [c₃]; ring
    rw [this]; exact mul_nonneg (by linarith only [hρ2]) hc₁.le
  have hs0 : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_one (by linarith only [hM1_ge])]; linarith only [hM1_ge]
  have hs1 : s < 1 := by dsimp [s]; linarith only [one_div_pos.mpr (by linarith only [hM1_ge] : 0 < M₁)]
  have h1s : 1 / (1 - s) = M₁ := by dsimp [s]; field_simp; ring
  have hs_eq : s = 1 - 1 / ((M + 1 : ℕ) : ℝ) := by dsimp [s]; rw [hM1_cast]
  have hγL : Real.log (M₁ / (R : ℝ) ^ 2) / Real.pi = γ * L := by dsimp [γ, L]; field_simp
  have hγL_cast : Real.log (((M + 1 : ℕ) : ℝ) / (R : ℝ) ^ 2) / Real.pi = γ * L := by
    rw [hM1_cast, hγL]
  have hL_cast : Real.log ((M + 1 : ℕ) : ℝ) / Real.pi = L := by dsimp [L]; rw [hM1_cast]
  have hlog2_pi : 2 * Real.log 2 / Real.pi ≤ 1 := by
    rw [div_le_one hpi]; linarith only [Real.log_two_lt_d9, Real.pi_gt_three]
  have hlog3_pi : 2 * Real.log 3 / Real.pi ≤ 2 := by
    have hlog3 : Real.log 3 ≤ 2 := by
      have h1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.exp_one_gt_d9
        calc (3 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
          _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) this.le 2
          _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr h1
    rw [div_le_iff₀ hpi]; linarith only [hlog3, Real.pi_gt_three]
  have hne_rot : rot p ≠ rot q := fun h ↦ hpq (rot_injective h)
  have hp_not_mem : rot p ∉ Prot p R σ := fun hmem ↦ by
    rw [Prot, Finset.mem_image] at hmem
    obtain ⟨p', hp', heq⟩ := hmem
    exact p_not_mem_P0 p hR hσ (rot_injective heq ▸ hp')
  have hq_not_mem : rot q ∉ Prot p R σ := fun hmem ↦ by
    rw [Prot, Finset.mem_image] at hmem
    obtain ⟨q', hq', heq⟩ := hmem
    rw [rot_injective heq] at hq'
    dsimp [σ] at hq'
    exact q_not_mem_P0 p q hR hq'
  have hProt_ne_p : ∀ z ∈ Prot p R σ, z ≠ rot p := fun z hz heq ↦ hp_not_mem (heq ▸ hz)
  have hProt_ne_q : ∀ z ∈ Prot p R σ, z ≠ rot q := fun z hz heq ↦ hq_not_mem (heq ▸ hz)
  have hsum_F_eq : ∑ z ∈ F, coeff z * green X s (rot w₀ - z) =
      (M₁ * c₁ / L) * (green X s (rot w₀ - rot p) + green X s (rot w₀ - rot q)) -
        (M₁ * c₃ / ((R : ℝ) * L)) * ∑ z ∈ Prot p R σ, green X s (rot w₀ - z) := by
    dsimp [F]
    rw [Finset.sum_insert (by simp [hne_rot, hp_not_mem]), Finset.sum_insert hq_not_mem]
    have hp_val : coeff (rot p) = M₁ * c₁ / L := by dsimp [coeff]; rw [if_pos (Or.inl rfl)]
    have hq_val : coeff (rot q) = M₁ * c₁ / L := by dsimp [coeff]; rw [if_pos (Or.inr rfl)]
    have hP_sum : ∑ z ∈ Prot p R σ, coeff z * green X s (rot w₀ - z) =
        -((M₁ * c₃ / ((R : ℝ) * L)) * ∑ z ∈ Prot p R σ, green X s (rot w₀ - z)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z hz ↦ ?_
      dsimp [coeff]
      rw [if_neg (not_or.mpr ⟨hProt_ne_p z hz, hProt_ne_q z hz⟩), if_pos hz]
      ring
    rw [hp_val, hq_val, hP_sum]
    ring
  unfold trialPsi
  rw [h1s, hsum_F_eq, Prot,
    Finset.sum_image (fun a _ b _ hab ↦ rot_injective hab)]
  have hsum_rot : ∑ z₀ ∈ P0 p R σ, green X s (rot w₀ - rot z₀) =
      ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (w₀ - z₀)) :=
    Finset.sum_congr rfl fun z₀ _ ↦ by rw [← rot_sub, hs_eq]
  rw [hsum_rot]
  have hg_ge_mul : ∀ (u₀ : ℤ × ℤ) (k : ℕ), 1 ≤ k → (k * R) ^ 2 ≤ M + 1 →
      rnorm u₀ ≤ k * R →
      γ * L - (3 + 2 * Real.log (k : ℝ) / Real.pi) ≤ green X s (rot u₀) := by
    intro u₀ k hk hkR huk
    by_cases hu : u₀ = 0
    · subst hu
      have hg0 := green_zero_ge hX (by omega : 2 ≤ M + 1)
      rw [rot_zero, hs_eq]
      rw [hL_cast] at hg0
      have hγL1 : γ * L ≤ L := mul_le_of_le_one_left hL0.le hγ_le1
      have hk0 : 0 ≤ 2 * Real.log (k : ℝ) / Real.pi :=
        div_nonneg (mul_nonneg zero_le_two (Real.log_nonneg (by exact_mod_cast hk))) hpi.le
      linarith only [hg0, hγL1, hk0]
    · have hu1 : 1 ≤ rnorm u₀ := Nat.pos_of_ne_zero fun h0 ↦ hu ((rnorm_eq_zero_iff u₀).mp h0)
      have hge := green_rot_ge hX (by omega : 2 ≤ M + 1) u₀ hu1
      have hge' : Real.log (M₁ / (rnorm u₀ : ℝ) ^ 2) / Real.pi - 3 ≤
          green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot u₀) := by
        rw [← hM1_cast]; exact hge
      rw [hs_eq]
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hlog_cmp : Real.log (M₁ / ((k : ℝ) * (R : ℝ)) ^ 2) ≤
          Real.log (M₁ / (rnorm u₀ : ℝ) ^ 2) := by
        refine Real.log_le_log (by positivity) ?_
        exact div_le_div_of_nonneg_left (by linarith only [hM1_ge])
          (by exact_mod_cast (by nlinarith : 0 < rnorm u₀ ^ 2))
          (by exact_mod_cast (by nlinarith : rnorm u₀ ^ 2 ≤ (k * R) ^ 2))
      have hlog_eq : Real.log (M₁ / ((k : ℝ) * (R : ℝ)) ^ 2) / Real.pi =
          γ * L - 2 * Real.log (k : ℝ) / Real.pi := by
        rw [show M₁ / ((k : ℝ) * (R : ℝ)) ^ 2 = (M₁ / (R : ℝ) ^ 2) / (k : ℝ) ^ 2 by ring,
          Real.log_div (by positivity) (by positivity), Real.log_pow, sub_div, hγL]
        push_cast; ring
      have hdiv_le := div_le_div_of_nonneg_right hlog_cmp hpi.le
      linarith only [hge', hdiv_le, hlog_eq]
  by_cases hnear : rnorm (w₀ - p) ≤ 2 * R
  · have hwp_ge : γ * L - 5 ≤ green X s (rot w₀ - rot p) := by
      rw [← rot_sub]
      have h := hg_ge_mul (w₀ - p) 2 (by omega) (le_trans (by nlinarith) h3R) hnear
      push_cast at h
      linarith only [h, hlog2_pi]
    have hwq_le : rnorm (w₀ - q) ≤ 3 * R := by
      have := rnorm_add_le (w₀ - p) (p - q)
      rw [show (w₀ - p) + (p - q) = w₀ - q by abel] at this
      omega
    have hwq_ge : γ * L - 5 ≤ green X s (rot w₀ - rot q) := by
      rw [← rot_sub]
      have h := hg_ge_mul (w₀ - q) 3 (by omega) h3R hwq_le
      push_cast at h
      linarith only [h, hlog3_pi]
    have hP_le := sum_green_P0_le_near hX (by omega : 2 ≤ M + 1) p hR (σ := σ) w₀
    rw [hL_cast, hγL_cast, max_eq_right (mul_nonneg hγ_nn hL0.le)] at hP_le
    have h4pi : γ * L + 2 + 4 / Real.pi ≤ γ * L + 4 := by
      have : 4 / Real.pi ≤ 2 := by rw [div_le_iff₀ hpi]; linarith only [Real.pi_gt_three]
      linarith only [this]
    have hP_le' : ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (w₀ - z₀)) ≤
        (L + 2) + (R : ℝ) * (γ * L + 4) :=
      hP_le.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h4pi hR0.le))
    have hc1' : 0 ≤ M₁ * c₁ / L := by positivity
    have hc3' : 0 ≤ M₁ * c₃ / ((R : ℝ) * L) := by positivity
    have hlow : M₁ + ((M₁ * c₁ / L) * (2 * γ * L - 10) -
        (M₁ * c₃ / ((R : ℝ) * L)) * ((L + 2) + (R : ℝ) * (γ * L + 4))) ≤
        M₁ + ((M₁ * c₁ / L) * (green X s (rot w₀ - rot p) + green X s (rot w₀ - rot q)) -
          (M₁ * c₃ / ((R : ℝ) * L)) *
            ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (w₀ - z₀))) :=
      add_le_add le_rfl (sub_le_sub (mul_le_mul_of_nonneg_left (by linarith only [hwp_ge, hwq_ge]) hc1')
        (mul_le_mul_of_nonneg_left hP_le' hc3'))
    refine le_trans ?_ hlow
    have h_alg : M₁ + ((M₁ * c₁ / L) * (2 * γ * L - 10) -
        (M₁ * c₃ / ((R : ℝ) * L)) * ((L + 2) + (R : ℝ) * (γ * L + 4))) =
        M₁ * (1 + (2 * c₁ - c₃) * γ - (10 * c₁ + 4 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L) := by
      field_simp [hL0.ne', hR0.ne']; ring
    rw [h_alg]
    have h2 : 1 / 2 ≤ 1 + (2 * c₁ - c₃) * γ - (10 * c₁ + 4 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L := by
      have h1 : (10 * c₁ + 4 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L ≤ 1 / 2 := by
        rw [div_le_iff₀ hL0]
        have hL_eq : L = Real.log ((M : ℝ) + 1) / Real.pi := rfl
        have hc3_eq : c₃ = ρ * c₁ := rfl
        linarith only [hL_big, hc₃, hL_eq, hc3_eq]
      have hnn : 0 ≤ (2 * c₁ - c₃) * γ := mul_nonneg h2c_ge hγ_nn
      linarith only [h1, hnn]
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h2 (by linarith only [hM1_ge] : 0 ≤ M₁)
  · push Not at hnear
    set D : ℕ := rnorm (w₀ - p)
    have hD1 : 1 ≤ D := by omega
    have hP_le := sum_green_P0_le_far hX (by omega : 2 ≤ M + 1) p hR hσ hnear
    set γD : ℝ := max 0 (Real.log (M₁ / (D : ℝ) ^ 2) / Real.pi)
    have hγD_nn : 0 ≤ γD := le_max_left _ _
    by_cases hD2 : D ^ 2 ≤ M + 1
    · have hlogD_nn : 0 ≤ Real.log (M₁ / (D : ℝ) ^ 2) / Real.pi := by
        refine div_nonneg (Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)) hpi.le
        rw [← hM1_cast]; exact_mod_cast hD2
      have hγD_eq : γD = Real.log (M₁ / (D : ℝ) ^ 2) / Real.pi := max_eq_right hlogD_nn
      have hwp_ge : γD - 3 ≤ green X s (rot w₀ - rot p) := by
        rw [← rot_sub, hs_eq, hγD_eq, ← hM1_cast]
        exact green_rot_ge hX (by omega : 2 ≤ M + 1) (w₀ - p) hD1
      have hwq_le : 2 * rnorm (w₀ - q) ≤ 3 * D := by
        have := rnorm_add_le (w₀ - p) (p - q)
        rw [show (w₀ - p) + (p - q) = w₀ - q by abel] at this
        omega
      have hwq1 : 1 ≤ rnorm (w₀ - q) := by
        have := rnorm_add_le (w₀ - q) (q - p)
        rw [show (w₀ - q) + (q - p) = w₀ - p by abel, show q - p = -(p - q) by abel,
          rnorm_neg] at this
        omega
      have hwq_ge : γD - 5 ≤ green X s (rot w₀ - rot q) := by
        rw [← rot_sub, hs_eq, hγD_eq]
        have h := green_rot_ge hX (by omega : 2 ≤ M + 1) (w₀ - q) hwq1
        have h' : Real.log (M₁ / (rnorm (w₀ - q) : ℝ) ^ 2) / Real.pi - 3 ≤
            green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (w₀ - q)) := by
          rw [← hM1_cast]; exact h
        have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
        have hrq0 : (0 : ℝ) < rnorm (w₀ - q) := by exact_mod_cast hwq1
        have hcmp : (rnorm (w₀ - q) : ℝ) ^ 2 ≤ ((3 : ℝ) / 2 * (D : ℝ)) ^ 2 := by
          have : 2 * (rnorm (w₀ - q) : ℝ) ≤ 3 * (D : ℝ) := by exact_mod_cast hwq_le
          nlinarith only [this]
        have hlog_cmp : Real.log (M₁ / ((3 : ℝ) / 2 * (D : ℝ)) ^ 2) ≤
            Real.log (M₁ / (rnorm (w₀ - q) : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by linarith only [hM1_ge]) (by positivity) hcmp)
        have hlog_eq : Real.log (M₁ / ((3 : ℝ) / 2 * (D : ℝ)) ^ 2) / Real.pi =
            Real.log (M₁ / (D : ℝ) ^ 2) / Real.pi - 2 * Real.log (3 / 2) / Real.pi := by
          rw [show M₁ / ((3 : ℝ) / 2 * (D : ℝ)) ^ 2 = (M₁ / (D : ℝ) ^ 2) / (3 / 2 : ℝ) ^ 2 by ring,
            Real.log_div (by positivity) (by norm_num), Real.log_pow, sub_div]
          push_cast; ring
        have hlog32 : 2 * Real.log (3 / 2) / Real.pi ≤ 2 := by
          have : Real.log (3 / 2) ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
          have : 2 * Real.log (3 / 2) / Real.pi ≤ 2 * Real.log 3 / Real.pi :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this zero_le_two) hpi.le
          linarith only [this, hlog3_pi]
        have hd := div_le_div_of_nonneg_right hlog_cmp hpi.le
        linarith only [h', hd, hlog_eq, hlog32]
      have hc1' : 0 ≤ M₁ * c₁ / L := by positivity
      have hc3' : 0 ≤ M₁ * c₃ / ((R : ℝ) * L) := by positivity
      have hP_le' : ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (w₀ - z₀)) ≤
          (R : ℝ) * (γD + 3) := by
        simpa [hM1_cast, γD] using hP_le
      have hlow : M₁ + ((M₁ * c₁ / L) * (2 * γD - 8) -
          (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (γD + 3))) ≤
          M₁ + ((M₁ * c₁ / L) * (green X s (rot w₀ - rot p) + green X s (rot w₀ - rot q)) -
            (M₁ * c₃ / ((R : ℝ) * L)) *
              ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (w₀ - z₀))) :=
        add_le_add le_rfl (sub_le_sub (mul_le_mul_of_nonneg_left (by linarith only [hwp_ge, hwq_ge]) hc1')
          (mul_le_mul_of_nonneg_left hP_le' hc3'))
      refine le_trans ?_ hlow
      have h_alg : M₁ + ((M₁ * c₁ / L) * (2 * γD - 8) -
          (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (γD + 3))) =
          M₁ * (1 + (2 * c₁ - c₃) * (γD / L) - (8 * c₁ + 3 * c₃) / L) := by
        field_simp [hL0.ne', hR0.ne']; ring
      rw [h_alg]
      have h2 : 1 / 2 ≤ 1 + (2 * c₁ - c₃) * (γD / L) - (8 * c₁ + 3 * c₃) / L := by
        have h1 : (8 * c₁ + 3 * c₃) / L ≤ 1 / 2 := by
          rw [div_le_iff₀ hL0]
          have hL_eq : L = Real.log ((M : ℝ) + 1) / Real.pi := rfl
          have hc3_eq : c₃ = ρ * c₁ := rfl
          have hnnR : 0 ≤ c₃ * (Real.log ((M : ℝ) + 1) / Real.pi + 2) / (R : ℝ) := by positivity
          linarith only [hL_big, hc₁, hc₃, hL_eq, hc3_eq, hnnR]
        have hnn : 0 ≤ (2 * c₁ - c₃) * (γD / L) := mul_nonneg h2c_ge (div_nonneg hγD_nn hL0.le)
        linarith only [h1, hnn]
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h2 (by linarith only [hM1_ge] : 0 ≤ M₁)
    · push Not at hD2
      have hlog_neg : Real.log (M₁ / (D : ℝ) ^ 2) / Real.pi ≤ 0 := by
        refine div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (by positivity) ?_) hpi.le
        rw [div_le_one (by exact_mod_cast (by nlinarith : 0 < D ^ 2))]
        rw [← hM1_cast]; exact_mod_cast hD2.le
      have hγD0 : γD = 0 := max_eq_left hlog_neg
      have hP_le' : ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (w₀ - z₀)) ≤
          (R : ℝ) * 3 := by
        have h1 := hP_le
        have h0 : max 0 (Real.log (((M + 1 : ℕ) : ℝ) / (D : ℝ) ^ 2) / Real.pi) = 0 := by
          rw [hM1_cast]; exact hγD0
        rw [h0, zero_add] at h1
        exact h1
      have hgp0 : 0 ≤ green X s (rot w₀ - rot p) := green_nonneg X hs0 _
      have hgq0 : 0 ≤ green X s (rot w₀ - rot q) := green_nonneg X hs0 _
      have hc1' : 0 ≤ M₁ * c₁ / L := by positivity
      have hc3' : 0 ≤ M₁ * c₃ / ((R : ℝ) * L) := by positivity
      have hlow : M₁ - (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * 3) ≤
          M₁ + ((M₁ * c₁ / L) * (green X s (rot w₀ - rot p) + green X s (rot w₀ - rot q)) -
            (M₁ * c₃ / ((R : ℝ) * L)) *
              ∑ z₀ ∈ P0 p R σ, green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (w₀ - z₀))) := by
        have : 0 ≤ (M₁ * c₁ / L) * (green X s (rot w₀ - rot p) + green X s (rot w₀ - rot q)) :=
          mul_nonneg hc1' (add_nonneg hgp0 hgq0)
        linarith only [this, mul_le_mul_of_nonneg_left hP_le' hc3']
      refine le_trans ?_ hlow
      have h_alg : M₁ - (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * 3) = M₁ * (1 - 3 * c₃ / L) := by
        field_simp [hL0.ne', hR0.ne']
      rw [h_alg]
      have h1 : 3 * c₃ / L ≤ 1 / 2 := by
        rw [div_le_iff₀ hL0]
        have hL_eq : L = Real.log ((M : ℝ) + 1) / Real.pi := rfl
        have hc3_eq : c₃ = ρ * c₁ := rfl
        have hnnR : 0 ≤ c₃ * (Real.log ((M : ℝ) + 1) / Real.pi + 2) / (R : ℝ) := by positivity
        linarith only [hL_big, hc₁, hc₃, hL_eq, hc3_eq, hnnR]
      have h2 : 1 / 2 ≤ 1 - 3 * c₃ / L := by linarith only [h1]
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h2 (by linarith only [hM1_ge] : 0 ≤ M₁)

/-- Helper `Prot` super-solution bound for `prob_locShift_two_good_le`. -/
lemma prob_locShift_two_good_psi_in_Prot {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 25 ≤ M)
    {p q : ℤ × ℤ} (hpq : p ≠ q) {R : ℕ} (hR : 1 ≤ R)
    (hdR : rnorm (p - q) ≤ R) (h3R : (3 * R) ^ 2 ≤ M + 1)
    {c₁ ρ : ℝ} (hc₁ : 0 < c₁) (hρ0 : 0 ≤ ρ) (hρ2 : ρ < 2)
    (hL_big : 10 * c₁ + 6 * (ρ * c₁) + (ρ * c₁) * (Real.log ((M : ℝ) + 1) / Real.pi + 2) / (R : ℝ) ≤
      Real.log ((M : ℝ) + 1) / Real.pi / 2)
    (τ : ℝ) :
    let M₁ : ℝ := (M : ℝ) + 1
    let L : ℝ := Real.log M₁ / Real.pi
    let c₃ : ℝ := ρ * c₁
    let σ : ℤ := pdir p q
    let γ : ℝ := Real.log (M₁ / (R : ℝ) ^ 2) / Real.log M₁
    let ψ_low : ℝ := 1 + (2 * c₁ - c₃) * γ - (8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L
    let w_p : ℝ := c₃ / ((R : ℝ) * L * ψ_low)
    let F : Finset (ℤ × ℤ) := insert (rot p) (insert (rot q) (Prot p R σ))
    let coeff : ℤ × ℤ → ℝ := fun z ↦
      if z = rot p ∨ z = rot q then M₁ * c₁ / L
      else if z ∈ Prot p R σ then -(M₁ * c₃ / ((R : ℝ) * L)) else 0
    let u : ℤ × ℤ → ℝ := fun z ↦
      if z = rot p ∨ z = rot q then (1 - τ)⁻¹
      else if z ∈ Prot p R σ then Real.exp (-w_p) else 1
    (∀ w, 0 ≤ trialPsi X (1 - 1 / M₁) F coeff w) →
    ∀ z ∈ Prot p R σ, (1 - (u z)⁻¹) * trialPsi X (1 - 1 / M₁) F coeff z ≤ coeff z := by
  intro M₁ L c₃ σ γ ψ_low w_p F coeff u hpsi_nn z hzP
  set s : ℝ := 1 - 1 / M₁
  have hσ : σ = 1 ∨ σ = -1 := by dsimp [σ, pdir]; split_ifs <;> simp
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hpi := Real.pi_pos
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith only [hM1_ge])).mpr (this.trans hM1_ge)
  have hL_ge : 3 / 4 ≤ L := by
    dsimp [L]; rw [le_div_iff₀ hpi]; linarith only [hlogM1, Real.pi_lt_four]
  have hL0 : 0 < L := by linarith only [hL_ge]
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hc₃ : 0 ≤ c₃ := mul_nonneg hρ0 hc₁.le
  have hR2 : R ^ 2 ≤ M + 1 := le_trans (by nlinarith) h3R
  have hM1_cast : ((M + 1 : ℕ) : ℝ) = M₁ := by dsimp [M₁]; push_cast; ring
  have hγ_nn : 0 ≤ γ := by
    dsimp [γ]
    refine div_nonneg (Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)) (by linarith only [hlogM1])
    rw [← hM1_cast]; exact_mod_cast hR2
  have h2c_ge : 0 ≤ 2 * c₁ - c₃ := by
    have : 2 * c₁ - c₃ = (2 - ρ) * c₁ := by dsimp [c₃]; ring
    rw [this]; exact mul_nonneg (by linarith only [hρ2]) hc₁.le
  have hψlow_ge : 1 / 2 ≤ ψ_low := by
    dsimp [ψ_low]
    have h1 : (8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L ≤ 1 / 2 := by
      rw [div_le_iff₀ hL0]
      have hL_eq : L = Real.log ((M : ℝ) + 1) / Real.pi := rfl
      have hc3_eq : c₃ = ρ * c₁ := rfl
      linarith only [hL_big, hc₁.le, hL_eq, hc3_eq]
    have h2 : 0 ≤ (2 * c₁ - c₃) * γ := mul_nonneg h2c_ge hγ_nn
    linarith only [h1, h2]
  have hψlow_pos : 0 < ψ_low := by linarith only [hψlow_ge]
  have hwp0 : 0 ≤ w_p := div_nonneg hc₃ (by positivity)
  have hne_rot : rot p ≠ rot q := fun h ↦ hpq (rot_injective h)
  have hp_not_mem : rot p ∉ Prot p R σ := fun hmem ↦ by
    rw [Prot, Finset.mem_image] at hmem; obtain ⟨p', hp', heq⟩ := hmem
    exact p_not_mem_P0 p hR hσ (rot_injective heq ▸ hp')
  have hq_not_mem : rot q ∉ Prot p R σ := fun hmem ↦ by
    rw [Prot, Finset.mem_image] at hmem; obtain ⟨q', hq', heq⟩ := hmem
    rw [rot_injective heq] at hq'; dsimp [σ] at hq'
    exact q_not_mem_P0 p q hR hq'
  have hProt_ne_p : ∀ w ∈ Prot p R σ, w ≠ rot p := fun w hw heq ↦ hp_not_mem (heq ▸ hw)
  have hProt_ne_q : ∀ w ∈ Prot p R σ, w ≠ rot q := fun w hw heq ↦ hq_not_mem (heq ▸ hw)
  have h1s : 1 / (1 - s) = M₁ := by dsimp [s]; field_simp; ring
  have hs_eq : s = 1 - 1 / ((M + 1 : ℕ) : ℝ) := by dsimp [s]; rw [hM1_cast]
  have hγL : Real.log (M₁ / (R : ℝ) ^ 2) / Real.pi = γ * L := by dsimp [γ, L]; field_simp
  have hγL_cast : Real.log (((M + 1 : ℕ) : ℝ) / (R : ℝ) ^ 2) / Real.pi = γ * L := by
    rw [hM1_cast, hγL]
  have hL_cast : Real.log ((M + 1 : ℕ) : ℝ) / Real.pi = L := by dsimp [L]; rw [hM1_cast]
  have hlog2_pi : 2 * Real.log 2 / Real.pi ≤ 1 := by
    rw [div_le_one hpi]; linarith only [Real.log_two_lt_d9, Real.pi_gt_three]
  have hsum_F_eq : ∀ w : ℤ × ℤ,
      ∑ v ∈ F, coeff v * green X s (w - v) =
        (M₁ * c₁ / L) * (green X s (w - rot p) + green X s (w - rot q)) -
          (M₁ * c₃ / ((R : ℝ) * L)) * ∑ v ∈ Prot p R σ, green X s (w - v) := by
    intro w
    dsimp [F]
    rw [Finset.sum_insert (by simp [hne_rot, hp_not_mem]), Finset.sum_insert hq_not_mem]
    have hp_val : coeff (rot p) = M₁ * c₁ / L := by dsimp [coeff]; rw [if_pos (Or.inl rfl)]
    have hq_val : coeff (rot q) = M₁ * c₁ / L := by dsimp [coeff]; rw [if_pos (Or.inr rfl)]
    have hP_sum : ∑ v ∈ Prot p R σ, coeff v * green X s (w - v) =
        -((M₁ * c₃ / ((R : ℝ) * L)) * ∑ v ∈ Prot p R σ, green X s (w - v)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v hv ↦ ?_
      dsimp [coeff]
      rw [if_neg (not_or.mpr ⟨hProt_ne_p v hv, hProt_ne_q v hv⟩), if_pos hv]
      ring
    rw [hp_val, hq_val, hP_sum]
    ring
  have hzne : ¬ (z = rot p ∨ z = rot q) :=
    not_or.mpr ⟨hProt_ne_p z hzP, hProt_ne_q z hzP⟩
  have h1u : 1 - (u z)⁻¹ ≤ -w_p := by
    dsimp [u]; rw [if_neg hzne, if_pos hzP, ← Real.exp_neg, neg_neg]
    linarith only [Real.add_one_le_exp w_p]
  have hzP_mem := hzP
  rw [Prot, Finset.mem_image] at hzP
  obtain ⟨z₀, hz₀, rfl⟩ := hzP
  have hzp_ge : γ * L - 3 ≤ green X s (rot z₀ - rot p) := by
    rw [← rot_sub, hs_eq]
    have hr_eq : rnorm (z₀ - p) = R := mem_P0_rnorm hσ hz₀
    have hge := green_rot_ge hX (by omega : 2 ≤ M + 1) (z₀ - p) (by rw [hr_eq]; exact hR)
    rw [hr_eq] at hge
    have hge' : Real.log (M₁ / (R : ℝ) ^ 2) / Real.pi - 3 ≤
        green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (z₀ - p)) := by
      rw [← hM1_cast]; exact hge
    rw [hγL] at hge'
    exact hge'
  have hzq_ge : γ * L - 4 ≤ green X s (rot z₀ - rot q) := by
    rw [← rot_sub, hs_eq]
    have hzq := mem_P0_rnorm_sub_q (p := p) (q := q) (R := R) hz₀
    have hr_pos : 1 ≤ rnorm (z₀ - q) := by omega
    have hr_le : rnorm (z₀ - q) ≤ 2 * R := by omega
    have hge := green_rot_ge hX (by omega : 2 ≤ M + 1) (z₀ - q) hr_pos
    have hge' : Real.log (M₁ / (rnorm (z₀ - q) : ℝ) ^ 2) / Real.pi - 3 ≤
        green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (z₀ - q)) := by
      rw [← hM1_cast]; exact hge
    have hcmp : Real.log (M₁ / (2 * (R : ℝ)) ^ 2) ≤
        Real.log (M₁ / (rnorm (z₀ - q) : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by linarith only [hM1_ge])
        (by exact_mod_cast (by nlinarith : 0 < rnorm (z₀ - q) ^ 2))
        (by exact_mod_cast (by nlinarith : rnorm (z₀ - q) ^ 2 ≤ (2 * R) ^ 2)))
    have hlog_eq : Real.log (M₁ / (2 * (R : ℝ)) ^ 2) / Real.pi =
        γ * L - 2 * Real.log 2 / Real.pi := by
      rw [show M₁ / (2 * (R : ℝ)) ^ 2 = (M₁ / (R : ℝ) ^ 2) / 2 ^ 2 by ring,
        Real.log_div (by positivity) (by norm_num), Real.log_pow, sub_div, hγL]
      push_cast; ring
    have hd := div_le_div_of_nonneg_right hcmp hpi.le
    linarith only [hge', hd, hlog_eq, hlog2_pi]
  have hP_le : ∑ w ∈ Prot p R σ, green X s (rot z₀ - w) ≤
      (L + 2) + (R : ℝ) * (γ * L + 4) := by
    rw [Prot, Finset.sum_image (fun a _ b _ hab ↦ rot_injective hab)]
    have hnear := sum_green_P0_le_near hX (by omega : 2 ≤ M + 1) p hR (σ := σ) z₀
    have hle1 : ∑ w₀ ∈ P0 p R σ, green X s (rot z₀ - rot w₀) ≤
        ∑ w₀ ∈ P0 p R σ, green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (z₀ - w₀)) :=
      le_of_eq (Finset.sum_congr rfl fun w₀ _ ↦ by rw [← rot_sub, hs_eq])
    rw [hL_cast, hγL_cast, max_eq_right (mul_nonneg hγ_nn hL0.le)] at hnear
    have h4pi : γ * L + 2 + 4 / Real.pi ≤ γ * L + 4 := by
      have : 4 / Real.pi ≤ 2 := by rw [div_le_iff₀ hpi]; linarith only [Real.pi_gt_three]
      linarith only [this]
    exact hle1.trans (hnear.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h4pi hR0.le)))
  have hpsi_ge : M₁ * ψ_low ≤ trialPsi X s F coeff (rot z₀) := by
    unfold trialPsi
    rw [h1s, hsum_F_eq]
    have hc1' : 0 ≤ M₁ * c₁ / L := by positivity
    have hc3' : 0 ≤ M₁ * c₃ / ((R : ℝ) * L) := by positivity
    have h_bd : M₁ * ψ_low ≤ M₁ * (1 + (2 * c₁ - c₃) * γ -
          (7 * c₁ + 4 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hM1_ge])
      dsimp [ψ_low]
      have hsub_le : (7 * c₁ + 4 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L ≤
          (8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L :=
        div_le_div_of_nonneg_right (by linarith only [hc₁, hc₃]) hL0.le
      linarith only [hsub_le]
    have h_eq : M₁ * (1 + (2 * c₁ - c₃) * γ -
          (7 * c₁ + 4 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L) =
        M₁ + ((M₁ * c₁ / L) * (2 * γ * L - 7) -
          (M₁ * c₃ / ((R : ℝ) * L)) * ((L + 2) + (R : ℝ) * (γ * L + 4))) := by
      field_simp [hL0.ne', hR0.ne']; ring
    have h_comb : M₁ + ((M₁ * c₁ / L) * (2 * γ * L - 7) -
          (M₁ * c₃ / ((R : ℝ) * L)) * ((L + 2) + (R : ℝ) * (γ * L + 4))) ≤
        M₁ + ((M₁ * c₁ / L) * (green X s (rot z₀ - rot p) + green X s (rot z₀ - rot q)) -
          (M₁ * c₃ / ((R : ℝ) * L)) * ∑ w ∈ Prot p R σ, green X s (rot z₀ - w)) :=
      add_le_add le_rfl (sub_le_sub (mul_le_mul_of_nonneg_left (by linarith only [hzp_ge, hzq_ge]) hc1')
        (mul_le_mul_of_nonneg_left hP_le hc3'))
    exact h_bd.trans (h_eq ▸ h_comb)
  calc (1 - (u (rot z₀))⁻¹) * trialPsi X s F coeff (rot z₀)
      ≤ (-w_p) * trialPsi X s F coeff (rot z₀) :=
        mul_le_mul_of_nonneg_right h1u (hpsi_nn _)
    _ ≤ (-w_p) * (M₁ * ψ_low) := by
        have : w_p * (M₁ * ψ_low) ≤ w_p * trialPsi X s F coeff (rot z₀) :=
          mul_le_mul_of_nonneg_left hpsi_ge hwp0
        linarith only [this]
    _ = -(M₁ * c₃ / ((R : ℝ) * L)) * (ψ_low / ψ_low) := by dsimp [w_p]; ring
    _ = -(M₁ * c₃ / ((R : ℝ) * L)) := by rw [div_self hψlow_pos.ne', mul_one]
    _ = coeff (rot z₀) := by dsimp [coeff]; rw [if_neg hzne, if_pos hzP_mem]

set_option maxHeartbeats 400000 in
/-- Part B 3-point Chernoff bound with perimeter truncation at `2 * M`. -/
lemma prob_locShift_two_good_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {M : ℕ} (hM : 25 ≤ M)
    {p q : ℤ × ℤ} (hpq : p ≠ q) {R : ℕ} (hR : 1 ≤ R)
    (hdR : rnorm (p - q) ≤ R) (hR2d : R < 2 * rnorm (p - q)) (h3R : (3 * R) ^ 2 ≤ M + 1)
    {c₁ ρ : ℝ} (hc₁ : 0 < c₁) (hρ0 : 0 ≤ ρ) (hρ2 : ρ < 2)
    {v₁ v₃ : ℝ} (_hv₁ : 0 ≤ v₁) (_hv₃ : 0 ≤ v₃)
    (hL_big : 10 * c₁ + 6 * (ρ * c₁) + (ρ * c₁) * (Real.log ((M : ℝ) + 1) / Real.pi + 2) / (R : ℝ) ≤
      Real.log ((M : ℝ) + 1) / Real.pi / 2) :
    let M₁ : ℝ := (M : ℝ) + 1
    let L : ℝ := Real.log M₁ / Real.pi
    let c₃ : ℝ := ρ * c₁
    let γ : ℝ := Real.log (M₁ / (R : ℝ) ^ 2) / Real.log M₁
    let ψ_up : ℝ := 1 + c₁ * (1 + γ - ρ * γ) + (6 * c₁ + 5 * c₃) / L
    let ψ_low : ℝ := 1 + (2 * c₁ - c₃) * γ - (8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L
    (ℙ {ω | v₁ ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        v₁ ≤ (locShift 0 (path X ω) M (rot q) : ℝ) ∧
        (∑ z ∈ Prot p R (pdir p q), (locShift 0 (path X ω) (2 * M) z : ℝ)) ≤ v₃}).toReal ≤
      Real.exp 2 * (1 + 8 * c₁) *
        Real.exp (-(2 * v₁ * (c₁ / (L * ψ_up)) - v₃ * (c₃ / ((R : ℝ) * L * ψ_low)))) := by
  intro M₁ L c₃ γ ψ_up ψ_low
  set σ : ℤ := pdir p q
  have hσ : σ = 1 ∨ σ = -1 := by dsimp [σ, pdir]; split_ifs <;> simp
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hpi := Real.pi_pos
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (this.trans hM1_ge)
  have hL_ge : 3 / 4 ≤ L := by
    dsimp [L]; rw [le_div_iff₀ hpi]; linarith [Real.pi_lt_four]
  have hL0 : 0 < L := by linarith
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hc₃ : 0 ≤ c₃ := mul_nonneg hρ0 hc₁.le
  have hR2 : R ^ 2 ≤ M + 1 := le_trans (by nlinarith) h3R
  have hM1_cast : ((M + 1 : ℕ) : ℝ) = M₁ := by dsimp [M₁]; push_cast; ring
  have hγ_nn : 0 ≤ γ := by
    dsimp [γ]
    refine div_nonneg (Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)) (by linarith)
    rw [← hM1_cast]; exact_mod_cast hR2
  have hγ_le1 : γ ≤ 1 := by
    dsimp [γ]; rw [div_le_one (by linarith)]
    exact Real.log_le_log (by positivity)
      (div_le_self (by linarith) (by exact_mod_cast (by nlinarith : 1 ≤ R ^ 2)))
  have h2c_ge : 0 ≤ 2 * c₁ - c₃ := by
    have : 2 * c₁ - c₃ = (2 - ρ) * c₁ := by dsimp [c₃]; ring
    rw [this]; exact mul_nonneg (by linarith) hc₁.le
  have hψlow_ge : 1 / 2 ≤ ψ_low := by
    dsimp [ψ_low]
    have h1 : (8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L ≤ 1 / 2 := by
      rw [div_le_iff₀ hL0]
      have hL_eq : L = Real.log ((M : ℝ) + 1) / Real.pi := rfl
      have hc3_eq : c₃ = ρ * c₁ := rfl
      linarith only [hL_big, hc₁.le, hL_eq, hc3_eq]
    have h2 : 0 ≤ (2 * c₁ - c₃) * γ := mul_nonneg h2c_ge hγ_nn
    linarith only [h1, h2]
  have hψlow_pos : 0 < ψ_low := by linarith only [hψlow_ge]
  have hψup_ge : c₁ < L * ψ_up := by
    have h1g : 0 ≤ 1 + γ - ρ * γ := by
      have : 1 + γ - ρ * γ = (1 - γ) + (2 - ρ) * γ := by ring
      rw [this]; exact add_nonneg (by linarith) (mul_nonneg (by linarith) hγ_nn)
    have h1 : 1 + 6 * c₁ / L ≤ ψ_up := by
      dsimp [ψ_up]
      rw [add_div]
      have : 0 ≤ c₁ * (1 + γ - ρ * γ) := mul_nonneg hc₁.le h1g
      have : 0 ≤ 5 * c₃ / L := by positivity
      linarith
    have h2 : L * (1 + 6 * c₁ / L) = L + 6 * c₁ := by field_simp [hL0.ne']
    have h3 : L * (1 + 6 * c₁ / L) ≤ L * ψ_up := mul_le_mul_of_nonneg_left h1 hL0.le
    nlinarith only [hc₁, hL_ge, h2, h3]
  have hψup_pos : 0 < ψ_up := by
    have : 0 < L * ψ_up := lt_trans hc₁ hψup_ge
    exact (mul_pos_iff_of_pos_left hL0).mp this
  set τ : ℝ := c₁ / (L * ψ_up)
  set w_p : ℝ := c₃ / ((R : ℝ) * L * ψ_low)
  have hτ0 : 0 < τ := div_pos hc₁ (mul_pos hL0 hψup_pos)
  have hτ1 : τ < 1 := (div_lt_one (mul_pos hL0 hψup_pos)).mpr hψup_ge
  have hwp0 : 0 ≤ w_p := div_nonneg hc₃ (by positivity)
  have hne_rot : rot p ≠ rot q := fun h ↦ hpq (rot_injective h)
  have hp_not_mem : rot p ∉ Prot p R σ := fun hmem ↦ by
    rw [Prot, Finset.mem_image] at hmem
    obtain ⟨p', hp', heq⟩ := hmem
    exact p_not_mem_P0 p hR hσ (rot_injective heq ▸ hp')
  have hq_not_mem : rot q ∉ Prot p R σ := fun hmem ↦ by
    rw [Prot, Finset.mem_image] at hmem
    obtain ⟨q', hq', heq⟩ := hmem
    rw [rot_injective heq] at hq'
    dsimp [σ] at hq'
    exact q_not_mem_P0 p q hR hq'
  have hProt_ne_p : ∀ z ∈ Prot p R σ, z ≠ rot p := fun z hz heq ↦ hp_not_mem (heq ▸ hz)
  have hProt_ne_q : ∀ z ∈ Prot p R σ, z ≠ rot q := fun z hz heq ↦ hq_not_mem (heq ▸ hz)
  let F₀ : Finset (ℤ × ℤ) := insert p (insert q (P0 p R σ))
  let F : Finset (ℤ × ℤ) := F₀.image rot
  have hF_eq : F = insert (rot p) (insert (rot q) (Prot p R σ)) := by
    dsimp [F, F₀, Prot]
    rw [Finset.image_insert, Finset.image_insert]
  let coeff : ℤ × ℤ → ℝ := fun z ↦
    if z = rot p ∨ z = rot q then M₁ * c₁ / L
    else if z ∈ Prot p R σ then -(M₁ * c₃ / ((R : ℝ) * L)) else 0
  let u : ℤ × ℤ → ℝ := fun z ↦
    if z = rot p ∨ z = rot q then (1 - τ)⁻¹
    else if z ∈ Prot p R σ then Real.exp (-w_p) else 1
  have hu_pos : ∀ z, 0 < u z := fun z ↦ by
    dsimp [u]
    split_ifs <;> [exact inv_pos.mpr (by linarith); exact Real.exp_pos _; exact zero_lt_one]
  have hu_out : ∀ z, z ∉ F → u z = 1 := fun z hz ↦ by
    rw [hF_eq, Finset.mem_insert, Finset.mem_insert, not_or, not_or] at hz
    dsimp [u]
    rw [if_neg (by tauto), if_neg hz.2.2]
  set s : ℝ := 1 - 1 / M₁
  have hs0 : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr (by linarith : 0 < M₁)]
  have h1s : 1 / (1 - s) = M₁ := by dsimp [s]; field_simp; ring
  have hs_eq : s = 1 - 1 / ((M + 1 : ℕ) : ℝ) := by dsimp [s]; rw [hM1_cast]
  have hγL : Real.log (M₁ / (R : ℝ) ^ 2) / Real.pi = γ * L := by
    dsimp [γ, L]; field_simp
  have hγL_cast : Real.log (((M + 1 : ℕ) : ℝ) / (R : ℝ) ^ 2) / Real.pi = γ * L := by
    rw [hM1_cast, hγL]
  have hL_cast : Real.log ((M + 1 : ℕ) : ℝ) / Real.pi = L := by
    dsimp [L]; rw [hM1_cast]
  have hlog2_pi : 2 * Real.log 2 / Real.pi ≤ 1 := by
    rw [div_le_one hpi]; linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have hlog3_pi : 2 * Real.log 3 / Real.pi ≤ 2 := by
    have hlog3 : Real.log 3 ≤ 2 := by
      have h1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.exp_one_gt_d9
        calc (3 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
          _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) this.le 2
          _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr h1
    rw [div_le_iff₀ hpi]; linarith [Real.pi_gt_three]
  have hsum_F_eq : ∀ w : ℤ × ℤ,
      ∑ z ∈ F, coeff z * green X s (w - z) =
        (M₁ * c₁ / L) * (green X s (w - rot p) + green X s (w - rot q)) -
          (M₁ * c₃ / ((R : ℝ) * L)) * ∑ z ∈ Prot p R σ, green X s (w - z) := by
    intro w
    rw [hF_eq, Finset.sum_insert (by simp [hne_rot, hp_not_mem]), Finset.sum_insert hq_not_mem]
    have hp_val : coeff (rot p) = M₁ * c₁ / L := by dsimp [coeff]; rw [if_pos (Or.inl rfl)]
    have hq_val : coeff (rot q) = M₁ * c₁ / L := by dsimp [coeff]; rw [if_pos (Or.inr rfl)]
    have hP_sum : ∑ z ∈ Prot p R σ, coeff z * green X s (w - z) =
        -((M₁ * c₃ / ((R : ℝ) * L)) * ∑ z ∈ Prot p R σ, green X s (w - z)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z hz ↦ ?_
      dsimp [coeff]
      rw [if_neg (not_or.mpr ⟨hProt_ne_p z hz, hProt_ne_q z hz⟩), if_pos hz]
      ring
    rw [hp_val, hq_val, hP_sum]
    ring
  have hpsi_rot_ge : ∀ w₀ : ℤ × ℤ, M₁ / 2 ≤ trialPsi X s F coeff (rot w₀) := fun w₀ ↦ by
    rw [show s = 1 - 1 / M₁ from rfl, hF_eq]
    exact prob_locShift_two_good_psi_rot_ge hX hM hpq hR hdR h3R hc₁ hρ0 hρ2 hL_big w₀
  have hpsi_nn : ∀ w, 0 ≤ trialPsi X s F coeff w := by
    rw [show F = F₀.image rot from rfl]
    exact trialPsi_nonneg_of_rot hX hs0 hs1 fun w₀ ↦ le_trans (by linarith only [hM1_ge]) (hpsi_rot_ge w₀)
  have hpsi_in : ∀ z ∈ F, (1 - (u z)⁻¹) * trialPsi X s F coeff z ≤ coeff z := by
    intro z hz
    rw [hF_eq, Finset.mem_insert, Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hzP
    · have h1u : 1 - (u (rot p))⁻¹ = τ := by
        dsimp [u]; rw [if_pos (Or.inl rfl), inv_inv]; ring
      have hg0 : green X s (rot p - rot p) ≤ L + 2 := by
        rw [sub_self, hs_eq]
        have h0 := green_zero_le hX (by omega : 2 ≤ M + 1)
        rwa [hL_cast] at h0
      have hgd : green X s (rot p - rot q) ≤ γ * L + 3 := by
        rw [← rot_sub, hs_eq]
        have hd1 : 1 ≤ rnorm (p - q) :=
          Nat.pos_of_ne_zero fun h0 ↦ hpq (sub_eq_zero.mp ((rnorm_eq_zero_iff (p - q)).mp h0))
        have hg := green_rot_le hX (by omega : 2 ≤ M + 1) (p - q) hd1
        have hg' : green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (p - q)) ≤
            max 0 (Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.pi) + 2 := by
          rw [← hM1_cast]; exact hg
        have hcmp : Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.pi ≤ γ * L + 1 := by
          have hd0 : (0 : ℝ) < rnorm (p - q) := by exact_mod_cast hd1
          have hdiv : M₁ / (rnorm (p - q) : ℝ) ^ 2 ≤ 4 * (M₁ / (R : ℝ) ^ 2) := by
            rw [div_le_iff₀ (by positivity)]
            calc M₁ = M₁ / (R : ℝ) ^ 2 * (R : ℝ) ^ 2 := by field_simp [hR0.ne']
              _ ≤ M₁ / (R : ℝ) ^ 2 * (2 * (rnorm (p - q) : ℝ)) ^ 2 := by
                  gcongr; exact_mod_cast hR2d.le
              _ = 4 * (M₁ / (R : ℝ) ^ 2) * (rnorm (p - q) : ℝ) ^ 2 := by ring
          have h1 := Real.log_le_log (by positivity) hdiv
          rw [Real.log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.log_pow] at h1
          push_cast at h1
          have h1d := div_le_div_of_nonneg_right h1 hpi.le
          rw [show (2 * Real.log 2 + Real.log (M₁ / (R : ℝ) ^ 2)) / Real.pi =
            2 * Real.log 2 / Real.pi + Real.log (M₁ / (R : ℝ) ^ 2) / Real.pi by ring,
            hγL] at h1d
          linarith only [h1d, hlog2_pi]
        have hmax : max 0 (Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.pi) ≤ γ * L + 1 :=
          max_le (mul_nonneg hγ_nn hL0.le |>.trans (by linarith only)) hcmp
        linarith only [hg', hmax]
      have hP_ge : (R : ℝ) * (γ * L - 3) ≤ ∑ w ∈ Prot p R σ, green X s (rot p - w) := by
        rw [Prot, Finset.sum_image (fun a _ b _ hab ↦ rot_injective hab)]
        calc (R : ℝ) * (γ * L - 3) = ∑ _ ∈ P0 p R σ, (γ * L - 3) := by
              rw [Finset.sum_const, P0_card, nsmul_eq_mul]
          _ ≤ ∑ z₀ ∈ P0 p R σ, green X s (rot p - rot z₀) := by
              refine Finset.sum_le_sum fun z₀ hz₀ ↦ ?_
              rw [← rot_sub, hs_eq]
              have hr_eq : rnorm (p - z₀) = R := by
                rw [show p - z₀ = -(z₀ - p) by abel, rnorm_neg, mem_P0_rnorm hσ hz₀]
              have hge := green_rot_ge hX (by omega : 2 ≤ M + 1) (p - z₀)
                (by rw [hr_eq]; exact hR)
              rw [hr_eq] at hge
              have hge' : Real.log (M₁ / (R : ℝ) ^ 2) / Real.pi - 3 ≤
                  green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (p - z₀)) := by
                rw [← hM1_cast]; exact hge
              rw [hγL] at hge'
              exact hge'
      have hpsi_le : trialPsi X s F coeff (rot p) ≤ M₁ * ψ_up := by
        unfold trialPsi
        rw [h1s, hsum_F_eq]
        have hc1' : 0 ≤ M₁ * c₁ / L := by positivity
        have hc3' : 0 ≤ M₁ * c₃ / ((R : ℝ) * L) := by positivity
        have h_comb : M₁ + ((M₁ * c₁ / L) * (green X s (rot p - rot p) + green X s (rot p - rot q)) -
              (M₁ * c₃ / ((R : ℝ) * L)) * ∑ w ∈ Prot p R σ, green X s (rot p - w)) ≤
            M₁ + ((M₁ * c₁ / L) * ((L + 2) + (γ * L + 3)) -
              (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (γ * L - 3))) :=
          add_le_add le_rfl (sub_le_sub (mul_le_mul_of_nonneg_left (add_le_add hg0 hgd) hc1')
            (mul_le_mul_of_nonneg_left hP_ge hc3'))
        have h_eq : M₁ + ((M₁ * c₁ / L) * ((L + 2) + (γ * L + 3)) -
              (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (γ * L - 3))) =
            M₁ * (1 + c₁ * (1 + γ - ρ * γ) + (5 * c₁ + 3 * c₃) / L) := by
          dsimp [c₃]; field_simp [hL0.ne', hR0.ne']; ring
        have h_bd : M₁ * (1 + c₁ * (1 + γ - ρ * γ) + (5 * c₁ + 3 * c₃) / L) ≤ M₁ * ψ_up := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hM1_ge])
          dsimp [ψ_up]
          have hc_add : (5 * c₁ + 3 * c₃) / L ≤ (6 * c₁ + 5 * c₃) / L :=
            div_le_div_of_nonneg_right (by linarith only [hc₁, hc₃]) hL0.le
          linarith only [hc_add]
        exact h_comb.trans (h_eq.symm ▸ h_bd)
      rw [h1u]
      calc τ * trialPsi X s F coeff (rot p) ≤ τ * (M₁ * ψ_up) :=
            mul_le_mul_of_nonneg_left hpsi_le hτ0.le
        _ = (M₁ * c₁ / L) * (ψ_up / ψ_up) := by dsimp [τ]; ring
        _ = M₁ * c₁ / L := by rw [div_self hψup_pos.ne', mul_one]
        _ = coeff (rot p) := by dsimp [coeff]; rw [if_pos (Or.inl rfl)]
    · have h1u : 1 - (u (rot q))⁻¹ = τ := by
        dsimp [u]; rw [if_pos (Or.inr rfl), inv_inv]; ring
      have hg0 : green X s (rot q - rot q) ≤ L + 2 := by
        rw [sub_self, hs_eq]
        have h0 := green_zero_le hX (by omega : 2 ≤ M + 1)
        rwa [hL_cast] at h0
      have hgd : green X s (rot q - rot p) ≤ γ * L + 3 := by
        rw [← rot_sub, hs_eq]
        have hd1 : 1 ≤ rnorm (q - p) :=
          Nat.pos_of_ne_zero fun h0 ↦ hpq.symm (sub_eq_zero.mp ((rnorm_eq_zero_iff (q - p)).mp h0))
        have hg := green_rot_le hX (by omega : 2 ≤ M + 1) (q - p) hd1
        have hr_eq : rnorm (q - p) = rnorm (p - q) := by
          rw [show q - p = -(p - q) by abel, rnorm_neg]
        rw [hr_eq] at hg
        have hg' : green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (q - p)) ≤
            max 0 (Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.pi) + 2 := by
          rw [← hM1_cast]; exact hg
        have hcmp : Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.pi ≤ γ * L + 1 := by
          have hd1' : 1 ≤ rnorm (p - q) := by rw [← hr_eq]; exact hd1
          have hd0 : (0 : ℝ) < rnorm (p - q) := by exact_mod_cast hd1'
          have hdiv : M₁ / (rnorm (p - q) : ℝ) ^ 2 ≤ 4 * (M₁ / (R : ℝ) ^ 2) := by
            rw [div_le_iff₀ (by positivity)]
            calc M₁ = M₁ / (R : ℝ) ^ 2 * (R : ℝ) ^ 2 := by field_simp [hR0.ne']
              _ ≤ M₁ / (R : ℝ) ^ 2 * (2 * (rnorm (p - q) : ℝ)) ^ 2 := by
                  gcongr; exact_mod_cast hR2d.le
              _ = 4 * (M₁ / (R : ℝ) ^ 2) * (rnorm (p - q) : ℝ) ^ 2 := by ring
          have h1 := Real.log_le_log (by positivity) hdiv
          rw [Real.log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.log_pow] at h1
          push_cast at h1
          have h1d := div_le_div_of_nonneg_right h1 hpi.le
          rw [show (2 * Real.log 2 + Real.log (M₁ / (R : ℝ) ^ 2)) / Real.pi =
            2 * Real.log 2 / Real.pi + Real.log (M₁ / (R : ℝ) ^ 2) / Real.pi by ring,
            hγL] at h1d
          linarith only [h1d, hlog2_pi]
        have hmax : max 0 (Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.pi) ≤ γ * L + 1 :=
          max_le (mul_nonneg hγ_nn hL0.le |>.trans (by linarith only)) hcmp
        linarith only [hg', hmax]
      have hP_ge : (R : ℝ) * (γ * L - 4) ≤ ∑ w ∈ Prot p R σ, green X s (rot q - w) := by
        rw [Prot, Finset.sum_image (fun a _ b _ hab ↦ rot_injective hab)]
        calc (R : ℝ) * (γ * L - 4) = ∑ _ ∈ P0 p R σ, (γ * L - 4) := by
              rw [Finset.sum_const, P0_card, nsmul_eq_mul]
          _ ≤ ∑ z₀ ∈ P0 p R σ, green X s (rot q - rot z₀) := by
              refine Finset.sum_le_sum fun z₀ hz₀ ↦ ?_
              rw [← rot_sub, hs_eq]
              have hqz := mem_P0_rnorm_sub_q (p := p) (q := q) (R := R) hz₀
              have hr_pos : 1 ≤ rnorm (q - z₀) := by
                rw [show q - z₀ = -(z₀ - q) by abel, rnorm_neg]; omega
              have hr_le : rnorm (q - z₀) ≤ 2 * R := by
                rw [show q - z₀ = -(z₀ - q) by abel, rnorm_neg]; omega
              have hge := green_rot_ge hX (by omega : 2 ≤ M + 1) (q - z₀) hr_pos
              have hge' : Real.log (M₁ / (rnorm (q - z₀) : ℝ) ^ 2) / Real.pi - 3 ≤
                  green X (1 - 1 / ((M + 1 : ℕ) : ℝ)) (rot (q - z₀)) := by
                rw [← hM1_cast]; exact hge
              have hcmp : Real.log (M₁ / (2 * (R : ℝ)) ^ 2) ≤
                  Real.log (M₁ / (rnorm (q - z₀) : ℝ) ^ 2) :=
                Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by linarith only [hM1_ge])
                  (by exact_mod_cast (by nlinarith : 0 < rnorm (q - z₀) ^ 2))
                  (by exact_mod_cast (by nlinarith : rnorm (q - z₀) ^ 2 ≤ (2 * R) ^ 2)))
              have hlog_eq : Real.log (M₁ / (2 * (R : ℝ)) ^ 2) / Real.pi =
                  γ * L - 2 * Real.log 2 / Real.pi := by
                rw [show M₁ / (2 * (R : ℝ)) ^ 2 = (M₁ / (R : ℝ) ^ 2) / 2 ^ 2 by ring,
                  Real.log_div (by positivity) (by norm_num), Real.log_pow, sub_div, hγL]
                push_cast; ring
              have hd := div_le_div_of_nonneg_right hcmp hpi.le
              linarith only [hge', hd, hlog_eq, hlog2_pi]
      have hpsi_le : trialPsi X s F coeff (rot q) ≤ M₁ * ψ_up := by
        unfold trialPsi
        rw [h1s, hsum_F_eq]
        have hc1' : 0 ≤ M₁ * c₁ / L := by positivity
        have hc3' : 0 ≤ M₁ * c₃ / ((R : ℝ) * L) := by positivity
        have h_comb : M₁ + ((M₁ * c₁ / L) * (green X s (rot q - rot p) + green X s (rot q - rot q)) -
              (M₁ * c₃ / ((R : ℝ) * L)) * ∑ w ∈ Prot p R σ, green X s (rot q - w)) ≤
            M₁ + ((M₁ * c₁ / L) * ((γ * L + 3) + (L + 2)) -
              (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (γ * L - 4))) :=
          add_le_add le_rfl (sub_le_sub (mul_le_mul_of_nonneg_left (add_le_add hgd hg0) hc1')
            (mul_le_mul_of_nonneg_left hP_ge hc3'))
        have h_eq : M₁ + ((M₁ * c₁ / L) * ((γ * L + 3) + (L + 2)) -
              (M₁ * c₃ / ((R : ℝ) * L)) * ((R : ℝ) * (γ * L - 4))) =
            M₁ * (1 + c₁ * (1 + γ - ρ * γ) + (5 * c₁ + 4 * c₃) / L) := by
          dsimp [c₃]; field_simp [hL0.ne', hR0.ne']; ring
        have h_bd : M₁ * (1 + c₁ * (1 + γ - ρ * γ) + (5 * c₁ + 4 * c₃) / L) ≤ M₁ * ψ_up := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hM1_ge])
          dsimp [ψ_up]
          have hc_add : (5 * c₁ + 4 * c₃) / L ≤ (6 * c₁ + 5 * c₃) / L :=
            div_le_div_of_nonneg_right (by linarith only [hc₁, hc₃]) hL0.le
          linarith only [hc_add]
        exact h_comb.trans (h_eq.symm ▸ h_bd)
      rw [h1u]
      calc τ * trialPsi X s F coeff (rot q) ≤ τ * (M₁ * ψ_up) :=
            mul_le_mul_of_nonneg_left hpsi_le hτ0.le
        _ = (M₁ * c₁ / L) * (ψ_up / ψ_up) := by dsimp [τ]; ring
        _ = M₁ * c₁ / L := by rw [div_self hψup_pos.ne', mul_one]
        _ = coeff (rot q) := by dsimp [coeff]; rw [if_pos (Or.inr rfl)]
    · rw [show s = 1 - 1 / M₁ from rfl, hF_eq]
      refine prob_locShift_two_good_psi_in_Prot hX hM hpq hR hdR h3R hc₁ hρ0 hρ2 hL_big τ ?_ z hzP
      intro w
      change 0 ≤ trialPsi X s (insert (rot p) (insert (rot q) (Prot p R σ))) coeff w
      rw [← hF_eq]
      exact hpsi_nn w
  let A_good : Set (ℕ → ℤ × ℤ) :=
    {y | v₁ ≤ (locShift 0 y M (rot p) : ℝ) ∧ v₁ ≤ (locShift 0 y M (rot q) : ℝ) ∧
      (∑ z ∈ Prot p R σ, (locShift 0 y (2 * M) z : ℝ)) ≤ v₃}
  let B : ℝ := Real.exp (2 * v₁ * τ - v₃ * w_p)
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hBA_k : ∀ k : ℕ, ∀ y : ℕ → ℤ × ℤ,
      v₁ ≤ (locShift 0 y k (rot p) : ℝ) → v₁ ≤ (locShift 0 y k (rot q) : ℝ) →
      (∑ z ∈ Prot p R σ, (locShift 0 y k z : ℝ)) ≤ v₃ →
      B ≤ prodWalk u 0 y k := by
    intro k y hy1 hy2 hy3
    rw [prodWalk_eq_finset_pow hu_out, hF_eq, Finset.prod_insert (by simp [hne_rot, hp_not_mem]),
      Finset.prod_insert hq_not_mem]
    have hexp_1 : ∀ z, z = rot p ∨ z = rot q →
        ∀ l : ℕ, v₁ ≤ (l : ℝ) → Real.exp (v₁ * τ) ≤ (u z) ^ l := by
      intro z hz l hl
      have h1 : Real.exp τ ≤ u z := by
        dsimp [u]; rw [if_pos hz]
        have h1m : 0 < 1 - τ := by linarith
        rw [← inv_inv (Real.exp τ), ← Real.exp_neg]
        exact inv_anti₀ h1m (Real.one_sub_le_exp_neg τ)
      calc Real.exp (v₁ * τ) ≤ Real.exp ((l : ℝ) * τ) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hl hτ0.le)
        _ = (Real.exp τ) ^ l := by rw [Real.exp_nat_mul]
        _ ≤ (u z) ^ l := pow_le_pow_left₀ (Real.exp_pos _).le h1 _
    have hexp_P : Real.exp (-(v₃ * w_p)) ≤ ∏ z ∈ Prot p R σ, (u z) ^ locShift 0 y k z := by
      have h_each : ∀ z ∈ Prot p R σ,
          (u z) ^ locShift 0 y k z = Real.exp (-((locShift 0 y k z : ℝ) * w_p)) := by
        intro z hz
        have hzne : ¬ (z = rot p ∨ z = rot q) :=
          not_or.mpr ⟨hProt_ne_p z hz, hProt_ne_q z hz⟩
        dsimp [u]; rw [if_neg hzne, if_pos hz, ← Real.exp_nat_mul]
        congr 1; ring
      rw [Finset.prod_congr rfl h_each, ← Real.exp_sum]
      refine Real.exp_le_exp.mpr ?_
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
      linarith only [mul_le_mul_of_nonneg_right hy3 hwp0]
    calc B = (Real.exp (v₁ * τ) * Real.exp (v₁ * τ)) * Real.exp (-(v₃ * w_p)) := by
          dsimp [B]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ ((u (rot p)) ^ locShift 0 y k (rot p) * (u (rot q)) ^ locShift 0 y k (rot q)) *
            ∏ z ∈ Prot p R σ, (u z) ^ locShift 0 y k z := by
          refine mul_le_mul (mul_le_mul (hexp_1 (rot p) (Or.inl rfl) _ hy1)
            (hexp_1 (rot q) (Or.inr rfl) _ hy2) (Real.exp_pos _).le (pow_nonneg (hu_pos _).le _))
            hexp_P (Real.exp_pos _).le (mul_nonneg (pow_nonneg (hu_pos _).le _) (pow_nonneg (hu_pos _).le _))
      _ = _ := by ring
  let A_seq : ℕ → Set (ℕ → ℤ × ℤ) := fun k ↦
    if M ≤ k then
      {y | v₁ ≤ (locShift 0 y k (rot p) : ℝ) ∧ v₁ ≤ (locShift 0 y k (rot q) : ℝ) ∧
        (∑ z ∈ Prot p R σ, (locShift 0 y k z : ℝ)) ≤ v₃}
    else ∅
  have hA_det : ∀ k, Det k (A_seq k) := fun k ↦ by
    dsimp [A_seq]
    split_ifs with hk
    · intro y y' h hy
      refine ⟨?_, ?_, ?_⟩
      · rw [← det_locShift k (rot p) y y' h]; exact hy.1
      · rw [← det_locShift k (rot q) y y' h]; exact hy.2.1
      · refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ ↦ ?_)) hy.2.2
        rw [det_locShift k z y y' h]
    · exact fun _ _ _ hmem ↦ False.elim hmem
  have hA_B : ∀ k, ∀ y ∈ A_seq k, B ≤ prodWalk u 0 y k := fun k y hy ↦ by
    dsimp [A_seq] at hy
    split_ifs at hy with hk
    · exact hBA_k k y hy.1 hy.2.1 hy.2.2
    · exact False.elim hy
  have hfk := feynman_kac_chernoff hX hs0 hs1 hu_pos hu_out hpsi_nn hpsi_in hA_det hB0 hA_B (2 * M)
  have hsub_icc : Finset.Icc M (2 * M) ⊆ Finset.range (2 * M + 1) := fun k hk ↦ by
    rw [Finset.mem_Icc] at hk; exact Finset.mem_range.mpr (by omega)
  have hsub_A : ∀ k ∈ Finset.Icc M (2 * M),
      (ℙ {ω | path X ω ∈ A_good}).toReal ≤ (ℙ {ω | path X ω ∈ A_seq k}).toReal := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hset_sub : {ω : Ω | path X ω ∈ A_good} ⊆ {ω : Ω | path X ω ∈ A_seq k} := by
      intro ω hω
      dsimp only [A_seq, A_good, Set.mem_ofPred_eq] at hω ⊢
      rw [if_pos hk.1]
      refine ⟨hω.1.trans (by exact_mod_cast locShift_zero_mono hk.1 (rot p)),
        hω.2.1.trans (by exact_mod_cast locShift_zero_mono hk.1 (rot q)), ?_⟩
      refine le_trans (Finset.sum_le_sum fun z _ ↦ ?_) hω.2.2
      exact_mod_cast locShift_zero_mono hk.2 z
    exact ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hset_sub)
  have hs2M : (Real.exp 1)⁻¹ ^ 2 ≤ s ^ (2 * M) := by
    rw [mul_comm 2 M, pow_mul, hs_eq]
    have h1 : (Real.exp 1)⁻¹ ≤ (1 - 1 / ((M + 1 : ℕ) : ℝ)) ^ M := by
      simpa [Nat.cast_add, Nat.cast_one] using one_sub_inv_pow_ge M (by omega)
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hs_k : ∀ k ∈ Finset.Icc M (2 * M), Real.exp (-2) ≤ s ^ k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    calc Real.exp (-2) = (Real.exp 1)⁻¹ ^ 2 := by
          rw [inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]; norm_num
      _ ≤ s ^ (2 * M) := hs2M
      _ ≤ s ^ k := pow_le_pow_of_le_one hs0 hs1.le hk.2
  have hsum_lower : B * (M₁ * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_good}).toReal) ≤
      B * ∑ k ∈ Finset.range (2 * M + 1), s ^ k * (ℙ {ω | path X ω ∈ A_seq k}).toReal := by
    refine mul_le_mul_of_nonneg_left ?_ hB0
    calc M₁ * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_good}).toReal
        = ∑ _ ∈ Finset.Icc M (2 * M), Real.exp (-2) * (ℙ {ω | path X ω ∈ A_good}).toReal := by
          rw [Finset.sum_const, Nat.card_Icc, show 2 * M + 1 - M = M + 1 by omega, nsmul_eq_mul,
            hM1_cast]; ring
      _ ≤ ∑ k ∈ Finset.Icc M (2 * M), s ^ k * (ℙ {ω | path X ω ∈ A_seq k}).toReal := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          exact mul_le_mul (hs_k k hk) (hsub_A k hk) ENNReal.toReal_nonneg (pow_nonneg hs0 k)
      _ ≤ ∑ k ∈ Finset.range (2 * M + 1), s ^ k * (ℙ {ω | path X ω ∈ A_seq k}).toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_icc fun k _ _ ↦
            mul_nonneg (pow_nonneg hs0 k) ENNReal.toReal_nonneg
  have hrhs : 1 / (1 - s) + ∑ z ∈ F, coeff z * green X s z ≤ M₁ * (1 + 8 * c₁) := by
    have hL4 : L + 2 ≤ 4 * L := by linarith only [hL_ge]
    have hgp : green X s (rot p) ≤ 4 * L := by
      rw [hs_eq]
      have h0 := green_rot_le_zero hX (by omega : 2 ≤ M + 1) p
      rw [hL_cast] at h0
      exact h0.trans hL4
    have hgq : green X s (rot q) ≤ 4 * L := by
      rw [hs_eq]
      have h0 := green_rot_le_zero hX (by omega : 2 ≤ M + 1) q
      rw [hL_cast] at h0
      exact h0.trans hL4
    have hP0_nn : 0 ≤ (M₁ * c₃ / ((R : ℝ) * L)) * ∑ z ∈ Prot p R σ, green X s z :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ ↦ green_nonneg X hs0 _)
    have hsum0 : ∑ z ∈ F, coeff z * green X s z = ∑ z ∈ F, coeff z * green X s (0 - z) :=
      Finset.sum_congr rfl fun z _ ↦ by rw [zero_sub, green_symm hX]
    have hsym : ∀ z, green X s (0 - z) = green X s z := fun z ↦ by rw [zero_sub, green_symm hX]
    rw [h1s, hsum0, hsum_F_eq 0, hsym, hsym]
    simp_rw [hsym]
    calc M₁ + ((M₁ * c₁ / L) * (green X s (rot p) + green X s (rot q)) -
          (M₁ * c₃ / ((R : ℝ) * L)) * ∑ z ∈ Prot p R σ, green X s z)
        ≤ M₁ + (M₁ * c₁ / L) * (4 * L + 4 * L) := by
          have : (M₁ * c₁ / L) * (green X s (rot p) + green X s (rot q)) ≤
              (M₁ * c₁ / L) * (4 * L + 4 * L) :=
            mul_le_mul_of_nonneg_left (add_le_add hgp hgq) (by positivity)
          linarith only [this, hP0_nn]
      _ = M₁ * (1 + 8 * c₁) := by field_simp [hL0.ne']; ring
  have hcomb : M₁ * (B * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_good}).toReal) ≤
      M₁ * (1 + 8 * c₁) := by
    calc M₁ * (B * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_good}).toReal)
        = B * (M₁ * Real.exp (-2) * (ℙ {ω | path X ω ∈ A_good}).toReal) := by ring
      _ ≤ M₁ * (1 + 8 * c₁) := hsum_lower.trans (hfk.trans hrhs)
  have hcomb' := le_of_mul_le_mul_left hcomb (by linarith only [hM1_ge] : 0 < M₁)
  have hB_pos : 0 < B * Real.exp (-2) := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hfinal : (ℙ {ω | path X ω ∈ A_good}).toReal ≤ Real.exp 2 * (1 + 8 * c₁) * B⁻¹ := by
    have : (ℙ {ω | path X ω ∈ A_good}).toReal * (B * Real.exp (-2)) ≤ 1 + 8 * c₁ := by
      linarith only [hcomb']
    calc (ℙ {ω | path X ω ∈ A_good}).toReal
        ≤ (1 + 8 * c₁) / (B * Real.exp (-2)) := (le_div_iff₀ hB_pos).mpr this
      _ = Real.exp 2 * (1 + 8 * c₁) * B⁻¹ := by
          rw [div_eq_mul_inv, mul_inv, Real.exp_neg, inv_inv]; ring
  rw [show B⁻¹ = Real.exp (-(2 * v₁ * τ - v₃ * w_p)) from (Real.exp_neg _).symm] at hfinal
  exact hfinal

/- ### Section 6: Finite Paley-Zygmund, Block Amplification, and H2 Completion -/

/-- Finite-indicator Paley-Zygmund second-moment lower bound on `P(⋃ x ∈ Q, E x)`. -/
lemma paley_zygmund_finset {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {ι : Type*} [DecidableEq ι] (Q : Finset ι) (E : ι → Set Ω)
    (hEm : ∀ x ∈ Q, MeasurableSet (E x))
    {S₁ S₂ : ℝ} (hS1_pos : 0 < S₁) (hS2_pos : 0 < S₂)
    (h1 : S₁ ≤ ∑ x ∈ Q, (ℙ (E x)).toReal)
    (h2 : ∑ p ∈ Q ×ˢ Q, (ℙ (E p.1 ∩ E p.2)).toReal ≤ S₂) :
    S₁ ^ 2 / S₂ ≤ (ℙ (⋃ x ∈ Q, E x)).toReal := by
  classical
  let Ppos : Finset (Finset ι) := Q.powerset.filter fun T ↦ T.Nonempty
  let atom : Finset ι → Set Ω := fun T ↦ {ω | ∀ x ∈ Q, ω ∈ E x ↔ x ∈ T}
  have hatom_eq : ∀ T : Finset ι, atom T = ⋂ x ∈ Q, if x ∈ T then E x else (E x)ᶜ := by
    intro T; ext ω
    simp only [atom, Set.mem_ofPred_eq, Set.mem_iInter]
    refine forall₂_congr fun x _ ↦ ?_
    by_cases hx : x ∈ T <;> simp [hx]
  have hatom_meas : ∀ T : Finset ι, MeasurableSet (atom T) := fun T ↦ by
    rw [hatom_eq T]
    exact MeasurableSet.biInter Q.countable_toSet fun x hx ↦ by
      split_ifs
      · exact hEm x hx
      · exact (hEm x hx).compl
  have hatom_disj : Set.PairwiseDisjoint (Ppos : Set (Finset ι)) atom := by
    intro T₁ hT1 T₂ hT2 hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1ω h2ω
    have hT1Q : T₁ ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hT1).1
    have hT2Q : T₂ ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hT2).1
    have hnot : ¬ (T₁ ⊆ T₂ ∧ T₂ ⊆ T₁) := fun ⟨h12, h21⟩ ↦ hne (Finset.Subset.antisymm h12 h21)
    rw [not_and_or, Finset.not_subset, Finset.not_subset] at hnot
    rcases hnot with ⟨x, hx1, hx2⟩ | ⟨x, hx2, hx1⟩
    · exact hx2 ((h2ω x (hT1Q hx1)).mp ((h1ω x (hT1Q hx1)).mpr hx1))
    · exact hx1 ((h1ω x (hT2Q hx2)).mp ((h2ω x (hT2Q hx2)).mpr hx2))
  have hU_eq : (⋃ x ∈ Q, E x) = ⋃ T ∈ Ppos, atom T := by
    ext ω
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x₀, hx₀, hω⟩
      refine ⟨Q.filter (fun x ↦ ω ∈ E x), Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.filter_subset _ _), ⟨x₀, Finset.mem_filter.mpr ⟨hx₀, hω⟩⟩⟩, fun x hx ↦ ?_⟩
      simp [hx]
    · rintro ⟨T, hT, hω⟩
      obtain ⟨hTQ, ⟨x₀, hx₀⟩⟩ := Finset.mem_filter.mp hT
      have hx₀Q : x₀ ∈ Q := Finset.mem_powerset.mp hTQ hx₀
      exact ⟨x₀, hx₀Q, (hω x₀ hx₀Q).mpr hx₀⟩
  have hE_eq : ∀ x ∈ Q, E x = ⋃ T ∈ Ppos.filter (x ∈ ·), atom T := by
    intro x hx; ext ω
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter]
    constructor
    · intro hω
      refine ⟨Q.filter (fun y ↦ ω ∈ E y), ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.filter_subset _ _), ⟨x, Finset.mem_filter.mpr ⟨hx, hω⟩⟩⟩,
        Finset.mem_filter.mpr ⟨hx, hω⟩⟩, fun y hy ↦ ?_⟩
      simp [hy]
    · rintro ⟨T, ⟨_, hxT⟩, hω⟩
      exact (hω x hx).mpr hxT
  have hEE_eq : ∀ p ∈ Q ×ˢ Q, E p.1 ∩ E p.2 = ⋃ T ∈ Ppos.filter (fun T ↦ p.1 ∈ T ∧ p.2 ∈ T), atom T := by
    intro p hp; rw [Finset.mem_product] at hp; ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop, Finset.mem_filter]
    constructor
    · rintro ⟨h1ω, h2ω⟩
      refine ⟨Q.filter (fun y ↦ ω ∈ E y), ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.filter_subset _ _), ⟨p.1, Finset.mem_filter.mpr ⟨hp.1, h1ω⟩⟩⟩,
        Finset.mem_filter.mpr ⟨hp.1, h1ω⟩, Finset.mem_filter.mpr ⟨hp.2, h2ω⟩⟩, fun y hy ↦ ?_⟩
      simp [hy]
    · rintro ⟨T, ⟨_, hp1, hp2⟩, hω⟩
      exact ⟨(hω p.1 hp.1).mpr hp1, (hω p.2 hp.2).mpr hp2⟩
  let μT : Finset ι → ℝ := fun T ↦ (ℙ (atom T)).toReal
  have hμ_nn : ∀ T, 0 ≤ μT T := fun _ ↦ ENNReal.toReal_nonneg
  have hU_sum : (ℙ (⋃ x ∈ Q, E x)).toReal = ∑ T ∈ Ppos, μT T := by
    rw [hU_eq, measure_biUnion_finset hatom_disj (fun T _ ↦ hatom_meas T),
      ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top ℙ _)]
  have hE_sum : ∑ x ∈ Q, (ℙ (E x)).toReal = ∑ T ∈ Ppos, (T.card : ℝ) * μT T := by
    have h_each : ∀ x ∈ Q, (ℙ (E x)).toReal = ∑ T ∈ Ppos, (if x ∈ T then μT T else 0) := by
      intro x hx
      rw [hE_eq x hx, measure_biUnion_finset (hatom_disj.subset (Finset.filter_subset _ _))
        (fun T _ ↦ hatom_meas T), ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top ℙ _),
        Finset.sum_filter]
    rw [Finset.sum_congr rfl h_each, Finset.sum_comm]
    refine Finset.sum_congr rfl fun T hT ↦ ?_
    have hTQ : T ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    rw [← Finset.sum_filter,
      show Q.filter (· ∈ T) = T by
        ext x; simp only [Finset.mem_filter, and_iff_right_iff_imp]; exact fun h ↦ hTQ h,
      Finset.sum_const, nsmul_eq_mul]
  have hEE_sum : ∑ p ∈ Q ×ˢ Q, (ℙ (E p.1 ∩ E p.2)).toReal = ∑ T ∈ Ppos, (T.card : ℝ) ^ 2 * μT T := by
    have h_each : ∀ p ∈ Q ×ˢ Q, (ℙ (E p.1 ∩ E p.2)).toReal =
        ∑ T ∈ Ppos, (if p.1 ∈ T ∧ p.2 ∈ T then μT T else 0) := by
      intro p hp
      rw [hEE_eq p hp, measure_biUnion_finset (hatom_disj.subset (Finset.filter_subset _ _))
        (fun T _ ↦ hatom_meas T), ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top ℙ _),
        Finset.sum_filter]
    rw [Finset.sum_congr rfl h_each, Finset.sum_comm]
    refine Finset.sum_congr rfl fun T hT ↦ ?_
    have hTQ : T ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    rw [← Finset.sum_filter,
      show (Q ×ˢ Q).filter (fun p ↦ p.1 ∈ T ∧ p.2 ∈ T) = T ×ˢ T by
        ext p; simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨hTQ h.1, hTQ h.2⟩, h⟩⟩,
      Finset.sum_const, Finset.card_product, nsmul_eq_mul, Nat.cast_mul, ← sq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Ppos (fun T ↦ Real.sqrt (μT T))
    (fun T ↦ (T.card : ℝ) * Real.sqrt (μT T))
  have hcs1 : ∑ T ∈ Ppos, Real.sqrt (μT T) * ((T.card : ℝ) * Real.sqrt (μT T)) =
      ∑ T ∈ Ppos, (T.card : ℝ) * μT T :=
    Finset.sum_congr rfl fun T _ ↦ by
      rw [mul_left_comm, Real.mul_self_sqrt (hμ_nn T)]
  have hcs2 : ∑ T ∈ Ppos, Real.sqrt (μT T) ^ 2 = ∑ T ∈ Ppos, μT T :=
    Finset.sum_congr rfl fun T _ ↦ Real.sq_sqrt (hμ_nn T)
  have hcs3 : ∑ T ∈ Ppos, ((T.card : ℝ) * Real.sqrt (μT T)) ^ 2 =
      ∑ T ∈ Ppos, (T.card : ℝ) ^ 2 * μT T :=
    Finset.sum_congr rfl fun T _ ↦ by rw [mul_pow, Real.sq_sqrt (hμ_nn T)]
  rw [hcs1, hcs2, hcs3, ← hE_sum, ← hU_sum, ← hEE_sum] at hcs
  have hS1_sq : S₁ ^ 2 ≤ (∑ x ∈ Q, (ℙ (E x)).toReal) ^ 2 :=
    pow_le_pow_left₀ hS1_pos.le h1 2
  have hmul : S₁ ^ 2 ≤ (ℙ (⋃ x ∈ Q, E x)).toReal * S₂ :=
    hS1_sq.trans (hcs.trans (mul_le_mul_of_nonneg_left h2 ENNReal.toReal_nonneg))
  exact (div_le_iff₀ hS2_pos).mpr hmul

lemma locShift_sh_le_maxLocalTime {Ω : Type} (X : ℕ → Ω → ℤ × ℤ)
    (ω : Ω) {t m n : ℕ} (htn : t + m ≤ n) (z : ℤ × ℤ) :
    locShift 0 (sh t (path X ω)) m z ≤ maxLocalTime X n ω := by
  have heq : ∀ j : ℕ, pos (sh t (path X ω)) j = z ↔ position X (t + j) ω = position X t ω + z := by
    intro j
    have hps := pos_shift (path X ω) t j
    change position X (t + j) ω = position X t ω + pos (sh t (path X ω)) j at hps
    constructor
    · intro h; rw [hps, h]
    · intro h; rw [hps] at h; exact add_left_cancel h
  have hcard : locShift 0 (sh t (path X ω)) m z ≤
      ((Finset.range (n + 1)).filter fun k ↦ position X k ω = position X t ω + z).card := by
    unfold locShift
    simp only [zero_add]
    refine Finset.card_le_card_of_injOn (fun j ↦ t + j) ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨by omega, (heq j).mp hj.2⟩
    · intro j₁ _ j₂ _ h
      exact add_left_cancel h
  exact hcard.trans (localTime_le_maxLocalTime X n ω (position X t ω + z))

lemma prob_block_repeat {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {L_blk : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det L_blk A) :
    ∀ K : ℕ, ℙ {ω | ∀ j < K, sh (j * L_blk) (path X ω) ∈ A} = (ℙ {ω | path X ω ∈ A}) ^ K ∧
      Det (K * L_blk) {y | ∀ j < K, sh (j * L_blk) y ∈ A}
  | 0 => by
    refine ⟨?_, fun _ _ _ _ j hj ↦ absurd hj (Nat.not_lt_zero j)⟩
    simp [measure_univ]
  | K + 1 => by
    have ih := prob_block_repeat hX hA K
    have hDet_succ : Det ((K + 1) * L_blk) {y | ∀ j < K + 1, sh (j * L_blk) y ∈ A} := by
      intro y y' h hy j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjK | hjK
      · exact ih.2 y y' (fun i hi ↦ h i (by nlinarith))
          (fun m hm ↦ hy m (Nat.lt_succ_of_lt hm)) j hjK
      · rw [hjK]
        refine hA _ _ (fun i hi ↦ ?_) (hy K (Nat.lt_succ_self K))
        exact h (K * L_blk + i) (by rw [Nat.succ_mul]; omega)
    refine ⟨?_, hDet_succ⟩
    have hset : {ω : Ω | ∀ j < K + 1, sh (j * L_blk) (path X ω) ∈ A} =
        {ω | path X ω ∈ {y | ∀ j < K, sh (j * L_blk) y ∈ A} ∧ sh (K * L_blk) (path X ω) ∈ A} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h; exact ⟨fun j hj ↦ h j (Nat.lt_succ_of_lt hj), h K (Nat.lt_succ_self K)⟩
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjK | hjK
        · exact h1 j hjK
        · rw [hjK]; exact h2
    have ih1 : ℙ {ω | path X ω ∈ {y | ∀ j < K, sh (j * L_blk) y ∈ A}} =
        (ℙ {ω | path X ω ∈ A}) ^ K := ih.1
    rw [hset, prob_block hX ih.2 hA, ih1, pow_succ]

lemma prob_all_blocks_fail {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M K T : ℕ} {B_blk : Set (ℕ → ℤ × ℤ)} (hB : Det (2 * M) B_blk)
    (hB_hit : ∀ y ∈ B_blk, ∃ z : ℤ × ℤ, T ≤ locShift 0 y (2 * M) z) :
    (ℙ {ω | maxLocalTime X (K * (2 * M)) ω < T}).toReal ≤
      Real.exp (-((K : ℝ) * (ℙ {ω | path X ω ∈ B_blk}).toReal)) := by
  have hBc : Det (2 * M) B_blkᶜ := fun y y' h hny hy ↦
    hny (hB y' y (fun i hi ↦ (h i hi).symm) hy)
  have hsub : {ω : Ω | maxLocalTime X (K * (2 * M)) ω < T} ⊆
      {ω | ∀ j < K, sh (j * (2 * M)) (path X ω) ∈ B_blkᶜ} := by
    intro ω hω j hj hmem
    obtain ⟨z, hz⟩ := hB_hit _ hmem
    have hle : j * (2 * M) + 2 * M ≤ K * (2 * M) := by
      have : j + 1 ≤ K := hj
      nlinarith
    have hmax := locShift_sh_le_maxLocalTime X ω hle z
    have : (T : ℕ) ≤ maxLocalTime X (K * (2 * M)) ω := hz.trans hmax
    exact absurd this (not_le_of_gt hω)
  have hrep := (prob_block_repeat hX hBc K).1
  have hm_le := ENNReal.toReal_mono (ENNReal.pow_ne_top (measure_ne_top ℙ _))
    ((measure_mono hsub).trans hrep.le)
  rw [ENNReal.toReal_pow] at hm_le
  have hcompl : {ω : Ω | path X ω ∈ B_blkᶜ} = ({ω : Ω | path X ω ∈ B_blk})ᶜ := rfl
  have hmeas : MeasurableSet {ω : Ω | path X ω ∈ B_blk} := by
    rw [path_eq]; exact det_meas hX hB 0
  rw [hcompl, prob_compl_eq_one_sub hmeas, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one] at hm_le
  set p : ℝ := (ℙ {ω | path X ω ∈ B_blk}).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    simpa [p] using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one : ℙ {ω | path X ω ∈ B_blk} ≤ 1)
  have hexp : (1 - p) ^ K ≤ Real.exp (-((K : ℝ) * p)) := by
    calc (1 - p) ^ K ≤ (Real.exp (-p)) ^ K :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) K
      _ = Real.exp (-((K : ℝ) * p)) := by rw [← Real.exp_nat_mul]; ring_nf
  exact hm_le.trans hexp

/-- Algebraic gap for Part A (perimeter truncation) exponent. -/
lemma partA_limit_margin {a η_lo : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hη0 : 0 < η_lo) (_hη1 : η_lo ≤ 1) :
    let s := 1 + (1 - a) / 8
    let b := a * s ^ 2
    let ρ := (s ^ 2 - 1) / 2
    let m := ρ * η_lo * (b - a * (1 + ρ)) / (1 + ρ) ^ 2
    let c₁ := 4 * (a + b) * (1 + ρ) ^ 2 / (ρ * η_lo * (b - a * (1 + ρ)))
    0 < ρ ∧ 0 < m ∧ 0 < c₁ ∧
      ∀ γ : ℝ, η_lo ≤ γ → γ ≤ 1 →
        a + 3 * m / 4 ≤
          a * c₁ / (1 + c₁ * (1 + ρ * γ)) + b * γ ^ 2 * (ρ * c₁) / (1 + (1 + ρ) * γ * c₁) := by
  intro s b ρ m c₁
  have hs1 : 1 < s := by dsimp [s]; linarith only [ha1]
  have hs2 : 1 < s ^ 2 := by nlinarith only [hs1]
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith only [hs2]
  have hba : b - a * (1 + ρ) = a * (s ^ 2 - 1) / 2 := by dsimp [b, ρ]; ring
  have hba0 : 0 < b - a * (1 + ρ) := by rw [hba]; exact div_pos (mul_pos ha0 (by linarith only [hs2])) two_pos
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hc10 : 0 < c₁ := by dsimp [c₁]; positivity
  refine ⟨hρ0, hm0, hc10, fun γ hγlo hγhi ↦ ?_⟩
  have hγ0 : 0 < γ := lt_of_lt_of_le hη0 hγlo
  have h1ρ : 1 + ρ * γ ≤ 1 + ρ := by
    have : ρ * γ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hγhi hρ0.le
    linarith only [this]
  have h1ρ_pos : 0 < 1 + ρ * γ := by positivity
  have hd1_pos : 0 < 1 + c₁ * (1 + ρ * γ) := by positivity
  have hd2_pos : 0 < 1 + (1 + ρ) * γ * c₁ := by positivity
  have hterm1 : a / (1 + ρ * γ) - a / c₁ ≤ a * c₁ / (1 + c₁ * (1 + ρ * γ)) := by
    have hdiff : a / (1 + ρ * γ) - a * c₁ / (1 + c₁ * (1 + ρ * γ)) =
        a / ((1 + ρ * γ) * (1 + c₁ * (1 + ρ * γ))) := by
      field_simp [h1ρ_pos.ne', hd1_pos.ne']; ring
    have hden : c₁ ≤ (1 + ρ * γ) * (1 + c₁ * (1 + ρ * γ)) := by
      have h1 : 1 ≤ 1 + ρ * γ := by nlinarith only [hρ0, hγ0]
      have h2 : c₁ ≤ (1 + ρ * γ) * c₁ := le_mul_of_one_le_left hc10.le h1
      have h3 : c₁ * 1 ≤ c₁ * (1 + ρ * γ) := mul_le_mul_of_nonneg_left h1 hc10.le
      calc c₁ ≤ (1 + ρ * γ) * c₁ := h2
        _ ≤ (1 + ρ * γ) * (1 + c₁ * (1 + ρ * γ)) :=
            mul_le_mul_of_nonneg_left (by linarith only [h3]) (by linarith only [h1])
    have hle : a / ((1 + ρ * γ) * (1 + c₁ * (1 + ρ * γ))) ≤ a / c₁ :=
      div_le_div_of_nonneg_left ha0.le hc10 hden
    linarith only [hdiff, hle]
  have hterm2 : b * γ * ρ / (1 + ρ) - b / c₁ ≤
      b * γ ^ 2 * (ρ * c₁) / (1 + (1 + ρ) * γ * c₁) := by
    have hdiff : b * γ * ρ / (1 + ρ) - b * γ ^ 2 * (ρ * c₁) / (1 + (1 + ρ) * γ * c₁) =
        b * (γ * ρ) / ((1 + ρ) * (1 + (1 + ρ) * γ * c₁)) := by
      field_simp [hd2_pos.ne']; ring
    have hden : (γ * ρ) * c₁ ≤ (1 + ρ) * (1 + (1 + ρ) * γ * c₁) := by
      have hρle : ρ ≤ (1 + ρ) ^ 2 := by nlinarith only [hρ0]
      calc (γ * ρ) * c₁ = γ * c₁ * ρ := by ring
        _ ≤ γ * c₁ * (1 + ρ) ^ 2 := mul_le_mul_of_nonneg_left hρle (by positivity)
        _ = (1 + ρ) * ((1 + ρ) * γ * c₁) := by ring
        _ ≤ (1 + ρ) * (1 + (1 + ρ) * γ * c₁) := by nlinarith only [hρ0]
    have hle : b * (γ * ρ) / ((1 + ρ) * (1 + (1 + ρ) * γ * c₁)) ≤ b / c₁ := by
      rw [div_le_div_iff₀ (by positivity) hc10]
      calc b * (γ * ρ) * c₁ = b * (γ * ρ * c₁) := by ring
        _ ≤ b * ((1 + ρ) * (1 + (1 + ρ) * γ * c₁)) := mul_le_mul_of_nonneg_left hden hb0.le
    linarith only [hdiff, hle]
  have hlim : a + m ≤ a / (1 + ρ * γ) + b * γ * ρ / (1 + ρ) := by
    have h_eq : a / (1 + ρ * γ) + b * γ * ρ / (1 + ρ) - a =
        ρ * γ * (b * (1 + ρ * γ) - a * (1 + ρ)) / ((1 + ρ * γ) * (1 + ρ)) := by
      field_simp [h1ρ_pos.ne']; ring
    have h11 : 1 ≤ 1 + ρ * γ := by nlinarith only [hρ0, hγ0]
    have h12 : b ≤ b * (1 + ρ * γ) := le_mul_of_one_le_right hb0.le h11
    have h1 : b - a * (1 + ρ) ≤ b * (1 + ρ * γ) - a * (1 + ρ) := by linarith only [h12]
    have hnum : ρ * η_lo * (b - a * (1 + ρ)) ≤ ρ * γ * (b * (1 + ρ * γ) - a * (1 + ρ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hγlo hρ0.le) h1 hba0.le (by positivity)
    have hden : (1 + ρ * γ) * (1 + ρ) ≤ (1 + ρ) ^ 2 := by nlinarith only [h1ρ, hρ0]
    have hnum_nn : 0 ≤ ρ * γ * (b * (1 + ρ * γ) - a * (1 + ρ)) :=
      mul_nonneg (mul_nonneg hρ0.le hγ0.le) (by linarith only [h1, hba0])
    have hdiv : m ≤ ρ * γ * (b * (1 + ρ * γ) - a * (1 + ρ)) / ((1 + ρ * γ) * (1 + ρ)) := by
      dsimp [m]
      exact div_le_div₀ hnum_nn hnum (by positivity) hden
    linarith only [h_eq, hdiv]
  have hcb : (a + b) / c₁ = m / 4 := by
    dsimp [c₁, m]; field_simp [hρ0.ne', hη0.ne', hba0.ne']
  rw [add_div] at hcb
  linarith only [hterm1, hterm2, hlim, hcb]

/-- Algebraic gap for Part B 3-point Chernoff exponent. -/
lemma partB_good_limit_margin {a η_lo : ℝ} (ha78 : 7 / 8 ≤ a) (ha1 : a < 1)
    (hη0 : 0 < η_lo) :
    let t := (1 - a) / 8
    let s := 1 + t
    let b := a * s ^ 2
    let η_up := (1 - a) / 2
    let m := a * t ^ 2 * η_lo
    let c₁ := 16 / (η_up ^ 2 * m)
    0 < t ∧ 0 < η_up ∧ 0 < m ∧ 0 < c₁ ∧
      ∀ γ : ℝ, η_lo ≤ γ → γ ≤ 1 - η_up →
        let u := s * (1 - γ) / (1 - s * γ)
        let ρ := 2 - u
        0 < ρ ∧ ρ < 2 ∧ η_up ≤ u ∧ u ≤ 2 ∧
          (2 * a - γ) + m / 2 ≤
            2 * a * c₁ / (1 + c₁ * (1 + γ - ρ * γ)) - b * γ ^ 2 * (ρ * c₁) / (1 + (2 - ρ) * c₁ * γ) := by
  intro t s b η_up m c₁
  have ht0 : 0 < t := by dsimp [t]; linarith only [ha1]
  have ht_le : t ≤ 1 / 64 := by dsimp [t]; linarith only [ha78]
  have hηup0 : 0 < η_up := by dsimp [η_up]; linarith only [ha1]
  have hηup_eq : η_up = 4 * t := by dsimp [η_up, t]; ring
  have ha0 : 0 < a := by linarith only [ha78]
  have hs1 : 1 < s := by dsimp [s]; linarith only [ht0]
  have hs2 : s ≤ 2 := by dsimp [s]; linarith only [ht_le]
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hc10 : 0 < c₁ := by dsimp [c₁]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨ht0, hηup0, hm0, hc10, fun γ hγlo hγhi ↦ ?_⟩
  intro u ρ
  have hγ0 : 0 < γ := lt_of_lt_of_le hη0 hγlo
  have hγ_le1 : γ ≤ 1 := by linarith only [hγhi, hηup0]
  have hden_ge : 3 * t ≤ 1 - s * γ := by
    have : s * γ ≤ (1 + t) * (1 - 4 * t) := by
      have h1 : γ ≤ 1 - 4 * t := by linarith only [hγhi, hηup_eq]
      exact mul_le_mul_of_nonneg_left h1 (by linarith only [ht0])
    dsimp [s] at this ⊢
    nlinarith only [this, ht0]
  have hden_pos : 0 < 1 - s * γ := by linarith only [hden_ge, ht0]
  have hden_le1 : 1 - s * γ ≤ 1 := by linarith only [mul_nonneg (by linarith only [ht0] : 0 ≤ s) hγ0.le]
  have hu_ge : η_up ≤ u := by
    dsimp [u]
    rw [le_div_iff₀ hden_pos]
    have h1 : η_up * (1 - s * γ) ≤ η_up := mul_le_of_le_one_right hηup0.le hden_le1
    have h2 : η_up ≤ s * (1 - γ) := by
      have : η_up ≤ 1 - γ := by linarith only [hγhi]
      nlinarith only [this, hs1, hηup0]
    linarith only [h1, h2]
  have hu_le2 : u ≤ 2 := by
    dsimp [u]
    rw [div_le_iff₀ hden_pos]
    have h1 : γ ≤ 1 - 4 * t := by linarith only [hγhi, hηup_eq]
    dsimp [s]
    nlinarith only [h1, ht0, hγ0]
  have hu_lt2 : u < 2 := by
    dsimp [u]
    rw [div_lt_iff₀ hden_pos]
    have h1 : γ ≤ 1 - 4 * t := by linarith only [hγhi, hηup_eq]
    dsimp [s]
    nlinarith only [h1, ht0, hγ0]
  have hu0 : 0 < u := lt_of_lt_of_le hηup0 hu_ge
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith only [hu_lt2]
  have hρ2 : ρ < 2 := by dsimp [ρ]; linarith only [hu0]
  have h2mρ : 2 - ρ = u := by dsimp [ρ]; ring
  have hus : 1 + γ - ρ * γ = u / s := by
    have h1 : 1 + γ - ρ * γ = 1 - γ + u * γ := by dsimp [ρ]; ring
    have hds : 1 - γ * s ≠ 0 := by
      have : 0 < 1 - γ * s := by linarith only [hden_pos, show γ * s = s * γ by ring]
      exact this.ne'
    rw [h1]
    dsimp [u]
    field_simp [hden_pos.ne', hds, (by linarith only [hs1] : s ≠ 0)]
    ring
  have hlim_gap : 2 * a - γ + m ≤ 2 * a * s / u - b * γ * ρ / u := by
    have hlin : 2 * a * t ^ 2 ≤ (1 - a - 2 * a * t + a * t ^ 2) + γ * (a * s ^ 2 - 1) := by
      have hf0 : 2 * a * t ^ 2 ≤ 1 - a - 2 * a * t + a * t ^ 2 := by
        have h1 : a * t ^ 2 ≤ t := by nlinarith only [ha1, ht0, ht_le]
        have h2 : 1 - a = 8 * t := by dsimp [t]; ring
        nlinarith only [h1, h2, ha1, ha0, ht0]
      have hf1 : 1 - a - 2 * a * t + a * t ^ 2 + (a * s ^ 2 - 1) = 2 * a * t ^ 2 := by
        dsimp [s]; ring
      have hconv : (1 - a - 2 * a * t + a * t ^ 2) + γ * (a * s ^ 2 - 1) =
          (1 - γ) * (1 - a - 2 * a * t + a * t ^ 2) +
            γ * ((1 - a - 2 * a * t + a * t ^ 2) + (a * s ^ 2 - 1)) := by ring
      rw [hconv, hf1]
      nlinarith only [hf0, hγ_le1, hγ0]
    have h_alg : 2 * a * s / u - b * γ * ρ / u - (2 * a - γ) =
        γ * s * ((1 - a - 2 * a * t + a * t ^ 2) + γ * (a * s ^ 2 - 1)) / (u * (1 - s * γ)) := by
      have hρ_eq : ρ = 2 - u := rfl
      have hu_mul : u * (1 - s * γ) = s * (1 - γ) := by
        dsimp [u]; field_simp [hden_pos.ne']
      rw [hρ_eq]
      field_simp [hu0.ne', hden_pos.ne']
      calc (2 * a * s - b * γ * (2 - u) - u * (2 * a - γ)) * (1 - s * γ)
          = 2 * a * s * (1 - s * γ) - b * γ * (2 * (1 - s * γ) - u * (1 - s * γ)) -
              (u * (1 - s * γ)) * (2 * a - γ) := by ring
        _ = 2 * a * s * (1 - s * γ) - b * γ * (2 * (1 - s * γ) - s * (1 - γ)) -
              (s * (1 - γ)) * (2 * a - γ) := by rw [hu_mul]
        _ = s * γ * (1 - a - 2 * a * t + a * t ^ 2 + γ * (a * s ^ 2 - 1)) := by
            dsimp [b, s]; ring
    have hden_ub : u * (1 - s * γ) ≤ 2 := by nlinarith only [hu_le2, hden_le1, hden_pos]
    have hlin_nn : 0 ≤ (1 - a - 2 * a * t + a * t ^ 2) + γ * (a * s ^ 2 - 1) := by
      have h0 : 0 ≤ 2 * a * t ^ 2 := by positivity
      linarith only [h0, hlin]
    have hnum_lb : 2 * a * t ^ 2 * γ ≤
        γ * s * ((1 - a - 2 * a * t + a * t ^ 2) + γ * (a * s ^ 2 - 1)) := by
      have h1 : 2 * a * t ^ 2 ≤ s * ((1 - a - 2 * a * t + a * t ^ 2) + γ * (a * s ^ 2 - 1)) :=
        hlin.trans (le_mul_of_one_le_left hlin_nn hs1.le)
      calc 2 * a * t ^ 2 * γ = γ * (2 * a * t ^ 2) := by ring
        _ ≤ γ * (s * ((1 - a - 2 * a * t + a * t ^ 2) + γ * (a * s ^ 2 - 1))) :=
            mul_le_mul_of_nonneg_left h1 hγ0.le
        _ = _ := by ring
    have hdiv : m ≤ γ * s * ((1 - a - 2 * a * t + a * t ^ 2) + γ * (a * s ^ 2 - 1)) /
        (u * (1 - s * γ)) := by
      have hnum_nn : 0 ≤ 2 * a * t ^ 2 * γ := by positivity
      calc m = (2 * a * t ^ 2 * η_lo) / 2 := by dsimp [m]; ring
        _ ≤ (2 * a * t ^ 2 * γ) / 2 := by gcongr
        _ ≤ (γ * s * ((1 - a - 2 * a * t + a * t ^ 2) + γ * (a * s ^ 2 - 1))) /
              (u * (1 - s * γ)) :=
            div_le_div₀ (mul_nonneg (mul_nonneg hγ0.le (by linarith only [hs1])) hlin_nn)
              hnum_lb (mul_pos hu0 hden_pos) hden_ub
    linarith only [h_alg, hdiv]
  have hterm1 : 2 * a * s / u - m / 2 ≤ 2 * a * c₁ / (1 + c₁ * (u / s)) := by
    have hus_pos : 0 < u / s := div_pos hu0 (by linarith only [hs1])
    have hd1_pos : 0 < 1 + c₁ * (u / s) := by positivity
    have hdiff : 2 * a * s / u - 2 * a * c₁ / (1 + c₁ * (u / s)) =
        2 * a / ((u / s) * (1 + c₁ * (u / s))) := by
      field_simp [hu0.ne', (by linarith only [hs1] : s ≠ 0), hd1_pos.ne']; ring
    have hus_lb : η_up / 2 ≤ u / s :=
      (div_le_div_of_nonneg_right hu_ge zero_le_two).trans
        (div_le_div_of_nonneg_left hu0.le (by linarith only [hs1]) hs2)
    have hden_lb : c₁ * (η_up ^ 2 / 4) ≤ (u / s) * (1 + c₁ * (u / s)) := by
      have h1 : (η_up / 2) ^ 2 * c₁ ≤ (u / s) ^ 2 * c₁ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hus_lb 2) hc10.le
      nlinarith only [h1, hus_pos]
    have herr : 2 * a / ((u / s) * (1 + c₁ * (u / s))) ≤ m / 2 := by
      calc 2 * a / ((u / s) * (1 + c₁ * (u / s)))
          ≤ 2 / (c₁ * (η_up ^ 2 / 4)) := by
            refine div_le_div₀ zero_le_two (by linarith only [ha1]) (by positivity) hden_lb
        _ = m / 2 := by dsimp [c₁]; field_simp [hηup0.ne', hm0.ne']; ring
    linarith only [hdiff, herr]
  have hterm2 : b * γ ^ 2 * (ρ * c₁) / (1 + u * c₁ * γ) ≤ b * γ * ρ / u := by
    have h1 : b * γ ^ 2 * (ρ * c₁) / (1 + u * c₁ * γ) ≤ b * γ ^ 2 * (ρ * c₁) / (u * c₁ * γ) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only)
    have h2 : b * γ ^ 2 * (ρ * c₁) / (u * c₁ * γ) = b * γ * ρ / u := by
      field_simp [hu0.ne', hc10.ne', hγ0.ne']
    linarith only [h1, h2]
  rw [hus, h2mρ]
  exact ⟨hρ0, hρ2, hu_ge, hu_le2, by linarith only [hlim_gap, hterm1, hterm2]⟩

lemma dyadic_scale_exists {d : ℕ} (hd : 1 ≤ d) :
    ∃ j : ℕ, d ≤ 2 ^ j ∧ 2 ^ j < 2 * d := by
  refine ⟨Nat.clog 2 d, Nat.le_pow_clog (by decide) d, ?_⟩
  rcases Nat.eq_or_lt_of_le hd with rfl | hd1
  · norm_num
  · have hc0 : 0 < Nat.clog 2 d := Nat.clog_pos (by decide) hd1
    have hpred : 2 ^ (Nat.clog 2 d - 1) < d :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp (Nat.sub_lt hc0 one_pos)
    calc 2 ^ Nat.clog 2 d = 2 * 2 ^ (Nat.clog 2 d - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hc0]
      _ < 2 * d := Nat.mul_lt_mul_of_pos_left hpred two_pos

lemma dyadic_pairs_card_le {Rmax R : ℕ} (hR : 1 ≤ R) :
    ((Q0 Rmax ×ˢ Q0 Rmax).filter fun pq ↦ rnorm (pq.1 - pq.2) ≤ R).card ≤ 9 * Rmax ^ 2 * R ^ 2 := by
  let box : ℤ × ℤ → Finset (ℤ × ℤ) := fun p ↦
    Finset.Icc (p.1 - (R : ℤ)) (p.1 + (R : ℤ)) ×ˢ Finset.Icc (p.2 - (R : ℤ)) (p.2 + (R : ℤ))
  have hsub : ((Q0 Rmax ×ˢ Q0 Rmax).filter fun pq ↦ rnorm (pq.1 - pq.2) ≤ R) ⊆
      (Q0 Rmax).biUnion fun p ↦ (box p).map ⟨fun q ↦ (p, q), fun _ _ h ↦ (Prod.ext_iff.mp h).2⟩ := by
    rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_map] at hpq ⊢
    refine ⟨p, hpq.1.1, q, ?_, rfl⟩
    have hr := hpq.2
    simp only [rnorm, Prod.fst_sub, Prod.snd_sub] at hr
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_, Finset.mem_Icc.mpr ?_⟩ <;> omega
  have hbox_card : ∀ p : ℤ × ℤ, (box p).card ≤ 9 * R ^ 2 := fun p ↦ by
    dsimp [box]
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    have h1 : (p.1 + (R : ℤ) + 1 - (p.1 - (R : ℤ))).toNat = 2 * R + 1 := by omega
    have h2 : (p.2 + (R : ℤ) + 1 - (p.2 - (R : ℤ))).toNat = 2 * R + 1 := by omega
    rw [h1, h2]
    nlinarith
  calc ((Q0 Rmax ×ˢ Q0 Rmax).filter fun pq ↦ rnorm (pq.1 - pq.2) ≤ R).card
      ≤ ((Q0 Rmax).biUnion fun p ↦
          (box p).map ⟨fun q ↦ (p, q), fun _ _ h ↦ (Prod.ext_iff.mp h).2⟩).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Q0 Rmax, ((box p).map ⟨fun q ↦ (p, q), fun _ _ h ↦ (Prod.ext_iff.mp h).2⟩).card :=
        Finset.card_biUnion_le
    _ = ∑ p ∈ Q0 Rmax, (box p).card := Finset.sum_congr rfl fun _ _ ↦ Finset.card_map _
    _ ≤ ∑ _ ∈ Q0 Rmax, 9 * R ^ 2 := Finset.sum_le_sum fun p _ ↦ hbox_card p
    _ = (Q0 Rmax).card * (9 * R ^ 2) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Rmax ^ 2 * (9 * R ^ 2) := by
        refine Nat.mul_le_mul_right _ ?_
        unfold Q0
        rw [Finset.card_product, Int.card_Icc]
        rcases eq_or_ne Rmax 0 with rfl | h0
        · simp
        · have h1 : ((Rmax : ℤ) - 1 + 1 - 0).toNat = Rmax := by omega
          rw [h1, sq]
    _ = 9 * Rmax ^ 2 * R ^ 2 := by ring

noncomputable def goodScales (M : ℕ) (η_lo η_up : ℝ) : Finset ℕ :=
  by classical
  exact (Finset.range (Nat.log 2 (M + 1) + 1)).filter fun j ↦
    let R : ℕ := 2 ^ j
    let M₁ : ℝ := (M : ℝ) + 1
    let γ : ℝ := Real.log (M₁ / (R : ℝ) ^ 2) / Real.log M₁
    (3 * R) ^ 2 ≤ M + 1 ∧ η_lo ≤ γ ∧ γ ≤ 1 - η_up

noncomputable def perimCap (M R : ℕ) (b : ℝ) : ℝ :=
  let M₁ : ℝ := (M : ℝ) + 1
  let L : ℝ := Real.log M₁ / Real.pi
  let γ : ℝ := Real.log (M₁ / (R : ℝ) ^ 2) / Real.log M₁
  (R : ℝ) * (b * γ ^ 2 * L * Real.log M₁)

noncomputable def goodEvent (M T : ℕ) (b η_lo η_up : ℝ) (p : ℤ × ℤ) : Set (ℕ → ℤ × ℤ) :=
  {y | T ≤ locShift 0 y M (rot p) ∧
    ∀ j ∈ goodScales M η_lo η_up, ∀ σ ∈ ({1, -1} : Finset ℤ),
      ∑ z ∈ Prot p (2 ^ j) σ, (locShift 0 y (2 * M) z : ℝ) ≤ perimCap M (2 ^ j) b}

lemma det_goodEvent (M T : ℕ) (b η_lo η_up : ℝ) (p : ℤ × ℤ) :
    Det (2 * M) (goodEvent M T b η_lo η_up p) := by
  intro y y' h hy
  refine ⟨?_, ?_⟩
  · have h' : ∀ i < M, y i = y' i := fun i hi ↦ h i (by omega)
    rw [← det_locShift M (rot p) y y' h']
    exact hy.1
  · intro j hj σ hσ
    have hsum : ∑ z ∈ Prot p (2 ^ j) σ, (locShift 0 y' (2 * M) z : ℝ) =
        ∑ z ∈ Prot p (2 ^ j) σ, (locShift 0 y (2 * M) z : ℝ) :=
      Finset.sum_congr rfl fun z _ ↦ by rw [det_locShift (2 * M) z y y' h]
    rw [hsum]
    exact hy.2 j hj σ hσ

lemma goodEvent_meas {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (M T : ℕ) (b η_lo η_up : ℝ) (p : ℤ × ℤ) :
    MeasurableSet {ω | path X ω ∈ goodEvent M T b η_lo η_up p} := by
  rw [path_eq]
  exact det_meas hX (det_goodEvent M T b η_lo η_up p) 0

/-- Lower bound on single-site visit probability using Section 4 renewal identity. -/
lemma prob_hit_single_ge {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M M₀ Rmax T : ℕ} {a η_1 : ℝ}
    (hM : 100 ≤ M) (ha0 : 7 / 8 ≤ a) (ha1 : a < 1) (hη0 : 0 < η_1) (hη1 : η_1 ≤ 1 / 4)
    (hT_eq : T = Nat.ceil (a * Real.log ((M : ℝ) + 1) ^ 2 / Real.pi))
    (hM0_ge : (M : ℝ) / (8 * Real.log ((M : ℝ) + 1)) ≤ (M₀ : ℝ))
    (hM0_le : (M₀ : ℝ) ≤ (M : ℝ) / (4 * Real.log ((M : ℝ) + 1)))
    (hM0_val : 200 ≤ M₀)
    (hRmax : (Rmax : ℝ) ≤ Real.sqrt (M₀ : ℝ) / 1024)
    (hlog_big : Real.log (8 * Real.log ((M : ℝ) + 1)) + 3 * Real.pi ≤ η_1 * Real.log ((M : ℝ) + 1))
    {p : ℤ × ℤ} (hp : p ∈ Q0 Rmax) :
    (1 / (4 * Real.log ((M : ℝ) + 1))) * Real.exp (-(a + 2 * η_1) * Real.log ((M : ℝ) + 1)) ≤
      (ℙ {ω | T ≤ locShift 0 (path X ω) M (rot p)}).toReal := by
  set M₁ : ℝ := (M : ℝ) + 1
  set L1 : ℝ := Real.log M₁
  have hpi := Real.pi_pos
  have hM1_ge : (101 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 101 ≤ M + 1)
  have hL1_ge : 4 ≤ L1 := by
    dsimp [L1]
    have hexp : Real.exp 4 ≤ 101 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 4
        _ ≤ 101 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith only [hM1_ge])).mpr (hexp.trans hM1_ge)
  have hL1_pos : 0 < L1 := by linarith only [hL1_ge]
  have hM0_pos : (0 : ℝ) < M₀ := by exact_mod_cast (by omega : 0 < M₀)
  have hs0 : 0 ≤ 1 - 1 / (M₀ : ℝ) := by
    rw [sub_nonneg, div_le_one hM0_pos]; exact_mod_cast (by omega : 1 ≤ M₀)
  have hs1 : 1 - 1 / (M₀ : ℝ) < 1 := by linarith only [one_div_pos.mpr hM0_pos]
  have hv1_pos : 1 ≤ a * L1 ^ 2 / Real.pi := by
    have h1 : (7 / 8 : ℝ) * 16 ≤ a * L1 ^ 2 := by nlinarith only [ha0, hL1_ge]
    rw [le_div_iff₀ hpi]
    linarith only [h1, Real.pi_lt_four]
  have hT_ge1 : 1 ≤ T := by
    rw [hT_eq]
    exact Nat.one_le_cast.mp ((le_trans (by norm_num) hv1_pos).trans (Nat.le_ceil _))
  have hT_lt : (T : ℝ) < a * L1 ^ 2 / Real.pi + 1 := by
    rw [hT_eq]; exact Nat.ceil_lt_add_one (by linarith only [hv1_pos])
  have hTm1 : ((T - 1 : ℕ) : ℝ) ≤ a * L1 ^ 2 / Real.pi := by
    rw [Nat.cast_sub hT_ge1, Nat.cast_one]; linarith only [hT_lt]
  have h_gen := prob_locShift_ge_of_genHit hX hs0 hs1 hT_ge1 (rot p) M
  set G : ℝ := green X (1 - 1 / (M₀ : ℝ)) 0
  have hG_lo : Real.log (M₀ : ℝ) / Real.pi - 1 ≤ G := green_zero_ge hX (by omega : 2 ≤ M₀)
  have hG_hi : G ≤ Real.log (M₀ : ℝ) / Real.pi + 2 := green_zero_le hX (by omega : 2 ≤ M₀)
  have hG_le_L1 : G ≤ L1 := by
    have hM0_lt_M : (M₀ : ℝ) ≤ M₁ := by
      have h1 : (M : ℝ) / (4 * L1) ≤ (M : ℝ) := div_le_self (by positivity) (by linarith only [hL1_ge])
      have h2 : (M : ℝ) ≤ M₁ := by dsimp [M₁]; linarith only
      exact hM0_le.trans (h1.trans h2)
    have hlog_le : Real.log (M₀ : ℝ) ≤ L1 := Real.log_le_log hM0_pos hM0_lt_M
    have hdiv_le : Real.log (M₀ : ℝ) / Real.pi ≤ L1 / 3 :=
      (div_le_div_of_nonneg_right hlog_le hpi.le).trans
        (div_le_div_of_nonneg_left hL1_pos.le (by norm_num) Real.pi_gt_three.le)
    linarith only [hG_hi, hdiv_le, hL1_ge]
  have hG_pos : 0 < G := by
    have hlog5 : (5 : ℝ) ≤ Real.log (M₀ : ℝ) := by
      have hexp : Real.exp 5 ≤ 200 := by
        have := Real.exp_one_lt_d9
        calc Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.7182818286 ^ 5 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 5
          _ ≤ 200 := by norm_num
      have hM0_200 : (200 : ℝ) ≤ M₀ := by exact_mod_cast hM0_val
      exact (Real.le_log_iff_exp_le hM0_pos).mpr (hexp.trans hM0_200)
    have h5_div : 5 / Real.pi - 1 ≤ Real.log (M₀ : ℝ) / Real.pi - 1 := by
      have : 5 / Real.pi ≤ Real.log (M₀ : ℝ) / Real.pi := div_le_div_of_nonneg_right hlog5 hpi.le
      linarith only [this]
    have h14 : 1 / 4 ≤ 5 / Real.pi - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ hpi]; linarith only [Real.pi_lt_four]
    linarith only [hG_lo, h5_div, h14]
  have hratio : 1 / L1 ≤ green X (1 - 1 / (M₀ : ℝ)) (rot p) / G := by
    by_cases hp0 : p = 0
    · subst hp0
      rw [rot_zero, div_self hG_pos.ne']
      rw [div_le_one hL1_pos]
      linarith only [hL1_ge]
    · have hp1 : 1 ≤ rnorm p := Nat.pos_of_ne_zero fun h0 ↦ hp0 ((rnorm_eq_zero_iff p).mp h0)
      have hge := green_rot_ge hX (by omega : 2 ≤ M₀) p hp1
      have hr_lt : rnorm p < Rmax := mem_Q0_rnorm hp
      have hdiv_ge : (1024 : ℝ) ^ 2 ≤ (M₀ : ℝ) / (rnorm p : ℝ) ^ 2 := by
        have hR_pos : (0 : ℝ) < Rmax := by exact_mod_cast (by omega : 0 < Rmax)
        have hr2 : (rnorm p : ℝ) ^ 2 ≤ (Rmax : ℝ) ^ 2 := by
          exact_mod_cast (by nlinarith : rnorm p ^ 2 ≤ Rmax ^ 2)
        have hR2 : (Rmax : ℝ) ^ 2 ≤ (M₀ : ℝ) / 1024 ^ 2 := by
          calc (Rmax : ℝ) ^ 2 ≤ (Real.sqrt (M₀ : ℝ) / 1024) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hRmax 2
            _ = (M₀ : ℝ) / 1024 ^ 2 := by rw [div_pow, Real.sq_sqrt hM0_pos.le]
        have hr_pos : (0 : ℝ) < rnorm p := by exact_mod_cast hp1
        calc (1024 : ℝ) ^ 2 ≤ (M₀ : ℝ) / (Rmax : ℝ) ^ 2 := by
              rw [le_div_iff₀ (sq_pos_of_pos hR_pos)]
              rw [le_div_iff₀ (by positivity)] at hR2
              linarith only [hR2]
          _ ≤ (M₀ : ℝ) / (rnorm p : ℝ) ^ 2 := div_le_div_of_nonneg_left hM0_pos.le (by positivity) hr2
      have hlog_ge : 13 ≤ Real.log ((M₀ : ℝ) / (rnorm p : ℝ) ^ 2) := by
        have hexp : Real.exp 13 ≤ 1024 ^ 2 := by
          have := Real.exp_one_lt_d9
          calc Real.exp 13 = Real.exp 1 ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
            _ ≤ 2.7182818286 ^ 13 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 13
            _ ≤ 1024 ^ 2 := by norm_num
        exact (Real.le_log_iff_exp_le (by positivity)).mpr (hexp.trans hdiv_ge)
      have hpi_d2 := Real.pi_lt_d2
      have h13 : 1 ≤ Real.log ((M₀ : ℝ) / (rnorm p : ℝ) ^ 2) / Real.pi - 3 := by
        rw [le_sub_iff_add_le, le_div_iff₀ hpi]
        linarith only [hlog_ge, hpi_d2]
      have hgp_ge1 : 1 ≤ green X (1 - 1 / (M₀ : ℝ)) (rot p) := by linarith only [hge, h13]
      calc 1 / L1 ≤ 1 / G := one_div_le_one_div_of_le hG_pos hG_le_L1
        _ ≤ green X (1 - 1 / (M₀ : ℝ)) (rot p) / G := div_le_div_of_nonneg_right hgp_ge1 hG_pos.le
  have hlogM0_lb : L1 - Real.log (8 * L1) - 1 ≤ Real.log (M₀ : ℝ) := by
    have hM_ge : M₁ / 2 ≤ (M : ℝ) := by
      have : (100 : ℝ) ≤ M := by exact_mod_cast hM
      dsimp [M₁]; linarith only [this]
    have hM0_lb2 : M₁ / (16 * L1) ≤ (M₀ : ℝ) := by
      calc M₁ / (16 * L1) = (M₁ / 2) / (8 * L1) := by ring
        _ ≤ (M : ℝ) / (8 * L1) := div_le_div_of_nonneg_right hM_ge (by positivity)
        _ ≤ (M₀ : ℝ) := hM0_ge
    have hlog1 : L1 - Real.log (16 * L1) ≤ Real.log (M₀ : ℝ) := by
      rw [← Real.log_div (by linarith only [hM1_ge]) (by positivity)]
      exact Real.log_le_log (by positivity) hM0_lb2
    have hlog2 : Real.log (16 * L1) = Real.log 2 + Real.log (8 * L1) := by
      rw [show (16 : ℝ) * L1 = 2 * (8 * L1) by ring, Real.log_mul (by norm_num) (by positivity)]
    linarith only [hlog1, hlog2, Real.log_two_lt_d9]
  have hGm1_ge : (1 - η_1) * L1 / Real.pi ≤ G - 1 := by
    have h1 : Real.log (M₀ : ℝ) / Real.pi - 2 ≤ G - 1 := by linarith only [hG_lo]
    have h2 : (1 - η_1) * L1 ≤ Real.log (M₀ : ℝ) - 2 * Real.pi := by
      linarith only [hlogM0_lb, hlog_big, Real.pi_gt_three]
    have h3 : (1 - η_1) * L1 / Real.pi ≤ (Real.log (M₀ : ℝ) - 2 * Real.pi) / Real.pi :=
      div_le_div_of_nonneg_right h2 hpi.le
    rw [sub_div, mul_div_cancel_right₀ _ hpi.ne'] at h3
    linarith only [h1, h3]
  have hGm1_pos : 0 < G - 1 := by
    have : 0 < (1 - η_1) * L1 / Real.pi := div_pos (mul_pos (by linarith only [hη1]) hL1_pos) hpi
    linarith only [this, hGm1_ge]
  have hret_pow : Real.exp (-(a + 2 * η_1) * L1) ≤ (1 - 1 / G) ^ (T - 1) := by
    have hbase : Real.exp (-((1 : ℝ) / (G - 1))) ≤ 1 - 1 / G := by
      have h1 : 1 - 1 / G = (1 + 1 / (G - 1))⁻¹ := by
        field_simp [hG_pos.ne', hGm1_pos.ne']; ring
      have h_exp := Real.add_one_le_exp (1 / (G - 1))
      rw [add_comm] at h_exp
      rw [h1, Real.exp_neg]
      exact inv_anti₀ (by positivity) h_exp
    have hpow : Real.exp (-(((T - 1 : ℕ) : ℝ) / (G - 1))) ≤ (1 - 1 / G) ^ (T - 1) := by
      calc Real.exp (-(((T - 1 : ℕ) : ℝ) / (G - 1)))
          = (Real.exp (-((1 : ℝ) / (G - 1)))) ^ (T - 1) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ (1 - 1 / G) ^ (T - 1) := pow_le_pow_left₀ (Real.exp_pos _).le hbase (T - 1)
    have hexp_le : ((T - 1 : ℕ) : ℝ) / (G - 1) ≤ (a + 2 * η_1) * L1 := by
      calc ((T - 1 : ℕ) : ℝ) / (G - 1)
          ≤ (a * L1 ^ 2 / Real.pi) / ((1 - η_1) * L1 / Real.pi) :=
            div_le_div₀ (by positivity) hTm1 (div_pos (mul_pos (by linarith only [hη1]) hL1_pos) hpi) hGm1_ge
        _ = (a / (1 - η_1)) * L1 := by field_simp [hL1_pos.ne', hpi.ne', (by linarith only [hη1] : 1 - η_1 ≠ 0)]
        _ ≤ (a + 2 * η_1) * L1 := by
            refine mul_le_mul_of_nonneg_right ?_ hL1_pos.le
            rw [div_le_iff₀ (by linarith only [hη1])]
            nlinarith only [ha1, hη0, hη1]
    exact (Real.exp_le_exp.mpr (by linarith only [hexp_le])).trans hpow
  have hmain_term : (1 / L1) * Real.exp (-(a + 2 * η_1) * L1) ≤
      (green X (1 - 1 / (M₀ : ℝ)) (rot p) / G) * (1 - 1 / G) ^ (T - 1) := by
    have hratio_nn : 0 ≤ green X (1 - 1 / (M₀ : ℝ)) (rot p) / G :=
      le_trans (by positivity) hratio
    exact mul_le_mul hratio hret_pow (Real.exp_pos _).le hratio_nn
  have htail_le : (1 - 1 / (M₀ : ℝ)) ^ (M + 1) ≤ (1 / (2 * L1)) * Real.exp (-(a + 2 * η_1) * L1) := by
    have h1m : 1 - 1 / (M₀ : ℝ) ≤ Real.exp (-(1 / (M₀ : ℝ))) := Real.one_sub_le_exp_neg _
    have hpow : (1 - 1 / (M₀ : ℝ)) ^ (M + 1) ≤ Real.exp (-((M₁) / (M₀ : ℝ))) := by
      calc (1 - 1 / (M₀ : ℝ)) ^ (M + 1) ≤ (Real.exp (-(1 / (M₀ : ℝ)))) ^ (M + 1) :=
            pow_le_pow_left₀ hs0 h1m (M + 1)
        _ = Real.exp (-((M₁) / (M₀ : ℝ))) := by
            rw [← Real.exp_nat_mul]; congr 1; dsimp [M₁]; push_cast; ring
    have h_ratio : 4 * L1 ≤ M₁ / (M₀ : ℝ) := by
      rw [le_div_iff₀ hM0_pos, mul_comm]
      have h1 : (M₀ : ℝ) * (4 * L1) ≤ M := (le_div_iff₀ (by positivity)).mp hM0_le
      have h2 : (M : ℝ) ≤ M₁ := by dsimp [M₁]; linarith only
      linarith only [h1, h2]
    have hexp_tail : Real.exp (-(M₁ / (M₀ : ℝ))) ≤ Real.exp (-(4 * L1)) :=
      Real.exp_le_exp.mpr (by linarith only [h_ratio])
    have hexp_2L1 : 2 * L1 ≤ Real.exp (2 * L1) := by linarith only [Real.add_one_le_exp (2 * L1)]
    have h4L1 : Real.exp (-(4 * L1)) ≤ (1 / (2 * L1)) * Real.exp (-(a + 2 * η_1) * L1) := by
      have hsplit : Real.exp (-(4 * L1)) = Real.exp (-(2 * L1)) * Real.exp (-(2 * L1)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hinv : Real.exp (-(2 * L1)) ≤ 1 / (2 * L1) := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (by positivity) hexp_2L1
      have ha_le2 : a + 2 * η_1 ≤ 2 := by linarith only [ha1, hη1]
      have hexp2 : Real.exp (-(2 * L1)) ≤ Real.exp (-(a + 2 * η_1) * L1) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith only [ha_le2, hL1_pos]
      rw [hsplit]
      exact mul_le_mul hinv hexp2 (Real.exp_pos _).le (by positivity)
    exact hpow.trans (hexp_tail.trans h4L1)
  have hdiff : (1 / (4 * L1)) * Real.exp (-(a + 2 * η_1) * L1) ≤
      (1 / L1) * Real.exp (-(a + 2 * η_1) * L1) - (1 / (2 * L1)) * Real.exp (-(a + 2 * η_1) * L1) := by
    have h1 : (1 / (4 * L1) : ℝ) ≤ 1 / L1 - 1 / (2 * L1) := by
      have : 1 / L1 - 1 / (2 * L1) = 1 / (2 * L1) := by field_simp [hL1_pos.ne']; ring
      rw [this]; exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith only [hL1_pos])
    calc (1 / (4 * L1)) * Real.exp (-(a + 2 * η_1) * L1)
        ≤ (1 / L1 - 1 / (2 * L1)) * Real.exp (-(a + 2 * η_1) * L1) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = _ := by ring
  linarith only [h_gen, hmain_term, htail_le, hdiff]

lemma div_sub_err_le {c X err : ℝ} (hc : 0 ≤ c) (hX : 1 / 2 ≤ X) (herr : 0 ≤ err) :
    c / X - 4 * c * err ≤ c / (X + err) := by
  have h1 : 0 < X := by linarith only [hX]
  have h2 : 0 < X + err := by linarith only [h1, herr]
  have hdiff : c / X - c / (X + err) = c * err / (X * (X + err)) := by
    field_simp [h1.ne', h2.ne']; ring
  have hden : 1 / 4 ≤ X * (X + err) := by nlinarith only [hX, herr]
  have hle : c * err / (X * (X + err)) ≤ 4 * c * err := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : c * err * (1 / 4) ≤ c * err * (X * (X + err)) :=
      mul_le_mul_of_nonneg_left hden (mul_nonneg hc herr)
    linarith only [h3]
  linarith only [hdiff, hle]

lemma div_sub_le_add_err {c X err : ℝ} (hc : 0 ≤ c) (hXm : 1 / 2 ≤ X - err) (herr : 0 ≤ err) :
    c / (X - err) ≤ c / X + 4 * c * err := by
  have h1 : 0 < X - err := by linarith only [hXm]
  have h2 : 0 < X := by linarith only [h1, herr]
  have hdiff : c / (X - err) - c / X = c * err / ((X - err) * X) := by
    field_simp [h1.ne', h2.ne']; ring
  have hden : 1 / 4 ≤ (X - err) * X := by nlinarith only [hXm, herr]
  have hle : c * err / ((X - err) * X) ≤ 4 * c * err := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : c * err * (1 / 4) ≤ c * err * ((X - err) * X) :=
      mul_le_mul_of_nonneg_left hden (mul_nonneg hc herr)
    linarith only [h3]
  linarith only [hdiff, hle]

set_option maxHeartbeats 1200000 in
/-- Part A bad-perimeter upper bound for active dyadic scales. -/
lemma prob_bad_perim_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M T : ℕ} {a η_lo η_up : ℝ}
    (hM : 25 ≤ M) (ha0 : 7 / 8 ≤ a) (ha1 : a < 1) (hη0 : 0 < η_lo) (hη1 : η_lo ≤ 1)
    (hT_eq : T = Nat.ceil (a * Real.log ((M : ℝ) + 1) ^ 2 / Real.pi))
    {j : ℕ} (hj : j ∈ goodScales M η_lo η_up) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (p : ℤ × ℤ) :
    let s_p := 1 + (1 - a) / 8
    let b := a * s_p ^ 2
    let ρ := (s_p ^ 2 - 1) / 2
    let m := ρ * η_lo * (b - a * (1 + ρ)) / (1 + ρ) ^ 2
    let c₁ := 4 * (a + b) * (1 + ρ) ^ 2 / (ρ * η_lo * (b - a * (1 + ρ)))
    let c₃ := ρ * c₁
    let M₁ : ℝ := (M : ℝ) + 1
    let M₂ : ℝ := ((2 * M : ℕ) : ℝ) + 1
    let L₂ : ℝ := Real.log M₂ / Real.pi
    (16 * (1 + c₁ + c₃) * (2 * Real.log 2 + 1) / Real.log M₁ +
        4 * (c₁ * (2 * c₁ + 2 * c₃) + b * c₃ * (2 * c₁ + 7 * c₃)) / L₂ ≤ m / 4) →
    ((L₂ + 2) / ((2 ^ j : ℕ) : ℝ) ≤ 1) →
    (ℙ {ω | (T : ℝ) ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        perimCap M (2 ^ j) b < ∑ z ∈ Prot p (2 ^ j) σ, (locShift 0 (path X ω) (2 * M) z : ℝ)}).toReal ≤
      Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) * Real.exp (-(a + m / 2) * Real.log M₁) := by
  intro s_p b ρ m c₁ c₃ M₁ M₂ L₂ herr_small hR_big
  have hpi := Real.pi_pos
  have ha_pos : 0 < a := by linarith only [ha0]
  obtain ⟨hρ0, hm0, hc10, hlimA⟩ := partA_limit_margin ha_pos ha1 hη0 hη1
  change 0 < ρ at hρ0
  change 0 < m at hm0
  change 0 < c₁ at hc10
  change ∀ γ : ℝ, η_lo ≤ γ → γ ≤ 1 →
    a + 3 * m / 4 ≤
      a * c₁ / (1 + c₁ * (1 + ρ * γ)) + b * γ ^ 2 * (ρ * c₁) / (1 + (1 + ρ) * γ * c₁) at hlimA
  have hc30 : 0 ≤ c₃ := mul_nonneg hρ0.le hc10.le
  have hb0 : 0 < b := by dsimp [b, s_p]; positivity
  have hjf := Finset.mem_filter.mp hj
  set R : ℕ := 2 ^ j
  have hR1 : 1 ≤ R := Nat.one_le_pow j 2 two_pos
  have h3R : (3 * R) ^ 2 ≤ M + 1 := hjf.2.1
  have hR2_M : R ^ 2 ≤ M + 1 := le_trans (by nlinarith) h3R
  have hR2_2M : R ^ 2 ≤ 2 * M + 1 := le_trans hR2_M (by omega)
  have hγ_lo : η_lo ≤ Real.log (M₁ / (R : ℝ) ^ 2) / Real.log M₁ := hjf.2.2.1
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hM1_pos : 0 < M₁ := by linarith only [hM1_ge]
  have hM2_ge : M₁ ≤ M₂ := by dsimp [M₁, M₂]; push_cast; linarith only
  have hM2_pos : 0 < M₂ := by linarith only [hM1_ge, hM2_ge]
  have hM2_le : M₂ ≤ 2 * M₁ := by dsimp [M₁, M₂]; push_cast; linarith only
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le hM1_pos).mpr (this.trans hM1_ge)
  have hlogM1_pos : 0 < Real.log M₁ := by linarith only [hlogM1]
  have hlogM2_ge : Real.log M₁ ≤ Real.log M₂ := Real.log_le_log hM1_pos hM2_ge
  have hlogM2_pos : 0 < Real.log M₂ := by linarith only [hlogM1_pos, hlogM2_ge]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogM2_le : Real.log M₂ ≤ Real.log M₁ + Real.log 2 := by
    have h1 := Real.log_le_log hM2_pos hM2_le
    rw [Real.log_mul two_ne_zero hM1_pos.ne'] at h1
    linarith only [h1]
  have hL₂_pos : 0 < L₂ := div_pos hlogM2_pos hpi
  set γ : ℝ := Real.log (M₁ / (R : ℝ) ^ 2) / Real.log M₁
  set γ₂ : ℝ := Real.log (M₂ / (R : ℝ) ^ 2) / Real.log M₂
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR1
  have hR2_pos : (0 : ℝ) < (R : ℝ) ^ 2 := sq_pos_of_pos hR0
  have hR_ge1 : (1 : ℝ) ≤ (R : ℝ) ^ 2 := by exact_mod_cast (by nlinarith : 1 ≤ R ^ 2)
  have hγ_le_γ₂ : γ ≤ γ₂ := by
    have hlogR0 : 0 ≤ Real.log ((R : ℝ) ^ 2) := Real.log_nonneg hR_ge1
    have h1 : γ = 1 - Real.log ((R : ℝ) ^ 2) / Real.log M₁ := by
      dsimp [γ]
      rw [Real.log_div hM1_pos.ne' hR2_pos.ne', sub_div, div_self hlogM1_pos.ne']
    have h2 : γ₂ = 1 - Real.log ((R : ℝ) ^ 2) / Real.log M₂ := by
      dsimp [γ₂]
      rw [Real.log_div hM2_pos.ne' hR2_pos.ne', sub_div, div_self hlogM2_pos.ne']
    rw [h1, h2]
    exact sub_le_sub_left (div_le_div_of_nonneg_left hlogR0 hlogM1_pos hlogM2_ge) 1
  have hγ₂_lo : η_lo ≤ γ₂ := hγ_lo.trans hγ_le_γ₂
  have hγ₂_pos : 0 < γ₂ := lt_of_lt_of_le hη0 hγ₂_lo
  have hγ₂_le1 : γ₂ ≤ 1 := by
    dsimp [γ₂]; rw [div_le_one hlogM2_pos]
    exact Real.log_le_log (div_pos hM2_pos hR2_pos) (div_le_self hM2_pos.le hR_ge1)
  have hγ_le_γ₂' : γ₂ ≤ γ + Real.log 2 / Real.log M₁ := by
    have h1 : γ₂ * Real.log M₂ ≤ γ * Real.log M₁ + Real.log 2 := by
      have heq1 : γ₂ * Real.log M₂ = Real.log (M₂ / (R : ℝ) ^ 2) := by
        dsimp [γ₂]; field_simp [hlogM2_pos.ne']
      have heq2 : γ * Real.log M₁ = Real.log (M₁ / (R : ℝ) ^ 2) := by
        dsimp [γ]; field_simp [hlogM1_pos.ne']
      rw [heq1, heq2]
      have hdiv : M₂ / (R : ℝ) ^ 2 ≤ 2 * (M₁ / (R : ℝ) ^ 2) := by
        rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hM2_le hR2_pos.le
      have hlog := Real.log_le_log (div_pos hM2_pos hR2_pos) hdiv
      rw [Real.log_mul two_ne_zero (div_pos hM1_pos hR2_pos).ne'] at hlog
      linarith only [hlog]
    have h2 : γ₂ * Real.log M₁ ≤ γ₂ * Real.log M₂ := mul_le_mul_of_nonneg_left hlogM2_ge hγ₂_pos.le
    have h3 : γ₂ * Real.log M₁ ≤ γ * Real.log M₁ + Real.log 2 := h2.trans h1
    calc γ₂ = (γ₂ * Real.log M₁) / Real.log M₁ := by field_simp [hlogM1_pos.ne']
      _ ≤ (γ * Real.log M₁ + Real.log 2) / Real.log M₁ :=
          div_le_div_of_nonneg_right h3 hlogM1_pos.le
      _ = γ + Real.log 2 / Real.log M₁ := by
          rw [add_div, mul_div_cancel_right₀ _ hlogM1_pos.ne']
  set v₁ : ℝ := a * Real.log M₁ ^ 2 / Real.pi
  set v₃ : ℝ := perimCap M R b
  have hv₁ : 0 ≤ v₁ := by dsimp [v₁]; positivity
  have hv₃ : 0 ≤ v₃ := by dsimp [v₃, perimCap]; positivity
  have hsub : {ω : Ω | (T : ℝ) ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        v₃ < ∑ z ∈ Prot p R σ, (locShift 0 (path X ω) (2 * M) z : ℝ)} ⊆
      {ω | v₁ ≤ (locShift 0 (path X ω) (2 * M) (rot p) : ℝ) ∧
        v₃ ≤ ∑ z ∈ Prot p R σ, (locShift 0 (path X ω) (2 * M) z : ℝ)} := by
    intro ω hω
    have hv1T : v₁ ≤ (T : ℝ) := by rw [hT_eq]; exact Nat.le_ceil _
    have hmono : (locShift 0 (path X ω) M (rot p) : ℝ) ≤ (locShift 0 (path X ω) (2 * M) (rot p) : ℝ) := by
      exact_mod_cast locShift_zero_mono (by omega : M ≤ 2 * M) (rot p)
    exact ⟨hv1T.trans (hω.1.trans hmono), hω.2.le⟩
  have hprob := prob_locShift_bad_P0_le hX (by omega : 25 ≤ 2 * M) p hR1 hR2_2M hσ hc10 hc30 hv₁ hv₃
  have hm_le := (ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hsub)).trans hprob
  set ψ_x : ℝ := 1 + c₁ + c₃ * γ₂ + (2 * c₁ + 2 * c₃) / L₂
  set ψ_z : ℝ := 1 + (c₁ + c₃) * γ₂ + (2 * c₁ + 6 * c₃ + c₃ * (L₂ + 2) / (R : ℝ)) / L₂
  have hψx_pos : 0 < ψ_x := by
    have : 0 ≤ c₃ * γ₂ := mul_nonneg hc30 hγ₂_pos.le
    have : 0 ≤ (2 * c₁ + 2 * c₃) / L₂ := div_nonneg (by linarith only [hc10, hc30]) hL₂_pos.le
    dsimp [ψ_x]; linarith only [hc10, ‹0 ≤ c₃ * γ₂›, ‹0 ≤ (2 * c₁ + 2 * c₃) / L₂›]
  have hψz_pos : 0 < ψ_z := by
    have h1 : 0 ≤ (c₁ + c₃) * γ₂ := mul_nonneg (by linarith only [hc10, hc30]) hγ₂_pos.le
    have h2 : 0 ≤ (2 * c₁ + 6 * c₃ + c₃ * (L₂ + 2) / (R : ℝ)) / L₂ :=
      div_nonneg (add_nonneg (by linarith only [hc10, hc30])
        (div_nonneg (mul_nonneg hc30 (by linarith only [hL₂_pos])) hR0.le)) hL₂_pos.le
    dsimp [ψ_z]; linarith only [h1, h2]
  have hratio_log : 1 - Real.log 2 / Real.log M₁ ≤ Real.log M₁ / Real.log M₂ := by
    have h1 : Real.log M₂ - Real.log 2 ≤ Real.log M₁ := by linarith only [hlogM2_le]
    have h2 : 1 - Real.log 2 / Real.log M₂ ≤ Real.log M₁ / Real.log M₂ := by
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hlogM2_pos]
      linarith only [h1]
    have h3' : Real.log 2 / Real.log M₂ ≤ Real.log 2 / Real.log M₁ :=
      div_le_div_of_nonneg_left hlog2_pos.le hlogM1_pos hlogM2_ge
    linarith only [h2, h3']
  have hb_lt2 : b ≤ 2 := by
    dsimp [b, s_p]
    have hsp : 1 + (1 - a) / 8 ≤ (9 / 8 : ℝ) := by linarith only [ha0]
    have hs0 : (0 : ℝ) ≤ 1 + (1 - a) / 8 := by linarith only [ha1]
    have hsp2 : (1 + (1 - a) / 8) ^ 2 ≤ (9 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hs0 hsp 2
    have hmul := mul_le_mul ha1.le hsp2 (sq_nonneg _) zero_le_one
    linarith only [hmul]
  have hr_nn : 0 ≤ Real.log M₁ / Real.log M₂ := div_nonneg hlogM1_pos.le hlogM2_pos.le
  have hr_le1 : Real.log M₁ / Real.log M₂ ≤ 1 := (div_le_one hlogM2_pos).mpr hlogM2_ge
  have hratio_sq : 1 - 2 * Real.log 2 / Real.log M₁ ≤ (Real.log M₁ / Real.log M₂) ^ 2 := by
    have h2 : 1 - (1 - Real.log 2 / Real.log M₁) ^ 2 ≤ 2 * (Real.log 2 / Real.log M₁) := by
      have h_eq : 1 - (1 - Real.log 2 / Real.log M₁) ^ 2 =
          (Real.log 2 / Real.log M₁) * (2 - Real.log 2 / Real.log M₁) := by ring
      have h_nn : 0 ≤ Real.log 2 / Real.log M₁ := div_nonneg hlog2_pos.le hlogM1_pos.le
      nlinarith only [h_eq, h_nn]
    have h3 : (1 - Real.log 2 / Real.log M₁) ^ 2 ≤ (Real.log M₁ / Real.log M₂) ^ 2 := by
      have h0 : 0 ≤ 1 - Real.log 2 / Real.log M₁ := by
        have : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
        have : Real.log 2 / Real.log M₁ ≤ 1 := (div_le_one hlogM1_pos).mpr (by linarith only [this, hlogM1])
        linarith only [this]
      exact pow_le_pow_left₀ h0 hratio_log 2
    linarith only [h2, h3, show 2 * (Real.log 2 / Real.log M₁) = 2 * Real.log 2 / Real.log M₁ by ring]
  have hratio_sq_le1 : (Real.log M₁ / Real.log M₂) ^ 2 ≤ 1 := by
    nlinarith only [hr_le1, hr_nn]
  have hv1_eq : v₁ * (c₁ / (L₂ * ψ_x)) = Real.log M₂ * (a * (Real.log M₁ / Real.log M₂) ^ 2 * (c₁ / ψ_x)) := by
    dsimp [v₁, L₂]
    field_simp [hlogM2_pos.ne', hpi.ne', hψx_pos.ne']
  have hv3_eq : v₃ * (c₃ / ((R : ℝ) * L₂ * ψ_z)) =
      Real.log M₂ * (b * γ ^ 2 * (Real.log M₁ / Real.log M₂) ^ 2 * (c₃ / ψ_z)) := by
    have hpc_eq : v₃ = (R : ℝ) * (b * γ ^ 2 * (Real.log M₁ / Real.pi) * Real.log M₁) := rfl
    rw [hpc_eq]
    dsimp [L₂]
    field_simp [hR0.ne', hlogM2_pos.ne', hpi.ne', hψz_pos.ne']
  set r2 : ℝ := (Real.log M₁ / Real.log M₂) ^ 2
  set ex1 : ℝ := (2 * c₁ + 2 * c₃) / L₂
  set ez1 : ℝ := (2 * c₁ + 7 * c₃) / L₂
  have hr2_nn : 0 ≤ r2 := sq_nonneg _
  have hex1_nn : 0 ≤ ex1 := div_nonneg (by linarith only [hc10, hc30]) hL₂_pos.le
  have hez1_nn : 0 ≤ ez1 := div_nonneg (by linarith only [hc10, hc30]) hL₂_pos.le
  have hx_inv : c₁ / (1 + c₁ * (1 + ρ * γ₂)) - 4 * c₁ * ex1 ≤ c₁ / ψ_x := by
    have hX : 1 / 2 ≤ 1 + c₁ * (1 + ρ * γ₂) := by
      have : 0 ≤ c₁ * (1 + ρ * γ₂) := mul_nonneg hc10.le (by linarith only [mul_nonneg hρ0.le hγ₂_pos.le])
      linarith only [this]
    have h_eq : ψ_x = (1 + c₁ * (1 + ρ * γ₂)) + ex1 := by
      dsimp [ψ_x, ex1, c₃]; ring
    rw [h_eq]
    exact div_sub_err_le hc10.le hX hex1_nn
  have hz_inv : c₃ / (1 + (1 + ρ) * γ₂ * c₁) - 4 * c₃ * ez1 ≤ c₃ / ψ_z := by
    have hX : 1 / 2 ≤ 1 + (1 + ρ) * γ₂ * c₁ := by
      have : 0 ≤ (1 + ρ) * γ₂ * c₁ := mul_nonneg (mul_nonneg (by linarith only [hρ0]) hγ₂_pos.le) hc10.le
      linarith only [this]
    have hRle : c₃ * (L₂ + 2) / (R : ℝ) ≤ c₃ := by
      rw [mul_div_assoc]; exact mul_le_of_le_one_right hc30 hR_big
    have herr_le : (2 * c₁ + 6 * c₃ + c₃ * (L₂ + 2) / (R : ℝ)) / L₂ ≤ ez1 :=
      div_le_div_of_nonneg_right (by linarith only [hRle]) hL₂_pos.le
    have h1 : c₃ / ((1 + (1 + ρ) * γ₂ * c₁) + ez1) ≤ c₃ / ψ_z := by
      refine div_le_div_of_nonneg_left hc30 hψz_pos ?_
      dsimp [ψ_z]
      have heq_main : 1 + (1 + ρ) * γ₂ * c₁ = 1 + (c₁ + c₃) * γ₂ := by dsimp [c₃]; ring
      linarith only [heq_main, herr_le]
    exact (div_sub_err_le hc30 hX hez1_nn).trans h1
  have h_lim := hlimA γ₂ hγ₂_lo hγ₂_le1
  clear hlimA
  have h1ρg_ge1 : 1 ≤ 1 + ρ * γ₂ := le_add_of_nonneg_right (mul_nonneg hρ0.le hγ₂_pos.le)
  have h1_den_pos : 0 < 1 + c₁ * (1 + ρ * γ₂) :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hc10.le (zero_le_one.trans h1ρg_ge1))
  have h1_nn : 0 ≤ c₁ / (1 + c₁ * (1 + ρ * γ₂)) := div_nonneg hc10.le h1_den_pos.le
  have h1_le1 : c₁ / (1 + c₁ * (1 + ρ * γ₂)) ≤ 1 := by
    rw [div_le_one h1_den_pos]
    have : c₁ ≤ c₁ * (1 + ρ * γ₂) := le_mul_of_one_le_right hc10.le h1ρg_ge1
    linarith only [this]
  have h2_den_ge1 : 1 ≤ 1 + (1 + ρ) * γ₂ * c₁ :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by linarith only [hρ0]) hγ₂_pos.le) hc10.le)
  have h2_den_pos : 0 < 1 + (1 + ρ) * γ₂ * c₁ := lt_of_lt_of_le zero_lt_one h2_den_ge1
  have h2_nn : 0 ≤ c₃ / (1 + (1 + ρ) * γ₂ * c₁) := div_nonneg hc30 h2_den_pos.le
  have h2_lec3 : c₃ / (1 + (1 + ρ) * γ₂ * c₁) ≤ c₃ := div_le_self hc30 h2_den_ge1
  have hterm1_fin : a * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) - 2 * Real.log 2 / Real.log M₁ - 4 * c₁ * ex1 ≤
      a * r2 * (c₁ / ψ_x) := by
    have h1 : a * r2 * (c₁ / (1 + c₁ * (1 + ρ * γ₂)) - 4 * c₁ * ex1) ≤ a * r2 * (c₁ / ψ_x) :=
      mul_le_mul_of_nonneg_left hx_inv (mul_nonneg ha_pos.le hr2_nn)
    have h2 : a * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) - 2 * Real.log 2 / Real.log M₁ ≤
        a * r2 * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) := by
      have h1mr : 1 - r2 ≤ 2 * Real.log 2 / Real.log M₁ := by linarith only [hratio_sq]
      have ha_prod : a * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) ≤ 1 := by nlinarith only [ha1, h1_le1, h1_nn]
      have hdiff : a * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) * (1 - r2) ≤ 1 * (2 * Real.log 2 / Real.log M₁) :=
        mul_le_mul ha_prod h1mr (by linarith only [hratio_sq_le1]) zero_le_one
      linarith only [hdiff, show a * r2 * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) =
        a * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) - a * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) * (1 - r2) by ring]
    have h3 : a * r2 * (4 * c₁ * ex1) ≤ 4 * c₁ * ex1 := by
      have ha_r : a * r2 ≤ 1 := by nlinarith only [ha1, hratio_sq_le1, hr2_nn]
      exact mul_le_of_le_one_left (mul_nonneg (mul_nonneg (by norm_num) hc10.le) hex1_nn) ha_r
    have h_eq1 : a * r2 * (c₁ / (1 + c₁ * (1 + ρ * γ₂)) - 4 * c₁ * ex1) =
        a * r2 * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) - a * r2 * (4 * c₁ * ex1) := by ring
    linarith only [h1, h2, h3, h_eq1]
  have hterm2_fin : b * γ₂ ^ 2 * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) -
      8 * c₃ * Real.log 2 / Real.log M₁ - 4 * b * c₃ * ez1 ≤ b * γ ^ 2 * r2 * (c₃ / ψ_z) := by
    have hγ0 : 0 ≤ γ := by linarith only [hγ_lo, hη0]
    have hγ_le1 : γ ≤ 1 := hγ_le_γ₂.trans hγ₂_le1
    have h1 : b * γ ^ 2 * r2 * (c₃ / (1 + (1 + ρ) * γ₂ * c₁) - 4 * c₃ * ez1) ≤
        b * γ ^ 2 * r2 * (c₃ / ψ_z) :=
      mul_le_mul_of_nonneg_left hz_inv (mul_nonneg (mul_nonneg hb0.le (sq_nonneg γ)) hr2_nn)
    have hγsq_diff : γ₂ ^ 2 - γ ^ 2 * r2 ≤ 4 * Real.log 2 / Real.log M₁ := by
      have h1_d : γ₂ ^ 2 - γ ^ 2 ≤ 2 * (Real.log 2 / Real.log M₁) := by
        have hsum2 : γ₂ + γ ≤ 2 := by linarith only [hγ₂_le1, hγ_le1]
        have hdiff_g : 0 ≤ γ₂ - γ := by linarith only [hγ_le_γ₂]
        have hdiff_le : γ₂ - γ ≤ Real.log 2 / Real.log M₁ := by linarith only [hγ_le_γ₂']
        calc γ₂ ^ 2 - γ ^ 2 = (γ₂ + γ) * (γ₂ - γ) := by ring
          _ ≤ 2 * (Real.log 2 / Real.log M₁) := mul_le_mul hsum2 hdiff_le hdiff_g zero_le_two
      have h2_d : γ ^ 2 * (1 - r2) ≤ 2 * (Real.log 2 / Real.log M₁) := by
        have hγ2_le1 : γ ^ 2 ≤ 1 := by nlinarith only [hγ0, hγ_le1]
        have h1mr : 1 - r2 ≤ 2 * (Real.log 2 / Real.log M₁) := by
          linarith only [hratio_sq, show 2 * Real.log 2 / Real.log M₁ = 2 * (Real.log 2 / Real.log M₁) by ring]
        have := mul_le_mul hγ2_le1 h1mr (sub_nonneg.mpr hratio_sq_le1) zero_le_one
        linarith only [this]
      calc γ₂ ^ 2 - γ ^ 2 * r2 = (γ₂ ^ 2 - γ ^ 2) + γ ^ 2 * (1 - r2) := by ring
        _ ≤ 2 * (Real.log 2 / Real.log M₁) + 2 * (Real.log 2 / Real.log M₁) := add_le_add h1_d h2_d
        _ = 4 * Real.log 2 / Real.log M₁ := by ring
    have h2 : b * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) * (γ₂ ^ 2 - γ ^ 2 * r2) ≤
        8 * c₃ * Real.log 2 / Real.log M₁ := by
      have hbc : b * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) ≤ 2 * c₃ := by nlinarith only [hb_lt2, h2_lec3, h2_nn]
      have hgr1 : γ ^ 2 ≤ γ₂ ^ 2 := pow_le_pow_left₀ hγ0 hγ_le_γ₂ 2
      have hgr2 : γ ^ 2 * r2 ≤ γ ^ 2 * 1 := mul_le_mul_of_nonneg_left hratio_sq_le1 (sq_nonneg γ)
      have hgr : 0 ≤ γ₂ ^ 2 - γ ^ 2 * r2 := by linarith only [hgr1, hgr2]
      have hmul := mul_le_mul hbc hγsq_diff hgr (mul_nonneg zero_le_two hc30)
      calc b * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) * (γ₂ ^ 2 - γ ^ 2 * r2)
          ≤ (2 * c₃) * (4 * Real.log 2 / Real.log M₁) := hmul
        _ = 8 * c₃ * Real.log 2 / Real.log M₁ := by ring
    have h3 : b * γ ^ 2 * r2 * (4 * c₃ * ez1) ≤ 4 * b * c₃ * ez1 := by
      have hγr : γ ^ 2 * r2 ≤ 1 := by nlinarith only [hγ0, hγ_le1, hratio_sq_le1]
      calc b * γ ^ 2 * r2 * (4 * c₃ * ez1) = (γ ^ 2 * r2) * (4 * b * c₃ * ez1) := by ring
        _ ≤ 1 * (4 * b * c₃ * ez1) :=
            mul_le_mul_of_nonneg_right hγr (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb0.le) hc30) hez1_nn)
        _ = _ := one_mul _
    have h_eq1 : b * γ ^ 2 * r2 * (c₃ / (1 + (1 + ρ) * γ₂ * c₁) - 4 * c₃ * ez1) =
        b * γ ^ 2 * r2 * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) - b * γ ^ 2 * r2 * (4 * c₃ * ez1) := by ring
    have h_eq2 : b * γ ^ 2 * r2 * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) =
        b * γ₂ ^ 2 * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) -
          b * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) * (γ₂ ^ 2 - γ ^ 2 * r2) := by ring
    linarith only [h1, h2, h3, h_eq1, h_eq2]
  have herr_sum : (2 * Real.log 2 / Real.log M₁ + 8 * c₃ * Real.log 2 / Real.log M₁) +
      (4 * c₁ * ex1 + 4 * b * c₃ * ez1) ≤ m / 4 := by
    have h1 : 2 * Real.log 2 / Real.log M₁ + 8 * c₃ * Real.log 2 / Real.log M₁ ≤
        16 * (1 + c₁ + c₃) * (2 * Real.log 2 + 1) / Real.log M₁ := by
      rw [← add_div, div_le_div_iff_of_pos_right hlogM1_pos]
      nlinarith only [hlog2_pos, hc10, hc30]
    have h2 : 4 * c₁ * ex1 + 4 * b * c₃ * ez1 =
        4 * (c₁ * (2 * c₁ + 2 * c₃) + b * c₃ * (2 * c₁ + 7 * c₃)) / L₂ := by
      dsimp [ex1, ez1]; ring
    linarith only [h1, h2, herr_small]
  have hlim_rw : a + 3 * m / 4 ≤ a * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) +
      b * γ₂ ^ 2 * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) := by
    have h_r1 : a * c₁ / (1 + c₁ * (1 + ρ * γ₂)) = a * (c₁ / (1 + c₁ * (1 + ρ * γ₂))) := by ring
    have h_r2 : b * γ₂ ^ 2 * (ρ * c₁) / (1 + (1 + ρ) * γ₂ * c₁) =
        b * γ₂ ^ 2 * (c₃ / (1 + (1 + ρ) * γ₂ * c₁)) := by dsimp [c₃]; ring
    linarith only [h_lim, h_r1, h_r2]
  have hexp_ge : a + m / 2 ≤ a * r2 * (c₁ / ψ_x) + b * γ ^ 2 * r2 * (c₃ / ψ_z) := by
    linarith only [hlim_rw, hterm1_fin, hterm2_fin, herr_sum]
  have hmul_exp : (a + m / 2) * Real.log M₁ ≤ v₁ * (c₁ / (L₂ * ψ_x)) + v₃ * (c₃ / ((R : ℝ) * L₂ * ψ_z)) := by
    rw [hv1_eq, hv3_eq, ← mul_add]
    calc (a + m / 2) * Real.log M₁ ≤ (a + m / 2) * Real.log M₂ :=
          mul_le_mul_of_nonneg_left hlogM2_ge (by positivity)
      _ ≤ Real.log M₂ * (a * r2 * (c₁ / ψ_x) + b * γ ^ 2 * r2 * (c₃ / ψ_z)) := by
          rw [mul_comm (a + m / 2)]; exact mul_le_mul_of_nonneg_left hexp_ge hlogM2_pos.le
  exact hm_le.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hmul_exp])) (by positivity))

/-- Part B 3-point bound for `goodEvent p ∩ goodEvent q` at an active dyadic scale. -/
lemma prob_two_good_pair_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M T : ℕ} {a η_lo : ℝ}
    (hM : 25 ≤ M) (ha0 : 7 / 8 ≤ a) (ha1 : a < 1) (hη0 : 0 < η_lo)
    (hT_eq : T = Nat.ceil (a * Real.log ((M : ℝ) + 1) ^ 2 / Real.pi))
    {p q : ℤ × ℤ} (hpq : p ≠ q) {j : ℕ}
    (hj : j ∈ goodScales M η_lo ((1 - a) / 2))
    (hdR : rnorm (p - q) ≤ 2 ^ j) (hR2d : 2 ^ j < 2 * rnorm (p - q)) :
    let t := (1 - a) / 8
    let s_p := 1 + t
    let b := a * s_p ^ 2
    let η_up := (1 - a) / 2
    let m := a * t ^ 2 * η_lo
    let c₁ := 16 / (η_up ^ 2 * m)
    let M₁ : ℝ := (M : ℝ) + 1
    let L : ℝ := Real.log M₁ / Real.pi
    let γ : ℝ := Real.log (M₁ / (2 ^ j : ℝ) ^ 2) / Real.log M₁
    ((L + 2) / ((2 ^ j : ℕ) : ℝ) ≤ 1) →
    (48 * c₁ ≤ L) →
    (8 * (16 * c₁ ^ 2 + 16 * c₁ ^ 2 * 22 * c₁) / L ≤ m / 4) →
    (ℙ ({ω | path X ω ∈ goodEvent M T b η_lo η_up p} ∩
        {ω | path X ω ∈ goodEvent M T b η_lo η_up q})).toReal ≤
      Real.exp 2 * (1 + 8 * c₁) * Real.exp (-(2 * a - γ + m / 4) * Real.log M₁) := by
  intro t s_p b η_up m c₁ M₁ L γ hR_big hL48 herr_small
  have hpi := Real.pi_pos
  obtain ⟨ht0, hηup0, hm0, hc10, hlimB⟩ := partB_good_limit_margin ha0 ha1 hη0
  change 0 < t at ht0
  change 0 < η_up at hηup0
  change 0 < m at hm0
  change 0 < c₁ at hc10
  change ∀ γ : ℝ, η_lo ≤ γ → γ ≤ 1 - η_up →
    let u := s_p * (1 - γ) / (1 - s_p * γ)
    let ρ := 2 - u
    0 < ρ ∧ ρ < 2 ∧ η_up ≤ u ∧ u ≤ 2 ∧
      (2 * a - γ) + m / 2 ≤
        2 * a * c₁ / (1 + c₁ * (1 + γ - ρ * γ)) - b * γ ^ 2 * (ρ * c₁) / (1 + (2 - ρ) * c₁ * γ) at hlimB
  have hjf := Finset.mem_filter.mp hj
  set R : ℕ := 2 ^ j
  have hR1 : 1 ≤ R := Nat.one_le_pow j 2 two_pos
  have h3R : (3 * R) ^ 2 ≤ M + 1 := hjf.2.1
  have hγ_eq : γ = Real.log (((M : ℝ) + 1) / (R : ℝ) ^ 2) / Real.log ((M : ℝ) + 1) := by
    dsimp [γ, M₁, R]; push_cast; rfl
  have hγ_lo : η_lo ≤ γ := by rw [hγ_eq]; exact hjf.2.2.1
  have hγ_hi : γ ≤ 1 - η_up := by rw [hγ_eq]; exact hjf.2.2.2
  obtain ⟨hρ0, hρ2, hu_ge, _, hexp_lim⟩ := hlimB γ hγ_lo hγ_hi
  clear hlimB
  set u := s_p * (1 - γ) / (1 - s_p * γ)
  set ρ := 2 - u
  set c₃ := ρ * c₁
  change 0 < ρ at hρ0
  change ρ < 2 at hρ2
  change η_up ≤ u at hu_ge
  change (2 * a - γ) + m / 2 ≤
    2 * a * c₁ / (1 + c₁ * (1 + γ - ρ * γ)) - b * γ ^ 2 * (ρ * c₁) / (1 + (2 - ρ) * c₁ * γ) at hexp_lim
  have hc30 : 0 ≤ c₃ := mul_nonneg hρ0.le hc10.le
  have hc3_le : c₃ ≤ 2 * c₁ := by dsimp [c₃]; nlinarith only [hρ2, hc10]
  have hb_lt2 : b ≤ 2 := by
    dsimp [b, s_p, t]
    have h1 : 1 + (1 - a) / 8 ≤ (9 / 8 : ℝ) := by linarith only [ha0]
    have h2 : 0 ≤ 1 + (1 - a) / 8 := by linarith only [ha1]
    have hsq : (1 + (1 - a) / 8) ^ 2 ≤ (9 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ h2 h1 2
    have hmul := mul_le_mul ha1.le hsq (sq_nonneg _) zero_le_one
    linarith only [hmul]
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hM1_pos : 0 < M₁ := by linarith only [hM1_ge]
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le hM1_pos).mpr (this.trans hM1_ge)
  have hlogM1_pos : 0 < Real.log M₁ := by linarith only [hlogM1]
  have hL_ge : 3 / 4 ≤ L := by dsimp [L]; rw [le_div_iff₀ hpi]; linarith only [hlogM1, Real.pi_lt_four]
  have hL0 : 0 < L := by linarith only [hL_ge]
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR1
  have hL_big : 10 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ) ≤ L / 2 := by
    have h1 : c₃ * (L + 2) / (R : ℝ) ≤ c₃ := by
      calc c₃ * (L + 2) / (R : ℝ) = c₃ * ((L + 2) / (R : ℝ)) := by ring
        _ ≤ c₃ * 1 := mul_le_mul_of_nonneg_left hR_big hc30
        _ = c₃ := mul_one _
    have h2 : 10 * c₁ + 6 * c₃ + c₃ ≤ 24 * c₁ := by linarith only [hc3_le, hc10]
    linarith only [h1, h2, hL48]
  set v₁ : ℝ := a * Real.log M₁ ^ 2 / Real.pi
  set v₃ : ℝ := perimCap M R b
  have hv₁ : 0 ≤ v₁ := by dsimp [v₁]; positivity
  have hv₃ : 0 ≤ v₃ := by dsimp [v₃, perimCap]; positivity
  have hsub : ({ω : Ω | path X ω ∈ goodEvent M T b η_lo η_up p} ∩
        {ω | path X ω ∈ goodEvent M T b η_lo η_up q}) ⊆
      {ω | v₁ ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        v₁ ≤ (locShift 0 (path X ω) M (rot q) : ℝ) ∧
        (∑ z ∈ Prot p R (pdir p q), (locShift 0 (path X ω) (2 * M) z : ℝ)) ≤ v₃} := by
    rintro ω ⟨hpω, hqω⟩
    have hv1T : v₁ ≤ (T : ℝ) := by rw [hT_eq]; exact Nat.le_ceil _
    have hdir : pdir p q ∈ ({1, -1} : Finset ℤ) := by
      dsimp [pdir]; split_ifs <;> simp
    exact ⟨hv1T.trans (by exact_mod_cast hpω.1), hv1T.trans (by exact_mod_cast hqω.1),
      hpω.2 j hj (pdir p q) hdir⟩
  have hprob := prob_locShift_two_good_le hX hM hpq hR1 hdR hR2d h3R hc10 hρ0.le hρ2 hv₁ hv₃ hL_big
  have hm_le := (ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hsub)).trans hprob
  set ψ_up : ℝ := 1 + c₁ * (1 + γ - ρ * γ) + (6 * c₁ + 5 * c₃) / L
  set ψ_low : ℝ := 1 + (2 * c₁ - c₃) * γ - (8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L
  have hγ0 : 0 ≤ γ := le_trans hη0.le hγ_lo
  have h1g_nn : 0 ≤ 1 + γ - ρ * γ := by
    have : 1 + γ - ρ * γ = (1 - γ) + (2 - ρ) * γ := by ring
    rw [this]; exact add_nonneg (by linarith only [hγ_hi, hηup0]) (mul_nonneg (by linarith only [hρ2]) hγ0)
  have hψup_pos : 0 < ψ_up := by
    have h1 : 0 ≤ c₁ * (1 + γ - ρ * γ) := mul_nonneg hc10.le h1g_nn
    have h2 : 0 ≤ (6 * c₁ + 5 * c₃) / L := div_nonneg (by linarith only [hc10, hc30]) hL0.le
    dsimp [ψ_up]; linarith only [h1, h2]
  have hXm : 1 / 2 ≤ ψ_low := by
    have h1 : (8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L ≤ 1 / 2 := by
      rw [div_le_iff₀ hL0]; linarith only [hL_big, hc10, hc30]
    have h2 : 0 ≤ (2 * c₁ - c₃) * γ := mul_nonneg (by linarith only [hc3_le]) hγ0
    dsimp [ψ_low]; linarith only [h1, h2]
  have hψlow_pos : 0 < ψ_low := by linarith only [hXm]
  have hup_inv : c₁ / (1 + c₁ * (1 + γ - ρ * γ)) - 4 * c₁ * ((6 * c₁ + 5 * c₃) / L) ≤ c₁ / ψ_up := by
    have hX : 1 / 2 ≤ 1 + c₁ * (1 + γ - ρ * γ) := by
      have : 0 ≤ c₁ * (1 + γ - ρ * γ) := mul_nonneg hc10.le h1g_nn
      linarith only [this]
    have h_eq : ψ_up = (1 + c₁ * (1 + γ - ρ * γ)) + (6 * c₁ + 5 * c₃) / L := rfl
    rw [h_eq]
    exact div_sub_err_le hc10.le hX (div_nonneg (by linarith only [hc10, hc30]) hL0.le)
  have hlow_inv : c₃ / ψ_low ≤
      c₃ / (1 + (2 * c₁ - c₃) * γ) + 4 * c₃ * ((8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L) :=
    div_sub_le_add_err hc30 hXm (div_nonneg (add_nonneg (by linarith only [hc10, hc30])
      (div_nonneg (mul_nonneg hc30 (by linarith only [hL0])) hR0.le)) hL0.le)
  have hv1_eq : 2 * v₁ * (c₁ / (L * ψ_up)) = Real.log M₁ * (2 * a * (c₁ / ψ_up)) := by
    dsimp [v₁, L]; field_simp [hpi.ne', hlogM1_pos.ne', hψup_pos.ne']
  have hv3_eq : v₃ * (c₃ / ((R : ℝ) * L * ψ_low)) = Real.log M₁ * (b * γ ^ 2 * (c₃ / ψ_low)) := by
    have hpc_eq : v₃ = (R : ℝ) * (b * γ ^ 2 * (Real.log M₁ / Real.pi) * Real.log M₁) := by
      dsimp [v₃, perimCap]; rw [← hγ_eq]
    rw [hpc_eq]
    dsimp [L]
    field_simp [hR0.ne', hpi.ne', hlogM1_pos.ne', hψlow_pos.ne']
  have herr_bd : 2 * a * (4 * c₁ * ((6 * c₁ + 5 * c₃) / L)) +
      b * γ ^ 2 * (4 * c₃ * ((8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L)) ≤ m / 4 := by
    have h1 : 2 * a * (4 * c₁ * ((6 * c₁ + 5 * c₃) / L)) ≤ 8 * (16 * c₁ ^ 2) / L := by
      have h16 : 6 * c₁ + 5 * c₃ ≤ 16 * c₁ := by linarith only [hc3_le]
      have ha_le : a ≤ 1 := ha1.le
      calc 2 * a * (4 * c₁ * ((6 * c₁ + 5 * c₃) / L))
          ≤ 2 * 1 * (4 * c₁ * (16 * c₁ / L)) := by gcongr
        _ = 8 * (16 * c₁ ^ 2) / L := by ring
    have h2 : b * γ ^ 2 * (4 * c₃ * ((8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L)) ≤
        8 * (16 * c₁ ^ 2 * 22 * c₁) / L := by
      have hγ_le1 : γ ≤ 1 := by linarith only [hγ_hi, hηup0]
      have hγ2_le1 : γ ^ 2 ≤ 1 := by nlinarith only [hγ0, hγ_le1]
      have hcR : c₃ * ((L + 2) / (R : ℝ)) ≤ c₃ * 1 := mul_le_mul_of_nonneg_left hR_big hc30
      have h22 : 8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ) ≤ 22 * c₁ := by
        rw [mul_div_assoc]; linarith only [hc3_le, hcR]
      calc b * γ ^ 2 * (4 * c₃ * ((8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L))
          ≤ 2 * 1 * (4 * (2 * c₁) * (22 * c₁ / L)) := by gcongr
        _ = 16 * c₁ * 22 * c₁ / L := by ring
        _ ≤ 8 * (16 * c₁ ^ 2 * 22 * c₁) / L := by
            have hc1_ge1 : 1 ≤ c₁ := by
              have h_den : η_up ^ 2 * m ≤ 16 := by
                have hηu : η_up ≤ 1 := by dsimp [η_up]; linarith only [ha0]
                have hm_le : m ≤ 1 := by
                  have ht_le : t ≤ 1 := by dsimp [t]; linarith only [ha0]
                  have hηl : η_lo ≤ 1 := by linarith only [hγ_lo, hγ_le1]
                  have h_at : a * t ^ 2 ≤ 1 := by
                    have : t ^ 2 ≤ 1 := by nlinarith only [ht0, ht_le]
                    nlinarith only [ha0, ha1, this]
                  dsimp [m]; nlinarith only [h_at, hηl, hη0]
                have hηu2 : η_up ^ 2 ≤ 1 := by nlinarith only [hηup0, hηu]
                calc η_up ^ 2 * m ≤ 1 * 1 := mul_le_mul hηu2 hm_le hm0.le zero_le_one
                  _ ≤ 16 := by norm_num
              dsimp [c₁]
              rw [one_le_div (mul_pos (sq_pos_of_pos hηup0) hm0)]
              exact h_den
            rw [div_le_div_iff_of_pos_right hL0]
            nlinarith only [hc1_ge1, hc10]
    have hsum_eq : 8 * (16 * c₁ ^ 2) / L + 8 * (16 * c₁ ^ 2 * 22 * c₁) / L =
        8 * (16 * c₁ ^ 2 + 16 * c₁ ^ 2 * 22 * c₁) / L := by ring
    linarith only [h1, h2, hsum_eq, herr_small]
  have hexp_ge : 2 * a - γ + m / 4 ≤ 2 * a * (c₁ / ψ_up) - b * γ ^ 2 * (c₃ / ψ_low) := by
    have h_diff1 : 2 * a * (c₁ / (1 + c₁ * (1 + γ - ρ * γ))) -
        2 * a * (4 * c₁ * ((6 * c₁ + 5 * c₃) / L)) ≤ 2 * a * (c₁ / ψ_up) := by
      have := mul_le_mul_of_nonneg_left hup_inv (by linarith only [ha0] : 0 ≤ 2 * a)
      linarith only [this]
    have h_diff2 : b * γ ^ 2 * (c₃ / ψ_low) ≤ b * γ ^ 2 * (c₃ / (1 + (2 * c₁ - c₃) * γ)) +
        b * γ ^ 2 * (4 * c₃ * ((8 * c₁ + 6 * c₃ + c₃ * (L + 2) / (R : ℝ)) / L)) := by
      have hbg : 0 ≤ b * γ ^ 2 := mul_nonneg (by dsimp [b, s_p, t]; positivity) (sq_nonneg γ)
      have := mul_le_mul_of_nonneg_left hlow_inv hbg
      linarith only [this]
    have hlim_eq1 : 2 * a * c₁ / (1 + c₁ * (1 + γ - ρ * γ)) =
        2 * a * (c₁ / (1 + c₁ * (1 + γ - ρ * γ))) := by ring
    have hlim_eq2 : b * γ ^ 2 * (ρ * c₁) / (1 + (2 - ρ) * c₁ * γ) =
        b * γ ^ 2 * (c₃ / (1 + (2 * c₁ - c₃) * γ)) := by dsimp [c₃]; ring
    linarith only [hexp_lim, h_diff1, h_diff2, hlim_eq1, hlim_eq2, herr_bd, hm0]
  have hmul_exp : (2 * a - γ + m / 4) * Real.log M₁ ≤
      2 * v₁ * (c₁ / (L * ψ_up)) - v₃ * (c₃ / ((R : ℝ) * L * ψ_low)) := by
    rw [hv1_eq, hv3_eq, ← mul_sub, mul_comm (2 * a - γ + m / 4)]
    exact mul_le_mul_of_nonneg_left hexp_ge hlogM1_pos.le
  have hm_le' : (ℙ ({ω | path X ω ∈ goodEvent M T b η_lo η_up p} ∩
        {ω | path X ω ∈ goodEvent M T b η_lo η_up q})).toReal ≤
      Real.exp 2 * (1 + 8 * c₁) *
        Real.exp (-(2 * v₁ * (c₁ / (L * ψ_up)) - v₃ * (c₃ / ((R : ℝ) * L * ψ_low)))) := by
    refine hm_le.trans (le_of_eq ?_)
    congr 3
    dsimp [L, ψ_up, ψ_low, c₃, γ, M₁, R]
    push_cast
    rfl
  exact hm_le'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hmul_exp]))
    (mul_nonneg (Real.exp_pos _).le (by linarith only [hc10])))

/-- Part B 2-point bound when `1 - η_up < γ_R`. -/
lemma prob_two_hi_scale_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M T : ℕ} {a b η_lo η_up : ℝ}
    (hM : 25 ≤ M) (ha0 : 7 / 8 ≤ a) (ha1 : a < 1) (hηup : η_up = (1 - a) / 2)
    (hT_eq : T = Nat.ceil (a * Real.log ((M : ℝ) + 1) ^ 2 / Real.pi))
    {p q : ℤ × ℤ} (hpq : p ≠ q) {j : ℕ}
    (hγ_hi : 1 - η_up < Real.log (((M : ℝ) + 1) / (2 ^ j : ℝ) ^ 2) / Real.log ((M : ℝ) + 1))
    (hL_hi : 32 * (16 / (1 - a)) ^ 2 / (Real.log ((M : ℝ) + 1) / Real.pi) ≤ (1 - a) / 8) :
    let c₁ := 16 / (1 - a)
    let M₁ : ℝ := (M : ℝ) + 1
    let γ : ℝ := Real.log (M₁ / (2 ^ j : ℝ) ^ 2) / Real.log M₁
    (ℙ ({ω | path X ω ∈ goodEvent M T b η_lo η_up p} ∩
        {ω | path X ω ∈ goodEvent M T b η_lo η_up q})).toReal ≤
      Real.exp 2 * (1 + 8 * c₁) * Real.exp (-(2 * a - γ) * Real.log M₁) := by
  intro c₁ M₁ γ
  have hpi := Real.pi_pos
  have hc10 : 0 < c₁ := div_pos (by norm_num) (by linarith only [ha1])
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith only [hM1_ge])).mpr (this.trans hM1_ge)
  set v₁ : ℝ := a * Real.log M₁ ^ 2 / Real.pi
  have hv₁ : 0 ≤ v₁ := by dsimp [v₁]; positivity
  have hsub : ({ω : Ω | path X ω ∈ goodEvent M T b η_lo η_up p} ∩
        {ω | path X ω ∈ goodEvent M T b η_lo η_up q}) ⊆
      {ω | v₁ ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        v₁ ≤ (locShift 0 (path X ω) M (rot q) : ℝ)} := by
    rintro ω ⟨hpω, hqω⟩
    have hv1T : v₁ ≤ (T : ℝ) := by rw [hT_eq]; exact Nat.le_ceil _
    exact ⟨hv1T.trans (by exact_mod_cast hpω.1), hv1T.trans (by exact_mod_cast hqω.1)⟩
  have hprob := prob_locShift_two_le hX hM hpq hc10 hv₁
  have hm_le := (ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hsub)).trans hprob
  set L : ℝ := Real.log M₁ / Real.pi
  set γd : ℝ := max 0 (Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.log M₁)
  set ψ₂ : ℝ := 1 + c₁ * (1 + γd) + 4 * c₁ / L
  have hd1 : 1 ≤ rnorm (p - q) :=
    Nat.pos_of_ne_zero fun h0 ↦ hpq (sub_eq_zero.mp ((rnorm_eq_zero_iff (p - q)).mp h0))
  have hγd_le1 : γd ≤ 1 := by
    refine max_le zero_le_one ?_
    rw [div_le_one (by linarith only [hlogM1])]
    exact Real.log_le_log (by positivity)
      (div_le_self (by linarith only [hM1_ge]) (by exact_mod_cast (by nlinarith : 1 ≤ rnorm (p - q) ^ 2)))
  have hψ₂_le : ψ₂ ≤ 1 + 2 * c₁ + 4 * c₁ / L := by
    dsimp [ψ₂]
    have : c₁ * (1 + γd) ≤ 2 * c₁ := by nlinarith only [hγd_le1, hc10]
    linarith only [this]
  have hL0 : 0 < L := div_pos (by linarith only [hlogM1]) hpi
  have hc1_inv : a - (1 - a) / 4 ≤ 2 * a * (c₁ / ψ₂) := by
    have h1 : 2 * a * (c₁ / (1 + 2 * c₁ + 4 * c₁ / L)) ≤ 2 * a * (c₁ / ψ₂) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hc10.le (by dsimp [ψ₂]; positivity) hψ₂_le)
        (by linarith only [ha0])
    have hX : 1 / 2 ≤ 1 + 2 * c₁ := by linarith only [hc10]
    have h2 : c₁ / (1 + 2 * c₁) - 4 * c₁ * (4 * c₁ / L) ≤ c₁ / (1 + 2 * c₁ + 4 * c₁ / L) :=
      div_sub_err_le hc10.le hX (by positivity)
    have h3 : 2 * a * (c₁ / (1 + 2 * c₁)) ≥ a - (1 - a) / 16 := by
      have hdiff : a - 2 * a * (c₁ / (1 + 2 * c₁)) = a / (1 + 2 * c₁) := by
        field_simp [(by positivity : 1 + 2 * c₁ ≠ 0)]; ring
      have hle : a / (1 + 2 * c₁) ≤ (1 - a) / 32 := by
        have hden : 32 / (1 - a) ≤ 1 + 2 * c₁ := by
          dsimp [c₁]
          have : 2 * (16 / (1 - a)) = 32 / (1 - a) := by ring
          linarith only [this]
        calc a / (1 + 2 * c₁) ≤ 1 / (32 / (1 - a)) :=
              div_le_div₀ zero_le_one ha1.le (div_pos (by norm_num) (by linarith only [ha1])) hden
          _ = (1 - a) / 32 := by field_simp [(by linarith only [ha1] : 1 - a ≠ 0)]
      linarith only [hdiff, hle, ha1]
    have h4 : 2 * a * (4 * c₁ * (4 * c₁ / L)) ≤ (1 - a) / 8 := by
      have h1a : 2 * a * (4 * c₁ * (4 * c₁ / L)) = a * (32 * c₁ ^ 2 / L) := by ring
      rw [h1a]
      calc a * (32 * c₁ ^ 2 / L) ≤ 1 * (32 * c₁ ^ 2 / L) :=
            mul_le_mul_of_nonneg_right ha1.le (by positivity)
        _ = 32 * c₁ ^ 2 / L := one_mul _
        _ ≤ (1 - a) / 8 := hL_hi
    have h5 : 2 * a * (c₁ / (1 + 2 * c₁)) - 2 * a * (4 * c₁ * (4 * c₁ / L)) ≤
        2 * a * (c₁ / (1 + 2 * c₁ + 4 * c₁ / L)) := by
      have := mul_le_mul_of_nonneg_left h2 (by linarith only [ha0] : 0 ≤ 2 * a)
      linarith only [this]
    linarith only [h1, h3, h4, h5, ha1]
  have h2aγ : 2 * a - γ ≤ 2 * a * (c₁ / ψ₂) := by
    have hγ' : 1 - (1 - a) / 2 < γ := by rw [← hηup]; exact hγ_hi
    have : 2 * a - γ < a - (1 - a) / 4 := by linarith only [hγ', ha1]
    linarith only [this, hc1_inv]
  have hv1_eq : 2 * v₁ * (c₁ / (L * ψ₂)) = Real.log M₁ * (2 * a * (c₁ / ψ₂)) := by
    dsimp [v₁, L]; field_simp [hpi.ne', (by linarith only [hlogM1] : Real.log M₁ ≠ 0)]
  have hmul_exp : (2 * a - γ) * Real.log M₁ ≤ 2 * v₁ * (c₁ / (L * ψ₂)) := by
    rw [hv1_eq, mul_comm (2 * a - γ)]
    exact mul_le_mul_of_nonneg_left h2aγ (by linarith only [hlogM1])
  exact hm_le.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hmul_exp])) (by positivity))

/-- Part B 2-point bound when `γ_R < η_lo`. -/
lemma prob_two_lo_scale_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M T : ℕ} {a b η_lo η_up : ℝ}
    (hM : 25 ≤ M) (ha0 : 7 / 8 ≤ a) (ha1 : a < 1) (hη0 : 0 < η_lo) (_hη1 : η_lo ≤ 1 / 4)
    (hT_eq : T = Nat.ceil (a * Real.log ((M : ℝ) + 1) ^ 2 / Real.pi))
    {p q : ℤ × ℤ} (hpq : p ≠ q) {j : ℕ}
    (hR2d : 2 ^ j < 2 * rnorm (p - q))
    (hγ_lo : Real.log (((M : ℝ) + 1) / (2 ^ j : ℝ) ^ 2) / Real.log ((M : ℝ) + 1) < η_lo)
    (hL_lo : 32 * (8 / η_lo) ^ 2 / (Real.log ((M : ℝ) + 1) / Real.pi) ≤ η_lo / 4 ∧
      2 * Real.log 2 / Real.log ((M : ℝ) + 1) ≤ η_lo / 8) :
    let c₁ := 8 / η_lo
    let M₁ : ℝ := (M : ℝ) + 1
    (ℙ ({ω | path X ω ∈ goodEvent M T b η_lo η_up p} ∩
        {ω | path X ω ∈ goodEvent M T b η_lo η_up q})).toReal ≤
      Real.exp 2 * (1 + 8 * c₁) * Real.exp (-(2 * a - 3 * η_lo) * Real.log M₁) := by
  intro c₁ M₁
  have hpi := Real.pi_pos
  have hc10 : 0 < c₁ := div_pos (by norm_num) hη0
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith only [hM1_ge])).mpr (this.trans hM1_ge)
  set v₁ : ℝ := a * Real.log M₁ ^ 2 / Real.pi
  have hv₁ : 0 ≤ v₁ := by dsimp [v₁]; positivity
  have hsub : ({ω : Ω | path X ω ∈ goodEvent M T b η_lo η_up p} ∩
        {ω | path X ω ∈ goodEvent M T b η_lo η_up q}) ⊆
      {ω | v₁ ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        v₁ ≤ (locShift 0 (path X ω) M (rot q) : ℝ)} := by
    rintro ω ⟨hpω, hqω⟩
    have hv1T : v₁ ≤ (T : ℝ) := by rw [hT_eq]; exact Nat.le_ceil _
    exact ⟨hv1T.trans (by exact_mod_cast hpω.1), hv1T.trans (by exact_mod_cast hqω.1)⟩
  have hprob := prob_locShift_two_le hX hM hpq hc10 hv₁
  have hm_le := (ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hsub)).trans hprob
  set L : ℝ := Real.log M₁ / Real.pi
  set γd : ℝ := max 0 (Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.log M₁)
  set ψ₂ : ℝ := 1 + c₁ * (1 + γd) + 4 * c₁ / L
  have hd1 : 1 ≤ rnorm (p - q) :=
    Nat.pos_of_ne_zero fun h0 ↦ hpq (sub_eq_zero.mp ((rnorm_eq_zero_iff (p - q)).mp h0))
  have hγd_le : γd ≤ η_lo + η_lo / 8 := by
    refine max_le (by positivity) ?_
    have hR1 : 1 ≤ (2 ^ j : ℕ) := Nat.one_le_pow j 2 two_pos
    have hdiv : M₁ / (rnorm (p - q) : ℝ) ^ 2 ≤ 4 * (M₁ / ((2 ^ j : ℕ) : ℝ) ^ 2) := by
      have hd0 : (0 : ℝ) < rnorm (p - q) := by exact_mod_cast hd1
      have hR0 : (0 : ℝ) < (2 ^ j : ℕ) := by exact_mod_cast hR1
      rw [div_le_iff₀ (by positivity)]
      calc M₁ = M₁ / ((2 ^ j : ℕ) : ℝ) ^ 2 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by field_simp [hR0.ne']
        _ ≤ M₁ / ((2 ^ j : ℕ) : ℝ) ^ 2 * (2 * (rnorm (p - q) : ℝ)) ^ 2 := by
            gcongr; exact_mod_cast hR2d.le
        _ = 4 * (M₁ / ((2 ^ j : ℕ) : ℝ) ^ 2) * (rnorm (p - q) : ℝ) ^ 2 := by ring
    have hlog := Real.log_le_log (by positivity) hdiv
    rw [Real.log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow] at hlog
    have h1 : Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.log M₁ ≤
        ((2 : ℕ) : ℝ) * Real.log 2 / Real.log M₁ +
          Real.log (M₁ / ((2 ^ j : ℕ) : ℝ) ^ 2) / Real.log M₁ := by
      calc Real.log (M₁ / (rnorm (p - q) : ℝ) ^ 2) / Real.log M₁
          ≤ (((2 : ℕ) : ℝ) * Real.log 2 + Real.log (M₁ / ((2 ^ j : ℕ) : ℝ) ^ 2)) / Real.log M₁ :=
            div_le_div_of_nonneg_right hlog (by linarith only [hlogM1])
        _ = ((2 : ℕ) : ℝ) * Real.log 2 / Real.log M₁ +
            Real.log (M₁ / ((2 ^ j : ℕ) : ℝ) ^ 2) / Real.log M₁ := add_div _ _ _
    have hlog4 : ((2 : ℕ) : ℝ) * Real.log 2 / Real.log M₁ = 2 * Real.log 2 / Real.log M₁ := by
      push_cast; ring
    have hL2' : 2 * Real.log 2 / Real.log M₁ ≤ η_lo / 8 := hL_lo.2
    have hlt : Real.log (M₁ / ((2 ^ j : ℕ) : ℝ) ^ 2) / Real.log M₁ < η_lo := by
      push_cast; exact hγ_lo
    linarith only [h1, hlog4, hL2', hlt]
  have hL0 : 0 < L := div_pos (by linarith only [hlogM1]) hpi
  have hγd0 : 0 ≤ γd := le_max_left _ _
  have hX : 1 / 2 ≤ 1 + c₁ * (1 + γd) := by
    have : 0 ≤ c₁ * (1 + γd) := mul_nonneg hc10.le (by linarith only [hγd0])
    linarith only [this]
  have hc1_inv : 2 * a - 3 * η_lo ≤ 2 * a * (c₁ / ψ₂) := by
    have h2 : c₁ / (1 + c₁ * (1 + γd)) - 4 * c₁ * (4 * c₁ / L) ≤ c₁ / ψ₂ := by
      have h_eq : ψ₂ = (1 + c₁ * (1 + γd)) + 4 * c₁ / L := rfl
      rw [h_eq]
      exact div_sub_err_le hc10.le hX (by positivity)
    have hlim : 2 * a - 2 * a * (γd + 1 / c₁) ≤ 2 * a * (c₁ / (1 + c₁ * (1 + γd))) := by
      have h1 : c₁ / (1 + c₁ * (1 + γd)) ≥ 1 - (γd + 1 / c₁) := by
        have hden0 : 0 < 1 + c₁ * (1 + γd) := by linarith only [hX]
        have hdiff : 1 - c₁ / (1 + c₁ * (1 + γd)) = (1 + c₁ * γd) / (1 + c₁ * (1 + γd)) := by
          field_simp [hden0.ne']; ring
        have hc1d : c₁ ≤ 1 + c₁ * (1 + γd) := by
          have : 0 ≤ γd := le_max_left _ _
          nlinarith only [hc10, this]
        have hle1 : (1 + c₁ * γd) / (1 + c₁ * (1 + γd)) ≤ (1 + c₁ * γd) / c₁ :=
          div_le_div_of_nonneg_left (by have : 0 ≤ γd := le_max_left _ _; positivity) hc10 hc1d
        have hle2 : (1 + c₁ * γd) / c₁ = γd + 1 / c₁ := by field_simp [hc10.ne']; ring
        linarith only [hdiff, hle1, hle2]
      have := mul_le_mul_of_nonneg_left h1 (by linarith only [ha0] : 0 ≤ 2 * a)
      linarith only [this]
    have herr : 2 * a * (4 * c₁ * (4 * c₁ / L)) ≤ η_lo / 4 := by
      calc 2 * a * (4 * c₁ * (4 * c₁ / L)) = a * (32 * c₁ ^ 2 / L) := by ring
        _ ≤ 1 * (32 * c₁ ^ 2 / L) := mul_le_mul_of_nonneg_right ha1.le (by positivity)
        _ = 32 * c₁ ^ 2 / L := one_mul _
        _ ≤ η_lo / 4 := hL_lo.1
    have hsub_tot : 2 * a * (γd + 1 / c₁) ≤ 2 * (η_lo + η_lo / 8 + η_lo / 8) := by
      have hc1_eq : 1 / c₁ = η_lo / 8 := by dsimp [c₁]; field_simp [hη0.ne']
      have h1 : γd + 1 / c₁ ≤ η_lo + η_lo / 8 + η_lo / 8 := by linarith only [hγd_le, hc1_eq]
      have ha2 : 2 * a ≤ 2 := by linarith only [ha1]
      nlinarith only [h1, ha2, hη0, ha0]
    have h_diff := mul_le_mul_of_nonneg_left h2 (by linarith only [ha0] : 0 ≤ 2 * a)
    linarith only [h_diff, hlim, herr, hsub_tot, hη0]
  have hv1_eq : 2 * v₁ * (c₁ / (L * ψ₂)) = Real.log M₁ * (2 * a * (c₁ / ψ₂)) := by
    dsimp [v₁, L]; field_simp [hpi.ne', (by linarith only [hlogM1] : Real.log M₁ ≠ 0)]
  have hmul_exp : (2 * a - 3 * η_lo) * Real.log M₁ ≤ 2 * v₁ * (c₁ / (L * ψ₂)) := by
    rw [hv1_eq, mul_comm (2 * a - 3 * η_lo)]
    exact mul_le_mul_of_nonneg_left hc1_inv (by linarith only [hlogM1])
  exact hm_le.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hmul_exp])) (by positivity))

/-- Diagonal upper bound `P(goodEvent p) ≤ C * M₁ ^ (-a + (1 - a) / 2)`. -/
lemma prob_goodEvent_diag_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M T : ℕ} {a b η_lo η_up : ℝ}
    (hM : 25 ≤ M) (ha0 : 7 / 8 ≤ a) (ha1 : a < 1)
    (hT_eq : T = Nat.ceil (a * Real.log ((M : ℝ) + 1) ^ 2 / Real.pi))
    (hL_diag : 8 * (4 / (1 - a)) ^ 2 / (Real.log ((M : ℝ) + 1) / Real.pi) ≤ (1 - a) / 4)
    (p : ℤ × ℤ) :
    let c₁ := 4 / (1 - a)
    let M₁ : ℝ := (M : ℝ) + 1
    (ℙ {ω | path X ω ∈ goodEvent M T b η_lo η_up p}).toReal ≤
      Real.exp 2 * (1 + 4 * c₁) * Real.exp (-(a - (1 - a) / 2) * Real.log M₁) := by
  intro c₁ M₁
  have hpi := Real.pi_pos
  have hc10 : 0 < c₁ := div_pos (by norm_num) (by linarith only [ha1])
  have hM1_ge : (26 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 26 ≤ M + 1)
  have hlogM1 : 3 ≤ Real.log M₁ := by
    have : Real.exp 3 ≤ 26 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
        _ ≤ 26 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith only [hM1_ge])).mpr (this.trans hM1_ge)
  set v₁ : ℝ := a * Real.log M₁ ^ 2 / Real.pi
  have hv₁ : 0 ≤ v₁ := by dsimp [v₁]; positivity
  have hsub : {ω : Ω | path X ω ∈ goodEvent M T b η_lo η_up p} ⊆
      {ω | v₁ ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        (0 : ℝ) ≤ ∑ z ∈ Prot p 1 1, (locShift 0 (path X ω) M z : ℝ)} := by
    intro ω hω
    have hv1T : v₁ ≤ (T : ℝ) := by rw [hT_eq]; exact Nat.le_ceil _
    exact ⟨hv1T.trans (by exact_mod_cast hω.1), Finset.sum_nonneg fun z _ ↦ Nat.cast_nonneg _⟩
  have hprob := prob_locShift_bad_P0_le hX hM p (R := 1) le_rfl (by omega) (Or.inl rfl)
    hc10 le_rfl hv₁ le_rfl
  have hm_le := (ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hsub)).trans hprob
  set L : ℝ := Real.log M₁ / Real.pi
  set γ : ℝ := Real.log (M₁ / ((1 : ℕ) : ℝ) ^ 2) / Real.log M₁
  set ψ_x : ℝ := 1 + c₁ + 0 * γ + (2 * c₁ + 2 * 0) / L
  have hψx_eq : ψ_x = (1 + c₁) + 2 * c₁ / L := by dsimp [ψ_x]; ring
  have hL0 : 0 < L := div_pos (by linarith only [hlogM1]) hpi
  have hinv : a - (1 - a) / 2 ≤ a * (c₁ / ψ_x) := by
    have hX : 1 / 2 ≤ 1 + c₁ := by linarith only [hc10]
    have h1 : c₁ / (1 + c₁) - 4 * c₁ * (2 * c₁ / L) ≤ c₁ / ψ_x := by
      rw [hψx_eq]; exact div_sub_err_le hc10.le hX (by positivity)
    have h2 : a - (1 - a) / 4 ≤ a * (c₁ / (1 + c₁)) := by
      have hdiff : a - a * (c₁ / (1 + c₁)) = a / (1 + c₁) := by
        field_simp [(by positivity : 1 + c₁ ≠ 0)]; ring
      have hle : a / (1 + c₁) ≤ (1 - a) / 4 := by
        have hden : 4 / (1 - a) ≤ 1 + c₁ := by dsimp [c₁]; linarith only
        calc a / (1 + c₁) ≤ 1 / (4 / (1 - a)) :=
              div_le_div₀ zero_le_one ha1.le (div_pos (by norm_num) (by linarith only [ha1])) hden
          _ = (1 - a) / 4 := by field_simp [(by linarith only [ha1] : 1 - a ≠ 0)]
      linarith only [hdiff, hle]
    have h3 : a * (4 * c₁ * (2 * c₁ / L)) ≤ (1 - a) / 4 := by
      calc a * (4 * c₁ * (2 * c₁ / L)) = a * (8 * c₁ ^ 2 / L) := by ring
        _ ≤ 1 * (8 * c₁ ^ 2 / L) := mul_le_mul_of_nonneg_right ha1.le (by positivity)
        _ = 8 * c₁ ^ 2 / L := one_mul _
        _ ≤ (1 - a) / 4 := hL_diag
    have h4 := mul_le_mul_of_nonneg_left h1 (by linarith only [ha0] : 0 ≤ a)
    linarith only [h2, h3, h4]
  have hconst : 1 + 4 * c₁ + 4 * (0 : ℝ) = 1 + 4 * c₁ := by ring
  have hm_le' : (ℙ {ω | path X ω ∈ goodEvent M T b η_lo η_up p}).toReal ≤
      Real.exp 2 * (1 + 4 * c₁) * Real.exp (-(v₁ * (c₁ / (L * ψ_x)))) := by
    have hpow0 : -(v₁ * (c₁ / (L * ψ_x)) + 0 * (0 / (((1 : ℕ) : ℝ) * L *
        (1 + (c₁ + 0) * γ + (2 * c₁ + 6 * 0 + 0 * (L + 2) / ((1 : ℕ) : ℝ)) / L)))) =
        -(v₁ * (c₁ / (L * ψ_x))) := by ring
    calc (ℙ {ω | path X ω ∈ goodEvent M T b η_lo η_up p}).toReal
        ≤ Real.exp 2 * (1 + 4 * c₁ + 4 * 0) * _ := hm_le
      _ = Real.exp 2 * (1 + 4 * c₁) * Real.exp (-(v₁ * (c₁ / (L * ψ_x)))) := by
          rw [hconst, hpow0]
  have hmul_exp : (a - (1 - a) / 2) * Real.log M₁ ≤ v₁ * (c₁ / (L * ψ_x)) := by
    have hv1_eq' : v₁ * (c₁ / (L * ψ_x)) = Real.log M₁ * (a * (c₁ / ψ_x)) := by
      dsimp [v₁, L]; field_simp [hpi.ne', (by linarith only [hlogM1] : Real.log M₁ ≠ 0)]
    rw [hv1_eq', mul_comm (a - (1 - a) / 2)]
    exact mul_le_mul_of_nonneg_left hinv (by linarith only [hlogM1])
  exact hm_le'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hmul_exp])) (by positivity))

lemma exp_mul_ge_mul_pow {α C x : ℝ} (hα : 0 < α) (_hC : 0 ≤ C) (hx1 : 1 ≤ x)
    (hxC : C * (Nat.factorial 7 : ℝ) / α ^ 7 ≤ x) :
    C * x ^ 6 ≤ Real.exp (α * x) := by
  have hx0 : 0 ≤ α * x := mul_nonneg hα.le (by linarith only [hx1])
  have hpow := Real.pow_div_factorial_le_exp (α * x) hx0 7
  have h1 : C * x ^ 6 ≤ (α * x) ^ 7 / (Nat.factorial 7 : ℝ) := by
    have hfac : (0 : ℝ) < Nat.factorial 7 := by positivity
    rw [le_div_iff₀ hfac, mul_pow]
    have hmul : C * (Nat.factorial 7 : ℝ) ≤ α ^ 7 * x := by
      rwa [div_le_iff₀' (pow_pos hα 7)] at hxC
    calc C * x ^ 6 * (Nat.factorial 7 : ℝ) = (C * (Nat.factorial 7 : ℝ)) * x ^ 6 := by ring
      _ ≤ (α ^ 7 * x) * x ^ 6 := mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = α ^ 7 * x ^ 7 := by ring
  exact h1.trans hpow

/-- First moment lower bound on `goodEvent` over `Q0 Rmax`. -/
lemma goodEvent_first_moment_ge {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M M₀ Rmax T : ℕ} {a η_lo η_up η_1 : ℝ}
    (hM : 100 ≤ M) (ha0 : 7 / 8 ≤ a) (ha1 : a < 1)
    (hηlo0 : 0 < η_lo) (hηlo1 : η_lo ≤ 1)
    (hη10 : 0 < η_1) (hη1_le : η_1 ≤ 1 / 4)
    (hT_eq : T = Nat.ceil (a * Real.log ((M : ℝ) + 1) ^ 2 / Real.pi))
    (hM0_ge : (M : ℝ) / (8 * Real.log ((M : ℝ) + 1)) ≤ (M₀ : ℝ))
    (hM0_le : (M₀ : ℝ) ≤ (M : ℝ) / (4 * Real.log ((M : ℝ) + 1)))
    (hM0_val : 200 ≤ M₀)
    (hRmax1 : 1 ≤ Rmax)
    (hRmax_le : (Rmax : ℝ) ≤ Real.sqrt (M₀ : ℝ) / 1024)
    (hlog_big : Real.log (8 * Real.log ((M : ℝ) + 1)) + 3 * Real.pi ≤ η_1 * Real.log ((M : ℝ) + 1))
    (herrA :
      let s_p := 1 + (1 - a) / 8
      let b := a * s_p ^ 2
      let ρ := (s_p ^ 2 - 1) / 2
      let m := ρ * η_lo * (b - a * (1 + ρ)) / (1 + ρ) ^ 2
      let c₁ := 4 * (a + b) * (1 + ρ) ^ 2 / (ρ * η_lo * (b - a * (1 + ρ)))
      let c₃ := ρ * c₁
      let M₁ : ℝ := (M : ℝ) + 1
      let M₂ : ℝ := ((2 * M : ℕ) : ℝ) + 1
      let L₂ : ℝ := Real.log M₂ / Real.pi
      16 * (1 + c₁ + c₃) * (2 * Real.log 2 + 1) / Real.log M₁ +
          4 * (c₁ * (2 * c₁ + 2 * c₃) + b * c₃ * (2 * c₁ + 7 * c₃)) / L₂ ≤ m / 4 ∧
        (∀ j ∈ goodScales M η_lo η_up, (L₂ + 2) / ((2 ^ j : ℕ) : ℝ) ≤ 1) ∧
        32 * Real.log M₁ ^ 2 * (Real.exp 2 * (1 + 4 * c₁ + 4 * c₃)) *
            Real.exp (-(a + m / 2) * Real.log M₁) ≤
          Real.exp (-(a + 2 * η_1) * Real.log M₁)) :
    let s_p := 1 + (1 - a) / 8
    let b := a * s_p ^ 2
    let M₁ : ℝ := (M : ℝ) + 1
    (Rmax : ℝ) ^ 2 * (1 / (8 * Real.log M₁)) * Real.exp (-(a + 2 * η_1) * Real.log M₁) ≤
      ∑ p ∈ Q0 Rmax, (ℙ {ω | path X ω ∈ goodEvent M T b η_lo η_up p}).toReal := by
  intro s_p b M₁
  let ρ := (s_p ^ 2 - 1) / 2
  let m := ρ * η_lo * (b - a * (1 + ρ)) / (1 + ρ) ^ 2
  let c₁ := 4 * (a + b) * (1 + ρ) ^ 2 / (ρ * η_lo * (b - a * (1 + ρ)))
  let c₃ := ρ * c₁
  have hL1_pos : 0 < Real.log M₁ := by
    have : (101 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 101 ≤ M + 1)
    exact Real.log_pos (by linarith only [this])
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hgs_card : ((goodScales M η_lo η_up).card : ℝ) ≤ 2 * Real.log M₁ := by
    have h1 : (goodScales M η_lo η_up).card ≤ Nat.log 2 (M + 1) + 1 :=
      (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    have h2 : ((Nat.log 2 (M + 1) : ℕ) : ℝ) * Real.log 2 ≤ Real.log M₁ := by
      have hpow : (2 ^ Nat.log 2 (M + 1) : ℕ) ≤ M + 1 := Nat.pow_log_le_self 2 (by omega)
      have hle : ((2 ^ Nat.log 2 (M + 1) : ℕ) : ℝ) ≤ M₁ := by
        dsimp [M₁]; exact_mod_cast hpow
      have hlog := Real.log_le_log (by positivity) hle
      rwa [Nat.cast_pow, Real.log_pow] at hlog
    have h3 : (Nat.log 2 (M + 1) : ℝ) ≤ Real.log M₁ / Real.log 2 :=
      (le_div_iff₀ hlog2_pos).mpr h2
    have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hexp : (Real.exp (1 / 2) : ℝ) ^ 2 ≤ 2 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
        have := Real.exp_one_lt_d9; linarith only [this]
      have : Real.exp (1 / 2) ≤ 2 := by nlinarith only [hexp, Real.exp_pos (1 / 2)]
      exact (Real.le_log_iff_exp_le two_pos).mpr this
    have hL1_ge4 : 4 ≤ Real.log M₁ := by
      have hM101 : (101 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 101 ≤ M + 1)
      have hexp : Real.exp 4 ≤ 101 := by
        have := Real.exp_one_lt_d9
        calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 4
          _ ≤ 101 := by norm_num
      exact (Real.le_log_iff_exp_le (by linarith only [hM101])).mpr (hexp.trans hM101)
    have h1r : ((goodScales M η_lo η_up).card : ℝ) ≤ (Nat.log 2 (M + 1) : ℝ) + 1 := by
      exact_mod_cast h1
    have hdiv2 : Real.log M₁ / Real.log 2 ≤ 2 * Real.log M₁ := by
      rw [div_le_iff₀ hlog2_pos]; nlinarith only [hlog2_ge, hL1_pos]
    have : (Nat.log 2 (M + 1) : ℝ) ≤ 2 * Real.log M₁ - 1 := by
      have hdiv3 : Real.log M₁ / Real.log 2 ≤ (7 / 4 : ℝ) * Real.log M₁ := by
        rw [div_le_iff₀ hlog2_pos]
        have h_gt : (0.6 : ℝ) ≤ Real.log 2 := by
          have hexp : Real.exp 0.6 ≤ 2 := by
            have h35 : Real.exp (3 / 5 : ℝ) ≤ 2 := by
              have h3 : Real.exp 3 ≤ 32 := by
                have := Real.exp_one_lt_d9
                calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
                  _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
                  _ ≤ 32 := by norm_num
              have hp : (Real.exp (3 / 5 : ℝ)) ^ 5 = Real.exp 3 := by
                rw [← Real.exp_nat_mul]; norm_num
              by_contra hlt; push Not at hlt
              have := pow_lt_pow_left₀ hlt (by norm_num) (by decide : 5 ≠ 0)
              rw [hp] at this; norm_num at this; linarith only [h3, this]
            rw [show (0.6 : ℝ) = 3 / 5 by norm_num]; exact h35
          exact (Real.le_log_iff_exp_le two_pos).mpr hexp
        nlinarith only [h_gt, hL1_pos]
      linarith only [h3, hdiv3, hL1_ge4]
    linarith only [h1r, this]
  have hterm : ∀ p ∈ Q0 Rmax,
      (1 / (8 * Real.log M₁)) * Real.exp (-(a + 2 * η_1) * Real.log M₁) ≤
        (ℙ {ω | path X ω ∈ goodEvent M T b η_lo η_up p}).toReal := by
    intro p hp
    have hhit := prob_hit_single_ge hX hM ha0 ha1 hη10 hη1_le hT_eq hM0_ge hM0_le hM0_val
      hRmax_le hlog_big hp
    let Bad : ℕ → ℤ → Set Ω := fun j σ ↦
      {ω | (T : ℝ) ≤ (locShift 0 (path X ω) M (rot p) : ℝ) ∧
        perimCap M (2 ^ j) b < ∑ z ∈ Prot p (2 ^ j) σ, (locShift 0 (path X ω) (2 * M) z : ℝ)}
    have hsub : {ω : Ω | T ≤ locShift 0 (path X ω) M (rot p)} ⊆
        {ω | path X ω ∈ goodEvent M T b η_lo η_up p} ∪
          ⋃ j ∈ goodScales M η_lo η_up, ⋃ σ ∈ ({1, -1} : Finset ℤ), Bad j σ := by
      intro ω hω
      by_cases hgood : path X ω ∈ goodEvent M T b η_lo η_up p
      · exact Or.inl hgood
      · refine Or.inr ?_
        simp only [goodEvent, Set.mem_ofPred_eq, not_and, not_forall, not_le] at hgood
        obtain ⟨j, hj, σ, hσ, hbad⟩ := hgood hω
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨j, hj, σ, hσ, by exact_mod_cast hω, hbad⟩
    have hm_le := measure_mono (μ := ℙ) hsub
    have hunion := hm_le.trans (measure_union_le _ _)
    have hbi1 : ℙ (⋃ j ∈ goodScales M η_lo η_up, ⋃ σ ∈ ({1, -1} : Finset ℤ), Bad j σ) ≤
        ∑ j ∈ goodScales M η_lo η_up, ∑ σ ∈ ({1, -1} : Finset ℤ), ℙ (Bad j σ) :=
      (measure_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum fun j _ ↦ measure_biUnion_finset_le _ _)
    have hm_tot := hunion.trans (add_le_add le_rfl hbi1)
    have hr := ENNReal.toReal_mono (by
      rw [ENNReal.add_ne_top]
      exact ⟨measure_ne_top ℙ _, ENNReal.sum_ne_top.mpr fun j _ ↦
        ENNReal.sum_ne_top.mpr fun σ _ ↦ measure_ne_top ℙ _⟩) hm_tot
    rw [ENNReal.toReal_add (measure_ne_top ℙ _) (ENNReal.sum_ne_top.mpr fun j _ ↦
      ENNReal.sum_ne_top.mpr fun σ _ ↦ measure_ne_top ℙ _),
      ENNReal.toReal_sum (fun j _ ↦ ENNReal.sum_ne_top.mpr fun σ _ ↦ measure_ne_top ℙ _)] at hr
    have hbad_sum : (∑ j ∈ goodScales M η_lo η_up, (∑ σ ∈ ({1, -1} : Finset ℤ), ℙ (Bad j σ)).toReal) ≤
        (1 / (8 * Real.log M₁)) * Real.exp (-(a + 2 * η_1) * Real.log M₁) := by
      have hbad_each : ∀ j ∈ goodScales M η_lo η_up, ∀ σ ∈ ({1, -1} : Finset ℤ),
          (ℙ (Bad j σ)).toReal ≤
            Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) * Real.exp (-(a + m / 2) * Real.log M₁) := by
        intro j hj σ hσ
        have hσ' : σ = 1 ∨ σ = -1 := by simpa using hσ
        exact prob_bad_perim_le hX (by omega : 25 ≤ M) ha0 ha1 hηlo0 hηlo1 hT_eq hj hσ' p
          herrA.1 (herrA.2.1 j hj)
      have hsum_bd : (∑ j ∈ goodScales M η_lo η_up, (∑ σ ∈ ({1, -1} : Finset ℤ), ℙ (Bad j σ)).toReal) ≤
          ((goodScales M η_lo η_up).card : ℝ) * 2 *
            (Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) * Real.exp (-(a + m / 2) * Real.log M₁)) := by
        calc ∑ j ∈ goodScales M η_lo η_up, (∑ σ ∈ ({1, -1} : Finset ℤ), ℙ (Bad j σ)).toReal
            = ∑ j ∈ goodScales M η_lo η_up, ∑ σ ∈ ({1, -1} : Finset ℤ), (ℙ (Bad j σ)).toReal := by
                refine Finset.sum_congr rfl fun j _ ↦ ?_
                exact ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top ℙ _)
          _ ≤ ∑ j ∈ goodScales M η_lo η_up, ∑ _ ∈ ({1, -1} : Finset ℤ),
                (Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) * Real.exp (-(a + m / 2) * Real.log M₁)) :=
                Finset.sum_le_sum fun j hj ↦ Finset.sum_le_sum fun σ hσ ↦ hbad_each j hj σ hσ
          _ = ((goodScales M η_lo η_up).card : ℝ) * 2 *
                (Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) * Real.exp (-(a + m / 2) * Real.log M₁)) := by
                simp only [Finset.sum_const, nsmul_eq_mul, show ({1, -1} : Finset ℤ).card = 2 by decide]
                push_cast; ring
      have hc13_nn : 0 ≤ Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) * Real.exp (-(a + m / 2) * Real.log M₁) := by
        obtain ⟨hρ0, _, hc10, _⟩ := partA_limit_margin (by linarith only [ha0] : 0 < a) ha1 hηlo0 hηlo1
        change 0 < ρ at hρ0
        change 0 < c₁ at hc10
        have hc30 : 0 ≤ c₃ := mul_nonneg hρ0.le hc10.le
        exact mul_nonneg (mul_nonneg (Real.exp_pos 2).le (by linarith only [hc10, hc30])) (Real.exp_pos _).le
      calc (∑ j ∈ goodScales M η_lo η_up, (∑ σ ∈ ({1, -1} : Finset ℤ), ℙ (Bad j σ)).toReal)
          ≤ (2 * Real.log M₁) * 2 *
              (Real.exp 2 * (1 + 4 * c₁ + 4 * c₃) * Real.exp (-(a + m / 2) * Real.log M₁)) :=
            hsum_bd.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hgs_card zero_le_two) hc13_nn)
        _ = (1 / (8 * Real.log M₁)) *
              (32 * Real.log M₁ ^ 2 * (Real.exp 2 * (1 + 4 * c₁ + 4 * c₃)) *
                Real.exp (-(a + m / 2) * Real.log M₁)) := by
            field_simp [hL1_pos.ne']; ring
        _ ≤ (1 / (8 * Real.log M₁)) * Real.exp (-(a + 2 * η_1) * Real.log M₁) :=
            mul_le_mul_of_nonneg_left herrA.2.2 (by positivity)
    have hhalf : (1 / (8 * Real.log M₁)) * Real.exp (-(a + 2 * η_1) * Real.log M₁) =
        (1 / (4 * Real.log M₁)) * Real.exp (-(a + 2 * η_1) * Real.log M₁) -
        (1 / (8 * Real.log M₁)) * Real.exp (-(a + 2 * η_1) * Real.log M₁) := by
      field_simp [hL1_pos.ne']; ring
    linarith only [hhit, hr, hbad_sum, hhalf]
  calc (Rmax : ℝ) ^ 2 * (1 / (8 * Real.log M₁)) * Real.exp (-(a + 2 * η_1) * Real.log M₁)
      = ∑ _ ∈ Q0 Rmax, (1 / (8 * Real.log M₁)) * Real.exp (-(a + 2 * η_1) * Real.log M₁) := by
          rw [Finset.sum_const, Q0_card hRmax1, nsmul_eq_mul, Nat.cast_pow]; ring
    _ ≤ ∑ p ∈ Q0 Rmax, (ℙ {ω | path X ω ∈ goodEvent M T b η_lo η_up p}).toReal :=
          Finset.sum_le_sum hterm

lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ y ∈ s.biUnion t, f y ≤ ∑ x ∈ s, ∑ y ∈ t x, f y := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert has]
    have h_union : ∑ y ∈ t a ∪ s.biUnion t, f y ≤ ∑ y ∈ t a, f y + ∑ y ∈ s.biUnion t, f y := by
      have h_eq : t a ∪ s.biUnion t = t a ∪ (s.biUnion t \ t a) := by
        ext y; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
      have h1 : ∑ y ∈ t a ∪ s.biUnion t, f y =
          ∑ y ∈ t a, f y + ∑ y ∈ (s.biUnion t) \ t a, f y := by
        rw [h_eq, Finset.sum_union disjoint_sdiff_self_right]
      have h2 : ∑ y ∈ (s.biUnion t) \ t a, f y ≤ ∑ y ∈ s.biUnion t, f y :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun y _ _ ↦ hf y
      linarith only [h1, h2]
    exact h_union.trans (add_le_add le_rfl ih)

set_option maxHeartbeats 800000 in
/-- Second moment upper bound on `goodEvent` over `Q0 Rmax ×ˢ Q0 Rmax`. -/
lemma goodEvent_second_moment_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M Rmax T : ℕ} {a η_lo : ℝ}
    (hM : 100 ≤ M) (ha0 : 7 / 8 ≤ a) (ha1 : a < 1) (hη0 : 0 < η_lo) (hη1 : η_lo ≤ 1 / 4)
    (hT_eq : T = Nat.ceil (a * Real.log ((M : ℝ) + 1) ^ 2 / Real.pi))
    (hRmax1 : 1 ≤ Rmax) (h36R : 36 * Rmax ^ 2 ≤ M + 1)
    (hL_conds :
      let t := (1 - a) / 8
      let η_up := (1 - a) / 2
      let m_B := a * t ^ 2 * η_lo
      let c₁B := 16 / (η_up ^ 2 * m_B)
      let M₁ : ℝ := (M : ℝ) + 1
      let L : ℝ := Real.log M₁ / Real.pi
      48 * c₁B ≤ L ∧
        8 * (16 * c₁B ^ 2 + 16 * c₁B ^ 2 * 22 * c₁B) / L ≤ m_B / 4 ∧
        32 * (16 / (1 - a)) ^ 2 / L ≤ (1 - a) / 8 ∧
        32 * (8 / η_lo) ^ 2 / L ≤ η_lo / 4 ∧
        2 * Real.log 2 / Real.log M₁ ≤ η_lo / 8 ∧
        8 * (4 / (1 - a)) ^ 2 / L ≤ (1 - a) / 4 ∧
        16 / η_up ^ 2 + 16 ≤ Real.log M₁) :
    let t := (1 - a) / 8
    let s_p := 1 + t
    let b := a * s_p ^ 2
    let η_up := (1 - a) / 2
    let m_B := a * t ^ 2 * η_lo
    let c₁B := 16 / (η_up ^ 2 * m_B)
    let C_tot := Real.exp 2 * (1 + 4 * (4 / (1 - a))) +
      9 * Real.exp 2 * (1 + 8 * max c₁B (max (16 / (1 - a)) (8 / η_lo)))
    let M₁ : ℝ := (M : ℝ) + 1
    ∑ pq ∈ Q0 Rmax ×ˢ Q0 Rmax,
        (ℙ ({ω | path X ω ∈ goodEvent M T b η_lo η_up pq.1} ∩
          {ω | path X ω ∈ goodEvent M T b η_lo η_up pq.2})).toReal ≤
      (1 + 2 * Real.log M₁) * C_tot * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) := by
  intro t s_p b η_up m_B c₁B C_tot M₁
  let E : ℤ × ℤ → Set Ω := fun p ↦ {ω | path X ω ∈ goodEvent M T b η_lo η_up p}
  have hM1_ge : (101 : ℝ) ≤ M₁ := by dsimp [M₁]; exact_mod_cast (by omega : 101 ≤ M + 1)
  have hlogM1_ge4 : 4 ≤ Real.log M₁ := by
    have hexp : Real.exp 4 ≤ 101 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 4
        _ ≤ 101 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith only [hM1_ge])).mpr (hexp.trans hM1_ge)
  have hlogM1_pos : 0 < Real.log M₁ := by linarith only [hlogM1_ge4]
  have hR2_le_M1 : (Rmax : ℝ) ^ 2 ≤ M₁ := by
    dsimp [M₁]; exact_mod_cast (by nlinarith : Rmax ^ 2 ≤ M + 1)
  have hsplit : ∑ pq ∈ Q0 Rmax ×ˢ Q0 Rmax, (ℙ (E pq.1 ∩ E pq.2)).toReal =
      (∑ pq ∈ (Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2), (ℙ (E pq.1 ∩ E pq.2)).toReal) +
      (∑ pq ∈ (Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 ≠ pq.2), (ℙ (E pq.1 ∩ E pq.2)).toReal) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  let c₁D := 4 / (1 - a)
  have hc1D_pos : 0 < c₁D := div_pos (by norm_num) (by linarith only [ha1])
  have hdiag_le : ∑ pq ∈ (Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2),
        (ℙ (E pq.1 ∩ E pq.2)).toReal ≤
      Real.exp 2 * (1 + 4 * c₁D) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) := by
    have hcard_le : ((Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2)).card ≤ Rmax ^ 2 := by
      calc ((Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2)).card
          ≤ ((Q0 Rmax).map ⟨fun p ↦ (p, p), fun _ _ h ↦ (Prod.ext_iff.mp h).1⟩).card := by
            refine Finset.card_le_card fun pq hpq ↦ ?_
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map] at hpq ⊢
            exact ⟨pq.1, hpq.1.1, Prod.ext rfl hpq.2⟩
        _ = (Q0 Rmax).card := Finset.card_map _
        _ = Rmax ^ 2 := Q0_card hRmax1
    have heach : ∀ pq ∈ (Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2),
        (ℙ (E pq.1 ∩ E pq.2)).toReal ≤
          Real.exp 2 * (1 + 4 * c₁D) * Real.exp (-(a - (1 - a) / 2) * Real.log M₁) := by
      intro pq hpq
      have heq := (Finset.mem_filter.mp hpq).2
      rw [heq, Set.inter_self]
      exact prob_goodEvent_diag_le hX (by omega : 25 ≤ M) ha0 ha1 hT_eq hL_conds.2.2.2.2.2.1 pq.2
    have hconst_nn : 0 ≤ Real.exp 2 * (1 + 4 * c₁D) := by positivity
    calc ∑ pq ∈ (Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2), (ℙ (E pq.1 ∩ E pq.2)).toReal
        ≤ ∑ _ ∈ (Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2),
            Real.exp 2 * (1 + 4 * c₁D) * Real.exp (-(a - (1 - a) / 2) * Real.log M₁) :=
          Finset.sum_le_sum heach
      _ = (((Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2)).card : ℝ) *
            (Real.exp 2 * (1 + 4 * c₁D) * Real.exp (-(a - (1 - a) / 2) * Real.log M₁)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M₁ * (Real.exp 2 * (1 + 4 * c₁D) * Real.exp (-(a - (1 - a) / 2) * Real.log M₁)) := by
          have hc : (((Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2)).card : ℝ) ≤ M₁ := by
            have h1 : (((Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 = pq.2)).card : ℝ) ≤ (Rmax : ℝ) ^ 2 := by
              exact_mod_cast hcard_le
            exact h1.trans hR2_le_M1
          exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = Real.exp 2 * (1 + 4 * c₁D) *
            (Real.exp (Real.log M₁) * Real.exp (-(a - (1 - a) / 2) * Real.log M₁)) := by
          rw [Real.exp_log (by linarith only [hM1_ge])]; ring
      _ = Real.exp 2 * (1 + 4 * c₁D) * Real.exp ((1 - a + (1 - a) / 2) * Real.log M₁) := by
          rw [← Real.exp_add]; congr 2; ring
      _ ≤ Real.exp 2 * (1 + 4 * c₁D) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hconst_nn
          have hgap : 1 - a + (1 - a) / 2 ≤ 2 - 2 * a + 3 * η_lo := by linarith only [ha1, hη0]
          exact mul_le_mul_of_nonneg_right hgap hlogM1_pos.le
  let Ksc := Nat.clog 2 Rmax + 1
  let scalePairs : ℕ → Finset ((ℤ × ℤ) × (ℤ × ℤ)) := fun j ↦
    (Q0 Rmax ×ˢ Q0 Rmax).filter fun pq ↦
      pq.1 ≠ pq.2 ∧ rnorm (pq.1 - pq.2) ≤ 2 ^ j ∧ 2 ^ j < 2 * rnorm (pq.1 - pq.2)
  have hsub_off : (Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 ≠ pq.2) ⊆
      (Finset.range Ksc).biUnion scalePairs := by
    rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hpq
    have hd1 : 1 ≤ rnorm (p - q) :=
      Nat.pos_of_ne_zero fun h0 ↦ hpq.2 (sub_eq_zero.mp ((rnorm_eq_zero_iff (p - q)).mp h0))
    have hd_lt : rnorm (p - q) < Rmax := Q0_sub_rnorm_lt hpq.1.1 hpq.1.2
    obtain ⟨j, hj1, hj2⟩ := dyadic_scale_exists hd1
    have hj_eq : j = Nat.clog 2 (rnorm (p - q)) := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hbad : 2 ^ j < rnorm (p - q) :=
          (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp hlt
        omega
      · have hgt2 : Nat.clog 2 (rnorm (p - q)) + 1 ≤ j := hgt
        have hbad : rnorm (p - q) ≤ 2 ^ Nat.clog 2 (rnorm (p - q)) := Nat.le_pow_clog (by decide) _
        have hpow : 2 * rnorm (p - q) ≤ 2 * 2 ^ Nat.clog 2 (rnorm (p - q)) := Nat.mul_le_mul_left 2 hbad
        have hpow2 : 2 * 2 ^ Nat.clog 2 (rnorm (p - q)) ≤ 2 ^ j := by
          calc 2 * 2 ^ Nat.clog 2 (rnorm (p - q)) = 2 ^ (Nat.clog 2 (rnorm (p - q)) + 1) := by
                rw [pow_succ']
            _ ≤ 2 ^ j := Nat.pow_le_pow_right two_pos hgt2
        omega
    have hjK : j ∈ Finset.range Ksc := by
      rw [Finset.mem_range, hj_eq]
      exact Nat.lt_succ_of_le (Nat.clog_mono_right 2 hd_lt.le)
    rw [Finset.mem_biUnion]
    exact ⟨j, hjK, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hpq.1, hpq.2, hj1, hj2⟩⟩
  have hKsc_le : (Ksc : ℝ) ≤ 2 * Real.log M₁ := by
    have hc_le : (Nat.clog 2 Rmax : ℝ) ≤ (5 / 3 : ℝ) * Real.log M₁ := by
      rcases eq_or_lt_of_le hRmax1 with h1 | hgt1
      · rw [← h1, Nat.clog_one_right, Nat.cast_zero]; exact mul_nonneg (by norm_num) hlogM1_pos.le
      · have hc0 := Nat.clog_pos (by decide : 1 < 2) hgt1
        have hpred : 2 ^ (Nat.clog 2 Rmax - 1) < Rmax :=
          (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp (Nat.sub_lt hc0 one_pos)
        have h2j : (2 : ℝ) ^ Nat.clog 2 Rmax ≤ M₁ := by
          have : 2 ^ Nat.clog 2 Rmax < 2 * Rmax := by
            calc 2 ^ Nat.clog 2 Rmax = 2 * 2 ^ (Nat.clog 2 Rmax - 1) := by rw [← pow_succ', Nat.sub_add_cancel hc0]
              _ < 2 * Rmax := Nat.mul_lt_mul_of_pos_left hpred two_pos
          have : 2 ^ Nat.clog 2 Rmax ≤ M + 1 := by nlinarith
          dsimp [M₁]; exact_mod_cast this
        have hlog := Real.log_le_log (by positivity) h2j
        rw [Real.log_pow] at hlog
        have hlog2_ge : (3 / 5 : ℝ) ≤ Real.log 2 := by
          have h35 : Real.exp (3 / 5 : ℝ) ≤ 2 := by
            have h3 : Real.exp 3 ≤ 32 := by
              have := Real.exp_one_lt_d9
              calc Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
                _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le this.le 3
                _ ≤ 32 := by norm_num
            have hp : (Real.exp (3 / 5 : ℝ)) ^ 5 = Real.exp 3 := by
              rw [← Real.exp_nat_mul]; norm_num
            by_contra hlt; push Not at hlt
            have := pow_lt_pow_left₀ hlt (by norm_num) (by decide : 5 ≠ 0)
            rw [hp] at this; norm_num at this; linarith only [h3, this]
          exact (Real.le_log_iff_exp_le two_pos).mpr h35
        have hc_nn : (0 : ℝ) ≤ (Nat.clog 2 Rmax : ℝ) := Nat.cast_nonneg _
        nlinarith only [hlog, hlog2_ge, hc_nn]
    have hK : (Ksc : ℝ) = (Nat.clog 2 Rmax : ℝ) + 1 := by dsimp [Ksc]; push_cast; ring
    linarith only [hK, hc_le, hlogM1_ge4]
  let cM := max c₁B (max (16 / (1 - a)) (8 / η_lo))
  have hcM0 : 0 ≤ cM := le_trans (by dsimp [c₁B, η_up, m_B, t]; positivity) (le_max_left _ _)
  have hscale_le : ∀ j ∈ Finset.range Ksc,
      ∑ pq ∈ scalePairs j, (ℙ (E pq.1 ∩ E pq.2)).toReal ≤
        9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) := by
    intro j hj
    rw [Finset.mem_range] at hj
    set R : ℕ := 2 ^ j
    have hR1 : 1 ≤ R := Nat.one_le_pow j 2 two_pos
    have hR_lt : R < 2 * Rmax := by
      have hj0' : 2 ^ Nat.clog 2 Rmax < 2 * Rmax := by
        rcases eq_or_lt_of_le hRmax1 with h1 | hgt1
        · rw [← h1]; norm_num
        · have hc0 := Nat.clog_pos (by decide : 1 < 2) hgt1
          have hpred := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp (Nat.sub_lt hc0 one_pos)
          calc 2 ^ Nat.clog 2 Rmax = 2 * 2 ^ (Nat.clog 2 Rmax - 1) := by rw [← pow_succ', Nat.sub_add_cancel hc0]
            _ < 2 * Rmax := Nat.mul_lt_mul_of_pos_left hpred two_pos
      have hpow : 2 ^ j ≤ 2 ^ Nat.clog 2 Rmax := Nat.pow_le_pow_right two_pos (Nat.lt_succ_iff.mp hj)
      exact lt_of_le_of_lt hpow hj0'
    have h3R : (3 * R) ^ 2 ≤ M + 1 := by
      have : 3 * R ≤ 6 * Rmax := by omega
      have : (3 * R) ^ 2 ≤ 36 * Rmax ^ 2 := by nlinarith
      omega
    set γ : ℝ := Real.log (M₁ / (R : ℝ) ^ 2) / Real.log M₁
    have hcard_bd : ((scalePairs j).card : ℝ) ≤ 9 * (Rmax : ℝ) ^ 2 * (R : ℝ) ^ 2 := by
      have hsub_sp : scalePairs j ⊆ (Q0 Rmax ×ˢ Q0 Rmax).filter fun pq ↦ rnorm (pq.1 - pq.2) ≤ R :=
        fun pq hpq ↦ by
          have := Finset.mem_filter.mp hpq
          exact Finset.mem_filter.mpr ⟨this.1, this.2.2.1⟩
      exact_mod_cast (Finset.card_le_card hsub_sp).trans (dyadic_pairs_card_le hR1)
    have hMR_exp : (Rmax : ℝ) ^ 2 * (R : ℝ) ^ 2 ≤ Real.exp ((2 - γ) * Real.log M₁) := by
      have hR0 : (0 : ℝ) < R := by exact_mod_cast hR1
      have hγ_eq : (2 - γ) * Real.log M₁ = Real.log (M₁ * (R : ℝ) ^ 2) := by
        have h1 : γ * Real.log M₁ = Real.log (M₁ / (R : ℝ) ^ 2) := by
          dsimp [γ]; field_simp [hlogM1_pos.ne']
        calc (2 - γ) * Real.log M₁ = 2 * Real.log M₁ - γ * Real.log M₁ := by ring
          _ = Real.log (M₁ ^ 2) - Real.log (M₁ / (R : ℝ) ^ 2) := by rw [Real.log_pow, h1]; push_cast; ring
          _ = Real.log (M₁ ^ 2 / (M₁ / (R : ℝ) ^ 2)) :=
              (Real.log_div (by positivity) (by positivity)).symm
          _ = Real.log (M₁ * (R : ℝ) ^ 2) := by
              congr 1; field_simp [(by linarith only [hM1_ge] : M₁ ≠ 0), hR0.ne']
      rw [hγ_eq, Real.exp_log (by positivity)]
      exact mul_le_mul_of_nonneg_right hR2_le_M1 (by positivity)
    by_cases hlo : γ < η_lo
    · have hcard_tot : ((scalePairs j).card : ℝ) ≤ Real.exp (2 * Real.log M₁) := by
        have h1 : (scalePairs j).card ≤ Rmax ^ 4 := by
          calc (scalePairs j).card ≤ (Q0 Rmax ×ˢ Q0 Rmax).card := Finset.card_le_card (Finset.filter_subset _ _)
            _ = Rmax ^ 2 * Rmax ^ 2 := by rw [Finset.card_product, Q0_card hRmax1]
            _ = Rmax ^ 4 := by ring
        have h1' : ((scalePairs j).card : ℝ) ≤ (Rmax : ℝ) ^ 4 := by exact_mod_cast h1
        have h2 : (Rmax : ℝ) ^ 4 ≤ M₁ ^ 2 := by nlinarith only [hR2_le_M1]
        rw [show 2 * Real.log M₁ = Real.log (M₁ ^ 2) by rw [Real.log_pow]; push_cast; ring,
          Real.exp_log (by positivity)]
        exact h1'.trans h2
      have heach : ∀ pq ∈ scalePairs j, (ℙ (E pq.1 ∩ E pq.2)).toReal ≤
          Real.exp 2 * (1 + 8 * cM) * Real.exp (-(2 * a - 3 * η_lo) * Real.log M₁) := by
        intro pq hpq
        have hf := Finset.mem_filter.mp hpq
        have h2 := prob_two_lo_scale_le (b := b) (η_up := η_up) hX (by omega : 25 ≤ M) ha0 ha1 hη0 hη1 hT_eq hf.2.1
          hf.2.2.2 (by dsimp [γ, M₁, R] at hlo; push_cast at hlo; exact hlo)
          ⟨hL_conds.2.2.2.1, hL_conds.2.2.2.2.1⟩
        have hc_le : 8 / η_lo ≤ cM := le_trans (le_max_right _ _) (le_max_right _ _)
        have hfac : Real.exp 2 * (1 + 8 * (8 / η_lo)) ≤ Real.exp 2 * (1 + 8 * cM) := by
          gcongr
        exact h2.trans (mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le)
      calc ∑ pq ∈ scalePairs j, (ℙ (E pq.1 ∩ E pq.2)).toReal
          ≤ ((scalePairs j).card : ℝ) *
              (Real.exp 2 * (1 + 8 * cM) * Real.exp (-(2 * a - 3 * η_lo) * Real.log M₁)) := by
            calc _ ≤ ∑ _ ∈ scalePairs j, _ := Finset.sum_le_sum heach
              _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Real.exp (2 * Real.log M₁) *
              (Real.exp 2 * (1 + 8 * cM) * Real.exp (-(2 * a - 3 * η_lo) * Real.log M₁)) :=
            mul_le_mul_of_nonneg_right hcard_tot (by positivity)
        _ = Real.exp 2 * (1 + 8 * cM) *
              (Real.exp (2 * Real.log M₁) * Real.exp (-(2 * a - 3 * η_lo) * Real.log M₁)) := by ring
        _ = Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) := by
            rw [← Real.exp_add]; congr 2; ring
        _ ≤ 9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) := by
            have : 0 ≤ Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) := by
              positivity
            linarith only [this]
    · push Not at hlo
      by_cases hhi : 1 - η_up < γ
      · have heach : ∀ pq ∈ scalePairs j, (ℙ (E pq.1 ∩ E pq.2)).toReal ≤
            Real.exp 2 * (1 + 8 * cM) * Real.exp (-(2 * a - γ) * Real.log M₁) := by
          intro pq hpq
          have hf := Finset.mem_filter.mp hpq
          have h2 := prob_two_hi_scale_le (b := b) (η_lo := η_lo) hX (by omega : 25 ≤ M) ha0 ha1 rfl hT_eq hf.2.1 (j := j)
            (by dsimp [γ, M₁, R, η_up] at hhi; push_cast at hhi; exact hhi) hL_conds.2.2.1
          have h2' : (ℙ (E pq.1 ∩ E pq.2)).toReal ≤
              Real.exp 2 * (1 + 8 * (16 / (1 - a))) * Real.exp (-(2 * a - γ) * Real.log M₁) := by
            convert h2 using 4
            dsimp [γ, M₁, R]; push_cast; rfl
          have hc_le : 16 / (1 - a) ≤ cM := le_trans (le_max_left _ _) (le_max_right _ _)
          have hfac : Real.exp 2 * (1 + 8 * (16 / (1 - a))) ≤ Real.exp 2 * (1 + 8 * cM) := by gcongr
          exact h2'.trans (mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le)
        calc ∑ pq ∈ scalePairs j, (ℙ (E pq.1 ∩ E pq.2)).toReal
            ≤ ((scalePairs j).card : ℝ) *
                (Real.exp 2 * (1 + 8 * cM) * Real.exp (-(2 * a - γ) * Real.log M₁)) := by
              calc _ ≤ ∑ _ ∈ scalePairs j, _ := Finset.sum_le_sum heach
                _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (9 * Real.exp ((2 - γ) * Real.log M₁)) *
                (Real.exp 2 * (1 + 8 * cM) * Real.exp (-(2 * a - γ) * Real.log M₁)) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc ((scalePairs j).card : ℝ) ≤ 9 * (Rmax : ℝ) ^ 2 * (R : ℝ) ^ 2 := hcard_bd
                _ = 9 * ((Rmax : ℝ) ^ 2 * (R : ℝ) ^ 2) := by ring
                _ ≤ 9 * Real.exp ((2 - γ) * Real.log M₁) :=
                    mul_le_mul_of_nonneg_left hMR_exp (by norm_num)
          _ = 9 * Real.exp 2 * (1 + 8 * cM) *
                (Real.exp ((2 - γ) * Real.log M₁) * Real.exp (-(2 * a - γ) * Real.log M₁)) := by ring
          _ = 9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a) * Real.log M₁) := by
              rw [← Real.exp_add]; congr 2; ring
          _ ≤ 9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
              nlinarith only [hη0, hlogM1_pos]
      · push Not at hhi
        have hj_good : j ∈ goodScales M η_lo η_up := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, h3R, hlo, hhi⟩
          have h2j_M : 2 ^ j ≤ M + 1 := by
            have hR9 : R ≤ 9 * R := by omega
            have h9R2 : 9 * R ≤ (3 * R) ^ 2 := by
              calc 9 * R ≤ (9 * R) * R := Nat.le_mul_of_pos_right _ hR1
                _ = (3 * R) ^ 2 := by ring
            exact (hR9.trans h9R2).trans h3R
          exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by decide) h2j_M)
        have hR_big : (Real.log M₁ / Real.pi + 2) / (R : ℝ) ≤ 1 := by
          have hηup0 : 0 < η_up := by dsimp [η_up]; linarith only [ha1]
          have hR_exp : Real.exp ((η_up / 2) * Real.log M₁) ≤ (R : ℝ) := by
            have h1 : η_up * Real.log M₁ ≤ 2 * Real.log (R : ℝ) := by
              have hγ_eq : γ * Real.log M₁ = Real.log M₁ - 2 * Real.log (R : ℝ) := by
                have hR0 : (0 : ℝ) < R := by exact_mod_cast hR1
                dsimp [γ]
                rw [Real.log_div (by linarith only [hM1_ge]) (by positivity), Real.log_pow,
                  div_mul_cancel₀ _ hlogM1_pos.ne']
                push_cast; ring
              have h2 : γ * Real.log M₁ ≤ (1 - η_up) * Real.log M₁ :=
                mul_le_mul_of_nonneg_right hhi hlogM1_pos.le
              linarith only [hγ_eq, h2]
            have h2 : (η_up / 2) * Real.log M₁ ≤ Real.log (R : ℝ) := by linarith only [h1]
            have := Real.exp_le_exp.mpr h2
            rwa [Real.exp_log (by exact_mod_cast hR1)] at this
          have hpow2 := Real.pow_div_factorial_le_exp ((η_up / 2) * Real.log M₁)
            (mul_nonneg (div_nonneg hηup0.le zero_le_two) hlogM1_pos.le) 2
          have hpow2' : ((η_up / 2) * Real.log M₁) ^ 2 / 2 ≤ Real.exp ((η_up / 2) * Real.log M₁) := by
            simpa [Nat.factorial] using hpow2
          have hL_le : Real.log M₁ / Real.pi + 2 ≤ ((η_up / 2) * Real.log M₁) ^ 2 / 2 := by
            have h1 : Real.log M₁ / Real.pi + 2 ≤ Real.log M₁ / 3 + 2 := by
              have : Real.log M₁ / Real.pi ≤ Real.log M₁ / 3 :=
                div_le_div_of_nonneg_left hlogM1_pos.le (by norm_num) Real.pi_gt_three.le
              linarith only [this]
            have h2 : Real.log M₁ / 3 + 2 ≤ Real.log M₁ := by linarith only [hlogM1_ge4]
            have h3 : Real.log M₁ ≤ ((η_up / 2) * Real.log M₁) ^ 2 / 2 := by
              have hL_ge : 16 / η_up ^ 2 ≤ Real.log M₁ := by linarith only [hL_conds.2.2.2.2.2.2]
              have h4 : 8 ≤ η_up ^ 2 * Real.log M₁ / 2 := by
                rw [le_div_iff₀ two_pos]
                have hmul := (div_le_iff₀' (sq_pos_of_pos hηup0)).mp hL_ge
                linarith only [hmul]
              calc Real.log M₁ ≤ (η_up ^ 2 * Real.log M₁ / 8) * Real.log M₁ := by
                    nlinarith only [h4, hlogM1_pos]
                _ = ((η_up / 2) * Real.log M₁) ^ 2 / 2 := by ring
            linarith only [h1, h2, h3]
          exact (div_le_one (by exact_mod_cast hR1)).mpr (hL_le.trans (hpow2'.trans hR_exp))
        have heach : ∀ pq ∈ scalePairs j, (ℙ (E pq.1 ∩ E pq.2)).toReal ≤
            Real.exp 2 * (1 + 8 * cM) * Real.exp (-(2 * a - γ) * Real.log M₁) := by
          intro pq hpq
          have hf := Finset.mem_filter.mp hpq
          have h2 := prob_two_good_pair_le hX (by omega : 25 ≤ M) ha0 ha1 hη0 hT_eq hf.2.1
            hj_good hf.2.2.1 hf.2.2.2 hR_big hL_conds.1 hL_conds.2.1
          have h2' : (ℙ (E pq.1 ∩ E pq.2)).toReal ≤
              Real.exp 2 * (1 + 8 * c₁B) * Real.exp (-(2 * a - γ + m_B / 4) * Real.log M₁) := by
            convert h2 using 4
            dsimp [γ, m_B, t, M₁, R]; push_cast; rfl
          have hc_le : c₁B ≤ cM := le_max_left _ _
          have hmB0 : 0 ≤ m_B := by dsimp [m_B, t]; positivity
          have hexp_m : Real.exp (-(2 * a - γ + m_B / 4) * Real.log M₁) ≤
              Real.exp (-(2 * a - γ) * Real.log M₁) := by
            refine Real.exp_le_exp.mpr ?_
            nlinarith only [hmB0, hlogM1_pos]
          have hfac : Real.exp 2 * (1 + 8 * c₁B) ≤ Real.exp 2 * (1 + 8 * cM) := by gcongr
          exact h2'.trans (mul_le_mul hfac hexp_m (Real.exp_pos _).le (by positivity))
        calc ∑ pq ∈ scalePairs j, (ℙ (E pq.1 ∩ E pq.2)).toReal
            ≤ ((scalePairs j).card : ℝ) *
                (Real.exp 2 * (1 + 8 * cM) * Real.exp (-(2 * a - γ) * Real.log M₁)) := by
              calc _ ≤ ∑ _ ∈ scalePairs j, _ := Finset.sum_le_sum heach
                _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (9 * Real.exp ((2 - γ) * Real.log M₁)) *
                (Real.exp 2 * (1 + 8 * cM) * Real.exp (-(2 * a - γ) * Real.log M₁)) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc ((scalePairs j).card : ℝ) ≤ 9 * (Rmax : ℝ) ^ 2 * (R : ℝ) ^ 2 := hcard_bd
                _ = 9 * ((Rmax : ℝ) ^ 2 * (R : ℝ) ^ 2) := by ring
                _ ≤ 9 * Real.exp ((2 - γ) * Real.log M₁) :=
                    mul_le_mul_of_nonneg_left hMR_exp (by norm_num)
          _ = 9 * Real.exp 2 * (1 + 8 * cM) *
                (Real.exp ((2 - γ) * Real.log M₁) * Real.exp (-(2 * a - γ) * Real.log M₁)) := by ring
          _ = 9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a) * Real.log M₁) := by
              rw [← Real.exp_add]; congr 2; ring
          _ ≤ 9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
              nlinarith only [hη0, hlogM1_pos]
  have hoff_le : ∑ pq ∈ (Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 ≠ pq.2),
        (ℙ (E pq.1 ∩ E pq.2)).toReal ≤
      2 * Real.log M₁ * (9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁)) := by
    calc ∑ pq ∈ (Q0 Rmax ×ˢ Q0 Rmax).filter (fun pq ↦ pq.1 ≠ pq.2), (ℙ (E pq.1 ∩ E pq.2)).toReal
        ≤ ∑ pq ∈ (Finset.range Ksc).biUnion scalePairs, (ℙ (E pq.1 ∩ E pq.2)).toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_off fun _ _ _ ↦ ENNReal.toReal_nonneg
      _ ≤ ∑ j ∈ Finset.range Ksc, ∑ pq ∈ scalePairs j, (ℙ (E pq.1 ∩ E pq.2)).toReal :=
          sum_biUnion_le_of_nonneg _ _ _ fun _ ↦ ENNReal.toReal_nonneg
      _ ≤ ∑ _ ∈ Finset.range Ksc,
            9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁) :=
          Finset.sum_le_sum hscale_le
      _ = (Ksc : ℝ) * (9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2 * Real.log M₁) *
            (9 * Real.exp 2 * (1 + 8 * cM) * Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁)) :=
          mul_le_mul_of_nonneg_right hKsc_le (by positivity)
  rw [hsplit]
  set Efac := Real.exp ((2 - 2 * a + 3 * η_lo) * Real.log M₁)
  set A1 := Real.exp 2 * (1 + 4 * c₁D)
  set A2 := 9 * Real.exp 2 * (1 + 8 * cM)
  have h1 := hdiag_le
  have h2 := hoff_le
  have hA1_nn : 0 ≤ A1 * Efac := mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith only [hc1D_pos])) (Real.exp_pos _).le
  have h3 : 1 * (A1 * Efac) ≤ (1 + 2 * Real.log M₁) * (A1 * Efac) :=
    mul_le_mul_of_nonneg_right (by linarith only [hlogM1_pos]) hA1_nn
  have h4 : (1 + 2 * Real.log M₁) * (A1 * Efac) + 2 * Real.log M₁ * (A2 * Efac) ≤
      (1 + 2 * Real.log M₁) * (A1 * Efac) + (1 + 2 * Real.log M₁) * (A2 * Efac) := by
    have hA2_nn : 0 ≤ A2 * Efac := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (by linarith only [hcM0])) (Real.exp_pos _).le
    have hle : 2 * Real.log M₁ * (A2 * Efac) ≤ (1 + 2 * Real.log M₁) * (A2 * Efac) :=
      mul_le_mul_of_nonneg_right (by linarith only) hA2_nn
    linarith only [hle]
  have h_eq : (1 + 2 * Real.log M₁) * C_tot * Efac =
      (1 + 2 * Real.log M₁) * (A1 * Efac) + (1 + 2 * Real.log M₁) * (A2 * Efac) := by
    dsimp [C_tot, A1, A2, c₁D]; ring
  linarith only [h1, h2, h3, h4, h_eq]

set_option maxHeartbeats 400000 in
private lemma h2_herrA {M : ℕ} {a η_lo η_1 : ℝ}
    (ha0 : 7 / 8 ≤ a) (ha1 : a < 1) (hηlo0 : 0 < η_lo) (hηlo1 : η_lo ≤ 1)
    (_hη10 : 0 < η_1)
    (hη1_le_mA :
      let s_p := 1 + (1 - a) / 8
      let b := a * s_p ^ 2
      let ρ_A := (s_p ^ 2 - 1) / 2
      let m_A := ρ_A * η_lo * (b - a * (1 + ρ_A)) / (1 + ρ_A) ^ 2
      η_1 ≤ m_A / 16)
    (hL1_ge1000 : 3000 ≤ Real.log ((M : ℝ) + 1))
    (hKL_A :
      let s_p := 1 + (1 - a) / 8
      let b := a * s_p ^ 2
      let ρ_A := (s_p ^ 2 - 1) / 2
      let m_A := ρ_A * η_lo * (b - a * (1 + ρ_A)) / (1 + ρ_A) ^ 2
      let c₁A := 4 * (a + b) * (1 + ρ_A) ^ 2 / (ρ_A * η_lo * (b - a * (1 + ρ_A)))
      let c₃A := ρ_A * c₁A
      let C_A := Real.exp 2 * (1 + 4 * c₁A + 4 * c₃A)
      128 * (1 + c₁A + c₃A) * (2 * Real.log 2 + 1) / m_A +
        32 * Real.pi * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) / m_A +
        (2 ^ 14 * C_A) * (Nat.factorial 7 : ℝ) / (m_A / 4) ^ 7 ≤ Real.log ((M : ℝ) + 1))
    (hKL_η : 16 / ((1 - a) / 2) ^ 2 + 16 ≤ Real.log ((M : ℝ) + 1)) :
    let s_p := 1 + (1 - a) / 8
    let b := a * s_p ^ 2
    let ρ := (s_p ^ 2 - 1) / 2
    let m := ρ * η_lo * (b - a * (1 + ρ)) / (1 + ρ) ^ 2
    let c₁ := 4 * (a + b) * (1 + ρ) ^ 2 / (ρ * η_lo * (b - a * (1 + ρ)))
    let c₃ := ρ * c₁
    let M₁ : ℝ := (M : ℝ) + 1
    let M₂ : ℝ := ((2 * M : ℕ) : ℝ) + 1
    let L₂ : ℝ := Real.log M₂ / Real.pi
    16 * (1 + c₁ + c₃) * (2 * Real.log 2 + 1) / Real.log M₁ +
        4 * (c₁ * (2 * c₁ + 2 * c₃) + b * c₃ * (2 * c₁ + 7 * c₃)) / L₂ ≤ m / 4 ∧
      (∀ j ∈ goodScales M η_lo ((1 - a) / 2), (L₂ + 2) / ((2 ^ j : ℕ) : ℝ) ≤ 1) ∧
      32 * Real.log M₁ ^ 2 * (Real.exp 2 * (1 + 4 * c₁ + 4 * c₃)) *
          Real.exp (-(a + m / 2) * Real.log M₁) ≤
        Real.exp (-(a + 2 * η_1) * Real.log M₁) := by
  intro s_p b ρ_A m_A c₁A c₃A M₁ M₂ L₂
  set L1 : ℝ := Real.log M₁
  set C_A : ℝ := Real.exp 2 * (1 + 4 * c₁A + 4 * c₃A)
  set η_up : ℝ := (1 - a) / 2
  change 128 * (1 + c₁A + c₃A) * (2 * Real.log 2 + 1) / m_A +
      32 * Real.pi * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) / m_A +
      (2 ^ 14 * C_A) * (Nat.factorial 7 : ℝ) / (m_A / 4) ^ 7 ≤ L1 at hKL_A
  have hpi := Real.pi_pos
  have ha_pos : 0 < a := by linarith only [ha0]
  have hL1_pos : 0 < L1 := lt_of_lt_of_le (by norm_num) hL1_ge1000
  have hηup0 : 0 < η_up := by dsimp [η_up]; linarith only [ha1]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨hρA0, hmA0, hc1A0, _hlimA⟩ := partA_limit_margin ha_pos ha1 hηlo0 hηlo1
  clear _hlimA
  have hc1A0' : 0 ≤ c₁A := by change 0 < c₁A at hc1A0; exact hc1A0.le
  have hmA0' : 0 < m_A := by change 0 < m_A at hmA0; exact hmA0
  have hc3A0 : 0 ≤ c₃A := by
    dsimp [c₃A]; exact mul_nonneg (by change 0 < ρ_A at hρA0; exact hρA0.le) hc1A0'
  have hCA0 : 0 < C_A := mul_pos (Real.exp_pos 2) (by linarith only [hc1A0', hc3A0])
  have hb0 : 0 ≤ b := by dsimp [b, s_p]; exact mul_nonneg ha_pos.le (sq_nonneg _)
  have hM1_pos : 0 < M₁ := by dsimp [M₁]; positivity
  have hM2_ge : M₁ ≤ M₂ := by dsimp [M₁, M₂]; push_cast; linarith only
  have hM2_pos : 0 < M₂ := lt_of_lt_of_le hM1_pos hM2_ge
  have hM2_le : M₂ ≤ 2 * M₁ := by dsimp [M₁, M₂]; push_cast; linarith only
  have hlogM2_ge : L1 ≤ Real.log M₂ := Real.log_le_log hM1_pos hM2_ge
  have hlogM2_le : Real.log M₂ ≤ L1 + Real.log 2 := by
    have h1 := Real.log_le_log hM2_pos hM2_le
    rw [Real.log_mul two_ne_zero hM1_pos.ne'] at h1
    linarith only [h1]
  have hL2_ge : L1 / Real.pi ≤ L₂ := div_le_div_of_nonneg_right hlogM2_ge hpi.le
  have hL2_pos : 0 < L₂ := lt_of_lt_of_le (div_pos hL1_pos hpi) hL2_ge
  have hnumA_nn : 0 ≤ 4 * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) :=
    mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg hc1A0' (add_nonneg (mul_nonneg zero_le_two hc1A0') (mul_nonneg zero_le_two hc3A0)))
      (mul_nonneg (mul_nonneg hb0 hc3A0) (add_nonneg (mul_nonneg zero_le_two hc1A0') (mul_nonneg (by norm_num) hc3A0))))
  have hnn_term1 : 0 ≤ 128 * (1 + c₁A + c₃A) * (2 * Real.log 2 + 1) / m_A :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hc1A0', hc3A0]))
      (by linarith only [hlog2_pos])) hmA0'.le
  have hnn_term2 : 0 ≤ 32 * Real.pi * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) / m_A :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi.le) (by linarith only [hnumA_nn])) hmA0'.le
  have hnn_term3 : 0 ≤ (2 ^ 14 * C_A) * (Nat.factorial 7 : ℝ) / (m_A / 4) ^ 7 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCA0.le) (Nat.cast_nonneg _))
      (pow_nonneg (by linarith only [hmA0']) 7)
  have h1 : 16 * (1 + c₁A + c₃A) * (2 * Real.log 2 + 1) / L1 ≤ m_A / 8 := by
    rw [div_le_iff₀ hL1_pos]
    have hbound : 128 * (1 + c₁A + c₃A) * (2 * Real.log 2 + 1) / m_A ≤ L1 := by
      linarith only [hKL_A, hnn_term2, hnn_term3]
    have hmul := (div_le_iff₀ hmA0').mp hbound
    linarith only [hmul]
  have h2 : 4 * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) / L₂ ≤ m_A / 8 := by
    have hbound : 32 * Real.pi * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) / m_A ≤ L1 := by
      linarith only [hKL_A, hnn_term1, hnn_term3]
    have hmul : 32 * Real.pi * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) ≤ L1 * m_A :=
      (div_le_iff₀ hmA0').mp hbound
    have h_pi : 4 * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) /
          (L1 / Real.pi) ≤ m_A / 8 := by
      rw [div_le_iff₀ (div_pos hL1_pos hpi)]
      calc 4 * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A))
          = (32 * Real.pi * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A))) / (8 * Real.pi) := by
              field_simp [hpi.ne']; ring
        _ ≤ (L1 * m_A) / (8 * Real.pi) := div_le_div_of_nonneg_right hmul (mul_pos (by norm_num) hpi).le
        _ = m_A / 8 * (L1 / Real.pi) := by ring
    exact (div_le_div_of_nonneg_left hnumA_nn (div_pos hL1_pos hpi) hL2_ge).trans h_pi
  have hR_big_2M : ∀ j ∈ goodScales M η_lo η_up, (L₂ + 2) / ((2 ^ j : ℕ) : ℝ) ≤ 1 := by
    intro j hj
    have hjf := Finset.mem_filter.mp hj
    set R : ℕ := 2 ^ j
    have hR1 : 1 ≤ R := Nat.one_le_pow j 2 two_pos
    have hR0 : (0 : ℝ) < R := by exact_mod_cast hR1
    have hγ_hi : Real.log (M₁ / (R : ℝ) ^ 2) / L1 ≤ 1 - η_up := hjf.2.2.2
    have hR_exp : Real.exp ((η_up / 2) * L1) ≤ (R : ℝ) := by
      have h1 : η_up * L1 ≤ 2 * Real.log (R : ℝ) := by
        have hγ_eq : (Real.log (M₁ / (R : ℝ) ^ 2) / L1) * L1 = L1 - 2 * Real.log (R : ℝ) := by
          rw [div_mul_cancel₀ _ hL1_pos.ne',
            Real.log_div hM1_pos.ne' (pow_pos hR0 2).ne', Real.log_pow]
          dsimp [L1]
        have h2 := mul_le_mul_of_nonneg_right hγ_hi hL1_pos.le
        linarith only [hγ_eq, h2]
      have := Real.exp_le_exp.mpr (by linarith only [h1] : (η_up / 2) * L1 ≤ Real.log (R : ℝ))
      rwa [Real.exp_log hR0] at this
    have hpow2 := Real.pow_div_factorial_le_exp ((η_up / 2) * L1) (mul_nonneg (by linarith only [hηup0]) hL1_pos.le) 2
    have hpow2' : ((η_up / 2) * L1) ^ 2 / 2 ≤ Real.exp ((η_up / 2) * L1) := by
      simpa [Nat.factorial] using hpow2
    have hL2_le : L₂ + 2 ≤ L1 := by
      have h1 : L₂ ≤ (L1 + 1) / 3 := by
        calc L₂ ≤ (L1 + Real.log 2) / Real.pi := div_le_div_of_nonneg_right hlogM2_le hpi.le
          _ ≤ (L1 + 1) / 3 := div_le_div₀ (by linarith only [hL1_pos, Real.log_two_lt_d9])
              (by linarith only [Real.log_two_lt_d9]) (by norm_num) Real.pi_gt_three.le
      linarith only [h1, hL1_ge1000]
    have hL1_sq : L1 ≤ ((η_up / 2) * L1) ^ 2 / 2 := by
      have h16 : 16 / η_up ^ 2 ≤ L1 := by linarith only [hKL_η]
      have hmul : 16 ≤ η_up ^ 2 * L1 := (div_le_iff₀' (sq_pos_of_pos hηup0)).mp h16
      have : L1 ≤ (η_up ^ 2 * L1 / 8) * L1 := by nlinarith only [hmul, hL1_pos]
      linarith only [this, show (η_up ^ 2 * L1 / 8) * L1 = ((η_up / 2) * L1) ^ 2 / 2 by ring]
    exact (div_le_one hR0).mpr (hL2_le.trans (hL1_sq.trans (hpow2'.trans hR_exp)))
  have h_tailA : 32 * L1 ^ 2 * C_A * Real.exp (-(a + m_A / 2) * L1) ≤
      Real.exp (-(a + 2 * η_1) * L1) := by
    have hbound : (2 ^ 14 * C_A) * (Nat.factorial 7 : ℝ) / (m_A / 4) ^ 7 ≤ L1 := by
      linarith only [hKL_A, hnn_term1, hnn_term2]
    have hexp_ge := exp_mul_ge_mul_pow (by linarith only [hmA0'] : 0 < m_A / 4)
      (mul_nonneg (by norm_num) hCA0.le) (by linarith only [hL1_ge1000]) hbound
    have hL1_6 : 32 * L1 ^ 2 * C_A ≤ 2 ^ 14 * C_A * L1 ^ 6 := by
      have hL2 : 1 ≤ L1 ^ 2 := by nlinarith only [hL1_ge1000]
      have h1 : 1 ≤ L1 ^ 4 := by nlinarith only [hL2]
      calc 32 * L1 ^ 2 * C_A = (C_A * L1 ^ 2) * 32 := by ring
        _ ≤ (C_A * L1 ^ 2) * (2 ^ 14 * L1 ^ 4) :=
            mul_le_mul_of_nonneg_left (by linarith only [h1]) (mul_nonneg hCA0.le (sq_nonneg L1))
        _ = 2 ^ 14 * C_A * L1 ^ 6 := by ring
    have hmul : 32 * L1 ^ 2 * C_A * Real.exp (-(a + m_A / 2) * L1) ≤
        Real.exp ((m_A / 4) * L1) * Real.exp (-(a + m_A / 2) * L1) :=
      mul_le_mul_of_nonneg_right (hL1_6.trans hexp_ge) (Real.exp_pos _).le
    rw [← Real.exp_add] at hmul
    refine hmul.trans (Real.exp_le_exp.mpr ?_)
    have h_ex : -(a + m_A / 2) + m_A / 4 = -(a + m_A / 4) := by ring
    have h_cmp : -(a + m_A / 4) ≤ -(a + 2 * η_1) := by linarith only [hη1_le_mA, hmA0']
    nlinarith only [h_ex, h_cmp, hL1_pos]
  exact ⟨by linarith only [h1, h2], hR_big_2M, h_tailA⟩

private lemma h2_hL_conds {M : ℕ} {a η_lo : ℝ}
    (ha0 : 7 / 8 ≤ a) (ha1 : a < 1) (hηlo0 : 0 < η_lo) (hL1_pos : 0 < Real.log ((M : ℝ) + 1))
    (hKL_B :
      let t := (1 - a) / 8
      let η_up := (1 - a) / 2
      let m_B := a * t ^ 2 * η_lo
      let c₁B := 16 / (η_up ^ 2 * m_B)
      Real.pi * (max (48 * c₁B) (max (32 * (16 * c₁B ^ 2 + 16 * c₁B ^ 2 * 22 * c₁B) / m_B)
        (max (256 * (16 / (1 - a)) ^ 2 / (1 - a)) (max (128 * (8 / η_lo) ^ 2 / η_lo)
        (32 * (4 / (1 - a)) ^ 2 / (1 - a)))))) ≤ Real.log ((M : ℝ) + 1))
    (hKL_lo : 16 * Real.log 2 / η_lo ≤ Real.log ((M : ℝ) + 1))
    (hKL_η : 16 / ((1 - a) / 2) ^ 2 + 16 ≤ Real.log ((M : ℝ) + 1)) :
    let t := (1 - a) / 8
    let η_up := (1 - a) / 2
    let m_B := a * t ^ 2 * η_lo
    let c₁B := 16 / (η_up ^ 2 * m_B)
    let M₁ : ℝ := (M : ℝ) + 1
    let L : ℝ := Real.log M₁ / Real.pi
    48 * c₁B ≤ L ∧
      8 * (16 * c₁B ^ 2 + 16 * c₁B ^ 2 * 22 * c₁B) / L ≤ m_B / 4 ∧
      32 * (16 / (1 - a)) ^ 2 / L ≤ (1 - a) / 8 ∧
      32 * (8 / η_lo) ^ 2 / L ≤ η_lo / 4 ∧
      2 * Real.log 2 / Real.log M₁ ≤ η_lo / 8 ∧
      8 * (4 / (1 - a)) ^ 2 / L ≤ (1 - a) / 4 ∧
      16 / η_up ^ 2 + 16 ≤ Real.log M₁ := by
  intro t η_up m_B c₁B M₁ L
  have hpi := Real.pi_pos
  have hL_pos : 0 < L := div_pos hL1_pos hpi
  have hmB0 : 0 < m_B := by
    have ha_pos : 0 < a := by linarith only [ha0]
    exact mul_pos (mul_pos ha_pos (sq_pos_of_pos (by dsimp [t]; linarith only [ha1]))) hηlo0
  have hb1 : 48 * c₁B ≤ L := by
    dsimp [L]; rw [le_div_iff₀ hpi, mul_comm]
    exact le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hpi.le) hKL_B
  have hb2 : 8 * (16 * c₁B ^ 2 + 16 * c₁B ^ 2 * 22 * c₁B) / L ≤ m_B / 4 := by
    rw [div_le_iff₀ hL_pos]
    have h1 : 32 * (16 * c₁B ^ 2 + 16 * c₁B ^ 2 * 22 * c₁B) / m_B ≤ L := by
      dsimp [L]; rw [le_div_iff₀ hpi, mul_comm]
      exact le_trans (mul_le_mul_of_nonneg_left (le_max_of_le_right (le_max_left _ _)) hpi.le) hKL_B
    have hmul := (div_le_iff₀ hmB0).mp h1
    linarith only [hmul]
  have hb3 : 32 * (16 / (1 - a)) ^ 2 / L ≤ (1 - a) / 8 := by
    rw [div_le_iff₀ hL_pos]
    have h1 : 256 * (16 / (1 - a)) ^ 2 / (1 - a) ≤ L := by
      dsimp [L]; rw [le_div_iff₀ hpi, mul_comm]
      exact le_trans (mul_le_mul_of_nonneg_left
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) hpi.le) hKL_B
    have hmul := (div_le_iff₀ (by linarith only [ha1] : 0 < 1 - a)).mp h1
    linarith only [hmul]
  have hb4 : 32 * (8 / η_lo) ^ 2 / L ≤ η_lo / 4 := by
    rw [div_le_iff₀ hL_pos]
    have h1 : 128 * (8 / η_lo) ^ 2 / η_lo ≤ L := by
      dsimp [L]; rw [le_div_iff₀ hpi, mul_comm]
      exact le_trans (mul_le_mul_of_nonneg_left
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))) hpi.le) hKL_B
    have hmul := (div_le_iff₀ hηlo0).mp h1
    linarith only [hmul]
  have hb5 : 2 * Real.log 2 / Real.log M₁ ≤ η_lo / 8 := by
    rw [div_le_iff₀ hL1_pos]
    have hmul := (div_le_iff₀ hηlo0).mp hKL_lo
    linarith only [hmul]
  have hb6 : 8 * (4 / (1 - a)) ^ 2 / L ≤ (1 - a) / 4 := by
    rw [div_le_iff₀ hL_pos]
    have h1 : 32 * (4 / (1 - a)) ^ 2 / (1 - a) ≤ L := by
      dsimp [L]; rw [le_div_iff₀ hpi, mul_comm]
      exact le_trans (mul_le_mul_of_nonneg_left
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))) hpi.le) hKL_B
    have hmul := (div_le_iff₀ (by linarith only [ha1] : 0 < 1 - a)).mp h1
    linarith only [hmul]
  exact ⟨hb1, hb2, hb3, hb4, hb5, hb6, hKL_η⟩

private lemma h2_blk_prob {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X)
    {M M₀ Rmax T : ℕ} {a η_lo η_1 C_tot C_pz : ℝ}
    (hM100 : 100 ≤ M) (ha0 : 7 / 8 ≤ a) (ha1 : a < 1)
    (hηlo0 : 0 < η_lo) (hηlo1 : η_lo ≤ 1) (hηlo14 : η_lo ≤ 1 / 4)
    (hη10 : 0 < η_1) (hη1_le14 : η_1 ≤ 1 / 4)
    (hT_eq : T = Nat.ceil (a * Real.log ((M : ℝ) + 1) ^ 2 / Real.pi))
    (hM0_ge : (M : ℝ) / (8 * Real.log ((M : ℝ) + 1)) ≤ (M₀ : ℝ))
    (hM0_le : (M₀ : ℝ) ≤ (M : ℝ) / (4 * Real.log ((M : ℝ) + 1)))
    (hM0_val : 200 ≤ M₀) (hM0_pos : (0 : ℝ) < M₀)
    (hRmax1 : 1 ≤ Rmax)
    (hRmax_le : (Rmax : ℝ) ≤ Real.sqrt (M₀ : ℝ) / 1024)
    (hRmax_ge : Real.sqrt (M₀ : ℝ) / 2048 ≤ (Rmax : ℝ))
    (h36R : 36 * Rmax ^ 2 ≤ M + 1)
    (hL1_ge1000 : 3000 ≤ Real.log ((M : ℝ) + 1))
    (hlog_big : Real.log (8 * Real.log ((M : ℝ) + 1)) + 3 * Real.pi ≤ η_1 * Real.log ((M : ℝ) + 1))
    (herrA :
      let s_p := 1 + (1 - a) / 8
      let b := a * s_p ^ 2
      let ρ := (s_p ^ 2 - 1) / 2
      let m := ρ * η_lo * (b - a * (1 + ρ)) / (1 + ρ) ^ 2
      let c₁ := 4 * (a + b) * (1 + ρ) ^ 2 / (ρ * η_lo * (b - a * (1 + ρ)))
      let c₃ := ρ * c₁
      let M₁ : ℝ := (M : ℝ) + 1
      let M₂ : ℝ := ((2 * M : ℕ) : ℝ) + 1
      let L₂ : ℝ := Real.log M₂ / Real.pi
      16 * (1 + c₁ + c₃) * (2 * Real.log 2 + 1) / Real.log M₁ +
          4 * (c₁ * (2 * c₁ + 2 * c₃) + b * c₃ * (2 * c₁ + 7 * c₃)) / L₂ ≤ m / 4 ∧
        (∀ j ∈ goodScales M η_lo ((1 - a) / 2), (L₂ + 2) / ((2 ^ j : ℕ) : ℝ) ≤ 1) ∧
        32 * Real.log M₁ ^ 2 * (Real.exp 2 * (1 + 4 * c₁ + 4 * c₃)) *
            Real.exp (-(a + m / 2) * Real.log M₁) ≤
          Real.exp (-(a + 2 * η_1) * Real.log M₁))
    (hL_conds :
      let t := (1 - a) / 8
      let η_up := (1 - a) / 2
      let m_B := a * t ^ 2 * η_lo
      let c₁B := 16 / (η_up ^ 2 * m_B)
      let M₁ : ℝ := (M : ℝ) + 1
      let L : ℝ := Real.log M₁ / Real.pi
      48 * c₁B ≤ L ∧
        8 * (16 * c₁B ^ 2 + 16 * c₁B ^ 2 * 22 * c₁B) / L ≤ m_B / 4 ∧
        32 * (16 / (1 - a)) ^ 2 / L ≤ (1 - a) / 8 ∧
        32 * (8 / η_lo) ^ 2 / L ≤ η_lo / 4 ∧
        2 * Real.log 2 / Real.log M₁ ≤ η_lo / 8 ∧
        8 * (4 / (1 - a)) ^ 2 / L ≤ (1 - a) / 4 ∧
        16 / η_up ^ 2 + 16 ≤ Real.log M₁)
    (hCtot_eq :
      let t := (1 - a) / 8
      let η_up := (1 - a) / 2
      let m_B := a * t ^ 2 * η_lo
      let c₁B := 16 / (η_up ^ 2 * m_B)
      C_tot = Real.exp 2 * (1 + 4 * (4 / (1 - a))) +
        9 * Real.exp 2 * (1 + 8 * max c₁B (max (16 / (1 - a)) (8 / η_lo))))
    (hCtot0 : 0 < C_tot)
    (hCpz_eq : C_pz = 4 * (2 ^ 29) ^ 2 * C_tot) :
    let b := a * (1 + (1 - a) / 8) ^ 2
    let η_up := (1 - a) / 2
    let B_blk : Set (ℕ → ℤ × ℤ) := {y | ∃ p ∈ Q0 Rmax, y ∈ goodEvent M T b η_lo η_up p}
    let L1 := Real.log ((M : ℝ) + 1)
    Det (2 * M) B_blk ∧
      (∀ y ∈ B_blk, ∃ z : ℤ × ℤ, T ≤ locShift 0 y (2 * M) z) ∧
      (1 / (C_pz * L1 ^ 5)) * Real.exp (-(4 * η_1 + 3 * η_lo) * L1) ≤
        (ℙ {ω | path X ω ∈ B_blk}).toReal := by
  intro b η_up B_blk L1
  set M₁ : ℝ := (M : ℝ) + 1
  have hM1_pos : 0 < M₁ := by dsimp [M₁]; positivity
  have hL1_pos : 0 < L1 := lt_of_lt_of_le (by norm_num) hL1_ge1000
  have hRmax0 : (0 : ℝ) < Rmax := by exact_mod_cast hRmax1
  have hS1 := goodEvent_first_moment_ge hX hM100 ha0 ha1 hηlo0 hηlo1 hη10 hη1_le14 hT_eq
    hM0_ge hM0_le hM0_val hRmax1 hRmax_le hlog_big herrA
  have hS2_raw := goodEvent_second_moment_le hX hM100 ha0 ha1 hηlo0 hηlo14 hT_eq hRmax1 h36R hL_conds
  have hS2 : ∑ pq ∈ Q0 Rmax ×ˢ Q0 Rmax,
      (ℙ ({ω | path X ω ∈ goodEvent M T b η_lo η_up pq.1} ∩
        {ω | path X ω ∈ goodEvent M T b η_lo η_up pq.2})).toReal ≤
      (1 + 2 * L1) * C_tot * Real.exp ((2 - 2 * a + 3 * η_lo) * L1) := by
    rw [hCtot_eq]; exact hS2_raw
  have hB_det : Det (2 * M) B_blk := fun y y' h ⟨p, hp, hy⟩ ↦
    ⟨p, hp, det_goodEvent M T b η_lo η_up p y y' h hy⟩
  have hB_hit : ∀ y ∈ B_blk, ∃ z : ℤ × ℤ, T ≤ locShift 0 y (2 * M) z := by
    rintro y ⟨p, _, hy⟩
    exact ⟨rot p, hy.1.trans (locShift_zero_mono (by omega : M ≤ 2 * M) (rot p))⟩
  let E : ℤ × ℤ → Set Ω := fun p ↦ {ω | path X ω ∈ goodEvent M T b η_lo η_up p}
  have hEm : ∀ p ∈ Q0 Rmax, MeasurableSet (E p) := fun p _ ↦ goodEvent_meas hX M T b η_lo η_up p
  set S₁_val : ℝ := (Rmax : ℝ) ^ 2 * (1 / (8 * L1)) * Real.exp (-(a + 2 * η_1) * L1)
  set S₂_val : ℝ := (1 + 2 * L1) * C_tot * Real.exp ((2 - 2 * a + 3 * η_lo) * L1)
  have hS1_pos : 0 < S₁_val :=
    mul_pos (mul_pos (sq_pos_of_pos hRmax0) (one_div_pos.mpr (mul_pos (by norm_num) hL1_pos))) (Real.exp_pos _)
  have hS2_pos : 0 < S₂_val :=
    mul_pos (mul_pos (by linarith only [hL1_pos]) hCtot0) (Real.exp_pos _)
  have hpz := paley_zygmund_finset (Q0 Rmax) E hEm hS1_pos hS2_pos hS1 hS2
  have hU_eq : (⋃ p ∈ Q0 Rmax, E p) = {ω | path X ω ∈ B_blk} := by
    ext ω; simp [E, B_blk]
  rw [hU_eq] at hpz
  have hRmax2_lb : M₁ / (2 ^ 26 * L1) ≤ (Rmax : ℝ) ^ 2 := by
    have hM_ge : M₁ / 2 ≤ (M : ℝ) := by
      dsimp [M₁]
      have : (100 : ℝ) ≤ M := by exact_mod_cast hM100
      linarith only [this]
    have hM0_lb2 : M₁ / (16 * L1) ≤ (M₀ : ℝ) := by
      calc M₁ / (16 * L1) = (M₁ / 2) / (8 * L1) := by ring
        _ ≤ (M : ℝ) / (8 * L1) := div_le_div_of_nonneg_right hM_ge (mul_pos (by norm_num) hL1_pos).le
        _ ≤ (M₀ : ℝ) := hM0_ge
    calc M₁ / (2 ^ 26 * L1) = (M₁ / (16 * L1)) / 2048 ^ 2 := by ring
      _ ≤ (M₀ : ℝ) / 2048 ^ 2 := div_le_div_of_nonneg_right hM0_lb2 (by norm_num)
      _ = (Real.sqrt (M₀ : ℝ) / 2048) ^ 2 := by rw [div_pow, Real.sq_sqrt hM0_pos.le]
      _ ≤ (Rmax : ℝ) ^ 2 := pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) hRmax_ge 2
  have hS1_lb : (1 / (2 ^ 29 * L1 ^ 2)) * Real.exp ((1 - a - 2 * η_1) * L1) ≤ S₁_val := by
    calc (1 / (2 ^ 29 * L1 ^ 2)) * Real.exp ((1 - a - 2 * η_1) * L1)
        = (Real.exp L1 / (2 ^ 26 * L1)) * (1 / (8 * L1)) * Real.exp (-(a + 2 * η_1) * L1) := by
            rw [show (1 - a - 2 * η_1) * L1 = L1 + -(a + 2 * η_1) * L1 by ring, Real.exp_add]
            field_simp [hL1_pos.ne']; ring
      _ = (M₁ / (2 ^ 26 * L1)) * (1 / (8 * L1)) * Real.exp (-(a + 2 * η_1) * L1) := by
            dsimp [L1]; rw [Real.exp_log hM1_pos]
      _ ≤ (Rmax : ℝ) ^ 2 * (1 / (8 * L1)) * Real.exp (-(a + 2 * η_1) * L1) := by
            have h18 : 0 ≤ (1 / (8 * L1)) * Real.exp (-(a + 2 * η_1) * L1) :=
              mul_nonneg (one_div_nonneg.mpr (mul_nonneg (by norm_num) hL1_pos.le)) (Real.exp_pos _).le
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hRmax2_lb h18
  have hS2_ub : S₂_val ≤ (3 * L1) * C_tot * Real.exp ((2 - 2 * a + 3 * η_lo) * L1) := by
    have h12 : 1 + 2 * L1 ≤ 3 * L1 := by linarith only [hL1_ge1000]
    dsimp [S₂_val]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h12 hCtot0.le) (Real.exp_pos _).le
  have hnum : (1 / (2 ^ 29 * L1 ^ 2)) ^ 2 * Real.exp ((2 - 2 * a - 4 * η_1) * L1) ≤ S₁_val ^ 2 := by
    have hnn : 0 ≤ (1 / (2 ^ 29 * L1 ^ 2)) * Real.exp ((1 - a - 2 * η_1) * L1) :=
      mul_nonneg (one_div_nonneg.mpr (mul_nonneg (by norm_num) (sq_nonneg L1))) (Real.exp_pos _).le
    calc (1 / (2 ^ 29 * L1 ^ 2)) ^ 2 * Real.exp ((2 - 2 * a - 4 * η_1) * L1)
        = ((1 / (2 ^ 29 * L1 ^ 2)) * Real.exp ((1 - a - 2 * η_1) * L1)) ^ 2 := by
            rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
      _ ≤ S₁_val ^ 2 := pow_le_pow_left₀ hnn hS1_lb 2
  have hdiv_lb : (1 / (C_pz * L1 ^ 5)) * Real.exp (-(4 * η_1 + 3 * η_lo) * L1) ≤ S₁_val ^ 2 / S₂_val := by
    have h_alg : ((1 / (2 ^ 29 * L1 ^ 2)) ^ 2 * Real.exp ((2 - 2 * a - 4 * η_1) * L1)) /
          ((3 * L1) * C_tot * Real.exp ((2 - 2 * a + 3 * η_lo) * L1)) =
        (1 / (3 * 2 ^ 58 * C_tot * L1 ^ 5)) * Real.exp (-(4 * η_1 + 3 * η_lo) * L1) := by
      have hexp_eq : Real.exp ((2 - 2 * a - 4 * η_1) * L1) /
            Real.exp ((2 - 2 * a + 3 * η_lo) * L1) =
          Real.exp (-(4 * η_1 + 3 * η_lo) * L1) := by
        rw [← Real.exp_sub]; congr 1; ring
      calc ((1 / (2 ^ 29 * L1 ^ 2)) ^ 2 * Real.exp ((2 - 2 * a - 4 * η_1) * L1)) /
            ((3 * L1) * C_tot * Real.exp ((2 - 2 * a + 3 * η_lo) * L1))
          = (1 / (3 * 2 ^ 58 * C_tot * L1 ^ 5)) *
              (Real.exp ((2 - 2 * a - 4 * η_1) * L1) / Real.exp ((2 - 2 * a + 3 * η_lo) * L1)) := by
              field_simp [hL1_pos.ne', hCtot0.ne', (Real.exp_pos _).ne']
        _ = _ := by rw [hexp_eq]
    have h_c : (1 / (C_pz * L1 ^ 5)) ≤ 1 / (3 * 2 ^ 58 * C_tot * L1 ^ 5) := by
      refine one_div_le_one_div_of_le (mul_pos (mul_pos (by norm_num) hCtot0) (pow_pos hL1_pos 5)) ?_
      have hcoef : 3 * 2 ^ 58 * C_tot ≤ C_pz := by rw [hCpz_eq]; linarith only [hCtot0]
      exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg hL1_pos.le 5)
    have h_step1 : (1 / (C_pz * L1 ^ 5)) * Real.exp (-(4 * η_1 + 3 * η_lo) * L1) ≤
        (1 / (3 * 2 ^ 58 * C_tot * L1 ^ 5)) * Real.exp (-(4 * η_1 + 3 * η_lo) * L1) :=
      mul_le_mul_of_nonneg_right h_c (Real.exp_pos _).le
    rw [← h_alg] at h_step1
    have hnum_nn : 0 ≤ (1 / (2 ^ 29 * L1 ^ 2)) ^ 2 * Real.exp ((2 - 2 * a - 4 * η_1) * L1) :=
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    exact h_step1.trans (div_le_div₀ (sq_nonneg S₁_val) hnum hS2_pos hS2_ub)
  exact ⟨hB_det, hB_hit, hdiv_lb.trans hpz⟩

set_option maxHeartbeats 250000 in
/-- Main theorem proving `H2` of `Erdos1166.erdos_1166.variants.dembo_peres_rosen_zeitouni.R1`. -/
theorem h2_main :
    OMA.R_Erdos1166_erdos_1166_variants_dembo_peres_rosen_zeitouni_R1.H2 := by
  intro Ω _ _ X hX ε hε
  set ε₀ : ℝ := min ε (1 / (2 * Real.pi))
  have hpi := Real.pi_pos
  have hε₀_pos : 0 < ε₀ := lt_min hε (by positivity)
  have hε₀_le : ε₀ ≤ ε := min_le_left _ _
  have hε₀_hi : ε₀ ≤ 1 / (2 * Real.pi) := min_le_right _ _
  set δ₁ : ℝ := Real.pi * ε₀
  have hδ₁_pos : 0 < δ₁ := mul_pos hpi hε₀_pos
  have hδ₁_le : δ₁ ≤ 1 / 2 := by
    dsimp [δ₁]
    calc Real.pi * ε₀ ≤ Real.pi * (1 / (2 * Real.pi)) := mul_le_mul_of_nonneg_left hε₀_hi hpi.le
      _ = 1 / 2 := by field_simp [hpi.ne']
  set a : ℝ := 1 - δ₁ / 4
  have ha0 : 7 / 8 ≤ a := by dsimp [a]; linarith only [hδ₁_le]
  have ha1 : a < 1 := by dsimp [a]; linarith only [hδ₁_pos]
  have ha_pos : 0 < a := by linarith only [ha0]
  set t : ℝ := (1 - a) / 8
  set s_p : ℝ := 1 + t
  set b : ℝ := a * s_p ^ 2
  set η_up : ℝ := (1 - a) / 2
  set D : ℕ := Nat.ceil (16 / δ₁) + 16
  have hD16 : 16 ≤ D := by omega
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hD_inv : 1 / (D : ℝ) ≤ δ₁ / 16 := by
    have hceil : 16 / δ₁ ≤ (D : ℝ) := by
      have : 16 / δ₁ ≤ (Nat.ceil (16 / δ₁) : ℝ) := Nat.le_ceil _
      have : (Nat.ceil (16 / δ₁) : ℝ) ≤ D := by dsimp [D]; exact_mod_cast (by omega : Nat.ceil (16 / δ₁) ≤ D)
      linarith only [‹16 / δ₁ ≤ (Nat.ceil (16 / δ₁) : ℝ)›, this]
    rw [div_le_iff₀ hD_pos]
    have : 16 ≤ (D : ℝ) * δ₁ := (div_le_iff₀ hδ₁_pos).mp hceil
    linarith only [this]
  set η_lo : ℝ := min ((1 - a) / 8) (1 / (32 * (D : ℝ)))
  have hηlo0 : 0 < η_lo := lt_min (by linarith only [ha1]) (by positivity)
  have hηlo_le_a : η_lo ≤ (1 - a) / 8 := min_le_left _ _
  have hηlo_le_D : η_lo ≤ 1 / (32 * (D : ℝ)) := min_le_right _ _
  have hηlo1 : η_lo ≤ 1 := by linarith only [hηlo_le_a, ha0]
  have hηlo14 : η_lo ≤ 1 / 4 := by linarith only [hηlo_le_a, ha0]
  set ρ_A : ℝ := (s_p ^ 2 - 1) / 2
  set m_A : ℝ := ρ_A * η_lo * (b - a * (1 + ρ_A)) / (1 + ρ_A) ^ 2
  set c₁A : ℝ := 4 * (a + b) * (1 + ρ_A) ^ 2 / (ρ_A * η_lo * (b - a * (1 + ρ_A)))
  set c₃A : ℝ := ρ_A * c₁A
  obtain ⟨hρA0, hmA0, hc1A0, _hlimA⟩ := partA_limit_margin ha_pos ha1 hηlo0 hηlo1
  set m_B : ℝ := a * t ^ 2 * η_lo
  set c₁B : ℝ := 16 / (η_up ^ 2 * m_B)
  obtain ⟨ht0, hηup0, hmB0, hc1B0, _hlimB⟩ := partB_good_limit_margin ha0 ha1 hηlo0
  clear _hlimA _hlimB
  set η_1 : ℝ := min (η_lo / 8) (m_A / 16)
  have hη10 : 0 < η_1 := lt_min (by positivity) (by positivity)
  have hη1_le_lo : η_1 ≤ η_lo / 8 := min_le_left _ _
  have hη1_le_mA : η_1 ≤ m_A / 16 := min_le_right _ _
  have hη1_le14 : η_1 ≤ 1 / 4 := by linarith only [hη1_le_lo, hηlo14]
  set C_A : ℝ := Real.exp 2 * (1 + 4 * c₁A + 4 * c₃A)
  set cM : ℝ := max c₁B (max (16 / (1 - a)) (8 / η_lo))
  set C_tot : ℝ := Real.exp 2 * (1 + 4 * (4 / (1 - a))) + 9 * Real.exp 2 * (1 + 8 * cM)
  have hCA0 : 0 < C_A := by
    have hc1A0' : 0 ≤ c₁A := by change 0 < c₁A at hc1A0; exact hc1A0.le
    have hc3A0 : 0 ≤ c₃A := by
      dsimp [c₃A]; exact mul_nonneg (by change 0 < ρ_A at hρA0; exact hρA0.le) hc1A0'
    dsimp [C_A]
    exact mul_pos (Real.exp_pos 2) (by linarith only [hc1A0', hc3A0])
  have hCtot0 : 0 < C_tot := by
    have hc1B0' : 0 ≤ cM := le_trans hc1B0.le (le_max_left _ _)
    have h4a : 0 ≤ 4 / (1 - a) := div_nonneg (by norm_num) (by linarith only [ha1])
    dsimp [C_tot]; positivity
  set C_pz : ℝ := 4 * (2 ^ 29) ^ 2 * C_tot
  have hCpz0 : 0 < C_pz := by dsimp [C_pz]; positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hexp : (Real.exp (1 / 2) : ℝ) ^ 2 ≤ 2 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
      have := Real.exp_one_lt_d9; linarith only [this]
    have : Real.exp (1 / 2) ≤ 2 := by nlinarith only [hexp, Real.exp_pos (1 / 2)]
    exact (Real.le_log_iff_exp_le two_pos).mpr this
  set K_L : ℝ := max 3000
    (max ((4 * (Nat.factorial 7 : ℝ) / η_1 ^ 2) + (2 * (3 * Real.pi + Real.log 8) / η_1) + 1)
    (max (Real.pi * (max (48 * c₁B) (max (32 * (16 * c₁B ^ 2 + 16 * c₁B ^ 2 * 22 * c₁B) / m_B)
      (max (256 * (16 / (1 - a)) ^ 2 / (1 - a)) (max (128 * (8 / η_lo) ^ 2 / η_lo)
      (32 * (4 / (1 - a)) ^ 2 / (1 - a)))))))
    (max (16 * Real.log 2 / η_lo) (max (16 / η_up ^ 2 + 16)
    (max (128 * (1 + c₁A + c₃A) * (2 * Real.log 2 + 1) / m_A +
      32 * Real.pi * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) / m_A +
      (2 ^ 14 * C_A) * (Nat.factorial 7 : ℝ) / (m_A / 4) ^ 7)
    (max (C_pz * (Nat.factorial 7 : ℝ) / (1 / (4 * (D : ℝ))) ^ 7) (2 ^ 13 * (D : ℝ) ^ 2)))))))
  set K₀ : ℕ := Nat.ceil (4 * K_L + 100 * (D : ℝ) ^ 2 + 2 ^ 30)
  have htail_bound : ∀ k : ℕ, K₀ ≤ k →
      ℙ {ω | (maxLocalTime X (2 ^ k) ω : ℝ) / (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 <
        1 / Real.pi - ε₀} ≤ ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
    intro k hk
    have hk_real : 4 * K_L + 100 * (D : ℝ) ^ 2 + 2 ^ 30 ≤ (k : ℝ) := by
      have : (K₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith only [this, Nat.le_ceil (4 * K_L + 100 * (D : ℝ) ^ 2 + 2 ^ 30)]
    have hKL_ge : 3000 ≤ K_L := le_max_left _ _
    have hD2_nn : (0 : ℝ) ≤ (D : ℝ) ^ 2 := sq_nonneg _
    have hk_D : 64 * D ≤ k := by
      have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
      have h1 : (64 * (D : ℝ) : ℝ) ≤ 100 * (D : ℝ) ^ 2 := by nlinarith only [hD1]
      have h2 : (64 * D : ℝ) ≤ (k : ℝ) := by linarith only [hk_real, h1, hKL_ge]
      exact_mod_cast h2
    let m : ℕ := k - k / D - 1
    let M : ℕ := 2 ^ m
    let K : ℕ := 2 ^ (k / D)
    have h_kD_le : k / D ≤ k / 16 := Nat.div_le_div_left hD16 (by omega)
    have hm_ge : k / 2 ≤ m := by dsimp [m]; omega
    have hn_eq : K * (2 * M) = 2 ^ k := by
      dsimp [K, M, m]
      have h_exp : k / D + (1 + (k - k / D - 1)) = k := by omega
      calc 2 ^ (k / D) * (2 * 2 ^ (k - k / D - 1))
          = 2 ^ (k / D) * 2 ^ (1 + (k - k / D - 1)) := by rw [pow_add, pow_one]
        _ = 2 ^ (k / D + (1 + (k - k / D - 1))) := by rw [← pow_add]
        _ = 2 ^ k := by rw [h_exp]
    let M₁ : ℝ := (M : ℝ) + 1
    let L1 : ℝ := Real.log M₁
    have hm_ge30 : 30 ≤ m := by
      have h1 : (2 ^ 30 : ℝ) ≤ k := by linarith only [hk_real, hKL_ge, hD2_nn]
      have h2 : 2 ^ 30 ≤ k := by exact_mod_cast h1
      omega
    have hM_ge30 : 2 ^ 30 ≤ M := Nat.pow_le_pow_right two_pos hm_ge30
    have hM100 : 100 ≤ M := by omega
    have hL1_ge : K_L ≤ L1 := by
      have hm_r : (k : ℝ) / 2 - 1 ≤ (m : ℝ) := by
        have h1 : (k : ℝ) ≤ 2 * (k / 2 : ℕ) + 1 := by exact_mod_cast (by omega : k ≤ 2 * (k / 2) + 1)
        have h2 : ((k / 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge
        linarith only [h1, h2]
      have hpow_le : (2 : ℝ) ^ m ≤ M₁ := by dsimp [M₁, M]; push_cast; linarith only
      have hlog_ge : (m : ℝ) * Real.log 2 ≤ L1 := by
        have := Real.log_le_log (by positivity) hpow_le
        rwa [Real.log_pow] at this
      have hk4 : (k : ℝ) / 4 - 1 / 2 ≤ L1 := by
        have hk_big : (2 ^ 30 : ℝ) ≤ k := by linarith only [hk_real, hKL_ge, hD2_nn]
        have h1 : (k : ℝ) / 4 - 1 / 2 = ((k : ℝ) / 2 - 1) * (1 / 2) := by ring
        have h2 : ((k : ℝ) / 2 - 1) * (1 / 2) ≤ (m : ℝ) * Real.log 2 := by
          exact mul_le_mul hm_r hlog2_ge (by norm_num) (Nat.cast_nonneg m)
        linarith only [h1, h2, hlog_ge]
      linarith only [hk_real, hk4, hD2_nn]
    have hL1_pos : 0 < L1 := by linarith only [hL1_ge, hKL_ge]
    have hL1_ge1000 : 3000 ≤ L1 := by linarith only [hL1_ge, hKL_ge]
    have hKL1 : 4 * (Nat.factorial 7 : ℝ) / η_1 ^ 2 + 2 * (3 * Real.pi + Real.log 8) / η_1 + 1 ≤ L1 :=
      (le_max_of_le_right (le_max_left _ _)).trans hL1_ge
    have hKL_B : Real.pi * (max (48 * c₁B) (max (32 * (16 * c₁B ^ 2 + 16 * c₁B ^ 2 * 22 * c₁B) / m_B)
        (max (256 * (16 / (1 - a)) ^ 2 / (1 - a)) (max (128 * (8 / η_lo) ^ 2 / η_lo)
        (32 * (4 / (1 - a)) ^ 2 / (1 - a)))))) ≤ L1 :=
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hL1_ge
    have hKL_lo : 16 * Real.log 2 / η_lo ≤ L1 :=
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))).trans hL1_ge
    have hKL_η : 16 / η_up ^ 2 + 16 ≤ L1 :=
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))))).trans hL1_ge
    have hKL_A : 128 * (1 + c₁A + c₃A) * (2 * Real.log 2 + 1) / m_A +
        32 * Real.pi * (c₁A * (2 * c₁A + 2 * c₃A) + b * c₃A * (2 * c₁A + 7 * c₃A)) / m_A +
        (2 ^ 14 * C_A) * (Nat.factorial 7 : ℝ) / (m_A / 4) ^ 7 ≤ L1 :=
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))).trans hL1_ge
    have hKL_pz : C_pz * (Nat.factorial 7 : ℝ) / (1 / (4 * (D : ℝ))) ^ 7 ≤ L1 :=
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))).trans hL1_ge
    have hKL_k2 : 2 ^ 13 * (D : ℝ) ^ 2 ≤ L1 :=
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))))).trans hL1_ge
    clear_value K₀ K_L
    let T : ℕ := Nat.ceil (a * L1 ^ 2 / Real.pi)
    let M₀ : ℕ := M / Nat.ceil (5 * L1)
    let Rmax : ℕ := Nat.floor (Real.sqrt (M₀ : ℝ) / 1024)
    have hM_exp : L1 ^ 4 / 24 ≤ (M : ℝ) + 1 := by
      have h_fac := Real.pow_div_factorial_le_exp L1 hL1_pos.le 4
      rw [show Real.exp L1 = M₁ from Real.exp_log (by positivity)] at h_fac
      simpa [Nat.factorial] using h_fac
    have hM_div8 : (2 ^ 24 : ℝ) ≤ (M : ℝ) / (8 * L1) := by
      have hL2 : 3000 ^ 2 ≤ L1 ^ 2 := pow_le_pow_left₀ (by norm_num) hL1_ge1000 2
      have hL3 : 3000 ^ 3 ≤ L1 ^ 3 := pow_le_pow_left₀ (by norm_num) hL1_ge1000 3
      have hL4 : 3000 ^ 3 * L1 ≤ L1 ^ 4 := by
        calc 3000 ^ 3 * L1 ≤ L1 ^ 3 * L1 := mul_le_mul_of_nonneg_right hL3 hL1_pos.le
          _ = L1 ^ 4 := by ring
      have hpow : 8 * (2 ^ 24 : ℝ) * L1 + 1 ≤ L1 ^ 4 / 24 := by
        linarith only [hL4, hL1_ge1000]
      have hle : 8 * (2 ^ 24 : ℝ) * L1 ≤ (M : ℝ) := by linarith only [hpow, hM_exp]
      rw [le_div_iff₀ (by positivity)]
      linarith only [hle]
    have hM0_ge : (M : ℝ) / (8 * L1) ≤ (M₀ : ℝ) := by
      have hc5_lt : (Nat.ceil (5 * L1) : ℝ) < 5 * L1 + 1 := Nat.ceil_lt_add_one (by positivity)
      have hc5_pos : 0 < Nat.ceil (5 * L1) := Nat.ceil_pos.mpr (by positivity)
      have hdiv_ge : (M : ℝ) / (Nat.ceil (5 * L1) : ℝ) - 1 ≤ (M₀ : ℝ) := by
        have h1 : M < (M₀ + 1) * Nat.ceil (5 * L1) := by
          have hdiv := Nat.div_add_mod M (Nat.ceil (5 * L1))
          have hM0_def : M₀ = M / Nat.ceil (5 * L1) := rfl
          rw [← hM0_def, Nat.mul_comm] at hdiv
          have hmod := Nat.mod_lt M hc5_pos
          linarith [hdiv, hmod, show (M₀ + 1) * Nat.ceil (5 * L1) = M₀ * Nat.ceil (5 * L1) + Nat.ceil (5 * L1) by ring]
        have h2 : (M : ℝ) < ((M₀ : ℝ) + 1) * (Nat.ceil (5 * L1) : ℝ) := by exact_mod_cast h1
        have h3 : (M : ℝ) / (Nat.ceil (5 * L1) : ℝ) < (M₀ : ℝ) + 1 :=
          (div_lt_iff₀ (by exact_mod_cast hc5_pos)).mpr h2
        linarith only [h3]
      have h_ceil_le : (Nat.ceil (5 * L1) : ℝ) ≤ 6 * L1 := by linarith only [hc5_lt, hL1_ge1000]
      have hM_div : (M : ℝ) / (6 * L1) ≤ (M : ℝ) / (Nat.ceil (5 * L1) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hc5_pos) h_ceil_le
      have h_gap : (M : ℝ) / (6 * L1) - (M : ℝ) / (8 * L1) = (M : ℝ) / (24 * L1) := by
        field_simp [hL1_pos.ne']; ring
      have h_ge1 : 1 ≤ (M : ℝ) / (24 * L1) := by
        have : (M : ℝ) / (24 * L1) = ((M : ℝ) / (8 * L1)) / 3 := by ring
        rw [this]; linarith only [hM_div8]
      linarith only [hdiv_ge, hM_div, h_gap, h_ge1]
    have hM0_le : (M₀ : ℝ) ≤ (M : ℝ) / (4 * L1) := by
      have hc5 : 5 * L1 ≤ (Nat.ceil (5 * L1) : ℝ) := Nat.le_ceil _
      have hc5_pos : 0 < Nat.ceil (5 * L1) := Nat.ceil_pos.mpr (by positivity)
      have hdiv : (M₀ : ℝ) ≤ (M : ℝ) / (Nat.ceil (5 * L1) : ℝ) := by
        have h1 : M₀ * Nat.ceil (5 * L1) ≤ M := Nat.div_mul_le_self M _
        have h2 : (M₀ : ℝ) * (Nat.ceil (5 * L1) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
        exact (le_div_iff₀ (by exact_mod_cast hc5_pos)).mpr h2
      have h45 : 4 * L1 ≤ (Nat.ceil (5 * L1) : ℝ) := by linarith only [hc5, hL1_pos]
      exact hdiv.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) h45)
    have hM0_24 : (2 ^ 24 : ℝ) ≤ (M₀ : ℝ) := hM_div8.trans hM0_ge
    have hM0_val : 200 ≤ M₀ := by
      have : (200 : ℝ) ≤ (M₀ : ℝ) := by linarith only [hM0_24, show (200 : ℝ) ≤ 2 ^ 24 by norm_num]
      exact_mod_cast this
    have hM0_pos : (0 : ℝ) < M₀ := by exact_mod_cast (by omega : 0 < M₀)
    have hsqrt_ge4 : 4 ≤ Real.sqrt (M₀ : ℝ) / 1024 := by
      have h1 : (4096 : ℝ) ^ 2 ≤ (M₀ : ℝ) := by linarith only [hM0_24, show (4096 : ℝ) ^ 2 = 2 ^ 24 by norm_num]
      have h2 : 4096 ≤ Real.sqrt (M₀ : ℝ) := (Real.le_sqrt (by norm_num) hM0_pos.le).mpr h1
      linarith only [h2]
    have hRmax_le : (Rmax : ℝ) ≤ Real.sqrt (M₀ : ℝ) / 1024 :=
      Nat.floor_le (by positivity)
    have hRmax_ge : Real.sqrt (M₀ : ℝ) / 2048 ≤ (Rmax : ℝ) := by
      have hlt : Real.sqrt (M₀ : ℝ) / 1024 - 1 < (Rmax : ℝ) := Nat.sub_one_lt_floor _
      linarith only [hlt, hsqrt_ge4]
    have hRmax1 : 1 ≤ Rmax := by
      have : (2 : ℝ) ≤ (Rmax : ℝ) := by linarith only [hRmax_ge, hsqrt_ge4]
      exact_mod_cast (by linarith only [this] : (1 : ℝ) ≤ Rmax)
    have h36R : 36 * Rmax ^ 2 ≤ M + 1 := by
      have hR2 : (Rmax : ℝ) ^ 2 ≤ (M₀ : ℝ) / 1024 ^ 2 := by
        calc (Rmax : ℝ) ^ 2 ≤ (Real.sqrt (M₀ : ℝ) / 1024) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hRmax_le 2
          _ = (M₀ : ℝ) / 1024 ^ 2 := by rw [div_pow, Real.sq_sqrt hM0_pos.le]
      have hM0_le_M : (M₀ : ℝ) ≤ (M : ℝ) :=
        hM0_le.trans (div_le_self (by positivity) (by linarith only [hL1_ge1000]))
      have h36 : 36 * (Rmax : ℝ) ^ 2 ≤ (M : ℝ) := by nlinarith only [hR2, hM0_le_M]
      have : ((36 * Rmax ^ 2 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by push_cast; linarith only [h36]
      exact_mod_cast this
    clear_value M₀ Rmax
    have hlog_big : Real.log (8 * L1) + 3 * Real.pi ≤ η_1 * L1 := by
      have h1 : Real.log (8 * L1) = Real.log 8 + 2 * Real.log (Real.sqrt L1) := by
        rw [show 8 * L1 = 8 * (Real.sqrt L1) ^ 2 by rw [Real.sq_sqrt hL1_pos.le],
          Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast; ring
      have h2 : Real.log (Real.sqrt L1) ≤ Real.sqrt L1 := by
        have := Real.add_one_le_exp (Real.log (Real.sqrt L1))
        rw [Real.exp_log (Real.sqrt_pos.mpr hL1_pos)] at this
        linarith only [this]
      have hA : 2 * Real.sqrt L1 ≤ (η_1 / 2) * L1 := by
        have hsq : 16 / η_1 ^ 2 ≤ L1 := by
          have h16 : 16 / η_1 ^ 2 ≤ 4 * (Nat.factorial 7 : ℝ) / η_1 ^ 2 := by
            gcongr; norm_num
          linarith only [hKL1, h16, show (0 : ℝ) < 2 * (3 * Real.pi + Real.log 8) / η_1 by positivity]
        have h16L : 16 ≤ η_1 ^ 2 * L1 := by
          linarith only [(div_le_iff₀ (sq_pos_of_pos hη10)).mp hsq]
        have hsqrt : 4 ≤ η_1 * Real.sqrt L1 := by
          have hsq1 : 4 ^ 2 ≤ (η_1 * Real.sqrt L1) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hL1_pos.le]; linarith only [h16L]
          have hnn_sqrt : 0 ≤ η_1 * Real.sqrt L1 := mul_nonneg hη10.le (Real.sqrt_nonneg L1)
          by_contra hlt; push Not at hlt
          nlinarith only [hlt, hsq1, hnn_sqrt]
        have hsq2 : 2 * Real.sqrt L1 ≤ (η_1 / 2) * (Real.sqrt L1 * Real.sqrt L1) := by
          nlinarith only [hsqrt, Real.sqrt_nonneg L1]
        rwa [Real.mul_self_sqrt hL1_pos.le] at hsq2
      have hB : Real.log 8 + 3 * Real.pi ≤ (η_1 / 2) * L1 := by
        have : 2 * (3 * Real.pi + Real.log 8) / η_1 ≤ L1 := by
          have hnn : 0 ≤ 4 * (Nat.factorial 7 : ℝ) / η_1 ^ 2 := by positivity
          linarith only [hKL1, hnn]
        have hmul := (div_le_iff₀ hη10).mp this
        linarith only [hmul]
      linarith only [h1, h2, hA, hB]
    have herrA := h2_herrA ha0 ha1 hηlo0 hηlo1 hη10 hη1_le_mA hL1_ge1000 hKL_A hKL_η
    have hL_conds := h2_hL_conds ha0 ha1 hηlo0 hL1_pos hKL_B hKL_lo hKL_η
    let B_blk : Set (ℕ → ℤ × ℤ) := {y | ∃ p ∈ Q0 Rmax, y ∈ goodEvent M T b η_lo η_up p}
    obtain ⟨hB_det, hB_hit, hp_blk_lb⟩ := h2_blk_prob hX hM100 ha0 ha1 hηlo0 hηlo1 hηlo14
      hη10 hη1_le14 rfl hM0_ge hM0_le hM0_val hM0_pos hRmax1 hRmax_le hRmax_ge h36R
      hL1_ge1000 hlog_big herrA hL_conds rfl hCtot0 rfl
    have hm1_k : (m : ℝ) + 1 ≤ (k : ℝ) := by
      have hkd_le : k / D ≤ k / 2 := Nat.div_le_div_left (by omega : 2 ≤ D) two_pos
      have hk2_le : 1 ≤ k - k / D := by omega
      have hm_nat : m + 1 ≤ k := (Nat.sub_add_cancel hk2_le).trans_le (Nat.sub_le k (k / D))
      exact_mod_cast hm_nat
    have hM1_2 : M₁ ≤ (2 : ℝ) ^ (m + 1) := by
      have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast (Nat.one_le_pow m 2 two_pos)
      dsimp [M₁, M]; rw [pow_succ]; push_cast; linarith only [h2p]
    have hL1_k : L1 ≤ (k : ℝ) * Real.log 2 := by
      have h1 := Real.log_le_log (by positivity) hM1_2
      rw [Real.log_pow] at h1
      have h2 : ((m + 1 : ℕ) : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log 2 := by
        push_cast; exact mul_le_mul_of_nonneg_right hm1_k hlog2_pos.le
      exact h1.trans h2
    have hK_lb : Real.exp ((1 / (2 * (D : ℝ))) * L1) ≤ (K : ℝ) := by
      have hkD_lb : (k : ℝ) / (2 * (D : ℝ)) ≤ ((k / D : ℕ) : ℝ) := by
        have h1 : (k : ℝ) < ((k / D : ℕ) : ℝ) * (D : ℝ) + (D : ℝ) := by
          have hdiv := Nat.div_add_mod k D
          rw [Nat.mul_comm] at hdiv
          have hmod := Nat.mod_lt k (by omega : 0 < D)
          have : k < (k / D) * D + D := by omega
          exact_mod_cast this
        have h2 : (k : ℝ) / (D : ℝ) - 1 < ((k / D : ℕ) : ℝ) := by
          rw [sub_lt_iff_lt_add, div_lt_iff₀ hD_pos]; linarith only [h1]
        have h3 : (k : ℝ) / (2 * (D : ℝ)) ≤ (k : ℝ) / (D : ℝ) - 1 := by
          have : (1 : ℝ) ≤ (k : ℝ) / (2 * (D : ℝ)) := by
            rw [one_le_div (by positivity)]
            have hk_D_r : (64 : ℝ) * (D : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_D
            linarith only [hk_D_r, hD_pos]
          linarith only [this, show (k : ℝ) / (D : ℝ) - (k : ℝ) / (2 * (D : ℝ)) = (k : ℝ) / (2 * (D : ℝ)) by ring]
        linarith only [h2, h3]
      have hexp_k : (1 / (2 * (D : ℝ))) * L1 ≤ ((k / D : ℕ) : ℝ) * Real.log 2 := by
        calc (1 / (2 * (D : ℝ))) * L1 ≤ (1 / (2 * (D : ℝ))) * ((k : ℝ) * Real.log 2) :=
              mul_le_mul_of_nonneg_left hL1_k (by positivity)
          _ = ((k : ℝ) / (2 * (D : ℝ))) * Real.log 2 := by ring
          _ ≤ ((k / D : ℕ) : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hkD_lb hlog2_pos.le
      calc Real.exp ((1 / (2 * (D : ℝ))) * L1)
          ≤ Real.exp (((k / D : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp_k
        _ = (K : ℝ) := by
            dsimp [K]; rw [Real.exp_nat_mul, Real.exp_log two_pos]; push_cast; rfl
    have hKp_ge_k : (k : ℝ) ≤ (K : ℝ) * (ℙ {ω | path X ω ∈ B_blk}).toReal := by
      have hexp_gap : 4 * η_1 + 3 * η_lo ≤ 1 / (8 * (D : ℝ)) := by
        have h41 : 4 * η_1 ≤ η_lo / 2 := by linarith only [hη1_le_lo]
        have h4l : 4 * η_lo ≤ 1 / (8 * (D : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hηlo_le_D (by norm_num : (0 : ℝ) ≤ 4)
          linarith only [this, show 4 * (1 / (32 * (D : ℝ))) = 1 / (8 * (D : ℝ)) by ring]
        linarith only [h41, h4l, hηlo0]
      have hexp_pz := exp_mul_ge_mul_pow (by positivity : 0 < 1 / (4 * (D : ℝ)))
        hCpz0.le (by linarith only [hL1_ge1000]) hKL_pz
      have hL1_56 : C_pz * L1 ^ 5 ≤ Real.exp ((1 / (4 * (D : ℝ))) * L1) := by
        have h1 : C_pz * L1 ^ 5 ≤ C_pz * L1 ^ 6 :=
          calc C_pz * L1 ^ 5 = (C_pz * L1 ^ 5) * 1 := (mul_one _).symm
            _ ≤ (C_pz * L1 ^ 5) * L1 :=
                mul_le_mul_of_nonneg_left (by linarith only [hL1_ge1000]) (mul_nonneg hCpz0.le (pow_nonneg hL1_pos.le 5))
            _ = C_pz * L1 ^ 6 := by ring
        exact h1.trans hexp_pz
      have h_pow_k : (k : ℝ) ≤ Real.exp ((1 / (8 * (D : ℝ))) * L1) := by
        have hpow2 := Real.pow_div_factorial_le_exp ((1 / (8 * (D : ℝ))) * L1) (by positivity) 2
        have h_100D : 100 * (D : ℝ) ^ 2 ≤ (k : ℝ) := by linarith only [hk_real, hKL_ge]
        have hk4 : (k : ℝ) / 4 ≤ L1 := by
          have hm34 : (3 / 4 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by
            have hk16_nat : 16 * (k / D) ≤ k :=
              (Nat.mul_le_mul_left 16 h_kD_le).trans (Nat.mul_div_le k 16)
            have hk16_r : 16 * ((k / D : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk16_nat
            have hk_big : (2 ^ 30 : ℝ) ≤ k := by linarith only [hk_real, hKL_ge, hD2_nn]
            have hm_eq : (k : ℝ) = (m : ℝ) + ((k / D : ℕ) : ℝ) + 1 := by
              have h1 : k / D + 1 ≤ k := by omega
              have hnat : k = m + k / D + 1 := by dsimp [m]; omega
              exact_mod_cast hnat
            linarith only [hk16_r, hk_big, hm_eq]
          have hpow_le : (2 : ℝ) ^ m ≤ M₁ := by dsimp [M₁, M]; push_cast; linarith only
          have hlog_ge : (m : ℝ) * Real.log 2 ≤ L1 := by
            have := Real.log_le_log (by positivity) hpow_le
            rwa [Real.log_pow] at this
          have h1 : (k : ℝ) / 4 ≤ ((3 / 4 : ℝ) * (k : ℝ)) * (1 / 2) := by
            have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            linarith only [hk_nn]
          have h2 : ((3 / 4 : ℝ) * (k : ℝ)) * (1 / 2) ≤ (m : ℝ) * Real.log 2 :=
            mul_le_mul hm34 hlog2_ge (by norm_num) (Nat.cast_nonneg m)
          linarith only [h1, h2, hlog_ge]
        have hk_ge_D : 2 ^ 11 * (D : ℝ) ^ 2 ≤ (k : ℝ) := by
          have hL1_le_k : L1 ≤ (k : ℝ) :=
            hL1_k.trans (mul_le_of_le_one_right (Nat.cast_nonneg k) (Real.log_two_lt_d9.le.trans (by norm_num)))
          linarith only [hKL_k2, hL1_le_k, hD2_nn]
        calc (k : ℝ) = (k : ℝ) * 1 := (mul_one _).symm
          _ ≤ (k : ℝ) * ((k : ℝ) / (2 ^ 11 * (D : ℝ) ^ 2)) :=
              mul_le_mul_of_nonneg_left ((one_le_div (by positivity)).mpr hk_ge_D) (by positivity)
          _ = ((1 / (8 * (D : ℝ))) * ((k : ℝ) / 4)) ^ 2 / 2 := by ring
          _ ≤ ((1 / (8 * (D : ℝ))) * L1) ^ 2 / 2 := by
              gcongr
          _ ≤ Real.exp ((1 / (8 * (D : ℝ))) * L1) := by simpa [Nat.factorial] using hpow2
      have h_split_exp : (k : ℝ) * (C_pz * L1 ^ 5) ≤
          Real.exp ((1 / (2 * (D : ℝ)) - (4 * η_1 + 3 * η_lo)) * L1) := by
        have h1 : (1 / (8 * (D : ℝ))) * L1 + (1 / (4 * (D : ℝ))) * L1 ≤
            (1 / (2 * (D : ℝ)) - (4 * η_1 + 3 * η_lo)) * L1 := by
          have h_c : 1 / (8 * (D : ℝ)) + 1 / (4 * (D : ℝ)) ≤ 1 / (2 * (D : ℝ)) - (4 * η_1 + 3 * η_lo) := by
            linarith only [hexp_gap, show 1 / (2 * (D : ℝ)) - 1 / (4 * (D : ℝ)) - 1 / (8 * (D : ℝ)) = 1 / (8 * (D : ℝ)) by ring]
          calc (1 / (8 * (D : ℝ))) * L1 + (1 / (4 * (D : ℝ))) * L1
              = (1 / (8 * (D : ℝ)) + 1 / (4 * (D : ℝ))) * L1 := by ring
            _ ≤ (1 / (2 * (D : ℝ)) - (4 * η_1 + 3 * η_lo)) * L1 := mul_le_mul_of_nonneg_right h_c hL1_pos.le
        calc (k : ℝ) * (C_pz * L1 ^ 5)
            ≤ Real.exp ((1 / (8 * (D : ℝ))) * L1) * Real.exp ((1 / (4 * (D : ℝ))) * L1) :=
              mul_le_mul h_pow_k hL1_56 (by positivity) (Real.exp_pos _).le
          _ = Real.exp ((1 / (8 * (D : ℝ))) * L1 + (1 / (4 * (D : ℝ))) * L1) := (Real.exp_add _ _).symm
          _ ≤ Real.exp ((1 / (2 * (D : ℝ)) - (4 * η_1 + 3 * η_lo)) * L1) := Real.exp_le_exp.mpr h1
      calc (k : ℝ) = ((k : ℝ) * (C_pz * L1 ^ 5)) / (C_pz * L1 ^ 5) := by
            field_simp [hCpz0.ne', hL1_pos.ne']
        _ ≤ Real.exp ((1 / (2 * (D : ℝ)) - (4 * η_1 + 3 * η_lo)) * L1) / (C_pz * L1 ^ 5) :=
            div_le_div_of_nonneg_right h_split_exp (by positivity)
        _ = Real.exp ((1 / (2 * (D : ℝ))) * L1) *
              ((1 / (C_pz * L1 ^ 5)) * Real.exp (-(4 * η_1 + 3 * η_lo) * L1)) := by
            rw [show (1 / (2 * (D : ℝ)) - (4 * η_1 + 3 * η_lo)) * L1 =
              (1 / (2 * (D : ℝ))) * L1 + -(4 * η_1 + 3 * η_lo) * L1 by ring, Real.exp_add]
            ring
        _ ≤ (K : ℝ) * (ℙ {ω | path X ω ∈ B_blk}).toReal :=
            mul_le_mul hK_lb hp_blk_lb
              (mul_nonneg (one_div_nonneg.mpr (mul_nonneg hCpz0.le (pow_nonneg hL1_pos.le 5)))
                (Real.exp_pos _).le)
              (Nat.cast_nonneg K)
    have hfail := prob_all_blocks_fail (K := K) hX hB_det hB_hit
    rw [hn_eq] at hfail
    have hT_gt : (1 / Real.pi - ε₀) * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 < (T : ℝ) := by
      have hlog_n : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
      have hlog_M : ((k : ℝ) * (1 - 1 / (D : ℝ) - 1 / (k : ℝ))) * Real.log 2 ≤ L1 := by
        have hm_eq : (k : ℝ) * (1 - 1 / (D : ℝ) - 1 / (k : ℝ)) ≤ (m : ℝ) := by
          have hk0 : (k : ℝ) ≠ 0 := by
            have : (2 ^ 30 : ℝ) ≤ k := by linarith only [hk_real, hKL_ge, hD2_nn]
            linarith only [this]
          have hkd : ((k / D : ℕ) : ℝ) ≤ (k : ℝ) / (D : ℝ) := by
            have h1 : (k / D) * D ≤ k := Nat.div_mul_le_self k D
            have h2 : ((k / D : ℕ) : ℝ) * (D : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
            exact (le_div_iff₀ hD_pos).mpr h2
          have hm_sub : (k : ℝ) - (k : ℝ) / (D : ℝ) - 1 ≤ (m : ℝ) := by
            have hm_nat : k = m + k / D + 1 := by dsimp [m]; omega
            have hm_cast : (k : ℝ) = (m : ℝ) + ((k / D : ℕ) : ℝ) + 1 := by exact_mod_cast hm_nat
            linarith only [hm_cast, hkd]
          calc (k : ℝ) * (1 - 1 / (D : ℝ) - 1 / (k : ℝ)) = (k : ℝ) - (k : ℝ) / (D : ℝ) - 1 := by
                field_simp [hk0]
            _ ≤ (m : ℝ) := hm_sub
        have hpow_le : (2 : ℝ) ^ m ≤ M₁ := by dsimp [M₁, M]; push_cast; linarith only
        have hlog := Real.log_le_log (by positivity) hpow_le
        rw [Real.log_pow] at hlog
        exact (mul_le_mul_of_nonneg_right hm_eq hlog2_pos.le).trans hlog
      have hratio_ge : 1 - δ₁ / 8 ≤ 1 - 1 / (D : ℝ) - 1 / (k : ℝ) := by
        have hk_inv : 1 / (k : ℝ) ≤ δ₁ / 16 := by
          have h1 : 1 / (k : ℝ) ≤ 1 / (D : ℝ) := by
            exact one_div_le_one_div_of_le hD_pos (by exact_mod_cast (by omega : D ≤ k))
          exact h1.trans hD_inv
        linarith only [hD_inv, hk_inv]
      have hL1_lb_n : (1 - δ₁ / 8) * Real.log ((2 ^ k : ℕ) : ℝ) ≤ L1 := by
        rw [hlog_n]
        calc (1 - δ₁ / 8) * ((k : ℝ) * Real.log 2)
            ≤ (1 - 1 / (D : ℝ) - 1 / (k : ℝ)) * ((k : ℝ) * Real.log 2) :=
              mul_le_mul_of_nonneg_right hratio_ge (by positivity)
          _ = ((k : ℝ) * (1 - 1 / (D : ℝ) - 1 / (k : ℝ))) * Real.log 2 := by ring
          _ ≤ L1 := hlog_M
      have hsq : (1 - δ₁ / 4) * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 ≤ L1 ^ 2 := by
        have h1 : 1 - δ₁ / 4 ≤ (1 - δ₁ / 8) ^ 2 := by nlinarith only [hδ₁_pos, hδ₁_le]
        have h0 : 0 ≤ (1 - δ₁ / 8) * Real.log ((2 ^ k : ℕ) : ℝ) :=
          mul_nonneg (by linarith only [hδ₁_le]) (by rw [hlog_n]; positivity)
        calc (1 - δ₁ / 4) * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2
            ≤ (1 - δ₁ / 8) ^ 2 * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
          _ = ((1 - δ₁ / 8) * Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 := by ring
          _ ≤ L1 ^ 2 := pow_le_pow_left₀ h0 hL1_lb_n 2
      have hstrict : 1 / Real.pi - ε₀ < a * (1 - δ₁ / 4) / Real.pi := by
        have h1 : 1 / Real.pi - ε₀ = (1 - δ₁) / Real.pi := by
          dsimp [δ₁]; field_simp [hpi.ne']
        have h2 : a * (1 - δ₁ / 4) / Real.pi = (1 - δ₁ / 4) ^ 2 / Real.pi := by dsimp [a]; ring
        rw [h1, h2, div_lt_div_iff_of_pos_right hpi]
        nlinarith only [hδ₁_pos, hδ₁_le]
      have hlogn_pos : 0 < Real.log ((2 ^ k : ℕ) : ℝ) := by
        rw [hlog_n]
        have : (0 : ℝ) < k := by linarith only [hk_real, hKL_ge, hD2_nn]
        positivity
      have h_lt_v : (1 / Real.pi - ε₀) * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 < a * L1 ^ 2 / Real.pi := by
        calc (1 / Real.pi - ε₀) * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2
            < (a * (1 - δ₁ / 4) / Real.pi) * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 :=
              mul_lt_mul_of_pos_right hstrict (sq_pos_of_pos hlogn_pos)
          _ = a * ((1 - δ₁ / 4) * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2) / Real.pi := by ring
          _ ≤ a * L1 ^ 2 / Real.pi :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq ha_pos.le) hpi.le
      exact lt_of_lt_of_le h_lt_v (Nat.le_ceil _)
    have hset_sub : {ω : Ω | (maxLocalTime X (2 ^ k) ω : ℝ) / (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 <
          1 / Real.pi - ε₀} ⊆
        {ω | maxLocalTime X (2 ^ k) ω < T} := by
      intro ω hω
      rw [Set.mem_ofPred_eq] at hω ⊢
      have hlogn_pos : 0 < Real.log ((2 ^ k : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]; push_cast
        have : (0 : ℝ) < k := by linarith only [hk_real, hKL_ge, hD2_nn]
        positivity
      have hlt_real : (maxLocalTime X (2 ^ k) ω : ℝ) <
          (1 / Real.pi - ε₀) * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 :=
        (div_lt_iff₀ (sq_pos_of_pos hlogn_pos)).mp hω
      exact Nat.cast_lt.mp (lt_trans hlt_real hT_gt)
    have hprob_real : (ℙ {ω | (maxLocalTime X (2 ^ k) ω : ℝ) / (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 <
          1 / Real.pi - ε₀}).toReal ≤ Real.exp (-(k : ℝ)) := by
      have hm1 := ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hset_sub)
      have hexp_cmp : Real.exp (-((K : ℝ) * (ℙ {ω | path X ω ∈ B_blk}).toReal)) ≤
          Real.exp (-(k : ℝ)) := Real.exp_le_exp.mpr (by linarith only [hKp_ge_k])
      exact hm1.trans (hfail.trans hexp_cmp)
    rw [← ENNReal.ofReal_toReal (measure_ne_top ℙ _)]
    exact ENNReal.ofReal_le_ofReal hprob_real
  have hsub_ε : ∀ k : ℕ,
      ℙ {ω | (maxLocalTime X (2 ^ k) ω : ℝ) / (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 <
        1 / Real.pi - ε} ≤
      (if k < K₀ then (1 : ℝ≥0∞) else 0) + ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
    intro k
    by_cases hk : k < K₀
    · rw [if_pos hk]
      exact prob_le_one.trans (le_add_right le_rfl)
    · push Not at hk
      rw [if_neg (not_lt.mpr hk), zero_add]
      have hsub_set : {ω : Ω | (maxLocalTime X (2 ^ k) ω : ℝ) / (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 <
            1 / Real.pi - ε} ⊆
          {ω | (maxLocalTime X (2 ^ k) ω : ℝ) / (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 <
            1 / Real.pi - ε₀} := by
        intro ω hω
        rw [Set.mem_ofPred_eq] at hω ⊢
        linarith only [hω, hε₀_le]
      exact (measure_mono hsub_set).trans (htail_bound k hk)
  have hsum_exp : Summable (fun k : ℕ ↦ Real.exp (-(k : ℝ))) := by
    have heq : (fun k : ℕ ↦ Real.exp (-(k : ℝ))) = fun k : ℕ ↦ (Real.exp (-1)) ^ k := by
      ext k; rw [← Real.exp_nat_mul]; congr 1; ring
    rw [heq]
    exact summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num))
  have hsum_ne_top : (∑' k : ℕ, ℙ {ω | (maxLocalTime X (2 ^ k) ω : ℝ) /
      (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 < 1 / Real.pi - ε}) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsub_ε)
    rw [ENNReal.tsum_add]
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · have hfin : (∑' k : ℕ, if k < K₀ then (1 : ℝ≥0∞) else 0) =
          ∑ k ∈ Finset.range K₀, (1 : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := Finset.range K₀) fun k hk ↦ if_neg (by simpa [Finset.mem_range] using hk)]
        exact Finset.sum_congr rfl fun k hk ↦ if_pos (Finset.mem_range.mp hk)
      rw [hfin, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact ENNReal.natCast_ne_top K₀
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (Real.exp_pos _).le) hsum_exp]
      exact ENNReal.ofReal_ne_top
  exact hsum_ne_top

end OMA.H2DPRZ

theorem OMA.solution : OMA.R_Erdos1166_erdos_1166_variants_dembo_peres_rosen_zeitouni_R1.H2 := OMA.H2DPRZ.h2_main
