import OMAReductions.R_Erdos1164_erdos_1164_R1

-- Step Erdos1164.erdos_1164.R1.H1: hypothesis H1 of reduction Erdos1164.erdos_1164.R1
-- Credit: @koolkao
--
-- Proof (elementary; Révész 1990, Kesten, see Dembo–Peres–Rosen–Zeitouni 2004, Section 1.3):
-- (1) Fixed-time Markov property and block independence, exact return probabilities (Wallis)
--     and renewal at returns to the origin (OMA.H1Proof, OMA.H3Proof: the Erdős–Taylor proofs).
-- (2) Few returns are unlikely: P(L_n(0) < K + 1) ≤ K q_s with K = ⌈δ log n⌉ and s ≈ 2 √n.
-- (3) P(S_t = x) is bounded below via C(2j, j + k) ≥ C(2j, j)(1 - 2k²/j), so E N_x(m) ≳ log r.
--     First visit plus last exit gives E N_x(m) ≤ G_m² · P(hit x before returning to 0), so this
--     probability is at least 1/(300 log r) for |x| ≤ r and m = 2 r⁴ + 1.
-- (4) Renewal with avoidance: P(L_n(0) ≥ K + 1, x not visited) ≤ (1 - 1/(300 log r))^K.
-- (5) A union bound over the (2r + 1)² sites of the box, with r = ⌈exp(c √(log n))⌉ and
--     c = ε/(16 π · 3000), finishes the proof.
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos1165

namespace OMA.H1Proof

/-- Partial sums of a step sequence. -/
def pos (y : ℕ → ℤ × ℤ) (t : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range t, y i

/-- Number of visits to the origin at times `0, …, n`. -/
def visits (y : ℕ → ℤ × ℤ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun t ↦ pos y t = 0).card

def sh (t : ℕ) (y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ y (t + i)

def path {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : ℕ → ℤ × ℤ := fun i ↦ X i ω

/-- `A` depends only on the first `m` coordinates. -/
def Det (m : ℕ) (A : Set (ℕ → ℤ × ℤ)) : Prop :=
  ∀ y y' : ℕ → ℤ × ℤ, (∀ i < m, y i = y' i) → y ∈ A → y' ∈ A

lemma pos_shift (y : ℕ → ℤ × ℤ) (t s : ℕ) : pos y (t + s) = pos y t + pos (sh t y) s :=
  Finset.sum_range_add _ _ _

lemma pos_congr {y y' : ℕ → ℤ × ℤ} {m t : ℕ} (h : ∀ i < m, y i = y' i) (ht : t ≤ m) :
    pos y t = pos y' t :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

lemma visits_congr {y y' : ℕ → ℤ × ℤ} {n : ℕ} (h : ∀ i < n, y i = y' i) :
    visits y n = visits y' n := by
  unfold visits
  congr 1
  refine Finset.filter_congr fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  rw [pos_congr h (by omega)]

/-- extension by zero of a finite window -/
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
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
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

lemma sh_zero (y : ℕ → ℤ × ℤ) : sh 0 y = y := funext fun i ↦ by simp [sh]

lemma path_eq {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (A : Set (ℕ → ℤ × ℤ)) :
    {ω | path X ω ∈ A} = {ω | sh 0 (path X ω) ∈ A} := by
  simp only [sh_zero]

/-- fixed-time Markov property: shifting does not change probabilities -/
lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)}
    (hA : Det m A) (j : ℕ) :
    ℙ {ω | sh j (path X ω) ∈ A} = ℙ {ω | path X ω ∈ A} := by
  have hT : MeasurableSet {z : Fin m → ℤ × ℤ | ext m z ∈ A} := (Set.to_countable _).measurableSet
  rw [path_eq, det_pre X hA, det_pre X hA, ← Measure.map_apply (meas_window hX m j) hT,
    ← Measure.map_apply (meas_window hX m 0) hT, map_window hX, map_window hX]

end OMA.H1Proof

namespace OMA.H1Proof

lemma preA {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det t A) :
    {ω | path X ω ∈ A} = (fun ω (i : Finset.range t) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : i ∈ Finset.range t then z ⟨i, h⟩ else 0) ∈ A} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [hi, path]
  · exact hA _ _ fun i hi ↦ by simp [hi, path]

lemma preB {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t s : ℕ} {B : Set (ℕ → ℤ × ℤ)} (hB : Det s B) :
    {ω | sh t (path X ω) ∈ B} = (fun ω (i : Finset.Ico t (t + s)) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then z ⟨t + i, h⟩ else 0) ∈ B} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  have key : ∀ i < s, sh t (path X ω) i =
      (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then
        (fun (i : Finset.Ico t (t + s)) ↦ X i ω) ⟨t + i, h⟩ else 0) i := by
    intro i hi
    have hm : t + i ∈ Finset.Ico t (t + s) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    simp [hm, sh, path]
  constructor
  · exact hB _ _ key
  · exact hB _ _ fun i hi ↦ (key i hi).symm

/-- independence of disjoint blocks, combined with the Markov property -/
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

end OMA.H1Proof

namespace OMA.H1Proof

/-- number of `±1` paths of length `t` ending at `u` -/
def c : ℕ → ℤ → ℕ
  | 0, u => if u = 0 then 1 else 0
  | t + 1, u => c t (u - 1) + c t (u + 1)

lemma c_neg : ∀ (t : ℕ) (u : ℤ), u < -(t : ℤ) → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_neg t (u - 1) (by push_cast at h; omega), c_neg t (u + 1) (by push_cast at h; omega)]

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

lemma c_odd0 (j : ℕ) : c (2 * j + 1) 0 = 0 := c_odd _ _ (by push_cast; omega)

/-- the 2D count factorizes after the 45 degree rotation -/
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

end OMA.H1Proof

namespace OMA.H1Proof

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
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [← pos_congr h le_rfl, hy]

lemma det_zero (e : ℤ × ℤ) : Det 1 {y | y 0 = e} := fun y y' h hy ↦ by
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [← h 0 one_pos, hy]

lemma prob_pos_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (x e : ℤ × ℤ)
    (he : e ∈ steps) :
    ℙ {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}} =
      ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_block hX (det_pos t (x - e)) (det_zero e)]
  congr 1
  exact prob_step_eq hX 0 he

lemma pos_succ (y : ℕ → ℤ × ℤ) (t : ℕ) : pos y (t + 1) = pos y t + y t :=
  Finset.sum_range_succ _ _

/-- the return probability bound, in counting form -/
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
        simp only [pos, Finset.range_zero, Finset.sum_empty, Set.mem_setOf_eq,
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
      simp only [Set.mem_setOf_eq, pos_succ] at hω
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

end OMA.H1Proof

namespace OMA.H1Proof

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

/-- return probability, as a real number -/
noncomputable def u {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = 0}).toReal

lemma prob_zero_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) :
    u X t * 4 ^ t ≤ (c t 0 : ℝ) ^ 2 := by
  have h := prob_pos_le hX t 0 0
  simp only [add_zero, sub_zero] at h
  change ℙ {ω | pos (path X ω) t = 0} * 4 ^ t ≤ _ at h
  have h' : (ℙ {ω | pos (path X ω) t = 0} * 4 ^ t).toReal ≤ ((c t 0 * c t 0 : ℕ) : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  unfold u
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4] at h'
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal * 4 ^ t ≤ ((c t 0 * c t 0 : ℕ) : ℝ) := h'
    _ = (c t 0 : ℝ) ^ 2 := by push_cast; ring

lemma u_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : 0 ≤ u X t :=
  ENNReal.toReal_nonneg

lemma u_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : u X t ≤ 1 := by
  unfold u
  have : ℙ {ω | pos (path X ω) t = 0} ≤ 1 := prob_le_one
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) this
    _ = 1 := by simp

lemma u_odd {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) : u X (2 * j + 1) = 0 := by
  have h := prob_zero_le hX (2 * j + 1)
  rw [c_odd0] at h
  have h0 := u_nonneg X (2 * j + 1)
  have hp : (0 : ℝ) < 4 ^ (2 * j + 1) := by positivity
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  nlinarith

lemma u_even {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) (hj : 1 ≤ j) :
    u X (2 * j) ≤ 1 / (Real.pi * j) := by
  have h := prob_zero_le hX (2 * j)
  rw [c_even, pow_mul] at h
  norm_num at h
  refine le_trans ?_ (cb_sq_le j hj)
  rw [le_div_iff₀ (by positivity)]
  exact h

lemma u_pair {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) :
    u X (2 * j + 1) + u X (2 * j + 2) ≤ 1 / (Real.pi * ((j : ℝ) + 1)) := by
  rw [u_odd hX, zero_add, show 2 * j + 2 = 2 * (j + 1) by ring]
  have := u_even hX (j + 1) (by omega)
  push_cast at this
  exact this

end OMA.H1Proof

namespace OMA.H1Proof

def NoRet (m : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∀ s, 1 ≤ s → s ≤ m → pos y s ≠ 0}

def FR (t : ℕ) : Set (ℕ → ℤ × ℤ) := {y | pos y t = 0 ∧ ∀ s, 1 ≤ s → s < t → pos y s ≠ 0}

def Vis (n k : ℕ) : Set (ℕ → ℤ × ℤ) := {y | k ≤ visits y n}

lemma det_noRet (m : ℕ) : Det m (NoRet m) := fun y y' h hy s h1 h2 ↦ by
  rw [← pos_congr h h2]; exact hy s h1 h2

lemma det_FR (t : ℕ) : Det t (FR t) := fun y y' h hy ↦
  ⟨by rw [← pos_congr h le_rfl]; exact hy.1,
   fun s h1 h2 ↦ by rw [← pos_congr h h2.le]; exact hy.2 s h1 h2⟩

lemma det_vis (n k : ℕ) : Det n (Vis n k) := fun y y' h hy ↦ by
  simp only [Vis, Set.mem_setOf_eq] at hy ⊢
  rw [← visits_congr h]; exact hy

lemma visits_mono (y : ℕ → ℤ × ℤ) {m n : ℕ} (h : m ≤ n) : visits y m ≤ visits y n :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

lemma pos_zero (y : ℕ → ℤ × ℤ) : pos y 0 = 0 := by simp [pos]

lemma pos_sh (y : ℕ → ℤ × ℤ) {t : ℕ} (ht : pos y t = 0) (s : ℕ) :
    pos (sh t y) s = pos y (t + s) := by
  rw [pos_shift, ht, zero_add]

lemma renewal_subset (n k : ℕ) (hk : 1 ≤ k) :
    Vis n (k + 1) ⊆ {y | ∃ t ∈ Finset.Icc 1 n, y ∈ FR t ∧ sh t y ∈ Vis (n - t) k} := by
  intro y hy
  simp only [Vis, Set.mem_setOf_eq, visits] at hy
  set V := (Finset.range (n + 1)).filter fun t ↦ pos y t = 0 with hV
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hcard : k ≤ (V.erase 0).card := by rw [Finset.card_erase_of_mem h0]; omega
  have hne : (V.erase 0).Nonempty := Finset.card_pos.mp (by omega)
  set t := (V.erase 0).min' hne with ht
  have htm : t ∈ V.erase 0 := Finset.min'_mem _ hne
  have htm' := Finset.mem_erase.mp htm
  have htV := Finset.mem_filter.mp htm'.2
  have htn : t < n + 1 := Finset.mem_range.mp htV.1
  refine ⟨t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨htV.2, fun s h1 h2 hs ↦ ?_⟩, ?_⟩
  · have hsV : s ∈ V.erase 0 :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩⟩
    have := Finset.min'_le (V.erase 0) s hsV
    omega
  · simp only [Vis, Set.mem_setOf_eq, visits]
    refine hcard.trans (Finset.card_le_card_of_injOn (fun a ↦ a - t) ?_ ?_)
    · intro a ha
      have ha' := Finset.mem_erase.mp ha
      have haV := Finset.mem_filter.mp ha'.2
      have hta : t ≤ a := Finset.min'_le (V.erase 0) a ha
      have han : a < n + 1 := Finset.mem_range.mp haV.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (show a - t < n - t + 1 by omega), ?_⟩
      rw [pos_sh y htV.2, show t + (a - t) = a by omega]
      exact haV.2
    · intro a ha b hb hab
      have hta : t ≤ a := Finset.min'_le (V.erase 0) a ha
      have htb : t ≤ b := Finset.min'_le (V.erase 0) b hb
      have hab' : a - t = b - t := hab
      omega

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

end OMA.H1Proof

namespace OMA.H1Proof

open Real

lemma sum_pairs (u : ℕ → ℝ) (M : ℕ) :
    ∑ t ∈ Finset.range (2 * M + 1), u t =
      u 0 + ∑ j ∈ Finset.range M, (u (2 * j + 1) + u (2 * j + 2)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

lemma green_le (u : ℕ → ℝ) (hu0 : ∀ t, 0 ≤ u t) (hu00 : u 0 ≤ 1)
    (hpair : ∀ j : ℕ, u (2 * j + 1) + u (2 * j + 2) ≤ 1 / (π * ((j : ℝ) + 1))) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), u t ≤ 1 + (1 + Real.log n) / π := by
  have hsub : ∑ t ∈ Finset.range (n + 1), u t ≤ ∑ t ∈ Finset.range (2 * n + 1), u t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun t _ _ ↦ hu0 t
  refine hsub.trans ?_
  rw [sum_pairs]
  have hh : ∑ j ∈ Finset.range n, (u (2 * j + 1) + u (2 * j + 2)) ≤ (harmonic n : ℝ) / π := by
    calc ∑ j ∈ Finset.range n, (u (2 * j + 1) + u (2 * j + 2))
        ≤ ∑ j ∈ Finset.range n, 1 / (π * ((j : ℝ) + 1)) := Finset.sum_le_sum fun j _ ↦ hpair j
      _ = (harmonic n : ℝ) / π := by
        rw [harmonic, Rat.cast_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        push_cast
        rw [one_div, mul_inv, div_eq_mul_inv, mul_comm]
  have hlog := harmonic_le_one_add_log n
  have : (harmonic n : ℝ) / π ≤ (1 + Real.log n) / π := by gcongr
  linarith

end OMA.H1Proof

namespace OMA.H1Proof

open Real

noncomputable def q {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (m : ℕ) : ℝ :=
  (ℙ {ω | path X ω ∈ NoRet m}).toReal

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma q_nonneg (m : ℕ) : 0 ≤ q X m := ENNReal.toReal_nonneg

lemma q_le_one (m : ℕ) : q X m ≤ 1 := by
  unfold q
  calc (ℙ {ω | path X ω ∈ NoRet m}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) prob_le_one
    _ = 1 := by simp

lemma q_anti : Antitone (q X) := by
  intro a b hab
  unfold q
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω s h1 h2 ↦ ?_)
  exact hω s h1 (h2.trans hab)

end OMA.H1Proof

namespace OMA.H3Proof
open OMA.H1Proof

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma meas_block (hX : IsSimpleRandomWalkSteps X) {t s : ℕ} {A B : Set (ℕ → ℤ × ℤ)}
    (hA : Det t A) (hB : Det s B) :
    MeasurableSet {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} := by
  have h1 : MeasurableSet {ω | path X ω ∈ A} := by rw [path_eq]; exact det_meas hX hA 0
  exact h1.inter (det_meas hX hB t)

/-- the return probability lower bound, in counting form -/
lemma prob_pos_ge (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞) ≤
      ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      have : {ω | pos (path X ω) 0 = ((0 : ℤ), (0 : ℤ))} = Set.univ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, pos_zero]; rfl
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
      simp only [Set.mem_setOf_eq, pos_succ]
      have key : ∀ e, ω ∈ E e → pos (path X ω) t + path X ω t = x := by
        rintro e ⟨h1, h2⟩
        simp only [Set.mem_setOf_eq] at h1 h2
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

end OMA.H3Proof

namespace OMA.H3Proof
open OMA.H1Proof Real

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma cb_sq_ge (j : ℕ) : 1 / (π * ((j : ℝ) + 1)) ≤ ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j := by
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
      ≤ π / 2 * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by gcongr
    _ ≤ (j.centralBinom : ℝ) ^ 2 * (π * ((j : ℝ) + 1)) := by nlinarith

lemma u_even_ge (hX : IsSimpleRandomWalkSteps X) (j : ℕ) :
    1 / (π * ((j : ℝ) + 1)) ≤ u X (2 * j) := by
  have h := prob_pos_ge hX (2 * j) 0 0
  simp only [add_zero, sub_zero] at h
  change _ ≤ ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j) at h
  have h' : ((c (2 * j) 0 * c (2 * j) 0 : ℕ) : ℝ≥0∞).toReal ≤
      (ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j)).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4, c_even, pow_mul] at h'
  norm_num at h'
  refine (cb_sq_ge j).trans ?_
  rw [div_le_iff₀ (by positivity)]
  unfold u
  nlinarith

lemma green_ge (hX : IsSimpleRandomWalkSteps X) (M : ℕ) :
    Real.log (M + 1) / π ≤ ∑ t ∈ Finset.range (2 * M + 1), u X t := by
  have hpi := Real.pi_pos
  rw [sum_pairs]
  have h0 : 1 ≤ u X 0 := by
    have hu : u X 0 = 1 := by
      unfold u
      have : {ω | pos (path X ω) 0 = 0} = Set.univ := by
        ext ω; simp [pos_zero]
      rw [this, measure_univ]; simp
    rw [hu]
  have hs : ∑ j ∈ Finset.range M, 1 / (π * (((j + 1 : ℕ) : ℝ) + 1)) ≤
      ∑ j ∈ Finset.range M, (u X (2 * j + 1) + u X (2 * j + 2)) := by
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have := u_even_ge hX (j + 1)
    rw [show 2 * (j + 1) = 2 * j + 2 by ring] at this
    linarith [u_nonneg X (2 * j + 1)]
  have hH : ∑ j ∈ Finset.range M, 1 / (π * (((j + 1 : ℕ) : ℝ) + 1)) =
      ((harmonic (M + 1) : ℝ) - 1) / π := by
    rw [harmonic, Finset.sum_range_succ', Rat.cast_add, Rat.cast_sum]
    simp only [Nat.cast_add, Nat.cast_one, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one, zero_add, inv_one, add_sub_cancel_right]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [one_div, mul_inv, div_eq_mul_inv, mul_comm]
  have hlog := log_add_one_le_harmonic (M + 1)
  have hcast : Real.log ((M : ℝ) + 1) ≤ Real.log (((M + 1 + 1 : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have e : Real.log (M + 1) / π ≤ 1 + ((harmonic (M + 1) : ℝ) - 1) / π := by
    have h1 : Real.log (M + 1) / π ≤ (harmonic (M + 1) : ℝ) / π := by
      gcongr; exact hcast.trans hlog
    have h2 : (harmonic (M + 1) : ℝ) / π = ((harmonic (M + 1) : ℝ) - 1) / π + 1 / π := by ring
    have h3 : 1 / π ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
    linarith
  linarith

lemma lastexit_le (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1),
      ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)} ≤ 1 := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (n + 1))) fun t ↦
      {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h3, h4⟩
    simp only [Set.mem_setOf_eq] at h1 h3
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    rcases lt_or_gt_of_ne hab with h | h
    · apply h2 (b - a) (by omega) (by omega)
      rw [pos_sh _ h1, show a + (b - a) = b by omega]; exact h3
    · apply h4 (a - b) (by omega) (by omega)
      rw [pos_sh _ h3, show b + (a - b) = a by omega]; exact h1
  calc ∑ t ∈ Finset.range (n + 1),
        ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)}
      = ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)} :=
        Finset.sum_congr rfl fun t _ ↦ (prob_block hX (det_pos t 0) (det_noRet (n - t))).symm
    _ = ℙ (⋃ t ∈ Finset.range (n + 1),
          {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)}) :=
        (measure_biUnion_finset hdisj fun t _ ↦ meas_block hX (det_pos t 0)
          (det_noRet (n - t))).symm
    _ ≤ 1 := prob_le_one

lemma q_green (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    q X n * ∑ t ∈ Finset.range (n + 1), u X t ≤ 1 := by
  have h := lastexit_le hX n
  have hne : ∀ t ∈ Finset.range (n + 1), ℙ {ω | pos (path X ω) t = 0} *
      ℙ {ω | path X ω ∈ NoRet (n - t)} ≠ ⊤ := fun t _ ↦
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have h' := ENNReal.toReal_mono ENNReal.one_ne_top h
  rw [ENNReal.toReal_sum hne] at h'
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul] at h'
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun t ht ↦ ?_) h'
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (q_anti (Nat.sub_le n t)) (u_nonneg X t)

/-- the upper bound on the escape probability at even times -/
lemma q_le (hX : IsSimpleRandomWalkSteps X) (M : ℕ) :
    q X (2 * M) * Real.log (M + 1) ≤ π := by
  have hpi := Real.pi_pos
  have h1 := q_green hX (2 * M)
  have h2 := green_ge hX M
  have h3 : q X (2 * M) * (Real.log (M + 1) / π) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left h2 (q_nonneg _)) h1
  have e : q X (2 * M) * Real.log (M + 1) = q X (2 * M) * (Real.log (M + 1) / π) * π := by
    rw [mul_assoc, div_mul_cancel₀ _ hpi.ne']
  rw [e]
  nlinarith

end OMA.H3Proof

namespace OMA.H3Proof
open OMA.H1Proof Real

lemma visits_sh_le (y : ℕ → ℤ × ℤ) {t n N : ℕ} (ht : 1 ≤ t) (hp : pos y t = 0)
    (hN : t + n ≤ N) : visits (sh t y) n + 1 ≤ visits y N := by
  unfold visits
  set V := (Finset.range (N + 1)).filter fun a ↦ pos y a = 0
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hc := Finset.card_erase_of_mem h0
  have hle : ((Finset.range (n + 1)).filter fun a ↦ pos (sh t y) a = 0).card ≤ (V.erase 0).card := by
    refine Finset.card_le_card_of_injOn (fun a ↦ t + a) ?_ ?_
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      have han := Finset.mem_range.mp ha'.1
      refine Finset.mem_erase.mpr ⟨show t + a ≠ 0 by omega, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (show t + a < N + 1 by omega), ?_⟩⟩
      show pos y (t + a) = 0
      rw [← pos_sh y hp]; exact ha'.2
    · intro a _ b _ hab
      have : t + a = t + b := hab
      omega
  have hpos : 0 < V.card := Finset.card_pos.mpr ⟨0, h0⟩
  omega

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma compl_noRet (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    ℙ {ω | path X ω ∈ NoRet n}ᶜ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} := by
  have hU : {ω | path X ω ∈ NoRet n}ᶜ = ⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ FR t} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, NoRet, Set.mem_iUnion, FR,
      Finset.mem_Icc, exists_prop, not_forall, not_not]
    constructor
    · rintro ⟨s, h1, h2, hs⟩
      classical
      let P : ℕ → Prop := fun s ↦ 1 ≤ s ∧ s ≤ n ∧ pos (path X ω) s = 0
      have hex : ∃ s, P s := ⟨s, h1, h2, hs⟩
      refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.1⟩,
        (Nat.find_spec hex).2.2, fun r hr1 hr2 hr ↦ ?_⟩
      exact Nat.find_min hex hr2 ⟨hr1, by have := (Nat.find_spec hex).2.1; omega, hr⟩
    · rintro ⟨t, ⟨h1, h2⟩, ht, -⟩
      exact ⟨t, h1, h2, ht⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) fun t ↦ {ω | path X ω ∈ FR t} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq, FR] at h1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
    · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
  rw [hU, measure_biUnion_finset hdisj fun t _ ↦ by rw [path_eq]; exact det_meas hX (det_FR t) 0]

lemma renewal_lower (hX : IsSimpleRandomWalkSteps X) (s : ℕ) :
    ∀ k, ℙ {ω | path X ω ∈ NoRet s}ᶜ ^ k ≤ ℙ {ω | path X ω ∈ Vis (k * s) (k + 1)}
  | 0 => by
    have : {ω | path X ω ∈ Vis (0 * s) (0 + 1)} = Set.univ := by
      ext ω
      simp only [Vis, Set.mem_setOf_eq, Set.mem_univ, iff_true, visits]
      exact Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨by simp, pos_zero _⟩⟩
    rw [this, measure_univ, pow_zero]
  | k + 1 => by
    have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 s)) fun t ↦
        {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (k * s) (k + 1)} := by
      intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      rintro ω ⟨h1, -⟩ ⟨h2, -⟩
      simp only [FR, Set.mem_setOf_eq] at h1 h2
      rcases lt_or_gt_of_ne hab with h | h
      · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
      · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
    calc ℙ {ω | path X ω ∈ NoRet s}ᶜ ^ (k + 1)
        = ℙ {ω | path X ω ∈ NoRet s}ᶜ * ℙ {ω | path X ω ∈ NoRet s}ᶜ ^ k := pow_succ' _ _
      _ ≤ ℙ {ω | path X ω ∈ NoRet s}ᶜ * ℙ {ω | path X ω ∈ Vis (k * s) (k + 1)} := by
          gcongr; exact renewal_lower hX s k
      _ = ∑ t ∈ Finset.Icc 1 s,
            ℙ {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (k * s) (k + 1)} := by
          rw [compl_noRet hX, Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ ↦
            (prob_block hX (det_FR t) (det_vis (k * s) (k + 1))).symm
      _ = ℙ (⋃ t ∈ Finset.Icc 1 s,
            {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (k * s) (k + 1)}) :=
          (measure_biUnion_finset hdisj fun t _ ↦
            meas_block hX (det_FR t) (det_vis _ _)).symm
      _ ≤ ℙ {ω | path X ω ∈ Vis ((k + 1) * s) (k + 1 + 1)} := by
          refine measure_mono fun ω hω ↦ ?_
          obtain ⟨t, ht, h1, h2⟩ := Set.mem_iUnion₂.mp hω
          have ht' := Finset.mem_Icc.mp ht
          simp only [Vis, Set.mem_setOf_eq] at h2 ⊢
          have := visits_sh_le (path X ω) ht'.1 h1.1
            (show t + k * s ≤ (k + 1) * s by nlinarith)
          omega

end OMA.H3Proof

namespace OMA.H3Proof
open Real

end OMA.H3Proof

namespace OMA.H3Proof
open OMA.H1Proof Real Filter

end OMA.H3Proof


namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

/-- binomial coefficients near the centre: `C(2j, j+k) ≥ C(2j, j) (1 - 2k²/j)` -/
lemma choose_near (j : ℕ) (hj : 1 ≤ j) :
    ∀ k : ℕ, k ≤ j → (j.centralBinom : ℝ) * (1 - 2 * (k : ℝ) ^ 2 / j) ≤ ((2 * j).choose (j + k) : ℝ)
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
    have hjk : ((j - k : ℕ) : ℝ) = j - k := by push_cast [Nat.cast_sub (show k ≤ j by omega)]; ring
    rw [hjk] at hrec'
    push_cast at hrec'
    have hpos : (0 : ℝ) < j + k + 1 := by positivity
    have hcb : (0 : ℝ) ≤ j.centralBinom := by positivity
    have hf : ((2 * j).choose (j + k + 1) : ℝ) =
        ((2 * j).choose (j + k) : ℝ) * ((j - k) / (j + k + 1)) := by
      rw [mul_div_assoc', eq_div_iff hpos.ne']
      exact hrec'
    rw [show j + (k + 1) = j + k + 1 by ring, hf]
    have hρ0 : 0 ≤ ((j : ℝ) - k) / (j + k + 1) := by
      have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hk
      apply div_nonneg <;> linarith
    have hρ : 1 - (2 * k + 1) / (j : ℝ) ≤ ((j : ℝ) - k) / (j + k + 1) := by
      rw [le_div_iff₀ hpos, sub_mul, div_mul_eq_mul_div, one_mul]
      have : (2 * (k : ℝ) + 1) * (j + k + 1) / j ≥ 2 * k + 1 := by
        rw [ge_iff_le, le_div_iff₀ hj']; nlinarith
      linarith
    have hk1 : (k : ℝ) + 1 ≤ j := by exact_mod_cast hk
    rcases le_or_gt (1 - 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / j) 0 with hT | hT
    · exact (mul_nonpos_of_nonneg_of_nonpos hcb hT).trans (by positivity)
    have hT' : 2 * ((k + 1 : ℕ) : ℝ) ^ 2 < j := by
      have := (div_lt_one hj').mp (by linarith : 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / j < 1)
      exact this
    push_cast at hT'
    have ha : 0 ≤ 1 - 2 * (k : ℝ) ^ 2 / j := by
      rw [sub_nonneg, div_le_one hj']; nlinarith
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

lemma choose_half (j k : ℕ) (hj : 1 ≤ j) (hk : 4 * k ^ 2 ≤ j) :
    (j.centralBinom : ℝ) / 2 ≤ ((2 * j).choose (j + k) : ℝ) := by
  have hkj : k ≤ j := by nlinarith
  refine le_trans ?_ (choose_near j hj k hkj)
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have : 2 * (k : ℝ) ^ 2 / j ≤ 1 / 2 := by
    rw [div_le_iff₀ hj']
    have : (4 * k ^ 2 : ℝ) ≤ j := by exact_mod_cast hk
    linarith
  have hcb : (0 : ℝ) ≤ j.centralBinom := by positivity
  nlinarith

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma c_symm : ∀ (t : ℕ) (u : ℤ), c t (-u) = c t u
  | 0, u => by simp [c]
  | t + 1, u => by
    simp only [c]
    rw [show -u - 1 = -(u + 1) by ring, show -u + 1 = -(u - 1) by ring, c_symm t, c_symm t]
    ring

lemma c_even_ge (j : ℕ) (hj : 1 ≤ j) (u : ℤ) (hu : Even u) (hu2 : u ^ 2 ≤ j) :
    (j.centralBinom : ℝ) / 2 ≤ (c (2 * j) u : ℝ) := by
  obtain ⟨k, rfl⟩ := hu
  have key : ∀ k' : ℕ, (k' : ℤ) = |k| → (j.centralBinom : ℝ) / 2 ≤ (c (2 * j) (k + k) : ℝ) := by
    intro k' hk'
    have hk2 : 4 * k' ^ 2 ≤ j := by
      have : ((4 * k' ^ 2 : ℕ) : ℤ) ≤ j := by
        push_cast; rw [hk']
        have : |k| ^ 2 = k ^ 2 := sq_abs k
        nlinarith
      exact_mod_cast this
    have hkj : k' ≤ j := by nlinarith
    have e : c (2 * j) (k + k) = c (2 * j) (2 * ((j + k' : ℕ) : ℤ) - ((2 * j : ℕ) : ℤ)) := by
      rcases le_or_gt 0 k with h | h
      · rw [abs_of_nonneg h] at hk'; congr 1; push_cast; rw [hk']; ring
      · rw [abs_of_neg h] at hk'
        rw [← c_symm]; congr 1; push_cast; rw [hk']; ring
    rw [e, c_choose]
    exact choose_half j k' hj hk2
  exact key k.natAbs (by simp)

/-- the probability of being at `x` at a given time, as a real number -/
noncomputable def v (X : ℕ → Ω → ℤ × ℤ) (x : ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = x}).toReal

lemma prob_even_ge (hX : IsSimpleRandomWalkSteps X) (a b : ℤ) (j : ℕ) (hj : 1 ≤ j)
    (hpar : Even (a + b)) (hu : (a + b) ^ 2 ≤ j) (hv : (a - b) ^ 2 ≤ j) :
    1 / (4 * π * ((j : ℝ) + 1)) ≤ v X (a, b) (2 * j) := by
  have h := prob_pos_ge hX (2 * j) a b
  have h' : ((c (2 * j) (a + b) * c (2 * j) (a - b) : ℕ) : ℝ≥0∞).toReal ≤
      (ℙ {ω | pos (path X ω) (2 * j) = (a, b)} * 4 ^ (2 * j)).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4, pow_mul] at h'
  norm_num at h'
  have hpar2 : Even (a - b) := by
    have : a - b = (a + b) - 2 * b := by ring
    rw [this]; exact hpar.sub (even_two_mul b)
  have h1 := c_even_ge j hj (a + b) hpar hu
  have h2 := c_even_ge j hj (a - b) hpar2 hv
  have hcb0 : (0 : ℝ) ≤ (j.centralBinom : ℝ) / 2 := by positivity
  have hprod : ((j.centralBinom : ℝ) / 2) * ((j.centralBinom : ℝ) / 2) ≤
      (c (2 * j) (a + b) : ℝ) * (c (2 * j) (a - b) : ℝ) := mul_le_mul h1 h2 hcb0 (by positivity)
  have hw := cb_sq_ge j
  have hpi := Real.pi_pos
  have h16 : (0 : ℝ) < 16 ^ j := by positivity
  unfold v
  set P := (ℙ {ω | pos (path X ω) (2 * j) = (a, b)}).toReal
  have : (j.centralBinom : ℝ) ^ 2 / 16 ^ j ≤ 4 * P := by
    rw [div_le_iff₀ h16]; nlinarith
  have e : 1 / (4 * π * ((j : ℝ) + 1)) = (1 / (π * ((j : ℝ) + 1))) / 4 := by
    rw [div_div, show π * ((j : ℝ) + 1) * 4 = 4 * π * ((j : ℝ) + 1) by ring]
  rw [e]
  linarith

lemma prob_succ_ge (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (x e : ℤ × ℤ) (he : e ∈ steps) :
    v X (x - e) t / 4 ≤ v X x (t + 1) := by
  have hsub : {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}} ⊆
      {ω | pos (path X ω) (t + 1) = x} := by
    rintro ω ⟨h1, h2⟩
    simp only [Set.mem_setOf_eq] at h1 h2 ⊢
    rw [pos_succ, h1, show path X ω t = e from h2]; abel
  have hm := measure_mono (μ := ℙ) hsub
  rw [prob_pos_step hX t x e he] at hm
  have hm' := ENNReal.toReal_mono (measure_ne_top _ _) hm
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at hm'
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4] at hm'
  unfold v
  rw [div_eq_mul_inv]
  exact hm'

/-- the pair of times `2j, 2j+1` carries probability at least `1/(16 π (j+1))` at `x` -/
lemma pair_ge (hX : IsSimpleRandomWalkSteps X) (a b : ℤ) (j : ℕ)
    (hj : ((|a| + |b| + 1) ^ 2 : ℤ) ≤ j) :
    1 / (16 * π * ((j : ℝ) + 1)) ≤ v X (a, b) (2 * j) + v X (a, b) (2 * j + 1) := by
  have hpi := Real.pi_pos
  have hj1 : 1 ≤ j := by
    have : (1 : ℤ) ≤ j := le_trans (by nlinarith [abs_nonneg a, abs_nonneg b]) hj
    exact_mod_cast this
  have hv0 : ∀ y t, 0 ≤ v X y t := fun _ _ ↦ ENNReal.toReal_nonneg
  have hA : (a + b) ^ 2 ≤ (|a| + |b| + 1) ^ 2 ∧ (a - b) ^ 2 ≤ (|a| + |b| + 1) ^ 2 ∧
      (a - 1 + b) ^ 2 ≤ (|a| + |b| + 1) ^ 2 ∧ (a - 1 - b) ^ 2 ≤ (|a| + |b| + 1) ^ 2 := by
    have h1 := abs_nonneg a
    have h2 := abs_nonneg b
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← sq_abs] <;> apply pow_le_pow_left₀ (abs_nonneg _) <;>
      [have := abs_add_le a b; have := abs_sub a b; have := abs_add_le (a - 1) b;
       have := abs_sub (a - 1) b] <;> have := abs_sub a 1 <;> simp at * <;> linarith
  rcases Int.even_or_odd (a + b) with hpar | hpar
  · have := prob_even_ge hX a b j hj1 hpar (hA.1.trans hj) (hA.2.1.trans hj)
    have h4 : 1 / (16 * π * ((j : ℝ) + 1)) ≤ 1 / (4 * π * ((j : ℝ) + 1)) := by
      gcongr; norm_num
    linarith [hv0 (a, b) (2 * j + 1)]
  · have hpar' : Even (a - 1 + b) := by
      have : a - 1 + b = (a + b) - 1 := by ring
      rw [this]; exact hpar.sub_odd odd_one
    have h1 := prob_even_ge hX (a - 1) b j hj1 hpar' (hA.2.2.1.trans hj) (hA.2.2.2.trans hj)
    have h2 := prob_succ_ge hX (2 * j) (a, b) (1, 0) (by simp [steps])
    have e : ((a, b) : ℤ × ℤ) - (1, 0) = (a - 1, b) := by simp
    rw [e] at h2
    have h3 : 1 / (16 * π * ((j : ℝ) + 1)) = 1 / (4 * π * ((j : ℝ) + 1)) / 4 := by
      rw [div_div, show 4 * π * ((j : ℝ) + 1) * 4 = 16 * π * ((j : ℝ) + 1) by ring]
    linarith [hv0 (a, b) (2 * j)]

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

def FH (x : ℤ × ℤ) (t : ℕ) : Set (ℕ → ℤ × ℤ) := {y | pos y t = x ∧ ∀ s < t, pos y s ≠ x}

def Hit (x : ℤ × ℤ) (n : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∃ t ≤ n, pos y t = x}

/-- hit `x` within `n` steps before returning to the origin -/
def A (x : ℤ × ℤ) (n : ℕ) : Set (ℕ → ℤ × ℤ) :=
  {y | ∃ τ ≤ n, pos y τ = x ∧ ∀ s, 1 ≤ s → s ≤ τ → pos y s ≠ 0}

lemma det_FH (x : ℤ × ℤ) (t : ℕ) : Det t (FH x t) := fun y y' h hy ↦
  ⟨by rw [← pos_congr h le_rfl]; exact hy.1, fun s hs ↦ by rw [← pos_congr h hs.le]; exact hy.2 s hs⟩

lemma det_A (x : ℤ × ℤ) (n : ℕ) : Det n (A x n) := fun y y' h ⟨τ, hτ, h1, h2⟩ ↦
  ⟨τ, hτ, by rw [← pos_congr h hτ]; exact h1,
    fun s hs1 hs2 ↦ by rw [← pos_congr h (hs2.trans hτ)]; exact h2 s hs1 hs2⟩

lemma A_mono (x : ℤ × ℤ) {m n : ℕ} (h : m ≤ n) : A x m ⊆ A x n :=
  fun _ ⟨τ, hτ, h1, h2⟩ ↦ ⟨τ, hτ.trans h, h1, h2⟩

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

/-- expected number of visits to `x` up to time `n`, and the Green function -/
noncomputable def EN (X : ℕ → Ω → ℤ × ℤ) (x : ℤ × ℤ) (n : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range (n + 1), ℙ {ω | pos (path X ω) t = x}

lemma first_visit (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (n : ℕ) :
    EN X x n ≤ ℙ {ω | path X ω ∈ Hit x n} * EN X 0 n := by
  have hpt : ∀ t, ℙ {ω | pos (path X ω) t = x} ≤ ∑ τ ∈ Finset.range (t + 1),
      ℙ {ω | path X ω ∈ FH x τ} * ℙ {ω | pos (path X ω) (t - τ) = 0} := by
    intro t
    calc ℙ {ω | pos (path X ω) t = x}
        ≤ ℙ (⋃ τ ∈ Finset.range (t + 1),
            {ω | path X ω ∈ FH x τ ∧ sh τ (path X ω) ∈ {y | pos y (t - τ) = 0}}) := by
          refine measure_mono fun ω hω ↦ ?_
          simp only [Set.mem_setOf_eq] at hω
          classical
          have hex : ∃ s, s ≤ t ∧ pos (path X ω) s = x := ⟨t, le_rfl, hω⟩
          set τ := Nat.find hex
          have hτ := Nat.find_spec hex
          refine Set.mem_iUnion₂.mpr ⟨τ, Finset.mem_range.mpr (by omega), ⟨hτ.2, fun s hs h ↦ ?_⟩, ?_⟩
          · exact Nat.find_min hex hs ⟨by omega, h⟩
          · simp only [Set.mem_setOf_eq]
            have e := pos_shift (path X ω) τ (t - τ)
            rw [show τ + (t - τ) = t by omega, hω, hτ.2] at e
            have : x + pos (sh τ (path X ω)) (t - τ) - x = 0 := by rw [← e]; abel
            simpa using this
      _ ≤ ∑ τ ∈ Finset.range (t + 1),
            ℙ {ω | path X ω ∈ FH x τ ∧ sh τ (path X ω) ∈ {y | pos y (t - τ) = 0}} :=
          measure_biUnion_finset_le _ _
      _ = _ := Finset.sum_congr rfl fun τ _ ↦ prob_block hX (det_FH x τ) (det_pos _ 0)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (n + 1))) fun τ ↦ {ω | path X ω ∈ FH x τ} := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hab with h | h
    · exact h4 a h h1
    · exact h2 b h h3
  have hFH : ∑ τ ∈ Finset.range (n + 1), ℙ {ω | path X ω ∈ FH x τ} ≤
      ℙ {ω | path X ω ∈ Hit x n} := by
    rw [← measure_biUnion_finset hdisj fun τ _ ↦ by rw [path_eq]; exact det_meas hX (det_FH x τ) 0]
    refine measure_mono fun ω hω ↦ ?_
    obtain ⟨τ, hτ, h1, -⟩ := Set.mem_iUnion₂.mp hω
    exact ⟨τ, by have := Finset.mem_range.mp hτ; omega, h1⟩
  calc EN X x n
      ≤ ∑ t ∈ Finset.range (n + 1), ∑ τ ∈ Finset.range (t + 1),
          ℙ {ω | path X ω ∈ FH x τ} * ℙ {ω | pos (path X ω) (t - τ) = 0} :=
        Finset.sum_le_sum fun t _ ↦ hpt t
    _ = ∑ τ ∈ Finset.range (n + 1), ∑ t ∈ Finset.Ico τ (n + 1),
          ℙ {ω | path X ω ∈ FH x τ} * ℙ {ω | pos (path X ω) (t - τ) = 0} := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm]
        simp only [Finset.range_eq_Ico]
    _ ≤ ∑ τ ∈ Finset.range (n + 1), ℙ {ω | path X ω ∈ FH x τ} * EN X 0 n := by
        refine Finset.sum_le_sum fun τ hτ ↦ ?_
        rw [← Finset.mul_sum]
        gcongr
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ = (∑ τ ∈ Finset.range (n + 1), ℙ {ω | path X ω ∈ FH x τ}) * EN X 0 n := by
        rw [Finset.sum_mul]
    _ ≤ ℙ {ω | path X ω ∈ Hit x n} * EN X 0 n := by gcongr

lemma last_zero (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (hx : x ≠ 0) (n : ℕ) :
    ℙ {ω | path X ω ∈ Hit x n} ≤ EN X 0 n * ℙ {ω | path X ω ∈ A x n} := by
  calc ℙ {ω | path X ω ∈ Hit x n}
      ≤ ℙ (⋃ t ∈ Finset.range (n + 1),
          {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ A x (n - t)}) := by
        refine measure_mono fun ω hω ↦ ?_
        obtain ⟨t0, ht0, hx0⟩ := hω
        classical
        have hex : ∃ s, s ≤ n ∧ pos (path X ω) s = x := ⟨t0, ht0, hx0⟩
        set τ := Nat.find hex
        have hτ := Nat.find_spec hex
        set Z := (Finset.range (τ + 1)).filter fun s ↦ pos (path X ω) s = 0
        have hZ0 : 0 ∈ Z := Finset.mem_filter.mpr ⟨by simp, pos_zero _⟩
        set t := Z.max' ⟨0, hZ0⟩
        have htZ := Finset.mem_filter.mp (Finset.max'_mem Z ⟨0, hZ0⟩)
        have htτ : t ≤ τ := by have := Finset.mem_range.mp htZ.1; omega
        have htne : t ≠ τ := by
          intro h
          have h0 : pos (path X ω) τ = 0 := h ▸ htZ.2
          exact hx (hτ.2.symm.trans h0)
        refine Set.mem_iUnion₂.mpr ⟨t, Finset.mem_range.mpr (by omega), htZ.2,
          τ - t, by omega, ?_, fun s hs1 hs2 hs ↦ ?_⟩
        · rw [pos_sh _ htZ.2, show t + (τ - t) = τ by omega]; exact hτ.2
        · rw [pos_sh _ htZ.2] at hs
          have : t + s ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩
          have := Finset.le_max' Z (t + s) this
          omega
    _ ≤ ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ A x (n - t)} :=
        measure_biUnion_finset_le _ _
    _ = ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ A x (n - t)} :=
        Finset.sum_congr rfl fun t _ ↦ prob_block hX (det_pos t 0) (det_A x _)
    _ ≤ ∑ t ∈ Finset.range (n + 1), ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ A x n} := by
        gcongr with t ht
        exact fun ω hω ↦ A_mono x (Nat.sub_le n t) hω
    _ = EN X 0 n * ℙ {ω | path X ω ∈ A x n} := by rw [EN, Finset.sum_mul]

/-- hitting before returning: `EN_x ≤ G² P(A)` -/
lemma hit_before_return (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (hx : x ≠ 0) (n : ℕ) :
    EN X x n ≤ EN X 0 n ^ 2 * ℙ {ω | path X ω ∈ A x n} := by
  calc EN X x n ≤ ℙ {ω | path X ω ∈ Hit x n} * EN X 0 n := first_visit hX x n
    _ ≤ EN X 0 n * ℙ {ω | path X ω ∈ A x n} * EN X 0 n := by gcongr; exact last_zero hX x hx n
    _ = EN X 0 n ^ 2 * ℙ {ω | path X ω ∈ A x n} := by ring

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

def Avoid (x : ℤ × ℤ) (n : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∀ t ≤ n, pos y t ≠ x}

def RB (x : ℤ × ℤ) (t : ℕ) : Set (ℕ → ℤ × ℤ) := FR t ∩ Avoid x t

lemma det_avoid (x : ℤ × ℤ) (n : ℕ) : Det n (Avoid x n) := fun y y' h hy t ht ↦ by
  rw [← pos_congr h ht]; exact hy t ht

lemma det_RB (x : ℤ × ℤ) (t : ℕ) : Det t (RB x t) := fun y y' h hy ↦
  ⟨det_FR t y y' h hy.1, det_avoid x t y y' h hy.2⟩

lemma det_inter {m : ℕ} {A B : Set (ℕ → ℤ × ℤ)} (hA : Det m A) (hB : Det m B) : Det m (A ∩ B) :=
  fun y y' h hy ↦ ⟨hA y y' h hy.1, hB y y' h hy.2⟩

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma rb_sum_le (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (n m : ℕ) :
    ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t} ≤ 1 - ℙ {ω | path X ω ∈ A x m} := by
  have hmA : MeasurableSet {ω | path X ω ∈ A x m} := by rw [path_eq]; exact det_meas hX (det_A x m) 0
  have hmR : ∀ t, MeasurableSet {ω | path X ω ∈ RB x t} := fun t ↦ by
    rw [path_eq]; exact det_meas hX (det_RB x t) 0
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) fun t ↦ {ω | path X ω ∈ RB x t} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, -⟩ ⟨h2, -⟩
    simp only [Set.mem_setOf_eq, FR] at h1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
    · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
  have hd2 : Disjoint (⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ RB x t}) {ω | path X ω ∈ A x m} := by
    rw [Set.disjoint_left]
    intro ω hω hA
    obtain ⟨t, ht, ⟨h1, h2⟩⟩ := Set.mem_iUnion₂.mp hω
    obtain ⟨τ, -, h3, h4⟩ := hA
    rcases le_or_gt τ t with h | h
    · exact h2 τ h h3
    · exact h4 t (Finset.mem_Icc.mp ht).1 h.le h1.1
  have hsum : ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t} + ℙ {ω | path X ω ∈ A x m} ≤ 1 := by
    rw [← measure_biUnion_finset hdisj fun t _ ↦ hmR t, ← measure_union hd2 hmA]
    exact prob_le_one
  exact ENNReal.le_sub_of_add_le_right (measure_ne_top _ _) hsum

/-- many returns to the origin and still no visit to `x` -/
lemma avoid_renewal (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (m : ℕ) :
    ∀ k n, ℙ {ω | path X ω ∈ Vis n (k + 1) ∩ Avoid x n} ≤ (1 - ℙ {ω | path X ω ∈ A x m}) ^ k
  | 0, n => by rw [pow_zero]; exact prob_le_one
  | k + 1, n => by
    set ρ := 1 - ℙ {ω | path X ω ∈ A x m}
    calc ℙ {ω | path X ω ∈ Vis n (k + 1 + 1) ∩ Avoid x n}
        ≤ ℙ (⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ RB x t ∧
            sh t (path X ω) ∈ Vis (n - t) (k + 1) ∩ Avoid x (n - t)}) := by
          refine measure_mono fun ω hω ↦ ?_
          obtain ⟨hv, hav⟩ := hω
          obtain ⟨t, ht, hFR, hsh⟩ := renewal_subset n (k + 1) (by omega) hv
          have ht' := Finset.mem_Icc.mp ht
          refine Set.mem_iUnion₂.mpr ⟨t, ht, ⟨hFR, fun s hs ↦ hav s (by omega)⟩, hsh, ?_⟩
          intro s hs
          rw [pos_sh _ hFR.1]
          exact hav (t + s) (by omega)
      _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t ∧
            sh t (path X ω) ∈ Vis (n - t) (k + 1) ∩ Avoid x (n - t)} :=
          measure_biUnion_finset_le _ _
      _ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t} *
            ℙ {ω | path X ω ∈ Vis (n - t) (k + 1) ∩ Avoid x (n - t)} :=
          Finset.sum_congr rfl fun t _ ↦
            prob_block hX (det_RB x t) (det_inter (det_vis _ _) (det_avoid x _))
      _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t} * ρ ^ k := by
          gcongr with t ht
          exact avoid_renewal hX x m k (n - t)
      _ = (∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t}) * ρ ^ k := by rw [Finset.sum_mul]
      _ ≤ ρ * ρ ^ k := by gcongr; exact rb_sum_le hX x n m
      _ = ρ ^ (k + 1) := (pow_succ' _ _).symm

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real Erdos1164

lemma covers_bdd {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) :
    BddAbove {r : ℕ | Covers X n ω (closedDisc r)} := by
  refine ⟨n, fun r hr ↦ ?_⟩
  simp only [Set.mem_setOf_eq] at hr
  classical
  have hmem : ∀ j : ℕ, j ≤ r → ((j : ℤ), (0 : ℤ)) ∈ closedDisc r := by
    intro j hj
    simp only [closedDisc, Set.mem_setOf_eq]
    have : (j : ℤ) ≤ r := by exact_mod_cast hj
    nlinarith
  have hk : ∀ j : ℕ, ∃ k, j ≤ r → k ≤ n ∧ position X k ω = ((j : ℤ), (0 : ℤ)) := by
    intro j
    by_cases hj : j ≤ r
    · obtain ⟨k, hk, hpos⟩ := hr _ (hmem j hj)
      exact ⟨k, fun _ ↦ ⟨hk, hpos⟩⟩
    · exact ⟨0, fun h ↦ absurd h hj⟩
  choose f hf using hk
  have hcard : (Finset.range (r + 1)).card ≤ (Finset.range (n + 1)).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro j hj
      have hj' : j ≤ r := by have := Finset.mem_range.mp hj; omega
      exact Finset.mem_range.mpr (by have := (hf j hj').1; omega)
    · intro a ha b hb hab
      have ha' : a ≤ r := by have := Finset.mem_range.mp ha; omega
      have hb' : b ≤ r := by have := Finset.mem_range.mp hb; omega
      have h1 := (hf a ha').2
      have h2 := (hf b hb').2
      have hab' : f a = f b := hab
      rw [hab', h2] at h1
      have := congrArg Prod.fst h1
      simp only at this
      exact_mod_cast this.symm
  simp only [Finset.card_range] at hcard
  omega

lemma le_coveringRadius {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) (r : ℕ)
    (h : Covers X n ω (closedDisc r)) : r ≤ coveringRadius X n ω :=
  le_csSup (covers_bdd X n ω) h

/-- the box containing the closed disc -/
def box (r : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(r : ℤ)) r ×ˢ Finset.Icc (-(r : ℤ)) r

lemma disc_sub_box (r : ℕ) (x : ℤ × ℤ) (hx : x ∈ closedDisc r) : x ∈ box r := by
  simp only [closedDisc, Set.mem_setOf_eq] at hx
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  have hr : (0 : ℤ) ≤ r := by positivity
  have h1 : x.1 ^ 2 ≤ (r : ℤ) ^ 2 := by nlinarith [sq_nonneg x.2]
  have h2 : x.2 ^ 2 ≤ (r : ℤ) ^ 2 := by nlinarith [sq_nonneg x.1]
  have a1 := abs_le_of_sq_le_sq' h1 hr
  have a2 := abs_le_of_sq_le_sq' h2 hr
  exact ⟨a1, a2⟩

lemma card_box (r : ℕ) : ((box r).card : ℝ) = (2 * r + 1) ^ 2 := by
  simp only [box, Finset.card_product, Int.card_Icc]
  have : ((r : ℤ) + 1 - -(r : ℤ)).toNat = 2 * r + 1 := by omega
  rw [this]; push_cast; ring

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma not_cover_le (n r K : ℕ) :
    ℙ {ω | ¬ Covers X n ω (closedDisc r)} ≤ ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} +
      ∑ x ∈ (box r).erase 0, ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n} := by
  calc ℙ {ω | ¬ Covers X n ω (closedDisc r)}
      ≤ ℙ ({ω | path X ω ∈ (Vis n (K + 1))ᶜ} ∪
          ⋃ x ∈ (box r).erase 0, {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n}) := by
        refine measure_mono fun ω hω ↦ ?_
        simp only [Set.mem_setOf_eq, Covers, not_forall] at hω
        obtain ⟨x, hx, hnot⟩ := hω
        by_cases hv : path X ω ∈ Vis n (K + 1)
        · right
          have hx0 : x ≠ 0 := by
            rintro rfl
            exact hnot ⟨0, Nat.zero_le _, by simp [position]⟩
          refine Set.mem_iUnion₂.mpr ⟨x, Finset.mem_erase.mpr ⟨hx0, disc_sub_box r x hx⟩, hv, ?_⟩
          intro t ht h
          exact hnot ⟨t, ht, h⟩
        · left; exact hv
    _ ≤ ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} +
          ℙ (⋃ x ∈ (box r).erase 0, {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n}) :=
        measure_union_le _ _
    _ ≤ _ := by gcongr; exact measure_biUnion_finset_le _ _

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

lemma sum_pairs2 (f : ℕ → ℝ) (M : ℕ) :
    ∑ t ∈ Finset.range (2 * M), f t = ∑ j ∈ Finset.range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

lemma harm_Ico (J M : ℕ) (h : J ≤ M + 1) :
    Real.log (M + 2) - (1 + Real.log J) ≤ ∑ j ∈ Finset.Ico J (M + 1), 1 / ((j : ℝ) + 1) := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) h
  have hH : ∀ n : ℕ, (harmonic n : ℝ) = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
    intro n
    rw [harmonic, Rat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast; rw [one_div]
  have h1 := log_add_one_le_harmonic (M + 1)
  have h2 := harmonic_le_one_add_log J
  rw [hH] at h1 h2
  have e : Real.log (((M + 1 + 1 : ℕ) : ℝ)) = Real.log ((M : ℝ) + 2) := by push_cast; ring_nf
  rw [e] at h1
  linarith

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma EN_toReal (X : ℕ → Ω → ℤ × ℤ) (x : ℤ × ℤ) (n : ℕ) :
    (EN X x n).toReal = ∑ t ∈ Finset.range (n + 1), v X x t :=
  ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _

/-- the probability of reaching `x` before returning is at least `1/(300 log r)` -/
lemma h_lower (hX : IsSimpleRandomWalkSteps X) (r : ℕ) (hr : 4 ≤ Real.log r) (x : ℤ × ℤ)
    (hx : x ∈ box r) (hx0 : x ≠ 0) :
    1 / (300 * Real.log r) ≤ (ℙ {ω | path X ω ∈ A x (2 * r ^ 4 + 1)}).toReal := by
  set L := Real.log r with hL
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hr0 : (0 : ℝ) < r := by
    by_contra h
    have : (r : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg r)
    rw [hL, this, Real.log_zero] at hr; linarith
  have hr1 : (1 : ℝ) ≤ r := by
    have : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hr0)
    exact_mod_cast this
  obtain ⟨a, b⟩ := x
  simp only [box, Finset.mem_product, Finset.mem_Icc] at hx
  set M := r ^ 4 with hM
  set J := (2 * r + 1) ^ 2 with hJ
  -- `r ≥ e^4 > 50`, so `J ≤ M`
  have hr54 : (50 : ℝ) ≤ r := by
    have h1 : Real.exp 4 ≤ r := by rw [← Real.exp_log hr0]; exact Real.exp_le_exp.mpr hr
    have h2 : (50 : ℝ) ≤ Real.exp 4 := by
      have h3 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have := pow_le_pow_left₀ (by norm_num) h27 4
      norm_num at this
      linarith
    linarith
  have hJM : J ≤ M + 1 := by
    have h1 : 2 * (r : ℝ) + 1 ≤ (r : ℝ) ^ 2 := by nlinarith
    have h2 : (2 * (r : ℝ) + 1) ^ 2 ≤ ((r : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have : ((J : ℕ) : ℝ) ≤ M := by
      rw [hJ, hM]; push_cast
      calc (2 * (r : ℝ) + 1) ^ 2 ≤ ((r : ℝ) ^ 2) ^ 2 := h2
        _ = (r : ℝ) ^ 4 := by ring
    have : J ≤ M := by exact_mod_cast this
    omega
  -- lower bound on the expected visits to x
  have hEN : 3 * L / (64 * π) ≤ (EN X (a, b) (2 * r ^ 4 + 1)).toReal := by
    rw [EN_toReal, show 2 * r ^ 4 + 1 + 1 = 2 * (M + 1) by ring, sum_pairs2]
    have hv0 : ∀ y t, 0 ≤ v X y t := fun _ _ ↦ ENNReal.toReal_nonneg
    calc 3 * L / (64 * π) ≤ (Real.log (M + 2) - (1 + Real.log J)) / (16 * π) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h4 : 4 * L ≤ Real.log ((M : ℝ) + 2) := by
            have e : Real.log ((r : ℝ) ^ 4) = 4 * L := by rw [hL, Real.log_pow]; norm_num
            rw [← e]
            exact Real.log_le_log (by positivity) (by rw [hM]; push_cast; linarith)
          have h5 : Real.log (J : ℝ) ≤ 4 + 2 * L := by
            have e : Real.log (J : ℝ) = 2 * Real.log (2 * r + 1) := by
              rw [hJ]; push_cast; rw [Real.log_pow]; push_cast; ring
            have h6 : Real.log (2 * (r : ℝ) + 1) ≤ Real.log 3 + L := by
              rw [hL, ← Real.log_mul (by norm_num) hr0.ne']
              exact Real.log_le_log (by positivity) (by linarith)
            have h7 : Real.log 3 ≤ 2 := by
              have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
            rw [e]; linarith
          nlinarith
      _ ≤ ∑ j ∈ Finset.Ico J (M + 1), 1 / (16 * π * ((j : ℝ) + 1)) := by
          rw [show (∑ j ∈ Finset.Ico J (M + 1), 1 / (16 * π * ((j : ℝ) + 1))) =
              (∑ j ∈ Finset.Ico J (M + 1), 1 / ((j : ℝ) + 1)) / (16 * π) by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [div_div, mul_comm]]
          gcongr
          exact harm_Ico J M hJM
      _ ≤ ∑ j ∈ Finset.Ico J (M + 1), (v X (a, b) (2 * j) + v X (a, b) (2 * j + 1)) := by
          refine Finset.sum_le_sum fun j hj ↦ pair_ge hX a b j ?_
          have hj := (Finset.mem_Ico.mp hj).1
          have h1 : |a| ≤ r := abs_le.mpr hx.1
          have h2 : |b| ≤ r := abs_le.mpr hx.2
          have : ((J : ℕ) : ℤ) ≤ j := by exact_mod_cast hj
          rw [hJ] at this; push_cast at this
          nlinarith [abs_nonneg a, abs_nonneg b]
      _ ≤ ∑ j ∈ Finset.range (M + 1), (v X (a, b) (2 * j) + v X (a, b) (2 * j + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun j hj ↦ Finset.mem_range.mpr
            (Finset.mem_Ico.mp hj).2) fun j _ _ ↦ add_nonneg (hv0 _ _) (hv0 _ _)
  -- upper bound on the Green function
  have hG : (EN X 0 (2 * r ^ 4 + 1)).toReal ≤ 6 * L / π := by
    rw [EN_toReal]
    have := green_le (u X) (u_nonneg X) (u_le_one X 0) (u_pair hX) (2 * r ^ 4 + 1)
    have hlog : Real.log (((2 * r ^ 4 + 1 : ℕ) : ℝ)) ≤ 2 + 4 * L := by
      have h1 : Real.log (((2 * r ^ 4 + 1 : ℕ) : ℝ)) ≤ Real.log (3 * (r : ℝ) ^ 4) := by
        apply Real.log_le_log (by positivity)
        have : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hr1
        push_cast; linarith
      have e : Real.log ((r : ℝ) ^ 4) = 4 * L := by rw [hL, Real.log_pow]; norm_num
      rw [Real.log_mul (by norm_num) (by positivity), e] at h1
      have h7 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
      linarith
    have e : ∑ t ∈ Finset.range (2 * r ^ 4 + 1 + 1), v X 0 t =
        ∑ t ∈ Finset.range (2 * r ^ 4 + 1 + 1), u X t := rfl
    rw [e]
    refine this.trans ?_
    rw [le_div_iff₀ hpi, add_mul, div_mul_cancel₀ _ hpi.ne', one_mul]
    have := Real.pi_le_four
    linarith

  have hkey := hit_before_return hX (a, b) hx0 (2 * r ^ 4 + 1)
  have hkey' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top
    (ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _)) (measure_ne_top _ _)) hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at hkey'
  set P := (ℙ {ω | path X ω ∈ A (a, b) (2 * r ^ 4 + 1)}).toReal
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  have hG0 : 0 ≤ (EN X 0 (2 * r ^ 4 + 1)).toReal := ENNReal.toReal_nonneg
  have hL0 : 0 < L := by linarith
  have hEN' : 3 * L ≤ 64 * π * (EN X (a, b) (2 * r ^ 4 + 1)).toReal := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * π)).mp hEN
    linarith
  have hG' : π * (EN X 0 (2 * r ^ 4 + 1)).toReal ≤ 6 * L := by
    have := (le_div_iff₀ hpi).mp hG
    linarith
  set G := (EN X 0 (2 * r ^ 4 + 1)).toReal
  have h1 : 3 * L ≤ 64 * π * (G ^ 2 * P) := hEN'.trans (by gcongr; exact hkey')
  have h2 : (π * G) ^ 2 ≤ (6 * L) ^ 2 := pow_le_pow_left₀ (by positivity) hG' 2
  have h3 : (L * π) * (3 * π) ≤ (L * π) * (2304 * L * P) := by
    have e1 : (L * π) * (3 * π) = π ^ 2 * (3 * L) := by ring
    have e2 : (L * π) * (2304 * L * P) = 64 * π * P * (6 * L) ^ 2 := by ring
    rw [e1, e2]
    calc π ^ 2 * (3 * L) ≤ π ^ 2 * (64 * π * (G ^ 2 * P)) := by gcongr
      _ = 64 * π * P * (π * G) ^ 2 := by ring
      _ ≤ 64 * π * P * (6 * L) ^ 2 := by gcongr
  have h4 := le_of_mul_le_mul_left h3 (by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real Erdos1164 Filter

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma noRet_compl (hX : IsSimpleRandomWalkSteps X) (s : ℕ) :
    ℙ {ω | path X ω ∈ NoRet s}ᶜ = ENNReal.ofReal (1 - q X s) := by
  have hmN : MeasurableSet {ω | path X ω ∈ NoRet s} := by
    rw [path_eq]; exact det_meas hX (det_noRet s) 0
  rw [prob_compl_eq_one_sub hmN]
  unfold q
  rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- few returns to the origin is unlikely -/
lemma few_returns (hX : IsSimpleRandomWalkSteps X) (n K M : ℕ) (hKM : K * (2 * M) ≤ n) :
    ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} ≤ ENNReal.ofReal (K * q X (2 * M)) := by
  have hmV : MeasurableSet {ω | path X ω ∈ Vis n (K + 1)} := by
    rw [path_eq]; exact det_meas hX (det_vis _ _) 0
  have h1 : ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} = 1 - ℙ {ω | path X ω ∈ Vis n (K + 1)} :=
    prob_compl_eq_one_sub hmV
  have h2 : ENNReal.ofReal ((1 - q X (2 * M)) ^ K) ≤ ℙ {ω | path X ω ∈ Vis n (K + 1)} := by
    have hq1 := q_le_one (X := X) (2 * M)
    rw [ENNReal.ofReal_pow (by linarith), ← noRet_compl hX]
    refine (renewal_lower hX (2 * M) K).trans (measure_mono fun ω hω ↦ ?_)
    simp only [Set.mem_setOf_eq, Vis] at hω ⊢
    exact hω.trans (visits_mono _ (by rw [mul_comm] at hKM; linarith))
  rw [h1]
  have hq0 := q_nonneg (X := X) (2 * M)
  have hq1 := q_le_one (X := X) (2 * M)
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -q X (2 * M) by linarith) K
  calc 1 - ℙ {ω | path X ω ∈ Vis n (K + 1)} ≤ 1 - ENNReal.ofReal ((1 - q X (2 * M)) ^ K) :=
        tsub_le_tsub_left h2 _
    _ = ENNReal.ofReal (1 - (1 - q X (2 * M)) ^ K) := by
        rw [ENNReal.ofReal_sub _ (pow_nonneg (by linarith) K), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (K * q X (2 * M)) := by
        apply ENNReal.ofReal_le_ofReal
        have e : (1 + -q X (2 * M)) = 1 - q X (2 * M) := by ring
        rw [e] at hb
        linarith

/-- a point of the box is missed despite many returns -/
lemma miss_point (hX : IsSimpleRandomWalkSteps X) (n K r : ℕ) (hr : 4 ≤ Real.log r)
    (x : ℤ × ℤ) (hx : x ∈ box r) (hx0 : x ≠ 0) :
    ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n} ≤
      ENNReal.ofReal (Real.exp (-(K / (300 * Real.log r)))) := by
  have hA := h_lower hX r hr x hx hx0
  refine (avoid_renewal hX x (2 * r ^ 4 + 1) K n).trans ?_
  set P := ℙ {ω | path X ω ∈ A x (2 * r ^ 4 + 1)}
  have hP1 : P.toReal ≤ 1 := by
    have : P ≤ 1 := prob_le_one
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (this.trans_eq ENNReal.ofReal_one.symm)
  have e : 1 - P = ENNReal.ofReal (1 - P.toReal) := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [e, ← ENNReal.ofReal_pow (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  calc (1 - P.toReal) ^ K ≤ Real.exp (-P.toReal) ^ K :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) K
    _ = Real.exp (-(K * P.toReal)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-(K / (300 * Real.log r))) := by
        apply Real.exp_le_exp.mpr
        have : (K : ℝ) / (300 * Real.log r) ≤ K * P.toReal := by
          rw [div_eq_mul_one_div]; gcongr
        linarith

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real Erdos1164 Filter

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

/-- the lower half for one `n`, with explicit conditions -/
lemma lower_fixed (hX : IsSimpleRandomWalkSteps X) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ)
    (hn8 : 64 ≤ n) (hℓ1 : 16 * π / ε ≤ Real.log n)
    (hℓ2 : 4 ≤ ε / (16 * π) / 3000 * √(Real.log n))
    (hℓ3 : Real.log (100 / ε) ≤ 4 * √(Real.log n)) :
    1 - ε ≤ (ℙ {ω | ε / (16 * π) / 3000 * √(Real.log n) ≤
      Real.log (coveringRadius X n ω)}).toReal := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  set δ := ε / (16 * π) with hδ
  set c := δ / 3000 with hc
  set ℓ := Real.log n with hℓ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 16 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hn0 : (0 : ℝ) < n := by
    have : (64 : ℝ) ≤ n := by exact_mod_cast hn8
    linarith
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hsq8 : (8 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hn0.le]; norm_num; exact_mod_cast hn8
  have hℓ0 : 0 < ℓ := by
    have : 0 < 16 * π / ε := by positivity
    linarith
  set K := ⌈δ * ℓ⌉₊ with hK
  set M := ⌊√(n : ℝ)⌋₊ with hM
  set E := Real.exp (c * √ℓ) with hE
  set r := ⌈E⌉₊ with hr
  -- the radius
  have hE4 : Real.exp 4 ≤ E := Real.exp_le_exp.mpr hℓ2
  have hE1 : 1 ≤ E := le_trans (Real.one_le_exp (by norm_num)) hE4
  have hrE : E ≤ r := Nat.le_ceil E
  have hrE2 : (r : ℝ) ≤ 2 * E := by
    have := Nat.ceil_lt_add_one (show 0 ≤ E by linarith); linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr1 : c * √ℓ ≤ Real.log r := by
    rw [← Real.log_exp (c * √ℓ)]; exact Real.log_le_log (Real.exp_pos _) hrE
  have hlogr2 : Real.log r ≤ 2 * (c * √ℓ) := by
    have h1 : Real.log r ≤ Real.log (2 * E) := Real.log_le_log hr0 hrE2
    rw [Real.log_mul (by norm_num) (by positivity), hE, Real.log_exp] at h1
    have : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hlogr4 : 4 ≤ Real.log r := hℓ2.trans hlogr1
  -- the returns
  have hKℓ : δ * ℓ ≤ K := Nat.le_ceil _
  have hKℓ2 : (K : ℝ) ≤ δ * ℓ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hMle : (M : ℝ) ≤ √(n : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hMge : √(n : ℝ) < M + 1 := Nat.lt_floor_add_one _
  have hlogsq : ℓ ≤ 2 * √(n : ℝ) := by
    have h1 : Real.log √(n : ℝ) = ℓ / 2 := Real.log_sqrt hn0.le
    have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn0)
    linarith
  have h2K : 2 * (K : ℝ) ≤ √(n : ℝ) := by nlinarith
  have hKM : K * (2 * M) ≤ n := by
    have : ((K * (2 * M) : ℕ) : ℝ) ≤ n := by
      push_cast
      calc (K : ℝ) * (2 * M) = (2 * K) * M := by ring
        _ ≤ √(n : ℝ) * √(n : ℝ) := by gcongr
        _ = n := by rw [← sq, hsq]
    exact_mod_cast this
  have hq : q X (2 * M) * ℓ ≤ 2 * π := by
    have h1 := q_le hX M
    have h2 : ℓ / 2 ≤ Real.log ((M : ℝ) + 1) := by
      rw [← Real.log_sqrt hn0.le]; exact Real.log_le_log (Real.sqrt_pos.mpr hn0) hMge.le
    have := mul_le_mul_of_nonneg_left h2 (q_nonneg (X := X) (2 * M))
    linarith
  have hKq : (K : ℝ) * q X (2 * M) ≤ ε / 4 := by
    have hq0 := q_nonneg (X := X) (2 * M)
    have h1 : q X (2 * M) ≤ ε / 8 := by
      have : q X (2 * M) * ℓ ≤ ε / 8 * ℓ := by
        have : 16 * π ≤ ε * ℓ := by rw [div_le_iff₀ hε] at hℓ1; linarith
        nlinarith
      exact le_of_mul_le_mul_right this hℓ0
    have h2 : δ * ℓ * q X (2 * M) ≤ ε / 8 := by
      have : δ * ℓ * q X (2 * M) = δ * (q X (2 * M) * ℓ) := by ring
      rw [this]
      calc δ * (q X (2 * M) * ℓ) ≤ δ * (2 * π) := by gcongr
        _ = ε / 8 := by
          rw [hδ, show ε / (16 * π) * (2 * π) = ε * (π / π) / 8 by ring, div_self hpi.ne', mul_one]
    calc (K : ℝ) * q X (2 * M) ≤ (δ * ℓ + 1) * q X (2 * M) := by gcongr
      _ = δ * ℓ * q X (2 * M) + q X (2 * M) := by ring
      _ ≤ ε / 4 := by linarith
  have hfew := few_returns hX n K M hKM
  -- the misses
  have hmiss : ∑ x ∈ (box r).erase 0, ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n} ≤
      ENNReal.ofReal (ε / 4) := by
    have hterm : ∀ x ∈ (box r).erase 0, ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n} ≤
        ENNReal.ofReal (Real.exp (-(K / (300 * Real.log r)))) := fun x hx ↦
      miss_point hX n K r hlogr4 x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((box r).erase 0).card : ℝ≥0∞) ≤ ENNReal.ofReal ((2 * r + 1) ^ 2) := by
      rw [← card_box, ENNReal.ofReal_natCast]
      exact_mod_cast Finset.card_erase_le
    calc (((box r).erase 0).card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(K / (300 * Real.log r))))
        ≤ ENNReal.ofReal ((2 * r + 1) ^ 2) *
            ENNReal.ofReal (Real.exp (-(K / (300 * Real.log r)))) := by gcongr
      _ = ENNReal.ofReal ((2 * r + 1) ^ 2 * Real.exp (-(K / (300 * Real.log r)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (ε / 4) := by
          apply ENNReal.ofReal_le_ofReal
          have hsqℓ : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
          have hℓsq : √ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ0.le
          have hexp : (K : ℝ) / (300 * Real.log r) ≥ 5 * √ℓ := by
            rw [ge_iff_le, le_div_iff₀ (by positivity)]
            calc 5 * √ℓ * (300 * Real.log r) ≤ 5 * √ℓ * (300 * (2 * (c * √ℓ))) := by gcongr
              _ = δ * √ℓ ^ 2 := by rw [hc]; ring
              _ = δ * ℓ := by rw [hℓsq]
              _ ≤ K := hKℓ
          have h1 : (2 * (r : ℝ) + 1) ^ 2 ≤ 25 * E ^ 2 := by nlinarith
          have h2 : E ^ 2 = Real.exp (2 * (c * √ℓ)) := by rw [hE, ← Real.exp_nat_mul]; norm_num
          have hc1 : c ≤ 1 / 2 := by rw [hc]; linarith
          have h3 : Real.exp (2 * (c * √ℓ)) * Real.exp (-(K / (300 * Real.log r))) ≤
              Real.exp (-(4 * √ℓ)) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
            have : c * √ℓ ≤ 1 / 2 * √ℓ := by gcongr
            linarith
          have h4 : 25 * Real.exp (-(4 * √ℓ)) ≤ ε / 4 := by
            have : Real.exp (Real.log (100 / ε)) ≤ Real.exp (4 * √ℓ) := Real.exp_le_exp.mpr hℓ3
            rw [Real.exp_log (by positivity)] at this
            rw [Real.exp_neg]
            have hpos : 0 < Real.exp (4 * √ℓ) := Real.exp_pos _
            rw [← div_eq_mul_inv, div_le_iff₀ hpos]
            have h6 : 100 / ε * ε = 100 := div_mul_cancel₀ _ hε.ne'
            have h5 : ε / 4 * (100 / ε) = 25 := by
              rw [show ε / 4 * (100 / ε) = (100 / ε * ε) / 4 by ring, h6]; norm_num
            calc (25 : ℝ) = ε / 4 * (100 / ε) := h5.symm
              _ ≤ ε / 4 * Real.exp (4 * √ℓ) := by gcongr
          calc (2 * (r : ℝ) + 1) ^ 2 * Real.exp (-(K / (300 * Real.log r)))
              ≤ 25 * E ^ 2 * Real.exp (-(K / (300 * Real.log r))) := by gcongr
            _ = 25 * (Real.exp (2 * (c * √ℓ)) * Real.exp (-(K / (300 * Real.log r)))) := by
                rw [h2]; ring
            _ ≤ 25 * Real.exp (-(4 * √ℓ)) := by gcongr
            _ ≤ ε / 4 := h4
  -- combine
  have hnc := not_cover_le (X := X) n r K
  have hbad : ℙ {ω | ¬ Covers X n ω (closedDisc r)} ≤ ENNReal.ofReal ε := by
    refine hnc.trans ?_
    calc ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} +
          ∑ x ∈ (box r).erase 0, ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n}
        ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
          gcongr
          exact hfew.trans (ENNReal.ofReal_le_ofReal hKq)
      _ = ENNReal.ofReal (ε / 4 + ε / 4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
  set S := {ω | c * √ℓ ≤ Real.log (coveringRadius X n ω)}
  have hSc : Sᶜ ⊆ {ω | ¬ Covers X n ω (closedDisc r)} := by
    intro ω hω hcov
    apply hω
    have h1 := le_coveringRadius X n ω r hcov
    have h2 : (r : ℝ) ≤ coveringRadius X n ω := by exact_mod_cast h1
    exact hlogr1.trans (Real.log_le_log hr0 h2)
  have h1 : (1 : ℝ≥0∞) ≤ ℙ S + ENNReal.ofReal ε := by
    calc (1 : ℝ≥0∞) = ℙ (S ∪ Sᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ ℙ S + ℙ Sᶜ := measure_union_le _ _
      _ ≤ ℙ S + ENNReal.ofReal ε := by gcongr; exact (measure_mono hSc).trans hbad
  have h2 : ENNReal.ofReal (1 - ε) ≤ ℙ S := by
    rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
    exact tsub_le_iff_right.mpr h1
  have h3 := ENNReal.toReal_mono (measure_ne_top _ _) h2
  rwa [ENNReal.toReal_ofReal (by linarith)] at h3

theorem lower : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X → ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop, 1 - ε ≤
        (ℙ {ω | c * √(Real.log n) ≤ Real.log (coveringRadius X n ω)}).toReal := by
  intro Ω _ _ X hX ε hε
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hpi := Real.pi_pos
  refine ⟨ε' / (16 * π) / 3000, by positivity, ?_⟩
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  set T := max (16 * π / ε') (max ((4 / (ε' / (16 * π) / 3000)) ^ 2) ((Real.log (100 / ε') / 4) ^ 2))
  filter_upwards [eventually_ge_atTop 64, hlog.eventually_ge_atTop T] with n hn hT
  have hT1 : 16 * π / ε' ≤ Real.log n := le_trans (le_max_left _ _) hT
  have hT2 : (4 / (ε' / (16 * π) / 3000)) ^ 2 ≤ Real.log n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT3 : (Real.log (100 / ε') / 4) ^ 2 ≤ Real.log n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hc0 : 0 < ε' / (16 * π) / 3000 := by positivity
  have h2 : 4 ≤ ε' / (16 * π) / 3000 * √(Real.log n) := by
    have : 4 / (ε' / (16 * π) / 3000) ≤ √(Real.log n) := Real.le_sqrt_of_sq_le hT2
    rw [div_le_iff₀ hc0] at this; linarith
  have h3 : Real.log (100 / ε') ≤ 4 * √(Real.log n) := by
    have : Real.log (100 / ε') / 4 ≤ √(Real.log n) := Real.le_sqrt_of_sq_le hT3
    linarith
  have := lower_fixed hX ε' hε'0 hε'1 n hn hT1 h2 h3
  have hmin : 1 - ε ≤ 1 - ε' := by linarith [min_le_left ε 1]
  exact hmin.trans this

end OMA.C64

theorem OMA.solution : OMA.R_Erdos1164_erdos_1164_R1.H1 :=
  fun hX ε hε ↦ OMA.C64.lower hX ε hε
