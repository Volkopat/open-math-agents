import OMAReductions.R_oeis_a191625_R1

open PowerSeries OMA.S_oeis_a191625

namespace A191625H2

def prudent {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  ∀ (i : Fin n) (j : ℕ), j ≤ i.val → ∀ k : ℕ, 0 < k →
    pos w j ≠ pos w i.val + k • dir (w i)

def prefixEdge {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  ∀ i ≤ n, (∀ j ≤ i, (pos w j).1 ≤ (pos w i).1) ∨
            (∀ j ≤ i, (pos w j).2 ≤ (pos w i).2)

def prefValid {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  prudent w ∧ prefixEdge w

def onTop {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  ∀ j ≤ n, (pos w j).2 ≤ (pos w n).2

def onRight {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  ∀ j ≤ n, (pos w j).1 ≤ (pos w n).1

def maxX {n : ℕ} (w : Fin n → Fin 4) : ℤ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
    (fun j => (pos w j).1)

def maxY {n : ℕ} (w : Fin n → Fin 4) : ℤ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
    (fun j => (pos w j).2)

def topDist {n : ℕ} (w : Fin n → Fin 4) (k : ℕ) : Prop :=
  prefValid w ∧ onTop w ∧ maxX w = (pos w n).1 + (k : ℤ)

lemma dir_zero : dir 0 = (1, 0) := rfl
lemma dir_one : dir 1 = (0, 1) := rfl
lemma dir_two : dir 2 = (-1, 0) := rfl
lemma dir_three : dir 3 = (0, -1) := rfl

lemma smul_dir_zero (k : ℕ) : k • dir 0 = ((k : ℤ), 0) := by
  rw [dir_zero]; ext <;> simp

lemma smul_dir_one (k : ℕ) : k • dir 1 = (0, (k : ℤ)) := by
  rw [dir_one]; ext <;> simp

lemma smul_dir_two (k : ℕ) : k • dir 2 = (-(k : ℤ), 0) := by
  rw [dir_two]; ext <;> simp

lemma dir_cases (d : Fin 4) : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by
  fin_cases d <;> simp

lemma dir_step_abs (d : Fin 4) : |(dir d).1| ≤ 1 ∧ |(dir d).2| ≤ 1 := by
  fin_cases d <;> simp [dir]

lemma pos_succ {n : ℕ} (w : Fin n → Fin 4) {i : ℕ} (hi : i < n) :
    pos w (i + 1) = pos w i + dir (w ⟨i, hi⟩) := by
  simp [pos, hi]

lemma le_maxX {n : ℕ} (w : Fin n → Fin 4) {j : ℕ} (hj : j ≤ n) :
    (pos w j).1 ≤ maxX w :=
  Finset.le_sup' (fun m => (pos w m).1) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

lemma exists_eq_maxX {n : ℕ} (w : Fin n → Fin 4) :
    ∃ j ≤ n, (pos w j).1 = maxX w := by
  obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_sup'
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩ (fun m => (pos w m).1)
  exact ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), h.symm⟩

lemma le_maxY {n : ℕ} (w : Fin n → Fin 4) {j : ℕ} (hj : j ≤ n) :
    (pos w j).2 ≤ maxY w :=
  Finset.le_sup' (fun m => (pos w m).2) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

lemma exists_eq_maxY {n : ℕ} (w : Fin n → Fin 4) :
    ∃ j ≤ n, (pos w j).2 = maxY w := by
  obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_sup'
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩ (fun m => (pos w m).2)
  exact ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), h.symm⟩

lemma onRight_iff_maxX {n : ℕ} (w : Fin n → Fin 4) :
    onRight w ↔ maxX w = (pos w n).1 := by
  constructor
  · intro h
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j hj => h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    · exact le_maxX w le_rfl
  · intro h j hj
    rw [← h]
    exact le_maxX w hj

lemma onTop_iff_maxY {n : ℕ} (w : Fin n → Fin 4) :
    onTop w ↔ maxY w = (pos w n).2 := by
  constructor
  · intro h
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j hj => h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    · exact le_maxY w le_rfl
  · intro h j hj
    rw [← h]
    exact le_maxY w hj

lemma valid_iff_topDist_zero {n : ℕ} (w : Fin n → Fin 4) :
    valid w ↔ topDist w 0 := by
  rw [valid, topDist, prefValid, prudent, prefixEdge, onTop]
  simp only [Nat.cast_zero, add_zero]
  rw [← onRight_iff_maxX]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun j hj => (h3 j hj).2, fun j hj => (h3 j hj).1⟩
  · rintro ⟨⟨h1, h2⟩, htop, hright⟩
    exact ⟨h1, h2, fun j hj => ⟨hright j hj, htop j hj⟩⟩

def snoc {n : ℕ} (w : Fin n → Fin 4) (d : Fin 4) : Fin (n + 1) → Fin 4 :=
  fun i => if h : i.val < n then w ⟨i.val, h⟩ else d

def init {n : ℕ} (w : Fin (n + 1) → Fin 4) : Fin n → Fin 4 :=
  fun i => w i.castSucc

@[simp] lemma init_snoc {n : ℕ} (w : Fin n → Fin 4) (d : Fin 4) :
    init (snoc w d) = w := by
  ext i
  simp [init, snoc, i.isLt]

@[simp] lemma snoc_last {n : ℕ} (w : Fin n → Fin 4) (d : Fin 4) :
    snoc w d ⟨n, Nat.lt_succ_self n⟩ = d := by
  simp [snoc]

lemma snoc_init_last {n : ℕ} (w : Fin (n + 1) → Fin 4) :
    snoc (init w) (w ⟨n, Nat.lt_succ_self n⟩) = w := by
  ext ⟨i, hi⟩
  by_cases h : i < n
  · simp [snoc, init, h]
  · have : i = n := by omega
    subst this
    simp [snoc]

lemma pos_snoc_le {n : ℕ} (w : Fin n → Fin 4) (d : Fin 4) :
    ∀ i ≤ n, pos (snoc w d) i = pos w i := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i < n := Nat.lt_of_succ_le hi
    rw [pos_succ _ (Nat.lt_succ_of_lt hi'), pos_succ _ hi', ih (Nat.le_of_lt hi')]
    simp [snoc, hi']

lemma pos_snoc_succ {n : ℕ} (w : Fin n → Fin 4) (d : Fin 4) :
    pos (snoc w d) (n + 1) = pos w n + dir d := by
  rw [pos_succ _ (Nat.lt_succ_self n), pos_snoc_le w d n le_rfl, snoc_last]

lemma pos_init_le {n : ℕ} (w : Fin (n + 1) → Fin 4) {i : ℕ} (hi : i ≤ n) :
    pos (init w) i = pos w i := by
  conv_rhs => rw [← snoc_init_last w]
  exact (pos_snoc_le (init w) (w ⟨n, Nat.lt_succ_self n⟩) i hi).symm

lemma prefValid_init {n : ℕ} {w : Fin (n + 1) → Fin 4} (hw : prefValid w) :
    prefValid (init w) := by
  refine ⟨?_, ?_⟩
  · intro i j hj k hk
    have h := hw.1 i.castSucc j hj k hk
    rw [pos_init_le w (by omega), pos_init_le w (by omega)]
    exact h
  · intro i hi
    rcases hw.2 i (Nat.le_succ_of_le hi) with h | h
    · left; intro j hj; rw [pos_init_le w (by omega), pos_init_le w hi]; exact h j hj
    · right; intro j hj; rw [pos_init_le w (by omega), pos_init_le w hi]; exact h j hj

lemma prefValid_snoc_iff {n : ℕ} {w : Fin n → Fin 4} {d : Fin 4} :
    prefValid (snoc w d) ↔
      prefValid w ∧
      (∀ j ≤ n, ∀ k : ℕ, 0 < k → pos w j ≠ pos w n + k • dir d) ∧
      (onRight (snoc w d) ∨ onTop (snoc w d)) := by
  constructor
  · intro hw
    refine ⟨?_, ?_, ?_⟩
    · have := prefValid_init hw
      simpa using this
    · intro j hj k hk
      have h := hw.1 ⟨n, Nat.lt_succ_self n⟩ j hj k hk
      rw [pos_snoc_le w d j hj, pos_snoc_le w d n le_rfl, snoc_last] at h
      exact h
    · exact hw.2 (n + 1) le_rfl
  · rintro ⟨hw, hpr, hedge⟩
    refine ⟨?_, ?_⟩
    · intro ⟨i, hi⟩ j hj k hk
      · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heqi | hin
        · have hj' : j ≤ n := by omega
          have hpr' := hpr j hj' k hk
          simp_rw [heqi]
          rw [pos_snoc_le w d j hj', pos_snoc_le w d n le_rfl, snoc_last]
          exact hpr'
        · have h := hw.1 ⟨i, hin⟩ j hj k hk
          rw [pos_snoc_le w d j (by omega), pos_snoc_le w d i (Nat.le_of_lt hin)]
          simpa [snoc, hin] using h
    · intro i hi
      by_cases hin : i ≤ n
      · rcases hw.2 i hin with h | h
        · left; intro j hj; rw [pos_snoc_le w d j (by omega), pos_snoc_le w d i hin]; exact h j hj
        · right; intro j hj; rw [pos_snoc_le w d j (by omega), pos_snoc_le w d i hin]; exact h j hj
      · have : i = n + 1 := by omega
        subst this
        exact hedge

lemma maxX_snoc_of_le {n : ℕ} (w : Fin n → Fin 4) (d : Fin 4)
    (hd : (dir d).1 ≤ 0) : maxX (snoc w d) = maxX w := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    have hjn : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases h : j ≤ n
    · rw [pos_snoc_le w d j h]; exact le_maxX w h
    · have : j = n + 1 := by omega
      subst this
      rw [pos_snoc_succ]
      simp only [Prod.fst_add]
      have := le_maxX w le_rfl
      omega
  · obtain ⟨j, hj, hjm⟩ := exists_eq_maxX w
    rw [← hjm, ← pos_snoc_le w d j hj]
    exact le_maxX (snoc w d) (Nat.le_succ_of_le hj)

lemma maxX_init_of_lt {n : ℕ} (w : Fin (n + 1) → Fin 4)
    (hlt : (pos w (n + 1)).1 < maxX w) : maxX (init w) = maxX w := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [pos_init_le w hjn]
    exact le_maxX w (Nat.le_succ_of_le hjn)
  · obtain ⟨j, hj, hjm⟩ := exists_eq_maxX w
    have hjn : j ≤ n := by
      by_contra h
      have : j = n + 1 := by omega
      subst this
      omega
    rw [← hjm, ← pos_init_le w hjn]
    exact le_maxX (init w) hjn

-- Diagonal reflection
def reflD (d : Fin 4) : Fin 4 :=
  if d = 0 then 1 else if d = 1 then 0 else if d = 2 then 3 else 2

def reflW {n : ℕ} (w : Fin n → Fin 4) : Fin n → Fin 4 :=
  fun i => reflD (w i)

@[simp] lemma reflD_reflD (d : Fin 4) : reflD (reflD d) = d := by
  fin_cases d <;> rfl

@[simp] lemma reflW_reflW {n : ℕ} (w : Fin n → Fin 4) : reflW (reflW w) = w := by
  ext i; simp [reflW]

lemma dir_reflD (d : Fin 4) : dir (reflD d) = ((dir d).2, (dir d).1) := by
  fin_cases d <;> rfl

lemma pos_reflW {n : ℕ} (w : Fin n → Fin 4) (i : ℕ) :
    pos (reflW w) i = ((pos w i).2, (pos w i).1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    by_cases hi : i < n
    · simp only [pos_succ _ hi, ih, reflW, dir_reflD, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]
    · simp [pos, hi, ih]

lemma prudent_reflW {n : ℕ} (w : Fin n → Fin 4) :
    prudent (reflW w) ↔ prudent w := by
  suffices h : ∀ {u : Fin n → Fin 4}, prudent u → prudent (reflW u) from
    ⟨fun h' => by simpa using h h', h⟩
  intro u hu i j hj k hk heq
  apply hu i j hj k hk
  simp only [pos_reflW, reflW, dir_reflD, Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq] at heq
  ext <;> simp [heq.1, heq.2]

lemma prefixEdge_reflW {n : ℕ} (w : Fin n → Fin 4) :
    prefixEdge (reflW w) ↔ prefixEdge w := by
  simp only [prefixEdge, pos_reflW]
  constructor <;> intro h i hi
  · exact (h i hi).symm
  · exact (h i hi).symm

lemma prefValid_reflW {n : ℕ} (w : Fin n → Fin 4) :
    prefValid (reflW w) ↔ prefValid w := by
  simp only [prefValid, prudent_reflW, prefixEdge_reflW]

lemma onTop_reflW {n : ℕ} (w : Fin n → Fin 4) :
    onTop (reflW w) ↔ onRight w := by
  simp only [onTop, onRight, pos_reflW]

lemma onRight_reflW {n : ℕ} (w : Fin n → Fin 4) :
    onRight (reflW w) ↔ onTop w := by
  simp only [onTop, onRight, pos_reflW]

lemma maxX_reflW {n : ℕ} (w : Fin n → Fin 4) :
    maxX (reflW w) = maxY w := by
  simp only [maxX, maxY, pos_reflW]

lemma maxY_reflW {n : ℕ} (w : Fin n → Fin 4) :
    maxY (reflW w) = maxX w := by
  simp only [maxX, maxY, pos_reflW]

lemma valid_reflW {n : ℕ} (w : Fin n → Fin 4) :
    valid (reflW w) ↔ valid w := by
  suffices h : ∀ {u : Fin n → Fin 4}, valid u → valid (reflW u) from
    ⟨fun h' => by simpa using h h', h⟩
  intro u ⟨h1, h2, h3⟩
  refine ⟨(prudent_reflW u).mpr h1, (prefixEdge_reflW u).mpr h2, ?_⟩
  intro j hj
  simp only [pos_reflW]
  exact ⟨(h3 j hj).2, (h3 j hj).1⟩

-- Discrete IVT
lemma discrete_ivt_aux :
    ∀ (d : ℕ) (f : ℕ → ℤ) (a : ℕ) (z : ℤ),
      (∀ m, a ≤ m → m < a + d → |f (m + 1) - f m| ≤ 1) →
      f a ≤ z → z ≤ f (a + d) →
      ∃ m, a ≤ m ∧ m ≤ a + d ∧ f m = z := by
  intro d
  induction d with
  | zero =>
    intro f a z _ ha hb
    exact ⟨a, le_rfl, le_rfl, le_antisymm ha hb⟩
  | succ d ih =>
    intro f a z hstep ha hb
    by_cases hz : z ≤ f (a + d)
    · obtain ⟨m, hm1, hm2, hm3⟩ := ih f a z (fun m h1 h2 => hstep m h1 (by omega)) ha hz
      exact ⟨m, hm1, Nat.le_succ_of_le hm2, hm3⟩
    · have h1 := abs_le.mp (hstep (a + d) (by omega) (by omega))
      have h2 : f (a + d) < z := lt_of_not_ge hz
      have h4 : a + (d + 1) = a + d + 1 := by omega
      rw [h4] at hb
      have h3 : z = f (a + d + 1) := by omega
      exact ⟨a + d + 1, by omega, by omega, h3.symm⟩

lemma discrete_ivt {f : ℕ → ℤ} {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ m, a ≤ m → m < b → |f (m + 1) - f m| ≤ 1)
    {z : ℤ} (hza : f a ≤ z) (hzb : z ≤ f b) :
    ∃ m, a ≤ m ∧ m ≤ b ∧ f m = z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact discrete_ivt_aux d f a z hstep hza hzb

lemma discrete_ivt_down {f : ℕ → ℤ} {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ m, a ≤ m → m < b → |f (m + 1) - f m| ≤ 1)
    {z : ℤ} (hzb : f b ≤ z) (hza : z ≤ f a) :
    ∃ m, a ≤ m ∧ m ≤ b ∧ f m = z := by
  have hstep' : ∀ m, a ≤ m → m < b → |(-f (m + 1)) - (-f m)| ≤ 1 := by
    intro m h1 h2
    have := hstep m h1 h2
    rwa [show -f (m + 1) - -f m = -(f (m + 1) - f m) by ring, abs_neg]
  obtain ⟨m, hm1, hm2, hm3⟩ := discrete_ivt (f := fun m => -f m) hab hstep' (z := -z)
    (neg_le_neg hza) (neg_le_neg hzb)
  exact ⟨m, hm1, hm2, by omega⟩

lemma exists_max_lt {n : ℕ} (P : ℕ → Prop) [DecidablePred P]
    {j : ℕ} (hjn : j ≤ n) (hj : P j) (hnot : ¬ P n) :
    ∃ i, j ≤ i ∧ i < n ∧ P i ∧ ∀ m, i < m → m ≤ n → ¬ P m := by
  let S := (Finset.range (n + 1)).filter (fun m => j ≤ m ∧ P m)
  have hS : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_rfl, hj⟩⟩
  let i := S.max' hS
  have hi_mem := Finset.max'_mem S hS
  rw [Finset.mem_filter, Finset.mem_range] at hi_mem
  have hin : i < n := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi_mem.1) with hlt | heq
    · exact hlt
    · exfalso; rw [heq] at hi_mem; exact hnot hi_mem.2.2
  refine ⟨i, hi_mem.2.1, hin, hi_mem.2.2, ?_⟩
  intro m hm1 hm2 hPm
  have hm_mem : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, hPm⟩
  have := Finset.le_max' S m hm_mem
  omega

-- Counts T and Td
noncomputable def T (k n : ℕ) : ℤ := by
  classical
  exact ((Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k)).card : ℤ)

noncomputable def Td (d : Fin 4) (k n : ℕ) : ℤ := by
  classical
  exact ((Finset.univ.filter (fun w : Fin n → Fin 4 =>
    topDist w k ∧ ∃ h : 0 < n, w ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = d)).card : ℤ)

lemma T_zero_eq_count (n : ℕ) : T 0 n = count n := by
  classical
  simp only [T, count, valid_iff_topDist_zero]

lemma T_eq_sum_Td {k n : ℕ} (hn : 0 < n) :
    T k n = Td 0 k n + Td 1 k n + Td 2 k n := by
  classical
  have hlt : n - 1 < n := Nat.sub_lt hn Nat.zero_lt_one
  have h3 : ∀ w : Fin n → Fin 4, topDist w k → w ⟨n - 1, hlt⟩ ≠ 3 := by
    intro w hw hlast
    have htop := hw.2.1 (n - 1) (Nat.sub_le n 1)
    have hstep := pos_succ w hlt
    rw [Nat.sub_add_cancel hn, hlast, dir_three] at hstep
    have : (pos w n).2 = (pos w (n - 1)).2 - 1 := by
      rw [hstep]; simp; ring
    omega
  have hsplit : (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k)) =
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ w ⟨n - 1, hlt⟩ = 0)) ∪
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ w ⟨n - 1, hlt⟩ = 1)) ∪
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ w ⟨n - 1, hlt⟩ = 2)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hw
      rcases dir_cases (w ⟨n - 1, hlt⟩) with h | h | h | h
      · left; left; exact ⟨hw, h⟩
      · left; right; exact ⟨hw, h⟩
      · right; exact ⟨hw, h⟩
      · exact False.elim (h3 w hw h)
    · rintro ((⟨hw, _⟩ | ⟨hw, _⟩) | ⟨hw, _⟩) <;> exact hw
  have hd01 : Disjoint
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ w ⟨n - 1, hlt⟩ = 0))
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ w ⟨n - 1, hlt⟩ = 1)) := by
    rw [Finset.disjoint_filter]
    intro w _ h0 h1
    exact absurd (h0.2.symm.trans h1.2) (by decide)
  have hd012 : Disjoint
      ((Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ w ⟨n - 1, hlt⟩ = 0)) ∪
       (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ w ⟨n - 1, hlt⟩ = 1)))
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ w ⟨n - 1, hlt⟩ = 2)) := by
    rw [Finset.disjoint_left]
    intro w hw h2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hw h2
    rcases hw with ⟨_, h0⟩ | ⟨_, h1⟩
    · exact absurd (h0.symm.trans h2.2) (by decide)
    · exact absurd (h1.symm.trans h2.2) (by decide)
  have hcard : ∀ d : Fin 4,
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ ∃ h : 0 < n, w ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = d)).card =
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w k ∧ w ⟨n - 1, hlt⟩ = d)).card := by
    intro d; congr 1; ext w; simp [hn]
  simp only [T, Td]
  rw [hcard 0, hcard 1, hcard 2, hsplit, Finset.card_union_of_disjoint hd012,
    Finset.card_union_of_disjoint hd01]
  push_cast
  ring

lemma Td_two_zero {n : ℕ} : Td 2 0 n = 0 := by
  classical
  have h : (Finset.univ.filter (fun w : Fin n → Fin 4 =>
      topDist w 0 ∧ ∃ h : 0 < n, w ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 2)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro w _ ⟨hw, hn, hlast⟩
    have hstep := pos_succ w (Nat.sub_lt hn Nat.zero_lt_one)
    rw [Nat.sub_add_cancel hn, hlast, dir_two] at hstep
    have hle := le_maxX w (Nat.sub_le n 1)
    have hmax := hw.2.2
    simp only [Nat.cast_zero, add_zero] at hmax
    have : (pos w n).1 = (pos w (n - 1)).1 - 1 := by
      rw [hstep]; simp; ring
    omega
  simp [Td, h]

lemma Td_zero_eq_Td_one_at_zero (n : ℕ) : Td 0 0 n = Td 1 0 n := by
  classical
  simp only [Td]
  congr 1
  refine Finset.card_bij (fun w _ => reflW w) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rcases hw with ⟨hw, hn, hlast⟩
    refine ⟨(valid_iff_topDist_zero _).mp ((valid_reflW w).mpr ((valid_iff_topDist_zero w).mpr hw)), hn, ?_⟩
    simp [reflW, hlast, reflD]
  · intro w1 _ w2 _ h
    simpa using congrArg reflW h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases hw with ⟨hw, hn, hlast⟩
    refine ⟨reflW w, ?_, reflW_reflW w⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(valid_iff_topDist_zero _).mp ((valid_reflW w).mpr ((valid_iff_topDist_zero w).mpr hw)), hn, ?_⟩
    simp [reflW, hlast, reflD]

lemma T_zero_zero : T 0 0 = 1 := by
  classical
  have h : (Finset.univ.filter (fun w : Fin 0 → Fin 4 => topDist w 0)) = Finset.univ := by
    rw [Finset.filter_eq_self]
    intro w _
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i hi
      rcases Nat.le_zero.mp hi with rfl
      left; intro j hj; rcases Nat.le_zero.mp hj with rfl; exact le_rfl
    · intro j hj; rcases Nat.le_zero.mp hj with rfl; exact le_rfl
    · have hm : maxX w = (pos w 0).1 := by
        apply le_antisymm
        · exact Finset.sup'_le _ _ (fun j hj => by
            rcases Nat.le_zero.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) with rfl
            exact le_rfl)
        · exact le_maxX w le_rfl
      rw [hm]; simp
  simp only [T, h, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero, Nat.cast_one]

lemma T_pos_zero {k : ℕ} (hk : 0 < k) : T k 0 = 0 := by
  classical
  have h : (Finset.univ.filter (fun w : Fin 0 → Fin 4 => topDist w k)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro w _ hw
    have hm : maxX w = (pos w 0).1 := by
      apply le_antisymm
      · exact Finset.sup'_le _ _ (fun j hj => by
          rcases Nat.le_zero.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) with rfl
          exact le_rfl)
      · exact le_maxX w le_rfl
    have h0 : (pos w 0).1 = 0 := rfl
    have hmax := hw.2.2
    rw [hm, h0] at hmax
    omega
  rw [T, h]
  simp

lemma Td_zero_len {d : Fin 4} {k : ℕ} : Td d k 0 = 0 := by
  classical
  simp [Td]

-- Lemma 1: Extending by 1 (Up)
lemma topDist_snoc_one {n k : ℕ} {w : Fin n → Fin 4} (hw : topDist w k) :
    topDist (snoc w 1) k := by
  have htop' : onTop (snoc w 1) := by
    intro j hj
    rw [pos_snoc_succ, dir_one]
    by_cases hjn : j ≤ n
    · rw [pos_snoc_le w 1 j hjn]
      have := hw.2.1 j hjn
      simp only [Prod.snd_add]; omega
    · have : j = n + 1 := by omega
      subst this
      rw [pos_snoc_succ, dir_one]
  refine ⟨?_, htop', ?_⟩
  · rw [prefValid_snoc_iff]
    refine ⟨hw.1, ?_, Or.inr htop'⟩
    intro j hj m hm heq
    rw [smul_dir_one] at heq
    have := hw.2.1 j hj
    have h2 := congrArg Prod.snd heq
    simp only [Prod.snd_add] at h2
    omega
  · rw [maxX_snoc_of_le w 1 (by simp [dir_one]), pos_snoc_succ, dir_one]
    simp [hw.2.2]

lemma topDist_init_of_one {n k : ℕ} (hk : 0 < k) {w : Fin (n + 1) → Fin 4}
    (hw : topDist w k) (hlast : w ⟨n, Nat.lt_succ_self n⟩ = 1) :
    topDist (init w) k := by
  have hpos : pos w (n + 1) = pos w n + (0, 1) := by
    rw [pos_succ _ (Nat.lt_succ_self n), hlast, dir_one]
  have hlt : (pos w (n + 1)).1 < maxX w := by
    have := hw.2.2; omega
  have hmax : maxX (init w) = maxX w := maxX_init_of_lt w hlt
  have hnotRight : ¬ onRight (init w) := by
    rw [onRight_iff_maxX, hmax, pos_init_le w le_rfl]
    have : (pos w (n + 1)).1 = (pos w n).1 := by simp [hpos]
    omega
  have hpref := prefValid_init hw.1
  have htop : onTop (init w) := (hpref.2 n le_rfl).resolve_left hnotRight
  refine ⟨hpref, htop, ?_⟩
  rw [hmax, pos_init_le w le_rfl, hw.2.2]
  simp [hpos]

lemma Td_one_succ {k n : ℕ} (hk : 0 < k) : Td 1 k (n + 1) = T k n := by
  classical
  simp only [Td, T]
  congr 1
  refine Finset.card_bij (fun w _ => init w) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rcases hw with ⟨hw, _, hlast⟩
    exact topDist_init_of_one hk hw hlast
  · intro w1 hw1 w2 hw2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    have h1 : w1 ⟨n, Nat.lt_succ_self n⟩ = 1 := hw1.2.2
    have h2 : w2 ⟨n, Nat.lt_succ_self n⟩ = 1 := hw2.2.2
    rw [← snoc_init_last w1, ← snoc_init_last w2, h1, h2, heq]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨snoc u 1, ?_, init_snoc u 1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨topDist_snoc_one hu, Nat.zero_lt_succ n, snoc_last u 1⟩

-- Lemma 2: Extending by 0 (Right) from topDist w (k + 1)
lemma prudent_snoc_zero_of_topDist_succ {n k : ℕ} {w : Fin n → Fin 4}
    (hw : topDist w (k + 1)) (hn : 0 < n) (hne2 : w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ≠ 2) :
    ∀ j ≤ n, ∀ m : ℕ, 0 < m → pos w j ≠ pos w n + m • dir 0 := by
  intro j hj m hm heq
  rw [smul_dir_zero] at heq
  have hy : (pos w j).2 = (pos w n).2 := (congrArg Prod.snd heq).trans (by simp)
  have hx : (pos w j).1 > (pos w n).1 := by
    have h1 := congrArg Prod.fst heq
    simp only [Prod.fst_add] at h1
    omega
  have hjn : j < n := by
    rcases lt_or_eq_of_le hj with h | h
    · exact h
    · subst h; omega
  have hex : ∃ r, j ≤ r ∧ r < n ∧ (pos w r).1 > (pos w n).1 ∧
      ∀ t, r ≤ t → t ≤ n → (pos w t).2 = (pos w n).2 := by
    by_cases hall : ∀ t, j ≤ t → t ≤ n → (pos w t).2 = (pos w n).2
    · exact ⟨j, le_rfl, hjn, hx, hall⟩
    · have hex_lt : ∃ t, j ≤ t ∧ t ≤ n ∧ (pos w t).2 < (pos w n).2 := by
        push Not at hall
        obtain ⟨t, ht1, ht2, ht3⟩ := hall
        have := hw.2.1 t ht2
        exact ⟨t, ht1, ht2, lt_of_le_of_ne this ht3⟩
      obtain ⟨t0, ht0_1, ht0_2, ht0_3⟩ := hex_lt
      obtain ⟨i, hi1, hi2, hi3, himax⟩ := exists_max_lt (fun t => (pos w t).2 < (pos w n).2)
        ht0_2 ht0_3 (lt_irrefl _)
      have hji : j ≤ i := le_trans ht0_1 hi1
      have hnotTop : ¬ (∀ s ≤ i, (pos w s).2 ≤ (pos w i).2) := by
        intro h; have := h j hji; omega
      have hright_i : ∀ s ≤ i, (pos w s).1 ≤ (pos w i).1 :=
        (hw.1.2 i (Nat.le_of_lt hi2)).resolve_right hnotTop
      have hxi : (pos w i).1 > (pos w n).1 := lt_of_lt_of_le hx (hright_i j hji)
      have hi1_y : (pos w (i + 1)).2 = (pos w n).2 := by
        have hle := hw.2.1 (i + 1) (by omega)
        have hnot := himax (i + 1) (Nat.lt_succ_self i) (by omega)
        omega
      have hstep_i := pos_succ w hi2
      have hdir_i : w ⟨i, hi2⟩ = 1 := by
        rcases dir_cases (w ⟨i, hi2⟩) with h | h | h | h
        · rw [h, dir_zero] at hstep_i; have := congrArg Prod.snd hstep_i; simp at this; omega
        · exact h
        · rw [h, dir_two] at hstep_i; have := congrArg Prod.snd hstep_i; simp at this; omega
        · rw [h, dir_three] at hstep_i; have := congrArg Prod.snd hstep_i; simp at this; omega
      have hxi1 : (pos w (i + 1)).1 = (pos w i).1 := by
        rw [hstep_i, hdir_i, dir_one]; simp
      have hi1_lt : i + 1 < n := by
        by_contra h
        have heq_n : i + 1 = n := by omega
        have hpos_eq : (pos w (i + 1)).1 = (pos w n).1 := congrArg (fun t => (pos w t).1) heq_n
        omega
      refine ⟨i + 1, by omega, hi1_lt, by omega, ?_⟩
      intro t ht1 ht2
      have hle := hw.2.1 t ht2
      have hnot := himax t (by omega) ht2
      omega
  obtain ⟨r, hrj, hrn, hrx, hry⟩ := hex
  have hny1 : (pos w (n - 1)).2 = (pos w n).2 := hry (n - 1) (by omega) (Nat.sub_le n 1)
  have hstep_last := pos_succ w (Nat.sub_lt hn Nat.zero_lt_one)
  rw [Nat.sub_add_cancel hn] at hstep_last
  have hlast_zero : w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ = 0 := by
    rcases dir_cases (w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩) with h | h | h | h
    · exact h
    · rw [h, dir_one] at hstep_last; have := congrArg Prod.snd hstep_last; simp at this; omega
    · exact False.elim (hne2 h)
    · rw [h, dir_three] at hstep_last; have := congrArg Prod.snd hstep_last; simp at this; omega
  have hnx1 : (pos w (n - 1)).1 = (pos w n).1 - 1 := by
    rw [hstep_last, hlast_zero, dir_zero]; simp
  have hstep_abs : ∀ t, r ≤ t → t < n - 1 → |(pos w (t + 1)).1 - (pos w t).1| ≤ 1 := by
    intro t _ ht2
    rw [pos_succ w (by omega)]
    have := (dir_step_abs (w ⟨t, by omega⟩)).1
    simpa using this
  obtain ⟨p, hp1, hp2, hp3⟩ := discrete_ivt_down (f := fun t => (pos w t).1) (a := r) (b := n - 1)
    (by omega) hstep_abs (z := (pos w n).1) (by omega) (by omega)
  have hpy : (pos w p).2 = (pos w n).2 := hry p hp1 (by omega)
  apply hw.1.1 ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ p hp2 1 Nat.zero_lt_one
  rw [hlast_zero, dir_zero, one_smul]
  ext
  · simp [hp3, hnx1]
  · simp [hpy, hny1]

lemma topDist_snoc_zero {n k : ℕ} {w : Fin n → Fin 4}
    (hw : topDist w (k + 1)) (hn : 0 < n) (hne2 : w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ≠ 2) :
    topDist (snoc w 0) k := by
  have htop : onTop (snoc w 0) := by
    intro j hj
    rw [pos_snoc_succ, dir_zero]
    by_cases hjn : j ≤ n
    · rw [pos_snoc_le w 0 j hjn]
      simpa using hw.2.1 j hjn
    · have : j = n + 1 := by omega
      subst this
      rw [pos_snoc_succ, dir_zero]
  refine ⟨?_, htop, ?_⟩
  · rw [prefValid_snoc_iff]
    exact ⟨hw.1, prudent_snoc_zero_of_topDist_succ hw hn hne2, Or.inr htop⟩
  · have hmax : maxX (snoc w 0) = maxX w := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro j hj
        have hjn : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        by_cases h : j ≤ n
        · rw [pos_snoc_le w 0 j h]; exact le_maxX w h
        · have : j = n + 1 := by omega
          subst this
          rw [pos_snoc_succ, dir_zero]
          have := hw.2.2
          simp only [Prod.fst_add]; omega
      · obtain ⟨j, hj, hjm⟩ := exists_eq_maxX w
        rw [← hjm, ← pos_snoc_le w 0 j hj]
        exact le_maxX (snoc w 0) (Nat.le_succ_of_le hj)
    rw [hmax, pos_snoc_succ, dir_zero, hw.2.2]
    push_cast
    simp only [Prod.fst_add]
    ring

lemma topDist_init_of_zero {n k : ℕ} (hk : 0 < k) {w : Fin (n + 1) → Fin 4}
    (hw : topDist w k) (hlast : w ⟨n, Nat.lt_succ_self n⟩ = 0) :
    topDist (init w) (k + 1) ∧ ∃ hn : 0 < n, (init w) ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ≠ 2 := by
  have hpos : pos w (n + 1) = pos w n + (1, 0) := by
    rw [pos_succ _ (Nat.lt_succ_self n), hlast, dir_zero]
  have hlt : (pos w (n + 1)).1 < maxX w := by
    have := hw.2.2; omega
  have hmax : maxX (init w) = maxX w := maxX_init_of_lt w hlt
  have hnotRight : ¬ onRight (init w) := by
    rw [onRight_iff_maxX, hmax, pos_init_le w le_rfl]
    have : (pos w (n + 1)).1 = (pos w n).1 + 1 := by simp [hpos]
    omega
  have hpref := prefValid_init hw.1
  have htop : onTop (init w) := (hpref.2 n le_rfl).resolve_left hnotRight
  have htd : topDist (init w) (k + 1) := by
    refine ⟨hpref, htop, ?_⟩
    rw [hmax, pos_init_le w le_rfl, hw.2.2]
    have : (pos w (n + 1)).1 = (pos w n).1 + 1 := by simp [hpos]
    push_cast
    omega
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    have hm : maxX (init w) = (pos (init w) 0).1 := by
      apply le_antisymm
      · exact Finset.sup'_le _ _ (fun j hj => by
          rcases Nat.le_zero.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) with rfl
          exact le_rfl)
      · exact le_maxX _ le_rfl
    have hmax_eq := htd.2.2
    rw [hm] at hmax_eq
    omega
  refine ⟨htd, hn, ?_⟩
  intro h2
  have hlt1 : n - 1 < n := Nat.sub_lt hn Nat.zero_lt_one
  have hlt2 : n - 1 < n + 1 := Nat.lt_succ_of_lt hlt1
  have hstep := pos_succ w hlt2
  have hinit2 : w ⟨n - 1, hlt2⟩ = 2 := h2
  rw [Nat.sub_add_cancel hn, hinit2, dir_two] at hstep
  apply hw.1.1 ⟨n, Nat.lt_succ_self n⟩ (n - 1) (Nat.sub_le n 1) 1 Nat.zero_lt_one
  rw [hlast, dir_zero, one_smul]
  ext
  · have : (pos w n).1 = (pos w (n - 1)).1 - 1 := by rw [hstep]; simp; ring
    simp; omega
  · have : (pos w n).2 = (pos w (n - 1)).2 := by rw [hstep]; simp
    simp; omega

lemma Td_zero_succ {k n : ℕ} (hk : 0 < k) :
    Td 0 k (n + 1) = T (k + 1) n - Td 2 (k + 1) n := by
  classical
  have hcard :
      (Finset.univ.filter (fun w : Fin (n + 1) → Fin 4 =>
        topDist w k ∧ ∃ h : 0 < n + 1, w ⟨n + 1 - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 0)).card =
      (Finset.univ.filter (fun w : Fin n → Fin 4 =>
        topDist w (k + 1) ∧ ¬ (∃ h : 0 < n, w ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 2))).card := by
    refine Finset.card_bij (fun w _ => init w) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      have hlast : w ⟨n, Nat.lt_succ_self n⟩ = 0 := hw.2.2
      obtain ⟨htd, hn, hne2⟩ := topDist_init_of_zero hk hw.1 hlast
      exact ⟨htd, fun ⟨_, h2⟩ => hne2 h2⟩
    · intro w1 hw1 w2 hw2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
      have h1 : w1 ⟨n, Nat.lt_succ_self n⟩ = 0 := hw1.2.2
      have h2 : w2 ⟨n, Nat.lt_succ_self n⟩ = 0 := hw2.2.2
      rw [← snoc_init_last w1, ← snoc_init_last w2, h1, h2, heq]
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      have hn : 0 < n := by
        by_contra h
        have : n = 0 := by omega
        subst this
        have := hu.1.2.2
        simp [maxX, pos] at this
        omega
      have hne2 : u ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ≠ 2 := fun h => hu.2 ⟨hn, h⟩
      refine ⟨snoc u 0, ?_, init_snoc u 0⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨topDist_snoc_zero hu.1 hn hne2, Nat.zero_lt_succ n, snoc_last u 0⟩
  have hsdiff :
      (Finset.univ.filter (fun w : Fin n → Fin 4 =>
        topDist w (k + 1) ∧ ¬ (∃ h : 0 < n, w ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 2))).card +
      (Finset.univ.filter (fun w : Fin n → Fin 4 =>
        topDist w (k + 1) ∧ ∃ h : 0 < n, w ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 2)).card =
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w (k + 1))).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_filter]; intro w _ h1 h2; exact h1.2 h2.2
  simp only [Td, T]
  omega

-- Lemma 3: Extending by 2 (Left) from topDist w (k + 1)
lemma prudent_snoc_two_of_topDist_succ {n k : ℕ} {w : Fin n → Fin 4}
    (hw : topDist w (k + 1)) (hn : 0 < n) (hne0 : w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ≠ 0) :
    ∀ j ≤ n, ∀ m : ℕ, 0 < m → pos w j ≠ pos w n + m • dir 2 := by
  intro j hj m hm heq
  rw [smul_dir_two] at heq
  have hy : (pos w j).2 = (pos w n).2 := (congrArg Prod.snd heq).trans (by simp)
  have hx : (pos w j).1 < (pos w n).1 := by
    have h1 := congrArg Prod.fst heq
    simp only [Prod.fst_add] at h1
    omega
  have hjn : j < n := by
    rcases lt_or_eq_of_le hj with h | h
    · exact h
    · subst h; omega
  have hlast_two : ∀ r ≤ n, r < n → (pos w r).1 < (pos w n).1 →
      (∀ t, r ≤ t → t ≤ n → (pos w t).2 = (pos w n).2) → False := by
    intro r hrn hrltn hrx hry
    have hny1 : (pos w (n - 1)).2 = (pos w n).2 := hry (n - 1) (by omega) (Nat.sub_le n 1)
    have hstep_last := pos_succ w (Nat.sub_lt hn Nat.zero_lt_one)
    rw [Nat.sub_add_cancel hn] at hstep_last
    have hlast_2 : w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ = 2 := by
      rcases dir_cases (w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩) with h | h | h | h
      · exact False.elim (hne0 h)
      · rw [h, dir_one] at hstep_last; have := congrArg Prod.snd hstep_last; simp at this; omega
      · exact h
      · rw [h, dir_three] at hstep_last; have := congrArg Prod.snd hstep_last; simp at this; omega
    have hnx1 : (pos w (n - 1)).1 = (pos w n).1 + 1 := by
      rw [hstep_last, hlast_2, dir_two]; simp
    have hstep_abs : ∀ t, r ≤ t → t < n - 1 → |(pos w (t + 1)).1 - (pos w t).1| ≤ 1 := by
      intro t _ ht2
      rw [pos_succ w (by omega)]
      have := (dir_step_abs (w ⟨t, by omega⟩)).1
      simpa using this
    obtain ⟨p, hp1, hp2, hp3⟩ := discrete_ivt (f := fun t => (pos w t).1) (a := r) (b := n - 1)
      (by omega) hstep_abs (z := (pos w n).1) (by omega) (by omega)
    have hpy : (pos w p).2 = (pos w n).2 := hry p hp1 (by omega)
    apply hw.1.1 ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ p hp2 1 Nat.zero_lt_one
    rw [hlast_2, dir_two, one_smul]
    ext
    · simp [hp3, hnx1]
    · simp [hpy, hny1]
  by_cases hall : ∀ t, j ≤ t → t ≤ n → (pos w t).2 = (pos w n).2
  · exact hlast_two j hj hjn hx hall
  · have hex_lt : ∃ t, j ≤ t ∧ t ≤ n ∧ (pos w t).2 < (pos w n).2 := by
      push Not at hall
      obtain ⟨t, ht1, ht2, ht3⟩ := hall
      have := hw.2.1 t ht2
      exact ⟨t, ht1, ht2, lt_of_le_of_ne this ht3⟩
    obtain ⟨t0, ht0_1, ht0_2, ht0_3⟩ := hex_lt
    obtain ⟨i, hi1, hi2, hi3, himax⟩ := exists_max_lt (fun t => (pos w t).2 < (pos w n).2)
      ht0_2 ht0_3 (lt_irrefl _)
    have hji : j ≤ i := le_trans ht0_1 hi1
    have hnotTop : ¬ (∀ s ≤ i, (pos w s).2 ≤ (pos w i).2) := by
      intro h; have := h j hji; omega
    have hright_i : ∀ s ≤ i, (pos w s).1 ≤ (pos w i).1 :=
      (hw.1.2 i (Nat.le_of_lt hi2)).resolve_right hnotTop
    have hi1_y : (pos w (i + 1)).2 = (pos w n).2 := by
      have hle := hw.2.1 (i + 1) (by omega)
      have hnot := himax (i + 1) (Nat.lt_succ_self i) (by omega)
      omega
    have hstep_i := pos_succ w hi2
    have hdir_i : w ⟨i, hi2⟩ = 1 := by
      rcases dir_cases (w ⟨i, hi2⟩) with h | h | h | h
      · rw [h, dir_zero] at hstep_i; have := congrArg Prod.snd hstep_i; simp at this; omega
      · exact h
      · rw [h, dir_two] at hstep_i; have := congrArg Prod.snd hstep_i; simp at this; omega
      · rw [h, dir_three] at hstep_i; have := congrArg Prod.snd hstep_i; simp at this; omega
    have hxi1 : (pos w (i + 1)).1 = (pos w i).1 := by
      rw [hstep_i, hdir_i, dir_one]; simp
    have hi1_ry : ∀ t, i + 1 ≤ t → t ≤ n → (pos w t).2 = (pos w n).2 := by
      intro t ht1 ht2
      have hle := hw.2.1 t ht2
      have hnot := himax t (by omega) ht2
      omega
    rcases lt_trichotomy (pos w (i + 1)).1 (pos w n).1 with hlt | heqx | hgt
    · have hi1_lt : i + 1 < n := by
        by_contra h
        have heqn : i + 1 = n := by omega
        have hpos_eq : (pos w (i + 1)).1 = (pos w n).1 := congrArg (fun t => (pos w t).1) heqn
        omega
      exact hlast_two (i + 1) (by omega) hi1_lt hlt hi1_ry
    · have hi1_lt : i + 1 < n := by
        by_contra h
        have heqn : i + 1 = n := by omega
        have hmax_i := hw.2.2
        have hmax_le : maxX w ≤ (pos w i).1 := by
          apply Finset.sup'_le
          intro s hs
          have hsn : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
          by_cases hsi : s ≤ i
          · exact hright_i s hsi
          · have hse : s = i + 1 := by omega
            rw [hse, hxi1]
        have hpos_eq : (pos w (i + 1)).1 = (pos w n).1 := congrArg (fun t => (pos w t).1) heqn
        omega
      have hny1 : (pos w (n - 1)).2 = (pos w n).2 := hi1_ry (n - 1) (by omega) (Nat.sub_le n 1)
      have hstep_last := pos_succ w (Nat.sub_lt hn Nat.zero_lt_one)
      rw [Nat.sub_add_cancel hn] at hstep_last
      have hlast_2 : w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ = 2 := by
        rcases dir_cases (w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩) with h | h | h | h
        · exact False.elim (hne0 h)
        · rw [h, dir_one] at hstep_last; have := congrArg Prod.snd hstep_last; simp at this; omega
        · exact h
        · rw [h, dir_three] at hstep_last; have := congrArg Prod.snd hstep_last; simp at this; omega
      have hnx1 : (pos w (n - 1)).1 = (pos w n).1 + 1 := by
        rw [hstep_last, hlast_2, dir_two]; simp
      have hlt_last : i + 1 < n - 1 := by
        by_contra h
        have heq_last : i + 1 = n - 1 := by omega
        have hpos_eq : (pos w (i + 1)).1 = (pos w (n - 1)).1 := congrArg (fun t => (pos w t).1) heq_last
        omega
      apply hw.1.1 ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ (i + 1) (by simp; omega) 1 Nat.zero_lt_one
      rw [hlast_2, dir_two, one_smul]
      ext
      · simp [heqx, hnx1]
      · simp [hi1_y, hny1]
    · have hi1_lt : i + 1 < n := by
        by_contra h
        have heq_n : i + 1 = n := by omega
        have hpos_eq : (pos w (i + 1)).1 = (pos w n).1 := congrArg (fun t => (pos w t).1) heq_n
        omega
      have hex2 : ∃ m, i + 1 ≤ m ∧ m < n ∧ (∀ hmn : m < n, w ⟨m, hmn⟩ = 2) ∧
          ∀ t, i + 1 ≤ t → t ≤ m → (pos w t).1 ≥ (pos w (i + 1)).1 := by
        let Slt := (Finset.range (n + 1)).filter (fun t => i + 1 ≤ t ∧ (pos w t).1 < (pos w (i + 1)).1)
        have hSlt : Slt.Nonempty := ⟨n, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), by omega, hgt⟩⟩
        let m1 := Slt.min' hSlt
        have hm1_mem := Finset.min'_mem Slt hSlt
        rw [Finset.mem_filter, Finset.mem_range] at hm1_mem
        have hm1_gt : i + 1 < m1 := by
          rcases lt_or_eq_of_le hm1_mem.2.1 with h | h
          · exact h
          · exfalso; have := hm1_mem.2.2; rw [h] at this; omega
        refine ⟨m1 - 1, by omega, by omega, ?_, ?_⟩
        · intro hmn
          have hm1_lt : (pos w m1).1 < (pos w (i + 1)).1 := hm1_mem.2.2
          have hprev_ge : (pos w (m1 - 1)).1 ≥ (pos w (i + 1)).1 := by
            by_contra h
            have hmem : m1 - 1 ∈ Slt := Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩
            have := Finset.min'_le Slt (m1 - 1) hmem
            omega
          have hy1 : (pos w (m1 - 1)).2 = (pos w n).2 := hi1_ry (m1 - 1) (by omega) (by omega)
          have hy2 : (pos w m1).2 = (pos w n).2 := hi1_ry m1 (by omega) (by omega)
          have hstep_m := pos_succ w hmn
          rw [Nat.sub_add_cancel (by omega : 0 < m1)] at hstep_m
          rcases dir_cases (w ⟨m1 - 1, hmn⟩) with h | h | h | h
          · rw [h, dir_zero] at hstep_m; have := congrArg Prod.fst hstep_m; simp at this; omega
          · rw [h, dir_one] at hstep_m; have := congrArg Prod.fst hstep_m; simp at this; omega
          · exact h
          · rw [h, dir_three] at hstep_m; have := congrArg Prod.fst hstep_m; simp at this; omega
        · intro t ht1 ht2
          by_contra h
          have hmem : t ∈ Slt := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by omega), ht1, by omega⟩
          have := Finset.min'_le Slt t hmem
          omega
      obtain ⟨m, hm1, hm2, hm_dir, hm_ge⟩ := hex2
      have hmx : (pos w m).1 ≥ (pos w (i + 1)).1 := hm_ge m hm1 le_rfl
      have hmy : (pos w m).2 = (pos w n).2 := hi1_ry m hm1 (by omega)
      have hdiff_pos : 0 < (pos w m).1 - (pos w j).1 := by omega
      have hd_pos : 0 < ((pos w m).1 - (pos w j).1).toNat := Int.lt_toNat.mpr hdiff_pos
      apply hw.1.1 ⟨m, hm2⟩ j (by simp; omega) ((pos w m).1 - (pos w j).1).toNat hd_pos
      rw [hm_dir hm2, smul_dir_two]
      ext
      · simp only [Prod.fst_add]
        have htn := Int.toNat_of_nonneg (le_of_lt hdiff_pos)
        omega
      · simp [hy, hmy]

lemma topDist_snoc_two {n k : ℕ} {w : Fin n → Fin 4}
    (hw : topDist w (k + 1)) (hn : 0 < n) (hne0 : w ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ≠ 0) :
    topDist (snoc w 2) (k + 2) := by
  have htop : onTop (snoc w 2) := by
    intro j hj
    rw [pos_snoc_succ, dir_two]
    by_cases hjn : j ≤ n
    · rw [pos_snoc_le w 2 j hjn]
      simpa using hw.2.1 j hjn
    · have : j = n + 1 := by omega
      subst this
      rw [pos_snoc_succ, dir_two]
  refine ⟨?_, htop, ?_⟩
  · rw [prefValid_snoc_iff]
    exact ⟨hw.1, prudent_snoc_two_of_topDist_succ hw hn hne0, Or.inr htop⟩
  · rw [maxX_snoc_of_le w 2 (by simp [dir_two]), pos_snoc_succ, dir_two, hw.2.2]
    push_cast
    simp only [Prod.fst_add]
    ring

lemma topDist_init_of_two_ge_two {n k : ℕ} (hk : 2 ≤ k) {w : Fin (n + 1) → Fin 4}
    (hw : topDist w k) (hlast : w ⟨n, Nat.lt_succ_self n⟩ = 2) :
    topDist (init w) (k - 1) ∧ ∃ hn : 0 < n, (init w) ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ≠ 0 := by
  have hpos : pos w (n + 1) = pos w n + (-1, 0) := by
    rw [pos_succ _ (Nat.lt_succ_self n), hlast, dir_two]
  have hlt : (pos w (n + 1)).1 < maxX w := by
    have := hw.2.2; omega
  have hmax : maxX (init w) = maxX w := maxX_init_of_lt w hlt
  have hnotRight : ¬ onRight (init w) := by
    rw [onRight_iff_maxX, hmax, pos_init_le w le_rfl]
    have hmaxw := hw.2.2
    have : (pos w (n + 1)).1 = (pos w n).1 - 1 := by rw [hpos]; simp; ring
    omega
  have hpref := prefValid_init hw.1
  have htop : onTop (init w) := (hpref.2 n le_rfl).resolve_left hnotRight
  have htd : topDist (init w) (k - 1) := by
    refine ⟨hpref, htop, ?_⟩
    rw [hmax, pos_init_le w le_rfl, hw.2.2]
    have : (pos w (n + 1)).1 = (pos w n).1 - 1 := by rw [hpos]; simp; ring
    have hk1 : 1 ≤ k := by omega
    rw [Nat.cast_sub hk1]
    omega
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    have hm : maxX (init w) = (pos (init w) 0).1 := by
      apply le_antisymm
      · exact Finset.sup'_le _ _ (fun j hj => by
          rcases Nat.le_zero.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) with rfl
          exact le_rfl)
      · exact le_maxX _ le_rfl
    have hmax_eq := htd.2.2
    rw [hm] at hmax_eq
    omega
  refine ⟨htd, hn, ?_⟩
  intro h0
  have hlt1 : n - 1 < n := Nat.sub_lt hn Nat.zero_lt_one
  have hlt2 : n - 1 < n + 1 := Nat.lt_succ_of_lt hlt1
  have hstep := pos_succ w hlt2
  have hinit0 : w ⟨n - 1, hlt2⟩ = 0 := h0
  rw [Nat.sub_add_cancel hn, hinit0, dir_zero] at hstep
  apply hw.1.1 ⟨n, Nat.lt_succ_self n⟩ (n - 1) (Nat.sub_le n 1) 1 Nat.zero_lt_one
  rw [hlast, dir_two, one_smul]
  ext
  · have : (pos w n).1 = (pos w (n - 1)).1 + 1 := by rw [hstep]; simp
    simp; omega
  · have : (pos w n).2 = (pos w (n - 1)).2 := by rw [hstep]; simp
    simp; omega

lemma Td_two_succ_ge_two {k n : ℕ} (hk : 2 ≤ k) :
    Td 2 k (n + 1) = T (k - 1) n - Td 0 (k - 1) n := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  have hcard :
      (Finset.univ.filter (fun w : Fin (n + 1) → Fin 4 =>
        topDist w (m + 2) ∧ ∃ h : 0 < n + 1, w ⟨n + 1 - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 2)).card =
      (Finset.univ.filter (fun w : Fin n → Fin 4 =>
        topDist w (m + 1) ∧ ¬ (∃ h : 0 < n, w ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 0))).card := by
    refine Finset.card_bij (fun w _ => init w) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      have hlast : w ⟨n, Nat.lt_succ_self n⟩ = 2 := hw.2.2
      obtain ⟨htd, hn, hne0⟩ := topDist_init_of_two_ge_two (by omega : 2 ≤ m + 2) hw.1 hlast
      rw [show m + 2 - 1 = m + 1 by omega] at htd
      exact ⟨htd, fun ⟨_, h0⟩ => hne0 h0⟩
    · intro w1 hw1 w2 hw2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
      have h1 : w1 ⟨n, Nat.lt_succ_self n⟩ = 2 := hw1.2.2
      have h2 : w2 ⟨n, Nat.lt_succ_self n⟩ = 2 := hw2.2.2
      rw [← snoc_init_last w1, ← snoc_init_last w2, h1, h2, heq]
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      have hn : 0 < n := by
        by_contra h
        have : n = 0 := by omega
        subst this
        have := hu.1.2.2
        simp [maxX, pos] at this
        omega
      have hne0 : u ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ≠ 0 := fun h => hu.2 ⟨hn, h⟩
      refine ⟨snoc u 2, ?_, init_snoc u 2⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨topDist_snoc_two hu.1 hn hne0, Nat.zero_lt_succ n, snoc_last u 2⟩
  have hsdiff :
      (Finset.univ.filter (fun w : Fin n → Fin 4 =>
        topDist w (m + 1) ∧ ¬ (∃ h : 0 < n, w ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 0))).card +
      (Finset.univ.filter (fun w : Fin n → Fin 4 =>
        topDist w (m + 1) ∧ ∃ h : 0 < n, w ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 0)).card =
      (Finset.univ.filter (fun w : Fin n → Fin 4 => topDist w (m + 1))).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_filter]; intro w _ h1 h2; exact h1.2 h2.2
  simp only [Td, T]
  omega

-- Lemma 4: Td 2 1 1 = 1 and Td 2 1 (n + 2) = count n
lemma Td_two_one_one : Td 2 1 1 = 1 := by
  classical
  have h : (Finset.univ.filter (fun w : Fin 1 → Fin 4 =>
      topDist w 1 ∧ ∃ h : 0 < 1, w ⟨1 - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 2)) = {fun _ => 2} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, h2⟩
      funext ⟨i, hi⟩
      rcases Nat.le_zero.mp (Nat.lt_succ_iff.mp hi) with rfl
      exact h2
    · intro hw
      subst hw
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, Nat.zero_lt_one, rfl⟩
      · intro ⟨i, hi⟩ j hj k hk
        rcases Nat.le_zero.mp (Nat.lt_succ_iff.mp hi) with rfl
        rcases Nat.le_zero.mp hj with rfl
        rw [smul_dir_two]
        intro heq
        have := congrArg Prod.fst heq
        simp [pos] at this
        omega
      · intro i hi
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
        · left; intro j hj; rcases Nat.le_zero.mp hj with rfl; exact le_rfl
        · right; intro j hj
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
          · simp [pos, dir]
          · exact le_rfl
      · intro j hj
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
        · simp [pos, dir]
        · exact le_rfl
      · have hm : maxX (fun _ : Fin 1 => (2 : Fin 4)) = 0 := by
          apply le_antisymm
          · apply Finset.sup'_le; intro j hj
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) with rfl | rfl
            · simp [pos]
            · simp [pos, dir]
          · exact le_maxX _ (Nat.zero_le 1)
        rw [hm]; simp [pos, dir]
  simp only [Td]
  rw [h, Finset.card_singleton]
  norm_num

lemma Td_two_one_succ_succ (n : ℕ) : Td 2 1 (n + 2) = count n := by
  classical
  simp only [Td, count]
  congr 1
  refine Finset.card_bij (fun w _ => init (init w)) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rcases hw with ⟨hw, _, hlast⟩
    have hlast' : w ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ = 2 := hlast
    have hpos1 : pos w (n + 2) = pos w (n + 1) + (-1, 0) := by
      rw [pos_succ _ (Nat.lt_succ_self (n + 1)), hlast', dir_two]
    have hmax1 : maxX (init w) = (pos (init w) (n + 1)).1 := by
      have h1 : maxX w = (pos w (n + 1)).1 := by
        have := hw.2.2; simp only [Nat.cast_one] at this
        have : (pos w (n + 2)).1 = (pos w (n + 1)).1 - 1 := by rw [hpos1]; simp; ring
        omega
      have hlt : (pos w (n + 2)).1 < maxX w := by
        have : (pos w (n + 2)).1 = (pos w (n + 1)).1 - 1 := by rw [hpos1]; simp; ring
        omega
      rw [maxX_init_of_lt w hlt, pos_init_le w le_rfl, h1]
    have hpref1 := prefValid_init hw.1
    have htop1 : onTop (init w) := by
      intro j hj
      rw [pos_init_le w hj, pos_init_le w le_rfl]
      have := hw.2.1 j (Nat.le_succ_of_le hj)
      have : (pos w (n + 2)).2 = (pos w (n + 1)).2 := by simp [hpos1]
      omega
    have h1_last : (init w) ⟨n, Nat.lt_succ_self n⟩ = 1 := by
      have hne3 : (init w) ⟨n, Nat.lt_succ_self n⟩ ≠ 3 := by
        intro h3
        have hst := pos_succ (init w) (Nat.lt_succ_self n)
        rw [h3, dir_three] at hst
        have := htop1 n (Nat.le_succ n)
        have : (pos (init w) (n + 1)).2 = (pos (init w) n).2 - 1 := by rw [hst]; simp; ring
        omega
      have hne2 : (init w) ⟨n, Nat.lt_succ_self n⟩ ≠ 2 := by
        intro h2
        have hst := pos_succ (init w) (Nat.lt_succ_self n)
        rw [h2, dir_two] at hst
        have hle := le_maxX (init w) (Nat.le_succ n)
        have : (pos (init w) (n + 1)).1 = (pos (init w) n).1 - 1 := by rw [hst]; simp; ring
        omega
      have hne0 : (init w) ⟨n, Nat.lt_succ_self n⟩ ≠ 0 := by
        intro h0
        have hst := pos_succ w (by omega : n < n + 2)
        have hw0 : w ⟨n, by omega⟩ = 0 := h0
        rw [hw0, dir_zero] at hst
        apply hw.1.1 ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ n (Nat.le_succ n) 1 Nat.zero_lt_one
        rw [hlast', dir_two, one_smul]
        ext
        · have : (pos w (n + 1)).1 = (pos w n).1 + 1 := by simp [hst]
          simp; omega
        · have : (pos w (n + 1)).2 = (pos w n).2 := by simp [hst]
          simp; omega
      rcases dir_cases ((init w) ⟨n, Nat.lt_succ_self n⟩) with h | h | h | h
      · exact False.elim (hne0 h)
      · exact h
      · exact False.elim (hne2 h)
      · exact False.elim (hne3 h)
    have hpos2 : pos (init w) (n + 1) = pos (init w) n + (0, 1) := by
      rw [pos_succ _ (Nat.lt_succ_self n), h1_last, dir_one]
    have hpref2 := prefValid_init hpref1
    have hright2 : onRight (init (init w)) := by
      intro j hj
      rw [pos_init_le (init w) hj, pos_init_le (init w) le_rfl]
      have hle := (onRight_iff_maxX (init w)).mpr hmax1 j (Nat.le_succ_of_le hj)
      have : (pos (init w) (n + 1)).1 = (pos (init w) n).1 := by simp [hpos2]
      omega
    have htop2 : onTop (init (init w)) := by
      intro j hj
      rw [pos_init_le (init w) hj, pos_init_le (init w) le_rfl]
      by_contra hgt
      have hle := htop1 j (Nat.le_succ_of_le hj)
      have hy_eq : (pos (init w) j).2 = (pos (init w) (n + 1)).2 := by
        have : (pos (init w) (n + 1)).2 = (pos (init w) n).2 + 1 := by simp [hpos2]
        omega
      have hx_le : (pos (init w) j).1 ≤ (pos (init w) (n + 1)).1 :=
        (onRight_iff_maxX (init w)).mpr hmax1 j (Nat.le_succ_of_le hj)
      rcases lt_or_eq_of_le hx_le with hx_lt | hx_eq
      · have hjn : j ≤ n + 1 := Nat.le_succ_of_le hj
        have hpos_j := pos_init_le w hjn
        have hpos_n1 := pos_init_le w (le_rfl : n + 1 ≤ n + 1)
        have hdiff_pos : 0 < (pos w (n + 1)).1 - (pos w j).1 := by
          rw [← hpos_j, ← hpos_n1]; omega
        have hd_pos : 0 < ((pos w (n + 1)).1 - (pos w j).1).toNat := Int.lt_toNat.mpr hdiff_pos
        apply hw.1.1 ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ j hjn
          ((pos w (n + 1)).1 - (pos w j).1).toNat hd_pos
        rw [hlast', smul_dir_two]
        ext
        · simp only [Prod.fst_add]
          have htn := Int.toNat_of_nonneg (le_of_lt hdiff_pos)
          omega
        · simp [hy_eq, ← hpos_j, ← hpos_n1]
      · apply hpref1.1 ⟨n, Nat.lt_succ_self n⟩ j hj 1 Nat.zero_lt_one
        rw [h1_last, dir_one, one_smul]
        ext
        · have : (pos (init w) (n + 1)).1 = (pos (init w) n).1 := by simp [hpos2]
          simp; omega
        · have : (pos (init w) (n + 1)).2 = (pos (init w) n).2 + 1 := by simp [hpos2]
          simp; omega
    exact (valid_iff_topDist_zero _).mpr ⟨hpref2, htop2, by simpa using (onRight_iff_maxX _).mp hright2⟩
  · intro w1 hw1 w2 hw2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    have get_second_last : ∀ w : Fin (n + 2) → Fin 4,
        topDist w 1 → w ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ = 2 →
        (init w) ⟨n, Nat.lt_succ_self n⟩ = 1 := by
      intro w hw hlast
      have hpos1 : pos w (n + 2) = pos w (n + 1) + (-1, 0) := by
        rw [pos_succ _ (Nat.lt_succ_self (n + 1)), hlast, dir_two]
      have hmax1 : maxX (init w) = (pos (init w) (n + 1)).1 := by
        have h1 : maxX w = (pos w (n + 1)).1 := by
          have := hw.2.2; simp only [Nat.cast_one] at this
          have : (pos w (n + 2)).1 = (pos w (n + 1)).1 - 1 := by rw [hpos1]; simp; ring
          omega
        have hlt : (pos w (n + 2)).1 < maxX w := by
          have : (pos w (n + 2)).1 = (pos w (n + 1)).1 - 1 := by rw [hpos1]; simp; ring
          omega
        rw [maxX_init_of_lt w hlt, pos_init_le w le_rfl, h1]
      have htop1 : onTop (init w) := by
        intro j hj
        rw [pos_init_le w hj, pos_init_le w le_rfl]
        have := hw.2.1 j (Nat.le_succ_of_le hj)
        have : (pos w (n + 2)).2 = (pos w (n + 1)).2 := by simp [hpos1]
        omega
      rcases dir_cases ((init w) ⟨n, Nat.lt_succ_self n⟩) with h | h | h | h
      · exfalso
        have hst := pos_succ w (by omega : n < n + 2)
        have hw0 : w ⟨n, by omega⟩ = 0 := h
        rw [hw0, dir_zero] at hst
        apply hw.1.1 ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ n (Nat.le_succ n) 1 Nat.zero_lt_one
        rw [hlast, dir_two, one_smul]
        ext
        · have : (pos w (n + 1)).1 = (pos w n).1 + 1 := by simp [hst]
          simp; omega
        · have : (pos w (n + 1)).2 = (pos w n).2 := by simp [hst]
          simp; omega
      · exact h
      · exfalso
        have hst := pos_succ (init w) (Nat.lt_succ_self n)
        rw [h, dir_two] at hst
        have hle := le_maxX (init w) (Nat.le_succ n)
        have : (pos (init w) (n + 1)).1 = (pos (init w) n).1 - 1 := by rw [hst]; simp; ring
        omega
      · exfalso
        have hst := pos_succ (init w) (Nat.lt_succ_self n)
        rw [h, dir_three] at hst
        have := htop1 n (Nat.le_succ n)
        have : (pos (init w) (n + 1)).2 = (pos (init w) n).2 - 1 := by rw [hst]; simp; ring
        omega
    have hl1 : w1 ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ = 2 := hw1.2.2
    have hl2 : w2 ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ = 2 := hw2.2.2
    have h1 := get_second_last w1 hw1.1 hl1
    have h2 := get_second_last w2 hw2.1 hl2
    have hinit : init w1 = init w2 := by
      rw [← snoc_init_last (init w1), ← snoc_init_last (init w2), h1, h2, heq]
    rw [← snoc_init_last w1, ← snoc_init_last w2, hl1, hl2, hinit]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hu_td : topDist u 0 := (valid_iff_topDist_zero u).mp hu
    have hu1_td : topDist (snoc u 1) 0 := topDist_snoc_one hu_td
    have htop2 : onTop (snoc (snoc u 1) 2) := by
      intro j hj
      rw [pos_snoc_succ, dir_two]
      by_cases hjn : j ≤ n + 1
      · rw [pos_snoc_le (snoc u 1) 2 j hjn]
        simpa using hu1_td.2.1 j hjn
      · have : j = n + 2 := by omega
        subst this; rw [pos_snoc_succ, dir_two]
    have hpr2 : ∀ j ≤ n + 1, ∀ m : ℕ, 0 < m →
        pos (snoc u 1) j ≠ pos (snoc u 1) (n + 1) + m • dir 2 := by
      intro j hj m hm heq
      rw [smul_dir_two] at heq
      have hy : (pos (snoc u 1) j).2 = (pos (snoc u 1) (n + 1)).2 :=
        (congrArg Prod.snd heq).trans (by simp)
      have hx : (pos (snoc u 1) j).1 < (pos (snoc u 1) (n + 1)).1 := by
        have h1 := congrArg Prod.fst heq
        simp only [Prod.fst_add] at h1
        omega
      by_cases hjn : j ≤ n
      · rw [pos_snoc_le u 1 j hjn, pos_snoc_succ, dir_one] at hy
        have := hu_td.2.1 j hjn
        simp at hy; omega
      · have : j = n + 1 := by omega
        subst this; omega
    have htd2 : topDist (snoc (snoc u 1) 2) 1 := by
      refine ⟨(prefValid_snoc_iff).mpr ⟨hu1_td.1, hpr2, Or.inr htop2⟩, htop2, ?_⟩
      rw [maxX_snoc_of_le (snoc u 1) 2 (by simp [dir_two]), pos_snoc_succ, dir_two, hu1_td.2.2]
      simp only [Prod.fst_add]
      ring
    refine ⟨snoc (snoc u 1) 2, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨htd2, Nat.zero_lt_succ (n + 1), snoc_last _ 2⟩

-- Lemma 5: Corner walks of length n+1 ending in 1
lemma Td_one_zero_one : Td 1 0 1 = 1 := by
  classical
  have h : (Finset.univ.filter (fun w : Fin 1 → Fin 4 =>
      topDist w 0 ∧ ∃ h : 0 < 1, w ⟨1 - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 1)) = {fun _ => 1} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, h1⟩
      funext ⟨i, hi⟩
      rcases Nat.le_zero.mp (Nat.lt_succ_iff.mp hi) with rfl
      exact h1
    · intro hw; subst hw
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, Nat.zero_lt_one, rfl⟩
      · intro ⟨i, hi⟩ j hj k hk
        rcases Nat.le_zero.mp (Nat.lt_succ_iff.mp hi) with rfl
        rcases Nat.le_zero.mp hj with rfl
        rw [smul_dir_one]; intro heq
        have := congrArg Prod.snd heq; simp [pos] at this; omega
      · intro i hi
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
        · left; intro j hj; rcases Nat.le_zero.mp hj with rfl; exact le_rfl
        · right; intro j hj
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
          · simp [pos, dir]
          · exact le_rfl
      · intro j hj
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
        · simp [pos, dir]
        · exact le_rfl
      · have hm : maxX (fun _ : Fin 1 => (1 : Fin 4)) = 0 := by
          apply le_antisymm
          · apply Finset.sup'_le; intro j hj
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) with rfl | rfl
            · simp [pos]
            · simp [pos, dir]
          · exact le_maxX _ (Nat.zero_le 1)
        rw [hm]; simp [pos, dir]
  simp only [Td]
  rw [h, Finset.card_singleton]
  norm_num

lemma Td_one_zero_succ (n : ℕ) : Td 1 0 (n + 1) = count n + T 1 n - Td 2 1 n := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    rw [Td_one_zero_one, ← T_zero_eq_count 0, T_zero_zero, T_pos_zero Nat.zero_lt_one, Td_zero_len]
    ring
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let A := Finset.univ.filter (fun w : Fin (n + 1) → Fin 4 => topDist w 0 ∧ w ⟨n, Nat.lt_succ_self n⟩ = 1)
  let A1 := A.filter (fun w => onTop (init w))
  let A2 := A.filter (fun w => ¬ onTop (init w))
  have hdisj : Disjoint A1 A2 := by
    rw [Finset.disjoint_filter]; intro w _ h1 h2; exact h2 h1
  have hunion : A = A1 ∪ A2 := by
    ext w; simp only [A1, A2, Finset.mem_union, Finset.mem_filter]; tauto
  have hTd_card : Td 1 0 (n + 1) = (A.card : ℤ) := by
    simp only [Td, A]
    congr 2; ext w; simp
  have hA1 : (A1.card : ℤ) = count n := by
    simp only [count]
    congr 1
    refine Finset.card_bij (fun w _ => init w) ?_ ?_ ?_
    · intro w hw
      simp only [A1, A, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rcases hw with ⟨⟨hw0, hlast⟩, htop_init⟩
      have hpos : pos w (n + 1) = pos w n + (0, 1) := by
        rw [pos_succ _ (Nat.lt_succ_self n), hlast, dir_one]
      have hright_init : onRight (init w) := by
        intro j hj
        rw [pos_init_le w hj, pos_init_le w le_rfl]
        have := (onRight_iff_maxX w).mpr (by simpa using hw0.2.2) j (Nat.le_succ_of_le hj)
        have : (pos w (n + 1)).1 = (pos w n).1 := by simp [hpos]
        omega
      exact (valid_iff_topDist_zero _).mpr ⟨prefValid_init hw0.1, htop_init, by simpa using (onRight_iff_maxX _).mp hright_init⟩
    · intro w1 hw1 w2 hw2 heq
      simp only [A1, A, Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
      rw [← snoc_init_last w1, ← snoc_init_last w2, hw1.1.2, hw2.1.2, heq]
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      have hutd := (valid_iff_topDist_zero u).mp hu
      refine ⟨snoc u 1, ?_, init_snoc u 1⟩
      simp only [A1, A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨topDist_snoc_one hutd, snoc_last u 1⟩, by simpa using hutd.2.1⟩
  have hA2 : (A2.card : ℤ) = T 1 n - Td 2 1 n := by
    have hcard : A2.card =
        (Finset.univ.filter (fun u : Fin n → Fin 4 =>
          topDist u 1 ∧ ¬ (∃ h : 0 < n, u ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 2))).card := by
      refine Finset.card_bij (fun w _ => reflW (init w)) ?_ ?_ ?_
      · intro w hw
        simp only [A2, A, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rcases hw with ⟨⟨hw0, hlast⟩, hnotTop⟩
        have hpos : pos w (n + 1) = pos w n + (0, 1) := by
          rw [pos_succ _ (Nat.lt_succ_self n), hlast, dir_one]
        have hright_init : onRight (init w) := by
          intro j hj
          rw [pos_init_le w hj, pos_init_le w le_rfl]
          have := (onRight_iff_maxX w).mpr (by simpa using hw0.2.2) j (Nat.le_succ_of_le hj)
          have : (pos w (n + 1)).1 = (pos w n).1 := by simp [hpos]
          omega
        have hmaxY_init : maxY (init w) = (pos (init w) n).2 + 1 := by
          apply le_antisymm
          · apply Finset.sup'_le; intro j hj
            have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            rw [pos_init_le w hjn, pos_init_le w le_rfl]
            have := hw0.2.1 j (Nat.le_succ_of_le hjn)
            have : (pos w (n + 1)).2 = (pos w n).2 + 1 := by simp [hpos]
            omega
          · simp only [onTop, not_forall, not_le] at hnotTop
            obtain ⟨j, hj, hgt⟩ := hnotTop
            have hle := le_maxY (init w) hj
            have : (pos (init w) j).2 ≤ (pos (init w) n).2 + 1 := by
              rw [pos_init_le w hj, pos_init_le w le_rfl]
              have := hw0.2.1 j (Nat.le_succ_of_le hj)
              have : (pos w (n + 1)).2 = (pos w n).2 + 1 := by simp [hpos]
              omega
            omega
        have hutd : topDist (reflW (init w)) 1 := by
          refine ⟨(prefValid_reflW _).mpr (prefValid_init hw0.1), (onTop_reflW _).mpr hright_init, ?_⟩
          rw [maxX_reflW, hmaxY_init, pos_reflW]
          simp
        refine ⟨hutd, ?_⟩
        intro ⟨_, h2⟩
        have hlt1 : n - 1 < n := Nat.sub_lt hn Nat.zero_lt_one
        have hlt2 : n - 1 < n + 1 := Nat.lt_succ_of_lt hlt1
        have h3 : w ⟨n - 1, hlt2⟩ = 3 := by
          have : reflD ((init w) ⟨n - 1, hlt1⟩) = 2 := h2
          have := congrArg reflD this
          rw [reflD_reflD] at this
          exact this
        have hstep := pos_succ w hlt2
        rw [Nat.sub_add_cancel hn, h3, dir_three] at hstep
        apply hw0.1.1 ⟨n, Nat.lt_succ_self n⟩ (n - 1) (Nat.sub_le n 1) 1 Nat.zero_lt_one
        rw [hlast, dir_one, one_smul]
        ext
        · have : (pos w n).1 = (pos w (n - 1)).1 := by simp [hstep]
          simp; omega
        · have : (pos w n).2 = (pos w (n - 1)).2 - 1 := by rw [hstep]; simp; ring
          simp; omega
      · intro w1 hw1 w2 hw2 heq
        simp only [A2, A, Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
        have hinit : init w1 = init w2 := by
          simpa using congrArg reflW heq
        rw [← snoc_init_last w1, ← snoc_init_last w2, hw1.1.2, hw2.1.2, hinit]
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        have hne2 : u ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ≠ 2 := fun h => hu.2 ⟨hn, h⟩
        have hutd0 := topDist_snoc_zero hu.1 hn hne2
        let w := snoc (reflW u) 1
        have hw_refl : w = reflW (snoc u 0) := by
          ext ⟨i, hi⟩
          by_cases h : i < n
          · simp [w, reflW, snoc, h]
          · have : i = n := by omega
            subst this; simp [w, reflW, snoc, reflD]
        have hw_td0 : topDist w 0 := by
          rw [hw_refl]
          exact (valid_iff_topDist_zero _).mp ((valid_reflW _).mpr ((valid_iff_topDist_zero _).mpr hutd0))
        have hw_nottop : ¬ onTop (init w) := by
          simp only [w, init_snoc, onTop_reflW, onRight_iff_maxX]
          have := hu.1.2.2
          omega
        refine ⟨w, ?_, ?_⟩
        · simp only [A2, A, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨hw_td0, snoc_last (reflW u) 1⟩, hw_nottop⟩
        · simp [w]
    have hsdiff :
        (Finset.univ.filter (fun u : Fin n → Fin 4 =>
          topDist u 1 ∧ ¬ (∃ h : 0 < n, u ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 2))).card +
        (Finset.univ.filter (fun u : Fin n → Fin 4 =>
          topDist u 1 ∧ ∃ h : 0 < n, u ⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = 2)).card =
        (Finset.univ.filter (fun u : Fin n → Fin 4 => topDist u 1)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      · rw [Finset.disjoint_filter]; intro u _ h1 h2; exact h1.2 h2.2
    simp only [T, Td] at hsdiff ⊢
    omega
  rw [hTd_card, hunion, Finset.card_union_of_disjoint hdisj]
  push_cast
  omega

-- PowerSeries step
noncomputable def T_ps (k : ℕ) : PowerSeries ℤ := PowerSeries.mk (T k)
noncomputable def T0_ps (k : ℕ) : PowerSeries ℤ := PowerSeries.mk (Td 0 k)
noncomputable def T1_ps (k : ℕ) : PowerSeries ℤ := PowerSeries.mk (Td 1 k)
noncomputable def T2_ps (k : ℕ) : PowerSeries ℤ := PowerSeries.mk (Td 2 k)

lemma coeff_two_mul (P : PowerSeries ℤ) (n : ℕ) : coeff n (2 * P) = 2 * coeff n P := by
  have h2 : (2 : PowerSeries ℤ) = PowerSeries.C 2 := rfl
  rw [h2, coeff_C_mul]

lemma coeff_X_mul_mk (g : ℕ → ℤ) (n : ℕ) : coeff (n + 1) (X * PowerSeries.mk g) = g n := by
  rw [← pow_one (X : PowerSeries ℤ), coeff_X_pow_mul, coeff_mk]

lemma coeff_X_mul (P : PowerSeries ℤ) (n : ℕ) : coeff (n + 1) (X * P) = coeff n P := by
  rw [← pow_one (X : PowerSeries ℤ), coeff_X_pow_mul]

lemma T_ps_zero : T_ps 0 = PowerSeries.mk count := by
  ext n; simp [T_ps, T_zero_eq_count]

lemma f_sub_one_eq_two_T1_zero :
    PowerSeries.mk count - 1 = 2 * T1_ps 0 := by
  ext n
  cases n with
  | zero =>
    have h0 : count 0 = 1 := by rw [← T_zero_eq_count 0, T_zero_zero]
    simp [T1_ps, Td_zero_len, coeff_zero_eq_constantCoeff_apply, h0]
  | succ n =>
    rw [map_sub, coeff_mk, coeff_one, if_neg (Nat.succ_ne_zero n), sub_zero, coeff_two_mul]
    rw [← T_zero_eq_count (n + 1), T_eq_sum_Td (Nat.zero_lt_succ n), Td_two_zero,
      Td_zero_eq_Td_one_at_zero (n + 1), add_zero]
    simp only [T1_ps, coeff_mk]
    ring

lemma T2_ps_one : T2_ps 1 = X + X ^ 2 * PowerSeries.mk count := by
  ext n
  rcases n with _ | _ | n
  · simp [T2_ps, Td_zero_len, coeff_zero_eq_constantCoeff_apply]
  · have h2 : coeff 1 (X ^ 2 * PowerSeries.mk count) = 0 :=
      X_pow_dvd_iff.mp (dvd_mul_right _ _) 1 (by omega)
    rw [map_add, h2, add_zero, coeff_X, if_pos rfl, T2_ps, coeff_mk, Td_two_one_one]
  · have h1 : coeff (n + 2) (X : PowerSeries ℤ) = 0 := by
      rw [coeff_X, if_neg (by omega)]
    rw [map_add, h1, zero_add, show n + 1 + 1 = n + 2 from rfl, coeff_X_pow_mul,
      T2_ps, coeff_mk, coeff_mk, Td_two_one_succ_succ n]

lemma T1_ps_zero :
    T1_ps 0 = X * PowerSeries.mk count + X * T_ps 1 - X * T2_ps 1 := by
  ext n
  cases n with
  | zero =>
    simp [T1_ps, Td_zero_len, coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [map_sub, map_add, coeff_X_mul, coeff_X_mul, coeff_X_mul]
    simp only [T1_ps, T_ps, T2_ps, coeff_mk]
    exact Td_one_zero_succ n

lemma T_ps_split {k : ℕ} (hk : 0 < k) :
    T_ps k = T0_ps k + T1_ps k + T2_ps k := by
  ext n
  cases n with
  | zero =>
    simp [T_ps, T0_ps, T1_ps, T2_ps, T_pos_zero hk, Td_zero_len]
  | succ n =>
    simp only [map_add, T_ps, T0_ps, T1_ps, T2_ps, coeff_mk]
    exact T_eq_sum_Td (Nat.zero_lt_succ n)

lemma T1_ps_eq {k : ℕ} (hk : 0 < k) : T1_ps k = X * T_ps k := by
  ext n
  cases n with
  | zero => simp [T1_ps, Td_zero_len, coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [coeff_X_mul]
    simp only [T1_ps, T_ps, coeff_mk]
    exact Td_one_succ hk

lemma T0_ps_eq {k : ℕ} (hk : 0 < k) :
    T0_ps k = X * (T_ps (k + 1) - T2_ps (k + 1)) := by
  ext n
  cases n with
  | zero => simp [T0_ps, Td_zero_len, coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [coeff_X_mul, map_sub]
    simp only [T0_ps, T_ps, T2_ps, coeff_mk]
    exact Td_zero_succ hk

lemma T2_ps_eq {k : ℕ} (hk : 2 ≤ k) :
    T2_ps k = X * (T_ps (k - 1) - T0_ps (k - 1)) := by
  ext n
  cases n with
  | zero => simp [T2_ps, Td_zero_len, coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [coeff_X_mul, map_sub]
    simp only [T2_ps, T_ps, T0_ps, coeff_mk]
    exact Td_two_succ_ge_two hk

lemma T_ps_recurrence {k : ℕ} (hk : 2 ≤ k) :
    X * T_ps (k + 1) + (-X ^ 3 - X ^ 2 + X - 1) * T_ps k + X * T_ps (k - 1) = 0 := by
  have h1 : T_ps k = T0_ps k + T1_ps k + T2_ps k := T_ps_split (by omega)
  have hT1 : T1_ps k = X * T_ps k := T1_ps_eq (by omega)
  have hT0 : T0_ps k = X * (T_ps (k + 1) - T2_ps (k + 1)) := T0_ps_eq (by omega)
  have hT2 : T2_ps k = X * (T_ps (k - 1) - T0_ps (k - 1)) := T2_ps_eq hk
  have hT2_next : T2_ps (k + 1) = X * (T_ps k - T0_ps k) := by
    simpa using T2_ps_eq (k := k + 1) (by omega)
  have hT0_prev : T0_ps (k - 1) = X * (T_ps k - T2_ps k) := by
    have := T0_ps_eq (k := k - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ k)] at this
  have hsum02 : T0_ps k + T2_ps k = (1 - X) * T_ps k := by linear_combination -h1 - hT1
  calc
    X * T_ps (k + 1) + (-X ^ 3 - X ^ 2 + X - 1) * T_ps k + X * T_ps (k - 1)
      = (T0_ps k + X * T2_ps (k + 1)) + (-X ^ 3 - X ^ 2 + X - 1) * T_ps k +
          (T2_ps k + X * T0_ps (k - 1)) := by rw [hT0, hT2]; ring
    _ = (T0_ps k + T2_ps k) + X ^ 2 * (2 * T_ps k - (T0_ps k + T2_ps k)) +
          (-X ^ 3 - X ^ 2 + X - 1) * T_ps k := by rw [hT2_next, hT0_prev]; ring
    _ = 0 := by rw [hsum02]; ring

lemma T_ps_boundary_two :
    2 * (X * T_ps 2 + (-X ^ 3 - X ^ 2 + X - 1) * T_ps 1 + X * T_ps 0) =
      X * (PowerSeries.mk count - 1) := by
  let f := PowerSeries.mk count
  have h1 : T_ps 1 = T0_ps 1 + T1_ps 1 + T2_ps 1 := T_ps_split Nat.zero_lt_one
  have hT1 : T1_ps 1 = X * T_ps 1 := T1_ps_eq Nat.zero_lt_one
  have hT0 : T0_ps 1 = X * (T_ps 2 - T2_ps 2) := T0_ps_eq Nat.zero_lt_one
  have hT2_2 : T2_ps 2 = X * (T_ps 1 - T0_ps 1) := by simpa using T2_ps_eq (k := 2) le_rfl
  have hT2_1 : T2_ps 1 = X + X ^ 2 * f := T2_ps_one
  have hT1_0 : T1_ps 0 = X * f + X * T_ps 1 - X * T2_ps 1 := T1_ps_zero
  have hf : f - 1 = 2 * T1_ps 0 := f_sub_one_eq_two_T1_zero
  have hT0_0 : T_ps 0 = f := T_ps_zero
  have h01 : T0_ps 1 = (1 - X) * T_ps 1 - T2_ps 1 := by linear_combination -h1 - hT1
  have hX2 : X * T_ps 2 = (1 - X + X ^ 3) * T_ps 1 - (1 - X ^ 2) * T2_ps 1 := by
    calc
      X * T_ps 2 = T0_ps 1 + X * T2_ps 2 := by rw [hT0]; ring
      _ = T0_ps 1 + X ^ 2 * (T_ps 1 - T0_ps 1) := by rw [hT2_2]; ring
      _ = (1 - X + X ^ 3) * T_ps 1 - (1 - X ^ 2) * T2_ps 1 := by rw [h01]; ring
  have h2T1 : 2 * X * T_ps 1 = (2 * X ^ 3 - 2 * X + 1) * f + 2 * X ^ 2 - 1 := by
    calc
      2 * X * T_ps 1 = 2 * T1_ps 0 - 2 * X * f + 2 * X * T2_ps 1 := by rw [hT1_0]; ring
      _ = (f - 1) - 2 * X * f + 2 * X * (X + X ^ 2 * f) := by rw [← hf, hT2_1]
      _ = (2 * X ^ 3 - 2 * X + 1) * f + 2 * X ^ 2 - 1 := by ring
  calc
    2 * (X * T_ps 2 + (-X ^ 3 - X ^ 2 + X - 1) * T_ps 1 + X * T_ps 0)
      = 2 * ((1 - X + X ^ 3) * T_ps 1 - (1 - X ^ 2) * T2_ps 1 +
          (-X ^ 3 - X ^ 2 + X - 1) * T_ps 1 + X * f) := by rw [hX2, hT0_0]
    _ = -X * (2 * X * T_ps 1) - 2 * (1 - X ^ 2) * (X + X ^ 2 * f) + 2 * X * f := by
          rw [hT2_1]; ring
    _ = X * (f - 1) := by rw [h2T1]; ring

lemma T_ps_boundary_one :
    2 * ((-X ^ 3 - X ^ 2 + X - 1) * T_ps 0 + X * T_ps 1) =
      -(2 * X ^ 2 + 1) * PowerSeries.mk count + 2 * X ^ 2 - 1 := by
  let f := PowerSeries.mk count
  have hT2_1 : T2_ps 1 = X + X ^ 2 * f := T2_ps_one
  have hT1_0 : T1_ps 0 = X * f + X * T_ps 1 - X * T2_ps 1 := T1_ps_zero
  have hf : f - 1 = 2 * T1_ps 0 := f_sub_one_eq_two_T1_zero
  have hT0_0 : T_ps 0 = f := T_ps_zero
  have h2T1 : 2 * X * T_ps 1 = (2 * X ^ 3 - 2 * X + 1) * f + 2 * X ^ 2 - 1 := by
    calc
      2 * X * T_ps 1 = 2 * T1_ps 0 - 2 * X * f + 2 * X * T2_ps 1 := by rw [hT1_0]; ring
      _ = (f - 1) - 2 * X * f + 2 * X * (X + X ^ 2 * f) := by rw [← hf, hT2_1]
      _ = (2 * X ^ 3 - 2 * X + 1) * f + 2 * X ^ 2 - 1 := by ring
  calc
    2 * ((-X ^ 3 - X ^ 2 + X - 1) * T_ps 0 + X * T_ps 1)
      = 2 * (-X ^ 3 - X ^ 2 + X - 1) * f + (2 * X * T_ps 1) := by rw [hT0_0]; ring
    _ = -(2 * X ^ 2 + 1) * f + 2 * X ^ 2 - 1 := by rw [h2T1]; ring

end A191625H2

theorem OMA.solution : OMA.R_oeis_a191625_R1.H2 := by
  intro u hu0 hu
  let t : PowerSeries ℤ := X
  let f := PowerSeries.mk count
  let b : PowerSeries ℤ := -t ^ 3 - t ^ 2 + t - 1
  let K : PowerSeries ℤ := t * u ^ 2 + b * u + t
  have hK : K = 0 := hu
  have hMain : 2 * t * f + (-(2 * t ^ 2 + 1) * f + 2 * t ^ 2 - 1) * u + t * (f - 1) * u ^ 2 = 0 := by
    ext N
    rw [map_zero]
    let M := N + 2
    let S := ∑ k ∈ Finset.range (M + 1), A191625H2.T_ps k * u ^ k
    have hKS : 2 * (K * S) = 0 := by rw [hK, zero_mul, mul_zero]
    have hsum_K : K * S =
        t * A191625H2.T_ps 0 +
        (b * A191625H2.T_ps 0 + t * A191625H2.T_ps 1) * u +
        (t * A191625H2.T_ps 0 + b * A191625H2.T_ps 1 + t * A191625H2.T_ps 2) * u ^ 2 +
        (∑ k ∈ Finset.range (M - 2),
          (t * A191625H2.T_ps (k + 1) + b * A191625H2.T_ps (k + 2) + t * A191625H2.T_ps (k + 3)) * u ^ (k + 3)) +
        ((t * A191625H2.T_ps (M - 1) + b * A191625H2.T_ps M) + t * A191625H2.T_ps M * u) * u ^ (M + 1) := by
      have hM : M = N + 2 := rfl
      have h0 : S = A191625H2.T_ps 0 + A191625H2.T_ps 1 * u +
          ∑ k ∈ Finset.range (M - 1), A191625H2.T_ps (k + 2) * u ^ (k + 2) := by
        simp only [S, hM]
        rw [Finset.sum_range_succ', Finset.sum_range_succ', show N + 2 - 1 = N + 1 by omega]
        simp only [pow_zero, mul_one]
        ring
      have h1 : u * S = A191625H2.T_ps 0 * u +
          (∑ k ∈ Finset.range (M - 1), A191625H2.T_ps (k + 1) * u ^ (k + 2)) +
          A191625H2.T_ps M * u ^ (M + 1) := by
        simp only [S, hM, Finset.mul_sum]
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have hstep : ∑ x ∈ Finset.range (N + 1), u * (A191625H2.T_ps (x + 1) * u ^ (x + 1)) =
            ∑ x ∈ Finset.range (N + 1), A191625H2.T_ps (x + 1) * u ^ (x + 2) := by
          refine Finset.sum_congr rfl (fun x _ => by ring)
        rw [hstep, show N + 2 - 1 = N + 1 by omega]
        simp only [pow_zero, mul_one]
        ring
      have h2 : u ^ 2 * S =
          (∑ k ∈ Finset.range (M - 1), A191625H2.T_ps k * u ^ (k + 2)) +
          A191625H2.T_ps (M - 1) * u ^ (M + 1) + A191625H2.T_ps M * u ^ (M + 2) := by
        simp only [S, hM, Finset.mul_sum]
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hstep : ∑ x ∈ Finset.range (N + 1), u ^ 2 * (A191625H2.T_ps x * u ^ x) =
            ∑ x ∈ Finset.range (N + 1), A191625H2.T_ps x * u ^ (x + 2) := by
          refine Finset.sum_congr rfl (fun x _ => by ring)
        rw [hstep, show N + 2 - 1 = N + 1 by omega]
        ring
      have hsplit2 : ∀ (g : ℕ → PowerSeries ℤ),
          ∑ k ∈ Finset.range (M - 1), g k = g 0 + ∑ k ∈ Finset.range (M - 2), g (k + 1) := by
        intro g
        rw [hM, show N + 2 - 1 = (N + 2 - 2) + 1 by omega, Finset.sum_range_succ']
        ring
      have hcomb :
          t * (∑ k ∈ Finset.range (M - 2), A191625H2.T_ps (k + 1) * u ^ (k + 3)) +
          b * (∑ k ∈ Finset.range (M - 2), A191625H2.T_ps (k + 2) * u ^ (k + 3)) +
          t * (∑ k ∈ Finset.range (M - 2), A191625H2.T_ps (k + 3) * u ^ (k + 3)) =
          ∑ k ∈ Finset.range (M - 2),
            (t * A191625H2.T_ps (k + 1) + b * A191625H2.T_ps (k + 2) + t * A191625H2.T_ps (k + 3)) * u ^ (k + 3) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => by ring)
      calc
        K * S = t * (u ^ 2 * S) + b * (u * S) + t * S := by dsimp [K]; ring
        _ = t * ((∑ k ∈ Finset.range (M - 1), A191625H2.T_ps k * u ^ (k + 2)) +
              A191625H2.T_ps (M - 1) * u ^ (M + 1) + A191625H2.T_ps M * u ^ (M + 2)) +
            b * (A191625H2.T_ps 0 * u +
              (∑ k ∈ Finset.range (M - 1), A191625H2.T_ps (k + 1) * u ^ (k + 2)) +
              A191625H2.T_ps M * u ^ (M + 1)) +
            t * (A191625H2.T_ps 0 + A191625H2.T_ps 1 * u +
              ∑ k ∈ Finset.range (M - 1), A191625H2.T_ps (k + 2) * u ^ (k + 2)) := by rw [h2, h1, h0]
        _ = (t * A191625H2.T_ps 0 +
              (b * A191625H2.T_ps 0 + t * A191625H2.T_ps 1) * u +
              (t * A191625H2.T_ps 0 + b * A191625H2.T_ps 1 + t * A191625H2.T_ps 2) * u ^ 2) +
            (t * ∑ k ∈ Finset.range (M - 2), A191625H2.T_ps (k + 1) * u ^ (k + 3) +
             b * ∑ k ∈ Finset.range (M - 2), A191625H2.T_ps (k + 2) * u ^ (k + 3) +
             t * ∑ k ∈ Finset.range (M - 2), A191625H2.T_ps (k + 3) * u ^ (k + 3)) +
            ((t * A191625H2.T_ps (M - 1) + b * A191625H2.T_ps M) + t * A191625H2.T_ps M * u) * u ^ (M + 1) := by
            have hs0 : ∑ k ∈ Finset.range (M - 1), A191625H2.T_ps k * u ^ (k + 2) =
                A191625H2.T_ps 0 * u ^ 2 +
                  ∑ k ∈ Finset.range (M - 2), A191625H2.T_ps (k + 1) * u ^ (k + 3) := by
              rw [hsplit2 (fun k => A191625H2.T_ps k * u ^ (k + 2))]
            have hs1 : ∑ k ∈ Finset.range (M - 1), A191625H2.T_ps (k + 1) * u ^ (k + 2) =
                A191625H2.T_ps 1 * u ^ 2 +
                  ∑ k ∈ Finset.range (M - 2), A191625H2.T_ps (k + 2) * u ^ (k + 3) := by
              rw [hsplit2 (fun k => A191625H2.T_ps (k + 1) * u ^ (k + 2))]
            have hs2 : ∑ k ∈ Finset.range (M - 1), A191625H2.T_ps (k + 2) * u ^ (k + 2) =
                A191625H2.T_ps 2 * u ^ 2 +
                  ∑ k ∈ Finset.range (M - 2), A191625H2.T_ps (k + 3) * u ^ (k + 3) := by
              rw [hsplit2 (fun k => A191625H2.T_ps (k + 2) * u ^ (k + 2))]
            rw [hs0, hs1, hs2]
            ring
        _ = _ := by
            rw [hcomb]
    have hrec_zero :
        ∑ k ∈ Finset.range (M - 2),
          (t * A191625H2.T_ps (k + 1) + b * A191625H2.T_ps (k + 2) + t * A191625H2.T_ps (k + 3)) * u ^ (k + 3) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hr := A191625H2.T_ps_recurrence (k := k + 2) (by omega)
      rw [show k + 2 + 1 = k + 3 by omega, show k + 2 - 1 = k + 1 by omega] at hr
      have hr' : t * A191625H2.T_ps (k + 1) + b * A191625H2.T_ps (k + 2) + t * A191625H2.T_ps (k + 3) = 0 := by
        dsimp [t, b]
        linear_combination hr
      rw [hr', zero_mul]
    rw [hsum_K, hrec_zero, add_zero] at hKS
    have hdvd : t ^ (M + 1) ∣ u ^ (M + 1) := by
      have hXu : t ∣ u := X_dvd_iff.mpr hu0
      exact pow_dvd_pow_of_dvd hXu (M + 1)
    have hc_tail : coeff N (2 * (((t * A191625H2.T_ps (M - 1) + b * A191625H2.T_ps M) +
        t * A191625H2.T_ps M * u) * u ^ (M + 1))) = 0 := by
      apply X_pow_dvd_iff.mp _ N (by omega : N < M + 1)
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hdvd _) _
    have hcongr := congrArg (coeff N) hKS
    rw [mul_add, map_add, hc_tail, add_zero, map_zero] at hcongr
    have heq_main :
        2 * (t * A191625H2.T_ps 0 +
          (b * A191625H2.T_ps 0 + t * A191625H2.T_ps 1) * u +
          (t * A191625H2.T_ps 0 + b * A191625H2.T_ps 1 + t * A191625H2.T_ps 2) * u ^ 2) =
        2 * t * f + (-(2 * t ^ 2 + 1) * f + 2 * t ^ 2 - 1) * u + t * (f - 1) * u ^ 2 := by
      have hb0 := A191625H2.T_ps_zero
      have hb1 := A191625H2.T_ps_boundary_one
      have hb2 := A191625H2.T_ps_boundary_two
      dsimp [t, b, f]
      linear_combination 2 * t * hb0 + u * hb1 + u ^ 2 * hb2
    rwa [heq_main] at hcongr
  dsimp only [t, f] at hMain
  linear_combination hMain + 2 * hu
