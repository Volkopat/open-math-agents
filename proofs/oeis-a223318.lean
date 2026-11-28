import OMAStatements.S_oeis_a223318

namespace OMA.S_oeis_a223318

open PowerSeries Finset









/-- Rows valid and consecutive rows compatible. -/
def Valid {n : ℕ} (f : Fin n → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : Prop :=
  (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12)).filter (fun f => Valid f ∧ f 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (g : Fin (n + 1) → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) ↔
      hrow x ∧ ok x (g 0) ∧ Valid g := by
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨by simpa using hr 0, ?_, fun i => by simpa using hr i.succ, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨hx, h0, hg, hgo⟩
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hx
      | succ i => simpa using hg i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          have hj : j = 0 := by ext; simp at hij; omega
          subst hj
          simpa using h0
      | succ i =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          simp only [Fin.cons_succ]
          exact hgo i j (by simp at hij; omega)

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12, if r.1 = 0 then W n r else 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs with hr
  · congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2, _⟩, h4⟩
      exact ⟨⟨h1, h2⟩, h4⟩
    · rintro ⟨⟨h1, h2⟩, h4⟩
      refine ⟨⟨h1, h2, fun i hi => ?_⟩, h4⟩
      have : i = 0 := Fin.ext hi
      rw [this, h4, hr]
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨_, _, h3⟩, h4⟩
    exact hr (h4 ▸ h3 0 rfl)

lemma W_zero (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : W 0 r = if hrow r then 1 else 0 := by
  unfold W
  split_ifs with hr
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => r, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hf⟩
      funext i
      rw [Fin.fin_one_eq_zero i, hf]
    · rintro rfl
      refine ⟨⟨fun _ => hr, ?_⟩, rfl⟩
      intro i j hij
      have := j.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨h1, _⟩, h0⟩
    exact hr (h0 ▸ h1 0)

/-- Prepending the row r to an array with n + 1 rows. -/
def consEmb (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) :
    (Fin (n + 1) → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) ↪ (Fin (n + 2) → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (g : Fin (n + 1) → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) :
    W (n + 1) r = ∑ s : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12, if hrow r ∧ ok r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12)).filter
      (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12)).filter
        (fun g => (hrow r ∧ ok r (g 0)) ∧ Valid g)).map (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, ⟨⟨h1, h2⟩, hg⟩, rfl⟩
      exact ⟨(valid_cons r g).2 ⟨h1, h2, hg⟩, by simp⟩
  unfold W
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs with hrs
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨⟨hrs.1, h0 ▸ hrs.2⟩, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨h1, h2⟩, _⟩, h0⟩
    exact hrs ⟨h1, h0 ▸ h2⟩

/-- The adjacency as one bit mask: y is adjacent to x when bit 12 x + y of `MASK` is set. -/
def MASK : ℕ := 9281011236766377541118938259142207560274150

/-- Fast adjacency. -/
def adjB (x y : Fin 12) : Bool := Nat.testBit MASK (12 * x.val + y.val)

set_option maxHeartbeats 4000000 in
lemma adj_iff : ∀ x y : Fin 12, adj x y ↔ adjB x y = true := by
  decide +kernel

/-- Fast row test. -/
def hrowB (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : Bool := adjB r.1 r.2.1 && (adjB r.2.1 r.2.2.1 && (adjB r.2.2.1 r.2.2.2.1 && (adjB r.2.2.2.1 r.2.2.2.2)))

/-- Fast compatibility test. -/
def okB (r s : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : Bool :=
  adjB r.2.1 s.1 && (adjB r.2.2.1 s.2.1 && (adjB r.2.2.2.1 s.2.2.1 && (adjB r.2.2.2.2 s.2.2.2.1)))

lemma hrow_iff (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : hrow r ↔ hrowB r = true := by
  simp only [hrow, hrowB, adj_iff, Bool.and_eq_true]

lemma ok_iff (r s : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : ok r s ↔ okB r s = true := by
  simp only [ok, okB, adj_iff, Bool.and_eq_true]

lemma W_invalid (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (h : hrowB r = false) : W n r = 0 := by
  unfold W
  rw [Finset.card_eq_zero]
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨⟨h1, _⟩, h0⟩
  have h2 := (hrow_iff r).1 (h0 ▸ h1 0)
  rw [h] at h2
  exact Bool.false_ne_true h2

lemma W_zeroB (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : W 0 r = if hrowB r = true then 1 else 0 := by
  rw [W_zero]
  by_cases hr : hrowB r = true
  · rw [if_pos hr, if_pos ((hrow_iff r).2 hr)]
  · rw [if_neg hr, if_neg (fun h => hr ((hrow_iff r).1 h))]

/-- The labels adjacent to c, listed. -/
def NL : Fin 12 → List (Fin 12) :=
  ![[1, 2, 5, 6, 7], [0, 2, 3, 7, 8], [0, 1, 4, 6, 8], [1, 7, 8, 9, 11], [2, 6, 8, 9, 10],
    [0, 6, 7, 10, 11], [0, 2, 4, 5, 10], [0, 1, 3, 5, 11], [1, 2, 3, 4, 9], [3, 4, 8, 10, 11],
    [4, 5, 6, 9, 11], [3, 5, 7, 9, 10]]

lemma NL_nodup : ∀ c : Fin 12, (NL c).Nodup := by
  decide +kernel

/-- The labels adjacent to c. -/
def N (c : Fin 12) : Finset (Fin 12) := ⟨NL c, NL_nodup c⟩

set_option maxHeartbeats 4000000 in
lemma N_eq : ∀ c : Fin 12, N c = univ.filter (fun y => adjB c y = true) := by
  decide +kernel

lemma sum_N (c : Fin 12) (F : Fin 12 → ℕ) :
    ∑ y ∈ N c, F y = ∑ y : Fin 12, if adjB c y = true then F y else 0 := by
  rw [N_eq, Finset.sum_filter]

lemma ite_and (b1 b2 : Bool) (X : ℕ) :
    (if b1 = true then (if b2 = true then X else 0) else 0) = if (b1 && b2) = true then X else 0 := by
  cases b1 <;> cases b2 <;> rfl

/-- The sum of g over the valid rows allowed below r, enumerated entry by entry: each entry runs
over the neighbors of one entry (of r or of the row being built), and the other conditions on it
are tested. -/
def succSum (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (g : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 → ℕ) : ℕ :=
  ∑ x ∈ N r.2.1, ∑ y ∈ N x, (if adjB r.2.2.1 y = true then ∑ z ∈ N y, (if adjB r.2.2.2.1 z = true then ∑ u ∈ N z, (if adjB r.2.2.2.2 u = true then ∑ v ∈ N u, g (x, y, z, u, v) else 0) else 0) else 0)

lemma cond_split (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (x y z u v : Fin 12) :
    (okB r (x, y, z, u, v) && hrowB (x, y, z, u, v)) = (adjB r.2.1 x && ((adjB x y && (adjB r.2.2.1 y)) && ((adjB y z && (adjB r.2.2.2.1 z)) && ((adjB z u && (adjB r.2.2.2.2 u)) && (adjB u v))))) := by
  simp only [okB, hrowB]
  generalize adjB r.2.1 x = b0
  generalize adjB r.2.2.1 y = b1
  generalize adjB r.2.2.2.1 z = b2
  generalize adjB r.2.2.2.2 u = b3
  generalize adjB x y = b4
  generalize adjB y z = b5
  generalize adjB z u = b6
  generalize adjB u v = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide

lemma succ_eq (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (hr : hrowB r = true) (g : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 → ℕ)
    (hg : ∀ s, hrowB s = false → g s = 0) :
    (∑ s : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12, if hrow r ∧ ok r s then g s else 0) = succSum r g := by
  have e1 : ∀ s : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12, (if hrow r ∧ ok r s then g s else 0) =
      if (okB r s && hrowB s) = true then g s else 0 := by
    intro s
    by_cases hs : hrowB s = true
    · simp [hrow_iff, ok_iff, hr, hs]
    · have h0 : g s = 0 := hg s (by simpa using hs)
      simp [h0]
  rw [Finset.sum_congr rfl (fun s _ => e1 s)]
  simp only [Fintype.sum_prod_type]
  unfold succSum
  simp only [sum_N, ite_and]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h0 : adjB r.2.1 x = true
  · rw [if_pos h0]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h1 : (adjB x y && (adjB r.2.2.1 y)) = true
    · rw [if_pos h1]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      by_cases h2 : (adjB y z && (adjB r.2.2.2.1 z)) = true
      · rw [if_pos h2]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        by_cases h3 : (adjB z u && (adjB r.2.2.2.2 u)) = true
        · rw [if_pos h3]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          by_cases h4 : adjB u v = true
          · rw [if_pos h4]
            simp [cond_split, h0, h1, h2, h3, h4]
          · rw [if_neg h4]
            simp [cond_split, h0, h1, h2, h3, h4]
        · rw [if_neg h3]
          refine Finset.sum_eq_zero (fun v _ => ?_)
          simp [cond_split, h0, h1, h2, h3]
      · rw [if_neg h2]
        refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))
        simp [cond_split, h0, h1, h2]
    · rw [if_neg h1]
      refine Finset.sum_eq_zero (fun z _ => Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_)))
      simp [cond_split, h0, h1]
  · rw [if_neg h0]
    refine Finset.sum_eq_zero (fun y _ => Finset.sum_eq_zero (fun z _ => Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))))
    simp [cond_split, h0]

/-- For each arc (x, y) of the graph an automorphism taking x to 0 and y to 1 (the identity when
x and y are not adjacent), as a word in base 16: digit v of `PW x y` is the image of v. -/
def PW : Fin 12 → Fin 12 → ℕ :=
  ![![205163983024656, 205163983024656, 188671056888096, 205163983024656, 205163983024656, 62235990079056, 79832186857296, 65507201549856, 205163983024656, 205163983024656, 205163983024656, 205163983024656],
    ![204124632404481, 205163983024656, 186605193351426, 63232567154181, 205163983024656, 205163983024656, 205163983024656, 63449896482306, 80820205463301, 205163983024656, 205163983024656, 205163983024656],
    ![171139535290401, 170113022373906, 205163983024656, 205163983024656, 162189368442981, 205163983024656, 162406697771106, 205163983024656, 163284835774581, 205163983024656, 205163983024656, 205163983024656],
    ![205163983024656, 99378995136531, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 40016638774131, 100542661724196, 44081015360346, 205163983024656, 21393929079396],
    ![205163983024656, 205163983024656, 181842870288771, 205163983024656, 205163983024656, 205163983024656, 73004000257971, 205163983024656, 199499463012996, 60552960312906, 54381038843556, 205163983024656],
    ![95285762373681, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 96453708195906, 129437799167106, 205163983024656, 205163983024656, 36874022505381, 20381599808181],
    ![77702403299121, 205163983024656, 182189298258306, 205163983024656, 73133098899381, 61274152343106, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 54445965743781, 205163983024656],
    ![100759991052321, 99724919666706, 205163983024656, 40145233976181, 205163983024656, 127242836989026, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 21457849100901],
    ![205163983024656, 81778519123731, 180735320412531, 65354547402276, 197296445805156, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 61644400129626, 205163983024656, 205163983024656],
    ![205163983024656, 205163983024656, 205163983024656, 41813826411321, 95668847863881, 205163983024656, 205163983024656, 205163983024656, 94565325502521, 205163983024656, 124273674048681, 25316872759881],
    ![205163983024656, 205163983024656, 205163983024656, 205163983024656, 88457575774356, 35641904941971, 88393404033171, 205163983024656, 205163983024656, 123251440366746, 205163983024656, 18122717608596],
    ![205163983024656, 205163983024656, 205163983024656, 5992191039876, 205163983024656, 2656304388531, 205163983024656, 5927515859331, 205163983024656, 7801461221706, 1629539752356, 205163983024656]]

/-- The inverse permutations, as words in the same way. -/
def QW : Fin 12 → Fin 12 → ℕ :=
  ![![205163983024656, 205163983024656, 188671056888096, 205163983024656, 205163983024656, 62235990079056, 144698104300896, 180952649740656, 205163983024656, 205163983024656, 205163983024656, 205163983024656],
    ![204124632404481, 205163983024656, 171139535290401, 95285762373681, 205163983024656, 205163983024656, 205163983024656, 163437238202481, 111777178928001, 205163983024656, 205163983024656, 205163983024656],
    ![186605193351426, 170113022373906, 205163983024656, 205163983024656, 96453708195906, 205163983024656, 162406697771106, 205163983024656, 129437799167106, 205163983024656, 205163983024656, 205163983024656],
    ![205163983024656, 99378995136531, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 40016638774131, 181842870288771, 35641904941971, 205163983024656, 73004000257971],
    ![205163983024656, 205163983024656, 100542661724196, 205163983024656, 205163983024656, 205163983024656, 21393929079396, 205163983024656, 199499463012996, 88457575774356, 54381038843556, 205163983024656],
    ![63232567154181, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 162189368442981, 163284835774581, 205163983024656, 205163983024656, 36874022505381, 20381599808181],
    ![150870025770246, 205163983024656, 170635924308006, 205163983024656, 25534202088006, 167364712837206, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 124491003376806, 205163983024656],
    ![186102337528071, 169609159671831, 205163983024656, 42095327480631, 205163983024656, 167429388017751, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 108067031655351],
    ![205163983024656, 116922587480856, 135609720636456, 182895046078776, 201582430954056, 205163983024656, 205163983024656, 205163983024656, 205163983024656, 123532689716376, 205163983024656, 205163983024656],
    ![205163983024656, 205163983024656, 205163983024656, 41813826411321, 95668847863881, 205163983024656, 205163983024656, 205163983024656, 128652435395721, 205163983024656, 124273674048681, 107785027146681],
    ![205163983024656, 205163983024656, 205163983024656, 205163983024656, 60552960312906, 44081015360346, 126522651837546, 205163983024656, 205163983024656, 123251440366746, 205163983024656, 143037816649146],
    ![205163983024656, 205163983024656, 205163983024656, 77110058190651, 205163983024656, 26553521277531, 205163983024656, 110094400881531, 205163983024656, 105727722079131, 142002745263531, 205163983024656]]

/-- The automorphism chosen for (x, y). -/
def P (x y v : Fin 12) : Fin 12 :=
  ⟨PW x y >>> (4 * v.val) % 16 % 12, Nat.mod_lt _ (by norm_num)⟩

/-- Its inverse. -/
def Q (x y v : Fin 12) : Fin 12 :=
  ⟨QW x y >>> (4 * v.val) % 16 % 12, Nat.mod_lt _ (by norm_num)⟩

set_option maxHeartbeats 4000000 in
lemma QP : ∀ x y v : Fin 12, Q x y (P x y v) = v := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma PQ : ∀ x y v : Fin 12, P x y (Q x y v) = v := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma P_adj : ∀ x y : Fin 12, adjB x y = true →
    ∀ v w : Fin 12, adjB (P x y v) (P x y w) = adjB v w := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma P_arc : ∀ x y : Fin 12, adjB x y = true → P x y x = 0 ∧ P x y y = 1 := by
  decide +kernel

/-- The automorphism chosen for (x, y), applied to every entry of a row. -/
def rot (x y : Fin 12) : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 ≃ Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 where
  toFun r := (P x y r.1, P x y r.2.1, P x y r.2.2.1, P x y r.2.2.2.1, P x y r.2.2.2.2)
  invFun r := (Q x y r.1, Q x y r.2.1, Q x y r.2.2.1, Q x y r.2.2.2.1, Q x y r.2.2.2.2)
  left_inv r := by simp [QP]
  right_inv r := by simp [PQ]

lemma hrow_rot (x y : Fin 12) (hxy : adjB x y = true) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : hrow (rot x y r) ↔ hrow r := by
  simp only [hrow_iff, hrowB, rot, Equiv.coe_fn_mk, P_adj x y hxy]

lemma ok_rot (x y : Fin 12) (hxy : adjB x y = true) (r s : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) :
    ok (rot x y r) (rot x y s) ↔ ok r s := by
  simp only [ok_iff, okB, rot, Equiv.coe_fn_mk, P_adj x y hxy]

/-- An equivalence of rows that preserves both conditions preserves the counts W(n, r). -/
lemma W_equiv (σ : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 ≃ Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (hh : ∀ r, hrow (σ r) ↔ hrow r)
    (ho : ∀ r s, ok (σ r) (σ s) ↔ ok r s) (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : W n (σ r) = W n r := by
  have hv : ∀ {m : ℕ} (f : Fin m → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12), Valid (fun i => σ (f i)) ↔ Valid f := by
    intro m f
    unfold Valid
    simp only [hh, ho]
  unfold W
  refine Finset.card_bij' (fun f _ => fun i => σ.symm (f i)) (fun f _ => fun i => σ (f i))
    ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    refine ⟨?_, by rw [hf.2]; simp⟩
    rw [← hv]
    simpa using hf.1
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact ⟨(hv f).2 hf.1, by rw [hf.2]⟩
  · intro f _
    funext i
    simp
  · intro f _
    funext i
    simp

/-- The normal form of a row: the automorphism chosen for its first two entries, applied to it. -/
def nrm (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 := rot r.1 r.2.1 r

lemma adj01 (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (hr : hrowB r = true) : adjB r.1 r.2.1 = true := by
  simp only [hrowB, Bool.and_eq_true] at hr
  exact hr.1

lemma W_nrm (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (hr : hrowB r = true) : W n (nrm r) = W n r :=
  W_equiv (rot r.1 r.2.1) (hrow_rot _ _ (adj01 r hr)) (ok_rot _ _ (adj01 r hr)) n r

lemma hrowB01 (z u v : Fin 12) (h1 : adjB 1 z = true) (h2 : adjB z u = true) (h3 : adjB u v = true) :
    hrowB (0, 1, z, u, v) = true := by
  have h0 : adjB 0 1 = true := by decide +kernel
  simp only [hrowB, h0, h1, h2, h3, Bool.and_self]

lemma nrm_spec (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (hr : hrowB r = true) : ∃ z u v : Fin 12,
    nrm r = (0, 1, z, u, v) ∧ adjB 1 z = true ∧ adjB z u = true ∧ adjB u v = true := by
  obtain ⟨e0, e1⟩ := P_arc r.1 r.2.1 (adj01 r hr)
  have hv : hrowB (nrm r) = true :=
    (hrow_iff _).1 ((hrow_rot _ _ (adj01 r hr) r).2 ((hrow_iff r).2 hr))
  refine ⟨(nrm r).2.2.1, (nrm r).2.2.2.1, (nrm r).2.2.2.2, ?_, ?_⟩
  · simp only [nrm, rot, Equiv.coe_fn_mk, e0, e1]
  · simp only [nrm, rot, Equiv.coe_fn_mk, e0, e1, hrowB, Bool.and_eq_true] at hv ⊢
    exact hv.2

/-- The automorphism fixing 0 and 1 other than the identity (a reflection), as a word in base 16:
digit v of `SW` is the image of v. -/
def SW : ℕ := 81995848451856

/-- That reflection. -/
def S (v : Fin 12) : Fin 12 := ⟨SW >>> (4 * v.val) % 16 % 12, Nat.mod_lt _ (by norm_num)⟩

set_option maxHeartbeats 4000000 in
lemma SS : ∀ v : Fin 12, S (S v) = v := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma S_adj : ∀ v w : Fin 12, adjB (S v) (S w) = adjB v w := by
  decide +kernel

lemma S0 : S 0 = 0 := by decide +kernel

lemma S1 : S 1 = 1 := by decide +kernel

/-- The reflection applied to every entry of a row. -/
def rot0 : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 ≃ Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 where
  toFun r := (S r.1, S r.2.1, S r.2.2.1, S r.2.2.2.1, S r.2.2.2.2)
  invFun r := (S r.1, S r.2.1, S r.2.2.1, S r.2.2.2.1, S r.2.2.2.2)
  left_inv r := by simp [SS]
  right_inv r := by simp [SS]

lemma W_rot0 (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : W n (rot0 r) = W n r :=
  W_equiv rot0 (fun r => by simp only [hrow_iff, hrowB, rot0, Equiv.coe_fn_mk, S_adj])
    (fun r s => by simp only [ok_iff, okB, rot0, Equiv.coe_fn_mk, S_adj]) n r

/-- The rows (0, 1, z, u, v) whose code is at most the code of their reflection; the kernel
checks run over these only. -/
def canonB (z u v : Fin 12) : Bool :=
  decide (144 * z.val + 12 * u.val + 1 * v.val ≤
    144 * (S z).val + 12 * (S u).val + 1 * (S v).val)

set_option maxHeartbeats 4000000 in
lemma canon_S : ∀ z : Fin 12, adjB 1 z = true → ∀ u : Fin 12, adjB z u = true → ∀ v : Fin 12, adjB u v = true → canonB z u v = false →
    canonB (S z) (S u) (S v) = true := by
  decide +kernel

/-- Every valid row has the counts of a checked row (0, 1, z, u, v), and a table invariant
under the reflection takes the same value at the normal form of the row and there. -/
lemma nrm_canon (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) (hr : hrowB r = true) : ∃ z u v : Fin 12,
    (∀ n, W n r = W n (0, 1, z, u, v)) ∧
    (adjB 1 z = true ∧ adjB z u = true ∧ adjB u v = true) ∧
    canonB z u v = true ∧
    ∀ g : Fin 12 → Fin 12 → Fin 12 → ℕ,
      (∀ z : Fin 12, adjB 1 z = true → ∀ u : Fin 12, adjB z u = true → ∀ v : Fin 12, adjB u v = true → g (S z) (S u) (S v) = g z u v) →
      g (nrm r).2.2.1 (nrm r).2.2.2.1 (nrm r).2.2.2.2 = g z u v := by
  obtain ⟨z, u, v, hn, h1, h2, h3⟩ := nrm_spec r hr
  by_cases hc : canonB z u v = true
  · exact ⟨z, u, v, fun n => by rw [← W_nrm n r hr, hn], ⟨h1, h2, h3⟩, hc,
      fun g _ => by simp only [hn]⟩
  · have hc' : canonB z u v = false := by simpa using hc
    have hs1 : adjB 1 (S z) = true := by
      have e := S_adj 1 z
      rw [S1] at e
      rw [e]
      exact h1
    refine ⟨S z, S u, S v, fun n => ?_,
      ⟨hs1, by rw [S_adj]; exact h2, by rw [S_adj]; exact h3⟩,
      canon_S z h1 u h2 v h3 hc', fun g hg => ?_⟩
    · rw [← W_nrm n r hr, hn, ← W_rot0 n (0, 1, z, u, v)]
      simp only [rot0, Equiv.coe_fn_mk, S0, S1]
    · simp only [hn]
      exact (hg z h1 u h2 v h3).symm

/-- W(1, (0, 1, z, u, v)) as a table (0 when that row is invalid). -/
def tab1 : Fin 12 → Fin 12 → Fin 12 → ℕ :=
  ![![0,
      ![605, 0, 515, 515, 0, 0, 0, 515, 515, 0, 0, 0],
      ![515, 380, 0, 0, 380, 0, 380, 0, 425, 0, 0, 0],
      0,
      0,
      ![515, 0, 0, 0, 0, 0, 380, 425, 0, 0, 380, 380],
      ![515, 0, 425, 0, 380, 380, 0, 0, 0, 0, 380, 0],
      ![515, 380, 0, 425, 0, 380, 0, 0, 0, 0, 0, 380],
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![![0, 380, 515, 0, 0, 380, 380, 425, 0, 0, 0, 0],
      ![515, 0, 605, 515, 0, 0, 0, 515, 515, 0, 0, 0],
      0,
      0,
      ![0, 0, 515, 0, 0, 0, 380, 0, 425, 380, 380, 0],
      0,
      ![425, 0, 515, 0, 380, 380, 0, 0, 0, 0, 380, 0],
      0,
      ![0, 380, 515, 425, 380, 0, 0, 0, 0, 380, 0, 0],
      0,
      0,
      0],
    ![0,
      ![515, 0, 515, 605, 0, 0, 0, 515, 515, 0, 0, 0],
      0,
      0,
      0,
      0,
      0,
      ![425, 380, 0, 515, 0, 380, 0, 0, 0, 0, 0, 380],
      ![0, 380, 425, 515, 380, 0, 0, 0, 0, 380, 0, 0],
      ![0, 0, 0, 515, 380, 0, 0, 0, 425, 0, 380, 380],
      0,
      ![0, 0, 0, 515, 0, 380, 0, 425, 0, 380, 380, 0]],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![![0, 380, 425, 0, 0, 380, 380, 515, 0, 0, 0, 0],
      ![515, 0, 515, 515, 0, 0, 0, 605, 515, 0, 0, 0],
      0,
      ![0, 380, 0, 0, 0, 0, 0, 515, 425, 380, 0, 380],
      0,
      ![425, 0, 0, 0, 0, 0, 380, 515, 0, 0, 380, 380],
      0,
      0,
      0,
      0,
      0,
      ![0, 0, 0, 425, 0, 380, 0, 515, 0, 380, 380, 0]],
    ![0,
      ![515, 0, 515, 515, 0, 0, 0, 515, 605, 0, 0, 0],
      ![425, 380, 0, 0, 380, 0, 380, 0, 515, 0, 0, 0],
      ![0, 380, 0, 0, 0, 0, 0, 425, 515, 380, 0, 380],
      ![0, 0, 425, 0, 0, 0, 380, 0, 515, 380, 380, 0],
      0,
      0,
      0,
      0,
      ![0, 0, 0, 425, 380, 0, 0, 0, 515, 0, 380, 380],
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0]]

/-- W(1, r), read from the table at the normal form of r (0 for an invalid row). -/
def dtab1 (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : ℕ := if hrowB r = true then tab1 (nrm r).2.2.1 (nrm r).2.2.2.1 (nrm r).2.2.2.2 else 0

/-- W(2, (0, 1, z, u, v)) as a table (0 when that row is invalid). -/
def tab2 : Fin 12 → Fin 12 → Fin 12 → ℕ :=
  ![![0,
      ![275665, 0, 231205, 231205, 0, 0, 0, 231205, 231205, 0, 0, 0],
      ![232960, 166270, 0, 0, 166270, 0, 166270, 0, 188500, 0, 0, 0],
      0,
      0,
      ![232960, 0, 0, 0, 0, 0, 166270, 188500, 0, 0, 166270, 166270],
      ![232960, 0, 188500, 0, 166270, 166270, 0, 0, 0, 0, 166270, 0],
      ![232960, 166270, 0, 188500, 0, 166270, 0, 0, 0, 0, 0, 166270],
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![![0, 166270, 232960, 0, 0, 166270, 166270, 188500, 0, 0, 0, 0],
      ![231205, 0, 275665, 231205, 0, 0, 0, 231205, 231205, 0, 0, 0],
      0,
      0,
      ![0, 0, 232960, 0, 0, 0, 166270, 0, 188500, 166270, 166270, 0],
      0,
      ![188500, 0, 232960, 0, 166270, 166270, 0, 0, 0, 0, 166270, 0],
      0,
      ![0, 166270, 232960, 188500, 166270, 0, 0, 0, 0, 166270, 0, 0],
      0,
      0,
      0],
    ![0,
      ![231205, 0, 231205, 275665, 0, 0, 0, 231205, 231205, 0, 0, 0],
      0,
      0,
      0,
      0,
      0,
      ![188500, 166270, 0, 232960, 0, 166270, 0, 0, 0, 0, 0, 166270],
      ![0, 166270, 188500, 232960, 166270, 0, 0, 0, 0, 166270, 0, 0],
      ![0, 0, 0, 232960, 166270, 0, 0, 0, 188500, 0, 166270, 166270],
      0,
      ![0, 0, 0, 232960, 0, 166270, 0, 188500, 0, 166270, 166270, 0]],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![![0, 166270, 188500, 0, 0, 166270, 166270, 232960, 0, 0, 0, 0],
      ![231205, 0, 231205, 231205, 0, 0, 0, 275665, 231205, 0, 0, 0],
      0,
      ![0, 166270, 0, 0, 0, 0, 0, 232960, 188500, 166270, 0, 166270],
      0,
      ![188500, 0, 0, 0, 0, 0, 166270, 232960, 0, 0, 166270, 166270],
      0,
      0,
      0,
      0,
      0,
      ![0, 0, 0, 188500, 0, 166270, 0, 232960, 0, 166270, 166270, 0]],
    ![0,
      ![231205, 0, 231205, 231205, 0, 0, 0, 231205, 275665, 0, 0, 0],
      ![188500, 166270, 0, 0, 166270, 0, 166270, 0, 232960, 0, 0, 0],
      ![0, 166270, 0, 0, 0, 0, 0, 188500, 232960, 166270, 0, 166270],
      ![0, 0, 188500, 0, 0, 0, 166270, 0, 232960, 166270, 166270, 0],
      0,
      0,
      0,
      0,
      ![0, 0, 0, 188500, 166270, 0, 0, 0, 232960, 0, 166270, 166270],
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0]]

/-- W(2, r), read from the table at the normal form of r (0 for an invalid row). -/
def dtab2 (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : ℕ := if hrowB r = true then tab2 (nrm r).2.2.1 (nrm r).2.2.2.1 (nrm r).2.2.2.2 else 0

set_option maxHeartbeats 4000000 in
lemma tab_sym1 : ∀ z : Fin 12, adjB 1 z = true → ∀ u : Fin 12, adjB z u = true → ∀ v : Fin 12, adjB u v = true →
    tab1 (S z) (S u) (S v) = tab1 z u v := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma tab_sym2 : ∀ z : Fin 12, adjB 1 z = true → ∀ u : Fin 12, adjB z u = true → ∀ v : Fin 12, adjB u v = true →
    tab2 (S z) (S u) (S v) = tab2 z u v := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ z : Fin 12, adjB 1 z = true → ∀ u : Fin 12, adjB z u = true → ∀ v : Fin 12, adjB u v = true → canonB z u v = true →
    succSum (0, 1, z, u, v) (fun s => if hrowB s = true then 1 else 0) = tab1 z u v := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ z : Fin 12, adjB 1 z = true → ∀ u : Fin 12, adjB z u = true → ∀ v : Fin 12, adjB u v = true → canonB z u v = true →
    succSum (0, 1, z, u, v) dtab1 = tab2 z u v := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ z : Fin 12, adjB 1 z = true → ∀ u : Fin 12, adjB z u = true → ∀ v : Fin 12, adjB u v = true → canonB z u v = true →
    succSum (0, 1, z, u, v) dtab2 + 15210 * tab1 z u v = 479 * tab2 z u v := by
  decide +kernel

lemma W_zero_fun : W 0 = fun s => if hrowB s = true then 1 else 0 := funext W_zeroB

lemma W1 (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : W 1 r = dtab1 r := by
  by_cases hr : hrowB r = true
  · obtain ⟨z, u, v, hW, ⟨h1, h2, h3⟩, hc, hg⟩ := nrm_canon r hr
    rw [hW, W_succ,
      succ_eq _ (hrowB01 z u v h1 h2 h3) (W 0) (W_invalid 0), W_zero_fun,
      check1 z h1 u h2 v h3 hc]
    simp only [dtab1, if_pos hr]
    exact (hg _ tab_sym1).symm
  · have hf : hrowB r = false := by simpa using hr
    rw [W_invalid 1 r hf]
    simp [dtab1, hf]

lemma W1_fun : W 1 = dtab1 := funext W1

lemma W2 (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : W 2 r = dtab2 r := by
  by_cases hr : hrowB r = true
  · obtain ⟨z, u, v, hW, ⟨h1, h2, h3⟩, hc, hg⟩ := nrm_canon r hr
    rw [hW, show W 2 (0, 1, z, u, v) = W (1 + 1) (0, 1, z, u, v) from rfl, W_succ,
      succ_eq _ (hrowB01 z u v h1 h2 h3) (W 1) (W_invalid 1), W1_fun,
      check2 z h1 u h2 v h3 hc]
    simp only [dtab2, if_pos hr]
    exact (hg _ tab_sym2).symm
  · have hf : hrowB r = false := by simpa using hr
    rw [W_invalid 2 r hf]
    simp [dtab2, hf]

lemma W2_fun : W 2 = dtab2 := funext W2

lemma W_rec (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) :
    W (n + 3) r + 15210 * W (n + 1) r = 479 * W (n + 2) r := by
  induction n generalizing r with
  | zero =>
    by_cases hr : hrowB r = true
    · obtain ⟨z, u, v, hW, ⟨h1, h2, h3⟩, hc, hg⟩ := nrm_canon r hr
      have e1 : W 1 (0, 1, z, u, v) = tab1 z u v := by
        rw [← hW, W1]
        simp only [dtab1, if_pos hr]
        exact hg _ tab_sym1
      have e2 : W 2 (0, 1, z, u, v) = tab2 z u v := by
        rw [← hW, W2]
        simp only [dtab2, if_pos hr]
        exact hg _ tab_sym2
      rw [show W (0 + 3) r = W 3 r from rfl,
        show W (0 + 2) r = W 2 r from rfl,
        show W (0 + 1) r = W 1 r from rfl,
        hW,
        hW,
        hW,
        e1,
        e2,
        show W 3 (0, 1, z, u, v) = W (2 + 1) (0, 1, z, u, v) from rfl,
        W_succ,
        succ_eq _ (hrowB01 z u v h1 h2 h3) (W 2) (W_invalid 2),
        W2_fun]
      exact base_check z h1 u h2 v h3 hc
    · have hf : hrowB r = false := by simpa using hr
      rw [W_invalid _ r hf, W_invalid _ r hf, W_invalid _ r hf]
  | succ n ih =>
    rw [W_succ (n + 3), W_succ (n + 1), W_succ (n + 2)]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hc : hrow r ∧ ok r s
    · simp only [if_pos hc]
      exact ih s
    · simp [hc]

lemma a_rec (n : ℕ) : a (n + 4) + 15210 * a (n + 2) = 479 * a (n + 3) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact W_rec n r
  · simp

lemma a_succ0 (n : ℕ) : a (n + 1) = ∑ t : Fin 12 × Fin 12 × Fin 12 × Fin 12, W n (0, t) := by
  rw [a_succ, Fintype.sum_prod_type, Finset.sum_eq_single (0 : Fin 12)]
  · simp
  · intro b _ hb
    exact Finset.sum_eq_zero (fun t _ => by simp [hb])
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The sum of g over the valid rows starting with 0, enumerated entry by entry. -/
def rowSum0 (g : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 → ℕ) : ℕ :=
  ∑ y ∈ N 0, ∑ z ∈ N y, ∑ u ∈ N z, ∑ v ∈ N u, g (0, y, z, u, v)

lemma row0_eq (g : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 → ℕ) (hg : ∀ s, hrowB s = false → g s = 0) :
    ∑ t : Fin 12 × Fin 12 × Fin 12 × Fin 12, g (0, t) = rowSum0 g := by
  simp only [Fintype.sum_prod_type]
  unfold rowSum0
  simp only [sum_N]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases g0 : adjB 0 y = true
  · rw [if_pos g0]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases g1 : adjB y z = true
    · rw [if_pos g1]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases g2 : adjB z u = true
      · rw [if_pos g2]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        by_cases g3 : adjB u v = true
        · rw [if_pos g3]
        · rw [if_neg g3]
          exact hg _ (by simp [hrowB, g0, g1, g2, g3])
      · rw [if_neg g2]
        exact Finset.sum_eq_zero (fun v _ => hg _ (by simp [hrowB, g0, g1, g2]))
    · rw [if_neg g1]
      exact Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => hg _ (by simp [hrowB, g0, g1])))
  · rw [if_neg g0]
    exact Finset.sum_eq_zero (fun z _ => Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => hg _ (by simp [hrowB, g0]))))

set_option maxHeartbeats 4000000 in
lemma a_one : a 1 = 625 := by
  rw [a_succ0, row0_eq _ (W_invalid 0), W_zero_fun]
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma a_two : a 2 = 274625 := by
  rw [a_succ0, row0_eq _ (W_invalid 1), W1_fun]
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma a_three : a 3 = 122039125 := by
  rw [a_succ0, row0_eq _ (W_invalid 2), W2_fun]
  decide +kernel

/-- a(k + 3) = 479 a(k + 2) - 15210 a(k + 1) for every k. -/
lemma a_rec' (k : ℕ) : (a (k + 3) : ℤ) = 479 * a (k + 2) - 15210 * a (k + 1) := by
  rcases k with _ | k
  · simp only [Nat.zero_add, a_one, a_two, a_three]
    norm_num
  · have h := a_rec k
    have hz : ((a (k + 4) : ℕ) : ℤ) + 15210 * a (k + 2) = 479 * a (k + 3) := by exact_mod_cast h
    rw [show k + 1 + 3 = k + 4 from rfl, show k + 1 + 2 = k + 3 from rfl,
      show k + 1 + 1 = k + 2 from rfl]
    linarith

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 125x(5 - 198x) / (1 - 479x + 15210x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 479 * X + 15210 * X ^ 2) = 125 * X * (5 - 198 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 479 * X + 15210 * X ^ 2) = A - A * X ^ 1 * C 479 + A * X ^ 2 * C 15210 := by
    rw [show (C (479 : ℚ) : ℚ⟦X⟧) = 479 from map_ofNat C 479,
      show (C (15210 : ℚ) : ℚ⟦X⟧) = 15210 from map_ofNat C 15210]
    ring
  have e2 : (125 * X * (5 - 198 * X) : ℚ⟦X⟧) = X ^ 1 * C 625 - X ^ 2 * C 24750 := by
    rw [show (C (625 : ℚ) : ℚ⟦X⟧) = 625 from map_ofNat C 625,
      show (C (24750 : ℚ) : ℚ⟦X⟧) = 24750 from map_ofNat C 24750]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · have hq : ((a (n + 3) : ℕ) : ℚ) = 479 * a (n + 2) - 15210 * a (n + 1) := by
      exact_mod_cast a_rec' n
    simp only [if_false, if_true, show ¬ (n + 3 = 0) by omega,
      show 1 ≤ n + 3 by omega,
      show ¬ (n + 3 - 1 = 0) by omega,
      show n + 3 - 1 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 2 ≤ n + 3 by omega,
      show ¬ (n + 3 - 2 = 0) by omega,
      show n + 3 - 2 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 3 = 1) by omega,
      show ¬ (n + 3 = 2) by omega]
    linear_combination hq

/-- The bracket of Barker's closed form. -/
noncomputable def Gf (n : ℕ) : ℝ :=
  (479 - Real.sqrt 168601) ^ n * (-3181 + 11 * Real.sqrt 168601) +
    (479 + Real.sqrt 168601) ^ n * (3181 + 11 * Real.sqrt 168601)

lemma Gf_rec (n : ℕ) : Gf (n + 2) = 958 * Gf (n + 1) - 60840 * Gf n := by
  have s2 : Real.sqrt 168601 ^ 2 = 168601 := Real.sq_sqrt (by norm_num)
  unfold Gf
  have h1 : (479 - Real.sqrt 168601) ^ 2 = 958 * (479 - Real.sqrt 168601) - 60840 := by
    linear_combination s2
  have h2 : (479 + Real.sqrt 168601) ^ 2 = 958 * (479 + Real.sqrt 168601) - 60840 := by
    linear_combination s2
  rw [show (479 - Real.sqrt 168601) ^ (n + 2) = (479 - Real.sqrt 168601) ^ n * (479 - Real.sqrt 168601) ^ 2 by ring,
    show (479 + Real.sqrt 168601) ^ (n + 2) = (479 + Real.sqrt 168601) ^ n * (479 + Real.sqrt 168601) ^ 2 by ring, h1, h2]
  ring

lemma Gf_zero : Gf 0 = 22 * Real.sqrt 168601 := by
  have s2 : Real.sqrt 168601 ^ 2 = 168601 := Real.sq_sqrt (by norm_num)
  unfold Gf
  linear_combination (0) * s2

lemma Gf_one : Gf 1 = 16900 * Real.sqrt 168601 := by
  have s2 : Real.sqrt 168601 ^ 2 = 168601 := Real.sq_sqrt (by norm_num)
  unfold Gf
  linear_combination (0) * s2

lemma Gf_two : Gf 2 = 14851720 * Real.sqrt 168601 := by
  rw [show Gf 2 = Gf (0 + 2) from rfl, Gf_rec, show Gf (0 + 1) = Gf 1 from rfl, Gf_one, Gf_zero]
  ring

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (25 * 2 ^ (-1 - (n : ℤ)) *
        ((479 - Real.sqrt 168601) ^ n * (-3181 + 11 * Real.sqrt 168601) +
        (479 + Real.sqrt 168601) ^ n * (3181 + 11 * Real.sqrt 168601))) /
        (169 * Real.sqrt 168601) := by
  have key : ∀ k, (a (k + 1) : ℝ) * 2 ^ (k + 2) * (169 * Real.sqrt 168601) = 25 * Gf (k + 1) ∧
      (a (k + 2) : ℝ) * 2 ^ (k + 3) * (169 * Real.sqrt 168601) = 25 * Gf (k + 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [a_one, Gf_one]; push_cast; ring
      · rw [a_two, Gf_two]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ((a (k + 3) : ℕ) : ℝ) = 479 * a (k + 2) - 15210 * a (k + 1) := by
        exact_mod_cast a_rec' k
      have hg := Gf_rec (k + 1)
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at hg
      show (a (k + 3) : ℝ) * 2 ^ (k + 4) * (169 * Real.sqrt 168601) = 25 * Gf (k + 3)
      linear_combination (2 ^ (k + 4) * (169 * Real.sqrt 168601)) * hr + 958 * ih.2 - 60840 * ih.1 -
        25 * hg
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  have hz : (2 : ℝ) ^ (-1 - ((k + 1 : ℕ) : ℤ)) = 1 / 2 ^ (k + 2) := by
    rw [show -1 - ((k + 1 : ℕ) : ℤ) = -((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, one_div]
  have ha : (a (k + 1) : ℝ) = 25 * Gf (k + 1) / (2 ^ (k + 2) * (169 * Real.sqrt 168601)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination hk
  show (a (k + 1) : ℝ) = (25 * 2 ^ (-1 - ((k + 1 : ℕ) : ℤ)) * Gf (k + 1)) / (169 * Real.sqrt 168601)
  rw [ha, hz]
  ring

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 479 * X + 15210 * X ^ 2) = 125 * X * (5 - 198 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (25 * 2 ^ (-1 - (n : ℤ)) *
        ((479 - Real.sqrt 168601) ^ n * (-3181 + 11 * Real.sqrt 168601) +
        (479 + Real.sqrt 168601) ^ n * (3181 + 11 * Real.sqrt 168601))) /
        (169 * Real.sqrt 168601) :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..11), from the recurrence and a(1), ..., a(3). -/
theorem controls :
    a 1 = 625 ∧ a 2 = 274625 ∧ a 3 = 122039125 ∧ a 4 = 54279694625 ∧ a 5 = 24143758634125 ∧ a 6 = 10739266230499625 ∧ a 7 = 4776881955584279125 ∧ a 8 = 2124782217358970404625 ∧ a 9 = 945114307570509938324125 ∧ a 10 = 420391815800244320602909625 ∧ a 11 = 186992491150169573406883769125 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6; have r7 := a_rec 7
  have h1 := a_one; have h2 := a_two; have h3 := a_three
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- Controls on the table: adjacency is symmetric and loop free, and every vertex has 5
neighbors (so the table has 30 edges). -/
theorem graph_controls : (∀ x y : Fin 12, adj x y ↔ adj y x) ∧ (∀ x : Fin 12, ¬ adj x x) ∧
    ∀ x : Fin 12, ((univ : Finset (Fin 12)).filter (adj x)).card = 5 := by
  decide +kernel

end OMA.S_oeis_a223318

theorem OMA.solution : type_of% @OMA.S_oeis_a223318.main :=
  OMA.S_oeis_a223318.conjecture
