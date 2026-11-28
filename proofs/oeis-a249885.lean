import OMAStatements.S_oeis_a249885

/-!
A249885: the generating function and recurrence for eight-position arrays with no
length-seven window whose third and fourth sorted values coincide.

The threshold-set bijection and recurrence propagation adapt @Salofe's A250064 proof,
PR https://github.com/lefttosolve2/open-math-agents/pull/23285 (head bd4969a8ddc52c3bd7f8d30008570b9868fd00b6).
Here the forbidden jump crosses cardinal three, there are two windows, and all
256-state tables are regenerated and certified for this exact problem.
The source conjectures are Colin Barker's; the formal statement is @clementtrecourt's.
-/

namespace OMA.Helpers

open OMA.S_oeis_a249885 Finset

/-! ### The window condition -/

/-- The condition of the statement on 7 values (without the bound on `v`). -/
def Cy (y : Fin 7 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 7)).powersetCard 3, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 7 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 3 := by
  obtain ⟨S, hS, v, h1, ⟨s, hs, hsv⟩, h3, ⟨t0, ht0, ht0v⟩⟩ := h
  have hc : S.card = 3 := (Finset.mem_powersetCard.1 hS).2
  by_cases hw : w < v
  · have hsub : univ.filter (fun t => y t ≤ w) ⊆ S.erase s := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have htS : t ∈ S := by
        by_contra hn
        have := h3 t hn
        omega
      refine Finset.mem_erase.2 ⟨?_, htS⟩
      rintro rfl
      omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hs, hc] at h1'
    omega
  · have hsub : insert t0 S ⊆ univ.filter (fun t => y t ≤ w) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · have := h1 t ht'
        omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ht0, hc] at h1'
    omega

theorem cy_of (y : Fin 7 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 3) :
    Cy y := by
  set U := univ.filter (fun s => 3 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 7)) y Finset.univ_nonempty
    refine ⟨m, ?_⟩
    rw [hU, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : univ.filter (fun t => y t ≤ y m) = univ := by
      apply Finset.filter_true_of_mem
      intro t _
      exact hm t (Finset.mem_univ t)
    rw [this]
    simp
  obtain ⟨s, hsU, hmin⟩ := Finset.exists_min_image U y hUne
  have hs2 : 3 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    rw [hU, Finset.mem_filter] at hsU
    exact hsU.2
  have hs3 : 4 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    have := h (y s)
    omega
  set L := univ.filter (fun t => y t < y s) with hL
  set E := univ.filter (fun t => y t = y s) with hE
  have hLc : L.card ≤ 2 := by
    by_cases hLne : L.Nonempty
    · obtain ⟨l, hl, hlmax⟩ := Finset.exists_max_image L y hLne
      have hyl : y l < y s := by
        rw [hL, Finset.mem_filter] at hl
        exact hl.2
      have hlU : l ∉ U := by
        intro hlU
        have := hmin l hlU
        omega
      have hcl : (univ.filter (fun t => y t ≤ y l)).card ≤ 2 := by
        rw [hU, Finset.mem_filter] at hlU
        have : ¬ 3 ≤ (univ.filter (fun t => y t ≤ y l)).card :=
          fun h2 => hlU ⟨Finset.mem_univ _, h2⟩
        omega
      have hsub : L ⊆ univ.filter (fun t => y t ≤ y l) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlmax t ht
      exact le_trans (Finset.card_le_card hsub) hcl
    · rw [Finset.not_nonempty_iff_eq_empty.mp hLne]
      simp
  have hsplit : (univ.filter (fun t => y t ≤ y s)) ⊆ L ∪ E := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [Finset.mem_union, hL, hE, Finset.mem_filter, Finset.mem_filter]
    rcases Nat.lt_or_ge (y t) (y s) with h' | h'
    · exact Or.inl ⟨Finset.mem_univ _, h'⟩
    · exact Or.inr ⟨Finset.mem_univ _, by omega⟩
  have hcard := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le L E)
  have hsE : s ∈ E := by
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hnotL : ∀ t, ¬ y t < y s → t ∉ L := by
    intro t ht htL
    rw [hL, Finset.mem_filter] at htL
    exact ht htL.2
  obtain ⟨D, hDE, hD⟩ := Finset.exists_subset_card_eq (s := E) (n := 3 - L.card) (by omega)
  have hLD : Disjoint L D := by
    apply Finset.disjoint_left.2
    intro t htL htD
    have he := hDE htD
    simp only [hL, hE, Finset.mem_filter, Finset.mem_univ, true_and] at htL he
    omega
  have hDc : 0 < D.card := by omega
  obtain ⟨d, hd⟩ := Finset.card_pos.1 hDc
  have hdc : y d = y s := by
    have := hDE hd
    simpa only [hE, Finset.mem_filter, Finset.mem_univ, true_and] using this
  obtain ⟨e, heE, heD⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := D) (t := E) (by omega)
  have hec : y e = y s := by
    simpa only [hE, Finset.mem_filter, Finset.mem_univ, true_and] using heE
  refine ⟨L ∪ D, ?_, y s, ?_, ⟨d, Finset.mem_union_right _ hd, hdc⟩, ?_, ⟨e, ?_, hec⟩⟩
  · apply Finset.mem_powersetCard.2
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_union_of_disjoint hLD, hD]
    omega
  · intro t ht
    rcases Finset.mem_union.1 ht with ht | ht
    · have := (Finset.mem_filter.1 ht).2
      omega
    · have := (Finset.mem_filter.1 (hDE ht)).2
      omega
  · intro t ht
    by_contra hlt
    apply ht
    apply Finset.mem_union_left
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_univ _, by omega⟩
  · intro he
    rcases Finset.mem_union.1 he with he | he
    · have := (Finset.mem_filter.1 he).2
      omega
    · exact heD he

theorem window_iff (y : Fin 7 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 3 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 7 → ℕ) :
    ¬ Cy y ↔ ∀ v : ℕ, ¬ ((univ.filter (fun t => y t < v)).card ≤ 2 ∧
      4 ≤ (univ.filter (fun t => y t < v + 1)).card) := by
  rw [window_iff, not_forall]
  simp only [ne_eq, not_not]
  constructor
  · rintro ⟨w, hw⟩ v ⟨h1, h3⟩
    rcases Nat.lt_or_ge w v with h | h
    · have hsub : univ.filter (fun t => y t ≤ w) ⊆ univ.filter (fun t => y t < v) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        omega
      have := Finset.card_le_card hsub
      omega
    · have hsub : univ.filter (fun t => y t < v + 1) ⊆ univ.filter (fun t => y t ≤ w) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        omega
      have := Finset.card_le_card hsub
      omega
  · intro h
    by_contra hne
    simp only [not_exists] at hne
    have key : ∀ v, (univ.filter (fun t => y t < v)).card ≤ 2 := by
      intro v
      induction v with
      | zero => simp
      | succ v ih =>
        have h1 := h v
        have h2 := hne v
        have e : univ.filter (fun t => y t < v + 1) = univ.filter (fun t => y t ≤ v) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        rw [e] at h1 ⊢
        by_contra hc
        exact h1 ⟨ih, by omega⟩
    have hall : univ.filter (fun t => y t < univ.sup y + 1) = univ := by
      apply Finset.filter_true_of_mem
      intro t _
      have := Finset.le_sup (f := y) (Finset.mem_univ t)
      omega
    have := key (univ.sup y + 1)
    rw [hall] at this
    simp at this

/-! ### Strict threshold sets -/

/-- Entry `k` of a set of positions (`false` past the end). -/
def fget (f : Fin 8 → Bool) (k : ℕ) : Bool := if h : k < 8 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 8 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 7 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most two positions to at least
four positions. -/
def Comp (S T : Fin 8 → Bool) : Prop := ∀ i < (2 : ℕ), ¬ (cntW S i ≤ 2 ∧ 4 ≤ cntW T i)

instance decComp (S T : Fin 8 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 8 → Fin (n + 1)) (v : ℕ) : Fin 8 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 8 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a249885.get x k ≤ n := by
  unfold OMA.S_oeis_a249885.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (2 : ℕ), cntW (fun _ => true) i = 7 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 8 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (2 : ℕ), ¬ Cy (fun t : Fin 7 => OMA.S_oeis_a249885.get x (i + t)) := by
    unfold good
    rw [decide_eq_true_iff]
    refine forall_congr' fun i => imp_congr_right fun _ => not_congr ?_
    constructor
    · rintro ⟨S, hS, v, _, h1, h2, h3, h4⟩
      exact ⟨S, hS, v, h1, h2, h3, h4⟩
    · rintro ⟨S, hS, v, h1, ⟨t, ht, htv⟩, h3, h4⟩
      refine ⟨S, hS, v, ?_, h1, ⟨t, ht, htv⟩, h3, h4⟩
      rw [← htv]
      exact Nat.lt_succ_of_le (get_le x _)
  have step2 : ∀ i < (2 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 7 => OMA.S_oeis_a249885.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 8 := by have := t.isLt; omega
    unfold OMA.S_oeis_a249885.get fget Lt
    rw [dif_pos ht, dif_pos ht, decide_eq_true_iff]
  have hfull : ∀ w, n < w → Lt x w = fun _ => true := by
    intro w hw
    funext p
    unfold Lt
    have := (x p).isLt
    simp only [decide_eq_true_iff]
    omega
  rw [step1]
  constructor
  · intro h v _ i hi
    have := (not_cy_iff _).1 (h i hi) v
    simp only [step2 i hi v, step2 i hi (v + 1)] at this
    exact this
  · intro h i hi
    rw [not_cy_iff]
    intro v
    simp only [step2 i hi v, step2 i hi (v + 1)]
    by_cases hv : v ≤ n
    · exact h v hv i hi
    · rw [hfull v (by omega), cnt_univ i hi]
      omega

/-! ### Chains of strict threshold sets -/

/-- Arrays with entries in `0..n` whose consecutive strict threshold sets are compatible, with
`Lt x n ⊆ T` and `Lt x n` compatible with `T`. -/
noncomputable def M (n : ℕ) (T : Fin 8 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 8 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 8 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 8 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
  classical
  unfold M
  split_ifs with h
  · rw [Finset.filter_true_of_mem]
    · simp
    · intro x _
      refine ⟨fun p hp => ?_, fun v hv => absurd hv (Nat.not_lt_zero _), ?_⟩
      · rw [Lt_zero] at hp
        exact absurd hp (by simp)
      · rw [Lt_zero]
        exact h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    apply h
    rw [← Lt_zero x]
    exact hx.2.2

/-- Restriction of an array with entries in `0..n+1` to entries in `0..n`. -/
def lower {n : ℕ} (x : Fin 8 → Fin (n + 2)) : Fin 8 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 8 → Bool) (x : Fin 8 → Fin (n + 1)) : Fin 8 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 8 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 8 → Bool) (x : Fin 8 → Fin (n + 1)) (p : Fin 8) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 8 → Bool) :
    M (n + 1) T = ∑ S : Fin 8 → Bool,
      if Comp S T ∧ (∀ p, S p = true → T p = true) then M n S else 0 := by
  classical
  unfold M
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => Lt x (n + 1)) (t := univ)
    (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hS
  · apply Finset.card_bij' (fun x _ => lower x) (fun x _ => raise S x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨⟨_, h2, _⟩, h3⟩ := hx
      refine ⟨fun p hp => ?_, fun v hv => ?_, ?_⟩
      · rw [Lt_lower x n le_rfl] at hp
        rw [← h3]
        have hp' : (x p : ℕ) < n := of_decide_eq_true hp
        exact decide_eq_true (by omega)
      · rw [Lt_lower x v (by omega), Lt_lower x (v + 1) (by omega)]
        exact h2 v (by omega)
      · rw [Lt_lower x n le_rfl, ← h3]
        exact h2 n (by omega)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨h1, h2, h3⟩ := hx
      have hTS : Lt (raise S x) (n + 1) = S := by
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) < n + 1) = S p
        rw [raise_val]
        by_cases hp : S p = true
        · rw [if_pos hp, hp]
          have := (x p).isLt
          exact decide_eq_true (by omega)
        · rw [if_neg hp]
          simp only [Bool.not_eq_true] at hp
          rw [hp]
          exact decide_eq_false (by omega)
      have hlow : ∀ v ≤ n, Lt (raise S x) v = Lt x v := by
        intro v hv
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) < v) = decide ((x p : ℕ) < v)
        rw [raise_val]
        split_ifs with hp
        · rfl
        · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p (decide_eq_true h))
          rw [decide_eq_decide]
          omega
      refine ⟨⟨?_, fun v hv => ?_, ?_⟩, hTS⟩
      · rw [hTS]
        exact hS.2
      · rcases Nat.lt_or_ge v n with hv' | hv'
        · rw [hlow v (by omega), hlow (v + 1) (by omega)]
          exact h2 v hv'
        · obtain rfl : v = n := by omega
          rw [hlow v le_rfl, hTS]
          exact h3
      · rw [hTS]
        exact hS.1
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨_, h3⟩ := hx
      funext p
      apply Fin.ext
      rw [raise_val]
      have hiff : S p = true ↔ (x p : ℕ) < n + 1 := by
        rw [← h3]
        exact decide_eq_true_iff
      split_ifs with hp
      · show min (x p : ℕ) n = x p
        have := hiff.1 hp
        omega
      · have : ¬ (x p : ℕ) < n + 1 := fun h => hp (hiff.2 h)
        have := (x p).isLt
        omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨h1, _⟩ := hx
      funext p
      apply Fin.ext
      show min ((raise S x p : Fin (n + 2)) : ℕ) n = x p
      rw [raise_val]
      split_ifs with hp
      · have := (x p).isLt
        omega
      · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p (decide_eq_true h))
        have := (x p).isLt
        omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    rintro ⟨⟨h1, _, h3⟩, h4⟩
    apply hS
    rw [← h4]
    exact ⟨h3, h1⟩

/-! ### Codes -/

/-- The set of positions with code `u`: position `p` is in it iff bit `p` of `u` is set. -/
def row (u : Fin 256) : Fin 8 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 8 → Bool) : ℕ := ∑ p : Fin 8, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 256, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 8 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2

theorem cnt_row : ∀ u : Fin 256, cntW (row u) 0 = pcb (u.val &&& 127) ∧
    cntW (row u) 1 = pcb (u.val &&& 254) := by
  decide +kernel

/-- Compatibility is checked separately in the two windows. -/
def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 127) ≤ 2 ∧ 4 ≤ pcb (t &&& 127)) ∧
    ¬ (pcb (s &&& 254) ≤ 2 ∧ 4 ≤ pcb (t &&& 254)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (2 : ℕ), P i) ↔ P 0 ∧ P 1 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 256) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1⟩ := cnt_row s
  obtain ⟨b0, b1⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, b0, b1]

theorem sub_iff (w u : Fin 256) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 8
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (256 : ℕ) ≤ 2 ^ i := by
          calc (256 : ℕ) = 2 ^ 8 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := w.isLt
        omega
      simp [hw]
  · intro h p hp
    unfold row at hp ⊢
    rw [← h, Nat.testBit_land] at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.2

/-- The codes of the subsets of the set with code `u`. -/
def subs (u : Fin 256) : Finset (Fin 256) :=
  univ.filter (fun w : Fin 256 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 256 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 256, M n (row u) = G n u := by
  induction n with
  | zero =>
    intro u
    rw [M_zero, ← row_zero, G]
    exact if_congr (compc_iff 0 u) rfl rfl
  | succ n ih =>
    intro u
    rw [M_succ, ← row_bijective.sum_comp]
    simp only [G, subs]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih w]
    by_cases h1 : (w.val &&& u.val == w.val) = true
    · rw [if_pos h1]
      exact if_congr ((and_iff_left ((sub_iff w u).2 h1)).trans (compc_iff w u)) rfl rfl
    · rw [if_neg h1, if_neg (fun h => h1 ((sub_iff w u).1 h.2))]

theorem row_full : ∀ p, row 255 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 255 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 8 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 255 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 255)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 255 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 255 := by
      rw [hr]
      funext p
      unfold Lt
      have := (x p).isLt
      simp only [decide_eq_true_iff]
      omega
    constructor
    · intro h
      refine ⟨fun p _ => row_full p, fun v hv => h v (by omega), ?_⟩
      rw [← hn]
      exact h n le_rfl
    · rintro ⟨_, h2, h3⟩ v hv
      rcases Nat.lt_or_ge v n with h | h
      · exact h2 v h
      · obtain rfl : v = n := by omega
        rw [hn]
        exact h3
  unfold a
  rw [h1, ← M_eq_G]
  unfold M
  congr 2

theorem G_succ (n : ℕ) (u : Fin 256) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 := rfl

/-- Packed state vectors, certified by the chain recursion, with 32-bit entries. -/
-- Each table row stores its field width followed by its packed coefficients.
def tb (T : ℕ × ℕ) (w : ℕ) : ℕ := (T.2 >>> (T.1 * w)) % 2 ^ T.1

def tabT : ℕ → ℕ × ℕ
  | 0 => (1, 0x30003033f0003033f033f3fff000101170117177f0117177f177f7fff)
  | 1 => (6, 0x8d450a50a28450a28428410450a28428410428410410440850a28428410428410410440828410410440810440840820450a28428410428410410440828410410440810440840820428410410440810440840820410440840820440820420410251428a28a10428a10410410828a10410410810410810820428a10410410810410810820410410810820410820420410228a104104108104108108204104108108204108204204102104108108204108204204102108204204102204102102081)
  | 2 => (11, 0xaaa821040b44102d0630384102d06303818c0e0220244102d06303818c0e02202418c0e0220240880902881b4102d06303818c0e02202418c0e0220240880902881b18c0e0220240880902881b0880902881b0a206c0d8094102d06303818c0e02202418c0e0220240880902881b18c0e0220240880902881b0880902881b0a206c0d80918c0e0220240880902881b0880902881b0a206c0d8090880902881b0a206c0d8090a206c0d809036024048034104b05a06e1681b81c0241681b81c0240700901201b1681b81c0240700901201b0700901201b04806c0d8091681b81c0240700901201b0700901201b04806c0d8090700901201b04806c0d80904806c0d809036024048031681b81c0240700901201b0700901201b04806c0d8090700901201b04806c0d80904806c0d809036024048030700901201b04806c0d80904806c0d8090360240480304806c0d809036024048030360240480301200c01801)
  | 3 => (15, 0x8fac5140a28056428a015902ee015828a015902ee01580bb805600cd009028a015902ee01580bb805600cd00900bb805600cd009003340240080004028a015902ee01580bb805600cd00900bb805600cd00900334024008000400bb805600cd009003340240080004003340240080004002000100020001028a015902ee01580bb805600cd00900bb805600cd00900334024008000400bb805600cd00900334024008000400334024008000400200010002000100bb805600cd009003340240080004003340240080004002000100020001003340240080004002000100020001002000100020001000800040008000428a01fe02b202300ac808c00ac00900ac808c00ac009002b0024004800400ac808c00ac009002b00240048004002b0024004800400120010002000100ac808c00ac009002b00240048004002b00240048004001200100020001002b0024004800400120010002000100120010002000100080004000800040ac808c00ac009002b00240048004002b00240048004001200100020001002b00240048004001200100020001001200100020001000800040008000402b002400480040012001000200010012001000200010008000400080004012001000200010008000400080004008000400080004002000100020001)
  | 4 => (18, 0x84d2876981da60193c1da60193c06c1005281da60193c06c10052806c100528017e801901da60193c06c10052806c100528017e8019006c100528017e80190017e80190009c4007d1da60193c06c10052806c100528017e8019006c100528017e80190017e80190009c4007d06c100528017e80190017e80190009c4007d017e80190009c4007d009c4007d001f400191da60193c06c10052806c100528017e8019006c100528017e80190017e80190009c4007d06c100528017e80190017e80190009c4007d017e80190009c4007d009c4007d001f4001906c100528017e80190017e80190009c4007d017e80190009c4007d009c4007d001f40019017e80190009c4007d009c4007d001f40019009c4007d001f40019001f400190006400051da602288064f00780064f00780014a00190064f00780014a00190014a0019000640007d064f00780014a00190014a0019000640007d014a0019000640007d00640007d001f40019064f00780014a00190014a0019000640007d014a0019000640007d00640007d001f40019014a0019000640007d00640007d001f4001900640007d001f40019001f40019000640005064f00780014a00190014a0019000640007d014a0019000640007d00640007d001f40019014a0019000640007d00640007d001f4001900640007d001f40019001f40019000640005014a0019000640007d00640007d001f4001900640007d001f40019001f4001900064000500640007d001f40019001f40019000640005001f40019000640005000640005000140001)
  | 5 => (20, 0xa72291eb541eb54056d61eb54056d605be600eec1eb54056d605be600eec05be600eec010ea003841eb54056d605be600eec05be600eec010ea0038405be600eec010ea00384010ea0038400510000d81eb54056d605be600eec05be600eec010ea0038405be600eec010ea00384010ea0038400510000d805be600eec010ea00384010ea0038400510000d8010ea0038400510000d800510000d8000d8000241eb54056d605be600eec05be600eec010ea0038405be600eec010ea00384010ea0038400510000d805be600eec010ea00384010ea0038400510000d8010ea0038400510000d800510000d8000d80002405be600eec010ea00384010ea0038400510000d8010ea0038400510000d800510000d8000d800024010ea0038400510000d800510000d8000d80002400510000d8000d800024000d80002400024000061eb54070bc056d601432056d60143200eec00384056d60143200eec0038400eec0038400384000d8056d60143200eec0038400eec0038400384000d800eec0038400384000d800384000d8000d800024056d60143200eec0038400eec0038400384000d800eec0038400384000d800384000d8000d80002400eec0038400384000d800384000d8000d80002400384000d8000d800024000d8000240002400006056d60143200eec0038400eec0038400384000d800eec0038400384000d800384000d8000d80002400eec0038400384000d800384000d8000d80002400384000d8000d800024000d800024000240000600eec0038400384000d800384000d8000d80002400384000d8000d800024000d800024000240000600384000d8000d800024000d8000240002400006000d800024000240000600024000060000600001)
  | 6 => (22, 0xa16d3c64a001928000f2d01928000f2d003fb28023e01928000f2d003fb28023e003fb28023e0009fe8006e41928000f2d003fb28023e003fb28023e0009fe8006e403fb28023e0009fe8006e4009fe8006e4002584001571928000f2d003fb28023e003fb28023e0009fe8006e403fb28023e0009fe8006e4009fe8006e40025840015703fb28023e0009fe8006e4009fe8006e400258400157009fe8006e4002584001570025840015700055c000311928000f2d003fb28023e003fb28023e0009fe8006e403fb28023e0009fe8006e4009fe8006e40025840015703fb28023e0009fe8006e4009fe8006e400258400157009fe8006e4002584001570025840015700055c0003103fb28023e0009fe8006e4009fe8006e400258400157009fe8006e4002584001570025840015700055c00031009fe8006e4002584001570025840015700055c000310025840015700055c0003100055c000310000c40000719280012f8403cb4002e3603cb4002e36008f80006e403cb4002e36008f80006e4008f80006e4001b900015703cb4002e36008f80006e4008f80006e4001b9000157008f80006e4001b9000157001b900015700055c0003103cb4002e36008f80006e4008f80006e4001b9000157008f80006e4001b9000157001b900015700055c00031008f80006e4001b9000157001b900015700055c00031001b900015700055c0003100055c000310000c40000703cb4002e36008f80006e4008f80006e4001b9000157008f80006e4001b9000157001b900015700055c00031008f80006e4001b9000157001b900015700055c00031001b900015700055c0003100055c000310000c400007008f80006e4001b9000157001b900015700055c00031001b900015700055c0003100055c000310000c400007001b900015700055c0003100055c000310000c40000700055c000310000c4000070000c40000700001c00001)
  | 7 => (24, 0x80b5ec1165c01165c00249281165c0024928026218004bb01165c0024928026218004bb0026218004bb000533c000c401165c0024928026218004bb0026218004bb000533c000c40026218004bb000533c000c4000533c000c400010000002001165c0024928026218004bb0026218004bb000533c000c40026218004bb000533c000c4000533c000c40001000000200026218004bb000533c000c4000533c000c4000100000020000533c000c400010000002000010000002000002000000401165c0024928026218004bb0026218004bb000533c000c40026218004bb000533c000c4000533c000c40001000000200026218004bb000533c000c4000533c000c4000100000020000533c000c40001000000200001000000200000200000040026218004bb000533c000c4000533c000c4000100000020000533c000c4000100000020000100000020000020000004000533c000c400010000002000010000002000002000000400010000002000002000000400002000000400000400000081165c002c6f0024928005e10024928005e10004bb0000c40024928005e10004bb0000c40004bb0000c40000c40000200024928005e10004bb0000c40004bb0000c40000c40000200004bb0000c40000c40000200000c40000200000200000040024928005e10004bb0000c40004bb0000c40000c40000200004bb0000c40000c40000200000c40000200000200000040004bb0000c40000c40000200000c40000200000200000040000c40000200000200000040000200000040000040000008024928005e10004bb0000c40004bb0000c40000c40000200004bb0000c40000c40000200000c40000200000200000040004bb0000c40000c40000200000c40000200000200000040000c40000200000200000040000200000040000040000008004bb0000c40000c40000200000c40000200000200000040000c40000200000200000040000200000040000040000008000c40000200000200000040000200000040000040000008000200000040000040000008000040000008000008000001)
  | 8 => (25, 0xb192ca0a9704054b82004ed68152e08013b5a00a39500090f0152e08013b5a00a39500090f0028e5400243c0013b78001440152e08013b5a00a39500090f0028e5400243c0013b78001440028e5400243c0013b78001440004ede00051000033420002d9152e08013b5a00a39500090f0028e5400243c0013b78001440028e5400243c0013b78001440004ede00051000033420002d9028e5400243c0013b78001440004ede00051000033420002d9004ede00051000033420002d9000cd08000b640005b2000051152e08013b5a00a39500090f0028e5400243c0013b78001440028e5400243c0013b78001440004ede00051000033420002d9028e5400243c0013b78001440004ede00051000033420002d9004ede00051000033420002d9000cd08000b640005b2000051028e5400243c0013b78001440004ede00051000033420002d9004ede00051000033420002d9000cd08000b640005b2000051004ede00051000033420002d9000cd08000b640005b2000051000cd08000b640005b200005100016c80001440000a2000009152e080176c4009dad000af500276b4002bd400121e00014400276b4002bd400121e000144000487800051000028800002d90276b4002bd400121e000144000487800051000028800002d900487800051000028800002d9000a200000b640005b20000510276b4002bd400121e000144000487800051000028800002d900487800051000028800002d9000a200000b640005b200005100487800051000028800002d9000a200000b640005b2000051000a200000b640005b200005100016c80001440000a20000090276b4002bd400121e000144000487800051000028800002d900487800051000028800002d9000a200000b640005b200005100487800051000028800002d9000a200000b640005b2000051000a200000b640005b200005100016c80001440000a200000900487800051000028800002d9000a200000b640005b2000051000a200000b640005b200005100016c80001440000a2000009000a200000b640005b200005100016c80001440000a200000900016c80001440000a20000090000288000024000012000001)
  | 9 => (26, 0xdacb6bc5d5f341757cd009bda21757cd009bda202843880101941757cd009bda20284388010194028438801019400457e0001fa41757cd009bda20284388010194028438801019400457e0001fa4028438801019400457e0001fa400457e0001fa40009c400003e81757cd009bda20284388010194028438801019400457e0001fa4028438801019400457e0001fa400457e0001fa40009c400003e8028438801019400457e0001fa400457e0001fa40009c400003e800457e0001fa40009c400003e80009c400003e80000fa00000641757cd009bda20284388010194028438801019400457e0001fa4028438801019400457e0001fa400457e0001fa40009c400003e8028438801019400457e0001fa400457e0001fa40009c400003e800457e0001fa40009c400003e80009c400003e80000fa0000064028438801019400457e0001fa400457e0001fa40009c400003e800457e0001fa40009c400003e80009c400003e80000fa000006400457e0001fa40009c400003e80009c400003e80000fa00000640009c400003e80000fa00000640000fa0000064000019000000a1757cd00b5fa4026f68801310a026f68801310a0040650001fa4026f68801310a0040650001fa40040650001fa40007e900003e8026f68801310a0040650001fa40040650001fa40007e900003e80040650001fa40007e900003e80007e900003e80000fa0000064026f68801310a0040650001fa40040650001fa40007e900003e80040650001fa40007e900003e80007e900003e80000fa00000640040650001fa40007e900003e80007e900003e80000fa00000640007e900003e80000fa00000640000fa0000064000019000000a026f68801310a0040650001fa40040650001fa40007e900003e80040650001fa40007e900003e80007e900003e80000fa00000640040650001fa40007e900003e80007e900003e80000fa00000640007e900003e80000fa00000640000fa0000064000019000000a0040650001fa40007e900003e80007e900003e80000fa00000640007e900003e80000fa00000640000fa0000064000019000000a0007e900003e80000fa00000640000fa0000064000019000000a0000fa0000064000019000000a000019000000a0000028000001)
  | _ => (1, 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def base_T : ∀ u : Fin 256, G 0 u = tb (tabT 0) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_0 : ∀ u : Fin 256, u.val / 16 = 0 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_1 : ∀ u : Fin 256, u.val / 16 = 1 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_2 : ∀ u : Fin 256, u.val / 16 = 2 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_3 : ∀ u : Fin 256, u.val / 16 = 3 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_4 : ∀ u : Fin 256, u.val / 16 = 4 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_5 : ∀ u : Fin 256, u.val / 16 = 5 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_6 : ∀ u : Fin 256, u.val / 16 = 6 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_7 : ∀ u : Fin 256, u.val / 16 = 7 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_8 : ∀ u : Fin 256, u.val / 16 = 8 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_9 : ∀ u : Fin 256, u.val / 16 = 9 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_10 : ∀ u : Fin 256, u.val / 16 = 10 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_11 : ∀ u : Fin 256, u.val / 16 = 11 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_12 : ∀ u : Fin 256, u.val / 16 = 12 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_13 : ∀ u : Fin 256, u.val / 16 = 13 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_14 : ∀ u : Fin 256, u.val / 16 = 14 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_15 : ∀ u : Fin 256, u.val / 16 = 15 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

theorem step_all (n : ℕ) (hn : n < 9) (u : Fin 256) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  have hu := u.isLt
  obtain ⟨c, hc⟩ : ∃ c, u.val / 16 = c := ⟨_, rfl⟩
  have hc2 : c < 16 := by omega
  interval_cases c
  · exact chunk_0 u hc n hn
  · exact chunk_1 u hc n hn
  · exact chunk_2 u hc n hn
  · exact chunk_3 u hc n hn
  · exact chunk_4 u hc n hn
  · exact chunk_5 u hc n hn
  · exact chunk_6 u hc n hn
  · exact chunk_7 u hc n hn
  · exact chunk_8 u hc n hn
  · exact chunk_9 u hc n hn
  · exact chunk_10 u hc n hn
  · exact chunk_11 u hc n hn
  · exact chunk_12 u hc n hn
  · exact chunk_13 u hc n hn
  · exact chunk_14 u hc n hn
  · exact chunk_15 u hc n hn

theorem G_eq_T (n : ℕ) (hn : n ≤ 9) : ∀ u : Fin 256, G n u = tb (tabT n) u.val := by
  induction n with
  | zero => exact base_T
  | succ n ih =>
    intro u
    rw [G_succ]
    have ih' := ih (by omega)
    simp only [ih']
    exact step_all n (by omega) u

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def tab_base : ∀ u : Fin 256,
    tb (tabT 9) u.val + 36 * tb (tabT 7) u.val + 126 * tb (tabT 5) u.val + 84 * tb (tabT 3) u.val + 9 * tb (tabT 1) u.val =
      9 * tb (tabT 8) u.val + 84 * tb (tabT 6) u.val + 126 * tb (tabT 4) u.val + 36 * tb (tabT 2) u.val + tb (tabT 0) u.val := by
  decide +kernel

theorem G_base : ∀ u : Fin 256,
    G 9 u + 36 * G 7 u + 126 * G 5 u + 84 * G 3 u + 9 * G 1 u =
      9 * G 8 u + 84 * G 6 u + 126 * G 4 u + 36 * G 2 u + G 0 u := by
  intro u
  rw [G_eq_T 9 (by norm_num) u, G_eq_T 8 (by norm_num) u, G_eq_T 7 (by norm_num) u, G_eq_T 6 (by norm_num) u, G_eq_T 5 (by norm_num) u, G_eq_T 4 (by norm_num) u, G_eq_T 3 (by norm_num) u, G_eq_T 2 (by norm_num) u, G_eq_T 1 (by norm_num) u, G_eq_T 0 (by norm_num) u]
  exact tab_base u

theorem G_rec (m : ℕ) : ∀ u : Fin 256,
    G (m + 9) u + 36 * G (m + 7) u + 126 * G (m + 5) u + 84 * G (m + 3) u + 9 * G (m + 1) u =
      9 * G (m + 8) u + 84 * G (m + 6) u + 126 * G (m + 4) u + 36 * G (m + 2) u + G m u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega, show m + 1 + 9 = (m + 9) + 1 by omega]
    rw [G_succ (m + 9), G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1), G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 9) + 36 * a (m + 7) + 126 * a (m + 5) + 84 * a (m + 3) + 9 * a (m + 1) =
      9 * a (m + 8) + 84 * a (m + 6) + 126 * a (m + 4) + 36 * a (m + 2) + a m := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 255

theorem G_vals : G 1 255 = 35 ∧ G 2 255 = 1365 ∧ G 3 255 = 18390 ∧ G 4 255 = 136010 ∧ G 5 255 = 684585 ∧ G 6 255 = 2644815 ∧ G 7 255 = 8435180 ∧ G 8 255 = 23274900 ∧ G 9 255 = 57355695 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num), G_eq_T 9 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 35 ∧ a 2 = 1365 ∧ a 3 = 18390 ∧ a 4 = 136010 ∧ a 5 = 684585 ∧ a 6 = 2644815 ∧ a 7 = 8435180 ∧ a 8 = 23274900 ∧ a 9 = 57355695 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num

theorem recurrence (n : ℕ) (hn : 10 ≤ n) :
    (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 9) + 36 * a (m + 7) + 126 * a (m + 5) + 84 * a (m + 3) + 9 * a (m + 1) : ℤ) : ℚ) =
      ((9 * a (m + 8) + 84 * a (m + 6) + 126 * a (m + 4) + 36 * a (m + 2) + a m : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 9 - 1 = (m + 8) by omega, show m + 9 - 2 = (m + 7) by omega, show m + 9 - 3 = (m + 6) by omega, show m + 9 - 4 = (m + 5) by omega, show m + 9 - 5 = (m + 4) by omega, show m + 9 - 6 = (m + 3) by omega, show m + 9 - 7 = (m + 2) by omega, show m + 9 - 8 = (m + 1) by omega, show m + 9 - 9 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 9 : PowerSeries ℚ) =
      5 * X * (7 + 210 * X + 1473 * X ^ 2 + 3340 * X ^ 3 + 2457 * X ^ 4 + 546 * X ^ 5 + 31 * X ^ 6) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 9 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 9 * (PowerSeries.mk F * X ^ 1) + C 36 * (PowerSeries.mk F * X ^ 2) - C 84 * (PowerSeries.mk F * X ^ 3) + C 126 * (PowerSeries.mk F * X ^ 4) - C 126 * (PowerSeries.mk F * X ^ 5) + C 84 * (PowerSeries.mk F * X ^ 6) - C 36 * (PowerSeries.mk F * X ^ 7) + C 9 * (PowerSeries.mk F * X ^ 8) - C 1 * (PowerSeries.mk F * X ^ 9) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (5 * X * (7 + 210 * X + 1473 * X ^ 2 + 3340 * X ^ 3 + 2457 * X ^ 4 + 546 * X ^ 5 + 31 * X ^ 6) : ℚ⟦X⟧) =
      C 35 * X ^ 1 + C 1050 * X ^ 2 + C 7365 * X ^ 3 + C 16700 * X ^ 4 + C 12285 * X ^ 5 + C 2730 * X ^ 6 + C 155 * X ^ 7 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    have hr := recurrence (j + 10) (by omega)
    simp only [show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega, show j + 10 - 8 = j + 2 by omega, show j + 10 - 9 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 10 by omega,
      show 1 ≤ j + 10 by omega,
      show 2 ≤ j + 10 by omega,
      show 3 ≤ j + 10 by omega,
      show 4 ≤ j + 10 by omega,
      show 5 ≤ j + 10 by omega,
      show 6 ≤ j + 10 by omega,
      show 7 ≤ j + 10 by omega,
      show 8 ≤ j + 10 by omega,
      show 9 ≤ j + 10 by omega,
      show j + 10 - 0 = j + 10 by omega,
      show j + 10 - 1 = j + 9 by omega,
      show j + 10 - 2 = j + 8 by omega,
      show j + 10 - 3 = j + 7 by omega,
      show j + 10 - 4 = j + 6 by omega,
      show j + 10 - 5 = j + 5 by omega,
      show j + 10 - 6 = j + 4 by omega,
      show j + 10 - 7 = j + 3 by omega,
      show j + 10 - 8 = j + 2 by omega,
      show j + 10 - 9 = j + 1 by omega,
      show ¬ (j + 10 = 1) by omega,
      show ¬ (j + 10 = 2) by omega,
      show ¬ (j + 10 = 3) by omega,
      show ¬ (j + 10 = 4) by omega,
      show ¬ (j + 10 = 5) by omega,
      show ¬ (j + 10 = 6) by omega,
      show ¬ (j + 10 = 7) by omega,
      show ¬ (j + 10 < 1) by omega,
      show ¬ (j + 9 < 1) by omega,
      show ¬ (j + 8 < 1) by omega,
      show ¬ (j + 7 < 1) by omega,
      show ¬ (j + 6 < 1) by omega,
      show ¬ (j + 5 < 1) by omega,
      show ¬ (j + 4 < 1) by omega,
      show ¬ (j + 3 < 1) by omega,
      show ¬ (j + 2 < 1) by omega,
      show ¬ (j + 1 < 1) by omega,
      if_true, if_false, hF]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a249885.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
