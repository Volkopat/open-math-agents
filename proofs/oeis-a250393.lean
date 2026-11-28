import OMAStatements.S_oeis_a250393

/-!
A250393: exact ten-position/seven-window adaptation of the threshold-chain proof
by @Salofe for A250064, PR #23285, commit bd4969a8ddc52c3bd7f8d30008570b9868fd00b6.
Related checked specialization: our A250390 proof, PR #26510.
Conjecture: Colin Barker (2017); registered statement: @clementtrecourt, PR #19434.
The finite tables certify a recurrence on every subset state; linearity then proves
it for all levels. All computations are kernel checked.
-/

namespace OMA.A250393

open OMA.S_oeis_a250393 Finset

/-! ### The window condition -/

/-- The condition of the statement on 4 values (without the bound on `v`). -/
def Cy (y : Fin 4 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 4)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 4 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
  obtain ⟨S, hS, v, h1, ⟨s, hs, hsv⟩, h3, ⟨t0, ht0, ht0v⟩⟩ := h
  have hc : S.card = 2 := (Finset.mem_powersetCard.1 hS).2
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

theorem cy_of (y : Fin 4 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 4)) y Finset.univ_nonempty
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
  have hs2 : 2 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    rw [hU, Finset.mem_filter] at hsU
    exact hsU.2
  have hs3 : 3 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    have := h (y s)
    omega
  set L := univ.filter (fun t => y t < y s) with hL
  set E := univ.filter (fun t => y t = y s) with hE
  have hLc : L.card ≤ 1 := by
    by_cases hLne : L.Nonempty
    · obtain ⟨l, hl, hlmax⟩ := Finset.exists_max_image L y hLne
      have hyl : y l < y s := by
        rw [hL, Finset.mem_filter] at hl
        exact hl.2
      have hlU : l ∉ U := by
        intro hlU
        have := hmin l hlU
        omega
      have hcl : (univ.filter (fun t => y t ≤ y l)).card ≤ 1 := by
        rw [hU, Finset.mem_filter] at hlU
        have : ¬ 2 ≤ (univ.filter (fun t => y t ≤ y l)).card :=
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
  rcases Nat.lt_or_ge 0 L.card with hpos | hzero
  · -- one value below `y s`
    obtain ⟨l, hLl⟩ := Finset.card_eq_one.1 (by omega : L.card = 1)
    have hlL : l ∈ L := by rw [hLl]; exact Finset.mem_singleton_self l
    have hyl : y l < y s := by
      rw [hL, Finset.mem_filter] at hlL
      exact hlL.2
    have hE1 : 1 ≤ (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < (E.erase s).card)
    have hes : e ≠ s := (Finset.mem_erase.1 he).1
    have hye : y e = y s := by
      have := (Finset.mem_erase.1 he).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hls : l ≠ s := by
      rintro rfl
      omega
    refine ⟨{l, s}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e, ?_, hye⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair hls⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · rw [Finset.mem_singleton.1 ht']
    · intro t ht
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLl, Finset.mem_singleton] at htL
      apply ht
      rw [htL]
      exact Finset.mem_insert_self l {s}
    · intro he'
      rcases Finset.mem_insert.1 he' with rfl | he''
      · omega
      · exact hes (Finset.mem_singleton.1 he'')
  · -- no value below `y s`
    have hL0 : L.card = 0 := by omega
    have hE3 : 3 ≤ E.card := by omega
    have hE2 : 1 < (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e1, he1, e2, he2, he12⟩ := Finset.one_lt_card.1 hE2
    have he1s : e1 ≠ s := (Finset.mem_erase.1 he1).1
    have he2s : e2 ≠ s := (Finset.mem_erase.1 he2).1
    have hye1 : y e1 = y s := by
      have := (Finset.mem_erase.1 he1).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hye2 : y e2 = y s := by
      have := (Finset.mem_erase.1 he2).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hLempty : L = ∅ := Finset.card_eq_zero.1 hL0
    refine ⟨{s, e1}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e2, ?_, hye2⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair he1s.symm⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · exact le_rfl
      · rw [Finset.mem_singleton.1 ht', hye1]
    · intro t _
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLempty] at htL
      exact Finset.notMem_empty t htL
    · intro he'
      rcases Finset.mem_insert.1 he' with h' | h'
      · exact he2s h'
      · exact he12 (Finset.mem_singleton.1 h').symm

theorem window_iff (y : Fin 4 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 4 → ℕ) :
    ¬ Cy y ↔ ∀ v : ℕ, ¬ ((univ.filter (fun t => y t < v)).card ≤ 1 ∧
      3 ≤ (univ.filter (fun t => y t < v + 1)).card) := by
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
    have key : ∀ v, (univ.filter (fun t => y t < v)).card ≤ 1 := by
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
def fget (f : Fin 10 → Bool) (k : ℕ) : Bool := if h : k < 10 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 10 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 4 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 10 → Bool) : Prop := ∀ i < (7 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 10 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 10 → Fin (n + 1)) (v : ℕ) : Fin 10 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 10 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a250393.get x k ≤ n := by
  unfold OMA.S_oeis_a250393.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (7 : ℕ), cntW (fun _ => true) i = 4 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 10 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (7 : ℕ), ¬ Cy (fun t : Fin 4 => OMA.S_oeis_a250393.get x (i + t)) := by
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
  have step2 : ∀ i < (7 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 4 => OMA.S_oeis_a250393.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 10 := by have := t.isLt; omega
    unfold OMA.S_oeis_a250393.get fget Lt
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
noncomputable def M (n : ℕ) (T : Fin 10 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 10 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 10 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 10 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
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
def lower {n : ℕ} (x : Fin 10 → Fin (n + 2)) : Fin 10 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 10 → Bool) (x : Fin 10 → Fin (n + 1)) : Fin 10 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 10 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 10 → Bool) (x : Fin 10 → Fin (n + 1)) (p : Fin 10) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 10 → Bool) :
    M (n + 1) T = ∑ S : Fin 10 → Bool,
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
def row (u : Fin 1024) : Fin 10 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 10 → Bool) : ℕ := ∑ p : Fin 10, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 1024, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 10 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2 + m / 256 % 2 + m / 512 % 2

theorem cnt_row : ∀ u : Fin 1024, cntW (row u) 0 = pcb (u.val &&& 15) ∧
    cntW (row u) 1 = pcb (u.val &&& 30) ∧
    cntW (row u) 2 = pcb (u.val &&& 60) ∧
    cntW (row u) 3 = pcb (u.val &&& 120) ∧
    cntW (row u) 4 = pcb (u.val &&& 240) ∧
    cntW (row u) 5 = pcb (u.val &&& 480) ∧
    cntW (row u) 6 = pcb (u.val &&& 960) := by
  decide +kernel

def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 15) ≤ 1 ∧ 3 ≤ pcb (t &&& 15)) ∧
    ¬ (pcb (s &&& 30) ≤ 1 ∧ 3 ≤ pcb (t &&& 30)) ∧
    ¬ (pcb (s &&& 60) ≤ 1 ∧ 3 ≤ pcb (t &&& 60)) ∧
    ¬ (pcb (s &&& 120) ≤ 1 ∧ 3 ≤ pcb (t &&& 120)) ∧
    ¬ (pcb (s &&& 240) ≤ 1 ∧ 3 ≤ pcb (t &&& 240)) ∧
    ¬ (pcb (s &&& 480) ≤ 1 ∧ 3 ≤ pcb (t &&& 480)) ∧
    ¬ (pcb (s &&& 960) ≤ 1 ∧ 3 ≤ pcb (t &&& 960)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (7 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 1024) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, a4, a5, a6, b0, b1, b2, b3, b4, b5, b6]

theorem sub_iff (w u : Fin 1024) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 10
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (1024 : ℕ) ≤ 2 ^ i := by
          calc (1024 : ℕ) = 2 ^ 10 := by norm_num
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
def subs (u : Fin 1024) : Finset (Fin 1024) :=
  univ.filter (fun w : Fin 1024 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 1024 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 1024, M n (row u) = G n u := by
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

theorem row_full : ∀ p, row 1023 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 1023 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 10 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 1023 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 1023)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 1023 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 1023 := by
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

/-! ### The recurrence -/

theorem G_succ (n : ℕ) (u : Fin 1024) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl


/-! Packed tables certify the recursion on every state. -/
-- Each table row stores its field width followed by its packed coefficients.
def tb (T : ℕ × ℕ) (w : ℕ) : ℕ := (T.2 >>> (T.1 * w)) % 2 ^ T.1

def tabT : ℕ → ℕ × ℕ
  | 0 => (1, 0xf077f033f177f00000000000000000000077f033f177f0000007f003f177f000f077f033f177f000000000000000000000000033f177f00000000003f177f000f077f033f177f000000000000177f0000077f033f177f0000007f003f177f000f077f033f177f)
  | 1 => (7, 0xc0c183060c303060c3031818303060c1830a18303123060618183030604183060c3030a146061818303122448c1230606123060618183030604081060c303060c30318183030a14285123060612306061818303120c4891224c0c1224c0c3030606122448c12306061230606181830306040810204101060c3031818303060c1830a18303123060618183030a082850a145051224c0c3030606122448c12306061230606181830318102041830c0c1830c0c8081010183060c308101030810104040808181060c1831010183101040408081830610184080818408082020404060c081020410102041010808101060c1830a18303123060618183030604183060c3030a146061818303122448c1230606123060618183030c081020c186060c186063030606183060c308101030810104040808181060c18310101831010404080818306101840808184080820204040c0810204082020c1860630306060c183061430606308101040408080c083060c186061831010404080818306101840808184080820204040c081020c186060c1860640408080c183061840808184080820204040c083060c188080c1880820204040c183080c204040c204041010202060418302041010204101080810102040810408101061020208081010604183060c3030a146061818303122448c1230606123060618183030604081060c303060c30318183030a14285123060612306061818303181060c183101018310104040808183061018408081840808202040406040810204101060c3031818303060c1830a18303123060618183030c083060c186061831010404080818306101840808184080820204040c081020c186060c1860640408080c183061840808184080820204040c083060c188080c1880820204040c183080c204040c204041010202060c081020410102041010808101060c1830a18303123060618183030604183060c3030a14606181830318306101840808184080820204040604081060c303060c30318183030c183061840808184080820204040c083060c188080c1880820204040c183080c204040c20404101020206040810204101060c3031818303060c1830a18303184080820204040604183060c3030c1880820204040c183080c204040c2040410102020604081060c303060c3032020404060c1830c204040c2040410102020604183060c404060c4041010202060c184061020206102020808101)
  | 2 => (11, 0xe309f54c95356258d0f8b55845b51a0bc6c0480900605685dcbb8c240c4b0960645fa72ce58993962644c8335683acc08c730231c9a86742e448ee89f3ba27c4f8355b2654ca8f332a3cc7985132a3cc798511e61442881b5843547f07f328344a206c328344a206c3f02a05403842e49492896366414828573664148285720a15c2b81d5fa3fcd98e1366384ca887366384ca88732a21c4382d32a384708871c221c4382d1c221c4382d10e0b41680f56233c6e06e21021864843328344a206c3f02a0540383023446886c2422a0540383664148285720a15c2b81d40c2c8908962422587384d366384ca88732a21c4382d32a384708871c221c4382d1c221c4382d10e0b41680f6c0414990993f0414ca8873f0414ca8875b23cc798513ba4148288732a3cc7985132a3cc798511e61442881b3962648288720a21c7985120a21c798511e61442881b1e621c4385110e1442881b10e1442881b0a206c0d8095324446686a1b81d05703a1fc21866044264198330223023446886c2422a0540383664148285720a15c2b81d2ee1fc6886c1a21b05403824a2588285720a15c2b81d32a384708871c221c4382d1c221c4382d10e0b41680f4682b8660662882a0828572882a08285732a21c4382d3ba4148288732a3cc7985132a3cc798511e61442881b3962648288720a21c7985120a21c798511e61442881b1e621c4385110e1442881b10e1442881b0a206c0d80943e294570571921984c8332882a08285732a21c4382d26a2a0540571ce21c4382d32a3cc798511e61442881b2581985405715015c4382d20a21c798511e61442881b1e621c4385110e1442881b10e1442881b0a206c0d80924015c3303315015c4382d15015c4382d1e61442881b13e15c2b82d10e1442881b10e1442881b0a206c0d8091320cc2b82d0ae0b42881b0ae0b42881b0a206c0d8090a20b41681b05a06c0d80905a06c0d809036024048034fa39c8888c19e1a8528371aa1b85703a20a15c2b81d1d61fc3f843164198330221fe2644c8331320cc198112ee1fc6886c1a21b05403824a2588285720a15c2b81d32a384708871c221c4382d1c221c4382d10e0b41680f2da1b8430431a21b0540381a21b05403820a15c2b81d2242584b04d1c221c4382d1c221c4382d10e0b41680f3962648288720a21c7985120a21c798511e61442881b1e621c4385110e1442881b10e1442881b0a206c0d8092c61a83a03a10c110330221a21b05403820a15c2b81d18e1b03603812c15c2b81d1c221c4382d10e0b41680f2581985405715015c4382d20a21c798511e61442881b1e621c4385110e1442881b10e1442881b0a206c0d80924015c3303315015c4382d15015c4382d1e61442881b13e15c2b82d10e1442881b10e1442881b0a206c0d8091320cc2b82d0ae0b42881b0ae0b42881b0a206c0d8090a20b41681b05a06c0d80905a06c0d809036024048032a6230350370dc0e82b81d0fe10c330221320cc1981118e1b03603812c15c2b81d1c221c4382d10e0b41680f18410c360380d80e02b81d12c1344382d10e0b41680f1e621c4385110e1442881b10e1442881b0a206c0d8091780e8220220d80e02b81d0d80e02b81d10e0b41680f13e15c2b82d10e1442881b10e1442881b0a206c0d8091320cc2b82d0ae0b42881b0ae0b42881b0a206c0d8090a20b41681b05a06c0d80905a06c0d8090360240480316a0dc1d01d086088198110d80e02b81d10e0b41680f0ce0e01c01d09a0b41680f10e1442881b0a206c0d8090c80881c01d0700741680f0ae0b42881b0a206c0d8090a20b41681b05a06c0d80905a06c0d809036024048030c0074110110700741680f0700741680f0a206c0d80906a0740e80f05a06c0d80905a06c0d809036024048030660440e80f03a03c0d80903a03c0d8090360240480303603c0780901e0240480301e0240480301200c01801)
  | 3 => (17, 0x91901357ca2ba1b9a2a3a874244ed009da2ba48783c52a80a551c10038201c1003822b1007c6c3e360ab713a983af01d7803af1a4005000280005000a00014000a0001402b1005d5c40680b16101a02c581e9003d21477038042a0005400a80015000a800150196204ad025680720095a01c800e4001c8095a01c800e4001c8039000720039000722ba4856703242086f10e602e902010040210e602e90201004020b10016200b100162147703b681db405150a0201e800f4001e80a0201e800f4001e803d0007a003d0007a1a4003870280806e40a0201b90150002a00a0201b90150002a0054000a80054000a8095a01b900dc802a0037200a80054000a8037200a80054000a80150002a00150002a2a3a853642c6e07730cca022e8177002ee10e602e90201004020b10016200b100162101a02e9017480402075e016200b1001620a0201e800f4001e803d0007a003d0007a13a982ad01d780515075e014540df001be0a0201b90150002a0054000a80054000a8095a01b900dc802a0037200a80054000a8037200a80054000a80150002a00150002a1c1003780200005600b1001e80150002a00b1001e80150002a0080001000080001000a8001e800f4002a00540010000800010005400100008000100020000400020000400a00015800f4002a003d000a800800010003d000a800800010002000040002000040039000a800540010001500040002000040015000400020000400080001000080001028ae85ad02a0c072a0b1b81ed814b002960c90822e817d002fa08000100008000100101a02e9017480402075e016200b1001620a0201e800f4001e803d0007a003d0007a0f8d821bc1748040205d2010080b100162076d014540f4001e803d0007a003d0007a095a01b900dc802a0037200a80054000a8037200a80054000a80150002a00150002a14aa0296017d004000804016200f4001e80804016200f4001e8054000a80054000a80a8001e800f4002a00540010000800010005400100008000100020000400020000400a00015800f4002a003d000a800800010003d000a800800010002000040002000040039000a800540010001500040002000040015000400020000400080001000080001013b40272014b0037805dc010000ac001580804016200f4001e8054000a80054000a807a4016200b1001e8037c00a80054000a80540010000800010002000040002000040075e010000b1001e802c4007a0054000a803d000a800800010002000040002000040039000a8005400100015000400020000400150004000200004000800010000800010070400de00800015802c4007a0054000a802c4007a0054000a80200004000200004002a0007a003d000a801500040002000040015000400020000400080001000080001002800056003d000a800f4002a00200004000f4002a0020000400080001000080001000e4002a00150004000540010000800010005400100008000100020000400020000426af854182d6807bc0a6c81ca8139002720ace01dcc14b0029606f000de006f000de0bab821bc10de02ee055a0100008000100070e015800ac0015802b00056002b000560f8d821bc1748040205d2010080b100162076d014540f4001e803d0007a003d0007a095a01b900dc802a0037200a80054000a8037200a80054000a80150002a00150002a0f0781dcc117402ee05d2010080b10016205d2010080b10016203d0007a003d0007a0700814540a2a01be037200a80054000a8037200a80054000a80150002a00150002a0a00015800f4002a003d000a800800010003d000a800800010002000040002000040039000a80054001000150004000200004001500040002000040008000100008000100e8481ca80f6c0296045d00be80800010005d2010080b10016203d0007a003d0007a058b0100808040162028a807a003d0007a037200a80054000a80150002a00150002a075e010000b1001e802c4007a0054000a803d000a800800010002000040002000040039000a8005400100015000400020000400150004000200004000800010000800010070400de00800015802c4007a0054000a802c4007a0054000a80200004000200004002a0007a003d000a801500040002000040015000400020000400080001000080001002800056003d000a800f4002a00200004000f4002a0020000400080001000080001000e4002a0015000400054001000080001000540010000800010002000040002000040dcd01ef00e54027203b980a5806f000de043780bb80800010002b00056002b00056058b0100808040162028a807a003d0007a037200a80054000a80150002a00150002a055b80bb80804016202010058803d0007a028a806f8054000a80150002a00150002a039000a8005400100015000400020000400150004000200004000800010000800010052a80a5805f4010002010058803d0007a02010058803d0007a0150002a00150002a02a0007a003d000a801500040002000040015000400020000400080001000080001002800056003d000a800f4002a00200004000f4002a0020000400080001000080001000e4002a00150004000540010000800010005400100008000100020000400020000404ed009c8052c00de01770040002b0005602010058803d0007a0150002a00150002a01e90058802c4007a00df002a00150002a015000400020000400080001000080001001d78040002c4007a00b1001e80150002a00f4002a0020000400080001000080001000e4002a00150004000540010000800010005400100008000100020000400020000401c1003780200005600b1001e80150002a00b1001e80150002a0080001000080001000a8001e800f4002a00540010000800010005400100008000100020000400020000400a00015800f4002a003d000a800800010003d000a800800010002000040002000040039000a800540010001500040002000040015000400020000400080001000080001)
  | 4 => (21, 0x8de1a0f12147e802100d220c3f8435e82abf20446521df9845b802ccae047ab0e371016be80b5f4012322198c8482342411a04a3f0ad5e817da40bed2013150d9f801e4600f2300183803c8c0060e003070004d82198c83acd82552e04ccb0954b81332c0c5a8013c40b4160171040fde80196403f7a006590032c8005140d4b201d0100e8080203a03a020080e8040740067203a020080e804074006720101d0019c800ce40014a21df98375981f51403f2c09bd30140b80ce40014a009bd30140b80ce40014a004268006a4003520005500b4160183980c1cc018d303d860088b80445c006d603d860088b80445c006d601117001b5800dac0015e0d9f8017bb00f61801fa403d86007e90057e4008ca03d86007e90057e4008ca015f900232801194001c203a02007e9003f48008ca00fd200232801194001c200fd200232801194001c200465000708003840005a20c3f8356a81c4820390207e820102f40a3480105409bd30140b80ce40014a004268006a4003520005500954b8140b80a05c014a003036806a40035200055003d860088b80445c006d601117001b5800dac0015e0ad5e8130180c0da018d30303680634c03fac0065e03d86007e90057e4008ca015f900232801194001c203a02007e9003f48008ca00fd200232801194001c200fd200232801194001c200465000708003840005a0e3710173180d0fc01a5e042680088b8057e4008ca042680088b8057e4008ca01e848030d40186a0027103f7a0088b80445c008ca015f90030d40186a00271015f90030d40186a002710061a8009c4004e20007d03c8c0069780445c008ca011170023280186a00271011170023280186a002710061a8009c4004e20007d0101d0023280119400271004650009c4004e20007d004650009c4004e20007d001388001f4000fa000191fa00836d581b028036ee0712080e9c00934400eba07d450102f40a5a0010900343f005398029cc0042e0954b8140b80a05c014a003036806a40035200055003d860088b80445c006d601117001b5800dac0015e0904680fcb00a05c014a00281700528003520005500307300634c0445c006d601117001b5800dac0015e03a02007e9003f48008ca00fd200232801194001c200fd200232801194001c200465000708003840005a0b32b8126880a5a0014e603390006a400445c006d603390006a400445c006d6015f900232801194001c203f7a0088b80445c008ca015f90030d40186a00271015f90030d40186a002710061a8009c4004e20007d03c8c0069780445c008ca011170023280186a00271011170023280186a002710061a8009c4004e20007d0101d0023280119400271004650009c4004e20007d004650009c4004e20007d001388001f4000fa000190aafc811788093440128e028d2005398034bc0054603390006a400445c006d6015f900232801194001c20316a006a4003520006d600feb00232801194001c2015f90030d40186a002710061a8009c4004e20007d02fb480539803520006d600d48001b5801194001c2011170023280186a002710061a8009c4004e20007d0101d0023280119400271004650009c4004e20007d004650009c4004e20007d001388001f4000fa0001902d7d004a38029cc0054600d48001b5801194001c200d48001b5801194001c20061a8009c4004e20007d00cb2001b5800dac001c2004650009c4004e20007d004650009c4004e20007d001388001f4000fa0001900c1c00151800dac001c20036b000708004e20007d0036b000708004e20007d001388001f4000fa0001900339000708003840007d000e10001f4000fa00019000e10001f4000fa000190003e80006400032000051e242833d981b6ac037ce06ad500dbb808bc400dfa06eb300e4080934400eba02e63004a380251c003b60759b00fcb007e580105402603005398029cc0042e02f76006978034bc0054600d2f00151800a8c0010e0904680fcb00a05c014a00281700528003520005500307300634c0445c006d601117001b5800dac0015e03a02007e9003f48008ca00fd200232801194001c200fd200232801194001c200465000708003840005a08b7000e4080817a0105402817005280035200055002817005280035200055001117001b5800dac0015e02e2080634c031a60065e00fd200232801194001c200fd200232801194001c200465000708003840005a03c8c0069780445c008ca011170023280186a00271011170023280186a002710061a8009c4004e20007d0101d0023280119400271004650009c4004e20007d004650009c4004e20007d001388001f4000fa00019086bd00dbb8074e000eba0205e804240029cc0042e02817005280035200055001117001b5800dac0015e02665805280029400055000c69801b5800dac0015e00fd200232801194001c200465000708003840005a02fb480539803520006d600d48001b5801194001c2011170023280186a002710061a8009c4004e20007d0101d0023280119400271004650009c4004e20007d004650009c4004e20007d001388001f4000fa0001902d7d004a38029cc0054600d48001b5801194001c200d48001b5801194001c20061a8009c4004e20007d00cb2001b5800dac001c2004650009c4004e20007d004650009c4004e20007d001388001f4000fa0001900c1c00151800dac001c20036b000708004e20007d0036b000708004e20007d001388001f4000fa0001900339000708003840007d000e10001f4000fa00019000e10001f4000fa000190003e80006400032000050806900df3806ddc00dfa01c81003ae80251c003b601f96004150029cc0042e00d2f00151800a8c0010e02665805280029400055000c69801b5800dac0015e00fd200232801194001c200465000708003840005a0251f804150029400055000a5000154000dac0015e00c6980197801194001c200465000708003840005a0101d0023280119400271004650009c4004e20007d004650009c4004e20007d001388001f4000fa00019023d5803ae8021200042e00a5000154000dac0015e00a5000154000dac0015e00465000708003840005a00cb2001b5800dac001c2004650009c4004e20007d004650009c4004e20007d001388001f4000fa0001900c1c00151800dac001c20036b000708004e20007d0036b000708004e20007d001388001f4000fa0001900339000708003840007d000e10001f4000fa00019000e10001f4000fa000190003e8000640003200005022328037e801d74003b60082a0010b800a8c0010e00a5000154000dac0015e00465000708003840005a009e200154000aa00015e0032f000708003840005a004650009c4004e20007d001388001f4000fa000190098a8010b800aa00015e002a8000578003840005a0036b000708004e20007d001388001f4000fa0001900339000708003840007d000e10001f4000fa00019000e10001f4000fa000190003e800064000320000500919000ed80085c0010e002a8000578003840005a002a8000578003840005a001388001f4000fa000190028a000578002bc0005a000e10001f4000fa00019000e10001f4000fa000190003e80006400032000050026c000438002bc0005a000af000168000fa00019000af000168000fa000190003e8000640003200005000a5000168000b4000190002d00006400032000050002d00006400032000050000c8000140000a00001)
  | 5 => (24, 0x9bb0561b75de1cb26a05d0551da5b00613620762d2013b231e97300645fa07b69c01491a0960e40190260190260042b11e6ecb067a12067a1201540c07880e01a22001a2200045b00919fb01fc5c01fc5c0054ba01fc5c0054ba0054ba000e1f1e6ecb05880406af63015edb06af63015edb01afd60047f907cb850197f00212dc00587a0212dc00587a00587a000ebf08ee0901ed1101ed11006b9401ed11006b94006b940011ee01ed11006b94006b940011ee006b940011ee0011ee0002fd1e97300543e105d6aa012d8806f0b7016c5701c03e004ab506f0b7016c5701c03e004ab50227f4005bfe005bfe000f5507cb8501a94701a9470056f40206d90071340071340012de0206d90071340071340012de0071340012de0012de0003250919fb01a62b0206d9006a590206d9006a59008b380017340206d9006a59008b38001734008b380017340017340003de01ed11006a59006a59001734006a590017340017340003de006a590017340017340003de0017340003de0003de0000a51da5b0051802055bb401149405dff5013351017412003e0306f0b7016c5701c03e004ab50227f4005bfe005bfe000f5506af63016c57016c57004ab501a7e3005bfe005bfe000f550206d90071340071340012de0071340012de0012de00032507880e015ede01a7e30056f401a7e30056f4006ac20011cb0206d9006a59008b38001734008b380017340017340003de01ed11006a59006a59001734006a590017340017340003de006a590017340017340003de0017340003de0003de0000a50960e4019cbc01c854005c1c0227f4007134008b380017340227f4007134008b3800173400b640001e60001e600005100212dc007134007134001734008b38001e60001e60000510008b38001e60001e60000510001e600005100005100000d801fc5c005c1c007134001734007134001734001e60000510007134001734001e60000510001e600005100005100000d8006b940017340017340005100017340005100005100000d80017340005100005100000d80005100000d80000d80000241cb26a051cbd05267f010b53055bb40119ef0155220038db05d6aa0133510178c2003ecb01c854004c0e004c0e000cad06af63016c57016c57004ab501a7e3005bfe005bfe000f550206d90071340071340012de0071340012de0012de000325067a12012d88016c57004ab5016c57004ab5005bfe000f5501a9470056f40071340012de0071340012de0012de00032501ed11006a59006a59001734006a590017340017340003de006a590017340017340003de0017340003de0003de0000a507b69c0155220178c2004c0e01c03e005bfe0071340012de01c03e005bfe0071340012de008b380017340017340003de0212dc007134007134001734008b38001e60001e60000510008b38001e60001e60000510001e600005100005100000d801fc5c005c1c007134001734007134001734001e60000510007134001734001e60000510001e600005100005100000d8006b940017340017340005100017340005100005100000d80017340005100005100000d80005100000d80000d80000240762d20145620155220044ca017412004c0e005c1c000f5a01c03e005bfe0071340012de008b380017340017340003de01afd6005bfe005bfe0012de006ac20017340017340003de008b38001e60001e60000510001e600005100005100000d801a220004c0e005bfe0012de005bfe0012de0017340003de007134001734001e60000510001e600005100005100000d8006b940017340017340005100017340005100005100000d80017340005100005100000d80005100000d80000d80000240190260044ca004c0e000f5a005bfe0012de0017340003de005bfe0012de0017340003de001e600005100005100000d800587a0012de0012de0003de0017340005100005100000d80017340005100005100000d80005100000d80000d80000240054ba000f5a0012de0003de0012de0003de0005100000d80012de0003de0005100000d80005100000d80000d80000240011ee0003de0003de0000d80003de0000d80000d80000240003de0000d80000d80000240000d80000240000240000061b75de04e0cf051cbd010993051802010b5301456200363b0543e10114940155220038db019cbc0044ca0044ca000b77058804012d88012d88003e03015ede004c0e004c0e000cad01a62b005c1c005c1c000f5a005c1c000f5a000f5a00028f067a12012d88016c57004ab5016c57004ab5005bfe000f5501a9470056f40071340012de0071340012de0012de00032501ed11006a59006a59001734006a590017340017340003de006a590017340017340003de0017340003de0003de0000a50645fa011494013351003e03016c57004ab5005bfe000f55016c57004ab5005bfe000f550071340012de0012de0003250197f00056f40056f40011cb006a590017340017340003de006a590017340017340003de0017340003de0003de0000a501fc5c005c1c007134001734007134001734001e60000510007134001734001e60000510001e600005100005100000d8006b940017340017340005100017340005100005100000d80017340005100005100000d80005100000d80000d8000024061362010b530119ef0038db013351003ecb004c0e000cad016c57004ab5005bfe000f550071340012de0012de000325015edb004ab5004ab5000f550056f40012de0012de000325006a590017340017340003de0017340003de0003de0000a501a220004c0e005bfe0012de005bfe0012de0017340003de007134001734001e60000510001e600005100005100000d8006b940017340017340005100017340005100005100000d80017340005100005100000d80005100000d80000d80000240190260044ca004c0e000f5a005bfe0012de0017340003de005bfe0012de0017340003de001e600005100005100000d800587a0012de0012de0003de0017340005100005100000d80017340005100005100000d80005100000d80000d80000240054ba000f5a0012de0003de0012de0003de0005100000d80012de0003de0005100000d80005100000d80000d80000240011ee0003de0003de0000d80003de0000d80000d80000240003de0000d80000d80000240000d800002400002400000605d055010993010b5300363b0114940038db0044ca000b77012d88003e03004c0e000cad005c1c000f5a000f5a00028f015edb004ab5004ab5000f550056f40012de0012de000325006a590017340017340003de0017340003de0003de0000a501540c003e03004ab5000f55004ab5000f550012de0003250056f40011cb0017340003de0017340003de0003de0000a5006b940017340017340005100017340005100005100000d80017340005100005100000d80005100000d80000d800002401491a0038db003ecb000cad004ab5000f550012de000325004ab5000f550012de0003250017340003de0003de0000a500587a0012de0012de0003de0017340005100005100000d80017340005100005100000d80005100000d80000d80000240054ba000f5a0012de0003de0012de0003de0005100000d80012de0003de0005100000d80005100000d80000d80000240011ee0003de0003de0000d80003de0000d80000d80000240003de0000d80000d80000240000d8000024000024000006013b2300363b0038db000b77003e03000cad000f5a00028f004ab5000f550012de0003250017340003de0003de0000a50047f9000f55000f550003250011cb0003de0003de0000a50017340005100005100000d80005100000d80000d80000240045b0000cad000f55000325000f550003250003de0000a50012de0003de0005100000d80005100000d80000d80000240011ee0003de0003de0000d80003de0000d80000d80000240003de0000d80000d80000240000d80000240000240000060042b1000b77000cad00028f000f550003250003de0000a5000f550003250003de0000a50005100000d80000d8000024000ebf0003250003250000a50003de0000d80000d80000240003de0000d80000d80000240000d8000024000024000006000e1f00028f0003250000a50003250000a50000d80000240003250000a50000d80000240000d80000240000240000060002fd0000a50000a50000240000a50000240000240000060000a5000024000024000006000024000006000006000001)
  | 6 => (26, 0xe9dc0308cd38824a4fb818b4b125c008019b7250795e980455aa26db9b41a7ba307e46fc048289095040805526e01549b800c2a226ba1bc1b45a006d168004a59707bf904058a21016288400ca97091ae5c06897701a25dc00ef1101a25dc00ef11003bc4400222726ba1bc17fd6f07047f804c81207047f804c812016d0f400d09b07fdcc4056f0101b31d400f8a301b31d400f8a3003e28c00238508f70240662cd0198b3401256d0198b3401256d00495b40029eb0198b3401256d00495b40029eb00495b40029eb000a7ac0005fd26db9b417040f06492a80439b10740ca804f163017943000d7940740ca804f163017943000d79401c230001014000405000024c007fdcc405a1eb01687ac00f52301ab5cc0132d3004cb4c002bd501ab5cc0132d3004cb4c002bd5004cb4c002bd5000af54000643091ae5c05a0b701ab5cc01232101ab5cc012321005b71c00344101ab5cc012321005b71c003441005b71c003441000d1040007770198b340123210048c840034410048c84003441000d1040007770048c84003441000d104000777000d1040007770001ddc00011125c008016544b05d6af403ec560650040044a97014324400b8a70740ca804f163017943000d79401c230001014000405000024c007047f804f163013c58c00d7940167a3801014000405000024c001ab5cc0132d3004cb4c002bd5004cb4c002bd5000af5400064307bf90404cdb40167a3800f5230167a3800f5230048f940029b301ab5cc012321005b71c003441005b71c003441000d1040007770198b340123210048c840034410048c84003441000d1040007770048c84003441000d104000777000d1040007770001ddc00011109504080582db018089001029701c23000132d3005b71c00344101c23000132d3005b71c0034410072e440041a7001069c00096101b31d40132d3004cb4c003441005b71c0041a7001069c000961005b71c0041a7001069c000961001069c000961000258400015701a25dc010297004cb4c003441004cb4c003441001069c000961004cb4c003441001069c000961001069c000961000258400015700495b4003441000d104000961000d1040009610002584000157000d10400096100025840001570002584000157000055c00003124a4fb816312105a3c5403cdc405d6af403fc24012bef000ab6406492a8044a970146bb000bab4018089000dbbc0036ef0001f6407047f804f163013c58c00d7940167a3801014000405000024c001ab5cc0132d3004cb4c002bd5004cb4c002bd5000af5400064306d16800439b1013c58c00d794013c58c00d79400405000024c001687ac00f523004cb4c002bd5004cb4c002bd5000af540006430198b340123210048c840034410048c84003441000d1040007770048c84003441000d104000777000d1040007770001ddc00011107e46fc04afbc0146bb000dbbc0179430010140004cb4c002bd50179430010140004cb4c002bd5005b71c003441000d10400077701b31d40132d3004cb4c003441005b71c0041a7001069c000961005b71c0041a7001069c000961001069c000961000258400015701a25dc010297004cb4c003441004cb4c003441001069c000961004cb4c003441001069c000961001069c000961000258400015700495b4003441000d104000961000d1040009610002584000157000d10400096100025840001570002584000157000055c0000310795e98047dc7012bef000c98d014324400dbbc0040a5c0024f10179430010140004cb4c002bd5005b71c003441000d104000777016d0f40101400040500002bd50048f94003441000d104000777005b71c0041a7001069c000961001069c0009610002584000157016288400dbbc0040500002bd50040500002bd5000d104000777004cb4c003441001069c000961001069c000961000258400015700495b4003441000d104000961000d1040009610002584000157000d10400096100025840001570002584000157000055c00003101549b800c98d0036ef00024f10040500002bd5000d1040007770040500002bd5000d104000777001069c0009610002584000157003e28c002bd5000af54000777000d1040009610002584000157000d10400096100025840001570002584000157000055c000031003bc440024f1000af54000777000af540007770002584000157000af5400077700025840001570002584000157000055c000031000a7ac0007770001ddc0001570001ddc000157000055c0000310001ddc000157000055c000031000055c00003100000c40000072334e20154c35058c48403be9e059512c03cdc4011f71c00a44105c103c03ec56012bef000ab640160b6c00c98d0032634001ccb05ff5bc0439b1010e6c400b8a701336d000dbbc0036ef0001f6401682dc0102970040a5c0024f10040a5c0024f100093c400054706d16800439b1013c58c00d794013c58c00d79400405000024c001687ac00f523004cb4c002bd5004cb4c002bd5000af540006430198b340123210048c840034410048c84003441000d1040007770048c84003441000d104000777000d1040007770001ddc000111069ee8c03ec560112a5c00b8a7013c58c00d79400405000024c0013c58c00d79400405000024c0004cb4c002bd5000af54000643015bc0400f523003d48c0029b30048c84003441000d1040007770048c84003441000d104000777000d1040007770001ddc00011101a25dc010297004cb4c003441004cb4c003441001069c000961004cb4c003441001069c000961001069c000961000258400015700495b4003441000d104000961000d1040009610002584000157000d10400096100025840001570002584000157000055c000031066dc9403cdc400ff09000ab640112a5c00bab40036ef0001f64013c58c00d79400405000024c0004cb4c002bd5000af54000643013204800d7940035e500024c0003d48c002bd5000af540006430048c84003441000d104000777000d1040007770001ddc000111016288400dbbc0040500002bd50040500002bd5000d104000777004cb4c003441001069c000961001069c000961000258400015700495b4003441000d104000961000d1040009610002584000157000d10400096100025840001570002584000157000055c00003101549b800c98d0036ef00024f10040500002bd5000d1040007770040500002bd5000d104000777001069c0009610002584000157003e28c002bd5000af54000777000d1040009610002584000157000d10400096100025840001570002584000157000055c000031003bc440024f1000af54000777000af540007770002584000157000af5400077700025840001570002584000157000055c000031000a7ac0007770001ddc0001570001ddc000157000055c0000310001ddc000157000055c000031000055c00003100000c4000007062d2c403be9e00f371000a44100fb15800ab640032634001ccb010e6c400b8a70036ef0001f640040a5c0024f100093c4000547013204800d7940035e500024c0003d48c002bd5000af540006430048c84003441000d104000777000d1040007770001ddc000111012965c00b8a70035e500024c00035e500024c0000af54000643003d48c0029b3000d104000777000d1040007770001ddc00011100495b4003441000d104000961000d1040009610002584000157000d10400096100025840001570002584000157000055c0000310120a2400ab64002ead0001f640035e500024c0000af540006430035e500024c0000af54000643000d1040007770001ddc000111003e28c002bd5000af54000777000d1040009610002584000157000d10400096100025840001570002584000157000055c000031003bc440024f1000af54000777000af540007770002584000157000af5400077700025840001570002584000157000055c000031000a7ac0007770001ddc0001570001ddc000157000055c0000310001ddc000157000055c000031000055c00003100000c400000701156a800a441002ad90001ccb002e29c001f6400093c40005470035e500024c0000af54000643000d1040007770001ddc000111003426c0024c00009300000643000a6cc0007770001ddc000111000d10400096100025840001570002584000157000055c0000310032a5c001f64000930000064300093000006430001ddc000111000af5400077700025840001570002584000157000055c000031000a7ac0007770001ddc0001570001ddc000157000055c0000310001ddc000157000055c000031000055c00003100000c40000070030a88001ccb0007d9000054700093000006430001ddc00011100093000006430001ddc0001110002584000157000055c0000310008e14000643000190c0001110001ddc000157000055c0000310001ddc000157000055c000031000055c00003100000c4000007000889c000547000190c000111000190c000111000055c000031000190c000111000055c000031000055c00003100000c400000700017f40001110000444000031000044400003100000c4000007000044400003100000c400000700000c4000007000001c000001)
  | 7 => (29, 0x865700008cffde8491d88c054656412c8237015e1df80ca13c000ca13c1349afb0167aea80d1866000d186603c7880003c788001e3c40001e3c4133e91401717ec80b8bf6400d75420339bb5003eb84001f5c20001f5c203b655000486800024340000243400090d0000090d0000486800004868133e914014bb7680bdaaa000dd03402f6aa8003740d00203440002034403510c2003dbc7802584000025840009610000096100004b0800004b0803a9fc800470f4002387a0002b500008e1e8000ad4000056a0000056a0008e1e8000ad4000056a0000056a00015a8000015a80000ad400000ad41349afb014016000acddac00c719a030d4b00038e8c002129400021294030d4b00038e8c002129400021294009aa800009aa80004d5400004d5403510c2003fb75001fdba800251160093dc8000b4400005a2000005a200093dc8000b4400005a2000005a20001688000016880000b4400000b4403b6550003fe1c0024f720002b1100093dc8000ac440006900000069000093dc8000ac44000690000006900001a4000001a400000d2000000d20008e1e8000ac4400056220000690000158880001a400000d2000000d2000158880001a400000d2000000d200003480000034800001a4000001a412c823701375a980a20dd400ba97202b59a000326e3001d0bc0001d0bc030d4b00038e8c002129400021294009aa800009aa80004d5400004d5402f6aa80038e8c001c74600021294007f35c0009aa80004d5400004d540093dc8000b4400005a2000005a20001688000016880000b4400000b440339bb50037a0a001fcd700025116007f35c0009445800564c0000564c0093dc8000ac44000690000006900001a4000001a400000d2000000d20008e1e8000ac4400056220000690000158880001a400000d2000000d2000158880001a400000d2000000d200003480000034800001a4000001a403c7880003eac00021cc000026f00009aa80000b440000690000006900009aa80000b440000690000006900002000000020000001000000010000096100000b4400005a2000006900001a4000002000000100000001000001a4000002000000100000001000000400000004000000200000002000090d000009bc00005a200000690000168800001a4000010000000100000168800001a40000100000001000000400000004000000200000002000015a800001a400000d2000001000000348000004000000200000002000003480000040000002000000020000008000000080000004000000040124762301340b6009d237800b56b40288375002f43f001b36c0001b36c02b376b00326e3001d5540001d5540087300000873000043980000439802f6aa80038e8c001c74600021294007f35c0009aa80004d5400004d540093dc8000b4400005a2000005a20001688000016880000b4400000b4402e2fd90031c66801c746000212940071d1800084a50004d5400004d54007f6ea00094458005a2000005a20001688000016880000b4400000b44008e1e8000ac4400056220000690000158880001a400000d2000000d2000158880001a400000d2000000d200003480000034800001a4000001a4034619800366d8001d55400021cc00084a500009aa80005a2000005a200084a500009aa80005a2000005a20001a4000001a400000d2000000d200096100000b4400005a2000006900001a4000002000000100000001000001a4000002000000100000001000000400000004000000200000002000090d000009bc00005a200000690000168800001a4000010000000100000168800001a40000100000001000000400000004000000200000002000015a800001a400000d200000100000034800000400000020000000200000348000004000000200000002000000800000008000000400000004003284f00034608001b36c0001f56000742f000087300004de000004de00084a500009aa80005a2000005a20001a4000001a400000d2000000d200080d100009aa80004d5400005a2000159300001a400000d2000000d20001a400000200000010000000100000040000000400000020000000200007d70800087300004d5400005a20001355000016880000d2000000d2000168800001a40000100000001000000400000004000000200000002000015a800001a400000d20000010000003480000040000002000000020000034800000400000020000000200000080000000800000040000000400078f100007d58000439800004de0001355000016880000d2000000d20001355000016880000d2000000d20000400000004000000200000002000012c2000016880000b4400000d2000034800000400000020000000200000348000004000000200000002000000800000008000000400000004000121a000013780000b4400000d200002d1000003480000200000002000002d100000348000020000000200000080000000800000040000000400002b50000034800001a400000200000069000000800000040000000400000690000008000000400000004000001000000010000000800000008119ffbd0128e67009a05b000b1ed0026eb53002d5ad001a3040001a30402802c0002ea5c801b36c0001b36c007d5800007d580003eac00003eac02976ed0031c668018e334001d0bc006f4140008730000439800004398007fc380009bc00004de000004de00013780000137800009bc000009bc02e2fd90031c66801c746000212940071d1800084a50004d5400004d54007f6ea00094458005a2000005a20001688000016880000b4400000b44008e1e8000ac4400056220000690000158880001a400000d2000000d2000158880001a400000d2000000d200003480000034800001a4000001a402cf5d5002ea5c80193718001d0bc0071d1800084a50004d5400004d540071d1800084a50004d5400004d54001688000016880000b4400000b44007b78f00094458004a22c000564c00158880001a400000d2000000d2000158880001a400000d2000000d200003480000034800001a4000001a40090d000009bc00005a200000690000168800001a4000010000000100000168800001a40000100000001000000400000004000000200000002000015a800001a400000d200000100000034800000400000020000000200000348000004000000200000002000000800000008000000400000004002bc3bf002d5ad0017a1f8001b36c0064dc600075550004398000043980071d1800084a50004d5400004d54001688000016880000b4400000b44006e81a00084a5000425280004d54001288b00016880000b4400000b4400158880001a400000d2000000d200003480000034800001a4000001a4007d70800087300004d5400005a20001355000016880000d2000000d2000168800001a40000100000001000000400000004000000200000002000015a800001a400000d20000010000003480000040000002000000020000034800000400000020000000200000080000000800000040000000400078f100007d58000439800004de0001355000016880000d2000000d20001355000016880000d2000000d20000400000004000000200000002000012c2000016880000b4400000d2000034800000400000020000000200000348000004000000200000002000000800000008000000400000004000121a000013780000b4400000d200002d1000003480000200000002000002d100000348000020000000200000080000000800000040000000400002b50000034800001a40000020000006900000080000004000000040000069000000800000040000000400000100000001000000080000000802a32b2002c7b40016ad68001a304005d4b90006cdb0003eac00003eac00638cd000742f0004398000043980013780000137800009bc000009bc006e81a00084a5000425280004d54001288b00016880000b4400000b4400158880001a400000d2000000d200003480000034800001a4000001a4006baa1000742f000425280004d54001094a00013550000b4400000b44001288b00015930000d2000000d200003480000034800001a4000001a40015a800001a400000d20000010000003480000040000002000000020000034800000400000020000000200000080000000800000040000000400068c330006cdb0003aaa80004398001094a00013550000b4400000b44001094a00013550000b4400000b440003480000034800001a4000001a40012c2000016880000b4400000d2000034800000400000020000000200000348000004000000200000002000000800000008000000400000004000121a000013780000b4400000d200002d1000003480000200000002000002d100000348000020000000200000080000000800000040000000400002b50000034800001a400000200000069000000800000040000000400000690000008000000400000004000001000000010000000800000008006509e00068c1000366d80003eac000e85e00010e600009bc000009bc001094a00013550000b4400000b440003480000034800001a4000001a400101a2000135500009aa80000b440002b26000034800001a4000001a40003480000040000002000000020000008000000080000004000000040000fae100010e600009aa80000b4400026aa00002d100001a4000001a40002d100000348000020000000200000080000000800000040000000400002b50000034800001a400000200000069000000800000040000000400000690000008000000400000004000001000000010000000800000008000f1e20000fab0000873000009bc00026aa00002d100001a4000001a400026aa00002d100001a4000001a400008000000080000004000000040000258400002d10000168800001a40000690000008000000400000004000006900000080000004000000040000010000000100000008000000080002434000026f0000168800001a400005a2000006900000400000004000005a2000006900000400000004000001000000010000000800000008000056a000006900000348000004000000d2000001000000080000000800000d2000001000000080000000800000200000002000000100000001)
  | 8 => (30, 0xfcf1aca0758fd361e62bb180f543241f26b0280fd92b4047f56f801ffb4e1fec42a8103ede004a625480210f42054708f0025875c00961d700042b7c1fdfcad810a6fee0429bfb8021e5da04977af8026cdae009b36b80044fbe0533478002c0cb800b032e0004e4f800b032e0004e4f8001393e00008b381fdfcad80f2c5a40443a7c8022b7320443a7c8022b732009f05400046ad004b58c2002649f600b603400050e5000b603400050e50001439400008fd00524544002b5e1000ad7840005bd6400ad7840005bd640016f590000a34400ad7840005bd640016f590000a3440016f590000a34400028d1000012241fec42a80eb4a0c03efa21001fb7980460e450023a63c00a3440000489000460e450023a63c00a34400004890000baff0000531c00014c70000093c004b58c20027615c009d857000500e200b3bec0005f28c0017ca30000a92c00b3bec0005f28c0017ca30000a92c0017ca30000a92c0002a4b000012cc053347800278eb000b3bec0005b71000b3bec0005b710001b3b10000c1a400b3bec0005b710001b3b10000c1a4001b3b10000c1a400030690000158400ad7840005b7100016dc40000c1a40016dc40000c1a40003069000015840016dc40000c1a40003069000015840003069000015840000561000002641f26b0280e5674c03b776f801df12403f1ff2002013f600916a400040a100460e450023a63c00a34400004890000baff0000531c00014c70000093c00443a7c8023a63c008e98f00048900009d4ef800531c00014c70000093c000b3bec0005f28c0017ca30000a92c0017ca30000a92c0002a4b000012cc04977af8022fc74009d4ef800500e2009d4ef800500e20016e4b0000a2cc00b3bec0005b710001b3b10000c1a4001b3b10000c1a400030690000158400ad7840005b7100016dc40000c1a40016dc40000c1a40003069000015840016dc40000c1a4000306900001584000306900001584000056100000264054708f0026df9c00a64a900053c4c00baff00005f28c001b3b10000c1a400baff00005f28c001b3b10000c1a400206fc4000e6a900039aa400019a100b60340005f28c0017ca30000c1a4001b3b10000e6a900039aa400019a1001b3b10000e6a900039aa400019a100039aa400019a10000668400002d900b032e00053c4c0017ca30000c1a40017ca30000c1a400039aa400019a10017ca30000c1a400039aa400019a100039aa400019a10000668400002d90016f590000c1a40003069000019a10003069000019a10000668400002d90003069000019a10000668400002d90000668400002d900000b6400000511e62bb180e27e14039d794001d2ee403b776f801e48c000893f70003cffc03efa21002013f60092b500004134000a64a900049e8400127a1000083640443a7c8023a63c008e98f00048900009d4ef800531c00014c70000093c000b3bec0005f28c0017ca30000a92c0017ca30000a92c0002a4b000012cc0429bfb801fb798008e98f00048900008e98f000489000014c70000093c0009d857000500e20017ca30000a92c0017ca30000a92c0002a4b000012cc00ad7840005b7100016dc40000c1a40016dc40000c1a40003069000015840016dc40000c1a400030690000158400030690000158400005610000026404a625480224fdc0092b5000049e8400a3440000531c00017ca30000a92c00a3440000531c00017ca30000a92c001b3b10000c1a400030690000158400b60340005f28c0017ca30000c1a4001b3b10000e6a900039aa400019a1001b3b10000e6a900039aa400019a100039aa400019a10000668400002d900b032e00053c4c0017ca30000c1a40017ca30000c1a400039aa400019a10017ca30000c1a400039aa400019a100039aa400019a10000668400002d90016f590000c1a40003069000019a10003069000019a10000668400002d90003069000019a10000668400002d90000668400002d900000b640000051047f56f802122a400893f7000451bc00916a400049e840014f13000094ec00a3440000531c00017ca30000a92c001b3b10000c1a4000306900001584009f054000531c00014c700000a92c0016e4b0000c1a4000306900001584001b3b10000e6a900039aa400019a100039aa400019a10000668400002d9009b36b80049e840014c700000a92c0014c700000a92c0003069000015840017ca30000c1a400039aa400019a100039aa400019a10000668400002d90016f590000c1a40003069000019a10003069000019a10000668400002d90003069000019a10000668400002d90000668400002d900000b64000005100961d7000451bc00127a1000094ec0014c700000a92c0003069000015840014c700000a92c00030690000158400039aa400019a10000668400002d900143940000a92c0002a4b000015840003069000019a10000668400002d90003069000019a10000668400002d90000668400002d900000b640000051001393e000094ec0002a4b000015840002a4b000015840000668400002d90002a4b000015840000668400002d90000668400002d900000b64000005100028d1000015840000561000002d90000561000002d900000b6400000510000561000002d900000b64000005100000b6400000510000014400000091d63f4d80db0c0c0389f85001c94f403959d3001d2ee400848a90003ae8403ad283001df12400893f70003cffc009b7e7000451bc001146f00007adc03cb169001fb798007ede600040a10008bf1d00049e8400127a100008364009e3ac00053c4c0014f13000094ec0014f13000094ec000253b0000108c0429bfb801fb798008e98f00048900008e98f000489000014c70000093c0009d857000500e20017ca30000a92c0017ca30000a92c0002a4b000012cc00ad7840005b7100016dc40000c1a40016dc40000c1a40003069000015840016dc40000c1a4000306900001584000306900001584000056100000264040fb78001df12400804fd80040a10008e98f000489000014c70000093c0008e98f000489000014c70000093c00017ca30000a92c0002a4b000012cc009927d800500e200140388000a2cc0016dc40000c1a40003069000015840016dc40000c1a400030690000158400030690000158400005610000026400b032e00053c4c0017ca30000c1a40017ca30000c1a400039aa400019a10017ca30000c1a400039aa400019a100039aa400019a10000668400002d90016f590000c1a40003069000019a10003069000019a10000668400002d90003069000019a10000668400002d90000668400002d900000b64000005103f64ad001d2ee400792300003cffc00804fd8004134000127a100008364008e98f000489000014c70000093c00017ca30000a92c0002a4b000012cc008adcc800489000012240000093c000140388000a92c0002a4b000012cc0016dc40000c1a4000306900001584000306900001584000056100000264009b36b80049e840014c700000a92c0014c700000a92c0003069000015840017ca30000c1a400039aa400019a100039aa400019a10000668400002d90016f590000c1a40003069000019a10003069000019a10000668400002d90003069000019a10000668400002d90000668400002d900000b64000005100961d7000451bc00127a1000094ec0014c700000a92c0003069000015840014c700000a92c00030690000158400039aa400019a10000668400002d900143940000a92c0002a4b000015840003069000019a10000668400002d90003069000019a10000668400002d90000668400002d900000b640000051001393e000094ec0002a4b000015840002a4b000015840000668400002d90002a4b000015840000668400002d90000668400002d900000b64000005100028d1000015840000561000002d90000561000002d900000b6400000510000561000002d900000b64000005100000b64000005100000144000000903d50c9001c94f40074bb90003ae840077c490003cffc001146f00007adc007ede600040a1000127a1000083640014f13000094ec000253b0000108c008adcc800489000012240000093c000140388000a92c0002a4b000012cc0016dc40000c1a4000306900001584000306900001584000056100000264008797680040a100012240000093c00012240000093c00002a4b000012cc00140388000a2cc0003069000015840003069000015840000561000002640016f590000c1a40003069000019a10003069000019a10000668400002d90003069000019a10000668400002d90000668400002d900000b64000005100843d08003cffc00104d0000083640012240000093c00002a4b000012cc0012240000093c00002a4b000012cc00030690000158400005610000026400143940000a92c0002a4b000015840003069000019a10000668400002d90003069000019a10000668400002d90000668400002d900000b640000051001393e000094ec0002a4b000015840002a4b000015840000668400002d90002a4b000015840000668400002d90000668400002d900000b64000005100028d1000015840000561000002d90000561000002d900000b6400000510000561000002d900000b64000005100000b640000051000001440000009007fed38003ae84000f3ff00007adc001028400008364000253b0000108c0012240000093c00002a4b000012cc0003069000015840000561000002640011ab4000093c000024f0000012cc00028b3000015840000561000002640003069000019a10000668400002d90000668400002d900000b64000005100113ef8000836400024f0000012cc00024f0000012cc0000561000002640002a4b000015840000668400002d90000668400002d900000b64000005100028d1000015840000561000002d90000561000002d900000b6400000510000561000002d900000b64000005100000b6400000510000014400000090010adf00007adc00020d90000108c00024f0000012cc00005610000026400024f0000012cc0000561000002640000668400002d900000b64000005100023f4000012cc00004b3000002640000561000002d900000b6400000510000561000002d900000b64000005100000b64000005100000144000000900022ce0000108c00004b30000026400004b30000026400000b64000005100004b30000026400000b64000005100000b640000051000001440000009000048900000264000009900000051000009900000051000001440000009000009900000051000001440000009000001440000009000000240000001)
  | 9 => (32, 0xcc39d2c61549985d15f2f1ed027562d716752d290288f56d02d6edde0048b16316f89bd90297f1f502ed7162004af1bd0347865c0053f3d60053f3d60008652f16f285cb02a7432502a74325004cb12902e58aab005691ea005691ea0008a831033d27c50060fa2c0060fa2c0009b29e0060fa2c0009b29e0009b29e0000f84316f285cb0271f39b02b66a2b004e642302b66a2b004e6423005883f60008d9ff02f6d7f5005593a70063e82c0009fd9e0063e82c0009fd9e0009fd9e0000ffc30334f4f1005fb1c1005fb1c1000b313c005fb1c1000b313c000b313c00011e86005fb1c1000b313c000b313c00011e86000b313c00011e8600011e8600001ca716f89bd90260bf8902872b6f004864e302c7456300504d23005aa866000910d702c7456300504d23005aa866000910d7006660fc000a3ce6000a3ce60001061702f6d7f50057c5490057c5490009e61f0062d351000b8efc000b8efc000127e60062d351000b8efc000b8efc000127e6000b8efc000127e6000127e600001d97033d27c50058420b0062d351000b27910062d351000b2791000d0bd800014dfc0062d351000b2791000d0bd800014dfc000d0bd800014dfc00014dfc00002166005fb1c1000b2791000b279100014dfc000b279100014dfc00014dfc00002166000b279100014dfc00014dfc0000216600014dfc00002166000021660000035716752d290252b97f0266a70b0044be4b02885c3100491e710051ccd200082e1502c7456300504d23005aa866000910d7006660fc000a3ce6000a3ce60001061702b66a2b00504d2300504d23000910d70057ad19000a3ce6000a3ce6000106170062d351000b8efc000b8efc000127e6000b8efc000127e6000127e600001d9702e58aab004f091a0057ad190009e61f0057ad190009e61f000b2aca00011de10062d351000b2791000d0bd800014dfc000d0bd800014dfc00014dfc00002166005fb1c1000b2791000b279100014dfc000b279100014dfc00014dfc00002166000b279100014dfc00014dfc0000216600014dfc0000216600002166000003570347865c0056dc54005c4324000a5294006660fc000b8efc000d0bd800014dfc006660fc000b8efc000d0bd800014dfc000f4240000186a0000186a0000027100063e82c000b8efc000b8efc00014dfc000d0bd8000186a0000186a000002710000d0bd8000186a0000186a000002710000186a00000271000002710000003e80060fa2c000a5294000b8efc00014dfc000b8efc00014dfc000186a000002710000b8efc00014dfc000186a000002710000186a00000271000002710000003e8000b313c00014dfc00014dfc0000271000014dfc0000271000002710000003e800014dfc0000271000002710000003e800002710000003e8000003e80000006415f2f1ed024aa9af0257636d004324650266a70b00456f2d004da9720007c42502872b6f00491e710052759200083ef5005c4324000939ea000939ea0000ec3102b66a2b00504d2300504d23000910d70057ad19000a3ce6000a3ce6000106170062d351000b8efc000b8efc000127e6000b8efc000127e6000127e600001d9702a74325004864e300504d23000910d700504d23000910d7000a3ce6000106170057c5490009e61f000b8efc000127e6000b8efc000127e6000127e600001d97005fb1c1000b2791000b279100014dfc000b279100014dfc00014dfc00002166000b279100014dfc00014dfc0000216600014dfc00002166000021660000035702ed7162004da97200527592000939ea005aa866000a3ce6000b8efc000127e6005aa866000a3ce6000b8efc000127e6000d0bd800014dfc00014dfc000021660063e82c000b8efc000b8efc00014dfc000d0bd8000186a0000186a000002710000d0bd8000186a0000186a000002710000186a00000271000002710000003e80060fa2c000a5294000b8efc00014dfc000b8efc00014dfc000186a000002710000b8efc00014dfc000186a000002710000186a00000271000002710000003e8000b313c00014dfc00014dfc0000271000014dfc0000271000002710000003e800014dfc0000271000002710000003e800002710000003e8000003e80000006402d6edde004b3912004da9720008afa20051ccd2000939ea000a529400010842005aa866000a3ce6000b8efc000127e6000d0bd800014dfc00014dfc00002166005883f6000a3ce6000a3ce6000127e6000b2aca00014dfc00014dfc00002166000d0bd8000186a0000186a000002710000186a00000271000002710000003e8005691ea000939ea000a3ce6000127e6000a3ce6000127e600014dfc00002166000b8efc00014dfc000186a000002710000186a00000271000002710000003e8000b313c00014dfc00014dfc0000271000014dfc0000271000002710000003e800014dfc0000271000002710000003e800002710000003e8000003e8000000640053f3d60008afa2000939ea00010842000a3ce6000127e600014dfc00002166000a3ce6000127e600014dfc00002166000186a00000271000002710000003e80009fd9e000127e6000127e60000216600014dfc0000271000002710000003e800014dfc0000271000002710000003e800002710000003e8000003e8000000640009b29e00010842000127e600002166000127e60000216600002710000003e8000127e60000216600002710000003e800002710000003e8000003e80000006400011e860000216600002166000003e800002166000003e8000003e80000006400002166000003e8000003e800000064000003e800000064000000640000000a1549985d0238fcad024aa9af0041be1b0252b97f00432465004b3912000785b50260bf890044be4b004da9720007c4250056dc540008afa20008afa20000de5d0271f39b004864e3004864e300082e15004f091a000939ea000939ea0000ec310058420b000a5294000a529400010842000a5294000108420001084200001a6d02a74325004864e300504d23000910d700504d23000910d7000a3ce6000106170057c5490009e61f000b8efc000127e6000b8efc000127e6000127e600001d97005fb1c1000b2791000b279100014dfc000b279100014dfc00014dfc00002166000b279100014dfc00014dfc0000216600014dfc0000216600002166000003570297f1f50044be4b00491e7100082e1500504d23000910d7000a3ce60001061700504d23000910d7000a3ce600010617000b8efc000127e6000127e600001d97005593a70009e61f0009e61f00011de1000b279100014dfc00014dfc00002166000b279100014dfc00014dfc0000216600014dfc0000216600002166000003570060fa2c000a5294000b8efc00014dfc000b8efc00014dfc000186a000002710000b8efc00014dfc000186a000002710000186a00000271000002710000003e8000b313c00014dfc00014dfc0000271000014dfc0000271000002710000003e800014dfc0000271000002710000003e800002710000003e8000003e8000000640288f56d0043246500456f2d0007c42500491e7100083ef5000939ea0000ec3100504d23000910d7000a3ce600010617000b8efc000127e6000127e600001d97004e6423000910d7000910d7000106170009e61f000127e6000127e600001d97000b279100014dfc00014dfc0000216600014dfc000021660000216600000357005691ea000939ea000a3ce6000127e6000a3ce6000127e600014dfc00002166000b8efc00014dfc000186a000002710000186a00000271000002710000003e8000b313c00014dfc00014dfc0000271000014dfc0000271000002710000003e800014dfc0000271000002710000003e800002710000003e8000003e8000000640053f3d60008afa2000939ea00010842000a3ce6000127e600014dfc00002166000a3ce6000127e600014dfc00002166000186a00000271000002710000003e80009fd9e000127e6000127e60000216600014dfc0000271000002710000003e800014dfc0000271000002710000003e800002710000003e8000003e8000000640009b29e00010842000127e600002166000127e60000216600002710000003e8000127e60000216600002710000003e800002710000003e8000003e80000006400011e860000216600002166000003e800002166000003e8000003e80000006400002166000003e8000003e800000064000003e800000064000000640000000a027562d70041be1b00432465000785b50044be4b0007c4250008afa20000de5d004864e300082e15000939ea0000ec31000a5294000108420001084200001a6d004e6423000910d7000910d7000106170009e61f000127e6000127e600001d97000b279100014dfc00014dfc0000216600014dfc000021660000216600000357004cb12900082e15000910d700010617000910d700010617000127e600001d970009e61f00011de100014dfc0000216600014dfc000021660000216600000357000b313c00014dfc00014dfc0000271000014dfc0000271000002710000003e800014dfc0000271000002710000003e800002710000003e8000003e800000064004af1bd0007c42500083ef50000ec31000910d700010617000127e600001d97000910d700010617000127e600001d9700014dfc0000216600002166000003570009fd9e000127e6000127e60000216600014dfc0000271000002710000003e800014dfc0000271000002710000003e800002710000003e8000003e8000000640009b29e00010842000127e600002166000127e60000216600002710000003e8000127e60000216600002710000003e800002710000003e8000003e80000006400011e860000216600002166000003e800002166000003e8000003e80000006400002166000003e8000003e800000064000003e800000064000000640000000a0048b163000785b50007c4250000de5d00082e150000ec310001084200001a6d000910d700010617000127e600001d9700014dfc0000216600002166000003570008d9ff000106170001061700001d9700011de100002166000021660000035700014dfc0000271000002710000003e800002710000003e8000003e8000000640008a8310000ec310001061700001d970001061700001d970000216600000357000127e60000216600002710000003e800002710000003e8000003e80000006400011e860000216600002166000003e800002166000003e8000003e80000006400002166000003e8000003e800000064000003e800000064000000640000000a0008652f0000de5d0000ec3100001a6d0001061700001d9700002166000003570001061700001d97000021660000035700002710000003e8000003e8000000640000ffc300001d9700001d970000035700002166000003e8000003e80000006400002166000003e8000003e800000064000003e800000064000000640000000a0000f84300001a6d00001d970000035700001d9700000357000003e80000006400001d9700000357000003e800000064000003e800000064000000640000000a00001ca70000035700000357000000640000035700000064000000640000000a0000035700000064000000640000000a000000640000000a0000000a00000001)
  | 10 => (34, 0x91f591380372a52df0e2fd217c05b778df0e7da784c05e177a701a1134640097a9eb0ecc3ca900601a48101ad01398009c007201db6c83000ace1a4002b38690000fb76c0ec99c9b8062279b501889e6d4009f5d4801a90f9c000b1dafa002c76be800102b2e01d65c22400c51a6b0031469ac0011eb210031469ac0011eb2100047ac840001a1030ec99c9b805b418830190b2ebc00a29fb10190b2ebc00a29fb1002d627b4001080e701b22ad8c00b00ef40032a58d400126abf0032a58d400126abf00049aafc0001ac9d01d234a8400c2d50d0030b5434001469370030b54340014693700051a4dc0001db050030b54340014693700051a4dc0001db0500051a4dc0001db05000076c1400002b2f0ecc3ca90058fe6790178463f8009775ab01999626000a63e45002e637d00010de5c01999626000a63e45002e637d00010de5c0033ca0200012d5180004b54600001b64801b22ad8c00b42861002d0a184001243dc0032297ac001505310005414c40001e9330032297ac001505310005414c40001e9330005414c40001e93300007a4cc00002c7901d65c22400b543070032297ac00145b090032297ac00145b090005dd464000221eb0032297ac00145b090005dd464000221eb0005dd464000221eb0000887ac000031a10030b543400145b09000516c24000221eb000516c24000221eb0000887ac000031a1000516c24000221eb0000887ac000031a10000887ac000031a100000c684000004830e7da784c05718cc70167126c8009083260178d4e200098d04c002a4ac84000f610301999626000a63e45002e637d00010de5c0033ca0200012d5180004b54600001b6480190b2ebc00a63e4500298f9140010de5c002cfff9c0012d5180004b54600001b6480032297ac001505310005414c40001e9330005414c40001e93300007a4cc00002c7901a90f9c000a3fa7e002cfff9c001243dc002cfff9c001243dc000517f0c0001da290032297ac00145b090005dd464000221eb0005dd464000221eb0000887ac000031a10030b543400145b09000516c24000221eb000516c24000221eb0000887ac000031a1000516c24000221eb0000887ac000031a10000887ac000031a100000c6840000048301db6c83000b29f21002f2b2f80012fd450033ca020001505310005dd464000221eb0033ca020001505310005dd464000221eb0006c20a40002751b00009d46c000039310032a58d4001505310005414c4000221eb0005dd4640002751b00009d46c000039310005dd4640002751b00009d46c0000393100009d46c0000393100000e4c4000005330031469ac0012fd450005414c4000221eb0005414c4000221eb00009d46c000039310005414c4000221eb00009d46c0000393100009d46c0000393100000e4c40000053300051a4dc000221eb0000887ac000039310000887ac0000393100000e4c4000005330000887ac0000393100000e4c40000053300000e4c4000005330000014cc000000790e2fd217c055e5181015ee6a14008d67060167126c80091cef4002858b88000eabe60178463f80098d04c002a9a8b0000f7e04002f2b2f8001126fa000449be800018f2e0190b2ebc00a63e4500298f9140010de5c002cfff9c0012d5180004b54600001b6480032297ac001505310005414c40001e9330005414c40001e93300007a4cc00002c7901889e6d4009775ab00298f9140010de5c00298f9140010de5c0004b54600001b648002d0a184001243dc0005414c40001e9330005414c40001e93300007a4cc00002c790030b543400145b09000516c24000221eb000516c24000221eb0000887ac000031a1000516c24000221eb0000887ac000031a10000887ac000031a100000c6840000048301ad0139800a162e2002a9a8b0001126fa002e637d00012d5180005414c40001e933002e637d00012d5180005414c40001e9330005dd464000221eb0000887ac000031a10032a58d4001505310005414c4000221eb0005dd4640002751b00009d46c000039310005dd4640002751b00009d46c0000393100009d46c0000393100000e4c4000005330031469ac0012fd450005414c4000221eb0005414c4000221eb00009d46c000039310005414c4000221eb00009d46c0000393100009d46c0000393100000e4c40000053300051a4dc000221eb0000887ac000039310000887ac0000393100000e4c4000005330000887ac0000393100000e4c40000053300000e4c4000005330000014cc0000007901a113464009cb789002858b8800103d03002a4ac84001126fa0004bf5140001b9ef002e637d00012d5180005414c40001e9330005dd464000221eb0000887ac000031a1002d627b40012d5180004b54600001e933000517f0c000221eb0000887ac000031a10005dd4640002751b00009d46c0000393100009d46c0000393100000e4c400000533002c76be8001126fa0004b54600001e9330004b54600001e9330000887ac000031a10005414c4000221eb00009d46c0000393100009d46c0000393100000e4c40000053300051a4dc000221eb0000887ac000039310000887ac0000393100000e4c4000005330000887ac0000393100000e4c40000053300000e4c4000005330000014cc00000079002b3869000103d03000449be80001b9ef0004b54600001e9330000887ac000031a10004b54600001e9330000887ac000031a100009d46c0000393100000e4c40000053300049aafc0001e93300007a4cc000031a10000887ac0000393100000e4c4000005330000887ac0000393100000e4c40000053300000e4c4000005330000014cc0000007900047ac840001b9ef00007a4cc000031a100007a4cc000031a100000e4c40000053300007a4cc000031a100000e4c40000053300000e4c4000005330000014cc00000079000076c14000031a100000c6840000053300000c684000005330000014cc0000007900000c684000005330000014cc000000790000014cc000000790000001e40000000b0dca94b7c05381aa3015794604008a7f68015c6331c008d670600272de24000e3f3b0163f99e400908326002858b88000eabe6002ca7c8400103d0300040f40c000179e9016d0620c009775ab0025dd6ac000f61030028fe9f8001126fa000449be800018f2e002d50c1c0012fd450004bf5140001b9ef0004bf5140001b9ef00006e7bc0000282d01889e6d4009775ab00298f9140010de5c00298f9140010de5c0004b54600001b648002d0a184001243dc0005414c40001e9330005414c40001e93300007a4cc00002c790030b543400145b09000516c24000221eb000516c24000221eb0000887ac000031a1000516c24000221eb0000887ac000031a10000887ac000031a100000c6840000048301806920400908326002634130000f610300298f9140010de5c0004b54600001b64800298f9140010de5c0004b54600001b6480005414c40001e93300007a4cc00002c79002c03bd0001243dc000490f700001da29000516c24000221eb0000887ac000031a1000516c24000221eb0000887ac000031a10000887ac000031a100000c684000004830031469ac0012fd450005414c4000221eb0005414c4000221eb00009d46c000039310005414c4000221eb00009d46c0000393100009d46c0000393100000e4c40000053300051a4dc000221eb0000887ac000039310000887ac0000393100000e4c4000005330000887ac0000393100000e4c40000053300000e4c4000005330000014cc0000007901785de9c008d6706002473bd0000eabe6002634130000f7e04000449be800018f2e00298f9140010de5c0004b54600001b6480005414c40001e93300007a4cc00002c790028a7ec40010de5c0004379700001b648000490f700001e93300007a4cc00002c79000516c24000221eb0000887ac000031a10000887ac000031a100000c68400000483002c76be8001126fa0004b54600001e9330004b54600001e9330000887ac000031a10005414c4000221eb00009d46c0000393100009d46c0000393100000e4c40000053300051a4dc000221eb0000887ac000039310000887ac0000393100000e4c4000005330000887ac0000393100000e4c40000053300000e4c4000005330000014cc00000079002b3869000103d03000449be80001b9ef0004b54600001e9330000887ac000031a10004b54600001e9330000887ac000031a100009d46c0000393100000e4c40000053300049aafc0001e93300007a4cc000031a10000887ac0000393100000e4c4000005330000887ac0000393100000e4c40000053300000e4c4000005330000014cc0000007900047ac840001b9ef00007a4cc000031a100007a4cc000031a100000e4c40000053300007a4cc000031a100000e4c40000053300000e4c4000005330000014cc00000079000076c14000031a100000c6840000053300000c684000005330000014cc0000007900000c684000005330000014cc000000790000014cc000000790000001e40000000b016dde37c008a7f68002359c18000e3f3b002420c98000eabe600040f40c000179e90025dd6ac000f6103000449be800018f2e0004bf5140001b9ef00006e7bc0000282d0028a7ec40010de5c0004379700001b648000490f700001e93300007a4cc00002c79000516c24000221eb0000887ac000031a10000887ac000031a100000c684000004830027d7520000f61030004379700001b6480004379700001b64800007a4cc00002c79000490f700001da290000887ac000031a10000887ac000031a100000c6840000048300051a4dc000221eb0000887ac000039310000887ac0000393100000e4c4000005330000887ac0000393100000e4c40000053300000e4c4000005330000014cc000000790027001c8000eabe60003df81000018f2e0004379700001b64800007a4cc00002c790004379700001b64800007a4cc00002c790000887ac000031a100000c6840000048300049aafc0001e93300007a4cc000031a10000887ac0000393100000e4c4000005330000887ac0000393100000e4c40000053300000e4c4000005330000014cc0000007900047ac840001b9ef00007a4cc000031a100007a4cc000031a100000e4c40000053300007a4cc000031a100000e4c40000053300000e4c4000005330000014cc00000079000076c14000031a100000c6840000053300000c684000005330000014cc0000007900000c684000005330000014cc000000790000014cc000000790000001e40000000b0025ea7ac000e3f3b0003aaf98000179e90003d840c00018f2e00006e7bc0000282d0004379700001b64800007a4cc00002c790000887ac000031a100000c6840000048300042039c0001b64800006d92000002c790000768a4000031a100000c684000004830000887ac0000393100000e4c40000053300000e4c4000005330000014cc0000007900040acb800018f2e00006d92000002c7900006d92000002c7900000c6840000048300007a4cc000031a100000e4c40000053300000e4c4000005330000014cc00000079000076c14000031a100000c6840000053300000c684000005330000014cc0000007900000c684000005330000014cc000000790000014cc000000790000001e40000000b0003eddb0000179e9000063cb80000282d00006d92000002c7900000c6840000048300006d92000002c7900000c6840000048300000e4c4000005330000014cc0000007900006b27400002c7900000b1e40000048300000c684000005330000014cc0000007900000c684000005330000014cc000000790000014cc000000790000001e40000000b00006840c0000282d00000b1e40000048300000b1e4000004830000014cc0000007900000b1e4000004830000014cc000000790000014cc000000790000001e40000000b00000acbc0000048300000120c0000007900000120c000000790000001e40000000b00000120c000000790000001e40000000b0000001e40000000b00000002c00000001)
  | 11 => (35, 0xbcf16eb4020a5aeb844307ec6d80c4533de1117663f603263377c06eafb040012729d6116da596e0336382040719fd720012eff9301f3362c0005333b2000a667640001bbbe6116ba53f003468ab54068d156a80135106101c2cc84a00556c0b000aad8160001c795901ee8cc20005dd3e0000bba7c00001f46a0002ee9f000007d1a80000fa350000029b38116ba53f003113046406ad164a0013aedaa01ab45928004ebb6a800ae1f440001d053601cbb84240054a6bdc00c07d400002014e000301f50000080538000100a7000002ac6801ea9a748005cdf15000b9be2a000233d60002e6f8a80008cf58000119eb000002efc8002e6f8a80008cf58000119eb000002efc8000467ac00000bbf20000177e4000003ea6116da596e02ff770b0064ebcb780127527101b3fe03800505811000b1aac40001d9c7601b3fe03800505811000b1aac40001d9c7600311e8c000082fc2000105f8400002ba9601cbb8424005674cb800ace9970001fd763002fb5ac800090d38000121a70000030468002fb5ac800090d38000121a700000304680004869c00000c11a00001823400000405e01ee8cc20005702df000bed6b2000232944002fb5ac80008ca510001403400000355e0002fb5ac80008ca510001403400000355e0000500d000000d57800001aaf0000004728002e6f8a80008ca510001194a20000355e00004652880000d57800001aaf00000047280004652880000d57800001aaf000000472800006abc0000011ca0000023940000005ee1117663f602f0426dc060b08748011ae6ed01942cfc8004a6d39800a35abc0001b39ca01b3fe03800505811000b1aac40001d9c7600311e8c000082fc2000105f8400002ba9601ab4592800505811000a0b0220001d9c76002b3254800082fc2000105f8400002ba96002fb5ac800090d38000121a700000304680004869c00000c11a00001823400000405e01c2cc84a004f6207000acc9520001fd763002b325480007f5d8c001197fc00002eeaa002fb5ac80008ca510001403400000355e0000500d000000d57800001aaf0000004728002e6f8a80008ca510001194a20000355e00004652880000d57800001aaf00000047280004652880000d57800001aaf000000472800006abc0000011ca0000023940000005ee01f3362c00055d6e8000b4804000021042000311e8c000090d380001403400000355e000311e8c000090d380001403400000355e00005b20000000f30000001e60000000510000301f50000090d38000121a700000355e0000500d000000f30000001e600000005100000500d000000f30000001e600000005100000079800000014400000028800000006c0002ee9f0000084108000121a700000355e00004869c00000d57800001e6000000051000004869c00000d57800001e600000005100000079800000014400000028800000006c0000467ac00000d57800001aaf000000510000006abc0000014400000028800000006c000006abc0000014400000028800000006c000000a200000001b000000036000000009010c1fb1b602e5f18f005ea8e11001153fde0182c21d200474c548009c774c0001a13e20193af2de004a6d39800a476540001b690e002d20100000785580000f0ab00000281c801ab4592800505811000a0b0220001d9c76002b3254800082fc2000105f8400002ba96002fb5ac800090d38000121a700000304680004869c00000c11a00001823400000405e01a3455aa0049d49c400a0b0220001d9c7600282c0880007671d800105f8400002ba96002b3a65c0007f5d8c00121a700000304680004869c00000c11a00001823400000405e002e6f8a80008ca510001194a20000355e00004652880000d57800001aaf00000047280004652880000d57800001aaf000000472800006abc0000011ca0000023940000005ee01c67f5c8004e3ba6000a476540001e1560002c6ab1000082fc2000121a70000030468002c6ab1000082fc2000121a70000030468000500d000000d57800001aaf000000472800301f50000090d38000121a700000355e0000500d000000f30000001e600000005100000500d000000f30000001e600000005100000079800000014400000028800000006c0002ee9f0000084108000121a700000355e00004869c00000d57800001e6000000051000004869c00000d57800001e600000005100000079800000014400000028800000006c0000467ac00000d57800001aaf000000510000006abc0000014400000028800000006c000006abc0000014400000028800000006c000000a200000001b000000036000000009001babec10004c22e20009c774c0001c9cf80028d6af00007855800010821000002c058002c6ab1000082fc2000121a70000030468000500d000000d57800001aaf0000004728002b87d1000082fc2000105f84000030468000465ff00000d57800001aaf0000004728000500d000000f30000001e600000005100000079800000014400000028800000006c0002ab605800078558000105f84000030468000417e100000c11a00001aaf00000047280004869c00000d57800001e600000005100000079800000014400000028800000006c0000467ac00000d57800001aaf000000510000006abc0000014400000028800000006c000006abc0000014400000028800000006c000000a200000001b0000000360000000090002999d900007273e0000f0ab000002c058000417e100000c11a00001aaf0000004728000417e100000c11a00001aaf0000004728000079800000014400000028800000006c00004029c00000c11a00001823400000472800006abc0000014400000028800000006c000006abc0000014400000028800000006c000000a200000001b00000003600000000900003e8d400000b0160000182340000047280000608d0000011ca0000028800000006c00000608d0000011ca0000028800000006c000000a200000001b000000036000000009000005df90000011ca0000023940000006c0000008e50000001b0000000360000000090000008e50000001b0000000360000000090000000d800000002400000004800000000c1052d75c202d2cb30805cbe31e0010fb5fc01782136e00454ff78009845c40001960f6017fbb8580046b9bb4009c774c0001a13e2002aeb7400007273e0000e4e7c00002626a0188982320049d49c40093a9388001b39ca0027b1038000785580000f0ab00000281c8002b816f80008410800010821000002c0580004208400000b01600001602c000003ab201a3455aa0049d49c400a0b0220001d9c7600282c0880007671d800105f8400002ba96002b3a65c0007f5d8c00121a700000304680004869c00000c11a00001823400000405e002e6f8a80008ca510001194a20000355e00004652880000d57800001aaf00000047280004652880000d57800001aaf000000472800006abc0000011ca0000023940000005ee019b1c1020046b9bb40094da730001b39ca00282c0880007671d800105f8400002ba9600282c0880007671d800105f8400002ba960004869c00000c11a00001823400000405e002a535ee0007f5d8c000febb180002eeaa0004652880000d57800001aaf00000047280004652880000d57800001aaf000000472800006abc0000011ca0000023940000005ee002ee9f0000084108000121a700000355e00004869c00000d57800001e6000000051000004869c00000d57800001e600000005100000079800000014400000028800000006c0000467ac00000d57800001aaf000000510000006abc0000014400000028800000006c000006abc0000014400000028800000006c000000a200000001b0000000360000000090019319bbe00454ff78008e98a90001a13e20025369cc0006da438000f0ab00000281c800282c0880007671d800105f8400002ba960004869c00000c11a00001823400000405e00275db540007671d8000ece3b00002ba960003faec60000c11a00001823400000405e0004652880000d57800001aaf000000472800006abc0000011ca0000023940000005ee002ab605800078558000105f84000030468000417e100000c11a00001aaf00000047280004869c00000d57800001e600000005100000079800000014400000028800000006c0000467ac00000d57800001aaf000000510000006abc0000014400000028800000006c000006abc0000014400000028800000006c000000a200000001b0000000360000000090002999d900007273e0000f0ab000002c058000417e100000c11a00001aaf0000004728000417e100000c11a00001aaf0000004728000079800000014400000028800000006c00004029c00000c11a00001823400000472800006abc0000014400000028800000006c000006abc0000014400000028800000006c000000a200000001b00000003600000000900003e8d400000b0160000182340000047280000608d0000011ca0000028800000006c00000608d0000011ca0000028800000006c000000a200000001b000000036000000009000005df90000011ca0000023940000006c0000008e50000001b0000000360000000090000008e50000001b0000000360000000090000000d800000002400000004800000000c0188a67bc0043ed7f0008a9fef0001960f600235cdda000684f88000e4e7c00002626a0024ea4e20006ce728000f0ab00000281c80004208400000b01600001602c000003ab200275db540007671d8000ece3b00002ba960003faec60000c11a00001823400000405e0004652880000d57800001aaf000000472800006abc0000011ca0000023940000005ee0026a20c20006ce728000ece3b00002ba960003b38ec0000aea580001823400000405e0003faec60000bbaa80001aaf000000472800006abc0000011ca0000023940000005ee000467ac00000d57800001aaf000000510000006abc0000014400000028800000006c000006abc0000014400000028800000006c000000a200000001b00000003600000000900025dff26000684f88000db4870000281c80003b38ec0000aea580001823400000405e0003b38ec0000aea580001823400000405e00006abc0000011ca0000023940000005ee0004029c00000c11a00001823400000472800006abc0000014400000028800000006c000006abc0000014400000028800000006c000000a200000001b00000003600000000900003e8d400000b0160000182340000047280000608d0000011ca0000028800000006c00000608d0000011ca0000028800000006c000000a200000001b000000036000000009000005df90000011ca0000023940000006c0000008e50000001b0000000360000000090000008e50000001b0000000360000000090000000d800000002400000004800000000c0024e53ac0006583d8000d09f100002626a0003673940000a07200001602c000003ab20003b38ec0000aea580001823400000405e00006abc0000011ca0000023940000005ee0003a0a6c0000aea5800015d4b00000405e00005dd54000011ca0000023940000005ee00006abc0000014400000028800000006c000000a200000001b000000036000000009000038f2b20000a072000015d4b00000405e00005752c000010178000023940000005ee0000608d0000011ca0000028800000006c000000a200000001b000000036000000009000005df90000011ca0000023940000006c0000008e50000001b0000000360000000090000008e50000001b0000000360000000090000000d800000002400000004800000000c0003777cc0000989a8000140e4000003ab200005752c000010178000023940000005ee00005752c000010178000023940000005ee00000a200000001b00000003600000000900000558d00000101780000202f0000005ee000008e50000001b0000000360000000090000008e50000001b0000000360000000090000000d800000002400000004800000000c00005367000000eac80000202f0000005ee0000080bc0000017b8000003600000000900000080bc0000017b800000360000000090000000d800000002400000004800000000c000007d4c0000017b8000002f7000000090000000bdc0000002400000004800000000c000000bdc0000002400000004800000000c00000012000000003000000006000000001)
  | _ => (1, 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def base_T : ∀ u : Fin 1024, G 0 u = tb (tabT 0) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_0 : ∀ u : Fin 1024, u.val / 8 = 0 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_1 : ∀ u : Fin 1024, u.val / 8 = 1 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_2 : ∀ u : Fin 1024, u.val / 8 = 2 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_3 : ∀ u : Fin 1024, u.val / 8 = 3 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_4 : ∀ u : Fin 1024, u.val / 8 = 4 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_5 : ∀ u : Fin 1024, u.val / 8 = 5 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_6 : ∀ u : Fin 1024, u.val / 8 = 6 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_7 : ∀ u : Fin 1024, u.val / 8 = 7 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_8 : ∀ u : Fin 1024, u.val / 8 = 8 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_9 : ∀ u : Fin 1024, u.val / 8 = 9 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_10 : ∀ u : Fin 1024, u.val / 8 = 10 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_11 : ∀ u : Fin 1024, u.val / 8 = 11 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_12 : ∀ u : Fin 1024, u.val / 8 = 12 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_13 : ∀ u : Fin 1024, u.val / 8 = 13 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_14 : ∀ u : Fin 1024, u.val / 8 = 14 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_15 : ∀ u : Fin 1024, u.val / 8 = 15 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_16 : ∀ u : Fin 1024, u.val / 8 = 16 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_17 : ∀ u : Fin 1024, u.val / 8 = 17 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_18 : ∀ u : Fin 1024, u.val / 8 = 18 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_19 : ∀ u : Fin 1024, u.val / 8 = 19 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_20 : ∀ u : Fin 1024, u.val / 8 = 20 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_21 : ∀ u : Fin 1024, u.val / 8 = 21 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_22 : ∀ u : Fin 1024, u.val / 8 = 22 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_23 : ∀ u : Fin 1024, u.val / 8 = 23 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_24 : ∀ u : Fin 1024, u.val / 8 = 24 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_25 : ∀ u : Fin 1024, u.val / 8 = 25 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_26 : ∀ u : Fin 1024, u.val / 8 = 26 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_27 : ∀ u : Fin 1024, u.val / 8 = 27 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_28 : ∀ u : Fin 1024, u.val / 8 = 28 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_29 : ∀ u : Fin 1024, u.val / 8 = 29 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_30 : ∀ u : Fin 1024, u.val / 8 = 30 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_31 : ∀ u : Fin 1024, u.val / 8 = 31 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_32 : ∀ u : Fin 1024, u.val / 8 = 32 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_33 : ∀ u : Fin 1024, u.val / 8 = 33 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_34 : ∀ u : Fin 1024, u.val / 8 = 34 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_35 : ∀ u : Fin 1024, u.val / 8 = 35 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_36 : ∀ u : Fin 1024, u.val / 8 = 36 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_37 : ∀ u : Fin 1024, u.val / 8 = 37 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_38 : ∀ u : Fin 1024, u.val / 8 = 38 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_39 : ∀ u : Fin 1024, u.val / 8 = 39 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_40 : ∀ u : Fin 1024, u.val / 8 = 40 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_41 : ∀ u : Fin 1024, u.val / 8 = 41 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_42 : ∀ u : Fin 1024, u.val / 8 = 42 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_43 : ∀ u : Fin 1024, u.val / 8 = 43 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_44 : ∀ u : Fin 1024, u.val / 8 = 44 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_45 : ∀ u : Fin 1024, u.val / 8 = 45 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_46 : ∀ u : Fin 1024, u.val / 8 = 46 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_47 : ∀ u : Fin 1024, u.val / 8 = 47 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_48 : ∀ u : Fin 1024, u.val / 8 = 48 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_49 : ∀ u : Fin 1024, u.val / 8 = 49 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_50 : ∀ u : Fin 1024, u.val / 8 = 50 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_51 : ∀ u : Fin 1024, u.val / 8 = 51 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_52 : ∀ u : Fin 1024, u.val / 8 = 52 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_53 : ∀ u : Fin 1024, u.val / 8 = 53 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_54 : ∀ u : Fin 1024, u.val / 8 = 54 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_55 : ∀ u : Fin 1024, u.val / 8 = 55 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_56 : ∀ u : Fin 1024, u.val / 8 = 56 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_57 : ∀ u : Fin 1024, u.val / 8 = 57 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_58 : ∀ u : Fin 1024, u.val / 8 = 58 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_59 : ∀ u : Fin 1024, u.val / 8 = 59 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_60 : ∀ u : Fin 1024, u.val / 8 = 60 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_61 : ∀ u : Fin 1024, u.val / 8 = 61 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_62 : ∀ u : Fin 1024, u.val / 8 = 62 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_63 : ∀ u : Fin 1024, u.val / 8 = 63 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_64 : ∀ u : Fin 1024, u.val / 8 = 64 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_65 : ∀ u : Fin 1024, u.val / 8 = 65 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_66 : ∀ u : Fin 1024, u.val / 8 = 66 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_67 : ∀ u : Fin 1024, u.val / 8 = 67 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_68 : ∀ u : Fin 1024, u.val / 8 = 68 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_69 : ∀ u : Fin 1024, u.val / 8 = 69 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_70 : ∀ u : Fin 1024, u.val / 8 = 70 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_71 : ∀ u : Fin 1024, u.val / 8 = 71 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_72 : ∀ u : Fin 1024, u.val / 8 = 72 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_73 : ∀ u : Fin 1024, u.val / 8 = 73 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_74 : ∀ u : Fin 1024, u.val / 8 = 74 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_75 : ∀ u : Fin 1024, u.val / 8 = 75 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_76 : ∀ u : Fin 1024, u.val / 8 = 76 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_77 : ∀ u : Fin 1024, u.val / 8 = 77 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_78 : ∀ u : Fin 1024, u.val / 8 = 78 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_79 : ∀ u : Fin 1024, u.val / 8 = 79 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_80 : ∀ u : Fin 1024, u.val / 8 = 80 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_81 : ∀ u : Fin 1024, u.val / 8 = 81 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_82 : ∀ u : Fin 1024, u.val / 8 = 82 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_83 : ∀ u : Fin 1024, u.val / 8 = 83 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_84 : ∀ u : Fin 1024, u.val / 8 = 84 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_85 : ∀ u : Fin 1024, u.val / 8 = 85 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_86 : ∀ u : Fin 1024, u.val / 8 = 86 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_87 : ∀ u : Fin 1024, u.val / 8 = 87 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_88 : ∀ u : Fin 1024, u.val / 8 = 88 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_89 : ∀ u : Fin 1024, u.val / 8 = 89 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_90 : ∀ u : Fin 1024, u.val / 8 = 90 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_91 : ∀ u : Fin 1024, u.val / 8 = 91 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_92 : ∀ u : Fin 1024, u.val / 8 = 92 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_93 : ∀ u : Fin 1024, u.val / 8 = 93 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_94 : ∀ u : Fin 1024, u.val / 8 = 94 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_95 : ∀ u : Fin 1024, u.val / 8 = 95 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_96 : ∀ u : Fin 1024, u.val / 8 = 96 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_97 : ∀ u : Fin 1024, u.val / 8 = 97 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_98 : ∀ u : Fin 1024, u.val / 8 = 98 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_99 : ∀ u : Fin 1024, u.val / 8 = 99 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_100 : ∀ u : Fin 1024, u.val / 8 = 100 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_101 : ∀ u : Fin 1024, u.val / 8 = 101 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_102 : ∀ u : Fin 1024, u.val / 8 = 102 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_103 : ∀ u : Fin 1024, u.val / 8 = 103 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_104 : ∀ u : Fin 1024, u.val / 8 = 104 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_105 : ∀ u : Fin 1024, u.val / 8 = 105 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_106 : ∀ u : Fin 1024, u.val / 8 = 106 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_107 : ∀ u : Fin 1024, u.val / 8 = 107 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_108 : ∀ u : Fin 1024, u.val / 8 = 108 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_109 : ∀ u : Fin 1024, u.val / 8 = 109 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_110 : ∀ u : Fin 1024, u.val / 8 = 110 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_111 : ∀ u : Fin 1024, u.val / 8 = 111 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_112 : ∀ u : Fin 1024, u.val / 8 = 112 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_113 : ∀ u : Fin 1024, u.val / 8 = 113 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_114 : ∀ u : Fin 1024, u.val / 8 = 114 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_115 : ∀ u : Fin 1024, u.val / 8 = 115 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_116 : ∀ u : Fin 1024, u.val / 8 = 116 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_117 : ∀ u : Fin 1024, u.val / 8 = 117 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_118 : ∀ u : Fin 1024, u.val / 8 = 118 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_119 : ∀ u : Fin 1024, u.val / 8 = 119 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_120 : ∀ u : Fin 1024, u.val / 8 = 120 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_121 : ∀ u : Fin 1024, u.val / 8 = 121 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_122 : ∀ u : Fin 1024, u.val / 8 = 122 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_123 : ∀ u : Fin 1024, u.val / 8 = 123 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_124 : ∀ u : Fin 1024, u.val / 8 = 124 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_125 : ∀ u : Fin 1024, u.val / 8 = 125 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_126 : ∀ u : Fin 1024, u.val / 8 = 126 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_127 : ∀ u : Fin 1024, u.val / 8 = 127 → ∀ n < (11 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

theorem step_all (n : ℕ) (hn : n < 11) (u : Fin 1024) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  have hu := u.isLt
  obtain ⟨c, hc⟩ : ∃ c, u.val / 8 = c := ⟨_, rfl⟩
  have hc2 : c < 128 := by omega
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
  · exact chunk_16 u hc n hn
  · exact chunk_17 u hc n hn
  · exact chunk_18 u hc n hn
  · exact chunk_19 u hc n hn
  · exact chunk_20 u hc n hn
  · exact chunk_21 u hc n hn
  · exact chunk_22 u hc n hn
  · exact chunk_23 u hc n hn
  · exact chunk_24 u hc n hn
  · exact chunk_25 u hc n hn
  · exact chunk_26 u hc n hn
  · exact chunk_27 u hc n hn
  · exact chunk_28 u hc n hn
  · exact chunk_29 u hc n hn
  · exact chunk_30 u hc n hn
  · exact chunk_31 u hc n hn
  · exact chunk_32 u hc n hn
  · exact chunk_33 u hc n hn
  · exact chunk_34 u hc n hn
  · exact chunk_35 u hc n hn
  · exact chunk_36 u hc n hn
  · exact chunk_37 u hc n hn
  · exact chunk_38 u hc n hn
  · exact chunk_39 u hc n hn
  · exact chunk_40 u hc n hn
  · exact chunk_41 u hc n hn
  · exact chunk_42 u hc n hn
  · exact chunk_43 u hc n hn
  · exact chunk_44 u hc n hn
  · exact chunk_45 u hc n hn
  · exact chunk_46 u hc n hn
  · exact chunk_47 u hc n hn
  · exact chunk_48 u hc n hn
  · exact chunk_49 u hc n hn
  · exact chunk_50 u hc n hn
  · exact chunk_51 u hc n hn
  · exact chunk_52 u hc n hn
  · exact chunk_53 u hc n hn
  · exact chunk_54 u hc n hn
  · exact chunk_55 u hc n hn
  · exact chunk_56 u hc n hn
  · exact chunk_57 u hc n hn
  · exact chunk_58 u hc n hn
  · exact chunk_59 u hc n hn
  · exact chunk_60 u hc n hn
  · exact chunk_61 u hc n hn
  · exact chunk_62 u hc n hn
  · exact chunk_63 u hc n hn
  · exact chunk_64 u hc n hn
  · exact chunk_65 u hc n hn
  · exact chunk_66 u hc n hn
  · exact chunk_67 u hc n hn
  · exact chunk_68 u hc n hn
  · exact chunk_69 u hc n hn
  · exact chunk_70 u hc n hn
  · exact chunk_71 u hc n hn
  · exact chunk_72 u hc n hn
  · exact chunk_73 u hc n hn
  · exact chunk_74 u hc n hn
  · exact chunk_75 u hc n hn
  · exact chunk_76 u hc n hn
  · exact chunk_77 u hc n hn
  · exact chunk_78 u hc n hn
  · exact chunk_79 u hc n hn
  · exact chunk_80 u hc n hn
  · exact chunk_81 u hc n hn
  · exact chunk_82 u hc n hn
  · exact chunk_83 u hc n hn
  · exact chunk_84 u hc n hn
  · exact chunk_85 u hc n hn
  · exact chunk_86 u hc n hn
  · exact chunk_87 u hc n hn
  · exact chunk_88 u hc n hn
  · exact chunk_89 u hc n hn
  · exact chunk_90 u hc n hn
  · exact chunk_91 u hc n hn
  · exact chunk_92 u hc n hn
  · exact chunk_93 u hc n hn
  · exact chunk_94 u hc n hn
  · exact chunk_95 u hc n hn
  · exact chunk_96 u hc n hn
  · exact chunk_97 u hc n hn
  · exact chunk_98 u hc n hn
  · exact chunk_99 u hc n hn
  · exact chunk_100 u hc n hn
  · exact chunk_101 u hc n hn
  · exact chunk_102 u hc n hn
  · exact chunk_103 u hc n hn
  · exact chunk_104 u hc n hn
  · exact chunk_105 u hc n hn
  · exact chunk_106 u hc n hn
  · exact chunk_107 u hc n hn
  · exact chunk_108 u hc n hn
  · exact chunk_109 u hc n hn
  · exact chunk_110 u hc n hn
  · exact chunk_111 u hc n hn
  · exact chunk_112 u hc n hn
  · exact chunk_113 u hc n hn
  · exact chunk_114 u hc n hn
  · exact chunk_115 u hc n hn
  · exact chunk_116 u hc n hn
  · exact chunk_117 u hc n hn
  · exact chunk_118 u hc n hn
  · exact chunk_119 u hc n hn
  · exact chunk_120 u hc n hn
  · exact chunk_121 u hc n hn
  · exact chunk_122 u hc n hn
  · exact chunk_123 u hc n hn
  · exact chunk_124 u hc n hn
  · exact chunk_125 u hc n hn
  · exact chunk_126 u hc n hn
  · exact chunk_127 u hc n hn

theorem G_eq_T (n : ℕ) (hn : n ≤ 11) : ∀ u : Fin 1024, G n u = tb (tabT n) u.val := by
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
def tab_base : ∀ u : Fin 1024,
    tb (tabT 11) u.val + 55 * tb (tabT 9) u.val + 330 * tb (tabT 7) u.val + 462 * tb (tabT 5) u.val + 165 * tb (tabT 3) u.val + 11 * tb (tabT 1) u.val =
      11 * tb (tabT 10) u.val + 165 * tb (tabT 8) u.val + 462 * tb (tabT 6) u.val + 330 * tb (tabT 4) u.val + 55 * tb (tabT 2) u.val + tb (tabT 0) u.val := by
  decide +kernel

theorem G_base : ∀ u : Fin 1024,
    G 11 u + 55 * G 9 u + 330 * G 7 u + 462 * G 5 u + 165 * G 3 u + 11 * G 1 u =
      11 * G 10 u + 165 * G 8 u + 462 * G 6 u + 330 * G 4 u + 55 * G 2 u + G 0 u := by
  intro u
  rw [G_eq_T 11 (by norm_num) u, G_eq_T 10 (by norm_num) u, G_eq_T 9 (by norm_num) u, G_eq_T 8 (by norm_num) u, G_eq_T 7 (by norm_num) u, G_eq_T 6 (by norm_num) u, G_eq_T 5 (by norm_num) u, G_eq_T 4 (by norm_num) u, G_eq_T 3 (by norm_num) u, G_eq_T 2 (by norm_num) u, G_eq_T 1 (by norm_num) u, G_eq_T 0 (by norm_num) u]
  exact tab_base u

theorem G_rec (m : ℕ) : ∀ u : Fin 1024,
    G (m + 11) u + 55 * G (m + 9) u + 330 * G (m + 7) u + 462 * G (m + 5) u + 165 * G (m + 3) u + 11 * G (m + 1) u =
      11 * G (m + 10) u + 165 * G (m + 8) u + 462 * G (m + 6) u + 330 * G (m + 4) u + 55 * G (m + 2) u + G m u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega, show m + 1 + 9 = (m + 9) + 1 by omega, show m + 1 + 10 = (m + 10) + 1 by omega, show m + 1 + 11 = (m + 11) + 1 by omega]
    rw [G_succ (m + 11), G_succ (m + 9), G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1), G_succ (m + 10), G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 11) + 55 * a (m + 9) + 330 * a (m + 7) + 462 * a (m + 5) + 165 * a (m + 3) + 11 * a (m + 1) =
      11 * a (m + 10) + 165 * a (m + 8) + 462 * a (m + 6) + 330 * a (m + 4) + 55 * a (m + 2) + a m := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 1023

theorem G_vals : G 1 1023 = 6 ∧ G 2 1023 = 1816 ∧ G 3 1023 = 74528 ∧ G 4 1023 = 1162292 ∧ G 5 1023 = 10203222 ∧ G 6 1023 = 61304844 ∧ G 7 1023 = 281731072 ∧ G 8 1023 = 1060924200 ∧ G 9 1023 = 3426341574 ∧ G 10 1023 = 9795159264 ∧ G 11 1023 = 25359512992 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num), G_eq_T 9 (by norm_num), G_eq_T 10 (by norm_num), G_eq_T 11 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 6 ∧ a 2 = 1816 ∧ a 3 = 74528 ∧ a 4 = 1162292 ∧ a 5 = 10203222 ∧ a 6 = 61304844 ∧ a 7 = 281731072 ∧ a 8 = 1060924200 ∧ a 9 = 3426341574 ∧ a 10 = 9795159264 ∧ a 11 = 25359512992 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  norm_num

theorem recurrence (n : ℕ) (hn : 12 ≤ n) :
    (a n : ℚ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 11) + 55 * a (m + 9) + 330 * a (m + 7) + 462 * a (m + 5) + 165 * a (m + 3) + 11 * a (m + 1) : ℤ) : ℚ) =
      ((11 * a (m + 10) + 165 * a (m + 8) + 462 * a (m + 6) + 330 * a (m + 4) + 55 * a (m + 2) + a m : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 11 - 1 = (m + 10) by omega, show m + 11 - 2 = (m + 9) by omega, show m + 11 - 3 = (m + 8) by omega, show m + 11 - 4 = (m + 7) by omega, show m + 11 - 5 = (m + 6) by omega, show m + 11 - 6 = (m + 5) by omega, show m + 11 - 7 = (m + 4) by omega, show m + 11 - 8 = (m + 3) by omega, show m + 11 - 9 = (m + 2) by omega, show m + 11 - 10 = (m + 1) by omega, show m + 11 - 11 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 11 : PowerSeries ℚ) =
      2 * X * (3 + 875 * X + 27441 * X ^ 2 + 220687 * X ^ 3 + 609695 * X ^ 4 + 647425 * X ^ 5 + 267419 * X ^ 6 + 39317 * X ^ 7 + 1538 * X ^ 8) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 11 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 11 * (PowerSeries.mk F * X ^ 1) + C 55 * (PowerSeries.mk F * X ^ 2) - C 165 * (PowerSeries.mk F * X ^ 3) + C 330 * (PowerSeries.mk F * X ^ 4) - C 462 * (PowerSeries.mk F * X ^ 5) + C 462 * (PowerSeries.mk F * X ^ 6) - C 330 * (PowerSeries.mk F * X ^ 7) + C 165 * (PowerSeries.mk F * X ^ 8) - C 55 * (PowerSeries.mk F * X ^ 9) + C 11 * (PowerSeries.mk F * X ^ 10) - C 1 * (PowerSeries.mk F * X ^ 11) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (3 + 875 * X + 27441 * X ^ 2 + 220687 * X ^ 3 + 609695 * X ^ 4 + 647425 * X ^ 5 + 267419 * X ^ 6 + 39317 * X ^ 7 + 1538 * X ^ 8) : ℚ⟦X⟧) =
      C 6 * X ^ 1 + C 1750 * X ^ 2 + C 54882 * X ^ 3 + C 441374 * X ^ 4 + C 1219390 * X ^ 5 + C 1294850 * X ^ 6 + C 534838 * X ^ 7 + C 78634 * X ^ 8 + C 3076 * X ^ 9 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 12
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 12 := ⟨k - 12, by omega⟩
    have hr := recurrence (j + 12) (by omega)
    simp only [show j + 12 - 1 = j + 11 by omega, show j + 12 - 2 = j + 10 by omega, show j + 12 - 3 = j + 9 by omega, show j + 12 - 4 = j + 8 by omega, show j + 12 - 5 = j + 7 by omega, show j + 12 - 6 = j + 6 by omega, show j + 12 - 7 = j + 5 by omega, show j + 12 - 8 = j + 4 by omega, show j + 12 - 9 = j + 3 by omega, show j + 12 - 10 = j + 2 by omega, show j + 12 - 11 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 12 by omega,
      show 1 ≤ j + 12 by omega,
      show 2 ≤ j + 12 by omega,
      show 3 ≤ j + 12 by omega,
      show 4 ≤ j + 12 by omega,
      show 5 ≤ j + 12 by omega,
      show 6 ≤ j + 12 by omega,
      show 7 ≤ j + 12 by omega,
      show 8 ≤ j + 12 by omega,
      show 9 ≤ j + 12 by omega,
      show 10 ≤ j + 12 by omega,
      show 11 ≤ j + 12 by omega,
      show j + 12 - 0 = j + 12 by omega,
      show j + 12 - 1 = j + 11 by omega,
      show j + 12 - 2 = j + 10 by omega,
      show j + 12 - 3 = j + 9 by omega,
      show j + 12 - 4 = j + 8 by omega,
      show j + 12 - 5 = j + 7 by omega,
      show j + 12 - 6 = j + 6 by omega,
      show j + 12 - 7 = j + 5 by omega,
      show j + 12 - 8 = j + 4 by omega,
      show j + 12 - 9 = j + 3 by omega,
      show j + 12 - 10 = j + 2 by omega,
      show j + 12 - 11 = j + 1 by omega,
      show ¬ (j + 12 = 1) by omega,
      show ¬ (j + 12 = 2) by omega,
      show ¬ (j + 12 = 3) by omega,
      show ¬ (j + 12 = 4) by omega,
      show ¬ (j + 12 = 5) by omega,
      show ¬ (j + 12 = 6) by omega,
      show ¬ (j + 12 = 7) by omega,
      show ¬ (j + 12 = 8) by omega,
      show ¬ (j + 12 = 9) by omega,
      show ¬ (j + 12 < 1) by omega,
      show ¬ (j + 11 < 1) by omega,
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

end OMA.A250393

theorem OMA.solution : type_of% @OMA.S_oeis_a250393.main :=
  ⟨OMA.A250393.gen_fun, OMA.A250393.recurrence⟩
