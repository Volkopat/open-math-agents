import OMAStatements.S_oeis_a249849

/-!
A249849: exact nine-position/five-window adaptation of the threshold-chain proof
by @Salofe for A250064, PR #23285, commit bd4969a8ddc52c3bd7f8d30008570b9868fd00b6.
This uses the same counting infrastructure as our A250390 proof, PR #26510.
Conjecture: Colin Barker (2017); registered statement: @clementtrecourt, PR #19348.
The finite tables certify a recurrence on every subset state; linearity then proves
it for all levels. All computations are kernel checked.
-/

namespace OMA.A249849

open OMA.S_oeis_a249849 Finset

/-! ### The window condition -/

/-- The condition of the statement on 5 values (without the bound on `v`). -/
def Cy (y : Fin 5 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 5)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 5 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
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

theorem cy_of (y : Fin 5 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 5)) y Finset.univ_nonempty
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

theorem window_iff (y : Fin 5 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 5 → ℕ) :
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
def fget (f : Fin 9 → Bool) (k : ℕ) : Bool := if h : k < 9 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 9 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 5 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 9 → Bool) : Prop := ∀ i < (5 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 9 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 9 → Fin (n + 1)) (v : ℕ) : Fin 9 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a249849.get x k ≤ n := by
  unfold OMA.S_oeis_a249849.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (5 : ℕ), cntW (fun _ => true) i = 5 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 9 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (5 : ℕ), ¬ Cy (fun t : Fin 5 => OMA.S_oeis_a249849.get x (i + t)) := by
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
  have step2 : ∀ i < (5 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 5 => OMA.S_oeis_a249849.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 9 := by have := t.isLt; omega
    unfold OMA.S_oeis_a249849.get fget Lt
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
noncomputable def M (n : ℕ) (T : Fin 9 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 9 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 9 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
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
def lower {n : ℕ} (x : Fin 9 → Fin (n + 2)) : Fin 9 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 9 → Bool) (x : Fin 9 → Fin (n + 1)) : Fin 9 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 9 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 9 → Bool) (x : Fin 9 → Fin (n + 1)) (p : Fin 9) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 9 → Bool) :
    M (n + 1) T = ∑ S : Fin 9 → Bool,
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
def row (u : Fin 512) : Fin 9 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 9 → Bool) : ℕ := ∑ p : Fin 9, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 512, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 9 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2 + m / 256 % 2

theorem cnt_row : ∀ u : Fin 512, cntW (row u) 0 = pcb (u.val &&& 31) ∧
    cntW (row u) 1 = pcb (u.val &&& 62) ∧
    cntW (row u) 2 = pcb (u.val &&& 124) ∧
    cntW (row u) 3 = pcb (u.val &&& 248) ∧
    cntW (row u) 4 = pcb (u.val &&& 496) := by
  decide +kernel

def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 31) ≤ 1 ∧ 3 ≤ pcb (t &&& 31)) ∧
    ¬ (pcb (s &&& 62) ≤ 1 ∧ 3 ≤ pcb (t &&& 62)) ∧
    ¬ (pcb (s &&& 124) ≤ 1 ∧ 3 ≤ pcb (t &&& 124)) ∧
    ¬ (pcb (s &&& 248) ≤ 1 ∧ 3 ≤ pcb (t &&& 248)) ∧
    ¬ (pcb (s &&& 496) ≤ 1 ∧ 3 ≤ pcb (t &&& 496)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (5 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 512) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3, b4⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4]

theorem sub_iff (w u : Fin 512) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 9
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (512 : ℕ) ≤ 2 ^ i := by
          calc (512 : ℕ) = 2 ^ 9 := by norm_num
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
def subs (u : Fin 512) : Finset (Fin 512) :=
  univ.filter (fun w : Fin 512 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 512 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 512, M n (row u) = G n u := by
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

theorem row_full : ∀ p, row 511 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 511 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 9 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 511 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 511)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 511 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 511 := by
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

theorem G_succ (n : ℕ) (u : Fin 512) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl

/-! Packed tables certify the recursion on every state. -/
-- Each table row stores its field width followed by its packed coefficients.
def tb (T : ℕ × ℕ) (w : ℕ) : ℕ := (T.2 >>> (T.1 * w)) % 2 ^ T.1

def tabT : ℕ → ℕ × ℕ
  | 0 => (1, 0x177f000000000000077f0000033f0117177f000000000000007f0000003f0017177f0000000f0007077f0003033f0117177f)
  | 1 => (5, 0x518c330c6330c6318cc330c6318cc318cc3618c33186318c6318c63298c318c63298c34b186618c330cc3184631846318cc31846318cc329586618c318c6318c63294a6298c36319064208642088210430c6130c631842118cc31842118cc318cc3618c318c2118c6318c63298c3318c664208642088210418461184631846318cc3308c631a0831a0882104318c6318c8318c832104318c832104321044108230c611842130c6318cc3184210844118cc3618c318c210842118c63298c318c63298c3642088210418461080211846318cc31846318cc331a088210418c6318c63318c832104318c832104321044108218420184211842118cc31842118cc318cc38210418c2118c6318c633210418c6332104321044108218461184631846318d041846318d0418d044108218c6318c6418c641908218c64190821908220841)
  | 2 => (11, 0x94a738f20a33f02bc5a05b4122d85f86118a1944c8334042d45e0601841904c83318e19c4f8351e61442881b4124485b8601761903203317e19c338351181442881b18e1b03603812c15c2b81d1c221c4382d10e0b41680f3f030c890601720fc32033176100338350ce0d42881b18410c360380d80e02b81d12c1344382d10e0b41680f18a19c338380ce0e01c01d1181342682d09a0b41680f1e621c4385110e1442881b10e1442881b0a206c0d8093c82cc6283f2241803203316e0e0210210ce0d42881b1780e8220220d80e02b81d0d80e02b81d10e0b41680f17e190210220ce0e01c01d0ce0e01c01d09a0b41680f13e15c2b82d10e1442881b10e1442881b0a206c0d809168108320220c80881c01d0c80881c01d0700741680f1320cc2b82d0ae0b42881b0ae0b42881b0a206c0d8091321442882d0a20b41681b0a20b41681b05a06c0d8090a20b41681b05a06c0d80905a06c0d8090360240480339c2a4598351860f821021224180320330ce0d42881b16a0dc1d01d086088198110d80e02b81d10e0b41680f16c1801c01d080088110110ce0e01c01d09a0b41680f0ce0e01c01d09a0b41680f10e1442881b0a206c0d80915e0f83001d07e050110110c80881c01d0700741680f0c80881c01d0700741680f0ae0b42881b0a206c0d8090ca0d41a81d06a0740e80f0a20b41681b05a06c0d8090a20b41681b05a06c0d80905a06c0d809036024048031460d41f8110c0074110110c0074110110700741680f0c0074110110700741680f0700741680f0a206c0d8090c20cc1081106a0740e80f06a0740e80f05a06c0d80906a0740e80f05a06c0d80905a06c0d809036024048030b6084198110660440e80f0660440e80f03a03c0d8090660440e80f03a03c0d80903a03c0d8090360240480306606c0d80f03603c0780903603c0780901e0240480303603c0780901e0240480301e0240480301200c01801)
  | 3 => (15, 0xeb0085e517f0900489e26584f703584adc27b8539838a15840ec027c013e4a10276852a8382156e0ebc2800140162c0f482a001500e4007200e400724adc34e05070382149a0ebc1d7814015340f481e90150098207200e40072162c100820101620a2a07a00f4007a0dc80a8015000a8054002a0054002a489e2a0c69c038214440afc1d78140149a0b341e9015007a405400e40072156e0bb82010162080405880f4007a0a2a06f815000a8054002a0054002a15840f481e9016207a405880b1007a098206f80df00a8037c02a0054002a0e400a80150010005400400080004005400400080004002000100020001045fc270854f02b11a700e081d78140141c0a0817100f807a405400e4007214aa0a5817d0100080405880f4007a080405880f4007a054002a0054002a14e60ebc171010007a405880b1007a07a405880b1007a037c02a0054002a0a8007a00f400a805400400080004005400400080004002000100020001013dc0b4c1d78100075e04000b1007a075e04000b1007a02c401e8054002a0a0005600f400a803d002a0080004003d002a0080004002000100020001009f007200e400a8039002a00540040039002a00540040015001000200010039002a0054004001500100020001001500100020001000800040008000442f225084e1025f15060ab016980f21a700e081d7814007a405400e4007213b409c814b00de05dc04000ac0056080405880f4007a054002a0054002a13dc0e0814100de059a0400080005607a405880b1007a037c02a0054002a07a405880b1007a037c02a0054002a054004000800040020001000200010132c0ab01c100de057e02e80800056075e04000b1007a02c401e8054002a075e04000b1007a02c401e8054002a03d002a00800040020001000200010076005400a8007a02a001e803d002a039002a00540040015001000200010039002a005400400150010002000100150010002000100080004000800041200097c15880a207040378080005607040378080005602c401e8054002a07040378080005602c401e8054002a02c401e8054002a0200010002000100714050007c005602a001e803d002a02a001e803d002a01500100020001002a001e803d002a01500100020001001500100020001000800040008000406b003c80a000560280015803d002a0280015803d002a00f400a802000100280015803d002a00f400a8020001000f400a80200010008000400080004027c01c8039002a00e400a8015001000e400a8015001000540040008000400e400a80150010005400400080004005400400080004002000100020001)
  | 4 => (19, 0xa4be849bdc994483f74278b010b9c22a1011782894e113ac2423012540946a04c280c03004ce283bc1119423d5812320947e04c540c1c004d80999604f100cb20051404074019c803390014a2894e156f822fb8123208f4404c54098a804d80937404f1009e20051402ed6019c803390014a09996052800a5000550031a601b58036b0015e03f48023280465001c2011940070800e10005a278b0120a82adf0123208ce003d8c098a804d808f4403ecc09e200514027880145003390014a0947e041500a50005500294001540036b0015e031a6019780465001c2011940070800e10005a0946a04f1009e200550027880154002a80015e02ed601978032f001c200cbc0070800e10005a040740232804650027101194009c401388007d01194009c401388007d004e2001f4003e800192651210f50246600f010ab7c048c8098a804d808bee03968080c00410027880145003390014a08f5603ae808480042e0294001540036b0015e0294001540036b0015e011940070800e10005a0908c04c54080c0042e027880154002a80015e027880154002a80015e00cbc0070800e10005a032c801b58036b001c201194009c401388007d01194009c401388007d004e2001f4003e8001908a8403ecc098a8042e0262a010b802a80015e0262a010b802a80015e00aa00057800e10005a0307001518036b001c200dac0070801388007d00dac0070801388007d004e2001f4003e800190300c019c80339001c200ce40070800e10007d00ce40070800e10007d00384001f4003e8001900ce40070800e10007d00384001f4003e8001900384001f4003e80019000fa00064000c8000524dee1037021ea00d9b0905403bc807d9803f20ab7c048c8098a804d8027880145003390014a088ca037e8075d003b6020a8010b802a30010e0294001540036b0015e011940070800e10005a089d6048c8072d003b601f66010b802170010e027880154002a80015e00cbc0070800e10005a027880154002a80015e00cbc0070800e10005a01194009c401388007d004e2001f4003e80019085ce03bc80919003b601ec600d4802170010e0262a010b802a80015e00aa00057800e10005a0262a010b802a80015e00aa00057800e10005a00dac0070801388007d004e2001f4003e800190261401450028a0015e00a280057800af0005a00ce40070800e10007d00384001f4003e8001900ce40070800e10007d00384001f4003e8001900384001f4003e80019000fa00064000c8000507ee80366c0780802f80246400ed802170010e0246400ed802170010e00aa00057800e10005a0246400ed802170010e00aa00057800e10005a00aa00057800e10005a004e2001f4003e80019024a80136002080010e00a280057800af0005a00a280057800af0005a00384001f4003e8001900a280057800af0005a00384001f4003e8001900384001f4003e80019000fa00064000c80005022f000fc8026c0010e009b00043800af0005a009b00043800af0005a002bc00168003e80019009b00043800af0005a002bc00168003e80019002bc00168003e80019000fa00064000c800050099c0052800a50005a0029400168002d000190029400168002d00019000b400064000c800050029400168002d00019000b400064000c80005000b400064000c800050003200014000280001)
  | 5 => (22, 0x8cd568679171ac4c0127d31b805c1356b04fe24040671c1e4813d53052d3804319054d0c0457301501800e011bea5813b23052468042b1055030045b00152e800e1f057b6c047f90161e800ebf01ae50011ee0047b8002fd1c1e4817a6205091c042b10525b0045b00116c000e1f054994047f9011fe400ebf014aa0011ee0047b8002fd057b6c04ab5012ad400f55015bd0012de004b780032501a96401734005cd0003de005cd0003de000f78000a51b805c149a605e988042b10510f403ace0116c000e1f0525b003bf0011fe400ebf011fe400ebf0047b8002fd05503003e03012ad400f55012ad400f55004b7800325015bd0011cb005cd0003de005cd0003de000f78000a5054d0c047f9011fe400f55011fe400f55003d5400325014aa0011cb00472c003de00472c003de000f78000a501ae5001734005cd000510005cd000510001440000d8005cd000510001440000d8001440000d8000360000241ac4c0138d90530a40395405e988042b10116c000e1f05091c0379f00f4ec00c5d011fe400ebf0047b8002fd052468038db00fb2c00cad012ad400f55004b7800325012ad400f55004b7800325005cd0003de000f78000a5052d38045b000f4ec00cad011fe400f55003d5400325011fe400f55003d540032500472c003de000f78000a50161e8012de004b78003de005cd000510001440000d8005cd000510001440000d8001440000d80003600002404fe2403bbe0116c000cad0116c000cad003d54003250116c000cad003d5400325003d5400325000f78000a50152e800f5a004b78003de004b78003de001440000d8004b78003de001440000d8001440000d800036000024015018011ee0047b8003de0047b8003de000f78000d80047b8003de000f78000d8000f78000d8000360000240047b8003de000f78000d8000f78000d800036000024000f78000d800036000024000360000240000900000619e45c12d1904e364034f60526980393100eef800c0305e988042b10116c000e1f011fe400ebf0047b8002fd04ec8c0363b00e36c00b7700f80c00cad003d680028f012ad400f55004b7800325005cd0003de000f78000a504f54c042b100de7c00b7700efc000cad0032b40028f011fe400f55003d540032500472c003de000f78000a5011fe400f55003d540032500472c003de000f78000a5005cd000510001440000d8001440000d80003600002404d5ac03931010ac400b7700eb3800a960032b40028f0116c000cad003d5400325003d5400325000f78000a50116c000cad003d5400325003d5400325000f78000a5004b78003de001440000d8001440000d8000360000240115cc00ebf003afc00325003afc00325000c94000a50047b8003de000f78000d8000f78000d8000360000240047b8003de000f78000d8000f78000d800036000024000f78000d8000360000240003600002400009000006049f4c034f600e550009a6010ac400b770032b40028f010ac400b770032b40028f003d5400325000f78000a5010ac400b770032b40028f003d5400325000f78000a5003d5400325000f78000a5001440000d800036000024010c6400e1f0031740028f003afc00325000c94000a5003afc00325000c94000a5000f78000d800036000024003afc00325000c94000a5000f78000d800036000024000f78000d800036000024000360000240000900000601019c00c0300387c0028f00387c0028f000c94000a500387c0028f000c94000a5000c94000a50003600002400387c0028f000c94000a5000c94000a500036000024000c94000a5000360000240003600002400009000006003804002fd000bf4000a5000bf4000a500029400024000bf4000a5000294000240002940002400009000006000bf4000a500029400024000294000240000900000600029400024000090000060000900000600001800001)
  | 6 => (24, 0xad11dd1af6c91bc2e3041ae71c6bd804447e04653200bccf1cf944045c950488ef00c3a504a20200c9d300ed270021e11ccae40455aa04828900c2a204a59700ca9700ef1100222704c81200d09b00f8a300238501256d0029eb0029eb0005fd1cf944050d78046d8200c2a204848f00ca9700ca9700222704a16100d09b00d09b00238500ea790029eb0029eb0005fd04c81200d79400d7940024c000f523002bd5002bd50006430123210034410034410007770034410007770007770001111c6bd8048147050d7800c2a20473c500b01800ca9700222704848f00b33d00d09b00238500d09b0023850029eb0005fd04a59700b8a700d7940024c000d7940024c0002bd500064300f5230029b300344100077700344100077700077700011104a20200d09b00d09b0024c000d09b0024c00024c000064300ea790029b30029b30007770029b300077700077700011101256d0034410034410009610034410009610009610001570034410009610009610001570009610001570001570000311bc2e3044e870488fd00abe2050d7800c2a200ca97002227046d8200a82a00b69a001eb500d09b0023850029eb0005fd04828900ab6400bab4001f6400d7940024c0002bd500064300d7940024c0002bd50006430034410007770007770001110488ef00ca9700b69a001f6400d09b0024c00024c000064300d09b0024c00024c00006430029b300077700077700011100f8a3002bd5002bd500077700344100096100096100015700344100096100096100015700096100015700015700003104653200b26b00ca97001f6400ca97001f640024c000064300ca97001f640024c00006430024c000064300077700011100ef110024f1002bd5000777002bd5000777000961000157002bd500077700096100015700096100015700015700003100ed270029eb0029eb0007770029eb0007770007770001570029eb0007770007770001570007770001570001570000310029eb0007770007770001570007770001570001570000310007770001570001570000310001570000310000310000071af6c9042a7d044e8700a0d604814700ab9c00b26b001de3050d7800c2a200ca9700222700d09b0023850029eb0005fd0455aa00a44100ab64001ccb00b8a7001f640024f100054700d7940024c0002bd5000643003441000777000777000111045c9500c2a200a82a001ccb00b33d001f64001f6400054700d09b0024c00024c00006430029b300077700077700011100d09b0024c00024c00006430029b300077700077700011100344100096100096100015700096100015700015700003104447e00ab9c00c2a2001ccb00b018001b12001f6400054700ca97001f640024c00006430024c000064300077700011100ca97001f640024c00006430024c0000643000777000111002bd500077700096100015700096100015700015700003100c9d30023850023850006430023850006430006430001110029eb0007770007770001570007770001570001570000310029eb000777000777000157000777000157000157000031000777000157000157000031000157000031000031000007041ae700a0d600abe200190500c2a2001ccb001f6400054700c2a2001ccb001f640005470024c000064300077700011100c2a2001ccb001f640005470024c00006430007770001110024c000064300077700011100096100015700015700003100c3a5002227001eb500054700238500064300064300011100238500064300064300011100077700015700015700003100238500064300064300011100077700015700015700003100077700015700015700003100015700003100003100000700bccf001de30022270005470022270005470006430001110022270005470006430001110006430001110001570000310022270005470006430001110006430001110001570000310006430001110001570000310001570000310000310000070021e10005fd0005fd0001110005fd0001110001110000310005fd0001110001110000310001110000310000310000070005fd000111000111000031000111000031000031000007000111000031000031000007000031000007000007000001)
  | 7 => (26, 0xa822bc05ad89e174e4500c0ad817cb3e80c75b403333f001d6f818335b00cb364034a10801e5f4035a83001f3d8008fb800047dc18111800ca13c034619801e3c4035d50801f5c20090d0000486803740d00203440096100004b0800ad4000056a00015a80000ad418335b00e689003388d001e3c40347e7801f5c2007d708004868035b0100203440080d10004b08008e8780056a00015a80000ad403740d00212940084a50004d540094458005a200016880000b4400ac440006900001a400000d20001a400000d2000034800001a417cb3e80d0fc2039a24001e3c4033cb5001bd52007d7080048680347e7801c4a60080d10004b080080d10004b080015a80000ad4035d50801d0bc0084a50004d540084a50004d540016880000b44009445800564c001a400000d20001a400000d2000034800001a4035a8300203440080d10004d540080d10004d540013550000b44008e87800564c0015930000d200015930000d2000034800001a400ad400006900001a400001000001a4000010000004000000200001a400001000000400000020000040000002000000800000040174e4500c8ea40348e7001b35e039a24001e3c4007d70800486803388d001ac3400730900042480080d10004b080015a80000ad4034619801b36c00755500043980084a50004d540016880000b440084a50004d540016880000b44001a400000d2000034800001a4034a10801f5c200730900043980080d10004d540013550000b440080d10004d540013550000b440015930000d2000034800001a40096100005a200016880000d20001a4000010000004000000200001a40000100000040000002000004000000200000080000004003333f001c25a007d708004398007d7080043980013550000b44007d7080043980013550000b440013550000b4400034800001a40090d00004de00016880000d200016880000d2000040000002000016880000d20000400000020000040000002000000800000040008fb800056a00015a80000d200015a80000d2000034800002000015a80000d200003480000200000348000020000008000000400015a80000d20000348000020000034800002000000800000040000348000020000008000000400000800000040000010000000816b62780c31e40323a90019b320343f0801b2e000709680040a4039a24001e3c4007d7080048680080d10004b080015a80000ad403284f001a304006cdb0003eac00742f000439800137800009bc0084a50004d540016880000b44001a400000d2000034800001a4032cd9001e3c4006b0d0003eac00712980043980010e600009bc0080d10004d540013550000b440015930000d2000034800001a40080d10004d540013550000b440015930000d2000034800001a4001a400001000000400000020000040000002000000800000040031d6d001b2e00078f10003eac006f548003b9c0010e600009bc007d7080043980013550000b440013550000b4400034800001a4007d7080043980013550000b440013550000b4400034800001a40016880000d20000400000020000040000002000000800000040007cf60004b080012c20000b440012c20000b440002d100001a40015a80000d200003480000200000348000020000008000000400015a80000d2000034800002000003480000200000080000004000034800002000000800000040000080000004000001000000080302b60019b32006cd780037ac0078f10003eac0010e600009bc0078f10003eac0010e600009bc0013550000b4400034800001a40078f10003eac0010e600009bc0013550000b4400034800001a40013550000b4400034800001a40004000000200000080000004000797d000486800109200009bc0012c20000b440002d100001a40012c20000b440002d100001a4000348000020000008000000400012c20000b440002d100001a40003480000200000080000004000034800002000000800000040000080000004000001000000080075be00040a400121a00009bc00121a00009bc0002d100001a400121a00009bc0002d100001a40002d100001a4000080000004000121a00009bc0002d100001a40002d100001a400008000000400002d100001a40000800000040000080000004000001000000080011f70000ad40002b500001a40002b500001a400006900000400002b500001a40000690000040000069000004000001000000080002b500001a40000690000040000069000004000001000000080000690000040000010000000800001000000080000020000001)
  | 8 => (28, 0x8910c901055a1210b792601ea830110790001f99da02064cc00412381149efa02024fa02132340042fc0021c94e0044ba4004dc1c0008a3c1133f6401ffb4e0210f420042b7c021e5da0044fbe004e4f80008b38022b7320046ad00050e500008fd0005bd64000a344000a34400012241149efa023e554020948a0042b7c021231c0044fbe0044fbe0008b38021d3a40046ad00046ad00008fd0004d442000a344000a3440001224022b7320048900004890000093c000500e2000a92c000a92c00012cc005b710000c1a4000c1a40001584000c1a40001584000158400002641107900020f28c023e5540042b7c020bb18003e2da0044fbe0008b38021231c003f1f20046ad00008fd00046ad00008fd0000a3440001224021e5da0040a10004890000093c0004890000093c0000a92c00012cc00500e2000a2cc000c1a40001584000c1a4000158400015840000264021c94e0046ad00046ad000093c00046ad000093c000093c000012cc004d442000a2cc000a2cc0001584000a2cc000158400015840000264005bd64000c1a4000c1a400019a1000c1a400019a100019a100002d9000c1a400019a100019a100002d900019a100002d900002d9000005110b792601fd0d00211f80003ce2e023e5540042b7c0044fbe0008b38020948a003c18c00400e000081180046ad00008fd0000a34400012240210f42003cffc00413400008364004890000093c0000a92c00012cc004890000093c0000a92c00012cc000c1a400015840001584000026402132340044fbe00400e000083640046ad000093c000093c000012cc0046ad000093c000093c000012cc000a2cc0001584000158400002640050e50000a92c000a92c0001584000c1a400019a100019a100002d9000c1a400019a100019a100002d900019a100002d900002d9000005102064cc003ecb20044fbe00083640044fbe000836400093c000012cc0044fbe000836400093c000012cc00093c000012cc00015840000264004e4f800094ec000a92c0001584000a92c000158400019a100002d9000a92c000158400019a100002d900019a100002d900002d90000051004dc1c000a344000a3440001584000a3440001584000158400002d9000a3440001584000158400002d9000158400002d900002d90000051000a3440001584000158400002d9000158400002d900002d90000051000158400002d900002d9000005100002d90000051000005100000091055a1201efed001fd0d00039e9a020f28c003cd5c003ecb20007e24023e5540042b7c0044fbe0008b380046ad00008fd0000a344000122401ffb4e003ae84003cffc0007adc0040a10000836400094ec000108c004890000093c0000a92c00012cc000c1a400015840001584000026402024fa0042b7c003c18c0007adc003f1f200083640008364000108c0046ad000093c000093c000012cc000a2cc0001584000158400002640046ad000093c000093c000012cc000a2cc000158400015840000264000c1a400019a100019a100002d900019a100002d900002d9000005101f99da003cd5c0042b7c0007adc003e2da00075cc0008364000108c0044fbe000836400093c000012cc00093c000012cc000158400002640044fbe000836400093c000012cc00093c000012cc00015840000264000a92c000158400019a100002d900019a100002d900002d900000510044ba40008fd00008fd000012cc0008fd000012cc00012cc0000264000a3440001584000158400002d9000158400002d900002d90000051000a3440001584000158400002d9000158400002d900002d90000051000158400002d900002d9000005100002d900000510000051000000901ea8300039e9a003ce2e0006ee80042b7c0007adc0008364000108c0042b7c0007adc0008364000108c00093c000012cc000158400002640042b7c0007adc0008364000108c00093c000012cc0001584000026400093c000012cc0001584000026400019a100002d900002d900000510042fc00008b380008118000108c0008fd000012cc00012cc00002640008fd000012cc00012cc0000264000158400002d900002d900000510008fd000012cc00012cc0000264000158400002d900002d90000051000158400002d900002d9000005100002d900000510000051000000900412380007e240008b38000108c0008b38000108c00012cc00002640008b38000108c00012cc000026400012cc000026400002d900000510008b38000108c00012cc000026400012cc000026400002d9000005100012cc000026400002d9000005100002d90000051000005100000090008a3c0001224000122400002640001224000026400002640000051000122400002640000264000005100002640000051000005100000090001224000026400002640000051000026400000510000051000000900002640000051000005100000090000051000000900000090000001)
  | 9 => (29, 0xc31e8fd0a661eb054f40a4045fb2b1598aba011fac0c093289e008373315e479b01241f4c096701a0086cdf02638e18022812c013446c000f69f15cb35b0122c58c095e37a008652f02658948022a0c4013653c000f8430273211802367fc013fb3c000ffc3005989e00047a180023d0c0001ca715e479b01423938093ebb6008652f02590188022a0c40115062000f843026480b802367fc011b3fe000ffc3004cafb80047a180023d0c0001ca702732118024435c01221ae0010617004f30f80049f980024fcc0001d9700593c8800537f00029bf80002166000a6fe0000859800042cc00003571598aba012aa0f40a11c9c008652f0252343801f95fc0115062000f84302590188020076c011b3fe000ffc30046cff8003ff0c0023d0c0001ca702658948020b85401221ae0010617004886b8004185c0024fcc0001d97004f30f800477840029bf80002166000a6fe0000859800042cc000035702638e1802367fc011b3fe00106170046cff8004185c0020c2e0001d97004cafb800477840023bc200021660008ef08000859800042cc0000357005989e000537f00029bf80002710000a6fe00009c400004e2000003e8000a6fe00009c400004e2000003e8000138800000fa000007d00000064153d029012165fc096091e007be730284727002194bc0115062000f843024faed801ea6740103a6a000e8710046cff8003ff0c0023d0c0001ca702578de801f10940107dea000ec31004886b8004185c0024fcc0001d97004886b8004185c0024fcc0001d97000a6fe0000859800042cc00003570259c068022a0c40103a6a000ec310046cff8004185c0020c2e0001d970046cff8004185c0020c2e0001d970008ef08000859800042cc0000357004fecf00049f980024fcc0002166000a6fe00009c400004e2000003e8000a6fe00009c400004e2000003e8000138800000fa000007d00000064024ca27801fdd3c0115062000ec3100454188003b0c40020c2e0001d9700454188003b0c40020c2e0001d97000830b8000765c00042cc0000357004d94f000421080024fcc000216600093f3000085980004e2000003e800093f3000085980004e2000003e8000138800000fa000007d00000064004d11b00047a180023d0c00021660008f430000859800042cc00003e80008f430000859800042cc00003e800010b300000fa000007d000000640008f430000859800042cc00003e800010b300000fa000007d0000006400010b300000fa000007d0000006400001f40000019000000c8000000a14cc3d6011aa8fc090b2fe007680f025541e801ef4a400fee9e000e3850284727002194bc0115062000f8430046cff8003ff0c0023d0c0001ca702458b1801e16d400f884a000de5d004170a8003b0c400210840001a6d004886b8004185c0024fcc0001d97000a6fe0000859800042cc000035702483e9802194bc00f533a000de5d00400ed8003b0c4001d8620001a6d0046cff8004185c0020c2e0001d970008ef08000859800042cc00003570046cff8004185c0020c2e0001d970008ef08000859800042cc0000357000a6fe00009c400004e2000003e8000138800000fa000007d00000064023f581801ef4a4010ca5e000de5d003f2bf800359d0001d8620001a6d00454188003b0c40020c2e0001d97000830b8000765c00042cc000035700454188003b0c40020c2e0001d97000830b8000765c00042cc000035700093f3000085980004e2000003e8000138800000fa000007d0000006400450258003ff0c001ff860001d970007fe18000765c0003b2e00003570008f430000859800042cc00003e800010b300000fa000007d000000640008f430000859800042cc00003e800010b300000fa000007d0000006400010b300000fa000007d0000006400001f40000019000000c8000000a022fd95801da03c00f7ce6000cb34004329780037974001d8620001a6d004329780037974001d8620001a6d000830b8000765c00042cc0000357004329780037974001d8620001a6d000830b8000765c00042cc0000357000830b8000765c00042cc0000357000138800000fa000007d00000064004366f8003e10c001d0e20001a6d0007fe18000765c0003b2e00003570007fe18000765c0003b2e000035700010b300000fa000007d000000640007fe18000765c0003b2e000035700010b300000fa000007d0000006400010b300000fa000007d0000006400001f40000019000000c8000000a0041b9980038e14001f0860001a6d0007c21800069b40003b2e00003570007c21800069b40003b2e00003570000ecb80000d5c00007d000000640007c21800069b40003b2e00003570000ecb80000d5c00007d000000640000ecb80000d5c00007d0000006400001f40000019000000c8000000a0007b4f8000729c000394e00003570000e5380000d5c00006ae00000640000e5380000d5c00006ae000006400001ab8000019000000c8000000a0000e5380000d5c00006ae000006400001ab8000019000000c8000000a00001ab8000019000000c8000000a00000320000002800000140000001)
  | 10 => (30, 0xf95475f46022c80187f8f18092850318dfcaa009633510265a46000f68eb192f27cc0984f900272103c00fc471027b772c0101d2100473b140019e6f191486b8097a9eb027001c800fb76c027d75200102b2e0047ac84001a103028a7ec401080e70049aafc001ac9d0051a4dc001db0500076c140002b2f192f27cc0a65b460268874400fb76c0271860c0102b2e0040acb8001a103027c93cc01080e70042039c001ac9d0046f208001db0500076c140002b2f028a7ec4010de5c00437970001b64800490f70001e9330007a4cc0002c7900516c2400221eb000887ac00031a1000887ac00031a10000c684000048318dfcaa009b5eab02996d1800fb76c026af62400ee3750040acb8001a1030271860c00f15160042039c001ac9d0042039c001ac9d00076c140002b2f027d752000f610300437970001b64800437970001b6480007a4cc0002c7900490f70001da29000887ac00031a1000887ac00031a10000c6840000483027b772c01080e70042039c001b6480042039c001b6480006d9200002c790046f208001da29000768a400031a1000768a400031a10000c68400004830051a4dc00221eb000887ac0003931000887ac00039310000e4c40000533000887ac00039310000e4c400005330000e4c40000533000014cc0000079187f8f1809701d3027038f400e9ee102996d1800fb76c0040acb8001a1030268874400e7e44003d100800189610042039c001ac9d00076c140002b2f027001c800eabe6003df8100018f2e00437970001b6480007a4cc0002c7900437970001b6480007a4cc0002c79000887ac00031a10000c68400004830272103c0102b2e003d10080018f2e0042039c001b6480006d9200002c790042039c001b6480006d9200002c79000768a400031a10000c68400004830049aafc001e9330007a4cc00031a1000887ac00039310000e4c40000533000887ac00039310000e4c400005330000e4c40000533000014cc00000790265a46000f01c00040acb80018f2e0040acb80018f2e0006d9200002c790040acb80018f2e0006d9200002c790006d9200002c790000c68400004830047ac84001b9ef0007a4cc00031a10007a4cc00031a10000e4c400005330007a4cc00031a10000e4c400005330000e4c40000533000014cc000007900473b14001db0500076c1400031a100076c1400031a10000c684000053300076c1400031a10000c68400005330000c6840000533000014cc000007900076c1400031a10000c68400005330000c6840000533000014cc00000790000c6840000533000014cc0000079000014cc0000079000001e4000000b1808b200093cdb9025c074c00e0bab026d7aac00e9cf2003c070000181a502996d1800fb76c0040acb8001a1030042039c001ac9d00076c140002b2f025ea7ac00e3f3b003aaf9800179e9003d840c0018f2e0006e7bc000282d00437970001b6480007a4cc0002c79000887ac00031a10000c684000048302613e4000fb76c0039f91000179e9003c54580018f2e00063cb8000282d0042039c001b6480006d9200002c79000768a400031a10000c68400004830042039c001b6480006d9200002c79000768a400031a10000c6840000483000887ac00039310000e4c400005330000e4c40000533000014cc00000790258cd4400e9cf2003eddb000179e9003b8dd40016e1800063cb8000282d0040acb80018f2e0006d9200002c790006d9200002c790000c68400004830040acb80018f2e0006d9200002c790006d9200002c790000c68400004830007a4cc00031a10000e4c400005330000e4c40000533000014cc000007900407484001ac9d0006b2740002c790006b2740002c790000b1e4000048300076c1400031a10000c68400005330000c6840000533000014cc000007900076c1400031a10000c68400005330000c6840000533000014cc00000790000c6840000533000014cc0000079000014cc0000079000001e4000000b024a140c00e0bab003a7b840015cb1003eddb000179e900063cb8000282d003eddb000179e900063cb8000282d0006d9200002c790000c6840000483003eddb000179e900063cb8000282d0006d9200002c790000c68400004830006d9200002c790000c68400004830000e4c40000533000014cc0000079003f11c4001a10300062584000282d0006b2740002c790000b1e400004830006b2740002c790000b1e400004830000c6840000533000014cc00000790006b2740002c790000b1e400004830000c6840000533000014cc00000790000c6840000533000014cc0000079000014cc0000079000001e4000000b003da3ac00181a50006840c000282d0006840c000282d0000b1e400004830006840c000282d0000b1e400004830000b1e40000483000014cc00000790006840c000282d0000b1e400004830000b1e40000483000014cc00000790000b1e40000483000014cc0000079000014cc0000079000001e4000000b000679bc0002b2f0000acbc00004830000acbc00004830000120c00000790000acbc00004830000120c00000790000120c0000079000001e4000000b0000acbc00004830000120c00000790000120c0000079000001e4000000b0000120c0000079000001e4000000b000001e4000000b0000002c0000001)
  | _ => (1, 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def base_T : ∀ u : Fin 512, G 0 u = tb (tabT 0) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_0 : ∀ u : Fin 512, u.val / 16 = 0 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_1 : ∀ u : Fin 512, u.val / 16 = 1 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_2 : ∀ u : Fin 512, u.val / 16 = 2 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_3 : ∀ u : Fin 512, u.val / 16 = 3 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_4 : ∀ u : Fin 512, u.val / 16 = 4 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_5 : ∀ u : Fin 512, u.val / 16 = 5 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_6 : ∀ u : Fin 512, u.val / 16 = 6 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_7 : ∀ u : Fin 512, u.val / 16 = 7 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_8 : ∀ u : Fin 512, u.val / 16 = 8 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_9 : ∀ u : Fin 512, u.val / 16 = 9 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_10 : ∀ u : Fin 512, u.val / 16 = 10 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_11 : ∀ u : Fin 512, u.val / 16 = 11 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_12 : ∀ u : Fin 512, u.val / 16 = 12 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_13 : ∀ u : Fin 512, u.val / 16 = 13 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_14 : ∀ u : Fin 512, u.val / 16 = 14 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_15 : ∀ u : Fin 512, u.val / 16 = 15 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_16 : ∀ u : Fin 512, u.val / 16 = 16 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_17 : ∀ u : Fin 512, u.val / 16 = 17 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_18 : ∀ u : Fin 512, u.val / 16 = 18 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_19 : ∀ u : Fin 512, u.val / 16 = 19 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_20 : ∀ u : Fin 512, u.val / 16 = 20 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_21 : ∀ u : Fin 512, u.val / 16 = 21 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_22 : ∀ u : Fin 512, u.val / 16 = 22 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_23 : ∀ u : Fin 512, u.val / 16 = 23 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_24 : ∀ u : Fin 512, u.val / 16 = 24 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_25 : ∀ u : Fin 512, u.val / 16 = 25 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_26 : ∀ u : Fin 512, u.val / 16 = 26 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_27 : ∀ u : Fin 512, u.val / 16 = 27 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_28 : ∀ u : Fin 512, u.val / 16 = 28 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_29 : ∀ u : Fin 512, u.val / 16 = 29 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_30 : ∀ u : Fin 512, u.val / 16 = 30 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_31 : ∀ u : Fin 512, u.val / 16 = 31 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

theorem step_all (n : ℕ) (hn : n < 10) (u : Fin 512) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  have hu := u.isLt
  obtain ⟨c, hc⟩ : ∃ c, u.val / 16 = c := ⟨_, rfl⟩
  have hc2 : c < 32 := by omega
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

theorem G_eq_T (n : ℕ) (hn : n ≤ 10) : ∀ u : Fin 512, G n u = tb (tabT n) u.val := by
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
def tab_base : ∀ u : Fin 512,
    tb (tabT 10) u.val + 45 * tb (tabT 8) u.val + 210 * tb (tabT 6) u.val + 210 * tb (tabT 4) u.val + 45 * tb (tabT 2) u.val + tb (tabT 0) u.val =
      10 * tb (tabT 9) u.val + 120 * tb (tabT 7) u.val + 252 * tb (tabT 5) u.val + 120 * tb (tabT 3) u.val + 10 * tb (tabT 1) u.val := by
  decide +kernel

theorem G_base : ∀ u : Fin 512,
    G 10 u + 45 * G 8 u + 210 * G 6 u + 210 * G 4 u + 45 * G 2 u + G 0 u =
      10 * G 9 u + 120 * G 7 u + 252 * G 5 u + 120 * G 3 u + 10 * G 1 u := by
  intro u
  rw [G_eq_T 10 (by norm_num) u, G_eq_T 9 (by norm_num) u, G_eq_T 8 (by norm_num) u, G_eq_T 7 (by norm_num) u, G_eq_T 6 (by norm_num) u, G_eq_T 5 (by norm_num) u, G_eq_T 4 (by norm_num) u, G_eq_T 3 (by norm_num) u, G_eq_T 2 (by norm_num) u, G_eq_T 1 (by norm_num) u, G_eq_T 0 (by norm_num) u]
  exact tab_base u

theorem G_rec (m : ℕ) : ∀ u : Fin 512,
    G (m + 10) u + 45 * G (m + 8) u + 210 * G (m + 6) u + 210 * G (m + 4) u + 45 * G (m + 2) u + G m u =
      10 * G (m + 9) u + 120 * G (m + 7) u + 252 * G (m + 5) u + 120 * G (m + 3) u + 10 * G (m + 1) u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega, show m + 1 + 9 = (m + 9) + 1 by omega, show m + 1 + 10 = (m + 10) + 1 by omega]
    rw [G_succ (m + 10), G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m, G_succ (m + 9), G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 10) + 45 * a (m + 8) + 210 * a (m + 6) + 210 * a (m + 4) + 45 * a (m + 2) + a m =
      10 * a (m + 9) + 120 * a (m + 7) + 252 * a (m + 5) + 120 * a (m + 3) + 10 * a (m + 1) := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 511

theorem G_vals : G 1 511 = 10 ∧ G 2 511 = 1189 ∧ G 3 511 = 30080 ∧ G 4 511 = 337396 ∧ G 5 511 = 2307418 ∧ G 6 511 = 11342301 ∧ G 7 511 = 44075760 ∧ G 8 511 = 143723664 ∧ G 9 511 = 409195002 ∧ G 10 511 = 1045765501 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num), G_eq_T 9 (by norm_num), G_eq_T 10 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 10 ∧ a 2 = 1189 ∧ a 3 = 30080 ∧ a 4 = 337396 ∧ a 5 = 2307418 ∧ a 6 = 11342301 ∧ a 7 = 44075760 ∧ a 8 = 143723664 ∧ a 9 = 409195002 ∧ a 10 = 1045765501 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  norm_num

theorem recurrence (n : ℕ) (hn : 11 ≤ n) :
    (a n : ℚ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 10) + 45 * a (m + 8) + 210 * a (m + 6) + 210 * a (m + 4) + 45 * a (m + 2) + a m : ℤ) : ℚ) =
      ((10 * a (m + 9) + 120 * a (m + 7) + 252 * a (m + 5) + 120 * a (m + 3) + 10 * a (m + 1) : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 10 - 1 = (m + 9) by omega, show m + 10 - 2 = (m + 8) by omega, show m + 10 - 3 = (m + 7) by omega, show m + 10 - 4 = (m + 6) by omega, show m + 10 - 5 = (m + 5) by omega, show m + 10 - 6 = (m + 4) by omega, show m + 10 - 7 = (m + 3) by omega, show m + 10 - 8 = (m + 2) by omega, show m + 10 - 9 = (m + 1) by omega, show m + 10 - 10 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 10 : PowerSeries ℚ) =
      X * (10 + 1089 * X + 18640 * X ^ 2 + 88901 * X ^ 3 + 146478 * X ^ 4 + 88511 * X ^ 5 + 18312 * X ^ 6 + 939 * X ^ 7) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 10 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 10 * (PowerSeries.mk F * X ^ 1) + C 45 * (PowerSeries.mk F * X ^ 2) - C 120 * (PowerSeries.mk F * X ^ 3) + C 210 * (PowerSeries.mk F * X ^ 4) - C 252 * (PowerSeries.mk F * X ^ 5) + C 210 * (PowerSeries.mk F * X ^ 6) - C 120 * (PowerSeries.mk F * X ^ 7) + C 45 * (PowerSeries.mk F * X ^ 8) - C 10 * (PowerSeries.mk F * X ^ 9) + C 1 * (PowerSeries.mk F * X ^ 10) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X * (10 + 1089 * X + 18640 * X ^ 2 + 88901 * X ^ 3 + 146478 * X ^ 4 + 88511 * X ^ 5 + 18312 * X ^ 6 + 939 * X ^ 7) : ℚ⟦X⟧) =
      C 10 * X ^ 1 + C 1089 * X ^ 2 + C 18640 * X ^ 3 + C 88901 * X ^ 4 + C 146478 * X ^ 5 + C 88511 * X ^ 6 + C 18312 * X ^ 7 + C 939 * X ^ 8 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 11
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 11 := ⟨k - 11, by omega⟩
    have hr := recurrence (j + 11) (by omega)
    simp only [show j + 11 - 1 = j + 10 by omega, show j + 11 - 2 = j + 9 by omega, show j + 11 - 3 = j + 8 by omega, show j + 11 - 4 = j + 7 by omega, show j + 11 - 5 = j + 6 by omega, show j + 11 - 6 = j + 5 by omega, show j + 11 - 7 = j + 4 by omega, show j + 11 - 8 = j + 3 by omega, show j + 11 - 9 = j + 2 by omega, show j + 11 - 10 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 11 by omega,
      show 1 ≤ j + 11 by omega,
      show 2 ≤ j + 11 by omega,
      show 3 ≤ j + 11 by omega,
      show 4 ≤ j + 11 by omega,
      show 5 ≤ j + 11 by omega,
      show 6 ≤ j + 11 by omega,
      show 7 ≤ j + 11 by omega,
      show 8 ≤ j + 11 by omega,
      show 9 ≤ j + 11 by omega,
      show 10 ≤ j + 11 by omega,
      show j + 11 - 0 = j + 11 by omega,
      show j + 11 - 1 = j + 10 by omega,
      show j + 11 - 2 = j + 9 by omega,
      show j + 11 - 3 = j + 8 by omega,
      show j + 11 - 4 = j + 7 by omega,
      show j + 11 - 5 = j + 6 by omega,
      show j + 11 - 6 = j + 5 by omega,
      show j + 11 - 7 = j + 4 by omega,
      show j + 11 - 8 = j + 3 by omega,
      show j + 11 - 9 = j + 2 by omega,
      show j + 11 - 10 = j + 1 by omega,
      show ¬ (j + 11 = 1) by omega,
      show ¬ (j + 11 = 2) by omega,
      show ¬ (j + 11 = 3) by omega,
      show ¬ (j + 11 = 4) by omega,
      show ¬ (j + 11 = 5) by omega,
      show ¬ (j + 11 = 6) by omega,
      show ¬ (j + 11 = 7) by omega,
      show ¬ (j + 11 = 8) by omega,
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

end OMA.A249849

theorem OMA.solution : type_of% @OMA.S_oeis_a249849.main :=
  ⟨OMA.A249849.gen_fun, OMA.A249849.recurrence⟩
