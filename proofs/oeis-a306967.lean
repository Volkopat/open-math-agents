import OMAStatements.S_oeis_a306967

-- Problem: A306967: a(n) is the first Zagreb index of the Fibonacci cube Gamma(n).
-- Upstream: formal-conjectures statements/oeis-a306967.lean:0 (declaration OMA.S_oeis_a306967.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: show hammingDist v u = 1 corresponds bijectively to single-bit flips, and for a
-- Fibonacci string v flipping bit i preserves IsFib iff both neighbours of i are false. Splitting
-- Fibonacci strings by their first bit gives coupled recurrences for the 0th, 1st and 2nd degree
-- moments T0, T1, T2: E(T0) = 0, E(T1) = 2*T0, E(T2) = 4*T1 + 2*shift(T0), where
-- E(s)(m) = s(m+2) - s(m+1) - s(m). Thus E(E(E(T2))) = 0, giving Barker's order-6 recurrence and
-- the generating function over Q by comparing coefficients.

open OMA.S_oeis_a306967

theorem bool_eq_not_of_ne67 : ∀ a b : Bool, a ≠ b → b = !a := by decide

theorem deg_eq_flip67 {n : ℕ} (v : Fin n → Bool) :
    deg v = (Finset.univ.filter (fun i : Fin n => IsFib (Function.update v i (!v i)))).card := by
  unfold deg
  symm
  refine Finset.card_bij (fun i _ => Function.update v i (!v i)) ?_ ?_ ?_
  · intro i hi
    have hfib : IsFib (Function.update v i (!v i)) := (Finset.mem_filter.1 hi).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hfib, ?_⟩
    unfold hammingDist
    have e : Finset.univ.filter (fun j : Fin n => v j ≠ Function.update v i (!v i) j) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        constructor
        · intro _; rfl
        · intro _
          cases v j <;> decide
      · rw [Function.update_of_ne hj]
        exact ⟨fun h => (h rfl).elim, fun h => (hj h).elim⟩
    rw [e, Finset.card_singleton]
  · intro i1 _ i2 _ heq
    by_contra hne
    have h := congrFun heq i1
    rw [Function.update_self, Function.update_of_ne hne] at h
    cases hv : v i1 <;> rw [hv] at h <;> exact absurd h (by decide)
  · intro u hu
    obtain ⟨hfib, hhd⟩ := (Finset.mem_filter.1 hu).2
    unfold hammingDist at hhd
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hhd
    have hu_eq : u = Function.update v i (!v i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        have hmem : j ∈ Finset.univ.filter (fun k : Fin n => v k ≠ u k) := by
          rw [hi]
          exact Finset.mem_singleton_self j
        exact bool_eq_not_of_ne67 (v j) (u j) (Finset.mem_filter.1 hmem).2
      · rw [Function.update_of_ne hj]
        have hnot : j ∉ Finset.univ.filter (fun k : Fin n => v k ≠ u k) := by
          rw [hi, Finset.mem_singleton]
          exact hj
        by_contra hne
        exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, Ne.symm hne⟩)
    rw [hu_eq] at hfib
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hfib⟩, hu_eq.symm⟩

/-- Both neighbours of position i in v are false. -/
def good67 {n : ℕ} (v : Fin n → Bool) (i : Fin n) : Prop :=
  (∀ j : Fin n, j.val + 1 = i.val → v j = false) ∧
  (∀ j : Fin n, j.val = i.val + 1 → v j = false)

instance {n : ℕ} (v : Fin n → Bool) (i : Fin n) : Decidable (good67 v i) := by
  unfold good67
  infer_instance

theorem flip_iff_good67 {n : ℕ} (v : Fin n → Bool) (hv : IsFib v) (i : Fin n) :
    IsFib (Function.update v i (!v i)) ↔ good67 v i := by
  cases hvi : v i with
  | true =>
    have hg : good67 v i := by
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · cases hvj : v j with
        | false => rfl
        | true => exact (hv j i hj.symm ⟨hvj, hvi⟩).elim
      · cases hvj : v j with
        | false => rfl
        | true => exact (hv i j hj ⟨hvi, hvj⟩).elim
    refine ⟨fun _ => hg, fun _ p q hpq ⟨hp, hq⟩ => ?_⟩
    by_cases hpi : p = i
    · subst hpi
      rw [Function.update_self] at hp
      exact absurd hp (by decide)
    · by_cases hqi : q = i
      · subst hqi
        rw [Function.update_self] at hq
        exact absurd hq (by decide)
      · rw [Function.update_of_ne hpi] at hp
        rw [Function.update_of_ne hqi] at hq
        exact hv p q hpq ⟨hp, hq⟩
  | false =>
    constructor
    · intro h
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · cases hvj : v j with
        | false => rfl
        | true =>
          have hji : j ≠ i := fun e => by subst e; omega
          have h1 : Function.update v i (!false) j = true := by rw [Function.update_of_ne hji, hvj]
          have h2 : Function.update v i (!false) i = true := by simp
          exact (h j i hj.symm ⟨h1, h2⟩).elim
      · cases hvj : v j with
        | false => rfl
        | true =>
          have hji : j ≠ i := fun e => by subst e; omega
          have h1 : Function.update v i (!false) i = true := by simp
          have h2 : Function.update v i (!false) j = true := by rw [Function.update_of_ne hji, hvj]
          exact (h i j hj ⟨h1, h2⟩).elim
    · rintro ⟨hL, hR⟩ p q hpq ⟨hp, hq⟩
      by_cases hpi : p = i
      · subst hpi
        have hqi : q ≠ p := fun e => by subst e; omega
        rw [Function.update_of_ne hqi] at hq
        have hf := hR q hpq
        rw [hf] at hq
        exact absurd hq (by decide)
      · by_cases hqi : q = i
        · subst hqi
          rw [Function.update_of_ne hpi] at hp
          have hf := hL p hpq.symm
          rw [hf] at hp
          exact absurd hp (by decide)
        · rw [Function.update_of_ne hpi] at hp
          rw [Function.update_of_ne hqi] at hq
          exact hv p q hpq ⟨hp, hq⟩

theorem deg_eq_good67 {n : ℕ} (v : Fin n → Bool) (hv : IsFib v) :
    deg v = (Finset.univ.filter (fun i : Fin n => good67 v i)).card := by
  rw [deg_eq_flip67]
  congr 1
  exact Finset.filter_congr (fun i _ => flip_iff_good67 v hv i)

/-- The first bit of v (if any) is false. -/
def first67 {n : ℕ} (v : Fin n → Bool) : Prop :=
  ∀ j : Fin n, j.val = 0 → v j = false

instance {n : ℕ} (v : Fin n → Bool) : Decidable (first67 v) := by
  unfold first67
  infer_instance

theorem first_cons67 {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    first67 (Fin.cons (α := fun _ => Bool) b w) ↔ b = false := by
  constructor
  · intro h
    have h0 := h 0 rfl
    rw [Fin.cons_zero] at h0
    exact h0
  · intro hb j hj
    have ej : j = 0 := Fin.ext hj
    rw [ej, Fin.cons_zero]
    exact hb

theorem isFib_cons67 {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    IsFib (Fin.cons (α := fun _ => Bool) b w) ↔ (b = true → first67 w) ∧ IsFib w := by
  constructor
  · intro h
    refine ⟨fun hb j hj => ?_, fun i j hij ⟨hi, hj⟩ => ?_⟩
    · cases hwj : w j with
      | false => rfl
      | true =>
        have hstep : j.succ.val = (0 : Fin (m + 1)).val + 1 := by simp [hj]
        have h0 : Fin.cons (α := fun _ => Bool) b w 0 = true := by rw [Fin.cons_zero]; exact hb
        have h1 : Fin.cons (α := fun _ => Bool) b w j.succ = true := by
          rw [Fin.cons_succ]; exact hwj
        exact (h 0 j.succ hstep ⟨h0, h1⟩).elim
    · have hstep : j.succ.val = i.succ.val + 1 := by simp [hij]
      have hi' : Fin.cons (α := fun _ => Bool) b w i.succ = true := by rw [Fin.cons_succ]; exact hi
      have hj' : Fin.cons (α := fun _ => Bool) b w j.succ = true := by rw [Fin.cons_succ]; exact hj
      exact h i.succ j.succ hstep ⟨hi', hj'⟩
  · rintro ⟨h1, h2⟩ p q hpq ⟨hp, hq⟩
    rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨p', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ q with rfl | ⟨q', rfl⟩
      · simp at hpq
      · rw [Fin.cons_zero] at hp
        rw [Fin.cons_succ] at hq
        have hq0 : q'.val = 0 := by simp at hpq; omega
        have hf := h1 hp q' hq0
        rw [hf] at hq
        exact absurd hq (by decide)
    · rcases Fin.eq_zero_or_eq_succ q with rfl | ⟨q', rfl⟩
      · simp at hpq
      · rw [Fin.cons_succ] at hp hq
        have hpq' : q'.val = p'.val + 1 := by simp at hpq; omega
        exact h2 p' q' hpq' ⟨hp, hq⟩

theorem good_cons_zero67 {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    good67 (Fin.cons (α := fun _ => Bool) b w) 0 ↔ first67 w := by
  constructor
  · intro ⟨_, hR⟩ j hj
    have hstep : j.succ.val = (0 : Fin (m + 1)).val + 1 := by simp [hj]
    have h := hR j.succ hstep
    rw [Fin.cons_succ] at h
    exact h
  · intro hw
    refine ⟨fun j hj => by simp at hj, fun j hj => ?_⟩
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · simp at hj
    · rw [Fin.cons_succ]
      exact hw j' (by simp at hj; omega)

theorem good_cons_succ67 {m : ℕ} (b : Bool) (w : Fin m → Bool) (i : Fin m) :
    good67 (Fin.cons (α := fun _ => Bool) b w) i.succ ↔ good67 w i ∧ (i.val = 0 → b = false) := by
  constructor
  · intro ⟨hL, hR⟩
    refine ⟨⟨fun j hj => ?_, fun j hj => ?_⟩, fun hi0 => ?_⟩
    · have h := hL j.succ (by simp [hj])
      rw [Fin.cons_succ] at h
      exact h
    · have h := hR j.succ (by simp [hj])
      rw [Fin.cons_succ] at h
      exact h
    · have h := hL 0 (by simp [hi0])
      rw [Fin.cons_zero] at h
      exact h
  · rintro ⟨⟨hL, hR⟩, hb⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rw [Fin.cons_zero]
        exact hb (by simp at hj; omega)
      · rw [Fin.cons_succ]
        exact hL j' (by simp at hj; omega)
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp at hj
      · rw [Fin.cons_succ]
        exact hR j' (by simp at hj; omega)

theorem deg_cons_false67 {m : ℕ} (w : Fin m → Bool) (hw : IsFib w) :
    deg (Fin.cons (α := fun _ => Bool) false w) = deg w + if first67 w then 1 else 0 := by
  have hc : IsFib (Fin.cons (α := fun _ => Bool) false w) :=
    (isFib_cons67 false w).2 ⟨fun h => absurd h (by decide), hw⟩
  rw [deg_eq_good67 _ hc, deg_eq_good67 _ hw, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_succ, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hiff : good67 (Fin.cons (α := fun _ => Bool) false w) i.succ ↔ good67 w i := by
      rw [good_cons_succ67]
      exact ⟨fun h => h.1, fun h => ⟨h, fun _ => rfl⟩⟩
    exact if_congr hiff rfl rfl
  · exact if_congr (good_cons_zero67 false w) rfl rfl

theorem deg_cons_true_false67 {m : ℕ} (u : Fin m → Bool) (hu : IsFib u) :
    deg (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false u)) =
      deg u + 1 := by
  have hfu : IsFib (Fin.cons (α := fun _ => Bool) false u) :=
    (isFib_cons67 false u).2 ⟨fun h => absurd h (by decide), hu⟩
  have htfu : IsFib (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false u)) :=
    (isFib_cons67 true _).2 ⟨fun _ => (first_cons67 false u).2 rfl, hfu⟩
  rw [deg_eq_good67 _ htfu, deg_eq_good67 _ hu, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h0 : good67 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false u)) 0 :=
    (good_cons_zero67 true _).2 ((first_cons67 false u).2 rfl)
  have h1 : ¬ good67 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false u))
      (0 : Fin (m + 1)).succ := by
    rw [good_cons_succ67]
    rintro ⟨-, hb⟩
    exact absurd (hb rfl) (by decide)
  rw [if_pos h0, if_neg h1, zero_add, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hiff : good67 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false u))
      i.succ.succ ↔ good67 u i := by
    rw [good_cons_succ67, good_cons_succ67]
    constructor
    · rintro ⟨⟨hg, -⟩, -⟩; exact hg
    · intro hg
      refine ⟨⟨hg, fun _ => rfl⟩, fun h => by simp at h⟩
  exact if_congr hiff rfl rfl

/-- Sum of f (deg v) over Fibonacci strings of length n with first bit false (or empty). -/
def SA67 (n : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool => IsFib v ∧ first67 v), f (deg v)

/-- Sum of f (deg v) over Fibonacci strings of length n with first bit true. -/
def SB67 (n : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool => IsFib v ∧ ¬ first67 v), f (deg v)

theorem SA67_zero (f : ℕ → ℤ) : SA67 0 f = f 0 := by
  unfold SA67
  have e : Finset.univ.filter (fun v : Fin 0 → Bool => IsFib v ∧ first67 v) = {Fin.elim0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; funext i; exact Fin.elim0 i
    · intro _; exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  rw [e, Finset.sum_singleton]
  have hd : deg (Fin.elim0 : Fin 0 → Bool) = 0 := by
    rw [deg_eq_flip67]
    simp
  rw [hd]

theorem SB67_zero (f : ℕ → ℤ) : SB67 0 f = 0 := by
  unfold SB67
  have e : Finset.univ.filter (fun v : Fin 0 → Bool => IsFib v ∧ ¬ first67 v) = ∅ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨-, hnf⟩
    exact hnf (fun i => Fin.elim0 i)
  rw [e, Finset.sum_empty]

theorem SB67_one (f : ℕ → ℤ) : SB67 1 f = f 1 := by
  unfold SB67
  have e : Finset.univ.filter (fun v : Fin 1 → Bool => IsFib v ∧ ¬ first67 v) =
      {fun _ => true} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hnf⟩
      funext i
      have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst hi
      cases hv : v 0 with
      | true => rfl
      | false =>
        exfalso
        apply hnf
        intro j hj
        have ej : j = 0 := Fin.ext hj
        rw [ej, hv]
    · rintro rfl
      refine ⟨fun i j hij => by have := i.isLt; have := j.isLt; omega, fun hf => ?_⟩
      exact absurd (hf 0 rfl) (by decide)
  rw [e, Finset.sum_singleton]
  have hd : deg (fun _ : Fin 1 => true) = 1 := by
    rw [deg_eq_flip67]
    have ef : Finset.univ.filter (fun i : Fin 1 => IsFib (Function.update (fun _ : Fin 1 => true) i
        (!(fun _ : Fin 1 => true) i))) = {0} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun _ => Fin.ext (by have := i.isLt; omega),
        fun _ p q hpq => by have := p.isLt; have := q.isLt; omega⟩
    rw [ef, Finset.card_singleton]
  rw [hd]

theorem SA67_succ (m : ℕ) (f : ℕ → ℤ) :
    SA67 (m + 1) f = SA67 m (fun d => f (d + 1)) + SB67 m f := by
  unfold SA67 SB67
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  have hcons := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Bool))
    (fun p : Bool × (Fin m → Bool) =>
      if IsFib (Fin.cons (α := fun _ => Bool) p.1 p.2) ∧
          first67 (Fin.cons (α := fun _ => Bool) p.1 p.2)
      then f (deg (Fin.cons (α := fun _ => Bool) p.1 p.2)) else 0)
    (fun v : Fin (m + 1) → Bool => if IsFib v ∧ first67 v then f (deg v) else 0)
    (fun _ => rfl)
  rw [← hcons, Fintype.sum_prod_type, Fintype.sum_bool]
  have ht : ∑ w : Fin m → Bool,
      (if IsFib (Fin.cons (α := fun _ => Bool) true w) ∧
          first67 (Fin.cons (α := fun _ => Bool) true w)
      then f (deg (Fin.cons (α := fun _ => Bool) true w)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    rintro ⟨-, hf⟩
    exact absurd ((first_cons67 true w).1 hf) (by decide)
  rw [ht, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : IsFib w
  · have hcf : IsFib (Fin.cons (α := fun _ => Bool) false w) :=
      (isFib_cons67 false w).2 ⟨fun h => absurd h (by decide), hw⟩
    have hff : first67 (Fin.cons (α := fun _ => Bool) false w) := (first_cons67 false w).2 rfl
    rw [if_pos ⟨hcf, hff⟩, deg_cons_false67 w hw]
    by_cases hfw : first67 w
    · rw [if_pos hfw, if_pos ⟨hw, hfw⟩, if_neg (fun h => h.2 hfw), add_zero]
    · rw [if_neg hfw, add_zero, if_neg (fun h => hfw h.2), if_pos ⟨hw, hfw⟩, zero_add]
  · rw [if_neg (fun h => hw ((isFib_cons67 false w).1 h.1).2),
      if_neg (fun h => hw h.1), if_neg (fun h => hw h.1), add_zero]

theorem SB67_succ_succ (m : ℕ) (f : ℕ → ℤ) :
    SB67 (m + 2) f = SA67 m (fun d => f (d + 1)) + SB67 m (fun d => f (d + 1)) := by
  unfold SA67 SB67
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  have hcons1 := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
    (fun p : Bool × (Fin (m + 1) → Bool) =>
      if IsFib (Fin.cons (α := fun _ => Bool) p.1 p.2) ∧
          ¬ first67 (Fin.cons (α := fun _ => Bool) p.1 p.2)
      then f (deg (Fin.cons (α := fun _ => Bool) p.1 p.2)) else 0)
    (fun v : Fin (m + 2) → Bool => if IsFib v ∧ ¬ first67 v then f (deg v) else 0)
    (fun _ => rfl)
  rw [← hcons1, Fintype.sum_prod_type, Fintype.sum_bool]
  have hf0 : ∑ w : Fin (m + 1) → Bool,
      (if IsFib (Fin.cons (α := fun _ => Bool) false w) ∧
          ¬ first67 (Fin.cons (α := fun _ => Bool) false w)
      then f (deg (Fin.cons (α := fun _ => Bool) false w)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    rintro ⟨-, hnf⟩
    exact hnf ((first_cons67 false w).2 rfl)
  rw [hf0, add_zero]
  have hcons2 := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Bool))
    (fun p : Bool × (Fin m → Bool) =>
      if IsFib (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) p.1 p.2)) ∧
          ¬ first67 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) p.1 p.2))
      then f (deg (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) p.1 p.2)))
      else 0)
    (fun w : Fin (m + 1) → Bool =>
      if IsFib (Fin.cons (α := fun _ => Bool) true w) ∧
          ¬ first67 (Fin.cons (α := fun _ => Bool) true w)
      then f (deg (Fin.cons (α := fun _ => Bool) true w)) else 0)
    (fun _ => rfl)
  rw [← hcons2, Fintype.sum_prod_type, Fintype.sum_bool]
  have htt : ∑ u : Fin m → Bool,
      (if IsFib (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) true u)) ∧
          ¬ first67 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) true u))
      then f (deg (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) true u)))
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg]
    rintro ⟨hfib, -⟩
    have hf1 := ((isFib_cons67 true _).1 hfib).1 rfl
    exact absurd ((first_cons67 true u).1 hf1) (by decide)
  rw [htt, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : IsFib u
  · have hfu : IsFib (Fin.cons (α := fun _ => Bool) false u) :=
      (isFib_cons67 false u).2 ⟨fun h => absurd h (by decide), hu⟩
    have htfu : IsFib (Fin.cons (α := fun _ => Bool) true
        (Fin.cons (α := fun _ => Bool) false u)) :=
      (isFib_cons67 true _).2 ⟨fun _ => (first_cons67 false u).2 rfl, hfu⟩
    have hnt : ¬ first67 (Fin.cons (α := fun _ => Bool) true
        (Fin.cons (α := fun _ => Bool) false u)) := by
      intro h
      exact absurd ((first_cons67 true _).1 h) (by decide)
    rw [if_pos ⟨htfu, hnt⟩, deg_cons_true_false67 u hu]
    by_cases hfirst : first67 u
    · rw [if_pos ⟨hu, hfirst⟩, if_neg (fun h => h.2 hfirst), add_zero]
    · rw [if_neg (fun h => hfirst h.2), if_pos ⟨hu, hfirst⟩, zero_add]
  · rw [if_neg (fun h => hu ((isFib_cons67 false u).1 ((isFib_cons67 true _).1 h.1).2).2),
      if_neg (fun h => hu h.1), if_neg (fun h => hu h.1), add_zero]

theorem a_eq_SA_add_SB67 (n : ℕ) :
    (a n : ℤ) = SA67 n (fun d => (d : ℤ) ^ 2) + SB67 n (fun d => (d : ℤ) ^ 2) := by
  unfold a SA67 SB67
  rw [Nat.cast_sum, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : IsFib v
  · by_cases hf : first67 v
    · rw [if_pos hv, if_pos ⟨hv, hf⟩, if_neg (fun h => h.2 hf), add_zero]
      push_cast
      rfl
    · rw [if_pos hv, if_neg (fun h => hf h.2), if_pos ⟨hv, hf⟩, zero_add]
      push_cast
      rfl
  · rw [if_neg hv, if_neg (fun h => hv h.1), if_neg (fun h => hv h.1), add_zero]

/-- Pure algebraic elimination for the Fibonacci degree moments. -/
theorem fib_moments_rec67 (A0 B0 A1 B1 A2 B2 : ℕ → ℤ)
    (h00 : A0 0 = 1) (hb01 : B0 1 = 1)
    (hA0 : ∀ m, A0 (m + 1) = A0 m + B0 m)
    (hB0 : ∀ m, B0 (m + 2) = A0 m + B0 m)
    (hA1 : ∀ m, A1 (m + 1) = A1 m + A0 m + B1 m)
    (hB1 : ∀ m, B1 (m + 2) = A1 m + A0 m + B1 m + B0 m)
    (hA2 : ∀ m, A2 (m + 1) = A2 m + 2 * A1 m + A0 m + B2 m)
    (hB2 : ∀ m, B2 (m + 2) = A2 m + 2 * A1 m + A0 m + B2 m + 2 * B1 m + B0 m) :
    ∀ m, (A2 (m + 6) + B2 (m + 6)) =
      3 * (A2 (m + 5) + B2 (m + 5)) - 5 * (A2 (m + 3) + B2 (m + 3)) +
        3 * (A2 (m + 1) + B2 (m + 1)) + (A2 m + B2 m) := by
  let T0 : ℕ → ℤ := fun m => A0 m + B0 m
  let T1 : ℕ → ℤ := fun m => A1 m + B1 m
  let T2 : ℕ → ℤ := fun m => A2 m + B2 m
  have hBA : ∀ m, B0 (m + 1) = A0 m := by
    intro m
    cases m with
    | zero => rw [hb01, h00]
    | succ k => rw [hB0 k, hA0 k]
  have eT0 : ∀ m, T0 (m + 2) - T0 (m + 1) - T0 m = 0 := by
    intro m
    change (A0 (m + 2) + B0 (m + 2)) - (A0 (m + 1) + B0 (m + 1)) - (A0 m + B0 m) = 0
    have h1 := hA0 (m + 1)
    have h2 := hB0 m
    linarith
  have eT1 : ∀ m, T1 (m + 2) - T1 (m + 1) - T1 m = 2 * T0 m := by
    intro m
    change (A1 (m + 2) + B1 (m + 2)) - (A1 (m + 1) + B1 (m + 1)) - (A1 m + B1 m) =
      2 * (A0 m + B0 m)
    have h1 := hA1 (m + 1)
    have h2 := hB1 m
    have h3 := hA0 m
    linarith
  have eT2 : ∀ m, T2 (m + 2) - T2 (m + 1) - T2 m = 4 * T1 m + 2 * T0 (m + 1) := by
    intro m
    change (A2 (m + 2) + B2 (m + 2)) - (A2 (m + 1) + B2 (m + 1)) - (A2 m + B2 m) =
      4 * (A1 m + B1 m) + 2 * (A0 (m + 1) + B0 (m + 1))
    have h1 := hA2 (m + 1)
    have h2 := hB2 m
    have h3 := hA1 m
    have h4 := hA0 m
    have h5 := hBA m
    linarith
  have eeT2 : ∀ m, T2 (m + 4) - 2 * T2 (m + 3) - T2 (m + 2) + 2 * T2 (m + 1) + T2 m =
      8 * T0 m := by
    intro m
    have q2 := eT2 (m + 2)
    have q1 := eT2 (m + 1)
    have q0 := eT2 m
    have r1 := eT1 m
    have r0 := eT0 (m + 1)
    linarith
  intro m
  have s2 := eeT2 (m + 2)
  have s1 := eeT2 (m + 1)
  have s0 := eeT2 m
  have t0 := eT0 m
  change T2 (m + 6) = 3 * T2 (m + 5) - 5 * T2 (m + 3) + 3 * T2 (m + 1) + T2 m
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a306967.main := by
  obtain ⟨A0, hA0def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SA67 n (fun _ => 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨B0, hB0def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SB67 n (fun _ => 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨A1, hA1def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SA67 n (fun d => (d : ℤ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨B1, hB1def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SB67 n (fun d => (d : ℤ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SA67 n (fun d => (d : ℤ) ^ 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨B2, hB2def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SB67 n (fun d => (d : ℤ) ^ 2) := ⟨_, fun _ => rfl⟩
  have hSA_add : ∀ n (f g : ℕ → ℤ), SA67 n (fun d => f d + g d) = SA67 n f + SA67 n g := by
    intro n f g
    unfold SA67
    exact Finset.sum_add_distrib
  have hSB_add : ∀ n (f g : ℕ → ℤ), SB67 n (fun d => f d + g d) = SB67 n f + SB67 n g := by
    intro n f g
    unfold SB67
    exact Finset.sum_add_distrib
  have hSA_mul : ∀ n (c : ℤ) (f : ℕ → ℤ), SA67 n (fun d => c * f d) = c * SA67 n f := by
    intro n c f
    unfold SA67
    exact (Finset.mul_sum _ _ _).symm
  have hSB_mul : ∀ n (c : ℤ) (f : ℕ → ℤ), SB67 n (fun d => c * f d) = c * SB67 n f := by
    intro n c f
    unfold SB67
    exact (Finset.mul_sum _ _ _).symm
  have hA0_0 : A0 0 = 1 := by rw [hA0def, SA67_zero]
  have hB0_0 : B0 0 = 0 := by rw [hB0def, SB67_zero]
  have hB0_1 : B0 1 = 1 := by rw [hB0def, SB67_one]
  have hA1_0 : A1 0 = 0 := by rw [hA1def, SA67_zero]; norm_num
  have hB1_0 : B1 0 = 0 := by rw [hB1def, SB67_zero]
  have hB1_1 : B1 1 = 1 := by rw [hB1def, SB67_one]; norm_num
  have hA2_0 : A2 0 = 0 := by rw [hA2def, SA67_zero]; norm_num
  have hB2_0 : B2 0 = 0 := by rw [hB2def, SB67_zero]
  have hB2_1 : B2 1 = 1 := by rw [hB2def, SB67_one]; norm_num
  have hA0 : ∀ m, A0 (m + 1) = A0 m + B0 m := by
    intro m; rw [hA0def, SA67_succ, ← hA0def, ← hB0def]
  have hB0 : ∀ m, B0 (m + 2) = A0 m + B0 m := by
    intro m; rw [hB0def, SB67_succ_succ, ← hA0def, ← hB0def]
  have hA1 : ∀ m, A1 (m + 1) = A1 m + A0 m + B1 m := by
    intro m
    rw [hA1def, SA67_succ]
    have e : (fun d : ℕ => ((d + 1 : ℕ) : ℤ)) = (fun d : ℕ => (d : ℤ) + 1) := by
      funext d; push_cast; rfl
    rw [e, hSA_add, ← hA1def, ← hA0def, ← hB1def]
  have hB1 : ∀ m, B1 (m + 2) = A1 m + A0 m + B1 m + B0 m := by
    intro m
    rw [hB1def, SB67_succ_succ]
    have e : (fun d : ℕ => ((d + 1 : ℕ) : ℤ)) = (fun d : ℕ => (d : ℤ) + 1) := by
      funext d; push_cast; rfl
    rw [e, hSA_add, hSB_add, ← hA1def, ← hA0def, ← hB1def, ← hB0def]
    ring
  have hA2 : ∀ m, A2 (m + 1) = A2 m + 2 * A1 m + A0 m + B2 m := by
    intro m
    rw [hA2def, SA67_succ]
    have e : (fun d : ℕ => ((d + 1 : ℕ) : ℤ) ^ 2) =
        (fun d : ℕ => ((d : ℤ) ^ 2 + 2 * (d : ℤ)) + 1) := by
      funext d; push_cast; ring
    rw [e, hSA_add, hSA_add, hSA_mul, ← hA2def, ← hA1def, ← hA0def, ← hB2def]
  have hB2 : ∀ m, B2 (m + 2) = A2 m + 2 * A1 m + A0 m + B2 m + 2 * B1 m + B0 m := by
    intro m
    rw [hB2def, SB67_succ_succ]
    have e : (fun d : ℕ => ((d + 1 : ℕ) : ℤ) ^ 2) =
        (fun d : ℕ => ((d : ℤ) ^ 2 + 2 * (d : ℤ)) + 1) := by
      funext d; push_cast; ring
    rw [e, hSA_add, hSA_add, hSA_mul, hSB_add, hSB_add, hSB_mul,
      ← hA2def, ← hA1def, ← hA0def, ← hB2def, ← hB1def, ← hB0def]
    ring
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℤ, ∀ n, (a n : ℤ) = b n := ⟨_, fun _ => rfl⟩
  have hb_eq : ∀ n, b n = A2 n + B2 n := by
    intro n
    rw [← hb, a_eq_SA_add_SB67, ← hA2def, ← hB2def]
  have hrec : ∀ m, b (m + 6) = 3 * b (m + 5) - 5 * b (m + 3) + 3 * b (m + 1) + b m := by
    intro m
    rw [hb_eq, hb_eq, hb_eq, hb_eq, hb_eq]
    exact fib_moments_rec67 A0 B0 A1 B1 A2 B2 hA0_0 hB0_1 hA0 hB0 hA1 hB1 hA2 hB2 m
  -- Compute initial values b 0 .. b 5 from the recurrences
  have hA0_1 : A0 1 = 1 := by have := hA0 0; linarith
  have hA0_2 : A0 2 = 2 := by have := hA0 1; linarith
  have hB0_2 : B0 2 = 1 := by have := hB0 0; linarith
  have hA0_3 : A0 3 = 3 := by have := hA0 2; linarith
  have hB0_3 : B0 3 = 2 := by have := hB0 1; linarith
  have hA0_4 : A0 4 = 5 := by have := hA0 3; linarith
  have hB0_4 : B0 4 = 3 := by have := hB0 2; linarith
  have hA1_1 : A1 1 = 1 := by have := hA1 0; linarith
  have hA1_2 : A1 2 = 3 := by have := hA1 1; linarith
  have hB1_2 : B1 2 = 1 := by have := hB1 0; linarith
  have hA1_3 : A1 3 = 6 := by have := hA1 2; linarith
  have hB1_3 : B1 3 = 4 := by have := hB1 1; linarith
  have hA1_4 : A1 4 = 13 := by have := hA1 3; linarith
  have hB1_4 : B1 4 = 7 := by have := hB1 2; linarith
  have hA2_1 : A2 1 = 1 := by have := hA2 0; linarith
  have hA2_2 : A2 2 = 5 := by have := hA2 1; linarith
  have hB2_2 : B2 2 = 1 := by have := hB2 0; linarith
  have hA2_3 : A2 3 = 14 := by have := hA2 2; linarith
  have hB2_3 : B2 3 = 8 := by have := hB2 1; linarith
  have hA2_4 : A2 4 = 37 := by have := hA2 3; linarith
  have hB2_4 : B2 4 = 17 := by have := hB2 2; linarith
  have hA2_5 : A2 5 = 85 := by have := hA2 4; linarith
  have hB2_5 : B2 5 = 47 := by have := hB2 3; linarith
  have vb0 : b 0 = 0 := by rw [hb_eq]; linarith
  have vb1 : b 1 = 2 := by rw [hb_eq]; linarith
  have vb2 : b 2 = 6 := by rw [hb_eq]; linarith
  have vb3 : b 3 = 22 := by rw [hb_eq]; linarith
  have vb4 : b 4 = 54 := by rw [hb_eq]; linarith
  have vb5 : b 5 = 132 := by rw [hb_eq]; linarith
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 3 = m + 4 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega]
    simp only [hb]
    have h := hrec (m + 1)
    rw [show m + 1 + 6 = m + 7 by omega, show m + 1 + 5 = m + 6 by omega,
      show m + 1 + 3 = m + 4 by omega, show m + 1 + 1 = m + 2 by omega] at h
    exact h
  · obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, ∀ n, f n = if n = 0 then (0 : ℚ) else (a n : ℚ) :=
      ⟨_, fun _ => rfl⟩
    have hfun : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = f :=
      funext fun n => (hf n).symm
    have f_eq_b : ∀ n, f n = (b n : ℚ) := by
      intro n
      cases n with
      | zero => rw [hf, if_pos rfl, vb0]; rfl
      | succ k =>
        rw [hf, if_neg (Nat.succ_ne_zero k)]
        have h := hb (k + 1)
        exact_mod_cast h
    have f0 : f 0 = 0 := by rw [f_eq_b, vb0]; norm_num
    have f1 : f 1 = 2 := by rw [f_eq_b, vb1]; norm_num
    have f2 : f 2 = 6 := by rw [f_eq_b, vb2]; norm_num
    have f3 : f 3 = 22 := by rw [f_eq_b, vb3]; norm_num
    have f4 : f 4 = 54 := by rw [f_eq_b, vb4]; norm_num
    have f5 : f 5 = 132 := by rw [f_eq_b, vb5]; norm_num
    have frec : ∀ m, f (m + 6) = 3 * f (m + 5) - 5 * f (m + 3) + 3 * f (m + 1) + f m := by
      intro m
      simp only [f_eq_b]
      exact_mod_cast hrec m
    rw [show PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = PowerSeries.mk f
      from congrArg PowerSeries.mk hfun]
    have e : PowerSeries.mk f * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 3 =
        PowerSeries.mk f
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * (PowerSeries.mk f * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk f * PowerSeries.X ^ 3)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * (PowerSeries.mk f * PowerSeries.X ^ 5)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1 * (PowerSeries.mk f * PowerSeries.X ^ 6) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
        map_one (PowerSeries.C : ℚ →+* PowerSeries ℚ)]
      ring
    have e2 : (2 * PowerSeries.X * (1 + 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3) :
        PowerSeries ℚ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
          + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
          - PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
      ring
    rw [e, e2]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n
      · norm_num [f0]
      · norm_num [f0, f1]
      · norm_num [f1, f2]
      · norm_num [f0, f2, f3]
      · norm_num [f1, f3, f4]
      · norm_num [f0, f2, f4, f5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [if_pos (by omega : 1 ≤ m + 6), if_pos (by omega : 3 ≤ m + 6),
        if_pos (by omega : 5 ≤ m + 6), if_pos (by omega : 6 ≤ m + 6),
        if_pos (by omega : 1 ≤ m + 6), if_pos (by omega : 3 ≤ m + 6),
        if_pos (by omega : 4 ≤ m + 6),
        if_neg (by omega : ¬ (m + 6 - 1 = 0)), if_neg (by omega : ¬ (m + 6 - 3 = 0)),
        if_neg (by omega : ¬ (m + 6 - 4 = 0)),
        show m + 6 - 1 = m + 5 by omega, show m + 6 - 3 = m + 3 by omega,
        show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega, frec m]
      ring
