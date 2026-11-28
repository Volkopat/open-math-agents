import OMAStatements.S_oeis_a307181

-- Problem: A307181: a(n) is the first Zagreb index of the Lucas cube Lambda(n).
-- Upstream: formal-conjectures statements/oeis-a307181.lean:0 (declaration OMA.S_oeis_a307181.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for n = m + 3, split Lucas vertices by their first bit into 0w (w a Fibonacci
-- string of length m+2, with deg_Luc(0w) = deg_Fib(w) + [first w and last w]) and 10u0 (u a
-- Fibonacci string of length m, with deg_Luc(10u0) = deg_Fib(u) + 1). Writing w with
-- first w and last w as 0u0 gives deg_Fib(0u0) = deg_Fib(u) + [first u] + [last u], and by
-- reversal symmetry on Fibonacci strings the sum of [last u] equals A0(m). This yields
-- a(m+3) = T2(m+2) + T2(m) + 4*T1(m) + 4*A0(m) + 2*T0(m) for all m >= 0, which is annihilated
-- by E^3 (where E(s)(m) = s(m+2) - s(m+1) - s(m)), proving Barker's recurrence for n > 8 and g.f.

open OMA.S_oeis_a307181

theorem bool_eq_not_of_ne81 : ∀ a b : Bool, a ≠ b → b = !a := by decide

/-- Fibonacci strings (no two consecutive true entries). -/
def IsFib81 {n : ℕ} (v : Fin n → Bool) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → ¬ (v i = true ∧ v j = true)

instance {n : ℕ} (v : Fin n → Bool) : Decidable (IsFib81 v) := by
  unfold IsFib81
  infer_instance

/-- Both linear neighbours of position i in v are false. -/
def goodF81 {n : ℕ} (v : Fin n → Bool) (i : Fin n) : Prop :=
  (∀ j : Fin n, j.val + 1 = i.val → v j = false) ∧
  (∀ j : Fin n, j.val = i.val + 1 → v j = false)

instance {n : ℕ} (v : Fin n → Bool) (i : Fin n) : Decidable (goodF81 v i) := by
  unfold goodF81
  infer_instance

/-- Degree of a Fibonacci string in the Fibonacci cube. -/
def degF81 {n : ℕ} (v : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => goodF81 v i)).card

/-- Cyclic neighbours of position i in v are false (valid for n >= 2). -/
def goodL81 {n : ℕ} (v : Fin n → Bool) (i : Fin n) : Prop :=
  goodF81 v i ∧
  (i.val = 0 → ∀ j : Fin n, j.val + 1 = n → v j = false) ∧
  (i.val + 1 = n → ∀ j : Fin n, j.val = 0 → v j = false)

instance {n : ℕ} (v : Fin n → Bool) (i : Fin n) : Decidable (goodL81 v i) := by
  unfold goodL81
  infer_instance

theorem deg_eq_flip81 {n : ℕ} (v : Fin n → Bool) :
    deg v = (Finset.univ.filter (fun i : Fin n => IsLuc (Function.update v i (!v i)))).card := by
  unfold deg
  symm
  refine Finset.card_bij (fun i _ => Function.update v i (!v i)) ?_ ?_ ?_
  · intro i hi
    have hluc : IsLuc (Function.update v i (!v i)) := (Finset.mem_filter.1 hi).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hluc, ?_⟩
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
    obtain ⟨hluc, hhd⟩ := (Finset.mem_filter.1 hu).2
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
        exact bool_eq_not_of_ne81 (v j) (u j) (Finset.mem_filter.1 hmem).2
      · rw [Function.update_of_ne hj]
        have hnot : j ∉ Finset.univ.filter (fun k : Fin n => v k ≠ u k) := by
          rw [hi, Finset.mem_singleton]
          exact hj
        by_contra hne
        exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, Ne.symm hne⟩)
    rw [hu_eq] at hluc
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hluc⟩, hu_eq.symm⟩

theorem flip_iff_goodL81 {n : ℕ} (hn : 2 ≤ n) (v : Fin n → Bool) (hv : IsLuc v) (i : Fin n) :
    IsLuc (Function.update v i (!v i)) ↔ goodL81 v i := by
  cases hvi : v i with
  | true =>
    have hg : goodL81 v i := by
      refine ⟨⟨fun j hj => ?_, fun j hj => ?_⟩, fun hi0 j hj => ?_, fun hin j hj => ?_⟩
      · cases hvj : v j with
        | false => rfl
        | true => exact (hv.1 j i hj.symm ⟨hvj, hvi⟩).elim
      · cases hvj : v j with
        | false => rfl
        | true => exact (hv.1 i j hj ⟨hvi, hvj⟩).elim
      · cases hvj : v j with
        | false => rfl
        | true => exact (hv.2 i j hi0 hj ⟨hvi, hvj⟩).elim
      · cases hvj : v j with
        | false => rfl
        | true => exact (hv.2 j i hj hin ⟨hvj, hvi⟩).elim
    refine ⟨fun _ => hg, fun _ => ⟨fun p q hpq ⟨hp, hq⟩ => ?_, fun p q hp0 hqn ⟨hp, hq⟩ => ?_⟩⟩
    · by_cases hpi : p = i
      · subst hpi; rw [Function.update_self] at hp; exact absurd hp (by decide)
      · by_cases hqi : q = i
        · subst hqi; rw [Function.update_self] at hq; exact absurd hq (by decide)
        · rw [Function.update_of_ne hpi] at hp; rw [Function.update_of_ne hqi] at hq
          exact hv.1 p q hpq ⟨hp, hq⟩
    · by_cases hpi : p = i
      · subst hpi; rw [Function.update_self] at hp; exact absurd hp (by decide)
      · by_cases hqi : q = i
        · subst hqi; rw [Function.update_self] at hq; exact absurd hq (by decide)
        · rw [Function.update_of_ne hpi] at hp; rw [Function.update_of_ne hqi] at hq
          exact hv.2 p q hp0 hqn ⟨hp, hq⟩
  | false =>
    constructor
    · intro h
      refine ⟨⟨fun j hj => ?_, fun j hj => ?_⟩, fun hi0 j hj => ?_, fun hin j hj => ?_⟩
      · cases hvj : v j with
        | false => rfl
        | true =>
          have hji : j ≠ i := fun e => by subst e; omega
          have h1 : Function.update v i (!false) j = true := by rw [Function.update_of_ne hji, hvj]
          have h2 : Function.update v i (!false) i = true := by rw [Function.update_self]; rfl
          exact (h.1 j i hj.symm ⟨h1, h2⟩).elim
      · cases hvj : v j with
        | false => rfl
        | true =>
          have hji : j ≠ i := fun e => by subst e; omega
          have h1 : Function.update v i (!false) i = true := by rw [Function.update_self]; rfl
          have h2 : Function.update v i (!false) j = true := by rw [Function.update_of_ne hji, hvj]
          exact (h.1 i j hj ⟨h1, h2⟩).elim
      · cases hvj : v j with
        | false => rfl
        | true =>
          have hji : j ≠ i := fun e => by subst e; omega
          have h1 : Function.update v i (!false) i = true := by rw [Function.update_self]; rfl
          have h2 : Function.update v i (!false) j = true := by rw [Function.update_of_ne hji, hvj]
          exact (h.2 i j hi0 hj ⟨h1, h2⟩).elim
      · cases hvj : v j with
        | false => rfl
        | true =>
          have hji : j ≠ i := fun e => by subst e; omega
          have h1 : Function.update v i (!false) j = true := by rw [Function.update_of_ne hji, hvj]
          have h2 : Function.update v i (!false) i = true := by rw [Function.update_self]; rfl
          exact (h.2 j i hj hin ⟨h1, h2⟩).elim
    · rintro ⟨⟨hL, hR⟩, h0n, hn0⟩
      refine ⟨fun p q hpq ⟨hp, hq⟩ => ?_, fun p q hp0 hqn ⟨hp, hq⟩ => ?_⟩
      · by_cases hpi : p = i
        · subst hpi
          have hqi : q ≠ p := fun e => by subst e; omega
          rw [Function.update_of_ne hqi] at hq
          rw [hR q hpq] at hq
          exact absurd hq (by decide)
        · by_cases hqi : q = i
          · subst hqi
            rw [Function.update_of_ne hpi] at hp
            rw [hL p hpq.symm] at hp
            exact absurd hp (by decide)
          · rw [Function.update_of_ne hpi] at hp; rw [Function.update_of_ne hqi] at hq
            exact hv.1 p q hpq ⟨hp, hq⟩
      · by_cases hpi : p = i
        · subst hpi
          have hqi : q ≠ p := fun e => by subst e; omega
          rw [Function.update_of_ne hqi] at hq
          rw [h0n hp0 q hqn] at hq
          exact absurd hq (by decide)
        · by_cases hqi : q = i
          · subst hqi
            rw [Function.update_of_ne hpi] at hp
            rw [hn0 hqn p hp0] at hp
            exact absurd hp (by decide)
          · rw [Function.update_of_ne hpi] at hp; rw [Function.update_of_ne hqi] at hq
            exact hv.2 p q hp0 hqn ⟨hp, hq⟩

theorem deg_eq_goodL81 {n : ℕ} (hn : 2 ≤ n) (v : Fin n → Bool) (hv : IsLuc v) :
    deg v = (Finset.univ.filter (fun i : Fin n => goodL81 v i)).card := by
  rw [deg_eq_flip81]
  congr 1
  exact Finset.filter_congr (fun i _ => flip_iff_goodL81 hn v hv i)

/-- The first bit of v (if any) is false. -/
def first81 {n : ℕ} (v : Fin n → Bool) : Prop :=
  ∀ j : Fin n, j.val = 0 → v j = false

instance {n : ℕ} (v : Fin n → Bool) : Decidable (first81 v) := by
  unfold first81
  infer_instance

/-- The last bit of v (if any) is false. -/
def last81 {n : ℕ} (v : Fin n → Bool) : Prop :=
  ∀ j : Fin n, j.val + 1 = n → v j = false

instance {n : ℕ} (v : Fin n → Bool) : Decidable (last81 v) := by
  unfold last81
  infer_instance

theorem first_cons81 {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    first81 (Fin.cons (α := fun _ => Bool) b w) ↔ b = false := by
  constructor
  · intro h; have h0 := h 0 rfl; rw [Fin.cons_zero] at h0; exact h0
  · intro hb j hj; have ej : j = 0 := Fin.ext hj; rw [ej, Fin.cons_zero]; exact hb

theorem last_snoc81 {m : ℕ} (u : Fin m → Bool) (b : Bool) :
    last81 (Fin.snoc (α := fun _ => Bool) u b) ↔ b = false := by
  constructor
  · intro h
    have h1 := h (Fin.last m) (by simp)
    rw [Fin.snoc_last] at h1
    exact h1
  · intro hb j hj
    have ej : j = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
    rw [ej, Fin.snoc_last]
    exact hb

theorem isFib_cons81 {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    IsFib81 (Fin.cons (α := fun _ => Bool) b w) ↔ (b = true → first81 w) ∧ IsFib81 w := by
  constructor
  · intro h
    refine ⟨fun hb j hj => ?_, fun i j hij ⟨hi, hj⟩ => ?_⟩
    · cases hwj : w j with
      | false => rfl
      | true =>
        have hstep : j.succ.val = (0 : Fin (m + 1)).val + 1 := by simp [hj]
        have h0 : Fin.cons (α := fun _ => Bool) b w 0 = true := by rw [Fin.cons_zero]; exact hb
        have h1 : Fin.cons (α := fun _ => Bool) b w j.succ = true := by rw [Fin.cons_succ]; exact hwj
        exact (h 0 j.succ hstep ⟨h0, h1⟩).elim
    · have hstep : j.succ.val = i.succ.val + 1 := by simp [hij]
      have hi' : Fin.cons (α := fun _ => Bool) b w i.succ = true := by rw [Fin.cons_succ]; exact hi
      have hj' : Fin.cons (α := fun _ => Bool) b w j.succ = true := by rw [Fin.cons_succ]; exact hj
      exact h i.succ j.succ hstep ⟨hi', hj'⟩
  · rintro ⟨h1, h2⟩ p q hpq ⟨hp, hq⟩
    rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨p', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ q with rfl | ⟨q', rfl⟩
      · simp at hpq
      · rw [Fin.cons_zero] at hp; rw [Fin.cons_succ] at hq
        have hf := h1 hp q' (by simp at hpq; omega)
        rw [hf] at hq; exact absurd hq (by decide)
    · rcases Fin.eq_zero_or_eq_succ q with rfl | ⟨q', rfl⟩
      · simp at hpq
      · rw [Fin.cons_succ] at hp hq
        exact h2 p' q' (by simp at hpq; omega) ⟨hp, hq⟩

theorem isFib_snoc_false81 {m : ℕ} (u : Fin m → Bool) :
    IsFib81 (Fin.snoc (α := fun _ => Bool) u false) ↔ IsFib81 u := by
  constructor
  · intro h i j hij ⟨hi, hj⟩
    have hstep : j.castSucc.val = i.castSucc.val + 1 := by simp [hij]
    have hi' : Fin.snoc (α := fun _ => Bool) u false i.castSucc = true := by
      rw [Fin.snoc_castSucc]; exact hi
    have hj' : Fin.snoc (α := fun _ => Bool) u false j.castSucc = true := by
      rw [Fin.snoc_castSucc]; exact hj
    exact h i.castSucc j.castSucc hstep ⟨hi', hj'⟩
  · intro h p q hpq ⟨hp, hq⟩
    rcases Fin.eq_castSucc_or_eq_last p with ⟨p', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last q with ⟨q', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc] at hp hq
        exact h p' q' (by simp at hpq; omega) ⟨hp, hq⟩
      · rw [Fin.snoc_last] at hq; exact absurd hq (by decide)
    · rw [Fin.snoc_last] at hp; exact absurd hp (by decide)

theorem goodF_cons_zero81 {m : ℕ} (b : Bool) (w : Fin m → Bool) :
    goodF81 (Fin.cons (α := fun _ => Bool) b w) 0 ↔ first81 w := by
  constructor
  · intro ⟨_, hR⟩ j hj
    have h := hR j.succ (by simp [hj])
    rw [Fin.cons_succ] at h
    exact h
  · intro hw
    refine ⟨fun j hj => by simp at hj, fun j hj => ?_⟩
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · simp at hj
    · rw [Fin.cons_succ]; exact hw j' (by simp at hj; omega)

theorem goodF_cons_succ81 {m : ℕ} (b : Bool) (w : Fin m → Bool) (i : Fin m) :
    goodF81 (Fin.cons (α := fun _ => Bool) b w) i.succ ↔ goodF81 w i ∧ (i.val = 0 → b = false) := by
  constructor
  · intro ⟨hL, hR⟩
    refine ⟨⟨fun j hj => ?_, fun j hj => ?_⟩, fun hi0 => ?_⟩
    · have h := hL j.succ (by simp [hj]); rw [Fin.cons_succ] at h; exact h
    · have h := hR j.succ (by simp [hj]); rw [Fin.cons_succ] at h; exact h
    · have h := hL 0 (by simp [hi0]); rw [Fin.cons_zero] at h; exact h
  · rintro ⟨⟨hL, hR⟩, hb⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rw [Fin.cons_zero]; exact hb (by simp at hj; omega)
      · rw [Fin.cons_succ]; exact hL j' (by simp at hj; omega)
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp at hj
      · rw [Fin.cons_succ]; exact hR j' (by simp at hj; omega)

theorem degF_cons_false81 {m : ℕ} (w : Fin m → Bool) :
    degF81 (Fin.cons (α := fun _ => Bool) false w) = degF81 w + if first81 w then 1 else 0 := by
  unfold degF81
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hiff : goodF81 (Fin.cons (α := fun _ => Bool) false w) i.succ ↔ goodF81 w i := by
      rw [goodF_cons_succ81]
      exact ⟨fun h => h.1, fun h => ⟨h, fun _ => rfl⟩⟩
    exact if_congr hiff rfl rfl
  · exact if_congr (goodF_cons_zero81 false w) rfl rfl

theorem degF_cons_true_false81 {m : ℕ} (u : Fin m → Bool) :
    degF81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false u)) =
      degF81 u + 1 := by
  unfold degF81
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h0 : goodF81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false u)) 0 :=
    (goodF_cons_zero81 true _).2 ((first_cons81 false u).2 rfl)
  have h1 : ¬ goodF81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false u))
      (0 : Fin (m + 1)).succ := by
    rw [goodF_cons_succ81]
    rintro ⟨-, hb⟩
    exact absurd (hb rfl) (by decide)
  rw [if_pos h0, if_neg h1, zero_add, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hiff : goodF81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false u))
      i.succ.succ ↔ goodF81 u i := by
    rw [goodF_cons_succ81, goodF_cons_succ81]
    constructor
    · rintro ⟨⟨hg, -⟩, -⟩; exact hg
    · intro hg; refine ⟨⟨hg, fun _ => rfl⟩, fun h => by simp at h⟩
  exact if_congr hiff rfl rfl

theorem degF_snoc_false81 {m : ℕ} (u : Fin m → Bool) :
    degF81 (Fin.snoc (α := fun _ => Bool) u false) = degF81 u + if last81 u then 1 else 0 := by
  unfold degF81
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hiff : goodF81 (Fin.snoc (α := fun _ => Bool) u false) i.castSucc ↔ goodF81 u i := by
      constructor
      · intro ⟨hL, hR⟩
        refine ⟨fun j hj => ?_, fun j hj => ?_⟩
        · have h := hL j.castSucc (by simp [hj]); rw [Fin.snoc_castSucc] at h; exact h
        · have h := hR j.castSucc (by simp [hj]); rw [Fin.snoc_castSucc] at h; exact h
      · intro ⟨hL, hR⟩
        refine ⟨fun j hj => ?_, fun j hj => ?_⟩
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
          · rw [Fin.snoc_castSucc]; exact hL j' (by simp at hj; omega)
          · simp at hj; have := i.isLt; omega
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
          · rw [Fin.snoc_castSucc]; exact hR j' (by simp at hj; omega)
          · rw [Fin.snoc_last]
    exact if_congr hiff rfl rfl
  · have hlast : goodF81 (Fin.snoc (α := fun _ => Bool) u false) (Fin.last m) ↔ last81 u := by
      constructor
      · intro ⟨hL, _⟩ j hj
        have h := hL j.castSucc (by simp [hj])
        rw [Fin.snoc_castSucc] at h
        exact h
      · intro hu
        refine ⟨fun j hj => ?_, fun j hj => ?_⟩
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
          · rw [Fin.snoc_castSucc]; exact hu j' (by simp at hj; omega)
          · simp at hj
        · have := j.isLt; simp at hj; omega
    exact if_congr hlast rfl rfl

theorem first_snoc_false81 {m : ℕ} (u : Fin m → Bool) :
    first81 (Fin.snoc (α := fun _ => Bool) u false) ↔ first81 u := by
  constructor
  · intro h j hj
    have h' := h j.castSucc (by simp [hj])
    rw [Fin.snoc_castSucc] at h'
    exact h'
  · intro h j hj
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]; exact h j' (by simp at hj; omega)
    · rw [Fin.snoc_last]

theorem degF_0u0_81 {m : ℕ} (u : Fin m → Bool) :
    degF81 (Fin.cons (α := fun _ => Bool) false (Fin.snoc (α := fun _ => Bool) u false)) =
      degF81 u + (if first81 u then 1 else 0) + (if last81 u then 1 else 0) := by
  rw [degF_cons_false81, degF_snoc_false81]
  have hf := if_congr (first_snoc_false81 u) (rfl : 1 = 1) (rfl : 0 = 0)
  rw [hf]
  omega

/-- Lucas cube properties for 0w and 10u0. -/
theorem isLuc_cons_false81 {m : ℕ} (w : Fin (m + 1) → Bool) :
    IsLuc (Fin.cons (α := fun _ => Bool) false w) ↔ IsFib81 w := by
  constructor
  · intro h
    exact ((isFib_cons81 false w).1 h.1).2
  · intro hw
    refine ⟨(isFib_cons81 false w).2 ⟨fun h => absurd h (by decide), hw⟩,
      fun i j hi0 _ ⟨hi, _⟩ => ?_⟩
    have ei : i = 0 := Fin.ext hi0
    rw [ei, Fin.cons_zero] at hi
    exact absurd hi (by decide)

theorem deg_cons_false81 {m : ℕ} (w : Fin (m + 1) → Bool) (hw : IsFib81 w) :
    deg (Fin.cons (α := fun _ => Bool) false w) =
      degF81 w + if first81 w ∧ last81 w then 1 else 0 := by
  have hluc : IsLuc (Fin.cons (α := fun _ => Bool) false w) := (isLuc_cons_false81 w).2 hw
  rw [deg_eq_goodL81 (by omega) _ hluc]
  unfold degF81
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hiff : goodL81 (Fin.cons (α := fun _ => Bool) false w) i.succ ↔ goodF81 w i := by
      unfold goodL81
      rw [goodF_cons_succ81]
      constructor
      · rintro ⟨⟨hg, -⟩, -, -⟩; exact hg
      · intro hg
        refine ⟨⟨hg, fun _ => rfl⟩, fun h => by simp at h, fun _ j hj => ?_⟩
        have ej : j = 0 := Fin.ext hj
        rw [ej, Fin.cons_zero]
    exact if_congr hiff rfl rfl
  · have h0 : goodL81 (Fin.cons (α := fun _ => Bool) false w) 0 ↔ first81 w ∧ last81 w := by
      unfold goodL81
      rw [goodF_cons_zero81]
      constructor
      · rintro ⟨hf, h0n, -⟩
        refine ⟨hf, fun j hj => ?_⟩
        have h := h0n rfl j.succ (by simp [hj])
        rw [Fin.cons_succ] at h
        exact h
      · rintro ⟨hf, hl⟩
        refine ⟨hf, fun _ j hj => ?_, fun h => by simp at h⟩
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · simp at hj
        · rw [Fin.cons_succ]; exact hl j' (by simp at hj; omega)
    exact if_congr h0 rfl rfl

theorem isLuc_cons_true81 {m : ℕ} (w : Fin (m + 1) → Bool) :
    IsLuc (Fin.cons (α := fun _ => Bool) true w) ↔ IsFib81 w ∧ first81 w ∧ last81 w := by
  constructor
  · intro ⟨h1, h2⟩
    obtain ⟨hf, hfib⟩ := (isFib_cons81 true w).1 h1
    refine ⟨hfib, hf rfl, fun j hj => ?_⟩
    cases hwj : w j with
    | false => rfl
    | true =>
      have h0 : Fin.cons (α := fun _ => Bool) true w 0 = true := by rw [Fin.cons_zero]
      have hlast : Fin.cons (α := fun _ => Bool) true w j.succ = true := by
        rw [Fin.cons_succ]; exact hwj
      exact (h2 0 j.succ rfl (by simp [hj]) ⟨h0, hlast⟩).elim
  · rintro ⟨hfib, hf, hl⟩
    refine ⟨(isFib_cons81 true w).2 ⟨fun _ => hf, hfib⟩, fun i j hi0 hjn ⟨hi, hj⟩ => ?_⟩
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · simp at hjn
    · rw [Fin.cons_succ] at hj
      rw [hl j' (by simp at hjn; omega)] at hj
      exact absurd hj (by decide)

theorem deg_10u0_81 {m : ℕ} (u : Fin m → Bool) (hu : IsFib81 u) :
    deg (Fin.cons (α := fun _ => Bool) true
        (Fin.cons (α := fun _ => Bool) false (Fin.snoc (α := fun _ => Bool) u false))) =
      degF81 u + 1 := by
  let w : Fin (m + 2) → Bool :=
    Fin.cons (α := fun _ => Bool) false (Fin.snoc (α := fun _ => Bool) u false)
  let v : Fin (m + 3) → Bool := Fin.cons (α := fun _ => Bool) true w
  have hw_fib : IsFib81 w :=
    (isFib_cons81 false _).2 ⟨fun h => absurd h (by decide), (isFib_snoc_false81 u).2 hu⟩
  have hw_first : first81 w := (first_cons81 false _).2 rfl
  have hw_last : last81 w := by
    intro j hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · simp at hj
    · show (Fin.snoc (α := fun _ => Bool) u false) j' = false
      exact (last_snoc81 u false).2 rfl j' (by simp at hj; omega)
  have hv_luc : IsLuc v := (isLuc_cons_true81 w).2 ⟨hw_fib, hw_first, hw_last⟩
  change deg v = degF81 u + 1
  rw [deg_eq_goodL81 (by omega) v hv_luc]
  unfold degF81
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_castSucc]
  have h0 : goodL81 v 0 := by
    refine ⟨(goodF_cons_zero81 true w).2 hw_first, fun _ j hj => ?_, fun h => by simp at h⟩
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · simp at hj
    · show w j' = false
      exact hw_last j' (by simp at hj; omega)
  have h1 : ¬ goodL81 v (0 : Fin (m + 2)).succ := by
    rintro ⟨hg, -, -⟩
    have := ((goodF_cons_succ81 true w 0).1 hg).2 rfl
    exact absurd this (by decide)
  have hlast : ¬ goodL81 v ((Fin.last m).succ.succ) := by
    rintro ⟨-, -, hn0⟩
    have h := hn0 (by simp) 0 rfl
    have hv0 : v 0 = true := by show Fin.cons (α := fun _ => Bool) true w 0 = true; rw [Fin.cons_zero]
    rw [hv0] at h
    exact absurd h (by decide)
  rw [if_pos h0, if_neg h1, if_neg hlast, zero_add, add_zero, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hiff : goodL81 v (j.castSucc.succ.succ) ↔ goodF81 u j := by
    unfold goodL81
    rw [goodF_cons_succ81, goodF_cons_succ81]
    constructor
    · rintro ⟨⟨⟨hg, -⟩, -⟩, -, -⟩
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · have h := hg.1 k.castSucc (by simp [hk]); rw [Fin.snoc_castSucc] at h; exact h
      · have h := hg.2 k.castSucc (by simp [hk]); rw [Fin.snoc_castSucc] at h; exact h
    · intro ⟨hL, hR⟩
      refine ⟨⟨⟨⟨fun k hk => ?_, fun k hk => ?_⟩, fun _ => rfl⟩, fun h => by simp at h⟩,
        fun h => by simp at h, fun h => by have := j.isLt; simp at h; omega⟩
      · rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]; exact hL k' (by simp at hk; omega)
        · have := j.isLt; simp at hk; omega
      · rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]; exact hR k' (by simp at hk; omega)
        · rw [Fin.snoc_last]
  exact if_congr hiff rfl rfl

/-- Sum of f (degF81 v) over Fibonacci strings with first bit false / true. -/
def SA81 (n : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool => IsFib81 v ∧ first81 v), f (degF81 v)

def SB81 (n : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool => IsFib81 v ∧ ¬ first81 v), f (degF81 v)

theorem SA81_zero (f : ℕ → ℤ) : SA81 0 f = f 0 := by
  unfold SA81
  have e : Finset.univ.filter (fun v : Fin 0 → Bool => IsFib81 v ∧ first81 v) = {Fin.elim0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun _ => funext fun i => Fin.elim0 i, fun _ => ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩
  rw [e, Finset.sum_singleton]
  have hd : degF81 (Fin.elim0 : Fin 0 → Bool) = 0 := by unfold degF81; simp
  rw [hd]

theorem SB81_zero (f : ℕ → ℤ) : SB81 0 f = 0 := by
  unfold SB81
  have e : Finset.univ.filter (fun v : Fin 0 → Bool => IsFib81 v ∧ ¬ first81 v) = ∅ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨-, hnf⟩
    exact hnf (fun i => Fin.elim0 i)
  rw [e, Finset.sum_empty]

theorem SB81_one (f : ℕ → ℤ) : SB81 1 f = f 1 := by
  unfold SB81
  have e : Finset.univ.filter (fun v : Fin 1 → Bool => IsFib81 v ∧ ¬ first81 v) =
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
        exfalso; apply hnf; intro j hj; have ej : j = 0 := Fin.ext hj; rw [ej, hv]
    · rintro rfl
      refine ⟨fun i j hij => by have := i.isLt; have := j.isLt; omega, fun hf => ?_⟩
      exact absurd (hf 0 rfl) (by decide)
  rw [e, Finset.sum_singleton]
  have hd : degF81 (fun _ : Fin 1 => true) = 1 := by
    unfold degF81
    have ef : Finset.univ.filter (fun i : Fin 1 => goodF81 (fun _ : Fin 1 => true) i) = {0} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun _ => Fin.ext (by have := i.isLt; omega),
        fun _ => ⟨fun j hj => by have := i.isLt; have := j.isLt; omega,
          fun j hj => by have := i.isLt; have := j.isLt; omega⟩⟩
    rw [ef, Finset.card_singleton]
  rw [hd]

theorem SA81_succ (m : ℕ) (f : ℕ → ℤ) :
    SA81 (m + 1) f = SA81 m (fun d => f (d + 1)) + SB81 m f := by
  unfold SA81 SB81
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  have hcons := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Bool))
    (fun p : Bool × (Fin m → Bool) =>
      if IsFib81 (Fin.cons (α := fun _ => Bool) p.1 p.2) ∧
          first81 (Fin.cons (α := fun _ => Bool) p.1 p.2)
      then f (degF81 (Fin.cons (α := fun _ => Bool) p.1 p.2)) else 0)
    (fun v : Fin (m + 1) → Bool => if IsFib81 v ∧ first81 v then f (degF81 v) else 0)
    (fun _ => rfl)
  rw [← hcons, Fintype.sum_prod_type, Fintype.sum_bool]
  have ht : ∑ w : Fin m → Bool,
      (if IsFib81 (Fin.cons (α := fun _ => Bool) true w) ∧
          first81 (Fin.cons (α := fun _ => Bool) true w)
      then f (degF81 (Fin.cons (α := fun _ => Bool) true w)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    rintro ⟨-, hf⟩
    exact absurd ((first_cons81 true w).1 hf) (by decide)
  rw [ht, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : IsFib81 w
  · have hcf : IsFib81 (Fin.cons (α := fun _ => Bool) false w) :=
      (isFib_cons81 false w).2 ⟨fun h => absurd h (by decide), hw⟩
    have hff : first81 (Fin.cons (α := fun _ => Bool) false w) := (first_cons81 false w).2 rfl
    rw [if_pos ⟨hcf, hff⟩, degF_cons_false81 w]
    by_cases hfw : first81 w
    · rw [if_pos hfw, if_pos ⟨hw, hfw⟩, if_neg (fun h => h.2 hfw), add_zero]
    · rw [if_neg hfw, add_zero, if_neg (fun h => hfw h.2), if_pos ⟨hw, hfw⟩, zero_add]
  · rw [if_neg (fun h => hw ((isFib_cons81 false w).1 h.1).2),
      if_neg (fun h => hw h.1), if_neg (fun h => hw h.1), add_zero]

theorem SB81_succ_succ (m : ℕ) (f : ℕ → ℤ) :
    SB81 (m + 2) f = SA81 m (fun d => f (d + 1)) + SB81 m (fun d => f (d + 1)) := by
  unfold SA81 SB81
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  have hcons1 := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
    (fun p : Bool × (Fin (m + 1) → Bool) =>
      if IsFib81 (Fin.cons (α := fun _ => Bool) p.1 p.2) ∧
          ¬ first81 (Fin.cons (α := fun _ => Bool) p.1 p.2)
      then f (degF81 (Fin.cons (α := fun _ => Bool) p.1 p.2)) else 0)
    (fun v : Fin (m + 2) → Bool => if IsFib81 v ∧ ¬ first81 v then f (degF81 v) else 0)
    (fun _ => rfl)
  rw [← hcons1, Fintype.sum_prod_type, Fintype.sum_bool]
  have hf0 : ∑ w : Fin (m + 1) → Bool,
      (if IsFib81 (Fin.cons (α := fun _ => Bool) false w) ∧
          ¬ first81 (Fin.cons (α := fun _ => Bool) false w)
      then f (degF81 (Fin.cons (α := fun _ => Bool) false w)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    rintro ⟨-, hnf⟩
    exact hnf ((first_cons81 false w).2 rfl)
  rw [hf0, add_zero]
  have hcons2 := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Bool))
    (fun p : Bool × (Fin m → Bool) =>
      if IsFib81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) p.1 p.2)) ∧
          ¬ first81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) p.1 p.2))
      then f (degF81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) p.1 p.2)))
      else 0)
    (fun w : Fin (m + 1) → Bool =>
      if IsFib81 (Fin.cons (α := fun _ => Bool) true w) ∧
          ¬ first81 (Fin.cons (α := fun _ => Bool) true w)
      then f (degF81 (Fin.cons (α := fun _ => Bool) true w)) else 0)
    (fun _ => rfl)
  rw [← hcons2, Fintype.sum_prod_type, Fintype.sum_bool]
  have htt : ∑ u : Fin m → Bool,
      (if IsFib81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) true u)) ∧
          ¬ first81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) true u))
      then f (degF81 (Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) true u)))
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg]
    rintro ⟨hfib, -⟩
    have hf1 := ((isFib_cons81 true _).1 hfib).1 rfl
    exact absurd ((first_cons81 true u).1 hf1) (by decide)
  rw [htt, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : IsFib81 u
  · have hfu : IsFib81 (Fin.cons (α := fun _ => Bool) false u) :=
      (isFib_cons81 false u).2 ⟨fun h => absurd h (by decide), hu⟩
    have htfu : IsFib81 (Fin.cons (α := fun _ => Bool) true
        (Fin.cons (α := fun _ => Bool) false u)) :=
      (isFib_cons81 true _).2 ⟨fun _ => (first_cons81 false u).2 rfl, hfu⟩
    have hnt : ¬ first81 (Fin.cons (α := fun _ => Bool) true
        (Fin.cons (α := fun _ => Bool) false u)) := by
      intro h; exact absurd ((first_cons81 true _).1 h) (by decide)
    rw [if_pos ⟨htfu, hnt⟩, degF_cons_true_false81 u]
    by_cases hfirst : first81 u
    · rw [if_pos ⟨hu, hfirst⟩, if_neg (fun h => h.2 hfirst), add_zero]
    · rw [if_neg (fun h => hfirst h.2), if_pos ⟨hu, hfirst⟩, zero_add]
  · rw [if_neg (fun h => hu ((isFib_cons81 false u).1 ((isFib_cons81 true _).1 h.1).2).2),
      if_neg (fun h => hu h.1), if_neg (fun h => hu h.1), add_zero]

theorem sum_fib_split81 (n : ℕ) (f : ℕ → ℤ) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool => IsFib81 v), f (degF81 v) =
      SA81 n f + SB81 n f := by
  unfold SA81 SB81
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : IsFib81 v
  · by_cases hf : first81 v
    · rw [if_pos hv, if_pos ⟨hv, hf⟩, if_neg (fun h => h.2 hf), add_zero]
    · rw [if_pos hv, if_neg (fun h => hf h.2), if_pos ⟨hv, hf⟩, zero_add]
  · rw [if_neg hv, if_neg (fun h => hv h.1), if_neg (fun h => hv h.1), add_zero]

/-- Reversal symmetry: number of Fibonacci strings ending in 0 equals number starting in 0. -/
theorem sum_last_eq_first81 (m : ℕ) :
    ∑ u ∈ Finset.univ.filter (fun u : Fin m → Bool => IsFib81 u),
        (if last81 u then (1 : ℤ) else 0) =
      SA81 m (fun _ => 1) := by
  unfold SA81
  rw [Finset.sum_filter, Finset.sum_filter]
  let e : (Fin m → Bool) ≃ (Fin m → Bool) :=
    { toFun := fun u i => u i.rev
      invFun := fun u i => u i.rev
      left_inv := fun u => by funext i; simp
      right_inv := fun u => by funext i; simp }
  rw [← Fintype.sum_equiv e _ (fun u => if IsFib81 u ∧ first81 u then (1 : ℤ) else 0) (fun _ => rfl)]
  apply Finset.sum_congr rfl
  intro u _
  have hfib : IsFib81 (e u) ↔ IsFib81 u := by
    constructor
    · intro h i j hij ⟨hi, hj⟩
      have hstep : i.rev.val = j.rev.val + 1 := by
        have := i.isLt; have := j.isLt
        simp only [Fin.val_rev]
        omega
      have hj' : e u j.rev = true := by change u j.rev.rev = true; simp [hj]
      have hi' : e u i.rev = true := by change u i.rev.rev = true; simp [hi]
      exact h j.rev i.rev hstep ⟨hj', hi'⟩
    · intro h i j hij ⟨hi, hj⟩
      have hstep : i.rev.val = j.rev.val + 1 := by
        have := i.isLt; have := j.isLt
        simp only [Fin.val_rev]
        omega
      exact h j.rev i.rev hstep ⟨hj, hi⟩
  have hfl : first81 (e u) ↔ last81 u := by
    constructor
    · intro h j hj
      have h' := h j.rev (by have := j.isLt; simp only [Fin.val_rev]; omega)
      change u j.rev.rev = false at h'
      simp at h'
      exact h'
    · intro h j hj
      exact h j.rev (by have := j.isLt; simp only [Fin.val_rev]; omega)
  by_cases hu : IsFib81 u
  · by_cases hl : last81 u
    · rw [if_pos hu, if_pos hl, if_pos ⟨hfib.2 hu, hfl.2 hl⟩]
    · rw [if_pos hu, if_neg hl, if_neg (fun h => hl (hfl.1 h.2))]
  · rw [if_neg hu, if_neg (fun h => hu (hfib.1 h.1))]

/-- Bijection between Fibonacci strings of length m+2 with first and last bits false and
all Fibonacci strings of length m. -/
theorem sum_0u0_81 (m : ℕ) (g : (Fin (m + 2) → Bool) → ℤ) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin (m + 2) → Bool => IsFib81 w ∧ first81 w ∧ last81 w),
        g w =
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Bool => IsFib81 u),
        g (Fin.cons (α := fun _ => Bool) false (Fin.snoc (α := fun _ => Bool) u false)) := by
  symm
  refine Finset.sum_bij (fun u _ =>
      Fin.cons (α := fun _ => Bool) false (Fin.snoc (α := fun _ => Bool) u false)) ?_ ?_ ?_ ?_
  · intro u hu
    have hfib := (Finset.mem_filter.1 hu).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, (first_cons81 false _).2 rfl, ?_⟩
    · exact (isFib_cons81 false _).2 ⟨fun h => absurd h (by decide), (isFib_snoc_false81 u).2 hfib⟩
    · intro j hj
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp at hj
      · rw [Fin.cons_succ]
        exact (last_snoc81 u false).2 rfl j' (by simp at hj; omega)
  · intro u1 _ u2 _ heq
    funext i
    have h := congrFun heq i.castSucc.succ
    rw [Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_castSucc] at h
    exact h
  · intro w hw
    obtain ⟨hfib, hf, hl⟩ := (Finset.mem_filter.1 hw).2
    let u : Fin m → Bool := fun i => w i.castSucc.succ
    have hu_fib : IsFib81 u := by
      intro i j hij ⟨hi, hj⟩
      exact hfib i.castSucc.succ j.castSucc.succ (by simp [hij]) ⟨hi, hj⟩
    refine ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, hu_fib⟩, ?_⟩
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rw [Fin.cons_zero]
      exact (hf 0 rfl).symm
    · rw [Fin.cons_succ]
      rcases Fin.eq_castSucc_or_eq_last i' with ⟨j, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
      · rw [Fin.snoc_last]
        exact (hl (Fin.last m).succ (by simp)).symm
  · intro _ _; rfl

/-- The miracle identity expressing a(m + 3) purely in terms of Fibonacci cube moments. -/
theorem lucas_miracle81 (m : ℕ) :
    (a (m + 3) : ℤ) =
      (SA81 (m + 2) (fun d => (d : ℤ) ^ 2) + SB81 (m + 2) (fun d => (d : ℤ) ^ 2)) +
      (SA81 m (fun d => (d : ℤ) ^ 2) + SB81 m (fun d => (d : ℤ) ^ 2)) +
      4 * (SA81 m (fun d => (d : ℤ)) + SB81 m (fun d => (d : ℤ))) +
      4 * SA81 m (fun _ => 1) +
      2 * (SA81 m (fun _ => 1) + SB81 m (fun _ => 1)) := by
  unfold a
  rw [Nat.cast_sum, Finset.sum_filter]
  have hcons := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 3) => Bool))
    (fun p : Bool × (Fin (m + 2) → Bool) =>
      if IsLuc (Fin.cons (α := fun _ => Bool) p.1 p.2)
      then ((deg (Fin.cons (α := fun _ => Bool) p.1 p.2) ^ 2 : ℕ) : ℤ) else 0)
    (fun v : Fin (m + 3) → Bool => if IsLuc v then ((deg v ^ 2 : ℕ) : ℤ) else 0)
    (fun _ => rfl)
  rw [← hcons, Fintype.sum_prod_type, Fintype.sum_bool]
  -- Part 1: v = Fin.cons true w
  have part1 : ∑ w : Fin (m + 2) → Bool,
      (if IsLuc (Fin.cons (α := fun _ => Bool) true w)
        then ((deg (Fin.cons (α := fun _ => Bool) true w) ^ 2 : ℕ) : ℤ) else 0) =
      (SA81 m (fun d => (d : ℤ) ^ 2) + SB81 m (fun d => (d : ℤ) ^ 2)) +
      2 * (SA81 m (fun d => (d : ℤ)) + SB81 m (fun d => (d : ℤ))) +
      (SA81 m (fun _ => 1) + SB81 m (fun _ => 1)) := by
    have e1 : ∑ w : Fin (m + 2) → Bool,
        (if IsLuc (Fin.cons (α := fun _ => Bool) true w)
          then ((deg (Fin.cons (α := fun _ => Bool) true w) ^ 2 : ℕ) : ℤ) else 0) =
        ∑ w ∈ Finset.univ.filter (fun w : Fin (m + 2) → Bool =>
            IsFib81 w ∧ first81 w ∧ last81 w),
          ((deg (Fin.cons (α := fun _ => Bool) true w) ^ 2 : ℕ) : ℤ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _
      exact if_congr (isLuc_cons_true81 w) rfl rfl
    rw [e1, sum_0u0_81 m]
    have e2 : ∑ u ∈ Finset.univ.filter (fun u : Fin m → Bool => IsFib81 u),
        ((deg (Fin.cons (α := fun _ => Bool) true
          (Fin.cons (α := fun _ => Bool) false (Fin.snoc (α := fun _ => Bool) u false))) ^ 2 : ℕ) : ℤ) =
        ∑ u ∈ Finset.univ.filter (fun u : Fin m → Bool => IsFib81 u),
          ((degF81 u : ℤ) ^ 2 + 2 * (degF81 u : ℤ) + 1) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [deg_10u0_81 u (Finset.mem_filter.1 hu).2]
      push_cast
      ring
    rw [e2, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_fib_split81 m (fun d => (d : ℤ) ^ 2), sum_fib_split81 m (fun d => (d : ℤ)),
      sum_fib_split81 m (fun _ => 1)]
  -- Part 0: v = Fin.cons false w
  have part0 : ∑ w : Fin (m + 2) → Bool,
      (if IsLuc (Fin.cons (α := fun _ => Bool) false w)
        then ((deg (Fin.cons (α := fun _ => Bool) false w) ^ 2 : ℕ) : ℤ) else 0) =
      (SA81 (m + 2) (fun d => (d : ℤ) ^ 2) + SB81 (m + 2) (fun d => (d : ℤ) ^ 2)) +
      2 * (SA81 m (fun d => (d : ℤ)) + SB81 m (fun d => (d : ℤ))) +
      4 * SA81 m (fun _ => 1) +
      (SA81 m (fun _ => 1) + SB81 m (fun _ => 1)) := by
    have e1 : ∑ w : Fin (m + 2) → Bool,
        (if IsLuc (Fin.cons (α := fun _ => Bool) false w)
          then ((deg (Fin.cons (α := fun _ => Bool) false w) ^ 2 : ℕ) : ℤ) else 0) =
        ∑ w ∈ Finset.univ.filter (fun w : Fin (m + 2) → Bool => IsFib81 w),
          ((degF81 w : ℤ) ^ 2 +
            if first81 w ∧ last81 w then 2 * (degF81 w : ℤ) + 1 else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : IsFib81 w
      · rw [if_pos ((isLuc_cons_false81 w).2 hw), if_pos hw, deg_cons_false81 w hw]
        by_cases hfl : first81 w ∧ last81 w
        · rw [if_pos hfl, if_pos hfl]; push_cast; ring
        · rw [if_neg hfl, if_neg hfl, add_zero, add_zero]; push_cast; rfl
      · rw [if_neg (fun h => hw ((isLuc_cons_false81 w).1 h)), if_neg hw]
    rw [e1, Finset.sum_add_distrib, sum_fib_split81 (m + 2) (fun d => (d : ℤ) ^ 2)]
    have e2 : ∑ w ∈ Finset.univ.filter (fun w : Fin (m + 2) → Bool => IsFib81 w),
        (if first81 w ∧ last81 w then 2 * (degF81 w : ℤ) + 1 else 0) =
        ∑ w ∈ Finset.univ.filter (fun w : Fin (m + 2) → Bool =>
            IsFib81 w ∧ first81 w ∧ last81 w),
          (2 * (degF81 w : ℤ) + 1) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : IsFib81 w
      · by_cases hfl : first81 w ∧ last81 w
        · rw [if_pos hw, if_pos hfl, if_pos ⟨hw, hfl⟩]
        · rw [if_pos hw, if_neg hfl, if_neg (fun h => hfl h.2)]
      · rw [if_neg hw, if_neg (fun h => hw h.1)]
    rw [e2, sum_0u0_81 m]
    have e3 : ∑ u ∈ Finset.univ.filter (fun u : Fin m → Bool => IsFib81 u),
        (2 * (degF81 (Fin.cons (α := fun _ => Bool) false
          (Fin.snoc (α := fun _ => Bool) u false)) : ℤ) + 1) =
        ∑ u ∈ Finset.univ.filter (fun u : Fin m → Bool => IsFib81 u),
          (2 * (degF81 u : ℤ) + 2 * (if first81 u then (1 : ℤ) else 0) +
            2 * (if last81 u then (1 : ℤ) else 0) + 1) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [degF_0u0_81 u]
      by_cases hf : first81 u <;> by_cases hl : last81 u
      · rw [if_pos hf, if_pos hl, if_pos hf, if_pos hl]; push_cast; ring
      · rw [if_pos hf, if_neg hl, if_pos hf, if_neg hl]; push_cast; ring
      · rw [if_neg hf, if_pos hl, if_neg hf, if_pos hl]; push_cast; ring
      · rw [if_neg hf, if_neg hl, if_neg hf, if_neg hl]; push_cast; ring
    have hfsum : ∑ u ∈ Finset.univ.filter (fun u : Fin m → Bool => IsFib81 u),
        (if first81 u then (1 : ℤ) else 0) = SA81 m (fun _ => 1) := by
      unfold SA81
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : IsFib81 u
      · by_cases hf : first81 u
        · rw [if_pos hu, if_pos hf, if_pos ⟨hu, hf⟩]
        · rw [if_pos hu, if_neg hf, if_neg (fun h => hf h.2)]
      · rw [if_neg hu, if_neg (fun h => hu h.1)]
    rw [e3, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_fib_split81 m (fun d => (d : ℤ)), sum_fib_split81 m (fun _ => 1), hfsum,
      sum_last_eq_first81]
    ring
  rw [part1, part0]
  ring

/-- Pure algebraic elimination for the Lucas cube Zagreb sequence. -/
theorem luc_moments_rec81 (A0 B0 A1 B1 A2 B2 : ℕ → ℤ)
    (h00 : A0 0 = 1) (hb01 : B0 1 = 1)
    (hA0 : ∀ m, A0 (m + 1) = A0 m + B0 m)
    (hB0 : ∀ m, B0 (m + 2) = A0 m + B0 m)
    (hA1 : ∀ m, A1 (m + 1) = A1 m + A0 m + B1 m)
    (hB1 : ∀ m, B1 (m + 2) = A1 m + A0 m + B1 m + B0 m)
    (hA2 : ∀ m, A2 (m + 1) = A2 m + 2 * A1 m + A0 m + B2 m)
    (hB2 : ∀ m, B2 (m + 2) = A2 m + 2 * A1 m + A0 m + B2 m + 2 * B1 m + B0 m) :
    let L : ℕ → ℤ := fun m =>
      (A2 (m + 2) + B2 (m + 2)) + (A2 m + B2 m) + 4 * (A1 m + B1 m) +
        4 * A0 m + 2 * (A0 m + B0 m)
    ∀ m, L (m + 6) = 3 * L (m + 5) - 5 * L (m + 3) + 3 * L (m + 1) + L m := by
  intro L
  let T0 : ℕ → ℤ := fun m => A0 m + B0 m
  let T1 : ℕ → ℤ := fun m => A1 m + B1 m
  let T2 : ℕ → ℤ := fun m => A2 m + B2 m
  have hBA : ∀ m, B0 (m + 1) = A0 m := by
    intro m
    cases m with
    | zero => rw [hb01, h00]
    | succ k => rw [hB0 k, hA0 k]
  have eA0 : ∀ m, A0 (m + 2) - A0 (m + 1) - A0 m = 0 := by
    intro m
    have h1 := hA0 (m + 1)
    have h2 := hBA m
    linarith
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
  have eL : ∀ m, L (m + 2) - L (m + 1) - L m =
      4 * T1 (m + 2) + 2 * T0 (m + 3) + 4 * T1 m + 2 * T0 (m + 1) + 8 * T0 m := by
    intro m
    change (T2 (m + 4) + T2 (m + 2) + 4 * T1 (m + 2) + 4 * A0 (m + 2) + 2 * T0 (m + 2)) -
      (T2 (m + 3) + T2 (m + 1) + 4 * T1 (m + 1) + 4 * A0 (m + 1) + 2 * T0 (m + 1)) -
      (T2 (m + 2) + T2 m + 4 * T1 m + 4 * A0 m + 2 * T0 m) = _
    have q1 := eT2 (m + 2)
    have q2 := eT2 m
    have q3 := eT1 m
    have q4 := eA0 m
    have q5 := eT0 m
    linarith
  have eeL : ∀ m, L (m + 4) - 2 * L (m + 3) - L (m + 2) + 2 * L (m + 1) + L m =
      8 * T0 (m + 2) + 8 * T0 m := by
    intro m
    have r2 := eL (m + 2)
    have r1 := eL (m + 1)
    have r0 := eL m
    have t1a := eT1 (m + 2)
    have t1b := eT1 m
    have t0a := eT0 (m + 3)
    have t0b := eT0 (m + 1)
    have t0c := eT0 m
    linarith
  intro m
  have s2 := eeL (m + 2)
  have s1 := eeL (m + 1)
  have s0 := eeL m
  have u2 := eT0 (m + 2)
  have u0 := eT0 m
  linarith

theorem a_one81 : a 1 = 0 := by decide
theorem a_two81 : a 2 = 6 := by decide

theorem OMA.solution : type_of% @OMA.S_oeis_a307181.main := by
  obtain ⟨A0, hA0def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SA81 n (fun _ => 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨B0, hB0def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SB81 n (fun _ => 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨A1, hA1def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SA81 n (fun d => (d : ℤ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨B1, hB1def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SB81 n (fun d => (d : ℤ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SA81 n (fun d => (d : ℤ) ^ 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨B2, hB2def⟩ : ∃ g : ℕ → ℤ, ∀ n, g n = SB81 n (fun d => (d : ℤ) ^ 2) := ⟨_, fun _ => rfl⟩
  have hSA_add : ∀ n (f g : ℕ → ℤ), SA81 n (fun d => f d + g d) = SA81 n f + SA81 n g := by
    intro n f g; unfold SA81; exact Finset.sum_add_distrib
  have hSB_add : ∀ n (f g : ℕ → ℤ), SB81 n (fun d => f d + g d) = SB81 n f + SB81 n g := by
    intro n f g; unfold SB81; exact Finset.sum_add_distrib
  have hSA_mul : ∀ n (c : ℤ) (f : ℕ → ℤ), SA81 n (fun d => c * f d) = c * SA81 n f := by
    intro n c f; unfold SA81; exact (Finset.mul_sum _ _ _).symm
  have hSB_mul : ∀ n (c : ℤ) (f : ℕ → ℤ), SB81 n (fun d => c * f d) = c * SB81 n f := by
    intro n c f; unfold SB81; exact (Finset.mul_sum _ _ _).symm
  have hA0_0 : A0 0 = 1 := by rw [hA0def, SA81_zero]
  have hB0_0 : B0 0 = 0 := by rw [hB0def, SB81_zero]
  have hB0_1 : B0 1 = 1 := by rw [hB0def, SB81_one]
  have hA1_0 : A1 0 = 0 := by rw [hA1def, SA81_zero]; norm_num
  have hB1_0 : B1 0 = 0 := by rw [hB1def, SB81_zero]
  have hB1_1 : B1 1 = 1 := by rw [hB1def, SB81_one]; norm_num
  have hA2_0 : A2 0 = 0 := by rw [hA2def, SA81_zero]; norm_num
  have hB2_0 : B2 0 = 0 := by rw [hB2def, SB81_zero]
  have hB2_1 : B2 1 = 1 := by rw [hB2def, SB81_one]; norm_num
  have hA0 : ∀ m, A0 (m + 1) = A0 m + B0 m := by
    intro m; rw [hA0def, SA81_succ, ← hA0def, ← hB0def]
  have hB0 : ∀ m, B0 (m + 2) = A0 m + B0 m := by
    intro m; rw [hB0def, SB81_succ_succ, ← hA0def, ← hB0def]
  have hA1 : ∀ m, A1 (m + 1) = A1 m + A0 m + B1 m := by
    intro m
    rw [hA1def, SA81_succ]
    have e : (fun d : ℕ => ((d + 1 : ℕ) : ℤ)) = (fun d : ℕ => (d : ℤ) + 1) := by
      funext d; push_cast; rfl
    rw [e, hSA_add, ← hA1def, ← hA0def, ← hB1def]
  have hB1 : ∀ m, B1 (m + 2) = A1 m + A0 m + B1 m + B0 m := by
    intro m
    rw [hB1def, SB81_succ_succ]
    have e : (fun d : ℕ => ((d + 1 : ℕ) : ℤ)) = (fun d : ℕ => (d : ℤ) + 1) := by
      funext d; push_cast; rfl
    rw [e, hSA_add, hSB_add, ← hA1def, ← hA0def, ← hB1def, ← hB0def]
    ring
  have hA2 : ∀ m, A2 (m + 1) = A2 m + 2 * A1 m + A0 m + B2 m := by
    intro m
    rw [hA2def, SA81_succ]
    have e : (fun d : ℕ => ((d + 1 : ℕ) : ℤ) ^ 2) =
        (fun d : ℕ => ((d : ℤ) ^ 2 + 2 * (d : ℤ)) + 1) := by
      funext d; push_cast; ring
    rw [e, hSA_add, hSA_add, hSA_mul, ← hA2def, ← hA1def, ← hA0def, ← hB2def]
  have hB2 : ∀ m, B2 (m + 2) = A2 m + 2 * A1 m + A0 m + B2 m + 2 * B1 m + B0 m := by
    intro m
    rw [hB2def, SB81_succ_succ]
    have e : (fun d : ℕ => ((d + 1 : ℕ) : ℤ) ^ 2) =
        (fun d : ℕ => ((d : ℤ) ^ 2 + 2 * (d : ℤ)) + 1) := by
      funext d; push_cast; ring
    rw [e, hSA_add, hSA_add, hSA_mul, hSB_add, hSB_add, hSB_mul,
      ← hA2def, ← hA1def, ← hA0def, ← hB2def, ← hB1def, ← hB0def]
    ring
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℤ, ∀ n, (a n : ℤ) = b n := ⟨_, fun _ => rfl⟩
  have hmir : ∀ m, b (m + 3) =
      (A2 (m + 2) + B2 (m + 2)) + (A2 m + B2 m) + 4 * (A1 m + B1 m) +
        4 * A0 m + 2 * (A0 m + B0 m) := by
    intro m
    rw [← hb, lucas_miracle81 m, ← hA2def, ← hB2def, ← hA1def, ← hB1def, ← hA0def, ← hB0def,
      ← hA2def m, ← hB2def m]
  have hrec : ∀ m, b (m + 9) = 3 * b (m + 8) - 5 * b (m + 6) + 3 * b (m + 4) + b (m + 3) := by
    intro m
    have h := luc_moments_rec81 A0 B0 A1 B1 A2 B2 hA0_0 hB0_1 hA0 hB0 hA1 hB1 hA2 hB2 m
    dsimp only at h
    rw [show m + 9 = (m + 6) + 3 by omega, show m + 8 = (m + 5) + 3 by omega,
      show m + 6 = (m + 3) + 3 by omega, show m + 4 = (m + 1) + 3 by omega,
      hmir (m + 6), hmir (m + 5), hmir (m + 3), hmir (m + 1), hmir m]
    exact h
  -- Initial Fibonacci moments up to 7
  have hA0_1 : A0 1 = 1 := by have := hA0 0; linarith
  have hA0_2 : A0 2 = 2 := by have := hA0 1; linarith
  have hB0_2 : B0 2 = 1 := by have := hB0 0; linarith
  have hA0_3 : A0 3 = 3 := by have := hA0 2; linarith
  have hB0_3 : B0 3 = 2 := by have := hB0 1; linarith
  have hA0_4 : A0 4 = 5 := by have := hA0 3; linarith
  have hB0_4 : B0 4 = 3 := by have := hB0 2; linarith
  have hA0_5 : A0 5 = 8 := by have := hA0 4; linarith
  have hB0_5 : B0 5 = 5 := by have := hB0 3; linarith
  have hA0_6 : A0 6 = 13 := by have := hA0 5; linarith
  have hB0_6 : B0 6 = 8 := by have := hB0 4; linarith
  have hA1_1 : A1 1 = 1 := by have := hA1 0; linarith
  have hA1_2 : A1 2 = 3 := by have := hA1 1; linarith
  have hB1_2 : B1 2 = 1 := by have := hB1 0; linarith
  have hA1_3 : A1 3 = 6 := by have := hA1 2; linarith
  have hB1_3 : B1 3 = 4 := by have := hB1 1; linarith
  have hA1_4 : A1 4 = 13 := by have := hA1 3; linarith
  have hB1_4 : B1 4 = 7 := by have := hB1 2; linarith
  have hA1_5 : A1 5 = 25 := by have := hA1 4; linarith
  have hB1_5 : B1 5 = 15 := by have := hB1 3; linarith
  have hA1_6 : A1 6 = 48 := by have := hA1 5; linarith
  have hB1_6 : B1 6 = 28 := by have := hB1 4; linarith
  have hA2_1 : A2 1 = 1 := by have := hA2 0; linarith
  have hA2_2 : A2 2 = 5 := by have := hA2 1; linarith
  have hB2_2 : B2 2 = 1 := by have := hB2 0; linarith
  have hA2_3 : A2 3 = 14 := by have := hA2 2; linarith
  have hB2_3 : B2 3 = 8 := by have := hB2 1; linarith
  have hA2_4 : A2 4 = 37 := by have := hA2 3; linarith
  have hB2_4 : B2 4 = 17 := by have := hB2 2; linarith
  have hA2_5 : A2 5 = 85 := by have := hA2 4; linarith
  have hB2_5 : B2 5 = 47 := by have := hB2 3; linarith
  have hA2_6 : A2 6 = 190 := by have := hA2 5; linarith
  have hB2_6 : B2 6 = 102 := by have := hB2 4; linarith
  have hA2_7 : A2 7 = 401 := by have := hA2 6; linarith
  have hB2_7 : B2 7 = 225 := by have := hB2 5; linarith
  have vb1 : b 1 = 0 := by rw [← hb, a_one81]; rfl
  have vb2 : b 2 = 6 := by rw [← hb, a_two81]; rfl
  have vb3 : b 3 = 12 := by have := hmir 0; linarith
  have vb4 : b 4 = 40 := by have := hmir 1; linarith
  have vb5 : b 5 = 90 := by have := hmir 2; linarith
  have vb6 : b 6 = 216 := by have := hmir 3; linarith
  have vb7 : b 7 = 462 := by have := hmir 4; linarith
  have vb8 : b 8 = 976 := by have := hmir 5; linarith
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 3 = m + 6 by omega,
      show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega]
    simp only [hb]
    exact hrec m
  · obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, ∀ n, f n = if n = 0 then (0 : ℚ) else (a n : ℚ) :=
      ⟨_, fun _ => rfl⟩
    have hfun : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = f :=
      funext fun n => (hf n).symm
    have f_pos : ∀ k, f (k + 1) = (b (k + 1) : ℚ) := by
      intro k
      rw [hf, if_neg (Nat.succ_ne_zero k)]
      have h := hb (k + 1)
      exact_mod_cast h
    have f0 : f 0 = 0 := by rw [hf, if_pos rfl]
    have f1 : f 1 = 0 := by rw [f_pos 0, vb1]; norm_num
    have f2 : f 2 = 6 := by rw [f_pos 1, vb2]; norm_num
    have f3 : f 3 = 12 := by rw [f_pos 2, vb3]; norm_num
    have f4 : f 4 = 40 := by rw [f_pos 3, vb4]; norm_num
    have f5 : f 5 = 90 := by rw [f_pos 4, vb5]; norm_num
    have f6 : f 6 = 216 := by rw [f_pos 5, vb6]; norm_num
    have f7 : f 7 = 462 := by rw [f_pos 6, vb7]; norm_num
    have f8 : f 8 = 976 := by rw [f_pos 7, vb8]; norm_num
    have frec : ∀ m, f (m + 9) = 3 * f (m + 8) - 5 * f (m + 6) + 3 * f (m + 4) + f (m + 3) := by
      intro m
      rw [show m + 9 = (m + 8) + 1 by omega, show m + 8 = (m + 7) + 1 by omega,
        show m + 6 = (m + 5) + 1 by omega, show m + 4 = (m + 3) + 1 by omega,
        show m + 3 = (m + 2) + 1 by omega, f_pos, f_pos, f_pos, f_pos, f_pos]
      rw [show m + 8 + 1 = m + 9 by omega, show m + 7 + 1 = m + 8 by omega,
        show m + 5 + 1 = m + 6 by omega, show m + 3 + 1 = m + 4 by omega,
        show m + 2 + 1 = m + 3 by omega]
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
    have e2 : (2 * PowerSeries.X ^ 2 * (3 - 3 * PowerSeries.X + 2 * PowerSeries.X ^ 2 +
        3 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 - PowerSeries.X ^ 6) : PowerSeries ℚ) =
        PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6
          - PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6
          + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
          + PowerSeries.X ^ 6 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6
          - PowerSeries.X ^ 7 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
          - PowerSeries.X ^ 8 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
      ring
    rw [e, e2]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
    rcases Nat.lt_or_ge n 9 with hn | hn
    · interval_cases n
      · norm_num [f0]
      · norm_num [f0, f1]
      · norm_num [f1, f2]
      · norm_num [f0, f2, f3]
      · norm_num [f1, f3, f4]
      · norm_num [f0, f2, f4, f5]
      · norm_num [f0, f1, f3, f5, f6]
      · norm_num [f1, f2, f4, f6, f7]
      · norm_num [f2, f3, f5, f7, f8]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      rw [if_pos (by omega : 1 ≤ m + 9), if_pos (by omega : 3 ≤ m + 9),
        if_pos (by omega : 5 ≤ m + 9), if_pos (by omega : 6 ≤ m + 9),
        if_pos (by omega : 2 ≤ m + 9), if_pos (by omega : 3 ≤ m + 9),
        if_pos (by omega : 4 ≤ m + 9), if_pos (by omega : 6 ≤ m + 9),
        if_pos (by omega : 7 ≤ m + 9), if_pos (by omega : 8 ≤ m + 9),
        if_neg (by omega : ¬ (m + 9 - 2 = 0)), if_neg (by omega : ¬ (m + 9 - 3 = 0)),
        if_neg (by omega : ¬ (m + 9 - 4 = 0)), if_neg (by omega : ¬ (m + 9 - 6 = 0)),
        if_neg (by omega : ¬ (m + 9 - 7 = 0)), if_neg (by omega : ¬ (m + 9 - 8 = 0)),
        show m + 9 - 1 = m + 8 by omega, show m + 9 - 3 = m + 6 by omega,
        show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, frec m]
      ring
