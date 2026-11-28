import OMAStatements.S_oeis_a372556

namespace JacobsthalCoins

open OMA.S_oeis_a372556
open Multiset

private theorem step (i : ℕ) :
    (Even i → jac (i + 1) = 2 * jac i + 1) ∧
    (Odd i → 2 * jac i = jac (i + 1) + 1) := by
  induction i with
  | zero => simp [jac]
  | succ i ih =>
    constructor
    · intro he
      have h := ih.2 (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he))
      rw [jac]
      omega
    · intro ho
      have h := ih.1 (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp ho))
      rw [jac]
      omega

private theorem evenTwo (i : ℕ) (hi : Even i) :
    jac (i + 2) = 4 * jac i + 1 := by
  rw [jac, (step i).1 hi]
  omega

private theorem jacMono : Monotone jac := by
  apply monotone_nat_of_le_succ
  intro i
  cases i with
  | zero => decide
  | succ i =>
    rw [jac]
    omega

private theorem jacLower (i : ℕ) (hi : 2 ≤ i) : i - 1 ≤ jac i := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases hb : 2 ≤ i
    · have hp : jac (i - 1) ≥ 1 := jacMono (by omega : 1 ≤ i - 1)
      have hrec : jac (i + 1) = jac i + 2 * jac (i - 1) := by
        conv_lhs => rw [show i + 1 = i - 1 + 2 by omega, jac]
        rw [show i - 1 + 1 = i by omega]
      have h := ih hb
      omega
    · have : i = 1 := by omega
      subst i
      decide

@[local simp] private theorem valueAdd (s t : Multiset ℕ) :
    value (s + t) = value s + value t := by simp [value]

@[local simp] private theorem valueRep (c i : ℕ) :
    value (replicate c i) = c * jac i := by simp [value]

@[local simp] private theorem valueOne (i : ℕ) : value {i} = jac i := by simp [value]

/-- The exponential score favors larger coins in the exchanges below. -/
private def score (s : Multiset ℕ) : ℕ := (s.map fun i => 3 ^ i).sum

@[local simp] private theorem scoreAdd (s t : Multiset ℕ) :
    score (s + t) = score s + score t := by simp [score]

@[local simp] private theorem scoreRep (c i : ℕ) :
    score (replicate c i) = c * 3 ^ i := by simp [score]

@[local simp] private theorem scoreOne (i : ℕ) : score {i} = 3 ^ i := by simp [score]

private def Preferred (m : Multiset ℕ) : Prop :=
  optimal (value m) m ∧
    ∀ t, represents (value m) t → t.card = m.card → score t ≤ score m

private theorem preferredPart {m s : Multiset ℕ} (hm : Preferred m) (hs : s ≤ m) :
    Preferred s := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp hs
  have hu : ∀ j ∈ u, 2 ≤ j := fun j hj => hm.1.1.1 j (mem_add.mpr (Or.inr hj))
  have join (t : Multiset ℕ) (ht : represents (value s) t) :
      represents (value (s + u)) (t + u) := by
    refine ⟨?_, by simp [ht.2]⟩
    intro j hj
    exact (mem_add.mp hj).elim (ht.1 j) (hu j)
  refine ⟨⟨⟨fun j hj => hm.1.1.1 j (mem_add.mpr (Or.inl hj)), rfl⟩, ?_⟩, ?_⟩
  · intro t ht
    have h := hm.1.2 (t + u) (join t ht)
    simpa using h
  · intro t ht hc
    have h := hm.2 (t + u) (join t ht) (by simp [hc])
    simpa using h

private theorem noReplacement {m s t : Multiset ℕ} (hm : Preferred m) (hs : s ≤ m)
    (ht : ∀ j ∈ t, 2 ≤ j) (hv : value t = value s)
    (hc : t.card ≤ s.card) (hw : score s < score t) : False := by
  have hp := preferredPart hm hs
  have hr : represents (value s) t := ⟨ht, hv⟩
  have he : t.card = s.card := Nat.le_antisymm hc (hp.1.2 t hr)
  exact (not_lt_of_ge (hp.2 t hr he)) hw

private theorem splitAt (m : Multiset ℕ) (i : ℕ) :
    replicate (count i m) i + m.filter (· ≠ i) = m := by
  simpa only [Multiset.filter_eq'] using Multiset.filter_add_not (· = i) m

private theorem enoughCopies {m : Multiset ℕ} {c i : ℕ} (h : c ≤ count i m) :
    replicate c i ≤ m := by
  conv_rhs => rw [← splitAt m i]
  exact (Multiset.replicate_le_replicate i |>.2 h).trans (Multiset.le_add_right _ _)

private theorem extraCoin {m : Multiset ℕ} {c i j : ℕ}
    (h : c ≤ count i m) (hj : j ∈ m) (hne : j ≠ i) :
    replicate c i + {j} ≤ m := by
  conv_rhs => rw [← splitAt m i]
  exact add_le_add (Multiset.replicate_le_replicate i |>.2 h)
    (Multiset.singleton_le.mpr (Multiset.mem_filter.mpr ⟨hj, hne⟩))

/-- Two odd-indexed coins can be replaced by the next coin and a unit coin. -/
private theorem noOddDouble {m : Multiset ℕ} (hm : Preferred m) {i : ℕ}
    (hi : Odd i) (h : 2 ≤ count i m) : False := by
  have hstep := (step i).2 hi
  have hi' : 2 ≤ i := hm.1.1.1 i (Multiset.count_pos.mp (by omega))
  apply noReplacement hm (enoughCopies h) (t := ({i + 1} + {2} : Multiset ℕ))
  · simp only [mem_add, mem_singleton]
    intro j hj
    rcases hj with rfl | rfl <;> omega
  · simp only [valueAdd, valueOne, valueRep]
    change jac (i + 1) + 1 = 2 * jac i
    omega
  · simp
  · simp only [scoreAdd, scoreOne, scoreRep, pow_succ]
    have hp : 0 < 3 ^ i := by positivity
    omega

/-- A repeated even index forces every smaller index in the representation to be even. -/
private theorem noOddBelowDouble {m : Multiset ℕ} (hm : Preferred m) {i j : ℕ}
    (hi : Even i) (h : 2 ≤ count i m) (hj : j ∈ m) (ho : Odd j) (hji : j ≤ i) : False := by
  have hne : j ≠ i := fun e => (Nat.not_even_iff_odd.mpr ho) (e ▸ hi)
  have hi' : 2 ≤ i := hm.1.1.1 i (Multiset.count_pos.mp (by omega))
  have hj' := hm.1.1.1 j hj
  have hj3 : 3 ≤ j := by
    rcases ho with ⟨k, hk⟩
    omega
  have hprev : Even (j - 1) := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp (by
    rw [show j - 1 + 1 = j by omega]
    exact ho))
  have hstep := (step i).1 hi
  have hstep' := (step (j - 1)).1 hprev
  rw [show j - 1 + 1 = j by omega] at hstep'
  apply noReplacement hm (extraCoin h hj hne) (t := ({i + 1} + replicate 2 (j - 1)))
  · simp only [mem_add, mem_singleton, mem_replicate]
    intro a ha
    rcases ha with rfl | ⟨_, rfl⟩ <;> omega
  · simp only [valueAdd, valueOne, valueRep]
    omega
  · simp
  · simp only [scoreAdd, scoreOne, scoreRep, pow_succ]
    have hp : 3 ^ j ≤ 3 ^ i := Nat.pow_le_pow_right (by decide) hji
    have hp' : 0 < 3 ^ (j - 1) := by positivity
    omega

/-- Four even-indexed coins and a fifth coin at a smaller or equal even index can be exchanged. -/
private theorem noFourthWithEven {m : Multiset ℕ} (hm : Preferred m) {i j : ℕ}
    (hi : Even i) (hj : Even j) (hji : j ≤ i)
    (hs : replicate 4 i + {j} ≤ m) : False := by
  have hi' : 2 ≤ i := hm.1.1.1 i (Multiset.mem_of_le hs (by simp))
  have hj' : 2 ≤ j := hm.1.1.1 j (Multiset.mem_of_le hs (by simp))
  have hstep := evenTwo i hi
  have hp : 3 ^ j ≤ 3 ^ i := Nat.pow_le_pow_right (by decide) hji
  have hp' : 0 < 3 ^ i := by positivity
  by_cases h2 : j = 2
  · subst j
    apply noReplacement hm hs (t := {i + 2})
    · simp only [mem_singleton]
      rintro _ rfl
      omega
    · simp only [valueAdd, valueOne, valueRep]
      change jac (i + 2) = 4 * jac i + 1
      exact hstep
    · simp
    · simp only [scoreAdd, scoreOne, scoreRep, pow_add]
      change 4 * 3 ^ i + 3 ^ 2 < 3 ^ i * 9
      omega
  · have hj4 : 4 ≤ j := by
      rcases hj with ⟨k, hk⟩
      omega
    have he : Even (j - 2) := by
      rcases hj with ⟨k, hk⟩
      exact ⟨k - 1, by omega⟩
    have hprev := evenTwo (j - 2) he
    rw [show j - 2 + 2 = j by omega] at hprev
    apply noReplacement hm hs (t := ({i + 2} + replicate 4 (j - 2)))
    · simp only [mem_add, mem_singleton, mem_replicate]
      intro a ha
      rcases ha with rfl | ⟨_, rfl⟩ <;> omega
    · simp only [valueAdd, valueOne, valueRep]
      omega
    · simp
    · simp only [scoreAdd, scoreOne, scoreRep, pow_add]
      change 4 * 3 ^ i + 3 ^ j < 3 ^ i * 9 + 4 * 3 ^ (j - 2)
      omega

private theorem filterMember {m : Multiset ℕ} {i j : ℕ} (hj : j ∈ m.filter (· ≠ i)) :
    j ∈ m ∧ j ≠ i := Multiset.mem_filter.mp hj

private theorem filterPreferred {m : Multiset ℕ} (hm : Preferred m) (i : ℕ) :
    Preferred (m.filter (· ≠ i)) := preferredPart hm (Multiset.filter_le _ _)

private theorem valueSplit (m : Multiset ℕ) (i : ℕ) :
    value m = count i m * jac i + value (m.filter (· ≠ i)) := by
  conv_lhs => rw [← splitAt m i]
  simp only [valueAdd, valueRep]

/-- With only even indices, three copies at the top leave a remainder below the top coin.
Four copies must exhaust the representation. -/
private theorem evenBound (i : ℕ) (hi : Even i) (hi2 : 2 ≤ i)
    (m : Multiset ℕ) (hm : Preferred m) (hb : ∀ j ∈ m, Even j ∧ j ≤ i) :
    value m < jac (i + 2) := by
  induction i using Nat.strong_induction_on generalizing m with
  | h i ih =>
    have htop := evenTwo i hi
    by_cases hc : 4 ≤ count i m
    · obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp (enoughCopies hc)
      by_cases hz : u = 0
      · rw [hu, hz, add_zero, valueRep, htop]
        omega
      · obtain ⟨j, hj⟩ := Multiset.exists_mem_of_ne_zero hz
        have hs : replicate 4 i + {j} ≤ m := by
          rw [hu]
          exact Multiset.add_le_add_left (Multiset.singleton_le.mpr hj)
        have hjm : j ∈ m := Multiset.mem_of_le hs (by simp)
        exact (noFourthWithEven hm hi (hb j hjm).1 (hb j hjm).2 hs).elim
    · have ht : value (m.filter (· ≠ i)) < jac i := by
        by_cases hi4 : 4 ≤ i
        · have hp : Even (i - 2) := by
            rcases hi with ⟨k, hk⟩
            exact ⟨k - 1, by omega⟩
          have hl (j : ℕ) (hj : j ∈ m.filter (· ≠ i)) : Even j ∧ j ≤ i - 2 := by
            obtain ⟨hjm, hne⟩ := filterMember hj
            obtain ⟨hej, hji⟩ := hb j hjm
            refine ⟨hej, ?_⟩
            rcases hej with ⟨a, ha⟩
            rcases hi with ⟨b, hb'⟩
            omega
          have h := ih (i - 2) (by omega) hp (by omega) _ (filterPreferred hm i) hl
          rwa [show i - 2 + 2 = i by omega] at h
        · have hz : m.filter (· ≠ i) = 0 := by
            apply Multiset.eq_zero_of_forall_notMem
            intro j hj
            obtain ⟨hjm, hne⟩ := filterMember hj
            obtain ⟨hej, hji⟩ := hb j hjm
            have hj2 := hm.1.1.1 j hjm
            rcases hej with ⟨a, ha⟩
            rcases hi with ⟨b, hb'⟩
            omega
          have h : i = 2 := by
            rcases hi with ⟨b, hb'⟩
            omega
          rw [hz, h]
          decide
      have hprod : count i m * jac i ≤ 3 * jac i :=
        Nat.mul_le_mul_right _ (by omega)
      rw [valueSplit m i, htop]
      omega

/-- A preferred representation capped at index i has value below the coin at i + 2. -/
private theorem allBound (i : ℕ) (hi2 : 2 ≤ i)
    (m : Multiset ℕ) (hm : Preferred m) (hb : ∀ j ∈ m, j ≤ i) :
    value m < jac (i + 2) := by
  induction i using Nat.strong_induction_on generalizing m with
  | h i ih =>
    by_cases hc : 2 ≤ count i m
    · by_cases hi : Even i
      · apply evenBound i hi hi2 m hm
        intro j hj
        refine ⟨?_, hb j hj⟩
        by_contra h
        exact noOddBelowDouble hm hi hc hj (Nat.not_even_iff_odd.mp h) (hb j hj)
      · exact (noOddDouble hm (Nat.not_even_iff_odd.mp hi) hc).elim
    · have ht : value (m.filter (· ≠ i)) < jac (i + 1) := by
        by_cases hi3 : 3 ≤ i
        · have h := ih (i - 1) (by omega) (by omega) _ (filterPreferred hm i)
              (fun j hj => by
                obtain ⟨hjm, hne⟩ := filterMember hj
                have hle := hb j hjm
                omega)
          rwa [show i - 1 + 2 = i + 1 by omega] at h
        · have hz : m.filter (· ≠ i) = 0 := by
            apply Multiset.eq_zero_of_forall_notMem
            intro j hj
            obtain ⟨hjm, hne⟩ := filterMember hj
            have hj2 := hm.1.1.1 j hjm
            have hle := hb j hjm
            omega
          rw [hz, show i = 2 by omega]
          decide
      have hprod : count i m * jac i ≤ jac i := by
        simpa using Nat.mul_le_mul_right (jac i) (show count i m ≤ 1 by omega)
      rw [valueSplit m i, jac]
      omega

private theorem powLink (i : ℕ) :
    (Even i → 3 * jac i + 1 = 2 ^ i) ∧
    (Odd i → 3 * jac i = 2 ^ i + 1) := by
  induction i with
  | zero => simp [jac]
  | succ i ih =>
    constructor
    · intro he
      have ho : Odd i := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he)
      have h := ih.2 ho
      have hs := (step i).2 ho
      rw [pow_succ]
      omega
    · intro ho
      have he : Even i := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp ho)
      have h := ih.1 he
      rw [(step i).1 he, pow_succ]
      omega

private theorem coinLeValue {m : Multiset ℕ} {j : ℕ} (hj : j ∈ m) :
    jac j ≤ value m := by
  obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp (Multiset.singleton_le.mpr hj)
  rw [hu, valueAdd, valueOne]
  omega

private theorem preferredExists (n : ℕ) :
    ∃ m : Multiset ℕ, value m = n ∧ Preferred m := by
  classical
  let R (c : ℕ) := ∃ m : Multiset ℕ, represents n m ∧ m.card = c
  have hR : ∃ c, R c := by
    refine ⟨n, replicate n 2, ⟨?_, ?_⟩, by simp⟩
    · intro j hj
      have hj' := (mem_replicate.mp hj).2
      omega
    · simp only [valueRep]
      change n * 1 = n
      simp
  let c := Nat.find hR
  let P (s : ℕ) := ∃ m : Multiset ℕ, represents n m ∧ m.card = c ∧ score m = s
  have scoreBound (t : Multiset ℕ) (ht : represents n t) (hc : t.card = c) :
      score t ≤ c * 3 ^ (n + 1) := by
    have h := Multiset.sum_le_card_nsmul
      (s := t.map fun i => 3 ^ i) (n := 3 ^ (n + 1)) (by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hx
        have hval := coinLeValue hj
        have hlow := jacLower j (ht.1 j hj)
        rw [ht.2] at hval
        exact Nat.pow_le_pow_right (by decide) (by omega))
    simpa [score, hc, nsmul_eq_mul] using h
  obtain ⟨m, hm, hmc⟩ := Nat.find_spec hR
  have hp : P (score m) := ⟨m, hm, hmc, rfl⟩
  obtain ⟨t, ht, htc, hts⟩ := Nat.findGreatest_spec (scoreBound m hm hmc) hp
  refine ⟨t, ht.2, ?_⟩
  rw [show Preferred t ↔ optimal (value t) t ∧
      ∀ u, represents (value t) u → u.card = t.card → score u ≤ score t from Iff.rfl, ht.2]
  refine ⟨⟨ht, ?_⟩, ?_⟩
  · intro u hu
    rw [htc]
    exact Nat.find_min' hR (show R u.card from ⟨u, hu, rfl⟩)
  · intro u hu huc
    have huc' : u.card = c := huc.trans htc
    rw [hts]
    exact Nat.le_findGreatest (scoreBound u hu huc') (show P (score u) from ⟨u, hu, huc', rfl⟩)

theorem existsOptimal (n : ℕ) (hn : 0 < n) :
    ∃ m : Multiset ℕ, optimal n m ∧
      (greedyIndex n ∈ m ∨ greedyIndex n - 1 ∈ m) := by
  obtain ⟨m, hv, hm⟩ := preferredExists n
  have hopt := hm.1
  rw [hv] at hopt
  refine ⟨m, hopt, ?_⟩
  let k := greedyIndex n
  change k ∈ m ∨ k - 1 ∈ m
  have hlog : ∀ j : ℕ, j ≤ k ↔ 2 ^ j ≤ 3 * n + 1 :=
    fun j => Nat.le_log_iff_pow_le (by decide) (by omega)
  have hhigh : jac k ≤ n := by
    have hp := (hlog k).mp le_rfl
    by_cases he : Even k
    · have h := (powLink k).1 he
      omega
    · have h := (powLink k).2 (Nat.not_even_iff_odd.mp he)
      omega
  by_contra hbad
  push Not at hbad
  have hlt (j : ℕ) (hj : j ∈ m) : j ≤ k - 2 := by
    have hval := coinLeValue hj
    rw [hv] at hval
    have hpow : 2 ^ j ≤ 3 * jac j + 1 := by
      by_cases he : Even j
      · have h := (powLink j).1 he
        omega
      · have h := (powLink j).2 (Nat.not_even_iff_odd.mp he)
        omega
    have hle := (hlog j).mpr (by omega)
    have hne : j ≠ k := fun e => hbad.1 (e ▸ hj)
    have hne' : j ≠ k - 1 := fun e => hbad.2 (e ▸ hj)
    omega
  have hm0 : m ≠ 0 := by
    intro he
    rw [he] at hv
    change 0 = n at hv
    omega
  obtain ⟨j, hj⟩ := Multiset.exists_mem_of_ne_zero hm0
  have hj2 := hm.1.1.1 j hj
  have hjk := hlt j hj
  have h2 : 2 ≤ k - 2 := by omega
  have hb := allBound (k - 2) h2 m hm hlt
  rw [show k - 2 + 2 = k by omega, hv] at hb
  omega

end JacobsthalCoins

theorem OMA.solution : type_of% @OMA.S_oeis_a372556.main := by
  constructor
  · refine ⟨⟨by simp, by simp [OMA.S_oeis_a372556.value]⟩, ?_⟩
    intro r _
    simp
  · exact JacobsthalCoins.existsOptimal
