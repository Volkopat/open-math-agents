import OMAStatements.S_oeis_a342909

-- Problem: A342909: a(1)=1. Thereafter, if a(n) is a novel term a(n+1) = number of prior terms > a(n); otherwise a(n+1) = number of prior terms <= a(n).
-- Upstream: formal-conjectures statements/oeis-a342909.lean:0 (declaration OMA.S_oeis_a342909.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: a(n+1) = nextVal a n, a count over the n - 1 prior terms, so a(n+1) < n. If the terms
-- were bounded by B, some value v would occur more than B + 1 times among a(1), ...,
-- a((B+1)^2 + 1); at its last occurrence n the term is not novel, so a(n+1) counts all earlier
-- occurrences of v and exceeds B. Hence the sequence is unbounded, so for every N there is a
-- first term a(m) above max(a(1), ..., a(N)); it is a strict record, hence novel with no prior
-- term above it, and a(m+1) = 0 with m + 1 > N.

namespace H11A342909

open OMA.S_oeis_a342909

theorem a_succ (n : ℕ) : a (n + 1) = G n (n + 1) := by
  unfold a
  rw [Nat.add_sub_cancel]

theorem G_stable (k : ℕ) : ∀ i, 1 ≤ i → i ≤ k + 1 → G k i = a i := by
  induction k with
  | zero =>
    intro i h1 h2
    obtain rfl : i = 1 := by omega
    rfl
  | succ k ih =>
    intro i h1 h2
    rcases Nat.lt_or_ge i (k + 2) with h | h
    · show Function.update (G k) (k + 2) (nextVal (G k) (k + 1)) i = a i
      rw [Function.update_of_ne (by omega : i ≠ k + 2)]
      exact ih i h1 (by omega)
    · obtain rfl : i = k + 2 := by omega
      exact (a_succ (k + 1)).symm

theorem nextVal_congr (g h : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hgh : ∀ i, 1 ≤ i → i ≤ n → g i = h i) : nextVal g n = nextVal h n := by
  have e : ∀ i ∈ Finset.Ico 1 n, g i = h i := fun i hi => by
    rw [Finset.mem_Ico] at hi
    exact hgh i hi.1 hi.2.le
  have en : g n = h n := hgh n hn le_rfl
  have f0 : (Finset.Ico 1 n).filter (fun i => g i = g n) =
      (Finset.Ico 1 n).filter (fun i => h i = h n) :=
    Finset.filter_congr (fun i hi => by rw [en, e i hi])
  have f1 : (Finset.Ico 1 n).filter (fun i => g n < g i) =
      (Finset.Ico 1 n).filter (fun i => h n < h i) :=
    Finset.filter_congr (fun i hi => by rw [en, e i hi])
  have f2 : (Finset.Ico 1 n).filter (fun i => g i ≤ g n) =
      (Finset.Ico 1 n).filter (fun i => h i ≤ h n) :=
    Finset.filter_congr (fun i hi => by rw [en, e i hi])
  unfold nextVal
  rw [f0, f1, f2]

theorem a_rec (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = nextVal a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]
  show Function.update (G m) (m + 2) (nextVal (G m) (m + 1)) (m + 1 + 1) = nextVal a (m + 1)
  rw [show m + 1 + 1 = m + 2 by omega, Function.update_self]
  exact nextVal_congr (G m) a (m + 1) hn (fun i h1 h2 => G_stable m i h1 h2)

theorem card_lt (n : ℕ) (hn : 1 ≤ n) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.Ico 1 n).filter p).card < n := by
  have h1 := Finset.card_filter_le (Finset.Ico 1 n) p
  rw [Nat.card_Ico] at h1
  omega

theorem nextVal_lt (g : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) : nextVal g n < n := by
  unfold nextVal
  by_cases H : ((Finset.Ico 1 n).filter (fun i => g i = g n)).card = 0
  · rw [if_pos H]
    exact card_lt n hn _
  · rw [if_neg H]
    exact card_lt n hn _

theorem record_zero (n : ℕ) (hn : 1 ≤ n) (hrec : ∀ i ∈ Finset.Ico 1 n, a i < a n) :
    a (n + 1) = 0 := by
  have hnov : ((Finset.Ico 1 n).filter (fun i => a i = a n)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    exact (hrec i hi).ne
  rw [a_rec n hn]
  unfold nextVal
  rw [if_pos hnov, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  exact not_lt.mpr (hrec i hi).le

theorem big_step (B v : ℕ) (hb : ∀ m, 1 ≤ m → a m ≤ B) (S : Finset ℕ)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ a x = v) (hc : B + 1 < S.card) : False := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨n, hnS, hmax⟩ : ∃ n ∈ S, ∀ x ∈ S, x ≤ n :=
    ⟨S.max' hne, S.max'_mem hne, fun x hx => S.le_max' x hx⟩
  obtain ⟨hn1, hnv⟩ := hS n hnS
  have hsub : S.erase n ⊆ (Finset.Ico 1 n).filter (fun i => a i ≤ a n) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hx1, hxv⟩ := hS x hx.2
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hx1, lt_of_le_of_ne (hmax x hx.2) hx.1⟩, (hxv.trans hnv.symm).le⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hnS] at hcard
  have hnot : ((Finset.Ico 1 n).filter (fun i => a i = a n)).card ≠ 0 := by
    obtain ⟨x, hx⟩ : (S.erase n).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hnS]; omega)
    have hx' := hsub hx
    rw [Finset.mem_filter] at hx'
    rw [Finset.mem_erase] at hx
    obtain ⟨_, hxv⟩ := hS x hx.2
    exact Finset.card_ne_zero.mpr ⟨x, Finset.mem_filter.mpr ⟨hx'.1, hxv.trans hnv.symm⟩⟩
  have h1 : a (n + 1) = ((Finset.Ico 1 n).filter (fun i => a i ≤ a n)).card := by
    rw [a_rec n hn1]
    unfold nextVal
    rw [if_neg hnot]
  have h2 := hb (n + 1) (by omega)
  omega

theorem unbounded (B : ℕ) : ∃ m, 1 ≤ m ∧ B < a m := by
  by_contra hcon
  have hb : ∀ m, 1 ≤ m → a m ≤ B := fun m hm => by
    by_contra h
    exact hcon ⟨m, hm, by omega⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (B + 1) * (B + 1) := ⟨_, rfl⟩
  have hmaps : ∀ i ∈ Finset.Icc 1 (Q + 1), a i ∈ Finset.range (B + 1) := fun i hi => by
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_range]
    have := hb i hi.1
    omega
  have hlt : (Finset.range (B + 1)).card * (B + 1) < (Finset.Icc 1 (Q + 1)).card := by
    rw [Finset.card_range, Nat.card_Icc, ← hQ]
    omega
  obtain ⟨v, _, hcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  exact big_step B v hb _ (fun x hx => by
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    exact ⟨hx.1.1, hx.2⟩) hcard

theorem zero_after (N : ℕ) : ∃ n, N < n ∧ a n = 0 := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ i ∈ Finset.Icc 1 N, a i ≤ B :=
    ⟨(Finset.Icc 1 N).sup a, fun i hi => Finset.le_sup hi⟩
  have hex : ∃ m, 1 ≤ m ∧ B < a m := unbounded B
  obtain ⟨m, ⟨hm1, hm2⟩, hmin⟩ : ∃ m, (1 ≤ m ∧ B < a m) ∧ ∀ j, j < m → ¬ (1 ≤ j ∧ B < a j) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hNm : N < m := by
    by_contra h
    have := hB m (Finset.mem_Icc.mpr ⟨hm1, by omega⟩)
    omega
  have hrec : ∀ i ∈ Finset.Ico 1 m, a i < a m := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have h2 : a i ≤ B := by
      by_contra h
      exact hmin i hi.2 ⟨hi.1, by omega⟩
    omega
  exact ⟨m + 1, by omega, record_zero m hm1 hrec⟩

end H11A342909

open OMA.S_oeis_a342909 H11A342909 in
theorem OMA.solution : type_of% @OMA.S_oeis_a342909.main := by
  refine ⟨fun n hn => ?_, zero_after⟩
  rw [a_rec n hn]
  exact nextVal_lt a n hn
