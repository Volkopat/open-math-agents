import FormalConjectures.ErdosProblems.«1074»

/-! The six Pillai primes below 72 exhaust the image of the first six indices. -/

-- Problem: Erdős Problem 1074 — PillaiPrimes init
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1074.lean:128 (declaration Erdos1074.erdos_1074.variants.PillaiPrimes_init)
-- Credit: @Slayzkami (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E1074P

open Nat Erdos1074

def primes : Finset ℕ := {23, 29, 59, 61, 67, 71}

lemma charac (n : ℕ) : n ∈ PillaiPrimes ↔
    (n.Prime ∧ ∃ m < n, 1 ≤ m ∧ ¬ n % m = 1 % m ∧ n ∣ m ! + 1) := by
  constructor
  · rintro ⟨hp, m, hm, hne, hd⟩
    refine ⟨hp, m, ?_, hm, hne, hd⟩
    by_contra hmn
    push Not at hmn
    have h1 : n ∣ m ! := Nat.dvd_factorial hp.pos hmn
    have h2 : n ∣ 1 := (Nat.dvd_add_right h1).1 hd
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  · rintro ⟨hp, m, -, hm, hne, hd⟩
    exact ⟨hp, m, hm, hne, hd⟩

set_option maxRecDepth 100000 in
lemma table : ∀ n < 72, (n.Prime ∧ ∃ m < n, 1 ≤ m ∧ ¬ n % m = 1 % m ∧ n ∣ m ! + 1) ↔
    n ∈ primes := by
  decide

lemma mem_iff (n : ℕ) (hn : n < 72) : n ∈ PillaiPrimes ↔ n ∈ primes :=
  (charac n).trans (table n hn)

def P : ℕ → Prop := fun n => n ∈ PillaiPrimes

lemma count72 [DecidablePred P] : count P 72 = 6 := by
  rw [Nat.count_eq_card_filter_range,
    Finset.filter_congr (p := P) (fun n hn => mem_iff n (Finset.mem_range.mp hn))]
  decide

end OMA.E1074P

open OMA.E1074P in
theorem OMA.solution : type_of% @Erdos1074.erdos_1074.variants.PillaiPrimes_init := by
  classical
  let indices := Finset.Icc (0 : ℕ) 5
  have included : primes ⊆ indices.image (Nat.nth P) := by
    intro p hp
    have small : ∀ p ∈ primes, p < 72 := by decide
    have hsmall := small p hp
    have hpillai : P p := (mem_iff p hsmall).mpr hp
    have hindex := Nat.count_strict_mono hpillai hsmall
    rw [count72] at hindex
    exact Finset.mem_image.mpr ⟨Nat.count P p, Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩,
      Nat.nth_count hpillai⟩
  have imageEq : indices.image (Nat.nth P) = primes :=
    (Finset.eq_of_subset_of_card_le included (Finset.card_image_le.trans (by decide))).symm
  have hset : Nat.nth P '' Set.Icc 0 5 = (↑primes : Set ℕ) := by
    rw [← Finset.coe_Icc, ← Finset.coe_image, imageEq]
  change Nat.nth P '' Set.Icc 0 5 = _
  simpa only [primes, Finset.coe_insert, Finset.coe_singleton] using hset
