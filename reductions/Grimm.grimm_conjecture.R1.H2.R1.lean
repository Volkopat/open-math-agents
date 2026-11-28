import OMAReductions.R_Grimm_grimm_conjecture_R1
import Mathlib

-- Reduction Grimm.grimm_conjecture.R1.H2.R1 of step Grimm.grimm_conjecture.R1.H2
-- Credit: @rickmanelius

/-!
# Grimm's conjecture for runs of at least four composites: only the smooth members matter

Write `P(T)` for the set of primes dividing some member of a set `T` of members of the run
`n, ..., n + k - 1`. By Hall's marriage theorem, Grimm's conclusion for the run is the statement
that `|P(T)| ≥ |T|` for every `T`. This file proves, for every run of composites:

* A common divisor of two members is less than `k`. So a prime `p ≥ k` divides at most one member,
  and the members with such a prime factor bring their own primes, distinct from each other and
  from every prime below `k`. Only the `k`-smooth members (every prime factor below `k`) remain.
* If `|P(T)| < |T|`, pick for each prime of `P(T)` a member of `T` with the highest power of it.
  Some member `m` of `T` is picked for no prime, so each prime power exactly dividing `m` also
  divides another member and is below `k`. Hence `m` divides `lcm(1, ..., k - 1)` and
  `m ≤ (k - 1) ^ (|T| - 1)`. So `T` can fail only if `n ≤ lcm(1, ..., k - 1)` and
  `n ≤ (k - 1) ^ (|T| - 1)` (the classical maximizer argument). In particular Grimm's conjecture
  holds for every run with `n > lcm(1, ..., k - 1)`.

What is left is Hall's condition for sets of `k`-smooth members under those two bounds.
`H1` is the case of runs of at most 13 composites. It is a finite statement: a failing set
contains a member dividing `lcm(1, ..., 12) = 27720`, and a case check over the 96 divisors of
`27720` settles it. `H2`, runs of at least 14 composites, is the open part.
-/

namespace OMA.R_Grimm_grimm_conjecture_R1_H2_R1

/-- Hall's condition for the `k`-smooth members of a run of at most 13 composites, for the sets
that the elementary bounds leave open (a finite statement: `n ≤ 27720`). -/
def H1 : Prop :=
  ∀ n k : ℕ, 1 ≤ n → 4 ≤ k → k ≤ 13 → n ≤ (Finset.Ico 1 k).lcm id →
    (∀ i : Fin k, (n + i).Composite) →
    ∀ T : Finset (Fin k), (∀ i ∈ T, ∀ p : ℕ, p.Prime → p ∣ n + i → p < k) →
      n ≤ (k - 1) ^ (T.card - 1) →
      T.card ≤ (T.biUnion fun i => (n + i).primeFactors).card

/-- Hall's condition for the `k`-smooth members of a run of at least 14 composites, for the sets
that the elementary bounds leave open. -/
def H2 : Prop :=
  ∀ n k : ℕ, 1 ≤ n → 14 ≤ k → n ≤ (Finset.Ico 1 k).lcm id →
    (∀ i : Fin k, (n + i).Composite) →
    ∀ T : Finset (Fin k), (∀ i ∈ T, ∀ p : ℕ, p.Prime → p ∣ n + i → p < k) →
      n ≤ (k - 1) ^ (T.card - 1) →
      T.card ≤ (T.biUnion fun i => (n + i).primeFactors).card

/-- A common divisor of two different members of a run of length `k` is less than `k`. -/
lemma lt_of_dvd_of_dvd {n k d : ℕ} {i j : Fin k} (hij : i ≠ j) (hi : d ∣ n + i)
    (hj : d ∣ n + j) : d < k := by
  have h1 : d ∣ (n + (j : ℕ)) - (n + i) := Nat.dvd_sub hj hi
  have h2 : d ∣ (n + (i : ℕ)) - (n + j) := Nat.dvd_sub hi hj
  have hi' := i.isLt
  have hj' := j.isLt
  have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hpos : 0 < (n + (j : ℕ)) - (n + i) := by omega
    have := Nat.le_of_dvd hpos h1
    omega
  · have hpos : 0 < (n + (i : ℕ)) - (n + j) := by omega
    have := Nat.le_of_dvd hpos h2
    omega

/-- Hall's condition for every set of members follows from Hall's condition for the smooth ones:
members with a prime factor at least `k` each bring their own such primes. -/
lemma hall_of_smooth (n k : ℕ)
    (hcomp : ∀ i : Fin k, (n + i).Composite)
    (hs : ∀ T : Finset (Fin k), (∀ i ∈ T, ∀ p : ℕ, p.Prime → p ∣ n + i → p < k) →
      T.card ≤ (T.biUnion fun i => (n + i).primeFactors).card)
    (T : Finset (Fin k)) : T.card ≤ (T.biUnion fun i => (n + i).primeFactors).card := by
  classical
  let S : Fin k → Prop := fun i => ∀ p : ℕ, p.Prime → p ∣ n + i → p < k
  let Ts := T.filter S
  let Tr := T.filter (fun i => ¬ S i)
  let big : Fin k → Finset ℕ := fun i => (n + (i : ℕ)).primeFactors.filter (fun p => k ≤ p)
  have hTs : Ts.card ≤ (Ts.biUnion fun i => (n + i).primeFactors).card :=
    hs Ts (fun i hi => (Finset.mem_filter.mp hi).2)
  have hTr : Tr.card ≤ (Tr.biUnion big).card := by
    apply Finset.card_le_card_biUnion
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro p hpi hpj
      simp only [big, Finset.mem_filter, Nat.mem_primeFactors] at hpi hpj
      have := lt_of_dvd_of_dvd hij hpi.1.2.1 hpj.1.2.1
      omega
    · intro i hi
      have hnot := (Finset.mem_filter.mp hi).2
      simp only [S, not_forall, not_lt] at hnot
      obtain ⟨p, hp, hpd, hpk⟩ := hnot
      refine ⟨p, ?_⟩
      simp only [big, Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp, hpd, by have := (hcomp i).1; omega⟩, hpk⟩
  have hdisj : Disjoint (Ts.biUnion fun i => (n + i).primeFactors) (Tr.biUnion big) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_biUnion] at hp1 hp2
    obtain ⟨i, hi, hpi⟩ := hp1
    obtain ⟨j, _, hpj⟩ := hp2
    have hSi := (Finset.mem_filter.mp hi).2
    rw [Nat.mem_primeFactors] at hpi
    simp only [big, Finset.mem_filter] at hpj
    have := hSi p hpi.1 hpi.2.1
    omega
  have hsub : (Ts.biUnion fun i => (n + i).primeFactors) ∪ (Tr.biUnion big) ⊆
      T.biUnion fun i => (n + i).primeFactors := by
    intro p hp
    rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion] at hp
    rw [Finset.mem_biUnion]
    rcases hp with ⟨i, hi, hpi⟩ | ⟨i, hi, hpi⟩
    · exact ⟨i, (Finset.mem_filter.mp hi).1, hpi⟩
    · exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hpi).1⟩
  have hcard : Ts.card + Tr.card = T.card := Finset.card_filter_add_card_filter_not S
  calc T.card = Ts.card + Tr.card := hcard.symm
    _ ≤ (Ts.biUnion fun i => (n + i).primeFactors).card + (Tr.biUnion big).card :=
        Nat.add_le_add hTs hTr
    _ = ((Ts.biUnion fun i => (n + i).primeFactors) ∪ (Tr.biUnion big)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (T.biUnion fun i => (n + i).primeFactors).card := Finset.card_le_card hsub

/-- If a set `T` of members has fewer distinct prime factors than members, one of its members is
not the member of `T` with the highest power of any prime: every prime power exactly dividing it
also divides another member, so it is below `k`. -/
lemma exists_member_small_powers {n k : ℕ} (hn : ∀ i : Fin k, n + (i : ℕ) ≠ 0)
    (T : Finset (Fin k)) (hT : (T.biUnion fun i => (n + (i : ℕ)).primeFactors).card < T.card) :
    ∃ m ∈ T, ∀ p ∈ (n + (m : ℕ)).primeFactors, p ^ ((n + (m : ℕ)).factorization p) < k := by
  classical
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h | h
    · simp [h] at hT
    · exact h
  have hmax : ∀ p : ℕ, ∃ j ∈ T, ∀ j' ∈ T,
      (n + (j' : ℕ)).factorization p ≤ (n + (j : ℕ)).factorization p :=
    fun p => Finset.exists_max_image T (fun j => (n + (j : ℕ)).factorization p) hTne
  choose g _ hg using hmax
  have himg : ((T.biUnion fun i => (n + (i : ℕ)).primeFactors).image g).card < T.card :=
    lt_of_le_of_lt Finset.card_image_le hT
  have hex : ∃ m ∈ T, m ∉ (T.biUnion fun i => (n + (i : ℕ)).primeFactors).image g := by
    by_contra h
    have hsub : T ⊆ (T.biUnion fun i => (n + (i : ℕ)).primeFactors).image g := by
      intro m hm
      by_contra hm'
      exact h ⟨m, hm, hm'⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨m, hmT, hmg⟩ := hex
  refine ⟨m, hmT, fun p hp => ?_⟩
  have hpP : p ∈ T.biUnion fun i => (n + (i : ℕ)).primeFactors :=
    Finset.mem_biUnion.mpr ⟨m, hmT, hp⟩
  have hne : m ≠ g p := fun h => hmg (Finset.mem_image.mpr ⟨p, hpP, h.symm⟩)
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hd1 : p ^ ((n + (m : ℕ)).factorization p) ∣ n + (m : ℕ) := Nat.ordProj_dvd _ _
  have hd2 : p ^ ((n + (m : ℕ)).factorization p) ∣ n + (g p : ℕ) :=
    (hpp.pow_dvd_iff_le_factorization (hn (g p))).mpr (hg p m hmT)
  exact lt_of_dvd_of_dvd hne hd1 hd2

lemma lcm_Ico_ne_zero (k : ℕ) : (Finset.Ico 1 k).lcm id ≠ 0 := by
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

/-- A number all of whose prime powers are below `k` divides `lcm(1, ..., k - 1)`. -/
lemma dvd_lcm_of_small_powers {x k : ℕ} (hx : x ≠ 0)
    (h : ∀ p ∈ x.primeFactors, p ^ (x.factorization p) < k) : x ∣ (Finset.Ico 1 k).lcm id := by
  have hL := lcm_Ico_ne_zero k
  rw [← Nat.factorization_le_iff_dvd hx hL, Finsupp.le_def]
  intro p
  by_cases hp : p ∈ x.primeFactors
  · have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hmem : p ^ (x.factorization p) ∈ Finset.Ico 1 k := by
      rw [Finset.mem_Ico]
      exact ⟨Nat.one_le_pow _ _ hpp.pos, h p hp⟩
    have hdvd : p ^ (x.factorization p) ∣ (Finset.Ico 1 k).lcm id := Finset.dvd_lcm hmem
    exact (hpp.pow_dvd_iff_le_factorization hL).mp hdvd
  · rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hp
    rw [hp]
    exact Nat.zero_le _

/-- A number all of whose prime powers are below `k` is at most `(k - 1) ^ ω`. -/
lemma le_pow_of_small_powers {x k : ℕ} (hx : x ≠ 0)
    (h : ∀ p ∈ x.primeFactors, p ^ (x.factorization p) < k) :
    x ≤ (k - 1) ^ x.primeFactors.card := by
  calc x = ∏ p ∈ x.primeFactors, p ^ x.factorization p := Nat.prod_primeFactors_pow_factorization hx
    _ ≤ (k - 1) ^ x.primeFactors.card := by
      apply Finset.prod_le_pow_card
      intro p hp
      have := h p hp
      omega

theorem main : H1 → H2 → OMA.R_Grimm_grimm_conjecture_R1.H2 := by
  intro h1 h2 n k hn hk hcomp
  classical
  have hn0 : ∀ i : Fin k, n + (i : ℕ) ≠ 0 := fun i => by have := (hcomp i).1; omega
  -- Hall's condition for the smooth members: a failing set obeys both bounds, then H1 or H2.
  have hs : ∀ T : Finset (Fin k), (∀ i ∈ T, ∀ p : ℕ, p.Prime → p ∣ n + i → p < k) →
      T.card ≤ (T.biUnion fun i => (n + i).primeFactors).card := by
    intro T hT
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨m, hmT, hsmall⟩ := exists_member_small_powers hn0 T hlt
    have hL : n ≤ (Finset.Ico 1 k).lcm id := by
      have hd := dvd_lcm_of_small_powers (hn0 m) hsmall
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero (lcm_Ico_ne_zero k)) hd
      omega
    have hP : n ≤ (k - 1) ^ (T.card - 1) := by
      have h3 := le_pow_of_small_powers (hn0 m) hsmall
      have hsub : (n + (m : ℕ)).primeFactors ⊆ T.biUnion fun i => (n + (i : ℕ)).primeFactors :=
        Finset.subset_biUnion_of_mem (fun i : Fin k => (n + (i : ℕ)).primeFactors) hmT
      have h4 := Finset.card_le_card hsub
      have h5 : (k - 1) ^ (n + (m : ℕ)).primeFactors.card ≤ (k - 1) ^ (T.card - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rcases Nat.lt_or_ge k 14 with h | h
    · have := h1 n k hn hk (by omega) hL hcomp T hT hP
      omega
    · have := h2 n k hn h hL hcomp T hT hP
      omega
  -- Hall's marriage theorem on all members turns the condition into the injective choice.
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun i : Fin k => (n + (i : ℕ)).primeFactors)).mp (hall_of_smooth n k hcomp hs)
  refine ⟨⟨f, hf⟩, fun i => ?_⟩
  have h := hmem i
  rw [Nat.mem_primeFactors] at h
  exact ⟨h.1, h.2.1⟩

end OMA.R_Grimm_grimm_conjecture_R1_H2_R1
