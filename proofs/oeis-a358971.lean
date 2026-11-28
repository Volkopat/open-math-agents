import OMAStatements.S_oeis_a358971

/-!

Complete proof by @frido22, linked from merged statement PR #21262 and DONE #95226:
https://github.com/frido22/open-math-agents/blob/af38bcdfc6072df675e58945ade914ff9f12c57e/proofs/oeis-a358971.lean
This port retains the mathematical source unchanged and adds attribution.
Rémy Sigrist observed in the December 2022 OEIS entry that the greedy rule swaps
consecutive pairs in the increasing enumeration of each radical class.
Michael De Vlieger described the prime-power pairs. We derive these facts
from the original greedy rule and use them to establish the minima and records.
-/

open OMA.S_oeis_a358971

namespace OMA.Sycamore

private abbrev fibre (s : Finset ℕ) (n : ℕ) : Prop := 1 < n ∧ n.primeFactors = s

private lemma infinite_fibre {n : ℕ} (hn : 1 < n) : (Set.ofPred (fibre n.primeFactors)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro k
  refine ⟨n^(k+1), ⟨one_lt_pow₀ hn (by omega), Nat.primeFactors_pow_succ n k⟩, ?_⟩
  have h : k+1 < n^(k+1) := Nat.lt_pow_self hn
  omega

/-- On zero-based ranks, exchange 0 with 1, 2 with 3, and so on. -/
private def swapRank (r : ℕ) : ℕ := if r%2 = 0 then r+1 else r-1

private lemma swap_twice (r : ℕ) : swapRank (swapRank r) = r := by
  unfold swapRank
  split_ifs <;> omega

private lemma swap_ne (r : ℕ) : swapRank r ≠ r := by
  unfold swapRank
  split_ifs <;> omega

private lemma swap_earlier {i j : ℕ} (hne : j ≠ i) (hlt : j < swapRank i) : swapRank j < i := by
  unfold swapRank at *
  split_ifs at * <;> omega

private noncomputable def mate (n : ℕ) : ℕ :=
  if 1 < n then Nat.nth (fibre n.primeFactors) (swapRank (Nat.count (fibre n.primeFactors) n)) else n

private lemma mate_in_fibre {s : Finset ℕ} {n : ℕ} (hn : fibre s n) :
    mate n = Nat.nth (fibre s) (swapRank (Nat.count (fibre s) n)) := by
  simp only [mate, if_pos hn.1, hn.2]

private lemma mate_at {s : Finset ℕ} (hs : (Set.ofPred (fibre s)).Infinite) (i : ℕ) :
    mate (Nat.nth (fibre s) i) = Nat.nth (fibre s) (swapRank i) := by
  rw [mate_in_fibre (Nat.nth_mem_of_infinite hs i), Nat.count_nth_of_infinite hs i]

private lemma inside {n : ℕ} (hn : 1 < n) : fibre n.primeFactors (mate n) := by
  rw [mate_in_fibre (show fibre n.primeFactors n from ⟨hn, rfl⟩)]
  exact Nat.nth_mem_of_infinite (infinite_fibre hn) _

private lemma mate_twice (n : ℕ) : mate (mate n) = n := by
  by_cases h : 1 < n
  · have hn : fibre n.primeFactors n := ⟨h, rfl⟩
    rw [mate_in_fibre hn, mate_at (infinite_fibre h), swap_twice, Nat.nth_count hn]
  · have e : mate n = n := by simp [mate, h]
    rw [e, e]

private lemma mate_injective : Function.Injective mate :=
  Function.LeftInverse.injective mate_twice

private lemma mate_ne {n : ℕ} (h : 1 < n) : mate n ≠ n := by
  let s := n.primeFactors
  have hn : fibre s n := ⟨h, rfl⟩
  intro he
  have e := (mate_in_fibre hn).symm.trans (he.trans (Nat.nth_count hn).symm)
  exact swap_ne _ (Nat.nth_injective (infinite_fibre h) e)

/-- A smaller admissible value already has a partner before the current index. -/
private lemma earlier {s : Finset ℕ} {n k : ℕ} (hs : (Set.ofPred (fibre s)).Infinite)
    (hn : fibre s n) (hk : fibre s k) (hne : k ≠ n) (hlt : k < mate n) : mate k < n := by
  obtain ⟨i, rfl⟩ : ∃ i, Nat.nth (fibre s) i = n := ⟨_, Nat.nth_count hn⟩
  obtain ⟨j, rfl⟩ : ∃ j, Nat.nth (fibre s) j = k := ⟨_, Nat.nth_count hk⟩
  rw [mate_at hs] at hlt ⊢
  exact (Nat.nth_lt_nth hs).mpr (swap_earlier (fun e => hne (congrArg _ e)) ((Nat.nth_lt_nth hs).mp hlt))

private lemma seen_succ (t : ℕ) :
    (state (t+1)).seen = insert (a (t+1)) (state t).seen := by
  cases t with
  | zero => ext k; simp [state, a, or_comm]
  | succ t => rfl

private lemma mem_seen (t k : ℕ) : k ∈ (state t).seen ↔ ∃ j ≤ t, a j = k := by
  induction t with
  | zero => simp [state, a, eq_comm]
  | succ t ih =>
    rw [seen_succ, Finset.mem_insert, ih]
    constructor
    · rintro (e | ⟨j, hj, h⟩)
      · exact ⟨t+1, le_rfl, e.symm⟩
      · exact ⟨j, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      by_cases e : j = t+1
      · exact Or.inl (e ▸ h.symm)
      · exact Or.inr ⟨j, by omega, h⟩

/-- The explicitly paired enumeration realizes the least-unused rule at every index. -/
private lemma greedy_eq (n : ℕ) : a n = mate n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | j+2 =>
      let C : Set ℕ := {k | 0 < k ∧ k ≠ j+2 ∧ k ∉ (state (j+1)).seen ∧ k.primeFactors = (j+2).primeFactors}
      change sInf C = mate (j+2)
      have hn : 1 < j+2 := by omega
      have hself : fibre (j+2).primeFactors (j+2) := ⟨hn, rfl⟩
      have hm : mate (j+2) ∈ C := by
        refine ⟨by have := (inside hn).1; omega, mate_ne hn, ?_, (inside hn).2⟩
        intro seen
        obtain ⟨i, hi, e⟩ := (mem_seen _ _).mp seen
        rw [ih i (by omega)] at e
        have := mate_injective e
        omega
      have least (k : ℕ) (hk : k ∈ C) : mate (j+2) ≤ k := by
        obtain ⟨_, hne, fresh, eq⟩ := hk
        have hclass : fibre (j+2).primeFactors k :=
          ⟨Nat.nonempty_primeFactors.mp (eq.symm ▸ Nat.nonempty_primeFactors.mpr hn), eq⟩
        by_contra! e
        have lt := earlier (infinite_fibre hn) hself hclass hne e
        apply fresh
        exact (mem_seen _ _).mpr ⟨mate k, by omega, (ih _ lt).trans (mate_twice k)⟩
      exact le_antisymm (Nat.sInf_le hm) (least _ (Nat.sInf_mem ⟨_, hm⟩))

theorem self_inverse (n : ℕ) : a (a n) = n := by
  simp only [greedy_eq, mate_twice]

private lemma positive {n : ℕ} (hn : 1 ≤ n) : 1 ≤ a n := by
  rcases eq_or_lt_of_le hn with e | h
  · subst n; decide
  · rw [greedy_eq]
    exact le_of_lt (inside h).1

private lemma upper_neighbour {s : Finset ℕ} {n w : ℕ} (hs : (Set.ofPred (fibre s)).Infinite)
    (hn : fibre s n) (hw : fibre s w) (hlt : n < w) : mate n ≤ w := by
  obtain ⟨i, rfl⟩ : ∃ i, Nat.nth (fibre s) i = n := ⟨_, Nat.nth_count hn⟩
  obtain ⟨j, rfl⟩ : ∃ j, Nat.nth (fibre s) j = w := ⟨_, Nat.nth_count hw⟩
  rw [mate_at hs]
  apply (Nat.nth_le_nth hs).mpr
  have := (Nat.nth_lt_nth hs).mp hlt
  unfold swapRank
  split_ifs <;> omega

private lemma square_bound (n : ℕ) : a n ≤ n^2 := by
  rw [greedy_eq]
  by_cases h : 1 < n
  · apply upper_neighbour (infinite_fibre h) (show fibre n.primeFactors n from ⟨h, rfl⟩)
      (show fibre n.primeFactors (n^2) from ⟨one_lt_pow₀ h (by decide), Nat.primeFactors_pow n (by decide)⟩)
    simpa using (pow_lt_pow_right₀ h (by decide : 1 < 2))
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> decide

/-- The increasing enumeration of the radical class of a prime is p, p², p³, ... . -/
private lemma prime_nth {p : ℕ} (hp : p.Prime) (i : ℕ) : Nat.nth (fibre {p}) i = p^(i+1) := by
  have inf : (Set.ofPred (fibre {p})).Infinite := by simpa [hp.primeFactors] using infinite_fibre hp.one_lt
  let F (j : ℕ) := p^(j+1)
  have admissible (j : ℕ) : ∀ hf : (Set.ofPred (fibre {p})).Finite, j < hf.toFinset.card :=
    fun hf => (inf hf).elim
  have maps (j : ℕ) : fibre {p} (F j) :=
    ⟨one_lt_pow₀ hp.one_lt (by omega), Nat.primeFactors_prime_pow (by omega) hp⟩
  have onto (k : ℕ) (hk : fibre {p} k) : ∃ j, F j = k := by
    have hk0 : k ≠ 0 := by have := hk.1; omega
    have eq : k = p^k.primeFactorsList.length := by
      apply Nat.eq_prime_pow_of_unique_prime_dvd hk0
      intro q hq hd
      have mem := (Nat.mem_primeFactors.mpr ⟨hq, hd, hk0⟩)
      rw [hk.2] at mem
      simpa using mem
    cases e : k.primeFactorsList.length with
    | zero => rw [e, pow_zero] at eq; exact False.elim ((by have := hk.1; omega : False))
    | succ j => exact ⟨j, by simpa [F, e] using eq.symm⟩
  have hmono : StrictMono F := by
    intro j k h
    exact pow_lt_pow_right₀ hp.one_lt (by omega : j+1 < k+1)
  have eq := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := fibre {p}) F
    (fun k hk => by obtain ⟨j, rfl⟩ := onto k hk; exact ⟨j, admissible j, rfl⟩)
    (fun j _ => maps j) (hmono.strictMonoOn _)
  exact (eq (admissible i)).symm

theorem prime_power_pairs {p : ℕ} (hp : p.Prime) (k : ℕ) :
    a (p^(2*k+1)) = p^(2*k+2) ∧ a (p^(2*k+2)) = p^(2*k+1) := by
  have hs : (Set.ofPred (fibre {p})).Infinite := by simpa [hp.primeFactors] using infinite_fibre hp.one_lt
  have lhs (j : ℕ) : a (p^(j+1)) = p^(swapRank j + 1) := by
    rw [greedy_eq, ← prime_nth hp j, mate_at hs, prime_nth hp]
  have e : swapRank (2*k) = 2*k+1 := by unfold swapRank; split_ifs <;> omega
  have o : swapRank (2*k+1) = 2*k := by unfold swapRank; split_ifs <;> omega
  exact ⟨by simpa [e] using lhs (2*k), by simpa [o] using lhs (2*k+1)⟩

private lemma at_prime {p : ℕ} (hp : p.Prime) : a p = p^2 := by
  simpa using (prime_power_pairs hp 0).1

private lemma at_prime_square {p : ℕ} (hp : p.Prime) : a (p^2) = p := by
  simpa using (prime_power_pairs hp 0).2

private lemma prime_index {i : ℕ} (hp : (a i).Prime) : i = (a i)^2 :=
  (self_inverse i).symm.trans (at_prime hp)

private lemma above_prime {p k : ℕ} (hp : p.Prime) (hk : (p-1)^2 < k) (hne : k ≠ p^2) :
    p < a k := by
  have rev : k ≤ (a k)^2 := by simpa only [self_inverse] using square_bound (a k)
  have ne : a k ≠ p := by
    intro e
    exact hne ((self_inverse k).symm.trans ((congrArg a e).trans (at_prime hp)))
  by_contra! h
  have := Nat.pow_le_pow_left (show a k ≤ p-1 by omega) 2
  omega

private lemma prime_minimum {p : ℕ} (hp : p.Prime) : localMinimum (p^2) := by
  have h := hp.one_lt
  have he : p^2 = (p-1)^2 + 2*(p-1)+1 := by
    nth_rw 1 [show p = p-1+1 by omega]
    ring
  have gap : (p-1)^2 < p^2-1 := by omega
  refine ⟨one_lt_pow₀ h (by decide), ?_, ?_⟩
  · rw [at_prime_square hp]
    exact above_prime hp gap (by omega)
  · rw [at_prime_square hp]
    exact above_prime hp (by omega) (by omega)

private lemma prime_record {p : ℕ} (hp : p.Prime) : record p := by
  refine ⟨hp.pos, fun j _ hj => ?_⟩
  rw [at_prime hp]
  exact (square_bound j).trans_lt (Nat.pow_lt_pow_left hj (by decide))

/-- An available larger member of the same class is n times its least prime factor. -/
private lemma minfac_bound (n : ℕ) (hn : 1 < n) : a n ≤ n*n.minFac := by
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  have hn0 : n ≠ 0 := by omega
  have hm : n.minFac ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd n, hn0⟩
  have lg : n < n*n.minFac := by
    simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt (by omega : 0 < n)
  have eq : (n*n.minFac).primeFactors = n.primeFactors := by
    rw [Nat.primeFactors_mul hn0 hp.ne_zero, hp.primeFactors]
    exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hm)
  rw [greedy_eq]
  exact upper_neighbour (infinite_fibre hn) (show fibre n.primeFactors n from ⟨hn, rfl⟩)
    (show fibre n.primeFactors (n*n.minFac) from ⟨by omega, eq⟩) lg

private lemma earlier_prime (n : ℕ) (hn : 1 < n) (hc : ¬n.Prime) :
    ∃ q < n, q.Prime ∧ n*n.minFac ≤ q^2 := by
  by_cases small : n < 16
  · have finite : ∀ k ∈ Finset.range 16, 1 < k → ¬k.Prime →
        ∃ p ∈ Finset.range k, p.Prime ∧ k*k.minFac ≤ p^2 := by decide +kernel
    obtain ⟨q, hq, hp, hb⟩ := finite n (Finset.mem_range.mpr small) hn hc
    exact ⟨q, Finset.mem_range.mp hq, hp, hb⟩
  · obtain ⟨q, hq, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n/2) (by omega)
    have neq : q ≠ n := fun eq => hc (eq ▸ hq)
    have hd : 4*n.minFac ≤ n := by
      by_cases hf : n.minFac ≤ 4
      · omega
      · have hi := Nat.mul_le_mul_right n.minFac (show 4 ≤ n.minFac by omega)
        have sq := Nat.minFac_sq_le_self (show 0 < n by omega) hc
        nlinarith only [hi, sq]
    refine ⟨q, by omega, hq, ?_⟩
    have h1 := Nat.mul_le_mul_left n hd
    have h2 := Nat.pow_le_pow_left (show n ≤ 2*q by omega) 2
    nlinarith only [h1, h2]

/-- The complete set of record indices is 1 together with the primes. At a prime
index p the record value is p². Bertrand's postulate excludes composite indices. -/
theorem record_iff (n : ℕ) : record n ↔ n = 1 ∨ n.Prime := by
  constructor
  · intro rec
    by_cases he : n = 1
    · exact Or.inl he
    · right
      by_contra hc
      have hn : 1 < n := by have := rec.1; omega
      obtain ⟨p, lt, hp, hb⟩ := earlier_prime n hn hc
      have strict := rec.2 p hp.pos lt
      rw [at_prime hp] at strict
      have upper := minfac_bound n hn
      omega
  · rintro (rfl | hp)
    · exact ⟨by decide, fun j hj hj' => by omega⟩
    · exact prime_record hp

end OMA.Sycamore

open OMA.Sycamore

theorem OMA.solution : type_of% @OMA.S_oeis_a358971.main := by
  refine ⟨⟨fun _ hi => positive hi, (Function.LeftInverse.injective self_inverse).injOn,
    fun n hn => ⟨a n, positive hn, self_inverse n⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro i j _ hij hpi hpj
    by_contra! h
    have hle := Nat.pow_le_pow_left h 2
    rw [← prime_index hpi, ← prime_index hpj] at hle
    omega
  · intro i _ hp
    simpa only [← prime_index hp] using prime_minimum hp
  · exact (record_iff 1).mpr (Or.inl rfl)
  · exact fun p hp => ⟨p, prime_record hp, at_prime hp⟩

