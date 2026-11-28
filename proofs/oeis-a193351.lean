import OMAStatements.S_oeis_a193351

-- Problem: A193351: Numbers k such that A071324(k) is prime.
-- Upstream: formal-conjectures statements/oeis-a193351.lean:0 (declaration OMA.S_oeis_a193351.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the sorted divisor list is k :: (proper divisors, nonincreasing), and the
-- alternating sum of a nonincreasing list of naturals lies between 0 and its first entry, so
-- A071324(k) >= k - k/2 >= 3 for k >= 5. The alternating sum has the parity of the plain sum
-- sigma(k). Write k = 2^a * m with m odd. If k is neither a square nor twice a square, m is not
-- a square, and d -> m/d pairs the odd divisors of k without fixed points, so sigma(k) is
-- even. Then A071324(k) is even and at least 3, hence not prime.

open OMA.S_oeis_a193351 in
theorem OMA.solution : type_of% @OMA.S_oeis_a193351.main := by
  have alt_nil : altSum [] = 0 := rfl
  have alt_cons : ∀ (x : ℕ) (l : List ℕ), altSum (x :: l) = (x : ℤ) - altSum l :=
    fun _ _ => rfl
  have altB : ∀ l : List ℕ, l.Pairwise (· ≥ ·) → ∀ x : ℕ, (∀ y ∈ l, y ≤ x) →
      0 ≤ altSum l ∧ altSum l ≤ (x : ℤ) := by
    intro l
    induction l with
    | nil =>
      intro _ x _
      rw [alt_nil]
      exact ⟨le_refl 0, Nat.cast_nonneg x⟩
    | cons d t ih =>
      intro hp x hx
      rw [List.pairwise_cons] at hp
      obtain ⟨hd, ht⟩ := hp
      have h1 := ih ht d (fun y hy => hd y hy)
      have h2 : d ≤ x := hx d (by simp)
      have h3 : (d : ℤ) ≤ (x : ℤ) := by exact_mod_cast h2
      rw [alt_cons]
      constructor
      · linarith [h1.2]
      · linarith [h1.1]
  have altP : ∀ l : List ℕ, ∃ c : ℤ, ((l.sum : ℕ) : ℤ) = altSum l + 2 * c := by
    intro l
    induction l with
    | nil => exact ⟨0, by simp [alt_nil]⟩
    | cons d t ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨altSum t + c, ?_⟩
      rw [alt_cons, List.sum_cons, Nat.cast_add, hc]
      ring
  intro k p hk hp hS
  have hk0 : k ≠ 0 := by omega
  have hdef : A071324 k = altSum ((Nat.divisors k).sort (· ≥ ·)) := rfl
  rw [hdef] at hS
  have hsort : (Nat.divisors k).sort (· ≥ ·) = k :: (Nat.properDivisors k).sort (· ≥ ·) := by
    rw [← Nat.insert_self_properDivisors hk0]
    refine Finset.sort_insert (· ≥ ·) ?_ Nat.self_notMem_properDivisors
    intro b hb
    exact le_of_lt (Nat.mem_properDivisors.mp hb).2
  have hpd : ∀ y ∈ (Nat.properDivisors k).sort (· ≥ ·), y ≤ k / 2 := by
    intro y hy
    rw [Finset.mem_sort] at hy
    obtain ⟨hyd, hylt⟩ := Nat.mem_properDivisors.mp hy
    obtain ⟨c, hc⟩ := hyd
    have hc2 : 2 ≤ c := by
      by_contra hlt
      rcases (by omega : c = 0 ∨ c = 1) with h0 | h1
      · rw [h0, mul_zero] at hc
        exact hk0 hc
      · rw [h1, mul_one] at hc
        omega
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    calc y * 2 ≤ y * c := Nat.mul_le_mul_left y hc2
      _ = k := hc.symm
  obtain ⟨_, hL1⟩ := altB ((Nat.properDivisors k).sort (· ≥ ·))
    (Finset.pairwise_sort _ _) (k / 2) hpd
  have hS2 : (p : ℤ) = (k : ℤ) - altSum ((Nat.properDivisors k).sort (· ≥ ·)) := by
    rw [← hS, hsort, alt_cons]
  by_contra hcon
  have hsq : ∀ m : ℕ, k ≠ m ^ 2 := fun m h => hcon (Or.inl ⟨m, h⟩)
  have htw : ∀ m : ℕ, k ≠ 2 * m ^ 2 := fun m h => hcon (Or.inr ⟨m, h⟩)
  have hk4 : k ≠ 4 := fun h => hsq 2 (h.trans (by norm_num))
  obtain ⟨a, m, hmodd, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  have hmsq : ∀ d : ℕ, m ≠ d * d := by
    intro d hd
    obtain ⟨b, hb | hb⟩ := Nat.even_or_odd' a
    · apply hsq (2 ^ b * d)
      rw [hkm, hd, hb, pow_mul' (2 : ℕ) 2 b]
      ring
    · apply htw (2 ^ b * d)
      rw [hkm, hd, hb, pow_succ (2 : ℕ) (2 * b), pow_mul' (2 : ℕ) 2 b]
      ring
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hk0 (by rw [hkm, mul_zero])
  have hqodd : ∀ d : ℕ, d ∣ m → m / d % 2 = 1 := by
    intro d hdm
    have h : Odd (d * (m / d)) := by
      rw [Nat.mul_div_cancel' hdm]
      exact hmodd
    exact Nat.odd_iff.mp (Nat.odd_mul.mp h).2
  have hoddm : ∀ d ∈ Nat.divisors k, d % 2 = 1 → d ∣ m := by
    intro d hd hdo
    have hdk : d ∣ 2 ^ a * m := by
      rw [← hkm]
      exact Nat.dvd_of_mem_divisors hd
    have h2 : ¬ 2 ∣ d := by omega
    have hc2 : Nat.Coprime d 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
    exact (Nat.Coprime.pow_right a hc2).dvd_of_dvd_mul_left hdk
  have hZ : ∑ d ∈ Nat.divisors k, ((d : ℕ) : ZMod 2) = 0 := by
    refine Finset.sum_involution
      (fun (d : ℕ) (_ : d ∈ Nat.divisors k) => if d % 2 = 1 then m / d else d) ?_ ?_ ?_ ?_
    · intro d hd
      show ((d : ℕ) : ZMod 2) + (((if d % 2 = 1 then m / d else d : ℕ)) : ZMod 2) = 0
      by_cases hdo : d % 2 = 1
      · rw [if_pos hdo, ← ZMod.natCast_mod d 2, ← ZMod.natCast_mod (m / d) 2, hdo,
          hqodd d (hoddm d hd hdo)]
        decide
      · rw [if_neg hdo, ← ZMod.natCast_mod d 2, show d % 2 = 0 by omega, Nat.cast_zero,
          add_zero]
    · intro d hd hne
      show (if d % 2 = 1 then m / d else d) ≠ d
      have hdo : d % 2 = 1 := by
        by_contra h
        apply hne
        show ((d : ℕ) : ZMod 2) = 0
        rw [← ZMod.natCast_mod d 2, show d % 2 = 0 by omega, Nat.cast_zero]
      rw [if_pos hdo]
      intro heq
      apply hmsq d
      rw [← Nat.div_mul_cancel (hoddm d hd hdo), heq]
    · intro d hd
      show (if d % 2 = 1 then m / d else d) ∈ Nat.divisors k
      by_cases hdo : d % 2 = 1
      · rw [if_pos hdo, Nat.mem_divisors]
        refine ⟨?_, hk0⟩
        rw [hkm]
        exact Dvd.dvd.mul_left (Nat.div_dvd_of_dvd (hoddm d hd hdo)) _
      · rw [if_neg hdo]
        exact hd
    · intro d hd
      show (if (if d % 2 = 1 then m / d else d) % 2 = 1 then
          m / (if d % 2 = 1 then m / d else d) else (if d % 2 = 1 then m / d else d)) = d
      by_cases hdo : d % 2 = 1
      · have hdm := hoddm d hd hdo
        rw [if_pos hdo, if_pos (hqodd d hdm), Nat.div_div_self hdm hm0]
      · simp only [if_neg hdo]
  have hev : 2 ∣ ∑ d ∈ Nat.divisors k, d := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    exact hZ
  obtain ⟨e, he⟩ := hev
  obtain ⟨c, hc⟩ := altP ((Nat.divisors k).sort (· ≥ ·))
  have hLsum : ((Nat.divisors k).sort (· ≥ ·)).sum = ∑ d ∈ Nat.divisors k, d := by
    have h := List.sum_toFinset (fun d => d) (Finset.sort_nodup (Nat.divisors k) (· ≥ ·))
    rw [Finset.sort_toFinset] at h
    rw [h]
    simp
  rw [hLsum, he, hS] at hc
  have hp3 : (3 : ℤ) ≤ (p : ℤ) := by
    rw [hS2]
    omega
  rcases hp.eq_two_or_odd with h2 | h2 <;> omega
