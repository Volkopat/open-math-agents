import OMAStatements.S_oeis_a066052

-- Problem: OEIS A066052, number of permutations of n letters of order at least 3.
-- Conjecture (R. J. Mathar): two P-recursive recurrences for a(n) (orders 3 and 4).
-- Proof. a(n) = n! - I(n), where I(n) counts the permutations with g^2 = 1. Such a permutation has
-- cycle type k transpositions, and Mathlib's count of permutations of a given cycle type gives
-- c(n,k) * ((n-2k)! * 2^k * k!) = n!, hence c(n+2,k+1) = c(n+1,k+1) + (n+1) c(n,k) and
-- I(n+2) = I(n+1) + (n+1) I(n). Both recurrences are then linear combinations of this relation
-- and of (n+1)! = (n+1) n!.

open OMA.S_oeis_a066052 Finset Equiv

/-- Number of permutations of `Fin n` whose cycle type is `k` transpositions. -/
noncomputable def OMA.c (n k : ℕ) : ℕ :=
  #({g | g.cycleType = Multiset.replicate k 2} : Finset (Perm (Fin n)))

lemma OMA.c_mul (n k : ℕ) (h : 2 * k ≤ n) :
    OMA.c n k * ((n - 2 * k).factorial * 2 ^ k * k.factorial) = n.factorial := by
  have key := Perm.card_of_cycleType_mul_eq (Fin n) (Multiset.replicate k 2)
  have hsum : (Multiset.replicate k 2).sum = 2 * k := by simp [mul_comm]
  have hprod : (Multiset.replicate k 2).prod = 2 ^ k := by simp
  have hcount : (∏ n ∈ (Multiset.replicate k 2).toFinset, ((Multiset.replicate k 2).count n).factorial)
      = k.factorial := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Multiset.toFinset_replicate, if_neg (by omega)]
      simp
  rw [hsum, hprod, hcount, Fintype.card_fin, if_pos] at key
  · exact key
  · exact ⟨h, fun a ha => by rw [Multiset.eq_of_mem_replicate ha]⟩

lemma OMA.c_zero_of_lt (n k : ℕ) (h : n < 2 * k) : OMA.c n k = 0 := by
  have key := (Perm.card_of_cycleType_eq_zero_iff (Fin n) (m := Multiset.replicate k 2)).mpr
  apply key
  rintro ⟨h1, -⟩
  simp [mul_comm] at h1
  omega

lemma OMA.alg1 (X2 X1 X0 F jf T kf n k i : ℕ) (hn : n = 2 * k + i + 1)
    (A : X2 * ((i + 1) * jf * (T * 2) * ((k + 1) * kf)) = (n + 2) * ((n + 1) * F))
    (B1 : X1 * (jf * (T * 2) * ((k + 1) * kf)) = (n + 1) * F)
    (B0 : X0 * ((i + 1) * jf * T * kf) = F) :
    X2 * ((i + 1) * jf * (T * 2) * ((k + 1) * kf))
      = (X1 + (n + 1) * X0) * ((i + 1) * jf * (T * 2) * ((k + 1) * kf)) := by
  subst hn
  have h1 : X1 * ((i + 1) * jf * (T * 2) * ((k + 1) * kf))
      = (i + 1) * (X1 * (jf * (T * 2) * ((k + 1) * kf))) := by ring
  have h0 : (2 * k + i + 1 + 1) * X0 * ((i + 1) * jf * (T * 2) * ((k + 1) * kf))
      = (2 * k + i + 1 + 1) * (2 * (k + 1)) * (X0 * ((i + 1) * jf * T * kf)) := by ring
  have hR : (X1 + (2 * k + i + 1 + 1) * X0) * ((i + 1) * jf * (T * 2) * ((k + 1) * kf))
      = X1 * ((i + 1) * jf * (T * 2) * ((k + 1) * kf))
        + (2 * k + i + 1 + 1) * X0 * ((i + 1) * jf * (T * 2) * ((k + 1) * kf)) := by ring
  rw [hR, h1, h0, B1, B0, A]
  ring

lemma OMA.alg0 (X2 X0 F jf T kf n k : ℕ) (hn : n = 2 * k)
    (A : X2 * (jf * (T * 2) * ((k + 1) * kf)) = (n + 2) * ((n + 1) * F))
    (B0 : X0 * (jf * T * kf) = F) :
    X2 * (jf * (T * 2) * ((k + 1) * kf))
      = (0 + (n + 1) * X0) * (jf * (T * 2) * ((k + 1) * kf)) := by
  subst hn
  have h0 : (2 * k + 1) * X0 * (jf * (T * 2) * ((k + 1) * kf))
      = (2 * k + 1) * (2 * (k + 1)) * (X0 * (jf * T * kf)) := by ring
  rw [zero_add, h0, B0, A]
  ring

lemma OMA.c_rec (n k : ℕ) :
    OMA.c (n + 2) (k + 1) = OMA.c (n + 1) (k + 1) + (n + 1) * OMA.c n k := by
  rcases Nat.lt_or_ge n (2 * k) with h | h
  · rw [OMA.c_zero_of_lt (n + 2) (k + 1) (by omega), OMA.c_zero_of_lt (n + 1) (k + 1) (by omega),
      OMA.c_zero_of_lt n k h]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * k + j := ⟨n - 2 * k, by omega⟩
    have e2 := OMA.c_mul (2 * k + j + 2) (k + 1) (by omega)
    have i2 : 2 * k + j + 2 - 2 * (k + 1) = j := by omega
    rw [i2] at e2
    have e0 := OMA.c_mul (2 * k + j) k (by omega)
    have i0 : 2 * k + j - 2 * k = j := by omega
    rw [i0] at e0
    have f2 : (2 * k + j + 2).factorial = (2 * k + j + 2) * ((2 * k + j + 1) * (2 * k + j).factorial) := by
      rw [show 2 * k + j + 2 = (2 * k + j + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    rw [f2, Nat.factorial_succ k, pow_succ] at e2
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hD : 0 < Nat.factorial 0 * (2 ^ k * 2) * ((k + 1) * k.factorial) := by positivity
      apply Nat.eq_of_mul_eq_mul_right hD
      rw [OMA.c_zero_of_lt (2 * k + 0 + 1) (k + 1) (by omega)]
      exact OMA.alg0 _ _ _ _ _ _ (2 * k + 0) k (by omega) e2 e0
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e1 := OMA.c_mul (2 * k + (i + 1) + 1) (k + 1) (by omega)
      have i1 : 2 * k + (i + 1) + 1 - 2 * (k + 1) = i := by omega
      rw [i1, Nat.factorial_succ k, pow_succ,
        show (2 * k + (i + 1) + 1).factorial = (2 * k + (i + 1) + 1) * (2 * k + (i + 1)).factorial from
          Nat.factorial_succ _] at e1
      rw [Nat.factorial_succ i] at e2 e0
      have hD : 0 < (i + 1) * i.factorial * (2 ^ k * 2) * ((k + 1) * k.factorial) := by positivity
      apply Nat.eq_of_mul_eq_mul_right hD
      exact OMA.alg1 _ _ _ _ _ _ _ (2 * k + (i + 1)) k i (by omega) e2 e1 e0

lemma OMA.c_zero (n : ℕ) : OMA.c n 0 = 1 := by
  have h := OMA.c_mul n 0 (Nat.zero_le _)
  simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, Nat.factorial_zero, mul_one] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n) (by rw [h, one_mul])

/-- Number of involutions (including the identity), as a sum over the number of transpositions. -/
noncomputable def OMA.Inv (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), OMA.c n k

lemma OMA.Inv_rec (n : ℕ) : OMA.Inv (n + 2) = OMA.Inv (n + 1) + (n + 1) * OMA.Inv n := by
  unfold OMA.Inv
  rw [Finset.sum_range_succ' (fun k => OMA.c (n + 2) k) (n + 2), OMA.c_zero]
  simp only [OMA.c_rec]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_range_succ' (fun k => OMA.c (n + 1) k) (n + 1), OMA.c_zero]
  rw [Finset.sum_range_succ (fun k => OMA.c (n + 1) (k + 1)) (n + 1)]
  rw [Finset.sum_range_succ (fun k => OMA.c n k) (n + 1)]
  rw [OMA.c_zero_of_lt (n + 1) (n + 1 + 1) (by omega), OMA.c_zero_of_lt n (n + 1) (by omega)]
  ring

lemma OMA.sq_eq_one_iff (n : ℕ) (g : Perm (Fin n)) (k : ℕ) :
    (g ^ 2 = 1 ∧ Multiset.card g.cycleType = k) ↔ g.cycleType = Multiset.replicate k 2 := by
  constructor
  · rintro ⟨h, hk⟩
    rw [Multiset.eq_replicate]
    refine ⟨hk, fun b hb => ?_⟩
    have h1 : b ∣ 2 := (Perm.dvd_of_mem_cycleType hb).trans (orderOf_dvd_of_pow_eq_one h)
    have h2 : 2 ≤ b := Perm.two_le_of_mem_cycleType hb
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2
  · intro h
    refine ⟨?_, by rw [h, Multiset.card_replicate]⟩
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [← Perm.lcm_cycleType, h]
    apply Multiset.lcm_dvd.mpr
    intro a ha
    rw [Multiset.eq_of_mem_replicate ha]

lemma OMA.card_cycleType_le (n : ℕ) (g : Perm (Fin n)) : Multiset.card g.cycleType ≤ n := by
  have h1 : Multiset.card g.cycleType • 2 ≤ g.cycleType.sum :=
    Multiset.card_nsmul_le_sum (fun x hx => Perm.two_le_of_mem_cycleType hx)
  have h2 := g.sum_cycleType_le
  rw [Fintype.card_fin] at h2
  simp only [smul_eq_mul] at h1
  omega

lemma OMA.card_invol (n : ℕ) :
    #({g | g ^ 2 = 1} : Finset (Perm (Fin n))) = OMA.Inv n := by
  unfold OMA.Inv OMA.c
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Perm (Fin n) => Multiset.card g.cycleType)
    (t := Finset.range (n + 1))]
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact OMA.sq_eq_one_iff n g k
  · intro g _
    simp only [Finset.coe_range, Set.mem_Iio]
    have := OMA.card_cycleType_le n g
    omega

lemma OMA.a_add (n : ℕ) : a n + OMA.Inv n = n.factorial := by
  rw [← OMA.card_invol]
  unfold a
  have h : ∀ g : Perm (Fin n), 3 ≤ orderOf g ↔ ¬ g ^ 2 = 1 := by
    intro g
    have hpos : 0 < orderOf g := orderOf_pos g
    rw [← orderOf_dvd_iff_pow_eq_one]
    constructor
    · intro h3 hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    · intro hnd
      by_contra h3
      apply hnd
      have h12 : orderOf g = 1 ∨ orderOf g = 2 := by omega
      rcases h12 with h | h <;> rw [h] <;> norm_num
  rw [Finset.filter_congr (fun g _ => h g), add_comm,
    Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]

theorem OMA.solution : type_of% @OMA.S_oeis_a066052.main := by
  have hz : ∀ n : ℕ, (a n : ℤ) = (n.factorial : ℤ) - (OMA.Inv n : ℤ) := by
    intro n
    have h := OMA.a_add n
    have h' : ((a n : ℕ) : ℤ) + (OMA.Inv n : ℤ) = (n.factorial : ℤ) := by exact_mod_cast h
    linarith
  have hI : ∀ n : ℕ, (OMA.Inv (n + 2) : ℤ) = OMA.Inv (n + 1) + ((n : ℤ) + 1) * OMA.Inv n := by
    intro n
    have h := OMA.Inv_rec n
    exact_mod_cast h
  have hF : ∀ n : ℕ, ((n + 1).factorial : ℤ) = ((n : ℤ) + 1) * n.factorial := by
    intro n
    rw [Nat.factorial_succ]
    push_cast
    ring
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have s1 : m + 3 - 1 = m + 2 := rfl
    have s2 : m + 3 - 2 = m + 1 := rfl
    have s3 : m + 3 - 3 = m := rfl
    rw [s1, s2, s3, hz (m + 3), hz (m + 2), hz (m + 1), hz m]
    have I1 : (OMA.Inv (m + 3) : ℤ) = OMA.Inv (m + 2) + ((m : ℤ) + 2) * OMA.Inv (m + 1) := by
      have h := hI (m + 1)
      push_cast at h
      linarith
    have I0 := hI m
    have F2 : ((m + 3).factorial : ℤ) = ((m : ℤ) + 3) * (m + 2).factorial := by
      have h := hF (m + 2)
      push_cast at h
      linarith
    have F1 : ((m + 2).factorial : ℤ) = ((m : ℤ) + 2) * (m + 1).factorial := by
      have h := hF (m + 1)
      push_cast at h
      linarith
    have F0 := hF m
    push_cast
    linear_combination (m : ℤ) * I1 - ((m : ℤ) + 1) * ((m : ℤ) + 2) * I0 - (m : ℤ) * F2
      + ((m : ℤ) + 2) * F1 + ((m : ℤ) + 1) * ((m : ℤ) + 2) * F0
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have s1 : m + 4 - 1 = m + 3 := rfl
    have s2 : m + 4 - 2 = m + 2 := rfl
    have s3 : m + 4 - 3 = m + 1 := rfl
    have s4 : m + 4 - 4 = m := rfl
    rw [s1, s2, s3, s4, hz (m + 4), hz (m + 3), hz (m + 2), hz (m + 1), hz m]
    have I2 : (OMA.Inv (m + 4) : ℤ) = OMA.Inv (m + 3) + ((m : ℤ) + 3) * OMA.Inv (m + 2) := by
      have h := hI (m + 2)
      push_cast at h
      linarith
    have I1 : (OMA.Inv (m + 3) : ℤ) = OMA.Inv (m + 2) + ((m : ℤ) + 2) * OMA.Inv (m + 1) := by
      have h := hI (m + 1)
      push_cast at h
      linarith
    have I0 := hI m
    have F3 : ((m + 4).factorial : ℤ) = ((m : ℤ) + 4) * (m + 3).factorial := by
      have h := hF (m + 3)
      push_cast at h
      linarith
    have F2 : ((m + 3).factorial : ℤ) = ((m : ℤ) + 3) * (m + 2).factorial := by
      have h := hF (m + 2)
      push_cast at h
      linarith
    have F1 : ((m + 2).factorial : ℤ) = ((m : ℤ) + 2) * (m + 1).factorial := by
      have h := hF (m + 1)
      push_cast at h
      linarith
    have F0 := hF m
    push_cast
    linear_combination (-1 : ℤ) * I2 + ((m : ℤ) + 6) * I1 - 2 * ((m : ℤ) + 2) * I0 + F3
      - 3 * F2 - ((m : ℤ) + 2) * F1 + 2 * ((m : ℤ) + 2) * F0
