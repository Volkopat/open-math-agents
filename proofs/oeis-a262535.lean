import OMAStatements.S_oeis_a262535

-- Problem: A262535: Triangle read by rows T(n,k) in which column k lists the partial sums of the k-th column of triangle A261699.
-- Upstream: formal-conjectures statements/oeis-a262535.lean:0 (declaration OMA.S_oeis_a262535.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the columns k with k(k+1)/2 > n contribute 0, so the row sum is the double sum of
-- A261699(j,k) over 1 <= j, k <= n; swap the sums. Row j of A261699 (any k-range 1..N with N >= j)
-- sums to the sum of the odd divisors of j: a nonzero entry has 2j = k(k+1) + 2ki; for odd
-- k = 2m+1 its value is k and j = k(m+1+i); for even k = 2m its value is d = 2m+1+2i and j = m*d.
-- The value map k -> A261699(j,k) is a bijection from the nonzero entries onto the odd divisors
-- d = 2a+1 of j = d*c (k = d when c >= a+1, k = 2c when c <= a).

namespace K03A262535

open OMA.S_oeis_a262535

theorem two_tri (k : ℕ) : 2 * (k * (k + 1) / 2) = k * (k + 1) :=
  Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_succ_self k))

theorem A_zero (j k : ℕ) (h : j < k * (k + 1) / 2) : A261699 j k = 0 := by
  have hn : ¬(k * (k + 1) / 2 ≤ j ∧ (j - k * (k + 1) / 2) % k = 0) :=
    fun h1 => absurd h1.1 (Nat.not_le.mpr h)
  unfold A261699
  rw [if_neg hn]

theorem A_spec (j k : ℕ) (h : A261699 j k ≠ 0) :
    ∃ i, 2 * j = k * (k + 1) + 2 * (k * i) ∧
      A261699 j k = (if k % 2 = 1 then k else k + 1 + 2 * i) := by
  by_cases hc : k * (k + 1) / 2 ≤ j ∧ (j - k * (k + 1) / 2) % k = 0
  · refine ⟨(j - k * (k + 1) / 2) / k, ?_, ?_⟩
    · have h1 : k * ((j - k * (k + 1) / 2) / k) = j - k * (k + 1) / 2 :=
        Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.2)
      have h2 := two_tri k
      have h3 := hc.1
      omega
    · unfold A261699
      rw [if_pos hc]
  · exfalso
    apply h
    unfold A261699
    rw [if_neg hc]

theorem A_of (j k i : ℕ) (hk : 1 ≤ k) (h : 2 * j = k * (k + 1) + 2 * (k * i)) :
    A261699 j k = (if k % 2 = 1 then k else k + 1 + 2 * i) := by
  have h2 := two_tri k
  have h1 : j - k * (k + 1) / 2 = k * i := by omega
  have hle : k * (k + 1) / 2 ≤ j := by omega
  have hm : (j - k * (k + 1) / 2) % k = 0 := by
    rw [h1]
    exact Nat.mul_mod_right k i
  have hd : (j - k * (k + 1) / 2) / k = i := by
    rw [h1]
    exact Nat.mul_div_cancel_left i (by omega)
  unfold A261699
  rw [if_pos ⟨hle, hm⟩, hd]

theorem odd_or_even (k : ℕ) : (∃ m, k = 2 * m + 1) ∨ (∃ m, k = 2 * m) := by
  by_cases h : k % 2 = 1
  · exact Or.inl ⟨k / 2, by omega⟩
  · exact Or.inr ⟨k / 2, by omega⟩

theorem spec_odd (j m : ℕ) (h : A261699 j (2 * m + 1) ≠ 0) :
    ∃ i, j = (2 * m + 1) * (m + 1 + i) ∧ A261699 j (2 * m + 1) = 2 * m + 1 := by
  obtain ⟨i, he, hv⟩ := A_spec j (2 * m + 1) h
  refine ⟨i, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    rw [he]
    ring
  · rw [hv, if_pos (show (2 * m + 1) % 2 = 1 by omega)]

theorem spec_even (j m : ℕ) (h : A261699 j (2 * m) ≠ 0) :
    ∃ i, j = m * (2 * m + 1 + 2 * i) ∧ A261699 j (2 * m) = 2 * m + 1 + 2 * i := by
  obtain ⟨i, he, hv⟩ := A_spec j (2 * m) h
  refine ⟨i, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    rw [he]
    ring
  · rw [hv, if_neg (show ¬((2 * m) % 2 = 1) by omega)]

theorem row_sum (j N : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, A261699 j k =
      ∑ d ∈ j.divisors.filter (fun d => d % 2 = 1), d := by
  refine Finset.sum_bij_ne_zero (fun k _ _ => A261699 j k) ?_ ?_ ?_ ?_
  · intro k _ hne
    have hne' : A261699 j k ≠ 0 := hne
    show A261699 j k ∈ j.divisors.filter (fun d => d % 2 = 1)
    rw [Finset.mem_filter, Nat.mem_divisors]
    rcases odd_or_even k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · obtain ⟨i, hj', hv⟩ := spec_odd j m hne'
      rw [hv]
      exact ⟨⟨Dvd.intro (m + 1 + i) hj'.symm, by omega⟩, by omega⟩
    · obtain ⟨i, hj', hv⟩ := spec_even j m hne'
      rw [hv]
      have hd : (2 * m + 1 + 2 * i) * m = j := by
        rw [hj']
        ring
      exact ⟨⟨Dvd.intro m hd, by omega⟩, by omega⟩
  · intro k1 _ hne1 k2 _ hne2 h12
    have h1 : A261699 j k1 ≠ 0 := hne1
    have h2 : A261699 j k2 ≠ 0 := hne2
    have he : A261699 j k1 = A261699 j k2 := h12
    rcases odd_or_even k1 with ⟨m1, rfl⟩ | ⟨m1, rfl⟩ <;>
      rcases odd_or_even k2 with ⟨m2, rfl⟩ | ⟨m2, rfl⟩
    · obtain ⟨_, _, hv1⟩ := spec_odd j m1 h1
      obtain ⟨_, _, hv2⟩ := spec_odd j m2 h2
      rw [hv1, hv2] at he
      exact he
    · obtain ⟨i1, hj1, hv1⟩ := spec_odd j m1 h1
      obtain ⟨i2, hj2, hv2⟩ := spec_even j m2 h2
      rw [hv1, hv2] at he
      rw [← he] at hj2
      have hc : (2 * m1 + 1) * (m1 + 1 + i1) = (2 * m1 + 1) * m2 :=
        hj1.symm.trans (hj2.trans (Nat.mul_comm _ _))
      have hm := Nat.eq_of_mul_eq_mul_left (show 0 < 2 * m1 + 1 by omega) hc
      omega
    · obtain ⟨i1, hj1, hv1⟩ := spec_even j m1 h1
      obtain ⟨i2, hj2, hv2⟩ := spec_odd j m2 h2
      rw [hv1, hv2] at he
      rw [he] at hj1
      have hc : (2 * m2 + 1) * (m2 + 1 + i2) = (2 * m2 + 1) * m1 :=
        hj2.symm.trans (hj1.trans (Nat.mul_comm _ _))
      have hm := Nat.eq_of_mul_eq_mul_left (show 0 < 2 * m2 + 1 by omega) hc
      omega
    · obtain ⟨i1, hj1, hv1⟩ := spec_even j m1 h1
      obtain ⟨i2, hj2, hv2⟩ := spec_even j m2 h2
      rw [hv1, hv2] at he
      rw [he] at hj1
      have hc : m1 * (2 * m2 + 1 + 2 * i2) = m2 * (2 * m2 + 1 + 2 * i2) := hj1.symm.trans hj2
      have hm := Nat.eq_of_mul_eq_mul_right (show 0 < 2 * m2 + 1 + 2 * i2 by omega) hc
      omega
  · intro b hb _
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    obtain ⟨⟨⟨c, hc⟩, hj0⟩, hodd⟩ := hb
    obtain ⟨a, rfl⟩ : ∃ a, b = 2 * a + 1 := ⟨b / 2, by omega⟩
    by_cases hca : a + 1 ≤ c
    · obtain ⟨i, rfl⟩ : ∃ i, c = a + 1 + i := ⟨c - (a + 1), by omega⟩
      have hA : A261699 j (2 * a + 1) = 2 * a + 1 := by
        rw [A_of j (2 * a + 1) i (by omega) (by rw [hc]; ring),
          if_pos (show (2 * a + 1) % 2 = 1 by omega)]
      have hle : 2 * a + 1 ≤ j := Nat.le_of_dvd (by omega) (Dvd.intro _ hc.symm)
      refine ⟨2 * a + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
      · show A261699 j (2 * a + 1) ≠ 0
        rw [hA]
        omega
      · show A261699 j (2 * a + 1) = 2 * a + 1
        exact hA
    · obtain ⟨i, rfl⟩ : ∃ i, a = c + i := ⟨a - c, by omega⟩
      have hc1 : 0 < c := by
        apply Nat.pos_of_ne_zero
        rintro rfl
        rw [Nat.mul_zero] at hc
        exact hj0 hc
      have hA : A261699 j (2 * c) = 2 * (c + i) + 1 := by
        rw [A_of j (2 * c) i (by omega) (by rw [hc]; ring),
          if_neg (show ¬((2 * c) % 2 = 1) by omega)]
        omega
      have hle0 : 2 * c ≤ (2 * (c + i) + 1) * c :=
        Nat.mul_le_mul (show 2 ≤ 2 * (c + i) + 1 by omega) (le_refl c)
      have hle : 2 * c ≤ j := by omega
      refine ⟨2 * c, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
      · show A261699 j (2 * c) ≠ 0
        rw [hA]
        omega
      · show A261699 j (2 * c) = 2 * (c + i) + 1
        exact hA
  · intro k _ _
    rfl

theorem main_eq (n : ℕ) : rowSum n = A078471 n := by
  unfold rowSum A078471 T
  have hsub : ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k * (k + 1) / 2 ≤ n),
        ∑ j ∈ Finset.Icc 1 n, A261699 j k =
      ∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, A261699 j k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnk
    apply Finset.sum_eq_zero
    intro j hj
    apply A_zero
    rw [Finset.mem_filter] at hnk
    rw [Finset.mem_Icc] at hj
    have hlt : ¬(k * (k + 1) / 2 ≤ n) := fun h => hnk ⟨hk, h⟩
    have hjn := hj.2
    omega
  rw [hsub, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact row_sum j n hj.1 hj.2

end K03A262535

open OMA.S_oeis_a262535 K03A262535 in
theorem OMA.solution : type_of% @OMA.S_oeis_a262535.main := by
  intro n _
  exact main_eq n
