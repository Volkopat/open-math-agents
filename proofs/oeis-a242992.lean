import OMAStatements.S_oeis_a242992

-- A proper divisor d of n-1 corresponds to the admissible index k=n-d.
-- The Mersenne divisibility condition is Euclidean division on the exponent.
open OMA.S_oeis_a242992

private theorem mers (d j : ℕ) :
    (2^d-1 : ℕ) ∣ 2^j-1 ↔ d ∣ j := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.pow_sub_one_mod_pow_sub_one, Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h
    by_contra hn
    have hlt : 1 < (2:ℕ)^(j%d) := Nat.one_lt_pow hn (by decide)
    omega
  · intro h; simp [h]

private theorem predicate_iff (n k : ℕ) (hn : 2 < n) (hk : n/2 < k) (hkn : k < n) :
    (2^(n-k)-1 : ℕ) ∣ 2^k-2 ↔ n-k ∈ (n-1).properDivisors := by
  have hk' : k-1+1 = k := by omega
  have ht : n-k-1+1 = n-k := by omega
  have hpos : 0 < (2:ℕ)^(k-1) := Nat.pow_pos (by decide)
  have htpos : 0 < (2:ℕ)^(n-k-1) := Nat.pow_pos (by decide)
  have hc : (2^(n-k)-1 : ℕ).Coprime 2 := by
    apply Nat.coprime_two_right.mpr
    refine ⟨2^(n-k-1)-1, ?_⟩
    conv_lhs => rw [← ht, pow_succ]
    omega
  have fac : (2:ℕ)^k-2 = 2*(2^(k-1)-1) := by
    conv_lhs => rw [← hk', pow_succ]
    omega
  rw [fac, hc.dvd_mul_left, mers, Nat.mem_properDivisors]
  have sum : n-1 = (n-k)+(k-1) := by omega
  constructor
  · intro h
    exact ⟨sum ▸ dvd_add (dvd_refl _) h, by omega⟩
  · rintro ⟨h, -⟩
    rw [sum] at h
    exact (Nat.dvd_add_iff_right (dvd_refl _)).mpr h

private theorem bound_of_divisor {n d : ℕ} (hn : 2 < n) (hd : d ∈ (n-1).properDivisors) :
    0 < d ∧ n/2 < n-d := by
  obtain ⟨t, ht, he⟩ := (Nat.mem_properDivisors_iff_exists (by omega : n-1 ≠ 0)).mp hd
  have h := Nat.mul_le_mul_left d (show 2 ≤ t by omega)
  have hpos := Nat.pos_of_mem_properDivisors hd
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a242992.main := by
  intro n hn
  let D := (n-1).properDivisors.sup id
  have oneMem := Nat.one_mem_properDivisors_iff_one_lt.mpr (show 1 < n-1 by omega)
  have hD : D ∈ (n-1).properDivisors := by
    have hh := Finset.sup_mem_of_nonempty (f := id) (show (n-1).properDivisors.Nonempty from ⟨1, oneMem⟩)
    simpa [D] using hh
  obtain ⟨hdpos, hk⟩ := bound_of_divisor hn hD
  have hdlt := (Nat.mem_properDivisors.mp hD).2
  have hkn : n-D < n := by omega
  have witness : n-D ∈ {k : ℕ | n/2 < k ∧ k < n ∧ (2^(n-k)-1) ∣ (2^k-2)} := by
    refine ⟨hk, hkn, (predicate_iff n (n-D) hn hk hkn).mpr ?_⟩
    rwa [show n-(n-D)=D by omega]
  have rhs : b (n-1) = D := by simp [b, D, show n-1 ≠ 1 by omega]
  rw [rhs, a]
  apply le_antisymm (csInf_le (OrderBot.bddBelow _) witness)
  refine le_csInf ⟨_, witness⟩ ?_
  rintro k ⟨hhalf, hkn', hpow⟩
  have hdiv := (predicate_iff n k hn hhalf hkn').mp hpow
  have hmax : n-k ≤ D := Finset.le_sup (f := id) hdiv
  omega
