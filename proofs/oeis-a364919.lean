import OMAStatements.S_oeis_a364919

namespace OMA.S_oeis_a364919




lemma a_succ (n : ℕ) :
    a (n + 1) = sInf {m | 0 < m ∧ (∀ j : Fin (n + 1), a j ≠ m) ∧ rad m ∣ P (n + 1)} := by
  rw [a]

lemma prime_dvd_P {n : ℕ} (hn : n ≠ 0) : ∃ p, p.Prime ∧ p ∣ P n := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hn
  refine ⟨Nat.nth Nat.Prime i, Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i, ?_⟩
  apply Finset.dvd_prod_of_mem
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hi⟩
  have h1 := Nat.ge_two_pow_of_testBit hi
  have h2 : i < 2 ^ i := Nat.lt_two_pow_self
  omega

lemma rad_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : rad (p ^ k) = p := by
  unfold rad
  rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton]

/-- The set defining a(n+1) is nonempty. -/
lemma nonempty (n : ℕ) :
    {m | 0 < m ∧ (∀ j : Fin (n + 1), a j ≠ m) ∧ rad m ∣ P (n + 1)}.Nonempty := by
  obtain ⟨p, hp, hpd⟩ := prime_dvd_P (Nat.succ_ne_zero n)
  set N := (∑ j : Fin (n + 1), a j) + 1 with hN
  refine ⟨p ^ N, pow_pos hp.pos N, fun j hj => ?_, by rw [rad_prime_pow hp (by omega)]; exact hpd⟩
  have h1 : a j ≤ ∑ j : Fin (n + 1), a j :=
    Finset.single_le_sum (f := fun j : Fin (n + 1) => a j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  have h2 : N < 2 ^ N := Nat.lt_two_pow_self
  have h3 : 2 ^ N ≤ p ^ N := Nat.pow_le_pow_left hp.two_le N
  omega

lemma spec (n : ℕ) : 0 < a (n + 1) ∧ (∀ j : Fin (n + 1), a j ≠ a (n + 1)) ∧
    rad (a (n + 1)) ∣ P (n + 1) := by
  rw [a_succ]
  exact Nat.sInf_mem (nonempty n)

lemma le_of_cand (n m : ℕ) (h0 : 0 < m) (h1 : ∀ j : Fin (n + 1), a j ≠ m)
    (h2 : rad m ∣ P (n + 1)) : a (n + 1) ≤ m := by
  rw [a_succ]
  exact Nat.sInf_le ⟨h0, h1, h2⟩

lemma pos (n : ℕ) : 0 < a n := by
  cases n with
  | zero => rw [a]; norm_num
  | succ n => exact (spec n).1

lemma injective : Function.Injective a := by
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    exact (spec n).2.1 ⟨i, by omega⟩ hij
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    exact (spec n).2.1 ⟨j, by omega⟩ hij.symm

/-- For t > m, rad(m) divides A019565(2^t - 1), the product of the first t primes. -/
lemma rad_dvd_P (m t : ℕ) (ht : m < t) : rad m ∣ P (2 ^ t - 1) := by
  have hf : (Finset.range (2 ^ t - 1)).filter (fun i => (2 ^ t - 1).testBit i) = Finset.range t := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have : t < 2 ^ t := Nat.lt_two_pow_self
      omega
  unfold P rad
  rw [hf]
  have hinj : Set.InjOn (Nat.nth Nat.Prime) ↑(Finset.range t) :=
    (Nat.nth_injective Nat.infinite_setOfPred_prime).injOn
  rw [← Finset.prod_image (f := fun p => p) hinj]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpm : p ≤ m := Nat.le_of_mem_primeFactors hp
  rw [Finset.mem_image]
  refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hpp⟩
  rw [Finset.mem_range]
  have := Nat.count_le (p := Nat.Prime) (n := p)
  omega

lemma surjective (m : ℕ) (hm : 0 < m) : ∃ n, a n = m := by
  by_contra hno
  push_neg at hno
  have hs : (Set.Ici (m + 1)).Infinite := Set.Ici_infinite _
  have hmaps : Set.MapsTo (fun t => a (2 ^ t - 1)) (Set.Ici (m + 1)) (Set.Iic m) := by
    intro t ht
    simp only [Set.mem_Ici] at ht
    simp only [Set.mem_Iic]
    have h2 : 2 ≤ 2 ^ t := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨n, hn⟩ : ∃ n, 2 ^ t - 1 = n + 1 := ⟨2 ^ t - 2, by omega⟩
    rw [hn]
    exact le_of_cand n m hm (fun j => hno j) (hn ▸ rad_dvd_P m t (by omega))
  obtain ⟨x, hx, y, hy, hxy, he⟩ := hs.exists_ne_map_eq_of_mapsTo hmaps (Set.finite_Iic m)
  have h1 := injective he
  simp only [Set.mem_Ici] at hx hy
  have hx2 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have hy2 : 1 ≤ 2 ^ y := Nat.one_le_two_pow
  have : 2 ^ x = 2 ^ y := by omega
  exact hxy (Nat.pow_right_injective (le_refl 2) this)

/-- The conjecture: a is a permutation of the positive integers. -/
theorem conjecture : (∀ n, 0 < a n) ∧ Function.Injective a ∧ ∀ m, 0 < m → ∃ n, a n = m :=
  ⟨pos, injective, surjective⟩

end OMA.S_oeis_a364919

theorem OMA.solution : type_of% @OMA.S_oeis_a364919.main :=
  OMA.S_oeis_a364919.conjecture
