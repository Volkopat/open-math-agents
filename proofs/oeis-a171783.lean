import OMAStatements.S_oeis_a171783

-- Problem: A171783, third smallest divisor of the least number with n divisors.
-- Credit: @ShoQo
-- Proof: in the least m with n divisors, a prime q ∣ m forces every smaller prime p ∣ m
-- (otherwise swapping q^e for p^e keeps the divisor count and shrinks m). So 2 ∣ m. Write
-- m = 2^a * s with s odd, so n = (a+1) * #divisors(s). For n prime, s = 1 and m = 2^(n-1),
-- whose divisors start 1, 2, 4. For n = x*y composite, s = 1 is impossible
-- (2^(y-1) * 3^(x-1) is smaller), so s has an odd prime factor and 3 ∣ m: divisors 1, 2, 3.

open OMA.S_oeis_a171783

namespace OMA_A171783_Proof

lemma card_pow_mul {p e r : ℕ} (hp : p.Prime) (hr : ¬ p ∣ r) :
    (p ^ e * r).divisors.card = (e + 1) * r.divisors.card := by
  rw [Nat.Coprime.card_divisors_mul (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hr)),
    Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

lemma card_prime_pow {p e : ℕ} (hp : p.Prime) : (p ^ e).divisors.card = e + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

lemma eq_one_of_card {s : ℕ} (hs0 : s ≠ 0) (h : s.divisors.card = 1) : s = 1 := by
  obtain ⟨d, hd⟩ := Finset.card_eq_one.1 h
  have h1 : 1 ∈ s.divisors := by simp [hs0]
  have h2 : s ∈ s.divisors := by simp [hs0]
  rw [hd, Finset.mem_singleton] at h1 h2
  omega

/-- In a least number with `n` divisors, a prime factor `q` forces every smaller prime. -/
lemma swap {n m p q : ℕ} (hm : IsLeast {m : ℕ | m.divisors.card = n} m) (hm0 : m ≠ 0)
    (hq : q.Prime) (hqm : q ∣ m) (hp : p.Prime) (hpq : p < q) : p ∣ m := by
  by_contra hpm
  set e := m.factorization q
  set r := m / q ^ e
  have hmr : q ^ e * r = m := Nat.ordProj_mul_ordCompl_eq_self m q
  have hqr : ¬ q ∣ r := Nat.not_dvd_ordCompl hq hm0
  have hpr : ¬ p ∣ r := fun h => hpm (h.trans (Nat.ordCompl_dvd m q))
  have he : 1 ≤ e := (hq.dvd_iff_one_le_factorization hm0).1 hqm
  have hr0 : 0 < r := Nat.ordCompl_pos q hm0
  have hcard : (p ^ e * r).divisors.card = n := by
    rw [card_pow_mul hp hpr, ← card_pow_mul hq hqr, hmr]; exact hm.1
  have hlt : p ^ e * r < m := by
    rw [← hmr]
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hpq (by omega)) hr0
  have := hm.2 hcard
  omega

lemma isLeast (n : ℕ) (hn : 1 ≤ n) : IsLeast {m : ℕ | m.divisors.card = n} (A005179 n) := by
  have hne : ({m : ℕ | m.divisors.card = n} : Set ℕ).Nonempty :=
    ⟨2 ^ (n - 1), by show _ = n; rw [card_prime_pow Nat.prime_two]; omega⟩
  exact ⟨Nat.sInf_mem hne, fun x hx => Nat.sInf_le hx⟩

lemma third_eq_three {m : ℕ} (hm0 : m ≠ 0) (h2 : 2 ∣ m) (h3 : 3 ∣ m) : Nat.nth (· ∣ m) 2 = 3 := by
  have hc : Nat.count (· ∣ m) 3 = 2 := by simp [Nat.count_succ, hm0, h2]
  have := Nat.nth_count (p := (· ∣ m)) h3
  rwa [hc] at this

lemma third_eq_four {m : ℕ} (hm0 : m ≠ 0) (h2 : 2 ∣ m) (h3 : ¬ 3 ∣ m) (h4 : 4 ∣ m) :
    Nat.nth (· ∣ m) 2 = 4 := by
  have hc : Nat.count (· ∣ m) 4 = 2 := by simp [Nat.count_succ, hm0, h2, h3]
  have := Nat.nth_count (p := (· ∣ m)) h4
  rwa [hc] at this

end OMA_A171783_Proof

open OMA_A171783_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a171783.main := by
  intro n hn
  have hm := isLeast n (by omega)
  unfold a
  set m := A005179 n
  have hcard : m.divisors.card = n := hm.1
  have hm0 : m ≠ 0 := by rintro h; rw [h] at hcard; simp at hcard; omega
  have hm1 : m ≠ 1 := by rintro h; rw [h] at hcard; simp at hcard; omega
  -- 2 divides m
  have h2 : 2 ∣ m := by
    have hq := Nat.minFac_prime hm1
    rcases (hq.two_le).lt_or_eq with h | h
    · exact swap hm hm0 hq (Nat.minFac_dvd m) Nat.prime_two h
    · rw [h]; exact Nat.minFac_dvd m
  -- m = 2^a * s with s odd
  set a := m.factorization 2
  set s := m / 2 ^ a
  have hms : 2 ^ a * s = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have hs2 : ¬ 2 ∣ s := Nat.not_dvd_ordCompl Nat.prime_two hm0
  have hs0 : s ≠ 0 := (Nat.ordCompl_pos 2 hm0).ne'
  have ha : 1 ≤ a := (Nat.prime_two.dvd_iff_one_le_factorization hm0).1 h2
  have hn_eq : n = (a + 1) * s.divisors.card := by rw [← hcard, ← hms, card_pow_mul Nat.prime_two hs2]
  split_ifs with hp
  · -- n prime: s = 1, m = 2^a with a = n - 1 ≥ 2
    rw [hn_eq] at hp
    rcases Nat.prime_mul_iff.1 hp with ⟨_, h1⟩ | ⟨_, h1⟩
    · have hs1 : s = 1 := eq_one_of_card hs0 h1
      rw [hs1, mul_one] at hms
      rw [h1, mul_one] at hn_eq
      apply third_eq_four hm0 h2
      · rw [← hms]; intro h
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
          (Nat.prime_three.dvd_of_dvd_pow h)
        omega
      · rw [← hms, show a = 2 + (a - 2) by omega, pow_add]; exact Dvd.intro _ rfl
    · omega
  · -- n composite: 3 divides m
    apply third_eq_three hm0 h2
    by_cases hs1 : s = 1
    · exfalso
      rw [hs1, mul_one] at hms
      rw [hs1, Nat.divisors_one, Finset.card_singleton, mul_one] at hn_eq
      obtain ⟨x, hxn, hx2, hxlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hp
      obtain ⟨y, hy⟩ := hxn
      have hy2 : 2 ≤ y := by
        by_contra h; push Not at h; interval_cases y <;> simp_all
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      have h3 : ¬ 2 ∣ 3 ^ x' := fun h => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).1
          (Nat.prime_two.dvd_of_dvd_pow h)
        omega
      have hc : (2 ^ y' * 3 ^ x').divisors.card = n := by
        rw [card_pow_mul Nat.prime_two h3, card_prime_pow Nat.prime_three, hy]; ring
      have hle := hm.2 hc
      have hlt : 2 ^ y' * 3 ^ x' < m := by
        have hx' : x' ≠ 0 := by omega
        have h34 : 3 ^ x' < (2 ^ (y' + 1)) ^ x' :=
          Nat.pow_lt_pow_left (by
            calc 3 < 4 := by norm_num
              _ = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (y' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) hx'
        have hexp : a = y' + (y' + 1) * x' := by nlinarith
        rw [← hms, hexp, pow_add, pow_mul]
        exact Nat.mul_lt_mul_of_pos_left h34 (by positivity)
      omega
    · have hs1' : s ≠ 1 := hs1
      have hq := Nat.minFac_prime hs1'
      have hqs : s.minFac ∣ m := (Nat.minFac_dvd s).trans (Nat.ordCompl_dvd m 2)
      have hq2 : s.minFac ≠ 2 := fun h => hs2 (h ▸ Nat.minFac_dvd s)
      rcases Nat.lt_trichotomy s.minFac 3 with h | h | h
      · have := hq.two_le; omega
      · rw [← h]; exact hqs
      · exact swap hm hm0 hq hqs Nat.prime_three h
