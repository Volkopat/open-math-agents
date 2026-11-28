import OMAReductions.R_OeisA17666_conjecture_R1_H1_R1_H2_R1

-- No odd perfect number has exactly three distinct prime factors (Peirce 1832, Sylvester 1888).
-- Original Lean proof of the classical theorem. The divisor sum satisfies sigma(n) * prod (p - 1) <= n * prod p
-- over the primes dividing n, so a perfect n needs 2 * prod (p - 1) <= prod p; with a bound for products over
-- distinct odd numbers this forces the prime factors to be 3, 5 and r with r in {7, 11, 13}. Writing
-- n = 3^a 5^b r^c: sigma(n) = 2n with n odd makes a and c even and b odd (4 divides 1 + 3 + ... + 3^a for odd
-- a, similarly for r = 7, 11, and 7 divides sigma(13^c) for odd c). Then: r = 7 is abundant; r = 11 needs
-- a >= 4 (sigma(9) = 13) and is deficient for b = 1, abundant for b >= 3; r = 13 is deficient for b = 1 and
-- for a = 2, impossible for b = 3 (4 divides sigma(125)), a = 4 (sigma(81) = 121) and a = 6 (sigma(729) = 1093),
-- and abundant for a >= 8, b >= 5.
-- A classical case of the odd perfect number problem (at least ten prime factors are known to be needed,
-- Nielsen 2015), not progress on it.

namespace OMA.OPN3

open ArithmeticFunction Finset

lemma geom' (c : ℕ) : ∀ i : ℕ, (∑ k ∈ range (i + 1), (c + 1) ^ k) * c + 1 = (c + 1) ^ (i + 1) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have e : (c + 1) ^ (i + 1 + 1) = (c + 1) ^ (i + 1) * (c + 1) := pow_succ _ _
    rw [Finset.sum_range_succ, e]
    nlinarith [ih]

lemma geom (p : ℕ) (hp : 1 ≤ p) (i : ℕ) : (∑ k ∈ range (i + 1), p ^ k) * (p - 1) + 1 = p ^ (i + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
  simpa using geom' c i

/-- The abundancy bound: `σ(n) * ∏ (p - 1) ≤ n * ∏ p` over the primes dividing `n`. -/
lemma sigma_bound (n : ℕ) :
    sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, Finset.prod_singleton,
      sigma_one_apply_prime_pow hp]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h := geom p hp.one_lt.le (j + 1)
    have h2 : p ^ (j + 1 + 1) = p ^ (j + 1) * p := pow_succ p (j + 1)
    omega
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, hab.primeFactors_mul,
      Finset.prod_union hab.disjoint_primeFactors, Finset.prod_union hab.disjoint_primeFactors]
    calc sigma 1 a * sigma 1 b * ((∏ p ∈ a.primeFactors, (p - 1)) * ∏ p ∈ b.primeFactors, (p - 1))
        = (sigma 1 a * ∏ p ∈ a.primeFactors, (p - 1)) *
            (sigma 1 b * ∏ p ∈ b.primeFactors, (p - 1)) := by ring
      _ ≤ (a * ∏ p ∈ a.primeFactors, p) * (b * ∏ p ∈ b.primeFactors, p) :=
          Nat.mul_le_mul iha ihb
      _ = a * b * ((∏ p ∈ a.primeFactors, p) * ∏ p ∈ b.primeFactors, p) := by ring

/-- For distinct numbers `≥ c + 1` of the parity of `c + 1`:
`∏ p / (p - 1) ≤ ∏_{j < r} (c + 2j + 1) / (c + 2j)`. -/
lemma odd_prod_bound_from (c : ℕ) (s : Finset ℕ) :
    (∀ p ∈ s, c + 1 ≤ p ∧ p % 2 = (c + 1) % 2) →
    (∏ j ∈ range s.card, (c + 2 * j)) * ∏ p ∈ s, p ≤
      (∏ j ∈ range s.card, (c + 2 * j + 1)) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    have hans : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hs' : ∀ p ∈ s, c + 1 ≤ p ∧ p % 2 = (c + 1) % 2 :=
      fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have ha3 := hs a (Finset.mem_insert_self a s)
    have ih' := ih hs'
    have hmap : ∀ x ∈ s, (x - (c + 1)) / 2 ∈ range ((a - (c + 1)) / 2) := by
      intro x hx
      have h1 := hs' x hx
      have h2 := ha x hx
      rw [Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun x : ℕ => (x - (c + 1)) / 2) (s : Set ℕ) := by
      intro x hx y hy hxy
      have h1 := hs' x hx
      have h2 := hs' y hy
      simp only at hxy
      omega
    have hcard : s.card ≤ (a - (c + 1)) / 2 := by
      have h := Finset.card_le_card_of_injOn (fun x : ℕ => (x - (c + 1)) / 2) hmap hinj
      rwa [Finset.card_range] at h
    have hstep : (c + 2 * s.card) * a ≤ (c + 2 * s.card + 1) * (a - 1) := by
      obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h3 : c + 2 * s.card ≤ d := by omega
      nlinarith
    rw [Finset.card_insert_of_notMem hans, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_insert hans, Finset.prod_insert hans]
    calc (∏ j ∈ range s.card, (c + 2 * j)) * (c + 2 * s.card) * (a * ∏ p ∈ s, p)
        = ((∏ j ∈ range s.card, (c + 2 * j)) * ∏ p ∈ s, p) * ((c + 2 * s.card) * a) := by ring
      _ ≤ ((∏ j ∈ range s.card, (c + 2 * j + 1)) * ∏ p ∈ s, (p - 1)) *
            ((c + 2 * s.card + 1) * (a - 1)) := Nat.mul_le_mul ih' hstep
      _ = (∏ j ∈ range s.card, (c + 2 * j + 1)) * (c + 2 * s.card + 1) *
            ((a - 1) * ∏ p ∈ s, (p - 1)) := by ring

/-- `S p a = 1 + p + ... + p^a`, the divisor sum of `p^a`. -/
def S (p a : ℕ) : ℕ := ∑ i ∈ range (a + 1), p ^ i

lemma S_succ (p a : ℕ) : S p (a + 1) = p * S p a + 1 := by
  unfold S
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ']

lemma S_upper (p a : ℕ) (hp : 1 ≤ p) : S p a * (p - 1) + 1 = p * p ^ a := by
  have h := geom p hp a
  rw [pow_succ'] at h
  exact h

lemma S_lower (p k : ℕ) : ∀ d : ℕ, S p k * p ^ (k + d) ≤ S p (k + d) * p ^ k := by
  intro d
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
    rw [← add_assoc, S_succ, pow_succ]
    nlinarith [Nat.mul_le_mul_right p ih, Nat.zero_le (p ^ k)]

lemma S_odd_dvd (p : ℕ) : ∀ m : ℕ, (p + 1) ∣ S p (2 * m + 1) := by
  intro m
  induction m with
  | zero =>
    have h : S p (2 * 0 + 1) = p + 1 := by
      simp [S, Finset.sum_range_succ]
      ring
    rw [h]
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    rw [e, S_succ, S_succ]
    obtain ⟨t, ht⟩ := ih
    exact ⟨p * p * t + 1, by rw [ht]; ring⟩

lemma S_parity (p a : ℕ) (hp : p % 2 = 1) : S p a % 2 = (a + 1) % 2 := by
  induction a with
  | zero => simp [S]
  | succ a ih =>
    rw [S_succ]
    have h1 : (p * S p a) % 2 = S p a % 2 := by
      rw [Nat.mul_mod, hp]
      simp
    omega

lemma sigma_pp (p a : ℕ) (hp : p.Prime) : sigma 1 (p ^ a) = S p a :=
  sigma_one_apply_prime_pow hp

/-- A prime `q` other than `2, 3, 5, r` does not divide `2 * (3^a * (5^b * r^c))`. -/
lemma not_dvd_form (q r a b c : ℕ) (hq : q.Prime) (h2 : ¬ q ∣ 2) (h3 : ¬ q ∣ 3) (h5 : ¬ q ∣ 5)
    (hr : ¬ q ∣ r) : ¬ q ∣ 2 * (3 ^ a * (5 ^ b * r ^ c)) := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact h2 h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact h3 (hq.dvd_of_dvd_pow h)
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact h5 (hq.dvd_of_dvd_pow h)
  · exact hr (hq.dvd_of_dvd_pow h)

/-- The size contradiction from three lower bounds. -/
lemma too_big {s3 s5 sr X Y Z A B C a' b' c' : ℕ} (hX : 0 < X * (Y * Z))
    (h3 : A * X ≤ s3 * a') (h5 : B * Y ≤ s5 * b') (hr : C * Z ≤ sr * c')
    (hs : s3 * (s5 * sr) = 2 * (X * (Y * Z))) (hnum : 2 * (a' * b' * c') < A * B * C) : False := by
  have h1 := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) hr
  have e1 : s3 * a' * (s5 * b') * (sr * c') = (a' * b' * c') * (s3 * (s5 * sr)) := by ring
  have e2 : A * X * (B * Y) * (C * Z) = (A * B * C) * (X * (Y * Z)) := by ring
  rw [e1, e2, hs] at h1
  have h2 : 2 * (a' * b' * c') * (X * (Y * Z)) < A * B * C * (X * (Y * Z)) :=
    Nat.mul_lt_mul_of_pos_right hnum hX
  have e3 : a' * b' * c' * (2 * (X * (Y * Z))) = 2 * (a' * b' * c') * (X * (Y * Z)) := by ring
  rw [e3] at h1
  omega

/-- The size contradiction from two strict upper bounds, the third factor being known. -/
lemma too_small {su sv U V a' b' k m : ℕ}
    (hu : su * a' < k * U) (hv : sv * b' < m * V)
    (hs : su * sv * (a' * b') ≥ k * m * (U * V)) : False := by
  have h1 := Nat.mul_lt_mul'' hu hv
  have e1 : su * a' * (sv * b') = su * sv * (a' * b') := by ring
  have e2 : k * U * (m * V) = k * m * (U * V) := by ring
  rw [e1, e2] at h1
  omega

theorem three_primes (n : ℕ) (hodd : Odd n) (hs : sigma 1 n = 2 * n) : n.primeFactors.card ≠ 3 := by
  intro hcard
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hn0 : n ≠ 0 := by omega
  have hpos : 0 < n := by omega
  -- the basic inequality 2 * ∏ (p - 1) ≤ ∏ p
  have hbound := sigma_bound n
  rw [hs] at hbound
  have hkey : 2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ p ∈ n.primeFactors, p := by
    have h2 : n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) ≤ n * ∏ p ∈ n.primeFactors, p := by
      calc n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) = 2 * n * ∏ p ∈ n.primeFactors, (p - 1) := by ring
        _ ≤ _ := hbound
    exact Nat.le_of_mul_le_mul_left h2 hpos
  have hge : ∀ p ∈ n.primeFactors, p.Prime ∧ 3 ≤ p ∧ p % 2 = 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpo : p % 2 = 1 := by
      obtain ⟨d, hd⟩ := hpd
      by_contra hne
      have hpe : p % 2 = 0 := by omega
      have : (p * d) % 2 = 0 := by rw [Nat.mul_mod, hpe]; simp
      omega
    have h2 := hpp.two_le
    exact ⟨hpp, by omega, hpo⟩
  have hQpos : ∀ t : Finset ℕ, t ⊆ n.primeFactors → 0 < ∏ p ∈ t, (p - 1) := by
    intro t ht
    exact Finset.prod_pos fun p hp => by have := (hge p (ht hp)).2.1; omega
  -- 3 is a prime factor
  have h3 : 3 ∈ n.primeFactors := by
    by_contra h3
    have hb := odd_prod_bound_from 4 n.primeFactors (fun p hp => by
      have h := hge p hp
      have hne : p ≠ 3 := fun e => h3 (e ▸ hp)
      exact ⟨by omega, by omega⟩)
    rw [hcard] at hb
    simp [Finset.prod_range_succ] at hb
    have hq := hQpos n.primeFactors (Finset.Subset.refl _)
    omega
  -- 5 is a prime factor
  have hP3 := Finset.mul_prod_erase n.primeFactors (fun p => p) h3
  have hQ3 := Finset.mul_prod_erase n.primeFactors (fun p => p - 1) h3
  have hcard3 : (n.primeFactors.erase 3).card = 2 := by
    rw [Finset.card_erase_of_mem h3, hcard]
  have h5 : 5 ∈ n.primeFactors.erase 3 := by
    by_contra h5
    have hb := odd_prod_bound_from 6 (n.primeFactors.erase 3) (fun p hp => by
      have hp' := Finset.mem_of_mem_erase hp
      have h := hge p hp'
      have hne3 : p ≠ 3 := Finset.ne_of_mem_erase hp
      have hne5 : p ≠ 5 := fun e => h5 (e ▸ hp)
      exact ⟨by omega, by omega⟩)
    rw [hcard3] at hb
    simp [Finset.prod_range_succ] at hb
    have hq := hQpos (n.primeFactors.erase 3) (Finset.erase_subset _ _)
    omega
  -- the third prime
  have hP5 := Finset.mul_prod_erase (n.primeFactors.erase 3) (fun p => p) h5
  have hQ5 := Finset.mul_prod_erase (n.primeFactors.erase 3) (fun p => p - 1) h5
  have hcard5 : ((n.primeFactors.erase 3).erase 5).card = 1 := by
    rw [Finset.card_erase_of_mem h5, hcard3]
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard5
  have hrmem : r ∈ (n.primeFactors.erase 3).erase 5 := by rw [hr]; exact Finset.mem_singleton_self r
  have hr5 : r ≠ 5 := Finset.ne_of_mem_erase hrmem
  have hrmem' := Finset.mem_of_mem_erase hrmem
  have hr3 : r ≠ 3 := Finset.ne_of_mem_erase hrmem'
  have hrge := hge r (Finset.mem_of_mem_erase hrmem')
  have hr16 : r ≤ 16 := by
    rw [hr, Finset.prod_singleton] at hP5 hQ5
    have h7 : 7 ≤ r := by omega
    obtain ⟨e, rfl⟩ : ∃ e, r = e + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hQ5
    omega
  have hpf : n.primeFactors = {3, 5, r} := by
    rw [← Finset.insert_erase h3, ← Finset.insert_erase h5, hr]
  have hrcases : r = 7 ∨ r = 11 ∨ r = 13 := by
    have hrp := hrge.1
    have h7 : 7 ≤ r := by omega
    interval_cases r <;> first | omega | (exfalso; revert hrp; norm_num)
  -- the factorization
  have hfac : n = 3 ^ n.factorization 3 * (5 ^ n.factorization 5 * r ^ n.factorization r) := by
    have h := Nat.prod_factorization_pow_eq_self hn0
    rw [Nat.prod_factorization_eq_prod_primeFactors, hpf, Finset.prod_insert (by simp [hr3.symm]),
      Finset.prod_insert (by simp [hr5.symm]), Finset.prod_singleton] at h
    exact h.symm
  have ha0 : 0 < n.factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three hn0 (Nat.dvd_of_mem_primeFactors h3)
  have hb0 : 0 < n.factorization 5 :=
    Nat.Prime.factorization_pos_of_dvd (by norm_num) hn0
      (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase h5))
  have hc0 : 0 < n.factorization r :=
    Nat.Prime.factorization_pos_of_dvd hrge.1 hn0
      (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hrmem'))
  generalize n.factorization 3 = a at hfac ha0
  generalize n.factorization 5 = b at hfac hb0
  generalize n.factorization r = c at hfac hc0
  have p5 : Nat.Prime 5 := by norm_num
  have c35 : Nat.Coprime 3 5 := by decide
  have c3r : Nat.Coprime 3 r := (Nat.coprime_primes Nat.prime_three hrge.1).mpr hr3.symm
  have c5r : Nat.Coprime 5 r := (Nat.coprime_primes p5 hrge.1).mpr hr5.symm
  have hsig : S 3 a * (S 5 b * S r c) = 2 * (3 ^ a * (5 ^ b * r ^ c)) := by
    have h1 : Nat.Coprime (3 ^ a) (5 ^ b * r ^ c) :=
      Nat.Coprime.pow_left a (Nat.Coprime.mul_right (c35.pow_right b) (c3r.pow_right c))
    have h2 : Nat.Coprime (5 ^ b) (r ^ c) := Nat.Coprime.pow b c c5r
    rw [← sigma_pp 3 a Nat.prime_three, ← sigma_pp 5 b p5, ← sigma_pp r c hrge.1,
      ← isMultiplicative_sigma.map_mul_of_coprime h2, ← isMultiplicative_sigma.map_mul_of_coprime h1,
      ← hfac]
    exact hs
  have hXYZ : 0 < 3 ^ a * (5 ^ b * r ^ c) := by rw [← hfac]; exact hpos
  have hform2 : (3 ^ a * (5 ^ b * r ^ c)) % 2 = 1 := by rw [← hfac]; exact hn2
  -- a is even
  have ha_even : a % 2 = 0 := by
    by_contra hne
    obtain ⟨m, rfl⟩ : ∃ m, a = 2 * m + 1 := ⟨a / 2, by omega⟩
    obtain ⟨t, ht⟩ := S_odd_dvd 3 m
    rw [ht] at hsig
    have e : (3 + 1) * t * (S 5 b * S r c) = 4 * (t * (S 5 b * S r c)) := by ring
    rw [e] at hsig
    omega
  -- c is even
  have hc_even : c % 2 = 0 := by
    by_contra hne
    obtain ⟨m, rfl⟩ : ∃ m, c = 2 * m + 1 := ⟨c / 2, by omega⟩
    obtain ⟨t, ht⟩ := S_odd_dvd r m
    rw [ht] at hsig
    rcases hrcases with rfl | rfl | rfl
    · have e : S 3 a * (S 5 b * ((7 + 1) * t)) = 4 * (2 * (S 3 a * (S 5 b * t))) := by ring
      rw [e] at hsig
      omega
    · have e : S 3 a * (S 5 b * ((11 + 1) * t)) = 4 * (3 * (S 3 a * (S 5 b * t))) := by ring
      rw [e] at hsig
      omega
    · have hd : 7 ∣ 2 * (3 ^ a * (5 ^ b * 13 ^ (2 * m + 1))) := by
        rw [← hsig]
        exact ⟨S 3 a * (S 5 b * (2 * t)), by ring⟩
      exact not_dvd_form 7 13 a b (2 * m + 1) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hd
  have h3par := S_parity 3 a (by norm_num)
  have hrpar := S_parity r c hrge.2.2
  -- b is odd
  have hb_odd : b % 2 = 1 := by
    by_contra hne
    have h5par := S_parity 5 b (by norm_num)
    have hprod : (S 3 a * (S 5 b * S r c)) % 2 = 1 := by
      rw [Nat.mul_mod, Nat.mul_mod (S 5 b), h3par, h5par, hrpar]
      have e1 : (a + 1) % 2 = 1 := by omega
      have e2 : (b + 1) % 2 = 1 := by omega
      have e3 : (c + 1) % 2 = 1 := by omega
      rw [e1, e2, e3]
    omega
  have ha2 : 2 ≤ a := by omega
  have hc2 : 2 ≤ c := by omega
  have v32 : S 3 2 = 13 := by decide
  have v51 : S 5 1 = 6 := by decide
  have l3 := S_lower 3 2 (a - 2)
  rw [show 2 + (a - 2) = a by omega, v32] at l3
  have l5 := S_lower 5 1 (b - 1)
  rw [show 1 + (b - 1) = b by omega, v51] at l5
  rcases hrcases with rfl | rfl | rfl
  · -- r = 7 : abundant
    have v72 : S 7 2 = 57 := by decide
    have l7 := S_lower 7 2 (c - 2)
    rw [show 2 + (c - 2) = c by omega, v72] at l7
    exact too_big hXYZ l3 l5 l7 hsig (by norm_num)
  · -- r = 11
    have v112 : S 11 2 = 133 := by decide
    have l11 := S_lower 11 2 (c - 2)
    rw [show 2 + (c - 2) = c by omega, v112] at l11
    by_cases ha : a = 2
    · subst ha
      have hd : 13 ∣ 2 * (3 ^ 2 * (5 ^ b * 11 ^ c)) := by
        rw [← hsig, v32]
        exact ⟨S 5 b * S 11 c, rfl⟩
      exact not_dvd_form 13 11 2 b c (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hd
    have ha4 : 4 ≤ a := by omega
    have v34 : S 3 4 = 121 := by decide
    have l34 := S_lower 3 4 (a - 4)
    rw [show 4 + (a - 4) = a by omega, v34] at l34
    by_cases hb : b = 1
    · subst hb
      rw [v51] at hsig
      have u3 := S_upper 3 a (by norm_num)
      have u11 := S_upper 11 c (by norm_num)
      refine too_small (su := S 3 a) (sv := S 11 c) (U := 3 ^ a) (V := 11 ^ c) (a' := 2) (b' := 10)
        (k := 3) (m := 11) (by omega) (by omega) ?_
      have e1 : S 3 a * (6 * S 11 c) = 6 * (S 3 a * S 11 c) := by ring
      have e2 : 2 * (3 ^ a * (5 ^ 1 * 11 ^ c)) = 10 * (3 ^ a * 11 ^ c) := by ring
      rw [e1, e2] at hsig
      omega
    · have hb3 : 3 ≤ b := by omega
      have v53 : S 5 3 = 156 := by decide
      have l53 := S_lower 5 3 (b - 3)
      rw [show 3 + (b - 3) = b by omega, v53] at l53
      exact too_big hXYZ l34 l53 l11 hsig (by norm_num)
  · -- r = 13
    have v132 : S 13 2 = 183 := by decide
    have l13 := S_lower 13 2 (c - 2)
    rw [show 2 + (c - 2) = c by omega, v132] at l13
    have u13 := S_upper 13 c (by norm_num)
    by_cases hb : b = 1
    · subst hb
      rw [v51] at hsig
      have u3 := S_upper 3 a (by norm_num)
      refine too_small (su := S 3 a) (sv := S 13 c) (U := 3 ^ a) (V := 13 ^ c) (a' := 2) (b' := 12)
        (k := 3) (m := 13) (by omega) (by omega) ?_
      have e1 : S 3 a * (6 * S 13 c) = 6 * (S 3 a * S 13 c) := by ring
      have e2 : 2 * (3 ^ a * (5 ^ 1 * 13 ^ c)) = 10 * (3 ^ a * 13 ^ c) := by ring
      rw [e1, e2] at hsig
      omega
    by_cases hb3 : b = 3
    · subst hb3
      have v53 : S 5 3 = 156 := by decide
      rw [v53] at hsig
      have e : S 3 a * (156 * S 13 c) = 4 * (39 * (S 3 a * S 13 c)) := by ring
      rw [e] at hsig
      omega
    have hb5 : 5 ≤ b := by omega
    have v55 : S 5 5 = 3906 := by decide
    have l55 := S_lower 5 5 (b - 5)
    rw [show 5 + (b - 5) = b by omega, v55] at l55
    by_cases ha : a = 2
    · subst ha
      rw [v32] at hsig
      have u5 := S_upper 5 b (by norm_num)
      refine too_small (su := S 5 b) (sv := S 13 c) (U := 5 ^ b) (V := 13 ^ c) (a' := 4) (b' := 12)
        (k := 5) (m := 13) (by omega) (by omega) ?_
      have e1 : 13 * (S 5 b * S 13 c) = 13 * (S 5 b * S 13 c) := rfl
      have e2 : 2 * (3 ^ 2 * (5 ^ b * 13 ^ c)) = 18 * (5 ^ b * 13 ^ c) := by ring
      rw [e2] at hsig
      omega
    by_cases ha4 : a = 4
    · subst ha4
      have v34 : S 3 4 = 121 := by decide
      have hd : 11 ∣ 2 * (3 ^ 4 * (5 ^ b * 13 ^ c)) := by
        rw [← hsig, v34]
        exact ⟨11 * (S 5 b * S 13 c), by ring⟩
      exact not_dvd_form 11 13 4 b c (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hd
    by_cases ha6 : a = 6
    · subst ha6
      have v36 : S 3 6 = 1093 := by decide
      have hd : 1093 ∣ 2 * (3 ^ 6 * (5 ^ b * 13 ^ c)) := by
        rw [← hsig, v36]
        exact ⟨S 5 b * S 13 c, rfl⟩
      exact not_dvd_form 1093 13 6 b c (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hd
    have ha8 : 8 ≤ a := by omega
    have v38 : S 3 8 = 9841 := by decide
    have l38 := S_lower 3 8 (a - 8)
    rw [show 8 + (a - 8) = a by omega, v38] at l38
    exact too_big hXYZ l38 l55 l13 hsig (by norm_num)

end OMA.OPN3

theorem OMA.solution : OMA.R_OeisA17666_conjecture_R1_H1_R1_H2_R1.H1 := by
  intro b _ hodd hc hs
  exact OMA.OPN3.three_primes b hodd hs hc
