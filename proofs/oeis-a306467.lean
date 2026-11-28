import OMAStatements.S_oeis_a306467

-- Problem: A306467: Let S(n)_k be the smallest positive integer t that t!_k is a multiple of n (t!_k is k-tuple factorial of t); then a(n) is the smallest k for which S(n)_k = n.
-- Upstream: formal-conjectures statements/oeis-a306467.lean:0 (declaration OMA.S_oeis_a306467.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: a prime P has S(P)_1 = P, so a(P) = 1; also a(4) = 1. For an odd prime q,
-- S(2q)_1 <= q (2 and q divide q!), and S(2q)_2 = 2q (for odd t the product t!_2 is odd, for
-- even t < 2q no factor is a multiple of q), so a(2q) = 2. For a composite m, two distinct even
-- numbers at most 2m - 2 have a product divisible by 2m, so S(2m)_2 < 2m and a(2m) is not 2.
-- For a prime r >= 5, S(3r)_1 <= r, S(3r)_2 <= r (3 and r are odd) and S(3r)_3 = 3r, so
-- a(3r) = 3. For an odd composite n that is not 3 times a prime, two distinct numbers in one
-- residue class mod 3, both below n, have a product divisible by n, so S(n)_3 < n.

namespace H03A306467

open OMA.S_oeis_a306467

theorem mem_set (k t j : ℕ) : j ∈ (Finset.Icc 1 t).filter (fun j => j % k = t % k) ↔
    1 ≤ j ∧ j ≤ t ∧ j % k = t % k := by
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem dvd_one (k t j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ t) (h3 : j % k = t % k) :
    j ∣ mfact k t :=
  Finset.dvd_prod_of_mem (fun j => j) ((mem_set k t j).2 ⟨h1, h2, h3⟩)

theorem dvd_two (k t x y : ℕ) (hxy : x ≠ y) (hx1 : 1 ≤ x) (hx2 : x ≤ t) (hx3 : x % k = t % k)
    (hy1 : 1 ≤ y) (hy2 : y ≤ t) (hy3 : y % k = t % k) : x * y ∣ mfact k t := by
  have hsub : ({x, y} : Finset ℕ) ⊆ (Finset.Icc 1 t).filter (fun j => j % k = t % k) := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj
    · rw [hj]
      exact (mem_set k t x).2 ⟨hx1, hx2, hx3⟩
    · rw [hj]
      exact (mem_set k t y).2 ⟨hy1, hy2, hy3⟩
  have h := Finset.prod_dvd_prod_of_subset _ _ (fun j => j) hsub
  rw [Finset.prod_pair hxy] at h
  exact h

theorem S_le (n k t : ℕ) (ht : 0 < t) (hd : n ∣ mfact k t) : S n k ≤ t := by
  have hmem : t ∈ {t | 0 < t ∧ n ∣ mfact k t} := show 0 < t ∧ n ∣ mfact k t from ⟨ht, hd⟩
  exact Nat.sInf_le hmem

theorem S_eq (n k : ℕ) (hn : 0 < n) (hd : n ∣ mfact k n)
    (hlow : ∀ t, 0 < t → t < n → ¬ n ∣ mfact k t) : S n k = n := by
  have hmem : n ∈ {t | 0 < t ∧ n ∣ mfact k t} := show 0 < n ∧ n ∣ mfact k n from ⟨hn, hd⟩
  apply le_antisymm (S_le n k n hn hd)
  show n ≤ sInf {t | 0 < t ∧ n ∣ mfact k t}
  refine le_csInf ⟨n, hmem⟩ ?_
  intro t ht
  have ht' : 0 < t ∧ n ∣ mfact k t := ht
  rcases Nat.lt_or_ge t n with h | h
  · exact absurd ht'.2 (hlow t ht'.1 h)
  · exact h

theorem a_eq (n k0 : ℕ) (hk0 : 0 < k0) (hS : S n k0 = n)
    (hlow : ∀ k, 0 < k → k < k0 → S n k ≠ n) : a n = k0 := by
  have hmem : k0 ∈ {k | 0 < k ∧ S n k = n} := show 0 < k0 ∧ S n k0 = n from ⟨hk0, hS⟩
  show sInf {k | 0 < k ∧ S n k = n} = k0
  apply le_antisymm (Nat.sInf_le hmem)
  refine le_csInf ⟨k0, hmem⟩ ?_
  intro k hk
  have hk' : 0 < k ∧ S n k = n := hk
  rcases Nat.lt_or_ge k k0 with h | h
  · exact absurd hk'.2 (hlow k hk'.1 h)
  · exact h

theorem a_spec (n k : ℕ) (h : a n = k) (hk : k ≠ 0) : S n k = n := by
  have hne : {k | 0 < k ∧ S n k = n}.Nonempty := by
    rcases Set.eq_empty_or_nonempty {k | 0 < k ∧ S n k = n} with he | he
    · exfalso
      apply hk
      rw [← h]
      show sInf {k | 0 < k ∧ S n k = n} = 0
      rw [he, Nat.sInf_empty]
    · exact he
  have hm : 0 < a n ∧ S n (a n) = n := Nat.sInf_mem hne
  rw [h] at hm
  exact hm.2

theorem comp_split (m : ℕ) (hm : 2 ≤ m) (hp : ¬ m.Prime) :
    ∃ u v, u.Prime ∧ u ≤ v ∧ m = u * v := by
  have hq : (Nat.minFac m).Prime := Nat.minFac_prime (by omega)
  obtain ⟨b, hb⟩ := Nat.minFac_dvd m
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < m) hp
  refine ⟨Nat.minFac m, b, hq, ?_, hb⟩
  have h2 : Nat.minFac m * Nat.minFac m ≤ Nat.minFac m * b := by
    rw [← pow_two, ← hb]
    exact hsq
  exact Nat.le_of_mul_le_mul_left h2 hq.pos

theorem S_prime (P : ℕ) (hP : P.Prime) : S P 1 = P := by
  apply S_eq P 1 hP.pos (dvd_one 1 P P hP.one_lt.le le_rfl rfl)
  intro t _ht htP hd
  have hd' : P ∣ ∏ j ∈ (Finset.Icc 1 t).filter (fun j => j % 1 = t % 1), j := hd
  rw [Prime.dvd_finsetProd_iff hP.prime] at hd'
  obtain ⟨j, hj, hPj⟩ := hd'
  rw [mem_set] at hj
  have h1 := Nat.le_of_dvd (by omega) hPj
  omega

theorem a_prime (P : ℕ) (hP : P.Prime) : a P = 1 :=
  a_eq P 1 (by norm_num) (S_prime P hP) (fun k hk hk1 => by omega)

theorem S_four : S 4 1 = 4 := by
  apply S_eq 4 1 (by norm_num) (dvd_one 1 4 4 (by norm_num) le_rfl rfl)
  intro t ht ht4
  interval_cases t <;> decide

theorem a_four : a 4 = 1 :=
  a_eq 4 1 (by norm_num) S_four (fun k hk hk1 => by omega)

theorem S_2q (q : ℕ) (hq : q.Prime) (hq3 : 3 ≤ q) : S (2 * q) 2 = 2 * q := by
  have hqodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by omega)
  apply S_eq (2 * q) 2 (by omega) (dvd_one 2 (2 * q) (2 * q) (by omega) le_rfl rfl)
  intro t _ht htq hd
  have hd' : 2 * q ∣ ∏ j ∈ (Finset.Icc 1 t).filter (fun j => j % 2 = t % 2), j := hd
  rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
  · have hqd : q ∣ ∏ j ∈ (Finset.Icc 1 t).filter (fun j => j % 2 = t % 2), j :=
      dvd_trans (dvd_mul_left q 2) hd'
    rw [Prime.dvd_finsetProd_iff hq.prime] at hqd
    obtain ⟨j, hj, hqj⟩ := hqd
    rw [mem_set] at hj
    obtain ⟨c, hc⟩ := hqj
    have hlt : q * c < q * 2 := by omega
    have hc2 : c < 2 := Nat.lt_of_mul_lt_mul_left hlt
    interval_cases c <;> omega
  · have h2d : 2 ∣ ∏ j ∈ (Finset.Icc 1 t).filter (fun j => j % 2 = t % 2), j :=
      dvd_trans (dvd_mul_right 2 q) hd'
    rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime] at h2d
    obtain ⟨j, hj, h2j⟩ := h2d
    rw [mem_set] at hj
    omega

theorem a_2q (q : ℕ) (hq : q.Prime) (hq3 : 3 ≤ q) : a (2 * q) = 2 := by
  apply a_eq (2 * q) 2 (by norm_num) (S_2q q hq hq3)
  intro k hk hk2
  have hk1 : k = 1 := by omega
  subst hk1
  have h := S_le (2 * q) 1 q (by omega)
    (dvd_two 1 q 2 q (by omega) (by norm_num) (by omega) (by omega) (by omega) le_rfl rfl)
  omega

theorem S_2m (m : ℕ) (hm : 2 ≤ m) (hp : ¬ m.Prime) : S (2 * m) 2 < 2 * m := by
  obtain ⟨u, v, hu, huv, rfl⟩ := comp_split m hm hp
  have hu2 := hu.two_le
  rcases Nat.lt_or_ge u v with h | h
  · have hd := dvd_two 2 (2 * v) (2 * u) (2 * v) (by omega) (by omega) (by omega) (by omega)
      (by omega) le_rfl rfl
    have h4 : 2 * (u * v) ∣ 2 * u * (2 * v) := ⟨2, by ring⟩
    have hS := S_le (2 * (u * v)) 2 (2 * v) (by omega) (dvd_trans h4 hd)
    have hm2 := Nat.mul_le_mul_right v hu2
    omega
  · have huv' : u = v := le_antisymm huv h
    rw [← huv']
    rcases Nat.lt_or_ge u 3 with h3 | h3
    · have hu' : u = 2 := by omega
      subst hu'
      show S (2 * 4) 2 < 2 * 4
      have hd := dvd_two 2 4 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) le_rfl rfl
      have hS := S_le (2 * 4) 2 4 (by norm_num) hd
      omega
    · have hd := dvd_two 2 (4 * u) (2 * u) (4 * u) (by omega) (by omega) (by omega) (by omega)
        (by omega) le_rfl rfl
      have h8 : 2 * (u * u) ∣ 2 * u * (4 * u) := ⟨4, by ring⟩
      have hS := S_le (2 * (u * u)) 2 (4 * u) (by omega) (dvd_trans h8 hd)
      have hm3 := Nat.mul_le_mul_right u h3
      omega

theorem S_3r (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) : S (3 * r) 3 = 3 * r := by
  have hr3 : r % 3 ≠ 0 := by
    intro h
    have h3 : 3 ∣ r := Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 h3
    omega
  apply S_eq (3 * r) 3 (by omega) (dvd_one 3 (3 * r) (3 * r) (by omega) le_rfl rfl)
  intro t _ht htr hd
  have hd' : 3 * r ∣ ∏ j ∈ (Finset.Icc 1 t).filter (fun j => j % 3 = t % 3), j := hd
  by_cases ht3 : t % 3 = 0
  · have hrd : r ∣ ∏ j ∈ (Finset.Icc 1 t).filter (fun j => j % 3 = t % 3), j :=
      dvd_trans (dvd_mul_left r 3) hd'
    rw [Prime.dvd_finsetProd_iff hr.prime] at hrd
    obtain ⟨j, hj, hrj⟩ := hrd
    rw [mem_set] at hj
    obtain ⟨c, hc⟩ := hrj
    have hlt : r * c < r * 3 := by omega
    have hc3 : c < 3 := Nat.lt_of_mul_lt_mul_left hlt
    interval_cases c <;> omega
  · have h3d : 3 ∣ ∏ j ∈ (Finset.Icc 1 t).filter (fun j => j % 3 = t % 3), j :=
      dvd_trans (dvd_mul_right 3 r) hd'
    rw [Prime.dvd_finsetProd_iff Nat.prime_three.prime] at h3d
    obtain ⟨j, hj, h3j⟩ := h3d
    rw [mem_set] at hj
    omega

theorem a_3r (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) : a (3 * r) = 3 := by
  have hodd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by omega)
  apply a_eq (3 * r) 3 (by norm_num) (S_3r r hr hr5)
  intro k hk hk3
  rcases (by omega : k = 1 ∨ k = 2) with hk' | hk'
  · subst hk'
    have h := S_le (3 * r) 1 r (by omega)
      (dvd_two 1 r 3 r (by omega) (by norm_num) (by omega) (by omega) (by omega) le_rfl rfl)
    omega
  · subst hk'
    have h := S_le (3 * r) 2 r (by omega)
      (dvd_two 2 r 3 r (by omega) (by norm_num) (by omega) (by omega) (by omega) le_rfl rfl)
    omega

theorem mod3_aux (u v : ℕ) (hu3 : u % 3 ≠ 0) (hv3 : v % 3 ≠ 0) (hc : ¬ u % 3 = v % 3) :
    (2 * u) % 3 = v % 3 := by
  have hu' : u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases hu' with h1 | h1
  · have hv' : v % 3 = 2 := by omega
    rw [hv']
    omega
  · have hv' : v % 3 = 1 := by omega
    rw [hv']
    omega

theorem S_odd_comp (n : ℕ) (hn : 2 ≤ n) (hodd : n % 2 = 1) (hp : ¬ n.Prime)
    (h3 : ¬ (3 ∣ n ∧ (n / 3).Prime)) : S n 3 < n := by
  by_cases h3n : 3 ∣ n
  · obtain ⟨m, rfl⟩ := h3n
    have hm : ¬ m.Prime := by
      intro hmp
      apply h3
      refine ⟨⟨m, rfl⟩, ?_⟩
      rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 3)]
      exact hmp
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have h01 : m = 0 ∨ m = 1 := by omega
      rcases h01 with h0 | h1
      · subst h0
        omega
      · subst h1
        exact hp (by norm_num)
    obtain ⟨u, v, hu, huv, rfl⟩ := comp_split m hm2 hm
    have hu2 := hu.two_le
    have huodd : u % 2 = 1 := by
      by_contra hev
      have h2u : 2 ∣ u := Nat.dvd_of_mod_eq_zero (by omega)
      have h2uv' : 2 ∣ u * v := Dvd.dvd.mul_right h2u v
      have h2uv : 2 ∣ 3 * (u * v) := Dvd.dvd.mul_left h2uv' 3
      omega
    rcases Nat.lt_or_ge u v with h | h
    · have hd := dvd_two 3 (3 * v) (3 * u) (3 * v) (by omega) (by omega) (by omega) (by omega)
        (by omega) le_rfl rfl
      have h9 : 3 * (u * v) ∣ 3 * u * (3 * v) := ⟨3, by ring⟩
      have hS := S_le (3 * (u * v)) 3 (3 * v) (by omega) (dvd_trans h9 hd)
      have hm3 := Nat.mul_le_mul_right v hu2
      omega
    · have huv' : u = v := le_antisymm huv h
      rw [← huv']
      have hu3 : 3 ≤ u := by omega
      have hd := dvd_two 3 (6 * u) (3 * u) (6 * u) (by omega) (by omega) (by omega) (by omega)
        (by omega) le_rfl rfl
      have h18 : 3 * (u * u) ∣ 3 * u * (6 * u) := ⟨6, by ring⟩
      have hS := S_le (3 * (u * u)) 3 (6 * u) (by omega) (dvd_trans h18 hd)
      have hm3 := Nat.mul_le_mul_right u hu3
      omega
  · obtain ⟨u, v, hu, huv, rfl⟩ := comp_split n hn hp
    have hu2 := hu.two_le
    have huodd : u % 2 = 1 := by
      by_contra hev
      have h2u : 2 ∣ u := Nat.dvd_of_mod_eq_zero (by omega)
      have h2 : 2 ∣ u * v := Dvd.dvd.mul_right h2u v
      omega
    have hvodd : v % 2 = 1 := by
      by_contra hev
      have h2v : 2 ∣ v := Nat.dvd_of_mod_eq_zero (by omega)
      have h2 : 2 ∣ u * v := Dvd.dvd.mul_left h2v u
      omega
    have hu3 : u % 3 ≠ 0 := by
      intro h0
      exact h3n (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h0) v)
    have hv3 : v % 3 ≠ 0 := by
      intro h0
      exact h3n (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h0) u)
    have hu5 : 5 ≤ u := by omega
    have hv5 : 5 ≤ v := by omega
    have hA := Nat.mul_le_mul_right v hu5
    have hB := Nat.mul_le_mul_left u hv5
    by_cases hc : u % 3 = v % 3
    · rcases Nat.lt_or_ge u v with h | h
      · have hd := dvd_two 3 v u v (by omega) (by omega) (by omega) hc (by omega) le_rfl rfl
        have hS := S_le (u * v) 3 v (by omega) hd
        omega
      · have huv' : u = v := le_antisymm huv h
        rw [← huv']
        have hd := dvd_two 3 (4 * u) u (4 * u) (by omega) (by omega) (by omega) (by omega)
          (by omega) le_rfl rfl
        have h4 : u * u ∣ u * (4 * u) := ⟨4, by ring⟩
        have hS := S_le (u * u) 3 (4 * u) (by omega) (dvd_trans h4 hd)
        have hm5 := Nat.mul_le_mul_right u hu5
        omega
    · have hc2 : (2 * u) % 3 = v % 3 := mod3_aux u v hu3 hv3 hc
      have h2 : u * v ∣ 2 * u * v := ⟨2, by ring⟩
      rcases Nat.lt_or_ge (2 * u) v with h | h
      · have hd := dvd_two 3 v (2 * u) v (by omega) (by omega) (by omega) hc2 (by omega) le_rfl rfl
        have hS := S_le (u * v) 3 v (by omega) (dvd_trans h2 hd)
        omega
      · have hd := dvd_two 3 (2 * u) (2 * u) v (by omega) (by omega) le_rfl rfl (by omega) h
          hc2.symm
        have hS := S_le (u * v) 3 (2 * u) (by omega) (dvd_trans h2 hd)
        omega

theorem conj1 (p : ℕ) (hp : p.Prime) : a (p + 1) = 2 ↔ 3 < p ∧ ((p + 1) / 2).Prime := by
  constructor
  · intro h
    have hS2 : S (p + 1) 2 = p + 1 := a_spec (p + 1) 2 h (by norm_num)
    have hp2 : p ≠ 2 := by
      intro h2
      subst h2
      have h3 : a (2 + 1) = 1 := a_prime 3 Nat.prime_three
      omega
    have hp3 : p ≠ 3 := by
      intro h3
      subst h3
      have h4 : a (3 + 1) = 1 := a_four
      omega
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      omega
    refine ⟨by omega, ?_⟩
    by_contra hq
    have e : p + 1 = 2 * ((p + 1) / 2) := by omega
    have hlt := S_2m ((p + 1) / 2) (by omega) hq
    rw [e] at hS2
    omega
  · rintro ⟨hp3, hq⟩
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    have e : p + 1 = 2 * ((p + 1) / 2) := by omega
    rw [e]
    exact a_2q _ hq (by omega)

end H03A306467

open OMA.S_oeis_a306467 H03A306467 in
theorem OMA.solution : type_of% @OMA.S_oeis_a306467.main := by
  refine ⟨conj1, ?_⟩
  intro p hp
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨hp3, hq⟩ := (conj1 p hp).1 h1
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    refine ⟨hq, ?_⟩
    by_contra hr
    have hn : ¬ (p + 2).Prime := by
      intro hpr
      have := a_prime (p + 2) hpr
      omega
    have hlt := S_odd_comp (p + 2) (by omega) (by omega) hn hr
    have hS3 := a_spec (p + 2) 3 h2 (by norm_num)
    omega
  · rintro ⟨hq, h3, hr⟩
    have hp2 : p ≠ 2 := by
      intro h2
      subst h2
      norm_num at hq
    have hp3 : p ≠ 3 := by
      intro h3'
      subst h3'
      omega
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    have hp5 : 3 < p := by
      have := hp.two_le
      omega
    refine ⟨(conj1 p hp).2 ⟨hp5, hq⟩, ?_⟩
    have e : p + 2 = 3 * ((p + 2) / 3) := by omega
    have hr5 : 5 ≤ (p + 2) / 3 := by
      have hr2 := hr.two_le
      rcases Nat.lt_or_ge ((p + 2) / 3) 5 with hlt | hge
      · exfalso
        have h234 : (p + 2) / 3 = 2 ∨ (p + 2) / 3 = 3 ∨ (p + 2) / 3 = 4 := by omega
        rcases h234 with h' | h' | h'
        · have hp4 : p = 4 := by omega
          rw [hp4] at hp
          norm_num at hp
        · have hp7 : p = 7 := by omega
          rw [hp7] at hq
          norm_num at hq
        · rw [h'] at hr
          norm_num at hr
      · exact hge
    rw [e]
    exact a_3r _ hr hr5
