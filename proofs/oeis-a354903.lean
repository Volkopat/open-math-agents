import OMAStatements.S_oeis_a354903
import Mathlib

namespace OMA.A354903Proof

open OMA.S_oeis_a354903

/-- The admissible next terms after the list `l` of the first terms. -/
def S (l : List ℕ) : Set ℕ :=
  {k : ℕ | 1 ≤ k ∧ k ∉ l ∧ Nat.Coprime k.divisors.card (l.getLastD 1)}

theorem mem_S {l : List ℕ} {k : ℕ} :
    k ∈ S l ↔ 1 ≤ k ∧ k ∉ l ∧ Nat.Coprime k.divisors.card (l.getLastD 1) := Iff.rfl

-- Divisor counts

theorem card_div_pp (q k : ℕ) (hq : q.Prime) : (q ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hq, Finset.card_map, Finset.card_range]

theorem card_div_prime (p : ℕ) (hp : p.Prime) : p.divisors.card = 2 := by
  have h := card_div_pp p 1 hp
  rwa [pow_one] at h

theorem card_mul (m n : ℕ) (h : Nat.Coprime m n) :
    (m * n).divisors.card = m.divisors.card * n.divisors.card :=
  Nat.Coprime.card_divisors_mul h

theorem split_pow (p : ℕ) (hp : p.Prime) (m : ℕ) : m ≠ 0 → ∃ e u, ¬ p ∣ u ∧ m = p ^ e * u := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hpm : p ∣ m
    · obtain ⟨k, rfl⟩ := hpm
      have hk : k ≠ 0 := by
        rintro rfl
        simp at hm
      have hlt : k < p * k := by
        have h2 := hp.two_le
        have h3 : 0 < k := Nat.pos_of_ne_zero hk
        nlinarith
      obtain ⟨e, u, hu, he⟩ := ih k hlt hk
      exact ⟨e + 1, u, hu, by rw [he, pow_succ]; ring⟩
    · exact ⟨0, m, hpm, by simp⟩

/-- If the divisor count of `m` is prime to `c`, every prime below `s` divides `c`, and the prime `p`
divides `m`, then `p ^ (s - 1)` divides `m`: the factor `e + 1` of the divisor count (with `e` the
exponent of `p`) has all its prime factors at least `s`. -/
theorem big_exp (m c s p : ℕ) (hp : p.Prime) (hm : m ≠ 0) (hpm : p ∣ m)
    (hc : Nat.Coprime m.divisors.card c) (hsmall : ∀ l, l < s → l.Prime → l ∣ c) :
    p ^ (s - 1) ∣ m := by
  obtain ⟨e, u, hu, rfl⟩ := split_pow p hp m hm
  have hcop : Nat.Coprime (p ^ e) u :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
  have hcard : (p ^ e * u).divisors.card = (e + 1) * u.divisors.card := by
    rw [card_mul _ _ hcop, card_div_pp p e hp]
  have he : 1 ≤ e := by
    by_contra h
    have h0 : e = 0 := by omega
    rw [h0, pow_zero, one_mul] at hpm
    exact hu hpm
  have hl := Nat.minFac_prime (show e + 1 ≠ 1 by omega)
  have hldvd : (e + 1).minFac ∣ (p ^ e * u).divisors.card := by
    rw [hcard]
    exact Dvd.dvd.mul_right (Nat.minFac_dvd (e + 1)) _
  have hsl : s ≤ (e + 1).minFac := by
    by_contra h
    have h1 := hsmall _ (by omega) hl
    have h4 : Nat.Coprime (e + 1).minFac c := Nat.Coprime.coprime_dvd_left hldvd hc
    have h5 := Nat.Coprime.eq_one_of_dvd h4 h1
    have h6 := hl.one_lt
    omega
  have hle := Nat.minFac_le (show 0 < e + 1 by omega)
  exact dvd_trans (pow_dvd_pow p (by omega)) (dvd_mul_right (p ^ e) u)

theorem le_sum_of_mem' (l : List ℕ) : ∀ x ∈ l, x ≤ l.sum := by
  induction l with
  | nil =>
    intro x hx
    simp at hx
  | cons y t ih =>
    intro x hx
    rw [List.sum_cons]
    rcases List.mem_cons.mp hx with h | h
    · omega
    · have := ih x h
      omega

theorem lt_three_pow (n : ℕ) : n < 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

-- Existence of an admissible term: q ^ (s - 1) with s a prime above c and q a prime above the list

theorem S_nonempty (l : List ℕ) (hc : 1 ≤ l.getLastD 1) : (S l).Nonempty := by
  obtain ⟨s, hs1, hs⟩ := Nat.exists_infinite_primes (l.getLastD 1 + 1)
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (l.sum + 1)
  have hs2 := hs.two_le
  refine ⟨q ^ (s - 1), mem_S.mpr ⟨?_, ?_, ?_⟩⟩
  · have := pow_pos hq.pos (s - 1)
    omega
  · intro hmem
    have h1 := le_sum_of_mem' l _ hmem
    have h2 : q ^ 1 ≤ q ^ (s - 1) := Nat.pow_le_pow_right hq.pos (by omega)
    rw [pow_one] at h2
    omega
  · rw [card_div_pp q (s - 1) hq, Nat.sub_add_cancel (by omega : 1 ≤ s),
      Nat.Prime.coprime_iff_not_dvd hs]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega

-- The greedy sequence

theorem pre_succ (n : ℕ) : pre (n + 1) = pre n ++ [sInf (S (pre n))] := rfl

theorem a_succ (n : ℕ) : a (n + 1) = sInf (S (pre n)) := by
  show (pre (n + 1)).getLastD 0 = _
  rw [pre_succ]
  simp

theorem last_succ (n : ℕ) : (pre (n + 1)).getLastD 1 = a (n + 1) := by
  rw [a_succ, pre_succ]
  simp

theorem last_eq (n : ℕ) (hn : 1 ≤ n) : (pre n).getLastD 1 = a n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact last_succ k

theorem last_pos (n : ℕ) : 1 ≤ (pre n).getLastD 1 := by
  induction n with
  | zero =>
    show 1 ≤ ([] : List ℕ).getLastD 1
    simp
  | succ n ih =>
    rw [last_succ, a_succ]
    exact (mem_S.mp (Nat.sInf_mem (S_nonempty (pre n) ih))).1

theorem a_succ_mem (n : ℕ) : a (n + 1) ∈ S (pre n) := by
  rw [a_succ]
  exact Nat.sInf_mem (S_nonempty (pre n) (last_pos n))

theorem a_succ_le (n k : ℕ) (hk : k ∈ S (pre n)) : a (n + 1) ≤ k := by
  rw [a_succ]
  exact Nat.sInf_le hk

theorem pre_eq_map (n : ℕ) : pre n = (List.range n).map (fun i => a (i + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pre_succ, List.range_succ, List.map_append, ← ih]
    simp only [List.map_cons, List.map_nil]
    rw [a_succ]

theorem mem_pre (n k : ℕ) : k ∈ pre n ↔ ∃ j, 1 ≤ j ∧ j ≤ n ∧ a j = k := by
  rw [pre_eq_map, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    exact ⟨i + 1, by omega, by omega, rfl⟩
  · rintro ⟨j, hj1, hj2, rfl⟩
    refine ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
    show a (j - 1 + 1) = a j
    rw [Nat.sub_add_cancel hj1]

theorem a_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ a n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (mem_S.mp (a_succ_mem k)).1

theorem a_ne (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) : a i ≠ a j := by
  intro h
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  have h1 := (mem_S.mp (a_succ_mem t)).2.1
  apply h1
  rw [mem_pre]
  exact ⟨i, hi, by omega, h⟩

theorem a_inj (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (h : a i = a j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (a_ne i j hi hlt)
  · exact heq
  · exact absurd h.symm (a_ne j i hj hgt)

theorem a_cop (n : ℕ) (hn : 1 ≤ n) : Nat.Coprime (a (n + 1)).divisors.card (a n) := by
  have h := (mem_S.mp (a_succ_mem n)).2.2
  rwa [last_eq n hn] at h

-- Within one divisor-count class the terms increase; so the primes come in natural order

theorem class_mono (i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hd : (a i).divisors.card = (a j).divisors.card) : a i < a j := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hS := mem_S.mp (a_succ_mem k)
  have hjS : a j ∈ S (pre k) := by
    refine mem_S.mpr ⟨a_pos j (by omega), ?_, ?_⟩
    · intro hmem
      obtain ⟨l, hl1, hl2, hl3⟩ := (mem_pre k (a j)).mp hmem
      exact a_ne l j hl1 (by omega) hl3
    · rw [← hd]
      exact hS.2.2
  have hle := a_succ_le k (a j) hjS
  have hne := a_ne (k + 1) j hi hij
  omega

theorem primes_order (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hpi : (a i).Prime)
    (hpj : (a j).Prime) : a i < a j :=
  class_mono i j hi hij (by rw [card_div_prime _ hpi, card_div_prime _ hpj])

-- Greedy exclusion and growth

/-- Greedy exclusion: if `x` never occurs and its divisor count is prime to `a n`, then `x` was
admissible at step `n + 1`, so the chosen term is smaller. -/
theorem block (x n : ℕ) (hx1 : 1 ≤ x) (hx : ∀ m, 1 ≤ m → a m ≠ x) (hn : 1 ≤ n)
    (hc : Nat.Coprime x.divisors.card (a n)) : a (n + 1) < x := by
  have hxS : x ∈ S (pre n) := by
    refine mem_S.mpr ⟨hx1, ?_, ?_⟩
    · intro hmem
      obtain ⟨j, hj1, _, hj3⟩ := (mem_pre n x).mp hmem
      exact hx j hj1 hj3
    · rw [last_eq n hn]
      exact hc
  have hle := a_succ_le n x hxS
  have hne := hx (n + 1) (by omega)
  omega

/-- The terms tend to infinity (they are distinct). -/
theorem ev_large (x : ℕ) : ∃ N, ∀ n, N ≤ n → x ≤ a n := by
  induction x with
  | zero => exact ⟨0, fun n _ => Nat.zero_le _⟩
  | succ x ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hx : ∃ m, 1 ≤ m ∧ a m = x
    · obtain ⟨m, hm1, hm⟩ := hx
      refine ⟨N + m + 1, fun n hn => ?_⟩
      have h1 := hN n (by omega)
      have h2 : a n ≠ x := by
        intro h
        have := a_inj n m (by omega) hm1 (h.trans hm.symm)
        omega
      omega
    · refine ⟨N + 1, fun n hn => ?_⟩
      have h1 := hN n (by omega)
      have h2 : a n ≠ x := fun h => hx ⟨n, by omega, h⟩
      omega

theorem bound_before (N : ℕ) : ∃ B, ∀ m, m < N → a m ≤ B := by
  induction N with
  | zero => exact ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | succ N ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B + a N, fun m hm => ?_⟩
    by_cases h : m < N
    · have := hB m h
      omega
    · have hmN : m = N := by omega
      rw [hmN]
      omega

/-- If `y` never occurs and has a prime number `r` of divisors, then `r` divides every late term. -/
theorem forced (r y : ℕ) (hr : r.Prime) (hy1 : 1 ≤ y) (hdy : y.divisors.card = r)
    (hy : ∀ m, 1 ≤ m → a m ≠ y) : ∃ N, ∀ n, N ≤ n → r ∣ a n := by
  obtain ⟨N, hN⟩ := ev_large y
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra hnd
  have hc : Nat.Coprime y.divisors.card (a n) := by
    rw [hdy]
    exact (Nat.Prime.coprime_iff_not_dvd hr).mpr hnd
  have h1 := block y n hy1 hy (by omega) hc
  have h2 := hN (n + 1) (by omega)
  omega

-- Every prime is a term

theorem prime_term (P : ℕ) (hP : P.Prime) : ∃ n, 1 ≤ n ∧ a n = P := by
  by_contra hcon
  have hmiss : ∀ m, 1 ≤ m → a m ≠ P := fun m hm h => hcon ⟨m, hm, h⟩
  -- (A) all late terms are even, so only finitely many odd values are used
  obtain ⟨N0, hN0⟩ := forced 2 P Nat.prime_two hP.one_lt.le (card_div_prime P hP) hmiss
  obtain ⟨B, hB⟩ := bound_before N0
  have odd_unused : ∀ y, B < y → ¬ 2 ∣ y → ∀ m, 1 ≤ m → a m ≠ y := by
    intro y hy hy2 m hm h
    by_cases hmN : m < N0
    · have := hB m hmN
      omega
    · have h2 := hN0 m (by omega)
      rw [h] at h2
      exact hy2 h2
  -- (B) every prime divides all late terms
  have forced_r : ∀ r, r.Prime → ∃ N, ∀ n, N ≤ n → r ∣ a n := by
    intro r hr
    obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (B + 3)
    have hq2 : ¬ 2 ∣ q := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h
      omega
    have hr2 := hr.two_le
    have hy1 : 1 ≤ q ^ (r - 1) := by
      have := pow_pos hq.pos (r - 1)
      omega
    have hdy : (q ^ (r - 1)).divisors.card = r := by
      rw [card_div_pp q (r - 1) hq]
      omega
    have hqB : B < q ^ (r - 1) := by
      have h3 : q ^ 1 ≤ q ^ (r - 1) := Nat.pow_le_pow_right hq.pos (by omega)
      rw [pow_one] at h3
      omega
    have hq2' : ¬ 2 ∣ q ^ (r - 1) := fun h => hq2 (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)
    exact forced r (q ^ (r - 1)) hr hy1 hdy (odd_unused _ hqB hq2')
  have small : ∀ K, ∃ N, ∀ n, N ≤ n → ∀ r, r.Prime → r ≤ K → r ∣ a n := by
    intro K
    induction K with
    | zero => exact ⟨0, fun n _ r hr hrK => absurd hr.two_le (by omega)⟩
    | succ K ih =>
      obtain ⟨N, hN⟩ := ih
      by_cases hK : (K + 1).Prime
      · obtain ⟨N', hN'⟩ := forced_r (K + 1) hK
        refine ⟨N + N', fun n hn r hr hrK => ?_⟩
        by_cases hrK' : r ≤ K
        · exact hN n (by omega) r hr hrK'
        · have hrK1 : r = K + 1 := by omega
          rw [hrK1]
          exact hN' n (by omega)
      · refine ⟨N, fun n hn r hr hrK => ?_⟩
        have hrK' : r ≤ K := by
          by_contra h
          have hrK1 : r = K + 1 := by omega
          rw [hrK1] at hr
          exact hK hr
        exact hN n hn r hr hrK'
  -- (C) the size clash at a late step n = N + 1
  obtain ⟨N, hN⟩ := small (B + 3)
  have hn1 : 1 ≤ N + 1 := by omega
  have hex : ∃ s, s.Prime ∧ ¬ s ∣ a (N + 1) := by
    obtain ⟨s, hs1, hs⟩ := Nat.exists_infinite_primes (a (N + 1) + 1)
    refine ⟨s, hs, fun hd => ?_⟩
    have := Nat.le_of_dvd (by have := a_pos (N + 1) hn1; omega) hd
    omega
  obtain ⟨s, hs, hmin⟩ : ∃ s, (s.Prime ∧ ¬ s ∣ a (N + 1)) ∧
      ∀ l, l < s → l.Prime → l ∣ a (N + 1) := by
    classical
    exact ⟨Nat.find hex, Nat.find_spec hex, fun l hl hlp => by
      by_contra hld
      exact Nat.find_min hex hl ⟨hlp, hld⟩⟩
  have hsK : B + 3 < s := by
    by_contra h
    exact hs.2 (hN (N + 1) (by omega) s hs.1 (by omega))
  have hy1 : 1 ≤ 3 ^ (s - 1) := by
    have := pow_pos (by norm_num : 0 < 3) (s - 1)
    omega
  have hyB : B < 3 ^ (s - 1) := by
    have := lt_three_pow (s - 1)
    omega
  have hy2 : ¬ 2 ∣ 3 ^ (s - 1) := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hyc : Nat.Coprime (3 ^ (s - 1)).divisors.card (a (N + 1)) := by
    rw [card_div_pp 3 (s - 1) Nat.prime_three, Nat.sub_add_cancel (by have := hs.1.two_le; omega)]
    exact (Nat.Prime.coprime_iff_not_dvd hs.1).mpr hs.2
  have hlt := block (3 ^ (s - 1)) (N + 1) hy1 (odd_unused _ hyB hy2) hn1 hyc
  have h3 : 3 ∣ a (N + 1 + 1) := hN (N + 1 + 1) (by omega) 3 Nat.prime_three (by omega)
  have hpos : 0 < a (N + 1 + 1) := by
    have := a_pos (N + 1 + 1) (by omega)
    omega
  have hpow : 3 ^ (s - 1) ∣ a (N + 1 + 1) :=
    big_exp (a (N + 1 + 1)) (a (N + 1)) s 3 Nat.prime_three (by omega) h3 (a_cop (N + 1) hn1) hmin
  have := Nat.le_of_dvd hpos hpow
  omega

-- Every positive integer is a term

theorem surj (x : ℕ) (hx : 1 ≤ x) : ∃ n, 1 ≤ n ∧ a n = x := by
  by_contra hcon
  have hmiss : ∀ m, 1 ≤ m → a m ≠ x := fun m hm h => hcon ⟨m, hm, h⟩
  obtain ⟨N, hN⟩ := ev_large x
  obtain ⟨B, hB⟩ := bound_before N
  have ht : 0 < x.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd x, by omega⟩⟩
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (B + x.divisors.card + 1)
  obtain ⟨n, hn1, hn⟩ := prime_term p hp
  have hnN : N ≤ n := by
    by_contra h
    have := hB n (by omega)
    omega
  have hc : Nat.Coprime x.divisors.card (a n) := by
    rw [hn, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have := Nat.le_of_dvd ht hd
    omega
  have h1 := block x n hx hmiss hn1 hc
  have h2 := hN (n + 1) (by omega)
  omega

end OMA.A354903Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a354903.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact OMA.A354903Proof.a_pos
  · exact OMA.A354903Proof.a_inj
  · exact OMA.A354903Proof.surj
  · exact OMA.A354903Proof.primes_order
