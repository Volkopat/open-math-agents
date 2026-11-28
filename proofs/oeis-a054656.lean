import OMAStatements.S_oeis_a054656

-- Problem: A054656: Number of primes <= n which do not appear in any partitions of n into distinct primes.
-- Upstream: formal-conjectures statements/oeis-a054656.lean:0 (declaration OMA.S_oeis_a054656.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof (Grok Bot w3): p appears in a partition of n iff n - p is a sum of distinct primes
-- avoiding p. Key lemma: for every p, every m >= 13 is such a sum. Proved by the Richert interval
-- method over the primes < N other than p: [13, S'(N) - 13] is covered, base N = 29 by a checked
-- subset-sum table, and the step needs S'(N) >= N + 25, which follows from
-- sum_{q<N prime} q >= 2N + 25 (explicit chunks up to 65536, then Chebyshev psi bounds from
-- Mathlib: pi(n) log n >= psi(n) >= n log 2 - log(n+1), and a sum of k distinct naturals is
-- >= k(k-1)/2). The values 1, 4, 6 are never sums of distinct primes; small n - p < 13 are
-- handled explicitly, and parity decides which of n-1, n-4, n-6 can be prime.

open Finset Real


namespace T054

def sig (N : ℕ) : ℕ := ∑ q ∈ (range N).filter Nat.Prime, q

lemma sig_mono {a b : ℕ} (h : a ≤ b) : sig a ≤ sig b := by
  unfold sig
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [mem_filter, mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

lemma list_le_sig (L : List ℕ) (a : ℕ) (hL : L.Nodup) (hp : ∀ q ∈ L, q.Prime ∧ q < a) :
    L.sum ≤ sig a := by
  unfold sig
  have e := List.sum_toFinset (fun x => x) hL
  simp only [List.map_id'] at e
  rw [← e]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [List.mem_toFinset] at hx
  simp only [mem_filter, mem_range]
  exact ⟨(hp x hx).2, (hp x hx).1⟩

lemma chunk (L : List ℕ) (a b : ℕ) (hL : L.Nodup) (hp : ∀ q ∈ L, q.Prime ∧ q < a)
    (hs : 2 * b + 25 ≤ L.sum) : ∀ N, a ≤ N → N ≤ b → 2 * N + 25 ≤ sig N := by
  intro N h1 h2
  have := list_le_sig L a hL hp
  have := sig_mono h1
  omega

lemma two_sum (s : Finset ℕ) : s.card * (s.card - 1) ≤ 2 * ∑ x ∈ s, x := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hna : a ∉ s := fun h => lt_irrefl _ (ha a h)
    rw [card_insert_of_notMem hna, sum_insert hna]
    have hc : s.card ≤ a := by
      have : s ⊆ range a := fun x hx => mem_range.2 (ha x hx)
      simpa using card_le_card this
    rcases Nat.eq_zero_or_pos s.card with h | h
    · rw [h]; simp
    · have e : (s.card + 1) * (s.card + 1 - 1) = s.card * (s.card - 1) + 2 * s.card := by
        rcases s.card with _ | c
        · omega
        · simp; ring
      rw [e]; omega


lemma real_part (x K : ℝ) (hx : 65536 ≤ x)
    (h : x * log 2 - log (x + 1) ≤ K * log x) (hK : 0 ≤ K) :
    4 * x + 54 ≤ K * (K - 1) ∧ 1 ≤ K := by
  set t := √(√x) with ht
  have hx0 : 0 ≤ x := by linarith
  have hs : (256:ℝ) ≤ √x := by
    rw [show (256:ℝ) = √(256^2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have ht16 : (16:ℝ) ≤ t := by
    rw [ht, show (16:ℝ) = √(16^2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have htx : t ^ 4 = x := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, ht, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hx0]
  have hlog : log x ≤ 4 * t := by
    rw [← htx, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < t by linarith)
    push_cast; linarith
  have hlog1 : log (x + 1) ≤ 1 + 4 * t := by
    have : log (x + 1) ≤ log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    have := Real.log_two_lt_d9
    linarith
  have hl2 := Real.log_two_gt_d9
  have h1 : 0.69 * t ^ 4 - 1 - 4 * t ≤ 4 * t * K := by
    have : K * log x ≤ K * (4 * t) := mul_le_mul_of_nonneg_left hlog hK
    have : 0.69 * x ≤ x * log 2 := by nlinarith
    rw [htx]
    linarith
  have h2 : 0.17 * t ^ 3 - 2 ≤ K := by
    by_contra hc
    push Not at hc
    have : 4 * t * K < 4 * t * (0.17 * t ^ 3 - 2) := by
      apply mul_lt_mul_of_pos_left hc; linarith
    nlinarith [pow_pos (show (0:ℝ) < t by linarith) 4]
  have h3 : 2.72 * t ^ 2 - 2 ≤ K := by
    have : 0.17 * t ^ 3 ≥ 2.72 * t ^ 2 := by
      have := mul_le_mul_of_nonneg_left ht16 (show 0 ≤ 0.17 * t ^ 2 by positivity)
      nlinarith
    linarith
  have ht2 : (256:ℝ) ≤ t ^ 2 := by nlinarith
  constructor
  · rw [← htx]
    have hA : 0 ≤ 2.72 * t ^ 2 - 3 := by nlinarith
    have : (2.72 * t ^ 2 - 2) * (2.72 * t ^ 2 - 3) ≤ K * (K - 1) := by
      apply mul_le_mul h3 (by linarith) hA (by linarith)
    nlinarith
  · nlinarith


lemma big (N : ℕ) (hN : 65537 ≤ N) : 2 * N + 25 ≤ sig N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hs : sig (n + 1) = ∑ q ∈ Nat.primesLE n, q := rfl
  have h1 := Chebyshev.psi_ge n
  have h2 := Chebyshev.psi_le_primeCounting_mul_log n
  rw [← Nat.primesLE_card_eq_primeCounting] at h2
  set k := (Nat.primesLE n).card with hk
  have hr := real_part (n : ℝ) (k : ℝ) (by exact_mod_cast (by omega : 65536 ≤ n))
    (by linarith) (by positivity)
  have hk1 : 1 ≤ k := by exact_mod_cast hr.2
  have : 4 * n + 54 ≤ k * (k - 1) := by
    have := hr.1
    have e : ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
      push_cast [Nat.cast_sub hk1]; ring
    exact_mod_cast (show ((4 * n + 54 : ℕ) : ℝ) ≤ ((k * (k - 1) : ℕ) : ℝ) by
      rw [e]; push_cast; linarith)
  have h3 := two_sum (Nat.primesLE n)
  rw [← hk] at h3
  rw [hs]; omega


lemma core (N : ℕ) (hN : 29 ≤ N) : 2 * N + 25 ≤ sig N := by
  have c0 := chunk [2, 3, 5, 7, 11, 13, 17, 19, 23] 29 37 (by decide) (by norm_num [List.forall_mem_cons]) (by norm_num)
  have c1 := chunk [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] 37 67 (by decide) (by norm_num [List.forall_mem_cons]) (by norm_num)
  have c2 := chunk [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] 67 238 (by decide) (by norm_num [List.forall_mem_cons]) (by norm_num)
  have c3 := chunk [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233] 238 2662 (by decide) (by norm_num [List.forall_mem_cons]) (by norm_num)
  have c4 := chunk [2659, 2657, 2647, 2633, 2621, 2617, 2609, 2593, 2591, 2579, 2557, 2551, 2549, 2543, 2539, 2531, 2521, 2503, 2477, 2473, 2467, 2459, 2447, 2441, 2437, 2423, 2417, 2411, 2399, 2393, 2389, 2383, 2381, 2377, 2371, 2357, 2351, 2347, 2341, 2339, 2333, 2311, 2309, 2297, 2293, 2287, 2281, 2273, 2269, 2267, 2251, 2243, 2239, 2237] 2662 65536 (by decide) (by norm_num [List.forall_mem_cons]) (by norm_num)
  have := big N
  by_cases h0 : N ≤ 37
  · exact c0 N hN h0
  by_cases h1 : N ≤ 67
  · exact c1 N (by omega) h1
  by_cases h2 : N ≤ 238
  · exact c2 N (by omega) h2
  by_cases h3 : N ≤ 2662
  · exact c3 N (by omega) h3
  by_cases h4 : N ≤ 65536
  · exact c4 N (by omega) h4
  exact big N (by omega)


def T (p N : ℕ) : Finset ℕ := (range N).filter (fun q => q.Prime ∧ q ≠ p)

lemma sig_le (p N : ℕ) : sig N ≤ ∑ q ∈ T p N, q + N := by
  unfold sig T
  rw [← Finset.sum_filter_add_sum_filter_not ((range N).filter Nat.Prime) (fun q => q ≠ p),
    Finset.filter_filter]
  gcongr
  calc ∑ x ∈ ((range N).filter Nat.Prime).filter (fun q => ¬ q ≠ p), x
      ≤ (((range N).filter Nat.Prime).filter (fun q => ¬ q ≠ p)).card • N := by
        apply Finset.sum_le_card_nsmul
        intro x hx; simp only [mem_filter, mem_range] at hx; omega
    _ ≤ 1 • N := by
        gcongr
        apply Finset.card_le_one.2
        intro a ha b hb; simp only [mem_filter] at ha hb; omega
    _ = N := one_smul _ _

lemma G (p N : ℕ) (hN : 29 ≤ N) : N + 25 ≤ ∑ q ∈ T p N, q := by
  have := sig_le p N; have := core N hN; omega

def Inv (p N : ℕ) : Prop :=
  ∀ m, 13 ≤ m → m + 13 ≤ ∑ q ∈ T p N, q → ∃ s ⊆ T p N, ∑ q ∈ s, q = m

lemma T_succ (p N : ℕ) : T p (N + 1) =
    if N.Prime ∧ N ≠ p then insert N (T p N) else T p N := by
  unfold T; rw [range_add_one, filter_insert]

lemma notMem_T (p N : ℕ) : N ∉ T p N := by simp [T]

lemma step (p N : ℕ) (hN : 29 ≤ N) (h : Inv p N) : Inv p (N + 1) := by
  intro m hm1 hm2
  have hsub : T p N ⊆ T p (N + 1) := by
    intro x hx; simp only [T, mem_filter, mem_range] at hx ⊢; exact ⟨by omega, hx.2⟩
  rw [T_succ] at hm2
  split_ifs at hm2 with hc
  · rw [sum_insert (notMem_T p N)] at hm2
    by_cases hm : m + 13 ≤ ∑ q ∈ T p N, q
    · obtain ⟨s, hs, hs2⟩ := h m hm1 hm
      exact ⟨s, hs.trans hsub, hs2⟩
    · have hG := G p N hN
      obtain ⟨s, hs, hs2⟩ := h (m - N) (by omega) (by omega)
      refine ⟨insert N s, ?_, ?_⟩
      · rw [T_succ, if_pos hc]; exact insert_subset_insert _ hs
      · rw [sum_insert (fun hh => notMem_T p N (hs hh))]; omega
  · obtain ⟨s, hs, hs2⟩ := h m hm1 hm2
    exact ⟨s, hs.trans hsub, hs2⟩

def reach : List ℕ → List ℕ
  | [] => [0]
  | q :: l => reach l ++ (reach l).map (· + q)

lemma reach_sound : ∀ (l : List ℕ), l.Nodup → ∀ m ∈ reach l,
    ∃ s : Finset ℕ, s ⊆ l.toFinset ∧ ∑ q ∈ s, q = m
  | [], _, m, hm => by simp [reach] at hm; exact ⟨∅, by simp, by simp [hm]⟩
  | q :: l, hnd, m, hm => by
    rw [List.nodup_cons] at hnd
    simp only [reach, List.mem_append, List.mem_map] at hm
    rcases hm with hm | ⟨x, hx, rfl⟩
    · obtain ⟨s, hs, hs2⟩ := reach_sound l hnd.2 m hm
      exact ⟨s, hs.trans (by intro y; simp; tauto), hs2⟩
    · obtain ⟨s, hs, hs2⟩ := reach_sound l hnd.2 x hx
      have hq : q ∉ s := fun h => hnd.1 (by simpa using hs h)
      refine ⟨insert q s, ?_, ?_⟩
      · intro y hy; simp only [mem_insert] at hy; simp only [List.toFinset_cons, mem_insert]
        rcases hy with rfl | hy; · left; rfl
        right; exact hs hy
      · rw [sum_insert hq, hs2]; ring

def PL : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23]

lemma base_dec : ∀ p ∈ (0 :: PL), ∀ m < 100, 13 ≤ m → m + 13 ≤ (PL.filter (· ≠ p)).sum →
    m ∈ reach (PL.filter (· ≠ p)) := by decide +kernel

lemma T29 (p : ℕ) : T p 29 = (PL.filter (· ≠ p)).toFinset := by
  ext q
  simp only [T, mem_filter, mem_range, List.mem_toFinset, List.mem_filter, PL]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, by simpa using h3⟩
    interval_cases q <;> first | (norm_num at h2; done) | simp
  · rintro ⟨h1, h2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    refine ⟨by omega, by rcases h1 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num,
      by simpa using h2⟩

lemma base (p : ℕ) : Inv p 29 := by
  intro m hm1 hm2
  have hnd : (PL.filter (· ≠ p)).Nodup := List.Nodup.filter _ (by decide)
  rw [T29] at hm2 ⊢
  rw [List.sum_toFinset _ hnd] at hm2
  simp only [List.map_id'] at hm2
  have key : m ∈ reach (PL.filter (· ≠ p)) := by
    have hle : (PL.filter (· ≠ p)).sum ≤ 100 := by
      have := List.Sublist.sum_le_sum (List.filter_sublist (p := fun x => decide (x ≠ p)) (l := PL))
        (by simp)
      simpa [PL] using this
    by_cases hp : p ∈ PL
    · exact base_dec p (List.mem_cons_of_mem _ hp) m (by omega) hm1 hm2
    · have e : PL.filter (· ≠ p) = PL.filter (· ≠ 0) := by
        rw [List.filter_eq_self.2, List.filter_eq_self.2]
        · intro a ha; simp; rintro rfl; simp [PL] at ha
        · intro a ha; simp; rintro rfl; exact hp ha
      rw [e] at hm2 ⊢
      exact base_dec 0 (by simp) m (by rw [e] at hle; omega) hm1 hm2
  exact reach_sound _ hnd m key

lemma key (p m : ℕ) (hm : 13 ≤ m) :
    ∃ s : Finset ℕ, (∀ q ∈ s, q.Prime) ∧ p ∉ s ∧ ∑ q ∈ s, q = m := by
  have hI : ∀ N, 29 ≤ N → Inv p N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact base p
    | succ N hN ih => exact step p N hN ih
  obtain ⟨s, hs, hs2⟩ := hI (m + 29) (by omega) m hm (by have := G p (m + 29) (by omega); omega)
  refine ⟨s, fun q hq => ?_, fun hp => ?_, hs2⟩
  · have := hs hq; simp [T] at this; exact this.2.1
  · have := hs hp; simp [T] at this


lemma no146 (t : Finset ℕ) (ht : ∀ q ∈ t, q.Prime) (h : ∑ q ∈ t, q = 1 ∨ ∑ q ∈ t, q = 4 ∨ ∑ q ∈ t, q = 6) :
    False := by
  have hsub : t ⊆ ({2, 3, 5} : Finset ℕ) := by
    intro q hq
    have h1 : q ≤ ∑ x ∈ t, x := Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hq
    have h2 := ht q hq
    have : q ≤ 6 := by omega
    interval_cases q <;> first | (norm_num at h2; done) | simp
  have hd : ∀ u ∈ ({2, 3, 5} : Finset ℕ).powerset,
      ¬ (∑ q ∈ u, q = 1 ∨ ∑ q ∈ u, q = 4 ∨ ∑ q ∈ u, q = 6) := by decide
  exact hd t (Finset.mem_powerset.2 hsub) h

end T054

namespace OMA.A054656Proof
open OMA.S_oeis_a054656

lemma of_avoid (n p : ℕ) (hp : p.Prime) (t : Finset ℕ) (ht : ∀ q ∈ t, q.Prime) (hpt : p ∉ t)
    (hs : p + ∑ q ∈ t, q = n) : Appears n p :=
  ⟨insert p t, by
    intro q hq; rw [Finset.mem_insert] at hq; rcases hq with rfl | hq; exacts [hp, ht q hq],
    Finset.mem_insert_self _ _, by rw [Finset.sum_insert hpt, hs]⟩

lemma appears_iff (n p : ℕ) (hn : 23 ≤ n) (hp : p.Prime) (hpn : p ≤ n) :
    Appears n p ↔ ¬ (n - p = 1 ∨ n - p = 4 ∨ n - p = 6) := by
  constructor
  · rintro ⟨s, hs1, hs2, hs3⟩ h
    have e := Finset.add_sum_erase s (fun q => q) hs2
    apply T054.no146 (s.erase p) (fun q hq => hs1 q (Finset.mem_of_mem_erase hq))
    omega
  · intro h
    by_cases hm : 13 ≤ n - p
    · obtain ⟨t, ht1, ht2, ht3⟩ := T054.key p (n - p) hm
      exact of_avoid n p hp t ht1 ht2 (by omega)
    · have h11 : 11 ≤ p := by omega
      have mk : ∀ t : Finset ℕ, (∀ q ∈ t, q.Prime) → (∀ q ∈ t, q < p) → ∑ q ∈ t, q = n - p →
          Appears n p := fun t ht1 ht2 ht3 =>
        of_avoid n p hp t ht1 (fun hh => lt_irrefl _ (ht2 p hh)) (by omega)
      have : n - p = 0 ∨ n - p = 2 ∨ n - p = 3 ∨ n - p = 5 ∨ n - p = 7 ∨ n - p = 8 ∨
          n - p = 9 ∨ n - p = 10 ∨ n - p = 11 ∨ n - p = 12 := by omega
      rcases this with e|e|e|e|e|e|e|e|e|e
      · exact mk ∅ (by simp) (by simp) (by simp [e])
      · exact mk {2} (by simp; norm_num) (by simp; omega) (by simp [e])
      · exact mk {3} (by simp; norm_num) (by simp; omega) (by simp [e])
      · exact mk {5} (by simp; norm_num) (by simp; omega) (by simp [e])
      · exact mk {7} (by simp; norm_num) (by simp; omega) (by simp [e])
      · exact mk {3, 5} (by simp; norm_num) (by simp; omega) (by simp [e])
      · exact mk {2, 7} (by simp; norm_num) (by simp; omega) (by simp [e])
      · exact mk {3, 7} (by simp; norm_num) (by simp; omega) (by simp [e])
      · exact mk {11} (by simp; norm_num) (by simp; omega) (by simp [e])
      · exact mk {5, 7} (by simp; norm_num) (by simp; omega) (by simp [e])

lemma not_prime_even (k : ℕ) (hk : 4 ≤ k) (he : Even k) : ¬ k.Prime := by
  intro h
  rcases h.eq_two_or_odd' with h2 | h2
  · omega
  · exact (Nat.not_even_iff_odd.2 h2) he

theorem main' : ∀ n : ℕ, 23 ≤ n →
    a n = if (n - 6).Prime ∧ (n - 4).Prime then 2
      else if (n - 6).Prime ∨ (n - 4).Prime ∨ (n - 1).Prime then 1 else 0 := by
  intro n hn
  have hset : {p : ℕ | p.Prime ∧ p ≤ n ∧ ¬ Appears n p} =
      ↑((({n - 1, n - 4, n - 6} : Finset ℕ)).filter Nat.Prime) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [appears_iff n p hn h1 h2, not_not] at h3
      exact ⟨by omega, h1⟩
    · rintro ⟨h1, h2⟩
      have hpn : p ≤ n := by omega
      refine ⟨h2, hpn, ?_⟩
      rw [appears_iff n p hn h2 hpn, not_not]; omega
  unfold a
  rw [hset, Set.ncard_coe_finset]
  rcases Nat.even_or_odd n with he | ho
  · have hA : ¬ (n - 6).Prime := not_prime_even _ (by omega) (by
      rcases he with ⟨r, hr⟩; exact ⟨r - 3, by omega⟩)
    have hB : ¬ (n - 4).Prime := not_prime_even _ (by omega) (by
      rcases he with ⟨r, hr⟩; exact ⟨r - 2, by omega⟩)
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp only [hA, hB, if_false, false_and, false_or]
    split_ifs <;> simp
  · have hC : ¬ (n - 1).Prime := not_prime_even _ (by omega) (by
      rcases ho with ⟨r, hr⟩; exact ⟨r, by omega⟩)
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp only [hC, if_false, or_false]
    have hne : n - 4 ≠ n - 6 := by omega
    split_ifs <;> simp_all

end OMA.A054656Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a054656.main := OMA.A054656Proof.main'
