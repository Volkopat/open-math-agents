import OMAStatements.S_oeis_a364902
import Mathlib

namespace OMA.A364902Proof

open OMA.S_oeis_a364902

/-- The candidate set at the index `N`, given the list `l` of the earlier terms. -/
def S (l : List ℕ) (N : ℕ) : Set ℕ :=
  {v : ℕ | v ∉ l ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
    (v = p * l.getD (k2 N - 1) 0 ∨ v = p * l.getD (k3 N - 1) 0)}

theorem mem_S {l : List ℕ} {N v : ℕ} :
    v ∈ S l N ↔ v ∉ l ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
      (v = p * l.getD (k2 N - 1) 0 ∨ v = p * l.getD (k3 N - 1) 0) := Iff.rfl

-- Basic facts on the list

theorem pre_succ (n : ℕ) : pre (n + 1) = pre n ++
    [if k2 (n + 1) = 0 ∨ k3 (n + 1) = 0 then n + 1 else sInf (S (pre n) (n + 1))] := rfl

theorem length_pre (n : ℕ) : (pre n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pre_succ, List.length_append, ih, List.length_singleton]

theorem a_succ (n : ℕ) : a (n + 1) =
    if k2 (n + 1) = 0 ∨ k3 (n + 1) = 0 then n + 1 else sInf (S (pre n) (n + 1)) := by
  rw [show a (n + 1) = (pre (n + 1)).getLastD 0 from rfl, pre_succ, List.getLastD_concat]

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

theorem getD_pre (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n) : (pre n).getD (k - 1) 0 = a k := by
  rw [List.getD_eq_getElem?_getD, pre_eq_map, List.getElem?_map,
    List.getElem?_range (show k - 1 < n by omega)]
  show a (k - 1 + 1) = a k
  rw [Nat.sub_add_cancel hk1]

-- The indices

theorem k2_lt (N : ℕ) (hN : 1 ≤ N) : k2 N < N := by
  have h := Nat.two_pow_pos (Nat.log 2 N)
  unfold k2
  omega

theorem k3_lt (N : ℕ) (hN : 1 ≤ N) : k3 N < N := by
  have h : 0 < 3 ^ Nat.log 3 N := Nat.pow_pos (by norm_num)
  unfold k3
  omega

theorem forced_pow (N : ℕ) (hN : 1 ≤ N) (hF : k2 N = 0 ∨ k3 N = 0) :
    N = 2 ^ Nat.log 2 N ∨ N = 3 ^ Nat.log 3 N := by
  have h2 := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  have h3 := Nat.pow_log_le_self 3 (show N ≠ 0 by omega)
  unfold k2 k3 at hF
  omega

theorem k2_two_pow (e : ℕ) : k2 (2 ^ e) = 0 := by
  unfold k2
  rw [Nat.log_pow (show 1 < 2 by norm_num)]
  exact Nat.sub_self _

theorem k3_three_pow (e : ℕ) : k3 (3 ^ e) = 0 := by
  unfold k3
  rw [Nat.log_pow (show 1 < 3 by norm_num)]
  exact Nat.sub_self _

theorem child_k2 (k x : ℕ) (hk : k < 2 ^ x) : k2 (2 ^ x + k) = k := by
  have hlog : Nat.log 2 (2 ^ x + k) = x := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · rw [pow_succ]
      omega
  unfold k2
  rw [hlog]
  omega

theorem three_dvd_of_k3 (N : ℕ) (hN : 2 ≤ N) (h : k3 N = 0) : 3 ∣ N := by
  have hle := Nat.pow_log_le_self 3 (show N ≠ 0 by omega)
  have heq : 3 ^ Nat.log 3 N = N := by
    unfold k3 at h
    omega
  rcases Nat.eq_zero_or_pos (Nat.log 3 N) with h0 | hpos
  · rw [h0, pow_zero] at heq
    omega
  · rw [← heq]
    exact dvd_pow_self 3 (by omega)

-- Divisibility facts

theorem dvd_of_eq' {x y : ℕ} (h : x = y) : x ∣ y := by
  subst h
  exact dvd_refl _

theorem not3_pow2 (x : ℕ) : ¬ 3 ∣ 2 ^ x := by
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem not2_pow3 (x : ℕ) : ¬ 2 ∣ 3 ^ x := by
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
  omega

theorem not6_pow2 (x : ℕ) : ¬ 6 ∣ 2 ^ x := fun h => not3_pow2 x (Nat.dvd_trans (by norm_num) h)

theorem not6_pow3 (x : ℕ) : ¬ 6 ∣ 3 ^ x := fun h => not2_pow3 x (Nat.dvd_trans (by norm_num) h)

theorem no_big2 (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) (x : ℕ) (h : q ∣ 2 ^ x) : False := by
  have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h)
  omega

theorem no_big3 (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) (x : ℕ) (h : q ∣ 3 ^ x) : False := by
  have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h)
  omega

theorem not6_mul (p A : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hA : ¬ 6 ∣ A) : ¬ 6 ∣ p * A := by
  intro h
  have h2 : 2 ∣ p * A := Nat.dvd_trans (by norm_num) h
  have h3 : 3 ∣ p * A := Nat.dvd_trans (by norm_num) h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h2p | h2A
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p
    omega
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3p | h3A
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p
    omega
  exact hA (by omega)

theorem unit_of_prime (p A : ℕ) (h5 : 5 ≤ p) (h : (p * A).Prime) : A = 1 := by
  rcases Nat.prime_mul_iff.mp h with h' | h'
  · exact h'.2
  · omega

-- The two kinds of steps

theorem S_nonempty (l : List ℕ) (N : ℕ) (hA : 1 ≤ l.getD (k2 N - 1) 0) : (S l N).Nonempty := by
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (l.sum + 5)
  refine ⟨p * l.getD (k2 N - 1) 0, mem_S.mpr ⟨?_, p, hp, by omega, Or.inl rfl⟩⟩
  intro hmem
  have h1 := List.le_sum_of_mem hmem
  have h2 : p ≤ p * l.getD (k2 N - 1) 0 := Nat.le_mul_of_pos_right p hA
  omega

theorem step_forced (N : ℕ) (hN : 1 ≤ N) (hF : k2 N = 0 ∨ k3 N = 0) : a N = N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [a_succ, if_pos hF]

theorem step_free (N : ℕ) (hN : 1 ≤ N) (hF : ¬ (k2 N = 0 ∨ k3 N = 0)) :
    a N = sInf (S (pre (N - 1)) N) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [a_succ, if_neg hF, Nat.add_sub_cancel]

theorem k2_pos (N : ℕ) (hF : ¬ (k2 N = 0 ∨ k3 N = 0)) : 1 ≤ k2 N := by
  have : k2 N ≠ 0 := fun h => hF (Or.inl h)
  omega

theorem k3_pos (N : ℕ) (hF : ¬ (k2 N = 0 ∨ k3 N = 0)) : 1 ≤ k3 N := by
  have : k3 N ≠ 0 := fun h => hF (Or.inr h)
  omega

theorem getD2 (N : ℕ) (hN : 1 ≤ N) (hF : ¬ (k2 N = 0 ∨ k3 N = 0)) :
    (pre (N - 1)).getD (k2 N - 1) 0 = a (k2 N) := by
  have := k2_lt N hN
  exact getD_pre (N - 1) (k2 N) (k2_pos N hF) (by omega)

theorem getD3 (N : ℕ) (hN : 1 ≤ N) (hF : ¬ (k2 N = 0 ∨ k3 N = 0)) :
    (pre (N - 1)).getD (k3 N - 1) 0 = a (k3 N) := by
  have := k3_lt N hN
  exact getD_pre (N - 1) (k3 N) (k3_pos N hF) (by omega)

theorem free_val' (N : ℕ) (hN : 1 ≤ N) (hF : ¬ (k2 N = 0 ∨ k3 N = 0)) (hA : 1 ≤ a (k2 N)) :
    a N ∉ pre (N - 1) ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ (a N = p * a (k2 N) ∨ a N = p * a (k3 N)) := by
  have e2 := getD2 N hN hF
  have e3 := getD3 N hN hF
  have hne : (S (pre (N - 1)) N).Nonempty := S_nonempty _ _ (by rw [e2]; exact hA)
  have hmem := Nat.sInf_mem hne
  rw [← step_free N hN hF, mem_S, e2, e3] at hmem
  exact hmem

theorem free_le (N : ℕ) (hN : 1 ≤ N) (hF : ¬ (k2 N = 0 ∨ k3 N = 0)) (v p : ℕ) (hp : p.Prime)
    (h5 : 5 ≤ p) (hv : v ∉ pre (N - 1)) (hvp : v = p * a (k2 N) ∨ v = p * a (k3 N)) : a N ≤ v := by
  rw [step_free N hN hF]
  apply Nat.sInf_le
  rw [mem_S, getD2 N hN hF, getD3 N hN hF]
  exact ⟨hv, p, hp, h5, hvp⟩

-- (1) Every term is positive and not divisible by 6

theorem good : ∀ N : ℕ, 1 ≤ N → 1 ≤ a N ∧ ¬ 6 ∣ a N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases hF : k2 N = 0 ∨ k3 N = 0
    · rw [step_forced N hN hF]
      refine ⟨hN, ?_⟩
      rcases forced_pow N hN hF with h | h
      · rw [h]
        exact not6_pow2 _
      · rw [h]
        exact not6_pow3 _
    · have g2 := ih (k2 N) (k2_lt N hN) (k2_pos N hF)
      have g3 := ih (k3 N) (k3_lt N hN) (k3_pos N hF)
      obtain ⟨_, p, hp, h5, hv⟩ := free_val' N hN hF g2.1
      rcases hv with hv | hv
      · rw [hv]
        exact ⟨le_trans g2.1 (Nat.le_mul_of_pos_left _ hp.pos), not6_mul p _ hp h5 g2.2⟩
      · rw [hv]
        exact ⟨le_trans g3.1 (Nat.le_mul_of_pos_left _ hp.pos), not6_mul p _ hp h5 g3.2⟩

theorem free_val (N : ℕ) (hN : 1 ≤ N) (hF : ¬ (k2 N = 0 ∨ k3 N = 0)) :
    a N ∉ pre (N - 1) ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ (a N = p * a (k2 N) ∨ a N = p * a (k3 N)) :=
  free_val' N hN hF (good (k2 N) (k2_pos N hF)).1

-- (2) Injectivity

theorem a_ne (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) : a i ≠ a j := by
  intro h
  have hj : 1 ≤ j := by omega
  by_cases hFj : k2 j = 0 ∨ k3 j = 0
  · have haj := step_forced j hj hFj
    by_cases hFi : k2 i = 0 ∨ k3 i = 0
    · have hai := step_forced i hi hFi
      omega
    · obtain ⟨_, p, hp, h5, hv⟩ := free_val i hi hFi
      have hdvd : p ∣ a i := by
        rcases hv with hv | hv
        · rw [hv]
          exact dvd_mul_right _ _
        · rw [hv]
          exact dvd_mul_right _ _
      rw [h, haj] at hdvd
      rcases forced_pow j hj hFj with hpow | hpow
      · rw [hpow] at hdvd
        exact no_big2 p hp h5 _ hdvd
      · rw [hpow] at hdvd
        exact no_big3 p hp h5 _ hdvd
  · apply (free_val j hj hFj).1
    rw [mem_pre]
    exact ⟨i, hi, by omega, h⟩

theorem a_inj (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (h : a i = a j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (a_ne i j hi hlt)
  · exact heq
  · exact absurd h.symm (a_ne j i hj hgt)

-- (3) The 2-children of `k`: one of each consecutive pair is not forced

theorem k_lt_pow (k m : ℕ) (hm : k ≤ m) : k < 2 ^ m :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hm)

/-- The index `2^(k + 2t) + k` or `2^(k + 2t + 1) + k`, whichever is not a power of 3. -/
def idx (k t : ℕ) : ℕ :=
  if k3 (2 ^ (k + 2 * t) + k) = 0 then 2 ^ (k + 2 * t + 1) + k else 2 ^ (k + 2 * t) + k

theorem idx_free (k t : ℕ) (hk : 1 ≤ k) :
    1 ≤ idx k t ∧ k2 (idx k t) = k ∧ ¬ (k2 (idx k t) = 0 ∨ k3 (idx k t) = 0) := by
  have hc := k_lt_pow k (k + 2 * t) (by omega)
  have hd := k_lt_pow k (k + 2 * t + 1) (by omega)
  have hc2 := child_k2 k _ hc
  have hd2 := child_k2 k _ hd
  unfold idx
  split_ifs with h
  · refine ⟨by omega, hd2, ?_⟩
    rintro (h' | h')
    · omega
    · have h1 := three_dvd_of_k3 _ (by omega) h
      have h2 := three_dvd_of_k3 _ (by omega) h'
      rw [pow_succ] at h2
      have h3 : 3 ∣ 2 ^ (k + 2 * t) := by omega
      exact not3_pow2 _ h3
  · refine ⟨by omega, hc2, ?_⟩
    rintro (h' | h')
    · omega
    · exact h h'

theorem idx_ge (k t : ℕ) : 2 ^ (k + 2 * t) + k ≤ idx k t := by
  have : 2 ^ (k + 2 * t) ≤ 2 ^ (k + 2 * t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold idx
  split_ifs <;> omega

theorem idx_le (k t : ℕ) : idx k t ≤ 2 ^ (k + 2 * t + 1) + k := by
  have : 2 ^ (k + 2 * t) ≤ 2 ^ (k + 2 * t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold idx
  split_ifs <;> omega

theorem idx_lt (k s t : ℕ) (hst : s < t) : idx k s < idx k t := by
  have h1 := idx_le k s
  have h2 := idx_ge k t
  have h3 : 2 ^ (k + 2 * s + 1) < 2 ^ (k + 2 * t) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem idx_inj (k s t : ℕ) (h : idx k s = idx k t) : s = t := by
  rcases lt_trichotomy s t with hlt | heq | hgt
  · have := idx_lt k s t hlt
    omega
  · exact heq
  · have := idx_lt k t s hgt
    omega

-- (4) Closure under multiplication by a prime at least 5

theorem closed_mul (k : ℕ) (hk : 1 ≤ k) (p0 : ℕ) (hp0 : p0.Prime) (h5 : 5 ≤ p0) :
    ∃ n, 1 ≤ n ∧ a n = p0 * a k := by
  by_contra hcon
  have hmiss : ∀ n, 1 ≤ n → a n ≠ p0 * a k := fun n hn h => hcon ⟨n, hn, h⟩
  have key : ∀ t, a (idx k t) < p0 * a k := by
    intro t
    obtain ⟨h1, h2, hF⟩ := idx_free k t hk
    have hle : a (idx k t) ≤ p0 * a k := by
      apply free_le (idx k t) h1 hF (p0 * a k) p0 hp0 h5
      · intro hmem
        obtain ⟨j, hj1, _, hj3⟩ := (mem_pre _ _).mp hmem
        exact hmiss j hj1 hj3
      · left
        rw [h2]
    have hne := hmiss (idx k t) h1
    omega
  have hcard : (Finset.range (p0 * a k + 1)).card ≤ (Finset.range (p0 * a k)).card :=
    Finset.card_le_card_of_injOn (fun t => a (idx k t))
      (by
        intro t _
        simpa using key t)
      (by
        intro s _ t _ hst
        exact idx_inj k s t (a_inj _ _ (idx_free k s hk).1 (idx_free k t hk).1 hst))
  rw [Finset.card_range, Finset.card_range] at hcard
  omega

-- (5) Surjectivity onto the numbers not divisible by 6

theorem a_two_pow (e : ℕ) : a (2 ^ e) = 2 ^ e :=
  step_forced _ Nat.one_le_two_pow (Or.inl (k2_two_pow e))

theorem a_three_pow (e : ℕ) : a (3 ^ e) = 3 ^ e :=
  step_forced _ (Nat.one_le_pow _ _ (by norm_num)) (Or.inr (k3_three_pow e))

theorem surj_core (r : ℕ) : 1 ≤ r → ¬ 2 ∣ r → ¬ 3 ∣ r → ∀ e : ℕ,
    (∃ n, 1 ≤ n ∧ a n = 2 ^ e * r) ∧ (∃ n, 1 ≤ n ∧ a n = 3 ^ e * r) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr h2 h3 e
    by_cases hr1 : r = 1
    · subst hr1
      refine ⟨⟨2 ^ e, Nat.one_le_two_pow, by rw [a_two_pow, mul_one]⟩,
        ⟨3 ^ e, Nat.one_le_pow _ _ (by norm_num), by rw [a_three_pow, mul_one]⟩⟩
    · obtain ⟨p, hp, hpd⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ r := ⟨r.minFac, Nat.minFac_prime hr1, Nat.minFac_dvd r⟩
      have hp2 := hp.two_le
      have hn2 : p ≠ 2 := by
        intro h
        rw [h] at hpd
        exact h2 hpd
      have hn3 : p ≠ 3 := by
        intro h
        rw [h] at hpd
        exact h3 hpd
      have hn4 : p ≠ 4 := by
        intro h
        rw [h] at hpd
        exact h2 (Nat.dvd_trans (by norm_num) hpd)
      have hp5 : 5 ≤ p := by omega
      obtain ⟨r', hr'⟩ := hpd
      have hr'1 : 1 ≤ r' := by
        rcases Nat.eq_zero_or_pos r' with h0 | h0
        · rw [h0, mul_zero] at hr'
          omega
        · exact h0
      have hlt : r' < r := by
        have : 5 * r' ≤ p * r' := Nat.mul_le_mul_right _ hp5
        omega
      have h2' : ¬ 2 ∣ r' := fun h => h2 (by rw [hr']; exact Dvd.dvd.mul_left h _)
      have h3' : ¬ 3 ∣ r' := fun h => h3 (by rw [hr']; exact Dvd.dvd.mul_left h _)
      obtain ⟨⟨n1, hn1, ha1⟩, ⟨n2, hn2', ha2⟩⟩ := ih r' hlt hr'1 h2' h3' e
      obtain ⟨m1, hm1, hb1⟩ := closed_mul n1 hn1 p hp hp5
      obtain ⟨m2, hm2, hb2⟩ := closed_mul n2 hn2' p hp hp5
      refine ⟨⟨m1, hm1, ?_⟩, ⟨m2, hm2, ?_⟩⟩
      · rw [hb1, ha1, hr']
        ring
      · rw [hb2, ha2, hr']
        ring

theorem surj (m : ℕ) (hm : 1 ≤ m) (h6 : ¬ 6 ∣ m) : ∃ n, 1 ≤ n ∧ a n = m := by
  by_cases h3 : 3 ∣ m
  · have h2 : ¬ 2 ∣ m := fun h => h6 (by omega)
    obtain ⟨e, r, hr3, hmr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show m ≠ 0 by omega) 3 (by norm_num)
    have hr2 : ¬ 2 ∣ r := fun h => h2 (by rw [hmr]; exact Dvd.dvd.mul_left h _)
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0, mul_zero] at hmr
        omega
      · exact h0
    obtain ⟨n, hn, ha⟩ := (surj_core r hr1 hr2 hr3 e).2
    exact ⟨n, hn, by rw [ha, hmr]⟩
  · obtain ⟨e, r, hr2, hmr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show m ≠ 0 by omega) 2 (by norm_num)
    have hr3 : ¬ 3 ∣ r := fun h => h3 (by rw [hmr]; exact Dvd.dvd.mul_left h _)
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0, mul_zero] at hmr
        omega
      · exact h0
    obtain ⟨n, hn, ha⟩ := (surj_core r hr1 hr2 hr3 e).1
    exact ⟨n, hn, by rw [ha, hmr]⟩

-- (6) Primes in order

theorem a_one : a 1 = 1 := by
  have h := a_two_pow 0
  rw [pow_zero] at h
  exact h

theorem a_two : a 2 = 2 := by
  have h := a_two_pow 1
  rw [pow_one] at h
  exact h

theorem a_three : a 3 = 3 := by
  have h := a_three_pow 1
  rw [pow_one] at h
  exact h

theorem prime_min (i : ℕ) (hi : 1 ≤ i) (hpr : (a i).Prime) (h5 : 5 ≤ a i) (q : ℕ) (hq : q.Prime)
    (hq5 : 5 ≤ q) (hqn : q ∉ pre (i - 1)) : a i ≤ q := by
  have hF : ¬ (k2 i = 0 ∨ k3 i = 0) := by
    intro hF
    have hai := step_forced i hi hF
    rcases forced_pow i hi hF with h | h
    · exact no_big2 (a i) hpr h5 _ (dvd_of_eq' (hai.trans h))
    · exact no_big3 (a i) hpr h5 _ (dvd_of_eq' (hai.trans h))
  obtain ⟨_, p, hp, hp5, hv⟩ := free_val i hi hF
  rcases hv with hv | hv
  · have h1 : a (k2 i) = 1 := unit_of_prime p _ hp5 (by rw [← hv]; exact hpr)
    apply free_le i hi hF q q hq hq5 hqn
    left
    rw [h1, mul_one]
  · have h1 : a (k3 i) = 1 := unit_of_prime p _ hp5 (by rw [← hv]; exact hpr)
    apply free_le i hi hF q q hq hq5 hqn
    right
    rw [h1, mul_one]

theorem primes_order (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hpi : (a i).Prime) (hpj : (a j).Prime) :
    a i < a j := by
  have hj : 1 ≤ j := by omega
  have hne := a_ne i j hi hij
  have h2i := hpi.two_le
  have h2j := hpj.two_le
  have h1 := a_one
  have h2 := a_two
  have h3 := a_three
  by_cases hbi : 5 ≤ a i
  · by_cases hbj : 5 ≤ a j
    · have hle := prime_min i hi hpi hbi (a j) hpj hbj (by
        intro hmem
        obtain ⟨j', hj'1, hj'2, hj'3⟩ := (mem_pre _ _).mp hmem
        exact a_ne j' j hj'1 (by omega) hj'3)
      omega
    · exfalso
      rcases (show a j = 2 ∨ a j = 3 ∨ a j = 4 by omega) with h | h | h
      · have := a_inj j 2 hj (by norm_num) (h.trans h2.symm)
        have : i = 1 := by omega
        subst this
        omega
      · have := a_inj j 3 hj (by norm_num) (h.trans h3.symm)
        have : i = 1 ∨ i = 2 := by omega
        rcases this with h' | h'
        · subst h'
          omega
        · subst h'
          omega
      · rw [h] at hpj
        norm_num at hpj
  · rcases (show a i = 2 ∨ a i = 3 ∨ a i = 4 by omega) with h | h | h
    · omega
    · have hi3 := a_inj i 3 hi (by norm_num) (h.trans h3.symm)
      have hj2 : a j ≠ 2 := fun h' => by
        have := a_inj j 2 hj (by norm_num) (h'.trans h2.symm)
        omega
      omega
    · rw [h] at hpi
      norm_num at hpi

end OMA.A364902Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a364902.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact OMA.A364902Proof.good
  · exact OMA.A364902Proof.a_inj
  · exact OMA.A364902Proof.surj
  · exact OMA.A364902Proof.primes_order
