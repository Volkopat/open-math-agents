import OMAStatements.S_oeis_a357601
import Mathlib

namespace OMA.A357601Proof

open OMA.S_oeis_a357601

/-- The numbers with `t` divisors that are not in the list `l`. -/
def S (l : List ℕ) (t : ℕ) : Set ℕ := {v : ℕ | v.divisors.card = t ∧ v ∉ l}

theorem mem_S {l : List ℕ} {t v : ℕ} : v ∈ S l t ↔ v.divisors.card = t ∧ v ∉ l := Iff.rfl

/-- `k = N - 2 ^ m`, where `2 ^ m` is the greatest power of 2 not exceeding `N`. -/
def kk (N : ℕ) : ℕ := N - 2 ^ Nat.log 2 N

/-- The number of divisors of the term `a N`. -/
noncomputable def D (N : ℕ) : ℕ := (a N).divisors.card

/-- The entry appended to `l = pre n`, for the index `n + 1`. -/
noncomputable def nxt (l : List ℕ) (n : ℕ) : ℕ :=
  if n + 1 = 2 ^ Nat.log 2 (n + 1) then n + 1 else
    sInf (S l ((l.getD (n + 1 - 2 ^ Nat.log 2 (n + 1) - 1) 0).divisors.card + 1))

-- Unfolding the recursion

theorem pre_succ (n : ℕ) : pre (n + 1) = pre n ++ [nxt (pre n) n] := rfl

theorem length_pre (n : ℕ) : (pre n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pre_succ, List.length_append, ih, List.length_singleton]

theorem a_succ (n : ℕ) : a (n + 1) = nxt (pre n) n := by
  show (pre (n + 1)).getLastD 0 = _
  rw [pre_succ]
  exact List.getLastD_concat

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

theorem getD_pre (n i : ℕ) (hi : i < n) : (pre n).getD i 0 = a (i + 1) := by
  rw [pre_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

-- The index `k`

theorem pow_log_le (N : ℕ) (hN : 1 ≤ N) : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)

theorem lt_two_pow_log (N : ℕ) : N < 2 * 2 ^ Nat.log 2 N := by
  have h : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two N
  rw [pow_succ] at h
  omega

theorem kk_lt (N : ℕ) (hN : 1 ≤ N) : kk N < 2 ^ Nat.log 2 N := by
  have h1 := pow_log_le N hN
  have h2 := lt_two_pow_log N
  unfold kk
  omega

theorem kk_pos (N : ℕ) (hN : 1 ≤ N) (hnf : N ≠ 2 ^ Nat.log 2 N) : 1 ≤ kk N := by
  have h1 := pow_log_le N hN
  unfold kk
  omega

theorem kk_lt_self (N : ℕ) (hN : 1 ≤ N) (_hnf : N ≠ 2 ^ Nat.log 2 N) : kk N < N := by
  have h1 := pow_log_le N hN
  have h3 : 0 < 2 ^ Nat.log 2 N := Nat.two_pow_pos _
  unfold kk
  omega

theorem log_kk_lt (N : ℕ) (hN : 1 ≤ N) (hnf : N ≠ 2 ^ Nat.log 2 N) :
    Nat.log 2 (kk N) < Nat.log 2 N :=
  Nat.log_lt_of_lt_pow (by have := kk_pos N hN hnf; omega) (kk_lt N hN)

-- The two cases of the recursion

theorem nxt_forced (n : ℕ) (hf : n + 1 = 2 ^ Nat.log 2 (n + 1)) : nxt (pre n) n = n + 1 := by
  unfold nxt
  rw [if_pos hf]

theorem nxt_nonforced (n : ℕ) (hnf : n + 1 ≠ 2 ^ Nat.log 2 (n + 1)) :
    nxt (pre n) n = sInf (S (pre n) (D (kk (n + 1)) + 1)) := by
  have hk1 := kk_pos (n + 1) (by omega) hnf
  have hk2 := kk_lt_self (n + 1) (by omega) hnf
  have hg : (pre n).getD (n + 1 - 2 ^ Nat.log 2 (n + 1) - 1) 0 = a (kk (n + 1)) := by
    have h := getD_pre n (kk (n + 1) - 1) (by omega)
    rw [Nat.sub_add_cancel hk1] at h
    exact h
  show (if n + 1 = 2 ^ Nat.log 2 (n + 1) then n + 1 else
    sInf (S (pre n) (((pre n).getD (n + 1 - 2 ^ Nat.log 2 (n + 1) - 1) 0).divisors.card + 1))) =
    sInf (S (pre n) ((a (kk (n + 1))).divisors.card + 1))
  rw [if_neg hnf, hg]

theorem a_forced (N : ℕ) (hN : 1 ≤ N) (hf : N = 2 ^ Nat.log 2 N) : a N = N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [a_succ, nxt_forced n hf]

theorem a_nonforced (N : ℕ) (hN : 1 ≤ N) (hnf : N ≠ 2 ^ Nat.log 2 N) :
    a N = sInf (S (pre (N - 1)) (D (kk N) + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [a_succ, nxt_nonforced n hnf, Nat.add_sub_cancel]

theorem a_one : a 1 = 1 := a_forced 1 le_rfl (by rw [Nat.log_one_right, pow_zero])

-- The set of candidates is nonempty

theorem le_sum_of_mem' : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.sum
  | [], x, h => by simp at h
  | y :: l, x, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with h | h
    · omega
    · have := le_sum_of_mem' l x h
      omega

theorem card_divisors_prime_pow (q t : ℕ) (hq : q.Prime) : (q ^ t).divisors.card = t + 1 := by
  rw [Nat.divisors_prime_pow hq, Finset.card_map, Finset.card_range]

theorem exists_mem_S (l : List ℕ) (t : ℕ) (ht : 2 ≤ t) : ∃ v, v ∈ S l t := by
  obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (l.sum + 1)
  refine ⟨q ^ (t - 1), mem_S.mpr ⟨?_, ?_⟩⟩
  · rw [card_divisors_prime_pow q (t - 1) hq2]
    omega
  · intro hmem
    have h1 := le_sum_of_mem' l (q ^ (t - 1)) hmem
    have h2 : q ≤ q ^ (t - 1) := Nat.le_self_pow (by omega) q
    omega

theorem a_mem (N : ℕ) (hN : 1 ≤ N) (hnf : N ≠ 2 ^ Nat.log 2 N) (hk : 1 ≤ D (kk N)) :
    a N ∈ S (pre (N - 1)) (D (kk N) + 1) := by
  obtain ⟨v, hv⟩ := exists_mem_S (pre (N - 1)) (D (kk N) + 1) (by omega)
  rw [a_nonforced N hN hnf]
  exact Nat.sInf_mem ⟨v, hv⟩

theorem a_le_of_mem (N : ℕ) (hN : 1 ≤ N) (hnf : N ≠ 2 ^ Nat.log 2 N) (v : ℕ)
    (hv : v ∈ S (pre (N - 1)) (D (kk N) + 1)) : a N ≤ v := by
  rw [a_nonforced N hN hnf]
  exact Nat.sInf_le hv

-- The divisor counts `D N`

theorem D_forced (N : ℕ) (hN : 1 ≤ N) (hf : N = 2 ^ Nat.log 2 N) : D N = Nat.log 2 N + 1 := by
  have h := card_divisors_prime_pow 2 (Nat.log 2 N) Nat.prime_two
  rw [← hf] at h
  show (a N).divisors.card = _
  rw [a_forced N hN hf]
  exact h

theorem D_two_pow (s : ℕ) : D (2 ^ s) = s + 1 := by
  have hlog : Nat.log 2 (2 ^ s) = s := Nat.log_pow Nat.one_lt_two s
  have h := D_forced (2 ^ s) Nat.one_le_two_pow (by rw [hlog])
  rw [hlog] at h
  exact h

theorem D_pos (N : ℕ) : 1 ≤ N → 1 ≤ D N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    by_cases hf : N = 2 ^ Nat.log 2 N
    · have := D_forced N hN hf
      omega
    · have hk := ih (kk N) (kk_lt_self N hN hf) (kk_pos N hN hf)
      have hm := a_mem N hN hf hk
      have h1 := (mem_S.mp hm).1
      show 1 ≤ (a N).divisors.card
      omega

theorem D_nonforced (N : ℕ) (hN : 1 ≤ N) (hnf : N ≠ 2 ^ Nat.log 2 N) : D N = D (kk N) + 1 :=
  (mem_S.mp (a_mem N hN hnf (D_pos (kk N) (kk_pos N hN hnf)))).1

theorem a_pos (N : ℕ) (hN : 1 ≤ N) : 1 ≤ a N := by
  have h := D_pos N hN
  by_contra hc
  have h0 : a N = 0 := by omega
  unfold D at h
  rw [h0, Nat.divisors_zero, Finset.card_empty] at h
  omega

/-- `D N` is at most the bit length of `N`. -/
theorem D_le (N : ℕ) : 1 ≤ N → D N ≤ Nat.log 2 N + 1 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    by_cases hf : N = 2 ^ Nat.log 2 N
    · have := D_forced N hN hf
      omega
    · have h1 := ih (kk N) (kk_lt_self N hN hf) (kk_pos N hN hf)
      have h2 := log_kk_lt N hN hf
      have h3 := D_nonforced N hN hf
      omega

/-- The first index with `t + 1` divisors is `2 ^ t`. -/
theorem pow_le_of_D (N t : ℕ) (hN : 1 ≤ N) (h : D N = t + 1) : 2 ^ t ≤ N := by
  have h1 := D_le N hN
  exact Nat.pow_le_of_le_log (by omega) (by omega)

-- Injectivity

theorem a_ne (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) : a i ≠ a j := by
  intro h
  by_cases hf : j = 2 ^ Nat.log 2 j
  · have hD : D i = Nat.log 2 j + 1 := by
      have h2 := D_forced j (by omega) hf
      show (a i).divisors.card = _
      rw [h]
      exact h2
    have h3 := pow_le_of_D i (Nat.log 2 j) hi hD
    omega
  · have hm := (mem_S.mp (a_mem j (by omega) hf (D_pos (kk j) (kk_pos j (by omega) hf)))).2
    apply hm
    rw [mem_pre]
    exact ⟨i, hi, by omega, h⟩

theorem a_inj (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (h : a i = a j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (a_ne i j hi hlt)
  · exact heq
  · exact absurd h.symm (a_ne j i hj hgt)

-- Surjectivity

theorem idx_log (s M : ℕ) : Nat.log 2 (2 ^ (s + 1 + M) + 2 ^ s) = s + 1 + M := by
  have h0 : 0 < 2 ^ s := Nat.two_pow_pos s
  have h1 : 2 ^ s < 2 ^ (s + 1 + M) := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · rw [pow_succ]
    omega

theorem class_lt (m s N : ℕ) (hs : m.divisors.card = s + 2) (hmiss : ∀ n, 1 ≤ n → a n ≠ m)
    (hN : 1 ≤ N) (hnf : N ≠ 2 ^ Nat.log 2 N) (hk : kk N = 2 ^ s) : a N < m := by
  have hmem : m ∈ S (pre (N - 1)) (D (kk N) + 1) := by
    rw [mem_S, hk, D_two_pow]
    refine ⟨by omega, ?_⟩
    intro hm
    obtain ⟨j, hj1, _, hj3⟩ := (mem_pre _ m).mp hm
    exact hmiss j hj1 hj3
  have hle := a_le_of_mem N hN hnf m hmem
  have hne := hmiss N hN
  omega

theorem surj (m : ℕ) (hm : 1 ≤ m) : ∃ n, 1 ≤ n ∧ a n = m := by
  by_contra hcon
  have hmiss : ∀ n, 1 ≤ n → a n ≠ m := fun n hn h => hcon ⟨n, hn, h⟩
  have h1 : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr (by omega)
  have h2 : m ∈ m.divisors := Nat.mem_divisors_self m (by omega)
  by_cases hc : m.divisors.card ≤ 1
  · have hm1 : m = 1 := Finset.card_le_one.mp hc m h2 1 h1
    exact hmiss 1 le_rfl (by rw [a_one, hm1])
  · obtain ⟨s, hs⟩ : ∃ s, m.divisors.card = s + 2 := ⟨m.divisors.card - 2, by omega⟩
    have h0 : 0 < 2 ^ s := Nat.two_pow_pos s
    have key : ∀ M, a (2 ^ (s + 1 + M) + 2 ^ s) < m := by
      intro M
      have hlt : 2 ^ s < 2 ^ (s + 1 + M) := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
      have hlog := idx_log s M
      exact class_lt m s (2 ^ (s + 1 + M) + 2 ^ s) hs hmiss (by omega) (by rw [hlog]; omega)
        (by unfold kk; rw [hlog]; omega)
    have hmaps : ∀ M ∈ Finset.range (m + 1), a (2 ^ (s + 1 + M) + 2 ^ s) ∈ Finset.range m := by
      intro M _
      rw [Finset.mem_range]
      exact key M
    have hinj : Set.InjOn (fun M => a (2 ^ (s + 1 + M) + 2 ^ s)) ↑(Finset.range (m + 1)) := by
      intro M1 _ M2 _ h
      have h' : a (2 ^ (s + 1 + M1) + 2 ^ s) = a (2 ^ (s + 1 + M2) + 2 ^ s) := h
      have p1 : 0 < 2 ^ (s + 1 + M1) := Nat.two_pow_pos _
      have p2 : 0 < 2 ^ (s + 1 + M2) := Nat.two_pow_pos _
      have h'' := a_inj (2 ^ (s + 1 + M1) + 2 ^ s) (2 ^ (s + 1 + M2) + 2 ^ s)
        (by omega) (by omega) h'
      have h3 : 2 ^ (s + 1 + M1) = 2 ^ (s + 1 + M2) := by omega
      have h4 := Nat.pow_right_injective (le_refl 2) h3
      omega
    have hc2 := Finset.card_le_card_of_injOn (fun M => a (2 ^ (s + 1 + M) + 2 ^ s))
      (by intro M hM; exact hmaps M hM) hinj
    rw [Finset.card_range, Finset.card_range] at hc2
    omega

-- The primes appear in natural order

theorem card_prime (p : ℕ) (hp : p.Prime) : p.divisors.card = 2 := by
  rw [Nat.Prime.divisors hp, Finset.card_pair hp.one_lt.ne]

/-- Inside one divisor class, a non-forced index takes a smaller value than every later index. -/
theorem class_mono (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hnf : i ≠ 2 ^ Nat.log 2 i)
    (hD : D i = D j) : a i < a j := by
  have hmem : a j ∈ S (pre (i - 1)) (D (kk i) + 1) := by
    rw [mem_S]
    refine ⟨?_, ?_⟩
    · exact hD.symm.trans (D_nonforced i hi hnf)
    · intro hmem
      obtain ⟨j', hj1, hj2, hj3⟩ := (mem_pre _ _).mp hmem
      exact a_ne j' j hj1 (by omega) hj3
  have hle := a_le_of_mem i hi hnf (a j) hmem
  have hne := a_ne i j hi hij
  omega

theorem primes_order (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hpi : (a i).Prime)
    (hpj : (a j).Prime) : a i < a j := by
  have hDi : D i = 2 := card_prime (a i) hpi
  have hDj : D j = 2 := card_prime (a j) hpj
  by_cases hfj : j = 2 ^ Nat.log 2 j
  · exfalso
    have h1 := D_forced j (by omega) hfj
    have h2 : Nat.log 2 j = 1 := by omega
    have h3 : j = 2 := by
      rw [h2, pow_one] at hfj
      exact hfj
    have h4 : i = 1 := by omega
    rw [h4, a_one] at hpi
    exact Nat.not_prime_one hpi
  · by_cases hfi : i = 2 ^ Nat.log 2 i
    · have h1 := D_forced i hi hfi
      have h2 : Nat.log 2 i = 1 := by omega
      have h3 : i = 2 := by
        rw [h2, pow_one] at hfi
        exact hfi
      have h4 : a i = 2 := (a_forced i hi hfi).trans h3
      have hne := a_ne i j hi hij
      have h5 := hpj.two_le
      omega
    · exact class_mono i j hi hij hfi (by rw [hDi, hDj])

end OMA.A357601Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a357601.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact OMA.A357601Proof.a_pos
  · exact OMA.A357601Proof.a_inj
  · exact OMA.A357601Proof.surj
  · exact OMA.A357601Proof.primes_order
