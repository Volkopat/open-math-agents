import OMAStatements.S_oeis_a329405
import Mathlib

namespace OMA.A329405Proof

open OMA.S_oeis_a329405

/-- The admissible next terms after the list `l` of the first `n` terms. -/
def S (l : List ℕ) (n : ℕ) : Set ℕ :=
  {k : ℕ | 1 ≤ k ∧ k ∉ l ∧ ∀ x ∈ l.drop (n - 2), ¬ (x + k).Prime}

theorem mem_S {l : List ℕ} {n k : ℕ} :
    k ∈ S l n ↔ 1 ≤ k ∧ k ∉ l ∧ ∀ x ∈ l.drop (n - 2), ¬ (x + k).Prime := Iff.rfl

-- Existence and a linear bound for the next term (one residue class mod 6)

theorem two_elems (L : List ℕ) (h : L.length ≤ 2) : ∃ x y : ℕ, ∀ z ∈ L, z = x ∨ z = y := by
  rcases L with _ | ⟨u, _ | ⟨v, _ | ⟨w, t⟩⟩⟩
  · exact ⟨0, 0, fun z hz => by simp at hz⟩
  · exact ⟨u, u, fun z hz => by simpa using hz⟩
  · exact ⟨u, v, fun z hz => by simpa using hz⟩
  · simp only [List.length_cons] at h
    omega

/-- With `k = (3 * x + 8 * y) % 6 + 6 * (j + 1)`, `x + k` is even and `y + k` is divisible by 3,
both at least 6. -/
theorem cand_good (x y j z : ℕ) (hz : z = x ∨ z = y) :
    ¬ (z + ((3 * x + 8 * y) % 6 + 6 * (j + 1))).Prime := by
  intro hp
  rcases hz with h | h
  · have h2 : 2 ∣ z + ((3 * x + 8 * y) % 6 + 6 * (j + 1)) := by omega
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h' | h' <;> omega
  · have h3 : 3 ∣ z + ((3 * x + 8 * y) % 6 + 6 * (j + 1)) := by omega
    rcases hp.eq_one_or_self_of_dvd 3 h3 with h' | h' <;> omega

theorem exists_cand (l : List ℕ) (c : ℕ) : ∃ j, j ≤ l.length ∧ c + 6 * (j + 1) ∉ l := by
  by_contra hcon
  have hall : ∀ j, j ≤ l.length → c + 6 * (j + 1) ∈ l := by
    intro j hj
    by_contra hj2
    exact hcon ⟨j, hj, hj2⟩
  have hsub : (Finset.range (l.length + 1)).image (fun j => c + 6 * (j + 1)) ⊆ l.toFinset := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    rw [Finset.mem_range] at hj
    rw [List.mem_toFinset]
    exact hall j (by omega)
  have hinj : Function.Injective (fun j => c + 6 * (j + 1)) := by
    intro i j hij
    have h : c + 6 * (i + 1) = c + 6 * (j + 1) := hij
    omega
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at h1
  have h2 : l.toFinset.card ≤ l.length := List.toFinset_card_le (l := l)
  omega

theorem S_bound (l : List ℕ) (n : ℕ) (hl : l.length = n) :
    ∃ k, k ∈ S l n ∧ k ≤ 6 * n + 11 := by
  have hlen : (l.drop (n - 2)).length ≤ 2 := by
    rw [List.length_drop]
    omega
  obtain ⟨x, y, hxy⟩ := two_elems _ hlen
  obtain ⟨j, hj, hnot⟩ := exists_cand l ((3 * x + 8 * y) % 6)
  refine ⟨(3 * x + 8 * y) % 6 + 6 * (j + 1), mem_S.mpr ⟨by omega, hnot, ?_⟩, by omega⟩
  intro z hz
  exact cand_good x y j z (hxy z hz)

-- The greedy sequence

theorem pre_succ (n : ℕ) : pre (n + 1) = pre n ++ [sInf (S (pre n) n)] := rfl

theorem length_pre (n : ℕ) : (pre n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pre_succ, List.length_append, ih, List.length_singleton]

theorem a_succ (n : ℕ) : a (n + 1) = sInf (S (pre n) n) := by
  show (pre (n + 1)).getLastD 0 = _
  rw [pre_succ]
  simp

theorem a_succ_mem (n : ℕ) : a (n + 1) ∈ S (pre n) n := by
  obtain ⟨k, hk, _⟩ := S_bound (pre n) n (length_pre n)
  rw [a_succ]
  exact Nat.sInf_mem ⟨k, hk⟩

theorem a_succ_le (n k : ℕ) (hk : k ∈ S (pre n) n) : a (n + 1) ≤ k := by
  rw [a_succ]
  exact Nat.sInf_le hk

theorem a_succ_bound (n : ℕ) : a (n + 1) ≤ 6 * n + 11 := by
  obtain ⟨k, hk, hb⟩ := S_bound (pre n) n (length_pre n)
  exact le_trans (a_succ_le n k hk) hb

theorem a_le (i : ℕ) : a i ≤ 6 * i + 5 := by
  rcases i with _ | n
  · have h0 : a 0 = 0 := rfl
    omega
  · have := a_succ_bound n
    omega

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

-- The last two entries of `pre (n + 2)`

theorem drop_app (l₁ l₂ : List ℕ) : (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ with
  | nil => rfl
  | cons x t ih => exact ih

theorem pre_two (n : ℕ) : pre (n + 2) = pre n ++ [a (n + 1), a (n + 2)] := by
  show pre (n + 1 + 1) = pre n ++ [a (n + 1), a (n + 1 + 1)]
  rw [pre_succ (n + 1), ← a_succ (n + 1), pre_succ n, ← a_succ n]
  simp

theorem drop_pre_two (n : ℕ) : (pre (n + 2)).drop (n + 2 - 2) = [a (n + 1), a (n + 2)] := by
  have h := drop_app (pre n) [a (n + 1), a (n + 2)]
  rw [length_pre] at h
  rw [pre_two, Nat.add_sub_cancel]
  exact h

/-- Greedy exclusion: if the value `m` never occurs and both `a (n + 1) + m` and `a (n + 2) + m`
are not prime, then `m` was admissible at step `n + 3`, so the chosen term is smaller. -/
theorem block (m : ℕ) (hm : 1 ≤ m) (hmiss : ∀ n, 1 ≤ n → a n ≠ m) (n : ℕ)
    (h1 : ¬ (a (n + 1) + m).Prime) (h2 : ¬ (a (n + 2) + m).Prime) : a (n + 3) < m := by
  have hmS : m ∈ S (pre (n + 2)) (n + 2) := by
    rw [mem_S]
    refine ⟨hm, ?_, ?_⟩
    · intro hmem
      obtain ⟨j, hj1, _, hj3⟩ := (mem_pre _ m).mp hmem
      exact hmiss j hj1 hj3
    · intro x hx
      rw [drop_pre_two] at hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]
        exact h1
      · rcases List.mem_cons.mp h with h' | h'
        · rw [h']
          exact h2
        · simp at h'
  have hle : a (n + 3) ≤ m := a_succ_le (n + 2) m hmS
  have hne := hmiss (n + 3) (by omega)
  omega

-- Choosing one index from each pair {2t+1, 2t+2}

noncomputable def idx (m t : ℕ) : ℕ := if (a (2 * t + 1) + m).Prime then 2 * t + 1 else 2 * t + 2

theorem idx_ge (m t : ℕ) : 2 * t + 1 ≤ idx m t := by
  unfold idx
  split <;> omega

theorem idx_le (m t : ℕ) : idx m t ≤ 2 * t + 2 := by
  unfold idx
  split <;> omega

theorem idx_not_prime (m t : ℕ) (h : ¬ (a (idx m t) + m).Prime) :
    ¬ (a (2 * t + 1) + m).Prime ∧ ¬ (a (2 * t + 2) + m).Prime := by
  unfold idx at h
  by_cases h1 : (a (2 * t + 1) + m).Prime
  · rw [if_pos h1] at h
    exact absurd h1 h
  · rw [if_neg h1] at h
    exact ⟨h1, h⟩

-- A linear prime-counting bound from the primorial bound

/-- The primes up to `x`. -/
def P (x : ℕ) : Finset ℕ := (Finset.range (x + 1)).filter (fun p => p.Prime)

theorem mem_P {x p : ℕ} : p ∈ P x ↔ p < x + 1 ∧ p.Prime := by
  unfold P
  rw [Finset.mem_filter, Finset.mem_range]

theorem prod_P (x : ℕ) : ∏ p ∈ P x, p ≤ 4 ^ x := primorial_le_four_pow x

theorem large_count (x T : ℕ) (hT : T = 4 ^ 13) (s : Finset ℕ) (hs : s ⊆ P x)
    (hTp : ∀ p ∈ s, T ≤ p) : 13 * s.card ≤ x := by
  have h1 : T ^ s.card ≤ ∏ p ∈ s, p := Finset.pow_card_le_prod s (fun p => p) T hTp
  have h2 : ∏ p ∈ s, p ≤ ∏ p ∈ P x, p :=
    Finset.prod_le_prod_of_subset_of_one_le' hs (fun p hp _ => (mem_P.mp hp).2.one_lt.le)
  have h3 := prod_P x
  rw [hT, ← pow_mul] at h1
  have h4 := le_trans h1 (le_trans h2 h3)
  by_contra hcon
  have h5 : 4 ^ (x + 1) ≤ 4 ^ (13 * s.card) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h6 : 0 < 4 ^ x := pow_pos (by norm_num) x
  rw [pow_succ] at h5
  omega

theorem prime_count (x : ℕ) : 13 * (P x).card ≤ x + 13 * (4 ^ 13 + 1) := by
  have key : ∀ T : ℕ, T = 4 ^ 13 → 13 * (P x).card ≤ x + 13 * (T + 1) := by
    intro T hT
    have hsub : P x ⊆ (P x).filter (fun p => p ≤ T) ∪ (P x).filter (fun p => ¬ p ≤ T) := by
      intro p hp
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h : p ≤ T
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hsmall : ((P x).filter (fun p => p ≤ T)).card ≤ T + 1 := by
      have h : (P x).filter (fun p => p ≤ T) ⊆ Finset.range (T + 1) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        rw [Finset.mem_range]
        omega
      have h' := Finset.card_le_card h
      rw [Finset.card_range] at h'
      exact h'
    have hlarge := large_count x T hT ((P x).filter (fun p => ¬ p ≤ T))
      (fun p hp => (Finset.mem_filter.mp hp).1)
      (fun p hp => by
        have h := (Finset.mem_filter.mp hp).2
        omega)
    omega
  exact key _ rfl

-- Surjectivity

theorem surj (m : ℕ) (hm : 1 ≤ m) : ∃ n, 1 ≤ n ∧ a n = m := by
  by_contra hcon
  have hmiss : ∀ n, 1 ≤ n → a n ≠ m := fun n hn h => hcon ⟨n, hn, h⟩
  have key : ∀ N, N ≤ m + (P (12 * N + 5 + m)).card := by
    intro N
    have hsub : Finset.range N ⊆ (Finset.range N).filter (fun t => (a (idx m t) + m).Prime) ∪
        (Finset.range N).filter (fun t => ¬ (a (idx m t) + m).Prime) := by
      intro t ht
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h : (a (idx m t) + m).Prime
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
    have h1 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    rw [Finset.card_range] at h1
    -- indices whose chosen sum is prime: injective into the primes up to 12 N + 5 + m
    have hmapsG : ∀ t ∈ (Finset.range N).filter (fun t => (a (idx m t) + m).Prime),
        a (idx m t) + m ∈ P (12 * N + 5 + m) := by
      intro t ht
      rw [Finset.mem_filter, Finset.mem_range] at ht
      obtain ⟨ht1, ht2⟩ := ht
      rw [mem_P]
      have e1 := a_le (idx m t)
      have e2 := idx_le m t
      exact ⟨by omega, ht2⟩
    have hinjG : Set.InjOn (fun t => a (idx m t) + m)
        ↑((Finset.range N).filter (fun t => (a (idx m t) + m).Prime)) := by
      intro s _ t _ hst
      have h : a (idx m s) + m = a (idx m t) + m := hst
      have e1 := idx_ge m s
      have e2 := idx_le m s
      have e3 := idx_ge m t
      have e4 := idx_le m t
      have h' := a_inj (idx m s) (idx m t) (by omega) (by omega) (by omega)
      omega
    have hG : ((Finset.range N).filter (fun t => (a (idx m t) + m).Prime)).card ≤
        (P (12 * N + 5 + m)).card :=
      Finset.card_le_card_of_injOn (fun t => a (idx m t) + m)
        (by intro t ht; exact hmapsG t ht) hinjG
    -- indices whose chosen sum is not prime: then a (2 t + 3) < m, injective into range m
    have hmapsH : ∀ t ∈ (Finset.range N).filter (fun t => ¬ (a (idx m t) + m).Prime),
        a (2 * t + 3) ∈ Finset.range m := by
      intro t ht
      rw [Finset.mem_filter] at ht
      rw [Finset.mem_range]
      obtain ⟨e1, e2⟩ := idx_not_prime m t ht.2
      exact block m hm hmiss (2 * t) e1 e2
    have hinjH : Set.InjOn (fun t => a (2 * t + 3))
        ↑((Finset.range N).filter (fun t => ¬ (a (idx m t) + m).Prime)) := by
      intro s _ t _ hst
      have h : a (2 * s + 3) = a (2 * t + 3) := hst
      have h' := a_inj (2 * s + 3) (2 * t + 3) (by omega) (by omega) h
      omega
    have hH : ((Finset.range N).filter (fun t => ¬ (a (idx m t) + m).Prime)).card ≤
        (Finset.range m).card :=
      Finset.card_le_card_of_injOn (fun t => a (2 * t + 3))
        (by intro t ht; exact hmapsH t ht) hinjH
    rw [Finset.card_range] at hH
    omega
  have hk := key (14 * m + 6 + 13 * (4 ^ 13 + 1))
  have hc := prime_count (12 * (14 * m + 6 + 13 * (4 ^ 13 + 1)) + 5 + m)
  omega

end OMA.A329405Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a329405.main := by
  refine ⟨?_, ?_, ?_⟩
  · exact OMA.A329405Proof.a_pos
  · exact OMA.A329405Proof.a_inj
  · exact OMA.A329405Proof.surj
