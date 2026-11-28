import OMAStatements.S_oeis_a293136

-- Problem: A293136: Irregular triangle T(n,k) read by rows: T(n,k) is the number of strongly unimodal compositions of n (A059618) into k parts.
-- Upstream: formal-conjectures statements/oeis-a293136.lean:0 (declaration OMA.S_oeis_a293136.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let S(k) = sum of min(i+1, k-i) over i < k, so that 4 S(k) + [k even] = (k+1)^2
-- (S(k+2) = S(k) + k + 2). A strongly unimodal composition f with k >= 1 parts and peak p has
-- f(i) >= i+1 for i <= p and f(i) >= k-i for i >= p, hence f(i) >= min(i+1, k-i), and at the peak
-- f >= max(p+1, k-p) >= min + [k even]; so its sum is at least S(k) + [k even]. For k > A293137(n)
-- one has k >= s = floor(sqrt(4n)) and 4 (S(k) + [k even]) >= (k+1)^2 >= (s+1)^2 > 4n: no such
-- composition. For n >= 1 and K = A293137(n) = s - 1, S(K) + [K even] <= n (parity of s^2 <= 4n),
-- and G(i) = min(i+1, K-i), plus n - S(K) - [K even] + [K even] at i = K/2, is a strongly
-- unimodal composition of n into K parts. Row 0 is the empty composition.

namespace K03A293136

open OMA.S_oeis_a293136

/-- S(k) = sum over i < k of min(i+1, k-i). -/
def Smin (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, min (i + 1) (k - i)

theorem Smin_rec (k : ℕ) : Smin (k + 2) = Smin k + (k + 2) := by
  have e1 : Smin (k + 2) = ∑ i ∈ Finset.range (k + 1), min (i + 1) (k + 2 - i) +
      min (k + 1 + 1) (k + 2 - (k + 1)) :=
    Finset.sum_range_succ (fun i => min (i + 1) (k + 2 - i)) (k + 1)
  have e2 : ∑ i ∈ Finset.range (k + 1), min (i + 1) (k + 2 - i) =
      ∑ i ∈ Finset.range k, min (i + 1 + 1) (k + 2 - (i + 1)) + min (0 + 1) (k + 2 - 0) :=
    Finset.sum_range_succ' (fun i => min (i + 1) (k + 2 - i)) k
  have e3 : ∑ i ∈ Finset.range k, min (i + 1 + 1) (k + 2 - (i + 1)) =
      ∑ i ∈ Finset.range k, (min (i + 1) (k - i) + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    omega
  have e5 : ∑ _i ∈ Finset.range k, (1 : ℕ) = k := by simp
  have e4 : ∑ i ∈ Finset.range k, (min (i + 1) (k - i) + 1) = Smin k + k := by
    rw [Finset.sum_add_distrib, e5]
    rfl
  omega

theorem Smin_pair (k : ℕ) : 4 * Smin k + (k + 1) % 2 = (k + 1) * (k + 1) ∧
    4 * Smin (k + 1) + (k + 1 + 1) % 2 = (k + 1 + 1) * (k + 1 + 1) := by
  induction k with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h : Smin (k + 1 + 1) = Smin k + (k + 2) := Smin_rec k
    have h1 := ih.1
    have hsq : (k + 1 + 1 + 1) * (k + 1 + 1 + 1) = (k + 1) * (k + 1) + 4 * k + 8 := by ring
    omega

theorem odd_or_even (k : ℕ) : (∃ m, k = 2 * m + 1) ∨ (∃ m, k = 2 * m) := by
  by_cases h : k % 2 = 1
  · exact Or.inl ⟨k / 2, by omega⟩
  · exact Or.inr ⟨k / 2, by omega⟩

theorem inc_bound (k : ℕ) (f : Fin k → ℕ) (hpos : ∀ i, 0 < f i) (p : ℕ)
    (hinc : ∀ i j : Fin k, i < j → (j : ℕ) ≤ p → f i < f j) :
    ∀ t (ht : t < k), t ≤ p → t + 1 ≤ f ⟨t, ht⟩ := by
  intro t
  induction t with
  | zero =>
    intro ht _
    have h0 := hpos ⟨0, ht⟩
    omega
  | succ t ih =>
    intro ht hp
    have htk : t < k := by omega
    have h1 := ih htk (by omega)
    have h2 : f ⟨t, htk⟩ < f ⟨t + 1, ht⟩ :=
      hinc ⟨t, htk⟩ ⟨t + 1, ht⟩ (Fin.mk_lt_mk.mpr (by omega)) hp
    omega

theorem dec_bound (k : ℕ) (f : Fin k → ℕ) (hpos : ∀ i, 0 < f i) (p : ℕ)
    (hdec : ∀ i j : Fin k, p ≤ (i : ℕ) → i < j → f j < f i) :
    ∀ u t (ht : t < k), t + u + 1 = k → p ≤ t → k - t ≤ f ⟨t, ht⟩ := by
  intro u
  induction u with
  | zero =>
    intro t ht hu _
    have h0 := hpos ⟨t, ht⟩
    omega
  | succ u ih =>
    intro t ht hu hp
    have ht1 : t + 1 < k := by omega
    have h1 := ih (t + 1) ht1 (by omega) (by omega)
    have h2 : f ⟨t + 1, ht1⟩ < f ⟨t, ht⟩ :=
      hdec ⟨t, ht⟩ ⟨t + 1, ht1⟩ hp (Fin.mk_lt_mk.mpr (by omega))
    omega

theorem low (k : ℕ) (hk : 1 ≤ k) (f : Fin k → ℕ) (hpos : ∀ i, 0 < f i) (hsu : SU k f) :
    Smin k + (k + 1) % 2 ≤ ∑ i, f i := by
  obtain ⟨p, hinc, hdec⟩ := hsu
  have hI := inc_bound k f hpos p hinc
  have hD := dec_bound k f hpos p hdec
  have hpt : ∀ i : Fin k, min ((i : ℕ) + 1) (k - (i : ℕ)) ≤ f i := by
    intro i
    have hik : (i : ℕ) < k := i.2
    by_cases hip : (i : ℕ) ≤ p
    · have h1 : (i : ℕ) + 1 ≤ f i := hI i.1 i.2 hip
      omega
    · have h1 : k - (i : ℕ) ≤ f i := hD (k - 1 - i.1) i.1 i.2 (by omega) (by omega)
      omega
  have hq : min p (k - 1) < k := by omega
  have a1 : min p (k - 1) + 1 ≤ f ⟨min p (k - 1), hq⟩ := hI (min p (k - 1)) hq (by omega)
  have a2 : k - min p (k - 1) ≤ f ⟨min p (k - 1), hq⟩ := by
    by_cases hpk : p ≤ k - 1
    · exact hD (k - 1 - min p (k - 1)) (min p (k - 1)) hq (by omega) (by omega)
    · have h0 := hpos ⟨min p (k - 1), hq⟩
      omega
  have hmem : (⟨min p (k - 1), hq⟩ : Fin k) ∈ Finset.univ := Finset.mem_univ _
  have e1 : f ⟨min p (k - 1), hq⟩ +
      ∑ i ∈ Finset.univ.erase (⟨min p (k - 1), hq⟩ : Fin k), f i = ∑ i, f i :=
    Finset.add_sum_erase Finset.univ f hmem
  have e2 : min (min p (k - 1) + 1) (k - min p (k - 1)) +
      ∑ i ∈ Finset.univ.erase (⟨min p (k - 1), hq⟩ : Fin k), min ((i : ℕ) + 1) (k - (i : ℕ)) =
      ∑ i : Fin k, min ((i : ℕ) + 1) (k - (i : ℕ)) :=
    Finset.add_sum_erase Finset.univ (fun i : Fin k => min ((i : ℕ) + 1) (k - (i : ℕ))) hmem
  have hle : ∑ i ∈ Finset.univ.erase (⟨min p (k - 1), hq⟩ : Fin k),
      min ((i : ℕ) + 1) (k - (i : ℕ)) ≤
      ∑ i ∈ Finset.univ.erase (⟨min p (k - 1), hq⟩ : Fin k), f i :=
    Finset.sum_le_sum (fun i _ => hpt i)
  have e3 : ∑ i : Fin k, min ((i : ℕ) + 1) (k - (i : ℕ)) = Smin k :=
    Fin.sum_univ_eq_sum_range (fun i => min (i + 1) (k - i)) k
  omega

/-- The composition used for the last column: min(i+1, K-i), plus a bonus at i = K/2. -/
def G (K e i : ℕ) : ℕ := min (i + 1) (K - i) + if i = K / 2 then e + (K + 1) % 2 else 0

theorem G_pos (K e i : ℕ) (hi : i < K) : 0 < G K e i := by
  unfold G
  split_ifs <;> omega

theorem G_inc (K e i j : ℕ) (hij : i < j) (hj : j ≤ K / 2) : G K e i < G K e j := by
  unfold G
  split_ifs <;> omega

theorem G_dec (K e i j : ℕ) (hi : K / 2 ≤ i) (hij : i < j) (hjK : j < K) :
    G K e j < G K e i := by
  unfold G
  split_ifs <;> omega

theorem G_sum (K e : ℕ) (hK : 1 ≤ K) :
    ∑ i ∈ Finset.range K, G K e i = Smin K + (e + (K + 1) % 2) := by
  unfold G
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr (show K / 2 < K by omega))]
  rfl

theorem exists_comp (n K : ℕ) (hK : 1 ≤ K) (hle : Smin K + (K + 1) % 2 ≤ n) :
    Nonempty {f : Fin K → ℕ // (∀ i, 0 < f i) ∧ ∑ i, f i = n ∧ SU K f} := by
  refine ⟨⟨fun i => G K (n - (Smin K + (K + 1) % 2)) i, ?_, ?_, ?_⟩⟩
  · intro i
    exact G_pos K _ i i.2
  · show ∑ i : Fin K, G K (n - (Smin K + (K + 1) % 2)) i = n
    have hs := G_sum K (n - (Smin K + (K + 1) % 2)) hK
    have e := Fin.sum_univ_eq_sum_range (G K (n - (Smin K + (K + 1) % 2))) K
    rw [e, hs]
    omega
  · unfold SU
    refine ⟨K / 2, ?_, ?_⟩
    · intro i j hij hj
      exact G_inc K _ i j hij hj
    · intro i j hi hij
      exact G_dec K _ i j hi hij j.2

theorem le_n {k n : ℕ} (f : Fin k → ℕ) (hs : ∑ i, f i = n) (i : Fin k) : f i ≤ n := by
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)

theorem finite_comp (n k : ℕ) :
    Finite {f : Fin k → ℕ // (∀ i, 0 < f i) ∧ ∑ i, f i = n ∧ SU k f} := by
  refine Finite.of_injective
    (fun x : {f : Fin k → ℕ // (∀ i, 0 < f i) ∧ ∑ i, f i = n ∧ SU k f} =>
      fun i : Fin k => (⟨x.1 i, Nat.lt_succ_of_le (le_n x.1 x.2.2.1 i)⟩ : Fin (n + 1))) ?_
  intro x y hxy
  apply Subtype.ext
  funext i
  have h := congrArg Fin.val (congrFun hxy i)
  exact h

theorem bound_K (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ A293137 n ∧ Smin (A293137 n) + (A293137 n + 1) % 2 ≤ n := by
  have hA : A293137 n = Nat.sqrt (4 * n) - 1 := by
    unfold A293137
    rw [if_neg (show ¬(n = 0) by omega)]
  have h2 : 2 ≤ Nat.sqrt (4 * n) := Nat.le_sqrt.mpr (by omega)
  have hsq : Nat.sqrt (4 * n) * Nat.sqrt (4 * n) ≤ 4 * n := Nat.sqrt_le (4 * n)
  obtain ⟨K, hK⟩ : ∃ K, Nat.sqrt (4 * n) = K + 1 := ⟨Nat.sqrt (4 * n) - 1, by omega⟩
  rw [hK] at hsq
  have hAK : A293137 n = K := by omega
  rw [hAK]
  have hS := (Smin_pair K).1
  refine ⟨by omega, ?_⟩
  rcases odd_or_even K with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have e : (2 * c + 1 + 1) * (2 * c + 1 + 1) = 4 * ((c + 1) * (c + 1)) := by ring
    omega
  · have e : (2 * c + 1) * (2 * c + 1) = 4 * (c * c + c) + 1 := by ring
    omega

theorem card_ne (n : ℕ) : T n (A293137 n) ≠ 0 := by
  unfold T
  rw [Nat.card_ne_zero]
  refine ⟨?_, finite_comp n (A293137 n)⟩
  by_cases hn : n = 0
  · subst hn
    have h0 : A293137 0 = 0 := by
      unfold A293137
      rw [if_pos rfl]
    rw [h0]
    refine ⟨⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp, ?_⟩⟩
    unfold SU
    exact ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · obtain ⟨h1, h2⟩ := bound_K n (by omega)
    exact exists_comp n (A293137 n) h1 h2

theorem zero_above (n k : ℕ) (hk : A293137 n < k) : T n k = 0 := by
  unfold T
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun x => ?_⟩
  obtain ⟨f, hpos, hsum, hsu⟩ := x
  have hk1 : 1 ≤ k := by omega
  have hlow := low k hk1 f hpos hsu
  have hS := (Smin_pair k).1
  have hks : Nat.sqrt (4 * n) ≤ k := by
    by_cases hn : n = 0
    · subst hn
      simp
    · have hA : A293137 n = Nat.sqrt (4 * n) - 1 := by
        unfold A293137
        rw [if_neg hn]
      omega
  have hlt : 4 * n < (Nat.sqrt (4 * n) + 1) * (Nat.sqrt (4 * n) + 1) := Nat.lt_succ_sqrt (4 * n)
  have hmul : (Nat.sqrt (4 * n) + 1) * (Nat.sqrt (4 * n) + 1) ≤ (k + 1) * (k + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

end K03A293136

open OMA.S_oeis_a293136 K03A293136 in
theorem OMA.solution : type_of% @OMA.S_oeis_a293136.main := by
  intro n
  exact ⟨card_ne n, fun k hk => zero_above n k hk⟩
