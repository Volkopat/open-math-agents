import OMAStatements.S_oeis_a396794
import Mathlib.Tactic

namespace OMA.P_oeis_a396794

open OMA.S_oeis_a396794

private lemma powSeq_zero_of_lt {g : ℕ → ℤ} (hg0 : g 0 = 0) :
    ∀ k n : ℕ, n < k → powSeq g k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · subst hi0; simp [hg0]
    · rw [ih (n - i) (by omega), mul_zero]

private lemma powSeq_one (g : ℕ → ℤ) (n : ℕ) : powSeq g 1 n = g n := by
  simp only [powSeq]
  have hterm : ∀ i ∈ Finset.range (n + 1), g i * (if n - i = 0 then (1 : ℤ) else 0) =
      if i = n then g n else 0 := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases h : i = n
    · subst h; simp
    · simp [h, show n - i ≠ 0 by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ n,
    if_pos (Finset.mem_range.mpr (Nat.lt_succ_self n))]

private lemma powSeq_diag {g : ℕ → ℤ} (hg0 : g 0 = 0) :
    ∀ k : ℕ, powSeq g k k = (g 1) ^ k := by
  intro k
  induction k with
  | zero => simp [powSeq]
  | succ k ih =>
    simp only [powSeq]
    have hterm : ∀ i ∈ Finset.range (k + 2),
        g i * powSeq g k (k + 1 - i) = if i = 1 then g 1 * (g 1) ^ k else 0 := by
      intro i hi
      have hik : i ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hi0 : i = 0
      · subst hi0; simp [hg0]
      · by_cases hi1 : i = 1
        · subst hi1; simp [ih]
        · rw [if_neg hi1, powSeq_zero_of_lt hg0 k (k + 1 - i) (by omega), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ 1,
      if_pos (Finset.mem_range.mpr (by omega)), pow_succ']

private lemma powSeq_congr {g1 g2 : ℕ → ℤ} {N : ℕ}
    (hg : ∀ i ≤ N, g1 i = g2 i) : ∀ k n : ℕ, n ≤ N → powSeq g1 k n = powSeq g2 k n := by
  intro k
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hg i (le_trans hin hn), ih (n - i) (by omega)]

private lemma powSeq_congr_lt {g1 g2 : ℕ → ℤ} {N : ℕ}
    (hg10 : g1 0 = 0) (hg20 : g2 0 = 0) (hg : ∀ i < N, g1 i = g2 i) :
    ∀ k : ℕ, 2 ≤ k → ∀ n ≤ N, powSeq g1 k n = powSeq g2 k n := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · subst hi0; simp [hg10, hg20]
    · by_cases hin' : i = n
      · subst hin'
        rw [Nat.sub_self, powSeq_zero_of_lt hg10 k 0 (by omega),
          powSeq_zero_of_lt hg20 k 0 (by omega), mul_zero, mul_zero]
      · rw [hg i (by omega), powSeq_congr (N := n - i) (fun j hj => hg j (by omega)) k (n - i) le_rfl]

private lemma comp_congr {f1 f2 g1 g2 : ℕ → ℤ} {N : ℕ}
    (hf : ∀ i ≤ N, f1 i = f2 i) (hg : ∀ i ≤ N, g1 i = g2 i) :
    ∀ n ≤ N, comp f1 g1 n = comp f2 g2 n := by
  intro n hn
  simp only [comp]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [hf k (le_trans hkn hn), powSeq_congr hg k n hn]

private lemma iterComp_congr {f1 f2 : ℕ → ℤ} {N : ℕ}
    (hf : ∀ i ≤ N, f1 i = f2 i) : ∀ r n : ℕ, n ≤ N → iterComp f1 r n = iterComp f2 r n := by
  intro r
  induction r with
  | zero => intro n _; rfl
  | succ r ih => intro n hn; exact comp_congr hf (fun i hi => ih i hi) n hn

private lemma iterComp_zero {f : ℕ → ℤ} (hf0 : f 0 = 0) : ∀ r : ℕ, iterComp f r 0 = 0 := by
  intro r
  induction r with
  | zero => simp [iterComp]
  | succ r _ => simp [iterComp, comp, powSeq, hf0]

private lemma iterComp_one {f : ℕ → ℤ} (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    ∀ r : ℕ, iterComp f r 1 = 1 := by
  intro r
  induction r with
  | zero => simp [iterComp]
  | succ r ih =>
    simp only [iterComp, comp, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hf0, zero_mul, zero_add, hf1, one_mul, powSeq_one, ih]

private lemma comp_split {f g : ℕ → ℤ}
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hg0 : g 0 = 0) (hg1 : g 1 = 1) {n : ℕ} (hn : 2 ≤ n) :
    comp f g n = f n + g n + ∑ k ∈ Finset.Icc 2 (n - 1), f k * powSeq g k n := by
  simp only [comp]
  rw [Finset.sum_range_succ]
  have hn1 : n = (n - 1) + 1 := by omega
  have hn2 : n - 1 = (n - 2) + 1 := by omega
  conv_lhs =>
    arg 1
    rw [hn1, Finset.sum_range_succ', hn2, Finset.sum_range_succ']
  simp only [hf0, zero_mul, add_zero, zero_add, hf1, one_mul, powSeq_one,
    powSeq_diag hg0, hg1, one_pow, mul_one]
  have hmid : ∑ x ∈ Finset.range (n - 2), f (x + 1 + 1) * powSeq g (x + 1 + 1) n =
      ∑ k ∈ Finset.Icc 2 (n - 1), f k * powSeq g k n := by
    refine Finset.sum_bij (fun x _ => x + 2) ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_range, Finset.mem_Icc] at hx ⊢; omega
    · intro _ _ _ _ h; omega
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      exact ⟨k - 2, by omega, by omega⟩
    · intro x _; rfl
  have hsubn : n - 2 + 1 + 1 = n := by omega
  rw [hsubn, hmid]
  ring

private lemma iterComp_trunc_diff {a u : ℕ → ℤ} {n : ℕ} (hn : 2 ≤ n)
    (ha0 : a 0 = 0) (ha1 : a 1 = 1) (hu0 : u 0 = 0) (hu1 : u 1 = 1)
    (hagree : ∀ i < n, a i = u i) (hun : u n = 0) :
    ∀ r : ℕ, iterComp a r n = (r : ℤ) * a n + iterComp u r n := by
  intro r
  induction r with
  | zero => simp [iterComp]
  | succ r ih =>
    change comp a (iterComp a r) n = ((r + 1 : ℕ) : ℤ) * a n + comp u (iterComp u r) n
    rw [comp_split ha0 ha1 (iterComp_zero ha0 r) (iterComp_one ha0 ha1 r) hn,
      comp_split hu0 hu1 (iterComp_zero hu0 r) (iterComp_one hu0 hu1 r) hn, hun, zero_add, ih]
    have hsum : ∑ k ∈ Finset.Icc 2 (n - 1), a k * powSeq (iterComp a r) k n =
        ∑ k ∈ Finset.Icc 2 (n - 1), u k * powSeq (iterComp u r) k n := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkn : k < n := by have := (Finset.mem_Icc.mp hk).2; omega
      rw [hagree k hkn, powSeq_congr_lt (N := n) (iterComp_zero ha0 r) (iterComp_zero hu0 r)
        (fun i hi => iterComp_congr (N := n - 1) (fun j hj => hagree j (by omega)) r i (by omega))
        k hk2 n le_rfl]
    rw [hsum]
    push_cast; ring

/-- If `m ∣ (u i - [i = 1])` for all `i`, then `m ∣ (powSeq u k n - [n = k])`. -/
private lemma dvd_powSeq_sub_delta {m : ℤ} {u : ℕ → ℤ}
    (hu : ∀ i : ℕ, m ∣ u i - (if i = 1 then 1 else 0)) :
    ∀ k n : ℕ, m ∣ powSeq u k n - (if n = k then 1 else 0) := by
  intro k
  induction k with
  | zero =>
    intro n; dsimp [powSeq]; simp
  | succ k ih =>
    intro n
    simp only [powSeq]
    -- Write `u i * powSeq u k (n - i) = (u i - [i=1]) * powSeq u k (n - i) + [i=1] * powSeq u k (n - i)`.
    have hsplit : ∑ i ∈ Finset.range (n + 1), u i * powSeq u k (n - i) - (if n = k + 1 then (1 : ℤ) else 0) =
        (∑ i ∈ Finset.range (n + 1), (u i - if i = 1 then 1 else 0) * powSeq u k (n - i)) +
        ((∑ i ∈ Finset.range (n + 1), (if i = 1 then (1 : ℤ) else 0) * powSeq u k (n - i)) -
          if n = k + 1 then 1 else 0) := by
      rw [← add_sub_assoc, ← Finset.sum_add_distrib]
      have : ∀ i ∈ Finset.range (n + 1),
          (u i - if i = 1 then 1 else 0) * powSeq u k (n - i) +
            (if i = 1 then (1 : ℤ) else 0) * powSeq u k (n - i) =
          u i * powSeq u k (n - i) := fun i _ => by ring
      rw [Finset.sum_congr rfl this]
    rw [hsplit]
    refine dvd_add (Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (hu i) _)) ?_
    have hterm : ∑ i ∈ Finset.range (n + 1), (if i = 1 then (1 : ℤ) else 0) * powSeq u k (n - i) =
        if 1 ≤ n then powSeq u k (n - 1) else 0 := by
      have ht : ∀ i ∈ Finset.range (n + 1),
          (if i = 1 then (1 : ℤ) else 0) * powSeq u k (n - i) =
          if i = 1 then powSeq u k (n - 1) else 0 := by
        intro i _; split_ifs with h <;> simp [h]
      rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' _ 1]
      by_cases hn1 : 1 ≤ n
      · rw [if_pos (Finset.mem_range.mpr (by omega)), if_pos hn1]
      · rw [if_neg (by simp only [Finset.mem_range]; omega), if_neg hn1]
    rw [hterm]
    by_cases hn1 : 1 ≤ n
    · rw [if_pos hn1]
      have hiff : (n - 1 = k) ↔ (n = k + 1) := by omega
      simpa [hiff] using ih (n - 1)
    · rw [if_neg hn1, if_neg (by omega), sub_self]; exact dvd_zero m

/-- Key mod `m^2` lemma: if `u 0 = 0, u 1 = 1` and `m ∣ u i` for `i ≥ 2`, then
`m^2 ∣ (iterComp u r n - ([n = 1] + r * (u n - [n = 1])))`. -/
private lemma sq_dvd_iterComp {m : ℤ} {u : ℕ → ℤ}
    (hu0 : u 0 = 0) (hu1 : u 1 = 1) (hum : ∀ i : ℕ, 2 ≤ i → m ∣ u i) :
    ∀ r n : ℕ, m ^ 2 ∣ iterComp u r n - ((if n = 1 then 1 else 0) + (r : ℤ) * (u n - if n = 1 then 1 else 0)) := by
  have hu_all : ∀ i : ℕ, m ∣ u i - (if i = 1 then 1 else 0) := by
    intro i
    rcases i with _ | _ | i
    · simp [hu0]
    · simp [hu1]
    · simp only [show i + 2 ≠ 1 by omega, ↓reduceIte, sub_zero]
      exact hum (i + 2) (by omega)
  intro r
  induction r with
  | zero =>
    intro n; simp [iterComp]
  | succ r ih =>
    intro n
    have hih_m : ∀ i : ℕ, m ∣ iterComp u r i - (if i = 1 then 1 else 0) := by
      intro i
      have h1 := dvd_trans (dvd_pow_self m (by norm_num : 2 ≠ 0)) (ih i)
      have h2 : m ∣ (r : ℤ) * (u i - if i = 1 then 1 else 0) := dvd_mul_of_dvd_right (hu_all i) _
      have h3 := dvd_add h1 h2
      have heq : iterComp u r i - ((if i = 1 then 1 else 0) + (r : ℤ) * (u i - if i = 1 then 1 else 0)) +
          (r : ℤ) * (u i - if i = 1 then 1 else 0) = iterComp u r i - (if i = 1 then 1 else 0) := by ring
      rwa [heq] at h3
    change m ^ 2 ∣ comp u (iterComp u r) n -
      ((if n = 1 then 1 else 0) + ((r + 1 : ℕ) : ℤ) * (u n - if n = 1 then 1 else 0))
    -- Rewrite `comp u g n = g n + ∑_{k ∈ range (n+1)} (u k - [k=1]) * powSeq g k n`!
    have hcomp_split : comp u (iterComp u r) n =
        iterComp u r n + ∑ k ∈ Finset.range (n + 1), (u k - if k = 1 then 1 else 0) * powSeq (iterComp u r) k n := by
      simp only [comp]
      have h1 : ∑ k ∈ Finset.range (n + 1), u k * powSeq (iterComp u r) k n =
          (∑ k ∈ Finset.range (n + 1), (if k = 1 then (1 : ℤ) else 0) * powSeq (iterComp u r) k n) +
          (∑ k ∈ Finset.range (n + 1), (u k - if k = 1 then 1 else 0) * powSeq (iterComp u r) k n) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => by ring)
      rw [h1]
      congr 1
      have h2 : ∀ k ∈ Finset.range (n + 1),
          (if k = 1 then (1 : ℤ) else 0) * powSeq (iterComp u r) k n =
          if k = 1 then iterComp u r n else 0 := by
        intro k _; split_ifs with h <;> simp [h, powSeq_one]
      rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' _ 1]
      by_cases hn1 : 1 ≤ n
      · rw [if_pos (Finset.mem_range.mpr (by omega))]
      · have hn0 : n = 0 := by omega
        subst hn0; simp [iterComp_zero hu0]
    rw [hcomp_split]
    -- Split off `u n - [n=1]` from the sum!
    have hsum_diff : m ^ 2 ∣
        (∑ k ∈ Finset.range (n + 1), (u k - if k = 1 then 1 else 0) * powSeq (iterComp u r) k n) -
        (u n - if n = 1 then 1 else 0) := by
      have hrew : (∑ k ∈ Finset.range (n + 1), (u k - if k = 1 then 1 else 0) * powSeq (iterComp u r) k n) -
          (u n - if n = 1 then 1 else 0) =
          ∑ k ∈ Finset.range (n + 1),
            (u k - if k = 1 then 1 else 0) * (powSeq (iterComp u r) k n - if n = k then 1 else 0) := by
        have h1 : ∑ k ∈ Finset.range (n + 1),
            (u k - if k = 1 then 1 else 0) * (if n = k then (1 : ℤ) else 0) =
            u n - if n = 1 then 1 else 0 := by
          have ht : ∀ k ∈ Finset.range (n + 1),
              (u k - if k = 1 then 1 else 0) * (if n = k then (1 : ℤ) else 0) =
              if k = n then (u n - if n = 1 then 1 else 0) else 0 := by
            intro k _; by_cases h : k = n
            · subst h; simp
            · simp [h, Ne.symm h]
          rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' _ n,
            if_pos (Finset.mem_range.mpr (Nat.lt_succ_self n))]
        rw [← h1, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => by ring)
      rw [hrew]
      refine Finset.dvd_sum (fun k _ => ?_)
      have h1 := hu_all k
      have h2 := dvd_powSeq_sub_delta hih_m k n
      rw [sq]
      exact mul_dvd_mul h1 h2
    have hcomb := dvd_add (ih n) hsum_diff
    have heq : iterComp u r n - ((if n = 1 then 1 else 0) + (r : ℤ) * (u n - if n = 1 then 1 else 0)) +
        ((∑ k ∈ Finset.range (n + 1), (u k - if k = 1 then 1 else 0) * powSeq (iterComp u r) k n) -
          (u n - if n = 1 then 1 else 0)) =
        iterComp u r n + (∑ k ∈ Finset.range (n + 1), (u k - if k = 1 then 1 else 0) * powSeq (iterComp u r) k n) -
        ((if n = 1 then 1 else 0) + ((r + 1 : ℕ) : ℤ) * (u n - if n = 1 then 1 else 0)) := by
      push_cast; ring
    rwa [heq] at hcomb

/-- For `p + q = m`, `m^2 ∣ mulSeq (iterComp u p) (iterComp u q) (n + 1)` whenever `n ≥ 2` and `m ∣ u i` for `i ≥ 2`. -/
private lemma sq_dvd_mulSeq_iterComp {p q : ℕ} {u : ℕ → ℤ}
    (hu0 : u 0 = 0) (hu1 : u 1 = 1) (hum : ∀ i : ℕ, 2 ≤ i → ((p + q : ℕ) : ℤ) ∣ u i)
    {n : ℕ} (hn : 2 ≤ n) :
    (((p + q : ℕ) : ℤ) ^ 2) ∣ mulSeq (iterComp u p) (iterComp u q) (n + 1) := by
  set m : ℤ := ((p + q : ℕ) : ℤ)
  have hu_all : ∀ i : ℕ, m ∣ u i - (if i = 1 then 1 else 0) := by
    intro i
    rcases i with _ | _ | i
    · simp [hu0]
    · simp [hu1]
    · simp only [show i + 2 ≠ 1 by omega, ↓reduceIte, sub_zero]
      exact hum (i + 2) (by omega)
  have hp_m : ∀ i : ℕ, m ∣ iterComp u p i - (if i = 1 then 1 else 0) := by
    intro i
    have h1 := dvd_trans (dvd_pow_self m (by norm_num : 2 ≠ 0)) (sq_dvd_iterComp hu0 hu1 hum p i)
    have h2 : m ∣ (p : ℤ) * (u i - if i = 1 then 1 else 0) := dvd_mul_of_dvd_right (hu_all i) _
    have h3 := dvd_add h1 h2
    have heq : iterComp u p i - ((if i = 1 then 1 else 0) + (p : ℤ) * (u i - if i = 1 then 1 else 0)) +
        (p : ℤ) * (u i - if i = 1 then 1 else 0) = iterComp u p i - (if i = 1 then 1 else 0) := by ring
    rwa [heq] at h3
  have hq_m : ∀ i : ℕ, m ∣ iterComp u q i - (if i = 1 then 1 else 0) := by
    intro i
    have h1 := dvd_trans (dvd_pow_self m (by norm_num : 2 ≠ 0)) (sq_dvd_iterComp hu0 hu1 hum q i)
    have h2 : m ∣ (q : ℤ) * (u i - if i = 1 then 1 else 0) := dvd_mul_of_dvd_right (hu_all i) _
    have h3 := dvd_add h1 h2
    have heq : iterComp u q i - ((if i = 1 then 1 else 0) + (q : ℤ) * (u i - if i = 1 then 1 else 0)) +
        (q : ℤ) * (u i - if i = 1 then 1 else 0) = iterComp u q i - (if i = 1 then 1 else 0) := by ring
    rwa [heq] at h3
  -- Expand `mulSeq` around `i = 1`, `i = n`, and middle terms `2 ≤ i ≤ n - 1`!
  simp only [mulSeq]
  have hsplit : ∑ i ∈ Finset.range (n + 2), iterComp u p i * iterComp u q (n + 1 - i) =
      iterComp u q n + iterComp u p n +
      ∑ i ∈ Finset.Icc 2 (n - 1), iterComp u p i * iterComp u q (n + 1 - i) := by
    rw [Finset.sum_range_succ, Nat.sub_self, iterComp_zero hu0, mul_zero, add_zero]
    rw [Finset.sum_range_succ, show n + 1 - n = 1 by omega, iterComp_one hu0 hu1, mul_one]
    have hn1 : n = (n - 1) + 1 := by omega
    have hn2 : n - 1 = (n - 2) + 1 := by omega
    conv_lhs =>
      arg 1
      rw [hn1, Finset.sum_range_succ', hn2, Finset.sum_range_succ']
    simp only [iterComp_zero hu0, zero_mul, add_zero, zero_add, iterComp_one hu0 hu1, one_mul]
    have hsub1 : n - 2 + 1 + 1 + 1 - 1 = n := by omega
    have hsub2 : n - 2 + 1 + 1 + 1 = n + 1 := by omega
    rw [hsub1, hsub2]
    have hmid : ∑ x ∈ Finset.range (n - 2), iterComp u p (x + 1 + 1) * iterComp u q (n + 1 - (x + 1 + 1)) =
        ∑ i ∈ Finset.Icc 2 (n - 1), iterComp u p i * iterComp u q (n + 1 - i) := by
      refine Finset.sum_bij (fun x _ => x + 2) ?_ ?_ ?_ ?_
      · intro x hx; simp only [Finset.mem_range, Finset.mem_Icc] at hx ⊢; omega
      · intro _ _ _ _ h; omega
      · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
        exact ⟨i - 2, by omega, by omega⟩
      · intro x _; rfl
    rw [hmid]; ring
  rw [hsplit]
  refine dvd_add ?_ (Finset.dvd_sum (fun i hi => ?_))
  · -- `m^2 ∣ iterComp u q n + iterComp u p n`!
    have h1 := sq_dvd_iterComp hu0 hu1 hum p n
    have h2 := sq_dvd_iterComp hu0 hu1 hum q n
    have hn1 : n ≠ 1 := by omega
    simp only [hn1, ↓reduceIte, zero_add, sub_zero] at h1 h2
    have h3 := dvd_add h2 h1
    have h4 : m ^ 2 ∣ ((q : ℤ) * u n + (p : ℤ) * u n) := by
      have heq : (q : ℤ) * u n + (p : ℤ) * u n = m * u n := by dsimp [m]; ring
      rw [heq, sq]
      exact mul_dvd_mul_left m (hum n hn)
    have h5 := dvd_add h3 h4
    have heq : (iterComp u q n - (q : ℤ) * u n) + (iterComp u p n - (p : ℤ) * u n) +
        ((q : ℤ) * u n + (p : ℤ) * u n) = iterComp u q n + iterComp u p n := by ring
    rwa [heq] at h5
  · -- For `2 ≤ i ≤ n - 1`, both `i ≠ 1` and `n + 1 - i ≠ 1`, so `m ∣ iterComp u p i` and `m ∣ iterComp u q (n+1-i)`!
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have hin : i ≤ n - 1 := (Finset.mem_Icc.mp hi).2
    have h1 := hp_m i
    have h2 := hq_m (n + 1 - i)
    simp only [show i ≠ 1 by omega, show n + 1 - i ≠ 1 by omega, ↓reduceIte, sub_zero] at h1 h2
    rw [sq]
    exact mul_dvd_mul h1 h2

private lemma prove_a396794 (a : ℕ → ℤ) (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (harec : ∀ n : ℕ, mulSeq (iterComp a 1) (iterComp a 3) n =
      (if n = 2 then 1 else 0) + (if n = 3 then 16 else 0))
    (n : ℕ) (hn : 2 ≤ n) : a n ≡ 0 [ZMOD 4] := by
  have hdvd : ∀ k : ℕ, 2 ≤ k → (4 : ℤ) ∣ a k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk2
      let u : ℕ → ℤ := fun i => if i < k then a i else 0
      have hu0 : u 0 = 0 := by dsimp [u]; rw [if_pos (by omega), ha0]
      have hu1 : u 1 = 1 := by dsimp [u]; rw [if_pos (by omega), ha1]
      have hun : u k = 0 := by dsimp [u]; rw [if_neg (lt_irrefl k)]
      have hagree : ∀ i < k, a i = u i := fun i hi => by dsimp [u]; rw [if_pos hi]
      have hum : ∀ i : ℕ, 2 ≤ i → (((1 + 3 : ℕ) : ℤ)) ∣ u i := by
        intro i hi2
        dsimp [u]
        by_cases hik : i < k
        · rw [if_pos hik]; simpa using ih i hik hi2
        · rw [if_neg hik]; exact dvd_zero _
      -- Compare `mulSeq (iterComp a 1) (iterComp a 3) (k + 1)` with `u`!
      have hdiff : mulSeq (iterComp a 1) (iterComp a 3) (k + 1) =
          4 * a k + mulSeq (iterComp u 1) (iterComp u 3) (k + 1) := by
        have hsplit : ∀ f : ℕ → ℤ, f 0 = 0 → f 1 = 1 →
            mulSeq (iterComp f 1) (iterComp f 3) (k + 1) =
            iterComp f 3 k + iterComp f 1 k +
            ∑ i ∈ Finset.Icc 2 (k - 1), iterComp f 1 i * iterComp f 3 (k + 1 - i) := by
          intro f hf0 hf1
          simp only [mulSeq]
          rw [Finset.sum_range_succ, Nat.sub_self, iterComp_zero hf0, mul_zero, add_zero]
          rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega, iterComp_one hf0 hf1, mul_one]
          have hk1 : k = (k - 1) + 1 := by omega
          have hk2' : k - 1 = (k - 2) + 1 := by omega
          conv_lhs =>
            arg 1
            rw [hk1, Finset.sum_range_succ', hk2', Finset.sum_range_succ']
          simp only [iterComp_zero hf0, zero_mul, add_zero, zero_add, iterComp_one hf0 hf1, one_mul]
          have hsub1 : k - 2 + 1 + 1 + 1 - 1 = k := by omega
          have hsub2 : k - 2 + 1 + 1 + 1 = k + 1 := by omega
          rw [hsub1, hsub2]
          have hmid : ∑ x ∈ Finset.range (k - 2), iterComp f 1 (x + 1 + 1) * iterComp f 3 (k + 1 - (x + 1 + 1)) =
              ∑ i ∈ Finset.Icc 2 (k - 1), iterComp f 1 i * iterComp f 3 (k + 1 - i) := by
            refine Finset.sum_bij (fun x _ => x + 2) ?_ ?_ ?_ ?_
            · intro x hx; simp only [Finset.mem_range, Finset.mem_Icc] at hx ⊢; omega
            · intro _ _ _ _ h; omega
            · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
              exact ⟨i - 2, by omega, by omega⟩
            · intro x _; rfl
          rw [hmid]; ring
        rw [hsplit a ha0 ha1, hsplit u hu0 hu1,
          iterComp_trunc_diff hk2 ha0 ha1 hu0 hu1 hagree hun 1,
          iterComp_trunc_diff hk2 ha0 ha1 hu0 hu1 hagree hun 3]
        have hmid_eq : ∑ i ∈ Finset.Icc 2 (k - 1), iterComp a 1 i * iterComp a 3 (k + 1 - i) =
            ∑ i ∈ Finset.Icc 2 (k - 1), iterComp u 1 i * iterComp u 3 (k + 1 - i) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
          have hik : i ≤ k - 1 := (Finset.mem_Icc.mp hi).2
          rw [iterComp_congr (N := k - 1) (fun j hj => hagree j (by omega)) 1 i (by omega),
              iterComp_congr (N := k - 1) (fun j hj => hagree j (by omega)) 3 (k + 1 - i) (by omega)]
        rw [hmid_eq]
        ring
      have h9u : (16 : ℤ) ∣ mulSeq (iterComp u 1) (iterComp u 3) (k + 1) := by
        simpa using sq_dvd_mulSeq_iterComp (p := 1) (q := 3) hu0 hu1 hum hk2
      have h9rhs : (16 : ℤ) ∣ mulSeq (iterComp a 1) (iterComp a 3) (k + 1) := by
        rw [harec (k + 1), if_neg (by omega), zero_add]
        split_ifs <;> norm_num
      have h9a : (16 : ℤ) ∣ 4 * a k := by
        have hsub := dvd_sub h9rhs h9u
        rwa [hdiff, add_sub_cancel_right] at hsub
      obtain ⟨t, ht⟩ := h9a
      exact ⟨t, by linarith⟩
  have h0 : (4 : ℤ) ∣ 0 - a n := by
    rw [zero_sub, dvd_neg]
    exact hdvd n hn
  exact Int.modEq_iff_dvd.mpr h0

end OMA.P_oeis_a396794

theorem OMA.solution : type_of% @OMA.S_oeis_a396794.main :=
  OMA.P_oeis_a396794.prove_a396794
