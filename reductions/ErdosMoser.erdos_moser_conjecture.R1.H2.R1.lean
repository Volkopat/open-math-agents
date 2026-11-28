import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1

-- Reduction ErdosMoser.erdos_moser_conjecture.R1.H2.R1 of step ErdosMoser.erdos_moser_conjecture.R1.H2
-- Credit: @rickmanelius
-- main proves, for a solution of S_k(m) = m ^ k with k even and k > 0:
--   k ≥ 2 and m ≥ 4 (m = 1, 2, 3 checked directly);
--   k + 2 ≤ m: if m ≤ k + 1, Bernoulli gives 2 i^k ≤ (i + 1)^k for i ≤ k, so 2^j (m - j)^k ≤ m^k
--   and S_k(m) ≤ (1 - 2^(1-m)) m^k < m^k (Krzysztofek 1966 has k + 2 < m);
--   m ≤ 2k + 1: (m - 1)^(k+1) ≤ (k + 1) S_k(m) (integral comparison by telescoping) and
--   m^k (m - k) ≤ m (m - 1)^k (Bernoulli) give (m - 1)(m - k) ≤ m (k + 1);
--   m ≡ 3 (mod 8): m is odd by a 2-adic count (Σ_{i < 2^a} i^k ≡ 2^(a-1) mod 2^a), m ≢ 0 (mod 4)
--   by parity, and m ≢ 7 (mod 8) since then 8 ∣ m + 1 and S_k(m + 1) = 2 m^k fails mod 8;
--   no prime p ∣ m has (p - 1) ∣ k: for odd p the same count gives Σ_{i < p^a} i^k ≡ -p^(a-1)
--   (mod p^a) when (p - 1) ∣ k (part of Moree, te Riele, Urbanowicz 1994); in particular 3 ∤ m;
--   Moser (1953), all four relations, prime by prime, from Σ_{x : ZMod p} x^k = -[(p - 1) ∣ k]:
--     p ∣ m - 1:          (p - 1) ∣ k and p ∣ (m - 1)/p + 1   (S_k(m) = m^k, m ≡ 1);
--     p ∣ m + 1, p odd:   (p - 1) ∣ k and p ∣ (m + 1)/p + 2   (S_k(m + 1) = 2 m^k, m ≡ -1);
--     p ∣ 2m - 1:         (p - 1) ∣ k and p ∣ (2m - 1)/p + 2  (pair 2i + 1 with 2(m - 1 - i));
--     p ∣ 2m + 1:         (p - 1) ∣ k and p ∣ (2m + 1)/p + 4  (pair 2i + 1 with 2(m - i));
--   hence m - 1, (m + 1)/4, 2m - 1, 2m + 1 are squarefree.
-- These match Moser (1953) and Moree (2013, Rocky Mountain J. Math. 43, 1707-1737):
-- m ≡ 3 (mod 8), m ≡ ±1 (mod 3).
-- What remains is split by the residue of m mod 3, the first prime where the cases differ:
-- H1 (m ≡ 1 mod 3): 3 ∣ m - 1 and 3 ∣ 2m + 1; Moser's relation at p = 3 then gives m ≡ 7 (mod 9);
-- H2 (m ≡ 2 mod 3): 3 ∣ m + 1 and 3 ∣ 2m - 1; Moser's relation at p = 3 then gives m ≡ 2 (mod 9).
-- Each keeps the equation.

namespace OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R1

/-- Case `m ≡ 1 (mod 3)`, hence `m ≡ 7 (mod 9)`: no solution of `S_k(m) = m ^ k` with `k` even,
`k ≥ 2`, `m ≥ 4`, `k + 2 ≤ m ≤ 2 k + 1`, `m ≡ 3 (mod 8)`, `m - 1`, `(m + 1) / 4`, `2 m - 1`,
`2 m + 1` squarefree, Moser's four
relations at every prime dividing `m - 1`, `m + 1` (odd primes), `2 m - 1`, `2 m + 1`, and
`(p - 1) ∤ k` for every prime `p ∣ m`. -/
def H1 : Prop := ∀ k m : ℕ, Even k → 2 ≤ k → 4 ≤ m → k + 2 ≤ m → m ≤ 2 * k + 1 →
  m % 8 = 3 → m % 9 = 7 →
  Squarefree (m - 1) → Squarefree ((m + 1) / 4) → Squarefree (2 * m - 1) →
  Squarefree (2 * m + 1) →
  (∀ p : ℕ, p.Prime → p ∣ m - 1 → (p - 1) ∣ k ∧ p ∣ (m - 1) / p + 1) →
  (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m + 1 → (p - 1) ∣ k ∧ p ∣ (m + 1) / p + 2) →
  (∀ p : ℕ, p.Prime → p ∣ 2 * m - 1 → (p - 1) ∣ k ∧ p ∣ (2 * m - 1) / p + 2) →
  (∀ p : ℕ, p.Prime → p ∣ 2 * m + 1 → (p - 1) ∣ k ∧ p ∣ (2 * m + 1) / p + 4) →
  (∀ p : ℕ, p.Prime → p ∣ m → ¬ (p - 1) ∣ k) →
  ErdosMoser.powerSum k m ≠ m ^ k

/-- Case `m ≡ 2 (mod 3)`, hence `m ≡ 2 (mod 9)`: no solution of `S_k(m) = m ^ k` with `k` even,
`k ≥ 2`, `m ≥ 4`, `k + 2 ≤ m ≤ 2 k + 1`, `m ≡ 3 (mod 8)`, `m - 1`, `(m + 1) / 4`, `2 m - 1`,
`2 m + 1` squarefree, Moser's four
relations at every prime dividing `m - 1`, `m + 1` (odd primes), `2 m - 1`, `2 m + 1`, and
`(p - 1) ∤ k` for every prime `p ∣ m`. -/
def H2 : Prop := ∀ k m : ℕ, Even k → 2 ≤ k → 4 ≤ m → k + 2 ≤ m → m ≤ 2 * k + 1 →
  m % 8 = 3 → m % 9 = 2 →
  Squarefree (m - 1) → Squarefree ((m + 1) / 4) → Squarefree (2 * m - 1) →
  Squarefree (2 * m + 1) →
  (∀ p : ℕ, p.Prime → p ∣ m - 1 → (p - 1) ∣ k ∧ p ∣ (m - 1) / p + 1) →
  (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m + 1 → (p - 1) ∣ k ∧ p ∣ (m + 1) / p + 2) →
  (∀ p : ℕ, p.Prime → p ∣ 2 * m - 1 → (p - 1) ∣ k ∧ p ∣ (2 * m - 1) / p + 2) →
  (∀ p : ℕ, p.Prime → p ∣ 2 * m + 1 → (p - 1) ∣ k ∧ p ∣ (2 * m + 1) / p + 4) →
  (∀ p : ℕ, p.Prime → p ∣ m → ¬ (p - 1) ∣ k) →
  ErdosMoser.powerSum k m ≠ m ^ k

lemma powerSum_at_one (k : ℕ) : ErdosMoser.powerSum k 1 = 0 := by
  unfold ErdosMoser.powerSum
  simp

lemma powerSum_at_two (k : ℕ) : ErdosMoser.powerSum k 2 = 1 := by
  unfold ErdosMoser.powerSum
  rw [show Finset.Ico 1 2 = {1} from by decide, Finset.sum_singleton, one_pow]

lemma powerSum_at_three (k : ℕ) : ErdosMoser.powerSum k 3 = 1 + 2 ^ k := by
  unfold ErdosMoser.powerSum
  rw [show Finset.Ico 1 3 = {1, 2} from by decide, Finset.sum_pair (by norm_num), one_pow]

lemma one_add_two_pow_lt (k : ℕ) (hk : 2 ≤ k) : 1 + 2 ^ k < 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ]
    omega

/-- `m ^ k ≡ m (mod 2)` for `k > 0`. -/
lemma pow_mod_two' (m k : ℕ) (hk : 0 < k) : m ^ k % 2 = m % 2 := by
  rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [h, zero_pow (by omega)]
    norm_num
  · rw [h, one_pow]
    norm_num

/-- `S_k(m) ≡ ⌊m / 2⌋ (mod 2)` for `k > 0`: it counts the odd terms. -/
lemma powerSum_mod_two (k : ℕ) (hk : 0 < k) (m : ℕ) :
    ErdosMoser.powerSum k m % 2 = (m / 2) % 2 := by
  induction m with
  | zero => simp [ErdosMoser.powerSum]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [ErdosMoser.powerSum]
    · have hs : ErdosMoser.powerSum k (n + 1) = ErdosMoser.powerSum k n + n ^ k := by
        unfold ErdosMoser.powerSum
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n)]
      rw [hs, Nat.add_mod, ih, pow_mod_two' n k hk]
      omega

/-- A solution with `k > 0` has `m % 4 = 0` or `m % 4 = 3`. -/
lemma mod_four_of_solution {k m : ℕ} (hk : 0 < k) (h : ErdosMoser.powerSum k m = m ^ k) :
    m % 4 = 0 ∨ m % 4 = 3 := by
  have hpar := powerSum_mod_two k hk m
  rw [h, pow_mod_two' m k hk] at hpar
  have e1 := Nat.div_add_mod m 2
  obtain ⟨q, hq⟩ : ∃ q, q = m / 2 := ⟨_, rfl⟩
  rw [← hq] at hpar e1
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with r | r | r | r
  · exact Or.inl r
  · exfalso
    omega
  · exfalso
    omega
  · exact Or.inr r

lemma powerSum_eq_range (k m : ℕ) (hk : 0 < k) :
    ErdosMoser.powerSum k m = ∑ i ∈ Finset.range m, i ^ k := by
  unfold ErdosMoser.powerSum
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm, zero_pow (by omega), zero_add]

/-- `Σ_{i < p} (i : ZMod p) ^ k = Σ_{x : ZMod p} x ^ k`. -/
lemma sum_range_cast_eq_univ (p k : ℕ) [NeZero p] :
    ∑ i ∈ Finset.range p, ((i : ZMod p) ^ k) = ∑ x : ZMod p, x ^ k := by
  refine Finset.sum_nbij' (fun i : ℕ => (i : ZMod p)) (fun x : ZMod p => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a ha
    have ha' : a < p := Finset.mem_range.mp ha
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha']
  · intro a _
    exact ZMod.natCast_zmod_val a
  · intro a _
    rfl

/-- Periodicity: `Σ_{i < p t} (i : ZMod p) ^ k = t * Σ_{i < p} (i : ZMod p) ^ k`. -/
lemma sum_range_mul_cast (p k t : ℕ) :
    ∑ i ∈ Finset.range (p * t), ((i : ZMod p) ^ k) =
      t * ∑ i ∈ Finset.range p, ((i : ZMod p) ^ k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hx : ∀ x ∈ Finset.range p, (((p * t + x : ℕ) : ZMod p) ^ k) = ((x : ZMod p) ^ k) := by
      intro x _
      push_cast
      rw [ZMod.natCast_self, zero_mul, zero_add]
    rw [Finset.sum_congr rfl hx]
    push_cast
    ring

/-- Power sums over `ZMod p` (`p` prime, `k > 0`): `-1` if `(p - 1) ∣ k`, else `0`. -/
lemma sum_zmod_pow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    ∑ x : ZMod p, x ^ k = if p - 1 ∣ k then -1 else 0 := by
  classical
  have key := FiniteField.sum_pow_units (ZMod p) k
  rw [ZMod.card] at key
  rw [← key]
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : Finset.univ.map φ = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, φ]
    exact isUnit_iff_ne_zero
  calc ∑ x : ZMod p, x ^ k = ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ k := by
        rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ, Finset.sum_singleton,
          zero_pow (by omega), add_zero]
    _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ k) := by
        simp [φ, ← hmap, Finset.univ.sum_map φ]

/-- Moser 1953: at a prime `p ∣ m - 1`, a solution has `(p - 1) ∣ k` and `p ∣ (m - 1) / p + 1`. -/
lemma moser_prime (k m p : ℕ) (hk : 0 < k) (hp : p.Prime) (hpm : p ∣ m - 1) (hm : 2 ≤ m)
    (h : ErdosMoser.powerSum k m = m ^ k) : (p - 1) ∣ k ∧ p ∣ (m - 1) / p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hpm
  have hmt : m = p * t + 1 := by omega
  have hdiv : (m - 1) / p = t := by rw [ht, Nat.mul_div_cancel_left t hp.pos]
  rw [hdiv]
  have hcast : ((ErdosMoser.powerSum k m : ℕ) : ZMod p) = ((m ^ k : ℕ) : ZMod p) := by rw [h]
  rw [powerSum_eq_range k m hk, hmt, Finset.sum_range_succ] at hcast
  push_cast at hcast
  rw [sum_range_mul_cast, sum_range_cast_eq_univ, sum_zmod_pow p k hk, ZMod.natCast_self,
    zero_mul, zero_add, zero_pow (by omega), add_zero, one_pow] at hcast
  by_cases hdk : p - 1 ∣ k
  · rw [if_pos hdk] at hcast
    refine ⟨hdk, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    linear_combination -hcast
  · rw [if_neg hdk, mul_zero] at hcast
    exact absurd hcast zero_ne_one

/-- A solution has `m - 1` squarefree. -/
lemma squarefree_of_solution (k m : ℕ) (hk : 0 < k) (hm : 2 ≤ m)
    (h : ErdosMoser.powerSum k m = m ^ k) : Squarefree (m - 1) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpm1 : p ∣ m - 1 := Dvd.dvd.trans (dvd_mul_right p p) hpp
  obtain ⟨_, h2⟩ := moser_prime k m p hk hp hpm1 hm h
  have h3 : p ∣ (m - 1) / p := by
    obtain ⟨c, hc⟩ := hpp
    rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    exact dvd_mul_right p c
  have h4 : p ∣ 1 := (Nat.dvd_add_right h3).mp h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

/-- `(2 ^ a + i) ^ k ≡ i ^ k (mod 2 ^ (a + 1))` for even `k` and `a ≥ 1`. -/
lemma two_adic_shift (a i k : ℕ) (ha : 1 ≤ a) (hk : Even k) :
    (2 ^ a + i) ^ k ≡ i ^ k [MOD 2 ^ (a + 1)] := by
  obtain ⟨j, rfl⟩ := hk
  have h2 : (2 ^ a + i) ^ 2 ≡ i ^ 2 [MOD 2 ^ (a + 1)] := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have e : (2 ^ (b + 1) + i) ^ 2 = i ^ 2 + 2 ^ (b + 1 + 1) * (2 ^ b + i) := by ring
    rw [e]
    exact Nat.add_mul_mod_self_left _ _ _
  rw [← two_mul, pow_mul, pow_mul]
  exact h2.pow j

/-- `Σ_{i < 2^a} i ^ k ≡ 2 ^ (a - 1) (mod 2 ^ a)` for even `k > 0` and `a ≥ 1`. -/
lemma two_adic_sum (k : ℕ) (hk : Even k) (hk0 : 0 < k) (a : ℕ) (ha : 1 ≤ a) :
    ∑ i ∈ Finset.range (2 ^ a), i ^ k ≡ 2 ^ (a - 1) [MOD 2 ^ a] := by
  induction a, ha using Nat.le_induction with
  | base =>
    have e : ∑ i ∈ Finset.range (2 ^ 1), i ^ k = 1 := by
      simp [Finset.sum_range_succ, zero_pow (by omega : k ≠ 0)]
    rw [e]
    rfl
  | succ a ha ih =>
    have hsplit : ∑ i ∈ Finset.range (2 ^ (a + 1)), i ^ k =
        ∑ i ∈ Finset.range (2 ^ a), i ^ k + ∑ i ∈ Finset.range (2 ^ a), (2 ^ a + i) ^ k := by
      rw [show 2 ^ (a + 1) = 2 ^ a + 2 ^ a by ring, Finset.sum_range_add]
    rw [hsplit, show a + 1 - 1 = a by omega]
    have hshift : ∑ i ∈ Finset.range (2 ^ a), (2 ^ a + i) ^ k ≡
        ∑ i ∈ Finset.range (2 ^ a), i ^ k [MOD 2 ^ (a + 1)] := by
      unfold Nat.ModEq
      rw [Finset.sum_nat_mod, Finset.sum_nat_mod (Finset.range (2 ^ a)) _ (fun i => i ^ k)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact two_adic_shift a i k ha hk
    have h2 := Nat.ModEq.mul_left' 2 ih
    have e1 : 2 * 2 ^ (a - 1) = 2 ^ a := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e1, show 2 * 2 ^ a = 2 ^ (a + 1) by ring] at h2
    calc ∑ i ∈ Finset.range (2 ^ a), i ^ k + ∑ i ∈ Finset.range (2 ^ a), (2 ^ a + i) ^ k
        ≡ ∑ i ∈ Finset.range (2 ^ a), i ^ k + ∑ i ∈ Finset.range (2 ^ a), i ^ k
          [MOD 2 ^ (a + 1)] := Nat.ModEq.add_left _ hshift
      _ = 2 * ∑ i ∈ Finset.range (2 ^ a), i ^ k := by ring
      _ ≡ 2 ^ a [MOD 2 ^ (a + 1)] := h2

/-- `Σ_{i < 2^a t} (i : ZMod 2^a) ^ k = t * 2 ^ (a - 1)` for even `k > 0`, `a ≥ 1`. -/
lemma two_adic_block (k : ℕ) (hk : Even k) (hk0 : 0 < k) (a t : ℕ) (ha : 1 ≤ a) :
    ((∑ i ∈ Finset.range (2 ^ a * t), i ^ k : ℕ) : ZMod (2 ^ a)) =
      (t : ZMod (2 ^ a)) * ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) := by
  rw [Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [sum_range_mul_cast]
  congr 1
  have h2a := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (two_adic_sum k hk hk0 a ha)
  rw [Nat.cast_sum] at h2a
  simp only [Nat.cast_pow] at h2a ⊢
  exact h2a

/-- A solution with even `k > 0` has `m` odd (2-adic valuation argument). -/
lemma m_odd_of_solution (k m : ℕ) (hk : Even k) (hk0 : 0 < k) (hm : 0 < m)
    (h : ErdosMoser.powerSum k m = m ^ k) : ¬ 2 ∣ m := by
  intro h2m
  obtain ⟨a, t, ht, hmt⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) 2 (by norm_num)
  have ha : 1 ≤ a := by
    by_contra ha0
    have a0 : a = 0 := by omega
    rw [a0, pow_zero, one_mul] at hmt
    exact ht (hmt ▸ h2m)
  have hR : ((m ^ k : ℕ) : ZMod (2 ^ a)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.trans ⟨t, hmt⟩ (dvd_pow_self m (by omega))
  have hL : ((ErdosMoser.powerSum k m : ℕ) : ZMod (2 ^ a)) =
      (t : ZMod (2 ^ a)) * ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) := by
    rw [powerSum_eq_range k m hk0, hmt]
    exact two_adic_block k hk hk0 a t ha
  have key : ((t * 2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) = 0 := by
    rw [Nat.cast_mul, ← hL, h]
    exact hR
  rw [ZMod.natCast_eq_zero_iff] at key
  have e : 2 ^ a = 2 * 2 ^ (a - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [e] at key
  exact ht (Nat.dvd_of_mul_dvd_mul_right (by positivity) key)

/-- Odd `m`, even `k`: `m ^ k ≡ 1 (mod 8)`. -/
lemma pow_mod_eight (m k : ℕ) (hm : ¬ 2 ∣ m) (hk : Even k) : m ^ k % 8 = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [← two_mul, pow_mul, Nat.pow_mod]
  have h8 : m ^ 2 % 8 = 1 := by
    rw [Nat.pow_mod]
    have : m % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have h1 : m % 2 = 1 := by omega
    interval_cases hr : m % 8 <;> omega
  rw [h8, one_pow]
  norm_num

/-- A solution with even `k > 0` and `m ≡ 3 (mod 4)` has `m ≡ 3 (mod 8)`: otherwise
`8 ∣ m + 1` and `S_k(m + 1) = 2 m ^ k` is `≡ 4 w` and `≡ 2 (mod 8)` at once. -/
lemma mod_eight_of_solution (k m : ℕ) (hk : Even k) (hk0 : 0 < k) (hm : 0 < m)
    (h4 : m % 4 = 3) (h : ErdosMoser.powerSum k m = m ^ k) : m % 8 = 3 := by
  by_contra hne
  have h7 : m % 8 = 7 := by omega
  obtain ⟨w, hw⟩ : 8 ∣ m + 1 := by omega
  have hmo : ¬ 2 ∣ m := by omega
  have hS : ErdosMoser.powerSum k (m + 1) = 2 * m ^ k := by
    unfold ErdosMoser.powerSum
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m)]
    unfold ErdosMoser.powerSum at h
    rw [h]
    ring
  have hL : ((ErdosMoser.powerSum k (m + 1) : ℕ) : ZMod (2 ^ 3)) =
      (w : ZMod (2 ^ 3)) * ((2 ^ (3 - 1) : ℕ) : ZMod (2 ^ 3)) := by
    rw [powerSum_eq_range k (m + 1) hk0, hw]
    exact two_adic_block k hk hk0 3 w (by norm_num)
  rw [hS] at hL
  have hc := (ZMod.natCast_eq_natCast_iff' _ _ _).mp (show ((2 * m ^ k : ℕ) : ZMod (2 ^ 3)) =
      ((w * 2 ^ (3 - 1) : ℕ) : ZMod (2 ^ 3)) by rw [hL]; push_cast; ring)
  have hp := pow_mod_eight m k hmo hk
  norm_num at hc
  omega

/-- If `y ^ 2 = 0` then `(y + x) ^ (n + 1) = x ^ (n + 1) + (n + 1) x ^ n y`. -/
lemma add_pow_succ_of_sq_zero {R : Type*} [CommRing R] (x y : R) (hy : y ^ 2 = 0) (n : ℕ) :
    (y + x) ^ (n + 1) = x ^ (n + 1) + ((n : R) + 1) * x ^ n * y := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero]
    ring
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((n : R) + 1) * x ^ n * hy

/-- Blocks: `Σ_{x < n q} f x = Σ_{j < q} Σ_{i < n} f (n j + i)`. -/
lemma sum_range_mul_blocks (f : ℕ → ℕ) (n q : ℕ) :
    ∑ x ∈ Finset.range (n * q), f x =
      ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range n, f (n * j + i) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Gauss for odd `p`: `Σ_{j < p} j = p * ((p - 1) / 2)`. -/
lemma sum_range_id_odd (p : ℕ) (hp : Odd p) : ∑ j ∈ Finset.range p, j = p * ((p - 1) / 2) := by
  have h := Finset.sum_range_id_mul_two p
  obtain ⟨r, rfl⟩ := hp
  have e : (2 * r + 1 - 1) / 2 = r := by omega
  rw [e]
  have e2 : (2 * r + 1) * (2 * r + 1 - 1) = (2 * r + 1) * r * 2 := by
    rw [show 2 * r + 1 - 1 = 2 * r by omega]
    ring
  rw [e2] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) h

/-- `Σ_{j < p} (p^a j + i)^k ≡ p i^k (mod p^(a+1))` for odd `p`, `a ≥ 1`, `k > 0`. -/
lemma p_adic_shift (p a i k : ℕ) (hp : Odd p) (ha : 1 ≤ a) (hk0 : 0 < k) :
    ∑ j ∈ Finset.range p, (p ^ a * j + i) ^ k ≡ p * i ^ k [MOD p ^ (a + 1)] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set y : ZMod (p ^ (a + 1)) := (p : ZMod (p ^ (a + 1))) ^ a with hy_def
  have hy : y ^ 2 = 0 := by
    rw [hy_def, ← pow_mul]
    have h0 : ((p ^ (a * 2) : ℕ) : ZMod (p ^ (a + 1))) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow p (by omega)
    exact_mod_cast h0
  have hpy : (p : ZMod (p ^ (a + 1))) * y = 0 := by
    rw [hy_def, ← pow_succ']
    have h0 : ((p ^ (a + 1) : ℕ) : ZMod (p ^ (a + 1))) = 0 := ZMod.natCast_self _
    exact_mod_cast h0
  have hterm : ∀ j ∈ Finset.range p,
      (y * (j : ZMod (p ^ (a + 1))) + (i : ZMod (p ^ (a + 1)))) ^ (n + 1) =
        (i : ZMod (p ^ (a + 1))) ^ (n + 1) +
          ((n : ZMod (p ^ (a + 1))) + 1) * (i : ZMod (p ^ (a + 1))) ^ n *
            (y * (j : ZMod (p ^ (a + 1)))) := by
    intro j _
    have hyj : (y * (j : ZMod (p ^ (a + 1)))) ^ 2 = 0 := by rw [mul_pow, hy, zero_mul]
    exact add_pow_succ_of_sq_zero _ _ hyj n
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum : ∑ j ∈ Finset.range p, (j : ZMod (p ^ (a + 1))) =
      (p : ZMod (p ^ (a + 1))) * (((p - 1) / 2 : ℕ) : ZMod (p ^ (a + 1))) := by
    have h' := congrArg (Nat.cast (R := ZMod (p ^ (a + 1)))) (sum_range_id_odd p hp)
    push_cast at h'
    exact h'
  rw [hsum, nsmul_eq_mul]
  linear_combination ((n : ZMod (p ^ (a + 1))) + 1) * (i : ZMod (p ^ (a + 1))) ^ n *
    (((p - 1) / 2 : ℕ) : ZMod (p ^ (a + 1))) * hpy

/-- `Σ_{i < p^a} i ^ k + p ^ (a - 1) ≡ 0 (mod p ^ a)` for an odd prime `p` with `(p - 1) ∣ k`. -/
lemma p_adic_sum (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk0 : 0 < k) (hdk : (p - 1) ∣ k)
    (a : ℕ) (ha : 1 ≤ a) :
    ∑ i ∈ Finset.range (p ^ a), i ^ k + p ^ (a - 1) ≡ 0 [MOD p ^ a] := by
  have : Fact p.Prime := ⟨hp⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  induction a, ha using Nat.le_induction with
  | base =>
    rw [← ZMod.natCast_eq_natCast_iff, pow_one]
    push_cast
    rw [sum_range_cast_eq_univ, sum_zmod_pow p k hk0, if_pos hdk]
    simp
  | succ a ha ih =>
    have hblk : ∑ i ∈ Finset.range (p ^ (a + 1)), i ^ k =
        ∑ i ∈ Finset.range (p ^ a), ∑ j ∈ Finset.range p, (p ^ a * j + i) ^ k := by
      rw [pow_succ, sum_range_mul_blocks (fun x => x ^ k) (p ^ a) p, Finset.sum_comm]
    have hshift : ∑ i ∈ Finset.range (p ^ a), ∑ j ∈ Finset.range p, (p ^ a * j + i) ^ k ≡
        ∑ i ∈ Finset.range (p ^ a), p * i ^ k [MOD p ^ (a + 1)] := by
      unfold Nat.ModEq
      rw [Finset.sum_nat_mod, Finset.sum_nat_mod (Finset.range (p ^ a)) _ (fun i => p * i ^ k)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact p_adic_shift p a i k hpo ha hk0
    have hp3 := Nat.ModEq.mul_left' p ih
    have e1 : p * (∑ i ∈ Finset.range (p ^ a), i ^ k + p ^ (a - 1)) =
        ∑ i ∈ Finset.range (p ^ a), p * i ^ k + p ^ a := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [Nat.add_sub_cancel, mul_add, Finset.mul_sum, pow_succ]
      ring
    rw [e1, mul_zero, show p * p ^ a = p ^ (a + 1) by ring] at hp3
    rw [hblk, show a + 1 - 1 = a by omega]
    exact (Nat.ModEq.add_right _ hshift).trans hp3

/-- A solution has no prime factor `p ≠ 2` of `m` with `(p - 1) ∣ k` (p-adic valuation argument;
part of Moree, te Riele, Urbanowicz 1994). -/
lemma prime_not_dvd_of_solution (k m p : ℕ) (hk0 : 0 < k) (hm : 0 < m) (hp : p.Prime)
    (hp2 : p ≠ 2) (hdk : (p - 1) ∣ k) (h : ErdosMoser.powerSum k m = m ^ k) : ¬ p ∣ m := by
  intro hpm
  obtain ⟨a, t, ht, hmt⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) p hp.one_lt.ne'
  have ha : 1 ≤ a := by
    by_contra ha0
    have a0 : a = 0 := by omega
    rw [a0, pow_zero, one_mul] at hmt
    exact ht (hmt ▸ hpm)
  have hR : ((m ^ k : ℕ) : ZMod (p ^ a)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.trans ⟨t, hmt⟩ (dvd_pow_self m (by omega))
  have hT := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (p_adic_sum p k hp hp2 hk0 hdk a ha)
  push_cast at hT
  have hL : ((ErdosMoser.powerSum k m : ℕ) : ZMod (p ^ a)) =
      (t : ZMod (p ^ a)) * ∑ i ∈ Finset.range (p ^ a), ((i : ZMod (p ^ a)) ^ k) := by
    rw [powerSum_eq_range k m hk0, hmt, Nat.cast_sum]
    simp only [Nat.cast_pow]
    rw [sum_range_mul_cast]
  have key : ((t * p ^ (a - 1) : ℕ) : ZMod (p ^ a)) = 0 := by
    have h1 : ((ErdosMoser.powerSum k m : ℕ) : ZMod (p ^ a)) = 0 := by rw [h]; exact hR
    rw [hL] at h1
    push_cast
    linear_combination -h1 + (t : ZMod (p ^ a)) * hT
  rw [ZMod.natCast_eq_zero_iff] at key
  have e : p ^ a = p * p ^ (a - 1) := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  rw [e] at key
  exact ht (Nat.dvd_of_mul_dvd_mul_right (pow_pos hp.pos _) key)

/-- `Σ_{j < p u} (j : ZMod p) ^ k = u * (if (p - 1) ∣ k then -1 else 0)`. -/
lemma sum_block_prime (p k u : ℕ) [Fact p.Prime] (hk0 : 0 < k) :
    ∑ j ∈ Finset.range (p * u), ((j : ZMod p) ^ k) =
      (u : ZMod p) * (if p - 1 ∣ k then -1 else 0) := by
  rw [sum_range_mul_cast, sum_range_cast_eq_univ, sum_zmod_pow p k hk0]

/-- From `u * (if (p - 1) ∣ k then -1 else 0) = c` with `c ≠ 0`: `(p - 1) ∣ k` and `p ∣ u + c`. -/
lemma moser_finish (p k u c : ℕ) [Fact p.Prime]
    (hc : (c : ZMod p) ≠ 0)
    (h : (u : ZMod p) * (if p - 1 ∣ k then -1 else 0) = c) : (p - 1) ∣ k ∧ p ∣ u + c := by
  by_cases hdk : p - 1 ∣ k
  · rw [if_pos hdk] at h
    refine ⟨hdk, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    linear_combination -h
  · rw [if_neg hdk, mul_zero] at h
    exact absurd h.symm hc

/-- In `ZMod p` with `p` an odd prime, `2 ^ n ≠ 0`. -/
lemma two_pow_ne_zero (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ((2 ^ n : ℕ) : ZMod p) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h0))

/-- `S_k(m + 1) = 2 m ^ k` for a solution with `m ≥ 1`. -/
lemma powerSum_succ_of_solution (k m : ℕ) (hm : 1 ≤ m) (h : ErdosMoser.powerSum k m = m ^ k) :
    ErdosMoser.powerSum k (m + 1) = 2 * m ^ k := by
  unfold ErdosMoser.powerSum
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m)]
  unfold ErdosMoser.powerSum at h
  rw [h]
  ring

/-- Moser 1953 at an odd prime `p ∣ m + 1`: `(p - 1) ∣ k` and `p ∣ (m + 1) / p + 2`. -/
lemma moser_prime_succ (k m p : ℕ) (hk : Even k) (hk0 : 0 < k) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ m + 1) (hm : 1 ≤ m) (h : ErdosMoser.powerSum k m = m ^ k) :
    (p - 1) ∣ k ∧ p ∣ (m + 1) / p + 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := hpm
  have hdiv : (m + 1) / p = u := by rw [hu, Nat.mul_div_cancel_left u hp.pos]
  rw [hdiv]
  have hm1 : (m : ZMod p) = -1 := by
    have h0 : ((m + 1 : ℕ) : ZMod p) = 0 := by
      rw [hu]
      push_cast
      rw [ZMod.natCast_self, zero_mul]
    push_cast at h0
    linear_combination h0
  have hcast : ((ErdosMoser.powerSum k (m + 1) : ℕ) : ZMod p) = ((2 * m ^ k : ℕ) : ZMod p) := by
    rw [powerSum_succ_of_solution k m hm h]
  rw [powerSum_eq_range k (m + 1) hk0, hu, Nat.cast_sum] at hcast
  simp only [Nat.cast_pow] at hcast
  rw [sum_block_prime p k u hk0] at hcast
  push_cast at hcast
  rw [hm1, hk.neg_one_pow, mul_one] at hcast
  have h2 := two_pow_ne_zero p 1 hp hp2
  rw [pow_one] at h2
  exact moser_finish p k u 2 h2 (by exact_mod_cast hcast)

/-- Split a sum over `j < 2 n` into even and odd `j`. -/
lemma sum_range_two_mul_pow (p k n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), ((j : ZMod p) ^ k) =
      ∑ i ∈ Finset.range n, (((2 * i : ℕ) : ZMod p) ^ k + ((2 * i + 1 : ℕ) : ZMod p) ^ k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- Moser 1953 at a prime `p ∣ 2 m - 1`: `(p - 1) ∣ k` and `p ∣ (2 m - 1) / p + 2`. -/
lemma moser_prime_two_mul_sub (k m p : ℕ) (hk : Even k) (hk0 : 0 < k) (hp : p.Prime)
    (hpm : p ∣ 2 * m - 1) (hm : 1 ≤ m) (h : ErdosMoser.powerSum k m = m ^ k) :
    (p - 1) ∣ k ∧ p ∣ (2 * m - 1) / p + 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  obtain ⟨u, hu⟩ := hpm
  have hdiv : (2 * m - 1) / p = u := by rw [hu, Nat.mul_div_cancel_left u hp.pos]
  rw [hdiv]
  have hz : ((2 * m - 1 : ℕ) : ZMod p) = 0 := by
    rw [hu]
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  have h2m : (2 : ZMod p) * (m : ZMod p) = 1 := by
    have e : 2 * m = (2 * m - 1) + 1 := by omega
    have h1 : ((2 * m : ℕ) : ZMod p) = 1 := by
      rw [e, Nat.cast_add, hz, zero_add, Nat.cast_one]
    exact_mod_cast h1
  have hA1 : ∑ j ∈ Finset.range (2 * m), ((j : ZMod p) ^ k) =
      (u : ZMod p) * (if p - 1 ∣ k then -1 else 0) := by
    rw [show 2 * m = (2 * m - 1) + 1 by omega, Finset.sum_range_succ, hz, zero_pow (by omega),
      add_zero, hu, sum_block_prime p k u hk0]
  have hS : ∑ i ∈ Finset.range m, ((i : ZMod p) ^ k) = (m : ZMod p) ^ k := by
    have h' := congrArg (Nat.cast (R := ZMod p)) h
    rw [powerSum_eq_range k m hk0] at h'
    push_cast at h'
    exact h'
  have hA2 : ∑ j ∈ Finset.range (2 * m), ((j : ZMod p) ^ k) =
      2 * (2 : ZMod p) ^ k * ∑ i ∈ Finset.range m, ((i : ZMod p) ^ k) := by
    rw [sum_range_two_mul_pow, Finset.sum_add_distrib]
    have hodd : ∀ i ∈ Finset.range m, (((2 * i + 1 : ℕ) : ZMod p) ^ k) =
        (((2 * (m - 1 - i) : ℕ) : ZMod p) ^ k) := by
      intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      have e : ((2 * (m - 1 - i) : ℕ) : ZMod p) + ((2 * i + 1 : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, show 2 * (m - 1 - i) + (2 * i + 1) = 2 * m - 1 by omega, hz]
      rw [show ((2 * i + 1 : ℕ) : ZMod p) = -((2 * (m - 1 - i) : ℕ) : ZMod p) by
        linear_combination e, Even.neg_pow hk]
    rw [Finset.sum_congr rfl hodd,
      Finset.sum_range_reflect (fun i => (((2 * i : ℕ) : ZMod p) ^ k)) m]
    push_cast
    simp only [mul_pow]
    rw [← Finset.mul_sum]
    ring
  have hfin : (u : ZMod p) * (if p - 1 ∣ k then -1 else 0) = ((2 : ℕ) : ZMod p) := by
    rw [← hA1, hA2, hS]
    have h1 : (2 : ZMod p) ^ k * (m : ZMod p) ^ k = 1 := by
      rw [← mul_pow, h2m, one_pow]
    push_cast
    linear_combination 2 * h1
  have h2 := two_pow_ne_zero p 1 hp hp2
  rw [pow_one] at h2
  exact moser_finish p k u 2 h2 hfin

/-- Moser 1953 at a prime `p ∣ 2 m + 1`: `(p - 1) ∣ k` and `p ∣ (2 m + 1) / p + 4`. -/
lemma moser_prime_two_mul_add (k m p : ℕ) (hk : Even k) (hk0 : 0 < k) (hp : p.Prime)
    (hpm : p ∣ 2 * m + 1) (hm : 1 ≤ m) (h : ErdosMoser.powerSum k m = m ^ k) :
    (p - 1) ∣ k ∧ p ∣ (2 * m + 1) / p + 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  obtain ⟨u, hu⟩ := hpm
  have hdiv : (2 * m + 1) / p = u := by rw [hu, Nat.mul_div_cancel_left u hp.pos]
  rw [hdiv]
  have hz : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by
    rw [hu]
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  have h2m : (2 : ZMod p) * (m : ZMod p) = -1 := by
    push_cast at hz
    linear_combination hz
  have hA1 : ∑ j ∈ Finset.range (2 * (m + 1)), ((j : ZMod p) ^ k) =
      (u : ZMod p) * (if p - 1 ∣ k then -1 else 0) := by
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Finset.sum_range_succ, hz, zero_pow (by omega),
      add_zero, hu, sum_block_prime p k u hk0]
  have hS : ∑ i ∈ Finset.range (m + 1), ((i : ZMod p) ^ k) = 2 * (m : ZMod p) ^ k := by
    have h' := congrArg (Nat.cast (R := ZMod p)) (powerSum_succ_of_solution k m hm h)
    rw [powerSum_eq_range k (m + 1) hk0] at h'
    push_cast at h'
    exact h'
  have hA2 : ∑ j ∈ Finset.range (2 * (m + 1)), ((j : ZMod p) ^ k) =
      2 * (2 : ZMod p) ^ k * ∑ i ∈ Finset.range (m + 1), ((i : ZMod p) ^ k) := by
    rw [sum_range_two_mul_pow, Finset.sum_add_distrib]
    have hodd : ∀ i ∈ Finset.range (m + 1), (((2 * i + 1 : ℕ) : ZMod p) ^ k) =
        (((2 * (m + 1 - 1 - i) : ℕ) : ZMod p) ^ k) := by
      intro i hi
      have hi' : i < m + 1 := Finset.mem_range.mp hi
      have e : ((2 * (m + 1 - 1 - i) : ℕ) : ZMod p) + ((2 * i + 1 : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, show 2 * (m + 1 - 1 - i) + (2 * i + 1) = 2 * m + 1 by omega, hz]
      rw [show ((2 * i + 1 : ℕ) : ZMod p) = -((2 * (m + 1 - 1 - i) : ℕ) : ZMod p) by
        linear_combination e, Even.neg_pow hk]
    rw [Finset.sum_congr rfl hodd,
      Finset.sum_range_reflect (fun i => (((2 * i : ℕ) : ZMod p) ^ k)) (m + 1)]
    push_cast
    simp only [mul_pow]
    rw [← Finset.mul_sum]
    ring
  have hfin : (u : ZMod p) * (if p - 1 ∣ k then -1 else 0) = ((2 ^ 2 : ℕ) : ZMod p) := by
    rw [← hA1, hA2, hS]
    have h1 : (2 : ZMod p) ^ k * (m : ZMod p) ^ k = 1 := by
      rw [← mul_pow, h2m, hk.neg_one_pow]
    push_cast
    linear_combination 4 * h1
  exact moser_finish p k u (2 ^ 2) (two_pow_ne_zero p 2 hp hp2) hfin

/-- `(m + 1) / 4` is squarefree: odd, and no odd `p ^ 2` divides `m + 1`. -/
lemma squarefree_succ_div_four (k m : ℕ) (hk : Even k) (hk0 : 0 < k) (hm : 1 ≤ m)
    (h8 : m % 8 = 3) (h : ErdosMoser.powerSum k m = m ^ k) : Squarefree ((m + 1) / 4) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  by_cases hp2 : p = 2
  · subst hp2
    omega
  · have hpp' : p * p ∣ m + 1 := Dvd.dvd.trans hpp (Nat.div_dvd_of_dvd (by omega : 4 ∣ m + 1))
    have hpm : p ∣ m + 1 := Dvd.dvd.trans (dvd_mul_right p p) hpp'
    obtain ⟨_, h2⟩ := moser_prime_succ k m p hk hk0 hp hp2 hpm hm h
    have h3 : p ∣ (m + 1) / p := by
      obtain ⟨c, hc⟩ := hpp'
      rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
      exact dvd_mul_right p c
    have h4 : p ∣ 2 := (Nat.dvd_add_right h3).mp h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)

/-- `2 m - 1` is squarefree. -/
lemma squarefree_two_mul_sub (k m : ℕ) (hk : Even k) (hk0 : 0 < k) (hm : 1 ≤ m)
    (h : ErdosMoser.powerSum k m = m ^ k) : Squarefree (2 * m - 1) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpm : p ∣ 2 * m - 1 := Dvd.dvd.trans (dvd_mul_right p p) hpp
  obtain ⟨_, h2⟩ := moser_prime_two_mul_sub k m p hk hk0 hp hpm hm h
  have h3 : p ∣ (2 * m - 1) / p := by
    obtain ⟨c, hc⟩ := hpp
    rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    exact dvd_mul_right p c
  have h4 : p ∣ 2 := (Nat.dvd_add_right h3).mp h2
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4
  subst hp2
  omega

/-- `2 m + 1` is squarefree. -/
lemma squarefree_two_mul_add (k m : ℕ) (hk : Even k) (hk0 : 0 < k) (hm : 1 ≤ m)
    (h : ErdosMoser.powerSum k m = m ^ k) : Squarefree (2 * m + 1) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpm : p ∣ 2 * m + 1 := Dvd.dvd.trans (dvd_mul_right p p) hpp
  obtain ⟨_, h2⟩ := moser_prime_two_mul_add k m p hk hk0 hp hpm hm h
  have h3 : p ∣ (2 * m + 1) / p := by
    obtain ⟨c, hc⟩ := hpp
    rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    exact dvd_mul_right p c
  have h4 : p ∣ 2 ^ 2 := by simpa using (Nat.dvd_add_right h3).mp h2
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4)
  subst hp2
  omega

/-- Bernoulli in ℕ: `i ^ k * (i + k) ≤ i * (i + 1) ^ k`. -/
lemma bern (i k : ℕ) : i ^ k * (i + k) ≤ i * (i + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    have h0 : i * (i + (k + 1)) ≤ (i + k) * (i + 1) := by nlinarith
    have h1 : i ^ k * i * (i + (k + 1)) ≤ i ^ k * (i + k) * (i + 1) := by
      calc i ^ k * i * (i + (k + 1)) = i ^ k * (i * (i + (k + 1))) := by ring
        _ ≤ i ^ k * ((i + k) * (i + 1)) := Nat.mul_le_mul_left _ h0
        _ = i ^ k * (i + k) * (i + 1) := by ring
    have h2 : i ^ k * (i + k) * (i + 1) ≤ i * (i + 1) ^ k * (i + 1) := Nat.mul_le_mul_right _ ih
    calc i ^ k * i * (i + (k + 1)) ≤ i ^ k * (i + k) * (i + 1) := h1
      _ ≤ i * (i + 1) ^ k * (i + 1) := h2
      _ = i * ((i + 1) ^ k * (i + 1)) := by ring

/-- For `1 ≤ i ≤ k`: `2 i ^ k ≤ (i + 1) ^ k`. -/
lemma two_mul_pow_le (i k : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) : 2 * i ^ k ≤ (i + 1) ^ k := by
  have h := bern i k
  have h2 : i ^ k * (2 * i) ≤ i ^ k * (i + k) := Nat.mul_le_mul_left _ (by omega)
  have h3 : i * (2 * i ^ k) ≤ i * (i + 1) ^ k := by
    calc i * (2 * i ^ k) = i ^ k * (2 * i) := by ring
      _ ≤ i ^ k * (i + k) := h2
      _ ≤ i * (i + 1) ^ k := h
  exact Nat.le_of_mul_le_mul_left h3 (by omega)

/-- If `m ≤ k + 1` then `2 ^ j (m - j) ^ k ≤ m ^ k` for `j < m`. -/
lemma chain (m k : ℕ) (hmk : m ≤ k + 1) : ∀ j, j < m → 2 ^ j * (m - j) ^ k ≤ m ^ k := by
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 : 2 * (m - (j + 1)) ^ k ≤ (m - (j + 1) + 1) ^ k :=
      two_mul_pow_le _ _ (by omega) (by omega)
    rw [show m - (j + 1) + 1 = m - j by omega] at h2
    calc 2 ^ (j + 1) * (m - (j + 1)) ^ k = 2 ^ j * (2 * (m - (j + 1)) ^ k) := by ring
      _ ≤ 2 ^ j * (m - j) ^ k := Nat.mul_le_mul_left _ h2
      _ ≤ m ^ k := h1

/-- Top partial sums: `2 ^ n Σ_{m - n ≤ i < m} i ^ k + m ^ k ≤ 2 ^ n m ^ k` for `n < m`. -/
lemma top_sum (m k : ℕ) (hmk : m ≤ k + 1) : ∀ n, n < m →
    2 ^ n * ∑ i ∈ Finset.Ico (m - n) m, i ^ k + m ^ k ≤ 2 ^ n * m ^ k := by
  intro n
  induction n with
  | zero =>
    intro _
    simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have hsplit : ∑ i ∈ Finset.Ico (m - (n + 1)) m, i ^ k =
        (m - (n + 1)) ^ k + ∑ i ∈ Finset.Ico (m - n) m, i ^ k := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : m - (n + 1) < m),
        show m - (n + 1) + 1 = m - n by omega]
    have h2 := chain m k hmk (n + 1) hn
    rw [hsplit]
    calc 2 ^ (n + 1) * ((m - (n + 1)) ^ k + ∑ i ∈ Finset.Ico (m - n) m, i ^ k) + m ^ k
        = 2 ^ (n + 1) * (m - (n + 1)) ^ k +
            2 * (2 ^ n * ∑ i ∈ Finset.Ico (m - n) m, i ^ k) + m ^ k := by ring
      _ ≤ m ^ k + 2 * (2 ^ n * ∑ i ∈ Finset.Ico (m - n) m, i ^ k) + m ^ k := by omega
      _ = 2 * (2 ^ n * ∑ i ∈ Finset.Ico (m - n) m, i ^ k + m ^ k) := by ring
      _ ≤ 2 * (2 ^ n * m ^ k) := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (n + 1) * m ^ k := by ring

/-- Size: a solution with `m ≥ 2` has `k + 2 ≤ m` (else `S_k(m) < m ^ k`). -/
lemma size_of_solution (k m : ℕ) (hm : 2 ≤ m) (h : ErdosMoser.powerSum k m = m ^ k) :
    k + 2 ≤ m := by
  by_contra hlt
  have hmk : m ≤ k + 1 := by omega
  have ht := top_sum m k hmk (m - 1) (by omega)
  rw [show m - (m - 1) = 1 by omega] at ht
  have hS : ∑ i ∈ Finset.Ico 1 m, i ^ k = m ^ k := h
  rw [hS] at ht
  have hpos : 0 < m ^ k := pow_pos (by omega) k
  nlinarith

/-- Lower Bernoulli in ℕ: `m ^ k * (m - k) ≤ m * (m - 1) ^ k` for `m ≥ 1`. -/
lemma bern_low1 (m k : ℕ) (hm : 1 ≤ m) : m ^ k * (m - k) ≤ m * (m - 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hbig : k + 1 ≤ m
    · have h1 : m * (m - (k + 1)) ≤ (m - k) * (m - 1) := by
        obtain ⟨a, ha⟩ : ∃ a, m = (k + 1) + a := ⟨m - (k + 1), by omega⟩
        subst ha
        rw [show k + 1 + a - (k + 1) = a by omega, show k + 1 + a - k = a + 1 by omega,
          show k + 1 + a - 1 = k + a by omega]
        nlinarith
      calc m ^ (k + 1) * (m - (k + 1)) = m ^ k * (m * (m - (k + 1))) := by ring
        _ ≤ m ^ k * ((m - k) * (m - 1)) := Nat.mul_le_mul_left _ h1
        _ = m ^ k * (m - k) * (m - 1) := by ring
        _ ≤ m * (m - 1) ^ k * (m - 1) := Nat.mul_le_mul_right _ ih
        _ = m * (m - 1) ^ (k + 1) := by ring
    · have h0 : m - (k + 1) = 0 := by omega
      rw [h0, mul_zero]
      exact Nat.zero_le _

/-- `(i + 1) ^ (k + 1) ≤ i ^ (k + 1) + (k + 1) (i + 1) ^ k`. -/
lemma step_upper (i k : ℕ) : (i + 1) ^ (k + 1) ≤ i ^ (k + 1) + (k + 1) * (i + 1) ^ k := by
  by_cases hik : i ≤ k
  · have e0 : (i + 1) ^ (k + 1) = (i + 1) * (i + 1) ^ k := by ring
    rw [e0]
    have h2 : (i + 1) * (i + 1) ^ k ≤ (k + 1) * (i + 1) ^ k := Nat.mul_le_mul_right _ (by omega)
    omega
  · have hb := bern_low1 (i + 1) k (by omega)
    rw [show i + 1 - 1 = i by omega] at hb
    have hA : (i + 1) * ((i + 1) ^ k * (i - k)) ≤ (i + 1) * i ^ (k + 1) := by
      have e1 : (i + 1) * (i - k) ≤ i * (i + 1 - k) := by
        obtain ⟨a, ha⟩ : ∃ a, i = k + 1 + a := ⟨i - (k + 1), by omega⟩
        subst ha
        rw [show k + 1 + a - k = a + 1 by omega, show k + 1 + a + 1 - k = a + 2 by omega]
        nlinarith
      calc (i + 1) * ((i + 1) ^ k * (i - k)) = (i + 1) ^ k * ((i + 1) * (i - k)) := by ring
        _ ≤ (i + 1) ^ k * (i * (i + 1 - k)) := Nat.mul_le_mul_left _ e1
        _ = i * ((i + 1) ^ k * (i + 1 - k)) := by ring
        _ ≤ i * ((i + 1) * i ^ k) := Nat.mul_le_mul_left _ hb
        _ = (i + 1) * i ^ (k + 1) := by ring
    have hB : (i + 1) ^ k * (i - k) ≤ i ^ (k + 1) := Nat.le_of_mul_le_mul_left hA (by omega)
    have e2 : (i + 1) ^ (k + 1) = (i + 1) ^ k * (i - k) + (k + 1) * (i + 1) ^ k := by
      obtain ⟨a, ha⟩ : ∃ a, i = k + 1 + a := ⟨i - (k + 1), by omega⟩
      subst ha
      rw [show k + 1 + a - k = a + 1 by omega]
      ring
    omega

/-- Integral comparison: `n ^ (k + 1) ≤ (k + 1) Σ_{1 ≤ i < n + 1} i ^ k`. -/
lemma integral_lower (k n : ℕ) :
    n ^ (k + 1) ≤ (k + 1) * ∑ i ∈ Finset.Ico 1 (n + 1), i ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1), mul_add]
    have hs := step_upper n k
    omega

/-- Upper size: a solution with `k ≥ 1`, `m ≥ k + 2` has `m ≤ 2 k + 1`, from
`(m - 1) ^ (k + 1) ≤ (k + 1) S_k(m)` and Bernoulli `m ^ k (m - k) ≤ m (m - 1) ^ k`. -/
lemma size_upper2 (k m : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) (hkm : k + 2 ≤ m)
    (h : ErdosMoser.powerSum k m = m ^ k) : m ≤ 2 * k + 1 := by
  have hI := integral_lower k (m - 1)
  rw [show m - 1 + 1 = m by omega] at hI
  have hS : ∑ i ∈ Finset.Ico 1 m, i ^ k = m ^ k := h
  rw [hS] at hI
  have hb := bern_low1 m k (by omega)
  have hpos : 0 < m ^ k := pow_pos (by omega) k
  have hC : m ^ k * ((m - 1) * (m - k)) ≤ m ^ k * (m * (k + 1)) := by
    calc m ^ k * ((m - 1) * (m - k)) = (m - 1) * (m ^ k * (m - k)) := by ring
      _ ≤ (m - 1) * (m * (m - 1) ^ k) := Nat.mul_le_mul_left _ hb
      _ = m * (m - 1) ^ (k + 1) := by ring
      _ ≤ m * ((k + 1) * m ^ k) := Nat.mul_le_mul_left _ hI
      _ = m ^ k * (m * (k + 1)) := by ring
  have hD : (m - 1) * (m - k) ≤ m * (k + 1) := Nat.le_of_mul_le_mul_left hC hpos
  by_contra hlt
  obtain ⟨x, hx⟩ : ∃ x, m = k + x := ⟨m - k, by omega⟩
  subst hx
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [show k + (y + 1) - 1 = k + y by omega, show k + (y + 1) - k = y + 1 by omega] at hD
  have hy : k + 1 ≤ y := by omega
  have hyy := Nat.mul_le_mul hy hy
  nlinarith

theorem main : H1 → H2 → OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H2 := by
  intro h1 h2 k m hk hm he h
  have hk2 : 2 ≤ k := by
    rcases he with ⟨j, hj⟩
    omega
  by_cases hm4 : 4 ≤ m
  · have hsq := squarefree_of_solution k m hk (by omega) h
    have hmo : ∀ p : ℕ, p.Prime → p ∣ m - 1 → (p - 1) ∣ k ∧ p ∣ (m - 1) / p + 1 :=
      fun p hp hpm => moser_prime k m p hk hp hpm (by omega) h
    have hodd := m_odd_of_solution k m he hk hm h
    have h43 : m % 4 = 3 := by
      rcases mod_four_of_solution hk h with r | r
      · exact absurd (Nat.dvd_of_mod_eq_zero (by omega)) hodd
      · exact r
    have h83 := mod_eight_of_solution k m he hk hm h43 h
    have hmo5 : ∀ p : ℕ, p.Prime → p ∣ m → ¬ (p - 1) ∣ k := by
      intro p hp hpm hdk
      by_cases hp2 : p = 2
      · subst hp2
        exact hodd hpm
      · exact prime_not_dvd_of_solution k m p hk hm hp hp2 hdk h hpm
    have h3 : ¬ 3 ∣ m := fun h3m => hmo5 3 Nat.prime_three h3m (even_iff_two_dvd.mp he)
    have hkm := size_of_solution k m (by omega) h
    have hku := size_upper2 k m (by omega) (by omega) hkm h
    have hmo2 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m + 1 → (p - 1) ∣ k ∧ p ∣ (m + 1) / p + 2 :=
      fun p hp hp2 hpm => moser_prime_succ k m p he hk hp hp2 hpm (by omega) h
    have hmo3 : ∀ p : ℕ, p.Prime → p ∣ 2 * m - 1 → (p - 1) ∣ k ∧ p ∣ (2 * m - 1) / p + 2 :=
      fun p hp hpm => moser_prime_two_mul_sub k m p he hk hp hpm (by omega) h
    have hmo4 : ∀ p : ℕ, p.Prime → p ∣ 2 * m + 1 → (p - 1) ∣ k ∧ p ∣ (2 * m + 1) / p + 4 :=
      fun p hp hpm => moser_prime_two_mul_add k m p he hk hp hpm (by omega) h
    have hsq2 := squarefree_succ_div_four k m he hk (by omega) h83 h
    have hsq3 := squarefree_two_mul_sub k m he hk (by omega) h
    have hsq4 := squarefree_two_mul_add k m he hk (by omega) h
    rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with r | r
    · have h9 : 3 ∣ (m - 1) / 3 + 1 := (hmo 3 Nat.prime_three (by omega)).2
      have r9 : m % 9 = 7 := by omega
      exact h1 k m he hk2 hm4 hkm hku h83 r9 hsq hsq2 hsq3 hsq4 hmo hmo2 hmo3 hmo4 hmo5 h
    · have h9 : 3 ∣ (m + 1) / 3 + 2 := (hmo2 3 Nat.prime_three (by norm_num) (by omega)).2
      have r9 : m % 9 = 2 := by omega
      exact h2 k m he hk2 hm4 hkm hku h83 r9 hsq hsq2 hsq3 hsq4 hmo hmo2 hmo3 hmo4 hmo5 h
  · have hm3 : m ≤ 3 := by omega
    interval_cases m
    · rw [powerSum_at_one, one_pow] at h
      omega
    · rw [powerSum_at_two] at h
      have h2k := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ k by omega)
      rw [pow_one] at h2k
      omega
    · rw [powerSum_at_three] at h
      have h3k := one_add_two_pow_lt k hk2
      omega

end OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R1
