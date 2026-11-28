import OMAStatements.S_oeis_a389475
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.Tactic

namespace OMA.P_oeis_a389475

open OMA.S_oeis_a389475

private def convZ (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), f i * g (n - i)

private lemma conv_cast (f g : ℕ → ℤ) (n : ℕ) :
    conv (fun k => (f k : ℚ)) (fun k => (g k : ℚ)) n = (convZ f g n : ℚ) := by
  unfold conv convZ
  push_cast
  rfl

/-- Unfolding `a389475 (n + 2)` without `Finset.attach`. -/
private lemma a389475_succ_succ (n : ℕ) :
    a389475 (n + 2) =
      ((if (n + 3) % 2 = 0 then (3 : ℚ) ^ ((n + 3) / 2) * a389475 ((n + 3) / 2) else 0) -
        (∑ i ∈ Finset.Icc 2 (n + 1), a389475 i * a389475 (n + 3 - i)) +
        2 * (∑ i ∈ Finset.Icc 1 (n + 1), ∑ j ∈ Finset.Icc 1 (n + 2 - i),
          a389475 i * a389475 j * a389475 (n + 3 - i - j))) / 2 := by
  rw [a389475]
  have h1 : (∑ i ∈ (Finset.Icc 2 (n + 1)).attach, a389475 i.1 * a389475 (n + 3 - i.1)) =
      ∑ i ∈ Finset.Icc 2 (n + 1), a389475 i * a389475 (n + 3 - i) :=
    Finset.sum_attach (Finset.Icc 2 (n + 1)) (fun i => a389475 i * a389475 (n + 3 - i))
  have h2 : (∑ i ∈ (Finset.Icc 1 (n + 1)).attach,
        ∑ j ∈ (Finset.Icc 1 (n + 2 - i.1)).attach,
          a389475 i.1 * a389475 j.1 * a389475 (n + 3 - i.1 - j.1)) =
      ∑ i ∈ Finset.Icc 1 (n + 1), ∑ j ∈ Finset.Icc 1 (n + 2 - i),
        a389475 i * a389475 j * a389475 (n + 3 - i - j) := by
    trans (∑ i ∈ (Finset.Icc 1 (n + 1)).attach,
        ∑ j ∈ Finset.Icc 1 (n + 2 - i.1), a389475 i.1 * a389475 j * a389475 (n + 3 - i.1 - j))
    · apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_attach (Finset.Icc 1 (n + 2 - i.1))
        (fun j => a389475 i.1 * a389475 j * a389475 (n + 3 - i.1 - j))
    · exact Finset.sum_attach (Finset.Icc 1 (n + 1))
        (fun i => ∑ j ∈ Finset.Icc 1 (n + 2 - i), a389475 i * a389475 j * a389475 (n + 3 - i - j))
  rw [h1, h2]

private lemma conv_a389475_sq (n : ℕ) :
    conv a389475 a389475 (n + 3) =
      2 * a389475 (n + 2) + ∑ i ∈ Finset.Icc 2 (n + 1), a389475 i * a389475 (n + 3 - i) := by
  unfold conv
  have h0 : a389475 0 = 0 := by rw [a389475]
  have h1 : a389475 1 = 1 := by rw [a389475]
  have hsplit : Finset.range (n + 4) =
      insert 0 (insert 1 (insert (n + 2) (insert (n + 3) (Finset.Icc 2 (n + 1))))) := by
    ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  have hs1 : n + 3 - 1 = n + 2 := by omega
  have hs2 : n + 3 - (n + 2) = 1 := by omega
  have hs3 : n + 3 - (n + 3) = 0 := by omega
  rw [hs1, hs2, hs3, h0, h1]
  ring

private lemma conv_a389475_cube (n : ℕ) :
    conv (conv a389475 a389475) a389475 (n + 3) =
      ∑ i ∈ Finset.Icc 1 (n + 1), ∑ j ∈ Finset.Icc 1 (n + 2 - i),
        a389475 i * a389475 j * a389475 (n + 3 - i - j) := by
  have h0 : a389475 0 = 0 := by rw [a389475]
  unfold conv
  -- Rewrite ∑_{k=0}^{n+3} (∑_{i=0}^k a_i a_{k-i}) a_{n+3-k}
  -- by reindexing (i, j) = (i, k - i), so k = i + j
  have hsum_range : ∀ m : ℕ,
      ∑ k ∈ Finset.range (m + 1), (∑ i ∈ Finset.range (k + 1), a389475 i * a389475 (k - i)) * a389475 (m - k) =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1 - i), a389475 i * a389475 j * a389475 (m - i - j) := by
    intro m
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    apply Finset.sum_bij (fun p _ => ⟨p.2, p.1 - p.2⟩)
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢; omega
    · intro p1 hp1 p2 hp2 hEq
      simp only [Finset.mem_sigma, Finset.mem_range] at hp1 hp2
      have h1 : p1.2 = p2.2 := congrArg Sigma.fst hEq
      have h2 : p1.1 - p1.2 = p2.1 - p2.2 := by
        have := congrArg Sigma.snd hEq; simpa using this
      exact Sigma.ext (by omega) (heq_of_eq h1)
    · intro q hq
      simp only [Finset.mem_sigma, Finset.mem_range] at hq
      refine ⟨⟨q.1 + q.2, q.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_range]; omega
      · exact Sigma.ext rfl (heq_of_eq (by dsimp; omega))
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_range] at hp
      have hsub : m - p.1 = m - p.2 - (p.1 - p.2) := by omega
      rw [hsub]
  rw [hsum_range (n + 3)]
  -- Drop zero terms where i = 0, i ≥ n + 2, j = 0, or j = n + 3 - i
  have hdrop_i : ∑ i ∈ Finset.range (n + 4),
        ∑ j ∈ Finset.range (n + 4 - i), a389475 i * a389475 j * a389475 (n + 3 - i - j) =
      ∑ i ∈ Finset.Icc 1 (n + 1),
        ∑ j ∈ Finset.range (n + 4 - i), a389475 i * a389475 j * a389475 (n + 3 - i - j) := by
    symm
    apply Finset.sum_subset (fun i hi => by
      simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega)
    intro i hi hnot
    simp only [Finset.mem_range, Finset.mem_Icc] at hi hnot
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    have hcases : i = 0 ∨ i = n + 2 ∨ i = n + 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp [h0]
    · have hjcases : j = 0 ∨ j = 1 := by omega
      rcases hjcases with rfl | rfl
      · simp [h0]
      · rw [show n + 3 - (n + 2) - 1 = 0 by omega, h0]; ring
    · have hj0 : j = 0 := by omega
      subst hj0; simp [h0]
  rw [hdrop_i]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  symm
  apply Finset.sum_subset (fun j hj => by
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega)
  intro j hj hnot
  simp only [Finset.mem_range, Finset.mem_Icc] at hj hnot
  have hcases : j = 0 ∨ j = n + 3 - i := by omega
  rcases hcases with rfl | rfl
  · simp [h0]
  · rw [show n + 3 - i - (n + 3 - i) = 0 by omega, h0]; ring

/-- `a389475` satisfies the exact functional equation `A(3*x^2) = 2*x^2 + A(x)^2 - 2*A(x)^3`. -/
private lemma func_eq (m : ℕ) :
    (if m % 2 = 0 then (3 : ℚ) ^ (m / 2) * a389475 (m / 2) else 0) =
      (if m = 2 then 2 else 0) + conv a389475 a389475 m - 2 * conv (conv a389475 a389475) a389475 m := by
  match m with
  | 0 =>
    simp [conv, a389475]
  | 1 =>
    simp [conv, Finset.sum_range_succ, a389475]
  | 2 =>
    simp [conv, Finset.sum_range_succ, a389475]
    norm_num
  | n + 3 =>
    rw [if_neg (by omega : n + 3 ≠ 2), zero_add, conv_a389475_sq n, conv_a389475_cube n, a389475_succ_succ n]
    ring

/-- Integrality: every `a389475 n` is an integer, proved by pairing off-diagonal terms in `s2` mod 2. -/
private lemma a389475_is_int : ∀ n : ℕ, ∃ z : ℤ, a389475 n = (z : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => exact ⟨0, by rw [a389475]; norm_num⟩
    | 1 => exact ⟨1, by rw [a389475]; norm_num⟩
    | n + 2 =>
      -- Build an integer function agreeing with a389475 on all k < n + 2
      have hfn : ∀ k : ℕ, ∃ z : ℤ, k < n + 2 → a389475 k = (z : ℚ) := fun k => by
        by_cases hk : k < n + 2
        · rcases ih k hk with ⟨z, hz⟩; exact ⟨z, fun _ => hz⟩
        · exact ⟨0, fun h => absurd h hk⟩
      choose z hz using hfn
      set lhsZ : ℤ := if (n + 3) % 2 = 0 then (3 : ℤ) ^ ((n + 3) / 2) * z ((n + 3) / 2) else 0
      set s2Z : ℤ := ∑ i ∈ Finset.Icc 2 (n + 1), z i * z (n + 3 - i)
      set s3Z : ℤ := ∑ i ∈ Finset.Icc 1 (n + 1), ∑ j ∈ Finset.Icc 1 (n + 2 - i),
        z i * z j * z (n + 3 - i - j)
      have hcast_eq : a389475 (n + 2) = ((lhsZ - s2Z + 2 * s3Z : ℤ) : ℚ) / 2 := by
        rw [a389475_succ_succ n]
        congr 1
        push_cast [lhsZ, s2Z, s3Z]
        have hl : (if (n + 3) % 2 = 0 then (3 : ℚ) ^ ((n + 3) / 2) * a389475 ((n + 3) / 2) else 0) =
            (if (n + 3) % 2 = 0 then (3 : ℚ) ^ ((n + 3) / 2) * (z ((n + 3) / 2) : ℚ) else 0) := by
          split_ifs with h
          · rw [hz ((n + 3) / 2) (by omega)]
          · rfl
        have h2 : (∑ i ∈ Finset.Icc 2 (n + 1), a389475 i * a389475 (n + 3 - i)) =
            ∑ i ∈ Finset.Icc 2 (n + 1), (z i : ℚ) * (z (n + 3 - i) : ℚ) := by
          apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_Icc] at hi
          rw [hz i (by omega), hz (n + 3 - i) (by omega)]
        have h3 : (∑ i ∈ Finset.Icc 1 (n + 1), ∑ j ∈ Finset.Icc 1 (n + 2 - i),
              a389475 i * a389475 j * a389475 (n + 3 - i - j)) =
            ∑ i ∈ Finset.Icc 1 (n + 1), ∑ j ∈ Finset.Icc 1 (n + 2 - i),
              (z i : ℚ) * (z j : ℚ) * (z (n + 3 - i - j) : ℚ) := by
          apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_Icc] at hi
          apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_Icc] at hj
          rw [hz i (by omega), hz j (by omega), hz (n + 3 - i - j) (by omega)]
        rw [hl, h2, h3]
      -- Prove 2 ∣ lhsZ - s2Z by pairing i ↔ n + 3 - i in s2Z
      have heven : (2 : ℤ) ∣ lhsZ - s2Z := by
        have hpair : ∀ (S : Finset ℕ) (f : ℕ → ℤ),
            (∀ i ∈ S, i ≤ n + 3) →
            (∀ i ∈ S, n + 3 - i ∈ S) →
            (∀ i ∈ S, i ≠ n + 3 - i) →
            (∀ i ∈ S, f (n + 3 - i) = f i) →
            (2 : ℤ) ∣ ∑ i ∈ S, f i := by
          intro S f hle hclosed hne hsym
          set Slt := S.filter (fun i => i < n + 3 - i)
          set Sgt := S.filter (fun i => n + 3 - i < i)
          have hdisj : Disjoint Slt Sgt := by
            rw [Finset.disjoint_left]; intro i h1 h2
            simp only [Slt, Sgt, Finset.mem_filter] at h1 h2; omega
          have hunion : S = Slt ∪ Sgt := by
            ext i; simp only [Slt, Sgt, Finset.mem_union, Finset.mem_filter]
            constructor
            · intro hi
              rcases lt_or_gt_of_ne (hne i hi) with h | h
              · exact Or.inl ⟨hi, h⟩
              · exact Or.inr ⟨hi, h⟩
            · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
          have hsum_eq : ∑ i ∈ Sgt, f i = ∑ i ∈ Slt, f i := by
            apply Finset.sum_bij (fun i _ => n + 3 - i)
            · intro i hi; simp only [Slt, Sgt, Finset.mem_filter] at hi ⊢
              rcases hi with ⟨hi1, hi2⟩
              have := hle i hi1
              exact ⟨hclosed i hi1, by omega⟩
            · intro a ha b hb hEq; simp only [Sgt, Finset.mem_filter] at ha hb
              have := hle a ha.1; have := hle b hb.1; omega
            · intro j hj; simp only [Slt, Sgt, Finset.mem_filter] at hj ⊢
              rcases hj with ⟨hj1, hj2⟩
              have := hle j hj1
              exact ⟨n + 3 - j, ⟨hclosed j hj1, by omega⟩, by omega⟩
            · intro i hi; simp only [Sgt, Finset.mem_filter] at hi; exact (hsym i hi.1).symm
          rw [hunion, Finset.sum_union hdisj, hsum_eq]
          exact ⟨∑ i ∈ Slt, f i, by ring⟩
        by_cases hpar : (n + 3) % 2 = 0
        · set k := (n + 3) / 2
          have h2k : n + 3 = 2 * k := by omega
          have hk_ge2 : 2 ≤ k := by omega
          have hk_mem : k ∈ Finset.Icc 2 (n + 1) := Finset.mem_Icc.mpr (by omega)
          have hlhs : lhsZ = (3 : ℤ) ^ k * z k := by simp [lhsZ, hpar, k]
          have hs2_split : s2Z = z k * z k + ∑ i ∈ (Finset.Icc 2 (n + 1)).erase k, z i * z (n + 3 - i) := by
            have := Finset.add_sum_erase (Finset.Icc 2 (n + 1)) (fun i => z i * z (n + 3 - i)) hk_mem
            rw [show n + 3 - k = k by omega] at this
            exact this.symm
          have hrest_even : (2 : ℤ) ∣ ∑ i ∈ (Finset.Icc 2 (n + 1)).erase k, z i * z (n + 3 - i) := by
            apply hpair
            · intro i hi; simp only [Finset.mem_erase, Finset.mem_Icc] at hi; omega
            · intro i hi; simp only [Finset.mem_erase, Finset.mem_Icc] at hi ⊢; omega
            · intro i hi; simp only [Finset.mem_erase, Finset.mem_Icc] at hi; omega
            · intro i hi; simp only [Finset.mem_erase, Finset.mem_Icc] at hi
              rw [show n + 3 - (n + 3 - i) = i by omega, mul_comm]
          have hdiag_even : (2 : ℤ) ∣ (3 : ℤ) ^ k * z k - z k * z k := by
            have h3odd : (3 : ℤ) ^ k % 2 = 1 := by
              induction k with
              | zero => rfl
              | succ m ihm => rw [pow_succ]; omega
            have hsub : (3 : ℤ) ^ k * z k - z k * z k = ((3 : ℤ) ^ k - 1) * z k - z k * (z k - 1) := by ring
            rw [hsub]
            apply dvd_sub
            · exact dvd_mul_of_dvd_left (by omega) _
            · exact Int.even_mul_pred_self (z k) |>.two_dvd
          rw [hlhs, hs2_split, show (3 : ℤ) ^ k * z k - (z k * z k + ∑ i ∈ (Finset.Icc 2 (n + 1)).erase k, z i * z (n + 3 - i)) =
              ((3 : ℤ) ^ k * z k - z k * z k) - ∑ i ∈ (Finset.Icc 2 (n + 1)).erase k, z i * z (n + 3 - i) by ring]
          exact dvd_sub hdiag_even hrest_even
        · have hlhs : lhsZ = 0 := by simp [lhsZ, hpar]
          have hs2_even : (2 : ℤ) ∣ s2Z := by
            apply hpair
            · intro i hi; simp only [Finset.mem_Icc] at hi; omega
            · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
            · intro i hi; simp only [Finset.mem_Icc] at hi; omega
            · intro i hi; simp only [Finset.mem_Icc] at hi
              rw [show n + 3 - (n + 3 - i) = i by omega, mul_comm]
          rw [hlhs, zero_sub]
          exact dvd_neg.mpr hs2_even
      rcases heven with ⟨q, hq⟩
      refine ⟨q + s3Z, ?_⟩
      rw [hcast_eq, hq]
      push_cast
      ring

/-- Frobenius in `Polynomial (ZMod 3)`: `convZ (convZ z z) z n ≡ (if 3 ∣ n then z (n/3) else 0) (mod 3)`. -/
private lemma triple_convZ_zmod3 (z : ℕ → ℤ) (n : ℕ) :
    (convZ (convZ z z) z n : ZMod 3) = if 3 ∣ n then (z (n / 3) : ZMod 3) else 0 := by
  let P : Polynomial (ZMod 3) := ∑ m ∈ Finset.range (n + 1), Polynomial.C (z m : ZMod 3) * Polynomial.X ^ m
  have hPcoeff : ∀ k ≤ n, P.coeff k = (z k : ZMod 3) := by
    intro k hk
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hne; simp [hne.symm]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  have hP2coeff : ∀ k ≤ n, (P * P).coeff k = (convZ z z k : ZMod 3) := by
    intro k hk
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * P.coeff j)]
    unfold convZ; push_cast
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    rw [hPcoeff i (by omega), hPcoeff (k - i) (by omega)]
  have hP3coeff : (P ^ 3).coeff n = (convZ (convZ z z) z n : ZMod 3) := by
    rw [show P ^ 3 = (P * P) * P by ring, Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (P * P).coeff i * P.coeff j)]
    have hR : (convZ (convZ z z) z n : ZMod 3) =
        ∑ i ∈ Finset.range (n + 1), (convZ z z i : ZMod 3) * (z (n - i) : ZMod 3) := by
      simp only [convZ, Int.cast_sum, Int.cast_mul]
    rw [hR]
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    rw [hP2coeff i (by omega), hPcoeff (n - i) (by omega)]
  have hFrob : P ^ 3 = ∑ m ∈ Finset.range (n + 1),
      Polynomial.C (z m : ZMod 3) * Polynomial.X ^ (3 * m) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hsum : (∑ m ∈ Finset.range (n + 1), Polynomial.C (z m : ZMod 3) * Polynomial.X ^ m) ^ 3 =
        ∑ m ∈ Finset.range (n + 1), (Polynomial.C (z m : ZMod 3) * Polynomial.X ^ m) ^ 3 :=
      map_sum (frobenius (Polynomial (ZMod 3)) 3) _ _
    rw [show P ^ 3 = _ from hsum]
    apply Finset.sum_congr rfl; intro m _
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm m 3, ZMod.pow_card]
  rw [← hP3coeff, hFrob]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h3 : 3 ∣ n
  · rw [if_pos h3, Finset.sum_eq_single (n / 3)]
    · have heq : 3 * (n / 3) = n := Nat.mul_div_cancel' h3
      simp [heq]
    · intro m _ hne
      have hne3 : n ≠ 3 * m := fun h => hne (by omega)
      simp [hne3]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · rw [if_neg h3]
    apply Finset.sum_eq_zero; intro m _
    have hne3 : n ≠ 3 * m := fun h => h3 ⟨m, h⟩
    simp [hne3]

private lemma int_cast_rat_num_den (z : ℤ) :
    (z : ℚ).den = 1 ∧ (z : ℚ).num = z := by
  have hd : (z : ℚ).den = 1 := by simp
  have hn : (z : ℚ).num = z := by
    have h := Rat.coe_int_num_of_den_eq_one hd
    exact_mod_cast h
  exact ⟨hd, hn⟩

private lemma zmod3_eq_iff_emod (a b : ℤ) :
    (a : ZMod 3) = (b : ZMod 3) → a % 3 = b % 3 := by
  intro h
  have hsub : ((a - b : ℤ) : ZMod 3) = 0 := by push_cast; exact sub_eq_zero.mpr h
  have hdvd : (3 : ℤ) ∣ a - b := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) 3).mp hsub
  omega

private lemma prove_main :
    (∀ m : ℕ,
      (if m % 2 = 0 then (3 : ℚ) ^ (m / 2) * a389475 (m / 2) else 0) =
        (if m = 2 then 2 else 0) + conv a389475 a389475 m - 2 * conv (conv a389475 a389475) a389475 m) ∧
    (∀ n : ℕ,
      (a389475 n).den = 1 ∧
      (conv (conv a389475 a389475) a389475 n).den = 1 ∧
      (conv a389475 a389475 n).den = 1 ∧
      (conv (conv a389475 a389475) a389475 n).num % 3 =
        (if 3 ∣ n then (a389475 (n / 3)).num else 0) % 3 ∧
      (conv a389475 a389475 n).num % 3 =
        ((if n = 2 then 1 else 0) + 2 * (if 3 ∣ n then (a389475 (n / 3)).num else 0)) % 3) := by
  refine ⟨func_eq, ?_⟩
  choose z hz using a389475_is_int
  have hfun : a389475 = fun k => (z k : ℚ) := funext hz
  have hconv2 : ∀ n, conv a389475 a389475 n = (convZ z z n : ℚ) := fun n => by
    rw [hfun, conv_cast]
  have hconv3 : ∀ n, conv (conv a389475 a389475) a389475 n = (convZ (convZ z z) z n : ℚ) := fun n => by
    have h2 : conv a389475 a389475 = fun k => (convZ z z k : ℚ) := funext hconv2
    rw [h2, hfun, conv_cast]
  intro n
  have hz0 : z 0 = 0 := by have := hz 0; rw [a389475] at this; exact_mod_cast this.symm
  rw [hz n, hconv3 n, hconv2 n,
      (int_cast_rat_num_den _).1, (int_cast_rat_num_den _).1, (int_cast_rat_num_den _).1,
      (int_cast_rat_num_den _).2, (int_cast_rat_num_den _).2]
  have h3num : (if 3 ∣ n then (a389475 (n / 3)).num else 0) = if 3 ∣ n then z (n / 3) else 0 := by
    split_ifs <;> simp [hz, (int_cast_rat_num_den _).2]
  rw [h3num]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · -- (4.a): A(x)^3 ≡ A(x^3) (mod 3)
    apply zmod3_eq_iff_emod
    rw [triple_convZ_zmod3 z n]
    split_ifs <;> simp
  · -- (4.b): A(x)^2 ≡ x^2 + 2 * A(x^3) (mod 3)
    have hfe := func_eq n
    rw [hconv2 n, hconv3 n, hz (n / 2)] at hfe
    have hfeZ : (if n % 2 = 0 then (3 : ℤ) ^ (n / 2) * z (n / 2) else 0) =
        (if n = 2 then 2 else 0) + convZ z z n - 2 * convZ (convZ z z) z n := by
      by_cases hn2 : n % 2 = 0 <;> by_cases hneq : n = 2 <;>
        simp only [hn2, hneq, ↓reduceIte] at hfe ⊢ <;> exact_mod_cast hfe
    have hlhs_mod3 : ((if n % 2 = 0 then (3 : ℤ) ^ (n / 2) * z (n / 2) else 0 : ℤ) : ZMod 3) = 0 := by
      split_ifs with h
      · by_cases h0 : n / 2 = 0
        · rw [h0, hz0, mul_zero]; simp
        · have hdvd : (3 : ℤ) ∣ (3 : ℤ) ^ (n / 2) * z (n / 2) :=
            dvd_mul_of_dvd_left (dvd_pow_self 3 h0) _
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdvd
      · simp
    apply zmod3_eq_iff_emod
    have hmod := congrArg (Int.cast : ℤ → ZMod 3) hfeZ
    rw [hlhs_mod3] at hmod
    push_cast at hmod
    rw [triple_convZ_zmod3 z n] at hmod
    have h3eq : (3 : ZMod 3) = 0 := by decide
    by_cases hneq : n = 2
    · subst hneq
      have hnd3 : ¬ (3 ∣ 2) := by decide
      simp only [↓reduceIte, hnd3] at hmod ⊢
      push_cast
      linear_combination -hmod - h3eq
    · by_cases h3 : 3 ∣ n
      · simp only [hneq, h3, ↓reduceIte] at hmod ⊢
        push_cast
        linear_combination -hmod
      · simp only [hneq, h3, ↓reduceIte] at hmod ⊢
        push_cast
        linear_combination -hmod

end OMA.P_oeis_a389475

theorem OMA.solution : type_of% @OMA.S_oeis_a389475.main :=
  OMA.P_oeis_a389475.prove_main
