import OMAStatements.S_arxiv_1801_04770

/-!
# A minimal-exponent reduction of Şiar and Keskin's Conjecture 32

Credit: @yuka30240

For even exponents the two factors give points on a common norm-two conic.
Squaring the corresponding elements and dividing by two gives two powers
of a fundamental norm-one unit. Their first coordinates are Chebyshev
values. The shift by one excludes even indices and forces the parameter
to have the form s² − 1. Every prime divisor of s divides both bases,
as in the coprimality obstruction in Theorem 23 of arXiv:1801.04770. For odd exponents it suffices to establish
uniqueness of the base on each squarefree twist.
-/

namespace OMA.R_arxiv_1801_04770_R2

def H1 : Prop :=
  ∀ (s : ℕ) (e i j a b : ℕ), 2 ≤ s → (e = 8 ∨ e = 10 ∨ e = 12) →
    2 < a → 2 < b → ¬ Nat.Coprime a b →
    (Polynomial.Chebyshev.T ℤ (2 * (i : ℤ) + 1)).eval ((s : ℤ) ^ 2 - 1) + 1 = (a : ℤ) ^ e →
    (Polynomial.Chebyshev.T ℤ (2 * (j : ℤ) + 1)).eval ((s : ℤ) ^ 2 - 1) + 1 = (b : ℤ) ^ e →
    a = b

def H2 : Prop :=
  ∀ d e a b u v : ℕ, Squarefree d → (e = 9 ∨ e = 15 ∨ e = 25) → 2 < a → 2 < b →
    d * u ^ 2 + 2 = a ^ e → d * v ^ 2 + 2 = b ^ e → a = b

def H3 : Prop :=
  ∀ d p a b u v : ℕ, Squarefree d → Nat.Prime p → 7 ≤ p → 2 < a → 2 < b →
    d * u ^ 2 + 2 = a ^ p → d * v ^ 2 + 2 = b ^ p → a = b

/-- Above 36, removing a prime factor at most five leaves an exponent above six. -/
lemma exponent_divisor {n : ℕ} (hn : 6 < n) :
    ∃ e : ℕ, e ∣ n ∧ ((e = 8 ∨ e = 10 ∨ e = 12) ∨
      (e = 9 ∨ e = 15 ∨ e = 25) ∨ (e.Prime ∧ 7 ≤ e)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n ≤ 36
    · interval_cases n <;> first
        | exact ⟨_, dvd_refl _, by decide⟩
        | exact ⟨8, by decide, by decide⟩
        | exact ⟨9, by decide, by decide⟩
        | exact ⟨10, by decide, by decide⟩
        | exact ⟨7, by decide, by decide⟩
        | exact ⟨11, by decide, by decide⟩
        | exact ⟨13, by decide, by decide⟩
        | exact ⟨17, by decide, by decide⟩
    obtain ⟨p, hp, q, hq⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
    by_cases hl : 7 ≤ p
    · exact ⟨p, ⟨q, hq⟩, Or.inr (Or.inr ⟨hp, hl⟩)⟩
    have hp' := hp.two_le
    have hq' : 6 < q := by
      by_contra! h
      have := Nat.mul_le_mul (show p ≤ 6 by omega) h
      omega
    have hqn : q < n := by nlinarith
    obtain ⟨e, he, ht⟩ := ih q hqn hq'
    exact ⟨e, he.trans ⟨p, by simpa [Nat.mul_comm] using hq⟩, ht⟩

lemma common_twist {A B x : ℕ} (ha : 0 < A) (h : A * B = x ^ 2) :
    ∃ d u v : ℕ, Squarefree d ∧ d * u ^ 2 = A ∧ d * v ^ 2 = B := by
  obtain ⟨d, u, hd, hu, hA, hfree⟩ := Nat.sq_mul_squarefree_of_pos ha
  have hux : u ^ 2 ∣ x ^ 2 := ⟨d * B, by rw [← h, ← hA]; ring⟩
  obtain ⟨w, hw⟩ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hux
  rw [← hA, hw, mul_pow, mul_assoc] at h
  have hB := Nat.eq_of_mul_eq_mul_left (pow_pos hu 2) h
  obtain ⟨v, hv⟩ := (hfree.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp
    (show d ∣ w ^ 2 from ⟨B, hB.symm⟩)
  refine ⟨d, u, v, hfree, by simpa [mul_comm] using hA, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hd
  rw [hB, hv]
  ring

open Polynomial Chebyshev

lemma pell_trace {d : ℤ} (g : Pell.Solution₁ d) (n : ℕ) :
    (T ℤ (n : ℤ)).eval g.x = (g ^ n).x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h₀ h₁ =>
    push_cast
    rw [T_add_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    push_cast at h₁
    rw [h₀, h₁]
    simp only [pow_succ, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
    linear_combination (g ^ n).x * g.prop

lemma rational_square {D u v : ℤ} (hu : u ≠ 0) (h : D * u ^ 2 = v ^ 2) : IsSquare D := by
  apply Rat.isSquare_intCast_iff.mp
  use (v : ℚ) / u
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have h' : (D : ℚ) * (u : ℚ) ^ 2 = (v : ℚ) ^ 2 := by exact_mod_cast h
  field_simp
  nlinarith only [h']

lemma trace_product (r m n : ℤ) :
    2 * (T ℤ m).eval r * (T ℤ n).eval r =
      (T ℤ (m+n)).eval r + (T ℤ (m-n)).eval r := by
  simpa using congrArg (Polynomial.eval r) (T_mul_T ℤ m n)

/-- Sum and difference forms of the Chebyshev half-angle identities at odd indices. -/
lemma odd_trace_identities (r j : ℤ) :
    (r+1) * ((T ℤ (2*j+1)).eval r + 1) = ((T ℤ (j+1)).eval r + (T ℤ j).eval r) ^ 2 ∧
    (r-1) * ((T ℤ (2*j+1)).eval r - 1) = ((T ℤ (j+1)).eval r - (T ℤ j).eval r) ^ 2 := by
  have h₀ := trace_product r j j
  have h₁ := trace_product r (j+1) (j+1)
  have h₂ := trace_product r (j+1) j
  have h₃ := trace_product r (2*j+1) 1
  simp only [sub_self, T_zero, eval_one, T_one, eval_X] at *
  ring_nf at h₀ h₁ h₂ h₃ ⊢
  simp only [T_one, eval_X] at h₂
  constructor <;> linarith only [h₀, h₁, h₂, h₃]

lemma odd_index_and_parameter {r z : ℤ} {n : ℕ} (hz : 0 < z)
    (h : (T ℤ (n : ℤ)).eval r + 1 = z ^ 2) :
    (∃ i : ℕ, n = 2 * i + 1) ∧ IsSquare (r + 1) := by
  rcases Nat.even_or_odd n with ⟨i, hi⟩ | ⟨i, hi⟩
  · subst n
    push_cast at h
    have h₂ := trace_product r i i
    simp only [sub_self, T_zero, eval_one] at h₂
    have he : 2 * ((T ℤ i).eval r) ^ 2 = z ^ 2 := by nlinarith only [h, h₂]
    have hn : (T ℤ i).eval r ≠ 0 := by rintro hh; rw [hh] at he; nlinarith
    have hns : ¬ IsSquare (2 : ℤ) := by
      rintro ⟨t, ht⟩
      have hl : -1 ≤ t := by nlinarith [sq_nonneg (t+2)]
      have hh : t ≤ 1 := by nlinarith [sq_nonneg (t-2)]
      interval_cases t <;> norm_num at ht
    exact (hns (rational_square hn he)).elim
  · refine ⟨⟨i, hi⟩, ?_⟩
    subst n
    push_cast at h
    have hs := (odd_trace_identities r (i : ℤ)).1
    rw [h] at hs
    exact rational_square hz.ne' hs

/-- Squaring a norm-two point and dividing by two gives coordinates (t² − 1, tu). -/
lemma norm_one_point {d t u : ℤ} (h : d * u ^ 2 + 2 = t ^ 2) :
    ∃ P : Pell.Solution₁ d, P.x = t ^ 2 - 1 ∧ P.y = t * u := by
  refine ⟨Pell.Solution₁.mk _ _ ?_, rfl, rfl⟩
  linear_combination -(t ^ 2) * h

lemma two_pell_indices {d t w u v : ℤ} (ht : 2 < t) (hw : 2 < w) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hA : d * u ^ 2 + 2 = t ^ 2) (hB : d * v ^ 2 + 2 = w ^ 2) :
    ∃ s i j : ℕ, 2 ≤ s ∧
      (T ℤ (2 * (i : ℤ) + 1)).eval ((s : ℤ) ^ 2 - 1) + 1 = t ^ 2 ∧
      (T ℤ (2 * (j : ℤ) + 1)).eval ((s : ℤ) ^ 2 - 1) + 1 = w ^ 2 := by
  obtain ⟨A, hAx, hAy⟩ := norm_one_point hA
  obtain ⟨B, hBx, hBy⟩ := norm_one_point hB
  have hAt : 1 < A.x := by nlinarith
  have hBt : 1 < B.x := by nlinarith
  obtain ⟨g, hg⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (Pell.Solution₁.d_pos_of_one_lt_x hAt) (Pell.Solution₁.d_nonsquare_of_one_lt_x hAt)
  obtain ⟨m, hm⟩ := hg.eq_pow_of_nonneg (by omega : 0 < A.x) (by rw [hAy]; positivity)
  obtain ⟨n, hn⟩ := hg.eq_pow_of_nonneg (by omega : 0 < B.x) (by rw [hBy]; positivity)
  have h₁ : (T ℤ m).eval g.x + 1 = t ^ 2 := by rw [pell_trace, ← hm, hAx]; ring
  have h₂ : (T ℤ n).eval g.x + 1 = w ^ 2 := by rw [pell_trace, ← hn, hBx]; ring
  obtain ⟨⟨i, rfl⟩, z, hz⟩ := odd_index_and_parameter (by omega) h₁
  obtain ⟨⟨j, rfl⟩, -⟩ := odd_index_and_parameter (by omega) h₂
  have hs : (z.natAbs : ℤ) ^ 2 - 1 = g.x := by rw [Int.natAbs_sq]; nlinarith
  refine ⟨z.natAbs, i, j, ?_, ?_, ?_⟩
  · have hgx := hg.1
    by_contra! h
    have hlo : (z.natAbs : ℤ) ≤ 1 := by exact_mod_cast (show z.natAbs ≤ 1 by omega)
    nlinarith [mul_self_le_mul_self (Int.natCast_nonneg z.natAbs) hlo]
  · rw [hs]; exact_mod_cast h₁
  · rw [hs]; exact_mod_cast h₂

/-- On this Chebyshev sequence, every shifted odd term is divisible by the seed squared. -/
lemma seed_sq_dvd {s a i e : ℕ}
    (h : (T ℤ (2 * (i : ℤ) + 1)).eval ((s : ℤ) ^ 2 - 1) + 1 = (a : ℤ) ^ e) :
    s ^ 2 ∣ a ^ e := by
  have hneg : (T ℤ (2 * (i : ℤ) + 1)).eval (-1) = -1 := by
    rw [T_eval_neg_one, Int.negOnePow_odd _ (show Odd (2 * (i : ℤ) + 1) from ⟨i, rfl⟩)]
    rfl
  have hdiv := Polynomial.sub_dvd_eval_sub ((s : ℤ) ^ 2 - 1) (-1) (T ℤ (2 * (i : ℤ) + 1))
  rw [hneg, sub_neg_eq_add, sub_neg_eq_add, sub_add_cancel, h] at hdiv
  exact_mod_cast hdiv

lemma even_exponent (h₁ : H1) {e a b d u v : ℕ}
    (he : e = 8 ∨ e = 10 ∨ e = 12) (ha : 2 < a) (hb : 2 < b)
    (hA : d * u ^ 2 + 2 = a ^ e) (hB : d * v ^ 2 + 2 = b ^ e) : a = b := by
  have hek : ∃ k : ℕ, 0 < k ∧ e = k * 2 := by
    rcases he with rfl | rfl | rfl
    · exact ⟨4, by decide, rfl⟩
    · exact ⟨5, by decide, rfl⟩
    · exact ⟨6, by decide, rfl⟩
  obtain ⟨k, hk, rfl⟩ := hek
  rw [pow_mul] at hA hB
  have ha' := ha.trans_le (Nat.le_self_pow hk.ne' a)
  have hb' := hb.trans_le (Nat.le_self_pow hk.ne' b)
  obtain ⟨s, i, j, hs, hi, hj⟩ := two_pell_indices (d := (d : ℤ))
    (t := (a : ℤ) ^ k) (w := (b : ℤ) ^ k) (u := (u : ℤ)) (v := (v : ℤ))
    (by exact_mod_cast ha') (by exact_mod_cast hb') (by positivity) (by positivity)
    (by exact_mod_cast hA) (by exact_mod_cast hB)
  rw [← pow_mul] at hi hj
  have hsA := seed_sq_dvd hi
  have hsB := seed_sq_dvd hj
  obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd (show s ≠ 1 by omega)
  have hpsq : p ∣ s ^ 2 := hps.trans (dvd_pow_self _ (by decide : 2 ≠ 0))
  have hcop := Nat.not_coprime_of_dvd_of_dvd hp.one_lt
    (hp.dvd_of_dvd_pow (hpsq.trans hsA)) (hp.dvd_of_dvd_pow (hpsq.trans hsB))
  exact h₁ s (k * 2) i j a b hs he ha hb hcop hi hj

theorem main : H1 → H2 → H3 → type_of% @OMA.S_arxiv_1801_04770.main := by
  intro h₁ h₂ h₃ a b n x ha hab eqn
  by_contra! hn
  obtain ⟨e, ⟨k, hk⟩, he⟩ := exponent_divisor hn
  have hk' : k ≠ 0 := by rintro rfl; simp_all
  have he' : e ≠ 0 := by rintro rfl; simp_all
  let A := a ^ k
  let B := b ^ k
  have hA : 2 < A := ha.trans_le (Nat.le_self_pow hk' a)
  have hAB : A < B := Nat.pow_lt_pow_left hab hk'
  have hB := hA.trans hAB
  have hAe := hA.trans_le (Nat.le_self_pow he' A)
  have hBe := hB.trans_le (Nat.le_self_pow he' B)
  have hAn : A ^ e = a ^ n := by rw [hk, mul_comm e k, pow_mul]
  have hBn : B ^ e = b ^ n := by rw [hk, mul_comm e k, pow_mul]
  have hn' : (A ^ e - 2) * (B ^ e - 2) = x ^ 2 := by
    rw [hAn] at hAe
    rw [hBn] at hBe
    rw [hAn, hBn]
    zify [hAe.le, hBe.le]
    exact eqn
  obtain ⟨d, u, v, hd, hu, hv⟩ := common_twist (by omega) hn'
  have hu' : d * u ^ 2 + 2 = A ^ e := by omega
  have hv' : d * v ^ 2 + 2 = B ^ e := by omega
  apply hAB.ne
  rcases he with h | h | ⟨hp, h⟩
  · exact even_exponent h₁ h hA hB hu' hv'
  · exact h₂ d e A B u v hd h hA hB hu' hv'
  · exact h₃ d e A B u v hd hp h hA hB hu' hv'

/-- A square product at a forbidden exponent uniquely determines the base. -/
lemma equal_bases_of_square (bound : type_of% @OMA.S_arxiv_1801_04770.main)
    {a b e : ℕ} (ha : 2 < a) (hb : 2 < b) (he : 6 < e)
    (h : IsSquare (((a : ℤ) ^ e - 2) * ((b : ℤ) ^ e - 2))) : a = b := by
  obtain ⟨z, hz⟩ := h
  have hx : ((a : ℤ) ^ e - 2) * ((b : ℤ) ^ e - 2) = (z.natAbs : ℤ) ^ 2 := by
    rw [Int.natAbs_sq, sq, hz]
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (he.not_ge (bound a b e z.natAbs ha hab hx)).elim
  · exact hab
  · exact (he.not_ge (bound b a e z.natAbs hb hab (mul_comm _ _ |>.trans hx))).elim

lemma equal_bases_on_twist (bound : type_of% @OMA.S_arxiv_1801_04770.main)
    {a b d e u v : ℕ} (ha : 2 < a) (hb : 2 < b) (he : 6 < e)
    (hA : d * u ^ 2 + 2 = a ^ e) (hB : d * v ^ 2 + 2 = b ^ e) : a = b := by
  apply equal_bases_of_square bound ha hb he
  have hA' : (d : ℤ) * (u : ℤ) ^ 2 + 2 = (a : ℤ) ^ e := by exact_mod_cast hA
  have hB' : (d : ℤ) * (v : ℤ) ^ 2 + 2 = (b : ℤ) ^ e := by exact_mod_cast hB
  exact ⟨(d : ℤ) * u * v, by rw [← hA', ← hB']; ring⟩

/-- Every failure of a step produces a counterexample to the original exponent bound. -/
theorem converse (bound : type_of% @OMA.S_arxiv_1801_04770.main) : H1 ∧ H2 ∧ H3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro s e i j a b hs he ha hb _ hi hj
    let r := (s : ℤ) ^ 2 - 1
    change (T ℤ (2 * (i : ℤ) + 1)).eval r + 1 = (a : ℤ) ^ e at hi
    change (T ℤ (2 * (j : ℤ) + 1)).eval r + 1 = (b : ℤ) ^ e at hj
    have hri := (odd_trace_identities r (i : ℤ)).2
    have hrj := (odd_trace_identities r (j : ℤ)).2
    have hr : r - 1 ≠ 0 := by
      have hs' : (2 : ℤ) ≤ s := by exact_mod_cast hs
      dsimp [r]
      nlinarith [sq_nonneg ((s : ℤ) - 2)]
    apply equal_bases_of_square bound (e := e) ha hb (by omega)
    apply rational_square hr (v := ((T ℤ ((i : ℤ)+1)).eval r - (T ℤ i).eval r) *
      ((T ℤ ((j : ℤ)+1)).eval r - (T ℤ j).eval r))
    rw [← hi, ← hj, mul_pow, ← hri, ← hrj]
    ring
  · intro d e a b u v _ he ha hb hu hv
    exact equal_bases_on_twist bound ha hb (by omega) hu hv
  · intro d p a b u v _ _ hp ha hb hu hv
    exact equal_bases_on_twist bound ha hb hp hu hv

end OMA.R_arxiv_1801_04770_R2
