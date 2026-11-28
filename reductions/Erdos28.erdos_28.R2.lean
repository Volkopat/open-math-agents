import FormalConjectures.ErdosProblems.«28»

/-!
# Reduction `Erdos28.erdos_28.R2` of Erdős Problem 28

Credit: `@sanchan`

Strictly strengthens `Erdos28.erdos_28.R1` by proving unconditionally inside `main`:
1. Grekos-Sándor-Konstantoulas lower bound (`limsup sumRep A n ≥ 6`): for every asymptotic
   basis `A ⊆ ℕ` with `(A + A)ᶜ` finite, `sumRep A n ≥ 6` holds for infinitely many `n`,
   proved via finite discrete Fourier Parseval on roots of unity (elementary, zero integrals).
2. Exact finite-edit normalization (eliminating `R1.H2` unconditionally): any asymptotic basis
   with bounded `sumRep` extends to an exact basis `B = F ∪ A` with `0 ∈ B` and
   `1 ≤ sumRep B n ≤ M` (with `6 ≤ M`) for all `n`.
3. Counting-function sandwich (`N + 1 ≤ B(N)^2 ≤ M * (2 * N + 1)`), additive-energy upper
   bound (`∑_{n ≤ 2N} sumRep S n ^ 2 ≤ M * S.card ^ 2` for every `S ⊆ B ∩ [0, N]`), and
   aperiodicity (`B` contains no infinite arithmetic progression).

Splits the remaining open bounded-cap exact-basis problem into two independent regimes:
- `H1`: thin-prefix regime (`B(N)^2 < 4 * N` for infinitely many `N`)
- `H2`: uniformly dense regime (`4 * N ≤ B(N)^2` eventually)
-/

open Filter Set AdditiveCombinatorics Finset
open scoped Classical Pointwise BigOperators

namespace OMA.R_Erdos28_erdos_28_R2

/- ### Part 1: Basic properties of sumRep and parity -/

lemma sumRep_monotone {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    sumRep A n ≤ sumRep B n := by
  simp only [sumRep_def]
  apply Finset.card_le_card
  intro p hp
  simp only [mem_filter] at hp ⊢
  exact ⟨hp.1, h hp.2.1, h hp.2.2⟩

lemma sumRep_le_add_one (A : Set ℕ) (n : ℕ) : sumRep A n ≤ n + 1 := by
  rw [sumRep_def]
  calc ({p ∈ Finset.HasAntidiagonal.antidiagonal n | p.1 ∈ A ∧ p.2 ∈ A}).card
      ≤ (Finset.HasAntidiagonal.antidiagonal n).card := Finset.card_filter_le _ _
    _ = n + 1 := Finset.Nat.card_antidiagonal n

lemma sumRep_insert_le (A : Set ℕ) (a n : ℕ) :
    sumRep (insert a A) n ≤ sumRep A n + 2 := by
  simp only [sumRep_def]
  let S := (Finset.HasAntidiagonal.antidiagonal n).filter fun p => p.1 ∈ A ∧ p.2 ∈ A
  let T := (Finset.HasAntidiagonal.antidiagonal n).filter fun p => p.1 ∈ insert a A ∧ p.2 ∈ insert a A
  have hsub : T ⊆ S ∪ {(a, n - a), (n - a, a)} := by
    intro p hp
    simp only [T, mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_insert_iff] at hp
    rcases hp with ⟨hsum, h1 | h1, h2 | h2⟩
    · apply Finset.mem_union_right
      have hp2 : p.2 = n - a := by omega
      have : p = (a, n - a) := Prod.ext h1 hp2
      simp [this]
    · apply Finset.mem_union_right
      have hp2 : p.2 = n - a := by omega
      have : p = (a, n - a) := Prod.ext h1 hp2
      simp [this]
    · apply Finset.mem_union_right
      have hp1 : p.1 = n - a := by omega
      have : p = (n - a, a) := Prod.ext hp1 h2
      simp [this]
    · apply Finset.mem_union_left
      exact mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum, h1, h2⟩
  have hle : T.card ≤ S.card + 2 :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_le_two _))
  convert hle

lemma sumRep_union_finset_le (A : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    sumRep ((F : Set ℕ) ∪ A) n ≤ sumRep A n + 2 * F.card := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    rw [Finset.coe_insert, Set.insert_union, Finset.card_insert_of_notMem ha]
    have h1 := sumRep_insert_le ((F : Set ℕ) ∪ A) a n
    omega

lemma sumRep_pos_iff (A : Set ℕ) (n : ℕ) : 1 ≤ sumRep A n ↔ n ∈ A + A := by
  rw [sumRep_def, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at h
    exact ⟨a, h.2.1, b, h.2.2, h.1⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr hab, ha, hb⟩⟩

lemma sumRep_filter_eq {A : Set ℕ} {N n : ℕ} (hn : n ≤ N) :
    sumRep (((Finset.Iic N).filter (· ∈ A) : Finset ℕ) : Set ℕ) n = sumRep A n := by
  simp only [sumRep_def]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_coe, Finset.mem_Iic]
  constructor
  · rintro ⟨hab, ⟨_, ha⟩, ⟨_, hb⟩⟩; exact ⟨hab, ha, hb⟩
  · rintro ⟨hab, ha, hb⟩; exact ⟨hab, ⟨by omega, ha⟩, ⟨by omega, hb⟩⟩

lemma sumRep_parity (A : Set ℕ) (n : ℕ) :
    (∃ a ∈ A, n = 2 * a) → Odd (sumRep A n) := by
  rintro ⟨a, ha, rfl⟩
  rw [sumRep_def]
  let S := (Finset.HasAntidiagonal.antidiagonal (2 * a)).filter fun p => p.1 ∈ A ∧ p.2 ∈ A
  have hdiag : (a, a) ∈ S := mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega), ha, ha⟩
  let S' := S.erase (a, a)
  have hcard : S.card = S'.card + 1 := (Finset.card_erase_add_one hdiag).symm
  have heven : Even S'.card := by
    let T := S'.filter fun p => p.1 < p.2
    let U := S'.filter fun p => p.2 < p.1
    have hdisj : Disjoint T U := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := (Finset.mem_filter.mp hp1).2
      have h2 := (Finset.mem_filter.mp hp2).2
      omega
    have hunion : T ∪ U = S' := by
      ext p
      simp only [T, U, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hp
        have hne : p ≠ (a, a) := (mem_erase.mp hp).1
        have hsum : p.1 + p.2 = 2 * a := Finset.HasAntidiagonal.mem_antidiagonal.mp (mem_filter.mp (mem_erase.mp hp).2).1
        have hpne : p.1 ≠ p.2 := fun heq => hne (Prod.ext (by omega) (by omega))
        rcases lt_or_gt_of_ne hpne with hlt | hgt
        · exact Or.inl ⟨hp, hlt⟩
        · exact Or.inr ⟨hp, hgt⟩
    have hcard_eq : T.card = U.card := by
      apply Finset.card_bij (fun p _ => (p.2, p.1))
      · intro p hp
        have h1 := mem_filter.mp hp
        have h2 := mem_erase.mp h1.1
        have h3 := mem_filter.mp h2.2
        have hsum : p.1 + p.2 = 2 * a := Finset.HasAntidiagonal.mem_antidiagonal.mp h3.1
        refine mem_filter.mpr ⟨mem_erase.mpr ⟨?_, mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega), h3.2.2, h3.2.1⟩⟩, h1.2⟩
        intro hEq
        have := Prod.mk.inj hEq
        omega
      · intro p1 _ p2 _ h
        exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
      · intro p hp
        have h1 := mem_filter.mp hp
        have h2 := mem_erase.mp h1.1
        have h3 := mem_filter.mp h2.2
        have hsum : p.1 + p.2 = 2 * a := Finset.HasAntidiagonal.mem_antidiagonal.mp h3.1
        refine ⟨(p.2, p.1), mem_filter.mpr ⟨mem_erase.mpr ⟨?_, mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega), h3.2.2, h3.2.1⟩⟩, h1.2⟩, rfl⟩
        intro hEq
        have := Prod.mk.inj hEq
        omega
    rw [← hunion, Finset.card_union_of_disjoint hdisj, ← hcard_eq]
    exact ⟨T.card, rfl⟩
  rw [hcard]
  exact Even.add_one heven

lemma sumRep_even_of_not_double (A : Set ℕ) (n : ℕ) (h : ¬ ∃ a ∈ A, n = 2 * a) :
    Even (sumRep A n) := by
  rw [sumRep_def]
  let S := (Finset.HasAntidiagonal.antidiagonal n).filter fun p => p.1 ∈ A ∧ p.2 ∈ A
  let T := S.filter fun p => p.1 < p.2
  let U := S.filter fun p => p.2 < p.1
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (mem_filter.mp hp1).2
    have h2 := (mem_filter.mp hp2).2
    omega
  have hunion : T ∪ U = S := by
    ext p
    simp only [T, U, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hp
      have hM := mem_filter.mp hp
      have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hM.1
      have hpne : p.1 ≠ p.2 := fun heq => h ⟨p.1, hM.2.1, by omega⟩
      rcases lt_or_gt_of_ne hpne with hlt | hgt
      · exact Or.inl ⟨hp, hlt⟩
      · exact Or.inr ⟨hp, hgt⟩
  have hcard_eq : T.card = U.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      have h1 := mem_filter.mp hp
      have h2 := mem_filter.mp h1.1
      have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp h2.1
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega), h2.2.2, h2.2.1⟩, h1.2⟩
    · intro p1 _ p2 _ h
      exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
    · intro p hp
      have h1 := mem_filter.mp hp
      have h2 := mem_filter.mp h1.1
      have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp h2.1
      exact ⟨(p.2, p.1), mem_filter.mpr ⟨mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega), h2.2.2, h2.2.1⟩, h1.2⟩, rfl⟩
  change Even S.card
  rw [← hunion, Finset.card_union_of_disjoint hdisj, ← hcard_eq]
  exact ⟨T.card, rfl⟩

/- ### Part 2: Elementary inequalities (harmonic dyadic bound, Bernoulli, powers) -/

lemma harmonic_pow_two_le (m : ℕ) :
    ∑ j ∈ Finset.Icc (1 : ℕ) (2 ^ m), (1 : ℝ) / (j : ℝ) ≤ (m : ℝ) + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : Finset.Icc (1 : ℕ) (2 ^ (m + 1)) =
        Finset.Icc 1 (2 ^ m) ∪ Finset.Icc (2 ^ m + 1) (2 ^ (m + 1)) := by
      ext j
      simp only [Finset.mem_union, Finset.mem_Icc]
      have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
      omega
    have hdisj : Disjoint (Finset.Icc (1 : ℕ) (2 ^ m)) (Finset.Icc (2 ^ m + 1) (2 ^ (m + 1))) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_Icc] at hj1 hj2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have htail : ∑ j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1)), (1 : ℝ) / (j : ℝ) ≤ 1 := by
      have hcard : (Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1))).card = 2 ^ m := by
        rw [Nat.card_Icc]
        have : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
        omega
      calc ∑ j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1)), (1 : ℝ) / (j : ℝ)
          ≤ ∑ _j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1)), (1 : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            have hj1 : 2 ^ m + 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have h2pos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
            have hle : ((2 ^ m : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show 2 ^ m ≤ j by omega)
            exact one_div_le_one_div_of_le h2pos hle
        _ = ((2 ^ m : ℕ) : ℝ) * ((1 : ℝ) / ((2 ^ m : ℕ) : ℝ)) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ = 1 := by
            have h2pos : ((2 ^ m : ℕ) : ℝ) ≠ 0 := by positivity
            field_simp [h2pos]
    push_cast
    linarith

lemma bernoulli_sub_le (x : ℝ) (hx1 : x ≤ 1) :
    ∀ k : ℕ, 1 - (k : ℝ) * x ≤ (1 - x) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    push_cast
    have h1 : (1 - (k : ℝ) * x) * (1 - x) ≤ (1 - x) ^ k * (1 - x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    nlinarith [sq_nonneg x, Nat.cast_nonneg (α := ℝ) k]

lemma one_sub_inv_pow_le_half (T : ℕ) (hT : 2 ≤ T) :
    (1 - (1 : ℝ) / (T : ℝ)) ^ T ≤ (1 : ℝ) / 2 := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hTm1 : (0 : ℝ) < (T : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  have hinv : (1 - (1 : ℝ) / (T : ℝ)) = ((1 : ℝ) + (1 : ℝ) / ((T : ℝ) - 1))⁻¹ := by
    field_simp [hTpos.ne', hTm1.ne']
    ring
  rw [hinv, inv_pow]
  have hbern : (2 : ℝ) ≤ ((1 : ℝ) + (1 : ℝ) / ((T : ℝ) - 1)) ^ T := by
    have hb := one_add_mul_le_pow (a := (1 : ℝ) / ((T : ℝ) - 1)) (by linarith [div_pos one_pos hTm1]) T
    have hge2 : (2 : ℝ) ≤ 1 + (T : ℝ) * ((1 : ℝ) / ((T : ℝ) - 1)) := by
      have : (1 : ℝ) ≤ (T : ℝ) / ((T : ℝ) - 1) := by
        rw [one_le_div hTm1]; linarith
      linarith [show (T : ℝ) * ((1 : ℝ) / ((T : ℝ) - 1)) = (T : ℝ) / ((T : ℝ) - 1) by ring]
    linarith
  exact (inv_anti₀ (by norm_num) hbern).trans_eq (by norm_num)

lemma twentyfive_sq_le_pow_two (T : ℕ) (hT : 10 ≤ T) :
    25 * T ^ 2 ≤ 2 ^ (2 * T) := by
  induction T, hT using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hpow : 2 ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]; norm_num; ring
    rw [hpow]
    nlinarith only [ih, hk]

lemma nat_le_pow_two_pred (m : ℕ) (hm : 1 ≤ m) : m ≤ 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hpow : 2 ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]; ring
    rw [hpow]
    have h1 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    omega

lemma quad_le_pow_two_40 (m : ℕ) (hm : 40 ≤ m) :
    10000 * (12 * m + 20) ^ 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    have hstep : (12 * (k + 1) + 20) ^ 2 ≤ 2 * (12 * k + 20) ^ 2 := by
      have h1 : 24 * (12 * k + 20) + 144 ≤ (12 * k + 20) ^ 2 := by nlinarith only [hk]
      nlinarith only [h1]
    calc 10000 * (12 * (k + 1) + 20) ^ 2
        ≤ 10000 * (2 * (12 * k + 20) ^ 2) := Nat.mul_le_mul_left _ hstep
      _ = 10000 * (12 * k + 20) ^ 2 * 2 := by ring
      _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right _ ih

/- ### Part 3: Finite Discrete Fourier Parseval and Dirichlet kernel L1 bound -/

lemma root_of_unity_sum_zero {K : ℕ} (hK : 0 < K) {d : ℤ} (hd0 : d ≠ 0)
    (hdK : d.natAbs < K) :
    ∑ j : Fin K, Complex.exp ((2 * Real.pi * (j.val : ℝ) * (d : ℝ) / (K : ℝ) : ℝ) * Complex.I) = 0 := by
  let ω : ℂ := Complex.exp ((2 * Real.pi * (d : ℝ) / (K : ℝ) : ℝ) * Complex.I)
  have hterm : ∀ j : Fin K,
      Complex.exp ((2 * Real.pi * (j.val : ℝ) * (d : ℝ) / (K : ℝ) : ℝ) * Complex.I) = ω ^ j.val := by
    intro j
    dsimp only [ω]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum_range : (∑ j : Fin K, ω ^ j.val) = ∑ j ∈ Finset.range K, ω ^ j :=
    Fin.sum_univ_eq_sum_range (fun j => ω ^ j) K
  have hωK : ω ^ K = 1 := by
    dsimp only [ω]
    rw [← Complex.exp_nat_mul]
    rw [Complex.exp_eq_one_iff]
    refine ⟨d, ?_⟩
    have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
    push_cast
    field_simp [hK0]
  have hωne1 : ω ≠ 1 := by
    intro h1
    dsimp only [ω] at h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have him := congrArg Complex.im hm
    simp at him
    have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    have hEqR : (d : ℝ) / (K : ℝ) = (m : ℝ) := by
      have h1' : (2 * Real.pi) * ((d : ℝ) / (K : ℝ)) = (2 * Real.pi) * (m : ℝ) := by
        rw [mul_div_assoc] at him
        linarith
      exact mul_left_cancel₀ hpi0 h1'
    have hEqZ : d = m * (K : ℤ) := by
      have hR : (d : ℝ) = (m : ℝ) * (K : ℝ) := (div_eq_iff hKpos.ne').mp hEqR
      exact_mod_cast hR
    have hdvd : (K : ℤ) ∣ d := ⟨m, by linarith⟩
    have hnatdvd : K ∣ d.natAbs := Int.natCast_dvd.mp hdvd
    have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
    have hle : K ≤ d.natAbs := Nat.le_of_dvd hpos hnatdvd
    omega
  have hgeom := geom_sum_mul ω K
  rw [hωK, sub_self] at hgeom
  have hsubne : ω - 1 ≠ 0 := sub_ne_zero.mpr hωne1
  have hzero : ∑ j ∈ Finset.range K, ω ^ j = 0 := (mul_eq_zero.mp hgeom).resolve_right hsubne
  simp_rw [hterm]
  rw [hsum_range, hzero]

lemma dft_parseval {K M : ℕ} (hMK : M < K) (c : ℕ → ℝ) :
    (∑ j : Fin K, ‖∑ n ∈ Finset.range (M + 1),
      (c n : ℂ) * Complex.exp ((2 * Real.pi * (j.val : ℝ) * (n : ℝ) / (K : ℝ) : ℝ) * Complex.I)‖ ^ 2) =
      (K : ℝ) * ∑ n ∈ Finset.range (M + 1), c n ^ 2 := by
  have hKpos : 0 < K := by omega
  let ζ : Fin K → ℕ → ℂ := fun j n =>
    Complex.exp ((2 * Real.pi * (j.val : ℝ) * (n : ℝ) / (K : ℝ) : ℝ) * Complex.I)
  have hnorm_sq : ∀ j : Fin K,
      ((‖∑ n ∈ Finset.range (M + 1), (c n : ℂ) * ζ j n‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
        (c a : ℂ) * (c b : ℂ) * Complex.exp ((2 * Real.pi * (j.val : ℝ) * ((a : ℤ) - (b : ℤ) : ℤ) / (K : ℝ) : ℝ) * Complex.I) := by
    intro j
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rw [map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [map_mul, Complex.conj_ofReal]
    have hconj : starRingEnd ℂ (ζ j b) =
        Complex.exp ((-(2 * Real.pi * (j.val : ℝ) * (b : ℝ) / (K : ℝ)) : ℝ) * Complex.I) := by
      dsimp only [ζ]
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [hconj]
    have hexp_mul : ζ j a * Complex.exp ((-(2 * Real.pi * (j.val : ℝ) * (b : ℝ) / (K : ℝ)) : ℝ) * Complex.I) =
        Complex.exp ((2 * Real.pi * (j.val : ℝ) * ((a : ℤ) - (b : ℤ) : ℤ) / (K : ℝ) : ℝ) * Complex.I) := by
      dsimp only [ζ]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc (c b : ℂ) * Complex.exp ((-(2 * Real.pi * (j.val : ℝ) * (b : ℝ) / (K : ℝ)) : ℝ) * Complex.I) *
          ((c a : ℂ) * ζ j a)
        = (c a : ℂ) * (c b : ℂ) *
          (ζ j a * Complex.exp ((-(2 * Real.pi * (j.val : ℝ) * (b : ℝ) / (K : ℝ)) : ℝ) * Complex.I)) := by ring
      _ = (c a : ℂ) * (c b : ℂ) *
          Complex.exp ((2 * Real.pi * (j.val : ℝ) * ((a : ℤ) - (b : ℤ) : ℤ) / (K : ℝ) : ℝ) * Complex.I) := by
        rw [hexp_mul]
  have hC : ((∑ j : Fin K, ‖∑ n ∈ Finset.range (M + 1), (c n : ℂ) * ζ j n‖ ^ 2 : ℝ) : ℂ) =
      (((K : ℝ) * ∑ n ∈ Finset.range (M + 1), c n ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [hnorm_sq]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext a
      rw [Finset.sum_comm]
    have hinner : ∀ a ∈ Finset.range (M + 1), ∀ b ∈ Finset.range (M + 1),
        (∑ j : Fin K, (c a : ℂ) * (c b : ℂ) *
          Complex.exp ((2 * Real.pi * (j.val : ℝ) * ((a : ℤ) - (b : ℤ) : ℤ) / (K : ℝ) : ℝ) * Complex.I)) =
        if a = b then (K : ℂ) * (c a : ℂ) ^ 2 else 0 := by
      intro a ha b hb
      rw [← Finset.mul_sum]
      by_cases hab : a = b
      · subst hab
        simp [sq, mul_comm]
      · have hd0 : (a : ℤ) - (b : ℤ) ≠ 0 := by omega
        have haM : a < M + 1 := Finset.mem_range.mp ha
        have hbM : b < M + 1 := Finset.mem_range.mp hb
        have hdK : ((a : ℤ) - (b : ℤ)).natAbs < K := by omega
        have hz := root_of_unity_sum_zero hKpos hd0 hdK
        rw [hz, mul_zero, if_neg hab]
    have hsimp : ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
        (∑ j : Fin K, (c a : ℂ) * (c b : ℂ) *
          Complex.exp ((2 * Real.pi * (j.val : ℝ) * ((a : ℤ) - (b : ℤ) : ℤ) / (K : ℝ) : ℝ) * Complex.I)) =
        ∑ a ∈ Finset.range (M + 1), (K : ℂ) * (c a : ℂ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_congr rfl (hinner a ha)]
      simp [ha]
    rw [hsimp, ← Finset.mul_sum]
    push_cast
    rfl
  exact Complex.ofReal_injective hC

lemma norm_one_sub_mul_exp_ge {r θ : ℝ} (hr : (1 : ℝ) / 4 ≤ r) :
    |Real.sin (θ / 2)| ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
  have hsq : |Real.sin (θ / 2)| ^ 2 ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 := by
    rw [sq_abs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hre : ((1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re = 1 - r * Real.cos θ := by
      rw [Complex.exp_ofReal_mul_I]
      simp [Complex.sub_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    have him : ((1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im = -(r * Real.sin θ) := by
      rw [Complex.exp_ofReal_mul_I]
      simp [Complex.sub_im, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    rw [hre, him]
    have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have := Real.cos_two_mul' (θ / 2)
      have h2 : 2 * (θ / 2) = θ := by ring
      rw [h2] at this
      nlinarith [Real.cos_sq_add_sin_sq (θ / 2)]
    have hexp : (1 - r * Real.cos θ) * (1 - r * Real.cos θ) + (-(r * Real.sin θ)) * (-(r * Real.sin θ)) =
        (1 - r) ^ 2 + 4 * r * Real.sin (θ / 2) ^ 2 := by
      linear_combination r ^ 2 * hcs - 2 * r * hcos
    rw [hexp]
    nlinarith [sq_nonneg (1 - r), sq_nonneg (Real.sin (θ / 2)), hr]
  nlinarith [abs_nonneg (Real.sin (θ / 2)),
    norm_nonneg ((1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))]

lemma geom_poly_L1_bound {K N : ℕ} (hK : 2 ≤ K) {r : ℝ} (hr0 : (1 : ℝ) / 4 ≤ r) (hr1 : r < 1) :
    (∑ j : Fin K, ‖∑ n ∈ Finset.range (N + 1),
      ((r : ℂ) * Complex.exp ((2 * Real.pi * (j.val : ℝ) / (K : ℝ) : ℝ) * Complex.I)) ^ n‖) ≤
      1 / (1 - r) + 2 * (K : ℝ) * ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  let f : Fin K → ℝ := fun j =>
    ‖∑ n ∈ Finset.range (N + 1),
      ((r : ℂ) * Complex.exp ((2 * Real.pi * (j.val : ℝ) / (K : ℝ) : ℝ) * Complex.I)) ^ n‖
  have h0_mem : (⟨0, by omega⟩ : Fin K) ∈ (univ : Finset (Fin K)) := mem_univ _
  have hsplit := Finset.add_sum_erase (univ : Finset (Fin K)) f h0_mem
  have hf0 : f ⟨0, by omega⟩ ≤ 1 / (1 - r) := by
    dsimp only [f]
    simp only [Nat.cast_zero, mul_zero, zero_div, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    have hsumR : (∑ n ∈ Finset.range (N + 1), ((r : ℂ) ^ n)) =
        ((∑ n ∈ Finset.range (N + 1), r ^ n : ℝ) : ℂ) := by push_cast; rfl
    rw [hsumR, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (by linarith) _)]
    have hg := geom_sum_mul r (N + 1)
    have hpos : 0 < 1 - r := by linarith
    have hpow0 : 0 ≤ r ^ (N + 1) := pow_nonneg (by linarith) _
    rw [le_div_iff₀ hpos]
    linarith
  have htail_pt : ∀ j ∈ (univ : Finset (Fin K)).erase ⟨0, by omega⟩,
      f j ≤ (K : ℝ) / (j.val : ℝ) + (K : ℝ) / ((K - j.val : ℕ) : ℝ) := by
    intro j hj
    have hjne0 : j.val ≠ 0 := fun h => (mem_erase.mp hj).1 (Fin.ext h)
    have hjpos : 1 ≤ j.val := by omega
    have hjlt : j.val < K := j.isLt
    let θ : ℝ := 2 * Real.pi * (j.val : ℝ) / (K : ℝ)
    let z : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    have hznorm : ‖z‖ = r := by
      dsimp only [z]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith),
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hsin_lb : min (2 * (j.val : ℝ) / (K : ℝ)) (2 * ((K - j.val : ℕ) : ℝ) / (K : ℝ)) ≤
        |Real.sin (θ / 2)| := by
      have hθ2 : θ / 2 = Real.pi * (j.val : ℝ) / (K : ℝ) := by dsimp only [θ]; ring
      rw [hθ2]
      by_cases hhalf : 2 * j.val ≤ K
      · have hle : Real.pi * (j.val : ℝ) / (K : ℝ) ≤ Real.pi / 2 := by
          rw [div_le_div_iff₀ hKpos (by norm_num)]
          have h2j : 2 * (j.val : ℝ) ≤ (K : ℝ) := by exact_mod_cast hhalf
          nlinarith [Real.pi_pos]
        have hnn : 0 ≤ Real.pi * (j.val : ℝ) / (K : ℝ) := by positivity
        have hms := Real.mul_le_sin hnn hle
        have hval : 2 / Real.pi * (Real.pi * (j.val : ℝ) / (K : ℝ)) = 2 * (j.val : ℝ) / (K : ℝ) := by
          field_simp [Real.pi_pos.ne', hKpos.ne']
        rw [hval] at hms
        exact (min_le_left _ _).trans (hms.trans (le_abs_self _))
      · have h2j' : 2 * (K - j.val) ≤ K := by omega
        have hle : Real.pi * ((K - j.val : ℕ) : ℝ) / (K : ℝ) ≤ Real.pi / 2 := by
          rw [div_le_div_iff₀ hKpos (by norm_num)]
          have h2j : 2 * ((K - j.val : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h2j'
          nlinarith [Real.pi_pos]
        have hnn : 0 ≤ Real.pi * ((K - j.val : ℕ) : ℝ) / (K : ℝ) := by positivity
        have hms := Real.mul_le_sin hnn hle
        have hval : 2 / Real.pi * (Real.pi * ((K - j.val : ℕ) : ℝ) / (K : ℝ)) =
            2 * ((K - j.val : ℕ) : ℝ) / (K : ℝ) := by
          field_simp [Real.pi_pos.ne', hKpos.ne']
        rw [hval] at hms
        have hsin_eq : Real.sin (Real.pi * (j.val : ℝ) / (K : ℝ)) =
            Real.sin (Real.pi * ((K - j.val : ℕ) : ℝ) / (K : ℝ)) := by
          rw [← Real.sin_pi_sub]
          congr 1
          rw [Nat.cast_sub hjlt.le]
          field_simp [hKpos.ne']
        rw [hsin_eq]
        exact (min_le_right _ _).trans (hms.trans (le_abs_self _))
    have hdenom_pos : 0 < min (2 * (j.val : ℝ) / (K : ℝ)) (2 * ((K - j.val : ℕ) : ℝ) / (K : ℝ)) := by
      apply lt_min
      · have : (0 : ℝ) < (j.val : ℝ) := by exact_mod_cast (show 0 < j.val by omega)
        positivity
      · have : (0 : ℝ) < ((K - j.val : ℕ) : ℝ) := by exact_mod_cast (show 0 < K - j.val by omega)
        positivity
    have h1mz : min (2 * (j.val : ℝ) / (K : ℝ)) (2 * ((K - j.val : ℕ) : ℝ) / (K : ℝ)) ≤ ‖(1 : ℂ) - z‖ :=
      hsin_lb.trans (norm_one_sub_mul_exp_ge hr0)
    have h1mz_pos : 0 < ‖(1 : ℂ) - z‖ := lt_of_lt_of_le hdenom_pos h1mz
    have hgeom_eq : (∑ n ∈ Finset.range (N + 1), z ^ n) * ((1 : ℂ) - z) = 1 - z ^ (N + 1) := by
      have hg := geom_sum_mul z (N + 1)
      linear_combination -hg
    have hnum_le : ‖(1 : ℂ) - z ^ (N + 1)‖ ≤ 2 := by
      calc ‖(1 : ℂ) - z ^ (N + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ (N + 1)‖ := norm_sub_le _ _
        _ = 1 + r ^ (N + 1) := by rw [norm_one, norm_pow, hznorm]
        _ ≤ 2 := by
          have : r ^ (N + 1) ≤ 1 := pow_le_one₀ (by linarith) hr1.le
          linarith
    have hfj_le : f j ≤ 2 / ‖(1 : ℂ) - z‖ := by
      have hmul : f j * ‖(1 : ℂ) - z‖ = ‖(1 : ℂ) - z ^ (N + 1)‖ := by
        dsimp only [f]
        rw [← norm_mul, hgeom_eq]
      rw [le_div_iff₀ h1mz_pos, hmul]
      exact hnum_le
    have hrec : 2 / ‖(1 : ℂ) - z‖ ≤
        2 / min (2 * (j.val : ℝ) / (K : ℝ)) (2 * ((K - j.val : ℕ) : ℝ) / (K : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) hdenom_pos h1mz
    have hmin_bound : 2 / min (2 * (j.val : ℝ) / (K : ℝ)) (2 * ((K - j.val : ℕ) : ℝ) / (K : ℝ)) ≤
        (K : ℝ) / (j.val : ℝ) + (K : ℝ) / ((K - j.val : ℕ) : ℝ) := by
      rcases le_total (2 * (j.val : ℝ) / (K : ℝ)) (2 * ((K - j.val : ℕ) : ℝ) / (K : ℝ)) with h | h
      · rw [min_eq_left h]
        have hjR : (0 : ℝ) < (j.val : ℝ) := by exact_mod_cast (show 0 < j.val by omega)
        have hkjR : (0 : ℝ) ≤ (K : ℝ) / ((K - j.val : ℕ) : ℝ) := by positivity
        have heq : 2 / (2 * (j.val : ℝ) / (K : ℝ)) = (K : ℝ) / (j.val : ℝ) := by
          field_simp [hjR.ne', hKpos.ne']
        linarith
      · rw [min_eq_right h]
        have hkjR : (0 : ℝ) < ((K - j.val : ℕ) : ℝ) := by exact_mod_cast (show 0 < K - j.val by omega)
        have hjR : (0 : ℝ) ≤ (K : ℝ) / (j.val : ℝ) := by positivity
        have heq : 2 / (2 * ((K - j.val : ℕ) : ℝ) / (K : ℝ)) = (K : ℝ) / ((K - j.val : ℕ) : ℝ) := by
          field_simp [hkjR.ne', hKpos.ne']
        linarith
    exact hfj_le.trans (hrec.trans hmin_bound)
  have hsum_tail : ∑ j ∈ (univ : Finset (Fin K)).erase ⟨0, by omega⟩, f j ≤
      2 * (K : ℝ) * ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ) := by
    calc ∑ j ∈ (univ : Finset (Fin K)).erase ⟨0, by omega⟩, f j
        ≤ ∑ j ∈ (univ : Finset (Fin K)).erase ⟨0, by omega⟩,
            ((K : ℝ) / (j.val : ℝ) + (K : ℝ) / ((K - j.val : ℕ) : ℝ)) :=
          Finset.sum_le_sum htail_pt
      _ = (∑ j ∈ (univ : Finset (Fin K)).erase ⟨0, by omega⟩, (K : ℝ) / (j.val : ℝ)) +
          (∑ j ∈ (univ : Finset (Fin K)).erase ⟨0, by omega⟩, (K : ℝ) / ((K - j.val : ℕ) : ℝ)) :=
          Finset.sum_add_distrib
      _ ≤ (K : ℝ) * (∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ)) +
          (K : ℝ) * (∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ)) := by
          have h1 : (∑ j ∈ (univ : Finset (Fin K)).erase ⟨0, by omega⟩, (K : ℝ) / (j.val : ℝ)) ≤
              (K : ℝ) * ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ) := by
            have hrew : ∀ j : Fin K, (K : ℝ) / (j.val : ℝ) = (K : ℝ) * ((1 : ℝ) / (j.val : ℝ)) :=
              fun j => by ring
            simp_rw [hrew, ← Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ hKpos.le
            let emb : Fin K → ℕ := fun j => j.val
            have hinj : Set.InjOn emb ((univ : Finset (Fin K)).erase ⟨0, by omega⟩) :=
              fun _ _ _ _ h => Fin.ext h
            rw [← Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hinj]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
              have hne : j.val ≠ 0 := fun h => (mem_erase.mp hj).1 (Fin.ext h)
              have hjlt : j.val < K := j.isLt
              dsimp only [emb]
              exact Finset.mem_Icc.mpr ⟨by omega, hjlt.le⟩
            · intro _ _ _; positivity
          have h2 : (∑ j ∈ (univ : Finset (Fin K)).erase ⟨0, by omega⟩, (K : ℝ) / ((K - j.val : ℕ) : ℝ)) ≤
              (K : ℝ) * ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ) := by
            have hrew : ∀ j : Fin K, (K : ℝ) / ((K - j.val : ℕ) : ℝ) = (K : ℝ) * ((1 : ℝ) / ((K - j.val : ℕ) : ℝ)) :=
              fun j => by ring
            simp_rw [hrew, ← Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ hKpos.le
            let emb : Fin K → ℕ := fun j => K - j.val
            have hinj : Set.InjOn emb ((univ : Finset (Fin K)).erase ⟨0, by omega⟩) := by
              intro a _ b _ h
              dsimp only [emb] at h
              exact Fin.ext (by omega)
            rw [← Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hinj]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
              have hne : j.val ≠ 0 := fun h => (mem_erase.mp hj).1 (Fin.ext h)
              have hjlt : j.val < K := j.isLt
              dsimp only [emb]
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            · intro _ _ _; positivity
          linarith
      _ = 2 * (K : ℝ) * ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ) := by ring
  change ∑ j : Fin K, f j ≤ _
  linarith

/- ### Part 4: Grekos-Sándor-Konstantoulas theorem (limsup sumRep A n >= 6) -/

lemma poly_sq_coeff (S : Finset ℕ) (N : ℕ) (hS : S ⊆ Finset.Iic N) (z : ℂ) :
    (∑ a ∈ S, z ^ a) ^ 2 =
      ∑ n ∈ Finset.range (2 * N + 1), ((sumRep (S : Set ℕ) n : ℝ) : ℂ) * z ^ n := by
  rw [sq, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  have hmap : ∀ p ∈ S ×ˢ S, p.1 + p.2 ∈ Finset.range (2 * N + 1) := by
    intro p hp
    have h1 : p.1 ≤ N := Finset.mem_Iic.mp (hS (mem_product.mp hp).1)
    have h2 : p.2 ≤ N := Finset.mem_Iic.mp (hS (mem_product.mp hp).2)
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro n _
  have hfib : (S ×ˢ S).filter (fun p => p.1 + p.2 = n) =
      (Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ (S : Set ℕ) ∧ p.2 ∈ (S : Set ℕ)) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_coe]
    tauto
  rw [hfib, sumRep_def]
  have hterm : ∀ p ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ (S : Set ℕ) ∧ p.2 ∈ (S : Set ℕ)),
      z ^ p.1 * z ^ p.2 = z ^ n := by
    intro p hp
    rw [← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp (mem_filter.mp hp).1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  norm_cast

lemma poly_sq_real_coeff (S : Finset ℕ) (N : ℕ) (hS : S ⊆ Finset.Iic N) (x : ℝ) :
    (∑ a ∈ S, x ^ a) ^ 2 =
      ∑ n ∈ Finset.range (2 * N + 1), (sumRep (S : Set ℕ) n : ℝ) * x ^ n := by
  have hC := poly_sq_coeff S N hS (x : ℂ)
  apply Complex.ofReal_injective
  push_cast
  exact hC

lemma six_step_Y_bound (A : Set ℕ) (N1 N : ℕ) (r D : ℝ)
    (hN1N : N1 ≤ N)
    (hle5 : ∀ n ≥ N1, sumRep A n ≤ 5)
    (hr_ge : (1 : ℝ) / 4 ≤ r) (hr_lt1 : r < 1)
    (hD_eq : D = 1 / (1 - r ^ 2))
    (hD_big : (100 * (N1 + 4) ^ 3 + 40 * N1 + 10000 : ℝ) ≤ D) :
    ∑ a ∈ (Finset.Iic N).filter (· ∈ A), r ^ (4 * a) ≤ (3 / 100 : ℝ) * D := by
  let S : Finset ℕ := (Finset.Iic N).filter (· ∈ A)
  have hSsub : S ⊆ Finset.Iic N := Finset.filter_subset _ _
  let Y : ℝ := ∑ a ∈ S, r ^ (4 * a)
  have hr2_pos : 0 < 1 - r ^ 2 := by nlinarith only [hr_ge, hr_lt1]
  have hD10000 : (10000 : ℝ) ≤ D := by
    have hnn : (0 : ℝ) ≤ 100 * ((N1 : ℝ) + 4) ^ 3 + 40 * (N1 : ℝ) := by positivity
    linarith only [hnn, hD_big]
  have hD_pos : 0 < D := by linarith only [hD10000]
  have hYnn : 0 ≤ Y := Finset.sum_nonneg fun _ _ => pow_nonneg (by linarith only [hr_ge]) _
  have hY2 : Y ^ 2 ≤ (N1 : ℝ) ^ 2 + 5 * D := by
    have hYsq : Y ^ 2 = ∑ n ∈ Finset.range (2 * N + 1), (sumRep (S : Set ℕ) n : ℝ) * (r ^ 4) ^ n := by
      have hrew : Y = ∑ a ∈ S, (r ^ 4) ^ a := by
        dsimp only [Y]; apply Finset.sum_congr rfl; intro a _; rw [← pow_mul]
      rw [hrew]
      exact poly_sq_real_coeff S N hSsub (r ^ 4)
    rw [hYsq]
    have hsplit : Finset.range (2 * N + 1) = Finset.range N1 ∪ Finset.Ico N1 (2 * N + 1) := by
      ext n; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range N1) (Finset.Ico N1 (2 * N + 1)) := by
      rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
    rw [hsplit, Finset.sum_union hdisj]
    have hhead : ∑ n ∈ Finset.range N1, (sumRep (S : Set ℕ) n : ℝ) * (r ^ 4) ^ n ≤ (N1 : ℝ) ^ 2 := by
      calc ∑ n ∈ Finset.range N1, (sumRep (S : Set ℕ) n : ℝ) * (r ^ 4) ^ n
          ≤ ∑ _n ∈ Finset.range N1, (N1 : ℝ) := by
            apply Finset.sum_le_sum
            intro n hn
            have hnlt : n < N1 := Finset.mem_range.mp hn
            have hrp : (r ^ 4) ^ n ≤ 1 :=
              pow_le_one₀ (by positivity) (pow_le_one₀ (by linarith only [hr_ge]) hr_lt1.le)
            have hsr : (sumRep (S : Set ℕ) n : ℝ) ≤ (N1 : ℝ) := by
              have h1 := sumRep_le_add_one (S : Set ℕ) n
              exact_mod_cast (show sumRep (S : Set ℕ) n ≤ N1 by omega)
            have hsr_nn : (0 : ℝ) ≤ (sumRep (S : Set ℕ) n : ℝ) := Nat.cast_nonneg _
            nlinarith only [hrp, hsr, hsr_nn]
        _ = (N1 : ℝ) ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have htail : ∑ n ∈ Finset.Ico N1 (2 * N + 1), (sumRep (S : Set ℕ) n : ℝ) * (r ^ 4) ^ n ≤ 5 * D := by
      have hle : ∑ n ∈ Finset.Ico N1 (2 * N + 1), (sumRep (S : Set ℕ) n : ℝ) * (r ^ 4) ^ n ≤
          ∑ n ∈ Finset.range (2 * N + 1), 5 * (r ^ 2) ^ n := by
        calc ∑ n ∈ Finset.Ico N1 (2 * N + 1), (sumRep (S : Set ℕ) n : ℝ) * (r ^ 4) ^ n
            ≤ ∑ n ∈ Finset.Ico N1 (2 * N + 1), 5 * (r ^ 2) ^ n := by
              apply Finset.sum_le_sum
              intro n hn
              have hnN1 : N1 ≤ n := (Finset.mem_Ico.mp hn).1
              have hsr : sumRep (S : Set ℕ) n ≤ 5 :=
                (sumRep_monotone (fun x hx => (mem_filter.mp hx).2) n).trans (hle5 n hnN1)
              have hsrR : (sumRep (S : Set ℕ) n : ℝ) ≤ 5 := by exact_mod_cast hsr
              have hr42 : (r ^ 4) ^ n ≤ (r ^ 2) ^ n :=
                pow_le_pow_left₀ (by positivity)
                  (pow_le_pow_of_le_one (by linarith only [hr_ge]) hr_lt1.le (by norm_num)) n
              have hpow_nn : 0 ≤ (r ^ 2) ^ n := by positivity
              have hsr_nn : (0 : ℝ) ≤ (sumRep (S : Set ℕ) n : ℝ) := Nat.cast_nonneg _
              nlinarith only [hsrR, hr42, hpow_nn, hsr_nn]
          _ ≤ ∑ n ∈ Finset.range (2 * N + 1), 5 * (r ^ 2) ^ n := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro n hn; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
              · intro _ _ _; positivity
      have hgeom : ∑ n ∈ Finset.range (2 * N + 1), (r ^ 2) ^ n ≤ D := by
        have hg := geom_sum_mul (r ^ 2) (2 * N + 1)
        rw [hD_eq, le_div_iff₀ hr2_pos]
        have hpow_nn : 0 ≤ (r ^ 2) ^ (2 * N + 1) := by positivity
        linarith only [hg, hpow_nn]
      rw [← Finset.mul_sum] at hle
      linarith only [hle, hgeom]
    linarith only [hhead, htail]
  have hN1_nat : N1 ^ 2 ≤ 100 * (N1 + 4) ^ 3 + 40 * N1 + 10000 := by nlinarith
  have hN1D : (N1 : ℝ) ^ 2 ≤ D := by
    have h1 : (N1 : ℝ) ^ 2 ≤ (100 * (N1 + 4) ^ 3 + 40 * N1 + 10000 : ℝ) := by exact_mod_cast hN1_nat
    linarith only [h1, hD_big]
  have hsq : Y ^ 2 ≤ ((3 / 100 : ℝ) * D) ^ 2 := by
    nlinarith only [hY2, hN1D, hD10000]
  change Y ≤ (3 / 100 : ℝ) * D
  nlinarith only [hsq, hYnn, hD_pos]

lemma six_step_X_lower (A : Set ℕ) (N1 N T : ℕ) (r D : ℝ)
    (hN1N : N1 ≤ N) (hT10 : 10 ≤ T) (hT40 : 40 * N1 ≤ T)
    (hge1 : ∀ n ≥ N1, 1 ≤ sumRep A n)
    (hr_eq : r = 1 - (1 : ℝ) / (T : ℝ))
    (hr_ge : (1 : ℝ) / 4 ≤ r) (hr_lt1 : r < 1)
    (hD_eq : D = 1 / (1 - r ^ 2)) (hD_pos : 0 < D)
    (hr2N : r ^ (2 * N) ≤ 1 / ((2 ^ (2 * T) : ℕ) : ℝ))
    (hY_le : ∑ a ∈ (Finset.Iic N).filter (· ∈ A), r ^ (4 * a) ≤ (3 / 100 : ℝ) * D) :
    (13 / 10 : ℝ) * Real.sqrt D ≤ ∑ a ∈ (Finset.Iic N).filter (· ∈ A), r ^ (2 * a) := by
  let S : Finset ℕ := (Finset.Iic N).filter (· ∈ A)
  have hSsub : S ⊆ Finset.Iic N := Finset.filter_subset _ _
  let X : ℝ := ∑ a ∈ S, r ^ (2 * a)
  let Y : ℝ := ∑ a ∈ S, r ^ (4 * a)
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hr2_pos : 0 < 1 - r ^ 2 := by nlinarith only [hr_ge, hr_lt1]
  have hXnn : 0 ≤ X := Finset.sum_nonneg fun _ _ => pow_nonneg (by linarith only [hr_ge]) _
  have hX2_eq : X ^ 2 = ∑ n ∈ Finset.range (2 * N + 1), (sumRep (S : Set ℕ) n : ℝ) * (r ^ 2) ^ n := by
    have hrew : X = ∑ a ∈ S, (r ^ 2) ^ a := by
      dsimp only [X]; apply Finset.sum_congr rfl; intro a _; rw [← pow_mul]
    rw [hrew]
    exact poly_sq_real_coeff S N hSsub (r ^ 2)
  have hX2_ge_Icc : ∑ n ∈ Finset.Icc N1 N, (sumRep (S : Set ℕ) n : ℝ) * (r ^ 2) ^ n ≤ X ^ 2 := by
    rw [hX2_eq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn; exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
    · intro _ _ _; positivity
  have hpt_lb : ∀ n ∈ Finset.Icc N1 N,
      (2 - (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0)) * (r ^ 2) ^ n ≤
      (sumRep (S : Set ℕ) n : ℝ) * (r ^ 2) ^ n := by
    intro n hn
    have hn1 : N1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn2 : n ≤ N := (Finset.mem_Icc.mp hn).2
    have heq : sumRep (S : Set ℕ) n = sumRep A n := sumRep_filter_eq hn2
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [heq]
    by_cases hdbl : ∃ a ∈ S, n = 2 * a
    · rw [if_pos hdbl]
      have h1 : (1 : ℝ) ≤ (sumRep A n : ℝ) := by exact_mod_cast hge1 n hn1
      linarith only [h1]
    · rw [if_neg hdbl]
      have hnotA : ¬ ∃ a ∈ A, n = 2 * a := by
        rintro ⟨a, ha, rfl⟩
        exact hdbl ⟨a, mem_filter.mpr ⟨Finset.mem_Iic.mpr (by omega), ha⟩, rfl⟩
      have hev := sumRep_even_of_not_double A n hnotA
      have hpos := hge1 n hn1
      obtain ⟨t, ht⟩ := hev
      have h2 : 2 ≤ sumRep A n := by omega
      have h2R : (2 : ℝ) ≤ (sumRep A n : ℝ) := by exact_mod_cast h2
      linarith only [h2R]
  have hsum_dbl : ∑ n ∈ Finset.Icc N1 N, (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0) * (r ^ 2) ^ n ≤ Y := by
    have hrew : (∑ n ∈ Finset.Icc N1 N, (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0) * (r ^ 2) ^ n) =
        ∑ n ∈ (Finset.Icc N1 N).filter (fun n => ∃ a ∈ S, n = 2 * a), (r ^ 2) ^ n := by
      rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro n _; split_ifs <;> simp
    rw [hrew]
    have hsub_img : (Finset.Icc N1 N).filter (fun n => ∃ a ∈ S, n = 2 * a) ⊆ S.image (2 * ·) := by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := (mem_filter.mp hn).2
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    calc ∑ n ∈ (Finset.Icc N1 N).filter (fun n => ∃ a ∈ S, n = 2 * a), (r ^ 2) ^ n
        ≤ ∑ n ∈ S.image (2 * ·), (r ^ 2) ^ n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_img fun _ _ _ => by positivity
      _ = ∑ a ∈ S, (r ^ 2) ^ (2 * a) := by
          rw [Finset.sum_image (fun a _ b _ h => by omega)]
      _ = Y := by
          dsimp only [Y]; apply Finset.sum_congr rfl; intro a _; rw [← pow_mul]; ring_nf
  have hgeom_Icc : ∑ n ∈ Finset.Icc N1 N, (r ^ 2) ^ n = ((r ^ 2) ^ N1 - (r ^ 2) ^ (N + 1)) * D := by
    have hIcc : Finset.Icc N1 N = (Finset.range (N + 1)) \ (Finset.range N1) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range]; omega
    have hsub : Finset.range N1 ⊆ Finset.range (N + 1) := Finset.range_mono (by omega)
    rw [hIcc, Finset.sum_sdiff_eq_sub hsub]
    have hg1 := geom_sum_mul (r ^ 2) (N + 1)
    have hg2 := geom_sum_mul (r ^ 2) N1
    rw [hD_eq]
    have hne : (1 - r ^ 2 : ℝ) ≠ 0 := hr2_pos.ne'
    have h1 : ∑ n ∈ Finset.range (N + 1), (r ^ 2) ^ n = (1 - (r ^ 2) ^ (N + 1)) / (1 - r ^ 2) := by
      rw [eq_div_iff hne]; linarith only [hg1]
    have h2 : ∑ n ∈ Finset.range N1, (r ^ 2) ^ n = (1 - (r ^ 2) ^ N1) / (1 - r ^ 2) := by
      rw [eq_div_iff hne]; linarith only [hg2]
    rw [h1, h2]
    field_simp [hne]
    ring
  have hr2N1_ge : (19 / 20 : ℝ) ≤ (r ^ 2) ^ N1 := by
    rw [← pow_mul]
    have hb := bernoulli_sub_le (1 / (T : ℝ)) (by
      have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast (show 1 ≤ T by omega)
      exact div_le_one_of_le₀ hT1 hTpos.le) (2 * N1)
    have hfrac : (2 * N1 : ℝ) * (1 / (T : ℝ)) ≤ 1 / 20 := by
      have hT40R : (40 : ℝ) * (N1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT40
      rw [mul_one_div, div_le_iff₀ hTpos]
      linarith only [hT40R]
    have hcast : ((2 * N1 : ℕ) : ℝ) = (2 * N1 : ℝ) := by push_cast; ring
    rw [hcast] at hb
    rw [hr_eq]
    linarith only [hb, hfrac]
  have hr2N_le : (r ^ 2) ^ (N + 1) ≤ (1 / 20 : ℝ) := by
    rw [← pow_mul]
    have hle : r ^ (2 * (N + 1)) ≤ r ^ (2 * N) :=
      pow_le_pow_of_le_one (by linarith only [hr_ge]) hr_lt1.le (by omega)
    have h2T20 : (20 : ℝ) ≤ ((2 ^ (2 * T) : ℕ) : ℝ) := by
      have h1 : 20 ≤ 2 ^ (2 * T) := by
        calc 20 ≤ 25 * T ^ 2 := by nlinarith only [hT10]
          _ ≤ 2 ^ (2 * T) := twentyfive_sq_le_pow_two T hT10
      exact_mod_cast h1
    have hinv20 : 1 / ((2 ^ (2 * T) : ℕ) : ℝ) ≤ 1 / 20 :=
      one_div_le_one_div_of_le (by norm_num) h2T20
    linarith only [hle, hr2N, hinv20]
  have hX2_lb : (169 / 100 : ℝ) * D ≤ X ^ 2 := by
    have hsum_le := Finset.sum_le_sum hpt_lb
    have hexp : ∑ n ∈ Finset.Icc N1 N, (2 - (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0)) * (r ^ 2) ^ n =
        2 * ∑ n ∈ Finset.Icc N1 N, (r ^ 2) ^ n -
        ∑ n ∈ Finset.Icc N1 N, (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0) * (r ^ 2) ^ n := by
      simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hexp, hgeom_Icc] at hsum_le
    nlinarith only [hX2_ge_Icc, hsum_le, hsum_dbl, hr2N1_ge, hr2N_le, hY_le, hD_pos]
  have hsq_lb : ((13 / 10 : ℝ) * Real.sqrt D) ^ 2 ≤ X ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD_pos.le]
    linarith only [hX2_lb]
  change (13 / 10 : ℝ) * Real.sqrt D ≤ X
  nlinarith only [Real.sqrt_nonneg D, hXnn, hsq_lb]

lemma six_step_parseval_diff (A : Set ℕ) (N1 N : ℕ) (r D : ℝ)
    (hN1N : N1 ≤ N)
    (hge1 : ∀ n ≥ N1, 1 ≤ sumRep A n) (hle5 : ∀ n ≥ N1, sumRep A n ≤ 5)
    (hr_ge : (1 : ℝ) / 4 ≤ r) (hr_lt1 : r < 1)
    (hD_eq : D = 1 / (1 - r ^ 2))
    (hD_big : (100 * (N1 + 4) ^ 3 + 40 * N1 + 10000 : ℝ) ≤ D)
    (hY_le : ∑ a ∈ (Finset.Iic N).filter (· ∈ A), r ^ (4 * a) ≤ (3 / 100 : ℝ) * D)
    (h25N : 25 * (N : ℝ) * r ^ (2 * N) ≤ 1) :
    ∑ j : Fin (2 * N + 1),
      ‖(∑ a ∈ (Finset.Iic N).filter (· ∈ A),
          ((r : ℂ) * Complex.exp ((2 * Real.pi * (j.val : ℝ) / ((2 * N + 1 : ℕ) : ℝ) : ℝ) * Complex.I)) ^ a) ^ 2 -
        ∑ n ∈ Finset.range (N + 1),
          (3 : ℂ) * ((r : ℂ) * Complex.exp ((2 * Real.pi * (j.val : ℝ) / ((2 * N + 1 : ℕ) : ℝ) : ℝ) * Complex.I)) ^ n‖ ^ 2 ≤
      ((2 * N + 1 : ℕ) : ℝ) * ((121 / 100 : ℝ) * D) := by
  let S : Finset ℕ := (Finset.Iic N).filter (· ∈ A)
  have hSsub : S ⊆ Finset.Iic N := Finset.filter_subset _ _
  let Y : ℝ := ∑ a ∈ S, r ^ (4 * a)
  let K : ℕ := 2 * N + 1
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hr2_pos : 0 < 1 - r ^ 2 := by nlinarith only [hr_ge, hr_lt1]
  have hD10000 : (10000 : ℝ) ≤ D := by
    have hnn : (0 : ℝ) ≤ 100 * ((N1 : ℝ) + 4) ^ 3 + 40 * (N1 : ℝ) := by positivity
    linarith only [hnn, hD_big]
  let ζ : Fin K → ℂ := fun j => Complex.exp ((2 * Real.pi * (j.val : ℝ) / (K : ℝ) : ℝ) * Complex.I)
  have hζ_pow : ∀ (j : Fin K) (n : ℕ),
      ζ j ^ n = Complex.exp ((2 * Real.pi * (j.val : ℝ) * (n : ℝ) / (K : ℝ) : ℝ) * Complex.I) := by
    intro j n
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  let cD : ℕ → ℝ := fun n =>
    if n ≤ N then ((sumRep (S : Set ℕ) n : ℝ) - 3) * r ^ n
    else (sumRep (S : Set ℕ) n : ℝ) * r ^ n
  have hdiff_eq : ∀ j : Fin K,
      (∑ a ∈ S, ((r : ℂ) * ζ j) ^ a) ^ 2 - ∑ n ∈ Finset.range (N + 1), (3 : ℂ) * ((r : ℂ) * ζ j) ^ n =
      ∑ n ∈ Finset.range (2 * N + 1),
        (cD n : ℂ) * Complex.exp ((2 * Real.pi * (j.val : ℝ) * (n : ℝ) / (K : ℝ) : ℝ) * Complex.I) := by
    intro j
    have hP2 : (∑ a ∈ S, ((r : ℂ) * ζ j) ^ a) ^ 2 = ∑ n ∈ Finset.range (2 * N + 1),
        ((sumRep (S : Set ℕ) n : ℝ) : ℂ) * ((r : ℂ) * ζ j) ^ n :=
      poly_sq_coeff S N hSsub ((r : ℂ) * ζ j)
    have hQ_ext : ∑ n ∈ Finset.range (N + 1), (3 : ℂ) * ((r : ℂ) * ζ j) ^ n =
        ∑ n ∈ Finset.range (2 * N + 1), (if n ≤ N then (3 : ℂ) * ((r : ℂ) * ζ j) ^ n else 0) := by
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [mem_filter, Finset.mem_range]
      omega
    rw [hP2, hQ_ext, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [cD]
    rw [mul_pow, ← hζ_pow j n]
    split_ifs <;> push_cast <;> ring
  change ∑ j : Fin K,
    ‖(∑ a ∈ S, ((r : ℂ) * ζ j) ^ a) ^ 2 - ∑ n ∈ Finset.range (N + 1), (3 : ℂ) * ((r : ℂ) * ζ j) ^ n‖ ^ 2 ≤
    (K : ℝ) * ((121 / 100 : ℝ) * D)
  simp_rw [hdiff_eq]
  rw [dft_parseval (K := K) (M := 2 * N) (by dsimp only [K]; omega) cD]
  apply mul_le_mul_of_nonneg_left _ hKpos.le
  have hsplit1 : Finset.range (2 * N + 1) = Finset.range (N + 1) ∪ Finset.Icc (N + 1) (2 * N) := by
    ext n; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]; omega
  have hdisj1 : Disjoint (Finset.range (N + 1)) (Finset.Icc (N + 1) (2 * N)) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_range, Finset.mem_Icc] at h1 h2; omega
  have hsplit2 : Finset.range (N + 1) = Finset.range N1 ∪ Finset.Icc N1 N := by
    ext n; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]; omega
  have hdisj2 : Disjoint (Finset.range N1) (Finset.Icc N1 N) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_range, Finset.mem_Icc] at h1 h2; omega
  rw [hsplit1, Finset.sum_union hdisj1, hsplit2, Finset.sum_union hdisj2]
  have hpart1 : ∑ n ∈ Finset.range N1, cD n ^ 2 ≤ (N1 : ℝ) * ((N1 : ℝ) + 4) ^ 2 := by
    calc ∑ n ∈ Finset.range N1, cD n ^ 2
        ≤ ∑ _n ∈ Finset.range N1, ((N1 : ℝ) + 4) ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hnlt : n < N1 := Finset.mem_range.mp hn
          have hnN : n ≤ N := by omega
          dsimp only [cD]
          rw [if_pos hnN, mul_pow]
          have hrp : (r ^ n) ^ 2 ≤ 1 :=
            pow_le_one₀ (by positivity) (pow_le_one₀ (by linarith only [hr_ge]) hr_lt1.le)
          have hsr : (sumRep (S : Set ℕ) n : ℝ) ≤ (N1 : ℝ) := by
            have := sumRep_le_add_one (S : Set ℕ) n
            exact_mod_cast (show sumRep (S : Set ℕ) n ≤ N1 by omega)
          have hsr_nn : (0 : ℝ) ≤ (sumRep (S : Set ℕ) n : ℝ) := Nat.cast_nonneg _
          have hN1_nn : (0 : ℝ) ≤ (N1 : ℝ) := Nat.cast_nonneg _
          have hsq : ((sumRep (S : Set ℕ) n : ℝ) - 3) ^ 2 ≤ ((N1 : ℝ) + 4) ^ 2 := by
            nlinarith only [hsr, hsr_nn, hN1_nn]
          have hsq_nn : 0 ≤ ((sumRep (S : Set ℕ) n : ℝ) - 3) ^ 2 := sq_nonneg _
          nlinarith only [hsq, hrp, hsq_nn]
      _ = (N1 : ℝ) * ((N1 : ℝ) + 4) ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hpart2 : ∑ n ∈ Finset.Icc N1 N, cD n ^ 2 ≤ D + 3 * Y := by
    have hpt2 : ∀ n ∈ Finset.Icc N1 N,
        cD n ^ 2 ≤ (1 + 3 * (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0)) * (r ^ 2) ^ n := by
      intro n hn
      have hn1 : N1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn2 : n ≤ N := (Finset.mem_Icc.mp hn).2
      dsimp only [cD]
      rw [if_pos hn2, mul_pow, ← pow_mul, show n * 2 = 2 * n by ring, pow_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [sumRep_filter_eq hn2]
      have h1 := hge1 n hn1
      have h5 := hle5 n hn1
      by_cases hdbl : ∃ a ∈ S, n = 2 * a
      · rw [if_pos hdbl]
        have h1R : (1 : ℝ) ≤ (sumRep A n : ℝ) := by exact_mod_cast h1
        have h5R : (sumRep A n : ℝ) ≤ 5 := by exact_mod_cast h5
        nlinarith only [h1R, h5R]
      · rw [if_neg hdbl]
        have hnotA : ¬ ∃ a ∈ A, n = 2 * a := by
          rintro ⟨a, ha, rfl⟩
          exact hdbl ⟨a, mem_filter.mpr ⟨Finset.mem_Iic.mpr (by omega), ha⟩, rfl⟩
        obtain ⟨t, ht⟩ := sumRep_even_of_not_double A n hnotA
        have hcases : sumRep A n = 2 ∨ sumRep A n = 4 := by omega
        rcases hcases with h2 | h4
        · rw [h2]; norm_num
        · rw [h4]; norm_num
    have hsum2 := Finset.sum_le_sum hpt2
    have hexp2 : ∑ n ∈ Finset.Icc N1 N,
        (1 + 3 * (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0)) * (r ^ 2) ^ n =
        ∑ n ∈ Finset.Icc N1 N, (r ^ 2) ^ n +
        3 * ∑ n ∈ Finset.Icc N1 N, (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0) * (r ^ 2) ^ n := by
      simp_rw [add_mul, one_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hexp2] at hsum2
    have hg_le : ∑ n ∈ Finset.Icc N1 N, (r ^ 2) ^ n ≤ D := by
      calc ∑ n ∈ Finset.Icc N1 N, (r ^ 2) ^ n
          ≤ ∑ n ∈ Finset.range (N + 1), (r ^ 2) ^ n := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn; exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
            · intro _ _ _; positivity
        _ ≤ D := by
            have hg := geom_sum_mul (r ^ 2) (N + 1)
            rw [hD_eq, le_div_iff₀ hr2_pos]
            have hpow_nn : 0 ≤ (r ^ 2) ^ (N + 1) := by positivity
            linarith only [hg, hpow_nn]
    have hsum_dbl2 : ∑ n ∈ Finset.Icc N1 N,
        (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0) * (r ^ 2) ^ n ≤ Y := by
      have hrew : (∑ n ∈ Finset.Icc N1 N, (if ∃ a ∈ S, n = 2 * a then (1 : ℝ) else 0) * (r ^ 2) ^ n) =
          ∑ n ∈ (Finset.Icc N1 N).filter (fun n => ∃ a ∈ S, n = 2 * a), (r ^ 2) ^ n := by
        rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro n _; split_ifs <;> simp
      rw [hrew]
      have hsub_img : (Finset.Icc N1 N).filter (fun n => ∃ a ∈ S, n = 2 * a) ⊆ S.image (2 * ·) := by
        intro n hn
        obtain ⟨a, ha, rfl⟩ := (mem_filter.mp hn).2
        exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      calc ∑ n ∈ (Finset.Icc N1 N).filter (fun n => ∃ a ∈ S, n = 2 * a), (r ^ 2) ^ n
          ≤ ∑ n ∈ S.image (2 * ·), (r ^ 2) ^ n :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_img fun _ _ _ => by positivity
        _ = ∑ a ∈ S, (r ^ 2) ^ (2 * a) := by
            rw [Finset.sum_image (fun a _ b _ h => by omega)]
        _ = Y := by
            dsimp only [Y]; apply Finset.sum_congr rfl; intro a _; rw [← pow_mul]; ring_nf
    linarith only [hsum2, hg_le, hsum_dbl2]
  have hpart3 : ∑ n ∈ Finset.Icc (N + 1) (2 * N), cD n ^ 2 ≤ 1 := by
    have hcard3 : (Finset.Icc (N + 1) (2 * N)).card = N := by
      rw [Nat.card_Icc]; omega
    calc ∑ n ∈ Finset.Icc (N + 1) (2 * N), cD n ^ 2
        ≤ ∑ _n ∈ Finset.Icc (N + 1) (2 * N), 25 * r ^ (2 * N) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 : N + 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hnotle : ¬ n ≤ N := by omega
          dsimp only [cD]
          rw [if_neg hnotle, mul_pow, ← pow_mul, show n * 2 = 2 * n by ring]
          have hsr : sumRep (S : Set ℕ) n ≤ 5 :=
            (sumRep_monotone (fun x hx => (mem_filter.mp hx).2) n).trans (hle5 n (by omega))
          have hsr2 : (sumRep (S : Set ℕ) n : ℝ) ^ 2 ≤ 25 := by
            have hle5R : (sumRep (S : Set ℕ) n : ℝ) ≤ 5 := by exact_mod_cast hsr
            have hnn_sr : (0 : ℝ) ≤ (sumRep (S : Set ℕ) n : ℝ) := Nat.cast_nonneg _
            nlinarith only [hle5R, hnn_sr]
          have hrpow : r ^ (2 * n) ≤ r ^ (2 * N) :=
            pow_le_pow_of_le_one (by linarith only [hr_ge]) hr_lt1.le (by omega)
          have hnn : 0 ≤ r ^ (2 * n) := pow_nonneg (by linarith only [hr_ge]) _
          nlinarith only [hsr2, hrpow, hnn]
      _ = 25 * (N : ℝ) * r ^ (2 * N) := by
          rw [Finset.sum_const, hcard3, nsmul_eq_mul]; ring
      _ ≤ 1 := h25N
  have hC1_le : (N1 : ℝ) * ((N1 : ℝ) + 4) ^ 2 ≤ (1 / 100 : ℝ) * D := by
    have hnat : 100 * (N1 * (N1 + 4) ^ 2) ≤ 100 * (N1 + 4) ^ 3 + 40 * N1 + 10000 := by nlinarith
    have hR : 100 * ((N1 : ℝ) * ((N1 : ℝ) + 4) ^ 2) ≤ (100 * (N1 + 4) ^ 3 + 40 * N1 + 10000 : ℝ) := by
      exact_mod_cast hnat
    linarith only [hR, hD_big]
  linarith only [hpart1, hpart2, hpart3, hC1_le, hY_le, hD10000]

lemma six_frequently_of_cofinite (A : Set ℕ) (hA : (A + A)ᶜ.Finite) :
    ∀ K0 : ℕ, ∃ n ≥ K0, 6 ≤ sumRep A n := by
  by_contra hneg
  push Not at hneg
  obtain ⟨K0, hK0⟩ := hneg
  let N1 : ℕ := max K0 (hA.toFinset.sup id + 1)
  have hge1 : ∀ n ≥ N1, 1 ≤ sumRep A n := by
    intro n hn
    rw [sumRep_pos_iff]
    by_contra hnot
    have hmem : n ∈ hA.toFinset := hA.mem_toFinset.mpr hnot
    have hle : n ≤ hA.toFinset.sup id := Finset.le_sup (f := id) hmem
    have : hA.toFinset.sup id + 1 ≤ N1 := le_max_right _ _
    omega
  have hle5 : ∀ n ≥ N1, sumRep A n ≤ 5 := fun n hn =>
    Nat.lt_succ_iff.mp (hK0 n ((le_max_left _ _).trans hn))
  obtain ⟨m, hm40, hm_big⟩ : ∃ m : ℕ, 40 ≤ m ∧ 100 * (N1 + 4) ^ 3 + 40 * N1 + 10000 ≤ m :=
    ⟨max 40 (100 * (N1 + 4) ^ 3 + 40 * N1 + 10000), le_max_left _ _, le_max_right _ _⟩
  let T : ℕ := 2 ^ m
  have h2m1_ge_m : m ≤ 2 ^ (m - 1) := nat_le_pow_two_pred m (by omega)
  have hT_eq : T = 2 * 2 ^ (m - 1) := by
    dsimp only [T]
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    ring
  have hT40 : 40 * N1 ≤ T := by omega
  have hT10 : 10 ≤ T := by omega
  let N : ℕ := T ^ 2
  have hN_ge_N1 : N1 ≤ N := by
    have : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) T
    omega
  let K : ℕ := 2 * N + 1
  have hK2 : 2 ≤ K := by dsimp only [K, N]; nlinarith only [hT10]
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  let r : ℝ := 1 - (1 : ℝ) / (T : ℝ)
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hr_ge : (1 : ℝ) / 4 ≤ r := by
    dsimp only [r]
    have hT4 : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast (show 4 ≤ T by omega)
    have hinv : (1 : ℝ) / (T : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hT4
    linarith only [hinv]
  have hr_lt1 : r < 1 := by
    dsimp only [r]
    linarith [div_pos one_pos hTpos]
  let D : ℝ := 1 / (1 - r ^ 2)
  have hD_ge : ((2 ^ (m - 1) : ℕ) : ℝ) ≤ D := by
    dsimp only [D, r]
    have h1mr2 : 1 - (1 - 1 / (T : ℝ)) ^ 2 = (2 * (T : ℝ) - 1) / (T : ℝ) ^ 2 := by
      field_simp [hTpos.ne']; ring
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast (show 1 ≤ T by omega)
    rw [h1mr2, one_div_div, le_div_iff₀ (by linarith only [hT1])]
    have hTeqR : (T : ℝ) = 2 * ((2 ^ (m - 1) : ℕ) : ℝ) := by exact_mod_cast hT_eq
    nlinarith only [hTeqR, hTpos]
  have hD_big : (100 * (N1 + 4) ^ 3 + 40 * N1 + 10000 : ℝ) ≤ D := by
    have h1 : (100 * (N1 + 4) ^ 3 + 40 * N1 + 10000 : ℝ) ≤ ((2 ^ (m - 1) : ℕ) : ℝ) := by
      exact_mod_cast (hm_big.trans h2m1_ge_m)
    linarith only [h1, hD_ge]
  have hD_pos : 0 < D := by
    have hnn : (0 : ℝ) < 100 * ((N1 : ℝ) + 4) ^ 3 + 40 * (N1 : ℝ) + 10000 := by positivity
    linarith only [hnn, hD_big]
  let S : Finset ℕ := (Finset.Iic N).filter (· ∈ A)
  have hSsub : S ⊆ Finset.Iic N := Finset.filter_subset _ _
  let X : ℝ := ∑ a ∈ S, r ^ (2 * a)
  have hY_le : ∑ a ∈ S, r ^ (4 * a) ≤ (3 / 100 : ℝ) * D :=
    six_step_Y_bound A N1 N r D hN_ge_N1 hle5 hr_ge hr_lt1 rfl hD_big
  have hr2N : r ^ (2 * N) ≤ 1 / ((2 ^ (2 * T) : ℕ) : ℝ) := by
    have hhalf := one_sub_inv_pow_le_half T (by omega)
    have hpow : (r ^ T) ^ (2 * T) ≤ ((1 : ℝ) / 2) ^ (2 * T) :=
      pow_le_pow_left₀ (by positivity) hhalf (2 * T)
    have h2N_eq : 2 * N = T * (2 * T) := by dsimp only [N]; ring
    rw [h2N_eq, pow_mul]
    calc (r ^ T) ^ (2 * T) ≤ ((1 : ℝ) / 2) ^ (2 * T) := hpow
      _ = 1 / ((2 ^ (2 * T) : ℕ) : ℝ) := by rw [one_div_pow]; push_cast; rfl
  have h25N : 25 * (N : ℝ) * r ^ (2 * N) ≤ 1 := by
    have h25 := twentyfive_sq_le_pow_two T hT10
    have h25R : (25 : ℝ) * (N : ℝ) ≤ ((2 ^ (2 * T) : ℕ) : ℝ) := by
      dsimp only [N]; exact_mod_cast h25
    have hpos2T : (0 : ℝ) < ((2 ^ (2 * T) : ℕ) : ℝ) := by positivity
    calc 25 * (N : ℝ) * r ^ (2 * N)
        ≤ 25 * (N : ℝ) * (1 / ((2 ^ (2 * T) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hr2N (by positivity)
      _ ≤ ((2 ^ (2 * T) : ℕ) : ℝ) * (1 / ((2 ^ (2 * T) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right h25R (by positivity)
      _ = 1 := by field_simp [hpos2T.ne']
  have hX_lb : (13 / 10 : ℝ) * Real.sqrt D ≤ X :=
    six_step_X_lower A N1 N T r D hN_ge_N1 hT10 hT40 hge1 rfl hr_ge hr_lt1 rfl hD_pos hr2N hY_le
  -- Step 4: Discrete Fourier comparison on K = 2*N + 1 roots of unity
  let ζ : Fin K → ℂ := fun j => Complex.exp ((2 * Real.pi * (j.val : ℝ) / (K : ℝ) : ℝ) * Complex.I)
  let P : Fin K → ℂ := fun j => ∑ a ∈ S, ((r : ℂ) * ζ j) ^ a
  let Q : Fin K → ℂ := fun j => ∑ n ∈ Finset.range (N + 1), (3 : ℂ) * ((r : ℂ) * ζ j) ^ n
  have hζ_pow : ∀ (j : Fin K) (n : ℕ),
      ζ j ^ n = Complex.exp ((2 * Real.pi * (j.val : ℝ) * (n : ℝ) / (K : ℝ) : ℝ) * Complex.I) := by
    intro j n
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  -- Parseval on P: (1/K) * sum ||P(j)||^2 = X
  have hParseval_P : ∑ j : Fin K, ‖P j‖ ^ 2 = (K : ℝ) * X := by
    let cP : ℕ → ℝ := fun n => if n ∈ S then r ^ n else 0
    have hP_eq : ∀ j : Fin K, P j = ∑ n ∈ Finset.range (2 * N + 1),
        (cP n : ℂ) * Complex.exp ((2 * Real.pi * (j.val : ℝ) * (n : ℝ) / (K : ℝ) : ℝ) * Complex.I) := by
      intro j
      dsimp only [P, cP]
      have h1 : ∑ n ∈ Finset.range (2 * N + 1),
          ((if n ∈ S then r ^ n else 0 : ℝ) : ℂ) *
            Complex.exp ((2 * Real.pi * (j.val : ℝ) * (n : ℝ) / (K : ℝ) : ℝ) * Complex.I) =
          ∑ n ∈ (Finset.range (2 * N + 1)).filter (· ∈ S), ((r : ℂ) * ζ j) ^ n := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n _
        split_ifs with hn
        · rw [mul_pow, ← hζ_pow j n]; push_cast; rfl
        · simp
      rw [h1]
      congr 1
      ext n
      simp only [mem_filter, Finset.mem_range]
      constructor
      · intro hn; exact ⟨by have := Finset.mem_Iic.mp (hSsub hn); omega, hn⟩
      · exact fun h => h.2
    simp_rw [hP_eq]
    rw [dft_parseval (K := K) (M := 2 * N) (by dsimp only [K]; omega) cP]
    congr 1
    dsimp only [cP, X]
    have h1 : ∑ n ∈ Finset.range (2 * N + 1), (if n ∈ S then r ^ n else 0) ^ 2 =
        ∑ n ∈ (Finset.range (2 * N + 1)).filter (· ∈ S), r ^ (2 * n) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs
      · rw [← pow_mul]; ring_nf
      · simp
    rw [h1]
    congr 1
    ext n
    simp only [mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hn; exact ⟨by have := Finset.mem_Iic.mp (hSsub hn); omega, hn⟩
  -- Parseval on P^2 - Q: (1/K) * sum ||P(j)^2 - Q(j)||^2 <= (121/100) * D
  have hParseval_diff : ∑ j : Fin K, ‖P j ^ 2 - Q j‖ ^ 2 ≤ (K : ℝ) * ((121 / 100 : ℝ) * D) :=
    six_step_parseval_diff A N1 N r D hN_ge_N1 hge1 hle5 hr_ge hr_lt1 rfl hD_big hY_le h25N
  -- L1 bound on Q: (1/K) * sum ||Q(j)|| < (1/10) * sqrt D
  have hQ_L1 : ∑ j : Fin K, ‖Q j‖ < (K : ℝ) * ((1 / 10 : ℝ) * Real.sqrt D) := by
    have hQ_eq : ∀ j : Fin K, ‖Q j‖ =
        3 * ‖∑ n ∈ Finset.range (N + 1),
          ((r : ℂ) * Complex.exp ((2 * Real.pi * (j.val : ℝ) / (K : ℝ) : ℝ) * Complex.I)) ^ n‖ := by
      intro j
      dsimp only [Q, ζ]
      rw [← Finset.mul_sum, norm_mul]
      norm_num
    simp_rw [hQ_eq, ← Finset.mul_sum]
    have hgb := geom_poly_L1_bound (N := N) hK2 hr_ge hr_lt1
    have hK_le : K ≤ 2 ^ (2 * m + 2) := by
      dsimp only [K, N, T]
      have hsq : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul]; ring_nf
      rw [hsq]
      have hpow : 2 ^ (2 * m + 2) = 4 * 2 ^ (2 * m) := by rw [pow_add]; norm_num; ring
      have hpos : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
      omega
    have hharm : ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ) ≤ (2 * m + 3 : ℝ) := by
      calc ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ)
          ≤ ∑ j ∈ Finset.Icc (1 : ℕ) (2 ^ (2 * m + 2)), (1 : ℝ) / (j : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
            · intro _ _ _; positivity
        _ ≤ ((2 * m + 2 : ℕ) : ℝ) + 1 := harmonic_pow_two_le (2 * m + 2)
        _ = (2 * m + 3 : ℝ) := by push_cast; ring
    have h1mr : 1 / (1 - r) = (T : ℝ) := by
      dsimp only [r]; field_simp [hTpos.ne']; ring
    have hT_div_K : (T : ℝ) ≤ (K : ℝ) := by
      dsimp only [K, N]; exact_mod_cast (show T ≤ 2 * T ^ 2 + 1 by nlinarith)
    have htot : 3 * (1 / (1 - r) + 2 * (K : ℝ) * ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ)) ≤
        (K : ℝ) * (12 * (m : ℝ) + 21) := by
      rw [h1mr]
      nlinarith only [hT_div_K, hharm, hKpos]
    have hquad := quad_le_pow_two_40 m hm40
    have hquadR : 10000 * (12 * (m : ℝ) + 20) ^ 2 ≤ (T : ℝ) := by
      dsimp only [T]; exact_mod_cast hquad
    have hTeq2 : (T : ℝ) ≤ 2 * D := by
      have : (T : ℝ) = 2 * ((2 ^ (m - 1) : ℕ) : ℝ) := by exact_mod_cast hT_eq
      linarith
    have hsmall : (12 * (m : ℝ) + 21) < (1 / 10 : ℝ) * Real.sqrt D := by
      have hsq : (12 * (m : ℝ) + 21) ^ 2 < ((1 / 10 : ℝ) * Real.sqrt D) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hD_pos.le]
        have hmR : (40 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm40
        nlinarith only [hquadR, hTeq2, hmR]
      nlinarith [Real.sqrt_nonneg D, hsq]
    have hmul_lt : (K : ℝ) * (12 * (m : ℝ) + 21) < (K : ℝ) * ((1 / 10 : ℝ) * Real.sqrt D) :=
      mul_lt_mul_of_pos_left hsmall hKpos
    linarith only [hgb, htot, hmul_lt]
  -- Combine via triangle inequality and Cauchy-Schwarz
  have htri : ∑ j : Fin K, ‖P j‖ ^ 2 ≤ (∑ j : Fin K, ‖P j ^ 2 - Q j‖) + ∑ j : Fin K, ‖Q j‖ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have h1 : ‖P j‖ ^ 2 = ‖P j ^ 2‖ := (norm_pow (P j) 2).symm
    rw [h1]
    calc ‖P j ^ 2‖ = ‖(P j ^ 2 - Q j) + Q j‖ := by ring_nf
      _ ≤ ‖P j ^ 2 - Q j‖ + ‖Q j‖ := norm_add_le _ _
  have hCS : (∑ j : Fin K, ‖P j ^ 2 - Q j‖) ≤ (K : ℝ) * ((11 / 10 : ℝ) * Real.sqrt D) := by
    have hcs_sq : (∑ j : Fin K, ‖P j ^ 2 - Q j‖) ^ 2 ≤
        (K : ℝ) * ∑ j : Fin K, ‖P j ^ 2 - Q j‖ ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin K))
        (fun _ => (1 : ℝ)) (fun j => ‖P j ^ 2 - Q j‖)
      simp only [one_mul, one_pow, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one] at h
      exact h
    have hsq_le : (∑ j : Fin K, ‖P j ^ 2 - Q j‖) ^ 2 ≤
        ((K : ℝ) * ((11 / 10 : ℝ) * Real.sqrt D)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hD_pos.le]
      nlinarith only [hcs_sq, hParseval_diff, hKpos]
    have hnn : 0 ≤ ∑ j : Fin K, ‖P j ^ 2 - Q j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hB_nn : 0 ≤ (K : ℝ) * ((11 / 10 : ℝ) * Real.sqrt D) := by positivity
    nlinarith only [hsq_le, hnn, hB_nn]
  have hKX_lb : (K : ℝ) * ((13 / 10 : ℝ) * Real.sqrt D) ≤ (K : ℝ) * X :=
    mul_le_mul_of_nonneg_left hX_lb hKpos.le
  rw [hParseval_P] at htri
  have hsqrtD_pos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD_pos
  nlinarith only [hKX_lb, htri, hCS, hQ_L1, hKpos, hsqrtD_pos]

/- ### Part 5: Counting-function sandwich, additive energy, and aperiodicity -/

lemma counting_sandwich {B : Set ℕ} {M : ℕ}
    (hcov : ∀ n, 1 ≤ sumRep B n) (hcap : ∀ n, sumRep B n ≤ M) (N : ℕ) :
    N + 1 ≤ ((Finset.Iic N).filter (· ∈ B)).card ^ 2 ∧
      ((Finset.Iic N).filter (· ∈ B)).card ^ 2 ≤ M * (2 * N + 1) := by
  let S : Finset ℕ := (Finset.Iic N).filter (· ∈ B)
  have hSsub : S ⊆ Finset.Iic N := Finset.filter_subset _ _
  have hsum_all : ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n = S.card ^ 2 := by
    have hR := poly_sq_real_coeff S N hSsub 1
    simp only [one_pow, mul_one, Finset.sum_const, nsmul_eq_mul] at hR
    exact_mod_cast hR.symm
  constructor
  · have h1 : N + 1 ≤ ∑ n ∈ Finset.range (N + 1), sumRep (S : Set ℕ) n := by
      calc N + 1 = ∑ _n ∈ Finset.range (N + 1), 1 := by simp
        _ ≤ ∑ n ∈ Finset.range (N + 1), sumRep (S : Set ℕ) n := by
            apply Finset.sum_le_sum
            intro n hn
            have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
            rw [sumRep_filter_eq hnN]
            exact hcov n
    have h2 : ∑ n ∈ Finset.range (N + 1), sumRep (S : Set ℕ) n ≤
        ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    change N + 1 ≤ S.card ^ 2
    omega
  · have h1 : ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n ≤ M * (2 * N + 1) := by
      calc ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n
          ≤ ∑ _n ∈ Finset.range (2 * N + 1), M := by
            apply Finset.sum_le_sum
            intro n _
            exact (sumRep_monotone (fun x hx => (mem_filter.mp hx).2) n).trans (hcap n)
        _ = M * (2 * N + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
    change S.card ^ 2 ≤ M * (2 * N + 1)
    omega

lemma energy_bound_of_cap {B : Set ℕ} {M : ℕ} (hcap : ∀ n, sumRep B n ≤ M)
    (N : ℕ) (S : Finset ℕ) (hSN : S ⊆ Finset.Iic N) (hSB : (S : Set ℕ) ⊆ B) :
    ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n ^ 2 ≤ M * S.card ^ 2 := by
  have hsum_all : ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n = S.card ^ 2 := by
    have hR := poly_sq_real_coeff S N hSN 1
    simp only [one_pow, mul_one, Finset.sum_const, nsmul_eq_mul] at hR
    exact_mod_cast hR.symm
  calc ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n ^ 2
      ≤ ∑ n ∈ Finset.range (2 * N + 1), M * sumRep (S : Set ℕ) n := by
        apply Finset.sum_le_sum
        intro n _
        have hle : sumRep (S : Set ℕ) n ≤ M := (sumRep_monotone hSB n).trans (hcap n)
        rw [sq]
        exact Nat.mul_le_mul_right _ hle
    _ = M * ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n := (Finset.mul_sum _ _ _).symm
    _ = M * S.card ^ 2 := by rw [hsum_all]

lemma no_infinite_ap_of_cap {B : Set ℕ} {M : ℕ} (hcap : ∀ n, sumRep B n ≤ M) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ B := by
  rintro ⟨a, d, hd, hAP⟩
  have hge : M + 1 ≤ sumRep B (2 * a + M * d) := by
    rw [sumRep_def]
    let f : ℕ → ℕ × ℕ := fun k => (a + k * d, a + (M - k) * d)
    have hcard_range : (Finset.range (M + 1)).card = M + 1 := Finset.card_range (M + 1)
    rw [← hcard_range]
    apply Finset.card_le_card_of_injOn f
    · intro k hk
      have hkM : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      refine mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr ?_, hAP k, hAP (M - k)⟩
      dsimp only [f]
      have hmul : k * d + (M - k) * d = M * d := by
        rw [← Nat.add_mul, Nat.add_sub_of_le hkM]
      omega
    · intro k1 _ k2 _ hEq
      have h1 : a + k1 * d = a + k2 * d := congrArg Prod.fst hEq
      have h2 : k1 * d = k2 * d := by omega
      exact Nat.eq_of_mul_eq_mul_right hd h2
  have hle := hcap (2 * a + M * d)
  omega

/- ### Reduction hypotheses H1 and H2 -/

/-- Thin-prefix regime: no exact additive basis `B ⊆ ℕ` with bounded ordered representations
`1 ≤ sumRep B n ≤ M` (`6 ≤ M`), infinitely many `sumRep B n ≥ 6`, counting sandwich
`N + 1 ≤ B(N)^2 ≤ M * (2 * N + 1)`, additive-energy bound `E(S) ≤ M * |S|^2`, and no
infinite arithmetic progression can have thin prefixes `B(N)^2 < 4 * N` infinitely often. -/
def H1 : Prop :=
  ∀ (B : Set ℕ) (M : ℕ), 6 ≤ M → (0 : ℕ) ∈ B →
    (∀ n, 1 ≤ sumRep B n ∧ sumRep B n ≤ M) →
    (∀ K, ∃ n ≥ K, 6 ≤ sumRep B n) →
    (∀ N, N + 1 ≤ ((Finset.Iic N).filter (· ∈ B)).card ^ 2 ∧
      ((Finset.Iic N).filter (· ∈ B)).card ^ 2 ≤ M * (2 * N + 1)) →
    (∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Iic N → (S : Set ℕ) ⊆ B →
      ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n ^ 2 ≤ M * S.card ^ 2) →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ B) →
    (∀ K, ∃ N ≥ K, ((Finset.Iic N).filter (· ∈ B)).card ^ 2 < 4 * N) →
    False

/-- Uniformly dense regime: the same impossibility for exact bounded-cap bases satisfying
all proved invariants and having uniformly dense prefixes `4 * N ≤ B(N)^2` eventually. -/
def H2 : Prop :=
  ∀ (B : Set ℕ) (M : ℕ), 6 ≤ M → (0 : ℕ) ∈ B →
    (∀ n, 1 ≤ sumRep B n ∧ sumRep B n ≤ M) →
    (∀ K, ∃ n ≥ K, 6 ≤ sumRep B n) →
    (∀ N, N + 1 ≤ ((Finset.Iic N).filter (· ∈ B)).card ^ 2 ∧
      ((Finset.Iic N).filter (· ∈ B)).card ^ 2 ≤ M * (2 * N + 1)) →
    (∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Iic N → (S : Set ℕ) ⊆ B →
      ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n ^ 2 ≤ M * S.card ^ 2) →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ B) →
    (∀ᶠ N : ℕ in atTop, 4 * N ≤ ((Finset.Iic N).filter (· ∈ B)).card ^ 2) →
    False

theorem main : H1 → H2 → type_of% @Erdos28.erdos_28 := by
  intro h1 h2 A hA
  by_contra hnotTop
  have hltTop : limsup (fun n : ℕ => (sumRep A n : ℕ∞)) atTop < ⊤ :=
    lt_top_iff_ne_top.mpr hnotTop
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℕ, limsup (fun n : ℕ => (sumRep A n : ℕ∞)) atTop < (m0 : ℕ∞) := by
    cases hval : limsup (fun n : ℕ => (sumRep A n : ℕ∞)) atTop with
    | top => exact (hnotTop hval).elim
    | coe k => exact ⟨k + 1, by exact_mod_cast Nat.lt_succ_self k⟩
  have hev : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℕ∞) < (m0 : ℕ∞) :=
    eventually_lt_of_limsup_lt hm0 ⟨⊤, Eventually.of_forall fun _ => le_top⟩
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N0, hN0⟩ := hev
  let M0 : ℕ := max m0 ((Finset.range N0).sup (sumRep A))
  have hcapA : ∀ n : ℕ, sumRep A n ≤ M0 := by
    intro n
    by_cases hn : n < N0
    · exact (Finset.le_sup (f := sumRep A) (Finset.mem_range.mpr hn)).trans (le_max_right _ _)
    · have hlt := hN0 n (Nat.le_of_not_lt hn)
      have hltN : sumRep A n < m0 := by exact_mod_cast hlt
      exact hltN.le.trans (le_max_left _ _)
  let F : Finset ℕ := insert 0 hA.toFinset
  let B : Set ℕ := (F : Set ℕ) ∪ A
  have h0B : (0 : ℕ) ∈ B := Or.inl (by simp [F])
  have hcovB : ∀ n : ℕ, 1 ≤ sumRep B n := by
    intro n
    rw [sumRep_pos_iff]
    by_cases hn : n ∈ A + A
    · obtain ⟨a, ha, b, hb, hab⟩ := hn
      exact ⟨a, Or.inr ha, b, Or.inr hb, hab⟩
    · have hnF : n ∈ F := Finset.mem_insert_of_mem (hA.mem_toFinset.mpr hn)
      exact ⟨0, h0B, n, Or.inl hnF, Nat.zero_add n⟩
  let M : ℕ := M0 + 2 * F.card
  have hcapB : ∀ n : ℕ, sumRep B n ≤ M := fun n =>
    (sumRep_union_finset_le A F n).trans (Nat.add_le_add_right (hcapA n) _)
  have hsixA : ∀ K, ∃ n ≥ K, 6 ≤ sumRep A n := six_frequently_of_cofinite A hA
  have hsixB : ∀ K, ∃ n ≥ K, 6 ≤ sumRep B n := fun K => by
    obtain ⟨n, hnK, h6⟩ := hsixA K
    exact ⟨n, hnK, h6.trans (sumRep_monotone Set.subset_union_right n)⟩
  have hM6 : 6 ≤ M := by
    obtain ⟨n, _, h6⟩ := hsixB 0
    exact h6.trans (hcapB n)
  have hsand : ∀ N, N + 1 ≤ ((Finset.Iic N).filter (· ∈ B)).card ^ 2 ∧
      ((Finset.Iic N).filter (· ∈ B)).card ^ 2 ≤ M * (2 * N + 1) :=
    fun N => by convert counting_sandwich hcovB hcapB N
  have henergy : ∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Iic N → (S : Set ℕ) ⊆ B →
      ∑ n ∈ Finset.range (2 * N + 1), sumRep (S : Set ℕ) n ^ 2 ≤ M * S.card ^ 2 :=
    fun N S hSN hSB => energy_bound_of_cap hcapB N S hSN hSB
  have hnoAP : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ B :=
    no_infinite_ap_of_cap hcapB
  by_cases hthin : ∀ K, ∃ N ≥ K, ((Finset.Iic N).filter (· ∈ B)).card ^ 2 < 4 * N
  · exact h1 B M hM6 h0B (fun n => ⟨hcovB n, hcapB n⟩) hsixB (fun N => by convert hsand N)
      henergy hnoAP (by convert hthin)
  · push Not at hthin
    obtain ⟨K, hK⟩ := hthin
    have hdense : ∀ᶠ N : ℕ in atTop, 4 * N ≤ ((Finset.Iic N).filter (· ∈ B)).card ^ 2 :=
      Filter.eventually_atTop.mpr ⟨K, hK⟩
    exact h2 B M hM6 h0B (fun n => ⟨hcovB n, hcapB n⟩) hsixB (fun N => by convert hsand N)
      henergy hnoAP (by convert hdense)

end OMA.R_Erdos28_erdos_28_R2
