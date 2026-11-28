import FormalConjectures.ErdosProblems.«542»
import Mathlib.Algebra.GCDMonoid.Nat

-- Credit: @mrnato255
-- The finite base-case lemmas are from R1 by @ivillar.

/-! A first-counterexample reduction with prime-class compression and canonical-hole packing. -/

open scoped BigOperators

namespace OMA.R_Erdos542_erdos_542_variants_only_two_R2

/-- The branch with a denominator at most the square root. -/
def H1 : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ), 12 ≤ n → Erdos542.IsLcmFree n A → n ∈ A →
    (∃ a ∈ A, a * a ≤ n) → (∑ a ∈ A, (1 : ℝ) / a) ≤ 1

/-- The all-large branch after compressing each isolated proper prime class
whose quotient is outside the two exceptional thresholds. -/
def H2 : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ), 12 ≤ n → Erdos542.IsLcmFree n A → n ∈ A →
    (∀ a ∈ A, n < a * a) →
    (∀ p : ℕ, p.Prime → p ∣ n → p < n →
      n = p * 5 ∨ n = p * 11 ∨ ∃ a ∈ A, ¬ p ∣ a ∧ a * p ≤ n) →
    ∀ U : ℕ → Finset ℕ,
      (∀ k m : ℕ, m ∈ U k ↔ 0 < m ∧ m ≤ k ∧ ∀ d : ℕ, d ∣ m → 1 < d → d * d.minFac ≤ k) →
      (∑ a ∈ A ∩ U n, (U (n / a)).card) ≤ (U n).card →
    (∑ a ∈ A, (1 : ℝ) / a) ≤ 1

/-- Kernel computation over the `2 ^ 11` subsets of `{1, …, 11}`. -/
lemma small_dec : ∀ A ∈ (Finset.Icc 1 11).powerset, 27720 < ∑ a ∈ A, 27720 / a →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ c ∈ A, c < Nat.lcm a b) →
    A = {2, 3, 5} ∨ A = {3, 4, 5, 7, 11} := by
  decide +kernel

lemma dvd_27720 : ∀ a ∈ Finset.Icc 1 11, a ∣ 27720 := by
  decide

/-- The conjecture for `n ≤ 11`. -/
lemma small {n : ℕ} {A : Finset ℕ} (hn : n ≤ 11) (hA : Erdos542.IsLcmFree n A)
    (hsum : 1 < ∑ a ∈ A, (1 : ℝ) / a) : A = {2, 3, 5} ∨ A = {3, 4, 5, 7, 11} := by
  have hsub : A ⊆ Finset.Icc 1 11 := fun a ha => by
    have := Finset.mem_Icc.mp (hA.1 ha)
    exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
  have hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ c ∈ A, c < Nat.lcm a b := by
    intro a ha b hb hab c hc
    have h1 : n < Nat.lcm a b := hA.2 ha hb hab
    have h2 := (Finset.mem_Icc.mp (hA.1 hc)).2
    omega
  have hnat : 27720 < ∑ a ∈ A, 27720 / a := by
    have hterm : ∀ a ∈ A, ((27720 / a : ℕ) : ℝ) = 27720 * ((1 : ℝ) / a) := by
      intro a ha
      have hd := dvd_27720 a (hsub ha)
      have ha0 : (a : ℝ) ≠ 0 := by
        have := (Finset.mem_Icc.mp (hsub ha)).1
        exact_mod_cast (by omega : a ≠ 0)
      rw [Nat.cast_div hd ha0]
      push_cast
      ring
    have hcast : ((∑ a ∈ A, 27720 / a : ℕ) : ℝ) = 27720 * ∑ a ∈ A, (1 : ℝ) / a := by
      rw [Nat.cast_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl hterm
    have hr : (27720 : ℝ) < ((∑ a ∈ A, 27720 / a : ℕ) : ℝ) := by
      rw [hcast]
      linarith
    exact_mod_cast hr
  exact small_dec A (Finset.mem_powerset.mpr hsub) hnat hpair

/-- Restrict to multiples of m and divide out m. Each denominator that
meets this progression gives one projected denominator. -/
theorem project_to_multiples (n m : ℕ) (A : Finset ℕ)
    (hm : 0 < m) (positive : ∀ a ∈ A, 0 < a)
    (separated : (A : Set ℕ).Pairwise fun a b ↦ n < Nat.lcm a b) :
    ∃ B : Finset ℕ, (∀ b ∈ B, 0 < b ∧ b ≤ n / m) ∧
      ((B : Set ℕ).Pairwise fun b c ↦ n / m < Nat.lcm b c) ∧
      (∑ b ∈ B, (1 : ℝ) / b) =
        (m : ℝ) * ∑ a ∈ A.filter (fun a ↦ Nat.lcm a m ≤ n), (1 : ℝ) / Nat.lcm a m := by
  let s := A.filter (fun a ↦ Nat.lcm a m ≤ n)
  let f (a : ℕ) := Nat.lcm a m / m
  have mul_f (a : ℕ) : m * f a = Nat.lcm a m :=
    Nat.mul_div_cancel' (Nat.dvd_lcm_right a m)
  have dvd_f (a : ℕ) : a ∣ m * f a := by
    rw [mul_f]
    exact Nat.dvd_lcm_left a m
  have pos_f {a : ℕ} (ha : a ∈ s) : 0 < f a := by
    apply Nat.pos_of_ne_zero
    intro h
    have hl := mul_f a
    rw [h, mul_zero] at hl
    exact Nat.lcm_ne_zero (positive a (Finset.mem_filter.mp ha).1).ne' hm.ne' hl.symm
  have le_f {a : ℕ} (ha : a ∈ s) : f a ≤ n / m := by
    apply (Nat.le_div_iff_mul_le hm).2
    rw [Nat.mul_comm, mul_f]
    exact (Finset.mem_filter.mp ha).2
  have separate_f {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
      n / m < Nat.lcm (f a) (f b) := by
    apply Nat.lt_of_not_ge
    intro h
    have upper : m * Nat.lcm (f a) (f b) ≤ n := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).1 h
    have dividing : Nat.lcm a b ∣ m * Nat.lcm (f a) (f b) := Nat.lcm_dvd
      ((dvd_f a).trans (Nat.mul_dvd_mul_left m (Nat.dvd_lcm_left _ _)))
      ((dvd_f b).trans (Nat.mul_dvd_mul_left m (Nat.dvd_lcm_right _ _)))
    have hpos := Nat.mul_pos hm (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (pos_f ha).ne' (pos_f hb).ne'))
    exact (not_lt_of_ge ((Nat.le_of_dvd hpos dividing).trans upper))
      (separated (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab)
  refine ⟨s.image f, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨pos_f ha, le_f ha⟩
  · intro b hb c hc hbc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hc
    exact separate_f ha ha' (fun h ↦ hbc (congrArg f h))
  · rw [Finset.sum_image, Finset.mul_sum]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [← mul_f a]
      push_cast
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have ha' : (f a : ℝ) ≠ 0 := by exact_mod_cast (pos_f ha).ne'
      field_simp
    · intro a ha b hb h
      by_contra hab
      have hlt := separate_f ha hb hab
      rw [← h, Nat.lcm_self] at hlt
      exact (not_lt_of_ge (le_f ha)) hlt

/-- If `a` does not contain `p`, any common multiple with a denominator
that contains `p` must be divisible by `a * p`. -/
theorem lcm_gt_of_prime_factor {n a b p : ℕ} (prime : p.Prime) (apos : 0 < a)
    (bpos : 0 < b) (apart : ¬ p ∣ a) (factor : p ∣ b) (large : n < a * p) :
    n < Nat.lcm a b := by
  have coprime : Nat.Coprime a p := (prime.coprime_iff_not_dvd.mpr apart).symm
  have divides : a * p ∣ Nat.lcm a b := coprime.mul_dvd_of_dvd_of_dvd
    (Nat.dvd_lcm_left a b) (factor.trans (Nat.dvd_lcm_right a b))
  have positive := Nat.pos_of_ne_zero (Nat.lcm_ne_zero apos.ne' bpos.ne')
  exact large.trans_le (Nat.le_of_dvd positive divides)

/-- A prime above the square-root threshold separates its multiples
from all the other large denominators. -/
theorem independent_large_prime_class {n a b p : ℕ} (prime : p.Prime)
    (largePrime : n < p * p) (largeDenom : n < a * a) (bpos : 0 < b)
    (apart : ¬ p ∣ a) (factor : p ∣ b) : n < Nat.lcm a b := by
  have apos : 0 < a := by
    by_contra! h
    have : a = 0 := by omega
    simp [this] at largeDenom
  have product : n < a * p := by
    rcases le_total a p with h | h
    · exact largeDenom.trans_le (Nat.mul_le_mul_left a h)
    · exact largePrime.trans_le (Nat.mul_le_mul_right p h)
  exact lcm_gt_of_prime_factor prime apos bpos apart factor product

/-- A composite threshold divisible by an isolated prime can be removed
without reducing weight if its prime class has weight at most `1/p`. -/
theorem compress_large_prime_class {n p : ℕ} (A : Finset ℕ) (prime : p.Prime)
    (plt : p < n) (dividesThreshold : p ∣ n)
    (bounds : ∀ a ∈ A, 0 < a ∧ a ≤ n)
    (separated : (A : Set ℕ).Pairwise fun a b ↦ n < Nat.lcm a b)
    (independent : ∀ a ∈ A, ¬ p ∣ a → n < a * p)
    (classBound : (∑ a ∈ A.filter (fun a ↦ p ∣ a), (1 : ℝ) / a) ≤ (1 : ℝ) / p) :
    ∃ C : Finset ℕ, (∀ a ∈ C, 0 < a ∧ a < n) ∧
      ((C : Set ℕ).Pairwise fun a b ↦ n < Nat.lcm a b) ∧
      (∑ a ∈ A, (1 : ℝ) / a) ≤ ∑ a ∈ C, (1 : ℝ) / a := by
  classical
  let keep := A.filter fun a ↦ ¬ p ∣ a
  have keep_mem {a : ℕ} (ha : a ∈ keep) : a ∈ A ∧ ¬ p ∣ a := Finset.mem_filter.mp ha
  have cross {a : ℕ} (ha : a ∈ keep) : n < Nat.lcm a p :=
    lcm_gt_of_prime_factor prime (bounds a (keep_mem ha).1).1 prime.pos (keep_mem ha).2
      (dvd_refl p) (independent a (keep_mem ha).1 (keep_mem ha).2)
  refine ⟨insert p keep, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | kept
    · exact ⟨prime.pos, plt⟩
    · obtain ⟨mem, apart⟩ := keep_mem kept
      refine ⟨(bounds a mem).1, lt_of_le_of_ne (bounds a mem).2 ?_⟩
      exact fun eq ↦ apart (eq.symm ▸ dividesThreshold)
  · intro a ha b hb different
    change a ∈ insert p keep at ha
    change b ∈ insert p keep at hb
    rcases Finset.mem_insert.mp ha with rfl | keptA
    · rcases Finset.mem_insert.mp hb with rfl | keptB
      · exact (different rfl).elim
      · simpa only [Nat.lcm_comm] using cross keptB
    · rcases Finset.mem_insert.mp hb with rfl | keptB
      · exact cross keptA
      · exact separated (keep_mem keptA).1 (keep_mem keptB).1 different
  · have notKeep : p ∉ keep := by simp [keep]
    rw [Finset.sum_insert notKeep, ← Finset.sum_filter_add_sum_filter_not A (fun a ↦ p ∣ a)]
    exact add_le_add classBound le_rfl

theorem canonicalHole_mul_of_local {n a k : ℕ} (ha : 0 < a)
    (holeA : (∀ d : ℕ, d ∣ a → 1 < d → d * d.minFac ≤ n)) (holeK : (∀ d : ℕ, d ∣ k → 1 < d → d * d.minFac ≤ (n / a))) :
    (∀ d : ℕ, d ∣ (a * k) → 1 < d → d * d.minFac ≤ n) := by
  intro d hd hlt
  obtain ⟨u, v, hua, hvk, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  have hu := Nat.le_of_dvd ha hua
  rcases lt_or_ge 1 v with hv | hv
  · have hmin : (u * v).minFac ≤ v.minFac :=
      Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : v ≠ 1)).two_le
        ((Nat.minFac_dvd v).trans (dvd_mul_left v u))
    calc
      (u * v) * (u * v).minFac ≤ (u * v) * v.minFac := Nat.mul_le_mul_left _ hmin
      _ = u * (v * v.minFac) := Nat.mul_assoc ..
      _ ≤ a * (n / a) := Nat.mul_le_mul hu (holeK v hvk hv)
      _ ≤ n := Nat.mul_div_le n a
  · have vpos : 0 < v := by
      apply Nat.pos_of_ne_zero
      intro eq
      simp [eq] at hlt
    have eq : v = 1 := by omega
    simpa [eq] using holeA u hua (by simpa [eq] using hlt)

theorem sum_canonicalHoles_card_le {n : ℕ} (A : Finset ℕ) (U : ℕ → Finset ℕ)
    (memU : (∀ k m : ℕ, m ∈ U k ↔ 0 < m ∧ m ≤ k ∧ ∀ d : ℕ, d ∣ m → 1 < d → d * d.minFac ≤ k))
    (inside : ∀ a ∈ A, a ∈ U n)
    (separated : (A : Set ℕ).Pairwise fun a b ↦ n < Nat.lcm a b) :
    ∑ a ∈ A, (U (n / a)).card ≤ (U n).card := by
  classical
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun x : Σ _ : ℕ, ℕ ↦ x.1 * x.2)
  · intro x hx
    obtain ⟨hxA, hxK⟩ := Finset.mem_sigma.mp hx
    have ha := (memU _ _).mp (inside x.1 hxA)
    have hk := (memU _ _).mp hxK
    apply (memU _ _).mpr
    refine ⟨Nat.mul_pos ha.1 hk.1, ?_,
      canonicalHole_mul_of_local ha.1 ha.2.2 hk.2.2⟩
    exact (Nat.mul_le_mul_left _ hk.2.1).trans (Nat.mul_div_le n x.1)
  · intro x hx y hy eq
    change x.1 * x.2 = y.1 * y.2 at eq
    obtain ⟨hxA, hxK⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hyA, _⟩ := Finset.mem_sigma.mp hy
    have ha := (memU _ _).mp (inside x.1 hxA)
    have hk := (memU _ _).mp hxK
    have common : Nat.lcm x.1 y.1 ∣ x.1 * x.2 := by
      apply Nat.lcm_dvd (dvd_mul_right _ _)
      rw [eq]
      exact dvd_mul_right _ _
    have he : x.1 = y.1 := by
      by_contra different
      exact not_lt_of_ge
        ((Nat.le_of_dvd (Nat.mul_pos ha.1 hk.1) common).trans
          ((Nat.mul_le_mul_left _ hk.2.1).trans (Nat.mul_div_le n _)))
        (separated hxA hyA different)
    obtain ⟨a, k⟩ := x
    obtain ⟨b, j⟩ := y
    change a = b at he
    subst b
    have equal : k = j := Nat.eq_of_mul_eq_mul_left ha.1 eq
    subst j
    rfl

lemma exceptional_bounds {n : ℕ} {B : Finset ℕ}
    (sep : (B : Set ℕ).Pairwise fun a b ↦ n < Nat.lcm a b)
    (e : B = {2, 3, 5} ∨ B = {3, 4, 5, 7, 11}) :
    (n < 6 ∧ 5 ∈ B) ∨ (n < 12 ∧ 11 ∈ B) := by
  rcases e with eq | eq
  · subst B
    have h := sep (show 2 ∈ ({2,3,5} : Finset ℕ) by decide)
      (show 3 ∈ ({2,3,5} : Finset ℕ) by decide) (by decide : 2 ≠ 3)
    exact Or.inl ⟨h, by decide⟩
  · subst B
    have h := sep (show 3 ∈ ({3,4,5,7,11} : Finset ℕ) by decide)
      (show 4 ∈ ({3,4,5,7,11} : Finset ℕ) by decide) (by decide : 3 ≠ 4)
    exact Or.inr ⟨h, by decide⟩

theorem main : H1 → H2 → type_of% @Erdos542.erdos_542.variants.only_two := by
  classical
  intro h1 h2 n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hA hsum
    by_cases smallN : n ≤ 11
    · exact small smallN hA hsum
    have hn : 12 ≤ n := by omega
    have pos {a : ℕ} (ha : a ∈ A) : 0 < a := (Finset.mem_Icc.mp (hA.1 ha)).1
    have upper {a : ℕ} (ha : a ∈ A) : a ≤ n := (Finset.mem_Icc.mp (hA.1 ha)).2
    have descend (B : Finset ℕ) (bounds : ∀ a ∈ B, 0 < a ∧ a < n)
        (sep : (B : Set ℕ).Pairwise fun a b ↦ n < Nat.lcm a b)
        (gt : 1 < ∑ b ∈ B, (1 : ℝ) / b) : False := by
      have free : Erdos542.IsLcmFree (n-1) B := by
        refine ⟨?_, fun _ ha _ hb ne => (Nat.sub_le n 1).trans_lt (sep ha hb ne)⟩
        intro a ha
        obtain ⟨ap, al⟩ := bounds a ha
        exact Finset.mem_Icc.mpr ⟨ap, by omega⟩
      have e := exceptional_bounds sep (ih (n-1) (by omega) B free gt)
      rcases e with h | h <;> omega
    have endpt : n ∈ A := by
      by_contra outside
      exact descend A (fun a ha => ⟨pos ha, lt_of_le_of_ne (upper ha)
        (fun e => outside (e ▸ ha))⟩) hA.2 hsum
    by_cases hasSmall : ∃ a ∈ A, a * a ≤ n
    · exact (not_lt_of_ge (h1 n A hn hA endpt hasSmall) hsum).elim
    have allLarge : ∀ a ∈ A, n < a * a := fun a ha =>
      Nat.lt_of_not_ge (fun le => hasSmall ⟨a, ha, le⟩)
    have endpointRestriction : ∀ p : ℕ, p.Prime → p ∣ n → p < n →
        n = p * 5 ∨ n = p * 11 ∨ ∃ a ∈ A, ¬ p ∣ a ∧ a * p ≤ n := by
      intro p prime dvd plt
      by_contra! contra
      obtain ⟨five, eleven, independent⟩ := contra
      have divide : p * (n / p) = n := Nat.mul_div_cancel' dvd
      have divlt : n / p < n := Nat.div_lt_self (by omega) prime.one_lt
      let C := A.filter (fun a => p ∣ a)
      obtain ⟨B, boundsB, sepB, sumB⟩ := project_to_multiples n p C prime.pos
        (fun a ha => pos (Finset.mem_filter.mp ha).1)
        (fun _ ha _ hb ne => hA.2 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 ne)
      have localFree : Erdos542.IsLcmFree (n / p) B :=
        ⟨fun a ha => Finset.mem_Icc.mpr (boundsB a ha), sepB⟩
      have localBound : (∑ b ∈ B, (1 : ℝ) / b) ≤ 1 := by
        by_contra! gt
        rcases exceptional_bounds sepB (ih (n/p) divlt B localFree gt) with ⟨lt, mem⟩ | ⟨lt, mem⟩
        · have eq : n / p = 5 := by have := (boundsB 5 mem).2; omega
          exact five (by simpa only [eq] using divide.symm)
        · have eq : n / p = 11 := by have := (boundsB 11 mem).2; omega
          exact eleven (by simpa only [eq] using divide.symm)
      have filterAll : C.filter (fun a => Nat.lcm a p ≤ n) = C := by
        apply Finset.filter_eq_self.mpr
        intro a ha
        obtain ⟨hmem, hdvd⟩ := Finset.mem_filter.mp ha
        rw [Nat.lcm_comm, Nat.lcm_eq_right hdvd]
        exact upper hmem
      rw [filterAll] at sumB
      have eq : (∑ a ∈ C, (1 : ℝ) / Nat.lcm a p) = ∑ a ∈ C, (1 : ℝ) / a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Nat.lcm_comm, Nat.lcm_eq_right (Finset.mem_filter.mp ha).2]
      rw [eq] at sumB
      have pR : (0 : ℝ) < p := by exact_mod_cast prime.pos
      have classBound : (∑ a ∈ C, (1 : ℝ) / a) ≤ (1 : ℝ) / p := by
        apply (le_div_iff₀ pR).mpr
        rw [mul_comm, ← sumB]
        exact localBound
      obtain ⟨T, boundsT, sepT, sumT⟩ := compress_large_prime_class A prime plt dvd
        (fun _ ha => ⟨pos ha, upper ha⟩) hA.2 independent classBound
      exact descend T boundsT sepT (hsum.trans_le sumT)
    let U (k : ℕ) := (Finset.Icc 1 k).filter
      (fun m => ∀ d : ℕ, d ∣ m → 1 < d → d * d.minFac ≤ k)
    have memU : (∀ k m : ℕ, m ∈ U k ↔ 0 < m ∧ m ≤ k ∧ ∀ d : ℕ, d ∣ m → 1 < d → d * d.minFac ≤ k) := by
      intro k m
      simp only [U, Finset.mem_filter, Finset.mem_Icc, and_assoc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
    have packed : (∑ a ∈ A ∩ U n, (U (n / a)).card) ≤ (U n).card :=
      sum_canonicalHoles_card_le (A ∩ U n) U memU
        (fun _ ha => (Finset.mem_inter.mp ha).2)
        (fun _ ha _ hb ne => hA.2 (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1 ne)
    exact (not_lt_of_ge (h2 n A hn hA endpt allLarge endpointRestriction U memU packed) hsum).elim

end OMA.R_Erdos542_erdos_542_variants_only_two_R2
