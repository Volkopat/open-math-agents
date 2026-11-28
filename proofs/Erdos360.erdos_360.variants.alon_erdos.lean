import FormalConjectures.ErdosProblems.«360»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Additive.SubsetSum
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Proof of `Erdos360.erdos_360.variants.alon_erdos`

We formalize the two-sided asymptotic bound
`n^(1/3) / (log n)^(4/3) ≪ f(n) ≪ n^(1/3) / (log n)^(1/3) * (log log n)^(1/3)`
for Erdős Problem 360.
-/

-- Problem: Erdős Problem 360 — alon erdos
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/360.lean:77 (declaration Erdos360.erdos_360.variants.alon_erdos)
-- Credit: @Andyi955 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics Finset Real
open scoped Nat.Prime

namespace Erdos360AlonErdos

/- Section 1: Partition and covering characterizations of `Erdos360.f` -/

lemma f_le_of_cover {n : ℕ} (ℱ : Finset (Finset ℕ))
    (hcov : Finset.Icc 1 (n - 1) ⊆ ℱ.biUnion id)
    (hfree : ∀ A ∈ ℱ, n ∉ subsetSums (A : Set ℕ)) :
    Erdos360.f n ≤ ℱ.card := by
  classical
  let pick : ℕ → Finset ℕ := fun x ↦
    if h : ∃ A ∈ ℱ, x ∈ A then Classical.choose h else ∅
  have hpick : ∀ x ∈ Finset.Icc 1 (n - 1), pick x ∈ ℱ ∧ x ∈ pick x := by
    intro x hx
    have hmem : ∃ A ∈ ℱ, x ∈ A := by
      have := hcov hx
      simpa [Finset.mem_biUnion] using this
    simpa [pick, hmem] using Classical.choose_spec hmem
  let cls : Finset ℕ → Finset ℕ := fun A ↦
    (Finset.Icc 1 (n - 1)).filter (fun x ↦ pick x = A)
  have hcls_sub : ∀ A ∈ ℱ, cls A ⊆ A := by
    intro A _ x hx
    simp only [cls, Finset.mem_filter] at hx
    have := (hpick x hx.1).2
    rwa [hx.2] at this
  let parts : Finset (Finset ℕ) := (ℱ.image cls).filter Finset.Nonempty
  have hsupIndep : parts.SupIndep id := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro B₁ hB₁ B₂ hB₂ hne
    rw [Finset.mem_coe] at hB₁ hB₂
    simp only [parts, Finset.mem_filter, Finset.mem_image] at hB₁ hB₂
    rcases hB₁.1 with ⟨A₁, _, rfl⟩
    rcases hB₂.1 with ⟨A₂, _, rfl⟩
    have hAne : A₁ ≠ A₂ := fun h ↦ hne (congrArg cls h)
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx₁ hx₂
    have hx₁' : pick x = A₁ := (Finset.mem_filter.mp hx₁).2
    have hx₂' : pick x = A₂ := (Finset.mem_filter.mp hx₂).2
    exact hAne (hx₁'.symm.trans hx₂')
  have hsup : parts.sup id = Finset.Icc 1 (n - 1) := by
    ext x
    simp only [Finset.mem_sup, id_eq, parts, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨B, ⟨⟨A, _, rfl⟩, _⟩, hxB⟩
      exact (Finset.mem_filter.mp hxB).1
    · intro hx
      refine ⟨cls (pick x), ⟨⟨pick x, (hpick x hx).1, rfl⟩, ⟨x, ?_⟩⟩, ?_⟩ <;>
        simp [cls, hx]
  have hbot : ⊥ ∉ parts := by
    simp [parts]
  let P : Finpartition (Finset.Icc 1 (n - 1)) := ⟨parts, hsupIndep, hsup, hbot⟩
  have hPfree : ∀ B ∈ P.parts, n ∉ subsetSums (B : Set ℕ) := by
    intro B hB
    simp only [P, parts, Finset.mem_filter, Finset.mem_image] at hB
    rcases hB.1 with ⟨A, hA, rfl⟩
    intro hn
    exact hfree A hA (subsetSums_mono (Finset.coe_subset.mpr (hcls_sub A hA)) hn)
  have hmem : P.parts.card ∈ {r : ℕ | ∃ Q : Finpartition (Finset.Icc 1 (n - 1)),
      Q.parts.card = r ∧ ∀ A ∈ Q.parts, n ∉ subsetSums (A : Set ℕ)} :=
    ⟨P, rfl, hPfree⟩
  calc Erdos360.f n ≤ P.parts.card := Nat.sInf_le hmem
    _ ≤ (ℱ.image cls).card := Finset.card_filter_le _ _
    _ ≤ ℱ.card := Finset.card_image_le

lemma f_set_nonempty {n : ℕ} (hn : 2 ≤ n) :
    {r : ℕ | ∃ P : Finpartition (Finset.Icc 1 (n - 1)),
      P.parts.card = r ∧ ∀ A ∈ P.parts, n ∉ subsetSums (A : Set ℕ)}.Nonempty := by
  let parts : Finset (Finset ℕ) := (Finset.Icc 1 (n - 1)).image (fun x ↦ {x})
  have hsupIndep : parts.SupIndep id := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hne
    rw [Finset.mem_coe] at hA hB
    simp only [parts, Finset.mem_image] at hA hB
    rcases hA with ⟨x, _, rfl⟩
    rcases hB with ⟨y, _, rfl⟩
    have hxy : x ≠ y := fun h ↦ hne (congrArg (fun z ↦ ({z} : Finset ℕ)) h)
    simp [Function.onFun, hxy]
  have hsup : parts.sup id = Finset.Icc 1 (n - 1) := by
    ext x
    simp only [Finset.mem_sup, id_eq, parts, Finset.mem_image]
    constructor
    · rintro ⟨A, ⟨y, hy, rfl⟩, hxA⟩
      simp only [Finset.mem_singleton] at hxA
      rwa [hxA]
    · intro hx
      exact ⟨{x}, ⟨x, hx, rfl⟩, Finset.mem_singleton_self x⟩
  have hbot : ⊥ ∉ parts := by
    simp [parts]
  let P : Finpartition (Finset.Icc 1 (n - 1)) := ⟨parts, hsupIndep, hsup, hbot⟩
  refine ⟨P.parts.card, P, rfl, ?_⟩
  intro A hA
  simp only [P, parts, Finset.mem_image] at hA
  rcases hA with ⟨x, hx, rfl⟩
  rintro ⟨B, hB, hsum⟩
  have hBsub : B ⊆ {x} := fun y hy ↦ by simpa using hB hy
  rcases Finset.subset_singleton_iff.mp hBsub with rfl | rfl
  · simp at hsum; omega
  · simp only [Finset.sum_singleton] at hsum
    simp only [Finset.mem_Icc] at hx
    omega

lemma le_f_of_forall_partition {n R : ℕ} (hn : 2 ≤ n)
    (h : ∀ P : Finpartition (Finset.Icc 1 (n - 1)),
      (∀ A ∈ P.parts, n ∉ subsetSums (A : Set ℕ)) → R ≤ P.parts.card) :
    R ≤ Erdos360.f n := by
  refine le_csInf (f_set_nonempty hn) ?_
  rintro r ⟨P, rfl, hfree⟩
  exact h P hfree

/- Section 2: Sum-free classes for the upper bound -/

def intervalClass (n k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n - 1)).filter (fun x ↦ n < (k + 1) * x ∧ k * x ≤ n)

lemma intervalClass_sum_free {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    n ∉ subsetSums (intervalClass n k : Set ℕ) := by
  rintro ⟨B, hB, hsum⟩
  have hBmem : ∀ x ∈ B, 1 ≤ x ∧ x ≤ n - 1 ∧ n < (k + 1) * x ∧ k * x ≤ n := by
    intro x hx
    have := hB hx
    simp only [Finset.mem_coe, intervalClass, Finset.mem_filter, Finset.mem_Icc] at this
    exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩
  by_cases hbig : k + 1 ≤ B.card
  · have h1 : (k + 1) * n = ∑ x ∈ B, (k + 1) * x := by
      rw [← Finset.mul_sum, ← hsum]
    have h2 : B.card * (n + 1) ≤ ∑ x ∈ B, (k + 1) * x := by
      calc B.card * (n + 1) = ∑ _x ∈ B, (n + 1) := by simp
        _ ≤ ∑ x ∈ B, (k + 1) * x := Finset.sum_le_sum fun x hx ↦ (hBmem x hx).2.2.1
    have h3 : (k + 1) * (n + 1) ≤ B.card * (n + 1) := Nat.mul_le_mul_right _ hbig
    nlinarith
  · push Not at hbig
    have hle : B.card ≤ k := Nat.lt_succ_iff.mp hbig
    rcases Nat.lt_trichotomy B.card 1 with h0 | h1 | h2
    · have : B = ∅ := Finset.card_eq_zero.mp (by omega)
      subst this; simp at hsum; omega
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
      simp only [Finset.sum_singleton] at hsum
      have := (hBmem x (Finset.mem_singleton_self x)).2.1
      omega
    · have hmul : k * n = ∑ x ∈ B, k * x := by
        rw [← Finset.mul_sum, ← hsum]
      obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := Finset.one_lt_card.mp h2
      have hex : ∃ x ∈ B, k * x < n := by
        by_contra hall
        push Not at hall
        have heq₁ : k * x₁ = n := le_antisymm (hBmem x₁ hx₁).2.2.2 (hall x₁ hx₁)
        have heq₂ : k * x₂ = n := le_antisymm (hBmem x₂ hx₂).2.2.2 (hall x₂ hx₂)
        exact hne (Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) (heq₁.trans heq₂.symm))
      obtain ⟨x₀, hx₀, hlt₀⟩ := hex
      have hstrict : ∑ x ∈ B, k * x < ∑ _x ∈ B, n :=
        Finset.sum_lt_sum (fun x hx ↦ (hBmem x hx).2.2.2) ⟨x₀, hx₀, hlt₀⟩
      simp only [Finset.sum_const, smul_eq_mul] at hstrict
      have : B.card * n ≤ k * n := Nat.mul_le_mul_right _ hle
      omega

def multClass (n d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n - 1)).filter (fun x ↦ d ∣ x)

lemma multClass_sum_free {n d : ℕ} (hd : ¬ d ∣ n) :
    n ∉ subsetSums (multClass n d : Set ℕ) := by
  rintro ⟨B, hB, hsum⟩
  apply hd
  rw [hsum]
  exact Finset.dvd_sum fun x hx ↦ by
    have := hB hx
    simp only [Finset.mem_coe, multClass, Finset.mem_filter] at this
    exact this.2

lemma small_sum_free {n : ℕ} {B : Finset ℕ} (hB : ∑ x ∈ B, x < n) :
    n ∉ subsetSums (B : Set ℕ) := by
  rintro ⟨C, hC, hsum⟩
  have hCsub : C ⊆ B := fun x hx ↦ by simpa using hC hx
  have hle : ∑ x ∈ C, x ≤ ∑ x ∈ B, x := Finset.sum_le_sum_of_subset (f := id) hCsub
  omega

lemma greedy_pack {n : ℕ} (hn : 2 ≤ n) (U : Finset ℕ) (hU : ∀ x ∈ U, 1 ≤ x ∧ 2 * x ≤ n) :
    ∃ ℬ : Finset (Finset ℕ),
      U ⊆ ℬ.biUnion id ∧
      (∀ B ∈ ℬ, ∑ x ∈ B, x < n) ∧
      n * ℬ.card ≤ 2 * (∑ x ∈ U, x) + n := by
  classical
  induction hcard : U.card using Nat.strong_induction_on generalizing U with
  | _ c ih =>
    by_cases hsum : ∑ x ∈ U, x < n
    · refine ⟨{U}, ?_, ?_, ?_⟩
      · intro x hx; simp [hx]
      · intro B hB; simp only [Finset.mem_singleton] at hB; subst hB; exact hsum
      · simp
    · push Not at hsum
      let valid := U.powerset.filter (fun B ↦ ∑ x ∈ B, x < n)
      have hvalid_ne : valid.Nonempty := ⟨∅, by simp [valid]; omega⟩
      obtain ⟨B, hBmem, hBmax⟩ := Finset.exists_max_image valid (fun B ↦ ∑ x ∈ B, x) hvalid_ne
      simp only [valid, Finset.mem_filter, Finset.mem_powerset] at hBmem
      have hBsub : B ⊆ U := hBmem.1
      have hBsum : ∑ x ∈ B, x < n := hBmem.2
      have hsdiff_ne : (U \ B).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
        have hEq : B = U := Finset.Subset.antisymm hBsub hemp
        subst hEq; omega
      obtain ⟨y, hy⟩ := hsdiff_ne
      have hyU : y ∈ U := (Finset.mem_sdiff.mp hy).1
      have hyB : y ∉ B := (Finset.mem_sdiff.mp hy).2
      have hBy_ge : n ≤ y + ∑ x ∈ B, x := by
        by_contra hlt
        push Not at hlt
        have hmem_ins : insert y B ∈ valid := by
          simp only [valid, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.insert_subset_iff.mpr ⟨hyU, hBsub⟩, by rw [Finset.sum_insert hyB]; exact hlt⟩
        have hle := hBmax (insert y B) hmem_ins
        rw [Finset.sum_insert hyB] at hle
        have := (hU y hyU).1
        omega
      have hB_half : n ≤ 2 * ∑ x ∈ B, x := by
        have := (hU y hyU).2
        omega
      have hB_ne : B.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        subst hemp; simp at hB_half; omega
      have hlt_card : (U \ B).card < c := by
        have h1 : (U \ B).card + B.card = U.card := Finset.card_sdiff_add_card_eq_card hBsub
        have h2 : 0 < B.card := Finset.card_pos.mpr hB_ne
        omega
      have hU' : ∀ x ∈ U \ B, 1 ≤ x ∧ 2 * x ≤ n := fun x hx ↦ hU x (Finset.mem_sdiff.mp hx).1
      obtain ⟨ℬ', hcov', hfree', hcard'⟩ := ih (U \ B).card hlt_card (U \ B) hU' rfl
      refine ⟨insert B ℬ', ?_, ?_, ?_⟩
      · intro x hx
        by_cases hxB : x ∈ B
        · exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_insert_self B ℬ', hxB⟩
        · have := hcov' (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
          rcases Finset.mem_biUnion.mp this with ⟨C, hC, hxC⟩
          exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_insert_of_mem hC, hxC⟩
      · intro C hC
        rcases Finset.mem_insert.mp hC with rfl | hC'
        · exact hBsum
        · exact hfree' C hC'
      · have hsplit : ∑ x ∈ U \ B, x + ∑ x ∈ B, x = ∑ x ∈ U, x := Finset.sum_sdiff hBsub
        have hcard_ins : (insert B ℬ').card ≤ ℬ'.card + 1 := Finset.card_insert_le B ℬ'
        nlinarith

/- Section 3: Analytic number theory helpers for the upper bound -/

lemma prime_pow_div_dvd_factorial (L p : ℕ) (hp : p.Prime) : p ^ (L / p) ∣ L.factorial := by
  have hfact : L.factorial = ∏ k ∈ Finset.Icc 1 L, k := by
    induction L with
    | zero => simp
    | succ m ih =>
      rw [Nat.factorial_succ, ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), mul_comm]
  rw [hfact]
  let S := (Finset.Icc 1 (L / p)).image (fun j ↦ p * j)
  have hSsub : S ⊆ Finset.Icc 1 L := by
    intro x hx
    simp only [S, Finset.mem_image, Finset.mem_Icc] at hx ⊢
    rcases hx with ⟨j, ⟨hj1, hjle⟩, rfl⟩
    have hppos : 0 < p := hp.pos
    exact ⟨by nlinarith, (Nat.mul_le_mul_left p hjle).trans (Nat.mul_div_le L p)⟩
  have hdvd1 : ∏ x ∈ S, x ∣ ∏ k ∈ Finset.Icc 1 L, k :=
    Finset.prod_dvd_prod_of_subset S (Finset.Icc 1 L) id hSsub
  have hinj : Set.InjOn (fun j ↦ p * j) (Finset.Icc 1 (L / p) : Set ℕ) :=
    fun a _ b _ hab ↦ Nat.eq_of_mul_eq_mul_left hp.pos hab
  have hprodS : ∏ x ∈ S, x = p ^ (L / p) * ∏ j ∈ Finset.Icc 1 (L / p), j := by
    rw [Finset.prod_image hinj, Finset.prod_mul_distrib, Finset.prod_const]
    simp
  exact dvd_trans (hprodS ▸ dvd_mul_right _ _) hdvd1

lemma prod_prime_pow_dvd_of_forall {s : Finset ℕ} {f : ℕ → ℕ} {M : ℕ}
    (hs : ∀ p ∈ s, p.Prime) (hdvd : ∀ p ∈ s, p ^ f p ∣ M) :
    (∏ p ∈ s, p ^ f p) ∣ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s' hp ih =>
    rw [Finset.prod_insert hp]
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s')
    have hs' : ∀ q ∈ s', q.Prime := fun q hq ↦ hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime (p ^ f p) (∏ q ∈ s', q ^ f q) := by
      refine Nat.Coprime.prod_right fun q hq ↦ ?_
      have hpq : p ≠ q := fun h ↦ hp (h ▸ hq)
      exact ((Nat.coprime_primes hpp (hs' q hq)).mpr hpq).pow _ _
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd p (Finset.mem_insert_self p s'))
      (ih hs' (fun q hq ↦ hdvd q (Finset.mem_insert_of_mem hq)))

lemma sum_log_div_prime_le (L : ℕ) (hL : 2 ≤ L) :
    ∑ p ∈ Nat.primesLE L, Real.log p / p ≤ Real.log L + Real.log 4 := by
  have hprod_dvd : ∏ p ∈ Nat.primesLE L, p ^ (L / p) ∣ L.factorial :=
    prod_prime_pow_dvd_of_forall (fun p hp ↦ Nat.prime_of_mem_primesLE hp)
      (fun p hp ↦ prime_pow_div_dvd_factorial L p (Nat.prime_of_mem_primesLE hp))
  have hprod_le : (∏ p ∈ Nat.primesLE L, p ^ (L / p) : ℕ) ≤ L ^ L :=
    (Nat.le_of_dvd (Nat.factorial_pos L) hprod_dvd).trans (Nat.factorial_le_pow L)
  have hprod_pos : (0 : ℝ) < (∏ p ∈ Nat.primesLE L, p ^ (L / p) : ℕ) := by
    exact_mod_cast Finset.prod_pos fun p hp ↦ pow_pos (Nat.prime_of_mem_primesLE hp).pos _
  have hlog_le : Real.log ((∏ p ∈ Nat.primesLE L, p ^ (L / p) : ℕ) : ℝ) ≤
      Real.log ((L ^ L : ℕ) : ℝ) := Real.log_le_log hprod_pos (by exact_mod_cast hprod_le)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hlog_lhs : Real.log ((∏ p ∈ Nat.primesLE L, p ^ (L / p) : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE L, ((L / p : ℕ) : ℝ) * Real.log p := by
    push_cast
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl fun p _ ↦ by rw [Real.log_pow]
    · intro p hp
      exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero)
  have hlog_rhs : Real.log ((L ^ L : ℕ) : ℝ) = L * Real.log L := by
    push_cast; rw [Real.log_pow]
  rw [hlog_lhs, hlog_rhs] at hlog_le
  have hstep : ∑ p ∈ Nat.primesLE L, ((L : ℝ) / p - 1) * Real.log p ≤ L * Real.log L := by
    refine le_trans (Finset.sum_le_sum fun p hp ↦ ?_) hlog_le
    have hpp := Nat.prime_of_mem_primesLE hp
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    refine mul_le_mul_of_nonneg_right ?_ hlogp
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hdiv : L < (L / p + 1) * p := by
      have := Nat.div_add_mod L p
      have hmod := Nat.mod_lt L hpp.pos
      nlinarith
    have hdivR : (L : ℝ) < ((L / p : ℕ) + 1) * p := by exact_mod_cast hdiv
    rw [sub_le_iff_le_add, div_le_iff₀ hppos]
    linarith
  have htheta : ∑ p ∈ Nat.primesLE L, Real.log p ≤ Real.log 4 * L := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hsplit : ∑ p ∈ Nat.primesLE L, ((L : ℝ) / p - 1) * Real.log p =
      L * (∑ p ∈ Nat.primesLE L, Real.log p / p) - ∑ p ∈ Nat.primesLE L, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ by ring
  rw [hsplit] at hstep
  have hcomb : (L : ℝ) * (∑ p ∈ Nat.primesLE L, Real.log p / p) ≤ L * (Real.log L + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left hcomb hLpos

lemma sum_inv_prime_le (L : ℕ) (hL : 3 ≤ L) :
    ∑ p ∈ Nat.primesLE L, (1 : ℝ) / p ≤ Real.log (Real.log L) + 5 := by
  let S : ℕ → ℝ := fun t ↦ ∑ p ∈ Nat.primesLE t, Real.log p / p
  have htele : ∀ p ∈ Nat.primesLE L,
      (1 : ℝ) / Real.log p = 1 / Real.log L +
        ∑ t ∈ Finset.Ico p L, (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) := by
    intro p hp
    have hpL : p ≤ L := Nat.le_of_mem_primesLE hp
    clear hp
    induction hdiff : L - p generalizing p with
    | zero =>
      have hpEq : p = L := by omega
      subst hpEq
      simp
    | succ d ih =>
      have hpLt : p < L := by omega
      have hstep := ih (p + 1) (by omega) (by omega)
      rw [Finset.sum_eq_sum_Ico_succ_bot hpLt]
      linarith
  have hrewrite : ∑ p ∈ Nat.primesLE L, (1 : ℝ) / p =
      S L / Real.log L +
        ∑ t ∈ Finset.Ico 2 L, S t * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) := by
    have h1 : ∑ p ∈ Nat.primesLE L, (1 : ℝ) / p =
        ∑ p ∈ Nat.primesLE L, (Real.log p / p) * (1 / Real.log p) := by
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hlogp : Real.log p ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt))
      field_simp
    rw [h1]
    have h2 : ∑ p ∈ Nat.primesLE L, (Real.log p / p) * (1 / Real.log p) =
        ∑ p ∈ Nat.primesLE L, (Real.log p / p) * (1 / Real.log L) +
        ∑ p ∈ Nat.primesLE L, ∑ t ∈ Finset.Ico p L,
          (Real.log p / p) * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [htele p hp, mul_add, Finset.mul_sum]
    rw [h2]
    congr 1
    · rw [← Finset.sum_mul]; ring
    · have hswap :
          ∑ p ∈ Nat.primesLE L, ∑ t ∈ Finset.Ico p L,
            (Real.log p / p) * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) =
          ∑ t ∈ Finset.Ico 2 L, ∑ p ∈ Nat.primesLE t,
            (Real.log p / p) * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) := by
        have hIco : ∀ p ∈ Nat.primesLE L,
            Finset.Ico p L = (Finset.Ico 2 L).filter (fun t ↦ p ≤ t) := by
          intro p hp
          have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesLE hp).two_le
          ext t; simp only [Finset.mem_Ico, Finset.mem_filter]; omega
        calc ∑ p ∈ Nat.primesLE L, ∑ t ∈ Finset.Ico p L,
              (Real.log p / p) * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ))
          _ = ∑ p ∈ Nat.primesLE L, ∑ t ∈ (Finset.Ico 2 L).filter (fun t ↦ p ≤ t),
              (Real.log p / p) * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) := by
              refine Finset.sum_congr rfl fun p hp ↦ by rw [hIco p hp]
          _ = ∑ p ∈ Nat.primesLE L, ∑ t ∈ Finset.Ico 2 L,
              if p ≤ t then (Real.log p / p) * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) else 0 := by
              refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_filter _ _
          _ = ∑ t ∈ Finset.Ico 2 L, ∑ p ∈ Nat.primesLE L,
              if p ≤ t then (Real.log p / p) * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) else 0 :=
              Finset.sum_comm
          _ = ∑ t ∈ Finset.Ico 2 L, ∑ p ∈ Nat.primesLE t,
              (Real.log p / p) * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) := by
              refine Finset.sum_congr rfl fun t ht ↦ ?_
              rw [← Finset.sum_filter]
              refine Finset.sum_congr ?_ fun _ _ ↦ rfl
              ext p
              simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_Ico] at ht ⊢
              exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨by omega, h.2⟩, h.1⟩⟩
      rw [hswap]
      refine Finset.sum_congr rfl fun t _ ↦ by rw [← Finset.sum_mul]
  rw [hrewrite]
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hfirst : S L / Real.log L ≤ 1 + Real.log 4 / Real.log L := by
    have hSL := sum_log_div_prime_le L (by omega)
    calc S L / Real.log L ≤ (Real.log L + Real.log 4) / Real.log L :=
          div_le_div_of_nonneg_right hSL hlogL_pos.le
      _ = 1 + Real.log 4 / Real.log L := by field_simp
  have hsum_bound :
      ∑ t ∈ Finset.Ico 2 L, S t * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) ≤
      (Real.log (Real.log L) - Real.log (Real.log 2)) +
      Real.log 4 * (1 / Real.log 2 - 1 / Real.log L) := by
    have hstep_le : ∀ t ∈ Finset.Ico 2 L,
        S t * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) ≤
        (Real.log (Real.log (t + 1 : ℕ)) - Real.log (Real.log t)) +
        Real.log 4 * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) := by
      intro t ht
      simp only [Finset.mem_Ico] at ht
      have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
      have hlogt1 : 0 < Real.log (t + 1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < t + 1))
      have hlog_le : Real.log t ≤ Real.log (t + 1 : ℕ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < t)) (by exact_mod_cast (by omega : t ≤ t + 1))
      have hdiff_nn : 0 ≤ 1 / Real.log t - 1 / Real.log (t + 1 : ℕ) := by
        have := one_div_le_one_div_of_le hlogt hlog_le
        linarith
      have hSt := sum_log_div_prime_le t ht.1
      have h1 : S t * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) ≤
          Real.log t * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) +
          Real.log 4 * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) := by
        nlinarith
      have h2 : Real.log t * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) ≤
          Real.log (Real.log (t + 1 : ℕ)) - Real.log (Real.log t) := by
        have hxpos : 0 < Real.log (t + 1 : ℕ) / Real.log t := div_pos hlogt1 hlogt
        have hinv := Real.one_sub_inv_le_log_of_pos hxpos
        rw [inv_div, Real.log_div hlogt1.ne' hlogt.ne'] at hinv
        have heq : Real.log t * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) =
            1 - Real.log t / Real.log (t + 1 : ℕ) := by
          field_simp
        linarith
      linarith
    have htele1 : ∑ t ∈ Finset.Ico 2 L,
        (Real.log (Real.log (t + 1 : ℕ)) - Real.log (Real.log t)) =
        Real.log (Real.log L) - Real.log (Real.log 2) := by
      have h := Finset.sum_Ico_sub (f := fun t : ℕ ↦ Real.log (Real.log t)) (by omega : 2 ≤ L)
      simpa using h
    have htele2 : ∑ t ∈ Finset.Ico 2 L,
        (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) =
        1 / Real.log 2 - 1 / Real.log L := by
      have h := Finset.sum_Ico_sub (f := fun t : ℕ ↦ -(1 / Real.log t)) (by omega : 2 ≤ L)
      simp only [sub_neg_eq_add] at h
      have h' : ∑ t ∈ Finset.Ico 2 L, (1 / Real.log t - 1 / Real.log (t + 1 : ℕ)) =
          ∑ t ∈ Finset.Ico 2 L, (-(1 / Real.log (t + 1 : ℕ)) + 1 / Real.log t) := by
        refine Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [h', h]; ring
    calc ∑ t ∈ Finset.Ico 2 L, S t * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ))
      _ ≤ ∑ t ∈ Finset.Ico 2 L,
          ((Real.log (Real.log (t + 1 : ℕ)) - Real.log (Real.log t)) +
           Real.log 4 * (1 / Real.log t - 1 / Real.log (t + 1 : ℕ))) :=
          Finset.sum_le_sum hstep_le
      _ = (Real.log (Real.log L) - Real.log (Real.log 2)) +
          Real.log 4 * (1 / Real.log 2 - 1 / Real.log L) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, htele1, htele2]
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [this, Real.log_pow]; norm_num
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4_div : Real.log 4 * (1 / Real.log 2) = 2 := by
    rw [hlog4_eq]; field_simp
  have hlog_log2 : -Real.log (Real.log 2) ≤ 2 := by
    have hgt : Real.exp (-2) ≤ Real.log 2 := by
      have h1 : (1 / 2 : ℝ) < Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      have h2 : Real.exp (-2) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
        have : (1 : ℝ) + 2 ≤ Real.exp 2 := by
          have := Real.add_one_le_exp (2 : ℝ); linarith
        linarith
      linarith
    have := Real.log_le_log (Real.exp_pos (-2)) hgt
    rw [Real.log_exp] at this
    linarith
  have hcalc : (1 + Real.log 4 / Real.log L) +
      ((Real.log (Real.log L) - Real.log (Real.log 2)) +
       Real.log 4 * (1 / Real.log 2 - 1 / Real.log L)) =
      Real.log (Real.log L) + 3 - Real.log (Real.log 2) := by
    have : Real.log 4 * (1 / Real.log 2 - 1 / Real.log L) =
        2 - Real.log 4 / Real.log L := by
      rw [mul_sub, hlog4_div, mul_one_div]
    linarith
  linarith

lemma prod_inv_one_sub_prime_le (L : ℕ) (hL : 3 ≤ L) :
    ∏ p ∈ Nat.primesLE L, (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp 6 * Real.log L := by
  have hfactor : ∀ p ∈ Nat.primesLE L,
      (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp ((1 : ℝ) / p + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have heq : (1 - (1 : ℝ) / p)⁻¹ = 1 + ((1 : ℝ) / p + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [heq]
    linarith [Real.add_one_le_exp ((1 : ℝ) / p + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)))]
  have hnonneg : ∀ p ∈ Nat.primesLE L, 0 ≤ (1 - (1 : ℝ) / p)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have h1 : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    have : 0 < 1 - (1 : ℝ) / p := by linarith
    exact inv_nonneg.mpr this.le
  have hprod : ∏ p ∈ Nat.primesLE L, (1 - (1 : ℝ) / p)⁻¹ ≤
      Real.exp (∑ p ∈ Nat.primesLE L, (1 : ℝ) / p +
        ∑ p ∈ Nat.primesLE L, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by
    calc ∏ p ∈ Nat.primesLE L, (1 - (1 : ℝ) / p)⁻¹
      _ ≤ ∏ p ∈ Nat.primesLE L, Real.exp ((1 : ℝ) / p + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) :=
          Finset.prod_le_prod hnonneg hfactor
      _ = Real.exp (∑ p ∈ Nat.primesLE L, ((1 : ℝ) / p + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)))) :=
          (Real.exp_sum _ _).symm
      _ = Real.exp (∑ p ∈ Nat.primesLE L, (1 : ℝ) / p +
            ∑ p ∈ Nat.primesLE L, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by
          rw [Finset.sum_add_distrib]
  have htail : ∑ p ∈ Nat.primesLE L, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) ≤ 1 := by
    have hsub : Nat.primesLE L ⊆ Finset.Ico 2 (L + 1) := by
      intro p hp
      simp only [Finset.mem_Ico]
      exact ⟨(Nat.prime_of_mem_primesLE hp).two_le, Nat.lt_succ_of_le (Nat.le_of_mem_primesLE hp)⟩
    have hnn : ∀ k ∈ Finset.Ico 2 (L + 1), 0 ≤ 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
      intro k hk
      simp only [Finset.mem_Ico] at hk
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
      have := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < (k : ℝ) - 1) (by linarith : (k : ℝ) - 1 ≤ k)
      linarith
    calc ∑ p ∈ Nat.primesLE L, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))
      _ ≤ ∑ k ∈ Finset.Ico 2 (L + 1), (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ ↦ hnn k hk)
      _ = ∑ k ∈ Finset.Ico 1 L, (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_bij (fun k _ ↦ k - 1) ?_ ?_ ?_ ?_
          · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
          · intro k₁ hk₁ k₂ hk₂ heq; simp only [Finset.mem_Ico] at hk₁ hk₂; omega
          · intro j hj; refine ⟨j + 1, ?_, by omega⟩; simp only [Finset.mem_Ico] at hj ⊢; omega
          · intro k hk
            simp only [Finset.mem_Ico] at hk
            have hk1 : 1 ≤ k := by omega
            have h1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by simp [Nat.cast_sub hk1]
            have h2 : ((k - 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Nat.sub_add_cancel hk1
            rw [h1, h2]
      _ = 1 / (1 : ℝ) - 1 / (L : ℝ) := by
          have h := Finset.sum_Ico_sub (f := fun k : ℕ ↦ -(1 / (k : ℝ))) (by omega : 1 ≤ L)
          have h' : ∑ k ∈ Finset.Ico 1 L, (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) =
              ∑ k ∈ Finset.Ico 1 L, (-(1 / ((k + 1 : ℕ) : ℝ)) - -(1 / (k : ℝ))) := by
            refine Finset.sum_congr rfl fun _ _ ↦ by ring
          rw [h', h]; simp; ring
      _ ≤ 1 := by
          have : 0 ≤ 1 / (L : ℝ) := by positivity
          linarith
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  calc ∏ p ∈ Nat.primesLE L, (1 - (1 : ℝ) / p)⁻¹
    _ ≤ Real.exp (∑ p ∈ Nat.primesLE L, (1 : ℝ) / p +
          ∑ p ∈ Nat.primesLE L, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) := hprod
    _ ≤ Real.exp (Real.log (Real.log L) + 6) := by
        apply Real.exp_le_exp.mpr
        linarith [sum_inv_prime_le L hL]
    _ = Real.exp 6 * Real.log L := by
        rw [Real.exp_add, Real.exp_log hlogL_pos, mul_comm]

lemma log_gt_four_of_ge_64 {n : ℕ} (hn : 64 ≤ n) : 4 < Real.log n := by
  have h64 : (64 : ℝ) = 2 ^ (6 : ℕ) := by norm_num
  have h1 : Real.log 64 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [h64, Real.log_pow] at h1
  push_cast at h1
  linarith [Real.log_two_gt_d9]

lemma log_log_gt_one_of_ge_64 {n : ℕ} (hn : 64 ≤ n) : 1 < Real.log (Real.log n) := by
  have hlogn := log_gt_four_of_ge_64 hn
  have h1 : Real.log 4 ≤ Real.log (Real.log n) := Real.log_le_log (by norm_num) hlogn.le
  have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
  rw [h4, Real.log_pow] at h1
  push_cast at h1
  linarith [Real.log_two_gt_d9]

lemma prod_inv_one_sub_primeFactors_le (n : ℕ) (hn : 64 ≤ n) :
    ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp 8 * Real.log (Real.log n) := by
  have hlogn_gt4 : 4 < Real.log n := log_gt_four_of_ge_64 hn
  have hloglog_gt1 : 1 < Real.log (Real.log n) := log_log_gt_one_of_ge_64 hn
  let L : ℕ := ⌊Real.log n⌋₊
  have hL_ge4 : 4 ≤ L := Nat.le_floor (by norm_num; linarith)
  have hL_le : (L : ℝ) ≤ Real.log n := Nat.floor_le (by linarith)
  let S₁ := n.primeFactors.filter (fun p ↦ p ≤ L)
  let S₂ := n.primeFactors.filter (fun p ↦ ¬ p ≤ L)
  have hsplit : ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p)⁻¹ =
      (∏ p ∈ S₁, (1 - (1 : ℝ) / p)⁻¹) * (∏ p ∈ S₂, (1 - (1 : ℝ) / p)⁻¹) :=
    (Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p ↦ p ≤ L) _).symm
  rw [hsplit]
  have hge1 : ∀ p ∈ Nat.primesLE L, (1 : ℝ) ≤ (1 - (1 : ℝ) / p)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have h1 : 0 < 1 - (1 : ℝ) / p := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2; linarith
    have h2 : 1 - (1 : ℝ) / p ≤ 1 := by
      have : 0 ≤ (1 : ℝ) / p := by positivity
      linarith
    exact (one_le_inv₀ h1).mpr h2
  have hS₁_sub : S₁ ⊆ Nat.primesLE L := by
    intro p hp
    simp only [S₁, Finset.mem_filter] at hp
    exact Nat.mem_primesLE.mpr ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
  have hprod₁ : ∏ p ∈ S₁, (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp 6 * Real.log (Real.log n) := by
    have hprod_le : ∏ p ∈ S₁, (1 - (1 : ℝ) / p)⁻¹ ≤
        ∏ p ∈ Nat.primesLE L, (1 - (1 : ℝ) / p)⁻¹ := by
      rw [← Finset.prod_sdiff hS₁_sub]
      have h1 : (1 : ℝ) ≤ ∏ p ∈ Nat.primesLE L \ S₁, (1 - (1 : ℝ) / p)⁻¹ :=
        Finset.one_le_prod fun p hp ↦ hge1 p (Finset.mem_sdiff.mp hp).1
      have hnn : 0 ≤ ∏ p ∈ S₁, (1 - (1 : ℝ) / p)⁻¹ :=
        Finset.prod_nonneg fun p hp ↦ zero_le_one.trans (hge1 p (hS₁_sub hp))
      exact le_mul_of_one_le_left hnn h1
    calc ∏ p ∈ S₁, (1 - (1 : ℝ) / p)⁻¹
      _ ≤ ∏ p ∈ Nat.primesLE L, (1 - (1 : ℝ) / p)⁻¹ := hprod_le
      _ ≤ Real.exp 6 * Real.log L := prod_inv_one_sub_prime_le L (by omega)
      _ ≤ Real.exp 6 * Real.log (Real.log n) :=
          mul_le_mul_of_nonneg_left
            (Real.log_le_log (by exact_mod_cast (by omega : 0 < L)) hL_le)
            (Real.exp_pos 6).le
  have hS₂_card : (S₂.card : ℝ) ≤ Real.log n := by
    have hpow : (Real.log n) ^ S₂.card ≤ (n : ℝ) := by
      have h1 : (Real.log n) ^ S₂.card ≤ ∏ p ∈ S₂, (p : ℝ) := by
        rw [← Finset.prod_const]
        refine Finset.prod_le_prod (fun _ _ ↦ by linarith) fun p hp ↦ ?_
        simp only [S₂, Finset.mem_filter] at hp
        exact (Nat.lt_of_floor_lt (not_le.mp hp.2)).le
      have h2 : (∏ p ∈ S₂, p : ℕ) ≤ n := by
        have hdvd : (∏ p ∈ S₂, p) ∣ (∏ p ∈ n.primeFactors, p) :=
          Finset.prod_dvd_prod_of_subset S₂ n.primeFactors id (Finset.filter_subset _ _)
        exact Nat.le_of_dvd (by omega) (hdvd.trans (Nat.prod_primeFactors_dvd n))
      exact h1.trans (by rw [← Nat.cast_prod]; exact_mod_cast h2)
    have hlog := Real.log_le_log (pow_pos (by linarith) _) hpow
    rw [Real.log_pow] at hlog
    nlinarith
  have hprod₂ : ∏ p ∈ S₂, (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp 2 := by
    have hterm : ∀ p ∈ S₂, (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp (2 / Real.log n) := by
      intro p hp
      simp only [S₂, Finset.mem_filter] at hp
      have hp_gt : Real.log n < p := Nat.lt_of_floor_lt (not_le.mp hp.2)
      have hp4 : (4 : ℝ) < p := by linarith
      have heq : (1 - (1 : ℝ) / p)⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp; ring
      rw [heq]
      have h1 : 1 / ((p : ℝ) - 1) ≤ 2 / Real.log n := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      linarith [Real.add_one_le_exp (2 / Real.log n)]
    have hnn : ∀ p ∈ S₂, 0 ≤ (1 - (1 : ℝ) / p)⁻¹ := by
      intro p hp
      simp only [S₂, Finset.mem_filter] at hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp.1).two_le
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      exact inv_nonneg.mpr (by linarith)
    calc ∏ p ∈ S₂, (1 - (1 : ℝ) / p)⁻¹
      _ ≤ ∏ _p ∈ S₂, Real.exp (2 / Real.log n) := Finset.prod_le_prod hnn hterm
      _ = Real.exp (S₂.card * (2 / Real.log n)) := by
          rw [Finset.prod_const, ← Real.exp_nat_mul]
      _ ≤ Real.exp 2 := by
          apply Real.exp_le_exp.mpr
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          linarith
  have hprod₂_nn : 0 ≤ ∏ p ∈ S₂, (1 - (1 : ℝ) / p)⁻¹ :=
    Finset.prod_nonneg fun p hp ↦ by
      simp only [S₂, Finset.mem_filter] at hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp.1).two_le
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      exact inv_nonneg.mpr (by linarith)
  calc (∏ p ∈ S₁, (1 - (1 : ℝ) / p)⁻¹) * (∏ p ∈ S₂, (1 - (1 : ℝ) / p)⁻¹)
    _ ≤ (Real.exp 6 * Real.log (Real.log n)) * Real.exp 2 :=
        mul_le_mul hprod₁ hprod₂ hprod₂_nn (by positivity)
    _ = (Real.exp 6 * Real.exp 2) * Real.log (Real.log n) := by ring
    _ = Real.exp 8 * Real.log (Real.log n) := by
        rw [← Real.exp_add]; norm_num

lemma sum_rpow_rad_subset_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (m : ℕ) {α : ℝ} (hα : 0 < α) :
    ∑ a ∈ (Finset.Icc 1 m).filter (fun a ↦ a.primeFactors ⊆ s), ((a : ℝ) ^ α)⁻¹ ≤
      ∏ p ∈ s, (1 - ((p : ℝ) ^ α)⁻¹)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    have hsub : (Finset.Icc 1 m).filter (fun a ↦ a.primeFactors ⊆ ∅) ⊆ {1} := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.subset_empty] at ha
      simp only [Finset.mem_singleton]
      by_contra hne
      obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hne
      have : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, by omega⟩
      rw [ha.2] at this
      exact Finset.notMem_empty p this
    calc ∑ a ∈ (Finset.Icc 1 m).filter (fun a ↦ a.primeFactors ⊆ ∅), ((a : ℝ) ^ α)⁻¹
      _ ≤ ∑ a ∈ ({1} : Finset ℕ), ((a : ℝ) ^ α)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
      _ = 1 := by simp
  | insert p s' hp_not ih =>
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s')
    have hs' : ∀ q ∈ s', q.Prime := fun q hq ↦ hs q (Finset.mem_insert_of_mem hq)
    let A := (Finset.Icc 1 m).filter (fun a ↦ a.primeFactors ⊆ insert p s')
    let B := (Finset.Icc 1 m).filter (fun b ↦ b.primeFactors ⊆ s')
    let g : ℕ × ℕ → ℕ := fun eb ↦ p ^ eb.1 * eb.2
    have hcov : A ⊆ (Finset.range (m + 1) ×ˢ B).image g := by
      intro a ha
      simp only [A, Finset.mem_filter, Finset.mem_Icc] at ha
      have ha1 : 1 ≤ a := ha.1.1
      have ham : a ≤ m := ha.1.2
      let e := a.factorization p
      let b := a / p ^ e
      have hpe_dvd : p ^ e ∣ a := Nat.ordProj_dvd a p
      have hmul : p ^ e * b = a := Nat.mul_div_cancel' hpe_dvd
      have he_le : e ≤ m := by
        have h1 : e < 2 ^ e := Nat.lt_two_pow_self
        have h2 : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hpp.two_le e
        have h3 : p ^ e ≤ a := Nat.le_of_dvd (by omega) hpe_dvd
        omega
      have hb_pos : 1 ≤ b := by
        by_contra hb0
        have hb_eq : b = 0 := Nat.lt_one_iff.mp (not_le.mp hb0)
        have ha0 : a = 0 := by rw [← hmul, hb_eq, mul_zero]
        omega
      have hb_le : b ≤ m := by
        have : 1 ≤ p ^ e := Nat.one_le_pow _ _ hpp.pos
        nlinarith
      have hb_pf : b.primeFactors ⊆ s' := by
        intro q hq
        have hqb_dvd : q ∣ b := Nat.dvd_of_mem_primeFactors hq
        have hqa_dvd : q ∣ a := dvd_trans hqb_dvd (hmul ▸ dvd_mul_left b (p ^ e))
        have hqa : q ∈ a.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq, hqa_dvd, by omega⟩
        have hqp : q ≠ p := by
          intro heq
          have hp_ndvd : ¬ p ∣ b := Nat.not_dvd_ordCompl hpp (by omega : a ≠ 0)
          exact hp_ndvd (heq ▸ hqb_dvd)
        rcases Finset.mem_insert.mp (ha.2 hqa) with rfl | hqs'
        · exact (hqp rfl).elim
        · exact hqs'
      exact Finset.mem_image.mpr ⟨(e, b), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb_pos, hb_le⟩, hb_pf⟩⟩,
        hmul⟩
    have hr_lt : ((p : ℝ) ^ α)⁻¹ < 1 := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have : (1 : ℝ) < (p : ℝ) ^ α := Real.one_lt_rpow hp1 hα
      exact inv_lt_one_of_one_lt₀ this
    have hr_nn : (0 : ℝ) ≤ ((p : ℝ) ^ α)⁻¹ := by positivity
    have hgeom : ∑ e ∈ Finset.range (m + 1), (((p : ℝ) ^ α)⁻¹) ^ e ≤ (1 - ((p : ℝ) ^ α)⁻¹)⁻¹ := by
      rw [geom_sum_eq hr_lt.ne]
      rw [div_eq_mul_inv]
      have h1 : 1 - (((p : ℝ) ^ α)⁻¹) ^ (m + 1) ≤ 1 := by
        have : 0 ≤ (((p : ℝ) ^ α)⁻¹) ^ (m + 1) := pow_nonneg hr_nn _
        linarith
      have h2 : (((p : ℝ) ^ α)⁻¹) ^ (m + 1) - 1 = -(1 - (((p : ℝ) ^ α)⁻¹) ^ (m + 1)) := by ring
      have h3 : ((p : ℝ) ^ α)⁻¹ - 1 = -(1 - ((p : ℝ) ^ α)⁻¹) := by ring
      rw [h2, h3, inv_neg, neg_mul_neg]
      have hinv_nn : 0 ≤ (1 - ((p : ℝ) ^ α)⁻¹)⁻¹ := inv_nonneg.mpr (by linarith)
      nlinarith
    have hsum_A : ∑ a ∈ A, ((a : ℝ) ^ α)⁻¹ ≤
        (∑ e ∈ Finset.range (m + 1), (((p : ℝ) ^ α)⁻¹) ^ e) *
        (∑ b ∈ B, ((b : ℝ) ^ α)⁻¹) := by
      calc ∑ a ∈ A, ((a : ℝ) ^ α)⁻¹
        _ ≤ ∑ a ∈ (Finset.range (m + 1) ×ˢ B).image g, ((a : ℝ) ^ α)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ ↦ by positivity)
        _ ≤ ∑ eb ∈ Finset.range (m + 1) ×ˢ B, ((g eb : ℝ) ^ α)⁻¹ :=
            Finset.sum_image_le_of_nonneg (fun _ _ ↦ by positivity)
        _ = ∑ e ∈ Finset.range (m + 1), ∑ b ∈ B, (((p ^ e * b : ℕ) : ℝ) ^ α)⁻¹ :=
            Finset.sum_product _ _ _
        _ = ∑ e ∈ Finset.range (m + 1), ∑ b ∈ B, ((((p : ℝ) ^ α)⁻¹) ^ e) * ((b : ℝ) ^ α)⁻¹ := by
            refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
            push_cast
            rw [Real.mul_rpow (by positivity) (by positivity), mul_inv,
              ← Real.rpow_natCast (p : ℝ) e, ← Real.rpow_mul (by positivity),
              mul_comm (e : ℝ) α, Real.rpow_mul (by positivity), Real.rpow_natCast, inv_pow]
        _ = (∑ e ∈ Finset.range (m + 1), (((p : ℝ) ^ α)⁻¹) ^ e) * (∑ b ∈ B, ((b : ℝ) ^ α)⁻¹) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun e _ ↦ by rw [← Finset.mul_sum]
    rw [Finset.prod_insert hp_not]
    exact hsum_A.trans (mul_le_mul hgeom (ih hs') (Finset.sum_nonneg fun _ _ ↦ by positivity)
      (inv_nonneg.mpr (by linarith)))

lemma primeCounting_le_five_mul_div_log (N : ℕ) (hN : 2 ≤ N) :
    (Nat.primeCounting N : ℝ) ≤ 5 * (N : ℝ) / Real.log N := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hpi := Chebyshev.pi_le_log4_mul_div hN1
  rw [Nat.floor_natCast] at hpi
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hlog_sqrt : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt (by linarith)
  have hterm1 : Real.log 4 * N / Real.log (Real.sqrt N) ≤ 3 * N / Real.log N := by
    rw [hlog_sqrt]
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      have : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
      rw [this, Real.log_pow]; norm_num
    have hlog2 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
    have heq : Real.log 4 * N / (Real.log N / 2) = (2 * Real.log 4) * N / Real.log N := by
      field_simp
    rw [heq]
    gcongr
    linarith
  have hterm2 : Real.sqrt N ≤ 2 * N / Real.log N := by
    rw [le_div_iff₀ hlogN]
    have h1 : Real.log (Real.sqrt N) ≤ Real.sqrt N := by
      linarith [Real.log_le_sub_one_of_pos hsqrtN]
    have h2 : Real.log N ≤ 2 * Real.sqrt N := by linarith
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt (by linarith)
    nlinarith
  have hsum_eq : 3 * (N : ℝ) / Real.log N + 2 * (N : ℝ) / Real.log N = 5 * (N : ℝ) / Real.log N := by
    ring
  linarith

lemma prod_rankin_le (n : ℕ) (hn : 64 ≤ n) :
    ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹)⁻¹ ≤
      Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)) := by
  have hlogn_gt4 : 4 < Real.log n := log_gt_four_of_ge_64 hn
  have hfactor : ∀ p ∈ n.primeFactors,
      (1 - ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹)⁻¹ ≤ Real.exp (4 / Real.sqrt p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hsqrt_ge : (4 / 3 : ℝ) < Real.sqrt p := by
      rw [Real.lt_sqrt (by norm_num)]
      linarith
    have hsqrt_pos : 0 < Real.sqrt p := by linarith
    have hrpow : (p : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt p := (Real.sqrt_eq_rpow p).symm
    rw [hrpow]
    have hu_le : (Real.sqrt p)⁻¹ ≤ 3 / 4 := by
      rw [inv_le_comm₀ hsqrt_pos (by norm_num)]
      linarith
    have h1u : 1 / 4 ≤ 1 - (Real.sqrt p)⁻¹ := by linarith
    have hinv_eq : (1 - (Real.sqrt p)⁻¹)⁻¹ = 1 + (Real.sqrt p)⁻¹ / (1 - (Real.sqrt p)⁻¹) := by
      have hne : 1 - (Real.sqrt p)⁻¹ ≠ 0 := by linarith
      have hne1 : Real.sqrt p - 1 ≠ 0 := by linarith
      have hne2 : Real.sqrt p ≠ 0 := by linarith
      field_simp
      ring
    rw [hinv_eq]
    have hdiv_le : (Real.sqrt p)⁻¹ / (1 - (Real.sqrt p)⁻¹) ≤ 4 / Real.sqrt p := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - (Real.sqrt p)⁻¹)]
      have h1 : (Real.sqrt p)⁻¹ = 1 / Real.sqrt p := (one_div _).symm
      rw [h1] at h1u ⊢
      have h4eq : 4 / Real.sqrt p = 4 * (1 / Real.sqrt p) := by ring
      rw [h4eq]
      have : 0 ≤ 1 / Real.sqrt p := by positivity
      nlinarith
    linarith [Real.add_one_le_exp (4 / Real.sqrt p)]
  have hnn : ∀ p ∈ n.primeFactors, 0 ≤ (1 - ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hrpow : (p : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt p := (Real.sqrt_eq_rpow p).symm
    rw [hrpow]
    have hsqrt_gt1 : 1 < Real.sqrt p := by rw [Real.lt_sqrt (by norm_num)]; linarith
    have : (Real.sqrt p)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsqrt_gt1
    exact inv_nonneg.mpr (by linarith)
  have hprod : ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹)⁻¹ ≤
      Real.exp (∑ p ∈ n.primeFactors, 4 / Real.sqrt p) := by
    calc ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹)⁻¹
      _ ≤ ∏ p ∈ n.primeFactors, Real.exp (4 / Real.sqrt p) := Finset.prod_le_prod hnn hfactor
      _ = Real.exp (∑ p ∈ n.primeFactors, 4 / Real.sqrt p) := (Real.exp_sum _ _).symm
  refine hprod.trans (Real.exp_le_exp.mpr ?_)
  let B : ℕ := ⌊Real.sqrt (Real.log n)⌋₊
  let S₁ := n.primeFactors.filter (fun p ↦ p ≤ B)
  let S₂ := n.primeFactors.filter (fun p ↦ ¬ p ≤ B)
  rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p ↦ p ≤ B)]
  have hS₁ : ∑ p ∈ S₁, 4 / Real.sqrt p ≤ 4 * (Real.log n) ^ (3 / 4 : ℝ) := by
    have hcard : S₁.card ≤ B := by
      have hsub : S₁ ⊆ Finset.Icc 1 B := fun p hp ↦ by
        simp only [S₁, Finset.mem_filter] at hp
        exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp.1).one_le, hp.2⟩
      exact (Finset.card_le_card hsub).trans (by simp)
    have hterm : ∀ p ∈ S₁, 4 / Real.sqrt p ≤ 4 := by
      intro p hp
      have hp1 : (1 : ℝ) ≤ Real.sqrt p := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_le
      exact div_le_self (by norm_num) hp1
    calc ∑ p ∈ S₁, 4 / Real.sqrt p
      _ ≤ ∑ _p ∈ S₁, (4 : ℝ) := Finset.sum_le_sum hterm
      _ = S₁.card * 4 := by simp
      _ ≤ B * 4 := by gcongr
      _ ≤ Real.sqrt (Real.log n) * 4 := by gcongr; exact Nat.floor_le (Real.sqrt_nonneg _)
      _ = 4 * (Real.log n) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow, mul_comm]
      _ ≤ 4 * (Real.log n) ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by norm_num)
  have hS₂ : ∑ p ∈ S₂, 4 / Real.sqrt p ≤ 8 * (Real.log n) ^ (3 / 4 : ℝ) := by
    have hcard_all : (n.primeFactors.card : ℝ) ≤ 2 * Real.log n := by
      have hpow : (2 : ℕ) ^ n.primeFactors.card ≤ n := by
        have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
          rw [← Finset.prod_const]
          exact Finset.prod_le_prod' fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le
        exact h1.trans (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n))
      have hpowR : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast hpow
      have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ n.primeFactors.card) hpowR
      rw [Real.log_pow] at hlog
      have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith
    have hcard : (S₂.card : ℝ) ≤ 2 * Real.log n :=
      (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _) : (S₂.card : ℝ) ≤ _).trans hcard_all
    have hterm : ∀ p ∈ S₂, 4 / Real.sqrt p ≤ 4 / (Real.log n) ^ (1 / 4 : ℝ) := by
      intro p hp
      simp only [S₂, Finset.mem_filter] at hp
      have hp_gt : Real.sqrt (Real.log n) < p := Nat.lt_of_floor_lt (not_le.mp hp.2)
      have hsqrt_ge : (Real.log n) ^ (1 / 4 : ℝ) ≤ Real.sqrt p := by
        rw [Real.sqrt_eq_rpow]
        have h1 : (Real.log n) ^ (1 / 4 : ℝ) = (Real.sqrt (Real.log n)) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]; norm_num
        rw [h1]
        exact Real.rpow_le_rpow (Real.sqrt_nonneg _) hp_gt.le (by norm_num)
      exact div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos (by linarith) _) hsqrt_ge
    calc ∑ p ∈ S₂, 4 / Real.sqrt p
      _ ≤ ∑ _p ∈ S₂, (4 / (Real.log n) ^ (1 / 4 : ℝ)) := Finset.sum_le_sum hterm
      _ = S₂.card * (4 / (Real.log n) ^ (1 / 4 : ℝ)) := by simp
      _ ≤ (2 * Real.log n) * (4 / (Real.log n) ^ (1 / 4 : ℝ)) := by gcongr
      _ = 8 * (Real.log n) ^ (3 / 4 : ℝ) := by
          have h1 : Real.log n / (Real.log n) ^ (1 / 4 : ℝ) = (Real.log n) ^ (3 / 4 : ℝ) := by
            conv_lhs => arg 1; rw [← Real.rpow_one (Real.log n)]
            rw [← Real.rpow_sub (by linarith)]
            norm_num
          linarith [show (2 * Real.log n) * (4 / (Real.log n) ^ (1 / 4 : ℝ)) =
            8 * (Real.log n / (Real.log n) ^ (1 / 4 : ℝ)) by ring]
  linarith

lemma list_prod_ge_pow_of_forall_ge {l : List ℕ} {y : ℕ} (h : ∀ p ∈ l, y ≤ p) :
    y ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.length_cons, List.prod_cons, pow_succ']
    exact Nat.mul_le_mul (h p (List.mem_cons_self ..)) (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

lemma uncovered_card_le {n m y : ℕ} (hn : 64 ≤ n) (hy : 2 ≤ y) (hm : m < y ^ 3)
    (hm_le : m ≤ n) (hy_log : Real.log n / 4 ≤ Real.log y) :
    (((Finset.Icc 1 m).filter
      (fun x ↦ ∀ p ∈ Nat.primesLE y, ¬ p ∣ n → ¬ p ∣ x)).card : ℝ) ≤
      (m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)) +
      (200 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n := by
  classical
  let U := (Finset.Icc 1 m).filter (fun x ↦ ∀ p ∈ Nat.primesLE y, ¬ p ∣ n → ¬ p ∣ x)
  let A := (Finset.Icc 1 m).filter (fun a ↦ a.primeFactors ⊆ n.primeFactors)
  let Pgt := (Nat.primesLE m).filter (fun p ↦ y < p)
  let U₁ := U.filter (fun x ↦ x ∈ A)
  let U₂ := U.filter (fun x ↦ ∃ a ∈ A, ∃ p ∈ Pgt, x = a * p)
  let U₃ := U.filter (fun x ↦ ∃ a ∈ A, ∃ p ∈ Pgt, ∃ q ∈ Pgt, x = a * p * q)
  have hU_sub : U ⊆ U₁ ∪ U₂ ∪ U₃ := by
    intro x hxU
    have hx := hxU
    simp only [U, Finset.mem_filter, Finset.mem_Icc] at hx
    let a := ∏ p ∈ x.primeFactors ∩ n.primeFactors, p ^ (x.factorization p)
    let b := ∏ p ∈ x.primeFactors \ n.primeFactors, p ^ (x.factorization p)
    have hmul : a * b = x := by
      have hdisj : Disjoint (x.primeFactors ∩ n.primeFactors) (x.primeFactors \ n.primeFactors) :=
        Finset.disjoint_left.mpr fun p h1 h2 ↦
          (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
      have hunion : (x.primeFactors ∩ n.primeFactors) ∪ (x.primeFactors \ n.primeFactors) =
          x.primeFactors := by
        ext p; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
      rw [← Finset.prod_union hdisj, hunion]
      have hxne : x ≠ 0 := by have := hx.1.1; omega
      exact (Nat.prod_factorization_eq_prod_primeFactors _).symm.trans
        (Nat.prod_factorization_pow_eq_self hxne)
    have ha_pos : 1 ≤ a := by
      by_contra h0
      have ha0 : a = 0 := by omega
      have hx0 : x = 0 := by rw [← hmul, ha0, zero_mul]
      have hx1 : 1 ≤ x := hx.1.1
      omega
    have hb_pos : 1 ≤ b := by
      by_contra h0
      have hb0 : b = 0 := by omega
      have hx0 : x = 0 := by rw [← hmul, hb0, mul_zero]
      have hx1 : 1 ≤ x := hx.1.1
      omega
    have ha_le : a ≤ m := by nlinarith [hx.1.2]
    have hb_le : b ≤ m := by nlinarith [hx.1.2]
    have ha_pf : a.primeFactors ⊆ n.primeFactors := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpdvd := Nat.dvd_of_mem_primeFactors hp
      rw [Prime.dvd_finsetProd_iff hpp.prime] at hpdvd
      rcases hpdvd with ⟨q, hq, hpdvdq⟩
      have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq).1
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp (hpp.dvd_of_dvd_pow hpdvdq)
      subst heq
      exact (Finset.mem_inter.mp hq).2
    have ha_mem : a ∈ A :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha_pos, ha_le⟩, ha_pf⟩
    have hb_gt : ∀ p ∈ b.primeFactorsList, y < p := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
      have hpdvd : p ∣ b := Nat.dvd_of_mem_primeFactorsList hp
      rw [Prime.dvd_finsetProd_iff hpp.prime] at hpdvd
      rcases hpdvd with ⟨q, hq, hpdvdq⟩
      have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp (hpp.dvd_of_dvd_pow hpdvdq)
      subst heq
      have hp_not_n : ¬ p ∣ n := by
        intro hdn
        exact (Finset.mem_sdiff.mp hq).2 (Nat.mem_primeFactors.mpr ⟨hpp, hdn, by omega⟩)
      have hp_dvd_x : p ∣ x := Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
      by_contra hle
      push Not at hle
      exact hx.2 p (Nat.mem_primesLE.mpr ⟨hle, hpp⟩) hp_not_n hp_dvd_x
    have hlen : b.primeFactorsList.length ≤ 2 := by
      by_contra hgt
      push Not at hgt
      have hge3 : 3 ≤ b.primeFactorsList.length := by omega
      have hprod_b : b.primeFactorsList.prod = b := Nat.prod_primeFactorsList (by omega)
      have hpow_le : y ^ b.primeFactorsList.length ≤ b.primeFactorsList.prod :=
        list_prod_ge_pow_of_forall_ge fun p hp ↦ (hb_gt p hp).le
      have hpow3 : y ^ 3 ≤ y ^ b.primeFactorsList.length := Nat.pow_le_pow_right (by omega) hge3
      omega
    rcases hlist : b.primeFactorsList with _ | ⟨p, _ | ⟨q, _ | ⟨r, rs⟩⟩⟩
    · have hb1 : b = 1 := by
        rw [← Nat.prod_primeFactorsList (by omega : b ≠ 0), hlist]; simp
      rw [hb1, mul_one] at hmul
      rw [hmul] at ha_mem
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxU, ha_mem⟩))
    · have hbp : b = p := by
        rw [← Nat.prod_primeFactorsList (by omega : b ≠ 0), hlist]; simp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList (hlist ▸ List.mem_cons_self ..)
      have hpy : y < p := hb_gt p (hlist ▸ List.mem_cons_self ..)
      have hpm : p ∈ Pgt := Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hbp ▸ hb_le, hpp⟩, hpy⟩
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hxU, ⟨a, ha_mem, p, hpm, by rw [← hmul, hbp]⟩⟩))
    · have hbpq : b = p * q := by
        rw [← Nat.prod_primeFactorsList (by omega : b ≠ 0), hlist]; simp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList (hlist ▸ List.mem_cons_self ..)
      have hqp : q.Prime := Nat.prime_of_mem_primeFactorsList
        (hlist ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hpy : y < p := hb_gt p (hlist ▸ List.mem_cons_self ..)
      have hqy : y < q := hb_gt q (hlist ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hp_le : p ≤ m := by nlinarith [hqp.one_le]
      have hq_le : q ≤ m := by nlinarith [hpp.one_le]
      have hpm : p ∈ Pgt := Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hp_le, hpp⟩, hpy⟩
      have hqm : q ∈ Pgt := Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hq_le, hqp⟩, hqy⟩
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hxU, ⟨a, ha_mem, p, hpm, q, hqm, by rw [← hmul, hbpq, mul_assoc]⟩⟩)
    · rw [hlist] at hlen; simp at hlen
  have hcard_split : (U.card : ℝ) ≤ (U₁.card : ℝ) + (U₂.card : ℝ) + (U₃.card : ℝ) := by
    have h1 : U.card ≤ U₁.card + U₂.card + U₃.card :=
      (Finset.card_le_card hU_sub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    exact_mod_cast h1
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogy_pos : 0 < Real.log y := by linarith
  have hU₁ : (U₁.card : ℝ) ≤ (m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)) := by
    have hsub : U₁ ⊆ A := fun x hx ↦ (Finset.mem_filter.mp hx).2
    have hcardA : (A.card : ℝ) ≤ (m : ℝ) ^ (1 / 2 : ℝ) * ∑ a ∈ A, ((a : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      calc (A.card : ℝ) = ∑ _a ∈ A, (1 : ℝ) := by simp
        _ ≤ ∑ a ∈ A, (m : ℝ) ^ (1 / 2 : ℝ) * ((a : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
            refine Finset.sum_le_sum fun a ha ↦ ?_
            simp only [A, Finset.mem_filter, Finset.mem_Icc] at ha
            have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha.1.1
            have hle : (a : ℝ) ^ (1 / 2 : ℝ) ≤ (m : ℝ) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow ha_pos.le (by exact_mod_cast ha.1.2) (by norm_num)
            rw [← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos ha_pos _)]
            exact hle
    have hsumA := sum_rpow_rad_subset_le n.primeFactors
      (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) m (by norm_num : (0 : ℝ) < 1 / 2)
    have hrankin := prod_rankin_le n hn
    calc (U₁.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ (m : ℝ) ^ (1 / 2 : ℝ) * ∑ a ∈ A, ((a : ℝ) ^ (1 / 2 : ℝ))⁻¹ := hcardA
      _ ≤ (m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)) := by
          gcongr
          exact hsumA.trans hrankin
  have hsumA1 : ∑ a ∈ A, (1 : ℝ) / a ≤ Real.exp 8 * Real.log (Real.log n) := by
    have h1 := sum_rpow_rad_subset_le n.primeFactors
      (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) m (by norm_num : (0 : ℝ) < 1)
    simp only [Real.rpow_one] at h1
    have hlhs : ∑ a ∈ A, (1 : ℝ) / a = ∑ a ∈ A, ((a : ℝ))⁻¹ := by
      refine Finset.sum_congr rfl fun _ _ ↦ one_div _
    have hrhs : ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹)⁻¹ =
        ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p)⁻¹ := by
      refine Finset.prod_congr rfl fun _ _ ↦ by rw [one_div]
    rw [hlhs]
    exact h1.trans (hrhs.trans_le (prod_inv_one_sub_primeFactors_le n hn))
  have hpi_gt : ∀ k : ℕ, y < k → (Nat.primeCounting k : ℝ) ≤ 20 * (k : ℝ) / Real.log n := by
    intro k hk
    have hk2 : 2 ≤ k := by omega
    have h1 := primeCounting_le_five_mul_div_log k hk2
    have hlogk : Real.log n / 4 ≤ Real.log k :=
      hy_log.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast hk.le))
    have hdiv : 5 * (k : ℝ) / Real.log k ≤ 5 * (k : ℝ) / (Real.log n / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlogk
    have heq : 5 * (k : ℝ) / (Real.log n / 4) = 20 * (k : ℝ) / Real.log n := by ring
    linarith
  have hU₂ : (U₂.card : ℝ) ≤ (20 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n := by
    have hsub : U₂ ⊆ A.biUnion (fun a ↦ (Pgt.filter (fun p ↦ p ≤ m / a)).image (fun p ↦ a * p)) := by
      intro x hx
      simp only [U₂, Finset.mem_filter] at hx
      rcases hx.2 with ⟨a, ha, p, hp, rfl⟩
      have hxle : a * p ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx.1).1).2
      have ha_pos : 0 < a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨p, Finset.mem_filter.mpr ⟨hp, (Nat.le_div_iff_mul_le ha_pos).mpr (by rwa [mul_comm])⟩, rfl⟩⟩
    have hcard_le : (U₂.card : ℝ) ≤ ∑ a ∈ A, ((Pgt.filter (fun p ↦ p ≤ m / a)).card : ℝ) := by
      have h1 : U₂.card ≤ ∑ a ∈ A, ((Pgt.filter (fun p ↦ p ≤ m / a)).image (fun p ↦ a * p)).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have h2 : ∑ a ∈ A, ((Pgt.filter (fun p ↦ p ≤ m / a)).image (fun p ↦ a * p)).card ≤
          ∑ a ∈ A, (Pgt.filter (fun p ↦ p ≤ m / a)).card :=
        Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le
      exact_mod_cast h1.trans h2
    have hinner : ∀ a ∈ A, ((Pgt.filter (fun p ↦ p ≤ m / a)).card : ℝ) ≤
        20 * (m : ℝ) / Real.log n * (1 / a) := by
      intro a ha
      by_cases hgt : y < m / a
      · have hsubp : Pgt.filter (fun p ↦ p ≤ m / a) ⊆ Nat.primesLE (m / a) := fun p hp ↦ by
          simp only [Pgt, Finset.mem_filter, Nat.mem_primesLE] at hp ⊢
          exact ⟨hp.2, hp.1.1.2⟩
        have h1 : ((Pgt.filter (fun p ↦ p ≤ m / a)).card : ℝ) ≤ Nat.primeCounting (m / a) := by
          rw [← Nat.primesLE_card_eq_primeCounting]
          exact_mod_cast Finset.card_le_card hsubp
        have h2 := hpi_gt (m / a) hgt
        have h3 : ((m / a : ℕ) : ℝ) ≤ (m : ℝ) / a := Nat.cast_div_le
        have h4 : 20 * ((m / a : ℕ) : ℝ) / Real.log n ≤ 20 * ((m : ℝ) / a) / Real.log n := by gcongr
        have heq : 20 * ((m : ℝ) / a) / Real.log n = 20 * (m : ℝ) / Real.log n * (1 / a) := by ring
        linarith
      · have hemp : Pgt.filter (fun p ↦ p ≤ m / a) = ∅ := by
          ext p; simp only [Pgt, Finset.mem_filter, Finset.notMem_empty, iff_false]; omega
        rw [hemp]; simp; positivity
    calc (U₂.card : ℝ) ≤ ∑ a ∈ A, ((Pgt.filter (fun p ↦ p ≤ m / a)).card : ℝ) := hcard_le
      _ ≤ ∑ a ∈ A, (20 * (m : ℝ) / Real.log n * (1 / a)) := Finset.sum_le_sum hinner
      _ = 20 * (m : ℝ) / Real.log n * ∑ a ∈ A, (1 : ℝ) / a := by rw [← Finset.mul_sum]
      _ ≤ 20 * (m : ℝ) / Real.log n * (Real.exp 8 * Real.log (Real.log n)) := by gcongr
      _ = (20 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n := by ring
  have hsum_Pgt : ∑ p ∈ Pgt, (1 : ℝ) / p ≤ 9 := by
    by_cases hm2 : 2 ≤ m
    · have h1 : Real.log y * ∑ p ∈ Pgt, (1 : ℝ) / p ≤ ∑ p ∈ Nat.primesLE m, Real.log p / p := by
        rw [Finset.mul_sum]
        calc ∑ p ∈ Pgt, Real.log y * (1 / p)
          _ ≤ ∑ p ∈ Pgt, Real.log p / p := by
              refine Finset.sum_le_sum fun p hp ↦ ?_
              simp only [Pgt, Finset.mem_filter] at hp
              rw [mul_one_div]
              exact div_le_div_of_nonneg_right
                (Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast hp.2.le))
                (by positivity)
          _ ≤ ∑ p ∈ Nat.primesLE m, Real.log p / p :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p hp _ ↦ by
                have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
                  exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
                exact div_nonneg (Real.log_nonneg hp1) (by positivity))
      have h2 := sum_log_div_prime_le m hm2
      have hlogm : Real.log m ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast hm_le)
      have hlog4 : Real.log 4 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4 ≤ n))
      have h3 : (Real.log n / 4) * ∑ p ∈ Pgt, (1 : ℝ) / p ≤ 2 * Real.log n := by
        have hnn : 0 ≤ ∑ p ∈ Pgt, (1 : ℝ) / p := Finset.sum_nonneg fun _ _ ↦ by positivity
        nlinarith
      nlinarith
    · have hemp : Pgt = ∅ := by
        ext p; simp only [Pgt, Finset.mem_filter, Nat.mem_primesLE, Finset.notMem_empty, iff_false]
        omega
      rw [hemp]; simp
  have hU₃ : (U₃.card : ℝ) ≤ (180 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n := by
    have hsub : U₃ ⊆ (A ×ˢ Pgt).biUnion
        (fun ap ↦ (Pgt.filter (fun q ↦ q ≤ m / (ap.1 * ap.2))).image (fun q ↦ ap.1 * ap.2 * q)) := by
      intro x hx
      simp only [U₃, Finset.mem_filter] at hx
      rcases hx.2 with ⟨a, ha, p, hp, q, hq, rfl⟩
      have hxle : a * p * q ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx.1).1).2
      have ha_pos : 0 < a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      have hp_pos : 0 < p := by
        simp only [Pgt, Finset.mem_filter] at hp; omega
      exact Finset.mem_biUnion.mpr ⟨(a, p), Finset.mem_product.mpr ⟨ha, hp⟩,
        Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr
          ⟨hq, (Nat.le_div_iff_mul_le (Nat.mul_pos ha_pos hp_pos)).mpr (by rwa [mul_comm])⟩, rfl⟩⟩
    have hcard_le : (U₃.card : ℝ) ≤
        ∑ ap ∈ A ×ˢ Pgt, ((Pgt.filter (fun q ↦ q ≤ m / (ap.1 * ap.2))).card : ℝ) := by
      have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have h2 := Finset.sum_le_sum (s := A ×ˢ Pgt) fun ap _ ↦
        Finset.card_image_le (f := fun q ↦ ap.1 * ap.2 * q) (s := Pgt.filter (fun q ↦ q ≤ m / (ap.1 * ap.2)))
      exact_mod_cast h1.trans h2
    have hinner : ∀ ap ∈ A ×ˢ Pgt,
        ((Pgt.filter (fun q ↦ q ≤ m / (ap.1 * ap.2))).card : ℝ) ≤
        20 * (m : ℝ) / Real.log n * (1 / (ap.1 : ℝ)) * (1 / (ap.2 : ℝ)) := by
      intro ap hap
      by_cases hgt : y < m / (ap.1 * ap.2)
      · have hsubq : Pgt.filter (fun q ↦ q ≤ m / (ap.1 * ap.2)) ⊆ Nat.primesLE (m / (ap.1 * ap.2)) :=
          fun q hq ↦ by
            simp only [Pgt, Finset.mem_filter, Nat.mem_primesLE] at hq ⊢
            exact ⟨hq.2, hq.1.1.2⟩
        have h1 : ((Pgt.filter (fun q ↦ q ≤ m / (ap.1 * ap.2))).card : ℝ) ≤
            Nat.primeCounting (m / (ap.1 * ap.2)) := by
          rw [← Nat.primesLE_card_eq_primeCounting]
          exact_mod_cast Finset.card_le_card hsubq
        have h2 := hpi_gt (m / (ap.1 * ap.2)) hgt
        have h3 : ((m / (ap.1 * ap.2) : ℕ) : ℝ) ≤ (m : ℝ) / ((ap.1 * ap.2 : ℕ) : ℝ) :=
          Nat.cast_div_le
        have h4 : 20 * ((m / (ap.1 * ap.2) : ℕ) : ℝ) / Real.log n ≤
            20 * ((m : ℝ) / ((ap.1 * ap.2 : ℕ) : ℝ)) / Real.log n := by gcongr
        have heq : 20 * ((m : ℝ) / ((ap.1 * ap.2 : ℕ) : ℝ)) / Real.log n =
            20 * (m : ℝ) / Real.log n * (1 / (ap.1 : ℝ)) * (1 / (ap.2 : ℝ)) := by
          push_cast; ring
        linarith
      · have hemp : Pgt.filter (fun q ↦ q ≤ m / (ap.1 * ap.2)) = ∅ := by
          ext q; simp only [Pgt, Finset.mem_filter, Finset.notMem_empty, iff_false]; omega
        rw [hemp]; simp; positivity
    have hloglog_nn : 0 ≤ Real.log (Real.log n) := (zero_lt_one.trans (log_log_gt_one_of_ge_64 hn)).le
    calc (U₃.card : ℝ)
      _ ≤ ∑ ap ∈ A ×ˢ Pgt, (20 * (m : ℝ) / Real.log n * (1 / (ap.1 : ℝ)) * (1 / (ap.2 : ℝ))) :=
          hcard_le.trans (Finset.sum_le_sum hinner)
      _ = (20 * (m : ℝ) / Real.log n) * (∑ a ∈ A, (1 : ℝ) / a) * (∑ p ∈ Pgt, (1 : ℝ) / p) := by
          rw [Finset.sum_product]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ (20 * (m : ℝ) / Real.log n) * (Real.exp 8 * Real.log (Real.log n)) * 9 := by
          have hnn2 : 0 ≤ ∑ p ∈ Pgt, (1 : ℝ) / p := Finset.sum_nonneg fun _ _ ↦ by positivity
          have h1 : (20 * (m : ℝ) / Real.log n) * (∑ a ∈ A, (1 : ℝ) / a) ≤
              (20 * (m : ℝ) / Real.log n) * (Real.exp 8 * Real.log (Real.log n)) := by gcongr
          have h2 : 0 ≤ (20 * (m : ℝ) / Real.log n) * (Real.exp 8 * Real.log (Real.log n)) := by
            positivity
          exact mul_le_mul h1 hsum_Pgt hnn2 h2
      _ = (180 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n := by ring
  change (U.card : ℝ) ≤ _
  have hsum_coeff : (20 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n +
      (180 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n =
      (200 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n := by ring
  linarith

/- Section 4: Putting the upper bound together -/

lemma alon_erdos_upper_rankin {n m : ℕ} {gn : ℝ} (hn : 64 ≤ n)
    (hlog_big : (100000000 : ℝ) ≤ Real.log n)
    (hlog_rpow : Real.log n ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 300 : ℝ))
    (hgn_eq : gn = (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (1 / 3 : ℝ))
    (hg_ge_quarter : (n : ℝ) ^ (1 / 4 : ℝ) ≤ gn)
    (hm_le_real : (m : ℝ) ≤ (n : ℝ) / gn) :
    2 * (m : ℝ) * ((m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ))) / n ≤ gn := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log n := by linarith
  have hloglog_ge1 : 1 ≤ Real.log (Real.log n) := (log_log_gt_one_of_ge_64 hn).le
  have hg_pos : 0 < gn := lt_of_lt_of_le (Real.rpow_pos_of_pos hn_pos _) hg_ge_quarter
  have hm_le_n34 : (m : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
    have h1 : (n : ℝ) / gn ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
      rw [div_le_iff₀ hg_pos]
      have hmul : (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = n := by
        rw [← Real.rpow_add hn_pos]; norm_num
      exact hmul.symm.le.trans (mul_le_mul_of_nonneg_left hg_ge_quarter (by positivity))
    exact hm_le_real.trans h1
  have h_exp : Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)) ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
    rw [Real.rpow_def_of_pos hn_pos]
    apply Real.exp_le_exp.mpr
    have h1 : (100 : ℝ) ≤ (Real.log n) ^ (1 / 4 : ℝ) := by
      calc (100 : ℝ) = (100000000 : ℝ) ^ (1 / 4 : ℝ) := by
            rw [show (100000000 : ℝ) = 100 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ (Real.log n) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) hlog_big (by norm_num)
    have h2 : (Real.log n) ^ (3 / 4 : ℝ) * (Real.log n) ^ (1 / 4 : ℝ) = Real.log n := by
      rw [← Real.rpow_add hlog_pos]; norm_num
    nlinarith [Real.rpow_pos_of_pos hlog_pos (3 / 4 : ℝ)]
  have hm_32 : (m : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (9 / 8 : ℝ) := by
    have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    calc (m : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ)
      _ ≤ (n : ℝ) ^ (3 / 4 : ℝ) * ((n : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / 2 : ℝ) :=
          mul_le_mul hm_le_n34 (Real.rpow_le_rpow hm_nn hm_le_n34 (by norm_num))
            (by positivity) (by positivity)
      _ = (n : ℝ) ^ (9 / 8 : ℝ) := by
          rw [← Real.rpow_mul hn_pos.le, ← Real.rpow_add hn_pos]; norm_num
  have hnum : 2 * (m : ℝ) * ((m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ))) ≤
      2 * (n : ℝ) ^ (5 / 4 : ℝ) := by
    calc 2 * (m : ℝ) * ((m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)))
      _ = 2 * ((m : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ)) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)) := by ring
      _ ≤ 2 * (n : ℝ) ^ (9 / 8 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) := by gcongr
      _ = 2 * (n : ℝ) ^ (5 / 4 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hn_pos]; norm_num
  have hdiv : 2 * (n : ℝ) ^ (5 / 4 : ℝ) / n = 2 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [mul_div_assoc]
    congr 1
    conv_lhs => arg 2; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_sub hn_pos]; norm_num
  have hhalf : 2 * (n : ℝ) ^ (1 / 4 : ℝ) ≤ gn := by
    have h1 : 2 * (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 300 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hn_pos]
      have h2le : (2 : ℝ) ≤ (n : ℝ) ^ (24 / 300 : ℝ) := by
        have h2pow : (2 : ℝ) ^ (100 : ℕ) ≤ (n : ℝ) := by
          have h100 : (100 : ℝ) * Real.log 2 ≤ Real.log n := by
            linarith [Real.log_two_lt_d9]
          have h2 := Real.exp_le_exp.mpr h100
          rw [Real.exp_log hn_pos] at h2
          have heq : Real.exp (100 * Real.log 2) = (2 : ℝ) ^ (100 : ℕ) := by
            rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
            ring_nf
          linarith
        calc (2 : ℝ) = ((2 : ℝ) ^ (100 : ℕ)) ^ (1 / 100 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
          _ ≤ (n : ℝ) ^ (1 / 100 : ℝ) := Real.rpow_le_rpow (by positivity) h2pow (by norm_num)
          _ ≤ (n : ℝ) ^ (24 / 300 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
      have hmul : 2 * (n : ℝ) ^ (1 / 4 + 1 / 300 : ℝ) ≤
          (n : ℝ) ^ (24 / 300 : ℝ) * (n : ℝ) ^ (1 / 4 + 1 / 300 : ℝ) := by gcongr
      rw [← Real.rpow_add hn_pos] at hmul
      exact hmul.trans (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num))
    have h2 : 2 * (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (1 / 3 : ℝ) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hlog_pos _)]
      exact (mul_le_mul_of_nonneg_left hlog_rpow (by positivity)).trans h1
    have h3 : 1 ≤ Real.log (Real.log n) ^ (1 / 3 : ℝ) := Real.one_le_rpow hloglog_ge1 (by norm_num)
    rw [hgn_eq]
    exact h2.trans (le_mul_of_one_le_right (by positivity) h3)
  calc 2 * (m : ℝ) * ((m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ))) / n
    _ ≤ 2 * (n : ℝ) ^ (5 / 4 : ℝ) / n := div_le_div_of_nonneg_right hnum hn_pos.le
    _ = 2 * (n : ℝ) ^ (1 / 4 : ℝ) := hdiv
    _ ≤ gn := hhalf

lemma alon_erdos_upper_main_term {n m : ℕ} {gn : ℝ} (hn : 64 ≤ n)
    (hgn_eq : gn = (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (1 / 3 : ℝ))
    (hm_le_real : (m : ℝ) ≤ (n : ℝ) / gn) :
    2 * (m : ℝ) * ((200 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n) / n ≤
      (400 * Real.exp 8) * gn := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log n := by linarith [log_gt_four_of_ge_64 hn]
  have hloglog_pos : 0 < Real.log (Real.log n) := by linarith [log_log_gt_one_of_ge_64 hn]
  have hg_pos : 0 < gn := by rw [hgn_eq]; positivity
  have hgn_cube : gn ^ 3 = (n : ℝ) * Real.log (Real.log n) / Real.log n := by
    rw [hgn_eq]
    have h1 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
    have h2 : ((Real.log n) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = Real.log n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlog_pos.le]; norm_num
    have h3 : ((Real.log (Real.log n)) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = Real.log (Real.log n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hloglog_pos.le]; norm_num
    rw [mul_pow, div_pow, h1, h2, h3]; ring
  have hm2 : (m : ℝ) ^ 2 ≤ ((n : ℝ) / gn) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg m) hm_le_real 2
  have hfactor_nn : 0 ≤ (400 * Real.exp 8) * Real.log (Real.log n) / (Real.log n * n) := by
    positivity
  calc 2 * (m : ℝ) * ((200 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n) / n
    _ = (m : ℝ) ^ 2 * ((400 * Real.exp 8) * Real.log (Real.log n) / (Real.log n * n)) := by ring
    _ ≤ ((n : ℝ) / gn) ^ 2 * ((400 * Real.exp 8) * Real.log (Real.log n) / (Real.log n * n)) :=
        mul_le_mul_of_nonneg_right hm2 hfactor_nn
    _ = (400 * Real.exp 8) * ((n : ℝ) * Real.log (Real.log n) / Real.log n) / gn ^ 2 := by
        field_simp
    _ = (400 * Real.exp 8) * gn ^ 3 / gn ^ 2 := by rw [hgn_cube]
    _ = (400 * Real.exp 8) * gn := by field_simp

lemma f_le_cover_params {n K y' : ℕ} (hn : 2 ≤ n) (hK : 2 ≤ K) :
    ∃ ℬ : Finset (Finset ℕ),
      let m := n / (K + 1)
      let U := (Finset.Icc 1 m).filter (fun x ↦ ∀ p ∈ Nat.primesLE y', ¬ p ∣ n → ¬ p ∣ x)
      Erdos360.f n ≤ K + y' + ℬ.card ∧ n * ℬ.card ≤ 2 * m * U.card + n := by
  classical
  let m := n / (K + 1)
  have h2m_le : 2 * m ≤ n := by
    have h1 : 2 * (n / (K + 1)) ≤ (K + 1) * (n / (K + 1)) := Nat.mul_le_mul_right _ (by omega)
    exact h1.trans (Nat.mul_div_le n (K + 1))
  let ℱ_int : Finset (Finset ℕ) := (Finset.Icc 1 K).image (intervalClass n)
  let ℱ_prime : Finset (Finset ℕ) :=
    ((Nat.primesLE y').filter (fun p ↦ ¬ p ∣ n)).image (multClass n)
  let U : Finset ℕ := (Finset.Icc 1 m).filter (fun x ↦ ∀ p ∈ Nat.primesLE y', ¬ p ∣ n → ¬ p ∣ x)
  have hU_el : ∀ x ∈ U, 1 ≤ x ∧ 2 * x ≤ n := by
    intro x hx
    simp only [U, Finset.mem_filter, Finset.mem_Icc] at hx
    exact ⟨hx.1.1, by omega⟩
  obtain ⟨ℬ, hℬ_cov, hℬ_sum, hℬ_card⟩ := greedy_pack hn U hU_el
  let ℱ := ℱ_int ∪ ℱ_prime ∪ ℬ
  have hcov : Finset.Icc 1 (n - 1) ⊆ ℱ.biUnion id := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    by_cases hxm : m < x
    · let k := n / x
      have hk1 : 1 ≤ k := Nat.div_pos (by omega) (by omega)
      have hk_le : k ≤ K := by
        have h1 : m + 1 ≤ x := hxm
        have h2 : n < (K + 1) * (m + 1) := by
          have hdm := Nat.div_add_mod n (K + 1)
          have hml := Nat.mod_lt n (by omega : 0 < K + 1)
          dsimp only [m]
          nlinarith
        have h3 : n < (K + 1) * x := lt_of_lt_of_le h2 (Nat.mul_le_mul_left _ h1)
        exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).mpr
          (by rw [Nat.succ_eq_add_one]; exact h3))
      have hx_int : x ∈ intervalClass n k := by
        simp only [intervalClass, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨hx, ?_, ?_⟩
        · have hdm := Nat.div_add_mod n x
          have hml := Nat.mod_lt n (by omega : 0 < x)
          dsimp only [k]
          nlinarith
        · rw [mul_comm]; exact Nat.mul_div_le n x
      exact Finset.mem_biUnion.mpr ⟨intervalClass n k,
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨k, Finset.mem_Icc.mpr ⟨hk1, hk_le⟩, rfl⟩)), hx_int⟩
    · push Not at hxm
      by_cases hdiv : ∃ p ∈ Nat.primesLE y', ¬ p ∣ n ∧ p ∣ x
      · rcases hdiv with ⟨p, hp, hndvd, hdvd⟩
        have hx_mult : x ∈ multClass n p := by
          simp only [multClass, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨hx, hdvd⟩
        exact Finset.mem_biUnion.mpr ⟨multClass n p,
          Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨p, Finset.mem_filter.mpr ⟨hp, hndvd⟩, rfl⟩)), hx_mult⟩
      · push Not at hdiv
        have hxU : x ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hx.1, hxm⟩, hdiv⟩
        rcases Finset.mem_biUnion.mp (hℬ_cov hxU) with ⟨B, hB, hxB⟩
        exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_union_right _ hB, hxB⟩
  have hfree : ∀ A ∈ ℱ, n ∉ subsetSums (A : Set ℕ) := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA12 | hA3
    · rcases Finset.mem_union.mp hA12 with hA1 | hA2
      · rcases Finset.mem_image.mp hA1 with ⟨k, hk, rfl⟩
        exact intervalClass_sum_free hn (Finset.mem_Icc.mp hk).1
      · rcases Finset.mem_image.mp hA2 with ⟨p, hp, rfl⟩
        exact multClass_sum_free (Finset.mem_filter.mp hp).2
    · exact small_sum_free (hℬ_sum A hA3)
  have hf_le : Erdos360.f n ≤ ℱ_int.card + ℱ_prime.card + ℬ.card :=
    (f_le_of_cover ℱ hcov hfree).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcard_int : ℱ_int.card ≤ K := Finset.card_image_le.trans (by simp)
  have hcard_prime : ℱ_prime.card ≤ y' := by
    refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
    have hsub : Nat.primesLE y' ⊆ Finset.Icc 1 y' := fun p hp ↦
      Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩
    exact (Finset.card_le_card hsub).trans (by simp)
  have hU_sum : ∑ x ∈ U, x ≤ m * U.card := by
    calc ∑ x ∈ U, x ≤ ∑ _x ∈ U, m :=
          Finset.sum_le_sum fun x hx ↦ (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).2
      _ = U.card * m := by simp
      _ = m * U.card := mul_comm _ _
  exact ⟨ℬ, by omega, by dsimp only [m, U] at hℬ_card hU_sum ⊢; linarith⟩

lemma alon_erdos_upper :
    (fun n : ℕ ↦ (Erdos360.f n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (1 / 3 : ℝ) *
        Real.log (Real.log n) ^ (1 / 3 : ℝ)) := by
  let g : ℕ → ℝ := fun n ↦
    (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (1 / 3 : ℝ)
  have hg_tendsto : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_big : ∀ᶠ n : ℕ in atTop, (100000000 : ℝ) ≤ Real.log n :=
    hg_tendsto.eventually_ge_atTop _
  have hpow_log : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 100 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 2] with n hn hn2
    have hlognn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    rw [Real.norm_of_nonneg hlognn, Real.norm_of_nonneg (by positivity), one_mul] at hn
    exact hn
  refine IsBigO.of_bound (6 + 400 * Real.exp 8) ?_
  filter_upwards [eventually_ge_atTop 64, hlog_big, hpow_log] with n hn64 hlog_big hpow_log
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log n := by linarith
  have hloglog_ge1 : 1 ≤ Real.log (Real.log n) := (log_log_gt_one_of_ge_64 hn64).le
  have hg_pos : 0 < g n := by dsimp only [g]; positivity
  have hlog_rpow : Real.log n ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 300 : ℝ) := by
    calc Real.log n ^ (1 / 3 : ℝ)
      _ ≤ ((n : ℝ) ^ (1 / 100 : ℝ)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow hlog_pos.le hpow_log (by norm_num)
      _ = (n : ℝ) ^ (1 / 300 : ℝ) := by rw [← Real.rpow_mul hn_pos.le]; norm_num
  have hg_ge_quarter : (n : ℝ) ^ (1 / 4 : ℝ) ≤ g n := by
    have h1 : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 300 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hn_pos]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    have h2 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (1 / 3 : ℝ) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hlog_pos _)]
      exact (mul_le_mul_of_nonneg_left hlog_rpow (by positivity)).trans h1
    have h3 : 1 ≤ Real.log (Real.log n) ^ (1 / 3 : ℝ) := Real.one_le_rpow hloglog_ge1 (by norm_num)
    dsimp only [g]
    exact h2.trans (le_mul_of_one_le_right (by positivity) h3)
  have hn_quarter_ge2 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    have : (16 : ℝ) ≤ n := by exact_mod_cast (by omega : 16 ≤ n)
    calc (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) this (by norm_num)
  let K : ℕ := ⌈g n⌉₊
  have hK_ge : g n ≤ K := Nat.le_ceil (g n)
  have hK_le : (K : ℝ) ≤ g n + 1 := (Nat.ceil_lt_add_one hg_pos.le).le
  have hK_ge2 : 2 ≤ K := by
    have : (2 : ℝ) ≤ K := hn_quarter_ge2.trans (hg_ge_quarter.trans hK_ge)
    exact_mod_cast this
  let m : ℕ := n / (K + 1)
  have hm_le_real : (m : ℝ) ≤ (n : ℝ) / (g n) := by
    have h1 : ((n / (K + 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((K + 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h2 : (n : ℝ) / ((K + 1 : ℕ) : ℝ) ≤ (n : ℝ) / g n := by
      refine div_le_div_of_nonneg_left hn_pos.le hg_pos ?_
      push_cast; linarith
    exact h1.trans h2
  let y' : ℕ := ⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊
  have hy'_ge : (n : ℝ) ^ (1 / 4 : ℝ) ≤ y' := Nat.le_ceil _
  have hy'_le : (y' : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hy'_ge2 : 2 ≤ y' := by
    have : (2 : ℝ) ≤ y' := hn_quarter_ge2.trans hy'_ge
    exact_mod_cast this
  have hy'_log : Real.log n / 4 ≤ Real.log y' := by
    have h1 : Real.log ((n : ℝ) ^ (1 / 4 : ℝ)) ≤ Real.log y' :=
      Real.log_le_log (by positivity) hy'_ge
    rw [Real.log_rpow hn_pos] at h1
    linarith
  have hm_lt_y3 : m < y' ^ 3 := by
    have hm_r : (m : ℝ) < (n : ℝ) ^ (3 / 4 : ℝ) := by
      have h1 : (n : ℝ) / g n ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
        rw [div_le_iff₀ hg_pos]
        have hmul : (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = n := by
          rw [← Real.rpow_add hn_pos]; norm_num
        exact hmul.symm.le.trans (mul_le_mul_of_nonneg_left hg_ge_quarter (by positivity))
      have h2 : (m : ℝ) ≤ (n : ℝ) / ((K : ℝ) + 1) := by
        have := Nat.cast_div_le (m := n) (n := K + 1) (α := ℝ)
        simpa using this
      have h3 : (n : ℝ) / ((K : ℝ) + 1) < (n : ℝ) / g n :=
        div_lt_div_of_pos_left hn_pos hg_pos (by linarith)
      linarith
    have hy3 : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (y' : ℝ) ^ 3 := by
      calc (n : ℝ) ^ (3 / 4 : ℝ)
        _ = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (3 : ℕ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
        _ ≤ (y' : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (by positivity) hy'_ge 3
    have : (m : ℝ) < ((y' ^ 3 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨ℬ, hf_nat, hℬ_nat⟩ := f_le_cover_params (y' := y') (by omega : 2 ≤ n) hK_ge2
  let U : Finset ℕ := (Finset.Icc 1 m).filter (fun x ↦ ∀ p ∈ Nat.primesLE y', ¬ p ∣ n → ¬ p ∣ x)
  have hB_real : (ℬ.card : ℝ) ≤ 2 * (m : ℝ) * (U.card : ℝ) / n + 1 := by
    have h1 : (n : ℝ) * (ℬ.card : ℝ) ≤ 2 * (m : ℝ) * (U.card : ℝ) + n := by
      exact_mod_cast hℬ_nat
    have h2 : (ℬ.card : ℝ) ≤ (2 * (m : ℝ) * (U.card : ℝ) + n) / n := by
      rw [le_div_iff₀ hn_pos]; linarith
    have h3 : (2 * (m : ℝ) * (U.card : ℝ) + n) / n = 2 * (m : ℝ) * (U.card : ℝ) / n + 1 := by
      field_simp
    linarith
  have hU_card : (U.card : ℝ) ≤
      (m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)) +
      (200 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n :=
    uncovered_card_le hn64 hy'_ge2 hm_lt_y3 (Nat.div_le_self n (K + 1)) hy'_log
  have hrankin_small := alon_erdos_upper_rankin hn64 hlog_big hlog_rpow rfl hg_ge_quarter hm_le_real
  have hmain_term := alon_erdos_upper_main_term hn64 rfl hm_le_real
  have h1_le_gn : (1 : ℝ) ≤ g n := by linarith only [hn_quarter_ge2, hg_ge_quarter]
  have hf_cast : (Erdos360.f n : ℝ) ≤ (K : ℝ) + (y' : ℝ) + (ℬ.card : ℝ) := by exact_mod_cast hf_nat
  have hBU : 2 * (m : ℝ) * (U.card : ℝ) / n ≤ g n + (400 * Real.exp 8) * g n := by
    have h1 : 2 * (m : ℝ) * (U.card : ℝ) / n ≤
        2 * (m : ℝ) * ((m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)) +
          (200 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n) / n := by
      gcongr
    have h2 : 2 * (m : ℝ) * ((m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ)) +
          (200 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n) / n =
        2 * (m : ℝ) * ((m : ℝ) ^ (1 / 2 : ℝ) * Real.exp (12 * (Real.log n) ^ (3 / 4 : ℝ))) / n +
        2 * (m : ℝ) * ((200 * Real.exp 8) * (m : ℝ) * Real.log (Real.log n) / Real.log n) / n := by
      ring
    linarith only [h1, h2, hrankin_small, hmain_term]
  have hf_real : (Erdos360.f n : ℝ) ≤ (6 + 400 * Real.exp 8) * g n := by
    linarith only [hf_cast, hK_le, hy'_le, hB_real, hBU, hg_ge_quarter, h1_le_gn]
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hg_pos.le]
  exact hf_real

/- Section 5: Lower bound — full subset-sum coverage in `ZMod p` -/

open scoped Pointwise

lemma double_count_zmod {p : ℕ} [NeZero p] (S : Finset (ZMod p)) (d : ℕ) (hd : d ≤ S.card) :
    (S.card - d) *
      (Finset.univ.filter (fun x : ZMod p ↦ ((S.image (· + x)) \ S).card ≤ d)).card ≤
      S.card * S.card := by
  classical
  let G := Finset.univ.filter (fun x : ZMod p ↦ ((S.image (· + x)) \ S).card ≤ d)
  have hterm : ∀ x : ZMod p,
      ((S.image (· + x)) \ S).card = (S.filter (fun y ↦ y + x ∉ S)).card := by
    intro x
    have heq : (S.image (· + x)) \ S = (S.filter (fun y ↦ y + x ∉ S)).image (· + x) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨⟨y, hyS, rfl⟩, hnot⟩
        exact ⟨y, ⟨hyS, hnot⟩, rfl⟩
      · rintro ⟨y, ⟨hyS, hnot⟩, rfl⟩
        exact ⟨⟨y, hyS, rfl⟩, hnot⟩
    rw [heq, Finset.card_image_of_injective _ (add_left_injective x)]
  have hsum_eq : ∑ x : ZMod p, ((S.image (· + x)) \ S).card = S.card * (p - S.card) := by
    simp_rw [hterm, Finset.card_filter]
    rw [Finset.sum_comm]
    have hinner : ∀ y ∈ S,
        ∑ x : ZMod p, (if y + x ∉ S then 1 else 0) = p - S.card := by
      intro y _
      rw [← Finset.card_filter]
      have hbij : (Finset.univ.filter (fun x : ZMod p ↦ y + x ∉ S)).card =
          (Finset.univ \ S).card := by
        refine Finset.card_bij (fun x _ ↦ y + x) ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
        · intro x₁ _ x₂ _ heq
          exact add_left_cancel heq
        · intro z hz
          refine ⟨z - y, ?_, by ring⟩
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rwa [add_sub_cancel]
      rw [hbij, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, ZMod.card]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  have hsum_le : ∑ x : ZMod p, ((S.image (· + x)) \ S).card ≤
      G.card * d + (p - G.card) * S.card := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : ZMod p ↦ ((S.image (· + x)) \ S).card ≤ d)]
    have h1 : ∑ x ∈ G, ((S.image (· + x)) \ S).card ≤ G.card * d := by
      calc ∑ x ∈ G, ((S.image (· + x)) \ S).card
        _ ≤ ∑ _x ∈ G, d := Finset.sum_le_sum fun x hx ↦ (Finset.mem_filter.mp hx).2
        _ = G.card * d := by simp
    have h2 : ∑ x ∈ Finset.univ.filter (fun x : ZMod p ↦ ¬ ((S.image (· + x)) \ S).card ≤ d),
        ((S.image (· + x)) \ S).card ≤ (p - G.card) * S.card := by
      have hcard_not : (Finset.univ.filter
          (fun x : ZMod p ↦ ¬ ((S.image (· + x)) \ S).card ≤ d)).card = p - G.card := by
        have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p)))
          (fun x : ZMod p ↦ ((S.image (· + x)) \ S).card ≤ d)
        rw [Finset.card_univ, ZMod.card] at h
        change G.card + (Finset.univ.filter
          (fun x : ZMod p ↦ ¬ ((S.image (· + x)) \ S).card ≤ d)).card = p at h
        omega
      calc ∑ x ∈ Finset.univ.filter (fun x : ZMod p ↦ ¬ ((S.image (· + x)) \ S).card ≤ d),
            ((S.image (· + x)) \ S).card
        _ ≤ ∑ _x ∈ Finset.univ.filter (fun x : ZMod p ↦ ¬ ((S.image (· + x)) \ S).card ≤ d),
            S.card := Finset.sum_le_sum fun x _ ↦
              (Finset.card_le_card Finset.sdiff_subset).trans Finset.card_image_le
        _ = (p - G.card) * S.card := by rw [Finset.sum_const, smul_eq_mul, hcard_not]
    exact Nat.add_le_add h1 h2
  have hS_le : S.card ≤ p := by
    calc S.card ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by rw [Finset.card_univ, ZMod.card]
  have hG_le : G.card ≤ p := by
    calc G.card ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by rw [Finset.card_univ, ZMod.card]
  have hineq : S.card * (p - S.card) ≤ G.card * d + (p - G.card) * S.card := hsum_eq ▸ hsum_le
  change (S.card - d) * G.card ≤ S.card * S.card
  zify [hS_le, hG_le, hd] at hineq ⊢
  nlinarith

lemma stable_period_add {p : ℕ} [NeZero p] (S : Finset (ZMod p)) (x y : ZMod p) :
    ((S.image (· + (x + y))) \ S).card ≤
      ((S.image (· + x)) \ S).card + ((S.image (· + y)) \ S).card := by
  classical
  have hsub : (S.image (· + (x + y))) \ S ⊆
      ((S.image (· + (x + y))) \ (S.image (· + y))) ∪ ((S.image (· + y)) \ S) := by
    intro z hz
    simp only [Finset.mem_sdiff, Finset.mem_union] at hz ⊢
    by_cases hzy : z ∈ S.image (· + y)
    · exact Or.inr ⟨hzy, hz.2⟩
    · exact Or.inl ⟨hz.1, hzy⟩
  have hshift : (S.image (· + (x + y))) \ (S.image (· + y)) =
      ((S.image (· + x)) \ S).image (· + y) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, haS, rfl⟩, hnot⟩
      refine ⟨a + x, ⟨⟨a, haS, rfl⟩, ?_⟩, by ring⟩
      intro haxS
      exact hnot ⟨a + x, haxS, by ring⟩
    · rintro ⟨w, ⟨⟨a, haS, rfl⟩, hnot⟩, rfl⟩
      refine ⟨⟨a, haS, by ring⟩, ?_⟩
      rintro ⟨b, hbS, hbeq⟩
      have : b = a + x := by
        have h1 : b + y = (a + x) + y := by simpa [add_assoc] using hbeq
        exact add_right_cancel h1
      exact hnot (this ▸ hbS)
  calc ((S.image (· + (x + y))) \ S).card
    _ ≤ (((S.image (· + (x + y))) \ (S.image (· + y))) ∪ ((S.image (· + y)) \ S)).card :=
        Finset.card_le_card hsub
    _ ≤ ((S.image (· + (x + y))) \ (S.image (· + y))).card + ((S.image (· + y)) \ S).card :=
        Finset.card_union_le _ _
    _ = ((S.image (· + x)) \ S).card + ((S.image (· + y)) \ S).card := by
        rw [hshift, Finset.card_image_of_injective _ (add_left_injective y)]

noncomputable def iterSum {p : ℕ} : ℕ → Finset (ZMod p) → Finset (ZMod p)
  | 0, _ => {0}
  | k + 1, U => by classical exact iterSum k U + U

lemma iterSum_nonempty {p : ℕ} {U : Finset (ZMod p)} (hU : U.Nonempty) (k : ℕ) :
    (iterSum k U).Nonempty := by
  classical
  induction k with
  | zero => simp [iterSum]
  | succ k ih =>
    simpa [iterSum] using ih.add hU

lemma iterSum_one {p : ℕ} (U : Finset (ZMod p)) : iterSum 1 U = U := by
  classical
  simp [iterSum, Finset.singleton_add]

lemma iterSum_card_ge {p : ℕ} (hp : p.Prime) {U : Finset (ZMod p)} (hU : U.Nonempty) :
    ∀ k : ℕ, 1 ≤ k → min p (k * U.card - k + 1) ≤ (iterSum k U).card := by
  classical
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [iterSum_one]
      have h1 : 1 ≤ U.card := Finset.card_pos.mpr hU
      have : 1 * U.card - 1 + 1 = U.card := by omega
      rw [this]
      exact min_le_right _ _
    · have hk1 : 1 ≤ k := by omega
      have hih := ih hk1
      have hcd : min p ((iterSum k U).card + U.card - 1) ≤ (iterSum (k + 1) U).card := by
        simpa [iterSum] using ZMod.cauchy_davenport hp (iterSum_nonempty hU k) hU
      have hU1 : 1 ≤ U.card := Finset.card_pos.mpr hU
      have hmin : min p ((k + 1) * U.card - (k + 1) + 1) ≤
          min p ((iterSum k U).card + U.card - 1) := by
        rcases le_or_gt p (iterSum k U).card with hp_le | hp_gt
        · have hge : p ≤ (iterSum k U).card + U.card - 1 := by omega
          rw [min_eq_left hge]
          exact min_le_left _ _
        · have hstep : k * U.card - k + 1 ≤ (iterSum k U).card := by
            rcases min_le_iff.mp hih with h1 | h2
            · omega
            · exact h2
          have hadd : (k + 1) * U.card - (k + 1) + 1 ≤ (iterSum k U).card + U.card - 1 := by
            have hku : k ≤ k * U.card := Nat.le_mul_of_pos_right k hU1
            have hk1u : k + 1 ≤ (k + 1) * U.card := Nat.le_mul_of_pos_right (k + 1) hU1
            have hne : 1 ≤ (iterSum k U).card := Finset.card_pos.mpr (iterSum_nonempty hU k)
            have hexp : (k + 1) * U.card = k * U.card + U.card := by rw [Nat.add_mul, one_mul]
            omega
          exact min_le_min_left p hadd
      exact hmin.trans hcd

lemma iterSum_stable_period {p : ℕ} [NeZero p] (S U : Finset (ZMod p)) (d : ℕ)
    (hU : ∀ x ∈ U, ((S.image (· + x)) \ S).card ≤ d) :
    ∀ k : ℕ, ∀ z ∈ iterSum k U, ((S.image (· + z)) \ S).card ≤ k * d := by
  classical
  intro k
  induction k with
  | zero =>
    intro z hz
    simp only [iterSum, Finset.mem_singleton] at hz
    subst hz
    simp
  | succ k ih =>
    intro z hz
    simp only [iterSum] at hz
    rcases Finset.mem_add.mp hz with ⟨a, ha, b, hb, rfl⟩
    have h1 := stable_period_add S a b
    have h2 := ih a ha
    have h3 := hU b hb
    have : (k + 1) * d = k * d + d := by ring
    omega

lemma small_expansion_card_le {p : ℕ} [NeZero p] (hp : p.Prime) (S : Finset (ZMod p)) (d : ℕ)
    (hS : 2 * S.card < p) (hd1 : 1 ≤ d) (hd2 : 2 * d ≤ S.card) :
    (Finset.univ.filter (fun x : ZMod p ↦ ((S.image (· + x)) \ S).card ≤ d)).card ≤ 8 * d := by
  classical
  let U := Finset.univ.filter (fun x : ZMod p ↦ ((S.image (· + x)) \ S).card ≤ d)
  have hU_ne : U.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have h0 : S.image (· + (0 : ZMod p)) = S := by ext z; simp
    rw [h0, Finset.sdiff_self]
    simp
  let k : ℕ := S.card / (2 * d)
  have hk1 : 1 ≤ k := Nat.div_pos hd2 (by omega)
  have h2kd_le : 2 * (k * d) ≤ S.card := by
    have := Nat.mul_div_le S.card (2 * d)
    dsimp only [k]; nlinarith
  have hS_lt_4kd : S.card < 4 * k * d := by
    have h1 := Nat.div_add_mod S.card (2 * d)
    have h2 := Nat.mod_lt S.card (by omega : 0 < 2 * d)
    dsimp only [k] at hk1 ⊢
    nlinarith
  let Gkd := Finset.univ.filter (fun x : ZMod p ↦ ((S.image (· + x)) \ S).card ≤ k * d)
  have hGkd_le : Gkd.card ≤ 2 * S.card := by
    have hkd_le : k * d ≤ S.card := by omega
    have hdc : (S.card - k * d) * Gkd.card ≤ S.card * S.card := double_count_zmod S (k * d) hkd_le
    have hhalf : S.card ≤ 2 * (S.card - k * d) := by omega
    have hmul : S.card * Gkd.card ≤ 2 * S.card * S.card := by nlinarith
    have hSpos : 0 < S.card := by omega
    nlinarith
  have hsub : iterSum k U ⊆ Gkd := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact iterSum_stable_period S U d (fun x hx ↦ (Finset.mem_filter.mp hx).2) k z hz
  have hcd := iterSum_card_ge hp hU_ne k hk1
  have hbound : min p (k * U.card - k + 1) ≤ 2 * S.card :=
    hcd.trans ((Finset.card_le_card hsub).trans hGkd_le)
  have hlt : k * U.card - k + 1 ≤ 2 * S.card := by
    rcases min_le_iff.mp hbound with h1 | h2
    · omega
    · exact h2
  have hU1 : 1 ≤ U.card := Finset.card_pos.mpr hU_ne
  have hmul_lt : k * (U.card - 1) < 2 * S.card := by
    have : k * U.card - k = k * (U.card - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    omega
  have hS_pos : 0 < S.card := by omega
  have hstep : S.card * (U.card - 1) < 8 * d * S.card := by
    calc S.card * (U.card - 1)
      _ ≤ (4 * k * d) * (U.card - 1) := Nat.mul_le_mul_right _ hS_lt_4kd.le
      _ = 4 * d * (k * (U.card - 1)) := by ring
      _ < 4 * d * (2 * S.card) := Nat.mul_lt_mul_of_pos_left hmul_lt (by omega)
      _ = 8 * d * S.card := by ring
  have hU_sub : U.card - 1 < 8 * d := Nat.lt_of_mul_lt_mul_right (by rw [mul_comm]; exact hstep)
  change U.card ≤ 8 * d
  omega

lemma compl_expansion_eq {p : ℕ} [NeZero p] (S : Finset (ZMod p)) (x : ZMod p) :
    ((S.image (· + x)) \ S).card =
      (((Finset.univ \ S).image (· + x)) \ (Finset.univ \ S)).card := by
  classical
  let T := Finset.univ \ S
  have h1 : ((S.image (· + x)) \ S).card = (S \ (S.image (· + x))).card := by
    have hcard_img : (S.image (· + x)).card = S.card :=
      Finset.card_image_of_injective _ (add_left_injective x)
    have ha := Finset.card_sdiff_add_card_inter (S.image (· + x)) S
    have hb := Finset.card_sdiff_add_card_inter S (S.image (· + x))
    rw [Finset.inter_comm] at hb
    omega
  have h2 : (T.image (· + x)) \ T = S \ (S.image (· + x)) := by
    ext z
    simp only [T, Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and, not_not]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, haxS⟩
      refine ⟨haxS, ?_⟩
      rintro ⟨b, hbS, hbeq⟩
      exact ha (add_right_cancel hbeq ▸ hbS)
    · rintro ⟨hzS, hnot⟩
      refine ⟨⟨z - x, ?_, by ring⟩, hzS⟩
      intro hzxS
      exact hnot ⟨z - x, hzxS, by ring⟩
  rw [h1, h2]

lemma four_pow_mul_sq_lt_nine_pow : ∀ r : ℕ, 10 ≤ r → 4 ^ r * (r + 1) ^ 2 < 9 ^ r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsq : (k + 2) ^ 2 ≤ 2 * (k + 1) ^ 2 := by nlinarith
    calc 4 ^ (k + 1) * (k + 2) ^ 2
      _ = 4 * 4 ^ k * (k + 2) ^ 2 := by ring
      _ ≤ 4 * 4 ^ k * (2 * (k + 1) ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = 8 * (4 ^ k * (k + 1) ^ 2) := by ring
      _ < 8 * 9 ^ k := Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ ≤ 9 * 9 ^ k := Nat.mul_le_mul_right _ (by omega)
      _ = 9 ^ (k + 1) := by ring

lemma sq_lt_four_pow : ∀ r : ℕ, 10 ≤ r → (r + 1) ^ 2 < 4 ^ r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsq : (k + 2) ^ 2 ≤ 4 * (k + 1) ^ 2 := by nlinarith
    calc (k + 2) ^ 2 ≤ 4 * (k + 1) ^ 2 := hsq
      _ < 4 * 4 ^ k := Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ = 4 ^ (k + 1) := by ring

lemma subsetSum_zmod_eq_univ {p : ℕ} [NeZero p] (hp : p.Prime) (hp100 : 100 ≤ p)
    (B : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ B) (hB : 20 * (Nat.sqrt p + 1) ≤ B.card) :
    B.subsetSum = Finset.univ := by
  classical
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  let r : ℕ := Nat.sqrt p
  have hr10 : 10 ≤ r := Nat.le_sqrt.mpr (by omega)
  have hp_lt_sq : p < (r + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt p
    dsimp only [r]; nlinarith
  let m : ℕ := B.card / 2
  have hm_ge : 10 * (r + 1) ≤ m := by dsimp only [m, r]; omega
  let k₀ : ℕ := (m - 1) / 8
  have hk0_ge : r + 1 ≤ k₀ := by dsimp only [k₀]; omega
  have h8k0_lt : 8 * k₀ < m := by dsimp only [k₀]; omega
  let step : Finset (ZMod p) × Finset (ZMod p) → Finset (ZMod p) × Finset (ZMod p) := fun SR ↦
    if h : SR.2.Nonempty then
      let x := Classical.choose
        (Finset.exists_max_image SR.2 (fun x ↦ ((SR.1.image (· + x)) \ SR.1).card) h)
      (SR.1 ∪ SR.1.image (· + x), SR.2.erase x)
    else SR
  let seq : ℕ → Finset (ZMod p) × Finset (ZMod p) := fun j ↦ step^[j] ({0}, B)
  have hinv : ∀ j : ℕ, (seq j).2 ⊆ B ∧ B.card ≤ (seq j).2.card + j ∧
      (seq j).1 ⊆ (B \ (seq j).2).subsetSum ∧ (seq j).1.Nonempty := by
    intro j
    induction j with
    | zero =>
      refine ⟨Finset.Subset.refl B, by simp [seq], ?_, ⟨0, by simp [seq]⟩⟩
      simp [seq]
    | succ j ih =>
      rcases ih with ⟨hRsub, hRcard, hSsub, hSne⟩
      have hseq : seq (j + 1) = step (seq j) := Function.iterate_succ_apply' step j ({0}, B)
      rw [hseq]
      dsimp only [step]
      split_ifs with hne
      · set hmax := Finset.exists_max_image (seq j).2
          (fun x ↦ (((seq j).1.image (· + x)) \ (seq j).1).card) hne
        set x := Classical.choose hmax
        have hx_spec := Classical.choose_spec hmax
        have hxR : x ∈ (seq j).2 := hx_spec.1
        have hR'sub : (seq j).2.erase x ⊆ B := (Finset.erase_subset x _).trans hRsub
        have hR'card : B.card ≤ ((seq j).2.erase x).card + (j + 1) := by
          have := Finset.card_erase_add_one hxR
          omega
        have hS'sub : (seq j).1 ∪ (seq j).1.image (· + x) ⊆
            (B \ (seq j).2.erase x).subsetSum := by
          have hsub_ins : insert x (B \ (seq j).2) ⊆ B \ (seq j).2.erase x := by
            intro y hy
            rcases Finset.mem_insert.mp hy with rfl | hy'
            · exact Finset.mem_sdiff.mpr ⟨hRsub hxR, Finset.notMem_erase x _⟩
            · exact Finset.mem_sdiff.mpr
                ⟨(Finset.mem_sdiff.mp hy').1, fun h ↦ (Finset.mem_sdiff.mp hy').2 (Finset.mem_of_mem_erase h)⟩
          have hxnot : x ∉ B \ (seq j).2 := fun h ↦ (Finset.mem_sdiff.mp h).2 hxR
          refine Finset.union_subset ?_ ?_
          · exact hSsub.trans (Finset.subsetSum_mono ((Finset.subset_insert x _).trans hsub_ins))
          · intro z hz
            rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
            have ha_sum := hSsub ha
            rcases Finset.mem_subsetSum_iff.mp ha_sum with ⟨C, hC, rfl⟩
            refine Finset.mem_subsetSum_iff.mpr ⟨insert x C, ?_, ?_⟩
            · exact (Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_self x _,
                hC.trans (Finset.subset_insert x _)⟩).trans hsub_ins
            · have hxC : x ∉ C := fun h ↦ hxnot (hC h)
              rw [Finset.sum_insert hxC, add_comm]
        exact ⟨hR'sub, hR'card, hS'sub, hSne.mono Finset.subset_union_left⟩
      · exact ⟨hRsub, by omega, hSsub, hSne⟩
  have hmono : ∀ j : ℕ, (seq j).1.card ≤ (seq (j + 1)).1.card := by
    intro j
    have hseq : seq (j + 1) = step (seq j) := Function.iterate_succ_apply' step j ({0}, B)
    rw [hseq]; dsimp only [step]
    split_ifs
    · exact Finset.card_le_card Finset.subset_union_left
    · exact le_rfl
  have hmono_le : ∀ {a b : ℕ}, a ≤ b → (seq a).1.card ≤ (seq b).1.card := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono _)
  have hstep_max : ∀ j : ℕ, j < m → ∀ x ∈ (seq j).2,
      (seq j).1.card + (((seq j).1.image (· + x)) \ (seq j).1).card ≤ (seq (j + 1)).1.card := by
    intro j hj x hx
    have hRcard : m ≤ (seq j).2.card := by have := (hinv j).2.1; omega
    have hne : (seq j).2.Nonempty := Finset.card_pos.mp (by omega)
    have hseq : seq (j + 1) = step (seq j) := Function.iterate_succ_apply' step j ({0}, B)
    rw [hseq]; dsimp only [step]
    rw [dif_pos hne]
    set hmax := Finset.exists_max_image (seq j).2
      (fun y ↦ (((seq j).1.image (· + y)) \ (seq j).1).card) hne
    set y := Classical.choose hmax
    have hy_spec := Classical.choose_spec hmax
    have hcard_union : ((seq j).1 ∪ (seq j).1.image (· + y)).card =
        (seq j).1.card + (((seq j).1.image (· + y)) \ (seq j).1).card := by
      rw [← Finset.union_sdiff_self_eq_union, Finset.card_union_of_disjoint Finset.disjoint_sdiff]
    rw [hcard_union]
    exact Nat.add_le_add_left (hy_spec.2 x hx) _
  -- Step growth:
  have hgrow_one : ∀ j : ℕ, j < m → (seq j).1.card < p →
      (seq j).1.card + 1 ≤ (seq (j + 1)).1.card := by
    intro j hj hlt
    have hRcard : m ≤ (seq j).2.card := by have := (hinv j).2.1; omega
    have hne : (seq j).2.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hne
    have hx0 : x ≠ 0 := fun h ↦ h0 (h ▸ (hinv j).1 hx)
    have hexp_pos : 1 ≤ (((seq j).1.image (· + x)) \ (seq j).1).card := by
      by_contra hzero
      have hcz : (((seq j).1.image (· + x)) \ (seq j).1).card = 0 := by omega
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hcz
      have hcl : ∀ a ∈ (seq j).1, a + x ∈ (seq j).1 := fun a ha ↦
        hcz (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      obtain ⟨a₀, ha₀⟩ := (hinv j).2.2.2
      have hmulti : ∀ k : ℕ, a₀ + (k : ZMod p) * x ∈ (seq j).1 := by
        intro k
        induction k with
        | zero => simpa using ha₀
        | succ k ih =>
          have : a₀ + ((k + 1 : ℕ) : ZMod p) * x = (a₀ + (k : ZMod p) * x) + x := by
            push_cast; ring
          rw [this]
          exact hcl _ ih
      have h_all : (seq j).1 = Finset.univ := by
        ext z
        simp only [Finset.mem_univ, iff_true]
        have : Fact p.Prime := ⟨hp⟩
        let w : ZMod p := (z - a₀) * x⁻¹
        have hw : a₀ + ((w.val : ℕ) : ZMod p) * x = z := by
          rw [ZMod.natCast_zmod_val]
          dsimp only [w]
          rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one, add_sub_cancel]
        exact hw ▸ hmulti w.val
      have : (seq j).1.card = p := by rw [h_all, Finset.card_univ, ZMod.card]
      omega
    exact (Nat.add_le_add_left hexp_pos _).trans (hstep_max j hj x hx)
  have hgrow_d : ∀ j d : ℕ, j < m → 1 ≤ d → 8 * d < m →
      2 * d ≤ min (seq j).1.card (p - (seq j).1.card) →
      (seq j).1.card + d + 1 ≤ (seq (j + 1)).1.card := by
    intro j d hj hd1 h8d h2d
    have hRcard : m ≤ (seq j).2.card := by have := (hinv j).2.1; omega
    have hS_le_p : (seq j).1.card ≤ p := by
      calc (seq j).1.card ≤ (Finset.univ : Finset (ZMod p)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = p := by rw [Finset.card_univ, ZMod.card]
    let Gd := Finset.univ.filter (fun x : ZMod p ↦ (((seq j).1.image (· + x)) \ (seq j).1).card ≤ d)
    have hGd_le : Gd.card ≤ 8 * d := by
      rcases lt_or_ge (2 * (seq j).1.card) p with hlt | hge
      · exact small_expansion_card_le hp (seq j).1 d hlt hd1 (h2d.trans (min_le_left _ _))
      · let T := Finset.univ \ (seq j).1
        have hTcard : T.card = p - (seq j).1.card := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card]
        have hTlt : 2 * T.card < p := by
          rcases hp_odd with ⟨q, hq⟩; omega
        have hTeq : Gd = Finset.univ.filter (fun x : ZMod p ↦ ((T.image (· + x)) \ T).card ≤ d) := by
          ext x
          simp only [Gd, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [compl_expansion_eq (seq j).1 x]
        rw [hTeq]
        exact small_expansion_card_le hp T d hTlt hd1 (by rw [hTcard]; exact h2d.trans (min_le_right _ _))
    have hex : ∃ x ∈ (seq j).2, x ∉ Gd := by
      by_contra hall
      push Not at hall
      have : (seq j).2.card ≤ Gd.card := Finset.card_le_card hall
      omega
    obtain ⟨x, hxR, hxnot⟩ := hex
    have hgt : d < (((seq j).1.image (· + x)) \ (seq j).1).card := by
      by_contra hle
      push Not at hle
      exact hxnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
    have := hstep_max j hj x hxR
    omega
  -- Five sequential phases
  have hphase1 : 2 ≤ (seq 1).1.card := by
    have hs0 : (seq 0).1.card = 1 := by simp [seq]
    have h1 := hgrow_one 0 (by omega) (by omega)
    simpa only [zero_add, hs0] using h1
  let j₂ := 1 + 2 * r
  have hphase2 : 2 * k₀ ≤ (seq j₂).1.card ∨ p / 2 < (seq j₂).1.card := by
    by_contra hcon
    push Not at hcon
    have h32 : ∀ i ≤ 2 * r, 3 ^ i * 2 ≤ 2 ^ i * (seq (1 + i)).1.card := by
      intro i hi
      induction i with
      | zero => simpa using hphase1
      | succ i ih =>
        have hprev := ih (by omega)
        have hle_j2 : (seq (1 + i)).1.card ≤ (seq j₂).1.card := hmono_le (by dsimp only [j₂]; omega)
        have hge2 : 2 ≤ (seq (1 + i)).1.card := hphase1.trans (hmono_le (by omega))
        let d := (seq (1 + i)).1.card / 2
        have hd1 : 1 ≤ d := by omega
        have h8d : 8 * d < m := by omega
        have h2d : 2 * d ≤ min (seq (1 + i)).1.card (p - (seq (1 + i)).1.card) := by
          apply le_min <;> omega
        have hstep := hgrow_d (1 + i) d (by omega) hd1 h8d h2d
        have h32step : 3 * (seq (1 + i)).1.card ≤ 2 * (seq (1 + (i + 1))).1.card := by
          rw [← add_assoc]; omega
        calc 3 ^ (i + 1) * 2 = 3 * (3 ^ i * 2) := by ring
          _ ≤ 3 * (2 ^ i * (seq (1 + i)).1.card) := Nat.mul_le_mul_left 3 hprev
          _ = 2 ^ i * (3 * (seq (1 + i)).1.card) := by ring
          _ ≤ 2 ^ i * (2 * (seq (1 + (i + 1))).1.card) := Nat.mul_le_mul_left _ h32step
          _ = 2 ^ (i + 1) * (seq (1 + (i + 1))).1.card := by ring
    have hfinal : 3 ^ (2 * r) * 2 ≤ 2 ^ (2 * r) * (seq j₂).1.card := h32 (2 * r) le_rfl
    have hpow1 : 3 ^ (2 * r) = 9 ^ r := by rw [pow_mul]; norm_num
    have hpow2 : 2 ^ (2 * r) = 4 ^ r := by rw [pow_mul]; norm_num
    have h49 := four_pow_mul_sq_lt_nine_pow r hr10
    have hs_lt : (seq j₂).1.card < (r + 1) ^ 2 := by
      have : (seq j₂).1.card ≤ p := by
        calc (seq j₂).1.card ≤ (Finset.univ : Finset (ZMod p)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = p := by rw [Finset.card_univ, ZMod.card]
      omega
    rw [hpow1, hpow2] at hfinal
    have hmul_le : 4 ^ r * (seq j₂).1.card ≤ 4 ^ r * (r + 1) ^ 2 := Nat.mul_le_mul_left _ hs_lt.le
    omega
  let j₃ := j₂ + (r + 1)
  have hphase3 : p - (seq j₃).1.card < 2 * k₀ := by
    by_contra hcon
    push Not at hcon
    have hj2_ge : 2 * k₀ ≤ (seq j₂).1.card := by
      rcases hphase2 with h | h
      · exact h
      · have hle : (seq j₂).1.card ≤ (seq j₃).1.card := hmono_le (by omega)
        omega
    have hlin : ∀ i ≤ r + 1, i * (k₀ + 1) ≤ (seq (j₂ + i)).1.card := by
      intro i hi
      induction i with
      | zero => simp
      | succ i ih =>
        have hprev := ih (by omega)
        have hge : 2 * k₀ ≤ (seq (j₂ + i)).1.card := hj2_ge.trans (hmono_le (by omega))
        have hle : (seq (j₂ + i)).1.card ≤ (seq j₃).1.card := hmono_le (by dsimp only [j₃]; omega)
        have hstep := hgrow_d (j₂ + i) k₀ (by dsimp only [j₂]; omega) (by omega) h8k0_lt
          (le_min hge (by omega))
        have hmul : (i + 1) * (k₀ + 1) = i * (k₀ + 1) + k₀ + 1 := by ring
        rw [← add_assoc]; omega
    have hfinal : (r + 1) * (k₀ + 1) ≤ (seq j₃).1.card := hlin (r + 1) le_rfl
    have hS_le_p : (seq j₃).1.card ≤ p := by
      calc (seq j₃).1.card ≤ (Finset.univ : Finset (ZMod p)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = p := by rw [Finset.card_univ, ZMod.card]
    have hsq : (r + 1) ^ 2 ≤ (r + 1) * (k₀ + 1) := by nlinarith
    omega
  let j₄ := j₃ + 2 * r
  have hphase4 : p - (seq j₄).1.card ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hhalf : ∀ i ≤ 2 * r, 2 ^ i * (p - (seq (j₃ + i)).1.card) ≤ p - (seq j₃).1.card := by
      intro i hi
      induction i with
      | zero => simp
      | succ i ih =>
        have hprev := ih (by omega)
        have hge2 : 2 ≤ p - (seq (j₃ + i)).1.card := by
          have := hmono_le (show j₃ + i ≤ j₄ by dsimp only [j₄]; omega)
          omega
        have hlt2k : p - (seq (j₃ + i)).1.card < 2 * k₀ := by
          have := hmono_le (show j₃ ≤ j₃ + i by omega)
          omega
        let d := (p - (seq (j₃ + i)).1.card) / 2
        have hd1 : 1 ≤ d := by omega
        have h8d : 8 * d < m := by omega
        have h2d : 2 * d ≤ min (seq (j₃ + i)).1.card (p - (seq (j₃ + i)).1.card) := by
          have hS_big : p / 2 < (seq (j₃ + i)).1.card := by
            have := hmono_le (show j₃ ≤ j₃ + i by omega)
            rcases hphase2 with h2 | h2
            · have := hmono_le (show j₂ ≤ j₃ + i by dsimp only [j₃]; omega)
              omega
            · have := hmono_le (show j₂ ≤ j₃ + i by dsimp only [j₃]; omega)
              omega
          apply le_min <;> omega
        have hstep := hgrow_d (j₃ + i) d (by dsimp only [j₃, j₂]; omega) hd1 h8d h2d
        have h2mul : 2 * (p - (seq (j₃ + (i + 1))).1.card) ≤ p - (seq (j₃ + i)).1.card := by
          rw [← add_assoc]; omega
        calc 2 ^ (i + 1) * (p - (seq (j₃ + (i + 1))).1.card)
          _ = 2 ^ i * (2 * (p - (seq (j₃ + (i + 1))).1.card)) := by ring
          _ ≤ 2 ^ i * (p - (seq (j₃ + i)).1.card) := Nat.mul_le_mul_left _ h2mul
          _ ≤ p - (seq j₃).1.card := hprev
    have hfinal : 2 ^ (2 * r) * (p - (seq j₄).1.card) ≤ p - (seq j₃).1.card := hhalf (2 * r) le_rfl
    have hpow2 : 2 ^ (2 * r) = 4 ^ r := by rw [pow_mul]; norm_num
    rw [hpow2] at hfinal
    have hsq := sq_lt_four_pow r hr10
    have hge_pow : 4 ^ r ≤ 4 ^ r * (p - (seq j₄).1.card) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  let j₅ := j₄ + 1
  have hphase5 : (seq j₅).1.card = p := by
    have hS_le_p : (seq j₅).1.card ≤ p := by
      calc (seq j₅).1.card ≤ (Finset.univ : Finset (ZMod p)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = p := by rw [Finset.card_univ, ZMod.card]
    by_cases heq : (seq j₄).1.card = p
    · have hmono4 : (seq j₄).1.card ≤ (seq j₅).1.card := hmono j₄
      omega
    · have hlt : (seq j₄).1.card < p := by
        have h4le : (seq j₄).1.card ≤ p := by
          calc (seq j₄).1.card ≤ (Finset.univ : Finset (ZMod p)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = p := by rw [Finset.card_univ, ZMod.card]
        omega
      have hstep4 : (seq j₄).1.card + 1 ≤ (seq j₅).1.card :=
        hgrow_one j₄ (by dsimp only [j₄, j₃, j₂]; omega) hlt
      omega
  have hS_univ : (seq j₅).1 = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [ZMod.card]; exact hphase5)
  have hsub_B : (seq j₅).1 ⊆ B.subsetSum :=
    (hinv j₅).2.2.1.trans (Finset.subsetSum_mono Finset.sdiff_subset)
  exact Finset.eq_univ_iff_forall.mpr fun z ↦ hsub_B (hS_univ ▸ Finset.mem_univ z)

/- Section 6: From `ZMod p` coverage to intervals in `subsetSum` and the lower bound -/

lemma card_subsetSum_insert_ge {A : Finset ℕ} {q : ℕ} (hq : 0 < q) (hqA : q ∉ A)
    (hcov : ∀ r : ZMod q, ∃ x ∈ A.subsetSum, (x : ZMod q) = r) :
    A.subsetSum.card + q ≤ (insert q A).subsetSum.card := by
  classical
  have : NeZero q := ⟨hq.ne'⟩
  have hfiber_ne : ∀ r : ZMod q, (A.subsetSum.filter (fun x : ℕ ↦ (x : ZMod q) = r)).Nonempty := by
    intro r
    rcases hcov r with ⟨x, hx, rfl⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  let f : ZMod q → ℕ := fun r ↦
    (A.subsetSum.filter (fun x : ℕ ↦ (x : ZMod q) = r)).max' (hfiber_ne r) + q
  have hf_mod : ∀ r : ZMod q, (f r : ZMod q) = r := by
    intro r
    dsimp only [f]
    have hmem := Finset.max'_mem _ (hfiber_ne r)
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    exact (Finset.mem_filter.mp hmem).2
  have hf_inj : Function.Injective f := fun r₁ r₂ h ↦ by
    have := congrArg (fun x : ℕ ↦ (x : ZMod q)) h
    simpa only [hf_mod] using this
  have hf_new : Finset.univ.image f ⊆ (insert q A).subsetSum \ A.subsetSum := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨r, _, rfl⟩
    have hmax_mem := Finset.max'_mem _ (hfiber_ne r)
    have hmax_in : (A.subsetSum.filter (fun x : ℕ ↦ (x : ZMod q) = r)).max' (hfiber_ne r) ∈
        A.subsetSum := (Finset.mem_filter.mp hmax_mem).1
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · rcases Finset.mem_subsetSum_iff.mp hmax_in with ⟨C, hC, hCsum⟩
      refine Finset.mem_subsetSum_iff.mpr ⟨insert q C, Finset.insert_subset_insert q hC, ?_⟩
      have hqC : q ∉ C := fun h ↦ hqA (hC h)
      rw [Finset.sum_insert hqC, hCsum, add_comm]
    · intro hmemA
      have hmem_filt : f r ∈ A.subsetSum.filter (fun x : ℕ ↦ (x : ZMod q) = r) :=
        Finset.mem_filter.mpr ⟨hmemA, hf_mod r⟩
      have hle := Finset.le_max' _ _ hmem_filt
      dsimp only [f] at hle
      omega
  have hdisj : Disjoint A.subsetSum (Finset.univ.image f) :=
    Finset.disjoint_left.mpr fun x hxA hxf ↦ (Finset.mem_sdiff.mp (hf_new hxf)).2 hxA
  have hunion_sub : A.subsetSum ∪ Finset.univ.image f ⊆ (insert q A).subsetSum :=
    Finset.union_subset (Finset.subsetSum_mono (Finset.subset_insert q A))
      (hf_new.trans Finset.sdiff_subset)
  calc A.subsetSum.card + q
    _ = A.subsetSum.card + (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, ZMod.card]
    _ = (A.subsetSum ∪ Finset.univ.image f).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (insert q A).subsetSum.card := Finset.card_le_card hunion_sub

lemma card_subsetSum_union_ge {B₁ B₂ : Finset ℕ} (hdisj : Disjoint B₁ B₂)
    (hcov : ∀ q ∈ B₂, 0 < q ∧ ∀ r : ZMod q, ∃ x ∈ B₁.subsetSum, (x : ZMod q) = r) :
    1 + ∑ q ∈ B₂, q ≤ (B₁ ∪ B₂).subsetSum.card := by
  classical
  induction B₂ using Finset.induction_on with
  | empty =>
    simp only [Finset.union_empty, Finset.sum_empty, add_zero]
    exact Finset.card_pos.mpr Finset.subsetSum_nonempty
  | insert q B₂' hq_not ih =>
    have hdisj' : Disjoint B₁ B₂' := hdisj.mono_right (Finset.subset_insert q B₂')
    have hqB₁ : q ∉ B₁ := fun h ↦ Finset.disjoint_left.mp hdisj h (Finset.mem_insert_self q B₂')
    have hq_not_u : q ∉ B₁ ∪ B₂' := fun h ↦ by
      rcases Finset.mem_union.mp h with h1 | h2
      · exact hqB₁ h1
      · exact hq_not h2
    have hq_spec := hcov q (Finset.mem_insert_self q B₂')
    have hcov_u : ∀ r : ZMod q, ∃ x ∈ (B₁ ∪ B₂').subsetSum, (x : ZMod q) = r := by
      intro r
      rcases hq_spec.2 r with ⟨x, hx, hxr⟩
      exact ⟨x, Finset.subsetSum_mono Finset.subset_union_left hx, hxr⟩
    have hstep := card_subsetSum_insert_ge hq_spec.1 hq_not_u hcov_u
    have hih := ih hdisj' (fun r hr ↦ hcov r (Finset.mem_insert_of_mem hr))
    rw [Finset.union_insert, Finset.sum_insert hq_not]
    omega

lemma dense_sumset_interval {S₁ S₂ : Finset ℕ} {L₁ L₂ E₁ E₂ : ℕ}
    (hS₁ : S₁ ⊆ Finset.Icc 0 L₁) (hS₂ : S₂ ⊆ Finset.Icc 0 L₂)
    (hE₁ : L₁ + 1 - S₁.card ≤ E₁) (hE₂ : L₂ + 1 - S₂.card ≤ E₂)
    {m : ℕ} (hm_lo : E₁ + E₂ ≤ m) (hm_hi : m ≤ min L₁ L₂) :
    ∃ a ∈ S₁, ∃ b ∈ S₂, a + b = m := by
  classical
  have hmL₁ : m ≤ L₁ := hm_hi.trans (min_le_left _ _)
  have hmL₂ : m ≤ L₂ := hm_hi.trans (min_le_right _ _)
  let I := Finset.Icc 0 m
  let Bad₁ := I \ S₁
  let Bad₂ := I.filter (fun a ↦ m - a ∉ S₂)
  have hBad₁ : Bad₁.card ≤ E₁ := by
    have hsub : Bad₁ ⊆ Finset.Icc 0 L₁ \ S₁ :=
      Finset.sdiff_subset_sdiff (Finset.Icc_subset_Icc_right hmL₁) (Finset.Subset.refl _)
    have hcard := Finset.card_sdiff_of_subset hS₁
    simp only [Nat.card_Icc, tsub_zero] at hcard
    exact (Finset.card_le_card hsub).trans (by omega)
  have hBad₂ : Bad₂.card ≤ E₂ := by
    have hsub : Bad₂.image (fun a ↦ m - a) ⊆ Finset.Icc 0 L₂ \ S₂ := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      simp only [Bad₂, I, Finset.mem_filter, Finset.mem_Icc] at ha
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, ha.2⟩
    have hinj : Set.InjOn (fun a ↦ m - a) (Bad₂ : Set ℕ) := by
      intro a₁ ha₁ a₂ ha₂ heq
      dsimp only at heq
      simp only [Finset.mem_coe, Bad₂, I, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
      omega
    have hcard := Finset.card_sdiff_of_subset hS₂
    simp only [Nat.card_Icc, tsub_zero] at hcard
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans (by omega)
  have hnot_cov : ¬ I ⊆ Bad₁ ∪ Bad₂ := by
    intro hcov
    have h1 : I.card ≤ (Bad₁ ∪ Bad₂).card := Finset.card_le_card hcov
    have h2 : (Bad₁ ∪ Bad₂).card ≤ Bad₁.card + Bad₂.card := Finset.card_union_le _ _
    have h3 : I.card = m + 1 := by simp [I]
    omega
  obtain ⟨a, haI, haNot⟩ := Finset.not_subset.mp hnot_cov
  have ha₁ : a ∈ S₁ := by
    by_contra hnot
    exact haNot (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haI, hnot⟩))
  have ha₂ : m - a ∈ S₂ := by
    by_contra hnot
    exact haNot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haI, hnot⟩))
  have ham : a ≤ m := (Finset.mem_Icc.mp haI).2
  exact ⟨a, ha₁, m - a, ha₂, by omega⟩

lemma subsetSum_union_add {A B : Finset ℕ} (hdisj : Disjoint A B) {a b : ℕ}
    (ha : a ∈ A.subsetSum) (hb : b ∈ B.subsetSum) : a + b ∈ (A ∪ B).subsetSum := by
  classical
  rcases Finset.mem_subsetSum_iff.mp ha with ⟨C₁, hC₁, rfl⟩
  rcases Finset.mem_subsetSum_iff.mp hb with ⟨C₂, hC₂, rfl⟩
  have hCdisj : Disjoint C₁ C₂ := hdisj.mono hC₁ hC₂
  refine Finset.mem_subsetSum_iff.mpr ⟨C₁ ∪ C₂, Finset.union_subset_union hC₁ hC₂, ?_⟩
  exact Finset.sum_union hCdisj

lemma graham_extend {A B : Finset ℕ} {u v : ℕ} (huv : u ≤ v)
    (hIcc : Finset.Icc u v ⊆ A.subsetSum)
    (hdisj : Disjoint A B) (hB : ∀ x ∈ B, x ≤ v - u + 1) :
    Finset.Icc u (v + ∑ x ∈ B, x) ⊆ (A ∪ B).subsetSum := by
  classical
  induction B using Finset.induction_on with
  | empty => simpa using hIcc
  | insert x B' hx_not ih =>
    have hdisj' : Disjoint A B' := hdisj.mono_right (Finset.subset_insert x B')
    have hxA : x ∉ A := fun h ↦ Finset.disjoint_left.mp hdisj h (Finset.mem_insert_self x B')
    have hx_not_u : x ∉ A ∪ B' := fun h ↦ by
      rcases Finset.mem_union.mp h with h1 | h2
      · exact hxA h1
      · exact hx_not h2
    have hih := ih hdisj' (fun y hy ↦ hB y (Finset.mem_insert_of_mem hy))
    have hx_le : x ≤ v - u + 1 := hB x (Finset.mem_insert_self x B')
    intro z hz
    simp only [Finset.mem_Icc] at hz
    rw [Finset.union_insert]
    rw [Finset.sum_insert hx_not] at hz
    by_cases hle : z ≤ v + ∑ y ∈ B', y
    · exact Finset.subsetSum_mono (Finset.subset_insert x _)
        (hih (Finset.mem_Icc.mpr ⟨hz.1, hle⟩))
    · have hzx : z - x ∈ Finset.Icc u (v + ∑ y ∈ B', y) := by
        simp only [Finset.mem_Icc]; omega
      have hmem := hih hzx
      rcases Finset.mem_subsetSum_iff.mp hmem with ⟨C, hC, hCsum⟩
      refine Finset.mem_subsetSum_iff.mpr ⟨insert x C, Finset.insert_subset_insert x hC, ?_⟩
      have hxC : x ∉ C := fun h ↦ hx_not_u (hC h)
      rw [Finset.sum_insert hxC, hCsum]
      omega

lemma subsetSum_zmod_image_of_primes {B : Finset ℕ} {q : ℕ}
    (hq : q.Prime) (hq100 : 100 ≤ q)
    (hB_lt : ∀ a ∈ B, 0 < a ∧ a < q) (hB_card : 20 * (Nat.sqrt q + 1) ≤ B.card) :
    ∀ r : ZMod q, ∃ x ∈ B.subsetSum, (x : ZMod q) = r := by
  classical
  have : NeZero q := ⟨hq.ne_zero⟩
  let Bz : Finset (ZMod q) := B.image (fun x : ℕ ↦ (x : ZMod q))
  have hinj : Set.InjOn (fun x : ℕ ↦ (x : ZMod q)) (B : Set ℕ) := by
    intro a ha b hb heq
    have ha_lt := (hB_lt a ha).2
    have hb_lt := (hB_lt b hb).2
    have h1 := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hb_lt] at h1
    exact h1
  have hBz_card : Bz.card = B.card := Finset.card_image_of_injOn hinj
  have h0_not : (0 : ZMod q) ∉ Bz := by
    rintro h0
    rcases Finset.mem_image.mp h0 with ⟨a, ha, ha0⟩
    have ha_pos := (hB_lt a ha).1
    have ha_lt := (hB_lt a ha).2
    have h1 := congrArg ZMod.val ha0
    rw [ZMod.val_natCast_of_lt ha_lt, ZMod.val_zero] at h1
    omega
  have hBz_univ : Bz.subsetSum = Finset.univ :=
    subsetSum_zmod_eq_univ hq hq100 Bz h0_not (by omega)
  intro r
  have hr : r ∈ Bz.subsetSum := hBz_univ ▸ Finset.mem_univ r
  rcases Finset.mem_subsetSum_iff.mp hr with ⟨Cz, hCz, hCz_sum⟩
  let C : Finset ℕ := B.filter (fun a : ℕ ↦ (a : ZMod q) ∈ Cz)
  have hCsub : C ⊆ B := Finset.filter_subset _ _
  have hCimg : C.image (fun a : ℕ ↦ (a : ZMod q)) = Cz := by
    ext z
    simp only [C, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨_, haz⟩, rfl⟩; exact haz
    · intro hz
      rcases Finset.mem_image.mp (hCz hz) with ⟨a, haB, rfl⟩
      exact ⟨a, ⟨haB, hz⟩, rfl⟩
  refine ⟨∑ a ∈ C, a, Finset.mem_subsetSum_iff.mpr ⟨C, hCsub, rfl⟩, ?_⟩
  rw [Nat.cast_sum, ← hCz_sum, ← hCimg]
  exact (Finset.sum_image (f := fun x : ZMod q ↦ x) (hinj.mono (by exact_mod_cast hCsub))).symm

lemma primes_in_interval_card_ge {y : ℕ} (hy : 2 ^ 20 ≤ y) :
    4 * (y : ℝ) / Real.log y ≤ ((Nat.primesLE (20 * y) \ Nat.primesLE y).card : ℝ) := by
  have hy_pos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hsub : Nat.primesLE y ⊆ Nat.primesLE (20 * y) := by
    intro p hp
    simp only [Nat.mem_primesLE] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hcard_eq : ((Nat.primesLE (20 * y) \ Nat.primesLE y).card : ℝ) =
      (Nat.primeCounting (20 * y) : ℝ) - (Nat.primeCounting y : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_card_eq_primeCounting]
    have hle : Nat.primeCounting y ≤ Nat.primeCounting (20 * y) :=
      Nat.monotone_primeCounting (by omega)
    exact Nat.cast_sub hle
  rw [hcard_eq]
  have hlogy_ge : 13.8 < Real.log y := by
    have h1 : Real.log ((2 : ℝ) ^ (20 : ℕ)) ≤ Real.log y :=
      Real.log_le_log (by positivity) (by exact_mod_cast hy)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [Real.log_two_gt_d9]
  have hlog20_le : Real.log 20 < 3.5 := by
    have h1 : Real.log 20 ≤ Real.log ((2 : ℝ) ^ (5 : ℕ)) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [Real.log_two_lt_d9]
  have hlog20y_le : Real.log (20 * y : ℕ) ≤ 1.3 * Real.log y := by
    push_cast
    rw [Real.log_mul (by norm_num) hy_pos.ne']
    linarith
  have hlog20y_pos : 0 < Real.log (20 * y : ℕ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 20 * y))
  have hlog_err : Real.log ((20 * y + 1 : ℕ) : ℝ) ≤ (y : ℝ) := by
    have h1 : Real.log ((20 * y + 1 : ℕ) : ℝ) = 2 * Real.log (Real.sqrt ((20 * y + 1 : ℕ) : ℝ)) := by
      rw [Real.log_sqrt (by positivity)]; ring
    have h2 : Real.log (Real.sqrt ((20 * y + 1 : ℕ) : ℝ)) ≤ Real.sqrt ((20 * y + 1 : ℕ) : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (20 * y + 1 : ℕ)))]
    have h3 : 2 * Real.sqrt ((20 * y + 1 : ℕ) : ℝ) ≤ (y : ℝ) := by
      have hsq : 4 * ((20 * y + 1 : ℕ) : ℝ) ≤ (y : ℝ) ^ 2 := by
        have hy100 : (100 : ℝ) ≤ y := by exact_mod_cast (by omega : 100 ≤ y)
        push_cast; nlinarith
      have hsq2 : (2 * Real.sqrt ((20 * y + 1 : ℕ) : ℝ)) ^ 2 ≤ (y : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; linarith
      nlinarith [Real.sqrt_nonneg ((20 * y + 1 : ℕ) : ℝ)]
    linarith
  have hpi_hi : 9 * (y : ℝ) / Real.log y ≤ (Nat.primeCounting (20 * y) : ℝ) := by
    have hge := Chebyshev.pi_ge (20 * y)
    have hnum : 11.7 * (y : ℝ) ≤ ((20 * y : ℕ) : ℝ) * Real.log 2 - Real.log ((20 * y + 1 : ℕ) : ℝ) := by
      have hlog_err' : Real.log (20 * (y : ℝ) + 1) ≤ (y : ℝ) := by simpa using hlog_err
      push_cast
      have := Real.log_two_gt_d9
      nlinarith
    have hdiv : 11.7 * (y : ℝ) / (1.3 * Real.log y) ≤
        (((20 * y : ℕ) : ℝ) * Real.log 2 - Real.log ((20 * y + 1 : ℕ) : ℝ)) / Real.log (20 * y : ℕ) := by
      calc 11.7 * (y : ℝ) / (1.3 * Real.log y)
        _ ≤ 11.7 * (y : ℝ) / Real.log (20 * y : ℕ) :=
            div_le_div_of_nonneg_left (by positivity) hlog20y_pos hlog20y_le
        _ ≤ (((20 * y : ℕ) : ℝ) * Real.log 2 - Real.log ((20 * y + 1 : ℕ) : ℝ)) / Real.log (20 * y : ℕ) :=
            div_le_div_of_nonneg_right hnum hlog20y_pos.le
    have heq : 11.7 * (y : ℝ) / (1.3 * Real.log y) = 9 * (y : ℝ) / Real.log y := by ring
    have hge' : (((20 * y : ℕ) : ℝ) * Real.log 2 - Real.log ((20 * y + 1 : ℕ) : ℝ)) /
        Real.log (20 * y : ℕ) ≤ (Nat.primeCounting (20 * y) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hge
    linarith
  have hpi_lo := primeCounting_le_five_mul_div_log y (by omega)
  have hsub_eq : 9 * (y : ℝ) / Real.log y - 5 * (y : ℝ) / Real.log y = 4 * (y : ℝ) / Real.log y := by
    ring
  linarith

lemma dense_primes_contains_sum {n y : ℕ} {A : Finset ℕ}
    (hy100 : 100 ≤ y)
    (hA_primes : ∀ a ∈ A, a.Prime ∧ y < a ∧ a ≤ 20 * y)
    (ht_lo : 40 * (20 * (Nat.sqrt (20 * y) + 1)) * y ≤ n)
    (hA_card : 122 * (20 * (Nat.sqrt (20 * y) + 1)) + n / y + 1 ≤ A.card) :
    n ∈ subsetSums (A : Set ℕ) := by
  classical
  let t : ℕ := 20 * (Nat.sqrt (20 * y) + 1)
  let u : ℕ := 60 * t
  let L := A.sort (· ≤ ·)
  have hL_len : L.length = A.card := Finset.length_sort _
  have hL_pw : L.Pairwise (· ≤ ·) := Finset.pairwise_sort A (· ≤ ·)
  have hL_nodup : L.Nodup := Finset.sort_nodup A (· ≤ ·)
  have hL_mem : ∀ {i : ℕ} (hi : i < L.length), L[i] ∈ A := fun hi ↦
    (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hi)
  have hL_mono : ∀ {i j : ℕ} (hi : i < L.length) (hj : j < L.length), i < j → L[i] < L[j] := by
    intro i j hi hj hij
    have hle : L[i] ≤ L[j] := List.pairwise_iff_getElem.mp hL_pw i j hi hj hij
    have hne : L[i] ≠ L[j] := fun h ↦ by
      have := (List.Nodup.getElem_inj_iff hL_nodup).mp h
      omega
    omega
  have hbound : 2 * t + 2 * u + n / y + 1 ≤ L.length := by
    have htu : 2 * t + 2 * u = 122 * t := by dsimp only [u]; ring
    rw [htu, hL_len]
    exact hA_card
  have h2tu_le : 2 * t + 2 * u ≤ L.length :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hbound)
  -- Helper to extract a Finset of elements at indices in a Finset of ℕ below L.length
  let idxSet : Finset ℕ → Finset ℕ := fun I ↦
    I.attach.image (fun i ↦ if h : i.1 < L.length then L[i.1] else 0)
  have hidx_mem : ∀ (I : Finset ℕ), (∀ i ∈ I, i < L.length) →
      ∀ x ∈ idxSet I, ∃ i ∈ I, ∃ hi : i < L.length, L[i] = x := by
    intro I hI x hx
    rcases Finset.mem_image.mp hx with ⟨⟨i, hiI⟩, _, rfl⟩
    have hi := hI i hiI
    exact ⟨i, hiI, hi, by simp [hi]⟩
  have hidx_sub : ∀ (I : Finset ℕ), (∀ i ∈ I, i < L.length) → idxSet I ⊆ A := by
    intro I hI x hx
    rcases hidx_mem I hI x hx with ⟨i, _, hi, rfl⟩
    exact hL_mem hi
  have hidx_card : ∀ (I : Finset ℕ), (∀ i ∈ I, i < L.length) → (idxSet I).card = I.card := by
    intro I hI
    rw [← Finset.card_attach (s := I)]
    refine Finset.card_image_of_injective _ fun ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ heq ↦ ?_
    have h1 := hI i₁ hi₁
    have h2 := hI i₂ hi₂
    simp only [h1, h2, dite_true] at heq
    have hidx_eq : i₁ = i₂ := by
      rcases lt_trichotomy i₁ i₂ with hlt | he | hgt
      · exact absurd heq (ne_of_lt (hL_mono h1 h2 hlt))
      · exact he
      · exact absurd heq (ne_of_gt (hL_mono h2 h1 hgt))
    exact Subtype.ext hidx_eq
  have hidx_disj : ∀ (I J : Finset ℕ), (∀ i ∈ I, i < L.length) → (∀ j ∈ J, j < L.length) →
      Disjoint I J → Disjoint (idxSet I) (idxSet J) := by
    intro I J hI hJ hd
    refine Finset.disjoint_left.mpr fun x hxI hxJ ↦ ?_
    rcases hidx_mem I hI x hxI with ⟨i, hiI, hi, rfl⟩
    rcases hidx_mem J hJ L[i] hxJ with ⟨j, hjJ, hj, heq⟩
    have hij : i = j := by
      rcases lt_trichotomy i j with hlt | he | hgt
      · exact absurd heq (ne_of_gt (hL_mono hi hj hlt))
      · exact he
      · exact absurd heq (ne_of_lt (hL_mono hj hi hgt))
    exact Finset.disjoint_left.mp hd hiI (hij ▸ hjJ)
  let I₁₁ := (Finset.range t).image (fun k ↦ 2 * k)
  let I₁₂ := (Finset.range t).image (fun k ↦ 2 * k + 1)
  let I₂₁ := (Finset.range u).image (fun k ↦ 2 * t + 2 * k)
  let I₂₂ := (Finset.range u).image (fun k ↦ 2 * t + 2 * k + 1)
  let I₃ := Finset.Ico (2 * t + 2 * u) L.length
  have hI₁₁_lt : ∀ i ∈ I₁₁, i < L.length := by
    intro i hi; rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk; exact lt_of_lt_of_le (by omega : 2 * k < 2 * t + 2 * u) h2tu_le
  have hI₁₂_lt : ∀ i ∈ I₁₂, i < L.length := by
    intro i hi; rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk; exact lt_of_lt_of_le (by omega : 2 * k + 1 < 2 * t + 2 * u) h2tu_le
  have hI₂₁_lt : ∀ i ∈ I₂₁, i < L.length := by
    intro i hi; rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk; exact lt_of_lt_of_le (by omega : 2 * t + 2 * k < 2 * t + 2 * u) h2tu_le
  have hI₂₂_lt : ∀ i ∈ I₂₂, i < L.length := by
    intro i hi; rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk; exact lt_of_lt_of_le (by omega : 2 * t + 2 * k + 1 < 2 * t + 2 * u) h2tu_le
  have hI₃_lt : ∀ i ∈ I₃, i < L.length := fun i hi ↦ (Finset.mem_Ico.mp hi).2
  let B₁₁ := idxSet I₁₁
  let B₁₂ := idxSet I₁₂
  let B₂₁ := idxSet I₂₁
  let B₂₂ := idxSet I₂₂
  let B₃ := idxSet I₃
  have hcard_B₁₁ : B₁₁.card = t := by
    rw [hidx_card I₁₁ hI₁₁_lt, Finset.card_image_of_injective _ (fun a b h ↦ by omega), Finset.card_range]
  have hcard_B₁₂ : B₁₂.card = t := by
    rw [hidx_card I₁₂ hI₁₂_lt, Finset.card_image_of_injective _ (fun a b h ↦ by omega), Finset.card_range]
  have hcard_B₂₁ : B₂₁.card = u := by
    rw [hidx_card I₂₁ hI₂₁_lt, Finset.card_image_of_injective _ (fun a b h ↦ by omega), Finset.card_range]
  have hcard_B₂₂ : B₂₂.card = u := by
    rw [hidx_card I₂₂ hI₂₂_lt, Finset.card_image_of_injective _ (fun a b h ↦ by omega), Finset.card_range]
  have hcard_B₃ : n / y + 1 ≤ B₃.card := by
    rw [hidx_card I₃ hI₃_lt, Nat.card_Ico]; omega
  -- Coverage of B₁₁ mod every q ∈ B₂₁, and B₁₂ mod every q ∈ B₂₂
  have hcov₁ : ∀ q ∈ B₂₁, 0 < q ∧ ∀ r : ZMod q, ∃ x ∈ B₁₁.subsetSum, (x : ZMod q) = r := by
    intro q hq
    rcases hidx_mem I₂₁ hI₂₁_lt q hq with ⟨j, hjI, hjL, rfl⟩
    have hqA := hA_primes L[j] (hL_mem hjL)
    refine ⟨hqA.1.pos, subsetSum_zmod_image_of_primes hqA.1 (by omega) ?_ ?_⟩
    · intro a ha
      rcases hidx_mem I₁₁ hI₁₁_lt a ha with ⟨i, hiI, hiL, rfl⟩
      have haA := hA_primes L[i] (hL_mem hiL)
      have hij : i < j := by
        rcases Finset.mem_image.mp hiI with ⟨k₁, hk₁, rfl⟩
        rcases Finset.mem_image.mp hjI with ⟨k₂, hk₂, rfl⟩
        rw [Finset.mem_range] at hk₁ hk₂; omega
      exact ⟨haA.1.pos, hL_mono hiL hjL hij⟩
    · rw [hcard_B₁₁]
      have : Nat.sqrt L[j] ≤ Nat.sqrt (20 * y) := Nat.sqrt_le_sqrt hqA.2.2
      dsimp only [t]; omega
  have hcov₂ : ∀ q ∈ B₂₂, 0 < q ∧ ∀ r : ZMod q, ∃ x ∈ B₁₂.subsetSum, (x : ZMod q) = r := by
    intro q hq
    rcases hidx_mem I₂₂ hI₂₂_lt q hq with ⟨j, hjI, hjL, rfl⟩
    have hqA := hA_primes L[j] (hL_mem hjL)
    refine ⟨hqA.1.pos, subsetSum_zmod_image_of_primes hqA.1 (by omega) ?_ ?_⟩
    · intro a ha
      rcases hidx_mem I₁₂ hI₁₂_lt a ha with ⟨i, hiI, hiL, rfl⟩
      have haA := hA_primes L[i] (hL_mem hiL)
      have hij : i < j := by
        rcases Finset.mem_image.mp hiI with ⟨k₁, hk₁, rfl⟩
        rcases Finset.mem_image.mp hjI with ⟨k₂, hk₂, rfl⟩
        rw [Finset.mem_range] at hk₁ hk₂; omega
      exact ⟨haA.1.pos, hL_mono hiL hjL hij⟩
    · rw [hcard_B₁₂]
      have : Nat.sqrt L[j] ≤ Nat.sqrt (20 * y) := Nat.sqrt_le_sqrt hqA.2.2
      dsimp only [t]; omega
  have hd_11_21 : Disjoint B₁₁ B₂₁ := hidx_disj I₁₁ I₂₁ hI₁₁_lt hI₂₁_lt (by
    refine Finset.disjoint_left.mpr fun x hx1 hx2 ↦ ?_
    rcases Finset.mem_image.mp hx1 with ⟨k₁, hk₁, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨k₂, _, heq⟩
    rw [Finset.mem_range] at hk₁; omega)
  have hd_12_22 : Disjoint B₁₂ B₂₂ := hidx_disj I₁₂ I₂₂ hI₁₂_lt hI₂₂_lt (by
    refine Finset.disjoint_left.mpr fun x hx1 hx2 ↦ ?_
    rcases Finset.mem_image.mp hx1 with ⟨k₁, hk₁, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨k₂, _, heq⟩
    rw [Finset.mem_range] at hk₁; omega)
  have hS₁_card := card_subsetSum_union_ge hd_11_21 hcov₁
  have hS₂_card := card_subsetSum_union_ge hd_12_22 hcov₂
  let S₁ := (B₁₁ ∪ B₂₁).subsetSum
  let S₂ := (B₁₂ ∪ B₂₂).subsetSum
  let L₁ := ∑ x ∈ B₁₁ ∪ B₂₁, x
  let L₂ := ∑ x ∈ B₁₂ ∪ B₂₂, x
  have hS₁_sub : S₁ ⊆ Finset.Icc 0 L₁ := by
    intro s hs
    rcases Finset.mem_subsetSum_iff.mp hs with ⟨C, hC, rfl⟩
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Finset.sum_le_sum_of_subset (f := id) hC⟩
  have hS₂_sub : S₂ ⊆ Finset.Icc 0 L₂ := by
    intro s hs
    rcases Finset.mem_subsetSum_iff.mp hs with ⟨C, hC, rfl⟩
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Finset.sum_le_sum_of_subset (f := id) hC⟩
  have hE₁ : L₁ + 1 - S₁.card ≤ 20 * t * y := by
    have hsum_u : L₁ = ∑ x ∈ B₁₁, x + ∑ x ∈ B₂₁, x := Finset.sum_union hd_11_21
    have hB₁₁_sum : ∑ x ∈ B₁₁, x ≤ 20 * t * y := by
      calc ∑ x ∈ B₁₁, x ≤ ∑ _x ∈ B₁₁, (20 * y) :=
            Finset.sum_le_sum fun x hx ↦ (hA_primes x (hidx_sub I₁₁ hI₁₁_lt hx)).2.2
        _ = B₁₁.card * (20 * y) := by simp
        _ = 20 * t * y := by rw [hcard_B₁₁]; ring
    have hS₁' : 1 + ∑ q ∈ B₂₁, q ≤ S₁.card := hS₁_card
    omega
  have hE₂ : L₂ + 1 - S₂.card ≤ 20 * t * y := by
    have hsum_u : L₂ = ∑ x ∈ B₁₂, x + ∑ x ∈ B₂₂, x := Finset.sum_union hd_12_22
    have hB₁₂_sum : ∑ x ∈ B₁₂, x ≤ 20 * t * y := by
      calc ∑ x ∈ B₁₂, x ≤ ∑ _x ∈ B₁₂, (20 * y) :=
            Finset.sum_le_sum fun x hx ↦ (hA_primes x (hidx_sub I₁₂ hI₁₂_lt hx)).2.2
        _ = B₁₂.card * (20 * y) := by simp
        _ = 20 * t * y := by rw [hcard_B₁₂]; ring
    have hS₂' : 1 + ∑ q ∈ B₂₂, q ≤ S₂.card := hS₂_card
    omega
  have hL₁_ge : 60 * t * y ≤ L₁ := by
    have h1 : ∑ x ∈ B₂₁, x ≤ L₁ :=
      Finset.sum_le_sum_of_subset (f := id) Finset.subset_union_right
    have h2 : 60 * t * y ≤ ∑ x ∈ B₂₁, x := by
      calc 60 * t * y = B₂₁.card * y := by rw [hcard_B₂₁]
        _ = ∑ _x ∈ B₂₁, y := by simp
        _ ≤ ∑ x ∈ B₂₁, x := Finset.sum_le_sum fun x hx ↦ (hA_primes x (hidx_sub I₂₁ hI₂₁_lt hx)).2.1.le
    omega
  have hL₂_ge : 60 * t * y ≤ L₂ := by
    have h1 : ∑ x ∈ B₂₂, x ≤ L₂ :=
      Finset.sum_le_sum_of_subset (f := id) Finset.subset_union_right
    have h2 : 60 * t * y ≤ ∑ x ∈ B₂₂, x := by
      calc 60 * t * y = B₂₂.card * y := by rw [hcard_B₂₂]
        _ = ∑ _x ∈ B₂₂, y := by simp
        _ ≤ ∑ x ∈ B₂₂, x := Finset.sum_le_sum fun x hx ↦ (hA_primes x (hidx_sub I₂₂ hI₂₂_lt hx)).2.1.le
    omega
  have hd_1_2 : Disjoint (B₁₁ ∪ B₂₁) (B₁₂ ∪ B₂₂) := by
    have hI_disj : Disjoint (I₁₁ ∪ I₂₁) (I₁₂ ∪ I₂₂) := by
      refine Finset.disjoint_left.mpr fun x hx1 hx2 ↦ ?_
      have hx_even : x % 2 = 0 := by
        rcases Finset.mem_union.mp hx1 with h | h <;>
          rcases Finset.mem_image.mp h with ⟨k, _, rfl⟩ <;> omega
      have hx_odd : x % 2 = 1 := by
        rcases Finset.mem_union.mp hx2 with h | h <;>
          rcases Finset.mem_image.mp h with ⟨k, _, rfl⟩ <;> omega
      omega
    have h1 : B₁₁ ∪ B₂₁ ⊆ idxSet (I₁₁ ∪ I₂₁) := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · rcases hidx_mem I₁₁ hI₁₁_lt x h with ⟨i, hiI, hiL, rfl⟩
        exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_left _ hiI⟩, Finset.mem_attach _ _, by simp [hiL]⟩
      · rcases hidx_mem I₂₁ hI₂₁_lt x h with ⟨i, hiI, hiL, rfl⟩
        exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_right _ hiI⟩, Finset.mem_attach _ _, by simp [hiL]⟩
    have h2 : B₁₂ ∪ B₂₂ ⊆ idxSet (I₁₂ ∪ I₂₂) := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · rcases hidx_mem I₁₂ hI₁₂_lt x h with ⟨i, hiI, hiL, rfl⟩
        exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_left _ hiI⟩, Finset.mem_attach _ _, by simp [hiL]⟩
      · rcases hidx_mem I₂₂ hI₂₂_lt x h with ⟨i, hiI, hiL, rfl⟩
        exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_right _ hiI⟩, Finset.mem_attach _ _, by simp [hiL]⟩
    have hlt1 : ∀ i ∈ I₁₁ ∪ I₂₁, i < L.length := fun i hi ↦ by
      rcases Finset.mem_union.mp hi with h | h
      · exact hI₁₁_lt i h
      · exact hI₂₁_lt i h
    have hlt2 : ∀ i ∈ I₁₂ ∪ I₂₂, i < L.length := fun i hi ↦ by
      rcases Finset.mem_union.mp hi with h | h
      · exact hI₁₂_lt i h
      · exact hI₂₂_lt i h
    exact (hidx_disj _ _ hlt1 hlt2 hI_disj).mono h1 h2
  have h2040 : 20 * t * y + 20 * t * y = 40 * t * y := by ring
  have h4060 : 40 * t * y + 20 * t * y = 60 * t * y := by ring
  have hIcc : Finset.Icc (40 * t * y) (60 * t * y) ⊆ ((B₁₁ ∪ B₂₁) ∪ (B₁₂ ∪ B₂₂)).subsetSum := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    obtain ⟨a, ha, b, hb, hab⟩ := dense_sumset_interval (m := m) hS₁_sub hS₂_sub hE₁ hE₂
      (by omega) (le_min (by omega) (by omega))
    exact hab ▸ subsetSum_union_add hd_1_2 ha hb
  have hd_12_3 : Disjoint ((B₁₁ ∪ B₂₁) ∪ (B₁₂ ∪ B₂₂)) B₃ := by
    have hsub12 : (B₁₁ ∪ B₂₁) ∪ (B₁₂ ∪ B₂₂) ⊆ idxSet (Finset.range (2 * t + 2 * u)) := by
      intro x hx
      have hmem_lt : ∀ (I : Finset ℕ), (∀ i ∈ I, i < 2 * t + 2 * u) → x ∈ idxSet I →
          x ∈ idxSet (Finset.range (2 * t + 2 * u)) := by
        intro I hI hxI
        rcases hidx_mem I (fun i hi ↦ lt_of_lt_of_le (hI i hi) h2tu_le) x hxI with ⟨i, hiI, hiL, rfl⟩
        exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_range.mpr (hI i hiI)⟩, Finset.mem_attach _ _, by simp [hiL]⟩
      rcases Finset.mem_union.mp hx with h1 | h2
      · rcases Finset.mem_union.mp h1 with h | h
        · exact hmem_lt I₁₁ (fun i hi ↦ by rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩; rw [Finset.mem_range] at hk; omega) h
        · exact hmem_lt I₂₁ (fun i hi ↦ by rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩; rw [Finset.mem_range] at hk; omega) h
      · rcases Finset.mem_union.mp h2 with h | h
        · exact hmem_lt I₁₂ (fun i hi ↦ by rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩; rw [Finset.mem_range] at hk; omega) h
        · exact hmem_lt I₂₂ (fun i hi ↦ by rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩; rw [Finset.mem_range] at hk; omega) h
    have hI_disj : Disjoint (Finset.range (2 * t + 2 * u)) I₃ := by
      refine Finset.disjoint_left.mpr fun i hi1 hi2 ↦ ?_
      rw [Finset.mem_range] at hi1; rw [Finset.mem_Ico] at hi2; omega
    exact (hidx_disj _ _ (fun i hi ↦ lt_of_lt_of_le (Finset.mem_range.mp hi) h2tu_le) hI₃_lt hI_disj).mono_left hsub12
  have hB₃_le : ∀ x ∈ B₃, x ≤ 60 * t * y - 40 * t * y + 1 := by
    intro x hx
    have h1 := (hA_primes x (hidx_sub I₃ hI₃_lt hx)).2.2
    have ht1 : 1 ≤ t := by dsimp only [t]; omega
    have h2 : 20 * y ≤ 20 * t * y := by nlinarith
    omega
  have hext := graham_extend (by omega : 40 * t * y ≤ 60 * t * y) hIcc hd_12_3 hB₃_le
  have hB₃_sum : n ≤ ∑ x ∈ B₃, x := by
    have h1 : B₃.card * y ≤ ∑ x ∈ B₃, x := by
      calc B₃.card * y = ∑ _x ∈ B₃, y := by simp
        _ ≤ ∑ x ∈ B₃, x := Finset.sum_le_sum fun x hx ↦ (hA_primes x (hidx_sub I₃ hI₃_lt hx)).2.1.le
    have h2 : n < (n / y + 1) * y := by
      have := Nat.div_add_mod n y
      have := Nat.mod_lt n (by omega : 0 < y)
      nlinarith
    have h3 : (n / y + 1) * y ≤ B₃.card * y := Nat.mul_le_mul_right y hcard_B₃
    omega
  have hn_mem : n ∈ (((B₁₁ ∪ B₂₁) ∪ (B₁₂ ∪ B₂₂)) ∪ B₃).subsetSum :=
    hext (Finset.mem_Icc.mpr ⟨ht_lo, by omega⟩)
  have hall_sub : ((B₁₁ ∪ B₂₁) ∪ (B₁₂ ∪ B₂₂)) ∪ B₃ ⊆ A :=
    Finset.union_subset
      (Finset.union_subset
        (Finset.union_subset (hidx_sub I₁₁ hI₁₁_lt) (hidx_sub I₂₁ hI₂₁_lt))
        (Finset.union_subset (hidx_sub I₁₂ hI₁₂_lt) (hidx_sub I₂₂ hI₂₂_lt)))
      (hidx_sub I₃ hI₃_lt)
  rcases Finset.mem_subsetSum_iff.mp (Finset.subsetSum_mono hall_sub hn_mem) with ⟨C, hC, hCsum⟩
  exact ⟨C, Finset.coe_subset.mpr hC, hCsum.symm⟩

lemma alon_erdos_lower :
    (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (4 / 3 : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (Erdos360.f n : ℝ)) := by
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (2 / 3 : ℝ) / 10000) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have hy_big : ∀ᶠ n : ℕ in atTop, (2 ^ 20 + 1 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) / 10000 :=
    hlim.eventually_ge_atTop _
  have hlog_ge1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  refine IsBigO.of_bound (200000000 : ℝ) ?_
  filter_upwards [eventually_ge_atTop (10 ^ 12), hy_big, hlog_ge1] with n hn12 hy_big hlog_ge1
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log n := by linarith
  have hn13_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
  let y : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ) / 10000⌋₊
  have hy_ge20 : 2 ^ 20 ≤ y := by
    have : ((2 ^ 20 : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) / 10000 := by
      push_cast; linarith
    exact Nat.le_floor this
  have hy_pos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hy_le : (y : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) / 10000 := Nat.floor_le (by positivity)
  have hy_ge_half : (n : ℝ) ^ (2 / 3 : ℝ) / 20000 ≤ (y : ℝ) := by
    have h1 : (n : ℝ) ^ (2 / 3 : ℝ) / 10000 - 1 < y := Nat.sub_one_lt_floor _
    linarith
  have h20y_lt_n : 20 * y < n := by
    have h1 : (20 * y : ℝ) < n := by
      have h2 : (n : ℝ) ^ (2 / 3 : ℝ) ≤ n := by
        conv_rhs => rw [← Real.rpow_one (n : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
      linarith
    exact_mod_cast h1
  have hpow_mul : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hn_pos]; norm_num
  have hf_ge : (n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n) ≤ (Erdos360.f n : ℝ) := by
    let R : ℕ := ⌈(n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n)⌉₊
    suffices hR : R ≤ Erdos360.f n by
      exact (Nat.le_ceil _).trans (by exact_mod_cast hR)
    refine le_f_of_forall_partition (by omega) fun P hfree ↦ ?_
    by_contra hlt_R
    push Not at hlt_R
    have hP_real : (P.parts.card : ℝ) < (n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n) :=
      Nat.lt_ceil.mp hlt_R
    let S : Finset ℕ := Nat.primesLE (20 * y) \ Nat.primesLE y
    have hS_sub : S ⊆ Finset.Icc 1 (n - 1) := by
      intro p hp
      simp only [S, Finset.mem_sdiff, Nat.mem_primesLE] at hp
      exact Finset.mem_Icc.mpr ⟨hp.1.2.one_le, by omega⟩
    have hS_card_ge : (n : ℝ) ^ (2 / 3 : ℝ) / (5000 * Real.log n) ≤ (S.card : ℝ) := by
      have h1 := primes_in_interval_card_ge hy_ge20
      have hlogy_pos : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
      have hlogy_le : Real.log y ≤ Real.log n :=
        Real.log_le_log hy_pos (by exact_mod_cast (by omega : y ≤ n))
      have h2 : 4 * (y : ℝ) / Real.log n ≤ 4 * (y : ℝ) / Real.log y :=
        div_le_div_of_nonneg_left (by positivity) hlogy_pos hlogy_le
      have h3 : (n : ℝ) ^ (2 / 3 : ℝ) / (5000 * Real.log n) ≤ 4 * (y : ℝ) / Real.log n := by
        have h4 : (n : ℝ) ^ (2 / 3 : ℝ) / (5000 * Real.log n) =
            (4 * ((n : ℝ) ^ (2 / 3 : ℝ) / 20000)) / Real.log n := by ring
        rw [h4]
        exact div_le_div_of_nonneg_right (by linarith) hlog_pos.le
      exact h3.trans (h2.trans h1)
    have hS_ne : S.Nonempty := by
      refine Finset.card_pos.mp ?_
      have hpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hS_card_ge
      exact_mod_cast hpos
    have hS_cov : S ⊆ P.parts.biUnion (fun A ↦ A ∩ S) := by
      intro p hp
      have hpIcc : p ∈ P.parts.sup id := P.sup_parts.symm ▸ hS_sub hp
      rcases Finset.mem_sup.mp hpIcc with ⟨A, hA, hpA⟩
      exact Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_inter.mpr ⟨hpA, hp⟩⟩
    have hP_ne : P.parts.Nonempty := by
      obtain ⟨p, hp⟩ := hS_ne
      rcases Finset.mem_biUnion.mp (hS_cov hp) with ⟨A, hA, _⟩
      exact ⟨A, hA⟩
    obtain ⟨A, hA_mem, hA_max⟩ := Finset.exists_max_image P.parts (fun A ↦ (A ∩ S).card) hP_ne
    let B := A ∩ S
    have hS_le_PB : S.card ≤ P.parts.card * B.card := by
      calc S.card ≤ (P.parts.biUnion (fun C ↦ C ∩ S)).card := Finset.card_le_card hS_cov
        _ ≤ ∑ C ∈ P.parts, (C ∩ S).card := Finset.card_biUnion_le
        _ ≤ ∑ _C ∈ P.parts, B.card := Finset.sum_le_sum fun C hC ↦ hA_max C hC
        _ = P.parts.card * B.card := by simp
    have hB_card_real : 40000 * (n : ℝ) ^ (1 / 3 : ℝ) ≤ (B.card : ℝ) := by
      have hP_pos : (0 : ℝ) < P.parts.card := by exact_mod_cast Finset.card_pos.mpr hP_ne
      have h1 : (n : ℝ) ^ (2 / 3 : ℝ) / (5000 * Real.log n) ≤ (P.parts.card : ℝ) * (B.card : ℝ) :=
        hS_card_ge.trans (by exact_mod_cast hS_le_PB)
      have h2 : (P.parts.card : ℝ) * (B.card : ℝ) ≤
          ((n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n)) * (B.card : ℝ) :=
        mul_le_mul_of_nonneg_right hP_real.le (Nat.cast_nonneg _)
      have h3 : (n : ℝ) ^ (2 / 3 : ℝ) / (5000 * Real.log n) ≤
          ((n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n)) * (B.card : ℝ) := h1.trans h2
      have h4 : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hn_pos]; norm_num
      rw [h4] at h3
      have hpos_fac : 0 < (n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n) := by positivity
      have h3' : ((n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n)) * (40000 * (n : ℝ) ^ (1 / 3 : ℝ)) ≤
          ((n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n)) * (B.card : ℝ) := by
        have heq : ((n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n)) * (40000 * (n : ℝ) ^ (1 / 3 : ℝ)) =
            (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) / (5000 * Real.log n) := by ring
        linarith
      exact le_of_mul_le_mul_left h3' hpos_fac
    -- Bound sqrt(20 * y) ≤ n^(1/3) / 20
    have hsqrt_le : (Nat.sqrt (20 * y) : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) / 20 := by
      have hsq : ((Nat.sqrt (20 * y) : ℕ) : ℝ) ^ 2 ≤ ((n : ℝ) ^ (1 / 3 : ℝ) / 20) ^ 2 := by
        have h1 : (Nat.sqrt (20 * y)) ^ 2 ≤ 20 * y := by
          rw [sq]; exact Nat.sqrt_le (20 * y)
        have h1R : ((Nat.sqrt (20 * y) : ℝ)) ^ 2 ≤ 20 * (y : ℝ) := by exact_mod_cast h1
        have h2 : 20 * (y : ℝ) ≤ 20 * ((n : ℝ) ^ (2 / 3 : ℝ) / 10000) := by linarith
        have h3 : ((n : ℝ) ^ (1 / 3 : ℝ) / 20) ^ 2 = (n : ℝ) ^ (2 / 3 : ℝ) / 400 := by
          rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
        linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt (20 * y)), Real.rpow_pos_of_pos hn_pos (1 / 3 : ℝ)]
    have ht_real : ((20 * (Nat.sqrt (20 * y) + 1) : ℕ) : ℝ) ≤ 21 * (n : ℝ) ^ (1 / 3 : ℝ) := by
      push_cast; linarith
    have ht_lo : 40 * (20 * (Nat.sqrt (20 * y) + 1)) * y ≤ n := by
      have hR : ((40 * (20 * (Nat.sqrt (20 * y) + 1)) * y : ℕ) : ℝ) ≤ (n : ℝ) := by
        push_cast
        have h1 : 40 * (20 * ((Nat.sqrt (20 * y) : ℝ) + 1)) * (y : ℝ) ≤
            40 * (21 * (n : ℝ) ^ (1 / 3 : ℝ)) * ((n : ℝ) ^ (2 / 3 : ℝ) / 10000) := by
          have ha : 0 ≤ 40 * (20 * ((Nat.sqrt (20 * y) : ℝ) + 1)) := by positivity
          have hb : 40 * (20 * ((Nat.sqrt (20 * y) : ℝ) + 1)) ≤ 40 * (21 * (n : ℝ) ^ (1 / 3 : ℝ)) := by
            push_cast at ht_real; linarith
          exact mul_le_mul hb hy_le hy_pos.le (by positivity)
        have h2 : 40 * (21 * (n : ℝ) ^ (1 / 3 : ℝ)) * ((n : ℝ) ^ (2 / 3 : ℝ) / 10000) =
            (840 / 10000 : ℝ) * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) := by ring
        rw [h2, hpow_mul] at h1
        linarith
      exact_mod_cast hR
    have hB_card_nat : 122 * (20 * (Nat.sqrt (20 * y) + 1)) + n / y + 1 ≤ B.card := by
      have hdiv_le : ((n / y : ℕ) : ℝ) ≤ 20000 * (n : ℝ) ^ (1 / 3 : ℝ) := by
        have h1 : ((n / y : ℕ) : ℝ) ≤ (n : ℝ) / (y : ℝ) := Nat.cast_div_le
        have h2 : (n : ℝ) / (y : ℝ) ≤ (n : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ) / 20000) :=
          div_le_div_of_nonneg_left hn_pos.le (by positivity) hy_ge_half
        have h3 : (n : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ) / 20000) = 20000 * (n : ℝ) ^ (1 / 3 : ℝ) := by
          calc (n : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ) / 20000)
            _ = ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) / ((n : ℝ) ^ (2 / 3 : ℝ) / 20000) := by
                rw [hpow_mul]
            _ = 20000 * (n : ℝ) ^ (1 / 3 : ℝ) := by field_simp
        linarith
      have hR : ((122 * (20 * (Nat.sqrt (20 * y) + 1)) + n / y + 1 : ℕ) : ℝ) ≤ (B.card : ℝ) := by
        push_cast at ht_real ⊢
        linarith
      exact_mod_cast hR
    have hB_primes : ∀ a ∈ B, a.Prime ∧ y < a ∧ a ≤ 20 * y := by
      intro a ha
      have haS := (Finset.mem_inter.mp ha).2
      simp only [S, Finset.mem_sdiff, Nat.mem_primesLE] at haS
      have hgt : y < a := by
        by_contra hle; push Not at hle
        exact haS.2 ⟨hle, haS.1.2⟩
      exact ⟨haS.1.2, hgt, haS.1.1⟩
    have hn_in_B : n ∈ subsetSums (B : Set ℕ) :=
      dense_primes_contains_sum (by omega) hB_primes ht_lo hB_card_nat
    exact hfree A hA_mem (subsetSums_mono (Finset.coe_subset.mpr Finset.inter_subset_left) hn_in_B)
  have hlog_pow : Real.log n ≤ Real.log n ^ (4 / 3 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one (Real.log n)]
    exact Real.rpow_le_rpow_of_exponent_le hlog_ge1 (by norm_num)
  have hdiv : (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (4 / 3 : ℝ) ≤
      (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n :=
    div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_pow
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hmul : (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ≤ 200000000 * (Erdos360.f n : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hf_ge (by norm_num : (0 : ℝ) ≤ 200000000)
    have h2 : 200000000 * ((n : ℝ) ^ (1 / 3 : ℝ) / (200000000 * Real.log n)) =
        (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n := by field_simp
    linarith
  linarith

end Erdos360AlonErdos

theorem OMA.solution : type_of% @Erdos360.erdos_360.variants.alon_erdos := by
  exact ⟨Erdos360AlonErdos.alon_erdos_lower, Erdos360AlonErdos.alon_erdos_upper⟩
