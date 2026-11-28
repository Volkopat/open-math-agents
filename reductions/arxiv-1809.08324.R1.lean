import OMAStatements.S_arxiv_1809_08324
import Mathlib

/- The case k = 1 (Seymour and Spirkl) is proved here by double counting over A x B:
for each pair (a, b) at most one of r a b, s b a fails to give a digon, so if there is no
digon then the out-degree sums satisfy beta |A||B| + alpha |A||B| <= |A||B|, contradicting
alpha + beta > 1. A digon is a closed walk with j = 1.
The case k = 2 is proved here too, by a second double count. Shrink each out-set of a in A
to O_a of size q = ceil(beta |B|) and let N(a, a') count b in O_a with s b a'. With no closed walk
of length 2 or 4, N(a, a') + N(a', a) <= q - |O_a inter O_a'| for every ordered pair; summing and
applying Cauchy-Schwarz to f(b) = #{a | b in O_a} gives 2 alpha <= 1 - q / |B| <= 1 - beta.
The case k = 2 already gives every k >= 2 whenever 2 alpha + beta > 1. So the hypotheses cover only
the range not covered by the k = 1, 2 arguments proved here (the paper also proves weaker
results for k = 3, 4 and symmetric cases, which are not used): H1 is k = 3 with 2 alpha + beta <= 1, and H2 is k >= 4 with
2 alpha + beta <= 1. -/
namespace OMA.R_arxiv_1809_08324_R1

open Finset

def H1 : Prop :=
  ∀ α β : ℝ, 0 < α → 0 < β → 1 < 3 * α + β → 2 * α + β ≤ 1 →
    ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
      (r : A → B → Prop) (s : B → A → Prop) [∀ a, DecidablePred (r a)]
      [∀ b, DecidablePred (s b)],
      (∀ a, β * Fintype.card B ≤ (Finset.univ.filter (r a)).card) →
      (∀ b, α * Fintype.card A ≤ (Finset.univ.filter (s b)).card) →
      ∃ j, 1 ≤ j ∧ j ≤ 3 ∧ ∃ (a : ℕ → A) (b : ℕ → B), a j = a 0 ∧
        ∀ i < j, r (a i) (b i) ∧ s (b i) (a (i + 1))

def H2 : Prop :=
  ∀ (k : ℕ), 4 ≤ k → ∀ α β : ℝ, 0 < α → 0 < β → 1 < k * α + β → 2 * α + β ≤ 1 →
    ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
      (r : A → B → Prop) (s : B → A → Prop) [∀ a, DecidablePred (r a)]
      [∀ b, DecidablePred (s b)],
      (∀ a, β * Fintype.card B ≤ (Finset.univ.filter (r a)).card) →
      (∀ b, α * Fintype.card A ≤ (Finset.univ.filter (s b)).card) →
      ∃ j, 1 ≤ j ∧ j ≤ k ∧ ∃ (a : ℕ → A) (b : ℕ → B), a j = a 0 ∧
        ∀ i < j, r (a i) (b i) ∧ s (b i) (a (i + 1))

theorem digon {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (r : A → B → Prop) (s : B → A → Prop) [∀ a, DecidablePred (r a)]
    [∀ b, DecidablePred (s b)] (α β : ℝ) (hab : 1 < α + β)
    (hr : ∀ a, β * Fintype.card B ≤ (Finset.univ.filter (r a)).card)
    (hs : ∀ b, α * Fintype.card A ≤ (Finset.univ.filter (s b)).card) :
    ∃ a b, r a b ∧ s b a := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have key : ∀ a b, (if r a b then 1 else 0) + (if s b a then 1 else 0) ≤ (1 : ℕ) := by
    intro a b
    by_cases h1 : r a b <;> by_cases h2 : s b a <;> simp [h1, h2]
    exact hne a b h1 h2
  have hsum : (∑ a, (univ.filter (r a)).card) + ∑ b, (univ.filter (s b)).card ≤
      Fintype.card A * Fintype.card B := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm (f := fun b a => if s b a then 1 else 0), ← Finset.sum_add_distrib]
    calc ∑ a, ((∑ b, if r a b then 1 else 0) + ∑ b, if s b a then 1 else 0)
        = ∑ a, ∑ b, ((if r a b then 1 else 0) + (if s b a then 1 else 0)) := by
          simp only [Finset.sum_add_distrib]
      _ ≤ ∑ _a : A, ∑ _b : B, (1 : ℕ) := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => key a b
      _ = Fintype.card A * Fintype.card B := by simp
  have hR : (Fintype.card A : ℝ) * (β * Fintype.card B) ≤
      ∑ a, ((univ.filter (r a)).card : ℝ) := by
    have := Finset.sum_le_sum (s := (univ : Finset A)) fun a _ => hr a
    simpa [Finset.sum_const, Finset.card_univ] using this
  have hS : (Fintype.card B : ℝ) * (α * Fintype.card A) ≤
      ∑ b, ((univ.filter (s b)).card : ℝ) := by
    have := Finset.sum_le_sum (s := (univ : Finset B)) fun b _ => hs b
    simpa [Finset.sum_const, Finset.card_univ] using this
  have hsumR : (∑ a, ((univ.filter (r a)).card : ℝ)) + ∑ b, ((univ.filter (s b)).card : ℝ) ≤
      (Fintype.card A : ℝ) * Fintype.card B := by
    exact_mod_cast hsum
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hAB : 0 < (Fintype.card A : ℝ) * Fintype.card B := mul_pos hA hB
  nlinarith

theorem four {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (r : A → B → Prop) (s : B → A → Prop) [∀ a, DecidablePred (r a)]
    [∀ b, DecidablePred (s b)] (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hab : 1 < 2 * α + β)
    (hr : ∀ a, β * Fintype.card B ≤ (Finset.univ.filter (r a)).card)
    (hs : ∀ b, α * Fintype.card A ≤ (Finset.univ.filter (s b)).card) :
    ∃ a0 b0 a1 b1, r a0 b0 ∧ s b0 a1 ∧ r a1 b1 ∧ s b1 a0 := by
  classical
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hm : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌈β * Fintype.card B⌉₊ := ⟨_, rfl⟩
  have hqle : ∀ a, q ≤ (univ.filter (r a)).card := fun a => by
    rw [hq]; exact Nat.ceil_le.mpr (hr a)
  have hqge : β * Fintype.card B ≤ q := by rw [hq]; exact Nat.le_ceil _
  have hO : ∀ a, ∃ t ⊆ univ.filter (r a), t.card = q := fun a =>
    Finset.exists_subset_card_eq (hqle a)
  choose O hOsub hOcard using hO
  have hOr : ∀ a b, b ∈ O a → r a b := fun a b hb => (Finset.mem_filter.mp (hOsub a hb)).2
  -- N a a' = number of b in O a with s b a'
  have half : ∀ a a', ((O a).filter (fun b => s b a')).card + (O a ∩ O a').card ≤ q := by
    intro a a'
    have hdisj : Disjoint ((O a).filter (fun b => s b a')) (O a ∩ O a') := by
      rw [Finset.disjoint_left]
      intro b hb hb'
      rw [Finset.mem_filter] at hb
      rw [Finset.mem_inter] at hb'
      exact hne a' b a' b (hOr a' b hb'.2) hb.2 (hOr a' b hb'.2) hb.2
    have hsub : (O a).filter (fun b => s b a') ∪ (O a ∩ O a') ⊆ O a :=
      Finset.union_subset (Finset.filter_subset _ _) Finset.inter_subset_left
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hOcard] at this
    exact this
  have claim1 : ∀ a a', ((O a).filter (fun b => s b a')).card +
      ((O a').filter (fun b => s b a)).card + (O a ∩ O a').card ≤ q := by
    intro a a'
    by_cases h1 : ((O a).filter (fun b => s b a')).card = 0
    · have := half a' a
      rw [Finset.inter_comm] at this
      omega
    by_cases h2 : ((O a').filter (fun b => s b a)).card = 0
    · have := half a a'
      omega
    exfalso
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h1)
    obtain ⟨b', hb'⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h2)
    rw [Finset.mem_filter] at hb hb'
    exact hne a b a' b' (hOr a b hb.1) hb.2 (hOr a' b' hb'.1) hb'.2
  have hsum1 : ∑ a, ∑ a', (((O a).filter (fun b => s b a')).card +
      ((O a').filter (fun b => s b a)).card + (O a ∩ O a').card) ≤
      Fintype.card A * Fintype.card A * q := by
    calc _ ≤ ∑ _a : A, ∑ _a' : A, q :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun a' _ => claim1 a a'
      _ = Fintype.card A * Fintype.card A * q := by
          simp [Finset.sum_const, Finset.card_univ]; ring
  have hsplit : ∑ a, ∑ a', (((O a).filter (fun b => s b a')).card +
      ((O a').filter (fun b => s b a)).card + (O a ∩ O a').card) =
      2 * ∑ a, ∑ a', ((O a).filter (fun b => s b a')).card +
        ∑ a, ∑ a', (O a ∩ O a').card := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a a' => ((O a').filter (fun b => s b a)).card)]
    ring
  -- the intersection sum is the sum of squared column counts
  have hinter : ∑ a, ∑ a', (O a ∩ O a').card =
      ∑ b, ((univ.filter (fun a => b ∈ O a)).card) ^ 2 := by
    have e1 : ∀ a a', (O a ∩ O a').card =
        ∑ b, (if b ∈ O a then 1 else 0) * (if b ∈ O a' then 1 else 0) := by
      intro a a'
      have hI : O a ∩ O a' = univ.filter (fun b => b ∈ O a ∧ b ∈ O a') := by
        ext b; simp
      rw [hI, Finset.card_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases h1 : b ∈ O a <;> by_cases h2 : b ∈ O a' <;> simp [h1, h2]
    simp_rw [e1, Finset.card_filter, sq, Finset.sum_mul_sum]
    exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
  have hf : ∑ b, (univ.filter (fun a => b ∈ O a)).card = Fintype.card A * q := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    simp [hOcard, Finset.sum_const, Finset.card_univ]
  have hCS := sq_sum_le_card_mul_sum_sq (s := (univ : Finset B))
    (f := fun b => (univ.filter (fun a => b ∈ O a)).card)
  rw [hf, Finset.card_univ, ← hinter] at hCS
  have hN : ∀ a, ∑ a', ((O a).filter (fun b => s b a')).card =
      ∑ b ∈ O a, (univ.filter (s b)).card := by
    intro a
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hNR : (Fintype.card A : ℝ) * (q * (α * Fintype.card A)) ≤
      ((∑ a, ∑ a', ((O a).filter (fun b => s b a')).card : ℕ) : ℝ) := by
    simp_rw [hN]
    push_cast
    have : ∀ a, (q : ℝ) * (α * Fintype.card A) ≤ ∑ b ∈ O a, ((univ.filter (s b)).card : ℝ) := by
      intro a
      have := Finset.sum_le_sum (s := O a) fun b _ => hs b
      simpa [Finset.sum_const, hOcard] using this
    have := Finset.sum_le_sum (s := (univ : Finset A)) fun a _ => this a
    simpa [Finset.sum_const, Finset.card_univ] using this
  have hmain : 2 * ∑ a, ∑ a', ((O a).filter (fun b => s b a')).card +
      ∑ a, ∑ a', (O a ∩ O a').card ≤ Fintype.card A * Fintype.card A * q := by
    rw [← hsplit]; exact hsum1
  have hmainR : 2 * ((∑ a, ∑ a', ((O a).filter (fun b => s b a')).card : ℕ) : ℝ) +
      ((∑ a, ∑ a', (O a ∩ O a').card : ℕ) : ℝ) ≤
      (Fintype.card A : ℝ) * Fintype.card A * q := by exact_mod_cast hmain
  have hCSR : ((Fintype.card A : ℝ) * q) ^ 2 ≤
      (Fintype.card B : ℝ) * ((∑ a, ∑ a', (O a ∩ O a').card : ℕ) : ℝ) := by
    exact_mod_cast hCS
  set X := ((∑ a, ∑ a', ((O a).filter (fun b => s b a')).card : ℕ) : ℝ)
  set I := ((∑ a, ∑ a', (O a ∩ O a').card : ℕ) : ℝ)
  set m := (Fintype.card A : ℝ)
  set n := (Fintype.card B : ℝ)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (mul_pos hβ hn) hqge
  have hM : 0 < m * m * q := by positivity
  -- n (2X + I) <= n m^2 q, n I >= m^2 q^2, X >= alpha m^2 q
  have h1 : n * (2 * (α * (m * m * q)) ) + (m * q) ^ 2 ≤ n * (m * m * q) := by
    nlinarith
  have h2 : (m * m * q) * (n * (2 * α) + q - n) ≤ 0 := by nlinarith
  have h3 : n * (2 * α) + q - n ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  nlinarith

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1809_08324.main := by
  intro h1 h2 k hk α β hα hβ hkab A B _ _ _ _ r s _ _ hr hs
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    have hab : 1 < α + β := by simpa using hkab
    obtain ⟨a₀, b₀, hr0, hs0⟩ := digon r s α β hab hr hs
    refine ⟨1, le_rfl, le_rfl, fun _ => a₀, fun _ => b₀, rfl, ?_⟩
    intro i _
    exact ⟨hr0, hs0⟩
  by_cases h2ab : 1 < 2 * α + β
  · obtain ⟨a₀, b₀, a₁, b₁, h1', h2', h3', h4'⟩ := four r s α β hα hβ h2ab hr hs
    refine ⟨2, by norm_num, hk2, fun i => if i = 1 then a₁ else a₀,
      fun i => if i = 1 then b₁ else b₀, by simp, ?_⟩
    intro i hi
    interval_cases i <;> simp_all
  push Not at h2ab
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · interval_cases k
    · exfalso
      have : (1 : ℝ) < 2 * α + β := by exact_mod_cast hkab
      linarith
    · have hab : 1 < 3 * α + β := by exact_mod_cast hkab
      exact h1 α β hα hβ hab h2ab A B r s hr hs
  · exact h2 k hk4 α β hα hβ hkab h2ab A B r s hr hs

end OMA.R_arxiv_1809_08324_R1
