import FormalConjectures.ErdosProblems.«138»
import Mathlib.NumberTheory.Bertrand

/-!
# Reduction of `Erdos138.erdos_138.variants.upper` (Gowers' Upper Bound for $W(k)$)

Following W. T. Gowers, *A new proof of Szemerédi's theorem*, Geom. Funct. Anal. 11 (2001),
465–588, we reduce Gowers' five-exponential van der Waerden bound
$$W(k) \le 2^{2^{2^{2^{2^{k+9}}}}}$$
to the two foundational pillars of Gowers' higher-order Fourier analysis:
1. (`H1`) The **generalized von Neumann theorem** (Gowers 2001, Theorem 3.2): the count of
   $k$-term arithmetic progressions in $\mathbb{Z}/P\mathbb{Z}$ ($P \ge k$ prime) weighted by
   $1$-bounded functions $f_0, \dots, f_{k-1}$ is controlled by the Gowers uniformity norm
   $\|f_{j_0}\|_{U^{k-1}(\mathbb{Z}/P\mathbb{Z})}$.
2. (`H2`) **Gowers' quantitative density increment from large $U^{k-1}$ norm** (Gowers 2001,
   Theorem 18.1 / Section 18): a subset $A \subseteq \{1, \dots, N\}$ of density $\delta \ge 1/2$
   whose balanced function has large $U^{k-1}$ norm in $\mathbb{Z}/P\mathbb{Z}$ ($2N < P \le 4N$
   prime) admits a density increment $\eta = 2^{-2^{3 \cdot 2^{k+7}}}$ on a subprogression of length
   at least $N^\eta$.

Inside `main`, we handle small $k \in \{0, 1, 2\}$ directly, prove the color-class pigeonhole
reduction, prove that non-trivial $k$-APs in $\{1, \dots, N\} \subseteq \mathbb{Z}/P\mathbb{Z}$
($P \ge 2N$) lift to genuine $k$-APs in $\mathbb{N}$ without wraparound, prove the telescoping
generalized von Neumann dichotomy from `H1`, and iterate `H2` over $2^{E-1}+1$ density-increment
steps ($E = 2^{3 \cdot 2^{k+7}}$) while tracking the exact five-exponential length lower bound.

Thanks to @MechaNuggan for the half-density color-class, affine pullback, and density-increment
iteration notes.
-/

-- Reduction Erdos138.erdos_138.variants.upper.R1 of Erdős Problem 138 — upper
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Finset
open scoped Classical BigOperators

namespace OMA.R_Erdos138_erdos_138_variants_upper_R1

/- ### Step 1: Arithmetic progressions in `ℕ`, color-class pigeonhole, and affine pullback -/

private def HasKAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ j < k, a + j * d ∈ A

private lemma hasKAP_to_monoAP {N k : ℕ} (coloring : Finset.Icc 1 N → Fin 2)
    (c : Fin 2) (A : Finset ℕ) (hA_sub : A ⊆ Finset.Icc 1 N)
    (hA_col : ∀ m : Finset.Icc 1 N, m.1 ∈ A → coloring m = c)
    (hAP : HasKAP A k) :
    ContainsMonoAPofLength coloring k := by
  obtain ⟨a, d, hd, hmem⟩ := hAP
  let ap : Set (Finset.Icc 1 N) := {m | ∃ j < k, m.1 = a + j * d}
  refine ⟨c, ap, ?_, ?_⟩
  · refine ⟨a, d, ?_, ?_⟩
    · have hinj : Function.Injective (fun j : Fin k => a + j.1 * d) := by
        intro j₁ j₂ h
        have hmul : j₁.1 * d = j₂.1 * d := Nat.add_left_cancel h
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd hmul)
      refine (congrArg (fun s : Set ℕ => ENat.card s)
          (a₂ := Set.range (fun j : Fin k => a + j.1 * d)) ?_).trans ?_
      · ext x
        constructor
        · rintro ⟨m, ⟨j, hjk, hmx⟩, rfl⟩
          exact ⟨⟨j, hjk⟩, hmx.symm⟩
        · rintro ⟨⟨j, hjk⟩, rfl⟩
          have hx : a + j * d ∈ Finset.Icc 1 N := hA_sub (hmem j hjk)
          exact ⟨⟨a + j * d, hx⟩, ⟨j, hjk, rfl⟩, rfl⟩
      · rw [ENat.card_congr (Equiv.ofInjective _ hinj).symm,
          ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    · ext x
      constructor
      · rintro ⟨m, ⟨j, hjk, hmx⟩, rfl⟩
        exact ⟨j, by exact_mod_cast hjk, by simpa [nsmul_eq_mul] using hmx.symm⟩
      · rintro ⟨j, hjk, rfl⟩
        have hjk' : j < k := by exact_mod_cast hjk
        have hx : a + j * d ∈ Finset.Icc 1 N := hA_sub (hmem j hjk')
        exact ⟨⟨a + j * d, hx⟩, ⟨j, hjk', rfl⟩, by simp⟩
  · intro m hm
    obtain ⟨j, hjk, hmx⟩ := hm
    exact hA_col m (hmx ▸ hmem j hjk)

private lemma pullback_hasKAP {M a d k : ℕ} {A : Finset ℕ} (hd : 0 < d)
    (hB : HasKAP ((Finset.Icc 1 M).filter fun i => a + i * d ∈ A) k) :
    HasKAP A k := by
  obtain ⟨b, r, hr, hmem⟩ := hB
  refine ⟨a + b * d, r * d, Nat.mul_pos hr hd, fun j hj => ?_⟩
  have h1 := (Finset.mem_filter.mp (hmem j hj)).2
  have heq : a + b * d + j * (r * d) = a + (b + j * r) * d := by ring
  rw [heq]
  exact h1

private lemma fin_two_cases (c : Fin 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma monoAP_of_k_le_two {N k : ℕ} (hN : 3 ≤ N) (hk : k ≤ 2)
    (coloring : Finset.Icc 1 N → Fin 2) :
    ContainsMonoAPofLength coloring k := by
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨0, ∅, ⟨0, 0, Set.IsAPOfLengthWith.zero.mpr (by simp)⟩,
      fun _ h => absurd h (Set.notMem_empty _)⟩
  by_cases hk1 : k = 1
  · subst hk1
    let x1 : Finset.Icc 1 N := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    refine ⟨coloring x1, {x1}, ⟨1, 0, Set.IsAPOfLengthWith.one.mpr (by simp [x1])⟩, ?_⟩
    intro m hm; rw [Set.mem_singleton_iff.mp hm]
  have hk2 : k = 2 := by omega
  subst hk2
  let x1 : Finset.Icc 1 N := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  let x2 : Finset.Icc 1 N := ⟨2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  let x3 : Finset.Icc 1 N := ⟨3, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hpair : ∀ (u v : Finset.Icc 1 N), u.1 < v.1 → coloring u = coloring v →
      ContainsMonoAPofLength coloring 2 := by
    intro u v huv hcol
    refine ⟨coloring u, {u, v}, ?_, ?_⟩
    · rw [Set.image_pair]
      exact Nat.isAPOfLength_pair huv
    · rintro m (rfl | rfl)
      · rfl
      · exact hcol.symm
  rcases fin_two_cases (coloring x1) with h1c | h1c <;>
  rcases fin_two_cases (coloring x2) with h2c | h2c <;>
  rcases fin_two_cases (coloring x3) with h3c | h3c
  · exact hpair x1 x2 (by norm_num : (1 : ℕ) < 2) (h1c.trans h2c.symm)
  · exact hpair x1 x2 (by norm_num : (1 : ℕ) < 2) (h1c.trans h2c.symm)
  · exact hpair x1 x3 (by norm_num : (1 : ℕ) < 3) (h1c.trans h3c.symm)
  · exact hpair x2 x3 (by norm_num : (2 : ℕ) < 3) (h2c.trans h3c.symm)
  · exact hpair x2 x3 (by norm_num : (2 : ℕ) < 3) (h2c.trans h3c.symm)
  · exact hpair x1 x3 (by norm_num : (1 : ℕ) < 3) (h1c.trans h3c.symm)
  · exact hpair x1 x2 (by norm_num : (1 : ℕ) < 2) (h1c.trans h2c.symm)
  · exact hpair x1 x2 (by norm_num : (1 : ℕ) < 2) (h1c.trans h2c.symm)

private lemma color_pigeonhole {N : ℕ} (coloring : Finset.Icc 1 N → Fin 2) :
    ∃ (c : Fin 2) (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ N ≤ 2 * A.card ∧
      ∀ m : Finset.Icc 1 N, m.1 ∈ A → coloring m = c := by
  let S0 : Finset ℕ := (Finset.Icc 1 N).filter fun x =>
    if hx : x ∈ Finset.Icc 1 N then coloring ⟨x, hx⟩ = 0 else False
  let S1 : Finset ℕ := (Finset.Icc 1 N).filter fun x =>
    if hx : x ∈ Finset.Icc 1 N then coloring ⟨x, hx⟩ = 1 else False
  have hunion : S0 ∪ S1 = Finset.Icc 1 N := by
    ext x
    simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases fin_two_cases (coloring ⟨x, hx⟩) with h0 | h1
      · exact Or.inl ⟨hx, by simp [hx, h0]⟩
      · exact Or.inr ⟨hx, by simp [hx, h1]⟩
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    have h0 := (Finset.mem_filter.mp hx0).2
    have h1 := (Finset.mem_filter.mp hx1).2
    have hx := (Finset.mem_filter.mp hx0).1
    simp only [hx, ↓reduceDIte] at h0 h1
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hsum : S0.card + S1.card = N := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Nat.card_Icc]
    omega
  by_cases hle : S1.card ≤ S0.card
  · refine ⟨0, S0, Finset.filter_subset _ _, by omega, fun m hm => ?_⟩
    have h0 := (Finset.mem_filter.mp hm).2
    simpa [m.2] using h0
  · refine ⟨1, S1, Finset.filter_subset _ _, by omega, fun m hm => ?_⟩
    have h1 := (Finset.mem_filter.mp hm).2
    simpa [m.2] using h1

/- ### Step 2: No-wraparound lift of modular $k$-APs from $\mathbb{Z}/P\mathbb{Z}$ ($P \ge 2N$) -/

private lemma zmod_ap_lift {N P k : ℕ} (hk : 3 ≤ k) (hP : 2 * N ≤ P)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (x r : ZMod P) (hr : r ≠ 0)
    (hmem : ∀ j : Fin k, (x + (j.1 : ZMod P) * r).val ∈ A) :
    HasKAP A k := by
  have hPpos : 0 < P := by
    have hmem0 := hA (hmem ⟨0, by omega⟩)
    have h1N : 1 ≤ N := by
      have := Finset.mem_Icc.mp hmem0; omega
    omega
  have : NeZero P := ⟨hPpos.ne'⟩
  let a : ℕ → ℕ := fun j => (x + (j : ZMod P) * r).val
  have ha_mem : ∀ j < k, a j ∈ A := fun j hj => hmem ⟨j, hj⟩
  have ha_le : ∀ j < k, 1 ≤ a j ∧ a j ≤ N := fun j hj => Finset.mem_Icc.mp (hA (ha_mem j hj))
  have ha_cast : ∀ j : ℕ, ((a j : ℤ) : ZMod P) = x + (j : ZMod P) * r := fun j => by
    dsimp [a]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  let Δ : ℤ := (a 1 : ℤ) - (a 0 : ℤ)
  have hΔ_mod : (Δ : ZMod P) = r := by
    dsimp [Δ]
    rw [Int.cast_sub, ha_cast 1, ha_cast 0]
    simp
  have hΔ_ne : Δ ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hΔ_mod
    exact hr hΔ_mod.symm
  have hstep : ∀ j, j + 1 < k → (a (j + 1) : ℤ) - (a j : ℤ) = Δ := by
    intro j hj
    have h1 := ha_le j (by omega)
    have h2 := ha_le (j + 1) hj
    have h0 := ha_le 0 (by omega)
    have h1' := ha_le 1 (by omega)
    have hmod : ((((a (j + 1) : ℤ) - (a j : ℤ) - Δ) : ℤ) : ZMod P) = 0 := by
      rw [Int.cast_sub, Int.cast_sub, ha_cast (j + 1), ha_cast j, hΔ_mod]
      push_cast
      ring
    have hdvd : (P : ℤ) ∣ ((a (j + 1) : ℤ) - (a j : ℤ) - Δ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).mp hmod
    have habs : ((a (j + 1) : ℤ) - (a j : ℤ) - Δ).natAbs < P := by
      dsimp [Δ]; omega
    by_contra hne
    have hne0 : (a (j + 1) : ℤ) - (a j : ℤ) - Δ ≠ 0 := sub_ne_zero.mpr hne
    have hdvd_nat : P ∣ ((a (j + 1) : ℤ) - (a j : ℤ) - Δ).natAbs := Int.natCast_dvd.mp hdvd
    have hpos : 0 < ((a (j + 1) : ℤ) - (a j : ℤ) - Δ).natAbs := Int.natAbs_pos.mpr hne0
    exact absurd (Nat.le_of_dvd hpos hdvd_nat) (by omega)
  have hlin : ∀ j < k, (a j : ℤ) = (a 0 : ℤ) + (j : ℤ) * Δ := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hs := hstep m hm
      push_cast
      linarith
  rcases lt_or_gt_of_ne hΔ_ne with hneg | hpos
  · let d : ℕ := (-Δ).toNat
    have hd_pos : 0 < d := by dsimp [d]; omega
    have hd_eq : (d : ℤ) = -Δ := Int.toNat_of_nonneg (by omega)
    refine ⟨a (k - 1), d, hd_pos, fun j hj => ?_⟩
    have h1 := hlin (k - 1) (by omega)
    have h2 := hlin (k - 1 - j) (by omega)
    have heqZ : ((a (k - 1) + j * d : ℕ) : ℤ) = (a (k - 1 - j) : ℤ) := by
      push_cast
      rw [h1, h2, hd_eq]
      have hsub : ((k - 1 - j : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) - (j : ℤ) := by omega
      rw [hsub]; ring
    have heqN : a (k - 1) + j * d = a (k - 1 - j) := by exact_mod_cast heqZ
    rw [heqN]
    exact ha_mem (k - 1 - j) (by omega)
  · let d : ℕ := Δ.toNat
    have hd_pos : 0 < d := by dsimp [d]; omega
    have hd_eq : (d : ℤ) = Δ := Int.toNat_of_nonneg (by omega)
    refine ⟨a 0, d, hd_pos, fun j hj => ?_⟩
    have h2 := hlin j hj
    have heqZ : ((a 0 + j * d : ℕ) : ℤ) = (a j : ℤ) := by
      push_cast; rw [h2, hd_eq]
    have heqN : a 0 + j * d = a j := by exact_mod_cast heqZ
    rw [heqN]
    exact ha_mem j hj

/- ### Step 3: Telescoping Generalized von Neumann dichotomy -/

private lemma prod_sub_prod_telescope {k : ℕ} (u v : Fin k → ℝ) :
    (∏ j : Fin k, u j) - (∏ j : Fin k, v j) =
      ∑ m : Fin k, ∏ j : Fin k, if j < m then u j else if j = m then u j - v j else v j := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
    have hsplit : (∏ i : Fin n, u i.castSucc) * u (Fin.last n) -
        (∏ i : Fin n, v i.castSucc) * v (Fin.last n) =
        ((∏ i : Fin n, u i.castSucc) - (∏ i : Fin n, v i.castSucc)) * v (Fin.last n) +
        (∏ i : Fin n, u i.castSucc) * (u (Fin.last n) - v (Fin.last n)) := by ring
    rw [hsplit, ih (fun i => u i.castSucc) (fun i => v i.castSucc), Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [Fin.prod_univ_castSucc]
      have hlast : ¬ (Fin.last n < m.castSucc) ∧ Fin.last n ≠ m.castSucc :=
        ⟨not_lt_of_ge (Fin.le_last _), (Fin.castSucc_lt_last m).ne'⟩
      simp only [hlast.1, hlast.2, ↓reduceIte]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]
    · rw [Fin.prod_univ_castSucc]
      simp only [lt_irrefl, ↓reduceIte]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      have hlt : j.castSucc < Fin.last n := Fin.castSucc_lt_last j
      simp [hlt]

private lemma gvn_dichotomy
    (h1 : ∀ (k : ℕ), 3 ≤ k → ∀ (P : ℕ) [NeZero P], P.Prime → k ≤ P →
      ∀ (f : Fin k → ZMod P → ℝ), (∀ j x, |f j x| ≤ 1) → ∀ j₀ : Fin k,
        |((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
            ∏ j : Fin k, f j (x + (j.1 : ZMod P) * r)| ^ (2 ^ (k - 1)) ≤
          ((P : ℝ) ^ k)⁻¹ * ∑ x : ZMod P, ∑ h : Fin (k - 1) → ZMod P,
            ∏ ω : Fin (k - 1) → Bool,
              f j₀ (x + ∑ i : Fin (k - 1), if ω i then h i else 0))
    {k N P : ℕ} [NeZero P] (hk : 3 ≤ k) (hN : 1024 * k * 2 ^ k ≤ N)
    (hP_prime : P.Prime) (hP_lo : 2 * N < P) (hP_hi : P ≤ 4 * N)
    (A : Finset ℕ) (hA_sub : A ⊆ Finset.Icc 1 N) (hA_dens : N ≤ 2 * A.card)
    (hNoAP : ¬ HasKAP A k) :
    let δ : ℝ := (A.card : ℝ) / (N : ℝ)
    let f : ZMod P → ℝ := fun x =>
      (if x.val ∈ A then (1 : ℝ) else 0) - δ * (if x.val ∈ Finset.Icc 1 N then (1 : ℝ) else 0)
    (1 / (256 * (k : ℝ) ^ 2 * (2 : ℝ) ^ k)) ^ (2 ^ (k - 1)) ≤
      ((P : ℝ) ^ k)⁻¹ * ∑ x : ZMod P, ∑ h : Fin (k - 1) → ZMod P,
        ∏ ω : Fin (k - 1) → Bool,
          f (x + ∑ i : Fin (k - 1), if ω i then h i else 0) := by
  intro δ f
  have hNpos : 0 < N := by
    have : 0 < 2 ^ k := by positivity
    nlinarith
  have hPpos : 0 < P := by omega
  have : NeZero P := ⟨hPpos.ne'⟩
  have hk_le_P : k ≤ P := by
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    nlinarith
  have hA_le_N : A.card ≤ N := by
    calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA_sub
      _ = N := by rw [Nat.card_Icc]; omega
  have hδ_lo : (1 / 2 : ℝ) ≤ δ := by
    dsimp [δ]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (N : ℝ) ≤ 2 * (A.card : ℝ) := by exact_mod_cast hA_dens
    linarith
  have hδ_hi : δ ≤ 1 := by
    dsimp [δ]
    rw [div_le_one (by positivity)]
    exact_mod_cast hA_le_N
  let gA : ZMod P → ℝ := fun x => if x.val ∈ A then 1 else 0
  let gI : ZMod P → ℝ := fun x => if x.val ∈ Finset.Icc 1 N then 1 else 0
  let gB : ZMod P → ℝ := fun x => δ * gI x
  have hf_eq : ∀ x, f x = gA x - gB x := fun _ => rfl
  have hgA_bd : ∀ x, |gA x| ≤ 1 := fun x => by dsimp [gA]; split_ifs <;> norm_num
  have hgB_bd : ∀ x, |gB x| ≤ 1 := fun x => by
    dsimp [gB, gI]; split_ifs
    · rw [mul_one, abs_of_nonneg (by linarith)]; exact hδ_hi
    · simp
  have hδ_nn : 0 ≤ δ := by linarith
  have hf_bd : ∀ x, |f x| ≤ 1 := fun x => by
    rw [hf_eq]
    dsimp [gA, gB, gI]
    by_cases hxA : x.val ∈ A
    · have hxI : x.val ∈ Finset.Icc 1 N := hA_sub hxA
      simp only [hxA, hxI, ↓reduceIte, mul_one]
      rw [abs_le]; constructor <;> linarith
    · split_ifs
      · rw [zero_sub, mul_one, abs_neg, abs_of_nonneg hδ_nn]; exact hδ_hi
      · simp
  -- Upper bound on k-APs in A: only r = 0 can contribute
  have hcountA : ((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
      ∏ j : Fin k, gA (x + (j.1 : ZMod P) * r) ≤ 1 / (4 * (N : ℝ)) := by
    have hinner : ∀ x : ZMod P,
        ∑ r : ZMod P, ∏ j : Fin k, gA (x + (j.1 : ZMod P) * r) = gA x := by
      intro x
      rw [Finset.sum_eq_single (0 : ZMod P)]
      · simp only [mul_zero, add_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        dsimp [gA]; split_ifs <;> simp [show k ≠ 0 by omega]
      · intro r _ hr0
        by_contra hne
        have hall : ∀ j : Fin k, (x + (j.1 : ZMod P) * r).val ∈ A := by
          intro j
          by_contra hnot
          apply hne
          refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
          dsimp [gA]; rw [if_neg hnot]
        exact hNoAP (zmod_ap_lift hk (by omega) A hA_sub x r hr0 hall)
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hinner]
    have hsumA : ∑ x : ZMod P, gA x ≤ (N : ℝ) := by
      have hcard : (Finset.univ.filter fun x : ZMod P => x.val ∈ A).card ≤ A.card := by
        refine Finset.card_le_card_of_injOn (fun x : ZMod P => x.val) ?_ ?_
        · intro x hx; exact Finset.mem_coe.mpr (Finset.mem_filter.mp hx).2
        · intro x₁ _ x₂ _ h; exact ZMod.val_injective P h
      have heq : ∑ x : ZMod P, gA x =
          ((Finset.univ.filter fun x : ZMod P => x.val ∈ A).card : ℝ) := by
        dsimp [gA]
        rw [Finset.sum_boole]
      rw [heq]
      exact_mod_cast hcard.trans hA_le_N
    have hP2_ge : (4 : ℝ) * (N : ℝ) ^ 2 ≤ (P : ℝ) ^ 2 := by
      have h2N : (2 : ℝ) * (N : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP_lo.le
      nlinarith
    have hP2_pos : (0 : ℝ) < (P : ℝ) ^ 2 := by positivity
    calc
      ((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, gA x
          ≤ ((P : ℝ) ^ 2)⁻¹ * (N : ℝ) := mul_le_mul_of_nonneg_left hsumA (by positivity)
      _ ≤ (4 * (N : ℝ) ^ 2)⁻¹ * (N : ℝ) :=
            mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) hP2_ge) (by positivity)
      _ = 1 / (4 * (N : ℝ)) := by field_simp [show (N : ℝ) ≠ 0 by positivity]
  -- Lower bound on k-APs in I = [1, N]
  have hcountB : δ ^ k / (128 * (k : ℝ)) ≤
      ((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
        ∏ j : Fin k, gB (x + (j.1 : ZMod P) * r) := by
    have hprodB : ∀ x r : ZMod P,
        ∏ j : Fin k, gB (x + (j.1 : ZMod P) * r) =
          δ ^ k * ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) := by
      intro x r
      dsimp [gB]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp_rw [hprodB, ← Finset.mul_sum]
    let BoxX : Finset (ZMod P) := (Finset.Icc 1 (N / 2)).image (fun n : ℕ => (n : ZMod P))
    let BoxR : Finset (ZMod P) := (Finset.Icc 1 (N / (2 * k))).image (fun n : ℕ => (n : ZMod P))
    have hinjX : Set.InjOn (fun n : ℕ => (n : ZMod P)) (Finset.Icc 1 (N / 2) : Set ℕ) := by
      intro a ha b hb h
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      have h1 := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
      exact h1
    have hinjR : Set.InjOn (fun n : ℕ => (n : ZMod P)) (Finset.Icc 1 (N / (2 * k)) : Set ℕ) := by
      intro a ha b hb h
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      have hdiv_le : N / (2 * k) ≤ N := Nat.div_le_self N (2 * k)
      have h1 := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
      exact h1
    have hBoxX_card : BoxX.card = N / 2 := by
      rw [Finset.card_image_of_injOn hinjX, Nat.card_Icc]; omega
    have hBoxR_card : BoxR.card = N / (2 * k) := by
      rw [Finset.card_image_of_injOn hinjR, Nat.card_Icc]; exact Nat.add_sub_cancel _ 1
    have hbox_one : ∀ x ∈ BoxX, ∀ r ∈ BoxR, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) = 1 := by
      intro x hx r hr
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hr
      have ha' := Finset.mem_Icc.mp ha
      have hd' := Finset.mem_Icc.mp hd
      refine Finset.prod_eq_one fun j _ => ?_
      have hjd : j.1 * d ≤ N / 2 := by
        calc j.1 * d ≤ k * (N / (2 * k)) := Nat.mul_le_mul j.2.le hd'.2
          _ ≤ N / 2 := by
            have hmul : 2 * (k * (N / (2 * k))) ≤ N := by
              rw [← mul_assoc]; exact Nat.mul_div_le N (2 * k)
            omega
      have hlt : a + j.1 * d < P := by omega
      have hval : ((a : ZMod P) + (j.1 : ZMod P) * (d : ZMod P)).val = a + j.1 * d := by
        have heq : (a : ZMod P) + (j.1 : ZMod P) * (d : ZMod P) = ((a + j.1 * d : ℕ) : ZMod P) := by
          push_cast; ring
        rw [heq, ZMod.val_natCast_of_lt hlt]
      dsimp [gI]
      rw [hval, if_pos (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    have hsumI_ge : (N : ℝ) ^ 2 / (8 * (k : ℝ)) ≤
        ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) := by
      have hnn : ∀ x r : ZMod P, 0 ≤ ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) := fun x r =>
        Finset.prod_nonneg fun j _ => by dsimp [gI]; split_ifs <;> norm_num
      have h1 : ∑ x ∈ BoxX, ∑ r ∈ BoxR, (1 : ℝ) ≤
          ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) := by
        calc
          ∑ x ∈ BoxX, ∑ r ∈ BoxR, (1 : ℝ)
              = ∑ x ∈ BoxX, ∑ r ∈ BoxR, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) := by
                refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun r hr => ?_
                exact (hbox_one x hx r hr).symm
          _ ≤ ∑ x ∈ BoxX, ∑ r : ZMod P, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) :=
                Finset.sum_le_sum fun x _ =>
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun r _ _ => hnn x r
          _ ≤ ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ =>
                  Finset.sum_nonneg fun r _ => hnn x r
      have h2 : ∑ x ∈ BoxX, ∑ r ∈ BoxR, (1 : ℝ) = ((N / 2 : ℕ) : ℝ) * ((N / (2 * k) : ℕ) : ℝ) := by
        simp [hBoxX_card, hBoxR_card]
      have h4k : 4 * k ≤ N := by
        have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
        nlinarith
      have hN2 : (N : ℝ) / 3 ≤ ((N / 2 : ℕ) : ℝ) := by
        have : 3 * (N / 2) ≥ N := by omega
        have : (N : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hN2k : (N : ℝ) / (2.5 * (k : ℝ)) ≤ ((N / (2 * k) : ℕ) : ℝ) := by
        have hdiv : N - 2 * k ≤ (2 * k) * (N / (2 * k)) := by
          have := Nat.div_add_mod N (2 * k)
          have hmod := Nat.mod_lt N (show 0 < 2 * k by omega)
          omega
        have hdivR : (N : ℝ) - 2 * (k : ℝ) ≤ 2 * (k : ℝ) * ((N / (2 * k) : ℕ) : ℝ) := by
          have : N ≤ 2 * k + 2 * k * (N / (2 * k)) := by omega
          have hcast : (N : ℝ) ≤ 2 * (k : ℝ) + 2 * (k : ℝ) * ((N / (2 * k) : ℕ) : ℝ) := by
            exact_mod_cast this
          linarith
        have h16k : 10 * (k : ℝ) ≤ (N : ℝ) := by
          have : 10 * k ≤ N := by
            have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
            nlinarith
          exact_mod_cast this
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have hprod_ge : (N : ℝ) ^ 2 / (8 * (k : ℝ)) ≤ ((N / 2 : ℕ) : ℝ) * ((N / (2 * k) : ℕ) : ℝ) := by
        have hmul := mul_le_mul hN2 hN2k (by positivity) (by positivity)
        have h75 : (N : ℝ) ^ 2 / (8 * (k : ℝ)) ≤ (N : ℝ) / 3 * ((N : ℝ) / (2.5 * (k : ℝ))) := by
          rw [div_mul_div_comm]
          have : (3 : ℝ) * (2.5 * (k : ℝ)) = 7.5 * (k : ℝ) := by ring
          rw [this]
          have h75le : (7.5 : ℝ) * (k : ℝ) ≤ 8 * (k : ℝ) := by linarith
          have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
          calc
            (N : ℝ) ^ 2 / (8 * (k : ℝ))
                = (N : ℝ) * (N : ℝ) / (8 * (k : ℝ)) := by rw [sq]
            _ ≤ (N : ℝ) * (N : ℝ) / (7.5 * (k : ℝ)) :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) h75le
        exact h75.trans hmul
      linarith
    have hP2_le : (P : ℝ) ^ 2 ≤ 16 * (N : ℝ) ^ 2 := by
      have : (P : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hP_hi
      nlinarith
    have hdiv_ge : (1 : ℝ) / (128 * (k : ℝ)) ≤
        ((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) := by
      calc
        (1 : ℝ) / (128 * (k : ℝ))
            = (16 * (N : ℝ) ^ 2)⁻¹ * ((N : ℝ) ^ 2 / (8 * (k : ℝ))) := by
              field_simp [show (N : ℝ) ≠ 0 by positivity, show (k : ℝ) ≠ 0 by positivity]
              ring
        _ ≤ ((P : ℝ) ^ 2)⁻¹ * ((N : ℝ) ^ 2 / (8 * (k : ℝ))) :=
              mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) hP2_le) (by positivity)
        _ ≤ ((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r) :=
              mul_le_mul_of_nonneg_left hsumI_ge (by positivity)
    have hmul_δ := mul_le_mul_of_nonneg_left hdiv_ge (pow_nonneg (by linarith : (0 : ℝ) ≤ δ) k)
    calc
      δ ^ k / (128 * (k : ℝ)) = δ ^ k * (1 / (128 * (k : ℝ))) := by ring
      _ ≤ δ ^ k * (((P : ℝ) ^ 2)⁻¹ *
            ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r)) := hmul_δ
      _ = ((P : ℝ) ^ 2)⁻¹ * (δ ^ k *
            ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin k, gI (x + (j.1 : ZMod P) * r)) := by ring
  -- Now deduce the U^{k-1} lower bound by contradiction using telescoping + H1
  by_contra hlt
  push Not at hlt
  let γ : ℝ := 1 / (256 * (k : ℝ) ^ 2 * (2 : ℝ) ^ k)
  have hγ_pos : 0 < γ := by dsimp [γ]; positivity
  have hterm_lt : ∀ m : Fin k,
      |((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
          ∏ j : Fin k, (if j < m then gA else if j = m then f else gB) (x + (j.1 : ZMod P) * r)| < γ := by
    intro m
    let fm : Fin k → ZMod P → ℝ := fun j => if j < m then gA else if j = m then f else gB
    have hfm_bd : ∀ j x, |fm j x| ≤ 1 := by
      intro j x; dsimp [fm]; split_ifs
      · exact hgA_bd x
      · exact hf_bd x
      · exact hgB_bd x
    have hfm_m : fm m = f := by
      dsimp [fm]; simp
    have hgvn := h1 k hk P hP_prime hk_le_P fm hfm_bd m
    rw [hfm_m] at hgvn
    have hpow_lt : |((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
        ∏ j : Fin k, fm j (x + (j.1 : ZMod P) * r)| ^ (2 ^ (k - 1)) < γ ^ (2 ^ (k - 1)) :=
      hgvn.trans_lt hlt
    by_contra hge
    push Not at hge
    have hpow_ge : γ ^ (2 ^ (k - 1)) ≤ |((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
        ∏ j : Fin k, fm j (x + (j.1 : ZMod P) * r)| ^ (2 ^ (k - 1)) :=
      pow_le_pow_left₀ hγ_pos.le hge _
    linarith
  have hdiff_eq :
      (((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin k, gA (x + (j.1 : ZMod P) * r)) -
      (((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin k, gB (x + (j.1 : ZMod P) * r)) =
      ∑ m : Fin k, ((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
        ∏ j : Fin k, (if j < m then gA else if j = m then f else gB) (x + (j.1 : ZMod P) * r) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    have hpt : ∀ x r : ZMod P,
        (∏ j : Fin k, gA (x + (j.1 : ZMod P) * r)) - (∏ j : Fin k, gB (x + (j.1 : ZMod P) * r)) =
        ∑ m : Fin k, ∏ j : Fin k,
          (if j < m then gA else if j = m then f else gB) (x + (j.1 : ZMod P) * r) := by
      intro x r
      have ht := prod_sub_prod_telescope (fun j : Fin k => gA (x + (j.1 : ZMod P) * r))
        (fun j : Fin k => gB (x + (j.1 : ZMod P) * r))
      rw [ht]
      refine Finset.sum_congr rfl fun m _ => Finset.prod_congr rfl fun j _ => ?_
      split_ifs <;> rfl
    simp_rw [hpt]
    have hcomm2 : ∑ x : ZMod P, ∑ m : Fin k, ∑ r : ZMod P,
        ∏ j : Fin k, (if j < m then gA else if j = m then f else gB) (x + (j.1 : ZMod P) * r) =
        ∑ m : Fin k, ∑ x : ZMod P, ∑ r : ZMod P,
        ∏ j : Fin k, (if j < m then gA else if j = m then f else gB) (x + (j.1 : ZMod P) * r) :=
      Finset.sum_comm
    have hinner_comm : ∀ x : ZMod P,
        ∑ r : ZMod P, ∑ m : Fin k,
          ∏ j : Fin k, (if j < m then gA else if j = m then f else gB) (x + (j.1 : ZMod P) * r) =
        ∑ m : Fin k, ∑ r : ZMod P,
          ∏ j : Fin k, (if j < m then gA else if j = m then f else gB) (x + (j.1 : ZMod P) * r) :=
      fun _ => Finset.sum_comm
    simp_rw [hinner_comm]
    rw [hcomm2, Finset.mul_sum]
  have hdiff_lt : |(((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
        ∏ j : Fin k, gA (x + (j.1 : ZMod P) * r)) -
      (((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
        ∏ j : Fin k, gB (x + (j.1 : ZMod P) * r))| < (k : ℝ) * γ := by
    rw [hdiff_eq]
    calc
      |∑ m : Fin k, ((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
          ∏ j : Fin k, (if j < m then gA else if j = m then f else gB) (x + (j.1 : ZMod P) * r)|
          ≤ ∑ m : Fin k, |((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
              ∏ j : Fin k, (if j < m then gA else if j = m then f else gB) (x + (j.1 : ZMod P) * r)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _m : Fin k, γ :=
            Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩)
              fun m _ => hterm_lt m
      _ = (k : ℝ) * γ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hδk_ge : (1 : ℝ) / (2 : ℝ) ^ k ≤ δ ^ k := by
    calc (1 : ℝ) / (2 : ℝ) ^ k = (1 / 2 : ℝ) ^ k := by rw [one_div_pow]
      _ ≤ δ ^ k := pow_le_pow_left₀ (by norm_num) hδ_lo k
  have hkγ_le : (k : ℝ) * γ ≤ δ ^ k / (256 * (k : ℝ)) := by
    have heq : (k : ℝ) * γ = (1 / (2 : ℝ) ^ k) / (256 * (k : ℝ)) := by
      dsimp [γ]; field_simp [show (k : ℝ) ≠ 0 by positivity]
    rw [heq]
    exact div_le_div_of_nonneg_right hδk_ge (by positivity)
  have h4N_le : 1 / (4 * (N : ℝ)) ≤ δ ^ k / (256 * (k : ℝ)) := by
    have hNR : (1024 : ℝ) * (k : ℝ) * (2 : ℝ) ^ k ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 : 1 / (4 * (N : ℝ)) ≤ (1 / (2 : ℝ) ^ k) / (256 * (k : ℝ)) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact h1.trans (div_le_div_of_nonneg_right hδk_ge (by positivity))
  have hneg : ((((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
      ∏ j : Fin k, gB (x + (j.1 : ZMod P) * r)) -
      (((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
      ∏ j : Fin k, gA (x + (j.1 : ZMod P) * r))) ≤
      |(((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
        ∏ j : Fin k, gA (x + (j.1 : ZMod P) * r)) -
      (((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
        ∏ j : Fin k, gB (x + (j.1 : ZMod P) * r))| := by
    rw [abs_sub_comm]; exact le_abs_self _
  have hhalf_k : δ ^ k / (128 * (k : ℝ)) = δ ^ k / (256 * (k : ℝ)) + δ ^ k / (256 * (k : ℝ)) := by
    ring
  linarith

/- ### Step 4: Five-exponential tower arithmetic and density-increment iteration -/

private lemma tower_step_budget (k : ℕ) (hk : 3 ≤ k) :
    let E := 2 ^ (3 * 2 ^ (k + 7))
    let e3 := 2 ^ (2 ^ (2 ^ (k + 9)))
    (2 ^ (E - 1) + 1) * E + 2 ^ (2 ^ (k + 8)) ≤ e3 := by
  intro E e3
  let b := 2 ^ (k + 7)
  have hb : 1024 ≤ b := by
    have : 2 ^ 10 ≤ 2 ^ (k + 7) := Nat.pow_le_pow_right (by omega) (by omega)
    simpa [b] using this
  have hE_eq : E = 2 ^ (3 * b) := rfl
  have hE_ge4 : 4 ≤ E := by
    have : 2 ^ 2 ≤ 2 ^ (3 * b) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h2E_le : 2 * E + 2 ≤ 2 ^ (4 * b) := by
    have h1 : 2 * E = 2 ^ (3 * b + 1) := by rw [hE_eq, pow_succ, mul_comm]
    have h2 : 2 ^ (3 * b + 1) + 2 ^ (3 * b + 1) ≤ 2 ^ (4 * b) := by
      have h3 : 2 ^ (3 * b + 1) + 2 ^ (3 * b + 1) = 2 ^ (3 * b + 2) := by
        rw [pow_succ]; ring
      rw [h3]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 2 ≤ 2 ^ (3 * b + 1) := by omega
    omega
  have hprod_le : (2 ^ (E - 1) + 1) * E ≤ 2 ^ (2 * E) := by
    have h1 : 2 ^ (E - 1) + 1 ≤ 2 ^ E := by
      have : 2 ^ E = 2 ^ (E - 1) + 2 ^ (E - 1) := by
        conv_lhs => rw [show E = (E - 1) + 1 by omega, pow_succ]
        ring
      have hpos : 1 ≤ 2 ^ (E - 1) := Nat.one_le_pow _ 2 (by omega)
      omega
    have h2 : E ≤ 2 ^ E := le_of_lt Nat.lt_two_pow_self
    calc
      (2 ^ (E - 1) + 1) * E ≤ 2 ^ E * 2 ^ E := Nat.mul_le_mul h1 h2
      _ = 2 ^ (2 * E) := by rw [← pow_add, two_mul]
  have he3_eq : e3 = 2 ^ (2 ^ (4 * b)) := by
    dsimp [e3, b]
    congr 2
    rw [show k + 9 = (k + 7) + 2 by omega, pow_add]
    ring
  have hpow1 : 2 ^ (2 * E) ≤ 2 ^ (2 ^ (4 * b) - 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hpow2 : 2 ^ (2 ^ (k + 8)) ≤ 2 ^ (2 ^ (4 * b) - 2) := by
    refine Nat.pow_le_pow_right (by omega) ?_
    have h2b : 2 ^ (k + 8) = 2 * b := by
      dsimp [b]; rw [show k + 8 = (k + 7) + 1 by omega, pow_succ]; ring
    rw [h2b]
    have hle : 2 * b + 2 ≤ 2 ^ (4 * b) := by
      have : 4 * b < 2 ^ (4 * b) := Nat.lt_two_pow_self
      omega
    omega
  have hsum_le : 2 ^ (2 ^ (4 * b) - 2) + 2 ^ (2 ^ (4 * b) - 2) ≤ 2 ^ (2 ^ (4 * b)) := by
    have hge2 : 2 ≤ 2 ^ (4 * b) := by omega
    have hrewrite : 2 ^ (4 * b) = (2 ^ (4 * b) - 2) + 2 := by omega
    conv_rhs => rw [hrewrite, pow_add]
    have : 2 ^ 2 = 4 := by norm_num
    rw [this]; omega
  rw [he3_eq]
  omega

private lemma floor_threshold_bound (k : ℕ) (hk : 3 ≤ k) :
    1024 * k * 2 ^ k ≤ 2 ^ (2 ^ (2 ^ (2 ^ (k + 8)))) := by
  have h1 : 1024 * k * 2 ^ k ≤ 2 ^ (2 * k + 10) := by
    have hk_le : k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
    calc
      1024 * k * 2 ^ k ≤ 2 ^ 10 * 2 ^ k * 2 ^ k := by
        have : 1024 = 2 ^ 10 := by norm_num
        rw [this]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk_le)
      _ = 2 ^ (2 * k + 10) := by rw [← pow_add, ← pow_add]; congr 1; ring
  have h2 : 2 * k + 10 ≤ 2 ^ (k + 8) := by
    have : ∀ m, m + 1 ≤ 2 ^ m := fun m => Nat.lt_two_pow_self
    have h3 : 2 * k + 10 ≤ 2 * (k + 8) := by omega
    have h4 : 2 * (k + 8) ≤ 2 ^ (k + 8) := by
      have : ∀ m, 3 ≤ m → 2 * m ≤ 2 ^ m := by
        intro m hm
        induction m with
        | zero => omega
        | succ n ih =>
          by_cases hn3 : 3 ≤ n
          · have := ih hn3; rw [pow_succ]; omega
          · have : n = 2 := by omega
            subst this; norm_num
      exact this (k + 8) (by omega)
    omega
  have h3 : 2 ^ (k + 8) ≤ 2 ^ (2 ^ (k + 8)) := le_of_lt Nat.lt_two_pow_self
  have h4 : 2 ^ (2 ^ (k + 8)) ≤ 2 ^ (2 ^ (2 ^ (k + 8))) := le_of_lt Nat.lt_two_pow_self
  exact h1.trans (Nat.pow_le_pow_right (by omega) (h2.trans (h3.trans h4)))

/- ### Hypotheses and main reduction theorem -/

/-- Generalized von Neumann theorem (Gowers 2001, Theorem 3.2): for every $k \ge 3$, prime $P \ge k$,
and $1$-bounded functions $f_0, \dots, f_{k-1} : \mathbb{Z}/P\mathbb{Z} \to [-1, 1]$, the
$k$-AP counting average is bounded by $\|f_{j_0}\|_{U^{k-1}(\mathbb{Z}/P\mathbb{Z})}$. -/
def H1 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (P : ℕ) [NeZero P], P.Prime → k ≤ P →
    ∀ (f : Fin k → ZMod P → ℝ), (∀ j x, |f j x| ≤ 1) → ∀ j₀ : Fin k,
      |((P : ℝ) ^ 2)⁻¹ * ∑ x : ZMod P, ∑ r : ZMod P,
          ∏ j : Fin k, f j (x + (j.1 : ZMod P) * r)| ^ (2 ^ (k - 1)) ≤
        ((P : ℝ) ^ k)⁻¹ * ∑ x : ZMod P, ∑ h : Fin (k - 1) → ZMod P,
          ∏ ω : Fin (k - 1) → Bool,
            f j₀ (x + ∑ i : Fin (k - 1), if ω i then h i else 0)

/-- Gowers' quantitative density increment from large $U^{k-1}$ norm (Gowers 2001, Theorem 18.1 /
Section 18): if $A \subseteq \{1, \dots, N\}$ has density $\delta \ge 1/2$, $N \ge 2^{2^{2^{2^{k+8}}}}$,
$P \in (2N, 4N]$ is prime, and the balanced function $f_A = 1_A - \delta 1_{[1, N]}$ has
$\|f_A\|_{U^{k-1}(\mathbb{Z}/P\mathbb{Z})} \ge (256 k^2 2^k)^{-1}$, then $A$ has a density
increment of at least $\eta = 2^{-2^{3 \cdot 2^{k+7}}}$ on a subprogression of length at least $N^\eta$. -/
def H2 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (N P : ℕ) [NeZero P],
    2 ^ (2 ^ (2 ^ (2 ^ (k + 8)))) ≤ N → P.Prime → 2 * N < P → P ≤ 4 * N →
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → N ≤ 2 * A.card →
      let δ : ℝ := (A.card : ℝ) / (N : ℝ)
      let f : ZMod P → ℝ := fun x =>
        (if x.val ∈ A then (1 : ℝ) else 0) - δ * (if x.val ∈ Finset.Icc 1 N then (1 : ℝ) else 0)
      (1 / (256 * (k : ℝ) ^ 2 * (2 : ℝ) ^ k)) ^ (2 ^ (k - 1)) ≤
        ((P : ℝ) ^ k)⁻¹ * ∑ x : ZMod P, ∑ h : Fin (k - 1) → ZMod P,
          ∏ ω : Fin (k - 1) → Bool,
            f (x + ∑ i : Fin (k - 1), if ω i then h i else 0) →
      let η : ℝ := ((2 : ℝ) ^ (2 ^ (3 * 2 ^ (k + 7))))⁻¹
      ∃ (a d M : ℕ), 1 ≤ d ∧ 1 ≤ M ∧ (N : ℝ) ^ η ≤ (M : ℝ) ∧
        (∀ i ∈ Finset.Icc 1 M, a + i * d ∈ Finset.Icc 1 N) ∧
        (δ + η) * (M : ℝ) ≤ (((Finset.Icc 1 M).filter fun i => a + i * d ∈ A).card : ℝ)

theorem main : H1 → H2 → type_of% @Erdos138.erdos_138.variants.upper := by
  intro h1 h2 k
  refine Nat.sInf_le ?_
  show 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ∈ Erdos138.monoAP_guarantee_set 2 k
  intro coloring
  let N0 : ℕ := 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))
  have hN0_ge3 : 3 ≤ N0 := by
    have hpow2 : ∀ m : ℕ, 1 ≤ m → 2 ≤ 2 ^ m := fun m hm => by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hm
    have h1' : 2 ≤ 2 ^ (k + 9) := hpow2 (k + 9) (by omega)
    have h2' : 2 ≤ 2 ^ 2 ^ (k + 9) := hpow2 _ (by omega)
    have h3' : 2 ≤ 2 ^ 2 ^ 2 ^ (k + 9) := hpow2 _ (by omega)
    have h4' : 2 ≤ 2 ^ (2 ^ 2 ^ 2 ^ (k + 9)) := hpow2 _ (by omega)
    have h5' : 4 ≤ N0 := by
      simpa [N0] using Nat.pow_le_pow_right (by omega : 1 ≤ 2) h4'
    omega
  by_cases hk3 : k ≤ 2
  · exact monoAP_of_k_le_two hN0_ge3 hk3 coloring
  have hk3 : 3 ≤ k := by omega
  obtain ⟨col, A0, hA0_sub, hA0_dens, hA0_col⟩ := color_pigeonhole coloring
  by_contra hNoMono
  have hA0_noAP : ¬ HasKAP A0 k := fun h => hNoMono (hasKAP_to_monoAP coloring col A0 hA0_sub hA0_col h)
  let E : ℕ := 2 ^ (3 * 2 ^ (k + 7))
  let e3 : ℕ := 2 ^ (2 ^ (2 ^ (k + 9)))
  let η : ℝ := ((2 : ℝ) ^ E)⁻¹
  have hbudget : (2 ^ (E - 1) + 1) * E + 2 ^ (2 ^ (k + 8)) ≤ e3 := tower_step_budget k hk3
  have hiter : ∀ t : ℕ, t ≤ 2 ^ (E - 1) + 1 →
      ∃ (N : ℕ) (A : Finset ℕ), 1 ≤ N ∧ A ⊆ Finset.Icc 1 N ∧ ¬ HasKAP A k ∧
        1 / 2 + (t : ℝ) * η ≤ (A.card : ℝ) / (N : ℝ) ∧
        (2 : ℝ) ^ ((2 : ℝ) ^ (e3 - t * E)) ≤ (N : ℝ) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨N0, A0, by omega, hA0_sub, hA0_noAP, ?_, ?_⟩
      · simp only [Nat.cast_zero, zero_mul, add_zero]
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have : (N0 : ℝ) ≤ 2 * (A0.card : ℝ) := by exact_mod_cast hA0_dens
        linarith
      · simp only [zero_mul, Nat.sub_zero]
        have hN0_eq : N0 = 2 ^ (2 ^ e3) := rfl
        rw [hN0_eq]
        have hcast : ((2 ^ (2 ^ e3) : ℕ) : ℝ) = (2 : ℝ) ^ ((2 ^ e3 : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; rfl
        rw [hcast]
        push_cast; rfl
    | succ s ih =>
      intro hs_le
      obtain ⟨N, A, hN1, hA_sub, hNoAP, hdens, hNlen⟩ := ih (by omega)
      have hsE : (s + 1) * E + 2 ^ (2 ^ (k + 8)) ≤ e3 := by
        have : (s + 1) * E ≤ (2 ^ (E - 1) + 1) * E := Nat.mul_le_mul_right E hs_le
        omega
      have hsE_split : s * E + E = (s + 1) * E := by ring
      have hsE' : s * E + E + 2 ^ (2 ^ (k + 8)) ≤ e3 := hsE_split ▸ hsE
      have hrem : 2 ^ (2 ^ (k + 8)) ≤ e3 - s * E :=
        Nat.le_sub_of_add_le (by linarith [hsE'])
      have hN_floor : 2 ^ (2 ^ (2 ^ (2 ^ (k + 8)))) ≤ N := by
        have h1 : (2 : ℝ) ^ ((2 : ℝ) ^ (2 ^ (2 ^ (k + 8)))) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (e3 - s * E)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          exact pow_le_pow_right₀ (by norm_num) hrem
        have h2 : ((2 ^ (2 ^ (2 ^ (2 ^ (k + 8)))) : ℕ) : ℝ) ≤ (N : ℝ) := by
          have hcast : ((2 ^ (2 ^ (2 ^ (2 ^ (k + 8)))) : ℕ) : ℝ) =
              (2 : ℝ) ^ ((2 : ℝ) ^ (2 ^ (2 ^ (k + 8)))) := by
            rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
          rw [hcast]
          exact h1.trans hNlen
        exact_mod_cast h2
      have hN_gvn : 1024 * k * 2 ^ k ≤ N := (floor_threshold_bound k hk3).trans hN_floor
      have hA_half : N ≤ 2 * A.card := by
        have h1 : (1 / 2 : ℝ) ≤ (A.card : ℝ) / (N : ℝ) := by
          have : 0 ≤ (s : ℝ) * η := by dsimp [η]; positivity
          linarith
        rw [div_le_div_iff₀ (by norm_num) (by positivity)] at h1
        have : (N : ℝ) ≤ 2 * (A.card : ℝ) := by linarith
        exact_mod_cast this
      obtain ⟨P, hP_prime, hP_lo, hP_hi⟩ :=
        Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
      have : NeZero P := ⟨hP_prime.ne_zero⟩
      have hP_hi4 : P ≤ 4 * N := by omega
      have hU := gvn_dichotomy h1 hk3 hN_gvn hP_prime hP_lo hP_hi4 A hA_sub hA_half hNoAP
      obtain ⟨a, d, M, hd1, hM1, hM_ge, hQ_sub, hdens_new⟩ :=
        h2 k hk3 N P hN_floor hP_prime hP_lo hP_hi4 A hA_sub hA_half hU
      let B : Finset ℕ := (Finset.Icc 1 M).filter fun i => a + i * d ∈ A
      refine ⟨M, B, hM1, Finset.filter_subset _ _, fun hB => hNoAP (pullback_hasKAP (by omega) hB), ?_, ?_⟩
      · have hMpos : (0 : ℝ) < M := by positivity
        rw [le_div_iff₀ hMpos]
        have hstep_dens : 1 / 2 + ((s + 1 : ℕ) : ℝ) * η ≤ (A.card : ℝ) / (N : ℝ) + η := by
          push_cast; linarith
        exact (mul_le_mul_of_nonneg_right hstep_dens hMpos.le).trans hdens_new
      · have hη_nn : 0 ≤ η := by dsimp [η]; positivity
        have hpow_M : ((2 : ℝ) ^ ((2 : ℝ) ^ (e3 - s * E))) ^ η ≤ (M : ℝ) :=
          (Real.rpow_le_rpow (by positivity) hNlen hη_nn).trans hM_ge
        have hexp_eq : ((2 : ℝ) ^ ((2 : ℝ) ^ (e3 - s * E))) ^ η =
            (2 : ℝ) ^ ((2 : ℝ) ^ (e3 - (s + 1) * E)) := by
          rw [← Real.rpow_mul (by norm_num)]
          congr 1
          dsimp [η]
          have hsub : e3 - s * E = (e3 - (s + 1) * E) + E := by
            rw [← hsE_split, ← Nat.sub_sub]
            have hle : E + s * E ≤ e3 := by
              rw [add_comm]
              exact Nat.le_trans (Nat.le_add_right _ _) hsE'
            exact (Nat.sub_add_cancel (Nat.le_sub_of_add_le hle)).symm
          rw [hsub, pow_add, mul_inv_cancel_right₀ (by positivity)]
        rw [← hexp_eq]
        exact hpow_M
  obtain ⟨N, A, hN1, hA_sub, _, hdens, _⟩ := hiter (2 ^ (E - 1) + 1) le_rfl
  have hA_le_N : (A.card : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : A.card ≤ N := (Finset.card_le_card hA_sub).trans (by rw [Nat.card_Icc]; omega)
    exact_mod_cast this
  have hgt1 : 1 < 1 / 2 + ((2 ^ (E - 1) + 1 : ℕ) : ℝ) * η := by
    have hE_pos : 1 ≤ E := Nat.one_le_pow _ 2 (by omega)
    have hpow : (2 : ℝ) ^ E = 2 * (2 : ℝ) ^ (E - 1) := by
      conv_lhs => rw [show E = (E - 1) + 1 by omega, pow_succ]
      ring
    have hhalf : ((2 : ℝ) ^ (E - 1)) * η = 1 / 2 := by
      dsimp [η]
      rw [hpow]
      have hne : (2 : ℝ) ^ (E - 1) ≠ 0 := by positivity
      field_simp [hne]
    have hη_pos : 0 < η := by dsimp [η]; positivity
    push_cast
    linarith
  linarith

end OMA.R_Erdos138_erdos_138_variants_upper_R1
