import OMAReductions.R_Bugeaud32_adamczewski_faverjon_R1
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

/-!
# Reduction of `Bugeaud32.adamczewski_faverjon.R1.H1` (One-Variable Mahler Transcendence)

Following K. Nishioka (*Mahler Functions and Transcendence*, Springer LNM 1631, 1996) and
B. Adamczewski & C. Faverjon (*Méthode de Mahler : relations linéaires, irrationalité et
transcendance*, Invent. Math. 207 (2017), 719–766, Theorems 1.3 and 1.7), we reduce one-variable
Mahler transcendence for irrational values of bounded `k`-Mahler systems at rational points
`α ∈ (0, 1)` to two canonical, independent pillars:

1. `H1`: **Regularization and `ℚ(z)`-basis extraction for `k`-Mahler systems**: given any bounded
   finite `k`-kernel system `f : Fin m → ℝ → ℝ` (`f_i(z) = ∑' n, (seq i n : ℝ) * z^n` satisfying
   `f_i(z) = ∑ j : Fin k, z^j * f_{step i j}(z^k)`) and `α ∈ ℚ ∩ (0, 1)`, there exist a shift
   `R : ℕ` (setting `β = α ^ (k ^ R)`), a bounded `ℚ[z]`-linearly independent subsystem
   `g : Fin r → ℝ → ℝ` satisfying a `ℚ[z]`-linear Mahler equation `Q(z) g(z) = A(z) g(z^k)` with
   `β` regular (`∀ n, Q(β^{k^n}) ≠ 0 ∧ (det A)(β^{k^n}) ≠ 0`), and a rational matrix
   `M : Matrix (Fin m) (Fin r) ℚ` such that `f_i(α) = ∑ t, M_{i,t} g_t(β)`.
2. `H2`: **Adamczewski–Faverjon–Nishioka linear independence at regular points** (Invent. Math. 2017,
   Theorem 1.3): for any `ℚ[z]`-linearly independent bounded `k`-Mahler system `g : Fin r → ℝ → ℝ`
   satisfying `Q(z) g(z) = A(z) g(z^k)` with `β ∈ ℚ ∩ (0, 1)` regular, the values
   `g_0(β), ..., g_{r-1}(β)` are linearly independent over the algebraic numbers `ℚbar ∩ ℝ`.

Inside `main`, we prove completely from scratch:
- Enlargement of the `k`-kernel `S` by the constant-`1` generating series `δ₀ = (1, 0, 0, ...)`
  and the zero series `0` into an explicit indexed `k`-Mahler system `seq : Fin (S.card + 2) → ℕ → ℕ`
  with `f 0 z = 1`, `f 1 z = 0`, and `f i₀ z = F_a(z)`.
- If `θ = F_a(α)` were algebraic over `ℚ`, then `λ t = (M i₀ t : ℝ) - θ * (M 0 t : ℝ)` would be
  algebraic over `ℚ` for every `t : Fin r` and satisfy `∑ t, λ t * g t β = θ - θ * 1 = 0`.
- `H2` forces `λ t = 0` for all `t`, while `1 = f 0 α = ∑ t, (M 0 t : ℝ) * g t β ≠ 0` supplies an
  index `t₀` with `M 0 t₀ ≠ 0`, yielding `θ = (M i₀ t₀ / M 0 t₀ : ℚ)` and contradicting
  `Irrational θ`.

Credit: @tkaiman
-/

namespace OMA.R_Bugeaud32_adamczewski_faverjon_R1_H1_R1

open scoped BigOperators Classical

/- ### Helper: Series evaluations for `δ₀` and `0` -/

private def deltaZero : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0

private lemma tsum_deltaZero (z : ℝ) :
    ∑' n : ℕ, (deltaZero n : ℝ) * z ^ n = 1 := by
  have h : (fun n : ℕ => (deltaZero n : ℝ) * z ^ n) = fun n => if n = 0 then (1 : ℝ) else 0 := by
    funext n
    cases n with
    | zero => simp [deltaZero]
    | succ m => simp [deltaZero]
  rw [h, tsum_ite_eq]

private lemma tsum_zeroSeq (z : ℝ) :
    ∑' n : ℕ, ((0 : ℕ) : ℝ) * z ^ n = 0 := by
  simp

/- ### Hypotheses -/

/-- **Regularization and `ℚ(z)`-basis extraction for `k`-Mahler systems**:
given `k ≥ 2`, `α ∈ ℚ ∩ (0, 1)`, and a bounded finite `k`-kernel system `seq : Fin m → ℕ → ℕ`
whose generating series `f_i(z) = ∑' n, (seq i n : ℝ) * z ^ n` satisfy
`f_i(z) = ∑ j : Fin k, z ^ j * f_{step i j}(z ^ k)` on `|z| < 1`, there exist a shift `R : ℕ`
(with `β = α ^ (k ^ R)`), a bounded subsystem `c : Fin r → ℕ → ℕ` whose generating series
`g_t(z) = ∑' n, (c t n : ℝ) * z ^ n` are `ℚ[z]`-linearly independent on `(-1, 1)` and satisfy a
`ℚ[z]`-linear `k`-Mahler equation `Q(z) g_t(z) = ∑ s, A_{t,s}(z) g_s(z^k)` regular at `β`,
and a rational matrix `M : Matrix (Fin m) (Fin r) ℚ` expressing `f_i(α) = ∑ t, M_{i,t} g_t(β)`. -/
def H1 : Prop :=
  ∀ (k B m : ℕ), 2 ≤ k → ∀ (α : ℚ), 0 < α → α < 1 →
    ∀ (seq : Fin m → ℕ → ℕ) (step : Fin m → Fin k → Fin m),
      (∀ i n, seq i n ≤ B) →
      (∀ (i : Fin m) (z : ℝ), |z| < 1 →
        ∑' n : ℕ, (seq i n : ℝ) * z ^ n =
          ∑ j : Fin k, z ^ j.1 * ∑' n : ℕ, (seq (step i j) n : ℝ) * (z ^ k) ^ n) →
      ∃ (r R B' : ℕ) (c : Fin r → ℕ → ℕ) (M : Matrix (Fin m) (Fin r) ℚ)
        (Q : Polynomial ℚ) (A : Matrix (Fin r) (Fin r) (Polynomial ℚ)),
        (∀ t n, c t n ≤ B') ∧
        (∀ i : Fin m,
          ∑' n : ℕ, (seq i n : ℝ) * (α : ℝ) ^ n =
            ∑ t : Fin r, (M i t : ℝ) * ∑' n : ℕ, (c t n : ℝ) * ((α ^ (k ^ R) : ℚ) : ℝ) ^ n) ∧
        (∀ P : Fin r → Polynomial ℚ,
          (∀ z : ℝ, |z| < 1 →
            ∑ t : Fin r, (Polynomial.aeval z (P t)) * (∑' n : ℕ, (c t n : ℝ) * z ^ n) = 0) →
          ∀ t : Fin r, P t = 0) ∧
        (∀ (t : Fin r) (z : ℝ), |z| < 1 →
          (Polynomial.aeval z Q) * (∑' n : ℕ, (c t n : ℝ) * z ^ n) =
            ∑ s : Fin r, (Polynomial.aeval z (A t s)) * (∑' n : ℕ, (c s n : ℝ) * (z ^ k) ^ n)) ∧
        (∀ n : ℕ,
          Polynomial.eval ((α ^ (k ^ R)) ^ (k ^ n)) Q ≠ 0 ∧
          Polynomial.eval ((α ^ (k ^ R)) ^ (k ^ n)) A.det ≠ 0)

/-- **Adamczewski–Faverjon–Nishioka linear independence at regular points** (Invent. Math. 2017,
Theorem 1.3): if bounded generating series `g_t(z) = ∑' n, (c t n : ℝ) * z ^ n` (`t : Fin r`)
are `ℚ[z]`-linearly independent on `|z| < 1` and satisfy a `ℚ[z]`-linear `k`-Mahler system
`Q(z) g_t(z) = ∑ s, A_{t,s}(z) g_s(z ^ k)` for which `β ∈ ℚ ∩ (0, 1)` is regular
(`∀ n, Q(β^{k^n}) ≠ 0 ∧ (det A)(β^{k^n}) ≠ 0`), then the values `g_0(β), ..., g_{r-1}(β)` are
linearly independent over the real algebraic numbers. -/
def H2 : Prop :=
  ∀ (k B' r : ℕ), 2 ≤ k → ∀ (β : ℚ), 0 < β → β < 1 →
    ∀ (c : Fin r → ℕ → ℕ) (Q : Polynomial ℚ) (A : Matrix (Fin r) (Fin r) (Polynomial ℚ)),
      (∀ t n, c t n ≤ B') →
      (∀ P : Fin r → Polynomial ℚ,
        (∀ z : ℝ, |z| < 1 →
          ∑ t : Fin r, (Polynomial.aeval z (P t)) * (∑' n : ℕ, (c t n : ℝ) * z ^ n) = 0) →
        ∀ t : Fin r, P t = 0) →
      (∀ (t : Fin r) (z : ℝ), |z| < 1 →
        (Polynomial.aeval z Q) * (∑' n : ℕ, (c t n : ℝ) * z ^ n) =
          ∑ s : Fin r, (Polynomial.aeval z (A t s)) * (∑' n : ℕ, (c s n : ℝ) * (z ^ k) ^ n)) →
      (∀ n : ℕ,
        Polynomial.eval (β ^ (k ^ n)) Q ≠ 0 ∧
        Polynomial.eval (β ^ (k ^ n)) A.det ≠ 0) →
      ∀ (lam : Fin r → ℝ),
        (∀ t : Fin r, IsAlgebraic ℚ (lam t)) →
        (∑ t : Fin r, lam t * ∑' n : ℕ, (c t n : ℝ) * (β : ℝ) ^ n = 0) →
        ∀ t : Fin r, lam t = 0

/- ### Main Reduction Theorem -/

theorem main : H1 → H2 → OMA.R_Bugeaud32_adamczewski_faverjon_R1.H1 := by
  intro hReg hLinInd
  dsimp only [OMA.R_Bugeaud32_adamczewski_faverjon_R1.H1]
  intro k B hk α hα_pos hα_lt a S ha_mem hS_bd htr_ex hirr
  obtain ⟨tr, htr⟩ := htr_ex
  -- Step 1: Enlarge `S` by `deltaZero` (index `0`) and `0` (index `1`) into `Fin (S.card + 2)`
  let eS : S ≃ Fin S.card := S.equivFin
  let m : ℕ := S.card + 2
  let i0 : Fin m := ⟨0, by dsimp [m]; omega⟩
  let i1 : Fin m := ⟨1, by dsimp [m]; omega⟩
  let idxOfS : S → Fin m := fun s => ⟨(eS s).1 + 2, by dsimp [m]; omega⟩
  let seq : Fin m → ℕ → ℕ := fun i =>
    if h0 : i.1 = 0 then deltaZero
    else if h1 : i.1 = 1 then fun _ => 0
    else (eS.symm ⟨i.1 - 2, by have := i.2; dsimp [m] at this; omega⟩).1
  let step : Fin m → Fin k → Fin m := fun i j =>
    if h0 : i.1 = 0 then
      if j.1 = 0 then i0 else i1
    else if h1 : i.1 = 1 then i1
    else idxOfS (tr (eS.symm ⟨i.1 - 2, by have := i.2; dsimp [m] at this; omega⟩) j)
  have hseq_bd : ∀ i n, seq i n ≤ max B 1 := by
    intro i n
    dsimp [seq]
    split_ifs with h0 h1
    · cases n <;> simp [deltaZero]
    · simp
    · exact le_trans (hS_bd _ (eS.symm ⟨i.1 - 2, by have := i.2; dsimp [m] at this; omega⟩).2 n)
        (le_max_left _ _)
  have hseq_0 : seq i0 = deltaZero := rfl
  have hseq_1 : seq i1 = fun _ => 0 := rfl
  have hseq_S : ∀ s : S, seq (idxOfS s) = s.1 := by
    intro s
    have hne0 : (idxOfS s).1 ≠ 0 := by dsimp [idxOfS]; omega
    have hne1 : (idxOfS s).1 ≠ 1 := by dsimp [idxOfS]; omega
    dsimp [seq]
    rw [dif_neg hne0, dif_neg hne1]
    have hfin : (⟨(idxOfS s).1 - 2, by dsimp [idxOfS]; omega⟩ : Fin S.card) = eS s := by
      ext; dsimp [idxOfS]; omega
    rw [hfin, Equiv.symm_apply_apply]
  have hstep_sys : ∀ (i : Fin m) (z : ℝ), |z| < 1 →
      ∑' n : ℕ, (seq i n : ℝ) * z ^ n =
        ∑ j : Fin k, z ^ j.1 * ∑' n : ℕ, (seq (step i j) n : ℝ) * (z ^ k) ^ n := by
    intro i z hz
    by_cases hi0 : i.1 = 0
    · have hi_eq : i = i0 := Fin.ext hi0
      rw [hi_eq, hseq_0, tsum_deltaZero]
      let j0 : Fin k := ⟨0, by omega⟩
      have hterm : ∀ j : Fin k,
          z ^ j.1 * ∑' n : ℕ, (seq (step i0 j) n : ℝ) * (z ^ k) ^ n =
            if j = j0 then (1 : ℝ) else 0 := by
        intro j
        by_cases hj0 : j.1 = 0
        · have hj_eq : j = j0 := Fin.ext hj0
          rw [hj_eq, if_pos rfl]
          have hst : step i0 j0 = i0 := rfl
          rw [hst, hseq_0, tsum_deltaZero]
          simp [j0]
        · have hj_ne : j ≠ j0 := fun h => hj0 (congrArg Fin.val h)
          have hst : step i0 j = i1 := by dsimp [step, i0]; exact if_neg hj0
          rw [if_neg hj_ne, hst, hseq_1, tsum_zeroSeq, mul_zero]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      simp
    · by_cases hi1 : i.1 = 1
      · have hi_eq : i = i1 := Fin.ext hi1
        rw [hi_eq, hseq_1, tsum_zeroSeq]
        symm
        refine Finset.sum_eq_zero fun j _ => ?_
        have hst : step i1 j = i1 := rfl
        rw [hst, hseq_1, tsum_zeroSeq, mul_zero]
      · let s : S := eS.symm ⟨i.1 - 2, by have := i.2; dsimp [m] at this; omega⟩
        have his : i = idxOfS s := by
          ext
          dsimp [idxOfS, s]
          have hval : (eS (eS.symm ⟨i.1 - 2, by have := i.2; dsimp [m] at this; omega⟩)).1 = i.1 - 2 := by
            rw [Equiv.apply_symm_apply]
          omega
        rw [his, hseq_S s, htr s z hz]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hst : step (idxOfS s) j = idxOfS (tr s j) := by
          have hne0 : (idxOfS s).1 ≠ 0 := by dsimp [idxOfS]; omega
          have hne1 : (idxOfS s).1 ≠ 1 := by dsimp [idxOfS]; omega
          dsimp [step]
          rw [dif_neg hne0, dif_neg hne1]
          have hfin : (⟨(idxOfS s).1 - 2, by dsimp [idxOfS]; omega⟩ : Fin S.card) = eS s := by
            ext; dsimp [idxOfS]; omega
          rw [hfin, Equiv.symm_apply_apply]
        rw [hst, hseq_S]
  -- Step 2: Regularize and extract a `ℚ[z]`-basis `c` at `β = α ^ (k ^ R)` via `H1`
  obtain ⟨r, R, B', c, M, Q, A, hc_bd, hM_eq, hc_ind, hMahler, hRegβ⟩ :=
    hReg k (max B 1) m hk α hα_pos hα_lt seq step hseq_bd hstep_sys
  let β : ℚ := α ^ (k ^ R)
  have hβ_pos : 0 < β := pow_pos hα_pos _
  have hβ_lt : β < 1 := pow_lt_one₀ hα_pos.le hα_lt (by positivity)
  -- Step 3: Assume `θ = F_a(α)` is algebraic over `ℚ` and derive a contradiction via `H2`
  intro halg
  set θ : ℝ := ∑' n : ℕ, (a n : ℝ) * (α : ℝ) ^ n
  let i₀ : Fin m := idxOfS ⟨a, ha_mem⟩
  have hval_i₀ : θ = ∑ t : Fin r, (M i₀ t : ℝ) * ∑' n : ℕ, (c t n : ℝ) * (β : ℝ) ^ n := by
    have := hM_eq i₀
    rwa [hseq_S ⟨a, ha_mem⟩] at this
  have hval_i1 : (1 : ℝ) = ∑ t : Fin r, (M i0 t : ℝ) * ∑' n : ℕ, (c t n : ℝ) * (β : ℝ) ^ n := by
    have := hM_eq i0
    rwa [hseq_0, tsum_deltaZero] at this
  let lam : Fin r → ℝ := fun t => (M i₀ t : ℝ) - θ * (M i0 t : ℝ)
  have hlam_alg : ∀ t : Fin r, IsAlgebraic ℚ (lam t) := by
    intro t
    have hq1 : IsAlgebraic ℚ (M i₀ t : ℝ) := by
      simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (M i₀ t)
    have hq2 : IsAlgebraic ℚ (M i0 t : ℝ) := by
      simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (M i0 t)
    exact hq1.sub (halg.mul hq2)
  have hlam_sum : ∑ t : Fin r, lam t * ∑' n : ℕ, (c t n : ℝ) * (β : ℝ) ^ n = 0 := by
    dsimp [lam]
    simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← hval_i₀, ← hval_i1, mul_one, sub_self]
  have hlam_zero : ∀ t : Fin r, lam t = 0 :=
    hLinInd k B' r hk β hβ_pos hβ_lt c Q A hc_bd hc_ind hMahler hRegβ lam hlam_alg hlam_sum
  -- Step 4: Since `1 ≠ 0`, some `M i0 t₀ ≠ 0`, forcing `θ ∈ ℚ`
  have hex_ne : ∃ t₀ : Fin r, M i0 t₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : ∑ t : Fin r, (M i0 t : ℝ) * ∑' n : ℕ, (c t n : ℝ) * (β : ℝ) ^ n = 0 := by
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [hall t, Rat.cast_zero, zero_mul]
    linarith [hval_i1]
  obtain ⟨t₀, ht₀⟩ := hex_ne
  have hrel : (M i₀ t₀ : ℝ) - θ * (M i0 t₀ : ℝ) = 0 := hlam_zero t₀
  have ht₀R : (M i0 t₀ : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ht₀
  have hθ_rat : θ = ((M i₀ t₀ / M i0 t₀ : ℚ) : ℝ) := by
    rw [Rat.cast_div]
    field_simp [ht₀R]
    linarith
  exact hirr ⟨M i₀ t₀ / M i0 t₀, hθ_rat.symm⟩

end OMA.R_Bugeaud32_adamczewski_faverjon_R1_H1_R1
