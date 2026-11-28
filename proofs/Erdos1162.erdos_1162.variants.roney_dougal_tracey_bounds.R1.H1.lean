import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_bounds_R1

/-!
# Roney-Dougal and Tracey Lower Bound for Subgroups of S_n

Proves `OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_bounds_R1.H1`:
there exists `α > 0` (explicitly `α = 1 / 64`) such that for all `n > 1`,
`2 ^ (n ^ 2 / 16 + α * n * Real.logb 2 n) ≤ Erdos1162.f n`.

The proof is completely elementary:
1. Small cases `n = 2, 3` give `2 ≤ f 2` and `4 ≤ f 3` directly via `⊥`, `⊤`, and swap subgroups.
2. For `n ≥ 4`, set `m = n / 2`, `a = m / 2`, `b = m - a`. Each fixed-point-free involution
   `σ` on `Fin (2 * m)` (matching of size `m`) and each `b × a` matrix `L` over `ZMod 2` with
   no zero row defines an elementary abelian 2-subgroup `H(σ, L) ≤ Equiv.Perm (Fin n)` of
   permutations that swap a subset of pairs of `σ` lying in the graph of `L`.
3. Every pair of `σ` is moved by some element of `H(σ, L)` (since `L` has no zero row), so
   `H(σ, L)` uniquely determines `σ` and hence `L`, and `H(σ, L) ≠ ⊥`.
4. Counting fixed-point-free involutions inductively gives `oddFact m * (2 ^ a - 1) ^ b + 1 ≤ f n`.
5. For `4 ≤ n < 32`, the inequality reduces to a finite natural-number check; for `n ≥ 32`,
   keeping the top `b` factors of `oddFact m` gives `oddFact m ≥ m ^ b` and `(2 ^ a - 1) ^ b ≥ 2 ^ ((a - 1) * b)`,
   whose base-2 logarithm exceeds `n ^ 2 / 16 + (1 / 64) * n * logb 2 n`.
-/

open scoped BigOperators

namespace Erdos1162Lower

/- ### Part 1: Small cases n = 2 and n = 3 -/

private def swapSubgroup {n : ℕ} (τ : Equiv.Perm (Fin n)) (hτ : τ * τ = 1) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {x | x = 1 ∨ x = τ}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | hx) (rfl | hy)
    · exact Or.inl (mul_one 1)
    · exact Or.inr (by rw [one_mul, hy])
    · exact Or.inr (by rw [mul_one, hx])
    · exact Or.inl (by rw [hx, hy, hτ])
  inv_mem' := by
    rintro x (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right hτ)

private lemma two_le_f_two : 2 ≤ Erdos1162.f 2 := by
  let g : Fin 2 → Subgroup (Equiv.Perm (Fin 2))
    | ⟨0, _⟩ => ⊥
    | ⟨1, _⟩ => ⊤
  have hinj : Function.Injective g := by
    intro i j hij
    have hne : (⊥ : Subgroup (Equiv.Perm (Fin 2))) ≠ ⊤ := by
      intro h
      have hmem : Equiv.swap (0 : Fin 2) 1 ∈ (⊥ : Subgroup (Equiv.Perm (Fin 2))) := by
        rw [h]; trivial
      rw [Subgroup.mem_bot] at hmem
      have h0 : Equiv.swap (0 : Fin 2) 1 0 = (1 : Equiv.Perm (Fin 2)) 0 := congrArg (· 0) hmem
      exact absurd h0 (by decide)
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hne
    · exact absurd hij.symm hne
    · rfl
  simpa [Erdos1162.f] using Nat.card_le_card_of_injective g hinj

private lemma four_le_f_three : 4 ≤ Erdos1162.f 3 := by
  let τ₁ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let τ₂ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let τ₃ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let g : Fin 4 → Subgroup (Equiv.Perm (Fin 3))
    | ⟨0, _⟩ => ⊥
    | ⟨1, _⟩ => swapSubgroup τ₁ (Equiv.swap_mul_self 0 1)
    | ⟨2, _⟩ => swapSubgroup τ₂ (Equiv.swap_mul_self 0 2)
    | ⟨3, _⟩ => swapSubgroup τ₃ (Equiv.swap_mul_self 1 2)
  have h10 : τ₁ ≠ 1 := by decide
  have h20 : τ₂ ≠ 1 := by decide
  have h30 : τ₃ ≠ 1 := by decide
  have h12 : τ₁ ≠ τ₂ := by decide
  have h13 : τ₁ ≠ τ₃ := by decide
  have h23 : τ₂ ≠ τ₃ := by decide
  have hinj : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      have hmem : τ₁ ∈ g ⟨1, by decide⟩ := Or.inr rfl
      rw [← hij] at hmem
      exact h10 (Subgroup.mem_bot.mp hmem)
    · exfalso
      have hmem : τ₂ ∈ g ⟨2, by decide⟩ := Or.inr rfl
      rw [← hij] at hmem
      exact h20 (Subgroup.mem_bot.mp hmem)
    · exfalso
      have hmem : τ₃ ∈ g ⟨3, by decide⟩ := Or.inr rfl
      rw [← hij] at hmem
      exact h30 (Subgroup.mem_bot.mp hmem)
    · exfalso
      have hmem : τ₁ ∈ g ⟨1, by decide⟩ := Or.inr rfl
      rw [hij] at hmem
      exact h10 (Subgroup.mem_bot.mp hmem)
    · rfl
    · exfalso
      have hmem : τ₁ ∈ g ⟨1, by decide⟩ := Or.inr rfl
      rw [hij] at hmem
      rcases hmem with h | h
      · exact h10 h
      · exact h12 h
    · exfalso
      have hmem : τ₁ ∈ g ⟨1, by decide⟩ := Or.inr rfl
      rw [hij] at hmem
      rcases hmem with h | h
      · exact h10 h
      · exact h13 h
    · exfalso
      have hmem : τ₂ ∈ g ⟨2, by decide⟩ := Or.inr rfl
      rw [hij] at hmem
      exact h20 (Subgroup.mem_bot.mp hmem)
    · exfalso
      have hmem : τ₂ ∈ g ⟨2, by decide⟩ := Or.inr rfl
      rw [hij] at hmem
      rcases hmem with h | h
      · exact h20 h
      · exact h12 h.symm
    · rfl
    · exfalso
      have hmem : τ₂ ∈ g ⟨2, by decide⟩ := Or.inr rfl
      rw [hij] at hmem
      rcases hmem with h | h
      · exact h20 h
      · exact h23 h
    · exfalso
      have hmem : τ₃ ∈ g ⟨3, by decide⟩ := Or.inr rfl
      rw [hij] at hmem
      exact h30 (Subgroup.mem_bot.mp hmem)
    · exfalso
      have hmem : τ₃ ∈ g ⟨3, by decide⟩ := Or.inr rfl
      rw [hij] at hmem
      rcases hmem with h | h
      · exact h30 h
      · exact h13 h.symm
    · exfalso
      have hmem : τ₃ ∈ g ⟨3, by decide⟩ := Or.inr rfl
      rw [hij] at hmem
      rcases hmem with h | h
      · exact h30 h
      · exact h23 h.symm
    · rfl
  simpa [Erdos1162.f] using Nat.card_le_card_of_injective g hinj

/- ### Part 2: Fixed-point-free involutions and odd double factorials -/

/-- The odd double factorial `1 * 3 * ... * (2 * m - 1)`. -/
def oddFact : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 * m + 1) * oddFact m

lemma oddFact_eq_prod (m : ℕ) : oddFact m = ∏ k ∈ Finset.range m, (2 * k + 1) := by
  induction m with
  | zero => simp [oddFact]
  | succ m ih =>
    rw [oddFact, Finset.prod_range_succ, ih, mul_comm]

lemma pow_le_oddFact (m : ℕ) : m ^ (m - m / 2) ≤ oddFact m := by
  rw [oddFact_eq_prod]
  set a := m / 2
  have hsub : Finset.Ico a m ⊆ Finset.range m := fun k hk =>
    Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hprod1 : 1 ≤ ∏ k ∈ Finset.range m \ Finset.Ico a m, (2 * k + 1) :=
    Finset.one_le_prod' fun k _ => by omega
  have hprod2 : m ^ (m - a) ≤ ∏ k ∈ Finset.Ico a m, (2 * k + 1) := by
    calc m ^ (m - a) = ∏ _k ∈ Finset.Ico a m, m := by
          rw [Finset.prod_const, Nat.card_Ico]
      _ ≤ ∏ k ∈ Finset.Ico a m, (2 * k + 1) := by
          refine Finset.prod_le_prod' fun k hk => ?_
          have hka : a ≤ k := (Finset.mem_Ico.mp hk).1
          omega
  calc m ^ (m - a)
      ≤ ∏ k ∈ Finset.Ico a m, (2 * k + 1) := hprod2
    _ ≤ (∏ k ∈ Finset.range m \ Finset.Ico a m, (2 * k + 1)) *
        (∏ k ∈ Finset.Ico a m, (2 * k + 1)) := Nat.le_mul_of_pos_left _ hprod1
    _ = ∏ k ∈ Finset.range m, (2 * k + 1) := Finset.prod_sdiff hsub

/-- Fixed-point-free involutions on `Fin n`, i.e., perfect matchings. -/
abbrev FPFInv (n : ℕ) := { σ : Equiv.Perm (Fin n) // σ * σ = 1 ∧ ∀ x, σ x ≠ x }

private lemma fpf_invol {n : ℕ} (σ : FPFInv n) (x : Fin n) : σ.1 (σ.1 x) = x := by
  have := congrArg (fun p : Equiv.Perm (Fin n) => p x) σ.2.1
  simpa using this

private def extendFPF {m : ℕ} (τ : FPFInv (2 * m)) : FPFInv (2 * m + 2) := by
  let f : Fin (2 * m + 2) → Fin (2 * m + 2) := fun x =>
    if h : x.1 < 2 * m then ⟨(τ.1 ⟨x.1, h⟩).1, by omega⟩
    else if x.1 = 2 * m then ⟨2 * m + 1, by omega⟩
    else ⟨2 * m, by omega⟩
  have hinv : Function.LeftInverse f f := by
    intro x
    dsimp only [f]
    by_cases h1 : x.1 < 2 * m
    · simp only [h1, ↓reduceDIte]
      have h2 : (τ.1 ⟨x.1, h1⟩).1 < 2 * m := (τ.1 ⟨x.1, h1⟩).2
      simp only [h2, ↓reduceDIte]
      apply Fin.ext
      exact congrArg (fun z : Fin (2 * m) => z.1) (fpf_invol τ ⟨x.1, h1⟩)
    · simp only [h1, ↓reduceDIte]
      by_cases h2 : x.1 = 2 * m
      · simp only [h2, ↓reduceIte]
        have hne1 : ¬ (2 * m + 1 < 2 * m) := by omega
        have hne2 : ¬ (2 * m + 1 = 2 * m) := by omega
        simp only [hne1, ↓reduceDIte, hne2, ↓reduceIte]
        exact Fin.ext h2.symm
      · simp only [h2, ↓reduceIte]
        have hne1 : ¬ (2 * m < 2 * m) := by omega
        simp only [hne1, ↓reduceDIte, if_true]
        exact Fin.ext (show 2 * m + 1 = x.1 by have := x.2; omega)
  let p : Equiv.Perm (Fin (2 * m + 2)) := ⟨f, f, hinv, hinv⟩
  refine ⟨p, ?_, ?_⟩
  · ext x
    exact congrArg Fin.val (hinv x)
  · intro x hx
    have hx' : (f x).1 = x.1 := congrArg Fin.val hx
    dsimp only [f] at hx'
    by_cases h1 : x.1 < 2 * m
    · simp only [h1, ↓reduceDIte] at hx'
      exact τ.2.2 ⟨x.1, h1⟩ (Fin.ext hx')
    · simp only [h1, ↓reduceDIte] at hx'
      by_cases h2 : x.1 = 2 * m
      · simp only [h2, ↓reduceIte] at hx'
        omega
      · simp only [h2, ↓reduceIte] at hx'
        omega

private def stepFPF {m : ℕ} (k : Fin (2 * m + 1)) (τ : FPFInv (2 * m)) : FPFInv (2 * m + 2) := by
  let s : Equiv.Perm (Fin (2 * m + 2)) := Equiv.swap ⟨k.1, by omega⟩ ⟨2 * m, by omega⟩
  let e : FPFInv (2 * m + 2) := extendFPF τ
  refine ⟨s * e.1 * s, ?_, ?_⟩
  · calc (s * e.1 * s) * (s * e.1 * s)
        = s * e.1 * (s * s) * e.1 * s := by group
      _ = s * (e.1 * e.1) * s := by rw [Equiv.swap_mul_self, mul_one]; group
      _ = s * s := by rw [e.2.1, mul_one]
      _ = 1 := Equiv.swap_mul_self _ _
  · intro x hx
    have h1 : s (e.1 (s x)) = x := hx
    have h2 : e.1 (s x) = s x := by
      calc e.1 (s x) = (s * s) (e.1 (s x)) := by rw [Equiv.swap_mul_self]; rfl
        _ = s (s (e.1 (s x))) := rfl
        _ = s x := congrArg s h1
    exact e.2.2 (s x) h2

private lemma stepFPF_last {m : ℕ} (k : Fin (2 * m + 1)) (τ : FPFInv (2 * m)) :
    (stepFPF k τ).1 ⟨2 * m + 1, by omega⟩ = ⟨k.1, by omega⟩ := by
  change Equiv.swap ⟨k.1, by omega⟩ ⟨2 * m, by omega⟩
    ((extendFPF τ).1 (Equiv.swap ⟨k.1, by omega⟩ ⟨2 * m, by omega⟩ ⟨2 * m + 1, by omega⟩)) =
    ⟨k.1, by omega⟩
  have hs1 : Equiv.swap (⟨k.1, by omega⟩ : Fin (2 * m + 2)) ⟨2 * m, by omega⟩ ⟨2 * m + 1, by omega⟩ =
      ⟨2 * m + 1, by omega⟩ :=
    Equiv.swap_apply_of_ne_of_ne
      (Fin.ne_of_val_ne (show 2 * m + 1 ≠ k.1 by omega))
      (Fin.ne_of_val_ne (show 2 * m + 1 ≠ 2 * m by omega))
  rw [hs1]
  have he : (extendFPF τ).1 ⟨2 * m + 1, by omega⟩ = ⟨2 * m, by omega⟩ := by
    have h1 : ¬ (2 * m + 1 < 2 * m) := by omega
    have h2 : ¬ (2 * m + 1 = 2 * m) := by omega
    simp [extendFPF, h1, h2]
  rw [he, Equiv.swap_apply_right]

private lemma stepFPF_injective (m : ℕ) :
    Function.Injective (fun p : Fin (2 * m + 1) × FPFInv (2 * m) => stepFPF p.1 p.2) := by
  rintro ⟨k₁, τ₁⟩ ⟨k₂, τ₂⟩ h
  dsimp only at h
  have hkval : (⟨k₁.1, by omega⟩ : Fin (2 * m + 2)) = ⟨k₂.1, by omega⟩ := by
    rw [← stepFPF_last k₁ τ₁, ← stepFPF_last k₂ τ₂, h]
  have hk : k₁ = k₂ := Fin.ext (congrArg (fun z : Fin (2 * m + 2) => z.1) hkval)
  subst hk
  have hval : (stepFPF k₁ τ₁).1 = (stepFPF k₁ τ₂).1 := congrArg Subtype.val h
  dsimp only [stepFPF] at hval
  have hext : (extendFPF τ₁).1 = (extendFPF τ₂).1 :=
    mul_left_cancel (mul_right_cancel hval)
  have hτ : τ₁ = τ₂ := by
    apply Subtype.ext
    ext i
    have hi := congrArg (fun p : Equiv.Perm (Fin (2 * m + 2)) => (p ⟨i.1, by omega⟩).1) hext
    have hlt : i.1 < 2 * m := i.2
    simpa [extendFPF, hlt] using hi
  exact Prod.ext rfl hτ

lemma oddFact_le_card_fpfInv (m : ℕ) : oddFact m ≤ Nat.card (FPFInv (2 * m)) := by
  induction m with
  | zero =>
    have : Nonempty (FPFInv 0) := ⟨⟨1, mul_one 1, fun x => Fin.elim0 x⟩⟩
    rw [oddFact]
    exact Nat.succ_le_of_lt (Nat.card_pos (α := FPFInv 0))
  | succ m ih =>
    have hstep := Nat.card_le_card_of_injective _ (stepFPF_injective m)
    rw [Nat.card_prod, Nat.card_fin] at hstep
    have heq : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [heq, oddFact]
    exact (Nat.mul_le_mul_left (2 * m + 1) ih).trans hstep

/- ### Part 3: Subgroup family H(σ, L) and injectivity -/

private def lows {m : ℕ} (σ : FPFInv (2 * m)) : Finset (Fin (2 * m)) :=
  Finset.univ.filter (fun x => x < σ.1 x)

private lemma lows_card {m : ℕ} (σ : FPFInv (2 * m)) : (lows σ).card = m := by
  let highs : Finset (Fin (2 * m)) := Finset.univ.filter (fun x => σ.1 x < x)
  have hdisj : Disjoint (lows σ) highs := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact lt_asymm (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2
  have hunion : lows σ ∪ highs = Finset.univ := by
    ext x
    simp only [Finset.mem_union, lows, highs, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact lt_or_gt_of_ne (σ.2.2 x).symm
  have hbij : (lows σ).card = highs.card := by
    refine Finset.card_bij (fun x _ => σ.1 x) ?_ ?_ ?_
    · intro x hx
      have hlt : x < σ.1 x := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [fpf_invol σ x]⟩
    · intro x₁ _ x₂ _ h
      exact σ.1.injective h
    · intro y hy
      have hlt : σ.1 y < y := (Finset.mem_filter.mp hy).2
      refine ⟨σ.1 y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, fpf_invol σ y⟩
      rwa [fpf_invol σ y]
  have htot : (lows σ).card + highs.card = 2 * m := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  omega

private def lowAt {m : ℕ} (σ : FPFInv (2 * m)) (k : Fin m) : Fin (2 * m) :=
  ((lows σ).orderIsoOfFin (lows_card σ) k).1

private lemma lowAt_lt {m : ℕ} (σ : FPFInv (2 * m)) (k : Fin m) :
    lowAt σ k < σ.1 (lowAt σ k) :=
  (Finset.mem_filter.mp ((lows σ).orderIsoOfFin (lows_card σ) k).2).2

private def pairIdx {m : ℕ} (σ : FPFInv (2 * m)) (x : Fin (2 * m)) : Fin m :=
  if h : x < σ.1 x then
    ((lows σ).orderIsoOfFin (lows_card σ)).symm ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  else
    ((lows σ).orderIsoOfFin (lows_card σ)).symm
      ⟨σ.1 x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [fpf_invol σ x]
        rcases lt_trichotomy x (σ.1 x) with h1 | h1 | h1
        · exact absurd h1 h
        · exact absurd h1.symm (σ.2.2 x)
        · exact h1⟩⟩

private lemma pairIdx_invol {m : ℕ} (σ : FPFInv (2 * m)) (x : Fin (2 * m)) :
    pairIdx σ (σ.1 x) = pairIdx σ x := by
  unfold pairIdx
  by_cases h : x < σ.1 x
  · have h' : ¬ (σ.1 x < σ.1 (σ.1 x)) := by
      rw [fpf_invol σ x]
      exact not_lt.mpr h.le
    simp only [h, ↓reduceDIte, h']
    congr 1
    exact Subtype.ext (fpf_invol σ x)
  · have hlt : σ.1 x < x := by
      rcases lt_trichotomy x (σ.1 x) with h1 | h1 | h1
      · exact absurd h1 h
      · exact absurd h1.symm (σ.2.2 x)
      · exact h1
    have h' : σ.1 x < σ.1 (σ.1 x) := by rwa [fpf_invol σ x]
    simp only [h, ↓reduceDIte, h']

private lemma pairIdx_lowAt {m : ℕ} (σ : FPFInv (2 * m)) (k : Fin m) :
    pairIdx σ (lowAt σ k) = k := by
  unfold pairIdx
  have h : lowAt σ k < σ.1 (lowAt σ k) := lowAt_lt σ k
  simp only [h, ↓reduceDIte]
  exact ((lows σ).orderIsoOfFin (lows_card σ)).symm_apply_apply k

private def actFun {m : ℕ} (σ : FPFInv (2 * m)) (c : Fin m → ZMod 2) (x : Fin (2 * m)) :
    Fin (2 * m) :=
  if c (pairIdx σ x) = 1 then σ.1 x else x

private lemma actFun_add {m : ℕ} (σ : FPFInv (2 * m)) (c₁ c₂ : Fin m → ZMod 2) (x : Fin (2 * m)) :
    actFun σ (c₁ + c₂) x = actFun σ c₁ (actFun σ c₂ x) := by
  unfold actFun
  have hidx : pairIdx σ (σ.1 x) = pairIdx σ x := pairIdx_invol σ x
  have hbit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbit (c₁ (pairIdx σ x)) with h1 | h1 <;> rcases hbit (c₂ (pairIdx σ x)) with h2 | h2
  · simp [h1, h2]
  · simp [h1, h2, hidx]
  · simp [h1, h2]
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp [h1, h2, hidx, h11, h01, fpf_invol σ x]

private lemma actFun_zero {m : ℕ} (σ : FPFInv (2 * m)) (x : Fin (2 * m)) :
    actFun σ 0 x = x := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp [actFun, h01]

private lemma actFun_self {m : ℕ} (σ : FPFInv (2 * m)) (c : Fin m → ZMod 2) (x : Fin (2 * m)) :
    actFun σ c (actFun σ c x) = x := by
  rw [← actFun_add]
  have hcc : c + c = 0 := by
    funext i
    exact (show ∀ z : ZMod 2, z + z = 0 by decide) (c i)
  rw [hcc, actFun_zero]

private def phi {n m : ℕ} (hmn : 2 * m ≤ n) (σ : FPFInv (2 * m)) (c : Fin m → ZMod 2) :
    Equiv.Perm (Fin n) := by
  let f : Fin n → Fin n := fun y =>
    if h : y.1 < 2 * m then ⟨(actFun σ c ⟨y.1, h⟩).1, by omega⟩ else y
  have hinv : Function.LeftInverse f f := by
    intro y
    dsimp only [f]
    by_cases h : y.1 < 2 * m
    · simp only [h, ↓reduceDIte]
      have h2 : (actFun σ c ⟨y.1, h⟩).1 < 2 * m := (actFun σ c ⟨y.1, h⟩).2
      simp only [h2, ↓reduceDIte]
      apply Fin.ext
      exact congrArg (fun z : Fin (2 * m) => z.1) (actFun_self σ c ⟨y.1, h⟩)
    · simp only [h, ↓reduceDIte]
  exact ⟨f, f, hinv, hinv⟩

private lemma phi_apply_lt {n m : ℕ} (hmn : 2 * m ≤ n) (σ : FPFInv (2 * m))
    (c : Fin m → ZMod 2) (x : Fin (2 * m)) :
    phi hmn σ c ⟨x.1, by omega⟩ = ⟨(actFun σ c x).1, by omega⟩ := by
  simp [phi, x.2]

private lemma phi_zero {n m : ℕ} (hmn : 2 * m ≤ n) (σ : FPFInv (2 * m)) :
    phi hmn σ 0 = 1 := by
  ext y
  dsimp only [phi]
  by_cases h : y.1 < 2 * m
  · simp [actFun_zero]
  · simp [h]

private lemma phi_add {n m : ℕ} (hmn : 2 * m ≤ n) (σ : FPFInv (2 * m))
    (c₁ c₂ : Fin m → ZMod 2) :
    phi hmn σ (c₁ + c₂) = phi hmn σ c₁ * phi hmn σ c₂ := by
  ext y
  change (phi hmn σ (c₁ + c₂) y).1 = (phi hmn σ c₁ (phi hmn σ c₂ y)).1
  by_cases h : y.1 < 2 * m
  · have h2 : (actFun σ c₂ ⟨y.1, h⟩).1 < 2 * m := (actFun σ c₂ ⟨y.1, h⟩).2
    simp only [phi, Equiv.coe_fn_mk, h, ↓reduceDIte, h2]
    exact congrArg (fun z : Fin (2 * m) => z.1) (actFun_add σ c₁ c₂ ⟨y.1, h⟩)
  · simp [phi, h]

private lemma phi_injective {n m : ℕ} (hmn : 2 * m ≤ n) (σ : FPFInv (2 * m)) :
    Function.Injective (phi hmn σ) := by
  intro c₁ c₂ hc
  funext k
  let x := lowAt σ k
  have hx := congrArg (fun p : Equiv.Perm (Fin n) => (p ⟨x.1, by omega⟩).1) hc
  simp only [phi_apply_lt] at hx
  have hact : actFun σ c₁ x = actFun σ c₂ x := Fin.ext hx
  unfold actFun at hact
  rw [pairIdx_lowAt σ k] at hact
  have hbit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hne : σ.1 x ≠ x := σ.2.2 x
  rcases hbit (c₁ k) with h1 | h1 <;> rcases hbit (c₂ k) with h2 | h2
  · rw [h1, h2]
  · simp [h1, h2] at hact
    exact absurd hact.symm hne
  · simp [h1, h2] at hact
    exact absurd hact hne
  · rw [h1, h2]

private abbrev NonzeroRows (a b : ℕ) := Fin b → { v : Fin a → ZMod 2 // v ≠ 0 }

private def InGraph {m a b : ℕ} (hab : a + b = m) (L : NonzeroRows a b)
    (c : Fin m → ZMod 2) : Prop :=
  ∀ j : Fin b, c ⟨a + j.1, by omega⟩ = ∑ i : Fin a, (L j).1 i * c ⟨i.1, by omega⟩

private def graphSubgroup {n m a b : ℕ} (hmn : 2 * m ≤ n) (hab : a + b = m)
    (σ : FPFInv (2 * m)) (L : NonzeroRows a b) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := { p | ∃ c : Fin m → ZMod 2, InGraph hab L c ∧ p = phi hmn σ c }
  one_mem' := ⟨0, fun j => by simp, (phi_zero hmn σ).symm⟩
  mul_mem' := by
    rintro p₁ p₂ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩
    refine ⟨c₁ + c₂, fun j => ?_, (phi_add hmn σ c₁ c₂).symm⟩
    simp only [Pi.add_apply, h₁ j, h₂ j, mul_add, Finset.sum_add_distrib]
  inv_mem' := by
    rintro p ⟨c, hc, rfl⟩
    refine ⟨c, hc, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [← phi_add]
    have hcc : c + c = 0 := by
      funext i
      exact (show ∀ z : ZMod 2, z + z = 0 by decide) (c i)
    rw [hcc, phi_zero]

private def basisVec {m a b : ℕ} (hab : a + b = m) (L : NonzeroRows a b) (i₀ : Fin a) :
    Fin m → ZMod 2 := fun k =>
  if h : k.1 < a then
    if k.1 = i₀.1 then 1 else 0
  else
    (L ⟨k.1 - a, by omega⟩).1 i₀

private lemma basisVec_lt {m a b : ℕ} (hab : a + b = m) (L : NonzeroRows a b) (i₀ : Fin a) :
    basisVec hab L i₀ ⟨i₀.1, by omega⟩ = 1 := by
  simp [basisVec, i₀.2]

private lemma basisVec_ge {m a b : ℕ} (hab : a + b = m) (L : NonzeroRows a b) (i₀ : Fin a)
    (j : Fin b) :
    basisVec hab L i₀ ⟨a + j.1, by omega⟩ = (L j).1 i₀ := by
  have h1 : ¬ (a + j.1 < a) := by omega
  dsimp only [basisVec]
  simp only [h1, ↓reduceDIte]
  exact congrArg (fun idx : Fin b => (L idx).1 i₀) (Fin.ext (show a + j.1 - a = j.1 by omega))

private lemma basisVec_inGraph {m a b : ℕ} (hab : a + b = m) (L : NonzeroRows a b) (i₀ : Fin a) :
    InGraph hab L (basisVec hab L i₀) := by
  intro j
  rw [basisVec_ge hab L i₀ j]
  have hrhs : ∑ i : Fin a, (L j).1 i * basisVec hab L i₀ ⟨i.1, by omega⟩ = (L j).1 i₀ := by
    trans ∑ i : Fin a, if i = i₀ then (L j).1 i else 0
    · refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [basisVec]
      simp only [i.2, ↓reduceDIte]
      by_cases hi : i = i₀
      · subst hi; simp
      · have hval : i.1 ≠ i₀.1 := fun h => hi (Fin.ext h)
        simp [hi, hval]
    · simp
  exact hrhs.symm

private lemma exists_graph_with_one {m a b : ℕ} (hab : a + b = m) (L : NonzeroRows a b)
    (k : Fin m) : ∃ c : Fin m → ZMod 2, InGraph hab L c ∧ c k = 1 := by
  by_cases hk : k.1 < a
  · refine ⟨basisVec hab L ⟨k.1, hk⟩, basisVec_inGraph hab L _, ?_⟩
    simpa [Fin.ext_iff] using basisVec_lt hab L ⟨k.1, hk⟩
  · let j : Fin b := ⟨k.1 - a, by omega⟩
    have hne : (L j).1 ≠ 0 := (L j).2
    have hex : ∃ i₀ : Fin a, (L j).1 i₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    have h1 : (L j).1 i₀ = 1 := by
      rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) ((L j).1 i₀) with h | h
      · exact absurd h hi₀
      · exact h
    refine ⟨basisVec hab L i₀, basisVec_inGraph hab L i₀, ?_⟩
    have hk_eq : k = ⟨a + j.1, by omega⟩ := Fin.ext (by dsimp only [j]; omega)
    rw [hk_eq, basisVec_ge hab L i₀ j, h1]

private lemma graphSubgroup_ne_bot {n m a b : ℕ} (hmn : 2 * m ≤ n) (hab : a + b = m)
    (ha : 1 ≤ a) (σ : FPFInv (2 * m)) (L : NonzeroRows a b) :
    graphSubgroup hmn hab σ L ≠ ⊥ := by
  intro hbot
  let i₀ : Fin a := ⟨0, by omega⟩
  let c := basisVec hab L i₀
  have hmem : phi hmn σ c ∈ graphSubgroup hmn hab σ L := ⟨c, basisVec_inGraph hab L i₀, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hc0 : c = 0 := phi_injective hmn σ (hmem.trans (phi_zero hmn σ).symm)
  have h1 : (1 : ZMod 2) = 0 := by
    have := congrArg (fun f : Fin m → ZMod 2 => f ⟨i₀.1, by omega⟩) hc0
    dsimp only [c] at this
    rw [basisVec_lt hab L i₀] at this
    exact this
  exact absurd h1 (by decide)

private lemma graphSubgroup_injective {n m a b : ℕ} (hmn : 2 * m ≤ n) (hab : a + b = m) :
    Function.Injective (fun p : FPFInv (2 * m) × NonzeroRows a b =>
      graphSubgroup hmn hab p.1 p.2) := by
  rintro ⟨σ₁, L₁⟩ ⟨σ₂, L₂⟩ hH
  dsimp only at hH
  have hσ : σ₁ = σ₂ := by
    apply Subtype.ext
    ext x
    obtain ⟨c, hc, hck⟩ := exists_graph_with_one hab L₁ (pairIdx σ₁ x)
    have hmem : phi hmn σ₁ c ∈ graphSubgroup hmn hab σ₂ L₂ := by
      rw [← hH]
      exact ⟨c, hc, rfl⟩
    obtain ⟨c', _, heq⟩ := hmem
    have hy := congrArg (fun p : Equiv.Perm (Fin n) => (p ⟨x.1, by omega⟩).1) heq
    simp only [phi_apply_lt] at hy
    have hact1 : actFun σ₁ c x = σ₁.1 x := by simp [actFun, hck]
    rw [hact1] at hy
    unfold actFun at hy
    split_ifs at hy with h'
    · exact hy
    · exact absurd (Fin.ext hy) (σ₁.2.2 x)
  subst hσ
  have hL : L₁ = L₂ := by
    funext j
    apply Subtype.ext
    funext i₀
    let c := basisVec hab L₁ i₀
    have hmem : phi hmn σ₁ c ∈ graphSubgroup hmn hab σ₁ L₂ := by
      rw [← hH]
      exact ⟨c, basisVec_inGraph hab L₁ i₀, rfl⟩
    obtain ⟨c', hc', heq⟩ := hmem
    have hceq : c = c' := phi_injective hmn σ₁ heq
    subst hceq
    have h1 := basisVec_ge hab L₁ i₀ j
    have h2 := hc' j
    have hsum : ∑ i : Fin a, (L₂ j).1 i * c ⟨i.1, by omega⟩ = (L₂ j).1 i₀ := by
      trans ∑ i : Fin a, if i = i₀ then (L₂ j).1 i else 0
      · refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [c, basisVec]
        simp only [i.2, ↓reduceDIte]
        by_cases hi : i = i₀
        · subst hi; simp
        · have hval : i.1 ≠ i₀.1 := fun h => hi (Fin.ext h)
          simp [hi, hval]
      · simp
    dsimp only [c] at h2 hsum
    rw [← h1, h2, hsum]
  exact Prod.ext rfl hL

private lemma card_nonzero_vec (a : ℕ) :
    Nat.card { v : Fin a → ZMod 2 // v ≠ 0 } = 2 ^ a - 1 := by
  classical
  have heq : Nat.card { v : Fin a → ZMod 2 // v ≠ 0 } =
      ((Finset.univ : Finset (Fin a → ZMod 2)).erase 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext v
    simp [Finset.mem_erase]
  rw [heq, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma main_combinatorial_lower (n : ℕ) (hn : 4 ≤ n) :
    oddFact (n / 2) * (2 ^ (n / 2 / 2) - 1) ^ (n / 2 - n / 2 / 2) + 1 ≤ Erdos1162.f n := by
  set m := n / 2
  set a := m / 2
  set b := m - a
  have hmn : 2 * m ≤ n := by omega
  have hab : a + b = m := by omega
  have ha : 1 ≤ a := by omega
  let embed : Option (FPFInv (2 * m) × NonzeroRows a b) → Subgroup (Equiv.Perm (Fin n))
    | none => ⊥
    | some p => graphSubgroup hmn hab p.1 p.2
  have hinj : Function.Injective embed := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some q => exact absurd hxy.symm (graphSubgroup_ne_bot hmn hab ha q.1 q.2)
    | some p =>
      cases y with
      | none => exact absurd hxy (graphSubgroup_ne_bot hmn hab ha p.1 p.2)
      | some q => exact congrArg some (graphSubgroup_injective hmn hab hxy)
  have hcard := Nat.card_le_card_of_injective embed hinj
  rw [Nat.card_eq_fintype_card (α := Option _), Fintype.card_option,
    ← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_fun, Nat.card_fin,
    card_nonzero_vec] at hcard
  have hmul : oddFact m * (2 ^ a - 1) ^ b ≤
      Nat.card (FPFInv (2 * m)) * (2 ^ a - 1) ^ b :=
    Nat.mul_le_mul_right _ (oddFact_le_card_fpfInv m)
  exact (Nat.add_le_add_right hmul 1).trans hcard

/- ### Part 4: Analytic inequalities for α = 1 / 64 -/

private lemma logb_two_pow_nat (k : ℕ) : Real.logb 2 ((2 : ℝ) ^ k) = (k : ℝ) := by
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

private lemma logb_two_le_of_le_pow {n k : ℕ} (hn : 0 < n) (h : n ≤ 2 ^ k) :
    Real.logb 2 (n : ℝ) ≤ (k : ℝ) := by
  calc Real.logb 2 (n : ℝ)
      ≤ Real.logb 2 ((2 : ℝ) ^ k) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast h)
    _ = (k : ℝ) := logb_two_pow_nat k

private lemma small_log_ceil (n : ℕ) :
    n ≤ 31 →
      n ≤ 2 ^ (if n ≤ 4 then 2 else if n ≤ 8 then 3 else if n ≤ 16 then 4 else 5) := by
  intro hn
  split_ifs <;> omega

private lemma small_range_nat_check :
    ∀ n : Fin 32, 4 ≤ n.1 →
      2 ^ ((4 * n.1 ^ 2 + n.1 * (if n.1 ≤ 4 then 2 else if n.1 ≤ 8 then 3 else if n.1 ≤ 16 then 4 else 5) + 63) / 64) ≤
        oddFact (n.1 / 2) * (2 ^ (n.1 / 2 / 2) - 1) ^ (n.1 / 2 - n.1 / 2 / 2) + 1 := by
  decide

private lemma bound_large (n : ℕ) (hn : 32 ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + (1 / 64 : ℝ) * n * Real.logb 2 n) ≤ (Erdos1162.f n : ℝ) := by
  set m := n / 2
  set a := m / 2
  set b := m - a
  have hm_pos : 0 < m := by omega
  have ha_pos : 1 ≤ a := by omega
  have hm_real : (0 : ℝ) < m := by positivity
  have hn_real : (0 : ℝ) < n := by positivity
  have hL5 : (5 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    calc (5 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (5 : ℕ)) := (logb_two_pow_nat 5).symm
      _ ≤ Real.logb 2 (n : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) (by norm_num; exact_mod_cast hn)
  have h4m : n ≤ 4 * m := by omega
  have hlogm : Real.logb 2 (n : ℝ) - 2 ≤ Real.logb 2 (m : ℝ) := by
    have h1 : Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((4 : ℝ) * (m : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) hn_real (by exact_mod_cast h4m)
    have h2 : Real.logb 2 ((4 : ℝ) * (m : ℝ)) = 2 + Real.logb 2 (m : ℝ) := by
      rw [Real.logb_mul (by norm_num) hm_real.ne']
      have h4 : Real.logb 2 (4 : ℝ) = 2 := by
        simpa [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num] using logb_two_pow_nat 2
      rw [h4]
    linarith
  have h_ab_nat : n ^ 2 ≤ 16 * ((a - 1) * b) + 8 * n + 7 := by
    have hn1 : (n - 1) + 1 = n := by omega
    have hm1 : (m - 1) + 1 = m := by omega
    have hmn2 : 2 * m ≤ n := by omega
    have h2m : n - 1 ≤ 2 * m := by omega
    have h2a : m - 1 ≤ 2 * a := by omega
    have h2b : m ≤ 2 * b := by omega
    have hbm : 2 * b ≤ m + 1 := by omega
    have h1 : (n - 1) ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left h2m 2
    have h2 : (m - 1) * m ≤ (2 * a) * (2 * b) := Nat.mul_le_mul h2a h2b
    have h3 : (a - 1) * b + b = a * b := by
      have : a = (a - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    nlinarith
  have h_ab_real : ((n : ℝ) ^ 2 - 8 * (n : ℝ) - 7) / 16 ≤ (((a - 1) * b : ℕ) : ℝ) := by
    have hcast : ((n ^ 2 : ℕ) : ℝ) ≤ ((16 * ((a - 1) * b) + 8 * n + 7 : ℕ) : ℝ) := by
      exact_mod_cast h_ab_nat
    push_cast at hcast ⊢
    linarith
  have hb_real : ((n : ℝ) - 1) / 4 ≤ (b : ℝ) := by
    have hb_nat : n - 1 ≤ 4 * b := by omega
    have hcast : ((n - 1 : ℕ) : ℝ) ≤ ((4 * b : ℕ) : ℝ) := by exact_mod_cast hb_nat
    rw [Nat.cast_sub (by omega : 1 ≤ n)] at hcast
    push_cast at hcast
    linarith
  have hexp :
      (n : ℝ) ^ 2 / 16 + (1 / 64 : ℝ) * (n : ℝ) * Real.logb 2 (n : ℝ) ≤
        (((a - 1) * b : ℕ) : ℝ) + (b : ℝ) * Real.logb 2 (m : ℝ) := by
    have hN32 : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hL2 : 0 ≤ Real.logb 2 (n : ℝ) - 2 := by linarith
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
    have hbmul : ((n : ℝ) - 1) / 4 * (Real.logb 2 (n : ℝ) - 2) ≤
        (b : ℝ) * Real.logb 2 (m : ℝ) := by
      calc ((n : ℝ) - 1) / 4 * (Real.logb 2 (n : ℝ) - 2)
          ≤ (b : ℝ) * (Real.logb 2 (n : ℝ) - 2) := mul_le_mul_of_nonneg_right hb_real hL2
        _ ≤ (b : ℝ) * Real.logb 2 (m : ℝ) := mul_le_mul_of_nonneg_left hlogm hb0
    nlinarith
  have hpow2 : (2 : ℕ) ^ (a - 1) ≤ 2 ^ a - 1 := by
    have ha1 : 2 ^ a = 2 ^ (a - 1) + 2 ^ (a - 1) := by
      have : a = (a - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    have hpos : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
    omega
  have hnat_bound : 2 ^ ((a - 1) * b) * m ^ b ≤ Erdos1162.f n := by
    have h1 : 2 ^ ((a - 1) * b) ≤ (2 ^ a - 1) ^ b := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left hpow2 b
    have h2 : m ^ b ≤ oddFact m := pow_le_oddFact m
    have h3 : 2 ^ ((a - 1) * b) * m ^ b ≤ oddFact m * (2 ^ a - 1) ^ b := by
      rw [mul_comm (oddFact m)]
      exact Nat.mul_le_mul h1 h2
    exact (h3.trans (Nat.le_succ _)).trans (main_combinatorial_lower n (by omega))
  calc (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + (1 / 64 : ℝ) * (n : ℝ) * Real.logb 2 (n : ℝ))
      ≤ (2 : ℝ) ^ ((((a - 1) * b : ℕ) : ℝ) + (b : ℝ) * Real.logb 2 (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2 : ℝ) ^ ((((a - 1) * b : ℕ) : ℝ)) * (2 : ℝ) ^ ((b : ℝ) * Real.logb 2 (m : ℝ)) :=
        Real.rpow_add (by norm_num) _ _
    _ = ((2 ^ ((a - 1) * b) : ℕ) : ℝ) * ((m ^ b : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
        congr 1
        rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hm_real,
          Real.rpow_natCast, Nat.cast_pow]
    _ = ((2 ^ ((a - 1) * b) * m ^ b : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (Erdos1162.f n : ℝ) := by exact_mod_cast hnat_bound

end Erdos1162Lower

theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_bounds_R1.H1 := by
  refine ⟨1 / 64, by norm_num, fun n hn => ?_⟩
  by_cases h2 : n = 2
  · subst h2
    have hlog : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    calc (2 : ℝ) ^ (((2 : ℕ) : ℝ) ^ 2 / 16 + (1 / 64 : ℝ) * (2 : ℕ) * Real.logb 2 (2 : ℕ))
        ≤ (2 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          push_cast
          rw [hlog]
          norm_num
      _ = (2 : ℝ) := by norm_num
      _ ≤ (Erdos1162.f 2 : ℝ) := by exact_mod_cast Erdos1162Lower.two_le_f_two
  · by_cases h3 : n = 3
    · subst h3
      have hlog : Real.logb 2 (3 : ℝ) ≤ 2 :=
        Erdos1162Lower.logb_two_le_of_le_pow (n := 3) (k := 2) (by omega) (by norm_num)
      calc (2 : ℝ) ^ (((3 : ℕ) : ℝ) ^ 2 / 16 + (1 / 64 : ℝ) * (3 : ℕ) * Real.logb 2 (3 : ℕ))
          ≤ (2 : ℝ) ^ (2 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            push_cast
            linarith
        _ = (4 : ℝ) := by norm_num
        _ ≤ (Erdos1162.f 3 : ℝ) := by exact_mod_cast Erdos1162Lower.four_le_f_three
    · by_cases h32 : 32 ≤ n
      · exact Erdos1162Lower.bound_large n h32
      · have hn4 : 4 ≤ n := by omega
        have hn31 : n ≤ 31 := by omega
        let k : ℕ := if n ≤ 4 then 2 else if n ≤ 8 then 3 else if n ≤ 16 then 4 else 5
        have hlog : Real.logb 2 (n : ℝ) ≤ (k : ℝ) :=
          Erdos1162Lower.logb_two_le_of_le_pow (by omega) (Erdos1162Lower.small_log_ceil n hn31)
        set e : ℕ := (4 * n ^ 2 + n * k + 63) / 64
        have hexp_nat : 4 * n ^ 2 + n * k ≤ 64 * e := by dsimp only [e]; omega
        have hexp_real :
            (n : ℝ) ^ 2 / 16 + (1 / 64 : ℝ) * (n : ℝ) * Real.logb 2 (n : ℝ) ≤ (e : ℝ) := by
          have h1 : (n : ℝ) ^ 2 / 16 + (1 / 64 : ℝ) * (n : ℝ) * Real.logb 2 (n : ℝ) ≤
              (n : ℝ) ^ 2 / 16 + (1 / 64 : ℝ) * (n : ℝ) * (k : ℝ) := by
            gcongr
          have h2 : ((4 * n ^ 2 + n * k : ℕ) : ℝ) ≤ ((64 * e : ℕ) : ℝ) := by
            exact_mod_cast hexp_nat
          push_cast at h2
          linarith
        have hnat : 2 ^ e ≤ Erdos1162.f n :=
          (Erdos1162Lower.small_range_nat_check ⟨n, by omega⟩ hn4).trans
            (Erdos1162Lower.main_combinatorial_lower n hn4)
        calc (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + (1 / 64 : ℝ) * (n : ℝ) * Real.logb 2 (n : ℝ))
            ≤ (2 : ℝ) ^ (e : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_real
          _ = ((2 ^ e : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
          _ ≤ (Erdos1162.f n : ℝ) := by exact_mod_cast hnat
