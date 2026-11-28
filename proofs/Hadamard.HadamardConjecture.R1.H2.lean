import OMAReductions.R_Hadamard_HadamardConjecture_R1

/-! Paley II: a Hadamard matrix of order 2(q + 1) for every prime power q = 1 (mod 4). -/

-- Step Hadamard.HadamardConjecture.R1.H2: hypothesis H2 of reduction Hadamard.HadamardConjecture.R1
-- Upstream: FormalConjectures/Wikipedia/Hadamard.lean (Hadamard.HadamardConjecture), reduction R1
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Formalises the classical Paley construction (R. E. A. C. Paley, On orthogonal matrices, 1933);
-- no new result is claimed.
--
-- Proof idea. Let F be the field with q elements and chi its quadratic character. On the index set
-- Option F put the conference matrix C with C none none = 0, C none (some b) = 1,
-- C (some a) none = chi (-1) and C (some a) (some b) = chi (a - b). The character sum
-- sum_c chi (c) chi (c + d) = -1 for d nonzero gives C * C^T = q * 1, and C^T = chi (-1) * C.
-- For q = 1 (mod 4), chi (-1) = 1, so C is symmetric with C * C = q * 1, and the block matrix
-- H = [[C + 1, C - 1], [C - 1, -C - 1]] satisfies H^T H = 2 (q + 1) * 1.

namespace OMA_Hadamard_R1_H2

open Matrix Finset

section CharSums

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The basic character sum: `∑_c χ(c) χ(c + d) = -1` for `d ≠ 0`. -/
lemma sum_chi_mul_chi_add (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    ∑ c : F, quadraticChar F c * quadraticChar F (c + d) = -1 := by
  have h1 : ∀ c : F, quadraticChar F c * quadraticChar F (c + d) =
      quadraticChar F (1 + d * c⁻¹) - (if c = 0 then 1 else 0) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp [quadraticChar_zero]
    · have hcd : c + d = c * (1 + d * c⁻¹) := by field_simp
      rw [hcd, map_mul, ← mul_assoc, if_neg hc, sub_zero]
      have hsq : quadraticChar F c * quadraticChar F c = 1 := by
        rw [← sq]; exact quadraticChar_sq_one hc
      rw [hsq, one_mul]
  have hbij : Function.Bijective (fun c : F => 1 + d * c⁻¹) := by
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    have : d * a⁻¹ = d * b⁻¹ := by simpa using hab
    have : a⁻¹ = b⁻¹ := mul_left_cancel₀ hd this
    exact inv_injective this
  have h2 : ∑ c : F, quadraticChar F (1 + d * c⁻¹) = 0 := by
    rw [Fintype.sum_bijective _ hbij (fun c => quadraticChar F (1 + d * c⁻¹))
      (fun e => quadraticChar F e) (fun _ => rfl)]
    exact quadraticChar_sum_zero hF
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_sub_distrib, h2]
  simp

lemma sum_chi_sub (hF : ringChar F ≠ 2) (a : F) : ∑ x : F, quadraticChar F (a - x) = 0 := by
  rw [Fintype.sum_equiv (Equiv.subLeft a) (fun x => quadraticChar F (a - x))
    (fun c => quadraticChar F c) (fun _ => rfl)]
  exact quadraticChar_sum_zero hF

lemma sum_chi_sub_mul_ne (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ x : F, quadraticChar F (a - x) * quadraticChar F (b - x) = -1 := by
  rw [Fintype.sum_equiv (Equiv.subLeft a)
    (fun x => quadraticChar F (a - x) * quadraticChar F (b - x))
    (fun c => quadraticChar F c * quadraticChar F (c + (b - a))) (fun x => by
      simp only [Equiv.subLeft_apply]; congr 2; ring)]
  exact sum_chi_mul_chi_add hF (sub_ne_zero.mpr (Ne.symm hab))

lemma sum_chi_sub_sq (a : F) :
    ∑ x : F, quadraticChar F (a - x) * quadraticChar F (a - x) = (Fintype.card F : ℤ) - 1 := by
  have h : ∀ x : F, quadraticChar F (a - x) * quadraticChar F (a - x) =
      1 - (if x = a then 1 else 0) := by
    intro x
    by_cases hx : x = a
    · subst hx; simp [quadraticChar_zero]
    · rw [if_neg hx, sub_zero, ← sq]
      exact quadraticChar_sq_one (sub_ne_zero.mpr (Ne.symm hx))
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_sub_distrib]
  simp

end CharSums

section Conference

variable (F : Type) [Field F] [Fintype F] [DecidableEq F]

/-- The Paley conference matrix on `Option F`. -/
def conf (ε : ℤ) : Matrix (Option F) (Option F) ℤ
  | none, none => 0
  | none, some _ => 1
  | some _, none => ε
  | some a, some b => quadraticChar F (a - b)

variable {F}

lemma conf_mul_transpose (hF : ringChar F ≠ 2) {ε : ℤ} (hε : ε * ε = 1) :
    conf F ε * (conf F ε)ᵀ = (Fintype.card F : ℤ) • (1 : Matrix (Option F) (Option F) ℤ) := by
  ext x y
  rw [mul_apply, Fintype.sum_option]
  rcases x with _ | a <;> rcases y with _ | b
  · simp [conf]
  · simp only [conf, transpose_apply, zero_mul, one_mul, zero_add, Matrix.smul_apply, one_apply,
      reduceCtorEq, if_false, smul_zero]
    exact sum_chi_sub hF b
  · simp only [conf, transpose_apply, mul_zero, mul_one, zero_add, Matrix.smul_apply, one_apply,
      reduceCtorEq, if_false, smul_zero]
    exact sum_chi_sub hF a
  · simp only [conf, transpose_apply, Matrix.smul_apply, one_apply, Option.some.injEq, hε]
    by_cases hab : a = b
    · subst hab
      rw [sum_chi_sub_sq, if_pos rfl]
      simp
    · rw [sum_chi_sub_mul_ne hF hab, if_neg hab]
      simp

lemma conf_transpose {ε : ℤ} (hε : ε = quadraticChar F (-1)) (hε2 : ε * ε = 1) :
    (conf F ε)ᵀ = ε • conf F ε := by
  ext x y
  rcases x with _ | a <;> rcases y with _ | b
  · simp [conf]
  · simp [conf]
  · simp [conf, hε2]
  · simp only [conf, transpose_apply, Matrix.smul_apply, smul_eq_mul, hε]
    rw [← map_mul]
    congr 1
    ring

lemma conf_entries (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (x y : Option F) :
    (x = y ∧ conf F ε x y = 0) ∨ (x ≠ y ∧ (conf F ε x y = 1 ∨ conf F ε x y = -1)) := by
  rcases x with _ | a <;> rcases y with _ | b
  · left; simp [conf]
  · right; simp [conf]
  · right; simp [conf, hε]
  · by_cases hab : a = b
    · left; subst hab; simp [conf, quadraticChar_zero]
    · right
      refine ⟨by simpa using hab, ?_⟩
      exact quadraticChar_dichotomy (sub_ne_zero.mpr hab)

end Conference


/-- Transport an integer `±1` matrix with `Mᵀ M = n` to a real Hadamard matrix on `Fin n`. -/
lemma pack {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : Fin n ≃ ι) (M : Matrix ι ι ℤ)
    (entries : ∀ i j, M i j = 1 ∨ M i j = -1)
    (gram : Mᵀ * M = (n : ℤ) • (1 : Matrix ι ι ℤ)) :
    ∃ W, Hadamard.IsHadamard' (n := n) W := by
  refine ⟨Matrix.of fun i j => (M (e i) (e j) : ℝ), ?_, ?_⟩
  · intro i j
    rcases entries (e i) (e j) with h | h <;> simp [h, Matrix.of_apply]
  · ext i j
    have hg := congrFun (congrFun gram (e i)) (e j)
    rw [mul_apply] at hg
    simp only [transpose_apply, Matrix.smul_apply, one_apply, EmbeddingLike.apply_eq_iff_eq,
      smul_eq_mul, mul_ite, mul_one, mul_zero] at hg
    rw [mul_apply, Matrix.natCast_apply]
    simp only [transpose_apply, Matrix.of_apply]
    have : (∑ k : Fin n, (M (e k) (e i) : ℝ) * (M (e k) (e j) : ℝ)) =
        ((∑ k : ι, M k (e i) * M k (e j) : ℤ) : ℝ) := by
      push_cast
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [this, hg]
    split_ifs <;> simp

/-- Entries of the Paley II block matrix are `±1`. -/
lemma block_entries {ι : Type} [DecidableEq ι] (C : Matrix ι ι ℤ)
    (hC : ∀ x y, (x = y ∧ C x y = 0) ∨ (x ≠ y ∧ (C x y = 1 ∨ C x y = -1))) :
    ∀ i j, fromBlocks (C + 1) (C - 1) (C - 1) (-C - 1) i j = 1 ∨
      fromBlocks (C + 1) (C - 1) (C - 1) (-C - 1) i j = -1 := by
  rintro (i | i) (j | j) <;> rcases hC i j with ⟨rfl, h0⟩ | ⟨hij, h | h⟩ <;>
    simp_all [Matrix.one_apply]

/-- Paley II over an abstract finite field. -/
theorem paley_two (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (h1 : Fintype.card F % 4 = 1) :
    ∃ W, Hadamard.IsHadamard' (n := 2 * (Fintype.card F + 1)) W := by
  have hF : ringChar F ≠ 2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  have hpos : quadraticChar F (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  set C := conf F 1 with hCdef
  have hCt : Cᵀ = C := by
    have := conf_transpose (F := F) (ε := 1) hpos.symm (by norm_num)
    rw [one_smul] at this
    exact this
  have hCC : C * C = (Fintype.card F : ℤ) • 1 := by
    have := conf_mul_transpose (F := F) hF (ε := 1) (by norm_num)
    rwa [← hCdef, hCt] at this
  have e : Fin (2 * (Fintype.card F + 1)) ≃ Option F ⊕ Option F :=
    (Fintype.equivFinOfCardEq (by simp [Fintype.card_sum]; ring)).symm
  refine pack e (fromBlocks (C + 1) (C - 1) (C - 1) (-C - 1)) ?_ ?_
  · exact block_entries C (conf_entries (F := F) 1 (Or.inl rfl))
  · have hs : (((2 * (Fintype.card F + 1) : ℕ) : ℤ)) • (1 : Matrix (Option F) (Option F) ℤ) =
        C * C + C * C + 1 + 1 := by
      rw [hCC]; push_cast
      rw [show (2 * ((Fintype.card F : ℤ) + 1)) = (Fintype.card F : ℤ) + Fintype.card F + 1 + 1
        by ring, add_smul, add_smul, add_smul, one_smul]
    rw [fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, smul_zero,
      hs]
    simp only [transpose_add, transpose_sub, transpose_neg, transpose_one, hCt]
    congr 1 <;> noncomm_ring

theorem main_h2 : OMA.R_Hadamard_HadamardConjecture_R1.H2 := by
  intro q hq h1
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hq
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p k (by omega)]
  have := paley_two (GaloisField p k) (by rw [hcard]; exact h1)
  rwa [hcard] at this

end OMA_Hadamard_R1_H2

theorem OMA.solution : OMA.R_Hadamard_HadamardConjecture_R1.H2 := OMA_Hadamard_R1_H2.main_h2
