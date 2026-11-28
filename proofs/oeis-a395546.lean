import OMAStatements.S_oeis_a395546

namespace OMA.P_oeis_a395546

open OMA.S_oeis_a395546

private def posClause {n : ℕ} (i : Fin n) : Clause3 n :=
  Sym.replicate 3 (i, true)

private def negClause {n : ℕ} (i : Fin n) : Clause3 n :=
  Sym.replicate 3 (i, false)

private def isMono {n : ℕ} (c : Clause3 n) : Prop :=
  ∃ i : Fin n, c = posClause i ∨ c = negClause i

private abbrev NonMonoClause (n : ℕ) := { c : Clause3 n // ¬ isMono c }

private lemma mem_posClause_iff {n : ℕ} (i : Fin n) (l : Fin n × Bool) :
    l ∈ posClause i ↔ l = (i, true) := by
  simp [posClause, Sym.mem_replicate]

private lemma mem_negClause_iff {n : ℕ} (i : Fin n) (l : Fin n × Bool) :
    l ∈ negClause i ↔ l = (i, false) := by
  simp [negClause, Sym.mem_replicate]

private lemma posClause_ne_negClause {n : ℕ} (i j : Fin n) :
    posClause i ≠ negClause j := by
  intro h
  have hmem : (i, true) ∈ posClause i := (mem_posClause_iff i (i, true)).mpr rfl
  rw [h, mem_negClause_iff] at hmem
  cases hmem

private lemma posClause_injective {n : ℕ} : Function.Injective (posClause (n := n)) := by
  intro i j h
  have hmem : (i, true) ∈ posClause i := (mem_posClause_iff i (i, true)).mpr rfl
  rw [h, mem_posClause_iff] at hmem
  exact (Prod.mk.inj hmem).1

private def mkUnsatFormula {n : ℕ} (p : Fin n × Sym (NonMonoClause n) 3) : Formula3SAT5 n :=
  posClause p.1 ::ₛ (negClause p.1 ::ₛ p.2.map Subtype.val)

private lemma mkUnsatFormula_unsat {n : ℕ} (p : Fin n × Sym (NonMonoClause n) 3) :
    ¬ Satisfiable (mkUnsatFormula p) := by
  rintro ⟨α, hα⟩
  have hpos : posClause p.1 ∈ mkUnsatFormula p := Sym.mem_cons_self _ _
  have hneg : negClause p.1 ∈ mkUnsatFormula p := Sym.mem_cons_of_mem (Sym.mem_cons_self _ _)
  obtain ⟨l₁, hl₁, hsat₁⟩ := hα (posClause p.1) hpos
  obtain ⟨l₂, hl₂, hsat₂⟩ := hα (negClause p.1) hneg
  rw [mem_posClause_iff] at hl₁
  rw [mem_negClause_iff] at hl₂
  subst hl₁; subst hl₂
  simp only at hsat₁ hsat₂
  rw [hsat₁] at hsat₂
  cases hsat₂

private lemma sym_cons_inj {α : Type} {m : ℕ} (a : α) {u v : Sym α m}
    (h : a ::ₛ u = a ::ₛ v) : u = v := by
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  exact (Multiset.cons_inj_right a).mp hval

private lemma mkUnsatFormula_injective {n : ℕ} :
    Function.Injective (mkUnsatFormula (n := n)) := by
  rintro ⟨i₁, s₁⟩ ⟨i₂, s₂⟩ h
  have hmem : posClause i₁ ∈ mkUnsatFormula (i₂, s₂) := by
    rw [← h]; exact Sym.mem_cons_self _ _
  unfold mkUnsatFormula at hmem
  rw [Sym.mem_cons] at hmem
  have hi : i₁ = i₂ := by
    rcases hmem with heq | hmem2
    · exact posClause_injective heq
    · rw [Sym.mem_cons] at hmem2
      rcases hmem2 with heq2 | hmem3
      · exact absurd heq2 (posClause_ne_negClause i₁ i₂)
      · rw [Sym.mem_map] at hmem3
        obtain ⟨c, _, hc⟩ := hmem3
        exact absurd ⟨i₁, Or.inl hc⟩ c.2
  subst hi
  unfold mkUnsatFormula at h
  have h1 := sym_cons_inj (posClause i₁) h
  have h2 := sym_cons_inj (negClause i₁) h1
  have hs : s₁ = s₂ := Sym.map_injective Subtype.val_injective 3 h2
  rw [hs]

private lemma card_clause3 (n : ℕ) :
    Nat.card (Clause3 n) = (2 * n + 2).choose 3 := by
  classical
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_multichoose, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  rw [Nat.multichoose_eq]
  have h1 : n * 2 + 3 - 1 = 2 * n + 2 := by omega
  rw [h1]

private lemma card_formula3SAT5 (n : ℕ) :
    Nat.card (Formula3SAT5 n) = ((2 * n + 2).choose 3 + 4).choose 5 := by
  classical
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_multichoose]
  have hc : Fintype.card (Clause3 n) = (2 * n + 2).choose 3 := by
    rw [← Nat.card_eq_fintype_card, card_clause3]
  rw [hc, Nat.multichoose_eq]
  have h1 : (2 * n + 2).choose 3 + 5 - 1 = (2 * n + 2).choose 3 + 4 := by omega
  rw [h1]

private lemma card_nonMonoClause_ge (n : ℕ) :
    (2 * n + 2).choose 3 - 2 * n ≤ Nat.card (NonMonoClause n) := by
  classical
  have htot : Fintype.card (NonMonoClause n) =
      Fintype.card (Clause3 n) - Fintype.card { c : Clause3 n // isMono c } :=
    Fintype.card_subtype_compl isMono
  have hmono_le : Fintype.card { c : Clause3 n // isMono c } ≤ 2 * n := by
    have hsurj : Function.Surjective
        (fun p : Fin n × Bool =>
          (⟨if p.2 then posClause p.1 else negClause p.1,
            ⟨p.1, by cases p.2 <;> simp⟩⟩ : { c : Clause3 n // isMono c })) := by
      rintro ⟨c, i, hpos | hneg⟩
      · exact ⟨(i, true), Subtype.ext hpos.symm⟩
      · exact ⟨(i, false), Subtype.ext hneg.symm⟩
    have hle := Fintype.card_le_of_surjective _ hsurj
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hle
    omega
  have hc : Fintype.card (Clause3 n) = (2 * n + 2).choose 3 := by
    rw [← Nat.card_eq_fintype_card, card_clause3]
  rw [Nat.card_eq_fintype_card, htot, hc]
  omega

private lemma unsat_card_ge (n : ℕ) :
    n * (((2 * n + 2).choose 3 - 2 * n) + 2).choose 3 ≤
      Nat.card { F : Formula3SAT5 n // ¬ Satisfiable F } := by
  classical
  let f : Fin n × Sym (NonMonoClause n) 3 → { F : Formula3SAT5 n // ¬ Satisfiable F } :=
    fun p => ⟨mkUnsatFormula p, mkUnsatFormula_unsat p⟩
  have hinj : Function.Injective f := by
    intro p₁ p₂ h
    exact mkUnsatFormula_injective (congrArg Subtype.val h)
  have hle : Fintype.card (Fin n × Sym (NonMonoClause n) 3) ≤
      Fintype.card { F : Formula3SAT5 n // ¬ Satisfiable F } :=
    Fintype.card_le_of_injective f hinj
  rw [Fintype.card_prod, Fintype.card_fin, Sym.card_sym_eq_multichoose, Nat.multichoose_eq,
    ← Nat.card_eq_fintype_card (α := NonMonoClause n),
    ← Nat.card_eq_fintype_card (α := { F : Formula3SAT5 n // ¬ Satisfiable F })] at hle
  have hsub : Nat.card (NonMonoClause n) + 3 - 1 = Nat.card (NonMonoClause n) + 2 := by omega
  rw [hsub] at hle
  have hmono : (((2 * n + 2).choose 3 - 2 * n) + 2).choose 3 ≤
      (Nat.card (NonMonoClause n) + 2).choose 3 :=
    Nat.choose_le_choose 3 (by have := card_nonMonoClause_ge n; omega)
  exact le_trans (Nat.mul_le_mul_left n hmono) hle

private lemma sat_plus_unsat (n : ℕ) :
    a395546 n + Nat.card { F : Formula3SAT5 n // ¬ Satisfiable F } =
      ((2 * n + 2).choose 3 + 4).choose 5 := by
  classical
  unfold a395546
  rw [← card_formula3SAT5 n]
  simp only [Nat.card_eq_fintype_card]
  have h1 := Fintype.card_subtype_compl (α := Formula3SAT5 n) Satisfiable
  have h2 := Fintype.card_subtype_le (α := Formula3SAT5 n) Satisfiable
  omega

private lemma choose_three_formula (m : ℕ) :
    6 * m.choose 3 = m * (m - 1) * (m - 2) := by
  have h1 := Nat.choose_succ_right_eq m 2
  have h2 := Nat.choose_succ_right_eq m 1
  have h3 : m.choose 1 = m := Nat.choose_one_right m
  rw [h3] at h2
  have hmul : 6 * m.choose 3 = 2 * (m.choose 3 * 3) := by ring
  rw [hmul, h1]
  have hmul2 : 2 * (m.choose 2 * (m - 2)) = (m.choose 2 * 2) * (m - 2) := by ring
  rw [hmul2, h2]

private theorem main_disproof : ¬ (type_of% @OMA.S_oeis_a395546.main) := by
  intro hmain
  have h11 := hmain 11 (by norm_num)
  have hsum := sat_plus_unsat 11
  have hlb := unsat_card_ge 11
  have hc24 : (2 * 11 + 2).choose 3 = 2024 := by
    rw [show 2 * 11 + 2 = 24 from rfl]
    have h := choose_three_formula 24
    omega
  rw [hc24] at hlb
  have h2004 : (2024 - 2 * 11 + 2).choose 3 = 1339342004 := by
    rw [show 2024 - 2 * 11 + 2 = 2004 from rfl]
    have h := choose_three_formula 2004
    omega
  rw [h2004] at hlb
  have hlb_val : 14732762044 ≤ Nat.card { F : Formula3SAT5 11 // ¬ Satisfiable F } := by
    omega
  have hsum_int : (a395546 11 : ℤ) + (Nat.card { F : Formula3SAT5 11 // ¬ Satisfiable F } : ℤ) =
      ((((2 * 11 + 2).choose 3 + 4).choose 5 : ℕ) : ℤ) := by
    exact_mod_cast hsum
  have hlb_int : (14732762044 : ℤ) ≤ (Nat.card { F : Formula3SAT5 11 // ¬ Satisfiable F } : ℤ) := by
    exact_mod_cast hlb_val
  set T : ℤ := ((((2 * 11 + 2).choose 3 + 4).choose 5 : ℕ) : ℤ)
  have hpoly :
      (129332 * ((11 : ℕ) : ℤ) ^ 6 - 2237100 * ((11 : ℕ) : ℤ) ^ 5 +
        16427761 * ((11 : ℕ) : ℤ) ^ 4 - 63136975 * ((11 : ℕ) : ℤ) ^ 3 +
        130884126 * ((11 : ℕ) : ℤ) ^ 2 - 135887564 * ((11 : ℕ) : ℤ) + 53820480) =
      39711906750 := by norm_num
  rw [hpoly] at h11
  linarith

end OMA.P_oeis_a395546

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a395546.main) :=
  OMA.P_oeis_a395546.main_disproof

