import FormalConjectures.ErdosProblems.«302»

/-! A disjoint family of scaled unit-fraction triples gives an upper density bound of 9/10. -/

open Filter Finset
open scoped BigOperators

private def M : List ℕ :=
  [2, 3, 6, 4, 5, 20, 8, 12, 24, 10, 15, 30, 18, 27, 54, 36, 60, 90,
   32, 48, 96, 45, 72, 120, 50, 75, 150, 80, 144, 180, 81, 108, 324,
   135, 216, 360, 128, 192, 384, 162, 270, 405, 160, 240, 480, 100, 125, 500,
   200, 300, 600, 320, 576, 720, 250, 375, 750, 288, 450, 800, 432, 675, 1200,
   486, 810, 1215, 540, 900, 1350]

private def C (i : Fin 23) (j : Fin 3) : ℕ := M.get ⟨3 * i.1 + j.1, by change 3 * i.1 + j.1 < 69; omega⟩
private def R : Fin 8 → ℕ := ![1, 7, 11, 13, 17, 19, 23, 29]
private def Q (i : Fin 23) : ℕ := 116640000 / (30 * C i 2)

theorem OMA.solution : type_of% @Erdos302.erdos_302.variants.upper_nine_tenths := by
  classical
  have hM : M.Nodup := by decide
  have hC : ∀ (i : Fin 23) (j : Fin 3), 0 < C i j ∧ C i j ≤ C i 2 ∧ C i j ∣ 3888000 := by decide
  have hX : ∀ i : Fin 23, C i 1 * C i 2 = C i 0 * (C i 1 + C i 2) := by decide
  have hR : ∀ r : Fin 8, 0 < R r ∧ R r < 30 ∧ (R r).Coprime 30 := by decide
  have hRi : Function.Injective R := by decide
  have hQ : (∀ i : Fin 23, Q i * (30 * C i 2) = 116640000) ∧ (∑ i : Fin 23, 8 * Q i) = 11674120 := by decide
  have hCi : Function.Injective fun p : Fin 23 × Fin 3 => C p.1 p.2 := fun i j hij => by
    have hv := congrArg Fin.val (List.nodup_iff_injective_get.1 hM hij)
    change 3 * i.1.1 + i.2.1 = 3 * j.1.1 + j.2.1 at hv
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  intro f hf ε hε
  obtain ⟨K, hK⟩ := exists_nat_ge ((11674120 : ℝ) / ε)
  filter_upwards [eventually_ge_atTop K] with N hKN
  obtain ⟨A, hA, hfree, hcard⟩ := (hf N).1
  let B := 116640000
  let P := Σ i : Fin 23, Fin 8 × Fin ((N / B) * Q i)
  let pt (p : P) (j : Fin 3) : ℕ := C p.1 j * (30 * p.2.2.1 + R p.2.1)
  have hsc (r : Fin 8) (k : ℕ) : (30 * k + R r).Coprime 3888000 := by
    have hc : (30 * k + R r).Coprime 30 := by simpa [Nat.Coprime] using (hR r).2.2
    change (30 * k + R r).Coprime (2 ^ 7 * 3 ^ 5 * 5 ^ 3)
    exact (((hc.coprime_dvd_right (by decide)).pow_right 7).mul_right
      ((hc.coprime_dvd_right (by decide)).pow_right 5)).mul_right ((hc.coprime_dvd_right (by decide)).pow_right 3)
  have hgcd (p : P) (j : Fin 3) : (pt p j).gcd 3888000 = C p.1 j := by
    rw [show pt p j = (30 * p.2.2.1 + R p.2.1) * C p.1 j by dsimp [pt]; ring]
    exact Nat.gcd_mul_of_coprime_of_dvd (hsc p.2.1 p.2.2.1) (hC p.1 j).2.2
  have hinj : Function.Injective fun p : P × Fin 3 => pt p.1 p.2 := by
    rintro ⟨⟨i, r, k⟩, j⟩ ⟨⟨i', r', k'⟩, j'⟩ h
    have hg := congrArg (·.gcd 3888000) h; simp only [hgcd] at hg
    rcases Prod.mk.inj (hCi hg : (i, j) = (i', j')) with ⟨rfl, rfl⟩
    have hs : 30 * k.1 + R r = 30 * k'.1 + R r' := Nat.eq_of_mul_eq_mul_left (hC i j).1 h
    have := (hR r).2.1; have := (hR r').2.1
    have hk : k = k' := Fin.ext (by omega)
    have hr : r = r' := hRi (by omega)
    subst k' r'; rfl
  have hm (p : P) : ∃ j, pt p j ∉ A := by
    by_contra! h
    have hneq {j k : Fin 3} (hjk : j ≠ k) : pt p j ≠ pt p k := fun he => by
      have hp : (p, j) = (p, k) := hinj he; exact hjk (congrArg Prod.snd hp)
    have huf : (1 : ℚ) / pt p 0 = 1 / pt p 1 + 1 / pt p 2 := by
      simp only [pt, Nat.cast_mul, div_mul_eq_div_div, ← add_div]; congr 1
      have hne (j : Fin 3) : (C p.1 j : ℚ) ≠ 0 := by exact_mod_cast (hC p.1 j).1.ne'
      have hx : (C p.1 1 : ℚ) * C p.1 2 = C p.1 0 * (C p.1 1 + C p.1 2) := by exact_mod_cast hX p.1
      field_simp [hne]; nlinarith only [hx]
    exact hfree _ (h 0) _ (h 1) _ (h 2) (hneq (by decide)) (hneq (by decide)) (hneq (by decide)) huf
  choose miss hmiss using hm
  have hle : Fintype.card P ≤ (Icc 1 N \ A).card := by
    have hpt (p : P) (j : Fin 3) : pt p j ∈ Icc 1 N :=
      mem_Icc.2 ⟨Nat.mul_pos (hC p.1 j).1 (by have := (hR p.2.1).1; omega),
        calc pt p j ≤ C p.1 2 * (30 * ((N / B) * Q p.1)) :=
              Nat.mul_le_mul (hC p.1 j).2.1 (by have := (hR p.2.1).2.1; have := p.2.2.2; omega)
          _ = (N / B) * (Q p.1 * (30 * C p.1 2)) := by ring
          _ = (N / B) * B := by rw [hQ.1]
          _ ≤ N := Nat.div_mul_le_self _ _⟩
    simpa using Fintype.card_le_of_injective
      (fun p : P => (⟨pt p (miss p), mem_sdiff.2 ⟨hpt p _, hmiss p⟩⟩ : ↥(Icc 1 N \ A)))
      fun p q h => by have hp : (p, miss p) = (q, miss q) := hinj (congrArg Subtype.val h); exact congrArg Prod.fst hp
  have hPc : Fintype.card P = 11674120 * (N / B) := by
    simp only [P, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    rw [← hQ.2, sum_mul]; exact sum_congr rfl fun _ _ => by ring
  have htot := card_sdiff_add_card_eq_card hA; rw [Nat.card_Icc] at htot
  have hpackR : (f N : ℝ) + 11674120 * ((N / B : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (show f N + 11674120 * (N / B) ≤ N by omega)
  have hdivR : (N : ℝ) < 116640000 * (((N / B : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ N (by decide : 0 < B)
  have herr : (11674120 : ℝ) ≤ ε * N := by
    simpa [mul_comm] using (div_le_iff₀ hε).1 (hK.trans (by exact_mod_cast hKN))
  nlinarith [show (0 : ℝ) ≤ (N / B : ℕ) + 1 by positivity]
