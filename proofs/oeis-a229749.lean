import OMAStatements.S_oeis_a229749

namespace OMA.P_oeis_a229749

open OMA.S_oeis_a229749

private def stepErr (p0 p1 c0 c1 : Fin 4) : ℕ :=
  (if c0 = c1 then 1 else 0) + (if p0 = c0 then 1 else 0) + (if p1 = c1 then 1 else 0) + (if p0 = c1 then 1 else 0) + (if p1 = c0 then 1 else 0)

private def dp : ℕ → Bool → ℕ → ℕ
  | 0, _, _ => 0
  | 1, true, 1 => 4
  | 1, false, 0 => 12
  | 1, _, _ => 0
  | n + 1, false, 0 => 2 * dp n false 0
  | n + 1, false, 1 => 8 * dp n false 0 + 2 * dp n false 1 + 6 * dp n true 1
  | n + 1, true, 1 => 2 * dp n false 0
  | n + 1, false, 2 => 2 * dp n false 0 + 8 * dp n false 1 + 2 * dp n false 2 + 6 * dp n true 2
  | n + 1, true, 2 => 2 * dp n false 1 + 3 * dp n true 1
  | _ + 1, _, _ => 0

private lemma dp_true_zero (n : ℕ) : dp n true 0 = 0 := by
  cases n with
  | zero => rfl
  | succ m => cases m <;> rfl

private lemma dp_closed (m : ℕ) :
    dp (m + 3) false 0 = 48 * 2 ^ m ∧
    dp (m + 3) false 1 = (336 * m + 576) * 2 ^ m ∧
    dp (m + 3) true 1 = 48 * 2 ^ m ∧
    dp (m + 3) false 2 = (1176 * m ^ 2 + 2112 * m + 1128) * 2 ^ m ∧
    dp (m + 3) true 2 = (336 * m + 312) * 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [show m + 1 + 3 = (m + 3) + 1 by omega, dp, h0, h1, h2, h3, h4]; ring)

private lemma mistakes_succ (n : ℕ) (hn : 1 ≤ n) (A : Fin (n + 1) → Fin 2 → Fin 4) :
    mistakes (n + 1) A = mistakes n (fun r => A r.castSucc) +
      stepErr (A ⟨n - 1, by omega⟩ 0) (A ⟨n - 1, by omega⟩ 1) (A (Fin.last n) 0) (A (Fin.last n) 1) := by
  unfold mistakes stepErr
  have h1 : (∑ r : Fin (n + 1), if A r 0 = A r 1 then 1 else 0) =
      (∑ r : Fin n, if A r.castSucc 0 = A r.castSucc 1 then 1 else 0) +
      (if A (Fin.last n) 0 = A (Fin.last n) 1 then 1 else 0) := Fin.sum_univ_castSucc _
  have h2 : (∑ r : Fin (n + 1 - 1),
      ((if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0))) =
      (∑ r : Fin (n - 1),
        ((if A (⟨r.1, by omega⟩ : Fin n).castSucc 0 = A (⟨r.1 + 1, by omega⟩ : Fin n).castSucc 0 then 1 else 0) +
    (if A (⟨r.1, by omega⟩ : Fin n).castSucc 1 = A (⟨r.1 + 1, by omega⟩ : Fin n).castSucc 1 then 1 else 0) +
    (if A (⟨r.1, by omega⟩ : Fin n).castSucc 0 = A (⟨r.1 + 1, by omega⟩ : Fin n).castSucc 1 then 1 else 0) +
    (if A (⟨r.1, by omega⟩ : Fin n).castSucc 1 = A (⟨r.1 + 1, by omega⟩ : Fin n).castSucc 0 then 1 else 0))) +
      ((if A ⟨n - 1, by omega⟩ 0 = A (Fin.last n) 0 then 1 else 0) +
       (if A ⟨n - 1, by omega⟩ 1 = A (Fin.last n) 1 then 1 else 0) + (if A ⟨n - 1, by omega⟩ 0 = A (Fin.last n) 1 then 1 else 0) + (if A ⟨n - 1, by omega⟩ 1 = A (Fin.last n) 0 then 1 else 0)) := by
    have heq_n : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [show (∑ r : Fin (n + 1 - 1), ((if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0))) =
        ∑ r : Fin ((n - 1) + 1),
          ((if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0)) by
      refine Fintype.sum_equiv (finCongr heq_n) _ _ fun r => rfl]
    rw [Fin.sum_univ_castSucc]
    congr 1
    have e1 : (⟨(Fin.last (n - 1)).1, by omega⟩ : Fin (n + 1)) = ⟨n - 1, by omega⟩ := Fin.ext (by simp [Fin.last])
    have e2 : (⟨(Fin.last (n - 1)).1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
    simp only [e1, e2]
  dsimp only; rw [h1, h2]; omega

private lemma step_card (p0 p1 : Fin 4) (eq : Bool) (de : ℕ) (hde : de ≤ 2) :
    Fintype.card {c : Fin 2 → Fin 4 // (decide (c 0 = c 1)) = eq ∧ stepErr p0 p1 (c 0) (c 1) = de} =
    if p0 = p1 then
      (if eq = false ∧ de = 2 then 6 else if eq = true ∧ de = 1 then 3 else if eq = false ∧ de = 0 then 6 else 0)
    else
      (if eq = false ∧ de = 2 then 2 else if eq = false ∧ de = 1 then 8 else if eq = true ∧ de = 1 then 2 else if eq = false ∧ de = 0 then 2 else 0) := by
  have : ∀ (p0 p1 : Fin 4) (eq : Bool) (de : Fin 3),
      Fintype.card {c : Fin 2 → Fin 4 // (decide (c 0 = c 1)) = eq ∧ stepErr p0 p1 (c 0) (c 1) = de.1} =
      if p0 = p1 then
        (if eq = false ∧ de.1 = 2 then 6 else if eq = true ∧ de.1 = 1 then 3 else if eq = false ∧ de.1 = 0 then 6 else 0)
      else
        (if eq = false ∧ de.1 = 2 then 2 else if eq = false ∧ de.1 = 1 then 8 else if eq = true ∧ de.1 = 1 then 2 else if eq = false ∧ de.1 = 0 then 2 else 0) := by
    decide
  exact this p0 p1 eq ⟨de, by omega⟩

private lemma card_total_eq_dp (n : ℕ) (hn : 1 ≤ n) :
    ∀ (eq : Bool) (err : ℕ), err ≤ 2 →
      Fintype.card {A : Fin n → Fin 2 → Fin 4 // mistakes n A = err ∧ decide (A ⟨n - 1, by omega⟩ 0 = A ⟨n - 1, by omega⟩ 1) = eq} =
      dp n eq err := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      intro eq err herr
      let e : {A : Fin 1 → Fin 2 → Fin 4 // mistakes 1 A = err ∧ decide (A ⟨1 - 1, by omega⟩ 0 = A ⟨1 - 1, by omega⟩ 1) = eq} ≃
          {p : Fin 4 × Fin 4 // (if p.1 = p.2 then 1 else 0) = err ∧ decide (p.1 = p.2) = eq} :=
        ⟨fun ⟨A, h1, h2⟩ => ⟨(A 0 0, A 0 1), by unfold mistakes at h1; rw [Fin.sum_univ_one, Fin.sum_univ_zero, add_zero] at h1; exact h1, h2⟩,
         fun ⟨p, h1, h2⟩ => ⟨fun _ c => if c.1 = 0 then p.1 else p.2, by unfold mistakes; rw [Fin.sum_univ_one, Fin.sum_univ_zero, add_zero]; exact h1, h2⟩,
         fun ⟨A, _, _⟩ => Subtype.ext (by funext r c; fin_cases r; fin_cases c <;> rfl),
         fun ⟨⟨_, _⟩, _, _⟩ => Subtype.ext rfl⟩
      rw [Fintype.card_congr e]
      have : ∀ (eq : Bool) (err : Fin 3),
          Fintype.card {p : Fin 4 × Fin 4 // (if p.1 = p.2 then 1 else 0) = err.1 ∧ decide (p.1 = p.2) = eq} =
          dp 1 eq err.1 := by decide
      exact this eq ⟨err, by omega⟩
    | succ k =>
      intro eq err herr
      let n := k + 1
      have hn' : 1 ≤ n := by omega
      -- Decompose A : Fin (n+1) into (A0 : Fin n, c : Fin 2)
      let φ : (Σ peq : Bool, Σ perr : Fin (err + 1),
          Σ A0 : {A : Fin n → Fin 2 → Fin 4 // mistakes n A = perr.1 ∧ decide (A ⟨n - 1, by omega⟩ 0 = A ⟨n - 1, by omega⟩ 1) = peq},
          {c : Fin 2 → Fin 4 // decide (c 0 = c 1) = eq ∧ stepErr (A0.1 ⟨n - 1, by omega⟩ 0) (A0.1 ⟨n - 1, by omega⟩ 1) (c 0) (c 1) = err - perr.1}) →
          {A : Fin (n + 1) → Fin 2 → Fin 4 // mistakes (n + 1) A = err ∧ decide (A ⟨n + 1 - 1, by omega⟩ 0 = A ⟨n + 1 - 1, by omega⟩ 1) = eq} :=
        fun ⟨_, perr, ⟨A0, hA0m, _⟩, ⟨c, hceq, hstep⟩⟩ =>
          ⟨Fin.snoc A0 c, by
            have hcast : (fun r : Fin n => (Fin.snoc A0 c : Fin (n + 1) → Fin 2 → Fin 4) r.castSucc) = A0 := by
              funext r; exact Fin.snoc_castSucc _ _ r
            have hlast : (Fin.snoc A0 c : Fin (n + 1) → Fin 2 → Fin 4) (Fin.last n) = c := Fin.snoc_last _ _
            have hp : (Fin.snoc A0 c : Fin (n + 1) → Fin 2 → Fin 4) ⟨n - 1, by omega⟩ = A0 ⟨n - 1, by omega⟩ := by
              have : (⟨n - 1, by omega⟩ : Fin (n + 1)) = (⟨n - 1, by omega⟩ : Fin n).castSucc := rfl
              rw [this]; exact congrFun hcast ⟨n - 1, by omega⟩
            have hl2 : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [Fin.last])
            constructor
            · rw [mistakes_succ n hn', hcast, hlast, hp, hA0m, hstep]; omega
            · rw [hl2, hlast]; exact hceq⟩
      have hbij : Function.Bijective φ := by
        constructor
        · rintro ⟨peqa, perra, ⟨A0a, hma, hpa⟩, ⟨ca, _, _⟩⟩ ⟨peqb, perrb, ⟨A0b, hmb, hpb⟩, ⟨cb, _, _⟩⟩ heq
          have hfun : (Fin.snoc A0a ca : Fin (n + 1) → Fin 2 → Fin 4) = Fin.snoc A0b cb := congrArg Subtype.val heq
          have hA0 : A0a = A0b := by funext i; simpa using congrFun hfun i.castSucc
          have hc : ca = cb := by simpa using congrFun hfun (Fin.last n)
          subst hA0; subst hc
          have hpeq : peqa = peqb := hpa.symm.trans hpb
          have hperr : perra = perrb := Fin.ext (hma.symm.trans hmb)
          subst hpeq; subst hperr; rfl
        · rintro ⟨A, hAm, hAeq⟩
          let A0 : Fin n → Fin 2 → Fin 4 := fun r => A r.castSucc
          let c : Fin 2 → Fin 4 := A (Fin.last n)
          have hms : mistakes (n + 1) A = mistakes n A0 + stepErr (A0 ⟨n - 1, by omega⟩ 0) (A0 ⟨n - 1, by omega⟩ 1) (c 0) (c 1) :=
            mistakes_succ n hn' A
          have hperr_le : mistakes n A0 < err + 1 := by omega
          let perr : Fin (err + 1) := ⟨mistakes n A0, hperr_le⟩
          let peq : Bool := decide (A0 ⟨n - 1, by omega⟩ 0 = A0 ⟨n - 1, by omega⟩ 1)
          have hl2 : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [Fin.last])
          have hceq : decide (c 0 = c 1) = eq := by rwa [hl2] at hAeq
          have hstep : stepErr (A0 ⟨n - 1, by omega⟩ 0) (A0 ⟨n - 1, by omega⟩ 1) (c 0) (c 1) = err - perr.1 := by
            dsimp [perr]; omega
          refine ⟨⟨peq, perr, ⟨A0, rfl, rfl⟩, ⟨c, hceq, hstep⟩⟩, ?_⟩
          apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
          · dsimp [φ, c]; rw [Fin.snoc_last]
          · intro j; dsimp [φ, A0]; rw [Fin.snoc_castSucc]
      rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
      have hinner : ∀ peq : Bool,
          Fintype.card (Σ perr : Fin (err + 1),
            Σ A0 : {A : Fin n → Fin 2 → Fin 4 // mistakes n A = perr.1 ∧ decide (A ⟨n - 1, by omega⟩ 0 = A ⟨n - 1, by omega⟩ 1) = peq},
            {c : Fin 2 → Fin 4 // decide (c 0 = c 1) = eq ∧ stepErr (A0.1 ⟨n - 1, by omega⟩ 0) (A0.1 ⟨n - 1, by omega⟩ 1) (c 0) (c 1) = err - perr.1}) =
          ∑ perr : Fin (err + 1), dp n peq perr.1 *
            (if peq = true then
              (if eq = false ∧ err - perr.1 = 2 then 6 else if eq = true ∧ err - perr.1 = 1 then 3 else if eq = false ∧ err - perr.1 = 0 then 6 else 0)
            else
              (if eq = false ∧ err - perr.1 = 2 then 2 else if eq = false ∧ err - perr.1 = 1 then 8 else if eq = true ∧ err - perr.1 = 1 then 2 else if eq = false ∧ err - perr.1 = 0 then 2 else 0)) := by
        intro peq
        rw [Fintype.card_sigma]
        apply Finset.sum_congr rfl; intro perr _
        rw [Fintype.card_sigma]
        have hconst : ∀ A0 : {A : Fin n → Fin 2 → Fin 4 // mistakes n A = perr.1 ∧ decide (A ⟨n - 1, by omega⟩ 0 = A ⟨n - 1, by omega⟩ 1) = peq},
            Fintype.card {c : Fin 2 → Fin 4 // decide (c 0 = c 1) = eq ∧ stepErr (A0.1 ⟨n - 1, by omega⟩ 0) (A0.1 ⟨n - 1, by omega⟩ 1) (c 0) (c 1) = err - perr.1} =
            if peq = true then
              (if eq = false ∧ err - perr.1 = 2 then 6 else if eq = true ∧ err - perr.1 = 1 then 3 else if eq = false ∧ err - perr.1 = 0 then 6 else 0)
            else
              (if eq = false ∧ err - perr.1 = 2 then 2 else if eq = false ∧ err - perr.1 = 1 then 8 else if eq = true ∧ err - perr.1 = 1 then 2 else if eq = false ∧ err - perr.1 = 0 then 2 else 0) := by
          intro A0
          rw [step_card _ _ eq (err - perr.1) (by omega)]
          have hpeq := A0.2.2
          cases peq with
          | true =>
            have he : A0.1 ⟨n - 1, by omega⟩ 0 = A0.1 ⟨n - 1, by omega⟩ 1 := of_decide_eq_true hpeq
            simp [he]
          | false =>
            have hne : A0.1 ⟨n - 1, by omega⟩ 0 ≠ A0.1 ⟨n - 1, by omega⟩ 1 := of_decide_eq_false hpeq
            simp [hne]
        simp_rw [hconst, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        rw [ih hn' peq perr.1 (by omega)]
      simp_rw [hinner]
      have hsum_bool : ∀ f : Bool → ℕ, (∑ b : Bool, f b) = f false + f true := fun f => by rw [Fintype.sum_bool, add_comm]
      rw [hsum_bool]
      rcases eq with _ | _ <;> (rcases (by omega : err = 0 ∨ err = 1 ∨ err = 2) with rfl | rfl | rfl <;>
        (simp [Fin.sum_univ_succ, dp, dp_true_zero, n]; try ring))

private lemma mistakes_mono_prefix (n : ℕ) (hn : 3 ≤ n) (A : Fin n → Fin 2 → Fin 4) :
    mistakes 3 (fun r => A ⟨r.1, by omega⟩) ≤ mistakes n A := by
  unfold mistakes
  have h1 : (∑ r : Fin 3, if A ⟨r.1, by omega⟩ 0 = A ⟨r.1, by omega⟩ 1 then 1 else 0) ≤
      ∑ r : Fin n, if A r 0 = A r 1 then 1 else 0 := by
    have hsub : (Finset.univ.image (fun r : Fin 3 => (⟨r.1, by omega⟩ : Fin n))) ⊆ Finset.univ := Finset.subset_univ _
    calc (∑ r : Fin 3, if A ⟨r.1, by omega⟩ 0 = A ⟨r.1, by omega⟩ 1 then 1 else 0)
        = ∑ x ∈ Finset.univ.image (fun r : Fin 3 => (⟨r.1, by omega⟩ : Fin n)), if A x 0 = A x 1 then 1 else 0 := by
          rw [Finset.sum_image]; intro a _ b _ h; exact Fin.ext (by simpa [Fin.ext_iff] using h)
      _ ≤ ∑ x ∈ Finset.univ, if A x 0 = A x 1 then 1 else 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have h2 : (∑ r : Fin (3 - 1),
      ((if A ⟨(⟨r.1, by omega⟩ : Fin 3).1, by omega⟩ 0 = A ⟨(⟨r.1 + 1, by omega⟩ : Fin 3).1, by omega⟩ 0 then 1 else 0) +
    (if A ⟨(⟨r.1, by omega⟩ : Fin 3).1, by omega⟩ 1 = A ⟨(⟨r.1 + 1, by omega⟩ : Fin 3).1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨(⟨r.1, by omega⟩ : Fin 3).1, by omega⟩ 0 = A ⟨(⟨r.1 + 1, by omega⟩ : Fin 3).1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨(⟨r.1, by omega⟩ : Fin 3).1, by omega⟩ 1 = A ⟨(⟨r.1 + 1, by omega⟩ : Fin 3).1, by omega⟩ 0 then 1 else 0))) ≤
      ∑ r : Fin (n - 1),
        ((if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0)) := by
    have hsub : (Finset.univ.image (fun r : Fin (3 - 1) => (⟨r.1, by omega⟩ : Fin (n - 1)))) ⊆ Finset.univ := Finset.subset_univ _
    calc _ = ∑ x ∈ Finset.univ.image (fun r : Fin (3 - 1) => (⟨r.1, by omega⟩ : Fin (n - 1))),
            ((if A ⟨x.1, by omega⟩ 0 = A ⟨x.1 + 1, by omega⟩ 0 then 1 else 0) +
    (if A ⟨x.1, by omega⟩ 1 = A ⟨x.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨x.1, by omega⟩ 0 = A ⟨x.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨x.1, by omega⟩ 1 = A ⟨x.1 + 1, by omega⟩ 0 then 1 else 0)) := by
          rw [Finset.sum_image]; intro a _ b _ h; exact Fin.ext (by simpa [Fin.ext_iff] using h)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  dsimp only at h2 ⊢; omega

private lemma no_small_coloring :
    ∀ f : Fin 3 → Fin 2 → Fin 2,
      2 < (∑ r : Fin 3, if f r 0 = f r 1 then 1 else 0) +
        (∑ r : Fin (3 - 1),
          ((if f ⟨r.1, by omega⟩ 0 = f ⟨r.1 + 1, by omega⟩ 0 then 1 else 0) +
    (if f ⟨r.1, by omega⟩ 1 = f ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if f ⟨r.1, by omega⟩ 0 = f ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if f ⟨r.1, by omega⟩ 1 = f ⟨r.1 + 1, by omega⟩ 0 then 1 else 0))) := by decide

private lemma uses_ge_Km1 (n : ℕ) (hn : 3 ≤ n) (A : Fin n → Fin 2 → Fin 4) (hm : mistakes n A = 2) :
    3 ≤ (Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2)).card := by
  by_contra hlt
  have hcard : (Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2)).card ≤ 2 := by omega
  let S := Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2)
  have hle : Fintype.card S ≤ 2 := by rw [Fintype.card_coe]; exact hcard
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let f : Fin 3 → Fin 2 → Fin 2 := fun r c =>
    ⟨(e ⟨A ⟨r.1, by omega⟩ c, Finset.mem_image.mpr ⟨(⟨r.1, by omega⟩, c), Finset.mem_univ _, rfl⟩⟩).1, by
      have := (e ⟨A ⟨r.1, by omega⟩ c, Finset.mem_image.mpr ⟨(⟨r.1, by omega⟩, c), Finset.mem_univ _, rfl⟩⟩).2; omega⟩
  have hfeq : ∀ r1 r2 : Fin 3, ∀ c1 c2 : Fin 2,
      (f r1 c1 = f r2 c2) ↔ (A ⟨r1.1, by omega⟩ c1 = A ⟨r2.1, by omega⟩ c2) := by
    intro r1 r2 c1 c2
    constructor
    · intro h
      have hv := congrArg Fin.val h
      have he : e ⟨A ⟨r1.1, by omega⟩ c1, _⟩ = e ⟨A ⟨r2.1, by omega⟩ c2, _⟩ := Fin.ext hv
      exact congrArg Subtype.val (e.injective he)
    · intro h; apply Fin.ext; dsimp [f]; congr 2; exact Subtype.ext h
  have hmf : (∑ r : Fin 3, if f r 0 = f r 1 then 1 else 0) +
      (∑ r : Fin (3 - 1), ((if f ⟨r.1, by omega⟩ 0 = f ⟨r.1 + 1, by omega⟩ 0 then 1 else 0) +
    (if f ⟨r.1, by omega⟩ 1 = f ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if f ⟨r.1, by omega⟩ 0 = f ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if f ⟨r.1, by omega⟩ 1 = f ⟨r.1 + 1, by omega⟩ 0 then 1 else 0))) =
      mistakes 3 (fun r => A ⟨r.1, by omega⟩) := by
    unfold mistakes
    simp only [hfeq]
  have h1 := no_small_coloring f
  have h2 := mistakes_mono_prefix n hn A
  omega

private lemma mistakes_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin 4)) (A : Fin n → Fin 2 → Fin 4) :
    mistakes n (fun r c => σ (A r c)) = mistakes n A := by
  unfold mistakes
  simp only [Equiv.apply_eq_iff_eq]

private lemma rowMajor_unique_perm (n : ℕ) (A B : Fin n → Fin 2 → Fin 4)
    (hA : isRowMajor n A) (hB : isRowMajor n B)
    (hcard : 3 ≤ (Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2)).card)
    (σ : Equiv.Perm (Fin 4)) (hσ : (fun r c => σ (A r c)) = B) :
    σ = Equiv.refl _ := by
  -- Prove by strong induction on v : ℕ that if v ∈ image A then σ v = v
  have hfix : ∀ v : Fin 4, v ∈ Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2) → σ v = v := by
    intro v hv
    induction hv_val : v.1 using Nat.strong_induction_on generalizing v with
    | _ k ih =>
      -- Let i0 be minimal index in Fin (2*n) with A i0 = v
      have hex : ∃ i : Fin (2 * n), A ⟨i.1 / 2, by omega⟩ ⟨i.1 % 2, by omega⟩ = v := by
        obtain ⟨⟨r, c⟩, _, hrc⟩ := Finset.mem_image.mp hv
        refine ⟨⟨2 * r.1 + c.1, by have := r.2; have := c.2; omega⟩, ?_⟩
        have e1 : (⟨(2 * r.1 + c.1) / 2, by have := r.2; have := c.2; omega⟩ : Fin n) = r := Fin.ext (by dsimp; have := c.2; omega)
        have e2 : (⟨(2 * r.1 + c.1) % 2, by have := r.2; have := c.2; omega⟩ : Fin 2) = c := Fin.ext (by dsimp; have := c.2; omega)
        rw [e1, e2]; exact hrc
      classical
      let i0 := Nat.find (show ∃ idx : ℕ, ∃ h : idx < 2 * n, A ⟨idx / 2, by omega⟩ ⟨idx % 2, by omega⟩ = v by
        obtain ⟨i, hi⟩ := hex; exact ⟨i.1, i.2, hi⟩)
      have hi0_spec := Nat.find_spec (show ∃ idx : ℕ, ∃ h : idx < 2 * n, A ⟨idx / 2, by omega⟩ ⟨idx % 2, by omega⟩ = v by
        obtain ⟨i, hi⟩ := hex; exact ⟨i.1, i.2, hi⟩)
      obtain ⟨hi0_lt, hi0_eq⟩ := hi0_spec
      have hi0_min : ∀ j : Fin (2 * n), j.1 < i0 → A ⟨j.1 / 2, by omega⟩ ⟨j.1 % 2, by omega⟩ ≠ v := by
        intro j hj heq
        exact Nat.find_min _ hj ⟨j.2, heq⟩
      have hBi0 : B ⟨i0 / 2, by omega⟩ ⟨i0 % 2, by omega⟩ = σ v := by
        rw [← hσ]; dsimp only; rw [hi0_eq]
      -- Every w < k appears before i0 in A, so σ w = w by ih, hence w != σ v, so (σ v).1 >= k
      have hge : k ≤ (σ v).1 := by
        by_contra hlt
        have hlt' : (σ v).1 < k := by omega
        obtain ⟨j, hj_lt, hj_eq⟩ := hA ⟨i0, hi0_lt⟩ (σ v).1 (by rw [hi0_eq, hv_val]; exact hlt')
        have hmem_sv : (σ v) ∈ Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2) := by
          refine Finset.mem_image.mpr ⟨(⟨j.1 / 2, by omega⟩, ⟨j.1 % 2, by omega⟩), Finset.mem_univ _, Fin.ext hj_eq⟩
        have hfix_sv : σ (σ v) = σ v := ih (σ v).1 hlt' (σ v) hmem_sv rfl
        have hveq : σ v = v := σ.injective hfix_sv
        omega
      -- Every w < (σ v).1 appears before i0 in B; if k < (σ v).1 then k appears before i0 in B, so σ⁻¹ k appears before i0 in A
      have hle : (σ v).1 ≤ k := by
        by_contra hgt
        have hlt' : k < (σ v).1 := by omega
        obtain ⟨j, hj_lt, hj_eq⟩ := hB ⟨i0, hi0_lt⟩ k (by rw [hBi0]; exact hlt')
        have hB_j : B ⟨j.1 / 2, by omega⟩ ⟨j.1 % 2, by omega⟩ = v := Fin.ext (hj_eq.trans hv_val.symm)
        have hA_j : σ (A ⟨j.1 / 2, by omega⟩ ⟨j.1 % 2, by omega⟩) = v := by
          have := congrFun (congrFun hσ ⟨j.1 / 2, by omega⟩) ⟨j.1 % 2, by omega⟩; exact this.trans hB_j
        -- Let u = A j. Since j < i0, u != v.
        have hu_ne : A ⟨j.1 / 2, by omega⟩ ⟨j.1 % 2, by omega⟩ ≠ v := hi0_min j hj_lt
        -- If u.1 < k then σ u = u by ih, so u = v, contradiction!
        -- If u.1 > k then k appears before j in A (by hA), contradicting hi0_min!
        have hu_gt : k < (A ⟨j.1 / 2, by omega⟩ ⟨j.1 % 2, by omega⟩).1 := by
          by_contra hule
          have hult : (A ⟨j.1 / 2, by omega⟩ ⟨j.1 % 2, by omega⟩).1 < k := by
            have : (A ⟨j.1 / 2, by omega⟩ ⟨j.1 % 2, by omega⟩).1 ≠ k := fun h => hu_ne (Fin.ext (h.trans hv_val.symm))
            omega
          have hmem_u : A ⟨j.1 / 2, by omega⟩ ⟨j.1 % 2, by omega⟩ ∈ Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2) :=
            Finset.mem_image.mpr ⟨(⟨j.1 / 2, by omega⟩, ⟨j.1 % 2, by omega⟩), Finset.mem_univ _, rfl⟩
          have hfix_u := ih _ hult _ hmem_u rfl
          exact hu_ne (hfix_u.symm.trans hA_j)
        obtain ⟨j', hj'_lt, hj'_eq⟩ := hA j k hu_gt
        exact hi0_min j' (lt_trans hj'_lt hj_lt) (Fin.ext (hj'_eq.trans hv_val.symm))
      exact Fin.ext (by omega)
  -- σ fixes at least K - 1 elements of Fin K, hence fixes all elements of Fin K!
  ext x
  by_cases hx : x ∈ Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2)
  · exact congrArg Fin.val (hfix x hx)
  · -- x is the unique element not in S; σ maps S onto S, so σ x ∉ S, hence σ x = x
    have hnot : σ x ∉ Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2) := by
      intro hmem
      have := hfix (σ x) hmem
      have := σ.injective this
      exact hx (this ▸ hmem)
    let S := Finset.univ.image (fun p : Fin n × Fin 2 => A p.1 p.2)
    have hcomp : (Finset.univ \ S).card ≤ 1 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]; dsimp [S]; omega
    have hx_mem : x ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
    have hsx_mem : σ x ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
    have heq : σ x = x := Finset.card_le_one.mp hcomp _ hsx_mem _ hx_mem
    exact congrArg Fin.val heq

private lemma exists_perm_rowMajor (n : ℕ) (A : Fin n → Fin 2 → Fin 4) :
    ∃ σ : Equiv.Perm (Fin 4), isRowMajor n (fun r c => σ (A r c)) := by
  classical
  let exP (c : Fin 4) : Prop := ∃ idx : ℕ, ∃ _ : idx < 2 * n, A ⟨idx / 2, by omega⟩ ⟨idx % 2, by omega⟩ = c
  let firstIdx (c : Fin 4) : ℕ := if h : exP c then Nat.find h else 2 * n + c.1
  have hinj : Function.Injective firstIdx := by
    intro a b hab
    dsimp [firstIdx] at hab
    by_cases ha : exP a
    · by_cases hb : exP b
      · rw [dif_pos ha, dif_pos hb] at hab
        have ha_s := Nat.find_spec ha
        have hb_s := Nat.find_spec hb
        have h1 : (⟨Nat.find ha / 2, by have := ha_s.1; omega⟩ : Fin n) = ⟨Nat.find hb / 2, by have := hb_s.1; omega⟩ := Fin.ext (by dsimp; omega)
        have h2 : (⟨Nat.find ha % 2, by have := ha_s.1; omega⟩ : Fin 2) = ⟨Nat.find hb % 2, by have := hb_s.1; omega⟩ := Fin.ext (by dsimp; omega)
        exact ha_s.2.symm.trans (by rw [h1, h2]; exact hb_s.2)
      · rw [dif_pos ha, dif_neg hb] at hab; have := (Nat.find_spec ha).1; omega
    · by_cases hb : exP b
      · rw [dif_neg ha, dif_pos hb] at hab; have := (Nat.find_spec hb).1; omega
      · rw [dif_neg ha, dif_neg hb] at hab; exact Fin.ext (by omega)
  let σ_fn (c : Fin 4) : Fin 4 :=
    ⟨(Finset.univ.filter (fun d : Fin 4 => firstIdx d < firstIdx c)).card, by
      have hlt : (Finset.univ.filter (fun d : Fin 4 => firstIdx d < firstIdx c)) ⊂ Finset.univ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.subset_univ _, fun heq => ?_⟩
        have : c ∈ Finset.univ.filter (fun d : Fin 4 => firstIdx d < firstIdx c) := heq.symm ▸ Finset.mem_univ c
        simp at this
      have := Finset.card_lt_card hlt
      simpa using this⟩
  have hσ_mono : ∀ a b : Fin 4, firstIdx a < firstIdx b → (σ_fn a).1 < (σ_fn b).1 := by
    intro a b hab
    dsimp [σ_fn]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun d hd => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢; omega, fun heq => ?_⟩
    have : a ∈ Finset.univ.filter (fun d : Fin 4 => firstIdx d < firstIdx b) := by simp [hab]
    rw [← heq] at this; simp at this
  have hσ_inj : Function.Injective σ_fn := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (hinj h)) with hlt | hgt
    · exact absurd (congrArg Fin.val hab) (ne_of_lt (hσ_mono a b hlt))
    · exact absurd (congrArg Fin.val hab) (ne_of_gt (hσ_mono b a hgt))
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective σ_fn ((Finite.injective_iff_bijective).mp hσ_inj)
  refine ⟨σ, fun i v hv => ?_⟩
  let c := A ⟨i.1 / 2, by omega⟩ ⟨i.1 % 2, by omega⟩
  change v < (σ c).1 at hv
  have hv_lt : v < 4 := lt_trans hv (σ c).2
  let d := σ.symm ⟨v, hv_lt⟩
  have hdv : (σ d).1 = v := by simp [d]
  have hfd_lt : firstIdx d < firstIdx c := by
    by_contra hge
    rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
    · have : d = c := hinj heq.symm
      rw [this] at hdv; omega
    · have := hσ_mono c d hgt
      change (σ c).1 < (σ d).1 at this
      omega
  have hc_ex : exP c := ⟨i.1, i.2, rfl⟩
  have hc_le : firstIdx c ≤ i.1 := by
    dsimp [firstIdx]; rw [dif_pos hc_ex]; exact Nat.find_min' hc_ex ⟨i.2, rfl⟩
  have hd_lt_2n : firstIdx d < 2 * n := by omega
  have hd_ex : exP d := by
    by_contra hno
    dsimp [firstIdx] at hd_lt_2n; rw [dif_neg hno] at hd_lt_2n; omega
  have hd_s := Nat.find_spec hd_ex
  have hd_eq : firstIdx d = Nat.find hd_ex := by dsimp [firstIdx]; rw [dif_pos hd_ex]
  refine ⟨⟨firstIdx d, hd_lt_2n⟩, by dsimp; omega, ?_⟩
  dsimp only
  have h1 : (⟨firstIdx d / 2, by omega⟩ : Fin n) = ⟨Nat.find hd_ex / 2, by have := hd_s.1; omega⟩ := Fin.ext (by dsimp; omega)
  have h2 : (⟨firstIdx d % 2, by omega⟩ : Fin 2) = ⟨Nat.find hd_ex % 2, by have := hd_s.1; omega⟩ := Fin.ext (by dsimp; omega)
  rw [h1, h2, hd_s.2]; exact hdv

private lemma a_eq_total (n : ℕ) (hn : 3 ≤ n) :
    24 * a n = dp n false 2 + dp n true 2 := by
  unfold a; rw [if_neg (by omega)]
  have htot : Fintype.card {A : Fin n → Fin 2 → Fin 4 // mistakes n A = 2} =
      dp n false 2 + dp n true 2 := by
    rw [← card_total_eq_dp n (by omega) false 2 (le_refl _),
        ← card_total_eq_dp n (by omega) true 2 (le_refl _)]
    let φ : {A : Fin n → Fin 2 → Fin 4 // mistakes n A = 2 ∧ decide (A ⟨n - 1, by omega⟩ 0 = A ⟨n - 1, by omega⟩ 1) = false} ⊕
            {A : Fin n → Fin 2 → Fin 4 // mistakes n A = 2 ∧ decide (A ⟨n - 1, by omega⟩ 0 = A ⟨n - 1, by omega⟩ 1) = true} →
            {A : Fin n → Fin 2 → Fin 4 // mistakes n A = 2} :=
      fun x => match x with | Sum.inl ⟨A, h, _⟩ => ⟨A, h⟩ | Sum.inr ⟨A, h, _⟩ => ⟨A, h⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro (⟨Aa, _, hfa⟩ | ⟨Aa, _, hta⟩) (⟨Ab, _, hfb⟩ | ⟨Ab, _, htb⟩) heq
        · dsimp [φ] at heq; have hA : Aa = Ab := congrArg Subtype.val heq; subst hA; rfl
        · dsimp [φ] at heq; have hA : Aa = Ab := congrArg Subtype.val heq; subst hA; rw [hfa] at htb; cases htb
        · dsimp [φ] at heq; have hA : Aa = Ab := congrArg Subtype.val heq; subst hA; rw [hta] at hfb; cases hfb
        · dsimp [φ] at heq; have hA : Aa = Ab := congrArg Subtype.val heq; subst hA; rfl
      · rintro ⟨A, hA⟩
        cases h : decide (A ⟨n - 1, by omega⟩ 0 = A ⟨n - 1, by omega⟩ 1)
        · exact ⟨Sum.inl ⟨A, hA, h⟩, rfl⟩
        · exact ⟨Sum.inr ⟨A, hA, h⟩, rfl⟩
    rw [← Fintype.card_sum, Fintype.card_congr (Equiv.ofBijective φ hbij)]
  rw [← htot]
  let ψ : Equiv.Perm (Fin 4) × {A : Fin n → Fin 2 → Fin 4 // mistakes n A = 2 ∧ isRowMajor n A} →
      {A : Fin n → Fin 2 → Fin 4 // mistakes n A = 2} :=
    fun ⟨σ, ⟨A, hAm, _⟩⟩ => ⟨fun r c => σ (A r c), by rw [mistakes_comp_perm]; exact hAm⟩
  have hbij : Function.Bijective ψ := by
    constructor
    · rintro ⟨σa, ⟨Aa, hAma, hAra⟩⟩ ⟨σb, ⟨Ab, _, hArb⟩⟩ heq
      have hfun : (fun r c => σa (Aa r c)) = fun r c => σb (Ab r c) := congrArg Subtype.val heq
      have hcomp : (fun r c => (σb.symm * σa) (Aa r c)) = Ab := by
        funext r c; simp only [Equiv.Perm.mul_apply]; exact congrArg σb.symm (congrFun (congrFun hfun r) c) |>.trans (σb.symm_apply_apply _)
      have hid := rowMajor_unique_perm n Aa Ab hAra hArb (uses_ge_Km1 n hn Aa hAma) (σb.symm * σa) hcomp
      have hσeq : σa = σb := by
        ext x
        have := Equiv.congr_fun hid x
        simp only [Equiv.Perm.mul_apply, Equiv.refl_apply] at this
        exact congrArg Fin.val ((σb.symm_apply_eq).mp this)
      subst hσeq
      have hAeq : Aa = Ab := by
        funext r c; exact σa.injective (congrFun (congrFun hfun r) c)
      subst hAeq; rfl
    · rintro ⟨A, hAm⟩
      obtain ⟨τ, hτ⟩ := exists_perm_rowMajor n A
      let B : Fin n → Fin 2 → Fin 4 := fun r c => τ (A r c)
      have hBm : mistakes n B = 2 := by rw [mistakes_comp_perm]; exact hAm
      refine ⟨⟨τ.symm, ⟨B, hBm, hτ⟩⟩, ?_⟩
      apply Subtype.ext; funext r c; dsimp [ψ, B]; exact τ.symm_apply_apply _
  rw [← Fintype.card_congr (Equiv.ofBijective ψ hbij), Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  rfl

private lemma a_closed_m (m : ℕ) : a (m + 3) = (49 * m ^ 2 + 102 * m + 60) * 2 ^ m := by
  have htot := a_eq_total (m + 3) (by omega)
  obtain ⟨h0, h1, h2, h3, h4⟩ := dp_closed m
  rw [h3, h4] at htot
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 24) (by rw [htot]; ring)

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_val_1 : a 1 = 0 := by
  unfold a; rw [if_neg (by omega)]
  let dec : Fin 4 × Fin 4 → Fin 1 → Fin 2 → Fin 4 := fun p _ c => if c.1 = 0 then p.1 else p.2
  let e : {A : Fin 1 → Fin 2 → Fin 4 // mistakes 1 A = 2 ∧ isRowMajor 1 A} ≃
      {p : Fin 4 × Fin 4 // mistakes 1 (dec p) = 2 ∧ isRowMajor 1 (dec p)} :=
    ⟨fun ⟨A, hA⟩ => ⟨(A 0 0, A 0 1), by
      have heq : dec (A 0 0, A 0 1) = A := by funext r c; fin_cases r; fin_cases c <;> rfl
      rwa [heq]⟩,
     fun ⟨p, hp⟩ => ⟨dec p, hp⟩,
     fun ⟨A, _⟩ => Subtype.ext (by funext r c; fin_cases r; fin_cases c <;> rfl),
     fun ⟨⟨_, _⟩, _⟩ => Subtype.ext rfl⟩
  rw [Fintype.card_congr e]; decide
private lemma a_val_2 : a 2 = 3 := by
  unfold a; rw [if_neg (by omega)]
  let dec : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Fin 2 → Fin 2 → Fin 4 :=
    fun p q r c => if r.1 = 0 then (if c.1 = 0 then p.1 else p.2) else (if c.1 = 0 then q.1 else q.2)
  let e : {A : Fin 2 → Fin 2 → Fin 4 // mistakes 2 A = 2 ∧ isRowMajor 2 A} ≃
      (Σ p : Fin 4 × Fin 4, {q : Fin 4 × Fin 4 // mistakes 2 (dec p q) = 2 ∧ isRowMajor 2 (dec p q)}) :=
    ⟨fun ⟨A, hA⟩ => ⟨(A 0 0, A 0 1), ⟨(A 1 0, A 1 1), by
      have heq : dec (A 0 0, A 0 1) (A 1 0, A 1 1) = A := by funext r c; fin_cases r <;> fin_cases c <;> rfl
      rwa [heq]⟩⟩,
     fun ⟨p, ⟨q, hq⟩⟩ => ⟨dec p q, hq⟩,
     fun ⟨A, _⟩ => Subtype.ext (by funext r c; fin_cases r <;> fin_cases c <;> rfl),
     fun ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ => rfl⟩
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have hrow : ∀ p : Fin 4 × Fin 4,
      Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec p q) = 2 ∧ isRowMajor 2 (dec p q)} =
      if p.1.1 = 0 ∧ p.2.1 ≤ 1 then
        Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec p q) = 2 ∧ isRowMajor 2 (dec p q)}
      else 0 := by
    intro p; split_ifs with hp
    · rfl
    · rw [Fintype.card_eq_zero_iff]; refine ⟨fun ⟨q, _, hrm⟩ => hp ⟨?_, ?_⟩⟩
      · by_contra h0; obtain ⟨j, hj, _⟩ := hrm ⟨0, by omega⟩ 0 (by dsimp [dec]; omega); dsimp at hj; omega
      · by_contra h1; obtain ⟨j, hj, hjv⟩ := hrm ⟨1, by omega⟩ 1 (by dsimp [dec]; omega)
        dsimp at hj
        have h00 : (dec p q 0 0).1 = 0 := by
          by_contra h0; obtain ⟨j', hj', _⟩ := hrm ⟨0, by omega⟩ 0 (by dsimp [dec] at h0 ⊢; omega); dsimp at hj'; omega
        have hj0 : j = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hj0] at hjv; dsimp [dec] at hjv h00; omega
  have hsum : (∑ p : Fin 4 × Fin 4, Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec p q) = 2 ∧ isRowMajor 2 (dec p q)}) =
      Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec (0, 0) q) = 2 ∧ isRowMajor 2 (dec (0, 0) q)} +
      Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec (0, 1) q) = 2 ∧ isRowMajor 2 (dec (0, 1) q)} := by
    rw [Fintype.sum_prod_type]
    have h0 : ∀ a : Fin 4, a ≠ 0 → (∑ b : Fin 4, Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec (a, b) q) = 2 ∧ isRowMajor 2 (dec (a, b) q)}) = 0 := by
      intro a ha; apply Finset.sum_eq_zero; intro b _
      rw [hrow (a, b), if_neg (fun h => ha (Fin.ext h.1))]
    rw [Fin.sum_univ_succ]
    have hrest : (∑ i : Fin 3, ∑ b : Fin 4, Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec (i.succ, b) q) = 2 ∧ isRowMajor 2 (dec (i.succ, b) q)}) = 0 :=
      Finset.sum_eq_zero fun i _ => h0 i.succ (Fin.succ_ne_zero i)
    rw [hrest, add_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hrest2 : (∑ i : Fin 2, Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec (0, i.succ.succ) q) = 2 ∧ isRowMajor 2 (dec (0, i.succ.succ) q)}) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hrow (0, i.succ.succ), if_neg (by simp)]
    rw [hrest2, add_zero]; rfl
  rw [hsum]
  have c0 : Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec (0, 0) q) = 2 ∧ isRowMajor 2 (dec (0, 0) q)} =
      1 := by decide
  have c1 : Fintype.card {q : Fin 4 × Fin 4 // mistakes 2 (dec (0, 1) q) = 2 ∧ isRowMajor 2 (dec (0, 1) q)} =
      2 := by decide
  rw [c0, c1]
private lemma a_val_3 : a 3 = 60 := by
  have h1 := a_eq_total 3 (by omega)
  have hdp : dp 3 false 2 + dp 3 true 2 = 1440 := by decide
  omega
private lemma a_val_4 : a 4 = 422 := by
  have h1 := a_eq_total 4 (by omega)
  have hdp : dp 4 false 2 + dp 4 true 2 = 10128 := by decide
  omega
private lemma a_val_5 : a 5 = 1840 := by
  have h1 := a_eq_total 5 (by omega)
  have hdp : dp 5 false 2 + dp 5 true 2 = 44160 := by decide
  omega

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ j * f) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, ih m]
      split_ifs with h1 h2
      · simp [Nat.succ_sub_succ]
      · omega
      · omega
      · rfl

private lemma coeff_mul_X_pow_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ j) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  rw [mul_comm]; exact coeff_X_pow_mul_eq f j n

theorem solution : type_of% @OMA.S_oeis_a229749.main := by
  have hclosed : ∀ n : ℕ, 2 < n → (a n : ℤ) = 2 ^ (n - 3) * (195 - 192 * (n : ℤ) + 49 * (n : ℤ) ^ 2) := by
    intro n hn
    have h := a_closed_m (n - 3)
    rw [show n - 3 + 3 = n by omega] at h
    have hq : (a n : ℤ) = (49 * ((n - 3 : ℕ) : ℤ) ^ 2 + 102 * ((n - 3 : ℕ) : ℤ) + 60) * 2 ^ (n - 3) := by exact_mod_cast h
    have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
    rw [hq, hn3]; ring
  refine ⟨?_, hclosed⟩
  ext n
  have hexp : (1 - 2 * (PowerSeries.X : PowerSeries ℚ)) ^ 3 = 1 - PowerSeries.C 6 * PowerSeries.X ^ 1 + PowerSeries.C 12 * PowerSeries.X ^ 2 - PowerSeries.C 8 * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X ^ 2 * (3 + 42 * PowerSeries.X + 98 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3) : PowerSeries ℚ) = PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.C 42 * PowerSeries.X ^ 3 + PowerSeries.C 98 * PowerSeries.X ^ 4 + PowerSeries.C 4 * PowerSeries.X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hR]
  have hc : ∀ (c : ℚ) (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ j)) =
      c * if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro c j
    rw [mul_comm (PowerSeries.C c), ← mul_assoc, mul_comm _ (PowerSeries.C c),
        PowerSeries.coeff_C_mul, coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, hc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]; try norm_num
  · simp [a_zero, a_val_1, a_val_2]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; try norm_num
  · simp [a_val_1, a_val_2, a_val_3, a_val_4]; try norm_num
  · simp [a_val_2, a_val_3, a_val_4, a_val_5]; try norm_num
  · simp only [Nat.add_assoc, Nat.reduceAdd, show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, ↓reduceIte,
      show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show ¬(m + 6 = 2) by omega, show ¬(m + 6 = 3) by omega, show ¬(m + 6 = 4) by omega, show ¬(m + 6 = 5) by omega]
    have ha0 : (a (m + 6) : ℚ) = ((49 * (m + 3) ^ 2 + 102 * (m + 3) + 60) * 2 ^ (m + 3)) := by have h := a_closed_m (m + 3); rw [show m + 3 + 3 = m + 6 by omega] at h; exact_mod_cast h
    have ha1 : (a (m + 5) : ℚ) = ((49 * (m + 2) ^ 2 + 102 * (m + 2) + 60) * 2 ^ (m + 2)) := by have h := a_closed_m (m + 2); rw [show m + 2 + 3 = m + 5 by omega] at h; exact_mod_cast h
    have ha2 : (a (m + 4) : ℚ) = ((49 * (m + 1) ^ 2 + 102 * (m + 1) + 60) * 2 ^ (m + 1)) := by have h := a_closed_m (m + 1); rw [show m + 1 + 3 = m + 4 by omega] at h; exact_mod_cast h
    have ha3 : (a (m + 3) : ℚ) = ((49 * (m + 0) ^ 2 + 102 * (m + 0) + 60) * 2 ^ (m + 0)) := by have h := a_closed_m (m + 0); rw [show m + 0 + 3 = m + 3 by omega] at h; exact_mod_cast h
    rw [ha0, ha1, ha2, ha3]
    ring

end OMA.P_oeis_a229749

theorem OMA.solution : type_of% @OMA.S_oeis_a229749.main :=
  OMA.P_oeis_a229749.solution
