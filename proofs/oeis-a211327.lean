import OMAStatements.S_oeis_a211327

namespace OMA.P_oeis_a211327

open OMA.S_oeis_a211327

private def sgn (k : ℕ) : ℤ := if Even k then 1 else -1

private lemma sgn_succ (k : ℕ) : sgn (k + 1) = -sgn k := by
  unfold sgn
  by_cases h : Even k
  · have h' : ¬Even (k + 1) := by rcases h with ⟨r, rfl⟩; intro ⟨s, hs⟩; omega
    simp [h, h']
  · have h' : Even (k + 1) := by
      rcases Nat.even_or_odd k with he | ⟨r, rfl⟩
      · exact absurd he h
      · exact ⟨r + 1, by omega⟩
    simp [h, h']

private lemma sgn_add (i j : ℕ) : sgn (i + j) = sgn i * sgn j := by
  induction i with
  | zero => unfold sgn; simp
  | succ i ih =>
    rw [show i + 1 + j = (i + j) + 1 by omega, sgn_succ, sgn_succ, ih]; ring

private lemma sgn_sq (k : ℕ) : sgn k * sgn k = 1 := by
  unfold sgn; split_ifs <;> norm_num

private lemma sgn_mul_self (k : ℕ) (x : ℤ) : sgn k * (sgn k * x) = x := by
  rw [← mul_assoc, sgn_sq, one_mul]

private def diagOk (n : ℕ) (h : Fin (n + 1) → ℤ) : Prop :=
  (∀ i : Fin (n + 1), -3 ≤ h i ∧ h i ≤ 3) ∧
  (∀ i j : Fin (n + 1), Even (h i + h j)) ∧
  (∀ i j : Fin n, ({h i.castSucc + h j.castSucc, -(h i.castSucc + h j.succ),
                    -(h i.succ + h j.castSucc), h i.succ + h j.succ} : Finset ℤ).card ≠ 2)

private def matOfDiag {n : ℕ} (h : Fin (n + 1) → ℤ) (i j : Fin (n + 1)) : ℤ :=
  sgn (i.1 + j.1) * ((h i + h j) / 2)

private lemma card_scale_eq (c : ℤ) (hc : c ≠ 0) (a b d e : ℤ) :
    ({c * a, c * b, c * d, c * e} : Finset ℤ).card = ({a, b, d, e} : Finset ℤ).card := by
  have himg : ({c * a, c * b, c * d, c * e} : Finset ℤ) = ({a, b, d, e} : Finset ℤ).image (fun x => c * x) := by
    ext x; simp
  rw [himg, Finset.card_image_of_injective _ (mul_right_injective₀ hc)]

private lemma matOfDiag_valid {n : ℕ} {h : Fin (n + 1) → ℤ} (hh : diagOk n h) :
    isValid n (matOfDiag h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; unfold matOfDiag sgn
    have hi := hh.1 i; have hj := hh.1 j
    split_ifs <;> omega
  · intro i j; unfold matOfDiag; rw [add_comm i.1 j.1, add_comm (h i) (h j)]
  · intro i j; unfold valid2x2 matOfDiag
    have h00 := hh.2.1 i.castSucc j.castSucc
    have h01 := hh.2.1 i.castSucc j.succ
    have h10 := hh.2.1 i.succ j.castSucc
    have h11 := hh.2.1 i.succ j.succ
    have e00 : 2 * ((h i.castSucc + h j.castSucc) / 2) = h i.castSucc + h j.castSucc := by
      rcases h00 with ⟨k, hk⟩; omega
    have e01 : 2 * ((h i.castSucc + h j.succ) / 2) = h i.castSucc + h j.succ := by
      rcases h01 with ⟨k, hk⟩; omega
    have e10 : 2 * ((h i.succ + h j.castSucc) / 2) = h i.succ + h j.castSucc := by
      rcases h10 with ⟨k, hk⟩; omega
    have e11 : 2 * ((h i.succ + h j.succ) / 2) = h i.succ + h j.succ := by
      rcases h11 with ⟨k, hk⟩; omega
    have s01 : sgn (i.castSucc.1 + j.succ.1) = -sgn (i.castSucc.1 + j.castSucc.1) := by
      have : i.castSucc.1 + j.succ.1 = (i.castSucc.1 + j.castSucc.1) + 1 := by simp [Fin.val_castSucc, Fin.val_succ]; omega
      rw [this, sgn_succ]
    have s10 : sgn (i.succ.1 + j.castSucc.1) = -sgn (i.castSucc.1 + j.castSucc.1) := by
      have : i.succ.1 + j.castSucc.1 = (i.castSucc.1 + j.castSucc.1) + 1 := by simp [Fin.val_castSucc, Fin.val_succ]; omega
      rw [this, sgn_succ]
    have s11 : sgn (i.succ.1 + j.succ.1) = sgn (i.castSucc.1 + j.castSucc.1) := by
      have : i.succ.1 + j.succ.1 = ((i.castSucc.1 + j.castSucc.1) + 1) + 1 := by simp [Fin.val_castSucc, Fin.val_succ]; omega
      rw [this, sgn_succ, sgn_succ, neg_neg]
    rw [s01, s10, s11]
    set s := sgn (i.castSucc.1 + j.castSucc.1)
    have hs : s ≠ 0 := by unfold s sgn; split_ifs <;> decide
    constructor
    · have h2 : 2 * (s * ((h i.castSucc + h j.castSucc) / 2) + -s * ((h i.castSucc + h j.succ) / 2) +
          -s * ((h i.succ + h j.castSucc) / 2) + s * ((h i.succ + h j.succ) / 2)) = 0 := by
        linear_combination s * e00 - s * e01 - s * e10 + s * e11
      omega
    · have hsc := card_scale_eq (2 * s) (mul_ne_zero (by decide) hs)
        (s * ((h i.castSucc + h j.castSucc) / 2))
        (-s * ((h i.castSucc + h j.succ) / 2))
        (-s * ((h i.succ + h j.castSucc) / 2))
        (s * ((h i.succ + h j.succ) / 2))
      rw [← hsc]
      have hss : s * s = 1 := sgn_sq _
      have t1 : 2 * s * (s * ((h i.castSucc + h j.castSucc) / 2)) = h i.castSucc + h j.castSucc := by
        calc 2 * s * (s * ((h i.castSucc + h j.castSucc) / 2))
            = (s * s) * (2 * ((h i.castSucc + h j.castSucc) / 2)) := by ring
          _ = h i.castSucc + h j.castSucc := by rw [hss, one_mul, e00]
      have t2 : 2 * s * (-s * ((h i.castSucc + h j.succ) / 2)) = -(h i.castSucc + h j.succ) := by
        calc 2 * s * (-s * ((h i.castSucc + h j.succ) / 2))
            = -(s * s) * (2 * ((h i.castSucc + h j.succ) / 2)) := by ring
          _ = -(h i.castSucc + h j.succ) := by rw [hss, e01]; ring
      have t3 : 2 * s * (-s * ((h i.succ + h j.castSucc) / 2)) = -(h i.succ + h j.castSucc) := by
        calc 2 * s * (-s * ((h i.succ + h j.castSucc) / 2))
            = -(s * s) * (2 * ((h i.succ + h j.castSucc) / 2)) := by ring
          _ = -(h i.succ + h j.castSucc) := by rw [hss, e10]; ring
      have t4 : 2 * s * (s * ((h i.succ + h j.succ) / 2)) = h i.succ + h j.succ := by
        calc 2 * s * (s * ((h i.succ + h j.succ) / 2))
            = (s * s) * (2 * ((h i.succ + h j.succ) / 2)) := by ring
          _ = h i.succ + h j.succ := by rw [hss, one_mul, e11]
      rw [t1, t2, t3, t4]
      exact hh.2.2 i j

private lemma valid_eq_matOfDiag {n : ℕ} {M : Fin (n + 1) → Fin (n + 1) → ℤ} (hM : isValid n M) :
    M = matOfDiag (fun i => M i i) ∧ diagOk n (fun i => M i i) := by
  let B : Fin (n + 1) → Fin (n + 1) → ℤ := fun i j => sgn (i.1 + j.1) * M i j
  have hB_add : ∀ i j : Fin n, B i.castSucc j.castSucc + B i.succ j.succ = B i.castSucc j.succ + B i.succ j.castSucc := by
    intro i j
    have hsum := (hM.2.2 i j).1
    change sgn (i.castSucc.1 + j.castSucc.1) * M i.castSucc j.castSucc +
           sgn (i.succ.1 + j.succ.1) * M i.succ j.succ =
           sgn (i.castSucc.1 + j.succ.1) * M i.castSucc j.succ +
           sgn (i.succ.1 + j.castSucc.1) * M i.succ j.castSucc
    have s01 : sgn (i.castSucc.1 + j.succ.1) = -sgn (i.castSucc.1 + j.castSucc.1) := by
      have : i.castSucc.1 + j.succ.1 = (i.castSucc.1 + j.castSucc.1) + 1 := by simp [Fin.val_castSucc, Fin.val_succ]; omega
      rw [this, sgn_succ]
    have s10 : sgn (i.succ.1 + j.castSucc.1) = -sgn (i.castSucc.1 + j.castSucc.1) := by
      have : i.succ.1 + j.castSucc.1 = (i.castSucc.1 + j.castSucc.1) + 1 := by simp [Fin.val_castSucc, Fin.val_succ]; omega
      rw [this, sgn_succ]
    have s11 : sgn (i.succ.1 + j.succ.1) = sgn (i.castSucc.1 + j.castSucc.1) := by
      have : i.succ.1 + j.succ.1 = ((i.castSucc.1 + j.castSucc.1) + 1) + 1 := by simp [Fin.val_castSucc, Fin.val_succ]; omega
      rw [this, sgn_succ, sgn_succ, neg_neg]
    rw [s01, s10, s11]
    linear_combination sgn (i.castSucc.1 + j.castSucc.1) * hsum
  have hB_eq : ∀ i j : Fin (n + 1), B i j = B i 0 + B 0 j - B 0 0 := by
    intro i j
    obtain ⟨iv, hiv⟩ := i; obtain ⟨jv, hjv⟩ := j
    induction iv generalizing jv with
    | zero =>
      have : (⟨0, hiv⟩ : Fin (n + 1)) = 0 := rfl
      rw [this]; ring
    | succ iv ihi =>
      induction jv with
      | zero =>
        have : (⟨0, hjv⟩ : Fin (n + 1)) = 0 := rfl
        rw [this]; ring
      | succ jv ihj =>
        have hstep := hB_add ⟨iv, by omega⟩ ⟨jv, by omega⟩
        have h1 := ihi (by omega) (jv + 1) hjv
        have h2 := ihi (by omega) jv (by omega)
        have h3 := ihj (by omega)
        have e00 : (⟨iv, by omega⟩ : Fin n).castSucc = ⟨iv, by omega⟩ := rfl
        have e01 : (⟨jv, by omega⟩ : Fin n).succ = ⟨jv + 1, hjv⟩ := rfl
        have e10 : (⟨iv, by omega⟩ : Fin n).succ = ⟨iv + 1, hiv⟩ := rfl
        have e11 : (⟨jv, by omega⟩ : Fin n).castSucc = ⟨jv, by omega⟩ := rfl
        rw [e00, e01, e10, e11] at hstep
        linarith
  have hB_sym : ∀ i j : Fin (n + 1), B i j = B j i := by
    intro i j; dsimp [B]; rw [add_comm i.1 j.1, hM.2.1 i j]
  have hB_diag : ∀ i : Fin (n + 1), B i i = M i i := by
    intro i; dsimp [B]
    have he : Even (i.1 + i.1) := ⟨i.1, rfl⟩
    unfold sgn; simp [he]
  have h2B : ∀ i j : Fin (n + 1), 2 * B i j = M i i + M j j := by
    intro i j
    have hij := hB_eq i j
    have hii := hB_eq i i
    have hjj := hB_eq j j
    have hs1 := hB_sym i 0
    have hs2 := hB_sym j 0
    rw [hB_diag i] at hii; rw [hB_diag j] at hjj
    linarith
  have heven : ∀ i j : Fin (n + 1), Even (M i i + M j j) := fun i j => ⟨B i j, by linarith [h2B i j]⟩
  have hMeq : M = matOfDiag (fun i => M i i) := by
    funext i j; unfold matOfDiag
    have hbij : (M i i + M j j) / 2 = B i j := by have := h2B i j; omega
    rw [hbij]; dsimp [B]; exact (sgn_mul_self (i.1 + j.1) (M i j)).symm
  refine ⟨hMeq, fun i => hM.1 i i, heven, ?_⟩
  intro i j
  have hcard := (hM.2.2 i j).2
  set s := sgn (i.castSucc.1 + j.castSucc.1)
  have hs : s ≠ 0 := by unfold s sgn; split_ifs <;> decide
  have hsc := card_scale_eq (2 * s) (mul_ne_zero (by decide) hs)
    (M i.castSucc j.castSucc) (M i.castSucc j.succ) (M i.succ j.castSucc) (M i.succ j.succ)
  rw [← hsc] at hcard
  have s01 : sgn (i.castSucc.1 + j.succ.1) = -s := by
    have : i.castSucc.1 + j.succ.1 = (i.castSucc.1 + j.castSucc.1) + 1 := by simp [Fin.val_castSucc, Fin.val_succ]; omega
    rw [this, sgn_succ]
  have s10 : sgn (i.succ.1 + j.castSucc.1) = -s := by
    have : i.succ.1 + j.castSucc.1 = (i.castSucc.1 + j.castSucc.1) + 1 := by simp [Fin.val_castSucc, Fin.val_succ]; omega
    rw [this, sgn_succ]
  have s11 : sgn (i.succ.1 + j.succ.1) = s := by
    have : i.succ.1 + j.succ.1 = ((i.castSucc.1 + j.castSucc.1) + 1) + 1 := by simp [Fin.val_castSucc, Fin.val_succ]; omega
    rw [this, sgn_succ, sgn_succ, neg_neg]
  have t1 : 2 * s * M i.castSucc j.castSucc = M i.castSucc i.castSucc + M j.castSucc j.castSucc := by
    have h := h2B i.castSucc j.castSucc
    change 2 * (s * M i.castSucc j.castSucc) = _ at h; linarith
  have t2 : 2 * s * M i.castSucc j.succ = -(M i.castSucc i.castSucc + M j.succ j.succ) := by
    have h := h2B i.castSucc j.succ
    change 2 * (sgn (i.castSucc.1 + j.succ.1) * M i.castSucc j.succ) = _ at h; rw [s01] at h; linarith
  have t3 : 2 * s * M i.succ j.castSucc = -(M i.succ i.succ + M j.castSucc j.castSucc) := by
    have h := h2B i.succ j.castSucc
    change 2 * (sgn (i.succ.1 + j.castSucc.1) * M i.succ j.castSucc) = _ at h; rw [s10] at h; linarith
  have t4 : 2 * s * M i.succ j.succ = M i.succ i.succ + M j.succ j.succ := by
    have h := h2B i.succ j.succ
    change 2 * (sgn (i.succ.1 + j.succ.1) * M i.succ j.succ) = _ at h; rw [s11] at h; linarith
  rw [t1, t2, t3, t4] at hcard
  exact hcard

private def oddValOf (x : Fin 4) : ℤ := match x.1 with | 0 => -3 | 1 => -1 | 2 => 1 | _ => 3

private def evenValOf (x : Fin 3) : ℤ := match x.1 with | 0 => -2 | 1 => 0 | _ => 2

private lemma odd_diag_ok_iff (a b : Fin 4) :
    ({oddValOf a + oddValOf a, -(oddValOf a + oddValOf b),
      -(oddValOf b + oddValOf a), oddValOf b + oddValOf b} : Finset ℤ).card ≠ 2 ↔
    a.1 % 2 ≠ b.1 % 2 := by
  revert a b; decide

private lemma odd_pair_ok (a b c d : Fin 4) (h1 : a.1 % 2 ≠ b.1 % 2) (h2 : c.1 % 2 ≠ d.1 % 2) :
    ({oddValOf a + oddValOf c, -(oddValOf a + oddValOf d),
      -(oddValOf b + oddValOf c), oddValOf b + oddValOf d} : Finset ℤ).card ≠ 2 := by
  revert a b c d h1 h2; decide

private lemma even_diag_ok_iff (a b : Fin 3) :
    ({evenValOf a + evenValOf a, -(evenValOf a + evenValOf b),
      -(evenValOf b + evenValOf a), evenValOf b + evenValOf b} : Finset ℤ).card ≠ 2 ↔
    (¬(a = 0 ∧ b = 0) ∧ ¬(a = 2 ∧ b = 2)) := by
  revert a b; decide

private lemma even_cross_bad (a b c d : Fin 3)
    (h1 : a = 1 ∧ b = 1) (h2 : (c = 0 ∧ d = 2) ∨ (c = 2 ∧ d = 0)) :
    ({evenValOf a + evenValOf c, -(evenValOf a + evenValOf d),
      -(evenValOf b + evenValOf c), evenValOf b + evenValOf d} : Finset ℤ).card = 2 := by
  revert a b c d h1 h2; decide

private lemma even_pair_ok (a b c d : Fin 3)
    (h : ¬((a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = 2) ∨ (c = 0 ∧ d = 0) ∨ (c = 2 ∧ d = 2) ∨
      ((a = 1 ∧ b = 1) ∧ ((c = 0 ∧ d = 2) ∨ (c = 2 ∧ d = 0))) ∨
      ((c = 1 ∧ d = 1) ∧ ((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0))))) :
    ({evenValOf a + evenValOf c, -(evenValOf a + evenValOf d),
      -(evenValOf b + evenValOf c), evenValOf b + evenValOf d} : Finset ℤ).card ≠ 2 := by
  revert a b c d h; decide

private abbrev OddWords (n : ℕ) :=
  {w : Fin (n + 1) → Fin 4 // ∀ i : Fin n, (w i.castSucc).1 % 2 ≠ (w i.succ).1 % 2}

private lemma card_OddWords (n : ℕ) : Fintype.card (OddWords n) = 4 * 2 ^ n := by
  induction n with
  | zero =>
    have e : OddWords 0 ≃ Fin 4 :=
      { toFun := fun ⟨w, _⟩ => w 0
        invFun := fun a => ⟨fun _ => a, fun i => i.elim0⟩
        left_inv := fun ⟨w, _⟩ => by apply Subtype.ext; funext i; fin_cases i; rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_fin]; norm_num
  | succ n ih =>
    let φ : OddWords n × Fin 2 → OddWords (n + 1) := fun ⟨⟨w, hw⟩, b⟩ =>
      let last : Fin 4 := ⟨2 * b.1 + (1 - (w (Fin.last n)).1 % 2), by omega⟩
      ⟨Fin.snoc w last, by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · have e1 : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
          rw [e1, Fin.snoc_last, Fin.snoc_castSucc]
          dsimp [last]; have := (w (Fin.last n)).2; omega
        · intro j
          have e2 : (j.castSucc.succ : Fin (n + 2)) = j.succ.castSucc := rfl
          rw [e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hw j⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨⟨wa, _⟩, ba⟩ ⟨⟨wb, _⟩, bb⟩ heq
        have hfun := congrArg Subtype.val heq
        have hw_eq : wa = wb := by funext i; simpa [φ] using congrFun hfun i.castSucc
        subst hw_eq
        have hlast := congrFun hfun (Fin.last (n + 1))
        simp only [φ, Fin.snoc_last, Fin.ext_iff] at hlast
        have hb_eq : ba = bb := Fin.ext (by omega)
        subst hb_eq; rfl
      · rintro ⟨w, hw⟩
        let w' : OddWords n := ⟨fun i => w i.castSucc, fun j => hw j.castSucc⟩
        let b : Fin 2 := ⟨(w (Fin.last (n + 1))).1 / 2, by have := (w (Fin.last (n + 1))).2; omega⟩
        refine ⟨⟨w', b⟩, ?_⟩
        apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
        · dsimp [φ, w', b]; rw [Fin.snoc_last]
          have hne := hw (Fin.last n)
          have h1 : (w (Fin.last n).castSucc).1 % 2 ≠ (w (Fin.last (n + 1))).1 % 2 := hne
          apply Fin.ext; dsimp; omega
        · intro j; dsimp [φ, w']; rw [Fin.snoc_castSucc]
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_prod, ih, Fintype.card_fin]
    ring

private abbrev EvenWords (n : ℕ) :=
  {w : Fin (n + 1) → Fin 3 //
    (∀ i : Fin n, ¬(w i.castSucc = 0 ∧ w i.succ = 0) ∧ ¬(w i.castSucc = 2 ∧ w i.succ = 2)) ∧
    ((∀ i : Fin n, ¬(w i.castSucc = 1 ∧ w i.succ = 1)) ∨
     (∀ i : Fin n, ¬(w i.castSucc = 0 ∧ w i.succ = 2) ∧ ¬(w i.castSucc = 2 ∧ w i.succ = 0)))}

private abbrev WordsA (n : ℕ) :=
  {w : Fin (n + 1) → Fin 3 // ∀ i : Fin n, w i.castSucc ≠ w i.succ}

private abbrev WordsB (n : ℕ) :=
  {w : Fin (n + 1) → Fin 3 // ∀ i : Fin n, w i.castSucc = 1 ∨ w i.succ = 1}

private abbrev WordsAB (n : ℕ) :=
  {w : Fin (n + 1) → Fin 3 // ∀ i : Fin n, (w i.castSucc = 1 ∧ w i.succ ≠ 1) ∨ (w i.castSucc ≠ 1 ∧ w i.succ = 1)}

private lemma card_WordsA (n : ℕ) : Fintype.card (WordsA n) = 3 * 2 ^ n := by
  induction n with
  | zero =>
    have e : WordsA 0 ≃ Fin 3 :=
      { toFun := fun ⟨w, _⟩ => w 0
        invFun := fun a => ⟨fun _ => a, fun i => i.elim0⟩
        left_inv := fun ⟨w, _⟩ => by apply Subtype.ext; funext i; fin_cases i; rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_fin]; norm_num
  | succ n ih =>
    let nextVal (x : Fin 3) (b : Fin 2) : Fin 3 :=
      ⟨(x.1 + b.1 + 1) % 3, Nat.mod_lt _ (by omega)⟩
    let φ : WordsA n × Fin 2 → WordsA (n + 1) := fun ⟨⟨w, hw⟩, b⟩ =>
      ⟨Fin.snoc w (nextVal (w (Fin.last n)) b), by
        intro i; refine Fin.lastCases ?_ ?_ i
        · have e1 : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
          rw [e1, Fin.snoc_last, Fin.snoc_castSucc]
          simp only [nextVal, ne_eq, Fin.ext_iff]
          have := (w (Fin.last n)).2; have := b.2; omega
        · intro j
          have e2 : (j.castSucc.succ : Fin (n + 2)) = j.succ.castSucc := rfl
          rw [e2, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hw j⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨⟨wa, _⟩, ba⟩ ⟨⟨wb, _⟩, bb⟩ heq
        have hfun := congrArg Subtype.val heq
        have hw_eq : wa = wb := by funext i; simpa [φ] using congrFun hfun i.castSucc
        subst hw_eq
        have hlast := congrFun hfun (Fin.last (n + 1))
        simp only [φ, Fin.snoc_last, nextVal, Fin.ext_iff] at hlast
        have := (wa (Fin.last n)).2; have := ba.2; have := bb.2
        have hb_eq : ba = bb := Fin.ext (by omega)
        subst hb_eq; rfl
      · rintro ⟨w, hw⟩
        let w' : WordsA n := ⟨fun i => w i.castSucc, fun j => hw j.castSucc⟩
        let x := w (Fin.last n).castSucc
        let y := w (Fin.last (n + 1))
        have hxy : x.1 ≠ y.1 := fun h => hw (Fin.last n) (Fin.ext h)
        let b : Fin 2 := ⟨(y.1 + 3 - x.1 - 1) % 3, by have := x.2; have := y.2; omega⟩
        refine ⟨⟨w', b⟩, ?_⟩
        apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
        · dsimp [φ, w', b, nextVal]; rw [Fin.snoc_last]
          apply Fin.ext; dsimp [x, y]; have := x.2; have := y.2; omega
        · intro j; dsimp [φ, w']; rw [Fin.snoc_castSucc]
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_prod, ih, Fintype.card_fin]
    ring

private def bEnd (n : ℕ) (isOne : Bool) : ℕ :=
  Fintype.card {w : WordsB n // (w.1 (Fin.last n) == 1) = isOne}

private lemma bEnd_step (n : ℕ) :
    bEnd (n + 1) true = bEnd n true + bEnd n false ∧
    bEnd (n + 1) false = 2 * bEnd n true := by
  constructor
  · unfold bEnd
    have hsplit : Fintype.card {w : WordsB (n + 1) // (w.1 (Fin.last (n + 1)) == 1) = true} =
        Fintype.card (WordsB n) := by
      let φ : WordsB n → {w : WordsB (n + 1) // (w.1 (Fin.last (n + 1)) == 1) = true} :=
        fun ⟨w, hw⟩ =>
          ⟨⟨Fin.snoc w 1, by
            intro i; refine Fin.lastCases ?_ ?_ i
            · right; simp [Fin.snoc_last]
            · intro j
              have e2 : (j.castSucc.succ : Fin (n + 2)) = j.succ.castSucc := rfl
              rw [e2, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hw j⟩, by simp [Fin.snoc_last]⟩
      have hbij : Function.Bijective φ := by
        constructor
        · rintro ⟨wa, _⟩ ⟨wb, _⟩ heq
          have hfun := congrArg (fun x => x.1.1) heq
          apply Subtype.ext; funext i; simpa [φ] using congrFun hfun i.castSucc
        · rintro ⟨⟨w, hw⟩, hlast⟩
          have hl : w (Fin.last (n + 1)) = 1 := by simpa using hlast
          refine ⟨⟨fun i => w i.castSucc, fun j => hw j.castSucc⟩, ?_⟩
          apply Subtype.ext; apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
          · dsimp [φ]; rw [Fin.snoc_last, hl]
          · intro j; dsimp [φ]; rw [Fin.snoc_castSucc]
      exact Fintype.card_congr (Equiv.ofBijective φ hbij).symm
    rw [hsplit]
    have hpart : Fintype.card (WordsB n) =
        Fintype.card {w : WordsB n // (w.1 (Fin.last n) == 1) = true} +
        Fintype.card {w : WordsB n // (w.1 (Fin.last n) == 1) = false} := by
      rw [← Fintype.card_sum]
      refine Fintype.card_congr
        { toFun := fun w => if h : (w.1 (Fin.last n) == 1) = true then Sum.inl ⟨w, h⟩ else Sum.inr ⟨w, by cases h' : (w.1 (Fin.last n) == 1) <;> simp_all⟩
          invFun := fun s => match s with | Sum.inl ⟨w, _⟩ => w | Sum.inr ⟨w, _⟩ => w
          left_inv := fun w => by dsimp; split_ifs <;> rfl
          right_inv := fun s => by
            cases s with
            | inl x => rcases x with ⟨w, hw⟩; simp [hw]
            | inr x => rcases x with ⟨w, hw⟩; simp [hw] }
    exact hpart
  · unfold bEnd
    let φ : {w : WordsB n // (w.1 (Fin.last n) == 1) = true} × Fin 2 →
        {w : WordsB (n + 1) // (w.1 (Fin.last (n + 1)) == 1) = false} :=
      fun ⟨⟨⟨w, hw⟩, hlast⟩, b⟩ =>
        let v : Fin 3 := if b.1 = 0 then 0 else 2
        ⟨⟨Fin.snoc w v, by
          intro i; refine Fin.lastCases ?_ ?_ i
          · left; rw [Fin.snoc_castSucc]; simpa using hlast
          · intro j
            have e2 : (j.castSucc.succ : Fin (n + 2)) = j.succ.castSucc := rfl
            rw [e2, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hw j⟩, by
          dsimp [v]; rw [Fin.snoc_last]; split_ifs <;> rfl⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨⟨⟨wa, hwa⟩, hla⟩, ba⟩ ⟨⟨⟨wb, hwb⟩, hlb⟩, bb⟩ heq
        have hfun := congrArg (fun x => x.1.1) heq
        have hw_eq : wa = wb := by funext i; simpa [φ] using congrFun hfun i.castSucc
        have hlast := congrFun hfun (Fin.last (n + 1))
        simp only [φ, Fin.snoc_last] at hlast
        have hb_eq : ba = bb := by
          fin_cases ba <;> fin_cases bb <;> simp_all
        subst hb_eq
        have : (⟨⟨wa, hwa⟩, hla⟩ : {w : WordsB n // (w.1 (Fin.last n) == 1) = true}) = ⟨⟨wb, hwb⟩, hlb⟩ := by
          apply Subtype.ext; apply Subtype.ext; exact hw_eq
        exact Prod.ext this rfl
      · rintro ⟨⟨w, hw⟩, hlast⟩
        have hne1 : w (Fin.last (n + 1)) ≠ 1 := by
          intro h; dsimp at hlast; rw [h] at hlast; exact absurd hlast (by decide)
        have hprev : w (Fin.last n).castSucc = 1 := by
          rcases hw (Fin.last n) with h | h
          · exact h
          · exact absurd h hne1
        let b : Fin 2 := if w (Fin.last (n + 1)) = 0 then 0 else 1
        refine ⟨⟨⟨⟨fun i => w i.castSucc, fun j => hw j.castSucc⟩, by simp [hprev]⟩, b⟩, ?_⟩
        apply Subtype.ext; apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
        · dsimp [φ, b]; rw [Fin.snoc_last]
          have h2 := (w (Fin.last (n + 1))).2
          by_cases h0 : w (Fin.last (n + 1)) = 0
          · simp [h0]
          · simp only [h0, ↓reduceIte]
            have h2eq : w (Fin.last (n + 1)) = 2 := by
              apply Fin.ext; dsimp
              have ha : (w (Fin.last (n + 1))).1 ≠ 0 := fun h => h0 (Fin.ext h)
              have hb : (w (Fin.last (n + 1))).1 ≠ 1 := fun h => hne1 (Fin.ext h)
              omega
            simp [h2eq]
        · intro j; dsimp [φ]; rw [Fin.snoc_castSucc]
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_prod, Fintype.card_fin]
    ring

private lemma card_WordsB_pair (n : ℕ) :
    3 * (bEnd n true : ℤ) = 2 ^ (n + 2) - (-1) ^ n ∧
    3 * (bEnd n false : ℤ) = 2 ^ (n + 2) + 2 * (-1) ^ n := by
  induction n with
  | zero =>
    have h1 : bEnd 0 true = 1 := by
      unfold bEnd
      refine Fintype.card_eq_one_iff.mpr ⟨⟨⟨fun _ => 1, fun i => i.elim0⟩, rfl⟩, ?_⟩
      rintro ⟨⟨w, _⟩, h⟩; apply Subtype.ext; apply Subtype.ext; funext i; fin_cases i
      simpa using h
    have h2 : bEnd 0 false = 2 := by
      unfold bEnd
      let e : {w : WordsB 0 // (w.1 (Fin.last 0) == 1) = false} ≃ Fin 2 :=
        { toFun := fun ⟨⟨w, _⟩, _⟩ => if w 0 = 0 then 0 else 1
          invFun := fun b => ⟨⟨fun _ => if b.1 = 0 then 0 else 2, fun i => i.elim0⟩, by fin_cases b <;> rfl⟩
          left_inv := fun ⟨⟨w, _⟩, h⟩ => by
            apply Subtype.ext; apply Subtype.ext; funext i; fin_cases i
            have hne : w 0 ≠ 1 := by intro he; dsimp at h; rw [he] at h; exact absurd h (by decide)
            dsimp; by_cases h0 : w 0 = 0
            · simp [h0]
            · simp only [h0, ↓reduceIte]
              apply Fin.ext; dsimp
              have := (w 0).2
              have ha : (w 0).1 ≠ 0 := fun h' => h0 (Fin.ext h')
              have hb : (w 0).1 ≠ 1 := fun h' => hne (Fin.ext h')
              omega
          right_inv := fun b => by fin_cases b <;> rfl }
      rw [Fintype.card_congr e, Fintype.card_fin]
    rw [h1, h2]; constructor <;> norm_num
  | succ n ih =>
    rcases bEnd_step n with ⟨hs1, hs2⟩
    zify at hs1 hs2
    constructor
    · rw [hs1]
      have hp1 : (2 : ℤ) ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) := by ring
      have hn1 : ((-1 : ℤ) ^ (n + 1)) = -((-1 : ℤ) ^ n) := by ring
      linarith [ih.1, ih.2]
    · rw [hs2]
      have hp1 : (2 : ℤ) ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) := by ring
      have hn1 : ((-1 : ℤ) ^ (n + 1)) = -((-1 : ℤ) ^ n) := by ring
      linarith [ih.1]

private lemma card_WordsB (n : ℕ) :
    3 * (Fintype.card (WordsB n) : ℤ) = 2 ^ (n + 3) + (-1) ^ n := by
  have hpart : Fintype.card (WordsB n) = bEnd n true + bEnd n false := by
    unfold bEnd; rw [← Fintype.card_sum]
    refine Fintype.card_congr
      { toFun := fun w => if h : (w.1 (Fin.last n) == 1) = true then Sum.inl ⟨w, h⟩ else Sum.inr ⟨w, by cases h' : (w.1 (Fin.last n) == 1) <;> simp_all⟩
        invFun := fun s => match s with | Sum.inl ⟨w, _⟩ => w | Sum.inr ⟨w, _⟩ => w
        left_inv := fun w => by dsimp; split_ifs <;> rfl
        right_inv := fun s => by
          cases s with
          | inl x => rcases x with ⟨w, hw⟩; simp [hw]
          | inr x => rcases x with ⟨w, hw⟩; simp [hw] }
  rw [hpart]; push_cast
  have h := card_WordsB_pair n
  have hp1 : (2 : ℤ) ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
  linarith [h.1, h.2]

private lemma card_WordsAB (n : ℕ) :
    Fintype.card (WordsAB n) = if Even n then 3 * 2 ^ (n / 2) else 2 ^ (n / 2 + 2) := by
  -- Split by whether w 0 = 1 or w 0 ≠ 1
  let S1 := {w : WordsAB n // w.1 0 = 1}
  let S2 := {w : WordsAB n // w.1 0 ≠ 1}
  have hpart : Fintype.card (WordsAB n) = Fintype.card S1 + Fintype.card S2 := by
    rw [← Fintype.card_sum]
    refine Fintype.card_congr
      { toFun := fun w => if h : w.1 0 = 1 then Sum.inl ⟨w, h⟩ else Sum.inr ⟨w, h⟩
        invFun := fun s => match s with | Sum.inl ⟨w, _⟩ => w | Sum.inr ⟨w, _⟩ => w
        left_inv := fun w => by dsimp; split_ifs <;> rfl
        right_inv := fun s => by
          cases s with
          | inl x => rcases x with ⟨w, hw⟩; simp [hw]
          | inr x => rcases x with ⟨w, hw⟩; simp [hw] }
  have hS1 : Fintype.card S1 = 2 ^ ((n + 1) / 2) := by
    let φ : (Fin ((n + 1) / 2) → Fin 2) → S1 := fun f =>
      ⟨⟨fun i => if h : Even i.1 then 1 else if (f ⟨i.1 / 2, by
          rcases Nat.even_or_odd i.1 with he | ⟨r, hr⟩
          · exact absurd he h
          · omega⟩).1 = 0 then 0 else 2, by
        intro i
        by_cases he : Even i.1
        · left
          have ho : ¬Even (i.1 + 1) := by rcases he with ⟨r, hr⟩; intro ⟨s, hs⟩; omega
          have he' : Even i.castSucc.1 := he
          have ho' : ¬Even i.succ.1 := ho
          dsimp only; rw [dif_pos he', dif_neg ho']
          refine ⟨rfl, ?_⟩; split_ifs <;> decide
        · right
          have he' : Even (i.1 + 1) := by
            rcases Nat.even_or_odd i.1 with h | ⟨r, hr⟩
            · exact absurd h he
            · exact ⟨r + 1, by omega⟩
          have ho' : ¬Even i.castSucc.1 := he
          have he'' : Even i.succ.1 := he'
          dsimp only; rw [dif_neg ho', dif_pos he'']
          refine ⟨?_, rfl⟩; split_ifs <;> decide⟩, by simp⟩
    have hbij : Function.Bijective φ := by
      constructor
      · intro fa fb heq
        have hfun := congrArg (fun x => x.1.1) heq
        funext k
        have hk := congrFun hfun ⟨2 * k.1 + 1, by omega⟩
        have ho : ¬Even (2 * k.1 + 1) := by intro ⟨s, hs⟩; omega
        simp only [φ, ho, ↓reduceDIte, show (2 * k.1 + 1) / 2 = k.1 by omega] at hk
        have hfa := (fa k).2; have hfb := (fb k).2
        by_cases h1 : (fa k).1 = 0 <;> by_cases h2 : (fb k).1 = 0 <;> simp only [h1, h2, ↓reduceIte] at hk
        · exact Fin.ext (by omega)
        · exact absurd hk (by decide)
        · exact absurd hk (by decide)
        · exact Fin.ext (by omega)
      · rintro ⟨⟨w, hw⟩, hw0⟩
        have hpar : ∀ i : Fin (n + 1), (Even i.1 → w i = 1) ∧ (¬Even i.1 → w i ≠ 1) := by
          intro ⟨iv, hiv⟩
          induction iv with
          | zero => exact ⟨fun _ => hw0, fun h => absurd ⟨0, rfl⟩ h⟩
          | succ iv ih =>
            have hstep := hw ⟨iv, by omega⟩
            rcases ih (by omega) with ⟨hpe, hpo⟩
            constructor
            · intro he
              have ho : ¬Even iv := by dsimp at he; rcases he with ⟨r, hr⟩; intro ⟨s, hs⟩; omega
              rcases hstep with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact absurd h1 (hpo ho)
              · exact h2
            · intro ho
              have he : Even iv := by
                dsimp at ho
                rcases Nat.even_or_odd iv with h | ⟨r, hr⟩
                · exact h
                · exact absurd ⟨r + 1, by omega⟩ ho
              rcases hstep with ⟨_, h2⟩ | ⟨h1, _⟩
              · exact h2
              · exact absurd (hpe he) h1
        let f : Fin ((n + 1) / 2) → Fin 2 := fun k => if w ⟨2 * k.1 + 1, by omega⟩ = 0 then 0 else 1
        refine ⟨f, ?_⟩
        apply Subtype.ext; apply Subtype.ext; funext i
        dsimp [φ, f]
        by_cases he : Even i.1
        · rw [dif_pos he]; exact ((hpar i).1 he).symm
        · rw [dif_neg he]
          have hieq : (⟨2 * (i.1 / 2) + 1, by
              rcases Nat.even_or_odd i.1 with h | ⟨r, hr⟩
              · exact absurd h he
              · omega⟩ : Fin (n + 1)) = i := by
            apply Fin.ext; dsimp
            rcases Nat.even_or_odd i.1 with h | ⟨r, hr⟩
            · exact absurd h he
            · omega
          simp only [hieq]
          have hne := (hpar i).2 he
          by_cases h0 : w i = 0
          · simp [h0]
          · simp only [h0, ↓reduceIte]
            apply Fin.ext; dsimp; have := (w i).2
            have ha : (w i).1 ≠ 0 := fun h => h0 (Fin.ext h)
            have hb : (w i).1 ≠ 1 := fun h => hne (Fin.ext h)
            omega
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hS2 : Fintype.card S2 = 2 ^ (n / 2 + 1) := by
    let φ : (Fin (n / 2 + 1) → Fin 2) → S2 := fun f =>
      ⟨⟨fun i => if Even i.1 then (if (f ⟨i.1 / 2, by omega⟩).1 = 0 then 0 else 2) else 1, by
        intro i
        by_cases he : Even i.1
        · right
          have ho : ¬Even (i.1 + 1) := by rcases he with ⟨r, hr⟩; intro ⟨s, hs⟩; omega
          have he' : Even i.castSucc.1 := he
          have ho' : ¬Even i.succ.1 := ho
          dsimp only; rw [if_pos he', if_neg ho']
          refine ⟨?_, rfl⟩; split_ifs <;> decide
        · left
          have he' : Even (i.1 + 1) := by
            rcases Nat.even_or_odd i.1 with h | ⟨r, hr⟩
            · exact absurd h he
            · exact ⟨r + 1, by omega⟩
          have ho' : ¬Even i.castSucc.1 := he
          have he'' : Even i.succ.1 := he'
          dsimp only; rw [if_neg ho', if_pos he'']
          refine ⟨rfl, ?_⟩; split_ifs <;> decide⟩, by
        dsimp only
        have hev : Even ((0 : Fin (n + 1)).1) := ⟨0, rfl⟩
        rw [if_pos hev]; split_ifs <;> decide⟩
    have hbij : Function.Bijective φ := by
      constructor
      · intro fa fb heq
        have hfun := congrArg (fun x => x.1.1) heq
        funext k
        have hk := congrFun hfun ⟨2 * k.1, by omega⟩
        have he : Even (2 * k.1) := ⟨k.1, by omega⟩
        simp only [φ, he, ↓reduceIte, show (2 * k.1) / 2 = k.1 by omega] at hk
        have hfa := (fa k).2; have hfb := (fb k).2
        by_cases h1 : (fa k).1 = 0 <;> by_cases h2 : (fb k).1 = 0 <;> simp only [h1, h2, ↓reduceIte] at hk
        · exact Fin.ext (by omega)
        · exact absurd hk (by decide)
        · exact absurd hk (by decide)
        · exact Fin.ext (by omega)
      · rintro ⟨⟨w, hw⟩, hw0⟩
        have hpar : ∀ i : Fin (n + 1), (Even i.1 → w i ≠ 1) ∧ (¬Even i.1 → w i = 1) := by
          intro ⟨iv, hiv⟩
          induction iv with
          | zero => exact ⟨fun _ => hw0, fun h => absurd ⟨0, rfl⟩ h⟩
          | succ iv ih =>
            have hstep := hw ⟨iv, by omega⟩
            rcases ih (by omega) with ⟨hpe, hpo⟩
            constructor
            · intro he
              have ho : ¬Even iv := by dsimp at he; rcases he with ⟨r, hr⟩; intro ⟨s, hs⟩; omega
              rcases hstep with ⟨_, h2⟩ | ⟨h1, _⟩
              · exact h2
              · exact absurd (hpo ho) h1
            · intro ho
              have he : Even iv := by
                dsimp at ho
                rcases Nat.even_or_odd iv with h | ⟨r, hr⟩
                · exact h
                · exact absurd ⟨r + 1, by omega⟩ ho
              rcases hstep with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact absurd h1 (hpe he)
              · exact h2
        let f : Fin (n / 2 + 1) → Fin 2 := fun k => if w ⟨2 * k.1, by omega⟩ = 0 then 0 else 1
        refine ⟨f, ?_⟩
        apply Subtype.ext; apply Subtype.ext; funext i
        dsimp [φ, f]
        by_cases he : Even i.1
        · rw [if_pos he]
          have hieq : (⟨2 * (i.1 / 2), by omega⟩ : Fin (n + 1)) = i := by
            apply Fin.ext; dsimp; rcases he with ⟨r, hr⟩; omega
          simp only [hieq]
          have hne := (hpar i).1 he
          by_cases h0 : w i = 0
          · simp [h0]
          · simp only [h0, ↓reduceIte]
            apply Fin.ext; dsimp; have := (w i).2
            have ha : (w i).1 ≠ 0 := fun h => h0 (Fin.ext h)
            have hb : (w i).1 ≠ 1 := fun h => hne (Fin.ext h)
            omega
        · rw [if_neg he]; exact ((hpar i).2 he).symm
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [hpart, hS1, hS2]
  by_cases he : Even n
  · rw [if_pos he]
    rcases he with ⟨k, rfl⟩
    have h1 : (k + k + 1) / 2 = k := by omega
    have h2 : (k + k) / 2 = k := by omega
    rw [h1, h2]; ring
  · rw [if_neg he]
    rcases Nat.even_or_odd n with h | ⟨k, rfl⟩
    · exact absurd h he
    · have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have h2 : (2 * k + 1) / 2 = k := by omega
      rw [h1, h2]; ring

private lemma card_EvenWords (n : ℕ) :
    3 * (Fintype.card (EvenWords n) : ℤ) =
      if Even n then 17 * 2 ^ n + 1 - 9 * 2 ^ (n / 2)
      else 17 * 2 ^ n - 1 - 3 * 2 ^ (n / 2 + 2) := by
  let SA : Finset (Fin (n + 1) → Fin 3) := Finset.univ.filter (fun w => ∀ i : Fin n, w i.castSucc ≠ w i.succ)
  let SB : Finset (Fin (n + 1) → Fin 3) := Finset.univ.filter (fun w => ∀ i : Fin n, w i.castSucc = 1 ∨ w i.succ = 1)
  have hEv : Fintype.card (EvenWords n) = (SA ∪ SB).card := by
    rw [Fintype.card_subtype]
    congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, SA, SB]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · left; intro i
        have h1i := h1 i; have h2i := h2 i
        intro heq
        have hx := (w i.castSucc).2
        have h0 : w i.castSucc ≠ 0 := fun h => h1i.1 ⟨h, heq ▸ h⟩
        have h1' : w i.castSucc ≠ 1 := fun h => h2i ⟨h, heq ▸ h⟩
        have h2' : w i.castSucc ≠ 2 := fun h => h1i.2 ⟨h, heq ▸ h⟩
        have ha : (w i.castSucc).1 ≠ 0 := fun h => h0 (Fin.ext h)
        have hb : (w i.castSucc).1 ≠ 1 := fun h => h1' (Fin.ext h)
        have hc : (w i.castSucc).1 ≠ 2 := fun h => h2' (Fin.ext h)
        omega
      · right; intro i
        have h1i := h1 i; have h2i := h2 i
        by_contra hnot; push Not at hnot
        have hx := (w i.castSucc).2; have hy := (w i.succ).2
        have hxa : (w i.castSucc).1 ≠ 1 := fun h => hnot.1 (Fin.ext h)
        have hya : (w i.succ).1 ≠ 1 := fun h => hnot.2 (Fin.ext h)
        by_cases hx0 : w i.castSucc = 0
        · by_cases hy0 : w i.succ = 0
          · exact h1i.1 ⟨hx0, hy0⟩
          · exact h2i.1 ⟨hx0, Fin.ext (by have : (w i.succ).1 ≠ 0 := fun h => hy0 (Fin.ext h); omega)⟩
        · have hx2 : w i.castSucc = 2 := Fin.ext (by have : (w i.castSucc).1 ≠ 0 := fun h => hx0 (Fin.ext h); omega)
          by_cases hy0 : w i.succ = 0
          · exact h2i.2 ⟨hx2, hy0⟩
          · exact h1i.2 ⟨hx2, Fin.ext (by have : (w i.succ).1 ≠ 0 := fun h => hy0 (Fin.ext h); omega)⟩
    · rintro (h | h)
      · refine ⟨fun i => ⟨fun ⟨ha, hb⟩ => h i (ha.trans hb.symm), fun ⟨ha, hb⟩ => h i (ha.trans hb.symm)⟩,
          Or.inl (fun i ⟨ha, hb⟩ => h i (ha.trans hb.symm))⟩
      · refine ⟨fun i => ?_, Or.inr (fun i => ?_)⟩
        · rcases h i with hi | hi <;> constructor <;> rintro ⟨ha, hb⟩ <;> simp_all
        · rcases h i with hi | hi <;> constructor <;> rintro ⟨ha, hb⟩ <;> simp_all
  have hA : SA.card = Fintype.card (WordsA n) := (Fintype.card_subtype _).symm
  have hB : SB.card = Fintype.card (WordsB n) := (Fintype.card_subtype _).symm
  have hAB : (SA ∩ SB).card = Fintype.card (WordsAB n) := by
    rw [Fintype.card_subtype]
    congr 1; ext w
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, SA, SB]
    constructor
    · rintro ⟨ha, hb⟩ i
      rcases hb i with h1 | h1
      · left; exact ⟨h1, fun h2 => ha i (h1.trans h2.symm)⟩
      · right; exact ⟨fun h2 => ha i (h2.trans h1.symm), h1⟩
    · intro h
      refine ⟨fun i heq => ?_, fun i => ?_⟩
      · rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
      · rcases h i with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Or.inl h1
        · exact Or.inr h2
  have hie := Finset.card_union_add_card_inter SA SB
  rw [← hEv, hA, hB, hAB, card_WordsA, card_WordsAB] at hie
  have hBc := card_WordsB n
  have hp8 : (2 : ℤ) ^ (n + 3) = 8 * 2 ^ n := by ring
  by_cases he : Even n
  · rw [if_pos he] at hie ⊢
    have hneg : ((-1 : ℤ) ^ n) = 1 := Even.neg_one_pow he
    rw [hneg] at hBc
    zify at hie
    linarith
  · rw [if_neg he] at hie ⊢
    have hodd : Odd n := Nat.not_even_iff_odd.mp he
    have hneg : ((-1 : ℤ) ^ n) = -1 := Odd.neg_one_pow hodd
    rw [hneg] at hBc
    zify at hie
    linarith

private lemma oddValOf_bd : ∀ x : Fin 4, -3 ≤ oddValOf x ∧ oddValOf x ≤ 3 := by decide
private lemma oddValOf_even_add : ∀ x y : Fin 4, Even (oddValOf x + oddValOf y) := by decide
private lemma evenValOf_bd : ∀ x : Fin 3, -3 ≤ evenValOf x ∧ evenValOf x ≤ 3 := by decide
private lemma evenValOf_even_add : ∀ x y : Fin 3, Even (evenValOf x + evenValOf y) := by decide
private lemma oddValOf_inj : ∀ x y : Fin 4, oddValOf x = oddValOf y → x = y := by decide
private lemma evenValOf_inj : ∀ x y : Fin 3, evenValOf x = evenValOf y → x = y := by decide
private lemma oddValOf_ne_evenValOf : ∀ x : Fin 4, ∀ y : Fin 3, oddValOf x ≠ evenValOf y := by decide

private lemma a_eq_odd_add_even (n : ℕ) (hn : 1 ≤ n) :
    a n = Fintype.card (OddWords n) + Fintype.card (EvenWords n) := by
  unfold a; rw [if_neg (by omega)]
  let φ : OddWords n ⊕ EvenWords n → {M : Fin (n + 1) → Fin (n + 1) → ℤ // isValid n M} :=
    fun s => match s with
    | Sum.inl ⟨w, hw⟩ =>
      ⟨matOfDiag (fun i => oddValOf (w i)), matOfDiag_valid ⟨
        fun i => oddValOf_bd (w i),
        fun i j => oddValOf_even_add (w i) (w j),
        fun i j => odd_pair_ok (w i.castSucc) (w i.succ) (w j.castSucc) (w j.succ) (hw i) (hw j)⟩⟩
    | Sum.inr ⟨w, hw⟩ =>
      ⟨matOfDiag (fun i => evenValOf (w i)), matOfDiag_valid ⟨
        fun i => evenValOf_bd (w i),
        fun i j => evenValOf_even_add (w i) (w j),
        fun i j => even_pair_ok (w i.castSucc) (w i.succ) (w j.castSucc) (w j.succ) (by
          have h1i := hw.1 i; have h1j := hw.1 j
          rintro (h | h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact h1i.1 h
          · exact h1i.2 h
          · exact h1j.1 h
          · exact h1j.2 h
          · rcases hw.2 with ha | hb
            · exact ha i h1
            · rcases h2 with h2 | h2
              · exact (hb j).1 h2
              · exact (hb j).2 h2
          · rcases hw.2 with ha | hb
            · exact ha j h1
            · rcases h2 with h2 | h2
              · exact (hb i).1 h2
              · exact (hb i).2 h2)⟩⟩
  have hbij : Function.Bijective φ := by
    constructor
    · intro sa sb heq
      have hfun := congrArg Subtype.val heq
      have hdiag : ∀ i : Fin (n + 1), (φ sa).1 i i = (φ sb).1 i i := fun i => congrFun (congrFun hfun i) i
      have hmat_diag : ∀ (f : Fin (n + 1) → ℤ) (i : Fin (n + 1)), matOfDiag f i i = f i := by
        intro f i; unfold matOfDiag sgn
        have he : Even (i.1 + i.1) := ⟨i.1, rfl⟩
        simp only [he, ↓reduceIte, one_mul]; omega
      cases sa with
      | inl wa =>
        cases sb with
        | inl wb =>
          congr 1; apply Subtype.ext; funext i
          have h := hdiag i; dsimp [φ] at h; rw [hmat_diag, hmat_diag] at h
          exact oddValOf_inj _ _ h
        | inr wb =>
          exfalso; have h := hdiag 0; dsimp [φ] at h; rw [hmat_diag, hmat_diag] at h
          exact oddValOf_ne_evenValOf _ _ h
      | inr wa =>
        cases sb with
        | inl wb =>
          exfalso; have h := hdiag 0; dsimp [φ] at h; rw [hmat_diag, hmat_diag] at h
          exact oddValOf_ne_evenValOf _ _ h.symm
        | inr wb =>
          congr 1; apply Subtype.ext; funext i
          have h := hdiag i; dsimp [φ] at h; rw [hmat_diag, hmat_diag] at h
          exact evenValOf_inj _ _ h
    · rintro ⟨M, hM⟩
      obtain ⟨hMeq, hdiag⟩ := valid_eq_matOfDiag hM
      let h : Fin (n + 1) → ℤ := fun i => M i i
      by_cases h0 : Even (h 0)
      · have hall_even : ∀ i : Fin (n + 1), Even (h i) := by
          intro i; have h0i := hdiag.2.1 0 i
          rcases h0 with ⟨a, ha⟩; rcases h0i with ⟨b, hb⟩; dsimp [h] at *; exact ⟨b - a, by omega⟩
        let w : Fin (n + 1) → Fin 3 := fun i => if h i = -2 then 0 else if h i = 0 then 1 else 2
        have hw_eq : ∀ i : Fin (n + 1), evenValOf (w i) = h i := by
          intro i; have hb := hdiag.1 i; rcases hall_even i with ⟨k, hk⟩
          dsimp [w, h] at *; split_ifs <;> simp [evenValOf] <;> omega
        have hw_valid : (∀ i : Fin n, ¬(w i.castSucc = 0 ∧ w i.succ = 0) ∧ ¬(w i.castSucc = 2 ∧ w i.succ = 2)) ∧
            ((∀ i : Fin n, ¬(w i.castSucc = 1 ∧ w i.succ = 1)) ∨
             (∀ i : Fin n, ¬(w i.castSucc = 0 ∧ w i.succ = 2) ∧ ¬(w i.castSucc = 2 ∧ w i.succ = 0))) := by
          constructor
          · intro i
            rw [← even_diag_ok_iff (w i.castSucc) (w i.succ)]
            rw [hw_eq, hw_eq]; exact hdiag.2.2 i i
          · by_cases hex : ∃ i : Fin n, w i.castSucc = 1 ∧ w i.succ = 1
            · right; rcases hex with ⟨i0, hi0⟩; intro j
              have hcard : ({evenValOf (w i0.castSucc) + evenValOf (w j.castSucc),
                -(evenValOf (w i0.castSucc) + evenValOf (w j.succ)),
                -(evenValOf (w i0.succ) + evenValOf (w j.castSucc)),
                evenValOf (w i0.succ) + evenValOf (w j.succ)} : Finset ℤ).card ≠ 2 := by
                rw [hw_eq, hw_eq, hw_eq, hw_eq]; exact hdiag.2.2 i0 j
              constructor
              · intro h02; exact hcard (even_cross_bad _ _ _ _ hi0 (Or.inl h02))
              · intro h20; exact hcard (even_cross_bad _ _ _ _ hi0 (Or.inr h20))
            · left; push Not at hex; intro i ⟨h1, h2⟩; exact hex i h1 h2
        refine ⟨Sum.inr ⟨w, hw_valid⟩, ?_⟩
        apply Subtype.ext; dsimp [φ]; rw [hMeq]; congr 1; funext i; exact hw_eq i
      · have hall_odd : ∀ i : Fin (n + 1), ¬Even (h i) := by
          intro i hi; have h0i := hdiag.2.1 0 i
          rcases hi with ⟨a, ha⟩; rcases h0i with ⟨b, hb⟩; dsimp [h] at *; exact h0 ⟨b - a, by omega⟩
        let w : Fin (n + 1) → Fin 4 := fun i =>
          if h i = -3 then 0 else if h i = -1 then 1 else if h i = 1 then 2 else 3
        have hw_eq : ∀ i : Fin (n + 1), oddValOf (w i) = h i := by
          intro i; have hb := hdiag.1 i; have ho := hall_odd i
          dsimp [w, h] at *
          by_cases h1 : M i i = -3
          · simp [h1, oddValOf]
          · by_cases h2 : M i i = -1
            · simp [h2, oddValOf]
            · by_cases h3 : M i i = 1
              · simp [h3, oddValOf]
              · simp only [h1, h2, h3, ↓reduceIte, oddValOf]
                by_contra h4; apply ho; exact ⟨(M i i) / 2, by omega⟩
        have hw_valid : ∀ i : Fin n, (w i.castSucc).1 % 2 ≠ (w i.succ).1 % 2 := by
          intro i
          rw [← odd_diag_ok_iff (w i.castSucc) (w i.succ)]
          rw [hw_eq, hw_eq]; exact hdiag.2.2 i i
        refine ⟨Sum.inl ⟨w, hw_valid⟩, ?_⟩
        apply Subtype.ext; dsimp [φ]; rw [hMeq]; congr 1; funext i; exact hw_eq i
  rw [Nat.card_congr (Equiv.ofBijective φ hbij).symm, Nat.card_eq_fintype_card, Fintype.card_sum]

private lemma a_zero : a 0 = 0 := by unfold a; simp

private lemma a_closed (n : ℕ) (hn : 1 ≤ n) :
    (Even n → 3 * (a n : ℤ) = -9 * 2 ^ (n / 2) + 29 * 2 ^ n + 1) ∧
    (Odd n → 3 * (a n : ℤ) = -3 * 2 ^ (n / 2 + 2) + 29 * 2 ^ n - 1) := by
  have ha := a_eq_odd_add_even n hn
  rw [card_OddWords] at ha
  have hev := card_EvenWords n
  constructor
  · intro he
    rw [if_pos he] at hev
    rw [ha]; push_cast; linarith
  · intro ho
    have hne : ¬Even n := Nat.not_even_iff_odd.mpr ho
    rw [if_neg hne] at hev
    rw [ha]; push_cast; linarith

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

theorem solution : type_of% @OMA.S_oeis_a211327.main := by
  refine ⟨?_, fun n hn he => (a_closed n hn).1 he, fun n hn ho => (a_closed n hn).2 ho⟩
  ext n
  have hexp : (1 + (PowerSeries.X : PowerSeries ℚ)) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) =
      1 - PowerSeries.X ^ 1 - PowerSeries.C 4 * PowerSeries.X ^ 2 + PowerSeries.C 2 * PowerSeries.X ^ 3 + PowerSeries.C 4 * PowerSeries.X ^ 4 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X : PowerSeries ℚ) * (15 + 18 * PowerSeries.X - 24 * PowerSeries.X ^ 2 - 28 * PowerSeries.X ^ 3) =
      PowerSeries.C 15 * PowerSeries.X ^ 1 + PowerSeries.C 18 * PowerSeries.X ^ 2 - PowerSeries.C 24 * PowerSeries.X ^ 3 - PowerSeries.C 28 * PowerSeries.X ^ 4 := by
    simp only [map_ofNat]; ring
  rw [hR]
  have hc : ∀ (c : ℚ) (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ j)) =
      c * if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro c j
    rw [mul_comm (PowerSeries.C c), ← mul_assoc, mul_comm _ (PowerSeries.C c),
        PowerSeries.coeff_C_mul, coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  have hX : ∀ (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * PowerSeries.X ^ j) =
      if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro j; rw [coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, hc, hX,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  have ha1 : (a 1 : ℚ) = 15 := by
    have h := (a_closed 1 (by omega)).2 (by decide); norm_num at h
    have hq : 3 * (a 1 : ℚ) = 45 := by exact_mod_cast h
    linarith
  have ha2 : (a 2 : ℚ) = 33 := by
    have h := (a_closed 2 (by omega)).1 (by decide); norm_num at h
    have hq : 3 * (a 2 : ℚ) = 99 := by exact_mod_cast h
    linarith
  have ha3 : (a 3 : ℚ) = 69 := by
    have h := (a_closed 3 (by omega)).2 (by decide); norm_num at h
    have hq : 3 * (a 3 : ℚ) = 207 := by exact_mod_cast h
    linarith
  have ha4 : (a 4 : ℚ) = 143 := by
    have h := (a_closed 4 (by omega)).1 (by decide); norm_num at h
    have hq : 3 * (a 4 : ℚ) = 429 := by exact_mod_cast h
    linarith
  rcases n with _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, ha1]
  · simp [a_zero, ha1, ha2]; norm_num
  · simp [a_zero, ha1, ha2, ha3]; norm_num
  · simp [a_zero, ha1, ha2, ha3, ha4]; norm_num
  · simp only [show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, ↓reduceIte,
      show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      show ¬(m + 5 = 1) by omega, show ¬(m + 5 = 2) by omega, show ¬(m + 5 = 3) by omega, show ¬(m + 5 = 4) by omega]
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have h5 : 3 * (a (k + k + 5) : ℚ) = -3 * 2 ^ (k + 4) + 29 * 2 ^ (k + k + 5) - 1 := by
        have h := (a_closed (k + k + 5) (by omega)).2 ⟨k + 2, by omega⟩
        rw [show (k + k + 5) / 2 + 2 = k + 4 by omega] at h; exact_mod_cast h
      have h4 : 3 * (a (k + k + 4) : ℚ) = -9 * 2 ^ (k + 2) + 29 * 2 ^ (k + k + 4) + 1 := by
        have h := (a_closed (k + k + 4) (by omega)).1 ⟨k + 2, by omega⟩
        rw [show (k + k + 4) / 2 = k + 2 by omega] at h; exact_mod_cast h
      have h3 : 3 * (a (k + k + 3) : ℚ) = -3 * 2 ^ (k + 3) + 29 * 2 ^ (k + k + 3) - 1 := by
        have h := (a_closed (k + k + 3) (by omega)).2 ⟨k + 1, by omega⟩
        rw [show (k + k + 3) / 2 + 2 = k + 3 by omega] at h; exact_mod_cast h
      have h2 : 3 * (a (k + k + 2) : ℚ) = -9 * 2 ^ (k + 1) + 29 * 2 ^ (k + k + 2) + 1 := by
        have h := (a_closed (k + k + 2) (by omega)).1 ⟨k + 1, by omega⟩
        rw [show (k + k + 2) / 2 = k + 1 by omega] at h; exact_mod_cast h
      have h1 : 3 * (a (k + k + 1) : ℚ) = -3 * 2 ^ (k + 2) + 29 * 2 ^ (k + k + 1) - 1 := by
        have h := (a_closed (k + k + 1) (by omega)).2 ⟨k, by omega⟩
        rw [show (k + k + 1) / 2 + 2 = k + 2 by omega] at h; exact_mod_cast h
      have hp : (2 : ℚ) ^ (k + 4) = 8 * 2 ^ (k + 1) ∧ (2 : ℚ) ^ (k + 3) = 4 * 2 ^ (k + 1) ∧ (2 : ℚ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        refine ⟨?_, ?_, ?_⟩ <;> ring
      have hq : (2 : ℚ) ^ (k + k + 5) = 16 * 2 ^ (k + k + 1) ∧ (2 : ℚ) ^ (k + k + 4) = 8 * 2 ^ (k + k + 1) ∧
                (2 : ℚ) ^ (k + k + 3) = 4 * 2 ^ (k + k + 1) ∧ (2 : ℚ) ^ (k + k + 2) = 2 * 2 ^ (k + k + 1) := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
      linarith [h5, h4, h3, h2, h1, hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2]
    · have h5 : 3 * (a (2 * k + 1 + 5) : ℚ) = -9 * 2 ^ (k + 3) + 29 * 2 ^ (2 * k + 6) + 1 := by
        have h := (a_closed (2 * k + 1 + 5) (by omega)).1 ⟨k + 3, by omega⟩
        rw [show (2 * k + 1 + 5) / 2 = k + 3 by omega, show 2 * k + 1 + 5 = 2 * k + 6 by omega] at h; exact_mod_cast h
      have h4 : 3 * (a (2 * k + 1 + 4) : ℚ) = -3 * 2 ^ (k + 4) + 29 * 2 ^ (2 * k + 5) - 1 := by
        have h := (a_closed (2 * k + 1 + 4) (by omega)).2 ⟨k + 2, by omega⟩
        rw [show (2 * k + 1 + 4) / 2 + 2 = k + 4 by omega, show 2 * k + 1 + 4 = 2 * k + 5 by omega] at h; exact_mod_cast h
      have h3 : 3 * (a (2 * k + 1 + 3) : ℚ) = -9 * 2 ^ (k + 2) + 29 * 2 ^ (2 * k + 4) + 1 := by
        have h := (a_closed (2 * k + 1 + 3) (by omega)).1 ⟨k + 2, by omega⟩
        rw [show (2 * k + 1 + 3) / 2 = k + 2 by omega, show 2 * k + 1 + 3 = 2 * k + 4 by omega] at h; exact_mod_cast h
      have h2 : 3 * (a (2 * k + 1 + 2) : ℚ) = -3 * 2 ^ (k + 3) + 29 * 2 ^ (2 * k + 3) - 1 := by
        have h := (a_closed (2 * k + 1 + 2) (by omega)).2 ⟨k + 1, by omega⟩
        rw [show (2 * k + 1 + 2) / 2 + 2 = k + 3 by omega, show 2 * k + 1 + 2 = 2 * k + 3 by omega] at h; exact_mod_cast h
      have h1 : 3 * (a (2 * k + 1 + 1) : ℚ) = -9 * 2 ^ (k + 1) + 29 * 2 ^ (2 * k + 2) + 1 := by
        have h := (a_closed (2 * k + 1 + 1) (by omega)).1 ⟨k + 1, by omega⟩
        rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, show 2 * k + 1 + 1 = 2 * k + 2 by omega] at h; exact_mod_cast h
      have hp : (2 : ℚ) ^ (k + 4) = 8 * 2 ^ (k + 1) ∧ (2 : ℚ) ^ (k + 3) = 4 * 2 ^ (k + 1) ∧ (2 : ℚ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        refine ⟨?_, ?_, ?_⟩ <;> ring
      have hq : (2 : ℚ) ^ (2 * k + 6) = 16 * 2 ^ (2 * k + 2) ∧ (2 : ℚ) ^ (2 * k + 5) = 8 * 2 ^ (2 * k + 2) ∧
                (2 : ℚ) ^ (2 * k + 4) = 4 * 2 ^ (2 * k + 2) ∧ (2 : ℚ) ^ (2 * k + 3) = 2 * 2 ^ (2 * k + 2) := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
      linarith [h5, h4, h3, h2, h1, hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2]

end OMA.P_oeis_a211327

theorem OMA.solution : type_of% @OMA.S_oeis_a211327.main :=
  OMA.P_oeis_a211327.solution
