import OMAStatements.S_oeis_a163714

namespace A163714Proof

open OMA.S_oeis_a163714 PowerSeries

abbrev Row := Fin 3

def rowVal : Row → Fin 2 → Fin 2
  | ⟨0, _⟩ => fun c => if c = 0 then 1 else 0
  | ⟨1, _⟩ => fun c => if c = 0 then 0 else 1
  | ⟨2, _⟩ => fun _ => 1

def toGrid {n : ℕ} (w : Fin n → Row) : Fin n → Fin 2 → Fin 2 :=
  fun i c => rowVal (w i) c

lemma rowVal_injective : Function.Injective rowVal := by
  decide

lemma toGrid_injective {n : ℕ} : Function.Injective (@toGrid n) := by
  intro w1 w2 h
  funext i
  exact rowVal_injective (funext fun c => congrFun (congrFun h i) c)

def isValidWord {n : ℕ} (w : Fin n → Row) : Prop :=
  (∀ i : Fin n, ∀ hi : (i : ℕ) + 1 < n,
    let r1 := w i
    let r2 := w ⟨(i : ℕ) + 1, hi⟩
    ¬ (r1 = 0 ∧ r2 = 1) ∧ ¬ (r1 = 1 ∧ r2 = 0) ∧ ¬ (r1 = 2 ∧ r2 = 2)) ∧
  (∀ i : Fin n, ∀ hi : (i : ℕ) + 2 < n,
    w ⟨(i : ℕ) + 1, by omega⟩ = 2 → w i ≠ w ⟨(i : ℕ) + 2, hi⟩)

instance {n : ℕ} (w : Fin n → Row) : Decidable (isValidWord w) := by
  unfold isValidWord
  infer_instance

lemma isAdj_symm {n : ℕ} {p q : Fin n × Fin 2} (h : isAdj p q) : isAdj q p := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · left; exact ⟨h1.symm, Or.inr h2⟩
  · left; exact ⟨h1.symm, Or.inl h2⟩
  · right; exact ⟨h1.symm, Or.inr h2⟩
  · right; exact ⟨h1.symm, Or.inl h2⟩

lemma adjOne_symm {n : ℕ} {A : Fin n → Fin 2 → Fin 2} {p q : Fin n × Fin 2}
    (h : adjOne A p q) : adjOne A q p :=
  ⟨h.2.1, h.1, isAdj_symm h.2.2⟩

lemma reflTransGen_adjOne_symm {n : ℕ} {A : Fin n → Fin 2 → Fin 2} {p q : Fin n × Fin 2}
    (h : Relation.ReflTransGen (adjOne A) p q) : Relation.ReflTransGen (adjOne A) q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (adjOne_symm hstep) ih

lemma fin2_eq_zero_of_ne_one {x : Fin 2} (h : x ≠ 1) : x = 0 := by
  fin_cases x <;> simp_all

lemma no_zero_row {n : ℕ} {A : Fin n → Fin 2 → Fin 2} (hA : isValid n A) (r : Fin n) :
    A r 0 = 1 ∨ A r 1 = 1 := by
  by_contra h
  have h00 : A r 0 ≠ 1 := fun h1 => h (Or.inl h1)
  have h01 : A r 1 ≠ 1 := fun h1 => h (Or.inr h1)
  rcases hA.2.1 with ⟨hn, c1, c2, h0, hlast, hpath⟩
  by_cases hr0 : (r : ℕ) = 0
  · have hreq : r = ⟨0, hn⟩ := Fin.ext hr0
    subst hreq
    fin_cases c1
    · exact h00 h0
    · exact h01 h0
  · by_cases hrl : (r : ℕ) = n - 1
    · have hreq : r = ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ := Fin.ext hrl
      subst hreq
      fin_cases c2
      · exact h00 hlast
      · exact h01 hlast
    · have hlt : ∀ q : Fin n × Fin 2,
          Relation.ReflTransGen (adjOne A) (⟨0, hn⟩, c1) q → (q.1 : ℕ) < (r : ℕ) := by
        intro q hq
        induction hq with
        | refl => simp; omega
        | @tail u v _ hstep ih =>
          rcases v with ⟨vr, vc⟩
          rcases hstep with ⟨_, hv1, hadj⟩
          have hne : (vr : ℕ) ≠ (r : ℕ) := by
            intro heq
            have hveq : vr = r := Fin.ext heq
            rw [hveq] at hv1
            fin_cases vc
            · exact h00 hv1
            · exact h01 hv1
          rcases hadj with ⟨h1, _⟩ | ⟨_, h2 | h2⟩
          · dsimp only at h1 ih ⊢; omega
          · dsimp only at h2 ih ⊢; omega
          · dsimp only at h2 ih ⊢; omega
      have hbad := hlt _ hpath
      simp at hbad
      omega

lemma deg_le_two_contra {n : ℕ} {A : Fin n → Fin 2 → Fin 2} (hA : isValid n A)
    {p q1 q2 q3 : Fin n × Fin 2}
    (hp : A p.1 p.2 = 1)
    (h1 : A q1.1 q1.2 = 1 ∧ isAdj p q1)
    (h2 : A q2.1 q2.2 = 1 ∧ isAdj p q2)
    (h3 : A q3.1 q3.2 = 1 ∧ isAdj p q3)
    (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h23 : q2 ≠ q3) : False := by
  have hle := hA.2.2 p hp
  have hsub : ({q1, q2, q3} : Finset (Fin n × Fin 2)) ⊆
      Finset.univ.filter (fun q : Fin n × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q) := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hq with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hcard : ({q1, q2, q3} : Finset (Fin n × Fin 2)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h23]
    · simp [h12, h13]
  have := Finset.card_le_card hsub
  omega

lemma isValid_one_iff (A : Fin 1 → Fin 2 → Fin 2) :
    isValid 1 A ↔ A 0 0 = 1 ∨ A 0 1 = 1 := by
  constructor
  · intro hA
    exact no_zero_row hA 0
  · intro h0
    refine ⟨?_, ?_, ?_⟩
    · intro p q hp hq
      rcases p with ⟨pr, pc⟩
      rcases q with ⟨qr, qc⟩
      have hp1 : pr = 0 := Subsingleton.elim _ _
      have hq1 : qr = 0 := Subsingleton.elim _ _
      subst hp1; subst hq1
      by_cases hc : pc = qc
      · subst hc; exact Relation.ReflTransGen.refl
      · apply Relation.ReflTransGen.single
        refine ⟨hp, hq, Or.inl ⟨rfl, ?_⟩⟩
        fin_cases pc <;> fin_cases qc <;> simp_all
    · rcases h0 with h | h
      · exact ⟨Nat.one_pos, 0, 0, h, h, Relation.ReflTransGen.refl⟩
      · exact ⟨Nat.one_pos, 1, 1, h, h, Relation.ReflTransGen.refl⟩
    · intro p _
      have hle : (Finset.univ.filter (fun q : Fin 1 × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q)).card ≤
          (Finset.univ : Finset (Fin 1 × Fin 2)).card :=
        Finset.card_filter_le _ _
      have hcard : (Finset.univ : Finset (Fin 1 × Fin 2)).card = 2 := by decide
      omega

lemma a_one : a 1 = 3 := by
  unfold a
  simp only [Nat.one_ne_zero, ↓reduceIte]
  rw [Nat.card_congr (Equiv.subtypeEquivRight isValid_one_iff), Nat.card_eq_fintype_card]
  decide

lemma isValid_two_iff (A : Fin 2 → Fin 2 → Fin 2) :
    isValid 2 A ↔
      (A 0 0 = 1 ∨ A 0 1 = 1) ∧
      (A 1 0 = 1 ∨ A 1 1 = 1) ∧
      ¬ (A 0 0 = 1 ∧ A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = 1) ∧
      ¬ (A 0 0 = 0 ∧ A 0 1 = 1 ∧ A 1 0 = 1 ∧ A 1 1 = 0) := by
  constructor
  · intro hA
    refine ⟨no_zero_row hA 0, no_zero_row hA 1, ?_, ?_⟩
    · rintro ⟨h00, h01, h10, h11⟩
      rcases hA.2.1 with ⟨hn, c1, c2, hc1, hc2, hpath⟩
      have hc1' : c1 = 0 := by fin_cases c1 <;> simp_all
      have hc2' : c2 = 1 := by fin_cases c2 <;> simp_all
      have hstay : ∀ q : Fin 2 × Fin 2,
          Relation.ReflTransGen (adjOne A) (0, 0) q → q = (0, 0) := by
        intro q hq
        induction hq with
        | refl => rfl
        | @tail u v _ hstep ih =>
          subst ih
          rcases v with ⟨vr, vc⟩
          rcases hstep with ⟨_, hv1, hadj⟩
          rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
          · have hvr : vr = 0 := Fin.ext (by dsimp only at h1; omega)
            have hvc : vc = 1 := Fin.ext (by dsimp only at h2; omega)
            subst hvr; subst hvc; simp [h01] at hv1
          · dsimp only at h2; omega
          · have hvr : vr = 1 := Fin.ext (by dsimp only at h2; omega)
            have hvc : vc = 0 := Fin.ext (by dsimp only at h1; omega)
            subst hvr; subst hvc; simp [h10] at hv1
          · dsimp only at h2; omega
      have hbad := hstay _ (by simpa [hc1', hc2'] using hpath)
      simp at hbad
    · rintro ⟨h00, h01, h10, h11⟩
      rcases hA.2.1 with ⟨hn, c1, c2, hc1, hc2, hpath⟩
      have hc1' : c1 = 1 := by fin_cases c1 <;> simp_all
      have hc2' : c2 = 0 := by fin_cases c2 <;> simp_all
      have hstay : ∀ q : Fin 2 × Fin 2,
          Relation.ReflTransGen (adjOne A) (0, 1) q → q = (0, 1) := by
        intro q hq
        induction hq with
        | refl => rfl
        | @tail u v _ hstep ih =>
          subst ih
          rcases v with ⟨vr, vc⟩
          rcases hstep with ⟨_, hv1, hadj⟩
          rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
          · dsimp only at h2; omega
          · have hvr : vr = 0 := Fin.ext (by dsimp only at h1; omega)
            have hvc : vc = 0 := Fin.ext (by dsimp only at h2; omega)
            subst hvr; subst hvc; simp [h00] at hv1
          · have hvr : vr = 1 := Fin.ext (by dsimp only at h2; omega)
            have hvc : vc = 1 := Fin.ext (by dsimp only at h1; omega)
            subst hvr; subst hvc; simp [h11] at hv1
          · dsimp only at h2; omega
      have hbad := hstay _ (by simpa [hc1', hc2'] using hpath)
      simp at hbad
  · rintro ⟨h0, h1, hno1, hno2⟩
    have hbridge : ∃ c : Fin 2, A 0 c = 1 ∧ A 1 c = 1 := by
      by_cases h00 : A 0 0 = 1
      · by_cases h10 : A 1 0 = 1
        · exact ⟨0, h00, h10⟩
        · have h10z : A 1 0 = 0 := fin2_eq_zero_of_ne_one h10
          have h11 : A 1 1 = 1 := by rcases h1 with h | h; exact absurd h h10; exact h
          by_cases h01 : A 0 1 = 1
          · exact ⟨1, h01, h11⟩
          · exact absurd ⟨h00, fin2_eq_zero_of_ne_one h01, h10z, h11⟩ hno1
      · have h00z : A 0 0 = 0 := fin2_eq_zero_of_ne_one h00
        have h01 : A 0 1 = 1 := by rcases h0 with h | h; exact absurd h h00; exact h
        by_cases h11 : A 1 1 = 1
        · exact ⟨1, h01, h11⟩
        · have h11z : A 1 1 = 0 := fin2_eq_zero_of_ne_one h11
          have h10 : A 1 0 = 1 := by rcases h1 with h | h; exact h; exact absurd h h11
          exact absurd ⟨h00z, h01, h10, h11z⟩ hno2
    rcases hbridge with ⟨cb, hcb0, hcb1⟩
    have hrow : ∀ (r c1 c2 : Fin 2), A r c1 = 1 → A r c2 = 1 →
        Relation.ReflTransGen (adjOne A) (r, c1) (r, c2) := by
      intro r c1 c2 hc1 hc2
      by_cases heq : c1 = c2
      · subst heq; exact Relation.ReflTransGen.refl
      · apply Relation.ReflTransGen.single
        refine ⟨hc1, hc2, Or.inl ⟨rfl, ?_⟩⟩
        fin_cases c1 <;> fin_cases c2 <;> simp_all
    have hstep01 : Relation.ReflTransGen (adjOne A) (0, cb) (1, cb) :=
      Relation.ReflTransGen.single ⟨hcb0, hcb1, Or.inr ⟨rfl, Or.inl rfl⟩⟩
    have hto0 : ∀ p : Fin 2 × Fin 2, A p.1 p.2 = 1 →
        Relation.ReflTransGen (adjOne A) (0, cb) p := by
      intro ⟨pr, pc⟩ hp
      fin_cases pr
      · exact hrow 0 cb pc hcb0 hp
      · exact hstep01.trans (hrow 1 cb pc hcb1 hp)
    refine ⟨?_, ?_, ?_⟩
    · intro p q hp hq
      exact (reflTransGen_adjOne_symm (hto0 p hp)).trans (hto0 q hq)
    · exact ⟨by omega, cb, cb, hcb0, hcb1, hstep01⟩
    · intro p _
      have hsub : Finset.univ.filter (fun q : Fin 2 × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q) ⊆
          Finset.univ.filter (fun q : Fin 2 × Fin 2 => isAdj p q) := by
        intro q hq; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢; exact hq.2
      have hle := Finset.card_le_card hsub
      have h2 : (Finset.univ.filter (fun q : Fin 2 × Fin 2 => isAdj p q)).card = 2 := by
        rcases p with ⟨r, c⟩
        fin_cases r <;> fin_cases c <;> decide
      omega

lemma a_two : a 2 = 7 := by
  unfold a
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [Nat.card_congr (Equiv.subtypeEquivRight isValid_two_iff), Nat.card_eq_fintype_card]
  decide

lemma row_has_one (r : Row) : ∃ c : Fin 2, rowVal r c = 1 := by
  fin_cases r
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

lemma rowVal_two_ne_same (a b : Row) (c : Fin 2)
    (hane : a ≠ 2) (hbne : b ≠ 2) (hab : a ≠ b)
    (ha : rowVal a c = 1) (hb : rowVal b c = 1) : False := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [rowVal]

lemma rowVal_no_horiz (a : Row) (c c' : Fin 2)
    (ha2 : a ≠ 2) (hc : rowVal a c = 1) (hne : c' ≠ c) : rowVal a c' ≠ 1 := by
  fin_cases a <;> fin_cases c <;> fin_cases c' <;> simp_all [rowVal]

lemma isValid_of_isValidWord {n : ℕ} (hn : 3 ≤ n) (w : Fin n → Row) (hw : isValidWord w) :
    isValid n (toGrid w) := by
  have hrow : ∀ (r : Fin n) (c1 c2 : Fin 2), toGrid w r c1 = 1 → toGrid w r c2 = 1 →
      Relation.ReflTransGen (adjOne (toGrid w)) (r, c1) (r, c2) := by
    intro r c1 c2 hc1 hc2
    by_cases heq : c1 = c2
    · subst heq; exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      refine ⟨hc1, hc2, Or.inl ⟨rfl, ?_⟩⟩
      fin_cases c1 <;> fin_cases c2 <;> simp_all
  have hbridge : ∀ (i : ℕ) (hi : i + 1 < n),
      ∃ c : Fin 2, toGrid w ⟨i, by omega⟩ c = 1 ∧ toGrid w ⟨i + 1, hi⟩ c = 1 := by
    intro i hi
    have h1 := hw.1 ⟨i, by omega⟩ (by dsimp; omega)
    have hnot01 : ¬ (w ⟨i, by omega⟩ = 0 ∧ w ⟨i + 1, hi⟩ = 1) := h1.1
    have hnot10 : ¬ (w ⟨i, by omega⟩ = 1 ∧ w ⟨i + 1, hi⟩ = 0) := h1.2.1
    generalize ha : w ⟨i, by omega⟩ = a at hnot01 hnot10
    generalize hb : w ⟨i + 1, hi⟩ = b at hnot01 hnot10
    simp only [toGrid, ha, hb]
    fin_cases a <;> fin_cases b <;> simp_all [rowVal]
    all_goals first | exact ⟨0, rfl, rfl⟩ | exact ⟨1, rfl, rfl⟩
  have hconn0 : ∀ (k : ℕ) (hk : k < n) (c0 ck : Fin 2),
      toGrid w ⟨0, by omega⟩ c0 = 1 → toGrid w ⟨k, hk⟩ ck = 1 →
      Relation.ReflTransGen (adjOne (toGrid w)) (⟨0, by omega⟩, c0) (⟨k, hk⟩, ck) := by
    intro k
    induction k with
    | zero =>
      intro hk c0 ck h0 hck
      exact hrow ⟨0, hk⟩ c0 ck h0 hck
    | succ k ih =>
      intro hk c0 ck h0 hck
      rcases hbridge k hk with ⟨cb, hcb1, hcb2⟩
      have hp1 := ih (by omega) c0 cb h0 hcb1
      have hstep : Relation.ReflTransGen (adjOne (toGrid w)) (⟨k, by omega⟩, cb) (⟨k + 1, hk⟩, cb) :=
        Relation.ReflTransGen.single ⟨hcb1, hcb2, Or.inr ⟨rfl, Or.inl rfl⟩⟩
      exact (hp1.trans hstep).trans (hrow ⟨k + 1, hk⟩ cb ck hcb2 hck)
  rcases row_has_one (w ⟨0, by omega⟩) with ⟨c0, hc0⟩
  rcases row_has_one (w ⟨n - 1, by omega⟩) with ⟨cl, hcl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p q hp hq
    exact (reflTransGen_adjOne_symm (hconn0 p.1.1 p.1.2 c0 p.2 hc0 hp)).trans
      (hconn0 q.1.1 q.1.2 c0 q.2 hc0 hq)
  · exact ⟨by omega, c0, cl, hc0, hcl, hconn0 (n - 1) (by omega) c0 cl hc0 hcl⟩
  · intro ⟨r, c⟩ hp
    by_cases hr2 : w r = 2
    · have hnotboth : ¬ ((∃ hlt : 0 < (r : ℕ), toGrid w ⟨(r : ℕ) - 1, by omega⟩ c = 1) ∧
          (∃ hgt : (r : ℕ) + 1 < n, toGrid w ⟨(r : ℕ) + 1, hgt⟩ c = 1)) := by
        rintro ⟨⟨hlt, hup⟩, ⟨hgt, hdn⟩⟩
        have hi2 : ((r : ℕ) - 1) + 2 < n := by omega
        have hrm1 : (⟨((r : ℕ) - 1) + 1, by omega⟩ : Fin n) = r := Fin.ext (by dsimp; omega)
        have hne := hw.2 ⟨(r : ℕ) - 1, by omega⟩ (by dsimp; omega) (by rw [hrm1]; exact hr2)
        have hnoBB1 := (hw.1 ⟨(r : ℕ) - 1, by omega⟩ (by dsimp; omega)).2.2
        rw [hrm1] at hnoBB1
        have hnoBB2 := (hw.1 r hgt).2.2
        have hne_fin : (⟨(r : ℕ) + 1, hgt⟩ : Fin n) = ⟨((r : ℕ) - 1) + 2, hi2⟩ := Fin.ext (by dsimp; omega)
        rw [hne_fin] at hnoBB2
        have hdn' : rowVal (w ⟨((r : ℕ) - 1) + 2, hi2⟩) c = 1 := by
          rw [← hne_fin]; exact hdn
        exact rowVal_two_ne_same (w ⟨(r : ℕ) - 1, by omega⟩) (w ⟨((r : ℕ) - 1) + 2, hi2⟩) c
          (fun ha2 => hnoBB1 ⟨ha2, hr2⟩) (fun hb2 => hnoBB2 ⟨hr2, hb2⟩) hne hup hdn'
      by_cases hup : ∃ hlt : 0 < (r : ℕ), toGrid w ⟨(r : ℕ) - 1, by omega⟩ c = 1
      · rcases hup with ⟨hlt, hupv⟩
        have hnodn : ∀ hgt : (r : ℕ) + 1 < n, toGrid w ⟨(r : ℕ) + 1, hgt⟩ c ≠ 1 := by
          intro hgt hdn; exact hnotboth ⟨⟨hlt, hupv⟩, ⟨hgt, hdn⟩⟩
        let s : Finset (Fin n × Fin 2) := {(r, 1 - c), (⟨(r : ℕ) - 1, by omega⟩, c)}
        have hsub : Finset.univ.filter (fun q : Fin n × Fin 2 =>
            toGrid w q.1 q.2 = 1 ∧ isAdj (r, c) q) ⊆ s := by
          intro ⟨qr, qc⟩ hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          simp only [s, Finset.mem_insert, Finset.mem_singleton]
          rcases hq.2 with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
          · dsimp only at h1 h2
            left; exact Prod.ext (Fin.ext h1.symm) (by fin_cases c <;> fin_cases qc <;> simp_all)
          · dsimp only at h1 h2
            left; exact Prod.ext (Fin.ext h1.symm) (by fin_cases c <;> fin_cases qc <;> simp_all)
          · dsimp only at h1 h2
            exfalso
            have hgt : (r : ℕ) + 1 < n := by omega
            have hqeq : qr = ⟨(r : ℕ) + 1, hgt⟩ := Fin.ext (by dsimp; omega)
            have hceq : qc = c := Fin.ext h1.symm
            rw [hqeq, hceq] at hq
            exact hnodn hgt hq.1
          · dsimp only at h1 h2
            right; exact Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext h1.symm)
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      · have hup' : ∀ hlt : 0 < (r : ℕ), toGrid w ⟨(r : ℕ) - 1, by omega⟩ c ≠ 1 :=
          fun hlt h => hup ⟨hlt, h⟩
        by_cases hgt : (r : ℕ) + 1 < n
        · let s : Finset (Fin n × Fin 2) := {(r, 1 - c), (⟨(r : ℕ) + 1, hgt⟩, c)}
          have hsub : Finset.univ.filter (fun q : Fin n × Fin 2 =>
              toGrid w q.1 q.2 = 1 ∧ isAdj (r, c) q) ⊆ s := by
            intro ⟨qr, qc⟩ hq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
            simp only [s, Finset.mem_insert, Finset.mem_singleton]
            rcases hq.2 with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
            · dsimp only at h1 h2
              left; exact Prod.ext (Fin.ext h1.symm) (by fin_cases c <;> fin_cases qc <;> simp_all)
            · dsimp only at h1 h2
              left; exact Prod.ext (Fin.ext h1.symm) (by fin_cases c <;> fin_cases qc <;> simp_all)
            · dsimp only at h1 h2
              right; exact Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext h1.symm)
            · dsimp only at h1 h2
              exfalso
              have hlt : 0 < (r : ℕ) := by omega
              have hqeq : qr = ⟨(r : ℕ) - 1, by omega⟩ := Fin.ext (by dsimp; omega)
              have hceq : qc = c := Fin.ext h1.symm
              rw [hqeq, hceq] at hq
              exact hup' hlt hq.1
          exact (Finset.card_le_card hsub).trans Finset.card_le_two
        · let s : Finset (Fin n × Fin 2) := {(r, 1 - c)}
          have hsub : Finset.univ.filter (fun q : Fin n × Fin 2 =>
              toGrid w q.1 q.2 = 1 ∧ isAdj (r, c) q) ⊆ s := by
            intro ⟨qr, qc⟩ hq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
            simp only [s, Finset.mem_singleton]
            rcases hq.2 with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
            · dsimp only at h1 h2
              exact Prod.ext (Fin.ext h1.symm) (by fin_cases c <;> fin_cases qc <;> simp_all)
            · dsimp only at h1 h2
              exact Prod.ext (Fin.ext h1.symm) (by fin_cases c <;> fin_cases qc <;> simp_all)
            · dsimp only at h1 h2; omega
            · dsimp only at h1 h2
              exfalso
              have hlt : 0 < (r : ℕ) := by omega
              have hqeq : qr = ⟨(r : ℕ) - 1, by omega⟩ := Fin.ext (by dsimp; omega)
              have hceq : qc = c := Fin.ext h1.symm
              rw [hqeq, hceq] at hq
              exact hup' hlt hq.1
          exact (Finset.card_le_card hsub).trans (by simp [s])
    · let s : Finset (Fin n × Fin 2) :=
        {(⟨(r : ℕ) - 1, by omega⟩, c), (⟨min ((r : ℕ) + 1) (n - 1), by omega⟩, c)}
      have hsub : Finset.univ.filter (fun q : Fin n × Fin 2 =>
          toGrid w q.1 q.2 = 1 ∧ isAdj (r, c) q) ⊆ s := by
        intro ⟨qr, qc⟩ hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        simp only [s, Finset.mem_insert, Finset.mem_singleton]
        rcases hq.2 with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
        · dsimp only at h1 h2
          exfalso
          have hq1 : qr = r := Fin.ext h1.symm
          rw [hq1] at hq
          exact rowVal_no_horiz (w r) c qc hr2 hp (by intro heq; subst heq; omega) hq.1
        · dsimp only at h1 h2
          exfalso
          have hq1 : qr = r := Fin.ext h1.symm
          rw [hq1] at hq
          exact rowVal_no_horiz (w r) c qc hr2 hp (by intro heq; subst heq; omega) hq.1
        · dsimp only at h1 h2
          right; exact Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext h1.symm)
        · dsimp only at h1 h2
          left; exact Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext h1.symm)
      exact (Finset.card_le_card hsub).trans Finset.card_le_two

lemma exists_isValidWord_of_isValid {n : ℕ} (hn : 3 ≤ n) {A : Fin n → Fin 2 → Fin 2}
    (hA : isValid n A) : ∃ w : Fin n → Row, A = toGrid w ∧ isValidWord w := by
  let w : Fin n → Row := fun i =>
    if A i 0 = 1 then (if A i 1 = 1 then 2 else 0) else 1
  have hgrid : A = toGrid w := by
    funext i c
    have hnz := no_zero_row hA i
    dsimp only [toGrid, w]
    split_ifs with h0 h1
    · fin_cases c <;> simp [rowVal, h0, h1]
    · fin_cases c
      · simp [rowVal, h0]
      · simp [rowVal, fin2_eq_zero_of_ne_one h1]
    · have h1 : A i 1 = 1 := by rcases hnz with h | h; exact absurd h h0; exact h
      fin_cases c
      · simp [rowVal, fin2_eq_zero_of_ne_one h0]
      · simp [rowVal, h1]
  refine ⟨w, hgrid, ?_, ?_⟩
  · intro i hi
    have hnoLR : ¬ (w i = 0 ∧ w ⟨(i : ℕ) + 1, hi⟩ = 1) := by
      rintro ⟨h0, h1⟩
      rcases hA.2.1 with ⟨hn0, c1, c2, hc1, hc2, hpath⟩
      have hstay : ∀ q : Fin n × Fin 2,
          Relation.ReflTransGen (adjOne A) (⟨0, hn0⟩, c1) q → (q.1 : ℕ) ≤ (i : ℕ) := by
        intro q hq
        induction hq with
        | refl => simp
        | @tail u v _ hstep ih =>
          rcases u with ⟨ur, uc⟩
          rcases v with ⟨vr, vc⟩
          rcases hstep with ⟨hu1, hv1, hadj⟩
          rcases hadj with ⟨heq, _⟩ | ⟨heq, hstep1 | hstep1⟩
          · dsimp only at heq ih ⊢; omega
          · dsimp only at heq hstep1 ih ⊢
            by_cases hui : (ur : ℕ) = (i : ℕ)
            · exfalso
              have hu1' : toGrid w i uc = 1 := by
                rw [← hgrid]; have : i = ur := Fin.ext hui.symm; rw [this]; exact hu1
              have hv1' : toGrid w ⟨(i : ℕ) + 1, hi⟩ uc = 1 := by
                rw [← hgrid]
                have hv1eq : (⟨(i : ℕ) + 1, hi⟩ : Fin n) = vr := Fin.ext (by dsimp; omega)
                have hv2eq : uc = vc := Fin.ext heq
                rw [hv1eq, hv2eq]; exact hv1
              simp only [toGrid, h0, h1] at hu1' hv1'
              fin_cases uc <;> simp [rowVal] at hu1' hv1'
            · omega
          · dsimp only at hstep1 ih ⊢; omega
      have hbad := hstay _ hpath
      simp at hbad
      omega
    have hnoRL : ¬ (w i = 1 ∧ w ⟨(i : ℕ) + 1, hi⟩ = 0) := by
      rintro ⟨h0, h1⟩
      rcases hA.2.1 with ⟨hn0, c1, c2, hc1, hc2, hpath⟩
      have hstay : ∀ q : Fin n × Fin 2,
          Relation.ReflTransGen (adjOne A) (⟨0, hn0⟩, c1) q → (q.1 : ℕ) ≤ (i : ℕ) := by
        intro q hq
        induction hq with
        | refl => simp
        | @tail u v _ hstep ih =>
          rcases u with ⟨ur, uc⟩
          rcases v with ⟨vr, vc⟩
          rcases hstep with ⟨hu1, hv1, hadj⟩
          rcases hadj with ⟨heq, _⟩ | ⟨heq, hstep1 | hstep1⟩
          · dsimp only at heq ih ⊢; omega
          · dsimp only at heq hstep1 ih ⊢
            by_cases hui : (ur : ℕ) = (i : ℕ)
            · exfalso
              have hu1' : toGrid w i uc = 1 := by
                rw [← hgrid]; have : i = ur := Fin.ext hui.symm; rw [this]; exact hu1
              have hv1' : toGrid w ⟨(i : ℕ) + 1, hi⟩ uc = 1 := by
                rw [← hgrid]
                have hv1eq : (⟨(i : ℕ) + 1, hi⟩ : Fin n) = vr := Fin.ext (by dsimp; omega)
                have hv2eq : uc = vc := Fin.ext heq
                rw [hv1eq, hv2eq]; exact hv1
              simp only [toGrid, h0, h1] at hu1' hv1'
              fin_cases uc <;> simp [rowVal] at hu1' hv1'
            · omega
          · dsimp only at hstep1 ih ⊢; omega
      have hbad := hstay _ hpath
      simp at hbad
      omega
    have hnoBB : ¬ (w i = 2 ∧ w ⟨(i : ℕ) + 1, hi⟩ = 2) := by
      rintro ⟨h0, h1⟩
      have hA_i : ∀ c : Fin 2, A i c = 1 := fun c => by
        rw [hgrid]; simp [toGrid, h0, rowVal]
      have hA_ip1 : ∀ c : Fin 2, A ⟨(i : ℕ) + 1, hi⟩ c = 1 := fun c => by
        rw [hgrid]; simp [toGrid, h1, rowVal]
      by_cases hi0 : 0 < (i : ℕ)
      · rcases no_zero_row hA ⟨(i : ℕ) - 1, by omega⟩ with hc | hc
        · exact deg_le_two_contra hA (p := (i, 0)) (q1 := (i, 1))
            (q2 := (⟨(i : ℕ) + 1, hi⟩, 0)) (q3 := (⟨(i : ℕ) - 1, by omega⟩, 0))
            (hA_i 0) ⟨hA_i 1, Or.inl ⟨rfl, Or.inl rfl⟩⟩
            ⟨hA_ip1 0, Or.inr ⟨rfl, Or.inl rfl⟩⟩
            ⟨hc, Or.inr ⟨rfl, Or.inr (by simp; omega)⟩⟩
            (by intro h; simp at h) (by intro h; simp at h)
            (by intro h; have := congrArg (fun x : Fin n × Fin 2 => (x.1 : ℕ)) h; simp at this; omega)
        · exact deg_le_two_contra hA (p := (i, 1)) (q1 := (i, 0))
            (q2 := (⟨(i : ℕ) + 1, hi⟩, 1)) (q3 := (⟨(i : ℕ) - 1, by omega⟩, 1))
            (hA_i 1) ⟨hA_i 0, Or.inl ⟨rfl, Or.inr rfl⟩⟩
            ⟨hA_ip1 1, Or.inr ⟨rfl, Or.inl rfl⟩⟩
            ⟨hc, Or.inr ⟨rfl, Or.inr (by simp; omega)⟩⟩
            (by intro h; simp at h) (by intro h; simp at h)
            (by intro h; have := congrArg (fun x : Fin n × Fin 2 => (x.1 : ℕ)) h; simp at this; omega)
      · have hi2 : (i : ℕ) + 2 < n := by omega
        rcases no_zero_row hA ⟨(i : ℕ) + 2, hi2⟩ with hc | hc
        · exact deg_le_two_contra hA (p := (⟨(i : ℕ) + 1, hi⟩, 0))
            (q1 := (⟨(i : ℕ) + 1, hi⟩, 1)) (q2 := (i, 0)) (q3 := (⟨(i : ℕ) + 2, hi2⟩, 0))
            (hA_ip1 0) ⟨hA_ip1 1, Or.inl ⟨rfl, Or.inl rfl⟩⟩
            ⟨hA_i 0, Or.inr ⟨rfl, Or.inr rfl⟩⟩
            ⟨hc, Or.inr ⟨rfl, Or.inl (by simp)⟩⟩
            (by intro h; simp at h) (by intro h; simp at h)
            (by intro h; have := congrArg (fun x : Fin n × Fin 2 => (x.1 : ℕ)) h; simp at this)
        · exact deg_le_two_contra hA (p := (⟨(i : ℕ) + 1, hi⟩, 1))
            (q1 := (⟨(i : ℕ) + 1, hi⟩, 0)) (q2 := (i, 1)) (q3 := (⟨(i : ℕ) + 2, hi2⟩, 1))
            (hA_ip1 1) ⟨hA_ip1 0, Or.inl ⟨rfl, Or.inr rfl⟩⟩
            ⟨hA_i 1, Or.inr ⟨rfl, Or.inr rfl⟩⟩
            ⟨hc, Or.inr ⟨rfl, Or.inl (by simp)⟩⟩
            (by intro h; simp at h) (by intro h; simp at h)
            (by intro h; have := congrArg (fun x : Fin n × Fin 2 => (x.1 : ℕ)) h; simp at this)
    exact ⟨hnoLR, hnoRL, hnoBB⟩
  · intro i hi hmid heq
    have hA_mid : ∀ c : Fin 2, A ⟨(i : ℕ) + 1, by omega⟩ c = 1 := fun c => by
      rw [hgrid]; simp [toGrid, hmid, rowVal]
    rcases row_has_one (w i) with ⟨c, hc⟩
    have h1 : A i c = 1 := by rw [hgrid]; exact hc
    have h2 : A ⟨(i : ℕ) + 2, hi⟩ c = 1 := by rw [hgrid]; simp [toGrid, ← heq, hc]
    fin_cases c
    · exact deg_le_two_contra hA (p := (⟨(i : ℕ) + 1, by omega⟩, 0))
        (q1 := (⟨(i : ℕ) + 1, by omega⟩, 1)) (q2 := (i, 0)) (q3 := (⟨(i : ℕ) + 2, hi⟩, 0))
        (hA_mid 0) ⟨hA_mid 1, Or.inl ⟨rfl, Or.inl rfl⟩⟩
        ⟨h1, Or.inr ⟨rfl, Or.inr rfl⟩⟩
        ⟨h2, Or.inr ⟨rfl, Or.inl (by simp)⟩⟩
        (by intro h; simp at h) (by intro h; simp at h)
        (by intro h; have := congrArg (fun x : Fin n × Fin 2 => (x.1 : ℕ)) h; simp at this)
    · exact deg_le_two_contra hA (p := (⟨(i : ℕ) + 1, by omega⟩, 1))
        (q1 := (⟨(i : ℕ) + 1, by omega⟩, 0)) (q2 := (i, 1)) (q3 := (⟨(i : ℕ) + 2, hi⟩, 1))
        (hA_mid 1) ⟨hA_mid 0, Or.inl ⟨rfl, Or.inr rfl⟩⟩
        ⟨h1, Or.inr ⟨rfl, Or.inr rfl⟩⟩
        ⟨h2, Or.inr ⟨rfl, Or.inl (by simp)⟩⟩
        (by intro h; simp at h) (by intro h; simp at h)
        (by intro h; have := congrArg (fun x : Fin n × Fin 2 => (x.1 : ℕ)) h; simp at this)

def W (n : ℕ) := { w : Fin n → Row // isValidWord w }
instance (n : ℕ) : Fintype (W n) := by unfold W; infer_instance

lemma a_eq_card_W {n : ℕ} (hn : 3 ≤ n) : a n = Fintype.card (W n) := by
  unfold a
  have hn0 : n ≠ 0 := by omega
  simp only [hn0, ↓reduceIte]
  rw [← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun w : W n =>
      (⟨toGrid w.1, isValid_of_isValidWord hn w.1 w.2⟩ : { A : Fin n → Fin 2 → Fin 2 // isValid n A }))
      ⟨?_, ?_⟩)
  · intro w1 w2 h
    exact Subtype.ext (toGrid_injective (congrArg Subtype.val h))
  · intro ⟨A, hA⟩
    rcases exists_isValidWord_of_isValid hn hA with ⟨w, rfl, hw⟩
    exact ⟨⟨w, hw⟩, rfl⟩

def WL (k : ℕ) := { w : W (k + 3) // w.1 ⟨k + 2, by omega⟩ = 0 }
def WR (k : ℕ) := { w : W (k + 3) // w.1 ⟨k + 2, by omega⟩ = 1 }
def WLB (k : ℕ) := { w : W (k + 3) // w.1 ⟨k + 1, by omega⟩ = 0 ∧ w.1 ⟨k + 2, by omega⟩ = 2 }
def WRB (k : ℕ) := { w : W (k + 3) // w.1 ⟨k + 1, by omega⟩ = 1 ∧ w.1 ⟨k + 2, by omega⟩ = 2 }

instance (k : ℕ) : Fintype (WL k) := by unfold WL; infer_instance
instance (k : ℕ) : Fintype (WR k) := by unfold WR; infer_instance
instance (k : ℕ) : Fintype (WLB k) := by unfold WLB; infer_instance
instance (k : ℕ) : Fintype (WRB k) := by unfold WRB; infer_instance

def initWord {n : ℕ} (w : Fin (n + 1) → Row) : Fin n → Row :=
  fun i => w ⟨i.1, by omega⟩

lemma isValidWord_init {n : ℕ} {w : Fin (n + 1) → Row} (hw : isValidWord w) :
    isValidWord (initWord w) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    exact hw.1 ⟨i.1, by omega⟩ (by dsimp; omega)
  · intro i hi hmid
    exact hw.2 ⟨i.1, by omega⟩ (by dsimp; omega) hmid

def snocWord {n : ℕ} (w : Fin n → Row) (r : Row) : Fin (n + 1) → Row :=
  fun i => if h : (i : ℕ) < n then w ⟨i.1, h⟩ else r

lemma init_snoc {n : ℕ} (w : Fin n → Row) (r : Row) :
    initWord (snocWord w r) = w := by
  funext i
  simp [initWord, snocWord, i.2]

lemma snoc_init {n : ℕ} (w : Fin (n + 1) → Row) :
    snocWord (initWord w) (w ⟨n, Nat.lt_succ_self n⟩) = w := by
  funext i
  dsimp only [snocWord, initWord]
  split_ifs with h
  · rfl
  · congr 1; exact Fin.ext (by dsimp; omega)

lemma isValidWord_snoc {n : ℕ} (hn : 2 ≤ n) {w : Fin n → Row} (hw : isValidWord w) (r : Row)
    (h1 : ¬ (w ⟨n - 1, by omega⟩ = 0 ∧ r = 1) ∧
          ¬ (w ⟨n - 1, by omega⟩ = 1 ∧ r = 0) ∧
          ¬ (w ⟨n - 1, by omega⟩ = 2 ∧ r = 2))
    (h2 : w ⟨n - 1, by omega⟩ = 2 → w ⟨n - 2, by omega⟩ ≠ r) :
    isValidWord (snocWord w r) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    by_cases hlt : (i : ℕ) + 1 < n
    · have hi' : (i : ℕ) < n := by omega
      simpa [snocWord, hi', hlt] using hw.1 ⟨i.1, hi'⟩ hlt
    · have hi_eq : (i : ℕ) = n - 1 := by omega
      have hi' : (i : ℕ) < n := by omega
      have hnot : ¬ ((i : ℕ) + 1 < n) := hlt
      have hfi : (⟨i.1, hi'⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext hi_eq
      simpa [snocWord, hi', hnot, hfi] using h1
  · intro i hi hmid
    by_cases hlt : (i : ℕ) + 2 < n
    · have hi' : (i : ℕ) < n := by omega
      have hi1 : (i : ℕ) + 1 < n := by omega
      simpa [snocWord, hi', hi1, hlt] using hw.2 ⟨i.1, hi'⟩ hlt (by simpa [snocWord, hi1] using hmid)
    · have hi_eq : (i : ℕ) = n - 2 := by omega
      have hi' : (i : ℕ) < n := by omega
      have hi1 : (i : ℕ) + 1 < n := by omega
      have hnot : ¬ ((i : ℕ) + 2 < n) := hlt
      have hfi : (⟨i.1, hi'⟩ : Fin n) = ⟨n - 2, by omega⟩ := Fin.ext hi_eq
      have hfi1 : (⟨i.1 + 1, hi1⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp; omega)
      simp only [snocWord, hi', hi1, hnot, ↓reduceDIte, hfi, hfi1] at hmid ⊢
      exact h2 hmid

lemma card_WL_succ (k : ℕ) :
    Fintype.card (WL (k + 1)) = Fintype.card (WL k) + Fintype.card (WRB k) := by
  rw [← Fintype.card_sum]
  refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
  · intro ⟨⟨w, hw⟩, hlast⟩
    dsimp only at hlast
    have hlast' : w ⟨k + 3, by omega⟩ = 0 := hlast
    have hprev : w ⟨k + 2, by omega⟩ = 0 ∨ w ⟨k + 2, by omega⟩ = 2 := by
      have h1 := (hw.1 ⟨k + 2, by omega⟩ (by dsimp; omega)).2.1
      have hne : w ⟨k + 2, by omega⟩ ≠ 1 := fun h => h1 ⟨h, hlast'⟩
      generalize ha : w ⟨k + 2, by omega⟩ = a at hne
      fin_cases a <;> simp_all
    by_cases hp0 : w ⟨k + 2, by omega⟩ = 0
    · exact Sum.inl ⟨⟨initWord w, isValidWord_init hw⟩, hp0⟩
    · have hp2 : w ⟨k + 2, by omega⟩ = 2 := by rcases hprev with h | h; exact absurd h hp0; exact h
      have hpp1 : w ⟨k + 1, by omega⟩ = 1 := by
        have hne0 := hw.2 ⟨k + 1, by omega⟩ (by dsimp; omega) hp2
        have hne2 := (hw.1 ⟨k + 1, by omega⟩ (by dsimp; omega)).2.2
        have h1 : w ⟨k + 1, by omega⟩ ≠ 0 := fun h => hne0 (h.trans hlast'.symm)
        have h2 : w ⟨k + 1, by omega⟩ ≠ 2 := fun h => hne2 ⟨h, hp2⟩
        generalize ha : w ⟨k + 1, by omega⟩ = a at h1 h2
        fin_cases a <;> simp_all
      exact Sum.inr ⟨⟨initWord w, isValidWord_init hw⟩, ⟨hpp1, hp2⟩⟩
  · rintro (⟨⟨w, hw⟩, hl⟩ | ⟨⟨w, hw⟩, ⟨hp1, hp2⟩⟩)
    · dsimp only at hl
      refine ⟨⟨snocWord w 0, isValidWord_snoc (n := k + 3) (by omega) hw 0 ?_ ?_⟩, ?_⟩
      · simp [hl]
      · simp [hl]
      · simp [snocWord]
    · dsimp only at hp1 hp2
      refine ⟨⟨snocWord w 0, isValidWord_snoc (n := k + 3) (by omega) hw 0 ?_ ?_⟩, ?_⟩
      · simp [hp2]
      · intro _; simp [hp1]
      · simp [snocWord]
  · intro ⟨⟨w, hw⟩, hlast⟩
    dsimp only at hlast ⊢
    split_ifs with hp0
    · apply Subtype.ext; apply Subtype.ext
      simpa [← hlast] using snoc_init (n := k + 3) w
    · apply Subtype.ext; apply Subtype.ext
      simpa [← hlast] using snoc_init (n := k + 3) w
  · rintro (⟨⟨w, hw⟩, hl⟩ | ⟨⟨w, hw⟩, ⟨hp1, hp2⟩⟩)
    · dsimp only at hl ⊢
      have hcond : snocWord w 0 ⟨k + 2, by omega⟩ = 0 := by simp [snocWord, hl]
      rw [dif_pos hcond]
      congr 1; apply Subtype.ext; apply Subtype.ext; exact init_snoc w 0
    · dsimp only at hp1 hp2 ⊢
      have hcond : ¬ (snocWord w 0 ⟨k + 2, by omega⟩ = 0) := by simp [snocWord, hp2]
      rw [dif_neg hcond]
      congr 1; apply Subtype.ext; apply Subtype.ext; exact init_snoc w 0

lemma card_WR_succ (k : ℕ) :
    Fintype.card (WR (k + 1)) = Fintype.card (WR k) + Fintype.card (WLB k) := by
  rw [← Fintype.card_sum]
  refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
  · intro ⟨⟨w, hw⟩, hlast⟩
    dsimp only at hlast
    have hlast' : w ⟨k + 3, by omega⟩ = 1 := hlast
    have hprev : w ⟨k + 2, by omega⟩ = 1 ∨ w ⟨k + 2, by omega⟩ = 2 := by
      have h1 := (hw.1 ⟨k + 2, by omega⟩ (by dsimp; omega)).1
      have hne : w ⟨k + 2, by omega⟩ ≠ 0 := fun h => h1 ⟨h, hlast'⟩
      generalize ha : w ⟨k + 2, by omega⟩ = a at hne
      fin_cases a <;> simp_all
    by_cases hp1 : w ⟨k + 2, by omega⟩ = 1
    · exact Sum.inl ⟨⟨initWord w, isValidWord_init hw⟩, hp1⟩
    · have hp2 : w ⟨k + 2, by omega⟩ = 2 := by rcases hprev with h | h; exact absurd h hp1; exact h
      have hpp0 : w ⟨k + 1, by omega⟩ = 0 := by
        have hne1 := hw.2 ⟨k + 1, by omega⟩ (by dsimp; omega) hp2
        have hne2 := (hw.1 ⟨k + 1, by omega⟩ (by dsimp; omega)).2.2
        have h1 : w ⟨k + 1, by omega⟩ ≠ 1 := fun h => hne1 (h.trans hlast'.symm)
        have h2 : w ⟨k + 1, by omega⟩ ≠ 2 := fun h => hne2 ⟨h, hp2⟩
        generalize ha : w ⟨k + 1, by omega⟩ = a at h1 h2
        fin_cases a <;> simp_all
      exact Sum.inr ⟨⟨initWord w, isValidWord_init hw⟩, ⟨hpp0, hp2⟩⟩
  · rintro (⟨⟨w, hw⟩, hl⟩ | ⟨⟨w, hw⟩, ⟨hp0, hp2⟩⟩)
    · dsimp only at hl
      refine ⟨⟨snocWord w 1, isValidWord_snoc (n := k + 3) (by omega) hw 1 ?_ ?_⟩, ?_⟩
      · simp [hl]
      · simp [hl]
      · simp [snocWord]
    · dsimp only at hp0 hp2
      refine ⟨⟨snocWord w 1, isValidWord_snoc (n := k + 3) (by omega) hw 1 ?_ ?_⟩, ?_⟩
      · simp [hp2]
      · intro _; simp [hp0]
      · simp [snocWord]
  · intro ⟨⟨w, hw⟩, hlast⟩
    dsimp only at hlast ⊢
    split_ifs with hp1
    · apply Subtype.ext; apply Subtype.ext
      simpa [← hlast] using snoc_init (n := k + 3) w
    · apply Subtype.ext; apply Subtype.ext
      simpa [← hlast] using snoc_init (n := k + 3) w
  · rintro (⟨⟨w, hw⟩, hl⟩ | ⟨⟨w, hw⟩, ⟨hp0, hp2⟩⟩)
    · dsimp only at hl ⊢
      have hcond : snocWord w 1 ⟨k + 2, by omega⟩ = 1 := by simp [snocWord, hl]
      rw [dif_pos hcond]
      congr 1; apply Subtype.ext; apply Subtype.ext; exact init_snoc w 1
    · dsimp only at hp0 hp2 ⊢
      have hcond : ¬ (snocWord w 1 ⟨k + 2, by omega⟩ = 1) := by simp [snocWord, hp2]
      rw [dif_neg hcond]
      congr 1; apply Subtype.ext; apply Subtype.ext; exact init_snoc w 1

lemma card_WLB_succ (k : ℕ) :
    Fintype.card (WLB (k + 1)) = Fintype.card (WL k) := by
  refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
  · intro ⟨⟨w, hw⟩, ⟨hp0, _⟩⟩
    exact ⟨⟨initWord w, isValidWord_init hw⟩, hp0⟩
  · intro ⟨⟨w, hw⟩, hl⟩
    dsimp only at hl
    refine ⟨⟨snocWord w 2, isValidWord_snoc (n := k + 3) (by omega) hw 2 ?_ ?_⟩, ?_, ?_⟩
    · simp [hl]
    · simp [hl]
    · simp [snocWord, hl]
    · simp [snocWord]
  · intro ⟨⟨w, hw⟩, ⟨_, hlast⟩⟩
    dsimp only at hlast ⊢
    apply Subtype.ext; apply Subtype.ext
    simpa [← hlast] using snoc_init (n := k + 3) w
  · intro ⟨⟨w, hw⟩, hl⟩
    apply Subtype.ext; apply Subtype.ext
    exact init_snoc w 2

lemma card_WRB_succ (k : ℕ) :
    Fintype.card (WRB (k + 1)) = Fintype.card (WR k) := by
  refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
  · intro ⟨⟨w, hw⟩, ⟨hp1, _⟩⟩
    exact ⟨⟨initWord w, isValidWord_init hw⟩, hp1⟩
  · intro ⟨⟨w, hw⟩, hl⟩
    dsimp only at hl
    refine ⟨⟨snocWord w 2, isValidWord_snoc (n := k + 3) (by omega) hw 2 ?_ ?_⟩, ?_, ?_⟩
    · simp [hl]
    · simp [hl]
    · simp [snocWord, hl]
    · simp [snocWord]
  · intro ⟨⟨w, hw⟩, ⟨_, hlast⟩⟩
    dsimp only at hlast ⊢
    apply Subtype.ext; apply Subtype.ext
    simpa [← hlast] using snoc_init (n := k + 3) w
  · intro ⟨⟨w, hw⟩, hl⟩
    apply Subtype.ext; apply Subtype.ext
    exact init_snoc w 2

lemma card_W_split (k : ℕ) :
    Fintype.card (W (k + 3)) =
      (Fintype.card (WL k) + Fintype.card (WR k)) +
      (Fintype.card (WLB k) + Fintype.card (WRB k)) := by
  rw [← Fintype.card_sum, ← Fintype.card_sum, ← Fintype.card_sum]
  refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
  · intro w
    by_cases h0 : w.1 ⟨k + 2, by omega⟩ = 0
    · exact Sum.inl (Sum.inl ⟨w, h0⟩)
    · by_cases h1 : w.1 ⟨k + 2, by omega⟩ = 1
      · exact Sum.inl (Sum.inr ⟨w, h1⟩)
      · have h2 : w.1 ⟨k + 2, by omega⟩ = 2 := by
          generalize ha : w.1 ⟨k + 2, by omega⟩ = a at h0 h1
          fin_cases a <;> simp_all
        by_cases hp0 : w.1 ⟨k + 1, by omega⟩ = 0
        · exact Sum.inr (Sum.inl ⟨w, ⟨hp0, h2⟩⟩)
        · have hp1 : w.1 ⟨k + 1, by omega⟩ = 1 := by
            have hne2 := (w.2.1 ⟨k + 1, by omega⟩ (by dsimp; omega)).2.2
            have hpne2 : w.1 ⟨k + 1, by omega⟩ ≠ 2 := fun h => hne2 ⟨h, h2⟩
            generalize ha : w.1 ⟨k + 1, by omega⟩ = a at hp0 hpne2
            fin_cases a <;> simp_all
          exact Sum.inr (Sum.inr ⟨w, ⟨hp1, h2⟩⟩)
  · rintro ((⟨w, _⟩ | ⟨w, _⟩) | (⟨w, _⟩ | ⟨w, _⟩)) <;> exact w
  · intro w
    dsimp only
    split_ifs <;> rfl
  · rintro ((⟨w, h0⟩ | ⟨w, h1⟩) | (⟨w, ⟨hp0, h2⟩⟩ | ⟨w, ⟨hp1, h2⟩⟩))
    · simp [h0]
    · simp [h1]
    · have hn0 : w.1 ⟨k + 2, by omega⟩ ≠ 0 := by simp [h2]
      have hn1 : w.1 ⟨k + 2, by omega⟩ ≠ 1 := by simp [h2]
      simp [hn0, hn1, hp0]
    · have hn0 : w.1 ⟨k + 2, by omega⟩ ≠ 0 := by simp [h2]
      have hn1 : w.1 ⟨k + 2, by omega⟩ ≠ 1 := by simp [h2]
      have hnp0 : w.1 ⟨k + 1, by omega⟩ ≠ 0 := by simp [hp1]
      simp [hn0, hn1, hnp0]

lemma card_four_fib (k : ℕ) :
    Fintype.card (WL k) = Nat.fib (k + 4) ∧
    Fintype.card (WR k) = Nat.fib (k + 4) ∧
    Fintype.card (WLB k) = Nat.fib (k + 3) ∧
    Fintype.card (WRB k) = Nat.fib (k + 3) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  | succ k ih =>
    rcases ih with ⟨hL, hR, hLB, hRB⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [card_WL_succ, hL, hRB, add_comm, ← Nat.fib_add_two]
    · rw [card_WR_succ, hR, hLB, add_comm, ← Nat.fib_add_two]
    · rw [card_WLB_succ, hL]
    · rw [card_WRB_succ, hR]

lemma a_eq_two_fib (n : ℕ) (hn : 3 ≤ n) : a n = 2 * Nat.fib (n + 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 3 k, a_eq_card_W (by omega), card_W_split]
  rcases card_four_fib k with ⟨hL, hR, hLB, hRB⟩
  rw [hL, hR, hLB, hRB]
  have hfib : Nat.fib (k + 3 + 2) = Nat.fib (k + 3) + Nat.fib (k + 4) := by
    rw [show k + 3 + 2 = (k + 3) + 2 by omega, Nat.fib_add_two]
  omega

lemma part1 : ∀ n ≥ 5, a n = a (n - 1) + a (n - 2) := by
  intro n hn
  rw [a_eq_two_fib n (by omega), a_eq_two_fib (n - 1) (by omega), a_eq_two_fib (n - 2) (by omega)]
  have h2 : n - 1 + 2 = n + 1 := by omega
  have h3 : n - 2 + 2 = n := by omega
  rw [h2, h3, Nat.fib_add_two]
  omega

lemma part2 :
    (1 - X - X ^ 2 : PowerSeries ℤ) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (1 + X) * (3 + X - X ^ 2) := by
  let F : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have hlhs : (1 - X - X ^ 2 : PowerSeries ℤ) * F =
      F - X ^ 1 * F - X ^ 2 * F := by ring
  have hrhs : (X * (1 + X) * (3 + X - X ^ 2) : PowerSeries ℤ) =
      PowerSeries.C 3 * (X ^ 1 : PowerSeries ℤ) + PowerSeries.C 4 * (X ^ 2 : PowerSeries ℤ) -
      (X ^ 4 : PowerSeries ℤ) := by
    simp only [map_ofNat]
    ring
  rw [show (1 - X - X ^ 2 : PowerSeries ℤ) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (1 - X - X ^ 2 : PowerSeries ℤ) * F from rfl, hlhs, hrhs]
  ext k
  have ha0 : (a 0 : ℤ) = 0 := by simp [a]
  have ha1 : (a 1 : ℤ) = 3 := by exact_mod_cast a_one
  have ha2 : (a 2 : ℤ) = 7 := by exact_mod_cast a_two
  have ha3 : (a 3 : ℤ) = 10 := by
    have := a_eq_two_fib 3 (by omega)
    norm_num [Nat.fib] at this
    exact_mod_cast this
  have ha4 : (a 4 : ℤ) = 16 := by
    have := a_eq_two_fib 4 (by omega)
    norm_num [Nat.fib] at this
    exact_mod_cast this
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
             PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk]
  rcases k with _ | _ | _ | _ | _ | m
  · simp [ha0]
  · simp [ha0, ha1]
  · simp [ha0, ha1, ha2]
  · simp [ha1, ha2, ha3]
  · simp [ha2, ha3, ha4]
  · have e0 : m + 1 + 1 + 1 + 1 + 1 = m + 5 := by omega
    have h1 : m + 5 - 1 = m + 4 := by omega
    have h2 : m + 5 - 2 = m + 3 := by omega
    rw [e0, h1, h2]
    have l1 : 1 ≤ m + 5 := by omega
    have l2 : 2 ≤ m + 5 := by omega
    have n1 : ¬ (m + 5 = 1) := by omega
    have n2 : ¬ (m + 5 = 2) := by omega
    have n4 : ¬ (m + 5 = 4) := by omega
    simp only [l1, l2, n1, n2, n4, ite_true, ite_false]
    have hrec : (a (m + 5) : ℤ) = (a (m + 4) : ℤ) + (a (m + 3) : ℤ) := by
      have := part1 (m + 5) (by omega)
      rw [h1, h2] at this
      exact_mod_cast this
    linarith

lemma binet_aux (n : ℕ) :
    (2 * Nat.fib (n + 2) : ℝ) =
      ((2 : ℝ) ^ (-(n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-3 + Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (3 + Real.sqrt 5))) / Real.sqrt 5 := by
  have hs5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 5 ≠ 0 := by positivity
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | m
    · norm_num [Nat.fib]
      field_simp [hne]
      ring
    · norm_num [Nat.fib]
      field_simp [hne]
      nlinarith [hs5]
    · have ih0 := ih m (by omega)
      have ih1 := ih (m + 1) (by omega)
      have hfib : (2 * Nat.fib (m + 2 + 2) : ℝ) =
          (2 * Nat.fib (m + 2) : ℝ) + (2 * Nat.fib (m + 1 + 2) : ℝ) := by
        have : Nat.fib (m + 2 + 2) = Nat.fib (m + 2) + Nat.fib (m + 1 + 2) := by
          rw [show m + 2 + 2 = (m + 2) + 2 by omega, Nat.fib_add_two]
        push_cast [this]
        ring
      rw [hfib, ih0, ih1]
      have hz1 : (2 : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(m : ℤ)) / 2 := by
        rw [Nat.cast_add, Nat.cast_one, neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num; ring
      have hz2 : (2 : ℝ) ^ (-((m + 2 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(m : ℤ)) / 4 := by
        rw [Nat.cast_add, Nat.cast_ofNat, neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num; ring
      rw [hz1, hz2]
      have hp1 : (1 - Real.sqrt 5) ^ (m + 2) = (1 - Real.sqrt 5) ^ m * (6 - 2 * Real.sqrt 5) := by
        rw [pow_add]; congr 1; ring_nf; linarith [hs5]
      have hp2 : (1 + Real.sqrt 5) ^ (m + 2) = (1 + Real.sqrt 5) ^ m * (6 + 2 * Real.sqrt 5) := by
        rw [pow_add]; congr 1; ring_nf; linarith [hs5]
      have hp1' : (1 - Real.sqrt 5) ^ (m + 1) = (1 - Real.sqrt 5) ^ m * (1 - Real.sqrt 5) := pow_succ _ _
      have hp2' : (1 + Real.sqrt 5) ^ (m + 1) = (1 + Real.sqrt 5) ^ m * (1 + Real.sqrt 5) := pow_succ _ _
      rw [hp1, hp2, hp1', hp2']
      field_simp [hne]
      ring

lemma part3 :
    ∀ n > 2, (a n : ℝ) =
      ((2 : ℝ) ^ (-(n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-3 + Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (3 + Real.sqrt 5))) / Real.sqrt 5 := by
  intro n hn
  have ha : (a n : ℝ) = (2 * Nat.fib (n + 2) : ℝ) := by
    exact_mod_cast a_eq_two_fib n (by omega)
  rw [ha]
  exact binet_aux n

end A163714Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a163714.main :=
  ⟨A163714Proof.part1, A163714Proof.part2, A163714Proof.part3⟩
