import OMAReductions.R_Erdos848_erdos_848_R3_H3_R1_H1_R1
import Mathlib
/- Adapted from MacchaCat/erdos848, 99b8d9bf40fdd090a2a117328c5707ca21ec748e, Apache-2.0. Prime summation cutoff: 10000. Finite interval [160000000, 1618722525]: prime counts above the cutoff are certified by a verified segmented bit sieve. -/
section

/-
# Erdős Problem #848 — basic definitions and elementary facts

Problem (Erdős–Sárközy): if `A ⊆ {1,…,N}` and `a*b+1` is never squarefree for `a, b ∈ A`
(`a = b` allowed), is `|A|` at most the number of `n ≤ N` with `n ≡ 7 (mod 25)`?
-/

namespace Erdos848

/-- `A` is *admissible*: `a*b+1` is not squarefree for all `a, b ∈ A` (including `a = b`). -/
def Admissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)

/-- `c7 N = #{n ∈ [1,N] : n ≡ 7 (mod 25)}` in closed form (see `c7_eq_card`). -/
def c7 (N : ℕ) : ℕ := (N + 18) / 25

/-- The extremal example `{n ∈ [1,N] : n ≡ 7 (mod 25)}`. -/
def C7set (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun n => n % 25 = 7)

/-- The statement of Erdős #848 for a given `N`. -/
def Statement (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → Admissible A → A.card ≤ c7 N

lemma not_squarefree_of_mul_self_dvd {n p : ℕ} (hp : 2 ≤ p) (h : p * p ∣ n) :
    ¬ Squarefree n := by
  intro hs
  have hu := hs p h
  rw [Nat.isUnit_iff] at hu
  omega

lemma C7set_card (N : ℕ) : (C7set N).card = c7 N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
    unfold C7set at ih ⊢
    rw [hIcc, Finset.filter_insert]
    unfold c7 at ih ⊢
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

/-- The class `7 mod 25` is admissible: `25 ∣ a*b+1`. -/
theorem C7set_admissible (N : ℕ) : Admissible (C7set N) := by
  intro a ha b hb
  simp only [C7set, Finset.mem_filter] at ha hb
  apply not_squarefree_of_mul_self_dvd (p := 5) (by norm_num)
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, Nat.mul_mod, ha.2, hb.2]

/-- Lower bound: the answer is at least `c7 N`. -/
theorem lower_bound (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Admissible A ∧ A.card = c7 N :=
  ⟨C7set N, Finset.filter_subset _ _, C7set_admissible N, C7set_card N⟩

/-- A proper colouring with `k` colours of the "compatibility graph" bounds admissible sets. -/
theorem card_le_of_coloring {A : Finset ℕ} {k : ℕ} (f : ℕ → ℕ) (hA : Admissible A)
    (hf : ∀ a ∈ A, f a < k)
    (hcol : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → f a = f b → Squarefree (a * b + 1)) :
    A.card ≤ k := by
  have hinj : Set.InjOn f A := by
    intro a ha b hb hab
    by_contra hne
    exact hA a ha b hb (hcol a ha b hb hne hab)
  calc A.card = (A.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range k).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        simpa using hf a ha
    _ = k := Finset.card_range k

/- ### Elementary congruence facts (F1–F4 of the written proof) -/

lemma mod_mul_add_one (a b m : ℕ) : (a * b + 1) % m = ((a % m) * (b % m) + 1) % m := by
  rw [Nat.add_mod, Nat.mul_mod]; conv_rhs => rw [Nat.add_mod]

/-- (F1) `25 ∣ x² + 1 ↔ x ≡ ±7 (mod 25)`. -/
lemma F1 (x : ℕ) : 25 ∣ x * x + 1 ↔ x % 25 = 7 ∨ x % 25 = 18 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one]
  have h := Nat.mod_lt x (by norm_num : 25 > 0)
  interval_cases (x % 25) <;> simp

/-- (F2, first half) if `a ≡ 7` then `25 ∣ ab+1 ↔ b ≡ 7 (mod 25)`. -/
lemma F2_seven (a b : ℕ) (ha : a % 25 = 7) : 25 ∣ a * b + 1 ↔ b % 25 = 7 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one, ha]
  have h := Nat.mod_lt b (by norm_num : 25 > 0)
  interval_cases (b % 25) <;> simp

/-- (F2, second half) if `a ≡ 18` then `25 ∣ ab+1 ↔ b ≡ 18 (mod 25)`. -/
lemma F2_eighteen (a b : ℕ) (ha : a % 25 = 18) : 25 ∣ a * b + 1 ↔ b % 25 = 18 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one, ha]
  have h := Nat.mod_lt b (by norm_num : 25 > 0)
  interval_cases (b % 25) <;> simp

/-- (F3) `a ≡ 7`, `b ≡ 18 (mod 25)` ⟹ `25 ∤ ab+1`. -/
lemma F3 (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 18) : ¬ 25 ∣ a * b + 1 := by
  rw [F2_seven a b ha, hb]; norm_num

/-- (F4) for odd `a, b`: `4 ∣ ab+1 ↔ a ≢ b (mod 4)`. -/
lemma F4 (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) : 4 ∣ a * b + 1 ↔ a % 4 ≠ b % 4 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one]
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  rcases ha4 with h1 | h1 <;> rcases hb4 with h2 | h2 <;> simp [h1, h2]

/-- (F4') if `a` or `b` is even then `ab+1` is odd, so `2 ∤ ab+1`. -/
lemma F4_even (a b : ℕ) (h : a % 2 = 0 ∨ b % 2 = 0) : ¬ 2 ∣ a * b + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one]
  rcases h with h | h <;> simp [h]

/-- Every element of an admissible set lies in `V = {n : n² + 1 not squarefree}`. -/
lemma mem_V_of_admissible {A : Finset ℕ} (hA : Admissible A) {a : ℕ} (ha : a ∈ A) :
    ¬ Squarefree (a * a + 1) := hA a ha a ha

end Erdos848
end

section

/-
# The combinatorial skeleton of the analytic part

For an admissible `A ⊆ [1,N]` we split `A = A₇ ∪ A₁₈ ∪ A*` and run the case analysis of
`proof.md` §5.  Every part of `A` is bounded by a *count* of integers in `[1,N]` — either a whole
residue class, or the integers `a` with `a·b+1` not squarefree for a witness `b ∈ A`, or the
integers `x` with `x²+1` not squarefree.  The theorem `statement_of_bounds` shows:

  if these explicit counts satisfy the inequalities collected in `CountBounds N`,
  then `Statement N` holds.

So the analytic part reduces to purely number-theoretic counting inequalities (`CountBounds N`),
with all combinatorial reasoning formalised here.
-/

namespace Erdos848

open Finset

/-- `a ∈ A*`-type residue: `a ≢ 7, 18 (mod 25)`. -/
def IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18

instance : DecidablePred IsStar := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Integers `a ∈ [1,N]` with property `P` and `a·b+1` not squarefree. -/
def badCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (b : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1))).card

/-- Integers `a ∈ [1,N]` with property `P`. -/
def classCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℕ := ((Icc 1 N).filter P).card

/-- Integers `x ∈ [1,N]` with property `P` and `x²+1` not squarefree. -/
def vCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℕ :=
  ((Icc 1 N).filter (fun x => P x ∧ ¬ Squarefree (x * x + 1))).card

/-- Lemma C set: `x ∈ [1,N]`, `x ≢ ±7 (25)`, `x²+1` and `x·b+1` both not squarefree. -/
def lemCCount (N b : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun x => IsStar x ∧ ¬ Squarefree (x * x + 1) ∧ ¬ Squarefree (x * b + 1))).card

/-- A witness: an element of `[1,N]` lying in `V` (its square plus one is not squarefree). -/
def Witness (N b : ℕ) : Prop := 1 ≤ b ∧ b ≤ N ∧ ¬ Squarefree (b * b + 1)

/-- The counting inequalities of the case analysis (`proof.md` §5), one per case. -/
structure CountBounds (N : ℕ) : Prop where
  /-- I.b: witnesses `b ∈ A₇` (sieves `A₁₈`) and `b' ∈ A₁₈` (sieves `A₇`). -/
  caseIb : ∀ b b', Witness N b → b % 25 = 7 → Witness N b' → b' % 25 = 18 →
    badCount N (fun a => a % 25 = 18) b + badCount N (fun a => a % 25 = 7) b' ≤ c7 N
  /-- II: an even witness `b ∈ A*` sieves `A₇ ∪ A₁₈`; Lemma C bounds `A*`. -/
  caseII : ∀ b, Witness N b → IsStar b → b % 2 = 0 →
    badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount N b ≤ c7 N
  /-- III.1: odd witnesses `b₁ ≡ 1`, `b₃ ≡ 3 (mod 4)` in `A*`; `A*` odd. -/
  caseIII1 : ∀ b₁ b₃, Witness N b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness N b₃ → IsStar b₃ → b₃ % 4 = 3 →
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
    vCount N (fun x => IsStar x ∧ x % 2 = 1) ≤ c7 N
  /-- III.2.a: `A* ⊆ {≡ r (mod 4)}` (r = 1 or 3, s = 4 - r), `A₇ ∪ A₁₈` odd. -/
  caseIII2a : ∀ b r, Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
    vCount N (fun x => IsStar x ∧ x % 4 = r) ≤ c7 N
  /-- III.2.b (even witness in `A₇`): `A* ⊆ {≡ r (mod 4)}`, even `b' ∈ A₇`. -/
  caseIII2b7 : ∀ b b' r, Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness N b' → b' % 25 = 7 → b' % 2 = 0 →
    classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
    badCount N (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount N (fun a => a % 25 = 18) b' +
    vCount N (fun x => IsStar x ∧ x % 4 = r) ≤ c7 N
  /-- III.2.b (even witness in `A₁₈`). -/
  caseIII2b18 : ∀ b b' r, Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness N b' → b' % 25 = 18 → b' % 2 = 0 →
    classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
    badCount N (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount N (fun a => a % 25 = 7) b' +
    vCount N (fun x => IsStar x ∧ x % 4 = r) ≤ c7 N

/- ### Basic counting tools -/

lemma card_le_two {A : Finset ℕ} (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ a ∈ A, P a ∨ Q a) : A.card ≤ (A.filter P).card + (A.filter Q).card := by
  calc A.card ≤ (A.filter P ∪ A.filter Q).card := by
        apply card_le_card; intro a ha
        rcases h a ha with hp | hq
        · exact mem_union_left _ (mem_filter.mpr ⟨ha, hp⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨ha, hq⟩)
    _ ≤ _ := card_union_le _ _

variable {N : ℕ} {A : Finset ℕ}

lemma filter_le_bad (hA : Admissible A) (hsub : A ⊆ Icc 1 N) {b : ℕ} (hb : b ∈ A)
    (P : ℕ → Prop) [DecidablePred P] : (A.filter P).card ≤ badCount N P b := by
  apply card_le_card; intro a ha
  rw [mem_filter] at ha
  exact mem_filter.mpr ⟨hsub ha.1, ha.2, hA a ha.1 b hb⟩

lemma filter_le_class (hsub : A ⊆ Icc 1 N) (P : ℕ → Prop) [DecidablePred P] :
    (A.filter P).card ≤ classCount N P := by
  apply card_le_card; intro a ha
  rw [mem_filter] at ha
  exact mem_filter.mpr ⟨hsub ha.1, ha.2⟩

lemma filter_le_v (hA : Admissible A) (hsub : A ⊆ Icc 1 N) (P : ℕ → Prop) [DecidablePred P] :
    (A.filter P).card ≤ vCount N P := by
  apply card_le_card; intro a ha
  rw [mem_filter] at ha
  exact mem_filter.mpr ⟨hsub ha.1, ha.2, hA a ha.1 a ha.1⟩

lemma witness_of_mem (hA : Admissible A) (hsub : A ⊆ Icc 1 N) {b : ℕ} (hb : b ∈ A) :
    Witness N b := by
  have := mem_Icc.mp (hsub hb)
  exact ⟨this.1, this.2, hA b hb b hb⟩

/-- The class `18 mod 25` is never larger than the class `7 mod 25` in `[1,N]`. -/
lemma class18_le_c7 : classCount N (fun a => a % 25 = 18) ≤ c7 N := by
  rw [← C7set_card]
  unfold classCount C7set
  apply card_le_card_of_injOn (fun a => a - 11)
  · intro a ha
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha ⊢
    refine ⟨⟨by omega, by omega⟩, by omega⟩
  · intro a ha a' ha' h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha ha'
    simp only at h
    omega

lemma class7_eq_c7 : classCount N (fun a => a % 25 = 7) = c7 N := C7set_card N

/- ### The case analysis -/

theorem statement_of_bounds (h : CountBounds N) : Statement N := by
  classical
  intro A hsub hA
  -- the three parts
  have hsplit : A.card ≤ (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card +
      (A.filter IsStar).card :=
    card_le_two _ _ (fun a _ => by unfold IsStar; omega)
  by_cases hII : ∃ b ∈ A, IsStar b ∧ b % 2 = 0
  · -- Case II
    obtain ⟨b, hb, hbs, hbe⟩ := hII
    have h1 := filter_le_bad hA hsub hb (fun a => a % 25 = 7 ∨ a % 25 = 18)
    have h2 : (A.filter IsStar).card ≤ lemCCount N b := by
      apply card_le_card; intro x hx
      rw [mem_filter] at hx
      exact mem_filter.mpr ⟨hsub hx.1, hx.2, hA x hx.1 x hx.1, hA x hx.1 b hb⟩
    have := h.caseII b (witness_of_mem hA hsub hb) hbs hbe
    omega
  push Not at hII
  -- from here on every element of A* is odd
  have hodd : ∀ x ∈ A, IsStar x → x % 2 = 1 := fun x hx hs => by
    have := hII x hx hs; omega
  by_cases hIII1 : ∃ b₁ ∈ A, ∃ b₃ ∈ A, IsStar b₁ ∧ b₁ % 4 = 1 ∧ IsStar b₃ ∧ b₃ % 4 = 3
  · -- Case III.1
    obtain ⟨b₁, hb₁, b₃, hb₃, hs₁, hr₁, hs₃, hr₃⟩ := hIII1
    have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
        badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
        badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ := by
      have := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
        (fun a => a % 4 = 1 ∨ a % 2 = 0) (fun a => a % 4 = 3) (fun a _ => by omega)
      rw [filter_filter, filter_filter] at this
      have e1 := filter_le_bad hA hsub hb₁ (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0))
      have e2 := filter_le_bad hA hsub hb₃ (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3)
      omega
    have hS : (A.filter IsStar).card ≤ vCount N (fun x => IsStar x ∧ x % 2 = 1) := by
      calc (A.filter IsStar).card = (A.filter (fun x => IsStar x ∧ x % 2 = 1)).card := by
            congr 1; apply filter_congr; intro x hx
            exact ⟨fun hs => ⟨hs, hodd x hx hs⟩, fun h => h.1⟩
        _ ≤ _ := filter_le_v hA hsub _
    have := h.caseIII1 b₁ b₃ (witness_of_mem hA hsub hb₁) hs₁ hr₁ (witness_of_mem hA hsub hb₃) hs₃ hr₃
    omega
  push Not at hIII1
  by_cases hStar : ∃ b ∈ A, IsStar b
  · -- Case III.2: all of A* lies in the residue class r = b mod 4
    obtain ⟨b, hb, hbs⟩ := hStar
    set r := b % 4 with hr
    have hr13 : r = 1 ∨ r = 3 := by have := hodd b hb hbs; omega
    have hAllr : ∀ x ∈ A, IsStar x → x % 4 = r := by
      intro x hx hxs
      have hxo := hodd x hx hxs
      rcases hr13 with h1 | h3
      · by_contra hne
        exact hIII1 b hb x hx hbs (by omega) hxs (by omega)
      · by_contra hne
        exact hIII1 x hx b hb hxs (by omega) hbs (by omega)
    have hS : (A.filter IsStar).card ≤ vCount N (fun x => IsStar x ∧ x % 4 = r) := by
      calc (A.filter IsStar).card = (A.filter (fun x => IsStar x ∧ x % 4 = r)).card := by
            congr 1; apply filter_congr; intro x hx
            exact ⟨fun hs => ⟨hs, hAllr x hx hs⟩, fun h => h.1⟩
        _ ≤ _ := filter_le_v hA hsub _
    have hwb := witness_of_mem hA hsub hb
    by_cases hEven : ∃ b' ∈ A, (b' % 25 = 7 ∨ b' % 25 = 18) ∧ b' % 2 = 0
    · obtain ⟨b', hb', h78, hbe'⟩ := hEven
      have hwb' := witness_of_mem hA hsub hb'
      rcases h78 with h7 | h18
      · -- III.2.b, even witness in A₇
        have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
            classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
            badCount N (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
            badCount N (fun a => a % 25 = 18) b' := by
          have c1 := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
            (fun a => a % 25 = 7) (fun a => a % 25 = 18) (fun a ha => (mem_filter.mp ha).2)
          have c2 := card_le_two (A := (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).filter (fun a => a % 25 = 7))
            (fun a => a % 4 = 4 - r) (fun a => a % 4 = r ∨ a % 2 = 0) (fun a _ => by omega)
          simp only [filter_filter] at c1 c2
          have e1 := filter_le_class hsub (fun a => a % 25 = 7 ∧ a % 4 = 4 - r)
          have e2 := filter_le_bad hA hsub hb (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0))
          have e3 := filter_le_bad hA hsub hb' (fun a => a % 25 = 18)
          have s1 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7) ∧ a % 4 = 4 - r)).card ≤
              (A.filter fun a => a % 25 = 7 ∧ a % 4 = 4 - r).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s2 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7) ∧ (a % 4 = r ∨ a % 2 = 0))).card ≤
              (A.filter fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s3 : ((A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18)).card ≤
              (A.filter fun a => a % 25 = 18).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
          omega
        have := h.caseIII2b7 b b' r hwb hbs rfl hr13 hwb' h7 hbe'
        omega
      · -- III.2.b, even witness in A₁₈
        have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
            classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
            badCount N (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
            badCount N (fun a => a % 25 = 7) b' := by
          have c1 := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
            (fun a => a % 25 = 18) (fun a => a % 25 = 7) (fun a ha => (mem_filter.mp ha).2.symm)
          have c2 := card_le_two (A := (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).filter (fun a => a % 25 = 18))
            (fun a => a % 4 = 4 - r) (fun a => a % 4 = r ∨ a % 2 = 0) (fun a _ => by omega)
          simp only [filter_filter] at c1 c2
          have e1 := filter_le_class hsub (fun a => a % 25 = 18 ∧ a % 4 = 4 - r)
          have e2 := filter_le_bad hA hsub hb (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0))
          have e3 := filter_le_bad hA hsub hb' (fun a => a % 25 = 7)
          have s1 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18) ∧ a % 4 = 4 - r)).card ≤
              (A.filter fun a => a % 25 = 18 ∧ a % 4 = 4 - r).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s2 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18) ∧ (a % 4 = r ∨ a % 2 = 0))).card ≤
              (A.filter fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s3 : ((A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7)).card ≤
              (A.filter fun a => a % 25 = 7).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
          omega
        have := h.caseIII2b18 b b' r hwb hbs rfl hr13 hwb' h18 hbe'
        omega
    · -- III.2.a: A₇ ∪ A₁₈ all odd
      push Not at hEven
      have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
          classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
          badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b := by
        have c := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
          (fun a => a % 4 = 4 - r) (fun a => a % 4 = r) (fun a ha => by
            have ha' := mem_filter.mp ha
            have := hEven a ha'.1 ha'.2
            omega)
        simp only [filter_filter] at c
        have e1 := filter_le_class hsub (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r)
        have e2 := filter_le_bad hA hsub hb (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r)
        omega
      have := h.caseIII2a b r hwb hbs rfl hr13
      omega
  · -- Case I: A* = ∅
    push Not at hStar
    have hS0 : (A.filter IsStar).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => hStar x hx
    have h78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
        (A.filter (fun a => a % 25 = 7)).card + (A.filter (fun a => a % 25 = 18)).card := by
      have c := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
        (fun a => a % 25 = 7) (fun a => a % 25 = 18) (fun a ha => (mem_filter.mp ha).2)
      simp only [filter_filter] at c
      have s1 : (A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7).card ≤ (A.filter fun a => a % 25 = 7).card :=
        card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
      have s2 : (A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18).card ≤ (A.filter fun a => a % 25 = 18).card :=
        card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
      omega
    by_cases h7 : ∃ b ∈ A, b % 25 = 7
    · by_cases h18 : ∃ b' ∈ A, b' % 25 = 18
      · -- I.b
        obtain ⟨b, hb, hb7⟩ := h7
        obtain ⟨b', hb', hb18⟩ := h18
        have e1 := filter_le_bad hA hsub hb (fun a => a % 25 = 18)
        have e2 := filter_le_bad hA hsub hb' (fun a => a % 25 = 7)
        have := h.caseIb b b' (witness_of_mem hA hsub hb) hb7 (witness_of_mem hA hsub hb') hb18
        omega
      · -- I.a with A₁₈ = ∅
        push Not at h18
        have h0 : (A.filter (fun a => a % 25 = 18)).card = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => h18 x hx
        have e := filter_le_class hsub (fun a => a % 25 = 7)
        rw [class7_eq_c7] at e
        omega
    · -- I.a with A₇ = ∅
      push Not at h7
      have h0 : (A.filter (fun a => a % 25 = 7)).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => h7 x hx
      have e := filter_le_class hsub (fun a => a % 25 = 18)
      have := class18_le_c7 (N := N)
      omega

end Erdos848
end

section

/-
# Phase 2: elementary counting lemmas

* `card_mod_eq_le`: a residue class mod `Q` has at most `N / Q + 1` elements in `[1,N]`.
* `exists_prime_sq_dvd`: a positive non-squarefree number has a prime square divisor.
* `prime_sq_dvd_mul_add_one_iff` (fact F5): for a prime `p ∤ b`, `p² ∣ ab+1` iff `a` lies in one
  fixed residue class mod `p²`.
* `badCount_le_sum`: `badCount` is bounded by a sum over primes of single-class counts.
-/

namespace Erdos848

open Finset

/-- A residue class mod `Q` meets `[1,N]` in at most `N / Q + 1` points. -/
lemma card_mod_eq_le (N Q r : ℕ) :
    ((Icc 1 N).filter (fun a => a % Q = r)).card ≤ N / Q + 1 := by
  -- the map a ↦ a / Q is injective on the class and lands in [0, N / Q]
  calc ((Icc 1 N).filter (fun a => a % Q = r)).card
      ≤ (range (N / Q + 1)).card := by
        apply card_le_card_of_injOn (fun a => a / Q)
        · intro a ha
          simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha
          simp only [coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right ha.1.2)
        · intro a ha a' ha' h
          simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha ha'
          simp only at h
          rw [← Nat.div_add_mod a Q, ← Nat.div_add_mod a' Q, h, ha.2, ha'.2]
    _ = N / Q + 1 := card_range _

/-- A positive integer that is not squarefree has a prime square divisor. -/
lemma exists_prime_sq_dvd {n : ℕ} (h : ¬ Squarefree n) : ∃ p, p.Prime ∧ p * p ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at h
  push Not at h
  obtain ⟨p, hp, hd⟩ := h
  exact ⟨p, hp, hd⟩

/-- If a prime divides `b`, its square cannot divide `ab + 1`. -/
lemma not_sq_dvd_of_dvd {p a b : ℕ} (hp : p.Prime) (hpb : p ∣ b) : ¬ p * p ∣ a * b + 1 := by
  intro h
  have h1 : p ∣ a * b + 1 := dvd_trans (Dvd.intro p rfl) h
  have h2 : p ∣ a * b := dvd_mul_of_dvd_right hpb a
  have : p ∣ 1 := (Nat.dvd_add_right h2).mp h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- (F5) For a prime `p ∤ b` there is a residue `c < p²` with
`p² ∣ ab+1 ↔ a ≡ c (mod p²)`. -/
lemma prime_sq_dvd_mul_add_one_iff {p b : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) :
    ∃ c < p * p, ∀ a, p * p ∣ a * b + 1 ↔ a % (p * p) = c := by
  have hpp : 0 < p * p := Nat.mul_pos hp.pos hp.pos
  have hcop : Nat.Coprime b (p * p) :=
    Nat.Coprime.mul_right ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)))
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)))
  -- let u be the inverse of b mod p²; c = (p² - 1) * u mod p²  (i.e. -b⁻¹)
  set u := ((ZMod.unitOfCoprime b hcop)⁻¹ : (ZMod (p * p))ˣ)
  set c := ((-(u : ZMod (p * p))).val) with hc
  have : NeZero (p * p) := ⟨hpp.ne'⟩
  refine ⟨c, ZMod.val_lt _, fun a => ?_⟩
  have hb : ((b : ZMod (p * p)) * (u : ZMod (p * p))) = 1 := by
    have := Units.mul_inv (ZMod.unitOfCoprime b hcop)
    simp [u, ZMod.coe_unitOfCoprime] at this ⊢
  rw [← ZMod.natCast_eq_zero_iff]   -- p² ∣ ab+1 ↔ (ab+1 : ZMod p²) = 0
  constructor
  · intro h
    have h' : ((a : ZMod (p * p)) * b + 1) = 0 := by exact_mod_cast h
    have : (a : ZMod (p * p)) = -(u : ZMod (p * p)) := by
      have := congrArg (· * (u : ZMod (p * p))) h'
      simp only [add_mul, zero_mul, one_mul, mul_assoc, hb, mul_one] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [hc, ← this, ZMod.val_natCast]
  · intro h
    have : (a : ZMod (p * p)) = -(u : ZMod (p * p)) := by
      rw [← ZMod.natCast_mod a (p * p), h, hc, ZMod.natCast_zmod_val]
    push_cast
    rw [this, neg_mul, mul_comm (u : ZMod (p * p)) (b : ZMod (p * p)), hb, neg_add_cancel]

/-- Union bound: if every `a` counted by `badCount` (with `a ≤ N`) has a prime square divisor of
`ab+1` with `p ∈ S`, then `badCount` is at most the sum over `S` of the per-prime counts. -/
lemma badCount_le_sum (N b : ℕ) (P : ℕ → Prop) [DecidablePred P] (S : Finset ℕ)
    (hS : ∀ p, p.Prime → ¬ p ∣ b → p * p ≤ N * b + 1 → p ∈ S) :
    badCount N P b ≤ ∑ p ∈ S, ((Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1)).card := by
  unfold badCount
  calc ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1))).card
      ≤ (S.biUnion (fun p => (Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1))).card := by
        apply card_le_card
        intro a ha
        simp only [mem_filter, mem_Icc] at ha
        obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd ha.2.2
        have hpb : ¬ p ∣ b := fun h => not_sq_dvd_of_dvd hp h hd
        have hle : p * p ≤ N * b + 1 := by
          have := Nat.le_of_dvd (Nat.succ_pos _) hd
          have : a * b ≤ N * b := Nat.mul_le_mul_right b ha.1.2
          omega
        simp only [mem_biUnion, mem_filter, mem_Icc]
        exact ⟨p, hS p hp hpb hle, ⟨ha.1, ha.2.1, hd⟩⟩
    _ ≤ _ := card_biUnion_le

/-- Each per-prime term is a single residue class (for `p ∤ b`), hence `≤ N / p² + 1`. -/
lemma card_sq_dvd_le (N b : ℕ) (P : ℕ → Prop) [DecidablePred P] {p : ℕ} (hp : p.Prime)
    (hpb : ¬ p ∣ b) :
    ((Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1)).card ≤ N / (p * p) + 1 := by
  obtain ⟨c, -, hc⟩ := prime_sq_dvd_mul_add_one_iff hp hpb
  calc ((Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1)).card
      ≤ ((Icc 1 N).filter (fun a => a % (p * p) = c)).card := by
        apply card_le_card; intro a ha
        simp only [mem_filter] at ha ⊢
        exact ⟨ha.1, (hc a).mp ha.2.2⟩
    _ ≤ N / (p * p) + 1 := card_mod_eq_le N (p * p) c

end Erdos848
end

section

/-
# Phase 3: inclusion–exclusion for small primes

Step 1: a residue class mod `Q` has between `N/Q - 1` and `N/Q + 1` elements in `[1,N]`;
a union of `K` residue classes has between `K·N/Q - K` and `K·N/Q + K` elements.
-/

namespace Erdos848

open Finset

/-- A residue class mod `Q` (with `r < Q`) has at least `⌊N/Q⌋` elements in `[1,N]`. -/
lemma card_mod_eq_ge (N Q r : ℕ) (hQ : 0 < Q) (hr : r < Q) :
    N / Q ≤ ((Icc 1 N).filter (fun a => a % Q = r)).card := by
  -- block i ↦ the element of (iQ, iQ+Q] congruent to r
  let f : ℕ → ℕ := fun i => if r = 0 then (i + 1) * Q else i * Q + r
  calc N / Q = (range (N / Q)).card := (card_range _).symm
    _ ≤ ((Icc 1 N).filter (fun a => a % Q = r)).card := by
      apply card_le_card_of_injOn f
      · intro i hi
        simp only [coe_range, Set.mem_Iio] at hi
        have hiQ : (i + 1) * Q ≤ N := by
          have := (Nat.lt_div_iff_mul_lt hQ).mp hi
          calc (i + 1) * Q ≤ N / Q * Q := Nat.mul_le_mul_right Q hi
            _ ≤ N := Nat.div_mul_le_self N Q
        simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc, f]
        split_ifs with h0
        · refine ⟨⟨by nlinarith, hiQ⟩, ?_⟩
          rw [h0]; exact Nat.mul_mod_left _ _
        · refine ⟨⟨by omega, by nlinarith⟩, ?_⟩
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      · intro i _ j _ hij
        simp only [f] at hij
        split_ifs at hij with h0
        · exact Nat.succ_injective (Nat.eq_of_mul_eq_mul_right hQ hij)
        · have : i * Q = j * Q := by omega
          exact Nat.eq_of_mul_eq_mul_right hQ this

/-- Real-valued two-sided bound for a residue class. -/
lemma card_mod_eq_real (N Q r : ℕ) (hQ : 0 < Q) (hr : r < Q) :
    |(((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) - (N : ℝ) / Q| ≤ 1 := by
  have h1 := card_mod_eq_le N Q r
  have h2 := card_mod_eq_ge N Q r hQ hr
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have e1 : ((N / Q : ℕ) : ℝ) ≤ (N : ℝ) / Q := Nat.cast_div_le
  have e2 : (N : ℝ) / Q < ((N / Q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hQ']
    have := Nat.lt_div_mul_add hQ (a := N)
    exact_mod_cast (by nlinarith [Nat.div_add_mod N Q, Nat.mod_lt N hQ] : N < (N / Q + 1) * Q)
  rw [abs_le]
  constructor
  · have : ((N / Q : ℕ) : ℝ) ≤ (((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) := by exact_mod_cast h2
    linarith
  · have : (((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) ≤ ((N / Q : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith

/-- A union of residue classes `D ⊆ [0,Q)` meets `[1,N]` in `|D|·N/Q ± |D|` points. -/
lemma card_mod_mem_real (N Q : ℕ) (hQ : 0 < Q) (D : Finset ℕ) (hD : ∀ r ∈ D, r < Q) :
    |(((Icc 1 N).filter (fun a => a % Q ∈ D)).card : ℝ) - D.card * ((N : ℝ) / Q)| ≤ D.card := by
  have hsplit : ((Icc 1 N).filter (fun a => a % Q ∈ D)).card =
      ∑ r ∈ D, ((Icc 1 N).filter (fun a => a % Q = r)).card := by
    rw [← card_biUnion]
    · congr 1; ext a; simp only [mem_filter, mem_biUnion]
      constructor
      · rintro ⟨ha, hD'⟩; exact ⟨a % Q, hD', ha, rfl⟩
      · rintro ⟨r, hr, ha, rfl⟩; exact ⟨ha, hr⟩
    · intro r _ s _ hrs
      rw [Function.onFun, disjoint_left]
      intro a ha hb
      simp only [mem_filter] at ha hb
      exact hrs (ha.2.symm.trans hb.2)
  rw [hsplit]
  push_cast
  calc |∑ r ∈ D, ((((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ)) - D.card * ((N : ℝ) / Q)|
      = |∑ r ∈ D, ((((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) - (N : ℝ) / Q)| := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ ≤ ∑ r ∈ D, |((((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) - (N : ℝ) / Q)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ D, (1 : ℝ) := sum_le_sum (fun r hr => card_mod_eq_real N Q r hQ (hD r hr))
    _ = D.card := by simp

/- ### Step 2: counting residues by CRT -/

section CRT
variable (q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ)

/-- The combined modulus `q · ∏_{p ∈ T} m p`. -/
def bigMod (T : Finset ℕ) : ℕ := q * ∏ p ∈ T, m p

/-- Residues mod `bigMod T` satisfying all the conditions. -/
def resSet (T : Finset ℕ) : Finset ℕ :=
  (range (bigMod q m T)).filter (fun r => r % q = t ∧ ∀ p ∈ T, r % m p ∈ Rs p)

variable {q t m Rs}

lemma mod_bigMod_mod_q (T : Finset ℕ) (a : ℕ) : a % bigMod q m T % q = a % q :=
  Nat.mod_mod_of_dvd a (dvd_mul_right q _)

lemma mod_bigMod_mod_m {T : Finset ℕ} {p : ℕ} (hp : p ∈ T) (a : ℕ) :
    a % bigMod q m T % m p = a % m p :=
  Nat.mod_mod_of_dvd a (dvd_mul_of_dvd_right (dvd_prod_of_mem m hp) q)

/-- The conditions only depend on `a mod bigMod T`. -/
lemma cond_iff_resSet (T : Finset ℕ) (hq : 0 < q) (hm : ∀ p ∈ T, 0 < m p) (a : ℕ) :
    (a % q = t ∧ ∀ p ∈ T, a % m p ∈ Rs p) ↔ a % bigMod q m T ∈ resSet q t m Rs T := by
  have hpos : 0 < bigMod q m T := Nat.mul_pos hq (prod_pos (fun p hp => hm p hp))
  simp only [resSet, mem_filter, mem_range, Nat.mod_lt _ hpos, true_and, mod_bigMod_mod_q]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun p hp => by rw [mod_bigMod_mod_m hp]; exact h2 p hp⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun p hp => by have := h2 p hp; rwa [mod_bigMod_mod_m hp] at this⟩

/-- **CRT count.** If the moduli `m p` (`p ∈ T`) are pairwise coprime and coprime to `q`, `t < q`
and `Rs p ⊆ [0, m p)`, then there are exactly `∏ |Rs p|` admissible residues. -/
theorem card_resSet (T : Finset ℕ) (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ T, 0 < m p) (hR : ∀ p ∈ T, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ T, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ T, ∀ p' ∈ T, p ≠ p' → Nat.Coprime (m p) (m p')) :
    (resSet q t m Rs T).card = ∏ p ∈ T, (Rs p).card := by
  induction T using Finset.induction_on with
  | empty =>
    have : resSet q t m Rs ∅ = {t} := by
      ext r
      simp only [resSet, bigMod, prod_empty, mul_one, mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hr, h, -⟩; rwa [Nat.mod_eq_of_lt hr] at h
      · rintro rfl; exact ⟨ht, Nat.mod_eq_of_lt ht, fun p hp => absurd hp (Finset.notMem_empty p)⟩
    rw [this]; simp
  | insert p T hpT ih =>
    have ih' := ih (fun p' hp' => hm p' (mem_insert_of_mem hp'))
      (fun p' hp' => hR p' (mem_insert_of_mem hp')) (fun p' hp' => hcopq p' (mem_insert_of_mem hp'))
      (fun a ha b hb hab => hcop a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab)
    rw [prod_insert hpT, ← ih']
    set Q' := bigMod q m T
    have hQ'pos : 0 < Q' := Nat.mul_pos hq (prod_pos (fun p' hp' => hm p' (mem_insert_of_mem hp')))
    have hmp : 0 < m p := hm p (mem_insert_self p T)
    have hcopQ : Nat.Coprime Q' (m p) := by
      apply Nat.coprime_mul_iff_left.mpr
      refine ⟨hcopq p (mem_insert_self p T), ?_⟩
      rw [Nat.coprime_prod_left_iff]
      intro p' hp'
      exact hcop p' (mem_insert_of_mem hp') p (mem_insert_self p T) (fun h => hpT (h ▸ hp'))
    have hbig : bigMod q m (insert p T) = Q' * m p := by
      simp only [bigMod, Q', prod_insert hpT]; ring
    -- bijection r ↦ (r % Q', r % m p)
    rw [mul_comm, ← card_product]
    apply card_bij (fun r _ => (r % Q', r % m p))
    · intro r hr
      simp only [resSet, mem_filter, mem_range, hbig] at hr
      simp only [mem_product, resSet, mem_filter, mem_range]
      refine ⟨⟨Nat.mod_lt _ hQ'pos, ?_, ?_⟩, ?_⟩
      · rw [mod_bigMod_mod_q]; exact hr.2.1
      · intro p' hp'; rw [mod_bigMod_mod_m hp']; exact hr.2.2 p' (mem_insert_of_mem hp')
      · exact hr.2.2 p (mem_insert_self p T)
    · intro r hr r' hr' h
      simp only [Prod.mk.injEq] at h
      simp only [resSet, mem_filter, mem_range, hbig] at hr hr'
      have := (Nat.modEq_and_modEq_iff_modEq_mul hcopQ).mp ⟨h.1, h.2⟩
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt hr.1, Nat.mod_eq_of_lt hr'.1] at this
    · intro ⟨u, v⟩ huv
      simp only [mem_product, resSet, mem_filter, mem_range] at huv
      obtain ⟨⟨hu, hut, huT⟩, hv⟩ := huv
      have hvm : v < m p := hR p (mem_insert_self p T) v hv
      let k := Nat.chineseRemainder hcopQ u v
      refine ⟨k.1 % (Q' * m p), ?_, ?_⟩
      · simp only [resSet, mem_filter, mem_range, hbig]
        have hk1 : k.1 % (Q' * m p) % Q' = u := by
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_right Q' (m p))]
          have := k.2.1; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hu]
        have hk2 : k.1 % (Q' * m p) % m p = v := by
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_left (m p) Q')]
          have := k.2.2; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hvm]
        refine ⟨Nat.mod_lt _ (Nat.mul_pos hQ'pos hmp), ?_, ?_⟩
        · rw [← mod_bigMod_mod_q (m := m) T, hk1]; exact hut
        · intro p' hp'
          rcases mem_insert.mp hp' with rfl | hp''
          · rw [hk2]; exact hv
          · rw [← mod_bigMod_mod_m (q := q) hp'', hk1]; exact huT p' hp''
      · simp only [Prod.mk.injEq]
        constructor
        · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right Q' (m p))]
          have := k.2.1; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hu]
        · rw [Nat.mod_mod_of_dvd _ (dvd_mul_left (m p) Q')]
          have := k.2.2; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hvm]

end CRT

/- ### Step 3: the inclusion–exclusion bound -/

/-- Algebraic identity: `∑_{∅ ≠ T ⊆ P} (-1)^{|T|+1} ∏_{T} x = 1 - ∏_{P} (1 - x)`. -/
lemma sum_powerset_alt (P : Finset ℕ) (x : ℕ → ℝ) :
    ∑ T ∈ P.powerset.filter (·.Nonempty), (-1 : ℝ) ^ (T.card + 1) * ∏ p ∈ T, x p =
      1 - ∏ p ∈ P, (1 - x p) := by
  have h := Finset.prod_add (fun p => -x p) (fun _ => (1 : ℝ)) P
  simp only [prod_const_one, mul_one] at h
  have h' : ∏ p ∈ P, (1 - x p) = ∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p := by
    rw [show (fun p => 1 - x p) = (fun p => -x p + 1) by ext; ring, h]
    apply sum_congr rfl; intro T _
    rw [prod_neg]
  rw [h', ← sum_filter_add_sum_filter_not P.powerset (·.Nonempty)]
  have hempty : ∑ T ∈ P.powerset.filter (fun T => ¬ T.Nonempty), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p = 1 := by
    rw [show P.powerset.filter (fun T => ¬ T.Nonempty) = {∅} by
      ext T; simp only [mem_filter, mem_powerset, not_nonempty_iff_eq_empty, mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨empty_subset _, rfl⟩]
    simp
  rw [hempty]
  have : ∀ T ∈ P.powerset.filter (·.Nonempty),
      (-1 : ℝ) ^ (T.card + 1) * ∏ p ∈ T, x p = -((-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) := by
    intro T _; ring
  rw [sum_congr rfl this, sum_neg_distrib]; ring

/-- `∑_{∅ ≠ T ⊆ P} ∏_{T} y = ∏_{P} (1 + y) - 1`. -/
lemma sum_powerset_prod (P : Finset ℕ) (y : ℕ → ℝ) :
    ∑ T ∈ P.powerset.filter (·.Nonempty), ∏ p ∈ T, y p = ∏ p ∈ P, (1 + y p) - 1 := by
  have h := Finset.prod_add y (fun _ => (1 : ℝ)) P
  simp only [prod_const_one, mul_one] at h
  rw [show (fun p => 1 + y p) = (fun p => y p + 1) by ext; ring, h,
    ← sum_filter_add_sum_filter_not P.powerset (·.Nonempty)]
  rw [show P.powerset.filter (fun T => ¬ T.Nonempty) = {∅} by
      ext T; simp only [mem_filter, mem_powerset, not_nonempty_iff_eq_empty, mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨empty_subset _, rfl⟩]
  simp

/-- **Inclusion–exclusion, two-sided.** Under the CRT hypotheses,
`#{a ∈ [1,N] : a ≡ t (q), ∃ p ∈ P, a mod m p ∈ Rs p}` differs from
`(N/q)(1 - ∏_P (1 - |Rs p|/m p))` by at most `∏_P (1 + |Rs p|) - 1`. -/
theorem card_union_abs (N q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p')) :
    |(((Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) -
      (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p))| ≤
        ∏ p ∈ P, (1 + ((Rs p).card : ℝ)) - 1 := by
  classical
  let S : ℕ → Finset ℕ := fun p => (Icc 1 N).filter (fun a => a % q = t ∧ a % m p ∈ Rs p)
  have hunion : (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p) = P.biUnion S := by
    ext a; simp only [mem_filter, mem_biUnion, S]
    constructor
    · rintro ⟨ha, h1, p, hp, h2⟩; exact ⟨p, hp, ha, h1, h2⟩
    · rintro ⟨p, hp, ha, h1, h2⟩; exact ⟨ha, h1, p, hp, h2⟩
  -- intersections are periodic sets mod bigMod T
  have hinter : ∀ T (hT : T.Nonempty), T ⊆ P →
      T.inf' hT S = (Icc 1 N).filter (fun a => a % bigMod q m T ∈ resSet q t m Rs T) := by
    intro T hT hTP
    ext a
    rw [mem_inf']
    simp only [S, mem_filter]
    rw [← cond_iff_resSet T hq (fun p hp => hm p (hTP hp))]
    constructor
    · intro h
      obtain ⟨p0, hp0⟩ := hT
      exact ⟨(h p0 hp0).1, (h p0 hp0).2.1, fun p hp => (h p hp).2.2⟩
    · rintro ⟨ha, h1, h2⟩ p hp; exact ⟨ha, h1, h2 p hp⟩
  -- per-T estimate
  have hT : ∀ T ∈ P.powerset.filter (·.Nonempty),
      |(-1 : ℝ) ^ (T.card + 1) * (((Icc 1 N).filter
          (fun a => a % bigMod q m T ∈ resSet q t m Rs T)).card : ℝ) -
        (-1 : ℝ) ^ (T.card + 1) * ((N : ℝ) / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p)| ≤
          ∏ p ∈ T, ((Rs p).card : ℝ) := by
    intro T hTm
    simp only [mem_filter, mem_powerset] at hTm
    have hTP := hTm.1
    have hpos : 0 < bigMod q m T := Nat.mul_pos hq (prod_pos (fun p hp => hm p (hTP hp)))
    have hD : ∀ r ∈ resSet q t m Rs T, r < bigMod q m T := by
      intro r hr; simp only [resSet, mem_filter, mem_range] at hr; exact hr.1
    have hc := card_mod_mem_real N (bigMod q m T) hpos (resSet q t m Rs T) hD
    have hcard := card_resSet T hq ht (fun p hp => hm p (hTP hp)) (fun p hp => hR p (hTP hp))
      (fun p hp => hcopq p (hTP hp)) (fun p hp p' hp' => hcop p (hTP hp) p' (hTP hp'))
    rw [hcard] at hc
    have hbigR : ((bigMod q m T : ℕ) : ℝ) = (q : ℝ) * ∏ p ∈ T, (m p : ℝ) := by
      simp only [bigMod, Nat.cast_mul, Nat.cast_prod]
    have hmain : ((∏ p ∈ T, (Rs p).card : ℕ) : ℝ) * ((N : ℝ) / ((bigMod q m T : ℕ) : ℝ)) =
        (N : ℝ) / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p := by
      rw [hbigR, Nat.cast_prod, prod_div_distrib]; ring
    rw [hmain, Nat.cast_prod] at hc
    rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hc
  rw [hunion]
  have hIE := inclusion_exclusion_card_biUnion P S
  have hIE' : ((P.biUnion S).card : ℝ) = ∑ T ∈ P.powerset.filter (·.Nonempty),
      (-1 : ℝ) ^ (T.card + 1) * (((Icc 1 N).filter
          (fun a => a % bigMod q m T ∈ resSet q t m Rs T)).card : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIE
    simp only [Int.cast_natCast] at this
    rw [this]; push_cast
    rw [← sum_coe_sort (P.powerset.filter (·.Nonempty))]
    apply sum_congr rfl
    intro T _
    have hTP : T.1 ⊆ P := (mem_powerset.mp (mem_filter.mp T.2).1)
    rw [hinter T.1 (mem_filter.mp T.2).2 hTP]
  have hmainE : (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p)) =
      ∑ T ∈ P.powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (T.card + 1) * ((N : ℝ) / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p) := by
    rw [← sum_powerset_alt, mul_sum]; apply sum_congr rfl; intro T _; ring
  rw [hIE', hmainE, ← sum_sub_distrib, ← sum_powerset_prod]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hT)

/-- **Inclusion–exclusion bound** (upper half of `card_union_abs`). -/
theorem card_union_le (N q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p')) :
    (((Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p)) +
        (∏ p ∈ P, (1 + ((Rs p).card : ℝ)) - 1) := by
  have := card_union_abs N q t m Rs P hq ht hm hR hcopq hcop
  rw [abs_le] at this; linarith [this.2]

/-- Lower half of `card_union_abs`. -/
theorem card_union_ge (N q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p')) :
    (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p)) -
        (∏ p ∈ P, (1 + ((Rs p).card : ℝ)) - 1) ≤
      (((Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) := by
  have := card_union_abs N q t m Rs P hq ht hm hR hcopq hcop
  rw [abs_le] at this; linarith [this.1]

end Erdos848
end

section

/-
# Phase 4 (part 1): counting square roots modulo `b`

`sqrtCount b c = #{x ∈ [0,b) : x² ≡ c (mod b)}`.

* `sqrtCount_mul_le`: for coprime `b₁, b₂`, `sqrtCount (b₁ b₂) c ≤ sqrtCount b₁ c · sqrtCount b₂ c`
  (reduction mod `b₁` and mod `b₂` is injective on `[0, b₁ b₂)`).
* `sqrtCount_oddPrimePow_le`: for an odd prime `p` with `p ∤ c`, `sqrtCount (p^e) c ≤ 2`
  (if `x² ≡ y²` then `p^e ∣ (x−y)(x+y)`, and `p` cannot divide both factors).
-/

namespace Erdos848

open Finset

def sqrtCount (b c : ℕ) : ℕ := ((range b).filter (fun x => x * x % b = c % b)).card

theorem sqrtCount_mul_le {b₁ b₂ : ℕ} (h : Nat.Coprime b₁ b₂) (c : ℕ) :
    sqrtCount (b₁ * b₂) c ≤ sqrtCount b₁ c * sqrtCount b₂ c := by
  unfold sqrtCount
  rw [← card_product]
  apply card_le_card_of_injOn (fun x => (x % b₁, x % b₂))
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hx
    have hb₁ : 0 < b₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
    have hb₂ : 0 < b₂ := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
    have hmod := hx.2
    simp only [coe_product, coe_filter, Set.mem_prod, Set.mem_ofPred_eq, mem_range]
    refine ⟨⟨Nat.mod_lt _ hb₁, ?_⟩, ⟨Nat.mod_lt _ hb₂, ?_⟩⟩
    · have : x * x % b₁ = c % b₁ := by
        have := congrArg (· % b₁) hmod
        simpa [Nat.mod_mod_of_dvd _ (dvd_mul_right b₁ b₂)] using this
      rw [← Nat.mul_mod]; exact this
    · have : x * x % b₂ = c % b₂ := by
        have := congrArg (· % b₂) hmod
        simpa [Nat.mod_mod_of_dvd _ (dvd_mul_left b₂ b₁)] using this
      rw [← Nat.mul_mod]; exact this
  · intro x hx y hy hxy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hx hy
    simp only [Prod.mk.injEq] at hxy
    have h1 : x ≡ y [MOD b₁] := hxy.1
    have h2 : x ≡ y [MOD b₂] := hxy.2
    have h12 : x ≡ y [MOD b₁ * b₂] := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨h1, h2⟩
    unfold Nat.ModEq at h12
    rwa [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h12

theorem sqrtCount_oddPrimePow_le {p e c : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hpc : ¬ p ∣ c) :
    sqrtCount (p ^ e) c ≤ 2 := by
  unfold sqrtCount
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp only [pow_zero]
    calc ((range 1).filter (fun x => x * x % 1 = c % 1)).card ≤ (range 1).card := card_filter_le _ _
      _ ≤ 2 := by simp
  set P := p ^ e with hP
  set S := (range P).filter (fun x => x * x % P = c % P)
  by_cases hS : S = ∅
  · rw [hS]; simp
  obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.mpr hS
  have hPpos : 0 < P := pow_pos hp.pos e
  have hpP : p ∣ P := dvd_pow_self p he.ne'
  -- solutions are not divisible by p
  have hnd : ∀ z, z * z % P = c % P → ¬ p ∣ z := by
    intro z hz hpz
    apply hpc
    have h2 : (z * z) % P % p = c % P % p := by rw [hz]
    rw [Nat.mod_mod_of_dvd _ hpP, Nat.mod_mod_of_dvd _ hpP] at h2
    exact Nat.dvd_of_mod_eq_zero (h2 ▸ Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hpz z))
  simp only [S, mem_filter, mem_range] at hx₀
  have hx0 := hnd x₀ hx₀.2
  have key : ∀ y ∈ S, y = x₀ ∨ y = P - x₀ := by
    intro y hy
    simp only [S, mem_filter, mem_range] at hy
    -- (P : ℤ) ∣ (x₀ - y)(x₀ + y)
    have hmod : y * y ≡ x₀ * x₀ [MOD P] := by unfold Nat.ModEq; rw [hx₀.2, hy.2]
    have hdvd : (P : ℤ) ∣ ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) := by
      have := (Nat.modEq_iff_dvd.mp hmod)
      push_cast at this
      have e1 : ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) = (x₀ : ℤ) * x₀ - y * y := by ring
      rw [e1]; exact this
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    -- p cannot divide both factors
    have hnot : ¬ ((p : ℤ) ∣ (x₀ : ℤ) - y ∧ (p : ℤ) ∣ (x₀ : ℤ) + y) := by
      rintro ⟨h1, h2⟩
      have h3 : (p : ℤ) ∣ 2 * (x₀ : ℤ) := by
        have := dvd_add h1 h2; rw [show (x₀ : ℤ) - y + (x₀ + y) = 2 * x₀ by ring] at this; exact this
      rcases hpZ.dvd_or_dvd h3 with h4 | h4
      · have : p ∣ 2 := by exact_mod_cast h4
        exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      · exact hx0 (by exact_mod_cast h4)
    have hPZ : (P : ℤ) = (p : ℤ) ^ e := by rw [hP]; push_cast; ring
    by_cases hu : (p : ℤ) ∣ (x₀ : ℤ) - y
    · -- then p ∤ x₀ + y, so P ∣ x₀ - y, hence y = x₀
      have hv : ¬ (p : ℤ) ∣ (x₀ : ℤ) + y := fun hv => hnot ⟨hu, hv⟩
      have hcop : IsCoprime ((p : ℤ) ^ e) ((x₀ : ℤ) + y) :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpZ).mpr hv)
      have : (P : ℤ) ∣ (x₀ : ℤ) - y := by
        rw [hPZ] at hdvd ⊢; exact hcop.dvd_of_dvd_mul_right hdvd
      left
      have hlt : |(x₀ : ℤ) - y| < (P : ℤ) := by
        rw [abs_lt]; constructor <;> push_cast <;> omega
      have := Int.eq_zero_of_abs_lt_dvd this hlt
      omega
    · -- P ∣ x₀ + y, and 0 < x₀ + y < 2P, so y = P - x₀
      have hcop : IsCoprime ((p : ℤ) ^ e) ((x₀ : ℤ) - y) :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpZ).mpr hu)
      have h1 : (P : ℤ) ∣ (x₀ : ℤ) + y := by
        rw [hPZ] at hdvd ⊢; exact hcop.dvd_of_dvd_mul_left hdvd
      have h2 : P ∣ x₀ + y := by exact_mod_cast h1
      right
      obtain ⟨k, hk⟩ := h2
      have hx0pos : 0 < x₀ := Nat.pos_of_ne_zero (fun h => hx0 (h ▸ dvd_zero p))
      rcases k with _ | _ | k
      · omega
      · omega
      · nlinarith
  calc S.card ≤ ({x₀, P - x₀} : Finset ℕ).card := by
        apply card_le_card; intro y hy
        rcases key y hy with h | h <;> simp [h]
    _ ≤ 2 := Finset.card_le_two


/-- Two odd numbers whose squares agree modulo `2^e` (`e ≥ 3`) agree up to sign modulo `2^(e-1)`. -/
lemma two_pow_sq_eq {e : ℕ} (he : 3 ≤ e) {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : (2 : ℤ) ^ e ∣ (x - y) * (x + y)) :
    (2 : ℤ) ^ (e - 1) ∣ x - y ∨ (2 : ℤ) ^ (e - 1) ∣ x + y := by
  obtain ⟨u, hu⟩ : (2 : ℤ) ∣ x - y := Int.dvd_of_emod_eq_zero (by omega)
  obtain ⟨v, hv⟩ : (2 : ℤ) ∣ x + y := Int.dvd_of_emod_eq_zero (by omega)
  have hsum : u + v = x := by linarith
  have h4 : (2 : ℤ) ^ e = 2 * 2 * 2 ^ (e - 2) := by
    conv_lhs => rw [show e = (e - 2) + 2 from by omega]
    rw [pow_add]; ring
  have hdvd : (2 : ℤ) ^ (e - 2) ∣ u * v := by
    rw [hu, hv, h4] at h
    have : (2 * 2 * 2 ^ (e - 2) : ℤ) ∣ 2 * 2 * (u * v) := by
      rw [show (2 : ℤ) * u * (2 * v) = 2 * 2 * (u * v) by ring] at h; exact h
    exact (mul_dvd_mul_iff_left (by norm_num : (2 * 2 : ℤ) ≠ 0)).mp this
  have hodd2 : ∀ w : ℤ, w % 2 = 1 → IsCoprime ((2 : ℤ) ^ (e - 2)) w := by
    intro w hw
    apply IsCoprime.pow_left
    exact (Prime.coprime_iff_not_dvd Int.prime_two).mpr (by omega)
  have hpow : (2 : ℤ) ^ (e - 1) = 2 * 2 ^ (e - 2) := by
    rw [← pow_succ']; congr 1; omega
  rcases Int.emod_two_eq_zero_or_one u with hu0 | hu1
  · -- u even ⇒ v odd ⇒ 2^(e-2) ∣ u ⇒ 2^(e-1) ∣ 2u = x - y
    have hv1 : v % 2 = 1 := by omega
    have := (hodd2 v hv1).dvd_of_dvd_mul_right hdvd
    left; rw [hu, hpow]; exact mul_dvd_mul_left 2 this
  · -- u odd ⇒ 2^(e-2) ∣ v ⇒ 2^(e-1) ∣ 2v = x + y
    have := (hodd2 u hu1).dvd_of_dvd_mul_left hdvd
    right; rw [hv, hpow]; exact mul_dvd_mul_left 2 this

/-- Modulo `2^e`, an odd number has at most 4 square roots. -/
theorem sqrtCount_twoPow_le {e c : ℕ} (hc : c % 2 = 1) : sqrtCount (2 ^ e) c ≤ 4 := by
  unfold sqrtCount
  rcases Nat.lt_or_ge e 3 with he | he
  · calc ((range (2 ^ e)).filter (fun x => x * x % 2 ^ e = c % 2 ^ e)).card ≤ (range (2 ^ e)).card :=
          card_filter_le _ _
      _ = 2 ^ e := card_range _
      _ ≤ 4 := by interval_cases e <;> norm_num
  set P := 2 ^ e with hP
  set Q := 2 ^ (e - 1) with hQ
  have hPQ : P = 2 * Q := by rw [hP, hQ, ← pow_succ']; congr 1; omega
  have hQpos : 0 < Q := pow_pos (by norm_num) _
  set S := (range P).filter (fun x => x * x % P = c % P)
  by_cases hS : S = ∅
  · rw [hS]; simp
  obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.mpr hS
  have h2P : 2 ∣ P := by rw [hPQ]; exact dvd_mul_right 2 Q
  have hoddsol : ∀ z, z * z % P = c % P → z % 2 = 1 := by
    intro z hz
    have h2 : (z * z) % P % 2 = c % P % 2 := by rw [hz]
    rw [Nat.mod_mod_of_dvd _ h2P, Nat.mod_mod_of_dvd _ h2P, hc] at h2
    rcases Nat.mod_two_eq_zero_or_one z with h | h
    · rw [Nat.mul_mod, h] at h2; simp at h2
    · exact h
  simp only [S, mem_filter, mem_range] at hx₀
  have hx0o := hoddsol x₀ hx₀.2
  -- every solution y has y % Q ∈ {x₀ % Q, (Q - x₀ % Q) % Q}
  have key : ∀ y ∈ S, y % Q = x₀ % Q ∨ (y + x₀) % Q = 0 := by
    intro y hy
    simp only [S, mem_filter, mem_range] at hy
    have hyo := hoddsol y hy.2
    have hmod : y * y ≡ x₀ * x₀ [MOD P] := by unfold Nat.ModEq; rw [hx₀.2, hy.2]
    have hdvd : ((2 : ℤ) ^ e) ∣ ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) := by
      have := (Nat.modEq_iff_dvd.mp hmod)
      rw [hP] at this; push_cast at this
      have e1 : ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) = (x₀ : ℤ) * x₀ - y * y := by ring
      rw [e1]; exact this
    have hQZ : ((Q : ℕ) : ℤ) = (2 : ℤ) ^ (e - 1) := by rw [hQ]; push_cast; ring
    rcases two_pow_sq_eq he (by omega) (by omega) hdvd with h1 | h1
    · left
      have : ((Q : ℕ) : ℤ) ∣ (x₀ : ℤ) - y := by rw [hQZ]; exact h1
      exact (Nat.modEq_iff_dvd).mpr this
    · right
      have : ((Q : ℕ) : ℤ) ∣ (x₀ : ℤ) + y := by rw [hQZ]; exact h1
      have h2 : Q ∣ y + x₀ := by
        have : ((Q : ℕ) : ℤ) ∣ ((y + x₀ : ℕ) : ℤ) := by push_cast; rwa [add_comm]
        exact_mod_cast this
      exact Nat.mod_eq_zero_of_dvd h2
  -- so y lies in a set of size ≤ 4
  set r₁ := x₀ % Q
  set r₂ := (Q - x₀ % Q) % Q
  calc S.card ≤ ({r₁, r₁ + Q, r₂, r₂ + Q} : Finset ℕ).card := by
        apply card_le_card
        intro y hy
        have hyP : y < P := by simp only [S, mem_filter, mem_range] at hy; exact hy.1
        have hr1 : r₁ < Q := Nat.mod_lt _ hQpos
        rcases key y hy with h | h
        · -- y ≡ r₁ (mod Q), y < 2Q
          have : y = r₁ ∨ y = r₁ + Q := by
            have := Nat.div_add_mod y Q
            have hq : y / Q < 2 := by rw [Nat.div_lt_iff_lt_mul hQpos]; omega
            interval_cases hyq : y / Q <;> omega
          rcases this with h' | h' <;> simp [h']
        · -- y + x₀ ≡ 0 (mod Q) ⇒ y ≡ r₂ (mod Q)
          have hy2 : y % Q = r₂ := by
            have ha : y % Q < Q := Nat.mod_lt _ hQpos
            have hb : x₀ % Q < Q := Nat.mod_lt _ hQpos
            rw [Nat.add_mod] at h
            have hdm := Nat.div_add_mod (y % Q + x₀ % Q) Q
            rw [h] at hdm
            have hq : (y % Q + x₀ % Q) / Q < 2 := by rw [Nat.div_lt_iff_lt_mul hQpos]; omega
            simp only [r₂]
            interval_cases hq' : (y % Q + x₀ % Q) / Q
            · -- both residues are 0
              have h0 : x₀ % Q = 0 := by omega
              have h0' : y % Q = 0 := by omega
              rw [h0, h0', Nat.sub_zero, Nat.mod_self]
            · -- residues sum to Q
              rcases Nat.eq_zero_or_pos (x₀ % Q) with h0 | h0
              · rw [h0, Nat.sub_zero, Nat.mod_self]; omega
              · rw [Nat.mod_eq_of_lt (show Q - x₀ % Q < Q by omega)]; omega
          have : y = r₂ ∨ y = r₂ + Q := by
            have := Nat.div_add_mod y Q
            have hq : y / Q < 2 := by rw [Nat.div_lt_iff_lt_mul hQpos]; omega
            interval_cases hyq : y / Q <;> omega
          rcases this with h' | h' <;> simp [h']
    _ ≤ 4 := by
        calc ({r₁, r₁ + Q, r₂, r₂ + Q} : Finset ℕ).card
            ≤ ({r₁ + Q, r₂, r₂ + Q} : Finset ℕ).card + 1 := card_insert_le _ _
          _ ≤ (({r₂, r₂ + Q} : Finset ℕ).card + 1) + 1 := by gcongr; exact card_insert_le _ _
          _ ≤ ((({r₂ + Q} : Finset ℕ).card + 1) + 1) + 1 := by gcongr; exact card_insert_le _ _
          _ = 4 := by simp

/-- Modulo `2`, an odd number has exactly one square root. -/
lemma sqrtCount_two_le {c : ℕ} (hc : c % 2 = 1) : sqrtCount (2 ^ 1) c ≤ 1 := by
  unfold sqrtCount; rw [pow_one, hc]; decide

/-- Modulo `4`, an odd number has at most two square roots. -/
lemma sqrtCount_four_le {c : ℕ} (hc : c % 2 = 1) : sqrtCount (2 ^ 2) c ≤ 2 := by
  unfold sqrtCount
  have : c % 4 = 1 ∨ c % 4 = 3 := by omega
  norm_num
  rcases this with h | h <;> rw [h] <;> decide

/-- Number of odd prime factors. -/
def oddOmega (b : ℕ) : ℕ := (b.primeFactors.filter (· ≠ 2)).card

/-- The 2-adic factor: `4` if `8 ∣ b`, `2` if `4 ∣ b` but `8 ∤ b`, otherwise `1`. -/
def twoFactor (b : ℕ) : ℕ := if 8 ∣ b then 4 else if 4 ∣ b then 2 else 1

/-- The bound `twoFactor b · 2^(number of odd prime factors)`. -/
def rhoBound (b : ℕ) : ℕ := twoFactor b * 2 ^ oddOmega b

lemma oddOmega_mul {a b : ℕ} (h : Nat.Coprime a b) : oddOmega (a * b) = oddOmega a + oddOmega b := by
  unfold oddOmega
  rw [Nat.Coprime.primeFactors_mul h, filter_union]
  exact card_union_of_disjoint (disjoint_filter_filter h.disjoint_primeFactors)

lemma twoFactor_mul {a b : ℕ} (h : Nat.Coprime a b) : twoFactor a * twoFactor b = twoFactor (a * b) := by
  -- at most one of a, b is even
  have h2 : ¬ (2 ∣ a ∧ 2 ∣ b) := by
    rintro ⟨ha, hb⟩
    have := Nat.Coprime.coprime_dvd_left ha (Nat.Coprime.coprime_dvd_right hb h)
    norm_num at this
  have key : ∀ x y : ℕ, ¬ 2 ∣ x → twoFactor x * twoFactor y = twoFactor (x * y) := by
    intro x y hx
    have hx8 : ¬ 8 ∣ x := fun h8 => hx (dvd_trans (by norm_num) h8)
    have hx4 : ¬ 4 ∣ x := fun h4 => hx (dvd_trans (by norm_num) h4)
    have c8 : Nat.Coprime 8 x := Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx)
    have c4 : Nat.Coprime 4 x := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx)
    have e8 : 8 ∣ x * y ↔ 8 ∣ y := ⟨fun h => c8.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h x⟩
    have e4 : 4 ∣ x * y ↔ 4 ∣ y := ⟨fun h => c4.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h x⟩
    unfold twoFactor
    simp only [hx8, hx4, ite_false, one_mul, e8, e4]
  by_cases ha : 2 ∣ a
  · have hb : ¬ 2 ∣ b := fun hb => h2 ⟨ha, hb⟩
    rw [mul_comm, mul_comm a b]; exact key b a hb
  · exact key a b ha

lemma rhoBound_mul {a b : ℕ} (h : Nat.Coprime a b) : rhoBound a * rhoBound b = rhoBound (a * b) := by
  unfold rhoBound
  rw [oddOmega_mul h, pow_add, ← twoFactor_mul h]; ring

/-- **Square roots modulo `b`.** If `gcd(c, b) = 1`, then `x² ≡ c (mod b)` has at most
`rhoBound b` solutions in `[0, b)`. -/
theorem sqrtCount_le_rhoBound : ∀ b c, Nat.Coprime c b → sqrtCount b c ≤ rhoBound b := by
  intro b
  induction b using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro c hc
    rcases eq_or_ne p 2 with rfl | hp2
    · have hodd : c % 2 = 1 := by
        have : Nat.Coprime c 2 := Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 hn.ne') hc
        rcases Nat.mod_two_eq_zero_or_one c with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) (by
            intro h2; have := Nat.Coprime.coprime_dvd_left h2 this; norm_num at this)
        · exact h
      have hω : oddOmega (2 ^ n) = 0 := by
        unfold oddOmega; rw [Nat.primeFactors_prime_pow hn.ne' Nat.prime_two]; simp
      unfold rhoBound; rw [hω, pow_zero, mul_one]
      rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
      · subst h1; calc sqrtCount (2 ^ 1) c ≤ 1 := sqrtCount_two_le hodd
          _ = twoFactor (2 ^ 1) := by decide
      · subst h2; calc sqrtCount (2 ^ 2) c ≤ 2 := sqrtCount_four_le hodd
          _ = twoFactor (2 ^ 2) := by decide
      · calc sqrtCount (2 ^ n) c ≤ 4 := sqrtCount_twoPow_le hodd
          _ = twoFactor (2 ^ n) := by
            unfold twoFactor
            have : 8 ∣ 2 ^ n := by
              have : (8 : ℕ) = 2 ^ 3 := by norm_num
              rw [this]; exact Nat.pow_dvd_pow 2 h3
            simp [this]
    · have hpc : ¬ p ∣ c := by
        intro h
        have : p ∣ Nat.gcd c (p ^ n) := Nat.dvd_gcd h (dvd_pow_self p hn.ne')
        rw [hc] at this
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      calc sqrtCount (p ^ n) c ≤ 2 := sqrtCount_oddPrimePow_le hp hp2 hpc
        _ = rhoBound (p ^ n) := by
          unfold rhoBound oddOmega
          rw [Nat.primeFactors_prime_pow hn.ne' hp]
          have h2 : ¬ 2 ∣ p ^ n := by
            intro h
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h)
            exact hp2 this.symm
          have h8 : ¬ 8 ∣ p ^ n := fun h8 => h2 (dvd_trans (by norm_num) h8)
          have h4 : ¬ 4 ∣ p ^ n := fun h4 => h2 (dvd_trans (by norm_num) h4)
          simp [twoFactor, h8, h4, Finset.filter_singleton, hp2]
  | zero => intro c _; simp [sqrtCount]
  | one =>
    intro c _
    unfold sqrtCount rhoBound oddOmega twoFactor
    calc ((range 1).filter (fun x => x * x % 1 = c % 1)).card ≤ (range 1).card := card_filter_le _ _
      _ = 1 := by simp
      _ ≤ _ := by simp
  | coprime a b ha hb hab iha ihb =>
    intro c hc
    calc sqrtCount (a * b) c ≤ sqrtCount a c * sqrtCount b c := sqrtCount_mul_le hab c
      _ ≤ rhoBound a * rhoBound b := Nat.mul_le_mul
          (iha c (Nat.Coprime.coprime_mul_right_right hc)) (ihb c (Nat.Coprime.coprime_mul_left_right hc))
      _ = rhoBound (a * b) := rhoBound_mul hab

end Erdos848
end

section

/-
# Phase 4 (part 2): bounding the number of odd prime factors

`primeProd k` is the product of the first `k` odd primes.  We show that `k` distinct odd primes
have product at least `primeProd k` (`primeProd_le_prod`), and deduce the bound used by the
certificates (`code/n0_exact.py`, `rho_max`):

  for `1 ≤ b ≤ N < primeProd 45`:  `rhoBound b ≤ rhoMax N`,
  `rhoMax N = max (2^W(N)) (max (2·2^W(N/4)) (4·2^W(N/8)))`,  `W(L) = max {k ≤ 45 : primeProd k ≤ L}`.
-/

namespace Erdos848

open Finset

/-- The odd primes below 200. -/
def OP : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
  181, 191, 193, 197, 199]

lemma OP_length : OP.length = 45 := rfl

/-- Product of the first `k` odd primes. -/
def primeProd (k : ℕ) : ℕ := (OP.take k).prod

set_option maxRecDepth 20000 in
lemma OP_complete : ∀ p < 200, p.Prime → p ≠ 2 → p ∈ OP := by decide

set_option maxRecDepth 20000 in
lemma OP_count : ∀ a < 200, ∀ k < 45, a < OP[k]! → (OP.filter (· ≤ a)).length ≤ k := by decide

lemma OP_le_199 : ∀ k < 45, OP[k]! ≤ 199 := by decide

lemma primeProd_succ {k : ℕ} (hk : k < 45) : primeProd (k + 1) = primeProd k * OP[k]! := by
  unfold primeProd
  rw [List.prod_take_succ OP k (by rw [OP_length]; exact hk)]
  congr 1
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [OP_length]; exact hk)]

/-- `k` distinct odd primes have product at least `primeProd k`. -/
theorem primeProd_le_prod : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≠ 2) → S.card ≤ 45 →
    primeProd S.card ≤ ∏ p ∈ S, p := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _ _; simp [primeProd]
  | insert a s hlt ih =>
    intro hS hcard
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has, prod_insert has] at *
    have hk : s.card < 45 := by omega
    have ih' := ih (fun p hp => hS p (mem_insert_of_mem hp)) (by omega)
    rw [primeProd_succ hk]
    -- the (s.card)-th odd prime is at most a
    have hOa : OP[s.card]! ≤ a := by
      by_contra hcon
      push Not at hcon
      have ha200 : a < 200 := lt_of_lt_of_le hcon (by have := OP_le_199 s.card hk; omega)
      have hsub : insert a s ⊆ (OP.filter (· ≤ a)).toFinset := by
        intro x hx
        have hxp := hS x hx
        have hxa : x ≤ a := by
          rcases mem_insert.mp hx with rfl | hx'
          · exact le_refl _
          · exact (hlt x hx').le
        rw [List.mem_toFinset, List.mem_filter]
        exact ⟨OP_complete x (by omega) hxp.1 hxp.2, by simpa using hxa⟩
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem has] at h1
      have h2 := List.toFinset_card_le (OP.filter (· ≤ a))
      have h3 := OP_count a ha200 s.card hk hcon
      omega
    calc primeProd s.card * OP[s.card]! ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul ih' hOa
      _ = a * ∏ p ∈ s, p := mul_comm _ _

/-- Odd prime factors of `b`. -/
def oddPF (b : ℕ) : Finset ℕ := b.primeFactors.filter (· ≠ 2)

lemma oddOmega_eq (b : ℕ) : oddOmega b = (oddPF b).card := rfl

lemma oddPF_prime {b p : ℕ} (hp : p ∈ oddPF b) : p.Prime ∧ p ≠ 2 := by
  unfold oddPF at hp
  rw [mem_filter, Nat.mem_primeFactors] at hp
  exact ⟨hp.1.1, hp.2⟩

lemma prod_oddPF_dvd (b : ℕ) : (∏ p ∈ oddPF b, p) ∣ b :=
  dvd_trans (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)) (Nat.prod_primeFactors_dvd b)

lemma coprime_two_prod_oddPF (b : ℕ) (n : ℕ) : Nat.Coprime (2 ^ n) (∏ p ∈ oddPF b, p) := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  have := oddPF_prime hp
  exact (Nat.coprime_primes Nat.prime_two this.1).mpr (Ne.symm this.2)

/-- `W L = max {k ≤ 45 : primeProd k ≤ L}`. -/
def W (L : ℕ) : ℕ := Nat.findGreatest (fun k => primeProd k ≤ L) 45

lemma le_W {k L : ℕ} (hk : k ≤ 45) (h : primeProd k ≤ L) : k ≤ W L := Nat.le_findGreatest hk h

/-- The ρ bound used by the certificates. -/
def rhoMax (N : ℕ) : ℕ := max (2 ^ W N) (max (2 * 2 ^ W (N / 4)) (4 * 2 ^ W (N / 8)))

lemma card_oddPF_le {b L : ℕ} (hprod : (∏ p ∈ oddPF b, p) ≤ L) (hL : L < primeProd 45) :
    (oddPF b).card ≤ W L := by
  by_cases h45 : (oddPF b).card ≤ 45
  · exact le_W h45 ((primeProd_le_prod _ (fun p hp => oddPF_prime hp) h45).trans hprod)
  · -- impossible: a 45-element subset already has product ≥ primeProd 45 > L
    exfalso
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (show 45 ≤ (oddPF b).card by omega)
    have h1 := primeProd_le_prod T (fun p hp => oddPF_prime (hT hp)) (by omega)
    rw [hTc] at h1
    have h2 : (∏ p ∈ T, p) ≤ ∏ p ∈ oddPF b, p :=
      prod_le_prod_of_subset_of_one_le hT (fun _ _ => Nat.zero_le _) (fun p hp _ => (oddPF_prime hp).1.one_lt.le)
    omega

/-- **The ρ bound.** For `1 ≤ b ≤ N < primeProd 45`, `rhoBound b ≤ rhoMax N`. -/
theorem rhoBound_le_rhoMax {b N : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) (hN : N < primeProd 45) :
    rhoBound b ≤ rhoMax N := by
  unfold rhoBound twoFactor rhoMax
  rw [oddOmega_eq]
  set P := ∏ p ∈ oddPF b, p
  have hb0 : b ≠ 0 := by omega
  have hPb : P ∣ b := prod_oddPF_dvd b
  split_ifs with h8 h4
  · -- 8 ∣ b: 8·P ∣ b, so P ≤ N / 8
    have : 2 ^ 3 * P ∣ b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_prod_oddPF b 3) (by simpa using h8) hPb
    have hP : P ≤ N / 8 := by
      have := Nat.le_of_dvd (by omega) this
      rw [Nat.le_div_iff_mul_le (by norm_num)]; norm_num at this; linarith
    have := card_oddPF_le hP (by have := Nat.div_le_self N 8; omega)
    calc 4 * 2 ^ (oddPF b).card ≤ 4 * 2 ^ W (N / 8) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
      _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)
  · -- 4 ∣ b
    have : 2 ^ 2 * P ∣ b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_prod_oddPF b 2) (by simpa using h4) hPb
    have hP : P ≤ N / 4 := by
      have := Nat.le_of_dvd (by omega) this
      rw [Nat.le_div_iff_mul_le (by norm_num)]; norm_num at this; linarith
    have := card_oddPF_le hP (by have := Nat.div_le_self N 4; omega)
    calc 2 * 2 ^ (oddPF b).card ≤ 2 * 2 ^ W (N / 4) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
      _ ≤ _ := le_trans (le_max_left _ _) (le_max_right _ _)
  · have hP : P ≤ N := (Nat.le_of_dvd (by omega) hPb).trans hbN
    have := card_oddPF_le hP hN
    calc 1 * 2 ^ (oddPF b).card ≤ 2 ^ W N := by rw [one_mul]; exact Nat.pow_le_pow_right (by norm_num) this
      _ ≤ _ := le_max_left _ _

end Erdos848
end

section

/-
# Phase 4 (part 3): the bound for `Ex(b)` (Lemma A′(ii))

`exSet N b Y = {a ∈ [1,N] : ∃ p > Y, p² ∣ ab+1}` and

  `#exSet N b Y ≤ rhoBound b · (2(N+1)/Y + (Nb+1)/Y²)`   (`card_exSet_le`, for `1 ≤ b`, `1 ≤ Y`).

Proof: write `ab+1 = p² m`; `a ↦ (m, p)` is injective, `m ≤ (Nb+1)/(Y+1)²`, `p ≤ √((Nb+1)/m)`,
and for fixed `m` the residue `p mod b` lies in a set of at most `rhoBound b` square roots.
-/

namespace Erdos848

open Finset Real

/- ### A real-analysis lemma: `∑_{m ≤ M} 1/√m ≤ 2√M` -/

lemma sum_inv_sqrt_le (M : ℕ) : ∑ m ∈ Icc 1 M, (1 / √(m : ℝ)) ≤ 2 * √(M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM : (0 : ℝ) ≤ M := by positivity
    have key : 1 / √((M + 1 : ℕ) : ℝ) ≤ 2 * √((M + 1 : ℕ) : ℝ) - 2 * √(M : ℝ) := by
      push_cast
      have h1 : 0 < √((M : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      rw [div_le_iff₀ h1]
      have hsq : √(M : ℝ) * √((M : ℝ) + 1) ≤ (M : ℝ) + 1 / 2 := by
        rw [← Real.sqrt_mul hM]
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      have e1 : √((M : ℝ) + 1) * √((M : ℝ) + 1) = (M : ℝ) + 1 := Real.mul_self_sqrt (by linarith)
      nlinarith
    linarith

/- ### The set `Ex(b)` and its bound -/

def exSet (N b Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun a => ∃ p ∈ Icc (Y + 1) (N * b + 1), p * p ∣ a * b + 1)

/-- Residues `s < b` with `s² m ≡ 1 (mod b)`. -/
def rootSet (b m : ℕ) : Finset ℕ := (range b).filter (fun s => s * s * m % b = 1 % b)

lemma card_rootSet_le (b m : ℕ) : (rootSet b m).card ≤ rhoBound b := by
  by_cases hR : rootSet b m = ∅
  · rw [hR]; simp
  obtain ⟨s₀, hs₀⟩ := nonempty_iff_ne_empty.mpr hR
  simp only [rootSet, mem_filter, mem_range] at hs₀
  -- gcd(m, b) = 1 and gcd(s₀², b) = 1
  have hcop : Nat.Coprime (s₀ * s₀ * m) b := by
    have : s₀ * s₀ * m ≡ 1 [MOD b] := hs₀.2
    have h := Nat.ModEq.gcd_eq this
    rw [Nat.gcd_one_left] at h
    exact h
  have hm : Nat.Coprime m b := Nat.Coprime.coprime_mul_left hcop
  have hs : Nat.Coprime (s₀ * s₀) b := Nat.Coprime.coprime_mul_right hcop
  calc (rootSet b m).card ≤ sqrtCount b (s₀ * s₀) := by
        apply card_le_card
        intro x hx
        simp only [rootSet, mem_filter, mem_range] at hx
        simp only [mem_filter, mem_range]
        refine ⟨hx.1, ?_⟩
        -- x² m ≡ s₀² m ≡ 1, cancel m
        have h1 : x * x * m ≡ s₀ * s₀ * m [MOD b] := by
          unfold Nat.ModEq; rw [hx.2, hs₀.2]
        have h2 : x * x ≡ s₀ * s₀ [MOD b] :=
          Nat.ModEq.cancel_right_of_coprime (Nat.coprime_comm.mp hm) h1
        exact h2
    _ ≤ rhoBound b := sqrtCount_le_rhoBound b _ hs

/-- Integers `p ∈ [1, X]` with `p mod b` in `R`: at most `|R| (X/b + 1)`. -/
lemma card_mod_mem_le (X b : ℕ) (R : Finset ℕ) :
    ((Icc 1 X).filter (fun p => p % b ∈ R)).card ≤ R.card * (X / b + 1) := by
  calc ((Icc 1 X).filter (fun p => p % b ∈ R)).card
      ≤ (R.biUnion (fun r => (Icc 1 X).filter (fun p => p % b = r))).card := by
        apply card_le_card; intro p hp
        simp only [mem_filter] at hp
        simp only [mem_biUnion, mem_filter]
        exact ⟨p % b, hp.2, hp.1, rfl⟩
    _ ≤ ∑ r ∈ R, ((Icc 1 X).filter (fun p => p % b = r)).card := card_biUnion_le
    _ ≤ ∑ _r ∈ R, (X / b + 1) := sum_le_sum (fun r _ => card_mod_eq_le X b r)
    _ = R.card * (X / b + 1) := by simp

/-- **Lemma A′(ii).** `#Ex(b) ≤ rhoBound b · (2(N+1)/Y + (Nb+1)/Y²)`. -/
theorem card_exSet_le (N b Y : ℕ) (hb : 1 ≤ b) (hY : 1 ≤ Y) :
    ((exSet N b Y).card : ℝ) ≤ rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
  classical
  set K := N * b + 1 with hK
  set M := K / ((Y + 1) * (Y + 1)) with hM
  -- per-m sets of admissible p
  let Pm : ℕ → Finset ℕ := fun m => (Icc 1 (Nat.sqrt (K / m))).filter (fun p => p % b ∈ rootSet b m)
  -- every a ∈ Ex(b) is (p² m − 1)/b for some (m, p) in the sigma set
  have hcard : (exSet N b Y).card ≤ ((Icc 1 M).sigma Pm).card := by
    calc (exSet N b Y).card
        ≤ (((Icc 1 M).sigma Pm).image (fun x => (x.2 * x.2 * x.1 - 1) / b)).card := by
          apply card_le_card
          intro a ha
          simp only [exSet, mem_filter, mem_Icc] at ha
          obtain ⟨⟨ha1, haN⟩, p, hpI, hdvd⟩ := ha
          have hp1 : Y + 1 ≤ p := hpI.1
          obtain ⟨m, hm⟩ := hdvd
          have hp0 : 0 < p * p := Nat.mul_pos (by omega) (by omega)
          have hab : a * b + 1 ≤ K := by rw [hK]; nlinarith
          have hm1 : 1 ≤ m := by
            rcases Nat.eq_zero_or_pos m with h0 | h0
            · rw [h0] at hm; simp at hm
            · exact h0
          rw [mem_image]
          refine ⟨⟨m, p⟩, ?_, ?_⟩
          · simp only [mem_sigma, mem_Icc, Pm, mem_filter]
            refine ⟨⟨hm1, ?_⟩, ⟨by omega, ?_⟩, ?_⟩
            · rw [hM, Nat.le_div_iff_mul_le (by positivity)]
              calc m * ((Y + 1) * (Y + 1)) ≤ m * (p * p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hp1 hp1)
                _ = a * b + 1 := by rw [hm]; ring
                _ ≤ K := hab
            · apply Nat.le_sqrt.mpr
              rw [Nat.le_div_iff_mul_le (by omega)]
              rw [show p * p * m = a * b + 1 by rw [hm]]; exact hab
            · simp only [rootSet, mem_filter, mem_range]
              refine ⟨Nat.mod_lt _ (by omega), ?_⟩
              have h1 : p * p * m % b = 1 % b := by
                rw [← hm, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
              have h2 : p % b * (p % b) * m % b = p * p * m % b :=
                (((Nat.mod_modEq p b).mul (Nat.mod_modEq p b)).mul_right m)
              rw [h2, h1]
          · simp only
            rw [show p * p * m = a * b + 1 by rw [hm], Nat.add_sub_cancel, Nat.mul_div_cancel _ (by omega)]
      _ ≤ ((Icc 1 M).sigma Pm).card := card_image_le
  -- count the sigma set
  have hsig : ((Icc 1 M).sigma Pm).card ≤ ∑ m ∈ Icc 1 M, rhoBound b * (Nat.sqrt (K / m) / b + 1) := by
    rw [card_sigma]
    apply sum_le_sum; intro m _
    calc (Pm m).card ≤ (rootSet b m).card * (Nat.sqrt (K / m) / b + 1) := card_mod_mem_le _ _ _
      _ ≤ rhoBound b * (Nat.sqrt (K / m) / b + 1) := Nat.mul_le_mul_right _ (card_rootSet_le b m)
  -- real estimate of the sum
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hKpos : (0 : ℝ) < K := by positivity
  have hterm : ∀ m ∈ Icc 1 M, ((Nat.sqrt (K / m) / b + 1 : ℕ) : ℝ) ≤ √(K : ℝ) / b * (1 / √(m : ℝ)) + 1 := by
    intro m hm
    simp only [mem_Icc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
    push_cast
    have h1 : ((Nat.sqrt (K / m) / b : ℕ) : ℝ) ≤ (Nat.sqrt (K / m) : ℝ) / b := Nat.cast_div_le
    have h2 : (Nat.sqrt (K / m) : ℝ) ≤ √((K / m : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    have h3 : ((K / m : ℕ) : ℝ) ≤ (K : ℝ) / m := Nat.cast_div_le
    have h4 : √((K / m : ℕ) : ℝ) ≤ √((K : ℝ) / m) := Real.sqrt_le_sqrt h3
    have h5 : √((K : ℝ) / m) = √(K : ℝ) * (1 / √(m : ℝ)) := by
      rw [Real.sqrt_div' _ hm0.le, div_eq_mul_one_div]
    have hbpos : (0 : ℝ) < b := by linarith
    have : (Nat.sqrt (K / m) : ℝ) / b ≤ √(K : ℝ) / b * (1 / √(m : ℝ)) := by
      rw [div_mul_eq_mul_div, ← h5]
      exact div_le_div_of_nonneg_right (h2.trans h4) hbpos.le
    linarith
  have hsum := sum_inv_sqrt_le M
  have hMreal : (M : ℝ) ≤ (K : ℝ) / ((Y : ℝ) + 1) ^ 2 := by
    rw [hM]
    have := (Nat.cast_div_le (m := K) (n := (Y + 1) * (Y + 1)) : ((K / ((Y + 1) * (Y + 1)) : ℕ) : ℝ) ≤ _)
    push_cast at this; rw [sq]; exact this
  have hsqM : √(M : ℝ) ≤ √(K : ℝ) / ((Y : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity), ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (Y : ℝ) + 1),
      ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc (M : ℝ) * ((Y : ℝ) + 1) ^ 2 ≤ (K : ℝ) / ((Y : ℝ) + 1) ^ 2 * ((Y : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hMreal (by positivity)
      _ = K := by field_simp
  calc ((exSet N b Y).card : ℝ) ≤ ((∑ m ∈ Icc 1 M, rhoBound b * (Nat.sqrt (K / m) / b + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard.trans hsig
    _ = rhoBound b * ∑ m ∈ Icc 1 M, ((Nat.sqrt (K / m) / b + 1 : ℕ) : ℝ) := by
        push_cast; rw [mul_sum]
    _ ≤ rhoBound b * ∑ m ∈ Icc 1 M, (√(K : ℝ) / b * (1 / √(m : ℝ)) + 1) := by
        apply mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = rhoBound b * (√(K : ℝ) / b * ∑ m ∈ Icc 1 M, (1 / √(m : ℝ)) + M) := by
        rw [sum_add_distrib, ← mul_sum]; simp
    _ ≤ rhoBound b * (√(K : ℝ) / b * (2 * √(M : ℝ)) + (K : ℝ) / ((Y : ℝ) + 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) hMreal
    _ ≤ rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hKN : (K : ℝ) = N * b + 1 := by rw [hK]; push_cast; ring
        have hsK : √(K : ℝ) * √(K : ℝ) = K := Real.mul_self_sqrt hKpos.le
        have e1 : √(K : ℝ) / b * (2 * √(M : ℝ)) ≤ 2 * (N + 1) / Y := by
          calc √(K : ℝ) / b * (2 * √(M : ℝ)) ≤ √(K : ℝ) / b * (2 * (√(K : ℝ) / ((Y : ℝ) + 1))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
            _ = 2 * (√(K : ℝ) * √(K : ℝ)) / (b * ((Y : ℝ) + 1)) := by
                have : (b : ℝ) ≠ 0 := by linarith
                field_simp
            _ = 2 * K / (b * ((Y : ℝ) + 1)) := by rw [hsK]
            _ ≤ 2 * (N + 1) / Y := by
                rw [hKN, div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ N) (by linarith : (0:ℝ) ≤ b - 1)]
        have e2 : (K : ℝ) / ((Y : ℝ) + 1) ^ 2 ≤ (N * b + 1) / (Y : ℝ) ^ 2 := by
          rw [hKN]; apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
        linarith

end Erdos848
end

section

/-
# Phase 5: an elementary bound for the Pell tail of Lemma B

`pell_growth`: if `x₁ < x₂` and `xᵢ² + 1 = m yᵢ²`, then `3 x₁ ≤ x₂`.
`card_pell_le`: for fixed `m`, at most `Nat.log 3 N + 1` integers `x ∈ [1,N]` satisfy
`x² + 1 = m y²` for some `y`.

Proof idea (integers only): with `a = m y₁ y₂ − x₁ x₂` and `c = x₂ y₁ − x₁ y₂` one has
`a² − m c² = 1` and `x₂ = a x₁ + m c y₁`; then `c ≥ 1`, `a ≥ 2` and `m y₁ ≥ x₁` give `x₂ ≥ 3 x₁`.
This replaces the unit-group argument of `proof.md` §3 (the certificates were re-checked with the
resulting weaker constant `1/ln 3`).
-/

namespace Erdos848

open Finset

theorem pell_growth {m x₁ y₁ x₂ y₂ : ℕ} (h₁ : x₁ ^ 2 + 1 = m * y₁ ^ 2)
    (h₂ : x₂ ^ 2 + 1 = m * y₂ ^ 2) (hlt : x₁ < x₂) : 3 * x₁ ≤ x₂ := by
  have H₁ : (x₁ : ℤ) ^ 2 + 1 = m * (y₁ : ℤ) ^ 2 := by exact_mod_cast h₁
  have H₂ : (x₂ : ℤ) ^ 2 + 1 = m * (y₂ : ℤ) ^ 2 := by exact_mod_cast h₂
  have hlt' : (x₁ : ℤ) < x₂ := by exact_mod_cast hlt
  have hx₁ : (0 : ℤ) ≤ x₁ := by positivity
  have hx₂ : (0 : ℤ) ≤ x₂ := by positivity
  have hy₁ : (0 : ℤ) ≤ y₁ := by positivity
  have hy₂ : (0 : ℤ) ≤ y₂ := by positivity
  have hm : (0 : ℤ) ≤ m := by positivity
  set a : ℤ := m * y₁ * y₂ - x₁ * x₂ with ha
  set c : ℤ := x₂ * y₁ - x₁ * y₂ with hc
  have hnorm : a ^ 2 - m * c ^ 2 = 1 := by
    rw [ha, hc]; linear_combination ((x₂ : ℤ) ^ 2 - m * (y₂ : ℤ) ^ 2) * H₁ - H₂
  have hx₂eq : (x₂ : ℤ) = a * x₁ + m * c * y₁ := by
    rw [ha, hc]; linear_combination (x₂ : ℤ) * H₁
  -- c ≥ 1
  have hsq : ((x₁ : ℤ) * y₂) ^ 2 < ((x₂ : ℤ) * y₁) ^ 2 := by
    have hyy : (y₁ : ℤ) ^ 2 < (y₂ : ℤ) ^ 2 := by nlinarith
    have : ((x₂ : ℤ) * y₁) ^ 2 - ((x₁ : ℤ) * y₂) ^ 2 = (y₂ : ℤ) ^ 2 - (y₁ : ℤ) ^ 2 := by
      linear_combination (y₁ : ℤ) ^ 2 * H₂ - (y₂ : ℤ) ^ 2 * H₁
    linarith
  have hc1 : 1 ≤ c := by
    have : (x₁ : ℤ) * y₂ < x₂ * y₁ :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    rw [hc]; linarith
  -- a ≥ 2
  have ha1 : 1 ≤ a := by
    have hsq' : ((x₁ : ℤ) * x₂) ^ 2 < ((m : ℤ) * y₁ * y₂) ^ 2 := by
      have : ((m : ℤ) * y₁ * y₂) ^ 2 = ((x₁ : ℤ) ^ 2 + 1) * ((x₂ : ℤ) ^ 2 + 1) := by
        rw [H₁, H₂]; ring
      rw [this]; nlinarith [sq_nonneg ((x₁ : ℤ)), sq_nonneg ((x₂ : ℤ))]
    have : (x₁ : ℤ) * x₂ < m * y₁ * y₂ := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq'
    rw [ha]; linarith
  have hm1 : (1 : ℤ) ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp at h₁
    · exact_mod_cast hpos
  have ha2 : 2 ≤ a := by
    by_contra hlt2
    have : a = 1 := by omega
    rw [this] at hnorm
    nlinarith
  -- m y₁ ≥ x₁
  have hmy : (x₁ : ℤ) ≤ m * y₁ := by
    have : ((x₁ : ℤ)) ^ 2 < ((m : ℤ) * y₁) ^ 2 := by
      have : (m : ℤ) * y₁ ^ 2 ≤ (m * y₁) ^ 2 := by nlinarith
      nlinarith
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) this).le
  have : (3 : ℤ) * x₁ ≤ x₂ := by
    rw [hx₂eq]; nlinarith
  exact_mod_cast this

/-- For fixed `m`, the integers `x ∈ [1,N]` with `x² + 1 = m y²` (some `y`). -/
def pellSet (m N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ y ∈ range (x + 1), x ^ 2 + 1 = m * y ^ 2)

lemma mem_pellSet {m N x : ℕ} :
    x ∈ pellSet m N ↔ 1 ≤ x ∧ x ≤ N ∧ ∃ y, x ^ 2 + 1 = m * y ^ 2 := by
  unfold pellSet
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, y, -, hy⟩; exact ⟨h1, h2, y, hy⟩
  · rintro ⟨h1, h2, y, hy⟩
    refine ⟨⟨h1, h2⟩, y, ?_, hy⟩
    -- y ≤ x since m ≥ 1 and m y² = x² + 1 ≤ (x+1)², so y ≤ x + 1 - 1
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0; simp at hy
    · by_contra hge
      push Not at hge
      have : (x + 1) ^ 2 ≤ m * y ^ 2 := by
        calc (x + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hge 2
          _ ≤ m * y ^ 2 := Nat.le_mul_of_pos_left _ hm
      nlinarith

/-- At most one element of `pellSet m N` lies in `(N/3, N]`. -/
lemma card_pellSet_le (m : ℕ) : ∀ N, (pellSet m N).card ≤ Nat.log 3 N + 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 3 with hN | hN
    · -- N < 3: the set has at most N ≤ 2 ... use a direct bound: elements x ≤ 2 with growth
      -- any two elements x < x' satisfy 3x ≤ x', impossible below 3 unless the smaller is 0
      have : (pellSet m N).card ≤ 1 := by
        rw [card_le_one]
        intro x hx x' hx'
        rw [mem_pellSet] at hx hx'
        obtain ⟨hx1, hxN, y, hy⟩ := hx
        obtain ⟨hx1', hxN', y', hy'⟩ := hx'
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have := pell_growth hy hy' hlt; omega
        · have := pell_growth hy' hy hlt; omega
      omega
    · -- split off (N/3, N]
      have hsplit : pellSet m N ⊆ pellSet m (N / 3) ∪ (pellSet m N).filter (fun x => N / 3 < x) := by
        intro x hx
        by_cases h : N / 3 < x
        · exact mem_union_right _ (mem_filter.mpr ⟨hx, h⟩)
        · apply mem_union_left
          rw [mem_pellSet] at hx ⊢
          exact ⟨hx.1, by omega, hx.2.2⟩
      have hone : ((pellSet m N).filter (fun x => N / 3 < x)).card ≤ 1 := by
        rw [card_le_one]
        intro x hx x' hx'
        rw [mem_filter, mem_pellSet] at hx hx'
        obtain ⟨⟨hx1, hxN, y, hy⟩, hxl⟩ := hx
        obtain ⟨⟨hx1', hxN', y', hy'⟩, hxl'⟩ := hx'
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have := pell_growth hy hy' hlt; omega
        · have := pell_growth hy' hy hlt; omega
      have hih := ih (N / 3) (by omega)
      have hlog : Nat.log 3 (N / 3) + 1 = Nat.log 3 N := by
        rw [Nat.log_div_base]
        have : 1 ≤ Nat.log 3 N := Nat.log_pos (by norm_num) hN
        omega
      calc (pellSet m N).card ≤ (pellSet m (N / 3)).card + ((pellSet m N).filter (fun x => N / 3 < x)).card :=
            (card_le_card hsplit).trans (Finset.card_union_le _ _)
        _ ≤ Nat.log 3 (N / 3) + 1 + 1 := by omega
        _ = Nat.log 3 N + 1 := by omega

/-- **Pell tail of Lemma B.** The integers `n ∈ [1,N]` such that `n² + 1` is divisible by `p²`
for some `p > Y` number at most `⌊(N²+1)/(Y+1)²⌋ · (log₃ N + 1)`. -/
theorem pellTail_le (N Y : ℕ) :
    ((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card ≤
      ((N ^ 2 + 1) / (Y + 1) ^ 2) * (Nat.log 3 N + 1) := by
  set M := (N ^ 2 + 1) / (Y + 1) ^ 2
  calc ((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card
      ≤ ((Icc 1 M).biUnion (fun m => pellSet m N)).card := by
        apply card_le_card
        intro n hn
        simp only [mem_filter, mem_Icc] at hn
        obtain ⟨⟨hn1, hnN⟩, p, ⟨hp1, -⟩, hd⟩ := hn
        obtain ⟨m, hm⟩ := hd
        have hp0 : 0 < p := by omega
        have hm1 : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | h
          · subst h0; simp at hm
          · exact h
        have hmM : m ≤ M := by
          apply (Nat.le_div_iff_mul_le (by positivity)).mpr
          have h1 : (Y + 1) ^ 2 ≤ p * p := by nlinarith
          have h2 : n ^ 2 + 1 ≤ N ^ 2 + 1 := by nlinarith
          calc m * (Y + 1) ^ 2 ≤ m * (p * p) := Nat.mul_le_mul_left _ h1
            _ = n ^ 2 + 1 := by rw [hm]; ring
            _ ≤ N ^ 2 + 1 := h2
        simp only [mem_biUnion, mem_Icc]
        refine ⟨m, ⟨hm1, hmM⟩, mem_pellSet.mpr ⟨hn1, hnN, p, ?_⟩⟩
        rw [hm]; ring
    _ ≤ ∑ m ∈ Icc 1 M, (pellSet m N).card := card_biUnion_le
    _ ≤ ∑ _m ∈ Icc 1 M, (Nat.log 3 N + 1) := sum_le_sum (fun m _ => card_pellSet_le m N)
    _ = M * (Nat.log 3 N + 1) := by simp

end Erdos848
end

section

/-
# Phase 6 (part 1): root sets and single-class sieves

`witRoots b p` : residues `r < p²` with `p² ∣ r·b + 1` (at most one, `card_witRoots_le`);
`sqRoots p`    : residues `r < p²` with `p² ∣ r² + 1` (at most two for odd `p`, `card_sqRoots_le`).

`classSieve_le` is the generic single-class sieve of Lemma A′(iii) and Lemma B:
small primes by inclusion–exclusion (`card_union_le`), medium primes by a union bound.
-/

namespace Erdos848

open Finset

/-- Residues `r < p²` with `p² ∣ r b + 1`. -/
def witRoots (b p : ℕ) : Finset ℕ := (range (p * p)).filter (fun r => p * p ∣ r * b + 1)

/-- Residues `r < p²` with `p² ∣ r² + 1`. -/
def sqRoots (p : ℕ) : Finset ℕ := (range (p * p)).filter (fun r => p * p ∣ r * r + 1)

lemma witRoots_sub (b p : ℕ) : witRoots b p ⊆ range (p * p) := filter_subset _ _
lemma sqRoots_sub (p : ℕ) : sqRoots p ⊆ range (p * p) := filter_subset _ _

lemma mod_mem_witRoots {b p : ℕ} (hp : 0 < p) (a : ℕ) :
    a % (p * p) ∈ witRoots b p ↔ p * p ∣ a * b + 1 := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hmod : (a % (p * p)) * b + 1 ≡ a * b + 1 [MOD p * p] :=
    Nat.ModEq.add_right 1 (Nat.ModEq.mul_right b (Nat.mod_modEq a _))
  simp only [witRoots, mem_filter, mem_range, Nat.mod_lt a hpp, true_and]
  exact (Nat.ModEq.dvd_iff hmod dvd_rfl)

lemma mod_mem_sqRoots {p : ℕ} (hp : 0 < p) (a : ℕ) :
    a % (p * p) ∈ sqRoots p ↔ p * p ∣ a * a + 1 := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hmod : (a % (p * p)) * (a % (p * p)) + 1 ≡ a * a + 1 [MOD p * p] :=
    Nat.ModEq.add_right 1 (Nat.ModEq.mul (Nat.mod_modEq a _) (Nat.mod_modEq a _))
  simp only [sqRoots, mem_filter, mem_range, Nat.mod_lt a hpp, true_and]
  exact (Nat.ModEq.dvd_iff hmod dvd_rfl)

lemma card_witRoots_le {b p : ℕ} (hp : p.Prime) : (witRoots b p).card ≤ 1 := by
  by_cases hpb : p ∣ b
  · have : witRoots b p = ∅ := by
      rw [witRoots, filter_eq_empty_iff]
      intro r _; exact not_sq_dvd_of_dvd hp hpb
    rw [this]; simp
  · obtain ⟨c, -, hc⟩ := prime_sq_dvd_mul_add_one_iff hp hpb
    rw [card_le_one]
    intro r hr r' hr'
    simp only [witRoots, mem_filter, mem_range] at hr hr'
    have h1 := (hc r).mp hr.2
    have h2 := (hc r').mp hr'.2
    rw [Nat.mod_eq_of_lt hr.1] at h1
    rw [Nat.mod_eq_of_lt hr'.1] at h2
    omega

lemma card_sqRoots_le {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : (sqRoots p).card ≤ 2 := by
  have hpp : 1 ≤ p * p := Nat.mul_pos hp.pos hp.pos
  have hpc : ¬ p ∣ p * p - 1 := by
    intro h
    have h1 : p ∣ p * p - (p * p - 1) := Nat.dvd_sub (dvd_mul_right p p) h
    rw [Nat.sub_sub_self hpp] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have := sqrtCount_oddPrimePow_le (e := 2) hp hodd hpc
  unfold sqrtCount at this
  rw [pow_two] at this
  refine le_trans (card_le_card ?_) this
  intro r hr
  simp only [sqRoots, mem_filter, mem_range] at hr ⊢
  refine ⟨hr.1, ?_⟩
  rw [Nat.mod_eq_of_lt (Nat.sub_lt hpp one_pos)]
  obtain ⟨k, hk⟩ := hr.2
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0] at hk; omega
    · exact h
  have : r * r = (p * p) * (k - 1) + (p * p - 1) := by
    have : p * p * k = p * p * (k - 1) + p * p := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hk1)]
    omega
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.sub_lt hpp one_pos)]

/-- U1 primes: `p ≡ 1 (mod 4)`, `p ≥ 13`. -/
def IsU1 (p : ℕ) : Prop := p.Prime ∧ p % 4 = 1 ∧ 13 ≤ p

instance : DecidablePred IsU1 := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A prime whose square divides `x² + 1` is `≡ 1 (mod 4)`. -/
lemma prime_mod_four_of_sq_dvd {p x : ℕ} (hp : p.Prime) (h : p * p ∣ x * x + 1) : p % 4 = 1 := by
  have hdvd : p ∣ x * x + 1 := dvd_trans (dvd_mul_right p p) h
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : x * x % 4 = 0 ∨ x * x % 4 = 1 := by
      rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
    omega
  have h3 : p % 4 ≠ 3 := by
    have := Fact.mk hp
    apply ZMod.mod_four_ne_three_of_sq_eq_neg_one (y := (x : ZMod p))
    have : ((x * x + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at this
    linear_combination this
  rcases Nat.Prime.eq_two_or_odd hp with h2 | h2
  · exact absurd h2 hp2
  · omega

/-- For `x ≢ ±7 (mod 25)`, a prime square dividing `x² + 1` comes from a U1 prime. -/
lemma isU1_of_sq_dvd {p x : ℕ} (hp : p.Prime) (h : p * p ∣ x * x + 1)
    (hx : x % 25 ≠ 7 ∧ x % 25 ≠ 18) : IsU1 p := by
  have h4 := prime_mod_four_of_sq_dvd hp h
  refine ⟨hp, h4, ?_⟩
  by_contra hlt
  push Not at hlt
  have hp5 : p = 5 := by
    interval_cases p <;> first | rfl | omega | (exfalso; norm_num at hp)
  subst hp5
  have h25 : (x * x + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h)
  have hx25 : (x * x + 1) % 25 = ((x % 25) * (x % 25) + 1) % 25 := by
    rw [Nat.add_mod, Nat.mul_mod]; conv_rhs => rw [Nat.add_mod]
  have : x % 25 < 25 := Nat.mod_lt _ (by norm_num)
  rw [hx25] at h25
  interval_cases hr : x % 25 <;> omega

/- ### The generic single-class sieve -/

/-- Primes `p ≤ z` with property `Q`. -/
def smallP (z : ℕ) (Q : ℕ → Prop) [DecidablePred Q] : Finset ℕ :=
  (range (z + 1)).filter (fun p => p.Prime ∧ Q p)

/-- Primes `z < p ≤ w` with property `Q`. -/
def midP (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] : Finset ℕ :=
  (Ioc z w).filter (fun p => p.Prime ∧ Q p)

lemma coprime_sq_of_primes {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (h : p ≠ p') :
    Nat.Coprime (p * p) (p' * p') := by
  have := (Nat.coprime_primes hp hp').mpr h
  have h2 : Nat.Coprime (p * p) p' := Nat.coprime_mul_iff_left.mpr ⟨this, this⟩
  exact Nat.Coprime.mul_right h2 h2

/-- One prime: `#{a ≤ N : a ≡ t (q), a mod p² ∈ R} ≤ |R| (N/q)/p² + |R|`. -/
lemma card_single_le (N q t p : ℕ) (R : Finset ℕ) (hq : 0 < q) (ht : t < q) (hp : 0 < p)
    (hR : R ⊆ range (p * p)) (hcop : Nat.Coprime q p) :
    (((Icc 1 N).filter (fun a => a % q = t ∧ a % (p * p) ∈ R)).card : ℝ) ≤
      (R.card : ℝ) * ((N : ℝ) / q / (p * p)) + R.card := by
  have h := card_union_le N q t (fun p => p * p) (fun _ => R) {p} hq ht
    (by simp [hp.ne']) (fun p' hp' r hr => by
      rw [mem_singleton] at hp'; subst hp'; exact mem_range.mp (hR hr))
    (fun p' hp' => by rw [mem_singleton] at hp'; subst hp'; exact Nat.Coprime.mul_right hcop hcop)
    (fun p₁ h₁ p₂ h₂ hne => by rw [mem_singleton] at h₁ h₂; exact absurd (h₁.trans h₂.symm) hne)
  have hset : (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p' ∈ ({p} : Finset ℕ), a % (p' * p') ∈ R) =
      (Icc 1 N).filter (fun a => a % q = t ∧ a % (p * p) ∈ R) := by
    apply filter_congr; intro a _; simp
  rw [hset] at h
  simp only [prod_singleton, Nat.cast_mul] at h
  have : (N : ℝ) / q * (1 - (1 - (R.card : ℝ) / (p * p))) + (1 + (R.card : ℝ) - 1) =
      (R.card : ℝ) * ((N : ℝ) / q / (p * p)) + R.card := by ring
  linarith

/-- **Single-class sieve.** Small primes (`p ≤ z`) by inclusion–exclusion, medium primes
(`z < p ≤ w`) by a union bound; `c` bounds the number of bad residues mod `p²`. -/
theorem classSieve_le (N q t z w c : ℕ) (Rs : ℕ → Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hq : 0 < q) (ht : t < q) (hc : c ≤ 4)
    (hRs : ∀ p, Rs p ⊆ range (p * p)) (hRc : ∀ p, p.Prime → Q p → (Rs p).card ≤ c)
    (hcop : ∀ p, p.Prime → Q p → Nat.Coprime q p) :
    (((Icc 1 N).filter (fun a => a % q = t ∧
        ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p)).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p))) +
        (((1 + c : ℕ) : ℝ) ^ (smallP z Q).card - 1) +
        ∑ p ∈ midP z w Q, ((c : ℝ) * ((N : ℝ) / q / (p * p)) + c) := by
  classical
  set A := (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ smallP z Q, a % (p * p) ∈ Rs p)
  set B : ℕ → Finset ℕ := fun p => (Icc 1 N).filter (fun a => a % q = t ∧ a % (p * p) ∈ Rs p)
  have hsub : (Icc 1 N).filter (fun a => a % q = t ∧
      ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p) ⊆ A ∪ (midP z w Q).biUnion B := by
    intro a ha
    simp only [mem_filter] at ha
    obtain ⟨ha1, hat, p, hpw, hp, hQ, hR⟩ := ha
    by_cases hpz : p ≤ z
    · apply mem_union_left
      simp only [A, mem_filter, smallP, mem_range]
      exact ⟨ha1, hat, p, ⟨by omega, hp, hQ⟩, hR⟩
    · apply mem_union_right
      simp only [mem_biUnion, B, mem_filter, midP, mem_Ioc]
      exact ⟨p, ⟨⟨by omega, hpw⟩, hp, hQ⟩, ha1, hat, hR⟩
  have hcard : (((Icc 1 N).filter (fun a => a % q = t ∧
      ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p)).card : ℝ) ≤
      (A.card : ℝ) + ∑ p ∈ midP z w Q, ((B p).card : ℝ) := by
    have h1 := (card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := card_biUnion_le (s := midP z w Q) (t := B)
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  -- small primes
  have hsmallP : ∀ p ∈ smallP z Q, p.Prime ∧ Q p := fun p hp => (mem_filter.mp hp).2
  have hA := card_union_le N q t (fun p => p * p) Rs (smallP z Q) hq ht
    (fun p hp => Nat.mul_pos (hsmallP p hp).1.pos (hsmallP p hp).1.pos)
    (fun p _ r hr => mem_range.mp (hRs p hr))
    (fun p hp => Nat.Coprime.mul_right (hcop p (hsmallP p hp).1 (hsmallP p hp).2)
      (hcop p (hsmallP p hp).1 (hsmallP p hp).2))
    (fun p hp p' hp' hne => coprime_sq_of_primes (hsmallP p hp).1 (hsmallP p' hp').1 hne)
  have hNq : (0 : ℝ) ≤ (N : ℝ) / q := by positivity
  have hprod : ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p)) ≤
      ∏ p ∈ smallP z Q, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ)) := by
    apply prod_le_prod
    · intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hsmallP p hp).1.two_le
      have : (c : ℝ) ≤ 4 := by exact_mod_cast hc
      rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    · intro p hp
      have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p (hsmallP p hp).1 (hsmallP p hp).2
      push_cast
      have : (0 : ℝ) < p * p := by have := (hsmallP p hp).1.pos; positivity
      gcongr
  have hprod2 : ∏ p ∈ smallP z Q, (1 + ((Rs p).card : ℝ)) ≤ ((1 + c : ℕ) : ℝ) ^ (smallP z Q).card := by
    rw [← prod_const]
    apply prod_le_prod
    · intro p _; positivity
    · intro p hp
      have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p (hsmallP p hp).1 (hsmallP p hp).2
      push_cast; linarith
  have hA' : (A.card : ℝ) ≤ (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p))) +
      (((1 + c : ℕ) : ℝ) ^ (smallP z Q).card - 1) := by
    have : (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ))) ≤
        (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p))) :=
      mul_le_mul_of_nonneg_left (by linarith) hNq
    linarith
  -- medium primes
  have hB : ∀ p ∈ midP z w Q, ((B p).card : ℝ) ≤ (c : ℝ) * ((N : ℝ) / q / (p * p)) + c := by
    intro p hp
    have hpQ := (mem_filter.mp hp).2
    have h := card_single_le N q t p (Rs p) hq ht hpQ.1.pos (hRs p) (hcop p hpQ.1 hpQ.2)
    have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hpQ.1 hpQ.2
    have : (0 : ℝ) ≤ (N : ℝ) / q / (p * p) := by positivity
    calc ((B p).card : ℝ) ≤ ((Rs p).card : ℝ) * ((N : ℝ) / q / (p * p)) + (Rs p).card := h
      _ ≤ _ := by gcongr
  have := sum_le_sum hB
  linarith

/- ### Lemma A′: sieving by one witness -/

/-- `Mid(b)`: some prime `p ∈ (pc, Y]` has `p² ∣ ab + 1`. -/
def midSet (N b pc Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun a => ∃ p ≤ Y, p.Prime ∧ pc < p ∧ a % (p * p) ∈ witRoots b p)

/-- The restricted part of Lemma A′(iii) for one class `t`. -/
def resPart (N b q t pc : ℕ) (excl : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ≤ pc, p.Prime ∧ p ∉ excl ∧ a % (p * p) ∈ witRoots b p)

/-- Every `a` with `ab + 1` not squarefree and no excluded prime square lies in a restricted
part, in `Mid(b)` or in `Ex(b)`. -/
lemma witness_cover (N b q pc Y : ℕ) (Tset excl : Finset ℕ) (Pa : ℕ → Prop) [DecidablePred Pa]
    (hT : ∀ a, Pa a → a % q ∈ Tset) (hexcl : ∀ a, Pa a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (Icc 1 N).filter (fun a => Pa a ∧ ¬ Squarefree (a * b + 1)) ⊆
      (Tset.biUnion (fun t => resPart N b q t pc excl) ∪ midSet N b pc Y) ∪ exSet N b Y := by
  intro a ha
  simp only [mem_filter, mem_Icc] at ha
  obtain ⟨⟨ha1, haN⟩, hPa, hsq⟩ := ha
  obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd hsq
  have hpe : p ∉ excl := fun h => hexcl a hPa p h hd
  have hR : a % (p * p) ∈ witRoots b p := (mod_mem_witRoots hp.pos a).mpr hd
  by_cases hpc : p ≤ pc
  · apply mem_union_left; apply mem_union_left
    simp only [mem_biUnion, resPart, mem_filter, mem_Icc]
    exact ⟨a % q, hT a hPa, ⟨ha1, haN⟩, rfl, p, hpc, hp, hpe, hR⟩
  by_cases hpY : p ≤ Y
  · apply mem_union_left; apply mem_union_right
    simp only [midSet, mem_filter, mem_Icc]
    exact ⟨⟨ha1, haN⟩, p, hpY, hp, by omega, hR⟩
  · apply mem_union_right
    simp only [exSet, mem_filter, mem_Icc]
    have h1 : p ≤ a * b + 1 :=
      le_trans (Nat.le_mul_self p) (Nat.le_of_dvd (Nat.succ_pos _) hd)
    have h2 : a * b + 1 ≤ N * b + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right b haN) 1
    exact ⟨⟨ha1, haN⟩, p, ⟨by omega, h1.trans h2⟩, hd⟩

/-- **Lemma A′(i).** -/
lemma card_midSet_le (N b pc Y : ℕ) :
    ((midSet N b pc Y).card : ℝ) ≤
      ∑ p ∈ midP pc Y (fun p => pc < p), ((N : ℝ) / (p * p) + 1) := by
  have h := classSieve_le N 1 0 pc Y 1 (witRoots b) (fun p => pc < p) one_pos one_pos
    (by norm_num) (witRoots_sub b) (fun p hp _ => card_witRoots_le hp)
    (fun p _ _ => Nat.coprime_one_left p)
  have hsmall : smallP pc (fun p => pc < p) = ∅ := by
    rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
  rw [hsmall] at h
  simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_one,
    Nat.mod_one, true_and, div_one, one_mul] at h
  have hset : midSet N b pc Y = (Icc 1 N).filter
      (fun a => ∃ p ≤ Y, p.Prime ∧ pc < p ∧ a % (p * p) ∈ witRoots b p) := rfl
  rw [hset]
  simpa using h

/-- **Lemma A′(iii)** for one class `t`. -/
lemma card_resPart_le (N b q t z pc : ℕ) (excl : Finset ℕ) (hq : 0 < q) (ht : t < q)
    (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p) :
    ((resPart N b q t pc excl).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
        ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
        ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1) := by
  have h := classSieve_le N q t z pc 1 (witRoots b) (· ∉ excl) hq ht (by norm_num)
    (witRoots_sub b) (fun p hp _ => card_witRoots_le hp) hcop
  simp only [Nat.cast_one, one_mul, Nat.reduceAdd, Nat.cast_ofNat] at h
  exact h

/-- **Lemma A′** for a part of `A` lying in the classes `Tset` mod `q`. -/
theorem badCount_le (N b q z pc Y : ℕ) (Tset excl : Finset ℕ) (Pa : ℕ → Prop) [DecidablePred Pa]
    (hb : 1 ≤ b) (hY : 1 ≤ Y) (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q)
    (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p)
    (hT : ∀ a, Pa a → a % q ∈ Tset) (hexcl : ∀ a, Pa a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (badCount N Pa b : ℝ) ≤
      Tset.card * ((N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
        ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
        ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1)) +
      ∑ p ∈ midP pc Y (fun p => pc < p), ((N : ℝ) / (p * p) + 1) +
      rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
  have hc := card_le_card (witness_cover N b q pc Y Tset excl Pa hT hexcl)
  have h1 := Finset.card_union_le (Tset.biUnion (fun t => resPart N b q t pc excl) ∪ midSet N b pc Y)
    (exSet N b Y)
  have h1' := Finset.card_union_le (Tset.biUnion (fun t => resPart N b q t pc excl)) (midSet N b pc Y)
  have h2 := card_biUnion_le (s := Tset) (t := fun t => resPart N b q t pc excl)
  have hcN : badCount N Pa b ≤ ∑ t ∈ Tset, (resPart N b q t pc excl).card +
      (midSet N b pc Y).card + (exSet N b Y).card := by
    unfold badCount; omega
  have hcR : (badCount N Pa b : ℝ) ≤ ∑ t ∈ Tset, ((resPart N b q t pc excl).card : ℝ) +
      ((midSet N b pc Y).card : ℝ) + ((exSet N b Y).card : ℝ) := by exact_mod_cast hcN
  have hres : ∑ t ∈ Tset, ((resPart N b q t pc excl).card : ℝ) ≤ ∑ _t ∈ Tset,
      ((N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
        ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
        ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1)) :=
    sum_le_sum (fun t ht => card_resPart_le N b q t z pc excl hq (hTq t ht) hcop)
  rw [sum_const, nsmul_eq_mul] at hres
  have := card_midSet_le N b pc Y
  have := card_exSet_le N b Y hb hY
  linarith

/- ### Lemma B -/

lemma isU1_odd {p : ℕ} (h : IsU1 p) : p ≠ 2 := by have := h.2.1; omega

/-- The restricted part of Lemma B for one class `t`. -/
def vResPart (N q t pB : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => x % q = t ∧ ∃ p ≤ pB, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)

/-- The medium part of Lemma B (no class restriction). -/
def vMidSet (N pB Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ p ≤ Y, p.Prime ∧ (IsU1 p ∧ pB < p) ∧ x % (p * p) ∈ sqRoots p)

/-- The Pell part of Lemma B. -/
def vPellSet (N Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)

lemma v_cover (N q pB Y : ℕ) (Tset : Finset ℕ) (Px : ℕ → Prop) [DecidablePred Px]
    (hT : ∀ x, Px x → x % q ∈ Tset) (hstar : ∀ x, Px x → IsStar x) :
    (Icc 1 N).filter (fun x => Px x ∧ ¬ Squarefree (x * x + 1)) ⊆
      (Tset.biUnion (fun t => vResPart N q t pB) ∪ vMidSet N pB Y) ∪ vPellSet N Y := by
  intro x hx
  simp only [mem_filter, mem_Icc] at hx
  obtain ⟨⟨hx1, hxN⟩, hPx, hsq⟩ := hx
  obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd hsq
  have hU := isU1_of_sq_dvd hp hd (hstar x hPx)
  have hR : x % (p * p) ∈ sqRoots p := (mod_mem_sqRoots hp.pos x).mpr hd
  by_cases hpB : p ≤ pB
  · apply mem_union_left; apply mem_union_left
    simp only [mem_biUnion, vResPart, mem_filter, mem_Icc]
    exact ⟨x % q, hT x hPx, ⟨hx1, hxN⟩, rfl, p, hpB, hp, hU, hR⟩
  by_cases hpY : p ≤ Y
  · apply mem_union_left; apply mem_union_right
    simp only [vMidSet, mem_filter, mem_Icc]
    exact ⟨⟨hx1, hxN⟩, p, hpY, hp, ⟨hU, by omega⟩, hR⟩
  · apply mem_union_right
    simp only [vPellSet, mem_filter, mem_Icc]
    have h1 : p * p ≤ x * x + 1 := Nat.le_of_dvd (Nat.succ_pos _) hd
    have h2 : x * x + 1 ≤ N * N + 1 := Nat.add_le_add_right (Nat.mul_le_mul hxN hxN) 1
    have h3 : p ≤ N + 1 := by
      by_contra hc; push Not at hc
      have : (N + 2) * (N + 2) ≤ p * p := Nat.mul_le_mul hc hc
      nlinarith
    refine ⟨⟨hx1, hxN⟩, p, ⟨by omega, h3⟩, ?_⟩
    rw [sq]; exact hd

/-- **Lemma B.** -/
theorem vCount_le (N q zB pB Y : ℕ) (Tset : Finset ℕ) (Px : ℕ → Prop) [DecidablePred Px]
    (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q) (hcop : ∀ p, p.Prime → IsU1 p → Nat.Coprime q p)
    (hT : ∀ x, Px x → x % q ∈ Tset) (hstar : ∀ x, Px x → IsStar x) :
    (vCount N Px : ℝ) ≤
      Tset.card * ((N : ℝ) / q * (1 - ∏ p ∈ smallP zB IsU1, (1 - 2 / ((p : ℝ) * p))) +
        ((3 : ℝ) ^ (smallP zB IsU1).card - 1) +
        ∑ p ∈ midP zB pB IsU1, (2 * ((N : ℝ) / q / (p * p)) + 2)) +
      ∑ p ∈ midP pB Y (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
      (((N ^ 2 + 1) / (Y + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
  have hc := card_le_card (v_cover N q pB Y Tset Px hT hstar)
  have h1 := Finset.card_union_le (Tset.biUnion (fun t => vResPart N q t pB) ∪ vMidSet N pB Y)
    (vPellSet N Y)
  have h1' := Finset.card_union_le (Tset.biUnion (fun t => vResPart N q t pB)) (vMidSet N pB Y)
  have h2 := card_biUnion_le (s := Tset) (t := fun t => vResPart N q t pB)
  have hcN : vCount N Px ≤ ∑ t ∈ Tset, (vResPart N q t pB).card +
      (vMidSet N pB Y).card + (vPellSet N Y).card := by
    unfold vCount; omega
  have hcR : (vCount N Px : ℝ) ≤ ∑ t ∈ Tset, ((vResPart N q t pB).card : ℝ) +
      ((vMidSet N pB Y).card : ℝ) + ((vPellSet N Y).card : ℝ) := by exact_mod_cast hcN
  have hres : ∀ t ∈ Tset, ((vResPart N q t pB).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ smallP zB IsU1, (1 - 2 / ((p : ℝ) * p))) +
        ((3 : ℝ) ^ (smallP zB IsU1).card - 1) +
        ∑ p ∈ midP zB pB IsU1, (2 * ((N : ℝ) / q / (p * p)) + 2) := by
    intro t ht
    have h := classSieve_le N q t zB pB 2 (fun p => sqRoots p) IsU1 hq (hTq t ht) (by norm_num)
      sqRoots_sub (fun p hp hU => card_sqRoots_le hp (isU1_odd hU)) hcop
    simp only [Nat.cast_ofNat, Nat.reduceAdd] at h
    exact h
  have hres' := sum_le_sum hres
  rw [sum_const, nsmul_eq_mul] at hres'
  have hmid : ((vMidSet N pB Y).card : ℝ) ≤
      ∑ p ∈ midP pB Y (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) := by
    have h := classSieve_le N 1 0 pB Y 2 (fun p => sqRoots p) (fun p => IsU1 p ∧ pB < p)
      one_pos one_pos (by norm_num) sqRoots_sub
      (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1)) (fun p _ _ => Nat.coprime_one_left p)
    have hsmall : smallP pB (fun p => IsU1 p ∧ pB < p) = ∅ := by
      rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
    rw [hsmall] at h
    simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_ofNat,
      Nat.mod_one, true_and] at h
    simpa [vMidSet] using h
  have hpell : ((vPellSet N Y).card : ℝ) ≤
      (((N ^ 2 + 1) / (Y + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
    exact_mod_cast pellTail_le N Y
  linarith

end Erdos848
end

section

/-
# Phase 6: an explicit prime-counting bound from Chebyshev's `θ(x) ≤ x log 4`

`card_primesLE_le : #{p ≤ n prime} ≤ √n + 2 log 4 · n / log n` for `n ≥ 2`.

This is the only prime-counting bound the analytic certificates need beyond exact prime counts
(`code/n0_exact.py --cheb`); it replaces the Rosser–Schoenfeld bound, which is not in Mathlib.
-/

namespace Erdos848

open Real Finset Chebyshev

theorem card_primesLE_le (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.primesLE n).card : ℝ) ≤ √(n : ℝ) + 2 * log 4 * n / log n := by
  set s := Nat.sqrt n with hs
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 < log (n : ℝ) := log_pos hn1
  have hsplit := card_filter_add_card_filter_not (s := Nat.primesLE n) (fun p => p ≤ s)
  -- primes ≤ √n
  have h1 : (((Nat.primesLE n).filter (fun p => p ≤ s)).card : ℝ) ≤ √(n : ℝ) := by
    have hc : ((Nat.primesLE n).filter (fun p => p ≤ s)).card ≤ s := by
      calc ((Nat.primesLE n).filter (fun p => p ≤ s)).card ≤ (Icc 1 s).card := by
            apply card_le_card
            intro p hp
            simp only [mem_filter, Nat.mem_primesLE] at hp
            simp only [mem_Icc]
            exact ⟨hp.1.2.one_lt.le, hp.2⟩
        _ = s := by simp
    calc (((Nat.primesLE n).filter (fun p => p ≤ s)).card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hc
      _ ≤ √(n : ℝ) := Real.nat_sqrt_le_real_sqrt
  -- primes > √n: each has log p ≥ (log n) / 2
  set L := (Nat.primesLE n).filter (fun p => ¬ p ≤ s) with hL
  have hlogp : ∀ p ∈ L, log (n : ℝ) / 2 ≤ log p := by
    intro p hp
    simp only [hL, mem_filter, Nat.mem_primesLE, not_le] at hp
    have hsp : s + 1 ≤ p := hp.2
    have hlt : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
    have hnp : (n : ℝ) ≤ (p : ℝ) ^ 2 := by
      have : n ≤ p * p := le_trans hlt.le (Nat.mul_le_mul hsp hsp)
      rw [sq]; exact_mod_cast this
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.2.pos
    have := Real.log_le_log (by positivity) hnp
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have h2 : (L.card : ℝ) * (log (n : ℝ) / 2) ≤ log 4 * n := by
    calc (L.card : ℝ) * (log (n : ℝ) / 2) = ∑ _p ∈ L, (log (n : ℝ) / 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ L, log (p : ℝ) := sum_le_sum hlogp
      _ ≤ ∑ p ∈ Nat.primesLE n, log (p : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro p hp _
          exact log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le)
      _ = θ n := (theta_eq_sum_primesLE_log n).symm
      _ ≤ log 4 * n := theta_le_log4_mul_x (by positivity)
  have h3 : (L.card : ℝ) ≤ 2 * log 4 * n / log n := by
    rw [le_div_iff₀ hlogn]
    linarith
  have hsplit' : ((Nat.primesLE n).card : ℝ) =
      (((Nat.primesLE n).filter (fun p => p ≤ s)).card : ℝ) + (L.card : ℝ) := by
    rw [← hsplit]; push_cast; ring
  rw [hsplit']
  linarith

end Erdos848
end

section
/-
# Executable part of the prime table (core Lean only, precompiled)

Everything here is plain structural recursion so that it can be reasoned about in
`Erdos848/PrimeTable.lean`.  The primality test only needs to accept every prime
(`Erdos848.isPrimeB_of_prime`); accepting a composite would only weaken the bounds.
-/

namespace ErdosComp

/-- Trial division by `k, k+2, k+4, …` (with fuel); returns `n` if no divisor is found. -/
def minFacAux (n : Nat) : Nat → Nat → Nat
  | _, 0 => n
  | k, f + 1 => if n < k * k then n else if n % k == 0 then k else minFacAux n (k + 2) f

def isPrimeB (n : Nat) : Bool :=
  if n < 2 then false else if n % 2 == 0 then n == 2 else minFacAux n 3 n == n

def isU1B (n : Nat) : Bool := isPrimeB n && n % 4 == 1 && 13 ≤ n

/-- Scale for the reciprocal squares. -/
def KS : Nat := 10 ^ 30

/-- `⌈K/p²⌉`. -/
def ceilK (p : Nat) : Nat := (KS + p * p - 1) / (p * p)

structure PSt where
  cp : Nat
  cu : Nat
  fp : Nat
  fu : Nat

def stepSt (n : Nat) (s : PSt) : PSt :=
  if isPrimeB n then
    if isU1B n then ⟨s.cp + 1, s.cu + 1, s.fp + ceilK n, s.fu + ceilK n⟩
    else ⟨s.cp + 1, s.cu, s.fp + ceilK n, s.fu⟩
  else s

/-- The state after processing `1, …, n` (specification; slow). -/
def stAt : Nat → PSt
  | 0 => ⟨0, 0, 0, 0⟩
  | n + 1 => stepSt (n + 1) (stAt n)

/-- `k` more steps from position `n` (tail recursive). -/
def advance : Nat → Nat → PSt → PSt
  | 0, _, s => s
  | k + 1, n, s => advance k (n + 1) (stepSt (n + 1) s)

/-- One pass through the requested points (in increasing order). -/
def evalPts : List Nat → Nat → PSt → List (Nat × PSt)
  | [], _, _ => []
  | x :: xs, n, s =>
    (n + (x - n), advance (x - n) n s) :: evalPts xs (n + (x - n)) (advance (x - n) n s)

/-- Look a point up in the table (falling back to the specification). -/
def lookD (tab : List (Nat × PSt)) (x : Nat) : PSt :=
  match tab.find? (fun e => e.1 == x) with
  | some e => e.2
  | none => stAt x

end ErdosComp
end

section

/-
# The computational part (executable)

* `sqfTest n` — a squarefreeness test whose `true` answers are proved correct
  (`Erdos848/CompSound.lean`): trial division by all primes `p` with `p³ ≤ n`, then a perfect
  square test for the cofactor.
* `buildMarks X cert` — marks every `w ≤ X` that could have `w² + 1` non-squarefree: for every
  `p ≡ 1 (mod 4)`, `5 ≤ p ≤ X`, the certificate gives either a root `r² ≡ -1 (mod p²)` (then the
  two classes `±r mod p²` are marked) or a proper factor of `p`.
* `runFrom` — the guarded colouring: an *untrusted* proposer suggests operations, each of which
  is checked (classes stay pairwise compatible, at most `c₇(N)` classes, every marked `N` is
  coloured).
-/

namespace ErdosComp

/- ### Squarefreeness -/

/-- Bound for the trial division: `D³ ≥ (1.6·10⁸)² + 1`. -/
def DTr : Nat := 300000

/-- All primes `≤ DTr`, increasing. -/
def plist : List Nat := (List.range (DTr + 1)).filter isPrimeB

def isSq (m : Nat) : Bool := Nat.sqrt m * Nat.sqrt m == m

/-- Trial division of `rem` (initially `n`) by the primes `p` with `p³ ≤ n`. -/
def sqfGo (n : Nat) : Nat → List Nat → Bool
  | rem, [] => !(1 < rem && isSq rem)
  | rem, p :: ps =>
    if n < p * p * p then !(1 < rem && isSq rem)
    else if rem % p == 0 then (if rem / p % p == 0 then false else sqfGo n (rem / p) ps)
    else sqfGo n rem ps

def sqfTest (n : Nat) : Bool := decide (0 < n) && decide (n ≤ DTr * DTr * DTr) && sqfGo n n plist

/- ### Marks for `V` -/

/-- Mark `r, r + m, r + 2m, … ≤ X`. -/
def markProg (X m : Nat) : Nat → Nat → Array Bool → Array Bool
  | 0, _, a => a
  | f + 1, w, a => if X < w then a else markProg X m f (w + m) (a.set! w true)

/-- Process `p = 5, 9, 13, …` (`k` more values). `cert p = (0, r)` (a root) or `(1, d)` (a factor). -/
def markLoop (X : Nat) (cert : Nat → Nat × Nat) : Nat → Nat → Array Bool → Option (Array Bool)
  | 0, _, a => some a
  | k + 1, p, a =>
    let c := cert p
    if c.1 == 0 then
      let r := c.2
      if r < p * p && (r * r + 1) % (p * p) == 0 then
        let a := markProg X (p * p) (X / (p * p) + 2) r a
        let a := markProg X (p * p) (X / (p * p) + 2) (p * p - r) a
        markLoop X cert k (p + 4) a
      else none
    else if c.1 == 1 && 1 < c.2 && c.2 < p && p % c.2 == 0 then markLoop X cert k (p + 4) a
    else none

def buildMarks (X : Nat) (cert : Nat → Nat × Nat) : Option (Array Bool) :=
  markLoop X cert (X / 4 + 1) 5 (Array.replicate (X + 1) false)

/- ### Untrusted certificates for `buildMarks` -/

def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut b := b % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r

/-- Smallest factor `≤ √p` (or `p`). -/
def smallFactor (p : Nat) : Nat := Id.run do
  if p % 2 == 0 then return 2
  let mut d := 3
  while d * d ≤ p do
    if p % d == 0 then return d
    d := d + 2
  return p

def certGen (p : Nat) : Nat × Nat := Id.run do
  let d := smallFactor p
  if d < p then return (1, d)
  -- p prime, p ≡ 1 (mod 4): a square root of -1 mod p, lifted to p²
  let mut g := 2
  let mut r0 := 0
  while g < p do
    let x := powMod g ((p - 1) / 4) p
    if x * x % p == p - 1 then r0 := x; break
    g := g + 1
  let c := ((r0 * r0 + 1) / p) % p
  let inv := powMod (2 * r0 % p) (p - 2) p
  let k := (p - c) % p * inv % p
  return (0, (r0 + p * k) % (p * p))

/- ### Guarded colouring -/

inductive Op where
  | opn (v : Nat)
  | place (v c : Nat)
  | move (u c₁ c₂ : Nat)

def c7C (N : Nat) : Nat := (N + 18) / 25

def compatB (v : Nat) (arr : Array Nat) : Bool := arr.all (fun u => u == v || sqfTest (u * v + 1))

def applyOp (N : Nat) (cls : Array (Array Nat)) : Op → Option (Array (Array Nat))
  | .opn v => if cls.size + 1 ≤ c7C N then some (cls.push #[v]) else none
  | .place v c =>
    if h : c < cls.size then (if compatB v cls[c] then some (cls.modify c (·.push v)) else none)
    else none
  | .move u c₁ c₂ =>
    if h₁ : c₁ < cls.size then
      if h₂ : c₂ < cls.size then
        if c₁ != c₂ && cls[c₁].contains u && compatB u cls[c₂] then
          some ((cls.modify c₁ (·.erase u)).modify c₂ (·.push u))
        else none
      else none
    else none

def applyOps (N : Nat) : Array (Array Nat) → List Op → Option (Array (Array Nat))
  | cls, [] => some cls
  | cls, op :: ops => match applyOp N cls op with
    | some cls' => applyOps N cls' ops
    | none => none

/-- `prop aux cls v = (ops, c, aux')`: operations for step `v`, and the class that should then
contain `v`. -/
def runFrom {Aux : Type} (prop : Aux → Array (Array Nat) → Nat → List Op × Nat × Aux)
    (marks : Array Bool) : Nat → Nat → Aux → Array (Array Nat) → Bool
  | 0, _, _, _ => true
  | k + 1, v, aux, cls =>
    let r := prop aux cls v
    match applyOps v cls r.1 with
    | none => false
    | some cls' =>
      (if marks.getD v true then (if h : r.2.1 < cls'.size then cls'[r.2.1].contains v else false)
        else true) &&
      runFrom prop marks k (v + 1) r.2.2 cls'

end ErdosComp
end

section
namespace LowSieve
open Finset
-- Repeat a bit at multiples of p, using binary doubling.
def rep (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => let x := rep p k; x ||| (x <<< (p*2^k))
lemma rep_sound {p k i : ℕ} (h : (rep p k).testBit i = true) : p ∣ i := by
  induction k generalizing i with
  | zero => cases i with
    | zero => exact dvd_zero _
    | succ i => simp [rep, Nat.testBit_add_one] at h
  | succ k ih =>
    simp only [rep, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h1,h2⟩
    · exact ih h
    · have := dvd_add (dvd_mul_right p (2^k)) (ih h2)
      rwa [Nat.add_sub_of_le h1] at this

def pop : ℕ → ℕ → ℕ
  | 0, x => x % 2
  | k+1, x => let n := 2^k; pop k (x % (2^n)) + pop k (x >>> n)
lemma pop_eq (k x : ℕ) : pop k x = Nat.count (fun i => x.testBit i = true) (2^k) := by
  induction k generalizing x with
  | zero => simp [pop, Nat.count_one, Nat.testBit_eq_decide_div_mod_eq]; split <;> omega
  | succ k ih =>
    rw [pow_succ, Nat.mul_two, Nat.count_add, pop, ih, ih]; congr 1
    · rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]; congr 1
      apply filter_congr; intro i hi
      simp [Nat.testBit_mod_two_pow, mem_range.mp hi]
    · simp

def bad (w p : ℕ) := rep p ((w / p).log2 + 1) <<< (2*p)
lemma bad_false (w p n : ℕ) (hp : 2 ≤ p) (hn : n.Prime) : (bad w p).testBit n = false := by
  simp only [bad, Nat.testBit_shiftLeft, Bool.and_eq_false_imp, decide_eq_true_eq]
  intro h1
  apply Bool.eq_false_iff.mpr
  intro h2
  have hd := dvd_add (dvd_mul_left p 2) (rep_sound h2)
  rw [Nat.add_sub_of_le h1] at hd
  rcases (Nat.dvd_prime hn).mp hd with h | h <;> omega

def cover (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | p::ps => bad w p ||| cover w ps
lemma cover_false {w n : ℕ} {ps : List ℕ} (h : ∀ p ∈ ps, 2 ≤ p) (hn : n.Prime) :
    (cover w ps).testBit n = false := by
  induction ps with
  | nil => simp [cover]
  | cons p ps ih => simp [cover, bad_false w p n (h p (by simp)) hn, ih (fun q hq => h q (by simp [hq]))]

def mask (w : ℕ) (ps : List ℕ) (u : Bool) :=
  let b := cover w ps ||| (if u then rep 4 (w.log2+1) <<< 3 else 0)
  (2^w-1) ^^^ (b % (2^w))
lemma mask_true {w n : ℕ} {ps : List ℕ} {u : Bool} (hp : ∀ p ∈ ps, 2 ≤ p) (hn : n.Prime)
    (hw : n < w) (hu : u = true → n%4 = 1) : (mask w ps u).testBit n = true := by
  have h : (if u then rep 4 (w.log2+1) <<< 3 else 0).testBit n = false := by
    cases u with
    | false => simp
    | true =>
      simp only [Bool.true_eq, ↓reduceIte, Nat.testBit_shiftLeft, Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hn3
      apply Bool.eq_false_iff.mpr
      intro ht
      have := rep_sound ht
      have := hu rfl
      omega
  simp [mask, Nat.testBit_mod_two_pow, hw, cover_false hp hn, h]

def upper (w k : ℕ) (ps : List ℕ) (u : Bool) := pop k (mask w ps u)
lemma upper_sound {w k : ℕ} {ps : List ℕ} {u : Bool} {S : Finset ℕ} (h : ∀ p ∈ ps, 2 ≤ p)
    (hw : w ≤ 2^k) (hs : ∀ n ∈ S, n < w ∧ n.Prime ∧ (u = true → n%4=1)) : S.card ≤ upper w k ps u := by
  rw [upper, pop_eq, Nat.count_eq_card_filter_range]; apply card_le_card
  intro n hn
  obtain ⟨hlt, hp, hu⟩ := hs n hn
  exact mem_filter.mpr ⟨mem_range.mpr (hlt.trans_le hw), mask_true h hp hlt hu⟩




-- Segmented sieve on [a, a+S)
def offs (a p : ℕ) : ℕ := max (2*p) (a + (p - a % p) % p) - a
lemma offs_spec (a p : ℕ) (hp : 2 ≤ p) : p ∣ a + offs a p ∧ 2*p ≤ a + offs a p := by
  have hr := Nat.mod_lt a (show 0 < p by omega)
  have ha := Nat.div_add_mod a p
  have hd : p ∣ a + (p - a % p) % p := by
    rcases Nat.eq_zero_or_pos (a % p) with h0 | h0
    · rw [h0, Nat.sub_zero, Nat.mod_self, add_zero]; exact Nat.dvd_of_mod_eq_zero h0
    · rw [Nat.mod_eq_of_lt (by omega : p - a % p < p)]; exact ⟨a / p + 1, by rw [Nat.mul_add]; omega⟩
  unfold offs
  rw [Nat.add_sub_of_le (le_trans (Nat.le_add_right _ _) (le_max_right _ _))]
  refine ⟨?_, le_max_left _ _⟩
  rcases le_total (2*p) (a + (p - a % p) % p) with h | h
  · rw [max_eq_right h]; exact hd
  · rw [max_eq_left h]; exact dvd_mul_left _ _

def segBad (a S p : ℕ) : ℕ := rep p ((S / p).log2 + 1) <<< offs a p
lemma segBad_false (a S p i : ℕ) (hp : 2 ≤ p) (hn : (a+i).Prime) : (segBad a S p).testBit i = false := by
  simp only [segBad, Nat.testBit_shiftLeft, Bool.and_eq_false_imp, decide_eq_true_eq]
  intro h1
  apply Bool.eq_false_iff.mpr
  intro h2
  obtain ⟨hd, hge⟩ := offs_spec a p hp
  have hd2 := dvd_add hd (rep_sound h2)
  rw [show a + offs a p + (i - offs a p) = a + i by omega] at hd2
  rcases (Nat.dvd_prime hn).mp hd2 with h | h <;> omega

def segCover (a S : ℕ) : List ℕ → ℕ
  | [] => 0
  | p::ps => segBad a S p ||| segCover a S ps
lemma segCover_false {a S i : ℕ} {ps : List ℕ} (h : ∀ p ∈ ps, 2 ≤ p) (hn : (a+i).Prime) :
    (segCover a S ps).testBit i = false := by
  induction ps with
  | nil => simp [segCover]
  | cons p ps ih => simp [segCover, segBad_false a S p i (h p (by simp)) hn, ih (fun q hq => h q (by simp [hq]))]

def off3 (a : ℕ) : ℕ := (7 - a % 4) % 4
def segMask (a S : ℕ) (ps : List ℕ) (u : Bool) : ℕ :=
  let b := segCover a S ps ||| (if u then rep 4 (S.log2+1) <<< off3 a else 0)
  (2^S-1) ^^^ (b % (2^S))
lemma segMask_true {a S i : ℕ} {ps : List ℕ} {u : Bool} (hp : ∀ p ∈ ps, 2 ≤ p) (hn : (a+i).Prime)
    (hw : i < S) (hu : u = true → (a+i)%4 = 1) : (segMask a S ps u).testBit i = true := by
  have h : (if u then rep 4 (S.log2+1) <<< off3 a else 0).testBit i = false := by
    cases u with
    | false => simp
    | true =>
      simp only [↓reduceIte, Nat.testBit_shiftLeft, Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hn3
      apply Bool.eq_false_iff.mpr
      intro ht
      have h4 := rep_sound ht
      have := hu rfl
      unfold off3 at hn3 h4
      omega
  simp [segMask, Nat.testBit_mod_two_pow, hw, segCover_false hp hn, h]

/-- Counting function bound on a segment. -/
def segCnt (a S k : ℕ) (ps : List ℕ) (u : Bool) : ℕ := pop k (segMask a S ps u)
def PPred (u : Bool) (n : ℕ) : Prop := n.Prime ∧ (u = true → n % 4 = 1)
instance (u : Bool) : DecidablePred (PPred u) := fun n => by unfold PPred; infer_instance
lemma segCnt_sound {a S k : ℕ} {ps : List ℕ} {u : Bool} (h : ∀ p ∈ ps, 2 ≤ p) (hS : S ≤ 2^k) :
    ((Ico a (a+S)).filter (PPred u)).card ≤ segCnt a S k ps u := by
  rw [segCnt, pop_eq, Nat.count_eq_card_filter_range]
  calc ((Ico a (a+S)).filter (PPred u)).card
      = (((range S).filter (fun i => PPred u (a+i))).map (addLeftEmbedding a)).card := by
        congr 1; ext n; simp only [mem_filter, mem_Ico, mem_map, mem_range, addLeftEmbedding_apply]
        constructor
        · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨n-a, ⟨by omega, by rwa [Nat.add_sub_of_le h1]⟩, by omega⟩
        · rintro ⟨i,⟨h1,h2⟩,rfl⟩; exact ⟨⟨by omega, by omega⟩, h2⟩
    _ = ((range S).filter (fun i => PPred u (a+i))).card := card_map _
    _ ≤ _ := by
      apply card_le_card; intro i hi
      simp only [mem_filter, mem_range] at hi ⊢
      exact ⟨lt_of_lt_of_le hi.1 hS, segMask_true h hi.2.1 hi.1 hi.2.2⟩

-- Arithmetic popcount: x - Σ_{i=1}^{K} ⌊x/2^i⌋
def shSum (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | K+1 => shSum x K + (x >>> (K+1))
def popA (K x : ℕ) : ℕ := x - shSum x K
lemma popA_eq (K x : ℕ) (hx : x < 2^K) :
    popA K x = ((range K).filter (fun i => x.testBit i = true)).card := by
  have key : ∀ K, ((range K).filter (fun i => x.testBit i = true)).card + shSum x K
      + x / 2^K = x := by
    intro K
    induction K with
    | zero => simp [shSum]
    | succ K ih =>
      rw [Finset.range_add_one, filter_insert]
      have hb : (x / 2^K) % 2 + 2 * (x / 2^(K+1)) = x / 2^K := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega
      have hnot : K ∉ (range K).filter (fun i => x.testBit i = true) := by simp
      simp only [shSum, Nat.shiftRight_eq_div_pow]
      by_cases ht : x.testBit K = true
      · rw [if_pos ht, card_insert_of_notMem hnot]
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at ht
        omega
      · rw [if_neg ht]
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at ht
        omega
  have := key K
  rw [Nat.div_eq_of_lt hx] at this
  unfold popA; omega

def segCntA (a S k : ℕ) (ps : List ℕ) (u : Bool) : ℕ := popA k (segMask a S ps u)
lemma segMask_lt (a S : ℕ) (ps : List ℕ) (u : Bool) : segMask a S ps u < 2^S := by
  unfold segMask
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]; omega
lemma segCntA_sound {a S : ℕ} {ps : List ℕ} {u : Bool} (h : ∀ p ∈ ps, 2 ≤ p) :
    ((Ico a (a+S)).filter (PPred u)).card ≤ segCntA a S S ps u := by
  rw [segCntA, popA_eq S _ (segMask_lt a S ps u)]
  calc ((Ico a (a+S)).filter (PPred u)).card
      = (((range S).filter (fun i => PPred u (a+i))).map (addLeftEmbedding a)).card := by
        congr 1; ext n; simp only [mem_filter, mem_Ico, mem_map, mem_range, addLeftEmbedding_apply]
        constructor
        · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨n-a, ⟨by omega, by rwa [Nat.add_sub_of_le h1]⟩, by omega⟩
        · rintro ⟨i,⟨h1,h2⟩,rfl⟩; exact ⟨⟨by omega, by omega⟩, h2⟩
    _ = ((range S).filter (fun i => PPred u (a+i))).card := card_map _
    _ ≤ _ := by
      apply card_le_card; intro i hi
      simp only [mem_filter, mem_range] at hi ⊢
      exact ⟨hi.1, segMask_true h hi.2.1 hi.1 hi.2.2⟩

-- SWAR popcount (log-depth, kernel friendly)
def fsum (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | K+1, y => y % 2^b + fsum b K (y / 2^b)
def msk (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | K+1 => 2^(2*b) * msk b K + (2^b - 1)
def mskD (b : ℕ) : ℕ → ℕ
  | 0 => 2^b - 1
  | n+1 => let m := mskD b n; m ||| (m <<< (2*b*2^n))
def stp (m b y : ℕ) : ℕ := (y &&& m) + ((y >>> b) &&& m)
def go : ℕ → ℕ → ℕ → ℕ
  | 0, b, y => y % 2^b
  | n+1, b, y => go n (2*b) (stp (mskD b n) b y)

lemma and_split (y c m s : ℕ) (hc : c < 2^s) :
    y &&& (2^s * m + c) = 2^s * ((y >>> s) &&& m) + (y &&& c) := by
  apply Nat.eq_of_testBit_eq; intro j
  have h1 : y &&& c < 2^s := Nat.and_lt_two_pow _ hc
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hc, Nat.testBit_two_pow_mul_add _ h1]
  split_ifs with hj
  · simp
  · simp [Nat.testBit_shiftRight]; congr 2; omega

lemma msk_lt (b K : ℕ) : msk b K < 2^(2*b*K) := by
  induction K with
  | zero => simp [msk]
  | succ K ih =>
    simp only [msk]
    have : 2^b - 1 < 2^(2*b) := lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) one_pos) (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc 2^(2*b) * msk b K + (2^b - 1) < 2^(2*b) * msk b K + 2^(2*b) := by omega
      _ = 2^(2*b) * (msk b K + 1) := by ring
      _ ≤ 2^(2*b) * 2^(2*b*K) := Nat.mul_le_mul_left _ ih
      _ = 2^(2*b*(K+1)) := by rw [← pow_add]; ring_nf

lemma msk_add (b K L : ℕ) : msk b (L + K) = 2^(2*b*K) * msk b L + msk b K := by
  induction K with
  | zero => simp [msk]
  | succ K ih =>
    rw [← add_assoc, msk, ih, msk]
    rw [show 2*b*(K+1) = 2*b + 2*b*K by ring, pow_add]; ring

lemma mskD_eq (b n : ℕ) : mskD b n = msk b (2^n) := by
  induction n with
  | zero => simp [mskD, msk]
  | succ n ih =>
    simp only [mskD, ih]
    rw [pow_succ, mul_two, msk_add, Nat.shiftLeft_eq, mul_comm (msk b (2^n)), Nat.or_comm]
    exact (Nat.two_pow_add_eq_or_of_lt (msk_lt b _) _).symm

lemma stp_msk (b K y : ℕ) (hb : 1 ≤ b) :
    stp (msk b (K+1)) b y = 2^(2*b) * stp (msk b K) b (y / 2^(2*b)) + (y % 2^b + (y / 2^b) % 2^b) := by
  have hc : 2^b - 1 < 2^(2*b) := lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) one_pos) (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [stp, msk, and_split _ _ _ _ hc, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul, ← pow_add, show b + 2*b = 2*b + b by ring, pow_add, ← Nat.div_div_eq_div_mul]
  ring

lemma fsum_stp (b K y : ℕ) (hb : 1 ≤ b) : fsum (2*b) K (stp (msk b K) b y) = fsum b (2*K) y := by
  induction K generalizing y with
  | zero => simp [fsum]
  | succ K ih =>
    rw [stp_msk b K y hb, show 2*(K+1) = (2*K+1)+1 by ring, fsum, fsum, fsum]
    have hlt : y % 2^b + (y / 2^b) % 2^b < 2^(2*b) := by
      have := Nat.mod_lt y (Nat.two_pow_pos b); have := Nat.mod_lt (y / 2^b) (Nat.two_pow_pos b)
      have : 2^b + 2^b ≤ 2^(2*b) := by
        rw [← two_mul, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, add_zero, ih,
      Nat.div_div_eq_div_mul, ← pow_add, show b + b = 2*b by ring]
    ring

lemma go_eq (n b y : ℕ) (hb : 1 ≤ b) : go n b y = fsum b (2^n) y := by
  induction n generalizing b y with
  | zero => simp [go, fsum]
  | succ n ih =>
    rw [go, ih _ _ (by omega), mskD_eq, fsum_stp b _ y hb, pow_succ]; ring_nf

lemma fsum_one (K y : ℕ) : fsum 1 K y = Nat.count (fun i => y.testBit i = true) K := by
  induction K generalizing y with
  | zero => simp [fsum]
  | succ K ih =>
    rw [fsum, ih, Nat.count_succ']
    simp only [Nat.testBit_zero, decide_eq_true_eq, pow_one, ← Nat.testBit_div_two]
    split_ifs <;> omega

def popc (n y : ℕ) : ℕ := go n 1 y
lemma popc_eq (n y : ℕ) : popc n y = Nat.count (fun i => y.testBit i = true) (2^n) := by
  rw [popc, go_eq n 1 y le_rfl, fsum_one]

def segCntC (a S k : ℕ) (ps : List ℕ) (u : Bool) : ℕ := popc k (segMask a S ps u)
lemma segCntC_sound {a S k : ℕ} {ps : List ℕ} {u : Bool} (h : ∀ p ∈ ps, 2 ≤ p) (hS : S ≤ 2^k) :
    ((Ico a (a+S)).filter (PPred u)).card ≤ segCntC a S k ps u := by
  have := segCnt_sound (k := k) (a := a) h hS (u := u)
  rwa [segCnt, pop_eq, ← popc_eq] at this
end LowSieve
end

namespace ErdosComp
set_option maxRecDepth 100000 in
/-- Sieving primes for the segmented prime count (soundness only needs `2 ≤ p`). -/
def SPR : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999,3001,3011,3019,3023,3037,3041,3049,3061,3067,3079,3083,3089,3109,3119,3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313,3319,3323,3329,3331,3343,3347,3359,3361,3371,3373,3389,3391,3407,3413,3433,3449,3457,3461,3463,3467,3469,3491,3499,3511,3517,3527,3529,3533,3539,3541,3547,3557,3559,3571,3581,3583,3593,3607,3613,3617,3623,3631,3637,3643,3659,3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793,3797,3803,3821,3823,3833,3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929,3931,3943,3947,3967,3989,4001,4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079,4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,4231,4241,4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349,4357,4363,4373,4391,4397,4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523,4547,4549,4561,4567,4583,4591,4597,4603,4621,4637,4639,4643,4649,4651,4657,4663,4673,4679,4691,4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801,4813,4817,4831,4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969,4973,4987,4993,4999,5003,5009,5011,5021,5023,5039,5051,5059,5077,5081,5087,5099,5101,5107,5113,5119,5147,5153,5167,5171,5179,5189,5197,5209,5227,5231,5233,5237,5261,5273,5279,5281,5297,5303,5309,5323,5333,5347,5351,5381,5387,5393,5399,5407,5413,5417,5419,5431,5437,5441,5443,5449,5471,5477,5479,5483,5501,5503,5507,5519,5521,5527,5531,5557,5563,5569,5573,5581,5591,5623,5639,5641,5647,5651,5653,5657,5659,5669,5683,5689,5693,5701,5711,5717,5737,5741,5743,5749]
/-- Upper bound for the number of primes (`u`: primes `≡ 1 mod 4`) in `[a, a+len)`. -/
def ccnt (u : Bool) (_f a len : Nat) := if len ≤ 2^18 then LowSieve.segCntC a len 18 SPR u else len
set_option maxRecDepth 100000 in
/-- Prime-count table `(X, c, c')`: `#{p ≤ X prime} ≤ c`, `#{p ≤ X prime, p ≡ 1 (4)} ≤ c'`. -/
def GRID : List (Nat × Nat × Nat) := [(10315, 1266, 627), (10896, 1326, 655), (11255, 1361, 672), (12070, 1445, 712), (2097152, 155612, 77781), (2180391, 161351, 80619), (2200504, 162694, 81302), (2242025, 165537, 82710), (2434336, 178614, 89202), (2452644, 179864, 89829), (2484824, 182031, 90929), (2942026, 212930, 106352), (2984016, 215741, 107762), (2997538, 216642, 108203), (3923628, 278152, 138997), (3944157, 279528, 139691), (3997661, 282992, 141425), (4194304, 295948, 147938), (6088338, 418491, 209155), (6120195, 420547, 210169), (6203217, 425859, 212829), (6291456, 431503, 215680), (7326303, 497329, 248557), (7478251, 506904, 253305), (7517380, 509355, 254544), (8039387, 542218, 270970), (8141857, 548648, 274199), (8252304, 555625, 277681), (8388608, 564164, 281913), (8423457, 566354, 283023), (8898505, 596129, 297935), (8945065, 599049, 299390), (9066408, 606560, 303096), (9077976, 607289, 303472), (9191713, 614394, 307074), (9239807, 617422, 308576), (9365148, 625250, 312500), (10250726, 680108, 339942), (10304362, 683441, 341587), (10444144, 692123, 345923), (10485760, 694717, 347200), (10749330, 711069, 355373), (12582912, 823750, 411818), (14336176, 930493, 465173), (14680064, 951352, 475592), (16777216, 1077872, 538765), (18874368, 1203570, 601619), (19394561, 1234572, 617139), (19526971, 1242436, 621076), (19776800, 1257275, 628465), (19967355, 1268676, 634211), (19994185, 1270258, 634989), (20971520, 1328231, 663899), (23068672, 1452314, 725962), (25165824, 1575662, 787621), (27262976, 1698417, 849010), (29360128, 1820646, 910169), (31457280, 1942385, 971087), (33299814, 2048974, 1024314)]
def gridP : List (Nat × Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (X, c, _) :: g, x => if x ≤ X then some c else gridP g x
def gridU : List (Nat × Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (X, _, c) :: g, x => if x ≤ X then some c else gridU g x
end ErdosComp

section

/-
# Rational upper bounds for prime sums and prime counts (executable)
-/

namespace ErdosComp

/-- Limit of the prime table. -/
def PM : Nat := 10000

/-- `log 2 > 0.6931471803`. -/
def log2Lo : Rat := 6931471803 / 10000000000

/-- A rational lower bound for `log x`: `k log 2 + (1 - 2^k/x)` with `k = ⌊log₂ x⌋`. -/
def logLo (x : Nat) : Rat := (Nat.log2 x : Rat) * log2Lo + (1 - (2 ^ Nat.log2 x : Nat) / (x : Rat))

/-- `√x ≤ (x/s + s)/2`, `s = 2^⌊log₂ x / 2⌋`. -/
def sqrtUp (x : Nat) : Rat :=
  let s : Nat := 2 ^ (Nat.log2 x / 2)
  ((x : Rat) / s + s) / 2

/-- Chebyshev: `π(x) ≤ √x + 2 log 4 · x / log x` (and trivially `π(x) ≤ x`). -/
def chebUp (x : Nat) : Rat :=
  if 0 < logLo x then sqrtUp x + 2 * (13863 / 10000) * x / logLo x else x

/-- Upper bound for `∑_{p ∈ (lo, hi]} 1/p²` over primes. -/
def s2P (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).fp - (lookD tab lo).fp : Nat) : Rat) / KS
  else if lo ≤ PM then (((lookD tab PM).fp - (lookD tab lo).fp : Nat) : Rat) / KS + 1 / PM
  else 1 / lo

/-- Upper bound for `∑_{p ∈ (lo, hi]} 1/p²` over U1 primes. -/
def s2U (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).fu - (lookD tab lo).fu : Nat) : Rat) / KS
  else if lo ≤ PM then (((lookD tab PM).fu - (lookD tab lo).fu : Nat) : Rat) / KS + 1 / PM
  else 1 / lo

/-- Upper bound for the number of primes in `(lo, hi]`. -/
def cP (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).cp - (lookD tab lo).cp : Nat) : Rat)
  else match gridP GRID hi with | some c => (c : Rat) | none => chebUp hi

/-- Upper bound for the number of U1 primes in `(lo, hi]`. -/
def cU (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).cu - (lookD tab lo).cu : Nat) : Rat)
  else match gridU GRID hi with | some c => (c : Rat) | none => chebUp hi

end ErdosComp
end

section

/-
# The interval checker (executable)

For an interval `[Nlo, Nhi]` with parameters `(pc, Y, Y'_q, p_{B,q})`, each case of the
case analysis is bounded by `C·N + E` (`proof.md` §6.1, Lemma D); the soundness of every
component is proved in `Erdos848/CheckSound.lean`.  Fixed parameters: `z = 31`, `z_B = z₁ = 41`,
`z₂ = 1000`.
-/

namespace ErdosComp

/- ### Products, sums and counts over `[0, n)` -/

def prodF (cond : Nat → Bool) (f : Nat → Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => prodF cond f n * (if cond n then f n else 1)

def sumF (cond : Nat → Bool) (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumF cond f n + (if cond n then f n else 0)

def cntF (cond : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cntF cond n + (if cond n then 1 else 0)

/- ### Constants of the small primes -/

def condP (excl : List Nat) (p : Nat) : Bool := isPrimeB p && !(excl.contains p)

/-- `∏_{p ≤ 31, p ∉ excl} (1 - 1/p²)`. -/
def prod1 (excl : List Nat) : Rat := prodF (condP excl) (fun p => 1 - 1 / ((p : Rat) * p)) 32
def k1 (excl : List Nat) : Nat := cntF (condP excl) 32

/-- `∏_{U1, p ≤ 41} (1 - 2/p²)`. -/
def prodU : Rat := prodF isU1B (fun p => 1 - 2 / ((p : Rat) * p)) 42
def kU : Nat := cntF isU1B 42

def condE (p q : Nat) : Bool := isU1B q && q != p
def prErase (p : Nat) : Rat := prodF (condE p) (fun q => 1 - 2 / ((q : Rat) * q)) 42
def kErase (p : Nat) : Nat := cntF (condE p) 42

def condOdd (p : Nat) : Bool := isPrimeB p && p != 2 && p != 5

/-- `∑_{p ≤ 1000, p ≠ 2, 5} nonB = cNon · N + eNon`. -/
def cNon : Rat :=
  sumF condOdd (fun p => 23 / 25 * (1 / ((p : Rat) * p)) * (1 - prErase p)) 1001
def eNon : Rat := sumF condOdd (fun p => 3 * ((3 : Rat) ^ kErase p - 1)) 1001

/-- The first 30 U1 primes. -/
def UL : List Nat := [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 173,
  181, 193, 197, 229, 233, 241, 257, 269, 277, 281, 293, 313, 317]

/-- `g(p) = gA p · N + gE p`. -/
def gA (p : Nat) : Rat := 23 / 25 * prErase p / ((p : Rat) * p)
def gE (p : Nat) : Rat := 3 - 3 * ((3 : Rat) ^ kErase p - 1)

/- ### `ρ` and the Pell factor -/

def OPc : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
  181, 191, 193, 197, 199]

def primeProdC (k : Nat) : Nat := (OPc.take k).prod

/-- `W(L) = #{k ∈ [1, 45] : primeProdC k ≤ L}`. -/
def Wc (L : Nat) : Nat := ((List.range 45).filter (fun k => primeProdC (k + 1) ≤ L)).length

def rhoMaxC (N : Nat) : Nat := max (2 ^ Wc N) (max (2 * 2 ^ Wc (N / 4)) (4 * 2 ^ Wc (N / 8)))

def log3Go (n : Nat) : Nat → Nat → Nat
  | 0, k => k
  | f + 1, k => if 3 ^ (k + 1) ≤ n then log3Go n f (k + 1) else k

def log3C (n : Nat) : Nat := log3Go n n 0

def pellC (N Y : Nat) : Nat := (N * N + 1) / ((Y + 1) * (Y + 1)) * (log3C N + 1)

/- ### The components `(C, E)` -/

abbrev CE := Rat × Rat

def addCE (a b : CE) : CE := (a.1 + b.1, a.2 + b.2)

def resCE (tab : List (Nat × PSt)) (q T : Nat) (excl : List Nat) (pc : Nat) : CE :=
  ((T : Rat) / q * (1 - prod1 excl + s2P tab 31 pc),
   (T : Rat) * ((2 : Rat) ^ k1 excl - 1 + cP tab 31 pc))

def shCE (tab : List (Nat × PSt)) (Nhi pc Y : Nat) : CE :=
  (s2P tab pc Y,
   cP tab pc Y + (rhoMaxC Nhi : Rat) * (2 * ((Nhi : Rat) + 1) / Y + ((Nhi : Rat) * Nhi + 1) / ((Y : Rat) * Y)))

def lemBCE (tab : List (Nat × PSt)) (Nhi q T pB YB : Nat) : CE :=
  ((T : Rat) / q * (1 - prodU) + 2 * (T : Rat) / q * s2U tab 41 pB + 2 * s2U tab pB YB,
   (T : Rat) * ((3 : Rat) ^ kU - 1) + 2 * (T : Rat) * cU tab 41 pB + 2 * cU tab pB YB +
     (pellC Nhi YB : Rat))

def gSumC (L : Nat) : Rat := sumF (fun _ => true) (fun j => gA (UL.getD j 0)) L
def gSumE (Nlo L : Nat) : Rat :=
  sumF (fun _ => true) (fun j => max (gE (UL.getD j 0)) (-(gA (UL.getD j 0)) * Nlo)) L

/-- `q₀ q₁ ⋯ q_{l-1}`. -/
def ulProd : Nat → Nat
  | 0 => 1
  | l + 1 => ulProd l * UL.getD l 0

def lemCCE (tab : List (Nat × PSt)) (Nlo Nhi pB YB pc L : Nat) : CE :=
  (46 / 25 * s2U tab 41 pB + 2 * s2U tab pB YB + (1 - prodU) / 25 + cNon + gSumC L +
     s2P tab 1000 pc,
   46 * cU tab 41 pB + 2 * cU tab pB YB + (pellC Nhi YB : Rat) + ((3 : Rat) ^ kU - 1) + eNon +
     gSumE Nlo L + cP tab 1000 pc)

/-- `L = max {ℓ ≤ 29 : (q₀ ⋯ q_{ℓ-1})² ≤ N² + 1}`. -/
def Lval (Nhi : Nat) : Nat :=
  ((List.range 29).filter (fun l => ulProd (l + 1) * ulProd (l + 1) ≤ Nhi * Nhi + 1)).length

/- ### One interval -/

structure Row where
  Nlo : Nat
  Nhi : Nat
  pc : Nat
  Y : Nat
  Y25 : Nat
  Y50 : Nat
  Y100 : Nat
  pB25 : Nat
  pB50 : Nat
  pB100 : Nat

def okCE (Nlo : Nat) (c : CE) : Bool :=
  decide (c.1 < 1 / 25) && decide (c.1 * Nlo + c.2 < ((Nlo : Rat) - 6) / 25)

def caseIb (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (resCE tab 25 1 [5] r.pc) (shCE tab r.Nhi r.pc r.Y))
    (addCE (resCE tab 25 1 [5] r.pc) (shCE tab r.Nhi r.pc r.Y))

def caseII (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (resCE tab 25 2 [2, 5] r.pc) (lemCCE tab r.Nlo r.Nhi r.pB25 r.Y25 r.pc (Lval r.Nhi)))
    (shCE tab r.Nhi r.pc r.Y)

def caseIII1 (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (addCE (resCE tab 100 6 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y))
    (addCE (resCE tab 100 2 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y)))
    (lemBCE tab r.Nhi 50 23 r.pB50 r.Y50)

def caseIII2a (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (2 / 100, 2) (addCE (resCE tab 100 2 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y)))
    (lemBCE tab r.Nhi 100 23 r.pB100 r.Y100)

def caseIII2b (tab : List (Nat × PSt)) (r : Row) : CE :=
  addCE (addCE (addCE (1 / 100, 1) (addCE (resCE tab 100 3 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y)))
    (addCE (resCE tab 25 1 [2, 5] r.pc) (shCE tab r.Nhi r.pc r.Y)))
    (lemBCE tab r.Nhi 100 23 r.pB100 r.Y100)

def checkRow (tab : List (Nat × PSt)) (r : Row) : Bool :=
  decide (1 ≤ r.Y) && decide (7 ≤ r.Nlo) && decide (r.Nlo ≤ r.Nhi) &&
  decide (r.Nhi < primeProdC 45) &&
  decide (Nat.succ (Lval r.Nhi) ≤ 30) &&
  decide (r.Nhi * r.Nhi + 1 < ulProd (Lval r.Nhi + 1) * ulProd (Lval r.Nhi + 1)) &&
  okCE r.Nlo (caseIb tab r) && okCE r.Nlo (caseII tab r) && okCE r.Nlo (caseIII1 tab r) &&
  okCE r.Nlo (caseIII2a tab r) && okCE r.Nlo (caseIII2b tab r)

/-- The rows are contiguous from `a` to `b`. -/
def chain : Nat → Nat → List Row → Bool
  | a, b, [] => a == b
  | a, b, r :: rs => r.Nlo == a && chain r.Nhi b rs

/-- Points at which the prime table is needed. -/
def needPts (rows : List Row) : List Nat :=
  let raw := [31, 41, 1000, PM] ++ rows.flatMap (fun r => [r.pc, r.Y, r.Y25, r.Y50, r.Y100,
    r.pB25, r.pB50, r.pB100])
  (raw.filter (· ≤ PM)).mergeSort (· ≤ ·) |>.eraseDups

def checkAll (a b : Nat) (rows : List Row) : Bool :=
  let tab : List (Nat × PSt) := []
  chain a b rows && rows.all (checkRow tab)

end ErdosComp

/- ### The tail `N > 10⁶⁰` (fixed `p_c = p_B = 2000`, `Y = Y' > PM`) -/

namespace ErdosComp

def PM1 : Nat := PM + 1

def shT (tab : List (Nat × PSt)) : CE := (s2P tab 2000 PM1, 0)

def lemBT (tab : List (Nat × PSt)) (q T : Nat) : CE :=
  ((T : Rat) / q * (1 - prodU) + 2 * (T : Rat) / q * s2U tab 41 2000 + 2 * s2U tab 2000 PM1,
   (T : Rat) * ((3 : Rat) ^ kU - 1) + 2 * (T : Rat) * cU tab 41 2000)

def gAllC : Rat := sumF isU1B gA 1001
def gAllE (Nt : Nat) : Rat := sumF isU1B (fun p => max (gE p) (-(gA p) * Nt)) 1001

def lemCT (tab : List (Nat × PSt)) (Nt : Nat) : CE :=
  (46 / 25 * s2U tab 41 2000 + 2 * s2U tab 2000 PM1 + (1 - prodU) / 25 + cNon + gAllC +
     s2P tab 1000 2000,
   46 * cU tab 41 2000 + ((3 : Rat) ^ kU - 1) + eNon + gAllE Nt + cP tab 1000 2000)

def caseIbT (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (resCE tab 25 1 [5] 2000) (shT tab)) (addCE (resCE tab 25 1 [5] 2000) (shT tab))

def caseIIT (tab : List (Nat × PSt)) (Nt : Nat) : CE :=
  addCE (addCE (resCE tab 25 2 [2, 5] 2000) (lemCT tab Nt)) (shT tab)

def caseIII1T (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (addCE (resCE tab 100 6 [2, 5] 2000) (shT tab))
    (addCE (resCE tab 100 2 [2, 5] 2000) (shT tab))) (lemBT tab 50 23)

def caseIII2aT (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (2 / 100, 2) (addCE (resCE tab 100 2 [2, 5] 2000) (shT tab))) (lemBT tab 100 23)

def caseIII2bT (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (addCE (1 / 100, 1) (addCE (resCE tab 100 3 [2, 5] 2000) (shT tab)))
    (addCE (resCE tab 25 1 [2, 5] 2000) (shT tab))) (lemBT tab 100 23)

def okT (c : CE) : Bool := decide (c.1 ≤ 1 / 25 - 1 / 1000) && decide (c.2 ≤ 10 ^ 30)

def checkTailWith (tab : List (Nat × PSt)) (Nt : Nat) : Bool :=
  okT (caseIbT tab) && okT (caseIIT tab Nt) && okT (caseIII1T tab) && okT (caseIII2aT tab) &&
    okT (caseIII2bT tab)

def checkTail (Nt : Nat) : Bool := checkTailWith (evalPts [31, 41, 1000, 2000, PM] 0 (stAt 0)) Nt

end ErdosComp
end

section

end

section

/-
# Phase 7 (part 1): a verified prime table

`stAt n` records, for the integers in `[1, n]`, the number of primes, the number of U1 primes,
and the sums `∑ ⌈K/p²⌉` over primes and over U1 primes (`K = 10³⁰`).  It is defined by the
obvious recursion, so its specification (`stAt_spec`) is proved by induction; the fast evaluation
`evalPts` (one pass, recording the state at requested points) is proved to agree with it.

From these we get explicit rational upper bounds for
`∑_{p ∈ (lo, hi]} 1/p²` and `#{p ∈ (lo, hi]}` (primes, or U1 primes); above `PM = 2·10⁷` they use
`∑_{n > PM} 1/n² ≤ 1/PM` and Chebyshev's bound `π(x) ≤ √x + 2 log 4 · x / log x`.
-/

namespace Erdos848

open Finset

open ErdosComp

/- ### Primality test: every prime is accepted -/

lemma minFacAux_prime {n : ℕ} (hn : n.Prime) : ∀ f k, 2 ≤ k → ErdosComp.minFacAux n k f = n := by
  intro f
  induction f with
  | zero => intro k _; rfl
  | succ f ih =>
    intro k hk
    simp only [ErdosComp.minFacAux]
    split_ifs with h1 h2
    · rfl
    · exfalso
      have hdvd : k ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using h2)
      rcases hn.eq_one_or_self_of_dvd k hdvd with h | h
      · omega
      · subst h; push Not at h1; nlinarith
    · exact ih (k + 2) (by omega)

lemma isPrimeB_of_prime {n : ℕ} (hn : n.Prime) : isPrimeB n = true := by
  unfold isPrimeB
  have h2 := hn.two_le
  have hlt : ¬ n < 2 := by omega
  simp only [hlt, ↓reduceIte]
  split_ifs with he
  · have : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using he)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hn).mp this
    simp [this]
  · simp [minFacAux_prime hn n 3 (by norm_num)]

lemma isU1B_of_isU1 {n : ℕ} (hn : IsU1 n) : isU1B n = true := by
  unfold isU1B
  simp [isPrimeB_of_prime hn.1, hn.2.1, hn.2.2]

/- ### The state -/

/-- Accepted numbers (a superset of the primes) in `(lo, hi]`. -/
def accP (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter (fun n => isPrimeB n = true)

/-- Accepted U1 numbers in `(lo, hi]`. -/
def accU (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter (fun n => isU1B n = true)

lemma Ioc_succ (n : ℕ) : Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) := by
  ext x; simp only [mem_Ioc, mem_insert]; omega

lemma isPrimeB_of_isU1B {n : ℕ} (h : isU1B n = true) : isPrimeB n = true := by
  unfold isU1B at h; simp only [Bool.and_eq_true] at h; exact h.1.1

theorem stAt_spec (n : ℕ) :
    (stAt n).cp = (accP 0 n).card ∧ (stAt n).cu = (accU 0 n).card ∧
    (stAt n).fp = ∑ p ∈ accP 0 n, ceilK p ∧ (stAt n).fu = ∑ p ∈ accU 0 n, ceilK p := by
  induction n with
  | zero => simp [stAt, accP, accU]
  | succ n ih =>
    have hnot : n + 1 ∉ Ioc 0 n := by simp
    have hP : accP 0 (n + 1) = if isPrimeB (n + 1) = true then insert (n + 1) (accP 0 n)
        else accP 0 n := by
      unfold accP; rw [Ioc_succ, filter_insert]
    have hU : accU 0 (n + 1) = if isU1B (n + 1) = true then insert (n + 1) (accU 0 n)
        else accU 0 n := by
      unfold accU; rw [Ioc_succ, filter_insert]
    have hnP : n + 1 ∉ accP 0 n := fun h => hnot (mem_filter.mp h).1
    have hnU : n + 1 ∉ accU 0 n := fun h => hnot (mem_filter.mp h).1
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [stAt, stepSt]
    cases hp : isPrimeB (n + 1) with
    | true =>
      cases hu : isU1B (n + 1) with
      | true =>
        simp only [ite_true, hP, hp, hU, hu, card_insert_of_notMem hnP,
          card_insert_of_notMem hnU, sum_insert hnP, sum_insert hnU]
        refine ⟨by rw [h1], by rw [h2], by rw [h3]; ring, by rw [h4]; ring⟩
      | false =>
        simp only [ite_true, Bool.false_eq_true, ite_false, hP, hp, hU, hu,
          card_insert_of_notMem hnP, sum_insert hnP]
        refine ⟨by rw [h1], h2, by rw [h3]; ring, h4⟩
    | false =>
      have hu : isU1B (n + 1) = false := by
        cases h : isU1B (n + 1)
        · rfl
        · rw [isPrimeB_of_isU1B h] at hp; exact absurd hp (by simp)
      simp only [Bool.false_eq_true, ite_false, hP, hp, hU, hu]
      exact ⟨h1, h2, h3, h4⟩

/- ### Fast evaluation -/

lemma advance_stAt : ∀ k n, advance k n (stAt n) = stAt (n + k) := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    show advance k (n + 1) (stepSt (n + 1) (stAt n)) = stAt (n + (k + 1))
    rw [show stepSt (n + 1) (stAt n) = stAt (n + 1) from rfl, ih, Nat.add_right_comm, add_assoc]

lemma evalPts_sound : ∀ xs n, ∀ e ∈ evalPts xs n (stAt n), e.2 = stAt e.1 := by
  intro xs
  induction xs with
  | nil => intro n e he; simp [evalPts] at he
  | cons x xs ih =>
    intro n e he
    simp only [evalPts, List.mem_cons] at he
    rw [advance_stAt] at he
    rcases he with rfl | he
    · rfl
    · exact ih _ e he

lemma lookD_eq {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1) (x : ℕ) :
    lookD tab x = stAt x := by
  unfold lookD
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    have hx := List.find?_some he
    simp only [beq_iff_eq] at hx
    rw [htab e hmem, hx]
  · rfl

/- ### Bounds from the table -/

/-- `∑_{p ∈ P} 1/p²`. -/
noncomputable def S2 (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1 / ((p : ℝ) * p)

/-- Primes in `(lo, hi]`. -/
def primesIn (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter Nat.Prime

/-- U1 primes in `(lo, hi]`. -/
def u1In (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter IsU1

lemma S2_nonneg (P : Finset ℕ) : 0 ≤ S2 P := sum_nonneg (fun p _ => by positivity)

lemma S2_mono {P Q : Finset ℕ} (h : P ⊆ Q) : S2 P ≤ S2 Q :=
  sum_le_sum_of_subset_of_nonneg h (fun p _ _ => by positivity)

lemma primesIn_sub_accP (lo hi : ℕ) : primesIn lo hi ⊆ accP lo hi := fun p hp => by
  simp only [primesIn, accP, mem_filter] at hp ⊢; exact ⟨hp.1, isPrimeB_of_prime hp.2⟩

lemma u1In_sub_accU (lo hi : ℕ) : u1In lo hi ⊆ accU lo hi := fun p hp => by
  simp only [u1In, accU, mem_filter] at hp ⊢; exact ⟨hp.1, isU1B_of_isU1 hp.2⟩

lemma Ioc_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Ioc a c = Ioc a b ∪ Ioc b c := by
  ext x; simp only [mem_Ioc, mem_union]; omega

lemma Ioc_disj (a b c : ℕ) : Disjoint (Ioc a b) (Ioc b c) := by
  rw [disjoint_left]; intro x h1 h2; simp only [mem_Ioc] at h1 h2; omega

lemma filter_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → Bool) :
    (Ioc a c).filter (fun n => f n = true) =
      (Ioc a b).filter (fun n => f n = true) ∪ (Ioc b c).filter (fun n => f n = true) := by
  rw [Ioc_split hab hbc, filter_union]

lemma filter_disj (a b c : ℕ) (f : ℕ → Bool) :
    Disjoint ((Ioc a b).filter (fun n => f n = true)) ((Ioc b c).filter (fun n => f n = true)) :=
  disjoint_filter_filter (Ioc_disj a b c)

lemma inv_sq_le_ceilK {p : ℕ} (hp : 1 ≤ p) : 1 / ((p : ℝ) * p) ≤ (ceilK p : ℝ) / KS := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have h : KS ≤ ceilK p * (p * p) := by
    unfold ceilK
    have h1 := Nat.lt_div_mul_add (a := KS + p * p - 1) hpp
    have hK : 1 ≤ KS := by unfold KS; norm_num
    generalize (KS + p * p - 1) / (p * p) * (p * p) = y at h1 ⊢
    omega
  have hR : (KS : ℝ) ≤ (ceilK p : ℝ) * ((p : ℝ) * p) := by exact_mod_cast h
  have hK : (0 : ℝ) < KS := by unfold KS; positivity
  have hp' : (0 : ℝ) < (p : ℝ) * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  rw [div_le_div_iff₀ hp' hK]; linarith

/-- The table part of the reciprocal-square sum. -/
lemma S2_accP_le (lo hi : ℕ) :
    S2 (accP lo hi) ≤ (((stAt hi).fp - (stAt lo).fp : ℕ) : ℝ) / KS := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isPrimeB
    have hdisj := filter_disj 0 lo hi isPrimeB
    have hfp : (stAt hi).fp = (stAt lo).fp + ∑ p ∈ accP lo hi, ceilK p := by
      rw [(stAt_spec hi).2.2.1, (stAt_spec lo).2.2.1]
      unfold accP; rw [hsplit, sum_union hdisj]
    rw [hfp, Nat.add_sub_cancel_left, Nat.cast_sum, sum_div]
    unfold S2
    apply sum_le_sum; intro p hp
    exact inv_sq_le_ceilK (by simp only [accP, mem_filter, mem_Ioc] at hp; omega)
  · have : accP lo hi = ∅ := by
      unfold accP; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; unfold S2; simp only [sum_empty]; positivity

lemma S2_accU_le (lo hi : ℕ) :
    S2 (accU lo hi) ≤ (((stAt hi).fu - (stAt lo).fu : ℕ) : ℝ) / KS := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isU1B
    have hdisj := filter_disj 0 lo hi isU1B
    have hfu : (stAt hi).fu = (stAt lo).fu + ∑ p ∈ accU lo hi, ceilK p := by
      rw [(stAt_spec hi).2.2.2, (stAt_spec lo).2.2.2]
      unfold accU; rw [hsplit, sum_union hdisj]
    rw [hfu, Nat.add_sub_cancel_left, Nat.cast_sum, sum_div]
    unfold S2
    apply sum_le_sum; intro p hp
    exact inv_sq_le_ceilK (by simp only [accU, mem_filter, mem_Ioc] at hp; omega)
  · have : accU lo hi = ∅ := by
      unfold accU; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; unfold S2; simp only [sum_empty]; positivity

lemma card_accP_le (lo hi : ℕ) : (accP lo hi).card ≤ (stAt hi).cp - (stAt lo).cp := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isPrimeB
    have hdisj := filter_disj 0 lo hi isPrimeB
    have : (stAt hi).cp = (stAt lo).cp + (accP lo hi).card := by
      rw [(stAt_spec hi).1, (stAt_spec lo).1]; unfold accP; rw [hsplit, card_union_of_disjoint hdisj]
    omega
  · have : accP lo hi = ∅ := by
      unfold accP; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; simp

lemma card_accU_le (lo hi : ℕ) : (accU lo hi).card ≤ (stAt hi).cu - (stAt lo).cu := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isU1B
    have hdisj := filter_disj 0 lo hi isU1B
    have : (stAt hi).cu = (stAt lo).cu + (accU lo hi).card := by
      rw [(stAt_spec hi).2.1, (stAt_spec lo).2.1]; unfold accU; rw [hsplit, card_union_of_disjoint hdisj]
    omega
  · have : accU lo hi = ∅ := by
      unfold accU; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; simp

/-- `∑_{n ∈ (a, b]} 1/n² ≤ 1/a`. -/
lemma sum_inv_sq_Ioc_le {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    ∑ n ∈ Ioc a b, 1 / ((n : ℝ) * n) ≤ 1 / a - 1 / max a b := by
  induction b with
  | zero => rw [show Ioc a 0 = ∅ by ext; simp]; simp
  | succ b ih =>
    by_cases hab : b < a
    · have : Ioc a (b + 1) = ∅ := by
        ext x; simp only [mem_Ioc, notMem_empty, iff_false]; omega
      rw [this, max_eq_left (by omega)]; simp
    · push Not at hab
      have hins : Ioc a (b + 1) = insert (b + 1) (Ioc a b) := by
        ext x; simp only [mem_Ioc, mem_insert]; omega
      rw [hins, sum_insert (by simp), max_eq_right (by omega)]
      rw [max_eq_right hab] at ih
      have hb : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
      have key : 1 / (((b + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith

lemma S2_tail_le {a : ℕ} (ha : 1 ≤ a) (P : Finset ℕ) (b : ℕ) (hP : P ⊆ Ioc a b) :
    S2 P ≤ 1 / a := by
  have h1 := sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => by positivity : ∀ p ∈ Ioc a b,
    p ∉ P → (0 : ℝ) ≤ 1 / ((p : ℝ) * p))
  have h2 := sum_inv_sq_Ioc_le ha b
  have : (0 : ℝ) ≤ 1 / max (a : ℝ) b := by positivity
  unfold S2; push_cast at h2; linarith

/- ### Chebyshev above the table -/

lemma logLo_le_log (x : ℕ) (hx : 1 ≤ x) : ((logLo x : ℚ) : ℝ) ≤ Real.log x := by
  unfold logLo log2Lo
  set k := Nat.log2 x
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hsplit : Real.log x = k * Real.log 2 + Real.log (x / 2 ^ k) := by
    rw [Real.log_div hxR.ne' h2k.ne', Real.log_pow]; ring
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hxR h2k)
  have hl2 := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := by positivity
  push_cast
  rw [hsplit]
  rw [inv_div] at hlog
  nlinarith

lemma sqrt_le_sqrtUp (x : ℕ) : Real.sqrt x ≤ ((sqrtUp x : ℚ) : ℝ) := by
  unfold sqrtUp
  set s : ℕ := 2 ^ (Nat.log2 x / 2)
  have hs : (0 : ℝ) < s := by positivity
  push_cast
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ x by positivity)
  have : (Real.sqrt x - s) ^ 2 ≥ 0 := sq_nonneg _
  rw [div_add' _ _ _ hs.ne', le_div_iff₀ (by norm_num), le_div_iff₀ hs]
  nlinarith

lemma card_primesIn_le_cheb (lo x : ℕ) (hx : 2 ≤ x) :
    ((primesIn lo x).card : ℝ) ≤ ((chebUp x : ℚ) : ℝ) := by
  have hsub : primesIn lo x ⊆ Nat.primesLE x := by
    intro p hp; simp only [primesIn, mem_filter, mem_Ioc] at hp
    exact Nat.mem_primesLE.mpr ⟨hp.1.2, hp.2⟩
  have h1 : ((primesIn lo x).card : ℝ) ≤ (Nat.primesLE x).card := by
    exact_mod_cast card_le_card hsub
  unfold chebUp
  split_ifs with hpos
  · have hc := card_primesLE_le x hx
    have hlo := logLo_le_log x (by omega)
    have hposR : (0 : ℝ) < ((logLo x : ℚ) : ℝ) := by exact_mod_cast hpos
    have hsq := sqrt_le_sqrtUp x
    have hl4 : Real.log 4 ≤ 13863 / 10000 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith
    have hxR : (0 : ℝ) ≤ x := by positivity
    have hlogpos : 0 < Real.log x := lt_of_lt_of_le hposR hlo
    have h3 : 2 * Real.log 4 * x / Real.log x ≤ 2 * (13863 / 10000) * x / ((logLo x : ℚ) : ℝ) := by
      have hl4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      calc 2 * Real.log 4 * x / Real.log x ≤ 2 * (13863 / 10000) * x / Real.log x := by
            gcongr
        _ ≤ 2 * (13863 / 10000) * x / ((logLo x : ℚ) : ℝ) := by
            apply div_le_div_of_nonneg_left (by positivity) hposR hlo
    push_cast
    linarith
  · have : (Nat.primesLE x).card ≤ x := by
      calc (Nat.primesLE x).card ≤ (Ioc 0 x).card := by
            apply card_le_card; intro p hp
            have := Nat.mem_primesLE.mp hp
            simp only [mem_Ioc]; exact ⟨this.2.pos, this.1⟩
        _ = x := by simp
    push_cast
    exact h1.trans (by exact_mod_cast this)

/- ### The four bounds used by the checker -/

lemma PM_pos : (1 : ℕ) ≤ PM := by unfold PM; norm_num

lemma S2_union_le (A B : Finset ℕ) : S2 (A ∪ B) ≤ S2 A + S2 B := by
  unfold S2
  have := sum_union_inter (s₁ := A) (s₂ := B) (f := fun p => 1 / ((p : ℝ) * p))
  have : 0 ≤ ∑ p ∈ A ∩ B, 1 / ((p : ℝ) * p) := sum_nonneg (fun p _ => by positivity)
  linarith


/- ### Verified prime counts at the grid points -/

/-- Survivors of the sieve in `[0, X]`. -/
def PC (u : Bool) (X : ℕ) : ℕ := ((Ico 0 (X + 1)).filter (LowSieve.PPred u)).card

set_option maxRecDepth 100000 in
lemma SPR_two : ∀ p ∈ SPR, 2 ≤ p := by
  have h : SPR.all (fun p => decide (2 ≤ p)) = true := by decide +kernel
  intro p hp; simpa using List.all_eq_true.mp h p hp

lemma ccnt_sound (u : Bool) : ∀ f a len, ((Ico a (a + len)).filter (LowSieve.PPred u)).card ≤ ccnt u f a len
  | _, a, len => by
    unfold ccnt; split_ifs with h
    · exact LowSieve.segCntC_sound SPR_two h
    · exact (card_filter_le _ _).trans (by simp)

lemma PC_zero (u : Bool) : PC u 0 = 0 := by
  unfold PC; rw [card_eq_zero, filter_eq_empty_iff]; intro x hx h
  simp only [mem_Ico] at hx; have := h.1; rw [show x = 0 by omega] at this; exact Nat.not_prime_zero this

lemma PC_step (u : Bool) {x X c d e : ℕ} (hx : x ≤ X) (hp : PC u x ≤ c)
    (h : ccnt u 64 (x + 1) (X - x) ≤ d) (he : c + d ≤ e) : PC u X ≤ e := by
  have hs : Ico 0 (X + 1) = Ico 0 (x + 1) ∪ Ico (x + 1) (x + 1 + (X - x)) := by
    rw [Ico_union_Ico_eq_Ico (by omega) (by omega)]; congr 1; omega
  unfold PC at *; rw [hs, filter_union]
  have := (Finset.card_union_le _ _).trans (Nat.add_le_add hp ((ccnt_sound u 64 _ _).trans h)); omega
set_option maxRecDepth 100000 in
def short0 : PC false 10315 ≤ 1266 ∧ PC true 10315 ≤ 627 :=
  ⟨PC_step false (x := 0) (by decide) (PC_zero false).le (d := 1266) (by decide +kernel) (by decide),
   PC_step true (x := 0) (by decide) (PC_zero true).le (d := 627) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short1 : PC false 10896 ≤ 1326 ∧ PC true 10896 ≤ 655 :=
  ⟨PC_step false (x := 10315) (by decide) short0.1 (d := 60) (by decide +kernel) (by decide),
   PC_step true (x := 10315) (by decide) short0.2 (d := 28) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short2 : PC false 11255 ≤ 1361 ∧ PC true 11255 ≤ 672 :=
  ⟨PC_step false (x := 10896) (by decide) short1.1 (d := 35) (by decide +kernel) (by decide),
   PC_step true (x := 10896) (by decide) short1.2 (d := 17) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short3 : PC false 12070 ≤ 1445 ∧ PC true 12070 ≤ 712 :=
  ⟨PC_step false (x := 11255) (by decide) short2.1 (d := 84) (by decide +kernel) (by decide),
   PC_step true (x := 11255) (by decide) short2.2 (d := 40) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short4 : PC false 274214 ≤ 23979 ∧ PC true 274214 ≤ 11970 :=
  ⟨PC_step false (x := 12070) (by decide) short3.1 (d := 22534) (by decide +kernel) (by decide),
   PC_step true (x := 12070) (by decide) short3.2 (d := 11258) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short5 : PC false 536358 ≤ 44301 ∧ PC true 536358 ≤ 22126 :=
  ⟨PC_step false (x := 274214) (by decide) short4.1 (d := 20322) (by decide +kernel) (by decide),
   PC_step true (x := 274214) (by decide) short4.2 (d := 10156) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short6 : PC false 798502 ≤ 63849 ∧ PC true 798502 ≤ 31864 :=
  ⟨PC_step false (x := 536358) (by decide) short5.1 (d := 19548) (by decide +kernel) (by decide),
   PC_step true (x := 536358) (by decide) short5.2 (d := 9738) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short7 : PC false 1060646 ≤ 82885 ∧ PC true 1060646 ≤ 41389 :=
  ⟨PC_step false (x := 798502) (by decide) short6.1 (d := 19036) (by decide +kernel) (by decide),
   PC_step true (x := 798502) (by decide) short6.2 (d := 9525) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short8 : PC false 1322790 ≤ 101645 ∧ PC true 1322790 ≤ 50773 :=
  ⟨PC_step false (x := 1060646) (by decide) short7.1 (d := 18760) (by decide +kernel) (by decide),
   PC_step true (x := 1060646) (by decide) short7.2 (d := 9384) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short9 : PC false 1584934 ≤ 120099 ∧ PC true 1584934 ≤ 60002 :=
  ⟨PC_step false (x := 1322790) (by decide) short8.1 (d := 18454) (by decide +kernel) (by decide),
   PC_step true (x := 1322790) (by decide) short8.2 (d := 9229) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short10 : PC false 1847078 ≤ 138338 ∧ PC true 1847078 ≤ 69131 :=
  ⟨PC_step false (x := 1584934) (by decide) short9.1 (d := 18239) (by decide +kernel) (by decide),
   PC_step true (x := 1584934) (by decide) short9.2 (d := 9129) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short11 : PC false 2097152 ≤ 155612 ∧ PC true 2097152 ≤ 77781 :=
  ⟨PC_step false (x := 1847078) (by decide) short10.1 (d := 17274) (by decide +kernel) (by decide),
   PC_step true (x := 1847078) (by decide) short10.2 (d := 8650) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short12 : PC false 2180391 ≤ 161351 ∧ PC true 2180391 ≤ 80619 :=
  ⟨PC_step false (x := 2097152) (by decide) short11.1 (d := 5739) (by decide +kernel) (by decide),
   PC_step true (x := 2097152) (by decide) short11.2 (d := 2838) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short13 : PC false 2200504 ≤ 162694 ∧ PC true 2200504 ≤ 81302 :=
  ⟨PC_step false (x := 2180391) (by decide) short12.1 (d := 1343) (by decide +kernel) (by decide),
   PC_step true (x := 2180391) (by decide) short12.2 (d := 683) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short14 : PC false 2242025 ≤ 165537 ∧ PC true 2242025 ≤ 82710 :=
  ⟨PC_step false (x := 2200504) (by decide) short13.1 (d := 2843) (by decide +kernel) (by decide),
   PC_step true (x := 2200504) (by decide) short13.2 (d := 1408) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short15 : PC false 2434336 ≤ 178614 ∧ PC true 2434336 ≤ 89202 :=
  ⟨PC_step false (x := 2242025) (by decide) short14.1 (d := 13077) (by decide +kernel) (by decide),
   PC_step true (x := 2242025) (by decide) short14.2 (d := 6492) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short16 : PC false 2452644 ≤ 179864 ∧ PC true 2452644 ≤ 89829 :=
  ⟨PC_step false (x := 2434336) (by decide) short15.1 (d := 1250) (by decide +kernel) (by decide),
   PC_step true (x := 2434336) (by decide) short15.2 (d := 627) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short17 : PC false 2484824 ≤ 182031 ∧ PC true 2484824 ≤ 90929 :=
  ⟨PC_step false (x := 2452644) (by decide) short16.1 (d := 2167) (by decide +kernel) (by decide),
   PC_step true (x := 2452644) (by decide) short16.2 (d := 1100) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short18 : PC false 2746968 ≤ 199795 ∧ PC true 2746968 ≤ 99825 :=
  ⟨PC_step false (x := 2484824) (by decide) short17.1 (d := 17764) (by decide +kernel) (by decide),
   PC_step true (x := 2484824) (by decide) short17.2 (d := 8896) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short19 : PC false 2942026 ≤ 212930 ∧ PC true 2942026 ≤ 106352 :=
  ⟨PC_step false (x := 2746968) (by decide) short18.1 (d := 13135) (by decide +kernel) (by decide),
   PC_step true (x := 2746968) (by decide) short18.2 (d := 6527) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short20 : PC false 2984016 ≤ 215741 ∧ PC true 2984016 ≤ 107762 :=
  ⟨PC_step false (x := 2942026) (by decide) short19.1 (d := 2811) (by decide +kernel) (by decide),
   PC_step true (x := 2942026) (by decide) short19.2 (d := 1410) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short21 : PC false 2997538 ≤ 216642 ∧ PC true 2997538 ≤ 108203 :=
  ⟨PC_step false (x := 2984016) (by decide) short20.1 (d := 901) (by decide +kernel) (by decide),
   PC_step true (x := 2984016) (by decide) short20.2 (d := 441) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short22 : PC false 3259682 ≤ 234219 ∧ PC true 3259682 ≤ 117030 :=
  ⟨PC_step false (x := 2997538) (by decide) short21.1 (d := 17577) (by decide +kernel) (by decide),
   PC_step true (x := 2997538) (by decide) short21.2 (d := 8827) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short23 : PC false 3521826 ≤ 251582 ∧ PC true 3521826 ≤ 125726 :=
  ⟨PC_step false (x := 3259682) (by decide) short22.1 (d := 17363) (by decide +kernel) (by decide),
   PC_step true (x := 3259682) (by decide) short22.2 (d := 8696) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short24 : PC false 3783970 ≤ 268928 ∧ PC true 3783970 ≤ 134381 :=
  ⟨PC_step false (x := 3521826) (by decide) short23.1 (d := 17346) (by decide +kernel) (by decide),
   PC_step true (x := 3521826) (by decide) short23.2 (d := 8655) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short25 : PC false 3923628 ≤ 278152 ∧ PC true 3923628 ≤ 138997 :=
  ⟨PC_step false (x := 3783970) (by decide) short24.1 (d := 9224) (by decide +kernel) (by decide),
   PC_step true (x := 3783970) (by decide) short24.2 (d := 4616) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short26 : PC false 3944157 ≤ 279528 ∧ PC true 3944157 ≤ 139691 :=
  ⟨PC_step false (x := 3923628) (by decide) short25.1 (d := 1376) (by decide +kernel) (by decide),
   PC_step true (x := 3923628) (by decide) short25.2 (d := 694) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short27 : PC false 3997661 ≤ 282992 ∧ PC true 3997661 ≤ 141425 :=
  ⟨PC_step false (x := 3944157) (by decide) short26.1 (d := 3464) (by decide +kernel) (by decide),
   PC_step true (x := 3944157) (by decide) short26.2 (d := 1734) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short28 : PC false 4194304 ≤ 295948 ∧ PC true 4194304 ≤ 147938 :=
  ⟨PC_step false (x := 3997661) (by decide) short27.1 (d := 12956) (by decide +kernel) (by decide),
   PC_step true (x := 3997661) (by decide) short27.2 (d := 6513) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short29 : PC false 4456448 ≤ 313086 ∧ PC true 4456448 ≤ 156499 :=
  ⟨PC_step false (x := 4194304) (by decide) short28.1 (d := 17138) (by decide +kernel) (by decide),
   PC_step true (x := 4194304) (by decide) short28.2 (d := 8561) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short30 : PC false 4718592 ≤ 330178 ∧ PC true 4718592 ≤ 165054 :=
  ⟨PC_step false (x := 4456448) (by decide) short29.1 (d := 17092) (by decide +kernel) (by decide),
   PC_step true (x := 4456448) (by decide) short29.2 (d := 8555) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short31 : PC false 4980736 ≤ 347260 ∧ PC true 4980736 ≤ 173554 :=
  ⟨PC_step false (x := 4718592) (by decide) short30.1 (d := 17082) (by decide +kernel) (by decide),
   PC_step true (x := 4718592) (by decide) short30.2 (d := 8500) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short32 : PC false 5242880 ≤ 364196 ∧ PC true 5242880 ≤ 182017 :=
  ⟨PC_step false (x := 4980736) (by decide) short31.1 (d := 16936) (by decide +kernel) (by decide),
   PC_step true (x := 4980736) (by decide) short31.2 (d := 8463) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short33 : PC false 5505024 ≤ 381114 ∧ PC true 5505024 ≤ 190450 :=
  ⟨PC_step false (x := 5242880) (by decide) short32.1 (d := 16918) (by decide +kernel) (by decide),
   PC_step true (x := 5242880) (by decide) short32.2 (d := 8433) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short34 : PC false 5767168 ≤ 397907 ∧ PC true 5767168 ≤ 198850 :=
  ⟨PC_step false (x := 5505024) (by decide) short33.1 (d := 16793) (by decide +kernel) (by decide),
   PC_step true (x := 5505024) (by decide) short33.2 (d := 8400) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short35 : PC false 6029312 ≤ 414772 ∧ PC true 6029312 ≤ 207290 :=
  ⟨PC_step false (x := 5767168) (by decide) short34.1 (d := 16865) (by decide +kernel) (by decide),
   PC_step true (x := 5767168) (by decide) short34.2 (d := 8440) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short36 : PC false 6088338 ≤ 418491 ∧ PC true 6088338 ≤ 209155 :=
  ⟨PC_step false (x := 6029312) (by decide) short35.1 (d := 3719) (by decide +kernel) (by decide),
   PC_step true (x := 6029312) (by decide) short35.2 (d := 1865) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short37 : PC false 6120195 ≤ 420547 ∧ PC true 6120195 ≤ 210169 :=
  ⟨PC_step false (x := 6088338) (by decide) short36.1 (d := 2056) (by decide +kernel) (by decide),
   PC_step true (x := 6088338) (by decide) short36.2 (d := 1014) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short38 : PC false 6203217 ≤ 425859 ∧ PC true 6203217 ≤ 212829 :=
  ⟨PC_step false (x := 6120195) (by decide) short37.1 (d := 5312) (by decide +kernel) (by decide),
   PC_step true (x := 6120195) (by decide) short37.2 (d := 2660) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short39 : PC false 6291456 ≤ 431503 ∧ PC true 6291456 ≤ 215680 :=
  ⟨PC_step false (x := 6203217) (by decide) short38.1 (d := 5644) (by decide +kernel) (by decide),
   PC_step true (x := 6203217) (by decide) short38.2 (d := 2851) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short40 : PC false 6553600 ≤ 448183 ∧ PC true 6553600 ≤ 223963 :=
  ⟨PC_step false (x := 6291456) (by decide) short39.1 (d := 16680) (by decide +kernel) (by decide),
   PC_step true (x := 6291456) (by decide) short39.2 (d := 8283) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short41 : PC false 6815744 ≤ 464882 ∧ PC true 6815744 ≤ 232367 :=
  ⟨PC_step false (x := 6553600) (by decide) short40.1 (d := 16699) (by decide +kernel) (by decide),
   PC_step true (x := 6553600) (by decide) short40.2 (d := 8404) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short42 : PC false 7077888 ≤ 481616 ∧ PC true 7077888 ≤ 240753 :=
  ⟨PC_step false (x := 6815744) (by decide) short41.1 (d := 16734) (by decide +kernel) (by decide),
   PC_step true (x := 6815744) (by decide) short41.2 (d := 8386) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short43 : PC false 7326303 ≤ 497329 ∧ PC true 7326303 ≤ 248557 :=
  ⟨PC_step false (x := 7077888) (by decide) short42.1 (d := 15713) (by decide +kernel) (by decide),
   PC_step true (x := 7077888) (by decide) short42.2 (d := 7804) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short44 : PC false 7478251 ≤ 506904 ∧ PC true 7478251 ≤ 253305 :=
  ⟨PC_step false (x := 7326303) (by decide) short43.1 (d := 9575) (by decide +kernel) (by decide),
   PC_step true (x := 7326303) (by decide) short43.2 (d := 4748) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short45 : PC false 7517380 ≤ 509355 ∧ PC true 7517380 ≤ 254544 :=
  ⟨PC_step false (x := 7478251) (by decide) short44.1 (d := 2451) (by decide +kernel) (by decide),
   PC_step true (x := 7478251) (by decide) short44.2 (d := 1239) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short46 : PC false 7779524 ≤ 525882 ∧ PC true 7779524 ≤ 262836 :=
  ⟨PC_step false (x := 7517380) (by decide) short45.1 (d := 16527) (by decide +kernel) (by decide),
   PC_step true (x := 7517380) (by decide) short45.2 (d := 8292) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short47 : PC false 8039387 ≤ 542218 ∧ PC true 8039387 ≤ 270970 :=
  ⟨PC_step false (x := 7779524) (by decide) short46.1 (d := 16336) (by decide +kernel) (by decide),
   PC_step true (x := 7779524) (by decide) short46.2 (d := 8134) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short48 : PC false 8141857 ≤ 548648 ∧ PC true 8141857 ≤ 274199 :=
  ⟨PC_step false (x := 8039387) (by decide) short47.1 (d := 6430) (by decide +kernel) (by decide),
   PC_step true (x := 8039387) (by decide) short47.2 (d := 3229) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short49 : PC false 8252304 ≤ 555625 ∧ PC true 8252304 ≤ 277681 :=
  ⟨PC_step false (x := 8141857) (by decide) short48.1 (d := 6977) (by decide +kernel) (by decide),
   PC_step true (x := 8141857) (by decide) short48.2 (d := 3482) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short50 : PC false 8388608 ≤ 564164 ∧ PC true 8388608 ≤ 281913 :=
  ⟨PC_step false (x := 8252304) (by decide) short49.1 (d := 8539) (by decide +kernel) (by decide),
   PC_step true (x := 8252304) (by decide) short49.2 (d := 4232) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short51 : PC false 8423457 ≤ 566354 ∧ PC true 8423457 ≤ 283023 :=
  ⟨PC_step false (x := 8388608) (by decide) short50.1 (d := 2190) (by decide +kernel) (by decide),
   PC_step true (x := 8388608) (by decide) short50.2 (d := 1110) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short52 : PC false 8685601 ≤ 582805 ∧ PC true 8685601 ≤ 291240 :=
  ⟨PC_step false (x := 8423457) (by decide) short51.1 (d := 16451) (by decide +kernel) (by decide),
   PC_step true (x := 8423457) (by decide) short51.2 (d := 8217) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short53 : PC false 8898505 ≤ 596129 ∧ PC true 8898505 ≤ 297935 :=
  ⟨PC_step false (x := 8685601) (by decide) short52.1 (d := 13324) (by decide +kernel) (by decide),
   PC_step true (x := 8685601) (by decide) short52.2 (d := 6695) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short54 : PC false 8945065 ≤ 599049 ∧ PC true 8945065 ≤ 299390 :=
  ⟨PC_step false (x := 8898505) (by decide) short53.1 (d := 2920) (by decide +kernel) (by decide),
   PC_step true (x := 8898505) (by decide) short53.2 (d := 1455) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short55 : PC false 9066408 ≤ 606560 ∧ PC true 9066408 ≤ 303096 :=
  ⟨PC_step false (x := 8945065) (by decide) short54.1 (d := 7511) (by decide +kernel) (by decide),
   PC_step true (x := 8945065) (by decide) short54.2 (d := 3706) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short56 : PC false 9077976 ≤ 607289 ∧ PC true 9077976 ≤ 303472 :=
  ⟨PC_step false (x := 9066408) (by decide) short55.1 (d := 729) (by decide +kernel) (by decide),
   PC_step true (x := 9066408) (by decide) short55.2 (d := 376) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short57 : PC false 9191713 ≤ 614394 ∧ PC true 9191713 ≤ 307074 :=
  ⟨PC_step false (x := 9077976) (by decide) short56.1 (d := 7105) (by decide +kernel) (by decide),
   PC_step true (x := 9077976) (by decide) short56.2 (d := 3602) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short58 : PC false 9239807 ≤ 617422 ∧ PC true 9239807 ≤ 308576 :=
  ⟨PC_step false (x := 9191713) (by decide) short57.1 (d := 3028) (by decide +kernel) (by decide),
   PC_step true (x := 9191713) (by decide) short57.2 (d := 1502) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short59 : PC false 9365148 ≤ 625250 ∧ PC true 9365148 ≤ 312500 :=
  ⟨PC_step false (x := 9239807) (by decide) short58.1 (d := 7828) (by decide +kernel) (by decide),
   PC_step true (x := 9239807) (by decide) short58.2 (d := 3924) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short60 : PC false 9627292 ≤ 641543 ∧ PC true 9627292 ≤ 320651 :=
  ⟨PC_step false (x := 9365148) (by decide) short59.1 (d := 16293) (by decide +kernel) (by decide),
   PC_step true (x := 9365148) (by decide) short59.2 (d := 8151) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short61 : PC false 9889436 ≤ 657787 ∧ PC true 9889436 ≤ 328779 :=
  ⟨PC_step false (x := 9627292) (by decide) short60.1 (d := 16244) (by decide +kernel) (by decide),
   PC_step true (x := 9627292) (by decide) short60.2 (d := 8128) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short62 : PC false 10151580 ≤ 674035 ∧ PC true 10151580 ≤ 336898 :=
  ⟨PC_step false (x := 9889436) (by decide) short61.1 (d := 16248) (by decide +kernel) (by decide),
   PC_step true (x := 9889436) (by decide) short61.2 (d := 8119) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short63 : PC false 10250726 ≤ 680108 ∧ PC true 10250726 ≤ 339942 :=
  ⟨PC_step false (x := 10151580) (by decide) short62.1 (d := 6073) (by decide +kernel) (by decide),
   PC_step true (x := 10151580) (by decide) short62.2 (d := 3044) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short64 : PC false 10304362 ≤ 683441 ∧ PC true 10304362 ≤ 341587 :=
  ⟨PC_step false (x := 10250726) (by decide) short63.1 (d := 3333) (by decide +kernel) (by decide),
   PC_step true (x := 10250726) (by decide) short63.2 (d := 1645) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short65 : PC false 10444144 ≤ 692123 ∧ PC true 10444144 ≤ 345923 :=
  ⟨PC_step false (x := 10304362) (by decide) short64.1 (d := 8682) (by decide +kernel) (by decide),
   PC_step true (x := 10304362) (by decide) short64.2 (d := 4336) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short66 : PC false 10485760 ≤ 694717 ∧ PC true 10485760 ≤ 347200 :=
  ⟨PC_step false (x := 10444144) (by decide) short65.1 (d := 2594) (by decide +kernel) (by decide),
   PC_step true (x := 10444144) (by decide) short65.2 (d := 1277) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short67 : PC false 10747904 ≤ 710977 ∧ PC true 10747904 ≤ 355328 :=
  ⟨PC_step false (x := 10485760) (by decide) short66.1 (d := 16260) (by decide +kernel) (by decide),
   PC_step true (x := 10485760) (by decide) short66.2 (d := 8128) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short68 : PC false 10749330 ≤ 711069 ∧ PC true 10749330 ≤ 355373 :=
  ⟨PC_step false (x := 10747904) (by decide) short67.1 (d := 92) (by decide +kernel) (by decide),
   PC_step true (x := 10747904) (by decide) short67.2 (d := 45) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short69 : PC false 11011474 ≤ 727218 ∧ PC true 11011474 ≤ 363413 :=
  ⟨PC_step false (x := 10749330) (by decide) short68.1 (d := 16149) (by decide +kernel) (by decide),
   PC_step true (x := 10749330) (by decide) short68.2 (d := 8040) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short70 : PC false 11273618 ≤ 743382 ∧ PC true 11273618 ≤ 371518 :=
  ⟨PC_step false (x := 11011474) (by decide) short69.1 (d := 16164) (by decide +kernel) (by decide),
   PC_step true (x := 11011474) (by decide) short69.2 (d := 8105) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short71 : PC false 11535762 ≤ 759493 ∧ PC true 11535762 ≤ 379619 :=
  ⟨PC_step false (x := 11273618) (by decide) short70.1 (d := 16111) (by decide +kernel) (by decide),
   PC_step true (x := 11273618) (by decide) short70.2 (d := 8101) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short72 : PC false 11797906 ≤ 775641 ∧ PC true 11797906 ≤ 387753 :=
  ⟨PC_step false (x := 11535762) (by decide) short71.1 (d := 16148) (by decide +kernel) (by decide),
   PC_step true (x := 11535762) (by decide) short71.2 (d := 8134) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short73 : PC false 12060050 ≤ 791745 ∧ PC true 12060050 ≤ 395857 :=
  ⟨PC_step false (x := 11797906) (by decide) short72.1 (d := 16104) (by decide +kernel) (by decide),
   PC_step true (x := 11797906) (by decide) short72.2 (d := 8104) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short74 : PC false 12322194 ≤ 807830 ∧ PC true 12322194 ≤ 403916 :=
  ⟨PC_step false (x := 12060050) (by decide) short73.1 (d := 16085) (by decide +kernel) (by decide),
   PC_step true (x := 12060050) (by decide) short73.2 (d := 8059) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short75 : PC false 12582912 ≤ 823750 ∧ PC true 12582912 ≤ 411818 :=
  ⟨PC_step false (x := 12322194) (by decide) short74.1 (d := 15920) (by decide +kernel) (by decide),
   PC_step true (x := 12322194) (by decide) short74.2 (d := 7902) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short76 : PC false 12845056 ≤ 839846 ∧ PC true 12845056 ≤ 419891 :=
  ⟨PC_step false (x := 12582912) (by decide) short75.1 (d := 16096) (by decide +kernel) (by decide),
   PC_step true (x := 12582912) (by decide) short75.2 (d := 8073) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short77 : PC false 13107200 ≤ 855733 ∧ PC true 13107200 ≤ 427805 :=
  ⟨PC_step false (x := 12845056) (by decide) short76.1 (d := 15887) (by decide +kernel) (by decide),
   PC_step true (x := 12845056) (by decide) short76.2 (d := 7914) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short78 : PC false 13369344 ≤ 871736 ∧ PC true 13369344 ≤ 435812 :=
  ⟨PC_step false (x := 13107200) (by decide) short77.1 (d := 16003) (by decide +kernel) (by decide),
   PC_step true (x := 13107200) (by decide) short77.2 (d := 8007) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short79 : PC false 13631488 ≤ 887643 ∧ PC true 13631488 ≤ 443797 :=
  ⟨PC_step false (x := 13369344) (by decide) short78.1 (d := 15907) (by decide +kernel) (by decide),
   PC_step true (x := 13369344) (by decide) short78.2 (d := 7985) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short80 : PC false 13893632 ≤ 903649 ∧ PC true 13893632 ≤ 451758 :=
  ⟨PC_step false (x := 13631488) (by decide) short79.1 (d := 16006) (by decide +kernel) (by decide),
   PC_step true (x := 13631488) (by decide) short79.2 (d := 7961) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short81 : PC false 14155776 ≤ 919553 ∧ PC true 14155776 ≤ 459692 :=
  ⟨PC_step false (x := 13893632) (by decide) short80.1 (d := 15904) (by decide +kernel) (by decide),
   PC_step true (x := 13893632) (by decide) short80.2 (d := 7934) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short82 : PC false 14336176 ≤ 930493 ∧ PC true 14336176 ≤ 465173 :=
  ⟨PC_step false (x := 14155776) (by decide) short81.1 (d := 10940) (by decide +kernel) (by decide),
   PC_step true (x := 14155776) (by decide) short81.2 (d := 5481) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short83 : PC false 14598320 ≤ 946454 ∧ PC true 14598320 ≤ 473134 :=
  ⟨PC_step false (x := 14336176) (by decide) short82.1 (d := 15961) (by decide +kernel) (by decide),
   PC_step true (x := 14336176) (by decide) short82.2 (d := 7961) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short84 : PC false 14680064 ≤ 951352 ∧ PC true 14680064 ≤ 475592 :=
  ⟨PC_step false (x := 14598320) (by decide) short83.1 (d := 4898) (by decide +kernel) (by decide),
   PC_step true (x := 14598320) (by decide) short83.2 (d := 2458) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short85 : PC false 14942208 ≤ 967231 ∧ PC true 14942208 ≤ 483513 :=
  ⟨PC_step false (x := 14680064) (by decide) short84.1 (d := 15879) (by decide +kernel) (by decide),
   PC_step true (x := 14680064) (by decide) short84.2 (d := 7921) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short86 : PC false 15204352 ≤ 983030 ∧ PC true 15204352 ≤ 491417 :=
  ⟨PC_step false (x := 14942208) (by decide) short85.1 (d := 15799) (by decide +kernel) (by decide),
   PC_step true (x := 14942208) (by decide) short85.2 (d := 7904) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short87 : PC false 15466496 ≤ 998841 ∧ PC true 15466496 ≤ 499216 :=
  ⟨PC_step false (x := 15204352) (by decide) short86.1 (d := 15811) (by decide +kernel) (by decide),
   PC_step true (x := 15204352) (by decide) short86.2 (d := 7799) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short88 : PC false 15728640 ≤ 1014734 ∧ PC true 15728640 ≤ 507130 :=
  ⟨PC_step false (x := 15466496) (by decide) short87.1 (d := 15893) (by decide +kernel) (by decide),
   PC_step true (x := 15466496) (by decide) short87.2 (d := 7914) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short89 : PC false 15990784 ≤ 1030568 ∧ PC true 15990784 ≤ 515122 :=
  ⟨PC_step false (x := 15728640) (by decide) short88.1 (d := 15834) (by decide +kernel) (by decide),
   PC_step true (x := 15728640) (by decide) short88.2 (d := 7992) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short90 : PC false 16252928 ≤ 1046325 ∧ PC true 16252928 ≤ 522983 :=
  ⟨PC_step false (x := 15990784) (by decide) short89.1 (d := 15757) (by decide +kernel) (by decide),
   PC_step true (x := 15990784) (by decide) short89.2 (d := 7861) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short91 : PC false 16515072 ≤ 1062102 ∧ PC true 16515072 ≤ 530930 :=
  ⟨PC_step false (x := 16252928) (by decide) short90.1 (d := 15777) (by decide +kernel) (by decide),
   PC_step true (x := 16252928) (by decide) short90.2 (d := 7947) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short92 : PC false 16777216 ≤ 1077872 ∧ PC true 16777216 ≤ 538765 :=
  ⟨PC_step false (x := 16515072) (by decide) short91.1 (d := 15770) (by decide +kernel) (by decide),
   PC_step true (x := 16515072) (by decide) short91.2 (d := 7835) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short93 : PC false 17039360 ≤ 1093706 ∧ PC true 17039360 ≤ 546692 :=
  ⟨PC_step false (x := 16777216) (by decide) short92.1 (d := 15834) (by decide +kernel) (by decide),
   PC_step true (x := 16777216) (by decide) short92.2 (d := 7927) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short94 : PC false 17301504 ≤ 1109377 ∧ PC true 17301504 ≤ 554558 :=
  ⟨PC_step false (x := 17039360) (by decide) short93.1 (d := 15671) (by decide +kernel) (by decide),
   PC_step true (x := 17039360) (by decide) short93.2 (d := 7866) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short95 : PC false 17563648 ≤ 1125210 ∧ PC true 17563648 ≤ 562422 :=
  ⟨PC_step false (x := 17301504) (by decide) short94.1 (d := 15833) (by decide +kernel) (by decide),
   PC_step true (x := 17301504) (by decide) short94.2 (d := 7864) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short96 : PC false 17825792 ≤ 1140880 ∧ PC true 17825792 ≤ 570270 :=
  ⟨PC_step false (x := 17563648) (by decide) short95.1 (d := 15670) (by decide +kernel) (by decide),
   PC_step true (x := 17563648) (by decide) short95.2 (d := 7848) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short97 : PC false 18087936 ≤ 1156533 ∧ PC true 18087936 ≤ 578085 :=
  ⟨PC_step false (x := 17825792) (by decide) short96.1 (d := 15653) (by decide +kernel) (by decide),
   PC_step true (x := 17825792) (by decide) short96.2 (d := 7815) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short98 : PC false 18350080 ≤ 1172268 ∧ PC true 18350080 ≤ 585979 :=
  ⟨PC_step false (x := 18087936) (by decide) short97.1 (d := 15735) (by decide +kernel) (by decide),
   PC_step true (x := 18087936) (by decide) short97.2 (d := 7894) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short99 : PC false 18612224 ≤ 1187885 ∧ PC true 18612224 ≤ 593726 :=
  ⟨PC_step false (x := 18350080) (by decide) short98.1 (d := 15617) (by decide +kernel) (by decide),
   PC_step true (x := 18350080) (by decide) short98.2 (d := 7747) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short100 : PC false 18874368 ≤ 1203570 ∧ PC true 18874368 ≤ 601619 :=
  ⟨PC_step false (x := 18612224) (by decide) short99.1 (d := 15685) (by decide +kernel) (by decide),
   PC_step true (x := 18612224) (by decide) short99.2 (d := 7893) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short101 : PC false 19136512 ≤ 1219174 ∧ PC true 19136512 ≤ 609444 :=
  ⟨PC_step false (x := 18874368) (by decide) short100.1 (d := 15604) (by decide +kernel) (by decide),
   PC_step true (x := 18874368) (by decide) short100.2 (d := 7825) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short102 : PC false 19394561 ≤ 1234572 ∧ PC true 19394561 ≤ 617139 :=
  ⟨PC_step false (x := 19136512) (by decide) short101.1 (d := 15398) (by decide +kernel) (by decide),
   PC_step true (x := 19136512) (by decide) short101.2 (d := 7695) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short103 : PC false 19526971 ≤ 1242436 ∧ PC true 19526971 ≤ 621076 :=
  ⟨PC_step false (x := 19394561) (by decide) short102.1 (d := 7864) (by decide +kernel) (by decide),
   PC_step true (x := 19394561) (by decide) short102.2 (d := 3937) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short104 : PC false 19776800 ≤ 1257275 ∧ PC true 19776800 ≤ 628465 :=
  ⟨PC_step false (x := 19526971) (by decide) short103.1 (d := 14839) (by decide +kernel) (by decide),
   PC_step true (x := 19526971) (by decide) short103.2 (d := 7389) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short105 : PC false 19967355 ≤ 1268676 ∧ PC true 19967355 ≤ 634211 :=
  ⟨PC_step false (x := 19776800) (by decide) short104.1 (d := 11401) (by decide +kernel) (by decide),
   PC_step true (x := 19776800) (by decide) short104.2 (d := 5746) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short106 : PC false 19994185 ≤ 1270258 ∧ PC true 19994185 ≤ 634989 :=
  ⟨PC_step false (x := 19967355) (by decide) short105.1 (d := 1582) (by decide +kernel) (by decide),
   PC_step true (x := 19967355) (by decide) short105.2 (d := 778) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short107 : PC false 20256329 ≤ 1285834 ∧ PC true 20256329 ≤ 642741 :=
  ⟨PC_step false (x := 19994185) (by decide) short106.1 (d := 15576) (by decide +kernel) (by decide),
   PC_step true (x := 19994185) (by decide) short106.2 (d := 7752) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short108 : PC false 20518473 ≤ 1301367 ∧ PC true 20518473 ≤ 650497 :=
  ⟨PC_step false (x := 20256329) (by decide) short107.1 (d := 15533) (by decide +kernel) (by decide),
   PC_step true (x := 20256329) (by decide) short107.2 (d := 7756) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short109 : PC false 20780617 ≤ 1316977 ∧ PC true 20780617 ≤ 658292 :=
  ⟨PC_step false (x := 20518473) (by decide) short108.1 (d := 15610) (by decide +kernel) (by decide),
   PC_step true (x := 20518473) (by decide) short108.2 (d := 7795) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short110 : PC false 20971520 ≤ 1328231 ∧ PC true 20971520 ≤ 663899 :=
  ⟨PC_step false (x := 20780617) (by decide) short109.1 (d := 11254) (by decide +kernel) (by decide),
   PC_step true (x := 20780617) (by decide) short109.2 (d := 5607) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short111 : PC false 21233664 ≤ 1343757 ∧ PC true 21233664 ≤ 671668 :=
  ⟨PC_step false (x := 20971520) (by decide) short110.1 (d := 15526) (by decide +kernel) (by decide),
   PC_step true (x := 20971520) (by decide) short110.2 (d := 7769) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short112 : PC false 21495808 ≤ 1359383 ∧ PC true 21495808 ≤ 679545 :=
  ⟨PC_step false (x := 21233664) (by decide) short111.1 (d := 15626) (by decide +kernel) (by decide),
   PC_step true (x := 21233664) (by decide) short111.2 (d := 7877) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short113 : PC false 21757952 ≤ 1374874 ∧ PC true 21757952 ≤ 687283 :=
  ⟨PC_step false (x := 21495808) (by decide) short112.1 (d := 15491) (by decide +kernel) (by decide),
   PC_step true (x := 21495808) (by decide) short112.2 (d := 7738) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short114 : PC false 22020096 ≤ 1390440 ∧ PC true 22020096 ≤ 695074 :=
  ⟨PC_step false (x := 21757952) (by decide) short113.1 (d := 15566) (by decide +kernel) (by decide),
   PC_step true (x := 21757952) (by decide) short113.2 (d := 7791) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short115 : PC false 22282240 ≤ 1405840 ∧ PC true 22282240 ≤ 702745 :=
  ⟨PC_step false (x := 22020096) (by decide) short114.1 (d := 15400) (by decide +kernel) (by decide),
   PC_step true (x := 22020096) (by decide) short114.2 (d := 7671) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short116 : PC false 22544384 ≤ 1421285 ∧ PC true 22544384 ≤ 710451 :=
  ⟨PC_step false (x := 22282240) (by decide) short115.1 (d := 15445) (by decide +kernel) (by decide),
   PC_step true (x := 22282240) (by decide) short115.2 (d := 7706) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short117 : PC false 22806528 ≤ 1436786 ∧ PC true 22806528 ≤ 718172 :=
  ⟨PC_step false (x := 22544384) (by decide) short116.1 (d := 15501) (by decide +kernel) (by decide),
   PC_step true (x := 22544384) (by decide) short116.2 (d := 7721) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short118 : PC false 23068672 ≤ 1452314 ∧ PC true 23068672 ≤ 725962 :=
  ⟨PC_step false (x := 22806528) (by decide) short117.1 (d := 15528) (by decide +kernel) (by decide),
   PC_step true (x := 22806528) (by decide) short117.2 (d := 7790) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short119 : PC false 23330816 ≤ 1467773 ∧ PC true 23330816 ≤ 733715 :=
  ⟨PC_step false (x := 23068672) (by decide) short118.1 (d := 15459) (by decide +kernel) (by decide),
   PC_step true (x := 23068672) (by decide) short118.2 (d := 7753) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short120 : PC false 23592960 ≤ 1483174 ∧ PC true 23592960 ≤ 741376 :=
  ⟨PC_step false (x := 23330816) (by decide) short119.1 (d := 15401) (by decide +kernel) (by decide),
   PC_step true (x := 23330816) (by decide) short119.2 (d := 7661) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short121 : PC false 23855104 ≤ 1498552 ∧ PC true 23855104 ≤ 749039 :=
  ⟨PC_step false (x := 23592960) (by decide) short120.1 (d := 15378) (by decide +kernel) (by decide),
   PC_step true (x := 23592960) (by decide) short120.2 (d := 7663) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short122 : PC false 24117248 ≤ 1514023 ∧ PC true 24117248 ≤ 756761 :=
  ⟨PC_step false (x := 23855104) (by decide) short121.1 (d := 15471) (by decide +kernel) (by decide),
   PC_step true (x := 23855104) (by decide) short121.2 (d := 7722) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short123 : PC false 24379392 ≤ 1529498 ∧ PC true 24379392 ≤ 764540 :=
  ⟨PC_step false (x := 24117248) (by decide) short122.1 (d := 15475) (by decide +kernel) (by decide),
   PC_step true (x := 24117248) (by decide) short122.2 (d := 7779) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short124 : PC false 24641536 ≤ 1544879 ∧ PC true 24641536 ≤ 772191 :=
  ⟨PC_step false (x := 24379392) (by decide) short123.1 (d := 15381) (by decide +kernel) (by decide),
   PC_step true (x := 24379392) (by decide) short123.2 (d := 7651) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short125 : PC false 24903680 ≤ 1560305 ∧ PC true 24903680 ≤ 779931 :=
  ⟨PC_step false (x := 24641536) (by decide) short124.1 (d := 15426) (by decide +kernel) (by decide),
   PC_step true (x := 24641536) (by decide) short124.2 (d := 7740) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short126 : PC false 25165824 ≤ 1575662 ∧ PC true 25165824 ≤ 787621 :=
  ⟨PC_step false (x := 24903680) (by decide) short125.1 (d := 15357) (by decide +kernel) (by decide),
   PC_step true (x := 24903680) (by decide) short125.2 (d := 7690) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short127 : PC false 25427968 ≤ 1590924 ∧ PC true 25427968 ≤ 795241 :=
  ⟨PC_step false (x := 25165824) (by decide) short126.1 (d := 15262) (by decide +kernel) (by decide),
   PC_step true (x := 25165824) (by decide) short126.2 (d := 7620) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short128 : PC false 25690112 ≤ 1606311 ∧ PC true 25690112 ≤ 802951 :=
  ⟨PC_step false (x := 25427968) (by decide) short127.1 (d := 15387) (by decide +kernel) (by decide),
   PC_step true (x := 25427968) (by decide) short127.2 (d := 7710) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short129 : PC false 25952256 ≤ 1621722 ∧ PC true 25952256 ≤ 810624 :=
  ⟨PC_step false (x := 25690112) (by decide) short128.1 (d := 15411) (by decide +kernel) (by decide),
   PC_step true (x := 25690112) (by decide) short128.2 (d := 7673) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short130 : PC false 26214400 ≤ 1637055 ∧ PC true 26214400 ≤ 818308 :=
  ⟨PC_step false (x := 25952256) (by decide) short129.1 (d := 15333) (by decide +kernel) (by decide),
   PC_step true (x := 25952256) (by decide) short129.2 (d := 7684) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short131 : PC false 26476544 ≤ 1652423 ∧ PC true 26476544 ≤ 825997 :=
  ⟨PC_step false (x := 26214400) (by decide) short130.1 (d := 15368) (by decide +kernel) (by decide),
   PC_step true (x := 26214400) (by decide) short130.2 (d := 7689) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short132 : PC false 26738688 ≤ 1667777 ∧ PC true 26738688 ≤ 833730 :=
  ⟨PC_step false (x := 26476544) (by decide) short131.1 (d := 15354) (by decide +kernel) (by decide),
   PC_step true (x := 26476544) (by decide) short131.2 (d := 7733) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short133 : PC false 27000832 ≤ 1683116 ∧ PC true 27000832 ≤ 841392 :=
  ⟨PC_step false (x := 26738688) (by decide) short132.1 (d := 15339) (by decide +kernel) (by decide),
   PC_step true (x := 26738688) (by decide) short132.2 (d := 7662) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short134 : PC false 27262976 ≤ 1698417 ∧ PC true 27262976 ≤ 849010 :=
  ⟨PC_step false (x := 27000832) (by decide) short133.1 (d := 15301) (by decide +kernel) (by decide),
   PC_step true (x := 27000832) (by decide) short133.2 (d := 7618) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short135 : PC false 27525120 ≤ 1713702 ∧ PC true 27525120 ≤ 856641 :=
  ⟨PC_step false (x := 27262976) (by decide) short134.1 (d := 15285) (by decide +kernel) (by decide),
   PC_step true (x := 27262976) (by decide) short134.2 (d := 7631) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short136 : PC false 27787264 ≤ 1729041 ∧ PC true 27787264 ≤ 864310 :=
  ⟨PC_step false (x := 27525120) (by decide) short135.1 (d := 15339) (by decide +kernel) (by decide),
   PC_step true (x := 27525120) (by decide) short135.2 (d := 7669) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short137 : PC false 28049408 ≤ 1744366 ∧ PC true 28049408 ≤ 871995 :=
  ⟨PC_step false (x := 27787264) (by decide) short136.1 (d := 15325) (by decide +kernel) (by decide),
   PC_step true (x := 27787264) (by decide) short136.2 (d := 7685) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short138 : PC false 28311552 ≤ 1759652 ∧ PC true 28311552 ≤ 879636 :=
  ⟨PC_step false (x := 28049408) (by decide) short137.1 (d := 15286) (by decide +kernel) (by decide),
   PC_step true (x := 28049408) (by decide) short137.2 (d := 7641) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short139 : PC false 28573696 ≤ 1774898 ∧ PC true 28573696 ≤ 887255 :=
  ⟨PC_step false (x := 28311552) (by decide) short138.1 (d := 15246) (by decide +kernel) (by decide),
   PC_step true (x := 28311552) (by decide) short138.2 (d := 7619) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short140 : PC false 28835840 ≤ 1790109 ∧ PC true 28835840 ≤ 894887 :=
  ⟨PC_step false (x := 28573696) (by decide) short139.1 (d := 15211) (by decide +kernel) (by decide),
   PC_step true (x := 28573696) (by decide) short139.2 (d := 7632) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short141 : PC false 29097984 ≤ 1805353 ∧ PC true 29097984 ≤ 902513 :=
  ⟨PC_step false (x := 28835840) (by decide) short140.1 (d := 15244) (by decide +kernel) (by decide),
   PC_step true (x := 28835840) (by decide) short140.2 (d := 7626) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short142 : PC false 29360128 ≤ 1820646 ∧ PC true 29360128 ≤ 910169 :=
  ⟨PC_step false (x := 29097984) (by decide) short141.1 (d := 15293) (by decide +kernel) (by decide),
   PC_step true (x := 29097984) (by decide) short141.2 (d := 7656) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short143 : PC false 29622272 ≤ 1835829 ∧ PC true 29622272 ≤ 917735 :=
  ⟨PC_step false (x := 29360128) (by decide) short142.1 (d := 15183) (by decide +kernel) (by decide),
   PC_step true (x := 29360128) (by decide) short142.2 (d := 7566) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short144 : PC false 29884416 ≤ 1851081 ∧ PC true 29884416 ≤ 925359 :=
  ⟨PC_step false (x := 29622272) (by decide) short143.1 (d := 15252) (by decide +kernel) (by decide),
   PC_step true (x := 29622272) (by decide) short143.2 (d := 7624) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short145 : PC false 30146560 ≤ 1866445 ∧ PC true 30146560 ≤ 933027 :=
  ⟨PC_step false (x := 29884416) (by decide) short144.1 (d := 15364) (by decide +kernel) (by decide),
   PC_step true (x := 29884416) (by decide) short144.2 (d := 7668) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short146 : PC false 30408704 ≤ 1881721 ∧ PC true 30408704 ≤ 940720 :=
  ⟨PC_step false (x := 30146560) (by decide) short145.1 (d := 15276) (by decide +kernel) (by decide),
   PC_step true (x := 30146560) (by decide) short145.2 (d := 7693) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short147 : PC false 30670848 ≤ 1896957 ∧ PC true 30670848 ≤ 948368 :=
  ⟨PC_step false (x := 30408704) (by decide) short146.1 (d := 15236) (by decide +kernel) (by decide),
   PC_step true (x := 30408704) (by decide) short146.2 (d := 7648) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short148 : PC false 30932992 ≤ 1912155 ∧ PC true 30932992 ≤ 955966 :=
  ⟨PC_step false (x := 30670848) (by decide) short147.1 (d := 15198) (by decide +kernel) (by decide),
   PC_step true (x := 30670848) (by decide) short147.2 (d := 7598) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short149 : PC false 31195136 ≤ 1927205 ∧ PC true 31195136 ≤ 963487 :=
  ⟨PC_step false (x := 30932992) (by decide) short148.1 (d := 15050) (by decide +kernel) (by decide),
   PC_step true (x := 30932992) (by decide) short148.2 (d := 7521) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short150 : PC false 31457280 ≤ 1942385 ∧ PC true 31457280 ≤ 971087 :=
  ⟨PC_step false (x := 31195136) (by decide) short149.1 (d := 15180) (by decide +kernel) (by decide),
   PC_step true (x := 31195136) (by decide) short149.2 (d := 7600) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short151 : PC false 31719424 ≤ 1957544 ∧ PC true 31719424 ≤ 978638 :=
  ⟨PC_step false (x := 31457280) (by decide) short150.1 (d := 15159) (by decide +kernel) (by decide),
   PC_step true (x := 31457280) (by decide) short150.2 (d := 7551) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short152 : PC false 31981568 ≤ 1972742 ∧ PC true 31981568 ≤ 986221 :=
  ⟨PC_step false (x := 31719424) (by decide) short151.1 (d := 15198) (by decide +kernel) (by decide),
   PC_step true (x := 31719424) (by decide) short151.2 (d := 7583) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short153 : PC false 32243712 ≤ 1987891 ∧ PC true 32243712 ≤ 993792 :=
  ⟨PC_step false (x := 31981568) (by decide) short152.1 (d := 15149) (by decide +kernel) (by decide),
   PC_step true (x := 31981568) (by decide) short152.2 (d := 7571) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short154 : PC false 32505856 ≤ 2003092 ∧ PC true 32505856 ≤ 1001312 :=
  ⟨PC_step false (x := 32243712) (by decide) short153.1 (d := 15201) (by decide +kernel) (by decide),
   PC_step true (x := 32243712) (by decide) short153.2 (d := 7520) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short155 : PC false 32768000 ≤ 2018259 ∧ PC true 32768000 ≤ 1008910 :=
  ⟨PC_step false (x := 32505856) (by decide) short154.1 (d := 15167) (by decide +kernel) (by decide),
   PC_step true (x := 32505856) (by decide) short154.2 (d := 7598) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short156 : PC false 33030144 ≤ 2033400 ∧ PC true 33030144 ≤ 1016488 :=
  ⟨PC_step false (x := 32768000) (by decide) short155.1 (d := 15141) (by decide +kernel) (by decide),
   PC_step true (x := 32768000) (by decide) short155.2 (d := 7578) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short157 : PC false 33292288 ≤ 2048561 ∧ PC true 33292288 ≤ 1024103 :=
  ⟨PC_step false (x := 33030144) (by decide) short156.1 (d := 15161) (by decide +kernel) (by decide),
   PC_step true (x := 33030144) (by decide) short156.2 (d := 7615) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
def short158 : PC false 33299814 ≤ 2048974 ∧ PC true 33299814 ≤ 1024314 :=
  ⟨PC_step false (x := 33292288) (by decide) short157.1 (d := 413) (by decide +kernel) (by decide),
   PC_step true (x := 33292288) (by decide) short157.2 (d := 211) (by decide +kernel) (by decide)⟩
set_option maxRecDepth 100000 in
lemma GRID_sound : ∀ e ∈ GRID, PC false e.1 ≤ e.2.1 ∧ PC true e.1 ≤ e.2.2 := by
  intro e he
  simp only [GRID, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [short0, short1, short2, short3, short11, short12, short13, short14, short15, short16, short17, short19, short20, short21, short25, short26, short27, short28, short36, short37, short38, short39, short43, short44, short45, short47, short48, short49, short50, short51, short53, short54, short55, short56, short57, short58, short59, short63, short64, short65, short66, short68, short75, short82, short84, short92, short100, short102, short103, short104, short105, short106, short110, short118, short126, short134, short142, short150, short158]

lemma gridP_spec : ∀ (g : List (ℕ × ℕ × ℕ)) (x c : ℕ), gridP g x = some c → ∃ e ∈ g, x ≤ e.1 ∧ e.2.1 = c
  | [], _, _, h => by simp [gridP] at h
  | (X, c', c'') :: g, x, c, h => by
    simp only [gridP] at h
    split_ifs at h with hx
    · exact ⟨(X, c', c''), by simp, hx, Option.some.inj h⟩
    · obtain ⟨e, he, h1, h2⟩ := gridP_spec g x c h; exact ⟨e, by simp [he], h1, h2⟩

lemma gridU_spec : ∀ (g : List (ℕ × ℕ × ℕ)) (x c : ℕ), gridU g x = some c → ∃ e ∈ g, x ≤ e.1 ∧ e.2.2 = c
  | [], _, _, h => by simp [gridU] at h
  | (X, c', c'') :: g, x, c, h => by
    simp only [gridU] at h
    split_ifs at h with hx
    · exact ⟨(X, c', c''), by simp, hx, Option.some.inj h⟩
    · obtain ⟨e, he, h1, h2⟩ := gridU_spec g x c h; exact ⟨e, by simp [he], h1, h2⟩

lemma primesIn_le_grid {lo hi c : ℕ} (h : gridP GRID hi = some c) : (primesIn lo hi).card ≤ c := by
  obtain ⟨e, he, h1, rfl⟩ := gridP_spec _ _ _ h
  refine le_trans (card_le_card ?_) (GRID_sound e he).1
  intro p hp; simp only [primesIn, mem_filter, mem_Ioc] at hp
  simp only [mem_filter, mem_Ico, LowSieve.PPred]; exact ⟨⟨by omega, by omega⟩, hp.2, by simp⟩

lemma u1In_le_grid {lo hi c : ℕ} (h : gridU GRID hi = some c) : (u1In lo hi).card ≤ c := by
  obtain ⟨e, he, h1, rfl⟩ := gridU_spec _ _ _ h
  refine le_trans (card_le_card ?_) (GRID_sound e he).2
  intro p hp; simp only [u1In, mem_filter, mem_Ioc, IsU1] at hp
  simp only [mem_filter, mem_Ico, LowSieve.PPred]; exact ⟨⟨by omega, by omega⟩, hp.2.1, fun _ => hp.2.2.1⟩

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

theorem S2_primesIn_le (lo hi : ℕ) : S2 (primesIn lo hi) ≤ ((s2P tab lo hi : ℚ) : ℝ) := by
  unfold s2P
  simp only [lookD_eq htab]
  split_ifs with h1 h2
  · push_cast
    exact (S2_mono (primesIn_sub_accP lo hi)).trans (S2_accP_le lo hi)
  · push_cast
    have hsub : primesIn lo hi ⊆ accP lo PM ∪ primesIn PM hi := by
      intro p hp
      simp only [primesIn, accP, mem_filter, mem_Ioc, mem_union] at hp ⊢
      by_cases hpM : p ≤ PM
      · left; exact ⟨⟨hp.1.1, hpM⟩, isPrimeB_of_prime hp.2⟩
      · right; exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    have e1 := S2_mono hsub
    have e2 : S2 (accP lo PM ∪ primesIn PM hi) ≤ S2 (accP lo PM) + S2 (primesIn PM hi) := by
      exact S2_union_le _ _
    have e3 := S2_accP_le lo PM
    have e4 := S2_tail_le PM_pos (primesIn PM hi) hi (filter_subset _ _)
    linarith
  · push_cast
    have := S2_tail_le (show 1 ≤ lo by have := PM_pos; unfold PM at *; omega) (primesIn lo hi) hi
      (filter_subset _ _)
    exact this

theorem S2_u1In_le (lo hi : ℕ) : S2 (u1In lo hi) ≤ ((s2U tab lo hi : ℚ) : ℝ) := by
  unfold s2U
  simp only [lookD_eq htab]
  split_ifs with h1 h2
  · push_cast
    exact (S2_mono (u1In_sub_accU lo hi)).trans (S2_accU_le lo hi)
  · push_cast
    have hsub : u1In lo hi ⊆ accU lo PM ∪ u1In PM hi := by
      intro p hp
      simp only [u1In, accU, mem_filter, mem_Ioc, mem_union] at hp ⊢
      by_cases hpM : p ≤ PM
      · left; exact ⟨⟨hp.1.1, hpM⟩, isU1B_of_isU1 hp.2⟩
      · right; exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    have e1 := S2_mono hsub
    have e2 : S2 (accU lo PM ∪ u1In PM hi) ≤ S2 (accU lo PM) + S2 (u1In PM hi) := by
      exact S2_union_le _ _
    have e3 := S2_accU_le lo PM
    have e4 := S2_tail_le PM_pos (u1In PM hi) hi (filter_subset _ _)
    linarith
  · push_cast
    exact S2_tail_le (show 1 ≤ lo by have := PM_pos; unfold PM at *; omega) (u1In lo hi) hi (filter_subset _ _)

theorem card_primesIn_le (lo hi : ℕ) : ((primesIn lo hi).card : ℝ) ≤ ((cP tab lo hi : ℚ) : ℝ) := by
  unfold cP
  simp only [lookD_eq htab]
  split_ifs with h1
  · push_cast
    exact_mod_cast (card_le_card (primesIn_sub_accP lo hi)).trans (card_accP_le lo hi)
  · rcases hg : gridP GRID hi with _ | c
    · exact card_primesIn_le_cheb lo hi (by unfold PM at h1; omega)
    · push_cast; exact_mod_cast primesIn_le_grid hg

theorem card_u1In_le (lo hi : ℕ) : ((u1In lo hi).card : ℝ) ≤ ((cU tab lo hi : ℚ) : ℝ) := by
  unfold cU
  simp only [lookD_eq htab]
  split_ifs with h1
  · push_cast
    exact_mod_cast (card_le_card (u1In_sub_accU lo hi)).trans (card_accU_le lo hi)
  · rcases hg : gridU GRID hi with _ | c
    swap
    · push_cast; exact_mod_cast u1In_le_grid hg
    have hsub : u1In lo hi ⊆ primesIn lo hi := fun p hp => by
      simp only [u1In, primesIn, mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩
    exact (by exact_mod_cast card_le_card hsub : ((u1In lo hi).card : ℝ) ≤ (primesIn lo hi).card).trans
      (card_primesIn_le_cheb lo hi (by unfold PM at h1; omega))

end

end Erdos848
end

section

/-
# Phase 6 (part 2): Lemma C (sieving `A*` by an even witness)

For an odd prime `p₂ ≠ 5`, `xSet N b p₂ z₁` is the set of `x ≤ N`, `x ≢ ±7 (25)`, with
`p₂² ∣ x b + 1` and `p² ∣ x² + 1` for a U1 prime `p ≤ z₁`.  We prove (`card_xSet_le`)

  `#xSet ≤ (23/25)(N/p₂²) + 3`                                  if `p₂² ∣ b² + 1`,
  `#xSet ≤ (23/25)(N/p₂²)(1 - ∏_{U∖p₂}(1 - 2/p²)) + 3(3^{|U∖p₂|} - 1)`   otherwise,

where `U` is the set of U1 primes `≤ z₁` ("all classes minus the classes 7 and 18 mod 25").
-/

namespace Erdos848

open Finset

/- ### Small tools -/

/-- CRT: the classes `a (mod m)` and `c (mod n)` combine into one class mod `m n`. -/
lemma crt_class {m n a c : ℕ} (h : Nat.Coprime m n) (ha : a < m) (hc : c < n) :
    ∃ t < m * n, ∀ x, x % (m * n) = t ↔ x % m = a ∧ x % n = c := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h a c
  have hmn : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  refine ⟨k % (m * n), Nat.mod_lt _ hmn, fun x => ?_⟩
  have e : x % (m * n) = k % (m * n) ↔ x ≡ k [MOD m] ∧ x ≡ k [MOD n] :=
    (Nat.modEq_and_modEq_iff_modEq_mul h).symm
  rw [e]
  unfold Nat.ModEq at hk1 hk2 ⊢
  rw [hk1, hk2, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]

/-- If `X`, `B`, `C` are pairwise disjoint subsets of `A`, then `|X| + |B| + |C| ≤ |A|`. -/
lemma card_three_le {A X B C : Finset ℕ} (hX : X ⊆ A) (hB : B ⊆ A) (hC : C ⊆ A)
    (hXB : Disjoint X B) (hXC : Disjoint X C) (hBC : Disjoint B C) :
    X.card + B.card + C.card ≤ A.card := by
  rw [← card_union_of_disjoint hXB, ← card_union_of_disjoint (disjoint_union_left.mpr ⟨hXC, hBC⟩)]
  exact card_le_card (union_subset (union_subset hX hB) hC)

/-- If `p² ∣ c b + 1` and `p² ∣ c² + 1` then `p² ∣ b² + 1`. -/
lemma sq_dvd_of_roots {p b c : ℕ} (h1 : p * p ∣ c * b + 1) (h2 : p * p ∣ c * c + 1) :
    p * p ∣ b * b + 1 := by
  have e1 := (ZMod.natCast_eq_zero_iff _ (p * p)).mpr h1
  have e2 := (ZMod.natCast_eq_zero_iff _ (p * p)).mpr h2
  apply (ZMod.natCast_eq_zero_iff _ (p * p)).mp
  push_cast at e1 e2 ⊢
  linear_combination ((b : ZMod (p * p)) * b) * e2 - ((c : ZMod (p * p)) * b - 1) * e1

/-- Monotonicity of the inclusion–exclusion main and error terms in the root counts. -/
lemma ie_mono (P : Finset ℕ) (Rs : ℕ → Finset ℕ) (c : ℕ) (hc : c ≤ 4)
    (hP : ∀ p ∈ P, p.Prime) (hRc : ∀ p ∈ P, (Rs p).card ≤ c) :
    (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ))) ≤
        1 - ∏ p ∈ P, (1 - (c : ℝ) / (p * p)) ∧
      ∏ p ∈ P, (1 + ((Rs p).card : ℝ)) ≤ ((1 + c : ℕ) : ℝ) ^ P.card := by
  constructor
  · have : ∏ p ∈ P, (1 - (c : ℝ) / (p * p)) ≤
        ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ)) := by
      apply prod_le_prod
      · intro p hp
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
        have : (c : ℝ) ≤ 4 := by exact_mod_cast hc
        rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
      · intro p hp
        have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hp
        push_cast
        have : (0 : ℝ) < p * p := by have := (hP p hp).pos; positivity
        gcongr
    linarith
  · rw [← prod_const]
    apply prod_le_prod
    · intro p _; positivity
    · intro p hp
      have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hp
      push_cast; linarith

/- ### The term of one prime `p₂` -/

/-- `x ≤ N`, `x ≢ ±7 (25)`, `p₂² ∣ x b + 1`, and `p² ∣ x² + 1` for a U1 prime `p ≤ z₁`. -/
def xSet (N b p₂ z₁ : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => IsStar x ∧ x % (p₂ * p₂) ∈ witRoots b p₂ ∧
    ∃ p ≤ z₁, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)

/-- The bound for a prime `p₂ ∉ S_b` (sieve by the U1 primes `≤ z₁` other than `p₂`). -/
noncomputable def nonB (N p₂ z₁ : ℕ) : ℝ :=
  23 / 25 * ((N : ℝ) / ((p₂ : ℝ) * p₂)) *
      (1 - ∏ p ∈ (smallP z₁ IsU1).erase p₂, (1 - 2 / ((p : ℝ) * p))) +
    3 * ((3 : ℝ) ^ ((smallP z₁ IsU1).erase p₂).card - 1)

/-- The bound for a prime `p₂ ∈ S_b` (whole class). -/
noncomputable def wholeB (N p₂ : ℕ) : ℝ := 23 / 25 * ((N : ℝ) / ((p₂ : ℝ) * p₂)) + 3

lemma prod_one_sub_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, (1 - 2 / ((p : ℝ) * p)) ≤ 1 := by
  apply prod_le_one
  · intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  · intro p _; have : 0 ≤ 2 / ((p : ℝ) * p) := by positivity
    linarith

lemma nonB_nonneg (N p₂ z₁ : ℕ) : 0 ≤ nonB N p₂ z₁ := by
  unfold nonB
  have h1 := prod_one_sub_le_one ((smallP z₁ IsU1).erase p₂)
    (fun p hp => (mem_filter.mp (mem_of_mem_erase hp)).2.1)
  have h2 : (1 : ℝ) ≤ 3 ^ ((smallP z₁ IsU1).erase p₂).card := one_le_pow₀ (by norm_num)
  have : 0 ≤ (N : ℝ) / ((p₂ : ℝ) * p₂) := by positivity
  have : 0 ≤ 23 / 25 * ((N : ℝ) / ((p₂ : ℝ) * p₂)) * (1 - ∏ p ∈ (smallP z₁ IsU1).erase p₂,
      (1 - 2 / ((p : ℝ) * p))) := by
    apply mul_nonneg (by positivity); linarith
  linarith

lemma wholeB_nonneg (N p₂ : ℕ) : 0 ≤ wholeB N p₂ := by unfold wholeB; positivity

lemma coprime_25_sq {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : Nat.Coprime 25 (p * p) :=
  coprime_sq_of_primes Nat.prime_five hp (Ne.symm h5)

/-- **The term of `p₂`** (odd prime `p₂ ≠ 5`). -/
theorem card_xSet_le (N b p₂ z₁ : ℕ) (hp₂ : p₂.Prime) (h5 : p₂ ≠ 5) :
    ((xSet N b p₂ z₁).card : ℝ) ≤
      if p₂ * p₂ ∣ b * b + 1 then wholeB N p₂ else nonB N p₂ z₁ := by
  classical
  by_cases hW : witRoots b p₂ = ∅
  · have : xSet N b p₂ z₁ = ∅ := by
      rw [xSet, filter_eq_empty_iff]; intro x _ h; rw [hW] at h; simp at h
    rw [this, card_empty, Nat.cast_zero]
    split_ifs
    · exact wholeB_nonneg N p₂
    · exact nonB_nonneg N p₂ z₁
  obtain ⟨c, hcW⟩ := nonempty_iff_ne_empty.mpr hW
  have hpp : 0 < p₂ * p₂ := Nat.mul_pos hp₂.pos hp₂.pos
  have hc_lt : c < p₂ * p₂ := mem_range.mp (witRoots_sub b p₂ hcW)
  have hcdvd : p₂ * p₂ ∣ c * b + 1 := (mem_filter.mp hcW).2
  have huniq : ∀ x, x % (p₂ * p₂) ∈ witRoots b p₂ → x % (p₂ * p₂) = c := fun x hx =>
    card_le_one.mp (card_witRoots_le hp₂) _ hx _ hcW
  have hcop25 := coprime_25_sq hp₂ h5
  obtain ⟨t7, ht7, H7⟩ := crt_class hcop25 (a := 7) (by norm_num) hc_lt
  obtain ⟨t18, ht18, H18⟩ := crt_class hcop25 (a := 18) (by norm_num) hc_lt
  have hQ : ((25 * (p₂ * p₂) : ℕ) : ℝ) = 25 * ((p₂ : ℝ) * p₂) := by push_cast; ring
  have hQ' : ((p₂ * p₂ : ℕ) : ℝ) = (p₂ : ℝ) * p₂ := by push_cast; ring
  have hp2R : (0 : ℝ) < (p₂ : ℝ) * p₂ := by have := hp₂.pos; positivity
  have hNdiv : (N : ℝ) / (25 * ((p₂ : ℝ) * p₂)) = (N : ℝ) / ((p₂ : ℝ) * p₂) / 25 := by
    rw [div_div, mul_comm]
  split_ifs with hsq
  · -- whole class
    set A := (Icc 1 N).filter (fun x => x % (p₂ * p₂) = c)
    set B7 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t7)
    set B18 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t18)
    have h3 := card_three_le (A := A) (X := xSet N b p₂ z₁) (B := B7) (C := B18)
      (fun x hx => by
        simp only [xSet, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, huniq x hx.2.2.1⟩)
      (fun x hx => by
        simp only [B7, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H7 x).mp hx.2).2⟩)
      (fun x hx => by
        simp only [B18, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H18 x).mp hx.2).2⟩)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B7, mem_filter] at hx hb
        exact hx.2.1.1 ((H7 x).mp hb.2).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B18, mem_filter] at hx hb
        exact hx.2.1.2 ((H18 x).mp hb.2).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [B7, B18, mem_filter] at hx hb
        have := ((H7 x).mp hx.2).1; have := ((H18 x).mp hb.2).1; omega)
    have hA := card_mod_eq_real N (p₂ * p₂) c hpp hc_lt
    have hB7 := card_mod_eq_real N (25 * (p₂ * p₂)) t7 (by omega) ht7
    have hB18 := card_mod_eq_real N (25 * (p₂ * p₂)) t18 (by omega) ht18
    rw [hQ'] at hA; rw [hQ, hNdiv] at hB7 hB18
    rw [abs_le] at hA hB7 hB18
    have h3R : ((xSet N b p₂ z₁).card : ℝ) + B7.card + B18.card ≤ A.card := by exact_mod_cast h3
    unfold wholeB
    linarith [hA.2, hB7.1, hB18.1]
  · -- sieve by U ∖ {p₂}
    set U' := (smallP z₁ IsU1).erase p₂
    have hU' : ∀ p ∈ U', p.Prime ∧ IsU1 p ∧ p ≠ p₂ := by
      intro p hp
      have := mem_erase.mp hp
      exact ⟨(mem_filter.mp this.2).2.1, (mem_filter.mp this.2).2.2, this.1⟩
    set A := (Icc 1 N).filter (fun x => x % (p₂ * p₂) = c ∧
      ∃ p ∈ U', x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)
    set B7 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t7 ∧
      ∃ p ∈ U', x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)
    set B18 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t18 ∧
      ∃ p ∈ U', x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)
    have h3 := card_three_le (A := A) (X := xSet N b p₂ z₁) (B := B7) (C := B18)
      (fun x hx => by
        simp only [xSet, mem_filter] at hx; simp only [A, mem_filter]
        obtain ⟨hx1, -, hxW, p, hpz, hp, hpU, hpR⟩ := hx
        have hxc := huniq x hxW
        refine ⟨hx1, hxc, p, ?_, hpR⟩
        have hne : p ≠ p₂ := by
          rintro rfl
          rw [hxc] at hpR
          exact hsq (sq_dvd_of_roots hcdvd (mem_filter.mp hpR).2)
        exact mem_erase.mpr ⟨hne, mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpU⟩⟩)
      (fun x hx => by
        simp only [B7, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H7 x).mp hx.2.1).2, hx.2.2⟩)
      (fun x hx => by
        simp only [B18, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H18 x).mp hx.2.1).2, hx.2.2⟩)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B7, mem_filter] at hx hb
        exact hx.2.1.1 ((H7 x).mp hb.2.1).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B18, mem_filter] at hx hb
        exact hx.2.1.2 ((H18 x).mp hb.2.1).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [B7, B18, mem_filter] at hx hb
        have := ((H7 x).mp hx.2.1).1; have := ((H18 x).mp hb.2.1).1; omega)
    have hm : ∀ p ∈ U', 0 < (fun p => p * p) p := fun p hp =>
      Nat.mul_pos (hU' p hp).1.pos (hU' p hp).1.pos
    have hR : ∀ p ∈ U', ∀ r ∈ (fun p => sqRoots p) p, r < (fun p => p * p) p :=
      fun p _ r hr => mem_range.mp (sqRoots_sub p hr)
    have hcp : ∀ p ∈ U', ∀ p' ∈ U', p ≠ p' →
        Nat.Coprime ((fun p => p * p) p) ((fun p => p * p) p') := fun p hp p' hp' hne =>
      coprime_sq_of_primes (hU' p hp).1 (hU' p' hp').1 hne
    have hcq1 : ∀ p ∈ U', Nat.Coprime (p₂ * p₂) ((fun p => p * p) p) := fun p hp =>
      coprime_sq_of_primes hp₂ (hU' p hp).1 (Ne.symm (hU' p hp).2.2)
    have hcq2 : ∀ p ∈ U', Nat.Coprime (25 * (p₂ * p₂)) ((fun p => p * p) p) := fun p hp =>
      Nat.coprime_mul_iff_left.mpr ⟨coprime_25_sq (hU' p hp).1
        (by have := (hU' p hp).2.1.2.2; omega), hcq1 p hp⟩
    have hA := card_union_le N (p₂ * p₂) c (fun p => p * p) (fun p => sqRoots p) U' hpp hc_lt
      hm hR hcq1 hcp
    have hB7 := card_union_ge N (25 * (p₂ * p₂)) t7 (fun p => p * p) (fun p => sqRoots p) U'
      (by omega) ht7 hm hR hcq2 hcp
    have hB18 := card_union_ge N (25 * (p₂ * p₂)) t18 (fun p => p * p) (fun p => sqRoots p) U'
      (by omega) ht18 hm hR hcq2 hcp
    rw [hQ'] at hA; rw [hQ, hNdiv] at hB7 hB18
    have h3R : ((xSet N b p₂ z₁).card : ℝ) + B7.card + B18.card ≤ A.card := by exact_mod_cast h3
    obtain ⟨hM, hE⟩ := ie_mono U' (fun p => sqRoots p) 2 (by norm_num) (fun p hp => (hU' p hp).1)
      (fun p hp => card_sqRoots_le (hU' p hp).1 (isU1_odd (hU' p hp).2.1))
    set M := 1 - ∏ p ∈ U', (1 - (((fun p => sqRoots p) p).card : ℝ) / (((fun p => p * p) p : ℕ) : ℝ))
    set E := ∏ p ∈ U', (1 + (((fun p => sqRoots p) p).card : ℝ))
    set X := (N : ℝ) / ((p₂ : ℝ) * p₂)
    have hX : 0 ≤ X := by positivity
    have hmain : ((xSet N b p₂ z₁).card : ℝ) ≤ 23 / 25 * X * M + 3 * (E - 1) := by
      linarith [hA, hB7, hB18]
    unfold nonB
    simp only [Nat.cast_ofNat, Nat.reduceAdd] at hM hE
    have : 23 / 25 * X * M ≤ 23 / 25 * X * (1 - ∏ p ∈ U', (1 - 2 / ((p : ℝ) * p))) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    linarith

/-- The term `p₂ = 5`: one whole class mod 25, sieved by all U1 primes `≤ z₁`. -/
theorem card_xSet5_le (N b z₁ : ℕ) :
    ((xSet N b 5 z₁).card : ℝ) ≤
      (N : ℝ) / 25 * (1 - ∏ p ∈ smallP z₁ IsU1, (1 - 2 / ((p : ℝ) * p))) +
        ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1) := by
  classical
  set U := smallP z₁ IsU1
  have hU : ∀ p ∈ U, p.Prime ∧ IsU1 p := fun p hp => (mem_filter.mp hp).2
  have hRHS : 0 ≤ (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p))) +
      ((3 : ℝ) ^ U.card - 1) := by
    have h1 := prod_one_sub_le_one U (fun p hp => (hU p hp).1)
    have h2 : (1 : ℝ) ≤ 3 ^ U.card := one_le_pow₀ (by norm_num)
    have : 0 ≤ (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p))) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  by_cases hW : witRoots b 5 = ∅
  · have : xSet N b 5 z₁ = ∅ := by
      rw [xSet, filter_eq_empty_iff]; intro x _ h; rw [hW] at h; simp at h
    rw [this, card_empty, Nat.cast_zero]; exact hRHS
  obtain ⟨c, hcW⟩ := nonempty_iff_ne_empty.mpr hW
  have hc_lt : c < 5 * 5 := mem_range.mp (witRoots_sub b 5 hcW)
  have huniq : ∀ x, x % (5 * 5) ∈ witRoots b 5 → x % (5 * 5) = c := fun x hx =>
    card_le_one.mp (card_witRoots_le Nat.prime_five) _ hx _ hcW
  have hsub : xSet N b 5 z₁ ⊆ (Icc 1 N).filter (fun x => x % 25 = c ∧
      ∃ p ∈ U, x % (fun p => p * p) p ∈ (fun p => sqRoots p) p) := by
    intro x hx
    simp only [xSet, mem_filter] at hx
    obtain ⟨hx1, -, hxW, p, hpz, hp, hpU, hpR⟩ := hx
    exact mem_filter.mpr ⟨hx1, huniq x hxW, p,
      mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpU⟩, hpR⟩
  have hA := card_union_le N 25 c (fun p => p * p) (fun p => sqRoots p) U (by norm_num) hc_lt
    (fun p hp => Nat.mul_pos (hU p hp).1.pos (hU p hp).1.pos)
    (fun p _ r hr => mem_range.mp (sqRoots_sub p hr))
    (fun p hp => coprime_25_sq (hU p hp).1 (by have := (hU p hp).2.2.2; omega))
    (fun p hp p' hp' hne => coprime_sq_of_primes (hU p hp).1 (hU p' hp').1 hne)
  obtain ⟨hM, hE⟩ := ie_mono U (fun p => sqRoots p) 2 (by norm_num) (fun p hp => (hU p hp).1)
    (fun p hp => card_sqRoots_le (hU p hp).1 (isU1_odd (hU p hp).2))
  simp only [Nat.cast_ofNat, Nat.reduceAdd] at hM hE hA
  have hcard : ((xSet N b 5 z₁).card : ℝ) ≤ ((Icc 1 N).filter (fun x => x % 25 = c ∧
      ∃ p ∈ U, x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)).card := by
    exact_mod_cast card_le_card hsub
  have : (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - ((sqRoots p).card : ℝ) / ((p * p : ℕ) : ℝ))) ≤
      (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p))) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  linarith

/- ### The cover of the Lemma C set -/

/-- The 23 classes mod 25 other than 7 and 18. -/
def T25 : Finset ℕ := (range 25).filter (fun t => t ≠ 7 ∧ t ≠ 18)

/-- Large U1 primes `p ∈ (z₁, p_B]`, inside one class mod 25. -/
def lcRes (N t z₁ pB : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => x % 25 = t ∧
    ∃ p ≤ pB, p.Prime ∧ (IsU1 p ∧ z₁ < p) ∧ x % (p * p) ∈ sqRoots p)

/-- Witness primes `p₂ ∈ (z₂, p_c]`. -/
def lcMid (N b z₂ pc : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ p ≤ pc, p.Prime ∧ z₂ < p ∧ x % (p * p) ∈ witRoots b p)

/-- The Lemma C set. -/
def lemCSet (N b : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => IsStar x ∧ ¬ Squarefree (x * x + 1) ∧ ¬ Squarefree (x * b + 1))

/-- The part of the Lemma C bound not involving the shared sets. -/
def lemCPart (N b z₁ z₂ pB Y' pc : ℕ) : Finset ℕ :=
  ((T25.biUnion (fun t => lcRes N t z₁ pB) ∪ vMidSet N pB Y') ∪ vPellSet N Y') ∪
    ((smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSet N b p₂ z₁) ∪ lcMid N b z₂ pc)

lemma lemC_cover (N b z₁ z₂ pB Y' pc Y : ℕ) (hbe : b % 2 = 0) :
    lemCSet N b ⊆ (lemCPart N b z₁ z₂ pB Y' pc ∪ midSet N b pc Y) ∪ exSet N b Y := by
  intro x hx
  simp only [lemCSet, mem_filter, mem_Icc] at hx
  obtain ⟨⟨hx1, hxN⟩, hxs, hsq1, hsq2⟩ := hx
  obtain ⟨p₁, hp₁, hd₁⟩ := exists_prime_sq_dvd hsq1
  have hU₁ := isU1_of_sq_dvd hp₁ hd₁ hxs
  have hR₁ : x % (p₁ * p₁) ∈ sqRoots p₁ := (mod_mem_sqRoots hp₁.pos x).mpr hd₁
  by_cases hsmall : ∃ p ≤ z₁, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p
  · -- sieve by the witness b
    obtain ⟨p₂, hp₂, hd₂⟩ := exists_prime_sq_dvd hsq2
    have hR₂ : x % (p₂ * p₂) ∈ witRoots b p₂ := (mod_mem_witRoots hp₂.pos x).mpr hd₂
    have hp₂2 : p₂ ≠ 2 := by
      rintro rfl
      have : 2 ∣ x * b + 1 := dvd_trans ⟨2, rfl⟩ hd₂
      have : 2 ∣ x * b := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hbe) x
      omega
    by_cases hz₂ : p₂ ≤ z₂
    · apply mem_union_left; apply mem_union_left; apply mem_union_right; apply mem_union_left
      simp only [mem_biUnion, smallP, mem_filter, mem_range, xSet, mem_Icc]
      exact ⟨p₂, ⟨by omega, hp₂, hp₂2⟩, ⟨hx1, hxN⟩, hxs, hR₂, hsmall⟩
    by_cases hpc : p₂ ≤ pc
    · apply mem_union_left; apply mem_union_left; apply mem_union_right; apply mem_union_right
      simp only [lcMid, mem_filter, mem_Icc]
      exact ⟨⟨hx1, hxN⟩, p₂, hpc, hp₂, by omega, hR₂⟩
    by_cases hpY : p₂ ≤ Y
    · apply mem_union_left; apply mem_union_right
      simp only [midSet, mem_filter, mem_Icc]
      exact ⟨⟨hx1, hxN⟩, p₂, hpY, hp₂, by omega, hR₂⟩
    · apply mem_union_right
      simp only [exSet, mem_filter, mem_Icc]
      have h1 : p₂ ≤ x * b + 1 :=
        le_trans (Nat.le_mul_self p₂) (Nat.le_of_dvd (Nat.succ_pos _) hd₂)
      have h2 : x * b + 1 ≤ N * b + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right b hxN) 1
      exact ⟨⟨hx1, hxN⟩, p₂, ⟨by omega, h1.trans h2⟩, hd₂⟩
  · -- large U1 prime
    have hz₁ : z₁ < p₁ := by
      by_contra h; push Not at h; exact hsmall ⟨p₁, h, hp₁, hU₁, hR₁⟩
    apply mem_union_left; apply mem_union_left; apply mem_union_left
    by_cases hpB : p₁ ≤ pB
    · apply mem_union_left; apply mem_union_left
      simp only [mem_biUnion, T25, mem_filter, mem_range, lcRes, mem_Icc]
      exact ⟨x % 25, ⟨Nat.mod_lt _ (by norm_num), hxs⟩, ⟨hx1, hxN⟩, rfl, p₁, hpB, hp₁,
        ⟨hU₁, hz₁⟩, hR₁⟩
    by_cases hpY : p₁ ≤ Y'
    · apply mem_union_left; apply mem_union_right
      simp only [vMidSet, mem_filter, mem_Icc]
      exact ⟨⟨hx1, hxN⟩, p₁, hpY, hp₁, ⟨hU₁, by omega⟩, hR₁⟩
    · apply mem_union_right
      simp only [vPellSet, mem_filter, mem_Icc]
      have h1 : p₁ * p₁ ≤ x * x + 1 := Nat.le_of_dvd (Nat.succ_pos _) hd₁
      have h2 : x * x + 1 ≤ N * N + 1 := Nat.add_le_add_right (Nat.mul_le_mul hxN hxN) 1
      have h3 : p₁ ≤ N + 1 := by
        by_contra hc; push Not at hc
        have : (N + 2) * (N + 2) ≤ p₁ * p₁ := Nat.mul_le_mul hc hc
        nlinarith
      refine ⟨⟨hx1, hxN⟩, p₁, ⟨by omega, h3⟩, ?_⟩
      rw [sq]; exact hd₁

/- ### Lemma C2: prefix domination -/

lemma isU1_infinite : (Set.ofPred IsU1).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hp, hap, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 4) (a + 13) (by norm_num)
  refine ⟨p, ?_, by omega⟩
  show IsU1 p
  unfold Nat.ModEq at hmod
  exact ⟨hp, by simpa using hmod, by omega⟩

/-- The `j`-th U1 prime (`q₀ = 13, q₁ = 17, q₂ = 29, …`). -/
noncomputable def u1 (j : ℕ) : ℕ := Nat.nth IsU1 j

lemma u1_isU1 (j : ℕ) : IsU1 (u1 j) := Nat.nth_mem_of_infinite isU1_infinite j

lemma u1_le_of_count {a k : ℕ} (ha : IsU1 a) (hk : k ≤ Nat.count IsU1 a) : u1 k ≤ a := by
  unfold u1
  calc Nat.nth IsU1 k ≤ Nat.nth IsU1 (Nat.count IsU1 a) := Nat.nth_monotone isU1_infinite hk
    _ = a := Nat.nth_count ha

/-- **Prefix domination** (Lemma C2): for `g` antitone on U1 primes and a set `S` of U1 primes,
`∑_S g ≤ ∑_{j < |S|} g(q_j)` and `∏_{j < |S|} q_j ≤ ∏_S p`. -/
theorem prefix_dom (g : ℕ → ℝ) (hg : ∀ p p', IsU1 p → IsU1 p' → p ≤ p' → g p' ≤ g p) :
    ∀ S : Finset ℕ, (∀ p ∈ S, IsU1 p) →
      ∑ p ∈ S, g p ≤ ∑ j ∈ range S.card, g (u1 j) ∧
        ∏ j ∈ range S.card, u1 j ≤ ∏ p ∈ S, p := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro hS
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha : IsU1 a := hS a (mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun p hp => hS p (mem_insert_of_mem hp))
    have hcount : s.card ≤ Nat.count IsU1 a := by
      rw [Nat.count_eq_card_filter_range]
      apply card_le_card
      intro x hx
      simp only [mem_filter, mem_range]
      exact ⟨hlt x hx, hS x (mem_insert_of_mem hx)⟩
    have hua := u1_le_of_count ha hcount
    rw [card_insert_of_notMem has, sum_insert has, prod_insert has, sum_range_succ,
      prod_range_succ]
    refine ⟨?_, ?_⟩
    · have := hg (u1 s.card) a (u1_isU1 _) ha hua
      linarith
    · calc (∏ j ∈ range s.card, u1 j) * u1 s.card ≤ (∏ p ∈ s, p) * a :=
            Nat.mul_le_mul ih2 hua
        _ = a * ∏ p ∈ s, p := mul_comm _ _

/-- Consequence used by the certificates: if the product of the first `L + 1` U1 primes exceeds
`M ≥ ∏_S p`, then `∑_S g ≤ ∑_{j < L} max(g(q_j), 0)`. -/
theorem prefix_dom_max (g : ℕ → ℝ) (hg : ∀ p p', IsU1 p → IsU1 p' → p ≤ p' → g p' ≤ g p)
    (S : Finset ℕ) (hS : ∀ p ∈ S, IsU1 p) (M L : ℕ) (hSM : ∏ p ∈ S, p ≤ M)
    (hL : M < ∏ j ∈ range (L + 1), u1 j) :
    ∑ p ∈ S, g p ≤ ∑ j ∈ range L, max (g (u1 j)) 0 := by
  obtain ⟨h1, h2⟩ := prefix_dom g hg S hS
  have hcard : S.card ≤ L := by
    by_contra hc
    push Not at hc
    have hmono : ∏ j ∈ range (L + 1), u1 j ≤ ∏ j ∈ range S.card, u1 j := by
      apply prod_le_prod_of_subset_of_one_le (range_subset_range.mpr hc) (fun _ _ => Nat.zero_le _)
      intro j _ _; exact (u1_isU1 j).1.one_lt.le
    omega
  calc ∑ p ∈ S, g p ≤ ∑ j ∈ range S.card, g (u1 j) := h1
    _ ≤ ∑ j ∈ range S.card, max (g (u1 j)) 0 := sum_le_sum (fun j _ => le_max_left _ _)
    _ ≤ ∑ j ∈ range L, max (g (u1 j)) 0 :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hcard)
          (fun j _ _ => le_max_right _ _)

/- ### Lemma C1: the gain `g = whole − non` is decreasing -/

/-- `g(p) = wholeB − nonB`. -/
noncomputable def gC (N z₁ p : ℕ) : ℝ := wholeB N p - nonB N p z₁

/-- `P = ∏_{U} (1 − 2/q²)`, `U` = U1 primes `≤ z₁`. -/
noncomputable def PU (z₁ : ℕ) : ℝ := ∏ q ∈ smallP z₁ IsU1, (1 - 2 / ((q : ℝ) * q))

lemma factor_pos {q : ℕ} (hq : q.Prime) : 0 < 1 - 2 / ((q : ℝ) * q) := by
  have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  rw [sub_pos, div_lt_one (by positivity)]; nlinarith

lemma PU_pos (z₁ : ℕ) : 0 < PU z₁ :=
  prod_pos (fun _q hq => factor_pos (mem_filter.mp hq).2.1)

lemma mem_U_iff {z₁ p : ℕ} (hp : IsU1 p) : p ∈ smallP z₁ IsU1 ↔ p ≤ z₁ := by
  simp only [smallP, mem_filter, mem_range]
  constructor
  · intro h; omega
  · intro h; exact ⟨by omega, hp.1, hp⟩

lemma gC_in {N z₁ p : ℕ} (hpU : p ∈ smallP z₁ IsU1) :
    gC N z₁ p = 23 / 25 * N * PU z₁ / ((p : ℝ) * p - 2) + 3 -
      3 * ((3 : ℝ) ^ ((smallP z₁ IsU1).card - 1) - 1) := by
  have hp : p.Prime := (mem_filter.mp hpU).2.1
  have hf := factor_pos hp
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : (0 : ℝ) < p * p := by positivity
  have hpp2 : (0 : ℝ) < p * p - 2 := by nlinarith
  have hmul := mul_prod_erase (smallP z₁ IsU1) (fun q => (1 - 2 / ((q : ℝ) * q))) hpU
  have hpr : ∏ q ∈ (smallP z₁ IsU1).erase p, (1 - 2 / ((q : ℝ) * q)) =
      PU z₁ / (1 - 2 / ((p : ℝ) * p)) := by
    rw [PU, ← hmul, mul_div_cancel_left₀ _ hf.ne']
  unfold gC wholeB nonB
  rw [hpr, card_erase_of_mem hpU]
  have e : (1 : ℝ) - 2 / ((p : ℝ) * p) = ((p : ℝ) * p - 2) / ((p : ℝ) * p) := by
    field_simp
  rw [e]
  field_simp
  ring

lemma gC_out {N z₁ p : ℕ} (hpU : p ∉ smallP z₁ IsU1) :
    gC N z₁ p = 23 / 25 * N * PU z₁ / ((p : ℝ) * p) + 3 -
      3 * ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1) := by
  unfold gC wholeB nonB
  rw [erase_eq_of_notMem hpU]
  unfold PU
  ring

/-- **Lemma C1.** -/
theorem gC_anti (N z₁ : ℕ) :
    ∀ p p', IsU1 p → IsU1 p' → p ≤ p' → gC N z₁ p' ≤ gC N z₁ p := by
  intro p p' hp hp' hle
  have hP := PU_pos z₁
  have hN : (0 : ℝ) ≤ N := by positivity
  have h13 : (13 : ℝ) ≤ p := by exact_mod_cast hp.2.2
  have hle' : (p : ℝ) ≤ p' := by exact_mod_cast hle
  have hsq : (p : ℝ) * p ≤ (p' : ℝ) * p' := by nlinarith
  have hNP : 0 ≤ 23 / 25 * (N : ℝ) * PU z₁ := by positivity
  by_cases hpU : p ≤ z₁
  · rw [gC_in ((mem_U_iff hp).mpr hpU)]
    by_cases hpU' : p' ≤ z₁
    · rw [gC_in ((mem_U_iff hp').mpr hpU')]
      have : 23 / 25 * (N : ℝ) * PU z₁ / ((p' : ℝ) * p' - 2) ≤
          23 / 25 * (N : ℝ) * PU z₁ / ((p : ℝ) * p - 2) :=
        div_le_div_of_nonneg_left hNP (by nlinarith) (by linarith)
      linarith
    · rw [gC_out (fun h => hpU' ((mem_U_iff hp').mp h))]
      have hcard : 1 ≤ (smallP z₁ IsU1).card :=
        card_pos.mpr ⟨p, (mem_U_iff hp).mpr hpU⟩
      have hpow : (3 : ℝ) ^ ((smallP z₁ IsU1).card - 1) ≤ 3 ^ (smallP z₁ IsU1).card :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      have : 23 / 25 * (N : ℝ) * PU z₁ / ((p' : ℝ) * p') ≤
          23 / 25 * (N : ℝ) * PU z₁ / ((p : ℝ) * p - 2) :=
        div_le_div_of_nonneg_left hNP (by nlinarith) (by linarith)
      linarith
  · have hpU' : ¬ p' ≤ z₁ := by omega
    rw [gC_out (fun h => hpU ((mem_U_iff hp).mp h)),
      gC_out (fun h => hpU' ((mem_U_iff hp').mp h))]
    have : 23 / 25 * (N : ℝ) * PU z₁ / ((p' : ℝ) * p') ≤
        23 / 25 * (N : ℝ) * PU z₁ / ((p : ℝ) * p) :=
      div_le_div_of_nonneg_left hNP (by nlinarith) hsq
    linarith

/- ### The explicit Lemma C bound -/

lemma prod_sq_dvd {n : ℕ} : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p * p ∣ n) →
    (∏ p ∈ S, p) * (∏ p ∈ S, p) ∣ n := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | insert a s has ih =>
    intro hP hd
    rw [prod_insert has]
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := Nat.Coprime.prod_right (fun q hq =>
      (Nat.coprime_primes (hP a (mem_insert_self a s)) (hP q (mem_insert_of_mem hq))).mpr
        (fun h => has (h ▸ hq)))
    have hcop2 : Nat.Coprime (a * a) ((∏ p ∈ s, p) * (∏ p ∈ s, p)) :=
      Nat.Coprime.mul_right (Nat.coprime_mul_iff_left.mpr ⟨hcop, hcop⟩)
        (Nat.coprime_mul_iff_left.mpr ⟨hcop, hcop⟩)
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 (hd a (mem_insert_self a s))
      (ih (fun p hp => hP p (mem_insert_of_mem hp)) (fun p hp => hd p (mem_insert_of_mem hp)))
    calc a * (∏ p ∈ s, p) * (a * ∏ p ∈ s, p) = a * a * ((∏ p ∈ s, p) * (∏ p ∈ s, p)) := by ring
      _ ∣ n := this

lemma smallP_odd_eq (z₂ : ℕ) (h5 : 5 ≤ z₂) :
    smallP z₂ (· ≠ 2) = insert 5 (smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5)) := by
  ext p
  simp only [smallP, mem_insert, mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases h : p = 5
    · left; exact h
    · right; exact ⟨h1, h2, h3, h⟩
  · rintro (rfl | ⟨h1, h2, h3, -⟩)
    · exact ⟨by omega, Nat.prime_five, by norm_num⟩
    · exact ⟨h1, h2, h3⟩

/-- **Lemma C**, explicit form (without the shared sets `Mid(b)`, `Ex(b)`). -/
theorem card_lemCPart_le (N b z₁ z₂ pB Y' pc : ℕ) (G : ℝ) (hbN : b ≤ N) (hbs : IsStar b)
    (h5 : 5 ≤ z₂)
    (hG : ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 → ∑ p ∈ S, gC N z₁ p ≤ G) :
    ((lemCPart N b z₁ z₂ pB Y' pc).card : ℝ) ≤
      23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((N : ℝ) / 25 / (p * p)) + 2) +
      ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
      (((N ^ 2 + 1) / (Y' + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) +
      ((N : ℝ) / 25 * (1 - PU z₁) + ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1)) +
      ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ +
      G +
      ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((N : ℝ) / (p * p) + 1) := by
  classical
  -- card of the union
  set R1 := T25.biUnion (fun t => lcRes N t z₁ pB)
  set X := (smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSet N b p₂ z₁)
  have hU : (lemCPart N b z₁ z₂ pB Y' pc).card ≤ R1.card + (vMidSet N pB Y').card +
      (vPellSet N Y').card + (X.card + (lcMid N b z₂ pc).card) := by
    have hdef : lemCPart N b z₁ z₂ pB Y' pc =
        ((R1 ∪ vMidSet N pB Y') ∪ vPellSet N Y') ∪ (X ∪ lcMid N b z₂ pc) := rfl
    rw [hdef]
    have a1 := Finset.card_union_le ((R1 ∪ vMidSet N pB Y') ∪ vPellSet N Y') (X ∪ lcMid N b z₂ pc)
    have a2 := Finset.card_union_le (R1 ∪ vMidSet N pB Y') (vPellSet N Y')
    have a3 := Finset.card_union_le R1 (vMidSet N pB Y')
    have a4 := Finset.card_union_le X (lcMid N b z₂ pc)
    omega
  have hUR : ((lemCPart N b z₁ z₂ pB Y' pc).card : ℝ) ≤ (R1.card : ℝ) + (vMidSet N pB Y').card +
      (vPellSet N Y').card + ((X.card : ℝ) + (lcMid N b z₂ pc).card) := by exact_mod_cast hU
  -- R1
  have hR1 : (R1.card : ℝ) ≤ 23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p),
      (2 * ((N : ℝ) / 25 / (p * p)) + 2) := by
    have h1 : (R1.card : ℝ) ≤ ∑ t ∈ T25, ((lcRes N t z₁ pB).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have h2 : ∀ t ∈ T25, ((lcRes N t z₁ pB).card : ℝ) ≤
        ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((N : ℝ) / 25 / (p * p)) + 2) := by
      intro t ht
      have ht25 : t < 25 := mem_range.mp (mem_filter.mp ht).1
      have h := classSieve_le N 25 t z₁ pB 2 (fun p => sqRoots p) (fun p => IsU1 p ∧ z₁ < p)
        (by norm_num) ht25 (by norm_num) sqRoots_sub
        (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1))
        (fun p hp hU => Nat.Coprime.symm (Nat.Coprime.pow_right 2
          ((Nat.coprime_primes hp Nat.prime_five).mpr (by have := hU.1.2.2; omega))))
      have hsmall : smallP z₁ (fun p => IsU1 p ∧ z₁ < p) = ∅ := by
        rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
      rw [hsmall] at h
      simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_ofNat]
        at h
      simpa [lcRes] using h
    have hT : T25.card = 23 := by decide
    calc (R1.card : ℝ) ≤ ∑ t ∈ T25, ((lcRes N t z₁ pB).card : ℝ) := h1
      _ ≤ ∑ _t ∈ T25, ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p),
          (2 * ((N : ℝ) / 25 / (p * p)) + 2) := sum_le_sum h2
      _ = _ := by rw [sum_const, hT, nsmul_eq_mul]; norm_num
  -- vMid, Pell
  have hmid : ((vMidSet N pB Y').card : ℝ) ≤
      ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) := by
    have h := classSieve_le N 1 0 pB Y' 2 (fun p => sqRoots p) (fun p => IsU1 p ∧ pB < p)
      one_pos one_pos (by norm_num) sqRoots_sub
      (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1)) (fun p _ _ => Nat.coprime_one_left p)
    have hsmall : smallP pB (fun p => IsU1 p ∧ pB < p) = ∅ := by
      rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
    rw [hsmall] at h
    simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_ofNat,
      Nat.mod_one, true_and] at h
    simpa [vMidSet] using h
  have hpell : ((vPellSet N Y').card : ℝ) ≤
      (((N ^ 2 + 1) / (Y' + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
    exact_mod_cast pellTail_le N Y'
  -- lcMid
  have hlc : ((lcMid N b z₂ pc).card : ℝ) ≤
      ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((N : ℝ) / (p * p) + 1) := card_midSet_le N b z₂ pc
  -- the p₂ terms
  have hX1 : (X.card : ℝ) ≤ ∑ p ∈ smallP z₂ (· ≠ 2), ((xSet N b p z₁).card : ℝ) := by
    exact_mod_cast card_biUnion_le
  have hX5 := card_xSet5_le N b z₁
  have hodd : ∀ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), ((xSet N b p z₁).card : ℝ) ≤
      nonB N p z₁ + if p * p ∣ b * b + 1 then gC N z₁ p else 0 := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have := card_xSet_le N b p z₁ hpp.1 hpp.2.2
    split_ifs at this ⊢ <;> unfold gC at * <;> linarith
  set S := (smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5)).filter (fun p => p * p ∣ b * b + 1)
  have hsplit : ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5),
      (nonB N p z₁ + if p * p ∣ b * b + 1 then gC N z₁ p else 0) =
      ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ + ∑ p ∈ S, gC N z₁ p := by
    rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero]
  have hSU1 : ∀ p ∈ S, IsU1 p := fun p hp =>
    isU1_of_sq_dvd (mem_filter.mp (mem_filter.mp hp).1).2.1 (mem_filter.mp hp).2 hbs
  have hSprod : (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 := by
    have hd := prod_sq_dvd S (fun p hp => (hSU1 p hp).1) (fun p hp => (mem_filter.mp hp).2)
    have h1 := Nat.le_of_dvd (Nat.succ_pos _) hd
    have h2 : b * b + 1 ≤ N * N + 1 := Nat.add_le_add_right (Nat.mul_le_mul hbN hbN) 1
    omega
  have hC2 := hG S (filter_subset _ _) hSU1 hSprod
  have hXsum : ∑ p ∈ smallP z₂ (· ≠ 2), ((xSet N b p z₁).card : ℝ) ≤
      ((N : ℝ) / 25 * (1 - PU z₁) + ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1)) +
      (∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ +
        G) := by
    rw [smallP_odd_eq z₂ h5, sum_insert (by simp [smallP])]
    have := sum_le_sum hodd
    rw [hsplit] at this
    unfold PU
    linarith
  linarith

/-- The prefix bound (Lemma C2) as a `G` for `card_lemCPart_le`. -/
lemma gBound_prefix (N z₁ z₂ L : ℕ)
    (hL : N * N + 1 < (∏ j ∈ range (L + 1), u1 j) * (∏ j ∈ range (L + 1), u1 j)) :
    ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 →
        ∑ p ∈ S, gC N z₁ p ≤ ∑ j ∈ range L, max (gC N z₁ (u1 j)) 0 := by
  intro S _ hSU1 hSprod
  have : ∏ p ∈ S, p < ∏ j ∈ range (L + 1), u1 j :=
    Nat.mul_self_lt_mul_self_iff.mp (by omega)
  exact prefix_dom_max (gC N z₁) (gC_anti N z₁) S hSU1 (∏ p ∈ S, p) L le_rfl this

/-- All U1 primes `≤ z₂` (no prefix condition) as a `G`. -/
lemma gBound_all (N z₁ z₂ : ℕ) :
    ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 →
        ∑ p ∈ S, gC N z₁ p ≤ ∑ p ∈ smallP z₂ IsU1, max (gC N z₁ p) 0 := by
  intro S hS hSU1 _
  have hsub : S ⊆ smallP z₂ IsU1 := fun p hp => by
    have := hS hp
    simp only [smallP, mem_filter] at this ⊢
    exact ⟨this.1, this.2.1, hSU1 p hp⟩
  calc ∑ p ∈ S, gC N z₁ p ≤ ∑ p ∈ S, max (gC N z₁ p) 0 := sum_le_sum (fun p _ => le_max_left _ _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => le_max_right _ _)

end Erdos848
end

section

/-
# Phase 6 (part 3): explicit real bounds for each case of `CountBounds`

`resB`, `shB`, `lemBB`, `lemCB` are the explicit bounds of Lemma A′(iii) (restricted part),
Lemma A′(i)+(ii) (the shared sets of a witness), Lemma B and Lemma C.  For every case of
`CountBounds N` we bound the left-hand side by a sum of these (`caseIb_real`, …).
-/

namespace Erdos848

open Finset

/- ### The explicit bounds -/

/-- Lemma A′(iii): `T` classes mod `q`, primes in `excl` excluded. -/
noncomputable def resB (N q T z pc : ℕ) (excl : Finset ℕ) : ℝ :=
  T * ((N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
    ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
    ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1))

/-- Lemma A′(i)+(ii): the shared sets `Mid(b) ∪ Ex(b)` of a witness. -/
noncomputable def shB (N b pc Y : ℕ) : ℝ :=
  ∑ p ∈ midP pc Y (fun p => pc < p), ((N : ℝ) / (p * p) + 1) +
    rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2)

/-- Lemma B: `T` classes mod `q`. -/
noncomputable def lemBB (N q T zB pB Y' : ℕ) : ℝ :=
  T * ((N : ℝ) / q * (1 - ∏ p ∈ smallP zB IsU1, (1 - 2 / ((p : ℝ) * p))) +
    ((3 : ℝ) ^ (smallP zB IsU1).card - 1) +
    ∑ p ∈ midP zB pB IsU1, (2 * ((N : ℝ) / q / (p * p)) + 2)) +
  ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
  (((N ^ 2 + 1) / (Y' + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ)

/-- Lemma C (without the shared sets). -/
noncomputable def lemCB (N z₁ z₂ pB Y' pc : ℕ) (G : ℝ) : ℝ :=
  23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((N : ℝ) / 25 / (p * p)) + 2) +
  ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
  (((N ^ 2 + 1) / (Y' + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) +
  ((N : ℝ) / 25 * (1 - PU z₁) + ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1)) +
  ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ +
  G +
  ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((N : ℝ) / (p * p) + 1)

/- ### Residue facts -/

/-- (F2) -/
lemma not25_star {a b : ℕ} (ha : a % 25 = 7 ∨ a % 25 = 18) (hb : IsStar b) :
    ¬ 5 * 5 ∣ a * b + 1 := by
  intro h
  have h0 : (a * b + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h)
  rw [mod_mul_add_one] at h0
  have := Nat.mod_lt b (show 0 < 25 by norm_num)
  unfold IsStar at hb
  rcases ha with ha | ha <;> rw [ha] at h0 <;> interval_cases hr : b % 25 <;> omega

/-- (F3) -/
lemma not25_7_18 {a b : ℕ} (h : (a % 25 = 7 ∧ b % 25 = 18) ∨ (a % 25 = 18 ∧ b % 25 = 7)) :
    ¬ 5 * 5 ∣ a * b + 1 := by
  intro hd
  have h0 : (a * b + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using hd)
  rw [mod_mul_add_one] at h0
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] at h0 <;> norm_num at h0

/-- (F4), even case. -/
lemma not4_even {a b : ℕ} (h : a % 2 = 0 ∨ b % 2 = 0) : ¬ 2 * 2 ∣ a * b + 1 := by
  intro hd
  have h2 : 2 ∣ a * b + 1 := dvd_trans ⟨2, rfl⟩ hd
  have : 2 ∣ a * b := by
    rcases h with h | h
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) b
    · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) a
  omega

/-- (F4), odd case: `a ≡ b ≡ r (mod 4)` with `r` odd. -/
lemma not4_same {a b : ℕ} (h : (a % 4 = 1 ∧ b % 4 = 1) ∨ (a % 4 = 3 ∧ b % 4 = 3)) :
    ¬ 2 * 2 ∣ a * b + 1 := by
  intro hd
  have h0 : (a * b + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using hd)
  rw [mod_mul_add_one] at h0
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] at h0 <;> norm_num at h0

lemma coprime100 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) : Nat.Coprime 100 p := by
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have : p ∣ 2 ^ 2 * 5 ^ 2 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp this with h' | h'
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h'))

lemma coprime25 {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : Nat.Coprime 25 p := by
  have := (Nat.coprime_primes Nat.prime_five hp).mpr (Ne.symm h5)
  exact Nat.Coprime.pow_left 2 this

lemma coprime_U1 {p : ℕ} (hU : IsU1 p) : Nat.Coprime 100 p :=
  coprime100 hU.1 (by have := hU.2.2; omega) (by have := hU.2.2; omega)

/- ### Assembling one witness -/

lemma badCount_resB (N b q T z pc Y : ℕ) (Tset excl : Finset ℕ) (Pa : ℕ → Prop)
    [DecidablePred Pa] (hb : 1 ≤ b) (hY : 1 ≤ Y) (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q)
    (hTc : Tset.card = T) (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p)
    (hT : ∀ a, Pa a → a % q ∈ Tset) (hexcl : ∀ a, Pa a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (badCount N Pa b : ℝ) ≤ resB N q T z pc excl + shB N b pc Y := by
  have := badCount_le N b q z pc Y Tset excl Pa hb hY hq hTq hcop hT hexcl
  unfold resB shB; rw [← hTc]; linarith

lemma vCount_lemBB (N q T zB pB Y' : ℕ) (Tset : Finset ℕ) (Px : ℕ → Prop) [DecidablePred Px]
    (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q) (hTc : Tset.card = T)
    (hcop : ∀ p, p.Prime → IsU1 p → Nat.Coprime q p)
    (hT : ∀ x, Px x → x % q ∈ Tset) (hstar : ∀ x, Px x → IsStar x) :
    (vCount N Px : ℝ) ≤ lemBB N q T zB pB Y' := by
  have := vCount_le N q zB pB Y' Tset Px hq hTq hcop hT hstar
  unfold lemBB; rw [← hTc]; linarith

/-- A whole set of classes mod 100. -/
lemma classCount_le (N : ℕ) (D : Finset ℕ) (hD : ∀ t ∈ D, t < 100) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ a, P a → a % 100 ∈ D) :
    (classCount N P : ℝ) ≤ D.card * ((N : ℝ) / 100) + D.card := by
  have h := card_mod_mem_real N 100 (by norm_num) D hD
  rw [abs_le] at h
  have hsub : classCount N P ≤ ((Icc 1 N).filter (fun a => a % 100 ∈ D)).card := by
    unfold classCount; apply card_le_card; intro a ha
    rw [mem_filter] at ha ⊢; exact ⟨ha.1, hP a ha.2⟩
  have : (classCount N P : ℝ) ≤ ((Icc 1 N).filter (fun a => a % 100 ∈ D)).card := by
    exact_mod_cast hsub
  push_cast at h
  linarith

/- ### The cases -/

theorem caseIb_real (N b b' z pc Y : ℕ) (hY : 1 ≤ Y) (hw : Witness N b) (h7 : b % 25 = 7)
    (hw' : Witness N b') (h18 : b' % 25 = 18) :
    (badCount N (fun a => a % 25 = 18) b : ℝ) + badCount N (fun a => a % 25 = 7) b' ≤
      (resB N 25 1 z pc {5} + shB N b pc Y) + (resB N 25 1 z pc {5} + shB N b' pc Y) := by
  have e1 := badCount_resB N b 25 1 z pc Y {18} {5} (fun a => a % 25 = 18) hw.1 hY (by norm_num)
    (by simp) (by simp) (fun p hp hne => coprime25 hp (by simpa using hne)) (by simp)
    (fun a ha p hp => by
      rw [mem_singleton] at hp; subst hp; exact not25_7_18 (Or.inr ⟨ha, h7⟩))
  have e2 := badCount_resB N b' 25 1 z pc Y {7} {5} (fun a => a % 25 = 7) hw'.1 hY (by norm_num)
    (by simp) (by simp) (fun p hp hne => coprime25 hp (by simpa using hne)) (by simp)
    (fun a ha p hp => by
      rw [mem_singleton] at hp; subst hp; exact not25_7_18 (Or.inl ⟨ha, h18⟩))
  linarith

theorem caseII_real (N b z pc Y z₁ z₂ pB Y' : ℕ) (G : ℝ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hbs : IsStar b) (hbe : b % 2 = 0) (h5 : 5 ≤ z₂)
    (hG : ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 → ∑ p ∈ S, gC N z₁ p ≤ G) :
    (badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b : ℝ) + lemCCount N b ≤
      resB N 25 2 z pc {2, 5} + lemCB N z₁ z₂ pB Y' pc G + shB N b pc Y := by
  classical
  set Tset : Finset ℕ := {7, 18}
  set Bset := (Icc 1 N).filter (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Squarefree (a * b + 1))
  set R := Tset.biUnion (fun t => resPart N b 25 t pc {2, 5})
  have hB := witness_cover N b 25 pc Y Tset {2, 5} (fun a => a % 25 = 7 ∨ a % 25 = 18)
    (fun a ha => by simp only [Tset, mem_insert, mem_singleton]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_even (Or.inr hbe)
      · exact not25_star ha hbs)
  have hC := lemC_cover N b z₁ z₂ pB Y' pc Y hbe
  have hdisj : Disjoint Bset (lemCSet N b) := by
    rw [disjoint_left]; intro a ha hc
    simp only [Bset, lemCSet, mem_filter] at ha hc
    unfold IsStar at hc; omega
  have hsub : Bset ∪ lemCSet N b ⊆ ((R ∪ lemCPart N b z₁ z₂ pB Y' pc) ∪ midSet N b pc Y) ∪
      exSet N b Y := by
    intro a ha
    rcases mem_union.mp ha with h | h
    · have := hB h
      simp only [mem_union] at this ⊢; tauto
    · have := hC h
      simp only [mem_union] at this ⊢; tauto
  have hcard : Bset.card + (lemCSet N b).card ≤ R.card + (lemCPart N b z₁ z₂ pB Y' pc).card +
      (midSet N b pc Y).card + (exSet N b Y).card := by
    rw [← card_union_of_disjoint hdisj]
    have a0 := card_le_card hsub
    have a1 := Finset.card_union_le ((R ∪ lemCPart N b z₁ z₂ pB Y' pc) ∪ midSet N b pc Y)
      (exSet N b Y)
    have a2 := Finset.card_union_le (R ∪ lemCPart N b z₁ z₂ pB Y' pc) (midSet N b pc Y)
    have a3 := Finset.card_union_le R (lemCPart N b z₁ z₂ pB Y' pc)
    omega
  have hcardR : (badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b : ℝ) + lemCCount N b ≤
      (R.card : ℝ) + (lemCPart N b z₁ z₂ pB Y' pc).card + (midSet N b pc Y).card +
        (exSet N b Y).card := by
    have : badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount N b ≤ R.card +
        (lemCPart N b z₁ z₂ pB Y' pc).card + (midSet N b pc Y).card + (exSet N b Y).card :=
      hcard
    exact_mod_cast this
  have hR : (R.card : ℝ) ≤ resB N 25 2 z pc {2, 5} := by
    have h1 : (R.card : ℝ) ≤ ∑ t ∈ Tset, ((resPart N b 25 t pc {2, 5}).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have h2 := sum_le_sum (fun t (ht : t ∈ Tset) => card_resPart_le N b 25 t z pc {2, 5}
      (by norm_num) (by simp only [Tset, mem_insert, mem_singleton] at ht; omega)
      (fun p hp hne => coprime25 hp (by simp at hne; exact hne.2)))
    rw [sum_const, show Tset.card = 2 by decide, nsmul_eq_mul] at h2
    unfold resB; push_cast at h2 ⊢; linarith
  have hCP := card_lemCPart_le N b z₁ z₂ pB Y' pc G hw.2.1 hbs h5 hG
  have hmid := card_midSet_le N b pc Y
  have hex := card_exSet_le N b Y hw.1 hY
  unfold lemCB shB
  linarith

/-- The 23 odd classes mod 50 of `A*`. -/
def T50 : Finset ℕ := (range 50).filter (fun t => t % 2 = 1 ∧ t % 25 ≠ 7 ∧ t % 25 ≠ 18)

/-- The 23 classes mod 100 of `A*` in the class `r` mod 4. -/
def T100 (r : ℕ) : Finset ℕ := (range 100).filter (fun t => t % 25 ≠ 7 ∧ t % 25 ≠ 18 ∧ t % 4 = r)

lemma T100_card {r : ℕ} (hr : r = 1 ∨ r = 3) : (T100 r).card = 23 := by
  rcases hr with rfl | rfl <;> decide

lemma vCount_III2 (N zB pB Y' r : ℕ) (hr : r = 1 ∨ r = 3) :
    (vCount N (fun x => IsStar x ∧ x % 4 = r) : ℝ) ≤ lemBB N 100 23 zB pB Y' :=
  vCount_lemBB N 100 23 zB pB Y' (T100 r) _ (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) (T100_card hr)
    (fun p _ hU => coprime_U1 hU)
    (fun x hx => by
      unfold IsStar at hx
      simp only [T100, mem_filter, mem_range]; omega)
    (fun x hx => hx.1)

theorem caseIII1_real (N b₁ b₃ z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y)
    (hw₁ : Witness N b₁) (hs₁ : IsStar b₁) (hr₁ : b₁ % 4 = 1)
    (hw₃ : Witness N b₃) (hs₃ : IsStar b₃) (hr₃ : b₃ % 4 = 3) :
    (badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ : ℝ) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
      vCount N (fun x => IsStar x ∧ x % 2 = 1) ≤
      (resB N 100 6 z pc {2, 5} + shB N b₁ pc Y) + (resB N 100 2 z pc {2, 5} + shB N b₃ pc Y) +
        lemBB N 50 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  have e1 := badCount_resB N b₁ 100 6 z pc Y {32, 57, 82, 18, 68, 93} {2, 5}
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) hw₁.1 hY
    (by norm_num) (by simp) (by decide) hcop
    (fun a ha => by simp only [mem_insert, mem_singleton]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases ha.2 with h | h
        · exact not4_same (Or.inl ⟨h, hr₁⟩)
        · exact not4_even (Or.inl h)
      · exact not25_star ha.1 hs₁)
  have e3 := badCount_resB N b₃ 100 2 z pc Y {7, 43} {2, 5}
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) hw₃.1 hY
    (by norm_num) (by simp) (by decide) hcop
    (fun a ha => by simp only [mem_insert, mem_singleton]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_same (Or.inr ⟨ha.2, hr₃⟩)
      · exact not25_star ha.1 hs₃)
  have ev := vCount_lemBB N 50 23 zB pB Y' T50 (fun x => IsStar x ∧ x % 2 = 1) (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) (by decide)
    (fun p _ hU => Nat.Coprime.coprime_dvd_left (by norm_num) (coprime_U1 hU))
    (fun x hx => by
      have := hx.1; unfold IsStar at this
      simp only [T50, mem_filter, mem_range]; omega)
    (fun x hx => hx.1)
  linarith

theorem caseIII2a_real (N b r z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3) :
    (classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) : ℝ) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
      vCount N (fun x => IsStar x ∧ x % 4 = r) ≤
      (2 * ((N : ℝ) / 100) + 2) + (resB N 100 2 z pc {2, 5} + shB N b pc Y) +
        lemBB N 100 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  set D := (range 100).filter (fun t => (t % 25 = 7 ∨ t % 25 = 18) ∧ t % 4 = 4 - r)
  have hD : D.card = 2 := by rcases hr with rfl | rfl <;> decide
  have ec := classCount_le N D (fun t ht => mem_range.mp (mem_filter.mp ht).1)
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r)
    (fun a ha => by simp only [D, mem_filter, mem_range]; omega)
  rw [hD] at ec
  set Ts := (range 100).filter (fun t => (t % 25 = 7 ∨ t % 25 = 18) ∧ t % 4 = r)
  have hTs : Ts.card = 2 := by rcases hr with rfl | rfl <;> decide
  have eb := badCount_resB N b 100 2 z pc Y Ts {2, 5}
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) hw.1 hY (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) hTs hcop
    (fun a ha => by simp only [Ts, mem_filter, mem_range]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases hr with rfl | rfl
        · exact not4_same (Or.inl ⟨ha.2, hbr⟩)
        · exact not4_same (Or.inr ⟨ha.2, hbr⟩)
      · exact not25_star ha.1 hs)
  have ev := vCount_III2 N zB pB Y' r hr
  push_cast at ec
  linarith

theorem caseIII2b7_real (N b b' r z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3)
    (hw' : Witness N b') (h7 : b' % 25 = 7) (he : b' % 2 = 0) :
    (classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) : ℝ) +
      badCount N (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 18) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = r) ≤
      ((N : ℝ) / 100 + 1) + (resB N 100 3 z pc {2, 5} + shB N b pc Y) +
        (resB N 25 1 z pc {2, 5} + shB N b' pc Y) + lemBB N 100 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  set D := (range 100).filter (fun t => t % 25 = 7 ∧ t % 4 = 4 - r)
  have hD : D.card = 1 := by rcases hr with rfl | rfl <;> decide
  have ec := classCount_le N D (fun t ht => mem_range.mp (mem_filter.mp ht).1)
    (fun a => a % 25 = 7 ∧ a % 4 = 4 - r)
    (fun a ha => by simp only [D, mem_filter, mem_range]; omega)
  rw [hD] at ec
  set Ts := (range 100).filter (fun t => t % 25 = 7 ∧ (t % 4 = r ∨ t % 2 = 0))
  have hTs : Ts.card = 3 := by rcases hr with rfl | rfl <;> decide
  have eb := badCount_resB N b 100 3 z pc Y Ts {2, 5}
    (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) hw.1 hY (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) hTs hcop
    (fun a ha => by simp only [Ts, mem_filter, mem_range]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases ha.2 with h | h
        · rcases hr with rfl | rfl
          · exact not4_same (Or.inl ⟨h, hbr⟩)
          · exact not4_same (Or.inr ⟨h, hbr⟩)
        · exact not4_even (Or.inl h)
      · exact not25_star (Or.inl ha.1) hs)
  have eb' := badCount_resB N b' 25 1 z pc Y {18} {2, 5} (fun a => a % 25 = 18) hw'.1 hY
    (by norm_num) (by simp) (by simp)
    (fun p hp hne => coprime25 hp (by simp at hne; exact hne.2)) (by simp)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_even (Or.inr he)
      · exact not25_7_18 (Or.inr ⟨ha, h7⟩))
  have ev := vCount_III2 N zB pB Y' r hr
  push_cast at ec
  linarith

theorem caseIII2b18_real (N b b' r z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3)
    (hw' : Witness N b') (h18 : b' % 25 = 18) (he : b' % 2 = 0) :
    (classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) : ℝ) +
      badCount N (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 7) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = r) ≤
      ((N : ℝ) / 100 + 1) + (resB N 100 3 z pc {2, 5} + shB N b pc Y) +
        (resB N 25 1 z pc {2, 5} + shB N b' pc Y) + lemBB N 100 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  set D := (range 100).filter (fun t => t % 25 = 18 ∧ t % 4 = 4 - r)
  have hD : D.card = 1 := by rcases hr with rfl | rfl <;> decide
  have ec := classCount_le N D (fun t ht => mem_range.mp (mem_filter.mp ht).1)
    (fun a => a % 25 = 18 ∧ a % 4 = 4 - r)
    (fun a ha => by simp only [D, mem_filter, mem_range]; omega)
  rw [hD] at ec
  set Ts := (range 100).filter (fun t => t % 25 = 18 ∧ (t % 4 = r ∨ t % 2 = 0))
  have hTs : Ts.card = 3 := by rcases hr with rfl | rfl <;> decide
  have eb := badCount_resB N b 100 3 z pc Y Ts {2, 5}
    (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) hw.1 hY (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) hTs hcop
    (fun a ha => by simp only [Ts, mem_filter, mem_range]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases ha.2 with h | h
        · rcases hr with rfl | rfl
          · exact not4_same (Or.inl ⟨h, hbr⟩)
          · exact not4_same (Or.inr ⟨h, hbr⟩)
        · exact not4_even (Or.inl h)
      · exact not25_star (Or.inr ha.1) hs)
  have eb' := badCount_resB N b' 25 1 z pc Y {7} {2, 5} (fun a => a % 25 = 7) hw'.1 hY
    (by norm_num) (by simp) (by simp)
    (fun p hp hne => coprime25 hp (by simp at hne; exact hne.2)) (by simp)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_even (Or.inr he)
      · exact not25_7_18 (Or.inl ⟨ha, h18⟩))
  have ev := vCount_III2 N zB pB Y' r hr
  push_cast at ec
  linarith

end Erdos848
end

section

/-
# Phase 7 (part 2): soundness of the interval checker

Bridges between the executable definitions of `ErdosComp/Check.lean` and the mathematical
quantities of `Cases.lean`.
-/

namespace Erdos848

open Finset ErdosComp

/- ### The primality test is exact -/

lemma minFacAux_spec {n : ℕ} (hodd : n % 2 = 1) : ∀ f k, k % 2 = 1 → 3 ≤ k →
    n < (k + 2 * f) * (k + 2 * f) → ErdosComp.minFacAux n k f = n →
    ∀ d, k ≤ d → d * d ≤ n → ¬ d ∣ n := by
  intro f
  induction f with
  | zero =>
    intro k _hk _hk3 hlt _hres d hd hdd _hdvd
    have : k * k ≤ d * d := Nat.mul_le_mul hd hd
    simp only [mul_zero, add_zero] at hlt; omega
  | succ f ih =>
    intro k hk hk3 hlt hres d hd hdd hdvd
    simp only [ErdosComp.minFacAux] at hres
    split_ifs at hres with h1 h2
    · have : k * k ≤ d * d := Nat.mul_le_mul hd hd
      omega
    · -- returned k = n, impossible since k * k ≤ n
      push Not at h1
      have : k * k ≤ k := hres ▸ h1
      nlinarith
    · rcases Nat.lt_or_ge d (k + 2) with hlt2 | hge
      · rcases (show d = k ∨ d = k + 1 by omega) with rfl | rfl
        · exact h2 (by simpa using Nat.mod_eq_zero_of_dvd hdvd)
        · have h2k : 2 ∣ k + 1 := by omega
          have := Nat.dvd_trans h2k hdvd
          omega
      · exact ih (k + 2) (by omega) (by omega) (by nlinarith) hres d hge hdd hdvd

lemma prime_of_isPrimeB {n : ℕ} (h : isPrimeB n = true) : n.Prime := by
  unfold isPrimeB at h
  by_cases h1 : n < 2
  · simp [h1] at h
  by_cases h2 : n % 2 = 0
  · simp only [h1, h2, ↓reduceIte, beq_self_eq_true, beq_iff_eq] at h
    subst h; exact Nat.prime_two
  simp only [h1, ↓reduceIte, beq_iff_eq, h2] at h
  have hodd : n % 2 = 1 := by omega
  rw [Nat.prime_def_le_sqrt]
  refine ⟨by omega, fun m hm hms hdvd => ?_⟩
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
  · omega
  · exact minFacAux_spec hodd n 3 rfl le_rfl (by nlinarith) h m h3 hmm hdvd

lemma isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime :=
  ⟨prime_of_isPrimeB, isPrimeB_of_prime⟩

lemma isU1B_iff (n : ℕ) : isU1B n = true ↔ IsU1 n := by
  unfold isU1B IsU1
  simp only [Bool.and_eq_true, isPrimeB_iff, beq_iff_eq, decide_eq_true_eq]
  tauto

/- ### Finite products and sums -/

lemma prodF_eq (cond : ℕ → Bool) (f : ℕ → ℚ) (n : ℕ) :
    prodF cond f n = ∏ p ∈ (range n).filter (fun p => cond p = true), f p := by
  induction n with
  | zero => simp [prodF]
  | succ n ih =>
    rw [prodF, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [prod_insert (by simp), mul_comm]
    · rw [mul_one]

lemma sumF_eq (cond : ℕ → Bool) (f : ℕ → ℚ) (n : ℕ) :
    sumF cond f n = ∑ p ∈ (range n).filter (fun p => cond p = true), f p := by
  induction n with
  | zero => simp [sumF]
  | succ n ih =>
    rw [sumF, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [sum_insert (by simp), add_comm]
    · rw [add_zero]

lemma cntF_eq (cond : ℕ → Bool) (n : ℕ) :
    cntF cond n = ((range n).filter (fun p => cond p = true)).card := by
  induction n with
  | zero => simp [cntF]
  | succ n ih =>
    rw [cntF, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]
    · rw [add_zero]

/- ### The small prime sets -/

lemma smallP_excl5 : smallP 31 (· ∉ ({5} : Finset ℕ)) =
    (range 32).filter (fun p => condP [5] p = true) := by
  ext p; simp [smallP, condP, isPrimeB_iff]

lemma smallP_excl25 : smallP 31 (· ∉ ({2, 5} : Finset ℕ)) =
    (range 32).filter (fun p => condP [2, 5] p = true) := by
  ext p; simp [smallP, condP, isPrimeB_iff]

lemma smallP_U : smallP 41 IsU1 = (range 42).filter (fun p => isU1B p = true) := by
  ext p; simp only [smallP, mem_filter, isU1B_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2⟩⟩

lemma smallP_U_erase (p : ℕ) :
    (smallP 41 IsU1).erase p = (range 42).filter (fun q => condE p q = true) := by
  rw [smallP_U]; ext q
  simp only [mem_erase, mem_filter, condE, Bool.and_eq_true, bne_iff_ne]
  tauto

lemma smallP_odd : smallP 1000 (fun p => p ≠ 2 ∧ p ≠ 5) =
    (range 1001).filter (fun p => condOdd p = true) := by
  ext p
  simp only [smallP, mem_filter, condOdd, Bool.and_eq_true, bne_iff_ne, isPrimeB_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, h4⟩
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

/- ### `ρ` -/

lemma OPc_eq : OPc = OP := by decide

lemma primeProdC_eq (k : ℕ) : primeProdC k = primeProd k := by
  unfold primeProdC primeProd; rw [OPc_eq]

lemma primeProd_mono {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ 45) : primeProd j ≤ primeProd k := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · rw [h]
    · rw [primeProd_succ (by omega)]
      have h1 : 1 ≤ OP[k]! := by
        have : ∀ k < 45, 1 ≤ OP[k]! := by decide
        exact this k (by omega)
      calc primeProd j ≤ primeProd k := ih (by omega) (by omega)
        _ ≤ primeProd k * OP[k]! := Nat.le_mul_of_pos_right _ h1

lemma countP_range_ge (P : ℕ → Bool) : ∀ n k, k ≤ n → (∀ j < k, P j = true) →
    k ≤ (List.range n).countP P := by
  intro n
  induction n with
  | zero => intro k hk _; omega
  | succ n ih =>
    intro k hk hP
    rw [List.range_succ, List.countP_append]
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · have := ih k (by omega) hP; omega
    · have hk' : k = n + 1 := by omega
      have := ih n le_rfl (fun j hj => hP j (by omega))
      have hn : P n = true := hP n (by omega)
      simp [hn]; omega

lemma le_Wc {k L : ℕ} (hk : k ≤ 45) (h : primeProd k ≤ L) : k ≤ Wc L := by
  unfold Wc
  rw [← List.countP_eq_length_filter]
  apply countP_range_ge _ 45 k hk
  intro j hj
  simp only [decide_eq_true_eq, primeProdC_eq]
  exact (primeProd_mono (by omega) hk).trans h

lemma W_le_Wc (L : ℕ) : W L ≤ Wc L := by
  rcases Nat.eq_zero_or_pos (W L) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hP : primeProd (W L) ≤ L :=
      Nat.findGreatest_of_ne_zero (P := fun k => primeProd k ≤ L) (n := 45) rfl
        (Nat.pos_iff_ne_zero.mp hpos)
    exact le_Wc (Nat.findGreatest_le 45) hP

lemma rhoMax_le_rhoMaxC (N : ℕ) : rhoMax N ≤ rhoMaxC N := by
  unfold rhoMax rhoMaxC
  have h1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (W_le_Wc N)
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (W_le_Wc (N / 4))
  have h3 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (W_le_Wc (N / 8))
  omega

/-- `ρ`-bound for a witness `b ≤ N_hi`. -/
lemma rhoBound_le_C {b Nhi : ℕ} (hb : 1 ≤ b) (hbN : b ≤ Nhi) (hN : Nhi < primeProdC 45) :
    rhoBound b ≤ rhoMaxC Nhi :=
  (rhoBound_le_rhoMax hb hbN (by rw [← primeProdC_eq]; exact hN)).trans (rhoMax_le_rhoMaxC Nhi)

/- ### `log₃` -/

lemma log3Go_ge (n : ℕ) : ∀ f k, k ≤ log3Go n f k := by
  intro f
  induction f with
  | zero => intro k; simp [log3Go]
  | succ f ih =>
    intro k; simp only [log3Go]; split_ifs
    · exact (Nat.le_succ k).trans (ih (k + 1))
    · exact le_rfl

lemma log3Go_reach (n m : ℕ) (hm : 3 ^ m ≤ n) : ∀ f k, k ≤ m → m ≤ k + f → m ≤ log3Go n f k := by
  intro f
  induction f with
  | zero => intro k hk hkf; simp only [log3Go]; omega
  | succ f ih =>
    intro k hk hkf
    simp only [log3Go]
    rcases Nat.lt_or_ge k m with hlt | hge
    · have : 3 ^ (k + 1) ≤ n := (Nat.pow_le_pow_right (by norm_num) hlt).trans hm
      simp only [this, ↓reduceIte]; exact ih (k + 1) hlt (by omega)
    · split_ifs
      · exact (show m ≤ k + 1 by omega).trans (log3Go_ge n f (k + 1))
      · omega

lemma log_le_log3C {N Nhi : ℕ} (h : N ≤ Nhi) : Nat.log 3 N ≤ log3C Nhi := by
  have hmono : Nat.log 3 N ≤ Nat.log 3 Nhi := Nat.log_mono_right h
  refine hmono.trans ?_
  rcases Nat.eq_zero_or_pos Nhi with h0 | hpos
  · subst h0; simp
  have hm : 3 ^ Nat.log 3 Nhi ≤ Nhi := Nat.pow_log_le_self 3 (by omega)
  have hmn : Nat.log 3 Nhi ≤ Nhi := (Nat.lt_pow_self (by norm_num)).le.trans hm
  exact log3Go_reach Nhi _ hm Nhi 0 (Nat.zero_le _) (by omega)

/-- The Pell factor is monotone in `N`. -/
lemma pell_le_pellC {N Nhi : ℕ} (h : N ≤ Nhi) (Y : ℕ) :
    (N ^ 2 + 1) / (Y + 1) ^ 2 * (Nat.log 3 N + 1) ≤ pellC Nhi Y := by
  unfold pellC
  apply Nat.mul_le_mul
  · rw [sq, sq]; apply Nat.div_le_div_right; exact Nat.add_le_add_right (Nat.mul_le_mul h h) 1
  · exact Nat.add_le_add_right (log_le_log3C h) 1

/- ### The first 30 U1 primes -/

lemma UL_spec : ∀ j < 30, isU1B (UL.getD j 0) = true ∧ cntF isU1B (UL.getD j 0) = j := by
  decide +kernel

lemma count_U1_eq (n : ℕ) : Nat.count IsU1 n = cntF isU1B n := by
  rw [Nat.count_eq_card_filter_range, cntF_eq]
  congr 1; apply filter_congr; intro p _; rw [isU1B_iff]

lemma u1_eq_UL {j : ℕ} (hj : j < 30) : u1 j = UL.getD j 0 := by
  obtain ⟨h1, h2⟩ := UL_spec j hj
  have hU : IsU1 (UL.getD j 0) := (isU1B_iff _).mp h1
  unfold u1
  conv_lhs => rw [← h2, ← count_U1_eq]
  exact Nat.nth_count hU

/- ### Casting the constants -/

lemma prod1_cast (excl : List ℕ) :
    ((prod1 excl : ℚ) : ℝ) = ∏ p ∈ (range 32).filter (fun p => condP excl p = true),
      (1 - 1 / ((p : ℝ) * p)) := by
  unfold prod1; rw [prodF_eq]; push_cast; rfl

lemma k1_eq (excl : List ℕ) : k1 excl = ((range 32).filter (fun p => condP excl p = true)).card := by
  unfold k1; rw [cntF_eq]

lemma prodU_cast : ((prodU : ℚ) : ℝ) = PU 41 := by
  unfold prodU PU; rw [prodF_eq, smallP_U]; push_cast; rfl

lemma kU_eq : kU = (smallP 41 IsU1).card := by unfold kU; rw [cntF_eq, smallP_U]

lemma prErase_cast (p : ℕ) : ((prErase p : ℚ) : ℝ) =
    ∏ q ∈ (smallP 41 IsU1).erase p, (1 - 2 / ((q : ℝ) * q)) := by
  unfold prErase; rw [prodF_eq, smallP_U_erase]; push_cast; rfl

lemma kErase_eq (p : ℕ) : kErase p = ((smallP 41 IsU1).erase p).card := by
  unfold kErase; rw [cntF_eq, smallP_U_erase]

lemma prErase_nonneg (p : ℕ) : (0 : ℝ) ≤ ((prErase p : ℚ) : ℝ) := by
  rw [prErase_cast]
  apply prod_nonneg; intro q hq
  exact (factor_pos (mem_filter.mp (mem_of_mem_erase hq)).2.1).le

lemma gC_eq (N p : ℕ) : gC N 41 p = ((gA p : ℚ) : ℝ) * N + ((gE p : ℚ) : ℝ) := by
  unfold gC wholeB nonB gA gE
  push_cast
  rw [prErase_cast, kErase_eq]
  ring

lemma sumNon_eq (N : ℕ) : ∑ p ∈ smallP 1000 (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p 41 =
    ((cNon : ℚ) : ℝ) * N + ((eNon : ℚ) : ℝ) := by
  unfold cNon eNon
  rw [sumF_eq, sumF_eq, smallP_odd]
  push_cast
  rw [sum_mul, ← sum_add_distrib]
  apply sum_congr rfl; intro p _
  unfold nonB
  rw [← prErase_cast, ← kErase_eq]
  ring

/- ### Prime-range sums -/

lemma midsum_le (P S : Finset ℕ) (hPS : P ⊆ S) (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ P, (a / ((p : ℝ) * p) + 1) ≤ a * S2 S + S.card := by
  have h1 : ∑ p ∈ P, (a / ((p : ℝ) * p) + 1) = a * S2 P + P.card := by
    unfold S2; rw [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul, mul_one]
    congr 1; apply sum_congr rfl; intro p _; ring
  have h2 : S2 P ≤ S2 S := S2_mono hPS
  have h3 : (P.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hPS
  rw [h1]; nlinarith

lemma midP_sub_primesIn (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    midP z w Q ⊆ primesIn z w := fun p hp => by
  simp only [midP, primesIn, mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩

lemma midP_sub_u1In (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ p, Q p → IsU1 p) :
    midP z w Q ⊆ u1In z w := fun p hp => by
  simp only [midP, u1In, mem_filter] at hp ⊢; exact ⟨hp.1, hQ p hp.2.2⟩

lemma sum_two (P : Finset ℕ) (a : ℝ) :
    ∑ p ∈ P, (2 * (a / ((p : ℝ) * p)) + 2) = 2 * ∑ p ∈ P, (a / ((p : ℝ) * p) + 1) := by
  rw [mul_sum]; apply sum_congr rfl; intro p _; ring

lemma gmax_le (a e : ℝ) (ha : 0 ≤ a) {N Nlo : ℝ} (h : Nlo ≤ N) :
    max (a * N + e) 0 ≤ a * N + max e (-a * Nlo) := by
  rcases le_total 0 (a * N + e) with h0 | h0
  · rw [max_eq_left h0]; linarith [le_max_left e (-a * Nlo)]
  · rw [max_eq_right h0]
    have := le_max_right e (-a * Nlo)
    nlinarith

lemma gA_nonneg (p : ℕ) : (0 : ℝ) ≤ ((gA p : ℚ) : ℝ) := by
  unfold gA; push_cast
  have := prErase_nonneg p
  positivity

lemma gsum_sound (N Nlo L : ℕ) (hL : L ≤ 30) (hN : Nlo ≤ N) :
    ∑ j ∈ range L, max (gC N 41 (u1 j)) 0 ≤
      ((gSumC L : ℚ) : ℝ) * N + ((gSumE Nlo L : ℚ) : ℝ) := by
  unfold gSumC gSumE
  rw [sumF_eq, sumF_eq]
  have hf : (range L).filter (fun _ => true = true) = range L := filter_true_of_mem (fun _ _ => rfl)
  rw [hf]
  push_cast
  rw [sum_mul, ← sum_add_distrib]
  apply sum_le_sum; intro j hj
  have hj30 : j < 30 := by have := mem_range.mp hj; omega
  rw [u1_eq_UL hj30, gC_eq]
  have := gmax_le ((gA (UL.getD j 0) : ℚ) : ℝ) ((gE (UL.getD j 0) : ℚ) : ℝ) (gA_nonneg _)
    (show (Nlo : ℝ) ≤ N by exact_mod_cast hN)
  push_cast at this
  linarith

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

lemma primeSum_le (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + 1) ≤
      a * ((s2P tab z w : ℚ) : ℝ) + ((cP tab z w : ℚ) : ℝ) := by
  have := midsum_le _ _ (midP_sub_primesIn z w Q) a ha
  have h1 := S2_primesIn_le htab z w
  have h2 := card_primesIn_le htab z w
  nlinarith

lemma u1Sum_le (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ p, Q p → IsU1 p)
    (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + 1) ≤
      a * ((s2U tab z w : ℚ) : ℝ) + ((cU tab z w : ℚ) : ℝ) := by
  have := midsum_le _ _ (midP_sub_u1In z w Q hQ) a ha
  have h1 := S2_u1In_le htab z w
  have h2 := card_u1In_le htab z w
  nlinarith

/- ### The components -/

lemma res_sound (N q T pc : ℕ) (excl : Finset ℕ) (exclL : List ℕ)
    (hS : smallP 31 (· ∉ excl) = (range 32).filter (fun p => condP exclL p = true)) :
    resB N q T 31 pc excl ≤
      ((resCE tab q T exclL pc).1 : ℝ) * N + ((resCE tab q T exclL pc).2 : ℝ) := by
  unfold resB resCE
  have hm := primeSum_le htab 31 pc (· ∉ excl) ((N : ℝ) / q) (by positivity)
  have hT : (0 : ℝ) ≤ T := by positivity
  have := mul_le_mul_of_nonneg_left hm hT
  dsimp only
  push_cast
  rw [prod1_cast, k1_eq, ← hS]
  linear_combination this

lemma sh_sound (N Nhi b pc Y : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N) (hN : N ≤ Nhi)
    (hNhi : Nhi < primeProdC 45) (hY : 1 ≤ Y) :
    shB N b pc Y ≤ ((shCE tab Nhi pc Y).1 : ℝ) * N + ((shCE tab Nhi pc Y).2 : ℝ) := by
  unfold shB shCE
  have hm := primeSum_le htab pc Y (fun p => pc < p) (N : ℝ) (by positivity)
  have hρ : (rhoBound b : ℝ) ≤ rhoMaxC Nhi := by exact_mod_cast rhoBound_le_C hb (hbN.trans hN) hNhi
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hNR : (N : ℝ) ≤ Nhi := by exact_mod_cast hN
  have hbR : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hNb : (N : ℝ) * b ≤ (Nhi : ℝ) * Nhi := by
    have : (0 : ℝ) ≤ b := by positivity
    nlinarith
  have hG : 2 * ((N : ℝ) + 1) / Y + ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2 ≤
      2 * ((Nhi : ℝ) + 1) / Y + ((Nhi : ℝ) * Nhi + 1) / ((Y : ℝ) * Y) := by
    rw [sq]
    have hY0 : (0 : ℝ) < Y := by linarith
    gcongr
  have hG0 : 0 ≤ 2 * ((N : ℝ) + 1) / Y + ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2 := by positivity
  have hρ0 : (0 : ℝ) ≤ rhoBound b := by positivity
  have := mul_le_mul hρ hG hG0 (by positivity)
  dsimp only
  push_cast
  linarith

lemma lemB_sound (N Nhi q T pB YB : ℕ) (hN : N ≤ Nhi) :
    lemBB N q T 41 pB YB ≤
      ((lemBCE tab Nhi q T pB YB).1 : ℝ) * N + ((lemBCE tab Nhi q T pB YB).2 : ℝ) := by
  unfold lemBB lemBCE
  have h1 := u1Sum_le htab 41 pB IsU1 (fun _ h => h) ((N : ℝ) / q) (by positivity)
  have h2 := u1Sum_le htab pB YB (fun p => IsU1 p ∧ pB < p) (fun _ h => h.1) (N : ℝ)
    (by positivity)
  have hp : (((N ^ 2 + 1) / (YB + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) ≤ (pellC Nhi YB : ℝ) := by
    exact_mod_cast pell_le_pellC hN YB
  rw [sum_two, sum_two]
  have hT : (0 : ℝ) ≤ T := by positivity
  have h1' := mul_le_mul_of_nonneg_left h1 hT
  dsimp only
  push_cast
  rw [prodU_cast, kU_eq]
  unfold PU
  push_cast at hp
  linear_combination 2 * h1' + 2 * h2 + hp

lemma lemC_sound (N Nlo Nhi pB YB pc L : ℕ) (hL : L ≤ 30) (h1 : Nlo ≤ N) (h2 : N ≤ Nhi) :
    lemCB N 41 1000 pB YB pc (∑ j ∈ range L, max (gC N 41 (u1 j)) 0) ≤
      ((lemCCE tab Nlo Nhi pB YB pc L).1 : ℝ) * N + ((lemCCE tab Nlo Nhi pB YB pc L).2 : ℝ) := by
  unfold lemCB lemCCE
  have e1 := u1Sum_le htab 41 pB (fun p => IsU1 p ∧ 41 < p) (fun _ h => h.1) ((N : ℝ) / 25)
    (by positivity)
  have e2 := u1Sum_le htab pB YB (fun p => IsU1 p ∧ pB < p) (fun _ h => h.1) (N : ℝ)
    (by positivity)
  have e3 : (((N ^ 2 + 1) / (YB + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) ≤ (pellC Nhi YB : ℝ) := by
    exact_mod_cast pell_le_pellC h2 YB
  have e4 := sumNon_eq N
  have e5 := gsum_sound N Nlo L hL h1
  have e6 := primeSum_le htab 1000 pc (fun p => 1000 < p) (N : ℝ) (Nat.cast_nonneg N)
  rw [sum_two, sum_two]
  dsimp only
  push_cast
  rw [prodU_cast, kU_eq]
  push_cast at e3 e5
  linear_combination 46 * e1 + 2 * e2 + e3 + e4 + e5 + e6

end

/- ### Lemma D and one interval -/

lemma addCE_le {a b : CE} {N : ℕ} {X Y : ℝ} (hX : X ≤ (a.1 : ℝ) * N + a.2)
    (hY : Y ≤ (b.1 : ℝ) * N + b.2) :
    X + Y ≤ ((addCE a b).1 : ℝ) * N + (addCE a b).2 := by
  simp only [addCE]; push_cast; linarith

lemma const_le (a e : ℚ) (N : ℕ) : (a : ℝ) * N + e ≤ (((a, e) : CE).1 : ℝ) * N + ((a, e) : CE).2 :=
  le_rfl

/-- **Lemma D.** -/
lemma lemmaD {c : CE} {Nlo N X : ℕ} (hok : okCE Nlo c = true) (hN : Nlo ≤ N)
    (hX : (X : ℝ) ≤ (c.1 : ℝ) * N + c.2) : X ≤ c7 N := by
  unfold okCE at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨h1, h2⟩ := hok
  have h1R : (c.1 : ℝ) < 1 / 25 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h1; push_cast at this; exact this
  have h2R : (c.1 : ℝ) * Nlo + c.2 < ((Nlo : ℝ) - 6) / 25 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h2; push_cast at this; exact this
  have hNR : (Nlo : ℝ) ≤ N := by exact_mod_cast hN
  have hc7 : ((N : ℝ) - 6) / 25 ≤ c7 N := by
    unfold c7
    have := Nat.div_add_mod (N + 18) 25
    have := Nat.mod_lt (N + 18) (show 0 < 25 by norm_num)
    have h : N ≤ 25 * ((N + 18) / 25) + 6 := by omega
    have hR : (N : ℝ) ≤ 25 * (((N + 18) / 25 : ℕ) : ℝ) + 6 := by exact_mod_cast h
    linarith
  have : (X : ℝ) < c7 N := by nlinarith
  exact_mod_cast this.le

lemma ulProd_eq (n : ℕ) : ulProd n = ∏ j ∈ range n, UL.getD j 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ulProd, ih, prod_range_succ]

lemma ulProd_u1 {n : ℕ} (hn : n ≤ 30) : ulProd n = ∏ j ∈ range n, u1 j := by
  rw [ulProd_eq]; apply prod_congr rfl; intro j hj
  rw [u1_eq_UL (by have := mem_range.mp hj; omega)]

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

theorem countBounds_of_row (r : Row) (hr : checkRow tab r = true) (N : ℕ)
    (hlo : r.Nlo ≤ N) (hhi : N ≤ r.Nhi) : CountBounds N := by
  unfold checkRow at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hY, h7⟩, hlh⟩, hprod⟩, hL30⟩, hLc⟩, okIb⟩, okII⟩, okIII1⟩, okIIIa⟩, okIIIb⟩ := hr
  have hS5 := smallP_excl5
  have hS25 := smallP_excl25
  have sh : ∀ b, Witness N b → shB N b r.pc r.Y ≤
      ((shCE tab r.Nhi r.pc r.Y).1 : ℝ) * N + (shCE tab r.Nhi r.pc r.Y).2 :=
    fun b hw => sh_sound htab N r.Nhi b r.pc r.Y hw.1 hw.2.1 hhi hprod hY
  constructor
  · -- I.b
    intro b b' hw h7b hw' h18
    have := caseIb_real N b b' 31 r.pc r.Y hY hw h7b hw' h18
    have e := addCE_le (addCE_le (res_sound htab N 25 1 r.pc {5} [5] hS5) (sh b hw))
      (addCE_le (res_sound htab N 25 1 r.pc {5} [5] hS5) (sh b' hw'))
    exact lemmaD okIb hlo (by push_cast; exact this.trans e)
  · -- II
    intro b hw hs he
    have hL : N * N + 1 < (∏ j ∈ range (Lval r.Nhi + 1), u1 j) *
        (∏ j ∈ range (Lval r.Nhi + 1), u1 j) := by
      rw [← ulProd_u1 (n := Lval r.Nhi + 1) (by omega)]
      have : N * N ≤ r.Nhi * r.Nhi := Nat.mul_le_mul hhi hhi
      omega
    have := caseII_real N b 31 r.pc r.Y 41 1000 r.pB25 r.Y25 _ hY hw hs he
      (by norm_num) (gBound_prefix N 41 1000 (Lval r.Nhi) hL)
    have e := addCE_le (addCE_le (res_sound htab N 25 2 r.pc {2, 5} [2, 5] hS25)
      (lemC_sound htab N r.Nlo r.Nhi r.pB25 r.Y25 r.pc (Lval r.Nhi) (by omega) hlo hhi))
      (sh b hw)
    exact lemmaD okII hlo (by push_cast; exact this.trans e)
  · -- III.1
    intro b₁ b₃ hw₁ hs₁ hr₁ hw₃ hs₃ hr₃
    have := caseIII1_real N b₁ b₃ 31 r.pc r.Y 41 r.pB50 r.Y50 hY hw₁ hs₁ hr₁ hw₃ hs₃ hr₃
    have e := addCE_le (addCE_le
      (addCE_le (res_sound htab N 100 6 r.pc {2, 5} [2, 5] hS25) (sh b₁ hw₁))
      (addCE_le (res_sound htab N 100 2 r.pc {2, 5} [2, 5] hS25) (sh b₃ hw₃)))
      (lemB_sound htab N r.Nhi 50 23 r.pB50 r.Y50 hhi)
    exact lemmaD okIII1 hlo (by push_cast; exact this.trans e)
  · -- III.2.a
    intro b rr hw hs hbr hrr
    have := caseIII2a_real N b rr 31 r.pc r.Y 41 r.pB100 r.Y100 hY hw hs hbr hrr
    have hc : 2 * ((N : ℝ) / 100) + 2 ≤ (((2 / 100 : ℚ), (2 : ℚ)) : CE).1 * N +
        (((2 / 100 : ℚ), (2 : ℚ)) : CE).2 := by push_cast; linarith
    have e := addCE_le (addCE_le hc
      (addCE_le (res_sound htab N 100 2 r.pc {2, 5} [2, 5] hS25) (sh b hw)))
      (lemB_sound htab N r.Nhi 100 23 r.pB100 r.Y100 hhi)
    exact lemmaD okIIIa hlo (by push_cast; exact this.trans e)
  · -- III.2.b, even witness in A₇
    intro b b' rr hw hs hbr hrr hw' h7' he
    have := caseIII2b7_real N b b' rr 31 r.pc r.Y 41 r.pB100 r.Y100 hY hw hs hbr hrr hw' h7' he
    have hc : (N : ℝ) / 100 + 1 ≤ (((1 / 100 : ℚ), (1 : ℚ)) : CE).1 * N +
        (((1 / 100 : ℚ), (1 : ℚ)) : CE).2 := by push_cast; linarith
    have e := addCE_le (addCE_le (addCE_le hc
      (addCE_le (res_sound htab N 100 3 r.pc {2, 5} [2, 5] hS25) (sh b hw)))
      (addCE_le (res_sound htab N 25 1 r.pc {2, 5} [2, 5] hS25) (sh b' hw')))
      (lemB_sound htab N r.Nhi 100 23 r.pB100 r.Y100 hhi)
    exact lemmaD okIIIb hlo (by push_cast; exact this.trans e)
  · -- III.2.b, even witness in A₁₈
    intro b b' rr hw hs hbr hrr hw' h18' he
    have := caseIII2b18_real N b b' rr 31 r.pc r.Y 41 r.pB100 r.Y100 hY hw hs hbr hrr hw' h18' he
    have hc : (N : ℝ) / 100 + 1 ≤ (((1 / 100 : ℚ), (1 : ℚ)) : CE).1 * N +
        (((1 / 100 : ℚ), (1 : ℚ)) : CE).2 := by push_cast; linarith
    have e := addCE_le (addCE_le (addCE_le hc
      (addCE_le (res_sound htab N 100 3 r.pc {2, 5} [2, 5] hS25) (sh b hw)))
      (addCE_le (res_sound htab N 25 1 r.pc {2, 5} [2, 5] hS25) (sh b' hw')))
      (lemB_sound htab N r.Nhi 100 23 r.pB100 r.Y100 hhi)
    exact lemmaD okIIIb hlo (by push_cast; exact this.trans e)

end

/- ### Covering an interval of `N` -/

lemma chain_cover (b N : ℕ) : ∀ (rows : List Row) (a : ℕ), chain a b rows = true →
    (∀ r ∈ rows, r.Nlo ≤ r.Nhi) → rows ≠ [] → a ≤ N → N ≤ b →
    ∃ r ∈ rows, r.Nlo ≤ N ∧ N ≤ r.Nhi := by
  intro rows
  induction rows with
  | nil => intro a _ _ h; exact absurd rfl h
  | cons r rs ih =>
    intro a hc hle _ haN hNb
    simp only [chain, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hra, hc⟩ := hc
    by_cases hN : N ≤ r.Nhi
    · exact ⟨r, List.mem_cons_self .., hra ▸ haN, hN⟩
    · cases rs with
      | nil => simp [chain] at hc; omega
      | cons r' rs' =>
        obtain ⟨r'', hmem, h⟩ := ih r.Nhi hc (fun x hx => hle x (List.mem_cons_of_mem _ hx))
          (by simp) (by omega) hNb
        exact ⟨r'', List.mem_cons_of_mem _ hmem, h⟩

/-- **Soundness of the checker.** -/
theorem countBounds_of_checkAll {a b : ℕ} {rows : List Row} (hc : checkAll a b rows = true)
    (hne : rows ≠ []) (N : ℕ) (haN : a ≤ N) (hNb : N ≤ b) : CountBounds N := by
  unfold checkAll at hc
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hch, hall⟩ := hc
  have htab : ∀ e ∈ ([] : List (ℕ × PSt)), e.2 = stAt e.1 := by simp
  have hle : ∀ r ∈ rows, r.Nlo ≤ r.Nhi := by
    intro r hr
    have := hall r hr
    unfold checkRow at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1.1.1.1.2
  obtain ⟨r, hr, h1, h2⟩ := chain_cover b N rows a hch hle hne haN hNb
  exact countBounds_of_row htab r (hall r hr) N h1 h2

end Erdos848
end

open ErdosComp Erdos848
private def lowRows : List Row := [
  ⟨160000000, 176783285, 3988, 8039387, 2180391, 2242025, 2200504, 801, 2083, 2487⟩,
  ⟨176783285, 208411274, 4330, 9077976, 2452644, 2434336, 2484824, 870, 2261, 2700⟩,
  ⟨208411274, 270119770, 4930, 10749330, 2984016, 2997538, 2942026, 991, 2574, 3074⟩,
  ⟨270119770, 410681848, 6079, 14336176, 3944157, 3997661, 3923628, 1222, 3174, 3791⟩,
  ⟨410681848, 781497198, 8386, 19776800, 6120195, 6203217, 6088338, 1685, 4379, 5229⟩,
  ⟨781497198, 1007851533, 9524, 19967355, 7517380, 7326303, 7478251, 1914, 4973, 5939⟩,
  ⟨1007851533, 1182253286, 10315, 19994185, 8141857, 8252304, 8423457, 2073, 5386, 6432⟩,
  ⟨1182253286, 1319361736, 10896, 19526971, 8945065, 9066408, 8898505, 2190, 5690, 6795⟩,
  ⟨1319361736, 1407740760, 11255, 19394561, 9239807, 9365148, 9191713, 2262, 5878, 7019⟩,
  ⟨1407740760, 1618722525, 12070, 33299814, 10304362, 10444144, 10250726, 2426, 6303, 7526⟩]
set_option maxRecDepth 100000 in
private lemma lowNumeric : checkAll 160000000 1618722525 lowRows = true := by decide +kernel

theorem OMA.solution : OMA.R_Erdos848_erdos_848_R3_H3_R1_H1_R1.H1 := fun N hN hM => statement_of_bounds (countBounds_of_checkAll lowNumeric (by decide) N hN hM)
