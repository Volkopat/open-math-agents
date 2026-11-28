import OMAReductions.R_Erdos963_erdos_963_parts_ii_R1

-- Step Erdos963.erdos_963.parts.ii.R1.H1: hypothesis H1 of reduction Erdos963.erdos_963.parts.ii.R1
-- Written with Claude Code (AI-assisted).
-- Credit: the reduction and the statement of H1 are by @MrSeizy (reduction R1). The idea of
-- splitting a positive integer set into its odd and even parts (an odd point can be adjoined to a
-- dissociated set of even points) is taken from the public Problem 963 research notes at
-- erdosproblems.ai/wiki/research/erdos_963/proof_sketch. The odd-set bounds used here
-- (five positive odd integers contain a dissociated four-set, eight contain a dissociated
-- five-set) are proved by a machine-generated case tree (found with the z3 solver); the leaves of
-- the eight-number tree are closed by explicit integer certificates checked by rfl.

/-! Proof outline. A set that is not dissociated carries a nonzero relation with coefficients in
`{-1, 0, 1}` (`Rel`). Write `S d N` for: a positive set all of whose `(d+1)`-subsets carry a
relation has at most `N` elements, and `SO d N` for the same with all elements odd.
Halving all-even sets and splitting into odd and even parts gives `SO (d+1) a → S d b → S (d+1) (a+b)`.
With `SO 1 1`, `SO 2 2`, `SO 3 4`, `SO 4 7` this yields `S 1 1`, `S 2 3`, `S 3 7`, `S 4 14`. -/

namespace OMA.E963H1

def Rel (D : Finset ℤ) (s : ℤ) (nz : Prop) : Prop :=
  ∃ ε : ℤ → ℤ, (∀ z, -1 ≤ ε z ∧ ε z ≤ 1) ∧ (nz ∨ ∃ z ∈ D, ε z ≠ 0) ∧ s + ∑ z ∈ D, ε z * z = 0

lemma rel_of_not_diss {D : Finset ℤ} (h : ¬ AddDissociated (D : Set ℤ)) : Rel D 0 ((0 : ℤ) ≠ 0) := by
  classical
  obtain ⟨t, u, ht, hu, htu, hne, hsum⟩ := not_addDissociated_iff_exists_disjoint.1 h
  rw [Finset.coe_subset] at ht hu
  refine ⟨fun z ↦ (if z ∈ t then 1 else 0) - (if z ∈ u then 1 else 0), ?_, ?_, ?_⟩
  · intro z; dsimp only; split_ifs <;> simp
  · right
    by_contra hcon
    push Not at hcon
    have h1 : t = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun z hz ↦ ?_
      have := hcon z (ht hz)
      simp [hz, Finset.disjoint_left.1 htu hz] at this
    have h2 : u = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun z hz ↦ ?_
      have := hcon z (hu hz)
      simp [hz, Finset.disjoint_right.1 htu hz] at this
    exact hne (h1.trans h2.symm)
  · simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, zero_add]
    rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_eq_right.2 hu,
      Finset.inter_eq_right.2 ht, hsum, sub_self]

lemma rel_insert {D : Finset ℤ} {a s : ℤ} {nz : Prop} (ha : a ∉ D) (h : Rel (insert a D) s nz) :
    ∃ p : ℤ, (p = -1 ∨ p = 0 ∨ p = 1) ∧ Rel D (s + p * a) (nz ∨ p ≠ 0) := by
  obtain ⟨ε, hb, hnz, hsum⟩ := h
  refine ⟨ε a, by have := hb a; omega, ε, hb, ?_, ?_⟩
  · rcases hnz with h | ⟨z, hz, hz0⟩
    · exact Or.inl (Or.inl h)
    · rcases Finset.mem_insert.1 hz with rfl | hz'
      · exact Or.inl (Or.inr hz0)
      · exact Or.inr ⟨z, hz', hz0⟩
  · rw [Finset.sum_insert ha] at hsum; linarith

lemma rel_singleton {a s : ℤ} {nz : Prop} (h : Rel {a} s nz) :
    ∃ p : ℤ, (p = -1 ∨ p = 0 ∨ p = 1) ∧ (nz ∨ p ≠ 0) ∧ s + p * a = 0 := by
  obtain ⟨ε, hb, hnz, hsum⟩ := h
  refine ⟨ε a, by have := hb a; omega, ?_, ?_⟩
  · rcases hnz with h | ⟨z, hz, hz0⟩
    · exact Or.inl h
    · rw [Finset.mem_singleton.1 hz] at hz0; exact Or.inr hz0
  · rwa [Finset.sum_singleton] at hsum

lemma rel_drop_odd {D : Finset ℤ} {o : ℤ} (ho : o % 2 = 1) (hD : ∀ z ∈ D, ¬ z % 2 = 1)
    (hoD : o ∉ D) (h : Rel (insert o D) 0 ((0 : ℤ) ≠ 0)) : Rel D 0 ((0 : ℤ) ≠ 0) := by
  obtain ⟨ε, hb, hnz, hsum⟩ := h
  rw [Finset.sum_insert hoD] at hsum
  have hev : (2 : ℤ) ∣ ∑ z ∈ D, ε z * z :=
    Finset.dvd_sum fun z hz ↦ Dvd.dvd.mul_left (by have := hD z hz; omega) _
  have hb' := hb o
  have h0 : ε o = 0 := by
    rcases (by omega : ε o = -1 ∨ ε o = 0 ∨ ε o = 1) with h | h | h
    · rw [h] at hsum; omega
    · exact h
    · rw [h] at hsum; omega
  refine ⟨ε, hb, ?_, ?_⟩
  · rcases hnz with h | ⟨z, hz, hz0⟩
    · exact absurd rfl h
    · rcases Finset.mem_insert.1 hz with rfl | hz'
      · exact absurd h0 hz0
      · exact Or.inr ⟨z, hz', hz0⟩
  · rw [h0] at hsum; simpa using hsum

lemma rel_halve {D : Finset ℤ} (h : Rel (D.image (fun w ↦ 2 * w)) 0 ((0 : ℤ) ≠ 0)) : Rel D 0 ((0 : ℤ) ≠ 0) := by
  obtain ⟨ε, hb, hnz, hsum⟩ := h
  refine ⟨fun w ↦ ε (2 * w), fun w ↦ hb _, ?_, ?_⟩
  · rcases hnz with h | ⟨z, hz, hz0⟩
    · exact absurd rfl h
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
      exact Or.inr ⟨w, hw, hz0⟩
  · rw [Finset.sum_image (fun x _ y _ h ↦ by have h' : 2 * x = 2 * y := h; omega)] at hsum
    have h2 : ∑ w ∈ D, ε (2 * w) * (2 * w) = 2 * ∑ w ∈ D, ε (2 * w) * w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ ↦ by ring
    rw [h2] at hsum
    show 0 + ∑ w ∈ D, ε (2 * w) * w = 0
    omega

def S (d N : ℕ) : Prop :=
  ∀ P : Finset ℤ, (∀ x ∈ P, 0 < x) → (∀ D ⊆ P, D.card = d + 1 → Rel D 0 ((0 : ℤ) ≠ 0)) → P.card ≤ N

def SO (d N : ℕ) : Prop :=
  ∀ P : Finset ℤ, (∀ x ∈ P, 0 < x) → (∀ x ∈ P, x % 2 = 1) →
    (∀ D ⊆ P, D.card = d + 1 → Rel D 0 ((0 : ℤ) ≠ 0)) → P.card ≤ N

lemma step {d a b : ℕ} (hO : SO (d + 1) a) (hS : S d b) : S (d + 1) (a + b) := by
  have key : ∀ n : ℕ, ∀ P : Finset ℤ, (∀ x ∈ P, 0 < x) → (∀ x ∈ P, x ≤ (n : ℤ)) →
      (∀ D ⊆ P, D.card = d + 1 + 1 → Rel D 0 ((0 : ℤ) ≠ 0)) → P.card ≤ a + b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro P hpos hle hD
    by_cases hodd : ∃ o ∈ P, o % 2 = 1
    · obtain ⟨o, hoP, ho⟩ := hodd
      have h1 : (P.filter (fun x ↦ x % 2 = 1)).card ≤ a := by
        apply hO
        · intro x hx; exact hpos x (Finset.mem_filter.1 hx).1
        · intro x hx; exact (Finset.mem_filter.1 hx).2
        · intro D hDs hc; exact hD D (hDs.trans (Finset.filter_subset _ _)) hc
      have h2 : (P.filter (fun x ↦ ¬ x % 2 = 1)).card ≤ b := by
        apply hS
        · intro x hx; exact hpos x (Finset.mem_filter.1 hx).1
        · intro D hDs hc
          have hoD : o ∉ D := fun h ↦ (Finset.mem_filter.1 (hDs h)).2 ho
          have hr := hD (insert o D)
            (Finset.insert_subset hoP (hDs.trans (Finset.filter_subset _ _)))
            (by rw [Finset.card_insert_of_notMem hoD, hc])
          exact rel_drop_odd ho (fun z hz ↦ (Finset.mem_filter.1 (hDs hz)).2) hoD hr
      have h3 := Finset.card_filter_add_card_filter_not (s := P) (fun x ↦ x % 2 = 1)
      omega
    · push Not at hodd
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hP : P = ∅ := Finset.eq_empty_of_forall_notMem fun x hx ↦ by
          have := hpos x hx; have := hle x hx; omega
        simp [hP]
      · have hinj : Set.InjOn (fun x : ℤ ↦ x / 2) P := by
          intro x hx y hy hxy
          have := hodd x hx; have := hodd y hy
          have h' : x / 2 = y / 2 := hxy
          omega
        rw [← Finset.card_image_of_injOn hinj]
        apply ih (n / 2) (by omega)
        · intro w hw
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
          have := hpos x hx; have := hodd x hx
          show 0 < x / 2
          omega
        · intro w hw
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
          have := hle x hx; have := hpos x hx
          show x / 2 ≤ ((n / 2 : ℕ) : ℤ)
          omega
        · intro D hDs hcD
          have hsub : D.image (fun w ↦ 2 * w) ⊆ P := by
            intro y hy
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (hDs hw)
            have := hodd x hx
            have h' : 2 * (x / 2) = x := by omega
            show 2 * (x / 2) ∈ P
            rw [h']; exact hx
          have hcard : (D.image (fun w : ℤ ↦ 2 * w)).card = d + 1 + 1 := by
            rw [Finset.card_image_of_injective _
              (fun x y h ↦ by have h' : 2 * x = 2 * y := h; omega), hcD]
          exact rel_halve (hD _ hsub hcard)
  intro P hpos hD
  refine key (∑ x ∈ P, x).toNat P hpos (fun x hx ↦ ?_) hD
  have h1 : x ≤ ∑ y ∈ P, y := Finset.single_le_sum (fun y hy ↦ (hpos y hy).le) hx
  have h2 := Int.self_le_toNat (∑ y ∈ P, y)
  omega

lemma exists_sorted {P : Finset ℤ} {k : ℕ} (h : k ≤ P.card) :
    ∃ f : Fin k → ℤ, StrictMono f ∧ ∀ i, f i ∈ P := by
  obtain ⟨Q, hQ, hc⟩ := Finset.exists_subset_card_eq h
  exact ⟨Q.orderEmbOfFin hc, (Q.orderEmbOfFin hc).strictMono,
    fun i ↦ hQ (Q.orderEmbOfFin_mem hc i)⟩

lemma S00 : S 0 0 := by
  intro P hpos hD
  rw [Nat.le_zero, Finset.card_eq_zero]
  refine Finset.eq_empty_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨p, hp, hnz, hs⟩ := rel_singleton (hD {x} (Finset.singleton_subset_iff.2 hx) (by simp))
  have := hpos x hx
  rcases hp with rfl | rfl | rfl <;> omega

lemma SO11 : SO 1 1 := by
  intro P hpos hodd hD
  by_contra hlt
  obtain ⟨f, hm, hf⟩ := exists_sorted (k := 2) (by omega : 2 ≤ P.card)
  have h01 : f 0 < f 1 := hm (by decide)
  have h0 := hpos _ (hf 0)
  have hr := hD {f 0, f 1} (by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> exact hf _) (Finset.card_pair (by omega))
  obtain ⟨p, hp, hr⟩ := rel_insert (by simp only [Finset.mem_singleton]; omega) hr
  obtain ⟨q, hq, hnz, hs⟩ := rel_singleton hr
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> omega

lemma SO22 : SO 2 2 := by
  intro P hpos hodd hD
  by_contra hlt
  obtain ⟨f, hm, hf⟩ := exists_sorted (k := 3) (by omega : 3 ≤ P.card)
  have h01 : f 0 < f 1 := hm (by decide)
  have h12 : f 1 < f 2 := hm (by decide)
  have h0 := hpos _ (hf 0)
  have o0 := hodd _ (hf 0)
  have o1 := hodd _ (hf 1)
  have o2 := hodd _ (hf 2)
  have hr := hD {f 0, f 1, f 2} (by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> exact hf _) (by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_pair (by omega)])
  obtain ⟨p, hp, hr⟩ := rel_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) hr
  obtain ⟨q, hq, hr⟩ := rel_insert (by simp only [Finset.mem_singleton]; omega) hr
  obtain ⟨r, hr', hnz, hs⟩ := rel_singleton hr
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr' with rfl | rfl | rfl <;> omega

def R4 (w x y z : ℤ) : Prop := w + z = x + y ∨ w + x + y = z

def R5 (a b c d e : ℤ) : Prop :=
  R4 b c d e ∨ R4 a c d e ∨ R4 a b d e ∨ R4 a b c e ∨ R4 a b c d

lemma odd4 {w x y z : ℤ} (h0 : 0 < w) (h1 : w < x) (h2 : x < y) (h3 : y < z)
    (ow : w % 2 = 1) (ox : x % 2 = 1) (oy : y % 2 = 1) (oz : z % 2 = 1)
    (h : Rel {w, x, y, z} 0 ((0 : ℤ) ≠ 0)) : R4 w x y z := by
  obtain ⟨p, hp, h⟩ := rel_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) h
  obtain ⟨q, hq, h⟩ := rel_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) h
  obtain ⟨r, hr, h⟩ := rel_insert (by simp only [Finset.mem_singleton]; omega) h
  obtain ⟨t, ht, hnz, hs⟩ := rel_singleton h
  unfold R4
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> omega

set_option maxHeartbeats 4000000 in
lemma odd5 {a b c d e : ℤ} (h0 : 0 < a) (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e)
    (oa : a % 2 = 1) (ob : b % 2 = 1) (oc : c % 2 = 1) (od : d % 2 = 1) (oe : e % 2 = 1)
    (h : Rel {a, b, c, d, e} 0 ((0 : ℤ) ≠ 0)) : R5 a b c d e := by
  obtain ⟨p, hp, h⟩ := rel_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) h
  obtain ⟨q, hq, h⟩ := rel_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) h
  obtain ⟨r, hr, h⟩ := rel_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) h
  obtain ⟨s, hs, h⟩ := rel_insert (by simp only [Finset.mem_singleton]; omega) h
  obtain ⟨t, ht, hnz, hsum⟩ := rel_singleton h
  unfold R5 R4
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl <;>
    omega

lemma card4 {w x y z : ℤ} (h1 : w < x) (h2 : x < y) (h3 : y < z) :
    ({w, x, y, z} : Finset ℤ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.card_pair (by omega)]

lemma card5 {a b c d e : ℤ} (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) :
    ({a, b, c, d, e} : Finset ℤ).card = 5 := by
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    card4 h2 h3 h4]

set_option maxHeartbeats 400000000 in
lemma sub5_1 (f : Fin 5 → ℤ) (_p0 : 0 < f 0) (o0 : f 0 % 2 = 1) (o1 : f 1 % 2 = 1) (o2 : f 2 % 2 = 1) (o3 : f 3 % 2 = 1) (o4 : f 4 % 2 = 1) (_m0 : f 0 < f 1) (m1 : f 1 < f 2) (m2 : f 2 < f 3) (_m3 : f 3 < f 4)
    (H : ∀ i j k l : Fin 5, i < j → j < k → k < l → R4 (f i) (f j) (f k) (f l))
    (c1 : f 0 + f 3 = f 1 + f 2) (c2 : f 0 + f 1 + f 2 = f 4) : False := by
  by_cases c3 : f 0 + f 4 = f 1 + f 3
  ·
    have hS := H 0 2 3 4 (by decide) (by decide) (by decide)
    rcases hS with h|h
    · omega
    · omega
  have hS := H 0 1 3 4 (by decide) (by decide) (by decide)
  rcases hS with h|h
  · exact absurd h c3
  · clear c3; omega

set_option maxHeartbeats 400000000 in
lemma sub5_0 (f : Fin 5 → ℤ) (p0 : 0 < f 0) (o0 : f 0 % 2 = 1) (o1 : f 1 % 2 = 1) (o2 : f 2 % 2 = 1) (o3 : f 3 % 2 = 1) (o4 : f 4 % 2 = 1) (m0 : f 0 < f 1) (m1 : f 1 < f 2) (m2 : f 2 < f 3) (m3 : f 3 < f 4)
    (H : ∀ i j k l : Fin 5, i < j → j < k → k < l → R4 (f i) (f j) (f k) (f l))
    (c1 : f 0 + f 3 = f 1 + f 2) : False := by
  by_cases c2 : f 0 + f 1 + f 2 = f 4
  ·
    exact sub5_1 f p0 o0 o1 o2 o3 o4 m0 m1 m2 m3 H c1 c2
  have hS := H 0 1 2 4 (by decide) (by decide) (by decide)
  rcases hS with h|h
  · clear c2; omega
  · exact absurd h c2

set_option maxHeartbeats 400000000 in
lemma core5 (f : Fin 5 → ℤ) (hpos : ∀ i, 0 < f i) (hodd : ∀ i, f i % 2 = 1) (hm : StrictMono f)
    (H : ∀ i j k l : Fin 5, i < j → j < k → k < l → R4 (f i) (f j) (f k) (f l)) : False := by
  have p0 := hpos 0
  have o0 := hodd 0
  have o1 := hodd 1
  have o2 := hodd 2
  have o3 := hodd 3
  have o4 := hodd 4
  have m0 : f 0 < f 1 := hm (by decide)
  have m1 : f 1 < f 2 := hm (by decide)
  have m2 : f 2 < f 3 := hm (by decide)
  have m3 : f 3 < f 4 := hm (by decide)
  clear hpos hodd hm
  by_cases c1 : f 0 + f 3 = f 1 + f 2
  ·
    exact sub5_0 f p0 o0 o1 o2 o3 o4 m0 m1 m2 m3 H c1
  by_cases c4 : f 0 + f 1 + f 2 = f 3
  ·
    have hS := H 0 1 2 4 (by decide) (by decide) (by decide)
    rcases hS with h|h
    · clear c1; omega
    · clear c1; omega
  have hS := H 0 1 2 3 (by decide) (by decide) (by decide)
  rcases hS with h|h
  · exact absurd h c1
  · exact absurd h c4

/-! Certificate framework for `core8`. Put `y i = (x i - 1) / 2` for the eight odd numbers and
`y 8 = 1`. Every relation used in the case tree is a linear form in `y 0, …, y 8` with integer
coefficients (`cv`), stated as `Q`. A leaf of the tree is closed by an explicit integer combination
of the relations in scope (built with `K`, `P`, `M`, `Z`) that is either positive on the cone `0 ≤ y 0 < y 1 < ⋯ < y 7`
(`posb`) or violates parity (`parb`); both checks are evaluated by `decide`. -/

def dl (i a : ℕ) : ℤ := if i = a then 1 else 0

def cv (t : Bool) (a b c d i : ℕ) : ℤ :=
  bif t then dl i a + dl i b + dl i c + dl i 8 - dl i d else dl i a + dl i d - dl i b - dl i c

def ev (v y : ℕ → ℤ) : ℤ := ∑ i ∈ Finset.range 9, v i * y i

def Q (y : ℕ → ℤ) (t : Bool) (a b c d : ℕ) : Prop := ev (cv t a b c d) y = 0

def N (p : Prop) : Prop := ¬ p

lemma em (p : Prop) : p ∨ N p := Classical.em p

lemma ev_lin (k : ℤ) (u w y : ℕ → ℤ) : ev (fun i ↦ k * u i + w i) y = k * ev u y + ev w y := by
  simp only [ev, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma Z {y : ℕ → ℤ} : ev (fun _ ↦ 0) y = 0 := by simp [ev]

lemma K (k : ℤ) {y : ℕ → ℤ} {t : Bool} {a b c d : ℕ} {w : ℕ → ℤ} (h1 : Q y t a b c d)
    (h2 : ev w y = 0) : ev (fun i ↦ k * cv t a b c d i + w i) y = 0 := by
  have h1' : ev (cv t a b c d) y = 0 := h1
  rw [ev_lin, h1', h2]; simp

lemma P {y : ℕ → ℤ} {t : Bool} {a b c d : ℕ} {w : ℕ → ℤ} (h1 : Q y t a b c d)
    (h2 : ev w y = 0) : ev (fun i ↦ 1 * cv t a b c d i + w i) y = 0 := K 1 h1 h2

lemma M {y : ℕ → ℤ} {t : Bool} {a b c d : ℕ} {w : ℕ → ℤ} (h1 : Q y t a b c d)
    (h2 : ev w y = 0) : ev (fun i ↦ -1 * cv t a b c d i + w i) y = 0 := K (-1) h1 h2

structure Bs (y : ℕ → ℤ) : Prop where
  h8 : y 8 = 1
  h0 : 0 ≤ y 0
  m0 : y 0 < y 1
  m1 : y 1 < y 2
  m2 : y 2 < y 3
  m3 : y 3 < y 4
  m4 : y 4 < y 5
  m5 : y 5 < y 6
  m6 : y 6 < y 7

lemma ev_exp (v y : ℕ → ℤ) : ev v y = v 0 * y 0 + v 1 * y 1 + v 2 * y 2 + v 3 * y 3 + v 4 * y 4 +
    v 5 * y 5 + v 6 * y 6 + v 7 * y 7 + v 8 * y 8 := by
  simp only [ev, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

def posb (v : ℕ → ℤ) : Bool :=
  decide (0 ≤ v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7) &&
  decide (0 ≤ v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7) &&
  decide (0 ≤ v 2 + v 3 + v 4 + v 5 + v 6 + v 7) &&
  decide (0 ≤ v 3 + v 4 + v 5 + v 6 + v 7) &&
  decide (0 ≤ v 4 + v 5 + v 6 + v 7) &&
  decide (0 ≤ v 5 + v 6 + v 7) &&
  decide (0 ≤ v 6 + v 7) &&
  decide (0 ≤ v 7) &&
  decide (0 < v 8 + v 1 + 2 * v 2 + 3 * v 3 + 4 * v 4 + 5 * v 5 + 6 * v 6 + 7 * v 7)

lemma pos_sound {y : ℕ → ℤ} (B : Bs y) {v : ℕ → ℤ} (h : posb v = true) : 0 < ev v y := by
  simp only [posb, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b0, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, hc⟩ := h
  rw [ev_exp, B.h8]
  have g1 : 0 ≤ y 1 - y 0 - 1 := by have := B.m0; omega
  have g2 : 0 ≤ y 2 - y 1 - 1 := by have := B.m1; omega
  have g3 : 0 ≤ y 3 - y 2 - 1 := by have := B.m2; omega
  have g4 : 0 ≤ y 4 - y 3 - 1 := by have := B.m3; omega
  have g5 : 0 ≤ y 5 - y 4 - 1 := by have := B.m4; omega
  have g6 : 0 ≤ y 6 - y 5 - 1 := by have := B.m5; omega
  have g7 : 0 ≤ y 7 - y 6 - 1 := by have := B.m6; omega
  nlinarith [mul_nonneg b0 B.h0, mul_nonneg b1 g1, mul_nonneg b2 g2, mul_nonneg b3 g3,
    mul_nonneg b4 g4, mul_nonneg b5 g5, mul_nonneg b6 g6, mul_nonneg b7 g7]

def parb (v : ℕ → ℤ) : Bool :=
  decide (v 0 % 2 = 0) && decide (v 1 % 2 = 0) && decide (v 2 % 2 = 0) && decide (v 3 % 2 = 0) &&
  decide (v 4 % 2 = 0) && decide (v 5 % 2 = 0) && decide (v 6 % 2 = 0) && decide (v 7 % 2 = 0) &&
  decide (v 8 % 2 = 1)

lemma par_sound {y : ℕ → ℤ} (B : Bs y) {v : ℕ → ℤ} (h : parb v = true) : ev v y ≠ 0 := by
  simp only [parb, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b0, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, hc⟩ := h
  rw [ev_exp, B.h8]
  have d0 : (2 : ℤ) ∣ v 0 * y 0 := Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero b0) _
  have d1 : (2 : ℤ) ∣ v 1 * y 1 := Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero b1) _
  have d2 : (2 : ℤ) ∣ v 2 * y 2 := Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero b2) _
  have d3 : (2 : ℤ) ∣ v 3 * y 3 := Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero b3) _
  have d4 : (2 : ℤ) ∣ v 4 * y 4 := Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero b4) _
  have d5 : (2 : ℤ) ∣ v 5 * y 5 := Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero b5) _
  have d6 : (2 : ℤ) ∣ v 6 * y 6 := Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero b6) _
  have d7 : (2 : ℤ) ∣ v 7 * y 7 := Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero b7) _
  omega

lemma L {y : ℕ → ℤ} (B : Bs y) {v : ℕ → ℤ} (h : ev v y = 0) (ok : posb v = true) : False := by
  have := pos_sound B ok
  rw [h] at this
  exact lt_irrefl _ this

lemma G {y : ℕ → ℤ} (B : Bs y) {v : ℕ → ℤ} (h : ev v y = 0) (ok : parb v = true) : False :=
  par_sound B ok h

lemma LN {y : ℕ → ℤ} (B : Bs y) (m1 m2 : ℕ) {t : Bool} {a b c d : ℕ} (hn : N (Q y t a b c d))
    {v1 v2 : ℕ → ℤ} (e1 : ev v1 y = 0) (e2 : ev v2 y = 0)
    (ok1 : posb (fun i ↦ v1 i - m1 * (cv t a b c d i - dl i 8)) = true)
    (ok2 : posb (fun i ↦ v2 i + m2 * (cv t a b c d i + dl i 8)) = true) : False := by
  have p1 := pos_sound B ok1
  have p2 := pos_sound B ok2
  have hD : ev (cv t a b c d) y ≠ 0 := hn
  rw [ev_exp] at p1 p2 e1 e2 hD
  have k8 : dl 8 8 = 1 := by decide
  have k0 : dl 0 8 = 0 := by decide
  have k1 : dl 1 8 = 0 := by decide
  have k2 : dl 2 8 = 0 := by decide
  have k3 : dl 3 8 = 0 := by decide
  have k4 : dl 4 8 = 0 := by decide
  have k5 : dl 5 8 = 0 := by decide
  have k6 : dl 6 8 = 0 := by decide
  have k7 : dl 7 8 = 0 := by decide
  simp only [k0, k1, k2, k3, k4, k5, k6, k7, k8, B.h8] at p1 p2 e1 e2 hD
  have hm1 : (0 : ℤ) ≤ m1 := Int.natCast_nonneg _
  have hm2 : (0 : ℤ) ≤ m2 := Int.natCast_nonneg _
  rcases lt_or_gt_of_ne hD with hlt | hgt
  · nlinarith [mul_nonneg hm2 (by omega : (0 : ℤ) ≤ -(cv t a b c d 0 * y 0 + cv t a b c d 1 * y 1 + cv t a b c d 2 * y 2 + cv t a b c d 3 * y 3 + cv t a b c d 4 * y 4 + cv t a b c d 5 * y 5 + cv t a b c d 6 * y 6 + cv t a b c d 7 * y 7 + cv t a b c d 8 * 1) - 1)]
  · nlinarith [mul_nonneg hm1 (by omega : (0 : ℤ) ≤ (cv t a b c d 0 * y 0 + cv t a b c d 1 * y 1 + cv t a b c d 2 * y 2 + cv t a b c d 3 * y 3 + cv t a b c d 4 * y 4 + cv t a b c d 5 * y 5 + cv t a b c d 6 * y 6 + cv t a b c d 7 * y 7 + cv t a b c d 8 * 1) - 1)]

lemma Q0 {y : ℕ → ℤ} {a b c d : ℕ} (ha : a < 9) (hb : b < 9) (hc : c < 9) (hd : d < 9)
    (h : y a + y d = y b + y c) : Q y false a b c d := by
  unfold Q ev
  simp only [cv, dl, cond_false, sub_mul, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_range,
    if_pos ha, if_pos hb, if_pos hc, if_pos hd]
  omega

lemma Q1 {y : ℕ → ℤ} {a b c d : ℕ} (ha : a < 9) (hb : b < 9) (hc : c < 9) (hd : d < 9)
    (h8 : y 8 = 1) (h : y a + y b + y c + 1 = y d) : Q y true a b c d := by
  unfold Q ev
  simp only [cv, dl, cond_true, sub_mul, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_range,
    if_pos ha, if_pos hb, if_pos hc, if_pos hd, if_pos (by decide : 8 < 9)]
  omega

def R4y (y : ℕ → ℤ) (a b c d : ℕ) : Prop := Q y false a b c d ∨ Q y true a b c d

def R5y (y : ℕ → ℤ) (a b c d e : ℕ) : Prop :=
  R4y y b c d e ∨ R4y y a c d e ∨ R4y y a b d e ∨ R4y y a b c e ∨ R4y y a b c d

lemma r4c {y : ℕ → ℤ} {w x z u : ℤ} {a b c d : ℕ} (ha : a < 8) (hb : b < 8) (hc : c < 8)
    (hd : d < 8) (h8 : y 8 = 1) (ea : y a = w / 2) (eb : y b = x / 2) (ec : y c = z / 2)
    (ed : y d = u / 2) (ow : w % 2 = 1) (ox : x % 2 = 1) (oz : z % 2 = 1) (ou : u % 2 = 1)
    (h : R4 w x z u) : R4y y a b c d := by
  unfold R4 at h
  rcases h with h | h
  · exact Or.inl (Q0 (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact Or.inr (Q1 (by omega) (by omega) (by omega) (by omega) h8 (by omega))

structure AH (y : ℕ → ℤ) : Prop where
  h01234 : R5y y 0 1 2 3 4
  h01235 : R5y y 0 1 2 3 5
  h01236 : R5y y 0 1 2 3 6
  h01237 : R5y y 0 1 2 3 7
  h01245 : R5y y 0 1 2 4 5
  h01246 : R5y y 0 1 2 4 6
  h01247 : R5y y 0 1 2 4 7
  h01256 : R5y y 0 1 2 5 6
  h01257 : R5y y 0 1 2 5 7
  h01267 : R5y y 0 1 2 6 7
  h01345 : R5y y 0 1 3 4 5
  h01346 : R5y y 0 1 3 4 6
  h01347 : R5y y 0 1 3 4 7
  h01356 : R5y y 0 1 3 5 6
  h01357 : R5y y 0 1 3 5 7
  h01367 : R5y y 0 1 3 6 7
  h01456 : R5y y 0 1 4 5 6
  h01457 : R5y y 0 1 4 5 7
  h01467 : R5y y 0 1 4 6 7
  h01567 : R5y y 0 1 5 6 7
  h02345 : R5y y 0 2 3 4 5
  h02346 : R5y y 0 2 3 4 6
  h02347 : R5y y 0 2 3 4 7
  h02356 : R5y y 0 2 3 5 6
  h02357 : R5y y 0 2 3 5 7
  h02367 : R5y y 0 2 3 6 7
  h02456 : R5y y 0 2 4 5 6
  h02457 : R5y y 0 2 4 5 7
  h02467 : R5y y 0 2 4 6 7
  h02567 : R5y y 0 2 5 6 7
  h03456 : R5y y 0 3 4 5 6
  h03457 : R5y y 0 3 4 5 7
  h03467 : R5y y 0 3 4 6 7
  h03567 : R5y y 0 3 5 6 7
  h04567 : R5y y 0 4 5 6 7
  h12345 : R5y y 1 2 3 4 5
  h12346 : R5y y 1 2 3 4 6
  h12347 : R5y y 1 2 3 4 7
  h12356 : R5y y 1 2 3 5 6
  h12357 : R5y y 1 2 3 5 7
  h12367 : R5y y 1 2 3 6 7
  h12456 : R5y y 1 2 4 5 6
  h12457 : R5y y 1 2 4 5 7
  h12467 : R5y y 1 2 4 6 7
  h12567 : R5y y 1 2 5 6 7
  h13456 : R5y y 1 3 4 5 6
  h13457 : R5y y 1 3 4 5 7
  h13467 : R5y y 1 3 4 6 7
  h13567 : R5y y 1 3 5 6 7
  h14567 : R5y y 1 4 5 6 7
  h23456 : R5y y 2 3 4 5 6
  h23457 : R5y y 2 3 4 5 7
  h23467 : R5y y 2 3 4 6 7
  h23567 : R5y y 2 3 5 6 7
  h24567 : R5y y 2 4 5 6 7
  h34567 : R5y y 3 4 5 6 7

set_option maxHeartbeats 4000000 in
lemma s238 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c631 : Q y true 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (_c516 : N (Q y false 0 1 3 4)) (_c575 : N (Q y true 0 1 3 4)) (_c584 : N (Q y false 0 2 3 4)) (_c600 : N (Q y true 0 2 3 4)) (_c603 : N (Q y false 0 1 2 5)) (_c605 : N (Q y true 0 1 2 5)) (_c614 : N (Q y false 0 1 3 5)) (_c615 : N (Q y true 0 1 3 5)) (_c622 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 1 2 3 6) with c632 | c632
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c602 (P h Z)) rfl
  · exact L B (P c632 (M h Z)) rfl
  · exact L B (P c632 (P h Z)) rfl
  · exact L B (P c631 (M h Z)) rfl
  · exact L B (P c631 (P h Z)) rfl
  · exact L B (P c631 (M h Z)) rfl
  · exact L B (P c632 (K 2 h Z)) rfl
  · exact L B (P c631 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c602 (P h Z)) rfl
 · exact absurd h c632
 · exact L B (P c631 (P h Z)) rfl
 · exact L B (P c631 (M h Z)) rfl
 · exact L B (P c631 (P h Z)) rfl
 · exact L B (P c631 (M h Z)) rfl
 · exact L B (P c631 (P h Z)) rfl
 · exact L B (P c631 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s237 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (_c622 : Q y false 0 2 3 5) (c623 : Q y false 0 1 4 5) (c628 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (_c584 : N (Q y false 0 2 3 4)) (_c600 : N (Q y true 0 2 3 4)) (_c603 : N (Q y false 0 1 2 5)) (_c605 : N (Q y true 0 1 2 5)) (_c614 : N (Q y false 0 1 3 5)) (c615 : N (Q y true 0 1 3 5)) (_c624 : N (Q y true 0 1 2 6)) (_c626 : N (Q y true 0 1 3 6)) : False := by
 rcases em (Q y true 1 2 3 7) with c629 | c629
 ·
  rcases H.h02467 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c411 (P c628 (M c629 (M h Z))) (M c628 (P c629 (P h Z))) rfl rfl
  · exact L B (M c629 (P h Z)) rfl
  · exact L B (P c628 (M c629 (M h Z))) rfl
  · exact L B (M c623 (M c629 (P h Z))) rfl
  · exact L B (P c628 (M c629 (M h Z))) rfl
  · exact L B (M c623 (M c629 (P h Z))) rfl
  · exact LN B 1 1 c575 (P c629 (P h Z)) (M c629 (M h Z)) rfl rfl
  · exact LN B 1 1 c516 (M c629 (P h Z)) (P c629 (M h Z)) rfl rfl
  · exact LN B 1 1 c615 (M c623 (P c628 (P h Z))) (P c623 (M c628 (M h Z))) rfl rfl
  · exact L B (M c628 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c602 (P h Z)) rfl
 · exact absurd h c629
 · exact L B (M c602 (M c623 (P h Z))) rfl
 · exact L B (P c628 (M h Z)) rfl
 · exact L B (M c623 (P h Z)) rfl
 · exact L B (P c628 (M h Z)) rfl
 · exact L B (M c623 (P h Z)) rfl
 · exact L B (P c628 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s236 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (_c622 : Q y false 0 2 3 5) (c623 : Q y false 0 1 4 5) (c626 : Q y true 0 1 3 6) (_c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (_c516 : N (Q y false 0 1 3 4)) (_c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (_c603 : N (Q y false 0 1 2 5)) (_c605 : N (Q y true 0 1 2 5)) (_c614 : N (Q y false 0 1 3 5)) (_c615 : N (Q y true 0 1 3 5)) (c624 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 1 2 4 6) with c627 | c627
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c486 (P c626 (P h Z)) (M c626 (M h Z)) rfl rfl
  · exact L B (K 2 c627 (P h Z)) rfl
  · exact L B (P c627 (M h Z)) rfl
  · exact L B (P c627 (P h Z)) rfl
  · exact L B (P c627 (M h Z)) rfl
  · exact L B (P c627 (P h Z)) rfl
  · exact L B (M c602 (M c623 (P h Z))) rfl
  · exact L B (M c626 (P h Z)) rfl
  · exact absurd h c584
  · exact absurd h c600
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c627
 · exact L B (M c626 (P h Z)) rfl
 · exact G B (P c602 (P c626 (P h Z))) rfl
 · exact L B (M c626 (P h Z)) rfl
 · exact L B (M c623 (P h Z)) rfl
 · exact L B (M c626 (P h Z)) rfl
 · exact L B (M c623 (P h Z)) rfl
 · exact absurd h c624
 · exact absurd h c411
 · exact absurd h c486

set_option maxHeartbeats 4000000 in
lemma s235 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (_c622 : Q y false 0 2 3 5) (c623 : Q y false 0 1 4 5) (c624 : Q y true 0 1 2 6) (c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (_c603 : N (Q y false 0 1 2 5)) (_c605 : N (Q y true 0 1 2 5)) (_c614 : N (Q y false 0 1 3 5)) (_c615 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y false 1 3 4 6) with c625 | c625
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c625 (P h Z)) rfl
  · exact L B (M c624 (P h Z)) rfl
  · exact L B (P c625 (M h Z)) rfl
  · exact L B (M c624 (P h Z)) rfl
  · exact LN B 1 1 c1 (M c625 (P h Z)) (P c625 (M h Z)) rfl rfl
  · exact L B (M c624 (P h Z)) rfl
  · exact L B (M c602 (M c623 (P h Z))) rfl
  · exact L B (M c624 (P h Z)) rfl
  · exact absurd h c584
  · exact absurd h c600
 rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c625
 · exact L B (M c624 (P h Z)) rfl
 · exact G B (P c602 (P c624 (P h Z))) rfl
 · exact L B (M c624 (P h Z)) rfl
 · exact L B (M c623 (P h Z)) rfl
 · exact L B (M c624 (P h Z)) rfl
 · exact L B (M c623 (P h Z)) rfl
 · exact L B (M c624 (P h Z)) rfl
 · exact absurd h c516
 · exact absurd h c575

set_option maxHeartbeats 4000000 in
lemma s234 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c622 : Q y false 0 2 3 5) (c623 : Q y false 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (c603 : N (Q y false 0 1 2 5)) (c605 : N (Q y true 0 1 2 5)) (c614 : N (Q y false 0 1 3 5)) (c615 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y true 0 1 2 6) with c624 | c624
 ·
  exact s235 y B H c602 c622 c623 c624 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614 c615
 rcases em (Q y true 0 1 3 6) with c626 | c626
 ·
  exact s236 y B H c602 c622 c623 c626 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614 c615 c624
 rcases em (Q y true 0 2 3 6) with c628 | c628
 ·
  exact s237 y B H c602 c622 c623 c628 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614 c615 c624 c626
 rcases em (Q y true 1 2 3 6) with c630 | c630
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c602 (P h Z)) rfl
  · exact L B (P c630 (M h Z)) rfl
  · exact L B (M c602 (M c623 (P h Z))) rfl
  · exact L B (P c630 (M h Z)) rfl
  · exact L B (M c623 (P h Z)) rfl
  · exact L B (P c630 (M h Z)) rfl
  · exact L B (M c623 (P h Z)) rfl
  · exact L B (P c630 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c602 (P h Z)) rfl
 · exact absurd h c630
 · exact L B (M c602 (M c623 (P h Z))) rfl
 · exact absurd h c628
 · exact L B (M c623 (P h Z)) rfl
 · exact absurd h c626
 · exact L B (M c623 (P h Z)) rfl
 · exact absurd h c624
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s233 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c622 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (c603 : N (Q y false 0 1 2 5)) (c605 : N (Q y true 0 1 2 5)) (c614 : N (Q y false 0 1 3 5)) (c615 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y false 0 1 4 5) with c623 | c623
 ·
  exact s234 y B H c602 c622 c623 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614 c615
 rcases H.h01245 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c623 (M c602 (P c622 Z)) (P c602 (M c622 Z)) rfl rfl
 · exact L B (P c622 (P h Z)) rfl
 · exact L B (P c622 (M h Z)) rfl
 · exact L B (P c622 (P h Z)) rfl
 · exact absurd h c623
 · exact L B (M c602 (P c622 (P h Z))) rfl
 · exact absurd h c603
 · exact absurd h c605
 · exact absurd h c411
 · exact absurd h c486

set_option maxHeartbeats 4000000 in
lemma s232 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c615 : Q y true 0 1 3 5) (c616 : Q y false 0 1 4 5) (_c617 : Q y false 0 2 3 5) (c618 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (_c575 : N (Q y true 0 1 3 4)) (_c584 : N (Q y false 0 2 3 4)) (_c600 : N (Q y true 0 2 3 4)) (_c603 : N (Q y false 0 1 2 5)) (_c605 : N (Q y true 0 1 2 5)) (_c614 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y true 1 2 3 7) with c619 | c619
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c615 (P c618 (P h Z))) rfl
  · exact L B (M c619 (P h Z)) rfl
  · exact L B (M c615 (M c616 (P c618 (P h Z)))) rfl
  · exact LN B 1 1 c516 (M c619 (P h Z)) (P c619 (M h Z)) rfl rfl
  · exact L B (M c616 (P h Z)) rfl
  · exact L B (P c602 (P c618 (M h Z))) rfl
  · exact L B (M c616 (P h Z)) rfl
  · exact L B (P c615 (M h Z)) rfl
  · exact absurd h c411
  · exact absurd h c486
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c602 (P h Z)) rfl
 · exact absurd h c619
 · exact L B (M c602 (M c616 (P h Z))) rfl
 · exact L B (P c618 (M h Z)) rfl
 · exact L B (M c616 (P h Z)) rfl
 · exact L B (P c615 (M h Z)) rfl
 · exact L B (M c616 (P h Z)) rfl
 · exact L B (P c615 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s231 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c615 : Q y true 0 1 3 5) (c616 : Q y false 0 1 4 5) (c617 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (c603 : N (Q y false 0 1 2 5)) (c605 : N (Q y true 0 1 2 5)) (c614 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y true 0 2 3 6) with c618 | c618
 ·
  exact s232 y B H c602 c615 c616 c617 c618 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614
 rcases em (Q y true 1 2 3 6) with c620 | c620
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c602 (P h Z)) rfl
  · exact L B (P c620 (M h Z)) rfl
  · exact L B (M c602 (M c616 (P h Z))) rfl
  · exact L B (P c620 (M h Z)) rfl
  · exact L B (M c616 (P h Z)) rfl
  · exact L B (P c615 (M h Z)) rfl
  · exact L B (M c616 (P h Z)) rfl
  · exact L B (P c615 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c602 (P h Z)) rfl
 · exact absurd h c620
 · exact L B (M c602 (M c616 (P h Z))) rfl
 · exact absurd h c618
 · exact L B (M c616 (P h Z)) rfl
 · exact L B (P c615 (M h Z)) rfl
 · exact L B (M c616 (P h Z)) rfl
 · exact L B (P c615 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s230 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c615 : Q y true 0 1 3 5) (c616 : Q y false 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (c603 : N (Q y false 0 1 2 5)) (c605 : N (Q y true 0 1 2 5)) (c614 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c617 | c617
 ·
  exact s231 y B H c602 c615 c616 c617 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c617 (P c602 (P c616 Z)) (M c602 (M c616 Z)) rfl rfl
 · exact L B (P c616 (P h Z)) rfl
 · exact L B (P c616 (M h Z)) rfl
 · exact L B (P c616 (P h Z)) rfl
 · exact L B (P c616 (M h Z)) rfl
 · exact L B (P c616 (P h Z)) rfl
 · exact absurd h c617
 · exact L B (P c602 (P c616 (P h Z))) rfl
 · exact absurd h c584
 · exact absurd h c600

set_option maxHeartbeats 4000000 in
lemma s229 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c615 : Q y true 0 1 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (c603 : N (Q y false 0 1 2 5)) (c605 : N (Q y true 0 1 2 5)) (c614 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 0 1 4 5) with c616 | c616
 ·
  exact s230 y B H c602 c615 c616 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614
 rcases em (Q y false 1 2 4 5) with c621 | c621
 ·
  rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c486 (P c615 (P h Z)) (M c615 (M h Z)) rfl rfl
  · exact L B (P c621 (P h Z)) rfl
  · exact L B (P c621 (M h Z)) rfl
  · exact L B (P c621 (P h Z)) rfl
  · exact L B (P c621 (M h Z)) rfl
  · exact L B (P c621 (P h Z)) rfl
  · exact LN B 1 1 c616 (M c602 (P h Z)) (P c602 (M h Z)) rfl rfl
  · exact L B (M c615 (P h Z)) rfl
  · exact absurd h c584
  · exact absurd h c600
 rcases H.h01245 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c621
 · exact L B (M c615 (P h Z)) rfl
 · exact G B (P c602 (P c615 (P h Z))) rfl
 · exact L B (M c615 (P h Z)) rfl
 · exact absurd h c616
 · exact L B (M c615 (P h Z)) rfl
 · exact absurd h c603
 · exact absurd h c605
 · exact absurd h c411
 · exact absurd h c486

set_option maxHeartbeats 4000000 in
lemma s228 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c605 : Q y true 0 1 2 5) (c607 : Q y false 0 1 4 5) (_c608 : Q y false 0 2 3 5) (c610 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (_c575 : N (Q y true 0 1 3 4)) (_c584 : N (Q y false 0 2 3 4)) (_c600 : N (Q y true 0 2 3 4)) (_c603 : N (Q y false 0 1 2 5)) (_c606 : N (Q y false 0 1 3 5)) (_c609 : N (Q y true 0 1 3 6)) : False := by
 rcases em (Q y true 1 2 3 7) with c611 | c611
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c605 (P c610 (P h Z))) rfl
  · exact L B (M c611 (P h Z)) rfl
  · exact L B (M c605 (M c607 (P c610 (P h Z)))) rfl
  · exact LN B 1 1 c516 (M c611 (P h Z)) (P c611 (M h Z)) rfl rfl
  · exact L B (M c607 (P h Z)) rfl
  · exact L B (P c602 (P c610 (M h Z))) rfl
  · exact L B (P c610 (P h Z)) rfl
  · exact L B (P c610 (M h Z)) rfl
  · exact absurd h c411
  · exact absurd h c486
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c610 (P h Z)) rfl
 · exact absurd h c611
 · exact L B (P c610 (P h Z)) rfl
 · exact L B (P c610 (M h Z)) rfl
 · exact L B (M c607 (P h Z)) rfl
 · exact L B (P c610 (M h Z)) rfl
 · exact L B (P c610 (P h Z)) rfl
 · exact L B (P c610 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s227 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c605 : Q y true 0 1 2 5) (c607 : Q y false 0 1 4 5) (c608 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (c603 : N (Q y false 0 1 2 5)) (c606 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y true 0 1 3 6) with c609 | c609
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c605 (P c609 (P h Z))) rfl
  · exact L B (M c609 (P h Z)) rfl
  · exact L B (P c605 (P c607 (M c609 (M h Z)))) rfl
  · exact L B (M c609 (P h Z)) rfl
  · exact G B (P c602 (P c609 (P h Z))) rfl
  · exact L B (M c609 (P h Z)) rfl
  · exact L B (M c602 (M c607 (P h Z))) rfl
  · exact L B (M c609 (P h Z)) rfl
  · exact absurd h c584
  · exact absurd h c600
 rcases em (Q y true 0 2 3 6) with c610 | c610
 ·
  exact s228 y B H c602 c605 c607 c608 c610 c1 c320 c411 c486 c516 c575 c584 c600 c603 c606 c609
 rcases em (Q y true 1 2 3 6) with c612 | c612
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c612 (P h Z)) rfl
  · exact L B (P c612 (M h Z)) rfl
  · exact L B (M c602 (M c607 (P h Z))) rfl
  · exact L B (P c612 (M h Z)) rfl
  · exact L B (M c607 (P h Z)) rfl
  · exact L B (P c612 (M h Z)) rfl
  · exact L B (M c607 (P h Z)) rfl
  · exact L B (P c605 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c602 (P h Z)) rfl
 · exact absurd h c612
 · exact L B (M c602 (M c607 (P h Z))) rfl
 · exact absurd h c610
 · exact L B (M c607 (P h Z)) rfl
 · exact absurd h c609
 · exact L B (M c607 (P h Z)) rfl
 · exact L B (P c605 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s226 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c605 : Q y true 0 1 2 5) (c607 : Q y false 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (c603 : N (Q y false 0 1 2 5)) (c606 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c608 | c608
 ·
  exact s227 y B H c602 c605 c607 c608 c1 c320 c411 c486 c516 c575 c584 c600 c603 c606
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c608 (P c602 (P c607 Z)) (M c602 (M c607 Z)) rfl rfl
 · exact L B (M c605 (P h Z)) rfl
 · exact L B (P c607 (M h Z)) rfl
 · exact L B (P c607 (P h Z)) rfl
 · exact L B (P c607 (M h Z)) rfl
 · exact L B (P c607 (P h Z)) rfl
 · exact absurd h c608
 · exact L B (M c605 (P h Z)) rfl
 · exact absurd h c584
 · exact absurd h c600

set_option maxHeartbeats 4000000 in
lemma s225 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c602 : Q y false 1 2 3 4) (c605 : Q y true 0 1 2 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) (c603 : N (Q y false 0 1 2 5)) : False := by
 rcases em (Q y false 0 1 3 5) with c606 | c606
 ·
  rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c411 (P c606 (M h Z)) (M c606 (P h Z)) rfl rfl
  · exact L B (K 2 c606 (P h Z)) rfl
  · exact L B (P c606 (M h Z)) rfl
  · exact L B (P c606 (P h Z)) rfl
  · exact L B (P c606 (M h Z)) rfl
  · exact L B (P c606 (P h Z)) rfl
  · exact L B (P c606 (M h Z)) rfl
  · exact L B (P c606 (P h Z)) rfl
  · exact absurd h c584
  · exact absurd h c600
 rcases em (Q y false 0 1 4 5) with c607 | c607
 ·
  exact s226 y B H c602 c605 c607 c1 c320 c411 c486 c516 c575 c584 c600 c603 c606
 rcases em (Q y false 1 3 4 5) with c613 | c613
 ·
  rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c613 (P h Z)) rfl
  · exact L B (M c605 (P h Z)) rfl
  · exact L B (P c613 (M h Z)) rfl
  · exact L B (M c605 (P h Z)) rfl
  · exact LN B 1 1 c1 (M c613 (P h Z)) (P c613 (M h Z)) rfl rfl
  · exact L B (M c605 (P h Z)) rfl
  · exact LN B 1 1 c607 (M c602 (P h Z)) (P c602 (M h Z)) rfl rfl
  · exact L B (M c605 (P h Z)) rfl
  · exact absurd h c584
  · exact absurd h c600
 rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c613
 · exact L B (M c605 (P h Z)) rfl
 · exact G B (P c602 (P c605 (P h Z))) rfl
 · exact L B (M c605 (P h Z)) rfl
 · exact absurd h c607
 · exact L B (M c605 (P h Z)) rfl
 · exact absurd h c606
 · exact L B (M c605 (P h Z)) rfl
 · exact absurd h c516
 · exact absurd h c575

set_option maxHeartbeats 4000000 in
lemma s224 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (_c602 : Q y false 1 2 3 4) (c603 : Q y false 0 1 2 5) (_c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c584 : N (Q y false 0 2 3 4)) (c600 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y false 1 3 4 5) with c604 | c604
 ·
  rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c604 (P h Z)) rfl
  · exact L B (P c604 (P h Z)) rfl
  · exact L B (P c604 (M h Z)) rfl
  · exact L B (P c604 (P h Z)) rfl
  · exact L B (P c603 (M h Z)) rfl
  · exact L B (P c603 (P h Z)) rfl
  · exact L B (P c603 (M h Z)) rfl
  · exact L B (P c603 (P h Z)) rfl
  · exact absurd h c584
  · exact absurd h c600
 rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c604
 · exact L B (K 2 c603 (P h Z)) rfl
 · exact L B (P c603 (M h Z)) rfl
 · exact L B (P c603 (P h Z)) rfl
 · exact L B (P c603 (M h Z)) rfl
 · exact L B (P c603 (P h Z)) rfl
 · exact L B (P c603 (M h Z)) rfl
 · exact L B (P c603 (P h Z)) rfl
 · exact absurd h c516
 · exact absurd h c575

set_option maxHeartbeats 4000000 in
lemma s223 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c600 : Q y true 0 2 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (_c516 : N (Q y false 0 1 3 4)) (_c575 : N (Q y true 0 1 3 4)) (_c584 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y true 1 2 3 5) with c601 | c601
 ·
  rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c601 (P h Z)) rfl
  · exact L B (P c601 (M h Z)) rfl
  · exact L B (P c601 (P h Z)) rfl
  · exact L B (P c600 (M h Z)) rfl
  · exact L B (P c601 (K 2 h Z)) rfl
  · exact L B (P c600 (M h Z)) rfl
  · exact L B (P c601 (K 2 h Z)) rfl
  · exact L B (P c601 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01235 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c600 (P h Z)) rfl
 · exact absurd h c601
 · exact L B (P c600 (P h Z)) rfl
 · exact L B (P c600 (M h Z)) rfl
 · exact L B (P c600 (P h Z)) rfl
 · exact L B (P c600 (M h Z)) rfl
 · exact L B (P c600 (P h Z)) rfl
 · exact L B (P c600 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s222 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c584 : Q y false 0 2 3 4) (c597 : Q y true 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (_c516 : N (Q y false 0 1 3 4)) (_c575 : N (Q y true 0 1 3 4)) (_c585 : N (Q y true 0 1 2 5)) (_c592 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y true 1 2 3 6) with c598 | c598
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c584 (P h Z)) rfl
  · exact L B (P c598 (M h Z)) rfl
  · exact L B (M c584 (P h Z)) rfl
  · exact L B (P c597 (M h Z)) rfl
  · exact L B (M c584 (P h Z)) rfl
  · exact L B (P c597 (M h Z)) rfl
  · exact L B (M c584 (P h Z)) rfl
  · exact L B (P c597 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c597 (P h Z)) rfl
 · exact absurd h c598
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (P c597 (M h Z)) rfl
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (P c597 (M h Z)) rfl
 · exact L B (P c597 (P h Z)) rfl
 · exact L B (P c597 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s221 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c584 : Q y false 0 2 3 4) (c592 : Q y true 0 1 3 5) (c593 : Q y false 1 3 4 5) (c594 : Q y false 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (_c585 : N (Q y true 0 1 2 5)) : False := by
 rcases em (Q y true 0 2 3 6) with c595 | c595
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c593 (P h Z)) rfl
  · exact L B (M c595 (P h Z)) rfl
  · exact L B (P c592 (P c594 (M c595 (M h Z)))) rfl
  · exact L B (M c595 (P h Z)) rfl
  · exact L B (M c594 (P h Z)) rfl
  · exact L B (M c584 (M c595 (P h Z))) rfl
  · exact L B (M c584 (P h Z)) rfl
  · exact L B (P c592 (M h Z)) rfl
  · exact absurd h c516
  · exact absurd h c575
 rcases em (Q y true 1 2 3 6) with c596 | c596
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c596 (P h Z)) rfl
  · exact L B (P c596 (M h Z)) rfl
  · exact L B (P c596 (P h Z)) rfl
  · exact L B (P c596 (M h Z)) rfl
  · exact L B (P c596 (K 2 h Z)) rfl
  · exact L B (P c596 (M h Z)) rfl
  · exact L B (P c596 (K 2 h Z)) rfl
  · exact L B (P c596 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c593 (P h Z)) rfl
 · exact absurd h c596
 · exact L B (M c584 (P h Z)) rfl
 · exact absurd h c595
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (P c592 (M h Z)) rfl
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (P c592 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s220 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c584 : Q y false 0 2 3 4) (c592 : Q y true 0 1 3 5) (c593 : Q y false 1 3 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c585 : N (Q y true 0 1 2 5)) : False := by
 rcases em (Q y false 0 1 4 5) with c594 | c594
 ·
  exact s221 y B H c584 c592 c593 c594 c1 c320 c411 c486 c516 c575 c585
 rcases H.h01245 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c593 (P h Z)) rfl
 · exact L B (M c592 (P h Z)) rfl
 · exact LN B 1 1 c1 (M c593 (P h Z)) (P c593 (M h Z)) rfl rfl
 · exact L B (M c592 (P h Z)) rfl
 · exact absurd h c594
 · exact L B (M c592 (P h Z)) rfl
 · exact L B (M c584 (P h Z)) rfl
 · exact absurd h c585
 · exact absurd h c411
 · exact absurd h c486

set_option maxHeartbeats 4000000 in
lemma s219 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c584 : Q y false 0 2 3 4) (c592 : Q y true 0 1 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) (c585 : N (Q y true 0 1 2 5)) : False := by
 rcases em (Q y false 1 3 4 5) with c593 | c593
 ·
  exact s220 y B H c584 c592 c593 c1 c320 c411 c486 c516 c575 c585
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c486 (P c592 (P h Z)) (M c592 (M h Z)) rfl rfl
 · exact L B (M c592 (P h Z)) rfl
 · exact absurd h c593
 · exact L B (M c592 (P h Z)) rfl
 · exact G B (P c584 (P c592 (P h Z))) rfl
 · exact L B (M c592 (P h Z)) rfl
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (M c592 (P h Z)) rfl
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (M c592 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s218 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c584 : Q y false 0 2 3 4) (c585 : Q y true 0 1 2 5) (c586 : Q y false 0 1 4 5) (c587 : Q y false 1 2 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (_c516 : N (Q y false 0 1 3 4)) (_c575 : N (Q y true 0 1 3 4)) : False := by
 rcases em (Q y true 0 1 3 6) with c588 | c588
 ·
  rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c587 (P h Z)) rfl
  · exact L B (M c588 (P h Z)) rfl
  · exact LN B 1 1 c1 (M c585 (M c587 (P c588 (P h Z)))) (P c585 (P c587 (M c588 (M h Z)))) rfl rfl
  · exact L B (M c588 (P h Z)) rfl
  · exact L B (M c586 (P h Z)) rfl
  · exact L B (M c588 (P h Z)) rfl
  · exact L B (M c584 (P h Z)) rfl
  · exact L B (P c585 (M h Z)) rfl
  · exact absurd h c411
  · exact absurd h c486
 rcases em (Q y true 0 2 3 6) with c589 | c589
 ·
  rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c587 (P h Z)) rfl
  · exact L B (M c589 (P h Z)) rfl
  · exact L B (M c585 (M c586 (P c589 (P h Z)))) rfl
  · exact L B (M c589 (P h Z)) rfl
  · exact L B (M c586 (P h Z)) rfl
  · exact L B (M c584 (M c589 (P h Z))) rfl
  · exact L B (P c589 (P h Z)) rfl
  · exact L B (P c589 (M h Z)) rfl
  · exact absurd h c411
  · exact absurd h c486
 rcases em (Q y true 1 2 3 6) with c590 | c590
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c590 (P h Z)) rfl
  · exact L B (P c590 (M h Z)) rfl
  · exact L B (P c590 (P h Z)) rfl
  · exact L B (P c590 (M h Z)) rfl
  · exact L B (M c584 (P h Z)) rfl
  · exact L B (P c590 (M h Z)) rfl
  · exact L B (P c590 (K 2 h Z)) rfl
  · exact L B (P c590 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c584 (P h Z)) rfl
 · exact absurd h c590
 · exact L B (M c584 (P h Z)) rfl
 · exact absurd h c589
 · exact L B (M c586 (P h Z)) rfl
 · exact absurd h c588
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (P c585 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s217 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c584 : Q y false 0 2 3 4) (c585 : Q y true 0 1 2 5) (c586 : Q y false 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) : False := by
 rcases em (Q y false 1 2 4 5) with c587 | c587
 ·
  exact s218 y B H c584 c585 c586 c587 c1 c320 c411 c486 c516 c575
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c1 (P c586 (M h Z)) (M c586 (P h Z)) rfl rfl
 · exact L B (P c586 (P h Z)) rfl
 · exact G B (P c584 (P c585 (P h Z))) rfl
 · exact L B (M c585 (P h Z)) rfl
 · exact absurd h c587
 · exact L B (M c585 (P h Z)) rfl
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (P c584 (P c586 (P h Z))) rfl
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (P c584 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s216 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c584 : Q y false 0 2 3 4) (c585 : Q y true 0 1 2 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) (c575 : N (Q y true 0 1 3 4)) : False := by
 rcases em (Q y false 0 1 4 5) with c586 | c586
 ·
  exact s217 y B H c584 c585 c586 c1 c320 c411 c486 c516 c575
 rcases em (Q y false 0 3 4 5) with c591 | c591
 ·
  rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c591 (P h Z)) rfl
  · exact L B (M c585 (P h Z)) rfl
  · exact L B (M c591 (P h Z)) rfl
  · exact L B (M c585 (P h Z)) rfl
  · exact L B (M c591 (P h Z)) rfl
  · exact L B (M c585 (P h Z)) rfl
  · exact L B (M c584 (P h Z)) rfl
  · exact L B (M c585 (P h Z)) rfl
  · exact L B (M c584 (P h Z)) rfl
  · exact L B (P c584 (P h Z)) rfl
 rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact G B (P c584 (P c585 (P h Z))) rfl
 · exact L B (M c585 (P h Z)) rfl
 · exact absurd h c591
 · exact L B (M c585 (P h Z)) rfl
 · exact absurd h c586
 · exact L B (M c585 (P h Z)) rfl
 · exact L B (M c584 (P h Z)) rfl
 · exact L B (M c585 (P h Z)) rfl
 · exact absurd h c516
 · exact absurd h c575

set_option maxHeartbeats 4000000 in
lemma s215 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c575 : Q y true 0 1 3 4) (c581 : Q y false 1 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (_c516 : N (Q y false 0 1 3 4)) (c576 : N (Q y false 0 2 3 5)) (c579 : N (Q y true 0 2 3 5)) : False := by
 rcases em (Q y false 2 3 4 5) with c582 | c582
 ·
  rcases H.h01245 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c581 (M h Z)) rfl
  · exact L B (P c581 (P h Z)) rfl
  · exact L B (P c581 (M h Z)) rfl
  · exact L B (P c581 (P h Z)) rfl
  · exact LN B 1 1 c1 (M c582 (P h Z)) (P c582 (M h Z)) rfl rfl
  · exact LN B 1 1 c320 (P c582 (P h Z)) (M c582 (M h Z)) rfl rfl
  · exact L B (P c575 (P h Z)) rfl
  · exact L B (P c575 (M h Z)) rfl
  · exact absurd h c411
  · exact absurd h c486
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c582
 · exact L B (K 2 c581 (P h Z)) rfl
 · exact L B (P c581 (M h Z)) rfl
 · exact L B (P c581 (P h Z)) rfl
 · exact L B (P c581 (M h Z)) rfl
 · exact L B (P c581 (P h Z)) rfl
 · exact absurd h c576
 · exact absurd h c579
 · exact L B (P c581 (M h Z)) rfl
 · exact L B (P c581 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s214 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c575 : Q y true 0 1 3 4) (c579 : Q y true 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (_c516 : N (Q y false 0 1 3 4)) (_c576 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 1 2 3 6) with c580 | c580
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c579 (P h Z)) rfl
  · exact L B (P c580 (M h Z)) rfl
  · exact L B (P c579 (P h Z)) rfl
  · exact L B (P c579 (M h Z)) rfl
  · exact L B (P c575 (P h Z)) rfl
  · exact L B (P c575 (M h Z)) rfl
  · exact L B (P c575 (P h Z)) rfl
  · exact L B (P c575 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c579 (P h Z)) rfl
 · exact absurd h c580
 · exact L B (P c579 (P h Z)) rfl
 · exact L B (P c579 (M h Z)) rfl
 · exact L B (P c579 (P h Z)) rfl
 · exact L B (P c575 (M h Z)) rfl
 · exact L B (P c575 (P h Z)) rfl
 · exact L B (P c575 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s213 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c575 : Q y true 0 1 3 4) (c576 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (_c516 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y true 0 2 3 6) with c577 | c577
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c575 (M c576 (M c577 (M h Z)))) rfl
  · exact L B (M c577 (P h Z)) rfl
  · exact L B (P c575 (M c577 (M h Z))) rfl
  · exact L B (M c577 (P h Z)) rfl
  · exact L B (P c575 (M c577 (M h Z))) rfl
  · exact L B (M c577 (P h Z)) rfl
  · exact L B (P c575 (M c577 (M h Z))) rfl
  · exact L B (M c577 (P h Z)) rfl
  · exact L B (P c576 (M h Z)) rfl
  · exact L B (P c576 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c578 | c578
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c578 (P h Z)) rfl
  · exact L B (P c578 (M h Z)) rfl
  · exact L B (P c578 (P h Z)) rfl
  · exact L B (P c578 (M h Z)) rfl
  · exact L B (P c578 (K 2 h Z)) rfl
  · exact L B (P c578 (M h Z)) rfl
  · exact L B (P c578 (K 2 h Z)) rfl
  · exact L B (P c578 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c576 (P h Z)) rfl
 · exact absurd h c578
 · exact L B (M c576 (P h Z)) rfl
 · exact absurd h c577
 · exact L B (P c575 (P h Z)) rfl
 · exact L B (P c575 (M h Z)) rfl
 · exact L B (P c575 (P h Z)) rfl
 · exact L B (P c575 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s212 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c575 : Q y true 0 1 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c516 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y false 0 2 3 5) with c576 | c576
 ·
  exact s213 y B H c575 c576 c1 c320 c411 c486 c516
 rcases em (Q y true 0 2 3 5) with c579 | c579
 ·
  exact s214 y B H c575 c579 c1 c320 c411 c486 c516 c576
 rcases em (Q y false 1 2 3 5) with c581 | c581
 ·
  exact s215 y B H c575 c581 c1 c320 c411 c486 c516 c576 c579
 rcases em (Q y true 1 2 3 5) with c583 | c583
 ·
  rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c583 (P h Z)) rfl
  · exact L B (P c583 (M h Z)) rfl
  · exact L B (P c583 (P h Z)) rfl
  · exact L B (P c583 (M h Z)) rfl
  · exact L B (P c583 (K 2 h Z)) rfl
  · exact L B (P c583 (M h Z)) rfl
  · exact L B (P c583 (K 2 h Z)) rfl
  · exact L B (P c583 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01235 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c581
 · exact absurd h c583
 · exact absurd h c576
 · exact absurd h c579
 · exact L B (P c575 (P h Z)) rfl
 · exact L B (P c575 (M h Z)) rfl
 · exact L B (P c575 (P h Z)) rfl
 · exact L B (P c575 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s211 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c572 : Q y false 1 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (_c534 : N (Q y true 0 1 3 5)) (c545 : N (Q y false 0 2 3 5)) (c570 : N (Q y true 0 2 3 5)) : False := by
 rcases em (Q y false 2 3 4 5) with c573 | c573
 ·
  rcases H.h01245 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c572 (M h Z)) rfl
  · exact L B (P c572 (P h Z)) rfl
  · exact L B (P c572 (M h Z)) rfl
  · exact L B (P c572 (P h Z)) rfl
  · exact LN B 1 1 c1 (M c573 (P h Z)) (P c573 (M h Z)) rfl rfl
  · exact LN B 1 1 c320 (P c573 (P h Z)) (M c573 (M h Z)) rfl rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact absurd h c517
  · exact absurd h c411
  · exact absurd h c486
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c573
 · exact L B (K 2 c572 (P h Z)) rfl
 · exact L B (P c572 (M h Z)) rfl
 · exact L B (P c572 (P h Z)) rfl
 · exact L B (P c572 (M h Z)) rfl
 · exact L B (P c572 (P h Z)) rfl
 · exact absurd h c545
 · exact absurd h c570
 · exact L B (P c572 (M h Z)) rfl
 · exact L B (P c572 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s210 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c570 : Q y true 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (_c517 : N (Q y true 0 1 2 5)) (_c534 : N (Q y true 0 1 3 5)) (_c545 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 1 2 3 6) with c571 | c571
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c570 (P h Z)) rfl
  · exact L B (P c571 (M h Z)) rfl
  · exact L B (P c570 (P h Z)) rfl
  · exact L B (P c570 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c570 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c570 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c570 (P h Z)) rfl
 · exact absurd h c571
 · exact L B (P c570 (P h Z)) rfl
 · exact L B (P c570 (M h Z)) rfl
 · exact L B (M c516 (P h Z)) rfl
 · exact L B (P c570 (M h Z)) rfl
 · exact L B (M c516 (P h Z)) rfl
 · exact L B (P c570 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s209 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (_c545 : Q y false 0 2 3 5) (c564 : Q y false 1 2 4 5) (c565 : Q y true 0 1 2 6) (c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (_c517 : N (Q y true 0 1 2 5)) (c534 : N (Q y true 0 1 3 5)) (c546 : N (Q y false 0 1 4 5)) (_c560 : N (Q y true 0 1 4 5)) : False := by
 rcases em (Q y false 1 3 4 6) with c566 | c566
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c566 (M h Z)) rfl
  · exact L B (P c566 (P h Z)) rfl
  · exact L B (P c566 (M h Z)) rfl
  · exact L B (P c566 (P h Z)) rfl
  · exact LN B 1 1 c1 (P c564 (M c566 (P h Z))) (M c564 (P c566 (M h Z))) rfl rfl
  · exact L B (M c565 (P h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (M c565 (P h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact absurd h c534
 rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact G B (P c516 (P c565 (P h Z))) rfl
 · exact L B (M c565 (P h Z)) rfl
 · exact absurd h c566
 · exact L B (M c565 (P h Z)) rfl
 · exact L B (M c564 (P h Z)) rfl
 · exact L B (M c565 (P h Z)) rfl
 · exact L B (M c564 (P h Z)) rfl
 · exact L B (M c565 (P h Z)) rfl
 · exact LN B 1 1 c546 (P c516 (P c564 (M h Z))) (M c516 (M c564 (P h Z))) rfl rfl
 · exact L B (M c565 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s208 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c545 : Q y false 0 2 3 5) (c564 : Q y false 1 2 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (c534 : N (Q y true 0 1 3 5)) (c546 : N (Q y false 0 1 4 5)) (c560 : N (Q y true 0 1 4 5)) : False := by
 rcases em (Q y true 0 1 2 6) with c565 | c565
 ·
  exact s209 y B H c516 c545 c564 c565 c1 c320 c411 c486 c517 c534 c546 c560
 rcases em (Q y true 0 1 3 6) with c567 | c567
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c486 (P c567 (P h Z)) (M c567 (M h Z)) rfl rfl
  · exact L B (M c567 (P h Z)) rfl
  · exact LN B 1 1 c517 (M c564 (P c567 (P h Z))) (P c564 (M c567 (M h Z))) rfl rfl
  · exact L B (M c567 (P h Z)) rfl
  · exact L B (M c564 (P h Z)) rfl
  · exact L B (M c567 (P h Z)) rfl
  · exact L B (M c564 (P h Z)) rfl
  · exact L B (M c567 (P h Z)) rfl
  · exact LN B 1 1 c546 (P c516 (P c564 (M h Z))) (M c516 (M c564 (P h Z))) rfl rfl
  · exact L B (M c567 (P h Z)) rfl
 rcases em (Q y true 0 2 3 6) with c568 | c568
 ·
  rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c486 (P c564 (P c568 (P h Z))) (M c564 (M c568 (M h Z))) rfl rfl
  · exact L B (M c568 (P h Z)) rfl
  · exact LN B 1 1 c517 (P c568 (P h Z)) (M c568 (M h Z)) rfl rfl
  · exact L B (M c568 (P h Z)) rfl
  · exact LN B 1 1 c534 (P c568 (P h Z)) (M c568 (M h Z)) rfl rfl
  · exact L B (M c568 (P h Z)) rfl
  · exact L B (M c564 (P h Z)) rfl
  · exact L B (M c568 (P h Z)) rfl
  · exact L B (M c564 (P h Z)) rfl
  · exact L B (P c516 (P c564 (P h Z))) rfl
 rcases em (Q y true 1 2 3 6) with c569 | c569
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c564 (P h Z)) rfl
  · exact L B (P c569 (M h Z)) rfl
  · exact L B (M c516 (M c564 (P h Z))) rfl
  · exact L B (P c569 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c569 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c569 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c564 (P h Z)) rfl
 · exact absurd h c569
 · exact L B (M c516 (M c564 (P h Z))) rfl
 · exact absurd h c568
 · exact L B (M c516 (P h Z)) rfl
 · exact absurd h c567
 · exact L B (M c516 (P h Z)) rfl
 · exact absurd h c565
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s207 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (_c545 : Q y false 0 2 3 5) (c560 : Q y true 0 1 4 5) (c561 : Q y false 1 2 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (_c517 : N (Q y true 0 1 2 5)) (_c534 : N (Q y true 0 1 3 5)) (_c546 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y true 0 2 3 6) with c562 | c562
 ·
  rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c486 (P c561 (P c562 (P h Z))) (M c561 (M c562 (M h Z))) rfl rfl
  · exact L B (M c562 (P h Z)) rfl
  · exact L B (P c560 (M c562 (M h Z))) rfl
  · exact L B (M c562 (P h Z)) rfl
  · exact L B (P c560 (M c562 (M h Z))) rfl
  · exact L B (M c562 (P h Z)) rfl
  · exact L B (M c561 (P h Z)) rfl
  · exact L B (M c562 (P h Z)) rfl
  · exact L B (M c561 (P h Z)) rfl
  · exact L B (P c516 (P c561 (P h Z))) rfl
 rcases em (Q y true 1 2 3 6) with c563 | c563
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c563 (P h Z)) rfl
  · exact L B (P c563 (M h Z)) rfl
  · exact L B (P c563 (P h Z)) rfl
  · exact L B (P c563 (M h Z)) rfl
  · exact L B (P c563 (K 2 h Z)) rfl
  · exact L B (P c563 (M h Z)) rfl
  · exact L B (P c563 (K 2 h Z)) rfl
  · exact L B (P c563 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c561 (P h Z)) rfl
 · exact absurd h c563
 · exact L B (M c516 (M c561 (P h Z))) rfl
 · exact absurd h c562
 · exact L B (P c560 (P h Z)) rfl
 · exact L B (P c560 (M h Z)) rfl
 · exact L B (P c560 (P h Z)) rfl
 · exact L B (P c560 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s206 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c545 : Q y false 0 2 3 5) (c560 : Q y true 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (c534 : N (Q y true 0 1 3 5)) (c546 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y false 1 2 4 5) with c561 | c561
 ·
  exact s207 y B H c516 c545 c560 c561 c1 c320 c411 c486 c517 c534 c546
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c561 (M c516 (P c545 Z)) (P c516 (M c545 Z)) rfl rfl
 · exact L B (M c560 (P h Z)) rfl
 · exact L B (M c516 (P c545 (M h Z))) rfl
 · exact L B (P c545 (P h Z)) rfl
 · exact absurd h c561
 · exact L B (P c545 (P h Z)) rfl
 · exact L B (M c545 (P h Z)) rfl
 · exact L B (P c545 (P h Z)) rfl
 · exact L B (P c545 (P c560 (M h Z))) rfl
 · exact L B (P c545 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s205 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (_c545 : Q y false 0 2 3 5) (c546 : Q y false 0 1 4 5) (c547 : Q y false 1 2 3 4) (c548 : Q y true 0 1 2 6) (c549 : Q y false 0 2 4 6) (c550 : Q y false 0 1 5 6) (c551 : Q y false 3 4 5 6) (c552 : Q y false 1 2 5 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (_c534 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y true 0 1 3 7) with c553 | c553
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c552 (P h Z)) rfl
  · exact L B (M c553 (P h Z)) rfl
  · exact L B (M c546 (M c547 (M c551 (P h Z)))) rfl
  · exact L B (M c553 (P h Z)) rfl
  · exact L B (M c550 (P h Z)) rfl
  · exact L B (M c553 (P h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c548 (M h Z)) rfl
  · exact absurd h c411
  · exact absurd h c486
 rcases em (Q y true 0 2 3 7) with c554 | c554
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c516 (M c547 (M c550 (P h Z)))) rfl
  · exact L B (M c554 (P h Z)) rfl
  · exact L B (M c548 (M c550 (P c554 (P h Z)))) rfl
  · exact L B (M c554 (P h Z)) rfl
  · exact L B (M c516 (P c547 (M c552 (P h Z)))) rfl
  · exact L B (P c551 (M c552 (M c554 (P h Z)))) rfl
  · exact L B (M c550 (P h Z)) rfl
  · exact L B (P c548 (M h Z)) rfl
  · exact L B (M c546 (P h Z)) rfl
  · exact absurd h c517
 rcases em (Q y true 1 2 3 7) with c555 | c555
 ·
  rcases H.h13457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c547 (M c552 (P h Z))) rfl
  · exact L B (M c555 (P h Z)) rfl
  · exact L B (K 2 c546 (P c547 (M c548 (M c549 (P c555 (P h Z)))))) rfl
  · exact L B (M c555 (P h Z)) rfl
  · exact L B (M c548 (P c555 (P h Z))) rfl
  · exact L B (M c555 (P h Z)) rfl
  · exact L B (M c548 (P c555 (P h Z))) rfl
  · exact L B (M c555 (P h Z)) rfl
  · exact L B (P c546 (P c547 (M c550 (P c551 (M h Z))))) rfl
  · exact L B (P c546 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c547 (P h Z)) rfl
 · exact absurd h c555
 · exact L B (M c516 (M c547 (M c551 (P h Z)))) rfl
 · exact absurd h c554
 · exact L B (M c550 (P h Z)) rfl
 · exact absurd h c553
 · exact L B (M c546 (P h Z)) rfl
 · exact L B (P c548 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s204 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c545 : Q y false 0 2 3 5) (c546 : Q y false 0 1 4 5) (c547 : Q y false 1 2 3 4) (c548 : Q y true 0 1 2 6) (c549 : Q y false 0 2 4 6) (c550 : Q y false 0 1 5 6) (c551 : Q y false 3 4 5 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (c534 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y false 1 2 5 6) with c552 | c552
 ·
  exact s205 y B H c516 c545 c546 c547 c548 c549 c550 c551 c552 c1 c320 c411 c486 c517 c534
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c552 (M c546 (P c549 Z)) (M c547 (M c551 Z)) rfl rfl
 · exact L B (P c550 (P h Z)) rfl
 · exact L B (P c547 (P c551 (M h Z))) rfl
 · exact L B (P c550 (P h Z)) rfl
 · exact absurd h c552
 · exact L B (P c550 (P h Z)) rfl
 · exact L B (M c547 (P h Z)) rfl
 · exact L B (M c548 (P h Z)) rfl
 · exact L B (M c547 (P h Z)) rfl
 · exact L B (M c548 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s203 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c545 : Q y false 0 2 3 5) (c546 : Q y false 0 1 4 5) (c547 : Q y false 1 2 3 4) (c548 : Q y true 0 1 2 6) (c549 : Q y false 0 2 4 6) (c550 : Q y false 0 1 5 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (c534 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y false 3 4 5 6) with c551 | c551
 ·
  exact s204 y B H c516 c545 c546 c547 c548 c549 c550 c551 c1 c320 c411 c486 c517 c534
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c551
 · exact L B (M c548 (P h Z)) rfl
 · exact L B (P c550 (M h Z)) rfl
 · exact L B (M c548 (P h Z)) rfl
 · exact L B (P c550 (M h Z)) rfl
 · exact L B (P c550 (P h Z)) rfl
 · exact L B (M c516 (P c546 (P c547 (P c550 (M h Z))))) rfl
 · exact L B (M c548 (P h Z)) rfl
 · exact L B (P c546 (M h Z)) rfl
 · exact L B (P c546 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s202 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c545 : Q y false 0 2 3 5) (c546 : Q y false 0 1 4 5) (c547 : Q y false 1 2 3 4) (c548 : Q y true 0 1 2 6) (c549 : Q y false 0 2 4 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (c534 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y false 0 1 5 6) with c550 | c550
 ·
  exact s203 y B H c516 c545 c546 c547 c548 c549 c550 c1 c320 c411 c486 c517 c534
 rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c546 (P c549 (M h Z))) rfl
 · exact L B (P c549 (P h Z)) rfl
 · exact L B (P c549 (M h Z)) rfl
 · exact L B (P c549 (P h Z)) rfl
 · exact absurd h c550
 · exact L B (P c516 (M c546 (M c547 (P c549 (P h Z))))) rfl
 · exact L B (M c546 (P h Z)) rfl
 · exact L B (M c548 (P h Z)) rfl
 · exact L B (M c516 (P h Z)) rfl
 · exact absurd h c534

set_option maxHeartbeats 4000000 in
lemma s201 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c545 : Q y false 0 2 3 5) (c546 : Q y false 0 1 4 5) (c547 : Q y false 1 2 3 4) (c548 : Q y true 0 1 2 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (c534 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y false 0 2 4 6) with c549 | c549
 ·
  exact s202 y B H c516 c545 c546 c547 c548 c549 c1 c320 c411 c486 c517 c534
 rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact G B (P c516 (P c548 (P h Z))) rfl
 · exact L B (M c548 (P h Z)) rfl
 · exact G B (P c545 (P c546 (P c548 (P h Z)))) rfl
 · exact L B (M c548 (P h Z)) rfl
 · exact absurd h c549
 · exact L B (M c548 (P h Z)) rfl
 · exact L B (M c546 (M c547 (P h Z))) rfl
 · exact L B (M c548 (P h Z)) rfl
 · exact L B (P c516 (M h Z)) rfl
 · exact L B (P c516 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s200 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c545 : Q y false 0 2 3 5) (c546 : Q y false 0 1 4 5) (c547 : Q y false 1 2 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (c534 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y true 0 1 2 6) with c548 | c548
 ·
  exact s201 y B H c516 c545 c546 c547 c548 c1 c320 c411 c486 c517 c534
 rcases em (Q y true 0 1 3 6) with c556 | c556
 ·
  rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c516 (M c546 (M c547 (P h Z)))) rfl
  · exact L B (M c556 (P h Z)) rfl
  · exact G B (P c547 (P c556 (P h Z))) rfl
  · exact L B (M c556 (P h Z)) rfl
  · exact L B (M c545 (P c547 (P h Z))) rfl
  · exact L B (M c556 (P h Z)) rfl
  · exact L B (M c546 (P h Z)) rfl
  · exact absurd h c548
  · exact absurd h c411
  · exact absurd h c486
 rcases em (Q y true 0 2 3 6) with c557 | c557
 ·
  rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c534 (P c557 (P h Z)) (M c557 (M h Z)) rfl rfl
  · exact L B (M c557 (P h Z)) rfl
  · exact G B (P c516 (P c546 (P c557 (P h Z)))) rfl
  · exact L B (M c557 (P h Z)) rfl
  · exact LN B 1 1 c534 (M c516 (P c547 (P c557 (P h Z)))) (P c516 (M c547 (M c557 (M h Z)))) rfl rfl
  · exact L B (M c547 (M c557 (P h Z))) rfl
  · exact L B (M c546 (P h Z)) rfl
  · exact absurd h c548
  · exact L B (M c546 (P h Z)) rfl
  · exact absurd h c517
 rcases em (Q y true 1 2 3 6) with c558 | c558
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c547 (P h Z)) rfl
  · exact L B (P c558 (M h Z)) rfl
  · exact L B (P c558 (P h Z)) rfl
  · exact L B (P c558 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c558 (M h Z)) rfl
  · exact L B (M c546 (P h Z)) rfl
  · exact L B (P c558 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c547 (P h Z)) rfl
 · exact absurd h c558
 · exact L B (M c546 (M c547 (P h Z))) rfl
 · exact absurd h c557
 · exact L B (M c516 (P h Z)) rfl
 · exact absurd h c556
 · exact L B (M c546 (P h Z)) rfl
 · exact absurd h c548
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s199 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c534 : Q y true 0 1 3 5) (c541 : Q y false 1 2 4 5) (_c542 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (_c517 : N (Q y true 0 1 2 5)) (c535 : N (Q y false 0 1 4 5)) (_c540 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y true 0 2 3 6) with c543 | c543
 ·
  rcases H.h13456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c535 (P c516 (M c534 (P c541 (P c543 (P h Z))))) (M c516 (P c534 (M c541 (M c543 (M h Z))))) rfl rfl
  · exact L B (M c543 (P h Z)) rfl
  · exact L B (P c534 (M c543 (M h Z))) rfl
  · exact L B (M c543 (P h Z)) rfl
  · exact L B (P c534 (M c543 (M h Z))) rfl
  · exact L B (M c543 (P h Z)) rfl
  · exact LN B 1 1 c486 (P c543 (P h Z)) (M c543 (M h Z)) rfl rfl
  · exact L B (M c543 (P h Z)) rfl
  · exact L B (P c541 (M h Z)) rfl
  · exact L B (P c541 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c544 | c544
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c541 (P h Z)) rfl
  · exact L B (P c544 (M h Z)) rfl
  · exact L B (M c516 (M c541 (P h Z))) rfl
  · exact L B (P c544 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c534 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c534 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c541 (P h Z)) rfl
 · exact absurd h c544
 · exact L B (M c516 (M c541 (P h Z))) rfl
 · exact absurd h c543
 · exact L B (M c516 (P h Z)) rfl
 · exact L B (P c534 (M h Z)) rfl
 · exact L B (M c516 (P h Z)) rfl
 · exact L B (P c534 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s198 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c534 : Q y true 0 1 3 5) (c541 : Q y false 1 2 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) (c535 : N (Q y false 0 1 4 5)) (c540 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c542 | c542
 ·
  exact s199 y B H c516 c534 c541 c542 c1 c320 c411 c486 c517 c535 c540
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c542 (P c516 (P c541 Z)) (M c516 (M c541 Z)) rfl rfl
 · exact L B (P c541 (P h Z)) rfl
 · exact L B (P c541 (M h Z)) rfl
 · exact L B (P c541 (P h Z)) rfl
 · exact absurd h c540
 · exact L B (P c541 (P h Z)) rfl
 · exact absurd h c542
 · exact L B (P c516 (P c541 (P h Z))) rfl
 · exact L B (P c516 (M h Z)) rfl
 · exact L B (P c516 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s197 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c534 : Q y true 0 1 3 5) (c535 : Q y false 0 1 4 5) (c536 : Q y false 0 2 3 5) (c537 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (_c517 : N (Q y true 0 1 2 5)) : False := by
 rcases em (Q y true 1 2 3 7) with c538 | c538
 ·
  rcases H.h03457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c534 (M c535 (P c536 (P c537 (P h Z))))) rfl
  · exact L B (M c538 (P h Z)) rfl
  · exact L B (P c534 (M c538 (M h Z))) rfl
  · exact L B (M c516 (M c538 (P h Z))) rfl
  · exact L B (P c534 (M c538 (M h Z))) rfl
  · exact L B (M c535 (M c538 (P h Z))) rfl
  · exact LN B 1 1 c486 (P c538 (P h Z)) (M c538 (M h Z)) rfl rfl
  · exact L B (M c516 (M c538 (P h Z))) rfl
  · exact L B (P c535 (M h Z)) rfl
  · exact L B (P c535 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c536 (P h Z)) rfl
 · exact absurd h c538
 · exact L B (M c536 (P h Z)) rfl
 · exact L B (P c537 (M h Z)) rfl
 · exact L B (M c535 (P h Z)) rfl
 · exact L B (P c534 (M h Z)) rfl
 · exact L B (M c516 (P h Z)) rfl
 · exact L B (P c534 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s196 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c534 : Q y true 0 1 3 5) (c535 : Q y false 0 1 4 5) (c536 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) : False := by
 rcases em (Q y true 0 2 3 6) with c537 | c537
 ·
  exact s197 y B H c516 c534 c535 c536 c537 c1 c320 c411 c486 c517
 rcases em (Q y true 1 2 3 6) with c539 | c539
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c536 (P h Z)) rfl
  · exact L B (P c539 (M h Z)) rfl
  · exact L B (M c536 (P h Z)) rfl
  · exact L B (P c539 (M h Z)) rfl
  · exact L B (M c535 (P h Z)) rfl
  · exact L B (P c534 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c534 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c536 (P h Z)) rfl
 · exact absurd h c539
 · exact L B (M c536 (P h Z)) rfl
 · exact absurd h c537
 · exact L B (M c535 (P h Z)) rfl
 · exact L B (P c534 (M h Z)) rfl
 · exact L B (M c516 (P h Z)) rfl
 · exact L B (P c534 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s195 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c534 : Q y true 0 1 3 5) (c535 : Q y false 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c536 | c536
 ·
  exact s196 y B H c516 c534 c535 c536 c1 c320 c411 c486 c517
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c486 (P c534 (P h Z)) (M c534 (M h Z)) rfl rfl
 · exact L B (P c535 (P h Z)) rfl
 · exact L B (P c535 (M h Z)) rfl
 · exact L B (P c535 (P h Z)) rfl
 · exact L B (P c535 (M h Z)) rfl
 · exact L B (P c535 (P h Z)) rfl
 · exact absurd h c536
 · exact L B (M c534 (P h Z)) rfl
 · exact L B (P c516 (M h Z)) rfl
 · exact L B (P c516 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s194 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c534 : Q y true 0 1 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c517 : N (Q y true 0 1 2 5)) : False := by
 rcases em (Q y false 0 1 4 5) with c535 | c535
 ·
  exact s195 y B H c516 c534 c535 c1 c320 c411 c486 c517
 rcases em (Q y false 0 2 4 5) with c540 | c540
 ·
  rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c486 (P c534 (P h Z)) (M c534 (M h Z)) rfl rfl
  · exact L B (M c534 (P h Z)) rfl
  · exact LN B 1 1 c1 (P c540 (M h Z)) (M c540 (P h Z)) rfl rfl
  · exact L B (M c534 (P h Z)) rfl
  · exact L B (M c540 (P h Z)) rfl
  · exact L B (M c534 (P h Z)) rfl
  · exact L B (M c540 (P h Z)) rfl
  · exact L B (M c534 (P h Z)) rfl
  · exact G B (P c534 (P c540 (P h Z))) rfl
  · exact L B (M c534 (P h Z)) rfl
 rcases em (Q y false 1 2 4 5) with c541 | c541
 ·
  exact s198 y B H c516 c534 c541 c1 c320 c411 c486 c517 c535 c540
 rcases H.h01245 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c541
 · exact L B (M c534 (P h Z)) rfl
 · exact absurd h c540
 · exact L B (M c534 (P h Z)) rfl
 · exact absurd h c535
 · exact L B (M c534 (P h Z)) rfl
 · exact L B (M c516 (P h Z)) rfl
 · exact absurd h c517
 · exact absurd h c411
 · exact absurd h c486

set_option maxHeartbeats 4000000 in
lemma s193 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c517 : Q y true 0 1 2 5) (c528 : Q y false 0 2 4 5) (c529 : Q y false 1 2 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (_c518 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 0 1 3 6) with c530 | c530
 ·
  rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c528 (P h Z)) rfl
  · exact L B (M c530 (P h Z)) rfl
  · exact L B (M c528 (P h Z)) rfl
  · exact L B (M c530 (P h Z)) rfl
  · exact L B (M c528 (P h Z)) rfl
  · exact L B (M c530 (P h Z)) rfl
  · exact L B (M c528 (P h Z)) rfl
  · exact L B (P c530 (M h Z)) rfl
  · exact absurd h c411
  · exact absurd h c486
 rcases em (Q y true 0 2 3 6) with c531 | c531
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c517 (P c529 (P c531 (P h Z)))) rfl
  · exact L B (M c531 (P h Z)) rfl
  · exact L B (P c517 (M c531 (M h Z))) rfl
  · exact L B (M c531 (P h Z)) rfl
  · exact L B (P c517 (M c531 (M h Z))) rfl
  · exact L B (M c531 (P h Z)) rfl
  · exact L B (M c517 (M c528 (P c531 (P h Z)))) rfl
  · exact L B (M c531 (P h Z)) rfl
  · exact L B (P c528 (M h Z)) rfl
  · exact L B (M c531 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c532 | c532
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c528 (P h Z)) rfl
  · exact L B (P c532 (M h Z)) rfl
  · exact L B (P c532 (P h Z)) rfl
  · exact L B (P c532 (M h Z)) rfl
  · exact L B (M c528 (P h Z)) rfl
  · exact L B (P c532 (M h Z)) rfl
  · exact L B (M c528 (P h Z)) rfl
  · exact L B (P c532 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c528 (P h Z)) rfl
 · exact absurd h c532
 · exact L B (M c528 (P h Z)) rfl
 · exact absurd h c531
 · exact L B (M c516 (P h Z)) rfl
 · exact absurd h c530
 · exact L B (M c528 (P h Z)) rfl
 · exact L B (P c517 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s192 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c517 : Q y true 0 1 2 5) (c528 : Q y false 0 2 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) (c518 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y false 1 2 3 4) with c529 | c529
 ·
  exact s193 y B H c516 c517 c528 c529 c1 c320 c411 c486 c518
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact G B (P c516 (P c517 (P h Z))) rfl
 · exact L B (P c528 (P h Z)) rfl
 · exact LN B 1 1 c1 (P c528 (M h Z)) (M c528 (P h Z)) rfl rfl
 · exact L B (P c528 (P h Z)) rfl
 · exact L B (M c528 (P h Z)) rfl
 · exact L B (P c528 (P h Z)) rfl
 · exact L B (M c528 (P h Z)) rfl
 · exact L B (P c516 (P c528 (P h Z))) rfl
 · exact absurd h c529
 · exact L B (P c516 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s191 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c517 : Q y true 0 1 2 5) (_c518 : Q y false 0 2 3 5) (c524 : Q y false 1 2 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (c519 : N (Q y false 1 2 3 4)) : False := by
 rcases em (Q y true 0 1 3 6) with c525 | c525
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c517 (P c525 (P h Z))) rfl
  · exact L B (M c525 (P h Z)) rfl
  · exact L B (P c517 (P c524 (M c525 (M h Z)))) rfl
  · exact L B (M c525 (P h Z)) rfl
  · exact LN B 1 1 c1 (M c517 (M c524 (P c525 (P h Z)))) (P c517 (P c524 (M c525 (M h Z)))) rfl rfl
  · exact L B (M c525 (P h Z)) rfl
  · exact L B (M c516 (M c524 (P h Z))) rfl
  · exact L B (M c525 (P h Z)) rfl
  · exact L B (P c516 (M h Z)) rfl
  · exact L B (M c525 (P h Z)) rfl
 rcases em (Q y true 0 2 3 6) with c526 | c526
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c517 (P c526 (P h Z))) rfl
  · exact L B (M c526 (P h Z)) rfl
  · exact L B (M c517 (P c526 (P h Z))) rfl
  · exact L B (M c526 (P h Z)) rfl
  · exact L B (M c517 (P c526 (P h Z))) rfl
  · exact L B (M c526 (P h Z)) rfl
  · exact L B (P c526 (P h Z)) rfl
  · exact L B (M c526 (P h Z)) rfl
  · exact absurd h c519
  · exact L B (P c516 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c527 | c527
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c527 (P h Z)) rfl
  · exact L B (P c527 (M h Z)) rfl
  · exact L B (M c516 (M c524 (P h Z))) rfl
  · exact L B (P c527 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c527 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c517 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c524 (P h Z)) rfl
 · exact absurd h c527
 · exact L B (M c516 (M c524 (P h Z))) rfl
 · exact absurd h c526
 · exact L B (M c516 (P h Z)) rfl
 · exact absurd h c525
 · exact L B (M c516 (P h Z)) rfl
 · exact L B (P c517 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s190 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c517 : Q y true 0 1 2 5) (c518 : Q y false 0 2 3 5) (c519 : Q y false 1 2 3 4) (c521 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c486 : N (Q y true 0 1 2 4)) (_c520 : N (Q y true 0 1 3 6)) : False := by
 rcases em (Q y true 1 2 3 7) with c522 | c522
 ·
  rcases H.h02567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c517 (M c518 (M c522 (M h Z)))) rfl
  · exact L B (M c522 (P h Z)) rfl
  · exact L B (P c521 (M c522 (M h Z))) rfl
  · exact L B (P c521 (M c522 (P h Z))) rfl
  · exact L B (P c521 (M c522 (M h Z))) rfl
  · exact L B (P c521 (M c522 (P h Z))) rfl
  · exact L B (M c517 (P c522 (P h Z))) rfl
  · exact L B (M c516 (M c522 (P h Z))) rfl
  · exact G B (P c516 (P c518 (P c519 (P c521 (P h Z))))) rfl
  · exact L B (M c521 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c521 (P h Z)) rfl
 · exact absurd h c522
 · exact L B (P c521 (P h Z)) rfl
 · exact L B (P c521 (M h Z)) rfl
 · exact L B (P c521 (P h Z)) rfl
 · exact L B (P c521 (M h Z)) rfl
 · exact L B (M c516 (P h Z)) rfl
 · exact L B (P c521 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s189 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c517 : Q y true 0 1 2 5) (c518 : Q y false 0 2 3 5) (c519 : Q y false 1 2 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) : False := by
 rcases em (Q y true 0 1 3 6) with c520 | c520
 ·
  rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c516 (M c518 (P h Z))) rfl
  · exact L B (M c520 (P h Z)) rfl
  · exact G B (P c519 (P c520 (P h Z))) rfl
  · exact L B (M c520 (P h Z)) rfl
  · exact L B (M c518 (P c519 (P h Z))) rfl
  · exact L B (M c520 (P h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c517 (M h Z)) rfl
  · exact absurd h c411
  · exact absurd h c486
 rcases em (Q y true 0 2 3 6) with c521 | c521
 ·
  exact s190 y B H c516 c517 c518 c519 c521 c1 c320 c411 c486 c520
 rcases em (Q y true 1 2 3 6) with c523 | c523
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c523 (P h Z)) rfl
  · exact L B (P c523 (M h Z)) rfl
  · exact L B (M c518 (P h Z)) rfl
  · exact L B (P c523 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c523 (M h Z)) rfl
  · exact L B (M c516 (P h Z)) rfl
  · exact L B (P c517 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c519 (P h Z)) rfl
 · exact absurd h c523
 · exact L B (M c518 (P h Z)) rfl
 · exact absurd h c521
 · exact L B (M c516 (P h Z)) rfl
 · exact absurd h c520
 · exact L B (M c516 (P h Z)) rfl
 · exact L B (P c517 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s188 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c516 : Q y false 0 1 3 4) (c517 : Q y true 0 1 2 5) (c518 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c486 : N (Q y true 0 1 2 4)) : False := by
 rcases em (Q y false 1 2 3 4) with c519 | c519
 ·
  exact s189 y B H c516 c517 c518 c519 c1 c320 c411 c486
 rcases em (Q y false 1 2 4 5) with c524 | c524
 ·
  exact s191 y B H c516 c517 c518 c524 c1 c320 c411 c486 c519
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact G B (P c516 (P c517 (P h Z))) rfl
 · exact L B (M c517 (P h Z)) rfl
 · exact L B (M c516 (P c518 (M h Z))) rfl
 · exact L B (P c518 (P h Z)) rfl
 · exact absurd h c524
 · exact L B (M c517 (P h Z)) rfl
 · exact L B (M c518 (P h Z)) rfl
 · exact L B (M c517 (P h Z)) rfl
 · exact absurd h c519
 · exact L B (M c517 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s187 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (c512 : Q y true 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c487 : N (Q y false 0 1 3 5)) (_c488 : N (Q y true 0 1 3 5)) (_c496 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 1 2 3 6) with c513 | c513
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c512 (P h Z)) rfl
  · exact L B (P c513 (M h Z)) rfl
  · exact L B (P c512 (P h Z)) rfl
  · exact L B (P c512 (M h Z)) rfl
  · exact L B (P c513 (K 2 h Z)) rfl
  · exact L B (P c512 (M h Z)) rfl
  · exact L B (P c512 (P h Z)) rfl
  · exact L B (P c512 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c512 (P h Z)) rfl
 · exact absurd h c513
 · exact L B (P c512 (P h Z)) rfl
 · exact L B (P c512 (M h Z)) rfl
 · exact L B (P c512 (P h Z)) rfl
 · exact L B (P c512 (M h Z)) rfl
 · exact L B (P c486 (P h Z)) rfl
 · exact L B (P c512 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s186 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (c496 : Q y false 0 2 3 5) (c506 : Q y false 1 2 4 5) (c507 : Q y false 0 1 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (c487 : N (Q y false 0 1 3 5)) (c488 : N (Q y true 0 1 3 5)) (_c497 : N (Q y false 1 2 3 4)) : False := by
 rcases em (Q y true 0 1 3 6) with c508 | c508
 ·
  rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c486 (M c508 (M h Z))) rfl
  · exact L B (M c508 (P h Z)) rfl
  · exact L B (P c486 (M c508 (M h Z))) rfl
  · exact L B (M c508 (P h Z)) rfl
  · exact G B (P c496 (P c508 (P h Z))) rfl
  · exact L B (M c508 (P h Z)) rfl
  · exact L B (M c506 (P h Z)) rfl
  · exact L B (M c508 (P h Z)) rfl
  · exact L B (M c506 (P h Z)) rfl
  · exact L B (M c508 (P h Z)) rfl
 rcases em (Q y true 0 2 3 6) with c509 | c509
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c486 (M c509 (M h Z))) rfl
  · exact L B (M c509 (P h Z)) rfl
  · exact L B (P c486 (M c509 (M h Z))) rfl
  · exact L B (M c509 (P h Z)) rfl
  · exact LN B 1 1 c1 (M c486 (P c506 (P c509 (P h Z)))) (P c486 (M c506 (M c509 (M h Z)))) rfl rfl
  · exact L B (M c506 (M c509 (P h Z))) rfl
  · exact L B (M c507 (P h Z)) rfl
  · exact absurd h c508
  · exact absurd h c487
  · exact absurd h c488
 rcases em (Q y true 1 2 3 6) with c510 | c510
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c506 (P h Z)) rfl
  · exact L B (P c510 (M h Z)) rfl
  · exact L B (M c506 (M c507 (P h Z))) rfl
  · exact L B (P c510 (M h Z)) rfl
  · exact L B (M c507 (P h Z)) rfl
  · exact L B (P c510 (M h Z)) rfl
  · exact L B (M c507 (P h Z)) rfl
  · exact L B (P c486 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c506 (P h Z)) rfl
 · exact absurd h c510
 · exact L B (M c506 (M c507 (P h Z))) rfl
 · exact absurd h c509
 · exact L B (M c507 (P h Z)) rfl
 · exact absurd h c508
 · exact L B (M c507 (P h Z)) rfl
 · exact L B (P c486 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s185 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (c496 : Q y false 0 2 3 5) (c506 : Q y false 1 2 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c487 : N (Q y false 0 1 3 5)) (c488 : N (Q y true 0 1 3 5)) (c497 : N (Q y false 1 2 3 4)) : False := by
 rcases em (Q y false 0 1 3 4) with c507 | c507
 ·
  exact s186 y B H c486 c496 c506 c507 c1 c320 c411 c487 c488 c497
 rcases em (Q y true 0 1 4 5) with c511 | c511
 ·
  rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c506 (P h Z)) rfl
  · exact LN B 1 1 c507 (P c496 (M c506 Z)) (M c496 (P c506 Z)) rfl rfl
  · exact L B (M c496 (P h Z)) rfl
  · exact LN B 1 1 c507 (P c496 (M c506 Z)) (M c496 (P c506 Z)) rfl rfl
  · exact L B (M c496 (P h Z)) rfl
  · exact L B (P c511 (M h Z)) rfl
  · exact L B (P c511 (P h Z)) rfl
  · exact L B (P c511 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c506 (M h Z)) rfl
 · exact L B (P c506 (P h Z)) rfl
 · exact L B (P c506 (M h Z)) rfl
 · exact L B (P c506 (P h Z)) rfl
 · exact LN B 1 1 c507 (P c496 (M c506 Z)) (M c496 (P c506 Z)) rfl rfl
 · exact absurd h c511
 · exact absurd h c487
 · exact absurd h c488
 · exact absurd h c507
 · exact L B (P c496 (M c506 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s184 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (_c496 : Q y false 0 2 3 5) (c497 : Q y false 1 2 3 4) (c502 : Q y false 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c487 : N (Q y false 0 1 3 5)) (c488 : N (Q y true 0 1 3 5)) (_c498 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y true 0 1 3 6) with c503 | c503
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact G B (P c502 (P c503 (P h Z))) rfl
  · exact L B (M c503 (P h Z)) rfl
  · exact L B (P c486 (M c503 (M h Z))) rfl
  · exact L B (M c503 (P h Z)) rfl
  · exact L B (P c486 (M c503 (M h Z))) rfl
  · exact L B (M c503 (P h Z)) rfl
  · exact L B (P c486 (M c503 (M h Z))) rfl
  · exact L B (M c503 (P h Z)) rfl
  · exact L B (P c486 (M c503 (M h Z))) rfl
  · exact L B (M c503 (P h Z)) rfl
 rcases em (Q y true 0 2 3 6) with c504 | c504
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c488 (P c497 (P c504 (P h Z))) (M c497 (M c504 (M h Z))) rfl rfl
  · exact L B (M c504 (P h Z)) rfl
  · exact L B (P c486 (M c504 (M h Z))) rfl
  · exact L B (M c504 (P h Z)) rfl
  · exact L B (P c486 (M c504 (M h Z))) rfl
  · exact L B (M c504 (P h Z)) rfl
  · exact L B (P c486 (M c504 (M h Z))) rfl
  · exact L B (M c504 (P h Z)) rfl
  · exact L B (P c502 (M h Z)) rfl
  · exact L B (P c502 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c505 | c505
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c497 (P h Z)) rfl
  · exact L B (P c505 (M h Z)) rfl
  · exact L B (M c497 (M c502 (P h Z))) rfl
  · exact L B (P c505 (M h Z)) rfl
  · exact L B (M c502 (P h Z)) rfl
  · exact L B (P c505 (M h Z)) rfl
  · exact L B (M c502 (P h Z)) rfl
  · exact L B (P c486 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c497 (P h Z)) rfl
 · exact absurd h c505
 · exact L B (M c497 (M c502 (P h Z))) rfl
 · exact absurd h c504
 · exact L B (M c502 (P h Z)) rfl
 · exact absurd h c503
 · exact L B (M c502 (P h Z)) rfl
 · exact L B (P c486 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s183 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (c496 : Q y false 0 2 3 5) (c497 : Q y false 1 2 3 4) (c498 : Q y false 0 1 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c487 : N (Q y false 0 1 3 5)) (c488 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y true 0 1 3 6) with c499 | c499
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact G B (P c496 (P c497 (P c499 (P h Z)))) rfl
  · exact L B (M c499 (P h Z)) rfl
  · exact L B (P c486 (M c499 (M h Z))) rfl
  · exact L B (M c499 (P h Z)) rfl
  · exact L B (P c486 (M c499 (M h Z))) rfl
  · exact L B (M c499 (P h Z)) rfl
  · exact L B (P c486 (M c499 (M h Z))) rfl
  · exact L B (M c499 (P h Z)) rfl
  · exact L B (P c486 (M c499 (M h Z))) rfl
  · exact L B (M c499 (P h Z)) rfl
 rcases em (Q y true 0 2 3 6) with c500 | c500
 ·
  rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c488 (P c500 (P h Z)) (M c500 (M h Z)) rfl rfl
  · exact L B (M c500 (P h Z)) rfl
  · exact G B (P c496 (P c497 (P c498 (P c500 (P h Z))))) rfl
  · exact L B (M c500 (P h Z)) rfl
  · exact LN B 1 1 c488 (P c497 (M c498 (P c500 (P h Z)))) (M c497 (P c498 (M c500 (M h Z)))) rfl rfl
  · exact L B (M c497 (M c500 (P h Z))) rfl
  · exact L B (M c498 (P h Z)) rfl
  · exact L B (P c486 (M h Z)) rfl
  · exact L B (M c498 (P h Z)) rfl
  · exact L B (P c486 (M h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c501 | c501
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c497 (P h Z)) rfl
  · exact L B (P c501 (M h Z)) rfl
  · exact L B (M c496 (P h Z)) rfl
  · exact L B (P c501 (M h Z)) rfl
  · exact L B (M c498 (P h Z)) rfl
  · exact L B (P c501 (M h Z)) rfl
  · exact L B (M c498 (P h Z)) rfl
  · exact L B (P c486 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c497 (P h Z)) rfl
 · exact absurd h c501
 · exact L B (M c496 (P h Z)) rfl
 · exact absurd h c500
 · exact L B (M c498 (P h Z)) rfl
 · exact absurd h c499
 · exact L B (M c498 (P h Z)) rfl
 · exact L B (P c486 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s182 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (c496 : Q y false 0 2 3 5) (c497 : Q y false 1 2 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c487 : N (Q y false 0 1 3 5)) (c488 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y false 0 1 3 4) with c498 | c498
 ·
  exact s183 y B H c486 c496 c497 c498 c1 c320 c411 c487 c488
 rcases em (Q y false 0 1 4 5) with c502 | c502
 ·
  exact s184 y B H c486 c496 c497 c502 c1 c320 c411 c487 c488 c498
 rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c486 (P c496 (M h Z))) rfl
 · exact L B (P c496 (P h Z)) rfl
 · exact L B (P c496 (M h Z)) rfl
 · exact L B (P c496 (P h Z)) rfl
 · exact absurd h c502
 · exact L B (P c496 (M c497 (P h Z))) rfl
 · exact absurd h c487
 · exact absurd h c488
 · exact absurd h c498
 · exact L B (M c486 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s181 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (c488 : Q y true 0 1 3 5) (c492 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c487 : N (Q y false 0 1 3 5)) (_c489 : N (Q y false 0 2 3 6)) : False := by
 rcases em (Q y true 1 2 3 7) with c493 | c493
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c488 (P c492 (M c493 (M h Z)))) rfl
  · exact L B (M c493 (P h Z)) rfl
  · exact L B (P c486 (M c493 (M h Z))) rfl
  · exact L B (P c486 (M c493 (P h Z))) rfl
  · exact L B (P c488 (M c493 (M h Z))) rfl
  · exact L B (P c486 (M c493 (P h Z))) rfl
  · exact L B (P c486 (M c493 (M h Z))) rfl
  · exact L B (P c488 (M c493 (P h Z))) rfl
  · exact L B (P c486 (M c493 (M h Z))) rfl
  · exact L B (M c492 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c492 (P h Z)) rfl
 · exact absurd h c493
 · exact L B (P c492 (P h Z)) rfl
 · exact L B (P c492 (M h Z)) rfl
 · exact L B (P c488 (P h Z)) rfl
 · exact L B (P c488 (M h Z)) rfl
 · exact L B (P c486 (P h Z)) rfl
 · exact L B (P c486 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s180 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (_c488 : Q y true 0 1 3 5) (c489 : Q y false 0 2 3 6) (c490 : Q y false 2 3 4 5) (_c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) (_c411 : N (Q y false 0 1 2 4)) (_c487 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 2 4 5 6) with c491 | c491
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c491 (P h Z)) rfl
  · exact L B (P c491 (P h Z)) rfl
  · exact L B (P c491 (M h Z)) rfl
  · exact L B (P c489 (P h Z)) rfl
  · exact L B (P c489 (M h Z)) rfl
  · exact L B (P c489 (P h Z)) rfl
  · exact L B (P c489 (M h Z)) rfl
  · exact L B (P c489 (P h Z)) rfl
  · exact L B (P c489 (M h Z)) rfl
  · exact L B (P c489 (P h Z)) rfl
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c491
 · exact L B (K 2 c489 (P h Z)) rfl
 · exact L B (P c489 (M h Z)) rfl
 · exact L B (P c489 (P h Z)) rfl
 · exact L B (P c489 (M h Z)) rfl
 · exact L B (P c489 (P h Z)) rfl
 · exact L B (P c489 (M h Z)) rfl
 · exact L B (P c489 (P h Z)) rfl
 · exact L B (P c489 (M h Z)) rfl
 · exact L B (M c486 (P c490 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s179 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (c488 : Q y true 0 1 3 5) (c489 : Q y false 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c487 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 2 3 4 5) with c490 | c490
 ·
  exact s180 y B H c486 c488 c489 c490 c1 c320 c411 c487
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c490
 · exact L B (K 2 c489 (P h Z)) rfl
 · exact L B (P c486 (M c488 (M h Z))) rfl
 · exact L B (P c489 (P h Z)) rfl
 · exact L B (P c489 (M h Z)) rfl
 · exact L B (M c488 (P h Z)) rfl
 · exact L B (P c489 (M h Z)) rfl
 · exact L B (P c489 (P h Z)) rfl
 · exact L B (P c489 (M h Z)) rfl
 · exact L B (M c486 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s178 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c486 : Q y true 0 1 2 4) (c488 : Q y true 0 1 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c411 : N (Q y false 0 1 2 4)) (c487 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 0 2 3 6) with c489 | c489
 ·
  exact s179 y B H c486 c488 c489 c1 c320 c411 c487
 rcases em (Q y true 0 2 3 6) with c492 | c492
 ·
  exact s181 y B H c486 c488 c492 c1 c320 c411 c487 c489
 rcases em (Q y false 1 2 3 6) with c494 | c494
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c486 (P c488 (P h Z))) rfl
  · exact L B (K 2 c494 (P h Z)) rfl
  · exact L B (P c494 (M h Z)) rfl
  · exact L B (P c494 (P h Z)) rfl
  · exact L B (P c494 (M h Z)) rfl
  · exact L B (P c494 (P h Z)) rfl
  · exact absurd h c489
  · exact absurd h c492
  · exact L B (P c494 (M h Z)) rfl
  · exact L B (P c494 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c495 | c495
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c495 (P h Z)) rfl
  · exact L B (P c495 (M h Z)) rfl
  · exact L B (P c495 (P h Z)) rfl
  · exact L B (P c495 (M h Z)) rfl
  · exact L B (P c488 (P h Z)) rfl
  · exact L B (P c495 (M h Z)) rfl
  · exact L B (P c495 (K 2 h Z)) rfl
  · exact L B (P c495 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c494
 · exact absurd h c495
 · exact absurd h c489
 · exact absurd h c492
 · exact L B (P c488 (P h Z)) rfl
 · exact L B (P c488 (M h Z)) rfl
 · exact L B (P c486 (P h Z)) rfl
 · exact L B (P c488 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s177 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c482 : Q y true 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c412 : N (Q y true 0 1 2 5)) (_c437 : N (Q y false 0 1 3 5)) (_c453 : N (Q y true 0 1 3 5)) (_c463 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 1 2 3 6) with c483 | c483
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c483 (P h Z)) rfl
  · exact L B (P c483 (M h Z)) rfl
  · exact L B (P c482 (P h Z)) rfl
  · exact L B (P c482 (M h Z)) rfl
  · exact L B (P c482 (P h Z)) rfl
  · exact L B (P c482 (M h Z)) rfl
  · exact L B (M c411 (P h Z)) rfl
  · exact L B (P c482 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c482 (P h Z)) rfl
 · exact absurd h c483
 · exact L B (P c482 (P h Z)) rfl
 · exact L B (P c482 (M h Z)) rfl
 · exact L B (P c482 (P h Z)) rfl
 · exact L B (P c482 (M h Z)) rfl
 · exact L B (P c482 (P h Z)) rfl
 · exact L B (P c482 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s176 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c463 : Q y false 0 2 3 5) (c477 : Q y false 1 3 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c412 : N (Q y true 0 1 2 5)) (_c437 : N (Q y false 0 1 3 5)) (_c453 : N (Q y true 0 1 3 5)) (c464 : N (Q y false 1 2 3 4)) : False := by
 rcases em (Q y true 0 1 2 6) with c478 | c478
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c411 (M c463 (P h Z))) rfl
  · exact L B (M c478 (P h Z)) rfl
  · exact L B (P c411 (M c463 (P h Z))) rfl
  · exact L B (M c478 (P h Z)) rfl
  · exact L B (P c411 (M c463 (P h Z))) rfl
  · exact L B (M c478 (P h Z)) rfl
  · exact L B (M c463 (P h Z)) rfl
  · exact L B (M c478 (P h Z)) rfl
  · exact absurd h c464
  · exact L B (M c478 (P h Z)) rfl
 rcases em (Q y true 0 1 3 6) with c479 | c479
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c411 (M c463 (P h Z))) rfl
  · exact L B (M c479 (P h Z)) rfl
  · exact L B (P c411 (M c463 (P h Z))) rfl
  · exact L B (M c479 (P h Z)) rfl
  · exact L B (P c411 (M c463 (P h Z))) rfl
  · exact L B (M c479 (P h Z)) rfl
  · exact L B (M c463 (P h Z)) rfl
  · exact L B (M c479 (P h Z)) rfl
  · exact absurd h c464
  · exact L B (M c479 (P h Z)) rfl
 rcases em (Q y true 0 2 3 6) with c480 | c480
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c411 (M c463 (P h Z))) rfl
  · exact L B (M c480 (P h Z)) rfl
  · exact L B (P c411 (M c463 (P h Z))) rfl
  · exact L B (M c480 (P h Z)) rfl
  · exact L B (P c411 (M c463 (P h Z))) rfl
  · exact L B (M c480 (P h Z)) rfl
  · exact L B (M c477 (P h Z)) rfl
  · exact L B (M c480 (P h Z)) rfl
  · exact absurd h c464
  · exact L B (P c463 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c481 | c481
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c481 (P h Z)) rfl
  · exact L B (P c481 (M h Z)) rfl
  · exact L B (P c481 (P h Z)) rfl
  · exact L B (P c481 (M h Z)) rfl
  · exact L B (M c463 (P h Z)) rfl
  · exact L B (P c481 (M h Z)) rfl
  · exact L B (M c463 (P h Z)) rfl
  · exact L B (P c481 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c463 (P h Z)) rfl
 · exact absurd h c481
 · exact L B (M c463 (P h Z)) rfl
 · exact absurd h c480
 · exact L B (M c463 (P h Z)) rfl
 · exact absurd h c479
 · exact L B (M c463 (P h Z)) rfl
 · exact absurd h c478
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s175 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (_c463 : Q y false 0 2 3 5) (c464 : Q y false 1 2 3 4) (c465 : Q y false 0 1 4 5) (c467 : Q y true 0 1 3 6) (_c468 : Q y false 0 3 4 6) (c469 : Q y false 0 1 5 6) (_c470 : Q y false 2 4 5 6) (c471 : Q y false 1 3 5 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c412 : N (Q y true 0 1 2 5)) (c437 : N (Q y false 0 1 3 5)) (c453 : N (Q y true 0 1 3 5)) (_c466 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y true 0 2 3 7) with c472 | c472
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c411 (M c464 (M c469 (P h Z)))) rfl
  · exact L B (M c472 (P h Z)) rfl
  · exact L B (P c467 (P c469 (M c472 (M h Z)))) rfl
  · exact L B (M c472 (P h Z)) rfl
  · exact L B (M c469 (P h Z)) rfl
  · exact L B (M c465 (P c469 (M c471 (M c472 (P h Z))))) rfl
  · exact L B (M c465 (P h Z)) rfl
  · exact L B (P c467 (M h Z)) rfl
  · exact absurd h c437
  · exact absurd h c453
 rcases em (Q y true 1 2 3 7) with c473 | c473
 ·
  rcases H.h12457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c464 (M c471 (P h Z))) rfl
  · exact L B (M c473 (P h Z)) rfl
  · exact L B (P c464 (M c467 (M c471 (P c473 (P h Z))))) rfl
  · exact L B (M c473 (P h Z)) rfl
  · exact L B (M c471 (P h Z)) rfl
  · exact L B (M c473 (P h Z)) rfl
  · exact L B (M c467 (P c473 (P h Z))) rfl
  · exact L B (M c473 (P h Z)) rfl
  · exact L B (M c465 (P c469 (M c471 (P h Z)))) rfl
  · exact L B (P c465 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c464 (P h Z)) rfl
 · exact absurd h c473
 · exact L B (M c465 (M c471 (P h Z))) rfl
 · exact absurd h c472
 · exact L B (M c465 (P h Z)) rfl
 · exact L B (P c467 (M h Z)) rfl
 · exact L B (M c465 (P h Z)) rfl
 · exact L B (P c467 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s174 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c463 : Q y false 0 2 3 5) (c464 : Q y false 1 2 3 4) (c465 : Q y false 0 1 4 5) (c467 : Q y true 0 1 3 6) (c468 : Q y false 0 3 4 6) (c469 : Q y false 0 1 5 6) (c470 : Q y false 2 4 5 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c412 : N (Q y true 0 1 2 5)) (c437 : N (Q y false 0 1 3 5)) (c453 : N (Q y true 0 1 3 5)) (c466 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 1 3 5 6) with c471 | c471
 ·
  exact s175 y B H c411 c463 c464 c465 c467 c468 c469 c470 c471 c1 c320 c412 c437 c453 c466
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c470 (P h Z)) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact absurd h c471
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (M c464 (M c470 (P h Z))) rfl
 · exact L B (P c469 (P h Z)) rfl
 · exact L B (M c464 (P h Z)) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (M c464 (P h Z)) rfl
 · exact L B (M c467 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s173 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c463 : Q y false 0 2 3 5) (c464 : Q y false 1 2 3 4) (c465 : Q y false 0 1 4 5) (c467 : Q y true 0 1 3 6) (c468 : Q y false 0 3 4 6) (c469 : Q y false 0 1 5 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c412 : N (Q y true 0 1 2 5)) (c437 : N (Q y false 0 1 3 5)) (c453 : N (Q y true 0 1 3 5)) (c466 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 2 4 5 6) with c470 | c470
 ·
  exact s174 y B H c411 c463 c464 c465 c467 c468 c469 c470 c1 c320 c412 c437 c453 c466
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c470
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (P c469 (M h Z)) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (P c469 (M h Z)) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (P c411 (M c464 (M c465 (M c469 (P h Z))))) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (P c465 (M h Z)) rfl
 · exact L B (M c467 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s172 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c463 : Q y false 0 2 3 5) (c464 : Q y false 1 2 3 4) (c465 : Q y false 0 1 4 5) (c467 : Q y true 0 1 3 6) (c468 : Q y false 0 3 4 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c412 : N (Q y true 0 1 2 5)) (c437 : N (Q y false 0 1 3 5)) (c453 : N (Q y true 0 1 3 5)) (c466 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 0 1 5 6) with c469 | c469
 ·
  exact s173 y B H c411 c463 c464 c465 c467 c468 c469 c1 c320 c412 c437 c453 c466
 rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c465 (M c468 (P h Z))) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (P c411 (M c465 (P c468 (M h Z)))) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact absurd h c469
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (M c465 (P h Z)) rfl
 · exact absurd h c466
 · exact L B (M c465 (P h Z)) rfl
 · exact absurd h c412

set_option maxHeartbeats 4000000 in
lemma s171 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c463 : Q y false 0 2 3 5) (c464 : Q y false 1 2 3 4) (c465 : Q y false 0 1 4 5) (c467 : Q y true 0 1 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c412 : N (Q y true 0 1 2 5)) (c437 : N (Q y false 0 1 3 5)) (c453 : N (Q y true 0 1 3 5)) (c466 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 0 3 4 6) with c468 | c468
 ·
  exact s172 y B H c411 c463 c464 c465 c467 c468 c1 c320 c412 c437 c453 c466
 rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c411 (M c465 (P h Z))) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact absurd h c468
 · exact L B (M c467 (P h Z)) rfl
 · exact G B (P c464 (P c467 (P h Z))) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (M c464 (M c465 (P h Z))) rfl
 · exact L B (M c467 (P h Z)) rfl
 · exact L B (P c411 (M h Z)) rfl
 · exact L B (M c467 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s170 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c463 : Q y false 0 2 3 5) (c464 : Q y false 1 2 3 4) (c465 : Q y false 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c412 : N (Q y true 0 1 2 5)) (c437 : N (Q y false 0 1 3 5)) (c453 : N (Q y true 0 1 3 5)) : False := by
 rcases em (Q y true 0 1 2 6) with c466 | c466
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c411 (M c464 (M c465 (P h Z)))) rfl
  · exact L B (M c466 (P h Z)) rfl
  · exact G B (P c464 (P c466 (P h Z))) rfl
  · exact L B (M c466 (P h Z)) rfl
  · exact L B (M c465 (P h Z)) rfl
  · exact L B (M c466 (P h Z)) rfl
  · exact L B (M c465 (P h Z)) rfl
  · exact L B (M c466 (P h Z)) rfl
  · exact L B (P c411 (M h Z)) rfl
  · exact L B (M c466 (P h Z)) rfl
 rcases em (Q y true 0 1 3 6) with c467 | c467
 ·
  exact s171 y B H c411 c463 c464 c465 c467 c1 c320 c412 c437 c453 c466
 rcases em (Q y true 0 2 3 6) with c474 | c474
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c412 (P c474 (P h Z)) (M c474 (M h Z)) rfl rfl
  · exact L B (M c474 (P h Z)) rfl
  · exact G B (P c411 (P c465 (P c474 (P h Z)))) rfl
  · exact L B (M c474 (P h Z)) rfl
  · exact LN B 1 1 c412 (M c411 (P c464 (P c474 (P h Z)))) (P c411 (M c464 (M c474 (M h Z)))) rfl rfl
  · exact L B (M c464 (M c474 (P h Z))) rfl
  · exact L B (M c465 (P h Z)) rfl
  · exact absurd h c467
  · exact absurd h c437
  · exact absurd h c453
 rcases em (Q y true 1 2 3 6) with c475 | c475
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c475 (P h Z)) rfl
  · exact L B (P c475 (M h Z)) rfl
  · exact L B (P c475 (P h Z)) rfl
  · exact L B (P c475 (M h Z)) rfl
  · exact L B (M c465 (P h Z)) rfl
  · exact L B (P c475 (M h Z)) rfl
  · exact L B (M c465 (P h Z)) rfl
  · exact L B (P c475 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c464 (P h Z)) rfl
 · exact absurd h c475
 · exact L B (M c464 (M c465 (P h Z))) rfl
 · exact absurd h c474
 · exact L B (M c465 (P h Z)) rfl
 · exact absurd h c467
 · exact L B (M c465 (P h Z)) rfl
 · exact absurd h c466
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s169 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (_c411 : Q y false 0 1 2 4) (c453 : Q y true 0 1 3 5) (c459 : Q y false 0 3 4 5) (c460 : Q y false 1 2 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c412 : N (Q y true 0 1 2 5)) (_c437 : N (Q y false 0 1 3 5)) (_c454 : N (Q y false 0 2 3 5)) (c458 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y true 0 2 3 6) with c461 | c461
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c453 (M c460 (M c461 (M h Z)))) rfl
  · exact L B (M c461 (P h Z)) rfl
  · exact L B (P c453 (M c461 (M h Z))) rfl
  · exact L B (M c461 (P h Z)) rfl
  · exact L B (P c453 (M c461 (M h Z))) rfl
  · exact L B (M c461 (P h Z)) rfl
  · exact L B (M c459 (P h Z)) rfl
  · exact L B (M c461 (P h Z)) rfl
  · exact absurd h c458
  · exact L B (M c453 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c462 | c462
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c462 (P h Z)) rfl
  · exact L B (P c462 (M h Z)) rfl
  · exact L B (P c462 (P h Z)) rfl
  · exact L B (P c462 (M h Z)) rfl
  · exact L B (P c453 (P h Z)) rfl
  · exact L B (P c453 (M h Z)) rfl
  · exact L B (P c453 (P h Z)) rfl
  · exact L B (P c453 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c460 (P h Z)) rfl
 · exact absurd h c462
 · exact L B (M c459 (P h Z)) rfl
 · exact absurd h c461
 · exact L B (P c453 (P h Z)) rfl
 · exact L B (P c453 (M h Z)) rfl
 · exact L B (P c453 (P h Z)) rfl
 · exact L B (P c453 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s168 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c453 : Q y true 0 1 3 5) (c459 : Q y false 0 3 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c412 : N (Q y true 0 1 2 5)) (c437 : N (Q y false 0 1 3 5)) (c454 : N (Q y false 0 2 3 5)) (c458 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y false 1 2 3 4) with c460 | c460
 ·
  exact s169 y B H c411 c453 c459 c460 c1 c320 c412 c437 c454 c458
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c459 (P h Z)) rfl
 · exact L B (M c453 (P h Z)) rfl
 · exact L B (M c459 (P h Z)) rfl
 · exact L B (M c453 (P h Z)) rfl
 · exact L B (M c459 (P h Z)) rfl
 · exact L B (M c453 (P h Z)) rfl
 · exact L B (M c459 (P h Z)) rfl
 · exact L B (M c453 (P h Z)) rfl
 · exact absurd h c460
 · exact L B (K 2 c411 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s167 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (_c411 : Q y false 0 1 2 4) (c453 : Q y true 0 1 3 5) (c454 : Q y false 0 2 3 5) (c455 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c412 : N (Q y true 0 1 2 5)) (_c437 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y true 1 2 3 7) with c456 | c456
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c453 (M c454 (M c456 (M h Z)))) rfl
  · exact L B (M c456 (P h Z)) rfl
  · exact L B (P c455 (M c456 (M h Z))) rfl
  · exact L B (P c455 (M c456 (P h Z))) rfl
  · exact L B (P c455 (M c456 (M h Z))) rfl
  · exact L B (P c455 (M c456 (P h Z))) rfl
  · exact L B (P c453 (M c456 (M h Z))) rfl
  · exact L B (P c453 (M c456 (P h Z))) rfl
  · exact L B (P c453 (M c455 (M h Z))) rfl
  · exact L B (M c455 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c454 (P h Z)) rfl
 · exact absurd h c456
 · exact L B (M c454 (P h Z)) rfl
 · exact L B (P c455 (M h Z)) rfl
 · exact L B (P c453 (P h Z)) rfl
 · exact L B (P c453 (M h Z)) rfl
 · exact L B (P c453 (P h Z)) rfl
 · exact L B (P c453 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s166 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c453 : Q y true 0 1 3 5) (c454 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c412 : N (Q y true 0 1 2 5)) (c437 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y true 0 2 3 6) with c455 | c455
 ·
  exact s167 y B H c411 c453 c454 c455 c1 c320 c412 c437
 rcases em (Q y true 1 2 3 6) with c457 | c457
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c454 (P h Z)) rfl
  · exact L B (P c457 (M h Z)) rfl
  · exact L B (M c454 (P h Z)) rfl
  · exact L B (P c457 (M h Z)) rfl
  · exact L B (P c453 (P h Z)) rfl
  · exact L B (P c453 (M h Z)) rfl
  · exact L B (P c453 (P h Z)) rfl
  · exact L B (P c453 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c454 (P h Z)) rfl
 · exact absurd h c457
 · exact L B (M c454 (P h Z)) rfl
 · exact absurd h c455
 · exact L B (M c454 (P h Z)) rfl
 · exact L B (P c453 (M h Z)) rfl
 · exact L B (M c454 (P h Z)) rfl
 · exact L B (P c453 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s165 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c453 : Q y true 0 1 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c412 : N (Q y true 0 1 2 5)) (c437 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c454 | c454
 ·
  exact s166 y B H c411 c453 c454 c1 c320 c412 c437
 rcases em (Q y false 0 2 4 5) with c458 | c458
 ·
  rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c411 (M c458 (P h Z))) rfl
  · exact L B (M c453 (P h Z)) rfl
  · exact L B (P c411 (M c458 (P h Z))) rfl
  · exact L B (M c453 (P h Z)) rfl
  · exact L B (M c458 (P h Z)) rfl
  · exact L B (M c453 (P h Z)) rfl
  · exact L B (M c458 (P h Z)) rfl
  · exact L B (M c453 (P h Z)) rfl
  · exact G B (P c453 (P c458 (P h Z))) rfl
  · exact L B (K 2 c411 (P h Z)) rfl
 rcases em (Q y false 0 3 4 5) with c459 | c459
 ·
  exact s168 y B H c411 c453 c459 c1 c320 c412 c437 c454 c458
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c411 (P c453 (P h Z))) rfl
 · exact L B (M c453 (P h Z)) rfl
 · exact absurd h c459
 · exact L B (M c453 (P h Z)) rfl
 · exact absurd h c458
 · exact L B (M c453 (P h Z)) rfl
 · exact absurd h c454
 · exact L B (M c453 (P h Z)) rfl
 · exact L B (P c411 (M h Z)) rfl
 · exact L B (P c411 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s164 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c437 : Q y false 0 1 3 5) (c438 : Q y false 2 3 4 5) (c449 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c412 : N (Q y true 0 1 2 5)) (_c439 : N (Q y true 0 1 2 6)) (_c443 : N (Q y true 0 1 3 6)) (_c447 : N (Q y false 0 2 3 6)) : False := by
 rcases em (Q y true 1 2 3 7) with c450 | c450
 ·
  rcases H.h13457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (K 2 c411 (P c438 (P c450 (P h Z)))) rfl
  · exact L B (M c450 (P h Z)) rfl
  · exact L B (K 2 c411 (P c438 (P c450 (P h Z)))) rfl
  · exact L B (M c450 (P h Z)) rfl
  · exact L B (K 2 c437 (M c438 (P c450 (P h Z)))) rfl
  · exact L B (M c450 (P h Z)) rfl
  · exact L B (P c437 (M c438 (P c450 (P h Z)))) rfl
  · exact L B (M c450 (P h Z)) rfl
  · exact L B (P c438 (M h Z)) rfl
  · exact L B (P c438 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c449 (P h Z)) rfl
 · exact absurd h c450
 · exact L B (P c449 (P h Z)) rfl
 · exact L B (P c449 (M h Z)) rfl
 · exact L B (P c449 (P h Z)) rfl
 · exact L B (P c449 (M h Z)) rfl
 · exact L B (P c449 (P h Z)) rfl
 · exact L B (P c449 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s163 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (_c411 : Q y false 0 1 2 4) (c437 : Q y false 0 1 3 5) (_c438 : Q y false 2 3 4 5) (c447 : Q y false 0 2 3 6) (_c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) (_c412 : N (Q y true 0 1 2 5)) (_c439 : N (Q y true 0 1 2 6)) (_c443 : N (Q y true 0 1 3 6)) : False := by
 rcases em (Q y false 2 4 5 6) with c448 | c448
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c448 (P h Z)) rfl
  · exact L B (P c448 (P h Z)) rfl
  · exact L B (P c447 (M h Z)) rfl
  · exact L B (P c447 (P h Z)) rfl
  · exact L B (P c447 (M h Z)) rfl
  · exact L B (P c447 (P h Z)) rfl
  · exact L B (P c447 (M h Z)) rfl
  · exact L B (P c447 (P h Z)) rfl
  · exact L B (P c447 (M h Z)) rfl
  · exact L B (P c447 (P h Z)) rfl
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c448
 · exact L B (K 2 c447 (P h Z)) rfl
 · exact L B (P c447 (M h Z)) rfl
 · exact L B (P c447 (P h Z)) rfl
 · exact L B (P c447 (M h Z)) rfl
 · exact L B (P c447 (P h Z)) rfl
 · exact L B (P c447 (M h Z)) rfl
 · exact L B (P c447 (P h Z)) rfl
 · exact L B (P c437 (M h Z)) rfl
 · exact L B (P c437 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s162 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c437 : Q y false 0 1 3 5) (c438 : Q y false 2 3 4 5) (c443 : Q y true 0 1 3 6) (_c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) (c412 : N (Q y true 0 1 2 5)) (c439 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 0 1 5 6) with c444 | c444
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c437 (M c444 (P h Z))) rfl
  · exact L B (M c443 (P h Z)) rfl
  · exact L B (P c444 (M h Z)) rfl
  · exact L B (M c443 (P h Z)) rfl
  · exact L B (P c444 (M h Z)) rfl
  · exact L B (M c443 (P h Z)) rfl
  · exact L B (P c438 (P c444 (M h Z))) rfl
  · exact L B (M c443 (P h Z)) rfl
  · exact L B (P c438 (M h Z)) rfl
  · exact L B (M c443 (P h Z)) rfl
 rcases em (Q y false 0 2 5 6) with c445 | c445
 ·
  rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c411 (M c445 (P h Z))) rfl
  · exact L B (M c443 (P h Z)) rfl
  · exact L B (P c411 (M c445 (P h Z))) rfl
  · exact L B (M c443 (P h Z)) rfl
  · exact L B (M c445 (P h Z)) rfl
  · exact L B (P c445 (P h Z)) rfl
  · exact L B (M c445 (P h Z)) rfl
  · exact L B (M c443 (P h Z)) rfl
  · exact G B (P c443 (P c445 (P h Z))) rfl
  · exact L B (K 2 c437 (P h Z)) rfl
 rcases em (Q y false 1 2 5 6) with c446 | c446
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c444 (P c411 (P h Z)) (M c437 (P c438 (M h Z))) rfl rfl
  · exact L B (P c446 (P h Z)) rfl
  · exact L B (P c446 (M h Z)) rfl
  · exact L B (P c446 (P h Z)) rfl
  · exact absurd h c445
  · exact L B (P c446 (P h Z)) rfl
  · exact L B (P c437 (P c446 (M h Z))) rfl
  · exact L B (P c411 (P c438 (P c446 (P h Z)))) rfl
  · exact L B (P c437 (M h Z)) rfl
  · exact L B (P c411 (P c438 (P h Z))) rfl
 rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c446
 · exact L B (M c443 (P h Z)) rfl
 · exact absurd h c445
 · exact L B (M c443 (P h Z)) rfl
 · exact absurd h c444
 · exact L B (M c443 (P h Z)) rfl
 · exact L B (M c411 (P h Z)) rfl
 · exact absurd h c439
 · exact L B (M c437 (P h Z)) rfl
 · exact absurd h c412

set_option maxHeartbeats 4000000 in
lemma s161 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c437 : Q y false 0 1 3 5) (c438 : Q y false 2 3 4 5) (c439 : Q y true 0 1 2 6) (_c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) (_c412 : N (Q y true 0 1 2 5)) : False := by
 rcases em (Q y false 0 1 4 6) with c440 | c440
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c437 (P c440 (M h Z))) rfl
  · exact L B (M c439 (P h Z)) rfl
  · exact L B (P c440 (M h Z)) rfl
  · exact L B (M c439 (P h Z)) rfl
  · exact L B (P c440 (M h Z)) rfl
  · exact L B (P c440 (P h Z)) rfl
  · exact L B (P c440 (M h Z)) rfl
  · exact L B (P c440 (P h Z)) rfl
  · exact L B (P c437 (M h Z)) rfl
  · exact L B (P c411 (P c438 (P h Z))) rfl
 rcases em (Q y false 0 3 4 6) with c441 | c441
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c438 (P h Z)) rfl
  · exact L B (M c439 (P h Z)) rfl
  · exact L B (M c441 (P h Z)) rfl
  · exact L B (P c441 (P h Z)) rfl
  · exact L B (M c441 (P h Z)) rfl
  · exact L B (P c411 (P c441 (P h Z))) rfl
  · exact L B (M c441 (P h Z)) rfl
  · exact L B (P c411 (P c441 (P h Z))) rfl
  · exact G B (P c439 (P c441 (P h Z))) rfl
  · exact L B (K 2 c437 (P h Z)) rfl
 rcases em (Q y false 1 3 4 6) with c442 | c442
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c440 (P c437 (P h Z)) (M c411 (M c438 (M h Z))) rfl rfl
  · exact L B (M c439 (P h Z)) rfl
  · exact L B (P c442 (M h Z)) rfl
  · exact L B (M c439 (P h Z)) rfl
  · exact L B (P c442 (M h Z)) rfl
  · exact L B (M c439 (P h Z)) rfl
  · exact absurd h c441
  · exact L B (M c439 (P h Z)) rfl
  · exact L B (P c438 (M h Z)) rfl
  · exact L B (P c438 (P h Z)) rfl
 rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c442
 · exact L B (M c439 (P h Z)) rfl
 · exact absurd h c441
 · exact L B (M c439 (P h Z)) rfl
 · exact absurd h c440
 · exact L B (M c439 (P h Z)) rfl
 · exact L B (M c437 (P h Z)) rfl
 · exact L B (M c439 (P h Z)) rfl
 · exact L B (P c411 (M h Z)) rfl
 · exact L B (P c411 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s160 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c432 : Q y false 1 3 4 5) (c433 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c413 : N (Q y false 0 1 3 5)) (c423 : N (Q y false 0 1 4 5)) (_c431 : N (Q y false 0 3 4 5)) : False := by
 rcases em (Q y true 0 1 3 6) with c434 | c434
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c411 (M c433 (P h Z))) rfl
  · exact L B (M c434 (P h Z)) rfl
  · exact L B (P c411 (M c433 (P h Z))) rfl
  · exact L B (M c434 (P h Z)) rfl
  · exact L B (P c411 (M c433 (P h Z))) rfl
  · exact L B (M c434 (P h Z)) rfl
  · exact L B (M c433 (P h Z)) rfl
  · exact L B (M c434 (P h Z)) rfl
  · exact LN B 1 1 c423 (P c433 (M h Z)) (M c433 (P h Z)) rfl rfl
  · exact L B (P c433 (P h Z)) rfl
 rcases em (Q y true 0 2 3 6) with c435 | c435
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c412 (P c435 (P h Z))) rfl
  · exact L B (M c435 (P h Z)) rfl
  · exact L B (M c412 (P c435 (P h Z))) rfl
  · exact L B (M c435 (P h Z)) rfl
  · exact L B (M c412 (P c435 (P h Z))) rfl
  · exact L B (M c435 (P h Z)) rfl
  · exact L B (P c435 (P h Z)) rfl
  · exact L B (M c435 (P h Z)) rfl
  · exact LN B 1 1 c423 (P c433 (M h Z)) (M c433 (P h Z)) rfl rfl
  · exact L B (P c433 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c436 | c436
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c432 (P h Z)) rfl
  · exact L B (P c436 (M h Z)) rfl
  · exact L B (M c433 (P h Z)) rfl
  · exact L B (P c436 (M h Z)) rfl
  · exact L B (M c433 (P h Z)) rfl
  · exact L B (P c436 (M h Z)) rfl
  · exact L B (M c433 (P h Z)) rfl
  · exact L B (P c412 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c433 (P h Z)) rfl
 · exact absurd h c436
 · exact L B (M c433 (P h Z)) rfl
 · exact absurd h c435
 · exact L B (M c433 (P h Z)) rfl
 · exact absurd h c434
 · exact L B (M c433 (P h Z)) rfl
 · exact L B (P c412 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s159 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c432 : Q y false 1 3 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c413 : N (Q y false 0 1 3 5)) (c423 : N (Q y false 0 1 4 5)) (c431 : N (Q y false 0 3 4 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c433 | c433
 ·
  exact s160 y B H c411 c412 c432 c433 c1 c320 c413 c423 c431
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c432 (P h Z)) rfl
 · exact L B (M c412 (P h Z)) rfl
 · exact absurd h c431
 · exact L B (M c412 (P h Z)) rfl
 · exact L B (P c411 (P c432 (M h Z))) rfl
 · exact L B (M c412 (P h Z)) rfl
 · exact absurd h c433
 · exact L B (M c412 (P h Z)) rfl
 · exact L B (P c411 (M h Z)) rfl
 · exact L B (M c412 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s158 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c423 : Q y false 0 1 4 5) (_c424 : Q y false 0 2 3 5) (c425 : Q y false 1 2 3 4) (c427 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c413 : N (Q y false 0 1 3 5)) (_c426 : N (Q y true 0 1 3 6)) : False := by
 rcases em (Q y true 1 2 3 7) with c428 | c428
 ·
  rcases H.h02457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c412 (P c425 (P c427 (P h Z)))) rfl
  · exact L B (M c428 (P h Z)) rfl
  · exact L B (P c412 (M c428 (M h Z))) rfl
  · exact L B (M c423 (M c428 (P h Z))) rfl
  · exact L B (M c412 (P c428 (P h Z))) rfl
  · exact L B (M c423 (M c428 (P h Z))) rfl
  · exact L B (M c412 (M c423 (P c427 (P h Z)))) rfl
  · exact L B (P c411 (P c428 (M h Z))) rfl
  · exact L B (P c423 (M h Z)) rfl
  · exact L B (M c412 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c427 (P h Z)) rfl
 · exact absurd h c428
 · exact L B (P c427 (P h Z)) rfl
 · exact L B (P c427 (M h Z)) rfl
 · exact L B (P c427 (P h Z)) rfl
 · exact L B (P c427 (M h Z)) rfl
 · exact L B (P c427 (P h Z)) rfl
 · exact L B (P c427 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s157 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c423 : Q y false 0 1 4 5) (c424 : Q y false 0 2 3 5) (c425 : Q y false 1 2 3 4) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c413 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y true 0 1 3 6) with c426 | c426
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c412 (P c426 (P h Z))) rfl
  · exact L B (M c426 (P h Z)) rfl
  · exact L B (P c412 (P c423 (M c426 (M h Z)))) rfl
  · exact L B (M c426 (P h Z)) rfl
  · exact G B (P c425 (P c426 (P h Z))) rfl
  · exact L B (M c426 (P h Z)) rfl
  · exact L B (M c423 (M c425 (P h Z))) rfl
  · exact L B (M c426 (P h Z)) rfl
  · exact L B (P c411 (M h Z)) rfl
  · exact L B (M c412 (P h Z)) rfl
 rcases em (Q y true 0 2 3 6) with c427 | c427
 ·
  exact s158 y B H c411 c412 c423 c424 c425 c427 c1 c320 c413 c426
 rcases em (Q y true 1 2 3 6) with c429 | c429
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c425 (P h Z)) rfl
  · exact L B (P c429 (M h Z)) rfl
  · exact L B (M c423 (M c425 (P h Z))) rfl
  · exact L B (P c429 (M h Z)) rfl
  · exact L B (M c423 (P h Z)) rfl
  · exact L B (P c429 (M h Z)) rfl
  · exact L B (M c423 (P h Z)) rfl
  · exact L B (P c412 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c425 (P h Z)) rfl
 · exact absurd h c429
 · exact L B (M c423 (M c425 (P h Z))) rfl
 · exact absurd h c427
 · exact L B (M c423 (P h Z)) rfl
 · exact absurd h c426
 · exact L B (M c423 (P h Z)) rfl
 · exact L B (P c412 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s156 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c423 : Q y false 0 1 4 5) (c424 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c413 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 1 2 3 4) with c425 | c425
 ·
  exact s157 y B H c411 c412 c423 c424 c425 c1 c320 c413
 rcases em (Q y false 1 3 4 5) with c430 | c430
 ·
  rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c424 (P h Z)) rfl
  · exact LN B 1 1 c425 (P c411 (M c423 (P c430 Z))) (P c423 (M c424 Z)) rfl rfl
  · exact L B (M c424 (P h Z)) rfl
  · exact LN B 1 1 c425 (M c423 (P c424 Z)) (P c423 (M c424 Z)) rfl rfl
  · exact L B (M c423 (P h Z)) rfl
  · exact LN B 1 1 c425 (M c423 (P c424 Z)) (P c423 (M c424 Z)) rfl rfl
  · exact L B (M c423 (P h Z)) rfl
  · exact L B (P c412 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c411 (M c423 (P h Z))) rfl
 · exact L B (M c412 (P h Z)) rfl
 · exact absurd h c430
 · exact L B (M c412 (P h Z)) rfl
 · exact L B (P c411 (M c424 (P h Z))) rfl
 · exact L B (M c412 (P h Z)) rfl
 · exact L B (M c424 (P h Z)) rfl
 · exact L B (M c412 (P h Z)) rfl
 · exact absurd h c425
 · exact L B (M c412 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s155 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c423 : Q y false 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (c413 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c424 | c424
 ·
  exact s156 y B H c411 c412 c423 c424 c1 c320 c413
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c411 (M c423 (P h Z))) rfl
 · exact L B (M c412 (P h Z)) rfl
 · exact L B (P c423 (M h Z)) rfl
 · exact L B (M c412 (P h Z)) rfl
 · exact L B (P c423 (M h Z)) rfl
 · exact L B (M c412 (P h Z)) rfl
 · exact absurd h c424
 · exact L B (M c412 (P h Z)) rfl
 · exact L B (P c411 (M h Z)) rfl
 · exact L B (P c411 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s154 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c413 : Q y false 0 1 3 5) (c414 : Q y false 2 3 4 5) (c419 : Q y true 0 2 3 6) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) (_c415 : N (Q y true 0 1 3 6)) (_c417 : N (Q y false 0 2 3 6)) : False := by
 rcases em (Q y true 1 2 3 7) with c420 | c420
 ·
  rcases H.h01457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (K 2 c413 (M c414 (P c420 (P h Z)))) rfl
  · exact L B (M c420 (P h Z)) rfl
  · exact L B (P c412 (M c420 (M h Z))) rfl
  · exact L B (M c413 (M c420 (P h Z))) rfl
  · exact L B (P c413 (P c420 (P h Z))) rfl
  · exact L B (P c411 (P c414 (P c420 (M h Z)))) rfl
  · exact L B (P c411 (P c420 (P h Z))) rfl
  · exact L B (P c413 (P c420 (M h Z))) rfl
  · exact L B (P c413 (M h Z)) rfl
  · exact L B (M c412 (P h Z)) rfl
 rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c419 (P h Z)) rfl
 · exact absurd h c420
 · exact L B (P c419 (P h Z)) rfl
 · exact L B (P c419 (M h Z)) rfl
 · exact L B (P c419 (P h Z)) rfl
 · exact L B (P c419 (M h Z)) rfl
 · exact L B (P c419 (P h Z)) rfl
 · exact L B (P c419 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s153 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (_c412 : Q y true 0 1 2 5) (c413 : Q y false 0 1 3 5) (c414 : Q y false 2 3 4 5) (c417 : Q y false 0 2 3 6) (_c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) (_c415 : N (Q y true 0 1 3 6)) : False := by
 rcases em (Q y false 2 4 5 6) with c418 | c418
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c418 (P h Z)) rfl
  · exact L B (P c418 (P h Z)) rfl
  · exact L B (P c417 (M h Z)) rfl
  · exact L B (P c417 (P h Z)) rfl
  · exact L B (P c417 (M h Z)) rfl
  · exact L B (P c417 (P h Z)) rfl
  · exact L B (P c417 (M h Z)) rfl
  · exact L B (P c417 (P h Z)) rfl
  · exact L B (P c417 (M h Z)) rfl
  · exact L B (P c417 (P h Z)) rfl
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c418
 · exact L B (K 2 c417 (P h Z)) rfl
 · exact L B (P c417 (M h Z)) rfl
 · exact L B (P c417 (P h Z)) rfl
 · exact L B (P c417 (M h Z)) rfl
 · exact L B (P c417 (P h Z)) rfl
 · exact L B (P c417 (M h Z)) rfl
 · exact L B (P c417 (P h Z)) rfl
 · exact L B (P c411 (P c414 (M h Z))) rfl
 · exact L B (P c413 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s152 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c413 : Q y false 0 1 3 5) (c414 : Q y false 2 3 4 5) (c415 : Q y true 0 1 3 6) (_c1 : N (Q y false 0 1 2 3)) (_c320 : N (Q y true 0 1 2 3)) : False := by
 rcases em (Q y false 0 1 4 6) with c416 | c416
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c411 (P c416 (M h Z))) rfl
  · exact L B (M c415 (P h Z)) rfl
  · exact L B (P c412 (M c415 (M h Z))) rfl
  · exact L B (M c415 (P h Z)) rfl
  · exact L B (P c416 (M h Z)) rfl
  · exact L B (P c416 (P h Z)) rfl
  · exact L B (P c416 (M h Z)) rfl
  · exact L B (M c415 (P h Z)) rfl
  · exact L B (P c411 (P c414 (M h Z))) rfl
  · exact L B (P c413 (P h Z)) rfl
 rcases H.h01456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c412 (M c415 (M h Z))) rfl
 · exact L B (M c415 (P h Z)) rfl
 · exact L B (P c412 (M c415 (M h Z))) rfl
 · exact L B (M c415 (P h Z)) rfl
 · exact L B (P c411 (P c412 (M c415 (M h Z)))) rfl
 · exact L B (M c415 (P h Z)) rfl
 · exact absurd h c416
 · exact L B (M c415 (P h Z)) rfl
 · exact L B (P c413 (M h Z)) rfl
 · exact L B (M c412 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s151 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c413 : Q y false 0 1 3 5) (c414 : Q y false 2 3 4 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) : False := by
 rcases em (Q y true 0 1 3 6) with c415 | c415
 ·
  exact s152 y B H c411 c412 c413 c414 c415 c1 c320
 rcases em (Q y false 0 2 3 6) with c417 | c417
 ·
  exact s153 y B H c411 c412 c413 c414 c417 c1 c320 c415
 rcases em (Q y true 0 2 3 6) with c419 | c419
 ·
  exact s154 y B H c411 c412 c413 c414 c419 c1 c320 c415 c417
 rcases em (Q y false 1 2 3 6) with c421 | c421
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c414 (P h Z)) rfl
  · exact L B (K 2 c421 (P h Z)) rfl
  · exact L B (P c421 (M h Z)) rfl
  · exact L B (P c421 (P h Z)) rfl
  · exact L B (P c421 (M h Z)) rfl
  · exact L B (P c421 (P h Z)) rfl
  · exact absurd h c417
  · exact absurd h c419
  · exact L B (P c411 (M h Z)) rfl
  · exact L B (P c411 (P h Z)) rfl
 rcases em (Q y true 1 2 3 6) with c422 | c422
 ·
  rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c422 (P h Z)) rfl
  · exact L B (P c422 (M h Z)) rfl
  · exact L B (P c422 (P h Z)) rfl
  · exact L B (P c422 (M h Z)) rfl
  · exact L B (M c411 (M c414 (P h Z))) rfl
  · exact L B (P c422 (M h Z)) rfl
  · exact L B (M c413 (P h Z)) rfl
  · exact L B (P c422 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c421
 · exact absurd h c422
 · exact absurd h c417
 · exact absurd h c419
 · exact L B (M c411 (M c414 (P h Z))) rfl
 · exact absurd h c415
 · exact L B (M c413 (P h Z)) rfl
 · exact L B (P c412 (M h Z)) rfl
 · exact absurd h c1
 · exact absurd h c320

set_option maxHeartbeats 4000000 in
lemma s150 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c411 : Q y false 0 1 2 4) (c412 : Q y true 0 1 2 5) (c413 : Q y false 0 1 3 5) (c1 : N (Q y false 0 1 2 3)) (c320 : N (Q y true 0 1 2 3)) : False := by
 rcases em (Q y false 2 3 4 5) with c414 | c414
 ·
  exact s151 y B H c411 c412 c413 c414 c1 c320
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c414
 · exact L B (K 2 c413 (P h Z)) rfl
 · exact L B (P c413 (M h Z)) rfl
 · exact L B (P c413 (P h Z)) rfl
 · exact L B (P c413 (M h Z)) rfl
 · exact L B (M c412 (P h Z)) rfl
 · exact L B (P c413 (M h Z)) rfl
 · exact L B (P c413 (P h Z)) rfl
 · exact L B (P c411 (M h Z)) rfl
 · exact L B (P c411 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s149 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c384 : Q y false 1 2 4 5) (c393 : Q y true 0 1 3 4) (_c401 : Q y true 0 2 3 5) (c405 : Q y true 0 2 4 6) (_c1 : N (Q y false 0 1 2 3)) (c321 : N (Q y false 0 1 4 5)) (_c369 : N (Q y true 0 1 4 5)) (_c378 : N (Q y false 0 2 4 5)) (_c382 : N (Q y true 0 2 4 5)) (_c385 : N (Q y false 0 1 3 4)) (_c394 : N (Q y false 0 2 3 4)) (_c402 : N (Q y false 0 1 4 6)) (_c403 : N (Q y true 0 1 4 6)) (_c404 : N (Q y false 0 2 4 6)) : False := by
 rcases em (Q y true 1 2 4 7) with c406 | c406
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c321 (P c320 (M c406 (M h Z))) (M c320 (P c406 (P h Z))) rfl rfl
  · exact L B (M c406 (P h Z)) rfl
  · exact L B (P c320 (M c406 (M h Z))) rfl
  · exact L B (P c320 (M c406 (P h Z))) rfl
  · exact L B (P c384 (P c405 (P h Z))) rfl
  · exact L B (P c384 (P c405 (M h Z))) rfl
  · exact L B (P c405 (P h Z)) rfl
  · exact L B (P c405 (M h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c384 (P h Z)) rfl
 · exact absurd h c406
 · exact L B (P c405 (P h Z)) rfl
 · exact L B (P c405 (M h Z)) rfl
 · exact L B (P c405 (P h Z)) rfl
 · exact L B (P c405 (M h Z)) rfl
 · exact L B (P c405 (P h Z)) rfl
 · exact L B (P c405 (M h Z)) rfl
 · exact L B (P c393 (P h Z)) rfl
 · exact L B (P c393 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s148 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c384 : Q y false 1 2 4 5) (c393 : Q y true 0 1 3 4) (c401 : Q y true 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c321 : N (Q y false 0 1 4 5)) (c369 : N (Q y true 0 1 4 5)) (c378 : N (Q y false 0 2 4 5)) (c382 : N (Q y true 0 2 4 5)) (c385 : N (Q y false 0 1 3 4)) (c394 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y false 0 1 4 6) with c402 | c402
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (P c402 (M h Z))) rfl
  · exact L B (K 2 c402 (P h Z)) rfl
  · exact L B (P c402 (M h Z)) rfl
  · exact L B (P c402 (P h Z)) rfl
  · exact L B (P c402 (M h Z)) rfl
  · exact L B (P c402 (P h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
 rcases em (Q y true 0 1 4 6) with c403 | c403
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (M c403 (M h Z))) rfl
  · exact L B (M c403 (P h Z)) rfl
  · exact L B (P c320 (M c403 (M h Z))) rfl
  · exact L B (M c403 (P h Z)) rfl
  · exact LN B 1 1 c394 (P c384 (M c393 (P c403 (P h Z)))) (M c384 (P c393 (M c403 (M h Z)))) rfl rfl
  · exact L B (M c403 (P h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
 rcases em (Q y false 0 2 4 6) with c404 | c404
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c384 (P c393 (P c404 (M h Z)))) rfl
  · exact L B (P c404 (P h Z)) rfl
  · exact L B (P c404 (M h Z)) rfl
  · exact L B (P c404 (P h Z)) rfl
  · exact L B (P c404 (M h Z)) rfl
  · exact L B (P c404 (P h Z)) rfl
  · exact L B (P c404 (M h Z)) rfl
  · exact L B (P c404 (P h Z)) rfl
  · exact L B (P c384 (M h Z)) rfl
  · exact L B (P c384 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c405 | c405
 ·
  exact s149 y B H c320 c384 c393 c401 c405 c1 c321 c369 c378 c382 c385 c394 c402 c403 c404
 rcases em (Q y true 1 2 4 6) with c407 | c407
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c384 (P h Z)) rfl
  · exact L B (P c407 (M h Z)) rfl
  · exact L B (P c407 (P h Z)) rfl
  · exact L B (P c407 (M h Z)) rfl
  · exact L B (P c407 (K 2 h Z)) rfl
  · exact L B (P c407 (M h Z)) rfl
  · exact L B (P c407 (K 2 h Z)) rfl
  · exact L B (P c407 (M h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c384 (P h Z)) rfl
 · exact absurd h c407
 · exact absurd h c404
 · exact absurd h c405
 · exact absurd h c402
 · exact absurd h c403
 · exact L B (P c393 (P h Z)) rfl
 · exact L B (P c393 (M h Z)) rfl
 · exact L B (P c393 (P h Z)) rfl
 · exact L B (P c393 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s147 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (_c320 : Q y true 0 1 2 3) (c384 : Q y false 1 2 4 5) (c393 : Q y true 0 1 3 4) (c394 : Q y false 0 2 3 4) (c398 : Q y true 0 2 4 6) (_c1 : N (Q y false 0 1 2 3)) (c321 : N (Q y false 0 1 4 5)) (_c369 : N (Q y true 0 1 4 5)) (_c378 : N (Q y false 0 2 4 5)) (_c382 : N (Q y true 0 2 4 5)) (_c385 : N (Q y false 0 1 3 4)) (_c395 : N (Q y false 0 1 4 6)) (_c396 : N (Q y true 0 1 4 6)) (_c397 : N (Q y false 0 2 4 6)) : False := by
 rcases em (Q y true 1 2 4 7) with c399 | c399
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c384 (M c393 (M c394 (P c398 (P h Z))))) rfl
  · exact L B (M c399 (P h Z)) rfl
  · exact L B (P c384 (M c393 (M c394 (P c398 (P h Z))))) rfl
  · exact LN B 1 1 c321 (M c399 (P h Z)) (P c399 (M h Z)) rfl rfl
  · exact L B (P c384 (P c398 (P h Z))) rfl
  · exact L B (P c384 (P c398 (M h Z))) rfl
  · exact L B (P c398 (P h Z)) rfl
  · exact L B (P c398 (M h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c398 (P h Z)) rfl
 · exact absurd h c399
 · exact L B (P c398 (P h Z)) rfl
 · exact L B (P c398 (M h Z)) rfl
 · exact L B (P c398 (P h Z)) rfl
 · exact L B (P c398 (M h Z)) rfl
 · exact L B (P c398 (P h Z)) rfl
 · exact L B (P c398 (M h Z)) rfl
 · exact L B (P c393 (P h Z)) rfl
 · exact L B (P c393 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s146 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c384 : Q y false 1 2 4 5) (c393 : Q y true 0 1 3 4) (c394 : Q y false 0 2 3 4) (c1 : N (Q y false 0 1 2 3)) (c321 : N (Q y false 0 1 4 5)) (c369 : N (Q y true 0 1 4 5)) (c378 : N (Q y false 0 2 4 5)) (c382 : N (Q y true 0 2 4 5)) (c385 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y false 0 1 4 6) with c395 | c395
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (P c395 (M h Z))) rfl
  · exact L B (K 2 c395 (P h Z)) rfl
  · exact L B (P c395 (M h Z)) rfl
  · exact L B (P c395 (P h Z)) rfl
  · exact L B (P c395 (M h Z)) rfl
  · exact L B (P c395 (P h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
 rcases em (Q y true 0 1 4 6) with c396 | c396
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c393 (M c396 (M h Z))) rfl
  · exact L B (M c396 (P h Z)) rfl
  · exact L B (P c393 (M c396 (M h Z))) rfl
  · exact L B (M c396 (P h Z)) rfl
  · exact L B (P c320 (M c396 (M h Z))) rfl
  · exact L B (M c396 (P h Z)) rfl
  · exact L B (P c320 (M c396 (M h Z))) rfl
  · exact L B (M c396 (P h Z)) rfl
  · exact L B (P c384 (M h Z)) rfl
  · exact L B (P c384 (P h Z)) rfl
 rcases em (Q y false 0 2 4 6) with c397 | c397
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c384 (P h Z)) rfl
  · exact LN B 1 1 c396 (P c393 (P c394 (M c397 Z))) (M c393 (M c394 (P c397 Z))) rfl rfl
  · exact L B (M c397 (P h Z)) rfl
  · exact LN B 1 1 c396 (P c393 (P c394 (M c397 Z))) (M c393 (M c394 (P c397 Z))) rfl rfl
  · exact L B (M c397 (P h Z)) rfl
  · exact L B (P c393 (P c394 (M c397 (M h Z)))) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c398 | c398
 ·
  exact s147 y B H c320 c384 c393 c394 c398 c1 c321 c369 c378 c382 c385 c395 c396 c397
 rcases em (Q y true 1 2 4 6) with c400 | c400
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c400 (P h Z)) rfl
  · exact L B (P c400 (M h Z)) rfl
  · exact L B (P c400 (P h Z)) rfl
  · exact L B (P c400 (M h Z)) rfl
  · exact L B (P c400 (K 2 h Z)) rfl
  · exact L B (P c400 (M h Z)) rfl
  · exact L B (P c400 (K 2 h Z)) rfl
  · exact L B (P c400 (M h Z)) rfl
  · exact L B (P c393 (P h Z)) rfl
  · exact L B (P c393 (M h Z)) rfl
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c384 (P h Z)) rfl
 · exact absurd h c400
 · exact absurd h c397
 · exact absurd h c398
 · exact absurd h c395
 · exact absurd h c396
 · exact L B (M c394 (P h Z)) rfl
 · exact L B (P c393 (M h Z)) rfl
 · exact L B (P c393 (P h Z)) rfl
 · exact L B (P c393 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s145 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c384 : Q y false 1 2 4 5) (c385 : Q y false 0 1 3 4) (_c386 : Q y false 0 2 3 5) (c388 : Q y true 0 1 4 6) (_c1 : N (Q y false 0 1 2 3)) (c321 : N (Q y false 0 1 4 5)) (_c369 : N (Q y true 0 1 4 5)) (c378 : N (Q y false 0 2 4 5)) (c382 : N (Q y true 0 2 4 5)) (_c387 : N (Q y false 0 1 4 6)) : False := by
 rcases em (Q y false 0 2 4 6) with c389 | c389
 ·
  rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (M c388 (M h Z))) rfl
  · exact L B (M c388 (P h Z)) rfl
  · exact L B (P c320 (M c388 (M h Z))) rfl
  · exact L B (M c388 (P h Z)) rfl
  · exact LN B 1 1 c321 (P c389 (M h Z)) (M c389 (P h Z)) rfl rfl
  · exact L B (M c388 (P h Z)) rfl
  · exact L B (M c384 (P h Z)) rfl
  · exact L B (P c385 (P c389 (P h Z))) rfl
  · exact L B (M c384 (P h Z)) rfl
  · exact L B (P c384 (P c385 (P h Z))) rfl
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c320 (M c388 (M h Z))) rfl
 · exact L B (M c388 (P h Z)) rfl
 · exact L B (P c320 (M c388 (M h Z))) rfl
 · exact L B (M c388 (P h Z)) rfl
 · exact G B (P c384 (P c388 (P h Z))) rfl
 · exact L B (M c388 (P h Z)) rfl
 · exact absurd h c389
 · exact L B (M c388 (P h Z)) rfl
 · exact absurd h c378
 · exact absurd h c382

set_option maxHeartbeats 4000000 in
lemma s144 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c384 : Q y false 1 2 4 5) (c385 : Q y false 0 1 3 4) (c386 : Q y false 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c321 : N (Q y false 0 1 4 5)) (c369 : N (Q y true 0 1 4 5)) (c378 : N (Q y false 0 2 4 5)) (c382 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y false 0 1 4 6) with c387 | c387
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c385 (P c387 (M h Z))) rfl
  · exact L B (K 2 c387 (P h Z)) rfl
  · exact L B (P c387 (M h Z)) rfl
  · exact L B (P c387 (P h Z)) rfl
  · exact L B (P c387 (M h Z)) rfl
  · exact L B (P c387 (P h Z)) rfl
  · exact L B (P c387 (M h Z)) rfl
  · exact L B (P c387 (P h Z)) rfl
  · exact absurd h c378
  · exact absurd h c382
 rcases em (Q y true 0 1 4 6) with c388 | c388
 ·
  exact s145 y B H c320 c384 c385 c386 c388 c1 c321 c369 c378 c382 c387
 rcases em (Q y false 0 2 4 6) with c390 | c390
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c388 (P c320 (M h Z)) (M c320 (P h Z)) rfl rfl
  · exact L B (P c390 (P h Z)) rfl
  · exact L B (P c320 (P c390 (M h Z))) rfl
  · exact L B (P c390 (P h Z)) rfl
  · exact L B (M c384 (P h Z)) rfl
  · exact L B (P c390 (P h Z)) rfl
  · exact L B (M c384 (P h Z)) rfl
  · exact L B (P c385 (P c390 (P h Z))) rfl
  · exact LN B 1 1 c321 (P c384 (P c385 (M h Z))) (M c384 (M c385 (P h Z))) rfl rfl
  · exact L B (P c385 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c391 | c391
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c384 (P c385 (P c391 (P h Z)))) rfl
  · exact L B (M c391 (P h Z)) rfl
  · exact L B (P c320 (M c391 (M h Z))) rfl
  · exact L B (M c391 (P h Z)) rfl
  · exact L B (P c320 (M c391 (M h Z))) rfl
  · exact L B (M c391 (P h Z)) rfl
  · exact L B (P c320 (M c391 (M h Z))) rfl
  · exact L B (M c391 (P h Z)) rfl
  · exact L B (P c384 (M h Z)) rfl
  · exact L B (P c384 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c392 | c392
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c384 (P h Z)) rfl
  · exact L B (P c392 (M h Z)) rfl
  · exact L B (P c392 (P h Z)) rfl
  · exact L B (P c392 (M h Z)) rfl
  · exact L B (P c392 (K 2 h Z)) rfl
  · exact L B (P c392 (M h Z)) rfl
  · exact L B (P c392 (K 2 h Z)) rfl
  · exact L B (P c392 (M h Z)) rfl
  · exact L B (M c385 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c384 (P h Z)) rfl
 · exact absurd h c392
 · exact absurd h c390
 · exact absurd h c391
 · exact absurd h c387
 · exact absurd h c388
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s143 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c384 : Q y false 1 2 4 5) (c385 : Q y false 0 1 3 4) (c1 : N (Q y false 0 1 2 3)) (c321 : N (Q y false 0 1 4 5)) (c369 : N (Q y true 0 1 4 5)) (c378 : N (Q y false 0 2 4 5)) (c382 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c386 | c386
 ·
  exact s144 y B H c320 c384 c385 c386 c1 c321 c369 c378 c382
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c386 (P c384 (P c385 Z)) (M c384 (M c385 Z)) rfl rfl
 · exact L B (P c384 (P h Z)) rfl
 · exact L B (P c384 (M h Z)) rfl
 · exact L B (P c384 (P h Z)) rfl
 · exact absurd h c378
 · exact absurd h c382
 · exact absurd h c386
 · exact L B (P c384 (P c385 (P h Z))) rfl
 · exact L B (P c385 (M h Z)) rfl
 · exact L B (P c385 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s142 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c382 : Q y true 0 2 4 5) (_c1 : N (Q y false 0 1 2 3)) (_c321 : N (Q y false 0 1 4 5)) (_c369 : N (Q y true 0 1 4 5)) (_c378 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y true 1 2 4 6) with c383 | c383
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c383 (P h Z)) rfl
  · exact L B (P c383 (M h Z)) rfl
  · exact L B (P c382 (P h Z)) rfl
  · exact L B (P c382 (M h Z)) rfl
  · exact L B (P c382 (P h Z)) rfl
  · exact L B (P c382 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c382 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c382 (P h Z)) rfl
 · exact absurd h c383
 · exact L B (P c382 (P h Z)) rfl
 · exact L B (P c382 (M h Z)) rfl
 · exact L B (P c382 (P h Z)) rfl
 · exact L B (P c382 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s141 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c378 : Q y false 0 2 4 5) (_c1 : N (Q y false 0 1 2 3)) (_c321 : N (Q y false 0 1 4 5)) (c369 : N (Q y true 0 1 4 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c379 | c379
 ·
  rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (M c379 (M h Z))) rfl
  · exact L B (M c379 (P h Z)) rfl
  · exact L B (P c320 (M c379 (M h Z))) rfl
  · exact L B (M c379 (P h Z)) rfl
  · exact G B (P c378 (P c379 (P h Z))) rfl
  · exact L B (M c379 (P h Z)) rfl
  · exact L B (M c378 (P h Z)) rfl
  · exact L B (M c379 (P h Z)) rfl
  · exact L B (M c378 (P h Z)) rfl
  · exact L B (M c379 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c380 | c380
 ·
  rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (M c378 (M c380 (M h Z)))) rfl
  · exact L B (M c380 (P h Z)) rfl
  · exact L B (P c320 (M c380 (M h Z))) rfl
  · exact L B (M c380 (P h Z)) rfl
  · exact LN B 1 1 c369 (P c380 (P h Z)) (M c380 (M h Z)) rfl rfl
  · exact L B (M c380 (P h Z)) rfl
  · exact L B (M c378 (P h Z)) rfl
  · exact L B (M c380 (P h Z)) rfl
  · exact L B (M c378 (P h Z)) rfl
  · exact L B (P c378 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c381 | c381
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c378 (P h Z)) rfl
  · exact L B (P c381 (M h Z)) rfl
  · exact L B (P c381 (P h Z)) rfl
  · exact L B (P c381 (M h Z)) rfl
  · exact L B (M c378 (P h Z)) rfl
  · exact L B (P c381 (M h Z)) rfl
  · exact L B (P c381 (K 2 h Z)) rfl
  · exact L B (P c381 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c378 (P h Z)) rfl
 · exact absurd h c381
 · exact L B (M c378 (P h Z)) rfl
 · exact absurd h c380
 · exact L B (M c378 (P h Z)) rfl
 · exact absurd h c379
 · exact L B (M c378 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s140 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c369 : Q y true 0 1 4 5) (c375 : Q y false 1 2 4 6) (_c1 : N (Q y false 0 1 2 3)) (_c321 : N (Q y false 0 1 4 5)) (c370 : N (Q y false 0 2 4 6)) (c373 : N (Q y true 0 2 4 6)) : False := by
 rcases em (Q y false 2 4 5 6) with c376 | c376
 ·
  rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c375 (M h Z)) rfl
  · exact L B (P c375 (P h Z)) rfl
  · exact L B (P c375 (M h Z)) rfl
  · exact L B (P c375 (P h Z)) rfl
  · exact L B (P c320 (M c376 (P h Z))) rfl
  · exact L B (P c320 (M c376 (M h Z))) rfl
  · exact L B (P c369 (P h Z)) rfl
  · exact L B (P c369 (M h Z)) rfl
  · exact L B (P c369 (P h Z)) rfl
  · exact L B (P c369 (M h Z)) rfl
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c376
 · exact L B (K 2 c375 (P h Z)) rfl
 · exact L B (P c375 (M h Z)) rfl
 · exact L B (P c375 (P h Z)) rfl
 · exact L B (P c375 (M h Z)) rfl
 · exact L B (P c375 (P h Z)) rfl
 · exact absurd h c370
 · exact absurd h c373
 · exact L B (P c375 (M h Z)) rfl
 · exact L B (P c375 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s139 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c369 : Q y true 0 1 4 5) (c373 : Q y true 0 2 4 6) (_c1 : N (Q y false 0 1 2 3)) (_c321 : N (Q y false 0 1 4 5)) (_c370 : N (Q y false 0 2 4 6)) : False := by
 rcases em (Q y true 1 2 4 7) with c374 | c374
 ·
  rcases H.h02367 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (P c373 (M c374 (M h Z)))) rfl
  · exact L B (M c374 (P h Z)) rfl
  · exact L B (P c369 (M c374 (M h Z))) rfl
  · exact L B (P c369 (M c374 (P h Z))) rfl
  · exact L B (P c369 (M c374 (M h Z))) rfl
  · exact L B (P c369 (M c374 (P h Z))) rfl
  · exact L B (P c373 (P h Z)) rfl
  · exact L B (P c373 (M h Z)) rfl
  · exact L B (P c373 (P h Z)) rfl
  · exact L B (P c373 (M h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c373 (P h Z)) rfl
 · exact absurd h c374
 · exact L B (P c373 (P h Z)) rfl
 · exact L B (P c373 (M h Z)) rfl
 · exact L B (P c369 (P h Z)) rfl
 · exact L B (P c369 (M h Z)) rfl
 · exact L B (P c369 (P h Z)) rfl
 · exact L B (P c369 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s138 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c369 : Q y true 0 1 4 5) (c370 : Q y false 0 2 4 6) (c371 : Q y false 3 4 5 6) (_c1 : N (Q y false 0 1 2 3)) (_c321 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y true 1 2 3 6) with c372 | c372
 ·
  rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c371 (M h Z)) rfl
  · exact L B (M c372 (P h Z)) rfl
  · exact L B (K 2 c370 (P c372 (M h Z))) rfl
  · exact L B (M c372 (P h Z)) rfl
  · exact L B (P c369 (P c370 (M h Z))) rfl
  · exact L B (P c370 (P h Z)) rfl
  · exact L B (M c370 (P h Z)) rfl
  · exact L B (P c370 (P h Z)) rfl
  · exact L B (K 2 c370 (M c371 (P c372 (M h Z)))) rfl
  · exact L B (M c372 (P h Z)) rfl
 rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c320 (P c369 (P h Z))) rfl
 · exact L B (P c370 (P h Z)) rfl
 · exact L B (P c320 (P c370 (M h Z))) rfl
 · exact L B (P c370 (P h Z)) rfl
 · exact L B (M c370 (P h Z)) rfl
 · exact L B (P c370 (P h Z)) rfl
 · exact L B (M c370 (P h Z)) rfl
 · exact absurd h c372
 · exact L B (P c369 (P c370 (M c371 (M h Z)))) rfl
 · exact L B (P c370 (M c371 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s137 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c369 : Q y true 0 1 4 5) (c370 : Q y false 0 2 4 6) (c1 : N (Q y false 0 1 2 3)) (c321 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y false 3 4 5 6) with c371 | c371
 ·
  exact s138 y B H c320 c369 c370 c371 c1 c321
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c371
 · exact L B (P c370 (P h Z)) rfl
 · exact L B (P c370 (M h Z)) rfl
 · exact L B (P c370 (P h Z)) rfl
 · exact L B (P c370 (M h Z)) rfl
 · exact L B (P c370 (P h Z)) rfl
 · exact L B (P c370 (M h Z)) rfl
 · exact L B (P c370 (P h Z)) rfl
 · exact L B (P c370 (M h Z)) rfl
 · exact L B (P c370 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s136 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c369 : Q y true 0 1 4 5) (c1 : N (Q y false 0 1 2 3)) (c321 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y false 0 2 4 6) with c370 | c370
 ·
  exact s137 y B H c320 c369 c370 c1 c321
 rcases em (Q y true 0 2 4 6) with c373 | c373
 ·
  exact s139 y B H c320 c369 c373 c1 c321 c370
 rcases em (Q y false 1 2 4 6) with c375 | c375
 ·
  exact s140 y B H c320 c369 c375 c1 c321 c370 c373
 rcases em (Q y true 1 2 4 6) with c377 | c377
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c377 (P h Z)) rfl
  · exact L B (P c377 (M h Z)) rfl
  · exact L B (P c377 (P h Z)) rfl
  · exact L B (P c377 (M h Z)) rfl
  · exact L B (P c377 (K 2 h Z)) rfl
  · exact L B (P c377 (M h Z)) rfl
  · exact L B (P c377 (K 2 h Z)) rfl
  · exact L B (P c377 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c375
 · exact absurd h c377
 · exact absurd h c370
 · exact absurd h c373
 · exact L B (P c369 (P h Z)) rfl
 · exact L B (P c369 (M h Z)) rfl
 · exact L B (P c369 (P h Z)) rfl
 · exact L B (P c369 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s135 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (_c362 : Q y true 0 2 3 5) (c363 : Q y false 1 2 4 5) (c366 : Q y true 0 2 4 6) (_c1 : N (Q y false 0 1 2 3)) (_c322 : N (Q y false 0 2 3 4)) (_c329 : N (Q y true 0 2 3 4)) (_c337 : N (Q y false 0 2 3 5)) (_c364 : N (Q y true 0 1 4 6)) (_c365 : N (Q y false 0 2 4 6)) : False := by
 rcases em (Q y true 1 2 4 7) with c367 | c367
 ·
  rcases H.h02367 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (P c366 (M c367 (M h Z)))) rfl
  · exact L B (M c367 (P h Z)) rfl
  · exact L B (P c366 (M c367 (M h Z))) rfl
  · exact L B (P c366 (M c367 (P h Z))) rfl
  · exact L B (P c366 (M c367 (M h Z))) rfl
  · exact L B (P c366 (M c367 (P h Z))) rfl
  · exact L B (P c366 (P h Z)) rfl
  · exact L B (P c366 (M h Z)) rfl
  · exact L B (P c366 (P h Z)) rfl
  · exact L B (P c366 (M h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c363 (P h Z)) rfl
 · exact absurd h c367
 · exact L B (P c366 (P h Z)) rfl
 · exact L B (P c366 (M h Z)) rfl
 · exact L B (M c321 (P h Z)) rfl
 · exact L B (P c366 (M h Z)) rfl
 · exact L B (P c366 (P h Z)) rfl
 · exact L B (P c366 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s134 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c362 : Q y true 0 2 3 5) (c363 : Q y false 1 2 4 5) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) (c337 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c364 | c364
 ·
  rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c322 (P c321 (M c362 (M c363 (P c364 (P h Z))))) (M c321 (P c362 (P c363 (M c364 (M h Z))))) rfl rfl
  · exact L B (M c364 (P h Z)) rfl
  · exact G B (P c363 (P c364 (P h Z))) rfl
  · exact L B (M c364 (P h Z)) rfl
  · exact LN B 1 1 c322 (M c362 (P c364 (P h Z))) (P c362 (M c364 (M h Z))) rfl rfl
  · exact L B (M c364 (P h Z)) rfl
  · exact L B (P c362 (P h Z)) rfl
  · exact L B (P c362 (M h Z)) rfl
  · exact L B (P c362 (P h Z)) rfl
  · exact L B (P c362 (M h Z)) rfl
 rcases em (Q y false 0 2 4 6) with c365 | c365
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c362 (P c365 (M h Z))) rfl
  · exact L B (P c365 (P h Z)) rfl
  · exact L B (P c365 (M h Z)) rfl
  · exact L B (P c365 (P h Z)) rfl
  · exact L B (P c365 (M h Z)) rfl
  · exact L B (P c365 (P h Z)) rfl
  · exact L B (P c365 (M h Z)) rfl
  · exact L B (P c365 (P h Z)) rfl
  · exact L B (P c363 (M h Z)) rfl
  · exact L B (P c363 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c366 | c366
 ·
  exact s135 y B H c320 c321 c362 c363 c366 c1 c322 c329 c337 c364 c365
 rcases em (Q y true 1 2 4 6) with c368 | c368
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c363 (P h Z)) rfl
  · exact L B (P c368 (M h Z)) rfl
  · exact L B (P c368 (P h Z)) rfl
  · exact L B (P c368 (M h Z)) rfl
  · exact L B (M c321 (P h Z)) rfl
  · exact L B (P c368 (M h Z)) rfl
  · exact L B (P c368 (K 2 h Z)) rfl
  · exact L B (P c368 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c363 (P h Z)) rfl
 · exact absurd h c368
 · exact absurd h c365
 · exact absurd h c366
 · exact L B (M c321 (P h Z)) rfl
 · exact absurd h c364
 · exact L B (P c362 (P h Z)) rfl
 · exact L B (P c362 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s133 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c362 : Q y true 0 2 3 5) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) (c337 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y false 1 2 4 5) with c363 | c363
 ·
  exact s134 y B H c320 c321 c362 c363 c1 c322 c329 c337
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c320 (P c321 (M h Z))) rfl
 · exact L B (P c321 (P h Z)) rfl
 · exact L B (P c320 (P c321 (M h Z))) rfl
 · exact L B (P c321 (P h Z)) rfl
 · exact absurd h c363
 · exact L B (P c321 (P h Z)) rfl
 · exact L B (P c362 (P h Z)) rfl
 · exact L B (M c362 (P h Z)) rfl
 · exact L B (P c321 (P c362 (P h Z))) rfl
 · exact L B (M c362 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s132 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (_c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (_c345 : Q y false 0 2 4 6) (c346 : Q y false 3 4 5 6) (c353 : Q y true 0 1 3 4) (c354 : Q y true 0 1 5 6) (c355 : Q y false 1 2 5 6) (_c1 : N (Q y false 0 1 2 3)) (_c322 : N (Q y false 0 2 3 4)) (_c329 : N (Q y true 0 2 3 4)) (_c339 : N (Q y true 0 1 4 6)) (_c347 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y true 0 2 4 7) with c356 | c356
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (M c356 (M h Z))) rfl
  · exact L B (M c356 (P h Z)) rfl
  · exact L B (P c320 (M c356 (M h Z))) rfl
  · exact L B (M c356 (P h Z)) rfl
  · exact L B (P c354 (P h Z)) rfl
  · exact L B (P c354 (M h Z)) rfl
  · exact L B (P c354 (P h Z)) rfl
  · exact L B (P c353 (M h Z)) rfl
  · exact L B (M c338 (P c354 (P c355 (P h Z)))) rfl
  · exact L B (P c353 (M h Z)) rfl
 rcases em (Q y true 1 2 4 7) with c357 | c357
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c321 (P c353 (M c355 (M c357 (M h Z))))) rfl
  · exact L B (M c357 (P h Z)) rfl
  · exact L B (P c353 (M c357 (M h Z))) rfl
  · exact L B (P c354 (M c357 (P h Z))) rfl
  · exact L B (P c354 (M c357 (M h Z))) rfl
  · exact L B (P c338 (P c353 (M c355 (M c357 (P h Z))))) rfl
  · exact L B (P c320 (M c357 (M h Z))) rfl
  · exact L B (P c320 (M c357 (P h Z))) rfl
  · exact L B (P c355 (M h Z)) rfl
  · exact L B (P c338 (P c346 (P h Z))) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c355 (P h Z)) rfl
 · exact absurd h c357
 · exact L B (M c321 (M c355 (P h Z))) rfl
 · exact absurd h c356
 · exact L B (P c338 (P c353 (M c355 (P h Z)))) rfl
 · exact L B (P c354 (M h Z)) rfl
 · exact L B (P c353 (P h Z)) rfl
 · exact L B (P c353 (M h Z)) rfl
 · exact L B (P c353 (P h Z)) rfl
 · exact L B (P c353 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s131 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (c345 : Q y false 0 2 4 6) (c346 : Q y false 3 4 5 6) (c353 : Q y true 0 1 3 4) (c354 : Q y true 0 1 5 6) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) (c339 : N (Q y true 0 1 4 6)) (c347 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y false 1 2 5 6) with c355 | c355
 ·
  exact s132 y B H c320 c321 c337 c338 c345 c346 c353 c354 c355 c1 c322 c329 c339 c347
 rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c346 (M h Z)) rfl
 · exact L B (P c346 (P h Z)) rfl
 · exact L B (P c346 (M h Z)) rfl
 · exact L B (M c354 (P h Z)) rfl
 · exact absurd h c355
 · exact L B (P c338 (P c346 (P h Z))) rfl
 · exact L B (M c338 (M c346 (P h Z))) rfl
 · exact L B (P c321 (P c338 (P c346 (P h Z)))) rfl
 · exact L B (P c321 (P c338 (P c346 (P c354 (M h Z))))) rfl
 · exact L B (P c321 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s130 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (c345 : Q y false 0 2 4 6) (c346 : Q y false 3 4 5 6) (c353 : Q y true 0 1 3 4) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) (c339 : N (Q y true 0 1 4 6)) (c347 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y true 0 1 5 6) with c354 | c354
 ·
  exact s131 y B H c320 c321 c337 c338 c345 c346 c353 c354 c1 c322 c329 c339 c347
 rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c338 (P c346 (M h Z))) rfl
 · exact L B (P c338 (P c346 (P h Z))) rfl
 · exact L B (P c338 (P c346 (M h Z))) rfl
 · exact L B (P c338 (P c346 (P h Z))) rfl
 · exact L B (M c346 (P c353 (P h Z))) rfl
 · exact absurd h c354
 · exact L B (P c353 (P h Z)) rfl
 · exact L B (P c353 (M h Z)) rfl
 · exact L B (M c321 (P h Z)) rfl
 · exact L B (P c353 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s129 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (_c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (_c345 : Q y false 0 2 4 6) (c346 : Q y false 3 4 5 6) (c347 : Q y false 0 1 3 4) (c348 : Q y false 0 1 5 6) (c349 : Q y false 1 2 5 6) (_c1 : N (Q y false 0 1 2 3)) (_c322 : N (Q y false 0 2 3 4)) (_c329 : N (Q y true 0 2 3 4)) (c339 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y true 0 1 4 7) with c350 | c350
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c349 (P h Z)) rfl
  · exact L B (M c350 (P h Z)) rfl
  · exact G B (P c321 (P c338 (P c347 (P c350 (P h Z))))) rfl
  · exact L B (M c350 (P h Z)) rfl
  · exact L B (M c348 (P h Z)) rfl
  · exact L B (M c350 (P h Z)) rfl
  · exact L B (P c350 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases em (Q y true 0 2 4 7) with c351 | c351
 ·
  rcases H.h01267 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c339 (P c351 (P h Z)) (M c351 (M h Z)) rfl rfl
  · exact L B (M c351 (P h Z)) rfl
  · exact G B (P c321 (P c338 (P c347 (P c349 (P c351 (P h Z)))))) rfl
  · exact L B (M c351 (P h Z)) rfl
  · exact LN B 1 1 c339 (P c338 (P c346 (M c348 (P c351 (P h Z))))) (M c338 (P c347 (M c351 (M h Z)))) rfl rfl
  · exact L B (M c349 (M c351 (P h Z))) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases em (Q y true 1 2 4 7) with c352 | c352
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c339 (P c321 (P c338 (P c352 (P h Z)))) (M c321 (M c338 (M c352 (M h Z)))) rfl rfl
  · exact L B (M c352 (P h Z)) rfl
  · exact L B (P c320 (M c352 (M h Z))) rfl
  · exact L B (M c321 (M c352 (P h Z))) rfl
  · exact L B (P c320 (M c352 (M h Z))) rfl
  · exact L B (P c320 (M c352 (P h Z))) rfl
  · exact L B (P c320 (M c352 (M h Z))) rfl
  · exact L B (M c321 (M c352 (P h Z))) rfl
  · exact L B (P c349 (M h Z)) rfl
  · exact L B (P c349 (P h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c338 (P c347 (M c348 (P h Z)))) rfl
 · exact absurd h c352
 · exact L B (M c321 (M c338 (M c346 (P h Z)))) rfl
 · exact absurd h c351
 · exact L B (M c346 (M c347 (P h Z))) rfl
 · exact absurd h c350
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s128 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (c345 : Q y false 0 2 4 6) (c346 : Q y false 3 4 5 6) (c347 : Q y false 0 1 3 4) (c348 : Q y false 0 1 5 6) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) (c339 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 1 2 5 6) with c349 | c349
 ·
  exact s129 y B H c320 c321 c337 c338 c345 c346 c347 c348 c349 c1 c322 c329 c339
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c320 (P c346 (P c347 (M h Z)))) rfl
 · exact L B (P c348 (P h Z)) rfl
 · exact L B (P c338 (P c346 (M h Z))) rfl
 · exact L B (P c348 (P h Z)) rfl
 · exact absurd h c349
 · exact L B (P c346 (P c347 (P h Z))) rfl
 · exact L B (M c338 (P h Z)) rfl
 · exact L B (P c345 (M c346 (P c348 (P h Z)))) rfl
 · exact L B (M c338 (P h Z)) rfl
 · exact L B (P c321 (P c347 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s127 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (c345 : Q y false 0 2 4 6) (c346 : Q y false 3 4 5 6) (c347 : Q y false 0 1 3 4) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) (c339 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 0 1 5 6) with c348 | c348
 ·
  exact s128 y B H c320 c321 c337 c338 c345 c346 c347 c348 c1 c322 c329 c339
 rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c338 (P c346 (M h Z))) rfl
 · exact L B (P c346 (P c347 (P h Z))) rfl
 · exact L B (P c346 (P c347 (M h Z))) rfl
 · exact L B (P c338 (P c346 (P h Z))) rfl
 · exact absurd h c348
 · exact L B (P c346 (P c347 (P h Z))) rfl
 · exact L B (M c347 (P h Z)) rfl
 · exact G B (P c321 (P c346 (P h Z))) rfl
 · exact L B (M c347 (P h Z)) rfl
 · exact LN B 1 1 c348 (P c346 (P c347 Z)) (M c346 (M c347 Z)) rfl rfl

set_option maxHeartbeats 4000000 in
lemma s126 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (c345 : Q y false 0 2 4 6) (c346 : Q y false 3 4 5 6) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) (c339 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 0 1 3 4) with c347 | c347
 ·
  exact s127 y B H c320 c321 c337 c338 c345 c346 c347 c1 c322 c329 c339
 rcases em (Q y true 0 1 3 4) with c353 | c353
 ·
  exact s130 y B H c320 c321 c337 c338 c345 c346 c353 c1 c322 c329 c339 c347
 rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c320 (P c321 (P c338 (P c346 (M h Z))))) rfl
 · exact L B (P c321 (P c338 (P c346 (P h Z)))) rfl
 · exact L B (P c321 (P c338 (P c346 (M h Z)))) rfl
 · exact L B (P c321 (P c338 (P c346 (P h Z)))) rfl
 · exact L B (M c321 (P h Z)) rfl
 · exact absurd h c339
 · exact L B (M c321 (P h Z)) rfl
 · exact G B (P c337 (P c338 (P c346 (P h Z)))) rfl
 · exact absurd h c347
 · exact absurd h c353

set_option maxHeartbeats 4000000 in
lemma s125 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (_c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (c339 : Q y true 0 1 4 6) (c340 : Q y false 3 4 5 6) (_c341 : Q y false 0 2 4 6) (c342 : Q y false 1 2 5 6) (_c1 : N (Q y false 0 1 2 3)) (_c322 : N (Q y false 0 2 3 4)) (_c329 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y true 0 2 4 7) with c343 | c343
 ·
  rcases H.h03457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c340 (P h Z)) rfl
  · exact L B (M c343 (P h Z)) rfl
  · exact L B (P c320 (M c343 (M h Z))) rfl
  · exact L B (M c343 (P h Z)) rfl
  · exact L B (P c320 (M c343 (M h Z))) rfl
  · exact L B (M c343 (P h Z)) rfl
  · exact L B (P c320 (M c343 (M h Z))) rfl
  · exact L B (M c343 (P h Z)) rfl
  · exact L B (P c321 (M h Z)) rfl
  · exact L B (P c321 (P h Z)) rfl
 rcases em (Q y true 1 2 4 7) with c344 | c344
 ·
  rcases H.h04567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (K 2 c321 (P c342 (P c344 (P h Z)))) rfl
  · exact L B (M c344 (P h Z)) rfl
  · exact L B (P c320 (M c344 (M h Z))) rfl
  · exact L B (M c321 (M c344 (P h Z))) rfl
  · exact L B (P c320 (M c344 (M h Z))) rfl
  · exact L B (M c321 (M c344 (P h Z))) rfl
  · exact L B (P c320 (M c344 (M h Z))) rfl
  · exact L B (M c321 (M c344 (P h Z))) rfl
  · exact L B (P c342 (M h Z)) rfl
  · exact L B (P c342 (P h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c338 (M c340 (P h Z))) rfl
 · exact absurd h c344
 · exact L B (M c321 (M c342 (P h Z))) rfl
 · exact absurd h c343
 · exact L B (M c321 (P h Z)) rfl
 · exact L B (P c339 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s124 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (c339 : Q y true 0 1 4 6) (c340 : Q y false 3 4 5 6) (c341 : Q y false 0 2 4 6) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y false 1 2 5 6) with c342 | c342
 ·
  exact s125 y B H c320 c321 c337 c338 c339 c340 c341 c342 c1 c322 c329
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c320 (M c339 (M h Z))) rfl
 · exact L B (P c338 (P c340 (P h Z))) rfl
 · exact L B (P c338 (P c340 (M h Z))) rfl
 · exact L B (P c338 (P c340 (P h Z))) rfl
 · exact absurd h c342
 · exact L B (P c338 (P c340 (P h Z))) rfl
 · exact L B (M c338 (P h Z)) rfl
 · exact L B (M c339 (M c340 (P c341 (P h Z)))) rfl
 · exact L B (M c338 (P h Z)) rfl
 · exact L B (M c340 (P c341 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s123 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (c339 : Q y true 0 1 4 6) (c340 : Q y false 3 4 5 6) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y false 0 2 4 6) with c341 | c341
 ·
  exact s124 y B H c320 c321 c337 c338 c339 c340 c341 c1 c322 c329
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c340 (M h Z)) rfl
 · exact L B (P c340 (P h Z)) rfl
 · exact L B (P c340 (M h Z)) rfl
 · exact L B (P c340 (P h Z)) rfl
 · exact L B (P c338 (P c340 (M h Z))) rfl
 · exact L B (P c338 (P c340 (P h Z))) rfl
 · exact absurd h c341
 · exact L B (P c321 (P c338 (P c340 (P h Z)))) rfl
 · exact L B (P c321 (M h Z)) rfl
 · exact L B (P c321 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s122 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c337 : Q y false 0 2 3 5) (c338 : Q y false 1 2 3 4) (c339 : Q y true 0 1 4 6) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) (c329 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y false 3 4 5 6) with c340 | c340
 ·
  exact s123 y B H c320 c321 c337 c338 c339 c340 c1 c322 c329
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c340
 · exact L B (M c339 (P h Z)) rfl
 · exact L B (P c320 (M c339 (M h Z))) rfl
 · exact L B (M c339 (P h Z)) rfl
 · exact L B (P c320 (M c339 (M h Z))) rfl
 · exact L B (M c339 (P h Z)) rfl
 · exact L B (P c320 (M c339 (M h Z))) rfl
 · exact L B (M c339 (P h Z)) rfl
 · exact L B (P c321 (M h Z)) rfl
 · exact L B (P c321 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s121 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c329 : Q y true 0 2 3 4) (c330 : Q y true 1 2 3 5) (_c1 : N (Q y false 0 1 2 3)) (_c322 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y true 0 1 4 6) with c331 | c331
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c329 (M c331 (M h Z))) rfl
  · exact L B (M c331 (P h Z)) rfl
  · exact L B (P c330 (M c331 (M h Z))) rfl
  · exact L B (M c331 (P h Z)) rfl
  · exact L B (P c320 (M c331 (M h Z))) rfl
  · exact L B (M c331 (P h Z)) rfl
  · exact L B (P c320 (M c331 (M h Z))) rfl
  · exact L B (M c331 (P h Z)) rfl
  · exact L B (P c321 (M h Z)) rfl
  · exact L B (P c321 (P h Z)) rfl
 rcases em (Q y false 0 2 4 6) with c332 | c332
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (P c332 (M h Z))) rfl
  · exact L B (P c332 (P h Z)) rfl
  · exact L B (P c332 (M h Z)) rfl
  · exact L B (P c332 (P h Z)) rfl
  · exact L B (M c321 (P h Z)) rfl
  · exact absurd h c331
  · exact L B (P c329 (P h Z)) rfl
  · exact L B (P c329 (M h Z)) rfl
  · exact L B (P c329 (P h Z)) rfl
  · exact L B (P c329 (M h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c333 | c333
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c329 (M c333 (M h Z))) rfl
  · exact L B (M c333 (P h Z)) rfl
  · exact L B (P c329 (M c333 (M h Z))) rfl
  · exact L B (M c333 (P h Z)) rfl
  · exact L B (P c320 (M c333 (M h Z))) rfl
  · exact L B (M c333 (P h Z)) rfl
  · exact L B (P c320 (M c333 (M h Z))) rfl
  · exact L B (M c333 (P h Z)) rfl
  · exact L B (P c321 (M h Z)) rfl
  · exact L B (P c321 (P h Z)) rfl
 rcases em (Q y false 1 2 4 6) with c334 | c334
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c334 (M h Z)) rfl
  · exact L B (P c334 (P h Z)) rfl
  · exact L B (P c334 (M h Z)) rfl
  · exact L B (P c334 (P h Z)) rfl
  · exact L B (M c321 (P h Z)) rfl
  · exact absurd h c331
  · exact L B (M c321 (P h Z)) rfl
  · exact L B (P c329 (M h Z)) rfl
  · exact L B (P c330 (P c334 (P h Z))) rfl
  · exact L B (P c330 (P c334 (M h Z))) rfl
 rcases em (Q y true 1 2 4 6) with c335 | c335
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c335 (P h Z)) rfl
  · exact L B (P c335 (M h Z)) rfl
  · exact L B (P c335 (P h Z)) rfl
  · exact L B (P c335 (M h Z)) rfl
  · exact L B (M c321 (P h Z)) rfl
  · exact L B (P c335 (M h Z)) rfl
  · exact L B (P c335 (K 2 h Z)) rfl
  · exact L B (P c335 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c334
 · exact absurd h c335
 · exact absurd h c332
 · exact absurd h c333
 · exact L B (M c321 (P h Z)) rfl
 · exact absurd h c331
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c330 (M h Z)) rfl
 · exact L B (P c320 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s120 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c329 : Q y true 0 2 3 4) (c1 : N (Q y false 0 1 2 3)) (c322 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y true 1 2 3 5) with c330 | c330
 ·
  exact s121 y B H c320 c321 c329 c330 c1 c322
 rcases em (Q y false 1 2 4 5) with c336 | c336
 ·
  rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c336 (P h Z)) rfl
  · exact LN B 1 1 c330 (M c321 (P c329 Z)) (P c321 (M c329 Z)) rfl rfl
  · exact LN B 1 1 c330 (M c321 (P c329 Z)) (P c321 (M c329 Z)) rfl rfl
  · exact LN B 1 1 c330 (M c321 (P c329 Z)) (P c321 (M c329 Z)) rfl rfl
  · exact L B (M c321 (P h Z)) rfl
  · exact LN B 1 1 c330 (M c321 (P c329 Z)) (P c321 (M c329 Z)) rfl rfl
  · exact L B (P c329 (P h Z)) rfl
  · exact L B (P c329 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c320 (P c321 (M h Z))) rfl
 · exact L B (P c321 (P h Z)) rfl
 · exact L B (P c320 (P c321 (M h Z))) rfl
 · exact L B (P c321 (P h Z)) rfl
 · exact absurd h c336
 · exact L B (P c321 (P h Z)) rfl
 · exact L B (P c329 (P h Z)) rfl
 · exact absurd h c330
 · exact L B (P c329 (P h Z)) rfl
 · exact L B (M c329 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s119 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c322 : Q y false 0 2 3 4) (c323 : Q y false 1 2 4 5) (c326 : Q y true 0 2 4 6) (_c1 : N (Q y false 0 1 2 3)) (_c324 : N (Q y true 0 1 4 6)) (_c325 : N (Q y false 0 2 4 6)) : False := by
 rcases em (Q y true 1 2 4 7) with c327 | c327
 ·
  rcases H.h02367 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (P c326 (M c327 (M h Z)))) rfl
  · exact L B (M c327 (P h Z)) rfl
  · exact L B (P c326 (M c327 (M h Z))) rfl
  · exact L B (P c326 (M c327 (P h Z))) rfl
  · exact L B (P c326 (M c327 (M h Z))) rfl
  · exact L B (P c326 (M c327 (P h Z))) rfl
  · exact L B (P c326 (P h Z)) rfl
  · exact L B (P c326 (M h Z)) rfl
  · exact L B (P c326 (P h Z)) rfl
  · exact L B (P c326 (M h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c323 (P h Z)) rfl
 · exact absurd h c327
 · exact L B (P c326 (P h Z)) rfl
 · exact L B (P c326 (M h Z)) rfl
 · exact L B (M c321 (P h Z)) rfl
 · exact L B (P c326 (M h Z)) rfl
 · exact L B (P c326 (P h Z)) rfl
 · exact L B (P c326 (M h Z)) rfl
 · exact L B (M c322 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s118 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c322 : Q y false 0 2 3 4) (c323 : Q y false 1 2 4 5) (c1 : N (Q y false 0 1 2 3)) : False := by
 rcases em (Q y true 0 1 4 6) with c324 | c324
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact G B (P c322 (P c323 (P c324 (P h Z)))) rfl
  · exact L B (M c324 (P h Z)) rfl
  · exact L B (P c320 (M c324 (M h Z))) rfl
  · exact L B (M c324 (P h Z)) rfl
  · exact L B (P c320 (M c324 (M h Z))) rfl
  · exact L B (M c324 (P h Z)) rfl
  · exact L B (P c320 (M c324 (M h Z))) rfl
  · exact L B (M c324 (P h Z)) rfl
  · exact L B (P c321 (M h Z)) rfl
  · exact L B (P c323 (P h Z)) rfl
 rcases em (Q y false 0 2 4 6) with c325 | c325
 ·
  rcases H.h02356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c320 (M c323 (P c325 (M h Z)))) rfl
  · exact L B (P c325 (P h Z)) rfl
  · exact L B (P c325 (M h Z)) rfl
  · exact L B (P c325 (P h Z)) rfl
  · exact L B (P c325 (M h Z)) rfl
  · exact L B (P c325 (P h Z)) rfl
  · exact L B (M c322 (P h Z)) rfl
  · exact G B (P c321 (P c322 (P c323 (P c325 (P h Z))))) rfl
  · exact L B (M c322 (P h Z)) rfl
  · exact LN B 1 1 c324 (P c322 (P c323 (M c325 (P h Z)))) (M c322 (M c323 (P c325 (M h Z)))) rfl rfl
 rcases em (Q y true 0 2 4 6) with c326 | c326
 ·
  exact s119 y B H c320 c321 c322 c323 c326 c1 c324 c325
 rcases em (Q y true 1 2 4 6) with c328 | c328
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c323 (P h Z)) rfl
  · exact L B (P c328 (M h Z)) rfl
  · exact L B (P c328 (P h Z)) rfl
  · exact L B (P c328 (M h Z)) rfl
  · exact L B (M c321 (P h Z)) rfl
  · exact L B (P c328 (M h Z)) rfl
  · exact L B (P c328 (K 2 h Z)) rfl
  · exact L B (P c328 (M h Z)) rfl
  · exact L B (M c322 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c323 (P h Z)) rfl
 · exact absurd h c328
 · exact absurd h c325
 · exact absurd h c326
 · exact L B (M c321 (P h Z)) rfl
 · exact absurd h c324
 · exact L B (M c322 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl
 · exact L B (M c322 (P h Z)) rfl
 · exact L B (P c320 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s117 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c320 : Q y true 0 1 2 3) (c321 : Q y false 0 1 4 5) (c322 : Q y false 0 2 3 4) (c1 : N (Q y false 0 1 2 3)) : False := by
 rcases em (Q y false 1 2 4 5) with c323 | c323
 ·
  exact s118 y B H c320 c321 c322 c323 c1
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c320 (P c321 (M h Z))) rfl
 · exact L B (P c321 (P h Z)) rfl
 · exact L B (P c320 (P c321 (M h Z))) rfl
 · exact L B (P c321 (P h Z)) rfl
 · exact absurd h c323
 · exact L B (P c321 (P h Z)) rfl
 · exact L B (M c322 (P h Z)) rfl
 · exact L B (P c321 (P c322 (P h Z))) rfl
 · exact L B (M c322 (P h Z)) rfl
 · exact L B (P c322 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s116 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c304 : Q y true 0 1 3 4) (_c311 : Q y true 0 2 3 5) (c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (_c273 : N (Q y false 0 1 3 4)) (c305 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y false 0 1 4 6) with c312 | c312
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c1 (P c312 (M h Z))) rfl
  · exact L B (K 2 c312 (P h Z)) rfl
  · exact L B (P c312 (M h Z)) rfl
  · exact L B (P c312 (P h Z)) rfl
  · exact L B (P c312 (M h Z)) rfl
  · exact L B (P c312 (P h Z)) rfl
  · exact L B (M c312 (P h Z)) rfl
  · exact L B (P c304 (M h Z)) rfl
  · exact L B (P c304 (P h Z)) rfl
  · exact L B (P c304 (M h Z)) rfl
 rcases em (Q y true 0 1 4 6) with c313 | c313
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c304 (M c313 (M h Z))) rfl
  · exact L B (M c313 (P h Z)) rfl
  · exact L B (P c304 (M c313 (M h Z))) rfl
  · exact L B (M c313 (P h Z)) rfl
  · exact G B (P c272 (P c313 (P h Z))) rfl
  · exact L B (M c313 (P h Z)) rfl
  · exact LN B 1 1 c305 (M c304 (P c313 (P h Z))) (P c304 (M c313 (M h Z))) rfl rfl
  · exact L B (M c313 (P h Z)) rfl
  · exact absurd h c260
  · exact absurd h c270
 rcases em (Q y false 0 2 4 6) with c314 | c314
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c272 (P c304 (P c314 (M h Z)))) rfl
  · exact L B (P c314 (P h Z)) rfl
  · exact L B (P c314 (M h Z)) rfl
  · exact L B (P c314 (P h Z)) rfl
  · exact L B (P c314 (M h Z)) rfl
  · exact L B (P c314 (P h Z)) rfl
  · exact L B (P c314 (M h Z)) rfl
  · exact L B (P c314 (P h Z)) rfl
  · exact L B (P c272 (M h Z)) rfl
  · exact L B (P c272 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c315 | c315
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c315 (P h Z))) rfl
  · exact L B (M c315 (P h Z)) rfl
  · exact L B (P c1 (P c315 (P h Z))) rfl
  · exact L B (M c315 (P h Z)) rfl
  · exact L B (M c272 (P h Z)) rfl
  · exact L B (M c315 (P h Z)) rfl
  · exact L B (P c315 (P h Z)) rfl
  · exact L B (P c304 (P c315 (M h Z))) rfl
  · exact LN B 1 1 c245 (M c272 (P c304 (P h Z))) (P c272 (M c304 (M h Z))) rfl rfl
  · exact L B (M c304 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c316 | c316
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c272 (P h Z)) rfl
  · exact L B (P c316 (M h Z)) rfl
  · exact L B (P c316 (P h Z)) rfl
  · exact L B (P c316 (M h Z)) rfl
  · exact L B (P c316 (K 2 h Z)) rfl
  · exact L B (P c316 (M h Z)) rfl
  · exact L B (P c316 (K 2 h Z)) rfl
  · exact L B (P c316 (M h Z)) rfl
  · exact L B (P c304 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c272 (P h Z)) rfl
 · exact absurd h c316
 · exact absurd h c314
 · exact absurd h c315
 · exact absurd h c312
 · exact absurd h c313
 · exact L B (P c304 (P h Z)) rfl
 · exact L B (P c304 (M h Z)) rfl
 · exact L B (P c304 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s115 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c304 : Q y true 0 1 3 4) (c305 : Q y false 0 2 3 4) (c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c149 : N (Q y false 0 1 4 5)) (_c245 : N (Q y true 0 1 4 5)) (_c260 : N (Q y false 0 2 4 5)) (_c270 : N (Q y true 0 2 4 5)) (_c273 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y false 0 1 4 6) with c306 | c306
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c1 (P c306 (M h Z))) rfl
  · exact L B (K 2 c306 (P h Z)) rfl
  · exact L B (P c306 (M h Z)) rfl
  · exact L B (P c306 (P h Z)) rfl
  · exact L B (P c306 (M h Z)) rfl
  · exact L B (P c306 (P h Z)) rfl
  · exact L B (P c304 (P h Z)) rfl
  · exact L B (P c304 (M h Z)) rfl
  · exact L B (P c304 (P h Z)) rfl
  · exact L B (P c304 (M h Z)) rfl
 rcases em (Q y true 0 1 4 6) with c307 | c307
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c304 (M c307 (M h Z))) rfl
  · exact L B (M c307 (P h Z)) rfl
  · exact L B (P c304 (M c307 (M h Z))) rfl
  · exact L B (M c307 (P h Z)) rfl
  · exact L B (P c304 (P c305 (M c307 (M h Z)))) rfl
  · exact L B (M c307 (P h Z)) rfl
  · exact L B (P c304 (P c305 (M c307 (M h Z)))) rfl
  · exact L B (M c307 (P h Z)) rfl
  · exact L B (P c272 (M h Z)) rfl
  · exact L B (P c272 (P h Z)) rfl
 rcases em (Q y false 0 2 4 6) with c308 | c308
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c272 (P h Z)) rfl
  · exact LN B 1 1 c307 (P c304 (P c305 (M c308 Z))) (M c304 (M c305 (P c308 Z))) rfl rfl
  · exact L B (M c308 (P h Z)) rfl
  · exact LN B 1 1 c307 (P c304 (P c305 (M c308 Z))) (M c304 (M c305 (P c308 Z))) rfl rfl
  · exact L B (M c308 (P h Z)) rfl
  · exact L B (P c304 (P c305 (M c308 (M h Z)))) rfl
  · exact L B (P c304 (P h Z)) rfl
  · exact L B (P c304 (M h Z)) rfl
  · exact L B (P c304 (P h Z)) rfl
  · exact absurd h c2
 rcases em (Q y true 0 2 4 6) with c309 | c309
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c309 (P h Z))) rfl
  · exact L B (M c309 (P h Z)) rfl
  · exact L B (P c1 (P c309 (P h Z))) rfl
  · exact L B (M c309 (P h Z)) rfl
  · exact L B (P c309 (P h Z)) rfl
  · exact L B (M c309 (P h Z)) rfl
  · exact L B (P c309 (P h Z)) rfl
  · exact L B (P c304 (P c309 (M h Z))) rfl
  · exact L B (M c305 (P h Z)) rfl
  · exact L B (M c304 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c310 | c310
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c310 (P h Z)) rfl
  · exact L B (P c310 (M h Z)) rfl
  · exact L B (P c310 (P h Z)) rfl
  · exact L B (P c310 (M h Z)) rfl
  · exact L B (P c310 (K 2 h Z)) rfl
  · exact L B (P c310 (M h Z)) rfl
  · exact L B (P c310 (K 2 h Z)) rfl
  · exact L B (P c310 (M h Z)) rfl
  · exact L B (M c305 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c272 (P h Z)) rfl
 · exact absurd h c310
 · exact absurd h c308
 · exact absurd h c309
 · exact absurd h c306
 · exact absurd h c307
 · exact L B (P c304 (P h Z)) rfl
 · exact L B (P c304 (M h Z)) rfl
 · exact L B (P c304 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s114 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (_c274 : Q y false 0 2 3 5) (_c293 : Q y false 0 2 4 6) (c294 : Q y false 0 1 5 6) (c295 : Q y false 3 4 5 6) (_c296 : Q y false 1 3 4 6) (c297 : Q y false 2 3 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (_c260 : N (Q y false 0 2 4 5)) (_c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (_c284 : N (Q y false 0 1 4 6)) (c285 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y true 0 1 2 7) with c298 | c298
 ·
  rcases H.h12347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c294 (P h Z))) rfl
  · exact L B (M c298 (P h Z)) rfl
  · exact L B (M c272 (M c297 (P h Z))) rfl
  · exact L B (M c298 (P h Z)) rfl
  · exact L B (M c272 (P h Z)) rfl
  · exact L B (M c298 (P h Z)) rfl
  · exact L B (M c272 (P h Z)) rfl
  · exact L B (M c298 (P h Z)) rfl
  · exact LN B 1 1 c149 (P c272 (P c273 (M h Z))) (M c1 (M c272 (P c295 (M c297 (P h Z))))) rfl rfl
  · exact L B (P c273 (P h Z)) rfl
 rcases em (Q y true 0 1 4 7) with c299 | c299
 ·
  rcases H.h02347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c297 (P h Z)) rfl
  · exact L B (M c299 (P h Z)) rfl
  · exact LN B 1 1 c84 (M c272 (M c273 (P c299 (P h Z)))) (P c272 (P c294 (M c295 (M c299 (M h Z))))) rfl rfl
  · exact L B (M c299 (P h Z)) rfl
  · exact L B (M c1 (M c272 (M c297 (P h Z)))) rfl
  · exact L B (M c299 (P h Z)) rfl
  · exact L B (M c1 (M c272 (M c297 (P h Z)))) rfl
  · exact LN B 1 1 c149 (P c272 (P c294 (M c295 (M c299 (P h Z))))) (M c272 (M c273 (P c299 (M h Z)))) rfl rfl
  · exact L B (P c273 (M h Z)) rfl
  · exact L B (P c273 (P h Z)) rfl
 rcases em (Q y true 0 2 4 7) with c300 | c300
 ·
  rcases H.h01267 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c285 (P c300 (P h Z)) (M c300 (M h Z)) rfl rfl
  · exact L B (M c300 (P h Z)) rfl
  · exact LN B 1 1 c84 (M c1 (P c295 (P c300 (P h Z)))) (P c1 (P c273 (M c294 (M c300 (M h Z))))) rfl rfl
  · exact L B (M c300 (P h Z)) rfl
  · exact LN B 1 1 c2 (M c1 (P c272 (P c295 (P c300 (P h Z))))) (P c1 (M c272 (P c273 (M c294 (M c300 (M h Z)))))) rfl rfl
  · exact L B (M c272 (M c300 (P h Z))) rfl
  · exact L B (M c294 (P h Z)) rfl
  · exact absurd h c298
  · exact L B (M c294 (P h Z)) rfl
  · exact absurd h c275
 rcases em (Q y true 1 2 4 7) with c301 | c301
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c245 (P c1 (P c301 (P h Z))) (M c273 (M c295 (P c297 (M c301 (M h Z))))) rfl rfl
  · exact L B (M c301 (P h Z)) rfl
  · exact LN B 1 1 c285 (M c297 (P c301 (P h Z))) (M c1 (P c294 (M c301 (M h Z)))) rfl rfl
  · exact L B (M c1 (M c301 (P h Z))) rfl
  · exact L B (M c294 (P h Z)) rfl
  · exact L B (P c272 (P c301 (M h Z))) rfl
  · exact L B (M c273 (P h Z)) rfl
  · exact L B (P c301 (M h Z)) rfl
  · exact L B (M c273 (P h Z)) rfl
  · exact LN B 1 1 c285 (M c1 (P c273 (M c297 (P h Z)))) (P c1 (M c273 (P c297 (M h Z)))) rfl rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c272 (P h Z)) rfl
 · exact absurd h c301
 · exact L B (M c272 (M c294 (P h Z))) rfl
 · exact absurd h c300
 · exact L B (M c294 (P h Z)) rfl
 · exact absurd h c299
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c298
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s113 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c293 : Q y false 0 2 4 6) (c294 : Q y false 0 1 5 6) (c295 : Q y false 3 4 5 6) (c296 : Q y false 1 3 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (c284 : N (Q y false 0 1 4 6)) (c285 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 2 3 5 6) with c297 | c297
 ·
  exact s114 y B H c1 c272 c273 c274 c293 c294 c295 c296 c297 c2 c84 c149 c245 c260 c270 c275 c284 c285
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c297
 · exact L B (P c294 (P h Z)) rfl
 · exact L B (M c1 (P c273 (P c295 (M h Z)))) rfl
 · exact L B (P c273 (P c295 (P h Z))) rfl
 · exact LN B 1 1 c297 (M c1 (M c272 (P c293 Z))) (P c1 (M c273 (M c295 Z))) rfl rfl
 · exact L B (P c294 (P h Z)) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (P c272 (K 2 c294 (M c295 (P h Z)))) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (P c272 (P c273 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s112 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c293 : Q y false 0 2 4 6) (c294 : Q y false 0 1 5 6) (c295 : Q y false 3 4 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (c284 : N (Q y false 0 1 4 6)) (c285 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 1 3 4 6) with c296 | c296
 ·
  exact s113 y B H c1 c272 c273 c274 c293 c294 c295 c296 c2 c84 c149 c245 c260 c270 c275 c284 c285
 rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c294 (P h Z))) rfl
 · exact L B (P c272 (P c273 (P c295 (P h Z)))) rfl
 · exact absurd h c296
 · exact L B (P c272 (P c273 (P c295 (P h Z)))) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (P c272 (P c273 (P c295 (P h Z)))) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (P c272 (P c273 (P c294 (P h Z)))) rfl
 · exact LN B 1 1 c296 (M c1 (P c272 (P c273 (P c295 Z)))) (P c1 (M c272 (M c273 (M c295 Z)))) rfl rfl
 · exact L B (P c294 (M c295 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s111 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c293 : Q y false 0 2 4 6) (c294 : Q y false 0 1 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (c284 : N (Q y false 0 1 4 6)) (c285 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 3 4 5 6) with c295 | c295
 ·
  exact s112 y B H c1 c272 c273 c274 c293 c294 c295 c2 c84 c149 c245 c260 c270 c275 c284 c285
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c295
 · exact L B (P c294 (P h Z)) rfl
 · exact L B (P c294 (M h Z)) rfl
 · exact L B (P c294 (P h Z)) rfl
 · exact L B (P c294 (M h Z)) rfl
 · exact L B (P c294 (P h Z)) rfl
 · exact L B (P c272 (P c294 (M h Z))) rfl
 · exact L B (P c272 (P c294 (P h Z))) rfl
 · exact L B (P c272 (M h Z)) rfl
 · exact L B (P c272 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s110 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c293 : Q y false 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (c284 : N (Q y false 0 1 4 6)) (c285 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 0 1 5 6) with c294 | c294
 ·
  exact s111 y B H c1 c272 c273 c274 c293 c294 c2 c84 c149 c245 c260 c270 c275 c284 c285
 rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c294 (M c272 (P c293 Z)) (P c272 (M c293 Z)) rfl rfl
 · exact L B (P c293 (P h Z)) rfl
 · exact L B (P c293 (M h Z)) rfl
 · exact L B (P c293 (P h Z)) rfl
 · exact absurd h c294
 · exact L B (M c272 (P c293 (P h Z))) rfl
 · exact L B (M c273 (P h Z)) rfl
 · exact absurd h c275
 · exact L B (M c273 (P h Z)) rfl
 · exact absurd h c84

set_option maxHeartbeats 4000000 in
lemma s109 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (_c274 : Q y false 0 2 3 5) (c285 : Q y true 0 1 4 6) (_c286 : Q y false 0 2 4 6) (c287 : Q y false 0 1 5 6) (c288 : Q y false 3 4 5 6) (_c289 : Q y false 1 3 4 6) (c290 : Q y false 2 3 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (_c245 : N (Q y true 0 1 4 5)) (_c260 : N (Q y false 0 2 4 5)) (_c270 : N (Q y true 0 2 4 5)) (_c275 : N (Q y true 0 1 2 6)) (_c284 : N (Q y false 0 1 4 6)) : False := by
 rcases em (Q y true 0 2 4 7) with c291 | c291
 ·
  rcases H.h01367 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c285 (M c291 (M h Z))) rfl
  · exact L B (M c291 (P h Z)) rfl
  · exact L B (P c285 (M c291 (M h Z))) rfl
  · exact L B (M c291 (P h Z)) rfl
  · exact LN B 1 1 c149 (P c272 (M c285 (P c291 (P h Z)))) (M c272 (P c285 (M c291 (M h Z)))) rfl rfl
  · exact L B (M c272 (M c291 (P h Z))) rfl
  · exact L B (M c1 (M c290 (P h Z))) rfl
  · exact L B (P c285 (M h Z)) rfl
  · exact L B (M c273 (P h Z)) rfl
  · exact L B (P c285 (M h Z)) rfl
 rcases em (Q y true 1 2 4 7) with c292 | c292
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c285 (P c292 (P h Z))) rfl
  · exact L B (M c292 (P h Z)) rfl
  · exact L B (M c285 (P c292 (P h Z))) rfl
  · exact LN B 1 1 c149 (M c292 (P h Z)) (P c292 (M h Z)) rfl rfl
  · exact L B (M c287 (P h Z)) rfl
  · exact L B (P c272 (P c292 (M h Z))) rfl
  · exact L B (P c292 (K 2 h Z)) rfl
  · exact L B (P c292 (M h Z)) rfl
  · exact L B (M c273 (P h Z)) rfl
  · exact absurd h c84
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c272 (P h Z)) rfl
 · exact absurd h c292
 · exact L B (M c272 (M c273 (M c288 (P h Z)))) rfl
 · exact absurd h c291
 · exact L B (M c273 (M c288 (P h Z))) rfl
 · exact L B (P c285 (M h Z)) rfl
 · exact L B (M c273 (P h Z)) rfl
 · exact L B (P c285 (M h Z)) rfl
 · exact L B (M c273 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s108 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c285 : Q y true 0 1 4 6) (c286 : Q y false 0 2 4 6) (c287 : Q y false 0 1 5 6) (c288 : Q y false 3 4 5 6) (c289 : Q y false 1 3 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (c284 : N (Q y false 0 1 4 6)) : False := by
 rcases em (Q y false 2 3 5 6) with c290 | c290
 ·
  exact s109 y B H c1 c272 c273 c274 c285 c286 c287 c288 c289 c290 c2 c84 c149 c245 c260 c270 c275 c284
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c290
 · exact L B (P c273 (P c288 (P h Z))) rfl
 · exact L B (M c1 (P c287 (M h Z))) rfl
 · exact L B (P c287 (P h Z)) rfl
 · exact LN B 1 1 c290 (M c1 (M c272 (P c286 Z))) (P c1 (M c287 Z)) rfl rfl
 · exact L B (P c273 (P c288 (P h Z))) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (P c272 (K 2 c287 (M c288 (P h Z)))) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (P c272 (P c273 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s107 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c285 : Q y true 0 1 4 6) (c286 : Q y false 0 2 4 6) (c287 : Q y false 0 1 5 6) (c288 : Q y false 3 4 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (c284 : N (Q y false 0 1 4 6)) : False := by
 rcases em (Q y false 1 3 4 6) with c289 | c289
 ·
  exact s108 y B H c1 c272 c273 c274 c285 c286 c287 c288 c289 c2 c84 c149 c245 c260 c270 c275 c284
 rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c273 (M c288 (P h Z)))) rfl
 · exact L B (P c272 (P c287 (P h Z))) rfl
 · exact absurd h c289
 · exact L B (P c272 (P c287 (P h Z))) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (P c272 (P c287 (P h Z))) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (P c272 (K 2 c287 (M c288 (P h Z)))) rfl
 · exact LN B 1 1 c289 (M c1 (P c272 (P c273 (P c288 Z)))) (P c1 (M c272 (M c273 (M c288 Z)))) rfl rfl
 · exact L B (P c287 (M c288 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s106 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c285 : Q y true 0 1 4 6) (c286 : Q y false 0 2 4 6) (c287 : Q y false 0 1 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (c284 : N (Q y false 0 1 4 6)) : False := by
 rcases em (Q y false 3 4 5 6) with c288 | c288
 ·
  exact s107 y B H c1 c272 c273 c274 c285 c286 c287 c288 c2 c84 c149 c245 c260 c270 c275 c284
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c288
 · exact L B (P c287 (P h Z)) rfl
 · exact L B (P c287 (M h Z)) rfl
 · exact L B (P c287 (P h Z)) rfl
 · exact L B (P c287 (M h Z)) rfl
 · exact L B (P c287 (P h Z)) rfl
 · exact L B (P c272 (P c287 (M h Z))) rfl
 · exact L B (P c272 (P c287 (P h Z))) rfl
 · exact L B (P c272 (M h Z)) rfl
 · exact L B (P c272 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s105 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c285 : Q y true 0 1 4 6) (c286 : Q y false 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (c284 : N (Q y false 0 1 4 6)) : False := by
 rcases em (Q y false 0 1 5 6) with c287 | c287
 ·
  exact s106 y B H c1 c272 c273 c274 c285 c286 c287 c2 c84 c149 c245 c260 c270 c275 c284
 rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c287 (M c272 (P c286 Z)) (P c272 (M c286 Z)) rfl rfl
 · exact L B (M c285 (P h Z)) rfl
 · exact L B (P c286 (M h Z)) rfl
 · exact L B (M c285 (P h Z)) rfl
 · exact absurd h c287
 · exact L B (M c272 (P c286 (P h Z))) rfl
 · exact L B (M c273 (P h Z)) rfl
 · exact absurd h c275
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c84

set_option maxHeartbeats 4000000 in
lemma s104 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c285 : Q y true 0 1 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) (c275 : N (Q y true 0 1 2 6)) (c284 : N (Q y false 0 1 4 6)) : False := by
 rcases em (Q y false 0 2 4 6) with c286 | c286
 ·
  exact s105 y B H c1 c272 c273 c274 c285 c286 c2 c84 c149 c245 c260 c270 c275 c284
 rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (P c285 (P h Z))) rfl
 · exact L B (M c285 (P h Z)) rfl
 · exact LN B 1 1 c84 (M c272 (M c273 (P c285 (P h Z)))) (P c272 (P c273 (M c285 (M h Z)))) rfl rfl
 · exact L B (M c285 (P h Z)) rfl
 · exact absurd h c286
 · exact L B (M c285 (P h Z)) rfl
 · exact L B (M c272 (M c273 (P h Z))) rfl
 · exact LN B 1 1 c149 (P c272 (P c273 (M c285 (P h Z)))) (M c272 (M c273 (P c285 (M h Z)))) rfl rfl
 · exact L B (P c273 (M h Z)) rfl
 · exact L B (P c273 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s103 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c275 : Q y true 0 1 2 6) (_c276 : Q y false 1 3 4 6) (c277 : Q y false 0 1 5 6) (_c278 : Q y false 0 2 4 6) (c279 : Q y false 3 4 5 6) (c280 : Q y false 2 3 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (_c245 : N (Q y true 0 1 4 5)) (_c260 : N (Q y false 0 2 4 5)) (_c270 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y true 0 1 4 7) with c281 | c281
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact G B (P c1 (P c273 (P c274 (P c281 (P h Z))))) rfl
  · exact L B (M c281 (P h Z)) rfl
  · exact LN B 1 1 c149 (P c272 (K 2 c273 (P c275 (P c279 (M c281 (M h Z)))))) (K (-2) c1 (M c272 (M c275 (P c279 (K (-2) c280 (P c281 (P h Z))))))) rfl rfl
  · exact L B (M c281 (P h Z)) rfl
  · exact L B (M c1 (M c280 (P h Z))) rfl
  · exact L B (M c281 (P h Z)) rfl
  · exact L B (M c273 (P h Z)) rfl
  · exact L B (P c281 (M h Z)) rfl
  · exact L B (M c277 (P c279 (P h Z))) rfl
  · exact L B (M c1 (P c273 (M c280 (M c281 (P h Z))))) rfl
 rcases em (Q y true 0 2 4 7) with c282 | c282
 ·
  rcases H.h13457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c273 (M c277 (P h Z))) rfl
  · exact L B (M c282 (P h Z)) rfl
  · exact L B (M c275 (P c282 (P h Z))) rfl
  · exact L B (M c282 (P h Z)) rfl
  · exact L B (M c275 (P c282 (P h Z))) rfl
  · exact L B (M c282 (P h Z)) rfl
  · exact L B (M c272 (M c280 (P h Z))) rfl
  · exact L B (M c282 (P h Z)) rfl
  · exact L B (P c272 (M h Z)) rfl
  · exact L B (P c272 (P h Z)) rfl
 rcases em (Q y true 1 2 4 7) with c283 | c283
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c275 (P c283 (P h Z))) rfl
  · exact L B (M c283 (P h Z)) rfl
  · exact L B (M c275 (P c283 (P h Z))) rfl
  · exact LN B 1 1 c149 (M c283 (P h Z)) (P c283 (M h Z)) rfl rfl
  · exact L B (M c273 (M c279 (P h Z))) rfl
  · exact L B (P c272 (P c283 (M h Z))) rfl
  · exact L B (P c283 (K 2 h Z)) rfl
  · exact L B (P c275 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c84
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c272 (P h Z)) rfl
 · exact absurd h c283
 · exact L B (M c272 (M c273 (M c279 (P h Z)))) rfl
 · exact absurd h c282
 · exact L B (M c277 (P h Z)) rfl
 · exact absurd h c281
 · exact L B (M c273 (P h Z)) rfl
 · exact L B (P c275 (M h Z)) rfl
 · exact L B (M c277 (P c279 (P h Z))) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s102 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c275 : Q y true 0 1 2 6) (c276 : Q y false 1 3 4 6) (c277 : Q y false 0 1 5 6) (c278 : Q y false 0 2 4 6) (c279 : Q y false 3 4 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y false 2 3 5 6) with c280 | c280
 ·
  exact s103 y B H c1 c272 c273 c274 c275 c276 c277 c278 c279 c280 c2 c84 c149 c245 c260 c270
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c280
 · exact L B (P c277 (P h Z)) rfl
 · exact L B (M c1 (P c277 (M h Z))) rfl
 · exact L B (P c277 (P h Z)) rfl
 · exact LN B 1 1 c280 (M c1 (M c272 (P c278 Z))) (P c1 (M c277 Z)) rfl rfl
 · exact L B (P c277 (P h Z)) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (M c275 (P h Z)) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (P c272 (P c273 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s101 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c275 : Q y true 0 1 2 6) (c276 : Q y false 1 3 4 6) (c277 : Q y false 0 1 5 6) (c278 : Q y false 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y false 3 4 5 6) with c279 | c279
 ·
  exact s102 y B H c1 c272 c273 c274 c275 c276 c277 c278 c279 c2 c84 c149 c245 c260 c270
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c279
 · exact L B (M c275 (P h Z)) rfl
 · exact L B (P c277 (M h Z)) rfl
 · exact L B (P c277 (P h Z)) rfl
 · exact L B (P c277 (M h Z)) rfl
 · exact L B (P c277 (P h Z)) rfl
 · exact L B (P c272 (P c277 (M h Z))) rfl
 · exact L B (P c272 (P c277 (P h Z))) rfl
 · exact L B (P c272 (M h Z)) rfl
 · exact L B (P c272 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s100 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c275 : Q y true 0 1 2 6) (c276 : Q y false 1 3 4 6) (c277 : Q y false 0 1 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y false 0 2 4 6) with c278 | c278
 ·
  exact s101 y B H c1 c272 c273 c274 c275 c276 c277 c278 c2 c84 c149 c245 c260 c270
 rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c277 (P h Z))) rfl
 · exact L B (P c272 (P c277 (P h Z))) rfl
 · exact L B (P c272 (P c277 (M h Z))) rfl
 · exact L B (M c275 (P h Z)) rfl
 · exact absurd h c278
 · exact L B (P c272 (P c277 (P h Z))) rfl
 · exact L B (M c272 (M c273 (P h Z))) rfl
 · exact L B (M c275 (P h Z)) rfl
 · exact L B (P c273 (M h Z)) rfl
 · exact L B (P c273 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s99 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c275 : Q y true 0 1 2 6) (c276 : Q y false 1 3 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y false 0 1 5 6) with c277 | c277
 ·
  exact s100 y B H c1 c272 c273 c274 c275 c276 c277 c2 c84 c149 c245 c260 c270
 rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c276 (M h Z)) rfl
 · exact L B (P c276 (P h Z)) rfl
 · exact L B (P c276 (M h Z)) rfl
 · exact L B (P c276 (P h Z)) rfl
 · exact absurd h c277
 · exact L B (P c1 (M c272 (P c276 (P h Z)))) rfl
 · exact L B (M c273 (P h Z)) rfl
 · exact L B (M c275 (P h Z)) rfl
 · exact L B (M c273 (P h Z)) rfl
 · exact L B (M c275 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s98 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c272 : Q y false 1 2 4 5) (c273 : Q y false 0 1 3 4) (c274 : Q y false 0 2 3 5) (c275 : Q y true 0 1 2 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c260 : N (Q y false 0 2 4 5)) (c270 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y false 1 3 4 6) with c276 | c276
 ·
  exact s99 y B H c1 c272 c273 c274 c275 c276 c2 c84 c149 c245 c260 c270
 rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact G B (P c273 (P c275 (P h Z))) rfl
 · exact L B (M c275 (P h Z)) rfl
 · exact absurd h c276
 · exact L B (M c275 (P h Z)) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (M c275 (P h Z)) rfl
 · exact L B (M c272 (P h Z)) rfl
 · exact L B (M c275 (P h Z)) rfl
 · exact LN B 1 1 c149 (P c272 (P c273 (M h Z))) (M c272 (M c273 (P h Z))) rfl rfl
 · exact L B (P c273 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s97 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c270 : Q y true 0 2 4 5) (c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c149 : N (Q y false 0 1 4 5)) (_c245 : N (Q y true 0 1 4 5)) (_c260 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y true 1 2 4 6) with c271 | c271
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c270 (P h Z)) rfl
  · exact L B (P c271 (M h Z)) rfl
  · exact L B (P c270 (P h Z)) rfl
  · exact L B (P c270 (M h Z)) rfl
  · exact L B (P c271 (K 2 h Z)) rfl
  · exact L B (P c270 (M h Z)) rfl
  · exact L B (P c270 (P h Z)) rfl
  · exact L B (P c270 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c270 (P h Z)) rfl
 · exact absurd h c271
 · exact L B (P c270 (P h Z)) rfl
 · exact L B (P c270 (M h Z)) rfl
 · exact L B (P c270 (P h Z)) rfl
 · exact L B (P c270 (M h Z)) rfl
 · exact L B (P c270 (P h Z)) rfl
 · exact L B (P c270 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s96 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c260 : Q y false 0 2 4 5) (c265 : Q y true 0 2 4 6) (_c266 : Q y true 1 2 4 7) (c267 : Q y false 0 1 6 7) (c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (_c261 : N (Q y true 0 1 2 6)) (c263 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 0 3 5 7) with c268 | c268
 ·
  rcases H.h01456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c267 (P c268 (M h Z))) rfl
  · exact L B (M c265 (P h Z)) rfl
  · exact L B (P c268 (M h Z)) rfl
  · exact L B (M c265 (P h Z)) rfl
  · exact L B (M c1 (P c267 (M c268 (P h Z)))) rfl
  · exact L B (M c260 (M c265 (P h Z))) rfl
  · exact L B (M c260 (P h Z)) rfl
  · exact absurd h c263
  · exact absurd h c149
  · exact absurd h c245
 rcases H.h02357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c267 (P h Z))) rfl
 · exact L B (M c265 (P c267 (P h Z))) rfl
 · exact absurd h c268
 · exact L B (M c260 (M c265 (P c267 (P h Z)))) rfl
 · exact LN B 1 1 c245 (P c265 (M c267 (P h Z))) (M c265 (P c267 (M h Z))) rfl rfl
 · exact L B (M c260 (M c265 (P c267 (P h Z)))) rfl
 · exact L B (M c260 (P h Z)) rfl
 · exact L B (P c265 (M h Z)) rfl
 · exact L B (M c260 (P h Z)) rfl
 · exact LN B 1 1 c2 (M c1 (P c260 (P h Z))) (P c1 (M c260 (M h Z))) rfl rfl

set_option maxHeartbeats 4000000 in
lemma s95 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c260 : Q y false 0 2 4 5) (c265 : Q y true 0 2 4 6) (c266 : Q y true 1 2 4 7) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c261 : N (Q y true 0 1 2 6)) (c263 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 0 1 6 7) with c267 | c267
 ·
  exact s96 y B H c1 c260 c265 c266 c267 c2 c84 c149 c245 c261 c263
 rcases H.h01367 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c1 (P c265 (M c266 (M h Z)))) rfl
 · exact L B (M c266 (P h Z)) rfl
 · exact L B (P c265 (M c266 (M h Z))) rfl
 · exact L B (M c260 (M c266 (P h Z))) rfl
 · exact absurd h c267
 · exact L B (M c260 (M c266 (P h Z))) rfl
 · exact L B (M c260 (P h Z)) rfl
 · exact L B (P c265 (M h Z)) rfl
 · exact L B (M c260 (P h Z)) rfl
 · exact L B (P c265 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s94 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c260 : Q y false 0 2 4 5) (c265 : Q y true 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) (c261 : N (Q y true 0 1 2 6)) (c263 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y true 1 2 4 7) with c266 | c266
 ·
  exact s95 y B H c1 c260 c265 c266 c2 c84 c149 c245 c261 c263
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c260 (P h Z)) rfl
 · exact absurd h c266
 · exact L B (M c260 (P h Z)) rfl
 · exact L B (P c265 (M h Z)) rfl
 · exact L B (P c265 (P h Z)) rfl
 · exact L B (P c265 (M h Z)) rfl
 · exact L B (M c260 (P h Z)) rfl
 · exact L B (P c265 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s93 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c260 : Q y false 0 2 4 5) (c263 : Q y true 0 1 4 6) (_c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (_c149 : N (Q y false 0 1 4 5)) (_c245 : N (Q y true 0 1 4 5)) (c261 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 1 4 5 6) with c264 | c264
 ·
  rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c264 (P h Z)) rfl
  · exact L B (M c263 (P h Z)) rfl
  · exact L B (M c1 (M c264 (P h Z))) rfl
  · exact L B (M c263 (P h Z)) rfl
  · exact L B (M c1 (M c264 (P h Z))) rfl
  · exact L B (M c263 (P h Z)) rfl
  · exact L B (M c260 (P h Z)) rfl
  · exact absurd h c261
  · exact L B (M c260 (P h Z)) rfl
  · exact absurd h c84
 rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c84 (P c263 (P h Z)) (M c263 (M h Z)) rfl rfl
 · exact L B (M c263 (P h Z)) rfl
 · exact absurd h c264
 · exact L B (M c263 (P h Z)) rfl
 · exact G B (P c260 (P c263 (P h Z))) rfl
 · exact L B (M c263 (P h Z)) rfl
 · exact L B (M c260 (P h Z)) rfl
 · exact L B (M c263 (P h Z)) rfl
 · exact L B (M c260 (P h Z)) rfl
 · exact L B (M c263 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s92 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c260 : Q y false 0 2 4 5) (c261 : Q y true 0 1 2 6) (_c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c149 : N (Q y false 0 1 4 5)) (_c245 : N (Q y true 0 1 4 5)) : False := by
 rcases em (Q y false 1 2 3 4) with c262 | c262
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c260 (P h Z))) rfl
  · exact L B (M c261 (P h Z)) rfl
  · exact G B (P c261 (P c262 (P h Z))) rfl
  · exact L B (M c261 (P h Z)) rfl
  · exact L B (M c260 (P h Z)) rfl
  · exact L B (M c261 (P h Z)) rfl
  · exact L B (M c260 (P h Z)) rfl
  · exact L B (M c261 (P h Z)) rfl
  · exact L B (P c262 (M h Z)) rfl
  · exact L B (P c262 (P h Z)) rfl
 rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c260 (P h Z))) rfl
 · exact L B (M c261 (P h Z)) rfl
 · exact L B (P c1 (M c260 (P h Z))) rfl
 · exact L B (M c261 (P h Z)) rfl
 · exact L B (M c260 (P h Z)) rfl
 · exact L B (M c261 (P h Z)) rfl
 · exact L B (M c260 (P h Z)) rfl
 · exact L B (M c261 (P h Z)) rfl
 · exact absurd h c262
 · exact L B (M c261 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s91 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c260 : Q y false 0 2 4 5) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) (c245 : N (Q y true 0 1 4 5)) : False := by
 rcases em (Q y true 0 1 2 6) with c261 | c261
 ·
  exact s92 y B H c1 c260 c261 c2 c84 c149 c245
 rcases em (Q y true 0 1 4 6) with c263 | c263
 ·
  exact s93 y B H c1 c260 c263 c2 c84 c149 c245 c261
 rcases em (Q y true 0 2 4 6) with c265 | c265
 ·
  exact s94 y B H c1 c260 c265 c2 c84 c149 c245 c261 c263
 rcases em (Q y true 1 2 4 6) with c269 | c269
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c269 (P h Z)) rfl
  · exact L B (P c269 (M h Z)) rfl
  · exact L B (P c269 (P h Z)) rfl
  · exact L B (P c269 (M h Z)) rfl
  · exact L B (P c269 (K 2 h Z)) rfl
  · exact L B (P c269 (M h Z)) rfl
  · exact L B (P c269 (K 2 h Z)) rfl
  · exact L B (P c269 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c260 (P h Z)) rfl
 · exact absurd h c269
 · exact L B (M c260 (P h Z)) rfl
 · exact absurd h c265
 · exact L B (M c260 (P h Z)) rfl
 · exact absurd h c263
 · exact L B (M c260 (P h Z)) rfl
 · exact absurd h c261
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s90 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c245 : Q y true 0 1 4 5) (c257 : Q y false 1 2 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (_c149 : N (Q y false 0 1 4 5)) (c246 : N (Q y false 0 2 4 6)) (c255 : N (Q y true 0 2 4 6)) : False := by
 rcases em (Q y false 2 4 5 6) with c258 | c258
 ·
  rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c257 (M h Z)) rfl
  · exact L B (P c257 (P h Z)) rfl
  · exact L B (P c257 (M h Z)) rfl
  · exact L B (P c257 (P h Z)) rfl
  · exact L B (M c1 (M c258 (P h Z))) rfl
  · exact LN B 1 1 c2 (P c258 (P h Z)) (M c258 (M h Z)) rfl rfl
  · exact L B (P c245 (P h Z)) rfl
  · exact L B (P c245 (M h Z)) rfl
  · exact L B (P c245 (P h Z)) rfl
  · exact absurd h c84
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c258
 · exact L B (K 2 c257 (P h Z)) rfl
 · exact L B (P c257 (M h Z)) rfl
 · exact L B (P c257 (P h Z)) rfl
 · exact L B (P c257 (M h Z)) rfl
 · exact L B (P c257 (P h Z)) rfl
 · exact absurd h c246
 · exact absurd h c255
 · exact L B (P c257 (M h Z)) rfl
 · exact L B (P c257 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s89 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c245 : Q y true 0 1 4 5) (c255 : Q y true 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c149 : N (Q y false 0 1 4 5)) (_c246 : N (Q y false 0 2 4 6)) : False := by
 rcases em (Q y true 1 2 4 7) with c256 | c256
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c245 (P c255 (M c256 (M h Z)))) rfl
  · exact L B (M c256 (P h Z)) rfl
  · exact L B (P c245 (M c256 (M h Z))) rfl
  · exact L B (K 2 c245 (M c256 (P h Z))) rfl
  · exact L B (P c245 (M c256 (M h Z))) rfl
  · exact L B (P c245 (M c256 (P h Z))) rfl
  · exact L B (P c245 (M c256 (M h Z))) rfl
  · exact L B (P c245 (M c256 (P h Z))) rfl
  · exact L B (P c245 (M c255 (M h Z))) rfl
  · exact L B (M c255 (P h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c255 (P h Z)) rfl
 · exact absurd h c256
 · exact L B (P c255 (P h Z)) rfl
 · exact L B (P c255 (M h Z)) rfl
 · exact L B (P c245 (P h Z)) rfl
 · exact L B (P c245 (M h Z)) rfl
 · exact L B (P c245 (P h Z)) rfl
 · exact L B (P c245 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s88 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c245 : Q y true 0 1 4 5) (_c246 : Q y false 0 2 4 6) (c247 : Q y false 3 4 5 6) (_c248 : Q y false 0 2 3 5) (c249 : Q y false 1 2 4 5) (c250 : Q y false 0 1 5 6) (_c251 : Q y false 1 3 4 6) (c252 : Q y false 2 3 5 6) (c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c149 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y true 0 2 4 7) with c253 | c253
 ·
  rcases H.h01267 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c245 (M c253 (M h Z))) rfl
  · exact L B (M c253 (P h Z)) rfl
  · exact L B (P c245 (M c253 (M h Z))) rfl
  · exact L B (M c253 (P h Z)) rfl
  · exact LN B 1 1 c2 (M c1 (P c247 (P c249 (P c253 (P h Z))))) (M c247 (M c249 (P c250 (M c252 (M c253 (M h Z)))))) rfl rfl
  · exact L B (M c249 (M c253 (P h Z))) rfl
  · exact L B (P c245 (P h Z)) rfl
  · exact L B (P c245 (M h Z)) rfl
  · exact L B (P c245 (P h Z)) rfl
  · exact L B (P c245 (M h Z)) rfl
 rcases em (Q y true 1 2 4 7) with c254 | c254
 ·
  rcases H.h02367 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c249 (P c250 (P c254 (P h Z))))) rfl
  · exact L B (M c254 (P h Z)) rfl
  · exact L B (P c245 (M c254 (M h Z))) rfl
  · exact L B (P c245 (M c254 (P h Z))) rfl
  · exact L B (P c245 (M c254 (M h Z))) rfl
  · exact L B (M c250 (M c254 (P h Z))) rfl
  · exact L B (P c254 (P h Z)) rfl
  · exact L B (P c254 (M h Z)) rfl
  · exact L B (M c1 (M c249 (M c252 (P h Z)))) rfl
  · exact LN B 1 1 c2 (P c249 (P c252 (P h Z))) (P c1 (M c249 (M c250 (M h Z)))) rfl rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c249 (P h Z)) rfl
 · exact absurd h c254
 · exact L B (M c249 (M c250 (P h Z))) rfl
 · exact absurd h c253
 · exact L B (P c245 (P h Z)) rfl
 · exact L B (P c245 (M h Z)) rfl
 · exact L B (P c245 (P h Z)) rfl
 · exact L B (P c245 (M h Z)) rfl
 · exact L B (P c247 (M c250 (P h Z))) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s87 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c245 : Q y true 0 1 4 5) (c246 : Q y false 0 2 4 6) (c247 : Q y false 3 4 5 6) (c248 : Q y false 0 2 3 5) (c249 : Q y false 1 2 4 5) (c250 : Q y false 0 1 5 6) (c251 : Q y false 1 3 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y false 2 3 5 6) with c252 | c252
 ·
  exact s88 y B H c1 c245 c246 c247 c248 c249 c250 c251 c252 c2 c84 c149
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c252
 · exact L B (P c250 (P h Z)) rfl
 · exact L B (P c245 (P c249 (P c250 (M h Z)))) rfl
 · exact L B (P c250 (P h Z)) rfl
 · exact L B (P c245 (P c247 (P c248 (M h Z)))) rfl
 · exact L B (P c250 (P h Z)) rfl
 · exact L B (M c249 (P h Z)) rfl
 · exact L B (M c247 (P c249 (K 2 c250 (P h Z)))) rfl
 · exact L B (M c249 (P h Z)) rfl
 · exact L B (M c247 (P c249 (P c250 (P h Z)))) rfl

set_option maxHeartbeats 4000000 in
lemma s86 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c245 : Q y true 0 1 4 5) (c246 : Q y false 0 2 4 6) (c247 : Q y false 3 4 5 6) (c248 : Q y false 0 2 3 5) (c249 : Q y false 1 2 4 5) (c250 : Q y false 0 1 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y false 1 3 4 6) with c251 | c251
 ·
  exact s87 y B H c1 c245 c246 c247 c248 c249 c250 c251 c2 c84 c149
 rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (P c245 (P h Z))) rfl
 · exact L B (P c249 (P c250 (P h Z))) rfl
 · exact absurd h c251
 · exact L B (P c247 (P c248 (P h Z))) rfl
 · exact L B (M c249 (P h Z)) rfl
 · exact L B (P c247 (P c248 (P h Z))) rfl
 · exact L B (M c249 (P h Z)) rfl
 · exact L B (M c247 (P c249 (K 2 c250 (P h Z)))) rfl
 · exact L B (P c245 (M c247 (P c249 (P c250 (M h Z))))) rfl
 · exact L B (M c247 (P c250 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s85 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c245 : Q y true 0 1 4 5) (c246 : Q y false 0 2 4 6) (c247 : Q y false 3 4 5 6) (c248 : Q y false 0 2 3 5) (c249 : Q y false 1 2 4 5) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y false 0 1 5 6) with c250 | c250
 ·
  exact s86 y B H c1 c245 c246 c247 c248 c249 c250 c2 c84 c149
 rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c245 (P c247 (P c248 (M h Z)))) rfl
 · exact L B (P c247 (P c248 (P h Z))) rfl
 · exact L B (P c247 (P c248 (M h Z))) rfl
 · exact L B (P c247 (P c248 (P h Z))) rfl
 · exact absurd h c250
 · exact L B (P c247 (P c248 (M c249 (P h Z)))) rfl
 · exact L B (P c245 (P h Z)) rfl
 · exact L B (P c245 (M h Z)) rfl
 · exact L B (P c245 (P h Z)) rfl
 · exact absurd h c84

set_option maxHeartbeats 4000000 in
lemma s84 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c245 : Q y true 0 1 4 5) (c246 : Q y false 0 2 4 6) (c247 : Q y false 3 4 5 6) (c248 : Q y false 0 2 3 5) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y false 1 2 4 5) with c249 | c249
 ·
  exact s85 y B H c1 c245 c246 c247 c248 c249 c2 c84 c149
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (P c245 (P h Z))) rfl
 · exact L B (P c246 (P h Z)) rfl
 · exact L B (M c1 (P c248 (M h Z))) rfl
 · exact L B (P c248 (P h Z)) rfl
 · exact absurd h c249
 · exact L B (P c248 (P h Z)) rfl
 · exact L B (M c246 (P c247 (P h Z))) rfl
 · exact L B (P c248 (P h Z)) rfl
 · exact L B (P c245 (P c246 (M c247 (M h Z)))) rfl
 · exact L B (P c246 (M c247 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s83 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c245 : Q y true 0 1 4 5) (c246 : Q y false 0 2 4 6) (c247 : Q y false 3 4 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c248 | c248
 ·
  exact s84 y B H c1 c245 c246 c247 c248 c2 c84 c149
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (P c245 (P h Z))) rfl
 · exact L B (P c246 (P h Z)) rfl
 · exact L B (P c246 (M h Z)) rfl
 · exact L B (P c246 (P h Z)) rfl
 · exact L B (P c246 (M h Z)) rfl
 · exact L B (P c246 (P h Z)) rfl
 · exact absurd h c248
 · exact L B (P c246 (M c247 (P h Z))) rfl
 · exact L B (P c246 (M c247 (M h Z))) rfl
 · exact L B (P c246 (M c247 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s82 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c245 : Q y true 0 1 4 5) (c246 : Q y false 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c149 : N (Q y false 0 1 4 5)) : False := by
 rcases em (Q y false 3 4 5 6) with c247 | c247
 ·
  exact s83 y B H c1 c245 c246 c247 c2 c84 c149
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c247
 · exact L B (P c246 (P h Z)) rfl
 · exact L B (P c246 (M h Z)) rfl
 · exact L B (P c246 (P h Z)) rfl
 · exact L B (P c246 (M h Z)) rfl
 · exact L B (P c246 (P h Z)) rfl
 · exact L B (P c246 (M h Z)) rfl
 · exact L B (P c246 (P h Z)) rfl
 · exact L B (P c246 (M h Z)) rfl
 · exact L B (P c246 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s81 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c227 : Q y false 2 3 4 5) (c242 : Q y false 1 2 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (_c150 : N (Q y false 0 2 3 4)) (_c167 : N (Q y true 0 2 3 4)) (_c178 : N (Q y false 0 2 3 5)) (_c213 : N (Q y true 0 2 3 5)) (c228 : N (Q y true 0 1 2 6)) (_c235 : N (Q y true 0 1 4 6)) (c239 : N (Q y false 0 2 4 6)) (c240 : N (Q y true 0 2 4 6)) : False := by
 rcases em (Q y false 2 4 5 6) with c243 | c243
 ·
  rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c242 (M h Z)) rfl
  · exact L B (P c242 (P h Z)) rfl
  · exact L B (P c242 (M h Z)) rfl
  · exact L B (P c242 (P h Z)) rfl
  · exact L B (M c149 (P c227 (M c243 (P h Z)))) rfl
  · exact LN B 1 1 c2 (P c243 (P h Z)) (M c243 (M h Z)) rfl rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c228
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c84
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c243
 · exact L B (K 2 c242 (P h Z)) rfl
 · exact L B (P c242 (M h Z)) rfl
 · exact L B (P c242 (P h Z)) rfl
 · exact L B (P c242 (M h Z)) rfl
 · exact L B (P c242 (P h Z)) rfl
 · exact absurd h c239
 · exact absurd h c240
 · exact L B (P c242 (M h Z)) rfl
 · exact L B (P c242 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s80 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c227 : Q y false 2 3 4 5) (c240 : Q y true 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) (_c178 : N (Q y false 0 2 3 5)) (_c213 : N (Q y true 0 2 3 5)) (_c228 : N (Q y true 0 1 2 6)) (_c235 : N (Q y true 0 1 4 6)) (_c239 : N (Q y false 0 2 4 6)) : False := by
 rcases em (Q y true 1 2 4 7) with c241 | c241
 ·
  rcases H.h13457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c167 (P c149 (P c241 (P h Z))) (M c149 (M c241 (M h Z))) rfl rfl
  · exact L B (M c241 (P h Z)) rfl
  · exact LN B 1 1 c2 (P c1 (P c227 (P c241 (P h Z)))) (M c149 (M c241 (M h Z))) rfl rfl
  · exact L B (M c241 (P h Z)) rfl
  · exact L B (K 2 c149 (M c227 (P c241 (P h Z)))) rfl
  · exact L B (M c241 (P h Z)) rfl
  · exact L B (P c149 (M c227 (P c240 (P h Z)))) rfl
  · exact L B (M c241 (P h Z)) rfl
  · exact L B (M c1 (P c149 (M h Z))) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c240 (P h Z)) rfl
 · exact absurd h c241
 · exact L B (P c240 (P h Z)) rfl
 · exact L B (P c240 (M h Z)) rfl
 · exact L B (M c149 (P h Z)) rfl
 · exact L B (P c240 (M h Z)) rfl
 · exact L B (P c240 (P h Z)) rfl
 · exact L B (P c240 (M h Z)) rfl
 · exact L B (M c149 (P c227 (P h Z))) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s79 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c227 : Q y false 2 3 4 5) (c235 : Q y true 0 1 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (_c150 : N (Q y false 0 2 3 4)) (_c167 : N (Q y true 0 2 3 4)) (c178 : N (Q y false 0 2 3 5)) (_c213 : N (Q y true 0 2 3 5)) (c228 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 0 1 5 6) with c236 | c236
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c2 (P c227 (P c235 (P h Z))) (M c227 (M c235 (M h Z))) rfl rfl
  · exact L B (P c236 (P h Z)) rfl
  · exact L B (P c236 (M h Z)) rfl
  · exact L B (P c236 (P h Z)) rfl
  · exact L B (P c236 (M h Z)) rfl
  · exact L B (P c236 (P h Z)) rfl
  · exact L B (M c1 (P c149 (P c236 (M h Z)))) rfl
  · exact L B (P c227 (P c236 (P h Z))) rfl
  · exact L B (P c149 (M h Z)) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases em (Q y false 0 2 5 6) with c237 | c237
 ·
  rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c178 (P c227 (P c237 (M h Z))) (M c227 (M c237 (P h Z))) rfl rfl
  · exact L B (M c235 (P h Z)) rfl
  · exact L B (M c1 (P c237 (M h Z))) rfl
  · exact L B (M c235 (P h Z)) rfl
  · exact L B (M c237 (P h Z)) rfl
  · exact L B (M c235 (P h Z)) rfl
  · exact L B (M c237 (P h Z)) rfl
  · exact L B (M c235 (P h Z)) rfl
  · exact G B (P c235 (P c237 (P h Z))) rfl
  · exact L B (M c235 (P h Z)) rfl
 rcases em (Q y false 1 2 5 6) with c238 | c238
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c238 (M h Z)) rfl
  · exact L B (P c238 (P h Z)) rfl
  · exact L B (P c238 (M h Z)) rfl
  · exact L B (P c238 (P h Z)) rfl
  · exact absurd h c236
  · exact L B (M c235 (P h Z)) rfl
  · exact L B (M c1 (M c227 (P h Z))) rfl
  · exact L B (P c235 (M h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact LN B 1 1 c178 (P c1 (P c227 (P c235 (P c238 (M h Z))))) (M c1 (M c227 (M c235 (M c238 (P h Z))))) rfl rfl
 rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c238
 · exact L B (M c235 (P h Z)) rfl
 · exact absurd h c237
 · exact L B (M c235 (P h Z)) rfl
 · exact absurd h c236
 · exact L B (M c235 (P h Z)) rfl
 · exact L B (M c149 (P h Z)) rfl
 · exact absurd h c228
 · exact L B (M c149 (P h Z)) rfl
 · exact absurd h c84

set_option maxHeartbeats 4000000 in
lemma s78 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c227 : Q y false 2 3 4 5) (c228 : Q y true 0 1 2 6) (c229 : Q y false 0 1 3 4) (_c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) (c178 : N (Q y false 0 2 3 5)) (_c213 : N (Q y true 0 2 3 5)) : False := by
 rcases em (Q y false 0 1 5 6) with c230 | c230
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c1 (P c230 (M h Z))) rfl
  · exact L B (P c230 (P h Z)) rfl
  · exact L B (P c230 (M h Z)) rfl
  · exact L B (P c230 (P h Z)) rfl
  · exact L B (P c230 (M h Z)) rfl
  · exact L B (P c230 (P h Z)) rfl
  · exact LN B 1 1 c178 (P c229 (M c230 (P h Z))) (M c229 (P c230 (M h Z))) rfl rfl
  · exact L B (M c228 (P h Z)) rfl
  · exact L B (P c1 (P c227 (M h Z))) rfl
  · exact L B (P c1 (P c227 (P h Z))) rfl
 rcases em (Q y false 0 3 5 6) with c231 | c231
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c231 (P h Z)) rfl
  · exact L B (P c149 (P c231 (P h Z))) rfl
  · exact L B (M c231 (P h Z)) rfl
  · exact L B (M c228 (P h Z)) rfl
  · exact L B (M c231 (P h Z)) rfl
  · exact L B (M c228 (P h Z)) rfl
  · exact L B (M c231 (P h Z)) rfl
  · exact L B (M c228 (P h Z)) rfl
  · exact absurd h c150
  · exact absurd h c167
 rcases em (Q y false 1 3 5 6) with c232 | c232
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c232 (P h Z)) rfl
  · exact L B (P c1 (P c227 (P c232 (P h Z)))) rfl
  · exact L B (M c232 (P h Z)) rfl
  · exact L B (P c149 (P c232 (P h Z))) rfl
  · exact L B (M c232 (P h Z)) rfl
  · exact L B (P c1 (P c149 (P c232 (P h Z)))) rfl
  · exact L B (M c232 (P h Z)) rfl
  · exact L B (M c228 (P h Z)) rfl
  · exact G B (P c1 (P c227 (P c228 (P c232 (P h Z))))) rfl
  · exact L B (P c229 (P h Z)) rfl
 rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c232
 · exact L B (M c228 (P h Z)) rfl
 · exact absurd h c231
 · exact L B (M c228 (P h Z)) rfl
 · exact absurd h c230
 · exact L B (M c228 (P h Z)) rfl
 · exact L B (M c1 (M c227 (P h Z))) rfl
 · exact L B (M c228 (P h Z)) rfl
 · exact L B (M c1 (M c227 (P h Z))) rfl
 · exact L B (M c228 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s77 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c227 : Q y false 2 3 4 5) (c228 : Q y true 0 1 2 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) (c178 : N (Q y false 0 2 3 5)) (c213 : N (Q y true 0 2 3 5)) : False := by
 rcases em (Q y false 0 1 3 4) with c229 | c229
 ·
  exact s78 y B H c1 c149 c227 c228 c229 c2 c84 c150 c167 c178 c213
 rcases em (Q y false 0 3 4 6) with c233 | c233
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c149 (P h Z))) rfl
  · exact L B (M c228 (P h Z)) rfl
  · exact L B (M c233 (P h Z)) rfl
  · exact L B (M c228 (P h Z)) rfl
  · exact L B (M c233 (P h Z)) rfl
  · exact L B (P c1 (P c233 (P h Z))) rfl
  · exact L B (M c233 (P h Z)) rfl
  · exact L B (M c228 (P h Z)) rfl
  · exact G B (P c228 (P c233 (P h Z))) rfl
  · exact L B (M c228 (P h Z)) rfl
 rcases em (Q y false 1 3 4 6) with c234 | c234
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c178 (P c1 (P c234 (M h Z))) (M c149 (P c227 (M c234 (P h Z)))) rfl rfl
  · exact L B (P c234 (P h Z)) rfl
  · exact L B (P c234 (M h Z)) rfl
  · exact L B (M c228 (P h Z)) rfl
  · exact L B (P c234 (M h Z)) rfl
  · exact L B (P c234 (P h Z)) rfl
  · exact absurd h c233
  · exact L B (M c228 (P h Z)) rfl
  · exact L B (P c149 (M h Z)) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c234
 · exact L B (M c228 (P h Z)) rfl
 · exact absurd h c233
 · exact L B (M c228 (P h Z)) rfl
 · exact L B (M c149 (P h Z)) rfl
 · exact L B (M c228 (P h Z)) rfl
 · exact L B (M c149 (P h Z)) rfl
 · exact L B (M c228 (P h Z)) rfl
 · exact absurd h c229
 · exact L B (M c228 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s76 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c213 : Q y true 0 2 3 5) (c219 : Q y false 2 3 4 5) (c220 : Q y true 0 1 4 6) (_c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (_c167 : N (Q y true 0 2 3 4)) (_c178 : N (Q y false 0 2 3 5)) (c214 : N (Q y false 1 2 4 5)) : False := by
 rcases em (Q y false 0 2 5 6) with c221 | c221
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c149 (P h Z))) rfl
  · exact L B (M c220 (P h Z)) rfl
  · exact L B (P c1 (M c221 (P h Z))) rfl
  · exact L B (M c220 (P h Z)) rfl
  · exact L B (M c221 (P h Z)) rfl
  · exact L B (M c220 (P h Z)) rfl
  · exact L B (M c221 (P h Z)) rfl
  · exact L B (P c213 (M c221 (M h Z))) rfl
  · exact L B (P c213 (M c220 (P h Z))) rfl
  · exact L B (M c213 (P h Z)) rfl
 rcases em (Q y false 1 2 5 6) with c222 | c222
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c222 (M h Z)) rfl
  · exact L B (P c222 (P h Z)) rfl
  · exact L B (P c222 (M h Z)) rfl
  · exact L B (P c222 (P h Z)) rfl
  · exact LN B 1 1 c214 (P c1 (P c219 (P c222 (M h Z)))) (M c149 (M c222 (P h Z))) rfl rfl
  · exact L B (M c220 (P h Z)) rfl
  · exact L B (M c1 (M c219 (P h Z))) rfl
  · exact L B (P c220 (M h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (P c213 (M h Z)) rfl
 rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c222
 · exact L B (M c220 (P h Z)) rfl
 · exact absurd h c221
 · exact L B (M c220 (P h Z)) rfl
 · exact LN B 1 1 c150 (M c213 (P c220 (P h Z))) (P c213 (M c220 (M h Z))) rfl rfl
 · exact L B (M c220 (P h Z)) rfl
 · exact L B (P c213 (P h Z)) rfl
 · exact L B (P c213 (M h Z)) rfl
 · exact L B (P c213 (P h Z)) rfl
 · exact absurd h c84

set_option maxHeartbeats 4000000 in
lemma s75 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c213 : Q y true 0 2 3 5) (c219 : Q y false 2 3 4 5) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) (c178 : N (Q y false 0 2 3 5)) (c214 : N (Q y false 1 2 4 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c220 | c220
 ·
  exact s76 y B H c1 c149 c213 c219 c220 c2 c84 c150 c167 c178 c214
 rcases em (Q y false 0 2 4 6) with c223 | c223
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c213 (P c223 (M h Z))) rfl
  · exact L B (P c223 (P h Z)) rfl
  · exact L B (P c223 (M h Z)) rfl
  · exact L B (P c223 (P h Z)) rfl
  · exact L B (P c223 (M h Z)) rfl
  · exact L B (P c223 (P h Z)) rfl
  · exact L B (P c223 (M h Z)) rfl
  · exact L B (P c223 (P h Z)) rfl
  · exact L B (P c149 (M h Z)) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c224 | c224
 ·
  rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c213 (M c224 (M h Z))) rfl
  · exact L B (M c224 (P h Z)) rfl
  · exact L B (P c213 (M c224 (M h Z))) rfl
  · exact L B (M c224 (P h Z)) rfl
  · exact L B (P c149 (P c224 (P h Z))) rfl
  · exact L B (M c224 (P h Z)) rfl
  · exact L B (P c224 (P h Z)) rfl
  · exact L B (M c224 (P h Z)) rfl
  · exact absurd h c214
  · exact L B (P c1 (P c219 (P h Z))) rfl
 rcases em (Q y false 1 2 4 6) with c225 | c225
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c225 (M h Z)) rfl
  · exact L B (P c225 (P h Z)) rfl
  · exact L B (P c225 (M h Z)) rfl
  · exact L B (P c225 (P h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact absurd h c220
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (P c213 (M h Z)) rfl
  · exact L B (P c213 (P c225 (P h Z))) rfl
  · exact L B (P c213 (P c225 (M h Z))) rfl
 rcases em (Q y true 1 2 4 6) with c226 | c226
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c226 (P h Z)) rfl
  · exact L B (P c226 (M h Z)) rfl
  · exact L B (P c226 (P h Z)) rfl
  · exact L B (P c226 (M h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (P c226 (M h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (P c226 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c225
 · exact absurd h c226
 · exact absurd h c223
 · exact absurd h c224
 · exact L B (M c1 (M c219 (P h Z))) rfl
 · exact absurd h c220
 · exact L B (P c213 (P h Z)) rfl
 · exact L B (P c213 (M h Z)) rfl
 · exact L B (M c149 (P c219 (P h Z))) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s74 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c213 : Q y true 0 2 3 5) (c214 : Q y false 1 2 4 5) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (_c167 : N (Q y true 0 2 3 4)) (_c178 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c215 | c215
 ·
  rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c150 (P c149 (M c213 (M c214 (P c215 (P h Z))))) (M c149 (P c213 (P c214 (M c215 (M h Z))))) rfl rfl
  · exact L B (M c215 (P h Z)) rfl
  · exact G B (P c214 (P c215 (P h Z))) rfl
  · exact L B (M c215 (P h Z)) rfl
  · exact LN B 1 1 c150 (M c213 (P c215 (P h Z))) (P c213 (M c215 (M h Z))) rfl rfl
  · exact L B (M c215 (P h Z)) rfl
  · exact L B (P c213 (P h Z)) rfl
  · exact L B (P c213 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c84
 rcases em (Q y false 0 2 4 6) with c216 | c216
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c213 (P c216 (M h Z))) rfl
  · exact L B (P c216 (P h Z)) rfl
  · exact L B (P c216 (M h Z)) rfl
  · exact L B (P c216 (P h Z)) rfl
  · exact L B (P c216 (M h Z)) rfl
  · exact L B (P c216 (P h Z)) rfl
  · exact L B (P c216 (M h Z)) rfl
  · exact L B (P c216 (P h Z)) rfl
  · exact L B (P c214 (M h Z)) rfl
  · exact L B (P c214 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c217 | c217
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c149 (P h Z))) rfl
  · exact L B (M c217 (P h Z)) rfl
  · exact L B (P c1 (P c217 (P h Z))) rfl
  · exact L B (M c217 (P h Z)) rfl
  · exact L B (M c214 (P h Z)) rfl
  · exact L B (M c217 (P h Z)) rfl
  · exact L B (M c214 (P h Z)) rfl
  · exact L B (P c213 (P c214 (P c217 (M h Z)))) rfl
  · exact L B (P c149 (P c213 (P h Z))) rfl
  · exact L B (M c213 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c218 | c218
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c214 (P h Z)) rfl
  · exact L B (P c218 (M h Z)) rfl
  · exact L B (P c218 (P h Z)) rfl
  · exact L B (P c218 (M h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (P c218 (M h Z)) rfl
  · exact L B (P c218 (K 2 h Z)) rfl
  · exact L B (P c218 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c214 (P h Z)) rfl
 · exact absurd h c218
 · exact absurd h c216
 · exact absurd h c217
 · exact L B (M c149 (P h Z)) rfl
 · exact absurd h c215
 · exact L B (M c1 (P h Z)) rfl
 · exact L B (P c213 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s73 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (_c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c207 : Q y true 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c150 : N (Q y false 0 2 3 4)) (_c167 : N (Q y true 0 2 3 4)) (_c180 : N (Q y true 0 1 2 6)) (_c191 : N (Q y true 0 1 4 6)) (_c192 : N (Q y false 0 2 4 6)) : False := by
 rcases em (Q y true 1 2 4 7) with c208 | c208
 ·
  rcases H.h12357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c149 (P c208 (P h Z)))) rfl
  · exact L B (M c208 (P h Z)) rfl
  · exact L B (P c1 (P c149 (P c208 (P h Z)))) rfl
  · exact L B (M c208 (P h Z)) rfl
  · exact L B (P c149 (P c208 (P h Z))) rfl
  · exact L B (M c208 (P h Z)) rfl
  · exact L B (P c207 (P h Z)) rfl
  · exact L B (P c208 (M h Z)) rfl
  · exact L B (M c179 (P h Z)) rfl
  · exact L B (P c149 (P c179 (P h Z))) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c207 (P h Z)) rfl
 · exact absurd h c208
 · exact L B (P c207 (P h Z)) rfl
 · exact L B (P c207 (M h Z)) rfl
 · exact L B (M c149 (P h Z)) rfl
 · exact L B (P c207 (M h Z)) rfl
 · exact L B (P c207 (P h Z)) rfl
 · exact L B (P c207 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s72 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (_c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (_c192 : Q y false 0 2 4 6) (c193 : Q y false 3 4 5 6) (c203 : Q y true 0 1 5 6) (c204 : Q y false 1 2 5 6) (c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c150 : N (Q y false 0 2 3 4)) (_c167 : N (Q y true 0 2 3 4)) (_c180 : N (Q y true 0 1 2 6)) (_c191 : N (Q y true 0 1 4 6)) (_c194 : N (Q y false 0 1 5 6)) : False := by
 rcases em (Q y true 0 2 4 7) with c205 | c205
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c179 (P c203 (M c205 (M h Z)))) rfl
  · exact L B (M c205 (P h Z)) rfl
  · exact L B (P c203 (M c205 (M h Z))) rfl
  · exact L B (M c205 (P h Z)) rfl
  · exact L B (P c203 (M c205 (M h Z))) rfl
  · exact L B (M c205 (P h Z)) rfl
  · exact G B (P c1 (P c149 (P c205 (P h Z)))) rfl
  · exact L B (M c205 (P h Z)) rfl
  · exact L B (P c204 (M h Z)) rfl
  · exact L B (P c204 (P h Z)) rfl
 rcases em (Q y true 1 2 4 7) with c206 | c206
 ·
  rcases H.h02367 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c149 (P c204 (P c206 (P h Z))))) rfl
  · exact L B (M c206 (P h Z)) rfl
  · exact L B (P c203 (M c206 (M h Z))) rfl
  · exact L B (P c203 (M c206 (P h Z))) rfl
  · exact L B (P c203 (M c206 (M h Z))) rfl
  · exact L B (P c203 (M c206 (P h Z))) rfl
  · exact L B (P c206 (P h Z)) rfl
  · exact L B (P c206 (M h Z)) rfl
  · exact L B (M c179 (P c203 (P h Z))) rfl
  · exact L B (M c179 (P c203 (M h Z))) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c179 (M c193 (P h Z))) rfl
 · exact absurd h c206
 · exact L B (M c149 (M c179 (M c193 (P h Z)))) rfl
 · exact absurd h c205
 · exact L B (P c203 (P h Z)) rfl
 · exact L B (P c203 (M h Z)) rfl
 · exact L B (P c203 (P h Z)) rfl
 · exact L B (P c203 (M h Z)) rfl
 · exact L B (P c193 (P c203 (P h Z))) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s71 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c192 : Q y false 0 2 4 6) (c193 : Q y false 3 4 5 6) (c203 : Q y true 0 1 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) (c180 : N (Q y true 0 1 2 6)) (c191 : N (Q y true 0 1 4 6)) (c194 : N (Q y false 0 1 5 6)) : False := by
 rcases em (Q y false 1 2 5 6) with c204 | c204
 ·
  exact s72 y B H c1 c149 c178 c179 c192 c193 c203 c204 c2 c84 c150 c167 c180 c191 c194
 rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c193 (M h Z)) rfl
 · exact L B (M c203 (P h Z)) rfl
 · exact L B (P c193 (M h Z)) rfl
 · exact L B (M c203 (P h Z)) rfl
 · exact absurd h c204
 · exact L B (P c179 (P c193 (P h Z))) rfl
 · exact L B (M c179 (M c193 (P h Z))) rfl
 · exact L B (P c149 (P c179 (P c193 (P h Z)))) rfl
 · exact L B (P c149 (P c179 (P c193 (P c203 (M h Z))))) rfl
 · exact L B (P c149 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s70 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (_c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (_c192 : Q y false 0 2 4 6) (c193 : Q y false 3 4 5 6) (c194 : Q y false 0 1 5 6) (c195 : Q y false 0 1 3 4) (c196 : Q y false 1 2 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) (c180 : N (Q y true 0 1 2 6)) (c191 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y true 0 1 2 7) with c197 | c197
 ·
  rcases H.h02347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c179 (M c195 (M c196 (P h Z))))) rfl
  · exact L B (M c197 (P h Z)) rfl
  · exact G B (P c179 (P c197 (P h Z))) rfl
  · exact L B (M c197 (P h Z)) rfl
  · exact L B (M c149 (M c179 (M c193 (P h Z)))) rfl
  · exact L B (M c197 (P h Z)) rfl
  · exact L B (M c149 (M c179 (P h Z))) rfl
  · exact L B (M c197 (P h Z)) rfl
  · exact absurd h c150
  · exact absurd h c167
 rcases em (Q y true 0 1 4 7) with c198 | c198
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c196 (P h Z)) rfl
  · exact L B (M c198 (P h Z)) rfl
  · exact G B (P c149 (P c179 (P c195 (P c198 (P h Z))))) rfl
  · exact L B (M c198 (P h Z)) rfl
  · exact L B (P c179 (M c195 (M c196 (P h Z)))) rfl
  · exact L B (M c198 (P h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact absurd h c197
  · exact L B (P c193 (M c194 (P h Z))) rfl
  · exact absurd h c84
 rcases em (Q y true 0 2 4 7) with c199 | c199
 ·
  rcases H.h01267 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c191 (P c199 (P h Z)) (M c199 (M h Z)) rfl rfl
  · exact L B (M c199 (P h Z)) rfl
  · exact G B (P c149 (P c179 (P c195 (P c196 (P c199 (P h Z)))))) rfl
  · exact L B (M c199 (P h Z)) rfl
  · exact LN B 1 1 c191 (P c179 (M c195 (P c199 (P h Z)))) (M c179 (P c195 (M c199 (M h Z)))) rfl rfl
  · exact L B (M c196 (M c199 (P h Z))) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c197
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c180
 rcases em (Q y true 1 2 4 7) with c200 | c200
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c149 (P c200 (P h Z)))) rfl
  · exact L B (M c200 (P h Z)) rfl
  · exact LN B 1 1 c191 (P c1 (M c193 (M c195 (P c200 (P h Z))))) (M c1 (P c194 (M c200 (M h Z)))) rfl rfl
  · exact L B (M c149 (M c200 (P h Z))) rfl
  · exact L B (P c179 (M c195 (M c196 (P h Z)))) rfl
  · exact L B (P c149 (P c200 (M h Z))) rfl
  · exact L B (P c200 (K 2 h Z)) rfl
  · exact L B (P c200 (M h Z)) rfl
  · exact L B (M c179 (M c194 (P c196 (P h Z)))) rfl
  · exact LN B 1 1 c191 (M c193 (P h Z)) (M c179 (P c196 (M h Z))) rfl rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c196 (P h Z)) rfl
 · exact absurd h c200
 · exact L B (M c149 (M c196 (P h Z))) rfl
 · exact absurd h c199
 · exact L B (M c149 (P h Z)) rfl
 · exact absurd h c198
 · exact L B (M c149 (P h Z)) rfl
 · exact absurd h c197
 · exact L B (M c195 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s69 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c192 : Q y false 0 2 4 6) (c193 : Q y false 3 4 5 6) (c194 : Q y false 0 1 5 6) (c195 : Q y false 0 1 3 4) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) (c180 : N (Q y true 0 1 2 6)) (c191 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 1 2 5 6) with c196 | c196
 ·
  exact s70 y B H c1 c149 c178 c179 c192 c193 c194 c195 c196 c2 c84 c150 c167 c180 c191
 rcases em (Q y false 2 3 5 6) with c201 | c201
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c179 (M c193 (P h Z))) rfl
  · exact LN B 1 1 c196 (P c1 (P c179 (M c195 (P c201 Z)))) (M c179 (M c193 Z)) rfl rfl
  · exact L B (M c149 (M c179 (M c193 (P h Z)))) rfl
  · exact LN B 1 1 c196 (P c1 (P c179 (M c195 (P c201 Z)))) (M c179 (M c193 Z)) rfl rfl
  · exact L B (M c1 (M c201 (P h Z))) rfl
  · exact LN B 1 1 c196 (P c1 (P c179 (M c195 (P c201 Z)))) (M c179 (M c194 (P c195 Z))) rfl rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact LN B 1 1 c196 (P c1 (P c179 (M c195 (P c201 Z)))) (M c179 (M c193 Z)) rfl rfl
  · exact L B (P c193 (M c194 (P h Z))) rfl
  · exact absurd h c2
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c201
 · exact L B (P c179 (P c193 (P h Z))) rfl
 · exact L B (P c179 (P c193 (M h Z))) rfl
 · exact L B (P c194 (P h Z)) rfl
 · exact absurd h c196
 · exact L B (P c179 (P c193 (P h Z))) rfl
 · exact L B (M c179 (P h Z)) rfl
 · exact L B (P c149 (P c179 (P c194 (P h Z)))) rfl
 · exact L B (M c179 (P h Z)) rfl
 · exact L B (P c149 (M c193 (P c194 (P h Z)))) rfl

set_option maxHeartbeats 4000000 in
lemma s68 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c192 : Q y false 0 2 4 6) (c193 : Q y false 3 4 5 6) (c194 : Q y false 0 1 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) (c180 : N (Q y true 0 1 2 6)) (c191 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 0 1 3 4) with c195 | c195
 ·
  exact s69 y B H c1 c149 c178 c179 c192 c193 c194 c195 c2 c84 c150 c167 c180 c191
 rcases em (Q y false 1 3 4 6) with c202 | c202
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c179 (M c193 (P h Z))) rfl
  · exact LN B 1 1 c195 (M c193 (P c194 Z)) (P c193 (M c194 Z)) rfl rfl
  · exact L B (M c149 (M c179 (M c193 (P h Z)))) rfl
  · exact LN B 1 1 c195 (M c193 (P c194 Z)) (P c193 (M c194 Z)) rfl rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact LN B 1 1 c195 (M c193 (P c194 Z)) (P c193 (M c194 Z)) rfl rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact LN B 1 1 c195 (M c193 (P c194 Z)) (P c193 (M c194 Z)) rfl rfl
  · exact L B (P c193 (M c194 (P h Z))) rfl
  · exact absurd h c2
 rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c202
 · exact L B (P c149 (P c179 (P c193 (P h Z)))) rfl
 · exact L B (P c149 (P c179 (P c193 (M h Z)))) rfl
 · exact L B (P c149 (P c179 (P c193 (P h Z)))) rfl
 · exact L B (M c194 (P h Z)) rfl
 · exact absurd h c191
 · exact L B (M c149 (P h Z)) rfl
 · exact G B (P c178 (P c179 (P c193 (P h Z)))) rfl
 · exact absurd h c195
 · exact L B (M c193 (P c194 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s67 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (_c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c180 : Q y true 0 1 2 6) (_c181 : Q y false 0 2 4 6) (c182 : Q y false 0 1 5 6) (c183 : Q y false 3 4 5 6) (c184 : Q y false 0 1 3 4) (c185 : Q y false 1 2 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (_c150 : N (Q y false 0 2 3 4)) (_c167 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y true 0 1 4 7) with c186 | c186
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c179 (M c183 (P h Z))) rfl
  · exact L B (M c186 (P h Z)) rfl
  · exact L B (M c180 (M c182 (P c183 (M c185 (P c186 (P h Z)))))) rfl
  · exact L B (M c186 (P h Z)) rfl
  · exact L B (P c179 (M c184 (M c185 (P h Z)))) rfl
  · exact L B (M c186 (P h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c186 (M h Z)) rfl
  · exact L B (M c179 (M c182 (P c185 (P h Z)))) rfl
  · exact absurd h c84
 rcases em (Q y true 0 2 4 7) with c187 | c187
 ·
  rcases H.h13457 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c179 (M c185 (P h Z))) rfl
  · exact L B (M c187 (P h Z)) rfl
  · exact L B (M c180 (P c187 (P h Z))) rfl
  · exact L B (M c187 (P h Z)) rfl
  · exact L B (M c180 (P c187 (P h Z))) rfl
  · exact L B (M c187 (P h Z)) rfl
  · exact L B (P c1 (M c149 (M c179 (M c183 (P h Z))))) rfl
  · exact L B (M c187 (P h Z)) rfl
  · exact L B (P c149 (P c179 (M c182 (P c183 (M h Z))))) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases em (Q y true 1 2 4 7) with c188 | c188
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c180 (P c188 (P h Z))) rfl
  · exact L B (M c188 (P h Z)) rfl
  · exact L B (M c180 (P c188 (P h Z))) rfl
  · exact L B (M c149 (M c188 (P h Z))) rfl
  · exact L B (M c183 (M c184 (P h Z))) rfl
  · exact L B (P c149 (P c188 (M h Z))) rfl
  · exact L B (M c184 (P h Z)) rfl
  · exact L B (P c188 (M h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (M c180 (P h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c185 (P h Z)) rfl
 · exact absurd h c188
 · exact L B (M c149 (M c179 (M c183 (P h Z)))) rfl
 · exact absurd h c187
 · exact L B (M c149 (P h Z)) rfl
 · exact absurd h c186
 · exact L B (M c1 (P h Z)) rfl
 · exact L B (P c180 (M h Z)) rfl
 · exact L B (M c184 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s66 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c180 : Q y true 0 1 2 6) (c181 : Q y false 0 2 4 6) (c182 : Q y false 0 1 5 6) (c183 : Q y false 3 4 5 6) (c184 : Q y false 0 1 3 4) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y false 1 2 5 6) with c185 | c185
 ·
  exact s67 y B H c1 c149 c178 c179 c180 c181 c182 c183 c184 c185 c2 c84 c150 c167
 rcases em (Q y false 2 3 5 6) with c189 | c189
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c179 (M c183 (P h Z))) rfl
  · exact LN B 1 1 c185 (P c179 (P c182 (M c184 Z))) (M c1 (M c179 (P c184 (M c189 Z)))) rfl rfl
  · exact L B (M c149 (M c179 (M c183 (P h Z)))) rfl
  · exact LN B 1 1 c185 (P c179 (P c182 (M c184 Z))) (M c1 (M c179 (P c184 (M c189 Z)))) rfl rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact LN B 1 1 c185 (P c179 (P c183 Z)) (M c1 (M c179 (P c184 (M c189 Z)))) rfl rfl
  · exact L B (M c182 (P h Z)) rfl
  · exact L B (P c180 (M h Z)) rfl
  · exact L B (M c184 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c189
 · exact L B (P c182 (P h Z)) rfl
 · exact L B (P c179 (P c182 (M c184 (M h Z)))) rfl
 · exact L B (P c182 (P h Z)) rfl
 · exact absurd h c185
 · exact L B (P c182 (P h Z)) rfl
 · exact L B (M c179 (P h Z)) rfl
 · exact L B (P c149 (P c179 (P c182 (P h Z)))) rfl
 · exact L B (M c179 (P h Z)) rfl
 · exact L B (P c149 (P c179 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s65 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c180 : Q y true 0 1 2 6) (c181 : Q y false 0 2 4 6) (c182 : Q y false 0 1 5 6) (c183 : Q y false 3 4 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y false 0 1 3 4) with c184 | c184
 ·
  exact s66 y B H c1 c149 c178 c179 c180 c181 c182 c183 c184 c2 c84 c150 c167
 rcases em (Q y false 1 3 4 6) with c190 | c190
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c179 (M c183 (P h Z))) rfl
  · exact LN B 1 1 c184 (P c182 (M c183 Z)) (M c182 (P c183 Z)) rfl rfl
  · exact L B (M c149 (M c179 (M c183 (P h Z)))) rfl
  · exact LN B 1 1 c184 (P c182 (M c183 Z)) (M c182 (P c183 Z)) rfl rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact LN B 1 1 c184 (P c182 (M c183 Z)) (M c182 (P c183 Z)) rfl rfl
  · exact L B (M c182 (P h Z)) rfl
  · exact L B (P c180 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c190
 · exact L B (P c149 (P c182 (P h Z))) rfl
 · exact L B (P c149 (P c179 (P c183 (M h Z)))) rfl
 · exact L B (P c149 (P c179 (P c183 (P h Z)))) rfl
 · exact L B (M c149 (P h Z)) rfl
 · exact L B (M c180 (P h Z)) rfl
 · exact L B (M c182 (P h Z)) rfl
 · exact L B (M c180 (P h Z)) rfl
 · exact absurd h c184
 · exact L B (P c182 (M c183 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s64 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c180 : Q y true 0 1 2 6) (c181 : Q y false 0 2 4 6) (c182 : Q y false 0 1 5 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y false 3 4 5 6) with c183 | c183
 ·
  exact s65 y B H c1 c149 c178 c179 c180 c181 c182 c183 c2 c84 c150 c167
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c183
 · exact L B (P c182 (P h Z)) rfl
 · exact L B (P c182 (M h Z)) rfl
 · exact L B (M c180 (P h Z)) rfl
 · exact L B (P c182 (M h Z)) rfl
 · exact L B (P c182 (P h Z)) rfl
 · exact L B (M c1 (P c149 (P c182 (M h Z)))) rfl
 · exact L B (M c1 (P c149 (P c182 (P h Z)))) rfl
 · exact L B (P c149 (M h Z)) rfl
 · exact L B (P c149 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s63 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c180 : Q y true 0 1 2 6) (c181 : Q y false 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y false 0 1 5 6) with c182 | c182
 ·
  exact s64 y B H c1 c149 c178 c179 c180 c181 c182 c2 c84 c150 c167
 rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c149 (P c181 (M h Z))) rfl
 · exact L B (P c181 (P h Z)) rfl
 · exact L B (P c181 (M h Z)) rfl
 · exact L B (P c181 (P h Z)) rfl
 · exact absurd h c182
 · exact L B (M c180 (P h Z)) rfl
 · exact L B (M c149 (P h Z)) rfl
 · exact L B (M c180 (P h Z)) rfl
 · exact L B (M c149 (P h Z)) rfl
 · exact L B (M c180 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s62 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c178 : Q y false 0 2 3 5) (c179 : Q y false 1 2 3 4) (c180 : Q y true 0 1 2 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) (c167 : N (Q y true 0 2 3 4)) : False := by
 rcases em (Q y false 0 2 4 6) with c181 | c181
 ·
  exact s63 y B H c1 c149 c178 c179 c180 c181 c2 c84 c150 c167
 rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c149 (P h Z))) rfl
 · exact L B (M c180 (P h Z)) rfl
 · exact G B (P c149 (P c178 (P c180 (P h Z)))) rfl
 · exact L B (M c180 (P h Z)) rfl
 · exact absurd h c181
 · exact L B (M c180 (P h Z)) rfl
 · exact L B (M c149 (M c179 (P h Z))) rfl
 · exact L B (M c180 (P h Z)) rfl
 · exact absurd h c150
 · exact absurd h c167

set_option maxHeartbeats 4000000 in
lemma s61 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c167 : Q y true 0 2 3 4) (c168 : Q y true 1 2 3 5) (c169 : Q y true 0 1 4 6) (_c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c150 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y false 0 2 4 6) with c170 | c170
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c167 (M c169 (M h Z))) rfl
  · exact L B (M c169 (P h Z)) rfl
  · exact L B (P c167 (M c169 (M h Z))) rfl
  · exact L B (M c169 (P h Z)) rfl
  · exact L B (P c170 (M h Z)) rfl
  · exact L B (P c170 (P h Z)) rfl
  · exact L B (P c170 (M h Z)) rfl
  · exact L B (M c169 (P h Z)) rfl
  · exact L B (P c149 (M h Z)) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases em (Q y false 0 2 5 6) with c171 | c171
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c149 (P h Z))) rfl
  · exact L B (M c169 (P h Z)) rfl
  · exact L B (P c1 (M c171 (P h Z))) rfl
  · exact L B (M c169 (P h Z)) rfl
  · exact L B (M c171 (P h Z)) rfl
  · exact L B (M c169 (P h Z)) rfl
  · exact L B (M c171 (P h Z)) rfl
  · exact L B (P c168 (M h Z)) rfl
  · exact L B (P c167 (P h Z)) rfl
  · exact L B (M c167 (P h Z)) rfl
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c167 (M c169 (M h Z))) rfl
 · exact L B (M c169 (P h Z)) rfl
 · exact L B (P c167 (M c169 (M h Z))) rfl
 · exact L B (M c169 (P h Z)) rfl
 · exact absurd h c171
 · exact L B (M c169 (P h Z)) rfl
 · exact absurd h c170
 · exact L B (M c169 (P h Z)) rfl
 · exact L B (P c149 (M h Z)) rfl
 · exact L B (P c149 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s60 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c167 : Q y true 0 2 3 4) (c168 : Q y true 1 2 3 5) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y true 0 1 4 6) with c169 | c169
 ·
  exact s61 y B H c1 c149 c167 c168 c169 c2 c84 c150
 rcases em (Q y false 0 2 4 6) with c172 | c172
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c167 (P c172 (M h Z))) rfl
  · exact L B (P c172 (P h Z)) rfl
  · exact L B (P c172 (M h Z)) rfl
  · exact L B (P c172 (P h Z)) rfl
  · exact L B (P c172 (M h Z)) rfl
  · exact L B (P c172 (P h Z)) rfl
  · exact L B (P c172 (M h Z)) rfl
  · exact L B (P c172 (P h Z)) rfl
  · exact L B (P c149 (M h Z)) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c173 | c173
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c149 (P h Z))) rfl
  · exact L B (M c173 (P h Z)) rfl
  · exact L B (P c1 (P c173 (P h Z))) rfl
  · exact L B (M c173 (P h Z)) rfl
  · exact L B (P c173 (P h Z)) rfl
  · exact L B (M c173 (P h Z)) rfl
  · exact L B (P c167 (P h Z)) rfl
  · exact L B (M c149 (P c167 (M h Z))) rfl
  · exact L B (P c167 (P h Z)) rfl
  · exact L B (M c167 (P h Z)) rfl
 rcases em (Q y false 1 2 4 6) with c174 | c174
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c174 (M h Z)) rfl
  · exact L B (P c174 (P h Z)) rfl
  · exact L B (P c174 (M h Z)) rfl
  · exact L B (P c174 (P h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact absurd h c169
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (P c167 (M h Z)) rfl
  · exact L B (P c167 (P h Z)) rfl
  · exact L B (P c168 (P c174 (M h Z))) rfl
 rcases em (Q y true 1 2 4 6) with c175 | c175
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c175 (P h Z)) rfl
  · exact L B (P c175 (M h Z)) rfl
  · exact L B (P c175 (P h Z)) rfl
  · exact L B (P c175 (M h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (P c175 (M h Z)) rfl
  · exact L B (P c175 (K 2 h Z)) rfl
  · exact L B (P c175 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c174
 · exact absurd h c175
 · exact absurd h c172
 · exact absurd h c173
 · exact L B (M c149 (P h Z)) rfl
 · exact absurd h c169
 · exact L B (M c149 (P h Z)) rfl
 · exact L B (P c167 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s59 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c167 : Q y true 0 2 3 4) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c150 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y true 1 2 3 5) with c168 | c168
 ·
  exact s60 y B H c1 c149 c167 c168 c2 c84 c150
 rcases em (Q y false 1 2 4 5) with c176 | c176
 ·
  rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c176 (P h Z)) rfl
  · exact LN B 1 1 c168 (M c149 (P c167 Z)) (P c149 (M c167 Z)) rfl rfl
  · exact LN B 1 1 c168 (M c149 (P c167 Z)) (P c149 (M c167 Z)) rfl rfl
  · exact LN B 1 1 c168 (M c149 (P c167 Z)) (P c149 (M c167 Z)) rfl rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact LN B 1 1 c168 (M c149 (P c167 Z)) (P c149 (M c167 Z)) rfl rfl
  · exact L B (P c167 (P h Z)) rfl
  · exact L B (P c167 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases em (Q y false 2 3 4 5) with c177 | c177
 ·
  rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c168 (M c149 (P c167 Z)) (P c149 (M c167 Z)) rfl rfl
  · exact LN B 1 1 c168 (M c149 (P c167 Z)) (P c1 (M c167 (P c177 Z))) rfl rfl
  · exact LN B 1 1 c168 (M c149 (P c167 Z)) (P c149 (M c167 Z)) rfl rfl
  · exact LN B 1 1 c168 (M c149 (P c167 Z)) (P c1 (M c167 (P c177 Z))) rfl rfl
  · exact L B (M c1 (M c177 (P h Z))) rfl
  · exact LN B 1 1 c168 (M c149 (P c167 Z)) (P c1 (M c167 (P c177 Z))) rfl rfl
  · exact L B (P c167 (P h Z)) rfl
  · exact L B (P c167 (M h Z)) rfl
  · exact L B (P c167 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c177
 · exact L B (P c149 (P h Z)) rfl
 · exact L B (M c1 (P c149 (M h Z))) rfl
 · exact L B (P c149 (P h Z)) rfl
 · exact absurd h c176
 · exact L B (P c149 (P h Z)) rfl
 · exact L B (P c167 (P h Z)) rfl
 · exact absurd h c168
 · exact L B (P c167 (P h Z)) rfl
 · exact L B (M c167 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s58 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c150 : Q y false 0 2 3 4) (c158 : Q y false 2 3 4 5) (c161 : Q y true 0 1 4 6) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c151 : N (Q y false 1 2 4 5)) (_c159 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 0 1 5 6) with c162 | c162
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c150 (P c162 (M h Z))) rfl
  · exact L B (P c162 (P h Z)) rfl
  · exact L B (P c162 (M h Z)) rfl
  · exact L B (P c162 (P h Z)) rfl
  · exact L B (P c162 (M h Z)) rfl
  · exact L B (P c162 (P h Z)) rfl
  · exact LN B 1 1 c151 (M c162 (P h Z)) (P c162 (M h Z)) rfl rfl
  · exact L B (M c161 (P h Z)) rfl
  · exact L B (P c1 (P c158 (M h Z))) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c2 (P c149 (M c150 (P c161 (P h Z)))) (M c149 (P c150 (M c161 (M h Z)))) rfl rfl
 · exact L B (M c161 (P h Z)) rfl
 · exact LN B 1 1 c84 (M c150 (P c161 (P h Z))) (P c150 (M c161 (M h Z))) rfl rfl
 · exact L B (M c161 (P h Z)) rfl
 · exact absurd h c162
 · exact L B (M c161 (P h Z)) rfl
 · exact L B (M c150 (P h Z)) rfl
 · exact L B (P c161 (M h Z)) rfl
 · exact L B (M c150 (P h Z)) rfl
 · exact LN B 1 1 c2 (P c158 (P h Z)) (M c158 (M h Z)) rfl rfl

set_option maxHeartbeats 4000000 in
lemma s57 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (_c149 : Q y false 0 1 4 5) (c150 : Q y false 0 2 3 4) (c158 : Q y false 2 3 4 5) (c159 : Q y true 0 1 2 6) (_c2 : N (Q y true 0 1 2 4)) (_c84 : N (Q y true 0 1 2 5)) (_c151 : N (Q y false 1 2 4 5)) : False := by
 rcases em (Q y false 0 3 4 6) with c160 | c160
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c158 (P h Z)) rfl
  · exact L B (P c160 (P h Z)) rfl
  · exact L B (M c160 (P h Z)) rfl
  · exact L B (P c160 (P h Z)) rfl
  · exact L B (M c160 (P h Z)) rfl
  · exact L B (P c1 (P c160 (P h Z))) rfl
  · exact L B (M c160 (P h Z)) rfl
  · exact L B (M c159 (P h Z)) rfl
  · exact L B (M c150 (P h Z)) rfl
  · exact L B (P c150 (P h Z)) rfl
 rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact G B (P c150 (P c159 (P h Z))) rfl
 · exact L B (M c159 (P h Z)) rfl
 · exact absurd h c160
 · exact L B (M c159 (P h Z)) rfl
 · exact L B (M c1 (M c158 (P h Z))) rfl
 · exact L B (M c159 (P h Z)) rfl
 · exact L B (M c150 (P h Z)) rfl
 · exact L B (M c159 (P h Z)) rfl
 · exact L B (M c150 (P h Z)) rfl
 · exact L B (M c159 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s56 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c150 : Q y false 0 2 3 4) (c158 : Q y false 2 3 4 5) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (c151 : N (Q y false 1 2 4 5)) : False := by
 rcases em (Q y true 0 1 2 6) with c159 | c159
 ·
  exact s57 y B H c1 c149 c150 c158 c159 c2 c84 c151
 rcases em (Q y true 0 1 4 6) with c161 | c161
 ·
  exact s58 y B H c1 c149 c150 c158 c161 c2 c84 c151 c159
 rcases em (Q y false 0 2 4 6) with c163 | c163
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c150 (P c163 (M h Z))) rfl
  · exact L B (P c163 (P h Z)) rfl
  · exact L B (P c163 (M h Z)) rfl
  · exact L B (P c163 (P h Z)) rfl
  · exact L B (P c163 (M h Z)) rfl
  · exact L B (P c163 (P h Z)) rfl
  · exact L B (P c163 (M h Z)) rfl
  · exact L B (P c163 (P h Z)) rfl
  · exact L B (P c149 (M h Z)) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c164 | c164
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c149 (P h Z))) rfl
  · exact L B (M c164 (P h Z)) rfl
  · exact L B (P c1 (P c164 (P h Z))) rfl
  · exact L B (M c164 (P h Z)) rfl
  · exact L B (P c164 (P h Z)) rfl
  · exact L B (M c164 (P h Z)) rfl
  · exact L B (P c164 (P h Z)) rfl
  · exact L B (M c150 (P c164 (M h Z))) rfl
  · exact L B (M c150 (P h Z)) rfl
  · exact L B (P c150 (P h Z)) rfl
 rcases em (Q y false 1 2 4 6) with c165 | c165
 ·
  rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c150 (P c165 (M h Z))) rfl
  · exact L B (K 2 c165 (P h Z)) rfl
  · exact L B (P c165 (M h Z)) rfl
  · exact L B (P c165 (P h Z)) rfl
  · exact L B (P c165 (M h Z)) rfl
  · exact L B (P c165 (P h Z)) rfl
  · exact absurd h c163
  · exact absurd h c164
  · exact L B (P c165 (M h Z)) rfl
  · exact L B (P c165 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c166 | c166
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c166 (P h Z)) rfl
  · exact L B (P c166 (M h Z)) rfl
  · exact L B (P c166 (P h Z)) rfl
  · exact L B (P c166 (M h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (P c166 (M h Z)) rfl
  · exact L B (P c166 (K 2 h Z)) rfl
  · exact L B (P c166 (M h Z)) rfl
  · exact L B (M c150 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c165
 · exact absurd h c166
 · exact absurd h c163
 · exact absurd h c164
 · exact L B (M c1 (M c158 (P h Z))) rfl
 · exact absurd h c161
 · exact L B (M c150 (P h Z)) rfl
 · exact absurd h c159
 · exact L B (M c150 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s55 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c150 : Q y false 0 2 3 4) (c151 : Q y false 1 2 4 5) (c153 : Q y true 0 1 4 6) (_c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) (_c152 : N (Q y true 0 1 2 6)) : False := by
 rcases em (Q y false 0 1 5 6) with c154 | c154
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c150 (P c154 (M h Z))) rfl
  · exact L B (P c154 (P h Z)) rfl
  · exact L B (P c154 (M h Z)) rfl
  · exact L B (P c154 (P h Z)) rfl
  · exact L B (P c154 (M h Z)) rfl
  · exact L B (P c154 (P h Z)) rfl
  · exact L B (M c1 (P c149 (P c154 (M h Z)))) rfl
  · exact L B (M c1 (P c149 (P c154 (P h Z)))) rfl
  · exact L B (P c149 (M h Z)) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact G B (P c1 (P c151 (P c153 (P h Z)))) rfl
 · exact L B (M c153 (P h Z)) rfl
 · exact LN B 1 1 c84 (M c150 (P c153 (P h Z))) (P c150 (M c153 (M h Z))) rfl rfl
 · exact L B (M c153 (P h Z)) rfl
 · exact absurd h c154
 · exact L B (M c153 (P h Z)) rfl
 · exact L B (M c150 (P h Z)) rfl
 · exact L B (P c153 (M h Z)) rfl
 · exact L B (M c150 (P h Z)) rfl
 · exact G B (P c150 (P c151 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s54 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c149 : Q y false 0 1 4 5) (c150 : Q y false 0 2 3 4) (c151 : Q y false 1 2 4 5) (c2 : N (Q y true 0 1 2 4)) (c84 : N (Q y true 0 1 2 5)) : False := by
 rcases em (Q y true 0 1 2 6) with c152 | c152
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c149 (P h Z))) rfl
  · exact L B (M c152 (P h Z)) rfl
  · exact G B (P c150 (P c152 (P h Z))) rfl
  · exact L B (M c152 (P h Z)) rfl
  · exact L B (M c151 (P h Z)) rfl
  · exact L B (M c152 (P h Z)) rfl
  · exact L B (M c150 (P h Z)) rfl
  · exact L B (M c152 (P h Z)) rfl
  · exact L B (M c150 (P h Z)) rfl
  · exact L B (P c150 (P h Z)) rfl
 rcases em (Q y true 0 1 4 6) with c153 | c153
 ·
  exact s55 y B H c1 c149 c150 c151 c153 c2 c84 c152
 rcases em (Q y false 0 2 4 6) with c155 | c155
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c150 (P c155 (M h Z))) rfl
  · exact L B (P c155 (P h Z)) rfl
  · exact L B (P c155 (M h Z)) rfl
  · exact L B (P c155 (P h Z)) rfl
  · exact L B (P c155 (M h Z)) rfl
  · exact L B (P c155 (P h Z)) rfl
  · exact L B (P c155 (M h Z)) rfl
  · exact L B (P c155 (P h Z)) rfl
  · exact L B (P c149 (M h Z)) rfl
  · exact L B (P c149 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c156 | c156
 ·
  rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c149 (P h Z))) rfl
  · exact L B (M c156 (P h Z)) rfl
  · exact L B (P c1 (P c156 (P h Z))) rfl
  · exact L B (M c156 (P h Z)) rfl
  · exact L B (M c151 (P h Z)) rfl
  · exact L B (M c156 (P h Z)) rfl
  · exact L B (P c156 (P h Z)) rfl
  · exact L B (M c150 (P c156 (M h Z))) rfl
  · exact L B (M c150 (P h Z)) rfl
  · exact L B (P c150 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c157 | c157
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c151 (P h Z)) rfl
  · exact L B (P c157 (M h Z)) rfl
  · exact L B (P c157 (P h Z)) rfl
  · exact L B (P c157 (M h Z)) rfl
  · exact L B (M c149 (P h Z)) rfl
  · exact L B (P c157 (M h Z)) rfl
  · exact L B (P c157 (K 2 h Z)) rfl
  · exact L B (P c157 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c151 (P h Z)) rfl
 · exact absurd h c157
 · exact absurd h c155
 · exact absurd h c156
 · exact L B (M c149 (P h Z)) rfl
 · exact absurd h c153
 · exact L B (M c150 (P h Z)) rfl
 · exact absurd h c152
 · exact L B (M c150 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s53 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c144 : Q y false 1 3 4 5) (c145 : Q y false 0 2 4 5) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (_c110 : N (Q y false 0 1 3 5)) (_c111 : N (Q y false 0 1 4 5)) (c143 : N (Q y false 0 3 4 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c146 | c146
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c84 (P c146 (P h Z))) rfl
  · exact L B (M c146 (P h Z)) rfl
  · exact L B (P c84 (M c146 (M h Z))) rfl
  · exact L B (M c146 (P h Z)) rfl
  · exact G B (P c144 (P c146 (P h Z))) rfl
  · exact L B (M c146 (P h Z)) rfl
  · exact L B (M c84 (M c145 (P c146 (P h Z)))) rfl
  · exact L B (M c146 (P h Z)) rfl
  · exact absurd h c143
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c147 | c147
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c144 (P h Z)) rfl
  · exact L B (M c147 (P h Z)) rfl
  · exact L B (M c84 (M c145 (P c147 (P h Z)))) rfl
  · exact L B (M c147 (P h Z)) rfl
  · exact L B (P c147 (P h Z)) rfl
  · exact absurd h c146
  · exact L B (P c147 (P h Z)) rfl
  · exact L B (P c147 (M h Z)) rfl
  · exact absurd h c85
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c148 | c148
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c148 (P h Z)) rfl
  · exact L B (P c148 (M h Z)) rfl
  · exact L B (M c1 (M c144 (P h Z))) rfl
  · exact L B (P c148 (M h Z)) rfl
  · exact L B (P c148 (K 2 h Z)) rfl
  · exact L B (P c148 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c148 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c145 (P h Z)) rfl
 · exact absurd h c148
 · exact L B (M c145 (P h Z)) rfl
 · exact absurd h c147
 · exact L B (M c1 (M c144 (P h Z))) rfl
 · exact absurd h c146
 · exact L B (M c145 (P h Z)) rfl
 · exact L B (P c84 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s52 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c144 : Q y false 1 3 4 5) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (c110 : N (Q y false 0 1 3 5)) (c111 : N (Q y false 0 1 4 5)) (c143 : N (Q y false 0 3 4 5)) : False := by
 rcases em (Q y false 0 2 4 5) with c145 | c145
 ·
  exact s53 y B H c1 c84 c144 c145 c2 c85 c110 c111 c143
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c144 (P h Z)) rfl
 · exact L B (M c84 (P h Z)) rfl
 · exact absurd h c143
 · exact L B (M c84 (P h Z)) rfl
 · exact absurd h c145
 · exact L B (M c84 (P h Z)) rfl
 · exact L B (M c1 (M c144 (P h Z))) rfl
 · exact L B (M c84 (P h Z)) rfl
 · exact G B (P c84 (P c144 (P h Z))) rfl
 · exact L B (M c84 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s51 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c111 : Q y false 0 1 4 5) (c137 : Q y false 2 3 4 5) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (c110 : N (Q y false 0 1 3 5)) (c112 : N (Q y false 0 2 3 4)) (c124 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c138 | c138
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c124 (P c1 (M c84 (P c137 (P c138 (P h Z))))) (M c1 (P c84 (M c137 (M c138 (M h Z))))) rfl rfl
  · exact L B (M c138 (P h Z)) rfl
  · exact LN B 1 1 c112 (M c84 (P c138 (P h Z))) (P c84 (M c138 (M h Z))) rfl rfl
  · exact L B (M c138 (P h Z)) rfl
  · exact L B (M c1 (M c84 (P c138 (P h Z)))) rfl
  · exact L B (M c138 (P h Z)) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact L B (P c138 (M h Z)) rfl
  · exact absurd h c110
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y false 0 2 4 6) with c139 | c139
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c124 (P c139 (M h Z)) (M c139 (P h Z)) rfl rfl
  · exact L B (P c139 (P h Z)) rfl
  · exact L B (P c139 (M h Z)) rfl
  · exact L B (P c139 (P h Z)) rfl
  · exact L B (P c139 (M h Z)) rfl
  · exact L B (P c139 (P h Z)) rfl
  · exact L B (P c139 (M h Z)) rfl
  · exact L B (P c139 (P h Z)) rfl
  · exact L B (P c111 (M h Z)) rfl
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c140 | c140
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c84 (P c140 (P h Z))) rfl
  · exact L B (M c140 (P h Z)) rfl
  · exact L B (M c84 (M c111 (P c140 (P h Z)))) rfl
  · exact L B (M c140 (P h Z)) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact absurd h c138
  · exact L B (M c111 (P h Z)) rfl
  · exact L B (P c140 (M h Z)) rfl
  · exact absurd h c85
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y false 1 2 4 6) with c141 | c141
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c111 (P h Z))) rfl
  · exact L B (K 2 c141 (P h Z)) rfl
  · exact L B (P c141 (M h Z)) rfl
  · exact L B (P c141 (P h Z)) rfl
  · exact absurd h c139
  · exact absurd h c140
  · exact G B (P c84 (P c137 (P c141 (P h Z)))) rfl
  · exact L B (M c84 (P c141 (P h Z))) rfl
  · exact absurd h c112
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c142 | c142
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c142 (P h Z)) rfl
  · exact L B (P c142 (M h Z)) rfl
  · exact L B (P c142 (P h Z)) rfl
  · exact L B (P c142 (M h Z)) rfl
  · exact L B (M c1 (M c137 (P h Z))) rfl
  · exact L B (P c142 (M h Z)) rfl
  · exact L B (P c142 (K 2 h Z)) rfl
  · exact L B (P c142 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c141
 · exact absurd h c142
 · exact absurd h c139
 · exact absurd h c140
 · exact L B (M c1 (M c137 (P h Z))) rfl
 · exact absurd h c138
 · exact L B (M c1 (P h Z)) rfl
 · exact L B (P c84 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s50 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (_c84 : Q y true 0 1 2 5) (c111 : Q y false 0 1 4 5) (_c124 : Q y false 0 2 3 5) (c125 : Q y false 1 2 3 4) (c126 : Q y true 0 1 4 6) (c127 : Q y false 1 3 5 6) (_c128 : Q y false 0 3 4 6) (_c129 : Q y false 2 4 5 6) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (c110 : N (Q y false 0 1 3 5)) (_c112 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y true 0 2 4 7) with c130 | c130
 ·
  rcases H.h01347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c127 (P h Z)) rfl
  · exact L B (M c130 (P h Z)) rfl
  · exact L B (M c111 (M c127 (P h Z))) rfl
  · exact L B (M c130 (P h Z)) rfl
  · exact L B (M c1 (M c127 (P h Z))) rfl
  · exact L B (P c126 (M h Z)) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact L B (P c126 (M h Z)) rfl
  · exact absurd h c85
  · exact L B (P c125 (M c126 (M c127 (P h Z)))) rfl
 rcases em (Q y true 1 2 4 7) with c131 | c131
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c127 (P h Z)) rfl
  · exact L B (M c131 (P h Z)) rfl
  · exact L B (M c126 (M c127 (P c131 (P h Z)))) rfl
  · exact L B (M c1 (M c131 (P h Z))) rfl
  · exact L B (M c126 (P c131 (P h Z))) rfl
  · exact L B (P c111 (P c131 (M h Z))) rfl
  · exact L B (P c131 (K 2 h Z)) rfl
  · exact L B (P c126 (M h Z)) rfl
  · exact absurd h c110
  · exact L B (P c125 (M c126 (M c127 (P h Z)))) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c127 (P h Z)) rfl
 · exact absurd h c131
 · exact L B (M c1 (M c127 (P h Z))) rfl
 · exact absurd h c130
 · exact L B (M c111 (P h Z)) rfl
 · exact L B (P c126 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact L B (P c126 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s49 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c111 : Q y false 0 1 4 5) (c124 : Q y false 0 2 3 5) (c125 : Q y false 1 2 3 4) (c126 : Q y true 0 1 4 6) (c127 : Q y false 1 3 5 6) (c128 : Q y false 0 3 4 6) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (c110 : N (Q y false 0 1 3 5)) (c112 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y false 2 4 5 6) with c129 | c129
 ·
  exact s50 y B H c1 c84 c111 c124 c125 c126 c127 c128 c129 c2 c85 c110 c112
 rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c129
 · exact L B (M c126 (P h Z)) rfl
 · exact L B (P c127 (M h Z)) rfl
 · exact L B (M c126 (P h Z)) rfl
 · exact L B (M c127 (P h Z)) rfl
 · exact L B (M c126 (P h Z)) rfl
 · exact L B (M c127 (P h Z)) rfl
 · exact L B (M c126 (P h Z)) rfl
 · exact G B (P c1 (P c84 (P c125 (P h Z)))) rfl
 · exact L B (M c126 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s48 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c111 : Q y false 0 1 4 5) (c124 : Q y false 0 2 3 5) (c125 : Q y false 1 2 3 4) (c126 : Q y true 0 1 4 6) (c127 : Q y false 1 3 5 6) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (c110 : N (Q y false 0 1 3 5)) (c112 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y false 0 3 4 6) with c128 | c128
 ·
  exact s49 y B H c1 c84 c111 c124 c125 c126 c127 c128 c2 c85 c110 c112
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c125 (M c127 (P h Z))) rfl
 · exact L B (M c126 (P h Z)) rfl
 · exact L B (P c127 (M h Z)) rfl
 · exact L B (M c126 (P h Z)) rfl
 · exact L B (P c127 (M h Z)) rfl
 · exact L B (M c126 (P h Z)) rfl
 · exact absurd h c128
 · exact L B (M c126 (P h Z)) rfl
 · exact L B (P c111 (M h Z)) rfl
 · exact L B (M c126 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s47 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c111 : Q y false 0 1 4 5) (c124 : Q y false 0 2 3 5) (c125 : Q y false 1 2 3 4) (c126 : Q y true 0 1 4 6) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (c110 : N (Q y false 0 1 3 5)) (c112 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y false 1 3 5 6) with c127 | c127
 ·
  exact s48 y B H c1 c84 c111 c124 c125 c126 c127 c2 c85 c110 c112
 rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c127
 · exact L B (M c126 (P h Z)) rfl
 · exact L B (P c84 (P c125 (M c126 (M h Z)))) rfl
 · exact L B (M c126 (P h Z)) rfl
 · exact L B (M c1 (M c84 (P c126 (P h Z)))) rfl
 · exact L B (M c126 (P h Z)) rfl
 · exact L B (M c111 (P h Z)) rfl
 · exact L B (P c126 (M h Z)) rfl
 · exact absurd h c110
 · exact L B (M c84 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s46 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c111 : Q y false 0 1 4 5) (c124 : Q y false 0 2 3 5) (c125 : Q y false 1 2 3 4) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (c110 : N (Q y false 0 1 3 5)) (c112 : N (Q y false 0 2 3 4)) : False := by
 rcases em (Q y true 0 1 4 6) with c126 | c126
 ·
  exact s47 y B H c1 c84 c111 c124 c125 c126 c2 c85 c110 c112
 rcases em (Q y false 0 2 4 6) with c132 | c132
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c1 (P c132 (M h Z))) rfl
  · exact L B (P c132 (P h Z)) rfl
  · exact L B (P c132 (M h Z)) rfl
  · exact L B (P c132 (P h Z)) rfl
  · exact G B (P c1 (P c84 (P c125 (P c132 (P h Z))))) rfl
  · exact L B (M c1 (M c84 (M c125 (P c132 (P h Z))))) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact G B (P c125 (P c132 (P h Z))) rfl
  · exact absurd h c110
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c133 | c133
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c84 (P c133 (P h Z))) rfl
  · exact L B (M c133 (P h Z)) rfl
  · exact L B (M c84 (M c111 (P c133 (P h Z)))) rfl
  · exact L B (M c133 (P h Z)) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact absurd h c126
  · exact L B (M c111 (P h Z)) rfl
  · exact L B (P c133 (M h Z)) rfl
  · exact absurd h c85
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y false 1 2 4 6) with c134 | c134
 ·
  rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c111 (P h Z))) rfl
  · exact L B (K 2 c134 (P h Z)) rfl
  · exact L B (P c134 (M h Z)) rfl
  · exact L B (P c134 (P h Z)) rfl
  · exact absurd h c132
  · exact absurd h c133
  · exact L B (M c111 (M c125 (P h Z))) rfl
  · exact L B (M c84 (P c134 (P h Z))) rfl
  · exact absurd h c112
  · exact L B (P c125 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c135 | c135
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c135 (P h Z)) rfl
  · exact L B (P c135 (M h Z)) rfl
  · exact L B (P c135 (P h Z)) rfl
  · exact L B (P c135 (M h Z)) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact L B (P c135 (M h Z)) rfl
  · exact L B (P c135 (K 2 h Z)) rfl
  · exact L B (P c135 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c134
 · exact absurd h c135
 · exact absurd h c132
 · exact absurd h c133
 · exact L B (M c111 (P h Z)) rfl
 · exact absurd h c126
 · exact L B (M c111 (P h Z)) rfl
 · exact L B (P c84 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s45 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c111 : Q y false 0 1 4 5) (c112 : Q y false 0 2 3 4) (c118 : Q y false 2 3 4 5) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (c110 : N (Q y false 0 1 3 5)) (c113 : N (Q y false 1 2 4 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c119 | c119
 ·
  rcases H.h13456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c84 (P c119 (P h Z))) rfl
  · exact L B (M c119 (P h Z)) rfl
  · exact L B (P c84 (M c119 (M h Z))) rfl
  · exact L B (M c119 (P h Z)) rfl
  · exact L B (M c84 (M c112 (P c119 (P h Z)))) rfl
  · exact L B (M c119 (P h Z)) rfl
  · exact L B (M c84 (M c112 (P c119 (P h Z)))) rfl
  · exact L B (M c119 (P h Z)) rfl
  · exact L B (M c1 (P c111 (M h Z))) rfl
  · exact L B (P c111 (P h Z)) rfl
 rcases em (Q y false 0 2 4 6) with c120 | c120
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c1 (P c120 (M h Z))) rfl
  · exact L B (P c120 (P h Z)) rfl
  · exact L B (P c120 (M h Z)) rfl
  · exact L B (P c120 (P h Z)) rfl
  · exact LN B 1 1 c113 (P c120 (M h Z)) (M c120 (P h Z)) rfl rfl
  · exact L B (M c84 (M c112 (P c120 (P h Z)))) rfl
  · exact L B (M c112 (P h Z)) rfl
  · exact LN B 1 1 c113 (M c1 (M c84 (P c120 (P h Z)))) (P c84 (P c111 (M c118 (M c120 (M h Z))))) rfl rfl
  · exact absurd h c110
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c121 | c121
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c121 (P h Z))) rfl
  · exact L B (M c121 (P h Z)) rfl
  · exact L B (M c84 (M c112 (P c121 (P h Z)))) rfl
  · exact L B (M c121 (P h Z)) rfl
  · exact L B (M c1 (M c118 (P h Z))) rfl
  · exact absurd h c119
  · exact L B (P c121 (P h Z)) rfl
  · exact L B (P c121 (M h Z)) rfl
  · exact absurd h c85
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y false 1 2 4 6) with c122 | c122
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c122 (M h Z)) rfl
  · exact L B (P c122 (P h Z)) rfl
  · exact L B (P c122 (M h Z)) rfl
  · exact L B (P c122 (P h Z)) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact absurd h c119
  · exact L B (M c112 (P h Z)) rfl
  · exact G B (P c112 (P c122 (P h Z))) rfl
  · exact absurd h c85
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c123 | c123
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c123 (P h Z)) rfl
  · exact L B (P c123 (M h Z)) rfl
  · exact L B (P c123 (P h Z)) rfl
  · exact L B (P c123 (M h Z)) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact L B (P c123 (M h Z)) rfl
  · exact L B (P c123 (K 2 h Z)) rfl
  · exact L B (P c123 (M h Z)) rfl
  · exact L B (M c112 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c122
 · exact absurd h c123
 · exact absurd h c120
 · exact absurd h c121
 · exact L B (M c111 (P h Z)) rfl
 · exact absurd h c119
 · exact L B (M c112 (P h Z)) rfl
 · exact L B (P c84 (M h Z)) rfl
 · exact L B (M c112 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s44 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c111 : Q y false 0 1 4 5) (c112 : Q y false 0 2 3 4) (c113 : Q y false 1 2 4 5) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (_c110 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c114 | c114
 ·
  rcases H.h13456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c84 (P c114 (P h Z))) rfl
  · exact L B (M c114 (P h Z)) rfl
  · exact L B (P c84 (M c114 (M h Z))) rfl
  · exact L B (M c114 (P h Z)) rfl
  · exact L B (M c84 (M c112 (P c114 (P h Z)))) rfl
  · exact L B (M c114 (P h Z)) rfl
  · exact L B (M c84 (M c112 (P c114 (P h Z)))) rfl
  · exact L B (M c114 (P h Z)) rfl
  · exact L B (M c1 (P c111 (M h Z))) rfl
  · exact L B (P c111 (P h Z)) rfl
 rcases em (Q y false 0 2 4 6) with c115 | c115
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c112 (P c115 (M h Z))) rfl
  · exact L B (P c115 (P h Z)) rfl
  · exact L B (P c115 (M h Z)) rfl
  · exact L B (P c115 (P h Z)) rfl
  · exact L B (P c115 (M h Z)) rfl
  · exact L B (P c115 (P h Z)) rfl
  · exact L B (P c115 (M h Z)) rfl
  · exact L B (P c115 (P h Z)) rfl
  · exact L B (P c113 (M h Z)) rfl
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c116 | c116
 ·
  rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c116 (P h Z))) rfl
  · exact L B (M c116 (P h Z)) rfl
  · exact L B (M c84 (M c112 (P c116 (P h Z)))) rfl
  · exact L B (M c116 (P h Z)) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact absurd h c114
  · exact L B (P c116 (P h Z)) rfl
  · exact L B (P c116 (M h Z)) rfl
  · exact absurd h c85
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c117 | c117
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c113 (P h Z)) rfl
  · exact L B (P c117 (M h Z)) rfl
  · exact L B (P c117 (P h Z)) rfl
  · exact L B (P c117 (M h Z)) rfl
  · exact L B (M c111 (P h Z)) rfl
  · exact L B (P c117 (M h Z)) rfl
  · exact L B (P c117 (K 2 h Z)) rfl
  · exact L B (P c117 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c113 (P h Z)) rfl
 · exact absurd h c117
 · exact absurd h c115
 · exact absurd h c116
 · exact L B (M c111 (P h Z)) rfl
 · exact absurd h c114
 · exact L B (M c112 (P h Z)) rfl
 · exact L B (P c84 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s43 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c111 : Q y false 0 1 4 5) (c112 : Q y false 0 2 3 4) (c2 : N (Q y true 0 1 2 4)) (c85 : N (Q y false 0 1 3 4)) (c110 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 1 2 4 5) with c113 | c113
 ·
  exact s44 y B H c1 c84 c111 c112 c113 c2 c85 c110
 rcases em (Q y false 2 3 4 5) with c118 | c118
 ·
  exact s45 y B H c1 c84 c111 c112 c118 c2 c85 c110 c113
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c118
 · exact L B (M c84 (P h Z)) rfl
 · exact L B (M c1 (P c111 (M h Z))) rfl
 · exact L B (P c111 (P h Z)) rfl
 · exact absurd h c113
 · exact L B (P c111 (P h Z)) rfl
 · exact L B (M c112 (P h Z)) rfl
 · exact L B (P c111 (P c112 (P h Z))) rfl
 · exact L B (M c112 (P h Z)) rfl
 · exact L B (P c112 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s42 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c85 : Q y false 0 1 3 4) (c100 : Q y false 0 2 4 5) (c105 : Q y false 1 3 4 5) (c2 : N (Q y true 0 1 2 4)) (_c86 : N (Q y false 0 2 3 5)) (c101 : N (Q y false 1 2 3 4)) : False := by
 rcases em (Q y true 0 1 4 6) with c106 | c106
 ·
  rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c101 (M c84 (P c106 (P h Z))) (P c84 (M c106 (M h Z))) rfl rfl
  · exact L B (M c106 (P h Z)) rfl
  · exact L B (P c84 (P c85 (M c106 (M h Z)))) rfl
  · exact L B (M c106 (P h Z)) rfl
  · exact L B (M c1 (M c84 (P c106 (P h Z)))) rfl
  · exact L B (M c106 (P h Z)) rfl
  · exact L B (M c100 (P h Z)) rfl
  · exact L B (P c106 (M h Z)) rfl
  · exact L B (M c85 (P h Z)) rfl
  · exact L B (M c84 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c107 | c107
 ·
  rcases H.h23456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c84 (P c107 (P h Z))) rfl
  · exact L B (M c107 (P h Z)) rfl
  · exact L B (M c84 (P c107 (P h Z))) rfl
  · exact L B (M c107 (P h Z)) rfl
  · exact L B (M c84 (P c107 (P h Z))) rfl
  · exact L B (M c107 (P h Z)) rfl
  · exact L B (M c105 (P h Z)) rfl
  · exact L B (M c107 (P h Z)) rfl
  · exact L B (P c1 (M c100 (P h Z))) rfl
  · exact L B (P c105 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c108 | c108
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c108 (P h Z)) rfl
  · exact L B (P c108 (M h Z)) rfl
  · exact L B (M c1 (M c105 (P h Z))) rfl
  · exact L B (P c108 (M h Z)) rfl
  · exact L B (P c108 (K 2 h Z)) rfl
  · exact L B (P c108 (M h Z)) rfl
  · exact L B (P c108 (K 2 h Z)) rfl
  · exact L B (P c84 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c100 (P h Z)) rfl
 · exact absurd h c108
 · exact L B (M c100 (P h Z)) rfl
 · exact absurd h c107
 · exact L B (M c100 (P h Z)) rfl
 · exact absurd h c106
 · exact L B (M c1 (P h Z)) rfl
 · exact L B (P c84 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s41 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c85 : Q y false 0 1 3 4) (c100 : Q y false 0 2 4 5) (_c101 : Q y false 1 2 3 4) (c2 : N (Q y true 0 1 2 4)) (_c86 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c102 | c102
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c84 (P c102 (P h Z))) rfl
  · exact L B (M c102 (P h Z)) rfl
  · exact L B (P c84 (M c102 (M h Z))) rfl
  · exact L B (M c102 (P h Z)) rfl
  · exact L B (P c84 (P c85 (M c102 (M h Z)))) rfl
  · exact L B (M c102 (P h Z)) rfl
  · exact L B (M c84 (M c100 (P c102 (P h Z)))) rfl
  · exact L B (M c102 (P h Z)) rfl
  · exact L B (P c100 (M h Z)) rfl
  · exact L B (M c102 (P h Z)) rfl
 rcases em (Q y true 0 2 4 6) with c103 | c103
 ·
  rcases H.h23456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c84 (P c103 (P h Z))) rfl
  · exact L B (M c103 (P h Z)) rfl
  · exact L B (M c84 (P c103 (P h Z))) rfl
  · exact L B (M c103 (P h Z)) rfl
  · exact L B (M c84 (P c103 (P h Z))) rfl
  · exact L B (M c103 (P h Z)) rfl
  · exact L B (M c84 (P c103 (P h Z))) rfl
  · exact L B (M c103 (P h Z)) rfl
  · exact L B (P c1 (M c100 (P h Z))) rfl
  · exact L B (P c100 (P h Z)) rfl
 rcases em (Q y true 1 2 4 6) with c104 | c104
 ·
  rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c100 (P h Z)) rfl
  · exact L B (P c104 (M h Z)) rfl
  · exact L B (P c104 (P h Z)) rfl
  · exact L B (P c104 (M h Z)) rfl
  · exact L B (M c100 (P h Z)) rfl
  · exact L B (P c104 (M h Z)) rfl
  · exact L B (P c104 (K 2 h Z)) rfl
  · exact L B (P c104 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c100 (P h Z)) rfl
 · exact absurd h c104
 · exact L B (M c100 (P h Z)) rfl
 · exact absurd h c103
 · exact L B (M c100 (P h Z)) rfl
 · exact absurd h c102
 · exact L B (M c100 (P h Z)) rfl
 · exact L B (P c84 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s40 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c85 : Q y false 0 1 3 4) (c100 : Q y false 0 2 4 5) (c2 : N (Q y true 0 1 2 4)) (c86 : N (Q y false 0 2 3 5)) : False := by
 rcases em (Q y false 1 2 3 4) with c101 | c101
 ·
  exact s41 y B H c1 c84 c85 c100 c101 c2 c86
 rcases em (Q y false 1 3 4 5) with c105 | c105
 ·
  exact s42 y B H c1 c84 c85 c100 c105 c2 c86 c101
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c100 (P h Z))) rfl
 · exact L B (P c100 (P h Z)) rfl
 · exact absurd h c105
 · exact L B (P c100 (P h Z)) rfl
 · exact L B (M c100 (P h Z)) rfl
 · exact L B (P c100 (P h Z)) rfl
 · exact L B (M c100 (P h Z)) rfl
 · exact L B (P c85 (P c100 (P h Z))) rfl
 · exact absurd h c101
 · exact L B (P c85 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s39 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c85 : Q y false 0 1 3 4) (_c86 : Q y false 0 2 3 5) (c87 : Q y false 1 2 4 5) (_c90 : Q y false 0 2 4 6) (c91 : Q y false 0 1 5 6) (c92 : Q y false 3 4 5 6) (_c93 : Q y false 1 3 4 6) (c94 : Q y false 2 3 5 6) (c2 : N (Q y true 0 1 2 4)) (c88 : N (Q y false 0 1 4 6)) (c89 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y true 0 1 4 7) with c95 | c95
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact G B (P c1 (P c87 (P c95 (P h Z)))) rfl
  · exact L B (M c95 (P h Z)) rfl
  · exact L B (P c84 (P c85 (M c95 (M h Z)))) rfl
  · exact L B (M c95 (P h Z)) rfl
  · exact L B (M c85 (M c92 (P h Z))) rfl
  · exact L B (M c95 (P h Z)) rfl
  · exact L B (M c85 (P h Z)) rfl
  · exact L B (P c95 (M h Z)) rfl
  · exact L B (M c91 (P c92 (P h Z))) rfl
  · exact L B (M c92 (M c95 (P h Z))) rfl
 rcases em (Q y true 0 2 4 7) with c96 | c96
 ·
  rcases H.h01467 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c84 (M c96 (M h Z))) rfl
  · exact L B (M c96 (P h Z)) rfl
  · exact L B (P c84 (M c96 (M h Z))) rfl
  · exact L B (M c96 (P h Z)) rfl
  · exact L B (M c1 (M c84 (M c85 (P c91 (P c96 (P h Z)))))) rfl
  · exact L B (M c87 (M c96 (P h Z))) rfl
  · exact L B (M c85 (M c92 (P h Z))) rfl
  · exact absurd h c95
  · exact absurd h c88
  · exact absurd h c89
 rcases em (Q y true 1 2 4 7) with c97 | c97
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c84 (P c97 (P h Z))) rfl
  · exact L B (M c97 (P h Z)) rfl
  · exact L B (M c84 (P c97 (P h Z))) rfl
  · exact L B (M c1 (M c97 (P h Z))) rfl
  · exact L B (M c91 (P h Z)) rfl
  · exact L B (P c87 (P c97 (M h Z))) rfl
  · exact L B (M c85 (P h Z)) rfl
  · exact L B (P c84 (M c94 (M h Z))) rfl
  · exact L B (M c1 (P c92 (M c94 (P h Z)))) rfl
  · exact L B (M c84 (P h Z)) rfl
 rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c87 (P h Z)) rfl
 · exact absurd h c97
 · exact L B (M c85 (M c87 (M c92 (P h Z)))) rfl
 · exact absurd h c96
 · exact L B (M c85 (M c92 (P h Z))) rfl
 · exact absurd h c95
 · exact L B (M c91 (P h Z)) rfl
 · exact L B (P c84 (M h Z)) rfl
 · exact L B (M c85 (P h Z)) rfl
 · exact absurd h c2

set_option maxHeartbeats 4000000 in
lemma s38 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c85 : Q y false 0 1 3 4) (c86 : Q y false 0 2 3 5) (c87 : Q y false 1 2 4 5) (c90 : Q y false 0 2 4 6) (c91 : Q y false 0 1 5 6) (c92 : Q y false 3 4 5 6) (c93 : Q y false 1 3 4 6) (c2 : N (Q y true 0 1 2 4)) (c88 : N (Q y false 0 1 4 6)) (c89 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 2 3 5 6) with c94 | c94
 ·
  exact s39 y B H c1 c84 c85 c86 c87 c90 c91 c92 c93 c94 c2 c88 c89
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c94
 · exact L B (M c84 (P c92 (P h Z))) rfl
 · exact L B (M c1 (P c91 (M h Z))) rfl
 · exact L B (M c84 (P c92 (P h Z))) rfl
 · exact G B (P c1 (P c84 (P c86 (P c91 (P h Z))))) rfl
 · exact L B (P c91 (P h Z)) rfl
 · exact L B (M c87 (P h Z)) rfl
 · exact L B (M c84 (P c91 (P h Z))) rfl
 · exact L B (M c87 (P h Z)) rfl
 · exact L B (M c84 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s37 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c85 : Q y false 0 1 3 4) (c86 : Q y false 0 2 3 5) (c87 : Q y false 1 2 4 5) (c90 : Q y false 0 2 4 6) (c91 : Q y false 0 1 5 6) (c92 : Q y false 3 4 5 6) (c2 : N (Q y true 0 1 2 4)) (c88 : N (Q y false 0 1 4 6)) (c89 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 1 3 4 6) with c93 | c93
 ·
  exact s38 y B H c1 c84 c85 c86 c87 c90 c91 c92 c93 c2 c88 c89
 rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c85 (M c92 (P h Z)))) rfl
 · exact L B (M c84 (P c91 (P h Z))) rfl
 · exact absurd h c93
 · exact L B (M c84 (P c91 (P h Z))) rfl
 · exact L B (M c87 (P h Z)) rfl
 · exact L B (M c84 (P c92 (P h Z))) rfl
 · exact L B (M c87 (P h Z)) rfl
 · exact L B (M c84 (P c91 (P h Z))) rfl
 · exact G B (P c1 (P c84 (P c87 (P h Z)))) rfl
 · exact L B (P c85 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s36 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c85 : Q y false 0 1 3 4) (c86 : Q y false 0 2 3 5) (c87 : Q y false 1 2 4 5) (c90 : Q y false 0 2 4 6) (c91 : Q y false 0 1 5 6) (c2 : N (Q y true 0 1 2 4)) (c88 : N (Q y false 0 1 4 6)) (c89 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 3 4 5 6) with c92 | c92
 ·
  exact s37 y B H c1 c84 c85 c86 c87 c90 c91 c92 c2 c88 c89
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c92
 · exact L B (P c91 (P h Z)) rfl
 · exact L B (P c91 (M h Z)) rfl
 · exact L B (P c91 (P h Z)) rfl
 · exact L B (P c91 (M h Z)) rfl
 · exact L B (P c91 (P h Z)) rfl
 · exact L B (P c87 (P c91 (M h Z))) rfl
 · exact L B (M c84 (M c85 (P c91 (P h Z)))) rfl
 · exact L B (P c87 (M h Z)) rfl
 · exact L B (P c87 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s35 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c84 : Q y true 0 1 2 5) (c85 : Q y false 0 1 3 4) (c86 : Q y false 0 2 3 5) (c87 : Q y false 1 2 4 5) (c90 : Q y false 0 2 4 6) (c2 : N (Q y true 0 1 2 4)) (c88 : N (Q y false 0 1 4 6)) (c89 : N (Q y true 0 1 4 6)) : False := by
 rcases em (Q y false 0 1 5 6) with c91 | c91
 ·
  exact s36 y B H c1 c84 c85 c86 c87 c90 c91 c2 c88 c89
 rcases H.h01456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c85 (P c90 (M h Z))) rfl
 · exact L B (P c90 (P h Z)) rfl
 · exact L B (P c90 (M h Z)) rfl
 · exact L B (P c90 (P h Z)) rfl
 · exact absurd h c91
 · exact L B (M c87 (P c90 (P h Z))) rfl
 · exact absurd h c88
 · exact absurd h c89
 · exact G B (P c1 (P c84 (P c85 (P h Z)))) rfl
 · exact L B (M c84 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s34 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c67 : Q y false 1 2 5 6) (c69 : Q y true 0 1 3 5) (c70 : Q y false 0 2 4 6) (c71 : Q y false 3 4 5 6) (c72 : Q y true 0 1 4 6) (c73 : Q y false 0 2 3 5) (c74 : Q y false 1 2 3 4) (c3 : N (Q y false 0 1 5 6)) (_c47 : N (Q y true 0 1 5 6)) (_c58 : N (Q y false 0 2 5 6)) (_c65 : N (Q y true 0 2 5 6)) (_c68 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 0 3 4 7) with c75 | c75
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (K (-2) c73 (P c74 (P c75 (M h Z))))) rfl
  · exact L B (P c75 (P h Z)) rfl
  · exact L B (P c75 (M h Z)) rfl
  · exact L B (P c75 (P h Z)) rfl
  · exact L B (P c75 (M h Z)) rfl
  · exact L B (P c75 (P h Z)) rfl
  · exact L B (P c75 (M h Z)) rfl
  · exact L B (P c75 (P h Z)) rfl
  · exact L B (P c67 (M h Z)) rfl
  · exact L B (P c71 (P c74 (P h Z))) rfl
 rcases em (Q y true 0 3 4 7) with c76 | c76
 ·
  rcases H.h04567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c1 (P c71 (K 2 c73 (M c74 (P c76 (P h Z)))))) rfl
  · exact L B (M c76 (P h Z)) rfl
  · exact L B (P c1 (P c2 (M c76 (M h Z)))) rfl
  · exact L B (M c76 (P h Z)) rfl
  · exact L B (P c69 (M c76 (M h Z))) rfl
  · exact L B (M c76 (P h Z)) rfl
  · exact L B (P c69 (M c76 (M h Z))) rfl
  · exact L B (M c76 (P h Z)) rfl
  · exact L B (P c67 (M h Z)) rfl
  · exact L B (P c71 (P h Z)) rfl
 rcases em (Q y true 1 3 4 7) with c77 | c77
 ·
  rcases H.h01267 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c69 (P c71 (P c77 (P h Z)))) rfl
  · exact L B (P c1 (M c70 (M c77 (P h Z)))) rfl
  · exact L B (M c69 (P c71 (P c77 (P h Z)))) rfl
  · exact LN B 1 1 c3 (P c1 (P c67 (M c70 (M c77 (P h Z))))) (P c2 (M c67 (M c72 (P c74 (P c77 (M h Z)))))) rfl rfl
  · exact L B (M c72 (P c77 (P h Z))) rfl
  · exact L B (P c70 (P c77 (M h Z))) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c72 (M h Z)) rfl
 rcases H.h01347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c71 (M c73 (P h Z)))) rfl
 · exact absurd h c77
 · exact absurd h c75
 · exact absurd h c76
 · exact L B (P c72 (P h Z)) rfl
 · exact L B (P c72 (M h Z)) rfl
 · exact L B (P c72 (P h Z)) rfl
 · exact L B (P c69 (M h Z)) rfl
 · exact LN B 1 1 c3 (P c67 (M c74 (P h Z))) (M c71 (M h Z)) rfl rfl
 · exact L B (M c67 (M c72 (P c74 (P h Z)))) rfl

set_option maxHeartbeats 4000000 in
lemma s33 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c67 : Q y false 1 2 5 6) (c69 : Q y true 0 1 3 5) (c70 : Q y false 0 2 4 6) (c71 : Q y false 3 4 5 6) (c72 : Q y true 0 1 4 6) (c73 : Q y false 0 2 3 5) (c3 : N (Q y false 0 1 5 6)) (c47 : N (Q y true 0 1 5 6)) (c58 : N (Q y false 0 2 5 6)) (c65 : N (Q y true 0 2 5 6)) (c68 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 1 2 3 4) with c74 | c74
 ·
  exact s34 y B H c1 c2 c67 c69 c70 c71 c72 c73 c74 c3 c47 c58 c65 c68
 rcases em (Q y false 2 3 4 5) with c78 | c78
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c67 (P h Z)) rfl
  · exact LN B 1 1 c74 (P c67 (M c71 Z)) (M c67 (P c71 Z)) rfl rfl
  · exact LN B 1 1 c74 (P c67 (M c71 Z)) (M c67 (P c71 Z)) rfl rfl
  · exact LN B 1 1 c74 (P c67 (M c71 Z)) (M c67 (P c71 Z)) rfl rfl
  · exact LN B 1 1 c74 (P c67 (M c71 Z)) (M c67 (P c71 Z)) rfl rfl
  · exact LN B 1 1 c74 (P c67 (M c71 Z)) (M c67 (P c71 Z)) rfl rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c72 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c69 (M h Z)) rfl
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c78
 · exact L B (M c69 (P h Z)) rfl
 · exact L B (M c1 (P c70 (M h Z))) rfl
 · exact L B (M c69 (P h Z)) rfl
 · exact LN B 1 1 c78 (M c1 (M c67 (P c71 (P c73 Z)))) (P c1 (P c67 (M c71 (M c73 Z)))) rfl rfl
 · exact L B (M c72 (P h Z)) rfl
 · exact L B (M c67 (P c71 (P h Z))) rfl
 · exact L B (M c71 (M c72 (P h Z))) rfl
 · exact absurd h c74
 · exact L B (P c67 (M c71 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s32 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c67 : Q y false 1 2 5 6) (c69 : Q y true 0 1 3 5) (c70 : Q y false 0 2 4 6) (c71 : Q y false 3 4 5 6) (c72 : Q y true 0 1 4 6) (c3 : N (Q y false 0 1 5 6)) (c47 : N (Q y true 0 1 5 6)) (c58 : N (Q y false 0 2 5 6)) (c65 : N (Q y true 0 2 5 6)) (c68 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 0 2 3 5) with c73 | c73
 ·
  exact s33 y B H c1 c2 c67 c69 c70 c71 c72 c73 c3 c47 c58 c65 c68
 rcases em (Q y false 2 3 4 5) with c79 | c79
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c67 (P h Z)) rfl
  · exact LN B 1 1 c73 (P c1 (P c67 (M c71 (P c79 Z)))) (M c1 (M c67 (P c71 (M c79 Z)))) rfl rfl
  · exact LN B 1 1 c73 (P c1 (P c67 (M c71 (P c79 Z)))) (M c1 (M c67 (P c71 (M c79 Z)))) rfl rfl
  · exact LN B 1 1 c73 (P c1 (P c67 (M c71 (P c79 Z)))) (M c1 (M c67 (P c71 (M c79 Z)))) rfl rfl
  · exact LN B 1 1 c73 (P c1 (P c67 (M c71 (P c79 Z)))) (M c1 (M c67 (P c71 (M c79 Z)))) rfl rfl
  · exact LN B 1 1 c73 (P c1 (P c67 (M c71 (P c79 Z)))) (M c1 (M c67 (P c71 (M c79 Z)))) rfl rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c71 (P c72 (M h Z))) rfl
 rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c79
 · exact L B (M c69 (P h Z)) rfl
 · exact L B (P c70 (M h Z)) rfl
 · exact L B (M c69 (P h Z)) rfl
 · exact L B (P c70 (M h Z)) rfl
 · exact L B (M c69 (P h Z)) rfl
 · exact absurd h c73
 · exact L B (P c70 (M c71 (P h Z))) rfl
 · exact L B (P c67 (M c71 (M h Z))) rfl
 · exact L B (P c67 (M c71 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s31 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c67 : Q y false 1 2 5 6) (c69 : Q y true 0 1 3 5) (c70 : Q y false 0 2 4 6) (c71 : Q y false 3 4 5 6) (c3 : N (Q y false 0 1 5 6)) (c47 : N (Q y true 0 1 5 6)) (c58 : N (Q y false 0 2 5 6)) (c65 : N (Q y true 0 2 5 6)) (c68 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y true 0 1 4 6) with c72 | c72
 ·
  exact s32 y B H c1 c2 c67 c69 c70 c71 c72 c3 c47 c58 c65 c68
 rcases em (Q y false 1 3 4 6) with c80 | c80
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c67 (P h Z)) rfl
  · exact LN B 1 1 c72 (P c69 (M c71 Z)) (M c2 (M c67 (P c71 (P c80 Z)))) rfl rfl
  · exact LN B 1 1 c72 (P c69 (M c71 Z)) (M c2 (M c67 (P c71 (P c80 Z)))) rfl rfl
  · exact LN B 1 1 c72 (P c69 (M c71 Z)) (M c69 (P c71 Z)) rfl rfl
  · exact LN B 1 1 c72 (P c2 (P c67 (M c71 (M c80 Z)))) (M c2 (M c67 (P c71 (P c80 Z)))) rfl rfl
  · exact LN B 1 1 c72 (P c69 (M c71 Z)) (M c69 (P c71 Z)) rfl rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c69 (M h Z)) rfl
 rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c80
 · exact L B (P c67 (M c69 (P h Z))) rfl
 · exact L B (P c2 (P c67 (M c69 (M h Z)))) rfl
 · exact L B (P c67 (M c69 (P h Z))) rfl
 · exact L B (M c70 (P h Z)) rfl
 · exact absurd h c72
 · exact L B (M c70 (P h Z)) rfl
 · exact L B (P c69 (M h Z)) rfl
 · exact LN B 1 1 c80 (P c2 (P c67 (M c69 Z))) (M c2 (M c67 (P c69 Z))) rfl rfl
 · exact L B (M c2 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s30 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c67 : Q y false 1 2 5 6) (c69 : Q y true 0 1 3 5) (c70 : Q y false 0 2 4 6) (c3 : N (Q y false 0 1 5 6)) (c47 : N (Q y true 0 1 5 6)) (c58 : N (Q y false 0 2 5 6)) (c65 : N (Q y true 0 2 5 6)) (c68 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 3 4 5 6) with c71 | c71
 ·
  exact s31 y B H c1 c2 c67 c69 c70 c71 c3 c47 c58 c65 c68
 rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c71
 · exact L B (P c67 (P h Z)) rfl
 · exact L B (P c67 (M h Z)) rfl
 · exact L B (P c67 (P h Z)) rfl
 · exact L B (P c67 (M h Z)) rfl
 · exact L B (P c67 (P h Z)) rfl
 · exact L B (P c70 (M h Z)) rfl
 · exact L B (P c70 (P h Z)) rfl
 · exact L B (P c2 (M c69 (M h Z))) rfl
 · exact L B (M c69 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s29 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c67 : Q y false 1 2 5 6) (c69 : Q y true 0 1 3 5) (c3 : N (Q y false 0 1 5 6)) (c47 : N (Q y true 0 1 5 6)) (c58 : N (Q y false 0 2 5 6)) (c65 : N (Q y true 0 2 5 6)) (c68 : N (Q y false 0 1 3 5)) : False := by
 rcases em (Q y false 0 2 4 6) with c70 | c70
 ·
  exact s30 y B H c1 c2 c67 c69 c70 c3 c47 c58 c65 c68
 rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c70 (P c1 (P c2 (P c67 (M c69 Z)))) (M c1 (M c2 (M c67 (P c69 Z)))) rfl rfl
 · exact L B (P c67 (P h Z)) rfl
 · exact L B (P c67 (M h Z)) rfl
 · exact L B (P c67 (P h Z)) rfl
 · exact absurd h c58
 · exact absurd h c65
 · exact absurd h c70
 · exact L B (P c67 (M c69 (P h Z))) rfl
 · exact L B (P c1 (P c2 (M c69 (M h Z)))) rfl
 · exact L B (M c69 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s28 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c65 : Q y true 0 2 5 6) (_c3 : N (Q y false 0 1 5 6)) (_c47 : N (Q y true 0 1 5 6)) (_c58 : N (Q y false 0 2 5 6)) : False := by
 rcases em (Q y true 1 2 5 7) with c66 | c66
 ·
  rcases H.h02467 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c1 (P c65 (M c66 (M h Z)))) rfl
  · exact L B (M c66 (P h Z)) rfl
  · exact L B (P c65 (M c66 (M h Z))) rfl
  · exact L B (P c65 (M c66 (P h Z))) rfl
  · exact L B (P c65 (M c66 (M h Z))) rfl
  · exact L B (P c65 (M c66 (P h Z))) rfl
  · exact L B (P c65 (P h Z)) rfl
  · exact L B (P c65 (M h Z)) rfl
  · exact L B (P c65 (P h Z)) rfl
  · exact L B (P c65 (M h Z)) rfl
 rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c65 (P h Z)) rfl
 · exact absurd h c66
 · exact L B (P c65 (P h Z)) rfl
 · exact L B (P c65 (M h Z)) rfl
 · exact L B (P c65 (P h Z)) rfl
 · exact L B (P c65 (M h Z)) rfl
 · exact L B (P c65 (P h Z)) rfl
 · exact L B (P c65 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact L B (P c2 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s27 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c58 : Q y false 0 2 5 6) (c61 : Q y true 1 2 5 7) (c62 : Q y true 0 1 6 7) (c63 : Q y false 0 3 6 7) (_c3 : N (Q y false 0 1 5 6)) (_c47 : N (Q y true 0 1 5 6)) (_c59 : N (Q y true 0 1 5 7)) (_c60 : N (Q y true 0 2 5 7)) : False := by
 rcases em (Q y true 1 3 4 7) with c64 | c64
 ·
  rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c2 (P c58 (M c62 (M c63 (M h Z))))) rfl
  · exact L B (M c61 (P h Z)) rfl
  · exact L B (M c1 (P c58 (M h Z))) rfl
  · exact L B (M c61 (P h Z)) rfl
  · exact L B (P c61 (M c62 (P h Z))) rfl
  · exact L B (P c58 (P h Z)) rfl
  · exact L B (M c58 (P h Z)) rfl
  · exact L B (M c63 (M c64 (P h Z))) rfl
  · exact G B (P c58 (P c63 (P c64 (P h Z)))) rfl
  · exact L B (M c63 (M c64 (P h Z))) rfl
 rcases H.h01347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c63 (P h Z)) rfl
 · exact absurd h c64
 · exact L B (M c63 (P h Z)) rfl
 · exact L B (P c1 (P c61 (M h Z))) rfl
 · exact L B (M c63 (P h Z)) rfl
 · exact L B (P c61 (M h Z)) rfl
 · exact L B (M c63 (P h Z)) rfl
 · exact L B (P c62 (M h Z)) rfl
 · exact L B (P c2 (M c62 (M c63 (P h Z)))) rfl
 · exact L B (M c2 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s26 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c58 : Q y false 0 2 5 6) (c61 : Q y true 1 2 5 7) (c62 : Q y true 0 1 6 7) (c3 : N (Q y false 0 1 5 6)) (c47 : N (Q y true 0 1 5 6)) (c59 : N (Q y true 0 1 5 7)) (c60 : N (Q y true 0 2 5 7)) : False := by
 rcases em (Q y false 0 3 6 7) with c63 | c63
 ·
  exact s27 y B H c1 c2 c58 c61 c62 c63 c3 c47 c59 c60
 rcases H.h02367 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (P c62 (P h Z))) rfl
 · exact L B (M c62 (P h Z)) rfl
 · exact absurd h c63
 · exact L B (M c62 (P h Z)) rfl
 · exact LN B 1 1 c47 (M c58 (P c62 (P h Z))) (M c61 (M h Z)) rfl rfl
 · exact L B (M c62 (P h Z)) rfl
 · exact L B (M c58 (P h Z)) rfl
 · exact L B (M c58 (P c62 (M h Z))) rfl
 · exact L B (M c58 (P h Z)) rfl
 · exact L B (P c1 (P c2 (M c58 (M h Z)))) rfl

set_option maxHeartbeats 4000000 in
lemma s25 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c58 : Q y false 0 2 5 6) (c61 : Q y true 1 2 5 7) (c3 : N (Q y false 0 1 5 6)) (c47 : N (Q y true 0 1 5 6)) (c59 : N (Q y true 0 1 5 7)) (c60 : N (Q y true 0 2 5 7)) : False := by
 rcases em (Q y true 0 1 6 7) with c62 | c62
 ·
  exact s26 y B H c1 c2 c58 c61 c62 c3 c47 c59 c60
 rcases H.h01567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c2 (M c58 (M c61 (M h Z)))) rfl
 · exact L B (M c61 (P h Z)) rfl
 · exact L B (P c2 (M c61 (M h Z))) rfl
 · exact L B (M c58 (M c61 (P h Z))) rfl
 · exact L B (P c58 (P c61 (P h Z))) rfl
 · exact absurd h c62
 · exact L B (M c58 (P h Z)) rfl
 · exact absurd h c59
 · exact absurd h c3
 · exact absurd h c47

set_option maxHeartbeats 4000000 in
lemma s24 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c58 : Q y false 0 2 5 6) (c3 : N (Q y false 0 1 5 6)) (c47 : N (Q y true 0 1 5 6)) : False := by
 rcases em (Q y true 0 1 5 7) with c59 | c59
 ·
  rcases H.h12567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c2 (M c59 (M h Z))) rfl
  · exact L B (M c59 (P h Z)) rfl
  · exact L B (P c2 (M c59 (M h Z))) rfl
  · exact L B (M c59 (P h Z)) rfl
  · exact G B (P c58 (P c59 (P h Z))) rfl
  · exact L B (M c59 (P h Z)) rfl
  · exact L B (M c58 (P h Z)) rfl
  · exact L B (M c59 (P h Z)) rfl
  · exact L B (M c58 (P h Z)) rfl
  · exact L B (M c59 (P h Z)) rfl
 rcases em (Q y true 0 2 5 7) with c60 | c60
 ·
  rcases H.h12567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c2 (M c58 (M c60 (M h Z)))) rfl
  · exact L B (M c60 (P h Z)) rfl
  · exact L B (P c2 (M c60 (M h Z))) rfl
  · exact L B (M c60 (P h Z)) rfl
  · exact LN B 1 1 c47 (P c60 (P h Z)) (M c60 (M h Z)) rfl rfl
  · exact L B (M c60 (P h Z)) rfl
  · exact L B (M c58 (P h Z)) rfl
  · exact L B (M c60 (P h Z)) rfl
  · exact L B (M c58 (P h Z)) rfl
  · exact L B (P c58 (P h Z)) rfl
 rcases em (Q y true 1 2 5 7) with c61 | c61
 ·
  exact s25 y B H c1 c2 c58 c61 c3 c47 c59 c60
 rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c58 (P h Z)) rfl
 · exact absurd h c61
 · exact L B (M c58 (P h Z)) rfl
 · exact absurd h c60
 · exact L B (M c58 (P h Z)) rfl
 · exact absurd h c59
 · exact L B (M c58 (P h Z)) rfl
 · exact L B (P c2 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact L B (P c2 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s23 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c47 : Q y true 0 1 5 6) (c55 : Q y true 1 2 5 7) (c56 : Q y true 0 1 6 7) (_c3 : N (Q y false 0 1 5 6)) (_c48 : N (Q y false 0 2 5 7)) (_c50 : N (Q y true 0 2 5 7)) (_c53 : N (Q y false 1 2 5 7)) : False := by
 rcases em (Q y true 2 3 4 7) with c57 | c57
 ·
  rcases H.h23567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c1 (P c47 (K (-2) c55 (P c57 (M h Z))))) rfl
  · exact L B (M c57 (P h Z)) rfl
  · exact L B (P c2 (M c56 (M h Z))) rfl
  · exact L B (M c57 (P h Z)) rfl
  · exact L B (P c1 (P c56 (P h Z))) rfl
  · exact L B (M c56 (P h Z)) rfl
  · exact L B (P c1 (P c56 (P h Z))) rfl
  · exact L B (M c55 (P h Z)) rfl
  · exact L B (P c1 (P c47 (P h Z))) rfl
  · exact L B (M c47 (P h Z)) rfl
 rcases H.h02347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (P c56 (P h Z))) rfl
 · exact absurd h c57
 · exact L B (P c1 (P c55 (P h Z))) rfl
 · exact L B (P c1 (P c55 (M h Z))) rfl
 · exact L B (P c55 (P h Z)) rfl
 · exact L B (P c55 (M h Z)) rfl
 · exact L B (P c55 (P h Z)) rfl
 · exact L B (P c55 (M h Z)) rfl
 · exact L B (M c2 (P c47 (M c55 (P c56 (M h Z))))) rfl
 · exact L B (M c2 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s22 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c47 : Q y true 0 1 5 6) (c55 : Q y true 1 2 5 7) (c3 : N (Q y false 0 1 5 6)) (c48 : N (Q y false 0 2 5 7)) (c50 : N (Q y true 0 2 5 7)) (c53 : N (Q y false 1 2 5 7)) : False := by
 rcases em (Q y true 0 1 6 7) with c56 | c56
 ·
  exact s23 y B H c1 c2 c47 c55 c56 c3 c48 c50 c53
 rcases H.h01467 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c1 (P c47 (M c55 (M h Z)))) rfl
 · exact L B (M c55 (P h Z)) rfl
 · exact L B (P c47 (M c55 (M h Z))) rfl
 · exact L B (P c47 (M c55 (P h Z))) rfl
 · exact L B (M c47 (P c55 (P h Z))) rfl
 · exact absurd h c56
 · exact L B (P c55 (K 2 h Z)) rfl
 · exact L B (P c55 (M h Z)) rfl
 · exact L B (P c47 (P h Z)) rfl
 · exact L B (P c47 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s21 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c47 : Q y true 0 1 5 6) (c53 : Q y false 1 2 5 7) (_c3 : N (Q y false 0 1 5 6)) (c48 : N (Q y false 0 2 5 7)) (c50 : N (Q y true 0 2 5 7)) : False := by
 rcases em (Q y false 2 5 6 7) with c54 | c54
 ·
  rcases H.h01267 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c53 (M h Z)) rfl
  · exact L B (P c53 (P h Z)) rfl
  · exact L B (P c53 (M h Z)) rfl
  · exact L B (P c53 (P h Z)) rfl
  · exact L B (M c1 (M c54 (P h Z))) rfl
  · exact L B (P c2 (M c54 (M h Z))) rfl
  · exact L B (P c47 (P h Z)) rfl
  · exact L B (P c47 (M h Z)) rfl
  · exact L B (P c47 (P h Z)) rfl
  · exact L B (P c47 (M h Z)) rfl
 rcases H.h02567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c54
 · exact L B (K 2 c53 (P h Z)) rfl
 · exact L B (P c53 (M h Z)) rfl
 · exact L B (P c53 (P h Z)) rfl
 · exact L B (P c53 (M h Z)) rfl
 · exact L B (P c53 (P h Z)) rfl
 · exact absurd h c48
 · exact absurd h c50
 · exact L B (P c53 (M h Z)) rfl
 · exact L B (P c53 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s20 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c47 : Q y true 0 1 5 6) (c50 : Q y true 0 2 5 7) (c51 : Q y false 4 5 6 7) (_c3 : N (Q y false 0 1 5 6)) (_c48 : N (Q y false 0 2 5 7)) : False := by
 rcases em (Q y false 2 3 6 7) with c52 | c52
 ·
  rcases H.h12357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c47 (P h Z))) rfl
  · exact L B (M c47 (P c52 (P h Z))) rfl
  · exact L B (P c1 (P c50 (P h Z))) rfl
  · exact L B (M c47 (P c52 (P h Z))) rfl
  · exact L B (P c50 (P h Z)) rfl
  · exact L B (P c1 (M c47 (P c52 (P h Z)))) rfl
  · exact L B (P c50 (P h Z)) rfl
  · exact L B (M c1 (P c50 (P c51 (M c52 (M h Z))))) rfl
  · exact L B (M c47 (P c50 (P c51 (P h Z)))) rfl
  · exact L B (M c2 (M c51 (P c52 (P h Z)))) rfl
 rcases H.h02367 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c52
 · exact L B (M c50 (P h Z)) rfl
 · exact L B (P c47 (M c50 (M h Z))) rfl
 · exact L B (M c50 (P h Z)) rfl
 · exact L B (P c47 (M c50 (M h Z))) rfl
 · exact L B (M c50 (P h Z)) rfl
 · exact L B (P c50 (P h Z)) rfl
 · exact L B (P c50 (M h Z)) rfl
 · exact L B (P c50 (P c51 (P h Z))) rfl
 · exact L B (P c50 (P c51 (M h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s19 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c47 : Q y true 0 1 5 6) (c50 : Q y true 0 2 5 7) (c3 : N (Q y false 0 1 5 6)) (c48 : N (Q y false 0 2 5 7)) : False := by
 rcases em (Q y false 4 5 6 7) with c51 | c51
 ·
  exact s20 y B H c1 c2 c47 c50 c51 c3 c48
 rcases H.h04567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c51
 · exact L B (M c50 (P h Z)) rfl
 · exact L B (P c47 (M c50 (M h Z))) rfl
 · exact L B (M c50 (P h Z)) rfl
 · exact L B (P c47 (M c50 (M h Z))) rfl
 · exact L B (M c50 (P h Z)) rfl
 · exact L B (P c2 (M c50 (M h Z))) rfl
 · exact L B (M c50 (P h Z)) rfl
 · exact L B (P c2 (M c47 (M h Z))) rfl
 · exact L B (M c47 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s18 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (_c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c47 : Q y true 0 1 5 6) (c48 : Q y false 0 2 5 7) (_c3 : N (Q y false 0 1 5 6)) : False := by
 rcases em (Q y false 3 5 6 7) with c49 | c49
 ·
  rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c2 (P c47 (P h Z))) rfl
  · exact L B (P c48 (P h Z)) rfl
  · exact L B (P c48 (M h Z)) rfl
  · exact L B (P c48 (P h Z)) rfl
  · exact L B (P c48 (M h Z)) rfl
  · exact L B (P c48 (P h Z)) rfl
  · exact L B (P c48 (M c49 (M h Z))) rfl
  · exact L B (P c48 (M c49 (P h Z))) rfl
  · exact L B (P c48 (M c49 (M h Z))) rfl
  · exact L B (P c48 (M c49 (P h Z))) rfl
 rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c49
 · exact L B (P c48 (P h Z)) rfl
 · exact L B (P c48 (M h Z)) rfl
 · exact L B (P c48 (P h Z)) rfl
 · exact L B (P c48 (M h Z)) rfl
 · exact L B (P c48 (P h Z)) rfl
 · exact L B (P c48 (M h Z)) rfl
 · exact L B (P c48 (P h Z)) rfl
 · exact L B (P c48 (M h Z)) rfl
 · exact L B (P c48 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s17 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c47 : Q y true 0 1 5 6) (c3 : N (Q y false 0 1 5 6)) : False := by
 rcases em (Q y false 0 2 5 7) with c48 | c48
 ·
  exact s18 y B H c1 c2 c47 c48 c3
 rcases em (Q y true 0 2 5 7) with c50 | c50
 ·
  exact s19 y B H c1 c2 c47 c50 c3 c48
 rcases em (Q y false 1 2 5 7) with c53 | c53
 ·
  exact s21 y B H c1 c2 c47 c53 c3 c48 c50
 rcases em (Q y true 1 2 5 7) with c55 | c55
 ·
  exact s22 y B H c1 c2 c47 c55 c3 c48 c50 c53
 rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c53
 · exact absurd h c55
 · exact absurd h c48
 · exact absurd h c50
 · exact L B (P c47 (P h Z)) rfl
 · exact L B (P c47 (M h Z)) rfl
 · exact L B (P c47 (P h Z)) rfl
 · exact L B (P c47 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact L B (P c2 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s16 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (_c23 : Q y false 0 2 4 6) (c24 : Q y false 3 4 5 6) (_c25 : Q y false 0 2 3 5) (_c36 : Q y false 1 3 4 6) (c37 : Q y false 1 2 4 5) (c38 : Q y false 2 3 5 6) (c39 : Q y false 0 1 3 4) (_c4 : N (Q y false 0 2 4 5)) (_c18 : N (Q y true 0 2 4 5)) (c26 : N (Q y false 1 2 3 4)) : False := by
 rcases em (Q y true 0 2 4 7) with c40 | c40
 ·
  rcases H.h02567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c2 (M c37 (M c40 (M h Z)))) rfl
  · exact L B (M c40 (P h Z)) rfl
  · exact L B (P c2 (M c40 (M h Z))) rfl
  · exact L B (M c40 (P h Z)) rfl
  · exact L B (P c2 (P c3 (M c24 (M c38 (M c40 (M h Z)))))) rfl
  · exact L B (M c40 (P h Z)) rfl
  · exact LN B 1 1 c26 (M c1 (M c2 (P c37 (P c40 (P h Z))))) (P c1 (P c2 (M c37 (M c40 (M h Z))))) rfl rfl
  · exact L B (M c40 (P h Z)) rfl
  · exact L B (P c1 (P c38 (M h Z))) rfl
  · exact L B (P c3 (P h Z)) rfl
 rcases em (Q y false 0 3 4 7) with c41 | c41
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c40 (P c2 (P c39 (M c41 Z))) (M c2 (M c39 (P c41 Z))) rfl rfl
  · exact L B (P c1 (P c41 (P h Z))) rfl
  · exact LN B 1 1 c40 (P c2 (P c39 (M c41 Z))) (M c2 (M c39 (P c41 Z))) rfl rfl
  · exact L B (M c2 (M c39 (P c41 (P h Z)))) rfl
  · exact L B (M c24 (M c39 (P h Z))) rfl
  · exact LN B 1 1 c40 (P c2 (P c39 (M c41 Z))) (P c37 (M h Z)) rfl rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c39 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
 rcases em (Q y true 0 3 4 7) with c42 | c42
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c26 (K (-2) c1 (M c2 (K 2 c3 (M c24 (K 2 c37 (P c42 (P h Z))))))) (K 2 c1 (P c2 (M c24 (K (-2) c37 (K (-2) c39 (M c42 (M h Z))))))) rfl rfl
  · exact L B (M c42 (P h Z)) rfl
  · exact L B (P c1 (P c2 (M c42 (M h Z)))) rfl
  · exact L B (M c42 (P h Z)) rfl
  · exact L B (P c2 (M c38 (P c39 (M c42 (M h Z))))) rfl
  · exact L B (M c42 (P h Z)) rfl
  · exact LN B 1 1 c26 (M c1 (M c2 (P c37 (P c42 (P h Z))))) (P c1 (P c2 (M c37 (M c42 (M h Z))))) rfl rfl
  · exact L B (M c42 (P h Z)) rfl
  · exact L B (P c3 (M h Z)) rfl
  · exact L B (P c24 (P c39 (P h Z))) rfl
 rcases em (Q y true 2 3 4 7) with c43 | c43
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c37 (P c43 (P h Z))) rfl
  · exact L B (P c37 (P c43 (M h Z))) rfl
  · exact L B (P c37 (P c43 (P h Z))) rfl
  · exact L B (P c37 (P c43 (M h Z))) rfl
  · exact L B (M c1 (M c38 (P h Z))) rfl
  · exact L B (P c37 (P c43 (M h Z))) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c3 (P c24 (P h Z))) rfl
  · exact L B (P c2 (M h Z)) rfl
 rcases H.h02347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c24 (M c39 (P h Z)))) rfl
 · exact absurd h c43
 · exact absurd h c41
 · exact absurd h c42
 · exact L B (M c24 (M c37 (M c39 (P h Z)))) rfl
 · exact absurd h c40
 · exact L B (M c1 (M c37 (M c38 (P h Z)))) rfl
 · exact L B (P c1 (P c2 (M c3 (M c37 (M h Z))))) rfl
 · exact L B (P c39 (M h Z)) rfl
 · exact L B (P c1 (M c24 (P c38 (P h Z)))) rfl

set_option maxHeartbeats 4000000 in
lemma s15 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c23 : Q y false 0 2 4 6) (c24 : Q y false 3 4 5 6) (c25 : Q y false 0 2 3 5) (c36 : Q y false 1 3 4 6) (c37 : Q y false 1 2 4 5) (c38 : Q y false 2 3 5 6) (c4 : N (Q y false 0 2 4 5)) (c18 : N (Q y true 0 2 4 5)) (c26 : N (Q y false 1 2 3 4)) : False := by
 rcases em (Q y false 0 1 3 4) with c39 | c39
 ·
  exact s16 y B H c1 c2 c3 c23 c24 c25 c36 c37 c38 c39 c4 c18 c26
 rcases em (Q y true 0 1 4 5) with c44 | c44
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c39 (P c1 (M c24 (P c38 Z))) (M c3 (P c24 Z)) rfl rfl
  · exact LN B 1 1 c39 (P c3 (M c24 Z)) (M c1 (P c24 (M c38 Z))) rfl rfl
  · exact LN B 1 1 c39 (P c1 (M c24 (P c38 Z))) (M c3 (P c24 Z)) rfl rfl
  · exact LN B 1 1 c39 (P c1 (M c24 (P c38 Z))) (M c3 (P c24 Z)) rfl rfl
  · exact L B (M c1 (M c38 (P h Z))) rfl
  · exact LN B 1 1 c39 (P c3 (M c24 Z)) (M c3 (P c24 Z)) rfl rfl
  · exact L B (P c44 (P h Z)) rfl
  · exact L B (P c44 (M h Z)) rfl
  · exact L B (P c44 (P h Z)) rfl
  · exact L B (P c44 (M h Z)) rfl
 rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c37 (M h Z)) rfl
 · exact L B (P c37 (P h Z)) rfl
 · exact L B (P c37 (M h Z)) rfl
 · exact L B (P c37 (P h Z)) rfl
 · exact LN B 1 1 c39 (P c1 (M c24 (P c38 Z))) (M c25 (P c37 Z)) rfl rfl
 · exact absurd h c44
 · exact L B (M c3 (P c24 (P h Z))) rfl
 · exact LN B 1 1 c39 (P c3 (M c24 Z)) (M c1 (P c24 (M c38 Z))) rfl rfl
 · exact absurd h c39
 · exact L B (P c3 (M c24 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s14 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c23 : Q y false 0 2 4 6) (c24 : Q y false 3 4 5 6) (c25 : Q y false 0 2 3 5) (c36 : Q y false 1 3 4 6) (c37 : Q y false 1 2 4 5) (c4 : N (Q y false 0 2 4 5)) (c18 : N (Q y true 0 2 4 5)) (c26 : N (Q y false 1 2 3 4)) : False := by
 rcases em (Q y false 2 3 5 6) with c38 | c38
 ·
  exact s15 y B H c1 c2 c3 c23 c24 c25 c36 c37 c38 c4 c18 c26
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c38
 · exact L B (P c3 (P h Z)) rfl
 · exact L B (M c1 (P c3 (M h Z))) rfl
 · exact L B (P c3 (P h Z)) rfl
 · exact LN B 1 1 c38 (M c1 (P c23 (M c37 Z))) (P c1 (M c3 Z)) rfl rfl
 · exact L B (P c3 (P h Z)) rfl
 · exact L B (M c37 (P h Z)) rfl
 · exact L B (K 2 c3 (M c24 (P c37 (P h Z)))) rfl
 · exact L B (M c37 (P h Z)) rfl
 · exact L B (P c3 (M c24 (P c37 (P h Z)))) rfl

set_option maxHeartbeats 4000000 in
lemma s13 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c23 : Q y false 0 2 4 6) (c24 : Q y false 3 4 5 6) (c25 : Q y false 0 2 3 5) (c36 : Q y false 1 3 4 6) (c4 : N (Q y false 0 2 4 5)) (c18 : N (Q y true 0 2 4 5)) (c26 : N (Q y false 1 2 3 4)) : False := by
 rcases em (Q y false 1 2 4 5) with c37 | c37
 ·
  exact s14 y B H c1 c2 c3 c23 c24 c25 c36 c37 c4 c18 c26
 rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c37 (M c3 (P c24 (P c25 Z))) (M c1 (P c3 (M c36 Z))) rfl rfl
 · exact L B (P c36 (P h Z)) rfl
 · exact L B (M c3 (P c24 (P c25 (M h Z)))) rfl
 · exact L B (P c36 (P h Z)) rfl
 · exact absurd h c37
 · exact L B (P c25 (P h Z)) rfl
 · exact L B (M c25 (P h Z)) rfl
 · exact L B (P c1 (M c24 (P c36 (P h Z)))) rfl
 · exact absurd h c26
 · exact L B (P c3 (M c24 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s12 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c23 : Q y false 0 2 4 6) (c24 : Q y false 3 4 5 6) (_c25 : Q y false 0 2 3 5) (c26 : Q y false 1 2 3 4) (c27 : Q y false 1 2 5 6) (c28 : Q y false 0 1 3 4) (_c4 : N (Q y false 0 2 4 5)) (_c18 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y true 0 1 5 7) with c29 | c29
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c2 (M c3 (M c29 (M h Z))))) rfl
  · exact L B (M c29 (P h Z)) rfl
  · exact L B (P c2 (M c29 (M h Z))) rfl
  · exact L B (M c29 (P h Z)) rfl
  · exact L B (P c2 (P c26 (M c29 (M h Z)))) rfl
  · exact L B (M c29 (P h Z)) rfl
  · exact L B (P c2 (P c26 (M c29 (M h Z)))) rfl
  · exact L B (M c29 (P h Z)) rfl
  · exact L B (P c27 (M h Z)) rfl
  · exact L B (P c27 (P h Z)) rfl
 rcases em (Q y false 0 2 5 7) with c30 | c30
 ·
  rcases H.h01267 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c29 (P c1 (P c2 (M c3 (P c26 (M h Z))))) (M c1 (M c2 (M c26 (P c30 Z)))) rfl rfl
  · exact L B (P c30 (P h Z)) rfl
  · exact L B (P c30 (M h Z)) rfl
  · exact L B (P c30 (P h Z)) rfl
  · exact LN B 1 1 c29 (P c1 (P c2 (M c24 (P c27 (M c30 Z))))) (M c1 (M c2 (P c3 (M c28 (P h Z))))) rfl rfl
  · exact L B (M c24 (M c26 (P c30 (P h Z)))) rfl
  · exact L B (M c3 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
 rcases em (Q y true 0 2 5 7) with c31 | c31
 ·
  rcases H.h04567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c23 (P c31 (P h Z))) rfl
  · exact L B (M c31 (P h Z)) rfl
  · exact L B (P c2 (M c31 (M h Z))) rfl
  · exact L B (M c31 (P h Z)) rfl
  · exact L B (P c2 (M c31 (M h Z))) rfl
  · exact L B (M c31 (P h Z)) rfl
  · exact L B (P c2 (M c31 (M h Z))) rfl
  · exact L B (M c31 (P h Z)) rfl
  · exact L B (P c27 (M h Z)) rfl
  · exact L B (P c27 (P h Z)) rfl
 rcases em (Q y true 1 2 5 7) with c32 | c32
 ·
  rcases H.h02347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c24 (M c28 (P h Z)))) rfl
  · exact L B (M c1 (P c23 (M c32 (P h Z)))) rfl
  · exact L B (P c1 (P c32 (P h Z))) rfl
  · exact L B (P c1 (P c32 (M h Z))) rfl
  · exact L B (P c32 (P h Z)) rfl
  · exact L B (P c32 (M h Z)) rfl
  · exact L B (P c32 (P h Z)) rfl
  · exact L B (P c32 (M h Z)) rfl
  · exact L B (P c26 (M h Z)) rfl
  · exact L B (P c26 (P h Z)) rfl
 rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c27 (P h Z)) rfl
 · exact absurd h c32
 · exact absurd h c30
 · exact absurd h c31
 · exact L B (M c3 (P h Z)) rfl
 · exact absurd h c29
 · exact L B (M c3 (P h Z)) rfl
 · exact L B (P c2 (M h Z)) rfl
 · exact L B (M c1 (P h Z)) rfl
 · exact L B (P c2 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s11 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c23 : Q y false 0 2 4 6) (c24 : Q y false 3 4 5 6) (c25 : Q y false 0 2 3 5) (c26 : Q y false 1 2 3 4) (c27 : Q y false 1 2 5 6) (c4 : N (Q y false 0 2 4 5)) (c18 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y false 0 1 3 4) with c28 | c28
 ·
  exact s12 y B H c1 c2 c3 c23 c24 c25 c26 c27 c28 c4 c18
 rcases em (Q y true 0 1 3 5) with c33 | c33
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c27 (P h Z)) rfl
  · exact LN B 1 1 c28 (P c3 (P c26 (M c27 Z))) (M c3 (M c26 (P c27 Z))) rfl rfl
  · exact LN B 1 1 c28 (P c3 (P c26 (M c27 Z))) (M c3 (P c24 Z)) rfl rfl
  · exact LN B 1 1 c28 (P c3 (M c24 Z)) (M c3 (M c26 (P c27 Z))) rfl rfl
  · exact L B (M c3 (P h Z)) rfl
  · exact LN B 1 1 c28 (P c3 (P c26 (M c27 Z))) (M c3 (P c24 Z)) rfl rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c33 (M h Z)) rfl
  · exact L B (M c3 (P c24 (P h Z))) rfl
  · exact L B (P c33 (M h Z)) rfl
 rcases em (Q y false 0 1 4 5) with c34 | c34
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c27 (P h Z)) rfl
  · exact LN B 1 1 c33 (P c1 (P c2 (M c23 (P c24 (P c26 Z))))) (M c1 (M c2 (P c34 Z))) rfl rfl
  · exact LN B 1 1 c33 (P c1 (P c2 (M c34 Z))) (M c1 (M c2 (P c34 Z))) rfl rfl
  · exact LN B 1 1 c33 (P c1 (P c2 (M c23 (P c24 (P c26 Z))))) (M c1 (M c2 (P c34 Z))) rfl rfl
  · exact L B (M c3 (P h Z)) rfl
  · exact LN B 1 1 c33 (P c1 (P c2 (M c23 (P c27 Z)))) (M c1 (M c2 (P c34 Z))) rfl rfl
  · exact L B (M c3 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c34 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
 rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c3 (P c23 (M h Z))) rfl
 · exact L B (P c23 (P h Z)) rfl
 · exact L B (P c23 (M h Z)) rfl
 · exact L B (P c25 (P h Z)) rfl
 · exact absurd h c34
 · exact L B (P c24 (P c25 (M c27 (P h Z)))) rfl
 · exact L B (M c3 (P c24 (P h Z))) rfl
 · exact absurd h c33
 · exact absurd h c28
 · exact L B (P c3 (P c26 (M c27 (P h Z)))) rfl

set_option maxHeartbeats 4000000 in
lemma s10 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c23 : Q y false 0 2 4 6) (c24 : Q y false 3 4 5 6) (c25 : Q y false 0 2 3 5) (c26 : Q y false 1 2 3 4) (c4 : N (Q y false 0 2 4 5)) (c18 : N (Q y true 0 2 4 5)) : False := by
 rcases em (Q y false 1 2 5 6) with c27 | c27
 ·
  exact s11 y B H c1 c2 c3 c23 c24 c25 c26 c27 c4 c18
 rcases em (Q y false 2 3 5 6) with c35 | c35
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c24 (M c26 (P h Z))) rfl
  · exact LN B 1 1 c27 (P c24 (P c26 Z)) (M c24 (M c26 Z)) rfl rfl
  · exact LN B 1 1 c27 (P c24 (P c26 Z)) (M c24 (M c26 Z)) rfl rfl
  · exact LN B 1 1 c27 (P c24 (P c26 Z)) (M c24 (M c26 Z)) rfl rfl
  · exact L B (M c1 (M c35 (P h Z))) rfl
  · exact LN B 1 1 c27 (P c24 (P c26 Z)) (M c24 (M c26 Z)) rfl rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
 rcases H.h12356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c35
 · exact L B (P c24 (P c26 (P h Z))) rfl
 · exact L B (P c24 (P c26 (M h Z))) rfl
 · exact L B (P c3 (P h Z)) rfl
 · exact absurd h c27
 · exact L B (P c3 (P h Z)) rfl
 · exact L B (M c26 (P h Z)) rfl
 · exact L B (P c3 (P c25 (P h Z))) rfl
 · exact L B (M c26 (P h Z)) rfl
 · exact L B (P c23 (M c24 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s9 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (_c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c18 : Q y true 0 2 4 5) (c19 : Q y false 2 3 5 6) (c20 : Q y false 3 4 5 6) (_c21 : Q y true 0 3 4 6) (_c4 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y true 2 3 4 7) with c22 | c22
 ·
  rcases H.h04567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (K 2 c18 (M c19 (M c22 (M h Z)))) rfl
  · exact L B (M c22 (P h Z)) rfl
  · exact L B (P c18 (M c22 (M h Z))) rfl
  · exact L B (K 2 c18 (M c22 (P h Z))) rfl
  · exact L B (P c18 (M c22 (M h Z))) rfl
  · exact L B (P c18 (M c22 (P h Z))) rfl
  · exact L B (P c18 (M c22 (M h Z))) rfl
  · exact L B (P c18 (M c22 (P h Z))) rfl
  · exact L B (P c19 (M h Z)) rfl
  · exact L B (P c19 (P h Z)) rfl
 rcases H.h02347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c19 (P h Z)) rfl
 · exact absurd h c22
 · exact L B (P c18 (M c19 (P h Z))) rfl
 · exact L B (P c18 (M c19 (M h Z))) rfl
 · exact L B (P c18 (P h Z)) rfl
 · exact L B (P c18 (M h Z)) rfl
 · exact L B (P c18 (P h Z)) rfl
 · exact L B (P c18 (M h Z)) rfl
 · exact L B (P c1 (P c19 (M c20 (M h Z)))) rfl
 · exact L B (P c3 (M c20 (P h Z))) rfl

set_option maxHeartbeats 4000000 in
lemma s8 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c18 : Q y true 0 2 4 5) (c19 : Q y false 2 3 5 6) (c20 : Q y false 3 4 5 6) (c4 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y true 0 3 4 6) with c21 | c21
 ·
  exact s9 y B H c1 c2 c3 c18 c19 c20 c21 c4
 rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (P c18 (P h Z))) rfl
 · exact L B (M c18 (P c19 (P h Z))) rfl
 · exact L B (P c1 (M c3 (P c18 (P h Z)))) rfl
 · exact absurd h c21
 · exact L B (P c18 (P h Z)) rfl
 · exact L B (P c18 (M h Z)) rfl
 · exact L B (P c18 (P h Z)) rfl
 · exact L B (P c18 (M h Z)) rfl
 · exact L B (P c1 (P c19 (M c20 (M h Z)))) rfl
 · exact L B (P c1 (P c19 (M c20 (P h Z)))) rfl

set_option maxHeartbeats 4000000 in
lemma s7 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c18 : Q y true 0 2 4 5) (c19 : Q y false 2 3 5 6) (c4 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y false 3 4 5 6) with c20 | c20
 ·
  exact s8 y B H c1 c2 c3 c18 c19 c20 c4
 rcases H.h13456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c20
 · exact L B (P c19 (P h Z)) rfl
 · exact L B (P c19 (M h Z)) rfl
 · exact L B (P c19 (P h Z)) rfl
 · exact L B (P c19 (M h Z)) rfl
 · exact L B (P c19 (P h Z)) rfl
 · exact L B (P c18 (M c19 (P h Z))) rfl
 · exact L B (M c18 (P c19 (P h Z))) rfl
 · exact L B (P c3 (P c18 (M c19 (P h Z)))) rfl
 · exact L B (M c18 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s6 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c18 : Q y true 0 2 4 5) (c4 : N (Q y false 0 2 4 5)) : False := by
 rcases em (Q y false 2 3 5 6) with c19 | c19
 ·
  exact s7 y B H c1 c2 c3 c18 c19 c4
 rcases H.h02356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c19
 · exact L B (P c3 (P h Z)) rfl
 · exact L B (P c3 (M h Z)) rfl
 · exact L B (P c3 (P h Z)) rfl
 · exact L B (P c3 (M h Z)) rfl
 · exact L B (P c3 (P h Z)) rfl
 · exact L B (P c18 (P h Z)) rfl
 · exact L B (P c18 (M h Z)) rfl
 · exact L B (P c18 (P h Z)) rfl
 · exact L B (P c18 (M h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s5 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c4 : Q y false 0 2 4 5) (c5 : Q y false 1 2 5 6) (c11 : Q y false 0 3 4 6) (c12 : Q y false 1 3 4 5) (c13 : Q y true 1 2 3 6) (c14 : Q y false 2 3 5 6) (c6 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y true 0 1 4 7) with c15 | c15
 ·
  rcases H.h02347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c12 (P h Z)) rfl
  · exact L B (M c15 (P h Z)) rfl
  · exact L B (M c3 (M c12 (P h Z))) rfl
  · exact L B (M c15 (P h Z)) rfl
  · exact L B (M c4 (P h Z)) rfl
  · exact L B (M c15 (P h Z)) rfl
  · exact L B (M c1 (M c12 (P h Z))) rfl
  · exact L B (P c2 (M c4 (M c14 (M h Z)))) rfl
  · exact L B (M c1 (P c2 (M c12 (M c14 (M c15 (P h Z)))))) rfl
  · exact L B (M c2 (P h Z)) rfl
 rcases em (Q y true 0 3 4 7) with c16 | c16
 ·
  rcases H.h01267 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact LN B 1 1 c6 (M c1 (M c2 (K 2 c3 (M c5 (P c12 (P c16 (P h Z))))))) (M c1 (P c2 (P c5 (M c12 (K (-2) c14 (M c16 (M h Z))))))) rfl rfl
  · exact L B (M c12 (M c16 (P h Z))) rfl
  · exact G B (P c5 (P c12 (P c16 (P h Z)))) rfl
  · exact L B (M c14 (M c16 (P h Z))) rfl
  · exact LN B 1 1 c6 (M c2 (P c12 (P c14 (P c16 (P h Z))))) (P c3 (P c13 (M c14 (M c16 (M h Z))))) rfl rfl
  · exact L B (M c12 (M c16 (P h Z))) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c1 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
 rcases em (Q y true 1 3 4 7) with c17 | c17
 ·
  rcases H.h01357 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (P c3 (M c5 (P c12 (P c17 (P h Z)))))) rfl
  · exact L B (M c17 (P h Z)) rfl
  · exact LN B 1 1 c6 (M c2 (P c3 (M c5 (P c12 (P c17 (P h Z)))))) (P c2 (P c5 (M c11 (M c17 (M h Z))))) rfl rfl
  · exact L B (M c1 (M c12 (M c17 (P h Z)))) rfl
  · exact L B (M c3 (P h Z)) rfl
  · exact L B (P c12 (P c17 (M h Z))) rfl
  · exact L B (M c3 (P h Z)) rfl
  · exact L B (P c17 (M h Z)) rfl
  · exact L B (M c3 (M c12 (P c14 (P h Z)))) rfl
  · exact L B (P c2 (M c4 (P c5 (M c14 (M h Z))))) rfl
 rcases H.h01347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (M c4 (M c14 (P h Z))) rfl
 · exact absurd h c17
 · exact L B (M c4 (M c14 (P h Z))) rfl
 · exact absurd h c16
 · exact L B (M c3 (P h Z)) rfl
 · exact absurd h c15
 · exact L B (M c3 (P h Z)) rfl
 · exact L B (P c2 (M c12 (M h Z))) rfl
 · exact absurd h c6
 · exact L B (M c2 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s4 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c4 : Q y false 0 2 4 5) (c5 : Q y false 1 2 5 6) (c11 : Q y false 0 3 4 6) (c12 : Q y false 1 3 4 5) (c13 : Q y true 1 2 3 6) (c6 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y false 2 3 5 6) with c14 | c14
 ·
  exact s5 y B H c1 c2 c3 c4 c5 c11 c12 c13 c14 c6
 rcases H.h23456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact LN B 1 1 c14 (M c1 (P c3 Z)) (P c1 (M c3 Z)) rfl rfl
 · exact L B (P c3 (P h Z)) rfl
 · exact L B (M c1 (P c3 (M h Z))) rfl
 · exact L B (P c3 (P h Z)) rfl
 · exact absurd h c14
 · exact L B (P c3 (P h Z)) rfl
 · exact L B (M c12 (P h Z)) rfl
 · exact L B (P c3 (P c12 (P h Z))) rfl
 · exact L B (M c12 (P h Z)) rfl
 · exact L B (P c12 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s3 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c4 : Q y false 0 2 4 5) (c5 : Q y false 1 2 5 6) (c11 : Q y false 0 3 4 6) (c12 : Q y false 1 3 4 5) (c6 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y true 1 2 3 6) with c13 | c13
 ·
  exact s4 y B H c1 c2 c3 c4 c5 c11 c12 c13 c6
 rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c4 (P h Z))) rfl
 · exact L B (P c3 (P c12 (P h Z))) rfl
 · exact L B (P c1 (M c4 (P h Z))) rfl
 · exact L B (P c3 (P c12 (P h Z))) rfl
 · exact L B (M c4 (P h Z)) rfl
 · exact L B (P c1 (P c3 (P c12 (P h Z)))) rfl
 · exact L B (M c4 (P h Z)) rfl
 · exact absurd h c13
 · exact LN B 1 1 c13 (P c1 (P c2 (M c3 (M c4 Z)))) (M c2 (P c3 (P c12 Z))) rfl rfl
 · exact L B (M c2 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s2 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c4 : Q y false 0 2 4 5) (c5 : Q y false 1 2 5 6) (c11 : Q y false 0 3 4 6) (c6 : N (Q y false 0 1 3 4)) : False := by
 rcases em (Q y false 1 3 4 5) with c12 | c12
 ·
  exact s3 y B H c1 c2 c3 c4 c5 c11 c12 c6
 rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c12
 · exact L B (P c4 (P h Z)) rfl
 · exact L B (P c4 (M h Z)) rfl
 · exact L B (P c4 (P h Z)) rfl
 · exact L B (M c4 (P h Z)) rfl
 · exact LN B 1 1 c12 (M c3 (P c11 Z)) (P c3 (M c11 Z)) rfl rfl
 · exact L B (M c4 (P h Z)) rfl
 · exact L B (P c1 (P c2 (M c4 (M h Z)))) rfl
 · exact absurd h c6
 · exact L B (M c2 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s1 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c4 : Q y false 0 2 4 5) (c5 : Q y false 1 2 5 6) (c6 : Q y false 0 1 3 4) (c7 : Q y true 0 2 4 6) : False := by
 rcases em (Q y true 0 3 4 7) with c8 | c8
 ·
  rcases H.h03567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c1 (M c4 (P c7 (M c8 (M h Z))))) rfl
  · exact L B (M c8 (P h Z)) rfl
  · exact L B (P c7 (M c8 (M h Z))) rfl
  · exact L B (M c8 (P h Z)) rfl
  · exact L B (P c7 (M c8 (M h Z))) rfl
  · exact L B (M c8 (P h Z)) rfl
  · exact L B (P c5 (P c7 (M c8 (M h Z)))) rfl
  · exact L B (M c8 (P h Z)) rfl
  · exact L B (P c5 (M h Z)) rfl
  · exact L B (P c5 (P h Z)) rfl
 rcases em (Q y true 2 3 4 7) with c9 | c9
 ·
  rcases H.h24567 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c1 (P c3 (K 2 c4 (P c9 (P h Z))))) rfl
  · exact L B (M c9 (P h Z)) rfl
  · exact L B (M c4 (P c7 (M c9 (M h Z)))) rfl
  · exact L B (M c9 (P h Z)) rfl
  · exact L B (M c1 (M c2 (P c3 (P c4 (P c9 (P h Z)))))) rfl
  · exact L B (M c9 (P h Z)) rfl
  · exact L B (P c4 (P c6 (P c9 (P h Z)))) rfl
  · exact L B (M c9 (P h Z)) rfl
  · exact L B (P c3 (M c6 (M h Z))) rfl
  · exact L B (P c5 (P h Z)) rfl
 rcases H.h02347 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c3 (P h Z))) rfl
 · exact absurd h c9
 · exact L B (P c1 (M c3 (M c4 (P h Z)))) rfl
 · exact absurd h c8
 · exact L B (M c4 (P h Z)) rfl
 · exact L B (P c7 (M h Z)) rfl
 · exact L B (M c4 (P h Z)) rfl
 · exact L B (P c7 (M h Z)) rfl
 · exact L B (P c6 (M h Z)) rfl
 · exact L B (P c6 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma s0 (y : ℕ → ℤ) (B : Bs y) (H : AH y)
  (c1 : Q y false 0 1 2 3) (c2 : Q y true 0 1 2 4) (c3 : Q y false 0 1 5 6) (c4 : Q y false 0 2 4 5) (c5 : Q y false 1 2 5 6) (c6 : Q y false 0 1 3 4) : False := by
 rcases em (Q y true 0 2 4 6) with c7 | c7
 ·
  exact s1 y B H c1 c2 c3 c4 c5 c6 c7
 rcases em (Q y false 0 3 4 6) with c10 | c10
 ·
  rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c5 (P h Z)) rfl
  · exact LN B 1 1 c7 (P c1 (P c2 (M c3 (M c4 (P c6 Z))))) (M c1 (M c2 (P c3 (P c4 (M c6 Z))))) rfl rfl
  · exact LN B 1 1 c7 (P c1 (P c2 (M c3 (M c4 (P c6 Z))))) (M c1 (M c2 (P c3 (P c4 (M c6 Z))))) rfl rfl
  · exact LN B 1 1 c7 (P c1 (P c2 (M c3 (M c4 (P c6 Z))))) (M c1 (M c2 (P c3 (P c4 (M c6 Z))))) rfl rfl
  · exact L B (M c3 (P h Z)) rfl
  · exact LN B 1 1 c7 (P c1 (P c2 (M c3 (M c4 (P c6 Z))))) (M c1 (M c2 (P c3 (P c4 (M c6 Z))))) rfl rfl
  · exact L B (M c4 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
  · exact L B (M c4 (P h Z)) rfl
  · exact L B (P c2 (M h Z)) rfl
 rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact L B (P c1 (M c4 (P h Z))) rfl
 · exact L B (P c3 (P c4 (P h Z))) rfl
 · exact absurd h c10
 · exact L B (M c1 (P c3 (P c4 (P h Z)))) rfl
 · exact L B (M c4 (P h Z)) rfl
 · exact absurd h c7
 · exact L B (M c4 (P h Z)) rfl
 · exact L B (P c1 (P c2 (M c4 (M h Z)))) rfl
 · exact L B (P c6 (M h Z)) rfl
 · exact L B (P c6 (P h Z)) rfl

set_option maxHeartbeats 4000000 in
lemma core8y (y : ℕ → ℤ) (B : Bs y) (H : AH y) : False := by
 rcases em (Q y false 0 1 2 3) with c1 | c1
 ·
  rcases em (Q y true 0 1 2 4) with c2 | c2
  ·
   rcases em (Q y false 0 1 5 6) with c3 | c3
   ·
    rcases em (Q y false 0 2 4 5) with c4 | c4
    ·
     rcases em (Q y false 1 2 5 6) with c5 | c5
     ·
      rcases em (Q y false 0 1 3 4) with c6 | c6
      ·
       exact s0 y B H c1 c2 c3 c4 c5 c6
      rcases em (Q y false 0 3 4 6) with c11 | c11
      ·
       exact s2 y B H c1 c2 c3 c4 c5 c11 c6
      rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact L B (P c1 (M c4 (P h Z))) rfl
      · exact L B (P c3 (P c4 (P h Z))) rfl
      · exact absurd h c11
      · exact L B (M c1 (P c3 (P c4 (P h Z)))) rfl
      · exact L B (M c3 (P h Z)) rfl
      · exact G B (P c4 (P c5 (P h Z))) rfl
      · exact L B (M c4 (P h Z)) rfl
      · exact L B (P c1 (P c2 (M c4 (M h Z)))) rfl
      · exact absurd h c6
      · exact L B (M c2 (P h Z)) rfl
     rcases H.h12456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c1 (P c3 (M h Z))) rfl
     · exact L B (P c3 (P h Z)) rfl
     · exact L B (M c1 (P c3 (M h Z))) rfl
     · exact L B (P c3 (P h Z)) rfl
     · exact absurd h c5
     · exact L B (P c3 (P h Z)) rfl
     · exact L B (M c4 (P h Z)) rfl
     · exact L B (P c3 (P c4 (P h Z))) rfl
     · exact L B (M c4 (P h Z)) rfl
     · exact L B (P c4 (P h Z)) rfl
    rcases em (Q y true 0 2 4 5) with c18 | c18
    ·
     exact s6 y B H c1 c2 c3 c18 c4
    rcases em (Q y false 0 2 4 6) with c23 | c23
    ·
     rcases em (Q y false 3 4 5 6) with c24 | c24
     ·
      rcases em (Q y false 0 2 3 5) with c25 | c25
      ·
       rcases em (Q y false 1 2 3 4) with c26 | c26
       ·
        exact s10 y B H c1 c2 c3 c23 c24 c25 c26 c4 c18
       rcases em (Q y false 1 3 4 6) with c36 | c36
       ·
        exact s13 y B H c1 c2 c3 c23 c24 c25 c36 c4 c18 c26
       rcases H.h12346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
       · exact L B (P c1 (M c3 (P h Z))) rfl
       · exact L B (P c3 (P c25 (P h Z))) rfl
       · exact absurd h c36
       · exact L B (P c23 (P h Z)) rfl
       · exact L B (M c23 (P h Z)) rfl
       · exact L B (P c23 (P h Z)) rfl
       · exact L B (M c23 (P h Z)) rfl
       · exact L B (P c3 (P c25 (P h Z))) rfl
       · exact absurd h c26
       · exact L B (P c3 (M c24 (P h Z))) rfl
      rcases em (Q y false 2 3 4 5) with c45 | c45
      ·
       rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
       · exact L B (P c1 (M c23 (P c45 (P h Z)))) rfl
       · exact LN B 1 1 c25 (P c23 (M c24 Z)) (M c23 (P c24 Z)) rfl rfl
       · exact LN B 1 1 c25 (P c23 (M c24 Z)) (M c23 (P c24 Z)) rfl rfl
       · exact LN B 1 1 c25 (P c23 (M c24 Z)) (M c23 (P c24 Z)) rfl rfl
       · exact L B (M c3 (P h Z)) rfl
       · exact LN B 1 1 c25 (P c23 (M c24 Z)) (M c23 (P c24 Z)) rfl rfl
       · exact L B (M c1 (P h Z)) rfl
       · exact L B (P c2 (M h Z)) rfl
       · exact L B (M c3 (P c24 (P h Z))) rfl
       · exact L B (P c2 (M h Z)) rfl
      rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact absurd h c45
      · exact L B (P c23 (P h Z)) rfl
      · exact L B (P c23 (M h Z)) rfl
      · exact L B (P c23 (P h Z)) rfl
      · exact absurd h c4
      · exact absurd h c18
      · exact absurd h c25
      · exact L B (P c23 (M c24 (P h Z))) rfl
      · exact L B (P c3 (M c24 (M h Z))) rfl
      · exact L B (P c3 (M c24 (P h Z))) rfl
     rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact absurd h c24
     · exact L B (P c3 (P h Z)) rfl
     · exact L B (P c3 (M h Z)) rfl
     · exact L B (P c3 (P h Z)) rfl
     · exact L B (P c3 (M h Z)) rfl
     · exact L B (P c3 (P h Z)) rfl
     · exact L B (P c23 (M h Z)) rfl
     · exact L B (P c23 (P h Z)) rfl
     · exact L B (P c23 (M h Z)) rfl
     · exact L B (P c23 (P h Z)) rfl
    rcases em (Q y true 0 2 4 6) with c46 | c46
    ·
     rcases H.h01346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (P c1 (P c46 (P h Z))) rfl
     · exact L B (M c46 (P h Z)) rfl
     · exact LN B 1 1 c4 (P c1 (M c3 (P h Z))) (M c1 (P c3 (M h Z))) rfl rfl
     · exact L B (M c46 (P h Z)) rfl
     · exact L B (M c3 (P h Z)) rfl
     · exact L B (P c46 (M h Z)) rfl
     · exact L B (P c46 (P h Z)) rfl
     · exact L B (P c46 (M h Z)) rfl
     · exact LN B 1 1 c4 (P c1 (P c2 (M c3 (M c46 (P h Z))))) (M c1 (M c2 (P c3 (P c46 (M h Z))))) rfl rfl
     · exact L B (M c2 (P h Z)) rfl
    rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (M c1 (P c3 (M h Z))) rfl
    · exact L B (P c3 (P h Z)) rfl
    · exact L B (P c3 (M h Z)) rfl
    · exact L B (P c3 (P h Z)) rfl
    · exact L B (P c3 (M h Z)) rfl
    · exact L B (P c3 (P h Z)) rfl
    · exact absurd h c23
    · exact absurd h c46
    · exact absurd h c4
    · exact absurd h c18
   rcases em (Q y true 0 1 5 6) with c47 | c47
   ·
    exact s17 y B H c1 c2 c47 c3
   rcases em (Q y false 0 2 5 6) with c58 | c58
   ·
    exact s24 y B H c1 c2 c58 c3 c47
   rcases em (Q y true 0 2 5 6) with c65 | c65
   ·
    exact s28 y B H c1 c2 c65 c3 c47 c58
   rcases em (Q y false 1 2 5 6) with c67 | c67
   ·
    rcases em (Q y false 0 1 3 5) with c68 | c68
    ·
     rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c1 (P c68 (M h Z))) rfl
     · exact L B (K 2 c68 (P h Z)) rfl
     · exact L B (P c68 (M h Z)) rfl
     · exact L B (P c68 (P h Z)) rfl
     · exact L B (P c68 (M h Z)) rfl
     · exact L B (P c68 (P h Z)) rfl
     · exact L B (P c68 (M h Z)) rfl
     · exact L B (P c68 (P h Z)) rfl
     · exact L B (P c68 (M h Z)) rfl
     · exact L B (P c68 (P h Z)) rfl
    rcases em (Q y true 0 1 3 5) with c69 | c69
    ·
     exact s29 y B H c1 c2 c67 c69 c3 c47 c58 c65 c68
    rcases em (Q y false 0 1 3 6) with c81 | c81
    ·
     rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c1 (P c81 (M h Z))) rfl
     · exact L B (K 2 c81 (P h Z)) rfl
     · exact L B (P c81 (M h Z)) rfl
     · exact L B (P c81 (P h Z)) rfl
     · exact L B (P c81 (M h Z)) rfl
     · exact L B (P c81 (P h Z)) rfl
     · exact absurd h c68
     · exact absurd h c69
     · exact L B (P c81 (M h Z)) rfl
     · exact L B (M c2 (P h Z)) rfl
    rcases em (Q y true 0 1 3 6) with c82 | c82
    ·
     rcases H.h02356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (P c2 (M c82 (M h Z))) rfl
     · exact L B (M c82 (P h Z)) rfl
     · exact L B (P c2 (M c82 (M h Z))) rfl
     · exact L B (M c82 (P h Z)) rfl
     · exact absurd h c58
     · exact absurd h c65
     · exact LN B 1 1 c68 (M c67 (P h Z)) (P c67 (M h Z)) rfl rfl
     · exact L B (M c82 (P h Z)) rfl
     · exact G B (P c67 (P c82 (P h Z))) rfl
     · exact L B (M c82 (P h Z)) rfl
    rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (P c67 (M h Z)) rfl
    · exact L B (P c67 (P h Z)) rfl
    · exact L B (P c67 (M h Z)) rfl
    · exact L B (P c67 (P h Z)) rfl
    · exact absurd h c3
    · exact absurd h c47
    · exact absurd h c81
    · exact absurd h c82
    · exact absurd h c68
    · exact absurd h c69
   rcases em (Q y true 1 2 5 6) with c83 | c83
   ·
    rcases H.h01257 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (P c83 (P h Z)) rfl
    · exact L B (P c83 (M h Z)) rfl
    · exact L B (P c83 (P h Z)) rfl
    · exact L B (P c83 (M h Z)) rfl
    · exact L B (P c83 (K 2 h Z)) rfl
    · exact L B (P c83 (M h Z)) rfl
    · exact L B (P c83 (K 2 h Z)) rfl
    · exact L B (P c83 (M h Z)) rfl
    · exact L B (M c1 (P h Z)) rfl
    · exact L B (P c2 (M h Z)) rfl
   rcases H.h01256 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact absurd h c67
   · exact absurd h c83
   · exact absurd h c58
   · exact absurd h c65
   · exact absurd h c3
   · exact absurd h c47
   · exact L B (M c1 (P h Z)) rfl
   · exact L B (P c2 (M h Z)) rfl
   · exact L B (M c1 (P h Z)) rfl
   · exact L B (P c2 (M h Z)) rfl
  rcases em (Q y true 0 1 2 5) with c84 | c84
  ·
   rcases em (Q y false 0 1 3 4) with c85 | c85
   ·
    rcases em (Q y false 0 2 3 5) with c86 | c86
    ·
     rcases em (Q y false 1 2 4 5) with c87 | c87
     ·
      rcases em (Q y false 0 1 4 6) with c88 | c88
      ·
       rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
       · exact L B (M c1 (P c88 (M h Z))) rfl
       · exact L B (K 2 c88 (P h Z)) rfl
       · exact L B (P c88 (M h Z)) rfl
       · exact L B (P c88 (P h Z)) rfl
       · exact L B (P c88 (M h Z)) rfl
       · exact L B (P c88 (P h Z)) rfl
       · exact L B (M c85 (P h Z)) rfl
       · exact L B (M c1 (M c84 (P c88 (P h Z)))) rfl
       · exact L B (M c85 (P h Z)) rfl
       · exact L B (M c84 (P h Z)) rfl
      rcases em (Q y true 0 1 4 6) with c89 | c89
      ·
       rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
       · exact G B (P c1 (P c87 (P c89 (P h Z)))) rfl
       · exact L B (M c89 (P h Z)) rfl
       · exact L B (P c84 (P c85 (M c89 (M h Z)))) rfl
       · exact L B (M c89 (P h Z)) rfl
       · exact L B (M c1 (M c84 (P c89 (P h Z)))) rfl
       · exact L B (M c89 (P h Z)) rfl
       · exact L B (M c85 (P h Z)) rfl
       · exact L B (P c89 (M h Z)) rfl
       · exact L B (M c85 (P h Z)) rfl
       · exact L B (M c84 (P h Z)) rfl
      rcases em (Q y false 0 2 4 6) with c90 | c90
      ·
       exact s35 y B H c1 c84 c85 c86 c87 c90 c2 c88 c89
      rcases em (Q y true 0 2 4 6) with c98 | c98
      ·
       rcases H.h23456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
       · exact L B (M c84 (P c98 (P h Z))) rfl
       · exact L B (M c98 (P h Z)) rfl
       · exact L B (M c84 (P c98 (P h Z))) rfl
       · exact L B (M c98 (P h Z)) rfl
       · exact L B (M c84 (P c98 (P h Z))) rfl
       · exact L B (M c98 (P h Z)) rfl
       · exact L B (M c84 (P c98 (P h Z))) rfl
       · exact L B (M c98 (P h Z)) rfl
       · exact G B (P c84 (P c85 (P h Z))) rfl
       · exact L B (P c87 (P h Z)) rfl
      rcases em (Q y true 1 2 4 6) with c99 | c99
      ·
       rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
       · exact L B (M c87 (P h Z)) rfl
       · exact L B (P c99 (M h Z)) rfl
       · exact L B (P c99 (P h Z)) rfl
       · exact L B (P c99 (M h Z)) rfl
       · exact L B (P c99 (K 2 h Z)) rfl
       · exact L B (P c99 (M h Z)) rfl
       · exact L B (M c85 (P h Z)) rfl
       · exact L B (P c84 (M h Z)) rfl
       · exact L B (M c85 (P h Z)) rfl
       · exact absurd h c2
      rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact L B (M c87 (P h Z)) rfl
      · exact absurd h c99
      · exact absurd h c90
      · exact absurd h c98
      · exact absurd h c88
      · exact absurd h c89
      · exact L B (M c85 (P h Z)) rfl
      · exact L B (P c84 (M h Z)) rfl
      · exact L B (M c1 (P h Z)) rfl
      · exact absurd h c2
     rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact G B (P c84 (P c85 (P h Z))) rfl
     · exact L B (M c84 (P h Z)) rfl
     · exact L B (M c85 (P c86 (M h Z))) rfl
     · exact L B (P c86 (P h Z)) rfl
     · exact absurd h c87
     · exact L B (P c86 (P h Z)) rfl
     · exact L B (M c86 (P h Z)) rfl
     · exact L B (P c86 (P h Z)) rfl
     · exact G B (P c1 (P c84 (P c85 (P c86 (P h Z))))) rfl
     · exact L B (P c85 (P h Z)) rfl
    rcases em (Q y false 0 2 4 5) with c100 | c100
    ·
     exact s40 y B H c1 c84 c85 c100 c2 c86
    rcases em (Q y false 0 3 4 5) with c109 | c109
    ·
     rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c109 (P h Z)) rfl
     · exact L B (P c109 (P h Z)) rfl
     · exact L B (M c109 (P h Z)) rfl
     · exact L B (P c109 (P h Z)) rfl
     · exact L B (M c109 (P h Z)) rfl
     · exact L B (P c1 (P c109 (P h Z))) rfl
     · exact L B (M c109 (P h Z)) rfl
     · exact L B (M c84 (P h Z)) rfl
     · exact G B (P c84 (P c109 (P h Z))) rfl
     · exact L B (P c85 (P h Z)) rfl
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact G B (P c84 (P c85 (P h Z))) rfl
    · exact L B (M c84 (P h Z)) rfl
    · exact absurd h c109
    · exact L B (M c84 (P h Z)) rfl
    · exact absurd h c100
    · exact L B (M c84 (P h Z)) rfl
    · exact absurd h c86
    · exact L B (M c84 (P h Z)) rfl
    · exact L B (P c85 (M h Z)) rfl
    · exact L B (P c85 (P h Z)) rfl
   rcases em (Q y false 0 1 3 5) with c110 | c110
   ·
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (M c1 (P c110 (M h Z))) rfl
    · exact L B (K 2 c110 (P h Z)) rfl
    · exact L B (P c110 (M h Z)) rfl
    · exact L B (P c110 (P h Z)) rfl
    · exact L B (P c110 (M h Z)) rfl
    · exact L B (P c110 (P h Z)) rfl
    · exact L B (P c110 (M h Z)) rfl
    · exact L B (P c110 (P h Z)) rfl
    · exact L B (P c110 (M h Z)) rfl
    · exact L B (P c110 (P h Z)) rfl
   rcases em (Q y false 0 1 4 5) with c111 | c111
   ·
    rcases em (Q y false 0 2 3 4) with c112 | c112
    ·
     exact s43 y B H c1 c84 c111 c112 c2 c85 c110
    rcases em (Q y false 0 2 3 5) with c124 | c124
    ·
     rcases em (Q y false 1 2 3 4) with c125 | c125
     ·
      exact s46 y B H c1 c84 c111 c124 c125 c2 c85 c110 c112
     rcases em (Q y false 2 3 4 5) with c136 | c136
     ·
      rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact LN B 1 1 c125 (M c111 (P c124 Z)) (P c111 (M c124 Z)) rfl rfl
      · exact LN B 1 1 c125 (M c1 (P c124 (M c136 Z))) (P c1 (M c124 (P c136 Z))) rfl rfl
      · exact LN B 1 1 c125 (M c111 (P c124 Z)) (P c1 (M c124 (P c136 Z))) rfl rfl
      · exact LN B 1 1 c125 (M c111 (P c124 Z)) (P c1 (M c124 (P c136 Z))) rfl rfl
      · exact L B (M c111 (P h Z)) rfl
      · exact LN B 1 1 c125 (M c111 (P c124 Z)) (P c1 (M c124 (P c136 Z))) rfl rfl
      · exact L B (M c1 (P h Z)) rfl
      · exact L B (P c84 (M h Z)) rfl
      · exact L B (M c1 (P h Z)) rfl
      · exact absurd h c2
     rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact absurd h c136
     · exact L B (M c84 (P h Z)) rfl
     · exact L B (M c1 (P c111 (M h Z))) rfl
     · exact L B (M c84 (P h Z)) rfl
     · exact G B (P c1 (P c84 (P c111 (P c124 (P h Z))))) rfl
     · exact L B (P c111 (P h Z)) rfl
     · exact L B (M c124 (P h Z)) rfl
     · exact L B (P c124 (P h Z)) rfl
     · exact absurd h c125
     · exact L B (P c124 (P h Z)) rfl
    rcases em (Q y false 2 3 4 5) with c137 | c137
    ·
     exact s51 y B H c1 c84 c111 c137 c2 c85 c110 c112 c124
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact absurd h c137
    · exact L B (P c111 (P h Z)) rfl
    · exact L B (P c111 (M h Z)) rfl
    · exact L B (M c84 (P h Z)) rfl
    · exact L B (P c111 (M h Z)) rfl
    · exact L B (P c111 (P h Z)) rfl
    · exact absurd h c124
    · exact L B (M c84 (P h Z)) rfl
    · exact absurd h c112
    · exact L B (M c84 (P h Z)) rfl
   rcases em (Q y false 0 3 4 5) with c143 | c143
   ·
    rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (M c143 (P h Z)) rfl
    · exact L B (M c84 (P h Z)) rfl
    · exact L B (M c143 (P h Z)) rfl
    · exact L B (P c143 (P h Z)) rfl
    · exact L B (M c143 (P h Z)) rfl
    · exact L B (M c84 (P h Z)) rfl
    · exact L B (M c143 (P h Z)) rfl
    · exact L B (M c84 (P h Z)) rfl
    · exact G B (P c84 (P c143 (P h Z))) rfl
    · exact L B (M c84 (P h Z)) rfl
   rcases em (Q y false 1 3 4 5) with c144 | c144
   ·
    exact s52 y B H c1 c84 c144 c2 c85 c110 c111 c143
   rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact absurd h c144
   · exact L B (M c84 (P h Z)) rfl
   · exact absurd h c143
   · exact L B (M c84 (P h Z)) rfl
   · exact absurd h c111
   · exact L B (M c84 (P h Z)) rfl
   · exact absurd h c110
   · exact L B (M c84 (P h Z)) rfl
   · exact absurd h c85
   · exact L B (M c84 (P h Z)) rfl
  rcases em (Q y false 0 1 4 5) with c149 | c149
  ·
   rcases em (Q y false 0 2 3 4) with c150 | c150
   ·
    rcases em (Q y false 1 2 4 5) with c151 | c151
    ·
     exact s54 y B H c1 c149 c150 c151 c2 c84
    rcases em (Q y false 2 3 4 5) with c158 | c158
    ·
     exact s56 y B H c1 c149 c150 c158 c2 c84 c151
    rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact absurd h c158
    · exact L B (P c149 (P h Z)) rfl
    · exact L B (M c1 (P c149 (M h Z))) rfl
    · exact L B (P c149 (P h Z)) rfl
    · exact absurd h c151
    · exact L B (P c149 (P h Z)) rfl
    · exact L B (M c150 (P h Z)) rfl
    · exact L B (P c149 (P c150 (P h Z))) rfl
    · exact L B (M c150 (P h Z)) rfl
    · exact L B (P c150 (P h Z)) rfl
   rcases em (Q y true 0 2 3 4) with c167 | c167
   ·
    exact s59 y B H c1 c149 c167 c2 c84 c150
   rcases em (Q y false 0 2 3 5) with c178 | c178
   ·
    rcases em (Q y false 1 2 3 4) with c179 | c179
    ·
     rcases em (Q y true 0 1 2 6) with c180 | c180
     ·
      exact s62 y B H c1 c149 c178 c179 c180 c2 c84 c150 c167
     rcases em (Q y true 0 1 4 6) with c191 | c191
     ·
      rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact LN B 1 1 c84 (P c191 (P h Z)) (M c191 (M h Z)) rfl rfl
      · exact L B (M c191 (P h Z)) rfl
      · exact G B (P c1 (P c178 (P c191 (P h Z)))) rfl
      · exact L B (M c191 (P h Z)) rfl
      · exact LN B 1 1 c84 (M c1 (M c179 (P c191 (P h Z)))) (P c1 (P c179 (M c191 (M h Z)))) rfl rfl
      · exact L B (M c191 (P h Z)) rfl
      · exact LN B 1 1 c2 (M c1 (M c179 (P c191 (P h Z)))) (P c1 (P c179 (M c191 (M h Z)))) rfl rfl
      · exact L B (M c191 (P h Z)) rfl
      · exact L B (P c149 (M h Z)) rfl
      · exact L B (P c149 (P h Z)) rfl
     rcases em (Q y false 0 2 4 6) with c192 | c192
     ·
      rcases em (Q y false 3 4 5 6) with c193 | c193
      ·
       rcases em (Q y false 0 1 5 6) with c194 | c194
       ·
        exact s68 y B H c1 c149 c178 c179 c192 c193 c194 c2 c84 c150 c167 c180 c191
       rcases em (Q y true 0 1 5 6) with c203 | c203
       ·
        exact s71 y B H c1 c149 c178 c179 c192 c193 c203 c2 c84 c150 c167 c180 c191 c194
       rcases H.h01356 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
       · exact L B (P c179 (P c193 (M h Z))) rfl
       · exact L B (P c179 (P c193 (P h Z))) rfl
       · exact L B (P c179 (P c193 (M h Z))) rfl
       · exact L B (P c179 (P c193 (P h Z))) rfl
       · exact absurd h c194
       · exact absurd h c203
       · exact L B (M c149 (P h Z)) rfl
       · exact G B (P c149 (P c178 (P c192 (P h Z)))) rfl
       · exact L B (M c149 (P h Z)) rfl
       · exact LN B 1 1 c191 (M c193 (P h Z)) (P c193 (M h Z)) rfl rfl
      rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact absurd h c193
      · exact L B (P c192 (P h Z)) rfl
      · exact L B (P c192 (M h Z)) rfl
      · exact L B (P c192 (P h Z)) rfl
      · exact L B (P c192 (M h Z)) rfl
      · exact L B (P c192 (P h Z)) rfl
      · exact L B (P c192 (M h Z)) rfl
      · exact L B (P c192 (P h Z)) rfl
      · exact L B (P c149 (M h Z)) rfl
      · exact L B (P c149 (P h Z)) rfl
     rcases em (Q y true 0 2 4 6) with c207 | c207
     ·
      exact s73 y B H c1 c149 c178 c179 c207 c2 c84 c150 c167 c180 c191 c192
     rcases em (Q y false 1 2 4 6) with c209 | c209
     ·
      rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact L B (P c1 (M c149 (P h Z))) rfl
      · exact L B (K 2 c209 (P h Z)) rfl
      · exact L B (P c209 (M h Z)) rfl
      · exact L B (P c209 (P h Z)) rfl
      · exact absurd h c192
      · exact absurd h c207
      · exact L B (M c149 (M c179 (P h Z))) rfl
      · exact LN B 1 1 c191 (P c179 (P h Z)) (M c179 (M h Z)) rfl rfl
      · exact absurd h c150
      · exact absurd h c167
     rcases em (Q y true 1 2 4 6) with c210 | c210
     ·
      rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact L B (P c210 (P h Z)) rfl
      · exact L B (P c210 (M h Z)) rfl
      · exact L B (P c210 (P h Z)) rfl
      · exact L B (P c210 (M h Z)) rfl
      · exact L B (M c149 (P h Z)) rfl
      · exact L B (P c210 (M h Z)) rfl
      · exact L B (P c210 (K 2 h Z)) rfl
      · exact L B (P c210 (M h Z)) rfl
      · exact L B (M c1 (P h Z)) rfl
      · exact absurd h c2
     rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact absurd h c209
     · exact absurd h c210
     · exact absurd h c192
     · exact absurd h c207
     · exact L B (M c149 (P h Z)) rfl
     · exact absurd h c191
     · exact L B (M c149 (P h Z)) rfl
     · exact absurd h c180
     · exact L B (M c1 (P h Z)) rfl
     · exact absurd h c2
    rcases em (Q y false 1 2 4 5) with c211 | c211
    ·
     rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c211 (P h Z)) rfl
     · exact LN B 1 1 c179 (M c149 (P c178 Z)) (P c149 (M c178 Z)) rfl rfl
     · exact LN B 1 1 c179 (M c149 (P c178 Z)) (P c149 (M c178 Z)) rfl rfl
     · exact LN B 1 1 c179 (M c149 (P c178 Z)) (P c149 (M c178 Z)) rfl rfl
     · exact L B (M c149 (P h Z)) rfl
     · exact LN B 1 1 c179 (M c149 (P c178 Z)) (P c149 (M c178 Z)) rfl rfl
     · exact L B (M c1 (P h Z)) rfl
     · exact LN B 1 1 c179 (M c149 (P c178 Z)) (P c149 (M c178 Z)) rfl rfl
     · exact L B (M c178 (P c211 (P h Z))) rfl
     · exact absurd h c2
    rcases em (Q y false 2 3 4 5) with c212 | c212
    ·
     rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact LN B 1 1 c179 (M c1 (P c178 (M c212 Z))) (P c1 (M c178 (P c212 Z))) rfl rfl
     · exact LN B 1 1 c179 (M c1 (P c178 (M c212 Z))) (P c149 (M c178 Z)) rfl rfl
     · exact LN B 1 1 c179 (M c1 (P c178 (M c212 Z))) (P c1 (M c178 (P c212 Z))) rfl rfl
     · exact LN B 1 1 c179 (M c1 (P c178 (M c212 Z))) (P c1 (M c178 (P c212 Z))) rfl rfl
     · exact L B (M c149 (P h Z)) rfl
     · exact LN B 1 1 c179 (M c149 (P c178 Z)) (P c149 (M c178 Z)) rfl rfl
     · exact L B (M c1 (P h Z)) rfl
     · exact LN B 1 1 c179 (M c1 (P c178 (M c212 Z))) (P c1 (M c178 (P c212 Z))) rfl rfl
     · exact L B (M c149 (P c212 (P h Z))) rfl
     · exact absurd h c2
    rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact absurd h c212
    · exact L B (P c149 (P h Z)) rfl
    · exact L B (M c1 (P c149 (M h Z))) rfl
    · exact L B (P c149 (P h Z)) rfl
    · exact absurd h c211
    · exact L B (P c149 (P h Z)) rfl
    · exact L B (M c178 (P h Z)) rfl
    · exact L B (P c178 (P h Z)) rfl
    · exact absurd h c179
    · exact L B (P c178 (P h Z)) rfl
   rcases em (Q y true 0 2 3 5) with c213 | c213
   ·
    rcases em (Q y false 1 2 4 5) with c214 | c214
    ·
     exact s74 y B H c1 c149 c213 c214 c2 c84 c150 c167 c178
    rcases em (Q y false 2 3 4 5) with c219 | c219
    ·
     exact s75 y B H c1 c149 c213 c219 c2 c84 c150 c167 c178 c214
    rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact absurd h c219
    · exact L B (P c149 (P h Z)) rfl
    · exact L B (M c1 (P c149 (M h Z))) rfl
    · exact L B (P c149 (P h Z)) rfl
    · exact absurd h c214
    · exact L B (P c149 (P h Z)) rfl
    · exact L B (P c213 (P h Z)) rfl
    · exact L B (M c213 (P h Z)) rfl
    · exact L B (P c149 (P c213 (P h Z))) rfl
    · exact L B (M c213 (P h Z)) rfl
   rcases em (Q y false 2 3 4 5) with c227 | c227
   ·
    rcases em (Q y true 0 1 2 6) with c228 | c228
    ·
     exact s77 y B H c1 c149 c227 c228 c2 c84 c150 c167 c178 c213
    rcases em (Q y true 0 1 4 6) with c235 | c235
    ·
     exact s79 y B H c1 c149 c227 c235 c2 c84 c150 c167 c178 c213 c228
    rcases em (Q y false 0 2 4 6) with c239 | c239
    ·
     rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact LN B 1 1 c178 (P c239 (M h Z)) (M c239 (P h Z)) rfl rfl
     · exact L B (P c239 (P h Z)) rfl
     · exact L B (P c239 (M h Z)) rfl
     · exact L B (P c239 (P h Z)) rfl
     · exact L B (P c239 (M h Z)) rfl
     · exact L B (P c239 (P h Z)) rfl
     · exact L B (P c239 (M h Z)) rfl
     · exact L B (P c239 (P h Z)) rfl
     · exact L B (P c149 (M h Z)) rfl
     · exact L B (P c149 (P h Z)) rfl
    rcases em (Q y true 0 2 4 6) with c240 | c240
    ·
     exact s80 y B H c1 c149 c227 c240 c2 c84 c150 c167 c178 c213 c228 c235 c239
    rcases em (Q y false 1 2 4 6) with c242 | c242
    ·
     exact s81 y B H c1 c149 c227 c242 c2 c84 c150 c167 c178 c213 c228 c235 c239 c240
    rcases em (Q y true 1 2 4 6) with c244 | c244
    ·
     rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (P c244 (P h Z)) rfl
     · exact L B (P c244 (M h Z)) rfl
     · exact L B (P c244 (P h Z)) rfl
     · exact L B (P c244 (M h Z)) rfl
     · exact L B (M c1 (M c227 (P h Z))) rfl
     · exact L B (P c244 (M h Z)) rfl
     · exact L B (P c244 (K 2 h Z)) rfl
     · exact L B (P c244 (M h Z)) rfl
     · exact L B (M c149 (P c227 (P h Z))) rfl
     · exact absurd h c2
    rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact absurd h c242
    · exact absurd h c244
    · exact absurd h c239
    · exact absurd h c240
    · exact L B (M c1 (M c227 (P h Z))) rfl
    · exact absurd h c235
    · exact L B (M c1 (P h Z)) rfl
    · exact absurd h c228
    · exact L B (M c1 (P h Z)) rfl
    · exact absurd h c2
   rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact absurd h c227
   · exact L B (P c149 (P h Z)) rfl
   · exact L B (P c149 (M h Z)) rfl
   · exact L B (P c149 (P h Z)) rfl
   · exact L B (P c149 (M h Z)) rfl
   · exact L B (P c149 (P h Z)) rfl
   · exact absurd h c178
   · exact absurd h c213
   · exact absurd h c150
   · exact absurd h c167
  rcases em (Q y true 0 1 4 5) with c245 | c245
  ·
   rcases em (Q y false 0 2 4 6) with c246 | c246
   ·
    exact s82 y B H c1 c245 c246 c2 c84 c149
   rcases em (Q y true 0 2 4 6) with c255 | c255
   ·
    exact s89 y B H c1 c245 c255 c2 c84 c149 c246
   rcases em (Q y false 1 2 4 6) with c257 | c257
   ·
    exact s90 y B H c1 c245 c257 c2 c84 c149 c246 c255
   rcases em (Q y true 1 2 4 6) with c259 | c259
   ·
    rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (P c259 (P h Z)) rfl
    · exact L B (P c259 (M h Z)) rfl
    · exact L B (P c259 (P h Z)) rfl
    · exact L B (P c259 (M h Z)) rfl
    · exact L B (P c259 (K 2 h Z)) rfl
    · exact L B (P c259 (M h Z)) rfl
    · exact L B (P c259 (K 2 h Z)) rfl
    · exact L B (P c259 (M h Z)) rfl
    · exact L B (M c1 (P h Z)) rfl
    · exact absurd h c2
   rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact absurd h c257
   · exact absurd h c259
   · exact absurd h c246
   · exact absurd h c255
   · exact L B (P c245 (P h Z)) rfl
   · exact L B (P c245 (M h Z)) rfl
   · exact L B (P c245 (P h Z)) rfl
   · exact L B (P c245 (M h Z)) rfl
   · exact L B (M c1 (P h Z)) rfl
   · exact absurd h c2
  rcases em (Q y false 0 2 4 5) with c260 | c260
  ·
   exact s91 y B H c1 c260 c2 c84 c149 c245
  rcases em (Q y true 0 2 4 5) with c270 | c270
  ·
   exact s97 y B H c1 c270 c2 c84 c149 c245 c260
  rcases em (Q y false 1 2 4 5) with c272 | c272
  ·
   rcases em (Q y false 0 1 3 4) with c273 | c273
   ·
    rcases em (Q y false 0 2 3 5) with c274 | c274
    ·
     rcases em (Q y true 0 1 2 6) with c275 | c275
     ·
      exact s98 y B H c1 c272 c273 c274 c275 c2 c84 c149 c245 c260 c270
     rcases em (Q y false 0 1 4 6) with c284 | c284
     ·
      rcases H.h02456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact L B (M c273 (P c284 (M h Z))) rfl
      · exact L B (K 2 c284 (P h Z)) rfl
      · exact L B (P c284 (M h Z)) rfl
      · exact L B (P c284 (P h Z)) rfl
      · exact L B (P c284 (M h Z)) rfl
      · exact L B (P c284 (P h Z)) rfl
      · exact L B (P c284 (M h Z)) rfl
      · exact L B (P c284 (P h Z)) rfl
      · exact absurd h c260
      · exact absurd h c270
     rcases em (Q y true 0 1 4 6) with c285 | c285
     ·
      exact s104 y B H c1 c272 c273 c274 c285 c2 c84 c149 c245 c260 c270 c275 c284
     rcases em (Q y false 0 2 4 6) with c293 | c293
     ·
      exact s110 y B H c1 c272 c273 c274 c293 c2 c84 c149 c245 c260 c270 c275 c284 c285
     rcases em (Q y true 0 2 4 6) with c302 | c302
     ·
      rcases H.h23456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact L B (P c272 (P c273 (P c302 (P h Z)))) rfl
      · exact L B (M c302 (P h Z)) rfl
      · exact LN B 1 1 c2 (P c272 (P c302 (P h Z))) (M c272 (M c302 (M h Z))) rfl rfl
      · exact L B (M c302 (P h Z)) rfl
      · exact L B (P c1 (P c272 (P c302 (P h Z)))) rfl
      · exact L B (M c302 (P h Z)) rfl
      · exact L B (P c1 (P c302 (P h Z))) rfl
      · exact L B (M c302 (P h Z)) rfl
      · exact LN B 1 1 c149 (P c1 (P h Z)) (M c1 (M h Z)) rfl rfl
      · exact L B (P c272 (P h Z)) rfl
     rcases em (Q y true 1 2 4 6) with c303 | c303
     ·
      rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact L B (M c272 (P h Z)) rfl
      · exact L B (P c303 (M h Z)) rfl
      · exact L B (P c303 (P h Z)) rfl
      · exact L B (P c303 (M h Z)) rfl
      · exact L B (P c303 (K 2 h Z)) rfl
      · exact L B (P c303 (M h Z)) rfl
      · exact L B (P c303 (K 2 h Z)) rfl
      · exact L B (P c303 (M h Z)) rfl
      · exact L B (M c273 (P h Z)) rfl
      · exact absurd h c2
     rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c272 (P h Z)) rfl
     · exact absurd h c303
     · exact absurd h c293
     · exact absurd h c302
     · exact absurd h c284
     · exact absurd h c285
     · exact L B (M c273 (P h Z)) rfl
     · exact absurd h c275
     · exact L B (M c1 (P h Z)) rfl
     · exact absurd h c2
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact LN B 1 1 c274 (P c272 (P c273 Z)) (M c272 (M c273 Z)) rfl rfl
    · exact L B (P c272 (P h Z)) rfl
    · exact L B (P c272 (M h Z)) rfl
    · exact L B (P c272 (P h Z)) rfl
    · exact absurd h c260
    · exact absurd h c270
    · exact absurd h c274
    · exact L B (P c272 (P c273 (P h Z))) rfl
    · exact L B (P c273 (M h Z)) rfl
    · exact L B (P c273 (P h Z)) rfl
   rcases em (Q y true 0 1 3 4) with c304 | c304
   ·
    rcases em (Q y false 0 2 3 4) with c305 | c305
    ·
     exact s115 y B H c1 c272 c304 c305 c2 c84 c149 c245 c260 c270 c273
    rcases em (Q y true 0 2 3 5) with c311 | c311
    ·
     exact s116 y B H c1 c272 c304 c311 c2 c84 c149 c245 c260 c270 c273 c305
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact LN B 1 1 c311 (M c272 (P c304 Z)) (P c272 (M c304 Z)) rfl rfl
    · exact L B (P c272 (P h Z)) rfl
    · exact L B (P c272 (M h Z)) rfl
    · exact L B (P c272 (P h Z)) rfl
    · exact absurd h c260
    · exact absurd h c270
    · exact L B (M c272 (P c304 (P h Z))) rfl
    · exact absurd h c311
    · exact absurd h c305
    · exact L B (M c304 (P h Z)) rfl
   rcases em (Q y false 0 1 3 5) with c317 | c317
   ·
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (M c1 (P c317 (M h Z))) rfl
    · exact L B (K 2 c317 (P h Z)) rfl
    · exact L B (P c317 (M h Z)) rfl
    · exact L B (P c317 (P h Z)) rfl
    · exact absurd h c260
    · exact absurd h c270
    · exact L B (P c317 (M h Z)) rfl
    · exact L B (P c317 (P h Z)) rfl
    · exact L B (P c317 (M h Z)) rfl
    · exact L B (P c317 (P h Z)) rfl
   rcases em (Q y true 0 1 3 5) with c318 | c318
   ·
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact LN B 1 1 c149 (P c1 (P h Z)) (M c1 (M h Z)) rfl rfl
    · exact L B (P c272 (P h Z)) rfl
    · exact L B (P c272 (M h Z)) rfl
    · exact L B (P c272 (P h Z)) rfl
    · exact absurd h c260
    · exact absurd h c270
    · exact LN B 1 1 c273 (M c272 (P h Z)) (P c272 (M h Z)) rfl rfl
    · exact L B (M c318 (P h Z)) rfl
    · exact G B (P c272 (P c318 (P h Z))) rfl
    · exact L B (M c318 (P h Z)) rfl
   rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c272 (M h Z)) rfl
   · exact L B (P c272 (P h Z)) rfl
   · exact L B (P c272 (M h Z)) rfl
   · exact L B (P c272 (P h Z)) rfl
   · exact absurd h c149
   · exact absurd h c245
   · exact absurd h c317
   · exact absurd h c318
   · exact absurd h c273
   · exact absurd h c304
  rcases em (Q y true 1 2 4 5) with c319 | c319
  ·
   rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c319 (P h Z)) rfl
   · exact L B (P c319 (M h Z)) rfl
   · exact L B (P c319 (P h Z)) rfl
   · exact L B (P c319 (M h Z)) rfl
   · exact L B (P c319 (K 2 h Z)) rfl
   · exact L B (P c319 (M h Z)) rfl
   · exact L B (P c319 (K 2 h Z)) rfl
   · exact L B (P c319 (M h Z)) rfl
   · exact L B (M c1 (P h Z)) rfl
   · exact absurd h c2
  rcases H.h01245 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact absurd h c272
  · exact absurd h c319
  · exact absurd h c260
  · exact absurd h c270
  · exact absurd h c149
  · exact absurd h c245
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c84
  · exact L B (M c1 (P h Z)) rfl
  · exact absurd h c2
 rcases em (Q y true 0 1 2 3) with c320 | c320
 ·
  rcases em (Q y false 0 1 4 5) with c321 | c321
  ·
   rcases em (Q y false 0 2 3 4) with c322 | c322
   ·
    exact s117 y B H c320 c321 c322 c1
   rcases em (Q y true 0 2 3 4) with c329 | c329
   ·
    exact s120 y B H c320 c321 c329 c1 c322
   rcases em (Q y false 0 2 3 5) with c337 | c337
   ·
    rcases em (Q y false 1 2 3 4) with c338 | c338
    ·
     rcases em (Q y true 0 1 4 6) with c339 | c339
     ·
      exact s122 y B H c320 c321 c337 c338 c339 c1 c322 c329
     rcases em (Q y false 0 2 4 6) with c345 | c345
     ·
      rcases em (Q y false 3 4 5 6) with c346 | c346
      ·
       exact s126 y B H c320 c321 c337 c338 c345 c346 c1 c322 c329 c339
      rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact absurd h c346
      · exact L B (P c345 (P h Z)) rfl
      · exact L B (P c345 (M h Z)) rfl
      · exact L B (P c345 (P h Z)) rfl
      · exact L B (P c345 (M h Z)) rfl
      · exact L B (P c345 (P h Z)) rfl
      · exact L B (P c345 (M h Z)) rfl
      · exact L B (P c345 (P h Z)) rfl
      · exact L B (P c321 (M h Z)) rfl
      · exact L B (P c321 (P h Z)) rfl
     rcases em (Q y true 0 2 4 6) with c358 | c358
     ·
      rcases H.h03456 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact L B (P c321 (P c338 (P c358 (P h Z)))) rfl
      · exact L B (M c358 (P h Z)) rfl
      · exact L B (P c320 (M c358 (M h Z))) rfl
      · exact L B (M c358 (P h Z)) rfl
      · exact L B (P c320 (M c358 (M h Z))) rfl
      · exact L B (M c358 (P h Z)) rfl
      · exact L B (P c320 (M c358 (M h Z))) rfl
      · exact L B (M c358 (P h Z)) rfl
      · exact L B (P c321 (M h Z)) rfl
      · exact L B (P c321 (P h Z)) rfl
     rcases em (Q y false 1 2 4 6) with c359 | c359
     ·
      rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact LN B 1 1 c339 (P c320 (M h Z)) (M c320 (P h Z)) rfl rfl
      · exact L B (K 2 c359 (P h Z)) rfl
      · exact L B (P c359 (M h Z)) rfl
      · exact L B (P c359 (P h Z)) rfl
      · exact absurd h c345
      · exact absurd h c358
      · exact L B (M c321 (M c338 (P h Z))) rfl
      · exact LN B 1 1 c339 (P c338 (P h Z)) (M c338 (M h Z)) rfl rfl
      · exact absurd h c322
      · exact absurd h c329
     rcases em (Q y true 1 2 4 6) with c360 | c360
     ·
      rcases H.h01247 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
      · exact L B (P c360 (P h Z)) rfl
      · exact L B (P c360 (M h Z)) rfl
      · exact L B (P c360 (P h Z)) rfl
      · exact L B (P c360 (M h Z)) rfl
      · exact L B (M c321 (P h Z)) rfl
      · exact L B (P c360 (M h Z)) rfl
      · exact L B (P c360 (K 2 h Z)) rfl
      · exact L B (P c360 (M h Z)) rfl
      · exact L B (P c320 (P h Z)) rfl
      · exact L B (P c320 (M h Z)) rfl
     rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact absurd h c359
     · exact absurd h c360
     · exact absurd h c345
     · exact absurd h c358
     · exact L B (M c321 (P h Z)) rfl
     · exact absurd h c339
     · exact L B (P c320 (P h Z)) rfl
     · exact L B (P c320 (M h Z)) rfl
     · exact L B (P c320 (P h Z)) rfl
     · exact L B (P c320 (M h Z)) rfl
    rcases em (Q y false 1 2 4 5) with c361 | c361
    ·
     rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c361 (P h Z)) rfl
     · exact LN B 1 1 c338 (M c321 (P c337 Z)) (P c321 (M c337 Z)) rfl rfl
     · exact LN B 1 1 c338 (M c321 (P c337 Z)) (P c321 (M c337 Z)) rfl rfl
     · exact LN B 1 1 c338 (M c321 (P c337 Z)) (P c321 (M c337 Z)) rfl rfl
     · exact L B (M c321 (P h Z)) rfl
     · exact LN B 1 1 c338 (M c321 (P c337 Z)) (P c321 (M c337 Z)) rfl rfl
     · exact L B (P c320 (P h Z)) rfl
     · exact L B (P c320 (M h Z)) rfl
     · exact L B (P c320 (P h Z)) rfl
     · exact L B (P c320 (M h Z)) rfl
    rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (P c320 (P c321 (M h Z))) rfl
    · exact L B (P c321 (P h Z)) rfl
    · exact L B (P c320 (P c321 (M h Z))) rfl
    · exact L B (P c321 (P h Z)) rfl
    · exact absurd h c361
    · exact L B (P c321 (P h Z)) rfl
    · exact L B (M c337 (P h Z)) rfl
    · exact L B (P c337 (P h Z)) rfl
    · exact absurd h c338
    · exact L B (P c337 (P h Z)) rfl
   rcases em (Q y true 0 2 3 5) with c362 | c362
   ·
    exact s133 y B H c320 c321 c362 c1 c322 c329 c337
   rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c320 (P c321 (M h Z))) rfl
   · exact L B (P c321 (P h Z)) rfl
   · exact L B (P c321 (M h Z)) rfl
   · exact L B (P c321 (P h Z)) rfl
   · exact L B (P c321 (M h Z)) rfl
   · exact L B (P c321 (P h Z)) rfl
   · exact absurd h c337
   · exact absurd h c362
   · exact absurd h c322
   · exact absurd h c329
  rcases em (Q y true 0 1 4 5) with c369 | c369
  ·
   exact s136 y B H c320 c369 c1 c321
  rcases em (Q y false 0 2 4 5) with c378 | c378
  ·
   exact s141 y B H c320 c378 c1 c321 c369
  rcases em (Q y true 0 2 4 5) with c382 | c382
  ·
   exact s142 y B H c320 c382 c1 c321 c369 c378
  rcases em (Q y false 1 2 4 5) with c384 | c384
  ·
   rcases em (Q y false 0 1 3 4) with c385 | c385
   ·
    exact s143 y B H c320 c384 c385 c1 c321 c369 c378 c382
   rcases em (Q y true 0 1 3 4) with c393 | c393
   ·
    rcases em (Q y false 0 2 3 4) with c394 | c394
    ·
     exact s146 y B H c320 c384 c393 c394 c1 c321 c369 c378 c382 c385
    rcases em (Q y true 0 2 3 5) with c401 | c401
    ·
     exact s148 y B H c320 c384 c393 c401 c1 c321 c369 c378 c382 c385 c394
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact LN B 1 1 c401 (M c384 (P c393 Z)) (P c384 (M c393 Z)) rfl rfl
    · exact L B (P c384 (P h Z)) rfl
    · exact L B (P c384 (M h Z)) rfl
    · exact L B (P c384 (P h Z)) rfl
    · exact absurd h c378
    · exact absurd h c382
    · exact L B (M c384 (P c393 (P h Z))) rfl
    · exact absurd h c401
    · exact absurd h c394
    · exact L B (M c393 (P h Z)) rfl
   rcases em (Q y false 0 1 3 5) with c408 | c408
   ·
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (P c320 (P c408 (M h Z))) rfl
    · exact L B (K 2 c408 (P h Z)) rfl
    · exact L B (P c408 (M h Z)) rfl
    · exact L B (P c408 (P h Z)) rfl
    · exact absurd h c378
    · exact absurd h c382
    · exact L B (P c408 (M h Z)) rfl
    · exact L B (P c408 (P h Z)) rfl
    · exact L B (P c408 (M h Z)) rfl
    · exact L B (P c408 (P h Z)) rfl
   rcases em (Q y true 0 1 3 5) with c409 | c409
   ·
    rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (P c320 (M c409 (M h Z))) rfl
    · exact L B (P c384 (P h Z)) rfl
    · exact L B (P c384 (M h Z)) rfl
    · exact L B (P c384 (P h Z)) rfl
    · exact absurd h c378
    · exact absurd h c382
    · exact LN B 1 1 c385 (M c384 (P h Z)) (P c384 (M h Z)) rfl rfl
    · exact L B (M c409 (P h Z)) rfl
    · exact G B (P c384 (P c409 (P h Z))) rfl
    · exact L B (M c409 (P h Z)) rfl
   rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c384 (M h Z)) rfl
   · exact L B (P c384 (P h Z)) rfl
   · exact L B (P c384 (M h Z)) rfl
   · exact L B (P c384 (P h Z)) rfl
   · exact absurd h c321
   · exact absurd h c369
   · exact absurd h c408
   · exact absurd h c409
   · exact absurd h c385
   · exact absurd h c393
  rcases em (Q y true 1 2 4 5) with c410 | c410
  ·
   rcases H.h01246 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c410 (P h Z)) rfl
   · exact L B (P c410 (M h Z)) rfl
   · exact L B (P c410 (P h Z)) rfl
   · exact L B (P c410 (M h Z)) rfl
   · exact L B (P c410 (K 2 h Z)) rfl
   · exact L B (P c410 (M h Z)) rfl
   · exact L B (P c320 (P h Z)) rfl
   · exact L B (P c320 (M h Z)) rfl
   · exact L B (P c320 (P h Z)) rfl
   · exact L B (P c320 (M h Z)) rfl
  rcases H.h01245 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact absurd h c384
  · exact absurd h c410
  · exact absurd h c378
  · exact absurd h c382
  · exact absurd h c321
  · exact absurd h c369
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
  · exact L B (P c320 (P h Z)) rfl
  · exact L B (P c320 (M h Z)) rfl
 rcases em (Q y false 0 1 2 4) with c411 | c411
 ·
  rcases em (Q y true 0 1 2 5) with c412 | c412
  ·
   rcases em (Q y false 0 1 3 5) with c413 | c413
   ·
    exact s150 y B H c411 c412 c413 c1 c320
   rcases em (Q y false 0 1 4 5) with c423 | c423
   ·
    exact s155 y B H c411 c412 c423 c1 c320 c413
   rcases em (Q y false 0 3 4 5) with c431 | c431
   ·
    rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (M c431 (P h Z)) rfl
    · exact L B (M c412 (P h Z)) rfl
    · exact L B (M c431 (P h Z)) rfl
    · exact L B (M c412 (P h Z)) rfl
    · exact L B (M c431 (P h Z)) rfl
    · exact L B (M c412 (P h Z)) rfl
    · exact L B (M c431 (P h Z)) rfl
    · exact L B (M c412 (P h Z)) rfl
    · exact G B (P c412 (P c431 (P h Z))) rfl
    · exact L B (M c412 (P h Z)) rfl
   rcases em (Q y false 1 3 4 5) with c432 | c432
   ·
    exact s159 y B H c411 c412 c432 c1 c320 c413 c423 c431
   rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact absurd h c432
   · exact L B (M c412 (P h Z)) rfl
   · exact absurd h c431
   · exact L B (M c412 (P h Z)) rfl
   · exact absurd h c423
   · exact L B (M c412 (P h Z)) rfl
   · exact absurd h c413
   · exact L B (M c412 (P h Z)) rfl
   · exact L B (P c411 (M h Z)) rfl
   · exact L B (P c411 (P h Z)) rfl
  rcases em (Q y false 0 1 3 5) with c437 | c437
  ·
   rcases em (Q y false 2 3 4 5) with c438 | c438
   ·
    rcases em (Q y true 0 1 2 6) with c439 | c439
    ·
     exact s161 y B H c411 c437 c438 c439 c1 c320 c412
    rcases em (Q y true 0 1 3 6) with c443 | c443
    ·
     exact s162 y B H c411 c437 c438 c443 c1 c320 c412 c439
    rcases em (Q y false 0 2 3 6) with c447 | c447
    ·
     exact s163 y B H c411 c437 c438 c447 c1 c320 c412 c439 c443
    rcases em (Q y true 0 2 3 6) with c449 | c449
    ·
     exact s164 y B H c411 c437 c438 c449 c1 c320 c412 c439 c443 c447
    rcases em (Q y false 1 2 3 6) with c451 | c451
    ·
     rcases H.h02346 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c438 (P h Z)) rfl
     · exact L B (K 2 c451 (P h Z)) rfl
     · exact L B (P c451 (M h Z)) rfl
     · exact L B (P c451 (P h Z)) rfl
     · exact L B (P c451 (M h Z)) rfl
     · exact L B (P c451 (P h Z)) rfl
     · exact absurd h c447
     · exact absurd h c449
     · exact L B (P c437 (M h Z)) rfl
     · exact L B (P c411 (P h Z)) rfl
    rcases em (Q y true 1 2 3 6) with c452 | c452
    ·
     rcases H.h01237 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (P c452 (P h Z)) rfl
     · exact L B (P c452 (M h Z)) rfl
     · exact L B (P c452 (P h Z)) rfl
     · exact L B (P c452 (M h Z)) rfl
     · exact L B (P c452 (K 2 h Z)) rfl
     · exact L B (P c452 (M h Z)) rfl
     · exact L B (P c452 (K 2 h Z)) rfl
     · exact L B (P c452 (M h Z)) rfl
     · exact absurd h c1
     · exact absurd h c320
    rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact absurd h c451
    · exact absurd h c452
    · exact absurd h c447
    · exact absurd h c449
    · exact L B (M c437 (P h Z)) rfl
    · exact absurd h c443
    · exact L B (M c411 (P h Z)) rfl
    · exact absurd h c439
    · exact absurd h c1
    · exact absurd h c320
   rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact absurd h c438
   · exact L B (K 2 c437 (P h Z)) rfl
   · exact L B (P c437 (M h Z)) rfl
   · exact L B (P c437 (P h Z)) rfl
   · exact L B (P c437 (M h Z)) rfl
   · exact L B (P c437 (P h Z)) rfl
   · exact L B (P c437 (M h Z)) rfl
   · exact L B (P c437 (P h Z)) rfl
   · exact L B (P c411 (M h Z)) rfl
   · exact L B (P c411 (P h Z)) rfl
  rcases em (Q y true 0 1 3 5) with c453 | c453
  ·
   exact s165 y B H c411 c453 c1 c320 c412 c437
  rcases em (Q y false 0 2 3 5) with c463 | c463
  ·
   rcases em (Q y false 1 2 3 4) with c464 | c464
   ·
    rcases em (Q y false 0 1 4 5) with c465 | c465
    ·
     exact s170 y B H c411 c463 c464 c465 c1 c320 c412 c437 c453
    rcases em (Q y false 1 3 4 5) with c476 | c476
    ·
     rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c464 (P h Z)) rfl
     · exact LN B 1 1 c465 (P c463 (M c464 Z)) (M c463 (P c464 Z)) rfl rfl
     · exact L B (M c463 (P h Z)) rfl
     · exact LN B 1 1 c465 (P c463 (M c464 Z)) (M c463 (P c464 Z)) rfl rfl
     · exact L B (M c463 (P h Z)) rfl
     · exact LN B 1 1 c465 (P c463 (M c464 Z)) (M c463 (P c464 Z)) rfl rfl
     · exact L B (M c463 (P h Z)) rfl
     · exact LN B 1 1 c465 (P c463 (M c464 Z)) (M c463 (P c464 Z)) rfl rfl
     · exact absurd h c1
     · exact absurd h c320
    rcases H.h01345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact absurd h c476
    · exact L B (P c463 (P h Z)) rfl
    · exact L B (P c463 (M h Z)) rfl
    · exact L B (P c463 (P h Z)) rfl
    · exact absurd h c465
    · exact L B (P c463 (M c464 (P h Z))) rfl
    · exact absurd h c437
    · exact absurd h c453
    · exact L B (P c411 (M h Z)) rfl
    · exact L B (P c411 (P h Z)) rfl
   rcases em (Q y false 1 3 4 5) with c477 | c477
   ·
    exact s176 y B H c411 c463 c477 c1 c320 c412 c437 c453 c464
   rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c411 (M c463 (P h Z))) rfl
   · exact L B (P c463 (P h Z)) rfl
   · exact absurd h c477
   · exact L B (P c463 (P h Z)) rfl
   · exact L B (P c411 (M c463 (P h Z))) rfl
   · exact L B (P c463 (P h Z)) rfl
   · exact L B (M c463 (P h Z)) rfl
   · exact L B (P c463 (P h Z)) rfl
   · exact absurd h c464
   · exact L B (K 2 c411 (P h Z)) rfl
  rcases em (Q y true 0 2 3 5) with c482 | c482
  ·
   exact s177 y B H c411 c482 c1 c320 c412 c437 c453 c463
  rcases em (Q y false 1 2 3 5) with c484 | c484
  ·
   rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact LN B 1 1 c437 (P c411 (P h Z)) (M c411 (M h Z)) rfl rfl
   · exact L B (K 2 c484 (P h Z)) rfl
   · exact L B (P c484 (M h Z)) rfl
   · exact L B (P c484 (P h Z)) rfl
   · exact L B (P c484 (M h Z)) rfl
   · exact L B (P c484 (P h Z)) rfl
   · exact absurd h c463
   · exact absurd h c482
   · exact L B (P c484 (M h Z)) rfl
   · exact L B (P c484 (P h Z)) rfl
  rcases em (Q y true 1 2 3 5) with c485 | c485
  ·
   rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c485 (P h Z)) rfl
   · exact L B (P c485 (M h Z)) rfl
   · exact L B (P c485 (P h Z)) rfl
   · exact L B (P c485 (M h Z)) rfl
   · exact L B (P c485 (K 2 h Z)) rfl
   · exact L B (P c485 (M h Z)) rfl
   · exact L B (P c485 (K 2 h Z)) rfl
   · exact L B (P c485 (M h Z)) rfl
   · exact absurd h c1
   · exact absurd h c320
  rcases H.h01235 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact absurd h c484
  · exact absurd h c485
  · exact absurd h c463
  · exact absurd h c482
  · exact absurd h c437
  · exact absurd h c453
  · exact L B (M c411 (P h Z)) rfl
  · exact absurd h c412
  · exact absurd h c1
  · exact absurd h c320
 rcases em (Q y true 0 1 2 4) with c486 | c486
 ·
  rcases em (Q y false 0 1 3 5) with c487 | c487
  ·
   rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c486 (P c487 (M h Z))) rfl
   · exact L B (K 2 c487 (P h Z)) rfl
   · exact L B (P c487 (M h Z)) rfl
   · exact L B (P c487 (P h Z)) rfl
   · exact L B (P c487 (M h Z)) rfl
   · exact L B (P c487 (P h Z)) rfl
   · exact L B (P c487 (M h Z)) rfl
   · exact L B (P c487 (P h Z)) rfl
   · exact L B (P c487 (M h Z)) rfl
   · exact L B (P c487 (P h Z)) rfl
  rcases em (Q y true 0 1 3 5) with c488 | c488
  ·
   exact s178 y B H c486 c488 c1 c320 c411 c487
  rcases em (Q y false 0 2 3 5) with c496 | c496
  ·
   rcases em (Q y false 1 2 3 4) with c497 | c497
   ·
    exact s182 y B H c486 c496 c497 c1 c320 c411 c487 c488
   rcases em (Q y false 1 2 4 5) with c506 | c506
   ·
    exact s185 y B H c486 c496 c506 c1 c320 c411 c487 c488 c497
   rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact LN B 1 1 c488 (P c486 (M h Z)) (M c486 (P h Z)) rfl rfl
   · exact L B (P c496 (P h Z)) rfl
   · exact L B (P c486 (P c496 (M h Z))) rfl
   · exact L B (P c496 (P h Z)) rfl
   · exact absurd h c506
   · exact L B (P c496 (P h Z)) rfl
   · exact L B (M c496 (P h Z)) rfl
   · exact L B (P c496 (P h Z)) rfl
   · exact absurd h c497
   · exact L B (P c496 (P h Z)) rfl
  rcases em (Q y true 0 2 3 5) with c512 | c512
  ·
   exact s187 y B H c486 c512 c1 c320 c411 c487 c488 c496
  rcases em (Q y false 1 2 3 5) with c514 | c514
  ·
   rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact LN B 1 1 c488 (P c486 (M h Z)) (M c486 (P h Z)) rfl rfl
   · exact L B (K 2 c514 (P h Z)) rfl
   · exact L B (P c514 (M h Z)) rfl
   · exact L B (P c514 (P h Z)) rfl
   · exact L B (P c514 (M h Z)) rfl
   · exact L B (P c514 (P h Z)) rfl
   · exact absurd h c496
   · exact absurd h c512
   · exact L B (P c514 (M h Z)) rfl
   · exact L B (P c514 (P h Z)) rfl
  rcases em (Q y true 1 2 3 5) with c515 | c515
  ·
   rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c515 (P h Z)) rfl
   · exact L B (P c515 (M h Z)) rfl
   · exact L B (P c515 (P h Z)) rfl
   · exact L B (P c515 (M h Z)) rfl
   · exact L B (P c515 (K 2 h Z)) rfl
   · exact L B (P c515 (M h Z)) rfl
   · exact L B (P c486 (P h Z)) rfl
   · exact L B (P c515 (M h Z)) rfl
   · exact absurd h c1
   · exact absurd h c320
  rcases H.h01235 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact absurd h c514
  · exact absurd h c515
  · exact absurd h c496
  · exact absurd h c512
  · exact absurd h c487
  · exact absurd h c488
  · exact L B (P c486 (P h Z)) rfl
  · exact L B (P c486 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases em (Q y false 0 1 3 4) with c516 | c516
 ·
  rcases em (Q y true 0 1 2 5) with c517 | c517
  ·
   rcases em (Q y false 0 2 3 5) with c518 | c518
   ·
    exact s188 y B H c516 c517 c518 c1 c320 c411 c486
   rcases em (Q y false 0 2 4 5) with c528 | c528
   ·
    exact s192 y B H c516 c517 c528 c1 c320 c411 c486 c518
   rcases em (Q y false 0 3 4 5) with c533 | c533
   ·
    rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact L B (M c533 (P h Z)) rfl
    · exact L B (P c533 (P h Z)) rfl
    · exact L B (M c533 (P h Z)) rfl
    · exact L B (P c533 (P h Z)) rfl
    · exact L B (M c533 (P h Z)) rfl
    · exact L B (M c517 (P h Z)) rfl
    · exact L B (M c533 (P h Z)) rfl
    · exact L B (M c517 (P h Z)) rfl
    · exact G B (P c517 (P c533 (P h Z))) rfl
    · exact L B (M c517 (P h Z)) rfl
   rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact G B (P c516 (P c517 (P h Z))) rfl
   · exact L B (M c517 (P h Z)) rfl
   · exact absurd h c533
   · exact L B (M c517 (P h Z)) rfl
   · exact absurd h c528
   · exact L B (M c517 (P h Z)) rfl
   · exact absurd h c518
   · exact L B (M c517 (P h Z)) rfl
   · exact L B (P c516 (M h Z)) rfl
   · exact L B (P c516 (P h Z)) rfl
  rcases em (Q y true 0 1 3 5) with c534 | c534
  ·
   exact s194 y B H c516 c534 c1 c320 c411 c486 c517
  rcases em (Q y false 0 2 3 5) with c545 | c545
  ·
   rcases em (Q y false 0 1 4 5) with c546 | c546
   ·
    rcases em (Q y false 1 2 3 4) with c547 | c547
    ·
     exact s200 y B H c516 c545 c546 c547 c1 c320 c411 c486 c517 c534
    rcases em (Q y false 1 2 4 5) with c559 | c559
    ·
     rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
     · exact L B (M c559 (P h Z)) rfl
     · exact LN B 1 1 c547 (P c516 (M c546 (P c559 Z))) (M c516 (P c546 (M c559 Z))) rfl rfl
     · exact L B (M c516 (M c559 (P h Z))) rfl
     · exact LN B 1 1 c547 (P c516 (M c546 (P c559 Z))) (M c516 (P c546 (M c559 Z))) rfl rfl
     · exact L B (M c516 (P h Z)) rfl
     · exact LN B 1 1 c547 (P c516 (M c546 (P c559 Z))) (M c516 (P c546 (M c559 Z))) rfl rfl
     · exact L B (M c546 (P h Z)) rfl
     · exact LN B 1 1 c547 (P c516 (M c546 (P c559 Z))) (M c516 (P c546 (M c559 Z))) rfl rfl
     · exact absurd h c1
     · exact absurd h c320
    rcases H.h12345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
    · exact LN B 1 1 c559 (M c516 (P c545 Z)) (P c516 (M c545 Z)) rfl rfl
    · exact L B (P c546 (P h Z)) rfl
    · exact L B (M c516 (P c545 (M h Z))) rfl
    · exact L B (P c546 (P h Z)) rfl
    · exact absurd h c559
    · exact L B (P c546 (P h Z)) rfl
    · exact L B (M c545 (P h Z)) rfl
    · exact L B (P c516 (P c546 (P h Z))) rfl
    · exact absurd h c547
    · exact L B (P c516 (P h Z)) rfl
   rcases em (Q y true 0 1 4 5) with c560 | c560
   ·
    exact s206 y B H c516 c545 c560 c1 c320 c411 c486 c517 c534 c546
   rcases em (Q y false 1 2 4 5) with c564 | c564
   ·
    exact s208 y B H c516 c545 c564 c1 c320 c411 c486 c517 c534 c546 c560
   rcases H.h01245 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact absurd h c564
   · exact L B (P c545 (P h Z)) rfl
   · exact L B (P c545 (M h Z)) rfl
   · exact L B (P c545 (P h Z)) rfl
   · exact absurd h c546
   · exact absurd h c560
   · exact L B (M c516 (P h Z)) rfl
   · exact absurd h c517
   · exact absurd h c411
   · exact absurd h c486
  rcases em (Q y true 0 2 3 5) with c570 | c570
  ·
   exact s210 y B H c516 c570 c1 c320 c411 c486 c517 c534 c545
  rcases em (Q y false 1 2 3 5) with c572 | c572
  ·
   exact s211 y B H c516 c572 c1 c320 c411 c486 c517 c534 c545 c570
  rcases em (Q y true 1 2 3 5) with c574 | c574
  ·
   rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c574 (P h Z)) rfl
   · exact L B (P c574 (M h Z)) rfl
   · exact L B (P c574 (P h Z)) rfl
   · exact L B (P c574 (M h Z)) rfl
   · exact L B (M c516 (P h Z)) rfl
   · exact L B (P c574 (M h Z)) rfl
   · exact L B (M c516 (P h Z)) rfl
   · exact L B (P c574 (M h Z)) rfl
   · exact absurd h c1
   · exact absurd h c320
  rcases H.h01235 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact absurd h c572
  · exact absurd h c574
  · exact absurd h c545
  · exact absurd h c570
  · exact L B (M c516 (P h Z)) rfl
  · exact absurd h c534
  · exact L B (M c516 (P h Z)) rfl
  · exact absurd h c517
  · exact absurd h c1
  · exact absurd h c320
 rcases em (Q y true 0 1 3 4) with c575 | c575
 ·
  exact s212 y B H c575 c1 c320 c411 c486 c516
 rcases em (Q y false 0 2 3 4) with c584 | c584
 ·
  rcases em (Q y true 0 1 2 5) with c585 | c585
  ·
   exact s216 y B H c584 c585 c1 c320 c411 c486 c516 c575
  rcases em (Q y true 0 1 3 5) with c592 | c592
  ·
   exact s219 y B H c584 c592 c1 c320 c411 c486 c516 c575 c585
  rcases em (Q y true 0 2 3 5) with c597 | c597
  ·
   exact s222 y B H c584 c597 c1 c320 c411 c486 c516 c575 c585 c592
  rcases em (Q y true 1 2 3 5) with c599 | c599
  ·
   rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (P c599 (P h Z)) rfl
   · exact L B (P c599 (M h Z)) rfl
   · exact L B (P c599 (P h Z)) rfl
   · exact L B (P c599 (M h Z)) rfl
   · exact L B (P c599 (K 2 h Z)) rfl
   · exact L B (P c599 (M h Z)) rfl
   · exact L B (P c599 (K 2 h Z)) rfl
   · exact L B (P c599 (M h Z)) rfl
   · exact absurd h c1
   · exact absurd h c320
  rcases H.h01235 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c584 (P h Z)) rfl
  · exact absurd h c599
  · exact L B (M c584 (P h Z)) rfl
  · exact absurd h c597
  · exact L B (M c584 (P h Z)) rfl
  · exact absurd h c592
  · exact L B (M c584 (P h Z)) rfl
  · exact absurd h c585
  · exact absurd h c1
  · exact absurd h c320
 rcases em (Q y true 0 2 3 4) with c600 | c600
 ·
  exact s223 y B H c600 c1 c320 c411 c486 c516 c575 c584
 rcases em (Q y false 1 2 3 4) with c602 | c602
 ·
  rcases em (Q y false 0 1 2 5) with c603 | c603
  ·
   exact s224 y B H c602 c603 c1 c320 c411 c486 c516 c575 c584 c600
  rcases em (Q y true 0 1 2 5) with c605 | c605
  ·
   exact s225 y B H c602 c605 c1 c320 c411 c486 c516 c575 c584 c600 c603
  rcases em (Q y false 0 1 3 5) with c614 | c614
  ·
   rcases H.h02345 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact LN B 1 1 c411 (P c614 (M h Z)) (M c614 (P h Z)) rfl rfl
   · exact L B (K 2 c614 (P h Z)) rfl
   · exact L B (P c614 (M h Z)) rfl
   · exact L B (P c614 (P h Z)) rfl
   · exact L B (P c614 (M h Z)) rfl
   · exact L B (P c614 (P h Z)) rfl
   · exact L B (P c614 (M h Z)) rfl
   · exact L B (P c614 (P h Z)) rfl
   · exact absurd h c584
   · exact absurd h c600
  rcases em (Q y true 0 1 3 5) with c615 | c615
  ·
   exact s229 y B H c602 c615 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614
  rcases em (Q y false 0 2 3 5) with c622 | c622
  ·
   exact s233 y B H c602 c622 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614 c615
  rcases em (Q y true 0 2 3 5) with c631 | c631
  ·
   exact s238 y B H c602 c631 c1 c320 c411 c486 c516 c575 c584 c600 c603 c605 c614 c615 c622
  rcases em (Q y true 1 2 3 5) with c633 | c633
  ·
   rcases H.h01236 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
   · exact L B (M c602 (P h Z)) rfl
   · exact L B (P c633 (M h Z)) rfl
   · exact L B (P c633 (P h Z)) rfl
   · exact L B (P c633 (M h Z)) rfl
   · exact L B (P c633 (K 2 h Z)) rfl
   · exact L B (P c633 (M h Z)) rfl
   · exact L B (P c633 (K 2 h Z)) rfl
   · exact L B (P c633 (M h Z)) rfl
   · exact absurd h c1
   · exact absurd h c320
  rcases H.h01235 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (M c602 (P h Z)) rfl
  · exact absurd h c633
  · exact absurd h c622
  · exact absurd h c631
  · exact absurd h c614
  · exact absurd h c615
  · exact absurd h c603
  · exact absurd h c605
  · exact absurd h c1
  · exact absurd h c320
 rcases em (Q y true 1 2 3 4) with c634 | c634
 ·
  rcases H.h01235 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
  · exact L B (P c634 (P h Z)) rfl
  · exact L B (P c634 (M h Z)) rfl
  · exact L B (P c634 (P h Z)) rfl
  · exact L B (P c634 (M h Z)) rfl
  · exact L B (P c634 (K 2 h Z)) rfl
  · exact L B (P c634 (M h Z)) rfl
  · exact L B (P c634 (K 2 h Z)) rfl
  · exact L B (P c634 (M h Z)) rfl
  · exact absurd h c1
  · exact absurd h c320
 rcases H.h01234 with (h|h)|(h|h)|(h|h)|(h|h)|(h|h)
 · exact absurd h c602
 · exact absurd h c634
 · exact absurd h c584
 · exact absurd h c600
 · exact absurd h c516
 · exact absurd h c575
 · exact absurd h c411
 · exact absurd h c486
 · exact absurd h c1
 · exact absurd h c320

lemma core8 (f : Fin 8 → ℤ) (hpos : ∀ i, 0 < f i) (hodd : ∀ i, f i % 2 = 1) (hm : StrictMono f)
    (H : ∀ i j k l m : Fin 8, i < j → j < k → k < l → l < m → R5 (f i) (f j) (f k) (f l) (f m)) : False := by
  obtain ⟨y, hy8, hy⟩ : ∃ y : ℕ → ℤ, y 8 = 1 ∧ ∀ i : Fin 8, y i = f i / 2 :=
    ⟨fun i ↦ if h : i < 8 then f ⟨i, h⟩ / 2 else 1, by simp, fun i ↦ by simp⟩
  have e0 : y 0 = f 0 / 2 := hy 0
  have e1 : y 1 = f 1 / 2 := hy 1
  have e2 : y 2 = f 2 / 2 := hy 2
  have e3 : y 3 = f 3 / 2 := hy 3
  have e4 : y 4 = f 4 / 2 := hy 4
  have e5 : y 5 = f 5 / 2 := hy 5
  have e6 : y 6 = f 6 / 2 := hy 6
  have e7 : y 7 = f 7 / 2 := hy 7
  have o0 := hodd 0
  have o1 := hodd 1
  have o2 := hodd 2
  have o3 := hodd 3
  have o4 := hodd 4
  have o5 := hodd 5
  have o6 := hodd 6
  have o7 := hodd 7
  have m0 : f 0 < f 1 := hm (by decide)
  have m1 : f 1 < f 2 := hm (by decide)
  have m2 : f 2 < f 3 := hm (by decide)
  have m3 : f 3 < f 4 := hm (by decide)
  have m4 : f 4 < f 5 := hm (by decide)
  have m5 : f 5 < f 6 := hm (by decide)
  have m6 : f 6 < f 7 := hm (by decide)
  have p0 := hpos 0
  have B : Bs y := ⟨hy8, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have r : ∀ a b c d : Fin 8, R4 (f a) (f b) (f c) (f d) → R4y y a b c d := fun a b c d h ↦
    r4c a.isLt b.isLt c.isLt d.isLt hy8 (hy a) (hy b) (hy c) (hy d) (hodd a) (hodd b) (hodd c)
      (hodd d) h
  have KK : ∀ i j k l m : Fin 8, i < j → j < k → k < l → l < m → R5y y i j k l m := by
    intro i j k l m h1 h2 h3 h4
    have h := H i j k l m h1 h2 h3 h4
    unfold R5 at h
    rcases h with h | h | h | h | h
    · exact Or.inl (r _ _ _ _ h)
    · exact Or.inr (Or.inl (r _ _ _ _ h))
    · exact Or.inr (Or.inr (Or.inl (r _ _ _ _ h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (r _ _ _ _ h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (r _ _ _ _ h))))
  exact core8y y B
    ⟨KK 0 1 2 3 4 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 2 3 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 2 4 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 2 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 2 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 3 4 5 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 3 4 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 3 4 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 3 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 3 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 4 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 4 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 4 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 1 5 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 3 4 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 3 4 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 3 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 3 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 3 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 4 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 4 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 2 5 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 0 3 4 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 3 4 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 3 5 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 0 4 5 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 3 4 6 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 3 4 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 3 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 3 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 3 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 4 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 4 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 4 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 2 5 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 3 4 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 1 3 4 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 3 4 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 3 5 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 1 4 5 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 2 3 4 5 6 (by decide) (by decide) (by decide) (by decide),
     KK 2 3 4 5 7 (by decide) (by decide) (by decide) (by decide),
     KK 2 3 4 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 2 3 5 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 2 4 5 6 7 (by decide) (by decide) (by decide) (by decide),
     KK 3 4 5 6 7 (by decide) (by decide) (by decide) (by decide)⟩

lemma SO34 : SO 3 4 := by
  intro P hpos hodd hD
  by_contra hlt
  obtain ⟨f, hm, hf⟩ := exists_sorted (k := 5) (by omega : 5 ≤ P.card)
  refine core5 f (fun i ↦ hpos _ (hf i)) (fun i ↦ hodd _ (hf i)) hm ?_
  intro i j k l h1 h2 h3
  have hij := hm h1
  have hjk := hm h2
  have hkl := hm h3
  refine odd4 (hpos _ (hf i)) hij hjk hkl (hodd _ (hf i)) (hodd _ (hf j)) (hodd _ (hf k))
    (hodd _ (hf l)) (hD _ ?_ (card4 hij hjk hkl))
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> exact hf _

lemma SO47 : SO 4 7 := by
  intro P hpos hodd hD
  by_contra hlt
  obtain ⟨f, hm, hf⟩ := exists_sorted (k := 8) (by omega : 8 ≤ P.card)
  refine core8 f (fun i ↦ hpos _ (hf i)) (fun i ↦ hodd _ (hf i)) hm ?_
  intro i j k l m h1 h2 h3 h4
  have hij := hm h1
  have hjk := hm h2
  have hkl := hm h3
  have hlm := hm h4
  refine odd5 (hpos _ (hf i)) hij hjk hkl hlm (hodd _ (hf i)) (hodd _ (hf j)) (hodd _ (hf k))
    (hodd _ (hf l)) (hodd _ (hf m)) (hD _ ?_ (card5 hij hjk hkl hlm))
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl <;> exact hf _

lemma S11 : S 1 1 := step SO11 S00
lemma S23 : S 2 3 := step SO22 S11
lemma S37 : S 3 7 := step SO34 S23
lemma S414 : S 4 14 := step SO47 S37

theorem H1_proof : OMA.R_Erdos963_erdos_963_parts_ii_R1.H1 := by
  intro d hd P hpos hD
  have hD' : ∀ D ⊆ P, D.card = d + 1 → Rel D 0 ((0 : ℤ) ≠ 0) := fun D hDP hc ↦
    rel_of_not_diss (hD D hDP hc)
  interval_cases d
  · have := S00 P hpos hD'
    exact ⟨by omega, by omega⟩
  · have := S11 P hpos hD'
    exact ⟨by omega, by omega⟩
  · have := S23 P hpos hD'
    exact ⟨by omega, by omega⟩
  · have := S37 P hpos hD'
    exact ⟨by omega, by omega⟩
  · have := S414 P hpos hD'
    exact ⟨by omega, fun _ ↦ this⟩

end OMA.E963H1

theorem OMA.solution : OMA.R_Erdos963_erdos_963_parts_ii_R1.H1 := OMA.E963H1.H1_proof
