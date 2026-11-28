import OMAStatements.S_opg_blatter_specker_theorem_for_ternary_relations
import Mathlib

/- The iterated matching construction of Fischer and Makowsky, arXiv:2206.12135. -/

open OMA.S_opg_blatter_specker_theorem_for_ternary_relations

namespace SpeckerHierarchy

open Set

structure Hierarchy (k : ℕ) (V : Type) where
  rank : V → V → ℕ
  bound : ∀ x y, rank x y ≤ k
  zero_iff : ∀ x y, rank x y = 0 ↔ x = y
  symmetric : ∀ x y, rank x y = rank y x
  triangle : ∀ x y z, rank x z ≤ max (rank x y) (rank y z)
  realizes : ∀ x i, i ≤ k → ∃ y, rank x y = i
  no_positive_equilateral : ∀ x y z, rank x y ≠ 0 → rank x y = rank x z →
    rank x y ≠ rank y z

namespace Hierarchy

variable {k : ℕ} {V : Type}

theorem rank_self (H : Hierarchy k V) (x : V) : H.rank x x = 0 :=
  (H.zero_iff x x).2 rfl

def block (H : Hierarchy k V) (x : V) (i : ℕ) : Set V :=
  {y | H.rank x y ≤ i}

theorem mem_block_self (H : Hierarchy k V) (x : V) (i : ℕ) : x ∈ H.block x i := by
  show H.rank x x ≤ i
  simp [H.rank_self]

def restrict (H : Hierarchy k V) (x : V) {i : ℕ} (hi : i ≤ k) :
    Hierarchy i (H.block x i) where
  rank v w := H.rank v w
  bound v w := by
    have h := H.triangle v x w
    rw [H.symmetric v x] at h
    exact h.trans (max_le v.property w.property)
  zero_iff v w := by rw [H.zero_iff, Subtype.coe_inj]
  symmetric v w := H.symmetric _ _
  triangle v w z := H.triangle _ _ _
  realizes v j hj := by
    obtain ⟨w, hw⟩ := H.realizes v j (hj.trans hi)
    have hw' : H.rank x w ≤ i :=
      (H.triangle x v w).trans (max_le v.property (hw ▸ hj))
    exact ⟨⟨w, hw'⟩, hw⟩
  no_positive_equilateral v w z := H.no_positive_equilateral _ _ _

theorem complementary_blocks (H : Hierarchy (k + 1) V) {x y : V}
    (hxy : H.rank x y = k + 1) : H.block y k = (H.block x k)ᶜ := by
  ext z
  change H.rank y z ≤ k ↔ ¬ H.rank x z ≤ k
  have hT := H.triangle x z y
  rw [hxy, H.symmetric z y] at hT
  have hx := H.bound x z
  have hy := H.bound y z
  constructor
  · intro hy' hx'
    have := hT.trans (max_le hx' hy')
    omega
  · intro hx'
    by_contra! hy'
    have heqx : H.rank x y = H.rank x z := by omega
    have heqy : H.rank x y = H.rank y z := by omega
    exact H.no_positive_equilateral x y z (by omega) heqx heqy

theorem card_of : ∀ {V : Type} [Fintype V] [Nonempty V],
    Hierarchy k V → Fintype.card V = 2 ^ k := by
  induction k with
  | zero =>
    intro V _ _ H
    have : Subsingleton V :=
      ⟨fun x y => (H.zero_iff x y).1 (Nat.eq_zero_of_le_zero (H.bound x y))⟩
    let : Unique V := uniqueOfSubsingleton (Classical.choice (inferInstance : Nonempty V))
    simp
  | succ k ih =>
    intro V _ _ H
    classical
    let x : V := Classical.choice (inferInstance : Nonempty V)
    obtain ⟨y, hy⟩ := H.realizes x (k + 1) (by omega)
    let X := H.block x k
    let Y := H.block y k
    have hXY : Y = Xᶜ := H.complementary_blocks hy
    have : Nonempty X := ⟨⟨x, H.mem_block_self x k⟩⟩
    have : Nonempty Y := ⟨⟨y, H.mem_block_self y k⟩⟩
    have hX : Fintype.card X = 2 ^ k := ih (H.restrict x (Nat.le_succ k))
    have hY : Fintype.card Y = 2 ^ k := ih (H.restrict y (Nat.le_succ k))
    have hc : Fintype.card (Xᶜ : Set V) = 2 ^ k := by simpa only [hXY] using hY
    rw [← Fintype.card_congr (Equiv.Set.sumCompl X), Fintype.card_sum, hX, hc, pow_succ]
    omega

end Hierarchy

private theorem choose_half_pow_mod_two (k : ℕ) :
    (2 ^ (k + 1) - 1).choose (2 ^ k - 1) ≡ 1 [MOD 2] := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hn : 2 ^ (k + 1 + 1) - 1 = 2 * (2 ^ (k + 1) - 1) + 1 := by
      rw [pow_succ]
      have h := Nat.two_pow_pos (k + 1)
      omega
    have hm : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      rw [pow_succ]
      have h := Nat.two_pow_pos k
      omega
    have h : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have reduce (m : ℕ) : (2 * m + 1) % 2 = 1 ∧ (2 * m + 1) / 2 = m := by omega
    have h₁ := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := 2 * (2 ^ (k + 1) - 1) + 1) (k := 2 * (2 ^ k - 1) + 1) (p := 2)
    have h₂ : (2 * (2 ^ (k + 1) - 1) + 1).choose (2 * (2 ^ k - 1) + 1) ≡
        (2 ^ (k + 1) - 1).choose (2 ^ k - 1) [MOD 2] := by
      simpa only [(reduce _).1, (reduce _).2, Nat.choose_self, one_mul] using h₁
    exact hn ▸ hm ▸ h₂.trans ih

theorem not_periodic_pow_support (u : ℕ → ℕ)
    (hOn : ∀ n, (∃ k : ℕ, n + 2 = 2 ^ k) → u n % 2 = 1)
    (hOff : ∀ n, (¬ ∃ k : ℕ, n + 2 = 2 ^ k) → u n % 2 = 0) :
    ¬ ∃ N T : ℕ, 0 < T ∧ ∀ n ≥ N, u (n + T) ≡ u n [MOD 2] := by
  classical
  rintro ⟨N, T, hT, h⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (N + T + 2) (by decide : 1 < (2 : ℕ))
  let n := 2 ^ k - 2
  have hn : n + 2 = 2 ^ k := by dsimp [n]; omega
  have hnN : N ≤ n := by omega
  have hu₀ : u n % 2 = 1 := hOn n ⟨k, hn⟩
  have hu₁ : u (n + T) % 2 = 0 := by
    apply hOff
    rintro ⟨j, hj⟩
    have h₁ : 2 ^ k < 2 ^ j := by omega
    have hjk : k < j := (pow_lt_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).1 h₁
    have h₂ : 2 ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hjk
    rw [pow_succ] at h₂
    omega
  have hm := h n hnN
  change u (n + T) % 2 = u n % 2 at hm
  rw [hu₀, hu₁] at hm
  contradiction

namespace Hierarchy

variable {k : ℕ} {V W : Type}

theorem ext_rank {H J : Hierarchy k V} (h : ∀ x y, H.rank x y = J.rank x y) :
    H = J := by
  have hr : H.rank = J.rank := funext fun x => funext (h x)
  cases H
  cases J
  cases hr
  rfl

instance [Finite V] : Finite (Hierarchy k V) :=
  Finite.of_injective (fun h : Hierarchy k V => fun x y : V =>
    (⟨h.rank x y, Nat.lt_succ_of_le (h.bound x y)⟩ : Fin (k + 1)))
    (fun _H _J h => ext_rank fun x y => congrArg Fin.val (congrFun (congrFun h x) y))

noncomputable instance [Finite V] : Fintype (Hierarchy k V) := Fintype.ofFinite _

def relabel (e : V ≃ W) (H : Hierarchy k V) : Hierarchy k W where
  rank x y := H.rank (e.symm x) (e.symm y)
  bound x y := H.bound _ _
  zero_iff x y := (H.zero_iff _ _).trans e.symm.injective.eq_iff
  symmetric x y := H.symmetric _ _
  triangle x y z := H.triangle _ _ _
  realizes x i hi := by
    obtain ⟨y, hy⟩ := H.realizes (e.symm x) i hi
    exact ⟨e y, by simpa using hy⟩
  no_positive_equilateral x y z := H.no_positive_equilateral _ _ _

def relabelEquiv (e : V ≃ W) : Hierarchy k V ≃ Hierarchy k W where
  toFun := relabel e
  invFun := relabel e.symm
  left_inv H := by apply ext_rank; intro x y; simp [relabel]
  right_inv H := by apply ext_rank; intro x y; simp [relabel]

def sumRank (H : Hierarchy k V) (J : Hierarchy k W) : V ⊕ W → V ⊕ W → ℕ
  | .inl x, .inl y => H.rank x y
  | .inr x, .inr y => J.rank x y
  | .inl _, .inr _ | .inr _, .inl _ => k + 1

def join [Nonempty V] [Nonempty W] (H : Hierarchy k V) (J : Hierarchy k W) :
    Hierarchy (k + 1) (V ⊕ W) where
  rank := sumRank H J
  bound x y := by
    cases x <;> cases y <;> simp only [sumRank]
    · exact (H.bound _ _).trans (Nat.le_succ k)
    · exact le_rfl
    · exact le_rfl
    · exact (J.bound _ _).trans (Nat.le_succ k)
  zero_iff x y := by
    cases x <;> cases y <;> simp [sumRank, H.zero_iff, J.zero_iff]
  symmetric x y := by
    cases x <;> cases y <;> simp only [sumRank, H.symmetric, J.symmetric]
  triangle x y z := by
    cases x <;> cases y <;> cases z <;> simp only [sumRank]
    all_goals first | exact H.triangle _ _ _ | exact J.triangle _ _ _ |
      exact le_max_left _ _ | exact le_max_right _ _ |
      exact (H.bound _ _).trans ((Nat.le_succ _).trans (le_max_left _ _)) |
      exact (J.bound _ _).trans ((Nat.le_succ _).trans (le_max_left _ _))
  realizes x i hi := by
    cases x with
    | inl x =>
      by_cases hik : i ≤ k
      · obtain ⟨y, hy⟩ := H.realizes x i hik
        exact ⟨.inl y, hy⟩
      · exact ⟨.inr (Classical.choice inferInstance), by dsimp [sumRank]; omega⟩
    | inr x =>
      by_cases hik : i ≤ k
      · obtain ⟨y, hy⟩ := J.realizes x i hik
        exact ⟨.inr y, hy⟩
      · exact ⟨.inl (Classical.choice inferInstance), by dsimp [sumRank]; omega⟩
  no_positive_equilateral x y z := by
    have hH (a b : V) : H.rank a b ≠ k + 1 := by
      have := H.bound a b
      omega
    have hJ (a b : W) : J.rank a b ≠ k + 1 := by
      have := J.bound a b
      omega
    have hH' (a b : V) : k + 1 ≠ H.rank a b := (hH a b).symm
    have hJ' (a b : W) : k + 1 ≠ J.rank a b := (hJ a b).symm
    cases x <;> cases y <;> cases z <;> simp [sumRank, hH, hJ, hH', hJ']
    · exact H.no_positive_equilateral _ _ _
    · exact J.no_positive_equilateral _ _ _

theorem block_card [Fintype V] (H : Hierarchy (k + 1) V) (x : V) :
    Nat.card (H.block x k) = 2 ^ k := by
  classical
  let _ : Nonempty (H.block x k) := ⟨⟨x, H.mem_block_self x k⟩⟩
  rw [Nat.card_eq_fintype_card]
  exact card_of (H.restrict x (Nat.le_succ k))

theorem rank_le_of_same_side (H : Hierarchy (k + 1) V) {x u v : V}
    (hu : u ∈ H.block x k ↔ v ∈ H.block x k) : H.rank u v ≤ k := by
  by_cases hux : u ∈ H.block x k
  · have hvx := hu.mp hux
    have h := H.triangle u x v
    rw [H.symmetric u x] at h
    exact h.trans (max_le hux hvx)
  · obtain ⟨y, hy⟩ := H.realizes x (k + 1) le_rfl
    have hyx := H.complementary_blocks hy
    have hu' : u ∈ H.block y k := by rw [hyx]; exact hux
    have hv' : v ∈ H.block y k := by rw [hyx]; exact fun h => hux (hu.mpr h)
    have h := H.triangle u y v
    rw [H.symmetric u y] at h
    exact h.trans (max_le hu' hv')

theorem same_side_of_rank_le (H : Hierarchy (k + 1) V) {x u v : V}
    (huv : H.rank u v ≤ k) : u ∈ H.block x k ↔ v ∈ H.block x k := by
  constructor
  · intro hu
    exact (H.triangle x u v).trans (max_le hu huv)
  · intro hv
    rw [H.symmetric] at huv
    exact (H.triangle x v u).trans (max_le hv huv)

end Hierarchy
namespace Hierarchy

open Finset
open scoped BigOperators

variable {k : ℕ} {V : Type} [Fintype V] [DecidableEq V]

abbrev SplitChoice (x : V) (k : ℕ) :=
  ↥((Finset.univ.erase x).powersetCard (2 ^ k - 1))

def Side (x : V) (s : SplitChoice x k) : Set V := (↑(insert x s.val) : Set V)

instance (x : V) (s : SplitChoice x k) : DecidablePred (· ∈ Side x s) :=
  fun y => inferInstanceAs (Decidable (y ∈ insert x s.val))

theorem side_self (x : V) (s : SplitChoice x k) : x ∈ Side x s := by
  simp [Side]

theorem side_finset_card {x : V} (s : SplitChoice x k) :
    (insert x s.val).card = 2 ^ k := by
  have hs := Finset.mem_powersetCard.mp s.property
  have hx : x ∉ s.val := fun hx => (Finset.notMem_erase x _) (hs.1 hx)
  rw [Finset.card_insert_of_notMem hx, hs.2]
  have := Nat.two_pow_pos k
  omega

noncomputable def topChoice (H : Hierarchy (k + 1) V) (x : V) : SplitChoice x k := by
  classical
  let s := Finset.univ.filter fun y => y ∈ H.block x k
  have hx : x ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, H.mem_block_self x k⟩
  have hs : s.card = 2 ^ k := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact H.block_card x
  refine ⟨s.erase x, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
  · exact Finset.erase_subset_erase _ (Finset.subset_univ s)
  · rw [Finset.card_erase_of_mem hx, hs]

theorem topChoice_side (H : Hierarchy (k + 1) V) (x : V) :
    Side x (H.topChoice x) = H.block x k := by
  classical
  ext y
  simp only [Side, topChoice, Finset.mem_coe, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (he | ⟨_, hy⟩)
    · rw [he]; exact H.mem_block_self x k
    · exact hy
  · intro hy
    by_cases h : y = x
    · exact Or.inl h
    · exact Or.inr ⟨h, hy⟩

theorem topChoice_eq_of_side_eq {H : Hierarchy (k + 1) V} {x : V}
    {s : SplitChoice x k} (h : H.block x k = Side x s) : H.topChoice x = s := by
  have hs := (H.topChoice_side x).trans h
  apply Subtype.ext
  ext y
  have ht := Finset.mem_powersetCard.mp (H.topChoice x).property
  have hu := Finset.mem_powersetCard.mp s.property
  by_cases hy : y = x
  · subst y
    exact ⟨fun h => (Finset.notMem_erase _ _) (ht.1 h) |>.elim,
      fun h => (Finset.notMem_erase _ _) (hu.1 h) |>.elim⟩
  · have := Set.ext_iff.mp hs y
    simpa [Side, hy] using this

noncomputable def fromChoice {x : V} (s : SplitChoice x k)
    (hV : Fintype.card V = 2 ^ (k + 1))
    (L : Hierarchy k (Side x s)) (R : Hierarchy k ((Side x s)ᶜ : Set V)) :
    Hierarchy (k + 1) V := by
  classical
  let _ : Nonempty (Side x s) := ⟨⟨x, side_self x s⟩⟩
  let _ : Nonempty ((Side x s)ᶜ : Set V) := by
    have hlt : (insert x s.val).card < (Finset.univ : Finset V).card := by
      rw [side_finset_card, Finset.card_univ, hV, pow_succ]
      have := Nat.two_pow_pos k
      omega
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨⟨a, ha⟩⟩
  exact (join L R).relabel (Equiv.Set.sumCompl (Side x s))

theorem fromChoice_ll {x : V} (s : SplitChoice x k) (hV : Fintype.card V = 2 ^ (k + 1))
    (L : Hierarchy k (Side x s)) (R : Hierarchy k ((Side x s)ᶜ : Set V))
    {a b : V} (ha : a ∈ Side x s) (hb : b ∈ Side x s) :
    (fromChoice s hV L R).rank a b = L.rank ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [fromChoice, relabel, Equiv.Set.sumCompl_symm_apply_of_mem, ha, hb, join, sumRank]

theorem fromChoice_rr {x : V} (s : SplitChoice x k) (hV : Fintype.card V = 2 ^ (k + 1))
    (L : Hierarchy k (Side x s)) (R : Hierarchy k ((Side x s)ᶜ : Set V))
    {a b : V} (ha : a ∉ Side x s) (hb : b ∉ Side x s) :
    (fromChoice s hV L R).rank a b = R.rank ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [fromChoice, relabel, Equiv.Set.sumCompl_symm_apply_of_notMem, ha, hb, join, sumRank]

theorem fromChoice_lr {x : V} (s : SplitChoice x k) (hV : Fintype.card V = 2 ^ (k + 1))
    (L : Hierarchy k (Side x s)) (R : Hierarchy k ((Side x s)ᶜ : Set V))
    {a b : V} (ha : a ∈ Side x s) (hb : b ∉ Side x s) :
    (fromChoice s hV L R).rank a b = k + 1 := by
  simp [fromChoice, relabel, Equiv.Set.sumCompl_symm_apply_of_mem,
    Equiv.Set.sumCompl_symm_apply_of_notMem, ha, hb, join, sumRank]

theorem fromChoice_topChoice {x : V} (s : SplitChoice x k)
    (hV : Fintype.card V = 2 ^ (k + 1))
    (L : Hierarchy k (Side x s)) (R : Hierarchy k ((Side x s)ᶜ : Set V)) :
    (fromChoice s hV L R).topChoice x = s := by
  apply topChoice_eq_of_side_eq
  ext b
  change (fromChoice s hV L R).rank x b ≤ k ↔ b ∈ Side x s
  by_cases hb : b ∈ Side x s
  · rw [fromChoice_ll s hV L R (side_self x s) hb]
    simp [L.bound, hb]
  · rw [fromChoice_lr s hV L R (side_self x s) hb]
    simp [hb]

noncomputable def leftHierarchy (H : Hierarchy (k + 1) V) (x : V)
    (s : SplitChoice x k) (hs : H.topChoice x = s) : Hierarchy k (Side x s) :=
  (H.restrict x (Nat.le_succ k)).relabel
    (Equiv.setCongr ((H.topChoice_side x).symm.trans (congrArg (Side x) hs)))

noncomputable def rightHierarchy (H : Hierarchy (k + 1) V) (x : V)
    (s : SplitChoice x k) (hs : H.topChoice x = s) :
    Hierarchy k ((Side x s)ᶜ : Set V) := by
  let y := Classical.choose (H.realizes x (k + 1) le_rfl)
  have hy : H.rank x y = k + 1 := Classical.choose_spec (H.realizes x (k + 1) le_rfl)
  exact (H.restrict y (Nat.le_succ k)).relabel (Equiv.setCongr
    ((H.complementary_blocks hy).trans (congrArg Set.compl
      ((H.topChoice_side x).symm.trans (congrArg (Side x) hs)))))

noncomputable def choiceFiberEquiv (x : V) (s : SplitChoice x k)
    (hV : Fintype.card V = 2 ^ (k + 1)) :
    {H : Hierarchy (k + 1) V // H.topChoice x = s} ≃
      Hierarchy k (Side x s) × Hierarchy k ((Side x s)ᶜ : Set V) where
  toFun H := (H.val.leftHierarchy x s H.property, H.val.rightHierarchy x s H.property)
  invFun P := ⟨fromChoice s hV P.1 P.2, fromChoice_topChoice s hV P.1 P.2⟩
  left_inv := by
    rintro ⟨H, hs⟩
    apply Subtype.ext
    apply ext_rank
    intro a b
    change (fromChoice s hV (H.leftHierarchy x s hs) (H.rightHierarchy x s hs)).rank a b =
      H.rank a b
    have he : H.block x k = Side x s :=
      (H.topChoice_side x).symm.trans (congrArg (Side x) hs)
    have hcross {u v : V} (hu : u ∈ Side x s) (hv : v ∉ Side x s) : H.rank u v = k + 1 := by
      have hlt : ¬ H.rank u v ≤ k := by
        intro hp
        have hsame := H.same_side_of_rank_le (x := x) hp
        rw [he] at hsame
        exact hv (hsame.mp hu)
      have := H.bound u v
      omega
    by_cases ha : a ∈ Side x s <;> by_cases hb : b ∈ Side x s
    · rw [fromChoice_ll s hV _ _ ha hb]
      rfl
    · rw [fromChoice_lr s hV _ _ ha hb, hcross ha hb]
    · rw [symmetric _ a b, fromChoice_lr s hV _ _ hb ha, symmetric H a b, hcross hb ha]
    · rw [fromChoice_rr s hV _ _ ha hb]
      rfl
  right_inv := by
    rintro ⟨L, R⟩
    apply Prod.ext <;> apply ext_rank <;> intro a b
    · exact fromChoice_ll s hV L R a.property b.property
    · exact fromChoice_rr s hV L R a.property b.property

theorem side_card {x : V} (s : SplitChoice x k) : Fintype.card (Side x s) = 2 ^ k := by
  calc
    Fintype.card (Side x s) = Fintype.card ↥(insert x s.val) :=
      Fintype.card_congr (show (Side x s) ≃ ↥(insert x s.val) from Equiv.refl _)
    _ = 2 ^ k := (Fintype.card_coe _).trans (side_finset_card s)

theorem other_side_card {x : V} (s : SplitChoice x k) (hV : Fintype.card V = 2 ^ (k + 1)) :
    Fintype.card ((Side x s)ᶜ : Set V) = 2 ^ k := by
  classical
  have hc := Fintype.card_congr (Equiv.Set.sumCompl (Side x s))
  rw [Fintype.card_sum, side_card s, hV, pow_succ] at hc
  omega

theorem card_odd : ∀ (k : ℕ) {V : Type} [Fintype V],
    Fintype.card V = 2 ^ k → Fintype.card (Hierarchy k V) ≡ 1 [MOD 2] := by
  intro k
  induction k with
  | zero =>
    intro V _ hV
    have hcard : Fintype.card V = 1 := by simpa using hV
    have hsub : Subsingleton V := (Fintype.card_le_one_iff_subsingleton).mp hcard.le
    let H : Hierarchy 0 V := {
      rank := fun _ _ => 0
      bound := fun _ _ => le_rfl
      zero_iff := fun _ _ => ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩
      symmetric := fun _ _ => rfl
      triangle := fun _ _ _ => le_rfl
      realizes := fun x i hi => ⟨x, (Nat.eq_zero_of_le_zero hi).symm⟩
      no_positive_equilateral := fun _ _ _ h => (h rfl).elim }
    have hsingle : Subsingleton (Hierarchy 0 V) :=
      ⟨fun L R => ext_rank fun a b => (Nat.eq_zero_of_le_zero (L.bound a b)).trans
        (Nat.eq_zero_of_le_zero (R.bound a b)).symm⟩
    let _ : Unique (Hierarchy 0 V) := uniqueOfSubsingleton H
    simpa using (Nat.ModEq.refl (n := 2) 1)
  | succ k ih =>
    intro V _ hV
    classical
    have hpos : 0 < Fintype.card V := by rw [hV]; exact Nat.two_pow_pos _
    let x : V := Classical.choice (Fintype.card_pos_iff.mp hpos)
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun H : Hierarchy (k + 1) V => H.topChoice x)),
      Fintype.card_sigma]
    have hsum : (∑ s : SplitChoice x k,
        Fintype.card {H : Hierarchy (k + 1) V // H.topChoice x = s}) ≡
        (∑ _ : SplitChoice x k, 1) [MOD 2] := by
      apply Nat.ModEq.sum
      intro s _
      rw [Fintype.card_congr (choiceFiberEquiv x s hV), Fintype.card_prod]
      exact (ih (side_card s)).mul (ih (other_side_card s hV))
    apply hsum.trans
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hV]
    exact choose_half_pow_mod_two k

end Hierarchy
section Normalize

open Finset

variable {V : Type} [Fintype V]

noncomputable def levels (d : V → V → ℕ) : Finset ℕ :=
  Finset.univ.image fun p : V × V => d p.1 p.2

theorem level_mem (d : V → V → ℕ) (x y : V) : d x y ∈ levels d :=
  Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩

noncomputable def rankIndex (d : V → V → ℕ) (x y : V) : Fin (levels d).card :=
  ((levels d).orderIsoOfFin rfl).symm ⟨d x y, level_mem d x y⟩

theorem rankIndex_le_iff (d : V → V → ℕ) (x y u v : V) :
    rankIndex d x y ≤ rankIndex d u v ↔ d x y ≤ d u v := by
  exact (OrderIso.le_iff_le _)

theorem rankIndex_onto (d : V → V → ℕ) (i : Fin (levels d).card) :
    ∃ x y, rankIndex d x y = i := by
  let e := (levels d).orderIsoOfFin rfl
  obtain ⟨⟨x, y⟩, _, h⟩ := Finset.mem_image.mp (e i).property
  refine ⟨x, y, e.injective ?_⟩
  simp only [rankIndex, e, OrderIso.apply_symm_apply]
  exact Subtype.ext h

theorem rankIndex_zero (d : V → V → ℕ) (x y : V) (h : d x y = 0) :
    (rankIndex d x y : ℕ) = 0 := by
  let i : Fin (levels d).card := ⟨0, (rankIndex d x y).isLt.pos⟩
  obtain ⟨u, v, huv⟩ := rankIndex_onto d i
  have hle : rankIndex d x y ≤ rankIndex d u v :=
    (rankIndex_le_iff _ _ _ _ _).2 (h.symm ▸ Nat.zero_le _)
  rw [huv] at hle
  exact Nat.eq_zero_of_le_zero hle

def RankRel (V : Type) := V → V → V → Prop

def IsRankLe (R : RankRel V) (x y u v : V) : Prop :=
  ∀ z, R x y z → R u v z

def IsRankLt (R : RankRel V) (x y u v : V) : Prop :=
  IsRankLe R x y u v ∧ ¬ IsRankLe R u v x y

def IsRankEq (R : RankRel V) (x y u v : V) : Prop :=
  IsRankLe R x y u v ∧ IsRankLe R u v x y

structure RankLaws (R : RankRel V) (a : V) : Prop where
  empty_loops : ∀ x z, ¬ R x x z
  symmetric : ∀ x y z, R x y z → R y x z
  full : ∀ x y, x ≠ y → R x y a
  nested : ∀ x y u v, IsRankLe R x y u v ∨ IsRankLe R u v x y
  triangle : ∀ x y z, IsRankLe R x z x y ∨ IsRankLe R x z y z
  covers : ∀ x y z, ∃ w, IsRankEq R x y z w
  no_equilateral : ∀ x y z, x ≠ y → IsRankEq R x y x z → ¬ IsRankEq R x y y z
  anchored : ∀ x y z, R x y z ↔ IsRankLt R a z x y

noncomputable def rankSet (R : RankRel V) (x y : V) : Finset V :=
  open Classical in Finset.univ.filter fun z => R x y z

noncomputable def rankSize (R : RankRel V) (x y : V) : ℕ :=
  (rankSet R x y).card

theorem rankSet_subset_iff (R : RankRel V) (x y u v : V) :
    rankSet R x y ⊆ rankSet R u v ↔ IsRankLe R x y u v := by
  simp only [Finset.subset_iff, rankSet, Finset.mem_filter, Finset.mem_univ, true_and, IsRankLe]

theorem rankSize_le_iff {R : RankRel V} {a : V} (h : RankLaws R a) (x y u v : V) :
    rankSize R x y ≤ rankSize R u v ↔ IsRankLe R x y u v := by
  rw [← rankSet_subset_iff]
  constructor
  · intro hs
    rcases h.nested x y u v with hxy | huv
    · exact (rankSet_subset_iff _ _ _ _ _).2 hxy
    · have hsub := (rankSet_subset_iff _ _ _ _ _).2 huv
      exact (Finset.eq_of_subset_of_card_le hsub hs).ge
  · exact Finset.card_le_card

theorem rankSize_self {R : RankRel V} {a : V} (h : RankLaws R a) (x : V) :
    rankSize R x x = 0 := by
  classical
  simp [rankSize, rankSet, h.empty_loops]

theorem rankSize_positive {R : RankRel V} {a x y : V} (h : RankLaws R a)
    (hxy : x ≠ y) : 0 < rankSize R x y := by
  classical
  exact Finset.card_pos.mpr ⟨a, by simp [rankSet, h.full x y hxy]⟩

noncomputable def hierarchyOfRanks {R : RankRel V} {a : V} (h : RankLaws R a) :
    Hierarchy ((levels (rankSize R)).card - 1) V where
  rank x y := (rankIndex (rankSize R) x y).val
  bound x y := by have := (rankIndex (rankSize R) x y).isLt; omega
  zero_iff x y := by
    constructor
    · intro h0
      by_contra hn
      have hsz := rankSize_positive h hn
      have hx := rankIndex_zero (rankSize R) x x (rankSize_self h x)
      have hle : rankIndex (rankSize R) x y ≤ rankIndex (rankSize R) x x := by
        change (rankIndex (rankSize R) x y).val ≤ (rankIndex (rankSize R) x x).val
        omega
      have hc := (rankIndex_le_iff _ _ _ _ _).1 hle
      rw [rankSize_self h x] at hc
      omega
    · rintro rfl
      exact rankIndex_zero (rankSize R) x x (rankSize_self h x)
  symmetric x y := by
    have hs := h.symmetric x y
    have ht := h.symmetric y x
    have hxy := (rankSize_le_iff h x y y x).2 hs
    have hyx := (rankSize_le_iff h y x x y).2 ht
    exact congrArg Fin.val (le_antisymm
      ((rankIndex_le_iff _ _ _ _ _).2 hxy) ((rankIndex_le_iff _ _ _ _ _).2 hyx))
  triangle x y z := by
    rcases h.triangle x y z with hl | hr
    · exact le_trans ((rankIndex_le_iff _ _ _ _ _).2 ((rankSize_le_iff h _ _ _ _).2 hl))
        (le_max_left _ _)
    · exact le_trans ((rankIndex_le_iff _ _ _ _ _).2 ((rankSize_le_iff h _ _ _ _).2 hr))
        (le_max_right _ _)
  realizes x i hi := by
    have hcard := (rankIndex (rankSize R) x x).isLt
    let j : Fin (levels (rankSize R)).card := ⟨i, by omega⟩
    obtain ⟨u, v, huv⟩ := rankIndex_onto (rankSize R) j
    obtain ⟨y, hxy, hyx⟩ := h.covers u v x
    have heq := le_antisymm
      ((rankIndex_le_iff _ _ _ _ _).2 ((rankSize_le_iff h _ _ _ _).2 hyx))
      ((rankIndex_le_iff _ _ _ _ _).2 ((rankSize_le_iff h _ _ _ _).2 hxy))
    exact ⟨y, congrArg Fin.val (heq.trans huv)⟩
  no_positive_equilateral x y z hp hxy hyz := by
    have hx : x ≠ y := by
      rintro rfl
      exact hp (rankIndex_zero _ x x (rankSize_self h x))
    have equal {u v a b : V} (hh : (rankIndex (rankSize R) u v).val =
        (rankIndex (rankSize R) a b).val) : IsRankEq R u v a b := by
      have eq := Fin.ext hh
      exact ⟨(rankSize_le_iff h _ _ _ _).1 ((rankIndex_le_iff _ _ _ _ _).1 eq.le),
        (rankSize_le_iff h _ _ _ _).1 ((rankIndex_le_iff _ _ _ _ _).1 eq.ge)⟩
    exact h.no_equilateral x y z hx (equal hxy) (equal hyz)

def encodeHierarchy {k : ℕ} (H : Hierarchy k V) (a : V) : RankRel V :=
  fun x y z => H.rank a z < H.rank x y

omit [Fintype V] in
theorem rankLe_encoded {k : ℕ} (H : Hierarchy k V) (a x y u v : V) :
    IsRankLe (encodeHierarchy H a) x y u v ↔ H.rank x y ≤ H.rank u v := by
  constructor
  · intro h
    by_contra! hh
    obtain ⟨z, hz⟩ := H.realizes a (H.rank u v) (H.bound _ _)
    have h' := h z (show H.rank a z < H.rank x y by omega)
    change H.rank a z < H.rank u v at h'
    omega
  · intro h z hz
    exact lt_of_lt_of_le hz h

omit [Fintype V] in
theorem encode_has_laws {k : ℕ} (H : Hierarchy k V) (a : V) :
    RankLaws (encodeHierarchy H a) a where
  empty_loops x z := by simp [encodeHierarchy, H.rank_self]
  symmetric x y z := by simp only [encodeHierarchy, H.symmetric x y, imp_self]
  full x y h := by
    simpa [encodeHierarchy, H.rank_self] using Nat.pos_of_ne_zero (mt (H.zero_iff x y).1 h)
  nested x y u v := by simpa only [rankLe_encoded] using le_total (H.rank x y) (H.rank u v)
  triangle x y z := by simpa only [rankLe_encoded, le_max_iff] using H.triangle x y z
  covers x y z := by simpa only [IsRankEq, rankLe_encoded, le_antisymm_iff] using
    (H.realizes z (H.rank x y) (H.bound _ _)).imp fun _ hh => hh.symm
  no_equilateral x y z hn := by
    simp only [IsRankEq, rankLe_encoded, ← le_antisymm_iff]
    exact H.no_positive_equilateral x y z (mt (H.zero_iff x y).1 hn)
  anchored x y z := by
    simp only [encodeHierarchy, IsRankLt, rankLe_encoded, not_le]
    exact ⟨fun h => ⟨h.le, h⟩, And.right⟩

theorem reencode_ranks {R : RankRel V} {a : V} (h : RankLaws R a) :
    encodeHierarchy (hierarchyOfRanks h) a = R := by
  funext x y z
  apply propext
  rw [h.anchored]
  change (rankIndex (rankSize R) a z).val < (rankIndex (rankSize R) x y).val ↔
    IsRankLt R a z x y
  rw [show (rankIndex (rankSize R) a z).val < (rankIndex (rankSize R) x y).val ↔
      ¬ rankIndex (rankSize R) x y ≤ rankIndex (rankSize R) a z from (not_le).symm]
  rw [rankIndex_le_iff, rankSize_le_iff h, IsRankLt]
  exact ⟨fun hz => ⟨(h.nested a z x y).resolve_right hz, hz⟩, And.right⟩

end Normalize
end SpeckerHierarchy

namespace SpeckerFormula

def liftedRel {V : Type} [DecidableEq V] (R : V → V → V → Prop) :
    Option V → Option V → Option V → Prop
  | none, none, _ => False
  | some x, some y, none => x ≠ y
  | some _, none, none | none, some _, none => True
  | some x, some y, some z => x ≠ y ∧ R x y z
  | some x, none, some z | none, some x, some z => R x x z

theorem liftedRel_injective {V : Type} [DecidableEq V] :
    Function.Injective (liftedRel (V := V)) := by
  intro R S h
  funext x y z
  by_cases hxy : x = y
  · subst y
    exact congrFun (congrFun (congrFun h none) (some x)) (some z)
  · simpa [liftedRel, hxy] using congrFun (congrFun (congrFun h (some x)) (some y)) (some z)

inductive Formula
  | eq : Option ℕ → Option ℕ → Formula
  | rel : Option ℕ → Option ℕ → Option ℕ → Formula
  | neg : Formula → Formula
  | and : Formula → Formula → Formula
  | ex : ℕ → Formula → Formula

def termValue {V : Type} (s : ℕ → Option V) (t : Option ℕ) : Option V :=
  t.bind s

def Eval {V : Type} (R : Option V → Option V → Option V → Prop)
    (s : ℕ → Option V) : Formula → Prop
  | .eq x y => termValue s x = termValue s y
  | .rel x y z => R (termValue s x) (termValue s y) (termValue s z)
  | .neg φ => ¬ Eval R s φ
  | .and φ ψ => Eval R s φ ∧ Eval R s ψ
  | .ex x φ => ∃ b : Option V, Eval R (Function.update s x b) φ

def mask (A : Finset ℕ) (t : Option ℕ) : Option ℕ :=
  t.bind fun x => if x ∈ A then none else some x

def maskedEnv {V : Type} (A : Finset ℕ) (s : ℕ → V) (x : ℕ) : Option V :=
  if x ∈ A then none else some (s x)

theorem term_value_masked {V : Type} (A : Finset ℕ) (s : ℕ → V) (t : Option ℕ) :
    termValue (maskedEnv A s) t = (mask A t).map s := by
  cases t with
  | none => rfl
  | some t => by_cases h : t ∈ A <;> simp [termValue, maskedEnv, mask, h]

private def msoTrue : MSO := .eq 0 0
private def msoFalse : MSO := .neg msoTrue

private def compileEq : Option ℕ → Option ℕ → MSO
  | none, none => msoTrue
  | some x, some y => .eq x y
  | none, some _ | some _, none => msoFalse

private def compileRel : Option ℕ → Option ℕ → Option ℕ → MSO
  | none, none, _ => msoFalse
  | some x, some y, none => .neg (.eq x y)
  | some _, none, none | none, some _, none => msoTrue
  | some x, some y, some z => .conj (.neg (.eq x y)) (.rel x y z)
  | some x, none, some z | none, some x, some z => .rel x x z

private def msoOr (φ ψ : MSO) : MSO := .neg (.conj (.neg φ) (.neg ψ))

def compile (A : Finset ℕ) : Formula → MSO
  | .eq x y => compileEq (mask A x) (mask A y)
  | .rel x y z => compileRel (mask A x) (mask A y) (mask A z)
  | .neg φ => .neg (compile A φ)
  | .and φ ψ => .conj (compile A φ) (compile A ψ)
  | .ex x φ => msoOr (compile (insert x A) φ) (.exFO x (compile (A.erase x) φ))

private theorem sat_compileEq {n : ℕ} (R : Fin n → Fin n → Fin n → Prop)
    (s : ℕ → Fin n) (S : ℕ → Set (Fin n)) (x y : Option ℕ) :
    Sat R (compileEq x y) s S ↔ x.map s = y.map s := by
  cases x <;> cases y <;> simp [compileEq, msoTrue, msoFalse, Sat]

private theorem sat_compileRel {n : ℕ} (R : Fin n → Fin n → Fin n → Prop)
    (s : ℕ → Fin n) (S : ℕ → Set (Fin n)) (x y z : Option ℕ) :
    Sat R (compileRel x y z) s S ↔ liftedRel R (x.map s) (y.map s) (z.map s) := by
  cases x <;> cases y <;> cases z <;> simp [compileRel, liftedRel, msoTrue, msoFalse, Sat]

private theorem masked_insert {V : Type} (A : Finset ℕ) (s : ℕ → V) (x : ℕ) :
    maskedEnv (insert x A) s = Function.update (maskedEnv A s) x none := by
  ext y
  by_cases h : y = x
  · simp [h, maskedEnv]
  · simp [h, maskedEnv]

private theorem masked_erase {V : Type} (A : Finset ℕ) (s : ℕ → V) (x : ℕ) (b : V) :
    maskedEnv (A.erase x) (Function.update s x b) =
      Function.update (maskedEnv A s) x (some b) := by
  ext y
  by_cases h : y = x
  · simp [h, maskedEnv]
  · simp [h, maskedEnv]

theorem sat_compile {n : ℕ} (R : Fin n → Fin n → Fin n → Prop)
    (S : ℕ → Set (Fin n)) (φ : Formula) (A : Finset ℕ) (s : ℕ → Fin n) :
    Sat R (compile A φ) s S ↔ Eval (liftedRel R) (maskedEnv A s) φ := by
  classical
  induction φ generalizing A s with
  | eq x y => simp [compile, Eval, sat_compileEq, term_value_masked]
  | rel x y z => simp [compile, Eval, sat_compileRel, term_value_masked]
  | neg φ ih => simp [compile, Eval, Sat, ih]
  | and φ ψ ihφ ihψ => simp [compile, Eval, Sat, ihφ, ihψ]
  | ex x φ ih =>
    simp only [compile, msoOr, Sat, not_and_or, not_not, Eval, ih, masked_insert, masked_erase]
    constructor
    · rintro (h | ⟨b, hb⟩)
      · exact ⟨none, h⟩
      · exact ⟨some b, hb⟩
    · rintro ⟨b, hb⟩
      cases b with
      | none => exact Or.inl hb
      | some b => exact Or.inr ⟨b, hb⟩

end SpeckerFormula

namespace SpeckerHierarchy

theorem encodeHierarchy_injective {k : ℕ} {V : Type} (a : V) :
    Function.Injective (fun H : Hierarchy k V => encodeHierarchy H a) := by
  intro H J h
  change encodeHierarchy H a = encodeHierarchy J a at h
  have order_same (x y u v : V) : H.rank x y ≤ H.rank u v ↔ J.rank x y ≤ J.rank u v := by
    rw [← rankLe_encoded H a, ← rankLe_encoded J a, h]
  let rep (i : Fin (k + 1)) : V := Classical.choose (H.realizes a i.val (Nat.le_of_lt_succ i.isLt))
  have hrep (i : Fin (k + 1)) : H.rank a (rep i) = i.val :=
    Classical.choose_spec (H.realizes a i.val (Nat.le_of_lt_succ i.isLt))
  let labels (i : Fin (k + 1)) : Fin (k + 1) := ⟨J.rank a (rep i), Nat.lt_succ_of_le (J.bound _ _)⟩
  have hmono : StrictMono labels := by
    intro i j hij
    change J.rank a (rep i) < J.rank a (rep j)
    rw [← not_le, ← order_same, hrep, hrep]
    exact not_le_of_gt hij
  have hl : labels = id := hmono.eq_id
  apply Hierarchy.ext_rank
  intro x y
  let i : Fin (k + 1) := ⟨H.rank x y, Nat.lt_succ_of_le (H.bound x y)⟩
  have hJ : J.rank a (rep i) = J.rank x y := by
    apply le_antisymm
    · exact (order_same _ _ _ _).mp (by rw [hrep])
    · exact (order_same _ _ _ _).mp (by rw [hrep])
  have hin : J.rank a (rep i) = H.rank x y := congrArg Fin.val (congrFun hl i)
  exact hin.symm.trans hJ

end SpeckerHierarchy

namespace SpeckerFormula

open SpeckerHierarchy

def forallF (i : ℕ) (φ : Formula) : Formula := .neg (.ex i (.neg φ))
def impF (φ ψ : Formula) : Formula := .neg (.and φ (.neg ψ))
def orF (φ ψ : Formula) : Formula := .neg (.and (.neg φ) (.neg ψ))
def iffF (φ ψ : Formula) : Formula := .and (impF φ ψ) (impF ψ φ)

theorem eval_forallF {V : Type} (R : RankRel (Option V)) (s : ℕ → Option V) (i : ℕ)
    (φ : Formula) : Eval R s (forallF i φ) ↔ ∀ z, Eval R (Function.update s i z) φ := by
  classical
  simp [forallF, Eval]

theorem eval_impF {V : Type} (R : RankRel (Option V)) (s : ℕ → Option V) (φ ψ : Formula) :
    Eval R s (impF φ ψ) ↔ (Eval R s φ → Eval R s ψ) := by
  classical
  simp only [impF, Eval, not_and, not_not]

theorem eval_orF {V : Type} (R : RankRel (Option V)) (s : ℕ → Option V) (φ ψ : Formula) :
    Eval R s (orF φ ψ) ↔ (Eval R s φ ∨ Eval R s ψ) := by
  classical
  simp only [orF, Eval, not_and_or, not_not]

theorem eval_iffF {V : Type} (R : RankRel (Option V)) (s : ℕ → Option V) (φ ψ : Formula) :
    Eval R s (iffF φ ψ) ↔ (Eval R s φ ↔ Eval R s ψ) := by
  change (Eval R s (impF φ ψ) ∧ Eval R s (impF ψ φ)) ↔ _
  rw [eval_impF, eval_impF]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

def cmpF (x y u v : Option ℕ) : Formula :=
  forallF 4 (impF (.rel x y (some 4)) (.rel u v (some 4)))

def sameF (x y u v : Option ℕ) : Formula :=
  .and (cmpF x y u v) (cmpF u v x y)

def ltF (x y u v : Option ℕ) : Formula :=
  .and (cmpF x y u v) (.neg (cmpF u v x y))

def allF (l : List ℕ) (φ : Formula) : Formula := l.foldr forallF φ

def modelFormula : Formula :=
  let x := some 0
  let y := some 1
  let z := some 2
  let w := some 3
  .and (allF [0, 2] (.neg (.rel x x z))) <|
  .and (allF [0, 1, 2] (impF (.rel x y z) (.rel y x z))) <|
  .and (allF [0, 1] (impF (.neg (.eq x y)) (.rel x y none))) <|
  .and (allF [0, 1, 2, 3] (orF (cmpF x y z w) (cmpF z w x y))) <|
  .and (allF [0, 1, 2] (orF (cmpF x z x y) (cmpF x z y z))) <|
  .and (allF [0, 1, 2] (.ex 3 (sameF x y z w))) <|
  .and (allF [0, 1, 2] (impF (.neg (.eq x y))
    (impF (sameF x y x z) (.neg (sameF x y y z))))) <|
    allF [0, 1, 2] (iffF (.rel x y z) (ltF none z x y))

theorem eval_modelFormula {V : Type} (R : RankRel (Option V)) (s : ℕ → Option V) :
    Eval R s modelFormula ↔ RankLaws R none := by
  classical
  simp (discharger := omega) only [modelFormula, allF, List.foldr_cons,
    List.foldr_nil, eval_forallF, eval_impF, eval_orF, eval_iffF, sameF, ltF, cmpF,
    Eval, termValue, Option.bind_none, Option.bind_some, Function.update_apply, if_neg]
  change
    ((∀ x z, ¬ R x x z) ∧
      (∀ x y z, R x y z → R y x z) ∧
      (∀ x y, x ≠ y → R x y none) ∧
      (∀ x y u v, IsRankLe R x y u v ∨ IsRankLe R u v x y) ∧
      (∀ x y z, IsRankLe R x z x y ∨ IsRankLe R x z y z) ∧
      (∀ x y z, ∃ w, IsRankEq R x y z w) ∧
      (∀ x y z, x ≠ y → IsRankEq R x y x z → ¬ IsRankEq R x y y z) ∧
      (∀ x y z, R x y z ↔ IsRankLt R none z x y)) ↔ RankLaws R none
  constructor
  · rintro ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    exact ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  · intro h
    exact ⟨h.empty_loops, h.symmetric, h.full, h.nested, h.triangle,
      h.covers, h.no_equilateral, h.anchored⟩

def sentence : MSO := compile ∅ modelFormula

theorem sentence_iff {n : ℕ} (R : Fin n → Fin n → Fin n → Prop)
    (s : ℕ → Fin n) (S : ℕ → Set (Fin n)) :
    Sat R sentence s S ↔ RankLaws (liftedRel R) none :=
  (sat_compile R S modelFormula ∅ s).trans (eval_modelFormula _ _)

theorem isSentence : IsSentence sentence := by
  intro n R v w V W
  rw [sentence_iff, sentence_iff]

end SpeckerFormula

namespace SpeckerFormula

open SpeckerHierarchy

def lowerCode {V : Type} [DecidableEq V] {k : ℕ} (H : Hierarchy k (Option V)) :
    V → V → V → Prop :=
  fun x y z => if x = y then encodeHierarchy H none none (some x) (some z)
    else encodeHierarchy H none (some x) (some y) (some z)

theorem lift_lowerCode {V : Type} [DecidableEq V] {k : ℕ} (H : Hierarchy k (Option V)) :
    liftedRel (lowerCode H) = encodeHierarchy H none := by
  funext x y z
  apply propext
  have hp {a b : Option V} (h : a ≠ b) : 0 < H.rank a b :=
    Nat.pos_of_ne_zero (mt (H.zero_iff a b).1 h)
  cases x <;> cases y <;> cases z
  · simp [liftedRel, encodeHierarchy, H.rank_self]
  · simp [liftedRel, encodeHierarchy, H.rank_self]
  · simp [liftedRel, encodeHierarchy, H.rank_self, hp]
  · simp [liftedRel, lowerCode]
  · simp [liftedRel, encodeHierarchy, H.rank_self, hp]
  · simp [liftedRel, lowerCode, encodeHierarchy, H.symmetric]
  · rename_i x y
    by_cases h : x = y
    · subst y
      simp [liftedRel, encodeHierarchy, H.rank_self]
    · simp [liftedRel, encodeHierarchy, H.rank_self, h]
      exact hp (fun he => h (Option.some.inj he))
  · rename_i x y z
    by_cases h : x = y
    · subst y
      simp [liftedRel, encodeHierarchy, H.rank_self]
    · simp [liftedRel, lowerCode, h]

def heightTransport {V : Type} {i j : ℕ} (h : i = j) (H : Hierarchy i V) : Hierarchy j V :=
  h ▸ H

theorem heightTransport_rank {V : Type} {i j : ℕ} (h : i = j) (H : Hierarchy i V) (x y : V) :
    (heightTransport h H).rank x y = H.rank x y := by cases h; rfl

theorem powers_inj {i j : ℕ} (h : (2 : ℕ) ^ i = 2 ^ j) : i = j := by
  rcases lt_trichotomy i j with hlt | he | hgt
  · have hp := (pow_lt_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).2 hlt
    omega
  · exact he
  · have hp := (pow_lt_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).2 hgt
    omega

noncomputable def hierarchyAtHeight {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}
    (hcard : Fintype.card (Option V) = 2 ^ k)
    (R : V → V → V → Prop) (hR : RankLaws (liftedRel R) none) : Hierarchy k (Option V) :=
  heightTransport (powers_inj ((Hierarchy.card_of (hierarchyOfRanks hR)).symm.trans hcard))
    (hierarchyOfRanks hR)

theorem hierarchyAtHeight_encodes {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}
    (hcard : Fintype.card (Option V) = 2 ^ k)
    (R : V → V → V → Prop) (hR : RankLaws (liftedRel R) none) :
    encodeHierarchy (hierarchyAtHeight hcard R hR) none = liftedRel R := by
  rw [← reencode_ranks hR]
  funext x y z
  simp only [hierarchyAtHeight, encodeHierarchy, heightTransport_rank]

noncomputable def modelEquivHierarchy {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}
    (hcard : Fintype.card (Option V) = 2 ^ k) :
    {R : V → V → V → Prop // RankLaws (liftedRel R) none} ≃ Hierarchy k (Option V) where
  toFun R := hierarchyAtHeight hcard R.val R.property
  invFun H := ⟨lowerCode H, by rw [lift_lowerCode]; exact encode_has_laws H none⟩
  left_inv R := by
    apply Subtype.ext
    apply liftedRel_injective
    change liftedRel (lowerCode (hierarchyAtHeight hcard R.val R.property)) = liftedRel R.val
    rw [lift_lowerCode, hierarchyAtHeight_encodes]
  right_inv H := by
    apply encodeHierarchy_injective none
    change encodeHierarchy (hierarchyAtHeight hcard (lowerCode H) _) none =
      encodeHierarchy H none
    rw [hierarchyAtHeight_encodes, lift_lowerCode]

theorem models_on_power (n : ℕ) (h : ∃ k : ℕ, n + 2 = 2 ^ k) :
    f sentence n % 2 = 1 := by
  obtain ⟨k, hk⟩ := h
  have hcard : Fintype.card (Option (Fin (n + 1))) = 2 ^ k := by simpa using hk
  let e := (Equiv.subtypeEquivRight
    (fun R => sentence_iff (n := n + 1) R (fun _ => 0) (fun _ => ∅))).trans
      (modelEquivHierarchy hcard)
  have hc : f sentence n = Fintype.card (Hierarchy k (Option (Fin (n + 1)))) := by
    unfold f
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr e).trans Nat.card_eq_fintype_card
  rw [hc]
  exact Hierarchy.card_odd k hcard

theorem models_off_powers (n : ℕ) (h : ¬ ∃ k : ℕ, n + 2 = 2 ^ k) :
    f sentence n % 2 = 0 := by
  have hm : {R : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Prop |
      Sat R sentence (fun _ => 0) (fun _ => ∅)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro R hR
    have hl := (sentence_iff R _ _).1 hR
    have hc := Hierarchy.card_of (hierarchyOfRanks hl)
    apply h
    exact ⟨_, by simpa using hc⟩
  simp [f, hm]

end SpeckerFormula

theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_blatter_specker_theorem_for_ternary_relations.main) := by
  intro h
  exact SpeckerHierarchy.not_periodic_pow_support
    (f SpeckerFormula.sentence) SpeckerFormula.models_on_power SpeckerFormula.models_off_powers
    (h SpeckerFormula.sentence SpeckerFormula.isSentence 2 (by decide))
