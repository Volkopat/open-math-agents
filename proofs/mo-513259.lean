import OMAStatements.S_mo_513259

/-! Proof of the two graph congruences in MathOverflow question 513259.
Credit: @cjchaffin with Codex.

Over the field of three elements a mixed moment proves invariance of the
permanent under inversion. Modulo eight, reindex Ryser's Boolean sum by
the graph adjacency matrix modulo two. A product expanded about the
all-ones vector involves only Boolean faces of dimension at most two.
The surviving quadratic corrections cancel by the formula for the
second principal minors of a product of symmetric hollow matrices. -/


section
/-! The permanent of an invertible matrix over the field of three elements
equals the permanent of its inverse. The mixed moment of the coordinate
products of x and Ax is invariant under the change of variables y = Ax. -/

open Matrix Finset
namespace Mo513259
abbrev K := ZMod 3

private def coord {n : ℕ} (x : Fin n → K) : K := ∏ i, x i

private theorem moments {n : ℕ} (f : Fin n → Fin n) :
    (∑ x : Fin n → K, coord x * ∏ i, x (f i)) =
      if Function.Bijective f then (-1 : K)^n else 0 := by
  classical
  by_cases hf : Function.Bijective f
  · rw [if_pos hf]
    let e := Equiv.ofBijective f hf
    have h (x : Fin n → K) : (∏ i, x (f i)) = ∏ i, x i := e.prod_comp x
    simp_rw [h, coord, ← prod_mul_distrib]
    rw [← Fintype.prod_sum (fun _ : Fin n => fun t : K => t*t)]
    have h2 : (∑ t : K, t*t) = -1 := by decide
    simp [h2]
  · rw [if_neg hf]
    have hns : ¬ Function.Surjective f := fun h => hf (Finite.surjective_iff_bijective.mp h)
    obtain ⟨j, hj⟩ := not_forall.mp hns
    have hmiss (i) : f i ≠ j := fun h => hj ⟨i, h⟩
    let m (j : Fin n) := (univ.filter (fun i => f i = j)).card
    have h (x : Fin n → K) : (∏ i, x (f i)) = ∏ i, x i ^ m i := by
      simpa [m] using (Finset.prod_fiberwise' univ f x).symm
    simp_rw [h, coord, ← prod_mul_distrib]
    rw [← Fintype.prod_sum (fun j : Fin n => fun t : K => t * t ^ m j)]
    apply prod_eq_zero (mem_univ j)
    have hj0 : m j = 0 := by simp [m, hmiss]
    simp only [hj0, pow_zero, mul_one]
    decide

private def moment {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : K :=
  ∑ x : Fin n → K, coord x * coord (A *ᵥ x)

private theorem moment_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    moment A = A.permanent * (-1)^n := by
  classical
  have exp (x : Fin n → K) :
      coord (A *ᵥ x) = ∑ f : Fin n → Fin n, (∏ i, A i (f i)) * (∏ i, x (f i)) := by
    unfold coord
    simp only [mulVec, dotProduct, Fintype.prod_sum, prod_mul_distrib]
  unfold moment
  simp_rw [exp, mul_sum]
  rw [sum_comm]
  have collapse (f : Fin n → Fin n) :
      (∑ x : Fin n → K, coord x * ((∏ i, A i (f i)) * ∏ i, x (f i))) =
          (∏ i, A i (f i)) * (if Function.Bijective f then (-1 : K)^n else 0) := by
    rw [← moments f, mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  simp_rw [collapse]
  have hf (f : Fin n → Fin n) : (∏ i, A i (f i)) * (if Function.Bijective f then (-1 : K)^n else 0) =
      if Function.Bijective f then (∏ i, A i (f i)) * (-1 : K)^n else 0 := by split <;> simp
  simp_rw [hf]
  rw [← sum_filter, ← sum_mul, ← A.permanent_transpose, permanent]
  congr 1
  refine sum_bij (fun f hf => Equiv.ofBijective f (mem_filter.mp hf).2) (by simp) ?_ ?_ ?_
  · intro f hf g hg he
    exact congrArg DFunLike.coe he
  · intro e _
    exact ⟨e, mem_filter.mpr ⟨mem_univ _, e.bijective⟩, Equiv.ext (fun _ => rfl)⟩
  · intro f hf
    rfl

theorem permanent_inv_mod_three {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (h : IsUnit A.det) :
    A⁻¹.permanent = A.permanent := by
  classical
  let e : (Fin n → K) ≃ (Fin n → K) := {
    toFun := A.mulVec, invFun := A⁻¹.mulVec
    left_inv := fun x => by simp [mulVec_mulVec, nonsing_inv_mul A h]
    right_inv := fun x => by simp [mulVec_mulVec, mul_nonsing_inv A h] }
  have same : moment A = moment A⁻¹ := by
    apply Fintype.sum_equiv e
    intro x
    change coord x * coord (A *ᵥ x) = coord (A *ᵥ x) * coord (A⁻¹ *ᵥ (A *ᵥ x))
    simp [mulVec_mulVec, nonsing_inv_mul A h, mul_comm]
  rw [moment_eq, moment_eq] at same
  exact mul_right_cancel₀ (by simp) same.symm

end Mo513259
end

section
namespace OeisRyser
open Finset

/-- Ryser's inclusion-exclusion formula for the permanent. -/
theorem permanent_eq {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R) :
    A.permanent = ∑ s ∈ (univ : Finset (Fin n)).powerset,
      (-1 : R)^(n-s.card) * ∏ i, ∑ j ∈ s, A i j := by
  classical
  let S (j : Fin n) : Finset (Fin n → Fin n) := univ.filter fun f => ∀ i, f i ≠ j
  let w (f : Fin n → Fin n) := ∏ i, A i (f i)
  have good (f : Fin n → Fin n) :
      f ∈ (univ.inf (fun j => (S j)ᶜ)) ↔ Function.Surjective f := by
    simp [S, Finset.mem_inf, Function.Surjective]
  have avoid (t : Finset (Fin n)) : t.inf S = Fintype.piFinset (fun _ : Fin n => tᶜ) := by
    ext f
    simp only [Finset.mem_inf, S, mem_filter, mem_univ, true_and, Fintype.mem_piFinset, mem_compl]
    constructor
    · intro h i hi
      exact h (f i) hi i rfl
    · intro h j hj i he
      exact h i (he ▸ hj)
  calc
    _ = ∑ f ∈ (univ.inf (fun j => (S j)ᶜ)), w f := by
      rw [← Matrix.permanent_transpose A, Matrix.permanent]
      apply sum_bij (fun (σ : Equiv.Perm (Fin n)) _ => (σ : Fin n → Fin n))
      · intro σ _; exact (good _).mpr σ.surjective
      · intro σ _ τ _ h; exact Equiv.ext (congrFun h)
      · intro f hf
        have hb := (Finite.surjective_iff_bijective).mp ((good _).mp hf)
        exact ⟨Equiv.ofBijective f hb, mem_univ _, rfl⟩
      · intros; rfl
    _ = ∑ t ∈ (univ : Finset (Fin n)).powerset,
        (-1 : ℤ)^t.card • ∑ f ∈ t.inf S, w f :=
      inclusion_exclusion_sum_inf_compl _ _ _
    _ = _ := by
      apply sum_bij (fun t _ => tᶜ)
      · intros; simp
      · intro t _ s _ h; simpa using congrArg (fun v : Finset (Fin n) => vᶜ) h
      · intro s _; exact ⟨sᶜ, by simp, compl_compl s⟩
      · intro t ht
        have hc : t.card ≤ n := by simpa using card_le_univ t
        rw [avoid, show (∑ f ∈ Fintype.piFinset (fun _ : Fin n => tᶜ), w f) =
          ∏ i, ∑ j ∈ tᶜ, A i j from sum_prod_piFinset _ _]
        simp [Finset.card_compl, Nat.sub_sub_self hc, zsmul_eq_mul]



/-- For even dimension the sign is the product of one sign for each selected column. -/
theorem permanent_eq_bits {n : ℕ} {R : Type*} [CommRing R] (hn : Even n)
    (A : Matrix (Fin n) (Fin n) R) :
    A.permanent = ∑ x : Fin n → ZMod 2,
      (∏ i, if x i = 0 then (1 : R) else -1) *
        ∏ i, ∑ j, A i j * (if x j = 0 then 0 else 1) := by
  classical
  let χ (s : Finset (Fin n)) (i : Fin n) : ZMod 2 := if i ∈ s then 1 else 0
  rw [permanent_eq]
  apply sum_bij (fun s _ => χ s)
  · intros; simp
  · intro t _ s _ h
    ext i
    have he := congrFun h i
    by_cases ht : i ∈ t <;> by_cases hs : i ∈ s <;> simp_all [χ]
  · intro x _
    refine ⟨univ.filter (fun i => x i ≠ 0), by simp, ?_⟩
    funext i
    have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases h (x i) with h | h <;> simp [χ, h]
  · intro s hs
    have hc : s.card ≤ n := by simpa using card_le_univ s
    have hsign : (-1 : R)^(n-s.card) = (-1 : R)^s.card := by
      calc
        _ = (-1 : R)^(n-s.card) * ((-1 : R)^s.card * (-1 : R)^s.card) := by
          rw [← mul_pow]; simp
        _ = (-1 : R)^n * (-1 : R)^s.card := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hc]
        _ = _ := by rw [hn.neg_one_pow, one_mul]
    rw [hsign]
    congr 1
    · simp [χ]
    · apply prod_congr rfl
      intro i hi
      simp [χ, mul_ite]
end OeisRyser
end

section
namespace OeisRyser

open Finset

private def linearPart {n : ℕ} (y c : Fin n → ZMod 8) (s : Finset (Fin n)) : ZMod 8 :=
  ∑ i ∈ s, c i * ∏ j ∈ s.erase i, y j

private def quadraticPart {n : ℕ} (y c : Fin n → ZMod 8) (s : Finset (Fin n)) : ZMod 8 :=
  ∑ i ∈ s, ∑ j ∈ s with i < j, c i * c j * ∏ k ∈ (s.erase i).erase j, y k

private theorem truncated_on {n : ℕ} (y c : Fin n → ZMod 8) (s : Finset (Fin n)) :
    (∏ i ∈ s, (y i - 2 * c i)) =
      (∏ i ∈ s, y i) - 2 * linearPart y c s + 4 * quadraticPart y c s := by
  refine Finset.induction_on_min s (by simp [linearPart, quadraticPart]) ?_
  intro a t ha ih
  have hnot : a ∉ t := fun h => (ha a h).false
  have hL : linearPart y c (insert a t) =
      c a * (∏ i ∈ t, y i) + y a * linearPart y c t := by
    simp only [linearPart, sum_insert hnot, erase_insert hnot, mul_sum]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [erase_insert_of_ne (ha i hi).ne, prod_insert (fun h => hnot (mem_of_mem_erase h))]
    ring
  have hQ : quadraticPart y c (insert a t) =
      c a * linearPart y c t + y a * quadraticPart y c t := by
    simp only [quadraticPart, sum_insert hnot, erase_insert hnot, linearPart, mul_sum]
    congr 1
    · rw [filter_insert, if_neg (lt_irrefl a), filter_true_of_mem ha]
      refine sum_congr rfl fun i _ => ?_
      ring
    · refine sum_congr rfl fun i hi => ?_
      rw [filter_insert, if_neg (ha i hi).not_gt]
      refine sum_congr rfl fun j hj => ?_
      have hja := ha j (mem_filter.mp hj).1
      rw [erase_insert_of_ne (ha i hi).ne, erase_insert_of_ne hja.ne,
        prod_insert (fun h => hnot (mem_of_mem_erase (mem_of_mem_erase h)))]
      ring
  rw [prod_insert hnot, prod_insert hnot, ih, hL, hQ]
  have h8 : (8 : ZMod 8) = 0 := by decide
  linear_combination -(c a * quadraticPart y c t) * h8

/-- Expanding a product of even perturbations modulo eight retains only
the constant, linear and quadratic terms. -/
theorem truncated_product {n : ℕ} (y c : Fin n → ZMod 8) :
    (∏ i, (y i - 2 * c i)) = (∏ i, y i) -
      2 * (∑ i, c i * ∏ j ∈ univ.erase i, y j) +
      4 * (∑ i, ∑ j ∈ Ioi i, c i * c j * ∏ k ∈ (univ.erase i).erase j, y k) := by
  have intervals (i : Fin n) : (univ.filter (fun j => i < j)) = Ioi i := by ext; simp
  simpa only [linearPart, quadraticPart, intervals] using truncated_on y c univ

end OeisRyser
end

section
namespace Mo513259BooleanFaces

open Finset

abbrev Cube (n : ℕ) := Fin n → ZMod 2
abbrev ones {n : ℕ} : Cube n := fun _ => 1

private theorem update_ones {n : ℕ} (i : Fin n) : Function.update ones i 1 = ones :=
  Function.update_eq_self i ones

def weighted {n : ℕ} (f : Cube n → ZMod 8) (T : Finset (Fin n)) : ZMod 8 :=
  ∑ y : Cube n, f y * ∏ k ∈ T, (if y k = 0 then 0 else 1)

theorem weighted_eq_filter {n : ℕ} (f : Cube n → ZMod 8) (T : Finset (Fin n)) :
    weighted f T = ∑ y ∈ univ.filter (fun y : Cube n => ∀ k ∈ T, y k = 1), f y := by
  classical
  have hz (a : ZMod 2) : (if a = 0 then (0 : ZMod 8) else 1) =
      (if a = 1 then 1 else 0) := by fin_cases a <;> decide
  simp only [weighted, hz, Finset.prod_boole, Finset.sum_filter, mul_ite, mul_one, mul_zero]

theorem weighted_univ {n : ℕ} (f : Cube n → ZMod 8) :
    weighted f univ = f ones := by
  rw [weighted_eq_filter]
  have hu : univ.filter (fun y : Cube n => ∀ k ∈ (univ : Finset (Fin n)), y k = 1) =
      {ones} := by
    ext y
    simp [funext_iff, ones]
  rw [hu, sum_singleton]

theorem weighted_erase {n : ℕ} (f : Cube n → ZMod 8) (i : Fin n) :
    weighted f (univ.erase i) = f (Function.update ones i 0) + f ones := by
  classical
  rw [weighted_eq_filter]
  let v (a : ZMod 2) := Function.update (ones (n := n)) i a
  trans ∑ a : ZMod 2, f (v a)
  · symm
    apply sum_bij (fun (a : ZMod 2) _ => v a)
    · intro a _
      simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
      intro k hki
      simp [v, Function.update_of_ne hki]
    · intro a _ b _ he
      simpa [v] using congrFun he i
    · intro y hy
      have h := (mem_filter.mp hy).2
      refine ⟨y i, mem_univ _, funext fun k => ?_⟩
      by_cases hk : k = i
      · subst k; simp [v]
      · simpa [v, Function.update_of_ne hk] using (h k (by simp [hk])).symm
    · intros; rfl
  · change (∑ a : Fin 2, f (v a)) = _
    rw [Fin.sum_univ_two]
    change f (v 0) + f (v 1) = _
    simp only [v, update_ones]

theorem weighted_erase_erase {n : ℕ} (f : Cube n → ZMod 8) (i j : Fin n) (hij : i ≠ j) :
    weighted f ((univ.erase i).erase j) =
      f (Function.update (Function.update ones i 0) j 0) + f (Function.update ones i 0) +
        (f (Function.update ones j 0) + f ones) := by
  classical
  rw [weighted_eq_filter]
  let v (a b : ZMod 2) := Function.update (Function.update (ones (n := n)) i a) j b
  trans ∑ ab : ZMod 2 × ZMod 2, f (v ab.1 ab.2)
  · symm
    apply sum_bij (fun (ab : ZMod 2 × ZMod 2) _ => v ab.1 ab.2)
    · intro ab _
      simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
      rintro k ⟨hkj, hki⟩
      simp [v, Function.update_of_ne hkj, Function.update_of_ne hki]
    · intro ab _ cd _ he
      exact Prod.ext (by simpa [v, Function.update_of_ne hij] using congrFun he i)
        (by simpa [v] using congrFun he j)
    · intro y hy
      have h := (mem_filter.mp hy).2
      refine ⟨(y i, y j), mem_univ _, funext fun k => ?_⟩
      by_cases hkj : k = j
      · subst k; simp [v]
      by_cases hki : k = i
      · subst k; simp [v, Function.update_of_ne hij]
      · simpa [v, Function.update_of_ne hkj, Function.update_of_ne hki] using
          (h k (by simp [hki, hkj])).symm
    · intros; rfl
  · rw [Fintype.sum_prod_type]
    change (∑ a : Fin 2, ∑ b : Fin 2, f (v a b)) = _
    simp only [Fin.sum_univ_two]
    change f (v 0 0) + f (v 0 1) + (f (v 1 0) + f (v 1 1)) = _
    have hjone (a : ZMod 2) : v a 1 = Function.update ones i a := by
      unfold v
      apply Function.update_eq_self_iff.mpr
      simp [Function.update_of_ne hij.symm]
    rw [hjone, hjone]
    simp only [v, update_ones]

end Mo513259BooleanFaces
end

section
namespace Mo513259Principal

open Finset Matrix

private abbrev Pair (n : ℕ) := (i : Fin n) × ↥(Ioi i)

private theorem sum_pairs {n : ℕ} {R : Type*} [AddCommMonoid R] (f : Fin n → Fin n → R) :
    (∑ p : Pair n, f p.1 p.2.val) = ∑ i, ∑ j ∈ Ioi i, f i j := by
  rw [Fintype.sum_sigma (fun p : Pair n => f p.1 p.2.val)]
  apply sum_congr rfl
  intro i hi
  exact sum_coe_sort (Ioi i) (f i)

private theorem fold_pairs {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : Fin n → Fin n → R) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = ∑ p : Pair n, (f p.1 p.2.val + f p.2.val p.1) := by
  rw [sum_pairs (fun i j => f i j + f j i)]
  have split (i j) : f i j = (if i < j then f i j else 0) +
      (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h,not_lt_of_ge h.le]
    · simp [hd]
    · simp [h,not_lt_of_ge h.le]
  calc
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [← sum_add_distrib]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => split i j
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if i < j then f j i else 0) := by
      congr 1
      exact sum_comm
    _ = _ := by
      simp only [← sum_add_distrib, ← filter_lt_eq_Ioi, sum_filter]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by split_ifs <;> simp

private def minor {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (i j k l : Fin n) : R :=
  A i k * A j l - A i l * A j k

private theorem minor_mul {n : ℕ} {R : Type*} [CommRing R]
    (X Y : Matrix (Fin n) (Fin n) R) (i j a b : Fin n) :
    minor (X*Y) i j a b = ∑ p : Pair n,
      minor X i j p.1 p.2.val * minor Y p.1 p.2.val a b := by
  let f (k l : Fin n) :=
    (X i k * Y k a) * (X j l * Y l b) - (X i k * Y k b) * (X j l * Y l a)
  have he : minor (X*Y) i j a b = ∑ k, ∑ l, f k l := by
    simp only [minor,Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib,f]
    exact sum_comm
  rw [he,fold_pairs f (fun k => by dsimp [f]; ring)]
  apply sum_congr rfl
  intro p hp
  dsimp [f,minor]
  ring

def eTwo {n : ℕ} (P : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  ∑ i, ∑ j ∈ Ioi i, (P i i * P j j - P i j * P j i)

private theorem eTwo_mul {n : ℕ} (X Y : Matrix (Fin n) (Fin n) (ZMod 2)) :
    eTwo (X*Y) = ∑ p : Pair n, ∑ q : Pair n,
      minor X p.1 p.2.val q.1 q.2.val * minor Y q.1 q.2.val p.1 p.2.val := by
  change (∑ i, ∑ j ∈ Ioi i, minor (X*Y) i j i j) = _
  rw [← sum_pairs]
  exact sum_congr rfl fun p _ => minor_mul X Y _ _ _ _

private theorem cancel_symmetric {α : Type*} (s : Finset α) (f : α → α → ZMod 2)
    (hs : ∀ a b, f a b = f b a) :
    (∑ a ∈ s, ∑ b ∈ s, f a b) = ∑ a ∈ s, f a a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [sum_insert ha, sum_add_distrib]
    rw [ih, show (∑ b ∈ s, f b a) = ∑ b ∈ s, f a b from sum_congr rfl fun b _ => hs b a]
    have h := ZModModule.add_self (∑ b ∈ s, f a b)
    linear_combination h

theorem eTwo_mul_symmetric_hollow {n : ℕ} (M A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : M.IsSymm) (hA : A.IsSymm) (hMd : ∀ i, M i i = 0) (hAd : ∀ i, A i i = 0) :
    eTwo (M*A) = ∑ i, ∑ j ∈ Ioi i, M i j * A i j := by
  have sym {B : Matrix (Fin n) (Fin n) (ZMod 2)} (h : B.IsSymm) (i j k l : Fin n) :
      minor B i j k l = minor B k l i j := by
    simp only [minor]
    rw [h.apply i k,h.apply j l,h.apply i l,h.apply j k]
    ring
  have diag {B : Matrix (Fin n) (Fin n) (ZMod 2)} (h : B.IsSymm)
      (d : ∀ i, B i i = 0) (i j : Fin n) : minor B i j i j = B i j := by
    simp only [minor,d,zero_mul,zero_sub,h.apply i j,ZModModule.neg_eq_self]
    exact (by decide : ∀ x : ZMod 2, x*x=x) _
  rw [eTwo_mul, cancel_symmetric]
  · simpa only [diag hM hMd,diag hA hAd] using sum_pairs (fun i j => M i j * A i j)
  · intro p q
    rw [sym hM p.1 p.2.val q.1 q.2.val,sym hA q.1 q.2.val p.1 p.2.val]

theorem eTwo_mul_comm {n : ℕ} (X Y : Matrix (Fin n) (Fin n) (ZMod 2)) :
    eTwo (X*Y) = eTwo (Y*X) := by
  rw [eTwo_mul,eTwo_mul,sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_comm _ _

theorem eTwo_conjugated_diagonal {n : ℕ} (U V : Matrix (Fin n) (Fin n) (ZMod 2))
    (t : Fin n → ZMod 2) (h : U*V=1) :
    eTwo (V * diagonal t * U) = ∑ i, ∑ j ∈ Ioi i, t i * t j := by
  rw [eTwo_mul_comm _ U, ← Matrix.mul_assoc,h,one_mul]
  unfold eTwo
  refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
  have hij := (mem_Ioi.mp hj).ne
  simp [Matrix.diagonal_apply_ne _ hij]

end Mo513259Principal
end

section
namespace Mo513259Bookkeeping

open Matrix Finset
open scoped Matrix

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) (ZMod 2)

def d {n : ℕ} (A : Mat n) (i : Fin n) : ZMod 2 := ∑ j, A i j
def t {n : ℕ} (A : Mat n) (i : Fin n) : ZMod 2 := 1 + d A i
def M {n : ℕ} (A B : Mat n) := A.hadamard B
def P {n : ℕ} (A B : Mat n) := M A B * A
def C {n : ℕ} (A B : Mat n) := B * diagonal (t A) * A

variable {n : ℕ} (A B : Mat n)

theorem M_symm (hA : A.IsSymm) (hB : B.IsSymm) : (M A B).IsSymm := by
  change (A.hadamard B).transpose = A.hadamard B
  rw [transpose_hadamard, hA.eq, hB.eq]

theorem M_hollow (hA : ∀ i, A i i = 0) : ∀ i, M A B i i = 0 := by
  intro i
  simp [M, hadamard_apply, hA]

theorem row_M (hB : B.IsSymm) (hAB : A*B = 1) (i : Fin n) :
    (∑ j, M A B i j) = 1 := by
  calc
    _ = (A*B) i i := by
      rw [Matrix.mul_apply]
      exact sum_congr rfl fun j _ => by rw [M, hadamard_apply, hB.apply i j]
    _ = 1 := by simp [hAB]

private theorem absorb (a b : ZMod 2) : a * b * a = a * b :=
  (by decide : ∀ x y : ZMod 2, x*y*x=x*y) a b

theorem P_diag (hA : A.IsSymm) (hB : B.IsSymm) (hAB : A*B = 1) (i : Fin n) :
    P A B i i = 1 := by
  rw [← row_M A B hB hAB i]
  unfold P
  rw [Matrix.mul_apply]
  exact sum_congr rfl fun j _ => by
    rw [hA.apply i j]
    exact absorb _ _

theorem P_col_sum (hA : A.IsSymm) (hB : B.IsSymm) (hAB : A*B = 1) (j : Fin n) :
    (∑ i, P A B i j) = t A j + 1 := by
  have hm (k : Fin n) : (∑ i, M A B i k) = 1 := by
    simpa only [(M_symm A B hA hB).apply k] using row_M A B hB hAB k
  simp only [P, Matrix.mul_apply]
  rw [sum_comm]
  simp only [← sum_mul, hm, one_mul]
  have he : (∑ k, A k j) = d A j := sum_congr rfl fun k _ => hA.apply j k
  rw [he]
  exact (by decide : ∀ x : ZMod 2, x = (1+x)+1) _

theorem trace_C (hAB : A*B = 1) : (C A B).trace = ∑ i, t A i := by
  unfold C
  rw [trace_mul_cycle, hAB, one_mul, trace_diagonal]

theorem trace_PC (hA : A.IsSymm) (hB : B.IsSymm) (hAB : A*B = 1) :
    (P A B * C A B).trace = (C A B).trace := by
  have hrev : (P A B).transpose = A * M A B := by
    rw [P, transpose_mul, hA.eq, (M_symm A B hA hB).eq]
  have hprod : P A B * C A B = (M A B * diagonal (t A)) * A := by
    change (M A B * A) * (B * diagonal (t A) * A) = _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A B, hAB, one_mul]
  rw [hprod, trace_mul_cycle, ← hrev, trace_C A B hAB]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, P_diag A B hA hB hAB]

theorem eTwo_P (hA : A.IsSymm) (hB : B.IsSymm) (hAd : ∀ i, A i i = 0) :
    Mo513259Principal.eTwo (P A B) = ∑ i, ∑ j ∈ Ioi i, A i j * B i j := by
  rw [P, Mo513259Principal.eTwo_mul_symmetric_hollow _ _ (M_symm A B hA hB) hA
    (M_hollow A B hAd) hAd]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => absorb _ _

theorem sum_entries_zero (hA : A.IsSymm) (hAd : ∀ i, A i i = 0) :
    (∑ i, ∑ j, A i j) = 0 := by
  classical
  have aux (s : Finset (Fin n)) : (∑ i ∈ s, ∑ j ∈ s, A i j) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [sum_insert ha, sum_add_distrib, hAd, zero_add, ih, add_zero]
      have h : (∑ x ∈ s, A x a) = ∑ x ∈ s, A a x :=
        sum_congr rfl fun x _ => hA.apply a x
      rw [h, ZModModule.add_self]
  exact aux univ

theorem n_even (hA : A.IsSymm) (hB : B.IsSymm) (hAd : ∀ i, A i i = 0)
    (hAB : A*B = 1) : Even n := by
  have h := sum_entries_zero (M A B) (M_symm A B hA hB) (M_hollow A B hAd)
  simp only [row_M A B hB hAB, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff n 2).mp h)

theorem degree_sum_zero (hA : A.IsSymm) (hAd : ∀ i, A i i = 0) :
    (∑ i, d A i) = 0 := sum_entries_zero A hA hAd

theorem t_sum_zero (hA : A.IsSymm) (hB : B.IsSymm) (hAd : ∀ i, A i i = 0)
    (hAB : A*B = 1) : (∑ i, t A i) = 0 := by
  have hn := (ZMod.natCast_eq_zero_iff n 2).mpr (n_even A B hA hB hAd hAB).two_dvd
  simp [t, sum_add_distrib, degree_sum_zero A hA hAd, hn]

theorem even_card_ones (f : Fin n → ZMod 2) (hf : ∑ i, f i = 0) :
    Even (univ.filter fun i => f i = 1).card := by
  have hbit (x : ZMod 2) : (if x = 1 then 1 else 0) = x :=
    (by decide : ∀ x : ZMod 2, (if x = 1 then 1 else 0) = x) x
  have h : ((univ.filter fun i => f i = 1).card : ZMod 2) = 0 := by
    calc
      _ = ∑ i ∈ univ.filter (fun i => f i = 1), (1 : ZMod 2) := by simp
      _ = ∑ i, f i := by rw [sum_filter]; simp only [hbit]
      _ = 0 := hf
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ 2).mp h)

end Mo513259Bookkeeping
end

section
namespace Mo513259Mod8
open Finset
abbrev F2 := ZMod 2

section Sums
variable {n : ℕ} {R : Type*} [AddCommMonoid R]

theorem sum_upper_swap (f : Fin n → Fin n → R) :
    (∑ i, ∑ j ∈ Ioi i, (f i j + f j i)) =
      ∑ i, ∑ j, if i = j then 0 else f i j := by
  classical
  have hu (i : Fin n) : Ioi i = univ.filter (fun j => i < j) := by ext; simp
  simp_rw [hu, sum_filter, ite_add_zero, sum_add_distrib]
  rw [sum_comm (f := fun i j => if i < j then f j i else 0), ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne, h.not_gt]
  · simp
  · simp [h, h.ne', h.not_gt]

theorem sum_off_diag_add (f : Fin n → Fin n → R) :
    (∑ i, ∑ j, if i = j then 0 else f i j) + (∑ i, f i i) = ∑ i, ∑ j, f i j := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have h : (∑ j, if i = j then f i j else 0) = f i i := by simp
  rw [← h, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h : i = j <;> simp [h]
end Sums

def eTwoC {n : ℕ} (C : Matrix (Fin n) (Fin n) F2) : F2 :=
  ∑ i, ∑ j ∈ Ioi i, (C i i*C j j - C i j*C j i)

def fourValues (x y u v w z p q : F2) : F2 :=
  x*y + (x+u)*(y+w) + (x+v)*(y+z) + (x+u+v+p)*(y+w+z+q)

theorem fourValues_eq (x y u v w z p q : F2) :
    fourValues x y u v w z p q = (u*z-v*w) +
      (p*(y+z)+p*w + (q*(x+u)+q*v)) + p*q := by
  unfold fourValues
  decide +revert

theorem quadratic_sum {n : ℕ} (v t : Fin n → F2)
    (C P : Matrix (Fin n) (Fin n) F2)
    (hP : ∀ i, P i i = 1)
    (hcol : ∀ j, (∑ i, P i j) = t j + 1)
    (htr : (∑ i, ∑ j, P i j*C j i) = ∑ i, C i i) :
    (∑ i, ∑ j ∈ Ioi i,
        fourValues (v i) (v j) (C i i) (C i j) (C j i) (C j j) (P i j) (P j i)) =
      eTwoC C + (∑ i, t i * (v i+C i i)) + ∑ i, ∑ j ∈ Ioi i, P i j * P j i := by
  classical
  let f (i j : Fin n) := P i j * (v j+C j j) + P i j * C j i
  have split (i j : Fin n) :
      fourValues (v i) (v j) (C i i) (C i j) (C j i) (C j j) (P i j) (P j i) =
      (C i i*C j j-C i j*C j i)+(f i j+f j i)+P i j*P j i := by
    exact fourValues_eq ..
  have hsplit : (∑ i, ∑ j ∈ Ioi i,
        fourValues (v i) (v j) (C i i) (C i j) (C j i) (C j j) (P i j) (P j i)) =
      eTwoC C + (∑ i, ∑ j ∈ Ioi i, (f i j+f j i)) +
      ∑ i, ∑ j ∈ Ioi i, P i j*P j i := by simp only [split, eTwoC, sum_add_distrib]
  rw [hsplit]
  congr 1
  congr 1
  have hadd := sum_off_diag_add f
  have hdiag : (∑ i, f i i) = ∑ i, (v i + C i i) + ∑ i, C i i := by
    simp [f, hP, sum_add_distrib]
  have hall : (∑ i, ∑ j, f i j) = (∑ i, (t i+1) * (v i + C i i)) + ∑ i, C i i := by
    simp only [f, sum_add_distrib, htr]
    congr 1
    rw [sum_comm]
    simp only [← sum_mul, hcol]
  rw [hdiag, hall] at hadd
  simp_rw [add_mul, one_mul, sum_add_distrib] at hadd
  exact (sum_upper_swap f).trans (by simpa [add_assoc] using hadd)

end Mo513259Mod8
end

section
namespace Mo513259TraceParity
open Finset Matrix Mo513259Bookkeeping

abbrev rho : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)
abbrev Mat8 (n : ℕ) := Matrix (Fin n) (Fin n) (ZMod 8)

theorem two_upper {n : ℕ} (A B : Mat8 n) (hA : A.IsSymm) (hB : B.IsSymm)
    (hAd : ∀ i, A i i = 0) (hAB : A*B = 1) :
    2 * (∑ i, ∑ j ∈ Ioi i, A i j * B i j) = (n : ZMod 8) := by
  let f (i j : Fin n) := A i j * B i j
  have hs (i j) : f j i = f i j := by simp only [f, hA.apply i j, hB.apply i j]
  have hd (i) : f i i = 0 := by simp [f, hAd]
  have split := Mo513259Mod8.sum_upper_swap f
  have total := Mo513259Mod8.sum_off_diag_add f
  simp only [hd, sum_const_zero, add_zero] at total
  calc
    _ = ∑ i, ∑ j ∈ Ioi i, (f i j + f j i) := by
      simp only [hs, sum_add_distrib, f, two_mul]
    _ = ∑ i, ∑ j, f i j := split.trans total
    _ = (A*B).trace := by
      unfold Matrix.trace Matrix.diag
      change (∑ i, ∑ j, f i j) = ∑ i, ∑ j, A i j * B j i
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
        dsimp only [f]
        rw [hB.apply i j]
    _ = _ := by simp [hAB]

private theorem range_pairs (r : ℕ) : (∑ i ∈ range (r+r), (i : ZMod 2)) = (r : ZMod 2) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show r+1+(r+1) = (r+r+1)+1 by omega, sum_range_succ, sum_range_succ, ih]
    simp [Nat.cast_add, ZModModule.add_self]

theorem count_upper {n r : ℕ} (hn : n = r+r) :
    (∑ i : Fin n, ∑ _j ∈ Ioi i, (1 : ZMod 2)) = (r : ZMod 2) := by
  simp only [sum_const, nsmul_eq_mul, mul_one, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((n-1-j : ℕ) : ZMod 2))]
  rw [sum_range_reflect (fun j => (j : ZMod 2))]
  simpa only [hn] using range_pairs r

theorem upper_P_zero {n : ℕ} (A B : Mat8 n) (hA : A.IsSymm) (hB : B.IsSymm)
    (hAd : ∀ i, A i i = 0) (hAB : A*B = 1) :
    (∑ i, ∑ j ∈ Ioi i, (P (A.map rho) (B.map rho)) i j *
      (P (A.map rho) (B.map rho)) j i) = 0 := by
  let U := A.map rho
  let V := B.map rho
  have hU : U.IsSymm := hA.map rho
  have hV : V.IsSymm := hB.map rho
  have hUd (i) : U i i = 0 := by simp [U, hAd]
  have hUV : U * V = 1 := by
    simpa [U, V] using congrArg (fun X : Mat8 n => rho.mapMatrix X) hAB
  obtain ⟨r, hr⟩ := n_even U V hU hV hUd hUV
  let q := ∑ i, ∑ j ∈ Ioi i, A i j * B i j
  have hdouble : (2 : ZMod 8)*q = 2 * (r : ZMod 8) := by
    change 2 * (∑ i, ∑ j ∈ Ioi i, A i j * B i j) = _
    rw [two_upper A B hA hB hAd hAB, hr, Nat.cast_add, two_mul]
  have half (a b : ZMod 8) : 2*a = 2*b → rho a = rho b :=
    (by decide : ∀ x y : ZMod 8, 2*x=2*y → rho x=rho y) a b
  have hq : (∑ i, ∑ j ∈ Ioi i, U i j * V i j) = (r : ZMod 2) := by
    simpa only [q, map_sum, map_mul, map_natCast, U, V, Matrix.map_apply] using
      half q (r : ZMod 8) hdouble
  have he := eTwo_P U V hU hV hUd
  rw [Mo513259Principal.eTwo, hq] at he
  simp only [P_diag U V hU hV hUV, one_mul, sum_sub_distrib, count_upper hr] at he
  exact sub_eq_self.mp he

end Mo513259TraceParity
end

section
namespace Mo513259Scalar

open Finset Matrix

abbrev rho : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)

private theorem square_sum {n : ℕ} (t : Fin n → ZMod 8) (ht : ∀ i, t i = 0 ∨ t i = 1)
    (s : Finset (Fin n)) : (∑ i ∈ s, t i) ^ 2 = (∑ i ∈ s, t i) +
      2 * (∑ i ∈ s, ∑ j ∈ s with i < j, t i * t j) := by
  refine Finset.induction_on_min s (by simp) ?_
  intro a u ha ih
  have hnot : a ∉ u := fun h => (ha a h).false
  let p := ∑ i ∈ u, ∑ j ∈ u with i < j, t i * t j
  have pairs : (∑ i ∈ insert a u, ∑ j ∈ insert a u with i < j, t i * t j) =
      t a * (∑ i ∈ u, t i) + p := by
    rw [sum_insert hnot, filter_insert, if_neg (lt_irrefl a), filter_true_of_mem ha, mul_sum]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [filter_insert, if_neg (ha i hi).not_gt]
  have hsq : t a ^ 2 = t a := by rcases ht a with h | h <;> simp [h]
  change (∑ i ∈ u, t i) ^ 2 = (∑ i ∈ u, t i) + 2 * p at ih
  rw [pairs, sum_insert hnot]
  linear_combination ih + hsq

theorem scalar_cancellation {n : ℕ} (t : Fin n → ZMod 8)
    (ht : ∀ i, t i = 0 ∨ t i = 1) (he : ∑ i, rho (t i) = 0) :
    4 * (∑ i, ∑ j ∈ Ioi i, t i * t j) - 2 * (∑ i, t i) = 0 := by
  have intervals (i : Fin n) : (univ.filter (fun j => i < j)) = Ioi i := by ext; simp
  have hsq := square_sum t ht univ
  simp only [intervals] at hsq
  have even_residue : ∀ x : ZMod 8, rho x = 0 → 2 * x ^ 2 - 4 * x = 0 := by decide
  have h := even_residue (∑ i, t i) (by simpa only [map_sum] using he)
  linear_combination h - 2 * hsq

end Mo513259Scalar
end

section
namespace Mo513259Faces
open Matrix Finset
abbrev R := ZMod 8
abbrev K := ZMod 2
abbrev rho : R →+* K := ZMod.castHom (by decide : 2 ∣ 8) K
abbrev Idx (n : ℕ) := Fin n
abbrev Cube (n : ℕ) := Fin n → K
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) R

def bit (b : K) : R := if b = 0 then 0 else 1
def sign (b : K) : R := if b = 0 then 1 else -1
def ones {n : ℕ} : Cube n := fun _ => 1
def atOne {n : ℕ} (j : Fin n) : Cube n := Function.update ones j 0
def atTwo {n : ℕ} (j k : Fin n) : Cube n := Function.update (atOne j) k 0
def U {n : ℕ} (A : Mat n) := A.map rho
def d {n : ℕ} (A : Mat n) : Cube n := (U A) *ᵥ ones
def t {n : ℕ} (A : Mat n) (i : Fin n) : R := 1-bit (d A i)
def C {n : ℕ} (A B : Mat n) : Mat n := B * diagonal (t A) * A
def P {n : ℕ} (A B : Mat n) : Matrix (Fin n) (Fin n) K :=
  Matrix.of (fun i j => (U A) i j * (U B) i j) * U A
def alpha {n : ℕ} (A B : Mat n) (y : Cube n) : Fin n → R :=
  B *ᵥ (fun i => bit ((U A *ᵥ y) i))
def half (r : R) : R := (r.val/2 : ℕ)
def c {n : ℕ} (A B : Mat n) (y : Cube n) (i : Fin n) := half (bit (y i) - alpha A B y i)
def v {n : ℕ} (A B : Mat n) := c A B ones

private theorem cast_bit (b : K) : rho (bit b) = b := by decide +revert
private theorem half_spec (r : R) (h : rho r = 0) : 2 * half r = r := by decide +revert
private theorem eight_two {x y : R} (h : 2*x=2*y) : rho x = rho y := by decide +revert

private theorem atOne_vec {n : ℕ} (j : Fin n) : atOne j = ones - Pi.single j 1 := by
  funext k
  by_cases h : k=j <;> simp [atOne, ones, h]

private theorem atTwo_vec {n : ℕ} (j k : Fin n) (h : j ≠ k) :
    atTwo j k = atOne j - Pi.single k 1 := by
  funext l
  by_cases hl : l=k <;> simp [atTwo, hl, atOne, ones, h.symm]

private theorem U_one {n : ℕ} (A : Mat n) (j i : Fin n) :
    (U A *ᵥ atOne j) i = d A i - U A i j := by simp [atOne_vec, mulVec_sub, d]
private theorem U_two {n : ℕ} (A : Mat n) (j k i : Fin n) (h : j ≠ k) :
    (U A *ᵥ atTwo j k) i = d A i - U A i j - U A i k := by
  simp [atTwo_vec j k h, mulVec_sub, U_one]

private theorem bit_one (u a : K) :
    bit (u-a) = bit u + (1-2*bit u)*bit a := by decide +revert
private theorem bit_two (u a b : K) :
    bit (u-a-b) = bit u + (1-2*bit u)*bit a + (1-2*bit u)*bit b -
        2*(1-2*bit u)*bit a*bit b := by decide +revert
private theorem bit_entry {n : ℕ} (A : Mat n) (h01 : ∀ i j, A i j=0 ∨ A i j=1)
    (i j : Fin n) : bit (U A i j) = A i j := by
  rcases h01 i j with h | h <;> simp [U, Matrix.map_apply, h, bit]

theorem actual {n : ℕ} (A B : Mat n) (hBA : B*A=1) (y : Cube n) (i : Fin n) :
    alpha A B y i = bit (y i) - 2*c A B y i := by
  have hp : rho (alpha A B y i) = y i := by
    have hmat : U B * U A = 1 := by
      simpa [U] using congrArg (fun M : Mat n => rho.mapMatrix M) hBA
    calc
      _ = ((U B) *ᵥ ((U A) *ᵥ y)) i := by
        simp only [alpha, U, mulVec, dotProduct, map_sum, map_mul, cast_bit, Matrix.map_apply]
      _ = _ := by rw [mulVec_mulVec, hmat, one_mulVec]
  rw [c, half_spec _ (by rw [map_sub, cast_bit, hp, sub_self])]
  abel

private theorem C_apply {n : ℕ} (A B : Mat n) (i j : Fin n) :
    C A B i j = ∑ k, B i k * t A k * A k j := by
  rw [C, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

private theorem delta {n : ℕ} (A B : Mat n) (hBA : B*A=1) (i j : Fin n) :
    (∑ k, B i k * ((1-2*bit (d A k))*A k j)) = 2 * C A B i j - (1 : Mat n) i j := by
  have hd : (1 : Mat n) i j = ∑ k, B i k*A k j := by rw [← hBA, Matrix.mul_apply]
  rw [hd, C_apply, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  unfold t
  ring

private def D {n : ℕ} (A B : Mat n) (i j k : Fin n) : R :=
  ∑ l, B i l * (1-2*bit (d A l)) * A l j * A l k

private theorem alpha_one {n : ℕ} (A B : Mat n) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (i j : Fin n) :
    alpha A B (atOne j) i = alpha A B ones i + (2*C A B i j-(1:Mat n) i j) := by
  rw [← delta A B hBA]
  unfold alpha
  simp only [mulVec, dotProduct] at ⊢
  change (∑ k, B i k * bit ((U A *ᵥ atOne j) k)) = _
  simp_rw [U_one, bit_one, bit_entry A h01, mul_add, sum_add_distrib]
  rfl

private theorem alpha_two {n : ℕ} (A B : Mat n) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (i j k : Fin n) (hjk : j ≠ k) :
    alpha A B (atTwo j k) i = alpha A B ones i + (2*C A B i j-(1:Mat n) i j) +
      (2*C A B i k-(1:Mat n) i k) - 2*D A B i j k := by
  rw [← delta A B hBA, ← delta A B hBA]
  change (∑ l, B i l * bit ((U A *ᵥ atTwo j k) l)) = _
  simp_rw [U_two A j k _ hjk, bit_two, bit_entry A h01, mul_sub, mul_add, sum_sub_distrib,
    sum_add_distrib]
  unfold D
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro l _
  ring

private theorem bit_atOne {n : ℕ} (i j : Fin n) :
    bit (atOne j i) = 1 - (1 : Mat n) i j := by
  by_cases h : i=j
  · subst j; simp [bit, atOne]
  · simp [bit, atOne, ones, h]

private theorem bit_atTwo {n : ℕ} (i j k : Fin n) (hjk : j ≠ k) :
    bit (atTwo j k i) = 1 - (1 : Mat n) i j - (1 : Mat n) i k := by
  by_cases h : i=k <;> by_cases g : i=j <;> simp_all [bit, atTwo, atOne, ones, Matrix.one_apply]

theorem c_one_double {n : ℕ} (A B : Mat n) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (i j : Fin n) :
    2*c A B (atOne j) i = 2*(v A B i-C A B i j) := by
  have h := alpha_one A B hBA h01 i j
  rw [actual A B hBA (atOne j), actual A B hBA ones, bit_atOne] at h
  simp only [ones, bit, one_ne_zero, ↓reduceIte] at h
  unfold v
  linear_combination -h

theorem c_one_rho {n : ℕ} (A B : Mat n) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (i j : Fin n) :
    rho (c A B (atOne j) i) = rho (v A B i)+rho (C A B i j) := by
  rw [eight_two (c_one_double A B hBA h01 i j), map_sub]
  have hsub (a b : K) : a-b=a+b := by decide +revert
  exact hsub ..

private theorem c_two_double {n : ℕ} (A B : Mat n) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (i j k : Fin n) (hjk : j ≠ k) :
    2*c A B (atTwo j k) i = 2*(v A B i-C A B i j-C A B i k+D A B i j k) := by
  have h := alpha_two A B hBA h01 i j k hjk
  rw [actual A B hBA (atTwo j k), actual A B hBA ones, bit_atTwo _ _ _ hjk] at h
  simp only [ones, bit, one_ne_zero, ↓reduceIte] at h
  unfold v
  linear_combination -h

theorem c_two_rho {n : ℕ} (A B : Mat n) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (hA : A.IsSymm)
    (i j : Fin n) (hij : i ≠ j) :
    rho (c A B (atTwo i j) i) =
      rho (v A B i)+rho (C A B i i)+rho (C A B i j)+P A B i j := by
  have hd : rho (D A B i i j) = P A B i j := by
    simp only [D, P, Matrix.mul_apply, map_sum, map_mul, map_sub, map_one, map_ofNat]
    apply sum_congr rfl
    intro l _
    change _ = rho (A i l) * rho (B i l) * rho (A l j)
    rw [hA.apply l i]
    have h2 : (2 : K) = 0 := by decide
    simp [h2, mul_comm]
  rw [eight_two (c_two_double A B hBA h01 i i j hij), map_add, map_sub, map_sub, hd]
  have hsub (a b : K) : a-b=a+b := by decide +revert
  simp only [hsub]

theorem c_two_rho_right {n : ℕ} (A B : Mat n) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (hA : A.IsSymm)
    (i j : Fin n) (hij : i ≠ j) :
    rho (c A B (atTwo i j) j) =
      rho (v A B j)+rho (C A B j i)+rho (C A B j j)+P A B j i := by
  have sw : atTwo i j = atTwo j i := Function.update_comm hij ..
  rw [sw, c_two_rho A B hBA h01 hA j i hij.symm]
  abel

theorem map_mul_eq_one {n : ℕ} (A B : Mat n) (h : A*B=1) : U A * U B = 1 := by
  simpa [U] using congrArg (fun M : Mat n => rho.mapMatrix M) h

def e {n : ℕ} (A B : Mat n) (hAB : A*B=1) (hBA : B*A=1) : Cube n ≃ Cube n where
  toFun := (U A).mulVec
  invFun := (U B).mulVec
  left_inv := fun x => by rw [mulVec_mulVec, map_mul_eq_one B A hBA, one_mulVec]
  right_inv := fun x => by rw [mulVec_mulVec, map_mul_eq_one A B hAB, one_mulVec]

def phase {n : ℕ} (A : Mat n) (y : Cube n) := ∏ i, sign ((U A *ᵥ y) i)

private theorem sign_sum {n : ℕ} (s : Finset (Fin n)) (f : Fin n → K) :
    (∏ i ∈ s, sign (f i)) = sign (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, ih]
    exact (by decide : ∀ x y : K, sign x * sign y = sign (x+y)) _ _

theorem phase_ones {n : ℕ} (A : Mat n) (hd : (∑ i, d A i) = 0) :
    phase A ones = 1 := by
  change (∏ i, sign (d A i)) = 1
  rw [sign_sum, hd]
  decide

theorem phase_one {n : ℕ} (A : Mat n) (hA : A.IsSymm) (hd : (∑ i, d A i) = 0)
    (j : Fin n) : phase A (atOne j) = 2*t A j - 1 := by
  have hcol : (∑ i, U A i j) = d A j := by
    unfold d
    simp only [U, mulVec, dotProduct, ones, mul_one]
    exact sum_congr rfl fun i _ => congrArg rho (hA.apply j i)
  unfold phase
  simp_rw [U_one]
  rw [sign_sum, sum_sub_distrib, hd, zero_sub, hcol]
  exact (by decide : ∀ x : K, sign (-x) = 2*(1-bit x)-1) _

theorem phase_rho {n : ℕ} (A : Mat n) (y : Cube n) : rho (phase A y) = 1 := by
  have hs (x : K) : rho (sign x) = 1 := by decide +revert
  simp only [phase, map_prod, hs, prod_const_one]

end Mo513259Faces
end

section
namespace Mo513259Faces
open Finset Matrix

def linearAt {n : ℕ} (A B : Mat n) (i : Fin n) : R :=
  phase A (atOne i) * c A B (atOne i) i + phase A ones * c A B ones i

def qAt {n : ℕ} (A B : Mat n) (i j : Fin n) (y : Cube n) : R :=
  phase A y * c A B y i * c A B y j

def faceAt {n : ℕ} (A B : Mat n) (i j : Fin n) : R :=
  qAt A B i j (atTwo i j) + qAt A B i j (atOne i) +
    (qAt A B i j (atOne j) + qAt A B i j ones)

theorem degree_agrees {n : ℕ} (A : Mat n) (i : Fin n) :
    d A i = Mo513259Bookkeeping.d (U A) i := by
  simp [d, Mo513259Bookkeeping.d, mulVec, dotProduct, ones]

theorem t_agrees {n : ℕ} (A : Mat n) (i : Fin n) :
    rho (t A i) = Mo513259Bookkeeping.t (U A) i := by
  have h (x : K) : rho (1 - bit x) = 1+x := by decide +revert
  simp only [t, h, degree_agrees, Mo513259Bookkeeping.t]

theorem C_agrees {n : ℕ} (A B : Mat n) :
    U (C A B) = Mo513259Bookkeeping.C (U A) (U B) := by
  change rho.mapMatrix (B*diagonal (t A)*A) = _
  have hdiag : rho.mapMatrix (diagonal (t A)) = diagonal (Mo513259Bookkeeping.t (U A)) := by
    ext i j
    by_cases h : i=j
    · subst j; simpa using t_agrees A i
    · simp [h]
  rw [map_mul, map_mul, hdiag]
  rfl

theorem P_agrees {n : ℕ} (A B : Mat n) :
    P A B = Mo513259Bookkeeping.P (U A) (U B) := rfl

theorem linear_eval {n : ℕ} (A B : Mat n) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (hA : A.IsSymm) (hd : (∑ i, d A i) = 0) :
    2*(∑ i, linearAt A B i) =
      4*(∑ i, t A i*(v A B i-C A B i i)) + 2*(∑ i, C A B i i) := by
  simp only [mul_sum, ← sum_add_distrib, linearAt, phase_one A hA hd, phase_ones A hd, one_mul]
  apply sum_congr rfl
  intro i _
  change 2*((2*t A i-1)*c A B (atOne i) i+v A B i) = _
  linear_combination (2*t A i-1)*c_one_double A B hBA h01 i i

theorem face_eval {n : ℕ} (A B : Mat n) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (hA : A.IsSymm)
    (i j : Fin n) (hij : i ≠ j) :
    rho (faceAt A B i j) = Mo513259Mod8.fourValues
      (rho (v A B i)) (rho (v A B j)) (rho (C A B i i)) (rho (C A B i j))
      (rho (C A B j i)) (rho (C A B j j)) (P A B i j) (P A B j i) := by
  simp only [faceAt, qAt, map_add, map_mul, phase_rho, one_mul,
    c_two_rho A B hBA h01 hA i j hij, c_two_rho_right A B hBA h01 hA i j hij,
    c_one_rho A B hBA h01, Mo513259Mod8.fourValues, v]
  ring

theorem quadratic_eval {n : ℕ} (A B : Mat n) (hBA : B*A=1) (hAB : A*B=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (hA : A.IsSymm) (hB : B.IsSymm)
    (hpair : (∑ i, ∑ j ∈ Ioi i, P A B i j * P A B j i) = 0) :
    4*(∑ i, ∑ j ∈ Ioi i, faceAt A B i j) =
      4*((∑ i, ∑ j ∈ Ioi i, t A i * t A j) + ∑ i, t A i*(v A B i+C A B i i)) := by
  have cast4 (r s : R) (h : rho r = rho s) : 4*r = 4*s := by decide +revert
  apply cast4
  simp only [map_sum, map_add, map_mul]
  have step := Mo513259Mod8.quadratic_sum (fun i => rho (v A B i)) (fun i => rho (t A i))
    (U (C A B)) (P A B)
  have hAB' := map_mul_eq_one A B hAB
  have hA' : (U A).IsSymm := hA.map _
  have hB' : (U B).IsSymm := hB.map _
  have diagP := Mo513259Bookkeeping.P_diag (U A) (U B) hA' hB' hAB'
  have colP := Mo513259Bookkeeping.P_col_sum (U A) (U B) hA' hB' hAB'
  have htr := Mo513259Bookkeeping.trace_PC (U A) (U B) hA' hB' hAB'
  have hp := step diagP (fun j => (colP j).trans (by rw [t_agrees])) (by
    rw [C_agrees]; exact htr)
  have e2 : Mo513259Mod8.eTwoC (U (C A B)) =
      ∑ i, ∑ j ∈ Ioi i, rho (t A i)*rho (t A j) := by
    change Mo513259Principal.eTwo _ = _
    rw [C_agrees]
    simp_rw [t_agrees]
    exact Mo513259Principal.eTwo_conjugated_diagonal _ _ _ hAB'
  rw [e2, hpair, add_zero] at hp
  refine Eq.trans ?_ hp
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j hj
  exact face_eval A B hBA h01 hA i j (mem_Ioi.mp hj).ne

theorem final_arithmetic {n : ℕ} (A B : Mat n) (hAB : A*B=1)
    (hq : 4*(∑ i, ∑ j ∈ Ioi i, t A i*t A j) - 2*(∑ i, t A i) = 0)
    (hl : 2*(∑ i, linearAt A B i) =
      4*(∑ i, t A i*(v A B i-C A B i i)) + 2*(∑ i, C A B i i))
    (hf : 4*(∑ i, ∑ j ∈ Ioi i, faceAt A B i j) =
      4*((∑ i, ∑ j ∈ Ioi i, t A i*t A j) + ∑ i, t A i*(v A B i+C A B i i))) :
    1 - 2*(∑ i, linearAt A B i) + 4*(∑ i, ∑ j ∈ Ioi i, faceAt A B i j) = 1 := by
  have ht : (∑ i, C A B i i) = ∑ i, t A i := by
    change (B*diagonal (t A)*A).trace = _
    rw [trace_mul_cycle, hAB, one_mul, trace_diagonal]
  rw [hl, hf, ht]
  simp_rw [mul_sub, sum_sub_distrib, mul_add, sum_add_distrib]
  have hz : (8 : R)=0 := by decide
  linear_combination hq + (∑ i, t A i*C A B i i)*hz

end Mo513259Faces
end

section
open Finset Mo513259BooleanFaces

namespace Mo513259FaceExpansion

abbrev bit (a : ZMod 2) : ZMod 8 := if a = 0 then 0 else 1
abbrev sign {n : ℕ} (e : Cube n ≃ Cube n) (y : Cube n) : ZMod 8 :=
  ∏ k, if e y k = 0 then 1 else -1
abbrev single {n : ℕ} (i : Fin n) : Cube n := Function.update ones i 0
abbrev double {n : ℕ} (i j : Fin n) : Cube n := Function.update (single i) j 0
abbrev linear {n : ℕ} (e : Cube n ≃ Cube n) (c : Cube n → Fin n → ZMod 8)
    (i : Fin n) (y : Cube n) := sign e y * c y i
abbrev quadratic {n : ℕ} (e : Cube n ≃ Cube n) (c : Cube n → Fin n → ZMod 8)
    (i j : Fin n) (y : Cube n) := sign e y * c y i * c y j

theorem permanent_eq_faces {n : ℕ} (hn : Even n) (B : Matrix (Fin n) (Fin n) (ZMod 8))
    (e : Cube n ≃ Cube n) (c : Cube n → Fin n → ZMod 8)
    (h : ∀ y i, (∑ j, B i j * bit (e y j)) = bit (y i) - 2 * c y i) :
    B.permanent = sign e ones -
      2 * (∑ i, (linear e c i (single i) + linear e c i ones)) +
      4 * (∑ i : Fin n, ∑ j ∈ Ioi i, (quadratic e c i j (double i j) + quadratic e c i j (single i) +
          (quadratic e c i j (single j) + quadratic e c i j ones))) := by
  classical
  let P (y : Cube n) (t : Finset (Fin n)) := ∏ k ∈ t, bit (y k)
  have point (y : Cube n) : sign e y * (∏ i, (bit (y i) - 2 * c y i)) =
      sign e y * P y univ -
        2 * (∑ i, linear e c i y * P y (univ.erase i)) +
        4 * (∑ i : Fin n, ∑ j ∈ Ioi i, quadratic e c i j y * P y ((univ.erase i).erase j)) := by
    rw [OeisRyser.truncated_product (fun i => bit (y i)) (c y)]
    simp only [P, mul_add, mul_sub, mul_left_comm (sign e y) 2, mul_left_comm (sign e y) 4,
      Finset.mul_sum, linear, quadratic, ← mul_assoc]
  calc
    B.permanent = ∑ y : Cube n, sign e y * ∏ i, ∑ j, B i j * bit (e y j) := by
      rw [OeisRyser.permanent_eq_bits hn B]
      exact (Equiv.sum_comp e (fun x : Cube n =>
        (∏ i, if x i = 0 then (1 : ZMod 8) else -1) * ∏ i, ∑ j, B i j * bit (x j))).symm
    _ = weighted (sign e) univ -
          2 * (∑ i, weighted (linear e c i) (univ.erase i)) +
          4 * (∑ i : Fin n, ∑ j ∈ Ioi i, weighted (quadratic e c i j) ((univ.erase i).erase j)) := by
      simp_rw [h, point]
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
      congr 2
      · congr 1
        exact sum_comm
      · rw [sum_comm]
        apply sum_congr rfl
        intro i _
        exact sum_comm
    _ = _ := by
      rw [weighted_univ]
      simp_rw [weighted_erase]
      congr 2
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j hj
      exact weighted_erase_erase _ i j (mem_Ioi.mp hj).ne

end Mo513259FaceExpansion
end

section
namespace Mo513259Faces
open Finset Matrix

theorem permanent_eight_of_parity {n : ℕ} (A B : Mat n) (hAB : A*B=1) (hBA : B*A=1)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1) (hA : A.IsSymm) (hB : B.IsSymm)
    (hAd : ∀ i, A i i = 0)
    (hpair : (∑ i, ∑ j ∈ Ioi i, P A B i j * P A B j i) = 0) :
    B.permanent = 1 := by
  have hA' : (U A).IsSymm := hA.map _
  have hB' : (U B).IsSymm := hB.map _
  have hAd' (i) : U A i i = 0 := by change rho (A i i) = 0; rw [hAd, map_zero]
  have hAB' := map_mul_eq_one A B hAB
  have hn := Mo513259Bookkeeping.n_even (U A) (U B) hA' hB' hAd' hAB'
  have hd : (∑ i, d A i) = 0 := by
    simp_rw [degree_agrees]
    exact Mo513259Bookkeeping.degree_sum_zero (U A) hA' hAd'
  have ht (i) : t A i=0 ∨ t A i=1 := by
    exact (by decide : ∀ x : K, 1-bit x=0 ∨ 1-bit x=1) _
  have ht0 : (∑ i, rho (t A i)) = 0 := by
    simp_rw [t_agrees]
    exact Mo513259Bookkeeping.t_sum_zero (U A) (U B) hA' hB' hAd' hAB'
  have hbase := Mo513259FaceExpansion.permanent_eq_faces hn B (e A B hAB hBA) (c A B)
    (actual A B hBA)
  change B.permanent = phase A ones - 2*(∑ i, linearAt A B i) +
    4*(∑ i, ∑ j ∈ Ioi i, faceAt A B i j) at hbase
  rw [phase_ones A hd] at hbase
  exact hbase.trans (final_arithmetic A B hAB (Mo513259Scalar.scalar_cancellation _ ht ht0)
    (linear_eval A B hBA h01 hA hd) (quadratic_eval A B hBA hAB h01 hA hB hpair))

end Mo513259Faces
end

section
namespace Mo513259ModFour
open Finset Matrix

private abbrev π₄ := ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)
private def bit (z : ZMod 2) : ZMod 4 := if z = 0 then 0 else 1

private theorem pbit (z : ZMod 2) : π₄ (bit z) = z := (by decide : ∀ z : ZMod 2, π₄ (bit z) = z) z
private theorem two_eq {a b : ZMod 4} (h : π₄ a = π₄ b) : 2*a = 2*b :=
  (by decide : ∀ a b : ZMod 4, π₄ a = π₄ b → 2*a = 2*b) a b h
private theorem kill {a b : ZMod 4} (ha : π₄ a = 0) (hb : π₄ b = 0) : a*b = 0 :=
  (by decide : ∀ a b : ZMod 4, π₄ a = 0 → π₄ b = 0 → a*b = 0) a b ha hb

-- The diagonal trace of a symmetric even correction paired with a hollow
-- symmetric matrix vanishes because off-diagonal terms occur in equal pairs.
private theorem trace_even {n : ℕ} (B E : Matrix (Fin n) (Fin n) (ZMod 4))
    (hB : B.IsSymm) (hE : E.IsSymm) (hD : ∀ i, B i i = 0) (he : ∀ i j, π₄ (E i j) = 0) :
    (B*E).trace = 0 := by
  let f (i j : Fin n) := B i j * E j i
  have sym (i j) : f i j = f j i := by simp only [f, hB.apply i j, hE.apply i j]
  have dbl (i j) : f i j + f i j = 0 := by
    have h := two_eq (a := E j i) (b := 0) (by simp [he])
    dsimp only [f]
    linear_combination B i j * h
  have vanish (s : Finset (Fin n)) : (∑ i ∈ s, ∑ j ∈ s, f i j) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [sum_insert hi, sum_add_distrib, ih, add_zero]
      rw [show f i i = 0 by simp [f,hD], zero_add,
          show (∑ j ∈ s, f j i) = ∑ j ∈ s, f i j from sum_congr rfl (fun j _ => sym j i),
          ← sum_add_distrib]
      exact sum_eq_zero fun j _ => dbl i j
  exact vanish univ

private theorem product_linear {n : ℕ} (s : Finset (Fin n)) (f g : Fin n → ZMod 4)
    (h : ∀ i, π₄ (f i) = π₄ (g i)) :
    (∏ i ∈ s, f i) = ∏ i ∈ s, g i +
      ∑ i ∈ s, (f i - g i) * ∏ j ∈ s.erase i, g j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [prod_insert ha, sum_insert ha, erase_insert ha]
    have hh : (∑ i ∈ s, (f i - g i) * ∏ j ∈ (insert a s).erase i, g j) =
        f a * ∑ i ∈ s, (f i-g i) * ∏ j ∈ s.erase i, g j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have hne : a ≠ i := fun e => ha (e ▸ hi)
      rw [erase_insert_of_ne hne, prod_insert (fun ht => ha (mem_of_mem_erase ht))]
      have hkill := kill (a := f a-g a) (b := f i-g i) (by rw [map_sub, h, sub_self]) (by rw [map_sub, h, sub_self])
      linear_combination -(∏ j ∈ s.erase i, g j) * hkill
    rw [hh, ih]
    ring

abbrev Cube (n : ℕ) := Fin n → ZMod 2
abbrev ones {n : ℕ} : Cube n := fun _ => 1

private theorem update_ones {n : ℕ} (i : Fin n) : Function.update ones i 1 = ones :=
  Function.update_eq_self i ones

def weighted {n : ℕ} (f : Cube n → ZMod 4) (T : Finset (Fin n)) : ZMod 4 :=
  ∑ y : Cube n, f y * ∏ k ∈ T, (if y k = 0 then 0 else 1)

theorem weighted_eq_filter {n : ℕ} (f : Cube n → ZMod 4) (T : Finset (Fin n)) :
    weighted f T = ∑ y ∈ univ.filter (fun y : Cube n => ∀ k ∈ T, y k = 1), f y := by
  classical
  have hz (a : ZMod 2) : (if a = 0 then (0 : ZMod 4) else 1) =
      (if a = 1 then 1 else 0) := by fin_cases a <;> decide
  simp only [weighted, hz, Finset.prod_boole, Finset.sum_filter, mul_ite, mul_one, mul_zero]

theorem weighted_univ {n : ℕ} (f : Cube n → ZMod 4) :
    weighted f univ = f ones := by
  rw [weighted_eq_filter]
  have hu : univ.filter (fun y : Cube n => ∀ k ∈ (univ : Finset (Fin n)), y k = 1) =
      {ones} := by
    ext y
    simp [funext_iff, ones]
  rw [hu, sum_singleton]

theorem weighted_erase {n : ℕ} (f : Cube n → ZMod 4) (i : Fin n) :
    weighted f (univ.erase i) = f (Function.update ones i 0) + f ones := by
  classical
  rw [weighted_eq_filter]
  let v (a : ZMod 2) := Function.update (ones (n := n)) i a
  trans ∑ a : ZMod 2, f (v a)
  · symm
    apply sum_bij (fun (a : ZMod 2) _ => v a)
    · intro a _
      simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
      intro k hki
      simp [v, Function.update_of_ne hki]
    · intro a _ b _ he
      simpa [v] using congrFun he i
    · intro y hy
      have h := (mem_filter.mp hy).2
      refine ⟨y i, mem_univ _, funext fun k => ?_⟩
      by_cases hk : k = i
      · subst k; simp [v]
      · simpa [v, Function.update_of_ne hk] using (h k (by simp [hk])).symm
    · intros; rfl
  · change (∑ a : Fin 2, f (v a)) = _
    rw [Fin.sum_univ_two]
    change f (v 0) + f (v 1) = _
    simp only [v, update_ones]


private theorem sign_prod {n : ℕ} (x : Cube n) :
    (∏ i, if x i = 0 then (1 : ZMod 4) else -1) = 1-2*(∑ i, bit (x i)) := by
  have hi (s : Finset (Fin n)) :
      (∏ i ∈ s, if x i = 0 then (1 : ZMod 4) else -1) = 1-2*(∑ i ∈ s, bit (x i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha, ih]
      by_cases h : x a = 0
      · simp [bit,h]
      · rw [if_neg h, show bit (x a) = 1 by simp [bit,h]]
        have h4 : (4 : ZMod 4) = 0 := by decide
        linear_combination (∑ i ∈ s, bit (x i)) * h4
  exact hi univ

private theorem evaluate {n : ℕ} (x : Cube n → Cube n) (F : Cube n → Fin n → ZMod 4)
    (h : ∀ y i, π₄ (F y i) = y i) :
    (∑ y, (∏ i, if x y i = 0 then (1 : ZMod 4) else -1) * ∏ i, F y i) =
      1-2*(∑ i, bit (x ones i)) + ∑ i, (F (Function.update ones i 0) i + F ones i - 1) := by
  let w (y : Cube n) := ∏ i, if x y i = 0 then (1 : ZMod 4) else -1
  let e (y : Cube n) (i : Fin n) := F y i - bit (y i)
  have he (y i) : π₄ (e y i) = 0 := by dsimp only [e]; rw [map_sub, h, pbit, sub_self]
  have hw (y i) : w y * e y i = e y i := by
    have hv := kill (a := w y - 1) (b := e y i) (by
      dsimp only [w]; rw [sign_prod, map_sub, map_sub, map_mul, map_one]
      rw [show π₄ 2 = 0 by decide, zero_mul, sub_zero, sub_self]) (he _ _)
    linear_combination hv
  calc
    _ = weighted w univ + ∑ i, weighted (fun y => e y i) (univ.erase i) := by
      unfold weighted
      rw [sum_comm (f := fun i (y : Cube n) => e y i * _), ← sum_add_distrib]
      apply sum_congr rfl
      intro y _
      rw [product_linear univ (F y) (fun i => bit (y i)) (by intro i; rw [h,pbit]), mul_add, mul_sum]
      congr 1
      apply sum_congr rfl
      intro i _
      change w y * (e y i * _) = e y i * _
      rw [← mul_assoc, hw]; rfl
    _ = _ := by
      rw [weighted_univ]; dsimp only [w]; rw [sign_prod]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [weighted_erase]
      simp [e,ones,bit]; ring



theorem permanent_eq_one_of_even {n : ℕ} (hn : Even n) (B : Matrix (Fin n) (Fin n) (ZMod 4))
    (hs : B.IsSymm) (hd : ∀ i, B i i = 0) (hunit : IsUnit B.det) : B.permanent = 1 := by
  classical
  let V := B⁻¹
  have hBV : B*V=1 := Matrix.mul_nonsing_inv B hunit
  have hVB : V*B=1 := Matrix.nonsing_inv_mul B hunit
  have hsV : V.IsSymm := by change B⁻¹ᵀ=B⁻¹; rw [Matrix.transpose_nonsing_inv, hs.eq]
  let U := π₄.mapMatrix B
  let T := π₄.mapMatrix V
  have hUT : U*T=1 := by rw [show U*T=π₄.mapMatrix (B*V) from (map_mul _ _ _).symm,hBV,map_one]
  have hTU : T*U=1 := by rw [show T*U=π₄.mapMatrix (V*B) from (map_mul _ _ _).symm,hVB,map_one]
  let e : Cube n ≃ Cube n :=
    ⟨(T *ᵥ ·), (U *ᵥ ·), fun y => by change U *ᵥ (T *ᵥ y) = y; rw [mulVec_mulVec,hUT,one_mulVec],
      fun y => by change T *ᵥ (U *ᵥ y) = y; rw [mulVec_mulVec,hTU,one_mulVec]⟩
  let F (y : Cube n) := B *ᵥ (fun j => bit (e y j))
  have hF (y : Cube n) (i) : π₄ (F y i)=y i := by
    rw [show π₄ (F y i) = (U *ᵥ (π₄ ∘ fun j => bit (e y j))) i from RingHom.map_mulVec _ _ _ _]
    rw [show (π₄ ∘ fun j => bit (e y j)) = e y from funext (fun _ => pbit _)]
    change (U *ᵥ (T *ᵥ y)) i = y i
    rw [mulVec_mulVec,hUT,one_mulVec]
  let W := V.map (fun a => bit (π₄ a))
  have hW (i j) : 2*W i j = 2*V i j := two_eq (pbit _)
  have hsW : W.IsSymm := hsV.map _
  have htrace : (B*W).trace = n := by
    have h := trace_even B (W-V) hs (hsW.sub hsV) hd (by
      intro i j
      change π₄ (bit (π₄ (V i j)) - V i j)=0
      rw [map_sub,pbit,sub_self])
    rw [mul_sub,trace_sub,hBV,trace_one,sub_eq_zero] at h
    simpa using h
  have hWB (i) : 2*((W*B) i i) = 2 := by
    calc
      _ = 2*((V*B) i i) := by
        simp only [Matrix.mul_apply,mul_sum]
        apply sum_congr rfl
        intro j _
        rw [← mul_assoc,hW,mul_assoc]
      _ = _ := by rw [hVB]; simp
  let d (i : Fin n) := bit (e ones i)
  have diff (i j : Fin n) :
      bit (e (Function.update ones i 0) j) = d j + (1-2*d j)*W j i := by
    have hv : Function.update (ones (n:=n)) i 0 = ones + Pi.single i 1 := by
      funext j
      by_cases h : j=i
      · subst j; simp [ones]; decide
      · simp [Function.update_of_ne h,Pi.single_eq_of_ne h,ones]
    rw [hv]
    change bit ((T *ᵥ (ones + Pi.single i 1)) j) = _
    rw [mulVec_add,Pi.add_apply,mulVec_single_one]
    exact (by decide : ∀ a b : ZMod 2, bit (a+b) = bit a + (1-2*bit a)*bit b) _ _
  have single (i : Fin n) : F (Function.update ones i 0) i =
      F ones i + (B*W) i i - 2*(∑ j, d j * (B i j * W j i)) := by
    simp only [F,Matrix.mulVec,dotProduct,diff,Matrix.mul_apply]
    simp only [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    change _ = B i j * d j + _ - _
    ring
  have dblF (i : Fin n) : 2*F ones i=2 := by
    simpa using two_eq (a:=F ones i) (b:=1) (by rw [hF,map_one])
  have sw : (∑ i, 2*∑ j, d j * (B i j * W j i)) = ∑ j, 2*d j := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    calc
      _ = d j*(2*((W*B) j j)) := by
        simp only [Matrix.mul_apply,mul_sum]
        apply sum_congr rfl
        intros; ring
      _ = _ := by rw [hWB]; ring
  rw [OeisRyser.permanent_eq_bits hn B]
  rw [← e.sum_comp]
  change (∑ y, (∏ i, if e y i=0 then (1:ZMod 4) else -1)*∏ i, F y i) = _
  rw [evaluate e F hF]
  simp_rw [single]
  have replace (i) : F ones i + (B*W) i i - 2*(∑ j, d j * (B i j * W j i)) + F ones i - 1 =
      (1 : ZMod 4) + (B*W) i i - 2*(∑ j, d j * (B i j * W j i)) := by linear_combination dblF i
  simp_rw [replace]
  rw [sum_sub_distrib,sum_add_distrib,sw,← mul_sum]
  change 1-2*(∑ i, d i)+((∑ _ : Fin n, (1 : ZMod 4))+(B*W).trace-2*∑ i,d i)=1
  rw [htrace]
  obtain ⟨k,hk⟩ := hn
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,hk,Nat.cast_add]
  have h4 : (4 : ZMod 4)=0 := by decide
  linear_combination ((k : ZMod 4) - ∑ i,d i)*h4




/-- A symmetric hollow matrix with unit determinant over Z/4 has permanent one. -/
theorem permanent_eq_one {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 4))
    (hs : B.IsSymm) (hd : ∀ i, B i i = 0) (hu : IsUnit B.det) : B.permanent = 1 := by
  have hv : B⁻¹.IsSymm := by change B⁻¹ᵀ=B⁻¹; rw [transpose_nonsing_inv,hs.eq]
  have hz := trace_even B ((2 : ZMod 4) • B⁻¹) hs (hv.smul _) hd (by
    intro i j
    change π₄ (2*(B⁻¹ i j))=0
    rw [map_mul,show π₄ 2=0 by decide,zero_mul])
  rw [Matrix.mul_smul,Matrix.mul_nonsing_inv B hu,Matrix.trace_smul,Matrix.trace_one,
    Fintype.card_fin,smul_eq_mul] at hz
  have hc : (((2*n : ℕ) : ZMod 4)) = 0 := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz
  have hdiv := (ZMod.natCast_eq_zero_iff (2*n) 4).mp hc
  apply permanent_eq_one_of_even _ B hs hd hu
  rw [even_iff_two_dvd]
  omega

end Mo513259ModFour
end

section
namespace Mo513259
open OMA.S_mo_513259 Matrix

private theorem reduce_graph {n m k : ℕ} (φ : ZMod m →+* ZMod k)
    {A : Matrix (Fin n) (Fin n) (ZMod m)} (h : IsGraphMatrix A) :
    IsGraphMatrix (φ.mapMatrix A) := by
  obtain ⟨hs, hd, he⟩ := h
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · ext i j
    exact congrArg φ (congrFun (congrFun hs i) j)
  · change φ (A i i) = 0
    rw [hd, map_zero]
  · change φ (A i j) = 0 ∨ φ (A i j) = 1
    rcases he i j with h | h <;> simp [h]

private theorem reduce_unit {n m k : ℕ} (φ : ZMod m →+* ZMod k)
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (h : IsUnit A.det) :
    IsUnit (φ.mapMatrix A).det := by
  rw [← φ.map_det]
  exact h.map φ

private theorem reduce_permanent {n m k : ℕ} (φ : ZMod m →+* ZMod k)
    (A : Matrix (Fin n) (Fin n) (ZMod m)) :
    (φ.mapMatrix A).permanent = φ A.permanent := by
  simp [Matrix.permanent, RingHom.mapMatrix_apply, Matrix.map_apply]

private theorem reduce_inverse_permanent {n m k : ℕ} (φ : ZMod m →+* ZMod k)
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (h : IsUnit A.det) :
    (φ.mapMatrix A)⁻¹.permanent = φ (A⁻¹).permanent := by
  have hi : (φ.mapMatrix A)⁻¹ = φ.mapMatrix (A⁻¹) := by
    apply inv_eq_left_inv
    rw [← map_mul, nonsing_inv_mul A h, map_one]
  rw [hi, reduce_permanent]

private abbrev mod8 := ZMod.castHom (show 8 ∣ 24 by decide) (ZMod 8)
private abbrev mod4 := ZMod.castHom (show 4 ∣ 24 by decide) (ZMod 4)
private abbrev mod3 := ZMod.castHom (show 3 ∣ 24 by decide) (ZMod 3)

private theorem combine_residues :
    ∀ p q : ZMod 24, mod4 p = 1 → mod8 q = 1 → mod3 q = mod3 p →
      2 * p + q - 3 = 0 := by decide

theorem final_of_graph_lemmas
    (h8 : ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) (ZMod 8),
      IsGraphMatrix A → IsUnit A.det → (A⁻¹).permanent = 1)
    (h4 : ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) (ZMod 4),
      IsGraphMatrix A → IsUnit A.det → A.permanent = 1) :
    type_of% @OMA.S_mo_513259.main := by
  refine ⟨h8, ?_⟩
  intro n A hg hu
  apply combine_residues
  · rw [← reduce_permanent]
    exact h4 _ _ (reduce_graph _ hg) (reduce_unit _ A hu)
  · rw [← reduce_inverse_permanent mod8 A hu]
    exact h8 _ _ (reduce_graph _ hg) (reduce_unit _ A hu)
  · rw [← reduce_inverse_permanent mod3 A hu, ← reduce_permanent]
    exact permanent_inv_mod_three _ (reduce_unit _ A hu)

end Mo513259
end

theorem OMA.solution : type_of% @OMA.S_mo_513259.main := by
  apply Mo513259.final_of_graph_lemmas
  · intro n A hg hu
    obtain ⟨hA, hAd, h01⟩ := hg
    have hB : (A⁻¹).IsSymm := by
      change Matrix.transpose (A⁻¹) = A⁻¹
      rw [Matrix.transpose_nonsing_inv, hA.eq]
    have hAB := Matrix.mul_nonsing_inv A hu
    exact Mo513259Faces.permanent_eight_of_parity A A⁻¹ hAB (Matrix.nonsing_inv_mul A hu)
      h01 hA hB hAd (Mo513259TraceParity.upper_P_zero A A⁻¹ hA hB hAd hAB)
  · intro n A hg hu
    exact Mo513259ModFour.permanent_eq_one A hg.1 hg.2.1 hu
