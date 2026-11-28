import FormalConjectures.GreensOpenProblems.«22»
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
Finite shift averaging for monochromatic sums and products.

The construction follows Korsky, Forcing and Avoiding Monochromatic Pairs of the Form
x + y, xy, sections 3–4, https://hexagonmath.org/pdf/2611.00978v1.
The resulting finite bound implies Green and Sawhney, Theorem 1.1,
https://arxiv.org/abs/2511.09365v2.
-/

namespace GreenSawhneyFinite

open Finset
open scoped BigOperators

private theorem avg_congr {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    (h : ∀ i, f i = g i) : (𝔼 i, f i) = 𝔼 i, g i :=
  Finset.expect_congr rfl (fun i _ => h i)

private theorem avg_nonneg {ι : Type*} [Fintype ι] {f : ι → ℝ}
    (h : ∀ i, 0 ≤ f i) : 0 ≤ 𝔼 i, f i :=
  Finset.expect_nonneg (fun i _ => h i)

private theorem avg_le {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    (h : ∀ i, f i ≤ g i) : (𝔼 i, f i) ≤ 𝔼 i, g i :=
  Finset.expect_le_expect (fun i _ => h i)

private theorem avg_const {ι : Type*} [Fintype ι] [Nonempty ι] (x : ℝ) :
    (𝔼 _ : ι, x) = x :=
  Fintype.expect_const _

private theorem avg_add {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (𝔼 i : ι, (f i + g i)) = (𝔼 i : ι, f i) + (𝔼 i : ι, g i) :=
  Finset.expect_add_distrib _ _ _

private theorem avg_sub {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (𝔼 i : ι, (f i - g i)) = (𝔼 i : ι, f i) - (𝔼 i : ι, g i) :=
  Finset.expect_sub_distrib _ _ _

private theorem avg_mul_left {ι : Type*} [Fintype ι] (a : ℝ) (f : ι → ℝ) :
    (𝔼 i, a * f i) = a * 𝔼 i, f i :=
  (Finset.mul_expect _ _ _).symm

private theorem avg_mul_right {ι : Type*} [Fintype ι] (a : ℝ) (f : ι → ℝ) :
    (𝔼 i, f i * a) = (𝔼 i, f i) * a :=
  (Finset.expect_mul _ _ _).symm

private theorem avg_product {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ) :
    (𝔼 i : ι × κ, f i.1 i.2) = 𝔼 a, 𝔼 b, f a b := by
  rw [← Finset.univ_product_univ]
  exact Finset.expect_product' _ _ _

private theorem avg_swap {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ) :
    (𝔼 a, 𝔼 b, f a b) = 𝔼 b, 𝔼 a, f a b :=
  Finset.expect_comm _ _ _

private theorem avg_translate {G : Type*} [AddGroup G] [Fintype G] (a : G) (f : G → ℝ) :
    (𝔼 n, f (n + a)) = 𝔼 n, f n :=
  Fintype.expect_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

private theorem avg_cs {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (𝔼 i, f i * g i)^2 ≤ (𝔼 i, (f i)^2) * (𝔼 i, (g i)^2) :=
  Finset.expect_mul_sq_le_sq_mul_sq _ _ _

private theorem avg_sq {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (𝔼 i, f i)^2 ≤ 𝔼 i, (f i)^2 := by
  simpa [avg_const] using avg_cs f (fun _ => 1)

private theorem avg_sq_eq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (𝔼 i, f i)^2 = 𝔼 i, 𝔼 j, f i * f j := by
  simp_rw [pow_two, avg_mul_left, avg_mul_right]

private theorem avg_bool (f : Bool → ℝ) :
    (𝔼 b : Bool, f b) = (f false + f true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp [add_comm]

private theorem avg_indicator_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    (𝔼 x : ι, if x = a then (1 : ℝ) else 0) = 1 / Fintype.card ι := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  simp

private theorem avg_exists_ge {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → ℝ}
    {a : ℝ} (h : a ≤ 𝔼 i, f i) : ∃ i, a ≤ f i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty h
  exact ⟨i, hi⟩

private def split_coord {ι α : Type*} [DecidableEq ι] (i : ι) :
    (ι → α) ≃ α × ({j : ι // j ≠ i} → α) where
  toFun f := ⟨f i, fun j => f j⟩
  invFun p j := if h : j = i then p.1 else p.2 ⟨j, h⟩
  left_inv f := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j
      exact dif_neg j.2

private theorem avg_eval {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (i : ι) (f : α → ℝ) : (𝔼 e : ι → α, f (e i)) = 𝔼 x, f x := by
  calc
    _ = (𝔼 p : α × ({j : ι // j ≠ i} → α), f p.1) :=
      Fintype.expect_equiv (split_coord i) (fun e => f (e i)) (fun p => f p.1) (fun _ => rfl)
    _ = _ := by
      rw [avg_product (fun (x : α) (_ : {j : ι // j ≠ i} → α) => f x)]
      simp_rw [avg_const]

private theorem avg_eval_pair {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] {i j : ι} (h : i ≠ j) (f : α → α → ℝ) :
    (𝔼 e : ι → α, f (e i) (e j)) = 𝔼 x, 𝔼 y, f x y := by
  calc
    _ = (𝔼 p : α × ({k : ι // k ≠ i} → α), f p.1 (p.2 ⟨j, h.symm⟩)) :=
      Fintype.expect_equiv (split_coord i) (fun e => f (e i) (e j))
        (fun p => f p.1 (p.2 ⟨j, h.symm⟩)) (fun _ => rfl)
    _ = _ := by
      rw [avg_product (fun x (e : {k : ι // k ≠ i} → α) => f x (e ⟨j, h.symm⟩))]
      exact avg_congr fun x => avg_eval (ι := {k : ι // k ≠ i}) ⟨j, h.symm⟩ (f x)

private def multiplier {m K : ℕ} (e : Fin K → ZMod m) : ℕ :=
  ∏ i : Fin K, (i.val + 1) ^ (e i).val

private def signedMultiplier {m K : ℕ} (b : Bool) (e : Fin K → ZMod m) : ℤ :=
  if b then (multiplier e : ℤ) else -(multiplier e : ℤ)

private theorem multiplier_pos {m K : ℕ} (e : Fin K → ZMod m) : 0 < multiplier e := by
  unfold multiplier
  positivity

private theorem multiplier_dvd {m K : ℕ} [NeZero m] (e : Fin K → ZMod m) :
    multiplier e ∣ K.factorial ^ m := by
  have hf : (∏ i : Fin K, (i.val+1)) = K.factorial := by
    simpa only [Finset.prod_range_add_one_eq_factorial] using (Fin.prod_univ_eq_prod_range (fun j : ℕ => j+1) K)
  rw [← hf, ← Finset.prod_pow]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
    pow_dvd_pow _ (ZMod.val_lt (e i)).le

private noncomputable def rotateCoord {m K : ℕ} (i : Fin K) :
    (Fin K → ZMod m) ≃ (Fin K → ZMod m) :=
  Equiv.piCongrRight fun j => if j = i then Equiv.addRight 1 else Equiv.refl _

private theorem rotateCoord_apply {m K : ℕ} (i j : Fin K) (e : Fin K → ZMod m) :
    rotateCoord i e j = if j = i then e j + 1 else e j := by
  unfold rotateCoord
  split_ifs with h <;> simp [Equiv.piCongrRight, h]

private theorem rotate_multiplier {m K : ℕ} [NeZero m] (hm : 1 < m)
    (i : Fin K) (e : Fin K → ZMod m) (hne : e i ≠ ((m-1 : ℕ) : ZMod m)) :
    multiplier (rotateCoord i e) = (i.val + 1) * multiplier e := by
  classical
  have hei : (e i).val + 1 < m := by
    have hlt := ZMod.val_lt (e i)
    by_contra! hb
    apply hne
    apply ZMod.val_injective m
    rw [ZMod.val_natCast_of_lt (by omega : m - 1 < m)]
    omega
  unfold multiplier
  rw [← Finset.mul_prod_erase Finset.univ _ (mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j : Fin K => (j.val+1) ^ (e j).val) (mem_univ i)]
  have hprod : (∏ j ∈ Finset.univ.erase i, (j.val + 1) ^ (rotateCoord i e j).val) =
      ∏ j ∈ Finset.univ.erase i, (j.val + 1) ^ (e j).val := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [rotateCoord_apply, if_neg (Finset.mem_erase.mp hj).1]
  letI : Fact (1 < m) := ⟨hm⟩
  rw [hprod, rotateCoord_apply, if_pos rfl, ZMod.val_add_of_lt, ZMod.val_one m, pow_succ]
  · ring
  · simpa [ZMod.val_one m] using hei

/-- An exponent rotation agrees with multiplication except at the final residue. -/
private theorem multiplier_stable_pos {m K : ℕ} [NeZero m] (hm : 1 < m)
    (i : Fin K) (p : ℤ → ℝ) (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) :
    |(𝔼 e : Fin K → ZMod m, p ((i.val + 1 : ℕ) * (multiplier e : ℤ))) -
        𝔼 e : Fin K → ZMod m, p (multiplier e)| ≤ 1 / (m : ℝ) := by
  let b : ZMod m := ((m-1 : ℕ) : ZMod m)
  have heq : (𝔼 e : Fin K → ZMod m, p (multiplier (rotateCoord i e))) =
      𝔼 e : Fin K → ZMod m, p (multiplier e) :=
    Fintype.expect_equiv (rotateCoord i) _ _ (fun _ => rfl)
  rw [← heq, ← avg_sub]
  calc
    _ ≤ 𝔼 e : Fin K → ZMod m,
        |p ((i.val + 1 : ℕ) * (multiplier e : ℤ)) - p (multiplier (rotateCoord i e))| :=
      Finset.abs_expect_le _ _
    _ ≤ 𝔼 e : Fin K → ZMod m, if e i = b then 1 else 0 := by
      apply avg_le
      intro e
      split_ifs with h
      · have h0 := hp0 ((i.val + 1 : ℕ) * (multiplier e : ℤ))
        have h1 := hp1 ((i.val + 1 : ℕ) * (multiplier e : ℤ))
        have hr0 := hp0 (multiplier (rotateCoord i e))
        have hr1 := hp1 (multiplier (rotateCoord i e))
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · rw [rotate_multiplier hm i e h, Nat.cast_mul, sub_self, abs_zero]
    _ = _ := by rw [avg_eval i (fun z => if z = b then (1:ℝ) else 0), avg_indicator_eq, ZMod.card]

private theorem multiplier_stable {m K : ℕ} [NeZero m] (hm : 1 < m)
    (d : ℤ) (hd0 : d ≠ 0) (hdK : d.natAbs ≤ K)
    (p : ℤ → ℝ) (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) :
    |(𝔼 b : Bool, 𝔼 e : Fin K → ZMod m, p (d * signedMultiplier b e)) -
        𝔼 b : Bool, 𝔼 e : Fin K → ZMod m, p (signedMultiplier b e)| ≤ 1 / (m : ℝ) := by
  have hdpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
  let i : Fin K := ⟨d.natAbs - 1, by omega⟩
  have hi : i.val + 1 = d.natAbs := by change d.natAbs - 1 + 1 = _; omega
  have hplus := multiplier_stable_pos hm i p hp0 hp1
  have hminus := multiplier_stable_pos hm i (fun z => p (-z)) (fun z => hp0 _) (fun z => hp1 _)
  rw [hi] at hplus hminus
  rw [avg_bool, avg_bool]
  simp only [signedMultiplier, Bool.false_eq_true, if_false, if_true] at *
  have hd : d = (d.natAbs : ℤ) ∨ d = -(d.natAbs : ℤ) := by
    rcases le_total 0 d with h | h
    · exact Or.inl (Int.natAbs_of_nonneg h).symm
    · right; omega
  rcases hd with h | h
  · rw [h]
    simp only [mul_neg]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hplus).1, (abs_le.mp hminus).1],
      by linarith [(abs_le.mp hplus).2, (abs_le.mp hminus).2]⟩
  · rw [h]
    simp only [neg_mul, mul_neg, neg_neg]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hplus).1, (abs_le.mp hminus).1],
      by linarith [(abs_le.mp hplus).2, (abs_le.mp hminus).2]⟩

end GreenSawhneyFinite

namespace GreenSawhneyFinite

open Finset
open scoped BigOperators

private theorem avg01 {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    0 ≤ (𝔼 i, f i) ∧ (𝔼 i, f i) ≤ 1 := by
  exact ⟨avg_nonneg hf0, Finset.expect_le Finset.univ_nonempty (fun i _ => hf1 i)⟩

private theorem mul01 {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    0 ≤ x*y ∧ x*y ≤ 1 :=
  ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩

private theorem avg_fiber {ι : Type*} [Fintype ι] (p : ι → ℤ)
    (hinj : Function.Injective p) (a : ℤ) :
    (𝔼 i, if p i = a then (1 : ℝ) else 0) ≤ 1 / Fintype.card ι := by
  classical
  by_cases he : ∃ i, p i = a
  · obtain ⟨i, rfl⟩ := he
    simp only [hinj.eq_iff, avg_indicator_eq, le_refl]
  · push Not at he
    simp only [he, if_false, Finset.expect_const_zero]
    positivity

private abbrev Choice (m : ℕ) := Fin m × (Fin m × Fin m)

private def squareShift {m : ℕ} (i : Choice m) : ℤ := ((i.1.val : ℤ)+1)^2

private def linearShift {m : ℕ} (i : Choice m) : ℤ :=
  (i.2.1.val : ℤ) - (i.2.2.val : ℤ)

private theorem avg_square_collision {m : ℕ} [Nonempty (Fin m)] (a : ℤ) :
    (𝔼 i : Choice m, if squareShift i = a then (1 : ℝ) else 0) ≤ 1 / (m : ℝ) := by
  rw [show (𝔼 i : Choice m, if squareShift i = a then (1 : ℝ) else 0) =
      (𝔼 i : Fin m, 𝔼 _j : Fin m × Fin m, if ((i.val : ℤ)+1)^2 = a then 1 else 0) from
    avg_product (fun (i : Fin m) (_j : Fin m × Fin m) => if ((i.val : ℤ)+1)^2 = a then (1:ℝ) else 0)]
  simp_rw [avg_const]
  simpa using avg_fiber (fun i : Fin m => ((i.val : ℤ)+1)^2) (by
    intro i j hij
    apply Fin.ext
    have hi : (0 : ℤ) ≤ i.val := by positivity
    have hj : (0 : ℤ) ≤ j.val := by positivity
    have he : (i.val : ℤ) + 1 = (j.val : ℤ) + 1 := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hij with h | h
      · exact h
      · omega
    omega) a

private theorem avg_linear_collision {m : ℕ} [Nonempty (Fin m)] (a : ℤ) :
    (𝔼 i : Choice m, if linearShift i = a then (1 : ℝ) else 0) ≤ 1 / (m : ℝ) := by
  rw [show (𝔼 i : Choice m, if linearShift i = a then (1 : ℝ) else 0) =
      (𝔼 _i : Fin m, 𝔼 jk : Fin m × Fin m, if (jk.1.val : ℤ) - jk.2.val = a then 1 else 0) from
    avg_product (fun (_i : Fin m) (jk : Fin m × Fin m) => if (jk.1.val : ℤ) - jk.2.val = a then (1:ℝ) else 0)]
  rw [avg_const, show (𝔼 jk : Fin m × Fin m, if (jk.1.val : ℤ) - jk.2.val = a then (1 : ℝ) else 0) =
     (𝔼 j : Fin m, 𝔼 k : Fin m, if (j.val : ℤ) - k.val = a then 1 else 0) from avg_product (fun (j k : Fin m) => if (j.val : ℤ) - k.val = a then (1:ℝ) else 0),
    avg_swap, ← avg_const (ι := Fin m) (1 / (m : ℝ))]
  apply avg_le
  intro k
  simpa only [Fintype.card_fin] using avg_fiber (fun j : Fin m => (j.val : ℤ) - k.val)
    (by intro i j h; apply Fin.ext; change (i.val : ℤ) - k.val = (j.val : ℤ) - k.val at h; omega) a

private theorem avg_collision_pair {m : ℕ} [Nonempty (Fin m)] {p : Choice m → ℤ}
    (hp : ∀ a : ℤ, (𝔼 i, if p i = a then (1 : ℝ) else 0) ≤ 1 / (m : ℝ))
    (q : Choice m → ℤ) :
    (𝔼 i, 𝔼 j, if p i = q j then (1 : ℝ) else 0) ≤ 1 / (m : ℝ) := by
  rw [avg_swap, ← avg_const (ι := Choice m) (1 / (m : ℝ))]
  exact avg_le fun j => hp (q j)

private theorem avg_cs_translates {G ι : Type*} [AddCommGroup G] [Fintype G] [Fintype ι]
    [Nonempty ι] (v : ι → G) (h : G → ℝ) :
    (𝔼 n, h n)^2 ≤ 𝔼 i, 𝔼 j, 𝔼 n, h n * h (n + (v i - v j)) := by
  let b (n : G) := 𝔼 i, h (n + v i)
  have he : (𝔼 n, b n) = 𝔼 n, h n := by
    dsimp [b]
    rw [avg_swap]
    simp_rw [avg_translate, avg_const]
  have hsq : (𝔼 n, (b n)^2) = 𝔼 i, 𝔼 j, 𝔼 n, h n * h (n + (v i - v j)) := by
    dsimp [b]
    simp_rw [avg_sq_eq]
    rw [avg_swap]
    apply avg_congr; intro i
    rw [avg_swap]
    apply avg_congr; intro j
    rw [← avg_translate (v j) (fun n => h n * h (n + (v i - v j)))]
    apply avg_congr; intro n
    rw [mul_comm]
    congr 2
    abel
  rw [← he, ← hsq]
  exact avg_sq b

/-- Cauchy–Schwarz bounds the correlation averaged over differences of two linear shifts. -/
private theorem avg_shift_lower {G : Type*} [AddCommGroup G] [Fintype G] {m : ℕ}
    [Nonempty (Fin m)] (f : Fin m → G → ℝ)
    (hf : ∀ i n, 0 ≤ f i n ∧ f i n ≤ 1) (g : G → ℝ)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ 1) (v : G) :
    (𝔼 n, 𝔼 i : Fin m, g n * f i n)^2 ≤
      𝔼 n, 𝔼 k : Choice m, g n * f k.1 (n + linearShift k • v) := by
  let h (n : G) := g n * 𝔼 i : Fin m, f i n
  have hf' (n : G) : 0 ≤ (𝔼 i : Fin m, f i n) ∧ (𝔼 i : Fin m, f i n) ≤ 1 :=
    avg01 _ (fun i => (hf i n).1) (fun i => (hf i n).2)
  have hh : ∀ n, 0 ≤ h n := fun n => (mul01 (hg n) (hf' n)).1
  have hhg : ∀ n, h n ≤ g n := fun n => mul_le_of_le_one_right (hg n).1 (hf' n).2
  have hhf : ∀ n, h n ≤ (𝔼 i, f i n) := fun n => mul_le_of_le_one_left (hf' n).1 (hg n).2
  simp_rw [avg_mul_left]
  change (𝔼 n, h n)^2 ≤ _
  have h1 := avg_cs_translates (fun i : Fin m => (i.val : ℤ) • v) h
  refine h1.trans ?_
  have he :
      (𝔼 n, g n * (𝔼 k : Choice m, f k.1 (n + linearShift k • v))) =
      (𝔼 j : Fin m, 𝔼 k : Fin m, 𝔼 n, g n * (𝔼 i : Fin m,
          f i (n + (((j.val : ℤ) - k.val) • v)))) := by
    simp_rw [← avg_mul_left]
    simp_rw [show ∀ (n : G), (𝔼 k : Choice m, g n * f k.1 (n + linearShift k • v)) =
      (𝔼 i : Fin m, 𝔼 jk : Fin m × Fin m, g n * f i (n + ((jk.1.val : ℤ) - jk.2.val) • v)) from
      fun n => avg_product (fun i (jk : Fin m × Fin m) => g n * f i (n + ((jk.1.val : ℤ) - jk.2.val) • v))]
    apply Eq.trans (avg_congr (fun n => avg_swap _))
    simp_rw [show ∀ (n : G), (𝔼 jk : Fin m × Fin m, 𝔼 i : Fin m,
        g n * f i (n + ((jk.1.val : ℤ) - jk.2.val) • v)) =
        (𝔼 j : Fin m, 𝔼 k : Fin m, 𝔼 i : Fin m, g n * f i (n + ((j.val : ℤ) - k.val) • v)) from
        fun n => avg_product (fun (j k : Fin m) => 𝔼 i : Fin m, g n * f i (n + ((j.val : ℤ) - k.val) • v))]
    rw [avg_swap]
    apply avg_congr; intro j
    rw [avg_swap]
  rw [he]
  apply avg_le; intro j
  apply avg_le; intro k
  apply avg_le; intro n
  rw [sub_zsmul, sub_eq_add_neg]
  exact mul_le_mul (hhg n) (hhf _) (hh _) (hg n).1

private theorem cross_approx {G : Type*} [AddCommGroup G] [Fintype G]
    {m K : ℕ} [NeZero m] (hm : 1 < m) (q : G)
    (f g : G → ℝ) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1) (hg : ∀ n, 0 ≤ g n ∧ g n ≤ 1)
    (a b : ℤ) (hab : (b-a).natAbs ≤ K) :
    |(𝔼 s : Bool, 𝔼 e : Fin K → ZMod m, 𝔼 n,
        f (n + (a * signedMultiplier s e) • q) * g (n + (b * signedMultiplier s e) • q)) -
      (𝔼 s : Bool, 𝔼 e : Fin K → ZMod m, 𝔼 n, f n * g (n + signedMultiplier s e • q))|
      ≤ 1 / (m : ℝ) + if a = b then 1 else 0 := by
  let p (v : ℤ) := 𝔼 n, f n * g (n + v • q)
  have hp (v : ℤ) : 0 ≤ p v ∧ p v ≤ 1 :=
    avg01 _ (fun n => (mul01 (hf n) (hg _)).1) (fun n => (mul01 (hf n) (hg _)).2)
  have hc (v : ℤ) :
      (𝔼 n, f (n + (a*v) • q) * g (n + (b*v) • q)) = p ((b-a)*v) := by
    unfold p
    rw [← avg_translate ((a*v) • q) (fun n => f n * g (n + ((b-a)*v) • q))]
    apply avg_congr; intro n
    rw [sub_mul, sub_zsmul]
    congr 1
    congr 1
    abel
  simp_rw [hc]
  by_cases h : a = b
  · rw [if_pos h]
    have h1 := avg01 (fun s : Bool => 𝔼 e : Fin K → ZMod m, p ((b-a)*signedMultiplier s e))
      (fun s => avg_nonneg fun e => (hp _).1)
      (fun s => (avg01 _ (fun e => (hp _).1) (fun e => (hp _).2)).2)
    have h2 := avg01 (fun s : Bool => 𝔼 e : Fin K → ZMod m, p (signedMultiplier s e))
      (fun s => avg_nonneg fun e => (hp _).1)
      (fun s => (avg01 _ (fun e => (hp _).1) (fun e => (hp _).2)).2)
    change |(𝔼 s : Bool, 𝔼 e : Fin K → ZMod m, p ((b-a)*signedMultiplier s e)) -
      (𝔼 s : Bool, 𝔼 e : Fin K → ZMod m, p (signedMultiplier s e))| ≤ _
    have he : (0:ℝ) ≤ 1 / m := by positivity
    exact abs_le.mpr ⟨by linarith [h1.1,h2.2], by linarith [h1.2,h2.1]⟩
  · simpa only [if_neg h, add_zero] using
      multiplier_stable hm (b-a) (sub_ne_zero.mpr (Ne.symm h)) hab p (fun v => (hp v).1) (fun v => (hp v).2)

end GreenSawhneyFinite

namespace GreenSawhneyFinite

open Finset
open scoped BigOperators

private abbrev Exponents (m K : ℕ) := Fin K → ZMod m

private theorem shift_ranges {m : ℕ} (i : Choice m) :
    (-(m : ℤ) ≤ squareShift i ∧ squareShift i ≤ (m : ℤ)^2) ∧
    (-(m : ℤ) ≤ linearShift i ∧ linearShift i ≤ (m : ℤ)^2) := by
  have h1 := i.1.isLt
  have h2 := i.2.1.isLt
  have h3 := i.2.2.isLt
  have h4 : (i.1.val : ℤ) + 1 ≤ m := by omega
  have h5 : (0 : ℤ) ≤ (i.1.val : ℤ)+1 := by positivity
  have h6 : (m : ℤ) ≤ (m : ℤ)^2 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ m by positivity) (show (0 : ℤ) ≤ (m : ℤ)-1 by omega)]
  dsimp [squareShift, linearShift]
  exact ⟨⟨le_trans (by omega) (sq_nonneg _), pow_le_pow_left₀ h5 h4 2⟩, ⟨by omega, by omega⟩⟩

private theorem avg_cross_global {G : Type*} [AddCommGroup G] [Fintype G]
    {m : ℕ} [NeZero m] [Nonempty (Fin m)] (hm : 1 < m) (q : G)
    (f : Fin m → G → ℝ) (hf : ∀ i n, 0 ≤ f i n ∧ f i n ≤ 1)
    (p₁ p₂ : Choice m → ℤ)
    (h₁ : ∀ a, (𝔼 i, if p₁ i = a then (1 : ℝ) else 0) ≤ 1 / (m : ℝ))
    (h₂ : ∀ i j, (p₂ j - p₁ i).natAbs ≤ m^2+m) :
    |(𝔼 i, 𝔼 j, 𝔼 s : Bool, 𝔼 e : Exponents m (m^2+m), 𝔼 n,
        f i.1 (n + (p₁ i * signedMultiplier s e) • q) *
          f j.1 (n + (p₂ j * signedMultiplier s e) • q)) -
      (𝔼 i : Choice m, 𝔼 j : Choice m, 𝔼 s : Bool, 𝔼 e : Exponents m (m^2+m), 𝔼 n,
        f i.1 n * f j.1 (n + signedMultiplier s e • q))| ≤ 2 / (m : ℝ) := by
  let C (i j : Choice m) := 𝔼 s : Bool, 𝔼 e : Exponents m (m^2+m), 𝔼 n,
        f i.1 (n + (p₁ i * signedMultiplier s e) • q) *
          f j.1 (n + (p₂ j * signedMultiplier s e) • q)
  let Q (i j : Choice m) := 𝔼 s : Bool, 𝔼 e : Exponents m (m^2+m), 𝔼 n,
        f i.1 n * f j.1 (n + signedMultiplier s e • q)
  change |(𝔼 i, 𝔼 j, C i j) - (𝔼 i, 𝔼 j, Q i j)| ≤ _
  rw [← avg_sub (fun i => 𝔼 j, C i j) (fun i => 𝔼 j, Q i j)]
  have hd (i : Choice m) := (avg_sub (C i) (Q i)).symm
  simp_rw [hd]
  calc
    _ ≤ 𝔼 i : Choice m, |𝔼 j : Choice m, (C i j - Q i j)| := Finset.abs_expect_le _ _
    _ ≤ 𝔼 i : Choice m, 𝔼 j : Choice m, |C i j - Q i j| :=
      avg_le fun i => Finset.abs_expect_le _ _
    _ ≤ 𝔼 i : Choice m, 𝔼 j : Choice m,
        (1 / (m : ℝ) + if p₁ i = p₂ j then 1 else 0) := by
      apply avg_le; intro i
      apply avg_le; intro j
      exact cross_approx hm q (f i.1) (f j.1) (hf i.1) (hf j.1) (p₁ i) (p₂ j) (h₂ i j)
    _ ≤ _ := by
      simp_rw [avg_add, avg_const]
      have hc := avg_collision_pair h₁ p₂
      simp only [div_eq_mul_inv] at hc ⊢
      linarith only [hc]

private theorem avg_swap_pair {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (𝔼 a, 𝔼 b, 𝔼 c, f a b c) = 𝔼 b, 𝔼 c, 𝔼 a, f a b c := by
  rw [avg_swap]
  exact avg_congr fun b => avg_swap (fun a c => f a b c)

private theorem avg_move_triple {W I A B : Type*} [Fintype W] [Fintype I]
    [Fintype A] [Fintype B] (f : W → I → A → B → B → ℝ) :
    (𝔼 w, 𝔼 i, 𝔼 a, 𝔼 b, 𝔼 c, f w i a b c) =
      𝔼 b, 𝔼 c, 𝔼 w, 𝔼 i, 𝔼 a, f w i a b c := by
  calc
    _ = (𝔼 w, 𝔼 i, 𝔼 b, 𝔼 c, 𝔼 a, f w i a b c) :=
      avg_congr fun w => avg_congr fun i => avg_swap_pair (fun a b c => f w i a b c)
    _ = (𝔼 w, 𝔼 b, 𝔼 c, 𝔼 i, 𝔼 a, f w i a b c) :=
      avg_congr fun w => avg_swap_pair (fun i b c => 𝔼 a, f w i a b c)
    _ = _ := avg_swap_pair (fun w b c => 𝔼 i, 𝔼 a, f w i a b c)

/-- Pairs of unequal shifts give the same correlation up to the multiplier error. Each collision costs at most one. -/
private theorem avg_shift_moment {G : Type*} [AddCommGroup G] [Fintype G]
    {m : ℕ} [NeZero m] [Nonempty (Fin m)] (hm : 1 < m) (q : G)
    (f : Fin m → G → ℝ) (hf : ∀ i n, 0 ≤ f i n ∧ f i n ≤ 1) :
    let K := m^2+m
    let A (v : ℤ) (n : G) := 𝔼 i : Choice m, f i.1 (n + (squareShift i * v) • q)
    let B (v : ℤ) (n : G) := 𝔼 i : Choice m, f i.1 (n + (linearShift i * v) • q)
    (𝔼 e : Exponents m K, 𝔼 n, (A (multiplier e) n - B (multiplier e) n)^2) ≤ 16 / (m : ℝ) := by
  dsimp only
  let K := m^2+m
  let V := Exponents m K
  let S (v : ℤ) (n : G) (i : Choice m) := f i.1 (n + (squareShift i * v) • q)
  let L (v : ℤ) (n : G) (i : Choice m) := f i.1 (n + (linearShift i * v) • q)
  let M (v : ℤ) (n : G) := ((𝔼 i, S v n i) - (𝔼 i, L v n i))^2
  change (𝔼 e : V, 𝔼 n, M (multiplier e) n) ≤ _
  let Q := 𝔼 i : Choice m, 𝔼 j : Choice m, 𝔼 b : Bool, 𝔼 e : V, 𝔼 n,
    f i.1 n * f j.1 (n + signedMultiplier b e • q)
  let C (p₁ p₂ : Choice m → ℤ) := 𝔼 i, 𝔼 j, 𝔼 b : Bool, 𝔼 e : V, 𝔼 n,
    f i.1 (n + (p₁ i * signedMultiplier b e) • q) *
      f j.1 (n + (p₂ j * signedMultiplier b e) • q)
  have hgaps (p₁ p₂ : Choice m → ℤ)
      (hp₁ : ∀ i, -(m : ℤ) ≤ p₁ i ∧ p₁ i ≤ (m : ℤ)^2)
      (hp₂ : ∀ i, -(m : ℤ) ≤ p₂ i ∧ p₂ i ≤ (m : ℤ)^2)
      (hcol : ∀ a, (𝔼 i, if p₁ i = a then (1 : ℝ) else 0) ≤ 1 / (m : ℝ)) :
      |C p₁ p₂ - Q| ≤ 2 / (m : ℝ) := by
    apply avg_cross_global hm q f hf p₁ p₂ hcol
    intro i j
    have hi := hp₁ i
    have hj := hp₂ j
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    apply abs_le.mpr
    push_cast
    constructor <;> linarith [hi.1,hi.2,hj.1,hj.2]
  have hss := hgaps squareShift squareShift (fun i => (shift_ranges i).1)
    (fun i => (shift_ranges i).1) avg_square_collision
  have hsl := hgaps squareShift linearShift (fun i => (shift_ranges i).1)
    (fun i => (shift_ranges i).2) avg_square_collision
  have hls := hgaps linearShift squareShift (fun i => (shift_ranges i).2)
    (fun i => (shift_ranges i).1) avg_linear_collision
  have hll := hgaps linearShift linearShift (fun i => (shift_ranges i).2)
    (fun i => (shift_ranges i).2) avg_linear_collision
  have hexpand (v : ℤ) (n : G) : M v n = 𝔼 i, 𝔼 j, (S v n i - L v n i)*(S v n j - L v n j) := by
    unfold M
    rw [← avg_sub]
    exact avg_sq_eq _
  have hident :
      (𝔼 b : Bool, 𝔼 e : V, 𝔼 n, M (signedMultiplier b e) n) =
      C squareShift squareShift - C squareShift linearShift -
        C linearShift squareShift + C linearShift linearShift := by
    simp_rw [hexpand]
    rw [avg_move_triple]
    simp_rw [show ∀ a b c d : ℝ, (a-b)*(c-d) = a*c - a*d - b*c + b*d by intros; ring,
      avg_add, avg_sub]
    rfl
  have hbnd : (𝔼 b : Bool, 𝔼 e : V, 𝔼 n, M (signedMultiplier b e) n) ≤ 8 / (m : ℝ) := by
    rw [hident]
    have ha := (abs_le.mp hss).2
    have hb := (abs_le.mp hsl).1
    have hc := (abs_le.mp hls).1
    have hd := (abs_le.mp hll).2
    simp only [div_eq_mul_inv] at ha hb hc hd ⊢
    linarith only [ha,hb,hc,hd]
  rw [avg_bool] at hbnd
  have hneg : 0 ≤ 𝔼 e : V, 𝔼 n, M (signedMultiplier false e) n :=
    avg_nonneg fun e => avg_nonneg fun n => sq_nonneg _
  change ((𝔼 e : V, 𝔼 n, M (signedMultiplier false e) n) +
    (𝔼 e : V, 𝔼 n, M (multiplier e) n)) / 2 ≤ _ at hbnd
  simp only [div_eq_mul_inv] at hbnd ⊢
  linarith only [hbnd,hneg]

private theorem quadratic_shift_hit {G : Type*} [AddCommGroup G] [Fintype G]
    {m : ℕ} [NeZero m] [Nonempty (Fin m)] (hm : 1 < m) (q : G)
    (f : Fin m → G → ℝ) (hf : ∀ i n, 0 ≤ f i n ∧ f i n ≤ 1)
    (g : Exponents m (m^2+m) → G → ℝ) (hg : ∀ e n, 0 ≤ g e n ∧ g e n ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hmδ : 16 / (m : ℝ) < δ^4)
    (hd : δ ≤ 𝔼 e, 𝔼 n, 𝔼 i : Fin m, g e n * f i n) :
    ∃ (e : Exponents m (m^2+m)) (n : G) (i : Fin m), 0 < g e n * f i (n + (((i.val+1)^2 * multiplier e : ℕ) : ℤ) • q) := by
  let V := Exponents m (m^2+m)
  let A (e : V) (n : G) := 𝔼 i : Choice m, f i.1 (n + (squareShift i * multiplier e) • q)
  let B (e : V) (n : G) := 𝔼 i : Choice m, f i.1 (n + (linearShift i * multiplier e) • q)
  let d (e : V) := 𝔼 n, 𝔼 i : Fin m, g e n * f i n
  have hmo : (𝔼 e, 𝔼 n, (A e n - B e n)^2) ≤ 16 / (m : ℝ) :=
    avg_shift_moment hm q f hf
  have hb : δ^2 ≤ 𝔼 e, 𝔼 n, g e n * B e n := by
    calc
      _ ≤ (𝔼 e, d e)^2 := pow_le_pow_left₀ hδ.le hd 2
      _ ≤ 𝔼 e, (d e)^2 := avg_sq d
      _ ≤ _ := by
        apply avg_le
        intro e
        unfold d B
        have he := avg_shift_lower f hf (g e) (hg e) ((multiplier e : ℤ) • q)
        simp_rw [avg_mul_left, ← mul_zsmul] at he
        simpa only [avg_mul_left] using he
  by_contra! hnone
  have hzero : (𝔼 e, 𝔼 n, g e n * A e n) = 0 := by
    unfold A
    simp_rw [← avg_mul_left]
    trans 𝔼 e : V, 𝔼 _n : G, 𝔼 _i : Choice m, (0 : ℝ)
    · apply avg_congr; intro e
      apply avg_congr; intro n
      apply avg_congr; intro i
      exact le_antisymm (hnone e n i.1) (mul_nonneg (hg e n).1 (hf _ _).1)
    · simp
  have hB : (𝔼 e, 𝔼 n, g e n * (B e n - A e n)) = 𝔼 e, 𝔼 n, g e n * B e n := by
    simp_rw [mul_sub, avg_sub, hzero, sub_zero]
  have hs := avg_cs (fun en : V × G => g en.1 en.2)
    (fun en : V × G => B en.1 en.2 - A en.1 en.2)
  have hs' :
      (𝔼 e, 𝔼 n, g e n * (B e n - A e n))^2 ≤
      (𝔼 e, 𝔼 n, (g e n)^2) * (𝔼 e, 𝔼 n, (B e n - A e n)^2) := by
    rw [avg_product (fun e n => g e n * (B e n - A e n)),
      avg_product (fun e n => (g e n)^2), avg_product (fun e n => (B e n - A e n)^2)] at hs
    exact hs
  have hAB : (𝔼 e, 𝔼 n, (B e n - A e n)^2) = 𝔼 e, 𝔼 n, (A e n - B e n)^2 := by
    apply avg_congr; intro e
    apply avg_congr; intro n
    ring
  rw [hB, hAB] at hs'
  have hg' : (𝔼 e, 𝔼 n, (g e n)^2) ≤ 1 := by
    rw [← avg_const (ι := V) (1 : ℝ)]
    apply avg_le; intro e
    rw [← avg_const (ι := G) (1 : ℝ)]
    exact avg_le fun n => by
      simpa using pow_le_pow_left₀ (hg e n).1 (hg e n).2 2
  have hnn : 0 ≤ 𝔼 e, 𝔼 n, (A e n - B e n)^2 :=
    avg_nonneg fun e => avg_nonneg fun n => sq_nonneg _
  have hsq := pow_le_pow_left₀ (sq_nonneg δ) hb 2
  have hprod := mul_le_of_le_one_left hnn hg'
  nlinarith [hsq.trans (hs'.trans (hprod.trans hmo))]

end GreenSawhneyFinite


namespace GreenSawhneyFinite

open Finset
open scoped BigOperators

private theorem pigeonhole_average {G X : Type*} [Fintype G] [Fintype X] [Nonempty X]
    {r : ℕ} [NeZero r] (w : G → ℝ) (hw : ∀ n, 0 ≤ w n)
    (color : Fin (r+1) → X → G → Fin r) (δ : ℝ) (hδ : 0 < δ)
    (havg : δ ≤ (𝔼 n, w n) / ((r+1 : ℝ)^2*r)) :
    ∃ (a b : Fin (r+1)) (c : Fin r), a < b ∧
      δ ≤ 𝔼 n, 𝔼 x : X, 𝔼 y : X, if color a x n = c ∧ color b y n = c then w n else 0 := by
  classical
  let I := Fin (r+1)
  let J := I × (I × Fin r)
  let F (n : G) (e : I → X) (j : J) :=
    if j.1 < j.2.1 ∧ color j.1 (e j.1) n = j.2.2 ∧ color j.2.1 (e j.2.1) n = j.2.2
    then w n else 0
  have hcard : (Fintype.card J : ℝ) = (r+1 : ℝ)^2*r := by
    simp [J, I, Fintype.card_prod, pow_two]
    ring
  have hpoint (n : G) (e : I → X) : w n / ((r+1 : ℝ)^2*r) ≤ 𝔼 j, F n e j := by
    have hlt : Fintype.card (Fin r) < Fintype.card I := by simp [I]
    obtain ⟨a,b,hab,he⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun a => color a (e a) n) hlt
    have hone : ∃ j : J, F n e j = w n := by
      rcases lt_or_gt_of_ne hab with hh | hh
      · refine ⟨⟨a,b,color a (e a) n⟩, ?_⟩
        dsimp [F]
        rw [if_pos ⟨hh,rfl,he.symm⟩]
      · refine ⟨⟨b,a,color a (e a) n⟩, ?_⟩
        dsimp [F]
        rw [if_pos ⟨hh,he.symm,rfl⟩]
    obtain ⟨j,hj⟩ := hone
    rw [Fintype.expect_eq_sum_div_card, ← hcard, ← hj]
    exact div_le_div_of_nonneg_right
      (Finset.single_le_sum (fun k _ => by unfold F; split_ifs; exact hw n; exact le_rfl) (mem_univ j))
      (by positivity)
  have h1 := avg_le (fun n => avg_le (fun e => hpoint n e))
  have hleft : (𝔼 n, 𝔼 _e : I → X, w n / ((r+1 : ℝ)^2*r)) =
      (𝔼 n, w n) / ((r+1 : ℝ)^2*r) := by
    simp_rw [avg_const]
    exact (Finset.expect_div _ _ _).symm
  rw [hleft, avg_swap_pair] at h1
  have h2 : δ ≤ 𝔼 j, 𝔼 n, 𝔼 e, F n e j := by
    calc
      _ ≤ _ := havg
      _ ≤ _ := by
        have hperm :
            (𝔼 e : I → X, 𝔼 j : J, 𝔼 n, F n e j) =
              (𝔼 j : J, 𝔼 n, 𝔼 e : I → X, F n e j) :=
          avg_swap_pair (fun e j n => F n e j)
        exact h1.trans_eq hperm
  obtain ⟨j,hj⟩ := avg_exists_ge h2
  have hab : j.1 < j.2.1 := by
    by_contra! h
    have hh (n : G) (e : I → X) : F n e j = 0 := by
      simp [F,h]
    simp_rw [hh, Finset.expect_const_zero] at hj
    linarith
  refine ⟨j.1,j.2.1,j.2.2,hab,?_⟩
  have he (n : G) :
      (𝔼 e : I → X, F n e j) =
        (𝔼 x : X, 𝔼 y : X, if color j.1 x n = j.2.2 ∧ color j.2.1 y n = j.2.2 then w n else 0) := by
    simp only [F, hab, true_and]
    exact avg_eval_pair hab.ne (fun x y =>
      if color j.1 x n = j.2.2 ∧ color j.2.1 y n = j.2.2 then w n else 0)
  simpa only [he] using hj

/-- Restrict the starting point to the first half of the cycle so the translated point has an ordinary integer representative. -/
private theorem first_half_avg (h : ℕ) (hh : 0 < h) :
    letI : NeZero (2*h) := ⟨by omega⟩
    (𝔼 n : ZMod (2*h), if n.val < h then (1 : ℝ) else 0) = 1/2 := by
  letI : NeZero (2*h) := ⟨by omega⟩
  let G := ZMod (2*h)
  let w (n : G) : ℝ := if n.val < h then 1 else 0
  change (𝔼 n, w n) = _
  have ha : (h : G).val = h := ZMod.val_natCast_of_lt (by omega)
  have hsum (n : G) : w n + w (n + h) = 1 := by
    have hl : n.val < 2*h := ZMod.val_lt _
    by_cases hx : n.val < h
    · have hv := ZMod.val_add_of_lt (a := n) (b := (h : G)) (by rw [ha]; omega)
      simp [w, hx, hv, ha]
    · have hv := ZMod.val_add_of_le (a := n) (b := (h : G)) (by rw [ha]; omega)
      have hlt : n.val + h - 2*h < h := by omega
      simp [w, hx, hv, ha, hlt]
  have hs := avg_congr hsum
  rw [avg_add, avg_translate (h : G), avg_const] at hs
  linarith

private theorem pin_two_coords {G E S : Type*} [Fintype G] [Fintype E] [Fintype S]
    [Nonempty E] [Nonempty S] (f : G → (E × S) → (E × S) → ℝ) (d : ℝ)
    (hd : d ≤ 𝔼 n, 𝔼 u, 𝔼 v, f n u v) :
    ∃ a : E, ∃ b : S, d ≤ 𝔼 e : E, 𝔼 n, 𝔼 i : S, f n (a,i) (e,b) := by
  have h₁ (n : G) (u : E × S) : (𝔼 v, f n u v) = 𝔼 e : E, 𝔼 b : S, f n u (e,b) :=
    avg_product (fun e b => f n u (e,b))
  simp_rw [h₁] at hd
  have h₂ (n : G) : (𝔼 u, 𝔼 e : E, 𝔼 b : S, f n u (e,b)) =
      𝔼 a : E, 𝔼 i : S, 𝔼 e : E, 𝔼 b : S, f n (a,i) (e,b) :=
    avg_product (fun a i => 𝔼 e : E, 𝔼 b : S, f n (a,i) (e,b))
  simp_rw [h₂] at hd
  rw [avg_swap] at hd
  obtain ⟨a,ha⟩ := avg_exists_ge hd
  have hs (n : G) (i : S) :
      (𝔼 e : E, 𝔼 b : S, f n (a,i) (e,b)) = 𝔼 b : S, 𝔼 e : E, f n (a,i) (e,b) :=
    avg_swap _
  simp_rw [hs] at ha
  have ht (n : G) :
      (𝔼 i : S, 𝔼 b : S, 𝔼 e : E, f n (a,i) (e,b)) =
          𝔼 b : S, 𝔼 e : E, 𝔼 i : S, f n (a,i) (e,b) := avg_swap_pair _
  simp_rw [ht] at ha
  rw [avg_swap] at ha
  obtain ⟨b,hb⟩ := avg_exists_ge ha
  rw [avg_swap] at hb
  exact ⟨a,b,hb⟩

end GreenSawhneyFinite

namespace GreenSawhneyFinite

open Finset
open scoped BigOperators

private def scale (U j : ℕ) : ℕ := U ^ (4^(j+1) : ℕ)

private theorem scale_pos {U : ℕ} (hU : 0 < U) (j : ℕ) : 0 < scale U j := by
  unfold scale
  positivity

private theorem scale_dvd {U : ℕ} (j : ℕ) : U ∣ scale U j := by
  unfold scale
  exact dvd_pow_self _ (by positivity)

/-- Successive scales provide the divisors required by both the square shift and the two fixed coordinates. -/
private theorem scale_square_dvd {U a b : ℕ} (hab : a < b) :
    U^3 * (scale U a)^2 ∣ scale U b := by
  unfold scale
  rw [← pow_mul, ← pow_add]
  apply pow_dvd_pow
  have h1 : (4 : ℕ) ^ (a+1) * 4 ≤ 4^(b+1) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (show 1 ≤ (4:ℕ) by decide) (by omega)
  have h2 : 4 ≤ (4 : ℕ) ^ (a+1) := by
    exact pow_le_pow_right₀ (show 1 ≤ (4:ℕ) by decide) (by omega : 1 ≤ a+1)
  omega

private theorem frac01 {p : Prop} [Decidable p] :
    0 ≤ (if p then (1 : ℝ) else 0) ∧ (if p then (1 : ℝ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

private theorem size_threshold {r : ℕ} (hr : 1 ≤ r)
    (m : ℕ) (hm : m = 1024*(r+1)^16)
    (δ : ℝ) (hδ : δ = 1 / (2*(r+1 : ℝ)^3)) :
    0 < δ ∧ 16/(m : ℝ) < δ^4 ∧ δ ≤ (1/2) / ((r+1 : ℝ)^2*r) := by
  let R : ℝ := (r+1 : ℝ)
  have hR : 1 ≤ R := by dsimp [R]; linarith [show 0 ≤ (r:ℝ) by positivity]
  have hRpos : 0 < R := by linarith
  have hRr : (r:ℝ) ≤ R := by dsimp [R]; linarith
  have hrpos : 0 < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  subst m
  subst δ
  change 0 < 1 / (2*R^3) ∧ 16 / ((1024*(r+1)^16 : ℕ) : ℝ) < (1/(2*R^3))^4 ∧
    1/(2*R^3) ≤ (1/2) / (R^2*r)
  refine ⟨by positivity, ?_, ?_⟩
  · have hm' : ((1024*(r+1)^16 : ℕ) : ℝ) = 1024*R^16 := by push_cast; rfl
    rw [hm']
    have he : (1/(2*R^3))^4 = 1/(16*R^12) := by
      rw [div_pow, one_pow, mul_pow, ← pow_mul]
      norm_num
    rw [he]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    have hp : R^12 ≤ R^16 := pow_le_pow_right₀ hR (by decide)
    have hpos : 0 < R^12 := by positivity
    nlinarith
  · rw [div_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    calc
      2*(R^2*(r:ℝ)) ≤ 2*(R^2*R) := by gcongr
      _ = _ := by ring

set_option maxHeartbeats 4000000 in
private theorem finite_color_bound {r : ℕ} (hr : 1 ≤ r)
    (m K U H : ℕ) (hm : m = 1024*(r+1)^16) (hK : K = m^2+m)
    (hU : U = K.factorial^m) (hH : H = U*scale U r) (χ : ℕ → Fin r) :
    ∃ x y : ℕ, 3 ≤ x ∧ 3 ≤ y ∧ x+y ≤ 3*H^4 ∧ x*y ≤ 3*H^4 ∧ χ (x+y) = χ (x*y) := by
  classical
  have hm1 : 1 < m := by
    rw [hm]
    have hs : 0 < (r+1)^16 := by positivity
    omega
  have hmr : 0 < m := by omega
  have hr' : 0 < r := by omega
  letI : NeZero m := ⟨hmr.ne'⟩
  letI : NeZero r := ⟨hr'.ne'⟩
  letI : Nonempty (Fin m) := ⟨⟨0,hmr⟩⟩
  let E := Exponents m K
  have hUdiv : K.factorial ∣ U := by rw [hU]; exact dvd_pow_self _ hmr.ne'
  have hKU : K ≤ U := (Nat.self_le_factorial K).trans (Nat.le_of_dvd (by rw [hU]; positivity) hUdiv)
  have hmK : m^2 ≤ K := by rw [hK]; omega
  have h3U : 3 ≤ U := by
    have hsq : m ≤ m^2 := by nlinarith
    have hm3 : 3 ≤ K := by have := Nat.le_add_right m m; rw [hK]; nlinarith
    exact hm3.trans hKU
  have hUpos : 0 < U := by omega
  have hUpow : U ≤ H := by
    rw [hH]
    have h := scale_pos hUpos r
    exact Nat.le_mul_of_pos_right _ h
  have hHpos : 0 < H := by omega
  have h3H3 : 3 ≤ H^3 := by
    calc
      3 ≤ H := by omega
      _ ≤ H^3 := by exact Nat.le_self_pow (by decide : 3 ≠ 0) _
  let I := H^3
  have hIpos : 0 < I := by dsimp [I]; positivity
  letI : NeZero (2*I) := ⟨by omega⟩
  let G := ZMod (2*I)
  let nNat (n : G) := I+n.val
  let w (n : G) : ℝ := if n.val < I then 1 else 0
  let δ : ℝ := 1/(2*(r+1 : ℝ)^3)
  obtain ⟨hδ,hmδ,hδavg⟩ := size_threshold hr m hm δ rfl
  have hkeep : (𝔼 n : G, w n) = 1/2 := first_half_avg I hIpos
  have hdivS (i : Fin m) : i.val+1 ∣ U := by
    exact (Nat.dvd_factorial (by omega) (by nlinarith [i.isLt])).trans hUdiv
  have hdivU (e : E) : multiplier e ∣ U := by rw [hU]; exact multiplier_dvd e
  have hmulU (e : E) : multiplier e ≤ U := Nat.le_of_dvd hUpos (hdivU e)
  have hL (j : Fin (r+1)) : scale U j.val ≤ scale U r := by
    unfold scale
    exact pow_le_pow_right₀ (by omega) (pow_le_pow_right₀ (by decide) (by have := j.isLt; omega))
  let C (j : Fin (r+1)) (v : E × Fin m) (n : G) :=
    χ (scale U j.val * multiplier v.1 / (v.2.val+1) * nNat n)
  obtain ⟨a,b,c,hab,hd⟩ := pigeonhole_average w (fun n => (frac01 : 0 ≤ w n ∧ w n ≤ 1).1) C δ hδ
    (by rwa [hkeep])
  obtain ⟨e₀,s₀,hpinned⟩ :=
    pin_two_coords (fun n u v => if C a u n = c ∧ C b v n = c then w n else 0) δ hd
  let A := scale U a.val * multiplier e₀
  have hA0 : 0 < A := Nat.mul_pos (scale_pos hUpos _) (multiplier_pos e₀)
  have hUA : U ∣ A := dvd_mul_of_dvd_left (scale_dvd a.val) _
  have h3A := h3U.trans (Nat.le_of_dvd hA0 hUA)
  let sb := s₀.val+1
  have hsb : 0 < sb := by dsimp [sb]; positivity
  have hab' : a.val < b.val := hab
  have hdvd : sb*A^2 ∣ scale U b.val := by
    have h1 : sb * (multiplier e₀)^2 ∣ U^3 := by
      rw [show U^3 = U*U^2 by ring]
      exact mul_dvd_mul (hdivS s₀) (pow_dvd_pow_of_dvd (hdivU e₀) 2)
    have h2 := mul_dvd_mul_right h1 ((scale U a.val)^2)
    apply dvd_trans _ (scale_square_dvd hab')
    convert h2 using 1
    dsimp [A]
    ring
  obtain ⟨q,hq⟩ := hdvd
  have hq0 : 0 < q := by
    have hb := scale_pos hUpos b.val
    by_contra! hz
    have : q = 0 := by omega
    simp [hq,this] at hb
  have hqH : q ≤ H := by
    apply le_trans (Nat.le_of_dvd (scale_pos hUpos _) ⟨sb*A^2, by rw [hq]; ring⟩)
    rw [hH]
    exact (hL b).trans (Nat.le_mul_of_pos_left _ hUpos)
  let f (i : Fin m) (n : G) : ℝ :=
    if χ (A / (i.val+1) * nNat n) = c then 1 else 0
  let g (e : E) (n : G) : ℝ :=
    if n.val < I ∧ χ (A^2*q*multiplier e*nNat n) = c then 1 else 0
  have hCb (e : E) (n : G) : C b (e,s₀) n = χ (A^2*q*multiplier e*nNat n) := by
    dsimp [C]
    change χ (scale U b.val * multiplier e / sb * nNat n) = _
    rw [hq, show sb*A^2*q*multiplier e = sb*(A^2*q*multiplier e) by ring, Nat.mul_div_cancel_left _ hsb]
  have hpin : δ ≤ 𝔼 e : E, 𝔼 n, 𝔼 i : Fin m, g e n * f i n := by
    apply hpinned.trans_eq
    apply avg_congr; intro e
    apply avg_congr; intro n
    apply avg_congr; intro i
    rw [hCb]
    have hCa : C a (e₀,i) n = χ (A / (i.val+1) * nNat n) := rfl
    rw [hCa]
    dsimp [w,f,g]
    by_cases ha : χ (A / (i.val + 1) * nNat n) = c <;>
      by_cases hb : χ (A ^ 2 * q * multiplier e * nNat n) = c <;>
      by_cases hn : n.val < I <;> simp [ha,hb,hn]
  subst K
  obtain ⟨e,n,i,hhit⟩ := quadratic_shift_hit hm1 (q : G) f
    (fun i n => frac01) g (fun e n => frac01) δ hδ hmδ hpin
  let s := i.val+1
  let u := multiplier e
  let d := s^2*u*q
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hu0 : 0 < u := multiplier_pos e
  have hden : s ∣ A := (hdivS i).trans hUA
  have hdiv : (A/s)*s = A := Nat.div_mul_cancel hden
  have hdiv0 : 0 < A/s := Nat.div_pos (Nat.le_of_dvd hA0 hden) hs0
  have hs2U : s^2 ≤ U := (pow_le_pow_left₀ (Nat.zero_le _) (by dsimp [s]; have := i.isLt; omega) 2).trans (hmK.trans hKU)
  have huU : u ≤ U := hmulU e
  have hdI : d ≤ I := by
    change s^2*u*q ≤ H^3
    calc
      _ ≤ U*U*H := Nat.mul_le_mul (Nat.mul_le_mul hs2U huU) hqH
      _ ≤ H*H*H := Nat.mul_le_mul_right _ (Nat.mul_le_mul hUpow hUpow)
      _ = _ := by ring
  have hzsmul :
      (((i.val+1)^2 * multiplier e : ℕ) : ℤ) • (q : G) = (d : G) := by
    rw [natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul]
  rw [hzsmul] at hhit
  have hg1 : n.val < I ∧ χ (A^2*q*u*nNat n) = c := by
    by_contra h
    have hz : g e n = 0 := if_neg h
    rw [hz, zero_mul] at hhit
    exact lt_irrefl _ hhit
  have hf1 : χ (A / s * nNat (n+d)) = c := by
    by_contra h
    have hz : f i (n+d) = 0 := if_neg h
    rw [hz, mul_zero] at hhit
    exact lt_irrefl _ hhit
  have hval : (n+(d : G)).val = n.val+d := by
    have hdlt : d < 2*I := by omega
    have hvd : (d : G).val = d := ZMod.val_natCast_of_lt hdlt
    rw [ZMod.val_add_of_lt]
    · rw [hvd]
    · rw [hvd]
      have := hg1.1; omega
  let x := A/s*nNat n
  let y := A*s*u*q
  have heAdd : x+y = A/s*nNat (n+d) := by
    dsimp [x,y,nNat]
    rw [hval]
    have he : A / s * d = A*s*u*q := by
      dsimp [d]
      calc
        _ = (A/s*s)*s*u*q := by ring
        _ = _ := by rw [hdiv]
    rw [← he]
    ring
  have heMul : x*y = A^2*q*u*nNat n := by
    dsimp [x,y]
    calc
      _ = (A/s*s)*A*q*u*nNat n := by ring
      _ = _ := by rw [hdiv]; ring
  have hAs : A/s ≤ H := by
    calc
      _ ≤ A := Nat.div_le_self _ _
      _ ≤ scale U r * U := Nat.mul_le_mul (hL a) (hmulU e₀)
      _ = H := by rw [hH]; ring
  have hbc : A^2*q*u ≤ H := by
    have he : A^2*q*u = scale U b.val*u/sb := by
      rw [hq, show sb*A^2*q*u = sb*(A^2*q*u) by ring, Nat.mul_div_cancel_left _ hsb]
    rw [he]
    calc
      _ ≤ scale U b.val*u := Nat.div_le_self _ _
      _ ≤ scale U r*U := Nat.mul_le_mul (hL b) huU
      _ = H := by rw [hH]; ring
  have hx3 : 3 ≤ x := by
    apply h3H3.trans
    change I ≤ A/s*(I+n.val)
    exact (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ hdiv0)
  have hy3 : 3 ≤ y := by
    apply h3A.trans
    change A ≤ A*s*u*q
    rw [show A*s*u*q = A*(s*u*q) by ring]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hxsum : x+y ≤ 3*H^4 := by
    rw [heAdd]
    have hh : nNat (n+d) ≤ 3*I := by dsimp [nNat]; rw [hval]; have := hg1.1; omega
    exact (Nat.mul_le_mul hAs hh).trans_eq (by dsimp [I]; ring)
  have hxprod : x*y ≤ 3*H^4 := by
    rw [heMul]
    have hh : nNat n ≤ 3*I := by dsimp [nNat]; have := hg1.1; omega
    exact (Nat.mul_le_mul hbc hh).trans_eq (by dsimp [I]; ring)
  refine ⟨x,y,hx3,hy3,hxsum,hxprod,?_⟩
  rw [heAdd,heMul]
  exact hf1.trans hg1.2.symm

end GreenSawhneyFinite


namespace GreenSawhneyFinite

open Finset Filter
open scoped BigOperators

private theorem self_le_exp (x : ℝ) : x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

private theorem factorial_pow_exp (k m : ℕ) :
    (((k.factorial^m : ℕ)) : ℝ) ≤ Real.exp ((m:ℝ)*(k:ℝ)^2) := by
  have hfac : (k.factorial:ℝ) ≤ (k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
  rw [Nat.cast_pow]
  calc
    _ ≤ ((k:ℝ)^k)^m := pow_le_pow_left₀ (by positivity) hfac m
    _ ≤ (Real.exp (k:ℝ)^k)^m :=
      pow_le_pow_left₀ (pow_nonneg (by positivity) k)
        (pow_le_pow_left₀ (by positivity) (self_le_exp (k:ℝ)) k) m
    _ = _ := by
      rw [← Real.exp_nat_mul (k:ℝ) k, ← Real.exp_nat_mul ((k:ℝ)*(k:ℝ)) m]
      congr 1
      ring

private theorem exp_major (u L : ℝ) (j : ℕ) (hu0 : 0 ≤ u) (hu : u ≤ Real.exp L) :
    3*(u^(j+1))^4 ≤ Real.exp (3+4*((j:ℝ)+1)*L) := by
  have hpow : u^(j+1) ≤ Real.exp L^(j+1) := pow_le_pow_left₀ hu0 hu (j+1)
  have hpow0 : 0 ≤ u^(j+1) := pow_nonneg hu0 _
  have hpow4 : (u^(j+1))^4 ≤ (Real.exp L^(j+1))^4 := pow_le_pow_left₀ hpow0 hpow 4
  have hpow40 : 0 ≤ (u^(j+1))^4 := pow_nonneg hpow0 4
  calc
    _ ≤ Real.exp 3 * (Real.exp L^(j+1))^4 :=
      mul_le_mul (self_le_exp 3) hpow4 hpow40 (Real.exp_nonneg 3)
    _ = _ := by
      rw [← Real.exp_nat_mul L (j+1), ← Real.exp_nat_mul (((j+1:ℕ):ℝ)*L) 4, ← Real.exp_add]
      congr 1
      push_cast
      ring

private theorem pow_le_exp_mul (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    x^j ≤ Real.exp ((j:ℝ)*x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hx (self_le_exp x) j

set_option maxHeartbeats 900000 in
private theorem compare_bounds {r m K U H : ℕ} (hr : 1024 ≤ r)
    (hm : m = 1024*(r+1)^16) (hK : K = m^2+m)
    (hU : U = K.factorial^m) (hH : H = U*scale U r) :
    ((3*H^4 : ℕ) : ℝ) ≤ Green22.GreenSawhneyBound r := by
  let R : ℝ := (r : ℝ)+1
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [show 0 ≤ (r:ℝ) by positivity]
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hr0 : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
  have hR : 1024 ≤ R := by
    have hh : (1024 : ℝ) ≤ r := by exact_mod_cast hr
    dsimp [R]; linarith
  have hmR : (m : ℝ) ≤ R^17 := by
    rw [hm]
    push_cast
    change 1024 * R^16 ≤ R^17
    rw [pow_succ' R 16]
    exact mul_le_mul_of_nonneg_right hR (pow_nonneg hR0 16)
  have hKR : (K : ℝ) ≤ R^35 := by
    rw [hK]
    push_cast
    have hm1 : (1:ℝ) ≤ m := by
      have hh : 0 < m := by rw [hm]; positivity
      have hh' : 1 ≤ m := by omega
      exact_mod_cast hh'
    have hm2 : (m:ℝ) ≤ (m:ℝ)^2 := by
      nlinarith only [mul_nonneg hm0 (sub_nonneg.mpr hm1)]
    calc
      _ ≤ 2*(m:ℝ)^2 := by linarith
      _ ≤ R*(R^17)^2 := mul_le_mul (by linarith only [hR])
        (pow_le_pow_left₀ hm0 hmR 2) (sq_nonneg (m:ℝ)) hR0
      _ = _ := by rw [← pow_mul]; exact (pow_succ' R 34).symm
  have hmk : (m:ℝ) * (K:ℝ)^2 ≤ R^87 := by
    calc
      _ ≤ R^17*(R^35)^2 := by
        have hn : (K:ℝ)^2 ≤ (R^35)^2 := pow_le_pow_left₀ hK0 hKR 2
        exact mul_le_mul hmR hn (sq_nonneg (K:ℝ)) (pow_nonneg hR0 17)
      _ = _ := by rw [← pow_mul, ← pow_add]
  have hUbound : (U:ℝ) ≤ Real.exp (R^87) := by
    rw [hU]
    exact (factorial_pow_exp K m).trans (Real.exp_le_exp.mpr hmk)
  let J : ℕ := (4 : ℕ)^(r+1)
  have hJpos : 1 ≤ J := by
    have hj : 0 < J := by dsimp [J]; positivity
    omega
  have hH' : H = U^(J+1) := by rw [hH]; exact (pow_succ' U J).symm
  have hmajor : ((3*H^4 : ℕ) : ℝ) ≤ Real.exp (3+4*((J:ℝ)+1)*R^87) := by
    rw [Nat.cast_mul, Nat.cast_pow, hH', Nat.cast_pow]
    exact exp_major (U:ℝ) (R^87) J (Nat.cast_nonneg U) hUbound
  have h4 : (4:ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3:ℝ)]
  have hJ : (J:ℝ) ≤ Real.exp (3*R) := by
    dsimp [J]
    push_cast
    calc
      _ ≤ Real.exp 3 ^ (r+1) := pow_le_pow_left₀ (by norm_num) h4 (r+1)
      _ = _ := by rw [← Real.exp_nat_mul]; dsimp [R]; push_cast; ring_nf
  have hpol : R^87 ≤ Real.exp (87*R) := pow_le_exp_mul R hR0 87
  have h16 : (16:ℝ) ≤ Real.exp 6 := by
    calc
      16 = (4:ℝ)^2 := by norm_num
      _ ≤ Real.exp 3 ^ 2 := pow_le_pow_left₀ (by norm_num) h4 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hj1 : (1:ℝ) ≤ (J:ℝ) := by exact_mod_cast hJpos
  have hJR : (1:ℝ) ≤ (J:ℝ)*R^87 :=
    one_le_mul_of_one_le_of_one_le hj1 (one_le_pow₀ hR1)
  have hcoeff : 3 + 4*((J:ℝ)+1)*R^87 ≤ 16*(J:ℝ)*R^87 := by
    have hle : R^87 ≤ (J:ℝ)*R^87 :=
      le_mul_of_one_le_left (pow_nonneg hR0 87) hj1
    nlinarith only [hJR,hle]
  have hlast : 3+4*((J:ℝ)+1)*R^87 ≤ Real.exp ((r:ℝ)^50) := by
    calc
      _ ≤ _ := hcoeff
      _ ≤ Real.exp 6 * Real.exp (3*R) * Real.exp (87*R) := by
        have hfirst : (16:ℝ)*(J:ℝ) ≤ Real.exp 6 * Real.exp (3*R) :=
          mul_le_mul h16 hJ (Nat.cast_nonneg J) (Real.exp_nonneg 6)
        exact mul_le_mul hfirst hpol (pow_nonneg hR0 87)
          (mul_nonneg (Real.exp_nonneg 6) (Real.exp_nonneg (3*R)))
      _ = Real.exp (6+90*R) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hrr : (1024:ℝ) ≤ r := by exact_mod_cast hr
        have hr1 : (1:ℝ) ≤ r := by linarith
        have hsq : (r:ℝ)^2 ≤ (r:ℝ)^50 := pow_le_pow_right₀ hr1 (by decide)
        dsimp [R]
        nlinarith only [hrr, hsq, mul_nonneg hr0 (sub_nonneg.mpr hrr)]
  exact hmajor.trans (Real.exp_le_exp.mpr hlast)

end GreenSawhneyFinite

open Filter

set_option maxHeartbeats 3000000 in
theorem OMA.solution : type_of% @Green22.green_22.variants.green_sawhney_bound := by
  classical
  change ∀ᶠ r : ℕ in atTop, (Green22.N₀ r : ℝ) ≤ Green22.GreenSawhneyBound r
  filter_upwards [eventually_ge_atTop (1024 : ℕ)] with r hr
  let m := 1024*(r+1)^16
  let K := m^2+m
  let U := K.factorial^m
  let H := U*GreenSawhneyFinite.scale U r
  let N := 3*H^4
  have hr1 : 1 ≤ r := by omega
  have hgood : ∀ c : Finset.Icc 1 N → Fin r, Green22.HasMonochromaticSumProduct N r c := by
    intro c
    let χ (t : ℕ) : Fin r := if ht : t ∈ Finset.Icc 1 N then c ⟨t,ht⟩ else ⟨0,by omega⟩
    obtain ⟨x,y,hx,hy,hs,hp,hc⟩ := GreenSawhneyFinite.finite_color_bound hr1 m K U H rfl rfl rfl rfl χ
    have hsum : x+y ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega,hs⟩
    have hprod : x*y ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by
      have hxy : 0 < x*y := Nat.mul_pos (by omega) (by omega)
      omega,hp⟩
    refine ⟨x,y,hx,hy,hsum,hprod,?_⟩
    have he₁ : χ (x+y) = c ⟨x+y,hsum⟩ := dif_pos hsum
    have he₂ : χ (x*y) = c ⟨x*y,hprod⟩ := dif_pos hprod
    rwa [he₁,he₂] at hc
  have hN : Green22.N₀ r ≤ N := Nat.sInf_le hgood
  exact (show (Green22.N₀ r : ℝ) ≤ (N : ℝ) by exact_mod_cast hN).trans
    (GreenSawhneyFinite.compare_bounds hr rfl rfl rfl rfl)
