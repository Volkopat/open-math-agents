import OMAReductions.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1
import Mathlib

-- Problem: Step H2 of Erdos10.erdos_10.variants.gallagher.R1.H2.R1.H1.R1
-- Credit: @Aijy0264561
-- Gallagher's singular series average over block binary sums: G_R has mean 1 on ZMod P
-- (Chinese remainder theorem), Fourier on ZMod P bounds the pair sum by |Q|^2 plus P times
-- the largest nontrivial exponential sum squared, and those sums factor into k block sums
-- each at most l*B + 2 with l < 1, since |e(y) + e(2y)| < 2 for y nonzero.

open Finset Filter Real
open scoped Classical

namespace OMA.Gallagher.H2proof

/-- The local factor of the truncated singular series at `p`. -/
noncomputable def fp (p n : ℕ) : ℝ :=
  if p ∣ n then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2

def Pset (R : ℕ) : Finset ℕ := (Finset.range (R+1)).filter (fun p => p.Prime ∧ 2 < p)

noncomputable def GG (R d : ℕ) : ℝ := ∏ p ∈ Pset R, fp p d

def PP (R : ℕ) : ℕ := ∏ p ∈ Pset R, p

lemma mem_Pset {R p : ℕ} (h : p ∈ Pset R) : p.Prime ∧ 2 < p := (mem_filter.1 h).2

lemma fp_nonneg {p : ℕ} (hp : 2 < p) (n : ℕ) : 0 ≤ fp p n := by
  have h : (2:ℝ) < p := by exact_mod_cast hp
  unfold fp; split_ifs
  · apply div_nonneg <;> linarith
  · apply div_nonneg
    · apply mul_nonneg <;> linarith
    · positivity

lemma GG_nonneg (R d : ℕ) : 0 ≤ GG R d :=
  prod_nonneg fun p hp => fp_nonneg (mem_Pset hp).2 d

lemma PP_pos (R : ℕ) : 0 < PP R :=
  prod_pos fun p hp => (mem_Pset hp).1.pos

/-- Sums over `range (a*b)` of a product of an `a`-periodic and a `b`-periodic
function factor, for coprime `a`, `b` (Chinese remainder theorem). -/
lemma crt_sum {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a.Coprime b) (F H : ℕ → ℝ)
    (hF : ∀ x, F x = F (x % a)) (hH : ∀ x, H x = H (x % b)) :
    ∑ x ∈ range (a*b), F x * H x = (∑ x ∈ range a, F x) * ∑ y ∈ range b, H y := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun xy => (Nat.chineseRemainder h xy.1 xy.2 : ℕ))
    (fun x => (x % a, x % b))
  · intro xy _
    exact mem_range.2 (Nat.chineseRemainder_lt_mul h _ _ ha.ne' hb.ne')
  · intro x _
    exact mem_product.2 ⟨mem_range.2 (Nat.mod_lt _ ha), mem_range.2 (Nat.mod_lt _ hb)⟩
  · intro xy hxy
    obtain ⟨h1, h2⟩ := mem_product.1 hxy
    have c := (Nat.chineseRemainder h xy.1 xy.2).2
    have e1 : (Nat.chineseRemainder h xy.1 xy.2 : ℕ) % a = xy.1 := by
      rw [c.1]; exact Nat.mod_eq_of_lt (mem_range.1 h1)
    have e2 : (Nat.chineseRemainder h xy.1 xy.2 : ℕ) % b = xy.2 := by
      rw [c.2]; exact Nat.mod_eq_of_lt (mem_range.1 h2)
    simp only [e1, e2]
  · intro x hx
    have c := (Nat.chineseRemainder h (x % a) (x % b)).2
    have m1 : (Nat.chineseRemainder h (x % a) (x % b) : ℕ) ≡ x [MOD a] :=
      c.1.trans (Nat.mod_modEq x a)
    have m2 : (Nat.chineseRemainder h (x % a) (x % b) : ℕ) ≡ x [MOD b] :=
      c.2.trans (Nat.mod_modEq x b)
    have m := (Nat.modEq_and_modEq_iff_modEq_mul h).1 ⟨m1, m2⟩
    exact Nat.ModEq.eq_of_lt_of_lt m (Nat.chineseRemainder_lt_mul h _ _ ha.ne' hb.ne')
      (mem_range.1 hx)
  · intro xy hxy
    obtain ⟨h1, h2⟩ := mem_product.1 hxy
    have c := (Nat.chineseRemainder h xy.1 xy.2).2
    have e1 : (Nat.chineseRemainder h xy.1 xy.2 : ℕ) % a = xy.1 := by
      rw [c.1]; exact Nat.mod_eq_of_lt (mem_range.1 h1)
    have e2 : (Nat.chineseRemainder h xy.1 xy.2 : ℕ) % b = xy.2 := by
      rw [c.2]; exact Nat.mod_eq_of_lt (mem_range.1 h2)
    rw [hF (Nat.chineseRemainder h xy.1 xy.2 : ℕ), hH (Nat.chineseRemainder h xy.1 xy.2 : ℕ),
      e1, e2]

lemma fp_sum {p : ℕ} (hp : 2 < p) : ∑ x ∈ range p, fp p x = p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hrest : ∀ i ∈ range q, fp (q+1) (i+1) = ((q+1:ℕ):ℝ)*(((q+1:ℕ):ℝ)-2)/(((q+1:ℕ):ℝ)-1)^2 := by
    intro i hi
    have hi' := mem_range.1 hi
    unfold fp
    rw [if_neg]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  rw [Finset.sum_congr rfl hrest, sum_const, card_range]
  unfold fp
  rw [if_pos (dvd_zero _)]
  have hq : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  push_cast
  rw [nsmul_eq_mul]
  have e1 : (q:ℝ)+1-1 = q := by ring
  have e2 : (q:ℝ)+1-2 = q-1 := by ring
  rw [e1, e2]
  have hq0 : (q:ℝ) ≠ 0 := by linarith
  field_simp
  ring

lemma mean_prod (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ 2 < p) :
    ∑ x ∈ range (∏ p ∈ T, p), ∏ p ∈ T, fp p x = ∏ p ∈ T, (p:ℝ) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert q T hq ih =>
    have hqT := hT q (mem_insert_self q T)
    have hT' : ∀ p ∈ T, p.Prime ∧ 2 < p := fun p hp => hT p (mem_insert_of_mem hp)
    rw [prod_insert hq, prod_insert hq]
    simp_rw [prod_insert hq]
    have hpos : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (hT' p hp).1.pos
    have hcop : q.Coprime (∏ p ∈ T, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hqT.1 (hT' p hp).1).2 (fun h => hq (h ▸ hp))
    rw [crt_sum hqT.1.pos hpos hcop (fp q) (fun x => ∏ p ∈ T, fp p x)]
    · rw [fp_sum hqT.2, ih hT']
    · intro x; unfold fp
      simp only [Nat.dvd_mod_iff (dvd_refl q)]
    · intro x
      apply prod_congr rfl
      intro p hp
      unfold fp
      simp only [Nat.dvd_mod_iff (dvd_prod_of_mem (fun p : ℕ => p) hp)]

lemma sum_zmod_val {N : ℕ} [NeZero N] (F : ℕ → ℝ) :
    ∑ x : ZMod N, F x.val = ∑ n ∈ range N, F n := by
  apply Finset.sum_nbij' (fun x : ZMod N => x.val) (fun n => (n : ZMod N))
  · intro x _; exact mem_range.2 (ZMod.val_lt x)
  · intro n _; exact mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro n hn; exact ZMod.val_cast_of_lt (mem_range.1 hn)
  · intro x _; rfl

lemma mean_GG (R : ℕ) [NeZero (PP R)] :
    ∑ x : ZMod (PP R), GG R x.val = (PP R : ℝ) := by
  rw [sum_zmod_val (GG R)]
  unfold GG PP
  rw [mean_prod (Pset R) (fun p hp => mem_Pset hp)]
  push_cast; rfl

lemma dvd_dist_iff {p N : ℕ} [NeZero N] (hp : p ∣ N) (a b : ℕ) :
    p ∣ Nat.dist a b ↔ p ∣ (((a : ZMod N) - (b : ZMod N)).val) := by
  have e1 : p ∣ (((a : ZMod N) - (b : ZMod N)).val) ↔
      ((((a : ZMod N) - (b : ZMod N)).val : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).symm
  have e2 : ((((a : ZMod N) - (b : ZMod N)).val : ℕ) : ZMod p) =
      ZMod.castHom hp (ZMod p) ((a : ZMod N) - (b : ZMod N)) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [e1, e2, map_sub, map_natCast, map_natCast, sub_eq_zero, ZMod.natCast_eq_natCast_iff]
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.modEq_iff_dvd' h]
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, ← Nat.modEq_iff_dvd' h]
    exact ⟨fun h' => h'.symm, fun h' => h'.symm⟩

lemma GG_dist (R a b : ℕ) [NeZero (PP R)] :
    GG R (Nat.dist a b) = GG R (((a : ZMod (PP R)) - (b : ZMod (PP R))).val) := by
  unfold GG
  apply prod_congr rfl
  intro p hp
  unfold fp
  simp only [dvd_dist_iff (N := PP R) (dvd_prod_of_mem (fun p : ℕ => p) hp) a b]

lemma norm_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

lemma char_sum {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (f : ι → ZMod N) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- Fourier bound on `ZMod N`: a nonnegative `g` summed over all differences of a
family is at most its mean times `|S|²` plus `(∑ g)` times the largest nontrivial
exponential sum squared. -/
lemma fourier_bound {N : ℕ} [NeZero N] (g : ZMod N → ℝ) (hg : ∀ x, 0 ≤ g x)
    {ι : Type*} (S : Finset ι) (a : ι → ZMod N) (Mx : ℝ)
    (hM : ∀ m : ZMod N, m ≠ 0 → ‖∑ t ∈ S, ZMod.stdAddChar (m * a t)‖ ≤ Mx) :
    ∑ t ∈ S, ∑ u ∈ S, g (a t - a u) ≤
      (∑ x, g x) / N * (S.card:ℝ)^2 + (∑ x, g x) * Mx^2 := by
  have hN : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set gh : ZMod N → ℂ := fun m => ∑ x, (g x : ℂ) * ZMod.stdAddChar (-(m * x))
  set Sm : ZMod N → ℂ := fun m => ∑ t ∈ S, ZMod.stdAddChar (m * a t)
  have inv : ∀ y, (N:ℂ) * (g y : ℂ) = ∑ m, gh m * ZMod.stdAddChar (m * y) := by
    intro y
    have : ∑ m, gh m * ZMod.stdAddChar (m * y) =
        ∑ x, (g x : ℂ) * ∑ m, ZMod.stdAddChar (m * (y - x)) := by
      simp only [gh, sum_mul, mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro m _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2; ring
    rw [this]
    simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N), sub_eq_zero]
    simp only [ZMod.card]
    have hx : ∀ x, (g x : ℂ) * ((if y = x then N else 0 : ℕ) : ℂ) =
        if y = x then (g x : ℂ) * N else 0 := by
      intro x; split_ifs <;> simp
    rw [sum_congr rfl (fun x _ => hx x), Finset.sum_ite_eq]
    simp only [mem_univ, if_true]
    ring
  have key : (N:ℂ) * ((∑ t ∈ S, ∑ u ∈ S, g (a t - a u) : ℝ) : ℂ) =
      ∑ m, gh m * (Sm m * Sm (-m)) := by
    calc (N:ℂ) * ((∑ t ∈ S, ∑ u ∈ S, g (a t - a u) : ℝ) : ℂ)
        = ∑ t ∈ S, ∑ u ∈ S, (N:ℂ) * (g (a t - a u) : ℂ) := by
          push_cast; rw [mul_sum]; simp_rw [mul_sum]
      _ = ∑ t ∈ S, ∑ u ∈ S, ∑ m, gh m *
            (ZMod.stdAddChar (m * a t) * ZMod.stdAddChar (-m * a u)) := by
          apply sum_congr rfl; intro t _
          apply sum_congr rfl; intro u _
          rw [inv]
          apply sum_congr rfl; intro m _
          rw [← AddChar.map_add_eq_mul]
          congr 2; ring
      _ = ∑ t ∈ S, ∑ m, ∑ u ∈ S, gh m *
            (ZMod.stdAddChar (m * a t) * ZMod.stdAddChar (-m * a u)) := by
          apply sum_congr rfl; intro t _
          exact Finset.sum_comm
      _ = ∑ m, ∑ t ∈ S, ∑ u ∈ S, gh m *
            (ZMod.stdAddChar (m * a t) * ZMod.stdAddChar (-m * a u)) := Finset.sum_comm
      _ = ∑ m, gh m * (Sm m * Sm (-m)) := by
          apply sum_congr rfl; intro m _
          simp only [Sm]
          rw [sum_mul_sum, mul_sum]
          simp_rw [mul_sum]
  -- split off m = 0
  have h0 : gh 0 * (Sm 0 * Sm (-0)) = (((∑ x, g x) * (S.card:ℝ)^2 : ℝ) : ℂ) := by
    simp only [gh, Sm, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one, sum_const,
      nsmul_eq_mul]
    push_cast; ring
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod N)), h0] at key
  set E := ∑ m ∈ univ.erase (0 : ZMod N), gh m * (Sm m * Sm (-m))
  have hgh : ∀ m, ‖gh m‖ ≤ ∑ x, g x := by
    intro m
    calc ‖gh m‖ ≤ ∑ x, ‖(g x : ℂ) * ZMod.stdAddChar (-(m * x))‖ := norm_sum_le _ _
      _ = ∑ x, g x := by
        apply sum_congr rfl; intro x _
        rw [norm_mul, norm_stdAddChar, mul_one, Complex.norm_real, Real.norm_of_nonneg (hg x)]
  have hE : ‖E‖ ≤ N * ((∑ x, g x) * Mx^2) := by
    calc ‖E‖ ≤ ∑ m ∈ univ.erase (0 : ZMod N), ‖gh m * (Sm m * Sm (-m))‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ univ.erase (0 : ZMod N), (∑ x, g x) * Mx^2 := by
        apply sum_le_sum; intro m hm
        have hm0 : m ≠ 0 := ne_of_mem_erase hm
        have h1 := hM m hm0
        have h2 := hM (-m) (neg_ne_zero.2 hm0)
        have hMx : 0 ≤ Mx := le_trans (norm_nonneg _) h1
        rw [norm_mul, norm_mul]
        have hs0 : 0 ≤ ∑ x, g x := sum_nonneg fun x _ => hg x
        calc ‖gh m‖ * (‖Sm m‖ * ‖Sm (-m)‖) ≤ (∑ x, g x) * (Mx * Mx) :=
              mul_le_mul (hgh m) (mul_le_mul h1 h2 (norm_nonneg _) hMx)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs0
          _ = (∑ x, g x) * Mx^2 := by ring
      _ = ((univ.erase (0 : ZMod N)).card : ℝ) * ((∑ x, g x) * Mx^2) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ N * ((∑ x, g x) * Mx^2) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (sum_nonneg fun x _ => hg x) (sq_nonneg _))
        have : (univ.erase (0 : ZMod N)).card ≤ N := by
          rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]; omega
        exact_mod_cast this
  set L := ∑ t ∈ S, ∑ u ∈ S, g (a t - a u)
  have hre : (N:ℝ) * L = (∑ x, g x) * (S.card:ℝ)^2 + E.re := by
    have hk := congrArg Complex.re key
    have e1 : ((N:ℂ) * ((L:ℝ):ℂ)).re = (N:ℝ) * L := by simp
    have e2 : ((((∑ x, g x) * (S.card:ℝ)^2 : ℝ) : ℂ) + E).re =
        (∑ x, g x) * (S.card:ℝ)^2 + E.re := by rw [Complex.add_re, Complex.ofReal_re]
    rw [e1, e2] at hk
    exact hk
  have hEre : E.re ≤ ‖E‖ := Complex.re_le_norm E
  have : (N:ℝ) * L ≤ (N:ℝ) * ((∑ x, g x) / N * (S.card:ℝ)^2 + (∑ x, g x) * Mx^2) := by
    rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hN.ne']
    linarith
  exact le_of_mul_le_mul_left this hN

lemma norm_one_add_lt {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) : ‖1 + z‖ < 2 := by
  have hn : z.re^2 + z.im^2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith
  have hn2 : ‖1 + z‖^2 = 2 + 2 * z.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp; nlinarith
  by_contra hc
  push Not at hc
  have h4 : (4:ℝ) ≤ ‖1+z‖^2 := by nlinarith [norm_nonneg (1+z)]
  have hre : z.re = 1 := by
    have : z.re ≤ 1 := by nlinarith [sq_nonneg z.im]
    linarith
  have him : z.im = 0 := by nlinarith
  exact h1 (Complex.ext (by simp [hre]) (by simp [him]))

lemma pair_strict {N : ℕ} [NeZero N] {y : ZMod N} (hy : y ≠ 0) :
    ‖ZMod.stdAddChar y + ZMod.stdAddChar (2*y)‖ < 2 := by
  have e : ZMod.stdAddChar (2*y) = ZMod.stdAddChar y * ZMod.stdAddChar y := by
    rw [two_mul, AddChar.map_add_eq_mul]
  rw [e, show ZMod.stdAddChar y + ZMod.stdAddChar y * ZMod.stdAddChar y =
    ZMod.stdAddChar y * (1 + ZMod.stdAddChar y) by ring, norm_mul, norm_stdAddChar, one_mul]
  apply norm_one_add_lt (norm_stdAddChar y)
  intro h
  apply hy
  apply ZMod.injective_stdAddChar
  rw [h, AddChar.map_zero_eq_one]

lemma pair_bound (N : ℕ) [NeZero N] : ∃ l : ℝ, 0 ≤ l ∧ l < 1 ∧
    ∀ y : ZMod N, y ≠ 0 → ‖ZMod.stdAddChar y + ZMod.stdAddChar (2*y)‖ ≤ 2*l := by
  by_cases hne : (univ.filter (fun y : ZMod N => y ≠ 0)).Nonempty
  · obtain ⟨y₀, hy₀, hmax⟩ := exists_max_image _
      (fun y : ZMod N => ‖ZMod.stdAddChar y + ZMod.stdAddChar (2*y)‖) hne
    have hy₀' : y₀ ≠ 0 := (mem_filter.1 hy₀).2
    refine ⟨‖ZMod.stdAddChar y₀ + ZMod.stdAddChar (2*y₀)‖ / 2, by positivity, ?_, ?_⟩
    · have := pair_strict hy₀'; linarith
    · intro y hy
      have := hmax y (mem_filter.2 ⟨mem_univ _, hy⟩)
      linarith
  · refine ⟨0, le_rfl, one_pos, ?_⟩
    intro y hy
    exact absurd ⟨y, mem_filter.2 ⟨mem_univ _, hy⟩⟩ hne

lemma block_bound {N : ℕ} [NeZero N] {l : ℝ} (hl0 : 0 ≤ l)
    (hl : ∀ y : ZMod N, y ≠ 0 → ‖ZMod.stdAddChar y + ZMod.stdAddChar (2*y)‖ ≤ 2*l)
    (hu : IsUnit (2 : ZMod N)) :
    ∀ B : ℕ, ∀ y : ZMod N, y ≠ 0 → ‖∑ i ∈ range B, ZMod.stdAddChar (y * 2^i)‖ ≤ l * B + 2 := by
  intro B
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    intro y hy
    match B, ih with
    | 0, _ => simp
    | 1, _ =>
      simp only [range_one, sum_singleton, pow_zero, mul_one, norm_stdAddChar]
      push_cast; linarith
    | n+2, ih =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hy4 : y * 4 ≠ 0 := by
        have h4 : IsUnit (4 : ZMod N) := by
          rw [show (4 : ZMod N) = 2 * 2 by norm_num]; exact hu.mul hu
        intro h; exact hy (h4.mul_left_eq_zero.1 h)
      have hrec := ih n (by omega) (y * 4) hy4
      have e : ∀ i ∈ range n, ZMod.stdAddChar (y * 2^(i+1+1)) =
          ZMod.stdAddChar (y * 4 * 2^i) := by
        intro i _; congr 1; rw [pow_succ, pow_succ]; ring
      rw [Finset.sum_congr rfl e]
      have hp := hl y hy
      have e2 : ZMod.stdAddChar (y * 2^(0+1)) + ZMod.stdAddChar (y * 2^0) =
          ZMod.stdAddChar y + ZMod.stdAddChar (2*y) := by
        simp only [zero_add, pow_one, pow_zero, mul_one]; rw [mul_comm y 2]; ring
      calc ‖∑ i ∈ range n, ZMod.stdAddChar (y * 4 * 2^i) + ZMod.stdAddChar (y * 2^(0+1)) +
            ZMod.stdAddChar (y * 2^0)‖
          ≤ ‖∑ i ∈ range n, ZMod.stdAddChar (y * 4 * 2^i)‖ +
            ‖ZMod.stdAddChar (y * 2^(0+1)) + ZMod.stdAddChar (y * 2^0)‖ := by
            rw [add_assoc]; exact norm_add_le _ _
        _ ≤ (l * n + 2) + 2 * l := by rw [e2]; exact add_le_add hrec hp
        _ = l * ((n+2 : ℕ) : ℝ) + 2 := by push_cast; ring

lemma two_unit (R : ℕ) : IsUnit (2 : ZMod (PP R)) := by
  have h : Nat.Coprime 2 (PP R) := by
    apply Nat.Coprime.prod_right
    intro p hp
    have hp' := mem_Pset hp
    exact (Nat.coprime_primes Nat.prime_two hp'.1).2 (by omega)
  exact_mod_cast (ZMod.isUnit_iff_coprime 2 (PP R)).2 h

lemma family_injOn (k B : ℕ) :
    Set.InjOn (fun f : Fin k → ℕ => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j))
      ↑(Fintype.piFinset (fun _ : Fin k => Finset.range B)) := by
  apply Finset.injOn_of_card_image_eq
  rw [OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1.card_family,
    Fintype.card_piFinset]
  simp

lemma S_factor {N : ℕ} [NeZero N] (k B : ℕ) (m : ZMod N) :
    ∑ t ∈ (Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
        (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j)),
      ZMod.stdAddChar (m * (((t.map (fun i : ℕ => 2^i)).sum : ℕ) : ZMod N)) =
    ∏ j : Fin k, ∑ i ∈ range B, ZMod.stdAddChar ((m * 2^((j:ℕ)*B)) * 2^i) := by
  rw [sum_image (fun x hx y hy h => family_injOn k B hx hy h), prod_univ_sum]
  apply sum_congr rfl
  intro f _
  have hs : ((Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j)).map
      (fun i : ℕ => 2^i)).sum = ∑ j : Fin k, 2^((j:ℕ)*B + f j) := by
    rw [Multiset.map_map]; rfl
  rw [hs]
  push_cast
  rw [mul_sum, char_sum]
  apply prod_congr rfl
  intro j _
  congr 1
  rw [pow_add]; ring

theorem H2_holds : OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1.H2
  dsimp only
  intro ε hε R k₁
  haveI : NeZero (PP R) := ⟨(PP_pos R).ne'⟩
  obtain ⟨l, hl0, hl1, hl⟩ := pair_bound (PP R)
  have hu := two_unit R
  have hNpos : (0:ℝ) < PP R := by exact_mod_cast PP_pos R
  have hμ0 : 0 ≤ (1+l)/2 := by linarith
  have hμ1 : (1+l)/2 < 1 := by linarith
  have hμ2 : ((1+l)/2)^2 < 1 := by nlinarith
  obtain ⟨k', hk'⟩ := exists_pow_lt_of_lt_one (div_pos hε hNpos) hμ2
  refine ⟨max k₁ k', le_max_left _ _, ?_⟩
  have hμk : (((1+l)/2)^2)^(max k₁ k') ≤ ε / PP R :=
    le_trans (pow_le_pow_of_le_one (sq_nonneg _) hμ2.le (le_max_right _ _)) hk'.le
  filter_upwards [eventually_ge_atTop (⌈4/(1-l)⌉₊ + 1)] with B hB
  generalize max k₁ k' = k at hμk ⊢
  have hBl : l * B + 2 ≤ (1+l)/2 * B := by
    have h1 : 4/(1-l) ≤ (⌈4/(1-l)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈4/(1-l)⌉₊ : ℕ) : ℝ) ≤ (B:ℝ) := Nat.cast_le.mpr (by omega)
    rw [div_le_iff₀ (by linarith)] at h1
    nlinarith
  -- the exponential sums
  have hM : ∀ m : ZMod (PP R), m ≠ 0 →
      ‖∑ t ∈ (Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
          (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j)),
        ZMod.stdAddChar (m * (((t.map (fun i : ℕ => 2^i)).sum : ℕ) : ZMod (PP R)))‖ ≤
        (l * B + 2)^k := by
    intro m hm
    rw [S_factor, norm_prod]
    calc ∏ j : Fin k, ‖∑ i ∈ range B, ZMod.stdAddChar ((m * 2^((j:ℕ)*B)) * 2^i)‖
        ≤ ∏ _j : Fin k, (l * B + 2) := by
          apply prod_le_prod (fun j _ => norm_nonneg _)
          intro j _
          apply block_bound hl0 hl hu B
          intro h
          exact hm ((hu.pow _).mul_left_eq_zero.1 h)
      _ = (l * B + 2)^k := by simp
  have hcard : (((Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
      (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j))).card : ℝ) =
      (B:ℝ)^k := by
    rw [OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1.card_family]; push_cast; rfl
  generalize hQdef : (Fintype.piFinset (fun _ : Fin k => Finset.range B)).image
      (fun f => Finset.univ.val.map (fun j : Fin k => (j:ℕ)*B + f j)) = Q at hM hcard ⊢
  have hF := fourier_bound (fun x : ZMod (PP R) => GG R x.val) (fun x => GG_nonneg R _) Q
    (fun t => (((t.map (fun i : ℕ => 2^i)).sum : ℕ) : ZMod (PP R))) ((l * B + 2)^k) hM
  rw [mean_GG, hcard, div_self hNpos.ne', one_mul] at hF
  have hdrop : ∑ t ∈ Q, ∑ u ∈ Q.erase t,
      GG R (Nat.dist ((t.map (fun i : ℕ => 2^i)).sum) ((u.map (fun i : ℕ => 2^i)).sum)) ≤
      ∑ t ∈ Q, ∑ u ∈ Q,
      GG R (Nat.dist ((t.map (fun i : ℕ => 2^i)).sum) ((u.map (fun i : ℕ => 2^i)).sum)) :=
    sum_le_sum (fun t _ => sum_le_sum_of_subset_of_nonneg (erase_subset t Q)
      (fun u _ _ => GG_nonneg R _))
  have heq : ∑ t ∈ Q, ∑ u ∈ Q,
      GG R (Nat.dist ((t.map (fun i : ℕ => 2^i)).sum) ((u.map (fun i : ℕ => 2^i)).sum)) =
      ∑ t ∈ Q, ∑ u ∈ Q, (fun x : ZMod (PP R) => GG R x.val)
        ((((t.map (fun i : ℕ => 2^i)).sum : ℕ) : ZMod (PP R)) -
          (((u.map (fun i : ℕ => 2^i)).sum : ℕ) : ZMod (PP R))) := by
    apply sum_congr rfl; intro t _
    apply sum_congr rfl; intro u _
    exact GG_dist R _ _
  rw [heq] at hdrop
  rw [hcard]
  have hpowle : (l * B + 2)^k ≤ ((1+l)/2 * B)^k :=
    pow_le_pow_left₀ (by positivity) hBl k
  have hsq : ((l * B + 2)^k)^2 ≤ (((1+l)/2)^2)^k * ((B:ℝ)^k)^2 := by
    calc ((l * B + 2)^k)^2 ≤ (((1+l)/2 * B)^k)^2 :=
          pow_le_pow_left₀ (by positivity) hpowle 2
      _ = (((1+l)/2)^2)^k * ((B:ℝ)^k)^2 := by
          rw [mul_pow, mul_pow, pow_right_comm ((1+l)/2) k 2]
  have hfin : (PP R : ℝ) * ((l * B + 2)^k)^2 ≤ ε * ((B:ℝ)^k)^2 := by
    have hB2 : 0 ≤ ((B:ℝ)^k)^2 := sq_nonneg _
    calc (PP R : ℝ) * ((l * B + 2)^k)^2 ≤ (PP R : ℝ) * ((((1+l)/2)^2)^k * ((B:ℝ)^k)^2) :=
          mul_le_mul_of_nonneg_left hsq hNpos.le
      _ = ((PP R : ℝ) * (((1+l)/2)^2)^k) * ((B:ℝ)^k)^2 := by ring
      _ ≤ ε * ((B:ℝ)^k)^2 := by
          apply mul_le_mul_of_nonneg_right _ hB2
          rw [le_div_iff₀ hNpos] at hμk
          linarith
  show ∑ t ∈ Q, ∑ u ∈ Q.erase t,
      GG R (Nat.dist ((t.map (fun i : ℕ => 2^i)).sum) ((u.map (fun i : ℕ => 2^i)).sum)) ≤ _
  calc _ ≤ _ := hdrop
    _ ≤ ((B:ℝ)^k)^2 + (PP R : ℝ) * ((l * B + 2)^k)^2 := hF
    _ ≤ (1+ε) * ((B:ℝ)^k)^2 := by linarith

end OMA.Gallagher.H2proof

theorem OMA.solution : OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1.H2 :=
  OMA.Gallagher.H2proof.H2_holds
