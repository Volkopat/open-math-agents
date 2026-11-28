import OMAStatements.S_oeis_a230495

/-!
A230495, conjecture from the OEIS comments. The statement was contributed by
@niclorusso. For a fixed exponent bound, take a sum of widely separated powers
of two and remove its power-of-two factor. The binary blocks in every power
encode multinomial coefficients. Cyclic rotation of the slots makes the total
binary weight even.
-/

namespace OMA.EvilDigits

private theorem count_padded {a b L : ℕ} (ha : a < 2 ^ L) :
    (Nat.digits 2 (a + 2 ^ L * b)).count 1 =
      (Nat.digits 2 a).count 1 + (Nat.digits 2 b).count 1 := by
  by_cases hb : b = 0
  · simp [hb]
  have hlen := (Nat.digits_length_le_iff (by decide : 1 < 2) a).2 ha
  have h := Nat.digits_append_zeroes_append_digits (b := 2) (n := a)
    (k := L - (Nat.digits 2 a).length) (by decide) (Nat.pos_of_ne_zero hb)
  rw [Nat.add_sub_of_le hlen] at h
  rw [← h]
  simp [List.count_replicate]

theorem count_range (N L : ℕ) (g : ℕ → ℕ) (_hL : 0 < L)
    (hg : ∀ j < N, g j < 2 ^ L) :
    (Nat.digits 2 (∑ j ∈ Finset.range N, g j * 2 ^ (L * j))).count 1 =
      ∑ j ∈ Finset.range N, (Nat.digits 2 (g j)).count 1 := by
  induction N generalizing g with
  | zero => simp
  | succ N ih =>
    have htail := ih (fun j => g (j+1)) (fun j hj => hg (j+1) (by omega))
    have hs : (∑ j ∈ Finset.range (N+1), g j * 2 ^ (L*j)) =
        g 0 + 2 ^ L * ∑ j ∈ Finset.range N, g (j+1) * 2 ^ (L*j) := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [mul_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.mul_succ, pow_add]
      ring
    rw [hs, count_padded (hg 0 (by omega)), htail, Finset.sum_range_succ']
    omega

end OMA.EvilDigits

namespace OMA.EvilReindex

/-- Extend the coefficients by zero at gaps in their finite set of block numbers. -/
theorem separated_of_range
    (aligned : ∀ (N L : ℕ) (g : ℕ → ℕ), 0 < L →
      (∀ j < N, g j < 2 ^ L) →
      (Nat.digits 2 (∑ j ∈ Finset.range N, g j * 2 ^ (L * j))).count 1 =
        ∑ j ∈ Finset.range N, (Nat.digits 2 (g j)).count 1)
    {α : Type} (I : Finset α) (code c : α → ℕ) (L : ℕ) (hL : 0 < L)
    (injective : Set.InjOn code (I : Set α)) (bounded : ∀ a ∈ I, c a < 2 ^ L) :
    (Nat.digits 2 (∑ a ∈ I, c a * 2 ^ (L * code a))).count 1 =
      ∑ a ∈ I, (Nat.digits 2 (c a)).count 1 := by
  classical
  let N := I.sup code + 1
  let g (j : ℕ) : ℕ := if h : ∃ a ∈ I, code a = j then c h.choose else 0
  have g_at (a : α) (ha : a ∈ I) : g (code a) = c a := by
    have h : ∃ a' ∈ I, code a' = code a := ⟨a, ha, rfl⟩
    simp only [g, dif_pos h]
    exact congrArg c (injective h.choose_spec.1 ha h.choose_spec.2)
  have g_gap (j : ℕ) (hj : j ∉ I.image code) : g j = 0 := by
    have h : ¬ ∃ a ∈ I, code a = j := fun ⟨a, ha, eq⟩ => hj (Finset.mem_image.mpr ⟨a, ha, eq⟩)
    simp [g, h]
  have hbounded (j : ℕ) (_ : j < N) : g j < 2 ^ L := by
    by_cases hj : j ∈ I.image code
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
      simpa only [g_at a ha] using bounded a ha
    · rw [g_gap j hj]
      positivity
  have hsub : I.image code ⊆ Finset.range N := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup ha))
  have transport (w : ℕ → ℕ → ℕ) (w_zero : ∀ j, w j 0 = 0) :
      (∑ j ∈ Finset.range N, w j (g j)) = ∑ a ∈ I, w (code a) (c a) := by
    calc
      _ = ∑ j ∈ I.image code, w j (g j) :=
        (Finset.sum_subset hsub (fun j _ hj => by rw [g_gap j hj, w_zero])).symm
      _ = ∑ a ∈ I, w (code a) (g (code a)) := Finset.sum_image injective
      _ = _ := Finset.sum_congr rfl (fun a ha => by rw [g_at a ha])
  have h := aligned N L g hL hbounded
  rw [transport (fun j x => x * 2 ^ (L * j)) (by simp),
    transport (fun _ x => (Nat.digits 2 x).count 1) (by simp)] at h
  exact h

end OMA.EvilReindex

namespace OMA.EvilBlocks

private lemma digits_code {s : ℕ} (b : ℕ) (f : Fin s → ℕ) :
    Nat.ofDigits b (List.ofFn f) = ∑ j, f j * b ^ j.val := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ, ih, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

private lemma code_injOn {s i b : ℕ} (hb : 1 < b) (hib : i < b) :
    Set.InjOn (fun f : Fin s → ℕ => ∑ j, f j * b ^ j.val)
      (↑((Finset.univ : Finset (Fin s)).piAntidiag i) : Set (Fin s → ℕ)) := by
  intro f hf g hg h
  change f ∈ (Finset.univ : Finset (Fin s)).piAntidiag i at hf
  change g ∈ (Finset.univ : Finset (Fin s)).piAntidiag i at hg
  have digit_bound (a : Fin s → ℕ) (ha : a ∈ Finset.univ.piAntidiag i) :
      ∀ x ∈ List.ofFn a, x < b := by
    rw [List.forall_mem_ofFn_iff]
    intro j
    have hj := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact lt_of_le_of_lt (hj.trans_eq (Finset.mem_piAntidiag.mp ha).1) hib
  apply List.ofFn_injective
  apply Nat.ofDigits_inj_of_len_eq hb (by simp) (digit_bound f hf) (digit_bound g hg)
  simpa only [digits_code] using h

private lemma count_shift {v k : ℕ} (hk : 0 < k) :
    (Nat.digits 2 (2 ^ v * k)).count 1 = (Nat.digits 2 k).count 1 := by
  rw [Nat.digits_base_pow_mul (by decide : 1 < 2) hk]
  simp [List.count_replicate]

/-- Every power up to n of this odd k records the digit sum of its
multinomial coefficients, because different weak compositions lie in
disjoint binary blocks. -/
theorem block_realization (m n : ℕ)
    (separated : ∀ {α : Type} (I : Finset α) (code c : α → ℕ) (L : ℕ), 0 < L →
      Set.InjOn code (I : Set α) → (∀ a ∈ I, c a < 2 ^ L) →
      (Nat.digits 2 (∑ a ∈ I, c a * 2 ^ (L * code a))).count 1 =
        ∑ a ∈ I, (Nat.digits 2 (c a)).count 1) :
    ∃ k : ℕ, Odd k ∧ ∀ i ≤ n,
      (Nat.digits 2 (k ^ i)).count 1 =
      ∑ f ∈ (Finset.univ : Finset (Fin (2 ^ m))).piAntidiag i,
        (Nat.digits 2 (Nat.multinomial Finset.univ f)).count 1 := by
  let L := n.factorial
  let b := n+2
  let U := (Finset.univ : Finset (Fin (2 ^ m)))
  let base := fun j : Fin (2 ^ m) => 2 ^ (L * b ^ j.val)
  let K := ∑ j ∈ U, base j
  have hK : 0 < K := by
    let j : Fin (2 ^ m) := ⟨0, by positivity⟩
    have hj : 0 < base j := by dsimp [base]; positivity
    exact hj.trans_le (Finset.single_le_sum (f := base) (fun a _ => Nat.zero_le _) (Finset.mem_univ j))
  obtain ⟨v,k,hodd,hfac⟩ := Nat.exists_eq_two_pow_mul_odd hK.ne'
  have hk : 0 < k := by
    by_contra! he
    simp [show k = 0 by omega] at hodd
  refine ⟨k,hodd,?_⟩
  intro i hi
  let code := fun f : Fin (2 ^ m) → ℕ => ∑ j ∈ U, f j * b ^ j.val
  have hexpand : K^i = ∑ f ∈ U.piAntidiag i, Nat.multinomial U f * 2 ^ (L * code f) := by
    rw [show K = ∑ j ∈ U, base j from rfl, Finset.sum_pow_eq_sum_piAntidiag]
    apply Finset.sum_congr rfl
    intro f _
    congr 1
    dsimp only [base, code]
    simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcoef (f : Fin (2 ^ m) → ℕ) (hf : f ∈ U.piAntidiag i) :
      Nat.multinomial U f < 2 ^ L := by
    have hs := (Finset.mem_piAntidiag.mp hf).1
    unfold Nat.multinomial
    rw [hs]
    exact (Nat.div_le_self _ _).trans_lt ((Nat.factorial_le hi).trans_lt (show L < 2 ^ L from Nat.lt_two_pow_self))
  have hsep := separated (U.piAntidiag i) code (Nat.multinomial U) L (Nat.factorial_pos _)
    (code_injOn (by dsimp [b]; omega) (by dsimp [b]; omega)) hcoef
  rw [← hexpand] at hsep
  rw [hfac, mul_pow, ← pow_mul, count_shift (pow_pos hk i)] at hsep
  exact hsep

end OMA.EvilBlocks

open scoped BigOperators
open Finset

namespace EvilCyclic

abbrev Profile (s i : ℕ) := ↥(piAntidiag (univ : Finset (Fin s)) i)

def weight {s : ℕ} (f : Fin s → ℕ) : ℕ :=
  (Nat.digits 2 (Nat.multinomial univ f)).count 1

abbrev Point (s i : ℕ) := (f : Profile s i) × Fin (weight f.val)

def rotate {s i : ℕ} [NeZero s] (g : Fin s) (f : Profile s i) : Profile s i :=
  ⟨fun j ↦ f.val (j + g), by
    apply mem_piAntidiag.mpr
    exact ⟨(Equiv.sum_comp (Equiv.addRight g) f.val).trans (mem_piAntidiag.mp f.property).1,
      fun _ _ ↦ mem_univ _⟩⟩

theorem rotate_weight {s i : ℕ} [NeZero s] (g : Fin s) (f : Profile s i) :
    weight (rotate g f).val = weight f.val := by
  unfold weight Nat.multinomial
  simp only [rotate]
  have hs : (∑ j, f.val (j + g)) = ∑ j, f.val j := Equiv.sum_comp (Equiv.addRight g) f.val
  have hp : (∏ j, (f.val (j + g)).factorial) = ∏ j, (f.val j).factorial :=
    Equiv.prod_comp (Equiv.addRight g) (fun j ↦ (f.val j).factorial)
  rw [hs, hp]

def rotatePoint {s i : ℕ} [NeZero s] (g : Fin s) (p : Point s i) : Point s i :=
  ⟨rotate g p.1, ⟨p.2.val, (rotate_weight g p.1).symm ▸ p.2.isLt⟩⟩

theorem point_ext {s i : ℕ} {p q : Point s i}
    (hf : p.1 = q.1) (ht : p.2.val = q.2.val) : p = q := by
  exact Sigma.ext hf ((Fin.heq_ext_iff (congrArg (fun f : Profile s i ↦ weight f.val) hf)).mpr ht)

instance pointAction (s i : ℕ) [NeZero s] : MulAction (Multiplicative (Fin s)) (Point s i) where
  smul g p := rotatePoint g.toAdd p
  one_smul p := by
    refine point_ext ?_ ?_
    swap
    · rfl
    apply Subtype.ext
    funext j
    exact congrArg p.1.val (add_zero j)
  mul_smul g h p := by
    refine point_ext ?_ ?_
    swap
    · rfl
    apply Subtype.ext
    funext j
    exact congrArg p.1.val (add_assoc j g.toAdd h.toAdd).symm

theorem even_multinomial_digit_sum (m i : ℕ) (hi : 0 < i) (his : i < 2 ^ m) :
    Even (∑ f ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (2 ^ m))) i,
      ((Nat.digits 2 (Nat.multinomial Finset.univ f)).count 1)) := by
  classical
  let G := Multiplicative (Fin (2 ^ m))
  let P := Point (2 ^ m) i
  have group_order : Nat.card G = 2 ^ m := by change Nat.card (Fin (2 ^ m)) = _; simp
  have fixed_empty : IsEmpty (MulAction.fixedPoints G P) := by
    constructor
    intro x
    let f := x.val.1.val
    have hf (j : Fin (2 ^ m)) : f j = f 0 := by
      have h := x.property (Multiplicative.ofAdd j)
      have h' := congrArg (fun p : P ↦ p.1.val 0) h
      change f (0 + j) = f 0 at h'
      simpa using h'
    have sum_f : ∑ j, f j = i := (mem_piAntidiag.mp x.val.1.property).1
    have eq_i : 2 ^ m * f 0 = i := by simpa [hf] using sum_f
    by_cases h : f 0 = 0
    · simp [h] at eq_i
      omega
    · have := Nat.le_mul_of_pos_right (2 ^ m) (Nat.pos_of_ne_zero h)
      omega
  have mod_eq := (IsPGroup.of_card group_order).card_modEq_card_fixedPoints P
  have card_empty : Nat.card (MulAction.fixedPoints G P) = 0 := @Nat.card_of_isEmpty _ fixed_empty
  rw [card_empty] at mod_eq
  have h_even : Even (Nat.card P) := even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp mod_eq)
  rw [Nat.card_sigma] at h_even
  simp only [Nat.card_fin] at h_even
  rw [← Finset.sum_coe_sort]
  exact h_even

end EvilCyclic

theorem OMA.solution : type_of% @OMA.S_oeis_a230495.main := by
  intro n _hn
  obtain ⟨k, hk, h⟩ := OMA.EvilBlocks.block_realization n n
    (OMA.EvilReindex.separated_of_range OMA.EvilDigits.count_range)
  refine ⟨k, hk, ?_⟩
  intro i hi hin
  unfold OMA.S_oeis_a230495.IsEvil
  rw [h i hin]
  exact EvilCyclic.even_multinomial_digit_sum n i hi (hin.trans_lt (Nat.lt_two_pow_self))
