import OMAStatements.S_oeis_a236332

open Finset

namespace OMA.P_a236332

def act {n : ℕ} : DihedralGroup n → ZMod n → ZMod n
  | .r i, x => x - i
  | .sr j, x => j - x

instance instMA (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := act
  one_smul x := show x - 0 = x from sub_zero x
  mul_smul := by
    rintro (i|i) (j|j) x <;>
    simp only [HSMul.hSMul, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr, act] <;> ring

lemma smul_r {n : ℕ} (i x : ZMod n) : DihedralGroup.r i • x = x - i := rfl
lemma smul_sr {n : ℕ} (j x : ZMod n) : DihedralGroup.sr j • x = j - x := rfl

def O (k : ℕ) (t : Fin 4 → ZMod (k + 1)) : Finset (Fin 4 → ZMod (k + 1)) :=
  univ.image fun p : Bool × ZMod (k + 1) => fun i => if p.1 then p.2 - t i else p.2 + t i

lemma a_eq (k : ℕ) : S_oeis_a236332.a (k + 1) = (univ.image (O k)).card := rfl

open Classical in
lemma bridge (k : ℕ) : S_oeis_a236332.a (k + 1) =
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup (k + 1)) (Fin 4 → ZMod (k + 1)))) := by
  have ho : ∀ t u : Fin 4 → ZMod (k + 1), u ∈ O k t ↔
      u ∈ MulAction.orbit (DihedralGroup (k + 1)) t := by
    intro t u
    simp only [O, mem_image, mem_univ, true_and, MulAction.mem_orbit_iff,
      Prod.exists, Bool.exists_bool]
    constructor
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · refine ⟨DihedralGroup.r (-c), ?_⟩
        funext i
        show t i - -c = c + t i
        ring
      · exact ⟨DihedralGroup.sr c, rfl⟩
    · rintro ⟨(i | j), rfl⟩
      · refine Or.inl ⟨-i, ?_⟩
        funext x
        show -i + t x = t x - i
        ring
      · exact Or.inr ⟨j, rfl⟩
  have hf : ∀ t u : Fin 4 → ZMod (k + 1), O k t = O k u ↔
      MulAction.orbitRel (DihedralGroup (k + 1)) (Fin 4 → ZMod (k + 1)) t u := by
    intro t u
    rw [MulAction.orbitRel_apply, ← MulAction.orbit_eq_iff]
    constructor
    · intro h
      ext v
      rw [← ho, ← ho, h]
    · intro h
      ext v
      rw [ho, ho, h]
  rw [a_eq]
  rw [← Fintype.card_coe]
  refine (Fintype.card_congr (Equiv.ofBijective
    (Quotient.lift (s := MulAction.orbitRel (DihedralGroup (k + 1)) (Fin 4 → ZMod (k + 1)))
      (fun t => (⟨O k t, mem_image_of_mem _ (mem_univ _)⟩ :
        (univ.image (O k) : Finset _)))
      (fun t u h => Subtype.ext ((hf t u).2 h))) ⟨?_, ?_⟩)).symm
  · rintro ⟨t⟩ ⟨u⟩ h
    exact Quotient.sound ((hf t u).1 (congrArg Subtype.val h))
  · rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    exact ⟨⟦t⟧, rfl⟩

/-- number of fixed points of the reflection `sr j` on `ZMod n` -/
def c (n : ℕ) (j : ZMod n) [NeZero n] : ℕ := (univ.filter fun x : ZMod n => j - x = x).card

open Classical in
lemma count (n : ℕ) [NeZero n] :
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (Fin 4 → ZMod n))) * (2 * n) =
      n ^ 4 + ∑ j, c n j ^ 4 := by
  rw [← DihedralGroup.card, ← MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  have hfix : ∀ g : DihedralGroup n, Fintype.card (MulAction.fixedBy (Fin 4 → ZMod n) g) =
      (univ.filter fun x : ZMod n => g • x = x).card ^ 4 := by
    intro g
    rw [← Set.toFinset_card]
    have : (MulAction.fixedBy (Fin 4 → ZMod n) g).toFinset =
        Fintype.piFinset (fun _ => univ.filter fun x : ZMod n => g • x = x) := by
      ext f
      simp [MulAction.mem_fixedBy, Fintype.mem_piFinset, funext_iff]
    rw [this, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
  rw [Fintype.sum_congr _ _ hfix, ← DihedralGroup.equivSum.symm.sum_comp, Fintype.sum_sum_type]
  congr 1
  · have : ∀ i : ZMod n, (univ.filter fun x : ZMod n => DihedralGroup.equivSum.symm (Sum.inl i) • x = x).card ^ 4
        = if i = 0 then n ^ 4 else 0 := by
      intro i
      show (univ.filter fun x : ZMod n => x - i = x).card ^ 4 = _
      split_ifs with h
      · subst h; simp
      · simp [sub_eq_self, h]
    rw [Fintype.sum_congr _ _ this, sum_ite_eq']
    simp

lemma sum_c (n : ℕ) [NeZero n] : ∑ j, c n j = n := by
  have h := card_eq_sum_card_fiberwise (f := fun x : ZMod n => 2 * x) (s := univ) (t := univ)
    (fun _ _ => mem_univ _)
  rw [card_univ, ZMod.card] at h
  refine Eq.trans (sum_congr rfl fun j _ => ?_) h.symm
  unfold c
  congr 1
  refine filter_congr fun x _ => ?_
  rw [sub_eq_iff_eq_add, two_mul, eq_comm]

lemma odd_sum (n m : ℕ) [NeZero n] (hn : n = 2 * m + 1) : ∑ j, c n j ^ 4 = n := by
  have h2 : (2 : ZMod n) * (m + 1) = 1 := by
    have : ((2 * m + 1 : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
    push_cast at this
    linear_combination this
  have hc : ∀ j, c n j = 1 := by
    intro j
    unfold c
    rw [card_eq_one]
    refine ⟨(m + 1) * j, ?_⟩
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hx
      linear_combination (-(m + 1 : ZMod n)) * hx + (-x) * h2
    · rintro rfl
      linear_combination (-j) * h2
  simp [hc]

lemma two_mul_eq_zero (n p : ℕ) [NeZero n] (hn : n = 2 * p) (y : ZMod n) (hy : 2 * y = 0) :
    y = 0 ∨ y = p := by
  subst hn
  rw [← ZMod.natCast_zmod_val y] at hy ⊢
  have hd : 2 * p ∣ 2 * y.val := (ZMod.natCast_eq_zero_iff _ _).1 (by push_cast; exact hy)
  have hv := ZMod.val_lt y
  obtain ⟨q, hq⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
  have hq2 : q < 2 := by
    by_contra hq2
    rw [not_lt] at hq2
    have : p * 2 ≤ p * q := Nat.mul_le_mul_left p hq2
    omega
  interval_cases q
  · left; rw [hq]; simp
  · right; rw [hq, mul_one]

lemma even_sum (n p : ℕ) [NeZero n] (hn : n = 2 * p) (hp : 0 < p) : ∑ j, c n j ^ 4 = 8 * n := by
  have hp0 : (p : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, hn]
    intro h
    have := Nat.le_of_dvd hp h
    omega
  have h2p : (2 : ZMod n) * p = 0 := by
    have : ((2 * p : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
    push_cast at this
    exact this
  have hc : ∀ j, c n j ^ 4 = 8 * c n j := by
    intro j
    unfold c
    rcases (univ.filter fun x : ZMod n => j - x = x).eq_empty_or_nonempty with h | ⟨x0, hx0⟩
    · rw [h]; simp
    · simp only [mem_filter, mem_univ, true_and] at hx0
      have : (univ.filter fun x : ZMod n => j - x = x) = {x0, x0 + p} := by
        ext x
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · intro hx
          rcases two_mul_eq_zero n p hn (x - x0) (by linear_combination hx0 - hx) with h | h
          · left; linear_combination h
          · right; linear_combination h
        · rintro (rfl | rfl)
          · exact hx0
          · linear_combination hx0 - h2p
      rw [this, card_pair (by simpa using hp0)]
      norm_num
  rw [Fintype.sum_congr _ _ hc, ← mul_sum, sum_c]

end OMA.P_a236332

open OMA.P_a236332 in
theorem OMA.solution : type_of% @OMA.S_oeis_a236332.main := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [bridge]
  have hb := count (k + 1)
  set C := Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup (k + 1)) (Fin 4 → ZMod (k + 1))))
  rcases Nat.even_or_odd' (k + 1) with ⟨m, hm | hm⟩
  · rw [even_sum (k + 1) m hm (by omega)] at hb
    have h2 : C * 2 = (k + 1) ^ 3 + 8 := by
      apply Nat.eq_of_mul_eq_mul_left ((by omega : 0 < k + 1))
      linear_combination hb
    have hpow : (-1 : ℤ) ^ (k + 1) = 1 := by rw [hm, pow_mul]; norm_num
    rw [hpow]
    have : (9 + 7 * 1 + 2 * ((k + 1 : ℕ) : ℤ) ^ 3 : ℤ) = 4 * C := by
      have := congrArg (fun x : ℕ => (x : ℤ)) h2
      push_cast at this ⊢
      linear_combination -2 * this
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
  · rw [odd_sum (k + 1) m hm] at hb
    have h2 : C * 2 = (k + 1) ^ 3 + 1 := by
      apply Nat.eq_of_mul_eq_mul_left ((by omega : 0 < k + 1))
      linear_combination hb
    have hpow : (-1 : ℤ) ^ (k + 1) = -1 := by rw [hm, pow_succ, pow_mul]; norm_num
    rw [hpow]
    have : (9 + 7 * -1 + 2 * ((k + 1 : ℕ) : ℤ) ^ 3 : ℤ) = 4 * C := by
      have := congrArg (fun x : ℕ => (x : ℤ)) h2
      push_cast at this ⊢
      linear_combination -2 * this
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
