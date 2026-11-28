import OMAReductions.R_erdos_634_R1_H3_R1_H2_R1

/-!
# Erdos 634, step R1.H3.R1.H2.R1.H2 (sawtooth kernel triviality when a prime l >= 7 divides n)

Elementary self-contained proof via coset shifts modulo n / l.
-/

namespace OMA.E634PrimeGe7

open Finset

def sawQ (n k x : ℕ) : ℚ :=
  if Int.fract (((k * x : ℕ) : ℚ) / (n : ℚ)) = 0 then 0
  else Int.fract (((k * x : ℕ) : ℚ) / (n : ℚ)) - 1 / 2

def trivMod (n : ℕ) (a : Fin 3 → ℕ) : Submodule ℚ (Fin 3 → ℚ) :=
  Submodule.span ℚ
    ({v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪
     {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})

lemma card_filter_add_not {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  have hdisj : Disjoint (s.filter p) (s.filter (fun x => ¬ p x)) := by
    rw [Finset.disjoint_filter]
    intro x _ hp hnp; exact hnp hp
  have hunion : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

lemma int_dvd_sub_of_emod_eq {a b n : ℤ} (h : a % n = b % n) : n ∣ a - b :=
  Int.modEq_iff_dvd.mp h.symm

lemma coprime_of_modEq {a b n : ℕ} (h : a ≡ b [MOD n]) (hb : b.Coprime n) : a.Coprime n := by
  have hgcd : Nat.gcd a n = Nat.gcd b n := by
    rw [Nat.gcd_comm a n, Nat.gcd_comm b n, Nat.gcd_rec n a, Nat.gcd_rec n b]
    exact congrArg (fun x => Nat.gcd x n) h
  rwa [Nat.coprime_iff_gcd_eq_one, hgcd, ← Nat.coprime_iff_gcd_eq_one]

lemma sawQ_eq_mod {n k x : ℕ} (hn : 0 < n) (hndvd : ¬ n ∣ k * x) :
    sawQ n k x = ((k * x % n : ℕ) : ℚ) / (n : ℚ) - 1 / 2 := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdiv : ((k * x : ℕ) : ℚ) / (n : ℚ) =
      ((k * x % n : ℕ) : ℚ) / (n : ℚ) + (Int.ofNat (k * x / n) : ℚ) := by
    have hmod : k * x = k * x % n + n * (k * x / n) := by
      have := Nat.div_add_mod (k * x) n
      omega
    have hq : ((k * x : ℕ) : ℚ) = ((k * x % n : ℕ) : ℚ) + (n : ℚ) * ((k * x / n : ℕ) : ℚ) := by
      exact_mod_cast hmod
    rw [hq, add_div, mul_div_cancel_left₀ _ hnq]
    rfl
  have hlt : k * x % n < n := Nat.mod_lt _ hn
  have hpos : 0 < k * x % n := Nat.pos_of_ne_zero (fun h => hndvd (Nat.dvd_of_mod_eq_zero h))
  have hfr : Int.fract (((k * x : ℕ) : ℚ) / (n : ℚ)) = ((k * x % n : ℕ) : ℚ) / (n : ℚ) := by
    rw [hdiv, Int.fract_add_intCast, Int.fract_eq_self]
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    rw [div_lt_one (by exact_mod_cast hn)]
    exact_mod_cast hlt
  unfold sawQ
  rw [hfr, if_neg]
  exact div_ne_zero (by exact_mod_cast hpos.ne') hnq

lemma not_dvd_mul_of_coprime {n k x : ℕ} (hk : k.Coprime n) (hx0 : 0 < x) (hxn : x < n) :
    ¬ n ∣ k * x := by
  intro h
  have h' : n ∣ x := hk.symm.dvd_of_dvd_mul_left h
  exact absurd (Nat.le_of_dvd hx0 h') (by omega)

lemma a_lt_n {n : ℕ} {a : Fin 3 → ℕ} (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) (i : Fin 3) :
    a i < n := by
  have hs : a 0 + a 1 + a 2 = n := by rw [← hsum, Fin.sum_univ_three]
  have := hpos 0; have := hpos 1; have := hpos 2
  fin_cases i <;> dsimp <;> omega

lemma rel_mod_eq {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ}
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) {e : Fin 3 → ℚ}
    (hrel : ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k (a i) * e i = 0)
    {k : ℕ} (hk : k.Coprime n) :
    ∑ i : Fin 3, (((k * a i % n : ℕ) : ℚ) / (n : ℚ) - 1 / 2) * e i = 0 := by
  have h0 := hrel k hk
  refine Eq.trans ?_ h0
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sawQ_eq_mod hn (not_dvd_mul_of_coprime hk (hpos i) (a_lt_n hpos hsum i))]

lemma rel_int_eq {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ}
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) {e : Fin 3 → ℚ}
    (hrel : ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k (a i) * e i = 0)
    {k : ℕ} (hk : k.Coprime n) :
    ∑ i : Fin 3, (2 * ((k * a i % n : ℕ) : ℚ) - (n : ℚ)) * e i = 0 := by
  have h0 := rel_mod_eq hn hpos hsum hrel hk
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmul : (2 * (n : ℚ)) * ∑ i : Fin 3, (((k * a i % n : ℕ) : ℚ) / (n : ℚ) - 1 / 2) * e i = 0 := by
    rw [h0, mul_zero]
  rw [Finset.mul_sum] at hmul
  refine Eq.trans ?_ hmul
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp

lemma rel_k1_eq {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ}
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) {e : Fin 3 → ℚ}
    (hrel : ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k (a i) * e i = 0) :
    (2 * (a 0 : ℚ) - n) * e 0 + (2 * (a 1 : ℚ) - n) * e 1 + (2 * (a 2 : ℚ) - n) * e 2 = 0 := by
  have h := rel_int_eq hn hpos hsum hrel (Nat.coprime_one_left n)
  rw [Fin.sum_univ_three] at h
  have h0 : 1 * a 0 % n = a 0 := by rw [one_mul, Nat.mod_eq_of_lt (a_lt_n hpos hsum 0)]
  have h1 : 1 * a 1 % n = a 1 := by rw [one_mul, Nat.mod_eq_of_lt (a_lt_n hpos hsum 1)]
  have h2 : 1 * a 2 % n = a 2 := by rw [one_mul, Nat.mod_eq_of_lt (a_lt_n hpos hsum 2)]
  rw [h0, h1, h2] at h
  exact h

lemma all_eq_zero_of_eq {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ}
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) {e : Fin 3 → ℚ}
    (hrel : ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k (a i) * e i = 0)
    (he01 : e 0 = e 1) (he12 : e 1 = e 2) : e 0 = 0 := by
  have hk1 := rel_k1_eq hn hpos hsum hrel
  have hs : (a 0 : ℚ) + (a 1 : ℚ) + (a 2 : ℚ) = (n : ℚ) := by
    have : a 0 + a 1 + a 2 = n := by rw [← hsum, Fin.sum_univ_three]
    exact_mod_cast this
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← he12, ← he01] at hk1
  have hne : -(n : ℚ) * e 0 = 0 := by linear_combination hk1 - 2 * e 0 * hs
  rcases mul_eq_zero.mp hne with h | h
  · exact absurd (by linarith : (n : ℚ) = 0) hnq
  · exact h

lemma mod_shift_step {l m t x k : ℕ} (hl : 0 < l) (hm : 0 < m) :
    ((k + t * m) * x % (l * m) : ℕ) +
      (if l * m ≤ k * x % (l * m) + ((t * x) % l) * m then l * m else 0) =
      k * x % (l * m) + ((t * x) % l) * m := by
  have hn : 0 < l * m := Nat.mul_pos hl hm
  have h1 : (k + t * m) * x % (l * m) = (k * x % (l * m) + ((t * x) % l) * m) % (l * m) := by
    have htx : t * x = l * (t * x / l) + (t * x) % l := by
      have := Nat.div_add_mod (t * x) l; omega
    have hexp : (k + t * m) * x = k * x + ((t * x) % l) * m + (l * m) * (t * x / l) := by
      calc (k + t * m) * x = k * x + (t * x) * m := by ring
        _ = k * x + (l * (t * x / l) + (t * x) % l) * m := by rw [← htx]
        _ = k * x + ((t * x) % l) * m + (l * m) * (t * x / l) := by ring
    rw [hexp, Nat.add_mul_mod_self_left, Nat.mod_add_mod]
  have hcm : ((t * x) % l) * m < l * m := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hl) hm
  have hkx : k * x % (l * m) < l * m := Nat.mod_lt _ hn
  rw [h1]
  split_ifs with hge
  · have hsub : (k * x % (l * m) + ((t * x) % l) * m) % (l * m) =
        k * x % (l * m) + ((t * x) % l) * m - l * m := by
      have hq : k * x % (l * m) + ((t * x) % l) * m =
          (k * x % (l * m) + ((t * x) % l) * m - l * m) + l * m := by omega
      conv_lhs => rw [hq]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

def wrapB (l m t x k : ℕ) : Bool :=
  decide (l * m ≤ k * x % (l * m) + ((t * x) % l) * m)

def wrapQ (l m t x k : ℕ) : ℚ :=
  if wrapB l m t x k then 1 else 0

lemma jump_eq {l m t : ℕ} (hl : 0 < l) (hm : 0 < m) {a : Fin 3 → ℕ}
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = l * m) {e : Fin 3 → ℚ}
    (hrel : ∀ k : ℕ, k.Coprime (l * m) → ∑ i, sawQ (l * m) k (a i) * e i = 0)
    {k : ℕ} (hk1 : k.Coprime (l * m)) (hk2 : (k + t * m).Coprime (l * m)) :
    ∑ i : Fin 3, wrapQ l m t (a i) k * e i =
      (∑ i : Fin 3, (((t * a i) % l : ℕ) : ℚ) * e i) / (l : ℚ) := by
  set n := l * m
  have hn : 0 < n := Nat.mul_pos hl hm
  have h1 := rel_int_eq hn hpos hsum hrel hk1
  have h2 := rel_int_eq hn hpos hsum hrel hk2
  have hdiff : ∑ i : Fin 3,
      (2 * (((k + t * m) * a i % n : ℕ) : ℚ) - 2 * ((k * a i % n : ℕ) : ℚ)) * e i = 0 := by
    have hs : (∑ i : Fin 3, (2 * (((k + t * m) * a i % n : ℕ) : ℚ) - (n : ℚ)) * e i) -
              (∑ i : Fin 3, (2 * ((k * a i % n : ℕ) : ℚ) - (n : ℚ)) * e i) = 0 := by
      rw [h2, h1, sub_self]
    rw [← Finset.sum_sub_distrib] at hs
    refine Eq.trans ?_ hs
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hstep : ∀ i : Fin 3,
      (((k + t * m) * a i % n : ℕ) : ℚ) - ((k * a i % n : ℕ) : ℚ) =
      (((t * a i) % l : ℕ) : ℚ) * (m : ℚ) - wrapQ l m t (a i) k * ((l : ℚ) * (m : ℚ)) := by
    intro i
    have hnat := mod_shift_step (x := a i) (t := t) (k := k) hl hm
    have hnq : (n : ℚ) = (l : ℚ) * (m : ℚ) := by exact_mod_cast rfl
    by_cases hge : l * m ≤ k * a i % (l * m) + ((t * a i) % l) * m
    · have hw : wrapQ l m t (a i) k = 1 := by
        unfold wrapQ wrapB; rw [decide_eq_true hge]; rfl
      rw [hw, one_mul]
      rw [if_pos hge] at hnat
      have hq : (((k + t * m) * a i % (l * m) : ℕ) : ℚ) + ((l * m : ℕ) : ℚ) =
          ((k * a i % (l * m) : ℕ) : ℚ) + (((t * a i) % l : ℕ) : ℚ) * (m : ℚ) := by exact_mod_cast hnat
      change (((k + t * m) * a i % (l * m) : ℕ) : ℚ) - ((k * a i % (l * m) : ℕ) : ℚ) = _
      push_cast at hq; linarith
    · have hw : wrapQ l m t (a i) k = 0 := by
        unfold wrapQ wrapB; rw [decide_eq_false hge]; rfl
      rw [hw, zero_mul, sub_zero]
      rw [if_neg hge, add_zero] at hnat
      have hq : (((k + t * m) * a i % (l * m) : ℕ) : ℚ) =
          ((k * a i % (l * m) : ℕ) : ℚ) + (((t * a i) % l : ℕ) : ℚ) * (m : ℚ) := by exact_mod_cast hnat
      change (((k + t * m) * a i % (l * m) : ℕ) : ℚ) - ((k * a i % (l * m) : ℕ) : ℚ) = _
      linarith
  have hcomb : ∑ i : Fin 3,
      ((((t * a i) % l : ℕ) : ℚ) * (m : ℚ) -
        wrapQ l m t (a i) k * ((l : ℚ) * (m : ℚ))) * e i = 0 := by
    have hhalf : (2 : ℚ) * ∑ i : Fin 3,
        ((((t * a i) % l : ℕ) : ℚ) * (m : ℚ) -
          wrapQ l m t (a i) k * ((l : ℚ) * (m : ℚ))) * e i = 0 := by
      rw [Finset.mul_sum]
      refine Eq.trans ?_ hdiff
      refine Finset.sum_congr rfl (fun i _ => ?_)
      linear_combination -2 * e i * hstep i
    linarith
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have hsplit : (m : ℚ) * (∑ i : Fin 3, (((t * a i) % l : ℕ) : ℚ) * e i) -
      ((l : ℚ) * (m : ℚ)) * (∑ i : Fin 3, wrapQ l m t (a i) k * e i) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Eq.trans ?_ hcomb
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have heq : (l : ℚ) * (∑ i : Fin 3, wrapQ l m t (a i) k * e i) =
      ∑ i : Fin 3, (((t * a i) % l : ℕ) : ℚ) * e i := by
    apply mul_right_cancel₀ hmq
    linarith
  rw [eq_div_iff hlq]
  linarith

lemma wrap_count_coset {l m t x r : ℕ} (hl : 0 < l) (hm : 0 < m) :
    ((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      wrapB l m t x (r + j.1 * (t * m)) = true)).card = (t * x) % l := by
  set c := (t * x) % l
  have hstep : ∀ j : ℕ,
      (((r + (j + 1) * (t * m)) * x % (l * m) : ℕ) : ℤ) -
        (((r + j * (t * m)) * x % (l * m) : ℕ) : ℤ) =
      ((c * m : ℕ) : ℤ) - (if wrapB l m t x (r + j * (t * m)) then ((l * m : ℕ) : ℤ) else 0) := by
    intro j
    have hnat := mod_shift_step (x := x) (t := t) (k := r + j * (t * m)) hl hm
    have heq : r + (j + 1) * (t * m) = r + j * (t * m) + t * m := by ring
    rw [heq]
    by_cases hge : l * m ≤ (r + j * (t * m)) * x % (l * m) + c * m
    · have hw : wrapB l m t x (r + j * (t * m)) = true := decide_eq_true hge
      rw [hw, if_pos rfl]
      rw [if_pos hge] at hnat
      have hz : (((r + j * (t * m) + t * m) * x % (l * m) : ℕ) : ℤ) + ((l * m : ℕ) : ℤ) =
          (((r + j * (t * m)) * x % (l * m) : ℕ) : ℤ) + ((c * m : ℕ) : ℤ) := by exact_mod_cast hnat
      linarith
    · have hw : wrapB l m t x (r + j * (t * m)) = false := decide_eq_false hge
      rw [hw, if_neg Bool.false_ne_true]
      rw [if_neg hge, add_zero] at hnat
      have hz : (((r + j * (t * m) + t * m) * x % (l * m) : ℕ) : ℤ) =
          (((r + j * (t * m)) * x % (l * m) : ℕ) : ℤ) + ((c * m : ℕ) : ℤ) := by exact_mod_cast hnat
      linarith
  have htel : ∑ j ∈ Finset.range l,
      ((((r + (j + 1) * (t * m)) * x % (l * m) : ℕ) : ℤ) -
        (((r + j * (t * m)) * x % (l * m) : ℕ) : ℤ)) =
      (((r + l * (t * m)) * x % (l * m) : ℕ) : ℤ) -
        (((r + 0 * (t * m)) * x % (l * m) : ℕ) : ℤ) :=
    Finset.sum_range_sub (fun j => (((r + j * (t * m)) * x % (l * m) : ℕ) : ℤ)) l
  have hper : (r + l * (t * m)) * x % (l * m) = (r + 0 * (t * m)) * x % (l * m) := by
    have : (r + l * (t * m)) * x = (r + 0 * (t * m)) * x + (l * m) * (t * x) := by ring
    rw [this, Nat.add_mul_mod_self_left]
  rw [hper, sub_self] at htel
  have hsum : ∑ j ∈ Finset.range l,
      (((c * m : ℕ) : ℤ) - (if wrapB l m t x (r + j * (t * m)) then ((l * m : ℕ) : ℤ) else 0)) = 0 :=
    (Finset.sum_congr rfl (fun j _ => (hstep j).symm)).trans htel
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hcnt : ∑ j ∈ Finset.range l,
      (if wrapB l m t x (r + j * (t * m)) then ((l * m : ℕ) : ℤ) else 0) =
      (((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
        wrapB l m t x (r + j.1 * (t * m)) = true)).card : ℤ) * ((l * m : ℕ) : ℤ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [hcnt] at hsum
  have hposn : (0 : ℤ) < ((l * m : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos hl hm
  have hmul : (((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      wrapB l m t x (r + j.1 * (t * m)) = true)).card : ℤ) * ((l * m : ℕ) : ℤ) =
      (c : ℤ) * ((l * m : ℕ) : ℤ) := by
    have : (l : ℤ) * ((c * m : ℕ) : ℤ) = (c : ℤ) * ((l * m : ℕ) : ℤ) := by push_cast; ring
    linarith
  have hcardz : (((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      wrapB l m t x (r + j.1 * (t * m)) = true)).card : ℤ) = (c : ℤ) :=
    mul_right_cancel₀ hposn.ne' hmul
  exact_mod_cast hcardz

lemma exists_inv_mod_prime {l x : ℕ} (hl : l.Prime) (hx : ¬ l ∣ x) :
    ∃ t : ℕ, ¬ l ∣ t ∧ (t * x) % l = 1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hxz : (x : ZMod l) ≠ 0 := by
    intro h
    exact hx ((ZMod.natCast_eq_zero_iff x l).mp h)
  set z : ZMod l := (x : ZMod l)⁻¹
  refine ⟨z.val, ?_, ?_⟩
  · intro hd
    have hz0 : z = 0 := by
      have := (ZMod.natCast_eq_zero_iff z.val l).mpr hd
      simpa [ZMod.natCast_zmod_val] using this
    exact inv_ne_zero hxz hz0
  · have hmul : ((z.val * x : ℕ) : ZMod l) = 1 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact inv_mul_cancel₀ hxz
    have hval := congrArg ZMod.val hmul
    rw [ZMod.val_natCast, ZMod.val_one] at hval
    exact hval

lemma coprime_shift_m {m r j t : ℕ} (hr : r.Coprime m) : (r + j * (t * m)).Coprime m := by
  have : r + j * (t * m) = r + (j * t) * m := by ring
  rw [this, Nat.coprime_add_mul_right_left]
  exact hr

lemma bad_j_card_le_one {l m t r : ℕ} (hl : l.Prime) (hr : r.Coprime m) (ht : ¬ l ∣ t) :
    ((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      ¬ (r + j.1 * (t * m)).Coprime (l * m))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j₁ hj₁ j₂ hj₂
  rw [Finset.mem_filter] at hj₁ hj₂
  have hcm1 : (r + j₁.1 * (t * m)).Coprime m := coprime_shift_m hr
  have hcm2 : (r + j₂.1 * (t * m)).Coprime m := coprime_shift_m hr
  have hl1 : l ∣ r + j₁.1 * (t * m) := by
    by_contra hnd
    have hcl : (r + j₁.1 * (t * m)).Coprime l := (hl.coprime_iff_not_dvd.mpr hnd).symm
    exact hj₁.2 (hcl.mul_right hcm1)
  have hl2 : l ∣ r + j₂.1 * (t * m) := by
    by_contra hnd
    have hcl : (r + j₂.1 * (t * m)).Coprime l := (hl.coprime_iff_not_dvd.mpr hnd).symm
    exact hj₂.2 (hcl.mul_right hcm2)
  by_cases hlm : l ∣ m
  · exfalso
    have hlr : l ∣ r := by
      have hsub : l ∣ j₁.1 * (t * m) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hlm t) j₁.1
      exact (Nat.dvd_add_left hsub).mp hl1
    exact absurd (Nat.dvd_gcd hlr hlm) (by rw [hr.gcd_eq_one]; exact Nat.not_dvd_of_pos_of_lt Nat.zero_lt_one hl.one_lt)
  · have hltm : ¬ l ∣ t * m := fun h => (hl.dvd_mul.mp h).elim ht hlm
    have hsub : (l : ℤ) ∣ ((j₁.1 : ℤ) - (j₂.1 : ℤ)) * ((t * m : ℕ) : ℤ) := by
      have h1z : (l : ℤ) ∣ (r : ℤ) + (j₁.1 : ℤ) * ((t * m : ℕ) : ℤ) := by exact_mod_cast hl1
      have h2z : (l : ℤ) ∣ (r : ℤ) + (j₂.1 : ℤ) * ((t * m : ℕ) : ℤ) := by exact_mod_cast hl2
      have hds := dvd_sub h1z h2z
      have heq : ((r : ℤ) + (j₁.1 : ℤ) * ((t * m : ℕ) : ℤ)) - ((r : ℤ) + (j₂.1 : ℤ) * ((t * m : ℕ) : ℤ)) =
          ((j₁.1 : ℤ) - (j₂.1 : ℤ)) * ((t * m : ℕ) : ℤ) := by ring
      rw [heq] at hds
      exact hds
    have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    rcases hlp.dvd_or_dvd hsub with hd | hd
    · have hlt1 : j₁.1 < l := j₁.2
      have hlt2 : j₂.1 < l := j₂.2
      have heq : (j₁.1 : ℤ) - (j₂.1 : ℤ) = 0 := by
        obtain ⟨q, hq⟩ := hd
        have : q = 0 := by nlinarith
        rw [this, mul_zero] at hq
        exact hq
      exact Fin.ext (by omega)
    · exfalso
      exact hltm (Int.natCast_dvd_natCast.mp hd)

lemma bad_trans_card_le_two {l m t r : ℕ} (hl : l.Prime) (hr : r.Coprime m) (ht : ¬ l ∣ t) :
    ((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      ¬ ((r + j.1 * (t * m)).Coprime (l * m) ∧
         (r + (j.1 + 1) * (t * m)).Coprime (l * m)))).card ≤ 2 := by
  set B := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
    ¬ (r + j.1 * (t * m)).Coprime (l * m))
  have hB : B.card ≤ 1 := bad_j_card_le_one hl hr ht
  have hsub : ((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      ¬ ((r + j.1 * (t * m)).Coprime (l * m) ∧
         (r + (j.1 + 1) * (t * m)).Coprime (l * m)))) ⊆
      B ∪ B.image (fun j : Fin l => ⟨(j.1 + l - 1) % l, Nat.mod_lt _ hl.pos⟩) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_union]
    by_cases h1 : (r + j.1 * (t * m)).Coprime (l * m)
    · right
      have h2 : ¬ (r + (j.1 + 1) * (t * m)).Coprime (l * m) := fun hc => hj.2 ⟨h1, hc⟩
      rw [Finset.mem_image]
      refine ⟨⟨(j.1 + 1) % l, Nat.mod_lt _ hl.pos⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hc
        apply h2
        have hmod : (r + (j.1 + 1) * (t * m)) ≡ (r + ((j.1 + 1) % l) * (t * m)) [MOD l * m] := by
          have hdiv : j.1 + 1 = (j.1 + 1) % l + l * ((j.1 + 1) / l) := by
            have := Nat.div_add_mod (j.1 + 1) l; omega
          have hexp : r + (j.1 + 1) * (t * m) =
              r + ((j.1 + 1) % l) * (t * m) + (l * m) * (t * ((j.1 + 1) / l)) := by
            conv_lhs => rw [hdiv]
            ring
          rw [hexp]
          exact Nat.ModEq.symm (by simp [Nat.ModEq, Nat.add_mul_mod_self_left])
        exact coprime_of_modEq hmod hc
      · apply Fin.ext
        dsimp
        by_cases hlt : j.1 + 1 < l
        · rw [Nat.mod_eq_of_lt hlt]
          have : j.1 + 1 + l - 1 = j.1 + l := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.2]
        · have heq : j.1 + 1 = l := by omega
          rw [heq, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
          omega
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
  calc _ ≤ (B ∪ B.image (fun j : Fin l => (⟨(j.1 + l - 1) % l, Nat.mod_lt _ hl.pos⟩ : Fin l))).card :=
        Finset.card_le_card hsub
    _ ≤ B.card + (B.image _).card := Finset.card_union_le _ _
    _ ≤ B.card + B.card := Nat.add_le_add_left Finset.card_image_le _
    _ ≤ 2 := by omega

lemma valid_trans_card_ge {l m t r : ℕ} (hl : l.Prime) (hr : r.Coprime m) (ht : ¬ l ∣ t) :
    l - 2 ≤ ((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      (r + j.1 * (t * m)).Coprime (l * m) ∧
      (r + (j.1 + 1) * (t * m)).Coprime (l * m))).card := by
  have hbad := bad_trans_card_le_two hl hr ht
  have hsum := card_filter_add_not (Finset.univ : Finset (Fin l))
    (fun j : Fin l => (r + j.1 * (t * m)).Coprime (l * m) ∧
      (r + (j.1 + 1) * (t * m)).Coprime (l * m))
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  omega

lemma lift_coprime {d m r0 : ℕ} (hm : 0 < m) (hcop : r0.Coprime d) :
    ∃ r : ℕ, r.Coprime m ∧ r ≡ r0 [MOD d] := by
  set i := ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ∣ r0), p
  refine ⟨r0 + i * d, ?_, ?_⟩
  · rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    set p := (Nat.gcd (r0 + i * d) m).minFac
    have hp : p.Prime := Nat.minFac_prime hne
    have hpd1 : p ∣ r0 + i * d := dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_left _ _)
    have hpm : p ∣ m := dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_right _ _)
    by_cases hpr0 : p ∣ r0
    · have hpid : p ∣ i * d := (Nat.dvd_add_right hpr0).mp hpd1
      rcases hp.dvd_mul.mp hpid with hpi | hpd
      · obtain ⟨q, hqmem, hpq⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp) _).mp hpi
        rw [Finset.mem_filter] at hqmem
        have hqp : q.Prime := (Nat.mem_primeFactors.mp hqmem.1).1
        have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
        subst heq
        exact hqmem.2 hpr0
      · have := Nat.dvd_gcd hpr0 hpd
        rw [hcop.gcd_eq_one] at this
        exact absurd (Nat.le_of_dvd Nat.zero_lt_one this) (by have := hp.two_le; omega)
    · have hpmem : p ∈ m.primeFactors.filter (fun q => ¬ q ∣ r0) :=
        Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.ne'⟩, hpr0⟩
      have hpi : p ∣ i := Finset.dvd_prod_of_mem _ hpmem
      have hpid : p ∣ i * d := dvd_mul_of_dvd_left hpi d
      exact hpr0 ((Nat.dvd_add_left hpid).mp hpd1)
  · simp [Nat.ModEq, Nat.add_mul_mod_self_right]

lemma exists_mid_coprime {d : ℕ} (hd : 2 ≤ d) :
    ∃ u : ℕ, u.Coprime d ∧ d ≤ 6 * u ∧ 6 * u ≤ 5 * d ∧
      (d ≠ 4 → d ≠ 6 → 2 * d < 7 * u ∧ 7 * u < 5 * d) := by
  by_cases hle : d ≤ 6
  · interval_cases d
    · exact ⟨1, by norm_num, by omega, by omega, fun _ _ => by omega⟩
    · exact ⟨1, by norm_num, by omega, by omega, fun _ _ => by omega⟩
    · exact ⟨1, by norm_num, by omega, by omega, fun h _ => absurd rfl h⟩
    · exact ⟨2, by norm_num, by omega, by omega, fun _ _ => by omega⟩
    · exact ⟨1, by norm_num, by omega, by omega, fun _ h => absurd rfl h⟩
  · by_cases hodd : d % 2 = 1
    · refine ⟨d / 2, ?_, by omega, by omega, fun _ _ => by omega⟩
      have h1 : d = 2 * (d / 2) + 1 := by omega
      have : Nat.Coprime (d / 2) (2 * (d / 2) + 1) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        have hg : Nat.gcd (d / 2) (2 * (d / 2) + 1) ∣ 1 := by
          have hda := Nat.gcd_dvd_left (d / 2) (2 * (d / 2) + 1)
          have hdb := Nat.gcd_dvd_right (d / 2) (2 * (d / 2) + 1)
          have h2a : Nat.gcd (d / 2) (2 * (d / 2) + 1) ∣ 2 * (d / 2) := dvd_mul_of_dvd_right hda 2
          exact (Nat.dvd_add_right h2a).mp hdb
        exact Nat.eq_one_of_dvd_one hg
      rwa [← h1] at this
    · by_cases h4 : d % 4 = 0
      · set q := d / 2
        have hdq : d = 2 * q := by omega
        have hqeven : 2 ∣ q := ⟨d / 4, by omega⟩
        refine ⟨q - 1, ?_, by omega, by omega, fun _ _ => by omega⟩
        rw [hdq]
        apply Nat.Coprime.mul_right
        · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by obtain ⟨k, hk⟩ := hqeven; omega)).symm
        · have hsub : (q - 1) + 1 = q := by omega
          rw [Nat.coprime_iff_gcd_eq_one]
          have hg : Nat.gcd (q - 1) q ∣ 1 := by
            have hda := Nat.gcd_dvd_left (q - 1) q
            have hdb : Nat.gcd (q - 1) q ∣ (q - 1) + 1 := by
              rw [hsub]; exact Nat.gcd_dvd_right (q - 1) q
            exact (Nat.dvd_add_right hda).mp hdb
          exact Nat.eq_one_of_dvd_one hg
      · set q := d / 2
        have hdq : d = 2 * q := by omega
        have hqodd : q % 2 = 1 := by omega
        have hq5 : 5 ≤ q := by omega
        refine ⟨q - 2, ?_, by omega, by omega, fun _ _ => by omega⟩
        rw [hdq]
        apply Nat.Coprime.mul_right
        · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
        · rw [Nat.coprime_iff_gcd_eq_one]
          have hg2 : Nat.gcd (q - 2) q ∣ 2 := by
            have hda := Nat.gcd_dvd_left (q - 2) q
            have hsub : (q - 2) + 2 = q := by omega
            have hdb : Nat.gcd (q - 2) q ∣ (q - 2) + 2 := by
              rw [hsub]; exact Nat.gcd_dvd_right (q - 2) q
            exact (Nat.dvd_add_right hda).mp hdb
          have hgq : Nat.gcd (q - 2) q ∣ q := Nat.gcd_dvd_right _ _
          have hne2 : Nat.gcd (q - 2) q ≠ 2 := by
            intro h2; rw [h2] at hgq; omega
          have hle2 : Nat.gcd (q - 2) q ≤ 2 := Nat.le_of_dvd (by omega) hg2
          have hpos : 0 < Nat.gcd (q - 2) q := Nat.gcd_pos_of_pos_right _ (by omega)
          omega

lemma sum_rem_coset {l m t x r : ℕ} (hl : l.Prime) (hm : 0 < m)
    (ht : ¬ l ∣ t) (hx : ¬ l ∣ x) :
    ∑ j : Fin l, (r + j.1 * (t * m)) * x % (l * m) =
      l * (r * x % m) + m * (l * (l - 1) / 2) := by
  have hn : 0 < l * m := Nat.mul_pos hl.pos hm
  have hmodm : ∀ j : Fin l, (r + j.1 * (t * m)) * x % (l * m) % m = r * x % m := by
    intro j
    rw [Nat.mod_mul_left_mod]
    have : (r + j.1 * (t * m)) * x = r * x + m * (j.1 * t * x) := by ring
    rw [this, Nat.add_mul_mod_self_left]
  set q : Fin l → Fin l := fun j =>
    ⟨((r + j.1 * (t * m)) * x % (l * m)) / m,
      Nat.div_lt_of_lt_mul (by
        have hlt := Nat.mod_lt ((r + j.1 * (t * m)) * x) hn
        linarith)⟩
  have hdecomp : ∀ j : Fin l,
      (r + j.1 * (t * m)) * x % (l * m) = (r * x % m) + m * (q j).1 := by
    intro j
    have hdm := Nat.div_add_mod ((r + j.1 * (t * m)) * x % (l * m)) m
    rw [hmodm j] at hdm
    dsimp [q]
    omega
  have hq_inj : Function.Injective q := by
    intro j₁ j₂ hqeq
    have hv : (q j₁).1 = (q j₂).1 := congrArg Fin.val hqeq
    have hrem : (r + j₁.1 * (t * m)) * x % (l * m) = (r + j₂.1 * (t * m)) * x % (l * m) := by
      rw [hdecomp j₁, hdecomp j₂, hv]
    have hdvd : ((l * m : ℕ) : ℤ) ∣
        (((r + j₁.1 * (t * m)) * x : ℕ) : ℤ) - (((r + j₂.1 * (t * m)) * x : ℕ) : ℤ) :=
      int_dvd_sub_of_emod_eq (by exact_mod_cast hrem)
    have hfac : (((r + j₁.1 * (t * m)) * x : ℕ) : ℤ) - (((r + j₂.1 * (t * m)) * x : ℕ) : ℤ) =
        (m : ℤ) * (((j₁.1 : ℤ) - (j₂.1 : ℤ)) * ((t * x : ℕ) : ℤ)) := by
      push_cast; ring
    rw [hfac] at hdvd
    have hld : (l : ℤ) ∣ ((j₁.1 : ℤ) - (j₂.1 : ℤ)) * ((t * x : ℕ) : ℤ) := by
      obtain ⟨k, hk⟩ := hdvd
      refine ⟨k, ?_⟩
      have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
      apply mul_left_cancel₀ hmz
      push_cast at hk ⊢
      rw [hk]; ring
    have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    rcases hlp.dvd_or_dvd hld with hjj | htx
    · obtain ⟨k, hk⟩ := hjj
      have h1 := j₁.2; have h2 := j₂.2
      have hk0 : k = 0 := by nlinarith
      rw [hk0, mul_zero] at hk
      exact Fin.ext (by omega)
    · exfalso
      exact (hl.dvd_mul.mp (Int.natCast_dvd_natCast.mp htx)).elim ht hx
  have hq_bij : Function.Bijective q := (Finite.injective_iff_bijective).mp hq_inj
  have hsum_q : ∑ j : Fin l, (q j).1 = ∑ j : Fin l, j.1 :=
    Fintype.sum_bijective q hq_bij _ _ (fun _ => rfl)
  have hsum_fin : ∑ j : Fin l, j.1 = l * (l - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => j) l, Finset.sum_range_id]
  calc ∑ j : Fin l, (r + j.1 * (t * m)) * x % (l * m)
      = ∑ j : Fin l, ((r * x % m) + m * (q j).1) := Finset.sum_congr rfl (fun j _ => hdecomp j)
    _ = (∑ _j : Fin l, (r * x % m)) + ∑ j : Fin l, m * (q j).1 := Finset.sum_add_distrib
    _ = l * (r * x % m) + m * ∑ j : Fin l, (q j).1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.mul_sum]
    _ = l * (r * x % m) + m * (l * (l - 1) / 2) := by rw [hsum_q, hsum_fin]

lemma two_mul_tri_odd {l : ℕ} (hl : 2 ≤ l) : 2 * (l * (l - 1) / 2) = l * (l - 1) := by
  have hev : Even (l * (l - 1)) := by
    by_cases h : l % 2 = 0
    · refine ⟨(l / 2) * (l - 1), ?_⟩
      have hl2 : l = 2 * (l / 2) := by omega
      calc l * (l - 1) = (2 * (l / 2)) * (l - 1) := by rw [← hl2]
        _ = (l / 2) * (l - 1) + (l / 2) * (l - 1) := by ring
    · refine ⟨l * ((l - 1) / 2), ?_⟩
      have h2 : l - 1 = 2 * ((l - 1) / 2) := by omega
      calc l * (l - 1) = l * (2 * ((l - 1) / 2)) := by rw [← h2]
        _ = l * ((l - 1) / 2) + l * ((l - 1) / 2) := by ring
  obtain ⟨k, hk⟩ := hev
  omega

lemma exists_r_with_rem {m b u : ℕ} (hm : 0 < m) (hb0 : 0 < b) (hbm : b < m)
    (hu : u.Coprime (m / Nat.gcd m b)) :
    ∃ r : ℕ, r.Coprime m ∧ r * b % m = (u % (m / Nat.gcd m b)) * Nat.gcd m b := by
  set g := Nat.gcd m b
  set d := m / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  have hgd : g ∣ m := Nat.gcd_dvd_left m b
  have hgb : g ∣ b := Nat.gcd_dvd_right m b
  have hmd : m = g * d := (Nat.mul_div_cancel' hgd).symm
  set b1 := b / g
  have hbb1 : b = g * b1 := (Nat.mul_div_cancel' hgb).symm
  have hd2 : 2 ≤ d := by
    have : b < g * d := by rwa [← hmd]
    have : 1 ≤ b1 := by
      rcases Nat.eq_zero_or_pos b1 with h | h
      · rw [h, mul_zero] at hbb1; omega
      · exact h
    have : g * 1 ≤ g * b1 := Nat.mul_le_mul_left g this
    nlinarith
  have hcop_b1 : b1.Coprime d := by
    have := Nat.coprime_div_gcd_div_gcd (m := b) (n := m) (Nat.gcd_pos_of_pos_right _ hm)
    rwa [Nat.gcd_comm] at this
  have hφ : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
  set r0 := u * b1 ^ (Nat.totient d - 1)
  have hr0_cop : r0.Coprime d := hu.mul_left (hcop_b1.pow_left _)
  have hr0_mod : r0 * b1 ≡ u [MOD d] := by
    have hpow : r0 * b1 = u * b1 ^ Nat.totient d := by
      dsimp [r0]
      rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hφ]
    rw [hpow]
    have h1 := Nat.ModEq.pow_totient hcop_b1
    simpa using (Nat.ModEq.refl u).mul h1
  obtain ⟨r, hr_cop, hr_mod⟩ := lift_coprime hm hr0_cop
  refine ⟨r, hr_cop, ?_⟩
  have hrb1 : r * b1 ≡ u [MOD d] := (hr_mod.mul_right b1).trans hr0_mod
  have hrb1_mod : r * b1 % d = u % d := hrb1
  calc r * b % m = r * (g * b1) % (g * d) := by rw [hbb1, hmd]
    _ = g * (r * b1) % (g * d) := by ring_nf
    _ = g * (r * b1 % d) := Nat.mul_mod_mul_left g (r * b1) d
    _ = (u % d) * g := by rw [hrb1_mod, mul_comm]

/-- Helper for Case I (when ¬ l ∣ m): if remainder sum is constant across valid j in coset r',
    and r' * b2 % m = v with m < l * v, then either (l * v ≤ 2 * m and jb has large a 0 remainder)
    or (l - 2) * m < l * v. -/
lemma case_one_bad_bound {l m t b2 r' v : ℕ} (hl : l.Prime) (hl7 : 7 ≤ l) (hm : 0 < m)
    (ht : ¬ l ∣ t) {a : Fin 3 → ℕ} (hsum : ∑ i, a i = l * m)
    (ha0 : ¬ l ∣ a 0) (ha1 : ¬ l ∣ a 1) (hb2 : a 2 = l * b2)
    (hta0 : (t * a 0) % l = 1) (hta1 : (t * a 1) % l = l - 1) (hta2 : (t * a 2) % l = 0)
    (hr' : r'.Coprime m) (hrb' : r' * b2 % m = v) (hv_pos : 0 < v) (hlv_gt : m < l * v)
    (hconst : ∀ j₁ j₂ : Fin l,
      (r' + j₁.1 * (t * m)).Coprime (l * m) → (r' + j₂.1 * (t * m)).Coprime (l * m) →
      ((r' + j₁.1 * (t * m)) * a 0 % (l * m) + (r' + j₁.1 * (t * m)) * a 1 % (l * m) +
        (r' + j₁.1 * (t * m)) * a 2 % (l * m)) =
      ((r' + j₂.1 * (t * m)) * a 0 % (l * m) + (r' + j₂.1 * (t * m)) * a 1 % (l * m) +
        (r' + j₂.1 * (t * m)) * a 2 % (l * m))) :
    (l * v ≤ 2 * m ∧
      ∃ jb : Fin l, l ∣ (r' + jb.1 * (t * m)) ∧
        (l - 1) * m ≤ (r' + jb.1 * (t * m)) * a 0 % (l * m)) ∨
    (l - 2) * m < l * v := by
  have hn : 0 < l * m := Nat.mul_pos hl.pos hm
  have hsum_r' : ∑ j : Fin l, ((r' + j.1 * (t * m)) * a 0 % (l * m) +
      (r' + j.1 * (t * m)) * a 1 % (l * m) +
      (r' + j.1 * (t * m)) * a 2 % (l * m)) =
      l * (r' * a 0 % m + r' * a 1 % m) + l * m * (l - 1) + l * l * v := by
    have hs0 := sum_rem_coset (r := r') hl hm ht ha0
    have hs1 := sum_rem_coset (r := r') hl hm ht ha1
    have hs2 : ∑ j : Fin l, (r' + j.1 * (t * m)) * a 2 % (l * m) = l * (l * v) := by
      have hterm : ∀ j : Fin l, (r' + j.1 * (t * m)) * a 2 % (l * m) = l * v := by
        intro j
        rw [hb2]
        have : (r' + j.1 * (t * m)) * (l * b2) = l * (r' * b2) + (l * m) * (j.1 * t * b2) := by ring
        rw [this, Nat.add_mul_mod_self_left, Nat.mul_mod_mul_left, hrb']
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hs0, hs1, hs2]
    have htri := two_mul_tri_odd (by omega : 2 ≤ l)
    have hml : m * (l * (l - 1) / 2) + m * (l * (l - 1) / 2) = l * m * (l - 1) := by
      calc m * (l * (l - 1) / 2) + m * (l * (l - 1) / 2)
          = m * (2 * (l * (l - 1) / 2)) := by ring
        _ = m * (l * (l - 1)) := by rw [htri]
        _ = l * m * (l - 1) := by ring
    linarith
  have heps_vals : ∀ j : Fin l,
      ((r' + j.1 * (t * m)) * a 0 % (l * m) +
       (r' + j.1 * (t * m)) * a 1 % (l * m) +
       (r' + j.1 * (t * m)) * a 2 % (l * m) = l * m) ∨
      ((r' + j.1 * (t * m)) * a 0 % (l * m) +
       (r' + j.1 * (t * m)) * a 1 % (l * m) +
       (r' + j.1 * (t * m)) * a 2 % (l * m) = 2 * (l * m)) := by
    intro j
    set k := r' + j.1 * (t * m)
    have hdvd : l * m ∣ k * a 0 % (l * m) + k * a 1 % (l * m) + k * a 2 % (l * m) := by
      have hs : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
      have hmod : (k * a 0 % (l * m) + k * a 1 % (l * m) + k * a 2 % (l * m)) % (l * m) =
          (k * a 0 + k * a 1 + k * a 2) % (l * m) := by
        simp [Nat.add_mod]
      have hzero : (k * a 0 + k * a 1 + k * a 2) % (l * m) = 0 := by
        have : k * a 0 + k * a 1 + k * a 2 = (l * m) * k := by
          calc _ = k * (a 0 + a 1 + a 2) := by ring
            _ = k * (l * m) := by rw [hs]
            _ = (l * m) * k := by ring
        rw [this, Nat.mul_mod_right]
      exact Nat.dvd_of_mod_eq_zero (hmod.trans hzero)
    have h2pos : 0 < k * a 2 % (l * m) := by
      rw [hb2]
      have : k * (l * b2) = l * (r' * b2) + (l * m) * (j.1 * t * b2) := by dsimp [k]; ring
      rw [this, Nat.add_mul_mod_self_left, Nat.mul_mod_mul_left, hrb']
      exact Nat.mul_pos hl.pos hv_pos
    have hl0 := Nat.mod_lt (k * a 0) hn
    have hl1 := Nat.mod_lt (k * a 1) hn
    have hl2 := Nat.mod_lt (k * a 2) hn
    obtain ⟨c, hc⟩ := hdvd
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hc; omega
      · exact h
    have hc2 : c ≤ 2 := by nlinarith
    interval_cases c
    · left; linarith
    · right; linarith
  set B := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
    ¬ (r' + j.1 * (t * m)).Coprime (l * m))
  have hB1 : B.card ≤ 1 := bad_j_card_le_one hl hr' ht
  have hVpos : 0 < ((Finset.univ : Finset (Fin l)) \ B).card := by
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin l)) B
    rw [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hs
    omega
  obtain ⟨j0, hj0⟩ := Finset.card_pos.mp hVpos
  have hj0c : (r' + j0.1 * (t * m)).Coprime (l * m) := by
    rw [Finset.mem_sdiff] at hj0
    by_contra hc
    exact hj0.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  rcases heps_vals j0 with h1 | h2
  · left
    have hvalid1 : ∀ j : Fin l, j ∉ B →
        (r' + j.1 * (t * m)) * a 0 % (l * m) +
        (r' + j.1 * (t * m)) * a 1 % (l * m) +
        (r' + j.1 * (t * m)) * a 2 % (l * m) = l * m := by
      intro j hj
      have hjc : (r' + j.1 * (t * m)).Coprime (l * m) := by
        by_contra hc; exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
      exact (hconst j j0 hjc hj0c).trans h1
    have htot_le : ∑ j : Fin l, ((r' + j.1 * (t * m)) * a 0 % (l * m) +
        (r' + j.1 * (t * m)) * a 1 % (l * m) +
        (r' + j.1 * (t * m)) * a 2 % (l * m)) ≤ (l + 1) * (l * m) := by
      have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin l))
        (fun j : Fin l => j ∈ B) (fun j : Fin l =>
          (r' + j.1 * (t * m)) * a 0 % (l * m) +
          (r' + j.1 * (t * m)) * a 1 % (l * m) +
          (r' + j.1 * (t * m)) * a 2 % (l * m))).symm
      rw [hsplit]
      have hleB : ∑ j ∈ Finset.univ.filter (fun j : Fin l => j ∈ B),
          ((r' + j.1 * (t * m)) * a 0 % (l * m) +
           (r' + j.1 * (t * m)) * a 1 % (l * m) +
           (r' + j.1 * (t * m)) * a 2 % (l * m)) ≤ B.card * (2 * (l * m)) := by
        calc _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin l => j ∈ B), (2 * (l * m)) :=
              Finset.sum_le_sum (fun j _ => by rcases heps_vals j with hv | hv <;> omega)
          _ = (Finset.univ.filter (fun j : Fin l => j ∈ B)).card * (2 * (l * m)) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ = B.card * (2 * (l * m)) := by simp
      have hleV : ∑ j ∈ Finset.univ.filter (fun j : Fin l => j ∉ B),
          ((r' + j.1 * (t * m)) * a 0 % (l * m) +
           (r' + j.1 * (t * m)) * a 1 % (l * m) +
           (r' + j.1 * (t * m)) * a 2 % (l * m)) = (l - B.card) * (l * m) := by
        rw [Finset.sum_congr rfl (fun j hj => hvalid1 j (Finset.mem_filter.mp hj).2),
          Finset.sum_const, smul_eq_mul]
        have hfc := card_filter_add_not (Finset.univ : Finset (Fin l)) (fun j : Fin l => j ∈ B)
        rw [Finset.card_univ, Fintype.card_fin] at hfc
        have hBf : (Finset.univ.filter (fun j : Fin l => j ∈ B)).card = B.card := by simp
        congr 1; omega
      rw [hleV]
      have hB_le_l : B.card ≤ l := by omega
      have hcomb : (l - B.card) * (l * m) + B.card * (2 * (l * m)) = (l + B.card) * (l * m) := by
        zify [hB_le_l]; ring
      have hBmul : (l + B.card) * (l * m) ≤ (l + 1) * (l * m) :=
        Nat.mul_le_mul_right (l * m) (by omega)
      omega
    have hle2m : l * v ≤ 2 * m := by
      have h1' : (l + 1) * (l * m) = l * m * (l - 1) + 2 * (l * m) := by
        zify [show 1 ≤ l by omega]; ring
      have hll : l * (l * v) = l * l * v := by ring
      have h2m : l * (2 * m) = 2 * (l * m) := by ring
      have hmul : l * (l * v) ≤ l * (2 * m) := by omega
      exact Nat.le_of_mul_le_mul_left hmul hl.pos
    refine ⟨hle2m, ?_⟩
    have hex_bad : ∃ jb : Fin l, jb ∈ B ∧
        (r' + jb.1 * (t * m)) * a 0 % (l * m) +
        (r' + jb.1 * (t * m)) * a 1 % (l * m) +
        (r' + jb.1 * (t * m)) * a 2 % (l * m) = 2 * (l * m) := by
      by_contra hnone; push Not at hnone
      have hall1 : ∀ j : Fin l, (r' + j.1 * (t * m)) * a 0 % (l * m) +
          (r' + j.1 * (t * m)) * a 1 % (l * m) +
          (r' + j.1 * (t * m)) * a 2 % (l * m) = l * m := by
        intro j
        by_cases hjB : j ∈ B
        · rcases heps_vals j with hv | hv
          · exact hv
          · exact absurd hv (hnone j hjB)
        · exact hvalid1 j hjB
      rw [Finset.sum_congr rfl (fun j _ => hall1 j), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul] at hsum_r'
      have h1' : l * (l * m) = l * m * (l - 1) + l * m := by
        zify [show 1 ≤ l by omega]; ring
      have hll : l * (l * v) = l * l * v := by ring
      have : l * (l * v) ≤ l * m := by omega
      have : l * v ≤ m := Nat.le_of_mul_le_mul_left this hl.pos
      omega
    obtain ⟨jb, hjbB, hjb2⟩ := hex_bad
    have hjb_dvd : l ∣ r' + jb.1 * (t * m) := by
      have hnc := (Finset.mem_filter.mp hjbB).2
      by_contra hnd
      exact hnc (((hl.coprime_iff_not_dvd.mpr hnd).symm).mul_right (coprime_shift_m hr'))
    set jnext : Fin l := ⟨(jb.1 + 1) % l, Nat.mod_lt _ hl.pos⟩
    have hjnext_ne : jnext ≠ jb := by
      intro heq; have hv := congrArg Fin.val heq; dsimp [jnext] at hv
      by_cases hlt : jb.1 + 1 < l
      · rw [Nat.mod_eq_of_lt hlt] at hv; omega
      · have : jb.1 + 1 = l := by omega
        rw [this, Nat.mod_self] at hv; omega
    have hjnext1 := hvalid1 jnext (fun hmem => hjnext_ne (Finset.card_le_one.mp hB1 jnext hmem jb hjbB))
    have hnext_eq : ∀ x : ℕ, (r' + jnext.1 * (t * m)) * x % (l * m) =
        (r' + (jb.1 + 1) * (t * m)) * x % (l * m) := by
      intro x; dsimp [jnext]
      have hdiv : jb.1 + 1 = (jb.1 + 1) % l + l * ((jb.1 + 1) / l) := by
        have := Nat.div_add_mod (jb.1 + 1) l; omega
      have hexp : (r' + (jb.1 + 1) * (t * m)) * x =
          (r' + ((jb.1 + 1) % l) * (t * m)) * x + (l * m) * (t * ((jb.1 + 1) / l) * x) := by
        conv_lhs => rw [hdiv]
        ring
      rw [hexp, Nat.add_mul_mod_self_left]
    rw [hnext_eq (a 0), hnext_eq (a 1), hnext_eq (a 2)] at hjnext1
    have hs0 := mod_shift_step (x := a 0) (t := t) (k := r' + jb.1 * (t * m)) hl.pos hm
    have hs1 := mod_shift_step (x := a 1) (t := t) (k := r' + jb.1 * (t * m)) hl.pos hm
    have hs2 := mod_shift_step (x := a 2) (t := t) (k := r' + jb.1 * (t * m)) hl.pos hm
    have hkadd : r' + jb.1 * (t * m) + t * m = r' + (jb.1 + 1) * (t * m) := by ring
    rw [hkadd, hta0, one_mul] at hs0
    rw [hkadd, hta1] at hs1
    rw [hkadd, hta2, zero_mul, add_zero, if_neg (not_le.mpr (Nat.mod_lt _ hn)), add_zero] at hs2
    have hwrap0 : l * m ≤ (r' + jb.1 * (t * m)) * a 0 % (l * m) + m := by
      by_contra hnw
      rw [if_neg hnw, add_zero] at hs0
      have h1_ge : (r' + (jb.1 + 1) * (t * m)) * a 1 % (l * m) + l * m ≥
          (r' + jb.1 * (t * m)) * a 1 % (l * m) + (l - 1) * m := by
        split_ifs at hs1 <;> omega
      have hlm_eq : m + (l - 1) * m = l * m := by
        zify [show 1 ≤ l by omega]; ring
      omega
    refine ⟨jb, hjb_dvd, ?_⟩
    have : (l - 1) * m + m = l * m := by zify [show 1 ≤ l by omega]; ring
    omega
  · right
    have hvalid2 : ∀ j : Fin l, j ∉ B →
        (r' + j.1 * (t * m)) * a 0 % (l * m) +
        (r' + j.1 * (t * m)) * a 1 % (l * m) +
        (r' + j.1 * (t * m)) * a 2 % (l * m) = 2 * (l * m) := by
      intro j hj
      have hjc : (r' + j.1 * (t * m)).Coprime (l * m) := by
        by_contra hc; exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
      exact (hconst j j0 hjc hj0c).trans h2
    have htot_ge : (2 * l - 1) * (l * m) ≤ ∑ j : Fin l,
        ((r' + j.1 * (t * m)) * a 0 % (l * m) +
         (r' + j.1 * (t * m)) * a 1 % (l * m) +
         (r' + j.1 * (t * m)) * a 2 % (l * m)) := by
      have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin l))
        (fun j : Fin l => j ∈ B) (fun j : Fin l =>
          (r' + j.1 * (t * m)) * a 0 % (l * m) +
          (r' + j.1 * (t * m)) * a 1 % (l * m) +
          (r' + j.1 * (t * m)) * a 2 % (l * m))).symm
      rw [hsplit]
      have hgeB : B.card * (l * m) ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin l => j ∈ B),
          ((r' + j.1 * (t * m)) * a 0 % (l * m) +
           (r' + j.1 * (t * m)) * a 1 % (l * m) +
           (r' + j.1 * (t * m)) * a 2 % (l * m)) := by
        calc B.card * (l * m) = (Finset.univ.filter (fun j : Fin l => j ∈ B)).card * (l * m) := by simp
          _ = ∑ _j ∈ Finset.univ.filter (fun j : Fin l => j ∈ B), (l * m) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum (fun j _ => by rcases heps_vals j with hv | hv <;> omega)
      have hgeV : ∑ j ∈ Finset.univ.filter (fun j : Fin l => j ∉ B),
          ((r' + j.1 * (t * m)) * a 0 % (l * m) +
           (r' + j.1 * (t * m)) * a 1 % (l * m) +
           (r' + j.1 * (t * m)) * a 2 % (l * m)) = (l - B.card) * (2 * (l * m)) := by
        rw [Finset.sum_congr rfl (fun j hj => hvalid2 j (Finset.mem_filter.mp hj).2),
          Finset.sum_const, smul_eq_mul]
        have hfc := card_filter_add_not (Finset.univ : Finset (Fin l)) (fun j : Fin l => j ∈ B)
        rw [Finset.card_univ, Fintype.card_fin] at hfc
        have hBf : (Finset.univ.filter (fun j : Fin l => j ∈ B)).card = B.card := by simp
        congr 1; omega
      rw [hgeV]
      have hB_le_l : B.card ≤ l := by omega
      have hcomb : (l - B.card) * (2 * (l * m)) + B.card * (l * m) = (2 * l - B.card) * (l * m) := by
        zify [hB_le_l, show B.card ≤ 2 * l by omega]; ring
      have := Nat.mul_le_mul_right (l * m) (show 2 * l - 1 ≤ 2 * l - B.card by omega)
      omega
    have hr0lt : r' * a 0 % m < m := Nat.mod_lt _ hm
    have hr1lt : r' * a 1 % m < m := Nat.mod_lt _ hm
    have h1' : (2 * l - 1) * (l * m) = l * m * (l - 1) + l * (l * m) := by
      zify [show 1 ≤ l by omega, show 1 ≤ 2 * l by omega]; ring
    have h2' : l * (r' * a 0 % m + r' * a 1 % m) < l * (2 * m) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hl.pos
    have h3 : l * ((l - 2) * m) < l * (l * v) := by
      have ha : (l - 2) * (l * m) + 2 * (l * m) = l * (l * m) := by
        zify [show 2 ≤ l by omega]; ring
      have hb : l * (2 * m) = 2 * (l * m) := by ring
      have hc : l * ((l - 2) * m) = (l - 2) * (l * m) := by ring
      have hd : l * (l * v) = l * l * v := by ring
      omega
    exact Nat.lt_of_mul_lt_mul_left h3

/-- Helper for Case I when d ∈ {4, 6} and ¬ l ∣ m: derives contradiction from hneed. -/
lemma case_one_d46_contra {l m t b2 g d r1 : ℕ} (hl : l.Prime) (hl7 : 7 ≤ l) (hm : 0 < m)
    (hlm : ¬ l ∣ m) (hgpos : 0 < g) (hmd : m = g * d) (hd46 : d = 4 ∨ d = 6)
    (hgm : g ∣ m) (hgb2 : g ∣ b2) {a : Fin 3 → ℕ}
    (hg : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hsum : ∑ i, a i = l * m) (hb2 : a 2 = l * b2)
    (hr1_cop : r1.Coprime m) (hrb1 : r1 * b2 % m = g)
    (hneed : ∀ r' : ℕ, r'.Coprime m → r' * b2 % m = g →
      ∃ jb : Fin l, l ∣ (r' + jb.1 * (t * m)) ∧
        (l - 1) * m ≤ (r' + jb.1 * (t * m)) * a 0 % (l * m)) : False := by
  by_cases hg1 : g = 1
  · obtain ⟨jb, hjb_dvd, hjb_ge⟩ := hneed r1 hr1_cop hrb1
    obtain ⟨q, hq⟩ := hjb_dvd
    rw [hq, mul_assoc, Nat.mul_mod_mul_left] at hjb_ge
    have hqm : q * a 0 % m ≤ m - 1 := by have := Nat.mod_lt (q * a 0) hm; omega
    have hml : m < l := by rw [hmd, hg1, one_mul]; rcases hd46 with rfl | rfl <;> omega
    have hle1 : l * (q * a 0 % m) ≤ l * (m - 1) := Nat.mul_le_mul_left l hqm
    have hlt2 : l * (m - 1) < (l - 1) * m := by
      zify [show 1 ≤ m by omega, show 1 ≤ l by omega]; nlinarith
    omega
  · set p := g.minFac
    have hp : p.Prime := Nat.minFac_prime hg1
    have hpg : p ∣ g := Nat.minFac_dvd g
    have hpm : p ∣ m := dvd_trans hpg hgm
    have hpb2 : p ∣ b2 := dvd_trans hpg hgb2
    have hpa2 : p ∣ a 2 := by rw [hb2]; exact dvd_mul_of_dvd_right hpb2 l
    have hpa0 : ¬ p ∣ a 0 := by
      intro h0
      have hpa1 : p ∣ a 1 := by
        have hs : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
        have hpn : p ∣ l * m := dvd_mul_of_dvd_right hpm l
        have : p ∣ (a 0 + a 2) + a 1 := by rw [show (a 0 + a 2) + a 1 = l * m by omega]; exact hpn
        exact (Nat.dvd_add_right (dvd_add h0 hpa2)).mp this
      have hpgcd : p ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
        Nat.dvd_gcd h0 (Nat.dvd_gcd hpa1 hpa2)
      rw [hg] at hpgcd
      exact absurd (Nat.le_of_dvd Nat.zero_lt_one hpgcd) (by have := hp.two_le; omega)
    set m' := m / p
    have hmm' : m = p * m' := (Nat.mul_div_cancel' hpm).symm
    have hm'_pos : 0 < m' := by nlinarith
    have hdm' : d ∣ m' := by
      obtain ⟨g', hg'⟩ := hpg
      refine ⟨g', ?_⟩
      have : p * m' = p * (d * g') := by rw [← hmm', hmd, hg']; ring
      exact mul_left_cancel₀ hp.ne_zero this
    have hshift_b2 : ∀ c : ℕ, (r1 + c * m') * b2 % m = g := by
      intro c
      have hmb2 : m ∣ m' * b2 := by
        obtain ⟨b', hb'⟩ := hpb2
        refine ⟨b', ?_⟩
        rw [hmm', hb']; ring
      obtain ⟨k, hk⟩ := hmb2
      have : (r1 + c * m') * b2 = r1 * b2 + m * (c * k) := by
        calc (r1 + c * m') * b2 = r1 * b2 + c * (m' * b2) := by ring
          _ = r1 * b2 + c * (m * k) := by rw [hk]
          _ = r1 * b2 + m * (c * k) := by ring
      rw [this, Nat.add_mul_mod_self_left, hrb1]
    have hlm_cop : l.Coprime m := hl.coprime_iff_not_dvd.mpr hlm
    have hφm : 0 < Nat.totient m := Nat.totient_pos.mpr hm
    set invL := l ^ (Nat.totient m - 1)
    have hinvL : l * invL ≡ 1 [MOD m] := by
      have : l * invL = l ^ Nat.totient m := by
        dsimp [invL]; rw [← pow_succ', Nat.sub_add_cancel hφm]
      rw [this]
      exact Nat.ModEq.pow_totient hlm_cop
    have hp_invL : ¬ p ∣ invL := by
      intro h
      have : p ∣ l * invL := dvd_mul_of_dvd_right h l
      have hmod : (l * invL) % p = 1 % p := hinvL.of_dvd hpm
      rw [Nat.mod_eq_zero_of_dvd this, Nat.mod_eq_of_lt hp.one_lt] at hmod
      omega
    have hbig_val : ∀ c : ℕ, (r1 + c * m').Coprime m →
        (l - 1) * m ≤ l * (((r1 + c * m') * invL * a 0) % m) := by
      intro c hcc
      obtain ⟨jb, hjb_dvd, hjb_ge⟩ := hneed (r1 + c * m') hcc (hshift_b2 c)
      obtain ⟨q, hq⟩ := hjb_dvd
      have hq_mod : q ≡ (r1 + c * m') * invL [MOD m] := by
        have h1 : l * q ≡ r1 + c * m' [MOD m] := by
          rw [← hq]
          have : r1 + c * m' + jb.1 * (t * m) = (r1 + c * m') + m * (jb.1 * t) := by ring
          rw [this]; exact Nat.ModEq.symm (by simp [Nat.ModEq, Nat.add_mul_mod_self_left])
        have h2 : q * (l * invL) ≡ (r1 + c * m') * invL [MOD m] := by
          have : q * (l * invL) = (l * q) * invL := by ring
          rw [this]; exact h1.mul_right invL
        have h3 : q * (l * invL) ≡ q * 1 [MOD m] := (Nat.ModEq.refl q).mul hinvL
        rw [mul_one] at h3
        exact h3.symm.trans h2
      have hqa0 : q * a 0 % m = ((r1 + c * m') * invL * a 0) % m := hq_mod.mul_right (a 0)
      rw [hq, mul_assoc, Nat.mul_mod_mul_left, hqa0] at hjb_ge
      exact hjb_ge
    set w : Fin p → Fin p := fun c =>
      ⟨(((r1 + c.1 * m') * invL * a 0) % m) / m',
        Nat.div_lt_of_lt_mul (by
          calc ((r1 + c.1 * m') * invL * a 0) % m < m := Nat.mod_lt _ hm
            _ = p * m' := hmm'
            _ = m' * p := by ring)⟩
    have hw_inj : Function.Injective w := by
      intro c₁ c₂ hweq
      have hqeq : (w c₁).1 = (w c₂).1 := congrArg Fin.val hweq
      have hmodm' : ∀ c : Fin p, ((r1 + c.1 * m') * invL * a 0) % m % m' =
          (r1 * invL * a 0) % m' := by
        intro c
        rw [hmm', Nat.mod_mul_left_mod]
        have : (r1 + c.1 * m') * invL * a 0 = r1 * invL * a 0 + m' * (c.1 * invL * a 0) := by ring
        rw [this, Nat.add_mul_mod_self_left]
      have hrem : ((r1 + c₁.1 * m') * invL * a 0) % m = ((r1 + c₂.1 * m') * invL * a 0) % m := by
        have d1 := Nat.div_add_mod (((r1 + c₁.1 * m') * invL * a 0) % m) m'
        have d2 := Nat.div_add_mod (((r1 + c₂.1 * m') * invL * a 0) % m) m'
        rw [hmodm' c₁] at d1; rw [hmodm' c₂] at d2
        dsimp [w] at hqeq
        rw [← d1, ← d2, hqeq]
      have hdvd : (m : ℤ) ∣ (((r1 + c₁.1 * m') * invL * a 0 : ℕ) : ℤ) -
          (((r1 + c₂.1 * m') * invL * a 0 : ℕ) : ℤ) :=
        int_dvd_sub_of_emod_eq (by exact_mod_cast hrem)
      have hfac : (((r1 + c₁.1 * m') * invL * a 0 : ℕ) : ℤ) -
          (((r1 + c₂.1 * m') * invL * a 0 : ℕ) : ℤ) =
          (m' : ℤ) * (((c₁.1 : ℤ) - (c₂.1 : ℤ)) * ((invL * a 0 : ℕ) : ℤ)) := by
        push_cast; ring
      rw [hfac] at hdvd
      have hpd : (p : ℤ) ∣ ((c₁.1 : ℤ) - (c₂.1 : ℤ)) * ((invL * a 0 : ℕ) : ℤ) := by
        obtain ⟨k, hk⟩ := hdvd
        refine ⟨k, ?_⟩
        have hm'z : (m' : ℤ) ≠ 0 := by exact_mod_cast hm'_pos.ne'
        apply mul_left_cancel₀ hm'z
        have hmz : (m : ℤ) = (p : ℤ) * (m' : ℤ) := by exact_mod_cast hmm'
        rw [hmz] at hk; linarith
      have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpp.dvd_or_dvd hpd with hcc | hia
      · obtain ⟨k, hk⟩ := hcc
        have h1 := c₁.2; have h2 := c₂.2
        have hk0 : k = 0 := by nlinarith
        rw [hk0, mul_zero] at hk
        exact Fin.ext (by omega)
      · exfalso
        exact (hp.dvd_mul.mp (Int.natCast_dvd_natCast.mp hia)).elim hp_invL hpa0
    have hw_surj : Function.Surjective w :=
      ((Finite.injective_iff_bijective).mp hw_inj).2
    by_cases hpm' : p ∣ m'
    · obtain ⟨c0, hc0⟩ := hw_surj ⟨0, hp.pos⟩
      have hcop0 : (r1 + c0.1 * m').Coprime m := by
        rw [hmm']
        have hcm' : (r1 + c0.1 * m').Coprime m' := by
          rw [Nat.coprime_add_mul_right_left]
          exact hr1_cop.coprime_dvd_right ⟨p, by rw [hmm', mul_comm]⟩
        exact (hcm'.coprime_dvd_right hpm').mul_right hcm'
      have hbig := hbig_val c0.1 hcop0
      have hlt0 : ((r1 + c0.1 * m') * invL * a 0) % m < m' := by
        have hv : (w c0).1 = 0 := congrArg Fin.val hc0
        dsimp [w] at hv
        have hdm := Nat.div_add_mod (((r1 + c0.1 * m') * invL * a 0) % m) m'
        rw [hv, mul_zero, zero_add] at hdm
        rw [← hdm]
        exact Nat.mod_lt _ hm'_pos
      have hp2 : 2 ≤ p := hp.two_le
      have hlt_l : l * (((r1 + c0.1 * m') * invL * a 0) % m) < l * m' :=
        Nat.mul_lt_mul_of_pos_left hlt0 hl.pos
      have h1 : (l - 1) * (2 * m') ≤ (l - 1) * m := by
        calc (l - 1) * (2 * m') ≤ (l - 1) * (p * m') :=
            Nat.mul_le_mul_left (l - 1) (Nat.mul_le_mul_right m' hp2)
          _ = (l - 1) * m := by rw [← hmm']
      have h2 : l * m' ≤ (l - 1) * (2 * m') := by
        have h12 : l ≤ 2 * (l - 1) := by omega
        calc l * m' ≤ (2 * (l - 1)) * m' := Nat.mul_le_mul_right m' h12
          _ = (l - 1) * (2 * m') := by ring
      omega
    · have hpd_not : ¬ p ∣ d := fun h => hpm' (dvd_trans h hdm')
      have hp3 : 3 ≤ p := by
        have h2d : 2 ∣ d := by rcases hd46 with rfl | rfl <;> decide
        have hpne2 : p ≠ 2 := fun h => hpd_not (h ▸ h2d)
        have := hp.two_le; omega
      obtain ⟨c0, hc0⟩ := hw_surj ⟨0, hp.pos⟩
      obtain ⟨c1, hc1⟩ := hw_surj ⟨1, by omega⟩
      have hc01 : c0 ≠ c1 := by
        intro h; rw [h] at hc0
        have := congrArg Fin.val (hc0.symm.trans hc1); simp at this
      have hex_good : ∃ c : Fin p, (c = c0 ∨ c = c1) ∧ ¬ p ∣ r1 + c.1 * m' := by
        by_cases h0 : p ∣ r1 + c0.1 * m'
        · refine ⟨c1, Or.inr rfl, ?_⟩
          intro h1
          have hsub : (p : ℤ) ∣ ((c0.1 : ℤ) - (c1.1 : ℤ)) * (m' : ℤ) := by
            have hz0 : (p : ℤ) ∣ (r1 : ℤ) + (c0.1 : ℤ) * (m' : ℤ) := by exact_mod_cast h0
            have hz1 : (p : ℤ) ∣ (r1 : ℤ) + (c1.1 : ℤ) * (m' : ℤ) := by exact_mod_cast h1
            have hds := dvd_sub hz0 hz1
            have heq : ((r1 : ℤ) + (c0.1 : ℤ) * (m' : ℤ)) - ((r1 : ℤ) + (c1.1 : ℤ) * (m' : ℤ)) =
                ((c0.1 : ℤ) - (c1.1 : ℤ)) * (m' : ℤ) := by ring
            rw [heq] at hds
            exact hds
          have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
          rcases hpp.dvd_or_dvd hsub with hcc | hm'd
          · obtain ⟨k, hk⟩ := hcc
            have := c0.2; have := c1.2
            have hk0 : k = 0 := by
              by_contra hkne
              have hge : (p : ℤ) ≤ |(p : ℤ) * k| := by
                rw [abs_mul, abs_of_pos (by exact_mod_cast hp.pos : (0 : ℤ) < p)]
                have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hkne
                nlinarith
              have hlt : |(c0.1 : ℤ) - (c1.1 : ℤ)| < (p : ℤ) := by
                rw [abs_lt]; constructor <;> omega
              rw [hk] at hlt
              omega
            rw [hk0, mul_zero] at hk
            exact hc01 (Fin.ext (by omega))
          · exact hpm' (Int.natCast_dvd_natCast.mp hm'd)
        · exact ⟨c0, Or.inl rfl, h0⟩
      obtain ⟨c, hc_eq, hndp⟩ := hex_good
      have hcop_c : (r1 + c.1 * m').Coprime m := by
        rw [hmm']
        have hcm' : (r1 + c.1 * m').Coprime m' := by
          rw [Nat.coprime_add_mul_right_left]
          exact hr1_cop.coprime_dvd_right ⟨p, by rw [hmm', mul_comm]⟩
        exact ((hp.coprime_iff_not_dvd.mpr hndp).symm).mul_right hcm'
      have hbig := hbig_val c.1 hcop_c
      have hlt_c : ((r1 + c.1 * m') * invL * a 0) % m < 2 * m' := by
        have hwc : (w c).1 ≤ 1 := by
          rcases hc_eq with rfl | rfl
          · rw [hc0]; simp
          · rw [hc1]
        dsimp [w] at hwc
        have hdm := Nat.div_add_mod (((r1 + c.1 * m') * invL * a 0) % m) m'
        have hmlt := Nat.mod_lt (((r1 + c.1 * m') * invL * a 0) % m) hm'_pos
        have hmul : m' * ((((r1 + c.1 * m') * invL * a 0) % m) / m') ≤ m' * 1 :=
          Nat.mul_le_mul_left m' hwc
        omega
      have hlt_l : l * (((r1 + c.1 * m') * invL * a 0) % m) < l * (2 * m') :=
        Nat.mul_lt_mul_of_pos_left hlt_c hl.pos
      have h1 : (l - 1) * (3 * m') ≤ (l - 1) * m := by
        calc (l - 1) * (3 * m') ≤ (l - 1) * (p * m') :=
            Nat.mul_le_mul_left (l - 1) (Nat.mul_le_mul_right m' hp3)
          _ = (l - 1) * m := by rw [← hmm']
      have h2 : l * (2 * m') ≤ (l - 1) * (3 * m') := by
        have h23 : 2 * l ≤ 3 * (l - 1) := by omega
        calc l * (2 * m') = (2 * l) * m' := by ring
          _ ≤ (3 * (l - 1)) * m' := Nat.mul_le_mul_right m' h23
          _ = (l - 1) * (3 * m') := by ring
      omega

set_option maxHeartbeats 800000 in
/-- Case I: l divides a 2 (and l divides neither a 0 nor a 1). -/
lemma case_one_div_a2 {n l : ℕ} (hl : l.Prime) (hl7 : 7 ≤ l) (hln : l ∣ n)
    {a : Fin 3 → ℕ} (hg : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) {e : Fin 3 → ℚ}
    (hrel : ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k (a i) * e i = 0)
    (ha2 : l ∣ a 2) (ha0 : ¬ l ∣ a 0) (ha1 : ¬ l ∣ a 1) :
    e ∈ trivMod n a := by
  obtain ⟨m, rfl⟩ := hln
  have hm : 0 < m := by
    have hs : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
    have := hpos 0; nlinarith
  have hn : 0 < l * m := Nat.mul_pos hl.pos hm
  obtain ⟨t, ht, hta0⟩ := exists_inv_mod_prime hl ha0
  have hta2 : (t * a 2) % l = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right ha2 t)
  have hta1 : (t * a 1) % l = l - 1 := by
    have hs : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
    have hts : t * a 0 + t * a 1 + t * a 2 = l * (t * m) := by
      calc t * a 0 + t * a 1 + t * a 2 = t * (a 0 + a 1 + a 2) := by ring
        _ = t * (l * m) := by rw [hs]
        _ = l * (t * m) := by ring
    have hmod : (t * a 0 + t * a 1 + t * a 2) % l = 0 := by rw [hts, Nat.mul_mod_right]
    have hmod2 : (t * a 0 % l + t * a 1 % l + t * a 2 % l) % l = 0 := by
      simpa [Nat.add_mod] using hmod
    have hlt1 : (t * a 1) % l < l := Nat.mod_lt _ hl.pos
    have hne0 : (t * a 1) % l ≠ 0 := fun h0 =>
      (hl.dvd_mul.mp (Nat.dvd_of_mod_eq_zero h0)).elim ht ha1
    rw [hta0, hta2, add_zero] at hmod2
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod2
    have hq1 : q = 1 := by
      rcases Nat.eq_zero_or_pos q with rfl | hqpos
      · simp at hq
      · by_contra hne
        have h2 : 2 ≤ q := by omega
        have : 2 * l ≤ l * q := by
          calc 2 * l = l * 2 := by ring
            _ ≤ l * q := Nat.mul_le_mul_left l h2
        omega
    rw [hq1, mul_one] at hq
    omega
  -- Step 1: e 0 = e 1 using r = 1.
  have he01 : e 0 = e 1 := by
    set V := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      (1 + j.1 * (t * m)).Coprime (l * m) ∧ (1 + (j.1 + 1) * (t * m)).Coprime (l * m))
    have hV : l - 2 ≤ V.card := valid_trans_card_ge hl (Nat.coprime_one_left m) ht
    set W0 := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      wrapB l m t (a 0) (1 + j.1 * (t * m)) = true)
    have hW0 : W0.card = 1 := by rw [wrap_count_coset hl.pos hm, hta0]
    set NW1 := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      wrapB l m t (a 1) (1 + j.1 * (t * m)) = false)
    have hNW1 : NW1.card = 1 := by
      have hW1 : ((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
          wrapB l m t (a 1) (1 + j.1 * (t * m)) = true)).card = l - 1 := by
        rw [wrap_count_coset hl.pos hm, hta1]
      have htot := card_filter_add_not (Finset.univ : Finset (Fin l))
        (fun j : Fin l => wrapB l m t (a 1) (1 + j.1 * (t * m)) = true)
      rw [Finset.card_univ, Fintype.card_fin] at htot
      have hNW1_eq : NW1 = (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
          ¬ (wrapB l m t (a 1) (1 + j.1 * (t * m)) = true)) := by
        ext j; simp [NW1]
      rw [hNW1_eq]; omega
    have hdiff_pos : 0 < (V \ (W0 ∪ NW1)).card := by
      have hle : (W0 ∪ NW1).card ≤ 2 := by
        calc (W0 ∪ NW1).card ≤ W0.card + NW1.card := Finset.card_union_le _ _
          _ = 2 := by omega
      have hs := Finset.card_sdiff_add_card_inter V (W0 ∪ NW1)
      have hint : (V ∩ (W0 ∪ NW1)).card ≤ (W0 ∪ NW1).card :=
        Finset.card_le_card Finset.inter_subset_right
      omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hdiff_pos
    rw [Finset.mem_sdiff, Finset.mem_union] at hj
    have hjV := (Finset.mem_filter.mp hj.1).2
    have hnot0 : wrapB l m t (a 0) (1 + j.1 * (t * m)) = false := by
      by_contra h
      have ht0 : wrapB l m t (a 0) (1 + j.1 * (t * m)) = true := by
        cases hv : wrapB l m t (a 0) (1 + j.1 * (t * m)) <;> simp_all
      exact hj.2 (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0⟩))
    have htrue1 : wrapB l m t (a 1) (1 + j.1 * (t * m)) = true := by
      by_contra h
      have hf1 : wrapB l m t (a 1) (1 + j.1 * (t * m)) = false := by
        cases hv : wrapB l m t (a 1) (1 + j.1 * (t * m)) <;> simp_all
      exact hj.2 (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf1⟩))
    have hfalse2 : wrapB l m t (a 2) (1 + j.1 * (t * m)) = false := by
      unfold wrapB
      rw [hta2, zero_mul, add_zero, decide_eq_false_iff_not]
      exact not_le.mpr (Nat.mod_lt _ hn)
    have hjeq := jump_eq hl.pos hm hpos hsum hrel hjV.1 (by
      have : 1 + j.1 * (t * m) + t * m = 1 + (j.1 + 1) * (t * m) := by ring
      rw [this]; exact hjV.2)
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at hjeq
    unfold wrapQ at hjeq
    rw [hnot0, htrue1, hfalse2, hta0, hta1, hta2] at hjeq
    simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add, one_mul, add_zero,
      Nat.cast_one, Nat.cast_zero] at hjeq
    have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
    have hl1 : ((l - 1 : ℕ) : ℚ) = (l : ℚ) - 1 := Nat.cast_sub (by omega)
    rw [hl1, eq_div_iff hlq] at hjeq
    linarith
  -- Step 2: e 0 = 0.
  have he0 : e 0 = 0 := by
    by_contra he0_ne
    have hconst : ∀ r : ℕ, ∀ j₁ j₂ : Fin l,
        (r + j₁.1 * (t * m)).Coprime (l * m) →
        (r + j₂.1 * (t * m)).Coprime (l * m) →
        ((r + j₁.1 * (t * m)) * a 0 % (l * m) + (r + j₁.1 * (t * m)) * a 1 % (l * m) +
          (r + j₁.1 * (t * m)) * a 2 % (l * m)) =
        ((r + j₂.1 * (t * m)) * a 0 % (l * m) + (r + j₂.1 * (t * m)) * a 1 % (l * m) +
          (r + j₂.1 * (t * m)) * a 2 % (l * m)) := by
      intro r j₁ j₂ hc1 hc2
      have h1 := rel_int_eq hn hpos hsum hrel hc1
      have h2 := rel_int_eq hn hpos hsum hrel hc2
      rw [Fin.sum_univ_three] at h1 h2
      rw [← he01] at h1 h2
      have ha2_eq : (r + j₁.1 * (t * m)) * a 2 % (l * m) = (r + j₂.1 * (t * m)) * a 2 % (l * m) := by
        obtain ⟨b2, hb2⟩ := ha2
        have e1 : (r + j₁.1 * (t * m)) * (l * b2) = r * (l * b2) + (l * m) * (j₁.1 * t * b2) := by ring
        have e2 : (r + j₂.1 * (t * m)) * (l * b2) = r * (l * b2) + (l * m) * (j₂.1 * t * b2) := by ring
        rw [hb2, e1, e2, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
      rw [ha2_eq] at h1
      have hq : (2 * (((r + j₁.1 * (t * m)) * a 0 % (l * m) : ℕ) : ℚ) +
          2 * (((r + j₁.1 * (t * m)) * a 1 % (l * m) : ℕ) : ℚ) -
          (2 * (((r + j₂.1 * (t * m)) * a 0 % (l * m) : ℕ) : ℚ) +
           2 * (((r + j₂.1 * (t * m)) * a 1 % (l * m) : ℕ) : ℚ))) * e 0 = 0 := by
        linear_combination h1 - h2
      have hqeq : (((r + j₁.1 * (t * m)) * a 0 % (l * m) + (r + j₁.1 * (t * m)) * a 1 % (l * m) : ℕ) : ℚ) =
          (((r + j₂.1 * (t * m)) * a 0 % (l * m) + (r + j₂.1 * (t * m)) * a 1 % (l * m) : ℕ) : ℚ) := by
        push_cast
        have := (mul_eq_zero.mp hq).resolve_right he0_ne
        linarith
      have hneq : (r + j₁.1 * (t * m)) * a 0 % (l * m) + (r + j₁.1 * (t * m)) * a 1 % (l * m) =
          (r + j₂.1 * (t * m)) * a 0 % (l * m) + (r + j₂.1 * (t * m)) * a 1 % (l * m) := by
        exact_mod_cast hqeq
      omega
    obtain ⟨b2, hb2⟩ := ha2
    have hb2_pos : 0 < b2 := by have := hpos 2; rw [hb2] at this; nlinarith
    have hb2_lt : b2 < m := by have := a_lt_n hpos hsum 2; rw [hb2] at this; nlinarith
    set g := Nat.gcd m b2
    set d := m / g
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hm
    have hmd : m = g * d := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m b2)).symm
    have hd2 : 2 ≤ d := by
      obtain ⟨b1, hb1⟩ := Nat.gcd_dvd_right m b2
      have hb1_pos : 1 ≤ b1 := by
        rcases Nat.eq_zero_or_pos b1 with rfl | h
        · simp at hb1; omega
        · exact h
      have hlt_b1 : b1 < d := by
        have : g * b1 < g * d := by rw [← hb1, ← hmd]; exact hb2_lt
        exact Nat.lt_of_mul_lt_mul_left this
      omega
    obtain ⟨u, hu_cop, hu_lo, hu_hi, hu_strict⟩ := exists_mid_coprime hd2
    obtain ⟨r, hr_cop, hrb2⟩ := exists_r_with_rem hm hb2_pos hb2_lt hu_cop
    rw [Nat.mod_eq_of_lt (by omega : u < d)] at hrb2
    by_cases hlm : l ∣ m
    · -- All j : Fin l give k coprime to l * m!
      have hall_cop : ∀ j : Fin l, (r + j.1 * (t * m)).Coprime (l * m) := fun j =>
        ((coprime_shift_m hr_cop).coprime_dvd_right hlm).mul_right (coprime_shift_m hr_cop)
      have hsum_r : ∑ j : Fin l, ((r + j.1 * (t * m)) * a 0 % (l * m) +
          (r + j.1 * (t * m)) * a 1 % (l * m) +
          (r + j.1 * (t * m)) * a 2 % (l * m)) =
          l * (r * a 0 % m + r * a 1 % m) + l * m * (l - 1) + l * l * (u * g) := by
        have hs0 := sum_rem_coset (r := r) hl hm ht ha0
        have hs1 := sum_rem_coset (r := r) hl hm ht ha1
        have hs2 : ∑ j : Fin l, (r + j.1 * (t * m)) * a 2 % (l * m) = l * (l * (u * g)) := by
          have hterm : ∀ j : Fin l, (r + j.1 * (t * m)) * a 2 % (l * m) = l * (u * g) := by
            intro j; rw [hb2]
            have : (r + j.1 * (t * m)) * (l * b2) = l * (r * b2) + (l * m) * (j.1 * t * b2) := by ring
            rw [this, Nat.add_mul_mod_self_left, Nat.mul_mod_mul_left, hrb2]
          rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hs0, hs1, hs2]
        have htri := two_mul_tri_odd (by omega : 2 ≤ l)
        have hml : m * (l * (l - 1) / 2) + m * (l * (l - 1) / 2) = l * m * (l - 1) := by
          calc m * (l * (l - 1) / 2) + m * (l * (l - 1) / 2)
              = m * (2 * (l * (l - 1) / 2)) := by ring
            _ = m * (l * (l - 1)) := by rw [htri]
            _ = l * m * (l - 1) := by ring
        linarith
      have h0v : r * a 0 % (l * m) + r * a 1 % (l * m) + r * a 2 % (l * m) = l * m ∨
          r * a 0 % (l * m) + r * a 1 % (l * m) + r * a 2 % (l * m) = 2 * (l * m) := by
        have hs : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
        have hmod : (r * a 0 % (l * m) + r * a 1 % (l * m) + r * a 2 % (l * m)) % (l * m) = 0 := by
          have h1 : (r * a 0 % (l * m) + r * a 1 % (l * m) + r * a 2 % (l * m)) % (l * m) =
              (r * a 0 + r * a 1 + r * a 2) % (l * m) := by simp [Nat.add_mod]
          rw [h1, show r * a 0 + r * a 1 + r * a 2 = (l * m) * r by
            calc _ = r * (a 0 + a 1 + a 2) := by ring
              _ = r * (l * m) := by rw [hs]
              _ = (l * m) * r := by ring, Nat.mul_mod_right]
        obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hmod
        have h2pos : 0 < r * a 2 % (l * m) := by
          rw [hb2, show r * (l * b2) = l * (r * b2) by ring, Nat.mul_mod_mul_left, hrb2]
          exact Nat.mul_pos hl.pos (Nat.mul_pos (by omega) hgpos)
        have hl0 := Nat.mod_lt (r * a 0) hn; have hl1 := Nat.mod_lt (r * a 1) hn; have hl2 := Nat.mod_lt (r * a 2) hn
        have hc1 : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with rfl | h
          · simp at hc; omega
          · exact h
        have hc2 : c ≤ 2 := by
          by_contra h
          have h3 : 3 ≤ c := by omega
          have hmul : 3 * (l * m) ≤ l * m * c := by
            calc 3 * (l * m) = (l * m) * 3 := by ring
              _ ≤ (l * m) * c := Nat.mul_le_mul_left (l * m) h3
          omega
        have hc_eq : c = 1 ∨ c = 2 := by omega
        rcases hc_eq with rfl | rfl
        · left; omega
        · right; omega
      rcases h0v with h1 | h2
      · have hall1 : ∀ j : Fin l, (r + j.1 * (t * m)) * a 0 % (l * m) +
            (r + j.1 * (t * m)) * a 1 % (l * m) +
            (r + j.1 * (t * m)) * a 2 % (l * m) = l * m := fun j =>
          (hconst r j ⟨0, hl.pos⟩ (hall_cop j) (hall_cop ⟨0, hl.pos⟩)).trans (by simpa using h1)
        rw [Finset.sum_congr rfl (fun j _ => hall1 j), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul] at hsum_r
        have h1' : l * (l * m) = l * m * (l - 1) + l * m := by zify [show 1 ≤ l by omega]; ring
        have hll : l * (l * (u * g)) = l * l * (u * g) := by ring
        have hle1 : l * (u * g) ≤ m := Nat.le_of_mul_le_mul_left (by omega) hl.pos
        have hle1' : l * u * g ≤ d * g := by
          calc l * u * g = l * (u * g) := by ring
            _ ≤ m := hle1
            _ = g * d := hmd
            _ = d * g := by ring
        have hle_lu : l * u ≤ d := Nat.le_of_mul_le_mul_right hle1' hgpos
        have h6l : 6 * u < l * u := Nat.mul_lt_mul_of_pos_right (by omega : 6 < l) (by omega)
        omega
      · have hall2 : ∀ j : Fin l, (r + j.1 * (t * m)) * a 0 % (l * m) +
            (r + j.1 * (t * m)) * a 1 % (l * m) +
            (r + j.1 * (t * m)) * a 2 % (l * m) = 2 * (l * m) := fun j =>
          (hconst r j ⟨0, hl.pos⟩ (hall_cop j) (hall_cop ⟨0, hl.pos⟩)).trans (by simpa using h2)
        rw [Finset.sum_congr rfl (fun j _ => hall2 j), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul] at hsum_r
        have hr0lt : r * a 0 % m < m := Nat.mod_lt _ hm
        have hr1lt : r * a 1 % m < m := Nat.mod_lt _ hm
        have hbig : l * (2 * (l * m)) = l * m * (l - 1) + (l + 1) * (l * m) := by
          zify [show 1 ≤ l by omega]; ring
        have h2m : l * (r * a 0 % m + r * a 1 % m) < l * (2 * m) :=
          Nat.mul_lt_mul_of_pos_left (by omega) hl.pos
        have hlt2 : (l - 1) * m < l * (u * g) := by
          have h1' : (l - 1) * (l * m) + 2 * (l * m) = (l + 1) * (l * m) := by
            zify [show 1 ≤ l by omega]; ring
          have h3' : l * (2 * m) = 2 * (l * m) := by ring
          have h4' : l * ((l - 1) * m) = (l - 1) * (l * m) := by ring
          have h5' : l * (l * (u * g)) = l * l * (u * g) := by ring
          have : l * ((l - 1) * m) < l * (l * (u * g)) := by linarith
          exact Nat.lt_of_mul_lt_mul_left this
        have hlt2' : (l - 1) * d * g < l * u * g := by
          calc (l - 1) * d * g = (l - 1) * (g * d) := by ring
            _ = (l - 1) * m := by rw [← hmd]
            _ < l * (u * g) := hlt2
            _ = l * u * g := by ring
        have hlt_lu : (l - 1) * d < l * u := Nat.lt_of_mul_lt_mul_right hlt2'
        have h56 : 5 * l ≤ 6 * (l - 1) := by omega
        have ha : 6 * (l * u) ≤ 5 * l * d := by
          calc 6 * (l * u) = l * (6 * u) := by ring
            _ ≤ l * (5 * d) := Nat.mul_le_mul_left l hu_hi
            _ = 5 * l * d := by ring
        have hb : 5 * l * d ≤ 6 * ((l - 1) * d) := by
          calc 5 * l * d ≤ 6 * (l - 1) * d := Nat.mul_le_mul_right d h56
            _ = 6 * ((l - 1) * d) := by ring
        omega
    · -- ¬ l ∣ m: apply case_one_bad_bound and case_one_d46_contra!
      by_cases hd46 : d = 4 ∨ d = 6
      · obtain ⟨r1, hr1_cop, hrb1⟩ := exists_r_with_rem hm hb2_pos hb2_lt (Nat.coprime_one_left d)
        rw [Nat.mod_eq_of_lt (by omega : 1 < d), one_mul] at hrb1
        refine case_one_d46_contra (t := t) hl hl7 hm hlm hgpos hmd hd46
          (Nat.gcd_dvd_left m b2) (Nat.gcd_dvd_right m b2) hg hsum hb2 hr1_cop hrb1 ?_
        intro r' hr' hrb'
        have hlg_gt : m < l * g := by
          have hd6 : d < l := by omega
          calc m = g * d := hmd
            _ < g * l := Nat.mul_lt_mul_of_pos_left hd6 hgpos
            _ = l * g := by ring
        have hlg_lt : l * g < (l - 2) * m := by
          have h1 : l < (l - 2) * d := by rcases hd46 with hd | hd <;> (rw [hd]; omega)
          calc l * g < ((l - 2) * d) * g := Nat.mul_lt_mul_of_pos_right h1 hgpos
            _ = (l - 2) * (g * d) := by ring
            _ = (l - 2) * m := by rw [← hmd]
        rcases case_one_bad_bound hl hl7 hm ht hsum ha0 ha1 hb2 hta0 hta1 hta2 hr' hrb' hgpos hlg_gt (hconst r') with
          ⟨_, hjb⟩ | hbig
        · exact hjb
        · omega
      · push Not at hd46
        obtain ⟨hlo7, hhi7⟩ := hu_strict hd46.1 hd46.2
        have hlv_gt : m < l * (u * g) := by
          have hdu : d < l * u := by
            have h1 : 7 * d < 7 * (l * u) := by
              calc 7 * d < 2 * (7 * d) := by omega
                _ = 7 * (2 * d) := by ring
                _ < 7 * (7 * u) := Nat.mul_lt_mul_of_pos_left hlo7 (by omega)
                _ ≤ l * (7 * u) := Nat.mul_le_mul_right (7 * u) hl7
                _ = 7 * (l * u) := by ring
            omega
          calc m = g * d := hmd
            _ < g * (l * u) := Nat.mul_lt_mul_of_pos_left hdu hgpos
            _ = l * (u * g) := by ring
        rcases case_one_bad_bound hl hl7 hm ht hsum ha0 ha1 hb2 hta0 hta1 hta2 hr_cop hrb2
            (Nat.mul_pos (by omega) hgpos) hlv_gt (hconst r) with
          ⟨hle2, _⟩ | hgt2
        · have hle2' : l * u * g ≤ 2 * d * g := by
            calc l * u * g = l * (u * g) := by ring
              _ ≤ 2 * m := hle2
              _ = 2 * (g * d) := by rw [hmd]
              _ = 2 * d * g := by ring
          have hle_lu : l * u ≤ 2 * d := Nat.le_of_mul_le_mul_right hle2' hgpos
          have h1 : 7 * (2 * d) < 7 * (l * u) := by
            calc 7 * (2 * d) < 7 * (7 * u) := Nat.mul_lt_mul_of_pos_left hlo7 (by omega)
              _ ≤ l * (7 * u) := Nat.mul_le_mul_right (7 * u) hl7
              _ = 7 * (l * u) := by ring
          omega
        · have hgt2' : (l - 2) * d * g < l * u * g := by
            calc (l - 2) * d * g = (l - 2) * (g * d) := by ring
              _ = (l - 2) * m := by rw [← hmd]
              _ < l * (u * g) := hgt2
              _ = l * u * g := by ring
          have hlt_lu : (l - 2) * d < l * u := Nat.lt_of_mul_lt_mul_right hgt2'
          have h57 : 5 * l ≤ 7 * (l - 2) := by omega
          have h1 : 7 * (l * u) < 5 * l * d := by
            calc 7 * (l * u) = l * (7 * u) := by ring
              _ < l * (5 * d) := Nat.mul_lt_mul_of_pos_left hhi7 hl.pos
              _ = 5 * l * d := by ring
          have h2 : 5 * l * d ≤ 7 * ((l - 2) * d) := by
            calc 5 * l * d ≤ 7 * (l - 2) * d := Nat.mul_le_mul_right d h57
              _ = 7 * ((l - 2) * d) := by ring
          omega
  -- Step 3: With e 0 = e 1 = 0, finish from k = 1.
  have he1 : e 1 = 0 := he01.symm.trans he0
  have hk1 := rel_k1_eq hn hpos hsum hrel
  rw [he0, he1, mul_zero, mul_zero, zero_add, zero_add] at hk1
  rcases mul_eq_zero.mp hk1 with ha2_half | he2_zero
  · have h2a2 : 2 * a 2 = l * m := by
      have : (2 * (a 2 : ℚ)) = ((l * m : ℕ) : ℚ) := by linarith
      exact_mod_cast this
    have he_eq : e = e 2 • Pi.single (M := fun _ => ℚ) (2 : Fin 3) (1 : ℚ) := by
      funext i; fin_cases i <;> simp [he0, he1]
    rw [he_eq]
    apply Submodule.smul_mem
    exact Submodule.subset_span (Or.inr ⟨2, h2a2, rfl⟩)
  · have he_zero : e = 0 := by
      funext i; fin_cases i <;> simp [he0, he1, he2_zero]
    rw [he_zero]
    exact Submodule.zero_mem _

/-- Case II, 2-term sublemma: if l ∤ a 0, l ∤ a 1, l ∤ a 2 and e 2 = 0, then e ∈ trivMod n a. -/
lemma case_two_e2_zero {n l : ℕ} (hl : l.Prime) (hl7 : 7 ≤ l) (hln : l ∣ n)
    {a : Fin 3 → ℕ} (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) {e : Fin 3 → ℚ}
    (hrel : ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k (a i) * e i = 0)
    (ha0 : ¬ l ∣ a 0) (ha1 : ¬ l ∣ a 1) (ha2 : ¬ l ∣ a 2) (he2 : e 2 = 0) :
    e ∈ trivMod n a := by
  obtain ⟨m, rfl⟩ := hln
  have hm : 0 < m := by
    have hs : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
    have := hpos 0; nlinarith
  have hn : 0 < l * m := Nat.mul_pos hl.pos hm
  by_cases he0 : e 0 = 0
  · have hk1 := rel_k1_eq hn hpos hsum hrel
    rw [he0, he2, mul_zero, mul_zero, zero_add, add_zero] at hk1
    rcases mul_eq_zero.mp hk1 with h2 | he1
    · have h2a1 : 2 * a 1 = l * m := by
        have : 2 * (a 1 : ℚ) = ((l * m : ℕ) : ℚ) := by linarith
        exact_mod_cast this
      have he_eq : e = e 1 • Pi.single (M := fun _ => ℚ) (1 : Fin 3) (1 : ℚ) := by
        funext i; fin_cases i <;> simp [he0, he2]
      rw [he_eq]; exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨1, h2a1, rfl⟩))
    · have : e = 0 := by funext i; fin_cases i <;> simp [he0, he1, he2]
      rw [this]; exact Submodule.zero_mem _
  by_cases he1 : e 1 = 0
  · have hk1 := rel_k1_eq hn hpos hsum hrel
    rw [he1, he2, mul_zero, mul_zero, add_zero, add_zero] at hk1
    rcases mul_eq_zero.mp hk1 with h2 | h0
    · have h2a0 : 2 * a 0 = l * m := by
        have : 2 * (a 0 : ℚ) = ((l * m : ℕ) : ℚ) := by linarith
        exact_mod_cast this
      have he_eq : e = e 0 • Pi.single (M := fun _ => ℚ) (0 : Fin 3) (1 : ℚ) := by
        funext i; fin_cases i <;> simp [he1, he2]
      rw [he_eq]; exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨0, h2a0, rfl⟩))
    · exact absurd h0 he0
  have hnorm : ∀ (u v : Fin 3), u ≠ v → u ≠ 2 → v ≠ 2 →
      ¬ l ∣ a u → ¬ l ∣ a v → e u ≠ 0 → e v ≠ 0 →
      (e u + e v = 0 ∨ |e v| < |e u|) := by
    intro u v huv hu2 hv2 hau hav heu hev
    obtain ⟨t, ht, htu⟩ := exists_inv_mod_prime hl hau
    set c1 := (t * a v) % l
    have hc1_pos : 1 ≤ c1 := by
      have hne0 : c1 ≠ 0 := fun h0 => (hl.dvd_mul.mp (Nat.dvd_of_mod_eq_zero h0)).elim ht hav
      omega
    have hc1_lt : c1 < l := Nat.mod_lt _ hl.pos
    have hc1_ne_lm1 : c1 ≠ l - 1 := by
      intro heq
      have hs : a u + a v + a 2 = l * m := by
        have h3 : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
        fin_cases u <;> fin_cases v <;> simp_all; omega
      have hts : (t * a u + t * a v + t * a 2) % l = 0 := by
        have : t * a u + t * a v + t * a 2 = l * (t * m) := by
          calc _ = t * (a u + a v + a 2) := by ring
            _ = t * (l * m) := by rw [hs]
            _ = l * (t * m) := by ring
        rw [this, Nat.mul_mod_right]
      have hta2_0 : (t * a 2) % l = 0 := by
        have hm' : (t * a u % l + t * a v % l + t * a 2 % l) % l = 0 := by
          simpa [Nat.add_mod] using hts
        change (t * a u % l + c1 + t * a 2 % l) % l = 0 at hm'
        rw [htu, heq] at hm'
        have hlt2 : (t * a 2) % l < l := Nat.mod_lt _ hl.pos
        have : 1 + (l - 1) = l := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hlt2] at hm'
        exact hm'
      exact (hl.dvd_mul.mp (Nat.dvd_of_mod_eq_zero hta2_0)).elim ht ha2
    set V := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      (1 + j.1 * (t * m)).Coprime (l * m) ∧ (1 + (j.1 + 1) * (t * m)).Coprime (l * m))
    have hV : l - 2 ≤ V.card := valid_trans_card_ge hl (Nat.coprime_one_left m) ht
    set Wu := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
      wrapB l m t (a u) (1 + j.1 * (t * m)) = true)
    have hWu : Wu.card = 1 := by rw [wrap_count_coset hl.pos hm, htu]
    set J := V \ Wu
    have hJ : l - 3 ≤ J.card := by
      have hs := Finset.card_sdiff_add_card_inter V Wu
      have hi : (V ∩ Wu).card ≤ Wu.card := Finset.card_le_card Finset.inter_subset_right
      change l - 3 ≤ (V \ Wu).card
      omega
    have hJeq : ∀ j ∈ J, wrapQ l m t (a v) (1 + j.1 * (t * m)) * e v =
        (e u + (c1 : ℚ) * e v) / (l : ℚ) := by
      intro j hj
      rw [Finset.mem_sdiff] at hj
      have hjV := (Finset.mem_filter.mp hj.1).2
      have hfu : wrapB l m t (a u) (1 + j.1 * (t * m)) = false := by
        by_contra h
        have ht' : wrapB l m t (a u) (1 + j.1 * (t * m)) = true := by
          cases hv' : wrapB l m t (a u) (1 + j.1 * (t * m)) <;> simp_all
        exact hj.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩)
      have hjeq := jump_eq hl.pos hm hpos hsum hrel hjV.1 (by
        have : 1 + j.1 * (t * m) + t * m = 1 + (j.1 + 1) * (t * m) := by ring
        rw [this]; exact hjV.2)
      have hsum3 : ∀ f : Fin 3 → ℚ, ∑ i : Fin 3, f i = f u + f v + f 2 := by
        intro f; rw [Fin.sum_univ_three]
        fin_cases u <;> fin_cases v <;> simp_all; ring
      rw [hsum3, hsum3] at hjeq
      unfold wrapQ at hjeq ⊢
      rw [hfu, he2, htu] at hjeq
      simpa [c1] using hjeq
    obtain ⟨j0, hj0⟩ := Finset.card_pos.mp (by omega : 0 < J.card)
    have h0eq := hJeq j0 hj0
    have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
    by_cases hc1_1 : c1 = 1
    · left
      set Wv := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
        wrapB l m t (a v) (1 + j.1 * (t * m)) = true)
      have hWv : Wv.card = 1 := by rw [wrap_count_coset hl.pos hm]; exact hc1_1
      have hpos_f : 0 < (J \ Wv).card := by
        have hs := Finset.card_sdiff_add_card_inter J Wv
        have hi : (J ∩ Wv).card ≤ Wv.card := Finset.card_le_card Finset.inter_subset_right
        omega
      obtain ⟨jf, hjf⟩ := Finset.card_pos.mp hpos_f
      rw [Finset.mem_sdiff] at hjf
      have hfv : wrapB l m t (a v) (1 + jf.1 * (t * m)) = false := by
        by_contra h
        have ht' : wrapB l m t (a v) (1 + jf.1 * (t * m)) = true := by
          cases hv' : wrapB l m t (a v) (1 + jf.1 * (t * m)) <;> simp_all
        exact hjf.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩)
      have hfeq := hJeq jf hjf.1
      unfold wrapQ at hfeq
      rw [hfv, hc1_1] at hfeq
      simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, Nat.cast_one, one_mul] at hfeq
      exact (div_eq_zero_iff.mp hfeq.symm).resolve_right hlq
    · right
      have hc1_ge2 : (2 : ℚ) ≤ (c1 : ℚ) := by exact_mod_cast (show 2 ≤ c1 by omega)
      have hlmc_ge2 : (2 : ℚ) ≤ ((l : ℚ) - (c1 : ℚ)) := by
        have : (2 : ℚ) + (c1 : ℚ) ≤ (l : ℚ) := by exact_mod_cast (show 2 + c1 ≤ l by omega)
        linarith
      unfold wrapQ at h0eq
      cases hb : wrapB l m t (a v) (1 + j0.1 * (t * m))
      · rw [hb] at h0eq
        simp only [Bool.false_eq_true, ↓reduceIte, zero_mul] at h0eq
        have heq : e u = -((c1 : ℚ) * e v) := by
          have := (div_eq_zero_iff.mp h0eq.symm).resolve_right hlq
          linarith
        have hc1_nn : (0 : ℚ) ≤ (c1 : ℚ) := by linarith
        rw [heq, abs_neg, abs_mul, abs_of_nonneg hc1_nn]
        have habs_pos : 0 < |e v| := abs_pos.mpr hev
        nlinarith
      · rw [hb] at h0eq
        simp only [↓reduceIte, one_mul] at h0eq
        rw [eq_div_iff hlq] at h0eq
        have heq : e u = ((l : ℚ) - (c1 : ℚ)) * e v := by linarith
        have hlc_nn : (0 : ℚ) ≤ (l : ℚ) - (c1 : ℚ) := by linarith
        rw [heq, abs_mul, abs_of_nonneg hlc_nn]
        have habs_pos : 0 < |e v| := abs_pos.mpr hev
        nlinarith
  have hfinish : e 0 + e 1 = 0 → e ∈ trivMod (l * m) a := by
    intro hsum01
    have hk1 := rel_k1_eq hn hpos hsum hrel
    have he1_eq : e 1 = -e 0 := by linarith
    rw [he1_eq, he2, mul_zero, add_zero] at hk1
    have hfac : (2 * ((a 0 : ℚ) - (a 1 : ℚ))) * e 0 = 0 := by linarith
    have ha01 : a 0 = a 1 := by
      have : (a 0 : ℚ) = (a 1 : ℚ) := by
        have := (mul_eq_zero.mp hfac).resolve_right he0; linarith
      exact_mod_cast this
    have he_eq : e = e 0 • (Pi.single (M := fun _ => ℚ) (0 : Fin 3) (1 : ℚ) -
        Pi.single (M := fun _ => ℚ) (1 : Fin 3) (1 : ℚ)) := by
      funext i; fin_cases i <;> simp [he1_eq, he2]
    rw [he_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨0, 1, by decide, ha01, rfl⟩))
  rcases hnorm 0 1 (by decide) (by decide) (by decide) ha0 ha1 he0 he1 with hsum01 | hlt10
  · exact hfinish hsum01
  · rcases hnorm 1 0 (by decide) (by decide) (by decide) ha1 ha0 he1 he0 with hsum10 | hlt01
    · exact hfinish (by linarith)
    · exfalso; linarith

set_option maxHeartbeats 800000 in
/-- Case II, 3-term normalization lemma: when all e_i ≠ 0 and l ∤ a_i, normalizing a 0 gives one of 3 relations. -/
lemma case_two_norm_rel {n l : ℕ} (hl : l.Prime) (hl7 : 7 ≤ l) (hln : l ∣ n)
    {a : Fin 3 → ℕ} (hg : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) {e : Fin 3 → ℚ}
    (hrel : ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k (a i) * e i = 0)
    (ha0 : ¬ l ∣ a 0) (ha1 : ¬ l ∣ a 1) (ha2 : ¬ l ∣ a 2)
    (he0 : e 0 ≠ 0) (he1 : e 1 ≠ 0) (he2 : e 2 ≠ 0) :
    (e 1 + e 2 = 0 ∧ ∃ d : ℤ, d % 2 = 0 ∧ d ≠ 0 ∧ e 0 = (d : ℚ) * e 1) ∨
    (∃ c : ℕ, 1 ≤ c ∧ e 0 - e 1 = (c : ℚ) * (e 1 - e 2)) ∨
    (∃ c : ℕ, 1 ≤ c ∧ e 0 - e 2 = (c : ℚ) * (e 2 - e 1)) := by
  obtain ⟨m, rfl⟩ := hln
  have hm : 0 < m := by
    have hs : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
    have := hpos 0; nlinarith
  have hn : 0 < l * m := Nat.mul_pos hl.pos hm
  obtain ⟨t, ht, hta0⟩ := exists_inv_mod_prime hl ha0
  set c1 := (t * a 1) % l
  set c2 := (t * a 2) % l
  have hc1_pos : 1 ≤ c1 := by
    have : c1 ≠ 0 := fun h0 => (hl.dvd_mul.mp (Nat.dvd_of_mod_eq_zero h0)).elim ht ha1
    omega
  have hc2_pos : 1 ≤ c2 := by
    have : c2 ≠ 0 := fun h0 => (hl.dvd_mul.mp (Nat.dvd_of_mod_eq_zero h0)).elim ht ha2
    omega
  have hc_sum : 1 + c1 + c2 = l := by
    have hs : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
    have hts : (t * a 0 + t * a 1 + t * a 2) % l = 0 := by
      have : t * a 0 + t * a 1 + t * a 2 = l * (t * m) := by
        calc _ = t * (a 0 + a 1 + a 2) := by ring
          _ = t * (l * m) := by rw [hs]
          _ = l * (t * m) := by ring
      rw [this, Nat.mul_mod_right]
    have h1 : c1 < l := Nat.mod_lt _ hl.pos
    have h2 : c2 < l := Nat.mod_lt _ hl.pos
    have hm' : (t * a 0 % l + t * a 1 % l + t * a 2 % l) % l = 0 := by
      simpa [Nat.add_mod] using hts
    change (t * a 0 % l + c1 + c2) % l = 0 at hm'
    rw [hta0] at hm'
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hm'
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with rfl | h
      · simp at hq
      · exact h
    have hq2 : q ≤ 1 := by
      by_contra h
      have h2q : 2 ≤ q := by omega
      have hmul : 2 * l ≤ l * q := by
        calc 2 * l = l * 2 := by ring
          _ ≤ l * q := Nat.mul_le_mul_left l h2q
      omega
    have hqeq : q = 1 := by omega
    rw [hqeq, mul_one] at hq
    exact hq
  set V := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
    (1 + j.1 * (t * m)).Coprime (l * m) ∧ (1 + (j.1 + 1) * (t * m)).Coprime (l * m))
  have hV : l - 2 ≤ V.card := valid_trans_card_ge hl (Nat.coprime_one_left m) ht
  set W0 := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
    wrapB l m t (a 0) (1 + j.1 * (t * m)) = true)
  have hW0 : W0.card = 1 := by rw [wrap_count_coset hl.pos hm, hta0]
  set J := V \ W0
  have hJ : 4 ≤ J.card := by
    have hs := Finset.card_sdiff_add_card_inter V W0
    have hi : (V ∩ W0).card ≤ W0.card := Finset.card_le_card Finset.inter_subset_right
    change 4 ≤ (V \ W0).card
    omega
  set C : ℚ := (e 0 + (c1 : ℚ) * e 1 + (c2 : ℚ) * e 2) / (l : ℚ)
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hJeq : ∀ j ∈ J,
      wrapQ l m t (a 1) (1 + j.1 * (t * m)) * e 1 +
      wrapQ l m t (a 2) (1 + j.1 * (t * m)) * e 2 = C := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    have hjV := (Finset.mem_filter.mp hj.1).2
    have hf0 : wrapB l m t (a 0) (1 + j.1 * (t * m)) = false := by
      by_contra h
      have ht' : wrapB l m t (a 0) (1 + j.1 * (t * m)) = true := by
        cases hv : wrapB l m t (a 0) (1 + j.1 * (t * m)) <;> simp_all
      exact hj.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩)
    have hjeq := jump_eq hl.pos hm hpos hsum hrel hjV.1 (by
      have : 1 + j.1 * (t * m) + t * m = 1 + (j.1 + 1) * (t * m) := by ring
      rw [this]; exact hjV.2)
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at hjeq
    unfold wrapQ at hjeq ⊢
    rw [hf0, hta0] at hjeq
    simpa [C, c1, c2] using hjeq
  let b0 : Fin l → ℕ := fun j => if wrapB l m t (a 0) (1 + j.1 * (t * m)) then 1 else 0
  let b1 : Fin l → ℕ := fun j => if wrapB l m t (a 1) (1 + j.1 * (t * m)) then 1 else 0
  let b2 : Fin l → ℕ := fun j => if wrapB l m t (a 2) (1 + j.1 * (t * m)) then 1 else 0
  let wt : Fin l → ℕ := fun j => b0 j + b1 j + b2 j
  have hwt_le3 : ∀ j : Fin l, wt j ≤ 3 := by
    intro j
    have h0 : b0 j ≤ 1 := by dsimp [b0]; split_ifs <;> omega
    have h1 : b1 j ≤ 1 := by dsimp [b1]; split_ifs <;> omega
    have h2 : b2 j ≤ 1 := by dsimp [b2]; split_ifs <;> omega
    change b0 j + b1 j + b2 j ≤ 3
    omega
  have hsum_wt : ∑ j : Fin l, wt j = l := by
    have hcnt : ∀ i : Fin 3, ∑ j : Fin l,
        (if wrapB l m t (a i) (1 + j.1 * (t * m)) then (1 : ℕ) else 0) = (t * a i) % l := by
      intro i
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      exact wrap_count_coset hl.pos hm
    have h0 := hcnt 0; have h1 := hcnt 1; have h2 := hcnt 2
    rw [hta0] at h0
    change ∑ j : Fin l, (b0 j + b1 j + b2 j) = l
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h0, h1, h2]
    exact hc_sum
  have hwt_le2_of_gt1 : 1 < m → ∀ j : Fin l, wt j ≤ 2 := by
    intro hm1 j
    by_contra hgt2
    have hwt3 : wt j = 3 := by have := hwt_le3 j; omega
    have hb0 : wrapB l m t (a 0) (1 + j.1 * (t * m)) = true := by
      dsimp [wt, b0, b1, b2] at hwt3; cases hv : wrapB l m t (a 0) (1 + j.1 * (t * m)) <;> simp_all <;> split_ifs at hwt3 <;> omega
    have hb1 : wrapB l m t (a 1) (1 + j.1 * (t * m)) = true := by
      dsimp [wt, b0, b1, b2] at hwt3; cases hv : wrapB l m t (a 1) (1 + j.1 * (t * m)) <;> simp_all <;> split_ifs at hwt3 <;> omega
    have hb2 : wrapB l m t (a 2) (1 + j.1 * (t * m)) = true := by
      dsimp [wt, b0, b1, b2] at hwt3; cases hv : wrapB l m t (a 2) (1 + j.1 * (t * m)) <;> simp_all <;> split_ifs at hwt3 <;> omega
    have hs0 := mod_shift_step (l := l) (m := m) (x := a 0) (t := t) (k := 1 + j.1 * (t * m)) hl.pos hm
    have hs1 := mod_shift_step (l := l) (m := m) (x := a 1) (t := t) (k := 1 + j.1 * (t * m)) hl.pos hm
    have hs2 := mod_shift_step (l := l) (m := m) (x := a 2) (t := t) (k := 1 + j.1 * (t * m)) hl.pos hm
    unfold wrapB at hb0 hb1 hb2
    rw [if_pos (of_decide_eq_true hb0)] at hs0
    rw [if_pos (of_decide_eq_true hb1)] at hs1
    rw [if_pos (of_decide_eq_true hb2)] at hs2
    have hlt0 := Nat.mod_lt ((1 + j.1 * (t * m)) * a 0) hn
    have hlt1 := Nat.mod_lt ((1 + j.1 * (t * m)) * a 1) hn
    have hlt2 := Nat.mod_lt ((1 + j.1 * (t * m)) * a 2) hn
    have hcm : (t * a 0 % l) * m + (t * a 1 % l) * m + (t * a 2 % l) * m = l * m := by
      rw [hta0]; calc 1 * m + c1 * m + c2 * m = (1 + c1 + c2) * m := by ring
        _ = l * m := by rw [hc_sum]
    have hsumk_le : (1 + j.1 * (t * m)) * a 0 % (l * m) +
        (1 + j.1 * (t * m)) * a 1 % (l * m) +
        (1 + j.1 * (t * m)) * a 2 % (l * m) ≤ 2 * (l * m) := by
      have hs : a 0 + a 1 + a 2 = l * m := by rw [← hsum, Fin.sum_univ_three]
      set k := 1 + j.1 * (t * m)
      have hmod : (k * a 0 % (l * m) + k * a 1 % (l * m) + k * a 2 % (l * m)) % (l * m) = 0 := by
        have h1 : (k * a 0 % (l * m) + k * a 1 % (l * m) + k * a 2 % (l * m)) % (l * m) =
            (k * a 0 + k * a 1 + k * a 2) % (l * m) := by simp [Nat.add_mod]
        rw [h1, show k * a 0 + k * a 1 + k * a 2 = (l * m) * k by
          calc _ = k * (a 0 + a 1 + a 2) := by ring
            _ = k * (l * m) := by rw [hs]
            _ = (l * m) * k := by ring, Nat.mul_mod_right]
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
      have hq2 : q ≤ 2 := by
        by_contra h
        have h3 : 3 ≤ q := by omega
        have hmul : 3 * (l * m) ≤ l * m * q := by
          calc 3 * (l * m) = (l * m) * 3 := by ring
            _ ≤ (l * m) * q := Nat.mul_le_mul_left (l * m) h3
        omega
      have hle : l * m * q ≤ l * m * 2 := Nat.mul_le_mul_left (l * m) hq2
      omega
    have hnext0 : (1 + j.1 * (t * m) + t * m) * a 0 % (l * m) = 0 := by omega
    have hnext1 : (1 + j.1 * (t * m) + t * m) * a 1 % (l * m) = 0 := by omega
    have hnext2 : (1 + j.1 * (t * m) + t * m) * a 2 % (l * m) = 0 := by omega
    have hk_copm : (1 + j.1 * (t * m) + t * m).Coprime m := by
      have : 1 + j.1 * (t * m) + t * m = 1 + (j.1 + 1) * (t * m) := by ring
      rw [this]; exact coprime_shift_m (Nat.coprime_one_left m)
    have hma : ∀ i : Fin 3, m ∣ a i := by
      intro i
      have h0i : (1 + j.1 * (t * m) + t * m) * a i % (l * m) = 0 := by
        fin_cases i <;> assumption
      have hd : m ∣ (1 + j.1 * (t * m) + t * m) * a i :=
        dvd_trans ⟨l, by ring⟩ (Nat.dvd_of_mod_eq_zero h0i)
      exact hk_copm.symm.dvd_of_dvd_mul_left hd
    have hmgcd : m ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
      Nat.dvd_gcd (hma 0) (Nat.dvd_gcd (hma 1) (hma 2))
    rw [hg] at hmgcd
    exact absurd (Nat.le_of_dvd Nat.zero_lt_one hmgcd) (by omega)
  set Z0 := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l => wt j = 0)
  set Z2 := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l => wt j = 2)
  set Z3 := (Finset.univ : Finset (Fin l)).filter (fun j : Fin l => wt j = 3)
  have hbal : Z0.card = Z2.card + 2 * Z3.card := by
    have hsum_z : ∑ j : Fin l, ((wt j : ℤ) - 1) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      have : ∑ j : Fin l, (wt j : ℤ) = (l : ℤ) := by exact_mod_cast hsum_wt
      linarith
    have hpt : ∀ j : Fin l, ((wt j : ℤ) - 1) =
        (if wt j = 2 then 1 else 0) + (if wt j = 3 then 2 else 0) - (if wt j = 0 then 1 else 0) := by
      intro j
      have hle3 := hwt_le3 j
      interval_cases (wt j) <;> norm_num
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib,
      Finset.sum_add_distrib] at hsum_z
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, mul_one] at hsum_z
    have : (Z0.card : ℤ) = (Z2.card : ℤ) + 2 * (Z3.card : ℤ) := by
      dsimp [Z0, Z2, Z3] at *; linarith
    exact_mod_cast this
  have hnot_all00 : ¬ (∀ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = false ∧
      wrapB l m t (a 2) (1 + j.1 * (t * m)) = false) := by
    intro hall
    have hJZ0 : J ⊆ Z0 := by
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h12 := hall j hj
      have hf0 : wrapB l m t (a 0) (1 + j.1 * (t * m)) = false := by
        rw [Finset.mem_sdiff] at hj
        by_contra h
        have ht' : wrapB l m t (a 0) (1 + j.1 * (t * m)) = true := by
          cases hv : wrapB l m t (a 0) (1 + j.1 * (t * m)) <;> simp_all
        exact hj.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩)
      simp [wt, b0, b1, b2, hf0, h12.1, h12.2]
    have hZ0_ge4 : 4 ≤ Z0.card := le_trans hJ (Finset.card_le_card hJZ0)
    have hZ2_sub : Z2 ⊆ (Finset.univ : Finset (Fin l)) \ J := by
      intro j hj
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hjJ => ?_⟩
      have h0 := (Finset.mem_filter.mp (hJZ0 hjJ)).2
      have h2 := (Finset.mem_filter.mp hj).2
      omega
    by_cases hm1 : 1 < m
    · have hZ3_0 : Z3.card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _; have := hwt_le2_of_gt1 hm1 j; omega
      have hZ2_ge4 : 4 ≤ Z2.card := by omega
      have hcomp_le3 : ((Finset.univ : Finset (Fin l)) \ J).card ≤ 3 := by
        have hbad := bad_trans_card_le_two hl (Nat.coprime_one_left m) ht
        have hsub : (Finset.univ : Finset (Fin l)) \ J ⊆
            ((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
              ¬ ((1 + j.1 * (t * m)).Coprime (l * m) ∧
                 (1 + (j.1 + 1) * (t * m)).Coprime (l * m)))) ∪ W0 := by
          intro j hj
          rw [Finset.mem_sdiff] at hj
          rw [Finset.mem_union]
          by_cases hVmem : j ∈ V
          · right
            by_contra hW; exact hj.2 (Finset.mem_sdiff.mpr ⟨hVmem, hW⟩)
          · left
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hc => hVmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)⟩
        calc _ ≤ _ := Finset.card_le_card hsub
          _ ≤ _ + W0.card := Finset.card_union_le _ _
          _ ≤ 3 := by omega
      have := Finset.card_le_card hZ2_sub
      omega
    · have hmeq1 : m = 1 := by omega
      subst hmeq1
      have hZ3_le1 : Z3.card ≤ 1 := by
        have hsub : Z3 ⊆ (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
            ¬ (1 + (j.1 + 1) * (t * 1)).Coprime (l * 1)) := by
          intro j hj
          rw [Finset.mem_filter] at hj ⊢
          refine ⟨Finset.mem_univ _, fun hcop => ?_⟩
          have hwt3 := hj.2
          have hb0 : wrapB l 1 t (a 0) (1 + j.1 * (t * 1)) = true := by
            dsimp [wt, b0, b1, b2] at hwt3; cases hv : wrapB l 1 t (a 0) (1 + j.1 * (t * 1)) <;> simp_all <;> split_ifs at hwt3 <;> omega
          have hb1 : wrapB l 1 t (a 1) (1 + j.1 * (t * 1)) = true := by
            dsimp [wt, b0, b1, b2] at hwt3; cases hv : wrapB l 1 t (a 1) (1 + j.1 * (t * 1)) <;> simp_all <;> split_ifs at hwt3 <;> omega
          have hb2 : wrapB l 1 t (a 2) (1 + j.1 * (t * 1)) = true := by
            dsimp [wt, b0, b1, b2] at hwt3; cases hv : wrapB l 1 t (a 2) (1 + j.1 * (t * 1)) <;> simp_all <;> split_ifs at hwt3 <;> omega
          have hs0 := mod_shift_step (l := l) (m := 1) (x := a 0) (t := t) (k := 1 + j.1 * (t * 1)) hl.pos (by omega)
          have hs1 := mod_shift_step (l := l) (m := 1) (x := a 1) (t := t) (k := 1 + j.1 * (t * 1)) hl.pos (by omega)
          have hs2 := mod_shift_step (l := l) (m := 1) (x := a 2) (t := t) (k := 1 + j.1 * (t * 1)) hl.pos (by omega)
          unfold wrapB at hb0 hb1 hb2
          rw [if_pos (of_decide_eq_true hb0)] at hs0
          rw [if_pos (of_decide_eq_true hb1)] at hs1
          rw [if_pos (of_decide_eq_true hb2)] at hs2
          have hsumk_le : (1 + j.1 * (t * 1)) * a 0 % (l * 1) +
              (1 + j.1 * (t * 1)) * a 1 % (l * 1) +
              (1 + j.1 * (t * 1)) * a 2 % (l * 1) ≤ 2 * (l * 1) := by
            have hs : a 0 + a 1 + a 2 = l * 1 := by rw [← hsum, Fin.sum_univ_three]
            set k := 1 + j.1 * (t * 1)
            have hmod : (k * a 0 % (l * 1) + k * a 1 % (l * 1) + k * a 2 % (l * 1)) % (l * 1) = 0 := by
              have h1 : (k * a 0 % (l * 1) + k * a 1 % (l * 1) + k * a 2 % (l * 1)) % (l * 1) =
                  (k * a 0 + k * a 1 + k * a 2) % (l * 1) := by simp [Nat.add_mod]
              rw [h1, show k * a 0 + k * a 1 + k * a 2 = (l * 1) * k by
                calc _ = k * (a 0 + a 1 + a 2) := by ring
                  _ = k * (l * 1) := by rw [hs]
                  _ = (l * 1) * k := by ring, Nat.mul_mod_right]
            obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
            have hlt0 := Nat.mod_lt (k * a 0) hn
            have hlt1 := Nat.mod_lt (k * a 1) hn
            have hlt2 := Nat.mod_lt (k * a 2) hn
            have : q ≤ 2 := by nlinarith
            nlinarith
          have hcm : (t * a 0 % l) * 1 + (t * a 1 % l) * 1 + (t * a 2 % l) * 1 = l * 1 := by
            rw [hta0]; change 1 * 1 + c1 * 1 + c2 * 1 = l * 1; omega
          have hnext0 : (1 + j.1 * (t * 1) + t * 1) * a 0 % (l * 1) = 0 := by omega
          have : 1 + j.1 * (t * 1) + t * 1 = 1 + (j.1 + 1) * (t * 1) := by ring
          rw [this] at hnext0
          exact not_dvd_mul_of_coprime hcop (hpos 0) (a_lt_n hpos hsum 0) (Nat.dvd_of_mod_eq_zero hnext0)
        have himg : ((Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
            ¬ (1 + (j.1 + 1) * (t * 1)).Coprime (l * 1))).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro j₁ hj₁ j₂ hj₂
          have hj1' := (Finset.mem_filter.mp hj₁).2
          have hj2' := (Finset.mem_filter.mp hj₂).2
          have hl1 : l ∣ 1 + (j₁.1 + 1) * t := by
            by_contra hnd
            exact hj1' (by simpa [mul_one] using (hl.coprime_iff_not_dvd.mpr hnd).symm)
          have hl2 : l ∣ 1 + (j₂.1 + 1) * t := by
            by_contra hnd
            exact hj2' (by simpa [mul_one] using (hl.coprime_iff_not_dvd.mpr hnd).symm)
          have hsub' : (l : ℤ) ∣ ((j₁.1 : ℤ) - (j₂.1 : ℤ)) * (t : ℤ) := by
            have h1z : (l : ℤ) ∣ 1 + ((j₁.1 : ℤ) + 1) * (t : ℤ) := by exact_mod_cast hl1
            have h2z : (l : ℤ) ∣ 1 + ((j₂.1 : ℤ) + 1) * (t : ℤ) := by exact_mod_cast hl2
            have hds := dvd_sub h1z h2z
            have hsub_eq : (1 + ((j₁.1 : ℤ) + 1) * (t : ℤ)) - (1 + ((j₂.1 : ℤ) + 1) * (t : ℤ)) =
                ((j₁.1 : ℤ) - (j₂.1 : ℤ)) * (t : ℤ) := by ring
            rw [hsub_eq] at hds
            exact hds
          rcases (Nat.prime_iff_prime_int.mp hl).dvd_or_dvd hsub' with hd | hd
          · obtain ⟨k, hk⟩ := hd
            have := j₁.2; have := j₂.2
            have hk0 : k = 0 := by nlinarith
            rw [hk0, mul_zero] at hk; exact Fin.ext (by omega)
          · exact absurd (Int.natCast_dvd_natCast.mp hd) ht
        exact le_trans (Finset.card_le_card hsub) himg
      have hZ2_ge2 : 2 ≤ Z2.card := by omega
      have hZ2_W0 : Z2 ⊆ W0 := by
        intro j hj
        have hwt2 := (Finset.mem_filter.mp hj).2
        by_contra hnotW0
        have hjnotJ : j ∉ J := fun hjJ => by
          have := (Finset.mem_filter.mp (hJZ0 hjJ)).2; omega
        have hjnotV : j ∉ V := fun hjV => hjnotJ (Finset.mem_sdiff.mpr ⟨hjV, hnotW0⟩)
        have hbadj : ¬ ((1 + j.1 * (t * 1)).Coprime (l * 1) ∧
            (1 + (j.1 + 1) * (t * 1)).Coprime (l * 1)) := fun hc =>
          hjnotV (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
        by_cases hc1 : (1 + j.1 * (t * 1)).Coprime (l * 1)
        · have hnc2 : ¬ (1 + (j.1 + 1) * (t * 1)).Coprime (l * 1) := fun hc2 => hbadj ⟨hc1, hc2⟩
          have hd2 : l ∣ 1 + (j.1 + 1) * t := by
            by_contra hnd
            exact hnc2 (by simpa [mul_one] using (hl.coprime_iff_not_dvd.mpr hnd).symm)
          have hwrap_all : ∀ i : Fin 3, wrapB l 1 t (a i) (1 + j.1 * (t * 1)) = true := by
            intro i
            have hsi := mod_shift_step (l := l) (m := 1) (x := a i) (t := t) (k := 1 + j.1 * (t * 1)) hl.pos (by omega)
            have hnext0 : (1 + j.1 * (t * 1) + t * 1) * a i % (l * 1) = 0 := by
              rw [mul_one, mul_one]
              have : 1 + j.1 * t + t = 1 + (j.1 + 1) * t := by ring
              rw [this]
              exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd2 (a i))
            have hci_pos : 0 < (t * a i) % l := by
              fin_cases i
              · dsimp; rw [hta0]; omega
              · exact hc1_pos
              · exact hc2_pos
            rw [hnext0, zero_add] at hsi
            unfold wrapB
            by_contra hf
            have hnw : ¬ (l * 1 ≤ (1 + j.1 * (t * 1)) * a i % (l * 1) + ((t * a i) % l) * 1) := by
              simpa [decide_eq_true_eq] using hf
            rw [if_neg hnw] at hsi
            omega
          have hwt3 : wt j = 3 := by
            dsimp [wt, b0, b1, b2]
            rw [hwrap_all 0, hwrap_all 1, hwrap_all 2]
            decide
          omega
        · have hd1 : l ∣ 1 + j.1 * t := by
            by_contra hnd
            exact hc1 (by simpa [mul_one] using (hl.coprime_iff_not_dvd.mpr hnd).symm)
          have hnowr : ∀ i : Fin 3, wrapB l 1 t (a i) (1 + j.1 * (t * 1)) = false := by
            intro i
            unfold wrapB
            have hzero : (1 + j.1 * (t * 1)) * a i % (l * 1) = 0 := by
              rw [mul_one, mul_one]
              exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd1 (a i))
            rw [hzero, zero_add, mul_one, mul_one, decide_eq_false_iff_not]
            exact not_le.mpr (Nat.mod_lt _ hl.pos)
          have hwt0 : wt j = 0 := by
            dsimp [wt, b0, b1, b2]
            rw [hnowr 0, hnowr 1, hnowr 2]
            decide
          omega
      have := Finset.card_le_card hZ2_W0
      omega
  have hnot_all11 : ¬ (∀ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = true ∧
      wrapB l m t (a 2) (1 + j.1 * (t * m)) = true) := by
    intro hall
    have hJZ2 : J ⊆ Z2 := by
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h12 := hall j hj
      have hf0 : wrapB l m t (a 0) (1 + j.1 * (t * m)) = false := by
        rw [Finset.mem_sdiff] at hj
        by_contra h
        have ht' : wrapB l m t (a 0) (1 + j.1 * (t * m)) = true := by
          cases hv : wrapB l m t (a 0) (1 + j.1 * (t * m)) <;> simp_all
        exact hj.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩)
      simp [wt, b0, b1, b2, hf0, h12.1, h12.2]
    have hZ2_ge4 : 4 ≤ Z2.card := le_trans hJ (Finset.card_le_card hJZ2)
    have hZ0_bad : Z0 ⊆ (Finset.univ : Finset (Fin l)).filter (fun j : Fin l =>
        ¬ ((1 + j.1 * (t * m)).Coprime (l * m) ∧ (1 + (j.1 + 1) * (t * m)).Coprime (l * m))) := by
      intro j hj
      have hwt0 := (Finset.mem_filter.mp hj).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun hVok => ?_⟩
      have hnotW0 : j ∉ W0 := by
        intro hW
        have ht0 := (Finset.mem_filter.mp hW).2
        dsimp [wt, b0] at hwt0; rw [if_pos ht0] at hwt0; omega
      have hjJ : j ∈ J := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hVok⟩, hnotW0⟩
      have hwt2 := (Finset.mem_filter.mp (hJZ2 hjJ)).2
      omega
    have hbad := bad_trans_card_le_two hl (Nat.coprime_one_left m) ht
    have := Finset.card_le_card hZ0_bad
    omega
  have hno_00_10 : ¬ ((∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = false ∧ wrapB l m t (a 2) (1 + j.1 * (t * m)) = false) ∧
                      (∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = true  ∧ wrapB l m t (a 2) (1 + j.1 * (t * m)) = false)) := by
    rintro ⟨⟨j₁, h1, hf1, hf2⟩, ⟨j₂, h2, ht1, hf2'⟩⟩
    have eq1 := hJeq j₁ h1; have eq2 := hJeq j₂ h2
    unfold wrapQ at eq1 eq2
    rw [hf1, hf2] at eq1; rw [ht1, hf2'] at eq2
    simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero, one_mul] at eq1 eq2
    exact he1 (by linarith)
  have hno_00_01 : ¬ ((∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = false ∧ wrapB l m t (a 2) (1 + j.1 * (t * m)) = false) ∧
                      (∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = false ∧ wrapB l m t (a 2) (1 + j.1 * (t * m)) = true)) := by
    rintro ⟨⟨j₁, h1, hf1, hf2⟩, ⟨j₂, h2, hf1', ht2⟩⟩
    have eq1 := hJeq j₁ h1; have eq2 := hJeq j₂ h2
    unfold wrapQ at eq1 eq2
    rw [hf1, hf2] at eq1; rw [hf1', ht2] at eq2
    simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add, add_zero, one_mul] at eq1 eq2
    exact he2 (by linarith)
  have hno_10_01 : ¬ ((∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = true  ∧ wrapB l m t (a 2) (1 + j.1 * (t * m)) = false) ∧
                      (∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = false ∧ wrapB l m t (a 2) (1 + j.1 * (t * m)) = true)) := by
    rintro ⟨⟨j₁, h1, ht1, hf2⟩, ⟨j₂, h2, hf1, ht2⟩⟩
    have eq1 := hJeq j₁ h1; have eq2 := hJeq j₂ h2
    unfold wrapQ at eq1 eq2
    rw [ht1, hf2] at eq1; rw [hf1, ht2] at eq2
    simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add, add_zero, one_mul] at eq1 eq2
    have he12 : e 1 = e 2 := by linarith
    have he1C : e 1 = C := eq1
    dsimp [C] at he1C
    rw [eq_div_iff hlq, ← he12] at he1C
    have hcsum_q : (1 : ℚ) + (c1 : ℚ) + (c2 : ℚ) = (l : ℚ) := by exact_mod_cast hc_sum
    have he01 : e 0 = e 1 := by linear_combination -he1C - e 1 * hcsum_q
    exact he0 (all_eq_zero_of_eq hn hpos hsum hrel he01 he12)
  by_cases h00 : ∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = false ∧
      wrapB l m t (a 2) (1 + j.1 * (t * m)) = false
  · have h11 : ∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = true ∧
        wrapB l m t (a 2) (1 + j.1 * (t * m)) = true := by
      by_contra hno11
      apply hnot_all00
      intro j hj
      cases hv1 : wrapB l m t (a 1) (1 + j.1 * (t * m)) <;>
        cases hv2 : wrapB l m t (a 2) (1 + j.1 * (t * m))
      · exact ⟨rfl, rfl⟩
      · exact absurd ⟨h00, ⟨j, hj, hv1, hv2⟩⟩ hno_00_01
      · exact absurd ⟨h00, ⟨j, hj, hv1, hv2⟩⟩ hno_00_10
      · exact absurd ⟨j, hj, hv1, hv2⟩ hno11
    obtain ⟨j₁, h1, hf1, hf2⟩ := h00
    obtain ⟨j₂, h2, ht1, ht2⟩ := h11
    have eq1 := hJeq j₁ h1; have eq2 := hJeq j₂ h2
    unfold wrapQ at eq1 eq2
    rw [hf1, hf2] at eq1; rw [ht1, ht2] at eq2
    simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero, one_mul] at eq1 eq2
    have hsum12 : e 1 + e 2 = 0 := by linarith
    have hC0 : C = 0 := eq1.symm
    dsimp [C] at hC0
    have hnum0 : e 0 + (c1 : ℚ) * e 1 + (c2 : ℚ) * e 2 = 0 := (div_eq_zero_iff.mp hC0).resolve_right hlq
    have he2_eq : e 2 = -e 1 := by linarith
    rw [he2_eq] at hnum0
    left
    refine ⟨hsum12, (c2 : ℤ) - (c1 : ℤ), ?_, ?_, ?_⟩
    · have hl_odd : l % 2 = 1 := by
        have h2 : ¬ 2 ∣ l := fun h => by
          rcases hl.eq_one_or_self_of_dvd 2 h with h' | h' <;> omega
        omega
      omega
    · intro hd0
      have hceq : (c2 : ℚ) = (c1 : ℚ) := by
        have : (c2 : ℤ) = (c1 : ℤ) := by omega
        exact_mod_cast this
      rw [hceq] at hnum0
      exact he0 (by linarith)
    · push_cast; linarith
  · by_cases h10 : ∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = true ∧
        wrapB l m t (a 2) (1 + j.1 * (t * m)) = false
    · obtain ⟨j₁, h1, ht1, hf2⟩ := h10
      have eq1 := hJeq j₁ h1
      unfold wrapQ at eq1
      rw [ht1, hf2] at eq1
      simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero, one_mul] at eq1
      dsimp [C] at eq1
      rw [eq_div_iff hlq] at eq1
      have hcsum_q : (1 : ℚ) + (c1 : ℚ) + (c2 : ℚ) = (l : ℚ) := by exact_mod_cast hc_sum
      right; left
      exact ⟨c2, hc2_pos, by linear_combination -eq1 - e 1 * hcsum_q⟩
    · by_cases h01 : ∃ j ∈ J, wrapB l m t (a 1) (1 + j.1 * (t * m)) = false ∧
          wrapB l m t (a 2) (1 + j.1 * (t * m)) = true
      · obtain ⟨j₁, h1, hf1, ht2⟩ := h01
        have eq1 := hJeq j₁ h1
        unfold wrapQ at eq1
        rw [hf1, ht2] at eq1
        simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add, one_mul] at eq1
        dsimp [C] at eq1
        rw [eq_div_iff hlq] at eq1
        have hcsum_q : (1 : ℚ) + (c1 : ℚ) + (c2 : ℚ) = (l : ℚ) := by exact_mod_cast hc_sum
        right; right
        exact ⟨c1, hc1_pos, by linear_combination -eq1 - e 2 * hcsum_q⟩
      · exfalso
        apply hnot_all11
        intro j hj
        cases hv1 : wrapB l m t (a 1) (1 + j.1 * (t * m)) <;>
          cases hv2 : wrapB l m t (a 2) (1 + j.1 * (t * m))
        · exact absurd ⟨j, hj, hv1, hv2⟩ h00
        · exact absurd ⟨j, hj, hv1, hv2⟩ h01
        · exact absurd ⟨j, hj, hv1, hv2⟩ h10
        · exact ⟨rfl, rfl⟩

lemma abc_contradiction {x y z : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hneq : ¬ (x = y ∧ y = z))
    (h0 : (y + z = 0 ∧ ∃ d : ℤ, d % 2 = 0 ∧ d ≠ 0 ∧ x = (d : ℚ) * y) ∨
          (∃ c : ℕ, 1 ≤ c ∧ x - y = (c : ℚ) * (y - z)) ∨
          (∃ c : ℕ, 1 ≤ c ∧ x - z = (c : ℚ) * (z - y)))
    (h1 : (z + x = 0 ∧ ∃ d : ℤ, d % 2 = 0 ∧ d ≠ 0 ∧ y = (d : ℚ) * z) ∨
          (∃ c : ℕ, 1 ≤ c ∧ y - z = (c : ℚ) * (z - x)) ∨
          (∃ c : ℕ, 1 ≤ c ∧ y - x = (c : ℚ) * (x - z)))
    (h2 : (x + y = 0 ∧ ∃ d : ℤ, d % 2 = 0 ∧ d ≠ 0 ∧ z = (d : ℚ) * x) ∨
          (∃ c : ℕ, 1 ≤ c ∧ z - x = (c : ℚ) * (x - y)) ∨
          (∃ c : ℕ, 1 ≤ c ∧ z - y = (c : ℚ) * (y - x))) : False := by
  have hnoA : ∀ (u v w : ℚ), u ≠ 0 → v ≠ 0 → w ≠ 0 →
      (v + w = 0 ∧ ∃ d : ℤ, d % 2 = 0 ∧ d ≠ 0 ∧ u = (d : ℚ) * v) →
      ((w + u = 0 ∧ ∃ d : ℤ, d % 2 = 0 ∧ d ≠ 0 ∧ v = (d : ℚ) * w) ∨
       (∃ c : ℕ, 1 ≤ c ∧ v - w = (c : ℚ) * (w - u)) ∨
       (∃ c : ℕ, 1 ≤ c ∧ v - u = (c : ℚ) * (u - w))) →
      ((u + v = 0 ∧ ∃ d : ℤ, d % 2 = 0 ∧ d ≠ 0 ∧ w = (d : ℚ) * u) ∨
       (∃ c : ℕ, 1 ≤ c ∧ w - u = (c : ℚ) * (u - v)) ∨
       (∃ c : ℕ, 1 ≤ c ∧ w - v = (c : ℚ) * (v - u))) → False := by
    intro u v w hu hv hw ⟨hvw, d, hd_ev, hd_ne, hu_eq⟩ hv_rel hw_rel
    have hw_eq : w = -v := by linarith
    have hnot_vA : ¬ (w + u = 0 ∧ ∃ d' : ℤ, d' % 2 = 0 ∧ d' ≠ 0 ∧ v = (d' : ℚ) * w) := by
      rintro ⟨hwu, _⟩
      have : ((d : ℚ) - 1) * v = 0 := by linarith
      have hd1 : (d : ℚ) = 1 := by
        have := (mul_eq_zero.mp this).resolve_right hv; linarith
      have : d = 1 := by exact_mod_cast hd1
      omega
    have hnot_wA : ¬ (u + v = 0 ∧ ∃ d' : ℤ, d' % 2 = 0 ∧ d' ≠ 0 ∧ w = (d' : ℚ) * u) := by
      rintro ⟨huv, _⟩
      have : ((d : ℚ) + 1) * v = 0 := by linarith
      have hd1 : (d : ℚ) = -1 := by
        have := (mul_eq_zero.mp this).resolve_right hv; linarith
      have : d = -1 := by exact_mod_cast hd1
      omega
    have hd_neg2 : d = -2 := by
      rcases hv_rel with hA | ⟨c, hc1, hB⟩ | ⟨c, hc1, hC⟩
      · exact absurd hA hnot_vA
      · rw [hu_eq, hw_eq] at hB
        have hfac : ((2 : ℚ) + (c : ℚ) * (1 + (d : ℚ))) * v = 0 := by linarith
        have heq0 : (2 : ℚ) + (c : ℚ) * (1 + (d : ℚ)) = 0 :=
          (mul_eq_zero.mp hfac).resolve_right hv
        have hz : (2 : ℤ) + (c : ℤ) * (1 + d) = 0 := by exact_mod_cast heq0
        have hc1z : (1 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc1
        have hd_cases : d ≤ -4 ∨ d = -2 ∨ 2 ≤ d := by omega
        rcases hd_cases with hle | rfl | hge
        · nlinarith
        · rfl
        · nlinarith
      · rw [hu_eq, hw_eq] at hC
        have hfac : (1 - (d : ℚ) - (c : ℚ) * ((d : ℚ) + 1)) * v = 0 := by linarith
        have heq0 : 1 - (d : ℚ) - (c : ℚ) * ((d : ℚ) + 1) = 0 :=
          (mul_eq_zero.mp hfac).resolve_right hv
        have hz : (1 : ℤ) - d - (c : ℤ) * (d + 1) = 0 := by exact_mod_cast heq0
        have hc1z : (1 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc1
        have hd_cases : d ≤ -2 ∨ 2 ≤ d := by omega
        rcases hd_cases with hle | hge
        · nlinarith
        · nlinarith
    subst hd_neg2
    rcases hw_rel with hA | ⟨c, hc1, hB⟩ | ⟨c, hc1, hC⟩
    · exact hnot_wA hA
    · rw [hu_eq, hw_eq] at hB
      have hfac : (1 + 3 * (c : ℚ)) * v = 0 := by push_cast at hB; linarith
      have : (1 : ℚ) + 3 * (c : ℚ) = 0 := (mul_eq_zero.mp hfac).resolve_right hv
      have : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
      linarith
    · rw [hu_eq, hw_eq] at hC
      have hfac : (2 + 3 * (c : ℚ)) * v = 0 := by push_cast at hC; linarith
      have : (2 : ℚ) + 3 * (c : ℚ) = 0 := (mul_eq_zero.mp hfac).resolve_right hv
      have : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
      linarith
  rcases h0 with h0A | h0BC
  · exact hnoA x y z hx hy hz h0A h1 h2
  rcases h1 with h1A | h1BC
  · exact hnoA y z x hy hz hx h1A h2 (Or.inr h0BC)
  rcases h2 with h2A | h2BC
  · exact hnoA z x y hz hx hy h2A (Or.inr h0BC) (Or.inr h1BC)
  have hbc_step : ∀ (u v w : ℚ),
      ((∃ c : ℕ, 1 ≤ c ∧ u - v = (c : ℚ) * (v - w)) ∨
       (∃ c : ℕ, 1 ≤ c ∧ u - w = (c : ℚ) * (w - v))) →
      v ≠ w → |v - w| < max |w - u| |u - v| := by
    intro u v w hbc hne3
    have hvw_pos : 0 < |v - w| := abs_pos.mpr (sub_ne_zero.mpr hne3)
    rcases hbc with ⟨c, hc1, heq⟩ | ⟨c, hc1, heq⟩
    · by_cases hc1eq : c = 1
      · subst hc1eq; simp at heq
        have hlt : |v - w| < |w - u| := by
          have : |w - u| = 2 * |v - w| := by
            rw [show w - u = -(2 * (v - w)) by linarith, abs_neg, abs_mul,
              abs_of_pos (show (0 : ℚ) < 2 by norm_num)]
          linarith
        exact lt_max_of_lt_left hlt
      · have hc2 : (2 : ℚ) ≤ (c : ℚ) := by exact_mod_cast (show 2 ≤ c by omega)
        have hcpos : (0 : ℚ) < (c : ℚ) := by linarith
        have hlt : |v - w| < |u - v| := by
          rw [heq, abs_mul, abs_of_pos hcpos]
          nlinarith
        exact lt_max_of_lt_right hlt
    · by_cases hc1eq : c = 1
      · subst hc1eq; simp at heq
        have hlt : |v - w| < |u - v| := by
          have : |u - v| = 2 * |v - w| := by
            rw [show u - v = -(2 * (v - w)) by linarith, abs_neg, abs_mul,
              abs_of_pos (show (0 : ℚ) < 2 by norm_num)]
          linarith
        exact lt_max_of_lt_right hlt
      · have hc2 : (2 : ℚ) ≤ (c : ℚ) := by exact_mod_cast (show 2 ≤ c by omega)
        have hcpos : (0 : ℚ) < (c : ℚ) := by linarith
        have hlt : |v - w| < |w - u| := by
          rw [show w - u = -(u - w) by ring, abs_neg, heq, abs_mul, abs_of_pos hcpos,
            show w - v = -(v - w) by ring, abs_neg]
          nlinarith
        exact lt_max_of_lt_left hlt
  have hxy : x ≠ y := by
    intro heq
    rcases h2BC with ⟨c, _, h⟩ | ⟨c, _, h⟩
    · rw [heq, sub_self, mul_zero] at h; exact hneq ⟨heq, by linarith⟩
    · rw [heq, sub_self, mul_zero] at h; exact hneq ⟨heq, by linarith⟩
  have hyz : y ≠ z := by
    intro heq
    rcases h0BC with ⟨c, _, h⟩ | ⟨c, _, h⟩
    · rw [heq, sub_self, mul_zero] at h; exact hneq ⟨by linarith, heq⟩
    · rw [heq, sub_self, mul_zero] at h; exact hneq ⟨by linarith, heq⟩
  have hzx : z ≠ x := by
    intro heq
    rcases h1BC with ⟨c, _, h⟩ | ⟨c, _, h⟩
    · rw [heq, sub_self, mul_zero] at h; exact hneq ⟨by linarith, by linarith⟩
    · rw [heq, sub_self, mul_zero] at h; exact hneq ⟨by linarith, by linarith⟩
  have hlt0 := hbc_step x y z h0BC hyz
  have hlt1 := hbc_step y z x h1BC hzx
  have hlt2 := hbc_step z x y h2BC hxy
  rcases lt_max_iff.mp hlt0 with h0a | h0b <;>
    rcases lt_max_iff.mp hlt1 with h1a | h1b <;>
    rcases lt_max_iff.mp hlt2 with h2a | h2b <;> linarith

lemma perm_trivMod {n : ℕ} {a : Fin 3 → ℕ} {e : Fin 3 → ℚ} (σ : Equiv.Perm (Fin 3))
    (h : e ∘ σ ∈ trivMod n (a ∘ σ)) : e ∈ trivMod n a := by
  set L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) := (LinearEquiv.funCongrLeft ℚ ℚ σ.symm).toLinearMap
  have hL : L (e ∘ σ) = e := by
    funext i; simp [L]
  rw [← hL]
  have hmap : Submodule.map L (trivMod n (a ∘ σ)) ≤ trivMod n a := by
    unfold trivMod
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    apply Submodule.subset_span
    rcases hv with ⟨i, j, hij, haij, rfl⟩ | ⟨i, hi, rfl⟩
    · left
      refine ⟨σ i, σ j, fun h => hij (σ.injective h), haij, ?_⟩
      funext k
      simp [L, Pi.single_apply, Equiv.symm_apply_eq]
    · right
      refine ⟨σ i, hi, ?_⟩
      funext k
      simp [L, Pi.single_apply, Equiv.symm_apply_eq]
  exact hmap (Submodule.mem_map_of_mem h)

lemma perm_rel {n : ℕ} {a : Fin 3 → ℕ} {e : Fin 3 → ℚ} (σ : Equiv.Perm (Fin 3))
    (hrel : ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k (a i) * e i = 0) :
    ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k ((a ∘ σ) i) * (e ∘ σ) i = 0 := by
  intro k hk
  have := Equiv.sum_comp σ (fun i => sawQ n k (a i) * e i)
  simpa using this.trans (hrel k hk)

lemma perm_gcd {a : Fin 3 → ℕ} (σ : Equiv.Perm (Fin 3))
    (hg : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    Nat.gcd ((a ∘ σ) 0) (Nat.gcd ((a ∘ σ) 1) ((a ∘ σ) 2)) = 1 := by
  have hiff : ∀ d : ℕ, d ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) ↔ ∀ i : Fin 3, d ∣ a i := by
    intro d
    simp only [Nat.dvd_gcd_iff]
    constructor
    · intro ⟨h0, h1, h2⟩ i; fin_cases i <;> assumption
    · intro h; exact ⟨h 0, h 1, h 2⟩
  apply Nat.eq_one_of_dvd_one
  rw [← hg, hiff]
  intro i
  have h1 : ∀ j : Fin 3, Nat.gcd ((a ∘ σ) 0) (Nat.gcd ((a ∘ σ) 1) ((a ∘ σ) 2)) ∣ (a ∘ σ) j := by
    intro j
    have hd := dvd_refl (Nat.gcd ((a ∘ σ) 0) (Nat.gcd ((a ∘ σ) 1) ((a ∘ σ) 2)))
    simp only [Nat.dvd_gcd_iff] at hd
    fin_cases j
    · exact hd.1
    · exact hd.2.1
    · exact hd.2.2
  simpa using h1 (σ.symm i)

theorem main_prime_ge7 (n : ℕ) (a : Fin 3 → ℕ)
    (hl_ex : ∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ l ∣ n)
    (hg : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (e : Fin 3 → ℚ)
    (hrel : ∀ k : ℕ, k.Coprime n → ∑ i, sawQ n k (a i) * e i = 0) :
    e ∈ trivMod n a := by
  obtain ⟨l, hl, hl7, hln⟩ := hl_ex
  have hn : 0 < n := by
    have := hpos 0; have := hpos 1; have := hpos 2
    have hs : a 0 + a 1 + a 2 = n := by rw [← hsum, Fin.sum_univ_three]
    omega
  have hat_most_one : ∀ i j : Fin 3, i ≠ j → l ∣ a i → ¬ l ∣ a j := by
    intro i j hij hdi hdj
    have hdk : ∀ k : Fin 3, l ∣ a k := by
      have hs : a 0 + a 1 + a 2 = n := by rw [← hsum, Fin.sum_univ_three]
      intro k
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
      all_goals
        first
        | exact (Nat.dvd_add_right (dvd_add ‹l ∣ a 0› ‹l ∣ a 1›)).mp (by rwa [hs])
        | exact (Nat.dvd_add_right (dvd_add ‹l ∣ a 0› ‹l ∣ a 2›)).mp (by rw [show a 0 + a 2 + a 1 = n by omega]; exact hln)
        | exact (Nat.dvd_add_right (dvd_add ‹l ∣ a 1› ‹l ∣ a 2›)).mp (by rw [show a 1 + a 2 + a 0 = n by omega]; exact hln)
    have hlg := Nat.dvd_gcd (hdk 0) (Nat.dvd_gcd (hdk 1) (hdk 2))
    rw [hg] at hlg
    exact absurd (Nat.le_of_dvd Nat.zero_lt_one hlg) (by omega)
  have hsw02 : Equiv.swap (0 : Fin 3) 2 1 = 1 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hsw12 : Equiv.swap (1 : Fin 3) 2 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  by_cases h2 : l ∣ a 2
  · exact case_one_div_a2 hl hl7 hln hg hpos hsum hrel h2
      (hat_most_one 2 0 (by decide) h2) (hat_most_one 2 1 (by decide) h2)
  by_cases h0 : l ∣ a 0
  · set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    apply perm_trivMod σ
    exact case_one_div_a2 hl hl7 hln (perm_gcd σ hg) (fun i => hpos (σ i))
      ((Equiv.sum_comp σ a).trans hsum) (perm_rel σ hrel)
      (by simpa [σ] using h0)
      (by simpa [σ] using h2)
      (by simpa [σ, hsw02] using hat_most_one 0 1 (by decide) h0)
  by_cases h1 : l ∣ a 1
  · set σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    apply perm_trivMod σ
    exact case_one_div_a2 hl hl7 hln (perm_gcd σ hg) (fun i => hpos (σ i))
      ((Equiv.sum_comp σ a).trans hsum) (perm_rel σ hrel)
      (by simpa [σ] using h1)
      (by simpa [σ, hsw12] using h0)
      (by simpa [σ] using h2)
  by_cases he2 : e 2 = 0
  · exact case_two_e2_zero hl hl7 hln hpos hsum hrel h0 h1 h2 he2
  by_cases he0 : e 0 = 0
  · set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    apply perm_trivMod σ
    exact case_two_e2_zero hl hl7 hln (fun i => hpos (σ i))
      ((Equiv.sum_comp σ a).trans hsum) (perm_rel σ hrel)
      (by simpa [σ] using h2) (by simpa [σ, hsw02] using h1) (by simpa [σ] using h0)
      (by simpa [σ] using he0)
  by_cases he1 : e 1 = 0
  · set σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    apply perm_trivMod σ
    exact case_two_e2_zero hl hl7 hln (fun i => hpos (σ i))
      ((Equiv.sum_comp σ a).trans hsum) (perm_rel σ hrel)
      (by simpa [σ, hsw12] using h0) (by simpa [σ] using h2) (by simpa [σ] using h1)
      (by simpa [σ] using he1)
  exfalso
  have hneq : ¬ (e 0 = e 1 ∧ e 1 = e 2) := fun ⟨h01, h12⟩ =>
    he0 (all_eq_zero_of_eq hn hpos hsum hrel h01 h12)
  have r0 := case_two_norm_rel hl hl7 hln hg hpos hsum hrel h0 h1 h2 he0 he1 he2
  set σ1 : Equiv.Perm (Fin 3) :=
    { toFun := ![1, 2, 0]
      invFun := ![2, 0, 1]
      left_inv := fun i => by fin_cases i <;> decide
      right_inv := fun i => by fin_cases i <;> decide }
  have r1 := case_two_norm_rel hl hl7 hln (perm_gcd σ1 hg) (fun i => hpos (σ1 i))
    ((Equiv.sum_comp σ1 a).trans hsum) (perm_rel σ1 hrel)
    (by simpa [σ1] using h1) (by simpa [σ1] using h2) (by simpa [σ1] using h0)
    (by simpa [σ1] using he1) (by simpa [σ1] using he2) (by simpa [σ1] using he0)
  set σ2 : Equiv.Perm (Fin 3) := σ1.symm
  have r2 := case_two_norm_rel hl hl7 hln (perm_gcd σ2 hg) (fun i => hpos (σ2 i))
    ((Equiv.sum_comp σ2 a).trans hsum) (perm_rel σ2 hrel)
    (by simpa [σ2, σ1] using h2) (by simpa [σ2, σ1] using h0) (by simpa [σ2, σ1] using h1)
    (by simpa [σ2, σ1] using he2) (by simpa [σ2, σ1] using he0) (by simpa [σ2, σ1] using he1)
  exact abc_contradiction he0 he1 he2 hneq r0 (by simpa [σ1] using r1) (by simpa [σ2, σ1] using r2)

end OMA.E634PrimeGe7

theorem OMA.solution : OMA.R_erdos_634_R1_H3_R1_H2_R1.H2 := by
  intro n a hl hg hpos hsum e hrel
  exact OMA.E634PrimeGe7.main_prime_ge7 n a hl hg hpos hsum e hrel
