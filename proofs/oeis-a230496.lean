import OMAStatements.S_oeis_a230496
import Mathlib
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# Simultaneously odious powers

Shevelev and Moses ask whether, for every n >= 1, some odd K > 1 has all its
first n powers odious (OEIS A230496, https://oeis.org/A230496). Put m equal
to the smallest power of two exceeding n. For every L at least the bit length
of n!, an explicit witness is 1 plus the sum of 2^(L*(n+1)^j), 0 <= j < m.
Multinomial coefficients occupy disjoint binary blocks. Rotating their
multiplicity vectors gives even weight away from the constant term.

A second argument proves recurrence of an entire finite tuple of binary
digit-sum residues attained by nonnegative polynomials at a seed d. The tuple
recurs arbitrarily far along every arithmetic progression through d, for
every positive digit-sum modulus. Marking the support of a multiplicity
vector supplies the divisibility needed for general moduli.

Related work: T. Stoll, Thue-Morse Along Two Polynomial Subsequences,
WORDS 2015, investigates prescribed parities for pairs of powers.
-/

namespace Odious230
open Finset

def encode {m n : ℕ} (r : Fin m → Fin (n+1)) : ℕ :=
  ∑ j : Fin m, (r j : ℕ)*(n+1)^j.val

def weight {m n : ℕ} (r : Fin m → Fin (n+1)) : ℕ := ∑ j : Fin m, (r j : ℕ)

def coeff {m n : ℕ} (i : ℕ) (r : Fin m → Fin (n+1)) : ℕ :=
  if weight r ≤ i then Nat.multinomial Finset.univ
    (fun o : Option (Fin m) => o.elim (i-weight r) (fun j => (r j : ℕ))) else 0

end Odious230

namespace Odious230

theorem encode_succ {n m : ℕ} (r : Fin (m+1) → Fin (n+1)) :
    encode r = (r 0 : ℕ) + (n+1)*encode (fun j : Fin m => r j.succ) := by
  unfold encode
  rw [Fin.sum_univ_succ,Finset.mul_sum]
  simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- No carries are possible in the base-(n+1) encoding of a multiplicity vector. -/
theorem encode_injective (n m : ℕ) : Function.Injective (@encode m n) := by
  induction m with
  | zero =>
    intro x y _
    ext j
    exact Fin.elim0 j
  | succ m ih =>
    intro x y h
    rw [encode_succ,encode_succ] at h
    have f := congrArg (fun v => v%(n+1)) h
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (x 0).isLt,Nat.mod_eq_of_lt (y 0).isLt] at f
    have f0 : x 0 = y 0 := Fin.ext f
    rw [f0] at h
    have tail : (fun j : Fin m => x j.succ) = fun j => y j.succ :=
      ih (Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h))
    funext j
    exact Fin.cases f0 (fun i => congrFun tail i) j

end Odious230

namespace Odious230
open Finset

def augment {m n : ℕ} (i : ℕ) (r : Fin m → Fin (n+1)) (o : Option (Fin m)) : ℕ :=
  o.elim (i - weight r) (fun j => (r j : ℕ))

theorem coeff_zero {m n : ℕ} (i : ℕ) : coeff i (0 : Fin m → Fin (n+1)) = 1 := by
  simp [coeff, Nat.multinomial, Fintype.sum_option, Fintype.prod_option, weight]
  exact Nat.div_self (Nat.factorial_pos i)

theorem coeff_perm {m n : ℕ} (i : ℕ) (r : Fin m → Fin (n+1)) (σ : Equiv.Perm (Fin m)) :
    coeff i (r ∘ σ) = coeff i r := by
  have hw : weight (r ∘ σ) = weight r := Equiv.sum_comp σ (fun j => (r j : ℕ))
  have hp := Equiv.prod_comp σ (fun j => (r j).val.factorial)
  simp only [coeff, hw, Nat.multinomial, Fintype.sum_option, Fintype.prod_option,
    Option.elim_none, Option.elim_some, Function.comp_apply]
  change weight (r ∘ σ) = weight r at hw
  unfold weight at hw
  simp only [Function.comp_apply] at hw
  rw [hw, hp]

theorem power_expand_scaled (n m B i d q : ℕ) (hi : i ≤ n) :
    (d + q * ∑ j : Fin m, B^((n+1)^j.val))^i =
      ∑ r : Fin m → Fin (n+1), (coeff i r * d^(i-weight r) * q^(weight r)) * B^(encode r) := by
  classical
  let f (o : Option (Fin m)) := o.elim d (fun j => q * B ^ ((n+1)^j.val))
  have hf : (∑ o, f o) = d + q*∑ j : Fin m, B^((n+1)^j.val) := by
    rw [Fintype.sum_option, Finset.mul_sum]; rfl
  rw [← hf,Finset.sum_pow_eq_sum_piAntidiag]
  let s : Finset (Fin m → Fin (n+1)) := univ.filter (fun r => weight r ≤ i)
  have mem (r : Fin m → Fin (n+1)) : r ∈ s ↔ weight r ≤ i := by simp [s]
  symm
  calc
    _ = ∑ r ∈ s, (coeff i r * d^(i-weight r) * q^(weight r)) * B^(encode r) := by
      symm
      apply sum_subset (filter_subset ..)
      intro r _ hr
      have hbad : ¬weight r ≤ i := (mem r).not.mp hr
      simp [coeff, hbad]
    _ = _ := by
      apply sum_bij (fun r _ => augment i r)
      · intro r hr
        rw [mem_piAntidiag]
        refine ⟨?_, by simp⟩
        rw [Fintype.sum_option]
        change i - weight r + weight r = i
        exact Nat.sub_add_cancel ((mem r).mp hr)
      · intro r hr r' hr' he
        funext j
        apply Fin.ext
        exact congrFun he (some j)
      · intro g hg
        have H := (mem_piAntidiag.mp hg).1
        rw [Fintype.sum_option] at H
        have hb (j : Fin m) : g (some j) < n+1 := by
          have h0 : g (some j) ≤ ∑ k : Fin m, g (some k) := single_le_sum (fun k _ => Nat.zero_le (g (some k))) (mem_univ j)
          omega
        let r (j : Fin m) : Fin (n+1) := ⟨g (some j), hb j⟩
        have hw : weight r = ∑ j : Fin m, g (some j) := rfl
        refine ⟨r,(mem r).mpr (by omega),?_⟩
        funext o
        cases o with
        | none => change i - weight r = g none; omega
        | some j => rfl
      · intro r hr
        rw [coeff, if_pos ((mem r).mp hr)]
        simp only [Nat.cast_id]
        rw [Fintype.prod_option]
        change _ = Nat.multinomial univ (augment i r) *
          (d^(i-weight r) * ∏ j : Fin m, (q * B^((n+1)^j.val))^(r j).val)
        simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
        have he : encode r = ∑ j : Fin m, (n+1)^j.val * (r j : ℕ) := by
          unfold encode
          apply Finset.sum_congr rfl
          intro j _
          exact Nat.mul_comm ..
        rw [he]
        change (Nat.multinomial univ (augment i r) * d^(i-weight r) * q^(weight r)) * _ =
          Nat.multinomial univ (augment i r) * (d^(i-weight r) * (q^(weight r) * _))
        simp only [Nat.mul_assoc]

theorem power_expand (n m B i : ℕ) (hi : i ≤ n) :
    (1 + ∑ j : Fin m, B^((n+1)^j.val))^i =
      ∑ r : Fin m → Fin (n+1), coeff i r * B^(encode r) := by
  simpa using power_expand_scaled n m B i 1 1 hi

end Odious230

namespace Odious230
open Finset

theorem coeff_support {m n i : ℕ} {r : Fin m → Fin (n+1)} (h : coeff i r ≠ 0) :
    weight r ≤ i := by
  by_contra! hz
  exact h (by simp [coeff,hz.not_ge])

theorem coeff_le_total {m n i : ℕ} (hi : i ≤ n) (r : Fin m → Fin (n+1)) :
    coeff i r ≤ (m+1)^i := by
  have h := power_expand n m 1 i hi
  simp only [one_pow, mul_one, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  have h' : coeff i r ≤ ∑ t : Fin m → Fin (n+1), coeff i t :=
    single_le_sum (fun t _ => Nat.zero_le (coeff i t)) (mem_univ r)
  simpa [add_comm] using h'.trans_eq h.symm

theorem coeff_const_eq_zero {m n i : ℕ} (hi : i < m) (c : Fin (n+1)) (hc : c ≠ 0) :
    coeff i (fun _ : Fin m => c) = 0 := by
  by_contra h
  have hb := coeff_support h
  simp only [weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hb
  have hp : 0 < c.val := Fin.pos_iff_ne_zero.mpr hc
  have := Nat.le_mul_of_pos_right m hp
  omega

end Odious230

namespace Odious230

/-- For a cyclic power-of-two index set, rotation-invariant weights have the parity
of the weight of the distinguished constant word, provided all other constants have weight zero. -/
theorem cyclic_weight_mod_two {α : Type*} [Fintype α] (a₀ : α) (h : ℕ)
    (w : (Fin (2^h) → α) → ℕ)
    (rot : ∀ r, w (fun j => r (j+1)) = w r)
    (hconst : ∀ a : α, a ≠ a₀ → w (fun _ => a) = 0) :
    (∑ r : Fin (2^h) → α, w r) % 2 = w (fun _ => a₀) % 2 := by
  classical
  let I := Fin (2^h)
  let G := Multiplicative I
  let Y := {z : (I → α) × ℕ // z.2 < w z.1}
  let e : Y ≃ Σ r : I → α, Fin (w r) :=
    { toFun := fun z => ⟨z.val.1,⟨z.val.2,z.property⟩⟩
      invFun := fun p => ⟨(p.1,p.2.val),p.2.isLt⟩
      left_inv := by rintro ⟨⟨r,t⟩,h⟩; rfl
      right_inv := by rintro ⟨r,t⟩; rfl }
  let : Finite Y := Finite.of_equiv _ e.symm
  have put_succ (t : ℕ) : Fin.ofNat (2^h) (t+1) = Fin.ofNat (2^h) t + 1 := by
    apply Fin.ext
    change (t+1) % (2^h) = (t%(2^h) + 1%(2^h))%(2^h)
    exact Nat.add_mod _ _ _
  have natrot (t : ℕ) (r : I → α) : w (fun j => r (j+(Fin.ofNat (2^h) t))) = w r := by
    induction t with
    | zero => simp only [Fin.ofNat_zero,add_zero]
    | succ t ih =>
      calc
        w (fun j => r (j+(Fin.ofNat (2^h) (t+1)))) = w (fun j => r ((j+1)+(Fin.ofNat (2^h) t))) := by
          simp only [put_succ, add_assoc, add_comm (1 : I)]
        _ = _ := (rot (fun j => r (j+(Fin.ofNat (2^h) t)))).trans ih
  have allrot (r : I → α) (t : I) : w (fun j => r (j+t)) = w r := by
    have et : (Fin.ofNat (2^h) t.val) = t := Fin.ext (Nat.mod_eq_of_lt t.isLt)
    simpa only [et] using natrot t.val r
  let : MulAction G Y :=
    { smul := fun g z => ⟨(fun j => z.val.1 (j+g.toAdd),z.val.2), by
        rw [allrot]
        exact z.property⟩
      one_smul := by
        intro z
        apply Subtype.ext
        change ((fun j => z.val.1 (j+0)), z.val.2) = z.val
        simp
      mul_smul := by
        intro g₁ g₂ z
        apply Subtype.ext
        change ((fun j => z.val.1 (j+(g₁.toAdd+g₂.toAdd))), z.val.2) =
          ((fun j => z.val.1 ((j+g₁.toAdd)+g₂.toAdd)), z.val.2)
        simp only [add_assoc] }
  have fixZero (z : MulAction.fixedPoints G Y) : z.val.val.1 = fun _ => a₀ := by
    have eqc : z.val.val.1 = fun _ => z.val.val.1 0 := by
      funext t
      have fixed := MulAction.mem_fixedPoints.mp z.property (Multiplicative.ofAdd t)
      have eq := congrArg (fun y : Y => y.val.1 0) fixed
      change z.val.val.1 (0+t) = z.val.val.1 0 at eq
      simpa only [zero_add] using eq
    by_cases hs : z.val.val.1 0 = a₀
    · exact eqc.trans (by rw [hs])
    · have hz := z.val.property
      rw [eqc,hconst _ hs] at hz
      omega
  let q : MulAction.fixedPoints G Y ≃ Fin (w (fun _ => a₀)) :=
    { toFun := fun z => ⟨z.val.val.2, by rw [←fixZero z]; exact z.val.property⟩
      invFun := fun t => ⟨⟨(fun _ => a₀,t.val),t.isLt⟩,fun _ => rfl⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (fixZero z).symm rfl
      right_inv := by intro t; rfl }
  have hg : IsPGroup 2 G := IsPGroup.of_card (n:=h) (by
    change Nat.card (Multiplicative (Fin (2^h))) = _
    rw [Nat.card_congr Multiplicative.toAdd]
    simp)
  have hc := hg.card_modEq_card_fixedPoints Y
  rw [Nat.card_congr e, Nat.card_congr q, Nat.card_eq_fintype_card, Fintype.card_sigma] at hc
  simp only [Fintype.card_fin, Nat.card_fin,Nat.ModEq] at hc
  convert! hc

theorem odd_weight_sum (h n i : ℕ) (hi : i < 2^h)
    (w : (Fin (2^h) → Fin (n+1)) → ℕ)
    (rot : ∀ r, w (fun j => r (j+1)) = w r) :
    (∑ r : Fin (2^h) → Fin (n+1), if (∑ j, (r j).val) ≤ i then w r else 0) % 2 =
      w (fun _ => 0) % 2 := by
  let f (r : Fin (2^h) → Fin (n+1)) := if (∑ j, (r j).val) ≤ i then w r else 0
  have hr (r : Fin (2^h) → Fin (n+1)) : f (fun j => r (j+1)) = f r := by
    have ss := Equiv.sum_comp (Equiv.addRight (1 : Fin (2^h))) (fun j => (r j).val)
    change (∑ j, (r (j+1)).val) = _ at ss
    simp only [f,ss,rot]
  have hc (a : Fin (n+1)) (ha : a ≠ 0) : f (fun _ => a) = 0 := by
    have apos : 0 < a.val := by exact Nat.pos_of_ne_zero (fun e => ha (Fin.ext e))
    have bound : i < 2^h * a.val := hi.trans_le (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^h) apos)
    simp [f,bound.not_ge]
  apply (cyclic_weight_mod_two (0 : Fin (n+1)) h f hr hc).trans
  simp [f]

end Odious230

namespace Odious230

/-- The higher digits start above the final possible bit of `x`. -/
theorem pack_pair (x y k : ℕ) (hx : x < 2^k) :
    (Nat.digits 2 (x + 2^k*y)).count 1 =
      (Nat.digits 2 x).count 1 + (Nat.digits 2 y).count 1 := by
  obtain rfl | hy := Nat.eq_zero_or_pos y
  · simp
  have hlen := (Nat.digits_length_le_iff (by decide : 1 < 2) x).mpr hx
  have h := Nat.digits_append_zeroes_append_digits (n:=x)
    (k:=k-(Nat.digits 2 x).length) (by decide : 1 < 2) hy
  rw [Nat.add_sub_of_le hlen] at h
  rw [← h]
  simp [List.count_replicate]

/-- Binary blocks at distinct exponents contribute independently to the weight. -/
theorem pack_sum {α : Type*} (s : Finset α) (e c : α → ℕ) (L : ℕ)
    (hinj : Set.InjOn e (s : Set α)) (h : ∀ i ∈ s, c i < 2^L) :
    (Nat.digits 2 (∑ i ∈ s, c i * (2^L)^(e i))).count 1 =
      ∑ i ∈ s, (Nat.digits 2 (c i)).count 1 := by
  classical
  suffices aux : ∀ (N : ℕ) (t : Finset α), t ⊆ s → (∀ i ∈ t, e i < N) →
      (∑ i ∈ t, c i * (2^L)^(e i)) < (2^L)^N ∧
      (Nat.digits 2 (∑ i ∈ t, c i * (2^L)^(e i))).count 1 =
        ∑ i ∈ t, (Nat.digits 2 (c i)).count 1 by
    exact (aux (s.sup e + 1) s (by rfl) (fun i hi => Nat.lt_succ_of_le (Finset.le_sup hi))).2
  intro N
  induction N with
  | zero =>
    intro t _ ht
    have : t = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => Nat.not_lt_zero _ (ht i hi))
    simp [this]
  | succ N ih =>
    intro t ht hN
    by_cases hex : ∃ i ∈ t, e i = N
    · obtain ⟨i, hi, hei⟩ := hex
      have hsub := Finset.erase_subset i t
      have hem (j : α) (hj : j ∈ t.erase i) : e j < N := by
        have h1 := hN j (hsub hj)
        have h2 : e j ≠ N := fun he => (Finset.mem_erase.mp hj).1
          (hinj (ht (hsub hj)) (ht hi) (he.trans hei.symm))
        omega
      obtain ⟨hv, hw⟩ := ih (t.erase i) (hsub.trans ht) hem
      let v := ∑ j ∈ t.erase i, c j * (2^L)^(e j)
      change v < (2^L)^N at hv
      change (Nat.digits 2 v).count 1 = _ at hw
      have hval : (∑ j ∈ t, c j * (2^L)^(e j)) = v + (2^L)^N*c i := by
        rw [← Finset.sum_erase_add _ _ hi, hei, Nat.mul_comm (c i)]
      rw [hval]
      constructor
      · calc
          v + (2^L)^N*c i < (2^L)^N + (2^L)^N*c i := Nat.add_lt_add_right hv _
          _ = (2^L)^N * (c i+1) := by ring
          _ ≤ (2^L)^(N+1) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ (h i (ht hi))
      · rw [← pow_mul] at hv ⊢
        rw [pack_pair v (c i) (L*N) hv, hw, Finset.sum_erase_add _ _ hi]
    · have he (i : α) (hi : i ∈ t) : e i < N := by
        have h1 := hN i hi
        have h2 : e i ≠ N := fun he => hex ⟨i, hi, he⟩
        omega
      obtain ⟨hv, hw⟩ := ih t ht he
      exact ⟨hv.trans_le (Nat.pow_le_pow_right (by positivity) (by omega)), hw⟩

/-- Evaluate a natural polynomial in disjoint binary blocks. -/
theorem pack_eval (P : Polynomial ℕ) (L : ℕ) (h : ∀ j ∈ P.support, P.coeff j < 2^L) :
    (Nat.digits 2 (P.eval (2^L))).count 1 = ∑ j ∈ P.support, (Nat.digits 2 (P.coeff j)).count 1 := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact pack_sum P.support id P.coeff L Function.injective_id.injOn h

end Odious230

namespace Odious230
open Finset OMA.S_oeis_a230496

/-- The numerator of a coefficient of degree i is i!, independently of the variable count. -/
theorem coeff_le_factorial {m n : ℕ} (i : ℕ) (r : Fin m → Fin (n+1)) :
    coeff i r ≤ i.factorial := by
  unfold coeff
  split
  · rename_i hw
    unfold Nat.multinomial
    rw [Fintype.sum_option]
    change ((i-weight r) + weight r).factorial / _ ≤ i.factorial
    rw [Nat.sub_add_cancel hw]
    exact Nat.div_le_self _ _
  · exact Nat.zero_le _

/-- A sum with a low constant bit and an increasing sequence of higher bits has the
expected binary length, including when the first higher bit is the next position. -/
theorem size_sparse_ones (e : ℕ → ℕ) (he : StrictMono e) (h0 : 0 < e 0)
    (m : ℕ) (hm : 0 < m) :
    Nat.size (1 + ∑ j : Fin m, 2^(e j.val)) = e (m-1)+1 := by
  have room (k : ℕ) : 1 + ∑ j ∈ range k, (2:ℕ)^(e j) < 2^(e k) := by
    induction k with
    | zero => simpa using one_lt_pow₀ (by decide : 1 < (2:ℕ)) h0.ne'
    | succ k ih =>
      rw [sum_range_succ]
      calc
        1 + ((∑ j ∈ range k, (2:ℕ)^(e j)) + 2^(e k)) < 2^(e k) + 2^(e k) := by omega
        _ = 2^(e k+1) := by rw [pow_succ]; omega
        _ ≤ 2^(e (k+1)) := Nat.pow_le_pow_right (by decide) (he (Nat.lt_succ_self k))
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [Fin.sum_univ_eq_sum_range (fun j => (2:ℕ)^(e j)), sum_range_succ, Nat.succ_sub_one]
  have hi : 1 + ((∑ j ∈ range u, (2:ℕ)^(e j)) + 2^(e u)) < 2^(e u+1) := by
    rw [pow_succ]
    have := room u
    omega
  exact le_antisymm (Nat.size_le.mpr hi) (Nat.lt_size.mpr (by omega))

/-- An explicit odd witness for every finite number of powers, including its exact bit length. -/
theorem quantitative_odious (n L : ℕ) (hn : 0 < n) (hL : Nat.size n.factorial ≤ L) :
    let m := 2^(Nat.size n)
    let K := 1 + ∑ j : Fin m, (2^L)^((n+1)^j.val)
    1 < K ∧ Odd K ∧ 2^L ∣ K-1 ∧ Nat.size K = L*(n+1)^(m-1)+1 ∧
      ∀ i ≤ n, IsOdious (K^i) := by
  dsimp only
  let m := 2^(Nat.size n)
  let B := 2^L
  let S := ∑ j : Fin m, B^((n+1)^j.val)
  change 1 < 1+S ∧ Odd (1+S) ∧ B ∣ 1+S-1 ∧
    Nat.size (1+S) = L*(n+1)^(m-1)+1 ∧ ∀ i ≤ n, IsOdious ((1+S)^i)
  have hm : n < m := Nat.lt_size_self n
  have fc : n.factorial < B := Nat.size_le.mp hL
  have hLpos : 0 < L := (Nat.size_pos.mpr (Nat.factorial_pos n)).trans_le hL
  let j₀ : Fin m := ⟨0, by omega⟩
  have onebit : B^((n+1)^j₀.val) ≤ S :=
    single_le_sum (f:=fun j : Fin m => B^((n+1)^j.val)) (fun _ _ => Nat.zero_le _) (mem_univ j₀)
  have bS : B ≤ S := by simpa [j₀] using onebit
  have bulk : B ∣ S := dvd_sum fun j _ => dvd_pow_self _ (by positivity : (n+1)^j.val ≠ 0)
  have twoB : 2 ∣ B := (pow_one (2:ℕ)) ▸ pow_dvd_pow 2 hLpos
  refine ⟨by have := Nat.factorial_pos n; omega, ?_, by simpa using bulk, ?_, ?_⟩
  · obtain ⟨c,hc⟩ := twoB.trans bulk
    exact ⟨c, by omega⟩
  · have he : StrictMono (fun j : ℕ => L*(n+1)^j) :=
      fun _ _ hl => Nat.mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by omega) hl) hLpos
    have hsize := size_sparse_ones _ he (by simpa using hLpos) m (by omega)
    simpa only [S,B,←pow_mul] using hsize
  · intro i hi
    rw [show (1+S)^i = _ from power_expand n m B i hi]
    apply Nat.odd_iff.mpr
    rw [pack_sum univ encode (coeff i) L (encode_injective n m).injOn
      (fun r _ => (coeff_le_factorial i r).trans_lt ((Nat.factorial_le hi).trans_lt fc))]
    let w (r : Fin m → Fin (n+1)) := (Nat.digits 2 (coeff i r)).count 1
    have rot (r : Fin m → Fin (n+1)) : w (fun j => r (j+1)) = w r :=
      congrArg (fun c => (Nat.digits 2 c).count 1) (coeff_perm i r (Equiv.addRight 1))
    have vanish (c : Fin (n+1)) (hc : c ≠ 0) : w (fun _ => c) = 0 := by
      simp [w,coeff_const_eq_zero (hi.trans_lt hm) c hc]
    have par := cyclic_weight_mod_two (0 : Fin (n+1)) (Nat.size n) w rot vanish
    change (∑ r, w r) % 2 = 1
    rw [par]
    change (Nat.digits 2 (coeff i (0 : Fin m → Fin (n+1)))).count 1 % 2 = 1
    rw [coeff_zero]
    decide

end Odious230

namespace Odious230

/-- Each positive coordinate is marked with an equal share of `n!` copies of its
word's weight. Summing first over the marked coordinate gives a multiple of `H*n!`. -/
theorem marked_weight_mod {α : Type*} [Fintype α] [DecidableEq α]
    (a₀ : α) (H n : ℕ) (hH : 0 < H) (w : (Fin (H*n.factorial) → α) → ℕ)
    (perm : ∀ r (σ : Equiv.Perm (Fin (H*n.factorial))), w (r ∘ σ) = w r)
    (cut : ∀ r, n < (Finset.univ.filter fun j => r j ≠ a₀).card → w r = 0) :
    (∑ r, w r) % H = w (fun _ => a₀) % H := by
  classical
  let I := Fin (H*n.factorial)
  let blank : I → α := fun _ => a₀
  let size (r : I → α) := (Finset.univ.filter fun j => r j ≠ a₀).card
  let share (r : I → α) := w r * (n.factorial / size r)
  let rest (r : I → α) := if r = blank then 0 else w r
  let mark (r : I → α) (j : I) := if r j ≠ a₀ then share r else 0
  let slice (j : I) := ∑ r : I → α, mark r j
  let o : I := ⟨0,Nat.mul_pos hH n.factorial_pos⟩
  have szperm (r : I → α) (σ : Equiv.Perm I) : size (r ∘ σ) = size r := by
    have hs := Equiv.sum_comp σ (fun j => if r j ≠ a₀ then (1 : ℕ) else 0)
    simpa only [size, Function.comp_apply, Finset.sum_boole, Nat.cast_id] using hs
  have same_slice (j : I) : slice j = slice o := by
    let σ := Equiv.swap o j
    let rearr : (I → α) ≃ (I → α) :=
      { toFun := fun r => r ∘ σ
        invFun := fun r => r ∘ σ.symm
        left_inv := by intro r; funext k; simp
        right_inv := by intro r; funext k; simp }
    calc
      slice j = ∑ r : I → α, mark (r ∘ σ) o := by
        apply Finset.sum_congr rfl
        intro r _
        simp only [mark, share, perm, szperm, Function.comp_apply]
        rw [show σ o = j from Equiv.swap_apply_left o j]
      _ = slice o := Equiv.sum_comp rearr (fun r => mark r o)
  have per_word (r : I → α) : (∑ j : I, mark r j) = n.factorial * rest r := by
    have count : (∑ j : I, mark r j) = size r * share r := by
      simp only [mark, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, size]
    rw [count]
    by_cases hz : r = blank
    · subst r
      simp [size, blank, rest]
    · have pos : 0 < size r := by
        apply Finset.card_pos.mpr
        by_contra! ha
        apply hz
        funext j
        by_contra hj
        exact (Finset.eq_empty_iff_forall_notMem.mp ha) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      rw [show rest r = w r from if_neg hz]
      by_cases hs : size r ≤ n
      · have hcan := Nat.div_mul_cancel (Nat.dvd_factorial pos hs)
        calc
          size r * share r = (n.factorial / size r * size r) * w r := by dsimp [share]; ring
          _ = n.factorial * w r := by rw [hcan]
      · simp [share, cut r (Nat.lt_of_not_ge hs)]
  have balance : n.factorial * (∑ r, rest r) = n.factorial * (H * slice o) := by
    calc
      n.factorial * (∑ r, rest r) = ∑ r, ∑ j, mark r j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun r _ => (per_word r).symm)
      _ = ∑ j : I, slice j := Finset.sum_comm
      _ = n.factorial * (H * slice o) := by
        simp only [same_slice, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        rw [show Fintype.card I = H * n.factorial from Fintype.card_fin _]
        ring
  have mul := Nat.eq_of_mul_eq_mul_left n.factorial_pos balance
  have split (r : I → α) : w r = (if r = blank then w blank else 0) + rest r := by
    by_cases h : r = blank <;> simp [rest, h]
  have total : (∑ r, w r) = w blank + H * slice o := by
    calc
      _ = ∑ r : I → α, ((if r = blank then w blank else 0) + rest r) :=
        Finset.sum_congr rfl (fun r _ => split r)
      _ = _ := by
        rw [Finset.sum_add_distrib, mul, Finset.sum_ite_eq' _ blank (fun _ => w blank)]
        simp
  rw [total]
  exact Nat.add_mul_mod_self_left _ _ _

end Odious230

namespace Odious230
open Finset

/-- Coefficient of the block encoded by r after evaluating the polynomial
with coefficient vector a at d plus q times the sum of the separated places. -/
def scaledBlock {m n : ℕ} (a : Fin (n+1) → ℕ) (d q : ℕ) (r : Fin m → Fin (n+1)) : ℕ :=
  ∑ i : Fin (n+1), a i * (coeff i.val r * d^(i.val-weight r) * q^(weight r))

theorem expand_scaled_blocks (n m B d q : ℕ) (a : Fin (n+1) → ℕ) :
    (∑ i : Fin (n+1), a i * (d + q * ∑ j : Fin m, B^((n+1)^j.val))^i.val) =
    ∑ r : Fin m → Fin (n+1), scaledBlock a d q r * B^(encode r) := by
  have e (i : Fin (n+1)) := power_expand_scaled n m B i.val d q (Nat.le_of_lt_succ i.isLt)
  simp_rw [e,Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold scaledBlock
  simp only [Finset.sum_mul,Nat.mul_assoc]

theorem scaled_block_perm {m n : ℕ} (a : Fin (n+1) → ℕ) (d q : ℕ) (r : Fin m → Fin (n+1)) (σ : Equiv.Perm (Fin m)) :
    scaledBlock a d q (r ∘ σ) = scaledBlock a d q r := by
  have hw : weight (r ∘ σ) = weight r := Equiv.sum_comp σ (fun j => (r j : ℕ))
  simp only [scaledBlock,coeff_perm,hw]

theorem scaled_zero {m n : ℕ} (a : Fin (n+1) → ℕ) (d q : ℕ) :
    scaledBlock a d q (0 : Fin m → Fin (n+1)) = ∑ i : Fin (n+1), a i*d^i.val := by
  simp [scaledBlock,coeff_zero,weight]

theorem scaled_cut {m n : ℕ} (a : Fin (n+1) → ℕ) (d q : ℕ) (r : Fin m → Fin (n+1))
    (large : n < (Finset.univ.filter (fun j => r j ≠ 0)).card) : scaledBlock a d q r = 0 := by
  have le : (Finset.univ.filter (fun j => r j ≠ 0)).card ≤ weight r := by
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    apply Finset.sum_le_sum
    intro j _
    split
    · exact Nat.pos_of_ne_zero (fun z => by rename_i h; exact h (Fin.ext z))
    · exact Nat.zero_le _
  unfold scaledBlock
  apply Finset.sum_eq_zero
  intro i _
  have hw : ¬weight r ≤ i.val := by have := i.isLt; omega
  simp [coeff,hw]

/-- For any modulus H of binary digit weights, and any residue d modulo q,
all the given polynomials realize at arbitrarily large x in that residue
the same weight residues that they realized at d. -/
theorem progression_weight_residues (n A d q M H : ℕ) (hq : 0 < q) (hH : 0 < H) (a : Fin A → Fin (n+1) → ℕ) :
    ∃ x : ℕ, M < x ∧ x ≡ d [MOD q] ∧ ∀ t : Fin A,
      (Nat.digits 2 (∑ i : Fin (n+1), a t i*x^i.val)).count 1 % H =
      (Nat.digits 2 (∑ i : Fin (n+1), a t i*d^i.val)).count 1 % H := by
  classical
  let m := H*n.factorial
  have hm : 0 < m := Nat.mul_pos hH (Nat.factorial_pos n)
  let total := ∑ t : Fin A, ∑ r : Fin m → Fin (n+1), scaledBlock (a t) d q r
  let L := M + Nat.size total + 1
  let B := 2^L
  let S := ∑ j : Fin m, B^((n+1)^j.val)
  have bnd (t : Fin A) (r : Fin m → Fin (n+1)) : scaledBlock (a t) d q r < B := by
    have c₁ : scaledBlock (a t) d q r ≤ ∑ s : Fin m → Fin (n+1), scaledBlock (a t) d q s :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    have c₂ : (∑ s : Fin m → Fin (n+1), scaledBlock (a t) d q s) ≤ total :=
      Finset.single_le_sum (fun t _ => Nat.zero_le (∑ r : Fin m → Fin (n+1), scaledBlock (a t) d q r)) (Finset.mem_univ t)
    exact (c₁.trans c₂).trans_lt (total.lt_size_self.trans_le (Nat.pow_le_pow_right (by decide) (show Nat.size total ≤ L by dsimp [L]; omega)))
  let j₀ : Fin m := ⟨0,hm⟩
  have single : B^((n+1)^j₀.val) ≤ S :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (B^((n+1)^j.val))) (Finset.mem_univ j₀)
  have bS : B ≤ S := by simpa [j₀] using single
  have Mb : M < B := (show M ≤ L by dsimp [L]; omega).trans_lt L.lt_two_pow_self
  have s_le : S ≤ q*S := Nat.le_mul_of_pos_left S hq
  refine ⟨d+q*S,by omega,?_,?_⟩
  · exact Nat.add_comm d (q*S) ▸ Nat.ModEq.modulus_mul_add
  · intro t
    have exp := expand_scaled_blocks n m B d q (a t)
    rw [show (∑ i : Fin (n+1), a t i*(d+q*S)^i.val) = _ from exp,
      pack_sum Finset.univ encode (scaledBlock (a t) d q) L (encode_injective n m).injOn (fun r _ => bnd t r)]
    let w (r : Fin m → Fin (n+1)) := (Nat.digits 2 (scaledBlock (a t) d q r)).count 1
    have inv (r : Fin m → Fin (n+1)) (σ : Equiv.Perm (Fin m)) : w (r ∘ σ) = w r :=
      congrArg (fun v => (Nat.digits 2 v).count 1) (scaled_block_perm (a t) d q r σ)
    have vanish (r : Fin m → Fin (n+1)) (large : n < (Finset.univ.filter (fun j => r j ≠ 0)).card) : w r = 0 := by
      change (Nat.digits 2 (scaledBlock (a t) d q r)).count 1 = 0
      rw [scaled_cut (a t) d q r large]
      rfl
    change (∑ r, w r) % H = _
    rw [marked_weight_mod (0 : Fin (n+1)) H n hH w inv vanish]
    change (Nat.digits 2 (scaledBlock (a t) d q (0 : Fin m → Fin (n+1)))).count 1 % H = _
    rw [scaled_zero]

theorem simultaneous_progression (n A d q M : ℕ) (hq : 0 < q) (a : Fin A → Fin (n+1) → ℕ) :
    ∃ x : ℕ, M < x ∧ x ≡ d [MOD q] ∧ ∀ t : Fin A,
      (Nat.digits 2 (∑ i : Fin (n+1), a t i*x^i.val)).count 1 % 2 =
      (Nat.digits 2 (∑ i : Fin (n+1), a t i*d^i.val)).count 1 % 2 :=
  progression_weight_residues n A d q M 2 hq (by decide) a

end Odious230

namespace Odious230

/-- Every finite tuple of polynomial binary-weight residues attained at `d` occurs
arbitrarily far along every arithmetic progression through `d`. -/
theorem polynomial_weight_recurrence
    {ι : Type*} [Fintype ι] (P : ι → Polynomial ℕ) (d q M H : ℕ) (hq : 0 < q) (hH : 0 < H) :
    ∃ x > M, x ≡ d [MOD q] ∧ ∀ u : ι,
      (Nat.digits 2 ((P u).eval x)).count 1 % H =
      (Nat.digits 2 ((P u).eval d)).count 1 % H := by
  classical
  let n := Finset.univ.sup fun u => (P u).natDegree
  let e := Fintype.equivFin ι
  let a (v : Fin (Fintype.card ι)) (i : Fin (n+1)) := (P (e.symm v)).coeff i.val
  obtain ⟨x,hx,hmod,hw⟩ := progression_weight_residues n (Fintype.card ι) d q M H hq hH a
  refine ⟨x,hx,hmod,?_⟩
  intro u
  have hdeg : (P u).natDegree < n+1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun v => (P v).natDegree) (Finset.mem_univ u))
  rw [Polynomial.eval_eq_sum_range' hdeg x, Polynomial.eval_eq_sum_range' hdeg d,
    ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simpa only [a, Equiv.symm_apply_apply] using hw (e u)

end Odious230

theorem OMA.solution : type_of% @OMA.S_oeis_a230496.main := by
  intro n hn
  let L := Nat.size n.factorial
  obtain ⟨hlt,hodd,_,_,powers⟩ := Odious230.quantitative_odious n L hn le_rfl
  exact ⟨_,hodd,hlt,fun i _ hi => powers i hi⟩
