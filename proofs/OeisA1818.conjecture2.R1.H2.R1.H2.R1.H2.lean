import OMAReductions.R_OeisA1818_conjecture2_R1_H2_R1_H2_R1

/-! Fourier eigenbasis for the normalized kernel on the Teichmueller lifts modulo p^2.
The lifts are the (p-1)-th roots of unity, their power sums vanish off multiples of p-1,
and 1/(1-t) = -(1/n) sum r t^r gives the eigenvalues (2k-1-n)/2. -/

namespace OMA.A1818Fourier

open Finset

/-- Weighted geometric sum identity. -/
lemma weighted {R : Type*} [CommRing R] (t : R) (N : ℕ) :
    (1 - t) * ∑ r ∈ range N, (r : R) * t ^ r + 1 + (N : R) * t ^ N =
      ∑ r ∈ range (N + 1), t ^ r := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun r => t ^ r) (N + 1), ← ih]
    push_cast
    ring

/-- For r below n and k in [1, n], n divides r + k exactly when r = n - k. -/
lemma dvd_iff_eq {n r k : ℕ} (hr : r < n) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    n ∣ r + k ↔ r = n - k := by
  constructor
  · rintro ⟨c, hc⟩
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  · intro h
    exact ⟨1, by omega⟩

/-- The spectral identity for a family of n-th roots of unity with unit differences
whose power sums are those of all n-th roots of unity. -/
lemma key {N n : ℕ} (y : Fin n → ZMod N)
    (hy1 : ∀ i, y i ^ n = 1) (hyu : ∀ i, IsUnit (y i))
    (hdiff : ∀ i j, i ≠ j → IsUnit (y i - y j))
    (hS : ∀ s, ∑ i, y i ^ s = if n ∣ s then (n : ZMod N) else 0)
    (hnu : IsUnit (n : ZMod N)) (j : Fin n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    2 * ∑ l, (if j = l then 0 else y j * (y j - y l)⁻¹) * y l ^ k =
      (2 * (k : ZMod N) - 1 - n) * y j ^ k := by
  set q := y j with hqdef
  set w := q⁻¹ with hwdef
  have hqw : q * w = 1 := ZMod.mul_inv_of_unit q (hyu j)
  have hqn : q ^ n = 1 := hy1 j
  have hwn : w ^ n = 1 := by
    have h := congrArg (fun z => z ^ n) hqw
    simp only [mul_pow, hqn, one_mul, one_pow] at h
    exact h
  have hterm : ∀ l, j ≠ l → (n : ZMod N) * (q * (q - y l)⁻¹) =
      -∑ r ∈ range n, (r : ZMod N) * (y l * w) ^ r := by
    intro l hl
    have hinv : (q - y l) * (q - y l)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hdiff j l hl)
    have hb : q * (q - y l)⁻¹ * (1 - y l * w) = 1 := by
      linear_combination (-(y l * (q - y l)⁻¹)) * hqw + hinv
    have htn : (y l * w) ^ n = 1 := by rw [mul_pow, hy1 l, hwn, one_mul]
    have hgeom : ∑ r ∈ range n, (y l * w) ^ r = 0 := by
      have h1 := geom_sum_mul (y l * w) n
      rw [htn, sub_self] at h1
      have hu : IsUnit (y l * w - 1) := by
        have h2 : (y l * w - 1) * (-(q * (q - y l)⁻¹)) = 1 := by linear_combination hb
        exact ⟨⟨_, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
      exact (hu.mul_left_eq_zero).mp h1
    have hw := weighted (y l * w) n
    rw [Finset.sum_range_succ, hgeom, htn] at hw
    linear_combination (q * (q - y l)⁻¹) * hw - (∑ r ∈ range n, (r : ZMod N) * (y l * w) ^ r) * hb
  -- the full sum, multiplied by n
  set F : Fin n → ZMod N := fun l => -∑ r ∈ range n, (r : ZMod N) * w ^ r * y l ^ (r + k) with hF
  have hstep : ∀ l, (n : ZMod N) * ((if j = l then 0 else q * (q - y l)⁻¹) * y l ^ k) =
      F l - (if j = l then F l else 0) := by
    intro l
    by_cases h : j = l
    · simp [h]
    · simp only [h, if_false, sub_zero, hF]
      rw [← mul_assoc, hterm l h, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [mul_pow, pow_add]
      ring
  have hsumF : ∑ l, F l = -∑ r ∈ range n, (r : ZMod N) * w ^ r *
      (if n ∣ r + k then (n : ZMod N) else 0) := by
    simp only [hF, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← Finset.mul_sum, hS]
  have hFj : F j = -(q ^ k * ∑ r ∈ range n, (r : ZMod N)) := by
    simp only [hF, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    have : w ^ r * q ^ r = 1 := by rw [← mul_pow, mul_comm, hqw, one_pow]
    rw [← hqdef, pow_add]
    linear_combination ((r : ZMod N) * q ^ k) * this
  have hite : ∑ r ∈ range n, (r : ZMod N) * w ^ r * (if n ∣ r + k then (n : ZMod N) else 0) =
      ((n - k : ℕ) : ZMod N) * w ^ (n - k) * n := by
    rw [Finset.sum_congr rfl (g := fun r => if r = n - k then (r : ZMod N) * w ^ r * n else 0)]
    · rw [Finset.sum_ite_eq' (range n) (n - k)]
      rw [if_pos (Finset.mem_range.mpr (by omega))]
    · intro r hr
      rw [Finset.mem_range] at hr
      by_cases h : r = n - k
      · rw [if_pos h, if_pos ((dvd_iff_eq hr hk1 hkn).mpr h)]
      · rw [if_neg h, if_neg (fun hd => h ((dvd_iff_eq hr hk1 hkn).mp hd)), mul_zero]
  have hwq : w ^ (n - k) = q ^ k := by
    have h1 : q ^ k * (q * w) ^ (n - k) = q ^ k := by rw [hqw, one_pow, mul_one]
    rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkn, hqn, one_mul] at h1
    exact h1
  have hid : (∑ r ∈ range n, (r : ZMod N)) * 2 = (n : ZMod N) * ((n : ZMod N) - 1) := by
    have h := Finset.sum_range_id_mul_two n
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel] at h
      have h' := congrArg (fun z : ℕ => (z : ZMod N)) h
      push_cast at h' ⊢
      rw [h']
      ring
  have hcast : ((n - k : ℕ) : ZMod N) = (n : ZMod N) - k := by
    rw [Nat.cast_sub hkn]
  have htotal : (n : ZMod N) * (2 * ∑ l, (if j = l then 0 else q * (q - y l)⁻¹) * y l ^ k) =
      (n : ZMod N) * ((2 * (k : ZMod N) - 1 - n) * q ^ k) := by
    have e1 : (n : ZMod N) * ∑ l, (if j = l then 0 else q * (q - y l)⁻¹) * y l ^ k =
        ∑ l, F l - F j := by
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun l _ => hstep l), Finset.sum_sub_distrib,
        Finset.sum_ite_eq (univ) j F, if_pos (Finset.mem_univ j)]
    calc (n : ZMod N) * (2 * ∑ l, (if j = l then 0 else q * (q - y l)⁻¹) * y l ^ k)
        = 2 * ((n : ZMod N) * ∑ l, (if j = l then 0 else q * (q - y l)⁻¹) * y l ^ k) := by ring
      _ = 2 * (∑ l, F l - F j) := by rw [e1]
      _ = _ := by
        rw [hsumF, hFj, hite, hwq, hcast]
        linear_combination (q ^ k) * hid
  exact (hnu.mul_left_cancel htotal)

end OMA.A1818Fourier

namespace OMA.A1818Fourier

open Finset

/-- Reduction from ZMod (p^2) to ZMod p. -/
def phi (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)

lemma phi_natCast (p a : ℕ) : phi p (a : ZMod (p ^ 2)) = (a : ZMod p) := map_natCast _ a

lemma isUnit_of_phi {p : ℕ} (hp : p.Prime) {x : ZMod (p ^ 2)} (hx : phi p x ≠ 0) :
    IsUnit x := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [phi_natCast] at hx
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  have h1 : ¬ p ∣ x.val := fun h => hx ((ZMod.natCast_eq_zero_iff _ _).mpr h)
  exact (((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm).pow_right 2

/-- Teichmueller-type lift of a residue. -/
def T (p : ℕ) (x : ZMod p) : ZMod (p ^ 2) := ((x.val : ℕ) : ZMod (p ^ 2)) ^ p

lemma pow_p_eq {p a b : ℕ} (h : a % p = b % p) :
    ((a : ZMod (p ^ 2))) ^ p = ((b : ZMod (p ^ 2))) ^ p := by
  have ha : ((a : ℕ) : ZMod (p ^ 2)) =
      ((a % p : ℕ) : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * ((a / p : ℕ) : ZMod (p ^ 2)) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  have hb : ((b : ℕ) : ZMod (p ^ 2)) =
      ((b % p : ℕ) : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * ((b / p : ℕ) : ZMod (p ^ 2)) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  have hd : ((p : ℕ) : ZMod (p ^ 2)) ∣ (a : ZMod (p ^ 2)) - (b : ZMod (p ^ 2)) := by
    rw [ha, hb, h]
    exact ⟨((a / p : ℕ) : ZMod (p ^ 2)) - ((b / p : ℕ) : ZMod (p ^ 2)), by ring⟩
  have h2 := dvd_sub_pow_of_dvd_sub hd 1
  have hz : ((p : ℕ) : ZMod (p ^ 2)) ^ (1 + 1) = 0 := by
    have := ZMod.natCast_self (p ^ 2)
    push_cast at this
    exact this
  rw [hz, zero_dvd_iff, sub_eq_zero, pow_one] at h2
  exact h2

lemma T_mul {p : ℕ} [NeZero p] (x y : ZMod p) : T p (x * y) = T p x * T p y := by
  unfold T
  rw [← mul_pow, ← Nat.cast_mul]
  apply pow_p_eq
  rw [ZMod.val_mul, Nat.mod_mod]

lemma phi_T {p : ℕ} [Fact p.Prime] (x : ZMod p) : phi p (T p x) = x := by
  unfold T
  rw [map_pow, phi_natCast, ZMod.natCast_zmod_val, ZMod.pow_card]

lemma T_pow {p : ℕ} [hp : Fact p.Prime] {x : ZMod p} (hx : x ≠ 0) : T p x ^ (p - 1) = 1 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  have hu : IsUnit ((x.val : ℕ) : ZMod (p ^ 2)) :=
    isUnit_of_phi hp.out (by rw [phi_natCast, ZMod.natCast_zmod_val]; exact hx)
  have ht := ZMod.pow_totient hu.unit
  rw [Nat.totient_prime_pow hp.out two_pos] at ht
  have h2 := congrArg Units.val ht
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h2
  unfold T
  rw [← pow_mul]
  simpa using h2

lemma sum_units_pow {p : ℕ} [hp : Fact p.Prime] (s : ℕ) (hs : ¬ (p - 1) ∣ s) :
    ∑ u : (ZMod p)ˣ, T p (u : ZMod p) ^ s = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : (ZMod p)ˣ, c ^ s ≠ 1 := by
    by_contra h
    push Not at h
    apply hs
    have := Monoid.exponent_dvd_of_forall_pow_eq_one h
    rwa [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units] at this
  have hperm : ∑ u : (ZMod p)ˣ, T p ((c * u : (ZMod p)ˣ) : ZMod p) ^ s =
      ∑ u : (ZMod p)ˣ, T p (u : ZMod p) ^ s :=
    Fintype.sum_equiv (Equiv.mulLeft c) _ _ (fun u => rfl)
  simp only [Units.val_mul, T_mul, mul_pow] at hperm
  rw [← Finset.mul_sum] at hperm
  have hunit : IsUnit (T p (c : ZMod p) ^ s - 1) := by
    apply isUnit_of_phi hp.out
    rw [map_sub, map_pow, phi_T, map_one, sub_ne_zero]
    intro h
    apply hc
    ext
    simpa using h
  have h0 : (T p (c : ZMod p) ^ s - 1) * ∑ u : (ZMod p)ˣ, T p (u : ZMod p) ^ s = 0 := by
    rw [sub_mul, hperm, one_mul, sub_self]
  exact (hunit.mul_right_eq_zero).mp h0

lemma y_eq_T {p n : ℕ} (hnp : n + 1 = p) (i : Fin n) :
    ((i.val + 1 : ℕ) : ZMod (p ^ 2)) ^ p = T p ((i.val + 1 : ℕ) : ZMod p) := by
  unfold T
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

lemma ne_zero_res {p n : ℕ} (hnp : n + 1 = p) (i : Fin n) :
    ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by omega) h
  omega

lemma sum_fin_eq {p n : ℕ} [hp : Fact p.Prime] (hnp : n + 1 = p) (s : ℕ) :
    ∑ i : Fin n, (((i.val + 1 : ℕ) : ZMod (p ^ 2)) ^ p) ^ s =
      ∑ u : (ZMod p)ˣ, T p (u : ZMod p) ^ s := by
  let e : Fin n → (ZMod p)ˣ := fun i => Units.mk0 _ (ne_zero_res hnp i)
  have hinj : Function.Injective e := by
    intro i j h
    have h' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p).val) h
    simp only [e, Units.val_mk0, ZMod.val_natCast] at h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    exact Fin.ext (by omega)
  have hbij : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).mpr
      ⟨hinj, by rw [Fintype.card_fin, ZMod.card_units]; omega⟩
  exact Fintype.sum_bijective e hbij _ _ (fun i => by simp only [e, Units.val_mk0]; rw [y_eq_T hnp i])

lemma y_pow_n {p n : ℕ} [hp : Fact p.Prime] (hnp : n + 1 = p) (i : Fin n) :
    (((i.val + 1 : ℕ) : ZMod (p ^ 2)) ^ p) ^ n = 1 := by
  rw [y_eq_T hnp i]
  have h := T_pow (ne_zero_res hnp i)
  rwa [show p - 1 = n by omega] at h

lemma phi_y {p n : ℕ} [hp : Fact p.Prime] (hnp : n + 1 = p) (i : Fin n) :
    phi p (((i.val + 1 : ℕ) : ZMod (p ^ 2)) ^ p) = ((i.val + 1 : ℕ) : ZMod p) := by
  rw [y_eq_T hnp i, phi_T]

lemma res_inj {p n : ℕ} (hnp : n + 1 = p) {i j : Fin n}
    (h : ((i.val + 1 : ℕ) : ZMod p) = ((j.val + 1 : ℕ) : ZMod p)) : i = j := by
  have h' := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h'
  exact Fin.ext (by omega)

theorem fourier (m : ℕ) (hp : (2 * m + 1).Prime) :
    let p := 2*m+1
    let y (i : Fin (2*m)) := ((i.val+1 : ℕ) : ZMod (p^2))^p
    let B : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
      if i=j then 0 else y i*(y i-y j)⁻¹
    ∃ V : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)), IsUnit V.det ∧
      ((2 : ZMod (p^2)) • B)*V =
        V*Matrix.diagonal (fun i : Fin (2*m) => 2*(i.val:ZMod (p^2))+1-2*m) := by
  intro p y B
  have : Fact p.Prime := ⟨hp⟩
  have hnp : 2 * m + 1 = p := rfl
  have hy1 : ∀ i, y i ^ (2 * m) = 1 := fun i => y_pow_n hnp i
  have hyu : ∀ i, IsUnit (y i) := fun i =>
    isUnit_of_phi hp (by rw [phi_y hnp i]; exact ne_zero_res hnp i)
  have hdiff : ∀ i j, i ≠ j → IsUnit (y i - y j) := by
    intro i j hij
    apply isUnit_of_phi hp
    rw [map_sub, phi_y hnp i, phi_y hnp j, sub_ne_zero]
    exact fun h => hij (res_inj hnp h)
  have hS : ∀ s, ∑ i, y i ^ s = if 2 * m ∣ s then ((2 * m : ℕ) : ZMod (p ^ 2)) else 0 := by
    intro s
    split_ifs with h
    · obtain ⟨c, rfl⟩ := h
      simp only [pow_mul, hy1, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    · show ∑ i : Fin (2 * m), (((i.val + 1 : ℕ) : ZMod (p ^ 2)) ^ p) ^ s = 0
      rw [sum_fin_eq hnp s]
      exact sum_units_pow s (by rwa [show p - 1 = 2 * m by omega])
  have hnu : IsUnit ((2 * m : ℕ) : ZMod (p ^ 2)) := by
    apply isUnit_of_phi hp
    rw [phi_natCast]
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; exact absurd hp (by norm_num)
      · omega) h
    omega
  refine ⟨Matrix.diagonal y * Matrix.vandermonde y, ?_, ?_⟩
  · apply isUnit_of_phi hp
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde, map_mul, map_prod, map_prod]
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [phi_y hnp i]
      exact ne_zero_res hnp i
    · rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [map_prod, Finset.prod_ne_zero_iff]
      intro j hj
      rw [map_sub, phi_y hnp i, phi_y hnp j, sub_ne_zero]
      intro h
      have := res_inj hnp h
      subst this
      simp at hj
  · ext j i
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    have hV : ∀ l : Fin (2 * m), (Matrix.diagonal y * Matrix.vandermonde y) l i = y l ^ (i.val + 1) := by
      intro l
      rw [Matrix.diagonal_mul, Matrix.vandermonde_apply]
      exact (pow_succ' (y l) i.val).symm
    simp only [hV, Matrix.smul_apply, smul_eq_mul]
    have hk := key y hy1 hyu hdiff hS hnu j (i.val + 1) (by omega) (by omega)
    have e : ∑ l, 2 * B j l * y l ^ (i.val + 1) =
        2 * ∑ l, (if j = l then 0 else y j * (y j - y l)⁻¹) * y l ^ (i.val + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [B]
      ring
    rw [e, hk]
    push_cast
    ring

end OMA.A1818Fourier

theorem OMA.solution : OMA.R_OeisA1818_conjecture2_R1_H2_R1_H2_R1.H2 := by
  intro m hp
  exact OMA.A1818Fourier.fourier m hp
