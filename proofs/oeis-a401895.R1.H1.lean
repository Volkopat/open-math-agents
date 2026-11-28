import OMAReductions.R_oeis_a401895_R1

-- Credit: @jiyongparkphysics
-- Background: M. F. Ezerman et al., On Polynomial Pairs of Integers (2015),
-- Propositions 10 and 14. The proof below specializes the no-carry argument to repdigits.

lemma shell_rigid (d : ℕ) (hd : d < 10) (xs : List ℕ) (hp : List.Palindrome xs)
    (he : Nat.ofDigits (10 : ℕ) xs = Nat.ofDigits 10 (List.replicate xs.length d)) :
    xs = List.replicate xs.length d := by
  induction hp with
  | nil => rfl
  | singleton x =>
    simpa using he
  | @cons_concat a l pal ih =>
    let mid := List.replicate l.length d
    have rep : List.replicate (a :: (l ++ [a])).length d = d :: (mid ++ [d]) := by
      simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add]
      rw [List.replicate_succ, List.replicate_succ']
    rw [rep] at he ⊢
    simp only [Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_nil, Nat.mul_zero,
      Nat.add_zero] at he
    have hml : mid.length = l.length := List.length_replicate
    rw [hml] at he
    have hsmall : Nat.ofDigits 10 mid < 10 ^ l.length := by
      rw [← hml]
      apply Nat.ofDigits_lt_base_pow_length (by decide)
      intro x hx
      have hxd : x = d := (List.mem_replicate.mp hx).2
      simpa [hxd] using hd
    have had : a ≤ d := by
      by_contra! ha
      have hgap := Nat.mul_le_mul_left (10 ^ l.length) (show d+1 ≤ a by omega)
      rw [Nat.mul_add, Nat.mul_one] at hgap
      omega
    have heq : a = d := by omega
    subst a
    have hmid : Nat.ofDigits 10 l = Nat.ofDigits 10 mid := by omega
    exact congrArg (fun z => d :: (z ++ [d])) (ih hmid)

lemma autocorr_impossible (j d : ℕ) (hj : 0 < j) (hd : 0 < d) (v : Fin (j+1) → ℕ)
    (endpoint : v 0 * v (Fin.last j) = d) (center : (∑ i, v i * v i) = d) : False := by
  have hne : (0 : Fin (j+1)) ≠ Fin.last j := by
    intro h
    have h' := congrArg Fin.val h
    change 0 = j at h'
    omega
  have hp : (∑ i ∈ ({0, Fin.last j} : Finset (Fin (j+1))), v i * v i) ≤ ∑ i, v i * v i :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simp [hne] at hp
  rw [center] at hp
  have h := two_mul_le_add_sq (v 0) (v (Fin.last j))
  nlinarith [h, hp, endpoint]

open Finset

namespace DigitAutocorrelation

private lemma evalVector {m : ℕ} (v : Fin m → ℕ) :
    Nat.ofDigits 10 (List.ofFn v) = ∑ i, v i * 10 ^ i.val := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ, ih, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => by ring)

private lemma reverseVector {m : ℕ} (v : Fin m → ℕ) :
    (List.ofFn v).reverse = List.ofFn (fun i => v i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_reverse, Fin.rev]
    apply congrArg v
    apply Fin.ext
    dsimp
    omega

private def position {j : ℕ} (i h : Fin (j+1)) : Fin (2*j+1) :=
  ⟨i.val + (j-h.val), by have := i.isLt; omega⟩

private def corr {j : ℕ} (v : Fin (j+1) → ℕ) (k : Fin (2*j+1)) : ℕ :=
  ∑ i, ∑ h, if k = position i h then v i * v h else 0

private lemma mirror {j : ℕ} (v : Fin (j+1) → ℕ) (k : Fin (2*j+1)) :
    corr v k.rev = corr v k := by
  unfold corr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro h _
  have he : k.rev = position h i ↔ k = position i h := by
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only [Fin.rev, position]
    have := i.isLt
    have := h.isLt
    have := k.isLt
    omega
  simp [he, Nat.mul_comm]

private lemma productVector {j : ℕ} (v : Fin (j+1) → ℕ) :
    Nat.ofDigits 10 (List.ofFn (corr v)) =
      Nat.ofDigits 10 (List.ofFn v) * Nat.ofDigits 10 (List.ofFn v).reverse := by
  rw [reverseVector, evalVector, evalVector, evalVector]
  have hre : (∑ i : Fin (j+1), v i.rev * 10^i.val) =
      ∑ h : Fin (j+1), v h * 10^(j-h.val) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    simp [Fin.revPerm, Fin.rev_rev, Fin.val_rev]
  rw [hre, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ k : Fin (2*j+1), ∑ i : Fin (j+1), ∑ h : Fin (j+1),
           if k = position i h then v i * v h * 10^k.val else 0 := by
      simp only [corr, Finset.sum_mul, ite_mul, zero_mul]
    _ = ∑ i : Fin (j+1), ∑ h : Fin (j+1), ∑ k : Fin (2*j+1),
           if k = position i h then v i * v h * 10^k.val else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      simp [position, pow_add, Nat.mul_left_comm, Nat.mul_assoc]

private lemma centerCoeff {j : ℕ} (v : Fin (j+1) → ℕ) :
    corr v ⟨j, by omega⟩ = ∑ i, v i * v i := by
  unfold corr
  apply Finset.sum_congr rfl
  intro i _
  have he (h : Fin (j+1)) : (⟨j, by omega⟩ : Fin (2*j+1)) = position i h ↔ h = i := by
    rw [Fin.ext_iff, Fin.ext_iff]
    dsimp [position]
    have := h.isLt
    omega
  simp [he]

private lemma endCoeff {j : ℕ} (v : Fin (j+1) → ℕ) :
    corr v 0 = v 0 * v (Fin.last j) := by
  unfold corr
  have he (i h : Fin (j+1)) : (0 : Fin (2*j+1)) = position i h ↔ i = 0 ∧ h = Fin.last j := by
    simp only [Fin.ext_iff, position, Fin.val_zero, Fin.val_last]
    have := h.isLt
    omega
  simp_rw [he, ite_and]
  simp

theorem convolution_obstruction
    (rigid : ∀ (d : ℕ), d < 10 → ∀ xs : List ℕ, List.Palindrome xs →
      Nat.ofDigits 10 xs = Nat.ofDigits 10 (List.replicate xs.length d) →
      xs = List.replicate xs.length d)
    (impossible : ∀ (j d : ℕ), 0 < j → 0 < d → ∀ v : Fin (j+1) → ℕ,
      v 0 * v (Fin.last j) = d → (∑ i, v i * v i) = d → False)
    (ds : List ℕ) (j d : ℕ) (hlen : ds.length=j+1) (hj : 0<j) (hd : 0<d) (hd' : d<10)
    (prod : Nat.ofDigits 10 ds * Nat.ofDigits 10 ds.reverse =
      Nat.ofDigits 10 (List.replicate (2*j+1) d)) : False := by
  let v (i : Fin (j+1)) := ds[i.val]'(by have := i.isLt; omega)
  have hv : List.ofFn v = ds := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro i hi hj'
      rw [List.getElem_ofFn]
  have hp : List.Palindrome (List.ofFn (corr v)) := by
    apply List.Palindrome.iff_reverse_eq.mpr
    rw [reverseVector]
    simp [mirror]
  have he := rigid d hd' (List.ofFn (corr v)) hp (by
    rw [productVector, hv, List.length_ofFn]
    exact prod)
  have uniform (i : Fin (2*j+1)) : corr v i = d := by
    have hm : corr v i ∈ List.ofFn (corr v) := List.mem_ofFn.mpr ⟨i, rfl⟩
    rw [he] at hm
    exact List.eq_of_mem_replicate hm
  apply impossible j d hj hd v
  · rw [← endCoeff]
    exact uniform 0
  · rw [← centerCoeff]
    exact uniform _

end DigitAutocorrelation

open OMA.S_oeis_a401895
open OMA.R_oeis_a401895_R1

namespace OddRepdigit

-- The digit-polynomial obstruction is separated so the length and digit cases can be checked alone.
theorem of_convolution
    (obstruction : ∀ (ds : List ℕ) (j d : ℕ), ds.length = j+1 → 0<j → 0<d → d<10 →
      Nat.ofDigits 10 ds * Nat.ofDigits 10 ds.reverse =
        Nat.ofDigits 10 (List.replicate (2*j+1) d) → False) :
    OMA.R_oeis_a401895_R1.H1 := by
  intro n d j hn hd hsmall he
  obtain ⟨a,u,hu⟩ := List.exists_cons_of_ne_nil
    (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega : n ≠ 0) : Nat.digits 10 n ≠ [])
  obtain ⟨b,v,hv⟩ := List.exists_cons_of_ne_nil (show (Nat.digits 10 n).reverse ≠ [] by simp [hu])
  have hbds : Nat.digits 10 n = v.reverse ++ [b] := by simpa using congrArg List.reverse hv
  have hrds : (Nat.digits 10 n).reverse = u.reverse ++ [a] := by simp [hu]
  have len : v.length = u.length := by
    have e := congrArg List.length hv
    simpa [hu] using e.symm
  have small : ∀ x ∈ Nat.digits 10 n, x < 10 := fun _ h => Nat.digits_lt_base (by decide) h
  have nval := Nat.ofDigits_digits 10 n
  have nunit : n%10 = a := by
    rw [← nval, hu, Nat.ofDigits_cons]
    simpa [Nat.add_mul_mod_self_left] using Nat.mod_eq_of_lt (small a (hu ▸ List.mem_cons_self))
  have runit : R n%10 = b := by
    have hb : b < 10 := small b (by simp [hbds])
    simp [R,hv,Nat.ofDigits_cons,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hb]
  let P := 10^u.length
  have N : b*P ≤ n ∧ n < (b+1)*P := by
    have := last_bounds v.reverse b (fun x hx => small x (by rw [hbds]; exact List.mem_append_left _ hx))
    simpa only [← hbds, nval, List.length_reverse, len, P] using this
  have M : a*P ≤ R n ∧ R n < (a+1)*P := by
    have := last_bounds u.reverse a (fun x hx => small x (by rw [hu]; exact List.mem_cons_of_mem _ (List.mem_reverse.mp hx)))
    simpa only [← hrds, R, List.length_reverse,P] using this
  have value : n*R n = Nat.ofDigits 10 (List.replicate (2*j+1) d) := by
    simpa only [Nat.ofDigits_digits] using congrArg (Nat.ofDigits (10 : ℕ)) he
  have units : (a*b)%10 = d := by
    have eq := congrArg (· % 10) value
    rw [List.replicate_succ, Nat.ofDigits_cons, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hsmall, Nat.mul_mod, nunit, runit] at eq
    exact eq
  have ha : a < 10 := nunit ▸ Nat.mod_lt _ (by decide)
  have hb : b < 10 := runit ▸ Nat.mod_lt _ (by decide)
  have apos : 0 < a := by by_contra! hz; simp [show a = 0 by omega] at units; omega
  have bpos : 0 < b := by by_contra! hz; simp [show b = 0 by omega] at units; omega
  have boundlo : (b*a)*(P*P) ≤ n*R n := by simpa only [Nat.mul_mul_mul_comm] using Nat.mul_le_mul N.1 M.1
  have boundhi : n*R n < ((b+1)*(a+1))*(P*P) := by
    convert Nat.mul_lt_mul_of_lt_of_lt N.2 M.2 using 1; ring
  have lo : 10^(2*u.length) ≤ n*R n := by
    rw [Nat.mul_comm 2, pow_mul, pow_two]
    dsimp only [P] at boundlo
    exact (Nat.le_mul_of_pos_left _ (Nat.mul_pos bpos apos)).trans boundlo
  have hi : n*R n < 10^(2*(u.length+1)) := by
    have cap : (b+1)*(a+1) ≤ 100 := Nat.mul_le_mul (by omega : b+1 ≤ 10) (by omega : a+1 ≤ 10)
    calc
      _ < _ := boundhi
      _ ≤ 100 * (P*P) := Nat.mul_le_mul_right _ cap
      _ = _ := by rw [Nat.mul_comm 2,pow_mul,pow_succ (10:ℕ) u.length]; dsimp only [P]; ring
  have lowLen := (Nat.lt_digits_length_iff (by decide : 1<10) _).mpr lo
  have highLen := (Nat.digits_length_le_iff (by decide : 1<10) _).mpr hi
  rw [he,List.length_replicate] at lowLen highLen
  have lengths : j = u.length := by omega
  by_cases hj : 0 < j
  · apply obstruction (Nat.digits 10 n) j d (by simp [hu,lengths]) hj hd hsmall
    simpa only [Nat.ofDigits_digits,R] using value
  · have hj0 : j = 0 := by omega
    have hu0 : u = [] := List.length_eq_zero_iff.mp (by omega)
    have hna : n = a := by simpa [hu,hu0] using nval.symm
    have rev : R n = n := by simp [R,hu,hu0,hna.symm]
    simp [hj0,rev] at value
    nlinarith

end OddRepdigit

theorem OMA.solution : OMA.R_oeis_a401895_R1.H1 :=
  OddRepdigit.of_convolution (DigitAutocorrelation.convolution_obstruction shell_rigid autocorr_impossible)
