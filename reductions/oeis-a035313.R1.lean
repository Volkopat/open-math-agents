import OMAStatements.S_oeis_a035313

/-!
# The diagonal ratio of the Zorach triangle and collisions in trial rows

David W. Wilson conjectured that every positive integer occurs in the
diagonal or one of its iterated differences, and that the diagonal ratio
tends to two (https://oeis.org/A035313). This file proves the ratio limit
unconditionally. The greedy rule gives a cubic upper bound for the first
entry of each row. The diagonal is its binomial transform, and the centered
eighth moment of a binomial walk controls the change in consecutive terms.

For the remaining coverage question we prove that a rejected unused trial
must have an interior collision, with the blocking entry closer to the
right edge in its own row. The two residual hypotheses concern collisions
in bounded columns and collisions past a fixed column cutoff.
-/
namespace Zorach
open OMA.S_oeis_a035313

private theorem row_translate (l : List ℕ) (m b : ℕ) :
    nextRow l (m+b) = (nextRow l b).map (m+·) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [nextRow,List.scanl_cons,List.map_cons,List.cons.injEq,true_and]
    simpa only [nextRow,Nat.add_assoc] using ih (b+a)

private theorem row_ge (l : List ℕ) (m x : ℕ) (hx : x∈nextRow l m) : m≤x := by
  induction l generalizing m with
  | nil => simp [nextRow] at hx; omega
  | cons a l ih =>
    simp only [nextRow,List.scanl_cons] at hx
    rcases List.mem_cons.mp hx with rfl|hx
    · omega
    · have := ih (m+a) hx; omega

theorem nextRow_nodup (l : List ℕ) (hp : ∀ x ∈ l, 0<x) (m : ℕ) :
    (nextRow l m).Nodup := by
  induction l generalizing m with
  | nil => simp [nextRow]
  | cons a l ih =>
    simp only [nextRow,List.scanl_cons]
    refine List.nodup_cons.mpr ⟨?_, ih (fun x hx => hp x (List.mem_cons_of_mem _ hx)) _⟩
    intro hm
    have := row_ge l (m+a) m hm
    have := hp a List.mem_cons_self
    omega

/-- Each old entry and each new position forbid at most one positive starting value. -/
theorem admissible_witness (used prev : List ℕ) (hp : ∀ x ∈ prev, 0<x) :
    ∃ m, Admissible used prev m ∧ m ≤ used.length*(prev.length+1)+1 := by
  classical
  let off := nextRow prev 0
  let pairs := used.toFinset ×ˢ off.toFinset
  let bad := pairs.image (fun p : ℕ×ℕ => p.1-p.2)
  let B := used.length*(prev.length+1)+1
  have bad_card : bad.card < B := by
    have hlen : off.length=prev.length+1 := List.length_scanl
    have ho := List.toFinset_card_le (l:=off)
    have hu := List.toFinset_card_le (l:=used)
    have h := Finset.card_image_le (f:=fun p : ℕ×ℕ => p.1-p.2) (s:=pairs)
    have hprod := Nat.mul_le_mul hu ho
    rw [hlen] at hprod
    simp only [pairs,Finset.card_product] at h
    dsimp only [B,bad,pairs]
    omega
  obtain ⟨m,hm,hgood⟩ : ∃ m∈Finset.Icc 1 B, m∉bad := by
    by_contra! all
    have hc := Finset.card_le_card (show Finset.Icc 1 B ⊆ bad from all)
    rw [Nat.card_Icc] at hc
    omega
  obtain ⟨hmpos,hmB⟩ := Finset.mem_Icc.mp hm
  refine ⟨m, ⟨hmpos,nextRow_nodup prev hp m,?_⟩,hmB⟩
  intro x hx hxused
  have tr : nextRow prev m = off.map (m+·) := by simpa only [Nat.add_zero] using row_translate prev m 0
  rw [tr] at hx
  obtain ⟨d,hd,he⟩ := List.mem_map.mp hx
  apply hgood
  refine Finset.mem_image.mpr ⟨(x,d),Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hxused,List.mem_toFinset.mpr hd⟩,?_⟩
  dsimp
  omega

theorem start_sInf (n : ℕ) : ((state (n+1)).2.headD 0) = sInf {m | Admissible (state n).1 (state n).2 m} := by
  simp [state,nextRow,List.headD_eq_head?_getD]

theorem row_from_start (n : ℕ) : (state (n+1)).2 = nextRow (state n).2 (((state (n+1)).2.headD 0)) := by
  rw [start_sInf]; rfl

theorem start_le_admissible (n m : ℕ) (h : Admissible (state n).1 (state n).2 m) : ((state (n+1)).2.headD 0) ≤ m := by
  rw [start_sInf]; exact Nat.sInf_le h

theorem row_pos (n x : ℕ) (hx : x ∈ (state n).2) : 0 < x := by
  induction n generalizing x with
  | zero => simp [state] at hx; omega
  | succ n ih =>
    obtain ⟨m,hm,_⟩ := admissible_witness (state n).1 (state n).2 ih
    have adm := Nat.sInf_mem (⟨m,hm⟩ : {v | Admissible (state n).1 (state n).2 v}.Nonempty)
    rw [row_from_start,start_sInf] at hx
    exact lt_of_lt_of_le adm.1 (row_ge _ _ x hx)

theorem start_admissible (n : ℕ) : Admissible (state n).1 (state n).2 (((state (n+1)).2.headD 0)) := by
  obtain ⟨m,hm,_⟩ := admissible_witness (state n).1 (state n).2 (row_pos n)
  rw [start_sInf]
  exact Nat.sInf_mem (⟨m,hm⟩ : {v | Admissible (state n).1 (state n).2 v}.Nonempty)

theorem start_pos (n : ℕ) : 0 < ((state n).2.headD 0) := by
  cases n with
  | zero => decide
  | succ n => exact (start_admissible n).1

private theorem row_length_greedy (n : ℕ) : (state n).2.length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [row_from_start,nextRow,List.length_scanl,ih]

theorem used_length_twice (n : ℕ) : 2*(state n).1.length = (n+1)*(n+2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : (state (n+1)).1=(state n).1++(state (n+1)).2 := rfl
    rw [e,List.length_append,row_length_greedy]
    nlinarith only [ih]

theorem start_product_bound (n : ℕ) : ((state (n+1)).2.headD 0) ≤ (state n).1.length * (n+2)+1 := by
  obtain ⟨m,hm,hb⟩ := admissible_witness (state n).1 (state n).2 (row_pos n)
  rw [row_length_greedy] at hb
  exact (start_le_admissible n m hm).trans hb

theorem start_bound_twice (n : ℕ) : 2*((state (n+1)).2.headD 0) ≤ (n+1)*(n+2)^2+2 := by
  have hsize := congrArg (fun k : ℕ => k*(n+2)) (used_length_twice n)
  nlinarith only [hsize,start_product_bound n]

theorem start_bound (n : ℕ) : ((state n).2.headD 0) ≤ (n+2)^3 := by
  cases n with
  | zero => decide
  | succ n =>
    have hlen := used_length_twice n
    have h := start_product_bound n
    nlinarith only [h, congrArg (fun x : ℕ => x*(n+2)) hlen, hlen, Nat.zero_le n]

end Zorach

namespace Zorach
open OMA.S_oeis_a035313 Finset

theorem row_length (n : ℕ) : (state n).2.length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [state, nextRow, List.length_scanl, ih]

/-- Each entry to the right adds the entry immediately above its left neighbor. -/
theorem row_add {n i : ℕ} (hi : i ≤ n) :
    (state (n+1)).2.getD (i+1) 0 =
      (state (n+1)).2.getD i 0 + (state n).2.getD i 0 := by
  let prev := (state n).2
  let m := sInf {m | Admissible (state n).1 prev m}
  have len : i < prev.length := by simpa [prev,row_length] using hi
  have h := List.getElem_succ_scanl (l := prev) (b := m) (f := (·+·))
      (show i+1 < (prev.scanl (·+·) m).length by simpa using len)
  change (prev.scanl (·+·) m).getD (i+1) 0 =
    (prev.scanl (·+·) m).getD i 0 + prev.getD i 0
  simpa only [List.getD_eq_getElem?_getD, getElem?_pos prev i len,
    getElem?_pos (prev.scanl (·+·) m) (i+1) (show i+1 < (prev.scanl (·+·) m).length by simpa using len),
    getElem?_pos (prev.scanl (·+·) m) i (show i < (prev.scanl (·+·) m).length by simp; omega),
    Option.getD_some] using h

/-- The j-th forward difference, at position n, is column n of row n+j. -/
theorem diff_entry (j n : ℕ) :
    diff j (fun k => (a k : ℤ)) n = ((state (n+j)).2.getD n 0 : ℤ) := by
  induction j generalizing n with
  | zero =>
    simp only [diff,a,Nat.add_zero,List.getLastD_eq_getLast?,List.getLast?_eq_getElem?,
      row_length,Nat.add_sub_cancel,List.getD_eq_getElem?_getD]
  | succ j ih =>
    simp only [diff,ih]
    rw [show n+1+j=n+j+1 by omega, show n+(j+1)=n+j+1 by omega,
      row_add (show n ≤ n+j by omega),Nat.cast_add]
    abel

theorem difference_of_mem {m t : ℕ} (hm : m ∈ (state t).2) :
    ∃ j n : ℕ, diff j (fun k => (a k : ℤ)) n = m := by
  obtain ⟨n,hn,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨t-n,n,?_⟩
  have hnt : n ≤ t := by simpa only [row_length,Nat.lt_succ_iff] using hn
  rw [diff_entry, Nat.add_sub_of_le hnt, List.getD_eq_getElem?_getD,
    getElem?_pos (state t).2 n hn, Option.getD_some, he]

private theorem diff_eq_iter (f : ℕ → ℤ) (j : ℕ) : diff j f = (fwdDiff 1)^[j] f := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',←ih]
    rfl

/-- The Gregory–Newton coefficients at zero are the first entries of the rows. -/
theorem diagonal (n : ℕ) : a n = ∑ k ∈ range (n+1), n.choose k * ((state k).2.headD 0) := by
  have hn := shift_eq_sum_fwdDiff_iter 1 (fun k : ℕ => (a k : ℤ)) n 0
  simp only [nsmul_eq_mul,mul_one,zero_add,←diff_eq_iter,diff_entry,
    List.getD_eq_getElem?_getD,←List.head?_eq_getElem?,←List.headD_eq_head?_getD] at hn
  exact_mod_cast hn

end Zorach

namespace Zorach
open OMA.S_oeis_a035313 Finset

/-- An arbitrary triangle entry is a binomially weighted consecutive block of row starts. -/
theorem binomial_entry (j n : ℕ) :
    (state (n+j)).2.getD n 0 = ∑ k ∈ range (n+1), n.choose k * ((state (j+k)).2.headD 0) := by
  have iter (f : ℕ → ℤ) (u : ℕ) : (fwdDiff 1)^[u] f = diff u f := by
    induction u with
    | zero => rfl
    | succ u ih => rw [Function.iterate_succ_apply',ih]; rfl
  have comp (f : ℕ → ℤ) (v u : ℕ) : diff u (diff v f) = diff (v+u) f := by
    induction u with
    | zero => rfl
    | succ u ih =>
      funext k
      change diff u (diff v f) (k+1) - diff u (diff v f) k =
        diff (v+u) f (k+1) - diff (v+u) f k
      rw [ih]
  have h := shift_eq_sum_fwdDiff_iter 1 (diff j (fun k => (a k : ℤ))) n 0
  simp only [nsmul_eq_mul,mul_one,zero_add,iter,comp,diff_entry,
    List.getD_eq_getElem?_getD,←List.head?_eq_getElem?,←List.headD_eq_head?_getD] at h
  exact_mod_cast h

theorem entry_index_bound (pos : ∀ j, 0 < ((state j).2.headD 0)) (j n : ℕ) :
    n ≤ Nat.log 2 ((state (n+j)).2.getD n 0) := by
  apply Nat.le_log_of_pow_le (by decide)
  rw [binomial_entry,←Nat.sum_range_choose]
  apply sum_le_sum
  intro k hk
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n.choose k) (pos (j+k))

/-- Coverage of m can only occur through the finitely many binomial lengths n ≤ log₂(m). -/
theorem coverage_iff_blocks (pos : ∀ j, 0 < ((state j).2.headD 0)) (m : ℕ) :
    (∃ j n : ℕ, diff j (fun k => (a k : ℤ)) n = m) ↔
      ∃ (n j : ℕ), n ≤ Nat.log 2 m ∧
        (∑ k ∈ range (n+1), n.choose k * ((state (j+k)).2.headD 0)) = m := by
  constructor
  · rintro ⟨j,n,h⟩
    rw [diff_entry, Nat.cast_inj] at h
    exact ⟨n,j,h ▸ entry_index_bound pos j n,(binomial_entry j n).symm.trans h⟩
  · rintro ⟨n,j,_,h⟩
    exact ⟨j,n,by rw [diff_entry,binomial_entry,h]⟩

end Zorach

namespace Zorach
open OMA.S_oeis_a035313 Filter

theorem start_mem_row (n : ℕ) : ((state n).2.headD 0) ∈ (state n).2 := by
  cases n with
  | zero => simp [state]
  | succ n =>
    rw [row_from_start]
    apply List.mem_of_head?
    simp [nextRow]

theorem used_to_row_le {m n : ℕ} (h : m∈(state n).1) : ∃ t, t ≤ n ∧ m∈(state t).2 := by
  induction n with
  | zero => exact ⟨0,le_rfl,h⟩
  | succ n ih =>
    change m ∈ (state n).1 ++ (state (n+1)).2 at h
    rcases List.mem_append.mp h with h|h
    · obtain ⟨t,ht,hmem⟩ := ih h
      exact ⟨t,by omega,hmem⟩
    · exact ⟨n+1,le_rfl,h⟩

theorem used_to_row {m n : ℕ} (h : m∈(state n).1) : ∃ t, m∈(state t).2 := by
  obtain ⟨t,_,ht⟩ := used_to_row_le h
  exact ⟨t,ht⟩

private theorem row_to_used {m n : ℕ} (hm : m∈(state n).2) : m∈(state n).1 := by
  cases n with
  | zero => exact hm
  | succ n => exact List.mem_append.mpr (Or.inr hm)

private theorem used_later {m n k : ℕ} (hn : n≤k) (hm : m∈(state n).1) : m∈(state k).1 := by
  induction k,hn using Nat.le_induction with
  | base => exact hm
  | succ k hk ih => exact List.mem_append.mpr (Or.inl ih)

private theorem start_ne_later {i j : ℕ} (h : i<j) : ((state i).2.headD 0) ≠ ((state j).2.headD 0) := by
  cases j with
  | zero => omega
  | succ j =>
    have hold := used_later (show i≤j by omega) (row_to_used (start_mem_row i))
    have hnew : ((state (j+1)).2.headD 0) ∈ nextRow (state j).2 (((state (j+1)).2.headD 0)) := by
      apply List.mem_of_head?
      simp [nextRow]
    have hdisj := (start_admissible j).2.2 _ hnew
    intro eq
    exact hdisj (eq ▸ hold)

theorem start_injective : Function.Injective (fun n : ℕ => (state n).2.headD 0) := by
  intro i j he
  rcases lt_trichotomy i j with h|h|h
  · exact (start_ne_later h he).elim
  · exact h
  · exact (start_ne_later h he.symm).elim

theorem big_starts (m : ℕ) : ∀ᶠ n in atTop, m < ((state (n+1)).2.headD 0) := by
  have inj : Function.Injective (fun n : ℕ => ((state (n+1)).2.headD 0)) := by
    intro i j h
    have := start_injective h
    omega
  exact inj.nat_tendsto_atTop.eventually_gt_atTop m

theorem exists_conflict (n m : ℕ) (hm : 0 < m) (hsmall : m < ((state (n+1)).2.headD 0)) :
    ∃ x∈nextRow (state n).2 m, x∈(state n).1 := by
  by_contra! hf
  have hadm : Admissible (state n).1 (state n).2 m :=
    ⟨hm,nextRow_nodup _ (row_pos n) _,hf⟩
  have := start_le_admissible n m hadm
  omega

end Zorach

namespace Zorach
open OMA.S_oeis_a035313 Finset

/-- An elementary square bound for the largest weight in an even binomial row. -/
theorem central_atom_bound (n : ℕ) : (n+1)*(n.centralBinom)^2 ≤ 16^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have step := Nat.succ_mul_centralBinom_succ n
    have numerical : (n+2)*(2*(2*n+1))^2 ≤ 16*(n+1)^3 := by nlinarith
    apply Nat.le_of_mul_le_mul_left (c:=(n+1)^2) _ (by positivity)
    calc
      (n+1)^2*((n+1+1)*((n+1).centralBinom)^2) =
          (n+2)*((n+1)*(n+1).centralBinom)^2 := by ring
      _ = (n+2)*(2*(2*n+1))^2*(n.centralBinom)^2 := by rw [step]; ring
      _ ≤ (16*(n+1)^3)*(n.centralBinom)^2 := Nat.mul_le_mul_right _ numerical
      _ = ((n+1)^2*16)*((n+1)*(n.centralBinom)^2) := by ring
      _ ≤ ((n+1)^2*16)*16^n := Nat.mul_le_mul_left _ ih
      _ = (n+1)^2*16^(n+1) := by ring

theorem binomial_atom_bound (n k : ℕ) : (n/2+1)*(n.choose k)^2 ≤ (2^n)^2 := by
  let t := n/2
  have eqn : n=2*t ∨ n=2*t+1 := by dsimp [t]; omega
  have powers : (2^(2*t))^2 = 16^t := by
    calc
      (2^(2*t))^2 = 2^(2*t*2) := (pow_mul _ _ _).symm
      _ = 2^(4*t) := by congr 1; ring
      _ = (2^4)^t := pow_mul _ _ _
      _ = 16^t := rfl
  rcases eqn with he|ho
  · change (t+1)*(n.choose k)^2 ≤ (2^n)^2
    rw [he]
    calc
      (t+1)*((2*t).choose k)^2 ≤ (t+1)*(t.centralBinom)^2 := by
        gcongr; exact Nat.choose_le_centralBinom _ _
      _ ≤ 16^t := central_atom_bound _
      _ = (2^(2*t))^2 := powers.symm
  · change (t+1)*(n.choose k)^2 ≤ (2^n)^2
    rw [ho]
    have odd_atom : (2*t+1).choose k ≤ 2*t.centralBinom := by
      cases k with
      | zero => simp; have := Nat.centralBinom_pos t; omega
      | succ k =>
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one]
        have := Nat.choose_le_centralBinom k t
        have := Nat.choose_le_centralBinom (k+1) t
        omega
    calc
      (t+1)*((2*t+1).choose k)^2 ≤ (t+1)*(2*t.centralBinom)^2 := by gcongr
      _ = 4*((t+1)*(t.centralBinom)^2) := by ring
      _ ≤ 4*16^t := Nat.mul_le_mul_left _ (central_atom_bound _)
      _ = (2^(2*t+1))^2 := by rw [pow_succ (2:ℕ) (2*t), mul_pow, powers]; ring

/-- The diagonal grows at least as the binomial mass times the square root of its index. -/
theorem diagonal_sqrt_lower (b n : ℕ) (hn : 32*b^2 ≤ n) : b*2^n ≤ a n := by
  let s := (range (n+1)).filter fun k => ((state k).2.headD 0) < 2*b
  let t := (range (n+1)).filter fun k => ¬ ((state k).2.headD 0) < 2*b
  have small_card : s.card ≤ 2*b := by
    have subset : s.image (fun n : ℕ => (state n).2.headD 0) ⊆ range (2*b) := by
      intro x hx
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
      exact mem_range.mpr (mem_filter.mp hk).2
    simpa only [card_image_of_injective s start_injective, card_range] using card_le_card subset
  have atom (k : ℕ) : 4*b*n.choose k ≤ 2^n := by
    have num : (4*b)^2 ≤ n/2+1 := by
      calc
        (4*b)^2 = 16*b^2 := by ring
        _ ≤ n/2+1 := by omega
    have h := (Nat.mul_le_mul_right ((n.choose k)^2) num).trans (binomial_atom_bound n k)
    rw [←mul_pow] at h
    exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp h
  have atom' := atom (n/2)
  have mass : ∑ k ∈ s, n.choose k ≤ s.card*(n.choose (n/2)) := by
    simpa using s.sum_le_card_nsmul (fun k => n.choose k) (n.choose (n/2))
      (fun k _ => Nat.choose_le_middle k n)
  have mass' := mass.trans (Nat.mul_le_mul_right _ small_card)
  have splitmass : (∑ k ∈ s, n.choose k)+(∑ k ∈ t,n.choose k)=2^n := by
    rw [←Nat.sum_range_choose]
    exact sum_filter_add_sum_filter_not _ _ _
  rw [show 4*b*n.choose (n/2)= 2*(2*b*n.choose (n/2)) by ring] at atom'
  have large : 2^n ≤ 2*(∑ k ∈ t,n.choose k) := by omega
  calc
    b*2^n ≤ b*(2*(∑ k ∈ t,n.choose k)) := Nat.mul_le_mul_left _ large
    _ = ∑ k ∈ t, n.choose k*(2*b) := by rw [←sum_mul]; ring
    _ ≤ ∑ k ∈ t, n.choose k*((state k).2.headD 0) := by
      apply sum_le_sum; intro k hk
      exact Nat.mul_le_mul_left _ (Nat.le_of_not_gt (mem_filter.mp hk).2)
    _ ≤ ∑ k ∈ range (n+1), n.choose k*((state k).2.headD 0) := sum_le_sum_of_subset (filter_subset _ _)
    _ = a n := (diagonal n).symm

end Zorach

namespace Zorach
open OMA.S_oeis_a035313 Filter

theorem diagonal_normalized_unbounded :
    Tendsto (fun n => (a n : ℝ)/2^n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨b,hb⟩ := exists_nat_ge B
  filter_upwards [eventually_ge_atTop (32*b^2)] with n hn
  refine hb.trans ((le_div_iff₀ (by positivity : 0 < (2:ℝ)^n)).mpr ?_)
  exact_mod_cast diagonal_sqrt_lower b n hn

end Zorach

namespace Zorach
open OMA.S_oeis_a035313

private theorem trial_step {l : List ℕ} (m i : ℕ) (hi : i < l.length) :
    (nextRow l m).getD (i+1) 0 = (nextRow l m).getD i 0 + l.getD i 0 := by
  have h := List.getElem_succ_scanl (l := l) (b := m) (f := (·+·))
    (show i+1 < (l.scanl (·+·) m).length by simpa using hi)
  unfold nextRow
  simpa only [List.getD_eq_getElem?_getD, getElem?_pos l i hi,
    getElem?_pos (l.scanl (·+·) m) (i+1) (show i+1 < (l.scanl (·+·) m).length by simpa using hi),
    getElem?_pos (l.scanl (·+·) m) i (show i < (l.scanl (·+·) m).length by simp; omega),
    Option.getD_some] using h

private theorem trial_floor {l : List ℕ} (m i : ℕ) (hi : i ≤ l.length) :
    m ≤ (nextRow l m).getD i 0 := by
  induction i with
  | zero => simp [nextRow,List.getD_eq_getElem?_getD]
  | succ i ih =>
    rw [trial_step m i (by omega)]
    exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

/-- Along a row entries are nondecreasing, as are entries along southeast diagonals. -/
theorem old_entry_le {s j n i : ℕ} (hs : s ≤ n) (hj : j ≤ s) (hi : i ≤ n)
    (hcone : j + (n-s) ≤ i) :
    (state s).2.getD j 0 ≤ (state n).2.getD i 0 := by
  have diag (d : ℕ) : (state s).2.getD j 0 ≤ (state (s+d)).2.getD (j+d) 0 := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.add_succ, Nat.add_succ, row_add (show j+d ≤ s+d by omega)]
      exact ih.trans (Nat.le_add_left _ _)
  have east {u v : ℕ} (huv : u ≤ v) (hv : v ≤ n) :
      (state n).2.getD u 0 ≤ (state n).2.getD v 0 := by
    induction v with
    | zero => have := Nat.eq_zero_of_le_zero huv; subst u; rfl
    | succ v ih =>
      by_cases he : u=v+1
      · subst u; rfl
      · have curr := ih (by omega) (by omega)
        obtain ⟨n',rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
        rw [row_add (show v ≤ n' by omega)]
        exact curr.trans (Nat.le_add_right _ _)
  have chain := diag (n-s)
  rw [Nat.add_sub_of_le hs] at chain
  exact chain.trans (east hcone hi)

/-- Any previous entry hit by a positive-column conflict is strictly nearer the right edge. -/
theorem collision_cone {m n s j k : ℕ} (hm : 0 < m) (hs : s ≤ n) (hj : j ≤ s)
    (hk : 0 < k) (hb : k ≤ n+1)
    (he : (nextRow (state n).2 m).getD k 0 = (state s).2.getD j 0) :
    s-j < n+1-k := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  by_contra! hbad
  have hprev := old_entry_le hs hj (show k ≤ n by omega) (show j+(n-s) ≤ k by omega)
  have len : k < (state n).2.length := by rw [row_length]; omega
  rw [trial_step m k len] at he
  have hpos := trial_floor (l:=(state n).2) m k (by omega)
  omega

end Zorach

namespace Zorach
open OMA.S_oeis_a035313

/-- Arbitrarily late doublings overshoot every candidate start allowed by the cubic bound. -/
theorem large_doubling (N : ℕ) : ∃ n ≥ N, 2*a n+(n+3)^3 < a (n+1) := by
  by_contra! bounded
  let C := a N+(N+6)^3
  have control (d : ℕ) : a (N+d)+(N+d+6)^3 ≤ C*2^d := by
    induction d with
    | zero => simp [C]
    | succ d ih =>
      have h := bounded (N+d) (Nat.le_add_right _ _)
      have hp (n : ℕ) : (n+3)^3+(n+1+6)^3 ≤ 2*(n+6)^3 := by
        have eq : (n+3)^3+(n+1+6)^3 + (6*n^2+42*n+62) = 2*(n+6)^3 := by ring
        omega
      have p := hp (N+d)
      change a (N+d+1)+(N+d+1+6)^3 ≤ C*2^(d+1)
      rw [pow_succ (2:ℕ) d, ←mul_assoc]
      omega
  let d := 32*(C+1)^2
  have lower := diagonal_sqrt_lower (C+1) (N+d) (by dsimp [d]; omega)
  have upper := control d
  have order : 2^d ≤ 2^(N+d) := Nat.pow_le_pow_right (by decide) (by omega)
  have ind := (Nat.mul_le_mul_left (C+1) order).trans lower
  rw [Nat.add_mul,one_mul] at ind
  have hp : 0 < (2:ℕ)^d := pow_pos (by decide) _
  omega

private theorem trial_sum (l : List ℕ) (m k : ℕ) (hk : k ≤ l.length) :
    (nextRow l m).getD k 0 = m+(l.take k).sum := by
  have fold (v : List ℕ) (u : ℕ) : v.foldl (·+·) u = u+v.sum := by
    induction v generalizing u with
    | nil => simp
    | cons e v ih => simp [ih,Nat.add_assoc]
  simp [nextRow,List.getD_eq_getElem?_getD,hk,fold]

/-- At arbitrarily late stages every penultimate trial entry exceeds the whole old table. -/
theorem penultimate_clear (N : ℕ) : ∃ n ≥ N, ∀ m s j : ℕ, s ≤ n → j ≤ s →
    (state s).2.getD j 0 < (nextRow (state n).2 m).getD n 0 := by
  obtain ⟨n,hn,hfast⟩ := large_doubling N
  refine ⟨n,hn,?_⟩
  intro m s j hs hj
  have maxold := old_entry_le hs hj (le_refl n) (by omega)
  have last (d : ℕ) : (state d).2.getD d 0 = a d := by
    have e := diff_entry 0 d
    simpa [diff] using e.symm
  rw [last] at maxold
  have add := row_add (n:=n) (i:=n) (le_refl n)
  rw [last,last] at add
  rw [row_from_start, trial_sum _ _ _ (by rw [row_length]; omega)] at add
  rw [trial_sum _ _ _ (by rw [row_length]; omega)]
  have small := start_bound (n+1)
  change ((state (n+1)).2.headD 0) ≤ (n+3)^3 at small
  omega

end Zorach

namespace Zorach
open OMA.S_oeis_a035313

/-- When a positive unused trial is smaller than the greedy choice, a strictly
interior column must collide with an old entry. Neither endpoint can block it. -/
theorem interior_conflict (n m : ℕ) (hm : 0 < m) (miss : m ∉ (state n).1)
    (small : m < ((state (n+1)).2.headD 0)) : ∃ k, 0 < k ∧ k ≤ n ∧
      (nextRow (state n).2 m).getD k 0 ∈ (state n).1 := by
  obtain ⟨x,hnew,hold⟩ := exists_conflict n m hm small
  obtain ⟨k,hk,ex⟩ := List.mem_iff_getElem.mp hnew
  have hk' : k ≤ n+1 := by simpa [nextRow,row_length] using hk
  have dx : (nextRow (state n).2 m).getD k 0 = x := by
    rw [List.getD_eq_getElem?_getD,getElem?_pos (nextRow (state n).2 m) k hk,Option.getD_some,ex]
  have hpos : 0 < k := by
    by_contra e
    have eq : k = 0 := by omega
    rw [eq] at dx
    have hhead (l : List ℕ) : (nextRow l m).getD 0 0 = m := by
      simp [nextRow,List.getD_eq_getElem?_getD]
    rw [hhead] at dx
    exact miss (dx ▸ hold)
  obtain ⟨s,hs,hrow⟩ := used_to_row_le hold
  obtain ⟨j,hj,ey⟩ := List.mem_iff_getElem.mp hrow
  have hj' : j ≤ s := by simpa [row_length] using hj
  have old : (state s).2.getD j 0 = x := by
    rw [List.getD_eq_getElem?_getD,getElem?_pos (state s).2 j hj,Option.getD_some,ey]
  have narrow := collision_cone hm hs hj' hpos hk' (dx.trans old.symm)
  exact ⟨k,hpos,by omega,dx ▸ hold⟩
end Zorach

namespace Zorach

/-- The eighth moment of the signed endpoint of a binomial walk, translated by x. -/
theorem moment8_translate (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * (x + n - 2*k)^8) =
      2^n * (x^8 + 28*n*x^6 + 70*(3*(n:ℝ)^2-2*n)*x^4 +
        28*(15*(n:ℝ)^3-30*(n:ℝ)^2+16*n)*x^2 +
        105*(n:ℝ)^4 - 420*(n:ℝ)^3 + 588*(n:ℝ)^2 - 272*n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have split := Finset.sum_choose_succ_mul (fun (k _ : ℕ) => (x+(n+1:ℕ)-2*k)^8) n
    change (∑ k ∈ Finset.range (n+2), ((n+1).choose k : ℝ) * (x+(n+1:ℕ)-2*k)^8) = _
    rw [split]
    have plus (k : ℕ) : x+(n+1:ℕ)-2*k = (x+1)+n-2*k := by push_cast; ring
    have minus (k : ℕ) : x+(n+1:ℕ)-2*(k+1:ℕ) = (x-1)+n-2*k := by push_cast; ring
    simp_rw [minus, plus]
    rw [ih (x+1), ih (x-1), pow_succ (2:ℝ)]
    push_cast
    ring

theorem moment8 (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * ((n:ℝ)-2*k)^8) ≤
      10000*((n:ℝ)+1)^4*2^n := by
  have he := moment8_translate n 0
  simp at he
  rw [he, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hn : (0:ℝ) ≤ n := by positivity
  nlinarith [sq_nonneg (n:ℝ), pow_nonneg hn 3, pow_nonneg hn 4]

end Zorach

namespace Zorach
open Finset Filter Topology

section
variable (total : (ℕ → ℕ) → ℕ → ℝ)
variable (total_eq : ∀ (b : ℕ → ℕ) (n : ℕ), total b n =
  ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*b k)
include total_eq

theorem total_lower (b : ℕ → ℕ) (h : ∀ k, 0 < b k) (n : ℕ) :
    (2:ℝ)^n ≤ total b n := by
  have e : ∑ k ∈ range (n+1), (n.choose k : ℝ) = 2^n := by exact_mod_cast Nat.sum_range_choose n
  rw [←e,total_eq]
  apply sum_le_sum
  intro k _
  have hb : (1:ℝ) ≤ b k := by exact_mod_cast h k
  nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) (n.choose k)) (sub_nonneg.mpr hb)]

/-- The change in the binomial transform is the first centered moment of the tilted weights. -/
private theorem centered (b : ℕ → ℕ) (n : ℕ) :
    (∑ k ∈ range (n+2), ((n+1).choose k : ℝ) * b k * ((n+1:ℝ)-2*k)) =
      (n+1:ℝ) * (2*total b n - total b (n+1)) := by
  have scaled : (∑ k ∈ range (n+2), ((n+1).choose k:ℝ) * b k * ((n+1:ℝ)-k)) =
      (n+1:ℝ) * total b n := by
    calc
      _ = ∑ k ∈ range (n+2), (n+1:ℝ)*((n.choose k:ℝ) * b k) := by
        apply sum_congr rfl
        intro k hk
        have hk' : k ≤ n+1 := by have := mem_range.mp hk; omega
        have h := congrArg (fun a : ℕ => (a:ℝ)) (Nat.choose_mul_succ_eq n k)
        push_cast [Nat.cast_sub hk'] at h
        linear_combination -(b k : ℝ)*h
      _ = _ := by rw [sum_range_succ]; simp [total_eq,mul_sum]
  calc
    _ = 2 * (∑ k ∈ range (n+2), ((n+1).choose k:ℝ) * b k * ((n+1:ℝ)-k)) -
        (n+1:ℝ)*total b (n+1) := by
      simp only [total_eq,mul_sum,←sum_sub_distrib]
      apply sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [scaled]; ring

theorem concentration (b : ℕ → ℕ) (lo : ∀ k, 0 < b k)
    (hi : ∀ k, b k ≤ (k+2)^3)
    (moment : ∀ N : ℕ, (∑ k ∈ range (N+1), (N.choose k:ℝ)*((N:ℝ)-2*k)^8) ≤
      10000*((N:ℝ)+1)^4 * 2^N) (n : ℕ) :
    (2*total b n/total b (n+1)-1)^8 ≤ 4320000/(n+1:ℝ) := by
  let N := n+1
  let T := total b N
  have hN : (1:ℝ) ≤ N := by exact_mod_cast (show 1≤N by dsimp [N]; omega)
  have hNp : (0:ℝ) < N := by linarith
  have low := total_lower total total_eq b lo N
  have hT : 0<T := lt_of_lt_of_le (by positivity : (0:ℝ)<2^N) low
  let w (k : ℕ) : ℝ := (N.choose k:ℝ)*b k/T
  let z (k : ℕ) : ℝ := (N:ℝ)-2*k
  have hw (k : ℕ) : 0 ≤ w k := by dsimp [w]; positivity
  have wsum : ∑ k ∈ range (N+1), w k = 1 := by
    simp only [w,←sum_div,←total_eq]; exact div_self hT.ne'
  have j := Real.pow_arith_mean_le_arith_mean_pow_of_even (range (N+1)) w z
    (fun k _ => hw k) wsum (show Even 8 by decide)
  have mean : ∑ k ∈ range (N+1), w k*z k = (N:ℝ)*(2*total b n/T-1) := by
    calc
      _ = (∑ k ∈ range (N+1), (N.choose k:ℝ)*b k*z k)/T := by
        rw [sum_div]; apply sum_congr rfl; intro k _; dsimp [w]; ring
      _ = _ := by
        dsimp only [z,N]
        push_cast
        rw [centered total total_eq]
        change ((n:ℝ)+1)*(2*total b n-T)/T = ((n:ℝ)+1)*(2*total b n/T-1)
        field_simp [hT.ne']
  rw [mean,mul_pow] at j
  have upper : ∑ k ∈ range (N+1), w k*z k^8 ≤
      ((N:ℝ)+2)^3 * (10000*((N:ℝ)+1)^4*2^N) / T := by
    calc
      _ ≤ ∑ k ∈ range (N+1), (((N:ℝ)+2)^3/T)*((N.choose k:ℝ)*z k^8) := by
        apply sum_le_sum
        intro k hk
        have hk' : (k:ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)
        have hb : (b k:ℝ) ≤ ((N:ℝ)+2)^3 := by
          calc
            _ ≤ ((k:ℝ)+2)^3 := by exact_mod_cast hi k
            _ ≤ _ := by gcongr
        dsimp [w]
        calc
          _ = ((b k:ℝ)/T) * ((N.choose k:ℝ)*z k^8) := by ring
          _ ≤ _ := by gcongr
      _ ≤ _ := by
        rw [←mul_sum]
        calc
          _ ≤ (((N:ℝ)+2)^3/T)*(10000*((N:ℝ)+1)^4*2^N) :=
            mul_le_mul_of_nonneg_left (moment N) (by positivity)
          _ = _ := by ring
  have a1 : ((N:ℝ)+2)^3 ≤ (3*(N:ℝ))^3 := by gcongr; linarith
  have a2 : ((N:ℝ)+1)^4 ≤ (2*(N:ℝ))^4 := by gcongr; linarith
  have simple : ((N:ℝ)+2)^3*(10000*((N:ℝ)+1)^4*2^N)/T ≤ 4320000*(N:ℝ)^7 := by
    apply (div_le_iff₀ hT).mpr
    calc
      _ ≤ (3*(N:ℝ))^3 * (10000*(2*(N:ℝ))^4*T) := by gcongr
      _ = _ := by ring
  have h := (j.trans upper).trans simple
  have hn0 : (N:ℝ)^8 > 0 := by positivity
  have g : (2*total b n/T-1)^8 ≤ (4320000*(N:ℝ)^7)/(N:ℝ)^8 :=
    (le_div_iff₀ hn0).mpr (by linarith only [h])
  convert g using 1
  dsimp [N]
  push_cast
  field_simp

end
end Zorach

namespace Zorach
open Filter Topology

section
variable (total : (ℕ → ℕ) → ℕ → ℝ)
variable (total_eq : ∀ (b : ℕ → ℕ) (n : ℕ), total b n =
  ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*b k)
include total_eq

/-- Binomial smoothing gives the ratio 2 for every positive, cubically bounded input. -/
theorem transform_limit (b : ℕ → ℕ) (lo : ∀ k, 0 < b k) (hi : ∀ k, b k ≤ (k+2)^3) :
    Tendsto (fun n => total b (n+1) / total b n) atTop (𝓝 2) := by
  have first : Tendsto (fun n => 2*total b n/total b (n+1)) atTop (𝓝 1) := by
    apply Metric.tendsto_atTop.mpr
    intro ε he
    obtain ⟨N,hN⟩ := exists_nat_gt (4320000/ε^8)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply lt_of_pow_lt_pow_left₀ 8 he.le
    rw [(show Even 8 by decide).pow_abs]
    apply lt_of_le_of_lt (concentration total total_eq b lo hi moment8 n)
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < n+1)).mpr
    have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
    have h1 := (div_lt_iff₀ (pow_pos he 8)).mp hN
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (pow_nonneg he.le 8),pow_pos he 8]
  have last := (tendsto_const_nhds (x := (2:ℝ)) (f := (atTop : Filter ℕ))).div first (by norm_num)
  convert last using 1
  · funext n
    have hp (k : ℕ) : 0 < total b k :=
      lt_of_lt_of_le (by positivity : (0:ℝ)<2^k) (total_lower total total_eq b lo k)
    change total b (n+1)/total b n = 2/(2*total b n/total b (n+1))
    field_simp [(hp n).ne',(hp (n+1)).ne']
  · norm_num

end
end Zorach

namespace Zorach
open OMA.S_oeis_a035313 Filter Topology

/-- Wilson's ratio conjecture for the diagonal of the greedy Zorach triangle. -/
theorem ratio : Tendsto (fun n => (a (n+1):ℝ)/a n) atTop (𝓝 2) := by
  let b (k : ℕ) := (state k).2.headD 0
  let A (f : ℕ → ℕ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*f k
  have eq (n : ℕ) : (a n:ℝ) = A b n := by dsimp [A,b]; exact_mod_cast diagonal n
  simpa only [eq] using transform_limit A (fun _ _ => rfl) b start_pos start_bound

end Zorach

namespace OMA.R_oeis_a035313_R1
open OMA.S_oeis_a035313 Zorach Filter

/-- For a fixed column cutoff, collisions in those columns eventually cease
to prevent an unused positive trial from becoming a row start. -/
def H1 : Prop := ∀ m : ℕ, 0 < m → ∀ B : ℕ, ∃ N : ℕ, ∀ n ≥ N,
  m ∈ (state n).1 ∨ ∀ k : ℕ, 0 < k → k ≤ B → k ≤ n →
    (nextRow (state n).2 m).getD k 0 ∉ (state n).1

/-- For each positive trial, there is a cutoff beyond which the columns
are simultaneously free of collisions at arbitrarily late stages, up to
the time the trial is represented in the triangle. -/
def H2 : Prop := ∀ m : ℕ, 0 < m → ∃ B : ℕ, ∀ N : ℕ, ∃ n ≥ N,
  m ∈ (state n).1 ∨ ∀ k : ℕ, B < k → k ≤ n →
    (nextRow (state n).2 m).getD k 0 ∉ (state n).1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a035313.main := by
  intro near far
  refine ⟨?_,ratio⟩
  intro m hm
  suffices ∃ n : ℕ, m∈(state n).1 by
    obtain ⟨n,h⟩ := this
    obtain ⟨t,ht⟩ := used_to_row h
    exact difference_of_mem ht
  by_contra! miss
  obtain ⟨B,hB⟩ := far m hm
  obtain ⟨N,hN⟩ := near m hm B
  obtain ⟨L,hL⟩ := eventually_atTop.mp (big_starts m)
  obtain ⟨n,hn,outside⟩ := hB (max N L)
  obtain ⟨k,hk,hkn,hconf⟩ := interior_conflict n m hm (miss n) (hL n (by omega))
  by_cases e : k ≤ B
  · exact (hN n (by omega)).resolve_left (miss n) k hk e hkn hconf
  · exact outside.resolve_left (miss n) k (by omega) hkn hconf

end OMA.R_oeis_a035313_R1
