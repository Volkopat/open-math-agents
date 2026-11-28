import OMAStatements.S_oeis_a157792
import Mathlib

/-!
# Visibility from the bottom edge

The lower bound uses the point (1,3) to locate an observer outside the
middle residue class modulo three. It then chooses mutually separated
bottom-edge targets all missed by that observer. For the upper bound,
two balanced arithmetic progressions of observers cover the lattice.
-/

namespace A157792Proof
open OMA.S_oeis_a157792

private theorem ground {s x : ℤ} (h : Visible s x 0) : x-1 ≤ s ∧ s ≤ x+1 := by
  rcases h with ⟨he,_⟩ | hc
  · omega
  · simp at hc
    omega

private theorem lower {n : ℕ} (hn : 4 ≤ n) {S : Finset ℤ} (hc : Covers n S) :
    n/3+1 ≤ S.card := by
  classical
  obtain ⟨s, hs, hv⟩ := hc ⟨1, by omega⟩ ⟨3, by omega⟩
  have hr : s % 3 ≠ 1 := by
    intro he
    have hd : (3 : ℤ) ∣ s-1 := ⟨s/3, by omega⟩
    have dvd := Int.dvd_coe_gcd hd (dvd_refl (3 : ℤ))
    rcases hv with hm | h
    · norm_num at hm
    · change Int.gcd (s-1) 3 = 1 at h
      rw [h] at dvd
      norm_num at dvd
  let t := (s+1)/3
  let target (i : ℕ) : ℕ := 3*i + (if (i:ℤ)<t then 0 else 2)
  have ht (i : Fin (n/3)) : target i < n := by
    have := i.isLt
    dsimp [target]
    split <;> omega
  choose obs inside sees using fun i : Fin (n/3) => hc ⟨target i, ht i⟩ ⟨0, by omega⟩
  have near (i : Fin (n/3)) : (target i : ℤ)-1 ≤ obs i ∧ obs i ≤ (target i : ℤ)+1 :=
    ground (sees i)
  have inj : Function.Injective obs := by
    intro i j he
    apply Fin.ext
    have hi := near i
    have hj := near j
    dsimp [target] at hi hj
    split at hi <;> split at hj <;> push_cast at hi hj <;> omega
  have miss (i : Fin (n/3)) : obs i ≠ s := by
    have hi := near i
    dsimp [target,t] at hi
    split at hi <;> push_cast at hi <;> omega
  have bound : (Finset.univ.image obs).card ≤ (S.erase s).card := by
    apply Finset.card_le_card
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_erase.mpr ⟨miss i, inside i⟩
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin,
    Finset.card_erase_of_mem hs] at bound
  have := Finset.card_pos.mpr (show S.Nonempty from ⟨s, hs⟩)
  omega

/-- An integer relatively prime to a modulus remains so after changing
its representative by a multiple of that modulus. -/
private theorem transfer {a b q : ℤ} (h : IsCoprime b q) (hd : q ∣ a-b) :
    IsCoprime a q := by
  obtain ⟨k,hk⟩ := hd
  rw [show a = b + q*k by omega]
  exact h.add_mul_left_left k

private theorem cop_three {a : ℤ} (ha : a % 3 ≠ 0) : IsCoprime a 3 := by
  by_cases h : a % 3 = 1
  · exact ⟨1,-(a/3), by omega⟩
  · exact ⟨-1,a/3+1, by omega⟩

private theorem cop_four {a : ℤ} (ha : a % 2 = 1) : IsCoprime a 4 := by
  by_cases h : a % 4 = 1
  · exact ⟨1,-(a/4), by omega⟩
  · exact ⟨-1,a/4+1, by omega⟩

/-- The units 1, d, q-d, q-1 have cyclic gaps at most L.
The sole exceptional small modulus 6 is excluded by the hypothesis. -/
private theorem near_middle {q L : ℤ} (hq : 2 ≤ q) (h3 : q % 3 ≠ 0)
    (hL : 2 ≤ L) (bound : q ≤ 2*L) :
    ∃ d : ℤ, 1 ≤ d ∧ 2*d ≤ q ∧ q-2*d ≤ L ∧ IsCoprime d q := by
  by_cases odd : q % 2 = 1
  · refine ⟨q/2, by omega, by omega, by omega, -2, 1, by omega⟩
  by_cases small : q = 2
  · subst q
    exact ⟨1, by decide, by decide, by omega, by simp⟩
  by_cases four : q % 4 = 0
  · let d := q/2-1
    have hh : IsCoprime d 2 := ⟨1,-(d/2), by dsimp [d]; omega⟩
    have eq : q = 2 + 2*d := by dsimp [d]; omega
    refine ⟨d, ?_, ?_, ?_, ?_⟩
    · dsimp [d]; omega
    · dsimp [d]; omega
    · dsimp [d]; omega
    · rw [eq]; exact hh.add_mul_right_right 2
  · let d := q/2-2
    have hh : IsCoprime d 4 := cop_four (by dsimp [d]; omega)
    have eq : q = 4 + 2*d := by dsimp [d]; omega
    refine ⟨d, ?_, ?_, ?_, ?_⟩
    · dsimp [d]; omega
    · dsimp [d]; omega
    · dsimp [d]; omega
    · rw [eq]; exact hh.add_mul_right_right 2

private theorem interval_unit (a : ℤ) {q L : ℤ} (hq : 0 < q) (h3 : q % 3 ≠ 0)
    (hL : 2 ≤ L) (bound : q ≤ 2*L) :
    ∃ j : ℤ, 0 ≤ j ∧ j < L ∧ IsCoprime (a+j) q := by
  by_cases one : q = 1
  · exact ⟨0, le_rfl, by omega, by subst q; exact ⟨0,1,by ring⟩⟩
  obtain ⟨d, hd, hdq, gap, unit⟩ := near_middle (by omega) h3 hL bound
  let r := a % q
  have hr : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hq' : r < q := Int.emod_lt_of_pos _ hq
  have negUnit : IsCoprime (q-d) q := by
    exact transfer unit.neg_left ⟨1, by ring⟩
  have last : IsCoprime (q-1) q := ⟨-1,1,by ring⟩
  have pick (u : ℤ) (hu : r ≤ u) (dist : u-r < L) (cop : IsCoprime u q) :
      ∃ j : ℤ, 0 ≤ j ∧ j < L ∧ IsCoprime (a+j) q := by
    refine ⟨u-r, by omega, dist, transfer cop ⟨a/q, ?_⟩⟩
    have eq := Int.emod_add_mul_ediv a q
    dsimp [r]
    omega
  by_cases h1 : r ≤ 1
  · exact pick 1 h1 (by omega) ⟨1,0,by ring⟩
  by_cases h2 : r ≤ d
  · exact pick d h2 (by omega) unit
  by_cases h4 : r ≤ q-d
  · exact pick (q-d) h4 (by omega) negUnit
  exact pick (q-1) (by omega) (by omega) last

/-- Across a run of step three, remove powers of three from the height.
For the remaining modulus the inverse of three changes the run to
consecutive residues. -/
private theorem progression (a : ℤ) (q : ℕ) (hq : 0 < q) (ha : a % 3 ≠ 0)
    (L : ℤ) (hL : 2 ≤ L) (bound : (q:ℤ) ≤ 2*L) :
    ∃ j : ℤ, 0 ≤ j ∧ j < L ∧ IsCoprime (a+3*j) q := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases h3 : q % 3 = 0
    · have eq : q = 3*(q/3) := by omega
      obtain ⟨j,hj,hjL,cop⟩ := ih (q/3) (by omega) (by omega) (by omega)
      refine ⟨j,hj,hjL,?_⟩
      have e : (q:ℤ) = 3*((q/3:ℕ):ℤ) := by exact_mod_cast eq
      rw [e]
      exact (cop_three (by omega)).mul_right cop
    · have hh : (q:ℤ) % 3 ≠ 0 := by omega
      obtain ⟨b,c,hbc⟩ := (cop_three hh).symm
      obtain ⟨j,hj,hjL,cop⟩ := interval_unit (b*a) (by omega : 0 < (q:ℤ)) hh hL bound
      refine ⟨j,hj,hjL,transfer ((cop_three hh).symm.mul_left cop) ⟨c*a,?_⟩⟩
      linear_combination -a*hbc

private def pos (off L i : ℤ) : ℤ := if i < L then off+3*i else off+3*i-1

private theorem visible_one {s x h : ℤ} (hb : s-x = 1 ∨ s-x = -1) : Visible s x h := by
  right
  apply Int.isCoprime_iff_gcd_eq_one.mp
  rcases hb with hb | hb
  · exact ⟨1,0,by rw [hb]; ring⟩
  · exact ⟨-1,0,by rw [hb]; ring⟩

private theorem covers_point {m L off x h : ℤ}
    (hL : 2 ≤ L) (hR : 2 ≤ m+1-L)
    (lo : off-1 ≤ x) (hi : x ≤ off+3*m)
    (height : 0 ≤ h) (leftSize : h/3 ≤ 2*L) (rightSize : h/3 ≤ 2*(m+1-L)) :
    ∃ i : ℤ, 0 ≤ i ∧ i ≤ m ∧ Visible (pos off L i) x h := by
  have near : ∃ i : ℤ, 0 ≤ i ∧ i ≤ m ∧ x-1 ≤ pos off L i ∧ pos off L i ≤ x+1 := by
    by_cases first : x ≤ off+3*L-2
    · let i := (x-off+1)/3
      have hlt : i < L := by dsimp [i]; omega
      refine ⟨i, by dsimp [i]; omega, by omega, ?_, ?_⟩ <;> simp only [pos, if_pos hlt] <;> dsimp [i] <;> omega
    · let i := (x-off+2)/3
      have hge : ¬ i < L := by dsimp [i]; omega
      refine ⟨i, by omega, by dsimp [i]; omega, ?_, ?_⟩ <;> simp only [pos, if_neg hge] <;> dsimp [i] <;> omega
  obtain ⟨i, i0, im, near1, near2⟩ := near
  by_cases center : pos off L i = x
  · by_cases groundRow : h = 0
    · exact ⟨i,i0,im,Or.inl ⟨center,groundRow⟩⟩
    by_cases regular : h % 3 ≠ 0
    · have neighbor : ∃ j : ℤ, 0 ≤ j ∧ j ≤ m ∧
          (pos off L j - pos off L i = 3 ∨ pos off L j - pos off L i = -3) := by
        by_cases li : i < L
        · by_cases z : i = 0
          · refine ⟨i+1,by omega,by omega,Or.inl ?_⟩
            simp [pos, li, show i+1 < L by omega]
            ring
          · refine ⟨i-1,by omega,by omega,Or.inr ?_⟩
            simp [pos, li, show i-1 < L by omega]
            ring
        · by_cases z : i = m
          · refine ⟨i-1,by omega,by omega,Or.inr ?_⟩
            simp [pos, li, show ¬ i-1 < L by omega]
            ring
          · refine ⟨i+1,by omega,by omega,Or.inl ?_⟩
            simp [pos, li, show ¬ i+1 < L by omega]
            ring
      obtain ⟨j,hj0,hjm,dist⟩ := neighbor
      refine ⟨j,hj0,hjm,Or.inr (Int.isCoprime_iff_gcd_eq_one.mp ?_)⟩
      rw [← center]
      rcases dist with d | d <;> rw [d]
      · exact (cop_three regular).symm
      · exact (cop_three regular).symm.neg_left
    · let q := (h/3).toNat
      have qval : (q : ℤ) = h/3 := by dsimp [q]; omega
      have hq : 0 < q := by omega
      have fact : h = 3*(q:ℤ) := by omega
      by_cases first : i < L
      · let a := off+3*L-1-x
        have three : a % 3 ≠ 0 := by simp [pos,first] at center; dsimp [a]; omega
        obtain ⟨j,j0,jl,unit⟩ := progression a q hq three (m+1-L) hR (by omega)
        refine ⟨L+j,by omega,by omega,Or.inr (Int.isCoprime_iff_gcd_eq_one.mp ?_)⟩
        rw [show pos off L (L+j) - x = a+3*j by simp [pos,show ¬ L+j < L by omega,a]; ring, fact]
        exact (cop_three (by omega)).mul_right unit
      · let a := off-x
        have three : a % 3 ≠ 0 := by simp [pos,first] at center; dsimp [a]; omega
        obtain ⟨j,j0,jl,unit⟩ := progression a q hq three L hL (by omega)
        refine ⟨j,j0,by omega,Or.inr (Int.isCoprime_iff_gcd_eq_one.mp ?_)⟩
        rw [show pos off L j - x = a+3*j by simp [pos,jl,a]; ring, fact]
        exact (cop_three (by omega)).mul_right unit
  · exact ⟨i,i0,im,visible_one (by omega)⟩

private theorem mem_edge {n : ℕ} {x : ℤ} : x ∈ edge n ↔ 0 ≤ x ∧ x < n := by
  simp only [edge,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨hx,hn⟩
    exact ⟨x.toNat,by omega,by omega⟩

private theorem construction (n : ℕ) (hn : 9 ≤ n) :
    ∃ S ⊆ edge n, Covers n S ∧ S.card ≤ n/3+1 := by
  let m : ℤ := (n:ℤ)/3
  let L := (m+1)/2
  let off : ℤ := if n % 3 = 2 then 1 else 0
  let S := (Finset.Icc 0 m).image (pos off L)
  have hL : 2 ≤ L := by dsimp [L,m]; omega
  have hR : 2 ≤ m+1-L := by dsimp [L,m]; omega
  refine ⟨S, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨i0,im⟩ := Finset.mem_Icc.mp hi
    apply mem_edge.mpr
    dsimp [pos,off,L,m] at *
    split <;> split <;> omega
  · intro x h
    have xx := x.isLt
    have hh := h.isLt
    obtain ⟨i,i0,im,vis⟩ := covers_point (m := m) (L := L) (off := off) (x := (x.val:ℤ)) (h := (h.val:ℤ)) hL hR
      (by dsimp [off]; split <;> omega) (by dsimp [off,m]; split <;> omega)
      (by omega) (by dsimp [L,m]; omega) (by dsimp [L,m]; omega)
    exact ⟨pos off L i,Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨i0,im⟩),vis⟩
  · apply Finset.card_image_le.trans
    rw [Int.card_Icc]
    dsimp [m]
    omega

private theorem exact_count (n : ℕ) (hn : 9 ≤ n) : a n = n/3+1 := by
  obtain ⟨S,sub,cov,small⟩ := construction n hn
  have mem : S.card ∈ sizes n := Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr sub,cov⟩))
  apply Nat.le_antisymm ((Finset.min'_le _ _ mem).trans small)
  change n/3+1 ≤ a n
  have h := (sizes n).min'_mem ⟨n+1,Finset.mem_insert_self ..⟩
  change a n ∈ sizes n at h
  rcases Finset.mem_insert.mp h with eq | h
  · omega
  · obtain ⟨T,hT,eq⟩ := Finset.mem_image.mp h
    exact eq ▸ lower (by omega : 4 ≤ n) (Finset.mem_filter.mp hT).2

private theorem recurrence (n : ℕ) (hn : 13 ≤ n) :
    (a n : ℤ) = a (n-1) + a (n-3) - a (n-4) := by
  rw [exact_count n (by omega),exact_count (n-1) (by omega),exact_count (n-3) (by omega),
    exact_count (n-4) (by omega)]
  omega

-- Direct finite checks cover all the exceptional side lengths.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem small : ∀ i : Fin 9, a i.val = (i.val+1)/2 := by decide

private theorem all_counts (n : ℕ) : a n = if n < 9 then (n+1)/2 else n/3+1 := by
  split
  · rename_i h
    exact small ⟨n,h⟩
  · exact exact_count n (by omega)

open PowerSeries

private theorem generating :
    (X^4 - X^3 - X + 1) * PowerSeries.mk (fun n => (a n : ℤ)) = PowerSeries.mk numerator := by
  ext n
  have h1 (p : PowerSeries ℤ) : coeff n (X*p) =
      if 1 ≤ n then coeff (n-1) p else 0 := by
    simpa only [pow_one] using coeff_X_pow_mul' p 1 n
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, coeff_X_pow_mul', h1, coeff_mk]
  by_cases hn : n < 13
  · simp only [all_counts]
    interval_cases n <;> decide
  · have h := recurrence n (by omega)
    obtain ⟨t,ht⟩ : ∃ t : ℕ, n = t+13 := ⟨n-13,by omega⟩
    have nz : numerator n = 0 := by rw [ht]; rfl
    rw [nz, if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    omega

end A157792Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a157792.main := by
  exact ⟨A157792Proof.exact_count,A157792Proof.recurrence,A157792Proof.generating⟩
