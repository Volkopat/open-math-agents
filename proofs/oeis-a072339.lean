import OMAStatements.S_oeis_a072339

-- A representation with leading exponent h has value v with 2^h ≤ 2v ≤ 2^(h+1). So every
-- representation of 2^k + i (0 < i < 2^k) starts with k + 1, and its tail represents 2^k - i;
-- conversely k + 1 can be prepended to any representation of 2^k - i.

namespace OMA.A072339
open OMA.S_oeis_a072339

def v (l : List ℕ) : ℤ := (l.map (fun k => (2 : ℤ) ^ k)).alternatingSum

lemma v_cons (h : ℕ) (l : List ℕ) : v (h :: l) = 2 ^ h - v l := by
  simp [v, List.alternatingSum_cons]

lemma bounds : ∀ (l : List ℕ) (h : ℕ), (h :: l).Pairwise (· > ·) →
    (2 : ℤ) ^ h ≤ 2 * v (h :: l) ∧ v (h :: l) ≤ 2 ^ h := by
  intro l
  induction l with
  | nil => intro h _; simp [v]
  | cons h2 t ih =>
    intro h hp
    have h21 : h2 < h := (List.pairwise_cons.mp hp).1 h2 (by simp)
    obtain ⟨i1, i2⟩ := ih h2 (List.pairwise_cons.mp hp).2
    rw [v_cons h (h2 :: t)]
    have : (2 : ℤ) ^ h = 2 * 2 ^ (h - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : (2 : ℤ) ^ h2 ≤ 2 ^ (h - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    constructor <;> nlinarith [pow_pos (by norm_num : (0:ℤ) < 2) h2]

lemma le_head (l : List ℕ) (h : ℕ) (hp : (h :: l).Pairwise (· > ·)) : ∀ x ∈ l, x < h :=
  fun x hx => (List.pairwise_cons.mp hp).1 x hx

lemma exists_rep : ∀ n : ℕ, ∃ l, IsRep n l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨[], by simp [IsRep]⟩
    have hex : ∃ k, n ≤ 2 ^ k := ⟨n, (Nat.lt_two_pow_self).le⟩
    set k := Nat.find hex with hk
    have hk1 : n ≤ 2 ^ k := Nat.find_spec hex
    have hk2 : 2 ^ k < 2 * n := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0] at hk1 ⊢; simp at hk1 ⊢; omega
      · have := Nat.find_min hex (show k - 1 < k by omega)
        have e : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
        omega
    obtain ⟨l, hl1, hl2⟩ := ih (2 ^ k - n) (by omega)
    refine ⟨k :: l, ?_, ?_⟩
    · refine List.pairwise_cons.mpr ⟨?_, hl1⟩
      cases l with
      | nil => simp
      | cons h t =>
        have hb := (bounds t h hl1).1
        have hv : v (h :: t) = ((2 ^ k - n : ℕ) : ℤ) := hl2
        rw [hv] at hb
        have hlt : h < k := by
          by_contra hc
          have : (2 : ℤ) ^ k ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) (by omega)
          push_cast [Nat.cast_sub hk1] at hb
          have : ((2 ^ k : ℕ) : ℤ) < 2 * n := by exact_mod_cast hk2
          push_cast at this
          linarith
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlt
        · exact lt_trans (le_head t h hl1 x hx) hlt
    · have : v (k :: l) = 2 ^ k - v l := v_cons k l
      change v (k :: l) = n
      rw [this, show v l = ((2 ^ k - n : ℕ) : ℤ) from hl2, Nat.cast_sub hk1]
      push_cast; ring

lemma nonempty (n : ℕ) : {m : ℕ | ∃ l : List ℕ, IsRep n l ∧ l.length = m}.Nonempty := by
  obtain ⟨l, hl⟩ := exists_rep n
  exact ⟨_, l, hl, rfl⟩

lemma a_le (n : ℕ) (l : List ℕ) (hl : IsRep n l) : a n ≤ l.length := Nat.sInf_le ⟨l, hl, rfl⟩

lemma a_spec (n : ℕ) : ∃ l, IsRep n l ∧ l.length = a n := Nat.sInf_mem (nonempty n)

lemma pos_rep (n : ℕ) (hn : 0 < n) (l : List ℕ) (hl : IsRep n l) :
    ∃ h t, l = h :: t ∧ 2 ^ h ≤ 2 * (n : ℤ) ∧ (n : ℤ) ≤ 2 ^ h := by
  cases l with
  | nil => exfalso; have := hl.2; simp at this; omega
  | cons h t =>
    have hb := bounds t h hl.1
    have hv : v (h :: t) = n := hl.2
    rw [hv] at hb
    exact ⟨h, t, rfl, hb⟩

end OMA.A072339

open OMA.A072339 OMA.S_oeis_a072339 in
theorem OMA.solution : type_of% @OMA.S_oeis_a072339.main := by
  constructor
  · intro k
    apply le_antisymm
    · exact a_le _ [k] ⟨by simp, by simp⟩
    · obtain ⟨l, hl, hlen⟩ := a_spec (2 ^ k)
      obtain ⟨h, t, rfl, _⟩ := pos_rep _ (by positivity) l hl
      rw [← hlen]; simp
  · intro k i hi hik
    have hm : 0 < 2 ^ k - i := by omega
    apply le_antisymm
    · obtain ⟨l, hl, hlen⟩ := a_spec (2 ^ k - i)
      obtain ⟨h, t, rfl, hb1, _⟩ := pos_rep _ hm _ hl
      have hhk : h < k + 1 := by
        by_contra hc
        have : (2 : ℤ) ^ (k + 1) ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) (by omega)
        push_cast [Nat.cast_sub hik.le] at hb1
        rw [pow_succ] at this
        linarith
      have hrep : IsRep (2 ^ k + i) ((k + 1) :: h :: t) := by
        refine ⟨List.pairwise_cons.mpr ⟨?_, hl.1⟩, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hhk
          · exact lt_trans (le_head t h hl.1 x hx) hhk
        · change v ((k + 1) :: h :: t) = _
          rw [v_cons, show v (h :: t) = ((2 ^ k - i : ℕ) : ℤ) from hl.2, Nat.cast_sub hik.le]
          push_cast; ring
      have := a_le _ _ hrep
      rw [← hlen]; simpa using this
    · obtain ⟨L, hL, hlen⟩ := a_spec (2 ^ k + i)
      obtain ⟨H, t, rfl, hb1, hb2⟩ := pos_rep _ (by positivity) _ hL
      have hH : H = k + 1 := by
        push_cast at hb1 hb2
        have hik' : ((i : ℕ) : ℤ) < 2 ^ k := by exact_mod_cast hik
        have hi' : (0 : ℤ) < i := by exact_mod_cast hi
        rcases lt_trichotomy H (k + 1) with h1 | h1 | h1
        · have : (2 : ℤ) ^ H ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
          linarith
        · exact h1
        · have : (2 : ℤ) ^ (k + 2) ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) (by omega)
          rw [pow_succ, pow_succ] at this
          linarith
      subst hH
      have hrep : IsRep (2 ^ k - i) t := by
        refine ⟨(List.pairwise_cons.mp hL.1).2, ?_⟩
        have h2 : v ((k + 1) :: t) = ((2 ^ k + i : ℕ) : ℤ) := hL.2
        rw [v_cons] at h2
        change v t = _
        rw [Nat.cast_sub hik.le]
        push_cast at h2 ⊢
        rw [pow_succ] at h2
        linarith
      have := a_le _ _ hrep
      rw [← hlen]; simp; omega

