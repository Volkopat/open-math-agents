import OMAStatements.S_oeis_a362946
import Mathlib

/-! Robert C. Lyons' conjecture for OEIS A362946. With exponents one or two,
raising the ith exponent adds i(i−1), twice a triangular number. Their
subset sums eventually cover a growing interval of each available parity. -/

namespace OMA.S_oeis_a362946

private def tri : ℕ → ℕ
  | 0 => 0
  | k+1 => tri k+k+1

private lemma twice_tri (k : ℕ) : 2*tri k = k*(k+1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tri]; nlinarith

private def sums : ℕ → Finset ℕ
  | 0 => {0}
  | k+1 => (sums k).image (fun x => x+(k+1)) ∪ (sums k).image (fun x => x+(k+1)^2)

private lemma realize {k n : ℕ} (h : n ∈ sums k) :
    ∃ e : ℕ → ℕ, (∀ i, 1 ≤ e i) ∧ n = ∑ i ∈ Finset.Icc 1 k, i^(e i) := by
  induction k generalizing n with
  | zero =>
    refine ⟨fun _ => 1, by simp, ?_⟩
    simpa [sums] using h
  | succ k ih =>
    have adjoin (m : ℕ) (hm : m ∈ sums k) (t : ℕ) (ht : 1 ≤ t) :
        ∃ e : ℕ → ℕ, (∀ i, 1 ≤ e i) ∧ m+(k+1)^t = ∑ i ∈ Finset.Icc 1 (k+1), i^(e i) := by
      obtain ⟨e,he,rfl⟩ := ih hm
      refine ⟨Function.update e (k+1) t, fun i => ?_, ?_⟩
      · by_cases hx : i=k+1 <;> simp [hx, ht, he]
      · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1), Function.update_self]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (by have := (Finset.mem_Icc.mp hi).2; omega : i ≠ k+1)]
    rcases Finset.mem_union.mp h with h | h <;> obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp h
    · simpa using adjoin m hm 1 (by decide)
    · exact adjoin m hm 2 (by decide)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private lemma interval (k : ℕ) (hk : 9 ≤ k) (j : ℕ) (hj : j ≤ tri k) :
    tri k+68+2*j ∈ sums k := by
  induction k, hk using Nat.le_induction generalizing j with
  | base =>
    have cert : ∀ i : Fin 46, tri 9+68+2*i.val ∈ sums 9 := by decide
    exact cert ⟨j,by change j ≤ 45 at hj; omega⟩
  | succ k hk ih =>
    have hle : k+1 ≤ tri k := by
      have := Nat.mul_le_mul_right (k+1) (show 2≤k by omega)
      have := twice_tri k
      omega
    by_cases hjk : j ≤ tri k
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨_,ih j hjk, by simp [tri]; omega⟩
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨_, ih (j-tri k) (by simp only [tri] at hj; omega), ?_⟩
      have hsub : j-tri k+tri k=j := by omega
      have htri := twice_tri k
      simp only [tri]
      nlinarith

private lemma large (n : ℕ) (hn : 134 ≤ n) : IsExpressible n := by
  have available (k : ℕ) (hk : 9 ≤ k) (hlo : tri k+68 ≤ n) (hhi : n ≤ 3*tri k+68)
      (hpar : n%2 = tri k%2) : IsExpressible n := by
    let j := (n-(tri k+68))/2
    have hj : j≤tri k := by dsimp [j]; omega
    have he : n = tri k+68+2*j := by dsimp [j]; omega
    exact ⟨k,by omega,realize (he ▸ interval k hk j hj)⟩
  have cover (k : ℕ) (hk : 9 ≤ k) (hb : n ≤ tri (k+2)+68) : IsExpressible n := by
    induction k, hk using Nat.le_induction with
    | base =>
      change n ≤ 134 at hb
      have he : n = 134 := by omega
      subst n
      exact available 11 (by decide) (by decide) (by decide) (by decide)
    | succ k hk ih =>
      by_cases hold : n ≤ tri (k+2)+68
      · exact ih hold
      have hbig : n ≤ 3*tri k+68 := by
        have hmul := Nat.mul_le_mul_right (k+1) (show 4≤k by omega)
        have htri := twice_tri k
        simp only [tri] at hb
        omega
      by_cases hp : n%2=tri k%2
      · exact available k hk (by simp only [tri] at hold; omega) hbig hp
      · apply available (k+2) (by omega) (by omega)
        · simp only [tri]; omega
        · simp only [tri]; omega
  apply cover (n+9) (by omega)
  have hge (l : ℕ) : l≤tri l := by cases l <;> simp [tri]
  have := hge (n+9+2)
  omega

end OMA.S_oeis_a362946

theorem OMA.solution : type_of% @OMA.S_oeis_a362946.main := by
  apply (Set.finite_lt_nat 134).subset
  intro n hn
  change n < 134
  by_contra! h
  exact hn.2 (OMA.S_oeis_a362946.large n h)
