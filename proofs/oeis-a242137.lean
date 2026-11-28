import OMAStatements.S_oeis_a242137

/-! The gap conjecture of Alex Ratushnyak (OEIS A242137). -/

namespace TriangularGeometry

open OMA.S_oeis_a242137

def tri (m : ℕ) : ℕ := m * (m+1) / 2

theorem twice_tri (m : ℕ) : 2 * tri m = m * (m+1) :=
  Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one m)

theorem tri_mono : Monotone tri := by
  intro a b h
  dsimp [tri]
  gcongr

theorem triangular_bracket (N : ℕ) : ∃ m, tri m ≤ N^2 ∧ N^2 < tri (m+1) := by
  have ex : ∃ j, N^2 < tri j := by
    refine ⟨2*(N+1), ?_⟩
    nlinarith only [twice_tri (2*(N+1))]
  have hu := Nat.find_spec ex
  cases he : Nat.find ex with
  | zero => rw [he] at hu; simp [tri] at hu
  | succ m =>
    refine ⟨m, le_of_not_gt (Nat.find_min ex (show m < Nat.find ex by omega)), ?_⟩
    simpa only [he] using hu

theorem member_of_bracket (N k : ℕ) (hl : tri k ≤ N^2) (hu : N^2+N ≤ tri (k+1)) : P N := by
  intro j hj
  change N^2 < tri j ∧ tri j < N^2+N at hj
  by_cases h : j ≤ k
  · exact (not_lt_of_ge ((tri_mono h).trans hl)) hj.1
  · exact (not_lt_of_ge (hu.trans (tri_mono (show k+1 ≤ j by omega)))) hj.2

theorem large (N : ℕ) (hN : 200 ≤ N) (hp : P N) :
    ¬ P (N+1) ∧ ¬ P (N+4) ∧ (P (N+2) ∨ P (N+5)) := by
  obtain ⟨m, hlo, hnext⟩ := triangular_bracket N
  have hhi : N^2+N ≤ tri (m+1) := le_of_not_gt fun h => hp (m+1) ⟨hnext,h⟩
  have hbig := Nat.mul_le_mul_left N hN
  have hleft : 7*N ≤ 5*m := by
    by_contra! hh
    have hmul := Nat.mul_le_mul (show 5*(m+1) ≤ 7*N+5 by omega)
      (show 5*(m+2) ≤ 7*N+10 by omega)
    nlinarith only [hmul, hnext, twice_tri (m+1), hbig, hN]
  have hright : 7*m+3 ≤ 10*N := by
    by_contra! hh
    have hmul := Nat.mul_self_le_mul_self (show 10*N ≤ 7*m+2 by omega)
    nlinarith only [hmul, hlo, twice_tri m, hbig, hN]
  have shift (s : ℕ) : 2 * tri (m+s) = 2 * tri m + 2*s*m + s*(s+1) := by
    rw [twice_tri, twice_tri]
    ring
  refine ⟨fun h => h (m+2) ?_, fun h => h (m+6) ?_, ?_⟩
  · change (N+1)^2 < tri (m+2) ∧ tri (m+2) < (N+1)^2 + (N+1)
    constructor <;> nlinarith only [shift 1, shift 2, hhi, hlo, hleft, hright, hN]
  · change (N+4)^2 < tri (m+6) ∧ tri (m+6) < (N+4)^2 + (N+4)
    constructor <;> nlinarith only [shift 1, shift 6, hhi, hlo, hleft, hright, hN]
  by_cases h : tri (m+3) ≤ (N+2)^2
  · left
    apply member_of_bracket (N+2) (m+3) h
    nlinarith only [shift 1, shift 4, hhi, hlo, hleft, hright, hN]
  · right
    apply member_of_bracket (N+5) (m+7)
    · nlinarith only [shift 7, hlo, hright]
    · push Not at h
      nlinarith only [shift 3, shift 8, h, hleft, hN]

end TriangularGeometry

/-! A finite check of triangular-number gaps below 200. -/

namespace TriangularSmall

open OMA.S_oeis_a242137

private def tri (j : ℕ) : ℕ := j*(j+1)/2

private theorem tri_mono : Monotone tri := fun _ _ h =>
  Nat.div_le_div_right (Nat.mul_le_mul h (Nat.succ_le_succ h))

private theorem P_iff_next {n j : ℕ} (hleft : tri j ≤ n^2) (hright : n^2 < tri (j+1)) :
    P n ↔ n^2+n ≤ tri (j+1) := by
  constructor
  · intro hp
    exact Nat.le_of_not_gt (fun h => hp (j+1) ⟨hright,h⟩)
  · intro h m hm
    by_cases hs : m ≤ j
    · exact (not_lt_of_ge ((tri_mono hs).trans hleft)) hm.1
    · exact (not_lt_of_ge (h.trans (tri_mono (show j+1 ≤ m by omega)))) hm.2

private def index (n : ℕ) : ℕ := ((8*n^2+1).sqrt-1)/2
private def next (n : ℕ) : ℕ := tri (index n + 1)
private def marked (n : ℕ) : Bool := decide (n^2+n ≤ next n)

private theorem brackets : (List.range 205).all (fun n =>
    decide (tri (index n) ≤ n^2 ∧ n^2 < next n)) = true := by decide +kernel

private theorem checked {n : ℕ} (hn : n < 205) : P n ↔ marked n = true := by
  have h := of_decide_eq_true (List.all_eq_true.mp brackets n (List.mem_range.mpr hn))
  change P n ↔ decide (n^2+n ≤ tri (index n + 1)) = true
  exact ⟨fun hp => decide_eq_true ((P_iff_next h.1 h.2).mp hp),
    fun hb => (P_iff_next h.1 h.2).mpr (of_decide_eq_true hb)⟩

private theorem cases_table : (List.range 200).all (fun n =>
    decide (3 ≤ n → marked n = true →
      marked (n+1) = false ∧ marked (n+4) = false ∧
        (marked (n+2) = true ∨ marked (n+5) = true))) = true := by decide +kernel

theorem small_case {n : ℕ} (hn : 3 ≤ n) (hlt : n < 200) (hp : P n) :
    ¬P (n+1) ∧ ¬P (n+4) ∧ (P (n+2) ∨ P (n+5)) := by
  have h := of_decide_eq_true (List.all_eq_true.mp cases_table n (List.mem_range.mpr hlt))
  obtain ⟨h1,h4,h2 | h5⟩ := h hn ((checked (by omega)).mp hp)
  all_goals
    refine ⟨fun h => Bool.noConfusion (((checked (by omega)).mp h).symm.trans h1),
      fun h => Bool.noConfusion (((checked (by omega)).mp h).symm.trans h4), ?_⟩
  · exact Or.inl ((checked (by omega)).mpr h2)
  · exact Or.inr ((checked (by omega)).mpr h5)

theorem two_case : ¬P 3 ∧ P 4 := by
  rw [checked (by decide : 3 < 205), checked (by decide : 4 < 205)]
  decide +kernel

theorem small_next {n : ℕ} (hn : 2 ≤ n) (hlt : n < 200) (hp : P n) :
    ¬P (n+1) ∧ (P (n+2) ∨ (¬P (n+4) ∧ P (n+5))) := by
  by_cases h : n = 2
  · subst n
    exact ⟨two_case.1, Or.inl two_case.2⟩
  · obtain ⟨h1,h4,h2 | h5⟩ := small_case (by omega) hlt hp
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr ⟨h4,h5⟩⟩

end TriangularSmall

namespace TriangularGaps

open OMA.S_oeis_a242137

private theorem next_options (N : ℕ) (hN : 2 ≤ N) (hp : P N) :
    ¬P (N+1) ∧ (P (N+2) ∨ (¬P (N+4) ∧ P (N+5))) := by
  by_cases h : N < 200
  · exact TriangularSmall.small_next hN h hp
  · obtain ⟨h1,h4,h2 | h5⟩ := TriangularGeometry.large N (by omega) hp
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr ⟨h4,h5⟩⟩

private theorem unbounded (m : ℕ) : ∃ N, m < N ∧ 2 ≤ N ∧ P N := by
  induction m with
  | zero => exact ⟨4, by decide, by decide, TriangularSmall.two_case.2⟩
  | succ m ih =>
    obtain ⟨N, hm, hN, hp⟩ := ih
    rcases (next_options N hN hp).2 with h2 | ⟨_, h5⟩
    · exact ⟨N+2, by omega, by omega, h2⟩
    · exact ⟨N+5, by omega, by omega, h5⟩

theorem consecutive (i : ℕ) (hi : 2 ≤ i) :
    Nat.nth P (i+1) - Nat.nth P i = 2 ∨
    Nat.nth P (i+1) - Nat.nth P i = 3 ∨
    Nat.nth P (i+1) - Nat.nth P i = 5 := by
  have hinf : (Set.ofPred P).Infinite := Set.infinite_of_forall_exists_gt fun m => by
    obtain ⟨N, hm, _, hp⟩ := unbounded m
    exact ⟨N, hp, hm⟩
  have mono := Nat.nth_strictMono hinf
  let N := Nat.nth P i
  let M := Nat.nth P (i+1)
  have hN : 2 ≤ N := hi.trans (mono.id_le i)
  have hM : P M := Nat.nth_mem_of_infinite hinf _
  have hlt : N < M := mono (Nat.lt_succ_self i)
  have least (k : ℕ) (hk : N < k) (hp : P k) : M ≤ k := by
    obtain ⟨j, rfl⟩ := Nat.subset_range_nth (p := P) (show k ∈ Set.ofPred P from hp)
    exact mono.monotone (show i+1 ≤ j from mono.lt_iff_lt.mp hk)
  obtain ⟨h1, h2 | ⟨h4,h5⟩⟩ := next_options N hN (Nat.nth_mem_of_infinite hinf _)
  · have bound := least (N+2) (by omega) h2
    have e : M ≠ N+1 := fun h => h1 (h ▸ hM)
    change M-N=2 ∨ M-N=3 ∨ M-N=5
    omega
  · have bound := least (N+5) (by omega) h5
    have e1 : M ≠ N+1 := fun h => h1 (h ▸ hM)
    have e4 : M ≠ N+4 := fun h => h4 (h ▸ hM)
    change M-N=2 ∨ M-N=3 ∨ M-N=5
    omega

end TriangularGaps

theorem OMA.solution : type_of% @OMA.S_oeis_a242137.main := by
  intro n hn
  simpa only [OMA.S_oeis_a242137.a, show n+1-1 = n-1+1 by omega] using
    TriangularGaps.consecutive (n-1) (by omega)
