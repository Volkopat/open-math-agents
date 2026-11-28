import OMAStatements.S_oeis_a280172
import Mathlib

/-!
# OEIS A280172: in the greedy table, the (2^k)-th antidiagonal is constantly 2^k and T(2n, k) = 2*T(n, ceiling(k/2))

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Key fact: G(i,j) = 1 + (i XOR j). (1) x = i XOR j is not i XOR j' for j' < j nor i' XOR j for i' <
i, so x+1 is available. (2) Every t < x is taken: by Nat.lt_xor_cases, t < i XOR j gives (t XOR i) <
j or (t XOR j) < i, and the entry there is t+1. So the XOR table is greedy, and by strong induction
on i+j every greedy table equals it. (3) If i + j = 2^e - 1 then i and j are complementary in their
low e bits, so i XOR j = 2^e - 1. (4) For the k-th term of antidiagonal 2n, the coordinates k-1 and
2n-k have opposite parity and halves q-1 and n-q with q = ceil(k/2), so (k-1) XOR (2n-k) = 2*((q-1)
XOR (n-q)) + 1; adding 1 gives the doubling identity.
-/

open OMA.S_oeis_a280172

namespace OMA.A280172Proof

def xorTable (i j : ℕ) : ℕ := (i ^^^ j) + 1

lemma xorTable_available (i j : ℕ) : Available xorTable i j (xorTable i j) := by
  refine ⟨by unfold xorTable; omega, ?_, ?_⟩
  · intro k hk heq
    have hx : i ^^^ k = i ^^^ j := Nat.add_right_cancel heq
    have hkj := congrArg (fun x => i ^^^ x) hx
    simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at hkj
    omega
  · intro k hk heq
    have hx : k ^^^ j = i ^^^ j := Nat.add_right_cancel heq
    have hki := congrArg (fun x => x ^^^ j) hx
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hki
    omega

lemma xorTable_greedy : Greedy xorTable := by
  intro i j
  refine ⟨xorTable_available i j, ?_⟩
  intro v hv
  change Available xorTable i j v at hv
  have hvpos : 0 < v := hv.1
  by_contra h
  have hlt : v - 1 < i ^^^ j := by unfold xorTable at h; omega
  rcases Nat.lt_xor_cases hlt with hc | hr
  · have hne := hv.2.2 ((v - 1) ^^^ j) hc
    apply hne
    unfold xorTable
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    omega
  · have hne := hv.2.1 ((v - 1) ^^^ i) hr
    apply hne
    unfold xorTable
    rw [Nat.xor_comm (v - 1) i]
    simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    omega

lemma greedy_eq (G : ℕ → ℕ → ℕ) (hG : Greedy G) (i j : ℕ) :
    G i j = xorTable i j := by
  generalize hs : i + j = s
  induction s using Nat.strong_induction_on generalizing i j with
  | h s ih =>
    have hrow (k : ℕ) (hk : k < j) : G i k = xorTable i k :=
      ih (i + k) (by omega) i k rfl
    have hcol (k : ℕ) (hk : k < i) : G k j = xorTable k j :=
      ih (k + j) (by omega) k j rfl
    have hset : {v : ℕ | Available G i j v} =
        {v : ℕ | Available xorTable i j v} := by
      ext v
      change Available G i j v ↔ Available xorTable i j v
      constructor
      · intro hv
        refine ⟨hv.1, ?_, ?_⟩
        · intro k hk
          rw [← hrow k hk]
          exact hv.2.1 k hk
        · intro k hk
          rw [← hcol k hk]
          exact hv.2.2 k hk
      · intro hv
        refine ⟨hv.1, ?_, ?_⟩
        · intro k hk
          rw [hrow k hk]
          exact hv.2.1 k hk
        · intro k hk
          rw [hcol k hk]
          exact hv.2.2 k hk
    have hleast := hG i j
    rw [hset] at hleast
    exact hleast.unique (xorTable_greedy i j)

lemma xor_of_odd_sum (i j : ℕ) (h : (i + j) % 2 = 1) :
    i ^^^ j = 2 * (i / 2 ^^^ j / 2) + 1 := by
  have hmod : (i ^^^ j) % 2 = 1 := Nat.xor_mod_two_eq_one.mpr (by omega)
  have hdiv := Nat.xor_div_two (a := i) (b := j)
  omega

lemma xor_of_sum_pow (e i j : ℕ) (h : i + j = 2 ^ e - 1) :
    i ^^^ j = 2 ^ e - 1 := by
  induction e generalizing i j with
  | zero =>
    have hi : i = 0 := by norm_num at h; omega
    have hj : j = 0 := by norm_num at h; omega
    simp [hi, hj]
  | succ e ih =>
    have hpos : 0 < 2 ^ e := by positivity
    rw [pow_succ] at h ⊢
    have hodd : (i + j) % 2 = 1 := by omega
    have hhalf : i / 2 + j / 2 = 2 ^ e - 1 := by omega
    rw [xor_of_odd_sum i j hodd, ih (i / 2) (j / 2) hhalf]
    omega

lemma xorTable_double (n k : ℕ) (_hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ 2 * n) :
    T xorTable (2 * n) k = 2 * T xorTable n ((k + 1) / 2) := by
  unfold T xorTable
  have hodd : ((k - 1) + (2 * n - k)) % 2 = 1 := by omega
  have hi : (k - 1) / 2 = (k + 1) / 2 - 1 := by omega
  have hj : (2 * n - k) / 2 = n - (k + 1) / 2 := by omega
  rw [xor_of_odd_sum (k - 1) (2 * n - k) hodd, hi, hj]
  omega

end OMA.A280172Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a280172.main := by
  refine ⟨⟨OMA.A280172Proof.xorTable, OMA.A280172Proof.xorTable_greedy⟩, ?_⟩
  intro G hG
  have hEq : G = OMA.A280172Proof.xorTable := by
    funext i j
    exact OMA.A280172Proof.greedy_eq G hG i j
  subst G
  constructor
  · intro e i j h
    unfold OMA.A280172Proof.xorTable
    rw [OMA.A280172Proof.xor_of_sum_pow e i j h]
    have hpos : 0 < 2 ^ e := by positivity
    omega
  · exact OMA.A280172Proof.xorTable_double
