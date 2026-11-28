import OMAReductions.R_Erdos933_erdos_933_R1

/-!
Proof of `OMA.R_Erdos933_erdos_933_R1.H1`.
This is the lower bound proved upstream as `Erdos933.erdos_933.variants.lower_bound`:
for n = 2 ^ (3 ^ (r + 1)) the smooth part 2 ^ k(n) 3 ^ l(n) of n(n+1) exceeds n log n.
-/

namespace OMAProof.Erdos933H1
end OMAProof.Erdos933H1

theorem OMA.solution : OMA.R_Erdos933_erdos_933_R1.H1 :=
  Erdos933.erdos_933.variants.lower_bound
