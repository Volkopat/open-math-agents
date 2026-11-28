import OMAStatements.S_oeis_a076935

namespace OMA.S_oeis_a076935


/-- The increments of A076935: bit m is a(m) - a(m-1) for 1 <= m <= 61371 (bit 1 is a(1) = 1). -/
def D : ℕ := 0xd6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5ad5adad56b6ad6d6ab5b5adad5adad56b6ad6d6b56b6b55adad5adad56b6ad6d6b6b56b6b55adab5b5ad5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d5adad56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6d6ad6d6ab5b56b6b5ab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5aad6d6b6b56b6b55adab5b5ad5adad56b6b56b6b55adab5b5adad5adad56b6ad6d6b56b6b55adad6d6ad6d6ab5b56b6b5ab5b5aad6d6ad6d6ab5b56b6b5b5ab5b5aad6d5adad6ad6d6ab5b5ab5b5aad6d5adad6ad6d6ab5b56b6b55adad6d6a

/-- Bit i of T as a number 0 or 1. -/
def bitv (T i : ℕ) : ℕ := (T >>> i) % 2

/-- Prefix sums: A T m = bits 1..m of T. -/
def A (T : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => A T m + bitv T (m + 1)

/-- How much a pointer at s advances when the pointer it reads advances by b: bit s + 1 if b = 1. -/
def u (T b s : ℕ) : ℕ := cond (Nat.beq b 1) (bitv T (s + 1)) 0

/-- The streaming check from step n with pointer state s1..s5, ending in the state e1..e5. -/
def run (T : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, s1, s2, s3, s4, s5, e1, e2, e3, e4, e5 =>
    Nat.beq s1 e1 && Nat.beq s2 e2 && Nat.beq s3 e3 && Nat.beq s4 e4 && Nat.beq s5 e5
  | fuel + 1, n, s1, s2, s3, s4, s5, e1, e2, e3, e4, e5 =>
    Nat.beq (s1 + bitv T n + s1 + s3 + s5) (n + s2 + s4) &&
      run T fuel (n + 1) (s1 + bitv T n) (s2 + u T (bitv T n) s1)
        (s3 + u T (u T (bitv T n) s1) s2) (s4 + u T (u T (u T (bitv T n) s1) s2) s3)
        (s5 + u T (u T (u T (u T (bitv T n) s1) s2) s3) s4) e1 e2 e3 e4 e5

/-- The pointer invariant at step n. -/
def Inv (T n s1 s2 s3 s4 s5 : ℕ) : Prop :=
  s1 = A T (n - 1) ∧ s2 = A T s1 ∧ s3 = A T s2 ∧ s4 = A T s3 ∧ s5 = A T s4

/-- The recurrence of A076935 for A T at m. -/
def Rec (T m : ℕ) : Prop :=
  (A T m : ℤ) = m - A T (m - 1) + A T (A T (m - 1)) - A T (A T (A T (m - 1))) +
    A T (A T (A T (A T (m - 1)))) - A T (A T (A T (A T (A T (m - 1)))))

lemma bitv_le (T i : ℕ) : bitv T i ≤ 1 := by unfold bitv; omega

lemma u_le (T b s : ℕ) : u T b s ≤ 1 := by
  unfold u
  cases Nat.beq b 1
  · simp
  · exact bitv_le T (s + 1)

lemma A_le (T m : ℕ) : A T m ≤ m := by
  induction m with
  | zero => simp [A]
  | succ m ih =>
    have := bitv_le T (m + 1)
    simp only [A]
    omega

lemma adv (T s b : ℕ) (hb : b ≤ 1) : A T (s + b) = A T s + u T b s := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · rfl
  · simp [u, A]

theorem run_spec {T fuel n s1 s2 s3 s4 s5 e1 e2 e3 e4 e5 : ℕ}
    (h : run T fuel n s1 s2 s3 s4 s5 e1 e2 e3 e4 e5 = true) (hn : 1 ≤ n)
    (hi : Inv T n s1 s2 s3 s4 s5) :
    (∀ m, n ≤ m → m < n + fuel → Rec T m) ∧ Inv T (n + fuel) e1 e2 e3 e4 e5 := by
  induction fuel generalizing n s1 s2 s3 s4 s5 with
  | zero =>
    simp only [run, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    subst h1 h2 h3 h4 h5
    exact ⟨fun m h1 h2 => by omega, by simpa using hi⟩
  | succ fuel ih =>
    simp only [run, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨hc, hr⟩ := h
    obtain ⟨i1, i2, i3, i4, i5⟩ := hi
    have hb := bitv_le T n
    have hn1 : A T n = s1 + bitv T n := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [i1]
      simp [A]
    have hi' : Inv T (n + 1) (s1 + bitv T n) (s2 + u T (bitv T n) s1)
        (s3 + u T (u T (bitv T n) s1) s2) (s4 + u T (u T (u T (bitv T n) s1) s2) s3)
        (s5 + u T (u T (u T (u T (bitv T n) s1) s2) s3) s4) := by
      refine ⟨by rw [Nat.add_sub_cancel, hn1], ?_, ?_, ?_, ?_⟩
      · rw [adv T s1 _ hb, ← i2]
      · rw [adv T s2 _ (u_le _ _ _), ← i3]
      · rw [adv T s3 _ (u_le _ _ _), ← i4]
      · rw [adv T s4 _ (u_le _ _ _), ← i5]
    obtain ⟨ih1, ih2⟩ := ih hr (by omega) hi'
    refine ⟨fun m hm1 hm2 => ?_, by rw [show n + (fuel + 1) = n + 1 + fuel by ring]; exact ih2⟩
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
    · unfold Rec
      rw [hn1, ← i1, ← i2, ← i3, ← i4, ← i5]
      push_cast
      omega
    · exact ih1 m (by omega) (by omega)

theorem agree (T N : ℕ) (h1 : A T 1 = 1) (hr : ∀ m, 2 ≤ m → m ≤ N → Rec T m) :
    ∀ m, m ≤ N → a m = A T m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    match m with
    | 0 => simp [a, A]
    | 1 => rw [h1]; simp [a]
    | k + 2 =>
      have IH : ∀ j, j < k + 2 → a j = A T j := fun j hj => ih j hj (by omega)
      have l1 := A_le T (k + 1)
      have l2 := A_le T (A T (k + 1))
      have l3 := A_le T (A T (A T (k + 1)))
      have l4 := A_le T (A T (A T (A T (k + 1))))
      have e1 := IH (k + 1) (by omega)
      have e2 := IH (A T (k + 1)) (by omega)
      have e3 := IH (A T (A T (k + 1))) (by omega)
      have e4 := IH (A T (A T (A T (k + 1)))) (by omega)
      have e5 := IH (A T (A T (A T (A T (k + 1))))) (by omega)
      have hrk := hr (k + 2) (by omega) hm
      unfold Rec at hrk
      rw [show k + 2 - 1 = k + 1 by omega] at hrk
      rw [a]
      simp only [e1, Int.toNat_natCast, dif_pos (show A T (k + 1) < k + 2 by omega), e2,
        dif_pos (show A T (A T (k + 1)) < k + 2 by omega), e3,
        dif_pos (show A T (A T (A T (k + 1))) < k + 2 by omega), e4,
        dif_pos (show A T (A T (A T (A T (k + 1)))) < k + 2 by omega), e5]
      rw [hrk]
      push_cast
      ring

set_option maxHeartbeats 20000000 in
theorem a_N : a 61371 = 36670 := by
  have i0 : Inv D 2 1 1 1 1 1 := by
    unfold Inv
    decide +kernel
  have h0 : run D 7671 2 1 1 1 1 1 4584 2739 1637 978 584 = true := by
    decide +kernel
  have h1 : run D 7671 7673 4584 2739 1637 978 584 9167 5477 3273 1956 1169 = true := by
    decide +kernel
  have h2 : run D 7671 15344 9167 5477 3273 1956 1169 13751 8216 4909 2933 1753 = true := by
    decide +kernel
  have h3 : run D 7672 23015 13751 8216 4909 2933 1753 18335 10955 6546 3911 2337 = true := by
    decide +kernel
  have h4 : run D 7671 30687 18335 10955 6546 3911 2337 22918 13694 8182 4889 2922 = true := by
    decide +kernel
  have h5 : run D 7671 38358 22918 13694 8182 4889 2922 27502 16432 9818 5866 3505 = true := by
    decide +kernel
  have h6 : run D 7671 46029 27502 16432 9818 5866 3505 32085 19171 11455 6845 4090 = true := by
    decide +kernel
  have h7 : run D 7672 53700 32085 19171 11455 6845 4090 36670 21910 13091 7822 4673 = true := by
    decide +kernel
  have r0 := run_spec h0 (by norm_num) i0
  have i1 : Inv D 7673 4584 2739 1637 978 584 := r0.2
  have r1 := run_spec h1 (by norm_num) i1
  have i2 : Inv D 15344 9167 5477 3273 1956 1169 := r1.2
  have r2 := run_spec h2 (by norm_num) i2
  have i3 : Inv D 23015 13751 8216 4909 2933 1753 := r2.2
  have r3 := run_spec h3 (by norm_num) i3
  have i4 : Inv D 30687 18335 10955 6546 3911 2337 := r3.2
  have r4 := run_spec h4 (by norm_num) i4
  have i5 : Inv D 38358 22918 13694 8182 4889 2922 := r4.2
  have r5 := run_spec h5 (by norm_num) i5
  have i6 : Inv D 46029 27502 16432 9818 5866 3505 := r5.2
  have r6 := run_spec h6 (by norm_num) i6
  have i7 : Inv D 53700 32085 19171 11455 6845 4090 := r6.2
  have r7 := run_spec h7 (by norm_num) i7
  have i8 : Inv D 61372 36670 21910 13091 7822 4673 := r7.2
  have hrec : ∀ m, 2 ≤ m → m ≤ 61371 → Rec D m := by
    intro m h1 h2
    by_cases c0 : m < 7673
    · exact r0.1 m (by omega) (by omega)
    by_cases c1 : m < 15344
    · exact r1.1 m (by omega) (by omega)
    by_cases c2 : m < 23015
    · exact r2.1 m (by omega) (by omega)
    by_cases c3 : m < 30687
    · exact r3.1 m (by omega) (by omega)
    by_cases c4 : m < 38358
    · exact r4.1 m (by omega) (by omega)
    by_cases c5 : m < 46029
    · exact r5.1 m (by omega) (by omega)
    by_cases c6 : m < 53700
    · exact r6.1 m (by omega) (by omega)
    exact r7.1 m (by omega) (by omega)
  have hA1 : A D 1 = 1 := by decide +kernel
  have hlast : A D 61371 = 36670 := i8.1.symm
  rw [agree D 61371 hA1 hrec 61371 le_rfl, hlast]
  norm_num

/-- The real root of 1 - 2x + x^2 - x^3 + x^4 - x^5 lies in [0.5974970086, 0.5974970087]. -/
theorem root_exists : ∃ c : ℝ, (5974970086 / 10 ^ 10 : ℝ) ≤ c ∧ c ≤ 5974970087 / 10 ^ 10 ∧
    1 - 2 * c + c ^ 2 - c ^ 3 + c ^ 4 - c ^ 5 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => 1 - 2 * x + x ^ 2 - x ^ 3 + x ^ 4 - x ^ 5)
      (Set.Icc (5974970086 / 10 ^ 10) (5974970087 / 10 ^ 10)) := by fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => 1 - 2 * x + x ^ 2 - x ^ 3 + x ^ 4 - x ^ 5)
      (5974970087 / 10 ^ 10)) ((fun x : ℝ => 1 - 2 * x + x ^ 2 - x ^ 3 + x ^ 4 - x ^ 5)
      (5974970086 / 10 ^ 10)) := by
    simp only [Set.mem_Icc]
    constructor <;> norm_num
  obtain ⟨c, ⟨hl, hu⟩, hc⟩ := intermediate_value_Icc' (by norm_num) hcont hmem
  exact ⟨c, hl, hu, hc⟩

/-- Cloitre's conjecture fails: for the real root c, a(61371) = 36670 = floor(61371 c) + 2. -/
theorem disproof : ¬ (∀ c : ℝ, 1 - 2 * c + c ^ 2 - c ^ 3 + c ^ 4 - c ^ 5 = 0 →
    ∀ n : ℕ, 1 ≤ n → (a n = ⌊c * n⌋ ∨ a n = ⌊c * n⌋ + 1)) := by
  intro h
  obtain ⟨c, hl, hu, hc⟩ := root_exists
  have hfl : ⌊c * ((61371 : ℕ) : ℝ)⌋ = 36668 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith
  have ha : a 61371 = 36670 := by
    have := a_N
    exact this
  rcases h c hc 61371 (by norm_num) with h1 | h1 <;> rw [hfl, ha] at h1 <;> norm_num at h1

end OMA.S_oeis_a076935

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a076935.main) :=
  OMA.S_oeis_a076935.disproof
