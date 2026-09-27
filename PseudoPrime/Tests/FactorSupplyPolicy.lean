import PseudoPrime.NumberTheory.Factorization.PollardRho.FactorSupply
import PseudoPrime.PrimeTest.FactorizationPolicy
import PseudoPrime.PrimeTest.SmallInput

/-!
# Leaf policy and partial factorization regressions
These private checks distinguish rejection from compositeness and preserve partial products.
-/
namespace PseudoPrime.Tests.FactorSupplyPolicy

/-- Certify only the small inputs allowed by the caller. -/
private def smallPolicy : NumberTheory.Factorization.PrimeLeafPolicy :=
  PrimeTest.primeLeafPolicyOfDecision (PrimeTest.SmallInput.classify 2)

/-- Two splits retain the two certified factors and leave the out-of-range prime unresolved. -/
example :
    (NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply smallPolicy ⟨2, 1⟩ 2
      12).factors =
      [2, 2] := by
  decide +kernel

/-- An unclassified prime remains in the residual cofactor. -/
example :
    (NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply smallPolicy ⟨2, 1⟩ 2
      12).remainder =
      3 := by
  decide +kernel

/-- Complete factor supply may fail even when partial supply has certified factors. -/
example :
    NumberTheory.Factorization.PollardRho.primeFactorListFuel smallPolicy ⟨2, 1⟩ 2 12 = none := by
  decide +kernel

/-- Zero split budget preserves an unclassified input unchanged. -/
example :
    (NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply smallPolicy ⟨2, 1⟩ 0
      3).remainder =
      3 := by
  decide +kernel

/-- Rejection of zero and one never creates a prime leaf. -/
example :
    (NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply smallPolicy ⟨2, 1⟩ 0
      0).factors =
      [] ∧
    (NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply smallPolicy ⟨2, 1⟩ 0
      1).factors =
      [] := by
  decide +kernel

/-- An explicit two-node budget has the same partial result as the depth-bounded example. -/
example :
    (NumberTheory.Factorization.PollardRho.partialPrimeFactorSupplyByTree smallPolicy ⟨2, 1⟩
      (.split 1 .leaf (.split 1 .leaf .leaf)) 12).factors = [2, 2] ∧
    (NumberTheory.Factorization.PollardRho.partialPrimeFactorSupplyByTree smallPolicy ⟨2, 1⟩
      (.split 1 .leaf (.split 1 .leaf .leaf)) 12).remainder = 3 := by
  decide +kernel

/-- Unknown decisions supply no prime proof, including for a prime input. -/
example :
    (NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply
      (PrimeTest.primeLeafPolicyOfDecision (fun _ ↦ .unknown)) ⟨2, 1⟩ 0 2).factors = [] := by
  decide +kernel

end PseudoPrime.Tests.FactorSupplyPolicy
