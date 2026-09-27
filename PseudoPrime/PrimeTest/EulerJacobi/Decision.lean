import PseudoPrime.PrimeTest.Decision
import PseudoPrime.PrimeTest.EulerJacobi.Prime

/-! # Certified one-sided EulerJacobi decisions -/
namespace PseudoPrime.PrimeTest

/-- Refute primality using the raw n/2 Euler-Jacobi comparison.
Prime completeness includes zero and non-coprime bases; no coprimality guard is required.
Acceptance remains unknown and does not establish the conventional small-input boundaries. -/
def EulerJacobi.decideWithIntBase (n : ℕ) (a : ℤ) : Decision n :=
  decideByPrimePass n (eulerJacobiWithIntBase n a)
    (fun hp ↦ eulerJacobiWithIntBase_of_prime hp a)

/-- Refute primality using the raw n/2 Euler-Jacobi comparison.
Prime completeness includes zero and non-coprime bases; no coprimality guard is required.
Acceptance remains unknown and does not establish the conventional small-input boundaries. -/
def EulerJacobi.decideWithBase (n a : ℕ) : Decision n :=
  decideByPrimePass n (eulerJacobiWithBase n a)
    (fun hp ↦ eulerJacobiWithBase_of_prime_of_ne_two hp)

end PseudoPrime.PrimeTest
