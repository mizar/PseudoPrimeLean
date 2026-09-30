import PseudoPrime.PrimeTest.Decision
import PseudoPrime.PrimeTest.LucasV.Prime

/-! # Certified one-sided LucasV decisions -/

namespace PseudoPrime.PrimeTest

/-- Check the discriminant identity and Jacobi -1 branch before using prime completeness.
Invalid parameters and unsupported branches yield unknown, as does probable-prime acceptance.
Only a failed comparison with checked hypotheses proves non-primality. -/
def LucasV.decideWithParams (n : ℕ) (D P Q : ℤ) : Decision n :=
  if hd : D = P * P - 4 * Q then
    if hj : jacobiSym D n = -1 then
      decideByPrimePass n (lucasVWithParams n D P Q)
        (fun hp ↦ lucasVWithParams_of_prime hp D P Q hd hj)
    else .unknown
  else .unknown

end PseudoPrime.PrimeTest
