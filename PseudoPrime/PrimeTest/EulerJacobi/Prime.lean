/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.EulerJacobi.Spec

/-!
# Prime inputs for the Euler–Jacobi test

The prime case is proved directly in `ZMod` from the Legendre-symbol power
formula, avoiding any conversion of the Jacobi value to a natural residue.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Every natural base satisfies the raw Euler–Jacobi equality modulo the prime `p`.
The sole premise is `p.Prime`; bases divisible by `p` and the prime `2` are included.
The proof changes Jacobi to Legendre and applies its residue-ring power formula.
This private bridge provides acceptance of the natural-base executable comparison.
-/
private theorem eulerJacobi_condition_of_prime {p a : ℕ} (hp : p.Prime) :
    IsEulerJacobiProbablePrime p a := by
  change (a : ZMod p) ^ (p / 2) = (jacobiSym (a : ℤ) p : ZMod p)
  rw [← @jacobiSym.legendreSym.to_jacobiSym p ⟨hp⟩ (a : ℤ)]
  simpa only [Int.cast_natCast] using (@legendreSym.eq_pow p ⟨hp⟩ (a : ℤ)).symm

/--
Every prime `p` is accepted by the raw natural-base Euler–Jacobi comparison.
Despite the historical suffix, the theorem has no `p ≠ 2` or coprimality premise and covers
all natural bases `a`. Apply the executable equivalence to `eulerJacobi_condition_of_prime`.
The unguarded one-sided decision adapter uses precisely this stronger prime-pass contract.
-/
theorem eulerJacobiWithBase_of_prime_of_ne_two {p a : ℕ} (hp : p.Prime) :
    eulerJacobiWithBase p a = true := by
  apply (eulerJacobiWithBase_eq_true_iff).2
  exact eulerJacobi_condition_of_prime hp

/--
The raw Euler–Jacobi condition holds at modulus `2` for every natural base.
This is the general prime-modulus identity specialized using `Nat.prime_two`.
It supplies the modulus-two branch in the compatibility prime-pass theorem.
-/
private theorem eulerJacobi_condition_of_two {a : ℕ} : IsEulerJacobiProbablePrime 2 a := by
  exact eulerJacobi_condition_of_prime Nat.prime_two

/--
A natural base coprime to the prime `p` is accepted by the raw Euler–Jacobi comparison.
The statement retains the coprimality premise `ha` for callers, although the stronger
prime-pass identity used in the proof does not need it. Splitting `p = 2` handles the explicit
boundary lemma and otherwise uses `eulerJacobiWithBase_of_prime_of_ne_two`.
This compatibility theorem does not add a coprimality check to the executable definition.
-/
theorem eulerJacobiWithBase_of_prime {p a : ℕ} (hp : p.Prime) (ha : Nat.Coprime a p) :
    eulerJacobiWithBase p a = true := by
  rcases eq_or_ne p 2 with rfl | _hp2
  · apply (eulerJacobiWithBase_eq_true_iff).2
    exact eulerJacobi_condition_of_two
  · exact eulerJacobiWithBase_of_prime_of_ne_two hp

/--
Every signed integer base `a` passes the raw Euler–Jacobi test modulo a prime `p`.
Only `p.Prime` is assumed; negative, zero, and non-coprime bases are included.
Convert the executable Boolean to its equality, rewrite Jacobi as Legendre, and apply
`legendreSym.eq_pow`. Strengthened BPSW uses this theorem for the signed Lucas parameter `Q`.
-/
theorem eulerJacobiWithIntBase_of_prime {p : ℕ} (hp : p.Prime) (a : ℤ) :
    eulerJacobiWithIntBase p a = true := by
  apply (eulerJacobiWithIntBase_eq_true_iff).2
  change (a : ZMod p) ^ (p / 2) = (jacobiSym a p : ZMod p)
  rw [← @jacobiSym.legendreSym.to_jacobiSym p ⟨hp⟩ a]
  exact (@legendreSym.eq_pow p ⟨hp⟩ a).symm

end PseudoPrime.PrimeTest
