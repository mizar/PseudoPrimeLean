/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CorrelationEnergyMoments
public import Mathlib.Data.Int.Interval

/-! # Bounded Heilbronn congruences and the energy counting budget -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For prime p and natural H, the finite triples (u,x,y) with u in the Heilbronn subgroup,
-H<=x,y<=H, x,y nonzero, and u*x=y modulo p^2. This is the bounded congruence set
needed in the Fermat-quotient argument; no estimate is included in the definition. -/
noncomputable def boundedHeilbronnCongruences (p H : ℕ) [Fact p.Prime] :
    Finset (ZMod (p ^ 2) × ℤ × ℤ) := by
  classical
    exact
    ((shiftedTeichCoset p 0).toFinset ×ˢ
          (Finset.Icc (-(H : ℤ)) H ×ˢ Finset.Icc (-(H : ℤ)) H)).filter
      (fun z ↦ z.2.1 ≠ 0 ∧ z.2.2 ≠ 0 ∧ z.1 * (z.2.1 : ZMod (p ^ 2)) = (z.2.2 : ZMod (p ^ 2)))

/-- Number of bounded Heilbronn congruence triples for p,H. The finite-set definition
counts actual solutions rather than an assumed analytic bound. -/
noncomputable def boundedCongruenceCount (p H : ℕ) [Fact p.Prime] : ℕ :=
  (boundedHeilbronnCongruences p H).card

/-- For natural p,k,E,N,A,B, E^2<=A, N*k<=B and p^2*A*B^2<k^6 imply p*E*N<k^2.
Square the product estimate and compare it with the sixth power;
this is a generic counting budget. -/
theorem counting_budget_of_square_energy {p k E N A B : ℕ} (hE : E ^ 2 ≤ A) (hN : N * k ≤ B)
    (hgap : p ^ 2 * A * B ^ 2 < k ^ 6) : p * E * N < k ^ 2 := by
  have hN2 := Nat.pow_le_pow_left hN 2
  have hprod := Nat.mul_le_mul hE hN2
  have hp := Nat.mul_le_mul_left (p ^ 2) hprod
  have hbound : (p * E * N * k) ^ 2 < k ^ 6 := by
    have he : (p * E * N * k) ^ 2 ≤ p ^ 2 * A * B ^ 2 := by convert hp using 1 <;> ring
    exact he.trans_lt hgap
  by_contra hnot
  have hge : k ^ 2 ≤ p * E * N := Nat.le_of_not_gt hnot
  have hm := Nat.mul_le_mul_right k hge
  have hs := Nat.pow_le_pow_left hm 2
  nlinarith only [hbound, hs]

/-- For odd prime p, if the actual bounded congruence count times k is at most B
and 18874370*p^7*B^2<k^6, then p*E*count<k^2. Insert the proved unconditional 5/2
energy bound into the generic budget. The congruence estimate remains an explicit premise. -/
theorem boundedCongruenceCount_energy_budget {p H k B : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hcount : boundedCongruenceCount p H * k ≤ B) (hgap : 18874370 * p ^ 7 * B ^ 2 < k ^ 6) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  apply counting_budget_of_square_energy (heilbronnEnergy_square_le_uniform hodd) hcount
  convert hgap using 1
  ring

end PseudoPrime.NumberTheory.Heilbronn
