/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaRefinedLocalConductorBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrimeIndexedPrefix

/-! # Integer prefixes in the actual primitive Jacobi conductor comparison -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For odd n, the ambient prime factors of 4n are precisely the input
prime factors and the separate prime two. The sets are disjoint by oddness.
This identifies the ambient factor sum in the shared local-cost theorem. -/
theorem gamma_ambient_four_factor_sum_eq {n : ℕ} (hn : Odd n) (F : ℕ → ℝ) :
    (∑ p ∈ (4 * n).primeFactors, F p) = (∑ p ∈ n.primeFactors, F p) + F 2 := by
  have htwo : 2 ∉ n.primeFactors := fun hp ↦ hn.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hfour : (4 : ℕ).primeFactors = {2} := by decide +kernel
  rw [Nat.primeFactors_mul (by norm_num only : (4 : ℕ) ≠ 0) hn.pos.ne', hfour,
    Finset.singleton_union, Finset.sum_insert htwo, add_comm]

/-- Absence of negative Jacobi witnesses below b makes the actual
primitive character one at every prime coprime to the ambient 4n.
Coprimality excludes prime two and character value zero; quadraticity
and the odd-prime Jacobi evaluation exclude minus one. This transfers
the original witness assumption without assuming all conductor units are one. -/
theorem gamma_jacobi_no_negative_prefix_prime_one {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {b : ℝ}
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ b → jacobiSym n p ≠ -1) :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p (4 * n) → bridge.character p = 1 := by
  intro p hp hpb hcop
  have hodd : Odd p :=
    Nat.coprime_two_right.mp (hcop.of_dvd_right (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩))
  have hcopn : Nat.Coprime p n := hcop.of_dvd_right ⟨4, by ring⟩
  have hv : bridge.character p = (jacobiSym n p : ℂ) := by
    rw [bridge.character_eq]
    simpa only [Int.cast_natCast] using
      NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hp hodd
        (hp.coprime_iff_not_dvd.mp hcopn)
  have hu : IsUnit (p : ZMod (NumberTheory.complexQuadraticCharacter n hn).conductor) :=
    (ZMod.isUnit_iff_coprime _ _).mpr
      (hcop.of_dvd_right
        (DirichletCharacter.conductor_dvd_level (NumberTheory.complexQuadraticCharacter n hn)))
  rcases bridge.character_quadratic p with h0 | h1 | hm
  · exact False.elim ((MulChar.apply_ne_zero_iff.mpr hu) h0)
  · exact h1
  · have hj : jacobiSym n p = -1 := by exact_mod_cast (hv.symm.trans hm)
    exact False.elim (hno p hp hodd hpb hj)

/-- At the prescribed input scale, the actual integer prefix correction
and full ambient ramp sum obey the same finite signed dual bound as
the local costs. Reindex the original prefix over ambient prime factors
and split off two. The actual primitive bridge removes every separate
conductor and dyadic branch premise. -/
theorem gamma_jacobi_integer_prefix_local_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {b : ℝ} (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p (4 * n) → bridge.character p = 1)
    (hlarge : 10 ^ 100 ≤ n) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        ((∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
            (1 - (bridge.character m).re) * Analysis.gammaResolventMangoldtWeight m) +
          ∑ p ∈ (4 * n).primeFactors,
            Real.log p *
              ((∑' k : ℕ,
                  Analysis.exponentialRampLocalCorrection (bridge.character p)
                    ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
                Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale (Real.log n)) * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet (Analysis.gammaRefinedScale (Real.log n)),
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p
                  (Analysis.gammaRefinedScale (Real.log n)) -
                Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale (Real.log n)))
              0 := by
  let K := AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b
  have he :=
    AnalyticNumberTheory.DirichletLFunction.gamma_character_prefix_add_ambient_ramp_eq_local_cost
      bridge.character (Nat.mul_pos (by norm_num only) hn.pos) hb hone
      (Analysis.gammaRefinedScale (Real.log n))
  rw [he, gamma_ambient_four_factor_sum_eq hn]
  simpa only [add_assoc] using
    gamma_jacobi_refined_input_all_local_cost_le_finite_signed_dual bridge K (K 2) hlarge

/-- With no negative Jacobi prime witness up to b, the original integer
prefix and actual ambient ramp losses satisfy the finite signed dual
comparison. Transfer the witness assumption to ambient unit primes and
apply the integer-prefix budget. This is the no-negative-witness interface. -/
theorem gamma_jacobi_no_negative_integer_prefix_local_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {b : ℝ}
    (hb : 1 ≤ b) (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ b → jacobiSym n p ≠ -1)
    (hlarge : 10 ^ 100 ≤ n) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        ((∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
            (1 - (bridge.character m).re) * Analysis.gammaResolventMangoldtWeight m) +
          ∑ p ∈ (4 * n).primeFactors,
            Real.log p *
              ((∑' k : ℕ,
                  Analysis.exponentialRampLocalCorrection (bridge.character p)
                    ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
                Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale (Real.log n)) * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet (Analysis.gammaRefinedScale (Real.log n)),
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p
                  (Analysis.gammaRefinedScale (Real.log n)) -
                Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale (Real.log n)))
              0 := by
  exact
    gamma_jacobi_integer_prefix_local_budget bridge hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge hno) hlarge

/-- Signed finite dual budget at the prescribed real logarithmic scale.
It equals mu(x)*L plus the weighted positive ramified excess over the
finite scale-dependent odd-prime set. This definition is the numerical
quantity remaining after exact conductor and integer-prefix accounting. -/
noncomputable def gammaRefinedSignedDualBudget (L : ℝ) : ℝ :=
  Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale L) * L +
    ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet (Analysis.gammaRefinedScale L),
      Real.log p *
        max
          (Analysis.gammaRamifiedSignedCombinedCost p (Analysis.gammaRefinedScale L) -
            Analysis.gammaRamifiedDualParameter (Analysis.gammaRefinedScale L))
          0

/-- Under individual RH for the actual primitive Jacobi character, the
signed zero-mass prefix and full ambient ramp losses obey a common
finite dual comparison. The original integer prefix is retained and
its correction is absorbed by the proved local conductor budget. This
is the combined analytic interface for the remaining numerical inequality. -/
theorem gamma_jacobi_zeroMass_add_ambient_ramp_le_integer_prefix_dual {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis bridge.character) {b : ℝ}
    (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p (4 * n) → bridge.character p = 1)
    (hlarge : 10 ^ 100 ≤ n) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor bridge.character.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        (∑ p ∈ (4 * n).primeFactors,
          Real.log p *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (bridge.character p)
                  ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) *
                    (logDeriv bridge.character.gammaFactor
                        (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
          2 * (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) +
        (3 / 4 : ℝ) +
        gammaRefinedSignedDualBudget (Real.log n) := by
  have hf : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (gamma_jacobi_modulus_eq_discriminant bridge).symm ▸ bridge.discriminant_pos
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor := ⟨hf.ne'⟩
  have hq : 2 ≤ (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (Nat.succ_le_iff.mpr bridge.squarefreePart_gt_one).trans
      (Nat.le_of_dvd hf (gamma_jacobi_modulus_squarefree_data bridge).1)
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_le_signed_prefix hq hRH
      bridge.character_primitive bridge.character_ne_one
      (by
        rw [bridge.character_quadratic.inv]; exact bridge.character_ne_one)
      (Finset.Ioc 0 ⌊b⌋₊)
  have hl := gamma_jacobi_integer_prefix_local_budget bridge hb hone hlarge
  dsimp only [gammaRefinedSignedDualBudget]
  linarith only [hz, hl]

/-- Under individual RH and absence of negative Jacobi prime witnesses
up to b, the actual primitive zero mass and ambient ramp satisfy the
finite dual comparison with the original integer prefix. The witness
transfer excludes no square-part or ramified losses. The remaining
comparison is purely numerical in the logarithmic scale and prefix cutoff. -/
theorem gamma_jacobi_no_negative_zeroMass_add_ramp_le_prefix_dual {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis bridge.character) {b : ℝ}
    (hb : 1 ≤ b) (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ b → jacobiSym n p ≠ -1)
    (hlarge : 10 ^ 100 ≤ n) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor bridge.character.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        (∑ p ∈ (4 * n).primeFactors,
          Real.log p *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (bridge.character p)
                  ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) *
                    (logDeriv bridge.character.gammaFactor
                        (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
          2 * (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) +
        (3 / 4 : ℝ) +
        gammaRefinedSignedDualBudget (Real.log n) := by
  exact
    gamma_jacobi_zeroMass_add_ambient_ramp_le_integer_prefix_dual bridge hRH hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge hno) hlarge

end PseudoPrime.LLS
