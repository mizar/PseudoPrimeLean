/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.PartialFamilyEnvelopes
public import PseudoPrime.NumberTheory.CharacterKernelPowers

/-! # Exact conductor costs for cyclic endpoint families

Enumerate the actual finite character families used by the LLS bounds. The chosen small
orders and their analytic consumers remain here; the arbitrary-order conductor identity
is supplied separately by the general character foundation.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The kernel conductor cost is the sum of logs over powers below the character order.
Input: a character at nonzero level. Remove the principal term, whose log conductor is zero,
and use the finite cyclic annihilator enumeration. This supplies exact endpoint costs. -/
theorem kernel_conductor_sum_powers {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    subgroupConductorLogSum χ.toUnitHom.ker =
      ∑ i : Fin (orderOf χ), Real.log (χ ^ (i : ℕ)).conductor := by
  classical
  rw [subgroupConductorLogSum, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Subgroup.coe_one, DirichletCharacter.conductor_one, Nat.cast_one, Real.log_one,
    sub_zero]
  exact NumberTheory.sum_kernel_characters χ (fun ψ ↦ Real.log ψ.conductor)

/-- An order-four kernel has conductor cost twice the generator log plus its square log.
Input: a character of order four. Its third power has the same conductor as the generator.
Enumerate the four powers and collect terms. This supplies the cyclic-four full-family cost. -/
theorem four_kernel_conductor_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 4) :
    subgroupConductorLogSum χ.toUnitHom.ker =
      2 * Real.log χ.conductor + Real.log (χ ^ 2).conductor := by
  have hc : (χ ^ 3).conductor = χ.conductor :=
    NumberTheory.conductor_pow_coprime χ (ho.symm ▸ (by norm_num only : Nat.Coprime 3 4))
  rw [kernel_conductor_sum_powers,
    Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ Real.log (χ ^ k).conductor) (orderOf χ), ho]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, hc,
    DirichletCharacter.conductor_one, Nat.cast_one, Real.log_one, zero_add, add_zero]
  ring

/-- An order-five kernel has conductor cost four times the generator log conductor.
Input: a character of order five. Every nonprincipal exponent is coprime to five, hence
preserves the conductor. Enumerate the powers for the cyclic-five analytic radius. -/
theorem five_kernel_conductor_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 5) : subgroupConductorLogSum χ.toUnitHom.ker = 4 * Real.log χ.conductor := by
  have h2 := NumberTheory.conductor_pow_coprime χ (ho.symm ▸ (by norm_num only : Nat.Coprime 2 5))
  have h3 := NumberTheory.conductor_pow_coprime χ (ho.symm ▸ (by norm_num only : Nat.Coprime 3 5))
  have h4 := NumberTheory.conductor_pow_coprime χ (ho.symm ▸ (by norm_num only : Nat.Coprime 4 5))
  rw [kernel_conductor_sum_powers,
    Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ Real.log (χ ^ k).conductor) (orderOf χ), ho]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, h2, h3, h4,
    DirichletCharacter.conductor_one, Nat.cast_one, Real.log_one, zero_add, add_zero]
  ring

/-- An order-six kernel has the exact quadratic, cubic and generator conductor costs.
Input: a character of order six. Coprime powers identify the conjugate pair costs; enumerate
all six powers. This supplies the full-family endpoint alongside its quadratic and cubic parts. -/
theorem six_kernel_conductor_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 6) :
    subgroupConductorLogSum χ.toUnitHom.ker =
      2 * Real.log χ.conductor + 2 * Real.log (χ ^ 2).conductor + Real.log (χ ^ 3).conductor := by
  have ho2 : orderOf (χ ^ 2) = 3 := by
    rw [orderOf_pow, ho]; norm_num only
  have h4 : (χ ^ 4).conductor = (χ ^ 2).conductor :=
    (congrArg DirichletCharacter.conductor (pow_mul χ 2 2)).trans
      (NumberTheory.conductor_pow_coprime (χ ^ 2) (ho2.symm ▸ (by norm_num only : Nat.Coprime 2 3)))
  have h5 := NumberTheory.conductor_pow_coprime χ (ho.symm ▸ (by norm_num only : Nat.Coprime 5 6))
  rw [kernel_conductor_sum_powers,
    Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ Real.log (χ ^ k).conductor) (orderOf χ), ho]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, h4, h5,
    DirichletCharacter.conductor_one, Nat.cast_one, Real.log_one, zero_add, add_zero]
  ring

/-- The unit kernel of a character lies in the kernel of every natural power.
Input: a character and exponent. Powers stay in its kernel annihilator; apply finite duality.
This provides the partial-family supergroups at the original ambient modulus. -/
theorem kernel_le_power_kernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) :
    χ.toUnitHom.ker ≤ (χ ^ k).toUnitHom.ker :=
  NumberTheory.le_kernel_of_annihilator _ _
    ((NumberTheory.kernel_annihilator_zpowers χ).symm ▸
      (Subgroup.zpowers χ).pow_mem (Subgroup.mem_zpowers χ) k)

/-- Under GRH, an order-five character gives an actual least outside-prime conductor bound.
Input: GRH and a positive ambient allowance. Substitute the exact four-character cost into
the certified index-five radius. The threshold is uniform and no scalar gap is assumed. -/
theorem cyclic_five_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ χ : DirichletCharacter ℂ q,
              orderOf χ = 5 →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q χ.toUnitHom.ker) p ∧
                    (p : ℝ) ≤
                      (Real.sqrt (23 / 40) / ((5 : ℝ) - 1) * (4 * Real.log χ.conductor) +
                          ε * Real.log q) ^
                        2 :=
  Exists.elim (rationalPole_index_five_conductor hg hε) fun Q hQ ↦
    ⟨Q, hQ.1, fun q _ hq χ ho ↦
      five_kernel_conductor_sum χ ho ▸
        hQ.2 q hq χ.toUnitHom.ker ((NumberTheory.index_kernel_eq_order χ).trans ho)⟩

/-- Under GRH, an order-four kernel satisfies a quadratic/full-family minimum.
Input: GRH and positive allowance at the ambient modulus. The square is quadratic, its
kernel contains the original kernel, and the full cost is explicitly enumerated.
Identify actual least primes to obtain both bounds without a supplied scalar gap. -/
theorem cyclic_four_min_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ χ : DirichletCharacter ℂ q,
              orderOf χ = 4 →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q χ.toUnitHom.ker) p ∧
                    (p : ℝ) ≤
                      min
                        ((Real.sqrt (777 / 1000) * Real.log (χ ^ 2).conductor + ε * Real.log q) ^ 2)
                        ((Real.sqrt (623 / 1000) / ((4 : ℝ) - 1) *
                              (2 * Real.log χ.conductor + Real.log (χ ^ 2).conductor) +
                            ε * Real.log q) ^
                          2) :=
  Exists.elim (quadratic_full_min_radius hg hε) fun Q hQ ↦
    ⟨Q, hQ.1, fun q _ hq χ ho ↦
      four_kernel_conductor_sum χ ho ▸
        hQ.2 q hq χ.toUnitHom.ker (χ ^ 2) ((NumberTheory.index_kernel_eq_order χ).trans ho)
          ((orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 2) ho))
          (kernel_le_power_kernel χ 2)⟩

/-- Under GRH, an order-six kernel satisfies a quadratic/cubic/full-family minimum.
Input: GRH and positive ambient allowance. Its cube and square give the partial supergroups.
Substitute all exact conductor costs into the same-modulus least-prime envelope.
The uniform existential threshold and actual least certificate are preserved. -/
theorem cyclic_six_min_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ χ : DirichletCharacter ℂ q,
              orderOf χ = 6 →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q χ.toUnitHom.ker) p ∧
                    (p : ℝ) ≤
                      min
                        ((Real.sqrt (777 / 1000) / ((2 : ℝ) - 1) * Real.log (χ ^ 3).conductor +
                            ε * Real.log q) ^
                          2)
                        (min
                          ((Real.sqrt (7 / 10) / ((3 : ℝ) - 1) * (2 * Real.log (χ ^ 2).conductor) +
                              ε * Real.log q) ^
                            2)
                          ((Real.sqrt (549 / 1000) / ((6 : ℝ) - 1) *
                                (2 * Real.log χ.conductor + 2 * Real.log (χ ^ 2).conductor +
                                  Real.log (χ ^ 3).conductor) +
                              ε * Real.log q) ^
                            2)) :=
  Exists.elim (cubic_quadratic_full_radius hg hε) fun Q hQ ↦
    ⟨Q, hQ.1, fun q _ hq χ ho ↦
      let ho2 : orderOf (χ ^ 2) = 3 :=
        (orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 2) ho)
      let ho3 : orderOf (χ ^ 3) = 2 :=
        (orderOf_pow χ).trans (congrArg (fun n : ℕ ↦ n / Nat.gcd n 3) ho)
      six_kernel_conductor_sum χ ho ▸
        cubic_kernel_conductor_sum (χ ^ 2) ho2 ▸
        quadratic_kernel_conductor_sum (χ ^ 3) ho3 ▸
        hQ.2 q hq χ.toUnitHom.ker (χ ^ 3).toUnitHom.ker (χ ^ 2).toUnitHom.ker
          ((NumberTheory.index_kernel_eq_order χ).trans ho)
          ((NumberTheory.index_kernel_eq_order (χ ^ 3)).trans ho3)
          ((NumberTheory.index_kernel_eq_order (χ ^ 2)).trans ho2) (kernel_le_power_kernel χ 3)
          (kernel_le_power_kernel χ 2)⟩

/-- Every index-six subgroup has the explicit cyclic quadratic/cubic/full least-prime envelope.
Input: GRH, positive ambient allowance and an arbitrary index-six subgroup. Extract a generator
from its annihilator using the coprime-prime index theorem, then transport the actual least
certificate along the kernel equality. No CRT decomposition is assumed. -/
theorem index_six_min_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ H : Subgroup (ZMod q)ˣ,
              H.index = 6 →
                ∃ χ : DirichletCharacter ℂ q,
                  orderOf χ = 6 ∧
                    H = χ.toUnitHom.ker ∧
                    ∃ p : ℕ,
                      IsLeast (NumberTheory.primesOutside q H) p ∧
                        (p : ℝ) ≤
                          min
                            ((Real.sqrt (777 / 1000) / ((2 : ℝ) - 1) * Real.log (χ ^ 3).conductor +
                                ε * Real.log q) ^
                              2)
                            (min
                              ((Real.sqrt (7 / 10) / ((3 : ℝ) - 1) *
                                    (2 * Real.log (χ ^ 2).conductor) +
                                  ε * Real.log q) ^
                                2)
                              ((Real.sqrt (549 / 1000) / ((6 : ℝ) - 1) *
                                    (2 * Real.log χ.conductor + 2 * Real.log (χ ^ 2).conductor +
                                      Real.log (χ ^ 3).conductor) +
                                  ε * Real.log q) ^
                                2)) :=
  Exists.elim (cyclic_six_min_radius hg hε) fun Q hQ ↦
    ⟨Q, hQ.1, fun q _ hq H hi ↦
      Exists.elim (NumberTheory.coprime_prime_index_kernel H (show Nat.Coprime 2 3 from rfl) hi)
        fun χ hχ ↦ ⟨χ, hχ.1, hχ.2, hχ.2.symm ▸ hQ.2 q hq χ hχ.1⟩⟩

/-- Every index-five subgroup has an actual least-prime radius with a generating conductor.
Input: GRH, positive ambient allowance and an arbitrary index-five subgroup. Extract its
prime-order annihilator generator and transport the cyclic radius along the kernel equality.
The threshold remains uniform over all subgroups and generators. -/
theorem index_five_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ H : Subgroup (ZMod q)ˣ,
              H.index = 5 →
                ∃ χ : DirichletCharacter ℂ q,
                  orderOf χ = 5 ∧
                    H = χ.toUnitHom.ker ∧
                    ∃ p : ℕ,
                      IsLeast (NumberTheory.primesOutside q H) p ∧
                        (p : ℝ) ≤
                          (Real.sqrt (23 / 40) / ((5 : ℝ) - 1) * (4 * Real.log χ.conductor) +
                              ε * Real.log q) ^
                            2 :=
  Exists.elim (cyclic_five_radius hg hε) fun Q hQ ↦
    ⟨Q, hQ.1, fun q _ hq H hi ↦
      Exists.elim (@NumberTheory.prime_index_kernel q _ H 5 ⟨Nat.prime_five⟩ hi) fun χ hχ ↦
        ⟨χ, hχ.1, hχ.2, hχ.2.symm ▸ hQ.2 q hq χ hχ.1⟩⟩

end PseudoPrime.LLS.PaperStatements
