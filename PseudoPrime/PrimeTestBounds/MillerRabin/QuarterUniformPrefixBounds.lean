/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFirstBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformGammaPrefix
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedPrefixRange

/-! # Uniform triple bounds with reflected prefix savings -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A finite reflected prefix and the first Gamma-pole correction improve
the certified witness budget for a specified uniform Korselt triple. -/
theorem quarter_uniform_cell_prefix {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X U S P F H : ℝ} (hX : 1 ≤ X)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (t : Finset ℕ)
    (ht : ∀ k ∈ t, (k : ℝ) ≤ X) (hU : Real.log n ≤ U) (hcut : X ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hS :
      S ≤
        ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re)
    (hP : P ≤ ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k)
    (hF : (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re ≤ F)
    (hcert :
      quarterUniformBudget X U P F H - 3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
          4 * ∑ k ∈ t, refinedDualWeight X k ≤
        4 * S) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hc :
    0 ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * X ^ (-(27 / 25 : ℝ)) *
        ((21 / 8 : ℝ) + Real.log X) ^ 5) := by
    positivity
  have hm := mul_le_mul_of_nonneg_right (show 2 * Real.log n ≤ 2 * U by linarith only [hU]) hc
  have hfirst :=
    quarter_uniform_witness_prefix hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK
      hrK hvq hvr hX hH t ht
  have hw : ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    apply hfirst
    dsimp only [quarterUniformBudget] at hcert
    linarith only [hm, hU, hP, hF, hS, hcert]
  obtain ⟨l, hl, hlX, hf⟩ := hw
  exact ⟨l, hl, hlX.trans hcut, hf⟩

/-- The corrected finite budget yields a quarter-square witness for any
uniform Korselt triple. Extract its three distinct odd prime factors. -/
theorem quarter_uniform_bounds_prefix {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {X U S P F H : ℝ} (hX : 1 ≤ X) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (hU : Real.log n ≤ U) (t : Finset ℕ) (ht : ∀ k ∈ t, (k : ℝ) ≤ X)
    (hcut : X ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hS :
      S ≤
        ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re)
    (hP : P ≤ ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k)
    (hF : (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re ≤ F)
    (hcert :
      quarterUniformBudget X U P F H - 3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
          4 * ∑ k ∈ t, refinedDualWeight X k ≤
        4 * S) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hu.2.1
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpD := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqD := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrD := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hu.1).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 : p ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hpO)
  have hq2 : q ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hqO)
  have hr2 : r ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hrO)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  have hpqD : p * q ∣ n := ⟨r, hnprod⟩
  have hprD : p * r ∣ n := ⟨q, hnprod.trans (by ac_rfl)⟩
  have hqrD : q * r ∣ n := ⟨p, hnprod.trans (by ac_rfl)⟩
  exact
    quarter_uniform_cell_prefix hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hX hH t ht hU hcut hS hP hF hcert

/-- The centered principal-sum estimate gives a quarter-square witness
when the budget retains the reflected finite prefix and first Gamma pole. -/
theorem quarter_uniform_centered_prefix {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r H : ℝ} (hr : 180 ≤ r) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) (r ^ 2) ≤ H)
    (hU : Real.log n ≤ 2 * r) (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hcert :
      (4 * r) *
                  (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                    (r ^ 2) ^ (-(27 / 25 : ℝ)) *
                    ((21 / 8 : ℝ) + Real.log (r ^ 2)) ^ 5) +
                (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
              3 * quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) -
              4 * ∑ k ∈ Finset.Ioc 0 2701, refinedDualWeight (r ^ 2) k +
            H +
            (3 / 8 : ℝ) * (2 * r) +
            (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
          4 *
            ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
              ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k ≤
        (27 / 25 : ℝ) ^ 5 *
            ((24439 / 50000 : ℝ) * r - (108 / 1000 : ℝ) * Real.sqrt r - (6695 / 100000 : ℝ) -
              (29757 / 10000 : ℝ) / r -
              (526064 / 10000000 : ℝ) / Real.sqrt r) -
          3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have ht : ∀ k ∈ Finset.Ioc (0 : ℕ) 2701, (k : ℝ) ≤ r ^ 2 := by
    intro k hk
    have hk' : k ≤ 2701 := (Finset.mem_Ioc.mp hk).2
    have hkr : (k : ℝ) ≤ 2701 := by exact_mod_cast hk'
    nlinarith only [hkr, hr]
  let S : ℝ :=
    ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
      (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re
  let P : ℝ :=
    ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k
  let F : ℝ := (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re
  have hcenter := refined_combined_centered_numeric hGRH.riemann (by linarith only [hr])
  have hb :
    quarterUniformBudget (r ^ 2) (2 * r) P F H -
        3 * quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) -
        4 * ∑ k ∈ Finset.Ioc 0 2701, refinedDualWeight (r ^ 2) k ≤
      4 * S := by
    dsimp only [quarterUniformBudget, S, P, F]
    linarith only [hcert, hcenter]
  exact
    quarter_uniform_bounds_prefix hn ho hu hGRH hr2 hH hU (Finset.Ioc 0 2701) ht hcut le_rfl le_rfl
      le_rfl hb

/-- On radii 180 through 200 the two certified corrections improve the
scalar residual budget and yield a quarter-square witness. -/
theorem quarter_uniform_residual_prefix {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r P : ℝ} (hr : 180 ≤ r) (hR : r ≤ 200) (hU : Real.log n ≤ 2 * r)
    (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hP :
      P ≤ ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k)
    (hgap :
      quarterCenteredResidual r - 4 * (P - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) - 57 / 500 -
          7 / 250 ≤
        (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
          (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) (r ^ 2) ≤ quarterMomentScale r := by
    exact
      quarter_reflected_of_moments hr2
        (quarter_moment_bounds_of_integrals hGRH.riemann quarter_moment_integral_bounds)
  have hk : 0 ≤ quarterReflectedScale r := by
    dsimp only [quarterReflectedScale]
    have hl : 0 ≤ Real.log (r ^ 2) := Real.log_nonneg hr2
    positivity
  have he :=
    mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le
      (show (0 : ℝ) ≤ 3 * quarterReflectedScale r by positivity)
  have hfirst := quarter_first_correction_180_200 hr hR
  have hprefix := quarter_reflected_prefix_180_200 hr hR
  apply quarter_uniform_centered_prefix hn ho hu hGRH hr hH hU hcut
  have hw :
    3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r =
      3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
    rw [mul_div_assoc, quarter_reflected_scale_eq hr0]
  rw [hw]
  dsimp only [quarterCenteredResidual] at hgap
  change
    (4 * r) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
            3 * quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) -
            4 * ∑ k ∈ Finset.Ioc 0 2701, refinedDualWeight (r ^ 2) k +
          quarterMomentScale r +
          (3 / 8 : ℝ) * (2 * r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k ≤
      _
  ring_nf at hgap hP he hfirst hprefix ⊢
  linarith only [hgap, hP, he, hfirst, hprefix]

end PseudoPrime.PrimeTestBounds.MillerRabin
