/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositeMangoldtSqrtBound
public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionCounting
public import PseudoPrime.AnalyticNumberTheory.AGP.BrunTitchmarshSpecialization
public import PseudoPrime.AnalyticNumberTheory.AGP.ExceptionalModuli
public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionCountData

/-! # ProgressionTheta

Weighted prime sums in arithmetic progressions and their finite counting bounds.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Purpose: sum the logarithmic weights of primes up to `y` in one residue class.

Definition: filter `0, ..., y` by primality and the congruence `p ≡ a mod q`,
then sum `Real.log p` over the resulting finite set.

Inputs: a cutoff `y`, modulus `q`, and residue `a`.

Output: the Chebyshev theta sum for this finite progression segment.

Role: this weighted count is the finite endpoint for converting analytic theta
lower bounds into prime-count lower bounds.
-/
noncomputable def thetaInProgression (y q a : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % q = a % q), Real.log (p : ℝ)

/--
Inputs: a cutoff `y`, modulus `q`, and residue `a`.

Claim: the theta sum is at most the progression prime count times `log y`.

Proof: each prime in the sum is at most `y`, so monotonicity of the logarithm
bounds every summand by `log y`; summing the constant gives the stated count.

Role: this converts lower bounds for weighted progression sums into lower
bounds for `primeCountInProgression` without partial summation.
-/
theorem thetaInProgression_le_primeCount_mul_log (y q a : ℕ) :
    thetaInProgression y q a ≤ (primeCountInProgression y q a : ℝ) * Real.log (y : ℝ) := by
  classical
  let P : Finset ℕ := (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % q = a % q)
  have hpoint (p : ℕ) (hp : p ∈ P) : Real.log (p : ℝ) ≤ Real.log (y : ℝ) := by
    have hmem := Finset.mem_filter.mp hp
    have hpPrime := hmem.2.1
    have hple : p ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem.1)
    exact Real.log_le_log (by exact_mod_cast hpPrime.pos) (by exact_mod_cast hple)
  change (∑ p ∈ P, Real.log (p : ℝ)) ≤ (P.card : ℝ) * Real.log (y : ℝ)
  calc
    (∑ p ∈ P, Real.log (p : ℝ)) ≤ ∑ p ∈ P, Real.log (y : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpoint p hp
    _ = (P.card : ℝ) * Real.log (y : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul]

/--
Inputs: a cutoff `y ≥ 2`, a modulus and residue, and a real lower bound for the theta sum.

Claim: dividing that lower bound by `log y` gives a lower bound for the progression prime count.

Proof: combine `thetaInProgression_le_primeCount_mul_log` with positivity of `log y`.

Role: this is the finite conversion used after a weighted arithmetic-progression estimate.
-/
theorem primeCountInProgression_ge_div_log_of_theta_lower (y q a : ℕ) (hy : 2 ≤ y) (u : ℝ)
    (hu : u ≤ thetaInProgression y q a) :
    u / Real.log (y : ℝ) ≤ (primeCountInProgression y q a : ℝ) := by
  have h1y : 1 < y := lt_of_lt_of_le (by norm_num only : 1 < 2) hy
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast h1y)
  have htotal := hu.trans (thetaInProgression_le_primeCount_mul_log y q a)
  exact (div_le_iff₀ hlog).2 htotal

/--
Purpose: sum von Mangoldt weights on nonprime integers in one arithmetic progression.

Definition: filter the positive integers up to `floor y` by nonprimality and the
congruence `n ≡ a mod q`, then sum `vonMangoldt n`.

Inputs: a real cutoff `y`, modulus `q`, and residue `a`.

Output: the higher-prime-power contribution to the progression-restricted psi sum.

Role: this isolates the terms that must be removed when converting a weighted
progression estimate into a theta estimate.
-/
noncomputable def higherPrimePowerMassInProgression (y : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ ((Finset.Ioc 0 ⌊y⌋₊).filter (fun n => n % q = a % q)).filter (fun n => ¬Nat.Prime n),
    ArithmeticFunction.vonMangoldt n

/--
Purpose: sum all von Mangoldt weights in a residue class through a real cutoff.

Definition: filter the positive integers through `floor y` by the congruence
`n ≡ a mod q`, then sum `vonMangoldt n`.

Inputs: a real cutoff `y`, modulus `q`, and residue `a`.

Output: the finite progression-restricted Chebyshev psi sum.

Role: this is the weighted progression count decomposed into its prime and
higher-prime-power contributions.
-/
noncomputable def psiInProgression (y : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n

/--
Purpose: sum logarithmic prime weights in a residue class through a real cutoff.

Definition: restrict `Ioc 0 floor y` to primes congruent to `a modulo q` and
sum `log p`.

Inputs: a real cutoff `y`, modulus `q`, and residue `a`.

Output: the finite progression-restricted Chebyshev theta sum.

Role: this is the prime contribution in the exact decomposition of
`psiInProgression`.
-/
noncomputable def thetaInProgressionReal (y : ℝ) (q a : ℕ) : ℝ :=
  ∑ p ∈ ((Finset.Ioc 0 ⌊y⌋₊).filter (fun p => p % q = a % q)).filter Nat.Prime, Real.log (p : ℝ)

/--
Inputs: a real cutoff `y`, a modulus `q`, and a residue `a`.

Claim: the progression psi sum equals its prime theta sum plus its higher-prime-power mass.

Proof: partition the progression support by primality and use the von Mangoldt
value `log p` on primes.

Role: this exact identity transfers weighted progression estimates to the theta
sum before applying the `18 * sqrt y` error bound.
-/
theorem psiInProgression_eq_theta_add_higherPrimePowerMass (y : ℝ) (q a : ℕ) :
    psiInProgression y q a =
      thetaInProgressionReal y q a + higherPrimePowerMassInProgression y q a := by
  classical
  let B := (Finset.Ioc 0 ⌊y⌋₊).filter (fun n => n % q = a % q)
  have hprime :
    (∑ p ∈ B.filter Nat.Prime, ArithmeticFunction.vonMangoldt p) =
      thetaInProgressionReal y q a := by
    apply Finset.sum_congr rfl
    intro p hp
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := B) (p := Nat.Prime) (f := fun n =>
      ArithmeticFunction.vonMangoldt n)
  rw [hprime] at hsplit
  simpa only [psiInProgression, thetaInProgressionReal, higherPrimePowerMassInProgression, B] using
    hsplit.symm

/--
Inputs: a real cutoff `y ≥ 1`, a modulus `q`, and a residue `a`.

Claim: the higher-prime-power mass in one progression is nonnegative and at
most the full `psi y - theta y` defect, hence at most `18 * sqrt y`.

Proof: compare its filtered sum with the full nonprime Mangoldt sum using
nonnegativity, then apply the unconditional Chebyshev defect estimate.

Role: this supplies the uniform error term for converting progression psi
estimates to theta estimates.
-/
theorem higherPrimePowerMassInProgression_bounds (y : ℝ) (q a : ℕ) (hy : 1 ≤ y) :
    0 ≤ higherPrimePowerMassInProgression y q a ∧
      higherPrimePowerMassInProgression y q a ≤ 18 * Real.sqrt y := by
  classical
  let S := (Finset.Ioc 0 ⌊y⌋₊).filter (fun n => ¬Nat.Prime n)
  let P := ((Finset.Ioc 0 ⌊y⌋₊).filter (fun n => n % q = a % q)).filter (fun n => ¬Nat.Prime n)
  change
    0 ≤ (∑ n ∈ P, ArithmeticFunction.vonMangoldt n) ∧
      (∑ n ∈ P, ArithmeticFunction.vonMangoldt n) ≤ 18 * Real.sqrt y
  constructor
  · exact Finset.sum_nonneg (fun n hn => ArithmeticFunction.vonMangoldt_nonneg)
  · have hsub : P ⊆ S := by
      intro n hn
      have hmem := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmem.1).1, hmem.2⟩
    have hsum :=
      Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => ArithmeticFunction.vonMangoldt n)
        hsub (fun n hn _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hwhole := PseudoPrime.AnalyticNumberTheory.Arithmetic.psi_sub_theta_le_eighteen_sqrt hy
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime] at hwhole
    simpa only [S] using le_trans hsum hwhole

/--
Inputs: a real cutoff `y ≥ 1`, modulus `q`, and residue `a`.

Claim: the difference between the progression psi sum and theta sum is
nonnegative and at most `18 * sqrt y`.

Proof: use the exact prime/nonprime decomposition and the bound on the
higher-prime-power mass.

Role: this is the progression-restricted psi-to-theta error estimate.
-/
theorem psi_sub_thetaInProgression_bounds (y : ℝ) (q a : ℕ) (hy : 1 ≤ y) :
    0 ≤ psiInProgression y q a - thetaInProgressionReal y q a ∧
      psiInProgression y q a - thetaInProgressionReal y q a ≤ 18 * Real.sqrt y := by
  have hmass := higherPrimePowerMassInProgression_bounds y q a hy
  rw [psiInProgression_eq_theta_add_higherPrimePowerMass]
  simpa only [add_sub_cancel_left] using hmass

/--
Inputs: a natural cutoff `y`, modulus `q`, and residue `a`.

Claim: the real-cutoff theta sum at `y` agrees with the natural-cutoff theta sum.

Proof: the prime filters on `Ioc 0 y` and `range (y + 1)` have the same elements.

Role: this connects the exact psi decomposition to the finite theta-to-count estimate.
-/
theorem thetaInProgressionReal_natCast (y q a : ℕ) :
    thetaInProgressionReal (y : ℝ) q a = thetaInProgression y q a := by
  classical
  unfold thetaInProgressionReal thetaInProgression
  have hset :
    ((Finset.Ioc 0 ⌊(y : ℝ)⌋₊).filter (fun p => p % q = a % q)).filter Nat.Prime =
      (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % q = a % q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range, Nat.floor_natCast]
    constructor
    · rintro ⟨⟨⟨_, hpLe⟩, hcong⟩, hp⟩
      exact ⟨Nat.lt_succ_iff.mpr hpLe, hp, hcong⟩
    · rintro ⟨hpRange, hp, hcong⟩
      exact ⟨⟨⟨hp.pos, Nat.lt_succ_iff.mp hpRange⟩, hcong⟩, hp⟩
  rw [hset]

/--
Inputs: a natural cutoff `y ≥ 2`, modulus `q`, residue `a`, and a real lower
bound for the progression psi sum.

Claim: subtracting `18 * sqrt y` and dividing by `log y` gives a lower bound
for the progression prime count.

Proof: remove the higher-prime-power contribution with
`psi_sub_thetaInProgression_bounds`, identify the real and natural theta sums,
then apply the finite theta-to-count conversion.

Role: this is the direct finite conversion from a weighted progression lower
bound to an unweighted prime-count lower bound.
-/
theorem primeCountInProgression_ge_div_log_of_psi_lower (y q a : ℕ) (hy : 2 ≤ y) (u : ℝ)
    (hu : u ≤ psiInProgression (y : ℝ) q a) :
    (u - 18 * Real.sqrt (y : ℝ)) / Real.log (y : ℝ) ≤ (primeCountInProgression y q a : ℝ) := by
  have hyReal : 1 ≤ (y : ℝ) := by exact_mod_cast le_trans (by norm_num only : 1 ≤ 2) hy
  have hmass := higherPrimePowerMassInProgression_bounds (y : ℝ) q a hyReal
  have hdecomp := psiInProgression_eq_theta_add_higherPrimePowerMass (y : ℝ) q a
  rw [hdecomp] at hu
  have htheta : u - 18 * Real.sqrt (y : ℝ) ≤ thetaInProgressionReal (y : ℝ) q a := by
    linarith only [hu, hmass.2]
  have hthetaNat : u - 18 * Real.sqrt (y : ℝ) ≤ thetaInProgression y q a := by
    rw [← thetaInProgressionReal_natCast y q a]
    exact htheta
  exact primeCountInProgression_ge_div_log_of_theta_lower y q a hy _ hthetaNat

/--
Inputs: a real cutoff `y ≥ 1`, a modulus `q`, and a residue `a`.

Claim: the theta sum over primes in the progression is at most its psi sum.

Proof: decompose the psi sum into the prime theta sum and the nonnegative
higher-prime-power contribution.

Role: this transfers a weighted theta lower bound to the psi interface used by
the finite prime-count conversion.
-/
theorem thetaInProgressionReal_le_psiInProgression (y : ℝ) (q a : ℕ) (hy : 1 ≤ y) :
    thetaInProgressionReal y q a ≤ psiInProgression y q a := by
  rw [psiInProgression_eq_theta_add_higherPrimePowerMass]
  exact le_add_of_nonneg_right (higherPrimePowerMassInProgression_bounds y q a hy).1

/--
Inputs: a natural cutoff `y ≥ 2`, a positive modulus `q`, a residue `a`, and
a theta lower bound of half the expected main term.

Claim: if `72 * φ(q) * sqrt y ≤ y`, then the progression prime count is at
least `y / (4 * φ(q) * log y)`.

Proof: use the `18 * sqrt y` psi-theta defect bound and divide by the positive
logarithm after absorbing that defect into one quarter of the main term.

Role: this is the finite conversion needed after the weighted estimate in
paper95 Theorem 2.1 is specialized to an admissible progression.
-/
theorem primeCountInProgression_ge_main_term_of_theta_lower (y q a : ℕ) (hy : 2 ≤ y) (hq : 0 < q)
    (herror : 72 * (Nat.totient q : ℝ) * Real.sqrt (y : ℝ) ≤ (y : ℝ))
    (htheta : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ thetaInProgressionReal (y : ℝ) q a) :
    ((y : ℝ) / (4 * (Nat.totient q : ℝ))) / Real.log (y : ℝ) ≤
      (primeCountInProgression y q a : ℝ) := by
  have hphi : 0 < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hy))
  have hden : 0 < (4 : ℝ) * (Nat.totient q : ℝ) := mul_pos (by norm_num only) hphi
  have hsmall : 18 * Real.sqrt (y : ℝ) ≤ (y : ℝ) / (4 * (Nat.totient q : ℝ)) := by
    apply (le_div_iff₀ hden).2
    nlinarith only [herror]
  have hhalf : (y : ℝ) / (2 * (Nat.totient q : ℝ)) = 2 * ((y : ℝ) / (4 * (Nat.totient q : ℝ))) := by
    field_simp [ne_of_gt hphi]
    ring
  have hmain :
    (y : ℝ) / (4 * (Nat.totient q : ℝ)) ≤
      (y : ℝ) / (2 * (Nat.totient q : ℝ)) - 18 * Real.sqrt (y : ℝ) := by
    rw [hhalf]
    linarith only [hsmall]
  have hyReal : 1 ≤ (y : ℝ) := by exact_mod_cast (le_trans (by norm_num only : 1 ≤ 2) hy)
  have hpsi : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ psiInProgression (y : ℝ) q a :=
    le_trans htheta (thetaInProgressionReal_le_psiInProgression (y : ℝ) q a hyReal)
  calc
    ((y : ℝ) / (4 * (Nat.totient q : ℝ))) / Real.log (y : ℝ) ≤
        ((y : ℝ) / (2 * (Nat.totient q : ℝ)) - 18 * Real.sqrt (y : ℝ)) / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_right hmain (le_of_lt hlog)
    _ ≤ (primeCountInProgression y q a : ℝ) :=
      primeCountInProgression_ge_div_log_of_psi_lower y q a hy _ hpsi

/-
Inputs: a natural cutoff `y ≥ 2`, a positive modulus `q`, a residue `a`, and
a theta lower bound of half the expected main term. The stronger error bound
`108 * φ(q) * sqrt y ≤ y` is also assumed.

Claim: the progression prime count is at least `y / (3 * φ(q) * log y)`.

Proof: the stronger bound absorbs the `18 * sqrt y` psi-theta defect into
one sixth of the main term, leaving one third before division by the logarithm.

Role: this sharper finite conversion improves the coefficient in the AGP
finite average.
-/
theorem primeCountInProgression_ge_one_third_main_term_of_theta_lower (y q a : ℕ) (hy : 2 ≤ y)
    (hq : 0 < q) (herror : 108 * (Nat.totient q : ℝ) * Real.sqrt (y : ℝ) ≤ (y : ℝ))
    (htheta : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ thetaInProgressionReal (y : ℝ) q a) :
    ((y : ℝ) / (3 * (Nat.totient q : ℝ))) / Real.log (y : ℝ) ≤
      (primeCountInProgression y q a : ℝ) := by
  have hphi : 0 < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hy))
  have hden : 0 < (6 : ℝ) * (Nat.totient q : ℝ) := mul_pos (by norm_num only) hphi
  have hsmall : 18 * Real.sqrt (y : ℝ) ≤ (y : ℝ) / (6 * (Nat.totient q : ℝ)) := by
    apply (le_div_iff₀ hden).2
    nlinarith only [herror]
  have hhalf : (y : ℝ) / (2 * (Nat.totient q : ℝ)) = 3 * ((y : ℝ) / (6 * (Nat.totient q : ℝ))) := by
    field_simp [ne_of_gt hphi]
    ring
  have hthird :
    (y : ℝ) / (3 * (Nat.totient q : ℝ)) = 2 * ((y : ℝ) / (6 * (Nat.totient q : ℝ))) := by
    field_simp [ne_of_gt hphi]
    ring
  have hmain :
    (y : ℝ) / (3 * (Nat.totient q : ℝ)) ≤
      (y : ℝ) / (2 * (Nat.totient q : ℝ)) - 18 * Real.sqrt (y : ℝ) := by
    rw [hhalf, hthird]
    linarith only [hsmall]
  have hyReal : 1 ≤ (y : ℝ) := by exact_mod_cast (le_trans (by norm_num only : 1 ≤ 2) hy)
  have hpsi : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ psiInProgression (y : ℝ) q a :=
    le_trans htheta (thetaInProgressionReal_le_psiInProgression (y : ℝ) q a hyReal)
  calc
    ((y : ℝ) / (3 * (Nat.totient q : ℝ))) / Real.log (y : ℝ) ≤
        ((y : ℝ) / (2 * (Nat.totient q : ℝ)) - 18 * Real.sqrt (y : ℝ)) / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_right hmain (le_of_lt hlog)
    _ ≤ (primeCountInProgression y q a : ℝ) :=
      primeCountInProgression_ge_div_log_of_psi_lower y q a hy _ hpsi

/-
Inputs: `y ≥ 2`, a positive modulus `q`, a residue `a`, a half-main-term
theta lower bound, and the stronger error condition
`324 * φ(q) * sqrt y ≤ y`.

Claim: the progression prime count is at least four ninths of the main term,
divided by `log y`.

Proof: absorb the `18 * sqrt y` psi-theta defect into one eighteenth of the
main term, then use the existing weighted-count conversion.

Role: this sharpens the fixed-scale input to the AGP finite average.
-/
theorem primeCountInProgression_ge_four_ninths_main_term_of_theta_lower (y q a : ℕ) (hy : 2 ≤ y)
    (hq : 0 < q) (herror : 324 * (Nat.totient q : ℝ) * Real.sqrt (y : ℝ) ≤ (y : ℝ))
    (htheta : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ thetaInProgressionReal (y : ℝ) q a) :
    (4 / 9 : ℝ) * ((y : ℝ) / (Nat.totient q : ℝ)) / Real.log (y : ℝ) ≤
      (primeCountInProgression y q a : ℝ) := by
  have hphi : 0 < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hy))
  have hden : 0 < (18 : ℝ) * (Nat.totient q : ℝ) := mul_pos (by norm_num only) hphi
  have hsmall : 18 * Real.sqrt (y : ℝ) ≤ (y : ℝ) / (18 * (Nat.totient q : ℝ)) := by
    apply (le_div_iff₀ hden).2
    nlinarith only [herror]
  have hunit : (y : ℝ) / (18 * (Nat.totient q : ℝ)) = ((y : ℝ) / (Nat.totient q : ℝ)) / 18 := by
    field_simp [ne_of_gt hphi]
  have hhalf :
    (y : ℝ) / (2 * (Nat.totient q : ℝ)) = 9 * ((y : ℝ) / (18 * (Nat.totient q : ℝ))) := by
    field_simp [ne_of_gt hphi]
    ring
  have hfourNinth :
    (4 / 9 : ℝ) * ((y : ℝ) / (Nat.totient q : ℝ)) = 8 * ((y : ℝ) / (18 * (Nat.totient q : ℝ))) := by
    field_simp [ne_of_gt hphi]
    ring
  have hmain :
    (4 / 9 : ℝ) * ((y : ℝ) / (Nat.totient q : ℝ)) ≤
      (y : ℝ) / (2 * (Nat.totient q : ℝ)) - 18 * Real.sqrt (y : ℝ) := by
    rw [hhalf, hfourNinth]
    linarith only [hsmall]
  have hyReal : 1 ≤ (y : ℝ) := by exact_mod_cast (le_trans (by norm_num only : 1 ≤ 2) hy)
  have hpsi : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ psiInProgression (y : ℝ) q a :=
    le_trans htheta (thetaInProgressionReal_le_psiInProgression (y : ℝ) q a hyReal)
  calc
    (4 / 9 : ℝ) * ((y : ℝ) / (Nat.totient q : ℝ)) / Real.log (y : ℝ) ≤
        ((y : ℝ) / (2 * (Nat.totient q : ℝ)) - 18 * Real.sqrt (y : ℝ)) / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_right hmain (le_of_lt hlog)
    _ ≤ (primeCountInProgression y q a : ℝ) :=
      primeCountInProgression_ge_div_log_of_psi_lower y q a hy _ hpsi

/-
Inputs: `y ≥ 2`, a positive modulus `q`, a residue `a`, a real error fraction
`epsilon`, a half-main-term theta lower bound, and an error bound of
`epsilon * y / φ(q)` for the higher prime powers.

Claim: the progression prime count is at least `(1/2 - epsilon)` times the
main term, divided by `log y`.

Proof: subtract the error bound from the half-main-term theta estimate, then
apply the weighted prime-count conversion.

Role: this parameterized estimate lets the AGP scale use the full strength of
its large-modulus error bound.
-/
theorem primeCountInProgression_ge_half_minus_epsilon_main_term_of_theta_lower (y q a : ℕ)
    (hy : 2 ≤ y) (hq : 0 < q) (epsilon : ℝ)
    (herror : 18 * Real.sqrt (y : ℝ) ≤ epsilon * ((y : ℝ) / (Nat.totient q : ℝ)))
    (htheta : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ thetaInProgressionReal (y : ℝ) q a) :
    ((1 / 2 : ℝ) - epsilon) * ((y : ℝ) / (Nat.totient q : ℝ)) / Real.log (y : ℝ) ≤
      (primeCountInProgression y q a : ℝ) := by
  have hphi : 0 < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hy))
  have hhalf :
    (y : ℝ) / (2 * (Nat.totient q : ℝ)) = (1 / 2 : ℝ) * ((y : ℝ) / (Nat.totient q : ℝ)) := by
    field_simp [ne_of_gt hphi]
  have hmain :
    ((1 / 2 : ℝ) - epsilon) * ((y : ℝ) / (Nat.totient q : ℝ)) ≤
      (y : ℝ) / (2 * (Nat.totient q : ℝ)) - 18 * Real.sqrt (y : ℝ) := by
    rw [hhalf]
    linarith only [herror]
  have hyReal : 1 ≤ (y : ℝ) := by exact_mod_cast (le_trans (by norm_num only : 1 ≤ 2) hy)
  have hpsi : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ psiInProgression (y : ℝ) q a :=
    le_trans htheta (thetaInProgressionReal_le_psiInProgression (y : ℝ) q a hyReal)
  calc
    (((1 / 2 : ℝ) - epsilon) * ((y : ℝ) / (Nat.totient q : ℝ))) / Real.log (y : ℝ) ≤
        ((y : ℝ) / (2 * (Nat.totient q : ℝ)) - 18 * Real.sqrt (y : ℝ)) / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_right hmain (le_of_lt hlog)
    _ ≤ (primeCountInProgression y q a : ℝ) :=
      primeCountInProgression_ge_div_log_of_psi_lower y q a hy _ hpsi

/--
Inputs: natural numbers `y` and `q` with `(72 * q)^2 ≤ y`.

Claim: the `18 * sqrt y` progression error is at most `y`.

Proof: use `φ(q) ≤ q`, then take square roots of the modulus bound and multiply
by the nonnegative square root of `y`.

Role: this gives an elementary sufficient condition for the error hypothesis
in `primeCountInProgression_ge_main_term_of_theta_lower`.
-/
theorem progressionTheta_error_bound_of_modulus_square_bound (y q : ℕ)
    (hmodulus : (72 * (q : ℝ)) ^ 2 ≤ (y : ℝ)) :
    72 * (Nat.totient q : ℝ) * Real.sqrt (y : ℝ) ≤ (y : ℝ) := by
  have hphi : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hscaled : 72 * (Nat.totient q : ℝ) ≤ 72 * (q : ℝ) :=
    mul_le_mul_of_nonneg_left hphi (by norm_num only : (0 : ℝ) ≤ 72)
  have hsq : (72 * (Nat.totient q : ℝ)) ^ 2 ≤ (72 * (q : ℝ)) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le (Nat.totient q)))
          (mul_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le q))).2
      hscaled
  have hphiSquare : (72 * (Nat.totient q : ℝ)) ^ 2 ≤ (y : ℝ) := le_trans hsq hmodulus
  have hroot : 72 * (Nat.totient q : ℝ) ≤ Real.sqrt (y : ℝ) := Real.le_sqrt_of_sq_le hphiSquare
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (y : ℝ))
  rw [Real.mul_self_sqrt (by exact_mod_cast Nat.zero_le y)] at hmul
  exact hmul

/-
Inputs: a natural cutoff `y` and a modulus satisfying `(108 * q)^2 ≤ y`.

Claim: `108 * φ(q) * sqrt y ≤ y`.

Proof: use `φ(q) ≤ q`, take square roots of the modulus bound, and multiply
by `sqrt y`.

Role: this stronger error estimate supports the improved one-third
theta-to-prime-count conversion.
-/
theorem progressionTheta_strong_error_bound_of_modulus_square_bound (y q : ℕ)
    (hmodulus : (108 * (q : ℝ)) ^ 2 ≤ (y : ℝ)) :
    108 * (Nat.totient q : ℝ) * Real.sqrt (y : ℝ) ≤ (y : ℝ) := by
  have hphi : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hscaled : 108 * (Nat.totient q : ℝ) ≤ 108 * (q : ℝ) :=
    mul_le_mul_of_nonneg_left hphi (by norm_num only : (0 : ℝ) ≤ 108)
  have hsq : (108 * (Nat.totient q : ℝ)) ^ 2 ≤ (108 * (q : ℝ)) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le (Nat.totient q)))
          (mul_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le q))).2
      hscaled
  have hphiSquare : (108 * (Nat.totient q : ℝ)) ^ 2 ≤ (y : ℝ) := le_trans hsq hmodulus
  have hroot : 108 * (Nat.totient q : ℝ) ≤ Real.sqrt (y : ℝ) := Real.le_sqrt_of_sq_le hphiSquare
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (y : ℝ))
  rw [Real.mul_self_sqrt (by exact_mod_cast Nat.zero_le y)] at hmul
  exact hmul

/-
Inputs: a natural cutoff `y` and a modulus satisfying `(324 * q)^2 ≤ y`.

Claim: `324 * φ(q) * sqrt y ≤ y`.

Proof: use `φ(q) ≤ q`, take square roots of the modulus bound, and multiply
by `sqrt y`.

Role: this supplies the error condition for the four-ninths conversion.
-/
theorem progressionTheta_four_ninths_error_bound_of_modulus_square_bound (y q : ℕ)
    (hmodulus : (324 * (q : ℝ)) ^ 2 ≤ (y : ℝ)) :
    324 * (Nat.totient q : ℝ) * Real.sqrt (y : ℝ) ≤ (y : ℝ) := by
  have hphi : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hscaled : 324 * (Nat.totient q : ℝ) ≤ 324 * (q : ℝ) :=
    mul_le_mul_of_nonneg_left hphi (by norm_num only : (0 : ℝ) ≤ 324)
  have hsq : (324 * (Nat.totient q : ℝ)) ^ 2 ≤ (324 * (q : ℝ)) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le (Nat.totient q)))
          (mul_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le q))).2
      hscaled
  have hphiSquare : (324 * (Nat.totient q : ℝ)) ^ 2 ≤ (y : ℝ) := le_trans hsq hmodulus
  have hroot : 324 * (Nat.totient q : ℝ) ≤ Real.sqrt (y : ℝ) := Real.le_sqrt_of_sq_le hphiSquare
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (y : ℝ))
  rw [Real.mul_self_sqrt (by exact_mod_cast Nat.zero_le y)] at hmul
  exact hmul

/-
Inputs: a natural cutoff `y` and a modulus satisfying
`(18000000 * q)^2 ≤ y`.

Claim: `18000000 * φ(q) * sqrt y ≤ y`.

Proof: use `φ(q) ≤ q`, take square roots of the modulus bound, and multiply
by `sqrt y`.

Role: for epsilon `1 / 1000000`, this gives the error absorption required by
the sharper theta-to-prime-count conversion.
-/
theorem progressionTheta_millionth_error_bound_of_modulus_square_bound (y q : ℕ)
    (hmodulus : (18000000 * (q : ℝ)) ^ 2 ≤ (y : ℝ)) :
    18000000 * (Nat.totient q : ℝ) * Real.sqrt (y : ℝ) ≤ (y : ℝ) := by
  have hphi : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hscaled : 18000000 * (Nat.totient q : ℝ) ≤ 18000000 * (q : ℝ) :=
    mul_le_mul_of_nonneg_left hphi (by norm_num only : (0 : ℝ) ≤ 18000000)
  have hsq : (18000000 * (Nat.totient q : ℝ)) ^ 2 ≤ (18000000 * (q : ℝ)) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le (Nat.totient q)))
          (mul_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le q))).2
      hscaled
  have hphiSquare : (18000000 * (Nat.totient q : ℝ)) ^ 2 ≤ (y : ℝ) := le_trans hsq hmodulus
  have hroot : 18000000 * (Nat.totient q : ℝ) ≤ Real.sqrt (y : ℝ) :=
    Real.le_sqrt_of_sq_le hphiSquare
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (y : ℝ))
  rw [Real.mul_self_sqrt (by exact_mod_cast Nat.zero_le y)] at hmul
  exact hmul

/--
Inputs: `y ≥ 2`, a positive modulus `q` with `(72 * q)^2 ≤ y`, a residue `a`,
and a theta lower bound of half the expected main term.

Claim: the progression prime count is at least `y / (4 * φ(q) * log y)`.

Proof: derive the required `18 * sqrt y` error condition from the modulus
square bound, then apply the theta-to-count conversion.

Role: this packages the finite error check needed when applying a uniform
weighted progression estimate.
-/
theorem primeCountInProgression_ge_main_term_of_theta_lower_of_modulus_bound (y q a : ℕ)
    (hy : 2 ≤ y) (hq : 0 < q) (hmodulus : (72 * (q : ℝ)) ^ 2 ≤ (y : ℝ))
    (htheta : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ thetaInProgressionReal (y : ℝ) q a) :
    ((y : ℝ) / (4 * (Nat.totient q : ℝ))) / Real.log (y : ℝ) ≤
      (primeCountInProgression y q a : ℝ) := by
  have herror := progressionTheta_error_bound_of_modulus_square_bound y q hmodulus
  exact primeCountInProgression_ge_main_term_of_theta_lower y q a hy hq herror htheta

/-
Inputs: cutoffs `y ≤ x`, a positive modulus `q`, the modulus-square error
bound, and a theta lower bound of half the expected main term.

Claim: the progression prime count is at least `y / (4 * φ(q) * log x)`.

Proof: apply the theta-to-count estimate at cutoff `y`, then weaken its
denominator using `log y ≤ log x`.

Role: this expresses the raw progression-count estimate with the common
ambient cutoff used by the finite averaging argument.
-/
theorem primeCountInProgression_ge_main_term_over_log_upper_of_theta_lower (y x q a : ℕ)
    (hy : 2 ≤ y) (hq : 0 < q) (hyx : y ≤ x) (hmodulus : (72 * (q : ℝ)) ^ 2 ≤ (y : ℝ))
    (htheta : (y : ℝ) / (2 * (Nat.totient q : ℝ)) ≤ thetaInProgressionReal (y : ℝ) q a) :
    ((y : ℝ) / (4 * (Nat.totient q : ℝ))) / Real.log (x : ℝ) ≤
      (primeCountInProgression y q a : ℝ) := by
  have hbound :=
    primeCountInProgression_ge_main_term_of_theta_lower_of_modulus_bound y q a hy hq hmodulus htheta
  have hyPos : 0 < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hyxR : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hyx
  have hlog : Real.log (y : ℝ) ≤ Real.log (x : ℝ) := Real.log_le_log hyPos hyxR
  have hlogPos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hnumNonneg : 0 ≤ (y : ℝ) / (4 * (Nat.totient q : ℝ)) :=
    div_nonneg (by positivity) (by positivity)
  exact le_trans (div_le_div_of_nonneg_left hnumNonneg hlogPos hlog) hbound

/--
Inputs: `X ≥ 82944`, a divisor parameter `d ≤ X^2`, and a modulus `q ≤ 4d`.

Claim: `(72 * q)^2 ≤ d * X^3`.

Proof: bound `72q` by `288d`, then use `d ≤ X^2` and `288^2 ≤ X`.

Role: this is the explicit modulus-error condition at the AGP scale
`x = X^5` and `y = d * x^(3/5)`.
-/
theorem progressionTheta_modulus_square_bound_of_agp_fifth_power_scale (X d q : ℕ) (hX : 82944 ≤ X)
    (hd : d ≤ X ^ 2) (hq : q ≤ 4 * d) : (72 * q) ^ 2 ≤ d * X ^ 3 := by
  have hqScaled : 72 * q ≤ 288 * d := by
    calc
      72 * q ≤ 72 * (4 * d) := Nat.mul_le_mul_left 72 hq
      _ = 288 * d := by ring
  have hqSq : (72 * q) ^ 2 ≤ (288 * d) ^ 2 := Nat.pow_le_pow_left hqScaled 2
  have hbound : (288 * d) ^ 2 ≤ d * X ^ 3 := by
    calc
      (288 * d) ^ 2 = 288 ^ 2 * d ^ 2 := by ring
      _ ≤ 288 ^ 2 * (d * X ^ 2) :=
        Nat.mul_le_mul_left (288 ^ 2)
          (by
            calc
              d ^ 2 = d * d := by ring
              _ ≤ d * X ^ 2 := Nat.mul_le_mul_left d hd)
      _ ≤ X * (d * X ^ 2) :=
        Nat.mul_le_mul_right (d * X ^ 2)
          (by
            calc
              288 ^ 2 = 82944 := by norm_num only
              _ ≤ X := hX)
      _ = d * X ^ 3 := by ring
  exact le_trans hqSq hbound

/--
Inputs: `X ≥ 186624`, `d ≤ X^2`, and a modulus `q ≤ 4d`.

Claim: `(108 * q)^2 ≤ d * X^3`.

Proof: bound `108q` by `432d`, then use `d ≤ X^2` and `432^2 ≤ X`.

Role: this stronger modulus estimate absorbs the progression prime-power
error into one sixth of the main term.
-/
theorem progressionTheta_strong_modulus_square_bound_of_agp_fifth_power_scale (X d q : ℕ)
    (hX : 186624 ≤ X) (hd : d ≤ X ^ 2) (hq : q ≤ 4 * d) : (108 * q) ^ 2 ≤ d * X ^ 3 := by
  have hqScaled : 108 * q ≤ 432 * d := by
    calc
      108 * q ≤ 108 * (4 * d) := Nat.mul_le_mul_left 108 hq
      _ = 432 * d := by ring
  have hqSq : (108 * q) ^ 2 ≤ (432 * d) ^ 2 := Nat.pow_le_pow_left hqScaled 2
  have hbound : (432 * d) ^ 2 ≤ d * X ^ 3 := by
    calc
      (432 * d) ^ 2 = 432 ^ 2 * d ^ 2 := by ring
      _ ≤ 432 ^ 2 * (d * X ^ 2) :=
        Nat.mul_le_mul_left (432 ^ 2)
          (by
            calc
              d ^ 2 = d * d := by ring
              _ ≤ d * X ^ 2 := Nat.mul_le_mul_left d hd)
      _ ≤ X * (d * X ^ 2) :=
        Nat.mul_le_mul_right (d * X ^ 2)
          (by
            calc
              432 ^ 2 = 186624 := by norm_num only
              _ ≤ X := hX)
      _ = d * X ^ 3 := by ring
  exact le_trans hqSq hbound

/--
Inputs: `X ≥ 1679616`, `d ≤ X^2`, and a modulus `q ≤ 4d`.

Claim: `(324 * q)^2 ≤ d * X^3`.

Proof: bound `324q` by `1296d`, then use `d ≤ X^2` and `1296^2 ≤ X`.

Role: this fixed-scale condition absorbs the prime-power error into one
eighteenth of the progression main term.
-/
theorem progressionTheta_four_ninths_modulus_square_bound_of_agp_fifth_power_scale (X d q : ℕ)
    (hX : 1679616 ≤ X) (hd : d ≤ X ^ 2) (hq : q ≤ 4 * d) : (324 * q) ^ 2 ≤ d * X ^ 3 := by
  have hqScaled : 324 * q ≤ 1296 * d := by
    calc
      324 * q ≤ 324 * (4 * d) := Nat.mul_le_mul_left 324 hq
      _ = 1296 * d := by ring
  have hqSq : (324 * q) ^ 2 ≤ (1296 * d) ^ 2 := Nat.pow_le_pow_left hqScaled 2
  have hbound : (1296 * d) ^ 2 ≤ d * X ^ 3 := by
    calc
      (1296 * d) ^ 2 = 1296 ^ 2 * d ^ 2 := by ring
      _ ≤ 1296 ^ 2 * (d * X ^ 2) :=
        Nat.mul_le_mul_left (1296 ^ 2)
          (by
            calc
              d ^ 2 = d * d := by ring
              _ ≤ d * X ^ 2 := Nat.mul_le_mul_left d hd)
      _ ≤ X * (d * X ^ 2) :=
        Nat.mul_le_mul_right (d * X ^ 2)
          (by
            calc
              1296 ^ 2 = 1679616 := by norm_num only
              _ ≤ X := hX)
      _ = d * X ^ 3 := by ring
  exact le_trans hqSq hbound

/-
Inputs: `X ≥ 5184000000000000`, `d ≤ X^2`, and `q ≤ 4d`.

Claim: `(18000000 * q)^2 ≤ d * X^3`.

Proof: bound `18000000q` by `72000000d`, then use `d ≤ X^2` and
`72000000^2 ≤ X`.

Role: together with `2^56 ≤ X`, this absorbs the higher prime-power error to
within one millionth of the progression main term.
-/
theorem progressionTheta_millionth_modulus_square_bound_of_agp_fifth_power_scale (X d q : ℕ)
    (hX : 5184000000000000 ≤ X) (hd : d ≤ X ^ 2) (hq : q ≤ 4 * d) :
    (18000000 * q) ^ 2 ≤ d * X ^ 3 := by
  have hqScaled : 18000000 * q ≤ 72000000 * d := by
    calc
      18000000 * q ≤ 18000000 * (4 * d) := Nat.mul_le_mul_left 18000000 hq
      _ = 72000000 * d := by ring
  have hqSq : (18000000 * q) ^ 2 ≤ (72000000 * d) ^ 2 := Nat.pow_le_pow_left hqScaled 2
  have hbound : (72000000 * d) ^ 2 ≤ d * X ^ 3 := by
    calc
      (72000000 * d) ^ 2 = 72000000 ^ 2 * d ^ 2 := by ring
      _ ≤ 72000000 ^ 2 * (d * X ^ 2) :=
        Nat.mul_le_mul_left (72000000 ^ 2)
          (by
            calc
              d ^ 2 = d * d := by ring
              _ ≤ d * X ^ 2 := Nat.mul_le_mul_left d hd)
      _ ≤ X * (d * X ^ 2) :=
        Nat.mul_le_mul_right (d * X ^ 2)
          (by
            calc
              72000000 ^ 2 = 5184000000000000 := by norm_num only
              _ ≤ X := hX)
      _ = d * X ^ 3 := by ring
  exact le_trans hqSq hbound

/--
The chosen paper95 parameters satisfy `1/A - δ > B` for
`A = 49/20`, `δ = 1/1000`, and `B = 2/5`.

Role: this positive margin makes it possible to absorb the fixed CRT factor
four into both modulus bounds once the scale is sufficiently large.
-/
theorem paper95_agp_exponent_gap_positive : 0 < (20 : ℝ) / 49 - 1 / 1000 - 2 / 5 := by norm_num only

/--
Inputs: a real cutoff `x` at least `2^280`.

Claim: `x^(1/A - δ - B) ≥ 4` for the AGP choices `A = 49/20`,
`δ = 1/1000`, and `B = 2/5`.

Proof: compare the exponent with `2/280`, then use monotonicity of real powers
in the base and in the exponent.

Role: this provides a concrete sufficient cutoff for absorbing the factor four
in paper95 Theorem 2.1's modulus range.
-/
theorem paper95_scale_threshold_of_large_cutoff (x : ℝ) (hx : (2 : ℝ) ^ ((56 : ℝ) * 5) ≤ x) :
    4 ≤ x ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) := by
  have hbeta : 0 ≤ (20 : ℝ) / 49 - 1 / 1000 - 2 / 5 := by norm_num only
  have hlarge : 2 ≤ (56 : ℝ) * 5 * ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) := by norm_num only
  have hsmall : 4 ≤ ((2 : ℝ) ^ ((56 : ℝ) * 5)) ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num only
      _ ≤ (2 : ℝ) ^ ((56 : ℝ) * 5 * ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num only : (1 : ℝ) ≤ 2) hlarge
      _ = ((2 : ℝ) ^ ((56 : ℝ) * 5)) ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) :=
        Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 2) ((56 : ℝ) * 5) _
  exact
    le_trans hsmall
      (Real.rpow_le_rpow
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num only : (0 : ℝ) < 2) ((56 : ℝ) * 5))) hx hbeta)

/--
Inputs: an exceptional modulus `e`, a cutoff `x` whose logarithm exceeds `4`,
and the paper95 Theorem 2.1 lower bound `log x < e`.

Claim: `e` does not divide the fixed CRT modulus `4`.

Proof: divisibility by `4` would imply `e ≤ 4`, contradicting the two real
inequalities.

Role: this discharges the exceptional-modulus avoidance side condition for the
fixed progression modulus `4` once the Theorem 2.1 exceptional-set estimate is
available.
-/
theorem paper95_exceptional_modulus_not_dvd_four (e : ℕ) (x : ℝ) (hlog : (4 : ℝ) < Real.log x)
    (he : Real.log x < (e : ℝ)) : ¬e ∣ 4 := by
  intro hdiv
  have hltReal : (4 : ℝ) < (e : ℝ) := lt_trans hlog he
  have hle : e ≤ 4 := Nat.le_of_dvd (by norm_num only) hdiv
  have hleReal : (e : ℝ) ≤ 4 := by exact_mod_cast hle
  exact (not_le_of_gt hltReal) hleReal

/--
Inputs: a finite exceptional-modulus set, a cutoff with `log x > 4`, and the
paper95 lower bound `log x < e` for every exceptional modulus.

Claim: no exceptional modulus in the set divides `4`.

Proof: apply `paper95_exceptional_modulus_not_dvd_four` to each member.

Role: this supplies the `hEm` hypothesis required by modulus-aware factor
removal for the progression modulo four.
-/
theorem paper95_exceptional_moduli_not_dvd_four (E : Finset ℕ) (x : ℝ) (hlog : (4 : ℝ) < Real.log x)
    (hE : ∀ e ∈ E, Real.log x < (e : ℝ)) : ∀ e ∈ E, ¬e ∣ 4 := by
  intro e he
  exact paper95_exceptional_modulus_not_dvd_four e x hlog (hE e he)

/--
Inputs: a natural parameter `X ≥ 2^56` and the fifth-power cutoff `X^5`.

Claim: the logarithm of this cutoff is greater than `4`.

Proof: compare `X^5` with `2^280`, use monotonicity of `Real.log`, and apply
the explicit lower bound `Real.log_two_gt_d9`.

Role: this supplies the numerical condition needed to keep every paper95
exceptional modulus, which exceeds `log x`, from dividing the CRT modulus `4`.
-/
theorem paper95_log_gt_four_of_nat_fifth_power_scale (X : ℕ) (hX : 2 ^ 56 ≤ X) :
    (4 : ℝ) < Real.log ((X ^ 5 : ℕ) : ℝ) := by
  have hnat : 2 ^ 280 ≤ X ^ 5 := by
    calc
      2 ^ 280 = 2 ^ (56 * 5) := by congr 1
      _ = (2 ^ 56) ^ 5 := by rw [← pow_mul]
      _ ≤ X ^ 5 := Nat.pow_le_pow_left hX 5
  have hcast : (2 : ℝ) ^ 280 ≤ ((X ^ 5 : ℕ) : ℝ) := by exact_mod_cast hnat
  have hlog : Real.log ((2 : ℝ) ^ 280) ≤ Real.log ((X ^ 5 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) hcast
  have hlogpow : Real.log ((2 : ℝ) ^ 280) = (280 : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
    norm_num only
  have hgt : (4 : ℝ) < (280 : ℝ) * Real.log 2 := by nlinarith only [Real.log_two_gt_d9]
  exact
    lt_of_lt_of_le
      (by
        rw [hlogpow]; exact hgt)
      hlog

/--
Inputs: `X ≥ 2^56` and a finite exceptional set whose elements exceed
`log (X^5)` as in paper95 Theorem 2.1.

Claim: none of these exceptional moduli divides `4`.

Proof: the fifth-power cutoff has logarithm greater than `4`, so apply the
finite-set divisor exclusion theorem above.

Role: this derives the modulus-four side condition for exceptional-factor
removal directly from the paper95 exceptional-set property at the AGP scale.
-/
theorem paper95_exceptional_moduli_not_dvd_four_of_nat_fifth_power_scale (E : Finset ℕ) (X : ℕ)
    (hX : 2 ^ 56 ≤ X) (hE : ∀ e ∈ E, Real.log ((X ^ 5 : ℕ) : ℝ) < (e : ℝ)) : ∀ e ∈ E, ¬e ∣ 4 := by
  exact
    paper95_exceptional_moduli_not_dvd_four E ((X ^ 5 : ℕ) : ℝ)
      (paper95_log_gt_four_of_nat_fifth_power_scale X hX) hE

/--
Inputs: `X ≥ 2^56` and the paper95 lower bound `log (X^5) < e` for every
exceptional modulus `e` in `E`.

Claim: each exceptional modulus exceeds `1` and none divides `4`.

Proof: the logarithm exceeds `4`; cast the resulting lower bound to `ℕ` and
apply the exceptional-modulus divisor exclusion theorem.

Role: this provides both exceptional-set side conditions required by the
modulus-four version of the fifth-power prime-set construction.
-/
theorem paper95_exceptional_moduli_conditions_for_four_of_nat_fifth_power_scale (E : Finset ℕ)
    (X : ℕ) (hX : 2 ^ 56 ≤ X) (hE : ∀ e ∈ E, Real.log ((X ^ 5 : ℕ) : ℝ) < (e : ℝ)) :
    (∀ e ∈ E, 1 < e) ∧ ∀ e ∈ E, ¬e ∣ 4 := by
  have hlog := paper95_log_gt_four_of_nat_fifth_power_scale X hX
  constructor
  · intro e he
    have hfour : (4 : ℝ) < (e : ℝ) := lt_trans hlog (hE e he)
    have hone : (1 : ℝ) < (e : ℝ) := lt_trans (by norm_num only) hfour
    exact_mod_cast hone
  · exact paper95_exceptional_moduli_not_dvd_four_of_nat_fifth_power_scale E X hX hE

/--
Inputs: a real scale `x ≥ 1`, a divisor cutoff `d ≤ x^(2/5)`, and the
threshold `x^(1/A - δ - 2/5) ≥ 4` for `A = 49/20` and `δ = 1/1000`.

Claim: the CRT modulus `4d` satisfies both modulus upper bounds in paper95
Theorem 2.1 when its progression cutoff is `y = d * x^(3/5)`.

Proof: combine the divisor cutoff and factor-four threshold for the first
bound; cancel the displayed powers for the second.

Role: this proves the exact range reduction needed to apply Theorem 2.1 to the
fixed `B = 2/5` scale in Theorem 3.1.
-/
theorem paper95_modulus_range_of_agp_scale (x d : ℝ) (hx : 1 ≤ x) (hd : 0 ≤ d)
    (hdivisor : d ≤ x ^ ((2 : ℝ) / 5)) (hthreshold : 4 ≤ x ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5)) :
    4 * d ≤ x ^ ((20 : ℝ) / 49 - 1 / 1000) ∧
      4 * d ≤ (d * x ^ ((3 : ℝ) / 5)) / x ^ (1 - (20 : ℝ) / 49 + 1 / 1000) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num only : 0 < (1 : ℝ)) hx
  have hfirst : 4 * d ≤ x ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) * x ^ ((2 : ℝ) / 5) :=
    mul_le_mul hthreshold hdivisor hd (le_of_lt (Real.rpow_pos_of_pos hxpos _))
  have hpower :
    x ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) * x ^ ((2 : ℝ) / 5) =
      x ^ ((20 : ℝ) / 49 - 1 / 1000) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hsecondPower :
    (d * x ^ ((3 : ℝ) / 5)) / x ^ (1 - (20 : ℝ) / 49 + 1 / 1000) =
      d * x ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) := by
    calc
      (d * x ^ ((3 : ℝ) / 5)) / x ^ (1 - (20 : ℝ) / 49 + 1 / 1000) =
          d * (x ^ ((3 : ℝ) / 5) / x ^ (1 - (20 : ℝ) / 49 + 1 / 1000)) :=
        by ring
      _ = d * x ^ ((3 : ℝ) / 5 - (1 - (20 : ℝ) / 49 + 1 / 1000)) := by rw [← Real.rpow_sub hxpos]
      _ = d * x ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) := by
        congr 2
        ring
  constructor
  · calc
      4 * d ≤ x ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) * x ^ ((2 : ℝ) / 5) := hfirst
      _ = x ^ ((20 : ℝ) / 49 - 1 / 1000) := hpower
  · calc
      4 * d ≤ x ^ ((20 : ℝ) / 49 - 1 / 1000 - 2 / 5) * d := mul_le_mul_of_nonneg_right hthreshold hd
      _ = (d * x ^ ((3 : ℝ) / 5)) / x ^ (1 - (20 : ℝ) / 49 + 1 / 1000) := by
        rw [hsecondPower]
        ring

/--
Inputs: a real cutoff `x ≥ 2^280` and a divisor `d ≤ x^(2/5)`.

Claim: the CRT modulus `4d` satisfies both paper95 Theorem 2.1 modulus bounds
for `y = d * x^(3/5)` with `A = 49/20` and `δ = 1/1000`.

Proof: the explicit cutoff theorem supplies the factor-four threshold, after
which `paper95_modulus_range_of_agp_scale` applies.

Role: this is the scale-ready form of the range reduction.
-/
theorem paper95_modulus_range_of_large_cutoff (x d : ℝ) (hx : (2 : ℝ) ^ ((56 : ℝ) * 5) ≤ x)
    (hd : 0 ≤ d) (hdivisor : d ≤ x ^ ((2 : ℝ) / 5)) :
    4 * d ≤ x ^ ((20 : ℝ) / 49 - 1 / 1000) ∧
      4 * d ≤ (d * x ^ ((3 : ℝ) / 5)) / x ^ (1 - (20 : ℝ) / 49 + 1 / 1000) := by
  have hbase : 1 ≤ (2 : ℝ) ^ ((56 : ℝ) * 5) :=
    Real.one_le_rpow (by norm_num only : (1 : ℝ) ≤ 2) (by norm_num only : (0 : ℝ) ≤ (56 : ℝ) * 5)
  exact
    paper95_modulus_range_of_agp_scale x d (le_trans hbase hx) hd hdivisor
      (paper95_scale_threshold_of_large_cutoff x hx)

/--
Inputs: natural parameters `X` and `d` with `X ≥ 2^56` and `d ≤ X^2`.

Claim: at the AGP scale `x = X^5`, the CRT modulus `4d` satisfies both
paper95 Theorem 2.1 modulus bounds for `y = d * X^3`.

Proof: cast the natural scale and divisor bounds to reals, then apply the
large-cutoff modulus-range theorem.

Role: this connects the abstract real range calculation to the natural
parameters used by the finite prime-supply construction.
-/
theorem paper95_modulus_range_of_nat_fifth_power_scale (X d : ℕ) (hX : 2 ^ 56 ≤ X)
    (hd : d ≤ X ^ 2) :
    (4 : ℝ) * (d : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) ^ ((20 : ℝ) / 49 - 1 / 1000) ∧
      (4 : ℝ) * (d : ℝ) ≤
        ((d * X ^ 3 : ℕ) : ℝ) / ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) := by
  have hcutNat : (2 ^ 56) ^ 5 ≤ X ^ 5 := Nat.pow_le_pow_left hX 5
  have hcutReal : ((2 : ℝ) ^ 56) ^ 5 ≤ (X : ℝ) ^ 5 := by exact_mod_cast hcutNat
  have hinner : (2 : ℝ) ^ (56 : ℝ) = (2 : ℝ) ^ 56 := Real.rpow_natCast _ _
  have houter : ((2 : ℝ) ^ (56 : ℝ)) ^ (5 : ℝ) = ((2 : ℝ) ^ (56 : ℝ)) ^ 5 := Real.rpow_natCast _ _
  have hcutThreshold : (2 : ℝ) ^ ((56 : ℝ) * 5) = ((2 : ℝ) ^ 56) ^ 5 := by
    calc
      (2 : ℝ) ^ ((56 : ℝ) * 5) = ((2 : ℝ) ^ (56 : ℝ)) ^ (5 : ℝ) :=
        Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 2) 56 5
      _ = ((2 : ℝ) ^ (56 : ℝ)) ^ 5 := houter
      _ = ((2 : ℝ) ^ 56) ^ 5 := congrArg (fun z : ℝ => z ^ (5 : ℕ)) hinner
  have hxlower : (2 : ℝ) ^ ((56 : ℝ) * 5) ≤ ((X ^ 5 : ℕ) : ℝ) := by
    calc
      (2 : ℝ) ^ ((56 : ℝ) * 5) = ((2 : ℝ) ^ 56) ^ 5 := hcutThreshold
      _ ≤ (X : ℝ) ^ 5 := hcutReal
      _ = ((X ^ 5 : ℕ) : ℝ) := by rw [Nat.cast_pow]
  have hXnonneg : 0 ≤ (X : ℝ) := by exact_mod_cast Nat.zero_le X
  have hXfiveCast : ((X ^ 5 : ℕ) : ℝ) = (X : ℝ) ^ 5 := by simp only [Nat.cast_pow]
  have hXfiveRpow : (X : ℝ) ^ 5 = (X : ℝ) ^ (5 : ℝ) := (Real.rpow_natCast _ _).symm
  have hmulDivisor := Real.rpow_mul hXnonneg 5 ((2 : ℝ) / 5)
  have hexpDivisor : (5 : ℝ) * ((2 : ℝ) / 5) = 2 := by ring
  rw [hexpDivisor] at hmulDivisor
  have hXtwoRpow : (X : ℝ) ^ 2 = (X : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast _ _).symm
  have hdivisorPow : ((X : ℝ) ^ 5) ^ ((2 : ℝ) / 5) = (X : ℝ) ^ 2 := by
    rw [hXfiveRpow, hXtwoRpow]
    exact hmulDivisor.symm
  have hdivisor : (d : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) ^ ((2 : ℝ) / 5) := by
    rw [hXfiveCast, hdivisorPow]
    exact_mod_cast hd
  have hmulCutoff := Real.rpow_mul hXnonneg 5 ((3 : ℝ) / 5)
  have hexpCutoff : (5 : ℝ) * ((3 : ℝ) / 5) = 3 := by ring
  rw [hexpCutoff] at hmulCutoff
  have hXthreeRpow : (X : ℝ) ^ 3 = (X : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast _ _).symm
  have hyPow : ((X ^ 5 : ℕ) : ℝ) ^ ((3 : ℝ) / 5) = (X : ℝ) ^ 3 := by
    rw [hXfiveCast, hXfiveRpow, hXthreeRpow]
    exact hmulCutoff.symm
  have hrange :=
    paper95_modulus_range_of_large_cutoff ((X ^ 5 : ℕ) : ℝ) (d : ℝ) hxlower
      (by exact_mod_cast Nat.zero_le d) hdivisor
  have hY : ((d * X ^ 3 : ℕ) : ℝ) = (d : ℝ) * ((X ^ 5 : ℕ) : ℝ) ^ ((3 : ℝ) / 5) := by
    rw [Nat.cast_mul, Nat.cast_pow, hyPow]
  have hsecond :
    (4 : ℝ) * (d : ℝ) ≤
      ((d * X ^ 3 : ℕ) : ℝ) / ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) := by
    rw [hY]
    exact hrange.2
  exact ⟨hrange.1, hsecond⟩

/--
Inputs: a positive divisor `d ≤ X^2` and a natural cutoff at least
`ceil(log (X^5))`.

Claim: `log (d X^3) ≤ 4d`, so the modulus `4d` lies in the large-modulus
branch of paper95 Theorem 2.1.

Proof: compare `d X^3` with `X^5`, use monotonicity of `log`, and bound the
logarithm by the natural cutoff and then by `4d`.

Role: this makes the large-modulus range hold uniformly for every divisor
above the selected natural cutoff.
-/
theorem paper95_log_modulus_bound_of_nat_fifth_power_scale (X d : ℕ) (hdPos : 0 < d)
    (hd : d ≤ X ^ 2) (hceil : Nat.ceil (Real.log ((X ^ 5 : ℕ) : ℝ)) ≤ d) :
    Real.log ((d * X ^ 3 : ℕ) : ℝ) ≤ (4 : ℝ) * (d : ℝ) := by
  have hXPos : 0 < X := by
    have hXne : X ≠ 0 := by
      intro hX
      subst X
      norm_num only at hd
      have hdZero : d = 0 := Nat.le_zero.mp hd
      subst d
      norm_num only at hdPos
    exact Nat.pos_of_ne_zero hXne
  have hxyNat : d * X ^ 3 ≤ X ^ 5 := by
    calc
      d * X ^ 3 ≤ X ^ 2 * X ^ 3 := Nat.mul_le_mul_right _ hd
      _ = X ^ 5 := by rw [← pow_add]
  have hxy : ((d * X ^ 3 : ℕ) : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) := by exact_mod_cast hxyNat
  have hyPos : 0 < ((d * X ^ 3 : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hdPos (Nat.pow_pos hXPos)
  have hceilReal : Real.log ((X ^ 5 : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have hdle4d : (d : ℝ) ≤ 4 * (d : ℝ) := by
    have hdNonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    nlinarith only [hdNonneg]
  exact (Real.log_le_log hyPos hxy).trans (le_trans hceilReal hdle4d)

/--
Inputs: `X ≥ 2^56`, `1 ≤ d ≤ X^2`, the logarithmic lower-range estimate,
and `ceil(log x) ≤ d` for `x = X^5`.

Claim: it returns the lower modulus condition and the other cutoff inequalities
in Theorem 2.1 with `A = 49/20`, `δ = 1/1000`, and `ε = 1/2`.

Proof: derive `log y ≤ 4d` from `y ≤ x` and the natural cutoff, then use the
natural-scale modulus bounds, compare `x^(1/2)` with
`q * x^(1 - 1/A + δ)`, and bound `y` by `x ≤ exp x`.

Role: this isolates the large-modulus branch of the range check. The paper
handles `q ≤ log y` separately, and that small-modulus estimate remains to be
connected for all divisors.
-/
theorem paper95_cutoff_range_of_nat_fifth_power_scale (X d : ℕ) (hX : 2 ^ 56 ≤ X) (hdPos : 0 < d)
    (hd : d ≤ X ^ 2) (hlogMod : Real.log ((d * X ^ 3 : ℕ) : ℝ) ≤ (4 : ℝ) * (d : ℝ))
    (hlogRange : Real.log ((X ^ 5 : ℕ) : ℝ) ^ 4000 < ((X ^ 5 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) :
    Real.log ((X ^ 5 : ℕ) : ℝ) ^ 4000 < ((X ^ 5 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ∧
      Real.log ((d * X ^ 3 : ℕ) : ℝ) ≤ (4 : ℝ) * (d : ℝ) ∧
      1 ≤ (4 : ℝ) * (d : ℝ) ∧
      (4 : ℝ) * (d : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) ^ ((20 : ℝ) / 49 - 1 / 1000) ∧
      ((X ^ 5 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) <
        (4 : ℝ) * (d : ℝ) * ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) ∧
      (4 : ℝ) * (d : ℝ) * ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) ≤
        ((d * X ^ 3 : ℕ) : ℝ) ∧
      ((d * X ^ 3 : ℕ) : ℝ) ≤ Real.exp ((X ^ 5 : ℕ) : ℝ) := by
  have hmod := paper95_modulus_range_of_nat_fifth_power_scale X d hX hd
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (by omega : 0 < X)
  have hxpos : 0 < ((X ^ 5 : ℕ) : ℝ) := by positivity
  have hxone : 1 ≤ ((X ^ 5 : ℕ) : ℝ) := by
    have hXlarge : 0 < X := by omega
    exact_mod_cast Nat.one_le_pow 5 X hXlarge
  have hdOne : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdPos)
  have hqOne : 1 < (4 : ℝ) * (d : ℝ) := by
    have hdCast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdOne
    nlinarith only [hdCast]
  have hgamma : (1 : ℝ) / 2 ≤ 1 - (20 : ℝ) / 49 + 1 / 1000 := by norm_num only
  have hgammaPos := Real.rpow_pos_of_pos hxpos (1 - (20 : ℝ) / 49 + 1 / 1000)
  have hpowOrder := Real.rpow_le_rpow_of_exponent_le hxone hgamma
  have hstrict := mul_lt_mul_of_pos_right hqOne hgammaPos
  have hsecond := hmod.2
  have hdenomPos := Real.rpow_pos_of_pos hxpos (1 - (20 : ℝ) / 49 + 1 / 1000)
  have hYlower :
    (4 : ℝ) * (d : ℝ) * ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) ≤
      ((d * X ^ 3 : ℕ) : ℝ) := by
    exact (le_div_iff₀ hdenomPos).mp hsecond
  have hYupperNat : d * X ^ 3 ≤ X ^ 5 := by
    calc
      d * X ^ 3 ≤ X ^ 2 * X ^ 3 := Nat.mul_le_mul_right (X ^ 3) hd
      _ = X ^ 5 := by ring
  have hYupper : ((d * X ^ 3 : ℕ) : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) := by exact_mod_cast hYupperNat
  refine ⟨hlogRange, hlogMod, ?_⟩
  refine ⟨?_, hmod.1, ?_, hYlower, ?_⟩
  · have hdCast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdOne
    nlinarith only [hdCast]
  · exact lt_of_le_of_lt hpowOrder (by simpa only [one_mul] using hstrict)
  · calc
      ((d * X ^ 3 : ℕ) : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) := hYupper
      _ ≤ ((X ^ 5 : ℕ) : ℝ) + 1 := le_add_of_nonneg_right (by norm_num only)
      _ ≤ Real.exp ((X ^ 5 : ℕ) : ℝ) := Real.add_one_le_exp _

/--
Inputs: `X ≥ 2^56`, `d ≤ X^2`, and a positive divisor `d`.

Claim: the modulus `q = 4d` is at most `min (X^5) (d X^3) ^ (1/A - δ)`
for `A = 49/20` and `δ = 1/1000`.

Proof: the large-cutoff range gives `q * x^(1 - 1/A + δ) ≤ y`; since `y ≤ x`,
monotonicity of real powers converts this into the required bound by `y`.

Role: this puts the fixed natural scale in the modulus form used in paper95
Theorem 2.1, complementing the lower-modulus cutoff hypothesis above.
-/
theorem paper95_min_modulus_power_bound_of_nat_fifth_power_scale (X d : ℕ) (hX : 2 ^ 56 ≤ X)
    (hdPos : 0 < d) (hd : d ≤ X ^ 2) :
    (4 : ℝ) * (d : ℝ) ≤
      min ((X ^ 5 : ℕ) : ℝ) ((d * X ^ 3 : ℕ) : ℝ) ^ ((20 : ℝ) / 49 - 1 / 1000) := by
  have hmod := paper95_modulus_range_of_nat_fifth_power_scale X d hX hd
  have hxpos : 0 < ((X ^ 5 : ℕ) : ℝ) := by positivity
  have hgammaPosX := Real.rpow_pos_of_pos hxpos (1 - (20 : ℝ) / 49 + 1 / 1000)
  have hXposNat : 0 < X := by exact Nat.lt_of_lt_of_le (by norm_num only : 0 < 2 ^ 56) hX
  have hyPosNat : 0 < d * X ^ 3 := Nat.mul_pos hdPos (pow_pos hXposNat 3)
  have hyPos : 0 < ((d * X ^ 3 : ℕ) : ℝ) := by exact_mod_cast hyPosNat
  have hgammaPosY := Real.rpow_pos_of_pos hyPos (1 - (20 : ℝ) / 49 + 1 / 1000)
  have hYupperNat : d * X ^ 3 ≤ X ^ 5 := by
    calc
      d * X ^ 3 ≤ X ^ 2 * X ^ 3 := Nat.mul_le_mul_right (X ^ 3) hd
      _ = X ^ 5 := by ring
  have hYupper : ((d * X ^ 3 : ℕ) : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) := by exact_mod_cast hYupperNat
  have hYlower :
    (4 : ℝ) * (d : ℝ) * ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) ≤
      ((d * X ^ 3 : ℕ) : ℝ) :=
    (le_div_iff₀ hgammaPosX).mp hmod.2
  have hyGammaLeXGamma :=
    Real.rpow_le_rpow (le_of_lt hyPos) hYupper
      (by norm_num only : (0 : ℝ) ≤ 1 - (20 : ℝ) / 49 + 1 / 1000)
  have hprod :
    (4 : ℝ) * (d : ℝ) * ((d * X ^ 3 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) ≤
      ((d * X ^ 3 : ℕ) : ℝ) := by
    calc
      _ ≤ (4 : ℝ) * (d : ℝ) * ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) :=
        mul_le_mul_of_nonneg_left hyGammaLeXGamma (by positivity)
      _ ≤ ((d * X ^ 3 : ℕ) : ℝ) := hYlower
  have hsum : (20 : ℝ) / 49 - 1 / 1000 + (1 - (20 : ℝ) / 49 + 1 / 1000) = 1 := by ring
  have hfactor :
    ((d * X ^ 3 : ℕ) : ℝ) ^ ((20 : ℝ) / 49 - 1 / 1000) *
        ((d * X ^ 3 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) =
      ((d * X ^ 3 : ℕ) : ℝ) := by
    rw [← Real.rpow_add hyPos, hsum, Real.rpow_one]
  have hprod' :
    (4 : ℝ) * (d : ℝ) * ((d * X ^ 3 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) ≤
      ((d * X ^ 3 : ℕ) : ℝ) ^ ((20 : ℝ) / 49 - 1 / 1000) *
        ((d * X ^ 3 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) := by
    calc
      _ ≤ ((d * X ^ 3 : ℕ) : ℝ) := hprod
      _ = _ := hfactor.symm
  have hmin : min ((X ^ 5 : ℕ) : ℝ) ((d * X ^ 3 : ℕ) : ℝ) = ((d * X ^ 3 : ℕ) : ℝ) :=
    min_eq_right hYupper
  rw [hmin]
  exact le_of_mul_le_mul_right hprod' hgammaPosY

/--
Input: the natural logarithm and square-root functions on the real numbers.

Claim: there is a real cutoff beyond which `(log x)^4000 < sqrt x`.

Proof: use the little-o estimate for the 8000th power of `log x`, bound it
eventually by `x / 2`, and take square roots.

Role: this supplies the elementary logarithmic range condition in paper95
Theorem 2.1; its threshold can be combined with the analytic threshold there.
-/
theorem exists_paper95_log_range_cutoff :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Real.log x ^ 4000 < Real.sqrt x := by
  have hLittle : (fun x : ℝ => Real.log x ^ 8000) =o[Filter.atTop] fun x => x :=
    Real.isLittleO_pow_log_id_atTop
  have hsmall := (Asymptotics.isLittleO_iff.mp hLittle) (c := (1 / 2 : ℝ)) (by norm_num only)
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_atTop.2 ⟨1, fun x hx => hx⟩
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ 4000 < Real.sqrt x := by
    filter_upwards [hsmall, hlarge] with x hs hx
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num only) hx
    have hlognonneg := Real.log_nonneg hx
    have hlogpow : Real.log x ^ 8000 ≤ x / 2 := by
      have hs' := hs
      simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlognonneg 8000),
        abs_of_nonneg (le_of_lt hxpos)] at hs'
      nlinarith only [hs']
    have hsquare : (Real.log x ^ 4000) ^ 2 = Real.log x ^ 8000 := by rw [← pow_mul]
    have hrootEq : Real.sqrt (Real.log x ^ 8000) = Real.log x ^ 4000 := by
      rw [← hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hlognonneg 4000)]
    have hroot : Real.sqrt (Real.log x ^ 8000) ≤ Real.sqrt (x / 2) := Real.sqrt_le_sqrt hlogpow
    have hhalf : x / 2 < x := by linarith only [hxpos]
    rw [← hrootEq]
    exact lt_of_le_of_lt hroot (Real.sqrt_lt_sqrt (by positivity) hhalf)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hevent
  exact ⟨x₀, hx₀⟩

/--
Input: a natural cutoff `X` and the logarithmic estimate above a real threshold.

Claim: some natural cutoff makes `(log (X^5))^4000 < sqrt (X^5)` hold for
every larger natural `X`.

Proof: choose a natural number above the real threshold and use `X ≤ X^5`.

Role: this supplies the logarithmic range input to the fixed-scale form of
paper95 Theorem 2.1.
-/
theorem exists_nat_fifth_power_log_range_cutoff :
    ∃ X₀ : ℕ,
      ∀ X : ℕ, X₀ ≤ X → Real.log ((X ^ 5 : ℕ) : ℝ) ^ 4000 < Real.sqrt ((X ^ 5 : ℕ) : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := exists_paper95_log_range_cutoff
  obtain ⟨N, hN⟩ := exists_nat_gt x₀
  refine ⟨N, ?_⟩
  intro X hX
  have hNX : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpow : (X : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_pow (a := X) (b := 5) (by norm_num only)
  exact hx₀ ((X ^ 5 : ℕ) : ℝ) (le_trans (le_of_lt hN) (le_trans hNX hXpow))

/--
Inputs: a sufficiently large natural scale `X`, a natural divisor cutoff `q`
at least `ceil(log (X^5))`, and a divisor `d` with `q < d ≤ X^2`.

Claim: all large-modulus range conditions in paper95 Theorem 2.1 hold at
`x = X^5`, `q = 4d`, and `y = d X^3`, including the upper bound by
`min{x,y}`.

Proof: derive `log (d X^3) ≤ 4d` uniformly from `q < d`, then combine the
eventual logarithmic estimate with the fixed-scale range and minimum-modulus
bounds.

Role: this packages the verified large-modulus branch for later analytic
progression estimates.
-/
theorem exists_nat_fifth_power_large_modulus_range :
    ∃ X₀ : ℕ,
      ∀ X : ℕ,
        X₀ ≤ X →
          ∀ q : ℕ,
            Nat.ceil (Real.log ((X ^ 5 : ℕ) : ℝ)) ≤ q →
              ∀ d : ℕ,
                q < d →
                  d ≤ X ^ 2 →
                  (Real.log ((X ^ 5 : ℕ) : ℝ) ^ 4000 < ((X ^ 5 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ∧
                    Real.log ((d * X ^ 3 : ℕ) : ℝ) ≤ (4 : ℝ) * (d : ℝ) ∧
                    1 ≤ (4 : ℝ) * (d : ℝ) ∧
                    (4 : ℝ) * (d : ℝ) ≤
                      min ((X ^ 5 : ℕ) : ℝ) ((d * X ^ 3 : ℕ) : ℝ) ^ ((20 : ℝ) / 49 - 1 / 1000) ∧
                    ((X ^ 5 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) <
                      (4 : ℝ) * (d : ℝ) * ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) ∧
                    (4 : ℝ) * (d : ℝ) * ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) ≤
                      ((d * X ^ 3 : ℕ) : ℝ) ∧
                    ((d * X ^ 3 : ℕ) : ℝ) ≤ Real.exp ((X ^ 5 : ℕ) : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_fifth_power_log_range_cutoff
  refine ⟨max (2 ^ 56) N, ?_⟩
  intro X hX q hqceil d hqd hd
  have hdPos : 0 < d := Nat.zero_lt_of_lt hqd
  have hceil : Nat.ceil (Real.log ((X ^ 5 : ℕ) : ℝ)) ≤ d := le_trans hqceil (Nat.le_of_lt hqd)
  have hXlarge : 2 ^ 56 ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hNle : N ≤ X := le_trans (Nat.le_max_right _ _) hX
  have hlogRange := hN X hNle
  have hlogRangePower : Real.log ((X ^ 5 : ℕ) : ℝ) ^ 4000 < ((X ^ 5 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
    simpa only [Real.sqrt_eq_rpow] using hlogRange
  have hlogMod := paper95_log_modulus_bound_of_nat_fifth_power_scale X d hdPos hd hceil
  have hcut :=
    paper95_cutoff_range_of_nat_fifth_power_scale X d hXlarge hdPos hd hlogMod hlogRangePower
  have hmin := paper95_min_modulus_power_bound_of_nat_fifth_power_scale X d hXlarge hdPos hd
  rcases hcut with ⟨hlogRange', hlogMod', hqPos, _, hsqrt, hYlower, hYupper⟩
  exact ⟨hlogRange', hlogMod', hqPos, hmin, hsqrt, hYlower, hYupper⟩

/--
Inputs: `X ≥ 82944`, `d ≤ X^2`, and a modulus `q ≤ 4d`.

Claim: the `18 * sqrt y` error condition holds at the AGP scale `y = d * X^3`.

Proof: convert the modulus-square estimate into the uniform progression error
bound proved above.

Role: this supplies the error hypothesis for the weighted-to-prime-count
conversion at the fixed AGP scale.
-/
theorem progressionTheta_error_bound_of_agp_fifth_power_scale (X d q : ℕ) (hX : 82944 ≤ X)
    (hd : d ≤ X ^ 2) (hq : q ≤ 4 * d) :
    72 * (Nat.totient q : ℝ) * Real.sqrt ((d * X ^ 3 : ℕ) : ℝ) ≤ ((d * X ^ 3 : ℕ) : ℝ) := by
  have hmodNat := progressionTheta_modulus_square_bound_of_agp_fifth_power_scale X d q hX hd hq
  have hmodulus : (72 * (q : ℝ)) ^ 2 ≤ ((d * X ^ 3 : ℕ) : ℝ) := by exact_mod_cast hmodNat
  exact progressionTheta_error_bound_of_modulus_square_bound (d * X ^ 3) q hmodulus

/--
Inputs: `X ≥ 82944`, `1 ≤ d ≤ X^2`, a positive modulus `q ≤ 4d`, and the
expected half-main-term lower bound for the progression theta sum.

Claim: at `y = d * X^3`, the progression prime count is at least
`y / (4 * φ(q) * log y)`.

Proof: the scale assumptions give `y ≥ 2` and `(72q)^2 ≤ y`; the modulus-bound
conversion then supplies the prime-count lower bound.

Role: this is the fixed-scale application of the weighted progression bridge
needed for the divisor progressions in AGP.
-/
theorem primeCountInProgression_ge_main_term_of_theta_lower_agp_fifth_power_scale (X d q a : ℕ)
    (hX : 82944 ≤ X) (hdPos : 0 < d) (hd : d ≤ X ^ 2) (hqPos : 0 < q) (hq : q ≤ 4 * d)
    (htheta :
      ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient q : ℝ)) ≤
        thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) q a) :
    ((((d * X ^ 3 : ℕ) : ℝ) / (4 * (Nat.totient q : ℝ))) / Real.log ((d * X ^ 3 : ℕ) : ℝ)) ≤
      (primeCountInProgression (d * X ^ 3) q a : ℝ) := by
  have hXtwo : 2 ≤ X := le_trans (by norm_num only : 2 ≤ 82944) hX
  have hXcube : 2 ≤ X ^ 3 := by
    calc
      2 ≤ 2 ^ 3 := by norm_num only
      _ ≤ X ^ 3 := Nat.pow_le_pow_left hXtwo 3
  have hdOne : 1 ≤ d := Nat.succ_le_iff.mpr hdPos
  have hy : 2 ≤ d * X ^ 3 := by
    have hmul : X ^ 3 ≤ d * X ^ 3 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (X ^ 3) hdOne
    exact le_trans hXcube hmul
  have hmodNat := progressionTheta_modulus_square_bound_of_agp_fifth_power_scale X d q hX hd hq
  have hmodulus : (72 * (q : ℝ)) ^ 2 ≤ ((d * X ^ 3 : ℕ) : ℝ) := by exact_mod_cast hmodNat
  exact
    primeCountInProgression_ge_main_term_of_theta_lower_of_modulus_bound (d * X ^ 3) q a hy hqPos
      hmodulus htheta

/--
Inputs: `X ≥ 2` and positive `d` and `m`.

Claim: the main term at `y = d * X^3`, with modulus `d * m`, divided by 36,
is at least `X^3 / (36 * m * log (X^5))`.

Proof: bound `φ(d*m)` by `d*m`, use `log (d*X^3) ≤ log (X^5)`, and cancel
the positive common logarithm and factor 36.

Role: this is the uniform coefficient needed to pass the fixed-scale
progression estimates to the finite averaging theorem.
-/
theorem agp_fifth_power_main_term_over_36_lower (X d m : ℕ) (hX : 2 ≤ X) (hdPos : 0 < d)
    (hmPos : 0 < m) :
    (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) / 36 ≤
      ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) / 36 := by
  have hXfive : 1 < X ^ 5 := by
    calc
      1 < 2 := by norm_num only
      _ ≤ X ^ 5 := le_trans hX (Nat.le_self_pow (by norm_num only : 5 ≠ 0) X)
  have hlogPos : 0 < Real.log ((X ^ 5 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hXfive)
  have hmPosReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmPos
  have hphiPos : (0 : ℝ) < (Nat.totient (d * m) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hdPos hmPos)
  have hphiBound : (Nat.totient (d * m) : ℝ) ≤ (d : ℝ) * (m : ℝ) := by
    calc
      (Nat.totient (d * m) : ℝ) ≤ ((d * m : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le (d * m)
      _ = (d : ℝ) * (m : ℝ) := by norm_num only [Nat.cast_mul]
  have hratio : (X : ℝ) ^ 3 / (m : ℝ) ≤ ((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ) := by
    apply (div_le_div_iff₀ hmPosReal hphiPos).2
    calc
      (X : ℝ) ^ 3 * (Nat.totient (d * m) : ℝ) ≤ (X : ℝ) ^ 3 * ((d : ℝ) * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hphiBound (pow_nonneg (by exact_mod_cast Nat.zero_le X) 3)
      _ = ((d * X ^ 3 : ℕ) : ℝ) * (m : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_pow]
        ring
  calc
    ((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ) / 36 ≤
        ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) / 36 :=
      by
      exact
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hratio (le_of_lt hlogPos))
          (by norm_num only)

/--
Purpose: name the prime-count coefficient after absorbing a `1 / 1000000`
fraction of the main term for higher prime powers.

Definition: `1 / 2 - 1 / 1000000`.

Role: this is the raw progression coefficient before excluding prime factors
of the auxiliary modulus.
-/
noncomputable def agpFifthPowerRawPrimeCountCoefficient : ℝ :=
  (1 / 2 : ℝ) - 1 / 1000000

/--
Purpose: compute the finite-average coefficient from the reciprocal-prime sum
bound for the auxiliary modulus.

Definition: subtract `(40 / 3) * reciprocalBound` from the raw prime-count
coefficient, reflecting the Brun–Titchmarsh contribution of bad quotients.

Inputs: a real upper bound for the sum of reciprocal prime factors.

Output: the coefficient left after removing the corresponding bad-prime
contribution.

Role: this allows the finite average to use any established reciprocal-sum
bound; the reliable Proposition 1.5 threshold `1 / 60` gives the fixed
fifth-power coefficient below.
-/
noncomputable def agpFifthPowerAverageCoefficientOfReciprocalBound (reciprocalBound : ℝ) : ℝ :=
  agpFifthPowerRawPrimeCountCoefficient - (40 / 3) * reciprocalBound

/--
Purpose: compute the average coefficient after removing bad quotient primes.

Definition: subtract the bad quotient coefficient times the reciprocal-prime
sum bound from the raw prime-count coefficient.

Role: lets the finite progression argument use an unconditional progression
bound with a coefficient different from the classical Brun–Titchmarsh value.
-/
noncomputable def agpFifthPowerAverageCoefficientOfProgressionBound
    (progressionCoefficient reciprocalBound : ℝ) : ℝ :=
  agpFifthPowerRawPrimeCountCoefficient - progressionCoefficient * reciprocalBound

/--
Inputs: the progression-sieve coefficient `640 / 3` and reciprocal-prime sum bound `1 / 1024`.
Claim: the resulting fifth-power average coefficient is exactly
`7 / 24 - 1 / 1000000`.
Proof: unfold the coefficient definitions and normalize the rational arithmetic.
Role: records the numerical value used to establish the strict exceptional-loss margin.
-/
theorem agp_fifth_power_average_coefficient_640_1024_value :
    agpFifthPowerAverageCoefficientOfProgressionBound (640 / 3) (1 / 1024) =
      (7 / 24 - 1 / 1000000 : ℝ) := by
  norm_num only [agpFifthPowerAverageCoefficientOfProgressionBound,
    agpFifthPowerRawPrimeCountCoefficient]

/--
Claim: the coefficient `640 / 3` from the coarse progression sieve and the
reciprocal-prime sum bound `1 / 1024` leave a strict average margin above `1 / 4`.
Proof: rewrite the exact coefficient and normalize the rational comparison.
Role: supplies the strict numerical margin used by the unconditional AGP
exceptional-loss budget.
-/
theorem agp_fifth_power_average_coefficient_640_1024_gt_quarter :
    (1 / 4 : ℝ) < agpFifthPowerAverageCoefficientOfProgressionBound (640 / 3) (1 / 1024) := by
  rw [agp_fifth_power_average_coefficient_640_1024_value]
  norm_num only

/--
Purpose: name the uniform finite-average coefficient supplied by reliable
Proposition 1.5.

Definition: specialize `agpFifthPowerAverageCoefficientOfReciprocalBound` to
the reciprocal-sum threshold `1 / 60`.

Role: this coefficient is used by the fifth-power prime-supply endpoint and
the Proposition 1.5 scale comparison.
-/
noncomputable def agpFifthPowerAverageCoefficient : ℝ :=
  agpFifthPowerAverageCoefficientOfReciprocalBound (1 / 60)

/--
Purpose: name the average coefficient supplied by the improved seed reciprocal
sum bound `1 / 120`.

Definition: specialize `agpFifthPowerAverageCoefficientOfReciprocalBound` to
`1 / 120`.

Role: this is the coefficient used when the auxiliary modulus is built from
the 120-cutoff seed-prime tail.
-/
noncomputable def agpFifthPowerAverageCoefficient120 : ℝ :=
  agpFifthPowerAverageCoefficientOfReciprocalBound (1 / 120)

/--
Claim: the `1 / 120` reciprocal-sum threshold gives coefficient
`3499991 / 9000000`, which is positive and exceeds the coefficient from `1 / 60`.

Proof: unfold the coefficient definitions and normalize the rational
arithmetic.

Role: this records the numerical gain available to the generalized finite
average after the seed-tail improvement.
-/
theorem agp_fifth_power_average_coefficient120_value :
    agpFifthPowerAverageCoefficient120 = (3499991 / 9000000 : ℝ) := by
  norm_num only [agpFifthPowerAverageCoefficient120,
    agpFifthPowerAverageCoefficientOfReciprocalBound, agpFifthPowerRawPrimeCountCoefficient]

/--
Claim: the average coefficient associated with reciprocal sum `1 / 120` is
positive.

Proof: rewrite it as `3499991 / 9000000` and establish positivity.

Role: this supplies the positive coefficient hypothesis for the generalized
AGP scale and prime-supply theorems.
-/
theorem agp_fifth_power_average_coefficient120_pos : 0 < agpFifthPowerAverageCoefficient120 := by
  rw [agp_fifth_power_average_coefficient120_value]
  norm_num only

/--
Inputs: the fifth-power scale and positive divisor parameters.

Claim: `agpFifthPowerAverageCoefficient` times the uniform scale main term is
at most the same coefficient times the progression main term at `d * X^3`.

Proof: strengthen the established `1/36` comparison using the coefficient's
lower bound `1/4`.

Role: this supplies the divisor-uniform target for the sharper finite average.
-/
theorem agp_fifth_power_main_term_over_epsilon_adjusted_lower (X d m : ℕ) (hX : 2 ≤ X)
    (hdPos : 0 < d) (hmPos : 0 < m) :
    agpFifthPowerAverageCoefficient * (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      agpFifthPowerAverageCoefficient *
        ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hcoef : (1 / 4 : ℝ) ≤ agpFifthPowerAverageCoefficient := by
    norm_num only [agpFifthPowerAverageCoefficient,
      agpFifthPowerAverageCoefficientOfReciprocalBound, agpFifthPowerRawPrimeCountCoefficient]
  have hmain := agp_fifth_power_main_term_over_36_lower X d m hX hdPos hmPos
  have hscaled :=
    mul_le_mul_of_nonneg_left hmain
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 36)
        (le_trans (by norm_num only : (0 : ℝ) ≤ 1 / 4) hcoef))
  convert hscaled using 1 <;> ring

/-
Inputs: the fifth-power scale `X^5`, positive divisor parameters `d` and `m`,
and `X ≥ 2`.

Claim: the main term at `y = d * X^3`, with modulus `d*m`, divided by 9 is
at least `X^3 / (9*m*log(X^5))`.

Proof: multiply the established `1/36` comparison by four and normalize.

Role: this is the improved uniform coefficient for the finite averaging
theorem after the sharper prime-count conversion.
-/
theorem agp_fifth_power_main_term_over_9_lower (X d m : ℕ) (hX : 2 ≤ X) (hdPos : 0 < d)
    (hmPos : 0 < m) :
    (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) / 9 ≤
      ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) / 9 := by
  have hmain := agp_fifth_power_main_term_over_36_lower X d m hX hdPos hmPos
  have hscaled := mul_le_mul_of_nonneg_left hmain (by norm_num only : (0 : ℝ) ≤ 4)
  convert hscaled using 1 <;> ring

/-
Inputs: the fifth-power scale and positive divisor parameters.

Claim: the main term at `y = d * X^3`, multiplied by `2 / 9`, is at least
the uniform scale term multiplied by `2 / 9`.

Proof: multiply the `1/36` comparison by eight and normalize.

Role: this is the uniform coefficient after accounting for the `2 / 9`
exceptional prime-factor contribution.
-/
theorem agp_fifth_power_main_term_over_2_ninths_lower (X d m : ℕ) (hX : 2 ≤ X) (hdPos : 0 < d)
    (hmPos : 0 < m) :
    (2 / 9 : ℝ) * (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      (2 / 9 : ℝ) *
        ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hmain := agp_fifth_power_main_term_over_36_lower X d m hX hdPos hmPos
  have hscaled := mul_le_mul_of_nonneg_left hmain (by norm_num only : (0 : ℝ) ≤ 8)
  convert hscaled using 1 <;> ring

/-
Inputs: a prime bound `X` and the coefficient constant `c₀` from reliable
Proposition 1.5, with `18000000*c₀ ≤ 2499991*X^3`.

Claim: the Proposition 1.5 coefficient for modulus `4` and bound `X^5` is at
most `agpFifthPowerAverageCoefficient` times the uniform AGP progression
main term.

Proof: evaluate `φ(4) = 2`, use the scale inequality, and divide by the
positive logarithm.

Role: this supplies the Proposition 1.5 coefficient comparison needed when
the exceptional-loss prime set is transferred to `AGPProgressionCountData`.
-/
theorem reliableProp15Coefficient_le_agp_fifth_power_average_scale (X : ℕ) (c₀ : ℝ) (hX : 2 ≤ X)
    (hscale : 18000000 * c₀ ≤ 2499991 * (X : ℝ) ^ 3) :
    reliableProp15Coefficient c₀ 4 (X ^ 5) ≤
      agpFifthPowerAverageCoefficient * (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hXfive : 1 < X ^ 5 := by
    calc
      1 < 2 := by norm_num only
      _ ≤ X ^ 5 := le_trans hX (Nat.le_self_pow (by norm_num only : 5 ≠ 0) X)
  have hlog : 0 < Real.log ((X ^ 5 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hXfive)
  have hphi : Nat.totient 4 = 2 := by decide
  change c₀ / ((Nat.totient 4 : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) ≤ _
  rw [hphi]
  have hscaled : c₀ / 2 ≤ agpFifthPowerAverageCoefficient * ((X : ℝ) ^ 3 / 4) := by
    norm_num only [agpFifthPowerAverageCoefficient,
      agpFifthPowerAverageCoefficientOfReciprocalBound, agpFifthPowerRawPrimeCountCoefficient]
    nlinarith only [hscale]
  calc
    c₀ / (2 * Real.log ((X ^ 5 : ℕ) : ℝ)) = (c₀ / 2) / Real.log ((X ^ 5 : ℕ) : ℝ) := by ring
    _ ≤ (agpFifthPowerAverageCoefficient * ((X : ℝ) ^ 3 / 4)) / Real.log ((X ^ 5 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hscaled (le_of_lt hlog)
    _ = agpFifthPowerAverageCoefficient * (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
      ring

/-
Inputs: the scale inequality from the preceding coefficient comparison and a
positive divisor `d`.

Claim: the Proposition 1.5 coefficient is at most the per-divisor average
target used by the fifth-power prime-supply theorem.

Proof: compare it first with the uniform main term, then apply
`agp_fifth_power_main_term_over_epsilon_adjusted_lower`.

Role: this constructs the `htarget` field needed to derive the finite count
data from the AGP progression estimate.
-/
theorem reliableProp15Coefficient_le_agp_fifth_power_average_target (X d : ℕ) (c₀ : ℝ) (hX : 2 ≤ X)
    (hdPos : 0 < d) (hscale : 18000000 * c₀ ≤ 2499991 * (X : ℝ) ^ 3) :
    reliableProp15Coefficient c₀ 4 (X ^ 5) ≤
      agpFifthPowerAverageCoefficient *
        ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  exact
    le_trans (reliableProp15Coefficient_le_agp_fifth_power_average_scale X c₀ hX hscale)
      (agp_fifth_power_main_term_over_epsilon_adjusted_lower X d 4 hX hdPos (by norm_num only))

/-
Inputs: the reciprocal-prime sum bound and a scale inequality for reliable
Proposition 1.5.

Claim: the Proposition 1.5 coefficient for modulus `4` and bound `X^5` is at most the uniform
main term multiplied by the average coefficient determined by the reciprocal-prime sum bound.

Proof: reduce the totient of `4` to `2`, use the scale inequality in the numerator, and divide by
the positive logarithm.

Role: this extends the coefficient comparison to improved reciprocal-sum bounds.
-/
theorem reliableProp15Coefficient_le_agp_average_scale_of_reciprocal_bound (X : ℕ)
    (c₀ reciprocalBound : ℝ) (hX : 2 ≤ X)
    (hscale :
      2 * c₀ ≤ agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound * (X : ℝ) ^ 3) :
    reliableProp15Coefficient c₀ 4 (X ^ 5) ≤
      agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound *
        (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hXfive : 1 < X ^ 5 := by
    calc
      1 < 2 := by norm_num only
      _ ≤ X ^ 5 := le_trans hX (Nat.le_self_pow (by norm_num only : 5 ≠ 0) X)
  have hlog : 0 < Real.log ((X ^ 5 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hXfive)
  have hphi : Nat.totient 4 = 2 := by decide
  change c₀ / ((Nat.totient 4 : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) ≤ _
  rw [hphi]
  have hscaled :
    c₀ / 2 ≤
      agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound * ((X : ℝ) ^ 3 / 4) := by
    nlinarith only [hscale]
  calc
    c₀ / (2 * Real.log ((X ^ 5 : ℕ) : ℝ)) = (c₀ / 2) / Real.log ((X ^ 5 : ℕ) : ℝ) := by ring
    _ ≤
        (agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound * ((X : ℝ) ^ 3 / 4)) /
          Real.log ((X ^ 5 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hscaled (le_of_lt hlog)
    _ =
        agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound *
          (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) :=
      by ring

/--
Inputs: the improved reciprocal-sum coefficient and the scale condition for
Proposition 1.5.

Claim: the modulus-four Proposition 1.5 coefficient is at most the uniform
main term multiplied by `agpFifthPowerAverageCoefficient120`.

Proof: specialize the reciprocal-bound comparison to `1 / 120`.

Role: this is the explicit scale comparison for the improved seed-tail bound.
-/
theorem reliableProp15Coefficient_le_agp_average_scale120 (X : ℕ) (c₀ : ℝ) (hX : 2 ≤ X)
    (hscale : 2 * c₀ ≤ agpFifthPowerAverageCoefficient120 * (X : ℝ) ^ 3) :
    reliableProp15Coefficient c₀ 4 (X ^ 5) ≤
      agpFifthPowerAverageCoefficient120 * (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  apply reliableProp15Coefficient_le_agp_average_scale_of_reciprocal_bound X c₀ (1 / 120) hX
  simpa only [agpFifthPowerAverageCoefficient120] using hscale

/-
Inputs: a positive reciprocal-bound-dependent average coefficient and a positive divisor.

Claim: the uniform main term, scaled by that coefficient, is at most the corresponding
progression main term at `d * X^3`.

Proof: scale `agp_fifth_power_main_term_over_36_lower` by the nonnegative coefficient `36 * beta`
and normalize.

Role: this transfers a generalized Proposition 1.5 scale comparison to each divisor.
-/
theorem agp_fifth_power_main_term_lower_of_reciprocal_bound (X d : ℕ) (reciprocalBound : ℝ)
    (hX : 2 ≤ X) (hdPos : 0 < d)
    (hcoeff : 0 < agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound) :
    agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound *
        (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound *
        ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hmain := agp_fifth_power_main_term_over_36_lower X d 4 hX hdPos (by norm_num only)
  have hscaled :=
    mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 36) (le_of_lt hcoeff))
  convert hscaled using 1 <;> ring

/-
Inputs: a positive reciprocal-bound-dependent average coefficient and positive
divisor and modulus parameters.

Claim: the uniform fifth-power main term at modulus `m`, scaled by that
coefficient, is at most the progression main term at `d * X^3` and modulus
`d * m`.

Proof: scale `agp_fifth_power_main_term_over_36_lower` by `36 * beta` and
normalize.

Role: this provides the divisor comparison for the general residue-class
finite average.
-/
theorem agp_fifth_power_main_term_over_average_lower_of_reciprocal_bound (X d m : ℕ)
    (reciprocalBound : ℝ) (hX : 2 ≤ X) (hdPos : 0 < d) (hmPos : 0 < m)
    (hcoeff : 0 < agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound) :
    agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound *
        (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound *
        ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hmain := agp_fifth_power_main_term_over_36_lower X d m hX hdPos hmPos
  have hscaled :=
    mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 36) (le_of_lt hcoeff))
  convert hscaled using 1 <;> ring

/--
Inputs: a nonnegative progression coefficient, a reciprocal-prime sum bound,
and positive scale and divisor parameters.

Claim: the uniform fifth-power main term, multiplied by the resulting average
coefficient, is at most the corresponding progression main term.

Proof: scale the existing totient comparison by the positive average
coefficient and normalize the factor `36`.

Role: supplies the divisor comparison for coefficient-generalized
bad-quotient estimates.
-/
theorem agp_fifth_power_main_term_over_average_lower_of_progression_bound (X d m : ℕ)
    (progressionCoefficient reciprocalBound : ℝ) (hX : 2 ≤ X) (hdPos : 0 < d) (hmPos : 0 < m)
    (hcoeff :
      0 <
        agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound) :
    agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
        (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
        ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hmain := agp_fifth_power_main_term_over_36_lower X d m hX hdPos hmPos
  have hscaled :=
    mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 36) (le_of_lt hcoeff))
  convert hscaled using 1 <;> ring

/-
Inputs: the scale, the positive coefficient from a reciprocal-prime bound, and the numerator
comparison for reliable Proposition 1.5.

Claim: the Proposition 1.5 coefficient is at most the per-divisor target used by the generalized
finite average.

Proof: compare with the uniform term, then apply the divisor main-term bound.

Role: this supplies the generalized `htarget` field for the prime-set construction.
-/
theorem reliableProp15Coefficient_le_agp_average_target_of_reciprocal_bound (X d : ℕ)
    (c₀ reciprocalBound : ℝ) (hX : 2 ≤ X) (hdPos : 0 < d)
    (hcoeff : 0 < agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound)
    (hscale :
      2 * c₀ ≤ agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound * (X : ℝ) ^ 3) :
    reliableProp15Coefficient c₀ 4 (X ^ 5) ≤
      agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound *
        ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  exact
    le_trans
      (reliableProp15Coefficient_le_agp_average_scale_of_reciprocal_bound X c₀ reciprocalBound hX
        hscale)
      (agp_fifth_power_main_term_lower_of_reciprocal_bound X d reciprocalBound hX hdPos hcoeff)

/--
Inputs: the improved reciprocal-sum coefficient, the scale condition, and a
positive divisor parameter.

Claim: the modulus-four Proposition 1.5 coefficient is at most the
per-divisor average target for the `1 / 120` seed-tail bound.

Proof: combine the uniform scale comparison with the divisor main-term
comparison at reciprocal bound `1 / 120`.

Role: this supplies the divisor-wise target required by the finite
prime-supply theorem for the improved seed construction.
-/
theorem reliableProp15Coefficient_le_agp_average_target120 (X d : ℕ) (c₀ : ℝ) (hX : 2 ≤ X)
    (hdPos : 0 < d) (hscale : 2 * c₀ ≤ agpFifthPowerAverageCoefficient120 * (X : ℝ) ^ 3) :
    reliableProp15Coefficient c₀ 4 (X ^ 5) ≤
      agpFifthPowerAverageCoefficient120 *
        ((((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  exact
    reliableProp15Coefficient_le_agp_average_target_of_reciprocal_bound X d c₀ (1 / 120) hX hdPos
      (by
        simpa only [agpFifthPowerAverageCoefficient120] using
          agp_fifth_power_average_coefficient120_pos)
      (by simpa only [agpFifthPowerAverageCoefficient120] using hscale)

/-
Inputs: the reliable Proposition 1.5 coefficient and a reciprocal-bound
parameter whose average coefficient is positive.

Claim: beyond an explicit threshold, the paper95 fifth-power scale and the
generalized coefficient comparison both hold for every larger `X`.

Proof: take the ceiling of the square root of the positive part of
`2*c₀ / beta`, then compare `X^2` with `X^3`.

Role: this gives an eventual scale gate for each fixed reciprocal-sum bound.
-/
theorem exists_eventual_agp_average_coefficient_scale_of_reciprocal_bound (c₀ reciprocalBound : ℝ)
    (hcoeff : 0 < agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound) :
    ∃ X₀ : ℕ,
      ∀ X : ℕ,
        X₀ ≤ X →
          2 ^ 56 ≤ X ∧
            2 * c₀ ≤
              agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound * (X : ℝ) ^ 3 := by
  let beta := agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound
  let A : ℝ := max 0 ((2 * c₀) / beta)
  refine ⟨max (2 ^ 56) (Nat.ceil (Real.sqrt A)), ?_⟩
  intro X hX
  have hscaleNat : Nat.ceil (Real.sqrt A) ≤ X := le_trans (Nat.le_max_right (2 ^ 56) _) hX
  have hceil : (Nat.ceil (Real.sqrt A) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hscaleNat
  have hroot : Real.sqrt A ≤ (X : ℝ) := le_trans (Nat.le_ceil (Real.sqrt A)) hceil
  have hA_nonneg : 0 ≤ A := le_max_left 0 _
  have hA_scaled : (2 * c₀) / beta ≤ A := le_max_right 0 _
  have hAsq : A ≤ (X : ℝ) ^ 2 := by
    rw [← Real.sq_sqrt hA_nonneg]
    nlinarith only [hroot, Real.sqrt_nonneg A]
  have hXlarge : 2 ^ 56 ≤ X := le_trans (Nat.le_max_left (2 ^ 56) _) hX
  have hXtwo : 2 ≤ X := le_trans (by norm_num only) hXlarge
  have hXreal : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXtwo
  have hXone : (1 : ℝ) ≤ (X : ℝ) := le_trans (by norm_num only) hXreal
  have hXsqNonneg : 0 ≤ (X : ℝ) ^ 2 := sq_nonneg (X : ℝ)
  have hXsqCube : (X : ℝ) ^ 2 ≤ (X : ℝ) ^ 3 := by
    calc
      (X : ℝ) ^ 2 = 1 * (X : ℝ) ^ 2 := by ring
      _ ≤ (X : ℝ) * (X : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hXone hXsqNonneg
      _ = (X : ℝ) ^ 3 := by ring
  have hAcube : A ≤ (X : ℝ) ^ 3 := le_trans hAsq hXsqCube
  have hratio : (2 * c₀) / beta ≤ (X : ℝ) ^ 3 := le_trans hA_scaled hAcube
  have hscale : 2 * c₀ ≤ (X : ℝ) ^ 3 * beta := (div_le_iff₀ hcoeff).1 hratio
  have hscale' :
    2 * c₀ ≤ agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound * (X : ℝ) ^ 3 := by
    simpa only [beta, mul_comm] using hscale
  exact ⟨hXlarge, hscale'⟩

/-
Inputs: the coefficient constant `c₀` from reliable Proposition 1.5.

Claim: beyond an explicit natural threshold, both the paper95 fifth-power
scale `X ≥ 2^56` and the coefficient comparison hypothesis
`18000000*c₀ ≤ 2499991*X^3` hold.

Proof: take the maximum of `2^56` and the ceiling of
the square root of `max 0 ((18000000 / 2499991) * c₀)`, then compare
its square with `X^2` and use `X^2 ≤ X^3` for `X ≥ 2`.

Role: this removes the scale comparison as a separate eventuality condition
when `c₀` has been fixed by Proposition 1.5.
-/
theorem exists_eventual_agp_fifth_power_prop15_coefficient_scale (c₀ : ℝ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → 2 ^ 56 ≤ X ∧ 18000000 * c₀ ≤ 2499991 * (X : ℝ) ^ 3 := by
  let A : ℝ := max 0 ((18000000 / 2499991) * c₀)
  refine ⟨max (2 ^ 56) (Nat.ceil (Real.sqrt A)), ?_⟩
  intro X hX
  have hscaleNat : Nat.ceil (Real.sqrt A) ≤ X := le_trans (Nat.le_max_right (2 ^ 56) _) hX
  have hceil : (Nat.ceil (Real.sqrt A) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hscaleNat
  have hroot : Real.sqrt A ≤ (X : ℝ) := le_trans (Nat.le_ceil (Real.sqrt A)) hceil
  have hA_nonneg : 0 ≤ A := le_max_left 0 _
  have hA_scaled : (18000000 / 2499991) * c₀ ≤ A := le_max_right 0 _
  have hAsq : A ≤ (X : ℝ) ^ 2 := by
    rw [← Real.sq_sqrt hA_nonneg]
    nlinarith only [hroot, Real.sqrt_nonneg A]
  have hXlarge : 2 ^ 56 ≤ X := le_trans (Nat.le_max_left (2 ^ 56) _) hX
  have hXtwo : 2 ≤ X := le_trans (by norm_num only) hXlarge
  have hXreal : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXtwo
  have hXone : (1 : ℝ) ≤ (X : ℝ) := le_trans (by norm_num only) hXreal
  have hXsqNonneg : 0 ≤ (X : ℝ) ^ 2 := sq_nonneg (X : ℝ)
  have hXsqCube : (X : ℝ) ^ 2 ≤ (X : ℝ) ^ 3 := by
    calc
      (X : ℝ) ^ 2 = 1 * (X : ℝ) ^ 2 := by ring
      _ ≤ (X : ℝ) * (X : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hXone hXsqNonneg
      _ = (X : ℝ) ^ 3 := by ring
  have hAcube : A ≤ (X : ℝ) ^ 3 := le_trans hAsq hXsqCube
  have hscale : 18000000 * c₀ ≤ 2499991 * (X : ℝ) ^ 3 := by
    dsimp [A] at hA_nonneg hA_scaled hAcube ⊢
    nlinarith only [hA_nonneg, hA_scaled, hAcube]
  exact ⟨hXlarge, hscale⟩

/--
Inputs: a scale `X`, a positive divisor parameter `d`, positive moduli `q,m`,
and the bounds `d ≤ X^2`, `q ≤ m*d`, and `4*m*c₀ ≤ X^3`.

Claim: at `x = X^5` and `y = d*X^3`, the main term
`y / (4 * φ(q) * log y)` dominates the reliable Proposition 1.5
coefficient `c₀ / (φ(m) * log x)`.

Proof: use `φ(q) ≤ q ≤ m*d`, `1 ≤ φ(m)`, and `log y ≤ log x`; the
remaining numerator comparison is the scale hypothesis.

Role: this discharges the coefficient comparison needed by the per-divisor
weighted-to-prime-count estimate below.
-/
theorem prop15_coefficient_le_progression_main_term_agp_fifth_power_scale (X d q m : ℕ) (c₀ : ℝ)
    (hX : 82944 ≤ X) (hdPos : 0 < d) (hd : d ≤ X ^ 2) (hqPos : 0 < q) (hq : q ≤ m * d)
    (hmPos : 0 < m) (hc₀ : 0 < c₀) (hscale : 4 * (m : ℝ) * c₀ ≤ (X : ℝ) ^ 3) :
    c₀ / ((Nat.totient m : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      (((d * X ^ 3 : ℕ) : ℝ) / (4 * (Nat.totient q : ℝ))) / Real.log ((d * X ^ 3 : ℕ) : ℝ) := by
  have hXtwo : 2 ≤ X := le_trans (by norm_num only : 2 ≤ 82944) hX
  have hXcube : 2 ≤ X ^ 3 := by
    calc
      2 ≤ 2 ^ 3 := by norm_num only
      _ ≤ X ^ 3 := Nat.pow_le_pow_left hXtwo 3
  have hdOne : 1 ≤ d := Nat.succ_le_iff.mpr hdPos
  have hy : 2 ≤ d * X ^ 3 := by
    have hmul : X ^ 3 ≤ d * X ^ 3 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (X ^ 3) hdOne
    exact le_trans hXcube hmul
  have hXfive : 1 < X ^ 5 := by
    calc
      1 < 2 := by norm_num only
      _ ≤ X ^ 5 := le_trans hXtwo (Nat.le_self_pow (by norm_num only : 5 ≠ 0) X)
  have hxLogPos : 0 < Real.log ((X ^ 5 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hXfive)
  have hyLogPos : 0 < Real.log ((d * X ^ 3 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hy))
  have hcut : d * X ^ 3 ≤ X ^ 5 := by
    calc
      d * X ^ 3 ≤ X ^ 2 * X ^ 3 := Nat.mul_le_mul_right (X ^ 3) hd
      _ = X ^ 5 := by ring
  have hlogCut : Real.log ((d * X ^ 3 : ℕ) : ℝ) ≤ Real.log ((X ^ 5 : ℕ) : ℝ) :=
    Real.log_le_log
      (by
        exact_mod_cast
          (Nat.mul_pos hdPos (Nat.pow_pos (Nat.lt_of_lt_of_le (by norm_num only : 0 < 2) hXtwo))))
      (by exact_mod_cast hcut)
  have hphiMpos : 0 < (Nat.totient m : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hmPos
  have hphiMone : 1 ≤ (Nat.totient m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.totient_pos.mpr hmPos))
  have hphiQpos : 0 < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqPos
  have hphiQbound : (Nat.totient q : ℝ) ≤ (m * d : ℝ) := by
    have hphiQboundNat : Nat.totient q ≤ m * d := le_trans (Nat.totient_le q) hq
    exact_mod_cast hphiQboundNat
  have hlogProduct :
    (Nat.totient q : ℝ) * Real.log ((d * X ^ 3 : ℕ) : ℝ) ≤
      (m * d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ) :=
    mul_le_mul hphiQbound hlogCut (le_of_lt hyLogPos) (by exact_mod_cast (Nat.zero_le (m * d)))
  have hscaleNumerator : 4 * c₀ * (m : ℝ) ≤ (X : ℝ) ^ 3 := by
    calc
      4 * c₀ * (m : ℝ) = 4 * (m : ℝ) * c₀ := by ring
      _ ≤ (X : ℝ) ^ 3 := hscale
  have hfirst :
    (4 * c₀) * ((Nat.totient q : ℝ) * Real.log ((d * X ^ 3 : ℕ) : ℝ)) ≤
      (4 * c₀) * ((m * d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hlogProduct (mul_nonneg (by norm_num only) (le_of_lt hc₀))
  have hsecond :
    (4 * c₀ * (m : ℝ)) * ((d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      (X : ℝ) ^ 3 * ((d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hscaleNumerator
      (mul_nonneg (by exact_mod_cast Nat.zero_le d) (le_of_lt hxLogPos))
  have hthirdNonneg : 0 ≤ (X : ℝ) ^ 3 * (d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ) :=
    mul_nonneg
      (mul_nonneg (pow_nonneg (by exact_mod_cast Nat.zero_le X) 3)
        (by exact_mod_cast Nat.zero_le d))
      (le_of_lt hxLogPos)
  have hthird :
    (X : ℝ) ^ 3 * (d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ) ≤
      (X : ℝ) ^ 3 * (d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ) * (Nat.totient m : ℝ) := by
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left hphiMone hthirdNonneg)
  have hcross :
    c₀ * ((4 * (Nat.totient q : ℝ)) * Real.log ((d * X ^ 3 : ℕ) : ℝ)) ≤
      ((d * X ^ 3 : ℕ) : ℝ) * ((Nat.totient m : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) := by
    calc
      c₀ * ((4 * (Nat.totient q : ℝ)) * Real.log ((d * X ^ 3 : ℕ) : ℝ)) =
          (4 * c₀) * ((Nat.totient q : ℝ) * Real.log ((d * X ^ 3 : ℕ) : ℝ)) :=
        by ring
      _ ≤ (4 * c₀) * ((m * d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) := hfirst
      _ = (4 * c₀ * (m : ℝ)) * ((d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) := by ring
      _ ≤ (X : ℝ) ^ 3 * ((d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) := hsecond
      _ = (X : ℝ) ^ 3 * (d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ) := by ring
      _ ≤ ((X : ℝ) ^ 3 * (d : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) * (Nat.totient m : ℝ) := hthird
      _ = ((d * X ^ 3 : ℕ) : ℝ) * ((Nat.totient m : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) := by
        rw [Nat.cast_mul, Nat.cast_pow]
        rw [Nat.cast_pow]
        ring_nf
  rw [div_div]
  apply
    (div_le_div_iff₀ (mul_pos hphiMpos hxLogPos)
        (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 4) hphiQpos) hyLogPos)).2
  exact hcross

/--
Inputs: a fifth-power prime bound `X^5`, a divisor scale `d`, a CRT modulus
`q ≤ 4d` and `q ≤ m * d`, the scale comparison `4 * m * c₀ ≤ X^3`, and a
theta lower bound at `y = d * X^3`.

Claim: the theta lower bound implies that the progression count dominates the
reliable Proposition 1.5 coefficient. The scale comparison and totient/log
bounds prove the required coefficient comparison internally.

Role: this is the per-divisor estimate to sum before applying the finite
averaging lemma for the Proposition 1.5 parameter `k`.
-/
theorem primeCountInProgression_ge_prop15_coefficient_of_theta_lower_agp_scale (X d q a m : ℕ)
    (c₀ : ℝ) (hX : 82944 ≤ X) (hdPos : 0 < d) (hd : d ≤ X ^ 2) (hqPos : 0 < q) (hq : q ≤ 4 * d)
    (hqMul : q ≤ m * d) (hmPos : 0 < m) (hc₀ : 0 < c₀) (hscale : 4 * (m : ℝ) * c₀ ≤ (X : ℝ) ^ 3)
    (htheta :
      ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient q : ℝ)) ≤
        thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) q a) :
    c₀ / ((Nat.totient m : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      (primeCountInProgression (d * X ^ 3) q a : ℝ) := by
  have hcoef :=
    prop15_coefficient_le_progression_main_term_agp_fifth_power_scale X d q m c₀ hX hdPos hd hqPos
      hqMul hmPos hc₀ hscale
  exact
    le_trans hcoef
      (primeCountInProgression_ge_main_term_of_theta_lower_agp_fifth_power_scale X d q a hX hdPos hd
        hqPos hq htheta)

/-
Purpose: count primes in the CRT progression whose quotient by `d` is not
coprime to `L`.

Definition: count primes up to `x` in the simultaneous classes `1 mod d` and
`l mod m` for which `((p - 1) / d)` shares a factor with `L`.

Role: this is the discarded contribution that must be bounded before the
unrestricted progression estimate can feed the coprime-quotient average.
-/
def badQuotientPrimeCountInProgression (x d m l L : ℕ) (hdm : Nat.Coprime d m) : ℕ :=
  ((Finset.range (x + 1)).filter
      (fun p =>
        Nat.Prime p ∧
          p % (d * m) = progressionCoprimeResidue d m l hdm % (d * m) ∧
          ¬Nat.Coprime ((p - 1) / d) L)).card

/--
Inputs: a progression bound, coprime moduli `d,m`, coprime residue `l`, and a
nonzero integer `L`.

Claim: the number of progression primes whose quotient is not coprime to `L`
is at most the sum, over prime factors `q` of `L`, of the prime counts in the
class `1 mod (d*q)`.

Proof: each discarded prime has a prime factor `q` shared by its quotient and
`L`, so it lies in the corresponding progression modulo `d*q`. Bound the
finite union by the sum of its cardinalities.

Role: this is the finite union bound matching the bad-prime subtraction on
paper95, page 14.
-/
theorem badQuotientPrimeCountInProgression_le_sum_prime_factor_progressions (x d m l L : ℕ)
    (hd : 0 < d) (hL : L ≠ 0) (hdm : Nat.Coprime d m) (hlm : Nat.Coprime l m) :
    badQuotientPrimeCountInProgression x d m l L hdm ≤
      ∑ q ∈ L.primeFactors, primeCountInProgression x (d * q) 1 := by
  classical
  let Bad :=
    (Finset.range (x + 1)).filter
      (fun p =>
        Nat.Prime p ∧
          p % (d * m) = progressionCoprimeResidue d m l hdm % (d * m) ∧
          ¬Nat.Coprime ((p - 1) / d) L)
  let C : ℕ → Finset ℕ := fun q =>
    (Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p % (d * q) = 1 % (d * q))
  have hsubset : Bad ⊆ L.primeFactors.biUnion C := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have hpPrime := hp'.1
    have hcrt := hp'.2.1
    have hbad := hp'.2.2
    have hmods := (progressionCoprimeResidue_modEq_iff d m l p hdm hlm).mp hcrt
    obtain ⟨k, hfactor, _⟩ := exists_factorization_of_residue_one p d hpPrime.two_le hd hmods.1
    have hquot : (p - 1) / d = k := by
      rw [hfactor, Nat.add_sub_cancel_right]
      exact Nat.mul_div_right k hd
    have hgcd : Nat.gcd k L ≠ 1 := by
      intro heq
      apply hbad
      rw [hquot, Nat.coprime_iff_gcd_eq_one]
      exact heq
    obtain ⟨q, hqPrime, hqGcd⟩ := Nat.exists_prime_and_dvd hgcd
    have hqk : q ∣ k := Nat.dvd_trans hqGcd (Nat.gcd_dvd_left k L)
    have hqL : q ∣ L := Nat.dvd_trans hqGcd (Nat.gcd_dvd_right k L)
    have hqMem : q ∈ L.primeFactors := Nat.mem_primeFactors.mpr ⟨hqPrime, hqL, hL⟩
    have hdqDiv : d * q ∣ p - 1 := by
      rw [hfactor, Nat.add_sub_cancel_right]
      exact Nat.mul_dvd_mul_left d hqk
    have hpModDq : p % (d * q) = 1 % (d * q) := by
      calc
        p % (d * q) = ((p - 1) + 1) % (d * q) := by
          rw [Nat.sub_add_cancel (le_trans (by decide : 1 ≤ 2) hpPrime.two_le)]
        _ = (((p - 1) % (d * q) + 1 % (d * q)) % (d * q)) := Nat.add_mod _ _ _
        _ = 1 % (d * q) := by
          rw [Nat.mod_eq_zero_of_dvd hdqDiv]
          simp only [Nat.zero_add, Nat.mod_mod]
    have hpRange := (Finset.mem_filter.mp hp).1
    have hpC : p ∈ C q := by
      simp only [C, Finset.mem_filter]
      exact ⟨hpRange, hpPrime, hpModDq⟩
    exact Finset.mem_biUnion.mpr ⟨q, hqMem, hpC⟩
  calc
    badQuotientPrimeCountInProgression x d m l L hdm = Bad.card := rfl
    _ ≤ (L.primeFactors.biUnion C).card := Finset.card_le_card hsubset
    _ ≤ ∑ q ∈ L.primeFactors, (C q).card := Finset.card_biUnion_le
    _ = ∑ q ∈ L.primeFactors, primeCountInProgression x (d * q) 1 := by
      apply Finset.sum_congr rfl
      intro q hq
      rfl

/-
Inputs: coprime moduli `d,m`, a residue `l`, a nonzero modulus candidate `L`,
and coprimality of `L` and `m`.

Claim: the bad-quotient primes are bounded by the sum of progression counts
modulo `d*q*m`, with the CRT residue enforcing both source classes.

Proof: each bad quotient has a prime factor `q ∣ L`; then `p ≡ 1 mod d*q`
and `p ≡ l mod m`. Coprimality of `L` and `m` lets the CRT residue combine
these congruences before applying the finite union bound.

Role: this retains the residue restriction modulo `m` in the
Brun–Titchmarsh input used to remove bad quotients.
-/
theorem badQuotientPrimeCountInProgression_le_sum_prime_factor_crt_progressions (x d m l L : ℕ)
    (hd : 0 < d) (hL : L ≠ 0) (hdm : Nat.Coprime d m) (hlm : Nat.Coprime l m)
    (hLm : Nat.Coprime L m) :
    badQuotientPrimeCountInProgression x d m l L hdm ≤
      ∑ q ∈ L.primeFactors.attach,
        primeCountInProgression x (d * q.val * m)
          (progressionCoprimeResidue (d * q.val) m l
            (by
              have hqL : q.val ∣ L := (Nat.mem_primeFactors.mp q.property).2.1
              exact Nat.Coprime.mul_left hdm (Nat.Coprime.of_dvd_left hqL hLm))) := by
  classical
  let Bad :=
    (Finset.range (x + 1)).filter
      (fun p =>
        Nat.Prime p ∧
          p % (d * m) = progressionCoprimeResidue d m l hdm % (d * m) ∧
          ¬Nat.Coprime ((p - 1) / d) L)
  let C : { q // q ∈ L.primeFactors } → Finset ℕ := fun q =>
    (Finset.range (x + 1)).filter
      (fun p =>
        Nat.Prime p ∧
          p % (d * q.val * m) =
            progressionCoprimeResidue (d * q.val) m l
                (Nat.Coprime.mul_left hdm
                  (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm)) %
              (d * q.val * m))
  have hsubset : Bad ⊆ L.primeFactors.attach.biUnion C := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have hpPrime := hp'.1
    have hcrt := hp'.2.1
    have hbad := hp'.2.2
    have hmods := (progressionCoprimeResidue_modEq_iff d m l p hdm hlm).mp hcrt
    obtain ⟨k, hfactor, _⟩ := exists_factorization_of_residue_one p d hpPrime.two_le hd hmods.1
    have hquot : (p - 1) / d = k := by
      rw [hfactor, Nat.add_sub_cancel_right]
      exact Nat.mul_div_right k hd
    have hgcd : Nat.gcd k L ≠ 1 := by
      intro heq
      apply hbad
      rw [hquot, Nat.coprime_iff_gcd_eq_one]
      exact heq
    obtain ⟨q, hqPrime, hqGcd⟩ := Nat.exists_prime_and_dvd hgcd
    have hqk : q ∣ k := Nat.dvd_trans hqGcd (Nat.gcd_dvd_left k L)
    have hqL : q ∣ L := Nat.dvd_trans hqGcd (Nat.gcd_dvd_right k L)
    have hqMem : q ∈ L.primeFactors := Nat.mem_primeFactors.mpr ⟨hqPrime, hqL, hL⟩
    have hqm : Nat.Coprime q m := Nat.Coprime.of_dvd_left hqL hLm
    have hdmq : Nat.Coprime (d * q) m := Nat.Coprime.mul_left hdm hqm
    have hdqDiv : d * q ∣ p - 1 := by
      rw [hfactor, Nat.add_sub_cancel_right]
      exact Nat.mul_dvd_mul_left d hqk
    have hpModDq : p % (d * q) = 1 % (d * q) := by
      calc
        p % (d * q) = ((p - 1) + 1) % (d * q) := by
          rw [Nat.sub_add_cancel (le_trans (by decide : 1 ≤ 2) hpPrime.two_le)]
        _ = (((p - 1) % (d * q) + 1 % (d * q)) % (d * q)) := Nat.add_mod _ _ _
        _ = 1 % (d * q) := by
          rw [Nat.mod_eq_zero_of_dvd hdqDiv]
          simp only [Nat.zero_add, Nat.mod_mod]
    have hpRange := (Finset.mem_filter.mp hp).1
    let q' : { q // q ∈ L.primeFactors } := ⟨q, hqMem⟩
    have hpClass :
      p % (d * q' * m) = progressionCoprimeResidue (d * q') m l hdmq % (d * q' * m) := by
      exact (progressionCoprimeResidue_modEq_iff (d * q') m l p hdmq hlm).mpr ⟨hpModDq, hmods.2⟩
    have hpC : p ∈ C q' := by
      simp only [C, Finset.mem_filter]
      exact ⟨hpRange, hpPrime, hpClass⟩
    exact Finset.mem_biUnion.mpr ⟨q', Finset.mem_attach L.primeFactors q', hpC⟩
  calc
    badQuotientPrimeCountInProgression x d m l L hdm = Bad.card := rfl
    _ ≤ (L.primeFactors.attach.biUnion C).card := Finset.card_le_card hsubset
    _ ≤ ∑ q ∈ L.primeFactors.attach, (C q).card := Finset.card_biUnion_le
    _ =
        ∑ q ∈ L.primeFactors.attach,
          primeCountInProgression x (d * q.val * m)
            (progressionCoprimeResidue (d * q.val) m l
              (Nat.Coprime.mul_left hdm
                (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :=
      by
      apply Finset.sum_congr rfl
      intro q hq
      rfl

/--
Inputs: coprime moduli `d` and `m`, a residue `l`, a quotient coprimality
modulus `L`, and a lower bound for the CRT progression count with an additive
allowance for primes whose quotient is not coprime to `L`.

Claim: after removing that bad-prime allowance, the same lower bound holds for
`primeCountInProgressionWithCoprimeQuotient`.

Proof: partition the exact CRT progression into quotients coprime to `L` and
those not coprime to `L`, then use the assumed bound for their total count.

Role: this is the finite interface needed to turn the theta estimate into the
coprime-quotient counts summed by the Proposition 1.5 averaging argument.
-/
theorem primeCountInProgressionWithCoprimeQuotient_ge_of_crt_count (x d m l L : ℕ) (c : ℝ)
    (hdm : Nat.Coprime d m) (hlm : Nat.Coprime l m)
    (hraw :
      c + (badQuotientPrimeCountInProgression x d m l L hdm : ℝ) ≤
        (primeCountInProgression x (d * m) (progressionCoprimeResidue d m l hdm) : ℝ)) :
    c ≤ (primeCountInProgressionWithCoprimeQuotient x d m l L : ℝ) := by
  let D :=
    (Finset.range (x + 1)).filter
      (fun p => Nat.Prime p ∧ p % (d * m) = progressionCoprimeResidue d m l hdm % (d * m))
  let G := D.filter (fun p => Nat.Coprime ((p - 1) / d) L)
  let B := D.filter (fun p => ¬Nat.Coprime ((p - 1) / d) L)
  have hrawEq : primeCountInProgression x (d * m) (progressionCoprimeResidue d m l hdm) = D.card :=
    rfl
  have hgoodEq : primeCountInProgressionWithCoprimeQuotient x d m l L = G.card := by
    rw [primeCountInProgressionWithCoprimeQuotient_eq_crt_filter x d m l L hdm hlm]
    unfold G D
    congr 1
    ext p
    simp only [Finset.mem_filter, and_assoc]
  have hbadEq : badQuotientPrimeCountInProgression x d m l L hdm = B.card := by
    unfold badQuotientPrimeCountInProgression
    unfold B D
    congr 1
    ext p
    simp only [Finset.mem_filter, and_assoc]
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := D) (p := fun p => Nat.Coprime ((p - 1) / d) L)
  have hsplitReal : (G.card : ℝ) + (B.card : ℝ) = (D.card : ℝ) := by exact_mod_cast hsplit
  rw [hbadEq, hrawEq] at hraw
  rw [← hsplitReal] at hraw
  rw [← hgoodEq] at hraw
  exact (add_le_add_iff_right (B.card : ℝ)).mp hraw

/-
Inputs: a nonnegative expected main term, an error tolerance at most one half,
and an absolute error estimate for a progression theta sum.

Claim: the theta sum is at least half of its expected main term.

Proof: use the lower half of the absolute error estimate and the tolerance
bound.

Role: this converts the relative-error conclusion of paper95 Theorem 2.1 into
the theta lower bound consumed by the finite progression-count argument.
-/
theorem theta_lower_of_relative_error_half (theta mainTerm epsilon : ℝ) (hmain : 0 ≤ mainTerm)
    (hepsilonHalf : epsilon ≤ 1 / 2) (herror : |theta - mainTerm| ≤ epsilon * mainTerm) :
    mainTerm / 2 ≤ theta := by
  have hlower : -(epsilon * mainTerm) ≤ theta - mainTerm := (abs_le.mp herror).1
  have hprod : epsilon * mainTerm ≤ mainTerm / 2 := by
    calc
      epsilon * mainTerm ≤ (1 / 2 : ℝ) * mainTerm := mul_le_mul_of_nonneg_right hepsilonHalf hmain
      _ = mainTerm / 2 := by ring
  linarith only [hlower, hprod]

/-
Inputs: a real cutoff `y`, a positive modulus `q`, a residue `a`, and a
relative-error estimate for `thetaInProgressionReal`.

Claim: if the relative error is at most one half, the progression theta sum is
at least `y / (2 * φ(q))`.

Proof: instantiate the relative-error conversion with the expected main term
`y / φ(q)` and normalize the division by two.

Role: this is the direct interface from a sufficiently strong paper95
Theorem 2.1 estimate to the theta hypothesis used in the AGP counting bridge.
-/
theorem thetaInProgressionReal_ge_half_main_term_of_relative_error (y : ℝ) (q a : ℕ) (epsilon : ℝ)
    (hmain : 0 ≤ y / (Nat.totient q : ℝ)) (hepsilonHalf : epsilon ≤ 1 / 2)
    (herror :
      |thetaInProgressionReal y q a - y / (Nat.totient q : ℝ)| ≤
        epsilon * (y / (Nat.totient q : ℝ))) :
    y / (2 * (Nat.totient q : ℝ)) ≤ thetaInProgressionReal y q a := by
  have hbound :=
    theta_lower_of_relative_error_half (thetaInProgressionReal y q a) (y / (Nat.totient q : ℝ))
      epsilon hmain hepsilonHalf herror
  calc
    y / (2 * (Nat.totient q : ℝ)) = (y / (Nat.totient q : ℝ)) / 2 := by ring
    _ ≤ thetaInProgressionReal y q a := hbound

/--
Inputs: a squarefree factor `L` coprime to `m`, a finite set `E` of exceptional
moduli none of which divides `m`, a cutoff `y`, and a uniform lower bound for
good divisors of the modulus-adjusted exceptional-free part of `L`.

Claim: there are more than `T` distinct primes in the specified progression,
each represented by a small divisor of `exceptionalFreePartForModulus L E m`;
every such divisor avoids all exceptional moduli in the actual CRT modulus
obtained by multiplying it by `m`.

Proof: transfer the scaled divisor threshold through the `2 ^ E.card` loss,
apply the existing real-count to prime-set construction theorem, and expose
the finite exceptional-modulus avoidance property.

Role: this joins modulus-aware exceptional-factor removal to the prime supply
interface used by the AGP construction.
-/
theorem exists_prime_set_from_exceptionalFreePartForModulus_real_count_lower_bound (L : ℕ)
    (E : Finset ℕ) (y k x m a T : ℕ) (hL : L ≠ 0) (hSquarefree : Squarefree L) (hE : ∀ e ∈ E, 1 < e)
    (hEm : ∀ e ∈ E, ¬e ∣ m) (hLm : Nat.Coprime L m) (hk : 0 < k) (c : ℝ) (hc : 0 ≤ c)
    (htarget : (T : ℝ) * (2 ^ E.card : ℝ) < c * ((restrictedDivisors L y).card : ℝ))
    (hanalytic :
      c * ((restrictedDivisors (exceptionalFreePartForModulus L E m) y).card : ℝ) ≤
        ((((restrictedDivisors (exceptionalFreePartForModulus L E m) y).filter
                (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :
            ℕ) :
          ℝ)) :
    ∃ P : Finset ℕ,
      T < P.card ∧
        ∀ p ∈ P,
          Nat.Prime p ∧
            p ≤ x ∧
            p % m = a % m ∧
            ∃ d,
              d ∣ exceptionalFreePartForModulus L E m ∧
                d ≤ y ∧ p = d * k + 1 ∧ ∀ e ∈ E, ¬e ∣ d * m := by
  let Q := selectedExceptionalPrimeFactorsForModulus L E m
  have hQfixed : selectedExceptionalPrimeFactors L Q = Q :=
    selectedExceptionalPrimeFactorsForModulus_fixed L E m hL
  have hL'pos : 0 < exceptionalFreePartForModulus L E m := by
    change 0 < (L.primeFactors \ selectedExceptionalPrimeFactors L Q).prod id
    rw [hQfixed]
    apply Finset.prod_pos
    intro p hp
    exact ((Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1).pos
  have hlower :=
    exists_lt_exceptionalFreePartForModulus_card_of_scaled_bound L E m y hL hSquarefree (T : ℝ) c hc
      htarget
  have hprimeSet :=
    exists_prime_set_of_real_restricted_divisor_lower_bound (exceptionalFreePartForModulus L E m) y
      k x m a T (Nat.ne_of_gt hL'pos) hk c hlower hanalytic
  have havoid : ∀ d, d ∣ exceptionalFreePartForModulus L E m → ∀ e ∈ E, ¬e ∣ d * m := by
    intro d hd e he
    exact exceptionalFreePartForModulus_divisors_avoid L E m hL hSquarefree hE hEm hLm d hd e he
  rcases hprimeSet with ⟨P, hPcard, hPproperties⟩
  refine ⟨P, hPcard, ?_⟩
  intro p hp
  obtain ⟨hpPrime, hpx, hpm, d, hd, hdy, hpeq⟩ := hPproperties p hp
  exact ⟨hpPrime, hpx, hpm, d, hd, hdy, hpeq, havoid d hd⟩

/--
Inputs: a squarefree modulus, finite exceptional set, divisor cutoffs, a
prime-factor cutoff, and a scaled lower bound that includes both finite losses.

Claim: there are more than `T` primes in the target progression represented by
exceptional-free divisors larger than the prime-factor cutoff; each such divisor
avoids the exceptional moduli in the CRT modulus.

Proof: transfer the original divisor-count bound through exceptional-factor
removal and the small-divisor loss, then apply the large-divisor prime-set
construction.

Role: this joins the large-modulus range count to the finite prime-set output
needed by the AGP construction.
-/
theorem exists_prime_set_from_large_exceptionalFreePartForModulus_real_count_lower_bound (L : ℕ)
    (E : Finset ℕ) (y q C k x m a T : ℕ) (hL : L ≠ 0) (hSquarefree : Squarefree L)
    (hE : ∀ e ∈ E, 1 < e) (hEm : ∀ e ∈ E, ¬e ∣ m) (hLm : Nat.Coprime L m)
    (hqL : ∀ r, r ∣ exceptionalFreePartForModulus L E m → Nat.Prime r → r ≤ q) (hC : C ≤ q)
    (hk : 0 < k) (c : ℝ) (hc : 0 ≤ c)
    (htarget : (T + c * (q + 1 : ℝ)) * (2 ^ E.card : ℝ) < c * ((restrictedDivisors L y).card : ℝ))
    (hanalytic :
      c * ((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).card : ℝ) ≤
        ((((largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q).filter
                (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % m = a % m)).card :
            ℕ) :
          ℝ)) :
    ∃ P : Finset ℕ,
      T < P.card ∧
        ∀ p ∈ P,
          Nat.Prime p ∧
            p ≤ x ∧
            p % m = a % m ∧
            C < p ∧
            Nat.Coprime p (exceptionalFreePartForModulus L E m) ∧
            ∃ d,
              d ∣ exceptionalFreePartForModulus L E m ∧
                d ≤ y ∧ q < d ∧ p = d * k + 1 ∧ ∀ e ∈ E, ¬e ∣ d * m := by
  have hlower :=
    exists_lt_largeExceptionalFreePart_card_of_scaled_bound L E m y q hL hSquarefree (T : ℝ) c hc
      htarget
  let Q := selectedExceptionalPrimeFactorsForModulus L E m
  have hQfixed : selectedExceptionalPrimeFactors L Q = Q :=
    selectedExceptionalPrimeFactorsForModulus_fixed L E m hL
  have hL'pos : 0 < exceptionalFreePartForModulus L E m := by
    change 0 < (L.primeFactors \ selectedExceptionalPrimeFactors L Q).prod id
    rw [hQfixed]
    apply Finset.prod_pos
    intro p hp
    exact ((Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1).pos
  have hprimeSet :=
    exists_prime_set_from_large_restricted_divisor_real_lower_bound
      (exceptionalFreePartForModulus L E m) y q C k x m a T (Nat.ne_of_gt hL'pos) hqL hC hk c hlower
      hanalytic
  have havoid : ∀ d, d ∣ exceptionalFreePartForModulus L E m → ∀ e ∈ E, ¬e ∣ d * m := by
    intro d hd e he
    exact exceptionalFreePartForModulus_divisors_avoid L E m hL hSquarefree hE hEm hLm d hd e he
  rcases hprimeSet with ⟨P, hPcard, hPproperties⟩
  refine ⟨P, hPcard, ?_⟩
  intro p hp
  obtain ⟨hpPrime, hpx, hpm, hpC, hpcoprime, d, hd, hdy, hqd, hpeq⟩ := hPproperties p hp
  exact ⟨hpPrime, hpx, hpm, hpC, hpcoprime, d, hd, hdy, hqd, hpeq, havoid d hd⟩

/--
Inputs: a squarefree modulus, the modulus-adjusted exceptional-free part, a
positive progression parameter, and a prime set represented by its large
exceptional-free divisors.

Claim: a real lower bound for the number of supplied primes transfers to the
fixed-parameter good-divisor count required by reliable Proposition 1.5.

Proof: map primes injectively to their divisor labels, then include each such
label among the restricted divisors of the original modulus.

Role: this is the finite endpoint from the AGP prime-set output to the
`hProp15` field of `AGPProgressionCountData`.
-/
theorem reliableProp15_good_divisor_count_of_large_exceptionalFreePart_prime_set (L : ℕ)
    (E : Finset ℕ) (m y q k x T : ℕ) (c₀ : ℝ) (P : Finset ℕ) (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hk : 0 < k)
    (hP :
      ∀ p ∈ P,
        Nat.Prime p ∧
          p ≤ x ∧
          p % 4 = 3 % 4 ∧
          ∃ d,
            d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q ∧ p = d * k + 1)
    (hcount : reliableProp15Coefficient c₀ 4 x * ((restrictedDivisors L y).card : ℝ) ≤ (T : ℝ))
    (hPcard : T < P.card) :
    reliableProp15Coefficient c₀ 4 x * ((restrictedDivisors L y).card : ℝ) ≤
      ((((restrictedDivisors L y).filter
              (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % 4 = 3)).card :
          ℕ) :
        ℝ) := by
  let Q := selectedExceptionalPrimeFactorsForModulus L E m
  have hQfixed : selectedExceptionalPrimeFactors L Q = Q :=
    selectedExceptionalPrimeFactorsForModulus_fixed L E m hL
  have hL'pos : 0 < exceptionalFreePartForModulus L E m := by
    change 0 < (L.primeFactors \ selectedExceptionalPrimeFactors L Q).prod id
    rw [hQfixed]
    apply Finset.prod_pos
    intro p hp
    exact ((Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1).pos
  have hL'dvdL : exceptionalFreePartForModulus L E m ∣ L :=
    (exceptionalFreePartForModulus_properties L E m hL hSquarefree).2.2.1
  have hPfull :
    ∀ p ∈ P,
      Nat.Prime p ∧ p ≤ x ∧ p % 4 = 3 % 4 ∧ ∃ d, d ∈ restrictedDivisors L y ∧ p = d * k + 1 := by
    intro p hp
    obtain ⟨hpPrime, hpx, hpm, d, hd, hpeq⟩ := hP p hp
    have hd' := (mem_largeRestrictedDivisors (Nat.ne_of_gt hL'pos)).mp hd
    have hdFull : d ∈ restrictedDivisors L y :=
      (mem_restrictedDivisors hL).mpr ⟨Nat.dvd_trans hd'.1 hL'dvdL, hd'.2.1⟩
    exact ⟨hpPrime, hpx, hpm, d, hdFull, hpeq⟩
  have hPgood :=
    card_le_good_divisor_count_of_prime_set (restrictedDivisors L y) P k x 4 3 hk hPfull
  have hPcardReal : (T : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast Nat.le_of_lt hPcard
  have hPgoodReal :
    (P.card : ℝ) ≤
      (((restrictedDivisors L y).filter
            (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % 4 = 3)).card :
        ℝ) := by
    exact_mod_cast hPgood
  exact le_trans hcount (le_trans hPcardReal hPgoodReal)

/--
Inputs: the structural fields of AGP progression-count data, a prime set with
more than `T` members represented by large exceptional-free divisors, and a
comparison between `T` and the Proposition 1.5 coefficient count.

Claim: these data form an `AGPProgressionCountData` object.

Proof: transfer the prime-set lower bound to the fixed-parameter good-divisor
count, then fill the remaining fields directly.

Role: this is the finite endpoint from the distribution estimates to the
prime-supply input consumed by the Carmichael construction.
-/
def agpProgressionCountData_of_large_exceptionalFreePart_prime_set (W : Finset ℕ) (C : ℕ) (c₀ : ℝ)
    (x₀ L y q x k T m : ℕ) (E : Finset ℕ) (P : Finset ℕ) (hL : 2 < L) (hSquarefree : Squarefree L)
    (hLargeEnough : x₀ ≤ x) (hProp15Input : ReliableProp15Admissible L 4 y k x)
    (hCq : max C (W.sup id) ≤ q) (hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ q)
    (hlambda : 3 ≤ ArithmeticFunction.carmichael L) (hk : 0 < k) (hcoprime : Nat.Coprime k L)
    (hlower :
      ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log L) + q : ℕ) : ℝ) <
        reliableProp15Coefficient c₀ 4 x * ((restrictedDivisors L y).card : ℝ))
    (hcount : reliableProp15Coefficient c₀ 4 x * ((restrictedDivisors L y).card : ℝ) ≤ (T : ℝ))
    (hP :
      ∀ p ∈ P,
        Nat.Prime p ∧
          p ≤ x ∧
          p % 4 = 3 % 4 ∧
          ∃ d,
            d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q ∧ p = d * k + 1)
    (hPcard : T < P.card) : AGPProgressionCountData W C c₀ x₀ := by
  have hLne : L ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two hL)
  have hProp15 :=
    reliableProp15_good_divisor_count_of_large_exceptionalFreePart_prime_set L E m y q k x T c₀ P
      hLne hSquarefree hk hP hcount hPcard
  exact
    ⟨L, y, q, x, k, hL, hSquarefree, hLargeEnough, hProp15Input, hCq, hfactor, hlambda, hk,
      hcoprime, hlower, hProp15⟩

/--
Inputs: the fifth-power scale, coprime CRT moduli, a theta lower bound for
their combined residue, and a bound showing that the main term still exceeds
the target after subtracting primes with a non-coprime quotient.

Claim: the target lower bound holds for the CRT prime count with the quotient
coprimality condition imposed.

Proof: the theta estimate bounds the full progression count below by its main
term; apply the finite partition lemma to remove the stated bad-prime mass.

Role: this is the per-divisor analytic interface needed by the finite average.
-/
theorem primeCountInProgressionWithCoprimeQuotient_ge_of_theta_lower_and_bad_bound (X d m l L : ℕ)
    (c : ℝ) (hX : 82944 ≤ X) (hdPos : 0 < d) (hd : d ≤ X ^ 2) (hmPos : 0 < m)
    (hdm : Nat.Coprime d m) (hlm : Nat.Coprime l m) (hq : d * m ≤ 4 * d)
    (htheta :
      ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ)) ≤
        thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * m) (progressionCoprimeResidue d m l hdm))
    (hmargin :
      c + (badQuotientPrimeCountInProgression (d * X ^ 3) d m l L hdm : ℝ) ≤
        (((d * X ^ 3 : ℕ) : ℝ) / (4 * (Nat.totient (d * m) : ℝ))) /
          Real.log ((d * X ^ 3 : ℕ) : ℝ)) :
    c ≤ (primeCountInProgressionWithCoprimeQuotient (d * X ^ 3) d m l L : ℝ) := by
  have hmain :=
    primeCountInProgression_ge_main_term_of_theta_lower_agp_fifth_power_scale X d (d * m)
      (progressionCoprimeResidue d m l hdm) hX hdPos hd (Nat.mul_pos hdPos hmPos) hq htheta
  have hraw := le_trans hmargin hmain
  exact
    primeCountInProgressionWithCoprimeQuotient_ge_of_crt_count (d * X ^ 3) d m l L c hdm hlm hraw

/--
Inputs: an AGP scale, a theta lower bound for the CRT progression, and upper
bounds for the progressions corresponding to each prime factor of `L`.

Claim: the count of CRT primes whose quotient is coprime to `L` is at least
`c` whenever the main term minus those prime-factor bounds is at least `c`.

Proof: the finite union bound controls the bad quotient count by the sum of
the prime-factor progression counts, then the preceding theta interface
transfers the remaining lower bound.

Role: this exposes the exact Brun–Titchmarsh input needed by the AGP average.
-/
theorem primeCountInProgressionWithCoprimeQuotient_ge_of_theta_lower_and_bad_factor_counts
    (X d m l L : ℕ) (c : ℝ) (hX : 82944 ≤ X) (hdPos : 0 < d) (hd : d ≤ X ^ 2) (hL : L ≠ 0)
    (hmPos : 0 < m) (hdm : Nat.Coprime d m) (hlm : Nat.Coprime l m) (hq : d * m ≤ 4 * d)
    (htheta :
      ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ)) ≤
        thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * m) (progressionCoprimeResidue d m l hdm))
    (hmargin :
      c + (↑(∑ q ∈ L.primeFactors, primeCountInProgression (d * X ^ 3) (d * q) 1) : ℝ) ≤
        (((d * X ^ 3 : ℕ) : ℝ) / (4 * (Nat.totient (d * m) : ℝ))) /
          Real.log ((d * X ^ 3 : ℕ) : ℝ)) :
    c ≤ (primeCountInProgressionWithCoprimeQuotient (d * X ^ 3) d m l L : ℝ) := by
  have hbad :=
    badQuotientPrimeCountInProgression_le_sum_prime_factor_progressions (d * X ^ 3) d m l L hdPos hL
      hdm hlm
  have hbadReal :
    (badQuotientPrimeCountInProgression (d * X ^ 3) d m l L hdm : ℝ) ≤
      (↑(∑ q ∈ L.primeFactors, primeCountInProgression (d * X ^ 3) (d * q) 1) : ℝ) := by
    exact_mod_cast hbad
  have hmargin' :
    c + (badQuotientPrimeCountInProgression (d * X ^ 3) d m l L hdm : ℝ) ≤
      (((d * X ^ 3 : ℕ) : ℝ) / (4 * (Nat.totient (d * m) : ℝ))) /
        Real.log ((d * X ^ 3 : ℕ) : ℝ) := by
    linarith only [hbadReal, hmargin]
  exact
    primeCountInProgressionWithCoprimeQuotient_ge_of_theta_lower_and_bad_bound X d m l L c hX hdPos
      hd hmPos hdm hlm hq htheta hmargin'

/--
Inputs: a finite divisor set, variable prime bounds, a positive parameter
bound, and per-divisor lower bounds for CRT progression counts after charging
the primes with a quotient not coprime to `L`.

Claim: one positive parameter coprime to `L` yields more than `T` distinct
primes below `xmax` in residue class `l mod m`, each represented by `d*k+1`
for a divisor label in `D`.

Proof: split each CRT count into coprime and discarded quotients, sum the
resulting pointwise lower bounds, and apply the existing finite averaging
theorem.

Role: this is the finite bridge from per-divisor progression estimates to the
prime set required by the AGP construction.
-/
theorem exists_prime_set_from_crt_count_with_bad_quotient_allowance (D : Finset ℕ) (x : ℕ → ℕ)
    (xmax Kmax m l L T : ℕ) (c : ℝ) (hpos : ∀ d ∈ D, 0 < d) (hdm : ∀ d ∈ D, Nat.Coprime d m)
    (hlm : Nat.Coprime l m) (hcut : ∀ d ∈ D, x d ≤ d * Kmax + 1) (hcommon : ∀ d ∈ D, x d ≤ xmax)
    (hlower : ((positiveCoprimeParameters L Kmax).card * T : ℕ) < c * (D.card : ℝ))
    (hraw :
      ∀ d,
        ∀ hdD : d ∈ D,
          c + (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
            (primeCountInProgression (x d) (d * m) (progressionCoprimeResidue d m l (hdm d hdD)) :
              ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L Kmax,
      ∃ P : Finset ℕ,
        T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ xmax ∧ p % m = l % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  have hpoint : ∀ d ∈ D, c ≤ (primeCountInProgressionWithCoprimeQuotient (x d) d m l L : ℝ) := by
    intro d hdD
    exact
      primeCountInProgressionWithCoprimeQuotient_ge_of_crt_count (x d) d m l L c (hdm d hdD) hlm
        (hraw d hdD)
  have hsum := Finset.sum_le_sum hpoint
  have hanalytic :
    c * (D.card : ℝ) ≤
      (↑(∑ d ∈ D, primeCountInProgressionWithCoprimeQuotient (x d) d m l L) : ℝ) := by
    simpa only [Nat.cast_sum, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum
  exact
    exists_prime_set_from_variable_coprime_progression_lower_bound D x xmax Kmax m l L T c hpos hcut
      hcommon hlower hanalytic

/--
Inputs: a finite divisor set, an AGP fifth-power scale, theta lower bounds
for its CRT progressions, and upper bounds for all prime-factor progressions
that can contribute bad quotients.

Claim: one positive parameter coprime to `L` yields more than `T` distinct
primes below `X^5` in residue class `l mod m`, each represented by `d*k+1`
for some `d ∈ D`.

Proof: apply the per-divisor theta and bad-factor estimate, sum the resulting
coprime-quotient counts, and invoke the finite averaging theorem with
`Kmax = X^3`.

Role: this is the direct analytic-to-finite interface for the AGP prime supply.
-/
theorem exists_prime_set_from_theta_lower_and_bad_factor_counts (D : Finset ℕ) (X m l L T : ℕ)
    (c : ℝ) (hX : 82944 ≤ X) (hmPos : 0 < m) (hL : L ≠ 0) (hpos : ∀ d ∈ D, 0 < d)
    (hd : ∀ d ∈ D, d ≤ X ^ 2) (hdm : ∀ d ∈ D, Nat.Coprime d m) (hlm : Nat.Coprime l m)
    (hq : ∀ d ∈ D, d * m ≤ 4 * d)
    (htheta :
      ∀ d,
        ∀ hdD : d ∈ D,
          ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ)) ≤
            thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * m)
              (progressionCoprimeResidue d m l (hdm d hdD)))
    (hmargin :
      ∀ d ∈ D,
        c + (↑(∑ q ∈ L.primeFactors, primeCountInProgression (d * X ^ 3) (d * q) 1) : ℝ) ≤
          (((d * X ^ 3 : ℕ) : ℝ) / (4 * (Nat.totient (d * m) : ℝ))) /
            Real.log ((d * X ^ 3 : ℕ) : ℝ))
    (hlower : ((positiveCoprimeParameters L (X ^ 3)).card * T : ℕ) < c * (D.card : ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L (X ^ 3),
      ∃ P : Finset ℕ,
        T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ X ^ 5 ∧ p % m = l % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  let x := fun d : ℕ => d * X ^ 3
  have hcut : ∀ d ∈ D, x d ≤ d * X ^ 3 + 1 := by
    intro d hdD
    exact Nat.le_add_right (d * X ^ 3) 1
  have hcommon : ∀ d ∈ D, x d ≤ X ^ 5 := by
    intro d hdD
    calc
      x d = d * X ^ 3 := rfl
      _ ≤ X ^ 2 * X ^ 3 := Nat.mul_le_mul_right (X ^ 3) (hd d hdD)
      _ = X ^ 5 := by rw [← Nat.pow_add]
  have hraw :
    ∀ d,
      ∀ hdD : d ∈ D,
        c + (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
          (primeCountInProgression (x d) (d * m) (progressionCoprimeResidue d m l (hdm d hdD)) :
            ℝ) := by
    intro d hdD
    have hmain :=
      primeCountInProgression_ge_main_term_of_theta_lower_agp_fifth_power_scale X d (d * m)
        (progressionCoprimeResidue d m l (hdm d hdD)) hX (hpos d hdD) (hd d hdD)
        (Nat.mul_pos (hpos d hdD) hmPos) (hq d hdD) (htheta d hdD)
    have hbad :=
      badQuotientPrimeCountInProgression_le_sum_prime_factor_progressions (x d) d m l L (hpos d hdD)
        hL (hdm d hdD) hlm
    have hbadReal :
      (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
        (↑(∑ q ∈ L.primeFactors, primeCountInProgression (x d) (d * q) 1) : ℝ) := by
      exact_mod_cast hbad
    have hmargin' :
      c + (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
        (((d * X ^ 3 : ℕ) : ℝ) / (4 * (Nat.totient (d * m) : ℝ))) /
          Real.log ((d * X ^ 3 : ℕ) : ℝ) := by
      linarith only [hbadReal, hmargin d hdD]
    exact le_trans hmargin' hmain
  exact
    exists_prime_set_from_crt_count_with_bad_quotient_allowance D x (X ^ 5) (X ^ 3) m l L T c hpos
      hdm hlm hcut hcommon hlower hraw

/--
The reciprocal-sum condition in reliable Proposition 1.5 is stronger than
the condition in paper95 Theorem 3.1 at `B = 2 / 5`.
-/
theorem reciprocal_sum_threshold_le_paper95_threshold : (1 / 60 : ℝ) ≤ 3 / 160 := by norm_num only

/--
Inputs: a nonnegative main term, a reciprocal-prime-factor sum bound, and
Brun–Titchmarsh-type bounds for each progression modulo `d * q`.

Claim: the total contribution of prime-factor progressions is at most
`mainTerm / 4` when the reciprocal sum is at most `3 / 160`.

Proof: sum the individual bounds and multiply the reciprocal-sum estimate by
`(40 / 3) * mainTerm`.

Role: this records the explicit numerical loss in the bad-quotient removal on
pages 715–716 of paper95 for `B = 2 / 5`.
-/
theorem sum_primeFactor_progression_counts_le_quarter_main_term (y d L : ℕ) (mainTerm : ℝ)
    (hmainTerm : 0 ≤ mainTerm) (hrecip : (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) ≤ 3 / 160)
    (hBT :
      ∀ q ∈ L.primeFactors,
        (primeCountInProgression y (d * q) 1 : ℝ) ≤ (40 / 3) * (q : ℝ)⁻¹ * mainTerm) :
    (∑ q ∈ L.primeFactors, (primeCountInProgression y (d * q) 1 : ℝ)) ≤ (1 / 4) * mainTerm := by
  calc
    _ ≤ ∑ q ∈ L.primeFactors, (40 / 3) * (q : ℝ)⁻¹ * mainTerm := Finset.sum_le_sum hBT
    _ = (40 / 3) * mainTerm * (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) := by
      calc
        _ = ∑ q ∈ L.primeFactors, ((40 / 3) * mainTerm * (q : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = _ := by rw [← Finset.mul_sum]
    _ ≤ (40 / 3) * mainTerm * (3 / 160) :=
      mul_le_mul_of_nonneg_left hrecip (mul_nonneg (by norm_num only) hmainTerm)
    _ = (1 / 4) * mainTerm := by ring

/--
The reciprocal-prime-factor threshold `1 / 60` leaves the exact bad-count
coefficient `2 / 9` under the Brun–Titchmarsh bound with coefficient `40 / 3`.
-/
theorem sum_primeFactor_progression_counts_le_two_ninths_main_term (y d L : ℕ) (mainTerm : ℝ)
    (hmainTerm : 0 ≤ mainTerm) (hrecip : (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) ≤ 1 / 60)
    (hBT :
      ∀ q ∈ L.primeFactors,
        (primeCountInProgression y (d * q) 1 : ℝ) ≤ (40 / 3) * (q : ℝ)⁻¹ * mainTerm) :
    (∑ q ∈ L.primeFactors, (primeCountInProgression y (d * q) 1 : ℝ)) ≤ (2 / 9) * mainTerm := by
  calc
    _ ≤ ∑ q ∈ L.primeFactors, (40 / 3) * (q : ℝ)⁻¹ * mainTerm := Finset.sum_le_sum hBT
    _ = (40 / 3) * mainTerm * (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) := by
      calc
        _ = ∑ q ∈ L.primeFactors, ((40 / 3) * mainTerm * (q : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = _ := by rw [← Finset.mul_sum]
    _ ≤ (40 / 3) * mainTerm * (1 / 60) :=
      mul_le_mul_of_nonneg_left hrecip (mul_nonneg (by norm_num only) hmainTerm)
    _ = (2 / 9) * mainTerm := by ring

/--
Inputs: a CRT progression modulo `d*m`, Brun–Titchmarsh bounds for the
prime-factor progressions, and the main term.

Claim: the sum of bad prime counts is at most `(40 / 3) * mainTerm` times the
sum of reciprocal prime factors of `L`.

Proof: sum the individual Brun–Titchmarsh bounds and regroup the finite sum.

Role: this keeps the exact reciprocal-sum dependence available to later
finite-average theorems.
-/
theorem sum_primeFactor_crt_progression_counts_le_reciprocal_sum_multiple_main_term (y d m l L : ℕ)
    (progressionCoefficient : ℝ) (hdm : Nat.Coprime d m) (hLm : Nat.Coprime L m) (mainTerm : ℝ)
    (hBT :
      ∀ q : { q // q ∈ L.primeFactors },
        (primeCountInProgression y (d * q.val * m)
              (progressionCoprimeResidue (d * q.val) m l
                (Nat.Coprime.mul_left hdm
                  (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :
            ℝ) ≤
          progressionCoefficient * (q.val : ℝ)⁻¹ * mainTerm) :
    (∑ q ∈ L.primeFactors.attach,
        (primeCountInProgression y (d * q.val * m)
            (progressionCoprimeResidue (d * q.val) m l
              (Nat.Coprime.mul_left hdm
                (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :
          ℝ)) ≤
      progressionCoefficient * mainTerm * (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) := by
  calc
    _ ≤ ∑ q ∈ L.primeFactors.attach, progressionCoefficient * (q.val : ℝ)⁻¹ * mainTerm := by
      apply Finset.sum_le_sum
      intro q hq
      exact hBT q
    _ = progressionCoefficient * mainTerm * (∑ q ∈ L.primeFactors.attach, (q.val : ℝ)⁻¹) := by
      calc
        _ = ∑ q ∈ L.primeFactors.attach, (progressionCoefficient * mainTerm * (q.val : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = _ := by rw [← Finset.mul_sum]
    _ = progressionCoefficient * mainTerm * (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) := by
      exact
        congrArg (fun z : ℝ => progressionCoefficient * mainTerm * z)
          (Finset.sum_attach L.primeFactors (fun q => (q : ℝ)⁻¹))

/--
The `1 / 60` reciprocal-sum threshold gives a `2 / 9` bound while preserving
the CRT residue modulo `m` in each prime-factor progression.
-/
theorem sum_primeFactor_crt_progression_counts_le_two_ninths_main_term (y d m l L : ℕ)
    (hdm : Nat.Coprime d m) (hLm : Nat.Coprime L m) (mainTerm : ℝ) (hmainTerm : 0 ≤ mainTerm)
    (hrecip : (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) ≤ 1 / 60)
    (hBT :
      ∀ q : { q // q ∈ L.primeFactors },
        (primeCountInProgression y (d * q.val * m)
              (progressionCoprimeResidue (d * q.val) m l
                (Nat.Coprime.mul_left hdm
                  (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :
            ℝ) ≤
          (40 / 3) * (q.val : ℝ)⁻¹ * mainTerm) :
    (∑ q ∈ L.primeFactors.attach,
        (primeCountInProgression y (d * q.val * m)
            (progressionCoprimeResidue (d * q.val) m l
              (Nat.Coprime.mul_left hdm
                (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :
          ℝ)) ≤
      (2 / 9) * mainTerm := by
  have hsum :=
    sum_primeFactor_crt_progression_counts_le_reciprocal_sum_multiple_main_term y d m l L (40 / 3)
      hdm hLm mainTerm hBT
  calc
    _ ≤ (40 / 3) * mainTerm * (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) := hsum
    _ ≤ (40 / 3) * mainTerm * (1 / 60) :=
      mul_le_mul_of_nonneg_left hrecip (mul_nonneg (by norm_num only) hmainTerm)
    _ = (2 / 9) * mainTerm := by ring

/--
Inputs: a finite divisor set, a common reciprocal-prime-factor bound, a lower
bound of half the main term for each full progression, and Brun–Titchmarsh-type
upper bounds for the prime-factor progressions.

Claim: if each quarter-main-term exceeds the uniform threshold `c`, then one
parameter coprime to `L` gives more than `T` primes in the required residue
class, represented as `d * k + 1` for some `d` in the divisor set.

Proof: the previous numerical estimate leaves at least one quarter of each
main term after removing non-coprime quotients; sum these lower bounds and
apply the finite averaging theorem.

Role: this is the finite counting conclusion of the page-716 argument in
paper95, with its explicit prime-count estimates supplied as hypotheses.
-/
theorem exists_prime_set_from_brun_titchmarsh_progression_bounds (D : Finset ℕ) (x : ℕ → ℕ)
    (xmax Kmax m l L T : ℕ) (c : ℝ) (mainTerm : ℕ → ℝ) (hpos : ∀ d ∈ D, 0 < d)
    (hdm : ∀ d ∈ D, Nat.Coprime d m) (hlm : Nat.Coprime l m) (hcut : ∀ d ∈ D, x d ≤ d * Kmax + 1)
    (hcommon : ∀ d ∈ D, x d ≤ xmax) (hL : L ≠ 0) (hmainTerm : ∀ d ∈ D, 0 ≤ mainTerm d)
    (htarget : ∀ d ∈ D, c ≤ mainTerm d / 4) (hrecip : (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) ≤ 1 / 60)
    (hraw :
      ∀ d,
        ∀ hdD : d ∈ D,
          mainTerm d / 2 ≤
            (primeCountInProgression (x d) (d * m) (progressionCoprimeResidue d m l (hdm d hdD)) :
              ℝ))
    (hBT :
      ∀ d,
        ∀ q ∈ L.primeFactors,
          (primeCountInProgression (x d) (d * q) 1 : ℝ) ≤ (40 / 3) * (q : ℝ)⁻¹ * mainTerm d)
    (hlower : ((positiveCoprimeParameters L Kmax).card * T : ℕ) < c * (D.card : ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L Kmax,
      ∃ P : Finset ℕ,
        T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ xmax ∧ p % m = l % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  have hrawAllowance :
    ∀ d,
      ∀ hdD : d ∈ D,
        c + (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
          (primeCountInProgression (x d) (d * m) (progressionCoprimeResidue d m l (hdm d hdD)) :
            ℝ) := by
    intro d hdD
    have hbad :=
      badQuotientPrimeCountInProgression_le_sum_prime_factor_progressions (x d) d m l L (hpos d hdD)
        hL (hdm d hdD) hlm
    have hbadReal :
      (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
        (∑ q ∈ L.primeFactors, (primeCountInProgression (x d) (d * q) 1 : ℝ)) := by
      exact_mod_cast hbad
    have hrecipBT : (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) ≤ 3 / 160 :=
      le_trans hrecip reciprocal_sum_threshold_le_paper95_threshold
    have hsum :=
      sum_primeFactor_progression_counts_le_quarter_main_term (x d) d L (mainTerm d)
        (hmainTerm d hdD) hrecipBT (hBT d)
    have hmargin :
      c + (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤ mainTerm d / 2 := by
      linarith only [htarget d hdD, le_trans hbadReal hsum, hmainTerm d hdD]
    exact le_trans hmargin (hraw d hdD)
  exact
    exists_prime_set_from_crt_count_with_bad_quotient_allowance D x xmax Kmax m l L T c hpos hdm hlm
      hcut hcommon hlower hrawAllowance

/-
Inputs: a finite divisor set, theta lower bounds in the CRT progressions,
Brun–Titchmarsh upper bounds for prime-factor progressions, and the reciprocal
prime-factor sum bound from reliable Proposition 1.5.

Claim: one parameter coprime to `L` yields more than `T` distinct primes in the
required residue class, represented by `d * k + 1` for some `d ∈ D`.

Proof: the strengthened modulus-square condition leaves all but one millionth
of the main term after the prime-power error. The prime-factor progressions
contribute `(40 / 3)` times the reciprocal-prime sum; the remaining
coefficient is passed to the finite averaging theorem.

Role: this connects the existing theta-to-count estimate and the explicit
Brun–Titchmarsh coefficient to the AGP finite prime-supply interface.
-/
theorem exists_prime_set_from_theta_lower_and_brun_titchmarsh_bounds (D : Finset ℕ) (x : ℕ → ℕ)
    (xmax Kmax m l L T : ℕ) (c : ℝ) (progressionCoefficient reciprocalBound : ℝ)
    (hprogressionCoefficient : 0 ≤ progressionCoefficient) (hxmax : 2 ≤ xmax) (hmPos : 0 < m)
    (hpos : ∀ d ∈ D, 0 < d) (hdm : ∀ d ∈ D, Nat.Coprime d m) (hlm : Nat.Coprime l m)
    (hcut : ∀ d ∈ D, x d ≤ d * Kmax + 1) (hcommon : ∀ d ∈ D, x d ≤ xmax) (hx : ∀ d ∈ D, 2 ≤ x d)
    (hL : L ≠ 0) (hLm : Nat.Coprime L m)
    (hmodulus : ∀ d ∈ D, (18000000 * ((d * m : ℕ) : ℝ)) ^ 2 ≤ (x d : ℝ))
    (htheta :
      ∀ d,
        ∀ hdD : d ∈ D,
          (x d : ℝ) / (2 * (Nat.totient (d * m) : ℝ)) ≤
            thetaInProgressionReal (x d : ℝ) (d * m) (progressionCoprimeResidue d m l (hdm d hdD)))
    (hrecip : (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) ≤ reciprocalBound)
    (hBT :
      ∀ d,
        ∀ hdD : d ∈ D,
          ∀ q : { q // q ∈ L.primeFactors },
            (primeCountInProgression (x d) (d * q.val * m)
                  (progressionCoprimeResidue (d * q.val) m l
                    (Nat.Coprime.mul_left (hdm d hdD)
                      (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :
                ℝ) ≤
              progressionCoefficient * (q.val : ℝ)⁻¹ *
                ((x d : ℝ) / (Nat.totient (d * m) : ℝ) / Real.log (xmax : ℝ)))
    (htarget :
      ∀ d ∈ D,
        c ≤
          agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
            ((x d : ℝ) / (Nat.totient (d * m) : ℝ) / Real.log (xmax : ℝ)))
    (hlower : ((positiveCoprimeParameters L Kmax).card * T : ℕ) < c * (D.card : ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L Kmax,
      ∃ P : Finset ℕ,
        T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ xmax ∧ p % m = l % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  let mainTerm : ℕ → ℝ := fun d => (x d : ℝ) / (Nat.totient (d * m) : ℝ) / Real.log (xmax : ℝ)
  have hxmaxReal : (1 : ℝ) < (xmax : ℝ) := by exact_mod_cast (by omega : 1 < xmax)
  have hlogPos : 0 < Real.log (xmax : ℝ) := Real.log_pos hxmaxReal
  have hmainTerm : ∀ d ∈ D, 0 ≤ mainTerm d := by
    intro d hdD
    dsimp [mainTerm]
    have hphi : 0 < (Nat.totient (d * m) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos (hpos d hdD) hmPos)
    exact
      div_nonneg (div_nonneg (by exact_mod_cast Nat.zero_le (x d)) (le_of_lt hphi))
        (le_of_lt hlogPos)
  have hrawAllowance :
    ∀ d,
      ∀ hdD : d ∈ D,
        c + (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
          (primeCountInProgression (x d) (d * m) (progressionCoprimeResidue d m l (hdm d hdD)) :
            ℝ) := by
    intro d hdD
    have hqPos : 0 < d * m := Nat.mul_pos (hpos d hdD) hmPos
    have herror :=
      progressionTheta_millionth_error_bound_of_modulus_square_bound (x d) (d * m) (hmodulus d hdD)
    have hphi : 0 < (Nat.totient (d * m) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqPos
    have hscaled :
      (18 * Real.sqrt (x d : ℝ)) * (Nat.totient (d * m) : ℝ) ≤ (x d : ℝ) / 1000000 := by
      apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 1000000)).2
      nlinarith only [herror]
    have hrawError :
      18 * Real.sqrt (x d : ℝ) ≤ (1 / 1000000 : ℝ) * ((x d : ℝ) / (Nat.totient (d * m) : ℝ)) := by
      have hdiv :
        18 * Real.sqrt (x d : ℝ) ≤ ((1 / 1000000 : ℝ) * (x d : ℝ)) / (Nat.totient (d * m) : ℝ) := by
        apply (le_div_iff₀ hphi).2
        calc
          (18 * Real.sqrt (x d : ℝ)) * (Nat.totient (d * m) : ℝ) ≤ (x d : ℝ) / 1000000 := hscaled
          _ = (1 / 1000000 : ℝ) * (x d : ℝ) := by ring
      simpa only [mul_div_assoc] using hdiv
    have hrawAtY :=
      primeCountInProgression_ge_half_minus_epsilon_main_term_of_theta_lower (x d) (d * m)
        (progressionCoprimeResidue d m l (hdm d hdD)) (hx d hdD) hqPos (1 / 1000000 : ℝ) hrawError
        (htheta d hdD)
    have hxOne : 1 < x d := lt_of_lt_of_le (by norm_num only) (hx d hdD)
    have hlogY : 0 < Real.log (x d : ℝ) := Real.log_pos (by exact_mod_cast hxOne)
    have hlogCompare : Real.log (x d : ℝ) ≤ Real.log (xmax : ℝ) :=
      Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hxOne))
        (by exact_mod_cast hcommon d hdD)
    have hrawLower :
      (agpFifthPowerRawPrimeCountCoefficient * ((x d : ℝ) / (Nat.totient (d * m) : ℝ))) /
          Real.log (xmax : ℝ) ≤
        (primeCountInProgression (x d) (d * m) (progressionCoprimeResidue d m l (hdm d hdD)) :
          ℝ) := by
      exact
        le_trans
          (div_le_div_of_nonneg_left
            (mul_nonneg (by norm_num only [agpFifthPowerRawPrimeCountCoefficient])
              (div_nonneg (by exact_mod_cast (Nat.zero_le (x d)))
                (by exact_mod_cast Nat.zero_le (Nat.totient (d * m)))))
            hlogY hlogCompare)
          hrawAtY
    have hmainRaw :
      agpFifthPowerRawPrimeCountCoefficient * mainTerm d =
        (agpFifthPowerRawPrimeCountCoefficient * ((x d : ℝ) / (Nat.totient (d * m) : ℝ))) /
          Real.log (xmax : ℝ) := by
      dsimp [mainTerm]
      rw [mul_div_assoc]
    have hraw :
      agpFifthPowerRawPrimeCountCoefficient * mainTerm d ≤
        (primeCountInProgression (x d) (d * m) (progressionCoprimeResidue d m l (hdm d hdD)) :
          ℝ) := by
      exact hmainRaw ▸ hrawLower
    have hbad :=
      badQuotientPrimeCountInProgression_le_sum_prime_factor_crt_progressions (x d) d m l L
        (hpos d hdD) hL (hdm d hdD) hlm hLm
    have hbadReal :
      (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
        (∑ q ∈ L.primeFactors.attach,
          (primeCountInProgression (x d) (d * q.val * m)
              (progressionCoprimeResidue (d * q.val) m l
                (Nat.Coprime.mul_left (hdm d hdD)
                  (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :
            ℝ)) := by
      exact_mod_cast hbad
    have hsum :=
      sum_primeFactor_crt_progression_counts_le_reciprocal_sum_multiple_main_term (x d) d m l L
        progressionCoefficient (hdm d hdD) hLm (mainTerm d) (hBT d hdD)
    have hsumBound :
      (∑ q ∈ L.primeFactors.attach,
          (primeCountInProgression (x d) (d * q.val * m)
              (progressionCoprimeResidue (d * q.val) m l
                (Nat.Coprime.mul_left (hdm d hdD)
                  (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :
            ℝ)) ≤
        progressionCoefficient * mainTerm d * reciprocalBound := by
      calc
        _ ≤ progressionCoefficient * mainTerm d * (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) := hsum
        _ ≤ progressionCoefficient * mainTerm d * reciprocalBound :=
          mul_le_mul_of_nonneg_left hrecip (mul_nonneg hprogressionCoefficient (hmainTerm d hdD))
    have hmargin :
      c + (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
        agpFifthPowerRawPrimeCountCoefficient * mainTerm d := by
      calc
        c + (badQuotientPrimeCountInProgression (x d) d m l L (hdm d hdD) : ℝ) ≤
            agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient
                  reciprocalBound *
                mainTerm d +
              progressionCoefficient * mainTerm d * reciprocalBound :=
          by exact add_le_add (htarget d hdD) (le_trans hbadReal hsumBound)
        _ = agpFifthPowerRawPrimeCountCoefficient * mainTerm d := by
          rw [agpFifthPowerAverageCoefficientOfProgressionBound]
          ring
    exact le_trans hmargin hraw
  exact
    exists_prime_set_from_crt_count_with_bad_quotient_allowance D x xmax Kmax m l L T c hpos hdm hlm
      hcut hcommon hlower hrawAllowance

/--
Inputs: the fifth-power scale `X^5`, divisors `d ≤ X^2`, theta lower bounds
for the progressions modulo `d*m`, Brun–Titchmarsh bounds for the bad
quotients, and the finite-average threshold.

Claim: the estimates produce one `k ≤ X^3`, coprime to `L`, and more than
`T` primes below `X^5` in residue class `l mod m`, each represented by
`d*k+1` for some `d ∈ D`.

Proof: specialize the strengthened theta-to-count estimate and bad-quotient
averaging theorem to `y = d*X^3`; the divisor bound `φ(d*m) ≤ d*m` supplies
its uniform `2/9` coefficient.

Role: this packages the fixed-scale analytic inputs at the finite prime-set
endpoint used by the AGP supply construction.
-/
theorem exists_prime_set_from_agp_fifth_power_theta_and_brun_titchmarsh_bounds (D : Finset ℕ)
    (X m l L T : ℕ) (progressionCoefficient reciprocalBound : ℝ)
    (hprogressionCoefficient : 0 ≤ progressionCoefficient)
    (hcoeff :
      0 < agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound)
    (hX : 82944 ≤ X) (hmPos : 0 < m) (hpos : ∀ d ∈ D, 0 < d) (hd : ∀ d ∈ D, d ≤ X ^ 2)
    (hdm : ∀ d ∈ D, Nat.Coprime d m) (hlm : Nat.Coprime l m) (hL : L ≠ 0) (hLm : Nat.Coprime L m)
    (hmodulus : ∀ d ∈ D, (18000000 * ((d * m : ℕ) : ℝ)) ^ 2 ≤ ((d * X ^ 3 : ℕ) : ℝ))
    (htheta :
      ∀ d,
        ∀ hdD : d ∈ D,
          ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ)) ≤
            thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * m)
              (progressionCoprimeResidue d m l (hdm d hdD)))
    (hrecip : (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) ≤ reciprocalBound)
    (hBT :
      ∀ d,
        ∀ hdD : d ∈ D,
          ∀ q : { q // q ∈ L.primeFactors },
            (primeCountInProgression (d * X ^ 3) (d * q.val * m)
                  (progressionCoprimeResidue (d * q.val) m l
                    (Nat.Coprime.mul_left (hdm d hdD)
                      (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :
                ℝ) ≤
              progressionCoefficient * (q.val : ℝ)⁻¹ *
                (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)))
    (hlower :
      ((positiveCoprimeParameters L (X ^ 3)).card * T : ℕ) <
        (agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
            (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ))) *
          (D.card : ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L (X ^ 3),
      ∃ P : Finset ℕ,
        T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ X ^ 5 ∧ p % m = l % m ∧ ∃ d ∈ D, p = d * k + 1 := by
  let x : ℕ → ℕ := fun d => d * X ^ 3
  let c : ℝ :=
    agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
      (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ))
  have hXtwo : 2 ≤ X := le_trans (by norm_num only : 2 ≤ 82944) hX
  have hXfive : 2 ≤ X ^ 5 := by
    calc
      2 ≤ X := hXtwo
      _ ≤ X ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) X
  have hcut : ∀ d ∈ D, x d ≤ d * X ^ 3 + 1 := by
    intro d hdD
    exact Nat.le_succ (d * X ^ 3)
  have hcommon : ∀ d ∈ D, x d ≤ X ^ 5 := by
    intro d hdD
    dsimp [x]
    calc
      d * X ^ 3 ≤ X ^ 2 * X ^ 3 := Nat.mul_le_mul_right (X ^ 3) (hd d hdD)
      _ = X ^ 5 := by ring
  have hx : ∀ d ∈ D, 2 ≤ x d := by
    intro d hdD
    have hdOne : 1 ≤ d := Nat.succ_le_iff.mpr (hpos d hdD)
    have hXcube : 2 ≤ X ^ 3 := by
      calc
        2 ≤ 2 ^ 3 := by norm_num only
        _ ≤ X ^ 3 := Nat.pow_le_pow_left hXtwo 3
    have hmul : X ^ 3 ≤ d * X ^ 3 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (X ^ 3) hdOne
    exact le_trans hXcube (by simpa only [x] using hmul)
  have htarget :
    ∀ d ∈ D,
      c ≤
        agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
          ((x d : ℝ) / (Nat.totient (d * m) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
    intro d hdD
    simpa only [c, x, Nat.cast_pow] using
      agp_fifth_power_main_term_over_average_lower_of_progression_bound X d m progressionCoefficient
        reciprocalBound hXtwo (hpos d hdD) hmPos hcoeff
  exact
    exists_prime_set_from_theta_lower_and_brun_titchmarsh_bounds D x (X ^ 5) (X ^ 3) m l L T c
      progressionCoefficient reciprocalBound hprogressionCoefficient hXfive hmPos hpos hdm hlm hcut
      hcommon hx hL hLm hmodulus htheta hrecip hBT htarget hlower

/--
Input: positive real parameters `c` and `A`, nonnegative `q`, and separate
bounds for divisor exclusion and the averaged prime threshold.

Claim: these bounds imply the combined exceptional-loss inequality used by the
fixed-scale prime-set construction.

Proof: multiply the divisor bound by `c / 4`, the averaged-threshold bound by
`1 / 4`, add them, and use positivity of `c` and `H`.

Role: isolates the numerical step in deriving `hloss` from seed size estimates;
the seed must still supply both quantitative bounds.
-/
theorem agp_exceptional_loss_budget_of_separate_bounds (c H K T q A : ℝ) (hc : 0 < c) (hA : 0 < A)
    (hq : 0 ≤ q) (hdivisor : 4 * A * (q + 1) < H) (hthreshold : 4 * A * K * T < c * H) :
    (K * T + c * (q + 1)) * A < c * H := by
  have hdivisor' : c * A * (q + 1) < c * H / 4 := by
    have hmul := mul_lt_mul_of_pos_left hdivisor (div_pos hc (by norm_num only : (0 : ℝ) < 4))
    nlinarith only [hmul]
  have hthreshold' : A * K * T < c * H / 4 := by
    have hmul := mul_lt_mul_of_pos_right hthreshold (by norm_num only : (0 : ℝ) < (1 / 4 : ℝ))
    nlinarith only [hmul]
  have hsum := add_lt_add hdivisor' hthreshold'
  have hH : 0 < H := by
    have hqpos : 0 < q + 1 := by linarith only [hq]
    nlinarith only [hdivisor, hA, hqpos]
  nlinarith only [hsum, hc, hH]

/--
Inputs: a source divisor count `B < b * H`, a threshold `T` within one of
`b * H`, an upper bound `K ≤ M` for the averaging set, and coefficient bounds.

Claim: the source count and the coefficient bounds imply the exceptional-loss
budget for the finite average.

Proof: `B ≥ q + 1` gives the divisor-loss bound, while `B ≥ 1` and
`T ≤ b * H + 1` control the averaged threshold. The two resulting bounds feed
`agp_exceptional_loss_budget_of_separate_bounds`.

Role: converts the P2 divisor lower bound into the loss budget once the seed
and finite-average coefficients have been compared.
-/
theorem agp_exceptional_loss_budget_of_source_count (c H K M T q A b B : ℝ) (hA : 0 < A)
    (hM : 0 < M) (hH : 0 < H) (hb : 0 < b) (hq : 0 ≤ q) (hK : K ≤ M) (hT : 0 ≤ T)
    (hTupper : T ≤ b * H + 1) (hBq : q + 1 ≤ B) (hBone : 1 ≤ B) (hsource : B < b * H)
    (hsmall : 4 * A * b ≤ 1) (hmargin : 8 * A * M * b < c) : (K * T + c * (q + 1)) * A < c * H := by
  have hfourA : 0 < 4 * A := mul_pos (by norm_num only : (0 : ℝ) < 4) hA
  have hfourAM : 0 < 4 * A * M := mul_pos hfourA hM
  have hdivisor : 4 * A * (q + 1) < H := by
    calc
      4 * A * (q + 1) ≤ 4 * A * B := mul_le_mul_of_nonneg_left hBq hfourA.le
      _ < 4 * A * (b * H) := mul_lt_mul_of_pos_left hsource hfourA
      _ = (4 * A * b) * H := by ring
      _ ≤ 1 * H := mul_le_mul_of_nonneg_right hsmall hH.le
      _ = H := one_mul H
  have hsourceOne : 1 < b * H := lt_of_le_of_lt hBone hsource
  have hrounded : 4 * A * M * (b * H + 1) < c * H := by
    calc
      4 * A * M * (b * H + 1) = 4 * A * M * b * H + 4 * A * M := by ring
      _ < 4 * A * M * b * H + 4 * A * M * b * H := by
        have hmul := mul_lt_mul_of_pos_left hsourceOne hfourAM
        nlinarith only [hmul]
      _ = 8 * A * M * b * H := by ring
      _ < c * H := by simpa only [mul_assoc] using mul_lt_mul_of_pos_right hmargin hH
  have hKT : K * T ≤ M * (b * H + 1) := by
    calc
      K * T ≤ M * T := mul_le_mul_of_nonneg_right hK hT
      _ ≤ M * (b * H + 1) := mul_le_mul_of_nonneg_left hTupper hM.le
  have hscaled := mul_le_mul_of_nonneg_left hKT hfourA.le
  have hthreshold : 4 * A * K * T < c * H := by
    calc
      4 * A * K * T ≤ 4 * A * M * (b * H + 1) := by nlinarith only [hscaled]
      _ < c * H := hrounded
  have hA8 : 0 < 8 * A := mul_pos (by norm_num only : (0 : ℝ) < 8) hA
  have hA8M : 0 < 8 * A * M := mul_pos hA8 hM
  have hA8Mb : 0 < 8 * A * M * b := mul_pos hA8M hb
  exact
    agp_exceptional_loss_budget_of_separate_bounds c H K T q A (lt_trans hA8Mb hmargin) hA hq
      hdivisor hthreshold

/--
Inputs: a uniform bound `Dexc` on the number of exceptional moduli, a finite
exceptional set `E` with `E.card ≤ Dexc` whose elements exceed `1` and do not
divide `m`, the loss bound for the original restricted divisors, and theta and
Brun–Titchmarsh estimates on the large exceptional-free divisors.

Claim: the finite average yields more than `T` primes below `X^5` in residue
class `l mod m`, represented by the large exceptional-free divisors; every
representing divisor avoids every exceptional modulus in the CRT modulus.

Proof: convert the loss-inclusive divisor bound using the uniform count `Dexc`
and `exists_lt_largeExceptionalFreePart_card_of_exceptional_count_bound`, apply
the fixed-scale prime-set theorem, and use modulus-aware factor removal to
prove exceptional-modulus avoidance.

Role: this combines the finite exceptional-divisor loss with the analytic
progression-count endpoint.
-/
theorem exists_prime_set_from_agp_fifth_power_exceptional_loss_theta_and_brun_titchmarsh_bounds
    (E : Finset ℕ) (X m l L y q Dexc T : ℕ) (progressionCoefficient reciprocalBound : ℝ)
    (hprogressionCoefficient : 0 ≤ progressionCoefficient)
    (hcoeff :
      0 < agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound)
    (hX : 82944 ≤ X) (hmPos : 0 < m) (hL : L ≠ 0) (hSquarefree : Squarefree L)
    (hLm : Nat.Coprime L m) (hE : ∀ e ∈ E, 1 < e) (hEm : ∀ e ∈ E, ¬e ∣ m) (hEcard : E.card ≤ Dexc)
    (hpos : ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q, 0 < d)
    (hd : ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q, d ≤ X ^ 2)
    (hdm : ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q, Nat.Coprime d m)
    (hlm : Nat.Coprime l m)
    (hmodulus :
      ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q,
        (18000000 * ((d * m : ℕ) : ℝ)) ^ 2 ≤ ((d * X ^ 3 : ℕ) : ℝ))
    (htheta :
      ∀ d,
        ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q,
          ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ)) ≤
            thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * m)
              (progressionCoprimeResidue d m l (hdm d hdD)))
    (hrecip : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ reciprocalBound)
    (hBT :
      ∀ d,
        ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q,
          ∀ r : { r // r ∈ L.primeFactors },
            (primeCountInProgression (d * X ^ 3) (d * r.val * m)
                  (progressionCoprimeResidue (d * r.val) m l
                    (Nat.Coprime.mul_left (hdm d hdD)
                      (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp r.property).2.1 hLm))) :
                ℝ) ≤
              progressionCoefficient * (r.val : ℝ)⁻¹ *
                (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * m) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)))
    (hloss :
      ((((positiveCoprimeParameters L (X ^ 3)).card * T : ℕ) : ℝ) +
            (agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient
                  reciprocalBound *
                (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ))) *
              (q + 1 : ℝ)) *
          (2 ^ Dexc : ℝ) <
        (agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
            (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ))) *
          ((restrictedDivisors L y).card : ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L (X ^ 3),
      ∃ P : Finset ℕ,
        T < P.card ∧
          ∀ p ∈ P,
            Nat.Prime p ∧
              p ≤ X ^ 5 ∧
              p % m = l % m ∧
              ∃ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q,
                p = d * k + 1 ∧ ∀ e ∈ E, ¬e ∣ d * m := by
  let D := largeRestrictedDivisors (exceptionalFreePartForModulus L E m) y q
  let c : ℝ :=
    agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
      (((X : ℝ) ^ 3 / (m : ℝ)) / Real.log ((X ^ 5 : ℕ) : ℝ))
  have hXtwo : 2 ≤ X := le_trans (by norm_num only : 2 ≤ 82944) hX
  have hXfive : 1 < X ^ 5 := by
    calc
      1 < 2 := by norm_num only
      _ ≤ X ^ 5 := le_trans hXtwo (Nat.le_self_pow (by norm_num only : 5 ≠ 0) X)
  have hlogPos : 0 < Real.log ((X ^ 5 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hXfive)
  have hXposReal : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_two hXtwo)
  have hcPos : 0 < c := by
    dsimp [c]
    exact mul_pos hcoeff (div_pos (div_pos (pow_pos hXposReal 3) (by exact_mod_cast hmPos)) hlogPos)
  have hTnonneg : 0 ≤ (((positiveCoprimeParameters L (X ^ 3)).card * T : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hlower' :=
    exists_lt_largeExceptionalFreePart_card_of_exceptional_count_bound L E m y q Dexc hL hSquarefree
      hEcard (((positiveCoprimeParameters L (X ^ 3)).card * T : ℕ) : ℝ) c (le_of_lt hcPos) hTnonneg
      (by simpa only [c] using hloss)
  have hlower : ((positiveCoprimeParameters L (X ^ 3)).card * T : ℕ) < c * (D.card : ℝ) := by
    simpa only [D, c] using hlower'
  obtain ⟨k, hk, P, hPcard, hP⟩ :=
    exists_prime_set_from_agp_fifth_power_theta_and_brun_titchmarsh_bounds D X m l L T
      progressionCoefficient reciprocalBound hprogressionCoefficient hcoeff hX hmPos hpos hd hdm hlm
      hL hLm hmodulus htheta hrecip hBT hlower
  let Q := selectedExceptionalPrimeFactorsForModulus L E m
  have hQfixed : selectedExceptionalPrimeFactors L Q = Q :=
    selectedExceptionalPrimeFactorsForModulus_fixed L E m hL
  have hL'pos : 0 < exceptionalFreePartForModulus L E m := by
    change 0 < (L.primeFactors \ selectedExceptionalPrimeFactors L Q).prod id
    rw [hQfixed]
    apply Finset.prod_pos
    intro p hp
    exact ((Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1).pos
  have havoid : ∀ d ∈ D, ∀ e ∈ E, ¬e ∣ d * m := by
    intro d hdD e he
    have hddiv := (mem_largeRestrictedDivisors (Nat.ne_of_gt hL'pos)).mp hdD
    exact
      exceptionalFreePartForModulus_divisors_avoid L E m hL hSquarefree hE hEm hLm d hddiv.1 e he
  refine ⟨k, hk, P, hPcard, ?_⟩
  intro p hp
  obtain ⟨hpPrime, hpx, hpm, d, hdD, hpeq⟩ := hP p hp
  exact ⟨hpPrime, hpx, hpm, d, hdD, hpeq, havoid d hdD⟩

/--
Inputs: a finite divisor set with the AGP cutoff and scale conditions, a
uniform relative-error estimate for the progression theta sums, Brun–Titchmarsh
upper bounds for the prime-factor progressions, and an exceptional-modulus
avoidance condition for every selected divisor.

Claim: one parameter coprime to `L` yields more than `T` distinct primes in
the target residue class, with each representing divisor avoiding every
exceptional modulus in the actual CRT modulus.

Proof: turn each relative-error estimate with tolerance at most one half into
the theta lower bound, then apply the existing finite AGP averaging theorem.

Role: this is the finite endpoint for the distribution estimate in paper95
Theorem 2.1 once its range and exceptional-set hypotheses have been verified.
-/
theorem exists_prime_set_from_relative_error_and_brun_titchmarsh_bounds (D E : Finset ℕ) (x : ℕ → ℕ)
    (xmax Kmax m l L T qcut C : ℕ) (c epsilon reciprocalBound : ℝ) (hxmax : 2 ≤ xmax)
    (hmPos : 0 < m) (hepsilonHalf : epsilon ≤ 1 / 2) (hpos : ∀ d ∈ D, 0 < d)
    (hdm : ∀ d ∈ D, Nat.Coprime d m) (hlm : Nat.Coprime l m) (hcut : ∀ d ∈ D, x d ≤ d * Kmax + 1)
    (hcommon : ∀ d ∈ D, x d ≤ xmax) (hx : ∀ d ∈ D, 2 ≤ x d) (hL : L ≠ 0) (hLm : Nat.Coprime L m)
    (hDlarge : ∀ d ∈ D, qcut < d) (hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ qcut) (hC : C ≤ qcut)
    (hmodulus : ∀ d ∈ D, (18000000 * ((d * m : ℕ) : ℝ)) ^ 2 ≤ (x d : ℝ))
    (hrelative :
      ∀ d,
        ∀ hdD : d ∈ D,
          |thetaInProgressionReal (x d : ℝ) (d * m) (progressionCoprimeResidue d m l (hdm d hdD)) -
                (x d : ℝ) / (Nat.totient (d * m) : ℝ)| ≤
            epsilon * ((x d : ℝ) / (Nat.totient (d * m) : ℝ)))
    (hrecip : (∑ q ∈ L.primeFactors, (q : ℝ)⁻¹) ≤ reciprocalBound)
    (hBT :
      ∀ d,
        ∀ hdD : d ∈ D,
          ∀ q : { q // q ∈ L.primeFactors },
            (primeCountInProgression (x d) (d * q.val * m)
                  (progressionCoprimeResidue (d * q.val) m l
                    (Nat.Coprime.mul_left (hdm d hdD)
                      (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp q.property).2.1 hLm))) :
                ℝ) ≤
              (40 / 3) * (q.val : ℝ)⁻¹ *
                ((x d : ℝ) / (Nat.totient (d * m) : ℝ) / Real.log (xmax : ℝ)))
    (htarget :
      ∀ d ∈ D,
        c ≤
          agpFifthPowerAverageCoefficientOfReciprocalBound reciprocalBound *
            ((x d : ℝ) / (Nat.totient (d * m) : ℝ) / Real.log (xmax : ℝ)))
    (hlower : ((positiveCoprimeParameters L Kmax).card * T : ℕ) < c * (D.card : ℝ))
    (havoid : ∀ d ∈ D, ∀ e ∈ E, ¬e ∣ d * m) :
    ∃ k ∈ positiveCoprimeParameters L Kmax,
      ∃ P : Finset ℕ,
        T < P.card ∧
          ∀ p ∈ P,
            Nat.Prime p ∧
              p ≤ xmax ∧
              p % m = l % m ∧
              C < p ∧ Nat.Coprime p L ∧ ∃ d ∈ D, p = d * k + 1 ∧ ∀ e ∈ E, ¬e ∣ d * m := by
  have htheta :
    ∀ d,
      ∀ hdD : d ∈ D,
        (x d : ℝ) / (2 * (Nat.totient (d * m) : ℝ)) ≤
          thetaInProgressionReal (x d : ℝ) (d * m)
            (progressionCoprimeResidue d m l (hdm d hdD)) := by
    intro d hdD
    exact
      thetaInProgressionReal_ge_half_main_term_of_relative_error (x d : ℝ) (d * m)
        (progressionCoprimeResidue d m l (hdm d hdD)) epsilon
        (div_nonneg (by exact_mod_cast (Nat.zero_le (x d)))
          (by exact_mod_cast (Nat.zero_le (Nat.totient (d * m)))))
        hepsilonHalf (hrelative d hdD)
  obtain ⟨k, hk, P, hPcard, hPproperties⟩ :=
    exists_prime_set_from_theta_lower_and_brun_titchmarsh_bounds D x xmax Kmax m l L T c (40 / 3)
      reciprocalBound (by norm_num only) hxmax hmPos hpos hdm hlm hcut hcommon hx hL hLm hmodulus
      htheta hrecip hBT htarget hlower
  refine ⟨k, hk, P, hPcard, ?_⟩
  intro p hp
  obtain ⟨hpPrime, hpx, hpm, d, hdD, hpeq⟩ := hPproperties p hp
  have hkOne : 1 ≤ k := (mem_positiveCoprimeParameters.mp hk).1
  have hdp : qcut < p := by
    rw [hpeq]
    calc
      qcut < d := hDlarge d hdD
      _ = d * 1 := by simp only [Nat.mul_one]
      _ ≤ d * k := Nat.mul_le_mul_left d hkOne
      _ < d * k + 1 := Nat.lt_succ_self _
  have hpC : C < p := lt_of_le_of_lt hC hdp
  have hpNot : ¬p ∣ L := by
    intro hpL
    exact Nat.not_le_of_gt hdp (hfactor p hpL hpPrime)
  have hpCoprime : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hpPrime).2 hpNot
  exact ⟨hpPrime, hpx, hpm, hpC, hpCoprime, d, hdD, hpeq, havoid d hdD⟩

/-
Inputs: the fifth-power scale, an exceptional set satisfying the logarithmic
lower bound in paper95 Theorem 2.1, its common cutoff threshold and relative
theta estimate on the permitted modulus range, plus the Brun–Titchmarsh and
divisor-loss bounds.

Claim: these inputs give more than `T` primes below `X^5` that are `3 mod 4`
and whose representing divisors avoid every exceptional modulus after
combination with the CRT modulus `4`.

Proof: derive paper95's two modulus-range inequalities and the modulus-square
bound from the fixed scale, convert relative error at most one half to a
theta lower bound, and apply the exceptional-loss prime-set theorem.

Role: this is the finite endpoint for estimates in the form of paper95
Theorem 2.1.
-/
theorem
  exists_prime_set_from_agp_fifth_power_exceptional_loss_relative_error_and_brun_titchmarsh_bounds
    (E : Finset ℕ) (X x₀ L y q Dexc T : ℕ) (epsilon progressionCoefficient reciprocalBound : ℝ)
    (hprogressionCoefficient : 0 ≤ progressionCoefficient) (hX : 2 ^ 56 ≤ X)
    (hthreshold : x₀ ≤ X ^ 5)
    (hcoeff :
      0 < agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound)
    (hL : L ≠ 0) (hSquarefree : Squarefree L) (hLm : Nat.Coprime L 4)
    (hElog : ∀ e ∈ E, Real.log ((X ^ 5 : ℕ) : ℝ) < (e : ℝ)) (hEcard : E.card ≤ Dexc)
    (hpos : ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q, 0 < d)
    (hd : ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q, d ≤ X ^ 2)
    (hdm : ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q, Nat.Coprime d 4)
    (hpaper :
      ∀ d,
        ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q,
          x₀ ≤ X ^ 5 →
            (4 : ℝ) * (d : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) ^ ((20 : ℝ) / 49 - 1 / 1000) ∧
              (4 : ℝ) * (d : ℝ) ≤
                ((d * X ^ 3 : ℕ) : ℝ) / ((X ^ 5 : ℕ) : ℝ) ^ (1 - (20 : ℝ) / 49 + 1 / 1000) →
            |thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * 4)
                    (progressionCoprimeResidue d 4 3 (hdm d hdD)) -
                  ((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ)| ≤
              epsilon * (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ)))
    (hepsilon : epsilon ≤ 1 / 2) (hrecip : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ reciprocalBound)
    (hBT :
      ∀ d,
        ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q,
          ∀ r : { r // r ∈ L.primeFactors },
            (primeCountInProgression (d * X ^ 3) (d * r.val * 4)
                  (progressionCoprimeResidue (d * r.val) 4 3
                    (Nat.Coprime.mul_left (hdm d hdD)
                      (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp r.property).2.1 hLm))) :
                ℝ) ≤
              progressionCoefficient * (r.val : ℝ)⁻¹ *
                (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)))
    (hloss :
      ((((positiveCoprimeParameters L (X ^ 3)).card * T : ℕ) : ℝ) +
            (agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient
                  reciprocalBound *
                (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ))) *
              (q + 1 : ℝ)) *
          (2 ^ Dexc : ℝ) <
        (agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
            (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ))) *
          ((restrictedDivisors L y).card : ℝ)) :
    ∃ k ∈ positiveCoprimeParameters L (X ^ 3),
      ∃ P : Finset ℕ,
        T < P.card ∧
          ∀ p ∈ P,
            Nat.Prime p ∧
              p ≤ X ^ 5 ∧
              p % 4 = 3 ∧
              ∃ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q,
                p = d * k + 1 ∧ ∀ e ∈ E, ¬e ∣ d * 4 := by
  have hXweak : 82944 ≤ X := by
    have hnum : 82944 ≤ 2 ^ 56 := by norm_num only
    exact le_trans hnum hX
  have hEconditions :=
    paper95_exceptional_moduli_conditions_for_four_of_nat_fifth_power_scale E X hX hElog
  have hXstrong : 5184000000000000 ≤ X := by
    have hnum : 5184000000000000 ≤ 2 ^ 56 := by norm_num only
    exact le_trans hnum hX
  have hmodulus :
    ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q,
      (18000000 * ((d * 4 : ℕ) : ℝ)) ^ 2 ≤ ((d * X ^ 3 : ℕ) : ℝ) := by
    intro d hdD
    have hmodNat :=
      progressionTheta_millionth_modulus_square_bound_of_agp_fifth_power_scale X d (4 * d) hXstrong
        (hd d hdD) (by exact le_rfl)
    have hmod : (18000000 * ((4 * d : ℕ) : ℝ)) ^ 2 ≤ ((d * X ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast hmodNat
    simpa only [Nat.mul_comm d 4] using hmod
  have htheta :
    ∀ d,
      ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q,
        ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * 4) : ℝ)) ≤
          thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * 4)
            (progressionCoprimeResidue d 4 3 (hdm d hdD)) := by
    intro d hdD
    have hrange := paper95_modulus_range_of_nat_fifth_power_scale X d hX (hd d hdD)
    exact
      thetaInProgressionReal_ge_half_main_term_of_relative_error ((d * X ^ 3 : ℕ) : ℝ) (d * 4)
        (progressionCoprimeResidue d 4 3 (hdm d hdD)) epsilon
        (div_nonneg (by exact_mod_cast (Nat.zero_le (d * X ^ 3)))
          (by exact_mod_cast (Nat.zero_le (Nat.totient (d * 4)))))
        hepsilon (hpaper d hdD hthreshold hrange)
  exact
    exists_prime_set_from_agp_fifth_power_exceptional_loss_theta_and_brun_titchmarsh_bounds E X 4 3
      L y q Dexc T progressionCoefficient reciprocalBound hprogressionCoefficient hcoeff hXweak
      (by norm_num only) hL hSquarefree hLm hEconditions.1 hEconditions.2 hEcard hpos hd hdm
      (by norm_num only) hmodulus htheta hrecip hBT hloss

/-
Inputs: the AGP modulus and Proposition 1.5 count fields, fixed-scale theta
lower bounds, Brun–Titchmarsh bounds, and the coefficient margin for the
exceptional-loss inequality.

Claim: these inputs construct `AGPProgressionCountData` for every supplied
finite positive base set and lower bound. The auxiliary cutoff equals the
fifth power of the selected scale.

Proof: derive the P2 threshold and exceptional-loss budget, use the theta and
Brun–Titchmarsh estimates to obtain a prime set, then transfer it through the
existing Proposition 1.5 count-data constructor.

Role: this closes the fixed-scale theta interface to progression-count data.
-/
noncomputable def agpProgressionCountData_of_fifth_power_theta_and_brun_titchmarsh (W : Finset ℕ)
    (C : ℕ) (c₀ : ℝ) (x₀ X x₂₁ y Dexc T : ℕ) (E : Finset ℕ)
    (progressionCoefficient reciprocalBound : ℝ)
    (hprogressionCoefficient : 0 ≤ progressionCoefficient)
    (aux : AGPProgressionAuxiliaryData W C c₀ x₀) (hX : 2 ^ 56 ≤ X) (hthresholdSeed : x₂₁ ≤ x₀)
    (hcoeff :
      0 < agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound)
    (hEconditions : (∀ e ∈ E, 1 < e) ∧ ∀ e ∈ E, ¬e ∣ 4) (hEcard : E.card ≤ Dexc)
    (hSeedScale : aux.x = X ^ 5) (hcut : y = reliableProp15DivisorCutoff (X ^ 5))
    (hT :
      T =
        Nat.floor
            (reliableProp15Coefficient c₀ 4 (X ^ 5) * ((restrictedDivisors aux.L y).card : ℝ)) +
          1)
    (hpos : ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q, 0 < d)
    (hd :
      ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q, d ≤ X ^ 2)
    (hdm :
      ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q,
        Nat.Coprime d 4)
    (htheta :
      ∀ d,
        ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q,
          ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * 4) : ℝ)) ≤
            thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * 4)
              (progressionCoprimeResidue d 4 3 (hdm d hdD)))
    (hrecip : (∑ r ∈ aux.L.primeFactors, (r : ℝ)⁻¹) ≤ reciprocalBound)
    (hBT :
      ∀ d,
        ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q,
          ∀ r : { r // r ∈ aux.L.primeFactors },
            (primeCountInProgression (d * X ^ 3) (d * r.val * 4)
                  (progressionCoprimeResidue (d * r.val) 4 3
                    (Nat.Coprime.mul_left (hdm d hdD)
                      (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp r.property).2.1
                        aux.hProp15Input.2.1))) :
                ℝ) ≤
              progressionCoefficient * (r.val : ℝ)⁻¹ *
                (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)))
    (hcoeffmargin :
      16 * (2 ^ Dexc : ℝ) * c₀ <
        agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound) :
    AGPProgressionCountData W C c₀ x₀ := by
  let L := aux.L
  let q := aux.q
  let hL := aux.hL
  let hSquarefree := aux.hProp15Input.1
  let hLm := aux.hProp15Input.2.1
  let hSeedBound : aux.x ≤ X ^ 5 := le_of_eq hSeedScale
  let hLargeEnough := le_trans aux.hLargeEnough hSeedBound
  have hlower :
    ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael aux.L : ℝ) * Real.log aux.L) + aux.q :
          ℕ) :
        ℝ) <
      reliableProp15Coefficient c₀ 4 (X ^ 5) * ((restrictedDivisors aux.L y).card : ℝ) := by
    simpa only [hSeedScale, hcut] using aux.hlower
  have hcount :
    reliableProp15Coefficient c₀ 4 (X ^ 5) * ((restrictedDivisors aux.L y).card : ℝ) ≤ (T : ℝ) := by
    apply le_of_lt
    rw [hT]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one
        (reliableProp15Coefficient c₀ 4 (X ^ 5) * ((restrictedDivisors aux.L y).card : ℝ))
  let Bnat :=
    2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael aux.L : ℝ) * Real.log aux.L) + aux.q
  let B : ℝ := (Bnat : ℝ)
  let b : ℝ := reliableProp15Coefficient c₀ 4 (X ^ 5)
  let H : ℝ := ((restrictedDivisors aux.L y).card : ℝ)
  have hBqNat : aux.q + 1 ≤ Bnat := by
    have hLthree : 3 ≤ aux.L := Nat.succ_le_iff.mpr aux.hL
    have hLreal : (3 : ℝ) ≤ (aux.L : ℝ) := by exact_mod_cast hLthree
    have hlogthree : 1 < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num only : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
    have hlogL : 1 < Real.log (aux.L : ℝ) :=
      lt_of_lt_of_le hlogthree (Real.log_le_log (by norm_num only) hLreal)
    have hlambdaReal : (3 : ℝ) ≤ (ArithmeticFunction.carmichael aux.L : ℝ) := by
      exact_mod_cast aux.hlambda
    have hthreeLog : 3 ≤ 3 * Real.log (aux.L : ℝ) := by
      have h := mul_le_mul_of_nonneg_left (le_of_lt hlogL) (by norm_num only : (0 : ℝ) ≤ 3)
      simpa only [mul_one] using h
    have hlambdaLog :
      (1 : ℝ) ≤ (ArithmeticFunction.carmichael aux.L : ℝ) * Real.log (aux.L : ℝ) := by
      calc
        1 ≤ 3 := by norm_num only
        _ ≤ 3 * Real.log (aux.L : ℝ) := hthreeLog
        _ ≤ (ArithmeticFunction.carmichael aux.L : ℝ) * Real.log (aux.L : ℝ) :=
          mul_le_mul_of_nonneg_right hlambdaReal (by linarith only [hlogL])
    have hfloor :
      1 ≤ Nat.floor ((ArithmeticFunction.carmichael aux.L : ℝ) * Real.log (aux.L : ℝ)) := by
      apply Nat.le_floor
      exact_mod_cast hlambdaLog
    have hpow : 1 ≤ 2 ^ W.card := Nat.succ_le_of_lt (Nat.pow_pos (by norm_num only : 0 < 2))
    have hproduct :
      1 ≤
        2 ^ W.card *
          Nat.floor ((ArithmeticFunction.carmichael aux.L : ℝ) * Real.log (aux.L : ℝ)) := by
      calc
        1 = 1 * 1 := by norm_num only
        _ ≤
            2 ^ W.card *
              Nat.floor ((ArithmeticFunction.carmichael aux.L : ℝ) * Real.log (aux.L : ℝ)) :=
          Nat.mul_le_mul hpow hfloor
    calc
      aux.q + 1 = 1 + aux.q := Nat.add_comm _ _
      _ ≤
          2 ^ W.card *
              Nat.floor ((ArithmeticFunction.carmichael aux.L : ℝ) * Real.log (aux.L : ℝ)) +
            aux.q :=
        Nat.add_le_add_right hproduct aux.q
  have hOneLeQ : 1 ≤ aux.q + 1 := by simpa only [Nat.add_comm] using Nat.le_add_right 1 aux.q
  have hBOneNat : 1 ≤ Bnat := le_trans hOneLeQ hBqNat
  have hqnonneg : 0 ≤ (aux.q : ℝ) := by exact_mod_cast Nat.zero_le aux.q
  have hBqReal : (aux.q : ℝ) + 1 ≤ B := by
    change (aux.q : ℝ) + 1 ≤ (Bnat : ℝ)
    exact_mod_cast hBqNat
  have hBOneReal : 1 ≤ B := by
    change (1 : ℝ) ≤ (Bnat : ℝ)
    exact_mod_cast hBOneNat
  have hsource : B < b * H := by simpa only [B, Bnat, b, H] using hlower
  have hsourceOne : 1 < b * H := lt_of_le_of_lt hBOneReal hsource
  have hHnonneg : 0 ≤ H := by
    change 0 ≤ ((restrictedDivisors aux.L y).card : ℝ)
    exact_mod_cast Nat.zero_le ((restrictedDivisors aux.L y).card)
  have hHpos : 0 < H := by
    by_contra hNot
    have hZero : H = 0 := le_antisymm (le_of_not_gt hNot) hHnonneg
    rw [hZero, mul_zero] at hsourceOne
    exact (not_lt_of_ge (by norm_num only : (0 : ℝ) ≤ 1)) hsourceOne
  have hbpos : 0 < b := by
    by_contra hNot
    have hbnonpos : b ≤ 0 := le_of_not_gt hNot
    have hprod : b * H ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hbnonpos hHpos.le
    linarith only [hsourceOne, hprod]
  have hTupper : (T : ℝ) ≤ b * H + 1 := by
    rw [hT]
    have hfloor := Nat.floor_le (le_of_lt (mul_pos hbpos hHpos))
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith only [hfloor]
  have hKnat : (positiveCoprimeParameters aux.L (X ^ 3)).card ≤ X ^ 3 := by
    unfold positiveCoprimeParameters
    calc
      ((Finset.Icc 1 (X ^ 3)).filter (fun k => Nat.Coprime k aux.L)).card ≤
          (Finset.Icc 1 (X ^ 3)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = X ^ 3 := by
        rw [Nat.card_Icc]; omega
  have hK : ((positiveCoprimeParameters aux.L (X ^ 3)).card : ℝ) ≤ ((X ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hKnat
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num only : 0 < 2 ^ 56) hX
  have hMpos : 0 < ((X ^ 3 : ℕ) : ℝ) := by exact_mod_cast Nat.pow_pos hXpos
  have hApos : 0 < (2 ^ Dexc : ℝ) := by exact_mod_cast Nat.pow_pos (by norm_num only : 0 < 2)
  have hXcubeCast : ((X ^ 3 : ℕ) : ℝ) = (X : ℝ) ^ 3 := by norm_cast
  have hrecipNonneg : 0 ≤ reciprocalBound := by
    have hsum : 0 ≤ ∑ r ∈ aux.L.primeFactors, (r : ℝ)⁻¹ := by
      apply Finset.sum_nonneg
      intro r hr
      exact inv_nonneg.mpr (Nat.cast_nonneg r)
    exact le_trans hsum hrecip
  have hbetaOne :
    agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound ≤
      1 := by
    unfold agpFifthPowerAverageCoefficientOfProgressionBound agpFifthPowerRawPrimeCountCoefficient
    nlinarith only [hrecipNonneg, hprogressionCoefficient]
  have hXtwo : 2 ≤ X := le_trans (by norm_num only : 2 ≤ 2 ^ 56) hX
  have hXfiveLower : 3 ≤ X ^ 5 := by
    calc
      3 ≤ 2 ^ 5 := by norm_num only
      _ ≤ X ^ 5 := Nat.pow_le_pow_left hXtwo 5
  have hXfiveReal : (3 : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) := by exact_mod_cast hXfiveLower
  have hlogThree : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num only : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
  have hlogXfive : 1 < Real.log ((X ^ 5 : ℕ) : ℝ) :=
    lt_of_lt_of_le hlogThree (Real.log_le_log (by norm_num only) hXfiveReal)
  have hlogXfiveNonneg : 0 ≤ Real.log ((X ^ 5 : ℕ) : ℝ) :=
    le_trans (by norm_num only : (0 : ℝ) ≤ 1) hlogXfive.le
  have hmargin :
    8 * (2 ^ Dexc : ℝ) * (X : ℝ) ^ 3 * reliableProp15Coefficient c₀ 4 (X ^ 5) <
      agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
        (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
    have hphi : Nat.totient 4 = 2 := by decide
    have hlogPos : 0 < Real.log ((X ^ 5 : ℕ) : ℝ) :=
      lt_trans (by norm_num only : (0 : ℝ) < 1) hlogXfive
    have hMposReal : 0 < (X : ℝ) ^ 3 := by
      rw [← hXcubeCast]
      exact hMpos
    have hfactor : 0 < (X : ℝ) ^ 3 / (4 * Real.log ((X ^ 5 : ℕ) : ℝ)) :=
      div_pos hMposReal (mul_pos (by norm_num only : (0 : ℝ) < 4) hlogPos)
    have hmul := mul_lt_mul_of_pos_right hcoeffmargin hfactor
    change
      8 * (2 ^ Dexc : ℝ) * (X : ℝ) ^ 3 * (c₀ / ((Nat.totient 4 : ℝ) * Real.log ((X ^ 5 : ℕ) : ℝ))) <
        _
    rw [hphi]
    calc
      _ = (16 * (2 ^ Dexc : ℝ) * c₀) * ((X : ℝ) ^ 3 / (4 * Real.log ((X ^ 5 : ℕ) : ℝ))) := by ring
      _ <
          agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
            ((X : ℝ) ^ 3 / (4 * Real.log ((X ^ 5 : ℕ) : ℝ))) :=
        hmul
      _ =
          agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
            (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) :=
        by ring
  have hmargin' :
    8 * (2 ^ Dexc : ℝ) * ((X ^ 3 : ℕ) : ℝ) * b <
      agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
        (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
    rw [hXcubeCast]
    exact hmargin
  have hmainNonneg : 0 ≤ ((X : ℝ) ^ 3 / 4) := by
    exact div_nonneg (by exact_mod_cast Nat.zero_le (X ^ 3)) (by norm_num only : (0 : ℝ) ≤ 4)
  have hbetaMain :
    agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
        ((X : ℝ) ^ 3 / 4) ≤
      (X : ℝ) ^ 3 / 4 :=
    calc
      _ ≤ 1 * ((X : ℝ) ^ 3 / 4) := mul_le_mul_of_nonneg_right hbetaOne hmainNonneg
      _ = (X : ℝ) ^ 3 / 4 := by ring
  have hmainLog : (X : ℝ) ^ 3 / 4 ≤ ((X : ℝ) ^ 3 / 4) * Real.log ((X ^ 5 : ℕ) : ℝ) := by
    calc
      (X : ℝ) ^ 3 / 4 = ((X : ℝ) ^ 3 / 4) * 1 := by ring
      _ ≤ ((X : ℝ) ^ 3 / 4) * Real.log ((X ^ 5 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogXfive.le hmainNonneg
  have hcupper :
    agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
        (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      ((X ^ 3 : ℕ) : ℝ) / 4 := by
    rw [hXcubeCast]
    have hXfiveGtOne : (1 : ℝ) < ((X ^ 5 : ℕ) : ℝ) :=
      lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 3) hXfiveReal
    calc
      _ =
          (agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient
                reciprocalBound *
              ((X : ℝ) ^ 3 / 4)) /
            Real.log ((X ^ 5 : ℕ) : ℝ) :=
        by rw [← mul_div_assoc]
      _ ≤ (X : ℝ) ^ 3 / 4 :=
        (div_le_iff₀ (Real.log_pos hXfiveGtOne)).2 (le_trans hbetaMain hmainLog)
  have hsmall : 4 * (2 ^ Dexc : ℝ) * b ≤ 1 := by nlinarith only [hmargin', hcupper, hMpos]
  have hloss :
    ((((positiveCoprimeParameters aux.L (X ^ 3)).card * T : ℕ) : ℝ) +
          (agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient
                reciprocalBound *
              (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ))) *
            ((aux.q : ℝ) + 1)) *
        (2 ^ Dexc : ℝ) <
      (agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
          (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ))) *
        H := by
    have hbudget :=
      agp_exceptional_loss_budget_of_source_count
        (agpFifthPowerAverageCoefficientOfProgressionBound progressionCoefficient reciprocalBound *
          (((X : ℝ) ^ 3 / 4) / Real.log ((X ^ 5 : ℕ) : ℝ)))
        H ((positiveCoprimeParameters aux.L (X ^ 3)).card : ℝ) ((X ^ 3 : ℕ) : ℝ) (T : ℝ) (aux.q : ℝ)
        (2 ^ Dexc : ℝ) b B hApos hMpos hHpos hbpos hqnonneg hK (by exact_mod_cast Nat.zero_le T)
        hTupper hBqReal hBOneReal hsource hsmall hmargin'
    simpa only [Nat.cast_mul, B, b, H] using hbudget
  have hthreshold : x₂₁ ≤ X ^ 5 := le_trans hthresholdSeed (le_trans aux.hLargeEnough hSeedBound)
  let hSeedInput := aux.hProp15Input
  let hCq := aux.hCq
  let hfactor := aux.hfactor
  let hlambda := aux.hlambda
  let hProp15Input :
    ∀ k, k ∈ positiveCoprimeParameters L (X ^ 3) → ReliableProp15Admissible L 4 y k (X ^ 5) :=
    fun k hk =>
    reliableProp15Admissible_of_modFourInput hSeedInput hSeedBound hcut
      (reliableProp15ParamPowerBound_of_le_cube (mem_positiveCoprimeParameters.mp hk).2.1)
  have hXweak : 82944 ≤ X := by
    have hnum : 82944 ≤ 2 ^ 56 := by norm_num only
    exact le_trans hnum hX
  have hXstrong : 5184000000000000 ≤ X := by
    have hnum : 5184000000000000 ≤ 2 ^ 56 := by norm_num only
    exact le_trans hnum hX
  have hmodulus :
    ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q,
      (18000000 * ((d * 4 : ℕ) : ℝ)) ^ 2 ≤ ((d * X ^ 3 : ℕ) : ℝ) := by
    intro d hdD
    have hmodNat :=
      progressionTheta_millionth_modulus_square_bound_of_agp_fifth_power_scale X d (4 * d) hXstrong
        (hd d hdD) (by exact le_rfl)
    have hmod : (18000000 * ((4 * d : ℕ) : ℝ)) ^ 2 ≤ ((d * X ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast hmodNat
    simpa only [Nat.mul_comm d 4] using hmod
  let hprimeSet :=
    exists_prime_set_from_agp_fifth_power_exceptional_loss_theta_and_brun_titchmarsh_bounds E X 4 3
      aux.L y aux.q Dexc T progressionCoefficient reciprocalBound hprogressionCoefficient hcoeff
      hXweak (by norm_num only) (Nat.ne_of_gt (lt_trans Nat.zero_lt_two hL)) hSeedInput.1
      hSeedInput.2.1 hEconditions.1 hEconditions.2 hEcard hpos hd hdm (by norm_num only) hmodulus
      htheta hrecip hBT hloss
  let k := Classical.choose hprimeSet
  have hk : k ∈ positiveCoprimeParameters L (X ^ 3) := (Classical.choose_spec hprimeSet).1
  let hPExists :
    ∃ P : Finset ℕ,
      T < P.card ∧
        ∀ p ∈ P,
          Nat.Prime p ∧
            p ≤ X ^ 5 ∧
            p % 4 = 3 ∧
            ∃ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q,
              p = d * k + 1 ∧ ∀ e ∈ E, ¬e ∣ d * 4 :=
    (Classical.choose_spec hprimeSet).2
  let P := Classical.choose hPExists
  have hPcard : T < P.card := (Classical.choose_spec hPExists).1
  have hP := (Classical.choose_spec hPExists).2
  have hkFields := mem_positiveCoprimeParameters.mp hk
  have hP' :
    ∀ p ∈ P,
      Nat.Prime p ∧
        p ≤ X ^ 5 ∧
        p % 4 = 3 % 4 ∧
        ∃ d,
          d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus L E 4) y q ∧
            p = d * k + 1 := by
    intro p hp
    obtain ⟨hpPrime, hpx, hpm, d, hdD, hpeq, _⟩ := hP p hp
    exact ⟨hpPrime, hpx, by simpa only using hpm, d, hdD, hpeq⟩
  exact
    agpProgressionCountData_of_large_exceptionalFreePart_prime_set W C c₀ x₀ L y q (X ^ 5) k T 4 E P
      hL hSeedInput.1 hLargeEnough (hProp15Input k hk) hCq hfactor hlambda hkFields.1 hkFields.2.2
      hlower hcount hP' hPcard

end PseudoPrime.AnalyticNumberTheory.AGP
