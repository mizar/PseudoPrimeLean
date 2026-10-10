/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Tactic
public import PseudoPrime.NumberTheory.QuadraticFieldTorsion
public import PseudoPrime.NumberTheory.ImaginaryQuadraticInvariants

/-!
# Dirichlet L-values and quadratic class-number formulas

A divisor-sum formula for integral ideal counts gives `ζ_K = ζ L` to the right
of one. Comparing residues identifies `L(1,χ)` for a nonprincipal character.
For a quadratic field of discriminant `-q`, `q > 4`, the signature, regulator
and torsion order specialize the residue to `π h_K / sqrt q`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory

/-- Real points approaching one from above approach one in the punctured
complex plane. Continuity of the real embedding gives convergence, while
s > 1 excludes equality with one. Used to restrict the zeta residue limit. -/
private theorem realCast_tendsto_one_punctured :
    Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin 1 ({1}ᶜ : Set ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds : nhdsWithin (1 : ℝ) (Set.Ioi 1) ≤ nhds 1)
  · apply (eventually_mem_nhdsWithin : ∀ᶠ s in nhdsWithin (1 : ℝ) (Set.Ioi 1), s ∈ Set.Ioi 1).mono
    intro s hs
    change (s : ℂ) ≠ 1
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at hr
    exact (ne_of_gt hs) hr

/-- The product (s-1)ζ(s) tends to one as real s tends to one from above.
Compose the complex residue limit with the real embedding into the punctured
neighborhood. This is the pole contribution in a quadratic factorization. -/
private theorem riemannZeta_residue_real_right :
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta s) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (1 : ℂ)) := by
  exact riemannZeta_residue_one.comp realCast_tendsto_one_punctured

/-- For a nonprincipal character, a factorization ζ_K(s)=ζ(s)L(s,χ) on the
real half-line s > 1 implies (s-1)ζ_K(s) tends to L(1,χ) from the right.
Multiply the zeta residue limit by continuity of the L-function, then use
pointwise factorization. Used to identify the general class-number residue. -/
private theorem dedekindZeta_residue_limit_of_factorization (K : Type) [Field K] [NumberField K]
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hf : ∀ s : ℝ, 1 < s → NumberField.dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * NumberField.dedekindZeta K s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (χ.LFunction 1)) := by
  have hc := (DirichletCharacter.differentiableAt_LFunction χ 1 (Or.inr hne)).continuousAt
  have hcast := realCast_tendsto_one_punctured.mono_right nhdsWithin_le_nhds
  have hL := hc.tendsto.comp hcast
  have hp := riemannZeta_residue_real_right.mul hL
  simp only [one_mul] at hp
  have he :
    Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (fun s => (((s : ℂ) - 1) * riemannZeta s) * χ.LFunction s)
      (fun s => ((s : ℂ) - 1) * NumberField.dedekindZeta K s) := by
    apply (eventually_mem_nhdsWithin : ∀ᶠ s in nhdsWithin (1 : ℝ) (Set.Ioi 1), s ∈ Set.Ioi 1).mono
    intro s hs
    change
      (((s : ℂ) - 1) * riemannZeta s) * χ.LFunction s = ((s : ℂ) - 1) * NumberField.dedekindZeta K s
    rw [hf s hs]
    ring
  exact hp.congr' he

/-- For a nonprincipal character with ζ_K(s)=ζ(s)L(s,χ) for real s > 1,
L(1,χ) equals the complex embedding of the positive Dedekind zeta residue.
Uniqueness of limits compares the product limit with the general class-number
formula. This identifies the L-value once factorization has been established. -/
theorem LFunction_one_eq_dedekindZeta_residue_of_factorization (K : Type) [Field K] [NumberField K]
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hf : ∀ s : ℝ, 1 < s → NumberField.dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.LFunction 1 = (NumberField.dedekindZeta_residue K : ℂ) := by
  exact
    tendsto_nhds_unique (dedekindZeta_residue_limit_of_factorization K χ hne hf)
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)

/-- For a nonprincipal character with the stated Dedekind factorization,
the norm of L(1,χ) is the positive Dedekind zeta residue. Take norms in the
complex residue identity and use positivity. This is the real-valued interface
needed by the imaginary quadratic class-number bound. -/
theorem norm_LFunction_one_eq_dedekindZeta_residue_of_factorization (K : Type) [Field K]
    [NumberField K] {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hf : ∀ s : ℝ, 1 < s → NumberField.dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    ‖χ.LFunction 1‖ = NumberField.dedekindZeta_residue K := by
  rw [LFunction_one_eq_dedekindZeta_residue_of_factorization K χ hne hf, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (NumberField.dedekindZeta_residue_pos K)]

/-- If the number of integral ideals of every positive norm n equals the
divisor-antidiagonal sum of a character, then ζ_K(s)=ζ(s)L(s,χ) for Re(s)>1.
Interpret the coefficients as Dirichlet convolution and multiply the two
absolutely convergent L-series. The value at zero is irrelevant to L-series.
This reduces factorization to the arithmetic count of ideals. -/
theorem dedekindZeta_factorization_of_ideal_count (K : Type) [Field K] [NumberField K] {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q)
    (hc :
      ∀ n : ℕ,
        n ≠ 0 →
          (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } : ℂ) =
            ∑ p ∈ n.divisorsAntidiagonal, χ (p.2 : ℕ))
    {s : ℂ} (hs : 1 < s.re) : NumberField.dedekindZeta K s = riemannZeta s * χ.LFunction s := by
  have he :
    ∀ {n : ℕ},
      n ≠ 0 →
        (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } : ℂ) =
          LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => χ n) n := by
    intro n hn
    rw [LSeries.convolution_def]
    simpa only [Pi.one_apply, one_mul] using hc n hn
  rw [NumberField.dedekindZeta, LSeries_congr he,
    LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs),
    LSeries_one_eq_riemannZeta hs, ← DirichletCharacter.LFunction_eq_LSeries χ hs]

/-- For a nonprincipal character whose divisor sum counts ideals of every
positive norm, the norm of L(1,χ) equals the Dedekind zeta residue. Obtain the
half-plane factorization from convolution and apply the residue comparison.
Thus the arithmetic coefficient identity suffices to identify the L-value
norm used in the class-number bound. -/
theorem norm_LFunction_one_eq_dedekindZeta_residue_of_ideal_count (K : Type) [Field K]
    [NumberField K] {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hc :
      ∀ n : ℕ,
        n ≠ 0 →
          (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } : ℂ) =
            ∑ p ∈ n.divisorsAntidiagonal, χ (p.2 : ℕ)) :
    ‖χ.LFunction 1‖ = NumberField.dedekindZeta_residue K := by
  apply norm_LFunction_one_eq_dedekindZeta_residue_of_factorization K χ hne
  intro s hs
  exact
    dedekindZeta_factorization_of_ideal_count K χ hc (by simpa only [Complex.ofReal_re] using hs)

/-- For a degree-two field of discriminant -q with q > 4, the Dedekind zeta
residue is π h_K/√q. Substitute the proved signature, unit regulator and torsion
order two into the general residue formula. The cutoff excludes the fields
of discriminants -3 and -4; no additional invariant premise is required. -/
theorem imaginaryQuadratic_dedekindZeta_residue (q : ℕ) (hq : 4 < q) (K : Type) [Field K]
    [NumberField K] (hdeg : Module.finrank ℚ K = 2) (hd : NumberField.discr K = -(q : ℤ)) :
    NumberField.dedekindZeta_residue K = Real.pi / Real.sqrt q * NumberField.classNumber K := by
  have hdsmall : NumberField.discr K < -4 := by
    rw [hd]
    exact neg_lt_neg (by exact_mod_cast hq : (4 : ℤ) < q)
  have hdneg : NumberField.discr K < 0 := hdsmall.trans (by norm_num only : (-4 : ℤ) < 0)
  have ht := NumberTheory.quadratic_torsionOrder_eq_two K hdeg hdsmall
  have hs := NumberTheory.imaginaryQuadratic_signature K hdeg hdneg
  have hr := NumberTheory.imaginaryQuadratic_regulator_eq_one K hdeg hdneg
  rw [NumberField.dedekindZeta_residue_def, hs.1, hs.2, hr, ht, hd]
  simp only [pow_zero, pow_one, one_mul, mul_one, Nat.cast_ofNat, Int.cast_neg, Int.cast_natCast,
    abs_neg, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  ring

/-- If a character's L-value norm equals the Dedekind zeta residue of the
specified imaginary quadratic field with q > 4, then
h_K=√q norm(L(1,χ))/π. Use the specialized residue and cancel the positive
factors; this isolates the L-function identification needed by Corollary 1.3. -/
theorem imaginaryQuadratic_classNumber_formula_of_residue (q : ℕ) [NeZero q] (hq : 4 < q) (K : Type)
    [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 2) (hd : NumberField.discr K = -(q : ℤ))
    (χ : DirichletCharacter ℂ q) (hL : ‖χ.LFunction 1‖ = NumberField.dedekindZeta_residue K) :
    (NumberField.classNumber K : ℝ) = Real.sqrt q / Real.pi * ‖χ.LFunction 1‖ := by
  rw [hL, imaginaryQuadratic_dedekindZeta_residue q hq K hdeg hd]
  have hs : Real.sqrt q ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast (lt_trans (by norm_num only : (0 : ℕ) < 4) hq)))
  field_simp [hs, Real.pi_ne_zero]

end PseudoPrime.AnalyticNumberTheory
