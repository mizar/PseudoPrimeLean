/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Statement
public import PseudoPrime.NumberTheory.SubgroupAnnihilator
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.HadamardLimit
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Auxiliary objects used to state the numbered results of arXiv:1309.3595v3. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Membership of a natural residue in the image of a subgroup of units.
Nonunits are outside this image. Used for the subgroup prime bounds. -/
def residueInSubgroup (q : ℕ) (H : Subgroup (ZMod q)ˣ) (n : ℕ) : Prop :=
  ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (n : ZMod q)

/-- The eligible primes outside `H`: prime divisors of the modulus are excluded.
Its least element is the prime appearing in Theorems 1.1--1.3. -/
def primesOutside (q : ℕ) (H : Subgroup (ZMod q)ˣ) : Set ℕ :=
  {p | p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p}

/-- Prime residues in the coset `aH`, described by the quotient of units.
Used to express the least prime in Theorem 1.4. -/
def primesInCoset (q : ℕ) (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) : Set ℕ :=
  {p | p.Prime ∧ ∃ u : (ZMod q)ˣ, a⁻¹ * u ∈ H ∧ (u : ZMod q) = (p : ZMod q)}

/-- The coefficient in Theorem 1.2: `0.8`, `0.7`, and `0.66` for indices
two, three, and greater than three. Only indices greater than one are used. -/
noncomputable def theoreticalCoefficient (h : ℕ) : ℝ :=
  if h = 2 then 4 / 5 else if h = 3 then 7 / 10 else 33 / 50

/-- The logarithmic factor in the upper bound for `|L(1,χ)|` and the class number.
The input is the modulus; Theorem 1.5 uses it only for `q ≥ 10¹⁰`. -/
noncomputable def lValueUpperFactor (q : ℕ) : ℝ :=
  Real.log (Real.log q) - Real.log 2 + 1 / 2 + 1 / Real.log (Real.log q)

/-- The additional factor in the reciprocal `L`-value and class-number lower bounds.
It adds `14 log log q / log q` to the upper factor. -/
noncomputable def lValueReciprocalFactor (q : ℕ) : ℝ :=
  lValueUpperFactor q + 14 * Real.log (Real.log q) / Real.log q

/-- The paper's `ξ(s,χ) = q^(s/2) completedLFunction χ s` for a primitive character.
This level-scaled normalization is used in the logarithmic derivatives at zero. -/
noncomputable def xi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s / 2) * χ.completedLFunction s

/-- The real correction `Ẽ₀(x)` for even characters in Lemma 2.2.
The series is indexed from one by replacing `k` with `k + 1`. -/
noncomputable def logCorrectionEven (x : ℝ) : ℝ :=
  Real.pi ^ 2 / 24 - Real.eulerMascheroniConstant / 2 * Real.log x - (Real.log x) ^ 2 / 2 -
    ∑' k : ℕ, 1 / (x ^ (2 * (k + 1)) * (2 * ((k : ℝ) + 1)) ^ 2)

/-- The real correction `Ẽ₁(x)` for odd characters in Lemma 2.2.
Its series starts with the exponent one. -/
noncomputable def logCorrectionOdd (x : ℝ) : ℝ :=
  Real.pi ^ 2 / 8 - (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x -
    ∑' k : ℕ, 1 / (x ^ (2 * k + 1) * (2 * (k : ℝ) + 1) ^ 2)

/-- The correction `Ẽₐ(x)` chosen by the parity of the character.
Dirichlet characters are even or odd; the even branch corresponds to `a = 0`. -/
noncomputable def logCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  if χ (-1) = 1 then logCorrectionEven x else logCorrectionOdd x

/-- The real correction `E₀(x)` in Lemma 2.3, including its reciprocal tail. -/
noncomputable def reciprocalCorrectionEven (x : ℝ) : ℝ :=
  -Real.log 2 - Real.eulerMascheroniConstant / 2 * (1 - 1 / x) + (Real.log x + 1) / x -
    ∑' k : ℕ, 1 / (x ^ (2 * (k + 1) + 1) * (2 * ((k : ℝ) + 1)) * (2 * ((k : ℝ) + 1) + 1))

/-- The real correction `E₁(x)` in Lemma 2.3, with the series indexed from zero. -/
noncomputable def reciprocalCorrectionOdd (x : ℝ) : ℝ :=
  -(∑' k : ℕ, 1 / (x ^ (2 * k + 2) * (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2))) -
      Real.eulerMascheroniConstant / 2 * (1 - 1 / x) +
    Real.log 2 / x

/-- The correction `Eₐ(x)` chosen by character parity, for Lemma 2.3. -/
noncomputable def reciprocalCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  if χ (-1) = 1 then reciprocalCorrectionEven x else reciprocalCorrectionOdd x

/-- The finite real sum with weight `Λ(n)/(n log n) * log(x/n)/log x`.
The index one contributes zero under Lean's total division convention. -/
noncomputable def logLValueSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) * (Real.log (x / n) / Real.log x)

/-- For a complex Dirichlet character and any real cutoff `x`, define the finite
sum over `0 < n ≤ floor x` with weight `χ(n) Λ(n)/(n log n) * log(x/n)/log x`.
The index one contributes zero under total division. For primitive characters of level
at least three satisfying their RH predicate and `x ≥ 2`, Lemma 2.5 relates its real part
to `log ‖L(1,χ)‖` through explicit gamma, zero-mass, and bounded error terms. -/
noncomputable def characterLogLValueSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    χ n *
      (ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) * (Real.log (x / n) / Real.log x) :
        ℝ)

/-- The finite sum over prime powers weighted by the alternating value `(-1)^k`.
It is the comparison term in Lemma 5.1; exponents range from one through `p.log ⌊x⌋₊`. -/
noncomputable def alternatingPrimePowerSum (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊,
    ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
      ArithmeticFunction.vonMangoldt (p ^ k) * (-1 : ℝ) ^ k *
        (1 / ((p : ℝ) ^ k * Real.log ((p : ℝ) ^ k)) - 1 / (x * Real.log x))

/-- Inverse Mellin integral of `K` on the vertical line of real part `c`.
The parameterization `s = c + it` cancels the `i` in `ds/(2πi)`.
For an admissible kernel it agrees on all the allowed vertical lines. -/
noncomputable def inverseMellin (K : ℂ → ℂ) (c u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    MeasureTheory.integral MeasureTheory.volume
      (fun t : ℝ ↦ K ((c : ℂ) + Complex.I * t) * (u : ℂ) ^ (-((c : ℂ) + Complex.I * t)))

/-- The kernel assumptions preceding Lemma 6.1.
`region` is an open region containing the stated strip; `regularized` removes the
possible simple pole at `-1/2`. The decay bound is uniform away from that pole.
The vertical inverse Mellin integrals are integrable and agree, and their common
value is nonnegative and real for positive arguments, and is nonzero somewhere.
These are assumptions on a
kernel, not assumptions of Lemma 6.1's conclusion. -/
structure MellinKernel where
  /-- The holomorphic function, possibly with a simple pole at `-1/2`. -/
  function : ℂ → ℂ
  /-- The positive width extending the strip past both endpoints. -/
  delta : ℝ
  /-- The strip width is positive. -/
  delta_pos : 0 < delta
  /-- An open region containing the strip specified in Section 6. -/
  region : Set ℂ
  /-- The region is open, so holomorphy is meaningful at the upper boundary. -/
  region_open : IsOpen region
  /-- The paper's strip, with its closed upper boundary, is contained in the region. -/
  strip_subset : {s : ℂ | -1 / 2 - delta < s.re ∧ s.re ≤ 1 / 2 + delta} ⊆ region
  /-- Holomorphy away from the possible pole. -/
  holomorphic : DifferentiableOn ℂ function (region \ {(-1 / 2 : ℂ)})
  /-- Holomorphic extension of `(s + 1/2) K(s)` across the possible simple pole. -/
  regularized : ℂ → ℂ
  /-- The extension is holomorphic throughout the region. -/
  regularized_holomorphic : DifferentiableOn ℂ regularized region
  /-- Away from the pole, the extension agrees with the product. -/
  regularized_eq : ∀ s ∈ region, s ≠ -1 / 2 → regularized s = (s + 1 / 2) * function s
  /-- Quadratic decay, with the constant allowed to depend on distance from the pole. -/
  decay :
    ∀ η : ℝ,
      0 < η → ∃ C : ℝ, 0 < C ∧ ∀ s ∈ region, η ≤ ‖s + 1 / 2‖ → ‖function s‖ ≤ C / (1 + ‖s‖ ^ 2)
  /-- Absolute integrability of the inverse Mellin integral on each allowed line. -/
  mellin_integrable :
    ∀ c u : ℝ,
      -1 / 2 < c →
        c ≤ 1 / 2 + delta →
        0 < u →
        MeasureTheory.Integrable
          (fun t : ℝ ↦ function ((c : ℂ) + Complex.I * t) * (u : ℂ) ^ (-((c : ℂ) + Complex.I * t)))
  /-- Independence of the allowed vertical line in Mellin inversion. -/
  mellin_eq :
    ∀ c u : ℝ,
      -1 / 2 < c →
        c ≤ 1 / 2 + delta → 0 < u → inverseMellin function c u = inverseMellin function 0 u
  /-- Nonnegativity of the real inverse Mellin transform on positive arguments. -/
  mellin_nonneg : ∀ u : ℝ, 0 < u → 0 ≤ (inverseMellin function 0 u).re
  /-- The real transform is nonzero at some positive argument. Together with
  nonnegativity, this ensures positive mass and admits compactly supported transforms. -/
  mellin_nonzero : ∃ u : ℝ, 0 < u ∧ (inverseMellin function 0 u).re ≠ 0
  /-- The transform is real-valued, as required by the positivity assumption. -/
  mellin_real : ∀ u : ℝ, 0 < u → (inverseMellin function 0 u).im = 0

/-- The transform `K̃(u)`, evaluated on the line of real part zero. -/
noncomputable def MellinKernel.transform (K : MellinKernel) (u : ℝ) : ℂ :=
  inverseMellin K.function 0 u

/-- The factor `(2π)⁻¹ ∫ |K(it)| dt` in Lemma 6.1 and Proposition 6.1. -/
noncomputable def MellinKernel.mass (K : MellinKernel) : ℝ :=
  MeasureTheory.integral MeasureTheory.volume (fun t : ℝ ↦ ‖K.function (Complex.I * t)‖) /
    (2 * Real.pi)

/-- The individual smoothed Mangoldt term for a kernel, character, real cutoff
`x`, and natural index `n`: zero at `n = 0`, and `Λ(n)/sqrt n * χ(n) * K̃(n/x)` otherwise.
These terms form the infinite sum in Lemma 6.1. Summability is separately required in
that proposition and proved for positive `x`, rather than asserted by this definition. -/
noncomputable def MellinKernel.summand (K : MellinKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else (ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) * χ n * K.transform (n / x)

end PseudoPrime.LLS.PaperStatements
