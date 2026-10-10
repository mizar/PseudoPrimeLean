/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperDefinitions

/-!
# Numbered statements of arXiv:1309.3595v3

These are proposition definitions, not proofs or axioms. Each source label identifies
one numbered theorem, corollary, lemma, or proposition in the published document.
Independent occurrences of theta are quantified independently, as stipulated in Section 2.
Asymptotic bounds use epsilon thresholds uniform over subgroups of a fixed index.
Supporting mathematical objects are defined in `PaperDefinitions.lean`.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Theorem 1.1 (`thmexplicit`): under GRH, both proper-subgroup bounds for `q ≥ 3000`.
The existing specifications retain the endpoint convention in Part 2. -/
def lls_theorem11 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis → llsTheorem11S1 ∧ llsTheorem11S2

/-- Corollary 1.1 (`corexplicit`): under GRH, the least quadratic nonresidue of
a prime modulus `q ≥ 5` is strictly below `(log q)²`. The least positive nonresidue
is stated directly; it is not replaced by a character-kernel specialization. -/
def lls_corollary11 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ q : ℕ,
      q.Prime →
        5 ≤ q →
        ∃ n : ℕ, IsLeast {m : ℕ | 0 < m ∧ ¬IsSquare (m : ZMod q)} n ∧ (n : ℝ) < (Real.log q) ^ 2

/-- Theorem 1.2 (`thmtheoretical1`): for each fixed subgroup index `h > 1`,
GRH bounds the least eligible prime by `(α(h) + ε)(log q)²` once `q` is large
enough. The threshold may depend on `h` and `ε`, but not on the subgroup. -/
def lls_theorem12 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ h : ℕ,
      1 < h →
        ∀ ε : ℝ,
          0 < ε →
            ∃ Q : ℕ,
              ∀ (q : ℕ) [NeZero q],
                Q ≤ q →
                  ∀ H : Subgroup (ZMod q)ˣ,
                    H.index = h →
                      ∃ p : ℕ,
                        IsLeast (primesOutside q H) p ∧
                          (p : ℝ) < (theoreticalCoefficient h + ε) * (Real.log q) ^ 2

/-- Theorem 1.3 (`thmtheoretical2`): the refined fixed-index asymptotic bound
for `h ≥ 4`. The epsilon replaces the `o(1)` beside `1/4`, before the two
index-dependent factors; the threshold is uniform over subgroups of that index. -/
def lls_theorem13 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ h : ℕ,
      4 ≤ h →
        ∀ ε : ℝ,
          0 < ε →
            ∃ Q : ℕ,
              ∀ (q : ℕ) [NeZero q],
                Q ≤ q →
                  ∀ H : Subgroup (ZMod q)ˣ,
                    H.index = h →
                      ∃ p : ℕ,
                        IsLeast (primesOutside q H) p ∧
                          (p : ℝ) <
                            (1 / 4 + ε) * (1 - 1 / (h : ℝ)) ^ 2 *
                              (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2 *
                              (Real.log q) ^ 2

/-- Theorem 1.3 restricted to subgroup indices at least seven. Under GRH,
this defines the same coefficient and uniform epsilon threshold as the full
statement, with only the lower bound on the fixed index strengthened. -/
def lls_theorem13_of_index_ge_seven : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ h : ℕ,
      7 ≤ h →
        ∀ ε : ℝ,
          0 < ε →
            ∃ Q : ℕ,
              ∀ (q : ℕ) [NeZero q],
                Q ≤ q →
                  ∀ H : Subgroup (ZMod q)ˣ,
                    H.index = h →
                      ∃ p : ℕ,
                        IsLeast (primesOutside q H) p ∧
                          (p : ℝ) <
                            (1 / 4 + ε) * (1 - 1 / (h : ℝ)) ^ 2 *
                              (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2 *
                              (Real.log q) ^ 2

/-- Theorem 1.4 (`thmcoset`): under GRH and `q ≥ 20000`, the least prime in
any coset of a subgroup of index greater than one either is at most `10⁹`
or satisfies the displayed bound involving the subgroup index. -/
def lls_theorem14 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ (q : ℕ) [NeZero q],
      20000 ≤ q →
        ∀ H : Subgroup (ZMod q)ˣ,
          1 < H.index →
            ∀ a : (ZMod q)ˣ,
              ∃ p : ℕ,
                IsLeast (primesInCoset q H a) p ∧
                  ((p : ℝ) ≤ 10 ^ 9 ∨
                    (p : ℝ) ≤
                      (((H.index : ℝ) - 1) * Real.log q + 3 * ((H.index : ℝ) + 1) +
                          5 / 2 * (Real.log (Real.log q)) ^ 2) ^
                        2)

/-- Corollary 1.2 (`thmexplicit2`): under GRH, for `q > 3` and a reduced
residue class `a`, the least prime in that class is at most `(φ(q) log q)²`.
A unit supplies precisely the reduced-residue assumption. -/
def lls_corollary12 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ (q : ℕ) [NeZero q],
      3 < q →
        ∀ a : (ZMod q)ˣ,
          ∃ p : ℕ,
            IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
              (p : ℝ) ≤ ((Nat.totient q : ℝ) * Real.log q) ^ 2

/-- Theorem 1.5 (`L1chi`): under GRH, both explicit bounds for the norm of
`L(1,χ)` and its reciprocal, for primitive characters of modulus at least `10¹⁰`.
Both inequalities use the same character and its actual continued `L`-function. -/
def lls_theorem15 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      10 ^ 10 ≤ q →
        χ.IsPrimitive →
        ‖χ.LFunction 1‖ ≤ 2 * Real.exp Real.eulerMascheroniConstant * lValueUpperFactor q ∧
          1 / ‖χ.LFunction 1‖ ≤
            12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2 * lValueReciprocalFactor q

/-- Corollary 1.3 (`ClassBounds`): GRH gives the explicit lower and upper
bounds for the class number of an imaginary quadratic field of discriminant `-q`,
where `q ≥ 10¹⁰`. Degree two and the negative field discriminant identify the field
intrinsically, avoiding an arbitrary function supplied as a class-number placeholder. -/
def lls_corollary13 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ (q : ℕ) (K : Type) [Field K] [NumberField K],
      10 ^ 10 ≤ q →
        Module.finrank ℚ K = 2 →
        NumberField.discr K = -(q : ℤ) →
        Real.pi / (12 * Real.exp Real.eulerMascheroniConstant) * Real.sqrt q *
              (lValueReciprocalFactor q)⁻¹ ≤
            (NumberField.classNumber K : ℝ) ∧
          (NumberField.classNumber K : ℝ) ≤
            2 * Real.exp Real.eulerMascheroniConstant / Real.pi * Real.sqrt q * lValueUpperFactor q

/-- Lemma 2.1 (`lem1`): the full RH logarithmically weighted zeta formula
for `x > 1`, including the positive trivial-zero series and the bounded real error. -/
def lls_lemma21 : Prop :=
  RiemannHypothesis →
    ∀ x : ℝ,
      1 < x →
        ∃ θ : ℝ,
          |θ| ≤ 1 ∧
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x =
              x - Real.log (2 * Real.pi) * Real.log x - 1 +
                (∑' k : ℕ, (1 - 1 / x ^ (2 * (k + 1))) / (4 * ((k : ℝ) + 1) ^ 2)) +
                2 * θ * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1)

/-- Lemma 2.2 (`lem2`): both the complex explicit formula and its real-part
consequence, for primitive characters of level at least three under GRH and `x > 1`.
The two complex errors and two real errors are independently bounded by one. -/
def lls_lemma22 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      3 ≤ q →
        χ.IsPrimitive →
        ∀ x : ℝ,
          1 < x →
            (∃ θ₁ θ₂ : ℂ,
                ‖θ₁‖ ≤ 1 ∧
                  ‖θ₂‖ ≤ 1 ∧
                  AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ =
                    ((|AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| : ℝ) : ℂ) *
                          (2 * θ₁ * (Real.sqrt x : ℂ) + 2 * θ₂) -
                        logDeriv (xi χ) 0 * (Real.log x : ℂ) +
                      ((Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + logCorrection χ x : ℝ) :
                        ℂ)) ∧
              (∃ θ₁ θ₂ : ℝ,
                |θ₁| ≤ 1 ∧
                  |θ₂| ≤ 1 ∧
                  (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ).re =
                    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| *
                        (2 * θ₁ * Real.sqrt x + 2 * θ₂ + Real.log x) +
                      Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 +
                      logCorrection χ x)

/-- Lemma 2.3 (`lem3`): the reciprocal explicit formula and the resulting
inverse-factor identity for `|Re B(χ)|`. The inverse character realizes conjugation;
the real error in the consequence is quantified separately from the complex error. -/
def lls_lemma23 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      3 ≤ q →
        χ.IsPrimitive →
        ∀ x : ℝ,
          1 < x →
            (∃ θ : ℂ,
                ‖θ‖ ≤ 1 ∧
                  -logDeriv (xi χ⁻¹) 0 - (1 / (x : ℂ)) * logDeriv (xi χ) 0 +
                      2 * θ / (Real.sqrt x : ℂ) *
                        ((|AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| : ℝ) : ℂ) =
                    ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) +
                            reciprocalCorrection χ x :
                          ℝ) :
                        ℂ) -
                      AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ) ∧
              (∃ θ : ℝ,
                |θ| ≤ 1 ∧
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| =
                    (1 + 2 * θ / Real.sqrt x + 1 / x)⁻¹ *
                      (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) -
                          (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
                        reciprocalCorrection χ x))

/-- Lemma 2.4 (`lem4`): the exact RH reciprocal zeta formula for `x > 1`,
including Euler's constant, the trivial-zero series, and a bounded real error. -/
def lls_lemma24 : Prop :=
  RiemannHypothesis →
    ∀ x : ℝ,
      1 < x →
        ∃ θ : ℝ,
          |θ| ≤ 1 ∧
            AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x =
              Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x -
                  (∑' k : ℕ,
                    1 / (x ^ (2 * (k + 1) + 1) * (2 * ((k : ℝ) + 1)) * (2 * ((k : ℝ) + 1) + 1))) +
                2 * θ * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x

/-- Lemma 2.5 (`propL1`): under the RH predicate for the given primitive
character, the formula for `log |L(1,χ)|` at `x ≥ 2`. The digamma special values
are written explicitly by parity. Its two theta occurrences are independent. -/
def lls_lemma25 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3 ≤ q →
      χ.IsPrimitive →
      AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ →
      ∀ x : ℝ,
        2 ≤ x →
          ∃ θ₁ θ₂ : ℝ,
            |θ₁| ≤ 1 ∧
              |θ₂| ≤ 1 ∧
              Real.log ‖χ.LFunction 1‖ =
                (characterLogLValueSum χ x).re +
                      (1 / Real.log x) *
                        (Real.log ((q : ℝ) / Real.pi) / 2 +
                          (if χ (-1) = 1 then -2 * Real.log 2 - Real.eulerMascheroniConstant
                            else -Real.eulerMascheroniConstant) /
                            2) -
                    (1 / Real.log x + 2 * θ₁ / (Real.sqrt x * (Real.log x) ^ 2)) *
                      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
                  2 * θ₂ / (x * (Real.log x) ^ 2)

/-- Lemma 2.6 (`lem6`): under RH and `x ≥ e`, the logarithmic zeta sum
equals its main term with two independent real errors. The signed Hadamard
constant is `B = log(4π)/2 - 1 - γ/2`, rather than its absolute value. -/
def lls_lemma26 : Prop :=
  RiemannHypothesis →
    ∀ x : ℝ,
      Real.exp 1 ≤ x →
        ∃ θ₁ θ₂ : ℝ,
          |θ₁| ≤ 1 ∧
            |θ₂| ≤ 1 ∧
            logLValueSum x =
              Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 +
                Real.eulerMascheroniConstant / Real.log x +
                2 * (Real.log (4 * Real.pi) / 2 - 1 - Real.eulerMascheroniConstant / 2) * θ₁ /
                  (Real.sqrt x * (Real.log x) ^ 2) +
                θ₂ / (3 * x ^ 3 * (Real.log x) ^ 2)

/-- Lemma 3.1 (`lem5`): for `m ≥ 3` and `x ≥ 2`, both common-factor bounds,
including equality of the unrestricted reciprocal sum with the prime-factor sum.
The infinite sum includes positive natural indices, not an unspecified finite cutoff. -/
def lls_lemma31 : Prop :=
  ∀ (m : ℕ) (x : ℝ),
    3 ≤ m →
      2 ≤ x →
      AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x m ≤
          (m.primeFactors.card : ℝ) * (Real.log x) ^ 2 / 2 ∧
        AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum x m ≤
          (∑' n : ℕ,
            if 0 < n ∧ ¬Nat.Coprime n m then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) ∧
        (∑' n : ℕ,
            if 0 < n ∧ ¬Nat.Coprime n m then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) =
          AnalyticNumberTheory.Arithmetic.primeFactorLogSum m

/-- Lemma 5.1 (`lemma5.1`): for any Dirichlet character and `x ≥ 100`,
the real logarithmic prime-power sum is bounded below by the alternating sum.
No primitivity or GRH assumption is introduced into this elementary statement. -/
def lls_lemma51 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ),
    100 ≤ x →
      alternatingPrimePowerSum x ≤
        (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            χ n *
              (ArithmeticFunction.vonMangoldt n *
                  (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) :
                ℝ)).re

/-- Lemma 6.1 (`lemma6.1`): GRH gives the principal and nonprincipal smoothed
character estimates for an admissible Mellin kernel. The `O` constant depends on
the kernel and is uniform in modulus, subgroup, character, and `x ≥ 2`.
The nonprincipal `o(1)` is expressed by an arbitrary positive epsilon and a
modulus threshold. A bounded real theta retains the signed main contribution. -/
def lls_lemma61 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ K : MellinKernel,
      ∃ C : ℝ,
        0 < C ∧
          ∀ ε : ℝ,
            0 < ε →
              ∃ Q : ℕ,
                3 ≤ Q ∧
                  ∀ (q : ℕ) [NeZero q],
                    Q ≤ q →
                      ∀ H : Subgroup (ZMod q)ˣ,
                        H ≠ ⊤ →
                          ∀ χ : DirichletCharacter ℂ q,
                            NumberTheory.annihilatesSubgroup χ H →
                              ∀ x : ℝ,
                                2 ≤ x →
                                  Summable (K.summand χ x) ∧
                                    (χ = 1 →
                                      ‖(∑' n : ℕ, K.summand χ x n) -
                                            K.function (1 / 2) * (Real.sqrt x : ℂ)‖ ≤
                                        C * (1 + Real.log q * Real.log x / Real.sqrt x)) ∧
                                    (χ ≠ 1 →
                                      ∃ θ r : ℝ,
                                        |θ| ≤ 1 ∧
                                          |r| ≤ C * (1 + Real.log q * Real.log x / Real.sqrt x) ∧
                                          (∑' n : ℕ, K.summand χ x n).re =
                                            θ * (1 + ε) * Real.log q * K.mass + r)

/-- Proposition 6.1 (`prop:theoretical`): under GRH, if all eligible primes
through `X` lie in a subgroup of fixed index `h > 1`, then the kernel inequality
holds for every fixed `λ > 0`, with `1 + o(1)` expressed by `1 + ε` for sufficiently
large modulus. The threshold may depend on the kernel, index, lambda, and epsilon;
it is uniform in the subgroup and positive cutoff `X`. -/
def lls_proposition61 : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ K : MellinKernel,
      ∀ h : ℕ,
        1 < h →
          ∀ lambda : ℝ,
            0 < lambda →
              ∀ ε : ℝ,
                0 < ε →
                  ∃ Q : ℕ,
                    ∀ (q : ℕ) [NeZero q],
                      Q ≤ q →
                        ∀ H : Subgroup (ZMod q)ˣ,
                          H.index = h →
                            ∀ X : ℝ,
                              0 < X →
                                (∀ p : ℕ,
                                  p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) →
                                ((h : ℝ) *
                                        intervalIntegral
                                          (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) 0 lambda
                                          MeasureTheory.volume -
                                      (K.function (1 / 2)).re) *
                                    Real.sqrt X ≤
                                  (1 + ε) * Real.sqrt lambda * ((h : ℝ) - 1) * Real.log q * K.mass

end PseudoPrime.LLS.PaperStatements
