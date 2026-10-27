/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SharpGammaPhaseInterpolation
public import PseudoPrime.Analysis.ScaledGammaPhaseNodes

/-! # Adaptive rational interval certificates for actual Gamma phases -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A finite dyadic interval partition. A leaf retains the current interval;
a split replaces it by its two midpoint halves. No validity assumption is built into the type.
Role: store adaptive analytic certificates without expanded endpoint arithmetic. -/
inductive RationalIntervalTree where
  | leaf
  | split (left right : RationalIntervalTree)

/-- Input: a rational leaf checker, interval and partition tree.
Output: true exactly when every leaf checker succeeds on its inherited interval.
Role: verify compact adaptive covers with a computational Boolean predicate. -/
def rationalIntervalTreeCheck (check : ℚ → ℚ → Bool) (a b : ℚ) : RationalIntervalTree → Bool
  | .leaf => check a b
  | .split l r =>
    rationalIntervalTreeCheck check a ((a + b) / 2) l &&
      rationalIntervalTreeCheck check ((a + b) / 2) b r

/-- Input: a sound leaf checker and a successful interval-tree check.
Claim: the pointwise property holds throughout the complete initial real interval.
Proof: induct over the tree and split each ordinate at the midpoint.
Role: separate rational certificate computation from continuous coverage reasoning. -/
theorem rationalIntervalTreeCheck_sound {P : ℝ → Prop} {check : ℚ → ℚ → Bool}
    (hLeaf : ∀ a b, check a b = true → ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), P t)
    (tree : RationalIntervalTree) (a b : ℚ) (h : rationalIntervalTreeCheck check a b tree = true) :
    ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), P t := by
  induction tree generalizing a b with
  | leaf => exact hLeaf a b h
  | split l r ihl ihr =>
    simp only [rationalIntervalTreeCheck, Bool.and_eq_true] at h
    obtain ⟨hl, hr⟩ := h
    intro t ht
    by_cases hm : t ≤ (((a + b) / 2 : ℚ) : ℝ)
    · exact ihl a ((a + b) / 2) hl t ⟨ht.1, hm⟩
    · exact ihr ((a + b) / 2) b hr t ⟨(lt_of_not_ge hm).le, ht.2⟩

/-- Input: a grid, rational phase centers and uncertainties, and two endpoints.
Output: checks the ordinate domain and both rational gaps against the exact interpolation loss.
Role: accept variable widths rather than impose a uniform global mesh. -/
def scaledPhaseIntervalCheck (G : ℕ) (v ε : ℚ → ℚ) (a b : ℚ) : Bool :=
  decide
    (0 ≤ a ∧
      a < b ∧
      b ≤ 5 ∧
      |v a| ≤ 128 ∧
      |v b| ≤ 128 ∧
      (1 / 25000 + 32768 / (G : ℚ)) + 51 * (b - a) ^ 2 ≤
        rationalScaledPhase64Lower G a (v a) (ε a) ∧
      (1 / 25000 + 32768 / (G : ℚ)) + 51 * (b - a) ^ 2 ≤ rationalScaledPhase64Lower G b (v b) (ε b))

/-- Input: a positive bounded scale, valid phase enclosures and a successful leaf check.
Claim: the actual signed Gamma phase is bounded by the resolvent throughout the leaf interval.
Proof: transfer rounded node errors and use the moment364 interpolation with total cost408.
Role: turn rational adaptive leaves into continuous spectral certificates. -/
theorem scaledPhaseIntervalCheck_sound {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8) {G : ℕ}
    (hG : 0 < G) (v ε : ℚ → ℚ)
    (hphase : ∀ s : ℚ, |(s : ℝ) * Real.log (256 * x) - (v s : ℝ)| ≤ (ε s : ℝ)) (a b : ℚ)
    (hcheck : scaledPhaseIntervalCheck G v ε a b = true) (t : ℝ)
    (ht : t ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  have hc :
    0 ≤ a ∧
      a < b ∧
      b ≤ 5 ∧
      |v a| ≤ 128 ∧
      |v b| ≤ 128 ∧
      (1 / 25000 + 32768 / (G : ℚ)) + 51 * (b - a) ^ 2 ≤
        rationalScaledPhase64Lower G a (v a) (ε a) ∧
      (1 / 25000 + 32768 / (G : ℚ)) + 51 * (b - a) ^ 2 ≤
        rationalScaledPhase64Lower G b (v b) (ε b) :=
    of_decide_eq_true hcheck
  have hab : (a : ℝ) < b := Rat.cast_lt.mpr hc.2.1
  have ha0 : (0 : ℝ) ≤ a := Rat.cast_nonneg.mpr hc.1
  have hb5 : (b : ℝ) ≤ 5 := by exact_mod_cast hc.2.2.1
  have hca := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.1
  have hcb := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.2.1
  norm_num only [Rat.cast_abs, Rat.cast_ofNat] at hca hcb
  have hA := rationalScaledPhase64Lower_le G a (v a) (ε a) hca (hphase a)
  have hB := rationalScaledPhase64Lower_le G b (v b) (ε b) hcb (hphase b)
  have hAr := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.2.2.1
  have hBr := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.2.2.2
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_sub] at hAr hBr
  have hga :=
    phase64_actual_gap_ge_of_rounded_node (c := 51 * ((b : ℝ) - a) ^ 2) hx hG a
      (by
        rw [abs_of_nonneg ha0]; exact hab.le.trans hb5)
      (by linarith only [hAr, hA])
  have hgb :=
    phase64_actual_gap_ge_of_rounded_node (c := 51 * ((b : ℝ) - a) ^ 2) hx hG b
      (by
        rw [abs_of_nonneg (ha0.trans hab.le)]; exact hb5)
      (by linarith only [hBr, hB])
  have hg := phase64_gap_lower_on_interval_sharp (c := 51 * ((b : ℝ) - a) ^ 2) (t := t) hx hlog hab
  simp only [Complex.ofReal_ratCast] at hg
  have h := hg hga hgb ht
  nlinarith only [h]

/-- Input: positive bounded scale, phase enclosures and a successful adaptive phase tree.
Claim: the actual signed Gamma phase is bounded over its entire initial interval.
Proof: combine generic tree soundness and leaf interpolation soundness.
Role: certify complete low-frequency intervals from compact variable-width trees. -/
theorem scaledPhaseIntervalTree_sound {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8) {G : ℕ}
    (hG : 0 < G) (v ε : ℚ → ℚ)
    (hphase : ∀ s : ℚ, |(s : ℝ) * Real.log (256 * x) - (v s : ℝ)| ≤ (ε s : ℝ))
    (tree : RationalIntervalTree) (a b : ℚ)
    (hcheck : rationalIntervalTreeCheck (scaledPhaseIntervalCheck G v ε) a b tree = true) :
    ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
        finiteSignedResolvent phaseResolvent64Coefficients t := by
  exact
    rationalIntervalTreeCheck_sound
      (fun a b h t ht ↦ scaledPhaseIntervalCheck_sound hx hlog hG v ε hphase a b h t ht) tree a b
      hcheck

/-- Input: a nonempty finite chain of intervals, each satisfying a pointwise property.
Claim: the property holds from the first endpoint through the last endpoint.
Proof: induct over the chain and split at the penultimate endpoint.
Role: combine independently checked spectral blocks without repeating their computations. -/
theorem property_on_adjacent_chain {P : ℝ → Prop} (a : ℕ → ℝ) (n : ℕ)
    (hP : ∀ i < n + 1, ∀ t ∈ Set.Icc (a i) (a (i + 1)), P t) :
    ∀ t ∈ Set.Icc (a 0) (a (n + 1)), P t := by
  induction n with
  | zero => exact hP 0 (by norm_num only)
  | succ n ih =>
    intro t ht
    by_cases hm : t ≤ a (n + 1)
    · exact ih (fun i hi ↦ hP i (Nat.lt_trans hi (Nat.lt_succ_self (n + 1)))) t ⟨ht.1, hm⟩
    · exact hP (n + 1) (Nat.lt_succ_self (n + 1)) t ⟨(lt_of_not_ge hm).le, ht.2⟩

end PseudoPrime.Analysis
