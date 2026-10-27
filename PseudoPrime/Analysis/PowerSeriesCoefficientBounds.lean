/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-! # Coefficient bounds for finite products of power series -/

@[expose] public section

namespace PseudoPrime.Analysis

/--
Inputs: two complex power series and real coefficientwise bounds for their coefficient norms.

Claim: the product of the real series bounds coefficient norms of the complex product.

Proof: use the finite convolution formula, the triangle inequality, and termwise multiplication.

Role: propagates coefficient bounds through finite products without an analytic convergence
assumption.
-/
theorem powerSeries_coeff_mul_norm_le (f g : PowerSeries ℂ) (F G : PowerSeries ℝ)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ PowerSeries.coeff n F)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ PowerSeries.coeff n G) (n : ℕ) :
    ‖PowerSeries.coeff n (f * g)‖ ≤ PowerSeries.coeff n (F * G) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  exact mul_le_mul (hf p.1) (hg p.2) (norm_nonneg _) (le_trans (norm_nonneg _) (hf p.1))

/--
Inputs: a finite family of complex power series with all coefficient norms at most one.

Claim: coefficients of the corresponding power of the geometric series bound coefficient norms
of the product, including an empty family.

Proof: induct on the index set and apply the coefficientwise product bound.

Role: counts the possible terms of complete homogeneous symmetric expressions.
-/
theorem powerSeries_coeff_prod_norm_le_geometric {ι : Type} (s : Finset ι) (f : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, ∀ n, ‖PowerSeries.coeff n (f i)‖ ≤ 1) (n : ℕ) :
    ‖PowerSeries.coeff n (∏ i ∈ s, f i)‖ ≤
      PowerSeries.coeff n ((PowerSeries.mk 1 : PowerSeries ℝ) ^ s.card) := by
  classical
    induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp only [norm_one, norm_zero, le_refl]
  | @insert i s hi
    ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    apply powerSeries_coeff_mul_norm_le
    · intro j
      simpa only [PowerSeries.coeff_mk, Pi.one_apply] using hf i (Finset.mem_insert_self i s) j
    · intro j
      exact ih (fun k hk ↦ hf k (Finset.mem_insert_of_mem hk)) j

/--
Inputs: `k + 1` complex power series whose coefficient norms are at most one.

Claim: the norm of the product coefficient at `n` is at most `choose (k + n) k`.

Proof: evaluate the geometric-power bound by the formal binomial-series identity.

Role: provides the binomial bound for Newton interpolation coefficients at repeated nodes.
-/
theorem powerSeries_coeff_prod_norm_le_choose {ι : Type} (s : Finset ι) (f : ι → PowerSeries ℂ)
    {k : ℕ} (hs : s.card = k + 1) (hf : ∀ i ∈ s, ∀ n, ‖PowerSeries.coeff n (f i)‖ ≤ 1) (n : ℕ) :
    ‖PowerSeries.coeff n (∏ i ∈ s, f i)‖ ≤ (Nat.choose (k + n) k : ℝ) := by
  have h := powerSeries_coeff_prod_norm_le_geometric s f hf n
  rw [hs, PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk] at h
  exact h

end PseudoPrime.Analysis
