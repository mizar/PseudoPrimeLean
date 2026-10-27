/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.UniformMixedBandBounds
public import PseudoPrime.NumberTheory.Heilbronn.WeightedCorrelationIncidence
public import PseudoPrime.Analysis.DyadicBandMomentSums

/-! # Fourth-root envelopes summed over Heilbronn dyadic bands -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The fourth root of a product factors over nonnegative real inputs.

Input: A nonnegative first factor and an arbitrary second real factor.
Claim: The nested square root of their product is the product of their
nested square roots.
Proof: Apply the square-root product identity at each nesting level.
Role: Factors the invariant Fourier envelope into its prime, energy, and
band-cardinality contributions. -/
theorem fourthRoot_mul_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt (x * y)) = Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt y) := by
  rw [Real.sqrt_mul hx, Real.sqrt_mul (Real.sqrt_nonneg x)]

/-- The fourth root of a square is the ordinary square root.

Input: A nonnegative real `x`.
Claim: `sqrt(sqrt(x^2)) = sqrt(x)`.
Proof: Evaluate the inner square root using nonnegativity.
Role: Simplifies the prime-square factor of the Fourier envelope. -/
theorem fourthRoot_sq_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt (x ^ 2)) = Real.sqrt x := by rw [Real.sqrt_sq hx]

/-- The fourth root of a cube is the cube of the fourth root.

Input: A nonnegative real `x`.
Claim: `sqrt(sqrt(x^3)) = sqrt(sqrt(x))^3`.
Proof: Evaluate `sqrt(x^3)` as `x * sqrt(x)` and factor the outer root.
Role: Extracts the three-quarter power of each band cardinality. -/
theorem fourthRoot_cube_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt (x ^ 3)) = (Real.sqrt (Real.sqrt x)) ^ 3 := by
  let q := Real.sqrt (Real.sqrt x)
  have hq2 : q ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
  have hinner : Real.sqrt (x ^ 3) = x * Real.sqrt x := by
    rw [show x ^ 3 = x * x ^ 2 by ring, Real.sqrt_mul hx, Real.sqrt_sq hx]
    ring
  rw [hinner, Real.sqrt_mul hx]
  change Real.sqrt x * q = q ^ 3
  calc
    Real.sqrt x * q = q ^ 2 * q := by rw [← hq2]
    _ = q ^ 3 := by ring

/-- The fourth-root Fourier envelopes of all dyadic Heilbronn bands have a
band-count-free sum.

Input: An odd prime `p`; bands consist of nonzero differences with correlation
in `[2^j, 2^(j+1))`.
Claim: The sum of `2^(2j)` times each invariant Fourier envelope is at most
`16384 * p * sqrt(E_p)`.
Proof: Apply the quadratic and cubic band-cardinality budgets, sum their
fourth-root envelopes at the balanced cutoff, then use `p/(p-1) ≤ 2`.
Role: Supplies the aggregate Fourier error bound needed to combine weighted
incidences without a logarithmic band-count factor. -/
theorem heilbronn_dyadic_band_envelope_sum_le {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (∑ j ∈ Finset.range (Nat.log2 p + 1),
        ((2 : ℝ) ^ j) ^ 2 *
          invariantFourierEnvelope p
            (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1)))) ≤
      16384 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) := by
  let A : ℕ → ℝ := fun j ↦
    ((heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))).card : ℝ)
  have hA : ∀ j, 0 ≤ A j := fun j ↦ Nat.cast_nonneg _
  have hEpos : (0 : ℝ) < heilbronnEnergy p := by
    have h := one_le_heilbronnEnergy (p := p)
    exact_mod_cast (Nat.zero_lt_one.trans_le h)
  have henergy : heilbronnEnergy p ≤ 262144 * p ^ 3 := by
    calc
      heilbronnEnergy p ≤ (p - 1) ^ 3 := heilbronnEnergy_le_cube
      _ ≤ p ^ 3 := Nat.pow_le_pow_left (Nat.sub_le p 1) 3
      _ ≤ 262144 * p ^ 3 := by
        simpa only [one_mul] using Nat.mul_le_mul_right (p ^ 3) (by decide : 1 ≤ 262144)
  have hEB : heilbronnEnergy p ≤ 262144 * p ^ 3 := henergy
  have hbudget :
    ∀ j,
      A j * ((2 : ℝ) ^ j) ^ 2 ≤ heilbronnEnergy p ∧
        A j * ((2 : ℝ) ^ j) ^ 3 ≤ (262144 : ℝ) * (p : ℝ) ^ 3 := by
    intro j
    let Pj : ℕ → Prop := fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1)
    have hK : ∀ v, Pj v → 2 ^ j ≤ v := fun _ hv ↦ hv.1
    have hKpos : 0 < 2 ^ j := Nat.pow_pos (by decide : 0 < 2)
    have hPzero : ¬Pj 0 := by
      intro hzero
      exact Nat.not_le_of_gt hKpos hzero.1
    have hb := correlation_level_tail_budgets hodd Pj hPzero hK
    constructor
    · change ((heilbronnCorrelationLevel p Pj).card : ℝ) * ((2 : ℝ) ^ j) ^ 2 ≤ heilbronnEnergy p
      exact_mod_cast hb.1
    · change
        ((heilbronnCorrelationLevel p Pj).card : ℝ) * ((2 : ℝ) ^ j) ^ 3 ≤ (262144 : ℝ) * (p : ℝ) ^ 3
      exact_mod_cast hb.2
  have hsum :=
    Analysis.dyadic_fourthRoot_sum_le_of_balanced_band_budgets (n := Nat.log2 p) hEpos
      (by exact_mod_cast hEB) A hA (fun j ↦ (hbudget j).1) (fun j ↦ (hbudget j).2)
  have hpReal : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hrootB : Real.sqrt ((262144 : ℝ) * (p : ℝ) ^ 3) = 512 * (p : ℝ) * Real.sqrt p := by
    rw [Real.sqrt_mul (by norm_num only : (0 : ℝ) ≤ 262144)]
    rw [show (262144 : ℝ) = 512 ^ 2 by norm_num only,
      Real.sqrt_sq (by norm_num only : (0 : ℝ) ≤ 512)]
    rw [show (p : ℝ) ^ 3 = (p : ℝ) ^ 2 * p by ring, Real.sqrt_mul (sq_nonneg (p : ℝ)),
      Real.sqrt_sq hpReal]
    ring
  have hpminus : (0 : ℝ) < (p - 1 : ℕ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out))
  have hpt : (p : ℝ) ≤ 2 * (p - 1 : ℕ) := by
    rw [Nat.cast_sub (Nat.one_le_of_lt (Nat.Prime.one_lt Fact.out)), Nat.cast_one]
    have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.Prime.two_le Fact.out)
    linarith only [hp2]
  have hqE : (Real.sqrt (Real.sqrt (heilbronnEnergy p))) ^ 2 = Real.sqrt (heilbronnEnergy p) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  let qE := Real.sqrt (Real.sqrt (heilbronnEnergy p))
  have hqE' : qE ^ 2 = Real.sqrt (heilbronnEnergy p) := hqE
  have hscaled :
    8192 * (p : ℝ) ^ 2 * Real.sqrt (heilbronnEnergy p) ≤
      16384 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) * (p - 1 : ℕ) := by
    have hfactor :=
      mul_le_mul_of_nonneg_left hpt
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8192)
          (mul_nonneg hpReal (Real.sqrt_nonneg (heilbronnEnergy p))))
    nlinarith only [hfactor]
  have hsum' :
    (∑ j ∈ Finset.range (Nat.log2 p + 1),
        ((2 : ℝ) ^ j) ^ 2 *
          invariantFourierEnvelope p
            (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1)))) ≤
      8192 * (p : ℝ) ^ 2 * Real.sqrt (heilbronnEnergy p) / (p - 1 : ℕ) := by
    let c := Real.sqrt p * qE / (p - 1 : ℕ)
    have hc : 0 ≤ c :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg p) (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
    have hsumEnvelope :
      (∑ j ∈ Finset.range (Nat.log2 p + 1),
          ((2 : ℝ) ^ j) ^ 2 *
            invariantFourierEnvelope p
              (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1)))) =
        c *
          ∑ j ∈ Finset.range (Nat.log2 p + 1),
            ((2 : ℝ) ^ j) ^ 2 * (Real.sqrt (Real.sqrt (A j))) ^ 3 := by
      calc
        _ =
            ∑ j ∈ Finset.range (Nat.log2 p + 1),
              c * (((2 : ℝ) ^ j) ^ 2 * (Real.sqrt (Real.sqrt (A j))) ^ 3) :=
          by
          apply Finset.sum_congr rfl
          intro j hj
          rw [invariantFourierEnvelope]
          have hfourth :
            Real.sqrt (Real.sqrt ((p : ℝ) ^ 2 * heilbronnEnergy p * (A j) ^ 3)) =
              Real.sqrt p * qE * (Real.sqrt (Real.sqrt (A j))) ^ 3 := by
            calc
              _ = Real.sqrt (Real.sqrt (((p : ℝ) ^ 2 * heilbronnEnergy p) * (A j) ^ 3)) := by
                congr 1
              _ =
                  Real.sqrt (Real.sqrt ((p : ℝ) ^ 2 * heilbronnEnergy p)) *
                    Real.sqrt (Real.sqrt ((A j) ^ 3)) :=
                fourthRoot_mul_of_nonneg (mul_nonneg (sq_nonneg (p : ℝ)) hEpos.le)
              _ =
                  (Real.sqrt (Real.sqrt ((p : ℝ) ^ 2)) *
                      Real.sqrt (Real.sqrt (heilbronnEnergy p))) *
                    Real.sqrt (Real.sqrt ((A j) ^ 3)) :=
                by rw [fourthRoot_mul_of_nonneg (sq_nonneg (p : ℝ))]
              _ = Real.sqrt p * qE * (Real.sqrt (Real.sqrt (A j))) ^ 3 := by
                rw [fourthRoot_sq_of_nonneg hpReal, fourthRoot_cube_of_nonneg (hA j)]
          rw [hfourth]
          change
            ((2 : ℝ) ^ j) ^ 2 *
                (Real.sqrt p * qE * (Real.sqrt (Real.sqrt (A j))) ^ 3 / (p - 1 : ℕ)) =
              c * (((2 : ℝ) ^ j) ^ 2 * (Real.sqrt (Real.sqrt (A j))) ^ 3)
          dsimp only [c]
          ring
        _ =
            c *
              ∑ j ∈ Finset.range (Nat.log2 p + 1),
                ((2 : ℝ) ^ j) ^ 2 * (Real.sqrt (Real.sqrt (A j))) ^ 3 :=
          by rw [Finset.mul_sum]
    have hmain := mul_le_mul_of_nonneg_left hsum hc
    calc
      _ =
          c *
            ∑ j ∈ Finset.range (Nat.log2 p + 1),
              ((2 : ℝ) ^ j) ^ 2 * (Real.sqrt (Real.sqrt (A j))) ^ 3 :=
        hsumEnvelope
      _ ≤ c * (16 * qE * Real.sqrt ((262144 : ℝ) * (p : ℝ) ^ 3)) := by exact hmain
      _ = 8192 * (p : ℝ) ^ 2 * Real.sqrt (heilbronnEnergy p) / (p - 1 : ℕ) := by
        have hnum :
          (Real.sqrt p * Real.sqrt (Real.sqrt (heilbronnEnergy p))) *
              (16 * Real.sqrt (Real.sqrt (heilbronnEnergy p)) * (512 * (p : ℝ) * Real.sqrt p)) =
            8192 * (p : ℝ) ^ 2 * Real.sqrt (heilbronnEnergy p) := by
          calc
            _ =
                8192 * (p : ℝ) * (Real.sqrt p) ^ 2 *
                  (Real.sqrt (Real.sqrt (heilbronnEnergy p))) ^ 2 :=
              by ring
            _ = _ := by
              rw [Real.sq_sqrt hpReal, hqE]; ring
        calc
          _ = ((Real.sqrt p * qE) * (16 * qE * (512 * (p : ℝ) * Real.sqrt p))) / (p - 1 : ℕ) := by
            rw [hrootB]
            dsimp only [c]
            ring
          _ = _ := by rw [hnum]
  apply hsum'.trans
  apply (div_le_iff₀ hpminus).2
  exact hscaled

/-- The total quadratic mass of the half-open dyadic correlation bands is
bounded by the Heilbronn energy.

Input: A finite type, a natural-valued correlation function, a predicate
selecting residues, and a finite range of dyadic scales.
Claim: The sum of the squared lower endpoints over the selected bands is at
most the full sum of squared correlations.
Proof: Count by residues, use uniqueness of the half-open dyadic band, and
bound its lower endpoint by the correlation itself.
Role: Supplies the exact total band-mass budget for the weighted incidence
estimate below.
-/
theorem dyadic_band_card_mass_le_square_sum {α : Type*} [Fintype α] (r : α → ℕ) (P : α → Prop)
    [DecidablePred P] (m : ℕ) :
    (∑ j ∈ Finset.range m,
        ((2 : ℕ) ^ j) ^ 2 *
          (Finset.univ.filter (fun x : α ↦ P x ∧ 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1))).card) ≤
      ∑ x : α, r x ^ 2 := by
  classical
  let B : ℕ → Finset α := fun j ↦ Finset.univ.filter (fun x ↦ P x ∧ 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1))
  let g : α → ℕ → ℕ := fun x j ↦ if x ∈ B j then (2 ^ j) ^ 2 else 0
  have hterm (j : ℕ) : ((2 : ℕ) ^ j) ^ 2 * (B j).card = ∑ x ∈ B j, ((2 : ℕ) ^ j) ^ 2 := by
    rw [Finset.sum_const_nat (fun _ _ ↦ rfl), Nat.mul_comm]
  have hband (x : α) (j : ℕ) (hx : x ∈ B j) : Nat.log2 (r x) = j := by
    have hh := Finset.mem_filter.mp hx
    have hr0 : r x ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.pow_pos (by decide : 0 < 2)) hh.2.2.1)
    exact (Nat.log2_eq_iff hr0).2 hh.2.2
  have hpoint (x : α) : (∑ j ∈ Finset.range m, g x j) ≤ r x ^ 2 := by
    by_cases hPx : P x
    · by_cases hr0 : r x = 0
      · have hzero : ∀ j ∈ Finset.range m, g x j = 0 := by
          intro j hj
          have hx : x ∉ B j := by
            intro hx
            have hh := Finset.mem_filter.mp hx
            rw [hr0] at hh
            exact Nat.not_le_of_gt (Nat.pow_pos (by decide : 0 < 2)) hh.2.2.1
          simp only [g, ite_eq_right hx]
        rw [Finset.sum_eq_zero hzero, hr0]
        exact Nat.zero_le _
      · let k := Nat.log2 (r x)
        have hb : 2 ^ k ≤ r x ∧ r x < 2 ^ (k + 1) := (Nat.log2_eq_iff hr0).mp rfl
        have hkband : x ∈ B k := by
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hPx, hb⟩
        have hunique (j : ℕ) (hx : x ∈ B j) : j = k := (hband x j hx).symm
        by_cases hk : k ∈ Finset.range m
        · have hzero : ∀ j ∈ Finset.range m, j ≠ k → g x j = 0 := by
            intro j hj hne
            have hx : x ∉ B j := by
              intro hx
              exact hne (hunique j hx)
            simp only [g, ite_eq_right hx]
          have hsum := Finset.sum_eq_single k hzero (fun hn ↦ (hn hk).elim)
          calc
            _ = g x k := hsum
            _ = (2 ^ k) ^ 2 := by
              change (if x ∈ B k then (2 ^ k) ^ 2 else 0) = _
              rw [ite_eq_left hkband]
            _ ≤ r x ^ 2 := Nat.pow_le_pow_left (Nat.log2_self_le hr0) 2
        · have hzero : ∀ j ∈ Finset.range m, g x j = 0 := by
            intro j hj
            have hx : x ∉ B j := by
              intro hx
              have heq : j = k := hunique j hx
              exact hk (heq ▸ hj)
            simp only [g, ite_eq_right hx]
          rw [Finset.sum_eq_zero hzero]
          exact Nat.zero_le _
    · have hzero : ∀ j ∈ Finset.range m, g x j = 0 := by
        intro j hj
        have hx : x ∉ B j := by
          intro hx
          exact hPx (Finset.mem_filter.mp hx).2.1
        simp only [g, ite_eq_right hx]
      rw [Finset.sum_eq_zero hzero]
      exact Nat.zero_le _
  calc
    _ = ∑ j ∈ Finset.range m, ∑ x ∈ B j, ((2 : ℕ) ^ j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j
    _ =
        ∑ j ∈ Finset.range m,
          ∑ x : α, if P x ∧ 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1) then (2 ^ j) ^ 2 else 0 :=
      by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [B]
      rw [Finset.sum_filter]
    _ =
        ∑ x : α,
          ∑ j ∈ Finset.range m, if P x ∧ 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1) then (2 ^ j) ^ 2 else 0 :=
      by rw [Finset.sum_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [g, B, Finset.mem_filter, Finset.mem_univ, true_and] using hpoint x

/-- A weighted square sum is covered by half-open dyadic levels.

Input: A finite set, a natural-valued weight and level function, and a bound
for the level values on the set.
Claim: The weighted square sum is at most the sum of `4 * 2^(2j)` times the
weight mass in `[2^j, 2^(j+1))`.
Proof: Choose `j = log₂(r x)` for each positive level, compare the square
with the band endpoint, then interchange the finite sums.
Role: Converts weighted correlation energy into the all-band incidence sum.
-/
theorem weighted_sum_sq_le_dyadic_half_open_bands {ι : Type*} (S : Finset ι) (w r : ι → ℕ) (P : ℕ)
    (hr : ∀ x ∈ S, r x ≤ P) :
    (∑ x ∈ S, w x * r x ^ 2) ≤
      ∑ j ∈ Finset.range (Nat.log2 P + 1),
        4 * (2 ^ j) ^ 2 * ∑ x ∈ S.filter (fun x ↦ 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1)), w x := by
  have hpoint (x : ι) (hx : x ∈ S) :
    w x * r x ^ 2 ≤
      ∑ j ∈ Finset.range (Nat.log2 P + 1),
        if 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1) then 4 * (2 ^ j) ^ 2 * w x else 0 := by
    by_cases hr0 : r x = 0
    · rw [hr0, zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact Nat.zero_le _
    · let j := Nat.log2 (r x)
      have hlow : 2 ^ j ≤ r x := Nat.log2_self_le hr0
      have hhigh : r x < 2 ^ (j + 1) := Nat.lt_log2_self
      have hband : 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1) := ⟨hlow, hhigh⟩
      have hlog : Nat.log2 (r x) ≤ Nat.log2 P := by
        rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
        exact Nat.log_mono_right (b := 2) (hr x hx)
      have hj : j ∈ Finset.range (Nat.log2 P + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hlog)
      have hupper : r x ≤ 2 * 2 ^ j := by
        have hh := hhigh.le
        rw [Nat.pow_succ] at hh
        simpa only [Nat.mul_comm] using hh
      have hsq : r x ^ 2 ≤ (2 * 2 ^ j) ^ 2 := Nat.pow_le_pow_left hupper 2
      let F : ℕ → ℕ := fun k ↦ if 2 ^ k ≤ r x ∧ r x < 2 ^ (k + 1) then 4 * (2 ^ k) ^ 2 * w x else 0
      have hsum :=
        Finset.single_le_sum (s := Finset.range (Nat.log2 P + 1)) (f := F)
          (fun k hk ↦ Nat.zero_le (F k)) hj
      calc
        _ ≤ F j := by
          change
            w x * r x ^ 2 ≤ if 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1) then 4 * (2 ^ j) ^ 2 * w x else 0
          rw [ite_eq_left hband]
          calc
            _ ≤ w x * (2 * 2 ^ j) ^ 2 := Nat.mul_le_mul_left (w x) hsq
            _ = 4 * (2 ^ j) ^ 2 * w x := by ring
        _ ≤ ∑ k ∈ Finset.range (Nat.log2 P + 1), F k := hsum
  have hmass := Finset.sum_le_sum (fun x hx ↦ hpoint x hx)
  calc
    _ ≤
        ∑ x ∈ S,
          ∑ j ∈ Finset.range (Nat.log2 P + 1),
            if 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1) then 4 * (2 ^ j) ^ 2 * w x else 0 :=
      hmass
    _ =
        ∑ j ∈ Finset.range (Nat.log2 P + 1),
          ∑ x ∈ S, if 2 ^ j ≤ r x ∧ r x < 2 ^ (j + 1) then 4 * (2 ^ j) ^ 2 * w x else 0 :=
      by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter, ← Finset.mul_sum]

/-- The quadratic masses of the actual half-open Heilbronn correlation bands
sum to at most the full additive energy.

Input: An odd prime `p` and the correlation level for each dyadic interval.
Claim: The sum of `2^(2j) * card(Ω_j)` over `j ≤ log₂ p` is at most `E_p`.
Proof: Apply the generic disjoint-band mass estimate to the nonzero difference
correlations and unfold the energy definition.
Role: Removes the conditional band-mass input from the weighted incidence
estimate.
-/
theorem heilbronn_dyadic_band_card_mass_le_energy {p : ℕ} [Fact p.Prime] :
    (∑ j ∈ Finset.range (Nat.log2 p + 1),
        ((2 : ℕ) ^ j) ^ 2 *
          (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))).card) ≤
      heilbronnEnergy p := by
  classical
  have h :=
    dyadic_band_card_mass_le_square_sum
      (fun x : ZMod (p ^ 2) ↦ Nat.card (cosetDifferenceAt p 0 0 x)) (fun x : ZMod (p ^ 2) ↦ x ≠ 0)
      (Nat.log2 p + 1)
  simpa only [heilbronnCorrelationLevel, heilbronnEnergy] using h

/-- The weighted incidence sum over all dyadic correlation bands has no
logarithmic band-count loss.

Input: An odd prime `p`, a natural-number residue weight `f`, and the
quadratic band-mass budget `sum_j 2^(2j) card(Ω_j) ≤ E_p`.
Claim: The sum of `4 * 2^(2j)` times the weighted incidences is at most
`4 * E_p * mass(f)^2 / p^2 + 2^16 * p * sqrt(E_p) * sum(f^2)`.
Proof: Apply the weighted Fourier incidence bound on each band, sum the main
terms using the mass budget, and sum the Fourier envelopes by the preceding
band-free estimate.
Role: Establishes the weighted analogue of the mixed third-energy estimate
needed by the analysis7 amplification argument. -/
theorem weighted_dyadic_band_incidence_sum_le_of_card_mass {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (f : ZMod (p ^ 2) → ℕ)
    (hcard :
      (∑ j ∈ Finset.range (Nat.log2 p + 1),
          ((2 : ℝ) ^ j) ^ 2 *
            (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))).card) ≤
        heilbronnEnergy p) :
    (∑ j ∈ Finset.range (Nat.log2 p + 1),
        4 * ((2 : ℝ) ^ j) ^ 2 *
          weightedResidueDifferenceIncidence f
            (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1)))) ≤
      4 * heilbronnEnergy p * (weightedResidueMass f : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        65536 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) * ∑ x : ZMod (p ^ 2), (f x : ℝ) ^ 2 := by
  let bands : ℕ → Finset (ZMod (p ^ 2)) := fun j ↦
    heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))
  let mass := (weightedResidueMass f : ℝ)
  let squareMass := ∑ x : ZMod (p ^ 2), (f x : ℝ) ^ 2
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  have hsquareMass : 0 ≤ squareMass := Finset.sum_nonneg (fun x _ ↦ sq_nonneg (f x : ℝ))
  have henv := heilbronn_dyadic_band_envelope_sum_le hodd
  have hmain :
    (∑ j ∈ Finset.range (Nat.log2 p + 1),
        4 * ((2 : ℝ) ^ j) ^ 2 * (bands j).card * mass ^ 2 / (p : ℝ) ^ 2) ≤
      4 * heilbronnEnergy p * mass ^ 2 / (p : ℝ) ^ 2 := by
    have hsum :
      (∑ j ∈ Finset.range (Nat.log2 p + 1), ((2 : ℝ) ^ j) ^ 2 * (bands j).card) ≤
        heilbronnEnergy p := by
      simpa only [bands] using hcard
    calc
      _ =
          (4 * mass ^ 2 / (p : ℝ) ^ 2) *
            ∑ j ∈ Finset.range (Nat.log2 p + 1), ((2 : ℝ) ^ j) ^ 2 * (bands j).card :=
        by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [bands]
        ring
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left hsum
          (div_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (sq_nonneg mass))
            (sq_nonneg (p : ℝ)))
      _ = _ := by ring
  have herr :
    (∑ j ∈ Finset.range (Nat.log2 p + 1),
        (4 * squareMass) * (((2 : ℝ) ^ j) ^ 2 * invariantFourierEnvelope p (bands j))) ≤
      65536 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) * squareMass := by
    calc
      _ =
          ∑ j ∈ Finset.range (Nat.log2 p + 1),
            (4 * squareMass) * (((2 : ℝ) ^ j) ^ 2 * invariantFourierEnvelope p (bands j)) :=
        by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ =
          (4 * squareMass) *
            ∑ j ∈ Finset.range (Nat.log2 p + 1),
              ((2 : ℝ) ^ j) ^ 2 * invariantFourierEnvelope p (bands j) :=
        by
        exact
          (Finset.mul_sum (Finset.range (Nat.log2 p + 1))
              (fun j ↦ ((2 : ℝ) ^ j) ^ 2 * invariantFourierEnvelope p (bands j))
              (4 * squareMass)).symm
      _ ≤ _ := by
        have hmul :=
          mul_le_mul_of_nonneg_left henv (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hsquareMass)
        calc
          _ ≤ (4 * squareMass) * (16384 * (p : ℝ) * Real.sqrt (heilbronnEnergy p)) := hmul
          _ = _ := by ring
  calc
    _ ≤
        ∑ j ∈ Finset.range (Nat.log2 p + 1),
          4 * ((2 : ℝ) ^ j) ^ 2 *
            ((bands j).card * mass ^ 2 / (p : ℝ) ^ 2 +
              invariantFourierEnvelope p (bands j) * squareMass) :=
      by
      apply Finset.sum_le_sum
      intro j hj
      have hPzero : ¬(fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1)) 0 := by
        intro hz
        exact Nat.not_le_of_gt (Nat.pow_pos (by decide : 0 < 2)) hz.1
      have hinc :=
        weightedResidueDifferenceIncidence_le_correlation_level f
          (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1)) hPzero
      have hfactor : 0 ≤ 4 * ((2 : ℝ) ^ j) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hinc hfactor
    _ =
        (∑ j ∈ Finset.range (Nat.log2 p + 1),
            4 * ((2 : ℝ) ^ j) ^ 2 * (bands j).card * mass ^ 2 / (p : ℝ) ^ 2) +
          (∑ j ∈ Finset.range (Nat.log2 p + 1),
            (4 * squareMass) * (((2 : ℝ) ^ j) ^ 2 * invariantFourierEnvelope p (bands j))) :=
      by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := add_le_add hmain herr

/-- Sum the weighted incidence estimate over the actual Heilbronn dyadic
bands without a separate band-mass hypothesis.

Input: An odd prime `p` and a natural-number residue weight `f`.
Claim: The all-band weighted incidence sum is bounded by its energy main term
and the band-free Fourier error.
Proof: Supply the quadratic band-mass bound from the exact energy partition
and apply the conditional weighted incidence estimate.
Role: Exposes the unconditional all-band estimate used by amplification.
-/
theorem weighted_dyadic_band_incidence_sum_le {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (f : ZMod (p ^ 2) → ℕ) :
    (∑ j ∈ Finset.range (Nat.log2 p + 1),
        4 * ((2 : ℝ) ^ j) ^ 2 *
          weightedResidueDifferenceIncidence f
            (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1)))) ≤
      4 * heilbronnEnergy p * (weightedResidueMass f : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        65536 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) * ∑ x : ZMod (p ^ 2), (f x : ℝ) ^ 2 := by
  have hcardNat := heilbronn_dyadic_band_card_mass_le_energy (p := p)
  have hcard :
    (∑ j ∈ Finset.range (Nat.log2 p + 1),
        ((2 : ℝ) ^ j) ^ 2 *
          (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))).card) ≤
      heilbronnEnergy p := by
    exact_mod_cast hcardNat
  exact weighted_dyadic_band_incidence_sum_le_of_card_mass hodd f hcard

/-- Expand a weighted difference incidence as a real sum over its rows.

Input: A natural-number residue weight `f` and a finite difference set `Q`.
Claim: The incidence is the sum of `f x * f y` over pairs with `x-y ∈ Q`.
Proof: Rewrite the incidence as a cast natural pair sum and distribute the
cast over its finite sums and products.
Role: Identifies the band-filtered row sums in the dyadic correlation cover.
-/
theorem weightedResidueDifferenceIncidence_eq_filtered_real_sum {N : ℕ} [NeZero N] (f : ZMod N → ℕ)
    (Q : Finset (ZMod N)) :
    weightedResidueDifferenceIncidence f Q =
      ∑ x : ZMod N, ∑ y ∈ Finset.univ.filter (fun y ↦ x - y ∈ Q), (f x : ℝ) * f y := by
  rw [weightedResidueDifferenceIncidence_eq_filtered_sum]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- The weighted sum of squared nonzero difference correlations is bounded by
the sum of the half-open dyadic weighted incidences.

Input: An odd prime `p` and a natural-number weight `f` on `ZMod (p^2)`.
Claim: The pair sum of `f x * f y * r(x-y)^2` over nonzero differences is
at most the sum of `4 * 2^(2j)` times the incidence of the `j`th correlation
band.
Proof: Apply the generic dyadic square-sum cover to each fixed first residue,
then identify each band-filtered row with its weighted difference incidence.
Role: Connects the weighted Fourier estimates to the off-diagonal term in
Heilbronn amplification. -/
theorem weighted_pair_correlation_square_le_bands {p : ℕ} [Fact p.Prime] (f : ZMod (p ^ 2) → ℕ) :
    (∑ x : ZMod (p ^ 2),
        ∑ y ∈ Finset.univ.filter (fun y ↦ x - y ≠ 0),
          f x * f y * Nat.card (cosetDifferenceAt p 0 0 (x - y)) ^ 2) ≤
      ∑ j ∈ Finset.range (Nat.log2 p + 1),
        (4 : ℝ) * ((2 : ℝ) ^ j) ^ 2 *
          weightedResidueDifferenceIncidence f
            (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))) := by
  classical
  let Sx : ZMod (p ^ 2) → Finset (ZMod (p ^ 2)) := fun x ↦ Finset.univ.filter (fun y ↦ x - y ≠ 0)
  let r : ZMod (p ^ 2) → ZMod (p ^ 2) → ℕ := fun x y ↦ Nat.card (cosetDifferenceAt p 0 0 (x - y))
  have hrow (x : ZMod (p ^ 2)) :
    (∑ y ∈ Sx x, f x * f y * (r x y) ^ 2) ≤
      ∑ j ∈ Finset.range (Nat.log2 p + 1),
        4 * (2 ^ j) ^ 2 *
          ∑ y ∈ (Sx x).filter (fun y ↦ 2 ^ j ≤ r x y ∧ r x y < 2 ^ (j + 1)), f x * f y := by
    exact
      weighted_sum_sq_le_dyadic_half_open_bands (Sx x) (fun y ↦ f x * f y) (r x) p
        (fun y hy ↦ (card_cosetDifferenceAt_le 0 0 (x - y)).trans (Nat.sub_le p 1))
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod (p ^ 2)))) (fun x _ ↦ hrow x)
  have hfilter (x : ZMod (p ^ 2)) (j : ℕ) :
    (Sx x).filter (fun y ↦ 2 ^ j ≤ r x y ∧ r x y < 2 ^ (j + 1)) =
      Finset.univ.filter
        (fun y ↦ x - y ∈ heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))) := by
    ext y
    simp only [Sx, r, Finset.mem_filter, Finset.mem_univ, true_and, mem_heilbronnCorrelationLevel]
  have hinc (j : ℕ) :
    (∑ x : ZMod (p ^ 2),
        ∑ y ∈ (Sx x).filter (fun y ↦ 2 ^ j ≤ r x y ∧ r x y < 2 ^ (j + 1)), (f x : ℝ) * f y) =
      weightedResidueDifferenceIncidence f
        (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))) := by
    calc
      _ =
          ∑ x : ZMod (p ^ 2),
            ∑
              y ∈
                Finset.univ.filter
                  (fun y ↦
                    x - y ∈ heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))),
              (f x : ℝ) * f y :=
        by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hfilter]
      _ = _ := (weightedResidueDifferenceIncidence_eq_filtered_real_sum f _).symm
  have hcast :
    (↑(∑ x : ZMod (p ^ 2), ∑ y ∈ Sx x, f x * f y * (r x y) ^ 2) : ℝ) ≤
      ∑ x : ZMod (p ^ 2),
        ∑ j ∈ Finset.range (Nat.log2 p + 1),
          ↑(4 * (2 ^ j) ^ 2 *
                ∑ y ∈ (Sx x).filter (fun y ↦ 2 ^ j ≤ r x y ∧ r x y < 2 ^ (j + 1)), f x * f y :
              ℕ) := by
    exact_mod_cast hsum
  calc
    _ = ↑(∑ x : ZMod (p ^ 2), ∑ y ∈ Sx x, f x * f y * (r x y) ^ 2) := by simp only [Sx, r]
    _ ≤ _ := hcast
    _ =
        ∑ j ∈ Finset.range (Nat.log2 p + 1),
          (4 : ℝ) * ((2 : ℝ) ^ j) ^ 2 *
            weightedResidueDifferenceIncidence f
              (heilbronnCorrelationLevel p (fun v ↦ 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))) :=
      by
      simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
      congr 1
      exact hinc j

/-- The weighted off-diagonal correlation square sum satisfies the full
all-band estimate with a band-count-free Fourier error.

Input: An odd prime `p` and a natural-number weight `f` on `ZMod (p^2)`.
Claim: The pair sum over nonzero differences is at most
`4 E_p mass(f)^2 / p^2 + 2^16 p sqrt(E_p) sum_x f(x)^2`.
Proof: Combine the pair-to-band estimate with the unconditional all-band
weighted incidence bound.
Role: Supplies the weighted analogue of the target incidence estimate (4) in
the analysis7 plan. -/
theorem weighted_pair_correlation_square_le {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (f : ZMod (p ^ 2) → ℕ) :
    (∑ x : ZMod (p ^ 2),
        ∑ y ∈ Finset.univ.filter (fun y ↦ x - y ≠ 0),
          f x * f y * Nat.card (cosetDifferenceAt p 0 0 (x - y)) ^ 2) ≤
      4 * heilbronnEnergy p * (weightedResidueMass f : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        65536 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) * ∑ x : ZMod (p ^ 2), (f x : ℝ) ^ 2 := by
  exact
    (weighted_pair_correlation_square_le_bands f).trans
      (weighted_dyadic_band_incidence_sum_le hodd f)

end PseudoPrime.NumberTheory.Heilbronn
