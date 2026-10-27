/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteRampRows

/-! # Moving ramp lower bounds with reserved prime-power support -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The first n nonnegative exponential Taylor terms at rational height t.
For t at least zero the sum is a lower bound for exp(t). The rational value
is used to evaluate reserved prime-power rows at later rational scales. -/
def gammaPositiveTaylor (t : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, t ^ i / (i.factorial : ℚ)

/-- Input: a nonnegative rational height and any term count.
Claim: the rational Taylor polynomial is nonnegative.
Proof: each summand is nonnegative. This supplies the sign needed
when multiplying a certified lower exponential endpoint. -/
theorem gamma_positive_taylor_nonneg {t : ℚ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ gammaPositiveTaylor t n := by
  exact Finset.sum_nonneg (fun i _ ↦ div_nonneg (pow_nonneg ht i) (Nat.cast_nonneg i.factorial))

/-- Input: a nonnegative rational height and any term count.
Claim: the cast Taylor polynomial is at most the actual exponential.
Proof: cast the sum and use Real.sum_le_exp_of_nonneg.
This transfers the exact polynomial used in reserved rows to the real bound. -/
theorem gamma_positive_taylor_le_exp {t : ℚ} (ht : 0 ≤ t) (n : ℕ) :
    (gammaPositiveTaylor t n : ℝ) ≤ Real.exp (t : ℝ) := by
  simpa only [gammaPositiveTaylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using
    Real.sum_le_exp_of_nonneg ((Rat.cast_nonneg (K := ℝ)).mpr ht) n

/-- Input: a nonnegative endpoint below exp(-v/2).
Claim: its square is below exp(-v). Proof: multiply the endpoint bounds
and combine exponents. This supplies a reusable full-scale endpoint. -/
theorem gamma_exp_endpoint_square_le {v e : ℝ} (he : 0 ≤ e) (hev : e ≤ Real.exp (-v / 2)) :
    e ^ 2 ≤ Real.exp (-v) := by
  calc
    e ^ 2 ≤ Real.exp (-v / 2) * Real.exp (-v / 2) := by
      simpa only [pow_two] using mul_le_mul hev hev he (Real.exp_pos (-v / 2)).le
    _ = Real.exp (-v) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Input: u at most v and any lower endpoint e for exp(-v).
Claim: Taylor transport from v to u preserves the lower bound.
Proof: multiply the endpoint and Taylor bounds and combine exponents.
This separates transport from the choice of an endpoint certificate. -/
theorem gamma_exp_taylor_lower {u v e : ℝ} (huv : u ≤ v) (hev : e ≤ Real.exp (-v)) (n : ℕ) :
    e * (∑ i ∈ Finset.range n, (v - u) ^ i / (i.factorial : ℝ)) ≤ Real.exp (-u) := by
  have hp : 0 ≤ ∑ i ∈ Finset.range n, (v - u) ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg
      (fun i _ ↦ div_nonneg (pow_nonneg (sub_nonneg.mpr huv) i) (Nat.cast_nonneg i.factorial))
  calc
    _ ≤ Real.exp (-v) * Real.exp (v - u) :=
      mul_le_mul hev (Real.sum_le_exp_of_nonneg (sub_nonneg.mpr huv) n) hp (Real.exp_pos (-v)).le
    _ = Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Input: u at most v and a nonnegative endpoint e at most exp(-v/2).
Claim: e squared times the exponential Taylor sum at v-u bounds exp(-u).
Proof: square the endpoint, multiply the two exponential bounds,
and combine exponents. This lets one fixed half-scale row move to later scales. -/
theorem gamma_exp_square_taylor_lower {u v e : ℝ} (huv : u ≤ v) (he : 0 ≤ e)
    (hev : e ≤ Real.exp (-v / 2)) (n : ℕ) :
    e ^ 2 * (∑ i ∈ Finset.range n, (v - u) ^ i / (i.factorial : ℝ)) ≤ Real.exp (-u) := by
  exact gamma_exp_taylor_lower huv (gamma_exp_endpoint_square_le he hev) n

/-- The exact rational transported ramp allowance at target height u.
The endpoint e is taken at half the reference height v. The Taylor term count
is arbitrary and the exact ramp factor keeps both support joins at u. -/
def gammaRationalTransportLower (u v e : ℚ) (n : ℕ) : ℚ :=
  e ^ 2 * gammaPositiveTaylor (v - u) n * gammaRationalRampFactor u

/-- Input: ordered rational heights and any rational endpoint.
Claim: the transported ramp allowance is nonnegative.
Proof: all three factors are nonnegative. This supplies signs for
multiplication by a logarithm lower endpoint. -/
theorem gamma_rational_transport_nonneg {u v e : ℚ} (huv : u ≤ v) (n : ℕ) :
    0 ≤ gammaRationalTransportLower u v e n := by
  exact
    mul_nonneg (mul_nonneg (sq_nonneg e) (gamma_positive_taylor_nonneg (sub_nonneg.mpr huv) n))
      (gamma_rational_ramp_factor_nonneg u)

/-- Input: ordered rational heights and a nonnegative endpoint below exp(-v/2).
Claim: the exact rational transport allowance bounds the actual ramp at u.
Proof: multiply the exponential transport bound by the exact factor.
No primality or fixed numerical scale is needed. -/
theorem gamma_rational_transport_le {u v e : ℚ} (huv : u ≤ v) (he : 0 ≤ e)
    (hev : (e : ℝ) ≤ Real.exp (-(v : ℝ) / 2)) (n : ℕ) :
    (gammaRationalTransportLower u v e n : ℝ) ≤ exponentialRampWeight (u : ℝ) := by
  have h :=
    gamma_exp_square_taylor_lower ((Rat.cast_le (K := ℝ)).mpr huv)
      ((Rat.cast_nonneg (K := ℝ)).mpr he) hev n
  have ht : (e : ℝ) ^ 2 * (gammaPositiveTaylor (v - u) n : ℝ) ≤ Real.exp (-(u : ℝ)) := by
    simpa only [gammaPositiveTaylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_sub] using h
  rw [gammaRationalTransportLower, Rat.cast_mul, Rat.cast_mul, Rat.cast_pow,
    exponentialRampWeight_eq_rational_factor]
  exact
    mul_le_mul_of_nonneg_right ht
      ((Rat.cast_nonneg (K := ℝ)).mpr (gamma_rational_ramp_factor_nonneg u))

/-- Input: nonnegative mass, positive ordered scales, and a half-scale ramp endpoint.
Claim: rational transport bounds the ramp at the target scale.
Proof: the ramp endpoint bounds the half-scale exponential, and ordered
scales reverse the heights. This is independent of prime-power certificates. -/
theorem gamma_rational_transport_of_ramp_le {m a x e : ℚ} (hm : 0 ≤ m) (ha : 0 < a) (hax : a ≤ x)
    (he : 0 ≤ e) (hw : (e : ℝ) ≤ exponentialRampWeight ((m / (2 * a) : ℚ) : ℝ)) (n : ℕ) :
    (gammaRationalTransportLower (m / x) (m / a) e n : ℝ) ≤
      exponentialRampWeight ((m / x : ℚ) : ℝ) := by
  have hb := hw.trans (exponentialRampWeight_bounds _).2
  have hh : ((m / (2 * a) : ℚ) : ℝ) = ((m / a : ℚ) : ℝ) / 2 := by
    simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, div_div]
    rw [mul_comm (a : ℝ) 2]
  rw [hh] at hb
  exact
    gamma_rational_transport_le (div_le_div₀ hm le_rfl ha hax) he (by simpa only [neg_div] using hb)
      n

/-- The reserved lower allowance of a prime-power row at target scale x.
The row is certified at scale 2a. Square only its ramp endpoint, multiply
by the nonnegative Taylor sum at index times (1/a-1/x), and retain the exact
ramp factor at x. The log endpoint is used once, preserving Mangoldt weight. -/
def GammaFiniteRampRow.reservedLower (r : GammaFiniteRampRow) (a x : ℚ) (n : ℕ) : ℚ :=
  r.logLower * r.rampLower ^ 2 * gammaPositiveTaylor ((r.index : ℚ) * (1 / a - 1 / x)) n *
    gammaRationalRampFactor ((r.index : ℚ) / x)

/-- Input: any row, scales and term count.
Claim: the row allowance is its log endpoint times the common transport allowance.
Proof: distribute division in the Taylor height and associate products.
This identifies executable row data with the generic analytic bound. -/
theorem GammaFiniteRampRow.reservedLower_eq (r : GammaFiniteRampRow) (a x : ℚ) (n : ℕ) :
    r.reservedLower a x n =
      r.logLower *
        gammaRationalTransportLower ((r.index : ℚ) / x) ((r.index : ℚ) / a) r.rampLower n := by
  have hd : (r.index : ℚ) * (1 / a - 1 / x) = (r.index : ℚ) / a - (r.index : ℚ) / x := by ring
  rw [GammaFiniteRampRow.reservedLower, hd, gammaRationalTransportLower]
  ring

/-- Input: positive anchor a at most x, primality, and the row check at 2a.
Claim: the reserved rational allowance bounds the actual atom at x.
Proof: use the checked log and half-scale endpoint, the squared
exponential Taylor bound, and the exact ramp factor at x.
This includes rows entering support after a and respects both moving joins. -/
theorem GammaFiniteRampRow.reservedLower_le (r : GammaFiniteRampRow) {a x : ℚ} (ha : 0 < a)
    (hax : a ≤ x) (hp : r.prime.Prime) (hc : r.check (2 * a) = true) (n : ℕ) :
    (r.reservedLower a x n : ℝ) ≤
      ArithmeticFunction.vonMangoldt r.index * exponentialRampWeight ((r.index : ℝ) / (x : ℝ)) := by
  obtain ⟨hlog, hramp⟩ := Bool.and_eq_true_iff.mp hc
  have hl := (rationalLogIntervalCheck_sound hlog).1
  have hw := gamma_rational_ramp_lower_check_sound hramp
  have ht :=
    gamma_rational_transport_of_ramp_le (Nat.cast_nonneg r.index) ha hax
      ((Rat.cast_nonneg (K := ℝ)).mp hw.1) hw.2 n
  have hz :=
    (Rat.cast_nonneg (K := ℝ)).mpr
      (gamma_rational_transport_nonneg (e := r.rampLower)
        (div_le_div₀ (Nat.cast_nonneg r.index) le_rfl ha hax) n)
  norm_num only [Rat.cast_natCast] at hl
  have hm := mul_le_mul hl ht hz (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le))
  rw [r.reservedLower_eq, Rat.cast_mul]
  rw [GammaFiniteRampRow.index,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero r.exponent),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  simpa only [GammaFiniteRampRow.index, Rat.cast_div, Rat.cast_natCast] using hm

/-- Input: distinct checked prime-power rows inside the natural interval.
Claim: their reserved allowances bound the full actual interval sum at x.
Proof: sum the row bounds and retain nonnegative omitted atoms.
This is the reusable block interface for a closed-cell lower input. -/
theorem gamma_reserved_ramp_row_block_lower (rows : List GammaFiniteRampRow) (lo hi : ℕ) {a x : ℚ}
    (ha : 0 < a) (hax : a ≤ x) (n : ℕ) (hp : rows.Forall (fun r ↦ r.prime.Prime))
    (hc : rows.Forall (fun r ↦ r.check (2 * a) = true))
    (hn : (rows.map GammaFiniteRampRow.index).Nodup)
    (hm : rows.Forall (fun r ↦ lo < r.index ∧ r.index ≤ hi)) :
    (((rows.map (fun r ↦ r.reservedLower a x n)).sum : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc lo hi,
        ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (x : ℝ)) := by
  have hl :=
    List.sum_le_sum
      (fun (r : GammaFiniteRampRow) hr ↦
        r.reservedLower_le ha hax (List.forall_iff_forall_mem.mp hp r hr)
          (List.forall_iff_forall_mem.mp hc r hr) n)
  have hs : (rows.map GammaFiniteRampRow.index).toFinset ⊆ Finset.Ioc lo hi := by
    intro m hmem
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
    exact Finset.mem_Ioc.mpr (List.forall_iff_forall_mem.mp hm r hr)
  have ht :=
    Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun m _ _ ↦
        mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := m))
          (exponentialRampWeight_bounds ((m : ℝ) / (x : ℝ))).1)
  rw [List.sum_toFinset
      (fun m ↦ ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (x : ℝ))) hn,
    List.map_map] at ht
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact hl.trans ht

/-- Input: a positive real scale and a natural index beyond its support cutoff.
Claim: the actual Mangoldt-ramp atom vanishes.
Proof: the floor inequality puts the height past the ramp endpoint.
This permits reserved rows beyond the current support without a cutoff hypothesis. -/
theorem gamma_ramp_atom_eq_zero_of_cutoff_lt {x : ℝ} (hx : 0 < x) {m : ℕ}
    (hm : ⌊x * (99 / 40 : ℝ)⌋₊ < m) :
    ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / x) = 0 := by
  have hh : 99 / 40 ≤ (m : ℝ) / x :=
    (le_div_iff₀ hx).mpr (by simpa only [mul_comm] using (Nat.lt_of_floor_lt hm).le)
  rw [exponentialRampWeight_eq_zero hh, mul_zero]

/-- Input: any finite set of positive natural indices and a positive real scale.
Claim: its actual ramp sum is below the full actual ramp sum.
Proof: discard zero atoms outside support, then use nonnegativity.
There is no upper restriction on the indices or the scale. -/
theorem gamma_ramp_finset_le_actual (s : Finset ℕ) {x : ℝ} (hx : 0 < x) (hs : ∀ m ∈ s, 0 < m) :
    (∑ m ∈ s, ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / x)) ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x := by
  have heq :=
    Finset.sum_subset (Finset.filter_subset (fun m ↦ m ≤ ⌊x * (99 / 40 : ℝ)⌋₊) s) (f := fun m ↦
      ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / x))
      (fun m hm hnot ↦
        gamma_ramp_atom_eq_zero_of_cutoff_lt hx
          (lt_of_not_ge (fun h ↦ hnot (Finset.mem_filter.mpr ⟨hm, h⟩))))
  have hsub : s.filter (fun m ↦ m ≤ ⌊x * (99 / 40 : ℝ)⌋₊) ⊆ Finset.Ioc 0 ⌊x * (99 / 40 : ℝ)⌋₊ := by
    intro m hm
    obtain ⟨hms, hmc⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_Ioc.mpr ⟨hs m hms, hmc⟩
  rw [← heq]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ ↦
        mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := m))
          (exponentialRampWeight_bounds _).1)

/-- Input: distinct checked prime-power rows in a finite positive interval,
a positive anchor, and any later rational scale.
Claim: the sum of transported allowances bounds the actual ramp sum.
Proof: apply the row block bound and the unrestricted finite-set bound.
The reserved upper index may exceed the current ramp support. -/
theorem gamma_reserved_ramp_rows_lower_actual (rows : List GammaFiniteRampRow) (N : ℕ) {a x : ℚ}
    (ha : 0 < a) (hax : a ≤ x) (n : ℕ) (hp : rows.Forall (fun r ↦ r.prime.Prime))
    (hc : rows.Forall (fun r ↦ r.check (2 * a) = true))
    (hn : (rows.map GammaFiniteRampRow.index).Nodup)
    (hm : rows.Forall (fun r ↦ 0 < r.index ∧ r.index ≤ N)) :
    (((rows.map (fun r ↦ r.reservedLower a x n)).sum : ℚ) : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x := by
  exact
    (gamma_reserved_ramp_row_block_lower rows 0 N ha hax n hp hc hn hm).trans
      (gamma_ramp_finset_le_actual (Finset.Ioc 0 N) ((Rat.cast_pos (K := ℝ)).mpr (ha.trans_le hax))
        (fun _ hm ↦ (Finset.mem_Ioc.mp hm).1))

end PseudoPrime.Analysis
