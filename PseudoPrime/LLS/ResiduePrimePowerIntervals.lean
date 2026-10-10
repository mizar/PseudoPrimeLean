/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ResidueGapIntervals
public import PseudoPrime.LLS.CosetRootBounds

/-! Normalized prime-power bounds from lower-cutoff interval certificates. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a positive base b≤x and a fixed exponent limit K, the odd root prefix
normalized by sqrt x is at most its value at b. Sum the decreasing root-slice
ratios. This transfers a finite interval's root calculation to its lower cutoff. -/
theorem oddRootPrefix_div_sqrt_le_at_base {b x : ℝ} (hb : 0 < b) (hx : b ≤ x) (K : ℕ) :
    (∑ k ∈ (Finset.Icc 3 K).filter Odd,
          (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) /
        Real.sqrt x ≤
      (∑ k ∈ (Finset.Icc 3 K).filter Odd,
          (k : ℝ) * (b ^ ((1 : ℝ) / k) + Real.sqrt (b ^ ((1 : ℝ) / k)) / 20)) /
        Real.sqrt b := by
  rw [Finset.sum_div, Finset.sum_div]
  exact
    Finset.sum_le_sum fun k hk ↦
      rootSlice_div_sqrt_le_at_base hb hx
        ((by norm_num only : 2 ≤ 3).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1)

/-- For a nonnegative cutoff and nonnegative supplied root bounds b and c,
assume X≤b(k)^k and b(k)≤c(k)^2 at each odd exponent from three through K.
Bound each real root and square root, then sum the weighted inequalities.
This certifies a fixed prefix without assumptions on a logarithmic exponent limit. -/
theorem oddRootPrefix_le_power_certificates {X : ℝ} (hX : 0 ≤ X) (K : ℕ) (b c : ℕ → ℝ)
    (hb : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ b k)
    (hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ c k)
    (hpow : ∀ k ∈ (Finset.Icc 3 K).filter Odd, X ≤ b k ^ k)
    (hsq : ∀ k ∈ (Finset.Icc 3 K).filter Odd, b k ≤ c k ^ 2) :
    (∑ k ∈ (Finset.Icc 3 K).filter Odd,
        (k : ℝ) * (X ^ ((1 : ℝ) / k) + Real.sqrt (X ^ ((1 : ℝ) / k)) / 20)) ≤
      ∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * (b k + c k / 20) := by
  apply Finset.sum_le_sum
  intro k hk
  have hk0 : 0 < k :=
    lt_of_lt_of_le (by norm_num only : 0 < 3) (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  have hr := root_le_of_le_nat_pow hX (hb k hk) hk0 (hpow k hk)
  have hs := (Real.sqrt_le_left (hc k hk)).mpr (hr.trans (hsq k hk))
  exact
    mul_le_mul_of_nonneg_left
      (add_le_add hr (div_le_div_of_nonneg_right hs (by norm_num only : (0 : ℝ) ≤ 20)))
      (Nat.cast_nonneg k)

/-- Assume a positive lower radius s₀ with s₀²≤x and an exponent limit K covering
the cutoff logarithm. Nonnegative power and square-root certificates at s₀² bound
the variable odd root sum divided by sqrt x. Extend its exponent set, transfer
the normalized prefix to the lower cutoff and apply the finite power bounds.
This is the odd-prime-power input to shared residue interval estimates. -/
theorem oddRootSum_normalized_le_base_certificates {s₀ x : ℝ} (hs₀ : 0 < s₀) (hbase : s₀ ^ 2 ≤ x)
    {K : ℕ} (hK : ⌊Real.log x / Real.log 2⌋₊ ≤ K) (b c : ℕ → ℝ)
    (hb : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ b k)
    (hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ c k)
    (hpow : ∀ k ∈ (Finset.Icc 3 K).filter Odd, s₀ ^ 2 ≤ b k ^ k)
    (hsq : ∀ k ∈ (Finset.Icc 3 K).filter Odd, b k ≤ c k ^ 2) :
    (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
          (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) /
        Real.sqrt x ≤
      (∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * (b k + c k / 20)) / s₀ := by
  have hsub :
    (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd ⊆ (Finset.Icc 3 K).filter Odd := by
    intro k hk
    obtain ⟨hi, ho⟩ := Finset.mem_filter.mp hk
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hK⟩, ho⟩
  have he :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ ↦
      (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) hsub
      (fun k _ _ ↦
        mul_nonneg (Nat.cast_nonneg k)
          (add_nonneg (Real.rpow_nonneg ((sq_nonneg s₀).trans hbase) _)
            (div_nonneg (Real.sqrt_nonneg _) (by norm_num only : (0 : ℝ) ≤ 20))))
  have hr := oddRootPrefix_div_sqrt_le_at_base (sq_pos_of_pos hs₀) hbase K
  have hp :=
    div_le_div_of_nonneg_right
      (oddRootPrefix_le_power_certificates (sq_nonneg s₀) K b c hb hc hpow hsq)
      (Real.sqrt_nonneg (s₀ ^ 2))
  rw [Real.sqrt_sq hs₀.le] at hr hp
  exact (div_le_div_of_nonneg_right he (Real.sqrt_nonneg x)).trans (hr.trans hp)

/-- For a positive radius, normalize the square-congruence majorant by that
radius and separate the modulus and radius reciprocals. Cancel the radius in
the first quotient. This exposes the two lower endpoints used in its interval bound. -/
theorem squareResidueMajorant_normalized_eq {s : ℝ} (hs : 0 < s) (q C : ℝ) :
    C * (s / q + 1) / s = C * (1 / q + 1 / s) := by
  rw [mul_div_assoc, add_div, div_right_comm (b := q) (c := s), div_self hs.ne']

/-- Assume positive lower radius and modulus endpoints, a cutoff square at least
one, an upper cutoff logarithm and an upper distinct-prime count. The square
majorant divided by the radius is bounded at these endpoints. Compare the powers,
squared logarithms and reciprocal factors and multiply their nonnegative bounds. -/
theorem squareResidueMajorant_normalized_le_interval {s₀ s q₀ q T₁ : ℝ} {w W : ℕ} (hs₀ : 0 < s₀)
    (hss : s₀ ≤ s) (hq₀ : 0 < q₀) (hqq : q₀ ≤ q) (hx : 1 ≤ s ^ 2) (hT : Real.log (s ^ 2) ≤ T₁)
    (hw : w ≤ W) :
    (2 : ℝ) ^ w * (Real.log (s ^ 2)) ^ 2 / 4 * (s / q + 1) / s ≤
      (2 : ℝ) ^ W * T₁ ^ 2 / 4 * (1 / q₀ + 1 / s₀) := by
  rw [squareResidueMajorant_normalized_eq (hs₀.trans_le hss)]
  have hl := Real.log_nonneg hx
  have ht := (sq_le_sq₀ hl (hl.trans hT)).mpr hT
  have hp :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num only : (1 : ℝ) ≤ 2) hw) ht
      (sq_nonneg (Real.log (s ^ 2))) (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) W)
  have hr := add_le_add (one_div_le_one_div_of_le hq₀ hqq) (one_div_le_one_div_of_le hs₀ hss)
  exact
    mul_le_mul (div_le_div_of_nonneg_right hp (by norm_num only : (0 : ℝ) ≤ 4)) hr
      (add_nonneg (one_div_nonneg.mpr (hq₀.le.trans hqq)) (one_div_nonneg.mpr (hs₀.le.trans hss)))
      (div_nonneg (mul_nonneg (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) W) (sq_nonneg T₁))
        (by norm_num only : (0 : ℝ) ≤ 4))

/-- Under RH and a cutoff square greater than one, assume no prime in the unit
residue up to the cutoff. Positive lower modulus and radius endpoints, upper
logarithm and prime-count bounds and lower-cutoff power certificates bound its
Mangoldt sum divided by the radius. Apply the prime-free square-plus-odd-root
estimate and the two interval estimates. This supplies the prime-free input to
shared parity gap certificates. -/
theorem residue_logWeightedSum_normalized_le_interval_of_no_prime {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hRH : RiemannHypothesis) {q₀ s₀ s T₁ : ℝ} {W K : ℕ} (hs₀ : 0 < s₀) (hss : s₀ ≤ s)
    (hq₀ : 0 < q₀) (hqq : q₀ ≤ q) (hx : 1 < s ^ 2) (hT : Real.log (s ^ 2) ≤ T₁)
    (hw : q.primeFactors.card ≤ W) (hK : ⌊Real.log (s ^ 2) / Real.log 2⌋₊ ≤ K) (b c : ℕ → ℝ)
    (hb : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ b k)
    (hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ c k)
    (hpow : ∀ k ∈ (Finset.Icc 3 K).filter Odd, s₀ ^ 2 ≤ b k ^ k)
    (hsq : ∀ k ∈ (Finset.Icc 3 K).filter Odd, b k ≤ c k ^ 2)
    (hno : ∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ s ^ 2) :
    (∑ n ∈ (Finset.Icc 1 ⌊s ^ 2⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (s ^ 2) n) /
        s ≤
      (2 : ℝ) ^ W * T₁ ^ 2 / 4 * (1 / q₀ + 1 / s₀) +
        (∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * (b k + c k / 20)) / s₀ := by
  have hs := residue_logWeightedSum_le_root_sum_of_no_prime a hRH hx hno
  rw [Real.sqrt_sq (hs₀.le.trans hss)] at hs
  have hr :=
    oddRootSum_normalized_le_base_certificates hs₀ ((sq_le_sq₀ hs₀.le (hs₀.le.trans hss)).mpr hss)
      hK b c hb hc hpow hsq
  rw [Real.sqrt_sq (hs₀.le.trans hss)] at hr
  have hq := squareResidueMajorant_normalized_le_interval hs₀ hss hq₀ hqq hx.le hT hw
  have hd := div_le_div_of_nonneg_right hs (hs₀.le.trans hss)
  rw [add_div] at hd
  exact hd.trans (add_le_add hq hr)

/-- Normalized prime-free bound from a lower modulus q₀, lower radius s₀,
upper cutoff logarithm T₁, upper distinct-prime count W and odd root certificates
through K. Add the square-congruence bound and the lower-cutoff odd root cost.
Under the corresponding interval and power inequalities it bounds the residue
Mangoldt sum divided by the radius when no prime occurs below the cutoff. -/
noncomputable def residuePrimePowerIntervalBound (q₀ s₀ T₁ : ℝ) (W K : ℕ) (b c : ℕ → ℝ) : ℝ :=
  (2 : ℝ) ^ W * T₁ ^ 2 / 4 * (1 / q₀ + 1 / s₀) +
    (∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * (b k + c k / 20)) / s₀

/-- Under GRH, lower-endpoint odd root certificates and a strict uniform parity
gap bound the least prime in every unit residue at the cutoff radius squared.
Assume a modulus from 64 through 20000, positive lower totient, radius and modulus
bounds, the logarithmic interval, exponent and prime-count bounds, and the existing
cutoff and sign guards. Bound the prime-free Mangoldt sum by the radius times its
normalized interval bound and apply the parity interval theorem.
This removes a separate prime-free-sum hypothesis from interval certificates. -/
theorem exists_least_prime_in_residue_le_of_interval_power_certificates {q : ℕ} [NeZero q]
    (a : (ZMod q)ˣ) (hq : 64 ≤ q) (hu : q ≤ 20000)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q₀ h₀ s₀ s L₁ T₁ : ℝ} {W K : ℕ}
    (hh : (2 : ℝ) ≤ q.totient) (hh₀ : 0 < h₀) (hhh : h₀ ≤ q.totient) (hs₀ : 0 < s₀) (hss : s₀ ≤ s)
    (hq₀ : 0 < q₀) (hqq : q₀ ≤ q) (hs : (q.totient : ℝ) * Real.log q = s) (hx : 65536 ≤ s ^ 2)
    (hL : 1719 / 1000 ≤ Real.log q) (hLL : Real.log q ≤ L₁) (hT : 0 ≤ T₁)
    (hTx : Real.log (s ^ 2) ≤ T₁) (hw : q.primeFactors.card ≤ W)
    (hK : ⌊Real.log (s ^ 2) / Real.log 2⌋₊ ≤ K) (b c : ℕ → ℝ)
    (hb : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ b k)
    (hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ c k)
    (hpow : ∀ k ∈ (Finset.Icc 3 K).filter Odd, s₀ ^ 2 ≤ b k ^ k)
    (hsq : ∀ k ∈ (Finset.Icc 3 K).filter Odd, b k ≤ c k ^ 2)
    (hC : 0 ≤ residueParityIntervalCoefficient q.totient (s ^ 2) (Real.log q) T₁)
    (hR : 0 ≤ T₁ - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s))
    (hg :
      residueParityIntervalMajorant h₀ s₀ L₁ T₁ (residuePrimePowerIntervalBound q₀ s₀ T₁ W K b c)
          W <
        1719 / 1000) :
    ∃ p : ℕ, IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ s ^ 2 := by
  let A := residuePrimePowerIntervalBound q₀ s₀ T₁ W K b c
  have hf (hno : ∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ s ^ 2) :
    (∑ n ∈ (Finset.Icc 1 ⌊s ^ 2⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (s ^ 2) n) ≤
      s * A := by
    rw [mul_comm s A]
    exact
      (div_le_iff₀ (hs₀.trans_le hss)).mp
        (residue_logWeightedSum_normalized_le_interval_of_no_prime a hGRH.riemann hs₀ hss hq₀ hqq
          (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 65536) hx) hTx hw hK b c hb hc hpow hsq hno)
  have hA : s * A / s ≤ A := (mul_div_cancel_left₀ A (hs₀.trans_le hss).ne').le
  exact
    exists_least_prime_in_residue_le_of_parity_interval a hq hu hGRH hh hh₀ hhh hs₀ hss hs hx hL hLL
      hT hTx le_rfl (Nat.cast_le.mpr hw) hA hC hR hf hg

end PseudoPrime.LLS.PaperStatements
