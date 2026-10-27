/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalGcdReduction

/-! # Divisor counting for rational quotient sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Pairs from A times B with fixed numerator gcd, denominator gcd and quotient z.
The cell is finite; its divisor encoding bounds the number of representations of z. -/
noncomputable def quotientGcdCell (A B : Finset ℚ) (r s : ℕ) (z : ℚ) : Finset (ℚ × ℚ) := by
  classical
    exact
    (A ×ˢ B).filter
      (fun q ↦ q.1.num.natAbs.gcd q.2.num.natAbs = r ∧ q.1.den.gcd q.2.den = s ∧ q.1 / q.2 = z)

/-- For positive rational families, encode each fixed-gcd quotient representation by
its first numerator and denominator cofactors. These divide the canonical
numerator and denominator of z. -/
theorem quotientGcdCell_encoding_mem {A B : Finset ℚ} {r s : ℕ} {z : ℚ} (hA : ∀ q ∈ A, 0 < q)
    (hB : ∀ q ∈ B, 0 < q) {q : ℚ × ℚ} (hq : q ∈ quotientGcdCell A B r s z) :
    (q.1.num.natAbs / r, q.1.den / s) ∈ (z.num.natAbs.divisors ×ˢ z.den.divisors) := by
  classical
  obtain ⟨hmem, hr, hs, hz⟩ := Finset.mem_filter.mp hq
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hmem
  have hf := positive_quotient_num_den (hA _ ha) (hB _ hb)
  rw [hr, hs, hz] at hf
  have hzpos : 0 < z := hz ▸ div_pos (hA _ ha) (hB _ hb)
  apply Finset.mem_product.mpr
  constructor
  · apply Nat.mem_divisors.mpr
    exact
      ⟨hf.1.symm ▸ Nat.dvd_mul_right _ _,
        Nat.ne_of_gt (Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hzpos)))⟩
  · apply Nat.mem_divisors.mpr
    exact ⟨hf.2.symm ▸ Nat.dvd_mul_left _ _, z.den_ne_zero⟩

/-- For positive rational families the gcd-cofactor encoding of a quotient cell is
injective. Fixed gcds recover the first rational, and the nonzero quotient
equation recovers the second. -/
theorem quotientGcdCell_encoding_injective {A B : Finset ℚ} {r s : ℕ} {z : ℚ} (hA : ∀ q ∈ A, 0 < q)
    (hB : ∀ q ∈ B, 0 < q) :
    Set.InjOn (fun q : ℚ × ℚ ↦ (q.1.num.natAbs / r, q.1.den / s)) (quotientGcdCell A B r s z) := by
  intro q hq t ht he
  obtain ⟨hmq, hrq, hsq, hzq⟩ := Finset.mem_filter.mp hq
  obtain ⟨hmt, hrt, hst, hzt⟩ := Finset.mem_filter.mp ht
  have hqa := hA q.1 (Finset.mem_product.mp hmq).1
  have hta := hA t.1 (Finset.mem_product.mp hmt).1
  have hqb := hB q.2 (Finset.mem_product.mp hmq).2
  have htb := hB t.2 (Finset.mem_product.mp hmt).2
  have hqr : r ∣ q.1.num.natAbs := hrq ▸ Nat.gcd_dvd_left _ _
  have htr : r ∣ t.1.num.natAbs := hrt ▸ Nat.gcd_dvd_left _ _
  have hqs : s ∣ q.1.den := hsq ▸ Nat.gcd_dvd_left _ _
  have hts : s ∣ t.1.den := hst ▸ Nat.gcd_dvd_left _ _
  have hn : q.1.num.natAbs = t.1.num.natAbs := by
    calc
      _ = (q.1.num.natAbs / r) * r := (Nat.div_mul_cancel hqr).symm
      _ = (t.1.num.natAbs / r) * r := congrArg (fun a ↦ a * r) (congrArg Prod.fst he)
      _ = _ := Nat.div_mul_cancel htr
  have hd : q.1.den = t.1.den := by
    calc
      _ = (q.1.den / s) * s := (Nat.div_mul_cancel hqs).symm
      _ = (t.1.den / s) * s := congrArg (fun a ↦ a * s) (congrArg Prod.snd he)
      _ = _ := Nat.div_mul_cancel hts
  have hfirst : q.1 = t.1 := by
    calc
      _ = (q.1.num.natAbs : ℚ) / q.1.den := positive_rat_nat_fraction hqa
      _ = (t.1.num.natAbs : ℚ) / t.1.den := by rw [hn, hd]
      _ = _ := (positive_rat_nat_fraction hta).symm
  apply Prod.ext hfirst
  have hratio := hzq.trans (hzt.symm.trans (congrArg (fun a ↦ a / t.2) hfirst.symm))
  have hm := (div_eq_div_iff (ne_of_gt hqb) (ne_of_gt htb)).mp hratio
  exact (mul_left_cancel₀ (ne_of_gt hqa) hm).symm

/-- For positive rational families a fixed-gcd cell at z has at most
tau(num(z))*tau(den(z)) pairs. Inject into the product of the two actual divisor sets. -/
theorem card_quotientGcdCell_le {A B : Finset ℚ} {r s : ℕ} {z : ℚ} (hA : ∀ q ∈ A, 0 < q)
    (hB : ∀ q ∈ B, 0 < q) :
    (quotientGcdCell A B r s z).card ≤ z.num.natAbs.divisors.card * z.den.divisors.card := by
  classical
  have hc :=
    Finset.card_le_card_of_injOn (s := quotientGcdCell A B r s z) (t :=
      z.num.natAbs.divisors ×ˢ z.den.divisors) (fun q : ℚ × ℚ ↦ (q.1.num.natAbs / r, q.1.den / s))
      (fun q hq ↦ quotientGcdCell_encoding_mem hA hB hq) (quotientGcdCell_encoding_injective hA hB)
  exact hc.trans_eq (Finset.card_product _ _)

/-- Pairs from A times B with a fixed numerator gcd r and denominator gcd s.
Partition this finite class by quotient value to apply the divisor representation bound. -/
noncomputable def quotientGcdClass (A B : Finset ℚ) (r s : ℕ) : Finset (ℚ × ℚ) := by
  classical
    exact (A ×ˢ B).filter (fun q ↦ q.1.num.natAbs.gcd q.2.num.natAbs = r ∧ q.1.den.gcd q.2.den = s)

/-- The finite set of quotients q/t from q in A and t in B.
Positivity assumptions are supplied by the counting theorems, not built into the definition. -/
noncomputable def rationalQuotientSet (A B : Finset ℚ) : Finset ℚ := by
  classical exact (A ×ˢ B).image (fun q ↦ q.1 / q.2)

/-- Rationals in A whose canonical numerator is divisible by r and denominator by s.
The incidence sum is bounded by the divisor count of numerator times denominator. -/
noncomputable def divisorSlice (A : Finset ℚ) (r s : ℕ) : Finset ℚ := by
  classical exact A.filter (fun q ↦ r ∣ q.num.natAbs ∧ s ∣ q.den)

/-- A quotient cell is the quotient fiber inside its gcd class.
Reassociate the defining finite predicates to connect fiberwise counting. -/
theorem quotientGcdCell_eq_filter (A B : Finset ℚ) (r s : ℕ) (z : ℚ) :
    quotientGcdCell A B r s z = (quotientGcdClass A B r s).filter (fun q ↦ q.1 / q.2 = z) := by
  classical
  ext q
  simp only [quotientGcdCell, quotientGcdClass, Finset.mem_filter, and_assoc]

/-- The sum of quotient-cell cardinalities equals the gcd-class cardinality.
Partition by all quotient values occurring in A times B. -/
theorem sum_card_quotientGcdCell (A B : Finset ℚ) (r s : ℕ) :
    (∑ z ∈ rationalQuotientSet A B, (quotientGcdCell A B r s z).card) =
      (quotientGcdClass A B r s).card := by
  classical
  have he :=
    Finset.sum_card_fiberwise_eq_card_filter (quotientGcdClass A B r s) (rationalQuotientSet A B)
      (fun q ↦ q.1 / q.2)
  have hf :
    (quotientGcdClass A B r s).filter (fun q ↦ q.1 / q.2 ∈ rationalQuotientSet A B) =
      quotientGcdClass A B r s := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact Finset.mem_image.mpr ⟨q, (Finset.mem_filter.mp hq).1, rfl⟩
  rw [hf] at he
  simpa only [quotientGcdCell_eq_filter] using he

/-- For positive families and a bound T for the canonical divisor counts of all
quotients, each gcd class has at most card(A/B)*T^2 elements. Sum the proved fiber bounds. -/
theorem card_quotientGcdClass_le_of_divisor_bound {A B : Finset ℚ} {r s T : ℕ} (hA : ∀ q ∈ A, 0 < q)
    (hB : ∀ q ∈ B, 0 < q)
    (hT : ∀ z ∈ rationalQuotientSet A B, z.num.natAbs.divisors.card ≤ T ∧ z.den.divisors.card ≤ T) :
    (quotientGcdClass A B r s).card ≤ (rationalQuotientSet A B).card * T ^ 2 := by
  classical
  rw [← sum_card_quotientGcdCell]
  calc
    _ ≤ ∑ z ∈ rationalQuotientSet A B, T ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact
        (card_quotientGcdCell_le hA hB).trans
          ((Nat.mul_le_mul (hT z hz).1 (hT z hz).2).trans_eq (pow_two T).symm)
    _ = _ := Finset.sum_const_nat (fun _ _ ↦ rfl)

/-- A gcd class lies in the product of the corresponding divisor slices.
Gcd divisibility bounds its cardinality by the product of the two slice cardinalities. -/
theorem card_quotientGcdClass_le_slices (A B : Finset ℚ) (r s : ℕ) :
    (quotientGcdClass A B r s).card ≤ (divisorSlice A r s).card * (divisorSlice B r s).card := by
  classical
  apply (Finset.card_le_card _).trans_eq (Finset.card_product _ _)
  intro q hq
  obtain ⟨hm, hr, hs⟩ := Finset.mem_filter.mp hq
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hm
  apply Finset.mem_product.mpr
  exact
    ⟨Finset.mem_filter.mpr ⟨ha, hr ▸ Nat.gcd_dvd_left _ _, hs ▸ Nat.gcd_dvd_left _ _⟩,
      Finset.mem_filter.mpr ⟨hb, hr ▸ Nat.gcd_dvd_right _ _, hs ▸ Nat.gcd_dvd_right _ _⟩⟩

end PseudoPrime.NumberTheory.Heilbronn
