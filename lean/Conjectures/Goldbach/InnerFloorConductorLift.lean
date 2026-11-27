import Mathlib
import Conjectures.Goldbach.InnerFloorReducedGaussEnergy
import Conjectures.Goldbach.ShortProgressionsMeanTheta

/-!
Reduced-numerator conductor aggregation. This is an auxiliary research
statement and does not assume or assert the unproved primitive mean square.
The accepted ShortProgressionsMeanTheta module supplies the exact conductor
lifting for interior prime windows and the reciprocal-totient estimates.
-/

open Finset
open scoped Classical
namespace InnerFloorResearch
noncomputable section

open BombieriVinogradov.LargeSieve
open DyadicMixedB4ConductorPartition
open Conjectures.Goldbach.ReflectionCharacterContraction_aux

def reducedLevelEnergy (b : (q : ℕ) → (ZMod q)ˣ → ℂ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : (ZMod q)ˣ, ‖unitAdditiveError (b q) a‖^2

/-- Only logarithmic conductor multiplicity is paid in the reduced projection.
F d is an arbitrary primitive-family energy budget. -/
theorem reducedFamilyEnergy (A : ℕ)
    (b : (q : ℕ) → (ZMod q)ˣ → ℂ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d)
    (hcompat : ∀ (q : ℕ) [NeZero q], q ≤ A →
      ∀ (d : ℕ) (hd : d ∣ q),
        (∑ ψ ∈ primitiveCharacters d,
          ‖unitCharacterError (b q) (DirichletCharacter.changeLevel hd ψ)‖^2) ≤ F d) :
    (∑ q ∈ Icc 1 A, reducedLevelEnergy b q) ≤
      (∑ d ∈ Icc 1 A, (d : ℝ)*F d/(d.totient : ℝ)) *
        (ShortAPLinearTotient.weightConstant*(1+Real.log A)) := by
  have hterm (q : ℕ) (hq : q ∈ Icc 1 A) :
      reducedLevelEnergy b q ≤ (∑ d ∈ q.divisors, (d : ℝ)*F d)/(q.totient : ℝ) := by
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    letI : NeZero q := ⟨hq0.ne'⟩
    simp only [reducedLevelEnergy, dif_neg hq0.ne']
    apply (reducedConductorEnergy (b q)).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [sum_conductor_partition]
    rw [← Finset.sum_attach q.divisors (fun d => (d : ℝ)*F d)]
    apply sum_le_sum
    intro d _
    have hd : d.1 ∣ q := (Nat.mem_divisors.mp d.2).1
    calc
      _ = (d.1 : ℝ) * ∑ ψ ∈ primitiveCharacters d.1,
          ‖unitCharacterError (b q) (DirichletCharacter.changeLevel hd ψ)‖^2 := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro ψ hψ
        have hp : ψ.IsPrimitive := (mem_filter.mp hψ).2
        rw [(DirichletCharacter.conductor_changeLevel ψ hd).trans hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcompat q (mem_Icc.mp hq).2 d.1 hd)
        (Nat.cast_nonneg _)
  exact (sum_le_sum hterm).trans
    (ShortAPLinearTotient.sum_conductor_weights A (fun d => (d : ℝ)*F d)
      (fun d => mul_nonneg (Nat.cast_nonneg _) (hF d)))

/-- Two logarithms, rather than a polynomial factor in A, suffice to lift
a primitive squared-error budget to reduced-numerator energy. -/
theorem reducedFamilyEnergyLog (A : ℕ)
    (b : (q : ℕ) → (ZMod q)ˣ → ℂ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d)
    (hcompat : ∀ (q : ℕ) [NeZero q], q ≤ A →
      ∀ (d : ℕ) (hd : d ∣ q),
        (∑ ψ ∈ primitiveCharacters d,
          ‖unitCharacterError (b q) (DirichletCharacter.changeLevel hd ψ)‖^2) ≤ F d) :
    (∑ q ∈ Icc 1 A, reducedLevelEnergy b q) ≤
      (ShortAPLinearTotient.weightConstant*(1+Real.log A))^2 *
        ∑ d ∈ Icc 1 A, F d := by
  let W := ShortAPLinearTotient.weightConstant
  let L := 1 + Real.log A
  have hW : 0 ≤ W := ShortAPLinearTotient.weightConstant_nonneg
  have hL : 0 ≤ L := by
    dsimp [L]
    linarith [Real.log_natCast_nonneg A]
  have hs : (∑ d ∈ Icc 1 A, (d : ℝ)*F d/(d.totient : ℝ)) ≤
      (W*L)*(∑ d ∈ Icc 1 A, F d) := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have h := ShortAPLinearTotient.ratio_totient_le d (mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hdA : (d : ℝ) ≤ A := by exact_mod_cast (mem_Icc.mp hd).2
    have hl := Real.log_le_log hd0 hdA
    have h' : (d : ℝ)/(d.totient : ℝ) ≤ W*L :=
      h.trans (mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) hW)
    calc
      _ = ((d : ℝ)/(d.totient : ℝ))*F d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h' (hF d)
  calc
    _ ≤ _ := reducedFamilyEnergy A b F hF hcompat
    _ ≤ ((W*L)*(∑ d ∈ Icc 1 A, F d))*(W*L) :=
      mul_le_mul_of_nonneg_right hs (mul_nonneg hW hL)
    _ = _ := by dsimp [W,L]; ring

def primeWindowResidueError (q : ℕ) (y h : ℝ) (r : (ZMod q)ˣ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (ShortAP.theta q (r : ZMod q) y h : ℂ) -
      ((h/(q.totient : ℝ) : ℝ) : ℂ)

theorem primeWindowCharacterError {q : ℕ} [NeZero q] (y h : ℝ)
    (χ : DirichletCharacter ℂ q) :
    unitCharacterError (primeWindowResidueError q y h) χ =
      ShortAP.centeredPrimeSum χ y h := by
  classical
  unfold unitCharacterError ShortAP.centeredPrimeSum
  simp only [primeWindowResidueError, dif_neg (NeZero.ne q), sub_mul, sum_sub_distrib]
  congr 1
  · rw [sum_units_eq_sum
      (fun r : ZMod q => (ShortAP.theta q r y h : ℂ)*χ r)
      (fun r hr => by rw [MulChar.map_nonunit χ hr, mul_zero])]
    simp only [ShortAP.theta, Complex.ofReal_sum, sum_filter]
    simp_rw [sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    simp
  · rw [← Finset.mul_sum, sum_char_units]
    by_cases hc : χ = 1
    · rw [if_pos hc, if_pos hc]
      push_cast
      have hφ : (q.totient : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
      field_simp
    · simp [hc]

def primitivePrimeWindowEnergy (d : ℕ) (y h : ℝ) : ℝ :=
  ∑ ψ ∈ primitiveCharacters d, ‖ShortAP.centeredPrimeSum ψ y h‖^2

theorem primeWindowReducedFamilyEnergy (A : ℕ) (y h : ℝ)
    (hy : (A : ℝ) ≤ y) (hh : 0 ≤ h) :
    (∑ q ∈ Icc 1 A, reducedLevelEnergy
      (fun q r => primeWindowResidueError q y h r) q) ≤
      (ShortAPLinearTotient.weightConstant*(1+Real.log A))^2 *
        ∑ d ∈ Icc 1 A, primitivePrimeWindowEnergy d y h := by
  apply reducedFamilyEnergyLog
  · intro d
    exact sum_nonneg fun _ _ => sq_nonneg _
  · intro q inst hq d hd
    have hqy : (q : ℝ) ≤ y := (by exact_mod_cast hq : (q : ℝ) ≤ A).trans hy
    simp only [primeWindowCharacterError, ShortAP.centeredPrimeSum_changeLevel hd _ hqy hh,
      primitivePrimeWindowEnergy, le_refl]

end
end InnerFloorResearch
