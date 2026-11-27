import Conjectures.Goldbach.InnerFloorProductFamily
import Conjectures.Goldbach.InnerFloorReducedGallagher

/-!
Uniform energy of a clipped interval, with no prime distribution input.
The centered model term costs only reciprocal totients. This is used
on boundary windows of length at most h rather than on the full bulk.
-/
open Finset BombieriVinogradov.LargeSieve InnerFloorLinearTotient
open GoldbachGRHWindow (additiveModel)
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem additiveIntervalFamilyEnergy (A N : ℕ) (M : ℤ)
    (a : ℤ → ℂ) (hA : 0 < A) (W : ℝ) (hW : 0 ≤ W)
    (ha : ∀ k∈range N, ‖shiftedIntervalCoefficients a M k‖ ≤ W) :
    (∑ q∈Icc 1 A,modulusAdditiveEnergy a M N q) ≤
      64*((N:ℝ)+(A:ℝ)^2)*(N:ℝ)*W^2 := by
  rw [sum_modulusAdditiveEnergy_eq_fareySamples]
  apply (additiveLargeSieve hA (shiftedIntervalCoefficients a M)).trans
  have hs : (∑ k∈range N, ‖shiftedIntervalCoefficients a M k‖^2) ≤
      (N:ℝ)*W^2 := by
    calc
      _ ≤ ∑ _k∈range N,W^2 :=
        sum_le_sum fun k hk => pow_le_pow_left₀ (norm_nonneg _) (ha k hk) 2
      _ = _ := by simp [nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

theorem sum_unitModelEnergy (q : ℕ) [NeZero q] :
    (∑ u : (ZMod q)ˣ, ‖additiveModel q (u:ZMod q)‖^2) ≤
      1/(q.totient:ℝ) := by
  have hφ : 0 < (q.totient:ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hterm (u : (ZMod q)ˣ) : ‖additiveModel q (u:ZMod q)‖ ≤
      1/(q.totient:ℝ) := by
    rw [GoldbachGRHWindow.additiveModel_eq_moebius _ u.isUnit,norm_div,
      Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (DyadicMixedB4MoebiusGauss.norm_moebiusComplex_le_one q)
      hφ.le
  calc
    _ ≤ ∑ _u : (ZMod q)ˣ, (1/(q.totient:ℝ))^2 :=
      sum_le_sum fun u _ => pow_le_pow_left₀ (norm_nonneg _) (hterm u) 2
    _ = _ := by
      rw [sum_const,nsmul_eq_mul,card_univ,ZMod.card_units_eq_totient]
      field_simp

def centeredIntervalEnergy (a : ℤ → ℂ) (M : ℤ) (N q : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u -
      (N:ℂ)*additiveModel q (u:ZMod q)‖^2

theorem centeredIntervalEnergy_le (a : ℤ → ℂ) (M : ℤ) (N q : ℕ)
    (hq : 0 < q) :
    centeredIntervalEnergy a M N q ≤
      2*modulusAdditiveEnergy a M N q+2*(N:ℝ)^2/(q.totient:ℝ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [modulusAdditiveEnergy_eq]
  simp only [centeredIntervalEnergy,dif_neg hq.ne']
  have hterm (u : (ZMod q)ˣ) :
      ‖intervalAdditiveResidueSum a M N q u -
        (N:ℂ)*additiveModel q (u:ZMod q)‖^2 ≤
        2*‖intervalAdditiveResidueSum a M N q u‖^2+
        2*(N:ℝ)^2*‖additiveModel q (u:ZMod q)‖^2 := by
    have hs := norm_sub_le (intervalAdditiveResidueSum a M N q u)
      ((N:ℂ)*additiveModel q (u:ZMod q))
    rw [norm_mul,Complex.norm_natCast] at hs
    exact (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans
      (by
        have H := sq_nonneg (‖intervalAdditiveResidueSum a M N q u‖ -
          (N:ℝ)*‖additiveModel q (u:ZMod q)‖)
        nlinarith only [H])
  calc
    _ ≤ ∑ u : (ZMod q)ˣ, (2*‖intervalAdditiveResidueSum a M N q u‖^2+
        2*(N:ℝ)^2*‖additiveModel q (u:ZMod q)‖^2) := sum_le_sum fun u _ => hterm u
    _ = 2*(∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖^2)+
        2*(N:ℝ)^2*(∑ u : (ZMod q)ˣ, ‖additiveModel q (u:ZMod q)‖^2) := by
      rw [sum_add_distrib,← mul_sum,← mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sum_unitModelEnergy q)
        (show (0:ℝ) ≤ 2*(N:ℝ)^2 from by positivity)
      calc
        _ ≤ 2*(∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖^2)+
            2*(N:ℝ)^2*(1/(q.totient:ℝ)) := add_le_add le_rfl h
        _ = _ := by ring_nf <;> ac_rfl

/-- For any interval of N terms, the total centered reduced numerator
energy has at most a quadratic logarithmic model cost. -/
theorem centeredIntervalFamilyEnergy (A N : ℕ) (M : ℤ)
    (a : ℤ → ℂ) (hA : 0 < A) (W : ℝ) (hW : 0 ≤ W)
    (ha : ∀ k∈range N, ‖shiftedIntervalCoefficients a M k‖ ≤ W) :
    (∑ q∈Icc 1 A,centeredIntervalEnergy a M N q) ≤
      128*((N:ℝ)+(A:ℝ)^2)*(N:ℝ)*W^2+
      2*(N:ℝ)^2*(weightConstant*(1+Real.log A))^2 := by
  have hr := commonMultipleTotientWeight A 1 (by decide) hA
  simp only [one_dvd,filter_true,Nat.cast_one] at hr
  calc
    _ ≤ ∑ q∈Icc 1 A, (2*modulusAdditiveEnergy a M N q+2*(N:ℝ)^2/(q.totient:ℝ)) :=
      sum_le_sum fun q hq => centeredIntervalEnergy_le a M N q (mem_Icc.mp hq).1
    _ = 2*(∑ q∈Icc 1 A,modulusAdditiveEnergy a M N q)+
      2*(N:ℝ)^2*(∑ q∈Icc 1 A,1/(q.totient:ℝ)) := by
      rw [sum_add_distrib,← mul_sum]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left
        (additiveIntervalFamilyEnergy A N M a hA W hW ha) (by norm_num : (0:ℝ)≤2)
      have h2 := mul_le_mul_of_nonneg_left hr (by positivity : 0≤2*(N:ℝ)^2)
      linarith only [h1,h2]

end
end InnerFloorResearch
