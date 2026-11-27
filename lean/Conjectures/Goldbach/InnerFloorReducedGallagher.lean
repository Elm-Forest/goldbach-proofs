import Conjectures.Goldbach.LowSkirtFromShortProgressions
import Conjectures.Goldbach.InnerFloorConductorLift

/-!
Reduced-numerator Gallagher reduction. Unlike GBSkirtVariance.denominator_bound
this never sums over the nonunit numerators and never relaxes to q times the
full residue variance. The exact interior window is identified with the
verified conductor-lift estimate. The clipped endpoint windows are separate.
-/

open Finset MeasureTheory
open scoped Interval Classical
open GoldbachWindow (poly moving)
open GoldbachGRHAnalytic (errorCoeff)
open GoldbachGRHWindow (primeLog)
open Conjectures.Goldbach.ReflectionCharacterContraction_aux
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem reducedDenominatorBound {q : ℕ} [NeZero q] (n h : ℕ)
    (δ : ℝ) (hh : 0<h) (hd : 0≤δ) (hw : 6*(h:ℝ)*δ≤1) :
    (h:ℝ)^2/4 * (∑ a : (ZMod q)ˣ,
      ∫ t in -δ..δ, ‖poly (n+1) (errorCoeff (a:ZMod q)) t‖^2) ≤
      ∑ m∈range (n+1+h), ∑ a : (ZMod q)ˣ,
        ‖moving (n+1) h (errorCoeff (a:ZMod q)) m‖^2 := by
  rw [Finset.mul_sum,Finset.sum_comm (s := range (n+1+h))]
  exact sum_le_sum fun a _ =>
    GoldbachWindow.low_frequency_le (n+1) h (errorCoeff (a:ZMod q)) δ hh hd hw

theorem interiorWindowIndices (n y h : ℕ) (hfull : y+h≤n) :
    GBSkirtVariance.window n h (y+h) = Icc (y+1) (y+h) := by
  unfold GBSkirtVariance.window
  rw [min_eq_left hfull,show y+h+1-h=y+1 by omega]

theorem interiorResidueError_eq_zero {q : ℕ} [NeZero q]
    (n y h : ℕ) (hqy : q≤y) (hfull : y+h≤n)
    (r : ZMod q) (hr : ¬IsUnit r) :
    GBSkirtVariance.residueError (GBSkirtVariance.window n h (y+h)) primeLog r = 0 := by
  rw [interiorWindowIndices n y h hfull]
  unfold GBSkirtVariance.residueError
  rw [if_neg hr,sub_zero]
  change (∑ k ∈ (Icc (y+1) (y+h)).filter (fun k : ℕ => (k:ZMod q)=r),
    primeLog k)=0
  apply sum_eq_zero
  intro k hk
  obtain ⟨hk',hkr⟩ := mem_filter.mp hk
  have hqk : q<k := by have := (mem_Icc.mp hk').1; omega
  have hnp : ¬k.Prime := by
    intro hp
    have hcop : k.Coprime q := hp.coprime_iff_not_dvd.mpr
      (fun hd => (Nat.not_le_of_gt hqk) (Nat.le_of_dvd (NeZero.pos q) hd))
    exact hr (hkr ▸ (ZMod.isUnit_iff_coprime k q).mpr hcop)
  simp [primeLog,hnp]

theorem interiorResidueError_eq {q : ℕ} [NeZero q] (n y h : ℕ)
    (hfull : y+h≤n) (r : (ZMod q)ˣ) :
    GBSkirtVariance.residueError (GBSkirtVariance.window n h (y+h))
      primeLog (r:ZMod q) = primeWindowResidueError q y h r := by
  rw [interiorWindowIndices n y h hfull]
  unfold GBSkirtVariance.residueError
  change (∑ k ∈ (Icc (y+1) (y+h)).filter (fun k : ℕ => (k:ZMod q)=(r:ZMod q)),
    primeLog k) - (if IsUnit (r:ZMod q) then
      ((Icc (y+1) (y+h)).card:ℂ)/(q.totient:ℂ) else 0) =
    primeWindowResidueError q y h r
  simp only [r.isUnit,if_pos,primeWindowResidueError,dif_neg (NeZero.ne q),
    InnerFloorAP.theta,← Nat.cast_add,Nat.floor_natCast,Complex.ofReal_sum,
    Complex.ofReal_div,Complex.ofReal_natCast,primeLog]
  congr 1
  have hc : (Icc (y+1) (y+h)).card=h := by rw [Nat.card_Icc]; omega
  rw [hc]

theorem interiorMoving_eq_reduced {q : ℕ} [NeZero q] (n y h : ℕ)
    (hqy : q≤y) (hfull : y+h≤n) (a : (ZMod q)ˣ) :
    moving (n+1) h (errorCoeff (a:ZMod q)) (y+h) =
      unitAdditiveError (primeWindowResidueError q y h) a := by
  rw [GBSkirtVariance.moving_fourier]
  unfold unitAdditiveError
  rw [← sum_units_eq_sum
    (fun r : ZMod q => GBSkirtVariance.residueError
      (GBSkirtVariance.window n h (y+h)) primeLog r *
      ZMod.stdAddChar ((a:ZMod q)*r))
    (fun r hr => by rw [interiorResidueError_eq_zero n y h hqy hfull r hr,zero_mul])]
  exact sum_congr rfl fun r _ => by rw [interiorResidueError_eq n y h hfull]

def reducedMovingLevelEnergy (q n h m : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : (ZMod q)ˣ, ‖moving (n+1) h (errorCoeff (a:ZMod q)) m‖^2

/-- Full interior windows over any bounded family of levels satisfy the
same logarithmic conductor-lifting bound. No additional q factor. -/
theorem interiorReducedMovingFamilyEnergy (A n y h : ℕ)
    (hAy : A≤y) (hfull : y+h≤n) :
    (∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h (y+h)) ≤
      (InnerFloorLinearTotient.weightConstant*(1+Real.log A))^2 *
        ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h := by
  calc
    _ = ∑ q∈Icc 1 A, reducedLevelEnergy
      (fun q r => primeWindowResidueError q y h r) q := by
      apply sum_congr rfl
      intro q hq
      have hq0 : q≠0 := by have := (mem_Icc.mp hq).1; omega
      letI : NeZero q := ⟨hq0⟩
      simp only [reducedMovingLevelEnergy,reducedLevelEnergy,dif_neg hq0]
      apply sum_congr rfl
      intro a _
      rw [interiorMoving_eq_reduced n y h ((mem_Icc.mp hq).2.trans hAy) hfull]
    _ ≤ _ := primeWindowReducedFamilyEnergy A y h
      (by exact_mod_cast hAy) (Nat.cast_nonneg h)

end
end InnerFloorResearch
