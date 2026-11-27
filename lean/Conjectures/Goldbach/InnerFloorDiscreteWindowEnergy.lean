import Conjectures.Goldbach.InnerFloorReducedGallagher

/-!
Integer-to-real window energy without any inequality loss.
Generic step integral adapted from GBSkirtVariance.paper_integral,
accepted LowSkirtFromShortProgressions at pinned upstream 1fe24b28.
-/
open Finset MeasureTheory
open scoped Classical Interval
namespace InnerFloorResearch
noncomputable section

theorem centeredPrimeSum_on_unit {d : ℕ}
    (χ : DirichletCharacter ℂ d) (k h : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ico (k:ℝ) ((k+1:ℕ):ℝ)) :
    InnerFloorAP.centeredPrimeSum χ y h =
      InnerFloorAP.centeredPrimeSum χ (k:ℝ) h := by
  have hy₀ := (Nat.cast_nonneg k (α:=ℝ)).trans hy.1
  have hk : ⌊y⌋₊=k := (Nat.floor_eq_iff hy₀).2 ⟨hy.1,by simpa using hy.2⟩
  simp only [InnerFloorAP.centeredPrimeSum,Nat.floor_add_natCast hy₀,
    hk,Nat.floor_natCast,Nat.floor_add_natCast (Nat.cast_nonneg (α:=ℝ) k)]

theorem primitivePrimeWindowEnergy_on_unit (d k h : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ico (k:ℝ) ((k+1:ℕ):ℝ)) :
    primitivePrimeWindowEnergy d y h = primitivePrimeWindowEnergy d k h := by
  unfold primitivePrimeWindowEnergy
  apply sum_congr rfl
  intro χ _
  rw [centeredPrimeSum_on_unit χ k h hy]

theorem integer_step_integral (x z : ℕ) (hxz : x≤z)
    (f : ℝ → ℝ) (g : ℕ → ℝ)
    (hstep : ∀ k : ℕ, ∀ y∈Set.Ico (k:ℝ) ((k+1:ℕ):ℝ), f y=g k) :
    (∫ y in (x:ℝ)..(z:ℝ), f y) = ∑ k∈Ico x z,g k := by
  let a (k : ℕ) := (k:ℝ)
  have hle (k : ℕ) : a k ≤ a (k+1) := by dsimp [a]; push_cast; linarith
  have hi (k : ℕ) : IntervalIntegrable f volume (a k) (a (k+1)) := by
    apply (intervalIntegrable_iff_integrableOn_Ico_of_le (hle k)).2
    have hc : IntegrableOn (fun _ : ℝ => g k) (Set.Ico (a k) (a (k+1))) volume :=
      (intervalIntegrable_iff_integrableOn_Ico_of_le (hle k)).1 intervalIntegrable_const
    apply hc.congr_fun _ measurableSet_Ico
    intro y hy
    exact (hstep k y hy).symm
  have he (k : ℕ) : (∫ y in a k..a (k+1), f y) = g k := by
    rw [intervalIntegral.integral_of_le (hle k), ← integral_Ico_eq_integral_Ioc]
    calc
      _ = ∫ _y in Set.Ico (a k) (a (k+1)), g k := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro y hy
        exact hstep k y hy
      _ = _ := by simp [a,Real.volume_Ico]
  have ht := intervalIntegral.sum_integral_adjacent_intervals_Ico (a:=a) (m:=x) (n:=z)
    hxz (fun k _ => hi k)
  exact ht.symm.trans (sum_congr rfl fun k _ => he k)

theorem primitiveFamilyIntegerEnergy (A h x z : ℕ) (hxz : x≤z) :
    (∑ k∈Ico x z, ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d k h) =
      ∫ y in (x:ℝ)..(z:ℝ), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h := by
  symm
  apply integer_step_integral x z hxz
  intro k y hy
  exact sum_congr rfl fun d _ => primitivePrimeWindowEnergy_on_unit d k h hy

end
end InnerFloorResearch
