import Conjectures.Goldbach.InnerFloorArithmeticCore
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
Transfer from von Mangoldt windows to logarithmic prime windows, preserving
the character index and family squared-energy budget. This is independent
of zero-free assumptions and does not assert a bound on the zero sum.
-/

open Finset ArithmeticFunction MeasureTheory
open scoped Interval Classical
open OAI.Ostmann V7e V2h
namespace InnerFloorResearch
noncomputable section

def logPrimeWeight (k : ℕ) : ℝ :=
  if k.Prime then Real.log k else 0

theorem logPrimeWeight_le_vonMangoldt (k : ℕ) :
    logPrimeWeight k ≤ vonMangoldt k := by
  by_cases hk : k.Prime
  · simp [logPrimeWeight,hk,vonMangoldt_apply_prime hk]
  · simp [logPrimeWeight,hk]

/-- An arbitrary bounded multiplier cannot amplify the total proper
prime-power mass on any subset of the prefix. -/
theorem weightedPrimePowerError (s : Finset ℕ) (X : ℝ)
    (hsub : s ⊆ Ioc 0 ⌊X⌋₊) (a : ℕ → ℂ)
    (ha : ∀ k ∈ s, ‖a k‖ ≤ 1) :
    ‖(∑ k∈s, (vonMangoldt k:ℂ)*a k) -
      (∑ k∈s, (logPrimeWeight k:ℂ)*a k)‖ ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  have htotal :
      (∑ k∈Ioc 0 ⌊X⌋₊, (vonMangoldt k-logPrimeWeight k)) =
        Chebyshev.psi X-Chebyshev.theta X := by
    simp only [sum_sub_distrib,Chebyshev.psi,Chebyshev.theta,sum_filter,logPrimeWeight]
  rw [← sum_sub_distrib,← htotal]
  calc
    _ ≤ ∑ k∈s, ‖(vonMangoldt k:ℂ)*a k-(logPrimeWeight k:ℂ)*a k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k∈s, (vonMangoldt k-logPrimeWeight k) := by
      apply sum_le_sum
      intro k hk
      rw [← sub_mul,← Complex.ofReal_sub,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr (logPrimeWeight_le_vonMangoldt k))]
      exact mul_le_of_le_one_right (sub_nonneg.mpr (logPrimeWeight_le_vonMangoldt k)) (ha k hk)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => sub_nonneg.mpr (logPrimeWeight_le_vonMangoldt k))

/-- Exact identification of the floor-based integer-length window. -/
theorem windowIndices_eq (y : ℝ) (h : ℕ) (hy : 0 ≤ y) :
    V9a h y = Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ := by
  rw [V9a,Nat.floor_add_natCast hy h]
  ext k
  simp only [mem_Ioc,mem_Icc,Nat.add_one_le_iff]

theorem centeredPrimeWindowError (χ : PrimitiveComplexCharacter)
    {X y : ℝ} (h : ℕ) (hy : 0 ≤ y) (hX : y+(h:ℝ) ≤ X) :
    ‖V4q χ h y - InnerFloorAP.centeredPrimeSum χ.character y h‖ ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  let s := V9a h y
  have hsub : s ⊆ Ioc 0 ⌊X⌋₊ := by
    intro k hk
    have hm : k∈Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ := by
      simpa only [s,windowIndices_eq y h hy] using hk
    have hk' := (InnerFloorAP.mem_window hy (Nat.cast_nonneg h) k).mp hm
    exact mem_Ioc.mpr ⟨by exact_mod_cast hy.trans_lt hk'.1,
      (Nat.le_floor_iff (by linarith [Nat.cast_nonneg (α := ℝ) h])).2 (hk'.2.trans hX)⟩
  have he := weightedPrimePowerError s X hsub
    (fun k => χ.character (k:ZMod χ.modulus))
    (fun k _ => DirichletCharacter.norm_le_one _ _)
  unfold V4q InnerFloorAP.centeredPrimeSum
  rw [if_neg χ.nontrivial,sub_zero,← windowIndices_eq y h hy]
  simp only [Vl,mul_comm (χ.character _),logPrimeWeight] at he ⊢
  exact he

/-- The family error is at most O(Q² X² log² X) on [X,2X],
using the uniform proper-prime-power mass bound and the primitive
character cardinality estimate. -/
theorem primitivePrimeWindowErrorEnergy (F : Finset PrimitiveComplexCharacter)
    (Q h : ℕ) {X : ℝ} (hX : 1≤X) (hh : (h:ℝ)≤X)
    (hF : ∀ χ∈F, χ.modulus≤Q) :
    (∑ χ∈F, ∫ y in X..2*X,
      ‖V4q χ h y-InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
      X*(Q:ℝ)^2*(2*Real.sqrt (3*X)*Real.log (3*X))^2 := by
  let M := 2*Real.sqrt (3*X)*Real.log (3*X)
  have hM : 0≤M := by
    have hl : 0≤Real.log (3*X) := Real.log_nonneg (by linarith)
    dsimp [M]
    positivity
  have hterm (χ : PrimitiveComplexCharacter) :
      (∫ y in X..2*X, ‖V4q χ h y-InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        X*M^2 := by
    have hXX : X≤2*X := by linarith
    rw [intervalIntegral.integral_of_le hXX]
    have hb : ∀ y∈Set.Ioc X (2*X),
        ‖V4q χ h y-InnerFloorAP.centeredPrimeSum χ.character y h‖^2≤M^2 := by
      intro y hy
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      exact (centeredPrimeWindowError χ h (by linarith [hy.1])
        (by linarith [hy.2])).trans (Chebyshev.psi_sub_theta_le (by linarith))
    calc
      _ ≤ ∫ _y in Set.Ioc X (2*X), M^2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
          (integrableOn_const (by simp)) (by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
            exact hb y hy)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hXX,intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  calc
    _ ≤ ∑ _χ∈F, X*M^2 := sum_le_sum fun χ _ => hterm χ
    _ = (F.card:ℝ)*(X*M^2) := by simp [nsmul_eq_mul]
    _ ≤ _ := by
      have hc : (F.card:ℝ)≤(Q:ℝ)^2 := by exact_mod_cast V14i F Q hF
      have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0≤X*M^2)
      dsimp [M] at *
      nlinarith only [hm]

end
end InnerFloorResearch
