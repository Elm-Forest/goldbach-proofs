import Conjectures.Goldbach.InnerFloorPrincipalWindow
import Conjectures.Goldbach.InnerFloorPrimeWeightTransfer

/-! Principal prime window, without the nonprincipal zero-strip input. -/
open Finset Filter ArithmeticFunction
open scoped Classical Topology
open OAI.Ostmann V7e V2h GoldbachOC103
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem principalPrimePowerWindowError (χ : DirichletCharacter ℂ 1)
    {X y : ℝ} (h : ℕ) (hy : 0 ≤ y) (hX : y+(h:ℝ) ≤ X) :
    ‖V42 h y - InnerFloorAP.centeredPrimeSum χ y h‖ ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  have hχ : χ=1 := by
    ext1 r
    rw [show r=1 from Subsingleton.elim _ _]
    simp
  subst χ
  let s := V9a h y
  have hsub : s ⊆ Ioc 0 ⌊X⌋₊ := by
    intro k hk
    have hm : k∈Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ := by
      simpa only [s,windowIndices_eq y h hy] using hk
    have hk' := (InnerFloorAP.mem_window hy (Nat.cast_nonneg h) k).mp hm
    exact mem_Ioc.mpr ⟨by exact_mod_cast hy.trans_lt hk'.1,
      (Nat.le_floor_iff (by linarith [Nat.cast_nonneg (α := ℝ) h])).2 (hk'.2.trans hX)⟩
  have he := weightedPrimePowerError s X hsub (fun _ => 1) (by simp)
  have hval (k : ℕ) : (1 : DirichletCharacter ℂ 1) (k:ZMod 1)=1 := by
    rw [show (k:ZMod 1)=1 from Subsingleton.elim _ _]
    simp
  unfold V42 InnerFloorAP.centeredPrimeSum
  rw [if_pos rfl,← windowIndices_eq y h hy]
  simp only [hval,mul_one,V1n,sub_sub_sub_cancel_right]
  simpa only [s,mul_one,logPrimeWeight] using he

theorem principalPrimeWindowLogFour :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(4/5:ℝ) ≤ (h:ℝ) → (h:ℝ) ≤ X → ∀ χ : DirichletCharacter ℂ 1,
      ‖InnerFloorAP.centeredPrimeSum χ X h‖ ≤ C*(h:ℝ)/(Real.log X)^4 := by
  obtain ⟨C,hC,X₁,h₁⟩ := principalWindowLogFour
  obtain ⟨X₂,h₂⟩ := eventually_atTop.mp
    (eventually_power_log_bound (1/2) (4/5) 8 1 5 (by norm_num) (by norm_num))
  refine ⟨C+1,by positivity,max 2 (max X₁ X₂),le_max_left ..,?_⟩
  intro X hX h hh hhX χ
  have hX2 : 2≤X := (le_max_left _ _).trans hX
  have hX1 : X₁≤X := (le_max_left X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hX₂ : X₂≤X := (le_max_right X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hXp : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog : Real.log (2*X) ≤ 2*Real.log X := by
    rw [Real.log_mul (by norm_num) hXp.ne']
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 2) hX2]
  have hsqrt : Real.sqrt (2*X) ≤ 2*Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt 2 ≤ 2) (Real.sqrt_nonneg _)
  have hpow := (h₂ X hX₂).2
  have hsmall : 8*Real.sqrt X*Real.log X ≤ (h:ℝ)/(Real.log X)^4 := by
    apply (le_div_iff₀ (pow_pos hL 4)).2
    calc
      _ = 8*X^(1/2:ℝ)*(Real.log X)^5 := by rw [Real.sqrt_eq_rpow]; ring
      _ ≤ _ := (by simpa only [one_mul] using hpow : 8*X^(1/2:ℝ)*(Real.log X)^5 ≤ X^(4/5:ℝ)).trans hh
  have herr := principalPrimePowerWindowError χ (X := 2*X) h hXp.le (by linarith)
  have herror : ‖V42 h X-InnerFloorAP.centeredPrimeSum χ X h‖ ≤ (h:ℝ)/(Real.log X)^4 := by
    apply herr.trans
    apply (Chebyshev.psi_sub_theta_le (by linarith : 1 ≤ 2*X)).trans
    calc
      _ ≤ 2*(2*Real.sqrt X)*(2*Real.log X) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
        · exact hlog
        · exact Real.log_nonneg (by linarith)
        · positivity
      _ = 8*Real.sqrt X*Real.log X := by ring
      _ ≤ _ := hsmall
  have hnorm := norm_sub_le (V42 h X) (V42 h X-InnerFloorAP.centeredPrimeSum χ X h)
  rw [sub_sub_cancel] at hnorm
  calc
    _ ≤ _ := hnorm
    _ ≤ C*(h:ℝ)/(Real.log X)^4+(h:ℝ)/(Real.log X)^4 :=
      add_le_add (h₁ X hX1 h hh hhX) herror
    _ = _ := by ring

end
end InnerFloorResearch
