import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
Unconditional principal short-window estimate retaining logarithmic
saving rather than collapsing the bound to h/4. Adapted from the
accepted DyadicCellShortPrimeFloor, actual_principal_window_of_zero_weights,
pinned upstream 1fe24b28. No extra zero-free hypothesis.
-/
open Finset Filter
open scoped BigOperators Classical Topology
open OAI.Ostmann GoldbachOC103 Vx V7e V86 V1e V6i
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem principalWindowLogFour :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(4/5 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ C*(h : ℝ)/(Real.log X)^4 := by
  have hzero := actual_zero_weight_bounds
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets D C C hD.le
  obtain ⟨Xp,hXp⟩ := eventually_atTop.mp
    (eventually_power_log_bound (3/4) (4/5) 1 1 4 (by norm_num) (by norm_num))
  refine ⟨2*C+1,by positivity,max Xz (max Xb Xp),?_⟩
  intro X hX h hlower hupper
  have hbud := hb X ((le_max_left Xb Xp).trans ((le_max_right _ _).trans hX))
  have hX4 := hbud.scale_ge_four
  have hXpos : 0 < X := by linarith
  have hδ : 0 < X^(2/3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hV : 0 < X^(5/16 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  obtain ⟨hlo, hcount⟩ := hz X ((le_max_left _ _).trans hX) hX4
    hbud.log_ge_one hbud.split_ge_two hbud.split_le_scale
  let S := V3b X
  let A := S.filter (fun c => |c.val.1.im| ≤ X^(5/16 : ℝ))
  let R := S.filter (fun c => ¬ |c.val.1.im| ≤ X^(5/16 : ℝ))
  let K := C*(Real.log X)^14/(X^(5/16 : ℝ)*Real.sqrt (X^(5/16 : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : ∀ c ∈ S, |c.val.1.im| ≤ X := by
    intro c hc
    exact (V5l X c).mp hc
  have hlow : (∑ c ∈ A, X^(c.val.1.re-1)) ≤ C/(Real.log X)^4 :=
    hlo A (fun c hc => (mem_filter.mp hc).2)
  have hhigh : ∀ v : ℝ, X^(5/16 : ℝ) ≤ v →
      (∑ c ∈ R.filter (fun c => |c.val.1.im| ≤ v), X^(c.val.1.re-1)) ≤
        K*v*Real.sqrt v := by
    intro v hv
    exact weight_count_clamp R X (X^(5/16 : ℝ)) K v hV hbud.split_le_scale hK hv
      (fun c hc => hS c (mem_filter.mp hc).1) hcount
  have hpacket := smoothed_packet_of_weight_bounds S (fun c => c.val.1)
    X X h (X^(2/3 : ℝ)) (X^(5/16 : ℝ)) (C/(Real.log X)^4) K
    (by linarith) le_rfl (by linarith) hh hupper hδ hbud.smoothing_le_half hV hK
    (fun c _ => c.property.1.1) (fun c _ => c.property.1.2.1.le) hlow hhigh
  have hHighBudget :
      576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ))) ≤
        X^(3/4 : ℝ)/16 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    exact hbud.high_budget
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ ≤ X^(3/4 : ℝ)/16 := by
    exact hres.trans hbud.residual_budget
  have hnorm : ‖V42 h X‖ ≤
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ +
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ := by
    simpa only [add_sub_cancel_right] using
      norm_sub_le (V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
        (V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
  have hsmall := (hXp X ((le_max_right Xb Xp).trans ((le_max_right _ _).trans hX))).2
  have hlogp : 0 < Real.log X := by linarith [hbud.log_ge_one]
  have hsmall' : X^(3/4 : ℝ) ≤ (h:ℝ)/(Real.log X)^4 := by
    apply (le_div_iff₀ (pow_pos hlogp 4)).2
    have hs : X^(3/4 : ℝ)*(Real.log X)^4 ≤ X^(4/5 : ℝ) := by
      simpa only [one_mul] using hsmall
    exact hs.trans hlower
  calc
    _ ≤ X^(3/4 : ℝ)/16 +
      (2*(h:ℝ)*(C/(Real.log X)^4)+X^(3/4 : ℝ)/16) :=
      hnorm.trans (add_le_add hResidualBudget (hpacket.trans
        (add_le_add_right hHighBudget _)))
    _ ≤ _ := by
      linarith only [hsmall',div_nonneg hh (pow_nonneg hlogp.le 4),
        show (2*C+1)*(h:ℝ)/(Real.log X)^4 =
          2*(h:ℝ)*(C/(Real.log X)^4)+(h:ℝ)/(Real.log X)^4 by ring]

end
end InnerFloorResearch
