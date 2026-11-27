import Conjectures.Goldbach.InnerFloorGoodZeroWindow

/-!
All-height, fixed-strip primitive-character window energy.
The near-one zeros are deliberately not discarded: the conclusions apply
to arbitrary subsets satisfying the stated real-part cutoff.
-/

open Finset Filter MeasureTheory
open scoped Interval Topology Classical
open OAI.Ostmann V1e V6b V6i
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def zeroWindow (χ : PrimitiveComplexCharacter) (S : Finset ℕ)
    (h y : ℝ) : ℂ :=
  ∑ i ∈ S, Ve y h ((V1 χ).zeros i)

/-- Sum all the dyadic bands in the strip 1/2 ≤ Re ρ ≤ 7/8.
The loss is at most (K+1)^2, for U=2^(K+1). -/
theorem rightStripAllHeights (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ),
      1 ≤ Q → X₀ ≤ X → 0 < h → h ≤ X →
      (Q : ℝ)^2/(h/X) ≤ X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1)) ≤ 2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ ∈ F, S χ ⊆ (V1 χ).V14 ((2 : ℝ)^(K+1))) →
      (∀ χ ∈ F, ∀ i ∈ S χ, 1/2 ≤ ((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re ≤ 7/8) →
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        C*((K+1 : ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
  obtain ⟨C₁,hC₁,X₁,h₁⟩ := fixedStripWindowBand B
  obtain ⟨C₂,hC₂,X₂,h₂⟩ := fixedStripWindowLow B
  let C := max C₁ C₂
  refine ⟨C, hC₁.trans_le (le_max_left ..), max (max X₁ X₂) 2,
    by linarith [le_max_right (max X₁ X₂) (2:ℝ)], ?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF S hS hstrip
  have hX1 := (le_max_left X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hX2 := (le_max_right X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hXp : 0 < X := by linarith [(le_max_right (max X₁ X₂) (2:ℝ)).trans hX]
  have hXge : 2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  let P (k : ℕ) (χ : PrimitiveComplexCharacter) :=
    Vpt (S χ) (fun i => ((V1 χ).zeros i).im) k
  have hpart (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) (y : ℝ) :
      zeroWindow χ (S χ) h y =
        ∑ k ∈ range (K+1), zeroWindow χ (P k χ) h y := by
    unfold zeroWindow
    apply V9u
    intro i hi
    exact (ComplexZeroEnumeration.V2r _ _ _).mp (hS χ hχ hi)
  have hpow (k : ℕ) (hk : k ∈ range (K+1)) :
      (2 : ℝ)^(k+1) ≤ 2^(K+1) :=
    pow_le_pow_right₀ (by norm_num) (by have := mem_range.mp hk; omega)
  have hT (k : ℕ) : (2 : ℝ) ≤ 2^(k+1) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ k+1 by omega))
  have hlogk (k : ℕ) (hk : k ∈ range (K+1)) :
      Real.log ((Q : ℝ)*2^(k+1)) ≤ 2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (hpow k hk) (Nat.cast_nonneg _)
  have hblock (k : ℕ) (hk : k ∈ range (K+1)) :
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
    by_cases hk0 : k = 0
    · subst k
      have h := h₂ Q hQ X h hX2 hh hhX hscale
        (by simpa using hlogk 0 hk) F hF (P 0)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,_⟩ := mem_filter.mp hi
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr
            (by simpa using hiT),hstrip χ hχ i hiS⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_right ..)
    · have h := h₁ Q hQ X h ((2:ℝ)^(k+1)) hX1 (hT k) hh hhX hscale
        (hlogk k hk) F hF (P k)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,hiL⟩ := mem_filter.mp hi
          have hL' := hiL.resolve_left hk0
          have he : (2:ℝ)^(k+1)/2 = 2^k := by rw [pow_succ]; ring
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr hiT,
            (hstrip χ hχ i hiS).1,(hstrip χ hχ i hiS).2,by rw [he]; exact hL'.le⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_left ..)
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      (∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
    simp_rw [hpart χ hχ]
    simpa only [card_range] using
      (V1dr (range (K+1)) (fun k y => zeroWindow χ (P k χ) h y) X hXp.le
        (fun k _ => ContinuousOn.intervalIntegrable_of_Icc (by linarith)
          ((V6e (P k χ) (V1 χ).zeros X h hXp hh.le hhX).norm.pow 2)))
  calc
    _ ≤ ∑ χ ∈ F, ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) :=
      sum_le_sum hterm
    _ = ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1), ∑ χ ∈ F,
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
      rw [← mul_sum, sum_comm]
    _ ≤ ((K+1 : ℕ):ℝ)*(∑ _k ∈ range (K+1), C*h^2*X/(Real.log X)^B) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hblock) (by positivity)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-- Sum all the dyadic bands in the strip 1/2 ≤ Re ρ ≤ 1 - V2j (B+4) X.
The loss is at most (K+1)^2, for U=2^(K+1). -/
theorem goodZerosAllHeights (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ),
      1 ≤ Q → X₀ ≤ X → 0 < h → h ≤ X →
      (Q : ℝ)^2/(h/X) ≤ X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1)) ≤ 2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ ∈ F, S χ ⊆ (V1 χ).V14 ((2 : ℝ)^(K+1))) →
      (∀ χ ∈ F, ∀ i ∈ S χ, 1/2 ≤ ((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re ≤ 1 - V1l.V2j (B+4) X) →
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        C*((K+1 : ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
  obtain ⟨C₁,hC₁,X₁,h₁⟩ := V93.Vz7 B
  obtain ⟨C₂,hC₂,X₂,h₂⟩ := V93.V1ep B
  let C := max C₁ C₂
  refine ⟨C, hC₁.trans_le (le_max_left ..), max (max X₁ X₂) 2,
    by linarith [le_max_right (max X₁ X₂) (2:ℝ)], ?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF S hS hstrip
  have hX1 := (le_max_left X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hX2 := (le_max_right X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hXp : 0 < X := by linarith [(le_max_right (max X₁ X₂) (2:ℝ)).trans hX]
  have hXge : 2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  let P (k : ℕ) (χ : PrimitiveComplexCharacter) :=
    Vpt (S χ) (fun i => ((V1 χ).zeros i).im) k
  have hpart (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) (y : ℝ) :
      zeroWindow χ (S χ) h y =
        ∑ k ∈ range (K+1), zeroWindow χ (P k χ) h y := by
    unfold zeroWindow
    apply V9u
    intro i hi
    exact (ComplexZeroEnumeration.V2r _ _ _).mp (hS χ hχ hi)
  have hpow (k : ℕ) (hk : k ∈ range (K+1)) :
      (2 : ℝ)^(k+1) ≤ 2^(K+1) :=
    pow_le_pow_right₀ (by norm_num) (by have := mem_range.mp hk; omega)
  have hT (k : ℕ) : (2 : ℝ) ≤ 2^(k+1) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ k+1 by omega))
  have hlogk (k : ℕ) (hk : k ∈ range (K+1)) :
      Real.log ((Q : ℝ)*2^(k+1)) ≤ 2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (hpow k hk) (Nat.cast_nonneg _)
  have hblock (k : ℕ) (hk : k ∈ range (K+1)) :
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
    by_cases hk0 : k = 0
    · subst k
      have h := h₂ Q hQ X h hX2 hh hhX hscale
        (by simpa using hlogk 0 hk) F hF (P 0)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,_⟩ := mem_filter.mp hi
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr
            (by simpa using hiT),hstrip χ hχ i hiS⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_right ..)
    · have h := h₁ Q hQ X h ((2:ℝ)^(k+1)) hX1 (hT k) hh hhX hscale
        (hlogk k hk) F hF (P k)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,hiL⟩ := mem_filter.mp hi
          have hL' := hiL.resolve_left hk0
          have he : (2:ℝ)^(k+1)/2 = 2^k := by rw [pow_succ]; ring
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr hiT,
            (hstrip χ hχ i hiS).1,(hstrip χ hχ i hiS).2,by rw [he]; exact hL'.le⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_left ..)
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      (∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
    simp_rw [hpart χ hχ]
    simpa only [card_range] using
      (V1dr (range (K+1)) (fun k y => zeroWindow χ (P k χ) h y) X hXp.le
        (fun k _ => ContinuousOn.intervalIntegrable_of_Icc (by linarith)
          ((V6e (P k χ) (V1 χ).zeros X h hXp hh.le hhX).norm.pow 2)))
  calc
    _ ≤ ∑ χ ∈ F, ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) :=
      sum_le_sum hterm
    _ = ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1), ∑ χ ∈ F,
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
      rw [← mul_sum, sum_comm]
    _ ≤ ((K+1 : ℕ):ℝ)*(∑ _k ∈ range (K+1), C*h^2*X/(Real.log X)^B) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hblock) (by positivity)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-- Moving-average smoothing does not increase energy beyond the
slightly enlarged physical interval. -/
theorem smoothedWindowEnergy
    (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) {X h δ : ℝ}
    (hX : 0 < X) (hh : 0 ≤ h) (hhX : h ≤ X/2)
    (hδ : 0 < δ) (hδX : δ ≤ X/2) :
    (∑ χ ∈ F, ∫ y in X..2*X, ‖V3q (zeroWindow χ (S χ) h) δ y‖^2) ≤
      (∑ χ ∈ F, ∫ y in X/2..X, ‖zeroWindow χ (S χ) h y‖^2) +
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) := by
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro χ _
  let f := zeroWindow χ (S χ) h
  have hcont : ContinuousOn f (Set.Icc (X/2) (2*X)) := by
    unfold f zeroWindow
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hpos : y+h ≠ 0 := by linarith [hy.1]
      have hc : ContinuousAt (fun t : ℝ => t+h) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t : ℝ => ((t+h:ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+h) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+h) ((V1 χ).zeros i) (Or.inr hpos)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y ≠ 0))).continuousWithinAt
  have hsub : Set.Icc (X-δ) (2*X) ⊆ Set.Icc (X/2) (2*X) :=
    Set.Icc_subset_Icc (by linarith) le_rfl
  apply (V1qh f X δ hX.le hδ (hcont.mono hsub)).trans
  have hint : IntervalIntegrable (fun y => ‖f y‖^2) volume (X/2) (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hcont.norm.pow 2)
  calc
    _ ≤ ∫ u in X/2..2*X, ‖f u‖^2 :=
      intervalIntegral.integral_mono_interval (by linarith) (by linarith)
        le_rfl (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hint
    _ = _ := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hint.mono_set (by rw [Set.uIcc_of_le (by linarith : X/2≤X),
          Set.uIcc_of_le (by linarith : X/2≤2*X)]; exact Set.Icc_subset_Icc le_rfl (by linarith)))
        (hint.mono_set (by rw [Set.uIcc_of_le (by linarith : X≤2*X),
          Set.uIcc_of_le (by linarith : X/2≤2*X)]; exact Set.Icc_subset_Icc (by linarith) le_rfl))]

end
end InnerFloorResearch
