import Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion

/-!
Alternative direct reduction to the explicit canonical zero correction.
The accepted rational_canonical_model estimate is sufficient to make its
remaining analytic error negligible on all medium-width arcs. This leaves
the actual signed zero correction; it does not assert its negligibility.
-/

open Finset Filter MeasureTheory DeepThreeQuarters GoldbachTwistedMellin
open scoped Interval Topology Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem canonicalResidualPointwise (η : ℝ) (hη : 0<η) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n →
      ∀ (a q : ℕ) [NeZero q], a.Coprime q → (q:ℝ)≤Real.sqrt n →
      ∀ β : ℝ, |β|≤1/((q:ℝ)*Real.sqrt n) →
      ‖weightedSum n primeWeight ((a:ℝ)/q+β)-rationalModel n q β+
        canonicalCorrection n (a:ZMod q) β‖ ≤ (n:ℝ)^(3/4+η) := by
  let d := min (η/8) (1/8)
  have hd : 0<d := lt_min (by positivity) (by norm_num)
  have hd' : d≤1/8 := min_le_right .. 
  have hde : d≤η/8 := min_le_left ..
  obtain ⟨K,hK,hbound⟩ := rational_canonical_model hd hd'
  obtain ⟨D,hD,hlog⟩ := quartic_log_scale (show 0<η/4 by positivity)
  obtain ⟨P,hP⟩ := eventually_atTop.mp (eventually_absorb (K*D) η hη)
  refine ⟨max 64 P,?_⟩
  intro n hn a q _ ha hq β hβ
  have hn64 : 64≤n := (le_max_left _ _).trans hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hnp : (0:ℝ)<n := by linarith
  calc
    _ ≤ K*(n:ℝ)^(3/4+2*d)*logScale n^4 := hbound n hn64 a q ha hq β hβ
    _ ≤ K*(n:ℝ)^(3/4+2*d)*(D*(n:ℝ)^(η/4)) :=
      mul_le_mul_of_nonneg_left (hlog n hn1) (by positivity)
    _ = K*D*(n:ℝ)^(3/4+2*d+η/4) := by
      rw [Real.rpow_add hnp (3/4+2*d) (η/4)]
      ring
    _ ≤ K*D*(n:ℝ)^(3/4+η/2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
        (by positivity)
    _ ≤ _ := hP n ((le_max_right _ _).trans hn)

/-- Summed energy of the per-cell residual, bounded without any prime
distribution input by the total arc length times the squared uniform bound. -/
theorem summedArcResidualEnergy
    (n A : ℕ) (u E : ℝ) (hn : 0<n) (hu : 0≤u) (hE : 0≤E)
    (F : ℕ → ℕ → ℝ → ℂ)
    (hF : ∀ q∈Icc 1 A, ∀ a∈range (q+1), a.Coprime q →
      ∀ β∈Set.Icc (-u/((q:ℝ)*n)) (u/((q:ℝ)*n)), ‖F q a β‖≤E) :
    (∑ q∈Icc 1 A, ∑ a∈(range (q+1)).filter (fun a => a.Coprime q),
      ∫ β in -(u/((q:ℝ)*n))..u/((q:ℝ)*n), ‖F q a β‖^2) ≤
      4*u*(A:ℝ)/n*E^2 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hqTerm (q : ℕ) (hq : q∈Icc 1 A) :
      (∑ a∈(range (q+1)).filter (fun a => a.Coprime q),
        ∫ β in -(u/((q:ℝ)*n))..u/((q:ℝ)*n), ‖F q a β‖^2) ≤
        4*u/n*E^2 := by
    let R := u/((q:ℝ)*n)
    have hq1 : (1:ℝ)≤q := by exact_mod_cast (mem_Icc.mp hq).1
    have hqp : (0:ℝ)<q := by linarith
    have hR : 0≤R := by dsimp [R]; positivity
    have hterm (a : ℕ) (ha : a∈(range (q+1)).filter (fun a => a.Coprime q)) :
        (∫ β in -R..R, ‖F q a β‖^2) ≤ (2*R)*E^2 := by
      rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
      calc
        _ ≤ ∫ _β in Set.Ioc (-R) R, E^2 := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
            (integrableOn_const (by simp))
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with β hβ
          exact pow_le_pow_left₀ (norm_nonneg _) (hF q hq a
            (mem_filter.mp ha).1 (mem_filter.mp ha).2 β ⟨hβ.1.le,hβ.2⟩) 2
        _ = _ := by
          rw [← intervalIntegral.integral_of_le (by linarith : -R≤R),
            intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
    have hc : (((range (q+1)).filter (fun a => a.Coprime q)).card:ℝ) ≤ 2*q := by
      have hc0 := card_le_card (filter_subset (fun a => a.Coprime q) (range (q+1)))
      rw [card_range] at hc0
      have hc1 : (((range (q+1)).filter (fun a => a.Coprime q)).card:ℝ) ≤ q+1 := by
        exact_mod_cast hc0
      linarith
    calc
      _ ≤ ∑ a∈(range (q+1)).filter (fun a => a.Coprime q), (2*R)*E^2 :=
        sum_le_sum hterm
      _ = (((range (q+1)).filter (fun a => a.Coprime q)).card:ℝ)*((2*R)*E^2) := by
        simp [nsmul_eq_mul]
      _ ≤ (2*(q:ℝ))*((2*R)*E^2) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by dsimp [R]; field_simp; ring
  calc
    _ ≤ ∑ _q∈Icc 1 A, 4*u/n*E^2 := sum_le_sum hqTerm
    _ = _ := by simp [Nat.card_Icc,nsmul_eq_mul]; ring

/-- Exponent reserve for the canonical residual: u≤n^(1/6+.01),
A≤n^(.2), pointwise residual≤n^(3/4+.01). -/
theorem canonicalResidualExponent :
    2*((3:ℝ)/4+1/100)+(1/6+1/100)+1/5-1 ≤ 9/10 := by norm_num

end
end InnerFloorResearch
