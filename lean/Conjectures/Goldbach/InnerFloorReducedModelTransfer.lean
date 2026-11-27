import Conjectures.Goldbach.InnerFloorModelTransfer
import Conjectures.Goldbach.InnerFloorReducedGallagher

/-!
Exact reduced-numerator bridge for real-width model error. Allows an
independent window for each denominator band: 6 h u <= Q n.
The unit/numerator bijection is adapted from accepted
ShortProgressionsMeanTheta (XBribo #3789, pinned upstream 1fe24b28).
No analytic input is assumed beyond the already verified Gallagher
inequality. This replaces the earlier all-residue variance bound.
-/
open Finset MeasureTheory
open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHArcs (center)
open GoldbachGRHModel (model)
open scoped Classical Interval
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem inner_sum_units_eq_sum_coprime (q : ℕ) [NeZero q]
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ a : (ZMod q)ˣ, f ((a : ZMod q).val)) =
      ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), f a := by
  refine Finset.sum_bij (fun (a : (ZMod q)ˣ) _ => (a : ZMod q).val) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ hab
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (a : ZMod q), ← ZMod.natCast_zmod_val (b : ZMod q), hab]
  · intro a ha
    obtain ⟨haq, hac⟩ := Finset.mem_filter.mp ha
    have hu := (ZMod.isUnit_iff_coprime a q).mpr hac
    exact ⟨hu.unit, Finset.mem_univ _, by
      rw [hu.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp haq)]⟩
  · intro a _
    rfl

theorem middleEnergy_of_reducedWindow {n Q A h : ℕ} {u : ℝ} (hn : 0 < n)
    (hQ : 1 ≤ Q) (hh : 0 < h) (hu : 0 ≤ u) (hun : u ≤ n)
    (hwidth : 6*(h : ℝ)*u ≤ (Q:ℝ)*n) :
    (h : ℝ)^2 * mediumCellEnergy n Q A u ≤
      4 * ∑ q ∈ Ioc Q A, ∑ m∈range (n+1+h), reducedMovingLevelEnergy q n h m := by
  rw [mediumCellEnergy, sum_mediumIndices]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply sum_le_sum
  intro q hq
  have hq₂ : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
  have hq0 : 0 < q := by omega
  letI : NeZero q := ⟨hq0.ne'⟩
  let δ := realRadius n u q
  let E (a : ZMod q) : ℝ := ∫ β in -δ..δ,
    ‖GoldbachWindow.poly (n+1) (GoldbachGRHAnalytic.errorCoeff a) β‖^2
  have hd : 0 ≤ δ := by unfold δ realRadius; positivity
  have hw : 6*(h : ℝ)*δ ≤ 1 := by
    have hqR : (Q:ℝ) ≤ q := by exact_mod_cast (mem_Ioc.mp hq).1.le
    unfold δ realRadius
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (q : ℝ)*(n : ℝ)), one_mul]
    exact hwidth.trans (mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg n))
  have hE (a : ZMod q) : 0 ≤ E a :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hc (a : ℕ) (ha : a ∈ (range (q+1)).filter (fun a => a.Coprime q)) :
      (∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) = E (a : ZMod q) := by
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    have hUnit := (ZMod.isUnit_iff_coprime a q).2 hcop
    let G (β : ℝ) := ‖GoldbachWindow.poly (n+1)
      (GoldbachGRHAnalytic.errorCoeff (a : ZMod q)) β‖^2
    have he (t : ℝ) : G (t - center (q,a)) = ‖primeSum n t - model n (q,a) t‖^2 := by
      unfold G
      rw [GoldbachGRHAnalytic.shifted_error_eq, GoldbachGRHWindow.additiveModel_eq_moebius _ hUnit]
      unfold model
      rw [show (a : ℝ)/q+(t-center (q,a)) = t by unfold center; ring]
    calc
      _ = ∫ t in arcCell n u (q,a), G (t - center (q,a)) := by simp_rw [he]
      _ = E (a : ZMod q) :=
        arcCell_translate hn hu hun hq₂ (Nat.lt_succ_iff.mp (mem_range.mp haq)) hcop G
  have hR : (range (q+1)).filter (fun a => a.Coprime q) =
      (range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [mem_filter,mem_range]
    constructor
    · rintro ⟨ha,hc⟩
      refine ⟨?_,hc⟩
      by_contra! h
      have he : a=q := by omega
      subst a
      simp only [Nat.coprime_self] at hc
      omega
    · rintro ⟨ha,hc⟩
      exact ⟨by omega,hc⟩
  have hcells :
      (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
        ∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) =
        ∑ a : (ZMod q)ˣ, E (a:ZMod q) := by
    rw [sum_congr rfl hc,hR,← inner_sum_units_eq_sum_coprime q
      (fun a : ℕ => E (a:ZMod q))]
    simp only [ZMod.natCast_zmod_val]
  rw [hcells]
  have hden := reducedDenominatorBound (q := q) n h δ hh hd hw
  change (h:ℝ)^2/4*(∑ a : (ZMod q)ˣ,E (a:ZMod q)) ≤ _ at hden
  have he (m:ℕ) : reducedMovingLevelEnergy q n h m =
      ∑ a : (ZMod q)ˣ, ‖GoldbachWindow.moving (n+1) h
        (GoldbachGRHAnalytic.errorCoeff (a:ZMod q)) m‖^2 := by
    simp only [reducedMovingLevelEnergy,dif_neg hq0.ne']
  simp_rw [he]
  linarith only [hden]

end
end InnerFloorResearch
