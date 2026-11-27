import Conjectures.Goldbach.InnerFloorGeometry
import Conjectures.Goldbach.LowSkirtFromShortProgressions

open Finset MeasureTheory Filter
open scoped Interval Topology Classical

namespace InnerFloorResearch

noncomputable section
set_option maxHeartbeats 1500000

open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHArcs (center centers mem_centers)
open GoldbachGRHApproximation (integrand)
open GoldbachGRHModel (model model_continuous)

def realRadius (n : ℕ) (u : ℝ) (q : ℕ) : ℝ := u / ((q : ℝ) * (n : ℝ))

def realArc (n : ℕ) (u : ℝ) (i : ℕ × ℕ) : Set ℝ :=
  {t | |t - center i| ≤ realRadius n u i.1}

theorem realArc_eq_Icc (n : ℕ) (u : ℝ) (i : ℕ × ℕ) :
    realArc n u i =
      Set.Icc (center i - realRadius n u i.1) (center i + realRadius n u i.1) := by
  ext t
  change |t - center i| ≤ _ ↔ _
  rw [abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

def mediumIndices (Q A : ℕ) : Finset (ℕ × ℕ) :=
  (centers A).filter (fun i => Q < i.1)

theorem mediumIndices_spec {Q A : ℕ} {i : ℕ × ℕ} :
    i ∈ mediumIndices Q A ↔ Q < i.1 ∧ i.1 ≤ A ∧ i.2 ≤ i.1 ∧ i.2.Coprime i.1 := by
  simp only [mediumIndices, mem_filter, mem_centers]
  constructor
  · rintro ⟨⟨_, hA, ha, hc⟩, hQ⟩
    exact ⟨hQ, hA, ha, hc⟩
  · rintro ⟨hQ, hA, ha, hc⟩
    exact ⟨⟨by omega, hA, ha, hc⟩, hQ⟩

theorem mediumBand_eq_union (n Q A : ℕ) (u : ℝ) :
    mediumBand Q A u n = ⋃ i ∈ mediumIndices Q A, realArc n u i := by
  ext t
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨q,a,hQ,_,hA,ha,hc,ht⟩
    exact ⟨(q,a), mediumIndices_spec.mpr ⟨hQ,hA,ha,hc⟩, ht⟩
  · rintro ⟨⟨q,a⟩,hi,ht⟩
    obtain ⟨hQ,hA,ha,hc⟩ := mediumIndices_spec.mp hi
    exact ⟨q,a,hQ,by omega,hA,ha,hc,ht⟩

theorem measurable_mediumBand (n Q A : ℕ) (u : ℝ) :
    MeasurableSet (mediumBand Q A u n) := by
  rw [mediumBand_eq_union]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => by
    rw [realArc_eq_Icc]
    exact measurableSet_Icc

def arcCell (n : ℕ) (u : ℝ) (i : ℕ × ℕ) : Set ℝ := realArc n u i ∩ Set.Ioc 0 1

theorem measurable_arcCell (n : ℕ) (u : ℝ) (i : ℕ × ℕ) :
    MeasurableSet (arcCell n u i) := by
  unfold arcCell
  rw [realArc_eq_Icc]
  exact measurableSet_Icc.inter measurableSet_Ioc

theorem arcCells_disjoint {n Q A : ℕ} {u : ℝ} (hn : 0 < n) (hu : 0 ≤ u)
    (hsep : 2*u*(A : ℝ) < (n : ℝ)) :
    (↑(mediumIndices Q A) : Set (ℕ × ℕ)).PairwiseDisjoint (arcCell n u) := by
  rintro ⟨q,a⟩ hi ⟨r,b⟩ hj hij
  change Disjoint (arcCell n u (q,a)) (arcCell n u (r,b))
  rw [Set.disjoint_left]
  intro t ht ht'
  obtain ⟨hq,hqA,_,hc⟩ := mediumIndices_spec.mp (show (q,a) ∈ mediumIndices Q A from hi)
  obtain ⟨hr,hrA,_,hd⟩ := mediumIndices_spec.mp (show (r,b) ∈ mediumIndices Q A from hj)
  obtain ⟨hqr,hab⟩ := mediumBand_unique Q A u (n : ℝ) hu (by exact_mod_cast hn)
    hsep hq hr hqA hrA hc hd ht.1 ht'.1
  exact hij (Prod.ext hqr hab)

/-- Interior centers yield the full symmetric beta-window. The singleton
at zero does not contribute to the integral. -/
theorem arcCell_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n q a : ℕ} {u : ℝ} (hn : 0 < n) (hu : 0 ≤ u) (hun : u ≤ n)
    (hq : 2 ≤ q) (ha : a ≤ q) (hc : a.Coprime q) (G : ℝ → E) :
    (∫ t in arcCell n u (q,a), G (t - center (q,a))) =
      ∫ t in -(realRadius n u q)..(realRadius n u q), G t := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha0 : 1 ≤ a := by
    by_contra! h
    have he : a = 0 := by omega
    have h1 := (Nat.coprime_zero_left q).mp (he ▸ hc)
    omega
  have haq : a + 1 ≤ q := by
    by_contra! h
    have he : a = q := by omega
    have h1 : q = 1 := by simpa [he, Nat.Coprime] using hc
    omega
  have hrad : 0 ≤ realRadius n u q := div_nonneg hu (mul_pos hqR hnR).le
  have hr : realRadius n u q ≤ 1/(q : ℝ) := by
    apply (div_le_iff₀ (mul_pos hqR hnR)).2
    convert hun using 1
    field_simp
  have hleft : realRadius n u q ≤ center (q,a) :=
    hr.trans (div_le_div_of_nonneg_right (by exact_mod_cast ha0) hqR.le)
  have hright : center (q,a) + realRadius n u q ≤ 1 := by
    apply (add_le_add_right hr _).trans
    change (a : ℝ)/q + 1/(q : ℝ) ≤ 1
    rw [← add_div, div_le_one hqR]
    exact_mod_cast haq
  have hsub : realArc n u (q,a) ⊆ Set.Icc 0 1 := by
    rw [realArc_eq_Icc]
    exact Set.Icc_subset_Icc (sub_nonneg.mpr hleft) hright
  have he : arcCell n u (q,a) =ᵐ[volume] realArc n u (q,a) := by
    have h : Set.Ioc (0 : ℝ) 1 =ᵐ[volume] Set.Icc (0 : ℝ) 1 := Ioc_ae_eq_Icc
    filter_upwards [h] with t ht
    change (t ∈ realArc n u (q,a) ∧ t ∈ Set.Ioc 0 1) ↔ t ∈ realArc n u (q,a)
    exact ⟨And.left, fun hp => ⟨hp, ht.mpr (hsub hp)⟩⟩
  have hInt :
      (∫ t in arcCell n u (q,a), G (t - center (q,a))) =
        ∫ t in realArc n u (q,a), G (t - center (q,a)) :=
    setIntegral_congr_set he
  rw [hInt,
    realArc_eq_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hrad] :
      center (q,a) - realRadius n u q ≤ center (q,a) + realRadius n u q),
    intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

theorem sum_mediumIndices {E : Type*} [AddCommMonoid E] (Q A : ℕ)
    (F : ℕ × ℕ → E) :
    (∑ i ∈ mediumIndices Q A, F i) =
      ∑ q ∈ Ioc Q A, ∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q), F (q,a) := by
  have he : (Icc 1 A).filter (fun q => Q < q) = Ioc Q A := by
    ext q
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [mediumIndices, sum_filter, GoldbachGRHArcs.sum_centers_eq, ← he]
  conv_rhs => rw [sum_filter]
  apply sum_congr rfl
  intro q hq
  by_cases h : Q < q <;> simp [h]

def mediumIntegral (n Q A : ℕ) (u : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (mediumBand Q A u n).indicator (integrand n) t

def mediumModel (n Q A : ℕ) (u : ℝ) : ℂ :=
  ∑ i ∈ mediumIndices Q A, ∫ t in arcCell n u i, model n i t ^ 2 * phase (-(n : ℝ)*t)

def mediumCellEnergy (n Q A : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ mediumIndices Q A, ∫ t in arcCell n u i, ‖primeSum n t - model n i t‖^2

theorem mediumIntegral_eq_sum {n Q A : ℕ} {u : ℝ} (hn : 0 < n) (hu : 0 ≤ u)
    (hsep : 2*u*(A : ℝ) < (n : ℝ)) :
    mediumIntegral n Q A u = ∑ i ∈ mediumIndices Q A, ∫ t in arcCell n u i, integrand n t := by
  have hf : Continuous (integrand n) := by unfold integrand primeSum phase; fun_prop
  have hUnion :
      (⋃ i ∈ mediumIndices Q A, arcCell n u i) =
        mediumBand Q A u n ∩ Set.Ioc 0 1 := by
    ext t
    rw [mediumBand_eq_union]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, arcCell]
    constructor
    · rintro ⟨i, hi, ha, ht⟩
      exact ⟨⟨i,hi,ha⟩,ht⟩
    · rintro ⟨⟨i,hi,ha⟩,ht⟩
      exact ⟨i,hi,ha,ht⟩
  rw [mediumIntegral, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator (measurable_mediumBand n Q A u), ← hUnion]
  exact integral_biUnion_finset (mediumIndices Q A) (fun i _ => measurable_arcCell n u i)
    (arcCells_disjoint hn hu hsep) (fun i _ => (hf.intervalIntegrable 0 1).1.mono_set
      Set.inter_subset_right)

theorem mediumModel_re {n Q A : ℕ} {u : ℝ} (hn : 0 < n) (hQ : 1 ≤ Q)
    (hu : 0 ≤ u) (hun : u ≤ (n : ℝ)) :
    (mediumModel n Q A u).re =
      ∑ q ∈ Ioc Q A, (GoldbachExplicitModeledMajor.coefficient q n).re *
        GoldbachGRHKernel.mass n (realRadius n u q) := by
  have he :
      mediumModel n Q A u =
        ∑ q ∈ Ioc Q A, GoldbachExplicitModeledMajor.coefficient q n *
          (GoldbachGRHKernel.mass n (realRadius n u q) : ℂ) := by
    rw [mediumModel, sum_mediumIndices]
    apply sum_congr rfl
    intro q hq
    have hq₂ : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
    have hR : ((range (q+1)).filter (fun a => a.Coprime q)) =
        (range q).filter (fun a => a.Coprime q) := by
      ext a
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨ha,hc⟩
        have hne : a ≠ q := by
          intro heq
          have h1 : q = 1 := by simpa [heq,Nat.Coprime] using hc
          omega
        exact ⟨by omega,hc⟩
      · rintro ⟨ha,hc⟩
        exact ⟨by omega,hc⟩
    rw [hR, ← GoldbachGRHModelAssembly.sum_signedFactor, sum_mul]
    apply sum_congr rfl
    intro a ha
    obtain ⟨haq,hcop⟩ := mem_filter.mp ha
    simp_rw [GoldbachGRHModelAssembly.model_square_eq]
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal,
      arcCell_translate hn hu hun hq₂ (mem_range.mp haq).le hcop
        (fun t : ℝ => ‖GoldbachGRHKernel.kernel n t‖^2)] <;> rfl
  rw [he]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

/-- The Ramanujan model has the required signed lower floor at arbitrary
real widths up to half the ambient length. The weights are kernel masses
on nested beta-intervals, so the prefix bound is used by summation by parts. -/
theorem realWidthModelFloor (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n Q A : ℕ, 0 < n → Even n → 1 ≤ Q → K ≤ Q → Q ≤ A →
      ∀ u : ℝ, 0 < u → 2*u ≤ (n : ℝ) →
        -(ε*(n : ℝ)) ≤ (mediumModel n Q A u).re := by
  obtain ⟨K,hK⟩ := GoldbachGRHSignedModel.harmonic_suffix_floor (ε/2) (by positivity)
  refine ⟨K, ?_⟩
  intro n Q A hn he hQ hstart hQA u hu hun
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let w (q : ℕ) := GoldbachGRHKernel.mass n (realRadius n u q)
  have hpos (q : ℕ) (hq : Q ≤ q) : 0 < realRadius n u q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hQ.trans hq
    unfold realRadius
    exact div_pos hu (mul_pos (by linarith) hnR)
  have hmono (q : ℕ) (hq : Q ≤ q) : w (q+1) ≤ w q := by
    apply GoldbachGRHKernel.mass_mono n (hpos (q+1) (by omega)).le
    have hqR : (0 : ℝ) < q := by exact_mod_cast hQ.trans hq
    unfold realRadius
    exact div_le_div_of_nonneg_left hu.le (mul_pos hqR hnR) (by
      push_cast
      nlinarith only [hnR])
  have hw (q : ℕ) (hq : Q ≤ q) : 0 ≤ w q :=
    GoldbachGRHKernel.mass_nonneg n (hpos q hq).le
  have hr : realRadius n u Q ≤ 1/2 := by
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    apply (div_le_iff₀ (by positivity : 0 < (Q : ℝ)*(n : ℝ))).2
    nlinarith only [hun, mul_le_mul_of_nonneg_right hQR hnR.le]
  have hwQ : w Q ≤ (n : ℝ)+1 :=
    sub_nonneg.mp (GoldbachGRHKernel.mass_loss n (hpos Q le_rfl) hr).1
  have hweight := BandTail.weighted_prefix_lower Q A
    (fun q => (GoldbachExplicitModeledMajor.coefficient q n).re) w
    (ε/2) hQA (by positivity) hw hmono (by
      intro i hi _
      have hh := hK Q hstart n i he hi
      refine hh.trans (le_of_eq (sum_congr rfl ?_))
      intro q hq
      exact (GoldbachGRHSignedModel.coefficient_re_eq n q
        ((Nat.zero_le Q).trans_lt (mem_Ioc.mp hq).1)).symm)
  rw [mediumModel_re hn hQ hu.le (by linarith)]
  change -(ε*(n : ℝ)) ≤ ∑ q ∈ Ioc Q A, _ * w q
  apply le_trans _ hweight
  apply neg_le_neg
  calc
    _ ≤ (ε/2)*((n : ℝ)+1) := mul_le_mul_of_nonneg_left hwQ (by positivity)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hn1 hε.le]

/-- The finite Fourier reduction with real width and the exact denominator
band. The modulus factor is in `GBSkirtVariance.mass`. -/
theorem middleEnergy_of_window {n Q A h : ℕ} {u : ℝ} (hn : 0 < n)
    (hQ : 1 ≤ Q) (hh : 0 < h) (hu : 0 ≤ u) (hun : u ≤ n)
    (hwidth : 6*(h : ℝ)*u ≤ n) :
    (h : ℝ)^2 * mediumCellEnergy n Q A u ≤
      8 * ∑ q ∈ Ioc Q A, GBSkirtVariance.mass q n h := by
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
    have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq0
    unfold δ realRadius
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (q : ℝ)*(n : ℝ)), one_mul]
    exact hwidth.trans (by nlinarith only [mul_le_mul_of_nonneg_left hqR (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
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
  have hcells :
      (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
        ∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) ≤
        2 * ∑ a : ZMod q, E a :=
    (le_of_eq (sum_congr rfl hc)).trans (GoldbachGRHArcs.sum_numerators_le_real q E hE)
  have hden := GBSkirtVariance.denominator_bound (q := q) n h δ hh hd hw
  change (h : ℝ)^2/4 * (∑ a : ZMod q, E a) ≤ _ at hden
  rw [GBSkirtVariance.mass, dite_eq_right hq0.ne']
  linarith only [mul_le_mul_of_nonneg_left hcells (sq_nonneg (h : ℝ)), hden]

theorem signedMediumDifference {n Q A : ℕ} {u η : ℝ} (hn : 2 ≤ n) (hu : 0 ≤ u)
    (hsep : 2*u*(A : ℝ) < (n : ℝ)) (hη : 0 < η) :
    ‖mediumIntegral n Q A u - mediumModel n Q A u‖ ≤
      (1+1/η)*mediumCellEnergy n Q A u + η*((n : ℝ)+1)*(Real.log (n : ℝ))^2 := by
  let osc (t : ℝ) := phase (-(n : ℝ)*t)
  have hosc : Continuous osc := by unfold osc phase; fun_prop
  have hS : Continuous (primeSum n) := by unfold primeSum phase; fun_prop
  rw [mediumIntegral_eq_sum (by omega) hu hsep, mediumModel, ← sum_sub_distrib]
  have hsplit (i : ℕ × ℕ) :
      (∫ t in arcCell n u i, integrand n t) -
        (∫ t in arcCell n u i, model n i t ^ 2 * osc t) =
      ∫ t in arcCell n u i, (primeSum n t ^ 2 - model n i t ^ 2) * osc t := by
    have hpart : arcCell n u i ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_right
    have h₁ : IntegrableOn (integrand n) (arcCell n u i) volume :=
      (((hS.pow 2).mul hosc).intervalIntegrable 0 1).1.mono_set hpart
    have h₂ : IntegrableOn (fun t => model n i t ^ 2 * osc t) (arcCell n u i) volume :=
      ((((model_continuous n i).pow 2).mul hosc).intervalIntegrable 0 1).1.mono_set hpart
    rw [← integral_sub h₁ h₂]
    simp [integrand, osc, sub_mul]
  dsimp only [osc] at hsplit
  simp_rw [hsplit]
  apply (norm_sum_le _ _).trans
  have hb := GoldbachGRHWindowEnergy.sum_setIntegral_square_difference_le
    (mediumIndices Q A) (arcCell n u) (fun i _ => measurable_arcCell n u i)
    (fun _ _ => Set.inter_subset_right) (arcCells_disjoint (by omega) hu hsep)
    (primeSum n) (model n) osc hS (fun i _ => model_continuous n i) hosc
    (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(n : ℝ)*t)))) hη
  exact hb.trans (by
    unfold mediumCellEnergy
    rw [mul_assoc η]
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (GoldbachGRHAnalytic.prime_sum_energy_le n hn) hη.le) _)

end
end InnerFloorResearch
