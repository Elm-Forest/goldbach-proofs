import InnerFloorHighBand
import InnerFloorModelTransfer
import InnerFloorWindowScale
import InnerFloorWindowScale

open Finset MeasureTheory Filter
open scoped Interval Topology Classical

namespace InnerFloorResearch

noncomputable section

/-- The exact registered type at origin/main 1fe24b28926c. -/
def FrozenWideRemainderInnerFloor : Prop :=
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
  let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
  let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}
  let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t)
  let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  let H := fun n : ℕ => 256 * Q₁ n * Q n
  let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
  let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
  let lowPart := fun n : ℕ => lowWideArcs n \ arcs n
  let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n
  let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}
  let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re
  let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n)
  floor (fun n => remainder n ∩ inner n)

/-- Weighted sliding-window input for the middle denominators. The summand
already includes the Fourier weight `q`; the windows can be clipped. -/
def MiddleWindowVariance : Prop := ∀ᶠ n : ℕ in atTop,
  (∑ q ∈ Ioc (innerCutoff n) (middleCutoff n), GBSkirtVariance.mass q n (innerWindow n)) ≤
    (n : ℝ)*(innerWindow n : ℝ)^2/(Real.log (n : ℝ))^8

private theorem mediumIntegral_split {n Q A B : ℕ} {u : ℝ}
    (hn : 0 < n) (hu : 0 ≤ u) (hQA : Q ≤ A) (hAB : A ≤ B)
    (hsep : 2*u*(B : ℝ) < (n : ℝ)) :
    mediumIntegral n Q B u = mediumIntegral n Q A u + mediumIntegral n A B u := by
  let D := mediumBand Q A u (n : ℝ)
  let E := mediumBand A B u (n : ℝ)
  have hd : Disjoint D E := by
    rw [Set.disjoint_left]
    intro t ht ht'
    obtain ⟨q,a,hq,_,hqA,_,hc,ht⟩ := ht
    obtain ⟨r,b,hr,_,hrB,_,hd,ht'⟩ := ht'
    have hh := mediumBand_unique Q B u (n : ℝ) hu (by exact_mod_cast hn)
      hsep hq (hQA.trans_lt hr) (hqA.trans hAB) hrB hc hd ht ht'
    omega
  have hset : mediumBand Q B u (n : ℝ) = D ∪ E := by
    ext t
    constructor
    · rintro ⟨q,a,hq,hq0,hqB,ha,hc,ht⟩
      by_cases hqA : q ≤ A
      · exact Or.inl ⟨q,a,hq,hq0,hqA,ha,hc,ht⟩
      · exact Or.inr ⟨q,a,lt_of_not_ge hqA,hq0,hqB,ha,hc,ht⟩
    · rintro (⟨q,a,hq,hq0,hqA,ha,hc,ht⟩ | ⟨q,a,hq,hq0,hqB,ha,hc,ht⟩)
      · exact ⟨q,a,hq,hq0,hqA.trans hAB,ha,hc,ht⟩
      · exact ⟨q,a,hQA.trans_lt hq,hq0,hqB,ha,hc,ht⟩
  let f := GoldbachGRHApproximation.integrand n
  have hf : Continuous f := by
    unfold f GoldbachGRHApproximation.integrand GoldbachFourthMoment.primeSum GoldbachFourthMoment.phase
    fun_prop
  have hI (s : Set ℝ) (hs : MeasurableSet s) : IntervalIntegrable (s.indicator f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 <|
      (hf.intervalIntegrable 0 1).1.indicator hs
  have hind : (D ∪ E).indicator f = fun t => D.indicator f t + E.indicator f t := by
    ext t
    by_cases hD : t ∈ D
    · have hE : t ∉ E := fun h => Set.disjoint_left.mp hd hD h
      simp [Set.indicator, hD, hE]
    · by_cases hE : t ∈ E <;> simp [Set.indicator, hD, hE]
  unfold mediumIntegral
  rw [hset, hind]
  exact intervalIntegral.integral_add
    (hI D (measurable_mediumBand n Q A u)) (hI E (measurable_mediumBand n A B u))

private theorem signedDifferenceSmall (hVariance : MiddleWindowVariance) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖mediumIntegral n (innerCutoff n) (middleCutoff n) (innerWidth n) -
          mediumModel n (innerCutoff n) (middleCutoff n) (innerWidth n)‖ ≤ ε*(n : ℝ) := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventualInnerGeometry, eventualInnerWindow, hVariance,
    ht.eventually_ge_atTop (max 1 (18/ε))] with n hg hw hv hL
  obtain ⟨hn, hQ, hQA, hAB, huH, hbudget⟩ := hg
  let L := Real.log (n : ℝ)
  let u := innerWidth n
  let h := innerWindow n
  let A := middleCutoff n
  let Q := innerCutoff n
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLe : 18/ε ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hu : 0 ≤ u := by unfold u innerWidth; positivity
  have hhR : 0 < (h : ℝ) := (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < n) _).trans_le hw.1
  have hh : 0 < h := by exact_mod_cast hhR
  have hsep : 2*u*(A : ℝ) < (n : ℝ) := by
    apply lt_of_le_of_lt _ hbudget
    gcongr
  have hun : u ≤ (n : ℝ) := by
    have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hQ.trans hQA
    nlinarith only [hsep, mul_le_mul_of_nonneg_left hA1 hu, hu]
  have hE : mediumCellEnergy n Q A u ≤ 8*(n : ℝ)/L^8 := by
    have H := middleEnergy_of_window (by omega : 0 < n) hQ hh hu hun hw.2.2
    have H' := H.trans (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 8))
    apply le_of_mul_le_mul_left (a := (h : ℝ)^2) _ (by positivity)
    exact H'.trans_eq (by ring)
  have H := signedMediumDifference hn hu hsep (show 0 < 1/L^3 by positivity)
  change ‖_‖ ≤ (1+1/(1/L^3))*mediumCellEnergy n Q A u + (1/L^3)*((n : ℝ)+1)*L^2 at H
  calc
    _ ≤ _ := H
    _ ≤ (1+1/(1/L^3))*(8*(n : ℝ)/L^8) + (1/L^3)*((n : ℝ)+1)*L^2 := by gcongr
    _ ≤ 18*(n : ℝ)/L := by
      have h3 : 1 ≤ L^3 := one_le_pow₀ hL1
      have h7 : L^3 ≤ L^7 := pow_le_pow_right₀ hL1 (by decide)
      have ha : (1+L^3)*(8*(n : ℝ)) ≤ (16*(n : ℝ))*L^7 := by
        nlinarith only [mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ (n : ℝ)),
          mul_le_mul_of_nonneg_right h7 (by positivity : 0 ≤ (n : ℝ))]
      have hb : (1+1/(1/L^3))*(8*(n : ℝ)/L^8) ≤ 16*(n : ℝ)/L := by
        rw [one_div_one_div, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hL0]
        convert mul_le_mul_of_nonneg_right ha hL0.le using 1 <;> ring
      have hc : (1/L^3)*((n : ℝ)+1)*L^2 ≤ 2*(n : ℝ)/L := by
        rw [show (1/L^3)*((n : ℝ)+1)*L^2 = ((n : ℝ)+1)/L by field_simp <;> ring]
        exact div_le_div_of_nonneg_right (by linarith) hL0.le
      exact (add_le_add hb hc).trans_eq (by ring)
    _ ≤ _ := by
      apply (div_le_iff₀ hL0).2
      have he := (div_le_iff₀ hε).1 hLe
      nlinarith only [mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (n : ℝ))]

/-- The exact frozen type follows if the middle-band weighted variance is
proved. The two signed contributions are combined using the disjoint union. -/
theorem candidate_of_middleWindowVariance (hVariance : MiddleWindowVariance) :
    FrozenWideRemainderInnerFloor := by
  have hFun : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Even n → -(ε*(n : ℝ)) ≤
        (∫ t in (0 : ℝ)..1,
          ((((arcSet (outerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n) \
            (arcSet (innerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n)) ∩
            arcSet (outerCutoff n) (innerWidth n) n).indicator
              (GoldbachGRHApproximation.integrand n)) t).re := by
    intro ε hε
    let e := ε/3
    have he : 0 < e := by unfold e; positivity
    obtain ⟨K, hK⟩ := realWidthModelFloor e he
    filter_upwards [eventualInnerGeometry, GoldbachGRHConcreteFloor.eventually_narrow_ge K,
      signedDifferenceSmall hVariance e he, highBandLittleO e he]
      with n hg hlarge hdiff hhigh
    intro hnEven
    obtain ⟨hn,hQ,hQA,hAB,huH,hbud⟩ := hg
    let Q := innerCutoff n
    let A := middleCutoff n
    let B := outerCutoff n
    let H := (GoldbachGRHBudget.width n : ℝ)
    let u := innerWidth n
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hu : 0 < u := by
      unfold u innerWidth
      exact mul_pos (by exact_mod_cast hQ) (Real.rpow_pos_of_pos hnR _)
    have huQ : (Q : ℝ) ≤ u := by
      unfold u innerWidth
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hn1 (by norm_num))
    have hQB : Q ≤ B := hQA.trans hAB
    have hB₁ : (1 : ℝ) ≤ B := by exact_mod_cast (hQ.trans hQB)
    have hsep : 2*u*(B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      gcongr
    have hun : 2*u ≤ (n : ℝ) := by
      nlinarith only [hsep, mul_le_mul_of_nonneg_left hB₁ (show 0 ≤ 2*u by positivity)]
    have hmask : u*(Q : ℝ)+H*(B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      have hprod : u*(Q : ℝ) ≤ H*(B : ℝ) :=
        mul_le_mul huH (by exact_mod_cast hQB) (Nat.cast_nonneg _) (hu.le.trans huH)
      linarith only [hprod]
    rw [inner_remainder_eq Q B (Q : ℝ) H u (n : ℝ) (huQ.trans huH) huH hnR.le,
      masked_medium_eq Q B u H (n : ℝ) hu.le huH hnR hmask]
    change -(ε*(n : ℝ)) ≤ (mediumIntegral n Q B u).re
    rw [mediumIntegral_split (by omega) hu.le hQA hAB hsep, Complex.add_re]
    have hM := hK n Q A (by omega) hnEven hQ hlarge hQA u hu hun
    have hD : |(mediumIntegral n Q A u - mediumModel n Q A u).re| ≤ e*(n : ℝ) :=
      (Complex.abs_re_le_norm _).trans hdiff
    have hHigh' : ‖mediumIntegral n A B u‖ ≤ e*(n : ℝ) := by
      have hu' : u = (Nat.log 2 (n+2) : ℝ)^2 * (n : ℝ)^(1/6 : ℝ) := by
        unfold u innerWidth innerCutoff GoldbachGRHBudget.narrow
        push_cast <;> rfl
      have H := hhigh (mediumBand A B u n) (by
        intro t ht
        obtain ⟨q,a,hq,_,hqB,ha,hcop,ht⟩ := ht
        exact ⟨q,a,hq,hqB,ha,hcop,hu' ▸ ht⟩)
      exact H
    have hHigh := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hHigh')
    have hD' := neg_le_of_abs_le hD
    rw [Complex.sub_re] at hD'
    unfold e at hM hD' hHigh
    linarith only [hM, hD', hHigh]
  intro ε hε
  exact Filter.eventually_atTop.mp (hFun ε hε)

end
end InnerFloorResearch
