import PEqualNP.Outside.L_goldbach_frontier_medcore_bv_band

/- Research auxiliary, not the registered theorem. The integral-cover proof adapts
FrontierBand.actualIntegralBound from the accepted BV-band module, preserving its
Apache-2.0 provenance (muxkin, wzhxzkk and OpenAI sources credited in that module).
Changes: arbitrary real width Q and arbitrary subset D; no signed-monotonicity step. -/

open Finset MeasureTheory GoldbachMajorArc GoldbachBDH
open scoped Interval
namespace InnerFloorResearch

def realBandSet (Q : ℝ) (n A B : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, A<q ∧ q≤B ∧ a≤q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ Q/((q:ℝ)*n)}

theorem subsetIntegralBound (Q : ℝ) (n A B : ℕ) (D : Set ℝ)
    (hQ : 0 ≤ Q) (hA : 1≤A) (hB : 0<B) (hn : 2≤n)
    (hsub : D ⊆ realBandSet Q n A B) :
    ‖∫ t in (0:ℝ)..1, D.indicator
        (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t‖ ≤
      2*(Q/((A:ℝ)*n))*(((n:ℝ)+1+(B:ℝ)^2)*weightEnergy n) := by
  classical
  let g := fun t => ‖primeSum n t‖^2
  have cg : Continuous g := by dsimp [g,primeSum,phase]; fun_prop
  let R := Q/((A:ℝ)*n)
  have hR : 0≤R := by dsimp [R]; exact div_nonneg hQ (by positivity)
  let center := fun q a : ℕ => (a:ℝ)/q
  let F := fun (q a : ℕ) => (Set.Icc (center q a-R) (center q a+R)).indicator g
  have hF (q a : ℕ) : Integrable (F q a) volume :=
    (cg.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hp (q a : ℕ) (t : ℝ) : 0≤F q a t := by
    by_cases h : t ∈ Set.Icc (center q a-R) (center q a+R)
    · simpa only [F, Set.indicator_of_mem h] using sq_nonneg ‖primeSum n t‖
    · simp [F,h]
  let G := fun t => ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, F q a t
  have hGi : Integrable G volume := integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun a _ => hF q a
  have hGp (t : ℝ) : 0≤G t := sum_nonneg fun q _ => sum_nonneg fun a _ => hp q a t
  have hdom (t : ℝ) : ‖D.indicator (fun t => (primeSum n t)^2*phase (-(n:ℝ)*t)) t‖ ≤ G t := by
    by_cases ht : t∈D
    · rw [Set.indicator_of_mem ht,norm_mul,norm_pow,bandPhase_norm,mul_one]
      obtain ⟨q,a,haq,hqb,ha,hcop,hnear⟩ := hsub ht
      have hq : q∈Finset.Icc 1 B := mem_Icc.mpr ⟨by omega,hqb⟩
      have ha' : a∈num q := by
        refine mem_filter.mpr ⟨mem_range.mpr ?_,hcop⟩
        by_contra! hh
        have heq := Nat.le_antisymm ha hh
        have := (Nat.coprime_self q).mp (heq ▸ hcop)
        omega
      have hrad : Q/((q:ℝ)*n) ≤ R :=
        div_le_div_of_nonneg_left hQ (by positivity) (by gcongr)
      have htF : t∈Set.Icc (center q a-R) (center q a+R) := by
        have h := abs_le.mp (hnear.trans hrad)
        change center q a-R ≤ t ∧ t ≤ center q a+R
        dsimp [center] at *
        constructor <;> linarith [h.1,h.2]
      change g t ≤ _
      calc
        _ = F q a t := (Set.indicator_of_mem htF g).symm
        _ ≤ ∑ b ∈ num q, F q b t := single_le_sum (fun b _ => hp q b t) ha'
        _ ≤ _ := single_le_sum (fun r _ => sum_nonneg fun b _ => hp r b t) hq
    · simpa [ht] using hGp t
  have htranslate (q a : ℕ) :
      (∫ t, F q a t) = ∫ β in -R..R, g (β+center q a) := by
    rw [intervalIntegral.integral_comp_add_right,intervalIntegral.integral_of_le (by linarith)]
    unfold F
    rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc]
    congr 1 <;> congr 1 <;> ring
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖D.indicator (fun t => (primeSum n t)^2*phase (-(n:ℝ)*t)) t‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t, G t := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hGi.integrableOn (Filter.Eventually.of_forall hdom)).trans
        (setIntegral_le_integral hGi (Filter.Eventually.of_forall hGp))
    _ = ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, ∫ β in -R..R, g (β+center q a) := by
      unfold G
      rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ fun a _ => hF q a)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_finsetSum _ (fun a _ => hF q a)]
      simp_rw [htranslate]
    _ = ∫ β in -R..R, ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, g (β+center q a) := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro q _
        rw [intervalIntegral.integral_finsetSum]
        exact fun a _ => (cg.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
      · intro q _
        apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun _ _ => cg.comp (continuous_id.add continuous_const)
    _ ≤ ∫ _β in -R..R, (((n:ℝ)+1+(B:ℝ)^2)*weightEnergy n) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
          cg.comp (continuous_id.add continuous_const)
      · exact continuous_const.intervalIntegrable _ _
      · exact fun t _ => shifted_spectrum n B hB t
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; dsimp [R]; ring


theorem subsetBound (Q : ℝ) (n A B : ℕ) (D : Set ℝ)
    (hQ : 0≤Q) (hA : 1≤A) (hB : 0<B) (hBn : B^2≤n) (hn : 2≤n)
    (hsub : D ⊆ realBandSet Q n A B) :
    ‖∫ t in (0:ℝ)..1, D.indicator
        (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t‖ ≤
      24*(n:ℝ)*Q*(1+Real.log n)^2/A := by
  have h := subsetIntegralBound Q n A B D hQ hA hB hn hsub
  have he := energy_bound n (by omega)
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg _
  have hx : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : (0:ℝ)<A := by exact_mod_cast (show 0<A by omega)
  have hc : (n:ℝ)+1+(B:ℝ)^2 ≤ 3*n := by
    have hb : (B:ℝ)^2 ≤ n := by exact_mod_cast hBn
    linarith [show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)]
  have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have he' : weightEnergy n ≤ 3*n*Real.log n := he.trans (by gcongr)
  have he0 : 0≤weightEnergy n := sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ _ := h
    _ ≤ 2*(Q/((A:ℝ)*n))*((3*n)*(3*n*Real.log n)) := by
      gcongr
    _ = 18*(n:ℝ)*Q*Real.log n/A := by field_simp; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ ha.le
      have he'' : 18*Real.log n ≤ 24*(1+Real.log n)^2 := by nlinarith [sq_nonneg (Real.log (n:ℝ))]
      nlinarith only [mul_le_mul_of_nonneg_left he'' (mul_nonneg hx.le hQ)]

private theorem highBandLog (n : ℕ) (hn : 2≤n) :
    (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
  have hb := Real.natLog_le_logb (n+2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2:ℝ)≤n := by exact_mod_cast hn
  have hh : (n:ℝ)+2 ≤ (n:ℝ)^2 := by nlinarith [mul_nonneg (show 0≤(n:ℝ)-2 by linarith) (show 0≤(n:ℝ)+1 by linarith)]
  have hl := Real.log_le_log (by positivity : 0<(n:ℝ)+2) hh
  rw [Real.log_pow] at hl
  norm_num at hl
  have hx' := (le_div_iff₀ (by linarith : 0<Real.log 2)).mp hb
  have hm := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ)≤_)
  linarith only [hl,hx',hm]


open Filter
open scoped Topology

/-- The part with denominators above n^(1/5) has absolute mass o(n), even after
an arbitrary additional mask. The remaining lower-denominator part is not addressed. -/
theorem highBandLittleO (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Set ℝ,
      D ⊆ realBandSet ((Nat.log 2 (n+2):ℝ)^2 * (n:ℝ)^(1/6:ℝ)) n
        ⌊(n:ℝ)^(1/5:ℝ)⌋₊ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ →
      ‖∫ t in (0:ℝ)..1, D.indicator
          (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t‖ ≤ e*(n:ℝ) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/5)).comp ht
  have hc := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) (by norm_num : (0:ℝ)<1/30)).comp_tendsto ht).bound
    (by positivity : 0 < e/4000)
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    hp.eventually_ge_atTop 2,hc] with n hn hL hu hsmall
  intro D hD
  let L := Real.log (n:ℝ)
  let u := (n:ℝ)^(1/5:ℝ)
  let v := (n:ℝ)^(1/6:ℝ)
  let Q := (Nat.log 2 (n+2):ℝ)^2 * v
  let A : ℕ := ⌊u⌋₊
  let B : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hX : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hu2 : 2≤u := hu
  have hA : 1≤A := Nat.floor_pos.mpr (by linarith : 1≤u)
  have hAp : (0:ℝ)<A := by exact_mod_cast hA
  have hA1 : (1:ℝ)≤A := by exact_mod_cast hA
  have huA : u ≤ 2*(A:ℝ) := by
    have hf := Nat.lt_floor_add_one u
    change u < (A:ℝ)+1 at hf
    linarith
  have hB : 0<B := Nat.floor_pos.mpr (Real.one_le_rpow hX (by norm_num))
  have hBsq : B^2≤n := FrontierBand.denomSquare n hn _ (by norm_num)
  have hv : 0≤v := Real.rpow_nonneg hnR.le _
  have hQ : 0≤Q := mul_nonneg (sq_nonneg _) hv
  have hlog := highBandLog n hn
  have hlogSq := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ)≤_) hlog 2
  have hQb : Q ≤ 16*L^2*v := by
    have h := mul_le_mul_of_nonneg_right hlogSq hv
    dsimp [Q,L] at *
    nlinarith only [h]
  have hL1 : 1≤L := hL
  have hLsq : (1+L)^2 ≤ 4*L^2 := by nlinarith
  have hmul := mul_le_mul hQb hLsq (sq_nonneg _) (by positivity : 0≤16*L^2*v)
  have hs : L^4 ≤ (e/4000)*(n:ℝ)^(1/30:ℝ) := by
    change ‖Real.log (n:ℝ)^(4:ℝ)‖ ≤ (e/4000)*‖(n:ℝ)^(1/30:ℝ)‖ at hsmall
    simpa only [L,Real.rpow_ofNat,Real.norm_of_nonneg (by positivity : 0≤(Real.log (n:ℝ))^4),
      Real.norm_of_nonneg (Real.rpow_nonneg hnR.le (1/30:ℝ))] using hsmall
  have hpow : (n:ℝ)^(1/30:ℝ)*v = u := by
    dsimp [u,v]
    rw [← Real.rpow_add hnR]
    norm_num
  have hbudget : 24*Q*(1+L)^2 ≤ e*(A:ℝ) := by
    calc
      _ ≤ 1536*L^4*v := by nlinarith only [hmul]
      _ ≤ 1536*((e/4000)*(n:ℝ)^(1/30:ℝ))*v := by gcongr
      _ = (1536/4000:ℝ)*e*u := by rw [← hpow]; ring
      _ ≤ e*(A:ℝ) := by
        nlinarith only [mul_le_mul_of_nonneg_left huA he.le,
          mul_nonneg he.le (Nat.cast_nonneg A : (0:ℝ)≤A)]
  have hbound := subsetBound Q n A B D hQ hA hB hBsq hn hD
  refine hbound.trans ?_
  apply (div_le_iff₀ hAp).2
  have h := mul_le_mul_of_nonneg_right hbudget hnR.le
  dsimp [L] at h
  nlinarith only [h]

end InnerFloorResearch
