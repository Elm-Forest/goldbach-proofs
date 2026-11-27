import ShortAPBridge

open Filter Finset
open scoped Topology

namespace InnerFloorResearch

noncomputable section

abbrev innerCutoff := GoldbachGRHBudget.narrow
noncomputable abbrev outerCutoff := GoldbachGRHBudget.cutoff

def innerWidth (n : ℕ) : ℝ := (innerCutoff n : ℝ) * (n : ℝ) ^ (1/6 : ℝ)
def middleCutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1/5 : ℝ)⌋₊
def innerWindow (n : ℕ) : ℕ := ⌊(n : ℝ) / (12 * innerWidth n)⌋₊

private theorem narrow_le_log (n : ℕ) (hn : 2 ≤ n) :
    (innerCutoff n : ℝ) ≤ 16 * (Real.log (n : ℝ)) ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ (Nat.log 2 (n+2)) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n : ℝ)-2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2
    (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0 ≤ (_ : ℝ))
  have hL : (Nat.log 2 (n+2) : ℝ) ≤ 4 * Real.log (n : ℝ) := by
    push_cast at hraw hlog
    linarith only [hraw, hlog, hm]
  unfold innerCutoff GoldbachGRHBudget.narrow
  push_cast
  calc
    _ ≤ (4 * Real.log (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
    _ = _ := by ring

/-- The real inner radius fits the frozen wide-arc budget. -/
theorem eventualInnerGeometry : ∀ᶠ n : ℕ in atTop,
    2 ≤ n ∧ 1 ≤ innerCutoff n ∧ innerCutoff n ≤ middleCutoff n ∧
    middleCutoff n ≤ outerCutoff n ∧ innerWidth n ≤ (GoldbachGRHBudget.width n : ℝ) ∧
    2 * (GoldbachGRHBudget.width n : ℝ) * (outerCutoff n : ℝ) < (n : ℝ) := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/5) (1/16) (by norm_num) (by norm_num)]
    with n hg hlog
  obtain ⟨hn, hQ, hQB, _, _, hbudget⟩ := hg
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hQA : innerCutoff n ≤ middleCutoff n := by
    apply Nat.le_floor
    calc
      _ ≤ 16 * (Real.log (n : ℝ))^2 := narrow_le_log n hn
      _ ≤ (n : ℝ)^(1/5 : ℝ) := by linarith
  have hAB : middleCutoff n ≤ outerCutoff n := by
    apply Nat.floor_mono
    exact Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  have hB1 : (1 : ℝ) ≤ outerCutoff n := by exact_mod_cast hQ.trans hQB
  have h6 : (n : ℝ)^(1/6 : ℝ) ≤ 2 * (outerCutoff n : ℝ) := by
    have hf := Nat.lt_floor_add_one ((n : ℝ)^(1/3 : ℝ))
    change (n : ℝ)^(1/3 : ℝ) < (outerCutoff n : ℝ) + 1 at hf
    exact (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)).trans
      (show (n : ℝ)^(1/3 : ℝ) ≤ 2 * (outerCutoff n : ℝ) by linarith)
  refine ⟨hn, hQ, hQA, hAB, ?_, ?_⟩
  · unfold innerWidth GoldbachGRHBudget.width
    push_cast
    have hQ₀ : 0 ≤ (innerCutoff n : ℝ) := Nat.cast_nonneg _
    have hB₀ : 0 ≤ (outerCutoff n : ℝ) := Nat.cast_nonneg _
    nlinarith only [mul_le_mul_of_nonneg_left h6 hQ₀, mul_nonneg hQ₀ hB₀]
  · exact_mod_cast hbudget

/-- One common window for all inner-arc denominators, with a power margin
in the high-exponent short-progression hypothesis. -/
theorem eventualInnerWindow : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (4/5 : ℝ) ≤ (innerWindow n : ℝ) ∧ innerWindow n ≤ n ∧
    6 * (innerWindow n : ℝ) * innerWidth n ≤ (n : ℝ) := by
  filter_upwards [eventualInnerGeometry,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/30) (1/384) (by norm_num) (by norm_num)]
    with n hg hlog
  obtain ⟨hn, hQ, _, _, _, _⟩ := hg
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hQ' : (1 : ℝ) ≤ innerCutoff n := by exact_mod_cast hQ
  have hu : 0 < innerWidth n :=
    mul_pos (zero_lt_one.trans_le hQ') (Real.rpow_pos_of_pos hn0 _)
  have hu1 : 1 ≤ innerWidth n :=
    one_le_mul_of_one_le_of_one_le hQ' (Real.one_le_rpow hnR (by norm_num))
  have hQsmall : 384 * (Real.log (n : ℝ))^2 ≤ (n : ℝ)^(1/30 : ℝ) := by
    linarith
  have hwidth : 24 * innerWidth n ≤ (n : ℝ)^(1/5 : ℝ) := by
    have hs : 24 * (innerCutoff n : ℝ) ≤ (n : ℝ)^(1/30 : ℝ) := by
      linarith only [narrow_le_log n hn, hQsmall]
    calc
      _ = (24 * (innerCutoff n : ℝ)) * (n : ℝ)^(1/6 : ℝ) := by unfold innerWidth; ring
      _ ≤ (n : ℝ)^(1/30 : ℝ) * (n : ℝ)^(1/6 : ℝ) :=
        mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hdiv : 2 * (n : ℝ)^(4/5 : ℝ) ≤ (n : ℝ)/(12 * innerWidth n) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ = (24 * innerWidth n) * (n : ℝ)^(4/5 : ℝ) := by ring
      _ ≤ (n : ℝ)^(1/5 : ℝ) * (n : ℝ)^(4/5 : ℝ) :=
        mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hf := Nat.lt_floor_add_one ((n : ℝ)/(12 * innerWidth n))
  change (n : ℝ)/(12 * innerWidth n) < (innerWindow n : ℝ) + 1 at hf
  have h1 : 1 ≤ (n : ℝ)^(4/5 : ℝ) := Real.one_le_rpow hnR (by norm_num)
  have hfloor : (innerWindow n : ℝ) ≤ (n : ℝ)/(12 * innerWidth n) :=
    Nat.floor_le (by positivity)
  have hn' : (innerWindow n : ℝ) ≤ (n : ℝ) :=
    hfloor.trans (div_le_self hn0.le (by linarith))
  have hmul := (le_div_iff₀ (show 0 < 12 * innerWidth n by positivity)).1 hfloor
  exact ⟨by linarith, by exact_mod_cast hn', by nlinarith only [hmul, hn0]⟩

theorem sharpModulusBudget {n x h : ℕ} {t : ℝ} (hn : 1 ≤ n) (hx : 1 ≤ x)
    (hxn : x ≤ n) (hlo : (n : ℝ)^(4/5 : ℝ) ≤ (h : ℝ))
    (ht : (4/5 : ℝ) ≤ t) (ht' : t ≤ 1) :
    (outerCutoff n : ℝ)^2 * (x : ℝ)^((1-t)/3+1/16) ≤ (h : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxnR : (x : ℝ) ≤ n := by exact_mod_cast hxn
  have hB : (outerCutoff n : ℝ) ≤ (n : ℝ)^(1/3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hn0.le _)
  have hp : (x : ℝ)^((1-t)/3+1/16) ≤ (n : ℝ)^(31/240 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hxR (by linarith)).trans
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hxnR (by norm_num))
  calc
    _ ≤ ((n : ℝ)^(1/3 : ℝ))^2 * (n : ℝ)^(31/240 : ℝ) :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2) hp
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
    _ = (n : ℝ)^(191/240 : ℝ) := by
      rw [pow_two, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
      norm_num
    _ ≤ (n : ℝ)^(4/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
    _ ≤ _ := hlo

/-- The frozen real AP mean, converted to integer rows without weakening
the modulus condition to the exponent 1/4 used in the low-skirt proof. -/
theorem fullBandDyadicAP :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℕ, ∀ n x h : ℕ,
      X ≤ x → h ≤ x → x ≤ n → (n : ℝ)^(4/5 : ℝ) ≤ (h : ℝ) →
      1 ≤ outerCutoff n →
      (∑ y ∈ Ico x (2*x), GBSkirtVariance.row (outerCutoff n) h y) ≤
        C * (x : ℝ) * (h : ℝ) / (Real.log (x : ℝ))^18 := by
  obtain ⟨C, hC, X, hX⟩ := paperInput
  refine ⟨C, hC, max 2 X, ?_⟩
  intro n x h hx hhx hxn hlen hB
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxX : X ≤ x := (le_max_right _ _).trans hx
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hx0 := zero_lt_one.trans hx1
  have hlog := Real.log_pos hx1
  have hxpow : (x : ℝ)^(4/5 : ℝ) ≤ (h : ℝ) :=
    (Real.rpow_le_rpow (Nat.cast_nonneg x) (by exact_mod_cast hxn) (by norm_num)).trans hlen
  have hh0 := (Real.rpow_pos_of_pos hx0 (4/5 : ℝ)).trans_le hxpow
  let t := Real.log (h : ℝ) / Real.log (x : ℝ)
  have ht : (4/5 : ℝ) ≤ t := by
    apply (le_div_iff₀ hlog).2
    have H := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hxpow
    rwa [Real.log_rpow hx0] at H
  have ht' : t ≤ 1 := by
    apply (div_le_iff₀ hlog).2
    simpa only [one_mul] using Real.log_le_log hh0 (by exact_mod_cast hhx)
  have hpow : (x : ℝ)^t = (h : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]
    unfold t
    rw [show Real.log (x : ℝ) * (Real.log (h : ℝ) / Real.log (x : ℝ)) =
        Real.log (h : ℝ) by field_simp, Real.exp_log hh0]
  have hmod := sharpModulusBudget (show 1 ≤ n by omega) (show 1 ≤ x by omega) hxn hlen ht ht'
  rw [← hpow] at hmod
  have H := hX (x : ℝ) t (by exact_mod_cast hxX) hx1.le
    (by linarith) ht' (outerCutoff n) hB hmod
  rw [hpow, ← GBSkirtVariance.paper_integral] at H
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using H

end
end InnerFloorResearch
