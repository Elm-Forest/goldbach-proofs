import Conjectures.Goldbach.InnerFloorWindowScale

/-!
Ten fixed exponent bands rather than O(log n) dyadic denominator bands.
The first lower denominator is at least the frozen narrow cutoff;
each subsequent endpoint is floor(n^(j/50)). A constant number of
bands is enough because the explicit-formula scale inequalities have
strict exponent slack even at the top endpoint 1/5.

This is only the parameter/partition step, not the zero-free theorem.
-/
open Filter Finset
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def fixedBandLowerExp (j : ℕ) : ℝ := (j:ℝ)/50
def fixedBandUpperExp (j : ℕ) : ℝ := ((j+1:ℕ):ℝ)/50
def fixedBandWindowExp (j : ℕ) : ℝ :=
  min (5/6 + fixedBandLowerExp j - 1/100) (99/100)

def fixedBandEnd (n j : ℕ) : ℕ :=
  max (innerCutoff n) ⌊(n:ℝ)^(fixedBandLowerExp j)⌋₊

def fixedBandWindow (n j : ℕ) : ℕ :=
  ⌊(n:ℝ)^(fixedBandWindowExp j)⌋₊

/-- All relevant exponent inequalities have explicit slack. In particular,
the worst density scale is the last band and still saves 1/150. -/
theorem fixedBandExponents (j : ℕ) (hj : j < 10) (b : ℝ)
    (hb : fixedBandWindowExp j - 1/1000 ≤ b) (hb' : b ≤ 1) :
    0 ≤ fixedBandLowerExp j ∧
    fixedBandUpperExp j ≤ 1/5 ∧
    4/5+1/100 ≤ fixedBandWindowExp j ∧
    fixedBandWindowExp j ≤ 99/100 ∧
    fixedBandWindowExp j + 1/100 ≤ 5/6 + fixedBandLowerExp j ∧
    2*fixedBandUpperExp j+(7/12)*b-fixedBandWindowExp j ≤ -1/150 ∧
    fixedBandUpperExp j+(2/3)*b-fixedBandWindowExp j ≤ -1/10 ∧
    fixedBandUpperExp j-b/6-fixedBandWindowExp j ≤ -1/10 ∧
    3*fixedBandUpperExp j-b/6-fixedBandWindowExp j ≤ -1/10 ∧
    fixedBandUpperExp j+b/2-fixedBandWindowExp j ≤ -1/4 ∧
    fixedBandUpperExp j-b/2 ≤ -1/10 := by
  interval_cases j <;>
    norm_num [fixedBandLowerExp,fixedBandUpperExp,fixedBandWindowExp,min_def] at * <;>
    (repeat' (first | apply And.intro | linarith))

theorem fixedBandEnd_mono (n : ℕ) (hn : 1 ≤ n) :
    Monotone (fixedBandEnd n) := by
  intro j k hjk
  unfold fixedBandEnd
  apply max_le_max le_rfl
  apply Nat.floor_mono
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  unfold fixedBandLowerExp
  gcongr

theorem fixedBandEnd_zero (n : ℕ) (hQ : 1 ≤ innerCutoff n) :
    fixedBandEnd n 0=innerCutoff n := by
  simp [fixedBandEnd,fixedBandLowerExp,max_eq_left hQ]

theorem fixedBandEnd_ten (n : ℕ) (hQA : innerCutoff n ≤ middleCutoff n) :
    fixedBandEnd n 10=middleCutoff n := by
  have he : fixedBandLowerExp 10=1/5 := by norm_num [fixedBandLowerExp]
  rw [fixedBandEnd,he]
  exact max_eq_right hQA

theorem fixedBandWindow_bounds (n j : ℕ) (hn : 1 ≤ n) (hj : j < 10) :
    fixedBandWindow n j ≤ n ∧
    (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^(99/100:ℝ) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hc : fixedBandWindowExp j ≤ (99/100:ℝ) := min_le_right _ _
  have hf : (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^fixedBandWindowExp j :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hh := hf.trans (Real.rpow_le_rpow_of_exponent_le hn' hc)
  exact ⟨by exact_mod_cast (hh.trans
    (by simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hn' (show (99/100:ℝ) ≤ 1 by norm_num)))),hh⟩

/-- The ten widths all satisfy the exact Gallagher frequency condition
and the uniform lower bound needed for the principal prime window.
The cap n^.99 gives a polynomial boundary saving, not just a log cap. -/
theorem eventualFixedBandWindows : ∀ᶠ n : ℕ in atTop,
    ∀ j < 10,
      (n:ℝ)^(4/5:ℝ) ≤ (fixedBandWindow n j:ℝ) ∧
      (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^(99/100:ℝ) ∧
      6*(fixedBandWindow n j:ℝ)*innerWidth n ≤ (fixedBandEnd n j:ℝ)*n := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htiny := (tendsto_rpow_atTop (show (0:ℝ) < 1/100 by norm_num)).comp ht
  filter_upwards [eventualInnerGeometry,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/100) (1/192) (by norm_num) (by norm_num),
    htiny.eventually_ge_atTop 2] with n hg hlog hsmall
  intro j hj
  obtain ⟨hn,hQ,hQA,hAB,huH,hsep⟩ := hg
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hc : (4/5+1/100:ℝ) ≤ fixedBandWindowExp j := by
    unfold fixedBandWindowExp fixedBandLowerExp
    apply le_min <;> linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hres : fixedBandWindowExp j+1/100 ≤ 5/6+fixedBandLowerExp j := by
    linarith [min_le_left (5/6+fixedBandLowerExp j-1/100) (99/100:ℝ)]
  have hf := Nat.lt_floor_add_one ((n:ℝ)^fixedBandWindowExp j)
  change (n:ℝ)^fixedBandWindowExp j < (fixedBandWindow n j:ℝ)+1 at hf
  have hlower : 2*(n:ℝ)^(4/5:ℝ) ≤ (n:ℝ)^fixedBandWindowExp j := by
    calc
      _ ≤ (n:ℝ)^(1/100:ℝ)*(n:ℝ)^(4/5:ℝ) :=
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hnP.le _)
      _ = (n:ℝ)^(4/5+1/100:ℝ) := by rw [← Real.rpow_add hnP]; congr 1 <;> ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR hc
  have h1 := Real.one_le_rpow hnR (show (0:ℝ) ≤ 4/5 by norm_num)
  have hf' : (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^fixedBandWindowExp j :=
    Nat.floor_le (Real.rpow_nonneg hnP.le _)
  have hQlog : (innerCutoff n:ℝ) ≤ 16*(Real.log (n:ℝ))^2 := by
    -- Public re-use of the bound through the exact narrow definition.
    have hp : (2:ℝ)^Nat.log 2 (n+2) ≤ ((n+2:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2≠0)
    have hraw := Real.log_le_log (by positivity) hp
    have hin : ((n+2:ℕ):ℝ) ≤ (n:ℝ)^2 := by
      push_cast
      nlinarith only [(show (2:ℝ) ≤ n by exact_mod_cast hn),sq_nonneg ((n:ℝ)-2)]
    have hlog' := Real.log_le_log (by positivity) hin
    rw [Real.log_pow] at hraw hlog'
    have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (n+2)))
    have hL : (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
      push_cast at hraw hlog'
      linarith only [hraw,hlog',hm]
    unfold innerCutoff GoldbachGRHBudget.narrow
    push_cast
    calc
      _ ≤ (4*Real.log n)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
      _ = _ := by ring
  have hQsmall : 12*(innerCutoff n:ℝ) ≤ (n:ℝ)^(1/100:ℝ) := by
    linarith only [hQlog,hlog]
  have hD : (n:ℝ)^fixedBandLowerExp j ≤ 2*(fixedBandEnd n j:ℝ) := by
    have hp := Nat.lt_floor_add_one ((n:ℝ)^fixedBandLowerExp j)
    have hm : (⌊(n:ℝ)^fixedBandLowerExp j⌋₊:ℝ) ≤ (fixedBandEnd n j:ℝ) := by
      exact_mod_cast le_max_right (innerCutoff n) ⌊(n:ℝ)^fixedBandLowerExp j⌋₊
    have hD1 : (1:ℝ) ≤ fixedBandEnd n j := by
      exact_mod_cast hQ.trans (le_max_left _ _)
    linarith
  refine ⟨by linarith,(fixedBandWindow_bounds n j (by omega) hj).2,?_⟩
  have hpow : (n:ℝ)^(fixedBandWindowExp j+1/100+1/6) ≤ (n:ℝ)^(1+fixedBandLowerExp j) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  calc
    _ = (12*(innerCutoff n:ℝ))*(fixedBandWindow n j:ℝ)*(n:ℝ)^(1/6:ℝ)/2 := by
      unfold innerWidth
      ring
    _ ≤ ((n:ℝ)^(1/100:ℝ)*(n:ℝ)^fixedBandWindowExp j)*(n:ℝ)^(1/6:ℝ)/2 := by
      gcongr
    _ = (n:ℝ)^(fixedBandWindowExp j+1/100+1/6)/2 := by
      rw [← Real.rpow_add hnP,← Real.rpow_add hnP]
      congr 2 <;> ring
    _ ≤ (n:ℝ)^(1+fixedBandLowerExp j)/2 :=
      div_le_div_of_nonneg_right hpow (by norm_num)
    _ = (n:ℝ)*((n:ℝ)^fixedBandLowerExp j)/2 := by rw [Real.rpow_add hnP,Real.rpow_one]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hD hnP.le]

end
end InnerFloorResearch
