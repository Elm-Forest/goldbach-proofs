import Conjectures.Goldbach.InnerFloorClippedMoving
import Conjectures.Goldbach.InnerFloorFrozenAssembly

/-! Combine independently chosen denominator-band windows, with exact
coverage and an explicit bound on the number of bands. -/
open Finset MeasureTheory InnerFloorLinearTotient
open scoped Classical Interval
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem bandCellEnergy_le_bulkBoundary {n D A h X : ℕ} {u : ℝ}
    (hn : 0 < n) (hD : 1 ≤ D) (hA : 0 < A) (hh : 0 < h)
    (hu : 0 ≤ u) (hun : u≤n) (hwidth : 6*(h:ℝ)*u≤(D:ℝ)*n)
    (hAX : A≤X) (hX : X+h≤n) :
    (h:ℝ)^2 * mediumCellEnergy n D A u ≤
      4*((weightConstant*(1+Real.log A))^2 *
        (∑ y∈Ico X (n+1-h),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) +
        ((X+2*h:ℕ):ℝ)*boundaryWindowBudget A n h) := by
  apply (middleEnergy_of_reducedWindow hn hD hh hu hun hwidth).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ = ∑ m∈range (n+1+h),∑ q∈Ioc D A,reducedMovingLevelEnergy q n h m :=
      sum_comm
    _ ≤ ∑ m∈range (n+1+h),∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m := by
      apply sum_le_sum
      intro m _
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact mem_Icc.mpr ⟨hD.trans (mem_Ioc.mp hq).1.le,(mem_Ioc.mp hq).2⟩
      · intro q _ _
        exact reducedMovingLevelEnergy_nonneg q n h m
    _ ≤ _ := reducedMovingBulkBoundary A n h X hA hAX hX

theorem mediumCellEnergy_split (n Q D A : ℕ) (u : ℝ)
    (hQD : Q≤D) (hDA : D≤A) :
    mediumCellEnergy n Q A u =
      mediumCellEnergy n Q D u + mediumCellEnergy n D A u := by
  unfold mediumCellEnergy
  simp only [sum_mediumIndices]
  have he : Ioc Q A = Ioc Q D ∪ Ioc D A := by
    ext q
    simp only [mem_Ioc,mem_union]
    omega
  rw [he,sum_union]
  exact disjoint_left.mpr fun q hq hd => by
    have h₁ := (mem_Ioc.mp hq).2
    have h₂ := (mem_Ioc.mp hd).1
    omega

def denominatorBandEnd (Q A j : ℕ) : ℕ := min A (Q*2^j)

theorem denominatorBandEnd_mono (Q A : ℕ) : Monotone (denominatorBandEnd Q A) := by
  intro j k hjk
  unfold denominatorBandEnd
  exact min_le_min le_rfl (Nat.mul_le_mul_left Q (Nat.pow_le_pow_right (by decide) hjk))

theorem denominatorBandEnd_succ_le_double (Q A j : ℕ) :
    denominatorBandEnd Q A (j+1)≤2*denominatorBandEnd Q A j := by
  unfold denominatorBandEnd
  rw [pow_succ]
  by_cases h : A≤Q*2^j
  · rw [min_eq_left h]
    exact (min_le_left ..).trans (by omega)
  · rw [min_eq_right (by omega)]
    exact (min_le_right ..).trans_eq (by ring)

theorem mediumCellEnergy_dyadic_sum (n Q A K : ℕ) (u : ℝ)
    (hQA : Q≤A) (hcover : A≤Q*2^K) :
    mediumCellEnergy n Q A u =
      ∑ j∈range K,mediumCellEnergy n (denominatorBandEnd Q A j)
        (denominatorBandEnd Q A (j+1)) u := by
  have h0 : denominatorBandEnd Q A 0=Q := by
    simp [denominatorBandEnd,min_eq_right hQA]
  have hK : denominatorBandEnd Q A K=A := min_eq_left hcover
  have hprefix (k : ℕ) : mediumCellEnergy n Q (denominatorBandEnd Q A k) u =
      ∑ j∈range k,mediumCellEnergy n (denominatorBandEnd Q A j)
        (denominatorBandEnd Q A (j+1)) u := by
    induction k with
    | zero =>
      rw [h0]
      simp [mediumCellEnergy,sum_mediumIndices]
    | succ k ih =>
      have hq : Q≤denominatorBandEnd Q A k := by
        rw [← h0]
        exact denominatorBandEnd_mono Q A (Nat.zero_le _)
      rw [mediumCellEnergy_split n Q (denominatorBandEnd Q A k)
        (denominatorBandEnd Q A (k+1)) u hq
          (denominatorBandEnd_mono Q A (Nat.le_succ _)),ih,sum_range_succ]
  simpa only [hK] using hprefix K

/-- It is enough to bound each dyadic band by an allocated share of the
desired frozen energy. The partition is exact, not an estimate on
overlapping arcs. -/
theorem mediumCellEnergy_of_dyadic_bounds (n Q A : ℕ) (u M : ℝ)
    (hQ : 1≤Q) (hQA : Q≤A)
    (hb : ∀ j<Nat.log 2 A+1,
      mediumCellEnergy n (denominatorBandEnd Q A j) (denominatorBandEnd Q A (j+1)) u ≤ M) :
    mediumCellEnergy n Q A u ≤ ((Nat.log 2 A+1:ℕ):ℝ)*M := by
  let K := Nat.log 2 A+1
  have hcover : A≤Q*2^K :=
    (Nat.lt_pow_succ_log_self (by decide : 1<2) A).le.trans
      (Nat.le_mul_of_pos_left _ hQ)
  rw [mediumCellEnergy_dyadic_sum n Q A K u hQA hcover]
  calc
    _ ≤ ∑ _j∈range K,M := sum_le_sum fun j hj => hb j (mem_range.mp hj)
    _ = _ := by simp [K,nsmul_eq_mul]

end
end InnerFloorResearch
