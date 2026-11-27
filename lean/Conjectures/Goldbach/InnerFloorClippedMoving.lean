import Conjectures.Goldbach.InnerFloorBoundaryEnergy
import Conjectures.Goldbach.InnerFloorReducedModelTransfer

/-! Exact clipped windows and boundary energy. No zero-free assumption. -/
open Finset BombieriVinogradov.LargeSieve InnerFloorLinearTotient
open GoldbachGRHWindow (primeLog additiveModel)
open GoldbachWindow (moving)
open GoldbachGRHAnalytic (errorCoeff)
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def clipStart (h m : ℕ) : ℕ := m+1-h
def clipEnd (n m : ℕ) : ℕ := min m n
def clipLength (n h m : ℕ) : ℕ := clipEnd n m+1-clipStart h m
def clipShift (h m : ℕ) : ℤ := (clipStart h m:ℤ)-1

theorem clipLength_le (n h m : ℕ) : clipLength n h m ≤ h := by
  unfold clipLength clipStart clipEnd
  omega

theorem clipWindow_card (n h m : ℕ) :
    (GBSkirtVariance.window n h m).card = clipLength n h m := by
  rw [GBSkirtVariance.window,Nat.card_Icc]
  unfold clipLength clipStart clipEnd
  omega

theorem clipNatIntSum (n h m : ℕ) {M : Type*} [AddCommMonoid M]
    (f : ℤ → M) :
    (∑ k∈GBSkirtVariance.window n h m, f (k:ℤ)) =
      ∑ k∈Ioc (clipShift h m) (clipShift h m+(clipLength n h m:ℤ)),f k := by
  apply sum_bij (fun k _ => (k:ℤ))
  · intro k hk
    simp only [GBSkirtVariance.window,mem_Icc] at hk
    simp only [mem_Ioc,clipShift,clipLength,clipStart,clipEnd]
    omega
  · intro a ha b hb he
    exact_mod_cast he
  · intro k hk
    simp only [mem_Ioc,clipShift,clipLength,clipStart,clipEnd] at hk
    have hk0 : 0 ≤ k := by omega
    refine ⟨k.toNat,?_,Int.toNat_of_nonneg hk0⟩
    simp only [GBSkirtVariance.window,mem_Icc]
    omega
  · intro k hk
    rfl

theorem moving_eq_centeredInterval (n h m : ℕ) {q : ℕ} [NeZero q]
    (a : (ZMod q)ˣ) :
    moving (n+1) h (errorCoeff (a:ZMod q)) m =
      intervalAdditiveResidueSum (fun k : ℤ => primeLog k.toNat)
        (clipShift h m) (clipLength n h m) q a -
      (clipLength n h m:ℂ)*additiveModel q (a:ZMod q) := by
  rw [GoldbachWindow.moving_eq_sum]
  have hI : (range (n+1)).filter (fun k => m+1-h≤k ∧ k≤m) =
      GBSkirtVariance.window n h m := by
    ext k
    simp only [mem_filter,mem_range,GBSkirtVariance.window,mem_Icc,le_min_iff]
    omega
  rw [hI]
  unfold errorCoeff
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,clipWindow_card]
  congr 1
  unfold intervalAdditiveResidueSum
  rw [← clipNatIntSum n h m
    (fun k : ℤ => primeLog k.toNat * ZMod.stdAddChar ((k:ZMod q)*(a:ZMod q)))]
  apply sum_congr rfl
  intro k _
  simp only [Int.toNat_natCast,Int.cast_natCast]
  rw [mul_comm (a:ZMod q) (k:ZMod q)]

theorem reducedMoving_eq_centeredIntervalEnergy (n h m q : ℕ) :
    reducedMovingLevelEnergy q n h m =
      centeredIntervalEnergy (fun k : ℤ => primeLog k.toNat)
        (clipShift h m) (clipLength n h m) q := by
  by_cases hq : q=0
  · simp [reducedMovingLevelEnergy,centeredIntervalEnergy,hq]
  · simp only [reducedMovingLevelEnergy,centeredIntervalEnergy,dif_neg hq]
    exact sum_congr rfl fun a _ => by rw [moving_eq_centeredInterval n h m a]

theorem clipShiftedCoefficient_le (n h m k : ℕ)
    (hk : k∈range (clipLength n h m)) :
    ‖shiftedIntervalCoefficients (fun z : ℤ => primeLog z.toNat)
      (clipShift h m) k‖ ≤ Real.log ((n+2:ℕ):ℝ) := by
  let z := (clipShift h m+(k:ℤ)+1).toNat
  have hz : z≤n := by
    have hk' := mem_range.mp hk
    unfold z clipLength clipShift clipStart clipEnd at *
    omega
  change ‖primeLog z‖ ≤ _
  unfold primeLog
  split_ifs with hp
  · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show z≤n+2 by omega))
  · simp only [Complex.ofReal_zero,norm_zero]
    exact Real.log_nonneg (by exact_mod_cast (show 1≤n+2 by omega))

def boundaryWindowBudget (A n h : ℕ) : ℝ :=
  128*((h:ℝ)+(A:ℝ)^2)*(h:ℝ)*(Real.log ((n+2:ℕ):ℝ))^2+
    2*(h:ℝ)^2*(weightConstant*(1+Real.log A))^2

/-- Uniform per-window energy for the actual clipped error coefficients. -/
theorem actualClippedWindowFamilyEnergy (A n h m : ℕ) (hA : 0 < A) :
    (∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m) ≤
      boundaryWindowBudget A n h := by
  simp_rw [reducedMoving_eq_centeredIntervalEnergy]
  apply (centeredIntervalFamilyEnergy A (clipLength n h m) (clipShift h m)
    (fun z : ℤ => primeLog z.toNat) hA (Real.log ((n+2:ℕ):ℝ))
    (Real.log_nonneg (by exact_mod_cast (show 1≤n+2 by omega)))
    (fun k hk => clipShiftedCoefficient_le n h m k hk)).trans
  unfold boundaryWindowBudget
  have hl : (clipLength n h m:ℝ) ≤ h := by exact_mod_cast clipLength_le n h m
  gcongr
  all_goals positivity

theorem reducedMovingLevelEnergy_nonneg (q n h m : ℕ) :
    0 ≤ reducedMovingLevelEnergy q n h m := by
  unfold reducedMovingLevelEnergy
  split_ifs <;> first | exact le_rfl | exact sum_nonneg fun _ _ => sq_nonneg _

/-- Decompose the actual moving family into a bulk primitive window
sum and the at most X+2h endpoint/startup windows. -/
theorem reducedMovingBulkBoundary (A n h X : ℕ)
    (hA : 0 < A) (hAX : A≤X) (hX : X+h≤n) :
    (∑ m∈range (n+1+h), ∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m) ≤
      (weightConstant*(1+Real.log A))^2 *
        (∑ y∈Ico X (n+1-h), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) +
      ((X+2*h:ℕ):ℝ)*boundaryWindowBudget A n h := by
  let S := range (n+1+h)
  let G := Icc (X+h) n
  let E (m : ℕ) := ∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m
  have hGS : G⊆S := by
    intro m hm
    simp only [G,mem_Icc] at hm
    simp only [S,mem_range]
    omega
  have hcard : (S\G).card = X+2*h := by
    rw [card_sdiff_of_subset hGS]
    simp only [S,G,card_range,Nat.card_Icc]
    omega
  have hbulk :
      (∑ m∈G,E m) ≤ (weightConstant*(1+Real.log A))^2 *
        (∑ y∈Ico X (n+1-h), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) := by
    rw [mul_sum]
    have hre : (∑ m∈G,E m) =
        ∑ y∈Ico X (n+1-h), E (y+h) := by
      apply sum_bij (fun m _ => m-h)
      · intro m hm
        simp only [G,mem_Icc] at hm
        simp only [mem_Ico]
        omega
      · intro m hm k hk he
        simp only [G,mem_Icc] at hm hk
        omega
      · intro y hy
        simp only [mem_Ico] at hy
        refine ⟨y+h,?_,by omega⟩
        simp only [G,mem_Icc]
        omega
      · intro m hm
        simp only [G,mem_Icc] at hm
        rw [Nat.sub_add_cancel (by omega : h≤m)]
    rw [hre]
    apply sum_le_sum
    intro y hy
    have hy' := mem_Ico.mp hy
    exact interiorReducedMovingFamilyEnergy A n y h (hAX.trans hy'.1) (by omega)
  have hedge : (∑ m∈S\G,E m) ≤ ((X+2*h:ℕ):ℝ)*boundaryWindowBudget A n h := by
    calc
      _ ≤ ∑ _m∈S\G,boundaryWindowBudget A n h :=
        sum_le_sum fun m _ => actualClippedWindowFamilyEnergy A n h m hA
      _ = _ := by rw [sum_const,nsmul_eq_mul,hcard]
  change (∑ m∈S,E m) ≤ _
  calc
    _ = (∑ m∈G,E m)+(∑ m∈S\G,E m) := by
      rw [add_comm]
      exact (sum_sdiff hGS).symm
    _ ≤ _ := add_le_add hbulk hedge

end
end InnerFloorResearch
