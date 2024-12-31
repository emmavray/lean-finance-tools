import Batteries.Data.Rat
import FinanceTools.Basic

structure Period where
  PMT: Int
  r: Rat
  t: Nat

/-- represents a financial plan with periods of savings and withdrawals
  Properties:
    P: starting principle
    n: periods per year
    periods: ltr array of plan phases
      PMT: payment or withdrawal per period
      r: annual rate
      t: lenth of phase in years

  Getters:
    endingBalance: balance at the end of the plan
-/
structure Scenario where
  -- base scenario:
  P: Rat
  n: Nat
  -- saving or spending periods:
  periods : Array Period

  -- strategy for compounding payment
  (fseries := futureSeriesTrailing)

  def Scenario.endingBalance (self : Scenario) : Rat :=
    self.periods.foldl
      (fun acc p => compound acc p.PMT p.r self.n p.t self.fseries)
      self.P

-- t=0
theorem endingBalance_t_0
  (P: Rat)
  (PMT: Int)
  (r : Rat)
  (n : Nat) :
    let zero_time : Scenario := {
      P
      n
      periods := #[
        {PMT, r, t := 0},
        {PMT, r, t := 0},
        {PMT, r, t := 0}
      ]
    }
  Scenario.endingBalance zero_time = P := by
  unfold Scenario.endingBalance
  norm_num
  apply compound_t_zero

-- PMT=0 t=1
theorem endingBalance_t_one
  (P: Rat)
  (r : Rat)
  (n : Nat) :
    let zero_pmt : Scenario := {
      P
      n
      periods := #[
        {PMT := 0, r, t := 1}
      ]
    }
  Scenario.endingBalance zero_pmt = P * ((1 + r / n)^n) := by
  unfold Scenario.endingBalance
  norm_num
  apply compound_t_one
