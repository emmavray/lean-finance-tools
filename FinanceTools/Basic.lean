import Batteries.Data.Rat
import Mathlib.Data.Real.Basic -- useful for exponentiating Rats

-- PMT × {[(1 + r/n)^(nt) - 1] / (r/n)} × (1+r/n)
-- when contributions are made at the start of the period
def futureSeriesLeading
 (PMT : Int)
 (r : Rat)
 (n : Nat) : Rat :=
  PMT * (
    ((1 + r / n)^n - 1) /
    (r / n)) *
    (1 + r / n)

-- PMT = 0
theorem futureSeriesLeading_zero_pmt (r : Rat) (n : Nat) :
  futureSeriesLeading 0 r n = 0 := by
  unfold futureSeriesLeading
  norm_num


-- PMT × {[(1 + r/n)^(nt) - 1] / (r/n)}
-- when contributions are made at the end of the period
def futureSeriesTrailing
 (PMT : Int)
 (r : Rat)
 (n : Nat) : Rat :=
 if r = 0 then
     PMT * n
  else
     PMT * (
      ((1 + r / n)^n - 1) /
      (r / n))

-- PMT = 0
theorem futureSeriesTrailing_zero_pmt (r : Rat) (n : Nat) :
  futureSeriesTrailing 0 r n = 0 := by
  unfold futureSeriesTrailing
  norm_num

-- r = 0
theorem futureSeriesTrailing_zero_rate (PMT : Int) (n : Nat) :
  futureSeriesTrailing PMT 0 n = PMT * n := by
  unfold futureSeriesTrailing
  norm_num


-- A=P×(1+r/n)n×t
-- compound annually with contributions or expenses
def compound
  (P : Rat)   -- starting principle
  (PMT : Int) -- payments or withdrawals per period
  (r : Rat)   -- annual rate
  (n : Nat)   -- periods per year
  (t : Nat)   -- time in years
    : Rat :=
  match t with
  | Nat.zero => P
  | Nat.succ t' =>
      (compound P PMT r n t') *
      ((1 + r / n)^n) +
      (futureSeriesTrailing PMT r n)

-- t = 0
theorem compound_t_zero (P : Rat) (PMT : Int) (r : Rat) (n : Nat) :
    compound P PMT r n 0 = P := by
  unfold compound
  simp

-- t = 1
theorem compound_t_one (P : Rat) (r : Rat) (n : Nat) :
    compound P 0 r n 1 = P * ((1 + r / n)^n) := by
  simp [compound]
  apply futureSeriesTrailing_zero_pmt
