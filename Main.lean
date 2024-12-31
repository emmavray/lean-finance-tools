import FinanceTools


def main : IO Unit :=

  let plan : Scenario := {
    -- start with $1k
    P := 1 * 1000
    -- compound monthly
    n := 12
    periods := #[
      -- work for 30yrs:
      {
        PMT := 2 * 1000,
        r := 0.06,
        t := 30
      },
      -- retire for 30yrs:
      {
        PMT := -8000,
        r := 0.04,
        t := 30
      }
    ]
  }

  IO.println s!"balance at plan end ${plan.endingBalance.floor}"
