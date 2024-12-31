# finance-tools

Tools for performing personal finance calculations in Lean. It's like [Soulver](https://soulver.app), but limited to retirement planning and with a complicated type system.

Compounding is performed under the assumption that contributions are made at the _end_ of the period. In the future, both leading and trailing contributions should be supported.

## Future

Support for inflation is coming soon, and may require handling expenses separately from contributions.

Ultimately periods should be an _inductive_ type to allow getting the ending balance of each year (or even month) individually. This has implications for the compound function.

## Precision

Rational numbers are used throughout, to hopefully avoid some of the [pitfalls](https://stackoverflow.com/questions/3730019/why-not-use-double-or-float-to-represent-currency) of performing calculations with Floats. Lean's Rat provides a floor function which will give you useful output (with some loss of precision).

Typically programmers represent currency as a cent integer (or event tenths of a cent). All examples in this project are represented as dollars for clarity; choose your own precision.

More tests are needed. I'm not very good at Lean or math in general, as you will see.

## Usage

First install Lean 4: https://leanprover-community.github.io/get_started.html

I recommend you clone the repo, create a Scratchpad.lean file, and start defining some Scenarios.

Lean provides the ability to evaluate functions directly in your code editor via #eval - this is the entire motiviation of this project:

```
def plan : Scenario := {
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

-- end of plan balance will be $1,124,477:
#eval plan.endingBalance.floor


```
