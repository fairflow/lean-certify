# Deciders: choosing your tools without writing Lean

A *decider* answers a yes/no question about one input (a "specification")
and backs every answer with a certificate that a checker, proved correct in
Lean, has accepted.  You choose which tools it uses by editing four lines of
a settings file.  You do not need to know Lean to do that.

## The words

- **Prover.**  A tool that tries to show the answer is *yes*, by producing a
  certificate (for example a proof).
- **Disprover.**  A tool that tries to show the answer is *no*, by producing
  a certificate against (for example a countermodel).
- **Pair.**  A prover and a disprover used together.  By default they run at
  the same time (`race`); the first one to produce a certificate that its
  checker accepts gives the answer.
- **Fallback pairs.**  Pairs tried in order when the first pair finds
  nothing.  To fall back on one side only, repeat the other side's tool: for
  example `("subtab", "enum")` after a first pair `subtab`/`subtab` keeps the
  same prover and changes only the disprover.
- **Budget.**  A number handed to each tool to limit its search.  When a
  pair finds nothing, its budget is multiplied (`budgetFactor`) and the pair
  is tried again, `flagReruns` times, before the next pair.
- **Flag.**  The answer when every pair ran out of budget or time.  A flag
  is not "no": it means "not decided within these limits".  Its report lists
  every attempt.
- **REJECTED.**  A tool produced a certificate that its checker refused.
  That is a defect in the tool, never a wrong answer: the decider ignores the
  certificate, records it in the report, and carries on.

## The settings file

Your project has one settings file (for example `Harness/Settings.lean`).
Edit only the lines marked `EDIT`; the tool names come from the list the
project wrote once (`Harness.tools`).  A misspelt name is reported as an
error when the file is compiled, with the name that is unknown.

```lean
def Harness.decider : Harness.DeciderConfig where
  prover    := "subtab"                    -- EDIT
  disprover := "subtab"                    -- EDIT
  fallback  := [("frjw", "enum")]          -- EDIT: pairs, tried in order
  run       := { mode := .race,            -- EDIT: .race | .sequential
                 budget := 1000,
                 deadlineSec := 120 }

#certify_decider Harness.decider           -- checks every name
```

The settings you may leave out, with their defaults: `mode := .race`,
`budget := 1000`, `flagReruns := 2`, `budgetFactor := 4`,
`deadlineSec := 600`.

## Running it

The project's decider executable takes the input as one argument:

    <tool> "<input>"
    <tool> --deadline=300 --mode=sequential "<input>"      # override for one run
    <tool> --json                                            # print the settings as JSON

Command-line settings change one run only; they never change the file.
Exit codes: 0 yes, 1 no, 2 usage or parse error, 3 flag.

## JSON

`<tool> --json` prints the settings, for tools that are not Lean.  The JSON
is generated from the Lean file; editing the JSON changes nothing.

```json
{
  "prover": "subtab",
  "disprover": "subtab",
  "fallback": [["frjw", "enum"]],
  "run": { "mode": "race", "budget": 1000, "flagReruns": 2,
           "budgetFactor": 4, "deadlineSec": 120 }
}
```

## What a decider never does

It never answers without a certificate that its checker accepted, and it
never turns "ran out of budget" into "no".
