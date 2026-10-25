---
Template: ComputationalEssay
---

# LeanLink conversion workflow canary

This checks notebook plumbing only and is not a prize submission.

## Setup

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit=Environment["RULE30PRIZE_KIT"];
```

## Embedded proof

```wl
canaryEnvironment=LeanImportString[(*Iconize["Lean source"]*)"import Ruliology.CellularAutomata.Rule30Prize
namespace Rule30ConversionCanary
theorem reflexive (b : Bool) : b=b := rfl
end Rule30ConversionCanary
","ProjectDir"->$Rule30PrizeKit];
Head[canaryEnvironment]
```

## Complete replay

```wl
canaryTheorem=canaryEnvironment["Rule30ConversionCanary.reflexive"];
canaryKernelCheck=canaryTheorem["KernelCheck"];
canaryKernelCheck
```
