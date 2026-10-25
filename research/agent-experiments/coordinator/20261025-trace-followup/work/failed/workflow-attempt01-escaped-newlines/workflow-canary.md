---
Template: ComputationalEssay
---

# LeanLink conversion workflow canary

This checks notebook plumbing only and is not a prize submission.

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit=Environment["RULE30PRIZE_KIT"];
```

```wl
canaryEnvironment=LeanImportString[(*Iconize["Lean source"]*)"import Ruliology.CellularAutomata.Rule30Prize\nnamespace Rule30ConversionCanary\ntheorem reflexive (b : Bool) : b=b := rfl\nend Rule30ConversionCanary\n","ProjectDir"->$Rule30PrizeKit];
Head[canaryEnvironment]
```

```wl
canaryTheorem=canaryEnvironment["Rule30ConversionCanary.reflexive"];
canaryKernelCheck=canaryTheorem["KernelCheck"];
canaryKernelCheck
```
