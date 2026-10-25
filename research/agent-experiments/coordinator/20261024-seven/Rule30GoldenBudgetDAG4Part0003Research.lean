import Rule30GoldenBudgetDAG4Part0002Research
import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudgetDAG4Part0003Research
open Rule30GoldenCompactBudgetResearch

theorem node_384 : dfs 4 35 15 78445770705400931669 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1190234748176006744746 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_332
  · change dfs 4 34 16 1918881139091647919445 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_343

theorem node_385 : dfs 4 35 15 111304033587663559338 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1777132423146380667482 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 34 16 2385874977580232005029 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_367

theorem node_386 : dfs 4 35 15 111361864050063805098 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1771660628762745985626 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 34 16 2380403183199030781349 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_361

theorem node_387 : dfs 4 35 15 111442906303485008554 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1791015894896585528741 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_339
  · change dfs 4 34 16 2362864961185160833626 = true
    apply dfs_of_prune
    decide +kernel

theorem node_388 : dfs 4 35 15 111443073979142220458 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1772665564798925822554 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 34 16 2381408119234053383589 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_363

theorem node_389 : dfs 4 35 15 111731875551584279210 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1795723282408092259749 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_340
  · change dfs 4 34 16 2367572348694672124506 = true
    apply dfs_of_prune
    decide +kernel

theorem node_390 : dfs 4 35 15 111736744738843609770 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1795785145330353612197 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_341
  · change dfs 4 34 16 2367634211616861149786 = true
    apply dfs_of_prune
    decide +kernel

theorem node_391 : dfs 4 35 15 112037502295505023653 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1815070739887404959349 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_342
  · change dfs 4 34 16 2377696434137351240074 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_356

theorem node_392 : dfs 4 35 15 112228239044337051045 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1786264203742929384842 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_336
  · change dfs 4 34 16 2404230130213632445045 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_374

theorem node_393 : dfs 4 35 15 112383278980309231013 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1786260263093546939786 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_335
  · change dfs 4 34 16 2404226189563666991733 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_373

theorem node_394 : dfs 4 35 15 113079380360387970677 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1781000698711939812010 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_333
  · change dfs 4 34 16 2435860113332129428821 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_379

theorem node_395 : dfs 4 35 15 113173577720604756597 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1787652911186718841514 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_337
  · change dfs 4 34 16 2442512325804974843221 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_381

theorem node_396 : dfs 4 35 15 115342045015323571541 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1927203615278350120277 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_344
  · change dfs 4 34 16 2379148845085756312234 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_360

theorem node_397 : dfs 4 35 15 120008775335507817813 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1783365592093683264170 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_334
  · change dfs 4 34 16 2364438030416937833813 = true
    apply dfs_of_prune
    decide +kernel

theorem node_398 : dfs 4 35 15 148200307897508694698 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2385758235832284960165 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_366
  · change dfs 4 34 16 2957607302118557526618 = true
    apply dfs_of_prune
    decide +kernel

theorem node_399 : dfs 4 35 15 148243486251628018058 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2382698435434579075749 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_365
  · change dfs 4 34 16 2954547501721283091802 = true
    apply dfs_of_prune
    decide +kernel

theorem node_400 : dfs 4 35 15 148255352197482908330 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2361956439121451637338 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 34 16 2970698993557736433061 = true
    apply dfs_of_prune
    decide +kernel

theorem node_401 : dfs 4 35 15 148324172812333249930 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2363305750720568315226 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 34 16 2972048305155891311269 = true
    apply dfs_of_prune
    decide +kernel

theorem node_402 : dfs 4 35 15 148337683611760883082 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2386154763430763475621 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_368
  · change dfs 4 34 16 2958003829717205470554 = true
    apply dfs_of_prune
    decide +kernel

theorem node_403 : dfs 4 35 15 148342586900399086250 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2381257662059758540197 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_362
  · change dfs 4 34 16 2953106728348342233690 = true
    apply dfs_of_prune
    decide +kernel

theorem node_404 : dfs 4 35 15 148625913987375723914 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2386154763430763475621 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_368
  · change dfs 4 34 16 2958003829717205470554 = true
    apply dfs_of_prune
    decide +kernel

theorem node_405 : dfs 4 35 15 148633619364897978762 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2382415834557554270885 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_364
  · change dfs 4 34 16 2954264900845072899418 = true
    apply dfs_of_prune
    decide +kernel

theorem node_406 : dfs 4 35 15 148668698183890007434 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2364278528240281668954 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 34 16 2973021082675202011813 = true
    apply dfs_of_prune
    decide +kernel

theorem node_407 : dfs 4 35 15 148903405895069250213 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2405763992913379149429 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_378
  · change dfs 4 34 16 2968389687163019245962 = true
    apply dfs_of_prune
    decide +kernel

theorem node_408 : dfs 4 35 15 148916916693942973093 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2399711155013153015413 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_369
  · change dfs 4 34 16 2962336849264873486730 = true
    apply dfs_of_prune
    decide +kernel

theorem node_409 : dfs 4 35 15 148917525823387968165 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2405702103602863179381 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_377
  · change dfs 4 34 16 2968327797852526705034 = true
    apply dfs_of_prune
    decide +kernel

theorem node_410 : dfs 4 35 15 148918933198266868389 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2372036007537377114506 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_347
  · change dfs 4 34 16 2990001934010231981685 = true
    apply dfs_of_prune
    decide +kernel

theorem node_411 : dfs 4 35 15 148919027824985953701 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2405672443177170193013 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_376
  · change dfs 4 34 16 2968298137426877920650 = true
    apply dfs_of_prune
    decide +kernel

theorem node_412 : dfs 4 35 15 148969271039774732965 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2378138912798938937738 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_358
  · change dfs 4 34 16 2996104839270006867573 = true
    apply dfs_of_prune
    decide +kernel

theorem node_413 : dfs 4 35 15 149133652426147410597 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2404285686335709464181 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_375
  · change dfs 4 34 16 2966911380585320200586 = true
    apply dfs_of_prune
    decide +kernel

theorem node_414 : dfs 4 35 15 149135200607603053989 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2401925448287332158069 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_372
  · change dfs 4 34 16 2964551142536771450250 = true
    apply dfs_of_prune
    decide +kernel

theorem node_415 : dfs 4 35 15 149205147070228902565 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2400864076518296733301 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_370
  · change dfs 4 34 16 2963489770768943462794 = true
    apply dfs_of_prune
    decide +kernel

theorem node_416 : dfs 4 35 15 149257501415926444709 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2401197342890726344309 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_371
  · change dfs 4 34 16 2963823037141364685194 = true
    apply dfs_of_prune
    decide +kernel

theorem node_417 : dfs 4 35 15 149972868507807073909 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2371296509070645463722 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_346
  · change dfs 4 34 16 3026155923690835080533 = true
    apply dfs_of_prune
    decide +kernel

theorem node_418 : dfs 4 35 15 150074955963609467509 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2372232105505315969706 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_348
  · change dfs 4 34 16 3027091520124778882389 = true
    apply dfs_of_prune
    decide +kernel

theorem node_419 : dfs 4 35 15 150265514522909428341 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2376359654564597947050 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_353
  · change dfs 4 34 16 3031219069182467024213 = true
    apply dfs_of_prune
    decide +kernel

theorem node_420 : dfs 4 35 15 150279025321705556597 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2373315221215748905642 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_349
  · change dfs 4 34 16 3028174635835111155029 = true
    apply dfs_of_prune
    decide +kernel

theorem node_421 : dfs 4 35 15 150363186339761179253 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2441407395782353134933 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_380
  · change dfs 4 34 16 2967139601884596492970 = true
    apply dfs_of_prune
    decide +kernel

theorem node_422 : dfs 4 35 15 152232747000239138133 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2370826368893418048170 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_345
  · change dfs 4 34 16 3099472759809059222869 = true
    apply dfs_of_prune
    decide +kernel

theorem node_423 : dfs 4 35 15 152336329791878374741 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2378104185892590946986 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_357
  · change dfs 4 34 16 3106750576805547767125 = true
    apply dfs_of_prune
    decide +kernel

theorem node_424 : dfs 4 35 15 152371619717686928725 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2376947323738311461546 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_355
  · change dfs 4 34 16 3105593714651265660245 = true
    apply dfs_of_prune
    decide +kernel

theorem node_425 : dfs 4 35 15 152589382393095451989 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2373334697964739054250 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_350
  · change dfs 4 34 16 3101981088878908061013 = true
    apply dfs_of_prune
    decide +kernel

theorem node_426 : dfs 4 35 15 152659997427877147989 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2511581695726204400981 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_382
  · change dfs 4 34 16 2963526925534583671466 = true
    apply dfs_of_prune
    decide +kernel

theorem node_427 : dfs 4 35 15 152660588965518812501 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2373492499874163559082 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_351
  · change dfs 4 34 16 3102138890787120379221 = true
    apply dfs_of_prune
    decide +kernel

theorem node_428 : dfs 4 35 15 156899026519800051029 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2378876570820865075882 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_359
  · change dfs 4 34 16 2959949009144157394261 = true
    apply dfs_of_prune
    decide +kernel

theorem node_429 : dfs 4 35 15 156902263482926921045 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2373661402452388915882 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_352
  · change dfs 4 34 16 2954733840775643485525 = true
    apply dfs_of_prune
    decide +kernel

theorem node_430 : dfs 4 35 15 157277144171174081877 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 2376555528163199396522 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_354
  · change dfs 4 34 16 2957627966485910934869 = true
    apply dfs_of_prune
    decide +kernel

theorem node_431 : dfs 4 36 14 4650576111129152170 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 74336869327915670106 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 35 15 112383278980309231013 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_393

theorem node_432 : dfs 4 36 14 4762158944876579445 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 78445770705400931669 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_384
  · change dfs 4 35 15 111304033587663559338 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_385

theorem node_433 : dfs 4 36 14 4911693492652778837 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 74468375902644701866 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_383
  · change dfs 4 35 15 120008775335507817813 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_397

theorem node_434 : dfs 4 36 14 6959915563257607562 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 112037502295505023653 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_391
  · change dfs 4 35 15 147778068938666626394 = true
    apply dfs_of_prune
    decide +kernel

theorem node_435 : dfs 4 36 14 6965334922895907498 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 111088790955214711386 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 35 15 149135200607603053989 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_414

theorem node_436 : dfs 4 36 14 6978527000714193578 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 112228239044337051045 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_392
  · change dfs 4 35 15 147968805687507180122 = true
    apply dfs_of_prune
    decide +kernel

theorem node_437 : dfs 4 36 14 7004586911823475365 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 113079380360387970677 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_394
  · change dfs 4 35 15 148243486251628018058 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_399

theorem node_438 : dfs 4 36 14 7015116402102478245 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 113173577720604756597 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_395
  · change dfs 4 35 15 148337683611760883082 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_402

theorem node_439 : dfs 4 36 14 7069855730716804725 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 115342045015323571541 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_396
  · change dfs 4 35 15 148200307897508694698 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_398

theorem node_440 : dfs 4 36 14 7073631453655943797 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 111731875551584279210 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_389
  · change dfs 4 35 15 152660588965518812501 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_427

theorem node_441 : dfs 4 36 14 7087069684804717173 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 111442906303485008554 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_387
  · change dfs 4 35 15 152371619717686928725 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_424

theorem node_442 : dfs 4 36 14 7217536501866472789 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 111361864050063805098 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_386
  · change dfs 4 35 15 156902263482926921045 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_429

theorem node_443 : dfs 4 36 14 7218875157265446229 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 111736744738843609770 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_390
  · change dfs 4 35 15 157277144171174081877 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_430

theorem node_444 : dfs 4 36 14 7496851075869881685 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 111443073979142220458 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_388
  · change dfs 4 35 15 147760101374648800597 = true
    apply dfs_of_prune
    decide +kernel

theorem node_445 : dfs 4 36 14 9262262129556540074 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148123845622753876570 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 35 15 186170255275147437477 = true
    apply dfs_of_prune
    decide +kernel

theorem node_446 : dfs 4 36 14 9266811904410940810 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 149257501415926444709 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_416
  · change dfs 4 35 15 184998068059052133722 = true
    apply dfs_of_prune
    decide +kernel

theorem node_447 : dfs 4 36 14 9267612349053630858 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 147766011693766630746 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 35 15 185812421346222842533 = true
    apply dfs_of_prune
    decide +kernel

theorem node_448 : dfs 4 36 14 9270189604140119434 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 149205147070228902565 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_415
  · change dfs 4 35 15 184945713713413311834 = true
    apply dfs_of_prune
    decide +kernel

theorem node_449 : dfs 4 36 14 9271177932109601450 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 147982279102633814618 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 35 15 186028688755022157221 = true
    apply dfs_of_prune
    decide +kernel

theorem node_450 : dfs 4 36 14 9271388071974057354 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 149133652426147410597 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_413
  · change dfs 4 35 15 184874219069325790554 = true
    apply dfs_of_prune
    decide +kernel

theorem node_451 : dfs 4 36 14 9272516587524262570 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 147980818951187376730 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 35 15 186027228603585222053 = true
    apply dfs_of_prune
    decide +kernel

theorem node_452 : dfs 4 36 14 9275925760628665002 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 147676071711191226970 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 35 15 185722481363933046181 = true
    apply dfs_of_prune
    decide +kernel

theorem node_453 : dfs 4 36 14 9282669061157337482 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148917525823387968165 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_409
  · change dfs 4 35 15 184658092466834398554 = true
    apply dfs_of_prune
    decide +kernel

theorem node_454 : dfs 4 36 14 9283422093470685866 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148919027824985953701 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_411
  · change dfs 4 35 15 184659594468442450522 = true
    apply dfs_of_prune
    decide +kernel

theorem node_455 : dfs 4 36 14 9283700403055785354 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148916916693942973093 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_408
  · change dfs 4 35 15 184657483337395817818 = true
    apply dfs_of_prune
    decide +kernel

theorem node_456 : dfs 4 36 14 9284826303054640522 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148969271039774732965 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_412
  · change dfs 4 35 15 184709837682900421978 = true
    apply dfs_of_prune
    decide +kernel

theorem node_457 : dfs 4 36 14 9285626747428895114 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148918933198266868389 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_410
  · change dfs 4 35 15 184659499841722604890 = true
    apply dfs_of_prune
    decide +kernel

theorem node_458 : dfs 4 36 14 9285635547817413290 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 147767252011493186138 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 35 15 185813661664167503269 = true
    apply dfs_of_prune
    decide +kernel

theorem node_459 : dfs 4 36 14 9289048427611190666 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148903405895069250213 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_407
  · change dfs 4 35 15 184643972538505317722 = true
    apply dfs_of_prune
    decide +kernel

theorem node_460 : dfs 4 36 14 9301392502342985125 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148668698183890007434 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_406
  · change dfs 4 35 15 187291568588537301621 = true
    apply dfs_of_prune
    decide +kernel

theorem node_461 : dfs 4 36 14 9305937866248528549 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148633619364897978762 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_405
  · change dfs 4 35 15 187256489769584199285 = true
    apply dfs_of_prune
    decide +kernel

theorem node_462 : dfs 4 36 14 9307725689498281381 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148324172812333249930 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_401
  · change dfs 4 35 15 186947043217106373237 = true
    apply dfs_of_prune
    decide +kernel

theorem node_463 : dfs 4 36 14 9308200128585487781 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 150363186339761179253 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_421
  · change dfs 4 35 15 185527292230627931530 = true
    apply dfs_of_prune
    decide +kernel

theorem node_464 : dfs 4 36 14 9308200128719705509 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 150074955963609467509 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_418
  · change dfs 4 35 15 185239061854476219786 = true
    apply dfs_of_prune
    decide +kernel

theorem node_465 : dfs 4 36 14 9310429921037169317 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 149972868507807073909 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_417
  · change dfs 4 35 15 185136974399047121290 = true
    apply dfs_of_prune
    decide +kernel

theorem node_466 : dfs 4 36 14 9311952212061431205 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148625913987375723914 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_404
  · change dfs 4 35 15 187248784392131545717 = true
    apply dfs_of_prune
    decide +kernel

theorem node_467 : dfs 4 36 14 9325101821369570725 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 150279025321705556597 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_420
  · change dfs 4 35 15 185443131212610581898 = true
    apply dfs_of_prune
    decide +kernel

theorem node_468 : dfs 4 36 14 9325453665186403749 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 150265514522909428341 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_419
  · change dfs 4 35 15 185429620413642487178 = true
    apply dfs_of_prune
    decide +kernel

theorem node_469 : dfs 4 36 14 9373844963303967349 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 152232747000239138133 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_422
  · change dfs 4 35 15 185091009882501765802 = true
    apply dfs_of_prune
    decide +kernel

theorem node_470 : dfs 4 36 14 9379815311476688501 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 152659997427877147989 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_426
  · change dfs 4 35 15 185518260309552663210 = true
    apply dfs_of_prune
    decide +kernel

theorem node_471 : dfs 4 36 14 9391540503508781685 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148342586900399086250 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_403
  · change dfs 4 35 15 189271300314586326357 = true
    apply dfs_of_prune
    decide +kernel

theorem node_472 : dfs 4 36 14 9395237061582211701 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 152336329791878374741 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_423
  · change dfs 4 35 15 185194592673721572010 = true
    apply dfs_of_prune
    decide +kernel

theorem node_473 : dfs 4 36 14 9397581220391765621 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 152589382393095451989 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_425
  · change dfs 4 35 15 185447645274769787562 = true
    apply dfs_of_prune
    decide +kernel

theorem node_474 : dfs 4 36 14 9523379511080166741 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 148255352197482908330 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_400
  · change dfs 4 35 15 193795751630346024277 = true
    apply dfs_of_prune
    decide +kernel

theorem node_475 : dfs 4 36 14 9523617005592290645 = true := by
  apply dfs_of_children (fuel:=35)
  · change dfs 4 35 15 156899026519800051029 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_428
  · change dfs 4 35 15 185145603383564536490 = true
    apply dfs_of_prune
    decide +kernel

theorem node_476 : dfs 4 37 13 293484584879576485 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 4762158944876579445 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_432
  · change dfs 4 36 14 6959915563257607562 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_434

theorem node_477 : dfs 4 37 13 298827010016365173 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 4911693492652778837 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_433
  · change dfs 4 36 14 6965334922895907498 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_435

theorem node_478 : dfs 4 37 13 306638594512188757 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 4650576111129152170 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_431
  · change dfs 4 36 14 7496851075869881685 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_444

theorem node_479 : dfs 4 37 13 434991183948483242 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 6930299525381401178 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 9308200128719705509 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_464

theorem node_480 : dfs 4 37 13 435289838746688170 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 6947553061840824922 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 9325453665186403749 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_468

theorem node_481 : dfs 4 37 13 435948755463015082 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 6929825086068054618 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 9307725689498281381 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_462

theorem node_482 : dfs 4 37 13 436186798674064778 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 7004586911823475365 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_437
  · change dfs 4 36 14 9238372327080152410 = true
    apply dfs_of_prune
    decide +kernel

theorem node_483 : dfs 4 37 13 436476795914201770 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 7015116402102478245 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_438
  · change dfs 4 36 14 9248901817367681626 = true
    apply dfs_of_prune
    decide +kernel

theorem node_484 : dfs 4 37 13 437505897860276901 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 7069855730716804725 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_439
  · change dfs 4 36 14 9267612349053630858 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_447

theorem node_485 : dfs 4 37 13 437671378692515237 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 7087069684804717173 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_441
  · change dfs 4 36 14 9284826303054640522 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_456

theorem node_486 : dfs 4 37 13 438356236964255141 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 7073631453655943797 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_440
  · change dfs 4 36 14 9271388071974057354 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_450

theorem node_487 : dfs 4 37 13 442824550352504437 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 7218875157265446229 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_443
  · change dfs 4 36 14 9272516587524262570 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_451

theorem node_488 : dfs 4 37 13 442942198092221045 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 7217536501866472789 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_442
  · change dfs 4 36 14 9271177932109601450 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_449

theorem node_489 : dfs 4 37 13 470227129964328277 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 6978527000714193578 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_436
  · change dfs 4 36 14 9248341213008188757 = true
    apply dfs_of_prune
    decide +kernel

theorem node_490 : dfs 4 37 13 579405026822544042 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9253396071054518874 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 11631296674400097701 = true
    apply dfs_of_prune
    decide +kernel

theorem node_491 : dfs 4 37 13 579439969610413450 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9230350290118069594 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 11608250893540438693 = true
    apply dfs_of_prune
    decide +kernel

theorem node_492 : dfs 4 37 13 579464400449919658 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9325101821369570725 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_467
  · change dfs 4 36 14 11558887236643269210 = true
    apply dfs_of_prune
    decide +kernel

theorem node_493 : dfs 4 37 13 579580158419765930 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9301392502342985125 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_460
  · change dfs 4 36 14 11535177917698759258 = true
    apply dfs_of_prune
    decide +kernel

theorem node_494 : dfs 4 37 13 579744534331308426 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9253020570648730970 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 11630921174004376229 = true
    apply dfs_of_prune
    decide +kernel

theorem node_495 : dfs 4 37 13 580029034053413546 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9311952212061431205 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_466
  · change dfs 4 36 14 11545737627326634586 = true
    apply dfs_of_prune
    decide +kernel

theorem node_496 : dfs 4 37 13 580184339001293194 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9238383871868165466 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 11616284475207033509 = true
    apply dfs_of_prune
    decide +kernel

theorem node_497 : dfs 4 37 13 580214267388975786 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9235381672511482458 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 11613282275924170149 = true
    apply dfs_of_prune
    decide +kernel

theorem node_498 : dfs 4 37 13 580232271897627306 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9308200128585487781 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_463
  · change dfs 4 36 14 11541985543943006810 = true
    apply dfs_of_prune
    decide +kernel

theorem node_499 : dfs 4 37 13 580301986749920650 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9310429921037169317 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_465
  · change dfs 4 36 14 11544215336293846362 = true
    apply dfs_of_prune
    decide +kernel

theorem node_500 : dfs 4 37 13 580565320859224746 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9247349306877106778 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 11625249910183601573 = true
    apply dfs_of_prune
    decide +kernel

theorem node_501 : dfs 4 37 13 580606551445387658 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9305937866248528549 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_461
  · change dfs 4 36 14 11539723281571929434 = true
    apply dfs_of_prune
    decide +kernel

theorem node_502 : dfs 4 37 13 580765430878927242 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9235358015831235930 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 36 14 11613258619244683941 = true
    apply dfs_of_prune
    decide +kernel

theorem node_503 : dfs 4 37 13 581583015342813861 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9397581220391765621 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_473
  · change dfs 4 36 14 11595337838638053770 = true
    apply dfs_of_prune
    decide +kernel

theorem node_504 : dfs 4 37 13 581621085969687205 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9285626747428895114 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_457
  · change dfs 4 36 14 11699556147787892341 = true
    apply dfs_of_prune
    decide +kernel

theorem node_505 : dfs 4 37 13 581627000105784741 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9395237061582211701 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_472
  · change dfs 4 36 14 11592993679866770826 = true
    apply dfs_of_prune
    decide +kernel

theorem node_506 : dfs 4 37 13 581714961031288229 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9373844963303967349 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_469
  · change dfs 4 36 14 11571601581684995466 = true
    apply dfs_of_prune
    decide +kernel

theorem node_507 : dfs 4 37 13 581726093587096997 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9289048427611190666 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_459
  · change dfs 4 36 14 11702977827976874613 = true
    apply dfs_of_prune
    decide +kernel

theorem node_508 : dfs 4 37 13 581786566734816677 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9266811904410940810 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_446
  · change dfs 4 36 14 11680741304856840821 = true
    apply dfs_of_prune
    decide +kernel

theorem node_509 : dfs 4 37 13 582462624656437925 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9282669061157337482 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_453
  · change dfs 4 36 14 11696598461502015093 = true
    apply dfs_of_prune
    decide +kernel

theorem node_510 : dfs 4 37 13 582470462967424421 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9391540503508781685 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_471
  · change dfs 4 36 14 11589297121755035018 = true
    apply dfs_of_prune
    decide +kernel

theorem node_511 : dfs 4 37 13 582843197409306021 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9270189604140119434 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_448
  · change dfs 4 36 14 11684119004568717941 = true
    apply dfs_of_prune
    decide +kernel

end Rule30GoldenBudgetDAG4Part0003Research
