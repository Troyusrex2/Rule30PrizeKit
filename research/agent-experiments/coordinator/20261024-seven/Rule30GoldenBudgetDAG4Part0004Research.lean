import Rule30GoldenBudgetDAG4Part0003Research
import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudgetDAG4Part0004Research
open Rule30GoldenCompactBudgetResearch

theorem node_512 : dfs 4 37 13 583010868638425765 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9379815311476688501 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_470
  · change dfs 4 36 14 11577571929789921674 = true
    apply dfs_of_prune
    decide +kernel

theorem node_513 : dfs 4 37 13 583124672386016677 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9283700403055785354 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_455
  · change dfs 4 36 14 11697629803417274997 = true
    apply dfs_of_prune
    decide +kernel

theorem node_514 : dfs 4 37 13 586977671575341685 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9523617005592290645 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_475
  · change dfs 4 36 14 11577258435834370730 = true
    apply dfs_of_prune
    decide +kernel

theorem node_515 : dfs 4 37 13 587057386168076917 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9523379511080166741 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_474
  · change dfs 4 36 14 11577020941323295402 = true
    apply dfs_of_prune
    decide +kernel

theorem node_516 : dfs 4 37 13 587532375191538293 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9283422093470685866 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_454
  · change dfs 4 36 14 11841466681906603349 = true
    apply dfs_of_prune
    decide +kernel

theorem node_517 : dfs 4 37 13 594868970663900501 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9262262129556540074 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_445
  · change dfs 4 36 14 12108537094297269589 = true
    apply dfs_of_prune
    decide +kernel

theorem node_518 : dfs 4 37 13 595167625557484885 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9285635547817413290 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_458
  · change dfs 4 36 14 12131910512402920789 = true
    apply dfs_of_prune
    decide +kernel

theorem node_519 : dfs 4 37 13 613840940756006229 = true := by
  apply dfs_of_children (fuel:=36)
  · change dfs 4 36 14 9275925760628665002 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_452
  · change dfs 4 36 14 11545739972918465877 = true
    apply dfs_of_prune
    decide +kernel

theorem node_520 : dfs 4 38 12 18246693248404138 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 289052590944901722 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 37 13 437671378692515237 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_485

theorem node_521 : dfs 4 38 12 18249089839094442 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 293484584879576485 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_476
  · change dfs 4 37 13 433096173368322650 = true
    apply dfs_of_prune
    decide +kernel

theorem node_522 : dfs 4 38 12 18342788283028901 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 298827010016365173 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_477
  · change dfs 4 37 13 436186798674064778 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_482

theorem node_523 : dfs 4 38 12 18624237781993077 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 306638594512188757 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_478
  · change dfs 4 37 13 434991183948483242 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_479

theorem node_524 : dfs 4 38 12 27209224581462410 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 437505897860276901 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_484
  · change dfs 4 37 13 577117486338956634 = true
    apply dfs_of_prune
    decide +kernel

theorem node_525 : dfs 4 38 12 27253540315290282 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 438356236964255141 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_486
  · change dfs 4 37 13 577967825435175514 = true
    apply dfs_of_prune
    decide +kernel

theorem node_526 : dfs 4 38 12 27279593317251466 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 433002298229546330 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 37 13 581621085969687205 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_504

theorem node_527 : dfs 4 38 12 27349987537769893 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 442942198092221045 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_488
  · change dfs 4 37 13 580301986749920650 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_499

theorem node_528 : dfs 4 38 12 27431350322115237 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 442824550352504437 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_487
  · change dfs 4 37 13 580184339001293194 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_496

theorem node_529 : dfs 4 38 12 27700431393213045 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 435289838746688170 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_480
  · change dfs 4 37 13 595167625557484885 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_518

theorem node_530 : dfs 4 38 12 28194722265867605 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 470227129964328277 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_489
  · change dfs 4 37 13 580565320859224746 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_500

theorem node_531 : dfs 4 38 12 28241451517912405 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 435948755463015082 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_481
  · change dfs 4 37 13 613840940756006229 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_519

theorem node_532 : dfs 4 38 12 29329770455659861 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 436476795914201770 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_483
  · change dfs 4 37 13 578340184204334421 = true
    apply dfs_of_prune
    decide +kernel

theorem node_533 : dfs 4 38 12 29364954831942997 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 433662046158280021 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 37 13 580029034053413546 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_495

theorem node_534 : dfs 4 38 12 36181995634207402 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 583124672386016677 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_513
  · change dfs 4 37 13 722736260856830554 = true
    apply dfs_of_prune
    decide +kernel

theorem node_535 : dfs 4 38 12 36201168101800330 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 583010868638425765 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_512
  · change dfs 4 37 13 722622457107537242 = true
    apply dfs_of_prune
    decide +kernel

theorem node_536 : dfs 4 38 12 36216759112260266 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 581627000105784741 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_505
  · change dfs 4 37 13 721238588585093722 = true
    apply dfs_of_prune
    decide +kernel

theorem node_537 : dfs 4 38 12 36217180008393386 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 582843197409306021 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_511
  · change dfs 4 37 13 722454785880119898 = true
    apply dfs_of_prune
    decide +kernel

theorem node_538 : dfs 4 38 12 36225907389991594 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 581786566734816677 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_508
  · change dfs 4 37 13 721398155206023770 = true
    apply dfs_of_prune
    decide +kernel

theorem node_539 : dfs 4 38 12 36260404562578090 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 582470462967424421 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_510
  · change dfs 4 37 13 722082051438369370 = true
    apply dfs_of_prune
    decide +kernel

theorem node_540 : dfs 4 38 12 36261091757886122 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 577282967096613466 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 37 13 725901754844226981 = true
    apply dfs_of_prune
    decide +kernel

theorem node_541 : dfs 4 38 12 36263041672022698 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 577216858961914458 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 37 13 725835646705685925 = true
    apply dfs_of_prune
    decide +kernel

theorem node_542 : dfs 4 38 12 36263359499840170 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 581726093587096997 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_507
  · change dfs 4 37 13 721337682074688090 = true
    apply dfs_of_prune
    decide +kernel

theorem node_543 : dfs 4 38 12 36263488348576426 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 581714961031288229 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_506
  · change dfs 4 37 13 721326549520034394 = true
    apply dfs_of_prune
    decide +kernel

theorem node_544 : dfs 4 38 12 36280882696975754 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 581583015342813861 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_503
  · change dfs 4 37 13 721194603827907930 = true
    apply dfs_of_prune
    decide +kernel

theorem node_545 : dfs 4 38 12 36285418189010314 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 582462624656437925 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_509
  · change dfs 4 37 13 722074213118725466 = true
    apply dfs_of_prune
    decide +kernel

theorem node_546 : dfs 4 38 12 36317363858351525 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 586977671575341685 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_514
  · change dfs 4 37 13 724337460232484234 = true
    apply dfs_of_prune
    decide +kernel

theorem node_547 : dfs 4 38 12 36323376812610981 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 579439969610413450 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_491
  · change dfs 4 37 13 730310557151087221 = true
    apply dfs_of_prune
    decide +kernel

theorem node_548 : dfs 4 38 12 36333718005719717 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 580765430878927242 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_502
  · change dfs 4 37 13 731636018417141365 = true
    apply dfs_of_prune
    decide +kernel

theorem node_549 : dfs 4 38 12 36334371914208677 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 587532375191538293 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_516
  · change dfs 4 37 13 724892163848713610 = true
    apply dfs_of_prune
    decide +kernel

theorem node_550 : dfs 4 38 12 36357186792510885 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 587057386168076917 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_515
  · change dfs 4 37 13 724417174825776522 = true
    apply dfs_of_prune
    decide +kernel

theorem node_551 : dfs 4 38 12 36368180827435685 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 580606551445387658 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_501
  · change dfs 4 37 13 731477138990253685 = true
    apply dfs_of_prune
    decide +kernel

theorem node_552 : dfs 4 38 12 36394569110565541 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 579744534331308426 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_494
  · change dfs 4 37 13 730615121871980149 = true
    apply dfs_of_prune
    decide +kernel

theorem node_553 : dfs 4 38 12 36638636291475061 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 594868970663900501 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_517
  · change dfs 4 37 13 723221560100194986 = true
    apply dfs_of_prune
    decide +kernel

theorem node_554 : dfs 4 38 12 36685640415660661 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 580214267388975786 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_497
  · change dfs 4 37 13 740092054182995285 = true
    apply dfs_of_prune
    decide +kernel

theorem node_555 : dfs 4 38 12 36687701999979125 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 579464400449919658 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_492
  · change dfs 4 37 13 739342187261764949 = true
    apply dfs_of_prune
    decide +kernel

theorem node_556 : dfs 4 38 12 36707630647954037 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 579405026822544042 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_490
  · change dfs 4 37 13 739282813633340757 = true
    apply dfs_of_prune
    decide +kernel

theorem node_557 : dfs 4 38 12 36709005044041333 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 580232271897627306 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_498
  · change dfs 4 37 13 740110058680153429 = true
    apply dfs_of_prune
    decide +kernel

theorem node_558 : dfs 4 38 12 37245901993059669 = true := by
  apply dfs_of_children (fuel:=37)
  · change dfs 4 37 13 579580158419765930 = true
    exact Rule30GoldenBudgetDAG4Part0003Research.node_493
  · change dfs 4 37 13 757472343718524245 = true
    apply dfs_of_prune
    decide +kernel

theorem node_559 : dfs 4 39 11 579841343969962 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 9054114041506394 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 18342788283028901 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_522

theorem node_560 : dfs 4 39 11 1136144767415690 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 18142676085329242 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 27431350322115237 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_528

theorem node_561 : dfs 4 39 11 1140592274135722 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 18061313296247386 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 27349987537769893 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_527

theorem node_562 : dfs 4 39 11 1149173207839397 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 18624237781993077 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_523
  · change dfs 4 38 12 27209224581462410 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_524

theorem node_563 : dfs 4 39 11 1166965453703797 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 18249089839094442 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_521
  · change dfs 4 38 12 28241451517912405 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_531

theorem node_564 : dfs 4 39 11 1204363949942101 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 18246693248404138 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_520
  · change dfs 4 38 12 29364954831942997 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_533

theorem node_565 : dfs 4 39 11 1698373233363626 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 27028689611610714 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 36317363858351525 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_546

theorem node_566 : dfs 4 39 11 1699032510892714 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 27034702565780058 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 36323376812610981 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_547

theorem node_567 : dfs 4 39 11 1703527129462154 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 27105894876138842 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 36394569110565541 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_552

theorem node_568 : dfs 4 39 11 1705741250812586 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 27068512550988378 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 36357186792510885 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_550

theorem node_569 : dfs 4 39 11 1709374649980325 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 27700431393213045 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_529
  · change dfs 4 38 12 36285418189010314 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_545

theorem node_570 : dfs 4 39 11 1709924138005157 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 27279593317251466 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_526
  · change dfs 4 38 12 36709005044041333 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_557

theorem node_571 : dfs 4 39 11 1725483003251317 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 27253540315290282 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_525
  · change dfs 4 38 12 37245901993059669 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_558

theorem node_572 : dfs 4 39 11 1730430803217013 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 28194722265867605 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_530
  · change dfs 4 38 12 36216759112260266 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_536

theorem node_573 : dfs 4 39 11 1765114880107861 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 29329770455659861 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_532
  · change dfs 4 38 12 36225907389991594 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_538

theorem node_574 : dfs 4 39 11 2262044674258314 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36157074594811226 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 45445748831597221 = true
    apply dfs_of_prune
    decide +kernel

theorem node_575 : dfs 4 39 11 2262044674520458 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36042725381328218 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 45331399626502821 = true
    apply dfs_of_prune
    decide +kernel

theorem node_576 : dfs 4 39 11 2263219415354026 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36334371914208677 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_549
  · change dfs 4 38 12 45060096206219866 = true
    apply dfs_of_prune
    decide +kernel

theorem node_577 : dfs 4 39 11 2263522143287690 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36333718005719717 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_548
  · change dfs 4 38 12 45059442297167194 = true
    apply dfs_of_prune
    decide +kernel

theorem node_578 : dfs 4 39 11 2266459969006250 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36078494943959642 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 38 12 45367169186637221 = true
    apply dfs_of_prune
    decide +kernel

theorem node_579 : dfs 4 39 11 2266992478942602 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36368180827435685 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_551
  · change dfs 4 38 12 45093905110617434 = true
    apply dfs_of_prune
    decide +kernel

theorem node_580 : dfs 4 39 11 2271164964840869 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36687701999979125 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_555
  · change dfs 4 38 12 45272688795219338 = true
    apply dfs_of_prune
    decide +kernel

theorem node_581 : dfs 4 39 11 2271954968158885 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36201168101800330 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_535
  · change dfs 4 38 12 45630579832948341 = true
    apply dfs_of_prune
    decide +kernel

theorem node_582 : dfs 4 39 11 2272324603401637 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36707630647954037 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_556
  · change dfs 4 38 12 45292617443751306 = true
    apply dfs_of_prune
    decide +kernel

theorem node_583 : dfs 4 39 11 2272470632867237 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36280882696975754 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_544
  · change dfs 4 38 12 45710294423800437 = true
    apply dfs_of_prune
    decide +kernel

theorem node_584 : dfs 4 39 11 2275073114682021 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36638636291475061 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_553
  · change dfs 4 38 12 45223623090944394 = true
    apply dfs_of_prune
    decide +kernel

theorem node_585 : dfs 4 39 11 2275416980411813 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36685640415660661 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_554
  · change dfs 4 38 12 45270627210933642 = true
    apply dfs_of_prune
    decide +kernel

theorem node_586 : dfs 4 39 11 2292865360546421 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36263488348576426 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_543
  · change dfs 4 38 12 46255850027394389 = true
    apply dfs_of_prune
    decide +kernel

theorem node_587 : dfs 4 39 11 2294892585191029 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36263041672022698 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_541
  · change dfs 4 38 12 46255403350750549 = true
    apply dfs_of_prune
    decide +kernel

theorem node_588 : dfs 4 39 11 2323555118871893 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36260404562578090 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_539
  · change dfs 4 38 12 47378666147198293 = true
    apply dfs_of_prune
    decide +kernel

theorem node_589 : dfs 4 39 11 2330263856784725 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36261091757886122 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_540
  · change dfs 4 38 12 47379353341424981 = true
    apply dfs_of_prune
    decide +kernel

theorem node_590 : dfs 4 39 11 2393264585618773 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36263359499840170 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_542
  · change dfs 4 38 12 45129821271250261 = true
    apply dfs_of_prune
    decide +kernel

theorem node_591 : dfs 4 39 11 2393986136700245 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36181995634207402 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_534
  · change dfs 4 38 12 45048457415972181 = true
    apply dfs_of_prune
    decide +kernel

theorem node_592 : dfs 4 39 11 2397834428708181 = true := by
  apply dfs_of_children (fuel:=38)
  · change dfs 4 38 12 36217180008393386 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_537
  · change dfs 4 38 12 45083641785963861 = true
    apply dfs_of_prune
    decide +kernel

theorem node_593 : dfs 4 40 10 37479299238517 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 579841343969962 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_559
  · change dfs 4 39 11 1204363949942101 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_564

theorem node_594 : dfs 4 40 10 71014404765066 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1149173207839397 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_562
  · change dfs 4 39 11 1694530976435546 = true
    apply dfs_of_prune
    decide +kernel

theorem node_595 : dfs 4 40 10 71670978225573 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1136144767415690 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_560
  · change dfs 4 39 11 1725483003251317 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_571

theorem node_596 : dfs 4 40 10 71874989348261 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1166965453703797 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_563
  · change dfs 4 39 11 1703527129462154 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_567

theorem node_597 : dfs 4 40 10 72938549496437 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1140592274135722 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_561
  · change dfs 4 39 11 1765114880107861 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_573

theorem node_598 : dfs 4 40 10 106284692359850 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1690622822668890 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 39 11 2271164964840869 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_580

theorem node_599 : dfs 4 40 10 106473654498698 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1709924138005157 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_570
  · change dfs 4 39 11 2255281906601306 = true
    apply dfs_of_prune
    decide +kernel

theorem node_600 : dfs 4 40 10 106477429021354 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1709374649980325 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_569
  · change dfs 4 39 11 2254732419869274 = true
    apply dfs_of_prune
    decide +kernel

theorem node_601 : dfs 4 40 10 107095868614053 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1730430803217013 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_572
  · change dfs 4 39 11 2266992478942602 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_579

theorem node_602 : dfs 4 40 10 107848043416181 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1705741250812586 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_568
  · change dfs 4 39 11 2330263856784725 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_589

theorem node_603 : dfs 4 40 10 107942532777589 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1699032510892714 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_566
  · change dfs 4 39 11 2323555118871893 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_588

theorem node_604 : dfs 4 40 10 110057284105557 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 1698373233363626 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_565
  · change dfs 4 39 11 2393264585618773 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_590

theorem node_605 : dfs 4 40 10 141383148942730 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2275073114682021 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_584
  · change dfs 4 39 11 2820430883278170 = true
    apply dfs_of_prune
    decide +kernel

theorem node_606 : dfs 4 40 10 141393366157994 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2275416980411813 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_585
  · change dfs 4 39 11 2820774749186650 = true
    apply dfs_of_prune
    decide +kernel

theorem node_607 : dfs 4 40 10 141477638142346 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2271954968158885 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_581
  · change dfs 4 39 11 2817312737287514 = true
    apply dfs_of_prune
    decide +kernel

theorem node_608 : dfs 4 40 10 141516309441194 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2272470632867237 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_583
  · change dfs 4 39 11 2817828401601114 = true
    apply dfs_of_prune
    decide +kernel

theorem node_609 : dfs 4 40 10 141661801110186 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2272324603401637 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_582
  · change dfs 4 39 11 2817682373290586 = true
    apply dfs_of_prune
    decide +kernel

theorem node_610 : dfs 4 40 10 141927986143909 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2294892585191029 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_587
  · change dfs 4 39 11 2831454260787594 = true
    apply dfs_of_prune
    decide +kernel

theorem node_611 : dfs 4 40 10 142039722403237 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2262044674258314 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_574
  · change dfs 4 39 11 2851382910093941 = true
    apply dfs_of_prune
    decide +kernel

theorem node_612 : dfs 4 40 10 142056902469029 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2262044674520458 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_575
  · change dfs 4 39 11 2851382909831797 = true
    apply dfs_of_prune
    decide +kernel

theorem node_613 : dfs 4 40 10 142157767160485 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2263522143287690 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_577
  · change dfs 4 39 11 2852860378564213 = true
    apply dfs_of_prune
    decide +kernel

theorem node_614 : dfs 4 40 10 142243733525925 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2292865360546421 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_586
  · change dfs 4 39 11 2829427036304778 = true
    apply dfs_of_prune
    decide +kernel

theorem node_615 : dfs 4 40 10 143393193018997 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2263219415354026 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_576
  · change dfs 4 39 11 2887742022415701 = true
    apply dfs_of_prune
    decide +kernel

theorem node_616 : dfs 4 40 10 145338292938069 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2393986136700245 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_591
  · change dfs 4 39 11 2824994698136234 = true
    apply dfs_of_prune
    decide +kernel

theorem node_617 : dfs 4 40 10 145510092154197 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2397834428708181 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_592
  · change dfs 4 39 11 2828842987522730 = true
    apply dfs_of_prune
    decide +kernel

theorem node_618 : dfs 4 40 10 149715402011989 = true := by
  apply dfs_of_children (fuel:=39)
  · change dfs 4 39 11 2266459969006250 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_578
  · change dfs 4 39 11 2820613830235477 = true
    apply dfs_of_prune
    decide +kernel

theorem node_619 : dfs 4 41 9 2279231772069 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 37479299238517 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_593
  · change dfs 4 40 10 71014404765066 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_594

theorem node_620 : dfs 4 41 9 4454239013546 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 71670978225573 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_595
  · change dfs 4 40 10 105755839388250 = true
    apply dfs_of_prune
    decide +kernel

theorem node_621 : dfs 4 41 9 4458936601258 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 71874989348261 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_596
  · change dfs 4 40 10 105959850158682 = true
    apply dfs_of_prune
    decide +kernel

theorem node_622 : dfs 4 41 9 4499729896869 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 72938549496437 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_597
  · change dfs 4 40 10 106473654498698 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_599

theorem node_623 : dfs 4 41 9 6642524834474 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 107095868614053 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_601
  · change dfs 4 40 10 141180729514586 = true
    apply dfs_of_prune
    decide +kernel

theorem node_624 : dfs 4 41 9 6677278283173 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 107848043416181 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_602
  · change dfs 4 40 10 141383148942730 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_605

theorem node_625 : dfs 4 41 9 6688535847589 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 107942532777589 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_603
  · change dfs 4 40 10 141477638142346 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_607

theorem node_626 : dfs 4 41 9 6745599854197 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 110057284105557 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_604
  · change dfs 4 40 10 141393366157994 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_606

theorem node_627 : dfs 4 41 9 6758484757109 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 106477429021354 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_600
  · change dfs 4 40 10 145510092154197 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_617

theorem node_628 : dfs 4 41 9 6898478150997 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 106284692359850 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_598
  · change dfs 4 40 10 149715402011989 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_618

theorem node_629 : dfs 4 41 9 7168658404693 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 105782181188949 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 40 10 141516309441194 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_608

theorem node_630 : dfs 4 41 9 8841543989642 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 141103352667482 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 40 10 177387236598437 = true
    apply dfs_of_prune
    decide +kernel

theorem node_631 : dfs 4 41 9 8843691391370 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 141927986143909 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_610
  · change dfs 4 40 10 176012847308122 = true
    apply dfs_of_prune
    decide +kernel

theorem node_632 : dfs 4 41 9 8852285524650 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 142039722403237 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_611
  · change dfs 4 40 10 176124583565914 = true
    apply dfs_of_prune
    decide +kernel

theorem node_633 : dfs 4 41 9 8853359340202 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 142056902469029 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_612
  · change dfs 4 40 10 176141763238490 = true
    apply dfs_of_prune
    decide +kernel

theorem node_634 : dfs 4 41 9 8854428890506 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 142157767160485 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_613
  · change dfs 4 40 10 176242627792218 = true
    apply dfs_of_prune
    decide +kernel

theorem node_635 : dfs 4 41 9 8855372520106 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 140920883456602 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 40 10 177204767806885 = true
    apply dfs_of_prune
    decide +kernel

theorem node_636 : dfs 4 41 9 8856983112362 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 142243733525925 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_614
  · change dfs 4 40 10 176328594336346 = true
    apply dfs_of_prune
    decide +kernel

theorem node_637 : dfs 4 41 9 8876284752549 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 143393193018997 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_615
  · change dfs 4 40 10 176928298023306 = true
    apply dfs_of_prune
    decide +kernel

theorem node_638 : dfs 4 41 9 8955360545397 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 145338292938069 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_616
  · change dfs 4 40 10 176674375031466 = true
    apply dfs_of_prune
    decide +kernel

theorem node_639 : dfs 4 41 9 8957508012661 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 141661801110186 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_609
  · change dfs 4 40 10 180694464243029 = true
    apply dfs_of_prune
    decide +kernel

end Rule30GoldenBudgetDAG4Part0004Research
