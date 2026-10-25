import Rule30GoldenBudgetDAG4Part0004Research
import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudgetDAG4Part0005Research
open Rule30GoldenCompactBudgetResearch

theorem node_640 : dfs 4 41 9 9356944258389 = true := by
  apply dfs_of_children (fuel:=40)
  · change dfs 4 40 10 141103992296789 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 40 10 176838120417962 = true
    apply dfs_of_prune
    decide +kernel

theorem node_641 : dfs 4 42 8 141521410730 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 2279231772069 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_619
  · change dfs 4 41 9 4409535703642 = true
    apply dfs_of_prune
    decide +kernel

theorem node_642 : dfs 4 42 8 277215513258 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 4499729896869 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_622
  · change dfs 4 41 9 6630033762906 = true
    apply dfs_of_prune
    decide +kernel

theorem node_643 : dfs 4 42 8 284093138549 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 4458936601258 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_621
  · change dfs 4 41 9 6898478150997 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_628

theorem node_644 : dfs 4 42 8 293992768853 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 4454239013546 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_620
  · change dfs 4 41 9 7168658404693 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_629

theorem node_645 : dfs 4 42 8 415089670538 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 6688535847589 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_625
  · change dfs 4 41 9 8818839674202 = true
    apply dfs_of_prune
    decide +kernel

theorem node_646 : dfs 4 42 8 416399317674 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 6677278283173 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_624
  · change dfs 4 41 9 8807582214746 = true
    apply dfs_of_prune
    decide +kernel

theorem node_647 : dfs 4 42 8 417332441765 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 6745599854197 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_626
  · change dfs 4 41 9 8841543989642 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_630

theorem node_648 : dfs 4 42 8 417336645029 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 6758484757109 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_627
  · change dfs 4 41 9 8854428890506 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_634

theorem node_649 : dfs 4 42 8 429686912341 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 6642524834474 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_623
  · change dfs 4 41 9 9356944258389 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_640

theorem node_650 : dfs 4 42 8 447839827285 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 6619976258901 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 41 9 8853359340202 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_633

theorem node_651 : dfs 4 42 8 553065477514 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 8876284752549 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_637
  · change dfs 4 41 9 11006588702042 = true
    apply dfs_of_prune
    decide +kernel

theorem node_652 : dfs 4 42 8 553066531498 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 8812413934170 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 41 9 11080156751269 = true
    apply dfs_of_prune
    decide +kernel

theorem node_653 : dfs 4 42 8 554909803941 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 8955360545397 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_638
  · change dfs 4 41 9 11051304646026 = true
    apply dfs_of_prune
    decide +kernel

theorem node_654 : dfs 4 42 8 555442479781 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 8843691391370 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_631
  · change dfs 4 41 9 11145793930869 = true
    apply dfs_of_prune
    decide +kernel

theorem node_655 : dfs 4 42 8 555849307557 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 8957508012661 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_639
  · change dfs 4 41 9 11053452146058 = true
    apply dfs_of_prune
    decide +kernel

theorem node_656 : dfs 4 42 8 555983545765 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 8955360545397 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_638
  · change dfs 4 41 9 11051304646026 = true
    apply dfs_of_prune
    decide +kernel

theorem node_657 : dfs 4 42 8 558971045493 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 8856983112362 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_636
  · change dfs 4 41 9 11296524662101 = true
    apply dfs_of_prune
    decide +kernel

theorem node_658 : dfs 4 42 8 560044788341 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 8855372520106 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_635
  · change dfs 4 41 9 11294914028885 = true
    apply dfs_of_prune
    decide +kernel

theorem node_659 : dfs 4 42 8 568870675797 = true := by
  apply dfs_of_children (fuel:=41)
  · change dfs 4 41 9 8852285524650 = true
    exact Rule30GoldenBudgetDAG4Part0004Research.node_632
  · change dfs 4 41 9 11566704915797 = true
    apply dfs_of_prune
    decide +kernel

theorem node_660 : dfs 4 43 7 9148910197 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 141521410730 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_641
  · change dfs 4 42 8 293992768853 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_644

theorem node_661 : dfs 4 43 7 17336202634 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 275598495066 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 42 8 417332441765 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_647

theorem node_662 : dfs 4 43 7 17395178154 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 275602680410 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 42 8 417336645029 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_648

theorem node_663 : dfs 4 43 7 17494241957 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 284093138549 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_643
  · change dfs 4 42 8 415089670538 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_645

theorem node_664 : dfs 4 43 7 17738843765 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 277215513258 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_642
  · change dfs 4 42 8 429686912341 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_649

theorem node_665 : dfs 4 43 7 25926138250 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 413708541274 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 42 8 555442479781 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_654

theorem node_666 : dfs 4 43 7 25926388394 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 414249605722 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 42 8 555983545765 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_656

theorem node_667 : dfs 4 43 7 25993505450 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 413175863898 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 42 8 554909803941 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_653

theorem node_668 : dfs 4 43 7 26328779381 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 416399317674 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_646
  · change dfs 4 42 8 568870675797 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_659

theorem node_669 : dfs 4 43 7 26924639573 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 447839827285 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_650
  · change dfs 4 42 8 553066531498 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_652

theorem node_670 : dfs 4 43 7 34516071818 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 550476402010 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 42 8 692210348709 = true
    apply dfs_of_prune
    decide +kernel

theorem node_671 : dfs 4 43 7 34541488810 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 555849307557 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_655
  · change dfs 4 42 8 688993315418 = true
    apply dfs_of_prune
    decide +kernel

theorem node_672 : dfs 4 43 7 34575047338 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 550480587354 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 42 8 692214551973 = true
    apply dfs_of_prune
    decide +kernel

theorem node_673 : dfs 4 43 7 34674111141 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 558971045493 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_657
  · change dfs 4 42 8 689967577482 = true
    apply dfs_of_prune
    decide +kernel

theorem node_674 : dfs 4 43 7 34675152293 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 560044788341 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_658
  · change dfs 4 42 8 691041318282 = true
    apply dfs_of_prune
    decide +kernel

theorem node_675 : dfs 4 43 7 34708710821 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 553065477514 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_651
  · change dfs 4 42 8 696946887285 = true
    apply dfs_of_prune
    decide +kernel

theorem node_676 : dfs 4 43 7 36529599829 = true := by
  apply dfs_of_children (fuel:=42)
  · change dfs 4 42 8 551187469653 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 42 8 690773928618 = true
    apply dfs_of_prune
    decide +kernel

theorem node_677 : dfs 4 44 6 550786442 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 8635862362 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 43 7 17494241957 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_663

theorem node_678 : dfs 4 44 6 557004197 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 9148910197 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_660
  · change dfs 4 43 7 17336202634 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_661

theorem node_679 : dfs 4 44 6 1093612197 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 17738843765 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_664
  · change dfs 4 43 7 25926138250 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_665

theorem node_680 : dfs 4 44 6 1112824437 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 17395178154 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_662
  · change dfs 4 43 7 26924639573 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_669

theorem node_681 : dfs 4 44 6 1213551957 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 17269347669 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 43 7 25993505450 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_667

theorem node_682 : dfs 4 44 6 1624528266 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 25815731546 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 43 7 34674111141 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_673

theorem node_683 : dfs 4 44 6 1624595114 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 25850337882 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 43 7 34708710821 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_675

theorem node_684 : dfs 4 44 6 1630746021 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 26328779381 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_668
  · change dfs 4 43 7 34516071818 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_670

theorem node_685 : dfs 4 44 6 1681216853 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 25926388394 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_666
  · change dfs 4 43 7 36529599829 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_676

theorem node_686 : dfs 4 44 6 2159368874 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 34675152293 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_674
  · change dfs 4 43 7 42996656730 = true
    apply dfs_of_prune
    decide +kernel

theorem node_687 : dfs 4 44 6 2186565237 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 34541488810 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_671
  · change dfs 4 43 7 44070958421 = true
    apply dfs_of_prune
    decide +kernel

theorem node_688 : dfs 4 44 6 2186566261 = true := by
  apply dfs_of_children (fuel:=43)
  · change dfs 4 43 7 34575047338 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_672
  · change dfs 4 43 7 44104508757 = true
    apply dfs_of_prune
    decide +kernel

theorem node_689 : dfs 4 45 5 34428586 = true := by
  apply dfs_of_children (fuel:=44)
  · change dfs 4 44 6 557004197 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_678
  · change dfs 4 44 6 1077099098 = true
    apply dfs_of_prune
    decide +kernel

theorem node_690 : dfs 4 45 5 34917797 = true := by
  apply dfs_of_children (fuel:=44)
  · change dfs 4 44 6 550786442 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_677
  · change dfs 4 44 6 1112824437 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_680

theorem node_691 : dfs 4 45 5 67966346 = true := by
  apply dfs_of_children (fuel:=44)
  · change dfs 4 44 6 1093612197 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_679
  · change dfs 4 44 6 1613708634 = true
    apply dfs_of_prune
    decide +kernel

theorem node_692 : dfs 4 45 5 71652693 = true := by
  apply dfs_of_children (fuel:=44)
  · change dfs 4 44 6 1213551957 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_681
  · change dfs 4 44 6 1624595114 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_683

theorem node_693 : dfs 4 45 5 75846997 = true := by
  apply dfs_of_children (fuel:=44)
  · change dfs 4 44 6 1079334229 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 44 6 1624595114 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_683

theorem node_694 : dfs 4 45 5 101537450 = true := by
  apply dfs_of_children (fuel:=44)
  · change dfs 4 44 6 1630746021 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_684
  · change dfs 4 44 6 2150840922 = true
    apply dfs_of_prune
    decide +kernel

theorem node_695 : dfs 4 45 5 102026661 = true := by
  apply dfs_of_children (fuel:=44)
  · change dfs 4 44 6 1624528266 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_682
  · change dfs 4 44 6 2186566261 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_688

theorem node_696 : dfs 4 45 5 103093877 = true := by
  apply dfs_of_children (fuel:=44)
  · change dfs 4 44 6 1681216853 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_685
  · change dfs 4 44 6 2159368874 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_686

theorem node_697 : dfs 4 45 5 135515813 = true := by
  apply dfs_of_children (fuel:=44)
  · change dfs 4 44 6 2186565237 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_687
  · change dfs 4 44 6 2698271114 = true
    apply dfs_of_prune
    decide +kernel

theorem node_698 : dfs 4 46 4 546133 = true := by
  apply dfs_of_children (fuel:=45)
  · change dfs 4 45 5 349525 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 45 5 34428586 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_689

theorem node_699 : dfs 4 46 4 2151850 = true := by
  apply dfs_of_children (fuel:=45)
  · change dfs 4 45 5 34917797 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_690
  · change dfs 4 45 5 67423834 = true
    apply dfs_of_prune
    decide +kernel

theorem node_700 : dfs 4 46 4 4273061 = true := by
  apply dfs_of_children (fuel:=45)
  · change dfs 4 45 5 67966346 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_691
  · change dfs 4 45 5 103093877 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_696

theorem node_701 : dfs 4 46 4 4289445 = true := by
  apply dfs_of_children (fuel:=45)
  · change dfs 4 45 5 67966346 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_691
  · change dfs 4 45 5 103093877 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_696

theorem node_702 : dfs 4 46 4 4343157 = true := by
  apply dfs_of_children (fuel:=45)
  · change dfs 4 45 5 71652693 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_692
  · change dfs 4 45 5 101537450 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_694

theorem node_703 : dfs 4 46 4 4478293 = true := by
  apply dfs_of_children (fuel:=45)
  · change dfs 4 45 5 75846997 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_693
  · change dfs 4 45 5 101537450 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_694

theorem node_704 : dfs 4 46 4 6342026 = true := by
  apply dfs_of_children (fuel:=45)
  · change dfs 4 45 5 100912474 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 45 5 135515813 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_697

theorem node_705 : dfs 4 46 4 6346154 = true := by
  apply dfs_of_children (fuel:=45)
  · change dfs 4 45 5 102026661 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_695
  · change dfs 4 45 5 134532698 = true
    apply dfs_of_prune
    decide +kernel

theorem node_706 : dfs 4 47 3 17749 = true := by
  apply dfs_of_children (fuel:=46)
  · change dfs 4 46 4 546133 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_698
  · change dfs 4 46 4 2151850 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_699

theorem node_707 : dfs 4 47 3 133450 = true := by
  apply dfs_of_children (fuel:=46)
  · change dfs 4 46 4 2126682 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 46 4 4289445 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_701

theorem node_708 : dfs 4 47 3 134506 = true := by
  apply dfs_of_children (fuel:=46)
  · change dfs 4 46 4 2110298 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 46 4 4273061 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_700

theorem node_709 : dfs 4 47 3 267493 = true := by
  apply dfs_of_children (fuel:=46)
  · change dfs 4 46 4 4343157 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_702
  · change dfs 4 46 4 6342026 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_704

theorem node_710 : dfs 4 47 3 270709 = true := by
  apply dfs_of_children (fuel:=46)
  · change dfs 4 46 4 4478293 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_703
  · change dfs 4 46 4 6346154 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_705

theorem node_711 : dfs 4 48 2 597 = true := by
  apply dfs_of_children (fuel:=47)
  · change dfs 4 47 3 17749 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_706
  · change dfs 4 47 3 134506 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_708

theorem node_712 : dfs 4 48 2 8410 = true := by
  apply dfs_of_children (fuel:=47)
  · change dfs 4 47 3 132314 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 47 3 267493 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_709

theorem node_713 : dfs 4 48 2 8501 = true := by
  apply dfs_of_children (fuel:=47)
  · change dfs 4 47 3 133450 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_707
  · change dfs 4 47 3 270709 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_710

theorem node_714 : dfs 4 49 1 21 = true := by
  apply dfs_of_children (fuel:=48)
  · change dfs 4 48 2 597 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_711
  · change dfs 4 48 2 8410 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_712

theorem node_715 : dfs 4 49 1 526 = true := by
  apply dfs_of_children (fuel:=48)
  · change dfs 4 48 2 8501 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_713
  · change dfs 4 48 2 16442 = true
    apply dfs_of_prune
    decide +kernel

theorem node_716 : dfs 4 50 0 32 = true := by
  apply dfs_of_children (fuel:=49)
  · change dfs 4 49 1 21 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_714
  · change dfs 4 49 1 526 = true
    exact Rule30GoldenBudgetDAG4Part0005Research.node_715

end Rule30GoldenBudgetDAG4Part0005Research
