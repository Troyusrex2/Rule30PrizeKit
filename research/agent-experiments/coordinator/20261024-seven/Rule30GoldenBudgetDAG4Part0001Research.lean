import Rule30GoldenBudgetDAG4Part0000Research
import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudgetDAG4Part0001Research
open Rule30GoldenCompactBudgetResearch

theorem node_128 : dfs 4 29 21 2503181652643443978725926309 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40336023295667147547556285045 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_96
  · change dfs 4 28 22 49775316095218175739708208522 = true
    apply dfs_of_prune
    decide +kernel

theorem node_129 : dfs 4 29 21 2516173214827496858219349621 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39910467239802421065615280810 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_90
  · change dfs 4 28 22 50897185088460176801587131733 = true
    apply dfs_of_prune
    decide +kernel

theorem node_130 : dfs 4 29 21 2516857663576212873764227701 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39781722119164822870946044586 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_82
  · change dfs 4 28 22 50768439967822587488010675541 = true
    apply dfs_of_prune
    decide +kernel

theorem node_131 : dfs 4 29 21 2520975492605694915205301877 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39820451851089198906650004138 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_89
  · change dfs 4 28 22 50807169699746959476070675797 = true
    apply dfs_of_prune
    decide +kernel

theorem node_132 : dfs 4 29 21 2521113720940539429176821365 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40955509699943911358437979477 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_101
  · change dfs 4 28 22 49775832479852251703872916138 = true
    apply dfs_of_prune
    decide +kernel

theorem node_133 : dfs 4 29 21 2521415913952716667521436277 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39819110567466926021940173482 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_88
  · change dfs 4 28 22 50805828416124686569824232789 = true
    apply dfs_of_prune
    decide +kernel

theorem node_134 : dfs 4 29 21 2522222783761872577162218101 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40964210947734427785576490325 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_103
  · change dfs 4 28 22 49784533727642767936049732266 = true
    apply dfs_of_prune
    decide +kernel

theorem node_135 : dfs 4 29 21 2522476744699221469899885173 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40958910487962403789627106645 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_102
  · change dfs 4 28 22 49779233267870744748005087914 = true
    apply dfs_of_prune
    decide +kernel

theorem node_136 : dfs 4 29 21 2554041361708861136649254229 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39775867949465725157113154218 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_81
  · change dfs 4 28 22 52000525837408872222332466517 = true
    apply dfs_of_prune
    decide +kernel

theorem node_137 : dfs 4 29 21 2556072159152250574840460629 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 42219671943997409502388991317 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_105
  · change dfs 4 28 22 49802054684620369532964653738 = true
    apply dfs_of_prune
    decide +kernel

theorem node_138 : dfs 4 29 21 2556094388604759501892658517 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 42125475250972319095155488085 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_104
  · change dfs 4 28 22 49707857991595284995764488874 = true
    apply dfs_of_prune
    decide +kernel

theorem node_139 : dfs 4 29 21 2556462733190423020686714197 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39796026312302379009675987626 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_84
  · change dfs 4 28 22 52020684200245523930091779413 = true
    apply dfs_of_prune
    decide +kernel

theorem node_140 : dfs 4 30 20 116862658505440540723426698 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 1884217979175828082526696101 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_107
  · change dfs 4 29 21 2483845185704685756626849114 = true
    apply dfs_of_prune
    decide +kernel

theorem node_141 : dfs 4 30 20 116862828840603236834052778 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 1864868819886918180188019290 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 2503181652643443978725926309 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_128

theorem node_142 : dfs 4 30 20 117165023212867702055324330 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 1883008329835200392436426149 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_106
  · change dfs 4 29 21 2482635536364058067161799258 = true
    apply dfs_of_prune
    decide +kernel

theorem node_143 : dfs 4 30 20 121294733300553017975809365 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2014876364469138302408488277 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_108
  · change dfs 4 29 21 2488775285758075573141867178 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_116

theorem node_144 : dfs 4 30 20 125835187816281200010098005 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 1857697193987677317089285461 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 2486338620187288450754063018 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_111

theorem node_145 : dfs 4 30 20 126169139744656574615287125 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 1863348197237334865542993237 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 2491989623436943491513100970 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_118

theorem node_146 : dfs 4 30 20 155359259480118129579133610 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2485441296937299657049680474 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3123754129693825335918155173 = true
    apply dfs_of_prune
    decide +kernel

theorem node_147 : dfs 4 30 20 155402080829568665965476234 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2485147304664510415388433754 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3123460137421036087022297765 = true
    apply dfs_of_prune
    decide +kernel

theorem node_148 : dfs 4 30 20 155453870396840531955387050 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2479308127800135568298170970 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3117620960556661204287923621 = true
    apply dfs_of_prune
    decide +kernel

theorem node_149 : dfs 4 30 20 155472824093091487948650890 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2496006017456986574433133221 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_122
  · change dfs 4 29 21 3095633223985846344342723930 = true
    apply dfs_of_prune
    decide +kernel

theorem node_150 : dfs 4 30 20 155532566964950019781495466 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2496834608478707738219992485 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_123
  · change dfs 4 29 21 3096461815007567473468418650 = true
    apply dfs_of_prune
    decide +kernel

theorem node_151 : dfs 4 30 20 155548135721962445447977642 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2477583278749515497686116954 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3115896111506043375631259045 = true
    apply dfs_of_prune
    decide +kernel

theorem node_152 : dfs 4 30 20 155548455068271370424650410 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2483838839529608317637581402 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3122151672286134116175488421 = true
    apply dfs_of_prune
    decide +kernel

theorem node_153 : dfs 4 30 20 155747576578181692769610410 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2481646967494869018720492122 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3119959800251394025766364581 = true
    apply dfs_of_prune
    decide +kernel

theorem node_154 : dfs 4 30 20 155749119159570312960236202 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2499083543498628002953352613 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_125
  · change dfs 4 29 21 3098710750027485372933155418 = true
    apply dfs_of_prune
    decide +kernel

theorem node_155 : dfs 4 30 20 155750090807231311302522250 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2498446733646344541594759845 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_124
  · change dfs 4 29 21 3098073940175203251159256410 = true
    apply dfs_of_prune
    decide +kernel

theorem node_156 : dfs 4 30 20 155769244823612083676035466 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2478951559838984813802839386 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3117264392595511739567153829 = true
    apply dfs_of_prune
    decide +kernel

theorem node_157 : dfs 4 30 20 155787822325215344450964138 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2481572398765736497975745114 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3119885231522261435137828261 = true
    apply dfs_of_prune
    decide +kernel

theorem node_158 : dfs 4 30 20 155830177022368105312909706 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2482932243847490992775978330 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3121245076604016617206227621 = true
    apply dfs_of_prune
    decide +kernel

theorem node_159 : dfs 4 30 20 155830628670360335472572810 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2502276582276475654420144805 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_127
  · change dfs 4 29 21 3101903788805333145279159642 = true
    apply dfs_of_prune
    decide +kernel

theorem node_160 : dfs 4 30 20 155838201392086578171841194 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2482529962333073275196627546 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3120842795089599128283555237 = true
    apply dfs_of_prune
    decide +kernel

theorem node_161 : dfs 4 30 20 155844795769808970178017674 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2478853644521441641500138842 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3117166477277968411269898917 = true
    apply dfs_of_prune
    decide +kernel

theorem node_162 : dfs 4 30 20 155850689837824502355298986 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2501992900644315386887710117 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_126
  · change dfs 4 29 21 3101620107173173009792719450 = true
    apply dfs_of_prune
    decide +kernel

theorem node_163 : dfs 4 30 20 156011452736626152029336229 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2485960758036371339947456906 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_109
  · change dfs 4 29 21 3133944997349816607991744117 = true
    apply dfs_of_prune
    decide +kernel

theorem node_164 : dfs 4 30 20 156115728192937513480463013 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2516173214827496858219349621 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_129
  · change dfs 4 29 21 3106129014799439521950562698 = true
    apply dfs_of_prune
    decide +kernel

theorem node_165 : dfs 4 30 20 156115728235792125224375717 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2516857663576212873764227701 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_130
  · change dfs 4 29 21 3106813463548154819608491402 = true
    apply dfs_of_prune
    decide +kernel

theorem node_166 : dfs 4 30 20 156140523328210565069972901 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2521415913952716667521436277 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_133
  · change dfs 4 29 21 3111371713924657171334067594 = true
    apply dfs_of_prune
    decide +kernel

theorem node_167 : dfs 4 30 20 156148970946203730463532453 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2522476744699221469899885173 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_135
  · change dfs 4 29 21 3112432544671162109889508746 = true
    apply dfs_of_prune
    decide +kernel

theorem node_168 : dfs 4 30 20 156165584959416429724214693 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2522222783761872577162218101 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_134
  · change dfs 4 29 21 3112178583733813446978205066 = true
    apply dfs_of_prune
    decide +kernel

theorem node_169 : dfs 4 30 20 156312130773988258048431525 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2491910901398090804408268170 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_117
  · change dfs 4 29 21 3139895140711533405038266997 = true
    apply dfs_of_prune
    decide +kernel

theorem node_170 : dfs 4 30 20 156354430502403310722654885 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2491999183876319027890059658 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_119
  · change dfs 4 29 21 3139983423189761731553822325 = true
    apply dfs_of_prune
    decide +kernel

theorem node_171 : dfs 4 30 20 156445703550928127516058277 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2488543829127847809141012874 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_114
  · change dfs 4 29 21 3136528068441291617946732149 = true
    apply dfs_of_prune
    decide +kernel

theorem node_172 : dfs 4 30 20 156505927558642810998071973 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2520975492605694915205301877 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_131
  · change dfs 4 29 21 3110931292577635374947203466 = true
    apply dfs_of_prune
    decide +kernel

theorem node_173 : dfs 4 30 20 156530410952426812266164901 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2521113720940539429176821365 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_132
  · change dfs 4 29 21 3111069520912479933560437130 = true
    apply dfs_of_prune
    decide +kernel

theorem node_174 : dfs 4 30 20 157209892346248078233537141 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2485992042649289317220702890 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_110
  · change dfs 4 29 21 3172661908190402900850287957 = true
    apply dfs_of_prune
    decide +kernel

theorem node_175 : dfs 4 30 20 157261123962543597195527797 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2494405135138661105248111274 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_121
  · change dfs 4 29 21 3181075000679771925182543189 = true
    apply dfs_of_prune
    decide +kernel

theorem node_176 : dfs 4 30 20 157267002844403570671175285 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2554041361708861136649254229 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_136
  · change dfs 4 29 21 3105311535453136003405777578 = true
    apply dfs_of_prune
    decide +kernel

theorem node_177 : dfs 4 30 20 157267028208676671950505589 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2486341774064858934943746730 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_112
  · change dfs 4 29 21 3173011639605972268978730325 = true
    apply dfs_of_prune
    decide +kernel

theorem node_178 : dfs 4 30 20 157355547837454384937405045 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2487418197327116670556002986 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_113
  · change dfs 4 29 21 3174088062868228813224060245 = true
    apply dfs_of_prune
    decide +kernel

theorem node_179 : dfs 4 30 20 157361673462531277397772917 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2556094388604759501892658517 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_138
  · change dfs 4 29 21 3107364562349032424087050922 = true
    apply dfs_of_prune
    decide +kernel

theorem node_180 : dfs 4 30 20 157664080251575068754527861 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2556072159152250574840460629 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_137
  · change dfs 4 29 21 3107342332896523897434606250 = true
    apply dfs_of_prune
    decide +kernel

theorem node_181 : dfs 4 30 20 157715260652935627760814709 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2556462733190423020686714197 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_139
  · change dfs 4 29 21 3107732906934696569946331818 = true
    apply dfs_of_prune
    decide +kernel

theorem node_182 : dfs 4 30 20 164520814043949333600695637 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2476667213630367454538847573 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3105308639829978588203625130 = true
    apply dfs_of_prune
    decide +kernel

theorem node_183 : dfs 4 30 20 164615398715381753521272149 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2482710505339496494093653333 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 29 21 3111351931539105152510896810 = true
    apply dfs_of_prune
    decide +kernel

theorem node_184 : dfs 4 30 20 164813922385951324584457557 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2488768990824672175446403754 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_115
  · change dfs 4 29 21 3098067603910447930890671445 = true
    apply dfs_of_prune
    decide +kernel

theorem node_185 : dfs 4 30 20 164917593087645939350025557 = true := by
  apply dfs_of_children (fuel:=29)
  · change dfs 4 29 21 2492022701331370227508292266 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_120
  · change dfs 4 29 21 3101321314417144249933256021 = true
    apply dfs_of_prune
    decide +kernel

theorem node_186 : dfs 4 31 19 7317333729553586856495786 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 116245971280927115535276634 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 156140523328210565069972901 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_166

theorem node_187 : dfs 4 31 19 7366120024520462921684389 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 116862658505440540723426698 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_140
  · change dfs 4 30 20 157361673462531277397772917 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_179

theorem node_188 : dfs 4 31 19 7432241128486515093375605 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 121294733300553017975809365 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_143
  · change dfs 4 30 20 155749119159570312960236202 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_154

theorem node_189 : dfs 4 31 19 7567400499302353318638933 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 117165023212867702055324330 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_142
  · change dfs 4 30 20 164917593087645939350025557 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_185

theorem node_190 : dfs 4 31 19 7568299416099124427793749 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 125835187816281200010098005 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_144
  · change dfs 4 30 20 155453870396840531955387050 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_148

theorem node_191 : dfs 4 31 19 7580766343638044269258069 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 116862828840603236834052778 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_141
  · change dfs 4 30 20 164615398715381753521272149 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_183

theorem node_192 : dfs 4 31 19 7585939070083639235749205 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 126169139744656574615287125 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_145
  · change dfs 4 30 20 155787822325215344450964138 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_157

theorem node_193 : dfs 4 31 19 7892673589952964716819797 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 116457487440705888980391253 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 155747576578181692769610410 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_153

theorem node_194 : dfs 4 31 19 9712921700171490398221706 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156530410952426812266164901 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_173
  · change dfs 4 30 20 194007111360480704668978522 = true
    apply dfs_of_prune
    decide +kernel

theorem node_195 : dfs 4 31 19 9715483129214976427455882 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156011452736626152029336229 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_163
  · change dfs 4 30 20 193488153144680555522510170 = true
    apply dfs_of_prune
    decide +kernel

theorem node_196 : dfs 4 31 19 9716763905661208355322250 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156505927558642810998071973 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_172
  · change dfs 4 30 20 193982627966696636107087194 = true
    apply dfs_of_prune
    decide +kernel

theorem node_197 : dfs 4 31 19 9720307409905643449661834 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155208143772825022011694426 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 195102695820108307273196197 = true
    apply dfs_of_prune
    decide +kernel

theorem node_198 : dfs 4 31 19 9720799615491071902812842 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156115728235792125224375717 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_165
  · change dfs 4 30 20 193592428643846132853287514 = true
    apply dfs_of_prune
    decide +kernel

theorem node_199 : dfs 4 31 19 9721457953509627191277962 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156445703550928127516058277 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_171
  · change dfs 4 30 20 193922403958982033071824218 = true
    apply dfs_of_prune
    decide +kernel

theorem node_200 : dfs 4 31 19 9721698532287847375133354 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155168304955361542964193882 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 195062857002644680894895525 = true
    apply dfs_of_prune
    decide +kernel

theorem node_201 : dfs 4 31 19 9722367224649330974108330 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 154868102824701610521418330 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 194762654871985084668683685 = true
    apply dfs_of_prune
    decide +kernel

theorem node_202 : dfs 4 31 19 9734165459826691114097322 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156312130773988258048431525 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_169
  · change dfs 4 30 20 193788831182041962278234714 = true
    apply dfs_of_prune
    decide +kernel

theorem node_203 : dfs 4 31 19 9736755972126990651782538 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155098352740035942426299738 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 194992904787318888429302437 = true
    apply dfs_of_prune
    decide +kernel

theorem node_204 : dfs 4 31 19 9739338186272309537233578 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 154941274823208498572765786 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 194835826870491640010954149 = true
    apply dfs_of_prune
    decide +kernel

theorem node_205 : dfs 4 31 19 9739687948340496257694090 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156115728192937513480463013 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_164
  · change dfs 4 30 20 193592428600991614188805466 = true
    apply dfs_of_prune
    decide +kernel

theorem node_206 : dfs 4 31 19 9743804600939694463482250 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156354430502403310722654885 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_170
  · change dfs 4 30 20 193831130910457181659553114 = true
    apply dfs_of_prune
    decide +kernel

theorem node_207 : dfs 4 31 19 9743841251237945818057386 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156165584959416429724214693 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_168
  · change dfs 4 30 20 193642285367470300734511706 = true
    apply dfs_of_prune
    decide +kernel

theorem node_208 : dfs 4 31 19 9745291915846930331708074 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 156148970946203730463532453 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_167
  · change dfs 4 30 20 193625671354257899229174362 = true
    apply dfs_of_prune
    decide +kernel

theorem node_209 : dfs 4 31 19 9750204246263968937846181 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 157355547837454384937405045 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_178
  · change dfs 4 30 20 194227785335700973347829130 = true
    apply dfs_of_prune
    decide +kernel

theorem node_210 : dfs 4 31 19 9753103523511706194588325 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155402080829568665965476234 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_147
  · change dfs 4 30 20 195901095786659749777720949 = true
    apply dfs_of_prune
    decide +kernel

theorem node_211 : dfs 4 31 19 9753608323004326361224613 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 157715260652935627760814709 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_181
  · change dfs 4 30 20 194587498151182186912331146 = true
    apply dfs_of_prune
    decide +kernel

theorem node_212 : dfs 4 31 19 9753612282231348809475493 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 157209892346248078233537141 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_174
  · change dfs 4 30 20 194082129844495258812577162 = true
    apply dfs_of_prune
    decide +kernel

theorem node_213 : dfs 4 31 19 9757196190502263152878245 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 157261123962543597195527797 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_175
  · change dfs 4 30 20 194133361460790693972244874 = true
    apply dfs_of_prune
    decide +kernel

theorem node_214 : dfs 4 31 19 9759556857518582636524197 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 157267028208676671950505589 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_177
  · change dfs 4 30 20 194139265706923780186225034 = true
    apply dfs_of_prune
    decide +kernel

theorem node_215 : dfs 4 31 19 9759558731016027584901797 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 157267002844403570671175285 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_176
  · change dfs 4 30 20 194139240342650678764288394 = true
    apply dfs_of_prune
    decide +kernel

theorem node_216 : dfs 4 31 19 9759570260231073854698149 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155844795769808970178017674 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_161
  · change dfs 4 30 20 196343810726899448760583797 = true
    apply dfs_of_prune
    decide +kernel

theorem node_217 : dfs 4 31 19 9759570260231110361920165 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155830628670360335472572810 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_159
  · change dfs 4 30 20 196329643627450865594746485 = true
    apply dfs_of_prune
    decide +kernel

theorem node_218 : dfs 4 31 19 9759606589080454548791973 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155830177022368105312909706 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_158
  · change dfs 4 30 20 196329191979458634799285877 = true
    apply dfs_of_prune
    decide +kernel

theorem node_219 : dfs 4 31 19 9760368514257862498235045 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155472824093091487948650890 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_149
  · change dfs 4 30 20 195971839050182280055441013 = true
    apply dfs_of_prune
    decide +kernel

theorem node_220 : dfs 4 31 19 9761919193681564439851685 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 157664080251575068754527861 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_180
  · change dfs 4 30 20 194536317749821716711520650 = true
    apply dfs_of_prune
    decide +kernel

theorem node_221 : dfs 4 31 19 9772169706769569606313381 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155750090807231311302522250 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_155
  · change dfs 4 30 20 196249105764321755114343029 = true
    apply dfs_of_prune
    decide +kernel

theorem node_222 : dfs 4 31 19 9778449349869045127099045 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155769244823612083676035466 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_156
  · change dfs 4 30 20 196268259780702561897891445 = true
    apply dfs_of_prune
    decide +kernel

theorem node_223 : dfs 4 31 19 9824195115296067413247605 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155359259480118129579133610 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_146
  · change dfs 4 30 20 198276126076438537568908629 = true
    apply dfs_of_prune
    decide +kernel

theorem node_224 : dfs 4 31 19 9847807391315064868129397 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155548135721962445447977642 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_151
  · change dfs 4 30 20 198465002318282441053873493 = true
    apply dfs_of_prune
    decide +kernel

theorem node_225 : dfs 4 31 19 9853613886818229339637365 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155532566964950019781495466 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_150
  · change dfs 4 30 20 198449433561269996182762837 = true
    apply dfs_of_prune
    decide +kernel

theorem node_226 : dfs 4 31 19 9985455987776289443063125 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155838201392086578171841194 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_160
  · change dfs 4 30 20 203590771266864842708514133 = true
    apply dfs_of_prune
    decide +kernel

theorem node_227 : dfs 4 31 19 9986151055328382777206101 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 164520814043949333600695637 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_182
  · change dfs 4 30 20 194139496624508665545984682 = true
    apply dfs_of_prune
    decide +kernel

theorem node_228 : dfs 4 31 19 9986220374733838086743381 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155850689837824502355298986 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_162
  · change dfs 4 30 20 203603259712602721257944405 = true
    apply dfs_of_prune
    decide +kernel

theorem node_229 : dfs 4 31 19 9998617982867302618670421 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155548455068271370424650410 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_152
  · change dfs 4 30 20 203301024943049887111869781 = true
    apply dfs_of_prune
    decide +kernel

theorem node_230 : dfs 4 31 19 9998824330483882427348309 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 164813922385951324584457557 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_184
  · change dfs 4 30 20 194432604966510088641923754 = true
    apply dfs_of_prune
    decide +kernel

theorem node_231 : dfs 4 31 19 10300859387489174100276565 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155145477157458462310225237 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 194435566294934274693573290 = true
    apply dfs_of_prune
    decide +kernel

theorem node_232 : dfs 4 31 19 10301869346727305529685333 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155095154439625473116165461 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 194385243577101104574016170 = true
    apply dfs_of_prune
    decide +kernel

theorem node_233 : dfs 4 31 19 10310525229182223066232149 = true := by
  apply dfs_of_children (fuel:=30)
  · change dfs 4 30 20 155143113668374022570988885 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 30 20 194433202805849826360208042 = true
    apply dfs_of_prune
    decide +kernel

theorem node_234 : dfs 4 32 18 455812549396044690315946 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 7366120024520462921684389 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_187
  · change dfs 4 31 19 9708413800023898725755482 = true
    apply dfs_of_prune
    decide +kernel

theorem node_235 : dfs 4 32 18 456096479714166069086890 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 7256794743308550010526298 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 31 19 9750204246263968937846181 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_209

theorem node_236 : dfs 4 32 18 459964569886687319401893 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 7432241128486515093375605 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_188
  · change dfs 4 31 19 9736755972126990651782538 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_203

theorem node_237 : dfs 4 32 18 463573187492407699671669 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 7585939070083639235749205 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_192
  · change dfs 4 31 19 9739338186272309537233578 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_204

theorem node_238 : dfs 4 32 18 464390825574906291636853 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 7568299416099124427793749 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_190
  · change dfs 4 31 19 9721698532287847375133354 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_200

theorem node_239 : dfs 4 32 18 464736527511801711380085 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 7567400499302353318638933 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_189
  · change dfs 4 31 19 9720799615491071902812842 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_198

theorem node_240 : dfs 4 32 18 464962169675084534745717 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 7580766343638044269258069 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_191
  · change dfs 4 31 19 9734165459826691114097322 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_202

theorem node_241 : dfs 4 32 18 472691272935704105231701 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 7892673589952964716819797 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_193
  · change dfs 4 31 19 9743841251237945818057386 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_207

theorem node_242 : dfs 4 32 18 474158124607745104192853 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 7317333729553586856495786 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_186
  · change dfs 4 31 19 10301869346727305529685333 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_232

theorem node_243 : dfs 4 32 18 607209841086241853568394 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9674845949967551163747674 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 31 19 12168255452922975542096549 = true
    apply dfs_of_prune
    decide +kernel

theorem node_244 : dfs 4 32 18 607221430538031310654122 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9674512643643273563036250 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 31 19 12167922146598693295662501 = true
    apply dfs_of_prune
    decide +kernel

theorem node_245 : dfs 4 32 18 607278717697532358384298 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9683320103188062725155418 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 31 19 12176729606143339192964517 = true
    apply dfs_of_prune
    decide +kernel

theorem node_246 : dfs 4 32 18 607558897078968372589962 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9778449349869045127099045 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_222
  · change dfs 4 31 19 12120743125372485442686298 = true
    apply dfs_of_prune
    decide +kernel

theorem node_247 : dfs 4 32 18 607568678898457169463978 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9702151423707702849526362 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 31 19 12195560926662978176198053 = true
    apply dfs_of_prune
    decide +kernel

theorem node_248 : dfs 4 32 18 607605365219955325695370 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9759570260231110361920165 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_217
  · change dfs 4 31 19 12101864035734545969401178 = true
    apply dfs_of_prune
    decide +kernel

theorem node_249 : dfs 4 32 18 607608500535603657792170 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9753608323004326361224613 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_211
  · change dfs 4 31 19 12095902098507900141120090 = true
    apply dfs_of_prune
    decide +kernel

theorem node_250 : dfs 4 32 18 607608812163587264301738 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9753612282231348809475493 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_212
  · change dfs 4 31 19 12095906057734922517043802 = true
    apply dfs_of_prune
    decide +kernel

theorem node_251 : dfs 4 32 18 607660354171370889442698 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9753103523511706194588325 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_210
  · change dfs 4 31 19 12095397299015270527356250 = true
    apply dfs_of_prune
    decide +kernel

theorem node_252 : dfs 4 32 18 608247568078141676935850 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9684202088139047238838874 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 31 19 12177611591094403155154341 = true
    apply dfs_of_prune
    decide +kernel

theorem node_253 : dfs 4 32 18 608398286984725507241354 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9759556857518582636524197 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_214
  · change dfs 4 31 19 12101850633022091585604954 = true
    apply dfs_of_prune
    decide +kernel

theorem node_254 : dfs 4 32 18 608406789780822003447178 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9759558731016027584901797 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_215
  · change dfs 4 31 19 12101852506519536609480026 = true
    apply dfs_of_prune
    decide +kernel

theorem node_255 : dfs 4 32 18 608423003302453377152394 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9761919193681564439851685 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_220
  · change dfs 4 31 19 12104212969184988641185114 = true
    apply dfs_of_prune
    decide +kernel

end Rule30GoldenBudgetDAG4Part0001Research
