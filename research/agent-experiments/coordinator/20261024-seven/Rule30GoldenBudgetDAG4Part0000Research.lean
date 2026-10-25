import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudgetDAG4Part0000Research
open Rule30GoldenCompactBudgetResearch

theorem node_0 : dfs 4 17 33 701438054464928833167899749452690850417322 = true := by
  apply dfs_of_children (fuel:=16)
  · change dfs 4 16 34 11164891989843056019145041552156680608635482 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 16 34 14039597425591144158483807302313075618784677 = true
    apply dfs_of_prune
    decide +kernel

theorem node_1 : dfs 4 18 32 45073589559760705583580770909260660516181 = true := by
  apply dfs_of_children (fuel:=17)
  · change dfs 4 17 33 701438054464928833167899749452690850417322 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_0
  · change dfs 4 17 33 916496510358961942076777085002851731273045 = true
    apply dfs_of_prune
    decide +kernel

theorem node_2 : dfs 4 19 31 2766677294088542101645677190976520931957 = true := by
  apply dfs_of_children (fuel:=18)
  · change dfs 4 18 32 45073589559760705583580770909260660516181 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_1
  · change dfs 4 18 32 54771637017007451792293118792292673870506 = true
    apply dfs_of_prune
    decide +kernel

theorem node_3 : dfs 4 20 30 171265993162798926150293063564798900618 = true := by
  apply dfs_of_children (fuel:=19)
  · change dfs 4 19 31 2729538741728050641492879227059226172762 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 19 31 3431371123502486222387629477531651515045 = true
    apply dfs_of_prune
    decide +kernel

theorem node_4 : dfs 4 20 30 171688698856085063792331088674726172069 = true := by
  apply dfs_of_children (fuel:=19)
  · change dfs 4 19 31 2766677294088542101645677190976520931957 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_2
  · change dfs 4 19 31 3415340556031581047626578122667054511498 = true
    apply dfs_of_prune
    decide +kernel

theorem node_5 : dfs 4 21 29 10684881553705511535763733639282383530 = true := by
  apply dfs_of_children (fuel:=20)
  · change dfs 4 20 30 170747651387918700589905536427399785050 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 20 30 214612175248820924396078714777926686117 = true
    apply dfs_of_prune
    decide +kernel

theorem node_6 : dfs 4 21 29 10689265087986761149124233384794944906 = true := by
  apply dfs_of_children (fuel:=20)
  · change dfs 4 20 30 170687939756610418818379779336155123034 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 20 30 214552463617512642624623465998022390437 = true
    apply dfs_of_prune
    decide +kernel

theorem node_7 : dfs 4 21 29 10703304741397704667376073710638598826 = true := by
  apply dfs_of_children (fuel:=20)
  · change dfs 4 20 30 171688698856085063792331088674726172069 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_4
  · change dfs 4 20 30 212894766725417455853034383202553866842 = true
    apply dfs_of_prune
    decide +kernel

theorem node_8 : dfs 4 21 29 10709973434225918997924090428684831402 = true := by
  apply dfs_of_children (fuel:=20)
  · change dfs 4 20 30 170341519608109232858744632388449118810 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 20 30 214206043469011456665245054721613714853 = true
    apply dfs_of_prune
    decide +kernel

theorem node_9 : dfs 4 21 29 10751100239012452780381966075029795493 = true := by
  apply dfs_of_children (fuel:=20)
  · change dfs 4 20 30 171265993162798926150293063564798900618 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_3
  · change dfs 4 20 30 215795131021593607892996144716223694453 = true
    apply dfs_of_prune
    decide +kernel

theorem node_10 : dfs 4 22 28 668075093375070166639301283795613066 = true := by
  apply dfs_of_children (fuel:=21)
  · change dfs 4 21 29 10751100239012452780381966075029795493 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_9
  · change dfs 4 21 29 13326479480845727284238334575294106970 = true
    apply dfs_of_prune
    decide +kernel

theorem node_11 : dfs 4 22 28 671537399587106747568242219258389925 = true := by
  apply dfs_of_children (fuel:=21)
  · change dfs 4 21 29 10689265087986761149124233384794944906 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_6
  · change dfs 4 21 29 13472336204161428758190721534696983157 = true
    apply dfs_of_prune
    decide +kernel

theorem node_12 : dfs 4 22 28 675754961471013909124595090166483573 = true := by
  apply dfs_of_children (fuel:=21)
  · change dfs 4 21 29 10684881553705511535763733639282383530 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_5
  · change dfs 4 21 29 13634106169353293628961246709609047381 = true
    apply dfs_of_prune
    decide +kernel

theorem node_13 : dfs 4 22 28 675808089164862622668912710970066549 = true := by
  apply dfs_of_children (fuel:=21)
  · change dfs 4 21 29 10709973434225918997924090428684831402 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_8
  · change dfs 4 21 29 13659198049873701091030274225235752277 = true
    apply dfs_of_prune
    decide +kernel

theorem node_14 : dfs 4 22 28 677476584033089042669871784725218933 = true := by
  apply dfs_of_children (fuel:=21)
  · change dfs 4 21 29 10703304741397704667376073710638598826 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_7
  · change dfs 4 21 29 13652529357045486760480076058362246485 = true
    apply dfs_of_prune
    decide +kernel

theorem node_15 : dfs 4 23 27 41847258967868104295891557473946282 = true := by
  apply dfs_of_children (fuel:=22)
  · change dfs 4 22 28 671537399587106747568242219258389925 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_11
  · change dfs 4 22 28 832498602201686404076149351417469530 = true
    apply dfs_of_prune
    decide +kernel

theorem node_16 : dfs 4 23 27 41876151961144675968011798096487077 = true := by
  apply dfs_of_children (fuel:=22)
  · change dfs 4 22 28 677476584033089042669871784725218933 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_14
  · change dfs 4 22 28 835841638218401285364631104342817162 = true
    apply dfs_of_prune
    decide +kernel

theorem node_17 : dfs 4 23 27 41914049076085930713567815884121509 = true := by
  apply dfs_of_children (fuel:=22)
  · change dfs 4 22 28 675754961471013909124595090166483573 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_12
  · change dfs 4 22 28 834120015656326151827754690072442250 = true
    apply dfs_of_prune
    decide +kernel

theorem node_18 : dfs 4 23 27 41970848769670665099819573603784101 = true := by
  apply dfs_of_children (fuel:=22)
  · change dfs 4 22 28 668075093375070166639301283795613066 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_10
  · change dfs 4 22 28 842017038135986892238266858483042933 = true
    apply dfs_of_prune
    decide +kernel

theorem node_19 : dfs 4 23 27 41994938698559668452860058503000741 = true := by
  apply dfs_of_children (fuel:=22)
  · change dfs 4 22 28 675808089164862622668912710970066549 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_13
  · change dfs 4 22 28 834173143350174865381134968174590346 = true
    apply dfs_of_prune
    decide +kernel

theorem node_20 : dfs 4 24 26 1964277632871280732132098128562858 = true := by
  apply dfs_of_children (fuel:=23)
  · change dfs 4 23 27 31204936805357848718511624298388058 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 23 27 41914049076085930713567815884121509 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_17

theorem node_21 : dfs 4 24 26 2608078975249267678755820336929450 = true := by
  apply dfs_of_children (fuel:=23)
  · change dfs 4 23 27 41551629101997699952778498068916826 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 23 27 52260741372725781952855103350035877 = true
    apply dfs_of_prune
    decide +kernel

theorem node_22 : dfs 4 24 26 2608079258617582388512748787644810 = true := by
  apply dfs_of_children (fuel:=23)
  · change dfs 4 23 27 41876151961144675968011798096487077 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_16
  · change dfs 4 23 27 51936227124555904514521202399010138 = true
    apply dfs_of_prune
    decide +kernel

theorem node_23 : dfs 4 24 26 2609488061708447272310881554953610 = true := by
  apply dfs_of_children (fuel:=23)
  · change dfs 4 23 27 41994938698559668452860058503000741 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_19
  · change dfs 4 23 27 52055013861970896989864927586372954 = true
    apply dfs_of_prune
    decide +kernel

theorem node_24 : dfs 4 24 26 2612971196965945171196723518065322 = true := by
  apply dfs_of_children (fuel:=23)
  · change dfs 4 23 27 41646544729882531424367113463880282 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 23 27 52355657000610613414214961875690917 = true
    apply dfs_of_prune
    decide +kernel

theorem node_25 : dfs 4 24 26 2613052086547540869872306158394026 = true := by
  apply dfs_of_children (fuel:=23)
  · change dfs 4 23 27 41970848769670665099819573603784101 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_18
  · change dfs 4 23 27 52030923933081893636035497377868378 = true
    apply dfs_of_prune
    decide +kernel

theorem node_26 : dfs 4 24 26 2614730787648360473271288644679050 = true := by
  apply dfs_of_children (fuel:=23)
  · change dfs 4 23 27 41587210726154936668573829584997722 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 23 27 52296322996883018662967047880094373 = true
    apply dfs_of_prune
    decide +kernel

theorem node_27 : dfs 4 24 26 2678925353053723663400361584665941 = true := by
  apply dfs_of_children (fuel:=23)
  · change dfs 4 23 27 41847258967868104295891557473946282 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_15
  · change dfs 4 23 27 54665741837375960009056997961528661 = true
    apply dfs_of_prune
    decide +kernel

theorem node_28 : dfs 4 24 26 2765432812215521715539010029532501 = true := by
  apply dfs_of_children (fuel:=23)
  · change dfs 4 23 27 41606081937741782539634437519725909 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 23 27 52152934931640651165339741698239146 = true
    apply dfs_of_prune
    decide +kernel

theorem node_29 : dfs 4 25 25 127287264649867359117849738736981 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 1964277632871280732132098128562858 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_20
  · change dfs 4 24 26 2765432812215521715539010029532501 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_28

theorem node_30 : dfs 4 25 25 162998746174809408476231670008490 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2605444554628607695519610699602522 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 24 26 3274764071549112821011075325666725 = true
    apply dfs_of_prune
    decide +kernel

theorem node_31 : dfs 4 25 25 163087668286797954227163980462474 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2604599123719777296970796427468122 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 24 26 3273918640640282422538140242846373 = true
    apply dfs_of_prune
    decide +kernel

theorem node_32 : dfs 4 25 25 163117580113713660825761135372970 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2597796462779362794137556137695834 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 24 26 3267115979699867921737214319764901 = true
    apply dfs_of_prune
    decide +kernel

theorem node_33 : dfs 4 25 25 163415306756371897470853214243498 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2602896814360943796676363740162650 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 24 26 3272216331281448921593187935802789 = true
    apply dfs_of_prune
    decide +kernel

theorem node_34 : dfs 4 25 25 163469156088230606349253588465034 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2602909024627640955672652520443226 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 24 26 3272228541548146081163857561563813 = true
    apply dfs_of_prune
    decide +kernel

theorem node_35 : dfs 4 25 25 163723013585482146557292553491877 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2614730787648360473271288644679050 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_26
  · change dfs 4 24 26 3294191509370691434053874687756917 = true
    apply dfs_of_prune
    decide +kernel

theorem node_36 : dfs 4 25 25 163738202539662315420618371674789 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2608079258617582388512748787644810 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_22
  · change dfs 4 24 26 3287539980339913351476811853547125 = true
    apply dfs_of_prune
    decide +kernel

theorem node_37 : dfs 4 25 25 163965839231642729238412592981413 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2609488061708447272310881554953610 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_23
  · change dfs 4 24 26 3288948783430778234316227742108277 = true
    apply dfs_of_prune
    decide +kernel

theorem node_38 : dfs 4 25 25 165005853884897560668445852650101 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2608078975249267678755820336929450 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_21
  · change dfs 4 24 26 3328104516178901982567011751470421 = true
    apply dfs_of_prune
    decide +kernel

theorem node_39 : dfs 4 25 25 165058768634430371826477172869749 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2678925353053723663400361584665941 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_27
  · change dfs 4 24 26 3256974026757796273529220041628330 = true
    apply dfs_of_prune
    decide +kernel

theorem node_40 : dfs 4 25 25 165367383608142272915201527728757 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2613052086547540869872306158394026 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_25
  · change dfs 4 24 26 3333077627477175171388742482699605 = true
    apply dfs_of_prune
    decide +kernel

theorem node_41 : dfs 4 25 25 167908206777105924105832836035925 = true := by
  apply dfs_of_children (fuel:=24)
  · change dfs 4 24 26 2612971196965945171196723518065322 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_24
  · change dfs 4 24 26 3414126376310186154372892733388117 = true
    apply dfs_of_prune
    decide +kernel

theorem node_42 : dfs 4 26 24 7777549806826412469315132622453 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 127287264649867359117849738736981 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_29
  · change dfs 4 25 25 163415306756371897470853214243498 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_33

theorem node_43 : dfs 4 26 24 10193407925435300636438454777226 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 162776216746026632230873986583898 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 25 25 204608686553558202896235646857893 = true
    apply dfs_of_prune
    decide +kernel

theorem node_44 : dfs 4 26 24 10194008763511474934870873831818 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 162445783456960067598103056571738 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 25 25 204278253264491638363841029644965 = true
    apply dfs_of_prune
    decide +kernel

theorem node_45 : dfs 4 26 24 10207228308402390085968614552970 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 163738202539662315420618371674789 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_36
  · change dfs 4 25 25 203035371146737427542556197473626 = true
    apply dfs_of_prune
    decide +kernel

theorem node_46 : dfs 4 26 24 10207230675749149884419536500106 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 162470551908148408070110412623194 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 25 25 204303021715679978995041357443749 = true
    apply dfs_of_prune
    decide +kernel

theorem node_47 : dfs 4 26 24 10207955237985819942142530640554 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 162682142960428046828741824555610 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 25 25 204514612767959617453799494702501 = true
    apply dfs_of_prune
    decide +kernel

theorem node_48 : dfs 4 26 24 10213211697818339038654308375210 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 163723013585482146557292553491877 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_35
  · change dfs 4 25 25 203020182192557258661792729737818 = true
    apply dfs_of_prune
    decide +kernel

theorem node_49 : dfs 4 26 24 10213437332437153197746208721578 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 163965839231642729238412592981413 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_37
  · change dfs 4 25 25 203263007838717841100231798381146 = true
    apply dfs_of_prune
    decide +kernel

theorem node_50 : dfs 4 26 24 10226867270551995872047975945637 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 163469156088230606349253588465034 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_34
  · change dfs 4 25 25 205935451195876291656959480908405 = true
    apply dfs_of_prune
    decide +kernel

theorem node_51 : dfs 4 26 24 10226881274715965781490737173925 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 165367383608142272915201527728757 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_40
  · change dfs 4 25 25 204030726915103269987772432823690 = true
    apply dfs_of_prune
    decide +kernel

theorem node_52 : dfs 4 26 24 10246823007677480502338786776485 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 165005853884897560668445852650101 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_38
  · change dfs 4 25 25 203669197191858558089859995186570 = true
    apply dfs_of_prune
    decide +kernel

theorem node_53 : dfs 4 26 24 10247719433454577072301524964773 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 165058768634430371826477172869749 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_39
  · change dfs 4 25 25 203722111941391368900491225249162 = true
    apply dfs_of_prune
    decide +kernel

theorem node_54 : dfs 4 26 24 10253029640461363282104915501733 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 163087668286797954227163980462474 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_31
  · change dfs 4 25 25 205553963394443639832978977621621 = true
    apply dfs_of_prune
    decide +kernel

theorem node_55 : dfs 4 26 24 10308744295051984703747110815349 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 167908206777105924105832836035925 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_41
  · change dfs 4 25 25 204036248883610462387873747110570 = true
    apply dfs_of_prune
    decide +kernel

theorem node_56 : dfs 4 26 24 10470301824838654185209546319189 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 162998746174809408476231670008490 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_30
  · change dfs 4 25 25 213070944883824470773601358476629 = true
    apply dfs_of_prune
    decide +kernel

theorem node_57 : dfs 4 26 24 10788235627319588503606123722069 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 162371101656116933652167198594389 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 25 25 203569746163534390141110666832554 = true
    apply dfs_of_prune
    decide +kernel

theorem node_58 : dfs 4 26 24 10801427326103231441789096719701 = true := by
  apply dfs_of_children (fuel:=25)
  · change dfs 4 25 25 163117580113713660825761135372970 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_32
  · change dfs 4 25 25 203048574020902887723656126223701 = true
    apply dfs_of_prune
    decide +kernel

theorem node_59 : dfs 4 27 23 479863556648341337400027208362 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 7633190070483853826596690143834 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 26 24 10247719433454577072301524964773 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_53

theorem node_60 : dfs 4 27 23 482015850631038299190943392421 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 7777549806826412469315132622453 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_42
  · change dfs 4 26 24 10194008763511474934870873831818 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_44

theorem node_61 : dfs 4 27 23 636546186441514147530453375658 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10142875993804007693085349980762 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 26 24 12757405356774731091604440667557 = true
    apply dfs_of_prune
    decide +kernel

theorem node_62 : dfs 4 27 23 637124043857664037361237183146 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10148176065600074712923947883098 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 26 24 12762705428570798088709043692965 = true
    apply dfs_of_prune
    decide +kernel

theorem node_63 : dfs 4 27 23 637127295428923756735004244362 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10253029640461363282104915501733 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_54
  · change dfs 4 26 24 12709102678403557849533174865242 = true
    apply dfs_of_prune
    decide +kernel

theorem node_64 : dfs 4 27 23 637178455777341521429331270314 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10226867270551995872047975945637 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_50
  · change dfs 4 26 24 12682940308494190563023099996762 = true
    apply dfs_of_prune
    decide +kernel

theorem node_65 : dfs 4 27 23 637334373001323125665721813674 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10226881274715965781490737173925 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_51
  · change dfs 4 26 24 12682954312658160437335536872026 = true
    apply dfs_of_prune
    decide +kernel

theorem node_66 : dfs 4 27 23 637989816714252505091227912874 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10246823007677480502338786776485 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_52
  · change dfs 4 26 24 12702896045619675061286460893786 = true
    apply dfs_of_prune
    decide +kernel

theorem node_67 : dfs 4 27 23 638000204593394080070590106282 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10154412757115365363456143088218 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 26 24 12768942120086088673012798891429 = true
    apply dfs_of_prune
    decide +kernel

theorem node_68 : dfs 4 27 23 639500804498349959451883647653 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10308744295051984703747110815349 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_55
  · change dfs 4 26 24 12725203251737047187965820451210 = true
    apply dfs_of_prune
    decide +kernel

theorem node_69 : dfs 4 27 23 640427948883193301076383454629 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10207230675749149884419536500106 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_46
  · change dfs 4 26 24 12861374119977005287627984030325 = true
    apply dfs_of_prune
    decide +kernel

theorem node_70 : dfs 4 27 23 641128924709507798086229743013 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10193407925435300636438454777226 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_43
  · change dfs 4 26 24 12847551369663156118800418556533 = true
    apply dfs_of_prune
    decide +kernel

theorem node_71 : dfs 4 27 23 641201062232278991761451558309 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10207228308402390085968614552970 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_45
  · change dfs 4 26 24 12861371752630245489177284414069 = true
    apply dfs_of_prune
    decide +kernel

theorem node_72 : dfs 4 27 23 644539204293395654688560728693 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10213211697818339038654308375210 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_48
  · change dfs 4 26 24 13025811467074723125863383737685 = true
    apply dfs_of_prune
    decide +kernel

theorem node_73 : dfs 4 27 23 645444530056693857387483073141 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10207955237985819942142530640554 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_47
  · change dfs 4 26 24 13020555007242204020544055190869 = true
    apply dfs_of_prune
    decide +kernel

theorem node_74 : dfs 4 27 23 645767302699569814139634535029 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10470301824838654185209546319189 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_56
  · change dfs 4 26 24 12728304456495187970825045498538 = true
    apply dfs_of_prune
    decide +kernel

theorem node_75 : dfs 4 27 23 654457823118508905772197999957 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10213437332437153197746208721578 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_49
  · change dfs 4 26 24 13342949751750594635403815466325 = true
    apply dfs_of_prune
    decide +kernel

theorem node_76 : dfs 4 27 23 655282310001321540571690607957 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10788235627319588503606123722069 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_57
  · change dfs 4 26 24 12729325608919064943606242052778 = true
    apply dfs_of_prune
    decide +kernel

theorem node_77 : dfs 4 27 23 655651042226865362638331880789 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10801427326103231441789096719701 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_58
  · change dfs 4 26 24 12742517307702707771289546361514 = true
    apply dfs_of_prune
    decide +kernel

theorem node_78 : dfs 4 27 23 674265905029929297859995661653 = true := by
  apply dfs_of_children (fuel:=26)
  · change dfs 4 26 24 10148219391041453363495536252245 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 26 24 12723134672755044569853945621162 = true
    apply dfs_of_prune
    decide +kernel

theorem node_79 : dfs 4 28 22 29972474357628585302173596042 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 482015850631038299190943392421 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_60
  · change dfs 4 27 23 635520415502425476769318853978 = true
    apply dfs_of_prune
    decide +kernel

theorem node_80 : dfs 4 28 22 30378680568017944953190976117 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 479863556648341337400027208362 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_59
  · change dfs 4 27 23 655651042226865362638331880789 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_77

theorem node_81 : dfs 4 28 22 39775867949465725157113154218 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 641201062232278991761451558309 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_71
  · change dfs 4 27 23 794705627103666169288090933850 = true
    apply dfs_of_prune
    decide +kernel

theorem node_82 : dfs 4 28 22 39781722119164822870946044586 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 641128924709507798086229743013 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_70
  · change dfs 4 27 23 794633489580894976957400427098 = true
    apply dfs_of_prune
    decide +kernel

theorem node_83 : dfs 4 28 22 39781723742414968909237761418 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 636191974050449377609766227290 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 27 23 799600059236119597902451880613 = true
    apply dfs_of_prune
    decide +kernel

theorem node_84 : dfs 4 28 22 39796026312302379009675987626 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 636098093323061121206998358618 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 27 23 799506178508731341132757378469 = true
    apply dfs_of_prune
    decide +kernel

theorem node_85 : dfs 4 28 22 39796131933026401642418452874 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 636098867322497216619919859034 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 27 23 799506952508167436518844637861 = true
    apply dfs_of_prune
    decide +kernel

theorem node_86 : dfs 4 28 22 39796145469117795424310831786 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 634702326115473984557771545178 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 27 23 798110411301144203750232401317 = true
    apply dfs_of_prune
    decide +kernel

theorem node_87 : dfs 4 28 22 39817973367568980435651949962 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 639500804498349959451883647653 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_68
  · change dfs 4 27 23 793005369369737145796379757914 = true
    apply dfs_of_prune
    decide +kernel

theorem node_88 : dfs 4 28 22 39819110567466926021940173482 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 635849673952355744688338840154 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 27 23 799257759138025966642463561125 = true
    apply dfs_of_prune
    decide +kernel

theorem node_89 : dfs 4 28 22 39820451851089198906650004138 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 634263862802569467071986051674 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 27 23 797671947988239721994434991525 = true
    apply dfs_of_prune
    decide +kernel

theorem node_90 : dfs 4 28 22 39910467239802421065615280810 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 640427948883193301076383454629 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_69
  · change dfs 4 27 23 793932513754580478628557662810 = true
    apply dfs_of_prune
    decide +kernel

theorem node_91 : dfs 4 28 22 39975121130351636067302856101 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 645767302699569814139634535029 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_74
  · change dfs 4 27 23 796795987492386233365704652170 = true
    apply dfs_of_prune
    decide +kernel

theorem node_92 : dfs 4 28 22 40050906259441721257623922085 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 645444530056693857387483073141 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_73
  · change dfs 4 27 23 796473214849510276957683217802 = true
    apply dfs_of_prune
    decide +kernel

theorem node_93 : dfs 4 28 22 40071266125395349778776544677 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 644539204293395654688560728693 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_72
  · change dfs 4 27 23 795567889086212090717260133770 = true
    apply dfs_of_prune
    decide +kernel

theorem node_94 : dfs 4 28 22 40074486409716112513545380517 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 637127295428923756735004244362 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_63
  · change dfs 4 27 23 803011260693164756085309081205 = true
    apply dfs_of_prune
    decide +kernel

theorem node_95 : dfs 4 28 22 40258488941856508629469973109 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 636546186441514147530453375658 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_61
  · change dfs 4 27 23 812333672020038204107405305173 = true
    apply dfs_of_prune
    decide +kernel

theorem node_96 : dfs 4 28 22 40336023295667147547556285045 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 637178455777341521429331270314 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_64
  · change dfs 4 27 23 812965941355865567373117531477 = true
    apply dfs_of_prune
    decide +kernel

theorem node_97 : dfs 4 28 22 40336061680459260063373231733 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 654457823118508905772197999957 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_75
  · change dfs 4 27 23 795582987597042299257565350570 = true
    apply dfs_of_prune
    decide +kernel

theorem node_98 : dfs 4 28 22 40338640335248883610451282549 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 655282310001321540571690607957 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_76
  · change dfs 4 27 23 796407474479854915322472389290 = true
    apply dfs_of_prune
    decide +kernel

theorem node_99 : dfs 4 28 22 40340222186643651592344389237 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 637334373001323125665721813674 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_65
  · change dfs 4 27 23 813121858579847145221956760917 = true
    apply dfs_of_prune
    decide +kernel

theorem node_100 : dfs 4 28 22 40380337998306835293039396469 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 637989816714252505091227912874 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_66
  · change dfs 4 27 23 813777302292776527442854147413 = true
    apply dfs_of_prune
    decide +kernel

theorem node_101 : dfs 4 28 22 40955509699943911358437979477 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 637124043857664037361237183146 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_62
  · change dfs 4 27 23 832718570064754163081373463893 = true
    apply dfs_of_prune
    decide +kernel

theorem node_102 : dfs 4 28 22 40958910487962403789627106645 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 638000204593394080070590106282 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_67
  · change dfs 4 27 23 833594730800484186913742681429 = true
    apply dfs_of_prune
    decide +kernel

theorem node_103 : dfs 4 28 22 40964210947734427785576490325 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 674265905029929297859995661653 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_78
  · change dfs 4 27 23 795584028879896607308792826538 = true
    apply dfs_of_prune
    decide +kernel

theorem node_104 : dfs 4 28 22 42125475250972319095155488085 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 634041297815106006132804900181 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 27 23 794973502922205500327087221418 = true
    apply dfs_of_prune
    decide +kernel

theorem node_105 : dfs 4 28 22 42219671943997409502388991317 = true := by
  apply dfs_of_children (fuel:=27)
  · change dfs 4 27 23 635553358435904970962904700245 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 27 23 796485563543004431620947684010 = true
    apply dfs_of_prune
    decide +kernel

theorem node_106 : dfs 4 29 21 1883008329835200392436426149 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 30378680568017944953190976117 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_80
  · change dfs 4 28 22 39817973367568980435651949962 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_87

theorem node_107 : dfs 4 29 21 1884217979175828082526696101 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 29972474357628585302173596042 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_79
  · change dfs 4 28 22 40340222186643651592344389237 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_99

theorem node_108 : dfs 4 29 21 2014876364469138302408488277 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 29737882649924066009045882197 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 39796145469117795424310831786 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_86

theorem node_109 : dfs 4 29 21 2485960758036371339947456906 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40074486409716112513545380517 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_94
  · change dfs 4 28 22 49668521714177815336402181466 = true
    apply dfs_of_prune
    decide +kernel

theorem node_110 : dfs 4 29 21 2485992042649289317220702890 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39617318022769604226271881818 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 49830323346874008651143894437 = true
    apply dfs_of_prune
    decide +kernel

theorem node_111 : dfs 4 29 21 2486338620187288450754063018 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39718834463574873089214405210 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 49931839787679266238732019109 = true
    apply dfs_of_prune
    decide +kernel

theorem node_112 : dfs 4 29 21 2486341774064858934943746730 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40071266125395349778776544677 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_93
  · change dfs 4 28 22 49665301429857052910015916634 = true
    apply dfs_of_prune
    decide +kernel

theorem node_113 : dfs 4 29 21 2487418197327116670556002986 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39626876092530933625134983770 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 49839881416635335576105833893 = true
    apply dfs_of_prune
    decide +kernel

theorem node_114 : dfs 4 29 21 2488543829127847809141012874 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39742882227282317352475909466 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 49955887551386710793765692069 = true
    apply dfs_of_prune
    decide +kernel

theorem node_115 : dfs 4 29 21 2488768990824672175446403754 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40050906259441721257623922085 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_92
  · change dfs 4 28 22 49644941563903424756158454362 = true
    apply dfs_of_prune
    decide +kernel

theorem node_116 : dfs 4 29 21 2488775285758075573141867178 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39723287553422896327726815834 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 49936292877527289587984147877 = true
    apply dfs_of_prune
    decide +kernel

theorem node_117 : dfs 4 29 21 2491910901398090804408268170 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39715752208023196736930008410 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 49928757532127589526735860389 = true
    apply dfs_of_prune
    decide +kernel

theorem node_118 : dfs 4 29 21 2491989623436943491513100970 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39675834439056269811229809242 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 49888839763160662279995106725 = true
    apply dfs_of_prune
    decide +kernel

theorem node_119 : dfs 4 29 21 2491999183876319027890059658 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39665661841523385727882976602 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 49878667165627783551132017317 = true
    apply dfs_of_prune
    decide +kernel

theorem node_120 : dfs 4 29 21 2492022701331370227508292266 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39713955966156007099765250650 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 28 22 49926961290260399200891413925 = true
    apply dfs_of_prune
    decide +kernel

theorem node_121 : dfs 4 29 21 2494405135138661105248111274 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39975121130351636067302856101 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_91
  · change dfs 4 28 22 49569156434813343740734384730 = true
    apply dfs_of_prune
    decide +kernel

theorem node_122 : dfs 4 29 21 2496006017456986574433133221 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40380337998306835293039396469 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_100
  · change dfs 4 28 22 49819630797857866119980611978 = true
    apply dfs_of_prune
    decide +kernel

theorem node_123 : dfs 4 29 21 2496834608478707738219992485 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39781723742414968909237761418 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_83
  · change dfs 4 28 22 50149471571430044545630685813 = true
    apply dfs_of_prune
    decide +kernel

theorem node_124 : dfs 4 29 21 2498446733646344541594759845 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 39796131933026401642418452874 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_85
  · change dfs 4 28 22 50163879762041476139218978421 = true
    apply dfs_of_prune
    decide +kernel

theorem node_125 : dfs 4 29 21 2499083543498628002953352613 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40258488941856508629469973109 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_95
  · change dfs 4 28 22 49697781741407545056727840138 = true
    apply dfs_of_prune
    decide +kernel

theorem node_126 : dfs 4 29 21 2501992900644315386887710117 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40338640335248883610451282549 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_98
  · change dfs 4 28 22 49777933134799914024988734858 = true
    apply dfs_of_prune
    decide +kernel

theorem node_127 : dfs 4 29 21 2502276582276475654420144805 = true := by
  apply dfs_of_children (fuel:=28)
  · change dfs 4 28 22 40336061680459260063373231733 = true
    exact Rule30GoldenBudgetDAG4Part0000Research.node_97
  · change dfs 4 28 22 49775354480010290480010852746 = true
    apply dfs_of_prune
    decide +kernel

end Rule30GoldenBudgetDAG4Part0000Research
