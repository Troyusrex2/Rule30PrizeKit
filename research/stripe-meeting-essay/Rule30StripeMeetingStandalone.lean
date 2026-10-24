import Ruliology.CellularAutomata.Rule30Prize

/-!
# Finite certificates for stripe meeting and two-step preservation

A balanced tree of 2321 paired-row transducer states certifies initial
membership, closure under every accepted input, exclusion of a delayed first
stripe meeting, and preservation of an existing stripe relation after two
steps. Rule30StripeMeeting proves the unbounded word and actual-row meanings.
This data module alone is not a theorem about all Rule 30 traces.
-/


set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Rule30Submission

def tailNext (s : Nat) (b : Bool) : Nat :=
  match s, b with
  | 0, false => 0 | 0, true => 1
  | 1, false => 2 | 1, true => 3
  | 2, false => 4 | 2, true => 3
  | 3, false => 2 | 3, true => 4
  | _, _ => 4

def relStep (e : Nat) (a b allow : Bool) : Nat :=
  let ta := tailNext ((e / 8) / 5) a
  let tb := tailNext ((e / 8) % 5) b
  let valid := (e.testBit 0 && (a == b)) || (e.testBit 1 && !a && !b)
  let pending := allow && a && b && (ta == 1 || ta == 3) && (tb == 1 || tb == 3)
  8 * (5 * ta + tb) + 4 * (e.testBit 2 && (a == b)).toNat +
    2 * pending.toNat + valid.toNat

def first (h : Nat) (a : Bool) : Bool := xor a (h.testBit 0 || h.testBit 1)
def second (h : Nat) (a : Bool) : Bool := xor (first h a)
  (xor (h.testBit 0) (h.testBit 1 || h.testBit 2) ||
   xor (h.testBit 1) (h.testBit 2 || h.testBit 3))

def step (s v : Nat) : Option Nat :=
  let old := s >>> 32
  let marker := v.testBit 2
  if marker && old != 0 then none else
  let code := if marker then 1 else if old == 0 then 0 else min 4 (old + 1)
  let ha := (s >>> 24) % 16
  let hb := (s >>> 28) % 16
  let a := v.testBit 0
  let b := v.testBit 1
  let a1 := first ha a
  let b1 := first hb b
  if (code == 1 && a != b) || (code == 2 && a1 != b1) then none else
  let e0 := relStep (s % 256) a b (code == 0 || code ≤ 1)
  let e1 := relStep ((s >>> 8) % 256) a1 b1 (code == 0 || code ≤ 2)
  let e2 := relStep ((s >>> 16) % 256) (second ha a) (second hb b) (code == 0 || code ≤ 3)
  some (e0 + (e1 <<< 8) + (e2 <<< 16) +
    (((2 * ha + a.toNat) % 16) <<< 24) +
    (((2 * hb + b.toNat) % 16) <<< 28) + (code <<< 32))

def flush : Nat → Nat → Option Nat
  | 0, s => some s
  | n + 1, s => (step s 0).bind (flush n)

def accept (s t : Nat) : Bool :=
  (s >>> (8*t)).testBit 0 || (s >>> (8*t)).testBit 2

def endGood (s : Nat) : Bool :=
  if s >>> 32 == 0 then true else
  match flush 5 s with
  | none => true
  | some e => !(accept e 2 && !accept e 0 && !accept e 1)

inductive StateTree where
  | nil
  | node (key : Nat) (left right : StateTree)

def member : StateTree → Nat → Bool
  | .nil, _ => false
  | .node k l r, s => if s == k then true else if s < k then member l s else member r s

def allNodes : StateTree → (Nat → Bool) → Bool
  | .nil, _ => true
  | .node k l r, f => f k && (allNodes l f && allNodes r f)

def closedAt (p : StateTree) (s : Nat) : Bool :=
  (List.range 8).all fun v => match step s v with
    | none => true
    | some s' => member p s'

def initial : Nat := 4 + (4 <<< 8) + (4 <<< 16)
def certificate (p : StateTree) : Bool :=
  member p initial && allNodes p (fun s => closedAt p s && endGood s)

def pool : StateTree := (.node 9743746501 (.node 3549585810 (.node 1522581696 (.node 700498112 (.node 327309442 (.node 161521824 (.node 58216568 (.node 12961221 (.node 12632512 (.node 10526880 (.node 2105376 (.node 263172 .nil .nil) .nil) (.node 12632256 .nil .nil)) (.node 12895684 (.node 12698049 (.node 12697793 .nil .nil) .nil) (.node 12960965 .nil .nil))) (.node 38828112 (.node 27304096 (.node 21514312 (.node 19408936 .nil .nil) .nil) (.node 29409472 .nil .nil)) (.node 44081312 (.node 40933488 .nil .nil) (.node 46186688 .nil .nil)))) (.node 96518336 (.node 79741120 (.node 62963904 (.node 60858528 (.node 60321944 .nil .nil) .nil) (.node 77635744 .nil .nil)) (.node 93876376 (.node 91771000 .nil .nil) (.node 94412960 .nil .nil))) (.node 127967392 (.node 111190176 (.node 108042352 (.node 105936976 .nil .nil) .nil) (.node 113295552 .nil .nil)) (.node 144744608 (.node 130072768 .nil .nil) (.node 146849984 .nil .nil))))) (.node 268961800 (.node 213958848 (.node 180404416 (.node 175151216 (.node 173045840 (.node 163627200 .nil .nil) .nil) (.node 178299040 .nil .nil)) (.node 197181632 (.node 195076256 .nil .nil) (.node 211853472 .nil .nil))) (.node 245407904 (.node 228630688 (.node 228094104 (.node 225988728 .nil .nil) .nil) (.node 230736064 .nil .nil)) (.node 262185120 (.node 247513280 .nil .nil) (.node 264290496 .nil .nil)))) (.node 297910465 (.node 289949768 (.node 281067712 (.node 279488680 (.node 270540832 .nil .nil) .nil) (.node 288765494 .nil .nil)) (.node 297844928 (.node 296265896 .nil .nil) (.node 297845184 .nil .nil))) (.node 307790424 (.node 298173637 (.node 298108356 (.node 297910721 .nil .nil) .nil) (.node 298173893 .nil .nil)) (.node 313043112 (.node 309368944 .nil .nil) (.node 314622144 .nil .nil)))))) (.node 538976288 (.node 432062656 (.node 374899288 (.node 348176576 (.node 331399360 (.node 329820328 (.node 328757400 .nil .nil) .nil) (.node 346597544 .nil .nil)) (.node 363374760 (.node 362311832 (.node 360863874 .nil .nil) .nil) (.node 364953792 .nil .nil))) (.node 398508224 (.node 381731008 (.node 380151976 (.node 376477808 .nil .nil) .nil) (.node 396929192 .nil .nil)) (.node 415285440 (.node 413706408 .nil .nil) (.node 430483624 .nil .nil)))) (.node 495081602 (.node 464038056 (.node 447260840 (.node 443586672 (.node 442008152 .nil .nil) .nil) (.node 448839872 .nil .nil)) (.node 480815272 (.node 465617088 .nil .nil) (.node 482394304 .nil .nil))) (.node 515948736 (.node 499171520 (.node 497592488 (.node 496529560 .nil .nil) .nil) (.node 514369704 .nil .nil)) (.node 532725952 (.node 531146920 .nil .nil) (.node 537925648 .nil .nil))))) (.node 597192856 (.node 582006960 (.node 565229744 (.node 557335096 (.node 549503168 (.node 548452528 .nil .nil) .nil) (.node 558385224 .nil .nil)) (.node 577082981 (.node 566280384 .nil .nil) (.node 577804400 .nil .nil))) (.node 583321028 (.node 583123137 (.node 583057856 (.node 583057600 .nil .nil) .nil) (.node 583123393 .nil .nil)) (.node 583386565 (.node 583386309 .nil .nil) (.node 596142216 .nil .nil)))) (.node 643928673 (.node 629696648 (.node 615561392 (.node 599834816 (.node 598784176 .nil .nil) .nil) (.node 616612032 .nil .nil)) (.node 632338608 (.node 630747288 .nil .nil) (.node 633389248 .nil .nil))) (.node 666943680 (.node 650166464 (.node 649115824 (.node 644913264 .nil .nil) .nil) (.node 665893040 .nil .nil)) (.node 683720896 (.node 682670256 .nil .nil) (.node 699447472 .nil .nil))))))) (.node 1095256136 (.node 868598981 (.node 817410232 (.node 764965016 (.node 733001904 (.node 716224688 (.node 712022128 (.node 711037537 .nil .nil) .nil) (.node 717275328 .nil .nil)) (.node 750829760 (.node 749779120 (.node 734052544 .nil .nil) .nil) (.node 763914376 .nil .nil))) (.node 800110768 (.node 783333552 (.node 767606976 (.node 766556336 .nil .nil) .nil) (.node 784384192 .nil .nil)) (.node 806883352 (.node 801161408 .nil .nil) (.node 807411744 .nil .nil)))) (.node 851493056 (.node 834715840 (.node 826820680 (.node 826423362 (.node 817938624 .nil .nil) .nil) (.node 834187448 .nil .nil)) (.node 846239856 (.node 845711464 .nil .nil) (.node 850964664 .nil .nil))) (.node 868270528 (.node 867741880 (.node 865628312 (.node 865494422 .nil .nil) .nil) (.node 868270272 .nil .nil)) (.node 868336065 (.node 868335809 .nil .nil) (.node 868533700 .nil .nil))))) (.node 979929192 (.node 913348720 (.node 899182744 (.node 885047488 (.node 884519096 (.node 868599237 .nil .nil) .nil) (.node 898785682 .nil .nil)) (.node 901824704 (.node 901296312 .nil .nil) (.node 912820328 .nil .nil))) (.node 951627960 (.node 934850744 (.node 918601920 (.node 918073528 .nil .nil) .nil) (.node 935379136 .nil .nil)) (.node 968405176 (.node 952156352 .nil .nil) (.node 968933568 .nil .nil)))) (.node 1033400472 (.node 1002488000 (.node 985710784 (.node 985182392 (.node 980457584 .nil .nil) .nil) (.node 1001959608 .nil .nil)) (.node 1019265216 (.node 1018736824 .nil .nil) (.node 1033003410 .nil .nil))) (.node 1069068472 (.node 1052291256 (.node 1036042432 (.node 1035514040 .nil .nil) .nil) (.node 1052819648 .nil .nil)) (.node 1075847200 (.node 1069596864 .nil .nil) (.node 1086374080 .nil .nil)))))) (.node 1371058360 (.node 1220591808 (.node 1153548737 (.node 1136705728 (.node 1119928512 (.node 1114675312 (.node 1103151296 .nil .nil) .nil) (.node 1134063768 .nil .nil)) (.node 1153483200 (.node 1153482944 .nil .nil) (.node 1153548481 .nil .nil))) (.node 1170260160 (.node 1153811909 (.node 1153811653 (.node 1153746372 .nil .nil) .nil) (.node 1167618200 .nil .nil)) (.node 1187037376 (.node 1181784176 .nil .nil) (.node 1203814592 .nil .nil)))) (.node 1304477888 (.node 1287700672 (.node 1254146240 (.node 1248893040 (.node 1237369024 .nil .nil) .nil) (.node 1270923456 .nil .nil)) (.node 1287766465 (.node 1287766209 .nil .nil) (.node 1301835928 .nil .nil))) (.node 1354281144 (.node 1343754264 (.node 1338032320 (.node 1321255104 .nil .nil) .nil) (.node 1344282656 .nil .nil)) (.node 1363294274 (.node 1354809536 .nil .nil) (.node 1363691592 .nil .nil))))) (.node 1438761153 (.node 1405141184 (.node 1388363968 (.node 1383110768 (.node 1382582376 (.node 1371586752 .nil .nil) .nil) (.node 1387835576 .nil .nil)) (.node 1402499224 (.node 1402102162 .nil .nil) (.node 1404612792 .nil .nil))) (.node 1436053656 (.node 1435722131 (.node 1421918400 (.node 1421390008 .nil .nil) .nil) (.node 1435985303 .nil .nil)) (.node 1438695616 (.node 1438167224 .nil .nil) (.node 1438695872 .nil .nil)))) (.node 1471721656 (.node 1449691240 (.node 1439024325 (.node 1438959044 (.node 1438761409 .nil .nil) .nil) (.node 1439024581 .nil .nil)) (.node 1454944440 (.node 1450219632 .nil .nil) (.node 1455472832 .nil .nil))) (.node 1505804480 (.node 1489027264 (.node 1488498872 (.node 1472250048 .nil .nil) .nil) (.node 1505276088 .nil .nil)) (.node 1517328496 (.node 1516800104 .nil .nil) (.node 1522053304 .nil .nil)))))))) (.node 2579546304 (.node 1925234880 (.node 1722857648 (.node 1638971568 (.node 1589690560 (.node 1569939859 (.node 1555607736 (.node 1539358912 (.node 1538830520 .nil .nil) .nil) (.node 1556136128 .nil .nil)) (.node 1572913344 (.node 1572384952 (.node 1570271384 .nil .nil) .nil) (.node 1589162168 .nil .nil))) (.node 1622194352 (.node 1611667472 (.node 1606467776 (.node 1605939384 .nil .nil) .nil) (.node 1612718112 .nil .nil)) (.node 1631076920 (.node 1623244992 .nil .nil) (.node 1632127048 .nil .nil)))) (.node 1673576640 (.node 1656799424 (.node 1651546224 (.node 1650561633 (.node 1640022208 .nil .nil) .nil) (.node 1655748784 .nil .nil)) (.node 1670934680 (.node 1669884040 .nil .nil) (.node 1672526000 .nil .nil))) (.node 1706080432 (.node 1703438472 (.node 1690353856 (.node 1689303216 .nil .nil) .nil) (.node 1704489112 .nil .nil)) (.node 1717933925 (.node 1707131072 .nil .nil) (.node 1718655088 .nil .nil))))) (.node 1806743728 (.node 1740685504 (.node 1724171716 (.node 1723973825 (.node 1723908544 (.node 1723908288 .nil .nil) .nil) (.node 1723974081 .nil .nil)) (.node 1724237253 (.node 1724236997 .nil .nil) (.node 1739634864 .nil .nil))) (.node 1784779617 (.node 1773189296 (.node 1757462720 (.node 1756412080 .nil .nil) .nil) (.node 1774239936 .nil .nil)) (.node 1789966512 (.node 1785763952 .nil .nil) (.node 1791017152 .nil .nil)))) (.node 1858126016 (.node 1838706840 (.node 1824571584 (.node 1823520944 (.node 1807794368 .nil .nil) .nil) (.node 1837656200 .nil .nil)) (.node 1841348800 (.node 1840298160 .nil .nil) (.node 1857075376 .nil .nil))) (.node 1891680448 (.node 1874903232 (.node 1873852592 (.node 1858126272 .nil .nil) .nil) (.node 1881153568 .nil .nil)) (.node 1908457664 (.node 1900562504 .nil .nil) (.node 1919981680 .nil .nil)))))) (.node 2241360024 (.node 2059452608 (.node 2009121216 (.node 1975566528 (.node 1958789312 (.node 1942012096 (.node 1939370136 .nil .nil) .nil) (.node 1972924568 .nil .nil)) (.node 1992343744 (.node 1987090544 .nil .nil) (.node 2009120960 .nil .nil))) (.node 2009449925 (.node 2009384388 (.node 2009186753 (.node 2009186497 .nil .nil) .nil) (.node 2009449669 .nil .nil)) (.node 2042675392 (.node 2025898176 .nil .nil) (.node 2054199408 .nil .nil)))) (.node 2149589024 (.node 2109784256 (.node 2093007040 (.node 2076230080 (.node 2076229824 .nil .nil) .nil) (.node 2107142296 .nil .nil)) (.node 2143338688 (.node 2126561472 .nil .nil) (.node 2143338944 .nil .nil))) (.node 2193670336 (.node 2176893120 (.node 2168997960 (.node 2160115904 .nil .nil) .nil) (.node 2188417136 .nil .nil)) (.node 2210447552 (.node 2207805592 .nil .nil) (.node 2227224768 .nil .nil))))) (.node 2378219712 (.node 2294597060 (.node 2294333632 (.node 2260779200 (.node 2255526000 (.node 2244001984 .nil .nil) .nil) (.node 2277556416 .nil .nil)) (.node 2294399169 (.node 2294333888 .nil .nil) (.node 2294399425 .nil .nil))) (.node 2327888064 (.node 2311110848 (.node 2294662597 (.node 2294662341 .nil .nil) .nil) (.node 2322634864 .nil .nil)) (.node 2361442496 (.node 2344665280 .nil .nil) (.node 2375577752 .nil .nil)))) (.node 2476241048 (.node 2437433416 (.node 2418024480 (.node 2411774144 (.node 2394996928 .nil .nil) .nil) (.node 2428551360 .nil .nil)) (.node 2456852592 (.node 2445328576 .nil .nil) (.node 2462105792 .nil .nil))) (.node 2523961456 (.node 2509795480 (.node 2495660224 (.node 2478883008 .nil .nil) .nil) (.node 2512437440 .nil .nil)) (.node 2545991872 (.node 2529214656 .nil .nil) (.node 2562769088 .nil .nil))))))) (.node 2982199488 (.node 2791412577 (.node 2704818744 (.node 2629877952 (.node 2579875013 (.node 2579612097 (.node 2579611841 (.node 2579546560 .nil .nil) .nil) (.node 2579809732 .nil .nil)) (.node 2596323520 (.node 2591070320 (.node 2579875269 .nil .nil) .nil) (.node 2613100736 .nil .nil))) (.node 2685409296 (.node 2663432384 (.node 2646655168 (.node 2644013208 .nil .nil) .nil) (.node 2680209600 .nil .nil)) (.node 2695936176 (.node 2686459936 .nil .nil) (.node 2696986816 .nil .nil)))) (.node 2744676504 (.node 2725288048 (.node 2713764032 (.node 2712713392 (.node 2705868872 .nil .nil) .nil) (.node 2724303457 .nil .nil)) (.node 2730541248 (.node 2729490608 .nil .nil) (.node 2743625864 .nil .nil))) (.node 2777180296 (.node 2763045040 (.node 2747318464 (.node 2746267824 .nil .nil) .nil) (.node 2764095680 .nil .nil)) (.node 2779822256 (.node 2778230936 .nil .nil) (.node 2780872896 .nil .nil))))) (.node 2865022404 (.node 2847981760 (.node 2814427328 (.node 2797650112 (.node 2796599472 (.node 2792396912 .nil .nil) .nil) (.node 2813376688 .nil .nil)) (.node 2831204544 (.node 2830153904 .nil .nil) (.node 2846931120 .nil .nil))) (.node 2864758976 (.node 2859505776 (.node 2858784613 (.node 2858521441 .nil .nil) .nil) (.node 2863708336 .nil .nil)) (.node 2864824513 (.node 2864759232 .nil .nil) (.node 2864824769 .nil .nil)))) (.node 2914039984 (.node 2897262768 (.node 2880485552 (.node 2865087941 (.node 2865087685 .nil .nil) .nil) (.node 2881536192 .nil .nil)) (.node 2911398024 (.node 2898313408 .nil .nil) (.node 2912448664 .nil .nil))) (.node 2948645056 (.node 2931867840 (.node 2930817200 (.node 2915090624 .nil .nil) .nil) (.node 2947594416 .nil .nil)) (.node 2965422272 (.node 2954895392 .nil .nil) (.node 2974304328 .nil .nil)))))) (.node 3300966592 (.node 3150037185 (.node 3066085568 (.node 3032531136 (.node 3013111960 (.node 2998976704 (.node 2993723504 .nil .nil) .nil) (.node 3015753920 .nil .nil)) (.node 3049308352 (.node 3046666392 .nil .nil) (.node 3060832368 .nil .nil))) (.node 3127941232 (.node 3099640000 (.node 3082863040 (.node 3082862784 .nil .nil) .nil) (.node 3116417216 .nil .nil)) (.node 3149971648 (.node 3133194432 .nil .nil) (.node 3149971904 .nil .nil)))) (.node 3217080512 (.node 3166748864 (.node 3150300357 (.node 3150235076 (.node 3150037441 .nil .nil) .nil) (.node 3150300613 .nil .nil)) (.node 3183526080 (.node 3180884120 .nil .nil) (.node 3200303296 .nil .nil))) (.node 3262158960 (.node 3242739784 (.node 3233857728 (.node 3223330848 .nil .nil) .nil) (.node 3250634944 .nil .nil)) (.node 3281547416 (.node 3267412160 .nil .nil) (.node 3284189376 .nil .nil))))) (.node 3435513029 (.node 3384852672 (.node 3329267824 (.node 3315101848 (.node 3301032385 (.node 3301032129 .nil .nil) .nil) (.node 3317743808 .nil .nil)) (.node 3351298240 (.node 3334521024 .nil .nil) (.node 3368075456 .nil .nil))) (.node 3435184576 (.node 3418407104 (.node 3401629888 (.node 3396376688 .nil .nil) .nil) (.node 3435184320 .nil .nil)) (.node 3435250113 (.node 3435249857 .nil .nil) (.node 3435447748 .nil .nil)))) (.node 3502293184 (.node 3485515968 (.node 3451961536 (.node 3449319576 (.node 3435513285 .nil .nil) .nil) (.node 3468738752 .nil .nil)) (.node 3491766304 (.node 3491237912 .nil .nil) (.node 3501764792 .nil .nil))) (.node 3530066024 (.node 3518542008 (.node 3511175240 (.node 3510777922 .nil .nil) .nil) (.node 3519070400 .nil .nil)) (.node 3535319224 (.node 3530594416 .nil .nil) (.node 3535847616 .nil .nil))))))))) (.node 6018941121 (.node 4623724696 (.node 4028637216 (.node 3720725957 (.node 3653288128 (.node 3597174888 (.node 3569402048 (.node 3552624832 (.node 3552096440 (.node 3549982872 .nil .nil) .nil) (.node 3568873656 .nil .nil)) (.node 3585650872 (.node 3583537304 (.node 3583205779 .nil .nil) .nil) (.node 3586179264 .nil .nil))) (.node 3619733696 (.node 3602956480 (.node 3602428088 (.node 3597703280 .nil .nil) .nil) (.node 3619205304 .nil .nil)) (.node 3636510912 (.node 3635982520 .nil .nil) (.node 3652759736 .nil .nil)))) (.node 3717686679 (.node 3686314168 (.node 3669536952 (.node 3664812144 (.node 3664283752 .nil .nil) .nil) (.node 3670065344 .nil .nil)) (.node 3703091384 (.node 3686842560 .nil .nil) (.node 3703619776 .nil .nil))) (.node 3720462529 (.node 3720396992 (.node 3719868600 (.node 3717755032 .nil .nil) .nil) (.node 3720397248 .nil .nil)) (.node 3720660420 (.node 3720462785 .nil .nil) (.node 3720725701 .nil .nil))))) (.node 3871392192 (.node 3799029872 (.node 3760201760 (.node 3753423032 (.node 3737174208 (.node 3736645816 .nil .nil) .nil) (.node 3753951424 .nil .nil)) (.node 3779610696 (.node 3770728640 .nil .nil) (.node 3787505856 .nil .nil))) (.node 3851972760 (.node 3821060288 (.node 3818418328 (.node 3804283072 .nil .nil) .nil) (.node 3837837504 .nil .nil)) (.node 3866138736 (.node 3854614720 .nil .nil) (.node 3871391936 .nil .nil)))) (.node 3988832448 (.node 3938500800 (.node 3921723584 (.node 3904946368 (.node 3888169152 .nil .nil) .nil) (.node 3933247600 .nil .nil)) (.node 3972055232 (.node 3955278016 .nil .nil) (.node 3986190488 .nil .nil))) (.node 4005873092 (.node 4005675201 (.node 4005609920 (.node 4005609664 .nil .nil) .nil) (.node 4005675457 .nil .nil)) (.node 4005938629 (.node 4005938373 .nil .nil) (.node 4022386880 .nil .nil)))))) (.node 4307665089 (.node 4206936256 (.node 4120408216 (.node 4072718528 (.node 4055941312 (.node 4048046152 (.node 4039164096 .nil .nil) .nil) (.node 4067465328 .nil .nil)) (.node 4089495744 (.node 4086853784 .nil .nil) (.node 4106272960 .nil .nil))) (.node 4156604864 (.node 4139827392 (.node 4134574192 (.node 4123050176 .nil .nil) .nil) (.node 4156604608 .nil .nil)) (.node 4190159040 (.node 4173381824 .nil .nil) (.node 4201683056 .nil .nil)))) (.node 4290888129 (.node 4274045120 (.node 4254625944 (.node 4240490688 (.node 4223713472 .nil .nil) .nil) (.node 4257267904 .nil .nil)) (.node 4290822592 (.node 4290822336 .nil .nil) (.node 4290887873 .nil .nil))) (.node 4297072672 (.node 4291151301 (.node 4291151045 (.node 4291085764 .nil .nil) .nil) (.node 4295230468 .nil .nil)) (.node 4307599552 (.node 4305494176 .nil .nil) (.node 4307599808 .nil .nil))))) (.node 4470118512 (.node 4372603040 (.node 4333795408 (.node 4307928261 (.node 4307862980 (.node 4307665345 .nil .nil) .nil) (.node 4307928517 .nil .nil)) (.node 4339048608 (.node 4335900784 .nil .nil) (.node 4341153984 .nil .nil))) (.node 4408262848 (.node 4403009648 (.node 4400904272 (.node 4374708416 .nil .nil) .nil) (.node 4406157472 .nil .nil)) (.node 4441817280 (.node 4439711904 .nil .nil) (.node 4468013136 .nil .nil)))) (.node 4591233192 (.node 4540375200 (.node 4506820768 (.node 4475371712 (.node 4473266336 .nil .nil) .nil) (.node 4508926144 .nil .nil)) (.node 4583732790 (.node 4542480576 .nil .nil) (.node 4584917064 .nil .nil))) (.node 4593075652 (.node 4592877761 (.node 4592812480 (.node 4592812224 .nil .nil) .nil) (.node 4592878017 .nil .nil)) (.node 4593141189 (.node 4593140933 .nil .nil) (.node 4622276738 .nil .nil))))))) (.node 5327970706 (.node 4944083120 (.node 4832892944 (.node 4727029952 (.node 4658342056 (.node 4655831170 (.node 4626366656 (.node 4624787624 .nil .nil) .nil) (.node 4657279128 .nil .nil)) (.node 4693475520 (.node 4691896488 (.node 4659921088 .nil .nil) .nil) (.node 4725450920 .nil .nil))) (.node 4792559784 (.node 4790048898 (.node 4760584384 (.node 4759005352 .nil .nil) .nil) (.node 4791496856 .nil .nil)) (.node 4826114216 (.node 4794138816 .nil .nil) (.node 4827693248 .nil .nil)))) (.node 4878090433 (.node 4872771696 (.node 4844470464 (.node 4843419824 (.node 4833943584 .nil .nil) .nil) (.node 4872050277 .nil .nil)) (.node 4878024896 (.node 4876974256 .nil .nil) (.node 4878025152 .nil .nil))) (.node 4910528688 (.node 4878353605 (.node 4878288324 (.node 4878090689 .nil .nil) .nil) (.node 4878353861 .nil .nil)) (.node 4938895969 (.node 4911579328 .nil .nil) (.node 4939880560 .nil .nil))))) (.node 5162709176 (.node 5045797056 (.node 5006989424 (.node 4978688192 (.node 4977637552 (.node 4945133760 .nil .nil) .nil) (.node 5006004833 .nil .nil)) (.node 5012242624 (.node 5011191984 .nil .nil) (.node 5044746416 .nil .nil))) (.node 5129154744 (.node 5121390658 (.node 5079351488 (.node 5078300848 .nil .nil) .nil) (.node 5121787976 .nil .nil)) (.node 5160461718 (.node 5129683136 .nil .nil) (.node 5160595608 .nil .nil)))) (.node 5194150040 (.node 5163500996 (.node 5163303105 (.node 5163237824 (.node 5163237568 .nil .nil) .nil) (.node 5163303361 .nil .nil)) (.node 5163566533 (.node 5163566277 .nil .nil) (.node 5193752978 .nil .nil))) (.node 5263372472 (.node 5229818040 (.node 5196792000 (.node 5196263608 .nil .nil) .nil) (.node 5230346432 .nil .nil)) (.node 5296926904 (.node 5263900864 .nil .nil) (.node 5297455296 .nil .nil)))))) (.node 5731020952 (.node 5482004672 (.node 5414895808 (.node 5364564160 (.node 5331009728 (.node 5330481336 (.node 5328367768 .nil .nil) .nil) (.node 5364035768 .nil .nil)) (.node 5381341376 (.node 5370814496 .nil .nil) (.node 5409642608 .nil .nil))) (.node 5448713668 (.node 5448515777 (.node 5448450496 (.node 5448450240 .nil .nil) .nil) (.node 5448516033 .nil .nil)) (.node 5448779205 (.node 5448778949 .nil .nil) (.node 5476751472 .nil .nil)))) (.node 5658658888 (.node 5582733505 (.node 5549113536 (.node 5543860336 (.node 5515559104 .nil .nil) .nil) (.node 5582667968 .nil .nil)) (.node 5616222400 (.node 5582733761 .nil .nil) (.node 5658261570 .nil .nil))) (.node 5699580088 (.node 5697069458 (.node 5666554048 (.node 5666025656 .nil .nil) .nil) (.node 5697466520 .nil .nil)) (.node 5730689427 (.node 5700108480 .nil .nil) (.node 5730952599 .nil .nil))))) (.node 5867880640 (.node 5766688952 (.node 5733728705 (.node 5733663168 (.node 5733662912 (.node 5733134520 .nil .nil) .nil) (.node 5733728449 .nil .nil)) (.node 5733991621 (.node 5733926340 .nil .nil) (.node 5733991877 .nil .nil))) (.node 5834326208 (.node 5800771776 (.node 5800243384 (.node 5767217344 .nil .nil) .nil) (.node 5833797816 .nil .nil)) (.node 5865238680 (.node 5864907155 .nil .nil) (.node 5867352248 .nil .nil)))) (.node 5950716080 (.node 5917161648 (.node 5906634768 (.node 5901435072 (.node 5900906680 .nil .nil) .nil) (.node 5907685408 .nil .nil)) (.node 5945528929 (.node 5918212288 .nil .nil) (.node 5946513520 .nil .nil))) (.node 6013622384 (.node 5985321152 (.node 5984270512 (.node 5951766720 .nil .nil) .nil) (.node 6012901221 .nil .nil)) (.node 6018875584 (.node 6017824944 .nil .nil) (.node 6018875840 .nil .nil)))))))) (.node 7814037696 (.node 6981427232 (.node 6455083200 (.node 6236979392 (.node 6085984448 (.node 6051379376 (.node 6019204293 (.node 6019139012 (.node 6018941377 .nil .nil) .nil) (.node 6019204549 .nil .nil)) (.node 6080731248 (.node 6079746913 (.node 6052430016 .nil .nil) .nil) (.node 6084933808 .nil .nil))) (.node 6153093568 (.node 6152042672 (.node 6119538880 (.node 6118488240 .nil .nil) .nil) (.node 6153093312 .nil .nil)) (.node 6203424960 (.node 6195529800 .nil .nil) (.node 6234337432 .nil .nil)))) (.node 6304417221 (.node 6304153793 (.node 6304088256 (.node 6270533824 (.node 6267891864 .nil .nil) .nil) (.node 6304088512 .nil .nil)) (.node 6304351684 (.node 6304154049 .nil .nil) (.node 6304416965 .nil .nil))) (.node 6404751552 (.node 6371197376 (.node 6371197120 (.node 6337642688 .nil .nil) .nil) (.node 6402109592 .nil .nil)) (.node 6438306240 (.node 6438305984 .nil .nil) (.node 6444556320 .nil .nil))))) (.node 6740295872 (.node 6589366721 (.node 6555746496 (.node 6522192064 (.node 6488637632 (.node 6483384432 .nil .nil) .nil) (.node 6550493296 .nil .nil)) (.node 6589301184 (.node 6589300928 .nil .nil) (.node 6589366465 .nil .nil))) (.node 6622855360 (.node 6589629893 (.node 6589629637 (.node 6589564356 .nil .nil) .nil) (.node 6617602160 .nil .nil)) (.node 6689964224 (.node 6656409792 .nil .nil) (.node 6732400712 .nil .nil)))) (.node 6874579393 (.node 6840959168 (.node 6804762776 (.node 6773850304 (.node 6771208344 .nil .nil) .nil) (.node 6807404736 .nil .nil)) (.node 6874513856 (.node 6874513600 .nil .nil) (.node 6874579137 .nil .nil))) (.node 6938980504 (.node 6874842565 (.node 6874842309 (.node 6874777028 .nil .nil) .nil) (.node 6908068032 .nil .nil)) (.node 6975176896 (.node 6941622464 .nil .nil) (.node 6980376592 .nil .nil)))))) (.node 7377830080 (.node 7158675632 (.node 7086379873 (.node 7024457904 (.node 7019270753 (.node 6991954112 (.node 6990903472 .nil .nil) .nil) (.node 7020255344 .nil .nil)) (.node 7058012336 (.node 7025508544 .nil .nil) (.node 7059062976 .nil .nil))) (.node 7126171840 (.node 7092617408 (.node 7091566768 (.node 7087364208 .nil .nil) .nil) (.node 7125121200 .nil .nil)) (.node 7153751909 (.node 7153488737 .nil .nil) (.node 7154473072 .nil .nil)))) (.node 7193280704 (.node 7159989700 (.node 7159791809 (.node 7159726528 (.node 7159726272 .nil .nil) .nil) (.node 7159792065 .nil .nil)) (.node 7160055237 (.node 7160054981 .nil .nil) (.node 7192230064 .nil .nil))) (.node 7308079256 (.node 7269271624 (.node 7226835136 (.node 7225784496 .nil .nil) .nil) (.node 7277166784 .nil .nil)) (.node 7341633688 (.node 7310721216 .nil .nil) (.node 7344275648 .nil .nil))))) (.node 7595999425 (.node 7445267909 (.node 7445004481 (.node 7444938944 (.node 7411384512 (.node 7377830336 .nil .nil) .nil) (.node 7444939200 .nil .nil)) (.node 7445202372 (.node 7445004737 .nil .nil) (.node 7445267653 .nil .nil))) (.node 7528825024 (.node 7512047808 (.node 7478493376 (.node 7475851416 .nil .nil) .nil) (.node 7518298144 .nil .nil)) (.node 7562379456 (.node 7557126256 .nil .nil) (.node 7595933888 .nil .nil)))) (.node 7730217153 (.node 7691343984 (.node 7629488320 (.node 7624235120 (.node 7595999681 .nil .nil) .nil) (.node 7663042752 .nil .nil)) (.node 7730151616 (.node 7696597184 .nil .nil) (.node 7730151872 .nil .nil))) (.node 7763706048 (.node 7730480325 (.node 7730415044 (.node 7730217409 .nil .nil) .nil) (.node 7730480581 .nil .nil)) (.node 7806142536 (.node 7805745218 .nil .nil) (.node 7813509304 .nil .nil))))))) (.node 8602895557 (.node 8233468096 (.node 8015364544 (.node 7914700992 (.node 7878173075 (.node 7847063736 (.node 7844950168 (.node 7844553106 .nil .nil) .nil) (.node 7847592128 .nil .nil)) (.node 7881146560 (.node 7880618168 (.node 7878504600 .nil .nil) .nil) (.node 7914172600 .nil .nil))) (.node 8012653975 (.node 7981281464 (.node 7948255424 (.node 7947727032 .nil .nil) .nil) (.node 7981809856 .nil .nil)) (.node 8014835896 (.node 8012722328 .nil .nil) (.node 8015364288 .nil .nil)))) (.node 8065695936 (.node 8015693253 (.node 8015627716 (.node 8015430081 (.node 8015429825 .nil .nil) .nil) (.node 8015692997 .nil .nil)) (.node 8048918720 (.node 8048390328 .nil .nil) (.node 8055169056 .nil .nil))) (.node 8166359232 (.node 8132804800 (.node 8099250368 (.node 8093997168 .nil .nil) .nil) (.node 8161106032 .nil .nil)) (.node 8199913664 (.node 8166359488 .nil .nil) (.node 8228214896 .nil .nil))))) (.node 8518680768 (.node 8343013448 (.node 8300642753 (.node 8300577216 (.node 8300576960 (.node 8267022528 .nil .nil) .nil) (.node 8300642497 .nil .nil)) (.node 8300905669 (.node 8300840388 .nil .nil) (.node 8300905925 .nil .nil))) (.node 8418017472 (.node 8384463040 (.node 8381821080 (.node 8350908608 .nil .nil) .nil) (.node 8415375512 .nil .nil)) (.node 8451572160 (.node 8451571904 .nil .nil) (.node 8485126336 .nil .nil)))) (.node 8586118597 (.node 8585855169 (.node 8585789632 (.node 8552235200 (.node 8549593240 .nil .nil) .nil) (.node 8585789888 .nil .nil)) (.node 8586053060 (.node 8585855425 .nil .nil) (.node 8586118341 .nil .nil))) (.node 8602567104 (.node 8600461472 (.node 8592039968 (.node 8590197764 .nil .nil) .nil) (.node 8602566848 .nil .nil)) (.node 8602632641 (.node 8602632385 .nil .nil) (.node 8602830276 .nil .nil)))))) (.node 9173320901 (.node 8887845313 (.node 8818028696 (.node 8686452928 (.node 8683810968 (.node 8681705592 (.node 8602895813 .nil .nil) .nil) (.node 8684347552 .nil .nil)) (.node 8736784576 (.node 8734679200 .nil .nil) (.node 8815923320 .nil .nil))) (.node 8886200488 (.node 8878700084 (.node 8820670656 (.node 8818565280 .nil .nil) .nil) (.node 8879884360 .nil .nil)) (.node 8887779776 (.node 8887779520 .nil .nil) (.node 8887845057 .nil .nil)))) (.node 9072328896 (.node 8938111168 (.node 8888108485 (.node 8888108229 (.node 8888042948 .nil .nil) .nil) (.node 8936532136 .nil .nil)) (.node 9021997248 (.node 9020418216 .nil .nil) (.node 9070749864 .nil .nil))) (.node 9172992448 (.node 9171941552 (.node 9167738992 (.node 9167017573 .nil .nil) .nil) (.node 9172992192 .nil .nil)) (.node 9173057985 (.node 9173057729 .nil .nil) (.node 9173255620 .nil .nil))))) (.node 9458270657 (.node 9307209920 (.node 9240101056 (.node 9234847856 (.node 9233863265 (.node 9173321157 .nil .nil) .nil) (.node 9239050416 .nil .nil)) (.node 9301956720 (.node 9300972129 .nil .nil) (.node 9306159280 .nil .nil))) (.node 9457676472 (.node 9455429012 (.node 9374318784 (.node 9373268144 .nil .nil) .nil) (.node 9455562904 .nil .nil)) (.node 9458205120 (.node 9458204864 .nil .nil) (.node 9458270401 .nil .nil)))) (.node 9659531456 (.node 9525313728 (.node 9458533829 (.node 9458533573 (.node 9458468292 .nil .nil) .nil) (.node 9524785336 .nil .nil)) (.node 9592422592 (.node 9591894200 .nil .nil) (.node 9659003064 .nil .nil))) (.node 9743483073 (.node 9743417536 (.node 9693085888 (.node 9685190728 .nil .nil) .nil) (.node 9743417792 .nil .nil)) (.node 9743680964 (.node 9743483329 .nil .nil) (.node 9743746245 .nil .nil)))))))))) (.node 17863590080 (.node 14608875969 (.node 12310397377 (.node 11027368008 (.node 10314106308 (.node 10028959173 (.node 10025919893 (.node 9933688856 (.node 9877700801 (.node 9877635264 (.node 9827303616 .nil .nil) .nil) (.node 9877701057 .nil .nil)) (.node 9944744128 (.node 9944215736 (.node 9934217248 .nil .nil) .nil) (.node 10025656721 .nil .nil))) (.node 10028695745 (.node 10028630208 (.node 10028101816 (.node 10025988248 .nil .nil) .nil) (.node 10028630464 .nil .nil)) (.node 10028893636 (.node 10028696001 .nil .nil) (.node 10028958917 .nil .nil)))) (.node 10245683376 (.node 10162319544 (.node 10159874449 (.node 10078961856 (.node 10078433464 .nil .nil) .nil) (.node 10160205976 .nil .nil)) (.node 10240496225 (.node 10162847936 .nil .nil) (.node 10241480816 .nil .nil))) (.node 10313842880 (.node 10308589680 (.node 10307868517 (.node 10246734016 .nil .nil) .nil) (.node 10312792240 .nil .nil)) (.node 10313908417 (.node 10313843136 .nil .nil) (.node 10313908673 .nil .nil))))) (.node 10599384517 (.node 10448060864 (.node 10379901104 (.node 10374714209 (.node 10314171845 (.node 10314171589 .nil .nil) .nil) (.node 10375698544 .nil .nil)) (.node 10447009968 (.node 10380951744 .nil .nil) (.node 10448060608 .nil .nil))) (.node 10599121089 (.node 10599055552 (.node 10531946688 (.node 10529304728 .nil .nil) .nil) (.node 10599055808 .nil .nil)) (.node 10599318980 (.node 10599121345 .nil .nil) (.node 10599384261 .nil .nil)))) (.node 10884268224 (.node 10739523616 (.node 10733273280 (.node 10666164672 (.node 10666164416 .nil .nil) .nil) (.node 10733273536 .nil .nil)) (.node 10831294616 (.node 10750050496 .nil .nil) (.node 10833936576 .nil .nil))) (.node 10884596933 (.node 10884334017 (.node 10884333761 (.node 10884268480 .nil .nil) .nil) (.node 10884531652 .nil .nil)) (.node 10965512344 (.node 10884597189 .nil .nil) (.node 10968154304 .nil .nil)))))) (.node 11739906496 (.node 11448456033 (.node 11219812544 (.node 11169546433 (.node 11169480896 (.node 11085594816 (.node 11035263168 .nil .nil) .nil) (.node 11169481152 .nil .nil)) (.node 11169809605 (.node 11169744324 (.node 11169546689 .nil .nil) .nil) (.node 11169809861 .nil .nil))) (.node 11381347169 (.node 11319425200 (.node 11315222640 (.node 11314238049 .nil .nil) .nil) (.node 11320475840 .nil .nil)) (.node 11386534064 (.node 11382331504 .nil .nil) (.node 11387584704 .nil .nil)))) (.node 11455022277 (.node 11454693824 (.node 11453642928 (.node 11449440368 (.node 11448719205 .nil .nil) .nil) (.node 11454693568 .nil .nil)) (.node 11454759361 (.node 11454759105 .nil .nil) (.node 11454956996 .nil .nil))) (.node 11605688512 (.node 11521802432 (.node 11520751792 (.node 11455022533 .nil .nil) .nil) (.node 11603046552 .nil .nil)) (.node 11672797632 (.node 11672797376 .nil .nil) (.node 11739906240 .nil .nil))))) (.node 12025447621 (.node 11890901184 (.node 11740235205 (.node 11740169668 (.node 11739972033 (.node 11739971777 .nil .nil) .nil) (.node 11740234949 .nil .nil)) (.node 11832674376 (.node 11807015104 .nil .nil) (.node 11840569536 .nil .nil))) (.node 12025119168 (.node 11974787264 (.node 11890966977 (.node 11890966721 .nil .nil) .nil) (.node 12025118912 .nil .nil)) (.node 12025184705 (.node 12025184449 .nil .nil) (.node 12025382340 .nil .nil)))) (.node 12176113856 (.node 12092227776 (.node 12081700896 (.node 12081172504 (.node 12025447877 .nil .nil) .nil) (.node 12091699384 .nil .nil)) (.node 12173471896 (.node 12173140369 .nil .nil) (.node 12175585464 .nil .nil))) (.node 12309803192 (.node 12307621269 (.node 12226445504 (.node 12225917112 .nil .nil) .nil) (.node 12307689624 .nil .nil)) (.node 12310331840 (.node 12310331584 .nil .nil) (.node 12310397121 .nil .nil))))))) (.node 13467959488 (.node 12897797572 (.node 12679430336 (.node 12528435392 (.node 12394217664 (.node 12310660549 (.node 12310660293 (.node 12310595012 .nil .nil) .nil) (.node 12388964464 .nil .nil)) (.node 12461326784 (.node 12461326528 (.node 12456073328 .nil .nil) .nil) (.node 12523182192 .nil .nil))) (.node 12595807684 (.node 12595609793 (.node 12595544512 (.node 12595544256 .nil .nil) .nil) (.node 12595610049 .nil .nil)) (.node 12595873221 (.node 12595872965 .nil .nil) (.node 12676788376 .nil .nil)))) (.node 12881085637 (.node 12880757184 (.node 12813648064 (.node 12746539456 (.node 12746539200 .nil .nil) .nil) (.node 12880756928 .nil .nil)) (.node 12880822721 (.node 12880822465 .nil .nil) (.node 12881020356 .nil .nil))) (.node 12897534144 (.node 12887007264 (.node 12885165060 (.node 12881085893 .nil .nil) .nil) (.node 12895428768 .nil .nil)) (.node 12897599681 (.node 12897534400 .nil .nil) (.node 12897599937 .nil .nil))))) (.node 13174851656 (.node 13063200928 (.node 12912205984 (.node 12904310824 (.node 12897863109 (.node 12897862853 .nil .nil) .nil) (.node 12906416200 .nil .nil)) (.node 13057947728 (.node 12914311360 .nil .nil) (.node 13060053104 .nil .nil))) (.node 13155442720 (.node 13082083520 (.node 13079978144 (.node 13065306304 .nil .nil) .nil) (.node 13153863688 .nil .nil)) (.node 13165969600 (.node 13164390568 .nil .nil) (.node 13173666868 .nil .nil)))) (.node 13326909528 (.node 13182812609 (.node 13182747072 (.node 13182746816 (.node 13181167784 .nil .nil) .nil) (.node 13182812353 .nil .nil)) (.node 13183075525 (.node 13183010244 .nil .nil) (.node 13183075781 .nil .nil))) (.node 13350518976 (.node 13333741760 (.node 13332162728 (.node 13328488560 .nil .nil) .nil) (.node 13348939944 .nil .nil)) (.node 13462706288 (.node 13461984356 .nil .nil) (.node 13466908848 .nil .nil)))))) (.node 14038450625 (.node 13736394944 (.node 13483686064 (.node 13468288197 (.node 13468025281 (.node 13468025025 (.node 13467959744 .nil .nil) .nil) (.node 13468222916 .nil .nil)) (.node 13481044104 (.node 13468288453 .nil .nil) (.node 13482094744 .nil .nil))) (.node 13585400000 (.node 13568622784 (.node 13567572144 (.node 13484736704 .nil .nil) .nil) (.node 13584349360 .nil .nil)) (.node 13731141744 (.node 13730613352 .nil .nil) (.node 13735866552 .nil .nil)))) (.node 13753500869 (.node 13753172416 (.node 13752643768 (.node 13750530200 (.node 13750396308 .nil .nil) .nil) (.node 13753172160 .nil .nil)) (.node 13753237953 (.node 13753237697 .nil .nil) (.node 13753435588 .nil .nil))) (.node 13853835456 (.node 13837058240 (.node 13836529848 (.node 13753501125 .nil .nil) .nil) (.node 13853307064 .nil .nil)) (.node 14038385088 (.node 14038384832 .nil .nil) (.node 14038450369 .nil .nil))))) (.node 14323597760 (.node 14186737816 (.node 14055162048 (.node 14038713797 (.node 14038713541 (.node 14038648260 .nil .nil) .nil) (.node 14052520088 .nil .nil)) (.node 14172668097 (.node 14172602560 .nil .nil) (.node 14172668353 .nil .nil))) (.node 14320887189 (.node 14306820288 (.node 14306291896 (.node 14189379776 .nil .nil) .nil) (.node 14320624017 .nil .nil)) (.node 14323069112 (.node 14320955544 .nil .nil) (.node 14323597504 .nil .nil)))) (.node 14455173272 (.node 14323926469 (.node 14323860932 (.node 14323663297 (.node 14323663041 .nil .nil) .nil) (.node 14323926213 .nil .nil)) (.node 14441038016 (.node 14440509624 .nil .nil) (.node 14454841745 .nil .nil))) (.node 14607759536 (.node 14602835300 (.node 14457815232 (.node 14457286840 .nil .nil) .nil) (.node 14603556976 .nil .nil)) (.node 14608810432 (.node 14608810176 .nil .nil) (.node 14608875713 .nil .nil)))))))) (.node 17192764868 (.node 16018096320 (.node 15361142936 (.node 14894351813 (.node 14759805120 (.node 14625587392 (.node 14609139141 (.node 14609138885 (.node 14609073604 .nil .nil) .nil) (.node 14624536752 .nil .nil)) (.node 14743028160 (.node 14743027904 (.node 14741977264 .nil .nil) .nil) (.node 14758754480 .nil .nil))) (.node 14894088385 (.node 14894022848 (.node 14877245632 (.node 14871992432 .nil .nil) .nil) (.node 14894023104 .nil .nil)) (.node 14894286276 (.node 14894088641 .nil .nil) (.node 14894351557 .nil .nil)))) (.node 15179235776 (.node 15078572224 (.node 15028240832 (.node 15028240576 (.node 15011463360 .nil .nil) .nil) (.node 15073319024 .nil .nil)) (.node 15095349440 (.node 15092707480 .nil .nil) (.node 15179235520 .nil .nil))) (.node 15179564485 (.node 15179498948 (.node 15179301313 (.node 15179301057 .nil .nil) .nil) (.node 15179564229 .nil .nil)) (.node 15341754480 (.node 15196012736 .nil .nil) (.node 15347007680 .nil .nil))))) (.node 15743422817 (.node 15464777157 (.node 15464513729 (.node 15464448192 (.node 15447670976 (.node 15363784896 .nil .nil) .nil) (.node 15464448448 .nil .nil)) (.node 15464711620 (.node 15464513985 .nil .nil) (.node 15464776901 .nil .nil))) (.node 15589720120 (.node 15580838064 (.node 15571361824 (.node 15570311184 .nil .nil) .nil) (.node 15581888704 .nil .nil)) (.node 15597615280 (.node 15590770760 .nil .nil) (.node 15598665920 .nil .nil)))) (.node 15749989573 (.node 15749661120 (.node 15748610224 (.node 15744407664 (.node 15743685989 .nil .nil) .nil) (.node 15749660864 .nil .nil)) (.node 15749726657 (.node 15749726401 .nil .nil) (.node 15749924292 .nil .nil))) (.node 15850324160 (.node 15766438080 (.node 15765387440 (.node 15749989829 .nil .nil) .nil) (.node 15839797280 .nil .nil)) (.node 15867101376 (.node 15859206216 .nil .nil) (.node 16012843120 .nil .nil)))))) (.node 16605364673 (.node 16320414917 (.node 16185934017 (.node 16035136964 (.node 16034939073 (.node 16034873792 (.node 16034873536 .nil .nil) .nil) (.node 16034939329 .nil .nil)) (.node 16035202501 (.node 16035202245 .nil .nil) (.node 16185868480 .nil .nil))) (.node 16320086464 (.node 16202645696 (.node 16200003736 (.node 16185934273 .nil .nil) .nil) (.node 16320086208 .nil .nil)) (.node 16320152001 (.node 16320151745 .nil .nil) (.node 16320349636 .nil .nil)))) (.node 16471081152 (.node 16454303936 (.node 16336863424 (.node 16334221464 (.node 16320415173 .nil .nil) .nil) (.node 16453775544 .nil .nil)) (.node 16468439192 (.node 16468107665 .nil .nil) (.node 16470552760 .nil .nil))) (.node 16604770488 (.node 16602588565 (.node 16588521664 (.node 16587993272 .nil .nil) .nil) (.node 16602656920 .nil .nil)) (.node 16605299136 (.node 16605298880 .nil .nil) (.node 16605364417 .nil .nil))))) (.node 17041506496 (.node 16890511808 (.node 16756293824 (.node 16605627845 (.node 16605627589 (.node 16605562308 .nil .nil) .nil) (.node 16751040624 .nil .nil)) (.node 16773071040 (.node 16756294080 .nil .nil) (.node 16890511552 .nil .nil))) (.node 16890840517 (.node 16890774980 (.node 16890577345 (.node 16890577089 .nil .nil) .nil) (.node 16890840261 .nil .nil)) (.node 17019476080 (.node 16907288768 .nil .nil) (.node 17024729280 .nil .nil)))) (.node 17176053189 (.node 17175789761 (.node 17175724224 (.node 17158947008 (.node 17041506752 .nil .nil) .nil) (.node 17175724480 .nil .nil)) (.node 17175987652 (.node 17175790017 .nil .nil) (.node 17176052933 .nil .nil))) (.node 17192501696 (.node 17190396064 (.node 17181974560 (.node 17180132356 .nil .nil) .nil) (.node 17192501440 .nil .nil)) (.node 17192567233 (.node 17192566977 .nil .nil) (.node 17192764612 .nil .nil))))))) (.node 17511268544 (.node 17374945440 (.node 17271640184 (.node 17220802672 (.node 17199278120 (.node 17192830404 (.node 17192830149 (.node 17192830148 .nil .nil) .nil) (.node 17192830405 .nil .nil)) (.node 17209278656 (.node 17207173280 (.node 17201383496 .nil .nil) .nil) (.node 17218697296 .nil .nil))) (.node 17240727712 (.node 17238085752 (.node 17226055872 (.node 17223950496 .nil .nil) .nil) (.node 17240191128 .nil .nil)) (.node 17257504928 (.node 17242833088 .nil .nil) (.node 17259610304 .nil .nil)))) (.node 17309941952 (.node 17287911536 (.node 17276387520 (.node 17274282144 (.node 17273745560 .nil .nil) .nil) (.node 17285806160 .nil .nil)) (.node 17293164736 (.node 17291059360 .nil .nil) (.node 17307836576 .nil .nil))) (.node 17352915024 (.node 17341391008 (.node 17326719168 (.node 17324613792 .nil .nil) .nil) (.node 17343496384 .nil .nil)) (.node 17358168224 (.node 17355020400 .nil .nil) (.node 17360273600 .nil .nil))))) (.node 17476135080 (.node 17427382464 (.node 17407963288 (.node 17393828032 (.node 17391722656 (.node 17377050816 .nil .nil) .nil) (.node 17405857912 .nil .nil)) (.node 17410605248 (.node 17408499872 .nil .nil) (.node 17425277088 .nil .nil))) (.node 17459357864 (.node 17448830984 (.node 17444159680 (.node 17442054304 .nil .nil) .nil) (.node 17450410016 .nil .nil)) (.node 17468503092 (.node 17460936896 .nil .nil) (.node 17469818952 .nil .nil)))) (.node 17478043076 (.node 17477977284 (.node 17477779649 (.node 17477714368 (.node 17477714112 .nil .nil) .nil) (.node 17477779905 .nil .nil)) (.node 17478042820 (.node 17477977540 .nil .nil) (.node 17478042821 .nil .nil))) (.node 17494491328 (.node 17489238128 (.node 17487659096 (.node 17478043077 .nil .nil) .nil) (.node 17492912296 .nil .nil)) (.node 17508626584 (.node 17507047552 .nil .nil) (.node 17509689512 .nil .nil)))))) (.node 17729372352 (.node 17623455856 (.node 17560021160 (.node 17543243944 (.node 17540601984 (.node 17528045760 (.node 17526466728 .nil .nil) .nil) (.node 17542181016 .nil .nil)) (.node 17554767960 (.node 17544822976 .nil .nil) (.node 17556346992 .nil .nil))) (.node 17595154624 (.node 17578377408 (.node 17576798376 (.node 17561600192 .nil .nil) .nil) (.node 17593575592 .nil .nil)) (.node 17611931840 (.node 17610352808 .nil .nil) (.node 17621876824 .nil .nil)))) (.node 17677461672 (.node 17660684456 (.node 17643907240 (.node 17628709056 (.node 17627130024 .nil .nil) .nil) (.node 17645486272 .nil .nil)) (.node 17674819712 (.node 17662263488 .nil .nil) (.node 17676398744 .nil .nil))) (.node 17712595136 (.node 17695817920 (.node 17694238888 (.node 17679040704 .nil .nil) .nil) (.node 17711016104 .nil .nil)) (.node 17718845472 (.node 17717794832 .nil .nil) (.node 17728321712 .nil .nil))))) (.node 17763255749 (.node 17762926784 (.node 17756886116 (.node 17745098928 (.node 17738254408 (.node 17737203768 .nil .nil) .nil) (.node 17746149568 .nil .nil)) (.node 17757673584 (.node 17756951652 .nil .nil) (.node 17761876144 .nil .nil))) (.node 17763190212 (.node 17762992577 (.node 17762992321 (.node 17762927040 .nil .nil) .nil) (.node 17763189956 .nil .nil)) (.node 17763255493 (.node 17763255492 .nil .nil) (.node 17763255748 .nil .nil)))) (.node 17812207792 (.node 17795430576 (.node 17778653360 (.node 17777062040 (.node 17776011400 .nil .nil) .nil) (.node 17779704000 .nil .nil)) (.node 17809565832 (.node 17796481216 .nil .nil) (.node 17810616472 .nil .nil))) (.node 17830035648 (.node 17824782448 (.node 17823731808 (.node 17813258432 .nil .nil) .nil) (.node 17828985008 .nil .nil)) (.node 17846812864 (.node 17845762224 .nil .nil) (.node 17862539440 .nil .nil))))))))) (.node 19541311680 (.node 18629560424 (.node 18232688832 (.node 18048205249 (.node 17986752536 (.node 17930698944 (.node 17896093872 (.node 17890840672 (.node 17880367296 (.node 17879316656 .nil .nil) .nil) (.node 17891891312 .nil .nil)) (.node 17913921728 (.node 17912871088 (.node 17897144512 .nil .nil) .nil) (.node 17929648304 .nil .nil))) (.node 17963202736 (.node 17946425520 (.node 17944834200 (.node 17943783560 .nil .nil) .nil) (.node 17947476160 .nil .nil)) (.node 17979979952 (.node 17964253376 .nil .nil) (.node 17981030592 .nil .nil)))) (.node 18026109040 (.node 18006689864 (.node 17997807808 (.node 17997279416 (.node 17987280928 .nil .nil) .nil) (.node 18006161472 .nil .nil)) (.node 18014585024 (.node 18014056632 .nil .nil) (.node 18025580648 .nil .nil))) (.node 18047611064 (.node 18045232276 (.node 18031362240 (.node 18030833848 .nil .nil) .nil) (.node 18045497496 .nil .nil)) (.node 18048139712 (.node 18048139456 .nil .nil) (.node 18048204993 .nil .nil))))) (.node 18115248320 (.node 18078523536 (.node 18048468420 (.node 18048468164 (.node 18048402884 (.node 18048402628 .nil .nil) .nil) (.node 18048468165 .nil .nil)) (.node 18064388280 (.node 18048468421 .nil .nil) (.node 18064916672 .nil .nil))) (.node 18093217904 (.node 18081693888 (.node 18081165496 (.node 18079051928 .nil .nil) .nil) (.node 18092689512 .nil .nil)) (.node 18098471104 (.node 18097942712 .nil .nil) (.node 18114719928 .nil .nil)))) (.node 18181828792 (.node 18159798376 (.node 18148274360 (.node 18132025536 (.node 18131497144 .nil .nil) .nil) (.node 18148802752 .nil .nil)) (.node 18165051576 (.node 18160326768 .nil .nil) (.node 18165579968 .nil .nil))) (.node 18213269656 (.node 18199134400 (.node 18198606008 (.node 18182357184 .nil .nil) .nil) (.node 18212741264 .nil .nil)) (.node 18215911616 (.node 18215383224 .nil .nil) (.node 18232160440 .nil .nil)))))) (.node 18523623448 (.node 18333680837 (.node 18313932952 (.node 18275125320 (.node 18255716384 (.node 18249466048 (.node 18248937656 .nil .nil) .nil) (.node 18266243264 .nil .nil)) (.node 18294544496 (.node 18283020480 .nil .nil) (.node 18299797696 .nil .nil))) (.node 18333417921 (.node 18333352384 (.node 18333352128 (.node 18316574912 .nil .nil) .nil) (.node 18333417665 .nil .nil)) (.node 18333615556 (.node 18333615300 .nil .nil) (.node 18333680836 .nil .nil)))) (.node 18417238208 (.node 18361653360 (.node 18347487384 (.node 18333681093 (.node 18333681092 .nil .nil) .nil) (.node 18350129344 .nil .nil)) (.node 18383683776 (.node 18366906560 .nil .nil) (.node 18400460992 .nil .nil))) (.node 18481705112 (.node 18450792640 (.node 18434015424 (.node 18428762224 .nil .nil) .nil) (.node 18467569856 .nil .nil)) (.node 18501124288 (.node 18484347072 .nil .nil) (.node 18517901504 .nil .nil))))) (.node 18615394448 (.node 18562979952 (.node 18543560776 (.node 18534678720 (.node 18534150328 (.node 18524151840 .nil .nil) .nil) (.node 18543032384 .nil .nil)) (.node 18551455936 (.node 18550927544 .nil .nil) (.node 18562451560 .nil .nil))) (.node 18584481976 (.node 18581840016 (.node 18568233152 (.node 18567704760 .nil .nil) .nil) (.node 18582368408 .nil .nil)) (.node 18601259192 (.node 18585010368 .nil .nil) (.node 18601787584 .nil .nil)))) (.node 18618565056 (.node 18615723413 (.node 18615723156 (.node 18615657620 (.node 18615460241 .nil .nil) .nil) (.node 18615723412 .nil .nil)) (.node 18618036408 (.node 18615922840 .nil .nil) (.node 18618564800 .nil .nil))) (.node 18618893508 (.node 18618827972 (.node 18618630593 (.node 18618630337 .nil .nil) .nil) (.node 18618828228 .nil .nil)) (.node 18618893764 (.node 18618893509 .nil .nil) (.node 18618893765 .nil .nil))))))) (.node 18987663552 (.node 18836668608 (.node 18750140568 (.node 18696669288 (.node 18652119232 (.node 18635342016 (.node 18634813624 (.node 18630088816 .nil .nil) .nil) (.node 18651590840 .nil .nil)) (.node 18685145272 (.node 18668896448 (.node 18668368056 .nil .nil) .nil) (.node 18685673664 .nil .nil))) (.node 18719228096 (.node 18702450880 (.node 18701922488 (.node 18697197680 .nil .nil) .nil) (.node 18718699704 .nil .nil)) (.node 18736005312 (.node 18735476920 .nil .nil) (.node 18749612176 .nil .nil)))) (.node 18802063536 (.node 18785808568 (.node 18769031352 (.node 18752782528 (.node 18752254136 .nil .nil) .nil) (.node 18769559744 .nil .nil)) (.node 18791536656 (.node 18786336960 .nil .nil) (.node 18792587296 .nil .nil))) (.node 18819891392 (.node 18811996232 (.node 18810945592 (.node 18803114176 .nil .nil) .nil) (.node 18818840752 .nil .nil)) (.node 18831415408 (.node 18830364768 .nil .nil) (.node 18835617968 .nil .nil))))) (.node 18903843265 (.node 18885949616 (.node 18869172400 (.node 18852395184 (.node 18850803864 (.node 18849753224 .nil .nil) .nil) (.node 18853445824 .nil .nil)) (.node 18883307656 (.node 18870223040 .nil .nil) (.node 18884358296 .nil .nil))) (.node 18902726832 (.node 18897802596 (.node 18897736804 (.node 18887000256 .nil .nil) .nil) (.node 18898524272 .nil .nil)) (.node 18903777728 (.node 18903777472 .nil .nil) (.node 18903843009 .nil .nil)))) (.node 18936281264 (.node 18904106436 (.node 18904106180 (.node 18904040900 (.node 18904040644 .nil .nil) .nil) (.node 18904106181 .nil .nil)) (.node 18919504048 (.node 18904106437 .nil .nil) (.node 18920554688 .nil .nil))) (.node 18965633136 (.node 18954109120 (.node 18953058480 (.node 18937331904 .nil .nil) .nil) (.node 18964582496 .nil .nil)) (.node 18970886336 (.node 18969835696 .nil .nil) (.node 18986612912 .nil .nil)))))) (.node 19234068592 (.node 19121881280 (.node 19053721776 (.node 19020167344 (.node 19017525384 (.node 19004440768 (.node 19003390128 .nil .nil) .nil) (.node 19018576024 .nil .nil)) (.node 19036944560 (.node 19021217984 .nil .nil) (.node 19037995200 .nil .nil))) (.node 19088326848 (.node 19071549632 (.node 19061022752 (.node 19054772416 .nil .nil) .nil) (.node 19080431688 .nil .nil)) (.node 19105104064 (.node 19099850864 .nil .nil) (.node 19119239320 .nil .nil)))) (.node 19189055937 (.node 19172212928 (.node 19155435712 (.node 19152793752 (.node 19138658496 .nil .nil) .nil) (.node 19166959728 .nil .nil)) (.node 19188990400 (.node 19188990144 .nil .nil) (.node 19189055681 .nil .nil))) (.node 19189319108 (.node 19189318852 (.node 19189253572 (.node 19189253316 .nil .nil) .nil) (.node 19189318853 .nil .nil)) (.node 19205767360 (.node 19189319109 .nil .nil) (.node 19222544576 .nil .nil))))) (.node 19423871168 (.node 19339985088 (.node 19289653440 (.node 19272876224 (.node 19256099008 (.node 19239321792 .nil .nil) .nil) (.node 19287011480 .nil .nil)) (.node 19323207872 (.node 19306430656 .nil .nil) (.node 19329458208 .nil .nil))) (.node 19387674776 (.node 19368286320 (.node 19356762304 (.node 19348867144 .nil .nil) .nil) (.node 19373539520 .nil .nil)) (.node 19407093952 (.node 19390316736 .nil .nil) (.node 19421229208 .nil .nil)))) (.node 19474466244 (.node 19474203072 (.node 19457425600 (.node 19440648384 (.node 19435395184 .nil .nil) .nil) (.node 19474202816 .nil .nil)) (.node 19474268609 (.node 19474268353 .nil .nil) (.node 19474465988 .nil .nil))) (.node 19490980032 (.node 19474531780 (.node 19474531525 (.node 19474531524 .nil .nil) .nil) (.node 19474531781 .nil .nil)) (.node 19507757248 (.node 19502504048 .nil .nil) (.node 19524534464 .nil .nil)))))))) (.node 20514390208 (.node 20038653028 (.node 19860078784 (.node 19742638272 (.node 19641974976 (.node 19597893664 (.node 19574866112 (.node 19558088896 (.node 19555446936 .nil .nil) .nil) (.node 19591643328 .nil .nil)) (.node 19625197760 (.node 19617302600 (.node 19608420544 .nil .nil) .nil) (.node 19636721776 .nil .nil))) (.node 19692306624 (.node 19675529408 (.node 19658752192 (.node 19656110232 .nil .nil) .nil) (.node 19689664664 .nil .nil)) (.node 19709083840 (.node 19703830640 .nil .nil) (.node 19725861056 .nil .nil)))) (.node 19759744452 (.node 19759678660 (.node 19759481025 (.node 19759415744 (.node 19759415488 .nil .nil) .nil) (.node 19759481281 .nil .nil)) (.node 19759744196 (.node 19759678916 .nil .nil) (.node 19759744197 .nil .nil))) (.node 19809747136 (.node 19776192704 (.node 19770939504 (.node 19759744453 .nil .nil) .nil) (.node 19792969920 .nil .nil)) (.node 19826524352 (.node 19823882392 .nil .nil) (.node 19843301568 .nil .nil))))) (.node 19943964864 (.node 19904106592 (.node 19884687416 (.node 19875805360 (.node 19866329120 (.node 19865278480 .nil .nil) .nil) (.node 19876856000 .nil .nil)) (.node 19892582576 (.node 19885738056 .nil .nil) (.node 19893633216 .nil .nil))) (.node 19924545688 (.node 19910410432 (.node 19909359792 (.node 19905157232 .nil .nil) .nil) (.node 19923495048 .nil .nil)) (.node 19927187648 (.node 19926137008 .nil .nil) (.node 19942914224 .nil .nil)))) (.node 19993245872 (.node 19971215456 (.node 19959691440 (.node 19958100120 (.node 19957049480 .nil .nil) .nil) (.node 19960742080 .nil .nil)) (.node 19976468656 (.node 19972266096 .nil .nil) (.node 19977519296 .nil .nil))) (.node 20027850944 (.node 20011073728 (.node 20010023088 (.node 19994296512 .nil .nil) .nil) (.node 20026800304 .nil .nil)) (.node 20038390113 (.node 20038324320 .nil .nil) (.node 20038587492 .nil .nil)))))) (.node 20226535576 (.node 20078182592 (.node 20044891332 (.node 20044628160 (.node 20039374960 (.node 20038653285 (.node 20038653284 .nil .nil) .nil) (.node 20043577520 .nil .nil)) (.node 20044693697 (.node 20044628416 .nil .nil) (.node 20044693953 .nil .nil))) (.node 20044957125 (.node 20044956869 (.node 20044956868 (.node 20044891588 .nil .nil) .nil) (.node 20044957124 .nil .nil)) (.node 20061405376 (.node 20060354736 .nil .nil) (.node 20077131952 .nil .nil)))) (.node 20134764576 (.node 20110686384 (.node 20093909168 (.node 20092317848 (.node 20091267208 .nil .nil) .nil) (.node 20094959808 .nil .nil)) (.node 20127463600 (.node 20111737024 .nil .nil) (.node 20128514240 .nil .nil))) (.node 20178845888 (.node 20162068672 (.node 20154173512 (.node 20145291456 .nil .nil) .nil) (.node 20173592688 .nil .nil)) (.node 20195623104 (.node 20192981144 .nil .nil) (.node 20212400320 .nil .nil))))) (.node 20330169797 (.node 20329840832 (.node 20279509184 (.node 20245954752 (.node 20240701552 (.node 20229177536 .nil .nil) .nil) (.node 20262731968 .nil .nil)) (.node 20307810416 (.node 20296286400 .nil .nil) (.node 20313063616 .nil .nil))) (.node 20330104260 (.node 20329906625 (.node 20329906369 (.node 20329841088 .nil .nil) .nil) (.node 20330104004 .nil .nil)) (.node 20330169541 (.node 20330169540 .nil .nil) (.node 20330169796 .nil .nil)))) (.node 20430504128 (.node 20396949696 (.node 20363395264 (.node 20360753304 (.node 20346618048 .nil .nil) .nil) (.node 20380172480 .nil .nil)) (.node 20413726912 (.node 20403200032 .nil .nil) (.node 20422608968 .nil .nil))) (.node 20480835776 (.node 20461416600 (.node 20447281344 (.node 20442028144 .nil .nil) .nil) (.node 20464058560 .nil .nil)) (.node 20497612992 (.node 20494971032 .nil .nil) (.node 20509137008 .nil .nil))))))) (.node 20900595140 (.node 20748742840 (.node 20648607936 (.node 20615119297 (.node 20581499072 (.node 20564721856 (.node 20547944640 (.node 20531167424 .nil .nil) .nil) (.node 20576245872 .nil .nil)) (.node 20615053760 (.node 20615053504 (.node 20598276288 .nil .nil) .nil) (.node 20615119041 .nil .nil))) (.node 20615382468 (.node 20615382212 (.node 20615316932 (.node 20615316676 .nil .nil) .nil) (.node 20615382213 .nil .nil)) (.node 20629188760 (.node 20615382469 .nil .nil) (.node 20631830720 .nil .nil)))) (.node 20698939584 (.node 20682162368 (.node 20671635488 (.node 20671107096 (.node 20665385152 .nil .nil) .nil) (.node 20681633976 .nil .nil)) (.node 20691044424 (.node 20690516032 .nil .nil) (.node 20698411192 .nil .nil))) (.node 20729323664 (.node 20715188408 (.node 20710463600 (.node 20709935208 .nil .nil) .nil) (.node 20715716800 .nil .nil)) (.node 20731965624 (.node 20729852056 .nil .nil) (.node 20732494016 .nil .nil))))) (.node 20849406136 (.node 20782825664 (.node 20766048448 (.node 20763406488 (.node 20762878096 (.node 20749271232 .nil .nil) .nil) (.node 20765520056 .nil .nil)) (.node 20777572464 (.node 20777044072 .nil .nil) (.node 20782297272 .nil .nil))) (.node 20832628920 (.node 20815851704 (.node 20799602880 (.node 20799074488 .nil .nil) .nil) (.node 20816380096 .nil .nil)) (.node 20844152936 (.node 20833157312 .nil .nil) (.node 20844681328 .nil .nil)))) (.node 20899737784 (.node 20883488960 (.node 20866711744 (.node 20866183352 (.node 20849934528 .nil .nil) .nil) (.node 20882960568 .nil .nil)) (.node 20897424788 (.node 20897358996 .nil .nil) (.node 20897624216 .nil .nil))) (.node 20900529348 (.node 20900331713 (.node 20900266432 (.node 20900266176 .nil .nil) .nil) (.node 20900331969 .nil .nil)) (.node 20900594884 (.node 20900529604 .nil .nil) (.node 20900594885 .nil .nil)))))) (.node 21185807812 (.node 21051261120 (.node 20967375040 (.node 20933820608 (.node 20917043392 (.node 20916515000 (.node 20900595141 .nil .nil) .nil) (.node 20933292216 .nil .nil)) (.node 20950597824 (.node 20940070944 .nil .nil) (.node 20959479880 .nil .nil))) (.node 21017706688 (.node 20998287512 (.node 20984152256 (.node 20978899056 .nil .nil) .nil) (.node 21000929472 .nil .nil)) (.node 21034483904 (.node 21031841944 .nil .nil) (.node 21046007920 .nil .nil)))) (.node 21168701632 (.node 21118369984 (.node 21101592768 (.node 21084815552 (.node 21068038336 .nil .nil) .nil) (.node 21113116784 .nil .nil)) (.node 21151924416 (.node 21135147200 .nil .nil) (.node 21166059672 .nil .nil))) (.node 21185742020 (.node 21185544385 (.node 21185479104 (.node 21185478848 .nil .nil) .nil) (.node 21185544641 .nil .nil)) (.node 21185807556 (.node 21185742276 .nil .nil) (.node 21185807557 .nil .nil))))) (.node 21370028224 (.node 21266722968 (.node 21227915336 (.node 21208506400 (.node 21202256064 (.node 21185807813 .nil .nil) .nil) (.node 21219033280 .nil .nil)) (.node 21247334512 (.node 21235810496 .nil .nil) (.node 21252587712 .nil .nil))) (.node 21314443376 (.node 21300277400 (.node 21286142144 (.node 21269364928 .nil .nil) .nil) (.node 21302919360 .nil .nil)) (.node 21336473792 (.node 21319696576 .nil .nil) (.node 21353251008 .nil .nil)))) (.node 21470691776 (.node 21434495128 (.node 21403582656 (.node 21386805440 (.node 21381552240 .nil .nil) .nil) (.node 21420359872 .nil .nil)) (.node 21453914304 (.node 21437137088 .nil .nil) (.node 21470691520 .nil .nil))) (.node 21471020228 (.node 21470954692 (.node 21470757313 (.node 21470757057 .nil .nil) .nil) (.node 21470954948 .nil .nil)) (.node 21471020484 (.node 21471020229 .nil .nil) (.node 21471020485 .nil .nil)))))))))))

theorem checked : certificate pool = true := by decide +kernel

def preservesTwo (s : Nat) : Bool :=
  if s >>> 32 == 0 then true else
  match flush 5 s with
  | none => true
  | some e => !accept e 0 || accept e 2

theorem preservesTwo_pool : allNodes pool preservesTwo = true := by decide +kernel


end Rule30Submission

/-!
# Stripe relations and first meetings of finite Rule 30 rows

In the moving integer frame Phi(a)=a XOR((a<<1) OR(a<<2)), the center is
bit c+t at time t. Two rows are stripe-related if they are equal or share a
cut j<=c, both lower prefixes lie in 0*(1|11)(01)*, bit j+1 is white in both,
and all higher bits agree.

Stripe-related rows have identical entire center traces: the relation is
preserved after two steps, and the first two center observations agree.
Conversely, if rows become stripe-related at any finite time while all
preceding center observations agree, they were related at time zero or one.
All row sizes, center indices and finite times are quantified without bounds.

The proof connects finite certificates to arbitrary input lengths, exact
integer bit updates, typed packing, common-cut parser semantics and the
stripe grammar. It does not prove completeness for equal infinite traces,
numerical-normalizer equivalence, EdgeObservable, or a prize problem.
The component module names in some proof comments refer to the accompanying
research sources, from which these proof bodies are combined unchanged.
-/



namespace Rule30Submission

theorem all_of_member {p : StateTree} {f : Nat → Bool}
    (ha : allNodes p f = true) {s : Nat} (hm : member p s = true) : f s = true := by
  induction p generalizing s with
  | nil => simp [member] at hm
  | node k l r ihl ihr =>
      have hk := (Bool.and_eq_true_iff.mp ha).1
      have hc := (Bool.and_eq_true_iff.mp ha).2
      by_cases he : s = k
      · simpa only [he] using hk
      · by_cases hl : s < k
        · apply ihl (Bool.and_eq_true_iff.mp hc).1
          simpa [member, he, hl] using hm
        · apply ihr (Bool.and_eq_true_iff.mp hc).2
          simpa [member, he, hl] using hm

theorem initial_member : member pool initial = true := (Bool.and_eq_true_iff.mp checked).1

theorem good_of_member {s : Nat} (hs : member pool s = true) : endGood s = true := by
  have all := (Bool.and_eq_true_iff.mp checked).2
  exact (Bool.and_eq_true_iff.mp (all_of_member all hs)).2

theorem step_member {s v e : Nat} (hs : member pool s = true) (hv : v < 8)
    (he : step s v = some e) : member pool e = true := by
  have all := (Bool.and_eq_true_iff.mp checked).2
  have hc := (Bool.and_eq_true_iff.mp (all_of_member all hs)).1
  have h := List.all_eq_true.mp hc v (List.mem_range.mpr hv)
  rw [he] at h
  exact h

def run (s : Nat) : List Nat → Option Nat
  | [] => some s
  | v :: vs => (step s v).bind (fun e => run e vs)

theorem run_member {word : List Nat} {s e : Nat} (hs : member pool s = true)
    (hv : ∀ v, v ∈ word → v < 8) (hr : run s word = some e) : member pool e = true := by
  induction word generalizing s with
  | nil =>
      simp only [run, Option.some.injEq] at hr
      subst hr
      exact hs
  | cons v vs ih =>
      cases hstep : step s v with
      | none => simp [run, hstep] at hr
      | some next =>
          have hnext := step_member hs (hv v (by simp)) hstep
          apply ih hnext
          · intro u hu
            exact hv u (by simp [hu])
          · simpa only [run, hstep, Option.bind_some] using hr

/-- Every length of valid input stays outside the machine's forbidden end set.
The numerical-normalization interpretation is a separate obligation. -/
theorem all_input_lengths_safe (word : List Nat)
    (hv : ∀ v, v ∈ word → v < 8) {e : Nat} (hr : run initial word = some e) :
    endGood e = true :=
  good_of_member (run_member initial_member hv hr)

def Phi (a : Nat) : Nat := a ^^^ ((a <<< 1) ||| (a <<< 2))

def before (a i k : Nat) : Bool := decide (k < i) && a.testBit (i - (k+1))

theorem Phi_testBit (a i : Nat) :
    (Phi a).testBit i = xor (a.testBit i) (before a i 0 || before a i 1) := by
  have h1 : decide (1 ≤ i) = decide (0 < i) := by
    by_cases h : 1 ≤ i
    · have h' : 0 < i := by omega
      simp [h, h']
    · have h' : ¬ 0 < i := by omega
      simp [h, h']
  have h2 : decide (2 ≤ i) = decide (1 < i) := by
    by_cases h : 2 ≤ i
    · have h' : 1 < i := by omega
      simp [h, h']
    · have h' : ¬ 1 < i := by omega
      simp [h, h']
  simp only [Phi, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft, before,
    h1, h2, Nat.zero_add]

def pack4 (b0 b1 b2 b3 : Bool) : Nat :=
  b0.toNat ||| (b1.toNat <<< 1) ||| (b2.toNat <<< 2) ||| (b3.toNat <<< 3)

theorem pack4_bit0 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 0 = b0 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_bit1 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 1 = b1 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_bit2 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 2 = b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_bit3 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 3 = b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_lt (b0 b1 b2 b3 : Bool) : pack4 b0 b1 b2 b3 < 16 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_shift (b0 b1 b2 b3 x : Bool) :
    pack4 x b0 b1 b2 = (2 * pack4 b0 b1 b2 b3 + x.toNat) % 16 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases x <;> decide

def history (a i : Nat) : Nat := pack4 (before a i 0) (before a i 1)
  (before a i 2) (before a i 3)

theorem history_lt (a i : Nat) : history a i < 16 := pack4_lt _ _ _ _

theorem history_bit0 (a i : Nat) : (history a i).testBit 0 = before a i 0 := pack4_bit0 _ _ _ _
theorem history_bit1 (a i : Nat) : (history a i).testBit 1 = before a i 1 := pack4_bit1 _ _ _ _
theorem history_bit2 (a i : Nat) : (history a i).testBit 2 = before a i 2 := pack4_bit2 _ _ _ _
theorem history_bit3 (a i : Nat) : (history a i).testBit 3 = before a i 3 := pack4_bit3 _ _ _ _

theorem before_succ_zero (a i : Nat) : before a (i+1) 0 = a.testBit i := by
  simp [before]

theorem before_succ_succ (a i k : Nat) : before a (i+1) (k+1) = before a i k := by
  by_cases h : k < i
  · have h' : k+1 < i+1 := by omega
    have hi : (i+1)-(k+1+1) = i-(k+1) := by omega
    simp [before, h, h', hi]
  · have h' : ¬ k+1 < i+1 := by omega
    simp [before, h, h']

theorem history_zero (a : Nat) : history a 0 = 0 := by simp [history, before, pack4]

theorem history_succ (a i : Nat) :
    history a (i+1) = (2 * history a i + (a.testBit i).toNat) % 16 := by
  unfold history
  rw [before_succ_zero, before_succ_succ a i 0, before_succ_succ a i 1,
    before_succ_succ a i 2]
  exact pack4_shift _ _ _ _ _

theorem before_of_lt (a i k : Nat) (hk : k < i) :
    before a i k = a.testBit (i-(k+1)) := by simp [before, hk]

theorem before_shift (a i k l : Nat) (hk : k < i) :
    before a (i-(k+1)) l = before a i (k+l+1) := by
  by_cases hl : l < i-(k+1)
  · have hr : k+l+1 < i := by omega
    simp only [before, hl, hr, decide_true, Bool.true_and]
    congr 1
    omega
  · have hr : ¬ k+l+1 < i := by omega
    simp [before, hl, hr]

theorem before_Phi (a i k : Nat) :
    before (Phi a) i k = xor (before a i k)
      (before a i (k+1) || before a i (k+2)) := by
  by_cases hk : k < i
  · rw [before_of_lt _ _ _ hk, Phi_testBit,
      before_shift a i k 0 hk, before_shift a i k 1 hk, before_of_lt a i k hk]
  · have h1 : ¬ k+1 < i := by omega
    have h2 : ¬ k+2 < i := by omega
    simp [before, hk, h1, h2]

theorem first_exact (a i : Nat) :
    (Phi a).testBit i = first (history a i) (a.testBit i) := by
  rw [Phi_testBit]
  simp only [first, history_bit0, history_bit1]

theorem second_exact (a i : Nat) :
    (Phi (Phi a)).testBit i = second (history a i) (a.testBit i) := by
  rw [Phi_testBit, first_exact, before_Phi, before_Phi]
  simp only [second, first, history_bit0, history_bit1, history_bit2, history_bit3,
    Nat.zero_add]

structure View where
  e0 : Nat
  e1 : Nat
  e2 : Nat
  ha : Nat
  hb : Nat
  code : Nat

def View.Valid (v : View) : Prop := v.e0 < 200 ∧ v.e1 < 200 ∧ v.e2 < 200 ∧
  v.ha < 16 ∧ v.hb < 16 ∧ v.code ≤ 4

def View.encode (v : View) : Nat := v.e0 + (v.e1 <<< 8) + (v.e2 <<< 16) +
  (v.ha <<< 24) + (v.hb <<< 28) + (v.code <<< 32)

theorem View.decode_encode (v : View) (h : v.Valid) :
    v.encode % 256 = v.e0 ∧ (v.encode >>> 8) % 256 = v.e1 ∧
    (v.encode >>> 16) % 256 = v.e2 ∧ (v.encode >>> 24) % 16 = v.ha ∧
    (v.encode >>> 28) % 16 = v.hb ∧ v.encode >>> 32 = v.code := by
  obtain ⟨h0,h1,h2,ha,hb,hc⟩ := h
  unfold View.encode
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  repeat' constructor <;> omega

def symbol (a b marker : Bool) : Nat := a.toNat + 2 * b.toNat + 4 * marker.toNat

theorem symbol_lt (a b marker : Bool) : symbol a b marker < 8 := by
  cases a <;> cases b <;> cases marker <;> decide

theorem symbol_bits (a b marker : Bool) :
    (symbol a b marker).testBit 0 = a ∧ (symbol a b marker).testBit 1 = b ∧
    (symbol a b marker).testBit 2 = marker := by
  cases a <;> cases b <;> cases marker <;> decide

theorem tailNext_lt (s : Nat) (b : Bool) : tailNext s b < 5 := by
  unfold tailNext
  split <;> decide

theorem bool_nat_le (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem relStep_lt (e : Nat) (a b allow : Bool) : relStep e a b allow < 200 := by
  let ta := tailNext ((e / 8) / 5) a
  let tb := tailNext ((e / 8) % 5) b
  let valid := (e.testBit 0 && (a == b)) || (e.testBit 1 && !a && !b)
  let pending := allow && a && b && (ta == 1 || ta == 3) && (tb == 1 || tb == 3)
  let ident := e.testBit 2 && (a == b)
  change 8 * (5 * ta + tb) + 4 * ident.toNat + 2 * pending.toNat + valid.toNat < 200
  have ht : ta < 5 := tailNext_lt _ _
  have hu : tb < 5 := tailNext_lt _ _
  have hi := bool_nat_le ident
  have hp := bool_nat_le pending
  have hv := bool_nat_le valid
  omega

def nextCode (old : Nat) (marker : Bool) : Nat :=
  if marker then 1 else if old == 0 then 0 else min 4 (old+1)

theorem nextCode_le (old : Nat) (marker : Bool) : nextCode old marker ≤ 4 := by
  unfold nextCode
  split
  · decide
  · split
    · decide
    · exact Nat.min_le_left _ _

def View.advance (v : View) (a b marker : Bool) : Option View :=
  if marker && v.code != 0 then none else
  let code := nextCode v.code marker
  let a1 := first v.ha a
  let b1 := first v.hb b
  if (code == 1 && a != b) || (code == 2 && a1 != b1) then none else
  some ⟨relStep v.e0 a b (code == 0 || code ≤ 1),
    relStep v.e1 a1 b1 (code == 0 || code ≤ 2),
    relStep v.e2 (second v.ha a) (second v.hb b) (code == 0 || code ≤ 3),
    (2 * v.ha + a.toNat) % 16, (2 * v.hb + b.toNat) % 16, code⟩

theorem View.encode_advance (v : View) (hv : v.Valid) (a b marker : Bool) :
    step v.encode (symbol a b marker) = (v.advance a b marker).map View.encode := by
  obtain ⟨h0,h1,h2,ha,hb,hc⟩ := v.decode_encode hv
  obtain ⟨s0,s1,s2⟩ := symbol_bits a b marker
  have hcode : (if marker then 1 else if v.code == 0 then 0 else min 4 (v.code+1)) =
      nextCode v.code marker := rfl
  simp only [step, View.advance, h0,h1,h2,ha,hb,hc,s0,s1,s2,hcode]
  split
  · rfl
  · split <;> rfl

theorem View.advance_valid {v w : View} {a b marker : Bool}
    (h : v.advance a b marker = some w) : w.Valid := by
  unfold View.advance at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · have he := Option.some.inj h
      subst w
      exact ⟨relStep_lt _ _ _ _, relStep_lt _ _ _ _, relStep_lt _ _ _ _,
        Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), nextCode_le _ _⟩

structure Letter where
  a : Bool
  b : Bool
  marker : Bool

def Letter.val (x : Letter) : Nat := symbol x.a x.b x.marker

def View.run (v : View) : List Letter → Option View
  | [] => some v
  | x :: xs => (v.advance x.a x.b x.marker).bind (fun w => w.run xs)

theorem View.run_encode (v : View) (hv : v.Valid) (xs : List Letter) :
    Rule30Submission.run v.encode (xs.map Letter.val) = (v.run xs).map View.encode := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, Rule30Submission.run, View.run, Letter.val]
      rw [v.encode_advance hv]
      cases h : v.advance x.a x.b x.marker with
      | none => simp only [Option.map_none, Option.bind_none]
      | some w =>
          simp only [Option.map_some, Option.bind_some]
          exact ih w (View.advance_valid h)

def initialView : View := ⟨4,4,4,0,0,0⟩

theorem initialView_valid : initialView.Valid := by unfold View.Valid initialView; decide
theorem initialView_encode : initialView.encode = initial := by decide

theorem safe_after_input (xs : List Letter) {v : View} (h : initialView.run xs = some v) :
    endGood v.encode = true := by
  have hr : Rule30Submission.run initial (xs.map Letter.val) = some v.encode := by
    rw [← initialView_encode, initialView.run_encode initialView_valid, h]
    rfl
  apply all_input_lengths_safe (xs.map Letter.val) _ hr
  intro u hu
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hu
  exact symbol_lt x.a x.b x.marker

def centerCode (c n : Nat) : Nat := if n ≤ c then 0 else min 4 (n-c)

theorem centerCode_zero (c : Nat) : centerCode c 0 = 0 := by simp [centerCode]

theorem centerCode_succ (c n : Nat) :
    nextCode (centerCode c n) (decide (n = c)) = centerCode c (n+1) := by
  by_cases he : n = c
  · subst n
    simp [nextCode, centerCode]
  · by_cases hl : n < c
    · have hn : n ≤ c := by omega
      have hs : n+1 ≤ c := by omega
      simp [nextCode, centerCode, he, hn, hs]
    · have hn : ¬ n ≤ c := by omega
      have hs : ¬ n+1 ≤ c := by omega
      have hp : 0 < min 4 (n-c) := by omega
      simp only [nextCode, he, decide_false, Bool.false_eq_true, ↓reduceIte,
        centerCode, hn, hs]
      have hz : (min 4 (n-c) == 0) = false := by simp; omega
      rw [hz]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

theorem centerCode_marker (c n : Nat) :
    (decide (n = c) && centerCode c n != 0) = false := by
  by_cases he : n = c
  · subst n; simp [centerCode]
  · simp [he]

theorem centerCode_one (c n : Nat) : centerCode c (n+1) = 1 ↔ n = c := by
  unfold centerCode
  split <;> omega

theorem centerCode_two (c n : Nat) : centerCode c (n+1) = 2 ↔ n = c+1 := by
  unfold centerCode
  split <;> omega

theorem centerCode_allow (c n t : Nat) (ht : t < 3) :
    (centerCode c (n+1) == 0 || centerCode c (n+1) ≤ t+1) = decide (n ≤ c+t) := by
  unfold centerCode
  split
  · simp only [Nat.reduceBEq, Bool.true_or]
    have h : n ≤ c+t := by omega
    simp [h]
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    omega

def relationRun (a b c : Nat) : Nat → Nat
  | 0 => 4
  | n+1 => relStep (relationRun a b c n) (a.testBit n) (b.testBit n) (decide (n ≤ c))

def actualView (a b c n : Nat) : View :=
  ⟨relationRun a b c n, relationRun (Phi a) (Phi b) (c+1) n,
    relationRun (Phi (Phi a)) (Phi (Phi b)) (c+2) n,
    history a n, history b n, centerCode c n⟩

def actualLetter (a b c n : Nat) : Letter :=
  ⟨a.testBit n, b.testBit n, decide (n = c)⟩

theorem actualView_zero (a b c : Nat) : actualView a b c 0 = initialView := by
  simp [actualView, relationRun, history_zero, centerCode_zero, initialView]

theorem actualView_advance (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    (actualView a b c n).advance (a.testBit n) (b.testBit n) (decide (n = c)) =
      some (actualView a b c (n+1)) := by
  have g0 : (centerCode c (n+1) == 1 && a.testBit n != b.testBit n) = false := by
    by_cases hc : centerCode c (n+1) = 1
    · have hn := (centerCode_one c n).mp hc
      subst n
      simp [h0]
    · simp [hc]
  have g1 : (centerCode c (n+1) == 2 &&
      (Phi a).testBit n != (Phi b).testBit n) = false := by
    by_cases hc : centerCode c (n+1) = 2
    · have hn := (centerCode_two c n).mp hc
      subst n
      simp [h1]
    · simp [hc]
  simp only [View.advance, actualView, centerCode_marker, Bool.false_eq_true,
    ↓reduceIte, centerCode_succ, ← first_exact, g0, g1, Bool.false_or,
    ← second_exact, centerCode_allow c n 0 (by decide),
    centerCode_allow c n 1 (by decide), centerCode_allow c n 2 (by decide),
    Nat.add_zero, history_succ, relationRun]

def actualInput (a b c : Nat) (n : Nat) : List Letter :=
  (List.range n).map (actualLetter a b c)

theorem View.run_append (v : View) (xs ys : List Letter) :
    v.run (xs ++ ys) = (v.run xs).bind (fun w => w.run ys) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, View.run]
      cases h : v.advance x.a x.b x.marker with
      | none => rfl
      | some w => simpa only [Option.bind_some] using ih w

theorem actualInput_run (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    initialView.run (actualInput a b c n) = some (actualView a b c n) := by
  induction n with
  | zero => simp [actualInput, View.run, actualView_zero]
  | succ n ih =>
      simp only [actualInput, List.range_succ, List.map_append, List.map_singleton,
        View.run_append] at *
      rw [ih]
      simp only [Option.bind_some, View.run, actualLetter]
      rw [actualView_advance a b c n h0 h1]
      rfl

/-- The checked end condition applies to actual rows of every integer size,
provided the two relevant center observations agree. This does not yet state
the corresponding normalization implication. -/
theorem actual_input_safe (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    endGood (actualView a b c n).encode = true :=
  safe_after_input _ (actualInput_run a b c n h0 h1)

def relCode (ta tb : Nat) (ident pending valid : Bool) : Nat :=
  8 * (5 * ta + tb) + 4 * ident.toNat + 2 * pending.toNat + valid.toNat

theorem relCode_decode (ta tb : Nat) (ht : tb < 5) (ident pending valid : Bool) :
    (relCode ta tb ident pending valid / 8) / 5 = ta ∧
    (relCode ta tb ident pending valid / 8) % 5 = tb ∧
    (relCode ta tb ident pending valid).testBit 0 = valid ∧
    (relCode ta tb ident pending valid).testBit 1 = pending ∧
    (relCode ta tb ident pending valid).testBit 2 = ident := by
  cases ident <;> cases pending <;> cases valid <;>
    simp [relCode, Nat.testBit_eq_decide_div_mod_eq] <;> omega

def tailRun (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => tailNext (tailRun a n) (a.testBit n)

theorem tailRun_lt (a n : Nat) : tailRun a n < 5 := by
  cases n with
  | zero => simp [tailRun]
  | succ n => exact tailNext_lt _ _

def identAt (a b : Nat) : Nat → Bool
  | 0 => true
  | n+1 => identAt a b n && (a.testBit n == b.testBit n)

def pendingAt (a b c : Nat) : Nat → Bool
  | 0 => false
  | n+1 => decide (n ≤ c) && a.testBit n && b.testBit n &&
      (tailRun a (n+1) == 1 || tailRun a (n+1) == 3) &&
      (tailRun b (n+1) == 1 || tailRun b (n+1) == 3)

def validAt (a b c : Nat) : Nat → Bool
  | 0 => false
  | n+1 => (validAt a b c n && (a.testBit n == b.testBit n)) ||
      (pendingAt a b c n && !a.testBit n && !b.testBit n)

theorem relationRun_code (a b c n : Nat) :
    relationRun a b c n = relCode (tailRun a n) (tailRun b n)
      (identAt a b n) (pendingAt a b c n) (validAt a b c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      obtain ⟨hta,htb,hv,hp,hi⟩ := relCode_decode (tailRun a n) (tailRun b n)
        (tailRun_lt b n) (identAt a b n) (pendingAt a b c n) (validAt a b c n)
      rw [relationRun, ih]
      simp only [relStep, hta, htb, hv, hp, hi]
      rfl

def PrefixEq (a b n : Nat) : Prop := ∀ i, i < n → a.testBit i = b.testBit i

theorem identAt_iff (a b n : Nat) : identAt a b n = true ↔ PrefixEq a b n := by
  induction n with
  | zero => simp [identAt, PrefixEq]
  | succ n ih =>
      simp only [identAt, Bool.and_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ⟨h,he⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · have hn : i = n := by omega
          simpa [hn] using he
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

def EligibleCut (a b c j : Nat) : Prop :=
  j ≤ c ∧ a.testBit j = true ∧ b.testBit j = true ∧
    (tailRun a (j+1) = 1 ∨ tailRun a (j+1) = 3) ∧
    (tailRun b (j+1) = 1 ∨ tailRun b (j+1) = 3)

theorem pendingAt_iff (a b c n : Nat) : pendingAt a b c n = true ↔
    ∃ j, n = j+1 ∧ EligibleCut a b c j := by
  cases n with
  | zero => simp [pendingAt]
  | succ n => simp [pendingAt, EligibleCut, and_assoc]

def CutWitness (a b c n : Nat) : Prop := ∃ j, j+1 < n ∧ EligibleCut a b c j ∧
  a.testBit (j+1) = false ∧ b.testBit (j+1) = false ∧
  ∀ i, j+1 < i → i < n → a.testBit i = b.testBit i

theorem cutWitness_succ (a b c n : Nat) : CutWitness a b c (n+1) ↔
    (CutWitness a b c n ∧ a.testBit n = b.testBit n) ∨
    (pendingAt a b c n = true ∧ a.testBit n = false ∧ b.testBit n = false) := by
  constructor
  · rintro ⟨j,hj,he,hza,hzb,hs⟩
    by_cases hjn : j+1 < n
    · left
      exact ⟨⟨j,hjn,he,hza,hzb,fun i hi hn => hs i hi (by omega)⟩,
        hs n hjn (by omega)⟩
    · have hn : n = j+1 := by omega
      right
      exact ⟨(pendingAt_iff a b c n).mpr ⟨j,hn,he⟩, hn ▸ hza, hn ▸ hzb⟩
  · rintro (⟨⟨j,hj,he,hza,hzb,hs⟩,hn⟩ | ⟨hp,hza,hzb⟩)
    · refine ⟨j,by omega,he,hza,hzb,?_⟩
      intro i hi hin
      by_cases hh : i < n
      · exact hs i hi hh
      · have hi : i = n := by omega
        simpa [hi] using hn
    · obtain ⟨j,hn,he⟩ := (pendingAt_iff a b c n).mp hp
      refine ⟨j,by omega,he,?_,?_,?_⟩
      · simpa only [hn] using hza
      · simpa only [hn] using hzb
      · intro i hi hin
        omega

theorem validAt_iff (a b c n : Nat) : validAt a b c n = true ↔ CutWitness a b c n := by
  induction n with
  | zero => simp [validAt, CutWitness]
  | succ n ih =>
      rw [cutWitness_succ]
      simp [validAt, ih, and_assoc]

def relAccept (e : Nat) : Bool := e.testBit 0 || e.testBit 2

theorem relationRun_accept_iff (a b c n : Nat) :
    relAccept (relationRun a b c n) = true ↔ PrefixEq a b n ∨ CutWitness a b c n := by
  rw [relationRun_code]
  obtain ⟨_,_,hv,_,hi⟩ := relCode_decode (tailRun a n) (tailRun b n)
    (tailRun_lt b n) (identAt a b n) (pendingAt a b c n) (validAt a b c n)
  simp only [relAccept, hv, hi, Bool.or_eq_true, identAt_iff, validAt_iff, or_comm]

def ZerosFrom (a n : Nat) : Prop := ∀ i, n ≤ i → a.testBit i = false

theorem ZerosFrom.mono {a n m : Nat} (h : ZerosFrom a n) (hn : n ≤ m) : ZerosFrom a m :=
  fun i hi => h i (by omega)

theorem zerosFrom_large (a n : Nat) (ha : a ≤ n) : ZerosFrom a n := by
  intro i hi
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_le_of_lt (by omega) Nat.lt_two_pow_self

theorem ZerosFrom.phi {a n : Nat} (h : ZerosFrom a n) : ZerosFrom (Phi a) (n+2) := by
  intro i hi
  rw [Phi_testBit, before_of_lt a i 0 (by omega), before_of_lt a i 1 (by omega)]
  simp only [h i (by omega), h (i-(0+1)) (by omega), h (i-(1+1)) (by omega)]
  rfl

theorem relationRun_lt (a b c n : Nat) : relationRun a b c n < 200 := by
  cases n with
  | zero => simp [relationRun]
  | succ n => exact relStep_lt _ _ _ _

theorem actualView_valid (a b c n : Nat) : (actualView a b c n).Valid := by
  refine ⟨relationRun_lt _ _ _ _, relationRun_lt _ _ _ _, relationRun_lt _ _ _ _,
    history_lt _ _, history_lt _ _, ?_⟩
  change centerCode c n ≤ 4
  unfold centerCode
  split <;> omega

theorem relAccept_mod (e : Nat) : relAccept (e % 256) = relAccept e := by
  change relAccept (e % 2^8) = relAccept e
  simp only [relAccept, Nat.testBit_mod_two_pow, Nat.reduceLT, decide_true, Bool.true_and]

theorem View.accept_encode (v : View) (hv : v.Valid) :
    accept v.encode 0 = relAccept v.e0 ∧ accept v.encode 1 = relAccept v.e1 ∧
    accept v.encode 2 = relAccept v.e2 := by
  obtain ⟨h0,h1,h2,_,_,_⟩ := v.decode_encode hv
  have a0 := congrArg relAccept h0
  have a1 := congrArg relAccept h1
  have a2 := congrArg relAccept h2
  simp only [relAccept_mod] at a0 a1 a2
  exact ⟨a0,a1,a2⟩

theorem step_actual_zero (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (ha : a.testBit n = false) (hb : b.testBit n = false) (hc : n ≠ c) :
    step (actualView a b c n).encode 0 = some (actualView a b c (n+1)).encode := by
  have h := (actualView a b c n).encode_advance (actualView_valid a b c n)
    (a.testBit n) (b.testBit n) (decide (n = c))
  rw [actualView_advance a b c n h0 h1] at h
  simpa only [ha,hb,hc,decide_false,symbol,Bool.toNat_false,Nat.mul_zero,
    Nat.add_zero,Option.map_some] using h

theorem flush_actual (a b c n k : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (ha : ZerosFrom a n) (hb : ZerosFrom b n) (hc : c < n) :
    flush k (actualView a b c n).encode = some (actualView a b c (n+k)).encode := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [flush, step_actual_zero a b c n h0 h1 (ha n (by omega)) (hb n (by omega)) (by omega)]
      simp only [Option.bind_some]
      have h := ih (n+1) (ha.mono (by omega)) (hb.mono (by omega)) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h

def RowRelated (a b c : Nat) : Prop := a = b ∨ ∃ j, EligibleCut a b c j ∧
  a.testBit (j+1) = false ∧ b.testBit (j+1) = false ∧
  ∀ i, j+1 < i → a.testBit i = b.testBit i

theorem prefixEq_eq {a b n : Nat} (ha : ZerosFrom a n) (hb : ZerosFrom b n)
    (h : PrefixEq a b n) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h i hi
  · rw [ha i (by omega), hb i (by omega)]

theorem relationRun_full_iff (a b c n : Nat) (ha : ZerosFrom a n) (hb : ZerosFrom b n)
    (hc : c+1 < n) : relAccept (relationRun a b c n) = true ↔ RowRelated a b c := by
  rw [relationRun_accept_iff]
  constructor
  · rintro (he | ⟨j,hj,he,hza,hzb,hs⟩)
    · exact Or.inl (prefixEq_eq ha hb he)
    · right
      refine ⟨j,he,hza,hzb,?_⟩
      intro i hi
      by_cases hin : i < n
      · exact hs i hi hin
      · rw [ha i (by omega), hb i (by omega)]
  · rintro (he | ⟨j,he,hza,hzb,hs⟩)
    · left
      subst b
      intro i hi
      rfl
    · exact Or.inr ⟨j,by have hj := he.1; omega,he,hza,hzb,fun i hi _ => hs i hi⟩

/-- No pair of finite rows can first acquire the common-cut relation after
two steps if its two preceding center observations agree. The common-cut
relation's stripe language is interpreted in TailLanguageResearch;
numerical-normalizer equivalence remains open. -/
theorem two_step_common_cut (a b c : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (h2 : RowRelated (Phi (Phi a)) (Phi (Phi b)) (c+2)) :
    RowRelated a b c ∨ RowRelated (Phi a) (Phi b) (c+1) := by
  let n := a+b+c+1
  have ha : ZerosFrom a n := zerosFrom_large a n (by dsimp [n]; omega)
  have hb : ZerosFrom b n := zerosFrom_large b n (by dsimp [n]; omega)
  have hc : c < n := by dsimp [n]; omega
  have hp : (n+2)+2 ≤ n+5 := by omega
  have ha2 := ha.phi.phi.mono hp
  have hb2 := hb.phi.phi.mono hp
  have r2 := (relationRun_full_iff (Phi (Phi a)) (Phi (Phi b)) (c+2) (n+5)
    ha2 hb2 (by omega)).mpr h2
  have hgood := actual_input_safe a b c n h0 h1
  have hcode : (actualView a b c n).encode >>> 32 ≠ 0 := by
    have hdec := (actualView a b c n).decode_encode (actualView_valid a b c n)
    rw [hdec.2.2.2.2.2]
    change centerCode c n ≠ 0
    unfold centerCode
    split <;> omega
  simp only [endGood, hcode, beq_iff_eq, ↓reduceIte,
    flush_actual a b c n 5 h0 h1 ha hb hc] at hgood
  obtain ⟨ac0,ac1,ac2⟩ := (actualView a b c (n+5)).accept_encode
    (actualView_valid a b c (n+5))
  rw [ac0,ac1,ac2] at hgood
  change (!(relAccept (relationRun (Phi (Phi a)) (Phi (Phi b)) (c+2) (n+5)) &&
    !relAccept (relationRun a b c (n+5)) &&
    !relAccept (relationRun (Phi a) (Phi b) (c+1) (n+5)))) = true at hgood
  rw [r2] at hgood
  have hor : relAccept (relationRun a b c (n+5)) = true ∨
      relAccept (relationRun (Phi a) (Phi b) (c+1) (n+5)) = true := by
    cases hx : relAccept (relationRun a b c (n+5)) <;>
      cases hy : relAccept (relationRun (Phi a) (Phi b) (c+1) (n+5)) <;>
      simp_all
  rcases hor with he | he
  · exact Or.inl ((relationRun_full_iff a b c (n+5) (ha.mono (by omega))
      (hb.mono (by omega)) (by omega)).mp he)
  · exact Or.inr ((relationRun_full_iff (Phi a) (Phi b) (c+1) (n+5)
      (ha.phi.mono (by omega)) (hb.phi.mono (by omega)) (by omega)).mp he)

def ZeroWord (xs : List Bool) : Prop := ∀ b, b ∈ xs → b = false

inductive StripeWord : List Bool → Prop
  | single (zs : List Bool) (h : ZeroWord zs) : StripeWord (zs ++ [true])
  | double (zs : List Bool) (h : ZeroWord zs) : StripeWord (zs ++ [true,true])
  | extend {xs : List Bool} (h : StripeWord xs) : StripeWord (xs ++ [false,true])

def TailInvariant (xs : List Bool) (s : Nat) : Prop :=
  match s with
  | 0 => ZeroWord xs
  | 1 => ∃ zs, ZeroWord zs ∧ xs = zs ++ [true]
  | 2 => ∃ ys, StripeWord ys ∧ xs = ys ++ [false]
  | 3 => StripeWord xs
  | _ => True

theorem zeroWord_append_false {xs : List Bool} (h : ZeroWord xs) :
    ZeroWord (xs ++ [false]) := by
  intro b hb
  simp only [List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | hb
  · exact h b hb
  · exact hb

theorem tailInvariant_step (xs : List Bool) (s : Nat) (b : Bool)
    (h : TailInvariant xs s) : TailInvariant (xs ++ [b]) (tailNext s b) := by
  rcases s with _ | s
  · cases b
    · exact zeroWord_append_false h
    · exact ⟨xs,h,rfl⟩
  · rcases s with _ | s
    · obtain ⟨zs,hz,rfl⟩ := h
      cases b
      · exact ⟨zs ++ [true],StripeWord.single zs hz,rfl⟩
      · simpa [TailInvariant, tailNext, List.append_assoc] using
          StripeWord.double zs hz
    · rcases s with _ | s
      · obtain ⟨ys,hy,rfl⟩ := h
        cases b
        · trivial
        · simpa [TailInvariant, tailNext, List.append_assoc] using
            StripeWord.extend hy
      · rcases s with _ | s
        · cases b
          · exact ⟨xs,h,rfl⟩
          · trivial
        · cases b <;> trivial

def tailFold (s : Nat) (xs : List Bool) : Nat := xs.foldl tailNext s

theorem tailFold_append (s : Nat) (xs ys : List Bool) :
    tailFold s (xs ++ ys) = tailFold (tailFold s xs) ys := List.foldl_append

theorem tailInvariant_fold (xs ys : List Bool) (s : Nat) (h : TailInvariant xs s) :
    TailInvariant (xs ++ ys) (tailFold s ys) := by
  induction ys generalizing xs s with
  | nil => simpa only [List.append_nil,tailFold,List.foldl_nil] using h
  | cons b ys ih =>
      have hh := ih (xs ++ [b]) (tailNext s b) (tailInvariant_step xs s b h)
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        tailFold, List.foldl_cons] using hh

theorem tailFold_zero {xs : List Bool} (h : ZeroWord xs) : tailFold 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      have hb := h b (by simp)
      have hx : ZeroWord xs := fun x hx => h x (by simp [hx])
      simpa [tailFold, hb, tailNext] using ih hx

theorem stripeWord_accept {xs : List Bool} (h : StripeWord xs) :
    tailFold 0 xs = 1 ∨ tailFold 0 xs = 3 := by
  induction h with
  | single zs hz =>
      left
      rw [tailFold_append, tailFold_zero hz]
      rfl
  | double zs hz =>
      right
      rw [tailFold_append, tailFold_zero hz]
      rfl
  | extend h ih =>
      right
      rw [tailFold_append]
      rcases ih with hi | hi <;> rw [hi] <;> rfl

theorem tailFold_accept_iff (xs : List Bool) :
    tailFold 0 xs = 1 ∨ tailFold 0 xs = 3 ↔ StripeWord xs := by
  constructor
  · intro h
    have hz : TailInvariant [] 0 := by intro b hb; simp at hb
    have hi := tailInvariant_fold [] xs 0 hz
    simp only [List.nil_append] at hi
    rcases h with h | h
    · rw [h] at hi
      obtain ⟨zs,hz,rfl⟩ := hi
      exact StripeWord.single zs hz
    · simpa only [h, TailInvariant] using hi
  · exact stripeWord_accept

def rowBits (a n : Nat) : List Bool := (List.range n).map a.testBit

theorem rowBits_succ (a n : Nat) : rowBits a (n+1) = rowBits a n ++ [a.testBit n] := by
  simp only [rowBits, List.range_succ, List.map_append, List.map_singleton]

theorem tailRun_eq_fold (a n : Nat) : tailRun a n = tailFold 0 (rowBits a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rowBits_succ, tailFold_append, ← ih]
      rfl

theorem tailRun_accept_iff (a n : Nat) :
    tailRun a n = 1 ∨ tailRun a n = 3 ↔ StripeWord (rowBits a n) := by
  rw [tailRun_eq_fold]
  exact tailFold_accept_iff _

def StripeRelated (a b c : Nat) : Prop := a = b ∨ ∃ j, j ≤ c ∧
  StripeWord (rowBits a (j+1)) ∧ StripeWord (rowBits b (j+1)) ∧
  a.testBit j = true ∧ b.testBit j = true ∧
  a.testBit (j+1) = false ∧ b.testBit (j+1) = false ∧
  ∀ i, j+1 < i → a.testBit i = b.testBit i

theorem rowRelated_iff_stripeRelated (a b c : Nat) :
    RowRelated a b c ↔ StripeRelated a b c := by
  unfold RowRelated StripeRelated EligibleCut
  simp only [tailRun_accept_iff]
  constructor
  · rintro (he | ⟨j,⟨hc,ha,hb,hsa,hsb⟩,hza,hzb,hs⟩)
    · exact Or.inl he
    · exact Or.inr ⟨j,hc,hsa,hsb,ha,hb,hza,hzb,hs⟩
  · rintro (he | ⟨j,hc,hsa,hsb,ha,hb,hza,hzb,hs⟩)
    · exact Or.inl he
    · exact Or.inr ⟨j,⟨hc,ha,hb,hsa,hsb⟩,hza,hzb,hs⟩

/-- A pair with equal first two center observations cannot first become
stripe-related on the second step. This quantifies over all finite integer
rows and all center indices, with no bound on their sizes. -/
theorem two_step_stripe_related (a b c : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (h2 : StripeRelated (Phi (Phi a)) (Phi (Phi b)) (c+2)) :
    StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1) := by
  have h := two_step_common_cut a b c h0 h1
    ((rowRelated_iff_stripeRelated _ _ _).mpr h2)
  rcases h with h | h
  · exact Or.inl ((rowRelated_iff_stripeRelated _ _ _).mp h)
  · exact Or.inr ((rowRelated_iff_stripeRelated _ _ _).mp h)

def phiRows (a : Nat) : Nat → Nat
  | 0 => a
  | t+1 => Phi (phiRows a t)

def SameCenterPrefix (a b c t : Nat) : Prop :=
  ∀ s, s < t → (phiRows a s).testBit (c+s) = (phiRows b s).testBit (c+s)

theorem sameCenterPrefix_mono {a b c t u : Nat} (h : SameCenterPrefix a b c t)
    (hu : u ≤ t) : SameCenterPrefix a b c u := fun s hs => h s (by omega)

/-- If finite rows become stripe-related after any number of steps, and all
preceding center observations agree, they were stripe-related at time 0 or 1.
The stripe relation is allowed to disappear and reappear; no equivariance
or preservation under Phi is assumed. -/
theorem stripe_meeting_is_early (a b c t : Nat) (ht : SameCenterPrefix a b c t)
    (hr : StripeRelated (phiRows a t) (phiRows b t) (c+t)) :
    StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
      rcases t with _ | t
      · exact Or.inl hr
      · rcases t with _ | t
        · exact Or.inr hr
        · have h0 := ht t (by omega)
          have h1 := ht (t+1) (by omega)
          have hh : StripeRelated (Phi (Phi (phiRows a t)))
              (Phi (Phi (phiRows b t))) ((c+t)+2) := by
            simpa only [phiRows, Nat.add_assoc] using hr
          have he := two_step_stripe_related (phiRows a t) (phiRows b t) (c+t)
            h0 (by simpa only [phiRows, Nat.add_assoc] using h1) hh
          rcases he with he | he
          · exact ih t (by omega) (sameCenterPrefix_mono ht (by omega)) he
          · apply ih (t+1) (by omega) (sameCenterPrefix_mono ht (by omega))
            simpa only [phiRows, Nat.add_assoc] using he

/-- The contrapositive is useful for a trace-completeness argument: two rows
not stripe-related at time 0 or 1 cannot become stripe-related later while
their center observations continue to agree. It does not establish that
every equal infinite trace must eventually enter this relation. -/
theorem no_delayed_stripe_meeting (a b c t : Nat)
    (h0 : ¬ StripeRelated a b c)
    (h1 : ¬ StripeRelated (Phi a) (Phi b) (c+1))
    (ht : SameCenterPrefix a b c t) :
    ¬ StripeRelated (phiRows a t) (phiRows b t) (c+t) := by
  intro hr
  rcases stripe_meeting_is_early a b c t ht hr with h | h
  · exact h0 h
  · exact h1 h

theorem StripeRelated.center_pair {a b c : Nat} (h : StripeRelated a b c) :
    a.testBit c = b.testBit c ∧ (Phi a).testBit (c+1) = (Phi b).testBit (c+1) := by
  rcases h with he | ⟨j,hjc,hsa,hsb,hja,hjb,hza,hzb,hs⟩
  · subst b
    exact ⟨rfl,rfl⟩
  · have hagree : ∀ i, j ≤ i → a.testBit i = b.testBit i := by
      intro i hi
      by_cases h0 : i = j
      · rw [h0,hja,hjb]
      · by_cases h1 : i = j+1
        · rw [h1,hza,hzb]
        · exact hs i (by omega)
    refine ⟨hagree c hjc,?_⟩
    by_cases hc : c = j
    · subst c
      rw [Phi_testBit, Phi_testBit, before_succ_zero, before_succ_zero,hza,hzb,hja,hjb]
      simp
    · rw [Phi_testBit, Phi_testBit, before_succ_zero, before_succ_zero,
        before_of_lt a (c+1) 1 (by omega), before_of_lt b (c+1) 1 (by omega),
        hagree (c+1) (by omega), hagree c hjc, hagree ((c+1)-(1+1)) (by omega)]

theorem preservesTwo_after_actual (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    preservesTwo (actualView a b c n).encode = true := by
  have hr : Rule30Submission.run initial
      ((actualInput a b c n).map Letter.val) = some (actualView a b c n).encode := by
    rw [← initialView_encode, initialView.run_encode initialView_valid,
      actualInput_run a b c n h0 h1]
    rfl
  apply all_of_member preservesTwo_pool (run_member initial_member ?_ hr)
  intro u hu
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
  exact symbol_lt x.a x.b x.marker

/-- Stripe-related rows remain stripe-related after two Rule 30 steps.
One-step preservation is false, as shown by rows 2 and 3 at center 1. -/
theorem stripe_related_preserves_two (a b c : Nat) (h : StripeRelated a b c) :
    StripeRelated (Phi (Phi a)) (Phi (Phi b)) (c+2) := by
  obtain ⟨h0,h1⟩ := h.center_pair
  let n := a+b+c+1
  have ha : ZerosFrom a n := zerosFrom_large a n (by dsimp [n]; omega)
  have hb : ZerosFrom b n := zerosFrom_large b n (by dsimp [n]; omega)
  have hc : c < n := by dsimp [n]; omega
  have he := (rowRelated_iff_stripeRelated a b c).mpr h
  have r0 := (relationRun_full_iff a b c (n+5) (ha.mono (by omega))
    (hb.mono (by omega)) (by omega)).mpr he
  have hg := preservesTwo_after_actual a b c n h0 h1
  have hcode : (actualView a b c n).encode >>> 32 ≠ 0 := by
    have hdec := (actualView a b c n).decode_encode (actualView_valid a b c n)
    rw [hdec.2.2.2.2.2]
    change centerCode c n ≠ 0
    unfold centerCode
    split <;> omega
  simp only [preservesTwo, hcode, beq_iff_eq, ↓reduceIte,
    flush_actual a b c n 5 h0 h1 ha hb hc] at hg
  obtain ⟨ac0,_,ac2⟩ := (actualView a b c (n+5)).accept_encode
    (actualView_valid a b c (n+5))
  rw [ac0,ac2] at hg
  change (!relAccept (relationRun a b c (n+5)) ||
    relAccept (relationRun (Phi (Phi a)) (Phi (Phi b)) (c+2) (n+5))) = true at hg
  rw [r0] at hg
  simp only [Bool.not_true, Bool.false_or] at hg
  apply (rowRelated_iff_stripeRelated _ _ _).mp
  apply (relationRun_full_iff _ _ _ (n+5) (ha.phi.phi.mono (by omega))
    (hb.phi.phi.mono (by omega)) (by omega)).mp
  exact hg

theorem phiRows_add (a s t : Nat) : phiRows a (s+t) = phiRows (phiRows a s) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change Phi (phiRows a (s+t)) = Phi (phiRows (phiRows a s) t)
      exact congrArg Phi ih

theorem phiRows_two_start (a t : Nat) :
    phiRows (Phi (Phi a)) t = phiRows a (t+2) := by
  have h := (phiRows_add a 2 t).symm
  simpa only [Nat.add_comm 2 t,phiRows] using h

/-- Erasing or replacing a stripe prefix with a common white separator
preserves the entire center trace. This is one direction of the trace-kernel
classification; the converse is not claimed. -/
theorem stripe_related_same_trace (a b c : Nat) (h : StripeRelated a b c) (t : Nat) :
    (phiRows a t).testBit (c+t) = (phiRows b t).testBit (c+t) := by
  induction t using Nat.strongRecOn generalizing a b c with
  | ind t ih =>
      rcases t with _ | t
      · exact h.center_pair.1
      · rcases t with _ | t
        · exact h.center_pair.2
        · have hn : t+1+1 = t+2 := by omega
          rw [hn]
          have hh := ih t (by omega) (Phi (Phi a)) (Phi (Phi b)) (c+2)
            (stripe_related_preserves_two a b c h)
          have hc : (c+2)+t = c+(t+2) := by omega
          simpa only [phiRows_two_start,hc] using hh

theorem stripe_related_same_prefix (a b c t : Nat) (h : StripeRelated a b c) :
    SameCenterPrefix a b c t := fun s _ => stripe_related_same_trace a b c h s

/-- For a pair with equal entire center traces, entering the stripe relation
at any finite time is equivalent to entering it at time zero or one. This
does not assert that such an entry must happen. -/
theorem eventually_stripe_iff_early (a b c : Nat)
    (ht : ∀ t, (phiRows a t).testBit (c+t) = (phiRows b t).testBit (c+t)) :
    (∃ t, StripeRelated (phiRows a t) (phiRows b t) (c+t)) ↔
      StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1) := by
  constructor
  · rintro ⟨t,hr⟩
    exact stripe_meeting_is_early a b c t (fun s _ => ht s) hr
  · rintro (h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩

end Rule30Submission
