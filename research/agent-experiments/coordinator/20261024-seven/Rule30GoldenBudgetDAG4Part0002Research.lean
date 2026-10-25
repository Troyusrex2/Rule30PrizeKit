import Rule30GoldenBudgetDAG4Part0001Research
import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudgetDAG4Part0002Research
open Rule30GoldenCompactBudgetResearch

theorem node_256 : dfs 4 32 18 608435468703249170068874 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9759570260231073854698149 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_216
  · change dfs 4 31 19 12101864035734582476623194 = true
    apply dfs_of_prune
    decide +kernel

theorem node_257 : dfs 4 32 18 608716986464153376749962 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9757196190502263152878245 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_213
  · change dfs 4 31 19 12099489966005755998723418 = true
    apply dfs_of_prune
    decide +kernel

theorem node_258 : dfs 4 32 18 608745569369555656333994 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9696598660444613233551962 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 31 19 12190008163399843177092517 = true
    apply dfs_of_prune
    decide +kernel

theorem node_259 : dfs 4 32 18 608768705239350944381322 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9759606589080454548791973 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_218
  · change dfs 4 31 19 12101900364583890057583962 = true
    apply dfs_of_prune
    decide +kernel

theorem node_260 : dfs 4 32 18 608994347402628688409994 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9760368514257862498235045 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_219
  · change dfs 4 31 19 12102662289761298164436314 = true
    apply dfs_of_prune
    decide +kernel

theorem node_261 : dfs 4 32 18 608994623812133888281258 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9772169706769569606313381 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_221
  · change dfs 4 31 19 12114463482273005338057306 = true
    apply dfs_of_prune
    decide +kernel

theorem node_262 : dfs 4 32 18 609381062736046444421797 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9824195115296067413247605 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_223
  · change dfs 4 31 19 12128709958936717769144714 = true
    apply dfs_of_prune
    decide +kernel

theorem node_263 : dfs 4 32 18 609574489388960577803685 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9712921700171490398221706 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_194
  · change dfs 4 31 19 12244110134989845053917813 = true
    apply dfs_of_prune
    decide +kernel

theorem node_264 : dfs 4 32 18 609615700276634799678117 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9743804600939694463482250 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_206
  · change dfs 4 31 19 12274993035757915654489717 = true
    apply dfs_of_prune
    decide +kernel

theorem node_265 : dfs 4 32 18 609949179866371105141413 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9739687948340496257694090 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_205
  · change dfs 4 31 19 12270876383158740586940021 = true
    apply dfs_of_prune
    decide +kernel

theorem node_266 : dfs 4 32 18 609971049346153428988581 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9853613886818229339637365 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_225
  · change dfs 4 31 19 12158128730458715702606218 = true
    apply dfs_of_prune
    decide +kernel

theorem node_267 : dfs 4 32 18 609972958872436727132837 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9720307409905643449661834 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_197
  · change dfs 4 31 19 12251495844723899275495029 = true
    apply dfs_of_prune
    decide +kernel

theorem node_268 : dfs 4 32 18 609975552945790086853285 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9716763905661208355322250 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_196
  · change dfs 4 31 19 12247952340479516081473141 = true
    apply dfs_of_prune
    decide +kernel

theorem node_269 : dfs 4 32 18 610124534418400272033189 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9715483129214976427455882 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_195
  · change dfs 4 31 19 12246671564033291845995125 = true
    apply dfs_of_prune
    decide +kernel

theorem node_270 : dfs 4 32 18 610858546703130837824165 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9721457953509627191277962 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_199
  · change dfs 4 31 19 12252646388327922724587125 = true
    apply dfs_of_prune
    decide +kernel

theorem node_271 : dfs 4 32 18 610931762852570768692645 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9847807391315064868129397 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_224
  · change dfs 4 31 19 12152322234955543358387594 = true
    apply dfs_of_prune
    decide +kernel

theorem node_272 : dfs 4 32 18 615284417478720268356213 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9986220374733838086743381 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_228
  · change dfs 4 31 19 12139619490922579388357290 = true
    apply dfs_of_prune
    decide +kernel

theorem node_273 : dfs 4 32 18 615359957481170037720693 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9998824330483882427348309 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_230
  · change dfs 4 31 19 12152223446672523098131114 = true
    apply dfs_of_prune
    decide +kernel

theorem node_274 : dfs 4 32 18 615506553026734938475125 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9986151055328382777206101 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_227
  · change dfs 4 31 19 12139550171517105724545706 = true
    apply dfs_of_prune
    decide +kernel

theorem node_275 : dfs 4 32 18 615532583832579730393717 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9985455987776289443063125 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_226
  · change dfs 4 31 19 12138855103965019352947370 = true
    apply dfs_of_prune
    decide +kernel

theorem node_276 : dfs 4 32 18 616077897126913181583989 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9998617982867302618670421 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_229
  · change dfs 4 31 19 12152017099055949463509674 = true
    apply dfs_of_prune
    decide +kernel

theorem node_277 : dfs 4 32 18 623456559537982985119061 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 10300859387489174100276565 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_231
  · change dfs 4 31 19 12152027048774163788827306 = true
    apply dfs_of_prune
    decide +kernel

theorem node_278 : dfs 4 32 18 623807000387532752069973 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 10310525229182223066232149 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_233
  · change dfs 4 31 19 12161692890467204167469738 = true
    apply dfs_of_prune
    decide +kernel

theorem node_279 : dfs 4 32 18 642436264974740654568789 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9745291915846930331708074 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_208
  · change dfs 4 31 19 12125364623213325258741077 = true
    apply dfs_of_prune
    decide +kernel

theorem node_280 : dfs 4 32 18 642469918685909017589077 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9707622907843676208452949 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 31 19 12163253478935989100128938 = true
    apply dfs_of_prune
    decide +kernel

theorem node_281 : dfs 4 32 18 642629955787573937485141 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9722367224649330974108330 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_201
  · change dfs 4 31 19 12102439932015719525799253 = true
    apply dfs_of_prune
    decide +kernel

theorem node_282 : dfs 4 32 18 643857456901970100139349 = true := by
  apply dfs_of_children (fuel:=31)
  · change dfs 4 31 19 9696626810907100245808469 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 31 19 12152257381999407342922410 = true
    apply dfs_of_prune
    decide +kernel

theorem node_283 : dfs 4 33 17 28531685493877770988202 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 459964569886687319401893 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_236
  · change dfs 4 32 18 606357930855674596186714 = true
    apply dfs_of_prune
    decide +kernel

theorem node_284 : dfs 4 33 17 28582463509032759621002 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 454134864937697285721434 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 32 18 609972958872436727132837 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_267

theorem node_285 : dfs 4 33 17 28632439593159856661925 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 463573187492407699671669 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_237
  · change dfs 4 32 18 607605365219955325695370 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_248

theorem node_286 : dfs 4 33 17 28660380206709115037093 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 464962169675084534745717 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_240
  · change dfs 4 32 18 608994347402628688409994 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_260

theorem node_287 : dfs 4 33 17 28678504344176025973413 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 464736527511801711380085 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_239
  · change dfs 4 32 18 608768705239350944381322 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_259

theorem node_288 : dfs 4 33 17 28770820537814370047397 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 464390825574906291636853 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_238
  · change dfs 4 32 18 608423003302453377152394 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_255

theorem node_289 : dfs 4 33 17 28936791105848172694133 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 455812549396044690315946 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_234
  · change dfs 4 32 18 623456559537982985119061 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_277

theorem node_290 : dfs 4 33 17 28971018463018572925557 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 474158124607745104192853 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_242
  · change dfs 4 32 18 608745569369555656333994 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_258

theorem node_291 : dfs 4 33 17 28972238797782315010677 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 472691272935704105231701 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_241
  · change dfs 4 32 18 607278717697532358384298 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_245

theorem node_292 : dfs 4 33 17 29555243588480882898261 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 456096479714166069086890 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_235
  · change dfs 4 32 18 642629955787573937485141 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_281

theorem node_293 : dfs 4 33 17 37938802213833896015242 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 609949179866371105141413 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_265
  · change dfs 4 32 18 756342540835355168951642 = true
    apply dfs_of_prune
    decide +kernel

theorem node_294 : dfs 4 33 17 37951470135883355224458 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 609381062736046444421797 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_262
  · change dfs 4 32 18 755774423705067273936218 = true
    apply dfs_of_prune
    decide +kernel

theorem node_295 : dfs 4 33 17 37957007311626687052170 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 604659669030698555891034 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 32 18 760497762965454186521253 = true
    apply dfs_of_prune
    decide +kernel

theorem node_296 : dfs 4 33 17 37966958886101822802602 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 610931762852570768692645 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_271
  · change dfs 4 32 18 757325123821553037519450 = true
    apply dfs_of_prune
    decide +kernel

theorem node_297 : dfs 4 33 17 37973029570999527323018 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 610858546703130837824165 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_270
  · change dfs 4 32 18 757251907672112737373530 = true
    apply dfs_of_prune
    decide +kernel

theorem node_298 : dfs 4 33 17 37973545092683630217898 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 604899556083998250588762 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 32 18 760737650018753897997733 = true
    apply dfs_of_prune
    decide +kernel

theorem node_299 : dfs 4 33 17 37974249905758843336074 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 609975552945790086853285 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_268
  · change dfs 4 32 18 756368913914771950488922 = true
    apply dfs_of_prune
    decide +kernel

theorem node_300 : dfs 4 33 17 37974548691438298380682 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 609615700276634799678117 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_264
  · change dfs 4 32 18 756009061245650924363098 = true
    apply dfs_of_prune
    decide +kernel

theorem node_301 : dfs 4 33 17 37975029336624272837290 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 604881230796377037646426 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 32 18 760719324731132593132965 = true
    apply dfs_of_prune
    decide +kernel

theorem node_302 : dfs 4 33 17 37985497285457603287722 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 609574489388960577803685 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_263
  · change dfs 4 32 18 755967850357965848259162 = true
    apply dfs_of_prune
    decide +kernel

theorem node_303 : dfs 4 33 17 37987226667714303842986 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 604857887513614198975066 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 32 18 760695981448358295557541 = true
    apply dfs_of_prune
    decide +kernel

theorem node_304 : dfs 4 33 17 38015687666663135557002 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 606025499755819821518170 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 32 18 761863593690539239060133 = true
    apply dfs_of_prune
    decide +kernel

theorem node_305 : dfs 4 33 17 38023534344862603496106 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 605272866212519061707354 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 32 18 761110960147257449817509 = true
    apply dfs_of_prune
    decide +kernel

theorem node_306 : dfs 4 33 17 38024113901564714464650 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 609971049346153428988581 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_266
  · change dfs 4 32 18 756364410315153867361626 = true
    apply dfs_of_prune
    decide +kernel

theorem node_307 : dfs 4 33 17 38027032164034957388458 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 610124534418400272033189 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_269
  · change dfs 4 32 18 756517895387379294427738 = true
    apply dfs_of_prune
    decide +kernel

theorem node_308 : dfs 4 33 17 38027554510942400837002 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 605248971093660027800922 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 32 18 761087065028399571972773 = true
    apply dfs_of_prune
    decide +kernel

theorem node_309 : dfs 4 33 17 38105113172448405464485 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 616077897126913181583989 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_276
  · change dfs 4 32 18 760110074854457335248266 = true
    apply dfs_of_prune
    decide +kernel

theorem node_310 : dfs 4 33 17 38123247055988535698085 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 608716986464153376749962 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_257
  · change dfs 4 32 18 766916263640315033978485 = true
    apply dfs_of_prune
    decide +kernel

theorem node_311 : dfs 4 33 17 38126156241707084391845 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 607209841086241853568394 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_243
  · change dfs 4 32 18 765409118262430092593781 = true
    apply dfs_of_prune
    decide +kernel

theorem node_312 : dfs 4 33 17 38169543321291413041829 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 615359957481170037720693 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_273
  · change dfs 4 32 18 759392135208705664399754 = true
    apply dfs_of_prune
    decide +kernel

theorem node_313 : dfs 4 33 17 38172463660454559131045 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 607660354171370889442698 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_251
  · change dfs 4 32 18 765859631347549817113205 = true
    apply dfs_of_prune
    decide +kernel

theorem node_314 : dfs 4 33 17 38172631138064628295077 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 608398286984725507241354 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_253
  · change dfs 4 32 18 766597564160881529817717 = true
    apply dfs_of_prune
    decide +kernel

theorem node_315 : dfs 4 33 17 38173612641308373067173 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 608406789780822003447178 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_254
  · change dfs 4 32 18 766606066956977984604789 = true
    apply dfs_of_prune
    decide +kernel

theorem node_316 : dfs 4 33 17 38175994728857984095653 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 615284417478720268356213 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_272
  · change dfs 4 32 18 759316595206255849420170 = true
    apply dfs_of_prune
    decide +kernel

theorem node_317 : dfs 4 33 17 38177476729788534269349 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 608435468703249170068874 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_256
  · change dfs 4 32 18 766634745879405008620149 = true
    apply dfs_of_prune
    decide +kernel

theorem node_318 : dfs 4 33 17 38194175760547298727333 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 615532583832579730393717 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_275
  · change dfs 4 32 18 759564761560129635005834 = true
    apply dfs_of_prune
    decide +kernel

theorem node_319 : dfs 4 33 17 38194423212236235646373 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 607558897078968372589962 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_246
  · change dfs 4 32 18 765758174255141528898165 = true
    apply dfs_of_prune
    decide +kernel

theorem node_320 : dfs 4 33 17 38215553503553660474789 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 615506553026734938475125 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_274
  · change dfs 4 32 18 759538730754282023990666 = true
    apply dfs_of_prune
    decide +kernel

theorem node_321 : dfs 4 33 17 38416971763521605438069 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 623807000387532752069973 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_278
  · change dfs 4 32 18 758394445149361005222570 = true
    apply dfs_of_prune
    decide +kernel

theorem node_322 : dfs 4 33 17 38469918332546761198197 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 608247568078141676935850 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_252
  · change dfs 4 32 18 775891578220026000483669 = true
    apply dfs_of_prune
    decide +kernel

theorem node_323 : dfs 4 33 17 38504742557397168507509 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 607608500535603657792170 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_249
  · change dfs 4 32 18 775252510677517390751061 = true
    apply dfs_of_prune
    decide +kernel

theorem node_324 : dfs 4 33 17 38983335648042762806613 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 642469918685909017589077 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_280
  · change dfs 4 32 18 758167897516271340980906 = true
    apply dfs_of_prune
    decide +kernel

theorem node_325 : dfs 4 33 17 38984430128304013636949 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 642436264974740654568789 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_279
  · change dfs 4 32 18 758134243805108745095850 = true
    apply dfs_of_prune
    decide +kernel

theorem node_326 : dfs 4 33 17 38985727164996662785365 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 608994623812133888281258 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_261
  · change dfs 4 32 18 795528099885507782817109 = true
    apply dfs_of_prune
    decide +kernel

theorem node_327 : dfs 4 33 17 39004029793884477519189 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 607221430538031310654122 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_244
  · change dfs 4 32 18 793754906611439699146069 = true
    apply dfs_of_prune
    decide +kernel

theorem node_328 : dfs 4 33 17 39061734310358712755541 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 607568678898457169463978 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_247
  · change dfs 4 32 18 794102154971850923996501 = true
    apply dfs_of_prune
    decide +kernel

theorem node_329 : dfs 4 33 17 39061778888958188057941 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 643857456901970100139349 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_282
  · change dfs 4 32 18 759555435732299404888746 = true
    apply dfs_of_prune
    decide +kernel

theorem node_330 : dfs 4 33 17 39095110592750565913941 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 607608812163587264301738 = true
    exact Rule30GoldenBudgetDAG4Part0001Research.node_250
  · change dfs 4 32 18 794142288236979546666325 = true
    apply dfs_of_prune
    decide +kernel

theorem node_331 : dfs 4 33 17 40189300346753628140885 = true := by
  apply dfs_of_children (fuel:=32)
  · change dfs 4 32 18 604935082204236090791253 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 32 18 758411992897544021256874 = true
    apply dfs_of_prune
    decide +kernel

theorem node_332 : dfs 4 34 16 1190234748176006744746 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 18892558722224458914394 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 28632439593159856661925 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_285

theorem node_333 : dfs 4 34 16 1781000698711939812010 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28770820537814370047397 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_288
  · change dfs 4 33 17 37920405598380394981978 = true
    apply dfs_of_prune
    decide +kernel

theorem node_334 : dfs 4 34 16 1783365592093683264170 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28660380206709115037093 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_286
  · change dfs 4 33 17 37809965267280147929690 = true
    apply dfs_of_prune
    decide +kernel

theorem node_335 : dfs 4 34 16 1786260263093546939786 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28429662450368127651162 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 38169543321291413041829 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_312

theorem node_336 : dfs 4 34 16 1786264203742929384842 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28678504344176025973413 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_287
  · change dfs 4 33 17 37828089404746267839834 = true
    apply dfs_of_prune
    decide +kernel

theorem node_337 : dfs 4 34 16 1787652911186718841514 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28436113857932996323930 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 38175994728857984095653 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_316

theorem node_338 : dfs 4 34 16 1790107372840325129637 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28972238797782315010677 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_291
  · change dfs 4 33 17 37974249905758843336074 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_299

theorem node_339 : dfs 4 34 16 1791015894896585528741 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28936791105848172694133 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_289
  · change dfs 4 33 17 37938802213833896015242 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_293

theorem node_340 : dfs 4 34 16 1795723282408092259749 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28971018463018572925557 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_290
  · change dfs 4 33 17 37973029570999527323018 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_297

theorem node_341 : dfs 4 34 16 1795785145330353612197 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28582463509032759621002 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_284
  · change dfs 4 33 17 38469918332546761198197 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_322

theorem node_342 : dfs 4 34 16 1815070739887404959349 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 29555243588480882898261 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_292
  · change dfs 4 33 17 37966958886101822802602 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_296

theorem node_343 : dfs 4 34 16 1918881139091647919445 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28531685493877770988202 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_283
  · change dfs 4 33 17 37828844507033083663701 = true
    apply dfs_of_prune
    decide +kernel

theorem node_344 : dfs 4 34 16 1927203615278350120277 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 28434725245700303902037 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 38027032164034957388458 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_307

theorem node_345 : dfs 4 34 16 2370826368893418048170 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37782024653703039769178 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 47521905524638437516709 = true
    apply dfs_of_prune
    decide +kernel

theorem node_346 : dfs 4 34 16 2371296509070645463722 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38215553503553660474789 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_320
  · change dfs 4 33 17 47365138564119685409370 = true
    apply dfs_of_prune
    decide +kernel

theorem node_347 : dfs 4 34 16 2372036007537377114506 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37790984986275283295578 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 47530865857209408070309 = true
    apply dfs_of_prune
    decide +kernel

theorem node_348 : dfs 4 34 16 2372232105505315969706 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37791229694683219438170 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 47531110565616250836389 = true
    apply dfs_of_prune
    decide +kernel

theorem node_349 : dfs 4 34 16 2373315221215748905642 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38194175760547298727333 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_318
  · change dfs 4 33 17 47343760821113651931738 = true
    apply dfs_of_prune
    decide +kernel

theorem node_350 : dfs 4 34 16 2373334697964739054250 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38194423212236235646373 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_319
  · change dfs 4 33 17 47344008272802516523610 = true
    apply dfs_of_prune
    decide +kernel

theorem node_351 : dfs 4 34 16 2373492499874163559082 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37808541848311815821914 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 47548422719241576424869 = true
    apply dfs_of_prune
    decide +kernel

theorem node_352 : dfs 4 34 16 2373661402452388915882 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38105113172448405464485 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_309
  · change dfs 4 33 17 47254698233019438357082 = true
    apply dfs_of_prune
    decide +kernel

theorem node_353 : dfs 4 34 16 2376359654564597947050 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37877698807533061483098 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 47617579678457435837861 = true
    apply dfs_of_prune
    decide +kernel

theorem node_354 : dfs 4 34 16 2376555528163199396522 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38126156241707084391845 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_311
  · change dfs 4 33 17 47275741302278536714842 = true
    apply dfs_of_prune
    decide +kernel

theorem node_355 : dfs 4 34 16 2376947323738311461546 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38173612641308373067173 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_315
  · change dfs 4 33 17 47323197701874127821402 = true
    apply dfs_of_prune
    decide +kernel

theorem node_356 : dfs 4 34 16 2377696434137351240074 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38123247055988535698085 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_310
  · change dfs 4 33 17 47272832116554476182874 = true
    apply dfs_of_prune
    decide +kernel

theorem node_357 : dfs 4 34 16 2378104185892590946986 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38177476729788534269349 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_317
  · change dfs 4 33 17 47327061790354534390362 = true
    apply dfs_of_prune
    decide +kernel

theorem node_358 : dfs 4 34 16 2378138912798938937738 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37883655555812564557146 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 47623536426736932201125 = true
    apply dfs_of_prune
    decide +kernel

theorem node_359 : dfs 4 34 16 2378876570820865075882 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38172631138064628295077 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_314
  · change dfs 4 33 17 47322216198630292478554 = true
    apply dfs_of_prune
    decide +kernel

theorem node_360 : dfs 4 34 16 2379148845085756312234 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38172463660454559131045 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_313
  · change dfs 4 33 17 47322048721018075961946 = true
    apply dfs_of_prune
    decide +kernel

theorem node_361 : dfs 4 34 16 2380403183199030781349 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38416971763521605438069 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_321
  · change dfs 4 33 17 47418982871498133763466 = true
    apply dfs_of_prune
    decide +kernel

theorem node_362 : dfs 4 34 16 2381257662059758540197 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38504742557397168507509 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_323
  · change dfs 4 33 17 47506753665373194597770 = true
    apply dfs_of_prune
    decide +kernel

theorem node_363 : dfs 4 34 16 2381408119234053383589 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38027554510942400837002 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_308
  · change dfs 4 33 17 47915009334456452745845 = true
    apply dfs_of_prune
    decide +kernel

theorem node_364 : dfs 4 34 16 2382415834557554270885 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37951470135883355224458 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_294
  · change dfs 4 33 17 47838924959405997196917 = true
    apply dfs_of_prune
    decide +kernel

theorem node_365 : dfs 4 34 16 2382698435434579075749 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37957007311626687052170 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_295
  · change dfs 4 33 17 47844462135146369418869 = true
    apply dfs_of_prune
    decide +kernel

theorem node_366 : dfs 4 34 16 2385758235832284960165 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38024113901564714464650 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_306
  · change dfs 4 33 17 47911568725078493710965 = true
    apply dfs_of_prune
    decide +kernel

theorem node_367 : dfs 4 34 16 2385874977580232005029 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38015687666663135557002 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_304
  · change dfs 4 33 17 47903142490174452222581 = true
    apply dfs_of_prune
    decide +kernel

theorem node_368 : dfs 4 34 16 2386154763430763475621 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37974548691438298380682 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_300
  · change dfs 4 33 17 47862003514956997543541 = true
    apply dfs_of_prune
    decide +kernel

theorem node_369 : dfs 4 34 16 2399711155013153015413 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 39095110592750565913941 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_330
  · change dfs 4 33 17 47506825890367869356714 = true
    apply dfs_of_prune
    decide +kernel

theorem node_370 : dfs 4 34 16 2400864076518296733301 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38984430128304013636949 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_325
  · change dfs 4 33 17 47396145425929907014314 = true
    apply dfs_of_prune
    decide +kernel

theorem node_371 : dfs 4 34 16 2401197342890726344309 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38985727164996662785365 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_326
  · change dfs 4 33 17 47397442462622623271594 = true
    apply dfs_of_prune
    decide +kernel

theorem node_372 : dfs 4 34 16 2401925448287332158069 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38983335648042762806613 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_324
  · change dfs 4 33 17 47395050945666023250602 = true
    apply dfs_of_prune
    decide +kernel

theorem node_373 : dfs 4 34 16 2404226189563666991733 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37987226667714303842986 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_303
  · change dfs 4 33 17 48464977301586805171541 = true
    apply dfs_of_prune
    decide +kernel

theorem node_374 : dfs 4 34 16 2404230130213632445045 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37985497285457603287722 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_302
  · change dfs 4 33 17 48463247919329685185877 = true
    apply dfs_of_prune
    decide +kernel

theorem node_375 : dfs 4 34 16 2404285686335709464181 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37975029336624272837290 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_301
  · change dfs 4 33 17 48452779970501509576021 = true
    apply dfs_of_prune
    decide +kernel

theorem node_376 : dfs 4 34 16 2405672443177170193013 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 39061734310358712755541 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_328
  · change dfs 4 33 17 47473449607976604490410 = true
    apply dfs_of_prune
    decide +kernel

theorem node_377 : dfs 4 34 16 2405702103602863179381 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 39061778888958188057941 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_329
  · change dfs 4 33 17 47473494186576002288298 = true
    apply dfs_of_prune
    decide +kernel

theorem node_378 : dfs 4 34 16 2405763992913379149429 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 39004029793884477519189 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_327
  · change dfs 4 33 17 47415745091506075929258 = true
    apply dfs_of_prune
    decide +kernel

theorem node_379 : dfs 4 34 16 2435860113332129428821 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 38023534344862603496106 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_305
  · change dfs 4 33 17 49681876599452382967125 = true
    apply dfs_of_prune
    decide +kernel

theorem node_380 : dfs 4 34 16 2441407395782353134933 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37973545092683630217898 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_298
  · change dfs 4 33 17 49631887347278614787413 = true
    apply dfs_of_prune
    decide +kernel

theorem node_381 : dfs 4 34 16 2442512325804974843221 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 40189300346753628140885 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_331
  · change dfs 4 33 17 47420424023653500947114 = true
    apply dfs_of_prune
    decide +kernel

theorem node_382 : dfs 4 34 16 2511581695726204400981 = true := by
  apply dfs_of_children (fuel:=33)
  · change dfs 4 33 17 37803509507319306540373 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 33 17 47395816425662583515818 = true
    apply dfs_of_prune
    decide +kernel

theorem node_383 : dfs 4 35 15 74468375902644701866 = true := by
  apply dfs_of_children (fuel:=34)
  · change dfs 4 34 16 1181364818404040333914 = true
    apply dfs_of_prune
    decide +kernel
  · change dfs 4 34 16 1790107372840325129637 = true
    exact Rule30GoldenBudgetDAG4Part0002Research.node_338

end Rule30GoldenBudgetDAG4Part0002Research
