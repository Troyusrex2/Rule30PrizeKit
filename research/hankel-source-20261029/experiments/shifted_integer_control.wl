rows=CellularAutomaton[30,{{1},0},131];
c=rows[[130;;132,132]];
a=rows[[37;;41,132]];
result=<|"time"->129,"centerWord"->rows[[130,130;;134]],
 "centerTriple"->c,"sourceRightNeighbor"->rows[[131,133]],
 "freshSource"->rows[[131,132]] rows[[131,133]],
 "integerDeterminant"->Det[{{c[[1]],c[[2]]},{c[[2]],c[[3]]}}],
 "smallerCenterWord"->a,"smallerParentDeterminant"->Det[Table[a[[i+j-1]],{i,2},{j,2}]],
 "smallerChildDeterminant"->Det[Table[a[[i+j-1]],{i,3},{j,3}]],
 "smallerFreshSource"->rows[[40,132]] rows[[40,133]]|>;
Print[ExportString[result,"RawJSON"]];
