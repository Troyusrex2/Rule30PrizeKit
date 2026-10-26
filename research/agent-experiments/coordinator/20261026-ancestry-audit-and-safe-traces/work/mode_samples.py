from mode_data import states_graph,rotate,audit,C,integral

def data_for(P):
    states,word=states_graph(P);mask=(1<<P)-1;chosen={}
    byprofile={};bypair={}
    for i,(l,k,d) in enumerate(states):byprofile.setdefault(k,i);bypair.setdefault((l,k),i)
    for i,(l,k,d) in enumerate(states):
        drive=l|k
        if drive.bit_count()%2==0:continue
        for b in [0,1]:
            H=integral(drive|(drive<<P),b,2*P);K=k|(k<<P);gdrive=H|K
            if gdrive.bit_count()%2:continue
            for g0 in [0,1]:
                if C[C[C[d][b]][g0]][0] not in {0,1,2,3,5}:continue
                G=integral(gdrive,g0,2*P);q=(G^(G>>P))&mask;R=G|H;rho=(R^(R>>P))&mask
                S=mask^(rho^rotate(rho,1,P));assert S==q|((~k&~l)&mask)
                if S in chosen:assert chosen[S]['mode']==q
                else:chosen[S]={'clock':P,'initial_parent':word(i)+[b,g0],'mode':q,
                    'derived_observation':S,'rho':rho,'original_OR':R,
                    'newer_profile':G,'older_profile':H,'original_older_pair':[l,k]}
    return list(chosen.values()),states,word,byprofile,bypair
