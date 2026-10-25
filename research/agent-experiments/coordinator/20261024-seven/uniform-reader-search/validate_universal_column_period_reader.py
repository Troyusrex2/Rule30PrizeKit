"""Positive and negative controls for the universal spatial product-graph model."""
import numpy as np
from core import save
from universal_column_period_reader import synth

def main():
 T=np.array([[1 if a&1 else 2 if a&2 else 3 for a in range(8)], [1 if a&1 else 3 for a in range(8)], [2 if not a&1 and a&2 else 3 for a in range(8)], [3]*8],dtype=np.int16)
 black=synth(T,pattern=(1,));white=synth(T,pattern=(0,))
 assert black.get('exact_rational_graph_certificate') and black['rational_gamma']=='2'
 assert white['solver_status']==2
 save('universal-column-period-controls.json',{'black_column':black,'all_white_column':white,'interpretation':'Known black-run mass bound provides a positive control. An all-white column cannot force positive initial black mass. Neither control is claimed as a new prize result.','all_passed':True,'Lean_verified':False,'full_problem_solved':False})
 print({'black_gamma_exact':black['rational_gamma'],'white_infeasible':True,'all_passed':True},flush=True)
if __name__=='__main__':main()
