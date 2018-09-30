open PropLogicTableau
open Printf

module PropLogicTableau =
struct
	exception Atom_exception
	type prop = 
		ATOM of string |
		NOT of prop |
		AND of prop * prop |
		OR of prop * prop |
		COND of prop * prop |
		BIC of prop * prop
	type argument = prop list * prop
	
	let rec convert_arg_to_Prop prop_list =
		match prop_list with
			 p1::x ->   if(x=[]) then
							p1
						else
							AND(p1, convert_arg_to_Prop x)
			|[] -> ATOM("shouldn't reach here")
	
	(*
	let rec convert_to_NNF prop =
		match prop with
			 ATOM(a) -> ATOM(a)
			|NOT(ATOM a) -> NOT(ATOM a)
			|NOT (NOT (p)) -> convert_to_NNF(p)
			|AND(p, q) -> AND( convert_to_NNF(p) , convert_to_NNF(q) )
			|NOT (AND(p, q)) -> convert_to_NNF (OR (NOT (p) , NOT (q) ) )
			|OR (p, q) -> OR ( convert_to_NNF (p) , convert_to_NNF (q) )
			|NOT (OR (p, q) ) -> convert_to_NNF (AND (NOT (p) , NOT (q) ))
	*)
	
	let rec print_tuple_list_to_file fout dir =
		match dir with
			 (a,b)::tl -> (fprintf fout "%d->%d;\n" a b; print_tuple_list_to_file fout tl)
			| [] -> ()
	
	let tableau prop_list =
		let fout = open_out "arg.dot" in
		let _ = fprintf fout "%s\n%s\n%s\n" "digraph {" "\tranksep = 0.35;" "\tnode [shape=plaintext];" in
		(*extras - for expanding "A" of "and(A,B)" in all the branches in its subtrees*)
		(*fml_map - map of tree nodes index to propositional formula *)
		let rec tableau_helper prop lits n1 n2 extras =
			match prop with
				 AND(a,b) -> 	let _ = printf "and %d %d\n" n1 n2 in
								let (litsA, nA, dirA, fml_map) = tableau_helper b lits (n2+1) (n2+2) (a::extras) in
							 (* let _ = printf "nA: %d\n" nA in *)
							 (*let (litsB, nB, dirB) = tableau_helper a litsA nA (nA+1) in *)
								(litsA, nA, (n1,n2)::(n2,n2+1)::(dirA), (n2,a)::(n2+1,b)::fml_map)
				|OR(a,b) -> let _ = printf "or %d %d\n" n1 n2 in
							let (litsA, nA, dirA, fml_map1) = tableau_helper a lits n2 (n2+2) extras in
							let (litsB, nB, dirB, fml_map2) = tableau_helper b lits (n2+1) (nA+1) extras in
								(litsA@litsB, nB, (n1,n2)::(n1,n2+1)::(dirA@dirB), (n2,a)::(n2+1,b)::(fml_map1@fml_map2))
				|COND(a,b) -> tableau_helper (OR(NOT a,b)) lits n1 n2 extras
				|BIC(a,b) ->  tableau_helper (OR(AND(a,b), AND(NOT a, NOT b))) lits n1 n2 extras
				|NOT(AND(a,b)) -> tableau_helper (OR(NOT a, NOT b)) lits n1 n2 extras
				|NOT(OR(a,b)) -> tableau_helper (AND(NOT a, NOT b)) lits n1 n2 extras
				|NOT(COND(a,b)) -> tableau_helper (OR(a, NOT b)) lits n1 n2 extras
				|NOT(BIC(a,b)) ->  tableau_helper (OR(AND(a,NOT b), AND(NOT a, b))) lits n1 n2 extras
				|NOT(NOT a) ->  let _ = printf "not not %d %d\n" n1 n2 in
									tableau_helper a lits n1 n2  extras
				|NOT(ATOM s) -> (   let _ = printf "not atom %d %d\n" n1 n2 in
									match extras with
									 hd::tl -> let _ = printf "not atom extras %d %d\n" n1 n2 in
												let (litsA, nA, dirA, fml_map) = tableau_helper hd lits n1 n2 tl in     (*use inside let in, and and change 1 and n2 accord to last subtree formed*)
													(litsA, nA, dirA, (n1, ATOM(s))::fml_map)
									|[] -> (lits, n2, [], [])
								)
				|ATOM(s) -> (	printf "atom %d %d\n" n1 n2;
								match extras with
									 hd::tl -> let _ = printf "atom extras %d %d\n" n1 n2 in
												let (litsA, nA, dirA, fml_map) = tableau_helper hd lits (n1+1) (n2+1) tl in
													(litsA, nA, (n1,n2)::dirA, (n1, ATOM(s))::fml_map)
									|[] -> (lits, n2, [], [])
							)
		in
		let arg = AND(convert_arg_to_Prop (List.tl prop_list), (List.hd prop_list)) in
		let (lits, n, dir, fml_map_temp) = tableau_helper arg [] 1 2 [] in
		let fml_map = (1,arg)::fml_map_temp in
		let _ = fprintf fout "subgraph dir {\n" in
		let _ = print_tuple_list_to_file fout dir in
		let _ = fprintf fout "}\n}" in
			fml_map
	
end;;
#use "arg.ml";;
module PropLogicTableau = (PropLogicTableau : PropLogicTableau) ;;

let get_1_2 (a,_) = a;;
let get_2_2 (_,a) = a;;

let x = tableau ((NOT(get_2_2 arg))::(get_1_2 arg));;
