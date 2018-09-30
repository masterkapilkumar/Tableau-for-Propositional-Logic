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
	
	let rec print_edges_list_to_file fout dir =
		match dir with
			 (a,b)::tl -> (fprintf fout "\t\t%d->%d;\n" a b; print_edges_list_to_file fout tl)
			| [] -> ()
	
	let rec print_labels_list_to_file fout fml_map =
		let rec prop_to_tex prop =
			match prop with 
				 AND(NOT(ATOM(a)),NOT(ATOM(b))) ->  "\\neg " ^ a ^ " \\wedge \\neg " ^ b
				|AND(NOT(ATOM(a)),ATOM(b)) ->  "\\neg " ^ a ^ " \\wedge " ^ b
				|AND(ATOM(a),NOT(ATOM(b))) ->  a ^ " \\wedge \\neg " ^ b
				|AND(ATOM(a),ATOM(b)) ->  a ^ " \\wedge " ^ b
				|AND(a,NOT(ATOM(b))) ->  "(" ^ (prop_to_tex a) ^ ") \\wedge \\neg" ^ b
				|AND(a,ATOM(b)) ->  "(" ^ (prop_to_tex a) ^ ") \\wedge " ^ b
				|AND(NOT(ATOM(a)),b) ->  "\\neg " ^ a ^ " \\wedge (" ^ (prop_to_tex b) ^ ")"
				|AND(ATOM(a),b) ->  a ^ " \\wedge (" ^ (prop_to_tex b) ^ ")"
				|AND(a,b) -> "(" ^ (prop_to_tex a) ^ ") \\wedge (" ^ (prop_to_tex b) ^ ")"
				
				|OR(NOT(ATOM(a)),NOT(ATOM(b))) ->  "\\neg " ^ a ^ " \\vee \\neg " ^ b
				|OR(NOT(ATOM(a)),ATOM(b)) ->  "\\neg " ^ a ^ " \\vee " ^ b
				|OR(ATOM(a),NOT(ATOM(b))) ->  a ^ " \\vee \\neg " ^ b
				|OR(ATOM(a),ATOM(b)) ->  a ^ " \\vee " ^ b
				|OR(a,NOT(ATOM(b))) ->  "(" ^ (prop_to_tex a) ^ ") \\vee \\neg " ^ b
				|OR(a,ATOM(b)) ->  "(" ^ (prop_to_tex a) ^ ") \\vee " ^ b
				|OR(NOT(ATOM(a)),b) ->  "\\neg " ^ a ^ " \\vee (" ^ (prop_to_tex b) ^ ")"
				|OR(ATOM(a),b) ->  a ^ " \\vee (" ^ (prop_to_tex b) ^ ")"
				|OR(a,b) -> "(" ^ (prop_to_tex a) ^ ") \\vee (" ^ (prop_to_tex b) ^ ")"
				
				|COND(NOT(ATOM(a)),NOT(ATOM(b))) ->  "\\neg " ^ a ^ " \\rightarrow \\neg " ^ b
				|COND(NOT(ATOM(a)),ATOM(b)) ->  "\\neg " ^ a ^ " \\rightarrow " ^ b
				|COND(ATOM(a),NOT(ATOM(b))) ->  a ^ " \\rightarrow \\neg " ^ b
				|COND(ATOM(a),ATOM(b)) ->  a ^ " \\rightarrow " ^ b
				|COND(a,NOT(ATOM(b))) ->  "(" ^ (prop_to_tex a) ^ ") \\rightarrow \\neg " ^ b
				|COND(a,ATOM(b)) ->  "(" ^ (prop_to_tex a) ^ ") \\rightarrow " ^ b
				|COND(NOT(ATOM(a)),b) ->  "\\neg " ^ a ^ " \\rightarrow (" ^ (prop_to_tex b) ^ ")"
				|COND(ATOM(a),b) ->  a ^ " \\rightarrow (" ^ (prop_to_tex b) ^ ")"
				|COND(a,b) -> "(" ^ (prop_to_tex a) ^ ") \\rightarrow (" ^ (prop_to_tex b) ^ ")"
				
				|BIC(NOT(ATOM(a)),NOT(ATOM(b))) ->  "\\neg " ^ a ^ " \\leftrightarrow \\neg " ^ b
				|BIC(NOT(ATOM(a)),ATOM(b)) ->  "\\neg " ^ a ^ " \\leftrightarrow " ^ b
				|BIC(ATOM(a),NOT(ATOM(b))) ->  a ^ " \\leftrightarrow \\neg " ^ b
				|BIC(ATOM(a),ATOM(b)) ->  a ^ " \\leftrightarrow " ^ b
				|BIC(a,NOT(ATOM(b))) ->  "(" ^ (prop_to_tex a) ^ ") \\leftrightarrow \\neg " ^ b
				|BIC(a,ATOM(b)) ->  "(" ^ (prop_to_tex a) ^ ") \\leftrightarrow " ^ b
				|BIC(NOT(ATOM(a)),b) ->  "\\neg " ^ a ^ " \\leftrightarrow (" ^ (prop_to_tex b) ^ ")"
				|BIC(ATOM(a),b) ->  a ^ " \\leftrightarrow (" ^ (prop_to_tex b) ^ ")"
				|BIC(a,b) -> "(" ^ (prop_to_tex a) ^ ") \\leftrightarrow (" ^ (prop_to_tex b) ^ ")"
				
				|NOT(NOT(ATOM(a))) -> "\\neg\\neg " ^ a
				|NOT(ATOM(a)) -> "\\neg " ^ a
				|NOT(a) -> "\\neg (" ^ (prop_to_tex a) ^ ")"
				
				|ATOM(s) -> s
		in
		match fml_map with
			 (n,p)::tl -> (fprintf fout "\t%d [texlbl=\"\\underline{%d. {\\LARGE \\color{green} $%s$}}\"];\n" n n (prop_to_tex p); print_labels_list_to_file fout tl)
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
								let (litsA, nA, dirA, fml_map) = tableau_helper a lits n2 (n2+1) extras in
									(litsA, nA, (n1,n2)::dirA, (n2, a)::fml_map)
				|NOT(ATOM s) -> (   let _ = printf "not atom %d %d\n" n1 n2 in
									match extras with
									 hd::tl -> let _ = printf "not atom extras %d %d\n" n1 n2 in
												let (litsA, nA, dirA, fml_map) = tableau_helper hd lits n1 n2 tl in     (*use inside let in, and and change 1 and n2 accord to last subtree formed*)
													(litsA, nA, dirA, fml_map)
									|[] -> (lits, n1, [], [])
								)
				|ATOM(s) -> (	let _ = printf "atom %d %d\n" n1 n2 in
								match extras with
									 hd::tl -> let _ = printf "atom extras %d %d\n" n1 n2 in
												let (litsA, nA, dirA, fml_map) = tableau_helper hd lits n1 n2 tl in
													(litsA, nA, dirA, fml_map)
									|[] -> (lits, n1, [], [])
							)
		in
		let arg = AND(convert_arg_to_Prop (List.tl prop_list), (List.hd prop_list)) in
		let (lits, n, dir, fml_map_temp) = tableau_helper arg [] 1 2 [] in
		let fml_map = (1,arg)::fml_map_temp in
		let _ = print_labels_list_to_file fout fml_map in
		let _ = fprintf fout "\tsubgraph dir {\n" in
		let _ = print_edges_list_to_file fout dir in
		let _ = fprintf fout "\t}\n}" in
			close_out fout
	
end;;
#use "arg.ml";;
module PropLogicTableau = (PropLogicTableau : PropLogicTableau) ;;

let get_1_2 (a,_) = a;;
let get_2_2 (_,a) = a;;

let x = tableau ((NOT(get_2_2 arg))::(get_1_2 arg));;
