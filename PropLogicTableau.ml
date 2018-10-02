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
	
	
	(*Convert Argument type to Prop - take AND of all assumptions and negation of conclusion*)
	let rec convert_arg_to_Prop prop_list =
		match prop_list with
			 p1::x ->   if(x=[]) then
							p1
						else
							AND(p1, convert_arg_to_Prop x)
			|[] -> ATOM("shouldn't reach here")
	
	(* Print list of edges (tuples) in DOT syntax into a file *)
	(* fout - output stream *)
	(* dir - directed edges (tuples) list *)
	let rec print_edges_list_to_file fout dir =
		match dir with
			 (a,b)::tl -> (fprintf fout "\t\t%d->%d;\n" a b; print_edges_list_to_file fout tl)
			| [] -> ()
	
	(* Print list of propositional formulae (tree node labels) in latex syntax into a file *)
	(* fout - output stream *)
	(* fml_map - list of tuples (node number, formula) *)
	let rec print_labels_list_to_file fout fml_map =
		let rec prop_to_tex prop =
			match prop with 
				 AND(NOT(ATOM(a)),NOT(ATOM(b))) ->  "\\neg " ^ a ^ " \\wedge \\neg " ^ b
				|AND(NOT(ATOM(a)),ATOM(b)) ->  "\\neg " ^ a ^ " \\wedge " ^ b
				|AND(ATOM(a),NOT(ATOM(b))) ->  a ^ " \\wedge \\neg " ^ b
				|AND(ATOM(a),ATOM(b)) ->  a ^ " \\wedge " ^ b
				|AND(a,NOT(ATOM(b))) ->  "(" ^ (prop_to_tex a) ^ ") \\wedge \\neg " ^ b
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
				
				|NOT(NOT(ATOM(a))) -> "\\neg \\neg " ^ a
				|NOT(ATOM(a)) -> "\\neg " ^ a
				|NOT(a) -> "\\neg (" ^ (prop_to_tex a) ^ ")"
				
				|ATOM(s) -> s
		in
		match fml_map with
			(* Add formatting of dot2tex labels of tree nodes *)
			 (n,p)::tl -> (fprintf fout "\t%d [texlbl=\"\\underline{%d. {\\LARGE \\color{green} $%s$}}\"];\n" n n (prop_to_tex p); print_labels_list_to_file fout tl)
			| [] -> ()
	
	
	(* Check if any complementary pair of "prop" exists in lits (list of formulae) or not *)
	(* Case 1 - check if NOT(prop) exists in lits *)
	(* Case 2 - check if prop is equal to NOT(phi) for any phi in lits *)
	let rec findComplimentaryPair lits prop =
		match lits with
			 (n, hd)::tl -> if((NOT(hd) = prop) || NOT(prop) = hd) then n else findComplimentaryPair tl prop
			|[] -> -1
	
	
	let tableau prop_list =
		let fout = open_out "arg.dot" in
		(* Print header of node labels to a file in DOT syntax *)
		let _ = fprintf fout "%s\n%s\n%s\n" "digraph {" "\tranksep = 0.35;" "\tnode [shape=plaintext];" in
		
		(* Helper function for computing node labeling and edges of the tableau *)
		(* INPUT ARGUMENTS: *)
		(* prop - propositional formula which needs to be expanded in the tableau *)
		(* lits - list of formulae occuring in the path from root node to current node of the tableau *)
		(* n1 - numerical label for current node *)
		(* n2 - next possible numerical label for next expanded node *)
		(* extras - list of formulae of "A" in "and(A,B)" which are not yet expanded in the tableau. Only "B" has expanded so far. *)
		(* extra_index - correct numerical label of next expanded formula of "extras" *)
		
		(* RETURN VALUES: *)
		(* nA - last numerical label of subtree of current node *)
		(* dir - list of directed edges (black) from top to bottom *)
		(* ancestors - list of backward directed edges (blue dashed) from bottom to top *)
		(* fml_map - map of numerical label of tree nodes to propositional formula label *)
		(* closed - list of undirected edges between complementary pairs for closing the paths *)
		(* isClosed (boolean) - whether current path closed or not *)
		let rec tableau_helper prop lits n1 n2 extras extra_index =
			match prop with
				 AND(a,b) -> 	
							(* check if any complementary pair exists in current path or not *)
							let isClosed = findComplimentaryPair lits (AND(a,b)) in
								if(isClosed <> -1) then (n2, [], [], [], [(n1, isClosed)], true)
								else
							(* check if any complementary pair exists in current path after expanding "a" of AND(a,b) *)
							let isClosedA = findComplimentaryPair lits a in
								if(isClosedA <> -1) then 
									(n2, [(n1,n2)], [], [(n2,a)], [(n2, isClosedA)], true)
								else
							
							let litIndex = if(extra_index == -1) then n1 else extra_index in
							let (nA, dir, ancestors, fml_map, closed, isClosed) =
							        (* Expand "b" of AND(a,b) after adding current formula to lits and "a" to extras, which will be expanded later *)
									tableau_helper b ((litIndex, AND(a,b))::lits) (n2+1) (n2+2) ((n2,a)::extras) (-1) 
							in
							let ances = if(extra_index == -1) then (n1,n2+1)::ancestors else ancestors in
								(nA, (n1,n2)::(n2,n2+1)::dir, ances, (n2,a)::(n2+1,b)::fml_map, closed, isClosed)
				|OR(a,b) -> 
							(* check if any complementary pair exists in current path or not *)
							let isClosed = findComplimentaryPair lits (OR(a,b)) in
								if(isClosed <> -1) then (n1, [], [], [], [(n1, isClosed)], true)
								else
							let litIndex = if(extra_index == -1) then n1 else extra_index in
							
							(* First expand "a" in one branch and then "b" in the other branch *)
							let (nA, dirA, ancestors1, fml_map1, closed1, isClosed1) = tableau_helper a ((litIndex,OR(a,b))::lits) n2 (n2+2) extras (-1) in
							let (nB, dirB, ancestors2, fml_map2, closed2, isClosed2) = tableau_helper b ((litIndex,OR(a,b))::lits) (n2+1) (nA+1) extras (-1) in
								(* Merge the return values from both the branches *)
								(nB, (n1,n2)::(n1,n2+1)::(dirA@dirB), ancestors1@ancestors2, (n2,a)::(n2+1,b)::(fml_map1@fml_map2), closed1@closed2, (isClosed1 && isClosed2))
				
				|COND(a,b) -> tableau_helper (OR(NOT a,b)) lits n1 n2 extras (-1)
				|BIC(a,b) ->  tableau_helper (OR(AND(a,b), AND(NOT a, NOT b))) lits n1 n2 extras (-1)
				|NOT(AND(a,b)) -> tableau_helper (OR(NOT a, NOT b)) lits n1 n2 extras (-1)
				|NOT(OR(a,b)) -> tableau_helper (AND(NOT a, NOT b)) lits n1 n2 extras (-1)
				|NOT(COND(a,b)) -> tableau_helper (AND(a, NOT b)) lits n1 n2 extras (-1)
				|NOT(BIC(a,b)) ->  tableau_helper (OR(AND(a,NOT b), AND(NOT a, b))) lits n1 n2 extras (-1)
				
				|NOT(NOT a) ->
							(* check if any complementary pair exists in current path or not *)
							let isClosed = findComplimentaryPair lits (NOT(NOT a)) in
							if(isClosed <> -1) then (n1, [], [], [], [(n1, isClosed)], true)
							else
							(* NOT(NOT(a))=a *)
							let (nA, dir, ancestors, fml_map, closed, isClosed) = tableau_helper a ((n1,NOT(NOT a))::lits) n2 (n2+1) extras (-1) in
								(nA, (n1,n2)::dir, ancestors, (n2, a)::fml_map, closed, isClosed)
				|NOT(ATOM s) -> (
							(* check if any complementary pair exists in current path or not *)
							let isClosed = findComplimentaryPair lits (NOT(ATOM s)) in
							if(isClosed <> -1) then (n2, [], [], [], [(n1, isClosed)], true)
							else
							let litIndex = if(extra_index == -1) then n1 else extra_index in 
							
							(* Since current formula can't be expanded further, expand any pending formula in extras from this point *)
							match extras with
								(n,hd)::tl ->  (
												let (nA, dir, ancestors, fml_map, closed, isClosed) = tableau_helper hd ((litIndex, NOT(ATOM(s)))::lits) n1 n2 tl n in
												
												(* Add necessary back edges from current "extra" to its original position *)
												match hd with
													 AND(a,b) -> (nA, dir, (n,n2)::(n,n2+1)::ancestors, fml_map, closed, isClosed)
													|OR(a,b) -> (nA, dir, (n,n2)::(n,n2+1)::ancestors, fml_map, closed, isClosed)
													| NOT(NOT(a)) -> (nA, dir, (n,n2)::ancestors, fml_map, closed, isClosed)
													| _ -> (nA, dir, ancestors, fml_map, closed, isClosed)
												)
								|[] -> (n1, [], [], [], [], false)
							)
				|ATOM(s) -> (
							(* check if any complementary pair exists in current path or not *)
							let isClosed = findComplimentaryPair lits (ATOM s) in
							if(isClosed <> -1) then (n2, [], [], [], [(n1, isClosed)], true)
							else
							let litIndex = if(extra_index == -1) then n1 else extra_index in 
							
							(* Since current formula can't be expanded further, expand any pending formula in extras from this point *)
							match extras with
								 (n,hd)::tl ->  (
												let (nA, dir, ancestors, fml_map, closed, isClosed) = tableau_helper hd ((litIndex, ATOM(s))::lits) n1 n2 tl n in
												
												(* Add necessary back edges from current "extra" to its original position *)
												match hd with
													 AND(a,b) -> (nA, dir, (n,n2)::(n,n2+1)::ancestors, fml_map, closed, isClosed)
													|OR(a,b) -> (nA, dir, (n,n2)::(n,n2+1)::ancestors, fml_map, closed, isClosed)
													|COND(a,b) -> (nA, dir, (n,n2)::(n,n2+1)::ancestors, fml_map, closed, isClosed)
													|BIC(a,b) -> (nA, dir, (n,n2)::(n,n2+1)::ancestors, fml_map, closed, isClosed)
													| NOT(NOT(a)) -> (nA, dir, (n,n2)::ancestors, fml_map, closed, isClosed)
													| _ -> (nA, dir, ancestors, fml_map, closed, isClosed)
												)
								|[] -> (n1, [], [], [], [], false)
							)
		in
		let arg = AND(convert_arg_to_Prop (List.tl prop_list), (List.hd prop_list)) in
		let (n, dir, ancestors, fml_map_temp, closed, isClosed) = tableau_helper arg [] 1 2 [] (-1) in
		let _ = if(isClosed=false) then printf "\nThe given argument is invalid.\n" else printf "\nThe given argument is valid.\n" in
		let fml_map = (1,arg)::fml_map_temp in
		(* Print all edges and node labels to dot file *)
		let _ = print_labels_list_to_file fout fml_map in
		let _ = fprintf fout "\tsubgraph dir {\n" in
		let _ = print_edges_list_to_file fout dir in
		let _ = fprintf fout "\t}\n" in
		let _ = fprintf fout "\tsubgraph ancestor {\n\t\tedge [dir=back, color=blue, style=dashed]\n" in
		let _ = print_edges_list_to_file fout ancestors in
		let _ = fprintf fout "\t}\n" in
		let _ = fprintf fout "\tsubgraph undir {\n\t\tedge [dir=none, color=red]\n" in
		let _ = print_edges_list_to_file fout closed in
		let _ = fprintf fout "\t}\n}" in
			close_out fout
	
end;;
#use "arg.ml";;
module PropLogicTableau = (PropLogicTableau : PropLogicTableau) ;;

let get_1_2 (a,_) = a;;
let get_2_2 (_,a) = a;;

let x = tableau ((NOT(get_2_2 arg))::(get_1_2 arg));;
