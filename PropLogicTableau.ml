open PropLogicTableau

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
	
	let tableau prop_list =
		let helper prop_list =
			()
		in
		match prop_list with
			 x::xs -> ()
			|[] -> ()
end;;

module PropLogicTableau = (PropLogicTableau : PropLogicTableau) ;;