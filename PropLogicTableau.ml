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
	
	(*TODO - read the input from the file*)
	let perceive = ATOM "I perceive";;
	let delusive = ATOM "My perception is delusive";;
	let veridical = ATOM "My perception is veridical";;
	let something = ATOM "I perceive something";;
	let material = ATOM "I perceive a material object";;
	let sensation = ATOM "I perceive a sensation";;
	let differ = ATOM "My experience in veridical perception would always differ qualitatively from my experience in delusive perception";;
	
	let h1 = COND (perceive, NOT (BIC (delusive, veridical)));;
	let h2 = COND (delusive, AND (perceive, NOT (material)));;
	let h3 = COND (AND (perceive, NOT (material)), sensation);;
	let h4 = COND (veridical, perceive);;
	let h5 = COND (AND (veridical, material), differ);;
	let h6 = NOT (differ);;
	let c = COND (perceive, AND (sensation, NOT (material)));;
	let props = h1::h2::h3::h4::h5::h6::c::[];;
	(************************************************************************)
	
	let tableau prop_list =
		let helper prop_list =
			()
		in
		match prop_list with
			 x::xs -> ()
			|[] -> ()
	
	let xx = tableau props;;
end;;

module PropLogicTableau = (PropLogicTableau : PropLogicTableau) ;;