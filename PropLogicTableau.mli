module type PropLogicTableau =
sig
	exception Atom_exception
	type prop
	type argument
	val tableau: prop list -> unit
end