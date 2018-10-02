open PropLogicTableau

let perceive = ATOM "a";;
let delusive = ATOM "b";;
let veridical = ATOM "c";;
let something = ATOM "s";;
let material = ATOM "b";;
let sensation = ATOM "c";;
let differ = ATOM "d";;

let h1 = COND (perceive, NOT (BIC (delusive, veridical)));;
let h2 = COND (delusive, AND (perceive, NOT (material)));;
let h3 = COND (AND (perceive, NOT (material)), sensation);;
let h4 = COND (veridical, perceive);;
let h5 = COND (AND (veridical, material), differ);;
let h6 = NOT (differ);;
let c = COND (perceive, AND (sensation, NOT (material)));;
let arg = ([h1; h2; h3; h4; h5; h6], c);;

(*
let h1 = OR(AND(perceive, delusive),AND(NOT(perceive),veridical));;
let c = AND(OR(NOT(perceive),delusive),OR(perceive, veridical));;
let arg = ([h1], c);;
*)
(*

let h1 = OR (NOT(perceive), NOT (AND (OR(NOT(delusive), veridical), OR(NOT(veridical), delusive))));;
let h2 = OR (NOT(delusive), AND (perceive, NOT (material)));;
let h3 = OR (NOT(AND (perceive, NOT (material))), sensation);;
let h4 = OR (NOT(veridical), perceive);;
let h5 = OR (NOT(AND (veridical, material)), differ);;
let h6 = NOT (differ);;
let c = OR (NOT(perceive), AND (sensation, NOT (material)));;
let arg = ([h1; h2; h3; h4; h5; h6], c);;

let h1 = COND(NOT(perceive),delusive);;
let h2 = OR(perceive,veridical);;
let h3 = NOT(perceive);;
let c = AND(delusive,veridical);;
let arg = ([h1; h2; h3], c);;



let h1 = COND(perceive,COND(delusive,veridical));;
let c = AND( AND(perceive, veridical), AND(OR(NOT(perceive),delusive),OR(NOT(delusive),NOT(veridical))));;
let arg = ([], c);;
*)
