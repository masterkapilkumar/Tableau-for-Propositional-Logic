open PropLogicTableau

let perceive = ATOM "p";;
let delusive = ATOM "q";;
let veridical = ATOM "r";;
let something = ATOM "I perceive something";;
let material = ATOM "I perceive a material object";;
let sensation = ATOM "I perceive a sensation";;
let differ = ATOM "My experience in veridical perception would always differ qualitatively from my experience in delusive perception";;

(*
let h1 = COND (perceive, NOT (BIC (delusive, veridical)));;
let h2 = COND (delusive, AND (perceive, NOT (material)));;
let h3 = COND (AND (perceive, NOT (material)), sensation);;
let h4 = COND (veridical, perceive);;
let h5 = COND (AND (veridical, material), differ);;
let h6 = NOT (differ);;
let c = COND (perceive, AND (sensation, NOT (material)));;
let arg = ([h1; h2; h3; h4; h5; h6], c);;

*)

let h1 = OR(AND(perceive, delusive),AND(NOT(perceive),veridical));;
let c = AND(OR(NOT(perceive),delusive),OR(perceive, veridical));;
let arg = ([h1], c);;