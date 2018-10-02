# Tableau-for-Propositional-Logic
Implementation of Tableau method for Propositional Logic in OCaml.

## How to run
- First compile signature to generate binary file:

      ocamlc PropLogicTableau.mli

- Then put input propositional argument in arg.ml

- Then run the module:
      
      ocaml PropLogicTableau.ml
      
- It will generate arg.dot, which can be compiled using:
      
      dot -Timap -oarg.map -Tgif -oarg.gif arg.dot

- To see proper labeling of nodes, convert dot file to latex:
      
      dot2tex arg.dot > arg.tex

## Requirements
- OCaml
- xdot (www.graphviz.com)
- dot2tex library in Python2.x
