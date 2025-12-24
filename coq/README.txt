============================================================
🎸 Channeling Jack Black: This is Just a Tribute 🎸
============================================================

Inspired by Jack Black’s “Greatest Song in the World,” this Coq code is not the ultimate model of twistor string theory Feynman diagrams as homotopy types, but it’s a playful toy tribute / starting point.  

It models diagrams as **right-associated binary trees** and explores the idea that different internal structures can yield the same observable outcome.

------------------------------------------------------------
Overview
------------------------------------------------------------

- Only **right-associated binary trees** are considered as canonical representatives.  
- Equivalence is defined via **observable leaves** (external particles / amplitudes).  
- Internal node structure is ignored once canonical form is chosen.  
- Right-association ensures a **unique representative** and simplifies reasoning.

------------------------------------------------------------
Key Concepts
------------------------------------------------------------

Diagram:
- Binary tree representing a simplified Feynman diagram
- Leaf n  = external particle labeled n
- Node d1 d2 = combination of two subdiagrams
- Only **right-associated trees** are used in analysis:
    - All internal nesting goes to the right
    - Arbitrary trees must first be normalized to right-associated form before equivalence comparison

Right-associated canonical form:
Example with 3 leaves (1, 2, 3):

Arbitrary nesting (not canonical):

      Node
     /    \
   Node     3
  /    \
 1      2

Right-associated canonical form (canonical representative):

      Node
     /    \
    1     Node
         /   \
        2     3

- Both trees have the same leaves: [1;2;3]  
- The right-associated form is **required** for equivalence checking  

------------------------------------------------------------
Leaves function

- Extracts the observable external particles:

leaves : Diagram -> list nat
- Physics analogy: external states / amplitude inputs  
- CS analogy: public API output  

------------------------------------------------------------
Equivalence

- Two diagrams are equivalent if they have the **same leaves** (observable output).  
- Internal node differences are ignored after canonicalization.  
- Physics analogy: different Feynman diagrams may have different internal propagators or decay chains, but the **same final external particles** yield the same amplitude / S-matrix element.  
- CS analogy: different implementations that produce the same API output.

------------------------------------------------------------
Example

diagram1 = Node (Leaf 1) (Node (Leaf 2) (Leaf 3))
diagram2 = Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)

Eval compute in (leaves diagram1)  (* [1;2;3] *)
Eval compute in (leaves diagram2)  (* [1;2;3] *)

Example diagrams_equiv_test :
equiv diagram1 diagram2.
Proof.
  reflexivity.
Qed.

- Both diagrams are right-associated
- Leaves are identical, so equivalence holds
- This models multiple Feynman diagrams with the same observable final states but potentially different intermediate decays:

Example ASCII illustration:

  Meson decay 1:     Meson decay 2:

       M                  M
      / \                / \
     A   B              X   Y
    / \                  \
   e   e                  e

- Both produce final electrons (leaves = [e,e])
- Internal structure differs
- Our toy model treats them as equivalent

------------------------------------------------------------
CS Analogy

- Tree = internal implementation / private detail  
- Leaves = public API / observable output  
- Equivalence = same observable output  
- Right-associated tree = canonical implementation to simplify reasoning  

------------------------------------------------------------
Physics Analogy

- Different Feynman diagrams can produce the same final external particles  
- Leaves = external particles / observable states  
- Internal nodes = propagators (intermediate states)  
- Right-associated tree = canonical representative for reasoning about equivalence  

------------------------------------------------------------
Getting Started

1. Install Coq: https://coq.inria.fr/download  
2. Clone the repository:

   git clone https://github.com/FrancisErdman2025/dealpal.git
   cd dealpal/coq

3. Open diagrams_equiv.v in CoqIDE (or VS Code with Coq extension)  
4. Step through interactively (Coq -> Step Forward) to see Eval compute outputs  
5. Compile buffer (Compile -> Compile Buffer) to verify all unit tests pass  

------------------------------------------------------------
Notes / Disclaimer

- Toy model / playground; not production physics or full twistor string theory  
- Inspired by HoTT, simplified for CS intuition  
- Only right-associated trees are used for equivalence  
- Leaves = amplitude analogy is simplified, but captures the concept that different internal diagrams can yield the same observable outcome  

------------------------------------------------------------
License

MIT License — feel free to play with, fork, and extend this toy model
